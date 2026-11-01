(** * Instruction, terminator, block, cfg and function-level lemmas for the
      LambdaANF -> LLVM correctness proof.

    Everything is stated under Vellvm's call knot: for
    [ctx : CallE ~> itree (CallE +' MCFGEtop)],

      [runs t s s' r := interp_mcfg (interp_mrec ctx t) s ≈ Ret (s', r)]
      [oom t s       := ends_in_oom (interp_mcfg (interp_mrec ctx t) s)]

    with [s = (st, ((sf, stk), g))].  Operand evaluations are taken as
    [exp_eval] hypotheses (LLVM_exp_lemmas), so that the same lemma serves the
    emitter's compound operand and its flattened atom.

    API facts discovered while writing this file (Vellvm b63a28a0):

    - [denote_instr (IId x, INSTR_Op e, [])] is
        [uv <- denote_exp' None e;; lwrite x uv;; ret tt];
      [INSTR_Load dt (du, e) []] is
        [a <- denote_exp' (Some du) e;; v <- load dt a;; v' <- freeze v;; lwrite x v']
      where [freeze (DVALUE_Base v)] is [ITree.map DVALUE_Base (Ret v)] for
      non-poison [v]; [INSTR_Store (dt, ev) (du, ep) []] (void id) is
        [v <- denote_exp' (Some dt) ev;; a <- denote_exp' (Some du) ep;;
         (match a with poison => UB | _ => store dt a v);; ret tt];
      [INSTR_Alloca dt []] is [v <- alloca dt 1 None;; lwrite x v;; ret tt]
      (no annotations: one element, default alignment, which
      [handle_memoryM] turns into alignment 8);
      [INSTR_Call (dt, f) args [] []] is
        [vs <- map_monad (fun '(t, op) => denote_exp' (Some t) op) (map fst args);;
         r <- (match intrinsic_exp f with
               | Some s => intrinsic ... | None =>
                 fv <- denote_exp' None f;; res <- call dt fv vs;;
                 match res with inl exc => raiseLLVM exc | inr v => ret v end end);;
         (IVoid: ret tt | IId x: lwrite x r)].
      [intrinsic_exp] is [None] unless the callee is [EXP_Ident (ID_Global
      (Name s))] with [s] a declared intrinsic; ["garbage_collect"] is not one.
    - [denote_exp' t e = withCall (denote_exp t e) = translate inr1 (...)],
      which is definitionally [lift_top (denote_exp t e)].
    - [TERM_Br (DTYPE_I 1, e)] tests the bit with [equ b one]; [TERM_Switch]
      evaluates every literal with [coerce_integer_to_int (Some sz) (denote_int_syntax x)]
      (= [ret (DVALUE_I sz (repr _))]) and [select_switch] compares with
      [Integers.eq] (so modulo [2^64] for 64-bit literals), first match wins.
    - [denote_phis from phis] evaluates all phis first (each with [assoc from]
      on its argument list, first match), then performs all the local writes.
    - [denote_ocfg_map bmap va] is [ITree.iter] over [RM.find bid bmap];
      [ocfg_map] agrees with [find_block] ([ocfg_map_find_block]).
    - [handle_memoryM (Alloca t n align)] is [allocate_dtyp t n (align or 8)],
      which can run out of memory: the fresh address is
      [next_key_with_alignment (mem_of st) align] (one past the greatest
      allocated key, padded), and [int_to_ptr] of it, or of the following
      bytes ([get_consecutive_ptrs]), raises [raise_oom] beyond [2^64].  Every
      other step of an allocation is a plain state update, so an allocation
      either runs out of memory or runs ([allocate_dtyp_total]).
    - [push_call_frame df args] with [length args = length (df_args df)]
      allocates a 0-byte varargs block ([DTYPE_Struct true []]): it pushes an
      empty memory frame and a local frame, and only the provenance counter
      and the address allocator move.  It can still OOM (the 0-byte block
      needs a representable address).
    - [pop_call_frame = stack_pop;; mem_pop]; [mem_pop] fails on the last
      memory frame ([Singleton]), so the frame stack must be a [Snoc].
    - [run_exc] is [ITree.iter] over [observe]; it catches exactly the
      [LLVMExcE] summand ([exc_of_event]).  Its commutation with
      [interp_mcfg (interp_mrec ctx _)] ([runs_run_exc], [oom_run_exc]) is
      proved by unfolding the interpreted tree one constructor at a time
      ([Jmc_ret], [Jmc_tau], [Jmc_call], [Jmc_vis], [Jmc_exc]) and inducting on
      the number of [Tau]s before the [Ret] / the OOM [Vis] ([steps_to]). *)

From Stdlib Require Import ZArith NArith List Lia Program Morphisms String.
From ITree Require Import ITree ITreeFacts Eq.Eqit Interp.InterpFacts
     Interp.RecursionFacts Events.State Events.StateFacts.
From ExtLib Require Import Structures.Monads.
From Paco Require Import paco.
From Vellvm Require Import
  Utils Syntax Params
  Interfaces.Memory Implementations.Memory
  Implementations.ParamsV Implementations.IPtrFinite
  Semantics.DynamicValues Semantics.MemoryBytes Semantics.LLVMEvents
  Semantics.Denotation Semantics.Operations
  Semantics.InterpretationStack Handlers.
From Vellvm Require Import Utils.IntMaps Semantics.Operations.Gep Semantics.EOU
     Syntax.ScopeTheory.
From CertiRocq.CodegenLLVM Require Import LambdaANF_to_LLVM LambdaANF_to_LLVM_statement
     LLVM_interp_lemmas LLVM_call_lemmas LLVM_exp_lemmas LLVM_mem_lemmas LLVM_convert LLVM_emit_facts.

Import ListNotations.
Import MonadNotation.
Open Scope monad_scope.
Open Scope Z_scope.

Set Bullet Behavior "Strict Subproofs".
Unset Implicit Arguments.

(* ------------------------------------------------------------------ *)
(** ** Generic facts *)

Lemma upd_local_sf_twice sf m1 m2 : upd_local_sf (upd_local_sf sf m1) m2 = upd_local_sf sf m2.
Proof. destruct sf; reflexivity. Qed.

Lemma stack_vars_upd sf m : stack_vars (upd_local_sf sf m) = m.
Proof. reflexivity. Qed.

(** [denote_exp'] is [lift_top]. *)
Lemma denote_exp'_lift t e : denote_exp' t e = lift_top (denote_exp t e).
Proof. reflexivity. Qed.

#[global] Instance ends_in_oom_proper {R} : Proper (eutt Logic.eq ==> iff) (@ends_in_oom R).
Proof.
  intros t t' H. unfold ends_in_oom. split; intros [k Hk]; exists k; [rewrite <- H | rewrite H]; exact Hk.
Qed.

Lemma eutt_Ret_Vis_abs {E R X} (r : R) (e : E X) k : (Ret r : itree E R) ≈ Vis e k -> False.
Proof. intros H. apply eqit_inv in H. cbn in H. exact H. Qed.

Section Runs.

  Variable ctx : CallE ~> itree (CallE +' MCFGEtop).
  Variable va : option ptr.

  Definition runs {X} (t : CFGtop X) (s s' : FusedS) (r : X) : Prop :=
    interp_mcfg (interp_mrec ctx t) s ≈ Ret (s', r).

  Definition oom {X} (t : CFGtop X) (s : FusedS) : Prop :=
    ends_in_oom (interp_mcfg (interp_mrec ctx t) s).

  #[global] Instance interp_mrec_ctx_proper {R} :
    Proper (eutt Logic.eq ==> eutt Logic.eq) (@interp_mrec CallE MCFGEtop ctx R).
  Proof.
    intros t t' H. rewrite !(interp_mrec_as_interp ctx). rewrite H. reflexivity.
  Qed.

  (** Events of [MCFGEtop] seen from [CFGtop]: [trigger e] in [CFGtop] is
      definitionally [ev e]. *)
  Definition ev {E} {H : E -< MCFGEtop} {T} (e : E T) : CFGtop T :=
    @ITree.trigger CFGEtop T (inr1 (@subevent E MCFGEtop H T e)).

  Lemma interp_mrec_ev {E} `{E -< MCFGEtop} {T} (e : E T) :
    interp_mrec ctx (ev e) ≈ ITree.trigger (subevent _ e).
  Proof. unfold ev. apply (interp_mrec_event ctx). Qed.

  Ltac to_ev :=
    match goal with
    | |- context [@ITree.trigger ?F ?T (@subevent ?E ?F ?I ?T ?e0)] =>
        change (@ITree.trigger F T (@subevent E F I T e0)) with (ev e0)
    end.
  Ltac to_call :=
    match goal with
    | |- context [@ITree.trigger ?F ?T (@subevent ?E ?F ?I ?T ?e0)] =>
        change (@ITree.trigger F T (@subevent E F I T e0)) with (@ITree.trigger CFGEtop T (inl1 e0))
    end.

  Lemma runs_eutt {X} (t t' : CFGtop X) s s' r : t ≈ t' -> runs t s s' r -> runs t' s s' r.
  Proof. unfold runs. intros H. rewrite H. auto. Qed.

  Lemma oom_eutt {X} (t t' : CFGtop X) s : t ≈ t' -> oom t s -> oom t' s.
  Proof. unfold oom. intros H. rewrite H. auto. Qed.

  (* ---------------------------------------------------------------- *)
  (** ** Monadic plumbing *)

  Lemma runs_ret {X} (x : X) s : runs (Ret x) s s x.
  Proof. unfold runs. rewrite (interp_mrec_ret ctx). apply interp_mcfg_ret. Qed.

  Lemma runs_bind {X Y} (t : CFGtop X) (k : X -> CFGtop Y) s s1 x s2 y :
    runs t s s1 x -> runs (k x) s1 s2 y -> runs (ITree.bind t k) s s2 y.
  Proof.
    unfold runs. intros H1 H2.
    rewrite (interp_mrec_bind' ctx), interp_mcfg_bind, H1, Eqit.bind_ret_l. exact H2.
  Qed.

  Lemma runs_bind_inv {X Y} (t : CFGtop X) (k : X -> CFGtop Y) s s2 y :
    runs (ITree.bind t k) s s2 y -> exists s1 x, runs t s s1 x /\ runs (k x) s1 s2 y.
  Proof.
    unfold runs. intros H.
    rewrite (interp_mrec_bind' ctx), interp_mcfg_bind in H.
    apply eutt_inv_bind_ret in H. destruct H as ([s1 x] & H1 & H2).
    exists s1, x. auto.
  Qed.

  Lemma runs_tau {X} (t : CFGtop X) s s' r : runs t s s' r -> runs (Tau t) s s' r.
  Proof. apply runs_eutt. rewrite tau_eutt. reflexivity. Qed.

  Lemma oom_bind_l {X Y} (t : CFGtop X) (k : X -> CFGtop Y) s :
    oom t s -> oom (ITree.bind t k) s.
  Proof.
    unfold oom. intros H.
    unfold ends_in_oom in *. destruct H as [k0 H']. eexists.
    rewrite (interp_mrec_bind' ctx), interp_mcfg_bind, H', bind_vis. reflexivity.
  Qed.

  Lemma oom_bind_r {X Y} (t : CFGtop X) (k : X -> CFGtop Y) s s1 x :
    runs t s s1 x -> oom (k x) s1 -> oom (ITree.bind t k) s.
  Proof.
    unfold oom, runs, ends_in_oom. intros H1 [k0 H2]. exists k0.
    rewrite (interp_mrec_bind' ctx), interp_mcfg_bind, H1, Eqit.bind_ret_l. exact H2.
  Qed.

  (** Bridge from [exp_eval]. *)
  Lemma exp_eval_mrec st sf stk g t e v :
    exp_eval st sf stk g t e v ->
    runs (denote_exp' t e) (st, ((sf, stk), g)) (st, ((sf, stk), g)) v.
  Proof.
    intros H. unfold runs. rewrite denote_exp'_lift, (interp_mrec_lift_top ctx). exact H.
  Qed.

  (** Local writes and reads, and memory events, under the knot. *)
  Lemma runs_lwrite id v st sf stk g :
    runs (lwrite id v) (st, ((sf, stk), g))
         (st, ((upd_local_sf sf (Maps.add id v (stack_vars sf)), stk), g)) tt.
  Proof. unfold runs, lwrite. to_ev. rewrite interp_mrec_ev. apply interp_mcfg_lwrite. Qed.

  Lemma runs_lread id v st sf stk g :
    RM.find id (stack_vars sf) = Some v ->
    runs (lread id) (st, ((sf, stk), g)) (st, ((sf, stk), g)) v.
  Proof.
    intros H. unfold runs, lread. to_ev. rewrite interp_mrec_ev.
    rewrite interp_mcfg_lread by exact H. rewrite upd_local_sf_id. reflexivity.
  Qed.

  Lemma runs_gread id v st ls g :
    RM.find id g = Some v -> runs (gread id) (st, (ls, g)) (st, (ls, g)) v.
  Proof.
    intros H. unfold runs, gread. to_ev. rewrite interp_mrec_ev.
    apply interp_mcfg_gread. exact H.
  Qed.

  (** The memory handler, as seen through [interp_mcfg]. *)
  Lemma interp_mcfg_memory_gen {X} (e : MemoryE X) st rest :
    interp_mcfg (ITree.trigger (subevent _ e)) (st, rest)
    ≈ ITree.bind (@memM_interp _ MCFGEbot _ _ _ X (handle_memoryM e) st)
                 (fun '(st', x) => Ret ((st', rest), x)).
  Proof.
    unfold interp_mcfg.
    rewrite interp_intrinsics_trigger.
    cbn. unfold F_trigger.
    rewrite interp_state_trigger.
    cbn. unfold on_mem, handle_memory.
    apply eutt_eq_bind. intros [st' x]. reflexivity.
  Qed.

  Lemma runs_memory {X} (e : MemoryE X) st rest st' x :
    memS_runs st (handle_memoryM e) st' x ->
    runs (trigger e) (st, rest) (st', rest) x.
  Proof.
    intros H. unfold runs. to_ev. rewrite interp_mrec_ev.
    rewrite interp_mcfg_memory_gen, (memM_interp_runs H), Eqit.bind_ret_l. reflexivity.
  Qed.

  Lemma runs_memory_c {X} (e : MemoryE X) st rest st' x :
    memS_runs_c st (handle_memoryM e) st' x ->
    runs (trigger e) (st, rest) (st', rest) x.
  Proof.
    intros H. unfold runs. to_ev. rewrite interp_mrec_ev.
    rewrite interp_mcfg_memory_gen, (memM_interp_runs_c _ _ _ _ H), Eqit.bind_ret_l. reflexivity.
  Qed.

  (** A memory computation that runs out of memory. *)
  Inductive memS_oom {X} : state -> memM X -> Prop :=
  | MO_oom st s : memS_oom st (Moom s)
  | MO_get st k : memS_oom st (k st) -> memS_oom st (Mget k)
  | MO_put st st0 k : memS_oom st0 (k tt) -> memS_oom st (Mput st0 k)
  | MO_next_key st sz al (k : Z -> memM X) :
      memS_oom st (k (next_key_with_alignment (mem_of st) al)) ->
      memS_oom st (Mchoose (Cnext_key sz al) k)
  | MO_fresh st (k : provenance -> memM X) :
      memS_oom {| state_memory_stack := state_memory_stack st;
                  state_provenance := next_provenance (state_provenance st) |}
               (k (next_provenance (state_provenance st))) ->
      memS_oom st (Mchoose Cfresh_prov k)
  | MO_exposed st (k : option provenance -> memM X) :
      memS_oom st (k None) -> memS_oom st (Mchoose Cexposed_prov k).

  Lemma memM_interp_oom {X} st (m : memM X) :
    memS_oom st m ->
    exists k, @memM_interp _ MCFGEbot _ _ _ X m st ≈ Vis (subevent _ (ThrowOOM tt)) k.
  Proof.
    induction 1; cbn.
    1: eexists; unfold raiseOOM, trigger_cast'; rewrite bind_trigger; reflexivity.
    all: destruct IHmemS_oom as [k0 Hk]; exists k0; try (rewrite Eqit.bind_ret_l; cbn); exact Hk.
  Qed.

  Lemma memS_oom_bind_l {X Y} st (m : memM X) (k : X -> memM Y) :
    memS_oom st m -> memS_oom st (bind m k).
  Proof. induction 1; cbn; constructor; auto. Qed.

  Lemma memS_oom_bind_r {X Y} st (m : memM X) (k : X -> memM Y) st1 x :
    memS_runs_c st m st1 x -> memS_oom st1 (k x) -> memS_oom st (bind m k).
  Proof. intros H; revert k; induction H; intros k0 Hk; cbn in *; try constructor; auto. Qed.

  Lemma oom_memory {X} (e : MemoryE X) st rest :
    memS_oom st (handle_memoryM e) -> oom (trigger e) (st, rest).
  Proof.
    intros H. unfold oom, ends_in_oom.
    destruct (memM_interp_oom st _ H) as [k Hk]. eexists.
    to_ev. rewrite interp_mrec_ev, interp_mcfg_memory_gen, Hk, bind_vis.
    reflexivity.
  Qed.

  (** Stack events. *)
  Definition new_frame (bs : list (raw_id * dvalue)) : stack_frame :=
    Build_stack_frame (fold_right (fun '(x, dv) => Maps.add x dv) Maps.empty bs)
                      None (Some (printer_object.(printer_get_loc) tt)).

  Lemma runs_stack_push bs st sf stk g :
    runs (stack_push bs) (st, ((sf, stk), g)) (st, ((new_frame bs, sf :: stk), g)) tt.
  Proof.
    unfold runs, stack_push. to_ev. rewrite interp_mrec_ev.
    unfold interp_mcfg. rewrite interp_intrinsics_trigger. cbn. unfold F_trigger.
    rewrite interp_state_trigger. cbn. unfold on_ls, handle_stack. cbn.
    repeat (rewrite Eqit.bind_ret_l; cbn). reflexivity.
  Qed.

  Lemma runs_stack_pop st sf sf' stk g :
    runs stack_pop (st, ((sf, sf' :: stk), g)) (st, ((sf', stk), g)) tt.
  Proof.
    unfold runs, stack_pop. to_ev. rewrite interp_mrec_ev.
    unfold interp_mcfg. rewrite interp_intrinsics_trigger. cbn. unfold F_trigger.
    rewrite interp_state_trigger. cbn. unfold on_ls, handle_stack. cbn.
    repeat (rewrite Eqit.bind_ret_l; cbn). reflexivity.
  Qed.

  (** Internal calls. *)
  Lemma runs_call dt fv vs s s' r :
    runs (ctx _ (Call dt fv vs)) s s' r -> runs (call dt fv vs) s s' r.
  Proof. unfold runs, call. to_call. rewrite (interp_mrec_call ctx). auto. Qed.

  Lemma oom_call dt fv vs s :
    oom (ctx _ (Call dt fv vs)) s -> oom (call dt fv vs) s.
  Proof. unfold oom, call. to_call. rewrite (interp_mrec_call ctx). auto. Qed.

  (* ---------------------------------------------------------------- *)
  (** ** Code *)

  Lemma denote_code_nil_eq : denote_code [] va = Ret tt.
  Proof. reflexivity. Qed.

  Lemma denote_code_cons_eq i c :
    denote_code (i :: c) va = (denote_instr i va;; denote_code c va).
  Proof. reflexivity. Qed.

  Lemma denote_code_app_eutt c1 c2 :
    denote_code (c1 ++ c2)%list va ≈ (denote_code c1 va;; denote_code c2 va).
  Proof.
    induction c1 as [|i c1 IH].
    - rewrite app_nil_l, denote_code_nil_eq. cbn [bind Monad_itree]. rewrite Eqit.bind_ret_l. reflexivity.
    - rewrite <- app_comm_cons, !denote_code_cons_eq. cbn [bind Monad_itree]. rewrite Eqit.bind_bind.
      apply eutt_eq_bind. intros _. exact IH.
  Qed.

  Lemma runs_code_nil s : runs (denote_code [] va) s s tt.
  Proof. rewrite denote_code_nil_eq. apply runs_ret. Qed.

  Lemma runs_code_cons i c s s1 s2 :
    runs (denote_instr i va) s s1 tt -> runs (denote_code c va) s1 s2 tt ->
    runs (denote_code (i :: c) va) s s2 tt.
  Proof. rewrite denote_code_cons_eq. intros. eapply runs_bind; eauto. Qed.

  Lemma runs_code_app c1 c2 s s1 s2 :
    runs (denote_code c1 va) s s1 tt -> runs (denote_code c2 va) s1 s2 tt ->
    runs (denote_code (c1 ++ c2)%list va) s s2 tt.
  Proof.
    intros H1 H2. eapply runs_eutt; [symmetry; apply denote_code_app_eutt|].
    eapply runs_bind; eauto.
  Qed.

  Lemma runs_code_singleton i s s' :
    runs (denote_instr i va) s s' tt -> runs (denote_code [i] va) s s' tt.
  Proof. intros H. eapply runs_code_cons; [exact H|apply runs_code_nil]. Qed.

  Lemma oom_code_cons_l i c s :
    oom (denote_instr i va) s -> oom (denote_code (i :: c) va) s.
  Proof. rewrite denote_code_cons_eq. apply oom_bind_l. Qed.

  Lemma oom_code_cons_r i c s s1 :
    runs (denote_instr i va) s s1 tt -> oom (denote_code c va) s1 ->
    oom (denote_code (i :: c) va) s.
  Proof. rewrite denote_code_cons_eq. intros. eapply oom_bind_r; eauto. Qed.

  Lemma oom_code_app_l c1 c2 s :
    oom (denote_code c1 va) s -> oom (denote_code (c1 ++ c2)%list va) s.
  Proof.
    intros H. eapply oom_eutt; [symmetry; apply denote_code_app_eutt|]. apply oom_bind_l, H.
  Qed.

  Lemma oom_code_app_r c1 c2 s s1 :
    runs (denote_code c1 va) s s1 tt -> oom (denote_code c2 va) s1 ->
    oom (denote_code (c1 ++ c2)%list va) s.
  Proof.
    intros H1 H2. eapply oom_eutt; [symmetry; apply denote_code_app_eutt|].
    eapply oom_bind_r; eauto.
  Qed.

  (* ---------------------------------------------------------------- *)
  (** ** Blocks *)

  Lemma denote_block_eq (b : LLVMAst.block dtyp) from :
    denote_block b from va =
    (denote_phis from (blk_phis b);; denote_code (blk_code b) va;; denote_terminator (blk_term b)).
  Proof. reflexivity. Qed.

  Lemma runs_block (b : LLVMAst.block dtyp) from s s1 s2 s3 r :
    runs (denote_phis from (blk_phis b)) s s1 tt ->
    runs (denote_code (blk_code b) va) s1 s2 tt ->
    runs (denote_terminator (blk_term b)) s2 s3 r ->
    runs (denote_block b from va) s s3 r.
  Proof.
    rewrite denote_block_eq. intros H1 H2 H3.
    eapply runs_bind; [exact H1|]. eapply runs_bind; [exact H2|exact H3].
  Qed.

  Lemma oom_block_phis (b : LLVMAst.block dtyp) from s :
    oom (denote_phis from (blk_phis b)) s -> oom (denote_block b from va) s.
  Proof. rewrite denote_block_eq. apply oom_bind_l. Qed.

  Lemma oom_block_code (b : LLVMAst.block dtyp) from s s1 :
    runs (denote_phis from (blk_phis b)) s s1 tt ->
    oom (denote_code (blk_code b) va) s1 -> oom (denote_block b from va) s.
  Proof.
    rewrite denote_block_eq. intros H1 H2. eapply oom_bind_r; [exact H1|]. apply oom_bind_l, H2.
  Qed.

  Lemma oom_block_term (b : LLVMAst.block dtyp) from s s1 s2 :
    runs (denote_phis from (blk_phis b)) s s1 tt ->
    runs (denote_code (blk_code b) va) s1 s2 tt ->
    oom (denote_terminator (blk_term b)) s2 -> oom (denote_block b from va) s.
  Proof.
    rewrite denote_block_eq. intros H1 H2 H3.
    eapply oom_bind_r; [exact H1|]. eapply oom_bind_r; [exact H2|exact H3].
  Qed.

  (* ---------------------------------------------------------------- *)
  (** ** Open control-flow graphs *)

  Lemma denote_ocfg_map_unfold bmap from l (b : LLVMAst.block dtyp) :
    RM.find l bmap = Some b ->
    denote_ocfg_map bmap va (from, l)
    ≈ (bd <- denote_block b from va;;
       match bd with
       | inr dv => Ret (inr dv)
       | inl l' => denote_ocfg_map bmap va (l, l')
       end).
  Proof.
    intros H. unfold denote_ocfg_map at 1. rewrite unfold_iter. cbn. rewrite H.
    rewrite Eqit.bind_bind. apply eutt_eq_bind. intros [l'|dv]; rewrite Eqit.bind_ret_l.
    - rewrite tau_eutt. reflexivity.
    - reflexivity.
  Qed.

  Lemma denote_ocfg_map_not_in bmap from l :
    RM.find l bmap = None ->
    denote_ocfg_map bmap va (from, l) ≈ Ret (inl (from, l)).
  Proof.
    intros H. unfold denote_ocfg_map. rewrite unfold_iter. cbn. rewrite H.
    rewrite Eqit.bind_ret_l. reflexivity.
  Qed.

  Lemma runs_ocfg_ret bmap from l b s s1 v :
    RM.find l bmap = Some b ->
    runs (denote_block b from va) s s1 (inr v) ->
    runs (denote_ocfg_map bmap va (from, l)) s s1 (inr v).
  Proof.
    intros H1 H2. eapply runs_eutt; [symmetry; apply denote_ocfg_map_unfold, H1|].
    eapply runs_bind; [exact H2|]. apply runs_ret.
  Qed.

  Lemma runs_ocfg_jump bmap from l b l' s s1 s2 r :
    RM.find l bmap = Some b ->
    runs (denote_block b from va) s s1 (inl l') ->
    runs (denote_ocfg_map bmap va (l, l')) s1 s2 r ->
    runs (denote_ocfg_map bmap va (from, l)) s s2 r.
  Proof.
    intros H1 H2 H3. eapply runs_eutt; [symmetry; apply denote_ocfg_map_unfold, H1|].
    eapply runs_bind; [exact H2|]. exact H3.
  Qed.

  Lemma oom_ocfg_block bmap from l b s :
    RM.find l bmap = Some b ->
    oom (denote_block b from va) s ->
    oom (denote_ocfg_map bmap va (from, l)) s.
  Proof.
    intros H1 H2. eapply oom_eutt; [symmetry; apply denote_ocfg_map_unfold, H1|].
    apply oom_bind_l, H2.
  Qed.

  Lemma oom_ocfg_jump bmap from l b l' s s1 :
    RM.find l bmap = Some b ->
    runs (denote_block b from va) s s1 (inl l') ->
    oom (denote_ocfg_map bmap va (l, l')) s1 ->
    oom (denote_ocfg_map bmap va (from, l)) s.
  Proof.
    intros H1 H2 H3. eapply oom_eutt; [symmetry; apply denote_ocfg_map_unfold, H1|].
    eapply oom_bind_r; [exact H2|exact H3].
  Qed.

  (** [denote_ocfg] is [denote_ocfg_map] of [ocfg_map]. *)
  Lemma denote_ocfg_eq (B : ocfg dtyp) :
    denote_ocfg B va = denote_ocfg_map (ocfg_map B) va.
  Proof. reflexivity. Qed.

  (** Looking a block up in a graph with distinct labels. *)
  Lemma find_block_NoDup (B : ocfg dtyp) (b : LLVMAst.block dtyp) :
    NoDup (map blk_id B) -> In b B -> find_block B (blk_id b) = Some b.
  Proof.
    induction B as [|b0 B IH]; intros ND Hin; [destruct Hin|].
    cbn in ND. inversion ND as [|? ? Hnin ND']; subst.
    destruct Hin as [<-|Hin].
    - apply find_block_eq. reflexivity.
    - rewrite find_block_ineq.
      + apply IH; auto.
      + intros E. apply Hnin. rewrite E. apply in_map, Hin.
  Qed.

  Lemma find_ocfg_map (B : ocfg dtyp) (b : LLVMAst.block dtyp) :
    NoDup (map blk_id B) -> In b B -> RM.find (blk_id b) (ocfg_map B) = Some b.
  Proof. intros. rewrite ocfg_map_find_block. apply find_block_NoDup; auto. Qed.

  Lemma find_ocfg_map_cons (b : LLVMAst.block dtyp) (B : ocfg dtyp) :
    RM.find (blk_id b) (ocfg_map (b :: B)) = Some b.
  Proof. rewrite ocfg_map_find_block. apply find_block_eq. reflexivity. Qed.

  (* ---------------------------------------------------------------- *)
  (** ** Phi nodes *)

  Lemma runs_phi from id dt args md op v st sf stk g :
    assoc from args = Some op ->
    exp_eval st sf stk g (Some dt) op v ->
    runs (denote_phi from (id, Phi dt args, md)) (st, ((sf, stk), g)) (st, ((sf, stk), g)) (id, v).
  Proof.
    intros H1 H2. cbn [denote_phi]. rewrite H1.
    eapply runs_bind; [apply exp_eval_mrec, H2|]. apply runs_ret.
  Qed.

  Lemma runs_map_monad_phis from phis ivs s :
    Forall2 (fun ph iv => runs (denote_phi from ph) s s iv) phis ivs ->
    runs (map_monad (denote_phi from) phis) s s ivs.
  Proof.
    induction 1 as [|ph iv phis ivs H HF IH].
    - cbn. apply runs_ret.
    - cbn [map_monad]. eapply runs_bind; [exact H|]. eapply runs_bind; [exact IH|]. apply runs_ret.
  Qed.

  Definition phi_upd (ivs : list (local_id * dvalue)) (m : local_env) : local_env :=
    fold_left (fun m '(id, v) => Maps.add id v m) ivs m.

  Lemma runs_lwrites ivs st sf stk g :
    runs (map_monad (fun '(id, dv) => lwrite id dv) ivs) (st, ((sf, stk), g))
         (st, ((upd_local_sf sf (phi_upd ivs (stack_vars sf)), stk), g)) (map (fun _ => tt) ivs).
  Proof.
    revert sf. induction ivs as [|[id v] ivs IH]; intros sf.
    - cbn. rewrite upd_local_sf_id. apply runs_ret.
    - cbn [map_monad map]. eapply runs_bind; [apply runs_lwrite|].
      eapply runs_bind; [apply IH|]. unfold phi_upd. cbn [fold_left].
      rewrite stack_vars_upd, upd_local_sf_twice. apply runs_ret.
  Qed.

  Lemma runs_phis from phis ivs st sf stk g :
    Forall2 (fun ph iv => runs (denote_phi from ph) (st, ((sf, stk), g)) (st, ((sf, stk), g)) iv)
            phis ivs ->
    runs (denote_phis from phis) (st, ((sf, stk), g))
         (st, ((upd_local_sf sf (phi_upd ivs (stack_vars sf)), stk), g)) tt.
  Proof.
    intros H. unfold denote_phis.
    eapply runs_bind; [apply runs_map_monad_phis, H|].
    eapply runs_bind; [apply runs_lwrites|]. apply runs_ret.
  Qed.

  Lemma runs_phis_nil from s : runs (denote_phis from []) s s tt.
  Proof.
    destruct s as [st [[sf stk] g]].
    pose proof (runs_phis from [] [] st sf stk g (Forall2_nil _)) as H.
    unfold phi_upd in H. cbn [fold_left] in H. rewrite upd_local_sf_id in H. exact H.
  Qed.

  (** The emitter's safepoint phis, after type conversion ([cblock_eq]). *)
  Fixpoint phi_list_d (env : nenv) (seed : positive) (chk gc : block_id) (i : nat) (rs : list positive)
    : list (local_id * phi dtyp * list (metadata dtyp)) :=
    match rs with
    | [] => []
    | r :: rs' =>
        (ssname seed (2000 + i),
         Phi (DTYPE_I 64 : dtyp) [(chk, EXP_Ident (ID_Local (env r)));
                                  (gc, EXP_Ident (ID_Local (ssname seed (1000 + i))))],
         @nil (metadata dtyp))
          :: phi_list_d env seed chk gc (S i) rs'
    end.

  Lemma cphi_list env seed chk gc i rs :
    map (fun '(id, ph, md) => (id, tfmap cty ph, tfmap cty md)) (phi_list env seed chk gc i rs)
    = phi_list_d env seed chk gc i rs.
  Proof.
    revert i. induction rs as [|r rs IH]; intros i; cbn [phi_list phi_list_d map]; [reflexivity|].
    rewrite IH. f_equal. rewrite cphi_eq. cbn. rewrite cty_val. reflexivity.
  Qed.

  (** The phi results: [ssname seed (2000+i) ↦ v_i]. *)
  Fixpoint phi_ivs (seed : positive) (i : nat) (vs : list dvalue) : list (local_id * dvalue) :=
    match vs with
    | [] => []
    | v :: vs' => (ssname seed (2000 + i), v) :: phi_ivs seed (S i) vs'
    end.

  Lemma runs_phi_list_chk env seed chk gc i rs vs st sf stk g :
    Forall2 (fun r v => RM.find (env r) (stack_vars sf) = Some v) rs vs ->
    runs (denote_phis chk (phi_list_d env seed chk gc i rs)) (st, ((sf, stk), g))
         (st, ((upd_local_sf sf (phi_upd (phi_ivs seed i vs) (stack_vars sf)), stk), g)) tt.
  Proof.
    intros HF. apply runs_phis. revert i. induction HF as [|r v rs vs H HF IH]; intros i.
    - constructor.
    - cbn [phi_list_d phi_ivs]. constructor; [|apply IH].
      eapply runs_phi; [apply assoc_hd|]. apply exp_eval_local, H.
  Qed.

  Lemma runs_phi_list_gc env seed chk gc i rs vs st sf stk g :
    chk <> gc ->
    Forall2 (fun j v => RM.find (ssname seed (1000 + j)) (stack_vars sf) = Some v)
            (seq i (length rs)) vs ->
    runs (denote_phis gc (phi_list_d env seed chk gc i rs)) (st, ((sf, stk), g))
         (st, ((upd_local_sf sf (phi_upd (phi_ivs seed i vs) (stack_vars sf)), stk), g)) tt.
  Proof.
    intros Hne HF. apply runs_phis.
    revert i vs HF. induction rs as [|r rs IH]; intros i vs HF; cbn [length seq] in HF;
      inversion HF; subst; clear HF.
    - constructor.
    - cbn [phi_list_d phi_ivs]. constructor; [|apply IH; auto].
      eapply runs_phi; [|apply exp_eval_local; eassumption].
      rewrite assoc_tl by (intros E; apply Hne; auto). apply assoc_hd.
  Qed.

  (* ---------------------------------------------------------------- *)
  (** ** Terminators *)

  Lemma term_ret iid dt e v md st sf stk g :
    exp_eval st sf stk g (Some dt) e v ->
    runs (denote_terminator (iid, TERM_Ret (dt, e), md)) (st, ((sf, stk), g)) (st, ((sf, stk), g)) (inr v).
  Proof.
    intros H. cbn [denote_terminator]. eapply runs_bind; [apply exp_eval_mrec, H|]. apply runs_ret.
  Qed.

  Lemma term_br_1 iid l md s :
    runs (denote_terminator (iid, TERM_Br_1 l, md)) s s (inl l).
  Proof. cbn [denote_terminator]. apply runs_ret. Qed.

  Lemma term_br iid e b l1 l2 md st sf stk g :
    exp_eval st sf stk g (Some (DTYPE_I 1 : dtyp)) e (I1 b) ->
    runs (denote_terminator (iid, TERM_Br (DTYPE_I 1 : dtyp, e) l1 l2, md))
         (st, ((sf, stk), g)) (st, ((sf, stk), g)) (inl (if b then l1 else l2)).
  Proof.
    intros H. cbn [denote_terminator]. eapply runs_bind; [apply exp_eval_mrec, H|].
    destruct b; cbn; apply runs_ret.
  Qed.

  (** The destination of a switch on [z]: the first branch whose 64-bit
      literal equals [z] modulo [2^64], else the default. *)
  Fixpoint switch_dest (z : Z) (d : block_id) (brs : list (tint_literal * block_id)) : block_id :=
    match brs with
    | [] => d
    | (TInt_Literal _ x, l) :: rest =>
        if Z.eqb (z mod 2^64) (denote_int_syntax x mod 2^64) then l else switch_dest z d rest
    end.

  Definition lit64 (br : tint_literal * block_id) : Prop :=
    match br with (TInt_Literal sz _, _) => sz = 64%positive end.

  Lemma switch_lits brs :
    map_monad (fun '((TInt_Literal sz x, id) : tint_literal * block_id) =>
                 s <- coerce_integer_to_int (Some sz) (denote_int_syntax x);;
                 ret (DVALUE_Base s, id)) brs
    = ret (map (fun '((TInt_Literal sz x, id) : tint_literal * block_id) =>
                  (DVALUE_Base (DVALUE_I sz (Integers.repr (denote_int_syntax x))), id)) brs).
  Proof.
    apply map_monad_EOU_Forall2. induction brs as [|[[sz x] l] brs IH]; constructor; auto.
  Qed.

  Lemma select_switch_dest z d brs :
    Forall lit64 brs ->
    select_switch (I64 z) d
      (map (fun '((TInt_Literal sz x, id) : tint_literal * block_id) =>
              (DVALUE_Base (DVALUE_I sz (Integers.repr (denote_int_syntax x))), id)) brs)
    = ret (switch_dest z d brs).
  Proof.
    induction 1 as [|[[sz x] l] brs H HF IH]; [reflexivity|].
    cbn in H. subst sz. cbn [map switch_dest].
    unfold I64. cbn -[Z.pow Z.modulo denote_int_syntax]. rewrite int_eq64.
    destruct (_ =? _); [reflexivity|exact IH].
  Qed.

  Lemma dvalue_is_poison_I64 z : dvalue_is_poison (I64 z) = false.
  Proof. reflexivity. Qed.

  Lemma term_switch iid e z d brs md st sf stk g :
    Forall lit64 brs ->
    exp_eval st sf stk g (Some (DTYPE_I 64 : dtyp)) e (I64 z) ->
    runs (denote_terminator (iid, TERM_Switch (DTYPE_I 64 : dtyp, e) d brs, md))
         (st, ((sf, stk), g)) (st, ((sf, stk), g)) (inl (switch_dest z d brs)).
  Proof.
    intros HF H. cbn [denote_terminator]. eapply runs_bind; [apply exp_eval_mrec, H|].
    rewrite dvalue_is_poison_I64. cbn beta iota. rewrite switch_lits. cbn [bind ret EOU_monad].
    rewrite select_switch_dest by exact HF.
    cbn [EOU_to_itree]. eapply runs_bind; [apply runs_ret|]. apply runs_ret.
  Qed.

  (** The emitter's branch tables: literals [TInt_Literal 64 (Nat.to_num_int k)]. *)
  Lemma lit64_nat k l : lit64 (TInt_Literal 64 (Nat.to_num_int k), l).
  Proof. reflexivity. Qed.

  Lemma switch_dest_nat z d k l rest :
    0 <= z < 2^64 -> Z.of_nat k < 2^64 ->
    switch_dest z d ((TInt_Literal 64 (Nat.to_num_int k), l) :: rest)
    = if Z.eqb z (Z.of_nat k) then l else switch_dest z d rest.
  Proof.
    intros Hz Hk. cbn [switch_dest]. rewrite denote_int_syntax_nat.
    rewrite !Z.mod_small by lia. reflexivity.
  Qed.

  (* ---------------------------------------------------------------- *)
  (** ** Instructions *)

  Notation i64 := (DTYPE_I 64 : dtyp) (only parsing).
  Notation dptr := (DTYPE_Pointer : dtyp) (only parsing).

  Lemma runs_freeze_base (v : dvalue_base) s :
    (forall dt, v <> DVALUE_Poison dt) -> runs (freeze (DVALUE_Base v)) s s (DVALUE_Base v).
  Proof.
    intros Hp. cbn [freeze freeze_base]. destruct v; try (exfalso; eapply Hp; reflexivity);
      unfold ITree.map; (eapply runs_bind; [apply runs_ret|]); apply runs_ret.
  Qed.

  (** (I1) [x = load i64, ptr e] *)
  Lemma instr_load_word x e q w st sf stk g :
    exp_eval st sf stk g (Some dptr) e (Ptr q) ->
    reads_word st q w ->
    runs (denote_instr (IId x, INSTR_Load i64 (dptr, e) [], []) va)
         (st, ((sf, stk), g)) (st, ((upd_local_sf sf (Maps.add x (I64 w) (stack_vars sf)), stk), g)) tt.
  Proof.
    intros He Hr. cbn [denote_instr]. eapply runs_bind; [apply exp_eval_mrec, He|].
    eapply runs_bind; [apply runs_memory; cbn [handle_memoryM]; apply reads_word_runs, Hr|].
    eapply runs_bind; [|apply runs_lwrite].
    apply runs_freeze_base. discriminate.
  Qed.

  (** (I2) [x = load ptr, ptr e] *)
  Lemma instr_load_ptr x e q q' st sf stk g :
    exp_eval st sf stk g (Some dptr) e (Ptr q) ->
    reads_ptr st q q' ->
    runs (denote_instr (IId x, INSTR_Load dptr (dptr, e) [], []) va)
         (st, ((sf, stk), g)) (st, ((upd_local_sf sf (Maps.add x (Ptr q') (stack_vars sf)), stk), g)) tt.
  Proof.
    intros He Hr. cbn [denote_instr]. eapply runs_bind; [apply exp_eval_mrec, He|].
    eapply runs_bind; [apply runs_memory; cbn [handle_memoryM]; apply reads_ptr_runs, Hr|].
    eapply runs_bind; [|apply runs_lwrite].
    apply runs_freeze_base. discriminate.
  Qed.

  (** (I3) stores.  What a write of one word at [q] guarantees about the rest
      of the memory. *)
  Definition write_post (st st' : state) (q : ptr) : Prop :=
    heap_of st' = heap_of st /\ frames_of st' = frames_of st /\
    state_provenance st' = state_provenance st /\
    (forall a, ~ (ptr_to_int q <= a < ptr_to_int q + 8) ->
          IntMaps.lookup a (mem_of st') = IntMaps.lookup a (mem_of st)) /\
    (forall p, writable_word st' p <-> writable_word st p) /\
    (forall p z, reads_word st p z ->
            ptr_to_int p + 8 <= ptr_to_int q \/ ptr_to_int q + 8 <= ptr_to_int p ->
            reads_word st' p z) /\
    (forall p p', reads_ptr st p p' ->
             ptr_to_int p + 8 <= ptr_to_int q \/ ptr_to_int q + 8 <= ptr_to_int p ->
             reads_ptr st' p p').

  Lemma write_dvalue_post st t q v st' u :
    sizeof_dtyp t = 8%N ->
    memS_runs st (write_dvalue t q v) st' u -> write_post st st' q.
  Proof.
    intros Hsz H.
    pose proof (write_dvalue_heap _ _ _ _ _ _ H) as (E1 & E2 & E3).
    pose proof (write_dvalue_runs _ _ _ _ _ _ H) as (_ & Hout & Haid & _).
    rewrite Hsz in Hout. cbn [Z.of_N] in Hout.
    assert (Hsame : forall p, ptr_to_int p + 8 <= ptr_to_int q \/ ptr_to_int q + 8 <= ptr_to_int p ->
                              same_bytes st st' (ptr_to_int p) 8).
    { intros p Hd a' Ha'. apply Hout. lia. }
    repeat split; auto.
    - intros W. eapply writable_word_aid; [exact W|]. intros; symmetry; apply Haid.
    - intros W. eapply writable_word_aid; [exact W|]. intros; apply Haid.
    - intros p z Hr Hd. eapply reads_word_frame; [exact Hr|]. apply Hsame, Hd.
    - intros p p' Hr Hd. eapply reads_ptr_frame; [exact Hr|]. apply Hsame, Hd.
  Qed.

  Lemma instr_store_run n dt ev ep v q st sf stk g st' :
    exp_eval st sf stk g (Some dt) ev v ->
    exp_eval st sf stk g (Some dptr) ep (Ptr q) ->
    memS_runs st (write_dvalue dt q v) st' tt ->
    runs (denote_instr (IVoid n, INSTR_Store (dt, ev) (dptr, ep) [], []) va)
         (st, ((sf, stk), g)) (st', ((sf, stk), g)) tt.
  Proof.
    intros Hv Hp Hw. cbn [denote_instr]. eapply runs_bind; [apply exp_eval_mrec, Hv|].
    eapply runs_bind; [apply exp_eval_mrec, Hp|].
    eapply runs_bind; [|apply runs_ret]. unfold Ptr. apply runs_memory. cbn [handle_memoryM]. exact Hw.
  Qed.

  (** [store i64 w, ptr q] *)
  Lemma instr_store_word n ev ep w q st sf stk g :
    exp_eval st sf stk g (Some i64) ev (I64 w) ->
    exp_eval st sf stk g (Some dptr) ep (Ptr q) ->
    writable_word st q ->
    exists st',
      runs (denote_instr (IVoid n, INSTR_Store (i64, ev) (dptr, ep) [], []) va)
           (st, ((sf, stk), g)) (st', ((sf, stk), g)) tt /\
      reads_word st' q w /\ write_post st st' q.
  Proof.
    intros Hv Hp Hw. destruct (Hw w) as (st' & Hrun & Hr).
    exists st'. split; [eapply instr_store_run; eauto|]. split; [exact Hr|].
    eapply write_dvalue_post; [apply sizeof_i64|exact Hrun].
  Qed.

  (** [store ptr p', ptr q]: the pointer read back has [p']'s address and
      wildcard provenance ([write_read_ptr]). *)
  Lemma instr_store_ptr n ev ep p' q st sf stk g :
    exp_eval st sf stk g (Some dptr) ev (Ptr p') ->
    exp_eval st sf stk g (Some dptr) ep (Ptr q) ->
    writable_word st q ->
    exists st' p'',
      runs (denote_instr (IVoid n, INSTR_Store (dptr, ev) (dptr, ep) [], []) va)
           (st, ((sf, stk), g)) (st', ((sf, stk), g)) tt /\
      reads_ptr st' q p'' /\ ptr_to_int p'' = ptr_to_int p' /\ ptr_provenance p'' = wildcard_prov /\
      write_post st st' q.
  Proof.
    intros Hv Hp Hw. apply writable_word_iff in Hw. destruct Hw as (ptrs & E & W).
    destruct (write_dvalue_exists st DTYPE_Pointer q (Ptr p') ptrs) as (st' & Hrun);
      [rewrite sizeof_ptr; exact E | exact W |].
    destruct (write_read_ptr _ _ _ _ _ Hrun) as (p'' & Hr & E1 & E2).
    exists st', p''. split; [eapply instr_store_run; eauto|].
    split; [exact Hr|]. split; [exact E1|]. split; [exact E2|].
    eapply write_dvalue_post; [apply sizeof_ptr|exact Hrun].
  Qed.

  (** (I4) [x = op e] *)
  Lemma instr_op x e v st sf stk g :
    exp_eval st sf stk g None e v ->
    runs (denote_instr (IId x, INSTR_Op e, []) va)
         (st, ((sf, stk), g)) (st, ((upd_local_sf sf (Maps.add x v (stack_vars sf)), stk), g)) tt.
  Proof.
    intros He. cbn [denote_instr]. eapply runs_bind; [apply exp_eval_mrec, He|].
    eapply runs_bind; [apply runs_lwrite|]. apply runs_ret.
  Qed.

  (** (I6) calls.  Argument evaluation. *)
  Lemma runs_map_monad_exps (tes : list (texp dtyp)) dvs st sf stk g :
    Forall2 (fun '(t, e) v => exp_eval st sf stk g (Some t) e v) tes dvs ->
    runs (map_monad (fun '(t, op) => denote_exp' (Some t) op) tes)
         (st, ((sf, stk), g)) (st, ((sf, stk), g)) dvs.
  Proof.
    induction 1 as [|[t e] v tes dvs H HF IH].
    - cbn. apply runs_ret.
    - cbn [map_monad]. eapply runs_bind; [apply exp_eval_mrec, H|].
      eapply runs_bind; [exact IH|]. apply runs_ret.
  Qed.

  Lemma gc_not_intrinsic :
    IntrinsicsDefinitions.intrinsic_exp (T := dtyp) (EXP_Ident (ID_Global (Name "garbage_collect"))) = None.
  Proof. vm_compute. reflexivity. Qed.

  Lemma not_intrinsic_global_anon n :
    IntrinsicsDefinitions.intrinsic_exp (T := dtyp) (EXP_Ident (ID_Global (Anon n))) = None.
  Proof. reflexivity. Qed.

  Lemma not_intrinsic_conv cv t1 e t2 :
    IntrinsicsDefinitions.intrinsic_exp (T := dtyp) (OP_Conversion cv t1 e t2) = None.
  Proof. reflexivity. Qed.

  Lemma not_intrinsic_local id :
    IntrinsicsDefinitions.intrinsic_exp (T := dtyp) (EXP_Ident (ID_Local id)) = None.
  Proof. reflexivity. Qed.

  (** [x = call dt ef(args)]: the callee runs through the knot. *)
  Lemma instr_call x dt ef args fp dvs st sf stk g st' sf' stk' g' v :
    IntrinsicsDefinitions.intrinsic_exp ef = None ->
    exp_eval st sf stk g None ef (Ptr fp) ->
    Forall2 (fun '(t, e) v => exp_eval st sf stk g (Some t) e v) (map fst args) dvs ->
    runs (ctx _ (Call dt (Ptr fp) dvs)) (st, ((sf, stk), g)) (st', ((sf', stk'), g')) (inr v) ->
    runs (denote_instr (IId x, INSTR_Call (dt, ef) args [] [], []) va) (st, ((sf, stk), g))
         (st', ((upd_local_sf sf' (Maps.add x v (stack_vars sf')), stk'), g')) tt.
  Proof.
    intros Hi He HF Hc. cbn [denote_instr]. rewrite Hi.
    eapply runs_bind; [apply runs_map_monad_exps, HF|].
    eapply runs_bind; [|apply runs_lwrite].
    eapply runs_bind; [apply exp_eval_mrec, He|].
    eapply runs_bind; [apply runs_call, Hc|]. cbn. apply runs_ret.
  Qed.

  Lemma oom_instr_call x dt ef args fp dvs st sf stk g :
    IntrinsicsDefinitions.intrinsic_exp ef = None ->
    exp_eval st sf stk g None ef (Ptr fp) ->
    Forall2 (fun '(t, e) v => exp_eval st sf stk g (Some t) e v) (map fst args) dvs ->
    oom (ctx _ (Call dt (Ptr fp) dvs)) (st, ((sf, stk), g)) ->
    oom (denote_instr (IId x, INSTR_Call (dt, ef) args [] [], []) va) (st, ((sf, stk), g)).
  Proof.
    intros Hi He HF Hc. cbn [denote_instr]. rewrite Hi.
    eapply oom_bind_r; [apply runs_map_monad_exps, HF|].
    apply oom_bind_l.
    eapply oom_bind_r; [apply exp_eval_mrec, He|].
    apply oom_bind_l. apply oom_call, Hc.
  Qed.

  (** [call void @garbage_collect(ptr tinfo)] *)
  Lemma instr_call_gc n e tinfo gp st sf stk g st' ls' g' rv :
    exp_eval st sf stk g (Some dptr) e (Ptr tinfo) ->
    RM.find (Name "garbage_collect") g = Some (Ptr gp) ->
    runs (ctx _ (Call DTYPE_Void (Ptr gp) [Ptr tinfo])) (st, ((sf, stk), g)) (st', (ls', g')) (inr rv) ->
    runs (denote_instr (IVoid n, INSTR_Call (DTYPE_Void : dtyp, EXP_Ident (ID_Global (Name "garbage_collect")))
                                   [((dptr, e), [])] [] [], []) va)
         (st, ((sf, stk), g)) (st', (ls', g')) tt.
  Proof.
    intros He Hg Hc. cbn [denote_instr]. rewrite gc_not_intrinsic.
    eapply runs_bind; [apply (runs_map_monad_exps [(dptr, e)] [Ptr tinfo]); constructor; [exact He|constructor]|].
    eapply runs_bind; [|apply runs_ret].
    eapply runs_bind; [apply exp_eval_mrec; apply exp_eval_global; exact Hg|].
    eapply runs_bind; [apply runs_call, Hc|]. cbn. apply runs_ret.
  Qed.

  Lemma oom_instr_call_gc n e tinfo gp st sf stk g :
    exp_eval st sf stk g (Some dptr) e (Ptr tinfo) ->
    RM.find (Name "garbage_collect") g = Some (Ptr gp) ->
    oom (ctx _ (Call DTYPE_Void (Ptr gp) [Ptr tinfo])) (st, ((sf, stk), g)) ->
    oom (denote_instr (IVoid n, INSTR_Call (DTYPE_Void : dtyp, EXP_Ident (ID_Global (Name "garbage_collect")))
                                  [((dptr, e), [])] [] [], []) va)
        (st, ((sf, stk), g)).
  Proof.
    intros He Hg Hc. cbn [denote_instr]. rewrite gc_not_intrinsic.
    eapply oom_bind_r; [apply (runs_map_monad_exps [(dptr, e)] [Ptr tinfo]); constructor; [exact He|constructor]|].
    apply oom_bind_l.
    eapply oom_bind_r; [apply exp_eval_mrec; apply exp_eval_global; exact Hg|].
    apply oom_bind_l. apply oom_call, Hc.
  Qed.

  (* ---------------------------------------------------------------- *)
  (** ** Allocation

      Every allocation of a non-void type either runs out of memory or runs
      ([allocate_dtyp_total]): the only failures on the way are [from_Z]
      overflows, which raise [raise_oom].  [alloc_post] collects what an
      [alloca] of [sz] bytes at [p] guarantees. *)


  Definition eou_ok {X} (c : EOU.EOU X) : Prop :=
    match c with EOU.raise_ret _ | EOU.raise_oom _ => True | _ => False end.

  Lemma eou_ok_map_monad_acc {A B} (f : A -> EOU.EOU B) :
    (forall a, eou_ok (f a)) ->
    forall l acc,
    eou_ok ((fix loop (acc : list B) (l : list A) : EOU.EOU (list B) :=
       match l with
       | [] => ret (rev_append acc [])
       | a :: l' => b <- f a;; loop (b :: acc) l'
       end) acc l).
  Proof.
    intros Hf l. induction l as [|a l IH]; intros acc; cbn; [exact I|].
    specialize (Hf a). destruct (f a); cbn in *; auto.
  Qed.

  Lemma eou_ok_map_monad {A B} (f : A -> EOU.EOU B) l :
    (forall a, eou_ok (f a)) -> eou_ok (map_monad f l).
  Proof.
    intros Hf. induction l as [|a l IH]; cbn; [exact I|].
    specialize (Hf a). destruct (f a); cbn in *; auto.
    destruct (map_monad f l); cbn in *; auto.
  Qed.

  Lemma eou_ok_int_to_ptr z pr : eou_ok (int_to_ptr z pr).
  Proof. cbn. unfold from_Z_bits. destruct (_ && _); exact I. Qed.

  Lemma eou_ok_gcp p n : eou_ok (get_consecutive_ptrs p n).
  Proof.
    unfold get_consecutive_ptrs, intptr_seq. rewrite seq_map_monad_acc_eq.
    assert (H : eou_ok (map_monad (from_Z ∘ Z.of_N) (Nseq 0 (N_to_nat_safe n)))).
    { apply eou_ok_map_monad. intros a. cbn. unfold from_Z_bits. destruct (_ && _); exact I. }
    destruct (map_monad _ _); cbn in *; auto.
    unfold map_monad_acc. apply eou_ok_map_monad_acc. intros ix. cbn.
    apply eou_ok_int_to_ptr.
  Qed.
  Definition memS_total {X} st (m : memM X) : Prop :=
    memS_oom st m \/ exists st' x, memS_runs_c st m st' x.

  Lemma memS_total_bind {X Y} st (m : memM X) (k : X -> memM Y) :
    memS_total st m -> (forall st1 x, memS_runs_c st m st1 x -> memS_total st1 (k x)) ->
    memS_total st (bind m k).
  Proof.
    intros [H|(st1 & x & H)] Hk.
    - left. apply memS_oom_bind_l, H.
    - destruct (Hk _ _ H) as [H'|(st2 & y & H')].
      + left. eapply memS_oom_bind_r; eauto.
      + right. exists st2, y. eapply memS_runs_c_bind; eauto.
  Qed.

  Lemma memS_total_lift {X} st (c : EOU.EOU X) : eou_ok c -> memS_total st (lift c).
  Proof.
    destruct c; cbn; intros H; try contradiction;
      first [left; constructor | right; do 2 eexists; constructor].
  Qed.

  Lemma allocate_dtyp_total st t n align :
    dtyp_eqb t DTYPE_Void = false -> memS_total st (allocate_dtyp t n align).
  Proof.
    intros Ht. unfold allocate_dtyp. rewrite Ht. unfold allocate_bytes.
    apply memS_total_bind; [right; do 2 eexists; constructor; constructor|].
    intros st1 pr _. unfold Allocate_bytes_with_pr.
    apply memS_total_bind.
    - unfold get_free_block.
      apply memS_total_bind; [right; do 2 eexists; constructor; constructor|].
      intros st2 a _.
      apply memS_total_bind; [apply memS_total_lift, eou_ok_int_to_ptr|].
      intros st3 p _.
      apply memS_total_bind; [apply memS_total_lift, eou_ok_gcp|].
      intros st4 ptrs _. right. do 2 eexists. constructor.
    - intros st2 [p ptrs] _. right.
      unfold add_block_to_stack, add_block, add_ptrs_to_frame, get_mem, upd_mem, app_mem, app_mem_stack.
      cbn. do 2 eexists. repeat econstructor.
  Qed.
  Definition alloc_post (st st' : state) (sz : N) (p : ptr) : Prop :=
    heap_of st' = heap_of st /\
    (exists ptrs, consec p ptrs /\ length ptrs = N.to_nat sz /\
             frames_of st' = push_top ptrs (frames_of st)) /\
    (forall a, ptr_to_int p <= a -> IntMaps.lookup a (mem_of st) = None) /\
    (forall a, a < ptr_to_int p \/ ptr_to_int p + Z.of_N sz <= a ->
          IntMaps.lookup a (mem_of st') = IntMaps.lookup a (mem_of st)) /\
    (forall q, ptr_provenance q = ptr_provenance p ->
          ptr_to_int p <= ptr_to_int q < ptr_to_int p + Z.of_N sz -> writable_at st' q).

  Lemma allocate_dtyp_post st t st' p :
    memS_runs_c st (allocate_dtyp t 1 8) st' p -> alloc_post st st' (sizeof_dtyp t) p.
  Proof.
    intros H. apply allocate_dtyp_runs in H.
    rewrite N.mul_1_l in H. destruct H as (H1 & H2 & _ & H3 & H4 & H5).
    unfold alloc_post. auto.
  Qed.

  Lemma alloc_post_old st st' sz p a v :
    alloc_post st st' sz p -> IntMaps.lookup a (mem_of st) = Some v ->
    IntMaps.lookup a (mem_of st') = Some v.
  Proof.
    intros (_ & _ & Hf & Ho & _) Hv. rewrite Ho; [exact Hv|].
    left. destruct (Z_lt_le_dec a (ptr_to_int p)) as [?|Hle]; [assumption|].
    rewrite (Hf a Hle) in Hv. discriminate.
  Qed.

  Lemma alloc_not_heap st st' sz p :
    alloc_post st st' sz p ->
    (forall a, in_heap st a -> IntMaps.lookup a (mem_of st) <> None) ->
    forall a, ptr_to_int p <= a -> ~ in_heap st' a.
  Proof.
    intros (Hh & _ & Hf & _) Hm a Ha Hin. unfold in_heap in Hin. rewrite Hh in Hin.
    apply (Hm a Hin). apply Hf, Ha.
  Qed.


  Definition alloca_locals (sf : stack_frame) (x : raw_id) (p : ptr) : stack_frame :=
    upd_local_sf sf (Maps.add x (DVALUE_Base (DVALUE_Pointer p)) (stack_vars sf)).

  Lemma instr_alloca_eq x dt :
    denote_instr (IId x, INSTR_Alloca dt [], []) va ≈
    (v <- trigger (Alloca dt 1 None);; lwrite x v;; ret tt).
  Proof.
    cbn [denote_instr find]. rewrite bind_bind. apply eutt_eq_bind. intros v. reflexivity.
  Qed.

  Lemma instr_alloca x dt st sf stk g st' p :
    memS_runs_c st (allocate_dtyp dt 1 8) st' p ->
    runs (denote_instr (IId x, INSTR_Alloca dt [], []) va) (st, ((sf, stk), g))
         (st', ((alloca_locals sf x p, stk), g)) tt.
  Proof.
    intros H. eapply runs_eutt; [symmetry; apply instr_alloca_eq|].
    eapply runs_bind; [apply runs_memory_c; cbn [handle_memoryM]; eapply memS_runs_c_bind; [exact H|constructor]|].
    eapply runs_bind; [apply runs_lwrite|]. apply runs_ret.
  Qed.
  Lemma oom_instr_alloca x dt st sf stk g :
    memS_oom st (allocate_dtyp dt 1 8) ->
    oom (denote_instr (IId x, INSTR_Alloca dt [], []) va) (st, ((sf, stk), g)).
  Proof.
    intros H. eapply oom_eutt; [symmetry; apply instr_alloca_eq|].
    apply oom_bind_l. apply oom_memory. cbn [handle_memoryM]. apply memS_oom_bind_l, H.
  Qed.

  (** An [alloca] of a non-void type either runs out of memory or binds [x]
      to a fresh block of the current memory frame. *)
  Lemma instr_alloca_cases x dt st sf stk g :
    dtyp_eqb dt DTYPE_Void = false ->
    oom (denote_instr (IId x, INSTR_Alloca dt [], []) va) (st, ((sf, stk), g)) \/
    exists st' p,
      runs (denote_instr (IId x, INSTR_Alloca dt [], []) va) (st, ((sf, stk), g))
           (st', ((alloca_locals sf x p, stk), g)) tt /\
      alloc_post st st' (sizeof_dtyp dt) p.
  Proof.
    intros Ht. destruct (allocate_dtyp_total st dt 1 8 Ht) as [H|(st' & p & H)].
    - left. apply oom_instr_alloca, H.
    - right. exists st', p. split; [apply instr_alloca, H|apply allocate_dtyp_post, H].
  Qed.

  (** The two allocas of the emitter: the root array [alloca [n x i64]] and the
      shadow-stack frame [alloca {ptr, ptr, ptr}]. *)
  Lemma sizeof_arr_i64 n : sizeof_dtyp (DTYPE_Array false n i64) = (8 * n)%N.
  Proof. cbn. rewrite N.mul_comm. destruct n; reflexivity. Qed.

  Lemma sizeof_frame : sizeof_dtyp (DTYPE_Struct false [dptr; dptr; dptr]) = 24%N.
  Proof. reflexivity. Qed.

  Lemma instr_alloca_arr_cases x n st sf stk g :
    oom (denote_instr (IId x, INSTR_Alloca (DTYPE_Array false n i64) [], []) va) (st, ((sf, stk), g)) \/
    exists st' p,
      runs (denote_instr (IId x, INSTR_Alloca (DTYPE_Array false n i64) [], []) va) (st, ((sf, stk), g))
           (st', ((alloca_locals sf x p, stk), g)) tt /\
      alloc_post st st' (8 * n) p.
  Proof. rewrite <- sizeof_arr_i64. apply instr_alloca_cases. reflexivity. Qed.

  Lemma instr_alloca_frame_cases x st sf stk g :
    oom (denote_instr (IId x, INSTR_Alloca (DTYPE_Struct false [dptr; dptr; dptr]) [], []) va)
        (st, ((sf, stk), g)) \/
    exists st' p,
      runs (denote_instr (IId x, INSTR_Alloca (DTYPE_Struct false [dptr; dptr; dptr]) [], []) va)
           (st, ((sf, stk), g)) (st', ((alloca_locals sf x p, stk), g)) tt /\
      alloc_post st st' 24 p.
  Proof. rewrite <- sizeof_frame. apply instr_alloca_cases. reflexivity. Qed.
  Lemma alloc_post_allocated st st' sz p a :
    alloc_post st st' sz p -> IntMaps.lookup a (mem_of st) <> None ->
    IntMaps.lookup a (mem_of st') = IntMaps.lookup a (mem_of st).
  Proof.
    intros H Ha. destruct (IntMaps.lookup a (mem_of st)) as [v|] eqn:E; [|congruence].
    eapply alloc_post_old; eauto.
  Qed.

  Lemma consec_cover p ptrs a :
    consec p ptrs -> ptr_to_int p <= a < ptr_to_int p + Z.of_nat (length ptrs) ->
    exists q, In q ptrs /\ ptr_to_int q = a.
  Proof.
    intros C Ha. destruct (nth_error ptrs (Z.to_nat (a - ptr_to_int p))) as [q|] eqn:E.
    - exists q. split; [eapply nth_error_In; eauto|].
      destruct (C _ _ E) as [-> _]. lia.
    - apply nth_error_None in E. lia.
  Qed.

  Lemma alloc_post_read st st' sz p t q v :
    alloc_post st st' sz p -> memS_returns st (read_dvalue t q) v ->
    memS_returns st' (read_dvalue t q) v.
  Proof.
    intros Hp (st0 & H). pose proof H as H'.
    apply read_dvalue_runs in H. destruct H as (-> & ptrs & bs & Eg & HF & _).
    apply read_dvalue_frame in H'. destruct H' as [_ H']. exists st'. apply H'.
    apply gcp_spec in Eg. destruct Eg as [L C].
    intros a Ha. apply (alloc_post_allocated _ _ _ _ _ Hp).
    destruct (consec_cover q ptrs a C) as (q' & Hin & <-); [rewrite L; lia|].
    destruct (Forall2_In_l _ _ _ _ HF Hin) as (b & _ & aid & Eb & _). congruence.
  Qed.

  Lemma alloc_post_reads_word st st' sz p q z :
    alloc_post st st' sz p -> reads_word st q z -> reads_word st' q z.
  Proof. apply alloc_post_read. Qed.

  Lemma alloc_post_reads_ptr st st' sz p q q' :
    alloc_post st st' sz p -> reads_ptr st q q' -> reads_ptr st' q q'.
  Proof. apply alloc_post_read. Qed.

  Lemma alloc_post_writable_word st st' sz p q :
    alloc_post st st' sz p -> writable_word st q -> writable_word st' q.
  Proof.
    intros Hp W. eapply writable_word_aid; [exact W|].
    rewrite writable_word_iff in W. destruct W as (ptrs & Eg & W).
    apply gcp_spec in Eg. destruct Eg as [L C].
    intros a Ha. destruct (consec_cover q ptrs a C) as (q' & Hin & <-); [rewrite L, N_nat_Z; lia|].
    destruct (W q' Hin) as (aid & Ea & _). unfold aid_at in *.
    rewrite (alloc_post_allocated _ _ _ _ _ Hp); [reflexivity|].
    destruct (IntMaps.lookup (ptr_to_int q') (mem_of st)); cbn in Ea; congruence.
  Qed.

  (* ---------------------------------------------------------------- *)
  (** ** Straight-line store and load sequences

      [stores_run] runs a sequence of word stores whose operands evaluate
      independently of memory; [spill_code_run], [store_fields_run] and
      [reload_code_run] instantiate it (resp. [instr_load_word]) for the
      emitter's helper sequences.  Slots are [p + 8*i], [p + 8*(i+1)], ...
      ([slot_ptrs], [slots_ok]); [writes_post] is [write_post] for a list
      of written words. *)

  Lemma ptr_off_to_int p off q : ptr_off p off q -> ptr_to_int q = ptr_to_int p + off.
  Proof. unfold ptr_off. intros H. eapply ptr_to_int_int_to_ptr; eauto. Qed.

  Lemma rfind_add_eq (id : raw_id) (v : dvalue) (m : local_env) : RM.find id (Maps.add id v m) = Some v.
  Proof. apply RMF.F.add_eq_o. reflexivity. Qed.

  Lemma rfind_add_neq (id id' : raw_id) (v : dvalue) (m : local_env) :
    id <> id' -> RM.find id' (Maps.add id v m) = RM.find id' m.
  Proof. intros H. apply RMF.F.add_neq_o. exact H. Qed.

  Definition disj8 (p q : ptr) : Prop :=
    ptr_to_int p + 8 <= ptr_to_int q \/ ptr_to_int q + 8 <= ptr_to_int p.

  (** What a sequence of word stores to [qs] guarantees. *)
  Definition writes_post (st st' : state) (qs : list ptr) : Prop :=
    heap_of st' = heap_of st /\ frames_of st' = frames_of st /\
    state_provenance st' = state_provenance st /\
    (forall a, Forall (fun q => ~ (ptr_to_int q <= a < ptr_to_int q + 8)) qs ->
          IntMaps.lookup a (mem_of st') = IntMaps.lookup a (mem_of st)) /\
    (forall p, writable_word st' p <-> writable_word st p) /\
    (forall p z, reads_word st p z -> Forall (disj8 p) qs -> reads_word st' p z) /\
    (forall p p', reads_ptr st p p' -> Forall (disj8 p) qs -> reads_ptr st' p p').

  Lemma writes_post_nil st : writes_post st st [].
  Proof. repeat split; auto; tauto. Qed.

  Lemma writes_post_cons st st1 st2 q qs :
    write_post st st1 q -> writes_post st1 st2 qs -> writes_post st st2 (q :: qs).
  Proof.
    intros (H1 & H2 & H3 & H4 & H5 & H6 & H7) (K1 & K2 & K3 & K4 & K5 & K6 & K7).
    repeat split; try congruence.
    - intros a Ha. inversion Ha; subst. rewrite K4, H4; auto.
    - intros W. apply H5, K5, W.
    - intros W. apply K5, H5, W.
    - intros p z R Hd. inversion Hd; subst. apply K6; auto.
    - intros p p' R Hd. inversion Hd; subst. apply K7; auto.
  Qed.

  (** A straight-line sequence of word stores [*ep := ev] whose operands
      evaluate independently of memory. *)
  Inductive stores (sf : stack_frame) (stk : stack) (g : global_env) :
    code dtyp -> list (ptr * Z) -> Prop :=
  | stores_nil : stores sf stk g [] []
  | stores_cons n ev ep w q c l :
      (forall st0, exp_eval st0 sf stk g (Some i64) ev (I64 w)) ->
      (forall st0, exp_eval st0 sf stk g (Some dptr) ep (Ptr q)) ->
      stores sf stk g c l ->
      stores sf stk g ((IVoid n, INSTR_Store (i64, ev) (dptr, ep) [], []) :: c) ((q, w) :: l).

  Lemma stores_run sf stk g c l st :
    stores sf stk g c l ->
    Forall (fun qw => writable_word st (fst qw)) l ->
    ForallOrdPairs (fun a b => disj8 (fst a) (fst b)) l ->
    exists st',
      runs (denote_code c va) (st, ((sf, stk), g)) (st', ((sf, stk), g)) tt /\
      writes_post st st' (map fst l) /\
      Forall (fun qw => reads_word st' (fst qw) (snd qw)) l.
  Proof.
    intros H. revert st. induction H as [|n ev ep w q c l Hv Hp Hc IH]; intros st W D.
    - exists st. split; [apply runs_code_nil|split; [apply writes_post_nil|constructor]].
    - inversion W as [|? ? Wq Wl]; subst. inversion D as [|? ? Dq Dl]; subst.
      destruct (instr_store_word n ev ep w q st sf stk g (Hv st) (Hp st) Wq)
        as (st1 & R1 & Rq & P1).
      destruct (IH st1) as (st2 & R2 & P2 & Rl); [|exact Dl|].
      { eapply Forall_impl; [|exact Wl]. intros [q' w'] Wq'. apply P1, Wq'. }
      exists st2. split; [eapply runs_code_cons; eauto|split; [eapply writes_post_cons; eauto|]].
      constructor; [|exact Rl]. cbn. apply P2; [exact Rq|].
      rewrite Forall_forall in Dq |- *. intros q' Hin. apply in_map_iff in Hin.
      destruct Hin as ([q'' w''] & <- & Hin). apply (Dq _ Hin).
  Qed.

  (** Consecutive 8-byte slots [p + 8*i], [p + 8*(i+1)], ... *)
  Fixpoint slot_ptrs (p : ptr) (i : nat) (qs : list ptr) : Prop :=
    match qs with
    | [] => True
    | q :: qs' => ptr_off p (8 * Z.of_nat i) q /\ slot_ptrs p (S i) qs'
    end.

  (** [P] holds of the slot [p + 8*(i+k)] and the [k]-th word of [ws]. *)
  Fixpoint slots_ok (P : ptr -> Z -> Prop) (p : ptr) (i : nat) (ws : list Z) : Prop :=
    match ws with
    | [] => True
    | w :: ws' => (exists q, ptr_off p (8 * Z.of_nat i) q /\ P q w) /\ slots_ok P p (S i) ws'
    end.

  Lemma slot_ptrs_ge p i qs :
    slot_ptrs p i qs -> Forall (fun q => ptr_to_int p + 8 * Z.of_nat i <= ptr_to_int q) qs.
  Proof.
    revert i. induction qs as [|q qs IH]; intros i H; constructor.
    - destruct H as [H _]. apply ptr_off_to_int in H. lia.
    - destruct H as [_ H]. eapply Forall_impl; [|apply IH, H]. intros q'. cbn beta. lia.
  Qed.

  Lemma slot_ptrs_disj {B} p i qs (ws : list B) :
    slot_ptrs p i qs -> ForallOrdPairs (fun a b => disj8 (fst a) (fst b)) (combine qs ws).
  Proof.
    revert i ws. induction qs as [|q qs IH]; intros i ws H; [constructor|].
    destruct ws as [|w ws]; [constructor|]. destruct H as [Hq H]. cbn. constructor.
    - apply ptr_off_to_int in Hq. pose proof (slot_ptrs_ge _ _ _ H) as G.
      assert (G' : Forall (fun q' => disj8 q q') qs).
      { eapply Forall_impl; [|exact G]. intros q'. unfold disj8. cbn beta. lia. }
      clear -G'. revert ws. induction G' as [|q' qs D G' IHG]; intros [|w' ws]; constructor; auto.
    - eapply IH, H.
  Qed.

  Lemma slots_ok_ptrs (P : ptr -> Z -> Prop) p i ws :
    slots_ok P p i ws ->
    exists qs, slot_ptrs p i qs /\ length qs = length ws /\
          Forall (fun qw => P (fst qw) (snd qw)) (combine qs ws).
  Proof.
    revert i. induction ws as [|w ws IH]; intros i H.
    - exists []. repeat constructor.
    - destruct H as ((q & Hq & Pq) & H). destruct (IH _ H) as (qs & S & L & F).
      exists (q :: qs). cbn. auto.
  Qed.

  Lemma ptr_off_det p off q q' : ptr_off p off q -> ptr_off p off q' -> q = q'.
  Proof. unfold ptr_off. congruence. Qed.

  Lemma slots_ok_of_ptrs (P : ptr -> Z -> Prop) p i qs ws :
    slot_ptrs p i qs -> length qs = length ws ->
    Forall (fun qw => P (fst qw) (snd qw)) (combine qs ws) -> slots_ok P p i ws.
  Proof.
    revert i ws. induction qs as [|q qs IH]; intros i ws S L F; destruct ws as [|w ws];
      try discriminate; [exact I|].
    destruct S as [Hq S]. inversion F; subst. split; [exists q; auto|].
    eapply IH; eauto.
  Qed.

  Lemma slots_ok_ptrs_all (P : ptr -> Z -> Prop) p i qs ws :
    slots_ok P p i ws -> slot_ptrs p i qs -> length qs = length ws ->
    Forall (fun qw => P (fst qw) (snd qw)) (combine qs ws).
  Proof.
    revert i ws. induction qs as [|q qs IH]; intros i ws H S L; destruct ws as [|w ws];
      try discriminate; constructor.
    - destruct H as ((q' & Hq' & Pq) & _). cbn. rewrite (ptr_off_det _ _ _ _ (proj1 S) Hq'). exact Pq.
    - eapply IH; [apply H|apply S|cbn in L; injection L; auto].
  Qed.

  Lemma map_fst_combine {A B} (l : list A) (l' : list B) :
    length l = length l' -> map fst (combine l l') = l.
  Proof.
    revert l'. induction l as [|a l IH]; intros [|b l'] L; cbn in *; try discriminate; auto.
    rewrite IH; auto.
  Qed.

  (** [spill_code]: store the roots [rs] (locals [env r]) into the slots
      [i, i+1, ...] of the [alloca]'d root array [rootsp]. *)
  Lemma spill_code_run env rootsp n i rs ws p st sf stk g :
    (forall st0, exp_eval st0 sf stk g (Some dptr) (cexp rootsp) (Ptr p)) ->
    Forall2 (fun r w => RM.find (env r) (stack_vars sf) = Some (I64 w)) rs ws ->
    Z.of_nat (i + length rs) < 2^63 ->
    slots_ok (fun q _ => writable_word st q) p i ws ->
    exists st' qs,
      runs (denote_code (ccode (spill_code env rootsp (TYPE_Array n val_ty) i rs)) va)
           (st, ((sf, stk), g)) (st', ((sf, stk), g)) tt /\
      slot_ptrs p i qs /\ length qs = length ws /\ writes_post st st' qs /\
      slots_ok (fun q w => reads_word st' q w) p i ws.
  Proof.
    intros Hp Hrs Hi W.
    destruct (slots_ok_ptrs _ _ _ _ W) as (qs & S & L & Wq).
    assert (Hs : stores sf stk g (ccode (spill_code env rootsp (TYPE_Array n val_ty) i rs))
                        (combine qs ws)).
    { clear W Wq. revert i qs ws Hrs Hi S L. induction rs as [|r rs IH]; intros i qs ws Hrs Hi S L.
      - inversion Hrs; subst. destruct qs; [|discriminate]. rewrite ccode_spill_nil. constructor.
      - inversion Hrs as [|? w ? ws' Hr Hrs']; subst. destruct qs as [|q qs]; [discriminate|].
        destruct S as [Hq S]. rewrite ccode_spill_cons. cbn [combine].
        apply stores_cons.
        + intros st0. apply exp_eval_local, Hr.
        + intros st0. rewrite cexp_gep_arr. unfold LLVM_emit_facts.i64.
          eapply exp_eval_gep_arr; [cbn [length] in Hi; lia|apply Hp|exact Hq].
        + apply IH; auto. cbn [length] in Hi. lia. }
    destruct (stores_run _ _ _ _ _ st Hs) as (st' & R & P & Rd).
    - eapply Forall_impl; [|exact Wq]. intros [q w]. auto.
    - eapply slot_ptrs_disj, S.
    - exists st', qs. rewrite map_fst_combine in P by exact L.
      split; [exact R|split; [exact S|split; [exact L|split; [exact P|]]]].
      eapply slots_ok_of_ptrs; eauto.
  Qed.

  (** [store_fields]: store the fields [ys] at [vp + 8*i], [vp + 8*(i+1)], ... *)
  Lemma store_fields_run fs env vp i ys ws p st sf stk g :
    (forall st0, exp_eval st0 sf stk g (Some dptr) (cexp vp) (Ptr p)) ->
    Forall2 (fun y w => forall st0, exp_eval st0 sf stk g (Some i64) (cexp (gvar fs env y)) (I64 w)) ys ws ->
    Z.of_nat (N.to_nat i + length ys) < 2^63 ->
    slots_ok (fun q _ => writable_word st q) p (N.to_nat i) ws ->
    exists st' qs,
      runs (denote_code (ccode (store_fields fs env vp i ys)) va)
           (st, ((sf, stk), g)) (st', ((sf, stk), g)) tt /\
      slot_ptrs p (N.to_nat i) qs /\ length qs = length ws /\ writes_post st st' qs /\
      slots_ok (fun q w => reads_word st' q w) p (N.to_nat i) ws.
  Proof.
    intros Hp Hys Hi W.
    destruct (slots_ok_ptrs _ _ _ _ W) as (qs & S & L & Wq).
    assert (Hs : stores sf stk g (ccode (store_fields fs env vp i ys)) (combine qs ws)).
    { clear W Wq. revert i qs ws Hys Hi S L. induction ys as [|y ys IH]; intros i qs ws Hys Hi S L.
      - inversion Hys; subst. destruct qs; [|discriminate]. rewrite ccode_store_fields_nil. constructor.
      - inversion Hys as [|? w ? ws' Hy Hys']; subst. destruct qs as [|q qs]; [discriminate|].
        destruct S as [Hq S]. rewrite ccode_store_fields_cons. cbn [combine].
        apply stores_cons.
        + exact Hy.
        + intros st0. rewrite cexp_gep_at. unfold LLVM_emit_facts.i64.
          eapply exp_eval_gep_at; [cbn [length] in Hi; lia|apply Hp|exact Hq].
        + apply IH; auto; rewrite N2Nat.inj_succ; [cbn [length] in Hi; lia|exact S]. }
    destruct (stores_run _ _ _ _ _ st Hs) as (st' & R & P & Rd).
    - eapply Forall_impl; [|exact Wq]. intros [q w]. auto.
    - eapply slot_ptrs_disj, S.
    - exists st', qs. rewrite map_fst_combine in P by exact L.
      split; [exact R|split; [exact S|split; [exact L|split; [exact P|]]]].
      eapply slots_ok_of_ptrs; eauto.
  Qed.

  (** The locals written by [reload_code seed _ _ i]: [ssname seed (1000+i+k)]
      receives the [k]-th word. *)
  Fixpoint reload_locals (m : local_env) (seed : positive) (i : nat) (ws : list Z) : local_env :=
    match ws with
    | [] => m
    | w :: ws' => reload_locals (Maps.add (ssname seed (1000 + i)) (I64 w) m) seed (S i) ws'
    end.

  Lemma reload_locals_other m seed i ws x :
    (forall k, (k < length ws)%nat -> ssname seed (1000 + (i + k)) <> x) ->
    RM.find x (reload_locals m seed i ws) = RM.find x m.
  Proof.
    revert m i. induction ws as [|w ws IH]; intros m i H; [reflexivity|].
    cbn. rewrite IH.
    - apply rfind_add_neq. specialize (H 0%nat). rewrite Nat.add_0_r in H. apply H. cbn. lia.
    - intros k Hk. specialize (H (S k)). rewrite Nat.add_succ_r in H. apply H. cbn. lia.
  Qed.

  (** [reload_code]: load the slots [i, i+1, ...] of the root array (held by
      the local [r0]) into the locals [ssname seed (1000+i)], ... *)
  Lemma reload_code_run seed rootsp r0 n i rs ws p st sf stk g :
    cexp rootsp = EXP_Ident (ID_Local r0) ->
    RM.find r0 (stack_vars sf) = Some (Ptr p) ->
    (forall k, (k < length rs)%nat -> ssname seed (1000 + (i + k)) <> r0) ->
    length ws = length rs ->
    Z.of_nat (i + length rs) < 2^63 ->
    slots_ok (fun q w => reads_word st q w) p i ws ->
    runs (denote_code (ccode (reload_code seed rootsp (TYPE_Array n val_ty) i rs)) va)
         (st, ((sf, stk), g))
         (st, ((upd_local_sf sf (reload_locals (stack_vars sf) seed i ws), stk), g)) tt.
  Proof.
    intros Er Hr0 Hne. revert i ws sf Hr0 Hne. induction rs as [|r rs IH]; intros i ws sf Hr0 Hne L Hi R.
    - destruct ws; [|discriminate]. rewrite ccode_reload_nil. cbn [reload_locals].
      replace (upd_local_sf sf (stack_vars sf)) with sf by (destruct sf; reflexivity).
      apply runs_code_nil.
    - destruct ws as [|w ws]; [discriminate|]. destruct R as ((q & Hq & Rq) & R).
      rewrite ccode_reload_cons. eapply runs_code_cons.
      + unfold LLVM_emit_facts.i64, LLVM_emit_facts.dptr. apply (instr_load_word _ _ q w); [|exact Rq].
        rewrite cexp_gep_arr, Er. unfold LLVM_emit_facts.i64.
        eapply exp_eval_gep_arr; [cbn [length] in Hi; lia|apply exp_eval_local, Hr0|exact Hq].
      + cbn [reload_locals].
        set (m := Maps.add (ssname seed (1000 + i)) (I64 w) (stack_vars sf)).
        change (reload_locals m seed (S i) ws) with (reload_locals (stack_vars (upd_local_sf sf m)) seed (S i) ws).
        rewrite <- (upd_local_sf_twice sf m (reload_locals (stack_vars (upd_local_sf sf m)) seed (S i) ws)).
        apply IH.
        * change (RM.find r0 m = Some (Ptr p)). subst m. rewrite rfind_add_neq; [exact Hr0|].
          specialize (Hne 0%nat). rewrite Nat.add_0_r in Hne. apply Hne. cbn. lia.
        * intros k Hk. specialize (Hne (S k)). rewrite Nat.add_succ_r in Hne. apply Hne. cbn. lia.
        * cbn in L. lia.
        * cbn [length] in Hi. lia.
        * exact R.
  Qed.
End Runs.

(* ================================================================== *)
(** * Catching exceptions: [run_exc] commutes with [interp_mcfg (interp_mrec ctx _)]

    [steps_to P t n]: [t] reaches a tree satisfying [P] after exactly [n]
    [Tau]s (up to [eq_itree]).  A tree that is [≈ Ret v] (resp. ends in OOM)
    does so after finitely many [Tau]s, which gives an induction measure to
    push [run_exc] through the interpreted tree. *)

Section StepsTo.
  Context {E : Type -> Type} {R : Type}.
  Inductive steps_to (P : itree E R -> Prop) : itree E R -> nat -> Prop :=
  | ST0 t : P t -> steps_to P t 0
  | STS t t' n : t ≅ Tau t' -> steps_to P t' n -> steps_to P t (S n).

  Definition steps_closed (P : itree E R -> Prop) := forall t t', t ≅ t' -> P t -> P t'.

  Lemma steps_to_eq P t t' n : steps_closed P -> t ≅ t' -> steps_to P t n -> steps_to P t' n.
  Proof.
    intros C Heq H. revert t' Heq. induction H; intros t2 Heq.
    - constructor. eapply C; eauto.
    - econstructor; [|eauto]. rewrite <- Heq. assumption.
  Qed.

  Lemma steps_to_tau P u n : steps_closed P -> (forall t, P t -> forall u, ~ t ≅ Tau u) ->
    steps_to P (Tau u) n -> exists n', n = S n' /\ steps_to P u n'.
  Proof.
    intros C NP H. inversion H; subst.
    - exfalso. eapply NP; [eassumption|reflexivity].
    - exists n0. split; [reflexivity|]. eapply steps_to_eq; [exact C| |eassumption].
      apply eqit_inv_Tau. symmetry. assumption.
  Qed.

  Lemma steps_to_eutt P t n : steps_to P t n -> exists t0, P t0 /\ t ≈ t0.
  Proof.
    induction 1 as [t H|t t' n Ht _ IH]; [exists t; split; [auto|reflexivity]|].
    destruct IH as (t0 & H0 & E0). exists t0. split; auto. rewrite Ht, tau_eutt. auto.
  Qed.

  Definition is_ret_tree (v : R) (t : itree E R) : Prop := t ≅ Ret v.

  Lemma steps_closed_ret v : steps_closed (is_ret_tree v).
  Proof. intros t t' H H'. unfold is_ret_tree in *. rewrite <- H. auto. Qed.

  Lemma ret_not_tau v t : is_ret_tree v t -> forall u, ~ t ≅ Tau u.
  Proof. intros H u H'. unfold is_ret_tree in H. rewrite H in H'. apply eqit_inv in H'. exact H'. Qed.

  Lemma eutt_steps_to_ret t v : t ≈ Ret v -> exists n, steps_to (is_ret_tree v) t n.
  Proof.
    intros H. punfold H. red in H. cbn in H.
    remember (observe t) as ot. remember (RetF v : itree' E R) as ov.
    revert t Heqot. induction H; intros t Ho; subst; try discriminate.
    - inversion Heqov; subst. exists 0%nat. constructor. unfold is_ret_tree.
      rewrite (itree_eta t), <- Ho. reflexivity.
    - destruct (IHeqitF eq_refl t1 eq_refl) as [n Hn]. exists (S n).
      econstructor; [|exact Hn]. rewrite (itree_eta t), <- Ho. reflexivity.
  Qed.

  Lemma steps_to_ret_eutt v t n : steps_to (is_ret_tree v) t n -> t ≈ Ret v.
  Proof.
    intros H. destruct (steps_to_eutt _ _ _ H) as (t0 & H0 & E0). unfold is_ret_tree in H0. rewrite E0, H0. reflexivity.
  Qed.
End StepsTo.

Lemma steps_to_ret_bind {E A B} (t : itree E A) (k : A -> itree E B) v n :
  steps_to (is_ret_tree v) (ITree.bind t k) n ->
  exists w n1 n2, steps_to (is_ret_tree w) t n1 /\ steps_to (is_ret_tree v) (k w) n2 /\ (n1 + n2 = n)%nat.
Proof.
  revert t. induction n as [n IH] using lt_wf_ind. intros t H.
  destruct (observe t) as [w|u|X e h] eqn:Et.
  - assert (Hb : ITree.bind t k ≅ k w) by (rewrite (itree_eta t), Et, Eqit.bind_ret_l; reflexivity).
    apply (steps_to_eq _ _ _ _ (steps_closed_ret v) Hb) in H. exists w, 0%nat, n. split; [|split; [exact H|reflexivity]].
    constructor. unfold is_ret_tree. rewrite (itree_eta t), Et. reflexivity.
  - assert (Hb : ITree.bind t k ≅ Tau (ITree.bind u k)) by (rewrite (itree_eta t), Et, bind_tau; reflexivity).
    apply (steps_to_eq _ _ _ _ (steps_closed_ret v) Hb) in H.
    destruct (steps_to_tau _ _ _ (steps_closed_ret v) (ret_not_tau v) H) as (n' & -> & H').
    destruct (IH n' (Nat.lt_succ_diag_r _) u H') as (w & n1 & n2 & H1 & H2 & Hs).
    exists w, (S n1), n2. split; [|split; [exact H2|lia]].
    econstructor; [|exact H1]. rewrite (itree_eta t), Et. reflexivity.
  - assert (Hb : ITree.bind t k ≅ Vis e (fun x => ITree.bind (h x) k)) by (rewrite (itree_eta t), Et, bind_vis; reflexivity).
    apply (steps_to_eq _ _ _ _ (steps_closed_ret v) Hb) in H.
    exfalso. inversion H; subst.
    + unfold is_ret_tree in H0. apply eqit_inv in H0. exact H0.
    + apply eqit_inv in H0. exact H0.
Qed.

Section RunExc.
  Variable ctx : CallE ~> itree (CallE +' MCFGEtop).
  Definition Jmc {X} (t : CFGtop X) s := interp_mcfg (interp_mrec ctx t) s.

  #[local] Instance Jmc_proper {X} : Proper (eq_itree eq ==> eq ==> eq_itree eq) (@Jmc X).
  Proof. intros t t' H s s' <-. unfold Jmc, interp_mcfg. rewrite H. reflexivity. Qed.

  Lemma Jmc_ret {X} (r : X) s : Jmc (Ret r) s ≅ Ret (s, r).
  Proof. unfold Jmc, interp_mcfg. rewrite unfold_interp_mrec. cbn. rewrite interp_intrinsics_ret, interp_state_ret. reflexivity. Qed.

  Lemma Jmc_tau {X} (t : CFGtop X) s : Jmc (Tau t) s ≅ Tau (Jmc t s).
  Proof. unfold Jmc, interp_mcfg. rewrite unfold_interp_mrec. cbn. rewrite interp_intrinsics_Tau, interp_state_tau. reflexivity. Qed.

  Lemma Jmc_call {X Y} (c : CallE Y) (k : Y -> CFGtop X) s :
    Jmc (Vis (inl1 c) k) s ≅ Tau (Jmc (ITree.bind (ctx _ c) k) s).
  Proof. unfold Jmc, interp_mcfg. rewrite unfold_interp_mrec. cbn. rewrite interp_intrinsics_Tau, interp_state_tau. reflexivity. Qed.

  Lemma Jmc_bind {X Y} (t : CFGtop X) (k : X -> CFGtop Y) s :
    Jmc (ITree.bind t k) s ≅ ITree.bind (Jmc t s) (fun sx => Jmc (k (snd sx)) (fst sx)).
  Proof. unfold Jmc, interp_mcfg. rewrite interp_mrec_bind, interp_intrinsics_bind, interp_state_bind. reflexivity. Qed.

  Lemma Jmc_vis {Y} (e : MCFGEtop Y) s : exists Q, forall X (k : Y -> CFGtop X),
    Jmc (Vis (inr1 e) k) s ≅ ITree.bind Q (fun sx => Tau (Tau (Jmc (k (snd sx)) (fst sx)))).
  Proof.
    eexists. intros X k. unfold Jmc, interp_mcfg. rewrite unfold_interp_mrec. cbn.
    rewrite interp_intrinsics_vis_eqit, interp_state_bind.
    apply eqit_bind; [reflexivity|]. intros [s1 x]. cbn.
    rewrite interp_intrinsics_Tau, interp_state_tau, interp_state_tau. reflexivity.
  Qed.

  Lemma run_exc_ret {A} (a : A) : run_exc (Ret a : CFGtop A) ≅ Ret (inr a).
  Proof. unfold run_exc. rewrite unfold_iter. cbn. rewrite Eqit.bind_ret_l. reflexivity. Qed.

  Lemma run_exc_tau {A} (t : CFGtop A) : run_exc (Tau t) ≅ Tau (run_exc t).
  Proof. unfold run_exc. rewrite unfold_iter. cbn. rewrite Eqit.bind_ret_l. reflexivity. Qed.

  Lemma run_exc_vis {A Y} (e : CFGEtop Y) (k : Y -> CFGtop A) :
    exc_of_event e = None -> run_exc (Vis e k) ≅ Vis e (fun y => Tau (run_exc (k y))).
  Proof.
    intros He. unfold run_exc. rewrite unfold_iter. cbn. rewrite He. rewrite bind_vis.
    apply eqit_Vis. intros y. rewrite Eqit.bind_ret_l. reflexivity.
  Qed.

  Lemma exc_void {Y} (e : CFGEtop Y) x : exc_of_event e = Some x -> Y -> False.
  Proof.
    intros H y. unfold exc_of_event in H. unfold CFGEtop in e.
    destruct e as [c|e]; [discriminate|].
    repeat (destruct e as [?|e]; [discriminate|]).
    destruct e as [e|e]; [|destruct e; discriminate].
    destruct e. destruct y.
  Qed.
  #[local] Instance run_exc_proper {A : Type} : Proper (eq_itree eq ==> eq_itree eq) (fun t : CFGtop A => run_exc t).
  Proof.
    intros u1 u2 H. unfold run_exc. eapply (eq_itree_iter' (eq_itree eq) eq); [|exact H].
    intros j1 j2 Hj. punfold Hj. red in Hj. genobs j1 oj1. genobs j2 oj2.
    destruct Hj; pclearbot; try discriminate.
    - subst. apply eqit_Ret. constructor. reflexivity.
    - apply eqit_Ret. constructor. exact REL.
    - destruct (exc_of_event e).
      + apply eqit_Ret. constructor. reflexivity.
      + apply eqit_Vis. intros y. apply eqit_Ret. constructor. apply REL.
  Qed.

  Lemma steps_to_ret_tau {E Y} (u : itree E Y) v n :
    steps_to (is_ret_tree v) (Tau u) n -> exists n', n = S n' /\ steps_to (is_ret_tree v) u n'.
  Proof. apply steps_to_tau; [apply steps_closed_ret|apply ret_not_tau]. Qed.

  Lemma Jmc_run_exc_ret {X} n : forall (t : CFGtop X) s v,
    steps_to (is_ret_tree v) (Jmc t s) n -> Jmc (run_exc t) s ≈ Ret (fst v, inr (snd v)).
  Proof.
    induction n as [n IH] using lt_wf_ind. intros t s v H.
    pose proof (itree_eta t) as Ht. destruct (observe t) as [a|u|Y e k] eqn:Et;
      apply (steps_to_eq _ _ _ _ (steps_closed_ret v) (Jmc_proper _ _ Ht s s eq_refl)) in H; rewrite Ht.
    -       apply (steps_to_eq _ _ _ _ (steps_closed_ret v) (Jmc_ret a s)) in H.
      apply steps_to_ret_eutt, eutt_inv_Ret in H. subst v.
      rewrite run_exc_ret, Jmc_ret. reflexivity.
    -       apply (steps_to_eq _ _ _ _ (steps_closed_ret v) (Jmc_tau u s)) in H.
      apply steps_to_ret_tau in H. destruct H as (n' & -> & H).
      rewrite run_exc_tau, Jmc_tau, tau_eutt. eapply IH; [|exact H]. lia.
    - destruct e as [c|e].
      + apply (steps_to_eq _ _ _ _ (steps_closed_ret v) (Jmc_call c k s)) in H.
        apply steps_to_ret_tau in H. destruct H as (n' & -> & H).
        apply (steps_to_eq _ _ _ _ (steps_closed_ret v) (Jmc_bind _ _ s)) in H.
        apply steps_to_ret_bind in H. destruct H as (w & n1 & n2 & H1 & H2 & Hn).
        apply steps_to_ret_eutt in H1.
        rewrite run_exc_vis by reflexivity. rewrite Jmc_call, tau_eutt, Jmc_bind, H1, Eqit.bind_ret_l.
        cbn. rewrite Jmc_tau, tau_eutt. eapply IH; [|exact H2]. lia.
      + destruct (Jmc_vis e s) as [Q HQ].
        apply (steps_to_eq _ _ _ _ (steps_closed_ret v) (HQ _ k)) in H.
        apply steps_to_ret_bind in H. destruct H as (w & n1 & n2 & H1 & H2 & Hn).
        apply steps_to_ret_eutt in H1.
        destruct (exc_of_event (inr1 e)) as [x|] eqn:Ex.
        * exfalso. exact (exc_void _ _ Ex (snd w)).
        * rewrite run_exc_vis by exact Ex. rewrite HQ, H1, Eqit.bind_ret_l. cbn.
          rewrite !tau_eutt, Jmc_tau, tau_eutt.
          apply steps_to_ret_tau in H2. destruct H2 as (n3 & -> & H2).
          apply steps_to_ret_tau in H2. destruct H2 as (n4 & -> & H2).
          eapply IH; [|exact H2]. lia.
  Qed.

  Lemma Jmc_run_exc {X} (t : CFGtop X) s s' r :
    Jmc t s ≈ Ret (s', r) -> Jmc (run_exc t) s ≈ Ret (s', inr r).
  Proof.
    intros H. apply eutt_steps_to_ret in H. destruct H as [n H].
    apply (Jmc_run_exc_ret n t s (s', r) H).
  Qed.
  Definition oom_evb {X} (e : MCFGEbot X) : bool :=
    match e with inr1 (inl1 _) => true | _ => false end.
  Definition is_oom_tree {R} (t : itree MCFGEbot R) : Prop :=
    exists X (e : MCFGEbot X) k, oom_evb e = true /\ t ≅ Vis e k.

  Lemma vis_evb {R X Y} b1 b2 (e : MCFGEbot X) (e' : MCFGEbot Y) (k : X -> itree MCFGEbot R) k' :
    eqit eq b1 b2 (Vis e k) (Vis e' k') -> oom_evb e = oom_evb e'.
  Proof.
    intros H. punfold H. red in H. cbn in H.
    remember (VisF e k) as a. remember (VisF e' k') as b.
    destruct H; try discriminate.
    apply (f_equal (fun ot => match ot with VisF _ e _ => oom_evb e | _ => false end)) in Heqa, Heqb.
    cbn in *. congruence.
  Qed.

  Lemma Jmc_exc {X Y} (e : MCFGEtop Y) (k : Y -> CFGtop X) s x :
    exc_of_event (inr1 e) = Some x ->
    Jmc (Vis (inr1 e) k) s ≈ Vis (subevent void (LLVMExc x)) (fun v : void => match v with end).
  Proof.
    intros Ex.
    unfold exc_of_event in Ex.
    repeat (destruct e as [?|e]; [discriminate|]).
    destruct e as [e|e]; [|destruct e; discriminate].
    destruct e as [x']. cbn in Ex. injection Ex as <-.
    unfold Jmc, interp_mcfg. rewrite unfold_interp_mrec. cbn.
    rewrite interp_intrinsics_vis_eqit, interp_state_bind. cbn.
    unfold F_trigger. rewrite interp_state_trigger. cbn. unfold fused_trigger. rewrite Eqit.bind_bind.
    unfold trigger, ITree.trigger. rewrite bind_vis. apply eqit_Vis. intros [].
  Qed.
  Lemma steps_closed_oom {R} : steps_closed (@is_oom_tree R).
  Proof. intros t t' H (X & e & k & He & Ht). exists X, e, k. split; [exact He|]. rewrite <- H. exact Ht. Qed.

  Lemma oom_not_tau {R} (t : itree MCFGEbot R) : is_oom_tree t -> forall u, ~ t ≅ Tau u.
  Proof. intros (X & e & k & _ & Ht) u H. rewrite Ht in H. apply eqit_inv in H. exact H. Qed.

  Lemma steps_to_oom_tau {R} (u : itree MCFGEbot R) n :
    steps_to is_oom_tree (Tau u) n -> exists n', n = S n' /\ steps_to is_oom_tree u n'.
  Proof. apply steps_to_tau; [apply steps_closed_oom|apply oom_not_tau]. Qed.

  Lemma ends_in_oom_steps_to {R} (t : itree MCFGEbot R) :
    ends_in_oom t -> exists n, steps_to is_oom_tree t n.
  Proof.
    intros [k H]. punfold H. red in H. cbn in H.
    remember (observe t) as ot. remember (VisF (subevent void (ThrowOOM tt)) k) as ov.
    revert t Heqot. induction H; intros t Ho; subst; try discriminate.
    - exists 0%nat. constructor. exists u, e, k1. split.
      + apply (f_equal (fun ot => match ot with VisF _ e _ => oom_evb e | _ => false end)) in Heqov.
        exact Heqov.
      + rewrite (itree_eta t), <- Ho. reflexivity.
    - destruct (IHeqitF eq_refl t1 eq_refl) as [n Hn]. exists (S n).
      econstructor; [|exact Hn]. rewrite (itree_eta t), <- Ho. reflexivity.
  Qed.

  Lemma steps_to_oom_ends {R} (t : itree MCFGEbot R) n :
    steps_to is_oom_tree t n -> ends_in_oom t.
  Proof.
    intros H. destruct (steps_to_eutt _ _ _ H) as (t0 & (X & e & k & He & Ht) & E0).
    repeat (destruct e as [e|e]; try discriminate).
    destruct e as [[]]. exists k. rewrite E0, Ht. reflexivity.
  Qed.

  Lemma steps_to_oom_bind {A B} (t : itree MCFGEbot A) (k : A -> itree MCFGEbot B) n :
    steps_to is_oom_tree (ITree.bind t k) n ->
    (exists n1, steps_to is_oom_tree t n1) \/
    exists w n1 n2, steps_to (is_ret_tree w) t n1 /\ steps_to is_oom_tree (k w) n2 /\ (n1 + n2 = n)%nat.
  Proof.
    revert t. induction n as [n IH] using lt_wf_ind. intros t H.
    destruct (observe t) as [w|u|X e h] eqn:Et.
    - assert (Hb : ITree.bind t k ≅ k w) by (rewrite (itree_eta t), Et, Eqit.bind_ret_l; reflexivity).
      apply (steps_to_eq _ _ _ _ steps_closed_oom Hb) in H. right. exists w, 0%nat, n.
      split; [|split; [exact H|reflexivity]].
      constructor. unfold is_ret_tree. rewrite (itree_eta t), Et. reflexivity.
    - assert (Hb : ITree.bind t k ≅ Tau (ITree.bind u k)) by (rewrite (itree_eta t), Et, bind_tau; reflexivity).
      apply (steps_to_eq _ _ _ _ steps_closed_oom Hb) in H.
      destruct (steps_to_oom_tau _ _ H) as (n' & -> & H').
      destruct (IH n' (Nat.lt_succ_diag_r _) u H') as [(n1 & H1)|(w & n1 & n2 & H1 & H2 & Hs)].
      + left. exists (S n1). econstructor; [|exact H1]. rewrite (itree_eta t), Et. reflexivity.
      + right. exists w, (S n1), n2. split; [|split; [exact H2|lia]].
        econstructor; [|exact H1]. rewrite (itree_eta t), Et. reflexivity.
    - assert (Hb : ITree.bind t k ≅ Vis e (fun x => ITree.bind (h x) k)) by (rewrite (itree_eta t), Et, bind_vis; reflexivity).
      apply (steps_to_eq _ _ _ _ steps_closed_oom Hb) in H.
      inversion H; subst.
      + left. exists 0%nat. constructor. destruct H0 as (Y & e' & k' & He' & Ht').
        exists X, e, h. split.
        * rewrite (vis_evb _ _ _ _ _ _ Ht'). exact He'.
        * rewrite (itree_eta t), Et. reflexivity.
      + exfalso. apply eqit_inv in H0. exact H0.
  Qed.

  Lemma steps_to_oom_bind_l {A B} (t : itree MCFGEbot A) (k : A -> itree MCFGEbot B) n :
    steps_to is_oom_tree t n -> ends_in_oom (ITree.bind t k).
  Proof.
    intros H. apply steps_to_oom_ends in H. destruct H as [k0 H].
    exists (fun v : void => match v with end). rewrite H, bind_vis. apply eqit_Vis. intros [].
  Qed.

  Lemma Jmc_run_exc_oom {X} n : forall (t : CFGtop X) s,
    steps_to is_oom_tree (Jmc t s) n -> ends_in_oom (Jmc (run_exc t) s).
  Proof.
    induction n as [n IH] using lt_wf_ind. intros t s H.
    pose proof (itree_eta t) as Ht. destruct (observe t) as [a|u|Y e k] eqn:Et;
      apply (steps_to_eq _ _ _ _ steps_closed_oom (Jmc_proper _ _ Ht s s eq_refl)) in H; rewrite Ht.
    - apply (steps_to_eq _ _ _ _ steps_closed_oom (Jmc_ret a s)) in H. exfalso.
      inversion H; subst.
      + destruct H0 as (? & ? & ? & _ & H0). apply eqit_inv in H0. exact H0.
      + apply eqit_inv in H0. exact H0.
    - apply (steps_to_eq _ _ _ _ steps_closed_oom (Jmc_tau u s)) in H.
      apply steps_to_oom_tau in H. destruct H as (n' & -> & H).
      unfold ends_in_oom. setoid_rewrite run_exc_tau. setoid_rewrite Jmc_tau. setoid_rewrite tau_eutt.
      eapply IH; [|exact H]. lia.
    - destruct e as [c|e].
      + apply (steps_to_eq _ _ _ _ steps_closed_oom (Jmc_call c k s)) in H.
        apply steps_to_oom_tau in H. destruct H as (n' & -> & H).
        unfold ends_in_oom.
        setoid_rewrite run_exc_vis; [|reflexivity]. setoid_rewrite Jmc_call. setoid_rewrite tau_eutt.
        setoid_rewrite Jmc_bind.
        apply (steps_to_eq _ _ _ _ steps_closed_oom (Jmc_bind _ _ s)) in H.
        apply steps_to_oom_bind in H. destruct H as [(n1 & H1)|(w & n1 & n2 & H1 & H2 & Hn)].
        * apply (steps_to_oom_bind_l _ _ _ H1).
        * apply steps_to_ret_eutt in H1. setoid_rewrite H1. setoid_rewrite Eqit.bind_ret_l. cbn.
          setoid_rewrite Jmc_tau. setoid_rewrite tau_eutt. eapply IH; [|exact H2]. lia.
      + destruct (exc_of_event (inr1 e)) as [x|] eqn:Ex.
        * exfalso. pose proof (Jmc_exc e k s x Ex) as HE.
          destruct (steps_to_eutt _ _ _ H) as (t0 & (Z & e0 & k0 & He0 & Ht0) & E0).
          rewrite HE, Ht0 in E0. apply vis_evb in E0. rewrite He0 in E0. discriminate.
        * destruct (Jmc_vis e s) as [Q HQ].
          apply (steps_to_eq _ _ _ _ steps_closed_oom (HQ _ k)) in H.
          apply steps_to_oom_bind in H. destruct H as [(n1 & H1)|(w & n1 & n2 & H1 & H2 & Hn)].
          -- unfold ends_in_oom. setoid_rewrite run_exc_vis; [|exact Ex]. setoid_rewrite HQ.
             apply (steps_to_oom_bind_l _ _ _ H1).
          -- apply steps_to_ret_eutt in H1.
             unfold ends_in_oom. setoid_rewrite run_exc_vis; [|exact Ex]. setoid_rewrite HQ.
             setoid_rewrite H1. setoid_rewrite Eqit.bind_ret_l. cbn.
             setoid_rewrite tau_eutt. setoid_rewrite Jmc_tau. setoid_rewrite tau_eutt.
             apply steps_to_oom_tau in H2. destruct H2 as (n3 & -> & H2).
             apply steps_to_oom_tau in H2. destruct H2 as (n4 & -> & H2).
             setoid_rewrite tau_eutt. eapply IH; [|exact H2]. lia.
  Qed.

  Lemma Jmc_run_exc_ends_oom {X} (t : CFGtop X) s :
    ends_in_oom (Jmc t s) -> ends_in_oom (Jmc (run_exc t) s).
  Proof. intros H. apply ends_in_oom_steps_to in H. destruct H as [n H]. eapply Jmc_run_exc_oom, H. Qed.
End RunExc.

(* ================================================================== *)
(** * Function activations

    [denote_function df args] is
    [push_call_frame;; run_exc (denote_cfg_map ..);; pop_call_frame;; ret].
    - [push_call_frame_cases]: with [length args = length (df_args df)] the
      call frame push either OOMs (the 0-byte varargs alloca) or runs, binding
      the formals ([new_frame (combine (df_args df) args)]) on top of the
      caller's frame, pushing an empty memory frame ([push_post]).
    - [runs_cfg_entry]/[oom_cfg_entry]: a body whose entry block has no phis
      runs as code;; terminator ([block_tail], = [LLVM_sim.tail_of]).
    - [pop_call_frame_runs]: with a [Snoc] frame stack, [pop_call_frame]
      restores the caller's locals and frees the top memory frame ([pop_post]).
    - [denote_function_runs], [oom_denote_function_push],
      [oom_denote_function_body] compose these; together with [instr_call] /
      [oom_instr_call] (via [ctx _ (Call ..) = denote_function ..]). *)

Section Functions.
  Variable ctx : CallE ~> itree (CallE +' MCFGEtop).
  Notation runs := (runs ctx).
  Notation oom := (oom ctx).

  Lemma combine_varargs_eq {A B} (l1 : list A) (l2 : list B) :
    length l2 = length l1 -> combine_lists_varargs l1 l2 = EOU.raise_ret (combine l1 l2, []).
  Proof.
    revert l2. induction l1 as [|x l1 IH]; intros [|y l2] L; try discriminate; [reflexivity|].
    cbn. rewrite IH by (injection L; auto). reflexivity.
  Qed.

  Lemma push_call_frame_eq df args :
    length args = length (df_args df) ->
    push_call_frame df args ≈
    (mem_push;; stack_push (combine (df_args df) args);;
     varargs <- alloca (DTYPE_Struct true []) 1 None;;
     store (DTYPE_Struct true []) varargs (DVALUE_Struct true []);;
     match varargs with
     | DVALUE_Base (DVALUE_Pointer varg) => ret varg
     | _ => raise "Non-address returned from alloca of varargs"
     end).
  Proof.
    intros L. unfold push_call_frame. rewrite combine_varargs_eq by exact L.
    cbn. rewrite Eqit.bind_ret_l. cbn. rewrite Eqit.bind_ret_l. reflexivity.
  Qed.

  Lemma Mempush_exists st : exists st', memS_runs st Mempush st' tt.
  Proof. eexists. unfold Mempush, app_frame_stack. cbn. repeat econstructor. Qed.

  Lemma runs_mem_push st rest : exists st',
    runs mem_push (st, rest) (st', rest) tt /\
    mem_of st' = mem_of st /\ heap_of st' = heap_of st /\
    frames_of st' = Snoc (frames_of st) [] /\ state_provenance st' = state_provenance st.
  Proof.
    destruct (Mempush_exists st) as [st' H]. exists st'. split.
    - unfold mem_push. apply runs_memory. exact H.
    - apply Mempush_runs in H. exact H.
  Qed.
  Lemma store_empty_exists st p :
    exists st', memS_runs st (write_dvalue (DTYPE_Struct true []) p (DVALUE_Struct true [])) st' tt.
  Proof.
    eapply write_dvalue_exists; [reflexivity|]. intros q [].
  Qed.

  Lemma store_empty_post st p st' :
    memS_runs st (write_dvalue (DTYPE_Struct true []) p (DVALUE_Struct true [])) st' tt ->
    heap_of st' = heap_of st /\ frames_of st' = frames_of st /\
    forall a, IntMaps.lookup a (mem_of st') = IntMaps.lookup a (mem_of st).
  Proof.
    intros H. pose proof (write_dvalue_heap _ _ _ _ _ _ H) as (E1 & E2 & _).
    apply write_dvalue_runs in H. destruct H as (_ & Hout & _).
    split; [exact E1|split; [exact E2|]]. intros a. apply Hout. cbn. lia.
  Qed.

  Lemma Mempop_exists st fs f :
    frames_of st = Snoc fs f -> exists st', memS_runs st Mempop st' tt.
  Proof.
    intros E. eexists.
    unfold Mempop, get_frame, get_frame_stack, app_frame_stack_eob, get_framestack,
      app_frame_stack, app_mem.
    unfold frames_of in E. cbn. constructor. rewrite E. cbn. constructor. rewrite E. cbn. repeat econstructor.
  Qed.
  Definition push_post (st st' : state) : Prop :=
    heap_of st' = heap_of st /\ frames_of st' = Snoc (frames_of st) [] /\
    forall a, IntMaps.lookup a (mem_of st') = IntMaps.lookup a (mem_of st).

  Lemma push_call_frame_cases df args st sf stk g :
    length args = length (df_args df) ->
    oom (push_call_frame df args) (st, ((sf, stk), g)) \/
    exists st' p,
      runs (push_call_frame df args) (st, ((sf, stk), g))
           (st', ((new_frame (combine (df_args df) args), sf :: stk), g)) p /\
      push_post st st'.
  Proof.
    intros L.
    destruct (runs_mem_push st ((sf, stk), g)) as (st1 & Hpush & Em & Eh & Ef & _).
    destruct (allocate_dtyp_total st1 (DTYPE_Struct true []) 1 8 eq_refl) as [Ho|(st2 & p & Ha)].
    - left. eapply oom_eutt; [symmetry; apply push_call_frame_eq, L|].
      eapply oom_bind_r; [exact Hpush|]. eapply oom_bind_r; [apply runs_stack_push|].
      apply oom_bind_l. unfold alloca. apply oom_memory. cbn [handle_memoryM].
      apply memS_oom_bind_l, Ho.
    - right. destruct (store_empty_exists st2 p) as [st3 Hs]. exists st3, p. split.
      + eapply runs_eutt; [symmetry; apply push_call_frame_eq, L|].
        eapply runs_bind; [exact Hpush|]. eapply runs_bind; [apply runs_stack_push|].
        eapply runs_bind.
        { unfold alloca. apply runs_memory_c. cbn [handle_memoryM].
          eapply memS_runs_c_bind; [exact Ha|constructor]. }
        eapply runs_bind; [unfold store; apply runs_memory; cbn [handle_memoryM]; exact Hs|].
        apply runs_ret.
      + apply allocate_dtyp_post in Ha. destruct Ha as (H1 & (ptrs & _ & Lp & Fp) & _ & Ho & _).
        destruct ptrs; [|discriminate].
        destruct (store_empty_post _ _ _ Hs) as (S1 & S2 & S3).
        split; [congruence|split].
        * rewrite S2, Fp, Ef. reflexivity.
        * intros a. rewrite S3, Ho, Em; [reflexivity|]. cbn. lia.
  Qed.

  Lemma push_post_reads_word st st' q z :
    push_post st st' -> reads_word st q z -> reads_word st' q z.
  Proof. intros (_ & _ & Hm) H. eapply reads_word_frame; [exact H|]. intros a _. apply Hm. Qed.

  Lemma push_post_reads_ptr st st' q q' :
    push_post st st' -> reads_ptr st q q' -> reads_ptr st' q q'.
  Proof. intros (_ & _ & Hm) H. eapply reads_ptr_frame; [exact H|]. intros a _. apply Hm. Qed.

  Lemma push_post_writable_word st st' q :
    push_post st st' -> writable_word st q -> writable_word st' q.
  Proof. intros (_ & _ & Hm) H. eapply writable_word_aid; [exact H|]. intros a _. unfold aid_at. rewrite Hm. reflexivity. Qed.

  Definition pop_post (st st' : state) (fs : Framestack) (f : Frame) : Prop :=
    heap_of st' = heap_of st /\ frames_of st' = fs /\
    state_provenance st' = state_provenance st /\
    forall a, ~ In a (map ptr_to_int f) ->
         IntMaps.lookup a (mem_of st') = IntMaps.lookup a (mem_of st).

  Lemma pop_call_frame_runs st sf sf' stk g fs f :
    frames_of st = Snoc fs f ->
    exists st', runs pop_call_frame (st, ((sf, sf' :: stk), g)) (st', ((sf', stk), g)) tt /\
           pop_post st st' fs f.
  Proof.
    intros E. destruct (Mempop_exists st fs f E) as [st' H]. exists st'. split.
    - unfold pop_call_frame. eapply runs_bind; [apply runs_stack_pop|].
      unfold mem_pop. apply runs_memory. exact H.
    - apply Mempop_runs in H. destruct H as (fs0 & f0 & E1 & E2 & E3 & E4 & E5).
      rewrite E in E1. injection E1 as <- <-.
      split; [exact E3|split; [exact E2|split; [exact E4|]]].
      intros a Ha. rewrite E5. apply free_frame_memory_out, Ha.
  Qed.
  Definition cont_of (vb : option ptr) (B : list (LLVMAst.block dtyp)) (l : block_id)
             (r : block_id + dvalue) : CFGtop ((block_id * block_id) + dvalue) :=
    match r with
    | inl l' => denote_ocfg B vb (l, l')
    | inr v => Ret (inr v)
    end.

  Definition block_tail (vb : option ptr) (B : list (LLVMAst.block dtyp)) (b : LLVMAst.block dtyp)
    : CFGtop ((block_id * block_id) + dvalue) :=
    ITree.bind (denote_code (blk_code b) vb ;; denote_terminator (blk_term b))
               (cont_of vb B (blk_id b)).

  Lemma denote_phis_nil from : denote_phis from [] ≈ Ret tt.
  Proof. unfold denote_phis. cbn. rewrite Eqit.bind_ret_l. cbn. rewrite Eqit.bind_ret_l. reflexivity. Qed.

  Lemma entry_block_eq vb (B : list (LLVMAst.block dtyp)) b from :
    RM.find (blk_id b) (ocfg_map B) = Some b -> blk_phis b = [] ->
    denote_ocfg_map (ocfg_map B) vb (from, blk_id b) ≈ block_tail vb B b.
  Proof.
    intros Hf Hp. rewrite (denote_ocfg_map_unfold vb _ _ _ _ Hf).
    rewrite denote_block_eq, Hp, denote_phis_nil. cbn.
    rewrite Eqit.bind_ret_l.
    unfold block_tail. apply eutt_eq_bind. intros [l1|v]; reflexivity.
  Qed.

  Lemma runs_cfg_entry vb (f : cfg dtyp) b s s' v :
    init f = blk_id b -> RM.find (blk_id b) (ocfg_map (blks f)) = Some b -> blk_phis b = [] ->
    runs (block_tail vb (blks f) b) s s' (inr v) ->
    runs (denote_cfg_map (ocfg_map (blks f)) f vb) s s' v.
  Proof.
    intros Hi Hf Hp H. unfold denote_cfg_map. rewrite Hi.
    eapply runs_bind; [eapply runs_eutt; [symmetry; apply entry_block_eq; eauto|exact H]|].
    apply runs_ret.
  Qed.

  Lemma oom_cfg_entry vb (f : cfg dtyp) b s :
    init f = blk_id b -> RM.find (blk_id b) (ocfg_map (blks f)) = Some b -> blk_phis b = [] ->
    oom (block_tail vb (blks f) b) s ->
    oom (denote_cfg_map (ocfg_map (blks f)) f vb) s.
  Proof.
    intros Hi Hf Hp H. unfold denote_cfg_map. rewrite Hi. apply oom_bind_l.
    eapply oom_eutt; [symmetry; apply entry_block_eq; eauto|exact H].
  Qed.

  Lemma runs_run_exc {X} (t : CFGtop X) s s' r : runs t s s' r -> runs (run_exc t) s s' (inr r).
  Proof. apply (Jmc_run_exc ctx). Qed.

  Lemma oom_run_exc {X} (t : CFGtop X) s : oom t s -> oom (run_exc t) s.
  Proof. apply (Jmc_run_exc_ends_oom ctx). Qed.

  (** A whole function activation. *)
  Lemma denote_function_runs df b args st sf stk g st1 p st2 sf2 sf' stk' g2 v fs f :
    init (df_instrs df) = blk_id b ->
    RM.find (blk_id b) (ocfg_map (blks (df_instrs df))) = Some b -> blk_phis b = [] ->
    runs (push_call_frame df args) (st, ((sf, stk), g))
         (st1, ((new_frame (combine (df_args df) args), sf :: stk), g)) p ->
    runs (block_tail (Some p) (blks (df_instrs df)) b)
         (st1, ((new_frame (combine (df_args df) args), sf :: stk), g))
         (st2, ((sf2, sf' :: stk'), g2)) (inr v) ->
    frames_of st2 = Snoc fs f ->
    exists st3,
      runs (denote_function df args) (st, ((sf, stk), g)) (st3, ((sf', stk'), g2)) (inr v) /\
      pop_post st2 st3 fs f.
  Proof.
    intros Hi Hf Hp Hpush Hbody Hfr.
    destruct (pop_call_frame_runs st2 sf2 sf' stk' g2 fs f Hfr) as (st3 & Hpop & Hpost).
    exists st3. split; [|exact Hpost].
    unfold denote_function. eapply runs_bind; [exact Hpush|].
    eapply runs_bind; [apply runs_run_exc; eapply (runs_cfg_entry _ _ b); eauto|].
    eapply runs_bind; [exact Hpop|]. apply runs_ret.
  Qed.

  Lemma oom_denote_function_push df args s :
    oom (push_call_frame df args) s -> oom (denote_function df args) s.
  Proof. intros H. unfold denote_function. apply oom_bind_l, H. Qed.

  Lemma oom_denote_function_body df b args s s1 p :
    init (df_instrs df) = blk_id b ->
    RM.find (blk_id b) (ocfg_map (blks (df_instrs df))) = Some b -> blk_phis b = [] ->
    runs (push_call_frame df args) s s1 p ->
    oom (block_tail (Some p) (blks (df_instrs df)) b) s1 ->
    oom (denote_function df args) s.
  Proof.
    intros Hi Hf Hp Hpush H. unfold denote_function. eapply oom_bind_r; [exact Hpush|].
    apply oom_bind_l, oom_run_exc. eapply oom_cfg_entry; eauto.
  Qed.
  (** The shape of a converted definition ([LLVM_convert.conv_def]). *)
  Lemma conv_def_entry (d : Ldef) :
    let b := cblock (fst (df_instrs d)) in
    init (df_instrs (conv_def d)) = blk_id b /\
    RM.find (blk_id b) (ocfg_map (blks (df_instrs (conv_def d)))) = Some b /\
    df_args (conv_def d) = df_args d.
  Proof.
    cbn zeta. split; [reflexivity|split; [|reflexivity]].
    cbn [df_instrs conv_def blks map]. apply find_ocfg_map_cons.
  Qed.

  Lemma cblock_phis_nil (b : LLVMAst.block typ) : blk_phis b = [] -> blk_phis (cblock b) = [].
  Proof. destruct b; cbn. intros ->. reflexivity. Qed.
End Functions.
