(** * Simulation invariant and main simulation statement for the
    LambdaANF -> LLVM correctness proof.

    The main lemma [sim_exp] (stated via [sim_stmt] at the end of this file;
    its full statement is [LLVM_toplevel_link.sim_exp_statement], and its
    proof, assembled from the cases in [LLVM_sim_cases_*.v], is in
    [LLVM_sim_exp.v]) is by induction on [bstep_e].  It symbolically executes the FLATTENED, type-
    converted code of each emitted block ([Flatten.flat_block] after
    [convert_typ]) under [interp_mcfg (interp_mrec ctx _)], where [ctx] is
    Vellvm's call knot ([denote_mcfg]).  The flattening is transported segment
    by segment (file [Flatten_sem.v]); the semantics of each emitted instruction
    form is in [LLVM_instr_lemmas.v].

    The lemma speaks about the "tail" of the entry block of the translation of
    [e]: its (flattened) code and terminator, continued in the enclosing
    function's CFG [B].  It only assumes that the blocks of [tl blks] are found
    in [B] in flattened form: the entry block itself may have been extended
    with a prefix by [prepend_code], which the caller of the lemma has already
    executed. *)

From Stdlib Require Import ZArith NArith List Lia String Program Morphisms Classical_Prop.
From Stdlib Require Relations.Operators_Properties.
From ITree Require Import ITree Eq.Eqit Interp.InterpFacts Interp.RecursionFacts.
From ExtLib Require Import Structures.Monads.

From CertiRocq.LambdaANF Require Import term term_util eval identifiers.
From CertiRocq.Common Require Import AstCommon.
From CertiRocq.CodegenLLVM Require Import LambdaANF_to_LLVM Flatten
     LambdaANF_to_LLVM_statement LLVM_interp_lemmas LLVM_call_lemmas LLVM_convert
     LLVM_exp_lemmas LLVM_mem_lemmas LLVM_emit_syntax.
From CertiRocq.CodegenLLVM Require Flatten_sem LLVM_instr_lemmas.
From Vellvm Require Syntax.ScopeTheory.

From Vellvm Require Import
  Utils Syntax Params
  Interfaces.Memory Implementations.Memory
  Semantics.DynamicValues Semantics.LLVMEvents Semantics.Denotation
  Semantics.InterpretationStack Semantics.TopLevel Handlers.

Import ListNotations.
Import MonadNotation.
Open Scope monad_scope.
Open Scope Z_scope.

Unset Implicit Arguments.
Set Bullet Behavior "Strict Subproofs".

(* ------------------------------------------------------------------ *)
(** ** Memory well-formedness

    Vellvm's memory model guarantees these for every reachable state; the
    runtime specification will assume them of [make_tinfo]'s result and of the
    collector.  They are needed because popping a call frame frees the frame's
    addresses: those must not be heap addresses. *)

Fixpoint frames_ptrs (fs : Framestack) : list ptr :=
  match fs with
  | Singleton f => f
  | Snoc s f => (f ++ frames_ptrs s)%list
  end.

Definition in_frames (st : state) (a : Z) : Prop :=
  In a (map ptr_to_int (frames_ptrs (frames_of st))).

Definition mem_ok (st : state) : Prop :=
  (forall a, in_heap st a -> IntMaps.lookup a (mem_of st) <> None) /\
  (forall a, in_frames st a -> ~ in_heap st a).

(** The nursery does not overlap [thread_info]. *)
Definition nursery_tinfo_disjoint (st : state) (tinfo : ptr) : Prop :=
  forall a, nursery st tinfo a -> ~ (ptr_to_int tinfo <= a < ptr_to_int tinfo + 8232).

Section Simulation.

  (** The program and its runtime. *)
  Variable cenv : ctor_env.
  Variable pfs : prims.
  Variable prim_of : positive -> option (string * bool).
  Variable fds : fundefs.                     (* top-level functions *)
  Variable heap_inv : state -> ptr -> Prop.
  Variable gc : list dvalue -> MCFGtop (exc + dvalue).

  Let go := ord_of cenv.
  Let ga := arity_of cenv.
  Let fs := fun_ids fds.
  Notation tr := (translate_cfg go ga prim_of fs).

  (** The global environment after initialisation, and the call knot. *)
  Variable G : global_env.
  Variable ctx : CallE ~> itree (CallE +' MCFGEtop).

  (** The [thread_info] pointer, fixed for the whole run. *)
  Variable tinfo : ptr.

  (* ------------------------------------------------------------------ *)
  (** ** Algebra of the memory predicates *)

  Lemma ptr_off_int p off q : ptr_off p off q -> ptr_to_int q = ptr_to_int p + off.
  Proof. unfold ptr_off. intros H. eapply ptr_to_int_int_to_ptr; eauto. Qed.

  Lemma ptr_off_prov p off q : ptr_off p off q -> ptr_provenance q = ptr_provenance p.
  Proof. unfold ptr_off. intros H. eapply int_to_ptr_provenance; eauto. Qed.

  Lemma ptr_off_ex p off : 0 <= ptr_to_int p + off < 2^64 -> exists q, ptr_off p off q.
  Proof.
    intros H. destruct (int_to_ptr_total (ptr_provenance p) H) as (q & Hq & _).
    exists q. exact Hq.
  Qed.

  Lemma reads_ptr_det st p q q' : reads_ptr st p q -> reads_ptr st p q' -> q = q'.
  Proof.
    intros (s1 & H1) (s2 & H2). destruct (memS_runs_det _ _ _ _ _ _ H1 H2) as [_ E].
    injection E. auto.
  Qed.

  Lemma reads_word_det st p z z' : reads_word st p z -> reads_word st p z' -> I64 z = I64 z'.
  Proof.
    intros (s1 & H1) (s2 & H2). destruct (memS_runs_det _ _ _ _ _ _ H1 H2) as [_ E]. exact E.
  Qed.

  Lemma field_int st off q : field st tinfo off q -> exists a, ptr_off tinfo off a /\ ptr_to_int a = ptr_to_int tinfo + off /\ reads_ptr st a q.
  Proof. intros (a & Ha & Hr). exists a. split; [exact Ha|]. split; [apply ptr_off_int; exact Ha|exact Hr]. Qed.

  Lemma field_det st off q q' : field st tinfo off q -> field st tinfo off q' -> q = q'.
  Proof.
    intros (a & Ha & Hr) (a' & Ha' & Hr').
    assert (a = a').
    { unfold ptr_off in Ha, Ha'. rewrite Ha in Ha'. injection Ha'. auto. }
    subst a'. eapply reads_ptr_det; eauto.
  Qed.

  Lemma field_frame st st2 off q :
    field st tinfo off q -> same_bytes st st2 (ptr_to_int tinfo + off) 8 -> field st2 tinfo off q.
  Proof.
    intros (a & Ha & Hr) Hs. exists a. split; [exact Ha|].
    eapply reads_ptr_frame; eauto. rewrite (ptr_off_int _ _ _ Ha). exact Hs.
  Qed.

  (** [st2] differs from [st] only at the addresses in [W] (among the bytes
      allocated in [st]), keeps allocation ids, keeps the heap blocks, and
      extends the top memory frame with fresh addresses. *)
  Definition mstep (st st2 : state) (W : Z -> Prop) : Prop :=
    heap_of st2 = heap_of st /\
    (forall a, ~ W a -> IntMaps.lookup a (mem_of st) <> None ->
               IntMaps.lookup a (mem_of st2) = IntMaps.lookup a (mem_of st)) /\
    (forall a, IntMaps.lookup a (mem_of st) <> None -> aid_at st2 a = aid_at st a) /\
    (exists ks, frames_of st2 = push_top ks (frames_of st) /\
                Forall (fun k => IntMaps.lookup (ptr_to_int k) (mem_of st) = None) ks).

  Lemma push_top_nil fst0 : push_top [] fst0 = fst0.
  Proof. destruct fst0; reflexivity. Qed.

  Lemma push_top_app ks ks' fst0 : push_top ks' (push_top ks fst0) = push_top (ks ++ ks')%list fst0.
  Proof. destruct fst0; simpl; rewrite rev_app_distr, <- app_assoc; reflexivity. Qed.

  Lemma mstep_refl st W : mstep st st W.
  Proof.
    split; [reflexivity|]. split; [auto|]. split; [auto|].
    exists []. split; [symmetry; apply push_top_nil|constructor].
  Qed.

  Lemma mstep_alloc st st2 W a : mstep st st2 W -> IntMaps.lookup a (mem_of st) <> None -> IntMaps.lookup a (mem_of st2) <> None.
  Proof.
    intros (_ & _ & Haid & _) Ha. specialize (Haid a Ha). unfold aid_at in Haid.
    destruct (IntMaps.lookup a (mem_of st2)); [discriminate|].
    destruct (IntMaps.lookup a (mem_of st)); [discriminate|contradiction].
  Qed.

  Lemma mstep_trans st st2 st3 W W' :
    mstep st st2 W -> mstep st2 st3 W' ->
    (forall a, W' a -> IntMaps.lookup a (mem_of st) <> None -> W a) ->
    mstep st st3 W.
  Proof.
    intros H1 H2 HW. pose proof H1 as H1'. pose proof H2 as H2'.
    destruct H1 as (E1 & M1 & A1 & ks & F1 & K1). destruct H2 as (E2 & M2 & A2 & ks' & F2 & K2).
    split; [congruence|]. split.
    - intros a Hn Ha.
      assert (Ha2 : IntMaps.lookup a (mem_of st2) <> None) by (eapply mstep_alloc; eauto).
      assert (Hn' : ~ W' a) by (intros Hw; apply Hn; apply HW; auto).
      rewrite (M2 a Hn' Ha2). apply M1; auto.
    - split.
      + intros a Ha. rewrite A2; [apply A1; auto|eapply mstep_alloc; eauto].
      + exists (ks ++ ks')%list. split; [rewrite F2, F1; apply push_top_app|].
        apply Forall_app. split; [exact K1|].
        eapply Forall_impl; [|exact K2]. intros k Hk.
        destruct (IntMaps.lookup (ptr_to_int k) (mem_of st)) eqn:E; [|reflexivity].
        exfalso. apply (mstep_alloc _ _ _ (ptr_to_int k) H1'); [|exact Hk]. rewrite E. discriminate.
  Qed.

  Lemma mstep_same_bytes st st2 W a n :
    mstep st st2 W -> (forall a', a <= a' < a + n -> ~ W a' /\ IntMaps.lookup a' (mem_of st) <> None) ->
    same_bytes st st2 a n.
  Proof. intros (_ & M & _) H a' Ha. destruct (H a' Ha). apply M; auto. Qed.

  (** Bytes allocated outside the heap. *)
  Definition alloc_nonheap (st : state) (a : Z) : Prop :=
    IntMaps.lookup a (mem_of st) <> None /\ ~ in_heap st a.

  Lemma in_heap_mstep st st2 W a : mstep st st2 W -> (in_heap st2 a <-> in_heap st a).
  Proof. intros (E & _). unfold in_heap. rewrite E. reflexivity. Qed.

  (** The frame structs of the shadow stack from [fp]. *)
  Inductive chain (st : state) : ptr -> list ptr -> Prop :=
  | chain_nil f : ptr_to_int f = 0 -> chain st f []
  | chain_cons f prev frs :
      ptr_to_int f <> 0 ->
      (exists a, ptr_off f 16 a /\ reads_ptr st a prev) ->
      chain st prev frs -> chain st f (f :: frs).

  Definition frame_bytes (f : ptr) (a : Z) : Prop := ptr_to_int f <= a < ptr_to_int f + 24.
  Definition slot_bytes (rs : list ptr) (a : Z) : Prop :=
    exists r, In r rs /\ ptr_to_int r <= a < ptr_to_int r + 8.

  (** The shadow stack lives in stack memory: frames and root slots are
      allocated, non-heap bytes. *)
  Definition stack_ok (st : state) (fp : ptr) (rs : list ptr) : Prop :=
    (exists frs, chain st fp frs /\
                 (forall f, In f frs -> forall a, frame_bytes f a -> alloc_nonheap st a) /\
                 (forall f, In f frs -> forall a, frame_bytes f a -> ~ slot_bytes rs a)) /\
    (forall a, slot_bytes rs a -> alloc_nonheap st a).

  (** The frame condition of a function activation (and of each step inside
      it), relative to the caller's root slots [rs]: allocated non-heap bytes
      (the stack: shadow-stack frame structs, root slots, [alloca]s) stay
      allocated, do not become heap, keep their contents except for the root
      slots (which the collector may update), and keep their allocation ids.
      Nothing is said about heap bytes: the collector may free from-space.
      The first clause follows from the fourth; it is kept for the shape. *)
  Definition keeps_stack (st st' : state) (rs : list ptr) : Prop :=
    (forall a, alloc_nonheap st a -> IntMaps.lookup a (mem_of st') <> None) /\
    (forall a, alloc_nonheap st a -> ~ in_heap st' a) /\
    (forall a, alloc_nonheap st a -> ~ slot_bytes rs a ->
               IntMaps.lookup a (mem_of st') = IntMaps.lookup a (mem_of st)) /\
    (forall a, alloc_nonheap st a -> aid_at st' a = aid_at st a).

  Lemma keeps_stack_nonheap st st' rs a :
    keeps_stack st st' rs -> alloc_nonheap st a -> alloc_nonheap st' a.
  Proof. intros (K1 & K2 & _) Ha. split; [apply K1, Ha|apply K2, Ha]. Qed.

  Lemma keeps_stack_refl st rs : keeps_stack st st rs.
  Proof.
    split; [|split; [|split]].
    - intros a Ha. exact (proj1 Ha).
    - intros a Ha. exact (proj2 Ha).
    - reflexivity.
    - reflexivity.
  Qed.

  Lemma keeps_stack_trans st st1 st2 rs :
    keeps_stack st st1 rs -> keeps_stack st1 st2 rs -> keeps_stack st st2 rs.
  Proof.
    intros K. pose proof K as (A1 & A2 & A3 & A4). intros (B1 & B2 & B3 & B4).
    assert (Hn : forall a, alloc_nonheap st a -> alloc_nonheap st1 a)
      by (intros a; apply keeps_stack_nonheap with rs; exact K).
    split; [|split; [|split]].
    - intros a Ha. apply B1, Hn, Ha.
    - intros a Ha. apply B2, Hn, Ha.
    - intros a Ha Hs. rewrite B3 by (try apply Hn; assumption). apply A3; assumption.
    - intros a Ha. rewrite B4 by (apply Hn, Ha). apply A4, Ha.
  Qed.

  (** A step writing only heap bytes keeps the stack. *)
  Lemma keeps_stack_mstep st st' W rs :
    mstep st st' W -> (forall a, W a -> in_heap st a) -> keeps_stack st st' rs.
  Proof.
    intros Hm HW. pose proof Hm as (E & M & A & _).
    split; [|split; [|split]].
    - intros a Ha. eapply mstep_alloc; [exact Hm|exact (proj1 Ha)].
    - intros a Ha. rewrite (in_heap_mstep _ _ _ _ Hm). exact (proj2 Ha).
    - intros a Ha _. apply M; [|exact (proj1 Ha)]. intros Hw. exact (proj2 Ha (HW a Hw)).
    - intros a Ha. apply A, (proj1 Ha).
  Qed.

  (** The collector keeps the stack (from its frame conditions in [Hgc]). *)
  Lemma keeps_stack_gc st st' rs :
    (forall a, ~ in_heap st a -> ~ slot_bytes rs a ->
               IntMaps.lookup a (mem_of st') = IntMaps.lookup a (mem_of st)) ->
    (forall a, in_heap st' a -> in_heap st a \/ IntMaps.lookup a (mem_of st) = None) ->
    (forall a, slot_bytes rs a -> aid_at st' a = aid_at st a) ->
    keeps_stack st st' rs.
  Proof.
    intros Hnh Hgrow Hslaid.
    assert (A : forall a, alloc_nonheap st a -> aid_at st' a = aid_at st a).
    { intros a (Ha & Hn). destruct (classic (slot_bytes rs a)) as [Hs|Hs]; [apply Hslaid, Hs|].
      unfold aid_at. rewrite Hnh; auto. }
    split; [|split; [|split]].
    - intros a Ha. pose proof (A a Ha) as E. destruct Ha as (Ha & _). unfold aid_at in E.
      destruct (IntMaps.lookup a (mem_of st')); [discriminate|].
      destruct (IntMaps.lookup a (mem_of st)); [discriminate|contradiction].
    - intros a (Ha & Hn) Hin. destruct (Hgrow a Hin) as [H|H]; [exact (Hn H)|exact (Ha H)].
    - intros a (_ & Hn) Hs. apply Hnh; assumption.
    - exact A.
  Qed.

  (** Composing with an inner activation whose root slots [rs1 ++ rs] extend
      the caller's [rs] by slots that were not allocated stack before. *)
  Lemma keeps_stack_slots st st1 st2 rs rs1 :
    keeps_stack st st1 rs -> keeps_stack st1 st2 (rs1 ++ rs) ->
    (forall a, slot_bytes rs1 a -> ~ alloc_nonheap st a) ->
    keeps_stack st st2 rs.
  Proof.
    intros K. pose proof K as (A1 & A2 & A3 & A4). intros (B1 & B2 & B3 & B4) Hfr.
    assert (Hn : forall a, alloc_nonheap st a -> alloc_nonheap st1 a)
      by (intros a; apply keeps_stack_nonheap with rs; exact K).
    split; [|split; [|split]].
    - intros a Ha. apply B1, Hn, Ha.
    - intros a Ha. apply B2, Hn, Ha.
    - intros a Ha Hs. rewrite B3; [apply A3; assumption|apply Hn, Ha|].
      intros (r & Hr & Hra). apply in_app_or in Hr. destruct Hr as [Hr|Hr].
      + apply (Hfr a); [exists r; auto|exact Ha].
      + apply Hs. exists r. auto.
    - intros a Ha. rewrite B4 by (apply Hn, Ha). apply A4, Ha.
  Qed.

  (* ------------------------------------------------------------------ *)
  (** ** Invariants *)

  (** A representation that survives everything the generated code may later
      do to the heap. *)
  Definition stable_repr (st : state) (v : term.val) (z : Z) : Prop :=
    forall st2, heap_bytes_agree_except st st2 (not_object st tinfo) ->
      repr_val cenv fds G st2 v z.

  (** The runtime-level invariant: heap invariant, well-formed [thread_info],
      well-formed memory, and a shadow stack whose roots [rs] represent [vs]. *)
  Definition INV (st : state) (fp : ptr) (rs : list ptr) (vs : list term.val) : Prop :=
    heap_inv st tinfo /\ tinfo_ok st tinfo /\ mem_ok st /\ nursery_tinfo_disjoint st tinfo /\
    field st tinfo off_fp fp /\ shadow_stack st fp rs /\ stack_ok st fp rs /\
    roots_ok cenv fds G st tinfo rs vs.

  (** Source environment vs. Vellvm locals, on the variables [S].  Top-level
      functions are globals; every other variable is held, under its current
      SSA name [env x], as a word that stably represents its value. *)
  Definition env_rel (S : var -> Prop) (rho : M.t term.val) (env : nenv)
             (sf : stack_frame) (st : state) : Prop :=
    forall x, S x ->
      exists v, M.get x rho = Some v /\
        if is_fun fs x then exists rho', v = Vfun rho' fds x
        else exists z, RM.find (env x) (stack_vars sf) = Some (I64 z) /\ stable_repr st v z.

  (** [tinfo] is passed to every emitted function as its [%tinfo] parameter. *)
  Definition tinfo_local (sf : stack_frame) : Prop :=
    RM.find (Name "tinfo") (stack_vars sf) = Some (Ptr tinfo).

  (** The SSA environment only uses names the translation will not write
      again: ANF names, and, for the live variables [S], safepoint names with
      a seed below [fresh]; a variable outside [S] is under its ANF name. *)
  Definition env_ok (S : var -> Prop) (env : nenv) (fresh : positive) : Prop :=
    forall y, (S y -> env y = Raw (Zpos y) \/
                      exists s k, (s < fresh)%positive /\ env y = ssname s k) /\
              (~ S y -> env y = Raw (Zpos y)).

  (** The runtime's guarantees (the last two clauses of [runtime_correct],
      with the memory well-formedness added). *)
  Hypothesis Hmut : forall st st2 alloc alloc2 limit,
       heap_inv st tinfo -> tinfo_ok st tinfo ->
       heap_agree_except st st2 (mutator_writes st tinfo) ->
       field st tinfo off_alloc alloc -> field st tinfo off_limit limit ->
       field st2 tinfo off_alloc alloc2 ->
       (ptr_to_int alloc <= ptr_to_int alloc2 <= ptr_to_int limit)%Z ->
       (ptr_to_int alloc2 mod 8 = 0)%Z ->
       heap_inv st2 tinfo.
  Hypothesis Hgc : forall (st : state) ls fp rs vs nalloc,
       heap_inv st tinfo -> tinfo_ok st tinfo -> mem_ok st -> nursery_tinfo_disjoint st tinfo ->
       field st tinfo off_fp fp ->
       shadow_stack st fp rs ->
       roots_ok cenv fds G st tinfo rs vs ->
       0 <= nalloc < 2 ^ 61 ->
       (exists a, ptr_off tinfo off_nalloc a /\ reads_word st a nalloc) ->
       ends_in_oom (interp_mcfg (gc [Ptr tinfo]) (st, (ls, G)))
       \/ exists st',
           returns (interp_mcfg (gc [Ptr tinfo]) (st, (ls, G)))
                   ((st', (ls, G)), inr (DVALUE_Base DVALUE_None)) /\
           frames_of st' = frames_of st /\
           heap_inv st' tinfo /\ tinfo_ok st' tinfo /\ mem_ok st' /\ nursery_tinfo_disjoint st' tinfo /\
           field st' tinfo off_fp fp /\
           shadow_stack st' fp rs /\
           roots_ok cenv fds G st' tinfo rs vs /\
           room st' tinfo nalloc /\
           (forall a, ~ in_heap st a -> ~ slot_bytes rs a ->
                      IntMaps.lookup a (mem_of st') = IntMaps.lookup a (mem_of st)) /\
           (forall a, in_heap st' a -> in_heap st a \/ IntMaps.lookup a (mem_of st) = None) /\
           (forall a, slot_bytes rs a -> aid_at st' a = aid_at st a).

  (* ------------------------------------------------------------------ *)
  (** ** Preservation of the invariants by the mutator's steps *)

  (** [thread_info] fits in the address space (part of [tinfo_ok] eventually). *)
  Hypothesis Htinfo_range : ptr_to_int tinfo + 8232 < 2^64.

  Lemma tinfo_field_ex off : 0 <= off -> off + 8 <= 8232 -> exists a, ptr_off tinfo off a.
  Proof. intros H1 H2. apply ptr_off_ex. pose proof (ptr_to_int_range tinfo). lia. Qed.

  Lemma nursery_in_heap st a : tinfo_ok st tinfo -> nursery st tinfo a -> in_heap st a.
  Proof.
    intros (_ & _ & alloc & limit & Ha & Hl & _ & _ & Hin & _) (alloc' & limit' & Ha' & Hl' & Hr).
    rewrite (field_det _ _ _ _ Ha' Ha), (field_det _ _ _ _ Hl' Hl) in Hr. apply Hin. exact Hr.
  Qed.

  Lemma field_addr_in_heap st off b :
    tinfo_ok st tinfo -> In off [off_alloc; off_limit; off_fp; off_nalloc] ->
    field_addr tinfo off b -> in_heap st b.
  Proof.
    intros (Hf & _) Hoff Hb.
    assert (0 <= off /\ off + 8 <= 8232) as [H1 H2].
    { unfold off_alloc, off_limit, off_fp, off_nalloc in Hoff. simpl in Hoff. lia. }
    destruct (tinfo_field_ex off H1 H2) as (a & Ha).
    destruct (Hf off a Hoff Ha) as (_ & Hin). apply Hin. exact Hb.
  Qed.

  Lemma mutator_in_heap st a : tinfo_ok st tinfo -> mutator_writes st tinfo a -> in_heap st a.
  Proof.
    intros Hok [Hn|[Hf|[Hf|Hf]]]; [eapply nursery_in_heap; eauto|..];
      eapply field_addr_in_heap; eauto; simpl; auto.
  Qed.

  Lemma mutator_not_object st a : mutator_writes st tinfo a -> not_object st tinfo a.
  Proof.
    intros [Hn|[Hf|[Hf|Hf]]]; [left; exact Hn|..]; right; unfold field_addr in Hf;
      unfold off_alloc, off_fp, off_nalloc in Hf; lia.
  Qed.

  (** Non-heap bytes are untouched by a step writing only heap addresses. *)
  Lemma mstep_nonheap st st2 W a :
    mstep st st2 W -> (forall a, W a -> in_heap st a) -> alloc_nonheap st a ->
    IntMaps.lookup a (mem_of st2) = IntMaps.lookup a (mem_of st).
  Proof. intros (_ & M & _) HW (Ha & Hn). apply M; auto. Qed.

  Lemma mstep_same_bytes_nonheap st st2 W a n :
    mstep st st2 W -> (forall a, W a -> in_heap st a) ->
    (forall a', a <= a' < a + n -> alloc_nonheap st a') -> same_bytes st st2 a n.
  Proof. intros H HW Hn a' Ha. eapply mstep_nonheap; eauto. Qed.

  Lemma alloc_nonheap_mstep st st2 W a :
    mstep st st2 W -> alloc_nonheap st a -> alloc_nonheap st2 a.
  Proof.
    intros H (Ha & Hn). split; [eapply mstep_alloc; eauto|].
    rewrite (in_heap_mstep _ _ _ _ H). exact Hn.
  Qed.

  Lemma heap_agree_mstep st st2 W :
    mstep st st2 W -> mem_ok st -> heap_agree_except st st2 W.
  Proof.
    intros (E & M & _) (Hm & _). split; [exact E|]. intros a Hin Hn. apply M; auto.
  Qed.

  Lemma slots_from_state st st2 s e rs : slots_from st s e rs -> slots_from st2 s e rs.
  Proof. induction 1; econstructor; eauto. Qed.

  (** The shadow stack and its frames survive a step that only writes heap
      addresses. *)
  Lemma shadow_stack_chain st st2 fp rs frs :
    shadow_stack st fp rs -> chain st fp frs ->
    (forall f, In f frs -> same_bytes st st2 (ptr_to_int f) 24) ->
    shadow_stack st2 fp rs /\ chain st2 fp frs.
  Proof.
    intros Hss. revert frs. induction Hss as [f H0|f e s prev rs rs' Hnz He Hs Hp Hsl Hss IH];
      intros frs Hc Hb.
    - inversion Hc; subst; [|contradiction]. split; constructor; auto.
    - inversion Hc as [|? prev' frs' ? Hp' Hc']; subst; [contradiction|].
      destruct Hp as (a & Ha & Hr). destruct Hp' as (a' & Ha' & Hr').
      assert (a' = a). { unfold ptr_off in Ha, Ha'. rewrite Ha in Ha'. injection Ha'. auto. }
      subst a'. assert (prev' = prev) by (eapply reads_ptr_det; eauto). subst prev'.
      assert (Hf : same_bytes st st2 (ptr_to_int f) 24) by (apply Hb; left; reflexivity).
      destruct (IH frs' Hc') as [Hss2 Hc2]; [intros g Hg; apply Hb; right; exact Hg|].
      split.
      + apply (@SS_frame st2 f e s prev rs rs'); [exact Hnz| | | | |exact Hss2].
        * eapply reads_ptr_frame; eauto. intros b Hb'. apply Hf. lia.
        * destruct Hs as (b & Hb1 & Hb2). exists b. split; [exact Hb1|].
          eapply reads_ptr_frame; eauto. rewrite (ptr_off_int _ _ _ Hb1). intros c Hc0. apply Hf. lia.
        * exists a. split; [exact Ha|]. eapply reads_ptr_frame; eauto.
          rewrite (ptr_off_int _ _ _ Ha). intros c Hc0. apply Hf. lia.
        * eapply slots_from_state; eauto.
      + apply (chain_cons st2 f prev frs'); auto. exists a. split; [exact Ha|]. eapply reads_ptr_frame; eauto.
        rewrite (ptr_off_int _ _ _ Ha). intros c Hc0. apply Hf. lia.
  Qed.

  Lemma stack_ok_mstep st st2 W fp rs :
    mstep st st2 W -> (forall a, W a -> in_heap st a) ->
    shadow_stack st fp rs -> stack_ok st fp rs ->
    shadow_stack st2 fp rs /\ stack_ok st2 fp rs.
  Proof.
    intros H HW Hss ((frs & Hc & Hfr & Hfs) & Hsl).
    assert (Hb : forall f, In f frs -> same_bytes st st2 (ptr_to_int f) 24).
    { intros f Hf. eapply mstep_same_bytes_nonheap; [exact H|exact HW|]. intros a Ha. apply (Hfr f Hf). exact Ha. }
    destruct (shadow_stack_chain st st2 fp rs frs Hss Hc Hb) as [Hss2 Hc2].
    split; [exact Hss2|]. split.
    - exists frs. split; [exact Hc2|]. split; [|exact Hfs]. intros f Hf a Ha. eapply alloc_nonheap_mstep; eauto.
    - intros a Ha. eapply alloc_nonheap_mstep; eauto.
  Qed.

  (** Transitivity of heap agreement, when the second step's exceptions are
      contained in the first's. *)
  Lemma heap_bytes_agree_trans st st2 st3 S S' :
    heap_bytes_agree_except st st2 S -> heap_bytes_agree_except st2 st3 S' ->
    heap_of st2 = heap_of st -> (forall a, S' a -> S a) ->
    heap_bytes_agree_except st st3 S.
  Proof.
    intros H1 H2 E HS a Hin Hn. rewrite H2; [apply H1; auto| |auto].
    unfold in_heap. rewrite E. exact Hin.
  Qed.

  Lemma nursery_mono st st2 alloc alloc2 limit :
    field st tinfo off_alloc alloc -> field st tinfo off_limit limit ->
    field st2 tinfo off_alloc alloc2 -> field st2 tinfo off_limit limit ->
    ptr_to_int alloc <= ptr_to_int alloc2 ->
    forall a, nursery st2 tinfo a -> nursery st tinfo a.
  Proof.
    intros Ha Hl Ha2 Hl2 Hle a (al & li & Hal & Hli & Hr).
    rewrite (field_det _ _ _ _ Hal Ha2), (field_det _ _ _ _ Hli Hl2) in Hr.
    exists alloc, limit. repeat split; auto; lia.
  Qed.

  Lemma not_object_mono st st2 :
    (forall a, nursery st2 tinfo a -> nursery st tinfo a) ->
    forall a, not_object st2 tinfo a -> not_object st tinfo a.
  Proof. intros H a [Hn|Ht]; [left; auto|right; auto]. Qed.

  Lemma stable_repr_mono st st2 v z :
    stable_repr st v z ->
    heap_bytes_agree_except st st2 (not_object st tinfo) ->
    heap_of st2 = heap_of st ->
    (forall a, nursery st2 tinfo a -> nursery st tinfo a) ->
    stable_repr st2 v z.
  Proof.
    intros Hs Hag E Hn st3 Hag3. apply Hs. eapply heap_bytes_agree_trans; eauto.
    apply not_object_mono. exact Hn.
  Qed.

  Lemma roots_ok_mono st st2 rs vs :
    roots_ok cenv fds G st tinfo rs vs ->
    heap_bytes_agree_except st st2 (not_object st tinfo) ->
    heap_of st2 = heap_of st ->
    (forall a, nursery st2 tinfo a -> nursery st tinfo a) ->
    (forall r, In r rs -> same_bytes st st2 (ptr_to_int r) 8) ->
    roots_ok cenv fds G st2 tinfo rs vs.
  Proof.
    intros (zs & Hz & Hv) Hag E Hn Hr. exists zs. split.
    - clear Hv. induction Hz as [|r z rs zs H1 H2 IH]; constructor.
      + eapply reads_word_frame; eauto. apply Hr. left. reflexivity.
      + apply IH. intros r' Hr'. apply Hr. right. exact Hr'.
    - intros st3 Hag3. apply Hv. eapply heap_bytes_agree_trans; eauto. apply not_object_mono. exact Hn.
  Qed.

  Lemma env_rel_mono S rho env sf st st2 :
    env_rel S rho env sf st ->
    heap_bytes_agree_except st st2 (not_object st tinfo) ->
    heap_of st2 = heap_of st ->
    (forall a, nursery st2 tinfo a -> nursery st tinfo a) ->
    env_rel S rho env sf st2.
  Proof.
    intros H Hag E Hn x Hx. destruct (H x Hx) as (v & Hv & Hc). exists v. split; [exact Hv|].
    destruct (is_fun fs x); [exact Hc|]. destruct Hc as (z & Hz & Hs). exists z. split; [exact Hz|].
    eapply stable_repr_mono; eauto.
  Qed.

  Lemma writable_word_mstep st st2 W p :
    mstep st st2 W -> writable_word st p ->
    (forall a, ptr_to_int p <= a < ptr_to_int p + 8 -> IntMaps.lookup a (mem_of st) <> None) ->
    writable_word st2 p.
  Proof. intros (_ & _ & A & _) W0 Ha. eapply writable_word_aid; eauto. Qed.

  Lemma writable_word_alloc st p : writable_word st p ->
    forall a, ptr_to_int p <= a < ptr_to_int p + 8 -> IntMaps.lookup a (mem_of st) <> None.
  Proof.
    intros W a Ha. apply writable_word_iff in W. destruct W as (ptrs & Hp & Hw).
    apply gcp_spec in Hp. destruct Hp as [Hl Hc].
    assert (exists q, In q ptrs /\ ptr_to_int q = a) as (q & Hq & <-).
    { destruct (nth_error ptrs (Z.to_nat (a - ptr_to_int p))) as [q|] eqn:E.
      - exists q. split; [eapply nth_error_In; eauto|].
        destruct (Hc _ _ E) as [Hi _]. rewrite Hi. lia.
      - apply nth_error_None in E. lia. }
    destruct (Hw q Hq) as (aid & Haid & _). unfold aid_at in Haid.
    destruct (IntMaps.lookup (ptr_to_int q) (mem_of st)); [discriminate|discriminate].
  Qed.

  (** Main preservation lemma: a mutator step keeps every part of the
      invariant that does not mention the [fp] field, provided the nursery
      pointer only moved forward (staying aligned and with the same
      provenance).  [tinfo_ok] needs some well-formed shadow stack at the
      new [fp] field: [fp'], [rs']. *)
  Lemma INV_mstep_gen st st2 W fp rs vs alloc alloc2 limit fp' rs' :
    INV st fp rs vs ->
    mstep st st2 W ->
    (forall a, W a -> mutator_writes st tinfo a) ->
    field st tinfo off_alloc alloc -> field st tinfo off_limit limit ->
    field st2 tinfo off_alloc alloc2 ->
    ptr_to_int alloc <= ptr_to_int alloc2 <= ptr_to_int limit ->
    ptr_to_int alloc2 mod 8 = 0 ->
    ptr_provenance alloc2 = ptr_provenance alloc ->
    field st2 tinfo off_fp fp' -> shadow_stack st2 fp' rs' ->
    heap_inv st2 tinfo /\ tinfo_ok st2 tinfo /\ mem_ok st2 /\ nursery_tinfo_disjoint st2 tinfo /\
    shadow_stack st2 fp rs /\ stack_ok st2 fp rs /\ roots_ok cenv fds G st2 tinfo rs vs /\
    (forall a, nursery st2 tinfo a -> nursery st tinfo a) /\
    heap_bytes_agree_except st st2 (not_object st tinfo).
  Proof.
    intros (Hhi & Hok & Hmem & Hdis & Hfp & Hss & Hsk & Hroots) Hm HW Ha Hl Ha2 Hle Hal Hprov Hfp' Hss'.
    assert (HWh : forall a, W a -> in_heap st a) by (intros a Ha'; eapply mutator_in_heap; eauto).
    assert (Hag : heap_agree_except st st2 (mutator_writes st tinfo)).
    { destruct (heap_agree_mstep _ _ _ Hm Hmem) as [E M]. split; [exact E|].
      intros a Hin Hn. apply M; auto. }
    pose proof Hm as Hm'. destruct Hm' as (E & M & A & ks & F & K).
    (* fields other than alloc/fp... the limit field is unchanged *)
    assert (Hfield : forall off q, In off [off_limit; off_fp] -> field st tinfo off q ->
                                   (forall a, W a -> ~ field_addr tinfo off a) -> field st2 tinfo off q).
    { intros off q Hoff Hq Hnw. eapply field_frame; eauto. intros a Hra.
      apply M.
      - intros Hw. apply (Hnw a Hw). unfold field_addr. lia.
      - destruct Hmem as [Hm1 _]. apply Hm1. apply (field_addr_in_heap st off a Hok).
        + destruct Hoff as [<-|[<-|[]]]; simpl; auto.
        + unfold field_addr. lia. }
    assert (Hl2 : field st2 tinfo off_limit limit).
    { apply (Hfield off_limit limit); [simpl; auto|exact Hl|]. intros a Hw Hf. apply HW in Hw.
      unfold field_addr, off_limit in Hf.
      destruct Hw as [Hn|[Hf'|[Hf'|Hf']]].
      - apply (Hdis a Hn). lia.
      - unfold field_addr, off_alloc in Hf'. lia.
      - unfold field_addr, off_fp in Hf'. lia.
      - unfold field_addr, off_nalloc in Hf'. lia. }
    assert (Hn2 : forall a, nursery st2 tinfo a -> nursery st tinfo a).
    { eapply nursery_mono; eauto. lia. }
    assert (Hnob : heap_bytes_agree_except st st2 (not_object st tinfo)).
    { destruct Hag as [_ M']. intros a Hin Hn. apply M'; auto. intros Hw. apply Hn.
      apply mutator_not_object. exact Hw. }
    destruct (stack_ok_mstep _ _ _ _ _ Hm HWh Hss Hsk) as [Hss2 Hsk2].
    split; [|split; [|split; [|split; [|split; [|split; [|split; [|split]]]]]]].
    - eapply Hmut; eauto.
    - (* tinfo_ok *)
      destruct Hok as (Hf & _ & al & li & Hal' & Hli' & Halig & Hle' & Hin & Hwr & Hlal).
      pose proof (field_det _ _ _ _ Hal' Ha) as ->. pose proof (field_det _ _ _ _ Hli' Hl) as ->.
      split; [|split].
      + intros off a Hoff Hoa. destruct (Hf off a Hoff Hoa) as (Hw & Hin').
        split.
        * eapply writable_word_mstep; eauto. eapply writable_word_alloc; eauto.
        * intros b Hb. rewrite (in_heap_mstep _ _ _ _ Hm). apply Hin'. exact Hb.
      + exists fp', rs'. split; [exact Hfp'|exact Hss'].
      + exists alloc2, limit. split; [exact Ha2|]. split; [exact Hl2|].
        split; [exact Hal|]. split; [lia|]. split; [|split].
        * intros a Hr. rewrite (in_heap_mstep _ _ _ _ Hm). apply Hin. lia.
        * intros i q Hi Hq.
          set (k := (ptr_to_int alloc2 - ptr_to_int alloc) / 8).
          assert (Hk : ptr_to_int alloc2 - ptr_to_int alloc = 8 * k).
          { unfold k. apply Z.div_exact; [lia|]. rewrite Zminus_mod, Hal, Halig. reflexivity. }
          assert (Hq' : ptr_off alloc (8 * (i + k)) q).
          { unfold ptr_off in *. rewrite <- Hq, Hprov. f_equal. lia. }
          assert (Hw : writable_word st q) by (apply (Hwr (i + k) q); [lia|exact Hq']).
          eapply writable_word_mstep; [exact Hm|exact Hw|]. eapply writable_word_alloc; exact Hw.
        * exact Hlal.
    - (* mem_ok *)
      destruct Hmem as (Hm1 & Hm2). split.
      + intros a Hin. rewrite (in_heap_mstep _ _ _ _ Hm) in Hin. eapply mstep_alloc; eauto.
      + intros a Hfr. rewrite (in_heap_mstep _ _ _ _ Hm).
        assert (Hfresh : forall k, In k ks -> ~ in_heap st (ptr_to_int k)).
        { intros k Hk Hin. rewrite Forall_forall in K. apply Hm1 in Hin. apply Hin. apply K. exact Hk. }
        unfold in_frames in Hfr. rewrite F in Hfr.
        apply in_map_iff in Hfr. destruct Hfr as (k & <- & Hk).
        destruct (frames_of st) as [f0|s0 f0] eqn:Efr; cbn [push_top frames_ptrs] in Hk.
        * rewrite in_app_iff, <- in_rev in Hk. destruct Hk as [Hk|Hk]; [apply Hfresh; exact Hk|].
          apply Hm2. unfold in_frames. rewrite Efr. cbn [frames_ptrs]. apply in_map_iff. exists k. auto.
        * rewrite !in_app_iff, <- in_rev in Hk. destruct Hk as [[Hk|Hk]|Hk]; [apply Hfresh; exact Hk|..];
            apply Hm2; unfold in_frames; rewrite Efr; cbn [frames_ptrs]; apply in_map_iff; exists k;
            (split; [reflexivity|apply in_app_iff; auto]).
    - intros a Hn. apply Hdis. apply Hn2. exact Hn.
    - exact Hss2.
    - exact Hsk2.
    - eapply roots_ok_mono; eauto. intros r Hr. destruct Hsk as (_ & Hsl).
      eapply mstep_same_bytes_nonheap; eauto. intros a Ha'. apply Hsl. exists r. split; auto.
    - exact Hn2.
    - exact Hnob.
  Qed.

  (** A step not touching the [fp] field keeps the whole invariant. *)
  Lemma INV_mstep st st2 W fp rs vs alloc alloc2 limit :
    INV st fp rs vs ->
    mstep st st2 W ->
    (forall a, W a -> mutator_writes st tinfo a) ->
    (forall a, W a -> ~ field_addr tinfo off_fp a) ->
    field st tinfo off_alloc alloc -> field st tinfo off_limit limit ->
    field st2 tinfo off_alloc alloc2 ->
    ptr_to_int alloc <= ptr_to_int alloc2 <= ptr_to_int limit ->
    ptr_to_int alloc2 mod 8 = 0 ->
    ptr_provenance alloc2 = ptr_provenance alloc ->
    INV st2 fp rs vs.
  Proof.
    intros HI Hm HW Hfpw Ha Hl Ha2 Hle Hal Hprov.
    pose proof HI as (Hhi & Hok & Hmem & Hdis & Hfp & Hss & Hsk & Hroots).
    assert (HWh : forall a, W a -> in_heap st a) by (intros a Ha'; eapply mutator_in_heap; eauto).
    destruct (stack_ok_mstep _ _ _ _ _ Hm HWh Hss Hsk) as [Hss2 Hsk2].
    assert (Hfp2 : field st2 tinfo off_fp fp).
    { eapply field_frame; eauto. intros a Hra. destruct Hm as (_ & M & _). apply M.
      - intros Hw. apply (Hfpw a Hw). unfold field_addr. lia.
      - destruct Hmem as [Hm1 _]. apply Hm1. apply (field_addr_in_heap st off_fp a Hok); [simpl; auto|].
        unfold field_addr. lia. }
    destruct (INV_mstep_gen st st2 W fp rs vs alloc alloc2 limit fp rs HI Hm HW Ha Hl Ha2 Hle Hal Hprov Hfp2 Hss2)
      as (H1 & H2 & H3 & H4 & H5 & H6 & H7 & _).
    split; [exact H1|split; [exact H2|split; [exact H3|split; [exact H4|split; [exact Hfp2|
      split; [exact H5|split; [exact H6|exact H7]]]]]]].
  Qed.

  (** The invariant after a run of the collector (from the conclusions of
      [Hgc]): only [stack_ok] has to be re-established. *)
  Lemma INV_gc st st' fp rs vs :
    INV st fp rs vs ->
    frames_of st' = frames_of st ->
    heap_inv st' tinfo -> tinfo_ok st' tinfo -> mem_ok st' -> nursery_tinfo_disjoint st' tinfo ->
    field st' tinfo off_fp fp -> shadow_stack st' fp rs -> roots_ok cenv fds G st' tinfo rs vs ->
    (forall a, ~ in_heap st a -> ~ slot_bytes rs a ->
               IntMaps.lookup a (mem_of st') = IntMaps.lookup a (mem_of st)) ->
    (forall a, in_heap st' a -> in_heap st a \/ IntMaps.lookup a (mem_of st) = None) ->
    INV st' fp rs vs.
  Proof.
    intros (_ & _ & _ & _ & _ & Hss & ((frs & Hc & Hfr & Hfs) & Hsl) & _) Hfr' Hhi Hok Hmem Hdis Hfp Hss' Hroots Hnh Hgrow.
    split; [exact Hhi|]. split; [exact Hok|]. split; [exact Hmem|]. split; [exact Hdis|].
    split; [exact Hfp|]. split; [exact Hss'|]. split; [|exact Hroots].
    assert (Hnonheap : forall a, alloc_nonheap st a -> ~ slot_bytes rs a -> alloc_nonheap st' a).
    { intros a (Ha & Hn) Hs. split.
      - rewrite Hnh; auto.
      - intros Hin. destruct (Hgrow a Hin) as [Hin'|Hun]; [exact (Hn Hin')|exact (Ha Hun)]. }
    assert (Hb : forall f, In f frs -> same_bytes st st' (ptr_to_int f) 24).
    { intros f Hf a Ha. apply Hnh; [apply (Hfr f Hf); exact Ha|apply (Hfs f Hf); exact Ha]. }
    destruct (shadow_stack_chain st st' fp rs frs Hss Hc Hb) as [_ Hc'].
    split.
    - exists frs. split; [exact Hc'|]. split; [|exact Hfs].
      intros f Hf a Ha. apply Hnonheap; [apply (Hfr f Hf); exact Ha|apply (Hfs f Hf); exact Ha].
    - intros a Ha. destruct (Hsl a Ha) as (Hal & Hn). split.
      + (* the slot is read by [roots_ok st'] *)
        destruct Hroots as (zs & Hz & _). destruct Ha as (r & Hr & Hra).
        destruct (Forall2_In_l _ _ _ _ Hz Hr) as (z & _ & Hread).
        destruct Hread as (st'' & Hrun). apply read_dvalue_runs in Hrun.
        destruct Hrun as (_ & ptrs & bs & Hp & HF & _). apply gcp_spec in Hp. destruct Hp as [Hl Hcons].
        rewrite sizeof_i64 in Hl.
        assert (exists q, In q ptrs /\ ptr_to_int q = a) as (q & Hq & <-).
        { destruct (nth_error ptrs (Z.to_nat (a - ptr_to_int r))) as [q|] eqn:E.
          - exists q. split; [eapply nth_error_In; eauto|]. destruct (Hcons _ _ E) as [Hi _]. rewrite Hi. lia.
          - apply nth_error_None in E. lia. }
        destruct (Forall2_In_l _ _ _ _ HF Hq) as (b & _ & (aid & Hb' & _)). rewrite Hb'. discriminate.
      + intros Hin. destruct (Hgrow _ Hin) as [Hin'|Hun]; [exact (Hn Hin')|exact (Hal Hun)].
  Qed.

  (* ------------------------------------------------------------------ *)
  (** ** Pointers *)

  Lemma ptr_ext (p q : ptr) : ptr_to_int p = ptr_to_int q -> ptr_provenance p = ptr_provenance q -> p = q.
  Proof.
    intros Hi Hp.
    pose proof (int_to_ptr_ptr_to_int p eq_refl) as E1.
    pose proof (int_to_ptr_ptr_to_int q eq_refl) as E2.
    rewrite <- Hi, <- Hp in E2. rewrite E1 in E2. injection E2. auto.
  Qed.

  Lemma ptr_off_back p off q : ptr_off p off q -> ptr_off q (- off) p.
  Proof.
    intros H. unfold ptr_off. rewrite (ptr_off_int _ _ _ H), (ptr_off_prov _ _ _ H).
    replace (ptr_to_int p + off + - off) with (ptr_to_int p) by lia.
    apply int_to_ptr_ptr_to_int. reflexivity.
  Qed.

  Lemma ptr_off_add p o1 q o2 r : ptr_off p o1 q -> ptr_off q o2 r -> ptr_off p (o1 + o2) r.
  Proof.
    intros H1 H2. unfold ptr_off in *. rewrite <- H2, (ptr_off_int _ _ _ H1), (ptr_off_prov _ _ _ H1).
    f_equal. lia.
  Qed.

  Lemma ptr_off_0 p : ptr_off p 0 p.
  Proof. unfold ptr_off. rewrite Z.add_0_r. apply int_to_ptr_ptr_to_int. reflexivity. Qed.

  (* ------------------------------------------------------------------ *)
  (** ** Local frames *)

  Lemma find_add_eq (id : raw_id) (v : dvalue) (m : local_env) : RM.find id (Maps.add id v m) = Some v.
  Proof. apply RMF.F.add_eq_o. reflexivity. Qed.

  Lemma find_add_neq (id id' : raw_id) (v : dvalue) (m : local_env) :
    id <> id' -> RM.find id' (Maps.add id v m) = RM.find id' m.
  Proof. intros H. apply RMF.F.add_neq_o. exact H. Qed.

  Lemma stack_vars_upd sf m : stack_vars (upd_local_sf sf m) = m.
  Proof. reflexivity. Qed.

  Lemma env_rel_weaken S S' rho env sf st :
    env_rel S rho env sf st -> (forall x, S' x -> S x) -> env_rel S' rho env sf st.
  Proof. intros H Hs x Hx. apply H. apply Hs. exact Hx. Qed.

  (** Writing a local that no live non-function variable is held in. *)
  Lemma env_rel_write S rho env sf st id v :
    env_rel S rho env sf st ->
    (forall x, S x -> is_fun fs x = false -> env x <> id) ->
    env_rel S rho env (upd_local_sf sf (Maps.add id v (stack_vars sf))) st.
  Proof.
    intros H Hn x Hx. destruct (H x Hx) as (w & Hw & Hc). exists w. split; [exact Hw|].
    destruct (is_fun fs x) eqn:Ef; [exact Hc|]. destruct Hc as (z & Hz & Hs).
    exists z. split; [|exact Hs]. rewrite stack_vars_upd, find_add_neq; [exact Hz|].
    intros E. apply (Hn x Hx Ef). symmetry. exact E.
  Qed.

  Lemma tinfo_local_write sf id v :
    tinfo_local sf -> id <> Name "tinfo" ->
    tinfo_local (upd_local_sf sf (Maps.add id v (stack_vars sf))).
  Proof. intros H Hn. unfold tinfo_local. rewrite stack_vars_upd, find_add_neq; auto. Qed.

  (** The SSA environment never uses a flattening name [flat_id _]. *)
  Lemma env_ok_not_flat S env fresh :
    env_ok S env fresh -> forall y, Flatten_sem.is_flat (env y) = false.
  Proof.
    intros H y. destruct (H y) as [H1 H2].
    destruct (classic (S y)) as [Hy|Hy].
    - destruct (H1 Hy) as [E|(s' & k' & _ & E)]; rewrite E.
      + apply Flatten_sem.is_flat_pos.
      + apply Flatten_sem.is_flat_ssname.
    - rewrite (H2 Hy). apply Flatten_sem.is_flat_pos.
  Qed.

  (** [env_rel] only reads non-flattening names, so it is invariant under
      the local-frame relation of [Flatten_sem] ... *)
  Lemma env_rel_noflat S S' rho env fresh sf sf' st :
    env_ok S' env fresh ->
    env_rel S rho env sf st ->
    Flatten_sem.agree_noflat sf sf' ->
    env_rel S rho env sf' st.
  Proof.
    intros Hok H Ha x Hx. destruct (H x Hx) as (w & Hw & Hc). exists w. split; [exact Hw|].
    destruct (is_fun fs x); [exact Hc|]. destruct Hc as (z & Hz & Hs).
    exists z. split; [|exact Hs]. rewrite Ha; [exact Hz|].
    eapply env_ok_not_flat; exact Hok.
  Qed.

  (** ... and in particular under writes to [flat_id] locals. *)
  Lemma env_rel_flat_write S S' rho env fresh sf st c v :
    env_ok S' env fresh ->
    env_rel S rho env sf st ->
    env_rel S rho env (upd_local_sf sf (Maps.add (flat_id c) v (stack_vars sf))) st.
  Proof.
    intros Hok H. apply env_rel_write; [exact H|].
    intros x _ _ E. pose proof (env_ok_not_flat _ _ _ Hok x) as Hf.
    rewrite E in Hf. discriminate.
  Qed.

  Lemma tinfo_local_noflat sf sf' :
    tinfo_local sf -> Flatten_sem.agree_noflat sf sf' -> tinfo_local sf'.
  Proof. intros H Ha. unfold tinfo_local. rewrite Ha; [exact H|reflexivity]. Qed.

  Lemma tinfo_local_flat_write sf c v :
    tinfo_local sf -> tinfo_local (upd_local_sf sf (Maps.add (flat_id c) v (stack_vars sf))).
  Proof. intros H. apply tinfo_local_write; [exact H|discriminate]. Qed.

  (** Binding an ANF variable [x] (under its ANF name) to a word stably
      representing its value. *)
  Lemma env_rel_bind S S' rho env sf st x v z :
    env_rel S rho env sf st ->
    (forall y, S' y -> y = x \/ S y) ->
    (forall y, S y -> is_fun fs y = false -> env y <> Raw (Zpos x)) ->
    env x = Raw (Zpos x) ->
    is_fun fs x = false ->
    stable_repr st v z ->
    env_rel S' (M.set x v rho) env (upd_local_sf sf (Maps.add (Raw (Zpos x)) (I64 z) (stack_vars sf))) st.
  Proof.
    intros H Hs Hn Hx Hf Hz y Hy. destruct (Hs y Hy) as [->|HyS].
    - exists v. rewrite M.gss. split; [reflexivity|]. rewrite Hf. exists z.
      rewrite stack_vars_upd, Hx, find_add_eq. split; [reflexivity|exact Hz].
    - destruct (H y HyS) as (w & Hw & Hc). exists w. split.
      + rewrite M.gso; [exact Hw|]. intros E. subst y. apply (Hn x HyS Hf). exact Hx.
      + destruct (is_fun fs y) eqn:Ef; [exact Hc|]. destruct Hc as (z' & Hz' & Hs').
        exists z'. split; [|exact Hs']. rewrite stack_vars_upd, find_add_neq; [exact Hz'|].
        intros E. apply (Hn y HyS Ef). symmetry. exact E.
  Qed.

  (** [env_ok] gives the non-clash facts [env_rel_write]/[env_rel_bind] need. *)
  Lemma env_ok_not_pos S env fresh x :
    env_ok S env fresh -> ~ S x -> forall y, S y -> y <> x -> env y <> Raw (Zpos x).
  Proof.
    intros H Hx y Hy Hne. destruct (H y) as [H1 _]. destruct (H1 Hy) as [E|(s & k & _ & E)]; rewrite E.
    - intros E'. injection E' as E'. lia.
    - apply ssname_not_pos.
  Qed.

  Lemma env_ok_not_ssname S env fresh s k :
    env_ok S env fresh -> (fresh <= s)%positive -> forall y, env y <> ssname s k.
  Proof.
    intros H Hle y. destruct (H y) as [H1 H2].
    destruct (classic (S y)) as [Hy|Hy].
    - destruct (H1 Hy) as [E|(s' & k' & Hs' & E)]; rewrite E.
      + intros E'. symmetry in E'. apply (ssname_not_pos _ _ _ E').
      + intros E'. apply ssname_inj in E'. destruct E' as [-> _]. lia.
    - rewrite (H2 Hy). intros E'. symmetry in E'. apply (ssname_not_pos _ _ _ E').
  Qed.

  Lemma env_ok_not_ntmp S env fresh s k :
    env_ok S env fresh -> forall y, env y <> ntmp s k.
  Proof.
    intros H y. destruct (H y) as [H1 H2].
    destruct (classic (S y)) as [Hy|Hy].
    - destruct (H1 Hy) as [E|(s' & k' & Hs' & E)]; rewrite E.
      + intros E'. symmetry in E'. apply (ntmp_not_pos _ _ _ E').
      + apply ssname_not_ntmp.
    - rewrite (H2 Hy). intros E'. symmetry in E'. apply (ntmp_not_pos _ _ _ E').
  Qed.

  Lemma env_ok_not_tinfo S env fresh : env_ok S env fresh -> forall y, env y <> Name "tinfo".
  Proof.
    intros H y. destruct (H y) as [H1 H2].
    destruct (classic (S y)) as [Hy|Hy].
    - destruct (H1 Hy) as [E|(s' & k' & Hs' & E)]; rewrite E; [discriminate|]. unfold ssname. discriminate.
    - rewrite (H2 Hy). discriminate.
  Qed.

  Lemma env_ok_weaken S S' env fresh fresh' :
    env_ok S env fresh -> (forall y, S' y -> S y) -> (fresh <= fresh')%positive ->
    (forall y, S y -> ~ S' y -> env y = Raw (Zpos y)) ->
    env_ok S' env fresh'.
  Proof.
    intros H Hs Hle Hr y. destruct (H y) as [H1 H2]. split.
    - intros Hy. destruct (H1 (Hs y Hy)) as [E|(s & k & Hsk & E)]; [left; exact E|].
      right. exists s, k. split; [lia|exact E].
    - intros Hy. destruct (classic (S y)) as [HyS|HyS]; [apply Hr; auto|apply H2; exact HyS].
  Qed.

  (* ------------------------------------------------------------------ *)
  (** ** A freshly allocated boxed constructor is stably represented *)

  Lemma nth_error_Forall2 {A B} (R : A -> B -> Prop) l1 l2 i a :
    Forall2 R l1 l2 -> nth_error l1 i = Some a -> exists b, nth_error l2 i = Some b /\ R a b.
  Proof.
    intros H. revert i. induction H as [|x y l1 l2 Hxy Hl IH]; intros i Hi; [destruct i; discriminate|].
    destruct i as [|i]; simpl in *.
    - injection Hi as <-. exists y. auto.
    - apply IH. exact Hi.
  Qed.

  Lemma stable_repr_boxed st st' t vs zs (a0 p : ptr) :
    tag_ok cenv t ->
    arity_of cenv t = N.of_nat (length vs) ->
    vs <> [] ->
    Forall2 (stable_repr st) vs zs ->
    heap_bytes_agree_except st st' (not_object st tinfo) ->
    heap_of st' = heap_of st ->
    (forall a, nursery st' tinfo a -> nursery st tinfo a) ->
    (forall a, ptr_to_int a0 <= a < ptr_to_int a0 + 8 * (Z.of_nat (length vs) + 1) ->
               in_heap st a /\ ~ not_object st' tinfo a) ->
    ptr_to_int a0 mod 8 = 0 ->
    ptr_off a0 8 p ->
    reads_word st' a0 (Z.of_N (arity_of cenv t) * 1024 + Z.of_N (ord_of cenv t)) ->
    (forall i z, nth_error zs i = Some z ->
                 exists q, ptr_off p (8 * Z.of_nat i) q /\ reads_word st' q z) ->
    stable_repr st' (Vconstr t vs) (ptr_to_int p).
  Proof.
    intros Htag Har Hne Hzs Hag E Hn Hobj Hal Hp Hhdr Hfld st2 Hag2.
    assert (Hag0 : heap_bytes_agree_except st st2 (not_object st tinfo)).
    { eapply heap_bytes_agree_trans; eauto. apply not_object_mono. exact Hn. }
    assert (Hsame : forall a, ptr_to_int a0 <= a < ptr_to_int a0 + 8 * (Z.of_nat (length vs) + 1) ->
                              IntMaps.lookup a (mem_of st2) = IntMaps.lookup a (mem_of st')).
    { intros a Ha. destruct (Hobj a Ha) as [Hin Hno]. apply Hag2; [|exact Hno].
      unfold in_heap. rewrite E. exact Hin. }
    apply (@Repr_boxed cenv fds G st2 t vs p a0); auto.
    - apply ptr_off_back in Hp. exact Hp.
    - eapply reads_word_frame; [exact Hhdr|]. intros a Ha. apply Hsame. lia.
    - assert (Hlen : length zs = length vs) by (symmetry; eapply Forall2_length; eauto).
      assert (Hgen : forall i vs' zs', (i + length vs' = length vs)%nat ->
                       (forall j, (j < length vs')%nat -> nth_error vs' j = nth_error vs (i + j)) ->
                       (forall j, (j < length zs')%nat -> nth_error zs' j = nth_error zs (i + j)) ->
                       length zs' = length vs' ->
                       repr_fields cenv fds G st2 vs' p (8 * Z.of_nat i)).
      { intros i vs'. revert i. induction vs' as [|v vs' IH]; intros i zs' Hi Hv Hz Hl.
        - constructor.
        - destruct zs' as [|z zs']; [discriminate|].
          assert (Hvi : nth_error vs i = Some v).
          { replace i with (i + 0)%nat by lia. rewrite <- (Hv 0%nat); [reflexivity|simpl; lia]. }
          assert (Hzi : nth_error zs i = Some z).
          { replace i with (i + 0)%nat by lia. rewrite <- (Hz 0%nat); [reflexivity|simpl; lia]. }
          destruct (Hfld i z Hzi) as (q & Hq & Hr).
          destruct (nth_error_Forall2 _ _ _ _ _ Hzs Hvi) as (z' & Hz' & Hs). rewrite Hzi in Hz'. injection Hz' as <-.
          apply (@Repr_cons cenv fds G st2 v vs' p (8 * Z.of_nat i) q z); auto.
          + eapply reads_word_frame; [exact Hr|]. intros a Ha. apply Hsame.
            rewrite (ptr_off_int _ _ _ Hq), (ptr_off_int _ _ _ Hp) in Ha.
            assert (Hlt : (i < length vs)%nat) by (apply nth_error_Some; rewrite Hvi; discriminate).
            simpl in Hi. lia.
          + replace (8 * Z.of_nat i + 8) with (8 * Z.of_nat (S i)) by lia.
            apply IH with (zs' := zs').
            * simpl in Hi. lia.
            * intros j Hj. assert (E' := Hv (S j) ltac:(simpl; lia)). cbn [nth_error] in E'. rewrite E'. f_equal. lia.
            * intros j Hj. assert (E' := Hz (S j) ltac:(simpl; lia)). cbn [nth_error] in E'. rewrite E'. f_equal. lia.
            * simpl in Hl. lia. }
      replace 0 with (8 * Z.of_nat 0) by reflexivity.
      apply (Hgen 0%nat vs zs); auto.
    - rewrite (ptr_off_int _ _ _ Hp). replace (ptr_to_int a0 + 8) with (ptr_to_int a0 + 1 * 8) by lia.
      rewrite Z_mod_plus_full. exact Hal.
  Qed.

  (* ------------------------------------------------------------------ *)
  (** ** Object words are protected by [stable_repr]

      [repr_val] (fixed by the statement file) says nothing about whether
      the bytes of a boxed object are in the heap or outside the
      [not_object] region.  This protection nevertheless follows from
      [stable_repr]: if one of the object's bytes were unprotected, deleting
      it from the memory would give a state agreeing with the original one
      outside [not_object], in which the object's header or field could no
      longer be read. *)

  Lemma I64_inj a b : I64 a = I64 b -> a mod 2 ^ 64 = b mod 2 ^ 64.
  Proof.
    intros H. unfold I64 in H.
    apply (f_equal (fun d => match d with
                             | DVALUE_Base (DVALUE_I _ x) => Integers.unsigned x
                             | _ => 0 end)) in H.
    cbv beta iota in H. rewrite !LLVM_mem_lemmas.unsigned_repr64 in H. exact H.
  Qed.

  (** The 8 bytes read by a word read are allocated. *)
  Lemma reads_word_bytes st q z :
    reads_word st q z ->
    forall a, ptr_to_int q <= a < ptr_to_int q + 8 -> IntMaps.lookup a (mem_of st) <> None.
  Proof.
    intros Hr a Ha. apply reads_word_runs, read_dvalue_runs in Hr.
    destruct Hr as (_ & ptrs & bs & Hp & HF & _).
    apply gcp_spec in Hp. destruct Hp as [Hl Hc].
    assert (Hl8 : length ptrs = 8%nat) by (rewrite Hl; reflexivity). clear Hl.
    destruct (nth_error ptrs (Z.to_nat (a - ptr_to_int q))) as [r|] eqn:Er;
      [|apply nth_error_None in Er; lia].
    destruct (Hc _ _ Er) as [Hri _].
    destruct (nth_error_Forall2 _ _ _ _ _ HF Er) as (b & _ & (aid & Hb & _)).
    rewrite Hri in Hb. replace (ptr_to_int q + Z.of_nat (Z.to_nat (a - ptr_to_int q))) with a in Hb by lia.
    rewrite Hb. discriminate.
  Qed.

  (** Word reads only depend on the address, not on the provenance. *)
  Lemma reads_word_det_int st q q' z z' :
    ptr_to_int q = ptr_to_int q' -> reads_word st q z -> reads_word st q' z' -> I64 z = I64 z'.
  Proof.
    intros E Hr Hr'. apply (reads_word_det st q'); [|exact Hr'].
    apply reads_word_runs, read_dvalue_runs in Hr.
    destruct Hr as (_ & ptrs & bs & Hp & HF & Hv).
    pose proof Hr' as Hr2. apply reads_word_runs, read_dvalue_runs in Hr2.
    destruct Hr2 as (_ & ptrs' & bs' & Hp' & HF' & _).
    assert (Hlb := Forall2_length HF). assert (Hlb' := Forall2_length HF').
    apply gcp_spec in Hp. destruct Hp as [Hl Hc].
    pose proof Hp' as Hp2. apply gcp_spec in Hp2. destruct Hp2 as [Hl' Hc'].
    assert (Hl8 : length ptrs = 8%nat) by (rewrite Hl; reflexivity).
    assert (Hl8' : length ptrs' = 8%nat) by (rewrite Hl'; reflexivity). clear Hl Hl'.
    assert (Ebs : bs = bs').
    { apply nth_error_ext. intros n.
      destruct (nth_error ptrs n) as [r|] eqn:Er.
      - destruct (nth_error ptrs' n) as [r'|] eqn:Er';
          [|apply nth_error_None in Er'; assert (n < length ptrs)%nat
              by (apply nth_error_Some; rewrite Er; discriminate); lia].
        destruct (Hc _ _ Er) as [Hr1 _]. destruct (Hc' _ _ Er') as [Hr1' _].
        destruct (nth_error_Forall2 _ _ _ _ _ HF Er) as (b & Eb & (aid & Hb & _)).
        destruct (nth_error_Forall2 _ _ _ _ _ HF' Er') as (b' & Eb' & (aid' & Hb' & _)).
        rewrite Eb, Eb'. rewrite Hr1 in Hb. rewrite Hr1', <- E, Hb in Hb'.
        injection Hb' as ->. reflexivity.
      - apply nth_error_None in Er.
        rewrite (proj2 (nth_error_None bs n)) by lia.
        rewrite (proj2 (nth_error_None bs' n)) by lia. reflexivity. }
    subst bs'. exists st. apply read_dvalue_runs. split; [reflexivity|].
    exists ptrs', bs. auto.
  Qed.

  (** Representations are determined by their value modulo [2^64]. *)
  Lemma repr_val_inj sa sb v z z' :
    repr_val cenv fds G sa v z -> repr_val cenv fds G sb v z' ->
    z mod 2 ^ 64 = z' mod 2 ^ 64 -> z = z'.
  Proof.
    intros H1 H2 E.
    assert (Hr : forall s v0 z0, repr_val cenv fds G s v0 z0 ->
                   (exists t, v0 = Vconstr t [] /\ z0 = Z.of_N (ord_of cenv t) * 2 + 1) \/
                   0 <= z0 < 2 ^ 64).
    { intros s v0 z0 H. destruct H.
      - left. eauto.
      - right. apply ptr_to_int_range.
      - right. pose proof (Uint63.to_Z_bounded n) as B.
        assert (Uint63.wB = 2 ^ 63) as W by reflexivity. lia.
      - right. apply ptr_to_int_range. }
    destruct (Hr _ _ _ H1) as [(t & -> & ->)|R1].
    - inversion H2; subst; [reflexivity|congruence].
    - destruct (Hr _ _ _ H2) as [(t & -> & ->)|R2].
      + inversion H1; subst; [reflexivity|congruence].
      + rewrite !Z.mod_small in E by exact R1 || exact R2. exact E.
  Qed.

  Lemma repr_fields_nth s vs p off :
    repr_fields cenv fds G s vs p off ->
    forall i v, nth_error vs i = Some v ->
      exists q z, ptr_off p (off + 8 * Z.of_nat i) q /\ reads_word s q z /\
                  repr_val cenv fds G s v z.
  Proof.
    induction 1 as [p off|v vs p off q z Hq Hr Hv Hf IH]; intros i v0 Hi.
    - destruct i; discriminate.
    - destruct i as [|i]; cbn in Hi.
      + injection Hi as <-. exists q, z. rewrite Z.add_0_r. auto.
      + destruct (IH i v0 Hi) as (q' & z' & Hq' & Hr' & Hv').
        exists q', z'. replace (off + 8 * Z.of_nat (S i)) with (off + 8 + 8 * Z.of_nat i) by lia.
        auto.
  Qed.

  Lemma heap_bytes_agree_refl st S : heap_bytes_agree_except st st S.
  Proof. intros a _ _. reflexivity. Qed.

  (** The header and fields of a stably represented boxed object lie in the
      heap, outside the [not_object] region. *)
  Lemma stable_repr_protect st t vs z :
    vs <> [] -> stable_repr st (Vconstr t vs) z ->
    forall a, z - 8 <= a < z + 8 * Z.of_nat (length vs) ->
              in_heap st a /\ ~ not_object st tinfo a.
  Proof.
    intros Hne Hs a Ha. apply NNPP. intros Hno.
    set (st2 := set_mem st (IntMaps.delete a (mem_of st))).
    assert (Hag : heap_bytes_agree_except st st2 (not_object st tinfo)).
    { intros a' Hin Hn. destruct (Z.eq_dec a a') as [<-|Hne'].
      - exfalso. apply Hno. auto.
      - change (mem_of st2) with (IntMaps.delete a (mem_of st)).
        apply lookup_delete_neq. exact Hne'. }
    assert (Hdel : IntMaps.lookup a (mem_of st2) = None).
    { change (mem_of st2) with (IntMaps.delete a (mem_of st)).
      unfold IntMaps.lookup, IntMaps.delete. apply IntMaps.IP.F.remove_eq_o. reflexivity. }
    specialize (Hs st2 Hag). inversion Hs as [t0 Har E1 E2|t0 vs0 p ph Har Hne0 Hph Hhdr Hf Hal E1 E2| |]; subst.
    - congruence.
    - apply ptr_off_int in Hph.
      destruct (Z_lt_le_dec a (ptr_to_int p)) as [Hlt|Hle].
      + apply (reads_word_bytes _ _ _ Hhdr a); [lia|exact Hdel].
      + set (k := (a - ptr_to_int p) / 8).
        assert (Hk := Z.div_mod (a - ptr_to_int p) 8 ltac:(lia)).
        assert (Hm := Z.mod_pos_bound (a - ptr_to_int p) 8 ltac:(lia)).
        fold k in Hk.
        assert (Hk0 : 0 <= k) by lia.
        assert (Hkl : k < Z.of_nat (length vs)) by lia.
        destruct (nth_error vs (Z.to_nat k)) as [v|] eqn:Ev;
          [|apply nth_error_None in Ev; lia].
        destruct (repr_fields_nth _ _ _ _ Hf _ _ Ev) as (q & zq & Hq & Hrq & _).
        apply ptr_off_int in Hq. rewrite Z2Nat.id in Hq by lia.
        apply (reads_word_bytes _ _ _ Hrq a); [lia|exact Hdel].
  Qed.

  (** Reads inside a stably represented object are preserved by any change
      of the memory outside the [not_object] region. *)
  Lemma stable_repr_reads st st2 t vs z q w :
    vs <> [] -> stable_repr st (Vconstr t vs) z ->
    z - 8 <= ptr_to_int q -> ptr_to_int q + 8 <= z + 8 * Z.of_nat (length vs) ->
    reads_word st q w ->
    heap_bytes_agree_except st st2 (not_object st tinfo) ->
    reads_word st2 q w.
  Proof.
    intros Hne Hs H1 H2 Hr Hag. eapply reads_word_frame; [exact Hr|].
    intros a Ha. destruct (stable_repr_protect _ _ _ _ Hne Hs a ltac:(lia)) as [Hin Hno].
    apply Hag; assumption.
  Qed.

  (** The header of a stably represented boxed object. *)
  Lemma stable_repr_header st t vs z :
    vs <> [] -> stable_repr st (Vconstr t vs) z ->
    arity_of cenv t = N.of_nat (length vs) /\
    exists ph, ptr_to_int ph = z - 8 /\
      reads_word st ph (Z.of_N (arity_of cenv t) * 1024 + Z.of_N (ord_of cenv t)).
  Proof.
    intros Hne Hs. specialize (Hs st (heap_bytes_agree_refl _ _)).
    inversion Hs as [t0 Har E1 E2|t0 vs0 p ph Har Hne0 Hph Hhdr Hf Hal E1 E2| |]; subst.
    - congruence.
    - split; [exact Har|]. exists ph. split; [|exact Hhdr].
      apply ptr_off_int in Hph. lia.
  Qed.

  (** A stably represented boxed object is at an even address (in fact a
      word-aligned one): the emitted boxed/unboxed test [(y & 1) == 0]
      classifies it as boxed. *)
  Lemma stable_repr_even st t vs z :
    vs <> [] -> stable_repr st (Vconstr t vs) z -> z mod 2 = 0.
  Proof.
    intros Hne Hs. specialize (Hs st (heap_bytes_agree_refl _ _)).
    inversion Hs as [t0 Har E1 E2|t0 vs0 p ph Har Hne0 Hph Hhdr Hf Hal E1 E2| |]; subst.
    - congruence.
    - rewrite (Zmod_div_mod 2 8 (ptr_to_int p)) by (lia || (exists 4; lia)).
      rewrite Hal. reflexivity.
  Qed.

  (** Field [i] of a stably represented boxed object holds a word stably
      representing the [i]-th argument. *)
  Lemma stable_repr_field st t vs z i v :
    stable_repr st (Vconstr t vs) z -> nth_error vs i = Some v ->
    exists q zi, ptr_to_int q = z + 8 * Z.of_nat i /\ reads_word st q zi /\
                 stable_repr st v zi.
  Proof.
    intros Hs Hi.
    assert (Hne : vs <> []) by (intros ->; destruct i; discriminate).
    pose proof (Hs st (heap_bytes_agree_refl _ _)) as Hs0.
    inversion Hs0 as [t0 Har E1 E2|t0 vs0 p ph Har Hne0 Hph Hhdr Hf Hal E1 E2| |]; subst; [congruence|].
    destruct (repr_fields_nth _ _ _ _ Hf _ _ Hi) as (q & zi & Hq & Hrq & Hv).
    apply ptr_off_int in Hq.
    assert (Hlt : (i < length vs)%nat) by (apply nth_error_Some; rewrite Hi; discriminate).
    exists q, zi. split; [lia|]. split; [exact Hrq|].
    intros st2 Hag. pose proof (Hs st2 Hag) as Hs2.
    inversion Hs2 as [t1 Har1 E3 E4|t1 vs1 p1 ph1 Har1 Hne1 Hph1 Hhdr1 Hf1 Hal1 E3 E4| |]; subst; [congruence|].
    destruct (repr_fields_nth _ _ _ _ Hf1 _ _ Hi) as (q1 & zi1 & Hq1 & Hrq1 & Hv1).
    apply ptr_off_int in Hq1.
    assert (Hrq2 : reads_word st2 q zi).
    { eapply stable_repr_reads; [exact Hne|exact Hs|lia|lia|exact Hrq|exact Hag]. }
    assert (E : I64 zi = I64 zi1).
    { eapply reads_word_det_int; [|exact Hrq2|exact Hrq1]. assert (ptr_to_int p1 = ptr_to_int p) by assumption. lia. }
    apply I64_inj in E. rewrite (repr_val_inj _ _ _ _ _ Hv Hv1 E). exact Hv1.
  Qed.

  (* ------------------------------------------------------------------ *)
  (** ** Linking and unlinking a shadow-stack frame *)

  Lemma slots_from_det st s e rs rs' : slots_from st s e rs -> slots_from st s e rs' -> rs = rs'.
  Proof.
    intros H. revert rs'. induction H as [s e H0|s e s' rs Hlt Hs Hr IH]; intros rs' H'.
    - inversion H'; subst; [reflexivity|lia].
    - inversion H' as [|s'' rs'' Hlt' Hs' Hr']; subst; [lia|].
      assert (s'' = s'). { unfold ptr_off in Hs, Hs'. rewrite Hs in Hs'. injection Hs'. auto. }
      subst s''. f_equal. apply IH. exact Hr'.
  Qed.

  (** A frame [f] whose fields are [e] (roots end), [s] (roots start) and
      [prev]. *)
  Definition frame_fields (st : state) (f e s prev : ptr) : Prop :=
    ptr_to_int f <> 0 /\
    reads_ptr st f e /\
    (exists a, ptr_off f 8 a /\ reads_ptr st a s) /\
    (exists a, ptr_off f 16 a /\ reads_ptr st a prev).

  Lemma shadow_stack_link st f e s prev rs1 rs :
    frame_fields st f e s prev -> slots_from st s e rs1 -> shadow_stack st prev rs ->
    shadow_stack st f (rs1 ++ rs).
  Proof. intros (H0 & He & Hs & Hp) Hsl Hss. apply (@SS_frame st f e s prev rs1 rs); auto. Qed.

  Lemma shadow_stack_unlink st f e s prev rs1 rs' :
    frame_fields st f e s prev -> slots_from st s e rs1 ->
    shadow_stack st f rs' -> exists rs, rs' = (rs1 ++ rs)%list /\ shadow_stack st prev rs.
  Proof.
    intros (H0 & He & (a8 & Ha8 & Hs) & (a16 & Ha16 & Hp)) Hsl Hss.
    inversion Hss as [f' H0'|f' e' s' prev' rs1' rs0 H0' He' Hs8 Hp16 Hsl' Hss']; subst; [contradiction|].
    destruct Hs8 as (b8 & Hb8 & Hs'). destruct Hp16 as (b16 & Hb16 & Hp').
    assert (e' = e) by (eapply reads_ptr_det; eauto). subst e'.
    assert (b8 = a8). { unfold ptr_off in Ha8, Hb8. rewrite Ha8 in Hb8. injection Hb8. auto. } subst b8.
    assert (b16 = a16). { unfold ptr_off in Ha16, Hb16. rewrite Ha16 in Hb16. injection Hb16. auto. } subst b16.
    assert (s' = s) by (eapply reads_ptr_det; eauto). subst s'.
    assert (prev' = prev) by (eapply reads_ptr_det; eauto). subst prev'.
    assert (rs1' = rs1) by (eapply slots_from_det; eauto). subst rs1'.
    exists rs0. split; [reflexivity|exact Hss'].
  Qed.

  Lemma roots_ok_app st rs1 zs1 vs1 rs vs :
    Forall2 (reads_word st) rs1 zs1 -> Forall2 (stable_repr st) vs1 zs1 ->
    roots_ok cenv fds G st tinfo rs vs ->
    roots_ok cenv fds G st tinfo (rs1 ++ rs) (vs1 ++ vs).
  Proof.
    intros H1 H2 (zs & Hz & Hv). exists (zs1 ++ zs)%list. split; [apply Forall2_app; auto|].
    intros st2 Hag. apply Forall2_app; [|apply Hv; exact Hag].
    clear H1 Hz Hv. induction H2; constructor; auto.
  Qed.

  Lemma Forall2_app_inv' {A B} (R : A -> B -> Prop) l1 l2 l1' l2' :
    Forall2 R (l1 ++ l1') (l2 ++ l2') -> length l1 = length l2 ->
    Forall2 R l1 l2 /\ Forall2 R l1' l2'.
  Proof.
    revert l2. induction l1 as [|a l1 IH]; intros [|b l2] H Hl; try discriminate.
    - split; [constructor|exact H].
    - simpl in H. inversion H as [|? ? ? ? Hab Htl]; subst.
      destruct (IH l2 Htl ltac:(simpl in Hl; lia)) as [H1 H2]. split; [constructor; auto|exact H2].
  Qed.

  Lemma Forall2_forall_swap {A B C} (P : C -> Prop) (R : C -> A -> B -> Prop) l1 l2 :
    length l1 = length l2 ->
    (forall c, P c -> Forall2 (R c) l1 l2) ->
    Forall2 (fun a b => forall c, P c -> R c a b) l1 l2.
  Proof.
    revert l2. induction l1 as [|a l1 IH]; intros [|b l2] Hl H; try discriminate; constructor.
    - intros c Hc. specialize (H c Hc). inversion H. auto.
    - apply IH; [simpl in Hl; lia|]. intros c Hc. specialize (H c Hc). inversion H. auto.
  Qed.

  (** Splitting [roots_ok] at a frame boundary: the outer roots keep their
      property, and the inner ones are stably represented. *)
  Lemma roots_ok_split' st rs1 rs vs' :
    roots_ok cenv fds G st tinfo (rs1 ++ rs) vs' ->
    exists vs1 vs zs1, vs' = (vs1 ++ vs)%list /\
      Forall2 (reads_word st) rs1 zs1 /\ Forall2 (stable_repr st) vs1 zs1 /\
      roots_ok cenv fds G st tinfo rs vs.
  Proof.
    intros (zs & Hz & Hv).
    assert (Hlen : length (rs1 ++ rs) = length zs) by (eapply Forall2_length; eauto).
    assert (Hlen' : length vs' = length zs).
    { specialize (Hv st). eapply Forall2_length. apply Hv. intros a _ _. reflexivity. }
    exists (firstn (length rs1) vs'), (skipn (length rs1) vs'), (firstn (length rs1) zs).
    rewrite length_app in Hlen.
    split; [symmetry; apply firstn_skipn|].
    assert (Hzs : zs = (firstn (length rs1) zs ++ skipn (length rs1) zs)%list) by (symmetry; apply firstn_skipn).
    rewrite Hzs in Hz. apply Forall2_app_inv' in Hz; [|rewrite length_firstn; lia].
    destruct Hz as [Hz1 Hz2].
    split; [exact Hz1|]. split.
    - apply Forall2_forall_swap; [rewrite !length_firstn; lia|].
      intros st2 Hag. specialize (Hv st2 Hag).
      rewrite <- (firstn_skipn (length rs1) vs'), Hzs in Hv.
      apply Forall2_app_inv' in Hv; [|rewrite !length_firstn; lia]. destruct Hv as [Hv1 _]. exact Hv1.
    - exists (skipn (length rs1) zs). split; [exact Hz2|].
      intros st2 Hag. specialize (Hv st2 Hag).
      rewrite <- (firstn_skipn (length rs1) vs'), Hzs in Hv.
      apply Forall2_app_inv' in Hv; [|rewrite !length_firstn; lia]. destruct Hv as [_ Hv2]. exact Hv2.
  Qed.

  (* ------------------------------------------------------------------ *)
  (** ** Linking a frame at a safepoint *)

  Lemma alloc_le_limit st alloc limit :
    tinfo_ok st tinfo -> field st tinfo off_alloc alloc -> field st tinfo off_limit limit ->
    ptr_to_int alloc <= ptr_to_int limit /\ ptr_to_int alloc mod 8 = 0.
  Proof.
    intros (_ & _ & al & li & Hal & Hli & Halig & Hle & _) Ha Hl.
    rewrite (field_det _ _ _ _ Hal Ha) in *. rewrite (field_det _ _ _ _ Hli Hl) in *. auto.
  Qed.

  (** After a step that allocates a fresh frame [f] (fields [e], [s], [fp])
      and fresh root slots [rs1] holding [zs1], and links [f] into
      [thread_info], the invariant holds for the extended shadow stack. *)
  Lemma INV_link st st2 W fp rs vs alloc limit f e s rs1 zs1 vs1 :
    INV st fp rs vs ->
    mstep st st2 W ->
    (forall a, W a -> mutator_writes st tinfo a) ->
    field st tinfo off_alloc alloc -> field st tinfo off_limit limit ->
    field st2 tinfo off_alloc alloc ->
    field st2 tinfo off_fp f ->
    frame_fields st2 f e s fp ->
    slots_from st2 s e rs1 ->
    Forall2 (reads_word st2) rs1 zs1 ->
    Forall2 (stable_repr st) vs1 zs1 ->
    (forall a, frame_bytes f a -> alloc_nonheap st2 a /\ ~ slot_bytes (rs1 ++ rs) a /\
                                  IntMaps.lookup a (mem_of st) = None) ->
    (forall a, slot_bytes rs1 a -> alloc_nonheap st2 a /\ IntMaps.lookup a (mem_of st) = None) ->
    INV st2 f (rs1 ++ rs) (vs1 ++ vs).
  Proof.
    intros HI Hm HW Ha Hl Ha2 Hf2 Hff Hsl Hrd Hst Hfb Hsb.
    pose proof HI as (Hhi & Hok & Hmem & Hdis & Hfp & Hss & Hsk & Hroots).
    assert (HWh : forall a, W a -> in_heap st a) by (intros a Ha'; eapply mutator_in_heap; eauto).
    destruct (stack_ok_mstep _ _ _ _ _ Hm HWh Hss Hsk) as [Hss2 Hsk2].
    assert (Hss' : shadow_stack st2 f (rs1 ++ rs)) by (eapply shadow_stack_link; eauto).
    destruct (alloc_le_limit st alloc limit Hok Ha Hl) as [Hle Hal].
    destruct (INV_mstep_gen st st2 W fp rs vs alloc alloc limit f (rs1 ++ rs) HI Hm HW Ha Hl Ha2
                ltac:(lia) Hal eq_refl Hf2 Hss') as (H1 & H2 & H3 & H4 & _ & Hsk' & Hroots' & Hn2 & Hnob).
    split; [exact H1|split; [exact H2|split; [exact H3|split; [exact H4|split; [exact Hf2|
      split; [exact Hss'|split]]]]]].
    - (* stack_ok *)
      destruct Hsk' as ((frs & Hc & Hfr & Hfs) & Hsl').
      destruct Hsk as ((frs0 & Hc0 & Hfr0 & _) & _).
      assert (Hfrs : frs0 = frs).
      { destruct (shadow_stack_chain st st2 fp rs frs0 Hss Hc0) as [_ Hc0'].
        { intros g Hg. eapply mstep_same_bytes_nonheap; [exact Hm|exact HWh|]. intros a Ha'. apply (Hfr0 g Hg). exact Ha'. }
        clear - Hc Hc0'. revert frs Hc. induction Hc0' as [g H0|g prev frs0 Hnz Hp Hc0' IH]; intros frs Hc.
        - inversion Hc; subst; [reflexivity|contradiction].
        - inversion Hc as [|? prev' frs' Hnz' Hp' Hc']; subst; [contradiction|].
          destruct Hp as (a & Ha & Hr). destruct Hp' as (a' & Ha' & Hr').
          assert (a' = a). { unfold ptr_off in Ha, Ha'. rewrite Ha in Ha'. injection Ha'. auto. }
          subst a'. assert (prev' = prev) by (eapply reads_ptr_det; eauto). subst prev'.
          f_equal. apply IH. exact Hc'. }
      subst frs0.
      split.
      + exists (f :: frs). split.
        { destruct Hff as (Hnz & _ & _ & Hp). apply (chain_cons st2 f fp frs); auto. }
        split.
        * intros g [<-|Hg] a Ha'; [apply (Hfb a Ha')|apply (Hfr g Hg a Ha')].
        * intros g [<-|Hg] a Ha'; [apply (Hfb a Ha')|].
          intros (r & Hr & Hra). apply in_app_iff in Hr. destruct Hr as [Hr|Hr].
          -- (* old frame vs new slot: the slot was unallocated in [st] *)
             destruct (Hsb a) as (_ & Hun); [exists r; auto|].
             destruct (Hfr0 g Hg a Ha') as (Hal' & _). exact (Hal' Hun).
          -- apply (Hfs g Hg a Ha'). exists r. auto.
      + intros a (r & Hr & Hra). apply in_app_iff in Hr. destruct Hr as [Hr|Hr].
        * apply Hsb. exists r. auto.
        * apply Hsl'. exists r. auto.
    - (* roots_ok *)
      apply (roots_ok_app st2 rs1 zs1 vs1 rs vs); [exact Hrd| |exact Hroots'].
      eapply Forall2_impl; [|exact Hst]. intros v z Hz. eapply stable_repr_mono; eauto.
      destruct Hm as (E & _). exact E.
  Qed.

  (* ------------------------------------------------------------------ *)
  (** ** Running the tail of a block *)

  (** Continuing after a block's terminator in the open CFG [B]. *)
  Definition continue (va : option ptr) (B : list (LLVMAst.block dtyp)) (l : block_id)
             (r : block_id + dvalue) : CFGtop ((block_id * block_id) + dvalue) :=
    match r with
    | inl l' => denote_ocfg B va (l, l')
    | inr v => Ret (inr v)
    end.

  (** The code and terminator of block [b], continued in [B]. *)
  Definition tail_of (va : option ptr) (B : list (LLVMAst.block dtyp)) (b : LLVMAst.block dtyp)
    : CFGtop ((block_id * block_id) + dvalue) :=
    ITree.bind (denote_code (blk_code b) va ;; denote_terminator (blk_term b))
               (continue va B (blk_id b)).

  (** Jumping to a phi-free block [b'] of [B] runs its code and terminator
      and continues in [B]. *)
  Lemma denote_ocfg_jump va B from l b' :
    RM.find l (ocfg_map B) = Some b' ->
    blk_phis b' = [] ->
    denote_ocfg B va (from, l) ≈ tail_of va B b'.
  Proof.
    intros Hf Hp.
    assert (Hid : l = blk_id b').
    { rewrite ScopeTheory.ocfg_map_find_block in Hf.
      eapply ScopeTheory.find_block_has_id; exact Hf. }
    subst l. unfold denote_ocfg. rewrite (LLVM_instr_lemmas.denote_ocfg_map_unfold va _ _ _ _ Hf).
    unfold tail_of, denote_block. rewrite Hp. unfold denote_phis. cbn [map_monad bind ret Monad_itree].
    repeat (rewrite Eqit.bind_ret_l || rewrite Eqit.bind_bind || (progress cbn [map_monad bind ret Monad_itree])).
    unfold continue, denote_ocfg. reflexivity.
  Qed.

  (** The flattening of a converted block, as emitted: [flatten_prog] is
      [flat_blockP] on every block ([Flatten_sem.flat_block_eq]), and it
      commutes with the type conversion ([Flatten_sem.conv_def_flat_def]). *)
  Definition flatB (b : LLVMAst.block dtyp) (c : positive) : LLVMAst.block dtyp :=
    fst (Flatten_sem.flat_blockP b c).

  Lemma flatB_id b c : blk_id (flatB b c) = blk_id b.
  Proof. apply Flatten_sem.flat_blockP_id. Qed.

  Lemma flatB_phis b c : blk_phis (flatB b c) = blk_phis b.
  Proof. apply Flatten_sem.flat_blockP_phis. Qed.

  (** Every block of the translation except its entry is in [B], flattened. *)
  Definition blocks_in (B : list (LLVMAst.block dtyp)) (blks : list (LLVMAst.block typ)) : Prop :=
    forall b, In b (tl blks) ->
      exists c, RM.find (blk_id b) (ocfg_map B) = Some (flatB (cblock b) c).

  Definition hd_blk (blks : list (LLVMAst.block typ)) : LLVMAst.block typ :=
    match blks with b :: _ => b | [] => mk_block (Name "entry") [] [] (IVoid 0%Z, TERM_Unreachable, []) None end.

  (** The result of running the compiled code of an expression evaluating to
      [v]: out of memory, or a return of a word stably representing [v], with
      the invariant re-established, the same local stack and globals, the
      memory frames only extended (by this activation's [alloca]s, at
      addresses that were not allocated stack memory before: the collector
      may free heap blocks, which may then be reused by an [alloca]), and the
      caller's stack kept ([keeps_stack]). *)
  Definition sim_result (st : state) (stk : stack) (fp : ptr) (rs : list ptr)
             (vs : list term.val) (v : term.val)
             (t : MCFGbot (Res ((block_id * block_id) + dvalue))) : Prop :=
    ends_in_oom t \/
    exists st' sf' z,
      returns t ((st', ((sf', stk), G)), inr (I64 z)) /\
      stable_repr st' v z /\
      INV st' fp rs vs /\
      (exists ks, frames_of st' = push_top ks (frames_of st) /\
                  Forall (fun k => ~ alloc_nonheap st (ptr_to_int k)) ks) /\
      keeps_stack st st' rs.

  (* ------------------------------------------------------------------ *)
  (** ** The call knot *)

  Definition fun_def (f : var) (xs : list var) (e : term.exp) : definition dtyp (CFG.cfg dtyp) :=
    conv_def (flat_def (mk_fun go ga prim_of fs (Anon (Zpos f)) xs e)).

  (** Calling the address of a top-level function runs its body; calling the
      address of [garbage_collect] runs the collector.

      This is stated as Vellvm's knot ([Denotation.denote_mcfg]) resolves
      calls: [lookup_defn (DVALUE_Pointer p)] looks up [ptr_to_int p] in an
      [IntMap] keyed by the integer addresses of the globals
      ([TopLevel.address_one_function]); the provenance of [p] and the call's
      return type are ignored.  Indirect calls go through [inttoptr], which
      yields a pointer with the same address and a wildcard provenance, so the
      knot is specified for every pointer with the function's address.  (To
      discharge these for the real knot one needs the addresses of the
      program's functions and of the library functions to be distinct.) *)
  Hypothesis ctx_fun : forall f ft xs e fp,
    fun_in_fundefs fds (f, ft, xs, e) ->
    RM.find (Anon (Zpos f)) G = Some (Ptr fp) ->
    forall dt p args, ptr_to_int p = ptr_to_int fp ->
      ctx _ (Call dt (Ptr p) args) ≈ denote_function (fun_def f xs e) args.
  Hypothesis ctx_gc : forall gp,
    RM.find (Name "garbage_collect") G = Some (Ptr gp) ->
    forall dt p args, ptr_to_int p = ptr_to_int gp ->
      ctx _ (Call dt (Ptr p) args) ≈ lift_top (gc args).
  Hypothesis G_funs : forall f, In f fs -> exists fp, RM.find (Anon (Zpos f)) G = Some (Ptr fp).
  Hypothesis G_gc : exists gp, RM.find (Name "garbage_collect") G = Some (Ptr gp).

  (** [Repr_fun]'s [rid_lookup] is the [RM.find] used by [ctx_fun]. *)
  Lemma rid_lookup_find (k : raw_id) (fp : ptr) :
    RawIdMaps.rid_lookup k G = Some (DVALUE_Base (DVALUE_Pointer fp)) ->
    RM.find k G = Some (Ptr fp).
  Proof. intros H. exact H. Qed.

  (** A word representing a function value [Vfun rho fds f] is the address of
      [f]'s global; calling any pointer with that address runs [f]'s body. *)
  Lemma repr_fun_call st rho f z ft xs e :
    repr_val cenv fds G st (Vfun rho fds f) z ->
    fun_in_fundefs fds (f, ft, xs, e) ->
    exists fp, RM.find (Anon (Zpos f)) G = Some (Ptr fp) /\ z = ptr_to_int fp /\
      (forall dt p args, ptr_to_int p = z ->
        ctx _ (Call dt (Ptr p) args) ≈ denote_function (fun_def f xs e) args).
  Proof.
    intros Hr Hin. inversion Hr; subst.
    match goal with H : RawIdMaps.rid_lookup _ _ = Some _ |- _ =>
      apply rid_lookup_find in H end.
    eexists. split; [eassumption|]. split; [reflexivity|].
    intros dt p args Hp. eapply ctx_fun; eassumption.
  Qed.

  (** The whole program, for the constructor-environment facts. *)
  Variable main : term.exp.
  Hypothesis Hprog : llvm_restricted cenv fds main.

  (** [body_ok] is closed under subterms, so every proper subterm of the
      program is [body_ok]. *)
  Lemma body_ok_dsubterm e e' : body_ok cenv e -> dsubterm_e e' e -> body_ok cenv e'.
  Proof.
    intros Hb Hd. inversion Hd; subst; inversion Hb; subst; try assumption.
    match goal with HF : Forall _ _, Hin : In _ _ |- _ =>
      rewrite Forall_forall in HF; exact (proj2 (HF _ Hin)) end.
  Qed.

  Lemma fundefs_ok_dsubterm B e' : fundefs_ok cenv B -> dsubterm_fds_e e' B -> body_ok cenv e'.
  Proof. intros HB Hd. revert HB. induction Hd; intros HB; inversion HB; subst; auto. Qed.

  Lemma prog_body_ok e : subterm_or_eq e (Efun fds main) -> e = Efun fds main \/ body_ok cenv e.
  Proof.
    pose proof Hprog as (Hfok & Hbok & _).
    intros H. apply Operators_Properties.clos_rt_rt1n_iff in H.
    remember (Efun fds main) as top eqn:Etop. revert Etop.
    induction H as [|e e2 e3 Hd Hrt IH]; intros Etop; [left; reflexivity|right].
    subst e3. destruct (IH eq_refl) as [->|Hb].
    - inversion Hd; subst.
      + eapply fundefs_ok_dsubterm; eassumption.
      + exact Hbok.
    - eapply body_ok_dsubterm; eassumption.
  Qed.

  Lemma prog_constr x t ys e :
    subterm_or_eq (Econstr x t ys e) (Efun fds main) ->
    tag_ok cenv t /\ arity_of cenv t = N.of_nat (length ys) /\
    8 * Z.of_N (chunk_words (Econstr x t ys e)) < 2 ^ 64.
  Proof.
    intros H. destruct (prog_body_ok _ H) as [E|Hb]; [discriminate|].
    inversion Hb; subst. auto.
  Qed.

  Lemma prog_case x bs t e :
    subterm_or_eq (Ecase x bs) (Efun fds main) -> In (t, e) bs -> tag_ok cenv t.
  Proof.
    intros H Hin. destruct (prog_body_ok _ H) as [E|Hb]; [discriminate|].
    inversion Hb as [| |? ? HF| | | |]; subst. rewrite Forall_forall in HF.
    exact (proj1 (HF _ Hin)).
  Qed.

  (* ------------------------------------------------------------------ *)
  (** ** The main simulation lemma *)

  (** The simulation statement for one expression: the body of [sim_exp]
      (see [LLVM_toplevel_link.sim_exp_statement]) without the evaluation
      premise.  The cases of [sim_exp] are stated as
      [sim_stmt rho' e' v -> sim_stmt rho e v] (the premise being the
      induction hypothesis for the continuation), so they can be proved in
      separate files. *)
  Definition sim_stmt (rho : eval.env) (e : term.exp) (v : term.val) : Prop :=
    forall env chunk fresh blks f' (B : list (LLVMAst.block dtyp)) va c st sf stk fp rs vs,
      body_ok cenv e ->
      subterm_or_eq e (Efun fds main) ->
      unique_bindings e ->
      Ensembles.Disjoint _ (bound_var e) (occurs_free e) ->
      env_ok (occurs_free e) env fresh ->
      tr env chunk e fresh = (blks, f') ->
      blocks_in B blks ->
      INV st fp rs vs ->
      tinfo_local sf ->
      env_rel (occurs_free e) rho env sf st ->
      room st tinfo (Z.of_N chunk) ->
      sim_result st stk fp rs vs v
        (interp_mcfg (interp_mrec ctx (tail_of va B (flatB (cblock (hd_blk blks)) c)))
                     (st, ((sf, stk), G))).

End Simulation.
