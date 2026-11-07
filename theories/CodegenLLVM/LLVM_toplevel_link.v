(** * From Vellvm's top-level semantics to the hypotheses of [LLVM_sim]

    This file connects [run_program] (the statement's semantics: runtime
    set-up, Vellvm's [build_global_environment], the [denote_mcfg] call knot,
    and [@certirocq_main]) with the section hypotheses of [LLVM_sim.v]:

    - the knot: [denote_mcfg] is [mrec (ctx_of IM)] ([denote_mcfg_knot]) and,
      for the compiled program, [ctx_of IM] discharges [ctx_fun] and [ctx_gc]
      ([ctx_real_fun], [ctx_real_gc]);
    - global initialisation: every declared/defined function gets a fresh
      8-byte stack block, at pairwise distinct addresses ([alloc_decls_spec]),
      which gives [G_funs], [G_gc] and the distinctness of the keys of the
      knot's [IntMap];
    - the entry point: [main_correct_of_sim] derives the statement
      [LambdaANF_to_LLVM_correct_statement] from [sim_exp_statement], the
      statement of the main simulation lemma (proved in [LLVM_sim_exp.v],
      which also states the top-level theorem [LambdaANF_to_LLVM_correct]). *)

From Stdlib Require Import ZArith NArith List Lia String Program Morphisms Permutation.
From ITree Require Import ITree Eq.Eqit Interp.InterpFacts Interp.RecursionFacts Events.State Events.StateFacts.
From ExtLib Require Import Structures.Monads.

From CertiRocq.LambdaANF Require Import term term_util eval identifiers.
From CertiRocq.Common Require Import AstCommon.
From CertiRocq.CodegenLLVM Require Import LambdaANF_to_LLVM Flatten
     LambdaANF_to_LLVM_statement LLVM_interp_lemmas LLVM_call_lemmas LLVM_convert
     LLVM_exp_lemmas LLVM_mem_lemmas LLVM_emit_syntax LLVM_instr_lemmas LLVM_sim.
From CertiRocq.CodegenLLVM Require Flatten_sem.

From Vellvm Require Import
  Utils Syntax Params
  Interfaces.Memory Implementations.Memory
  Semantics.DynamicValues Semantics.LLVMEvents Semantics.Denotation
  Semantics.InterpretationStack Semantics.TopLevel Semantics.Libraries Handlers.
From Vellvm Require Import Utils.IntMaps.

Import ListNotations.
Import MonadNotation.
Open Scope monad_scope.
Open Scope Z_scope.

Unset Implicit Arguments.
Set Bullet Behavior "Strict Subproofs".

(* ------------------------------------------------------------------ *)
(** ** Running top-level ([MCFGtop]) computations *)

Definition truns {X} (t : MCFGtop X) (s s' : FusedS) (r : X) : Prop :=
  interp_mcfg t s ≈ Ret (s', r).

Definition toom {X} (t : MCFGtop X) (s : FusedS) : Prop :=
  ends_in_oom (interp_mcfg t s).

Lemma truns_ret {X} (x : X) s : truns (Ret x) s s x.
Proof. apply interp_mcfg_ret. Qed.

Lemma truns_bind {X Y} (t : MCFGtop X) (k : X -> MCFGtop Y) s s1 x s2 y :
  truns t s s1 x -> truns (k x) s1 s2 y -> truns (ITree.bind t k) s s2 y.
Proof.
  unfold truns. intros H1 H2. rewrite interp_mcfg_bind, H1, Eqit.bind_ret_l. exact H2.
Qed.

Lemma toom_bind_l {X Y} (t : MCFGtop X) (k : X -> MCFGtop Y) s :
  toom t s -> toom (ITree.bind t k) s.
Proof. unfold toom. intros H. rewrite interp_mcfg_bind. apply ends_in_oom_bind, H. Qed.

Lemma toom_bind_r {X Y} (t : MCFGtop X) (k : X -> MCFGtop Y) s s1 x :
  truns t s s1 x -> toom (k x) s1 -> toom (ITree.bind t k) s.
Proof.
  unfold truns, toom. intros H1 H2. rewrite interp_mcfg_bind, H1, Eqit.bind_ret_l. exact H2.
Qed.

Lemma truns_eutt {X} (t t' : MCFGtop X) s s' r : t ≈ t' -> truns t s s' r -> truns t' s s' r.
Proof. unfold truns. intros H. rewrite H. auto. Qed.

Lemma truns_gread id v st ls g :
  RM.find id g = Some v -> truns (gread id) (st, (ls, g)) (st, (ls, g)) v.
Proof. intros H. unfold truns, gread. apply interp_mcfg_gread, H. Qed.

Lemma truns_gwrite id v st ls g :
  truns (gwrite id v) (st, (ls, g)) (st, (ls, Maps.add id v g)) tt.
Proof.
  unfold truns, gwrite, interp_mcfg.
  rewrite interp_intrinsics_trigger. cbn. unfold F_trigger.
  rewrite interp_state_trigger. cbn. unfold on_genv, handle_global_debug.
  cbn. repeat (rewrite Eqit.bind_ret_l; cbn). reflexivity.
Qed.

Lemma truns_alloca st rest st' p :
  memS_runs_c st (allocate_dtyp DTYPE_Pointer 1 8) st' p ->
  truns (alloca DTYPE_Pointer 1 None) (st, rest) (st', rest) (Ptr p).
Proof.
  intros H. unfold truns.
  etransitivity; [exact (interp_mcfg_memory_gen (Alloca DTYPE_Pointer 1 None) st rest)|].
  rewrite (memM_interp_runs_c st _ st' (Ptr p)); [rewrite Eqit.bind_ret_l; reflexivity|].
  cbn [handle_memoryM]. eapply memS_runs_c_bind; [exact H|constructor].
Qed.

Lemma toom_alloca st rest :
  memS_oom st (allocate_dtyp DTYPE_Pointer 1 8) ->
  toom (alloca DTYPE_Pointer 1 None) (st, rest).
Proof.
  intros H. unfold toom, ends_in_oom.
  setoid_rewrite (interp_mcfg_memory_gen (Alloca DTYPE_Pointer 1 None) st rest).
  destruct (memM_interp_oom st _ (memS_oom_bind_l _ _ (fun p => Mret (Ptr p)) H)) as [k Hk].
  eexists. cbn [handle_memoryM]. rewrite Hk, bind_vis. reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(** ** Memory growth

    [grow st st']: same heap blocks, allocated bytes unchanged, and the new
    memory-frame addresses were unallocated.  Global allocation (stack
    [alloca]s in the bottom frame) and [mem_push] are such steps. *)

Definition grow (st st' : state) : Prop :=
  heap_of st' = heap_of st /\
  (forall a, IntMaps.lookup a (mem_of st) <> None ->
             IntMaps.lookup a (mem_of st') = IntMaps.lookup a (mem_of st)) /\
  (forall a, in_frames st' a -> in_frames st a \/ IntMaps.lookup a (mem_of st) = None).

Lemma grow_refl st : grow st st.
Proof. split; [reflexivity|]. split; [reflexivity|]. intros a H. left. exact H. Qed.

Lemma grow_trans st1 st2 st3 : grow st1 st2 -> grow st2 st3 -> grow st1 st3.
Proof.
  intros (H1 & M1 & F1) (H2 & M2 & F2). split; [congruence|]. split.
  - intros a Ha. rewrite M2; [apply M1; exact Ha|]. rewrite M1 by exact Ha. exact Ha.
  - intros a Ha. destruct (F2 a Ha) as [Hf|Hn]; [apply F1; exact Hf|].
    right. destruct (IntMaps.lookup a (mem_of st1)) eqn:E; [|reflexivity].
    rewrite M1 in Hn by (rewrite E; discriminate). congruence.
Qed.

Lemma grow_allocated st st' a :
  grow st st' -> IntMaps.lookup a (mem_of st) <> None -> IntMaps.lookup a (mem_of st') <> None.
Proof. intros (_ & M & _) H. rewrite M by exact H. exact H. Qed.

Lemma frames_ptrs_push_top ks fs : frames_ptrs (push_top ks fs) = (rev ks ++ frames_ptrs fs)%list.
Proof. destruct fs; cbn; [reflexivity|]. rewrite app_assoc. reflexivity. Qed.

Lemma alloc_post_grow st st' sz p : alloc_post st st' sz p -> grow st st'.
Proof.
  intros Hp. pose proof Hp as (Hh & (ptrs & Hc & _ & Hf) & Hfree & _ & _).
  split; [exact Hh|]. split; [intros a Ha; eapply alloc_post_allocated; eauto|].
  intros a Ha. unfold in_frames in Ha. rewrite Hf, frames_ptrs_push_top, map_app, in_app_iff in Ha.
  destruct Ha as [Ha|Ha]; [right|left; exact Ha].
  apply in_map_iff in Ha as (q & <- & Hq). rewrite <- in_rev in Hq.
  destruct (In_consec _ _ _ Hc Hq) as (i & _ & Ei & _). apply Hfree. lia.
Qed.

Lemma push_post_grow st st' : push_post st st' -> grow st st'.
Proof.
  intros (Hh & Hf & Hm). split; [exact Hh|]. split; [intros a _; apply Hm|].
  intros a Ha. left. unfold in_frames in *. rewrite Hf in Ha. exact Ha.
Qed.

(** Reads and writability survive growth. *)
Lemma grow_read st st' t q v :
  grow st st' -> memS_returns st (read_dvalue t q) v -> memS_returns st' (read_dvalue t q) v.
Proof.
  intros Hg (st0 & H). pose proof H as H'.
  apply read_dvalue_runs in H. destruct H as (-> & ptrs & bs & Eg & HF & _).
  apply read_dvalue_frame in H'. destruct H' as [_ H']. exists st'. apply H'.
  apply gcp_spec in Eg. destruct Eg as [L C].
  intros a Ha. destruct Hg as (_ & M & _). apply M.
  destruct (consec_cover q ptrs a C) as (q' & Hin & <-); [rewrite L; lia|].
  destruct (Forall2_In_l _ _ _ _ HF Hin) as (b & _ & aid & Eb & _). congruence.
Qed.

Lemma grow_reads_ptr st st' p q : grow st st' -> reads_ptr st p q -> reads_ptr st' p q.
Proof. apply grow_read. Qed.

Lemma grow_reads_word st st' p z : grow st st' -> reads_word st p z -> reads_word st' p z.
Proof. apply grow_read. Qed.

Lemma grow_writable_word st st' p : grow st st' -> writable_word st p -> writable_word st' p.
Proof.
  intros (_ & M & _) W. eapply writable_word_aid; [exact W|].
  intros a Ha. unfold aid_at. rewrite M; [reflexivity|]. eapply writable_word_alloc; eauto.
Qed.

Lemma grow_in_heap st st' a : grow st st' -> (in_heap st' a <-> in_heap st a).
Proof. intros (E & _). unfold in_heap. rewrite E. reflexivity. Qed.

Lemma grow_field st st' tinfo off q : grow st st' -> field st tinfo off q -> field st' tinfo off q.
Proof. intros Hg (a & Ha & Hr). exists a. split; [exact Ha|]. eapply grow_reads_ptr; eauto. Qed.

(* ------------------------------------------------------------------ *)
(** ** Allocation of the function addresses *)

Lemma alloca_ptr_cases st :
  memS_oom st (allocate_dtyp DTYPE_Pointer 1 8) \/
  exists st' p, memS_runs_c st (allocate_dtyp DTYPE_Pointer 1 8) st' p /\
    grow st st' /\
    IntMaps.lookup (ptr_to_int p) (mem_of st) = None /\
    IntMaps.lookup (ptr_to_int p) (mem_of st') <> None.
Proof.
  destruct (allocate_dtyp_total st DTYPE_Pointer 1 8 eq_refl) as [H|(st' & p & H)]; [left; exact H|].
  right. exists st', p. split; [exact H|].
  apply allocate_dtyp_post in H. split; [eapply alloc_post_grow; eauto|].
  destruct H as (_ & _ & Hfree & _ & Hw). split; [apply Hfree; lia|].
  destruct (Hw p eq_refl) as (aid & Ha & _); [rewrite sizeof_ptr; lia|].
  unfold aid_at in Ha. intros E. rewrite E in Ha. discriminate.
Qed.

Lemma allocate_declaration_eq d :
  IntrinsicsDefinitions.lookup_intrinsic_declaration (dc_name d) = None ->
  allocate_declaration d = (v <- alloca DTYPE_Pointer 1 None;; gwrite (dc_name d) v).
Proof. intros H. unfold allocate_declaration. rewrite H. reflexivity. Qed.

Lemma alloc_decls_spec (ds : list (declaration dtyp)) : forall st ls g,
  Forall (fun d => IntrinsicsDefinitions.lookup_intrinsic_declaration (dc_name d) = None) ds ->
  NoDup (map dc_name ds) ->
  toom (allocate_declarations ds) (st, (ls, g)) \/
  exists st' g' ps,
    truns (allocate_declarations ds) (st, (ls, g)) (st', (ls, g')) tt /\
    grow st st' /\
    Forall2 (fun d p => RM.find (dc_name d) g' = Some (Ptr p)) ds ps /\
    (forall n, ~ In n (map dc_name ds) -> RM.find n g' = RM.find n g) /\
    NoDup (map ptr_to_int ps) /\
    Forall (fun p => IntMaps.lookup (ptr_to_int p) (mem_of st) = None /\
                     IntMaps.lookup (ptr_to_int p) (mem_of st') <> None) ps.
Proof.
  induction ds as [|d ds IH]; intros st ls g Hint Hnd.
  - right. exists st, g, []. split; [apply truns_ret|]. split; [apply grow_refl|].
    split; [constructor|]. split; [auto|]. split; constructor.
  - inversion Hint as [|? ? Hd Hint']; subst. inversion Hnd as [|? ? Hnin Hnd']; subst.
    unfold allocate_declarations. cbn [loop_monad]. rewrite (allocate_declaration_eq d Hd).
    destruct (alloca_ptr_cases st) as [Ho|(st1 & p & Hr & Hg1 & Hfree & Hall)].
    + left. apply toom_bind_l, toom_bind_l, toom_alloca, Ho.
    + assert (H1 : truns (v <- alloca DTYPE_Pointer 1 None;; gwrite (dc_name d) v) (st, (ls, g))
                         (st1, (ls, Maps.add (dc_name d) (Ptr p) g)) tt).
      { eapply truns_bind; [apply truns_alloca, Hr|]. apply truns_gwrite. }
      destruct (IH st1 ls (Maps.add (dc_name d) (Ptr p) g) Hint' Hnd') as
        [Ho|(st' & g' & ps & Hrun & Hg & HF & Hoth & Hnd2 & Hfr)].
      * left. eapply toom_bind_r; [exact H1|exact Ho].
      * right. exists st', g', (p :: ps). split; [eapply truns_bind; [exact H1|exact Hrun]|].
        split; [eapply grow_trans; eauto|]. split; [|split; [|split]].
        -- constructor; [|exact HF]. rewrite Hoth by exact Hnin. apply rfind_add_eq.
        -- intros n Hn. rewrite Hoth by (intros H; apply Hn; right; exact H).
           apply rfind_add_neq. intros E. apply Hn. left. exact E.
        -- cbn [map]. constructor; [|exact Hnd2]. intros Hin. apply in_map_iff in Hin as (q & Eq & Hq).
           rewrite Forall_forall in Hfr. destruct (Hfr q Hq) as [Hq1 _]. rewrite Eq in Hq1. contradiction.
        -- constructor.
           ++ split; [exact Hfree|]. eapply grow_allocated; eauto.
           ++ eapply Forall_impl; [|exact Hfr]. intros q [Hq1 Hq2]. split; [|exact Hq2].
              destruct (IntMaps.lookup (ptr_to_int q) (mem_of st)) eqn:E; [|reflexivity].
              exfalso. apply (grow_allocated st st1 (ptr_to_int q) Hg1); [rewrite E; discriminate|exact Hq1].
Qed.

(* ------------------------------------------------------------------ *)
(** ** The call knot of [denote_mcfg] *)

(** The body of Vellvm's [denote_mcfg] knot, for the function table [IM]. *)
Definition ctx_of (IM : IntMap function_denotation) : CallE ~> itree (CallE +' MCFGEtop) :=
  fun T call =>
    match call with
    | Call dt fv args =>
        match lookup_defn fv IM with
        | Some f_den => f_den args
        | None => inr <$> external_call dt fv args
        end
    end.

Lemma denote_mcfg_knot IM dt f args :
  denote_mcfg IM dt f args = mrec (ctx_of IM) (Call dt f args).
Proof. reflexivity. Qed.

(** [mrec] unfolds to the knot applied to the entry call. *)
Lemma denote_mcfg_unfold IM dt f args :
  denote_mcfg IM dt f args = interp_mrec (ctx_of IM) (ctx_of IM _ (Call dt f args)).
Proof. reflexivity. Qed.

Lemma ctx_of_lookup IM dt p args den :
  IntMaps.lookup (ptr_to_int p) IM = Some den ->
  ctx_of IM _ (Call dt (Ptr p) args) = den args.
Proof. intros H. unfold ctx_of, lookup_defn, Ptr. rewrite H. reflexivity. Qed.

Lemma NoDup_NoDupA_eqk {A} (l : list (Z * A)) :
  NoDup (map fst l) -> SetoidList.NoDupA (@IM.eq_key A) l.
Proof.
  induction l as [|[k v] l IH]; intros Hn; constructor.
  - inversion Hn as [|? ? Hnin _]; subst. intros Hin.
    apply SetoidList.InA_alt in Hin as ([k' v'] & Ek & Hin).
    apply Hnin. unfold IM.eq_key, IM.Raw.Proofs.PX.eqk in Ek. cbn in Ek. subst k'.
    apply (in_map fst) in Hin. exact Hin.
  - inversion Hn; subst. apply IH. assumption.
Qed.

(** Lookup in the knot's function table built by [IP.of_list]. *)
Lemma of_list_lookup {A} (l : list (Z * A)) k v :
  NoDup (map fst l) -> In (k, v) l -> IntMaps.lookup k (IP.of_list l) = Some v.
Proof.
  intros Hn Hin. unfold IntMaps.lookup. apply IM.find_1. apply IP.of_list_1.
  - apply NoDup_NoDupA_eqk, Hn.
  - apply SetoidList.In_InA; [|exact Hin]. typeclasses eauto.
Qed.

(** The address a global name is bound to in [G] (0 if none). *)
Definition addr_of (G : global_env) (n : raw_id) : Z :=
  match RM.find n G with
  | Some (DVALUE_Base (DVALUE_Pointer p)) => ptr_to_int p
  | _ => 0
  end.

Lemma addr_of_ptr G n p : RM.find n G = Some (Ptr p) -> addr_of G n = ptr_to_int p.
Proof. unfold addr_of. intros ->. reflexivity. Qed.

Lemma address_defs_run (ds : list (definition dtyp (cfg dtyp))) st ls G :
  Forall (fun d => exists p, RM.find (dc_name (df_prototype d)) G = Some (Ptr p)) ds ->
  truns (map_monad address_one_function ds) (st, (ls, G)) (st, (ls, G))
        (map (fun d => (addr_of G (dc_name (df_prototype d)), denote_function d)) ds).
Proof.
  induction ds as [|d ds IH]; intros HF.
  - apply truns_ret.
  - inversion HF as [|? ? (p & Hp) HF']; subst. cbn [map_monad map].
    eapply truns_bind.
    { unfold address_one_function. eapply truns_bind; [apply truns_gread, Hp|].
      cbn. apply truns_ret. }
    eapply truns_bind; [apply IH, HF'|]. rewrite (addr_of_ptr _ _ _ Hp). apply truns_ret.
Qed.

Lemma address_libs_run (ls_ : list (function_id * function_denotation)) st ls G :
  Forall (fun nd => exists p, RM.find (fst nd) G = Some (Ptr p)) ls_ ->
  truns (map_monad address_one_library_function ls_) (st, (ls, G)) (st, (ls, G))
        (map (fun nd => (addr_of G (fst nd), snd nd)) ls_).
Proof.
  induction ls_ as [|[n den] l IH]; intros HF.
  - apply truns_ret.
  - inversion HF as [|? ? (p & Hp) HF']; subst. cbn [map_monad map fst snd] in *.
    eapply truns_bind.
    { unfold address_one_library_function. eapply truns_bind; [apply truns_gread, Hp|].
      cbn. apply truns_ret. }
    eapply truns_bind; [apply IH, HF'|]. rewrite (addr_of_ptr _ _ _ Hp). apply truns_ret.
Qed.

Lemma library_functions_gc :
  library_functions [cdecl gc_decl] = [].
Proof. rewrite cdecl_gc_decl. reflexivity. Qed.

Lemma not_intrinsic_anon z :
  IntrinsicsDefinitions.lookup_intrinsic_declaration (Anon z) = None.
Proof. reflexivity. Qed.

Lemma not_intrinsic_gc :
  IntrinsicsDefinitions.lookup_intrinsic_declaration (Name "garbage_collect") = None.
Proof. vm_compute. reflexivity. Qed.

Lemma not_intrinsic_main :
  IntrinsicsDefinitions.lookup_intrinsic_declaration (Name "certirocq_main") = None.
Proof. vm_compute. reflexivity. Qed.

(* ------------------------------------------------------------------ *)
(** ** Generic facts about the emitted program *)

Lemma cdecl_name (d : declaration typ) : dc_name (cdecl d) = dc_name d.
Proof. destruct d; reflexivity. Qed.

Lemma conv_flat_name (d : Ldef) :
  dc_name (df_prototype (conv_def (flat_def d))) = dc_name (df_prototype d).
Proof. cbn [conv_def df_prototype]. rewrite cdecl_name, flat_def_proto. reflexivity. Qed.

Lemma funs_to_defs_names' go ga po fs fds :
  map (fun d => dc_name (df_prototype d)) (funs_to_defs go ga po fs fds) =
  map (fun f => Anon (Zpos f)) (fun_ids fds).
Proof.
  induction fds as [f ft xs e rest IH|]; [|reflexivity].
  cbn [funs_to_defs fun_ids map]. rewrite IH, mk_fun_name. reflexivity.
Qed.

Lemma funs_to_defs_of_fun_in go ga po fs fds f ft xs e :
  fun_in_fundefs fds (f, ft, xs, e) ->
  In (mk_fun go ga po fs (Anon (Zpos f)) xs e) (funs_to_defs go ga po fs fds).
Proof.
  induction fds as [g gt ys e' rest IH|]; cbn; [|intros H; inversion H].
  intros H. inversion H as [? Hs|? Hs]; subst.
  - inversion Hs; subst. left. reflexivity.
  - right. apply IH, Hs.
Qed.

Lemma name_in_fun_ids fds x : name_in_fundefs fds x -> In x (fun_ids fds).
Proof.
  induction fds as [g gt ys e' rest IH|]; cbn; [|intros H; inversion H].
  intros H. inversion H as [? H1|? H1]; subst.
  - inversion H1. left. reflexivity.
  - right. apply IH, H1.
Qed.

Lemma is_fun_true fs x : In x fs -> is_fun fs x = true.
Proof. intros H. unfold is_fun. apply existsb_exists. exists x. split; [exact H|apply Pos.eqb_refl]. Qed.

Lemma unique_fun_ids fds : unique_bindings_fundefs fds -> NoDup (fun_ids fds).
Proof.
  induction fds as [f ft xs e rest IH|]; cbn; intros H; [|constructor].
  inversion H; subst. constructor; [|apply IH; assumption].
  intros Hin. match goal with Hn : ~ bound_var_fundefs rest f |- _ => apply Hn end.
  clear -Hin. induction rest as [g gt ys e' rest IH|]; cbn in Hin; [|contradiction].
  destruct Hin as [<-|Hin]; [constructor; left; reflexivity|].
  apply Bound_Fcons2. apply IH, Hin.
Qed.

Lemma cblock_id (b : LLVMAst.block typ) : blk_id (cblock b) = blk_id b.
Proof. rewrite cblock_eq. reflexivity. Qed.

Lemma flat_blocksP_in (bs : list (LLVMAst.block typ)) : forall c b,
  In b bs ->
  exists c', In (fst (Flatten_sem.flat_blockP (cblock b) c'))
                (fst (Flatten_sem.flat_blocksP (map cblock bs) c)).
Proof.
  induction bs as [|b0 bs IH]; intros c b Hin; [destruct Hin|].
  cbn [map Flatten_sem.flat_blocksP].
  destruct (Flatten_sem.flat_blockP (cblock b0) c) as [b0' n1] eqn:E0.
  destruct (Flatten_sem.flat_blocksP (map cblock bs) n1) as [rs n2] eqn:E1. cbn [fst].
  destruct Hin as [<-|Hin].
  - exists c. rewrite E0. left. reflexivity.
  - destruct (IH n1 b Hin) as (c' & Hc). rewrite E1 in Hc. exists c'. right. exact Hc.
Qed.

(* ------------------------------------------------------------------ *)
(** ** The compiled program and its global environment *)

Section Program.
  Variable cenv : ctor_env.
  Variable prim_of : positive -> option (string * bool).
  Variable fds : fundefs.
  Variable main : term.exp.
  Hypothesis Hnodup : NoDup (fun_ids fds).

  Let go := ord_of cenv.
  Let ga := arity_of cenv.
  Let fs := fun_ids fds.

  Definition main_ldef : Ldef := mk_fun go ga prim_of fs (Name "certirocq_main") [] main.
  Definition pdefs : list Ldef := (funs_to_defs go ga prim_of fs fds ++ [main_ldef])%list.
  Definition cdefs : list (definition dtyp (cfg dtyp)) := map (fun d => conv_def (flat_def d)) pdefs.
  Definition main_cdef := conv_def (flat_def main_ldef).

  Definition the_mcfg : CFG.mcfg dtyp :=
    {| m_name := None; m_target := None; m_datalayout := None;
       m_type_defs := []; m_globals := [];
       m_declarations := [cdecl gc_decl];
       m_definitions := cdefs |}.

  Lemma the_mcfg_eq :
    convert_types (CFG.mcfg_of_tle (link runtime_prelude (emitted cenv prim_of (Efun fds main))))
    = the_mcfg.
  Proof. rewrite convert_emitted. reflexivity. Qed.

  Definition decl_names : list raw_id :=
    Name "garbage_collect" :: map (fun d => dc_name (df_prototype d)) cdefs.

  Lemma decl_names_eq :
    decl_names = (Name "garbage_collect" :: map (fun f => Anon (Zpos f)) fs ++ [Name "certirocq_main"])%list.
  Proof.
    unfold decl_names, cdefs, pdefs. rewrite map_map.
    rewrite (map_ext _ (fun d => dc_name (df_prototype d)) conv_flat_name).
    rewrite map_app, funs_to_defs_names'. cbn. unfold main_ldef. rewrite mk_fun_name. reflexivity.
  Qed.

  Lemma decl_names_nodup : NoDup decl_names.
  Proof.
    rewrite decl_names_eq. constructor.
    - rewrite in_app_iff. intros [H|[H|[]]]; [|discriminate].
      apply in_map_iff in H as (f & E & _). discriminate.
    - apply NoDup_app_intro.
      + clear -Hnodup. induction Hnodup as [|f l Hf Hl IH]; cbn; constructor; auto.
        intros Hin. apply in_map_iff in Hin as (g & E & Hg). injection E as ->. auto.
      + repeat constructor. intros [].
      + intros a H1 [<-|[]]. apply in_map_iff in H1 as (g & E & _). discriminate.
  Qed.

  Lemma decl_names_not_intrinsic :
    Forall (fun n => IntrinsicsDefinitions.lookup_intrinsic_declaration n = None) decl_names.
  Proof.
    rewrite decl_names_eq. constructor; [apply not_intrinsic_gc|].
    apply Forall_app. split.
    - apply Forall_forall. intros n Hn. apply in_map_iff in Hn as (f & <- & _). apply not_intrinsic_anon.
    - constructor; [apply not_intrinsic_main|constructor].
  Qed.

  Lemma the_decls_names :
    map dc_name (m_declarations the_mcfg ++ map df_prototype (m_definitions the_mcfg)) = decl_names.
  Proof.
    cbn [m_declarations m_definitions the_mcfg]. rewrite map_app, map_map. cbn [map].
    rewrite cdecl_name. reflexivity.
  Qed.

  (** What global initialisation establishes: every declared name has a
      pointer, and these pointers have pairwise distinct addresses. *)
  Definition G_ok (G : global_env) : Prop :=
    (forall n, In n decl_names -> exists p, RM.find n G = Some (Ptr p)) /\
    NoDup (map (addr_of G) decl_names).

  Lemma Forall2_addr_of (ds : list (declaration dtyp)) ps G :
    Forall2 (fun d p => RM.find (dc_name d) G = Some (Ptr p)) ds ps ->
    map (addr_of G) (map dc_name ds) = map ptr_to_int ps.
  Proof.
    induction 1 as [|d p ds ps H _ IH]; [reflexivity|].
    cbn [map]. rewrite IH, (addr_of_ptr _ _ _ H). reflexivity.
  Qed.

  Theorem global_init st ls :
    toom (build_global_environment the_mcfg) (st, (ls, Maps.empty)) \/
    exists st' G,
      truns (build_global_environment the_mcfg) (st, (ls, Maps.empty)) (st', (ls, G)) tt /\
      grow st st' /\ G_ok G.
  Proof.
    set (ds := (m_declarations the_mcfg ++ map df_prototype (m_definitions the_mcfg))%list).
    assert (Hn : map dc_name ds = decl_names) by apply the_decls_names.
    assert (Hint : Forall (fun d => IntrinsicsDefinitions.lookup_intrinsic_declaration (dc_name d) = None) ds).
    { apply Forall_forall. intros d Hd. pose proof decl_names_not_intrinsic as H.
      rewrite <- Hn, Forall_map, Forall_forall in H. apply H, Hd. }
    assert (Hnd : NoDup (map dc_name ds)) by (rewrite Hn; apply decl_names_nodup).
    destruct (alloc_decls_spec ds st ls Maps.empty Hint Hnd) as
      [Ho|(st' & G & ps & Hrun & Hg & HF & _ & Hnd2 & _)].
    - left. unfold build_global_environment. apply toom_bind_l, Ho.
    - right. exists st', G. split; [|split; [exact Hg|split]].
      + unfold build_global_environment. eapply truns_bind; [exact Hrun|].
        cbn [m_globals the_mcfg allocate_globals initialize_globals loop_monad].
        eapply truns_bind; apply truns_ret.
      + intros n Hin. rewrite <- Hn in Hin. apply in_map_iff in Hin as (d & <- & Hd).
        destruct (Forall2_In_l _ _ _ _ HF Hd) as (p & _ & Hp). exists p. exact Hp.
      + rewrite <- Hn, (Forall2_addr_of _ _ _ HF). exact Hnd2.
  Qed.

  (** The function table of the knot. *)
  Variable gc_den : function_denotation.

  Definition fun_table_list (G : global_env) : list (Z * function_denotation) :=
    (map (fun d => (addr_of G (dc_name (df_prototype d)), denote_function d)) cdefs
     ++ [(addr_of G (Name "garbage_collect"), gc_den)])%list.

  Definition fun_table (G : global_env) : IntMap function_denotation :=
    IP.of_list (fun_table_list G).

  Lemma fun_table_keys G : G_ok G -> NoDup (map fst (fun_table_list G)).
  Proof.
    intros (_ & Hnd). unfold fun_table_list. rewrite map_app, map_map. cbn [map fst].
    eapply Permutation_NoDup; [|exact Hnd]. unfold decl_names. cbn [map].
    rewrite map_map. apply Permutation_cons_append.
  Qed.

  Lemma fun_table_lookup G n den p :
    G_ok G -> In (addr_of G n, den) (fun_table_list G) -> RM.find n G = Some (Ptr p) ->
    IntMaps.lookup (ptr_to_int p) (fun_table G) = Some den.
  Proof.
    intros Hok Hin Hf. rewrite <- (addr_of_ptr _ _ _ Hf). apply of_list_lookup; [|exact Hin].
    apply fun_table_keys, Hok.
  Qed.

  Lemma G_ok_fun G f : G_ok G -> In f fs -> exists fp, RM.find (Anon (Zpos f)) G = Some (Ptr fp).
  Proof.
    intros (H & _) Hf. apply H. rewrite decl_names_eq. right. apply in_app_iff. left.
    apply (in_map (fun f => Anon (Zpos f))), Hf.
  Qed.

  Lemma G_ok_gc G : G_ok G -> exists gp, RM.find (Name "garbage_collect") G = Some (Ptr gp).
  Proof. intros (H & _). apply H. left. reflexivity. Qed.

  Lemma G_ok_main G : G_ok G -> exists pm, RM.find (Name "certirocq_main") G = Some (Ptr pm).
  Proof.
    intros (H & _). apply H. rewrite decl_names_eq. right. apply in_app_iff. right. left. reflexivity.
  Qed.

  (** *** [ctx_fun], [ctx_gc] for the real knot *)

  Theorem ctx_real_fun G f ft xs e fp :
    G_ok G ->
    fun_in_fundefs fds (f, ft, xs, e) ->
    RM.find (Anon (Zpos f)) G = Some (Ptr fp) ->
    forall dt p args, ptr_to_int p = ptr_to_int fp ->
      ctx_of (fun_table G) _ (Call dt (Ptr p) args) ≈ denote_function (fun_def cenv prim_of fds f xs e) args.
  Proof.
    intros Hok Hin Hf dt p args Ep.
    rewrite (ctx_of_lookup _ dt p args (denote_function (fun_def cenv prim_of fds f xs e))); [reflexivity|].
    rewrite Ep. eapply fun_table_lookup; [exact Hok| |exact Hf].
    unfold fun_table_list. apply in_app_iff. left.
    apply in_map_iff. exists (fun_def cenv prim_of fds f xs e). split.
    - unfold fun_def. rewrite conv_flat_name, mk_fun_name. reflexivity.
    - unfold cdefs, pdefs. apply in_map_iff. exists (mk_fun go ga prim_of fs (Anon (Zpos f)) xs e).
      split; [reflexivity|]. apply in_app_iff. left. eapply funs_to_defs_of_fun_in; eauto.
  Qed.

  Theorem ctx_real_gc G gp :
    G_ok G ->
    RM.find (Name "garbage_collect") G = Some (Ptr gp) ->
    forall dt p args, ptr_to_int p = ptr_to_int gp ->
      ctx_of (fun_table G) _ (Call dt (Ptr p) args) ≈ gc_den args.
  Proof.
    intros Hok Hf dt p args Ep.
    rewrite (ctx_of_lookup _ dt p args gc_den); [reflexivity|].
    rewrite Ep. eapply fun_table_lookup; [exact Hok| |exact Hf].
    unfold fun_table_list. apply in_app_iff. right. left. reflexivity.
  Qed.

  Lemma ctx_real_main G pm args :
    G_ok G ->
    RM.find (Name "certirocq_main") G = Some (Ptr pm) ->
    ctx_of (fun_table G) _ (Call (DTYPE_I 64) (Ptr pm) args) = denote_function main_cdef args.
  Proof.
    intros Hok Hf. apply ctx_of_lookup. eapply fun_table_lookup; [exact Hok| |exact Hf].
    unfold fun_table_list. apply in_app_iff. left.
    apply in_map_iff. exists main_cdef. split.
    - unfold main_cdef. rewrite conv_flat_name. unfold main_ldef. rewrite mk_fun_name. reflexivity.
    - unfold cdefs, pdefs. apply in_map_iff. exists main_ldef. split; [reflexivity|].
      apply in_app_iff. right. left. reflexivity.
  Qed.

  (** Everything between the runtime set-up and the entry call. *)
  Lemma addresses_run st ls G :
    G_ok G ->
    truns (map_monad address_one_function (m_definitions the_mcfg)) (st, (ls, G)) (st, (ls, G))
          (map (fun d => (addr_of G (dc_name (df_prototype d)), denote_function d)) cdefs).
  Proof.
    intros (H & _). apply address_defs_run. apply Forall_forall. intros d Hd. apply H.
    right. apply (in_map (fun d => dc_name (df_prototype d))), Hd.
  Qed.

  Lemma libraries_run st ls G :
    G_ok G ->
    truns (map_monad address_one_library_function
             ([(Name "garbage_collect", gc_den)] ++ library_functions (m_declarations the_mcfg)))
          (st, (ls, G)) (st, (ls, G)) [(addr_of G (Name "garbage_collect"), gc_den)].
  Proof.
    intros Hok. cbn [m_declarations the_mcfg]. rewrite library_functions_gc. cbn [app].
    apply (address_libs_run [(Name "garbage_collect", gc_den)]). constructor; [|constructor].
    apply G_ok_gc, Hok.
  Qed.

End Program.

(* ------------------------------------------------------------------ *)
(** ** The invariant at the entry of [@certirocq_main]

    Right after the runtime set-up the shadow stack is empty ([fp] is null),
    so [INV] reduces to its runtime part [INV0].  [INV0] survives memory
    growth (global allocation and the entry's [mem_push]). *)

Section Entry_INV.
  Variable cenv : ctor_env.
  Variable fds : fundefs.
  Variable heap_inv : state -> ptr -> Prop.
  Variable G : global_env.
  Variable tinfo fp : ptr.
  Hypothesis Hfp0 : ptr_to_int fp = 0.

  Hypothesis Hmut : forall st st2 alloc alloc2 limit,
       heap_inv st tinfo -> tinfo_ok st tinfo ->
       heap_agree_except st st2 (mutator_writes st tinfo) ->
       field st tinfo off_alloc alloc -> field st tinfo off_limit limit ->
       field st2 tinfo off_alloc alloc2 ->
       (ptr_to_int alloc <= ptr_to_int alloc2 <= ptr_to_int limit)%Z ->
       (ptr_to_int alloc2 mod 8 = 0)%Z ->
       heap_inv st2 tinfo.

  Definition INV0 (st : state) : Prop :=
    heap_inv st tinfo /\ tinfo_ok st tinfo /\ mem_ok st /\ nursery_tinfo_disjoint st tinfo /\
    field st tinfo off_fp fp.

  Lemma INV0_grow st st' : grow st st' -> INV0 st -> INV0 st'.
  Proof.
    intros Hg (Hhi & Hok & (Hm1 & Hm2) & Hdis & Hfp).
    pose proof Hok as (Hf & _ & alloc & limit & Ha & Hl & Hal & Hle & Hin & Hwr & Hlal).
    pose proof Hg as (Eh & M & F).
    assert (Ha' : field st' tinfo off_alloc alloc) by (eapply grow_field; eauto).
    assert (Hl' : field st' tinfo off_limit limit) by (eapply grow_field; eauto).
    assert (Hnur : forall a, nursery st' tinfo a -> nursery st tinfo a).
    { intros a (al & li & Hal' & Hli' & Hr).
      rewrite (field_det tinfo _ _ _ _ Hal' Ha'), (field_det tinfo _ _ _ _ Hli' Hl') in Hr.
      exists alloc, limit. auto. }
    split; [|split; [|split; [|split]]].
    - eapply (Hmut st st' alloc alloc limit); eauto; [|lia].
      split; [exact Eh|]. intros a Hia _. apply M, Hm1, Hia.
    - split; [|split].
      + intros off a Hoff Hoa. destruct (Hf off a Hoff Hoa) as (Hw & Hin').
        split; [eapply grow_writable_word; eauto|].
        intros b Hb. rewrite (grow_in_heap _ _ _ Hg). apply Hin', Hb.
      + exists fp, []. split; [eapply grow_field; eauto|]. apply SS_nil, Hfp0.
      + exists alloc, limit. split; [exact Ha'|]. split; [exact Hl'|]. split; [exact Hal|].
        split; [exact Hle|]. split; [|split].
        * intros a Hr. rewrite (grow_in_heap _ _ _ Hg). apply Hin, Hr.
        * intros i q Hi Hq. eapply grow_writable_word; eauto.
        * exact Hlal.
    - split.
      + intros a Hia. rewrite (grow_in_heap _ _ _ Hg) in Hia. eapply grow_allocated; eauto.
      + intros a Hfr. rewrite (grow_in_heap _ _ _ Hg). destruct (F a Hfr) as [Hf'|Hn].
        * apply Hm2, Hf'.
        * intros Hia. apply (Hm1 a Hia), Hn.
    - intros a Hn. apply Hdis, Hnur, Hn.
    - eapply grow_field; eauto.
  Qed.

  Lemma INV0_INV st : INV0 st -> INV cenv fds heap_inv G tinfo st fp [] [].
  Proof.
    intros (Hhi & Hok & Hm & Hdis & Hfp).
    split; [exact Hhi|]. split; [exact Hok|]. split; [exact Hm|]. split; [exact Hdis|].
    split; [exact Hfp|]. split; [apply SS_nil, Hfp0|]. split.
    - split.
      + exists []. split; [apply chain_nil, Hfp0|]. split; intros f [].
      + intros a (r & [] & _).
    - exists []. split; [constructor|]. intros st2 _. constructor.
  Qed.

  Lemma INV0_room st : INV0 st -> room st tinfo (Z.of_N 0).
  Proof.
    intros (_ & (_ & _ & alloc & limit & Ha & Hl & _ & Hle & _) & _).
    exists alloc, limit. split; [exact Ha|]. split; [exact Hl|]. lia.
  Qed.
End Entry_INV.

(* ------------------------------------------------------------------ *)
(** ** The activation of [@certirocq_main] *)

Lemma fun_ids_name_in fds x : In x (fun_ids fds) -> name_in_fundefs fds x.
Proof.
  induction fds as [g gt ys e' rest IH|]; cbn; [|intros []].
  intros [<-|H]; [left; constructor|right; apply IH, H].
Qed.

(** Facts about [main] from [llvm_restricted]. *)
Lemma main_free cenv fds main x :
  llvm_restricted cenv fds main -> occurs_free main x -> name_in_fundefs fds x.
Proof.
  intros (_ & _ & Hcl & _) Hx. destruct (in_dec Pos.eq_dec x (fun_ids fds)) as [Hin|Hnin].
  - apply fun_ids_name_in, Hin.
  - exfalso. apply Hcl. exists x. apply Free_Efun1; [|exact Hx].
    intros H. apply Hnin, name_in_fun_ids, H.
Qed.

Lemma main_disjoint cenv fds main :
  llvm_restricted cenv fds main ->
  Ensembles.Disjoint _ (bound_var main) (occurs_free main).
Proof.
  intros Hp. pose proof Hp as (_ & _ & _ & Hub & _). inversion Hub as [| | | | |? ? _ _ Hdis| | | |]; subst.
  constructor. intros x Hx. inversion Hx as [? Hb Hf]; subst.
  apply (main_free _ _ _ _ Hp), name_in_fundefs_bound_var_fundefs in Hf.
  destruct Hdis as [Hdis]. apply (Hdis x). constructor; assumption.
Qed.

Lemma main_unique cenv fds main :
  llvm_restricted cenv fds main -> unique_bindings main /\ NoDup (fun_ids fds).
Proof.
  intros (_ & _ & _ & Hub & _). inversion Hub; subst. split; [assumption|].
  apply unique_fun_ids. assumption.
Qed.

Section Main_activation.
  Variable cenv : ctor_env.
  Variable prim_of : positive -> option (string * bool).
  Variable fds : fundefs.
  Variable main : term.exp.
  Variable heap_inv : state -> ptr -> Prop.
  Variable G : global_env.
  Variable ctx : CallE ~> itree (CallE +' MCFGEtop).
  Variable tinfo fp : ptr.
  Hypothesis Hfp0 : ptr_to_int fp = 0.
  Hypothesis Hmut : forall st st2 alloc alloc2 limit,
       heap_inv st tinfo -> tinfo_ok st tinfo ->
       heap_agree_except st st2 (mutator_writes st tinfo) ->
       field st tinfo off_alloc alloc -> field st tinfo off_limit limit ->
       field st2 tinfo off_alloc alloc2 ->
       (ptr_to_int alloc <= ptr_to_int alloc2 <= ptr_to_int limit)%Z ->
       (ptr_to_int alloc2 mod 8 = 0)%Z ->
       heap_inv st2 tinfo.
  Hypothesis Hprog : llvm_restricted cenv fds main.

  Let go := ord_of cenv.
  Let ga := arity_of cenv.
  Let fs := fun_ids fds.

  (** The source environment in which [main] runs. *)
  Definition rho_main : eval.env := def_funs fds fds (M.empty _) (M.empty _).

  Variable v : term.val.
  Hypothesis Hsim : sim_stmt cenv prim_of fds heap_inv G ctx tinfo main rho_main main v.

  Theorem main_activation st1 sf0 stk0 :
    INV0 heap_inv tinfo fp st1 ->
    oom ctx (denote_function (main_cdef cenv prim_of fds main) [Ptr tinfo]) (st1, ((sf0, stk0), G)) \/
    exists st3 z,
      runs ctx (denote_function (main_cdef cenv prim_of fds main) [Ptr tinfo])
           (st1, ((sf0, stk0), G)) (st3, ((sf0, stk0), G)) (inr (I64 z)) /\
      repr_val cenv fds G st3 v z.
  Proof.
    intros H0.
    pose proof Hprog as (_ & Hbo & _).
    destruct (main_unique _ _ _ Hprog) as [Hub _].
    destruct (translate_cfg go ga prim_of fs base_env 0%N main 1%positive) as [blks f'] eqn:Etr.
    destruct (translate_cfg_entry go ga prim_of fs base_env 0%N _ _ _ _ Etr)
      as (b & rest & q & -> & Hphb & _).
    destruct (translate_cfg_labels go ga prim_of fs base_env 0%N _ _ _ _ Etr) as [_ Hlbl].
    destruct (mk_fun_spec go ga prim_of fs (Name "certirocq_main") [] main _ _ Etr)
      as (b' & rest' & E & Hdi & _ & Hargs). injection E as <- <-.
    (* the shape of the converted, flattened definition *)
    set (b0 := flatB (cblock b) 1).
    set (B := b0 :: fst (Flatten_sem.flat_blocksP (map cblock rest)
                          (snd (Flatten_sem.flat_blockP (cblock b) 1)))).
    assert (Hdef : df_instrs (main_cdef cenv prim_of fds main) =
                   {| init := blk_id b; blks := B; args := [Name "tinfo"] |} /\
                   df_args (main_cdef cenv prim_of fds main) = [Name "tinfo"]).
    { unfold main_cdef. pose proof (Flatten_sem.conv_def_flat_def (main_ldef cenv prim_of fds main)) as Hc.
      cbv zeta in Hc. rewrite Hc. unfold main_ldef. fold go ga fs. rewrite Hdi, Hargs. split; reflexivity. }
    destruct Hdef as [Hdi' Hargs'].
    assert (Hinit : init (df_instrs (main_cdef cenv prim_of fds main)) = blk_id b0).
    { rewrite Hdi'. cbn. unfold b0. rewrite flatB_id, cblock_id. reflexivity. }
    assert (Hfind : RM.find (blk_id b0) (ocfg_map (blks (df_instrs (main_cdef cenv prim_of fds main))))
                    = Some b0).
    { rewrite Hdi'. apply find_ocfg_map_cons. }
    assert (Hphis : blk_phis b0 = []).
    { unfold b0. rewrite flatB_phis. apply cblock_phis_nil, Hphb. }
    assert (Hlen : length [Ptr tinfo] = length (df_args (main_cdef cenv prim_of fds main)))
      by (rewrite Hargs'; reflexivity).
    destruct (push_call_frame_cases ctx _ _ st1 sf0 stk0 G Hlen) as [Ho|(st' & p & Hpush & Hpp)].
    { left. apply oom_denote_function_push, Ho. }
    rewrite Hargs' in Hpush.
    assert (H0' : INV0 heap_inv tinfo fp st') by (eapply INV0_grow; eauto; apply push_post_grow, Hpp).
    set (sf := new_frame (combine [Name "tinfo"] [Ptr tinfo])) in Hpush.
    assert (Hsr := Hsim base_env 0%N 1%positive (b :: rest) f' B (Some p) 1%positive st' sf
                        (sf0 :: stk0) fp [] []).
    destruct Hsr as [Ho|(st2 & sf2 & z & Hret & Hstab & HINV & (ks & Hfr & _) & _)].
    - exact Hbo.
    - apply Relation_Operators.rt_step, dsubterm_fds2.
    - exact Hub.
    - eapply main_disjoint; eauto.
    - intros y. split; intros _; [left|]; reflexivity.
    - exact Etr.
    - (* blocks_in *)
      intros bb Hbb. cbn [tl] in Hbb.
      destruct (flat_blocksP_in rest (snd (Flatten_sem.flat_blockP (cblock b) 1)) bb Hbb) as (c' & Hc').
      exists c'. rewrite <- (cblock_id bb), <- (flatB_id (cblock bb) c').
      apply find_ocfg_map; [|right; exact Hc'].
      unfold B. cbn [map]. unfold b0. rewrite flatB_id, Flatten_sem.flat_blocksP_ids, map_map.
      rewrite (map_ext _ blk_id cblock_id). rewrite cblock_id. exact Hlbl.
    - apply INV0_INV; auto.
    - unfold tinfo_local, sf, new_frame. cbn. first [reflexivity|apply rfind_add_eq].
    - intros x Hx. pose proof (main_free _ _ _ _ Hprog Hx) as Hn.
      exists (Vfun (M.empty _) fds x). split; [apply def_funs_eq, Hn|].
      rewrite is_fun_true by (apply name_in_fun_ids, Hn). exists (M.empty _). reflexivity.
    - apply (INV0_room heap_inv tinfo fp), H0'.
    - (* out of memory in the body *)
      left. eapply oom_denote_function_body; [exact Hinit|exact Hfind|exact Hphis| |].
      + exact Hpush.
      + rewrite Hdi'. exact Ho.
    - (* return *)
      destruct Hpp as (_ & Hfr' & _).
      rewrite Hfr' in Hfr. cbn [push_top] in Hfr.
      assert (Hbody : runs ctx (block_tail (Some p) (blks (df_instrs (main_cdef cenv prim_of fds main))) b0)
                         (st', ((new_frame (combine (df_args (main_cdef cenv prim_of fds main)) [Ptr tinfo]),
                                 sf0 :: stk0), G))
                         (st2, ((sf2, sf0 :: stk0), G)) (inr (I64 z))).
      { rewrite Hdi', Hargs'. exact Hret. }
      rewrite <- Hargs' in Hpush.
      destruct (denote_function_runs ctx _ b0 [Ptr tinfo] st1 sf0 stk0 G st' p st2 sf2 sf0 stk0 G
                  (I64 z) (frames_of st1) (rev ks ++ [])%list Hinit Hfind Hphis Hpush Hbody Hfr)
        as (st3 & Hruns & Hpop).
      right. exists st3, z. split; [exact Hruns|].
      apply Hstab. intros a Hia _. destruct Hpop as (_ & _ & _ & Hout). apply Hout.
      intros Hin. destruct HINV as (_ & _ & (_ & Hm2) & _). apply (Hm2 a); [|exact Hia].
      unfold in_frames. rewrite Hfr. cbn [frames_ptrs]. rewrite map_app. apply in_app_iff. left. exact Hin.
  Qed.
End Main_activation.

(* ------------------------------------------------------------------ *)
(** ** The runtime contract needed by the proof

    The section hypotheses of [LLVM_sim] ([Hmut], [Hgc], [Htinfo_range]) and
    the entry invariant [INV0] are stated with [LLVM_sim]'s memory predicates
    ([mem_ok], [nursery_tinfo_disjoint], [slot_bytes]) and [Ptr].  The
    statement file has its own copies of these ([..._stmt]), with the same
    bodies, so the two are convertible.  [runtime_extra] collects what the
    proof uses beyond the [Hmut] clause, in [LLVM_sim]'s vocabulary, and
    [runtime_extra_of_correct] derives it from [runtime_correct]. *)

Lemma frames_ptrs_stmt_eq fs : frames_ptrs_stmt fs = frames_ptrs fs.
Proof. induction fs as [f|fs IH f]; cbn; [reflexivity|]. rewrite IH. reflexivity. Qed.

Lemma in_frames_stmt_iff st a : in_frames_stmt st a <-> in_frames st a.
Proof. unfold in_frames_stmt, in_frames. rewrite frames_ptrs_stmt_eq. reflexivity. Qed.

Lemma mem_ok_stmt_iff st : mem_ok_stmt st <-> mem_ok st.
Proof.
  unfold mem_ok_stmt, mem_ok. split; intros [H1 H2]; split; auto;
    intros a Ha; apply H2, in_frames_stmt_iff, Ha.
Qed.

Lemma nursery_tinfo_disjoint_stmt_iff st tinfo :
  nursery_tinfo_disjoint_stmt st tinfo <-> nursery_tinfo_disjoint st tinfo.
Proof. reflexivity. Qed.

Lemma slot_bytes_stmt_iff rs a : slot_bytes_stmt rs a <-> slot_bytes rs a.
Proof. reflexivity. Qed.

Definition gc_contract (cenv : ctor_env) (fds : fundefs) (heap_inv : state -> ptr -> Prop)
           (gc : list dvalue -> MCFGtop (exc + dvalue)) : Prop :=
  forall (G : global_env) (tinfo : ptr) (st : state) ls fp rs vs nalloc,
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

Definition runtime_extra (cenv : ctor_env) (fds : fundefs) (heap_inv : state -> ptr -> Prop)
           (gc : list dvalue -> MCFGtop (exc + dvalue)) (make_tinfo : MCFGtop dvalue) : Prop :=
  (forall st tinfo,
     returns (interp_mcfg make_tinfo initial_fused)
             ((st, snd initial_fused), DVALUE_Base (DVALUE_Pointer tinfo)) ->
     mem_ok st /\ nursery_tinfo_disjoint st tinfo /\ ptr_to_int tinfo + 8232 < 2^64) /\
  gc_contract cenv fds heap_inv gc.

Lemma runtime_extra_of_correct cenv fds heap_inv gc make_tinfo :
  runtime_correct cenv fds heap_inv gc make_tinfo -> runtime_extra cenv fds heap_inv gc make_tinfo.
Proof.
  intros (Hinit & _ & Hgc). split.
  - intros st tinfo Hret. unfold returns in Hret.
    destruct Hinit as [Ho|(st0 & tinfo0 & fp & Hret0 & (_ & _ & Hm & Hd & _) & _ & Hr)].
    + exfalso. destruct Ho as (k & Hk). rewrite Hret in Hk.
      apply eqit_inv in Hk. exact Hk.
    + unfold returns in Hret0. rewrite Hret in Hret0. apply eqit_inv in Hret0. cbn in Hret0.
      injection Hret0 as <- <-.
      split; [apply mem_ok_stmt_iff, Hm|]. split; [exact Hd|exact Hr].
  - intros G tinfo st ls fp rs vs nalloc Hhi Hok Hm Hd Hfp Hss Hroots Hnb Hn.
    destruct (Hgc G tinfo st ls fp rs vs nalloc
                (conj Hhi (conj Hok (conj (proj2 (mem_ok_stmt_iff st) Hm) (conj Hd (conj Hfp Hss)))))
                Hroots Hnb Hn)
      as [Ho|(st' & Hret & (Hhi' & Hok' & Hm' & Hd' & Hfp' & Hss') & Hroots' & Hroom & Hfr & Hw & Hfresh & Hslaid)].
    + left. exact Ho.
    + right. exists st'. split; [exact Hret|]. split; [exact Hfr|]. split; [exact Hhi'|].
      split; [exact Hok'|]. split; [apply mem_ok_stmt_iff, Hm'|]. split; [exact Hd'|].
      split; [exact Hfp'|]. split; [exact Hss'|]. split; [exact Hroots'|]. split; [exact Hroom|].
      split; [|split; [exact Hfresh|exact Hslaid]]. intros a Ha Hs. apply Hw; [exact Ha|].
      intros Hs'. apply Hs, slot_bytes_stmt_iff, Hs'.
Qed.

(** The statement of the main simulation lemma [sim_exp] (to be proved in
    [LLVM_sim_exp.v] by induction on [bstep_e], from the cases in
    [LLVM_sim_cases_*.v]): for every instance of the section variables of
    [LLVM_sim.Simulation] satisfying its section hypotheses ([Hmut], [Hgc],
    [Htinfo_range], [ctx_fun], [ctx_gc], [G_funs], [G_gc], [Hprog]), every
    terminating source evaluation is simulated ([sim_stmt]). *)
Definition sim_exp_statement : Prop :=
  forall (cenv : ctor_env) (pfs : prims) (prim_of : positive -> option (string * bool))
         (fds : fundefs) (heap_inv : state -> ptr -> Prop)
         (gc : list dvalue -> MCFGtop (exc + dvalue)) (G : global_env)
         (ctx : CallE ~> itree (CallE +' MCFGEtop)) (tinfo : ptr),
  (* Hmut *)
  (forall st st2 alloc alloc2 limit,
     heap_inv st tinfo -> tinfo_ok st tinfo ->
     heap_agree_except st st2 (mutator_writes st tinfo) ->
     field st tinfo off_alloc alloc -> field st tinfo off_limit limit ->
     field st2 tinfo off_alloc alloc2 ->
     (ptr_to_int alloc <= ptr_to_int alloc2 <= ptr_to_int limit)%Z ->
     (ptr_to_int alloc2 mod 8 = 0)%Z ->
     heap_inv st2 tinfo) ->
  (* Hgc *)
  (forall (st : state) ls fp rs vs nalloc,
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
         (forall a, slot_bytes rs a -> aid_at st' a = aid_at st a)) ->
  (* Htinfo_range *)
  ptr_to_int tinfo + 8232 < 2^64 ->
  (* ctx_fun *)
  (forall f ft xs e fp,
     fun_in_fundefs fds (f, ft, xs, e) ->
     RM.find (Anon (Zpos f)) G = Some (Ptr fp) ->
     forall dt p args, ptr_to_int p = ptr_to_int fp ->
       ctx _ (Call dt (Ptr p) args) ≈ denote_function (fun_def cenv prim_of fds f xs e) args) ->
  (* ctx_gc *)
  (forall gp,
     RM.find (Name "garbage_collect") G = Some (Ptr gp) ->
     forall dt p args, ptr_to_int p = ptr_to_int gp ->
       ctx _ (Call dt (Ptr p) args) ≈ lift_top (gc args)) ->
  (* G_funs *)
  (forall f, In f (fun_ids fds) -> exists fp, RM.find (Anon (Zpos f)) G = Some (Ptr fp)) ->
  (* G_gc *)
  (exists gp, RM.find (Name "garbage_collect") G = Some (Ptr gp)) ->
  forall main : term.exp,
  (* Hprog *)
  llvm_restricted cenv fds main ->
  forall rho e v n,
    bstep_e pfs cenv rho e v n ->
    sim_stmt cenv prim_of fds heap_inv G ctx tinfo main rho e v.

(* ------------------------------------------------------------------ *)
(** ** The whole program *)

Section Whole.
  Variable cenv : ctor_env.
  Variable pfs : prims.
  Variable prim_of : positive -> option (string * bool).
  Variable heap_inv : state -> ptr -> Prop.
  Variable gc : list dvalue -> MCFGtop (exc + dvalue).
  Variable make_tinfo : MCFGtop dvalue.
  Variable fds : fundefs.
  Variable main : term.exp.

  Hypothesis SIM : sim_exp_statement.
  Hypothesis Hrt : runtime_correct cenv fds heap_inv gc make_tinfo.
  Hypothesis Hprog : llvm_restricted cenv fds main.

  Definition gc_den : function_denotation := fun args => lift_top (gc args).
  Definition rt_libs := [(Name "garbage_collect", gc_den)].
  Definition whole : MCFGtop dvalue :=
    ITree.bind make_tinfo (fun tinfo =>
      denote_with_runtime rt_libs (DTYPE_I 64) (Name "certirocq_main") [tinfo] (the_mcfg cenv prim_of fds main)).

  Lemma run_program_whole :
    run_program gc make_tinfo (emitted cenv prim_of (Efun fds main)) = interp_mcfg whole initial_fused.
  Proof. unfold run_program. rewrite the_mcfg_eq. reflexivity. Qed.

  Variable v : term.val.
  Variable n : nat.
  Hypothesis Hev : bstep_e pfs cenv (M.empty _) (Efun fds main) v n.

  Theorem whole_correct :
    toom whole initial_fused \/
    exists st ls G z, truns whole initial_fused (st, (ls, G)) (I64 z) /\ repr_val cenv fds G st v z.
  Proof.
    destruct (main_unique _ _ _ Hprog) as [_ Hnd].
    assert (Hev' : bstep_e pfs cenv (rho_main fds) main v n) by (inversion Hev; subst; assumption).
    destruct (runtime_extra_of_correct _ _ _ _ _ Hrt) as (Hext1 & Hgcc).
    destruct Hrt as (Hinit & Hmut_all & _).
    unfold whole.
    destruct Hinit as [Ho|(st0 & tinfo & fp & Hret & (Hhi & Hok & _ & _ & Hfp & _) & Hfp0 & _)].
    { left. apply toom_bind_l, Ho. }
    destruct (Hext1 st0 tinfo Hret) as (Hmem & Hdis & Hrange).
    assert (Hmut : forall st st2 alloc alloc2 limit,
       heap_inv st tinfo -> tinfo_ok st tinfo ->
       heap_agree_except st st2 (mutator_writes st tinfo) ->
       field st tinfo off_alloc alloc -> field st tinfo off_limit limit ->
       field st2 tinfo off_alloc alloc2 ->
       (ptr_to_int alloc <= ptr_to_int alloc2 <= ptr_to_int limit)%Z ->
       (ptr_to_int alloc2 mod 8 = 0)%Z ->
       heap_inv st2 tinfo) by (intros; eapply Hmut_all; eauto).
    assert (H0 : INV0 heap_inv tinfo fp st0).
    { split; [exact Hhi|]. split; [exact Hok|]. split; [exact Hmem|]. split; [exact Hdis|exact Hfp]. }
    set (ls0 := fst (snd initial_fused)).
    assert (Hs0 : snd initial_fused = (ls0, Maps.empty)) by reflexivity.
    rewrite Hs0 in Hret.
    unfold denote_with_runtime.
    destruct (global_init cenv prim_of fds main Hnd st0 ls0) as [Ho|(st1 & G & Hglob & Hg & HGok)].
    { left. eapply toom_bind_r; [exact Hret|]. apply toom_bind_l, Ho. }
    assert (H1 : INV0 heap_inv tinfo fp st1) by (eapply INV0_grow; eauto).
    destruct (G_ok_main _ _ _ _ _ HGok) as (pm & Hpm).
    set (ctx := ctx_of (fun_table cenv prim_of fds main gc_den G)).
    (* the main simulation lemma, instantiated for the real knot *)
    assert (Hsim : sim_stmt cenv prim_of fds heap_inv G ctx tinfo main (rho_main fds) main v).
    { eapply (SIM cenv pfs prim_of fds heap_inv gc G ctx tinfo); [| | | | | | | exact Hprog | exact Hev'].
      - exact Hmut.
      - intros st ls fp' rs vs nalloc. apply (Hgcc G tinfo st ls fp' rs vs nalloc).
      - exact Hrange.
      - intros f ft xs e fp' Hin Hf. eapply ctx_real_fun; eauto.
      - intros gp Hf. eapply ctx_real_gc; eauto.
      - intros f Hf. eapply G_ok_fun; eauto.
      - eapply G_ok_gc; eauto. }
    (* everything up to the entry call *)
    assert (Hpre : forall X (k : _ -> MCFGtop X) s r,
      truns (k (map (fun d => (addr_of G (dc_name (df_prototype d)), denote_function d))
                    (cdefs cenv prim_of fds main))) (st1, (ls0, G)) s r ->
      truns ('defns <- map_monad address_one_function (m_definitions (the_mcfg cenv prim_of fds main)) ;; k defns)
            (st1, (ls0, G)) s r).
    { intros X k s r Hk. eapply truns_bind; [apply addresses_run; exact HGok|exact Hk]. }
    assert (Hlib : truns (map_monad address_one_library_function
                            (rt_libs ++ library_functions (m_declarations (the_mcfg cenv prim_of fds main))))
                         (st1, (ls0, G)) (st1, (ls0, G)) [(addr_of G (Name "garbage_collect"), gc_den)])
      by (apply libraries_run; exact HGok).
    assert (Hknot : forall s r,
      runs ctx (denote_function (main_cdef cenv prim_of fds main) [Ptr tinfo]) (st1, (ls0, G)) s r ->
      truns (denote_mcfg (fun_table cenv prim_of fds main gc_den G) (DTYPE_I 64) (Ptr pm) [Ptr tinfo])
            (st1, (ls0, G)) s r).
    { intros s r H. unfold truns. rewrite denote_mcfg_unfold.
      rewrite (ctx_real_main cenv prim_of fds main gc_den G pm [Ptr tinfo] HGok Hpm). exact H. }
    assert (Hknot_oom :
      oom ctx (denote_function (main_cdef cenv prim_of fds main) [Ptr tinfo]) (st1, (ls0, G)) ->
      toom (denote_mcfg (fun_table cenv prim_of fds main gc_den G) (DTYPE_I 64) (Ptr pm) [Ptr tinfo])
            (st1, (ls0, G))).
    { intros H. unfold toom. rewrite denote_mcfg_unfold.
      rewrite (ctx_real_main cenv prim_of fds main gc_den G pm [Ptr tinfo] HGok Hpm). exact H. }
    destruct ls0 as [sf0 stk0] eqn:Els.
    destruct (main_activation cenv prim_of fds main heap_inv G ctx tinfo fp Hfp0 Hmut Hprog v Hsim
                st1 sf0 stk0 H1) as [Ho|(st3 & z & Hruns & Hrepr)].
    - left. eapply toom_bind_r; [exact Hret|]. eapply toom_bind_r; [exact Hglob|].
      eapply toom_bind_r; [apply addresses_run; exact HGok|].
      eapply toom_bind_r; [exact Hlib|].
      eapply toom_bind_r; [apply truns_gread, Hpm|].
      apply toom_bind_l. apply Hknot_oom, Ho.
    - right. exists st3, (sf0, stk0), G, z. split; [|exact Hrepr].
      eapply truns_bind; [exact Hret|]. eapply truns_bind; [exact Hglob|].
      eapply truns_bind; [apply addresses_run; exact HGok|].
      eapply truns_bind; [exact Hlib|].
      eapply truns_bind; [apply truns_gread, Hpm|].
      eapply truns_bind; [apply Hknot, Hruns|].
      apply truns_ret.
  Qed.
End Whole.

(** The statement of the statement file follows from [sim_exp]'s statement. *)
Theorem main_correct_of_sim :
  sim_exp_statement -> LambdaANF_to_LLVM_correct_statement.
Proof.
  intros SIM cenv pfs prim_of heap_inv gc make_tinfo fds main v n Hrt Hprog Hev.
  rewrite run_program_whole.
  destruct (whole_correct cenv pfs prim_of heap_inv gc make_tinfo fds main SIM Hrt Hprog v n Hev)
    as [Ho|(st & ls & G & z & Hr & Hrepr)].
  - left. exact Ho.
  - right. exists st, ls, G, z. split; [exact Hr|exact Hrepr].
Qed.

(* ------------------------------------------------------------------ *)
(** ** The top-level theorem

    [Theorem LambdaANF_to_LLVM_correct : LambdaANF_to_LLVM_correct_statement]
    is [main_correct_of_sim] applied to the proof of [sim_exp_statement]; it
    is stated in [LLVM_sim_exp.v], after the cases of the simulation
    ([LLVM_sim_cases_*.v]), which this file does not depend on. *)
