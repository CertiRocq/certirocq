(** * Non-vacuity, continued: the example program really returns

    [LLVM_nonvacuity.ex_correct] says that the compiled
    [ex_prog = Efun Fnil (Econstr 1 1 [] (Ehalt 1))], run with the witness
    runtime, runs out of memory or returns [1].  This file runs it
    symbolically in Vellvm's concrete memory model and shows that it returns
    [1] ([ex_returns]), so the out-of-memory disjunct does not hold
    ([ex_not_oom]).

    The run ([ex_whole_runs], for any collector: the program never calls it):
    - [nv_make_tinfo] ([nv_make_tinfo_runs]): one [malloc]'d block at
      addresses [0, nv_block_size); no other byte is allocated ([blk_ok]);
    - [build_global_environment]: one 8-byte [alloca] per declared name
      ([@garbage_collect], [@certirocq_main]).  In the concrete model an
      allocation only runs out of memory when the next free address plus its
      size reaches [2^64] ([allocate_dtyp_exists]); we track an upper bound
      on the allocated addresses ([keys_below], [next_key_bound],
      [alloc_keys]), which stays below [nv_block_size + 32].  The general
      [global_init] then provides [G_ok] ([truns_det], [truns_not_toom]);
    - [@certirocq_main(tinfo)]: [push_call_frame] (a [mem_push] and a 0-byte
      [alloca] for the varargs, [push_call_frame_runs_keys]), the one block
      [%-6 = shl 0, 1; %1 = or %-6, 1; ret %1] ([ex_main_flat],
      [ex_blk_code], [ex_blk_term], [ex_body_runs]: a nullary constructor
      allocates nothing), and [pop_call_frame] ([denote_function_runs]).

    Everything is [Qed]; [Print Assumptions ex_returns] lists only the
    standard library's axioms used by the rest of the development. *)

From Stdlib Require Import ZArith NArith List Lia String Program Morphisms.
From ITree Require Import ITree Eq.Eqit Interp.InterpFacts Events.State Events.StateFacts.
From ExtLib Require Import Structures.Monads.
From CertiRocq.LambdaANF Require Import term term_util eval identifiers.
From CertiRocq.CodegenLLVM Require Import LambdaANF_to_LLVM_statement LLVM_interp_lemmas LLVM_call_lemmas
     LLVM_exp_lemmas LLVM_mem_lemmas LLVM_instr_lemmas LLVM_toplevel_link LLVM_nonvacuity LLVM_convert LambdaANF_to_LLVM.
From Vellvm Require Import
  Utils Syntax Params
  Interfaces.Memory Implementations.Memory
  Semantics.DynamicValues Semantics.LLVMEvents Semantics.Denotation
  Semantics.InterpretationStack Semantics.TopLevel Semantics.Libraries Handlers.
From Vellvm Require Import Utils.IntMaps Semantics.Operations.Gep Semantics.EOU.
Import ListNotations.
Import MonadNotation.
Open Scope monad_scope.
Open Scope Z_scope.
Unset Implicit Arguments.
Set Bullet Behavior "Strict Subproofs".

Definition keys_below (st : state) (B : Z) : Prop :=
  forall a, IntMaps.lookup a (mem_of st) <> None -> a < B.

Lemma next_key_bound st B al :
  keys_below st B -> 0 < B -> (0 < al)%N ->
  next_key_with_alignment (mem_of st) al < B + Z.of_N al.
Proof.
  intros HB H0 Hal. unfold next_key_with_alignment.
  destruct (IM_greatest_key (mem_of st)) as [gk|] eqn:E; [|lia].
  apply IM_greatest_key_In in E.
  assert (Hgk : gk < B).
  { apply HB. unfold IntMaps.lookup. apply IP.F.in_find_iff, E. }
  unfold pad_to, pad_amount.
  pose proof (N.mod_lt (al - (1 + Z.to_N gk) mod al) al) as Hm.
  assert (Z.of_N (1 + Z.to_N gk) <= B) by lia.
  lia.
Qed.

Lemma allocate_dtyp_exists st t n al :
  dtyp_eqb t DTYPE_Void = false ->
  next_key_with_alignment (mem_of st) al + Z.of_N (n * sizeof_dtyp t) < 2 ^ 64 ->
  exists st' p, memS_runs_c st (allocate_dtyp t n al) st' p.
Proof.
  intros Ht Hb. unfold allocate_dtyp. rewrite Ht. unfold allocate_bytes.
  set (init := concat_acc (repeatN n (generate_poison_bytes t))).
  assert (Hlen : N_length init = (n * sizeof_dtyp t)%N).
  { rewrite N_length_nat. unfold init. rewrite allocate_dtyp_bytes_length. lia. }
  set (pr := next_provenance (state_provenance st)).
  set (a := next_key_with_alignment (mem_of st) al) in Hb.
  pose proof (next_key_nonneg (mem_of st) al) as Ha0. fold a in Ha0.
  destruct (@int_to_ptr_total a (allocation_id_to_prov (provenance_to_allocation_id pr))) as (p & Ep & Ep1 & Ep2);
    [pose proof (N2Z.is_nonneg (n * sizeof_dtyp t)); lia|].
  destruct (gcp_exists p (N_length init)) as (ptrs & Eg); [rewrite Ep1, Hlen; lia|].
  eexists; exists p.
  eapply memS_runs_c_bind; [apply MRC_fresh; apply MRC_ret|].
  change (allocate_bytes_with_pr init al ?q) with (Allocate_bytes_with_pr init al q).
  unfold Allocate_bytes_with_pr, get_free_block, add_block_to_stack, add_block,
    add_ptrs_to_frame, get_mem, upd_mem, app_mem, app_mem_stack.
  eapply memS_runs_c_bind.
  { eapply memS_runs_c_bind; [apply MRC_next_key, MRC_ret|].
    eapply memS_runs_c_bind.
    { change (mem_of {| state_memory_stack := state_memory_stack st; state_provenance := next_provenance (state_provenance st) |}) with (mem_of st).
      change (next_provenance (state_provenance st)) with pr.
      fold a. rewrite Ep. apply MRC_ret. }
    eapply memS_runs_c_bind; [rewrite Eg; apply MRC_ret|]. apply MRC_ret. }
  cbn. repeat econstructor.
Qed.

Lemma alloc_keys st t n al st' p B :
  memS_runs_c st (allocate_dtyp t n al) st' p -> keys_below st B -> 0 < B -> (0 < al)%N ->
  keys_below st' (B + Z.of_N al + Z.of_N (n * sizeof_dtyp t)).
Proof.
  intros H HB H0 Hal.
  pose proof (next_key_bound st B al HB H0 Hal) as Hn.
  apply allocate_dtyp_runs in H. destruct H as (_ & _ & Ep & _ & Hout & _).
  intros a Ha.
  destruct (Z_lt_le_dec a (ptr_to_int p + Z.of_N (n * sizeof_dtyp t))) as [Hlt|Hge]; [lia|].
  rewrite Hout in Ha by lia. apply HB in Ha. lia.
Qed.

Lemma alloca_ptr_exists st B :
  keys_below st B -> 0 < B -> B + 16 < 2 ^ 64 ->
  exists st' p, memS_runs_c st (allocate_dtyp DTYPE_Pointer 1 8) st' p /\ keys_below st' (B + 16).
Proof.
  intros HB H0 H1.
  pose proof (next_key_bound st B 8 HB H0 eq_refl) as Hn.
  destruct (allocate_dtyp_exists st DTYPE_Pointer 1 8 eq_refl) as (st' & p & H);
    [rewrite N.mul_1_l, sizeof_ptr; lia|].
  exists st', p. split; [exact H|].
  pose proof (alloc_keys _ _ _ _ _ _ _ H HB H0 eq_refl) as K.
  rewrite N.mul_1_l, sizeof_ptr in K. intros a Ha. specialize (K a Ha). lia.
Qed.

Lemma truns_det {X} (t : MCFGtop X) s s1 r1 s2 r2 :
  truns t s s1 r1 -> truns t s s2 r2 -> s1 = s2 /\ r1 = r2.
Proof.
  unfold truns. intros H1 H2. rewrite H1 in H2. apply eqit_inv in H2. cbn in H2.
  injection H2. auto.
Qed.

Lemma truns_not_toom {X} (t : MCFGtop X) s s1 r : truns t s s1 r -> ~ toom t s.
Proof.
  unfold truns, toom, ends_in_oom. intros H [k Hk]. rewrite H in Hk.
  eapply eutt_Ret_Vis_abs; exact Hk.
Qed.

Lemma alloc_decls_runs (ds : list (declaration dtyp)) : forall st ls g B,
  Forall (fun d => IntrinsicsDefinitions.lookup_intrinsic_declaration (dc_name d) = None) ds ->
  keys_below st B -> 0 < B -> B + 16 * Z.of_nat (length ds) < 2 ^ 64 ->
  exists st' g',
    truns (allocate_declarations ds) (st, (ls, g)) (st', (ls, g')) tt /\
    keys_below st' (B + 16 * Z.of_nat (length ds)).
Proof.
  induction ds as [|d ds IH]; intros st ls g B Hint HB H0 H1.
  - exists st, g. split; [apply truns_ret|]. cbn [length]. rewrite Z.add_0_r. exact HB.
  - inversion Hint as [|? ? Hd Hint']; subst.
    cbn [length] in H1.
    destruct (alloca_ptr_exists st B HB H0) as (st1 & p & Hr & HB1); [lia|].
    destruct (IH st1 ls (Maps.add (dc_name d) (Ptr p) g) (B + 16) Hint' HB1) as (st' & g' & Hrun & HB'); [lia|lia|].
    exists st', g'. split.
    + unfold allocate_declarations. cbn [loop_monad]. rewrite (allocate_declaration_eq d Hd).
      eapply truns_bind; [|exact Hrun].
      eapply truns_bind; [apply truns_alloca, Hr|]. apply truns_gwrite.
    + cbn [length]. replace (B + 16 * Z.of_nat (S (length ds))) with (B + 16 + 16 * Z.of_nat (length ds)) by lia.
      exact HB'.
Qed.

Section Ex.
  Variable prim_of : positive -> option (string * bool).

  Lemma ex_global_init st ls B :
    keys_below st B -> 0 < B -> B + 64 < 2 ^ 64 ->
    exists st' G,
      truns (build_global_environment (the_mcfg ex_cenv prim_of Fnil ex_main)) (st, (ls, Maps.empty))
            (st', (ls, G)) tt /\
      G_ok ex_cenv prim_of Fnil ex_main G /\ keys_below st' (B + 32).
  Proof.
    intros HB H0 H1.
    set (M := the_mcfg ex_cenv prim_of Fnil ex_main).
    set (ds := (m_declarations M ++ map df_prototype (m_definitions M))%list).
    assert (Hlen : length ds = 2%nat) by reflexivity.
    assert (Hn : map dc_name ds = decl_names ex_cenv prim_of Fnil ex_main) by apply the_decls_names.
    assert (Hint : Forall (fun d => IntrinsicsDefinitions.lookup_intrinsic_declaration (dc_name d) = None) ds).
    { apply Forall_forall. intros d Hd. pose proof (decl_names_not_intrinsic ex_cenv prim_of Fnil ex_main) as H.
      rewrite <- Hn, Forall_map, Forall_forall in H. apply H, Hd. }
    destruct (alloc_decls_runs ds st ls Maps.empty B Hint HB H0) as (st' & g' & Hrun & HB');
      [rewrite Hlen; lia|].
    assert (Hb : truns (build_global_environment M) (st, (ls, Maps.empty)) (st', (ls, g')) tt).
    { unfold build_global_environment. eapply truns_bind; [exact Hrun|].
      cbn [m_globals M the_mcfg allocate_globals initialize_globals loop_monad].
      eapply truns_bind; apply truns_ret. }
    destruct (global_init ex_cenv prim_of Fnil ex_main (NoDup_nil _) st ls) as [Ho|(st2 & G & Hg & _ & Hok)].
    - exfalso. eapply truns_not_toom; [exact Hb|exact Ho].
    - destruct (truns_det _ _ _ _ _ _ Hb Hg) as [E _]. injection E as <- <-.
      exists st', g'. split; [exact Hb|]. split; [exact Hok|].
      rewrite Hlen in HB'. intros a Ha. specialize (HB' a Ha). lia.
  Qed.

  Lemma push_call_frame_runs_keys ctx df args st sf stk g B :
    length args = length (df_args df) -> keys_below st B -> 0 < B -> B + 8 < 2 ^ 64 ->
    exists st' p,
      runs ctx (push_call_frame df args) (st, ((sf, stk), g))
           (st', ((new_frame (combine (df_args df) args), sf :: stk), g)) p /\
      push_post st st'.
  Proof.
    intros L HB H0 H1.
    destruct (runs_mem_push ctx st ((sf, stk), g)) as (st1 & Hpush & Em & Eh & Ef & _).
    assert (HB1 : keys_below st1 B) by (intros a; rewrite Em; apply HB).
    pose proof (next_key_bound st1 B 8 HB1 H0 eq_refl) as Hn.
    destruct (allocate_dtyp_exists st1 (DTYPE_Struct true []) 1 8 eq_refl) as (st2 & p & Ha);
      [cbn; lia|].
    destruct (store_empty_exists st2 p) as [st3 Hs]. exists st3, p. split.
    - eapply runs_eutt; [symmetry; apply push_call_frame_eq, L|].
      eapply runs_bind; [exact Hpush|]. eapply runs_bind; [apply runs_stack_push|].
      eapply runs_bind.
      { unfold alloca. apply runs_memory_c. cbn [handle_memoryM].
        eapply memS_runs_c_bind; [exact Ha|constructor]. }
      eapply runs_bind; [unfold store; apply runs_memory; cbn [handle_memoryM]; exact Hs|].
      apply runs_ret.
    - apply allocate_dtyp_post in Ha. destruct Ha as (Ha1 & (ptrs & _ & Lp & Fp) & _ & Ho & _).
      destruct ptrs; [|discriminate].
      destruct (store_empty_post _ _ _ Hs) as (S1 & S2 & S3).
      split; [congruence|split].
      + rewrite S2, Fp, Ef. reflexivity.
      + intros a. rewrite S3, Ho, Em; [reflexivity|]. cbn. lia.
  Qed.

  (** The emitted [@certirocq_main] for [ex_main], before type conversion:
      one block computing [Val_long 0] and returning it. *)
  Definition ex_blk : LLVMAst.block typ :=
    mk_block (Anon 1%Z) []
      [(IId (Raw (-6)), INSTR_Op (OP_IBinop (Shl false false) (TYPE_I 64) (EXP_Integer (Nat.to_num_int 0))
                                            (EXP_Integer (Nat.to_num_int 1))), []);
       (IId (Raw 1), INSTR_Op (OP_IBinop (Or false) (TYPE_I 64) (EXP_Ident (ID_Local (Raw (-6))))
                                         (EXP_Integer (Nat.to_num_int 1))), [])]
      (IVoid 1%Z, TERM_Ret (TYPE_I 64, EXP_Ident (ID_Local (Raw 1))), []) None.

  Lemma ex_main_flat :
    df_instrs (Flatten.flat_def (main_ldef ex_cenv prim_of Fnil ex_main)) = (ex_blk, []) /\
    df_args (Flatten.flat_def (main_ldef ex_cenv prim_of Fnil ex_main)) = [Name "tinfo"].
  Proof. split; reflexivity. Qed.

  Lemma ex_blk_code :
    blk_code (cblock ex_blk) =
      [(IId (Raw (-6)), INSTR_Op (OP_IBinop (Shl false false) (DTYPE_I 64 : dtyp) (EXP_Integer (Nat.to_num_int 0))
                                            (EXP_Integer (Nat.to_num_int 1))), []);
       (IId (Raw 1), INSTR_Op (OP_IBinop (Or false) (DTYPE_I 64 : dtyp) (EXP_Ident (ID_Local (Raw (-6))))
                                         (EXP_Integer (Nat.to_num_int 1))), [])].
  Proof.
    rewrite cblock_eq. unfold ex_blk. cbn [blk_code].
    rewrite !ccode_cons, ccode_nil, !cinstr_Op, !cexp_IBinop, cty_I. reflexivity.
  Qed.

  Lemma ex_blk_term :
    blk_term (cblock ex_blk) = (IVoid 1%Z, TERM_Ret (DTYPE_I 64 : dtyp, EXP_Ident (ID_Local (Raw 1))), []).
  Proof.
    rewrite cblock_eq. unfold ex_blk. cbn [blk_term].
    rewrite cterm_Ret. unfold ctexp. cbn [fst snd]. rewrite cty_I, cexp_Ident. reflexivity.
  Qed.

  Lemma ex_body_runs ctx p bs st sf stk g :
    exists sf2,
      runs ctx (block_tail (Some p) bs (cblock ex_blk)) (st, ((sf, stk), g)) (st, ((sf2, stk), g)) (inr (I64 1)).
  Proof.
    set (sf1 := upd_local_sf sf (Maps.add (Raw (-6)) (I64 (2 * 0)) (stack_vars sf))).
    set (sf2 := upd_local_sf sf1 (Maps.add (Raw 1) (I64 (2 * 0 + 1)) (stack_vars sf1))).
    exists sf2. unfold block_tail. rewrite ex_blk_code, ex_blk_term.
    eapply runs_bind; [eapply runs_bind|].
    - eapply runs_code_cons; [apply instr_op|].
      { eapply exp_eval_ibinop; [apply (exp_eval_lit64 _ _ _ _ 0)|apply exp_eval_lit64|apply (eval_shl1 0)]. }
      eapply runs_code_cons; [apply instr_op|apply runs_code_nil].
      eapply exp_eval_ibinop; [|apply exp_eval_lit64|apply (eval_or1_even 0)].
      apply exp_eval_local. unfold sf1. rewrite stack_vars_upd. apply rfind_add_eq.
    - apply term_ret. apply exp_eval_local. unfold sf2. rewrite stack_vars_upd. apply rfind_add_eq.
    - cbn [cont_of]. apply runs_ret.
  Qed.

  Lemma ex_main_runs ctx tinfo st sf stk g B :
    keys_below st B -> 0 < B -> B + 8 < 2 ^ 64 ->
    exists st',
      runs ctx (denote_function (main_cdef ex_cenv prim_of Fnil ex_main) [Ptr tinfo])
           (st, ((sf, stk), g)) (st', ((sf, stk), g)) (inr (I64 1)).
  Proof.
    intros HB H0 H1.
    set (d := Flatten.flat_def (main_ldef ex_cenv prim_of Fnil ex_main)).
    destruct (conv_def_entry d) as (Hi & Hf & Ha). cbv zeta in Hi, Hf.
    destruct ex_main_flat as [Ed Ea]. fold d in Ed, Ea.
    rewrite Ed in Hi, Hf. cbn [fst] in Hi, Hf.
    change (conv_def d) with (main_cdef ex_cenv prim_of Fnil ex_main) in Hi, Hf, Ha.
    assert (Hp : blk_phis (cblock ex_blk) = []) by (apply cblock_phis_nil; reflexivity).
    assert (L : length [Ptr tinfo] = length (df_args (main_cdef ex_cenv prim_of Fnil ex_main)))
      by (rewrite Ha, Ea; reflexivity).
    destruct (push_call_frame_runs_keys ctx _ _ st sf stk g B L HB H0 H1) as (st1 & p & Hpush & (_ & Hfr & _)).
    destruct (ex_body_runs ctx p (blks (df_instrs (main_cdef ex_cenv prim_of Fnil ex_main))) st1
                (new_frame (combine (df_args (main_cdef ex_cenv prim_of Fnil ex_main)) [Ptr tinfo])) (sf :: stk) g)
      as (sf2 & Hbody).
    destruct (denote_function_runs ctx _ (cblock ex_blk) [Ptr tinfo] st sf stk g st1 p st1 sf2 sf stk g
                (I64 1) (frames_of st) [] Hi Hf Hp Hpush Hbody Hfr) as (st3 & Hruns & _).
    exists st3. exact Hruns.
  Qed.

  (** The whole run of the compiled [ex_prog], for any collector (the
      program never calls it). *)
  Theorem ex_whole_runs gc :
    exists st ls G,
      truns (whole ex_cenv prim_of gc nv_make_tinfo Fnil ex_main) initial_fused (st, (ls, G)) (I64 1).
  Proof.
    destruct nv_make_tinfo_runs as (st0 & tinfo & _ & _ & _ & Hrun & _ & _ & (_ & _ & _ & Hk) & _).
    assert (HB0 : keys_below st0 nv_block_size) by (intros a Ha; apply Hk, Ha).
    set (ls0 := fst (snd initial_fused)).
    assert (Hs0 : snd initial_fused = (ls0, Maps.empty)) by reflexivity.
    rewrite Hs0 in Hrun.
    destruct (ex_global_init st0 ls0 nv_block_size HB0) as (st1 & G & Hglob & HGok & HB1);
      [unfold nv_block_size; lia|unfold nv_block_size; lia|].
    destruct (G_ok_main _ _ _ _ _ HGok) as (pm & Hpm).
    set (ctx := ctx_of (fun_table ex_cenv prim_of Fnil ex_main (gc_den gc) G)).
    destruct ls0 as [sf0 stk0] eqn:Els.
    destruct (ex_main_runs ctx tinfo st1 sf0 stk0 G (nv_block_size + 32) HB1) as (st3 & Hruns);
      [unfold nv_block_size; lia|unfold nv_block_size; lia|].
    exists st3, (sf0, stk0), G.
    unfold whole. eapply truns_bind; [exact Hrun|].
    unfold denote_with_runtime.
    eapply truns_bind; [exact Hglob|].
    eapply truns_bind; [apply addresses_run; exact HGok|].
    eapply truns_bind; [apply (libraries_run ex_cenv prim_of Fnil ex_main (gc_den gc)); exact HGok|].
    eapply truns_bind; [apply truns_gread, Hpm|].
    assert (Hknot : truns (denote_mcfg (fun_table ex_cenv prim_of Fnil ex_main (gc_den gc) G) (DTYPE_I 64)
                             (Ptr pm) [Ptr tinfo]) (st1, ((sf0, stk0), G)) (st3, ((sf0, stk0), G)) (inr (I64 1))).
    { unfold truns. rewrite denote_mcfg_unfold.
      rewrite (ctx_real_main ex_cenv prim_of Fnil ex_main (gc_den gc) G pm [Ptr tinfo] HGok Hpm). exact Hruns. }
    eapply truns_bind; [apply Hknot|].
    apply truns_ret.
  Qed.

  (** The compiled example program returns [1] (the representation of the
      nullary constructor with ordinal 0): the out-of-memory disjunct of
      [ex_correct] does not hold. *)
  Theorem ex_returns :
    exists st ls genv,
      returns (run_program nv_gc nv_make_tinfo (emitted ex_cenv prim_of ex_prog)) ((st, (ls, genv)), I64 1).
  Proof.
    unfold ex_prog. rewrite run_program_whole.
    destruct (ex_whole_runs nv_gc) as (st & ls & G & H). exists st, ls, G. exact H.
  Qed.

  Corollary ex_not_oom : ~ ends_in_oom (run_program nv_gc nv_make_tinfo (emitted ex_cenv prim_of ex_prog)).
  Proof.
    intros [k Hk]. destruct ex_returns as (st & ls & G & H). unfold returns in H.
    rewrite H in Hk. eapply eutt_Ret_Vis_abs; exact Hk.
  Qed.
End Ex.
