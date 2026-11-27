(** * End-to-end correctness of [CertiRocq_pipeline]

    This file states and proves the correctness of [CertiRocq_pipeline] (see [pipeline.v]), the
    part of CertiRocq's compiler going from a MetaRocq Template program to LambdaANF, in its
    direct-style (ANF) configuration. It composes:

    - the correctness of MetaRocq's erasure pipeline followed by CertiRocq's post-processing
      ([certirocq_erasure_pipeline], via MetaRocq's [Transform] framework);
    - the correspondence between MetaRocq's substitution-based evaluation of erased programs
      and CertiRocq's environment-based semantics [fuel_sem] ([eval_to_fuel_sem], through
      MetaRocq's step-indexed evaluation and [eval_SI_to_fuel_sem.v]);
    - the correctness of the ANF conversion ([metarocq_to_anf_correct] in [correctness.v]);
    - the correctness of the LambdaANF optimization pipeline ([anf_pipeline_whole_program_correct]
      in [LambdaANF/toplevel_theorems.v]).

    The main theorem is [CertiRocq_pipeline_correct]: if a well-typed Template program [p]
    evaluates to a value [v], and [CertiRocq_pipeline] successfully compiles it to a LambdaANF
    program, then this program evaluates to a value [v_tgt] that has the same observable
    structure as the value computed by the erased program, which is related to [v] by the
    observational relation of MetaRocq's erasure pipeline.

    The programs must not use axioms nor primitive arrays: this is ensured by the [check_axioms]
    and [check_wellformed] passes of the pipeline, so it follows from the pipeline's success.
    Conversely, the pipeline succeeds on well-typed programs whose erasure has no axioms nor
    primitive arrays ([CertiRocq_pipeline_total]); [CertiRocq_pipeline_total_correct] combines
    both results.

    For programs computing a value of a first-order inductive type,
    [CertiRocq_pipeline_firstorder] describes the value computed by the LambdaANF program: it is
    the source value, with parameters erased, singleton constructors unboxed and constructors
    mapped to their LambdaANF tags. It builds on MetaRocq's [ErasureFirstorder], and only covers
    the verified passes of the untyped erasure pipeline, without inductive mappings.

    Besides the assumptions of MetaRocq's erasure pipeline, the results depend on the correctness
    of [unforce_axioms_transformation] ([metarocq_pipeline.v]), whose obligations are admitted.
    The definition of [erase_program] ([pipeline.v]) also uses the axioms
    [assume_wellformed_inductives_mapping] and MetaRocq's
    [assume_that_we_only_erase_on_welltyped_programs] to build the precondition of erasure; the
    theorems take these properties as hypotheses, and do not depend on the choice of this
    precondition ([erase_program_run]). *)

From Stdlib Require Import ssreflect ssrbool.
From Equations Require Import Equations.
From Stdlib Require Import ZArith NArith List ProofIrrelevance.
Require Import Common.Common Common.compM Common.Pipeline_utils.
Require Import ExtLib.Structures.Monad.
From MetaRocq.Common Require Import Transform.
From MetaRocq.Erasure Require Import EAst EWellformed EProgram.
From MetaRocq.Erasure Require EFirstorder.
From MetaRocq.ErasurePlugin Require Import Erasure.
From MetaRocq.Utils Require Import utils.
From CertiRocq.LambdaBox_to_LambdaANF Require Import common fuel_sem anf_convert_env anf_correct
  anf_toplevel anf_scoping anf_cenv.
Require Import LambdaANF.term LambdaANF.state LambdaANF.eval LambdaANF.identifiers
  LambdaANF.term_util LambdaANF.rel_comp LambdaANF.bounds.
From CertiRocq Require Import metarocq_pipeline pipeline correctness.
From MetaRocq.TemplatePCUIC Require TemplateToPCUIC.
From MetaRocq.PCUIC Require PCUICTyping PCUICClassification PCUICFirstorder.
From MetaRocq.ErasurePlugin Require ErasureCorrectness.
From MetaRocq.ErasurePlugin.transforms Require RebuildWfEnv CoInductiveToInductive Unboxing
  ConstsToValues ImplementBox ImplementLazyForce.
From MetaRocq.Template Require Typing.
From MetaRocq.ErasurePlugin Require ErasureFirstorder.
From MetaRocq.ErasurePlugin Require Import CheckWellformed.
From MetaRocq.Erasure Require StepIndex.Values StepIndex.EvalStepIndex StepIndex.EvalToEvalSI.
From CertiRocq.LambdaBox_to_LambdaANF Require eval_SI_to_fuel_sem.

Import Monads.
Import MonadNotation.
Import ListNotations.
Import Transform.
Import EFirstorder (firstorder_evalue_block, firstorder_evalue_block_elim).
Import ErasureFirstorder (is_unboxable_ctor, unbox_fo, unbox_fo_constr, unbox_fo_tree, unbox_fo_ext, unbox_tree,
  is_unboxable_ctor_map, is_unboxable_ctor_consts_to_values, consts_to_values_tree,
  implement_lazy_force_tree, implement_box_tree, map_id_tree, obseq_compose_inv).

(** ** Constructor environments *)

(** [cenv_extends], [fresh_ctor_tags]: see [anf_cenv.v] *)

Lemma caseConsistent_extends cenv cenv' cl t :
  cenv_extends cenv cenv' -> caseConsistent cenv cl t -> caseConsistent cenv' cl t.
Proof.
  intros hext h. induction h; econstructor; eauto.
Qed.

(** LambdaANF evaluation is preserved by extension of the constructor environment, and does not
    depend on the trace resource. *)
Lemma bstep_fuel_transfer {cenv cenv' : ctor_env} {fuel trace trace' : Type}
  {Hf : @fuel_resource fuel} {Ht : @trace_resource trace} {Ht' : @trace_resource trace'} :
  cenv_extends cenv cenv' ->
  forall rho e c r t,
    @bstep_fuel cenv fuel Hf trace Ht rho e c r t ->
    exists t', @bstep_fuel cenv' fuel Hf trace' Ht' rho e c r t'.
Proof.
  intros hext rho e c r t hev.
  set (P := fun rho e c r (_ : trace) => exists t', @bstep cenv' fuel Hf trace' Ht' rho e c r t').
  set (Q := fun rho e c r (_ : trace) => exists t', @bstep_fuel cenv' fuel Hf trace' Ht' rho e c r t').
  revert rho e c r t hev.
  apply (@bstep_fuel_ind' cenv fuel Hf trace Ht P Q); unfold P, Q; clear P Q; intros;
    repeat match goal with H : exists _, _ |- _ => destruct H end;
    try solve [eexists; econstructor; eauto using caseConsistent_extends].
Qed.

(** ** Observations *)

(** Erased values, as computed by MetaRocq's substitution-based evaluation, can be read back from
    CertiRocq's environment-based values ([fs_value_to_term]): this is the composition of
    MetaRocq's [StepIndex.Values.term_of_val] and of the inverse of
    [eval_SI_to_fuel_sem.convert_vals] (see [fs_value_to_term_convert]). *)

Definition prim_val_of_primitive_value (p : primitive_value) : EPrimitive.prim_val EAst.term :=
  match p with
  | existT t v =>
    match t return AstCommon.prim_value t -> EPrimitive.prim_val EAst.term with
    | AstCommon.primInt => fun i => EPrimitive.prim_int i
    | AstCommon.primFloat => fun f => EPrimitive.prim_float f
    | AstCommon.primString => fun s => EPrimitive.prim_string s
    end v
  end.

Fixpoint fs_value_to_term (v : fuel_sem.value) : EAst.term :=
  match v with
  | Con_v (ind, c) vs => EAst.tConstruct ind (N.to_nat c) (map fs_value_to_term vs)
  | Clos_v rho na b => ECSubst.substl (map fs_value_to_term rho) (EAst.tLambda na b)
  | ClosFix_v rho mfix idx => ECSubst.substl (map fs_value_to_term rho) (EAst.tFix mfix idx)
  | Prim_v p => EAst.tPrim (prim_val_of_primitive_value p)
  end.

Definition is_function_value (t : EAst.term) : Prop :=
  match t with
  | EAst.tLambda _ _ | EAst.tFix _ _ => True
  | _ => False
  end.

(** The observable structure of a (closure-converted) LambdaANF value [v] with respect to an
    erased value [t]: constructors are mapped to their tags, functions to closures, and
    primitive values are preserved. *)
Inductive obs_val (tgm : conId_map) : EAst.term -> val -> Prop :=
| obs_constr ind c args tag vs :
    dcon_to_tag (dcon_of_con ind c) tgm = Some tag ->
    Forall2 (obs_val tgm) args vs ->
    obs_val tgm (EAst.tConstruct ind c args) (Vconstr tag vs)
| obs_fun t clo_tag rho fds f env :
    is_function_value t ->
    obs_val tgm t (Vconstr clo_tag [Vfun rho fds f; env])
| obs_prim p :
    obs_val tgm (EAst.tPrim (prim_val_of_primitive_value p)) (Vprim p).

Lemma substl_lambda l na b :
  is_function_value (ECSubst.substl l (EAst.tLambda na b)).
Proof.
  induction l in b |- *; cbn => //; apply IHl.
Qed.

Lemma substl_fix l mfix idx :
  is_function_value (ECSubst.substl l (EAst.tFix mfix idx)).
Proof.
  induction l in mfix |- *; cbn => //; apply IHl.
Qed.

Lemma obs_val_compose tgm v_src v_anf v_tgt :
  anf_toplevel.value_ref tgm v_src v_anf ->
  value_ref_cc v_anf v_tgt ->
  obs_val tgm (fs_value_to_term v_src) v_tgt.
Proof.
  induction v_src using value_ind' in v_anf, v_tgt |- *; intros h1 h2.
  - destruct dc as [ind c]. destruct v_anf; cbn in h1; try contradiction.
    destruct h1 as [htag hvs]. destruct v_tgt; cbn in h2; try contradiction.
    destruct h2 as [<- hvs']. cbn.
    constructor.
    { unfold dcon_of_con. now rewrite Nnat.N2Nat.id. }
    clear htag. revert l l0 hvs hvs'.
    induction H as [|v vs hv _ IH]; intros l1 l2 h1 h2.
    + inversion h1; subst. inversion h2; subst. apply Forall2_nil.
    + inversion h1 as [|? a ? l1' ha hl1]; subst.
      inversion h2 as [|? b ? l2' hb hl2]; subst. cbn.
      apply Forall2_cons; [|now eauto].
      eapply hv; [now apply anf_toplevel.value_ref_eq | now apply value_ref_cc_eq].
  - destruct v_anf; cbn in h1; try contradiction.
    destruct v_tgt; cbn in h2; try contradiction.
    repeat (match type of h2 with context [match ?x with _ => _ end] => destruct x end;
            try contradiction).
    constructor. apply substl_lambda.
  - destruct v_anf; cbn in h1; try contradiction.
    destruct v_tgt; cbn in h2; try contradiction.
    repeat (match type of h2 with context [match ?x with _ => _ end] => destruct x end;
            try contradiction).
    constructor. apply substl_fix.
  - destruct v_anf; cbn in h1; try contradiction. subst.
    destruct v_tgt; cbn in h2; try contradiction. subst. constructor.
Qed.

(** ** From MetaRocq's evaluation to [fuel_sem] *)

(** [fs_value_to_term] mirrors MetaRocq's [term_of_val] on the values produced by the conversion
    of step-indexed values to [fuel_sem] values. *)
Lemma fs_value_to_term_convert {efl : EEnvFlags} hBox hCofix hLazy hPrimArray Σ
  (w : StepIndex.Values.value) h :
  fs_value_to_term
    (@eval_SI_to_fuel_sem.convert_vals efl hBox hCofix hLazy hPrimArray Σ w h) =
  StepIndex.Values.term_of_val w.
Proof.
  have hlist : forall (l : list StepIndex.Values.value),
    All_Forall.All (fun w => forall h,
      fs_value_to_term (@eval_SI_to_fuel_sem.convert_vals efl hBox hCofix hLazy hPrimArray Σ w h) =
      StepIndex.Values.term_of_val w) l ->
    forall h, map fs_value_to_term (eval_SI_to_fuel_sem.convert_list' Σ
      (@eval_SI_to_fuel_sem.convert_vals efl hBox hCofix hLazy hPrimArray Σ) l h) =
      map StepIndex.Values.term_of_val l.
  { induction 1 as [|x l hx hl IH]; intros h'; cbn; [reflexivity|]. f_equal; [apply hx|apply IH]. }
  induction w using StepIndex.Values.value_rect in h |- *; cbn.
  - exfalso. move: h => /=. rewrite hBox. discriminate.
  - rewrite Nat2N.id. f_equal. now apply hlist.
  - rewrite (hlist _ X). reflexivity.
  - rewrite (hlist _ X). reflexivity.
  - exfalso. move: h => /=. rewrite hCofix. discriminate.
  - destruct p as [t m]; destruct m; cbn; try reflexivity.
    exfalso. move: h => /=. rewrite /MetaRocq.Erasure.StepIndex.Utils.has_prim /= hPrimArray.
    discriminate.
  - exfalso. move: h => /=. rewrite hLazy. discriminate.
Qed.

(** Correspondence between MetaRocq's substitution-based call-by-value evaluation of erased
    programs, and CertiRocq's environment-based semantics [fuel_sem], for the erased programs
    produced by MetaRocq's pipeline. This is the composition of:
    - [eval_eval_SI] (EWcbvEval to MetaRocq's step-indexed, environment-based evaluation
      relation), and
    - [evalSI_to_fuel_sem] (the step-indexed evaluation to [fuel_sem]). *)
Lemma eval_to_fuel_sem (Σ : EAst.global_context) (t v : EAst.term) :
    @wf_glob (certirocq_flags env_flags) Σ ->
    @wellformed (certirocq_flags env_flags) Σ 0 t ->
    @EWcbvEval.eval final_wcbv_flags Σ t v ->
    exists (v' : fuel_sem.value) (f tr : nat),
      @eval_env_step nat LambdaBox_resource_fuel LambdaBox_resource_trace Σ [] t (Val v') f tr /\
      v = fs_value_to_term v'.
Proof.
  intros hwfΣ hwft hev.
  destruct (@StepIndex.EvalToEvalSI.eval_eval_SI (certirocq_flags env_flags) final_wcbv_flags
    Σ [] t v t eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl hwfΣ hwft eq_refl hev
    eq_refl) as (n & w & heq & hsi).
  have hwfw : @StepIndex.Values.wellformed_val (certirocq_flags env_flags) Σ w = true.
  { exact (@StepIndex.EvalStepIndex.eval_SI_wellformed_val (certirocq_flags env_flags) Σ [] t w n
      eq_refl eq_refl eq_refl
      hwfΣ eq_refl hwft hsi). }
  have [f [tr hstep]] := @eval_SI_to_fuel_sem.evalSI_to_fuel_sem (certirocq_flags env_flags)
    eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl Σ hwfΣ nat
    LambdaBox_resource_fuel LambdaBox_resource_trace [] t w n eq_refl hwfw eq_refl hwft hsi.
  eexists _, f, tr. split; [exact hstep|].
  by rewrite fs_value_to_term_convert heq.
Qed.

(** The program produced by ANF conversion is closed and has unique bindings *)
Lemma convert_top_anf_closed_unique_bindings func_tag default_tag default_itag next_id
  (Σ : EAst.global_context) e e_tgt comp_d :
  wf_eprogram (certirocq_flags env_flags) (Σ, e) ->
  let ie := inductive_env_east Σ in
  anf.convert_top_anf func_tag default_tag (M.empty _) default_itag next_id []
    (fun _ => None) ie (List.rev Σ) e = (compM.Ret e_tgt, comp_d) ->
  closed_exp e_tgt /\ unique_bindings e_tgt.
Proof.
  intros wf ie hcvt.
  destruct (anf_corresp.convert_top_anf_corresp func_tag default_tag default_itag ie Σ
    (efl := certirocq_flags env_flags) eq_refl (M.empty _) [] (proj1 wf)
    eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl (fun _ => eq_refl) (convert_env_reg _ _ _)
    next_id e e_tgt comp_d (proj2 wf) hcvt)
    as (cm & Sg & S' & C_env & C & r & hglob & hmain & ->).
  exact: anf_cvt_program_scoping hglob hmain.
Qed.

(** ** Inversion of the pipeline *)

(** Projections of LambdaANF programs: the constructor environment, the next free constructor
    tag, the evaluation environment and the LambdaANF expression *)
Definition anf_cenv (r : LambdaANF_FullTerm) : ctor_env := r.1.1.1.1.1.1.2.
Definition anf_ctag (r : LambdaANF_FullTerm) : ctor_tag := r.1.1.1.1.1.2.
Definition anf_env (r : LambdaANF_FullTerm) : eval.env := r.1.2.
Definition anf_exp (r : LambdaANF_FullTerm) : exp := r.2.

(** The LambdaANF program built from the result of ANF conversion ([compile_LambdaANF_ANF]) *)
Definition anf_program_of (e : exp) (data : comp_data) : LambdaANF_FullTerm :=
  (M.empty _, M.empty _, state.cenv data, nect_ctor_tag data, next_ind_tag data, state.nenv data,
   state.fenv data, M.empty _, e).

Lemma CertiRocq_pipeline_inv nid dbg p o w r w' :
  direct o = true ->
  runState (CertiRocq_pipeline nid [] dbg p) o w = (compM.Ret r, w') ->
  let p_er := erase_program [] (erasure_config o) (Pipeline_utils.inductives_mapping o) p in
  let ie := inductive_env_east p_er.1 in
  find_axioms [] [] p_er.1 = [] /\
  check_wf_eprogram (certirocq_check_flags false) p_er /\
  exists e_anf data log,
    anf.convert_top_anf fun_fun_tag default_ctor_tag (M.empty _) default_ind_tag nid []
      (fun _ => None) ie (List.rev p_er.1) p_er.2 = (compM.Ret e_anf, data) /\
    run_anf_pipeline nid (make_anf_options o) (anf_program_of e_anf data) = (compM.Ret r, log).
Proof.
  intros hdirect heq.
  unfold CertiRocq_pipeline, compile_LambdaBoxEAst, check_axioms, check_wellformed,
    Pipeline_utils.LiftCertiRocqTrans, Pipeline_utils.debug_msg, Pipeline_utils.get_options,
    compile_LambdaANF_ANF, compile_LambdaANF_debug, compile_LambdaANF,
    Pipeline_utils.LiftErrorCertiRocqTrans, Pipeline_utils.LiftErrorLogCertiRocqTrans,
    Pipeline_utils.timePhase_opt, AstCommon.timePhase in heq.
  set (p_er := erase_program _ _ _ _) in *.
  set (ie := inductive_env_east p_er.1).
  cbv beta iota zeta delta [Monad.bind Monad.ret compM.MonadErrorT compM.MonadState compM.ask
    compM.get compM.put compM.failwith Pipeline_utils.ret compM.runState compM.compM compM.errorT
    debug_msg get_options] in heq.
  rewrite hdirect in heq. destruct w.
  repeat (cbv beta iota zeta in heq; fold p_er ie in heq;
    match type of heq with
    | context [if dbg then _ else _] => destruct dbg
    | context [debug o] => destruct (debug o)
    | context [Pipeline_utils.time o] => destruct (Pipeline_utils.time o)
    | context [find_axioms ?a ?b ?c] => destruct (find_axioms a b c) eqn:hax; [|discriminate heq]
    | context [check_wf_eprogram ?f ?p] =>
      destruct (check_wf_eprogram f p) eqn:hwf; [|discriminate heq]
    | context [anf.convert_top_anf ?a ?b ?c ?d ?e ?f ?g ?h ?i ?j] =>
      destruct (anf.convert_top_anf a b c d e f g h i j) as [[|e_anf] []] eqn:hcvt;
        [discriminate heq|]
    | context [run_anf_pipeline ?a ?b ?c] =>
      destruct (run_anf_pipeline a b c) as [[|r'] log'] eqn:hrun; [discriminate heq|]
    end).
  all:cbv beta iota zeta in heq; injection heq as h1 _; subst r.
  all:split; [exact hax|split; [exact hwf|]].
  all:do 3 eexists; split; [exact hcvt|exact hrun].
Qed.

Lemma run_anf_pipeline_inv nid opts t r log :
  run_anf_pipeline nid opts t = (compM.Ret r, log) ->
  exists c e' c',
    state.next_var c = (max_var (anf_exp t) 1 + 1)%positive /\
    state.cenv c = anf_cenv t /\ nect_ctor_tag c = anf_ctag t /\
    anf_pipeline nid opts (anf_exp t) c = (compM.Ret e', c') /\
    anf_cenv r = state.cenv c' /\ anf_env r = M.empty _ /\ anf_exp r = e'.
Proof.
  destruct t as [[[[[[[[pr penv] cenv] ctag] itag] nenv] fenv] rho] e].
  unfold run_anf_pipeline.
  set (c := pack_data _ _ _ _ _ _ _ _ _).
  destruct (anf_pipeline nid opts e c) as [[|e'] [? ? ? ? ? ? ? ? ?]] eqn:hrun => //.
  intros [= <-]. exists c. do 2 eexists. split; [reflexivity|]. split; [reflexivity|].
  split; [reflexivity|]. split; [exact hrun|]. now repeat split.
Qed.

(** ** Erasure *)

Notation erasure_pipeline econf := (@certirocq_erasure_pipeline fake_guard_impl [] econf).

Lemma erase_program_run econf imap p (pr : Transform.pre (erasure_pipeline econf) (imap, p)) :
  erase_program [] econf imap p = Transform.transform (erasure_pipeline econf) (imap, p) pr.
Proof.
  unfold erase_program, run_erase_program, Transform.run, Transform.time. cbn [map].
  f_equal. apply proof_irrelevance.
Qed.

Lemma erasure_pipeline_post econf p :
  Transform.post (erasure_pipeline econf) p ->
  Transform.post (certirocq_post_metarocq_pipeline [] econf) p.
Proof.
  unfold certirocq_erasure_pipeline. now destruct enable_typed_erasure.
Qed.

(** The precondition of the erasure pipeline: the program is well-typed. Normalization is
    a standard assumption of MetaRocq ([PCUICSN.normalization]). *)
Lemma erasure_pipeline_pre econf imap p :
  wf_template_inductives_mapping p.1 imap ->
  ∥ @TemplateProgram.wt_template_program config.extraction_checker_flags p ∥ ->
  Transform.pre (erasure_pipeline econf) (imap, p).
Proof.
  intros hmap hwt. apply certirocq_erasure_pipeline_pre.
  split; [exact hmap|]. split; [exact hwt|].
  cbv [PCUICWeakeningEnvSN.normalizationInAdjustUniversesIn].
  pose proof @PCUICSN.normalization.
  split; typeclasses eauto.
Qed.

(** ** The end-to-end theorem *)

(** The erased program computed by the pipeline *)
Definition erased_program (o : Options) (p : Ast.Env.program) : eprogram :=
  erase_program [] (erasure_config o) (Pipeline_utils.inductives_mapping o) p.

(** The map from (erased) constructors to LambdaANF constructor tags *)
Definition erased_tag_map (o : Options) (p : Ast.Env.program) : conId_map :=
  top_tgm default_ctor_tag default_ind_tag (inductive_env_east (erased_program o p).1).

(** The observational relation of the erasure pipeline, relating the values of the source
    and erased programs *)
Definition erasure_obseq (o : Options) (p : Ast.Env.program) (v : Ast.term) (v' : EAst.term) :=
  exists pr, Transform.obseq (erasure_pipeline (erasure_config o))
    (Pipeline_utils.inductives_mapping o, p) pr (erased_program o p) v v'.

Theorem CertiRocq_pipeline_correct (next_id : positive) (dbg : bool) (o : Options)
  (p : Ast.Env.program) w w' r :
  (* The source program is well-typed *)
  wf_template_inductives_mapping p.1 (Pipeline_utils.inductives_mapping o) ->
  ∥ @TemplateProgram.wt_template_program config.extraction_checker_flags p ∥ ->
  (* We use the ANF translation, and do not register primitives *)
  direct o = true ->
  (* The pipeline succeeds *)
  runState (CertiRocq_pipeline next_id [] dbg p) o w = (compM.Ret r, w') ->
  forall v,
    eval_template_program_mapping (Pipeline_utils.inductives_mapping o, p) v ->
    exists v_er v_tgt c t,
      erasure_obseq o p v v_er /\
      eval_eprogram final_wcbv_flags (erased_program o p) v_er /\
      @bstep_fuel (anf_cenv r) nat fuel_res (nat * nat) trace_res (anf_env r) (anf_exp r) c
        (Res v_tgt) t /\
      obs_val (erased_tag_map o p) v_er v_tgt.
Proof.
  intros hmap hwt hdirect hrun v hev.
  have pre := erasure_pipeline_pre (erasure_config o) _ _ hmap hwt.
  (* Inversion of the pipeline *)
  move: (CertiRocq_pipeline_inv _ _ _ _ _ _ _ hdirect hrun).
  rewrite -/(erased_program o p).
  set (p_er := erased_program o p). set (tgm := erased_tag_map o p).
  intros (_ & hwf & e_anf & data & log & hcvt & hrun').
  apply check_wf_eprogram_spec in hwf. rewrite certirocq_check_flags_false in hwf.
  (* Erasure *)
  have hpost : Transform.post (certirocq_post_metarocq_pipeline [] (erasure_config o)) p_er.
  { apply erasure_pipeline_post. rewrite /p_er /erased_program (erase_program_run _ _ _ pre).
    apply Transform.correctness. }
  destruct (Transform.preservation (erasure_pipeline (erasure_config o)) _ v pre hev)
    as (v_er & hev_er & hobs).
  rewrite -(erase_program_run _ _ _ pre) -/(erased_program o p) -/p_er in hev_er hobs.
  exists v_er.
  (* From MetaRocq's semantics to fuel_sem *)
  have [hev_er'] := hev_er.
  destruct (eval_to_fuel_sem p_er.1 p_er.2 v_er (proj1 hwf) (proj2 hwf) hev_er')
    as (v_src & f & tr & hev_src & ->).
  apply fuel_sem.eval_step in hev_src.
  (* ANF conversion *)
  destruct (metarocq_to_anf_correct fun_fun_tag kon_fun_tag default_ctor_tag default_ind_tag
              next_id (erasure_config o) p_er hpost hwf _ _ hcvt) as [M href].
  destruct (href _ _ _ hev_src) as (v_anf & c_anf & hev_anf & _ & hv_anf).
  destruct (convert_top_anf_closed_unique_bindings _ _ _ _ p_er.1 p_er.2 _ _ hwf hcvt)
    as [hclosed huniq].
  (* LambdaANF pipeline *)
  apply run_anf_pipeline_inv in hrun'
    as (c & e' & c' & hnv & hc & hctag & hanf & -> & -> & ->).
  cbn in hnv, hc, hctag, hanf.
  destruct (convert_top_anf_cenv _ _ _ _ _ _ _ _ _ _ _ _ hcvt) as (hcenv0 & htags & hlt).
  rewrite -hc -hctag in htags hlt. rewrite -hc in hcenv0.
  have hok := cenv_ok_init c htags hlt.
  have hws : identifiers.well_scoped e_anf.
  { split => //. eapply Ensembles_util.Disjoint_Included_r; [apply hclosed|].
    apply Ensembles_util.Disjoint_Empty_set_r. }
  destruct (anf_pipeline_whole_program_correct (top_cenv default_ctor_tag default_ind_tag
              (inductive_env_east p_er.1)) next_id (make_anf_options o) e_anf c hclosed hws)
    as (e'' & c'' & hanf' & hterm & _).
  { rewrite hnv. apply Pos.lt_add_r. }
  rewrite hanf in hanf'. injection hanf' as <- <-.
  apply (@bstep_fuel_transfer _ _ _ _ (nat * nat) _ _ trace_res (fun _ _ h => h)) in hev_anf
    as [t_anf hev_anf].
  destruct (hterm _ _ _ hev_anf) as (v_tgt & c_tgt & t_tgt & hev_tgt & hv_tgt).
  have hext : cenv_extends (top_cenv default_ctor_tag default_ind_tag (inductive_env_east p_er.1))
    (state.cenv c').
  { rewrite -hcenv0. exact (anf_pipeline_cenv_extends _ _ _ _ _ _ hok hanf). }
  apply (bstep_fuel_transfer (trace' := nat * nat) hext) in hev_tgt as [t' hev_tgt].
  exists v_tgt, c_tgt, t'. split; [now exists pre|]. split => //. split => //.
  eapply obs_val_compose; eauto.
Qed.

(** ** Totality: the pipeline does not fail on programs without axioms nor primitive arrays *)

Lemma find_axioms_no_axioms {efl : EEnvFlags} (Σ : EAst.global_context) acc :
  has_axioms = false -> wf_glob Σ -> find_axioms [] acc Σ = acc.
Proof.
  intros hax wfΣ. induction wfΣ as [|kn d Σ _ IH hd _] in acc |- *; cbn => //.
  destruct d as [[[]]|]; cbn in hd |- * => //. now rewrite hax in hd.
Qed.

Lemma run_anf_pipeline_total nid opts t :
  closed_exp (anf_exp t) -> unique_bindings (anf_exp t) ->
  exists r log, run_anf_pipeline nid opts t = (compM.Ret r, log).
Proof.
  destruct t as [[[[[[[[pr penv] cenv] ctag] itag] nenv] fenv] rho] e].
  rewrite /anf_exp /=. intros hclosed huniq.
  have hws : identifiers.well_scoped e.
  { split => //. eapply Ensembles_util.Disjoint_Included_r; [apply hclosed|].
    apply Ensembles_util.Disjoint_Empty_set_r. }
  unfold run_anf_pipeline.
  set (c := pack_data _ _ _ _ _ _ _ _ _).
  destruct (anf_pipeline_whole_program_correct cenv nid opts e c hclosed hws)
    as (e' & c' & -> & _).
  { apply Pos.lt_add_r. }
  destruct c'. now do 2 eexists.
Qed.

(** If all the checks and translations succeed, so does the pipeline *)
Lemma CertiRocq_pipeline_succeeds nid dbg p o w :
  direct o = true ->
  let p_er := erase_program [] (erasure_config o) (Pipeline_utils.inductives_mapping o) p in
  let ie := inductive_env_east p_er.1 in
  find_axioms [] [] p_er.1 = [] ->
  check_wf_eprogram (certirocq_check_flags false) p_er ->
  forall e_anf data,
    anf.convert_top_anf fun_fun_tag default_ctor_tag (M.empty _) default_ind_tag nid []
      (fun _ => None) ie (List.rev p_er.1) p_er.2 = (compM.Ret e_anf, data) ->
  forall r log,
    run_anf_pipeline nid (make_anf_options o) (anf_program_of e_anf data) = (compM.Ret r, log) ->
    exists w', runState (CertiRocq_pipeline nid [] dbg p) o w = (compM.Ret r, w').
Proof.
  intros hdirect p_er ie hax hwf e_anf data hcvt r log hrun.
  destruct data. unfold anf_program_of in hrun; cbn -[run_anf_pipeline] in hrun.
  unfold CertiRocq_pipeline, compile_LambdaBoxEAst, check_axioms, check_wellformed,
    Pipeline_utils.LiftCertiRocqTrans, Pipeline_utils.debug_msg, Pipeline_utils.get_options,
    compile_LambdaANF_ANF, compile_LambdaANF_debug, compile_LambdaANF,
    Pipeline_utils.LiftErrorCertiRocqTrans, Pipeline_utils.LiftErrorLogCertiRocqTrans,
    Pipeline_utils.timePhase_opt, AstCommon.timePhase.
  fold p_er. fold ie.
  cbv beta iota zeta delta [Monad.bind Monad.ret compM.MonadErrorT compM.MonadState compM.ask
    compM.get compM.put compM.failwith Pipeline_utils.ret compM.runState compM.compM compM.errorT
    debug_msg get_options].
  rewrite hdirect. destruct w.
  repeat (cbv beta iota zeta; fold p_er ie; rewrite ?hax ?hwf ?hcvt ?hrun;
    match goal with
    | |- context [if dbg then _ else _] => destruct dbg
    | |- context [debug o] => destruct (debug o)
    | |- context [Pipeline_utils.time o] => destruct (Pipeline_utils.time o)
    end).
  all:cbv beta iota zeta; rewrite ?hcvt ?hrun; cbv beta iota zeta.
  all:now eexists.
Qed.

(** The pipeline succeeds on well-typed programs whose erasure has no axioms nor primitive
    arrays. *)
Theorem CertiRocq_pipeline_total (next_id : positive) (dbg : bool) (o : Options)
  (p : Ast.Env.program) w :
  (* The source program is well-typed *)
  wf_template_inductives_mapping p.1 (Pipeline_utils.inductives_mapping o) ->
  ∥ @TemplateProgram.wt_template_program config.extraction_checker_flags p ∥ ->
  (* We use the ANF translation, and do not register primitives *)
  direct o = true ->
  (* The erased program has no axioms nor primitive arrays *)
  wf_eprogram (certirocq_flags env_flags) (erased_program o p) ->
  exists r w', runState (CertiRocq_pipeline next_id [] dbg p) o w = (compM.Ret r, w').
Proof.
  intros hmap hwt hdirect hwf.
  have pre := erasure_pipeline_pre (erasure_config o) _ _ hmap hwt.
  set (p_er := erased_program o p) in *.
  have hpost : Transform.post (certirocq_post_metarocq_pipeline [] (erasure_config o)) p_er.
  { apply erasure_pipeline_post. rewrite /p_er /erased_program (erase_program_run _ _ _ pre).
    apply Transform.correctness. }
  destruct (metarocq_to_anf_total fun_fun_tag kon_fun_tag default_ctor_tag default_ind_tag
              next_id (erasure_config o) p_er hpost hwf) as (e_anf & data & hcvt & _).
  destruct (convert_top_anf_closed_unique_bindings _ _ _ _ p_er.1 p_er.2 _ _ hwf hcvt)
    as [hclosed huniq].
  destruct (run_anf_pipeline_total next_id (make_anf_options o) (anf_program_of e_anf data)
              hclosed huniq) as (r & rlog & hrun).
  exists r. eapply CertiRocq_pipeline_succeeds; tea.
  - apply (@find_axioms_no_axioms (certirocq_flags env_flags)); [reflexivity|apply hwf].
  - rewrite certirocq_check_flags_false. now apply check_wf_eprogram_complete.
Qed.

(** Totality and correctness together: on well-typed programs without axioms nor primitive
    arrays, the pipeline produces a LambdaANF program that refines the source program. *)
Corollary CertiRocq_pipeline_total_correct (next_id : positive) (dbg : bool) (o : Options)
  (p : Ast.Env.program) w :
  wf_template_inductives_mapping p.1 (Pipeline_utils.inductives_mapping o) ->
  ∥ @TemplateProgram.wt_template_program config.extraction_checker_flags p ∥ ->
  direct o = true ->
  wf_eprogram (certirocq_flags env_flags) (erased_program o p) ->
  exists r w',
    runState (CertiRocq_pipeline next_id [] dbg p) o w = (compM.Ret r, w') /\
    forall v,
      eval_template_program_mapping (Pipeline_utils.inductives_mapping o, p) v ->
      exists v_er v_tgt c t,
        erasure_obseq o p v v_er /\
        eval_eprogram final_wcbv_flags (erased_program o p) v_er /\
        @bstep_fuel (anf_cenv r) nat fuel_res (nat * nat) trace_res (anf_env r) (anf_exp r) c
          (Res v_tgt) t /\
        obs_val (erased_tag_map o p) v_er v_tgt.
Proof.
  intros hmap hwt hdirect hwf.
  destruct (CertiRocq_pipeline_total next_id dbg o p w hmap hwt hdirect hwf) as (r & w' & hrun).
  exists r, w'. split => //.
  now eapply CertiRocq_pipeline_correct.
Qed.

(** ** First-order results

    For programs computing a value of a first-order inductive type (in the sense of
    [ErasureFirstorder.firstorder_ind], the Template version of
    [PCUICFirstorder.firstorder_ind]), the value computed by the LambdaANF program is the value
    computed by the source program: a tree of constructors, with parameters erased (as in
    MetaRocq's [compile_value_box]), singleton constructors unboxed (as in [EUnboxing.unbox],
    see [unbox_fo]) and constructors mapped to their LambdaANF tags. *)

(** The PCUIC translation of the source program *)
Definition pcuic_env (p : Ast.Env.program) : PCUICAst.PCUICEnvironment.global_env :=
  PCUICProgram.trans_env_env (TemplateToPCUIC.trans_global_env p.1).

Definition pcuic_term (p : Ast.Env.program) (t : Ast.term) : PCUICAst.term :=
  TemplateToPCUIC.trans (TemplateToPCUIC.trans_global_env p.1) t.

(** An erased first-order value and the LambdaANF value representing it: the constructors
    unboxed by [EUnboxing] in [Σ] are skipped, the others are mapped to their tags in [tgm] *)
Inductive fo_value_ref (Σ : EAst.global_context) (tgm : conId_map) : EAst.term -> val -> Prop :=
| fo_ref_unboxed ind c a v :
    is_unboxable_ctor Σ ind c ->
    fo_value_ref Σ tgm a v ->
    fo_value_ref Σ tgm (EAst.tConstruct ind c [a]) v
| fo_ref_constr ind c args tag vs :
    ~~ (is_unboxable_ctor Σ ind c && (#|args| =? 1)%nat) ->
    dcon_to_tag (dcon_of_con ind c) tgm = Some tag ->
    Forall2 (fo_value_ref Σ tgm) args vs ->
    fo_value_ref Σ tgm (EAst.tConstruct ind c args) (Vconstr tag vs).

Lemma obs_val_unbox_fo Σ tgm Σw :
  forall t, firstorder_evalue_block Σw t ->
  forall v, obs_val tgm (unbox_fo Σ t) v -> fo_value_ref Σ tgm t v.
Proof.
  fix IH 2. intros t [ind c args hl hargs] v hobs.
  destruct (is_unboxable_ctor Σ ind c && (#|args| =? 1)%nat) eqn:hu.
  - move/andP: hu => [hunb /Nat.eqb_eq hlen]. destruct args as [|a []] => //.
    cbn in hobs; rewrite hunb in hobs. inversion hargs; subst. eapply fo_ref_unboxed; eauto.
  - rewrite unbox_fo_constr ?hu // in hobs.
    inversion hobs as [? ? ? tag vs htag hvs| |]; subst; cbn in *; try contradiction.
    eapply fo_ref_constr; [now rewrite hu|exact htag|].
    clear -IH hargs hvs. revert vs hvs.
    refine ((fix aux l (hl : Forall (firstorder_evalue_block Σw) l) {struct hl} :
      forall vs, Forall2 (obs_val tgm) (map (unbox_fo Σ) l) vs ->
        Forall2 (fo_value_ref Σ tgm) l vs := _) _ hargs).
    destruct hl as [|x l hx hl]; intros vs hvs; inversion hvs; subst; constructor; eauto.
Qed.

(** *** The post-erasure passes on first-order values *)

Lemma unforce_axioms_tree extracted Σ Σw t :
  firstorder_evalue_block Σw t -> unforce_axioms extracted Σ t = t.
Proof.
  induction 1 using firstorder_evalue_block_elim. cbn. f_equal. now apply map_id_tree.
Qed.

Lemma is_unboxable_ctor_unforce_axioms extracted Σ ind c :
  is_unboxable_ctor (unforce_axioms_env extracted Σ) ind c = is_unboxable_ctor Σ ind c.
Proof.
  rewrite /unforce_axioms_env.
  apply (is_unboxable_ctor_map (fun d => match d with
    | EAst.ConstantDecl cb =>
      EAst.ConstantDecl
        {| EAst.cst_body := option_map (unforce_axioms extracted Σ) (EAst.cst_body cb) |}
    | EAst.InductiveDecl i => EAst.InductiveDecl i end)).
  by case.
Qed.

(** Without unsafe passes, [certirocq_post_metarocq_pipeline] maps a first-order value to its
    unboxing. The environment [Σw] in which the value is first-order is arbitrary: the passes
    only depend on the shape of the value. *)
Lemma post_pipeline_firstorder econf (p : eprogram) pr p' Σw v v' :
  enable_unsafe econf = no_unsafe_passes ->
  firstorder_evalue_block Σw v ->
  Transform.obseq (certirocq_post_metarocq_pipeline [] econf) p pr p' v v' ->
  v' = unbox_fo (Transform.transform (certirocq_post_metarocq_pipeline [] econf) p pr).1 v.
Proof.
  destruct econf as [unsafe ? ? ? ? ?]. intros hunsafe htree. cbn in hunsafe. subst unsafe.
  unfold certirocq_post_metarocq_pipeline in pr |- *.
  intros obs.
  repeat (apply obseq_compose_inv in obs as (? & obs & ?)).
  cbn [Transform.obseq RebuildWfEnv.rebuild_wf_env_transform
       CoInductiveToInductive.coinductive_to_inductive_transformation Unboxing.unbox_transformation
       ETransform.optional_self_transform ConstsToValues.consts_to_values_transformation
       unforce_axioms_transformation ImplementLazyForce.implement_lazy_force_transformation
       ImplementBox.implement_box_transformation Erasure.no_unsafe_passes Erasure.make_unsafe_passes
       Erasure.inductives_extraction Erasure.betared Erasure.enable_unsafe] in *.
  subst.
  (* The value: only unboxing changes the tree *)
  rewrite (unbox_tree _ _ _ htree).
  match goal with |- context [unbox_fo ?Σu ?t] => have htree' := unbox_fo_tree _ Σu t htree end.
  rewrite (consts_to_values_tree _ _ htree') (unforce_axioms_tree _ _ _ _ htree')
    (implement_lazy_force_tree _ _ htree') (implement_box_tree _ _ htree').
  (* The environment: the later passes do not change the constructors *)
  apply: (unbox_fo_ext _ _ Σw) => // ind c.
  cbn [Transform.transform Transform.compose Transform.run Transform.time fst
       ImplementBox.implement_box_transformation ImplementLazyForce.implement_lazy_force_transformation
       unforce_axioms_transformation ConstsToValues.consts_to_values_transformation
       Unboxing.unbox_transformation EImplementBox.implement_box_program
       EImplementLazyForce.implement_lazy_force_program unforce_axioms_program
       EConstantsToValues.consts_to_values_program EUnboxing.unbox_program].
  rewrite /EImplementBox.implement_box_env
    (is_unboxable_ctor_map EImplementBox.implement_box_decl); [|by case].
  rewrite /EImplementLazyForce.implement_lazy_force_env
    (is_unboxable_ctor_map EImplementLazyForce.implement_lazy_force_decl); [|by case].
  rewrite is_unboxable_ctor_unforce_axioms is_unboxable_ctor_consts_to_values.
  rewrite /EUnboxing.unbox_env (is_unboxable_ctor_map (EUnboxing.unbox_decl _)); [|by case].
  reflexivity.
Qed.

(** *** MetaRocq's erasure pipeline on first-order values *)

Notation erasure_pipeline_mapping econf :=
  (@Erasure.erasure_pipeline_mapping fake_guard_impl econf).

(** MetaRocq's untyped erasure pipeline, without inductive mappings, maps a first-order value
    to its tree of constructors (with parameters erased), which is a first-order value of the
    erased environment in which no constructor belongs to a coinductive type (see
    [ErasureFirstorder.erasure_pipeline_mapping_firstorder]). *)
Lemma erasure_pipeline_mapping_firstorder econf (p : Ast.Env.program) pr i u args v v1 :
  ErasureFirstorder.axiom_free p.1 ->
  ∥ @Template.Typing.typing config.extraction_checker_flags (Ast.Env.empty_ext p.1) [] p.2
      (Ast.mkApps (Ast.tInd i u) args) ∥ ->
  ErasureFirstorder.firstorder_ind p.1 (ErasureFirstorder.firstorder_env p.1) i ->
  eval_template_program_mapping ([], p) v ->
  Transform.obseq (erasure_pipeline_mapping econf) ([], p) pr
    (Transform.run (erasure_pipeline_mapping econf) ([], p) pr) v v1 ->
  let t := ErasureCorrectness.compile_value_box (pcuic_env p) (pcuic_term p v) [] in
  let Σ' := (Transform.run (erasure_pipeline_mapping econf) ([], p) pr).1 in
  v1 = t /\ firstorder_evalue_block Σ' t /\
  ∥ EFirstorder.firstorder_ind_value Σ' t ∥.
Proof.
  intros hax hty hfo hev hobs t Σ'.
  destruct (ErasureFirstorder.erasure_pipeline_mapping_firstorder econf p pr i u args v v1
    (@PCUICSN.normalization _ _ _) hax hty hfo hev hobs) as (-> & hfov & hind).
  by split.
Qed.

(** The erasure pipeline maps first-order values to their trees of constructors, with
    parameters erased and singleton constructors unboxed. The tree is a first-order value of
    the environment computed by MetaRocq's pipeline, before CertiRocq's passes. We restrict to the verified passes
    of MetaRocq's untyped erasure pipeline, without inductive mappings: typed erasure removes
    dead constructor arguments (dearging), and the unsafe passes and inductive mappings change
    the representation of inductive values. *)
Lemma erasure_obseq_firstorder (o : Options) (p : Ast.Env.program) i u args v v_er :
  enable_typed_erasure (erasure_config o) = false ->
  enable_unsafe (erasure_config o) = no_unsafe_passes ->
  Pipeline_utils.inductives_mapping o = [] ->
  ErasureFirstorder.axiom_free p.1 ->
  ∥ @Template.Typing.typing config.extraction_checker_flags (Ast.Env.empty_ext p.1) [] p.2
      (Ast.mkApps (Ast.tInd i u) args) ∥ ->
  ErasureFirstorder.firstorder_ind p.1 (ErasureFirstorder.firstorder_env p.1) i ->
  eval_template_program_mapping (Pipeline_utils.inductives_mapping o, p) v ->
  erasure_obseq o p v v_er ->
  let t := ErasureCorrectness.compile_value_box (pcuic_env p) (pcuic_term p v) [] in
  (exists Σw, firstorder_evalue_block Σw t) /\ v_er = unbox_fo (erased_program o p).1 t.
Proof.
  intros htyped hunsafe himap hax hty hfo hev [pr hobs] t.
  rewrite /erased_program (erase_program_run _ _ _ pr) in hobs |- *.
  move: pr hev hobs. rewrite himap /certirocq_erasure_pipeline htyped => pr hev hobs.
  apply obseq_compose_inv in hobs as (v1 & hobs1 & hobs2).
  destruct (erasure_pipeline_mapping_firstorder _ _ _ _ _ _ _ _ hax hty hfo hev hobs1)
    as (-> & htree & _).
  split; [by eexists; exact htree|].
  exact (post_pipeline_firstorder _ _ _ _ _ _ _ hunsafe htree hobs2).
Qed.

(** The first-order variant of [CertiRocq_pipeline_total_correct]: the LambdaANF program
    computes the same tree of constructors as the source program. *)
Theorem CertiRocq_pipeline_firstorder (next_id : positive) (dbg : bool) (o : Options)
  (p : Ast.Env.program) w i u args :
  (* The source program is well-typed *)
  wf_template_inductives_mapping p.1 (Pipeline_utils.inductives_mapping o) ->
  ∥ @TemplateProgram.wt_template_program config.extraction_checker_flags p ∥ ->
  (* We use the ANF translation, and do not register primitives *)
  direct o = true ->
  (* The erased program has no axioms nor primitive arrays *)
  wf_eprogram (certirocq_flags env_flags) (erased_program o p) ->
  (* Only the verified erasure passes are used, without inductive mappings *)
  enable_typed_erasure (erasure_config o) = false ->
  enable_unsafe (erasure_config o) = no_unsafe_passes ->
  Pipeline_utils.inductives_mapping o = [] ->
  (* The source program computes a value of a first-order inductive type *)
  ErasureFirstorder.axiom_free p.1 ->
  ∥ @Template.Typing.typing config.extraction_checker_flags (Ast.Env.empty_ext p.1) [] p.2
      (Ast.mkApps (Ast.tInd i u) args) ∥ ->
  ErasureFirstorder.firstorder_ind p.1 (ErasureFirstorder.firstorder_env p.1) i ->
  exists r w',
    runState (CertiRocq_pipeline next_id [] dbg p) o w = (compM.Ret r, w') /\
    forall v,
      eval_template_program_mapping (Pipeline_utils.inductives_mapping o, p) v ->
      exists v_tgt c t,
        @bstep_fuel (anf_cenv r) nat fuel_res (nat * nat) trace_res (anf_env r) (anf_exp r) c
          (Res v_tgt) t /\
        fo_value_ref (erased_program o p).1 (erased_tag_map o p)
          (ErasureCorrectness.compile_value_box (pcuic_env p) (pcuic_term p v) []) v_tgt.
Proof.
  intros hmap hwt hdirect hwf htyped hunsafe himap hax hty hfo.
  destruct (CertiRocq_pipeline_total_correct next_id dbg o p w hmap hwt hdirect hwf)
    as (r & w' & hrun & hcorr).
  exists r, w'. split => // v hev.
  destruct (hcorr v hev) as (v_er & v_tgt & c & t & hobs & _ & hev_tgt & hv).
  destruct (erasure_obseq_firstorder o p i u args v v_er htyped hunsafe himap hax hty hfo hev hobs)
    as [[Σw htree] ->].
  exists v_tgt, c, t. split => //.
  exact (obs_val_unbox_fo _ _ _ _ htree _ hv).
Qed.
