(** * End-to-end correctness of [CertiRocq_pipeline]

    This file states and proves the correctness of [CertiRocq_pipeline] (see [pipeline.v]), the
    part of CertiRocq's compiler going from a MetaRocq Template program to LambdaANF, in its
    direct-style (ANF) configuration. It composes:

    - the correctness of MetaRocq's erasure pipeline followed by CertiRocq's post-processing
      ([certirocq_erasure_pipeline], via MetaRocq's [Transform] framework);
    - the correspondence between MetaRocq's substitution-based evaluation of erased programs
      and CertiRocq's environment-based semantics [fuel_sem] (assumed, see [eval_to_fuel_sem]);
    - the correctness of the ANF conversion ([metarocq_to_anf_correct] in [correctness.v]);
    - the correctness of the LambdaANF optimization pipeline ([anf_pipeline_whole_program_correct]
      in [LambdaANF/toplevel_theorems.v]).

    The final theorem is [CertiRocq_pipeline_correct]: if a well-typed Template program [p]
    evaluates to a value [v], and [CertiRocq_pipeline] successfully compiles it to a LambdaANF
    program, then this program evaluates to a value [v_tgt] that has the same observable
    structure as the value computed by the erased program, which is related to [v] by the
    observational relation of MetaRocq's erasure pipeline.

    The programs must not use axioms nor primitive arrays: this is ensured by the [check_axioms]
    and [check_wellformed] passes of the pipeline, so it follows from the pipeline's success.

    Remaining assumptions, besides the ones of the theorems we compose (see the end of the file):
    - [eval_to_fuel_sem] (axiom): proven by MetaRocq PR #1288 (WcbvEval to eval_SI) and
      CertiRocq PR #156 (eval_SI to fuel_sem);
    - [convert_top_anf_closed_unique_bindings], [convert_top_anf_cenv] and
      [anf_pipeline_cenv_extends] (admitted): syntactic properties of ANF conversion and of
      the constructor environment along the LambdaANF pipeline. *)

From Stdlib Require Import ssreflect ssrbool.
From Stdlib Require Import ZArith NArith List ProofIrrelevance.
Require Import Common.Common Common.compM Common.Pipeline_utils.
Require Import ExtLib.Structures.Monad.
From MetaRocq.Common Require Import Transform.
From MetaRocq.Erasure Require Import EAst EWellformed EProgram.
From MetaRocq.ErasurePlugin Require Import Erasure.
From MetaRocq.Utils Require Import utils.
From CertiRocq.LambdaBox_to_LambdaANF Require Import common fuel_sem anf_convert_env anf_correct
  anf_toplevel.
Require Import LambdaANF.term LambdaANF.state LambdaANF.eval LambdaANF.identifiers
  LambdaANF.term_util LambdaANF.rel_comp LambdaANF.bounds.
From CertiRocq Require Import metarocq_pipeline pipeline correctness.

Import Monads.
Import MonadNotation.
Import ListNotations.
Import Transform.

(** ** Constructor environments *)

(** [cenv'] extends [cenv] *)
Definition cenv_extends (cenv cenv' : ctor_env) : Prop :=
  forall t info, M.get t cenv = Some info -> M.get t cenv' = Some info.

(** All the tags of [cenv] are smaller than [t] *)
Definition fresh_ctor_tags (cenv : ctor_env) (t : ctor_tag) : Prop :=
  forall t' info, M.get t' cenv = Some info -> (t' < t)%positive.

Lemma cenv_extends_trans c1 c2 c3 :
  cenv_extends c1 c2 -> cenv_extends c2 c3 -> cenv_extends c1 c3.
Proof. intros h1 h2 t i h. now apply h2, h1. Qed.

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
    CertiRocq's environment-based values: this is the composition of [term_of_val] (MetaRocq
    PR #1288) and of the inverse of [convert_vals] (CertiRocq PR #156). *)

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

(** ** Assumptions *)

(** Correspondence between MetaRocq's substitution-based call-by-value evaluation of erased
    programs, and CertiRocq's environment-based semantics [fuel_sem], for the erased programs
    produced by MetaRocq's pipeline. This is the composition of:
    - [eval_eval_SI] from MetaRocq PR #1288 (EWcbvEval to the step-indexed, environment-based
      evaluation relation [eval_SI]), and
    - [evalSI_to_fuel_sem] from CertiRocq PR #156 ([eval_SI] to [fuel_sem]).
    TODO: replace by these results once both PRs are merged. *)
Axiom eval_to_fuel_sem :
  forall (Σ : EAst.global_context) (t v : EAst.term),
    @wf_glob (certirocq_flags env_flags) Σ ->
    @wellformed (certirocq_flags env_flags) Σ 0 t ->
    @EWcbvEval.eval final_wcbv_flags Σ t v ->
    exists (v' : fuel_sem.value) (f tr : nat),
      @eval_env_step nat LambdaBox_resource_fuel LambdaBox_resource_trace Σ [] t (Val v') f tr /\
      v = fs_value_to_term v'.

(** The program produced by ANF conversion is closed and has unique bindings.
    TODO: prove, by induction on [anf_cvt_rel] and [anf_cvt_rel_global] (see [anf_corresp.v]). *)
Lemma convert_top_anf_closed_unique_bindings func_tag default_tag default_itag next_id
  (Σ : EAst.global_context) e e_tgt comp_d :
  wf_eprogram (certirocq_flags env_flags) (Σ, e) ->
  let ie := inductive_env_east Σ in
  let tgm := (convert_env default_tag default_itag ie).2 in
  anf.convert_top_anf func_tag default_tag (M.empty _) default_itag next_id tgm []
    (fun _ => None) ie (List.rev Σ) e = (compM.Ret e_tgt, comp_d) ->
  closed_exp e_tgt /\ unique_bindings e_tgt.
Admitted.

(** ANF conversion does not modify the constructor environment computed from the inductive
    declarations, and all constructor tags allocated so far are below the next free tag.
    TODO: prove, by showing that the state operations used by ANF conversion leave the
    constructor environment unchanged, and that [convert_env] allocates fresh tags. *)
Lemma convert_top_anf_cenv func_tag default_tag default_itag next_id
  (Σ : EAst.global_context) e e_tgt comp_d :
  let ie := inductive_env_east Σ in
  let tgm := (convert_env default_tag default_itag ie).2 in
  anf.convert_top_anf func_tag default_tag (M.empty _) default_itag next_id tgm []
    (fun _ => None) ie (List.rev Σ) e = (compM.Ret e_tgt, comp_d) ->
  state.cenv comp_d = top_cenv default_tag default_itag ie /\
  fresh_ctor_tags (state.cenv comp_d) (nect_ctor_tag comp_d).
Admitted.

(** The LambdaANF pipeline only extends the constructor environment (closure conversion
    registers the constructors of closure environments, using fresh tags).
    TODO: prove, pass by pass. *)
Lemma anf_pipeline_cenv_extends next_var opts e c e' c' :
  fresh_ctor_tags (state.cenv c) (nect_ctor_tag c) ->
  anf_pipeline next_var opts e c = (compM.Ret e', c') ->
  cenv_extends (state.cenv c) (state.cenv c').
Admitted.

(** ** Inversion of the pipeline *)

Lemma CertiRocq_pipeline_inv nid dbg p o w r w' :
  direct o = true ->
  runState (CertiRocq_pipeline nid [] dbg p) o w = (compM.Ret r, w') ->
  let p_er := erase_program [] (erasure_config o) (Pipeline_utils.inductives_mapping o) p in
  let ie := inductive_env_east p_er.1 in
  let tgm := (convert_env default_ctor_tag default_ind_tag ie).2 in
  find_axioms [] [] p_er.1 = [] /\
  check_wf_eprogram (certirocq_check_flags false) p_er /\
  exists e_anf nv ctag itag ftag cenv fenv nenv imap lg log,
    anf.convert_top_anf fun_fun_tag default_ctor_tag (M.empty _) default_ind_tag nid tgm []
      (fun _ => None) ie (List.rev p_er.1) p_er.2 =
      (compM.Ret e_anf, mkCompData nv ctag itag ftag cenv fenv nenv imap lg) /\
    run_anf_pipeline nid (make_anf_options o)
      (M.empty _, M.empty _, cenv, ctag, itag, nenv, fenv, M.empty _, e_anf) = (compM.Ret r, log).
Proof.
  intros hdirect heq.
  unfold CertiRocq_pipeline, compile_LambdaBoxEAst, check_axioms, check_wellformed,
    Pipeline_utils.LiftCertiRocqTrans, Pipeline_utils.debug_msg, Pipeline_utils.get_options,
    compile_LambdaANF_ANF, compile_LambdaANF_debug, compile_LambdaANF,
    Pipeline_utils.LiftErrorCertiRocqTrans, Pipeline_utils.LiftErrorLogCertiRocqTrans,
    Pipeline_utils.timePhase_opt, AstCommon.timePhase in heq.
  set (p_er := erase_program _ _ _ _) in *.
  set (ie := inductive_env_east p_er.1).
  destruct (convert_env default_ctor_tag default_ind_tag ie) as [[[[? ?] ?] ?] dcm] eqn:hce.
  cbv beta iota zeta delta [Monad.bind Monad.ret compM.MonadErrorT compM.MonadState compM.ask
    compM.get compM.put compM.failwith Pipeline_utils.ret compM.runState compM.compM compM.errorT
    debug_msg get_options] in heq.
  rewrite hdirect in heq. destruct w.
  repeat (cbv beta iota zeta in heq; fold p_er ie in heq; rewrite ?hce in heq;
    match type of heq with
    | context [if dbg then _ else _] => destruct dbg
    | context [debug o] => destruct (debug o)
    | context [Pipeline_utils.time o] => destruct (Pipeline_utils.time o)
    | context [find_axioms ?a ?b ?c] => destruct (find_axioms a b c) eqn:hax; [|discriminate heq]
    | context [check_wf_eprogram ?f ?p] =>
      destruct (check_wf_eprogram f p) eqn:hwf; [|discriminate heq]
    | context [anf.convert_top_anf ?a ?b ?c ?d ?e ?f ?g ?h ?i ?j ?k] =>
      destruct (anf.convert_top_anf a b c d e f g h i j k) as [[|e_anf] []] eqn:hcvt;
        [discriminate heq|]
    | context [run_anf_pipeline ?a ?b ?c] =>
      destruct (run_anf_pipeline a b c) as [[|r'] log'] eqn:hrun; [discriminate heq|]
    end).
  all:cbv beta iota zeta in heq; injection heq as h1 _; subst r.
  all:split; [exact hax|split; [exact hwf|]].
  all:rewrite -/ie hce; cbn [snd].
  all:do 11 eexists; split; [exact hcvt|exact hrun].
Qed.

Lemma run_anf_pipeline_inv nid opts pr penv cenv ctag itag nenv fenv rho e r log :
  run_anf_pipeline nid opts (pr, penv, cenv, ctag, itag, nenv, fenv, rho, e) = (compM.Ret r, log) ->
  exists c e' c',
    state.next_var c = (max_var e 1 + 1)%positive /\
    state.cenv c = cenv /\ nect_ctor_tag c = ctag /\
    anf_pipeline nid opts e c = (compM.Ret e', c') /\
    r = (pr, penv, state.cenv c', nect_ctor_tag c', next_ind_tag c', state.nenv c', state.fenv c',
         M.empty _, e').
Proof.
  unfold run_anf_pipeline.
  set (c := pack_data _ _ _ _ _ _ _ _ _).
  destruct (anf_pipeline nid opts e c) as [[|e'] [? ? ? ? ? ? ? ? ?]] eqn:hrun => //.
  intros [= <-]. exists c. do 2 eexists. split; [reflexivity|]. split; [reflexivity|].
  split; [reflexivity|]. split; [exact hrun|reflexivity].
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
  (convert_env default_ctor_tag default_ind_tag (inductive_env_east (erased_program o p).1)).2.

(** The observational relation of the erasure pipeline, relating the values of the source
    and erased programs *)
Definition erasure_obseq (o : Options) (p : Ast.Env.program) (v : Ast.term) (v' : EAst.term) :=
  exists pr, Transform.obseq (erasure_pipeline (erasure_config o)) (Pipeline_utils.inductives_mapping o, p) pr
    (erased_program o p) v v'.

Theorem CertiRocq_pipeline_correct (next_id : positive) (dbg : bool) (o : Options)
  (p : Ast.Env.program) w w' pr penv cenv ctag itag nenv fenv rho e :
  (* The source program is well-typed *)
  wf_template_inductives_mapping p.1 (Pipeline_utils.inductives_mapping o) ->
  ∥ @TemplateProgram.wt_template_program config.extraction_checker_flags p ∥ ->
  (* We use the ANF translation, and do not register primitives *)
  direct o = true ->
  (* The pipeline succeeds *)
  runState (CertiRocq_pipeline next_id [] dbg p) o w =
    (compM.Ret (pr, penv, cenv, ctag, itag, nenv, fenv, rho, e), w') ->
  forall v,
    eval_template_program_mapping (Pipeline_utils.inductives_mapping o, p) v ->
    exists v_er v_tgt c t,
      erasure_obseq o p v v_er /\
      eval_eprogram final_wcbv_flags (erased_program o p) v_er /\
      @bstep_fuel cenv nat fuel_res (nat * nat) trace_res rho e c (Res v_tgt) t /\
      obs_val (erased_tag_map o p) v_er v_tgt.
Proof.
  intros hmap hwt hdirect hrun v hev.
  have pre := erasure_pipeline_pre (erasure_config o) _ _ hmap hwt.
  (* Inversion of the pipeline *)
  move: (CertiRocq_pipeline_inv _ _ _ _ _ _ _ hdirect hrun).
  rewrite -/(erased_program o p) -/(erased_tag_map o p).
  set (p_er := erased_program o p). set (tgm := erased_tag_map o p).
  intros (_ & hwf & e_anf & nv & ctag0 & itag0 & ftag0 & cenv0 & fenv0 & nenv0 & imap0 & lg0 & log
    & hcvt & hrun').
  apply check_wf_eprogram_spec in hwf. rewrite certirocq_check_flags_false in hwf.
  (* Erasure *)
  have hpost : Transform.post (certirocq_post_metarocq_pipeline [] (erasure_config o)) p_er.
  { apply erasure_pipeline_post. rewrite /p_er /erased_program (erase_program_run _ _ _ pre).
    apply Transform.correctness. }
  destruct (Transform.preservation (erasure_pipeline (erasure_config o)) _ v pre hev)
    as [v_er [hev_er hobs]].
  rewrite -(erase_program_run _ _ _ pre) -/(erased_program o p) -/p_er in hev_er hobs.
  exists v_er.
  (* From MetaRocq's semantics to fuel_sem *)
  have [hev_er'] := hev_er.
  destruct (eval_to_fuel_sem p_er.1 p_er.2 v_er (proj1 hwf) (proj2 hwf) hev_er')
    as [v_src [f [tr [hev_src ->]]]].
  apply fuel_sem.eval_step in hev_src.
  (* ANF conversion *)
  destruct (metarocq_to_anf_correct fun_fun_tag kon_fun_tag default_ctor_tag default_ind_tag
              next_id (erasure_config o) p_er hpost hwf _ _ hcvt) as [M href].
  destruct (href _ _ _ hev_src) as [v_anf [c_anf [hev_anf [_ hv_anf]]]].
  destruct (convert_top_anf_closed_unique_bindings _ _ _ _ p_er.1 p_er.2 _ _ hwf hcvt)
    as [hclosed huniq].
  (* LambdaANF pipeline *)
  apply run_anf_pipeline_inv in hrun' as [c [e' [c' [hnv [hc [hctag [hanf heq]]]]]]].
  injection heq; intros; subst.
  destruct (convert_top_anf_cenv _ _ _ _ _ _ _ _ hcvt) as [hcenv0 hfresh]. cbn in hcenv0, hfresh.
  have hws : identifiers.well_scoped e_anf.
  { split => //. eapply Ensembles_util.Disjoint_Included_r; [apply hclosed|].
    apply Ensembles_util.Disjoint_Empty_set_r. }
  destruct (anf_pipeline_whole_program_correct (top_cenv default_ctor_tag default_ind_tag
              (inductive_env_east p_er.1)) next_id (make_anf_options o) e_anf c hclosed hws)
    as [e'' [c'' [hanf' [hterm _]]]].
  { rewrite hnv. apply Pos.lt_add_r. }
  rewrite hanf in hanf'. injection hanf' as <- <-.
  apply (@bstep_fuel_transfer _ _ _ _ (nat * nat) _ _ trace_res (fun _ _ h => h)) in hev_anf
    as [t_anf hev_anf].
  destruct (hterm _ _ _ hev_anf) as [v_tgt [c_tgt [t_tgt [hev_tgt hv_tgt]]]].
  have hext : cenv_extends (top_cenv default_ctor_tag default_ind_tag (inductive_env_east p_er.1))
    (state.cenv c').
  { rewrite -hcenv0. exact (anf_pipeline_cenv_extends _ _ _ _ _ _ hfresh hanf). }
  apply (bstep_fuel_transfer (trace' := nat * nat) hext) in hev_tgt as [t' hev_tgt].
  exists v_tgt, c_tgt, t'. split; [now exists pre|]. split => //. split => //.
  eapply obs_val_compose; eauto.
Qed.
