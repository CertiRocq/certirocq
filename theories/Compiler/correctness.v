From Stdlib Require Import ssreflect ssrbool.
From Equations Require Import Equations.

Require Export LambdaANF.toplevel Codegen.toplevel CodegenWasm.toplevel.
Require Import LambdaBox_to_LambdaANF.fuel_sem.
Require Import LambdaBox_to_LambdaANF.common.
Require Import LambdaBox_to_LambdaANF.anf.
Require Import LambdaBox_to_LambdaANF.anf_toplevel.
Require Export LambdaANF.toplevel_theorems.
Require Import compcert.lib.Maps.
From Stdlib Require Import ZArith.
Require Import Common.Common Common.compM Common.Pipeline_utils.
From Stdlib Require Import List.
Require Import maps_util.
Require Import Glue.glue.
Require Import ExtLib.Structures.Monad.
Require Import MetaRocq.Common.BasicAst.
From MetaRocq.Erasure Require Import EAst Erasure EWellformed.
From MetaRocq.ErasurePlugin Require Import Erasure.
From MetaRocq.Utils Require Import utils.

From CertiRocq Require Import metarocq_pipeline pipeline.

Import Monads.
Import MonadNotation.
Import ListNotations.
Import common rel_comp.
Require Import LambdaANF.term.
Print CertiRocq_pipeline.
Print get_options.
Print compile_LambdaBoxEAst.
Print erase_program.
Print compile_LambdaANF_ANF.

Definition next_id := 100%positive.
Definition econf := Erasure.default_erasure_config.
Definition opts := default_opts.

Definition run_pipeline p pre :=
  let p' := Transform.Transform.run (verified_lambdabox_pipeline econf) p pre in
  let (perr, log) := run_pipeline _ _ opts p' (compile_LambdaANF_ANF next_id []) in
  match perr with
  | Ret p =>
    let '(pr, cenv, _, _, nenv, fenv, idm,  e) := p in
    Some (nenv, cenv, idm, e)
  | Err s => None
  end.
Import EEnvMap.

From MetaRocq.Erasure Require Import EWcbvEval.
Section lambdabox_anf_pipeline_correct.
Import EGlobalEnv.

Section Assumptions.

  Lemma lambda_glob_lookup Σ : 
    lambda_glob Σ -> 
    forall kn v, EGlobalEnv.lookup_env Σ kn = Some (ConstantDecl {| cst_body := Some v |}) -> 
    lambda_value_pred Σ v.
  Proof.
    induction 1.
    - intros kn v; cbn => //.
    - intros kn' v' hl. 
      cbn in hl. 
      destruct (eqb_specT kn' kn). subst kn'. noconf hl.
      destruct d0 as [na [t ->]]. now do 2 eexists.
      now cbn in d0.
  Qed.

  Lemma lambda_glob_declared Σ {efl : EEnvFlags} : 
    wf_glob Σ ->
    EWcbvEval.lambda_glob Σ ->
    forall (k : kername) (decl : constant_body),
    declared_constant Σ k decl ->
    decl_pred (lambda_value_pred Σ) (ConstantDecl decl).
  Proof.
    unfold EGlobalEnv.declared_constant.
    intros hwf hv kn decl hl. destruct decl as [] => //.
    destruct cst_body => //.
    eapply lambda_glob_lookup in hl; tea.
  Qed.
  Import ETransform EImplementLazyForce EImplementBox.
  
  Definition env_flags :=
     let efl := EConstructorsAsBlocks.switch_cstr_as_blocks
        (EInlineProjections.disable_projections_env_flag 
          (ERemoveParams.switch_no_params EWellformed.all_env_flags)) in
     let efl' := efl_coind_to_ind efl in
     switch_off_thunk (switch_off_box efl').

  Definition no_primitive_flags := {|
    has_primint := false;
    has_primfloat := false;
    has_primstring := false;
    has_primarray := false; |}.

  Lemma lambda_glob_eval_env_fuel (p : EProgram.eprogram) (efl := env_flags) :
    wf_glob p.1 ->
    EWcbvEval.lambda_glob p.1 ->
    forall (k : kername) (decl : constant_body) (body : term),
    EGlobalEnv.declared_constant p.1 k decl ->
    cst_body decl = Some body -> exists (src_v : fuel_sem.value) (f t : nat), 
    eval_env_fuel (Hf:=anf_correct.LambdaBox_resource_fuel) p.1 [] body (Val src_v) f t /\ f = <0>.
  Proof.
    destruct p as [Σ p]; cbn; clear p.
    intros hwf hv kn decl body hd hb.
    have hwfd := wf.wf_glob_globals_wf _ hwf _ _ _ hd hb.
    eapply (lambda_glob_declared _ hwf hv) in hd; tea.
    destruct decl as [[|]]=> //. noconf hb. cbn in hd.
    destruct hd as [na [b ->]]. do 3 eexists. split. constructor. constructor. now cbn.
  Qed.

  Context (func_tag kon_tag default_tag default_itag : positive)
          (tgm : conId_map).

  Notation refines_top Σ := (@refines_top default_tag default_itag tgm Σ).

  Theorem correctness_from_erasure (p : EProgram.eprogram) : 
    Transform.Transform.post (certirocq_post_metarocq_pipeline econf) p ->
    let ie := inductive_env_east (fst p) in
    forall (casecon : forall (P : list (ctor_tag × exp)) (ctag : ctor_tag), term_util.caseConsistent (top_cenv default_tag default_itag ie) P ctag),
    forall e_tgt comp_d',  
      convert_top_anf func_tag default_tag (M.empty _) default_itag next_id tgm []
      (fun _ => None)
      ie (List.rev (fst p)) (snd p) = (compM.Ret e_tgt, comp_d') ->
    exists M, refines_top (fst p) ie M (snd p) e_tgt.
  Proof.
    intros hp ie case_con e_tgt comp_d' cvt.
    cbn in hp.
    match goal with
    | [ _ : EProgram.wf_eprogram ?fl p /\ _ |- _ ] => set (efl := fl) in *
    end.
    destruct hp as [wfp [vg]].
    eapply (convert_top_anf_correct func_tag kon_tag default_tag default_itag tgm (fst p) (efl:=efl)); trea.
    - (* No axioms *) cbn. admit.
    - (* If tgm came from convert_env, wouldn't that be true? *)
      admit.
    - (* The environment entries evaluate to values *)
      intros kn decl hl hb hbody.
      eapply lambda_glob_eval_env_fuel in hb; tea.
      destruct hb as [srcv [f [t [ev eq]]]]. now exists srcv, f, t. apply wfp.
    - (* The environment entries should evaluate to values with 0 fuel (they're lambdas) *)
      intros kn decl b srcv f t hd hbody hev.
      eapply lambda_glob_eval_env_fuel in hd; tea. 2:apply wfp.
      destruct hd as [srcv' [f' [t' [ev eqf]]]].
      eapply eval_val_exact_det in hev; tea. destruct hev as [eq [eq' eq'']].
      now subst f' srcv' t' f.
    - (* Wellformed declarations in the global environment *) 
      destruct wfp as [wfΣ wf].      
      intros kn decl body hdecl hb.
      eapply lookup_env_wellformed  in hdecl; tea. destruct decl; trivial. cbn in hdecl. cbn in hb. now subst cst_body.
    - apply wfp.
    - (* No Var! *) admit.
    - (* No EVar! *) admit.
    - (* No PrimArray! *) admit.
    - (* No prims *)
      intros s. cbn. reflexivity.
    - apply wfp.
  Admitted.

(*
Section Assumptions.
  
  Context (func_tag kon_tag default_tag default_itag : positive)
          (tgm : conId_map).

  Context (box_dc : dcon)
          (box_tag : dcon_to_tag default_tag tgm = default_tag).

  Let Hf_src := LambdaBox_resource_fuel default_tag tgm box_tag.
  Let Ht_src := LambdaBox_resource_trace default_tag tgm box_tag.
  
  Existing Instance default_wcbv_flags. 

  Context {fuel trace : Type}.
  Context {Hf : @fuel_resource fuel} {Ht : @trace_resource trace}.
Transparent bind.
Transparent Pipeline_utils.ret.




  Theorem correctness_from_erasure (p : EProgram.eprogram_env) : 
  forall pre : Transform.Transform.pre (verified_lambdabox_pipeline econf) p,
  forall v, 
    EWcbvEval.eval (GlobalContextMap.global_decls (fst p)) (snd p) v ->
    exists nenv cenv cm e ev v' n r fuel trace, 
      run_pipeline p pre = Some (nenv, cenv, e) /\
      @eval_env_step _ Hf_src Ht_src [] [] v (Val v') n r /\
      eval.bstep_fuel (Hf:=Hf) (Ht := Ht) (snd nenv) emp e fuel (eval.Res ev) trace /\
      anf_util.anf_val_rel (Hf_src := Hf_src) (Ht_src:=Ht_src) func_tag default_tag tgm cm (fst p) v' ev.
  Proof.
    intros pre v ev.
    unfold run_pipeline.
    unfold Pipeline_utils.run_pipeline, runState.
    unfold Transform.Transform.run, Transform.time.
    set (tr := Transform.Transform.transform _ _ _).
    unfold compile_LambdaANF_ANF. unfold debug_msg, get_options, compM.ask. unfold opts, default_opts.
    About bind.
    cbn -[tr].
    destruct (LambdaANF_ANF _ _ _ ) eqn:ela.
    unfold LambdaANF_ANF in ela.
    Search anf.convert_top_anf. 


    { exfalso.
      unfold LambdaANF
    
    }
    cbn. destruct get_options. cbn. 
    Set Printing All. unfold tmBind. cbn.






From MetaRocq.Template Require Import WcbvEval TemplateProgram.

Theorem correctness mapping (p : template_program) : 
  Transform.Transform.pre (erasure_pipeline_mapping econf) (mapping, p) ->
  forall v, 
    eval (fst p) (snd p) v ->
    exists nenv cenv fuel trace e v' n r, 
      run_pipeline p = Some (nenv, cenv, e) /\ 
      eval.bstep_fuel cenv emp e fuel (eval.Res v1) trace /\
      eval_env_step [] v v' n r.




*)