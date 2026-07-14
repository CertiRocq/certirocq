From Stdlib Require Import ssreflect.
(* From Wasm Require Import binary_format_printer. *)

Require Export LambdaANF.toplevel Codegen.toplevel CodegenWasm.toplevel.
Require Import LambdaBox_to_LambdaANF.fuel_sem.
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
(* Require Import LambdaBox_to_LambdaANF.anf_correct.
Import LambdaBox_to_LambdaANF.anf.
Import LambdaBox_to_LambdaANF.anf_correct.
Require Import LambdaBox_to_LambdaANF.anf_toplevel. *)
Section lambdabox_anf_pipeline_correct.


Section Assumptions.
  
  Lemma values_glob_declared (p : EProgram.eprogram) : 
    EWcbvEval.values_glob (wfl := final_wcbv_flags) p.1 ->
    forall (k : kername) (decl : constant_body),
    EGlobalEnv.declared_constant p.1 k decl -> value_decl (wfl := final_wcbv_flags) p.1 (ConstantDecl decl).
  Proof.
    destruct p as [Σ p]; cbn; clear p.
    (* Needs weakening for value *)

    induction 1 as [|kn d Σ HΣ IHd].
    - intros k decl body.
      now unfold EGlobalEnv.declared_constant.
    - intros k decl body.
      unfold EGlobalEnv.declared_constant in body. cbn in body.
      move: body; case: (eqb_specT k kn) => [<-|hd]; eauto.
      ( )


  

  Lemma values_glob_eval_env_fuel (p : EProgram.eprogram) : EWcbvEval.values_glob (wfl := final_wcbv_flags) p.1 ->
    forall (k : kername) (decl : constant_body) (body : term),
    EGlobalEnv.declared_constant p.1 k decl ->
    cst_body decl = Some body -> exists (src_v : fuel_sem.value) (f t : nat), eval_env_fuel p.1 [] body (Val src_v) f t.
  Proof.
    destruct p as [Σ p]; cbn; clear p.
    induction 1 as [|kn d Σ HΣ IHd].
    - intros k decl body.
      now unfold EGlobalEnv.declared_constant.
    - intros k decl body. destruct d; cbn in v.



  Context (func_tag kon_tag default_tag default_itag : positive)
          (tgm : conId_map).

  Notation refines_top Σ := (@refines_top default_tag default_itag tgm Σ).
Print value_decl.

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
    | [ _ : EProgram.wf_eprogram ?fl p |- _ ] => set (efl := fl) in *
    end.
    unfold refines_top. unfold refines.
    eapply (convert_top_anf_correct func_tag kon_tag default_tag default_itag tgm (fst p) (efl:=efl)); trea.
    - (* No axioms *) cbn. admit.
    - (* If tgm came from convert_env, wouldn't that be true? *)
      admit.
    - assert (EWcbvEval.values_glob (wfl := final_wcbv_flags) p.1). admit.
      intros kn decl hl hb. (* The environment entries should be evaluable to values *)
      admit.
    - intros kn decl hl hb. (* Constants to values should carry its post-condition, for immediate values *)
      admit.
    - (* Wellformed declarations in the global environment *) 
      destruct hp as [wfg wfp].
      intros kn decl body hdecl hb.
      eapply lookup_env_wellformed  in hdecl; tea. destruct decl; trivial. cbn in hdecl. cbn in hb. now subst cst_body.
    - apply hp.
    - (* No Var! *) admit.
    - (* No EVar! *) admit.
    - (* No PrimArray! *) admit.
    - (* No prims *)
      intros s. cbn. reflexivity.
    - apply hp.
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