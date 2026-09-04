Definition opts := default_opts.

Definition run_pipeline p pre :=
  let p' := Transform.Transform.run (certirocq_post_metarocq_pipeline econf) p pre in
  let (perr, log) := run_pipeline _ _ opts p' (compile_LambdaANF_ANF next_id []) in
  match perr with
  | Ret p =>
    let '(pr, cenv, _, _, nenv, fenv, idm,  e) := p in
    Some (nenv, cenv, idm, e)
  | Err s => None
  end.

  Let Hf_src := LambdaBox_resource_fuel.
  Let Ht_src := LambdaBox_resource_trace.
  
  Existing Instance default_wcbv_flags.




  Context {fuel trace : Type}.
  Context {Hf : @fuel_resource fuel} {Ht : @trace_resource trace}.
(* Transparent bind. *)
(* Transparent Pipeline_utils.ret. *)


  Theorem correctness_from_erasure' (p : EProgram.eprogram) : 

  forall pre : Transform.Transform.pre (verified_lambdabox_pipeline econf) p,
  forall v, 
    EWcbvEval.eval (fst p) (snd p) v ->
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