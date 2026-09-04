From Stdlib Require Import ssreflect ssrbool.
From Equations Require Import Equations.

Require Export LambdaANF.toplevel Codegen.toplevel CodegenWasm.toplevel.
Require Import LambdaBox_to_LambdaANF.fuel_sem.
Require Import LambdaBox_to_LambdaANF.common.
Require Import LambdaBox_to_LambdaANF.anf.
Require Import LambdaBox_to_LambdaANF.anf_correct.
Require Import LambdaBox_to_LambdaANF.anf_convert_env.
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

Import EEnvMap.

From MetaRocq.Erasure Require Import EWcbvEval.
Import EGlobalEnv.
Import ETransform EImplementLazyForce EImplementBox.

Definition env_flags :=
  let efl := EConstructorsAsBlocks.switch_cstr_as_blocks
    (EInlineProjections.disable_projections_env_flag 
      (ERemoveParams.switch_no_params EWellformed.all_env_flags)) in
  let efl' := efl_coind_to_ind efl in
  switch_off_thunk (switch_off_box efl').

(* CertiRocq does not support primitives yet *)
Definition no_primitive_array_flags := {|
  has_primint := true;
  has_primfloat := true;
  has_primstring := true;
  has_primarray := false; |}.
  
Definition set_primitives (fl : ETermFlags) p :=
{| has_tBox := fl.(has_tBox)
  ; has_tRel := fl.(has_tRel)
  ; has_tVar := fl.(has_tVar)
  ; has_tEvar := fl.(has_tEvar)
  ; has_tLambda := fl.(has_tLambda)
  ; has_tLetIn := fl.(has_tLetIn)
  ; has_tApp := fl.(has_tApp)
  ; has_tConst := fl.(has_tConst)
  ; has_tConstruct := fl.(has_tConstruct)
  ; has_tCase := fl.(has_tCase)
  ; has_tProj := fl.(has_tProj)
  ; has_tFix := fl.(has_tFix)
  ; has_tCoFix := fl.(has_tCoFix)
  ; has_tPrim := p
  ; has_tLazy_Force := fl.(has_tLazy_Force)
|}.

(* CertiRocq's correctness lemma only supports global environments made of lambda abstractions 
  (not arbitrary expressions or values) *)
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

(* If the global environment is made of lambdas the all entries evaluate in 0 steps into values *)
Lemma lambda_glob_eval_env_fuel (p : EProgram.eprogram) (efl := env_flags) :
  wf_glob p.1 ->
  EWcbvEval.lambda_glob p.1 ->
  forall (k : kername) (decl : constant_body) (body : term),
  EGlobalEnv.declared_constant p.1 k decl ->
  cst_body decl = Some body -> exists (src_v : fuel_sem.value) (f t : nat), 
  eval_env_fuel (Hf:=LambdaBox_resource_fuel) p.1 [] body (Val src_v) f t /\ f = <0>.
Proof.
  destruct p as [Σ p]; cbn; clear p.
  intros hwf hv kn decl body hd hb.
  have hwfd := wf.wf_glob_globals_wf _ hwf _ _ _ hd hb.
  eapply (lambda_glob_declared _ hwf hv) in hd; tea.
  destruct decl as [[|]]=> //. noconf hb. cbn in hd.
  destruct hd as [na [b ->]]. do 3 eexists. split. constructor. constructor. now cbn.
Qed.

Section Correctness.

  Context (func_tag kon_tag default_tag default_itag : positive).
  Context (next_id : positive).

  Notation refines_toplevel Σ ie tgm := (@refines_top default_tag default_itag tgm Σ ie).

  (** To prove the correctness of connecting the MetaRocq pipeline and CertiRocq's ANF, we
      need a stronger well-formedness property. This formalizes the remaining mismatch 
      between metarocq's pipeline and certirocq's LambdaANF: 

    - primitives are not supported in fuel_sem, and primitive arrays are forbidden in ANF conversion.
    - the environment must be axiom free, as usual *)

  Definition certirocq_flags (efl : EEnvFlags) := 
    {| has_axioms := false; 
       has_cstr_params := efl.(has_cstr_params); 
       term_switches := set_primitives efl.(term_switches) no_primitive_array_flags;
       cstr_as_blocks := efl.(cstr_as_blocks) |}.

  Definition anf_convert ie tgm := 
    convert_top_anf func_tag default_tag (M.empty _) default_itag next_id tgm []
      (fun _ => None) ie.
  
  Theorem metarocq_to_anf_correct (econf : erasure_configuration) (p : EProgram.eprogram) : 
    (* The postcondition on MetaRocq's pipeline *)
    Transform.Transform.post (certirocq_post_metarocq_pipeline econf) p ->
    (* Stronger invariant: no axioms, no primitives *)
    EProgram.wf_eprogram (certirocq_flags env_flags) p ->
    let ie := inductive_env_east (fst p) in
    let tgm := (convert_env default_tag default_itag ie).2 in
    forall e_tgt comp_d', 
      anf_convert ie tgm (List.rev (fst p)) (snd p) = (compM.Ret e_tgt, comp_d') ->
      exists M, refines_toplevel (fst p) ie tgm M (snd p) e_tgt.
  Proof.
    intros hp wf' ie tgm e_tgt comp_d' cvt.
    cbn in hp. unfold certirocq_flags in wf'. cbn in wf'.
    unfold all_env_flags in hp. cbn in hp.
    match goal with
    | [ _ : EProgram.wf_eprogram ?fl p /\ _ |- _ ] => set (efl := fl) in *
    end.
    destruct hp as [wfp [vg]].
    have wf : wf_env_east ie.
    { apply wf_env_inductive, wfp. }
    eapply (convert_top_anf_correct func_tag kon_tag default_tag default_itag tgm (fst p) 
      (efl:=certirocq_flags env_flags)); trea.
    - (* The tag map is injective *) 
      now apply convert_env_inj.
    - (* All the original constructors are registered in the tag map *) 
      apply convert_env_reg.
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
      clear wfp wf. destruct wf' as [wfΣ wf].       
      intros kn decl body hdecl hb.
      eapply (lookup_env_wellformed (efl := certirocq_flags (switch_off_box env_flags))) in hdecl; tea.
      destruct decl; trivial. cbn in hdecl. cbn in hb.
      now subst cst_body.
    - apply wf'.
    - (* No prims *)
      intros s. cbn. reflexivity.
    - eapply (cenv_tgm_coh default_tag default_itag) in wf. unfold top_cenv.
      destruct convert_env as [[[[] ?] ?] ?]. apply wf.
    - apply wf'.
  Qed.

  Theorem metarocq_to_anf_total econf (p : EProgram.eprogram) : 
    (* The postcondition on MetaRocq's pipeline *)
    Transform.Transform.post (certirocq_post_metarocq_pipeline econf) p ->
    (* Stronger invariant: no axioms, no primitives *)
    EProgram.wf_eprogram (certirocq_flags env_flags) p ->
    let ie := inductive_env_east (fst p) in
    let tgm := (convert_env default_tag default_itag ie).2 in
    exists e_tgt comp_d', 
      anf_convert ie tgm (List.rev (fst p)) (snd p) = (compM.Ret e_tgt, comp_d') /\
      exists M, refines_toplevel (fst p) ie tgm M (snd p) e_tgt.
  Proof.
    intros hp wf' ie tgm.
    match goal with
    | [ _ : EProgram.wf_eprogram ?fl p |- _ ] => set (efl := fl) in *
    end.
    destruct hp as [wfp [vg]].
    have wf : wf_env_east ie.
    { apply wf_env_inductive. apply wf'. }
    unshelve eset (prf := anf_corresp.convert_top_anf_total func_tag default_tag default_itag tgm (fst p) 
      (efl:=certirocq_flags env_flags) eq_refl (M.empty _) [] (proj1 wf') eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl
      _
      (convert_env_reg _ _ _) next_id ie _ (proj2 wf')); trea.
    destruct prf as [e_tgt [comp_d' heq]]. exists e_tgt, comp_d'. split.
    unfold anf_convert. exact heq.
    eapply (metarocq_to_anf_correct econf); tea. split => //.
  Qed.
  
  (*
  Lemma metarocq_anf_pipeline (p : EProgram.eprogram) opts : 
    (* The postcondition on MetaRocq's pipeline *)
    Transform.Transform.post (certirocq_post_metarocq_pipeline econf) p ->
    (* Stronger invariant: no axioms, no primitives *)
    EProgram.wf_eprogram (certirocq_flags env_flags) p ->
    let ie := inductive_env_east (fst p) in
    let tgm := (convert_env default_tag default_itag ie).2 in
    let cenv := (convert_env default_tag default_itag ie).1.1.1.2 in
    exists e_tgt comp_d', 
      anf_convert ie tgm (List.rev (fst p)) (snd p) = (compM.Ret e_tgt, comp_d') /\
      exists e_tgt' data, 
        anf_pipeline next_id opts e_tgt comp_d' = (compM.Ret e_tgt', data) /\
        forall (v_src : fuel_sem.value) (f_src t_src : nat),
        eval_env_fuel (Hf := LambdaBox_resource_fuel) (Ht := LambdaBox_resource_trace) p.1 [] p.2 (Val v_src) f_src t_src ->
        exists (v2 : val) (c2 : nat) (t2 : nat × nat), eval.bstep_fuel  cenv emp e_tgt' c2 (eval.Res v2) t2 /\ anf_toplevel.value_ref tgm v_src v2.
         (* /\ refines (trace:=nat * nat) cenv value_ref_cc e_tgt e_tgt'. *)
  Proof.
    intros hp wf' ie tgm cenv.
    destruct (metarocq_to_anf_total p hp wf') as [e_tgt [comp_d' [heq [M href]]]].
    exists e_tgt, comp_d'. split => //.
    pose proof (anf_pipeline_whole_program_correct cenv next_id opts e_tgt comp_d').
    forward H.
    { admit. }
    forward H.
    { admit. }
    forward H by admit.
    destruct H as [e' [c' [hanf href']]].
    exists e', c'. split => //.
    do 2 red in href.
    intros v_src f_src t_src hev.
    specialize (href v_src f_src t_src hev) as [v_tgt [ctgt [hev' [hc href]]]].
    set (top_cenv := top_cenv _ _ _) in hev'. 
    assert (top_cenv = cenv). unfold top_cenv, cenv. unfold anf_toplevel.top_cenv. destruct convert_env as [[[[] ?] ?] ?]. reflexivity.
    clearbody top_cenv. subst top_cenv.
    destruct href' as [href' _].    
    specialize (href' v_tgt _ _ hev'). (href' v_tgt ctgt hev') as [v2 [c2 [t2 [hev'' href'']]]].
    destruct (href v_src f_src t_src hev).
    exists v2, c2, t2

    red in href'.
    exists M. split => //.
    Print anf_toplevel.refines.
    Print refines.
  Admitted.
*)

    




(* 
  Theorem metarocq_to_anf_eval (p : EProgram.eprogram) : 
    (* The postcondition on MetaRocq's pipeline *)
    Transform.Transform.post (certirocq_post_metarocq_pipeline econf) p ->
    (* Stronger invariant: no axioms, no primitives *)
    EProgram.wf_eprogram (certirocq_flags env_flags) p ->
    let ie := inductive_env_east (fst p) in
    let tgm := (convert_env default_tag default_itag ie).2 in
    forall v_src, 
      eval (fst p) (snd p) v_src ->
      exists M e_tgt v_tgt c_tgt,
      anf_convert ie tgm (List.rev (fst p)) (snd p) = (compM.Ret e_tgt, comp_d') /\
      eval.bstep_fuel (cenv comp_d') (M.empty val) e_tgt c_tgt (eval.Res v_tgt) tt /\
      anf_toplevel.value_ref tgm v_src v_tgt. *)
      
End Correctness.