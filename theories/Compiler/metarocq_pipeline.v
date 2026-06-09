Require Import Common.Common Common.compM Common.Pipeline_utils.
From Stdlib Require Import List.
Require Import maps_util.
Require Import MetaRocq.Common.BasicAst.
From MetaRocq.Erasure Require Import EAst Erasure.
From MetaRocq.ErasurePlugin Require Import Erasure.
From MetaRocq.Utils Require Import MRString.

Import Monads.
Import MonadNotation.
Import ListNotations.

From MetaRocq.Erasure Require Import EProgram ERemapInductives EBeta.
From MetaRocq.Common Require Import Transform.
From MetaRocq.ErasurePlugin Require Import ETransform.
Import Transform.

Import EWellformed.
From MetaRocq.Erasure Require Import EImplementBox EImplementLazyForce.
Import TemplateProgram.

(** The CertiRocq MetaRocq pipeline is composed of the verified typed or untyped MetaRocq pipelines plus:

    - CoFixpoints to fixpoints (unverified, only relevant if the source term contains cofixpoints)
    - Transformation of constants to values (verified, simplifies the ANF proof)
    - Transformation of lazy/force to lambda abstractions and applications (verified)
    - Unboxing of single argument constructors (verified)
    - Implementation of "box" as a fixpoint expression (verified)
    
    *)
Program Definition certirocq_post_metarocq_pipeline econf : Transform.t global_context global_context term term term term
  (eval_eprogram final_wcbv_flags)
  (eval_eprogram final_wcbv_flags) :=
  let efl := EConstructorsAsBlocks.switch_cstr_as_blocks
  (EInlineProjections.disable_projections_env_flag (ERemoveParams.switch_no_params EWellformed.all_env_flags)) in
  let efl' := efl_coind_to_ind efl in
  let efl'' := switch_off_thunk (efl_coind_to_ind efl) in
  let efl''' := switch_off_box (switch_off_thunk (efl_coind_to_ind efl)) in
  (* Rebuild the efficient lookup table *)
  rebuild_wf_env_transform (efl := efl) false false ▷
  (* Coinductives & cofixpoints are translated to inductive types and thunked fixpoints *)
  coinductive_to_inductive_transformation efl
      (has_app := eq_refl) (has_box := eq_refl) (has_rel := eq_refl) (has_pars := eq_refl) (has_cstrblocks := eq_refl) ▷
  consts_to_values_transformation efl' final_wcbv_flags eq_refl eq_refl eq_refl ▷
  (* Lazy-to-lambda *)
  implement_lazy_force_transformation efl' eq_refl eq_refl eq_refl eq_refl eq_refl ▷
  rebuild_wf_env_transform (efl := efl'') false false ▷
  unbox_transformation efl'' final_wcbv_flags (has_app := _) (has_cofix := _) (has_prop_case := eq_refl) (has_letin := eq_refl) (has_cstrparams := eq_refl) (has_cstr_block := eq_refl) ▷
  implement_box_transformation efl'' eq_refl eq_refl eq_refl eq_refl eq_refl ▷
  ETransform.optional_self_transform econf.(enable_unsafe).(inductives_extraction)
    (rebuild_wf_env_transform (efl := efl''') false false ▷
       extract_inductive_transformation efl''' final_wcbv_flags econf.(extracted_inductives) ▷
       forget_inductive_extraction_info_transformation efl''' final_wcbv_flags) ▷
  (* Heuristically do it twice for more beta-normal terms *)
  ETransform.optional_self_transform econf.(enable_unsafe).(Erasure.betared)
    (betared_transformation efl''' final_wcbv_flags ▷
     betared_transformation efl''' final_wcbv_flags).
Next Obligation.
Proof.
  destruct econf as [[? ? [] ?] ? ? ? ? ?]; cbn in *; intuition eauto.
Qed.
Next Obligation.
Proof.
  destruct econf as [[? ? [] []] ? ? [] ? []]; cbn in *; intuition eauto.
Qed.

Program Definition run_erase_program {guard : PCUICWfEnvImpl.abstract_guard_impl} (econf : erasure_configuration)
  (p : Transform.program inductives_mapping template_program) : pre pre_erasure_pipeline_mapping p -> Transform.program global_context EAst.term :=
 if econf.(enable_typed_erasure) as _ return pre pre_erasure_pipeline_mapping p -> Transform.program global_context EAst.term then
    run (typed_erasure_pipeline econf ▷ certirocq_post_metarocq_pipeline econf) p
  else
   run (erasure_pipeline_mapping econf ▷ certirocq_post_metarocq_pipeline econf) p.
Next Obligation.
Proof.
  destruct econf as [[[] ? ? ?] ? ? [] ? ?]; cbn in *; intuition eauto.
Qed.
Next Obligation.
Proof.
  destruct econf as [[[] ? ? ?] ? ? [] ? []]; cbn in *; intuition eauto.
Qed.