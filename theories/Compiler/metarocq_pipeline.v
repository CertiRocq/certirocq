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
From MetaRocq.Utils Require Import MRSquash.
From MetaRocq.Erasure Require EGlobalEnv EPrimitive EWcbvEval.

(** [consts_to_values] forces every constant. For axioms and for constants implemented in C
    ([Extract Constants], [CertiRocq Register]), CertiRocq calls the C function directly, so
    the force only adds a spurious [□] argument to every call. This pass removes the force
    on those constants; [extracted] lists the ones implemented in C.
    TODO: prove [unforce_axioms_transformation] correct. *)
Section UnforceAxioms.
  Context (extracted : list kername) (Σ : EAst.global_context).

  Definition unforce (kn : kername) : bool :=
    orb (existsb (fun kn' => ReflectEq.eqb kn kn') extracted)
        (match EGlobalEnv.lookup_constant Σ kn with
         | Some cb => match cb.(cst_body) with None => true | Some _ => false end
         | None => false
         end).

  Fixpoint unforce_axioms (t : term) : term :=
    match t with
    | tForce (tConst kn) => if unforce kn then tConst kn else tForce (tConst kn)
    | tLambda nm bod => tLambda nm (unforce_axioms bod)
    | tLetIn nm dfn bod => tLetIn nm (unforce_axioms dfn) (unforce_axioms bod)
    | tApp fn arg => tApp (unforce_axioms fn) (unforce_axioms arg)
    | tConstruct i m args => tConstruct i m (map unforce_axioms args)
    | tCase i mch brs =>
        tCase i (unforce_axioms mch) (map (fun br => (fst br, unforce_axioms (snd br))) brs)
    | tFix mfix idx => tFix (map (EAst.map_def unforce_axioms) mfix) idx
    | tCoFix mfix idx => tCoFix (map (EAst.map_def unforce_axioms) mfix) idx
    | tProj p bod => tProj p (unforce_axioms bod)
    | tPrim p => tPrim (EPrimitive.map_prim unforce_axioms p)
    | tLazy t => tLazy (unforce_axioms t)
    | tForce t => tForce (unforce_axioms t)
    | tEvar ev args => tEvar ev (map unforce_axioms args)
    | tVar _ | tRel _ | tBox | tConst _ => t
    end.
End UnforceAxioms.

Definition unforce_axioms_env extracted (Σ : EAst.global_context) : EAst.global_context :=
  map (fun d => (fst d, match snd d with
                        | ConstantDecl cb =>
                            ConstantDecl {| cst_body := option_map (unforce_axioms extracted Σ) cb.(cst_body) |}
                        | InductiveDecl idecl => InductiveDecl idecl
                        end)) Σ.

Definition unforce_axioms_program extracted (p : eprogram) : eprogram :=
  (unforce_axioms_env extracted (fst p), unforce_axioms extracted (fst p) (snd p)).

Program Definition unforce_axioms_transformation (extracted : list kername) (efl : EEnvFlags)
  (wfl : EWcbvEval.WcbvFlags) :
  Transform.t _ _ EAst.term EAst.term _ _ (eval_eprogram wfl) (eval_eprogram wfl) :=
  {| name := "Unforce axioms"%bs;
     transform p _ := unforce_axioms_program extracted p;
     pre p := wf_eprogram efl p /\ ∥ EWcbvEval.lazy_glob (fst p) ∥;
     post p := wf_eprogram efl p /\ ∥ EWcbvEval.lazy_glob (fst p) ∥;
     obseq p hp p' v v' := v' = unforce_axioms extracted (fst p) v |}.
Admit Obligations.

(** The CertiRocq MetaRocq pipeline is composed of the verified typed or untyped MetaRocq pipelines plus:

    - CoFixpoints to fixpoints (unverified, only relevant if the source term contains cofixpoints)
    - Transformation of constants to values (verified, simplifies the ANF proof)
    - Transformation of lazy/force to lambda abstractions and applications (verified)
    - Unboxing of single argument constructors (verified)
    - Implementation of "box" as a fixpoint expression (verified) *)

Program Definition certirocq_post_metarocq_pipeline (extracted : list kername) econf :
  Transform.t global_context global_context term term term term
  (eval_eprogram final_wcbv_flags)
  (eval_eprogram final_wcbv_flags) :=
  let efl := EConstructorsAsBlocks.switch_cstr_as_blocks
  (EInlineProjections.disable_projections_env_flag
   (ERemoveParams.switch_no_params EWellformed.all_env_flags)) in
  let efl' := efl_coind_to_ind efl in
  (* Rebuild the efficient lookup table *)
  rebuild_wf_env_transform (efl := efl) false false ▷
  (* Coinductives & cofixpoints are translated to inductive types and thunked fixpoints *)
  coinductive_to_inductive_transformation efl
      (has_app := eq_refl) (has_rel := eq_refl) 
      (has_pars := eq_refl) (has_cstrblocks := eq_refl) ▷
  (* Lazy-to-lambda *)
  rebuild_wf_env_transform (efl := efl') false false ▷
  unbox_transformation efl' final_wcbv_flags (has_app := _) (has_cofix := _) (has_prop_case := eq_refl) (has_letin := eq_refl) (has_cstrparams := eq_refl) (has_cstr_block := eq_refl) ▷
  ETransform.optional_self_transform econf.(enable_unsafe).(inductives_extraction)
    (rebuild_wf_env_transform (efl := efl') false false ▷
       extract_inductive_transformation efl' final_wcbv_flags econf.(extracted_inductives) ▷
       forget_inductive_extraction_info_transformation efl' final_wcbv_flags) ▷
  (* Heuristically do it twice for more beta-normal terms *)
  ETransform.optional_self_transform econf.(enable_unsafe).(Erasure.betared)
    (betared_transformation efl' final_wcbv_flags ▷
     betared_transformation efl' final_wcbv_flags) ▷  
  consts_to_values_transformation efl' final_wcbv_flags eq_refl eq_refl eq_refl ▷
  unforce_axioms_transformation extracted efl' final_wcbv_flags ▷
  implement_lazy_force_transformation efl' eq_refl eq_refl eq_refl eq_refl eq_refl true ▷
  implement_box_transformation (switch_off_thunk efl') eq_refl eq_refl eq_refl eq_refl eq_refl true.
Next Obligation.
Proof.
  destruct econf as [[? ? [] ?] ? ? ? ? ?]; cbn in *; intuition eauto.
Qed.
Next Obligation.
Proof.
  destruct econf as [[? ? [] []] ? ? [] ? []]; cbn in *; intuition eauto.
Qed.
Next Obligation.
Proof.
  destruct econf as [[? ? [] []] ? ? [] ? []]; cbn in *; intuition eauto.
Qed.

Program Definition run_erase_program {guard : PCUICWfEnvImpl.abstract_guard_impl} (extracted : list kername)
  (econf : erasure_configuration)
  (p : Transform.program inductives_mapping template_program) : pre pre_erasure_pipeline_mapping p -> Transform.program global_context EAst.term :=
 if econf.(enable_typed_erasure) as _ return pre pre_erasure_pipeline_mapping p -> Transform.program global_context EAst.term then
    run (typed_erasure_pipeline econf ▷ certirocq_post_metarocq_pipeline extracted econf) p
  else
   run (erasure_pipeline_mapping econf ▷ certirocq_post_metarocq_pipeline extracted econf) p.
Next Obligation.
Proof.
  destruct econf as [[[] ? ? ?] ? ? [] ? ?]; cbn in *; intuition eauto.
Qed.
Next Obligation.
Proof.
  destruct econf as [[[] ? ? ?] ? ? [] ? []]; cbn in *; intuition eauto.
Qed.