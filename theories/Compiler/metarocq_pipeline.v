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
From MetaRocq.ErasurePlugin.transforms Require Import RebuildWfEnv CoInductiveToInductive
  Unboxing ConstsToValues ImplementBox ImplementLazyForce.
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
  (* Coinductives and cofixpoints have already been translated to inductive
     types and lazy fixpoints by the MetaRocq pipeline *)
  let efl' := efl_coind_to_ind efl in
  (* Rebuild the efficient lookup table *)
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
  destruct econf as [[? [] ?] ? ? ? ? ?]; cbn in *; intuition eauto.
Qed.
Next Obligation.
Proof.
  destruct econf as [[? [] []] ? ? [] ? []]; cbn in *; intuition eauto.
Qed.
Next Obligation.
Proof.
  destruct econf as [[? [] []] ? ? [] ? []]; cbn in *; intuition eauto.
Qed.

(** The full erasure pipeline used by CertiRocq: MetaRocq's (typed or untyped) erasure pipeline
    followed by [certirocq_post_metarocq_pipeline]. *)
Program Definition certirocq_erasure_pipeline {guard : PCUICWfEnvImpl.abstract_guard_impl}
  (extracted : list kername) (econf : erasure_configuration) :
  Transform.t inductives_mapping global_context template_program EAst.term Ast.term EAst.term
    eval_template_program_mapping (eval_eprogram final_wcbv_flags) :=
  if econf.(enable_typed_erasure) then
    typed_erasure_pipeline econf ▷ certirocq_post_metarocq_pipeline extracted econf
  else
    erasure_pipeline_mapping econf ▷ certirocq_post_metarocq_pipeline extracted econf.

Lemma certirocq_erasure_pipeline_pre {guard : PCUICWfEnvImpl.abstract_guard_impl} extracted econf p :
  pre pre_erasure_pipeline_mapping p ->
  pre (certirocq_erasure_pipeline (guard := guard) extracted econf) p.
Proof.
  unfold certirocq_erasure_pipeline. now destruct enable_typed_erasure.
Qed.

Definition run_erase_program {guard : PCUICWfEnvImpl.abstract_guard_impl} (extracted : list kername)
  (econf : erasure_configuration)
  (p : Transform.program inductives_mapping template_program) :
  pre (certirocq_erasure_pipeline extracted econf) p -> Transform.program global_context EAst.term :=
  run (certirocq_erasure_pipeline extracted econf) p.

(** * Well-formedness of the programs given to CertiRocq's backend *)

From Stdlib Require Import ssreflect ssrbool.
Import ETransform EImplementLazyForce EImplementBox.

(** The flags ensured by the postcondition of [certirocq_post_metarocq_pipeline] *)
Definition env_flags :=
  let efl := EConstructorsAsBlocks.switch_cstr_as_blocks
    (EInlineProjections.disable_projections_env_flag
      (ERemoveParams.switch_no_params EWellformed.all_env_flags)) in
  let efl' := efl_coind_to_ind efl in
  switch_off_thunk (switch_off_box efl').

(* CertiRocq does not support primitive arrays yet *)
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

(** The flags supported by CertiRocq's ANF correctness proof:
    - primitives are supported, but not primitive arrays;
    - the environment must be axiom free, as usual. *)
Definition certirocq_flags (efl : EEnvFlags) :=
  {| has_axioms := false;
     has_cstr_params := efl.(has_cstr_params);
     term_switches := set_primitives efl.(term_switches) no_primitive_array_flags;
     cstr_as_blocks := efl.(cstr_as_blocks) |}.

(** The flags checked by the pipeline on erased programs ([check_wellformed]). Axioms are allowed
    when [axioms] is true: they may be realized by registered primitives, which [check_axioms]
    checks precisely. *)
Definition certirocq_check_flags (axioms : bool) :=
  {| has_axioms := axioms;
     has_cstr_params := env_flags.(has_cstr_params);
     term_switches := set_primitives env_flags.(term_switches) no_primitive_array_flags;
     cstr_as_blocks := env_flags.(cstr_as_blocks) |}.

Lemma certirocq_check_flags_false : certirocq_check_flags false = certirocq_flags env_flags.
Proof. reflexivity. Qed.

(** Boolean decision procedure for [wf_eprogram]. To avoid linear lookups in the environment,
    well-formedness is checked using environment maps ([GlobalContextMap.t]), built
    incrementally from the oldest declaration. *)

From MetaRocq.Utils Require Import utils.
From MetaRocq.Erasure Require Import EEnvMap EInduction ELiftSubst.

Section WfMap.
  Context {efl : EEnvFlags} (Σ : GlobalContextMap.t).

  Definition wf_brs_map ind brsl :=
    match GlobalContextMap.lookup_inductive Σ ind with
    | Some (mib, oib) => #|oib.(ind_ctors)| == brsl
    | None => false
    end.

  (** [wellformed], using the lookup functions of the environment map *)
  Fixpoint wellformed_map k (t : term) : bool :=
    match t with
    | tRel i => has_tRel && Nat.ltb i k
    | tEvar ev args => has_tEvar && List.forallb (wellformed_map k) args
    | tLambda _ M => has_tLambda && wellformed_map (S k) M
    | tApp u v => has_tApp && wellformed_map k u && wellformed_map k v
    | tLetIn na b b' => has_tLetIn && wellformed_map k b && wellformed_map (S k) b'
    | tCase ind c brs => has_tCase &&
      let brs' := List.forallb (fun br => wellformed_map (#|br.1| + k) br.2) brs in
      wf_brs_map ind.1 #|brs| && wellformed_map k c && brs'
    | tProj p c => has_tProj && isSome (GlobalContextMap.lookup_projection Σ p) && wellformed_map k c
    | tFix mfix idx => has_tFix &&
      List.forallb (fun d => isLambda d.(dbody) || has_tLazy_Force && EAstUtils.isLazy d.(dbody)) mfix &&
      wf_fix_gen wellformed_map k mfix idx
    | tCoFix mfix idx => has_tCoFix &&
      List.forallb (fun d => EAst.isLambdas d.(rarg) d.(dbody)) mfix &&
      wf_fix_gen wellformed_map k mfix idx
    | tBox => has_tBox
    | tConst kn => has_tConst &&
      match GlobalContextMap.lookup_constant Σ kn with
      | Some d => has_axioms || isSome d.(cst_body)
      | _ => false
      end
    | tConstruct ind c block_args => has_tConstruct &&
      isSome (GlobalContextMap.lookup_constructor Σ ind c) &&
      if cstr_as_blocks then match GlobalContextMap.lookup_constructor_pars_args Σ ind c with
        | Some (p, a) => (p + a) == #|block_args|
        | _ => true end
        && forallb (wellformed_map k) block_args else is_nil block_args
    | tVar _ => has_tVar
    | tPrim p => has_prim p && EPrimitive.test_prim (wellformed_map k) p
    | tLazy t => has_tLazy_Force && wellformed_map k t
    | tForce t => has_tLazy_Force && wellformed_map k t
    end.

  Definition wf_global_decl_map d : bool :=
    match d with
    | ConstantDecl cb => option_default (fun b => wellformed_map 0 b) cb.(cst_body) has_axioms
    | InductiveDecl idecl => wf_minductive idecl
    end.

End WfMap.

Lemma wellformed_map_spec {efl : EEnvFlags} (Σ : GlobalContextMap.t) k t :
  wellformed_map Σ k t = wellformed Σ k t.
Proof.
  induction t in k |- * using EInduction.term_forall_list_ind; cbn;
    rewrite ?GlobalContextMap.lookup_projection_spec ?GlobalContextMap.lookup_constant_spec
      ?GlobalContextMap.lookup_constructor_spec ?GlobalContextMap.lookup_constructor_pars_args_spec;
    unfold wf_brs_map, wf_brs; rewrite ?GlobalContextMap.lookup_inductive_spec;
    rewrite ?IHt ?IHt1 ?IHt2 ?IHt3 //.
  all: try solve [f_equal; solve_all].
  all: try (unfold wf_fix_gen; do 2 f_equal; solve_all).
  - destruct cstr_as_blocks => //. f_equal. solve_all.
Qed.

Lemma wf_global_decl_map_spec {efl : EEnvFlags} (Σ : GlobalContextMap.t) d :
  wf_global_decl_map Σ d = wf_global_decl Σ d.
Proof.
  destruct d as [[[]]|] => //=. apply wellformed_map_spec.
Qed.

Lemma lookup_env_None_fresh Σ kn :
  EGlobalEnv.lookup_env Σ kn = None -> EGlobalEnv.fresh_global kn Σ.
Proof.
  induction Σ as [|[kn' d] Σ IH]; cbn; constructor.
  - cbn. case: (ReflectEq.eqb_spec kn kn') H => // hneq _. congruence.
  - apply IH. now destruct ReflectEq.eqb.
Qed.

Lemma lookup_env_map_None_fresh (Σ : GlobalContextMap.t) kn :
  GlobalContextMap.lookup_env Σ kn = None -> EGlobalEnv.fresh_global kn Σ.
Proof.
  rewrite GlobalContextMap.lookup_env_spec. apply lookup_env_None_fresh.
Qed.

Definition option_None_dec {A} (o : option A) : {o = None} + {o <> None} :=
  match o return {o = None} + {o <> None} with
  | None => left eq_refl
  | Some a => right (fun h : Some a = None =>
      match h in _ = y return match y with None => False | Some _ => True end with eq_refl => I end)
  end.

(** Returns the environment map of [Σ] if it is well-formed *)
Fixpoint check_wf_glob {efl : EEnvFlags} (Σ : global_declarations) : option GlobalContextMap.t :=
  match Σ with
  | [] => Some GlobalContextMap.empty
  | (kn, d) :: Σ =>
    match check_wf_glob Σ with
    | None => None
    | Some m =>
      match option_None_dec (GlobalContextMap.lookup_env m kn) with
      | left hl =>
        if wf_global_decl_map m d then
          Some (GlobalContextMap.add m kn d (lookup_env_map_None_fresh m kn hl))
        else None
      | right _ => None
      end
    end
  end.

Definition check_wf_eprogram (efl : EEnvFlags) (p : eprogram) : bool :=
  match @check_wf_glob efl (fst p) with
  | Some m => @wellformed_map efl m 0 (snd p)
  | None => false
  end.

Lemma check_wf_glob_spec {efl : EEnvFlags} Σ m :
  check_wf_glob Σ = Some m -> wf_glob Σ /\ GlobalContextMap.global_decls m = Σ.
Proof.
  induction Σ as [|[kn d] Σ IH] in m |- *; cbn.
  - intros [= <-]. split => //. constructor.
  - destruct (check_wf_glob Σ) as [m'|] => //.
    specialize (IH _ eq_refl) as [wfΣ heq].
    destruct option_None_dec as [hl|] => //.
    destruct wf_global_decl_map eqn:hd => //. intros [= <-]. cbn.
    rewrite wf_global_decl_map_spec heq in hd. split; [|now rewrite heq].
    constructor => //. rewrite -heq. now apply lookup_env_map_None_fresh.
Qed.

Lemma check_wf_eprogram_spec efl p : check_wf_eprogram efl p -> wf_eprogram efl p.
Proof.
  unfold check_wf_eprogram.
  destruct check_wf_glob as [m|] eqn:hm => // ht.
  apply check_wf_glob_spec in hm as [wfΣ heq].
  rewrite wellformed_map_spec heq in ht. now split.
Qed.
