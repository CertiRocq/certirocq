From Stdlib Require Import ssreflect ssrbool.
From Equations Require Import Equations.

Require Export LambdaANF.toplevel Codegen.toplevel CodegenWasm.toplevel.
Require Import LambdaBox_to_LambdaANF.fuel_sem.
Require Import LambdaBox_to_LambdaANF.common.
Require Import LambdaBox_to_LambdaANF.anf.
Require Import LambdaBox_to_LambdaANF.anf_correct.
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

Definition next_id := 100%positive.
Definition econf := Erasure.default_erasure_config.
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
Definition no_primitive_flags := {|
  has_primint := false;
  has_primfloat := false;
  has_primstring := false;
  has_primarray := false; |}.
  
Definition switch_off_primitives (fl : ETermFlags) :=
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
  ; has_tPrim := no_primitive_flags
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

Definition inj_conIdMap tgm :=
  (forall dc dc' tg, dcon_to_tag dc tgm = Some tg ->
     dcon_to_tag dc' tgm = Some tg -> dc = dc').

Definition bounded_conIdMap (tgm : conId_map) p :=
  Forall (fun '(ind', nCon', tg) => tg < p)%positive tgm.
Inductive fromNP p : nat -> list positive -> positive -> Prop :=
| fromN0 : fromNP p 0 [] p
| fromNS n l p' : fromNP (p + 1)%positive n l p' -> fromNP p (S n) (Tcons p l) p'.

Lemma fromN_spec p n : fromNP p n (fromN p n).1 (fromN p n).2.
Proof.
  induction n in p |- *; cbn.
  - constructor.
  - destruct fromN eqn:hf.
    constructor. specialize (IHn (p + 1)%positive).
    rewrite hf in IHn. apply IHn.
Qed.

Lemma dcon_to_info_all_lt {dc tgm tg P} : dcon_to_info dc tgm = Some tg -> Forall (fun '(_, _, tg) => P tg) tgm -> P tg.
Proof.
  induction tgm; cbn; auto.
  - intros [=].
  - destruct a. destruct conId_dec.
    + intros [= <-].
      intros hf; depelim hf. now destruct d as [].
      move/IHtgm.
      intros ih hf; depelim hf. apply ih, hf.
Qed.

Lemma convert_cnstrs_tgm itypNm l cstrs ncstrs ind nCon unboxed boxed i0 c tgm cenv' tgm' p p' : 
  fromNP p ncstrs l p' ->
  ncstrs = #|cstrs| ->
  convert_cnstrs itypNm l cstrs ind nCon unboxed boxed i0 c tgm = (cenv', tgm') ->
  inj_conIdMap tgm ->
  bounded_conIdMap tgm p -> 
  inj_conIdMap tgm' /\ bounded_conIdMap tgm' p'.
Proof.
  induction 1 in cstrs, nCon, unboxed, boxed, i0, c, tgm |- *.
   (* in cstrs, ind, nCon, unboxed, boxed, i0, c, tgm |- *. *)
  - cbn. now intros ? [= <- <-].
  - cbn. destruct cstrs => //.
    cbn. intros [= ->]. 
    destruct c0 as [cname ccn].
    move/IHfromNP => IH. specialize (IH eq_refl).
    intros injm hlt.
    apply IH.
    clear -injm hlt.
    { intros dc dc' tg; cbn.
      destruct conId_dec; subst.
      intros [=]. subst p.
      destruct conId_dec; subst.
      intros [=]. reflexivity.
      have h := (dcon_to_info_all_lt _ hlt).
      move/h. lia.
      destruct conId_dec. subst.
      intros hd [= <-].
      have h := (dcon_to_info_all_lt hd hlt). lia.
      apply injm. }
    constructor. lia.
    eapply Forall_impl; tea. intros [[] ?]. lia.
Qed.

Lemma convert_typack_tgm ty id n acc acc' : convert_typack ty id n acc = acc' -> 
  inj_conIdMap acc.2 -> bounded_conIdMap acc.2 acc.1.1.2 -> 
  inj_conIdMap acc'.2 /\ bounded_conIdMap acc'.2 acc'.1.1.2.
Proof.
  induction ty in n, acc, acc' |- *.
  - destruct acc as ((((? & ?) & ?) & ?) & tgm); cbn.
    intros <-. now cbn.
  - destruct acc as ((((? & ?) & cn) & ?) & tgm); cbn.
    destruct acc' as ((((? & ?) & cn') & ?) & tgm'); cbn.
    destruct a as [itypNm cstrs].
    destruct fromN eqn:hfr.
    destruct convert_cnstrs eqn:eqcs.
    move/IHty. cbn.
    intros h2 inj0 hb.
    eapply convert_cnstrs_tgm in eqcs. apply h2. apply eqcs. apply eqcs.
    have he := fromN_spec cn #|cstrs|. rewrite hfr //= in he. exact he. 
    reflexivity. exact inj0. exact hb.
Qed.

Lemma convert_env'_tgm ie acc acc' : convert_env' ie acc = acc' -> 
  inj_conIdMap acc.2 -> bounded_conIdMap acc.2 acc.1.1.2 -> 
  inj_conIdMap acc'.2 /\ bounded_conIdMap acc'.2 acc'.1.1.2.
Proof.
  induction ie in acc, acc' |- *.
  - destruct acc as ((((? & ?) & ?) & ?) & tgm); cbn.
    intros <-. now cbn.
  - destruct acc as ((((? & ?) & ?) & ?) & tgm); cbn.
  - destruct acc' as ((((? & ?) & ?) & ?) & tgm'); cbn.
    destruct a as [id ty].
    intros ce' injtgm btgm.
    have hc := convert_typack_tgm ty id 0 (i, c, c0, i0, tgm) _ eq_refl injtgm btgm.
    eapply IHie in ce'; auto. apply hc. apply hc.
Qed.

Lemma convert_env_inj default_tag default_itag ie : 
  let tgm := (convert_env default_tag default_itag ie).2 in
  inj_conIdMap tgm.
Proof.
  unfold convert_env. cbn.
  have he := convert_env'_tgm ie _ _ eq_refl.
  apply he. cbn. red. cbn => //.
  cbn. red. constructor.
Qed.

Import anf_corresp.

Lemma convert_env_reg default_tag default_itag Σ : 
  let ie := inductive_env_east Σ in
  let tgm := (convert_env default_tag default_itag ie).2 in
  registered_constructors tgm Σ.
Proof.
Admitted.

Section Assumptions.

  Context (func_tag kon_tag default_tag default_itag : positive).
  
  (* This property should come from the well-formedness of terms w.r.t. their global environment, 
    currently missing in the ANF proof. 
    The list of [ctor_tag × exp] is built from the [ind] annotation of the Case construct in the anf, 
    and these lemma is used where [ctag] is built from [ind] as well. *)
  Context (casecon : forall p : EProgram.eprogram, 
    let ie := inductive_env_east (fst p) in
    forall (P : list (ctor_tag × exp)) (ctag : ctor_tag), 
    term_util.caseConsistent (top_cenv default_tag default_itag ie) 
      P ctag).

  Notation refines_top Σ ie tgm := (@refines_top default_tag default_itag tgm Σ ie).

  (** To prove the correctness of connecting the MetaRocq pipeline and CertiRocq's ANF, we
      need a stronger well-formedness property. This formalizes the remaining mismatch 
      between metarocq's pipeline and certirocq's LambdaANF: 

    - primitives are not supported in fuel_sem, and primitive arrays are forbidden in ANF conversion.
    - the environment must be axiom free, as usual *)


  Definition certirocq_flags (efl : EEnvFlags) := 
    {| has_axioms := false; 
       has_cstr_params := efl.(has_cstr_params); 
       term_switches := disable_box_term_flags (switch_off_primitives efl.(term_switches));
       cstr_as_blocks := efl.(cstr_as_blocks) |}.

  Definition anf_convert ie tgm := 
    convert_top_anf func_tag default_tag (M.empty _) default_itag next_id tgm []
      (fun _ => None) ie.
  
  Theorem correctness_from_erasure (p : EProgram.eprogram) : 
    (* The postcondition on MetaRocq's pipeline *)
    Transform.Transform.post (certirocq_post_metarocq_pipeline econf) p ->
    (* Stronger invariant: no axioms, no primitives *)
    EProgram.wf_eprogram (certirocq_flags env_flags) p ->
    let ie := inductive_env_east (fst p) in
    let tgm := (convert_env default_tag default_itag ie).2 in
    forall e_tgt comp_d', 
      anf_convert ie tgm (List.rev (fst p)) (snd p) = (compM.Ret e_tgt, comp_d') ->
      exists M, refines_top (fst p) ie tgm M (snd p) e_tgt.
  Proof.
    intros hp wf' ie tgm e_tgt comp_d' cvt.
    cbn in hp.
    match goal with
    | [ _ : EProgram.wf_eprogram ?fl p /\ _ |- _ ] => set (efl := fl) in *
    end.
    destruct hp as [wfp [vg]].
    eapply (convert_top_anf_correct func_tag kon_tag default_tag default_itag tgm (fst p) 
      (efl:=certirocq_flags (switch_off_box env_flags))); trea.
    - (* The conId_map is injective *)
      apply convert_env_inj.
    - (* The constructors are registered *)
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
      clear wfp. destruct wf' as [wfΣ wf].       
      intros kn decl body hdecl hb.
      eapply (lookup_env_wellformed (efl := certirocq_flags (switch_off_box env_flags))) in hdecl; tea.
      destruct decl; trivial. cbn in hdecl. cbn in hb.
      now subst cst_body.
    - apply wf'.
    - (* No prims *)
      intros s. cbn. reflexivity.
    - apply casecon.
    - apply wf'.
  Qed.

End Assumptions.
About correctness_from_erasure.