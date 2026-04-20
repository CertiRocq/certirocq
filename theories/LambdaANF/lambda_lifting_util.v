(* Computational definition and declarative spec for lambda lifting. Part of the CertiRocq project.
 * Author: Anonymized, 2016
 *)

Require Import Common.compM.
Require Import LambdaANF.alpha_conv LambdaANF.term LambdaANF.term_util LambdaANF.ctx LambdaANF.state LambdaANF.set_util LambdaANF.identifiers LambdaANF.List_util
        LambdaANF.functions LambdaANF.Ensembles_util LambdaANF.uncurry LambdaANF.tactics LambdaANF.lambda_lifting.
From Stdlib Require Import ZArith.Znumtheory Strings.String.
From Stdlib Require Import Lists.List MSets.MSets MSets.MSetRBT Numbers.BinNums
        NArith.BinNat PArith.BinPos Sets.Ensembles.
Require Import ExtLib.Structures.Monads ExtLib.Data.Monads.StateMonad ExtLib.Data.Monads.OptionMonad.
Require Import compcert.lib.Coqlib.

Import ListNotations Nnat MonadNotation PS.
Require Import compcert.lib.Maps.

Close Scope Z_scope.
Open Scope monad_scope.


(** * Syntactic properties of  the lambda lifting relation *)

Lemma Exp_lambda_lift_Ecase zeta sig x Pats S e S' :
  Exp_lambda_lift zeta sig (Ecase x Pats) S e S' ->
  exists Pats', e = Ecase (sig x) Pats' /\ Forall2 (fun p p' : ctor_tag * exp => fst p = fst p') Pats Pats'.
Proof.
  revert S S' e; induction Pats; intros S S' e Hexp; inv Hexp.
  - eexists; eauto.
  - eapply IHPats in H8. edestruct H8 as [P'' [Heq Hall]]. inv Heq.
    eexists; eauto.
Qed.

(** * Lemmas about [lifted_name], [Funs], [LiftedFuns], [FunsFVs] and [FunsFVsLst] *)

Lemma lifted_name_extend f x x' xs l :
  f_eq (lifted_name (f {x ~> Some (x', xs, l)})) ((lifted_name f) { x ~> Some x' }).
Proof.
  intros y. unfold lifted_name; simpl.
  destruct (peq x y); subst.
  - rewrite !extend_gss. reflexivity.
  - rewrite !extend_gso; eauto.
Qed.

Lemma lifted_name_eq f x x' xs l :
  f x = Some (x', xs, l) ->
  lifted_name f x = Some x'.
Proof.
  intros Heq; unfold lifted_name; rewrite Heq; eauto.
Qed.

Lemma Funs_extend_Some zeta f f' ft fvs :
  Included _ (Funs (zeta {f ~> Some (f', ft, fvs)}))
           (Union _ (Funs zeta) (Singleton _ f)).
Proof.
  intros x [val H].
  destruct (peq f x); subst.
  - rewrite lifted_name_extend, extend_gss in H. inv H. eauto.
  - rewrite lifted_name_extend, extend_gso in H; eauto.
    left. eexists; eauto.
Qed.

Lemma LiftedFuns_extend_Some zeta f f' ft fvs :
  Included _ (LiftedFuns (zeta {f ~> Some (f', ft, fvs)}))
           (Union _ (LiftedFuns zeta) (Singleton _ f')).
Proof.
  intros x [g [H1 H2]].
  destruct (peq f g); subst; rewrite lifted_name_extend in H2;
    apply Funs_extend_Some in H1.
  - rewrite extend_gss in H2. inv H2. eauto.
  - rewrite extend_gso in H2; eauto. inv H1; eauto.
    left. repeat eexists; eauto.
    inv H; congruence.
Qed.

Lemma FunsFVs_extend_Some zeta f f' ft fvs :
  Included _ (FunsFVs (zeta {f ~> Some (f', ft, fvs)}))
           (Union _ (FunsFVs zeta) (FromList fvs)).
Proof.
  intros x [g [g' [gt' [fvs' [H1 H2]]]]].
  destruct (peq f g); subst.
  - rewrite extend_gss in H1. inv H1. eauto.
  - rewrite extend_gso in H1; eauto.
    left. eexists; eauto.
Qed.

Lemma FunsFVs_extend_Some_eq zeta f f' ft fvs :
  ~ f \in Funs zeta ->
          Same_set var (FunsFVs (zeta {f ~> Some (f', ft, fvs)}))
                   (Union var (FunsFVs zeta) (FromList fvs)).
Proof.
  intros Hn; split.
  - now apply FunsFVs_extend_Some.
  - intros x Hin. inv Hin.
    destruct H as [g [g' [fg [l [Heq Hin]]]]].
    repeat eexists; eauto. rewrite extend_gso.
    eassumption. intros Hc; apply Hn. subst.
    repeat eexists; eauto. eapply lifted_name_eq.
    subst. eassumption.
    repeat eexists; eauto. rewrite extend_gss.
    reflexivity.
Qed.

Lemma lifted_name_f_eq_subdomain S f1 f2 :
  f_eq_subdomain S f1 f2 ->
  f_eq_subdomain S (lifted_name f1) (lifted_name f2).
Proof.
  intros Heq x Hin. unfold lifted_name. simpl; rewrite Heq; eauto.
Qed.

(** * Lemmas about [Add_functions] *)

Lemma Add_functions_free_set_Included B fvs zeta sig S zeta' sig' S' :
  Add_functions B fvs zeta sig S zeta' sig' S' ->
  Included _ S' S.
Proof with now eauto with Ensembles_DB.
  intros Hadd. induction Hadd...
Qed.

Lemma Add_functions_fvs_eq B fvs sig zeta S sig' zeta' S' f f' ft fvs' :
  Add_functions B fvs sig zeta S sig' zeta' S' ->
  zeta' f = Some (f', ft, fvs') ->
  f \in name_in_fundefs B ->
        fvs' = fvs.
Proof.
  intros Hadd Heq Hin; induction Hadd.
  - destruct (peq f f0); subst.
    + rewrite extend_gss in Heq. inv Heq. eauto.
    + inv Hin. inv H0; congruence.
      rewrite extend_gso in Heq; eauto.
  - inv Hin.
Qed.

Lemma Add_functions_eq B fvs sig zeta S sig' zeta' S' f :
  ~ f \in name_in_fundefs B ->
          Add_functions B fvs sig zeta S sig' zeta' S' ->
          zeta' f = zeta f.
Proof.
  intros Hin Hadd; induction Hadd.
  - rewrite extend_gso. eapply IHHadd.
    + intros Hc. eapply Hin. now right.
    + intros Hc. subst. eapply Hin. left. reflexivity.
  - reflexivity.
Qed.

Lemma Add_functions_image_Included Q B fvs sig zeta S sig' zeta' S' :
  Add_functions B fvs sig zeta S sig' zeta' S' ->
  (image sig' Q) \subset
               ((image sig (Q \\ ((name_in_fundefs B) :|: (S \\ S')))) :|: (name_in_fundefs B :|: (S \\ S'))).
Proof with now eauto with Ensembles_DB.
  intros Hadd. revert Q. induction Hadd; intros Q.
  - eapply Included_trans. now eapply image_extend_Included'.
    eapply Union_Included.
    eapply Included_trans. now eapply image_extend_Included'.
    eapply Union_Included; [| now eauto with Ensembles_DB ].
    eapply Included_trans. eapply IHHadd.
    simpl. eapply Included_Union_compat.
    rewrite !Setminus_Union. eapply image_monotonic.
    eapply Included_Setminus_compat. reflexivity.
    apply Union_Included. now eauto with Ensembles_DB.
    eapply Included_trans. eapply Setminus_Setminus_Included.
    now eauto with typeclass_instances.
    now eauto with Ensembles_DB.
    apply Union_Included. now eauto with Ensembles_DB.
    apply Included_Union_preserv_r. apply Included_Setminus_compat.
    reflexivity. now eauto with Ensembles_DB.
    simpl. do 2 apply Included_Union_preserv_r.
    apply Singleton_Included. constructor.
    eapply Add_functions_free_set_Included; now eauto.
    intros Hc; inv Hc; eauto.
  - simpl. rewrite Setminus_Same_set_Empty_set at 1.
    rewrite Setminus_Same_set_Empty_set at 1.
    repeat rewrite Union_Empty_set_neut_r at 1.
    rewrite Setminus_Empty_set_neut_r. reflexivity.
Qed.

Lemma Add_functions_LiftedFuns_Included_r B fvs sig zeta S sig' zeta' S' :
  Add_functions B fvs sig zeta S sig' zeta' S' ->
  Included _ (LiftedFuns zeta') (Union _ (LiftedFuns zeta) (Setminus _ S S')).
Proof with now eauto with Ensembles_DB.
  intros Hadd. induction Hadd.
  - eapply Included_trans.
    eapply LiftedFuns_extend_Some.
    eapply Union_Included.
    eapply Included_trans. now eapply IHHadd.
    now eauto with Ensembles_DB.
    eapply Included_Union_preserv_r.
    eapply Singleton_Included. constructor.
    eapply Add_functions_free_set_Included; eassumption.
    intros Hc. inv Hc. eauto.
  - now eauto with Ensembles_DB.
Qed.


Lemma Add_functions_lifted_name_Same_set B fvs sig zeta S sig' zeta' S' Q :
  unique_bindings_fundefs B ->
  Disjoint _ Q (name_in_fundefs B) ->
  Add_functions B fvs sig zeta S sig' zeta' S' ->
  Same_set _ (image' (lifted_name zeta') (Union _ Q (name_in_fundefs B)))
           (Union _ (image' (lifted_name zeta) Q) (Setminus _ S S')).
Proof with now eauto with Ensembles_DB.
  intros Hun HD Hadd. revert Q HD; induction Hadd; intros Q HD.
  - inv Hun. rewrite lifted_name_extend. simpl.
    rewrite image'_extend_is_Some_In_P.
    rewrite !Setminus_Union_distr, Setminus_Same_set_Empty_set, Union_Empty_set_neut_l.
    rewrite (Setminus_Disjoint (name_in_fundefs B)).
    rewrite IHHadd, Setminus_Setminus_Same_set.
    rewrite Setminus_Disjoint, Union_assoc...
    now eauto with typeclass_instances.
    apply Singleton_Included.
    now eapply Add_functions_free_set_Included; eauto.
    eassumption.
    eapply Disjoint_Included; [| | now apply HD ]...
    eapply Disjoint_Included_l. now apply name_in_fundefs_bound_var_fundefs.
    eapply Disjoint_Singleton_r. eassumption.
    now eauto with Ensembles_DB.
  - simpl. rewrite Union_Empty_set_neut_r, Setminus_Same_set_Empty_set, Union_Empty_set_neut_r...
Qed.

Lemma Add_functions_Funs_Included B fvs sig zeta S sig' zeta' S' :
  Add_functions B fvs sig zeta S sig' zeta' S' ->
  Included _ (Funs zeta') (Union _ (Funs zeta) (name_in_fundefs B)).
Proof with now eauto with Ensembles_DB.
  intros Hadd. induction Hadd.
  - eapply Included_trans.
    eapply Funs_extend_Some.
    eapply Union_Included.
    eapply Included_trans. now eapply IHHadd.
    now eauto with Ensembles_DB.
    eapply Included_Union_preserv_r...
  - now eauto with Ensembles_DB.
Qed.

Lemma Add_functions_Funs_Same_set B fvs sig zeta S sig' zeta' S' :
  Add_functions B fvs sig zeta S sig' zeta' S' ->
  Same_set _ (Funs zeta') (Union _ (Funs zeta) (name_in_fundefs B)).
Proof with now eauto with Ensembles_DB.
  intros Hadd. induction Hadd.
  - unfold Funs. rewrite lifted_name_extend, domain_extend_is_Some_Same_set, IHHadd.
    simpl. unfold Funs...
  - rewrite Union_Empty_set_neut_r...
Qed.

Lemma Add_functions_LiftedFuns_Included_l B fvs sig zeta S sig' zeta' S' :
  Add_functions B fvs sig zeta S sig' zeta' S' ->
  unique_bindings_fundefs B ->
  Disjoint _ (Funs zeta) (name_in_fundefs B) ->
  Included _ (LiftedFuns zeta)  (LiftedFuns zeta').
Proof with now eauto  with Ensembles_DB.
  intros Hadd Hun HD. unfold LiftedFuns.
  rewrite Add_functions_Funs_Same_set with (zeta' := zeta'); eauto.
  rewrite Add_functions_lifted_name_Same_set; eauto.
  now eauto with Ensembles_DB.
Qed.

Lemma Add_functions_FunsFVs_Included_r B fvs sig zeta S sig' zeta' S' :
  Add_functions B fvs sig zeta S sig' zeta' S' ->
  Included _ (FunsFVs zeta') (Union _ (FunsFVs zeta) (FromList fvs)).
Proof with now eauto with Ensembles_DB.
  intros Hadd. induction Hadd.
  - eapply Included_trans.
    eapply FunsFVs_extend_Some.
    eapply Union_Included.
    eapply Included_trans. now eapply IHHadd.
    now eauto with Ensembles_DB.
    eapply Included_Union_preserv_r...
  - now eauto with Ensembles_DB.
Qed.

Lemma Add_functions_FunsFVs_Included_l B fvs sig zeta S sig' zeta' S' :
  Add_functions B fvs sig zeta S sig' zeta' S' ->
  unique_bindings_fundefs B ->
  Disjoint _ (Funs zeta) (name_in_fundefs B) ->
  Included _ (FunsFVs zeta) (FunsFVs zeta').
Proof with now eauto with Ensembles_DB.
  intros Hadd Hun HD. induction Hadd.
  - inv Hun. eapply Included_trans. eapply IHHadd.
    eassumption. now eauto with Ensembles_DB.
    rewrite FunsFVs_extend_Some_eq.
    now eauto with Ensembles_DB.
    intros Hc.
    eapply Add_functions_Funs_Included in Hc; [| eassumption ].
    inv Hc. eapply HD. constructor; eauto. left; eauto.
    eapply H6. apply name_in_fundefs_bound_var_fundefs. eassumption.
  - now eauto with Ensembles_DB.
Qed.

Lemma Add_functions_sig_eq B fvs sig zeta S sig' zeta' S' :
  Add_functions B fvs sig zeta S sig' zeta' S' ->
  f_eq_subdomain (Complement _ (Union _ (name_in_fundefs B) (Setminus _ S S'))) sig sig'.
Proof.
  intros Hadd. induction Hadd; simpl.
  - eapply f_eq_subdomain_extend_not_In_S_r.
    intros Hc; apply Hc.
    eapply Singleton_Included. right. constructor.
    eapply Add_functions_free_set_Included; eassumption.
    intros Hc'. inv Hc'. now eauto. now eauto.
    eapply f_eq_subdomain_extend_not_In_S_r.
    intros Hc; apply Hc. now eauto.
    eapply f_eq_subdomain_antimon; [| eassumption ].
    now eauto with Ensembles_DB.
  - reflexivity.
Qed.

Lemma Add_functions_lifted_name_Disjoint B fvs sig zeta S sig' zeta' S' :
  Add_functions B fvs sig zeta S sig' zeta' S' ->
  unique_bindings_fundefs B ->
  Disjoint _ (LiftedFuns zeta) S ->
  Disjoint _ (image (lifted_name zeta') (name_in_fundefs B))
           (image (lifted_name zeta') (Complement _ (name_in_fundefs B))).
Proof.
  intros Hadd Hun HD. induction Hadd; simpl.
  - inv Hun. rewrite image_Union. apply Union_Disjoint_l.
    rewrite image_Singleton.
    rewrite !lifted_name_extend, !extend_gss.
    rewrite image_extend_not_In_S; eauto.
    constructor. intros x Hc. inv Hc. inv H0.
    destruct H1 as [x' [Hin Heq]].
    assert (Hin' : f' \in LiftedFuns ζ').
    now repeat eexists; eauto.
    eapply Add_functions_LiftedFuns_Included_r in Hin'; [| eassumption ].
    inv Hin'. eapply HD.  constructor; eauto.
    eapply Add_functions_free_set_Included; eassumption.
    inv H0; eauto.
    eapply Disjoint_Included; [| | now apply IHHadd ].
    rewrite lifted_name_extend. rewrite image_extend_not_In_S; eauto.
    apply image_monotonic...
    now eauto with Ensembles_DB.
    rewrite lifted_name_extend. rewrite image_extend_not_In_S; eauto.
    reflexivity. intros Hc. eapply H6.
    now eapply name_in_fundefs_bound_var_fundefs.
  - rewrite image_Empty_set. now eauto with Ensembles_DB.
Qed.


Lemma Add_functions_map_eq B fvs sig zeta S sig' zeta' S' l :
  Add_functions B fvs sig zeta S sig' zeta' S' ->
  Disjoint _ (FromList l) (Union _ (name_in_fundefs B) (Setminus _ S S'))->
  map sig l = map sig' l.
Proof.
  intros Hadd HD. induction l; eauto.
  simpl. rewrite FromList_cons in HD.
  erewrite Add_functions_sig_eq; [| eassumption |].
  rewrite IHl. reflexivity.
  now eauto with Ensembles_DB.
  intros Hc. eapply HD. constructor; eauto.
Qed.

Lemma Add_functions_FunsFVs_Included_alt Q B fvs sig zeta S sig' zeta' S' f f' ft fvs' :
  Add_functions B fvs sig zeta S sig' zeta' S' ->
  Disjoint _ (FunsFVs zeta) Q ->
  zeta' f = Some (f', ft, fvs') ->
  fvs' = fvs \/ Disjoint _ (FromList fvs') Q.
Proof with now eauto with Ensembles_DB.
  intros Hadd. induction Hadd; intros Hin Heq.
  - destruct (peq f0 f); subst.
    + rewrite extend_gss in Heq.
      inv Heq; eauto.
    + rewrite extend_gso in Heq; eauto.
  - right. eapply Disjoint_Included_l; [| eassumption ].
    repeat eexists; eauto.
Qed.

(* Lemma Add_functions_injective_subdomain P B fvs sig zeta S sig' zeta' S'  : *)
(*   Add_functions B fvs sig zeta S sig' zeta' S' -> *)
(*   unique_bindings_fundefs B -> *)
(*   injective_subdomain (Setminus _ P (name_in_fundefs B)) sig -> *)
(*   Disjoint _ (image sig (Setminus _ P (name_in_fundefs B))) (name_in_fundefs B) -> *)
(*   injective_subdomain P sig'. *)
(* Proof with now eauto with Ensembles_DB. *)
(*   intros Hadd. revert P; induction Hadd; intros P Hun Hinj HD. *)
(*   - inv Hun. eapply injective_subdomain_extend'. *)
(*     eapply IHHadd. eassumption. now rewrite Setminus_Union. *)
(*     rewrite Setminus_Union... *)
(*     intros Hc. eapply Add_functions_image_Included in Hc; [| eassumption ]. *)
(*     inv Hc. eapply HD. *)
(*     constructor; eauto. rewrite Setminus_Union in H0; eassumption. *)
(*     left; eauto. *)
(*     eapply H6. eapply name_in_fundefs_bound_var_fundefs. eassumption. *)
(*   - simpl in Hinj. now rewrite Setminus_Empty_set_neut_r in Hinj. *)
(* Qed. *)

Lemma Add_functions_image_LiftedFuns_Included B fvs sig zeta S sig' zeta' S' x f :
  Add_functions B fvs sig zeta S sig' zeta' S' ->
  lifted_name zeta' x = Some f ->
  x \in name_in_fundefs B  ->
        f \in S /\ ~ f \in S'.
Proof with now eauto with Ensembles_DB.
  intros Hadd. induction Hadd; intros Heq Hin.
  - destruct (peq f0 x); subst.
    + rewrite lifted_name_extend, extend_gss in Heq. inv Heq.
      split.
      eapply Add_functions_free_set_Included; eassumption.
      intros Hc. inv Hc; eauto.
    + rewrite lifted_name_extend, extend_gso in Heq; eauto.
      inv Hin. inv H0; congruence.
      eapply IHHadd in Heq; eauto. inv Heq.
      split; eauto. intros Hc. inv Hc. eauto.
  - inv Hin.
Qed.

Lemma Add_functions_injective_subdomain_LiftedFuns B fvs sig zeta S sig' zeta' S'  :
  Add_functions B fvs sig zeta S sig' zeta' S' ->
  injective_subdomain (name_in_fundefs B) (lifted_name zeta').
Proof with now eauto with Ensembles_DB.
  intros Hadd. induction Hadd.
  - simpl. rewrite lifted_name_extend. eapply injective_subdomain_extend.
    eassumption.
    intros [x [Hin Heq]]; subst. inv Hin.
    eapply Add_functions_image_LiftedFuns_Included in Hadd; try eassumption.
    inv Hadd; eauto.
  - eapply injective_subdomain_Empty_set.
Qed.

Lemma Add_functions_map_Disjoint B fvs f g S f' g' S' l :
  Add_functions B fvs f g S f' g' S' ->
  Disjoint positive (FromList l) (Union _ (name_in_fundefs B) (Setminus _ S S')) ->
  map f' l = map f l.
Proof with now eauto with Ensembles_DB.
  intros Hadd HD. induction Hadd.
  - rewrite !map_extend_not_In. eapply IHHadd...
    intros Hc. eapply HD; eauto.
    constructor; eauto. left. left; eauto.
    intros Hc. eapply HD; eauto.
    constructor; eauto. right. constructor; eauto.
    eapply Add_functions_free_set_Included; eassumption.
    intros Hc'; inv Hc'; eauto.
  - reflexivity.
Qed.

Lemma Add_functions_is_Some B fvs sig zeta S sig' zeta' S' f :
  Add_functions B fvs sig zeta S sig' zeta' S' ->
  f \in name_in_fundefs B ->
        exists f' ft',  zeta' f = Some (f', ft', fvs) /\ f' \in (S \\ S').
Proof.
  intros Hadd Hin; induction Hadd.
  - destruct (peq f f0); subst.
    + do 2 eexists. rewrite extend_gss. split. reflexivity.
      constructor. eapply Add_functions_free_set_Included; eassumption.
      intros Hc; inv Hc. eauto.
    + inv Hin. inv H0; contradiction.
      rewrite extend_gso; eauto.
      edestruct IHHadd as (f'' & ft'' & Heq & Hin). eassumption.
      do 2 eexists. split. eassumption. inv Hin.
      constructor; eauto. intros Hc; inv Hc; eauto.
  - inv Hin.
Qed.

Lemma Add_functions_lifted_name_Disjoint_Same_set B fvs sig zeta S sig' zeta' S' Q :
  Disjoint _ Q (Union _ S (name_in_fundefs B)) ->
  Add_functions B fvs sig zeta S sig' zeta' S' ->
  image' (lifted_name zeta') Q <--> image' (lifted_name zeta) Q.
Proof with now eauto with Ensembles_DB.
  intros HD Hadd. induction Hadd.
  - rewrite lifted_name_extend. rewrite image'_extend_is_Some_not_In_P.
    eapply IHHadd. simpl in *...
    intros Hc. eapply HD. constructor; eauto.
    right; left; eauto.
  - reflexivity.
Qed.

Lemma Add_functions_image_LiftedFuns_Same_set B fvs sig zeta S sig' zeta' S' :
  Disjoint _ S (name_in_fundefs B) ->
  unique_bindings_fundefs B ->
  Add_functions B fvs sig zeta S sig' zeta' S' ->
  image sig' (S \\ S') <--> (S \\ S').
Proof with now eauto with Ensembles_DB.
  intros HD Hun Hadd. induction Hadd; simpl.
  - inv Hun.
    rewrite image_extend_In_S, image_extend_not_In_S, !Setminus_Setminus_Same_set,
    !Setminus_Union_distr, Setminus_Same_set_Empty_set, Union_Empty_set_neut_r.
    rewrite !(Setminus_Disjoint (Setminus var S S')).
    rewrite IHHadd; eauto. reflexivity.
    now eauto with Ensembles_DB.
    eapply Disjoint_Singleton_r. now intros Hc; inv Hc; eauto.
    now eauto with typeclass_instances.
    eapply Singleton_Included.
    now eapply Add_functions_free_set_Included; eauto.
    intros Hc. inv Hc. inv H0.
    eapply HD; constructor; eauto. now left; eauto.
    constructor.
    now eapply Add_functions_free_set_Included; eauto.
    now intros Hc; inv Hc; eauto.
  - rewrite !Setminus_Same_set_Empty_set, image_Empty_set...
Qed.

Lemma Add_functions_image_Disjoint_Same_set B fvs sig zeta S sig' zeta' S' Q :
  Disjoint _ Q (Union _ S (name_in_fundefs B)) ->
  Add_functions B fvs sig zeta S sig' zeta' S' ->
  Same_set _ (image sig' Q) (image sig Q).
Proof with now eauto with Ensembles_DB.
  intros HD Hadd. induction Hadd.
  - rewrite !image_extend_not_In_S.
    eapply IHHadd. simpl in *...
    intros Hc; eapply HD. constructor; eauto.
    now right; left; eauto.
    intros Hc; eapply HD. constructor; eauto.
    left. now eapply Add_functions_free_set_Included; eauto.
  - reflexivity.
Qed.


Lemma Add_functions_image_name_in_fundefs B fvs sig zeta S sig' zeta' S' :
  Disjoint _ (name_in_fundefs B) S ->
  unique_bindings_fundefs B ->
  Add_functions B fvs sig zeta S sig' zeta' S' ->
  image sig' (name_in_fundefs B) <--> name_in_fundefs B.
Proof with now eauto with Ensembles_DB.
  intros HD Hun Hadd. induction Hadd.
  - rewrite image_extend_not_In_S.
    2:{ intros Hc. eapply HD. constructor. eassumption.
        eapply Add_functions_free_set_Included. eassumption. eassumption. }
    simpl. rewrite image_extend_In_S; [| sets ]. rewrite Setminus_Union_distr.
    rewrite Setminus_Same_set_Empty_set, Union_Empty_set_neut_l.
    rewrite Setminus_Disjoint. rewrite Union_commut. rewrite IHHadd. reflexivity. sets.
    inv Hun. eassumption. inv Hun. eapply Disjoint_Singleton_r.
    intros Hc. eapply H6. eapply name_in_fundefs_bound_var_fundefs. eassumption.
  - simpl. rewrite image_Empty_set. reflexivity.
Qed.

Lemma Add_functions_image_Same_set B fvs sig zeta S sig' zeta' S' Q :
  Disjoint _ S (name_in_fundefs B) ->
  Disjoint _ Q (name_in_fundefs B) ->
  Disjoint _ (image' (lifted_name zeta) Q) (Union var S (name_in_fundefs B)) ->
  unique_bindings_fundefs B ->
  Add_functions B fvs sig zeta S sig' zeta' S' ->
  Same_set _ (image sig' (image' (lifted_name zeta') (Union _ Q (name_in_fundefs B))))
           (Union _ (Setminus _ S S') (image sig (image' (lifted_name zeta) Q))).
Proof with now eauto with Ensembles_DB.
  intros. rewrite Add_functions_lifted_name_Same_set; eauto.
  rewrite image_Union, Union_commut. apply Same_set_Union_compat.
  rewrite Add_functions_image_LiftedFuns_Same_set...
  rewrite Add_functions_image_Disjoint_Same_set; eauto.
  reflexivity.
Qed.

Lemma Add_functions_same_name B fvs sig zeta S sig' zeta' S' f :
  f \in (name_in_fundefs B :|: (S \\ S')) ->
        Add_functions B fvs sig zeta S sig' zeta' S' ->
        sig' f = f.
Proof.
  intros Hin Hadd. induction Hadd; eauto.
  - destruct (peq f f'); subst.
    + rewrite extend_gss; eauto.
    + rewrite extend_gso; eauto. destruct (peq f0 f); subst.
      * rewrite extend_gss; eauto.
      * rewrite extend_gso; eauto. eapply IHHadd.
        inv Hin. inv H0. inv H1; congruence. now eauto.
        right. inv H0. constructor; eauto.
        intros Hc. eapply H2. constructor; eauto.
        intros Hc'; inv Hc'; congruence.
  - inv Hin. inv H. rewrite Setminus_Same_set_Empty_set in H. inv H.
Qed.

Lemma Add_functions_name_in_fundefs B1 fvs sig zeta S sig' zeta' S' :
  unique_bindings_fundefs B1 ->
  Add_functions B1 fvs sig zeta S sig' zeta' S' ->
  Same_set _ (image' (lifted_name zeta') (name_in_fundefs B1))
           (Setminus var S S').
Proof with now eauto with Ensembles_DB.
  intros Hun Hadd. induction Hadd; simpl in *.
  - rewrite lifted_name_extend, image'_Union, image'_Singleton_is_Some;
      [| now rewrite extend_gss; eauto ]. inv Hun.
    rewrite image'_extend_is_Some_not_In_P.
    rewrite IHHadd, Setminus_Setminus_Same_set; eauto.
    now eauto with Ensembles_DB.
    now eauto with typeclass_instances.
    eapply Singleton_Included.
    now eapply Add_functions_free_set_Included; eauto.
    intros Hc. eapply H6.
    now apply name_in_fundefs_bound_var_fundefs.
  - rewrite image'_Empty_set, Setminus_Same_set_Empty_set...
Qed.

Lemma Add_functions_name_in_fundefs_Included B1 fvs sig zeta S sig' zeta' S' :
  Add_functions B1 fvs sig zeta S sig' zeta' S' ->
  image' (lifted_name zeta') (name_in_fundefs B1) \subset (S \\ S').
Proof with now eauto with Ensembles_DB.
  intros Hadd. induction Hadd; simpl in *.
  - rewrite lifted_name_extend, image'_Union, image'_Singleton_is_Some;
      [| now rewrite extend_gss; eauto ].
    rewrite Setminus_Setminus_Same_set; tci.
    eapply Union_Included. sets.
    eapply Included_trans. eapply image'_extend_is_Some.
    eapply Union_Included; sets.
    eapply Included_trans. eapply image'_monotonic. eapply Setminus_Included.
    eapply Included_trans. eassumption. sets.
    eapply Add_functions_free_set_Included in Hadd; eauto.
    sets.
  - rewrite image'_Empty_set, Setminus_Same_set_Empty_set...
Qed.

Lemma Add_functions_sig_eq_alt (B : fundefs) (fvs : list var) (sig : var -> var) (zeta : var -> option (var * fun_tag * list var))
      (Q S : Ensemble var) (sig' : var -> var) (zeta' : var -> option (var * fun_tag * list var)) (S' : Ensemble var) :
  Add_functions B fvs sig zeta S sig' zeta' S' ->
  Disjoint _ Q (name_in_fundefs B :|: (S \\ S')) ->
  f_eq_subdomain Q sig sig'.
Proof.
  intros. eapply f_eq_subdomain_antimon; [| eapply Add_functions_sig_eq; eassumption ].
  intros x Hin Hin'. eapply H0; constructor; eauto.
Qed.


(** * Lemmas about [Make_wrappers] *)

Lemma Make_wrappers_free_set_Included zeta sig B S C S' zeta' :
  Make_wrappers zeta sig B S C S' zeta' ->
  Included _ S' S.
Proof with eauto with Ensembles_DB.
  intros Hmake. induction Hmake...
  - eapply Included_trans; [ eassumption | ]...
Qed.

Lemma Make_wrapper_image Q zeta sig B S C S' sig' :
  Make_wrappers zeta sig B S C S' sig' ->
  Disjoint _ Q (name_in_fundefs B) ->
  image sig Q <--> image sig' Q.
Proof.
  intros Hw Hd. induction Hw.
  - reflexivity.
  - rewrite image_extend_not_In_S. eapply IHHw.
    now sets.
    intros Hc. eapply Hd. constructor. eassumption. now left.
Qed.

Lemma Make_wrappers_f_eq_subdomain Q zeta sig B S C S' sig' :
  Make_wrappers zeta sig B S C S' sig' ->
  Disjoint _ Q (name_in_fundefs B) ->
  f_eq_subdomain Q sig sig'.
Proof.
  intros Hw Hd. induction Hw.
  - reflexivity.
  - eapply f_eq_subdomain_extend_not_In_S_r.
    intros Hc. eapply Hd. constructor. eassumption. now left.
    eapply IHHw. sets.
Qed.

Lemma Make_wrapper_image_name_in_fundefs zeta sig B S C S' sig' :
  Make_wrappers zeta sig B S C S' sig' ->
  unique_bindings_fundefs B ->
  image sig' (name_in_fundefs B) \subset S \\ S'.
Proof.
  intros Hw Hun. induction Hw.
  - rewrite image_Empty_set, Setminus_Same_set_Empty_set. reflexivity.
  - inv Hun. simpl. rewrite image_Union, image_Singleton.
    eapply Union_Included.
    + rewrite extend_gss. apply Singleton_Included. inv H3. constructor; eauto.
      intros Hc. eapply Make_wrappers_free_set_Included in Hc; [| eassumption ]. inv Hc. now eauto.
    + rewrite image_extend_not_In_S. eapply Included_trans. eapply IHHw. eassumption.
      now sets. intros Hc. eapply H10. eapply name_in_fundefs_bound_var_fundefs. eassumption.
Qed.

Lemma Make_wrappers_find_def f1 f2 z B S1 fds S2 f ft xs e :
  Make_wrappers z f1 B S1 fds S2 f2 ->
  find_def f B = Some (ft, xs, e) ->
  Disjoint _ (FunsFVs z) (name_in_fundefs B) ->
  unique_bindings_fundefs B ->
  exists f' ft' fvs g xs',
    z f = Some (f', ft', fvs) /\
    FromList xs' \subset S1 /\
    g \in S1 \\ FromList xs' /\
          length xs = length xs' /\ NoDup xs' /\
          f2 f = g /\
          find_def g fds = Some (ft, xs', Eapp f' ft' (xs' ++ map f1 fvs)).
Proof.
  intros Hw Hdef Hd Hun. induction Hw.
  - inv Hdef.
  - simpl in Hdef.
    destruct (M.elt_eq f f0); subst.
    + inv Hdef.
      do 5 eexists. repeat (split; first eassumption).
      split.
      * rewrite extend_gss. reflexivity.
      * simpl. rewrite peq_true. reflexivity.
    + inv Hun. edestruct IHHw as (f'' & ft'' & fvs' & g1 & xs'' & Hzeq & Hsub & Hin & Hleq & Hnd  & Heq & Hf); eauto.
      now sets.
      do 4 eexists. exists xs''. repeat (split; first eassumption).
      split; [| split; [| split; [| split; [| split ]]]]; try eassumption.
      * eapply Included_trans. eassumption. sets.
      * eapply Included_trans; [| | eapply Hin ]. reflexivity. sets.
      * rewrite extend_gso; eassumption.
      * simpl. rewrite peq_false; eauto.
        intros Hc. subst. inv Hin. inv H4; eauto.
Qed.


Lemma Make_wrappers_name_in_fundefs z f1 B S1 fds S2 f2 :
  Make_wrappers z f1 B S1 fds S2 f2 ->
  name_in_fundefs fds \subset S1 \\ S2.
Proof.
  intros Hw; induction Hw. now sets.
  simpl. eapply Union_Included. eapply Singleton_Included. inv H3; eauto.
  constructor; eauto.
  intros Hc. eapply Make_wrappers_free_set_Included in Hc; [| eassumption ].
  inv Hc; eauto.
  eapply Included_trans. eapply IHHw. sets.
Qed.

Lemma Make_wrappers_name_in_fundefs_eq z f1 B S1 fds S2 f2 :
  Make_wrappers z f1 B S1 fds S2 f2 ->
  bound_var_fundefs fds <--> S1 \\ S2.
Proof.
  intros Hw; induction Hw.
  normalize_bound_var. now sets.

  repeat normalize_bound_var. normalize_sets.
  rewrite IHHw.
  rewrite !Setminus_Union. rewrite !Union_assoc. rewrite Union_commut with (s2 := S').
  rewrite <- Setminus_Union. rewrite Union_Setminus_Included; tci; sets.
  eapply Make_wrappers_free_set_Included in Hw.
  rewrite Union_Same_set. reflexivity.
  intros z Hc. inv H3. inv Hc. inv H3.
  constructor. eassumption. intros Hc. eapply Hw in Hc. inv Hc. now eauto.
  constructor; eauto. intros Hc. eapply Hw in Hc. inv Hc. inv H6. now eauto.
Qed.

Lemma Make_wrappers_name_in_fundefs_image z f1 B S1 fds S2 f2 :
  Make_wrappers z f1 B S1 fds S2 f2 ->
  unique_bindings_fundefs B ->
  name_in_fundefs fds <--> image f2 (name_in_fundefs B).
Proof.
  intros Hw Hun; induction Hw.
  - simpl. rewrite image_Empty_set. reflexivity.
  - simpl. rewrite image_Union, image_Singleton. rewrite extend_gss.
    eapply Same_set_Union_compat. reflexivity.
    inv Hun. rewrite image_extend_not_In_S. eapply IHHw. eassumption.
    intros Hc. eapply H10. eapply name_in_fundefs_bound_var_fundefs. eassumption.
Qed.


Lemma Make_wrappers_image_Included S z f1 B S1 fds S2 f2 :
  Make_wrappers z f1 B S1 fds S2 f2 ->
  image f2 S \subset image f1 (S \\ name_in_fundefs B) :|: (S1 \\ S2).
Proof.
  intros Hw; revert S; induction Hw; intros Q.
  - simpl. sets.
  - simpl. eapply Included_trans.
    eapply image_extend_Included'. eapply Union_Included.
    + eapply Included_trans. eapply IHHw.
      eapply Included_Union_compat; [| now sets ].
      now xsets.
    + eapply Included_Union_preserv_r. eapply Singleton_Included. inv H3.
      constructor; eauto. intros Hc. eapply Make_wrappers_free_set_Included in Hc; [| eassumption ].
      inv Hc. now eauto.
Qed.


(** * Lemmas about [Exp_lambda_lift] and [Fundefs_lambda_lift] *)

Lemma Fundefs_lambda_lift_name_in_fundefs2 zeta sig B0 B S B' S' :
  Fundefs_lambda_lift2 zeta sig B0 B S B' S' ->
  name_in_fundefs B' <--> (image' (lifted_name zeta) (name_in_fundefs B)).
Proof.
  intros Hadd; induction Hadd; simpl.
  - assert (Heq := lifted_name_eq _ _ _ _ _ H).
    rewrite IHHadd. rewrite image'_Union, image'_Singleton_is_Some; eauto.
    reflexivity.
  - rewrite image'_Empty_set. reflexivity.
Qed.

Lemma Fundefs_lambda_lift_name_in_fundefs3 zeta sig B0 B S B' S' :
  Fundefs_lambda_lift3 zeta sig B0 B S B' S' ->
  name_in_fundefs B' <--> name_in_fundefs B.
Proof.
  intros Hadd; induction Hadd; simpl.
  - rewrite IHHadd. sets.
  - sets.
Qed.

Lemma Lambda_lift_free_set_Included_mut :
  (forall e zeta sig S e' S',
      Exp_lambda_lift zeta sig e S e' S' ->
      Included _ S' S) /\
  (forall B B0 zeta sig S B' S',
      Fundefs_lambda_lift2 zeta sig B0 B S B' S' \/
      Fundefs_lambda_lift3 zeta sig B0 B S B' S' ->
      Included _ S' S).
Proof with now eauto with Ensembles_DB.
  exp_defs_induction IHe IHl IHB; intros; inv H; try inv H0; try now eauto with Ensembles_DB.
  - eapply Included_trans. now eapply IHl; eauto.
    eapply IHe; eauto.
  - eapply Included_trans. now eapply IHe; eauto.
    eapply Included_trans. now eapply Make_wrappers_free_set_Included; eauto.
    eapply Included_trans. now eapply IHB; eauto.
    eapply Add_functions_free_set_Included; eauto.
  - eapply Included_trans. now eapply IHe; eauto.
    eapply (IHB f2); eauto.
  - eapply Included_trans. now eapply IHB; eauto.
    eapply Included_trans. now eapply IHe; eauto.
    eapply Included_trans. eapply Make_wrappers_free_set_Included; eauto.
    now sets.
  - eapply Included_trans.
    eapply IHB; eauto.
    now eapply IHe; eauto.
Qed.

Corollary Exp_Lambda_lift_free_set_Included :
  forall e zeta sig S e' S',
    Exp_lambda_lift zeta sig e S e' S' ->
    Included _ S' S.
Proof.
  destruct Lambda_lift_free_set_Included_mut; eauto.
Qed.

Corollary Fundefs_Lambda_lift_free_set_Included2 :
  forall B B0 zeta sig S B' S',
    Fundefs_lambda_lift2 zeta sig B0 B S B' S' ->
    Included _ S' S.
Proof.
  destruct Lambda_lift_free_set_Included_mut; eauto.
Qed.

Corollary Fundefs_Lambda_lift_free_set_Included3 :
  forall B B0 zeta sig S B' S',
    Fundefs_lambda_lift3 zeta sig B0 B S B' S' ->
    Included _ S' S.
Proof.
  intros B; intros.
  destruct Lambda_lift_free_set_Included_mut as [_ HB]. eapply HB with (B0 := B0); eauto.
Qed.


Lemma Fundefs_lambda_lift_find_def2 sig zeta S1 B0 B1 S2 B2 f t xs1 e1 f' t' fvs :
  Fundefs_lambda_lift2 zeta sig B0 B1 S1 B2 S2 ->
  zeta f = Some (f', t', fvs) ->
  Disjoint _ (bound_var_fundefs B1) (LiftedFuns zeta) ->
  injective_subdomain (name_in_fundefs B1) (lifted_name zeta) ->
  find_def f B1 = Some (t, xs1, e1) ->
  exists (ys : list var) (e2 : exp) S2 S3 S4 sig' fds,
    find_def f' B2 = Some (t', xs1 ++ ys, Efun fds e2) /\
    NoDup ys /\
    length ys = length fvs /\
    FromList ys \subset S1 /\
    S2 \subset S1 \\ FromList ys /\
    Disjoint _ (FromList ys) S2 /\
    Make_wrappers zeta (sig <{ xs1 ++ fvs ~> xs1 ++ ys }>) B0 S2 fds S3 sig' /\
    Exp_lambda_lift zeta sig' e1 S3 e2 S4.
Proof with now eauto with Ensembles_DB.
  intros Hll. induction Hll; intros Heq HD Hinj Hdef.
  - assert (Heq' := lifted_name_eq _ _ _ _ _ Heq).
    simpl in Hdef. destruct (M.elt_eq f f0); subst.
    + rewrite Heq in H; inv H. inv Hdef.
      exists ys, e'. do 5 eexists.
      split; [| split; [| split; [| split; [| split; [| split; [| split ]]]]]];
        [ | | | | | | eassumption | eassumption ]; eauto.
      * simpl. rewrite peq_true. reflexivity.
      * sets.
      * sets.
    + destruct IHHll as (ys' & e2 & S2 & S3 & S4 & sig'' & fds' & Hf1 & Hnd1 & Heq1 & Hs1 & Hs2 & Hd1 & Hw & Hexp).
      eassumption. normalize_bound_var_in_ctx...
      eapply injective_subdomain_antimon. eassumption.
      now eauto with Ensembles_DB. eassumption.
      eexists ys', e2. do 5 eexists.
      split; [| split; [| split; [| split; [| split; [| split; [| split ]]]]]];
        [ | | | | | | eassumption | eassumption ]; eauto.
      * simpl. rewrite peq_false; eauto.
        intros Hc; subst. eapply n. eapply Hinj.
        constructor 2. eapply fun_in_fundefs_name_in_fundefs.
        eapply find_def_correct. eassumption.
        now simpl; eauto. erewrite !lifted_name_eq; eauto.
      * eapply Included_trans. eassumption.
        eapply Included_trans. eapply Exp_Lambda_lift_free_set_Included.
        eassumption. eapply Included_trans.
        eapply Make_wrappers_free_set_Included. eassumption. sets.
      * eapply Included_trans. eassumption.
        eapply Included_Setminus_compat; [| reflexivity ].
        eapply Included_trans. eapply Exp_Lambda_lift_free_set_Included. eassumption.
        eapply Included_trans. eapply Make_wrappers_free_set_Included. eassumption. now sets.
  - inv Hdef.
Qed.

Lemma Fundefs_lambda_lift_find_def3 sig zeta S1 B B1 S2 B2 f t xs1 e1 :
  Fundefs_lambda_lift3 zeta sig B B1 S1 B2 S2 ->
  find_def f B1 = Some (t, xs1, e1) ->
  exists (e2 : exp) S1' S2',
    find_def f B2 = Some (t, xs1, e2) /\
    S1' \subset S1 /\
    Exp_lambda_lift zeta ((extend_fundefs sig B B) <{ xs1 ~> xs1 }>) e1 S1' e2 S2'.
Proof with now eauto with Ensembles_DB.
  intros Hll. induction Hll; intros (* Heq HD Hinj *) Hdef.
  - simpl in Hdef. destruct (M.elt_eq f f0); subst.
    + inv Hdef. do 3 eexists. split; [| split ].
      * simpl. rewrite peq_true. reflexivity.
      * reflexivity.
      * sets.
    + simpl. rewrite peq_false; eauto.
      destruct IHHll as (e2 & S1' & S2' & Hf1 & Hsub1 & Hexp).
      eassumption. do 3 eexists; split; [| split ]; [ eassumption | | eassumption ].
      eapply Included_trans. eassumption.
      eapply Exp_Lambda_lift_free_set_Included. eassumption.
  - inv Hdef.
Qed.


Lemma bound_var_Ecase_var x y B :
  bound_var (Ecase x B) <--> bound_var (Ecase y B).
Proof.
  induction B; repeat normalize_bound_var; sets.
  destruct a. repeat normalize_bound_var. sets.
Qed.

Ltac find_subsets :=
  match goal with
  | [ H : Fundefs_lambda_lift2 _ _ _ _ _ _ _ |- _ ] =>
    eapply Fundefs_Lambda_lift_free_set_Included2 in H
  | [ H : Fundefs_lambda_lift3 _ _ _ _ _ _ _ |- _ ] =>
    eapply Fundefs_Lambda_lift_free_set_Included3 in H
  | [ H : Exp_lambda_lift _ _ _ _ _ _ |- _ ] =>
    eapply Exp_Lambda_lift_free_set_Included in H
  | [ H : Make_wrappers _ _ _ _ _ _ _ |- _ ] =>
    eapply Make_wrappers_free_set_Included in H
  | [ H : Add_functions _ _ _ _ _ _ _ _ |- _ ] =>
    eapply Add_functions_free_set_Included in H
  end.


Lemma occurs_free_Ecase x y P :
  occurs_free (Ecase x P) \subset x |: occurs_free (Ecase y P).
Proof.
  induction P; repeat normalize_occurs_free; sets.
  destruct a. repeat normalize_occurs_free.
  eapply Union_Included. sets.
  eapply Union_Included; sets.
  eapply Included_trans. eassumption. sets.
Qed.


Lemma Make_wrappers_occurs_free z f1 B S1 fds S2 f2 :
  Make_wrappers z f1 B S1 fds S2 f2 ->
  occurs_free_fundefs fds \subset image f1 (FunsFVs z) :|: LiftedFuns z.
Proof.
  intros Hm; induction Hm.
  - now constructor.
  - repeat normalize_occurs_free. repeat normalize_sets.
    rewrite FromList_map_image_FromList.
    rewrite !Setminus_Union_distr. eapply Union_Included.
    eapply Union_Included.
    eapply Union_Included.
    now sets.
    eapply Included_trans. eapply Setminus_Included.
    eapply Included_Union_preserv_l. eapply image_monotonic.
    intros z Hin. do 4 eexists. now split; eauto.
    eapply Included_trans. eapply Setminus_Included.
    eapply Included_Union_preserv_r.
    eapply Singleton_Included. eexists. split. eexists.
    eapply lifted_name_eq. eassumption.
    eapply lifted_name_eq. eassumption.
    eapply Setminus_Included_Included_Union. sets.
Qed.

(* TODO move *)
Lemma image_extend_fundefs S f B:
  image (extend_fundefs f B B) S \subset image f (S \\ name_in_fundefs B) :|: name_in_fundefs B.
Proof.
  revert S; induction B; intros S; simpl in *; eauto.
  - eapply Included_trans. eapply image_extend_Included'.
    eapply Union_Included; [| now sets ]. eapply Included_trans. eapply IHB.
    xsets.
  - normalize_sets. sets.
Qed.

Lemma extend_fundefs_eq f B x :
  x \in name_in_fundefs B ->
        extend_fundefs f B B x = x.
Proof.
  intros Hin. induction B.
  destruct (peq x v); subst.
  - simpl. rewrite extend_gss. reflexivity.
  - inv Hin. inv H; contradiction. simpl.
    rewrite extend_gso; eauto.
  - inv Hin.
Qed.

Lemma extend_fundefs_neq f B x :
  ~ x \in name_in_fundefs B ->
          extend_fundefs f B B x = f x.
Proof.
  intros Hin. induction B; try reflexivity.
  simpl in *. rewrite extend_gso. now eauto.
  intros Hc. subst; eauto.
Qed.

Lemma extend_fundefs_image S B f:
  Disjoint _ S (name_in_fundefs B) ->
  image (extend_fundefs f B B) S <--> image f S.
Proof.
  intros Hin. induction B; try reflexivity.
  simpl in *. rewrite image_extend_not_In_S. eapply IHB. now sets.
  intros Hc. eapply Hin. constructor. eassumption. now left.
Qed.

Lemma Make_wrappers_bound_var zeta sig B S C S' sig' :
  Make_wrappers zeta sig B S C S' sig' ->
  bound_var_fundefs C \subset (S \\ S').
Proof with eauto with Ensembles_DB.
  intros Hmake. induction Hmake; normalize_bound_var...
  find_subsets.
  inv H3. intros z Hc. inv Hc.
  - inv H3. constructor; eauto. intros Hc. eapply Hmake; eauto.
  - inv H3.
    + constructor; eauto. intros Hc. eapply Hmake in Hc. inv Hc.
      inv H3. contradiction.
    + inv H6.
      * repeat normalize_bound_var_in_ctx. inv H3.
      * constructor; eauto. eapply IHHmake. eassumption.
        intros Hc. eapply IHHmake; eassumption.
Qed.

(* Why is this so painful? :'( *)

(* occurs_free_fundefs_big_cup: *)
(*   forall B : fundefs, *)
(*   occurs_free_fundefs B <--> *)
(*   \bigcup_(p in fun_in_fundefs B) *)
(*      ((let *)
(*        '(_, _, xs, e) := p in occurs_free e \\ FromList xs) \\ *)
(*       name_in_fundefs B) *)

(* TODO generalize it to also prove that Disjoint _ (fv s') (funnames e) *)

(* Thing to try:


Consider that Disjoint (names B') (sig (names B))

where names B' = lifted_names zeta (names B)


and then take occurs_free e' \\ name_in_fundefs B0
*)

Lemma fundefs_append_occurs_free : forall B1 B2,
  occurs_free_fundefs (fundefs_append B1 B2) <-->
    occurs_free_fundefs B1 \\ name_in_fundefs (fundefs_append B1 B2) :|:
    (occurs_free_fundefs B2 \\ name_in_fundefs (fundefs_append B1 B2)).
Proof.
  induction B1; intros B2; simpl; repeat normalize_occurs_free; repeat normalize_sets.
  - rewrite IHB1.
    repeat rewrite !Setminus_Union_distr, !Setminus_Union, !Union_assoc.
    repeat apply Same_set_Union_compat; eauto with Ensembles_DB.
    rewrite fundefs_append_name_in_fundefs by reflexivity.
    rewrite !Union_assoc.
    apply Same_set_Setminus_compat; eauto with Ensembles_DB.
    split; repeat apply Union_Included; eauto with Ensembles_DB.
  - rewrite <- Included_Setminus_Disjoint; eauto with Ensembles_DB.
    apply Disjoint_sym; apply occurs_free_fundefs_name_in_fundefs_Disjoint.
Qed.

Lemma Exp_lambda_lift_occurs_free_mut :
  (forall e zeta sig S e' S',
      Exp_lambda_lift zeta sig e S e' S' ->
      unique_bindings e ->
      Disjoint _ (image sig (occurs_free e :|: LiftedFuns zeta :|: FunsFVs zeta)) (S :|: bound_var e) ->
      Disjoint _ S (bound_var e :|: occurs_free e) ->
      Disjoint _ S (LiftedFuns zeta :|: FunsFVs zeta) ->
      Disjoint _ (bound_var e) (occurs_free e) ->
      Disjoint _ (bound_var e) (LiftedFuns zeta :|: FunsFVs zeta) ->
      occurs_free e' \subset image sig (occurs_free e :|: LiftedFuns zeta :|: FunsFVs zeta) :|: LiftedFuns zeta) /\
  (forall B Bpre B0 zeta sig S B' S',
      (Fundefs_lambda_lift2 zeta sig B0 B S B' S' ->
      name_in_fundefs B \subset name_in_fundefs B0 ->
      unique_bindings_fundefs B ->
      unique_bindings_fundefs B0 ->
      B0 = fundefs_append Bpre B ->
      (forall x, x \in name_in_fundefs B -> sig x = x) ->
      Disjoint _ (image sig (occurs_free_fundefs B0 :|: LiftedFuns zeta :|: FunsFVs zeta)) (S :|: bound_var_fundefs B0) ->
      Disjoint _ S (bound_var_fundefs B0 :|: occurs_free_fundefs B) ->
      Disjoint _ S (LiftedFuns zeta :|: FunsFVs zeta) ->
      Disjoint _ (bound_var_fundefs B) (occurs_free_fundefs B) ->
      Disjoint _ (bound_var_fundefs B :|: name_in_fundefs B0) (LiftedFuns zeta :|: FunsFVs zeta) ->
      occurs_free_fundefs B' \subset image sig (occurs_free_fundefs B0 :|: LiftedFuns zeta :|: FunsFVs zeta) :|: LiftedFuns zeta \\ name_in_fundefs B0) /\
     (Fundefs_lambda_lift3 zeta sig B0 B S B' S' ->
      name_in_fundefs B \subset name_in_fundefs B0 ->
      unique_bindings_fundefs B ->
      unique_bindings_fundefs B0 ->
      B0 = fundefs_append Bpre B ->
      (forall x, x \in name_in_fundefs B -> sig x = x) ->
      Disjoint _ (image sig (occurs_free_fundefs B0 :|: LiftedFuns zeta :|: FunsFVs zeta)) (S :|: bound_var_fundefs B0) ->
      Disjoint _ S (bound_var_fundefs B0 :|: occurs_free_fundefs B) ->
      Disjoint _ S (LiftedFuns zeta :|: FunsFVs zeta) ->
      Disjoint _ (bound_var_fundefs B) (occurs_free_fundefs B) ->
      Disjoint _ (bound_var_fundefs B :|: name_in_fundefs B0) (LiftedFuns zeta :|: FunsFVs zeta) ->
      occurs_free_fundefs B' \subset image sig (occurs_free_fundefs B0 :|: LiftedFuns zeta :|: FunsFVs zeta) :|: LiftedFuns zeta :|: name_in_fundefs Bpre)).
Proof with now eauto with Ensembles_DB.
  exp_defs_induction IHe IHl IHB; intros; try inv H.
  - inv H0. repeat normalize_occurs_free.
    rewrite FromList_map_image_FromList. eapply Union_Included. now sets.
    eapply Included_trans. eapply Included_Setminus_compat.
    eapply IHe; eauto.
    + eapply Disjoint_Included_l.
      eapply Included_trans. eapply image_extend_Included'. reflexivity.
      rewrite !Setminus_Union_distr.
      repeat normalize_bound_var_in_ctx. repeat normalize_occurs_free_in_ctx.
      eapply Union_Disjoint_l; sets.
      eapply Disjoint_Included; [| | eapply H1 ]; sets.
      eapply Union_Disjoint_r.
      eapply Disjoint_sym. eapply Disjoint_Included; [| | eapply H2 ]; sets.
      sets.
    + eapply Disjoint_Included_r. eapply bound_var_occurs_free_Econstr_Included. eassumption.
    + repeat normalize_occurs_free_in_ctx. repeat normalize_bound_var_in_ctx.
      eapply Disjoint_Included_r. eapply Included_Union_Setminus with (s2 := [set v]).
      tci. eapply Union_Disjoint_r; sets.
      eapply Disjoint_Included; [| | eapply H4 ]; sets.
    + repeat normalize_bound_var_in_ctx. sets.
    + reflexivity.
    + rewrite !Setminus_Union_distr.
      eapply Union_Included; [| now sets ].
      eapply Included_trans. eapply Included_Setminus_compat.
      eapply image_extend_Included'. reflexivity.
      rewrite !Setminus_Union_distr, !image_Union, !Setminus_Union_distr.
      eapply Union_Included; sets.
      eapply Union_Included; sets.
      eapply Union_Included; xsets.
  - repeat normalize_occurs_free. xsets.
  - inv H0. repeat normalize_occurs_free. eapply Union_Included. now xsets.
    eapply Union_Included.
    + eapply Included_trans.
      eapply IHe; eauto.
      * repeat normalize_bound_var_in_ctx. repeat normalize_occurs_free_in_ctx.
        eapply Disjoint_Included; [| | eapply H1 ]; sets.
      * eapply Disjoint_Included_r; [ eapply bound_var_occurs_free_Ecase_Included | ] ; [| eassumption ]. now left.
      * repeat normalize_occurs_free_in_ctx. repeat normalize_bound_var_in_ctx.
        eapply Disjoint_Included; [| | eapply H4 ]; sets.
      * repeat normalize_bound_var_in_ctx. xsets.
      * now xsets.
    + eapply Included_trans. eapply occurs_free_Ecase.
      eapply Union_Included. now xsets.
      eapply Included_trans. eapply IHl; eauto.
      * repeat normalize_bound_var_in_ctx. repeat normalize_occurs_free_in_ctx.
        eapply Disjoint_Included; [| | eapply H1 ]; sets.
        repeat find_subsets. sets.
      * eapply Disjoint_Included_r; [ eapply bound_var_occurs_free_Ecase_cons_Included | ].
        repeat find_subsets. sets.
      * repeat find_subsets.
        eapply Disjoint_Included_l. eassumption. eassumption.
      * repeat normalize_occurs_free_in_ctx. repeat normalize_bound_var_in_ctx.
        eapply Disjoint_Included; [| | eapply H4 ]; sets.
      * repeat normalize_bound_var_in_ctx. sets.
      * xsets.
  - inv H0. repeat normalize_occurs_free. eapply Union_Included. now xsets.
    eapply Included_trans. eapply Included_Setminus_compat.
    eapply IHe; eauto.
    + eapply Disjoint_Included_l.
      eapply Included_trans. eapply image_extend_Included'. reflexivity.
      rewrite !Setminus_Union_distr.
      repeat normalize_bound_var_in_ctx. repeat normalize_occurs_free_in_ctx.
      eapply Union_Disjoint_l; sets.
      eapply Disjoint_Included; [| | eapply H1 ]; sets.
      eapply Union_Disjoint_r; sets.
      eapply Disjoint_sym. eapply Disjoint_Included; [| | eapply H2 ]; sets.
    + eapply Disjoint_Included_r. eapply bound_var_occurs_free_Eproj_Included. eassumption.
    + repeat normalize_occurs_free_in_ctx. repeat normalize_bound_var_in_ctx.
      eapply Disjoint_Included_r. eapply Included_Union_Setminus with (s2 := [set v]).
      tci. eapply Union_Disjoint_r; sets.
      eapply Disjoint_Included; [| | eapply H4 ]; sets.
    + repeat normalize_bound_var_in_ctx. sets.
    + reflexivity.
    + rewrite !Setminus_Union_distr.
      eapply Union_Included; [| now sets ].
      eapply Included_trans. eapply Included_Setminus_compat.
      eapply image_extend_Included'. reflexivity.
      rewrite !Setminus_Union_distr, !image_Union, !Setminus_Union_distr.
      eapply Union_Included; sets.
      eapply Union_Included; sets.
      eapply Union_Included; xsets.
  - repeat normalize_occurs_free.
    rewrite FromList_map_image_FromList. repeat normalize_sets. rewrite !image_Union.
    eapply Union_Included; [ eapply Union_Included; [| eapply Union_Included ] | ]; sets.
    + do 2 eapply Included_Union_preserv_l. eapply Included_Union_preserv_r. eapply Singleton_Included.
      eapply In_image. eexists. split. eexists. eapply lifted_name_eq. eassumption.
      eapply lifted_name_eq. eassumption.
    + eapply Included_Union_preserv_l. eapply Included_Union_preserv_r. eapply image_monotonic.
      intros y Hin. do 4 eexists. split; eauto.
    + eapply Included_trans. eapply Included_Setminus_compat.
      inv H0. eapply IHe; eauto.
      * eapply Disjoint_Included_l.
        eapply Included_trans. eapply image_extend_Included'. reflexivity.
        rewrite !Setminus_Union_distr.
        repeat normalize_bound_var_in_ctx. repeat normalize_occurs_free_in_ctx.
        eapply Union_Disjoint_l; sets.
        eapply Disjoint_Included; [| | eapply H1 ]; sets.
        eapply Union_Disjoint_r; sets.
        eapply Disjoint_sym. eapply Disjoint_Included; [| | eapply H2 ]; sets.
      * eapply Disjoint_Included_r. eapply bound_var_occurs_free_Eletapp_Included. eassumption.
      * repeat normalize_occurs_free_in_ctx. repeat normalize_bound_var_in_ctx.
        eapply Disjoint_Included_r. eapply Included_Union_Setminus with (s2 := [set x]).
        tci. eapply Union_Disjoint_r; sets.
        eapply Disjoint_Included; [| | eapply H4 ]; sets.
      * repeat normalize_bound_var_in_ctx. sets.
      * reflexivity.
      * rewrite !Setminus_Union_distr.
        eapply Union_Included; [| now sets ].
        eapply Included_trans. eapply Included_Setminus_compat.
        eapply image_extend_Included'. reflexivity.
        rewrite !Setminus_Union_distr, !image_Union, !Setminus_Union_distr.
        eapply Union_Included; sets.
        eapply Union_Included; sets.
        eapply Union_Included; xsets.
  - repeat normalize_occurs_free.
    rewrite FromList_map_image_FromList. repeat normalize_sets. rewrite !image_Union.
    eapply Union_Included; [ eapply Union_Included | ]; sets.
    + xsets.
    + eapply Included_trans. eapply Included_Setminus_compat.
      inv H0. eapply IHe; eauto.
      * eapply Disjoint_Included_l.
        eapply Included_trans. eapply image_extend_Included'. reflexivity.
        rewrite !Setminus_Union_distr.
        repeat normalize_bound_var_in_ctx. repeat normalize_occurs_free_in_ctx.
        eapply Union_Disjoint_l; sets.
        eapply Disjoint_Included; [| | eapply H1 ]; sets.
        eapply Union_Disjoint_r.
        eapply Disjoint_sym. eapply Disjoint_Included; [| | eapply H2 ]; sets.
        sets.
      * eapply Disjoint_Included_r. eapply bound_var_occurs_free_Eletapp_Included. eassumption.
      * repeat normalize_occurs_free_in_ctx. repeat normalize_bound_var_in_ctx.
        eapply Disjoint_Included_r. eapply Included_Union_Setminus with (s2 := [set x]).
        tci. eapply Union_Disjoint_r; sets.
        eapply Disjoint_Included; [| | eapply H4 ]; sets.
      * repeat normalize_bound_var_in_ctx. sets.
      * reflexivity.
      * rewrite !Setminus_Union_distr.
        eapply Union_Included; [| now sets ].
        eapply Included_trans. eapply Included_Setminus_compat.
        eapply image_extend_Included'. reflexivity.
        rewrite !Setminus_Union_distr, !image_Union, !Setminus_Union_distr.
        eapply Union_Included; sets.
        eapply Union_Included; sets.
        eapply Union_Included; xsets.
  - inv H0. repeat normalize_occurs_free.
    rewrite <- Setminus_Disjoint with (s1 := occurs_free_fundefs B'). 2:{ eapply Disjoint_sym. eapply occurs_free_fundefs_name_in_fundefs_Disjoint. }
    assert (Hsub : image σ' (occurs_free e \\ name_in_fundefs f2 :|: occurs_free_fundefs f2 :|: LiftedFuns ζ' :|: FunsFVs ζ')
                         :|: LiftedFuns ζ' \\ name_in_fundefs B' \subset
                         image sig
                         (occurs_free_fundefs f2 :|: (occurs_free e \\ name_in_fundefs f2)
                                              :|: LiftedFuns zeta :|: FunsFVs zeta) :|: LiftedFuns zeta).
    { rewrite !Setminus_Union_distr. eapply Union_Included.
      - eapply Setminus_Included_Included_Union.
        rewrite Fundefs_lambda_lift_name_in_fundefs2 with (B' := B'); eauto.
        rewrite Add_functions_name_in_fundefs; eauto.
        rewrite <- Add_functions_image_LiftedFuns_Same_set with (S := S); eauto.
        eapply Included_trans. eapply image_monotonic.
        eapply Included_Union_compat. eapply Included_Union_compat.
        reflexivity.
        eapply Add_functions_LiftedFuns_Included_r. eassumption.
        eapply Add_functions_FunsFVs_Included_r. eassumption.
        rewrite !Union_assoc, Union_commut.
        rewrite Union_Same_set. 2:{ eapply Included_trans. eassumption. xsets. }
        rewrite <- Union_assoc. rewrite (Union_commut (S \\ S'0)).
        rewrite Union_assoc. rewrite image_Union. eapply Union_Included; [| now sets ].
        rewrite Add_functions_image_Disjoint_Same_set; eauto.
        do 2 eapply Included_Union_preserv_l. eapply image_monotonic.
        eapply Union_Included; [ now sets | ]. now sets.
        repeat normalize_bound_var_in_ctx. repeat normalize_occurs_free_in_ctx.
        eapply Union_Disjoint_r.
        eapply Union_Disjoint_l. eapply Union_Disjoint_l.
        eapply Disjoint_sym. eapply Disjoint_Included_r; [| eapply H2 ]; sets.
        eapply Disjoint_sym. eapply Disjoint_Included_r; [| eapply H3 ]; sets.
        eapply Disjoint_sym. eapply Disjoint_Included_r; [| eapply H3 ]; sets.
        eapply Disjoint_Included_r. eapply name_in_fundefs_bound_var_fundefs.
        eapply Disjoint_sym. eapply Union_Disjoint_r. eapply Union_Disjoint_r.
        eapply Disjoint_Included; [| | eapply H4 ]; sets.
        eapply Disjoint_Included; [| | eapply H5 ]; sets.
        eapply Disjoint_Included; [| | eapply H5 ]; sets.
        eapply Disjoint_Included_r. eapply name_in_fundefs_bound_var_fundefs.
        repeat normalize_bound_var_in_ctx.
        eapply Disjoint_Included; [| | eapply H2 ]; sets.
      - eapply Setminus_Included_Included_Union.
        rewrite Fundefs_lambda_lift_name_in_fundefs2 with (B' := B'); eauto.
        rewrite Add_functions_name_in_fundefs; eauto.
        eapply Included_trans.
        eapply Add_functions_LiftedFuns_Included_r. eassumption.
        sets. }
    assert (Hdis : Disjoint var
                            (image σ' (occurs_free_fundefs f2 :|: LiftedFuns ζ' :|: FunsFVs ζ')) (S'0 :|: bound_var_fundefs f2)).
        { repeat normalize_occurs_free_in_ctx. repeat normalize_bound_var_in_ctx.
          eapply Disjoint_Included_l. eapply image_monotonic.
          eapply Included_Union_compat. eapply Included_Union_compat. reflexivity.
          eapply Add_functions_LiftedFuns_Included_r. eassumption.
          eapply Add_functions_FunsFVs_Included_r. eassumption.
          rewrite !Union_assoc. rewrite Union_commut with (s2 := FromList fvs).
          rewrite Union_Same_set. 2:{ eapply Included_trans. eassumption. xsets. }
          rewrite <- !Union_assoc.  rewrite (Union_commut (S \\ S'0)). rewrite !Union_assoc.
          rewrite image_Union.
          rewrite Add_functions_image_Disjoint_Same_set; eauto.
          rewrite Add_functions_image_LiftedFuns_Same_set; eauto.
          repeat find_subsets.
          eapply Union_Disjoint_r; eapply Union_Disjoint_l; sets.
          -- eapply Disjoint_Included; [| | eapply H1 ]; sets.
          -- eapply Disjoint_Included; [| | eapply H1 ]; sets.
          -- eapply Disjoint_Included; [| | eapply H2 ]; sets.
          -- eapply Disjoint_Included_r. eapply name_in_fundefs_bound_var_fundefs.
             eapply Disjoint_Included; [| | eapply H2 ]; sets.
          -- eapply Union_Disjoint_r. eapply Union_Disjoint_l. eapply Union_Disjoint_l.
             eapply Disjoint_sym. now eapply Disjoint_Included; [| | eapply H2 ]; sets.
             eapply Disjoint_sym. now eapply Disjoint_Included; [| | eapply H3 ]; sets.
             eapply Disjoint_sym. now eapply Disjoint_Included; [| | eapply H3 ]; sets.
             eapply Disjoint_Included_r. eapply name_in_fundefs_bound_var_fundefs.
             rewrite <- Union_assoc. eapply Union_Disjoint_l.
             eapply Disjoint_sym. now eapply Disjoint_Included; [| | eapply H4 ]; sets.
             eapply Disjoint_sym. now eapply Disjoint_Included; [| | eapply H5 ]; sets. }
    eapply Union_Included; sets.
    + assert (Hsub' : occurs_free_fundefs B' \subset
                      image σ' (occurs_free_fundefs f2 :|: LiftedFuns ζ' :|: FunsFVs ζ') :|: LiftedFuns ζ' \\ name_in_fundefs f2).
      { specialize IHB with (Bpre := Fnil).
        edestruct IHB as [IHB' _].
        apply IHB'; eauto.
        * reflexivity.
        * intros; eapply Add_functions_same_name; eauto.
        * repeat normalize_occurs_free_in_ctx. repeat normalize_bound_var_in_ctx.
          repeat find_subsets. eapply Disjoint_Included; [ | | eapply H2 ]; sets.
        * eapply Disjoint_Included_r.
          eapply Included_Union_compat.
          eapply Add_functions_LiftedFuns_Included_r. eassumption.
          eapply Add_functions_FunsFVs_Included_r. eassumption.
          repeat find_subsets. eapply Union_Disjoint_r.
          eapply Union_Disjoint_r; sets.
          eapply Disjoint_Included_l. eassumption. now sets.
          eapply Union_Disjoint_r; sets.
          eapply Disjoint_Included_l. eassumption. now sets.
          eapply Disjoint_Included_l. eassumption.
          eapply Disjoint_Included_r. eassumption.
          repeat normalize_occurs_free_in_ctx.
          eapply Union_Disjoint_r. clear H3. now xsets.
          now sets.
        * repeat normalize_occurs_free_in_ctx. repeat normalize_bound_var_in_ctx.
          eapply Disjoint_Included; [| | eapply H4 ]; sets.
        * repeat normalize_occurs_free_in_ctx. repeat normalize_bound_var_in_ctx.
          eapply Disjoint_Included_l. eapply Union_Included. reflexivity.
          eapply name_in_fundefs_bound_var_fundefs.
          eapply Disjoint_Included_r.
          eapply Included_Union_compat.
          eapply Add_functions_LiftedFuns_Included_r. eassumption.
          eapply Add_functions_FunsFVs_Included_r. eassumption.
          repeat find_subsets. eapply Union_Disjoint_r.
          eapply Union_Disjoint_r; sets.
          now eapply Disjoint_Included; [| | eapply H5 ]; sets.
          eapply Disjoint_sym. now eapply Disjoint_Included; [| | eapply H2 ]; sets.
          eapply Union_Disjoint_r.
          now eapply Disjoint_Included; [| | eapply H5 ]; sets.
          eapply Disjoint_Included_r. eassumption.
          eapply Union_Disjoint_r.
          eapply Disjoint_Included; [| | eapply H4 ]; sets.
          now eapply Disjoint_Included; [| | eapply H5 ]; sets.
      }
      (* Follows from Hsub', Hsub *)
      eapply Included_trans; [apply Included_Setminus_compat; [apply Hsub'|apply Included_refl] |].
      eapply Included_trans; [|apply Hsub].
      do 2 apply Setminus_Included_Included_Union.
      apply Included_Union_preserv_l.
      eapply Included_trans; [|apply Included_Union_Setminus; eauto with Decidable_DB].
      rewrite !image_Union. repeat apply Union_Included; eauto with Ensembles_DB.
    + rewrite Setminus_Union_distr. eapply Union_Included.
      { eapply Included_trans. eapply Included_Setminus_compat.
        eapply Make_wrappers_occurs_free. eassumption. reflexivity.
        eapply Included_trans; [| eassumption ]. xsets. }
      { eapply Included_trans. eapply Included_Setminus_compat.
        eapply Included_Setminus_compat.
        eapply IHe; eauto.
        - repeat normalize_occurs_free_in_ctx. repeat normalize_bound_var_in_ctx.
          eapply Disjoint_Included_l. eapply image_monotonic.
          eapply Included_Union_compat. eapply Included_Union_compat. reflexivity.
          eapply Add_functions_LiftedFuns_Included_r. eassumption.
          eapply Add_functions_FunsFVs_Included_r. eassumption.
          eapply Disjoint_Included_l. eapply image_monotonic.
          eapply Included_Union_Setminus with (s2 := name_in_fundefs f2). now tci.
          rewrite image_Union.
          rewrite <- Make_wrappers_name_in_fundefs_image; eauto.
          rewrite <- Make_wrapper_image; eauto; sets.
          eapply Union_Disjoint_l.
          + rewrite <- !Union_assoc.  rewrite (Union_commut (S \\ S'0)). rewrite !Union_assoc.
            rewrite Setminus_Union_distr. rewrite image_Union. eapply Union_Disjoint_l.
            * rewrite Add_functions_image_Disjoint_Same_set; eauto.
              2:{ eapply Union_Disjoint_r; sets. rewrite !Setminus_Union_distr.
                  eapply Union_Disjoint_l. eapply Union_Disjoint_l. eapply Union_Disjoint_l.
                  eapply Disjoint_sym. now eapply Disjoint_Included; [| | eapply H2 ]; sets.
                  eapply Disjoint_sym. now eapply Disjoint_Included; [| | eapply H3 ]; sets.
                  eapply Disjoint_sym. now eapply Disjoint_Included; [| | eapply H3 ]; sets.
                  eapply Disjoint_Included_l. eapply Setminus_Included.
                  eapply Disjoint_Included_l. eassumption.
                  eapply Union_Disjoint_l; [| eapply Union_Disjoint_l ].
                  eapply Disjoint_sym. now eapply Disjoint_Included; [| | eapply H2 ]; sets.
                  eapply Disjoint_sym. now eapply Disjoint_Included; [| | eapply H3 ]; sets.
                  eapply Disjoint_sym. now eapply Disjoint_Included; [| | eapply H3 ]; sets. }
              eapply Disjoint_Included; [| | eapply H1 ].
              repeat find_subsets. eapply Union_Included; sets. eapply Included_trans. eassumption.
              eapply Included_trans. eassumption. now sets.
              rewrite !Setminus_Union_distr. eapply image_monotonic.
              eapply Union_Included; sets.  eapply Setminus_Included_Included_Union.
              eapply Included_trans. eassumption. xsets.
            * eapply Disjoint_Included_l. eapply image_monotonic. eapply Setminus_Included.
              rewrite Add_functions_image_LiftedFuns_Same_set; eauto.
              repeat find_subsets.
              eapply Union_Disjoint_r.
              eapply Disjoint_Included_r. eassumption. now sets.
              now eapply Disjoint_Included; [| | eapply H2 ]; sets.
              eapply Disjoint_Included_r. eapply name_in_fundefs_bound_var_fundefs.
              now eapply Disjoint_Included; [| | eapply H2 ]; sets.
          + eapply Disjoint_Included_l.
            eapply name_in_fundefs_bound_var_fundefs. eapply Disjoint_Included_l. eapply Make_wrappers_bound_var.
            eassumption.
            eapply Union_Disjoint_r. sets.
            eapply Disjoint_Included; [| | eapply H2 ]; sets.
            eapply Included_trans. eapply Setminus_Included.
            repeat find_subsets.
            eapply Included_trans. eassumption. sets.
        - repeat find_subsets.
          eapply Disjoint_Included_r. eapply bound_var_occurs_free_Efun_Included.
          eapply Disjoint_Included_l; [| eassumption ].
          eapply Included_trans. eassumption.
          eapply Included_trans; eassumption.
        - eapply Disjoint_Included_r.
          eapply Included_Union_compat.
          eapply Add_functions_LiftedFuns_Included_r. eassumption.
          eapply Add_functions_FunsFVs_Included_r. eassumption.
          repeat find_subsets. eapply Union_Disjoint_r.
          eapply Union_Disjoint_r; sets.
          eapply Disjoint_Included_l. eassumption.
          eapply Disjoint_Included_l. eassumption.
          eapply Disjoint_Included_l. eassumption. now sets.
          eapply Disjoint_Included_l. eassumption. now sets.
          eapply Disjoint_Included_l. eassumption.
          eapply Union_Disjoint_r.
          eapply Disjoint_Included_l. eassumption.
          eapply Disjoint_Included_l. eassumption. now sets.
          eapply Disjoint_Included_r. eassumption.
          repeat normalize_occurs_free_in_ctx. repeat normalize_bound_var_in_ctx.
          eapply Union_Disjoint_r.
          eapply Disjoint_Included_l. eassumption.
          eapply Disjoint_Included_l. eassumption.
          eapply Disjoint_Included_r; [| eapply H2 ]. now sets.
          eapply Disjoint_Included_l. eassumption.
          eapply Disjoint_Included_l. eassumption. now sets.
        - repeat normalize_occurs_free_in_ctx. repeat normalize_bound_var_in_ctx.
          eapply Disjoint_Included_r. eapply Included_Union_Setminus with (s2 := name_in_fundefs f2).
          tci. eapply Union_Disjoint_r; xsets.
          eapply Disjoint_Included; [| | eapply H4 ]; sets.
          eapply Disjoint_Included_r. eapply name_in_fundefs_bound_var_fundefs. now sets.
        - repeat normalize_occurs_free_in_ctx. repeat normalize_bound_var_in_ctx.
          eapply Disjoint_Included_r.
          eapply Included_Union_compat.
          eapply Add_functions_LiftedFuns_Included_r. eassumption.
          eapply Add_functions_FunsFVs_Included_r. eassumption.
          repeat find_subsets. eapply Union_Disjoint_r.
          eapply Union_Disjoint_r; sets.
          eapply Disjoint_Included; [| | eapply H5 ]; sets.
          eapply Disjoint_sym. now eapply Disjoint_Included; [| | eapply H2 ]; sets.
          eapply Union_Disjoint_r.
          eapply Disjoint_Included; [| | eapply H5 ]; sets.
          eapply Disjoint_Included_r. eassumption.
          eapply Union_Disjoint_r.
          eapply Disjoint_Included; [| | eapply H4 ]; now sets.
          eapply Disjoint_Included; [| | eapply H5 ]; now sets.
        - reflexivity.
        - reflexivity.
        - eapply Included_trans; [| eassumption ].
          rewrite !Setminus_Union_distr. eapply Union_Included; [| now sets ].
          eapply Included_trans. eapply Included_Setminus_compat. eapply Included_Setminus_compat.
          eapply image_monotonic.
          eapply Included_Union_Setminus with (s2 := name_in_fundefs f2). now tci. reflexivity. reflexivity.
          rewrite image_Union. do 2 rewrite Setminus_Union_distr. eapply Union_Included.
          + rewrite <- Make_wrapper_image; eauto. rewrite !Setminus_Union_distr.
            eapply Included_Union_preserv_l. rewrite Setminus_Union.
            eapply Included_Setminus_compat. now sets. now sets.
            now sets.
          + rewrite <- Make_wrappers_name_in_fundefs_image; eauto. now sets. }
  - inv H0. repeat normalize_occurs_free.
    eapply Union_Included.
    + repeat normalize_occurs_free_in_ctx. repeat normalize_bound_var_in_ctx.
      eapply Included_trans.
      edestruct IHB with (Bpre := Fnil) as [_ IHB'].
      apply IHB'; eauto. reflexivity.
      * apply extend_fundefs_eq.
      * rewrite extend_fundefs_image.
        eapply Disjoint_Included; [| | eapply H1 ]; now sets.
        eapply Disjoint_Included_r. eapply name_in_fundefs_bound_var_fundefs.
        eapply Union_Disjoint_l.
        eapply Union_Disjoint_l.
        eapply Disjoint_sym. now eapply Disjoint_Included; [| | eapply H4 ]; sets.
        eapply Disjoint_sym. now eapply Disjoint_Included; [| | eapply H5 ]; sets.
        eapply Disjoint_sym. now eapply Disjoint_Included; [| | eapply H5 ]; sets.
      * eapply Disjoint_sym.
        clear H3. now sets.
      * now eapply Disjoint_Included; [| | eapply H4 ]; sets.
      * eapply Disjoint_Included_l. eapply Union_Included. reflexivity.
        eapply name_in_fundefs_bound_var_fundefs.
        now sets.
      * rewrite extend_fundefs_image.
        now xsets.
        eapply Disjoint_Included_r. eapply name_in_fundefs_bound_var_fundefs.
        eapply Union_Disjoint_l.
        eapply Union_Disjoint_l.
        eapply Disjoint_sym. now eapply Disjoint_Included; [| | eapply H4 ]; sets.
        eapply Disjoint_sym. now eapply Disjoint_Included; [| | eapply H5 ]; sets.
        eapply Disjoint_sym. now eapply Disjoint_Included; [| | eapply H5 ]; sets.
    + repeat normalize_occurs_free_in_ctx. repeat normalize_bound_var_in_ctx.
      eapply Included_trans. eapply Included_Setminus_compat; [| reflexivity ].
      eapply IHe; eauto.
      * eapply Disjoint_Included_l.
        eapply image_extend_fundefs. eapply Union_Disjoint_l.
        eapply Disjoint_Included; [| | eapply H1 ].
        repeat find_subsets. now sets.
        rewrite !Setminus_Union_distr. sets.
        eapply Disjoint_Included_l. eapply name_in_fundefs_bound_var_fundefs.
        repeat find_subsets. eapply Union_Disjoint_r.
        eapply Disjoint_sym. now eapply Disjoint_Included; [| | eapply H2 ]; sets.
        now sets.
      * repeat find_subsets.
        eapply Disjoint_Included; [| | eapply H2 ]; sets.
        eapply Union_Included; sets. rewrite !Union_assoc.
        rewrite Union_Setminus_Included; sets.
        now tci. eapply Included_trans. eapply name_in_fundefs_bound_var_fundefs. now sets.
      * repeat find_subsets.
        eapply Disjoint_Included; [| | eapply H3 ]; sets.
      * eapply Disjoint_Included_r.
        eapply Included_Union_Setminus with (s2 := name_in_fundefs f2). tci.
        eapply Union_Disjoint_r.
        now eapply Disjoint_Included; [| | eapply H4 ]; sets.
        eapply Disjoint_Included_r. eapply name_in_fundefs_bound_var_fundefs. now sets.
      * now sets.
      * eapply Included_trans.
        eapply Included_Setminus_compat. eapply Included_Union_compat.
        eapply image_extend_fundefs. reflexivity. reflexivity.
        rewrite Fundefs_lambda_lift_name_in_fundefs3 with (B':= B'); eauto.
        rewrite !Setminus_Union_distr.
        rewrite Setminus_Same_set_Empty_set. normalize_sets.
        eapply Union_Included; sets.
        eapply Included_Union_preserv_l. sets.
  - repeat normalize_occurs_free. rewrite FromList_map_image_FromList. rewrite FromList_app.
    rewrite !image_Union. eapply Union_Included. eapply Union_Included.
    now sets.
    eapply Included_Union_preserv_l. eapply Included_Union_preserv_r.
    eapply image_monotonic. intros z Hc. do 4 eexists.
    now split; eauto.
    do 2 eapply Included_Union_preserv_l. eapply Included_Union_preserv_r.
    eapply Singleton_Included. eapply In_image. eexists. split. eexists.
    eapply lifted_name_eq; eauto.
    eapply lifted_name_eq; eauto.
  - repeat normalize_occurs_free. rewrite FromList_map_image_FromList.
    rewrite !image_Union, image_Singleton. sets.
  - inv H0. repeat normalize_occurs_free.
    rewrite !image_Union.
    eapply Included_trans.
    eapply Included_Setminus_compat.
    eapply IHe; eauto.
    + eapply Disjoint_Included_l.
      eapply Included_trans. eapply image_extend_Included'. reflexivity.
      rewrite !Setminus_Union_distr.
      repeat normalize_bound_var_in_ctx. repeat normalize_occurs_free_in_ctx.
      eapply Union_Disjoint_l; sets.
      eapply Disjoint_Included; [| | eapply H1 ]; sets.
      eapply Union_Disjoint_r.
      eapply Disjoint_sym. eapply Disjoint_Included; [| | eapply H2 ]; sets.
      sets.
    + eapply Disjoint_Included_r. eapply bound_var_occurs_free_Eprim_val_Included. eassumption.
    + repeat normalize_occurs_free_in_ctx. repeat normalize_bound_var_in_ctx.
      eapply Disjoint_Included_r. eapply Included_Union_Setminus with (s2 := [set v]).
      tci. eapply Union_Disjoint_r; sets.
    + repeat normalize_bound_var_in_ctx. sets.
    + reflexivity.
    + rewrite !Setminus_Union_distr.
      eapply Union_Included; [| now sets ].
      eapply Included_trans. eapply Included_Setminus_compat.
      eapply image_extend_Included'. reflexivity.
      rewrite !Setminus_Union_distr, !image_Union, !Setminus_Union_distr.
      eapply Union_Included; sets.
      eapply Union_Included; sets.
      eapply Union_Included; xsets.

  - inv H0. repeat normalize_occurs_free.
    rewrite FromList_map_image_FromList. eapply Union_Included. now sets.
    eapply Included_trans. eapply Included_Setminus_compat.
    eapply IHe; eauto.
    + eapply Disjoint_Included_l.
      eapply Included_trans. eapply image_extend_Included'. reflexivity.
      rewrite !Setminus_Union_distr.
      repeat normalize_bound_var_in_ctx. repeat normalize_occurs_free_in_ctx.
      eapply Union_Disjoint_l; sets.
      eapply Disjoint_Included; [| | eapply H1 ]; sets.
      eapply Union_Disjoint_r.
      eapply Disjoint_sym. eapply Disjoint_Included; [| | eapply H2 ]; sets.
      sets.
    + eapply Disjoint_Included_r. eapply bound_var_occurs_free_Eprim_Included. eassumption.
    + repeat normalize_occurs_free_in_ctx. repeat normalize_bound_var_in_ctx.
      eapply Disjoint_Included_r. eapply Included_Union_Setminus with (s2 := [set v]).
      tci. eapply Union_Disjoint_r; sets.
      eapply Disjoint_Included; [| | eapply H4 ]; sets.
    + repeat normalize_bound_var_in_ctx. sets.
    + reflexivity.
    + rewrite !Setminus_Union_distr.
      eapply Union_Included; [| now sets ].
      eapply Included_trans. eapply Included_Setminus_compat.
      eapply image_extend_Included'. reflexivity.
      rewrite !Setminus_Union_distr, !image_Union, !Setminus_Union_distr.
      eapply Union_Included; sets.
      eapply Union_Included; sets.
      eapply Union_Included; xsets.
  - repeat normalize_occurs_free.
    rewrite !image_Union, image_Singleton. sets.
  - split; intros; inv H.
  { inv H1. repeat normalize_occurs_free. repeat normalize_sets. simpl.
    remember (fundefs_append Bpre (Fcons v t0 l e f5)) as B0 eqn:HeqB0.
    rewrite !Setminus_Union_distr, !Setminus_Union. eapply Union_Included. eapply Union_Included.
    + eapply Included_trans. eapply Included_Setminus_compat.
      eapply Make_wrappers_occurs_free. eassumption. reflexivity.
      rewrite Setminus_Union_distr. eapply Union_Included.
      * eapply Included_trans. eapply Included_Setminus_compat.
        eapply image_extend_lst_Included. rewrite !length_app.
        rewrite H24. reflexivity. reflexivity. repeat normalize_sets.
        apply Included_Union_preserv_l.
        rewrite !image_Union, !Setminus_Union_distr.
        (* σ(FunsFVs ζ\(l∪fvs)) ⊆ σ(FunsFVs ζ)\names(B0) because H5 says σ(FunsFVs ζ) # BV(B0) *)
        apply Included_Union_preserv_r.
        repeat apply Union_Included; eauto with Ensembles_DB.
        eapply Setminus_Included_Included_Union, Included_Union_preserv_l.
        eapply Included_trans; [apply image_monotonic, Setminus_Included |].
        apply Included_Setminus; eauto with Ensembles_DB.
        eapply Disjoint_Included_l; [|eapply Disjoint_Included_r; [|apply H5]].
        { rewrite !image_Union; eauto with Ensembles_DB.  }
        { eapply Included_trans; [apply name_in_fundefs_bound_var_fundefs|]; eauto with Ensembles_DB. }
      * (* LiftedFuns ζ \ names(B0) = LiftedFuns ζ because LiftedFuns ζ # names(B0) by H9 *)
        apply Included_Union_preserv_r.
        apply Setminus_Included_preserv.
        apply Included_Setminus; eauto with Ensembles_DB.
        apply Disjoint_sym; eapply Disjoint_Included_l; [|eapply Disjoint_Included_r; [|apply H9]];
        eauto with Ensembles_DB.
    + subst B0. repeat normalize_bound_var_in_ctx. repeat normalize_occurs_free_in_ctx.
      eapply Included_trans. eapply Included_Setminus_compat.
      (* eapply Included_Setminus_compat. *) eapply IHe; try eassumption.
      * eapply Disjoint_Included_l. eapply image_monotonic.
        eapply Included_Union_Setminus with (s2 := name_in_fundefs (fundefs_append Bpre (Fcons v t0 l e f5))).
        now tci.
        rewrite image_Union.
        rewrite <- Make_wrappers_name_in_fundefs_image; eauto.
        rewrite <- Make_wrapper_image; eauto; sets.
        eapply Union_Disjoint_l.
        eapply Disjoint_Included_l.
        eapply image_extend_lst_Included. rewrite !length_app. rewrite H24. reflexivity.
        repeat normalize_sets.
        rewrite !Setminus_Union. rewrite !Setminus_Union_distr.
        eapply Union_Disjoint_l.
        -- eapply Disjoint_Included; [| | eapply H5 ].
           ++ repeat find_subsets.
              eapply Union_Included; sets.
              eapply Included_trans. eassumption. sets.
              rewrite fundefs_append_bound_vars; [|reflexivity].
              normalize_bound_var; eauto with Ensembles_DB.
           ++ eapply image_monotonic. eapply Union_Included; sets. eapply Union_Included; sets.
              do 2 eapply Included_Union_preserv_l.
              apply Setminus_Included_Included_Union.
              rewrite !fundefs_append_occurs_free. normalize_occurs_free.
              rewrite <- !Union_assoc.
              eapply Included_trans; [| apply Included_Union_r].
              rewrite (Union_commut (occurs_free e \\ _) (occurs_free_fundefs f5 \\ _)).
              rewrite !Setminus_Union_distr, !Setminus_Union, <- !Union_assoc.
              eapply Included_trans; [| apply Included_Union_r].
              apply Included_Union_Setminus_Included_Union; eauto with Decidable_DB.
              ** repeat apply Union_Included; eauto with Ensembles_DB.
                 { rewrite fundefs_append_name_in_fundefs by reflexivity.
                   simpl; eauto with Ensembles_DB. }
                 { rewrite (fundefs_append_name_in_fundefs Bpre (Fcons v t0 l e f5) (fundefs_append Bpre _))
                     by reflexivity.
                   simpl; eauto with Ensembles_DB. }
              ** eauto with Ensembles_DB.
        -- repeat find_subsets.
           (* l # S'0 because S'0 ⊆ S and H6.
              ys # S'0 because S'0 ⊆ S\ys.
              l # BV(e) because UB(B0).
              ys # BV(e) because ys ⊆ S and H6. *)
           apply Union_Disjoint_r; apply Union_Disjoint_l.
           { eapply Disjoint_Included_r with (s2 := S).
             - eapply Included_trans; eauto with Ensembles_DB.
             - eapply Disjoint_sym, Disjoint_Included_r; [|apply H6].
               rewrite fundefs_append_bound_vars by reflexivity; normalize_bound_var.
               eauto with Ensembles_DB. }
           { eapply Disjoint_Included_r; [eassumption|]; eauto with Ensembles_DB. }
           { now apply Disjoint_sym. }
           { eapply Disjoint_Included_l; [apply H16|].
             eapply Disjoint_Included_r; [|apply H6].
             rewrite fundefs_append_bound_vars by reflexivity; normalize_bound_var.
             eauto with Ensembles_DB. }
        -- eapply Disjoint_Included_l. eapply name_in_fundefs_bound_var_fundefs.
           eapply Disjoint_Included_l. eapply Make_wrappers_bound_var. eassumption.
           eapply Union_Disjoint_r; sets.
           eapply Disjoint_Included; [| | eapply H6 ]; sets.
           rewrite fundefs_append_bound_vars by reflexivity; normalize_bound_var.
           eauto with Ensembles_DB.
      * repeat find_subsets.
        apply Union_Disjoint_r.
        { eapply Disjoint_Included_l with (s3 := S); [eapply Included_trans; eauto with Ensembles_DB|].
          eapply Disjoint_Included_r; [|apply H6].
          rewrite fundefs_append_bound_vars by reflexivity; normalize_bound_var.
          eauto with Ensembles_DB. }
        { eapply Disjoint_Included_l with (s3 := S); [eapply Included_trans; eauto with Ensembles_DB|].
          eapply Disjoint_Included_r; [|apply H6].
          rewrite Union_commut, <- Union_assoc, Union_commut, <- !Union_assoc.
          eapply Included_trans; [|eapply Included_Union_r].
          rewrite Union_commut.
          apply Included_Union_Setminus_Included_Union; eauto with Decidable_DB; eauto with Ensembles_DB.
          rewrite fundefs_append_bound_vars by reflexivity; normalize_bound_var.
          repeat apply Union_Included; eauto with Ensembles_DB.
          eapply Included_trans; [apply name_in_fundefs_bound_var_fundefs|]; eauto with Ensembles_DB. }
      * repeat find_subsets.
        eapply Disjoint_Included_l. eassumption. now sets.
      * eapply Disjoint_Included_r.
        eapply Included_Union_Setminus with (s2 := (v |: (FromList l :|: name_in_fundefs f5))). now tci.
        eapply Union_Disjoint_r; sets.
        eapply Disjoint_Included; [| | eapply H8 ]; sets.
        eapply Union_Disjoint_r; sets.
        eapply Union_Disjoint_r; sets.
        eapply Disjoint_Included_r. eapply name_in_fundefs_bound_var_fundefs. now sets.
      * now sets.
      * reflexivity.
      * rewrite !Setminus_Union_distr. eapply Union_Included; sets.
        eapply Included_trans. eapply Included_Setminus_compat. (* eapply Included_Setminus_compat. *)
        eapply image_monotonic.
        eapply Included_Union_Setminus with (s2 := v |: (FromList l :|: name_in_fundefs f5)). now tci.
        reflexivity.
        rewrite image_Union. do 2 rewrite Setminus_Union_distr. eapply Union_Included.
        -- match goal with |- context [image σ' ?S] => remember S as Dom end.
           remember (fundefs_append Bpre (Fcons v t0 l e f5)) as B0.
           assert (Hdom : Dom \subset (Dom \\ name_in_fundefs B0) :|: name_in_fundefs B0). {
             apply Included_Union_Setminus; eauto with Decidable_DB; eauto with Ensembles_DB. }
           eapply Included_trans; [apply Included_Setminus_compat; [eapply image_monotonic, Hdom|apply Included_refl] | ].
           rewrite image_Union, Setminus_Union_distr; apply Union_Included.
           { rewrite <- Make_wrapper_image; eauto. 2: eauto with Ensembles_DB.
             subst Dom; rewrite !Setminus_Union_distr.
             eapply Included_trans. eapply Included_Setminus_compat.
             eapply image_extend_lst_Included. rewrite !length_app.
             rewrite H24. reflexivity. reflexivity. repeat normalize_sets.
             eapply Included_Union_preserv_l.
             repeat rewrite !Setminus_Union_distr, !Setminus_Union.
             apply Union_Included.
             2:{ apply Union_Included; eauto 10 with Ensembles_DB. }
             apply Setminus_Included_Included_Union, Included_Union_preserv_l.
             rewrite !image_Union.
             repeat apply Union_Included.
             { (* (e \ ...) ⊆ fv(B0).
                  σ(e \ ...) ⊆ σ(fv(B0)) # BV(B0) ⊇ names(B0) by H5.
                  Thus σ(e \ ...) ⊆ fv(B0) \ names(B0) *)
               assert (Hsub : occurs_free e \\
                                          (v |: (FromList l :|: name_in_fundefs f5) :|:
                                             name_in_fundefs B0 :|:
                                             (FromList l :|: FromList fvs))
                                          \subset occurs_free_fundefs B0). {
                 subst B0; rewrite !fundefs_append_occurs_free.
                 repeat normalize_occurs_free.
                 rewrite !Setminus_Union_distr.
                 apply Included_Union_preserv_r.
                 apply Included_Union_preserv_l.
                 rewrite Setminus_Union.
                 apply Included_Setminus_compat; sets. }
               rewrite !Setminus_Union_distr.
               do 2 apply Included_Union_preserv_l.
               apply Included_Setminus.
               - eapply Disjoint_Included_l; [|eapply Disjoint_Included_r; [|apply H5]].
                 + rewrite !image_Union; do 2 apply Included_Union_preserv_l; sets.
                 + eapply Included_trans; [apply name_in_fundefs_bound_var_fundefs|]; eauto with Ensembles_DB.
               - apply image_monotonic; sets. }
             { rewrite !Setminus_Union_distr.
               apply Included_Union_preserv_l; apply Included_Union_preserv_r.
               apply Included_Setminus.
               - eapply Disjoint_Included_l; [|eapply Disjoint_Included_r; [|apply H5]].
                 2: eapply Included_trans; [apply name_in_fundefs_bound_var_fundefs|]; eauto with Ensembles_DB.
                 apply image_monotonic, Setminus_Included_Included_Union; eauto with Ensembles_DB.
               - apply image_monotonic; eauto with Ensembles_DB. }
             { rewrite !Setminus_Union_distr.
               apply Included_Union_preserv_r.
               apply Included_Setminus.
               - eapply Disjoint_Included_l; [|eapply Disjoint_Included_r; [|apply H5]].
                 2: eapply Included_trans; [apply name_in_fundefs_bound_var_fundefs|]; eauto with Ensembles_DB.
                 apply image_monotonic, Setminus_Included_Included_Union; eauto with Ensembles_DB.
               - apply image_monotonic; eauto with Ensembles_DB. } }
           { rewrite <- Make_wrappers_name_in_fundefs_image; try eassumption.
             eauto with Ensembles_DB. }
        -- eapply Included_trans.
           eapply Included_Setminus_compat.
           rewrite !Union_assoc. rewrite (Union_commut [set v]). rewrite <- Union_assoc, image_Union.
           eapply Included_Union_compat.
           rewrite <- Make_wrapper_image; [| eassumption | ].
           rewrite extend_lst_app. eapply image_extend_lst_Included. reflexivity. reflexivity.
           { (* unique_bindings B0 /\ B0 = Bpre ++ Fcons v t l e f5 *)
             eapply fundefs_append_unique_bindings_l in H2; try reflexivity.
             decompose [and] H2; clear H2. inv H3.
             normalize_bound_var_in_ctx.
             rewrite fundefs_append_name_in_fundefs by reflexivity; simpl.
             repeat apply Union_Disjoint_r.
             { apply Disjoint_sym; eapply Disjoint_Included_l; [|eapply Disjoint_Included_r; [|apply H10]];
                 eauto with Ensembles_DB.
               apply name_in_fundefs_bound_var_fundefs. }
             { apply Disjoint_Singleton_r. assumption. }
             { apply Disjoint_sym. eapply Disjoint_Included_l; [|eassumption].
               apply name_in_fundefs_bound_var_fundefs. } }
           eapply @image_monotonic with (S' := name_in_fundefs (fundefs_append Bpre (Fcons v t0 l e f5))).
           eassumption. reflexivity. rewrite Setminus_Same_set_Empty_set, image_Empty_set.
           rewrite <- Make_wrappers_name_in_fundefs_image; eauto.
           rewrite !Setminus_Union_distr. eapply Union_Included. eapply Union_Included.
           now sets. now xsets. now xsets.
        -- (* LiftedFuns ζ \ names(B0) = LiftedFuns ζ because LiftedFuns ζ # names(B0) by H9 *)
          apply Included_Union_preserv_r.
          apply Setminus_Included_Included_Union, Included_Union_preserv_l.
          apply Included_Setminus; eauto with Ensembles_DB.
          apply Disjoint_sym; eapply Disjoint_Included_l; [|eapply Disjoint_Included_r; [|apply H9]];
            eauto with Ensembles_DB.
    + subst B0. repeat normalize_bound_var_in_ctx. repeat normalize_occurs_free_in_ctx.
      eapply Included_trans. eapply Included_Setminus_compat.
      edestruct IHB with (Bpre := fundefs_append Bpre (Fcons v t0 l e Fnil)) as [IHB' _].
      apply IHB'; eauto.
      * eapply Included_trans; [| eassumption ]. now sets.
      * rewrite <- fundefs_append_assoc; now simpl.
      * intros; rewrite H4; auto. now right.
      * repeat find_subsets.
        (* S'' ⊆ S /\ H5 *)
        eapply Disjoint_Included_r; [|apply H5].
        apply Included_Union_compat; eauto with Ensembles_DB.
        eapply Included_trans; eauto with Ensembles_DB.
        eapply Included_trans; eauto with Ensembles_DB.
      * repeat find_subsets.
        eapply Disjoint_Included_l; [|eapply Disjoint_Included_r; [|apply H6]].
        -- eapply Included_trans; eauto with Ensembles_DB.
           eapply Included_trans; eauto with Ensembles_DB.
        -- apply Union_Included; eauto with Ensembles_DB.
           rewrite fundefs_append_bound_vars by reflexivity.
           rewrite <- !Union_assoc. apply Included_Union_preserv_r.
           normalize_bound_var.
           rewrite <- !Union_assoc, Union_commut, <- !Union_assoc.
           do 4 apply Included_Union_preserv_r.
           apply Included_Union_Setminus; auto with Decidable_DB.
      * (* S'' ⊆ S /\ H7 *)
        repeat find_subsets.
        eapply Disjoint_Included_l; [|apply H7].
        eapply Included_trans; eauto with Ensembles_DB.
        eapply Included_trans; eauto with Ensembles_DB.
      * constructor; intros x Hx; inv Hx.
        destruct (Pos.eq_dec x v) as [Heq|Hne]; subst.
        { now contradiction H14. }
        { destruct H8 as [Hc]. contradiction (Hc x).
          constructor; auto. right; constructor; auto.
          inversion 1; now subst. }
      * (* H9 *) eapply Disjoint_Included_l; [|apply H9].
        eapply Included_Union_compat; eauto with Ensembles_DB.
      * reflexivity.
      * remember (fundefs_append Bpre (Fcons v t0 l e f5)) as B0.
        (* σ(...) ⊆ (σ(...)\names(B0)) ∪ names(B0). *)
        apply Setminus_Included_Included_Union, Included_Union_preserv_l.
        apply Setminus_Included_Included_Union.
        apply Union_Included.
        { rewrite (Union_commut (_ \\ _) (_ \\ _)).
          rewrite <- (Union_assoc (_ \\ _) _ (name_in_fundefs B0)).
          apply Included_Union_preserv_r.
          apply Included_Union_Setminus; sets; auto with Decidable_DB. }
        { rewrite <- Union_assoc; apply Included_Union_preserv_r.
          apply Included_Union_Setminus; sets; auto with Decidable_DB. } }
  { inv H1.
    repeat normalize_bound_var_in_ctx. repeat normalize_occurs_free_in_ctx.
    repeat normalize_occurs_free. repeat normalize_sets. simpl.
    remember (fundefs_append Bpre (Fcons v t0 l e f5)) as B0 eqn:HeqB0.
    eapply Union_Included.
    + eapply Included_trans. eapply Included_Setminus_compat; [| reflexivity ].
      eapply IHe; try eassumption.
      * eapply Disjoint_Included_l.
        eapply image_extend_lst_Included. reflexivity.
        eapply Union_Disjoint_l.
        -- eapply Disjoint_Included_l.
           eapply image_extend_fundefs.
           eapply Union_Disjoint_l.
           rewrite !Setminus_Union_distr.
           eapply Disjoint_Included; [| | eapply H5 ]; sets.
           ++ (* BV(e) ⊆ BV(B0) *)
              apply Included_Union_compat; sets.
              subst B0; rewrite fundefs_append_bound_vars by reflexivity; normalize_bound_var; sets.
           ++ eapply image_monotonic. eapply Union_Included; sets. eapply Union_Included; sets.
              (* normalize FV(B0) *)
              do 2 apply Included_Union_preserv_l.
              do 2 apply Setminus_Included_Included_Union.
              rewrite <- Union_assoc.
              subst B0; rewrite fundefs_append_occurs_free.
              rewrite <- Union_assoc.
              apply Included_Union_preserv_r.
              normalize_occurs_free.
              rewrite !Setminus_Union_distr.
              rewrite Union_commut.
              rewrite !Union_assoc.
              apply Included_Union_preserv_l.
              rewrite !Setminus_Union.
              rewrite Union_commut.
              apply Included_Union_Setminus_Included_Union; sets; eauto with Decidable_DB.
              (repeat apply Union_Included); sets.
              { rewrite fundefs_append_name_in_fundefs by reflexivity; simpl; sets. }
              { rewrite (fundefs_append_name_in_fundefs Bpre _ (fundefs_append _ _)) by reflexivity; simpl; sets. }
           ++ (* names(B0) # S by H6, names(B0) # BV(e) by UB(B0) *)
              eapply Union_Disjoint_r.
              { apply Disjoint_sym; eapply Disjoint_Included_l; [|eapply Disjoint_Included_r; [|apply H6]]; sets.
                apply Included_Union_preserv_l, name_in_fundefs_bound_var_fundefs. }
              { subst B0.
                eapply fundefs_append_unique_bindings_l in H2; [|reflexivity].
                decompose [and] H2; clear H2.
                normalize_bound_var_in_ctx.
                inv H3.
                rewrite fundefs_append_name_in_fundefs by reflexivity.
                apply Union_Disjoint_l.
                - eapply Disjoint_Included_l; [|eapply Disjoint_Included_r; [|apply H10]]; sets.
                  apply name_in_fundefs_bound_var_fundefs.
                - simpl; apply Union_Disjoint_l; sets.
                  apply Disjoint_sym.
                  eapply Disjoint_Included_l; [|eapply Disjoint_Included_r; [|apply H29]]; sets.
                  apply name_in_fundefs_bound_var_fundefs.  }
        -- (* l # S by H6; l # e by UB(B0) *)
           apply Union_Disjoint_r.
           { apply Disjoint_sym; eapply Disjoint_Included_l; [|eapply Disjoint_Included_r; [|apply H6]]; sets.
             apply Included_Union_preserv_l; subst B0; rewrite fundefs_append_bound_vars by reflexivity.
             normalize_bound_var; sets. }
           { subst B0.
             eapply fundefs_append_unique_bindings_l in H2; [|reflexivity].
             decompose [and] H2; clear H2.
             inv H3. apply Disjoint_sym; sets. }
      * eapply Disjoint_Included; [| | eapply H6 ]; xsets.
        (* BV(e) ⊆ BV(B0).
           FV(e) ⊆ (FV(e) \ (v ∪ l ∪ names(f5))) ∪ BV(B0) because v ∪ l ∪ names(f5) ⊆ BV(B0) *)
        apply Union_Included.
        { apply Included_Union_preserv_l.
          subst B0; rewrite fundefs_append_bound_vars by reflexivity; normalize_bound_var; sets. }
        { rewrite Union_assoc; apply Included_Union_preserv_l; rewrite Union_commut.
          apply Included_Union_Setminus_Included_Union; sets; eauto with Decidable_DB.
          subst B0; rewrite fundefs_append_bound_vars by reflexivity; normalize_bound_var.
          repeat apply Union_Included; sets.
          eapply Included_trans; [apply name_in_fundefs_bound_var_fundefs|]; sets. }
      * eapply Disjoint_Included_r.
        eapply Included_Union_Setminus with (s2 := (v |: (FromList l :|: name_in_fundefs f5))). now tci.
        eapply Union_Disjoint_r; sets.
        eapply Disjoint_Included; [| | eapply H8 ]; sets.
        eapply Union_Disjoint_r; sets.
        eapply Union_Disjoint_r; sets.
        eapply Disjoint_Included_r. eapply name_in_fundefs_bound_var_fundefs. now sets.
      * now sets.
      * rewrite !Setminus_Union_distr. eapply Union_Included; sets.
        eapply Included_trans. eapply Included_Setminus_compat. (* eapply Included_Setminus_compat. *)
        eapply image_monotonic.
        eapply Included_Union_Setminus with (s2 := v |: (FromList l :|: name_in_fundefs f5)). now tci.
        reflexivity.
        do 2 rewrite Setminus_Union_distr.
        eapply Included_trans. eapply Included_Setminus_compat.
        eapply Included_trans. eapply image_extend_lst_Included. reflexivity.
        eapply Included_trans. eapply Included_Union_compat.
        eapply image_extend_fundefs. reflexivity. reflexivity. reflexivity.
        rewrite !Setminus_Union, !Setminus_Union_distr, !Setminus_Union.
        eapply Union_Included; sets.
        eapply Union_Included; sets.
        ++ eapply Setminus_Included_Included_Union.
           (* FV(e) \ .. ⊆ FV(B0).
              LiftedFuns ζ \ .. ⊆ LiftedFuns.
              FunsFVs ζ \ .. ⊆ LiftedFuns.
              v \ .. = ∅ because v ∈ names(B0).
              l \ .. = ∅.
              names(f5) \ .. = ∅ because names(f5) ⊆ names(B0). *)
           do 3 apply Included_Union_preserv_l.
           apply image_monotonic; repeat apply Union_Included; sets.
           { do 2 apply Included_Union_preserv_l.
             subst B0; rewrite fundefs_append_occurs_free.
             apply Included_Union_preserv_r; normalize_occurs_free.
             rewrite Setminus_Union_distr; apply Included_Union_preserv_l.
             rewrite Setminus_Union.
             apply Included_Setminus_compat; sets. }
           { apply Setminus_Included_Included_Union; do 2 apply Included_Union_preserv_r.
             subst B0; rewrite fundefs_append_name_in_fundefs by reflexivity; simpl; sets. }
           { apply Setminus_Included_Included_Union; do 2 apply Included_Union_preserv_r. subst B0.
             rewrite (fundefs_append_name_in_fundefs _ _ (fundefs_append _ _)) by reflexivity. simpl; sets. }
        ++ (* names(B0) \ names(B'0) = names(B0) \ names(f5) = names(Bpre) *)
           apply Included_Union_preserv_r.
           assert (Hsub : name_in_fundefs B0 \\ (v |: (FromList l :|: name_in_fundefs B'0))
                 \subset name_in_fundefs B0 \\ (v |: name_in_fundefs B'0)) by sets.
           eapply Included_trans; [apply Hsub|].
           assert (Hsame : name_in_fundefs B'0 <--> name_in_fundefs f5). {
             eapply Fundefs_lambda_lift_name_in_fundefs3; eauto. }
           rewrite Hsame; subst B0; rewrite fundefs_append_name_in_fundefs by reflexivity; simpl.
           rewrite Setminus_Union_distr.
           apply Union_Included; sets.
    + assert (Heq : v = sig v). { rewrite H4; auto. now left. } rewrite Heq, <- image_Singleton at 1.
      eapply Included_trans. eapply Included_Setminus_compat.
      repeat normalize_bound_var_in_ctx. repeat normalize_occurs_free_in_ctx.
      eapply IHB with (Bpre := fundefs_append Bpre (Fcons v t0 l e Fnil)); eauto.
      * eapply Included_trans; [| eassumption ]. now sets.
      * rewrite <- fundefs_append_assoc; now simpl.
      * intros; apply H4; now right.
      * repeat find_subsets.
        (* S'0 ⊆ S /\ H5 *)
        eapply Disjoint_Included_r; [|apply H5]; apply Union_Included; sets.
      * repeat find_subsets.
        eapply Disjoint_Included; [| | eapply H6 ]; xsets.
        eapply Union_Included. now sets.
        rewrite (Union_commut (_ \\ _)), !Union_assoc.
        eapply Included_Union_preserv_l.
        rewrite Union_Setminus_Included. now sets. tci.
        subst B0; rewrite fundefs_append_bound_vars by reflexivity; normalize_bound_var; sets.
      * repeat find_subsets.
        eapply Disjoint_Included_l. eassumption.
        eapply Disjoint_Included_l; [| eapply H7 ]; sets.
      * eapply Disjoint_Included_r.
        eapply Included_Union_Setminus with (s2 := [set v]). now tci.
        eapply Union_Disjoint_r; sets.
        eapply Disjoint_Included; [| | eapply H8 ]; sets.
      * now sets.
      * reflexivity.
      * rewrite Setminus_Union_distr. eapply Union_Included; sets.
        apply Included_Union_preserv_r.
        rewrite fundefs_append_name_in_fundefs by reflexivity.
        rewrite Setminus_Union_distr; apply Union_Included; sets.
        assert (Himage : image sig [set v] <--> [set v]). {
          split; intros x Hx.
          - inv Hx. destruct H as [Hin Hsig]; inv Hin. now rewrite <- Heq.
          - inv Hx; exists x; now split. }
        simpl; rewrite Himage; sets. }
  - split; intros; inv H; rewrite occurs_free_fundefs_Fnil at 1; sets.
Qed.

Lemma Exp_lambda_lift_occurs_free :
  forall e zeta sig S e' S',
    Exp_lambda_lift zeta sig e S e' S' ->
    unique_bindings e ->
    Disjoint _ (image sig (occurs_free e :|: LiftedFuns zeta :|: FunsFVs zeta)) (S :|: bound_var e) ->
    Disjoint _ S (bound_var e :|: occurs_free e) ->
    Disjoint _ S (LiftedFuns zeta :|: FunsFVs zeta) ->
    Disjoint _ (bound_var e) (occurs_free e) ->
    Disjoint _ (bound_var e) (LiftedFuns zeta :|: FunsFVs zeta) ->
    occurs_free e' \subset image sig (occurs_free e :|: LiftedFuns zeta :|: FunsFVs zeta) :|: LiftedFuns zeta.
Proof. eapply Exp_lambda_lift_occurs_free_mut. Qed.

Lemma Exp_lambda_lift_bound_var_mut :
  (forall e zeta sig S e' S',
      Exp_lambda_lift zeta sig e S e' S' ->
      bound_var e' \subset bound_var e :|: (S \\ S')) /\
  (forall B B0 zeta sig S B' S',
      (Fundefs_lambda_lift2 zeta sig B0 B S B' S' ->
       bound_var_fundefs B' \subset bound_var_fundefs B :|: (S \\ S') :|: image' (lifted_name zeta) (name_in_fundefs B)) /\
      (Fundefs_lambda_lift3 zeta sig B0 B S B' S' ->
       bound_var_fundefs B' \subset bound_var_fundefs B :|: (S \\ S'))).
Proof with now eauto with Ensembles_DB.
  exp_defs_induction IHe IHl IHB; intros; try inv H; try inv H0;
    repeat normalize_bound_var; try now sets;
      try now (repeat normalize_bound_var; eapply Union_Included; sets;
               eapply Included_trans; [ now eapply IHe; sets |]; sets).
  - repeat normalize_bound_var. eapply Union_Included; sets.
    + eapply Included_trans. now eapply IHe; sets.
      eapply Union_Included; sets. repeat find_subsets. sets.
    + eapply Included_trans. rewrite bound_var_Ecase_var. now eapply IHl; eauto.
      repeat find_subsets. sets.
  - repeat normalize_bound_var. eapply Union_Included; [| eapply Union_Included ].
    + edestruct IHB as [IHB1 _]. eapply Included_trans. now eapply IHB1; sets.
      eapply Union_Included; sets. eapply Union_Included. sets. eapply Included_Union_preserv_r.
      repeat find_subsets.
      eapply Included_Setminus_compat. sets. eapply Included_trans; now sets.

      eapply Included_trans. eapply Add_functions_name_in_fundefs_Included.
      eassumption.
      repeat find_subsets.
      eapply Included_Union_preserv_r. eapply Included_Setminus_compat.
      reflexivity. eapply Included_trans. eassumption. eapply Included_trans; now sets.
    + eapply Included_trans. eapply Make_wrappers_bound_var. eassumption.
      repeat find_subsets.
      eapply Included_Union_preserv_r.
      eapply Included_Setminus_compat. eapply Included_trans; eassumption. sets.
    + eapply Included_trans. now eapply IHe; sets.
      eapply Fundefs_Lambda_lift_free_set_Included2 in H5.
      repeat find_subsets.
      eapply Union_Included; sets. eapply Included_Union_preserv_r.
      eapply Included_Setminus_compat. sets. eapply Included_trans. eassumption.
      eapply Included_trans. eassumption. eassumption. reflexivity.
  - repeat normalize_bound_var. eapply Union_Included; sets.
    + edestruct IHB as [_ IHB2]. eapply Included_trans. now eapply IHB2; sets.
      repeat find_subsets.
      eapply Union_Included; sets.
    + eapply Included_trans. now eapply IHe; sets.
      repeat find_subsets.
      eapply Union_Included; sets.
  - constructor.
    { intros H. inv H. edestruct IHB as [IHB1 IHB2]. repeat normalize_bound_var.
      eapply Union_Included; [| eapply Union_Included; [| eapply Union_Included ]]; sets.
      + eapply Included_Union_preserv_r. eapply Singleton_Included.
        simpl. rewrite image'_Union, image'_Singleton_is_Some; eauto.
        eapply lifted_name_eq. eassumption.
      + normalize_sets. eapply Union_Included.
        now sets.
        eapply Included_Union_preserv_l. eapply Included_Union_preserv_r. eapply Included_Setminus; sets.
        repeat find_subsets.
        eapply Disjoint_Included_r. eapply Included_trans. eassumption.
        eapply Included_trans. eassumption. eassumption. sets.
      + eapply Union_Included.
        * eapply Included_trans. eapply Make_wrappers_bound_var. eassumption.
          repeat find_subsets.
          eapply Included_Union_preserv_l. eapply Included_Union_preserv_r. eapply Included_Setminus_compat; sets.
          eapply Included_trans. eassumption. eassumption.
        * eapply Included_trans. eapply IHe; eauto.
          repeat find_subsets.
          eapply Union_Included; sets.
          eapply Included_Union_preserv_l. eapply Included_Union_preserv_r. eapply Included_Setminus_compat; sets.
          eapply Included_trans. eassumption. sets.
      + eapply Included_trans. eapply IHB1; eauto.
        repeat find_subsets.
        eapply Union_Included; sets. eapply Union_Included; sets.
        eapply Included_Union_preserv_l. eapply Included_Union_preserv_r. eapply Included_Setminus_compat; sets.
        eapply Included_trans. eassumption.
        eapply Included_trans. eassumption. sets. }
    { intros H. inv H. repeat normalize_bound_var.
      eapply Union_Included; [| eapply Union_Included; [| eapply Union_Included ]]; sets.
      + eapply Included_trans. eapply IHe; eauto. eapply Union_Included; sets.
        repeat find_subsets. sets.
      + eapply Included_trans. eapply IHB; eauto. eapply Union_Included; sets.
        repeat find_subsets. sets.  }
  - constructor; intros H; inv H; normalize_bound_var; sets.
Qed.

Lemma Exp_lambda_lift_bound_var :
  (forall e zeta sig S e' S',
      Exp_lambda_lift zeta sig e S e' S' ->
      bound_var e' \subset bound_var e :|: (S \\ S')).
Proof. eapply Exp_lambda_lift_bound_var_mut. Qed.

Lemma Fundefs_lambda_lift2_bound_var :
  forall B B0 zeta sig S B' S',
    Fundefs_lambda_lift2 zeta sig B0 B S B' S' ->
    bound_var_fundefs B' \subset bound_var_fundefs B :|: (S \\ S') :|: image' (lifted_name zeta) (name_in_fundefs B).
Proof.
  intros. edestruct Exp_lambda_lift_bound_var_mut.
  edestruct H1. eauto.
Qed.

Lemma Fundefs_lambda_lift3_bound_var :
  forall B B0 zeta sig S B' S',
    Fundefs_lambda_lift3 zeta sig B0 B S B' S' ->
    bound_var_fundefs B' \subset bound_var_fundefs B :|: (S \\ S').
Proof.
  intros. edestruct Exp_lambda_lift_bound_var_mut.
  edestruct H1. eauto.
Qed.


Lemma unique_bindings_Ecase x y B :
  unique_bindings (Ecase x B) ->
  unique_bindings (Ecase y B).
Proof.
  intros Hun. induction B; inv Hun.
  constructor; eauto.
  constructor; eauto.
  rewrite bound_var_Ecase_var. eassumption.
Qed.

Lemma Make_wrappers_unique_bindings_fundefs z f1 B S1 fds S2 f2 :
  Make_wrappers z f1 B S1 fds S2 f2 ->
  unique_bindings_fundefs fds.
Proof.
  intros Hm; induction Hm.
  - now constructor.
  - constructor.
    + intros Hc. inv Hc.
    + intros Hc. eapply Make_wrappers_bound_var in Hc; [| eassumption ].
      inv Hc. inv H4. eauto.
    + normalize_bound_var. now sets.
    + eapply Disjoint_Included_l. eapply Make_wrappers_bound_var. eassumption.
      sets.
    + normalize_bound_var. now sets.
    + inv H3. eassumption.
    + eassumption.
    + constructor.
    + eassumption.
Qed.


Lemma Exp_lambda_lift_unique_bindings_mut :
  (forall e zeta sig S e' S',
      Exp_lambda_lift zeta sig e S e' S' ->
      Disjoint _ (bound_var e) S ->
      Disjoint _ (bound_var e) (LiftedFuns zeta) ->
      unique_bindings e ->
      unique_bindings e') /\
  (forall B B0 zeta sig S B' S',
      Fundefs_lambda_lift2 zeta sig B0 B S B' S' /\
      Disjoint _ S (image' (lifted_name zeta) (name_in_fundefs B)) /\
      injective_subdomain (name_in_fundefs B) (lifted_name zeta) \/
      Fundefs_lambda_lift3 zeta sig B0 B S B' S' ->
      Disjoint _ (bound_var_fundefs B) S ->
      Disjoint _ (bound_var_fundefs B) (LiftedFuns zeta) ->
      unique_bindings_fundefs B ->
      unique_bindings_fundefs B').
Proof with now eauto with Ensembles_DB.
  exp_defs_induction IHe IHl IHB; intros; try inv H; try inv H2; try now constructor.
  - constructor; eauto.
    + intros Hc. eapply Exp_lambda_lift_bound_var in H12.
      eapply H12 in Hc. inv Hc; eauto.
      inv H. eapply H0; constructor; eauto.
    + repeat normalize_bound_var_in_ctx. eapply IHe; sets.
  - constructor; eauto.
    + repeat normalize_bound_var_in_ctx.
      eapply unique_bindings_Ecase. eapply IHl; sets.
      repeat find_subsets.
      eapply Disjoint_Included; [| | eapply H0 ]; sets.
    + repeat normalize_bound_var_in_ctx.
      eapply IHe; sets.
    + eapply Disjoint_Included.
      rewrite bound_var_Ecase_var. eapply Exp_lambda_lift_bound_var. eassumption.
      eapply Exp_lambda_lift_bound_var. eassumption.
      repeat normalize_bound_var_in_ctx.
      eapply Union_Disjoint_l; eapply Union_Disjoint_r; sets.
      eapply Exp_Lambda_lift_free_set_Included in H12.
      eapply Disjoint_Included; [| | eapply H0 ]; sets.
  - constructor; eauto.
    + intros Hc. eapply Exp_lambda_lift_bound_var in H13.
      eapply H13 in Hc. inv Hc; eauto.
      inv H. eapply H0; constructor; eauto.
    + repeat normalize_bound_var_in_ctx. eapply IHe; sets.
  - constructor; eauto.
    + intros Hc. eapply Exp_lambda_lift_bound_var in H14.
      eapply H14 in Hc. inv Hc; eauto.
      inv H. eapply H0; constructor; eauto.
    + repeat normalize_bound_var_in_ctx. eapply IHe; sets.
  - constructor; eauto.
    + intros Hc. eapply Exp_lambda_lift_bound_var in H13.
      eapply H13 in Hc. inv Hc; eauto.
      inv H.
      repeat normalize_bound_var_in_ctx. eapply H0; constructor; eauto.
    + repeat normalize_bound_var_in_ctx. eapply IHe; eauto; sets.
  - repeat normalize_bound_var_in_ctx.
    constructor. constructor.
    + eapply IHe; sets.
      repeat find_subsets.
      eapply Disjoint_Included; [| | eapply H0]; sets.
      eapply Included_trans. eassumption.
      eapply Included_trans. eassumption. eassumption.
      eapply Disjoint_Included_r. eapply Add_functions_LiftedFuns_Included_r.
      eassumption. sets.
    + eapply Make_wrappers_unique_bindings_fundefs. eassumption.
    + eapply Disjoint_Included.
      eapply Make_wrappers_bound_var. eassumption.
      eapply Exp_lambda_lift_bound_var. eassumption.
      repeat find_subsets.
      eapply Union_Disjoint_l; sets.
      eapply Disjoint_Included; [| | eapply H0]; sets.
      eapply Included_trans; [| eassumption ].
      eapply Included_trans; [| eassumption ]. sets.
    + eapply IHB. left. split. eassumption.  split.
      eapply Disjoint_Included_r. eapply Add_functions_name_in_fundefs_Included. eassumption.
      now sets.
      eapply Add_functions_injective_subdomain_LiftedFuns. eassumption.
      eapply Disjoint_Included; [| | eapply H0]; sets.
      repeat find_subsets. sets.

      eapply Disjoint_Included_r. eapply Add_functions_LiftedFuns_Included_r.
      eassumption. sets.
      eassumption.
    + repeat normalize_bound_var.
      eapply Disjoint_Included.
      eapply Fundefs_lambda_lift2_bound_var. eassumption.
      eapply Included_Union_compat. eapply Make_wrappers_bound_var. eassumption.
      eapply Exp_lambda_lift_bound_var. eassumption.
      rewrite Add_functions_name_in_fundefs; eauto.
      repeat find_subsets.
      eapply Union_Disjoint_l; eapply Union_Disjoint_r; sets.
      * eapply Union_Disjoint_r; sets.
        eapply Disjoint_sym. eapply Disjoint_Included; [| | eapply H0]; sets.
        eapply Included_trans; [| eassumption ].
        eapply Included_trans; [| eassumption ]. sets.
      * eapply Union_Disjoint_l; eapply Union_Disjoint_r; sets.
        eapply Disjoint_Included; [| | eapply H0]; sets.
        eapply Disjoint_sym. eapply Disjoint_Included; [| | eapply H0]; sets.
        eapply Included_trans; [| eassumption ].
        eapply Included_trans; [| eassumption ]. sets.
      * eapply Union_Disjoint_l; sets.
        eapply Disjoint_Included_l.
        eapply Included_trans. eapply Setminus_Included. eassumption. sets.
  - repeat normalize_bound_var_in_ctx.
    constructor.
    + eapply IHe; sets.
      repeat find_subsets.
      eapply Disjoint_Included; [| | eapply H0]; sets.
    + eapply IHB; sets.
    + repeat normalize_bound_var.
      eapply Disjoint_Included.
      eapply Fundefs_lambda_lift3_bound_var. eassumption.
      eapply Exp_lambda_lift_bound_var. eassumption.
      repeat find_subsets.
      eapply Union_Disjoint_l; eapply Union_Disjoint_r; sets.
      eapply Disjoint_sym. eapply Disjoint_Included; [| | eapply H0]; sets.
  - constructor; eauto.
    + intros Hc. eapply Exp_lambda_lift_bound_var in H11.
      eapply H11 in Hc. inv Hc; eauto.
      inv H. eapply H0; constructor; eauto.
    + repeat normalize_bound_var_in_ctx. eapply IHe; sets.
  - constructor; eauto.
    + intros Hc. eapply Exp_lambda_lift_bound_var in H12.
      eapply H12 in Hc. inv Hc; eauto.
      inv H. eapply H0; constructor; eauto.
    + repeat normalize_bound_var_in_ctx. eapply IHe; sets.
  - inv H3. inv H. repeat normalize_bound_var_in_ctx. constructor; eauto.
    + intros Hc. inv Hc.
      * eapply Make_wrappers_bound_var in H5; [| eassumption ].
        inv H5. inv H. eapply H2. constructor. eassumption. simpl.
        rewrite image'_Union, image'_Singleton_is_Some; eauto.
        eapply lifted_name_eq. eassumption.
      * eapply Exp_lambda_lift_bound_var in H5; [| eassumption ].
        inv H5; eauto.
        -- eapply H1. constructor. right. right. now left; eauto.
           eexists. split. unfold Funs. eexists.
           eapply lifted_name_eq. eassumption.
           eapply lifted_name_eq. eassumption.
        -- inv H. eapply H2. constructor.
           2:{ simpl. rewrite image'_Union, image'_Singleton_is_Some; eauto.
               eapply lifted_name_eq. eassumption. }
           repeat find_subsets; sets. eapply H27. eassumption.
    + intros Hc. eapply Fundefs_lambda_lift2_bound_var in Hc; [| eassumption ].
      inv H2. inv Hc. inv H2.
      * eapply H1. constructor. do 3 right. eassumption.
        eexists. split. unfold Funs. eexists.
        eapply lifted_name_eq. eassumption.
        eapply lifted_name_eq. eassumption.
      * inv H4. eapply H. constructor.
        2:{ simpl. rewrite image'_Union, image'_Singleton_is_Some; eauto.
            eapply lifted_name_eq. eassumption. }
        repeat find_subsets; sets. eapply H28 in H2. eapply H27 in H2.
        inv H2. eassumption.
      * simpl in *.
        eapply lifted_name_eq in H17. inv H2. inv H4.
        rewrite <- H17 in H5. eapply H3 in H5; eauto. subst.
        eapply H9. eapply name_in_fundefs_bound_var_fundefs. eassumption.
    + normalize_bound_var. eapply Union_Disjoint_l.
      * eapply Disjoint_Included_l. eapply Make_wrappers_bound_var. eassumption.
        normalize_sets. eapply Union_Disjoint_r; sets.
      * eapply Disjoint_Included_l. eapply Exp_lambda_lift_bound_var. eassumption.
        normalize_sets. eapply Union_Disjoint_r; eapply Union_Disjoint_l; sets.
        repeat find_subsets.
        eapply Disjoint_sym. eapply Disjoint_Included; [| | eapply H0 ]; sets.
        eapply Included_trans. eapply Setminus_Included. eapply Included_trans. eassumption.
        sets.
        now eapply Disjoint_Included; [| | eapply H0 ]; sets.
        repeat find_subsets; sets.
        eapply Disjoint_Included_l. eapply Setminus_Included.
        eapply Disjoint_Included_l. eassumption. sets.
    + eapply Disjoint_Included_l. eapply Fundefs_lambda_lift2_bound_var. eassumption.
      normalize_sets. eapply Union_Disjoint_r; eapply Union_Disjoint_l; sets.
      * eapply Union_Disjoint_l; sets.
        repeat find_subsets; sets.
        eapply Disjoint_Included_l. eapply Setminus_Included.
        eapply Disjoint_Included_l. eassumption.
        eapply Disjoint_Included_l. eassumption. sets.
      * eapply Disjoint_sym. eapply Disjoint_Included; [| | eapply H1 ].
        clear. now firstorder.
        now sets.
      * eapply Union_Disjoint_l; sets.
        eapply Disjoint_Included; [| | eapply H0 ]; sets.
        repeat find_subsets; sets.
        eapply Disjoint_Included_l. eapply Setminus_Included.
        eapply Disjoint_Included_l. eassumption.
        eapply Disjoint_Included_l. eassumption. sets.
      * eapply Disjoint_Included_r. eassumption.
        inv H2. sets.
    + normalize_bound_var. eapply Disjoint_Included.
      eapply Fundefs_lambda_lift2_bound_var. eassumption.
      eapply Included_Union_compat. eapply Make_wrappers_bound_var. eassumption.
      eapply Exp_lambda_lift_bound_var. eassumption.
      eapply Union_Disjoint_r; eapply Union_Disjoint_l; sets.
      * eapply Union_Disjoint_r; sets.
        eapply Disjoint_sym. eapply Disjoint_Included; [| | eapply H0 ]; sets.
        repeat find_subsets; sets.
      * eapply Union_Disjoint_r; eapply Union_Disjoint_l; sets.
        repeat find_subsets; sets.
        eapply Disjoint_sym. eapply Disjoint_Included; [| | eapply H0 ]; sets.
        eapply Included_trans. eapply Setminus_Included.
        eapply Included_trans. eassumption. now sets.
        repeat find_subsets; sets.
        eapply Disjoint_Included; [| | eapply H0 ]; sets.
        eapply Included_trans. eapply Setminus_Included.
        eapply Included_trans. eassumption.
        eapply Included_trans. eassumption. now sets.
      * inv H2. simpl in *. xsets.
      * eapply Union_Disjoint_l.
        eapply Disjoint_Included; [| | eapply H1 ].
        clear. now firstorder. now sets.
        repeat find_subsets. inv H2. eapply Disjoint_Included; [| | eapply H ]. now sets.
        eapply Included_trans. eapply Setminus_Included.
        eapply Included_trans. eassumption. sets.
    + intros Hc. eapply FromList_app in Hc. inv Hc.
      * eapply H1. constructor. right. now left; eauto.
        eexists. split. 2:{ eapply lifted_name_eq. eassumption. }
        eexists. eapply lifted_name_eq. eassumption.
      * inv H2. eapply H3. constructor. eapply H18. eassumption.
        simpl. rewrite image'_Union, image'_Singleton_is_Some.
        2:{ eapply lifted_name_eq. eassumption. }
        now left.
    + eapply List_util.NoDup_app; eauto.
      eapply Disjoint_Included_r. eassumption. sets.
    + constructor.
      eapply IHe; eauto. repeat find_subsets; sets.
      eapply Disjoint_Included; [| | eapply H0 ]; sets.
      eapply Included_trans. eassumption. now sets.
      now sets. eapply Make_wrappers_unique_bindings_fundefs. eassumption.
      eapply Disjoint_Included_l. eapply Exp_lambda_lift_bound_var. eassumption.
      eapply Disjoint_Included_r. eapply Make_wrappers_bound_var. eassumption.
      eapply Union_Disjoint_l; sets.
      repeat find_subsets; sets.
      eapply Disjoint_Included; [| | eapply H0 ]; sets.
    + inv H2. eapply IHB; auto. left. split; [| split ]. eassumption.
      repeat find_subsets. eapply Disjoint_Included; [| | eapply H ]. now sets.
      eapply Included_trans. eassumption. eapply Included_trans. eassumption. sets.
      eapply injective_subdomain_antimon. eassumption. now sets.
      repeat find_subsets; sets.
      eapply Disjoint_Included; [| | eapply H0 ]; sets.
      eapply Included_trans. eassumption.
      eapply Included_trans. eassumption. now sets.
      now sets.
  - inv H3. repeat normalize_bound_var_in_ctx. constructor; eauto.
    + intros Hc. eapply Exp_lambda_lift_bound_var in Hc; [| eassumption ].
      inv Hc; eauto. inv H. eapply H0. constructor. now left. eassumption.
    + intros Hc.  eapply Fundefs_lambda_lift3_bound_var in Hc; [| eassumption ].
      inv Hc; eauto. eapply H0. constructor; eauto. inv H.
      repeat find_subsets. sets.
    + eapply Disjoint_Included_l.
      eapply Exp_lambda_lift_bound_var. eassumption.
      eapply Union_Disjoint_l. sets. sets.
    + eapply Disjoint_Included_l.
      eapply Fundefs_lambda_lift3_bound_var. eassumption.
      eapply Union_Disjoint_l. sets.
      repeat find_subsets. eapply Disjoint_sym. eapply Disjoint_Included; [| | eapply H0 ]; sets.
    + eapply Disjoint_Included.
      eapply Fundefs_lambda_lift3_bound_var. eassumption.
      eapply Exp_lambda_lift_bound_var. eassumption.
      eapply Union_Disjoint_l; eapply Union_Disjoint_r; sets.
      repeat find_subsets. eapply Disjoint_Included; [| | eapply H0 ]; sets.
    + eapply IHe; eauto. sets. sets.
    + eapply IHB; eauto. repeat find_subsets.
      eapply Disjoint_Included; [| | eapply H0 ]; sets.
      sets.
  - inv H3. inv H2. inv H. constructor.
  - inv H3. constructor.
Qed.


Lemma Exp_lambda_lift_unique_bindings :
  forall e zeta sig S e' S',
    Exp_lambda_lift zeta sig e S e' S' ->
    Disjoint _ (bound_var e) S ->
    Disjoint _ (bound_var e) (LiftedFuns zeta) ->
    unique_bindings e ->
    unique_bindings e'.
Proof. eapply Exp_lambda_lift_unique_bindings_mut. Qed.

Lemma Fundefs_lambda_lift2_unique_bindings :
  forall B B0 zeta sig S B' S',
    Fundefs_lambda_lift2 zeta sig B0 B S B' S' ->
    Disjoint _ S (image' (lifted_name zeta) (name_in_fundefs B)) ->
    injective_subdomain (name_in_fundefs B) (lifted_name zeta)  ->
    Disjoint _ (bound_var_fundefs B) S ->
    Disjoint _ (bound_var_fundefs B) (LiftedFuns zeta) ->
    unique_bindings_fundefs B ->
    unique_bindings_fundefs B'.
Proof. intros. eapply Exp_lambda_lift_unique_bindings_mut; eauto. Qed.

Lemma Fundefs_lambda_lift3_unique_bindings :
  (forall B B0 zeta sig S B' S',
      Fundefs_lambda_lift3 zeta sig B0 B S B' S' ->
      Disjoint _ (bound_var_fundefs B) S ->
      Disjoint _ (bound_var_fundefs B) (LiftedFuns zeta) ->
      unique_bindings_fundefs B ->
      unique_bindings_fundefs B').
Proof. intros. eapply Exp_lambda_lift_unique_bindings_mut; eauto. Qed.
