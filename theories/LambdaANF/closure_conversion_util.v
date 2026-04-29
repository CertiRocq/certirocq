(* Syntactic properties of closure conversion. Part of the CertiRocq project.
 * Author: Anonymized, 2016
 *)

From CertiRocq Require Import LambdaANF.term LambdaANF.size_cps LambdaANF.term_util LambdaANF.set_util LambdaANF.identifiers LambdaANF.ctx
     LambdaANF.Ensembles_util LambdaANF.List_util LambdaANF.functions LambdaANF.closure_conversion LambdaANF.closure_conversion
     LambdaANF.eval LambdaANF.tactics.
Require Import compcert.lib.Coqlib.
From Stdlib Require Import ZArith.Znumtheory ArithRing Relations.Relations Arith.Wf_nat.
From Stdlib Require Import Lists.List MSets.MSets MSets.MSetRBT Numbers.BinNums
        NArith.BinNat PArith.BinPos Sets.Ensembles micromega.Lia.

Import ListNotations.

Open Scope ctx_scope.
Open Scope fun_scope.
Close Scope Z_scope.


(** * Syntactic Properties of the closure conversion relation *)

Section Closure_conversion_util.

  Variable clo_tag : ctor_tag.

  Lemma project_vars_length Scope Funs GFuns c genv Γ FVs S x y C Q :
    project_vars clo_tag Scope Funs GFuns c genv Γ FVs S x y C Q ->
    @List.length var x = @List.length var y.
  Proof.
    intros Hp; induction Hp; eauto. simpl; congruence.
  Qed.

  Lemma project_var_occurs_free_ctx_Included Scope Funs GFuns c genv Γ FVs S x y C Q F e:
    project_var clo_tag Scope Funs GFuns c genv Γ FVs S x y C Q ->
    (occurs_free e) \subset (F :|: [set y]) ->
    (Scope :|: (Funs \\ Scope) :|: (GFuns \\ Scope) :|: image genv (Funs \\ Scope) :|: [set Γ]) \subset F ->
    (occurs_free (C |[ e ]|)) \subset F.
  Proof with now eauto with Ensembles_DB functions_BD.
    intros Hproj Hinc1 Hinc2. inv Hproj.
    - simpl. eapply Included_trans. eassumption.
      apply Union_Included. now apply Included_refl.
      eapply Included_trans; [| eapply Hinc2 ]. eapply Singleton_Included. eauto.
    - simpl.
      rewrite occurs_free_Econstr, !FromList_cons, FromList_nil,
      Union_Empty_set_neut_r.
      eapply Union_Included.
      + eapply Included_trans; [| now apply Hinc2 ].
        eapply Union_Included.
        do 3 eapply Included_Union_preserv_l. eapply Included_Union_preserv_r.
        eapply Singleton_Included. constructor; eauto.

        eapply Included_Union_preserv_l. eapply Included_Union_preserv_r.
        eapply Singleton_Included. eapply In_image. constructor; eauto.
      + eauto with Ensembles_DB.
    - simpl.
      repeat normalize_occurs_free.
      rewrite FromList_cons, FromList_nil, Union_Empty_set_neut_l.
      rewrite FromList_singleton. rewrite !Setminus_Union_distr.
      rewrite Setminus_Same_set_Empty_set, Union_Empty_set_neut_r.
      eapply Union_Included.
      + eapply Included_trans; [| now apply Hinc2 ].
        xsets.
      + eauto with Ensembles_DB.
    - simpl. rewrite occurs_free_Eproj.
      eapply Union_Included.
      + eapply Included_trans; [| now apply Hinc2 ]...
      + eauto with Ensembles_DB.
  Qed.


  Lemma project_vars_occurs_free_ctx_Included Scope Funs GFuns c Γ genv
    FVs S xs xs' C S' F e:
    project_vars clo_tag Scope Funs GFuns c genv Γ FVs S xs xs' C S' ->
    (occurs_free e) \subset (F :|: (FromList xs')) ->
    (Scope :|:  (Funs \\ Scope) :|: (GFuns \\ Scope) :|: image genv (Funs \\ Scope) :|: [set  Γ]) \subset F ->
    occurs_free (C |[ e ]|) \subset F.
  Proof.
    intros Hproj. revert F.
    induction Hproj; intros F Hinc1 Hinc2; repeat normalize_sets.
    - eassumption.
    - rewrite <- app_ctx_f_fuse.
      eapply project_var_occurs_free_ctx_Included; [ eassumption | | eassumption ].
      eapply IHHproj. rewrite <- Union_assoc. eassumption.
      eapply Included_trans. eassumption. now apply Included_Union_l.
  Qed.


   (* Lemma occurs_free_ctx_Included Scope Funs GFuns Γ genv C F e:
    (occurs_free e) \subset F ->
    (Scope :|:  (Funs \\ Scope) :|: (GFuns \\ Scope) :|: image genv (Funs \\ Scope) :|: [set  Γ]) \subset F ->
    occurs_free (C |[ e ]|) \subset F.
  Proof.
    revert F.
    intros F Hinc1 Hinc2; repeat normalize_sets.
    unfold
    - eassumption.
    - rewrite <- app_ctx_f_fuse.
      eapply project_var_occurs_free_ctx_Included; [ eassumption | | eassumption ].
      eapply IHHproj. rewrite <- Union_assoc. eassumption.
      eapply Included_trans. eassumption. now apply Included_Union_l.
  Qed. *)

  Lemma project_var_occurs_free_ctx_alt_Included Scope Funs GFuns c genv Γ FVs S x y C Q F e:
    project_var clo_tag Scope Funs GFuns c genv Γ FVs S x y C Q ->
    (occurs_free e) \subset (F :|: [set y]) ->
    (Scope :|: ([set x] :&: (Funs \\ Scope :|: (GFuns \\ Scope))) :|: image genv (Funs \\ Scope) :|: [set Γ]) \subset F ->
    (occurs_free (C |[ e ]|)) \subset F.
  Proof with now eauto with Ensembles_DB functions_BD.
    intros Hproj Hinc1 Hinc2. inv Hproj.
    - simpl. eapply Included_trans. eassumption.
      apply Union_Included. now apply Included_refl.
      eapply Included_trans; [| eassumption ].
      eauto with Ensembles_DB.
    - simpl.
      rewrite occurs_free_Econstr, !FromList_cons, FromList_nil,
      Union_Empty_set_neut_r.
      eapply Union_Included.
      + eapply Included_trans; [| now apply Hinc2 ].
        eapply Union_Included; sets. eapply Singleton_Included. do 2 left. right.
        constructor; eauto. left; constructor; eauto.
        eapply Singleton_Included. left. right.
        eapply In_image. constructor; eauto.
      + eauto with Ensembles_DB.
    - simpl.
      repeat normalize_occurs_free.
      rewrite FromList_cons, FromList_nil, Union_Empty_set_neut_l.
      rewrite FromList_singleton. rewrite !Setminus_Union_distr.
      rewrite Setminus_Same_set_Empty_set, Union_Empty_set_neut_r.
      eapply Union_Included.
      + eapply Included_trans; [| now apply Hinc2 ].
        eapply Setminus_Included_Included_Union.
        eapply Singleton_Included. left. left. left. right.
        econstructor; eauto. right; constructor; eauto.
      + eauto with Ensembles_DB.
    - simpl. rewrite occurs_free_Eproj.
      eapply Union_Included.
      + eapply Included_trans; [| now apply Hinc2 ]...
      + eauto with Ensembles_DB.
  Qed.


  Lemma project_vars_occurs_free_ctx_alt_Included Scope Funs GFuns c genv Γ
        FVs S xs xs' C S' F e:
    project_vars clo_tag Scope Funs GFuns c genv Γ FVs S xs xs' C S' ->
    Included _ (occurs_free e) (Union _ F (FromList xs')) ->
    Included _ (Scope :|: (FromList xs :&: (Funs \\ Scope :|: (GFuns \\ Scope))) :|: image genv (Funs \\ Scope) :|: (Singleton _ Γ)) F ->
    Included _ (occurs_free (C |[ e ]|)) F.
  Proof.
    intros Hproj. revert F.
    induction Hproj; intros F Hinc1 Hinc2; repeat normalize_sets.
    - eassumption.
    - rewrite <- app_ctx_f_fuse.
      eapply project_var_occurs_free_ctx_alt_Included; [ eassumption | | ].
      eapply IHHproj. rewrite <- Union_assoc. eassumption.
      eapply Included_trans. eapply Included_trans; [| eapply Hinc2 ]; sets.
      eapply Included_Union_compat; sets.
      eapply Included_Union_compat; sets.
      eapply Included_Union_compat; sets.
      eapply Included_Intersection_compat; sets. sets.
      eapply Included_trans; [| eassumption ].
      eapply Included_Union_compat; sets.
      eapply Included_Union_compat; sets.
      eapply Included_Union_compat; sets.
      eapply Included_Intersection_compat; sets.
  Qed.


  Lemma project_var_In_Union Scope Funs GFuns c genv Γ FVs S x x' C S' :
    project_var clo_tag Scope Funs GFuns c genv Γ FVs S x x' C S' ->
    x \in (Scope :|: Funs :|: GFuns :|: FromList FVs).
  Proof.
    intros Hvar. inv Hvar; eauto.
    right. eapply nthN_In. eassumption.
  Qed.

  Lemma project_vars_In_Union Scope Funs GFuns c genv Γ FVs S xs xs' C S' :
    project_vars clo_tag Scope Funs GFuns c genv Γ FVs S xs xs' C S' ->
    (FromList xs) \subset (Scope :|: Funs :|: GFuns :|: FromList FVs).
  Proof.
    intros Hvar. induction Hvar; eauto.
    - rewrite FromList_nil. now apply Included_Empty_set.
    - rewrite FromList_cons.
      eapply Union_Included; [| eassumption ].
      eapply Singleton_Included. eapply project_var_In_Union.
      eassumption.
  Qed.


    (** * Lemmas about [add_global_funs] *)

  Lemma add_global_funs_included G F {_ : Decidable F} V G' :
    add_global_funs G F V G' ->
    G \subset G' :|: F.
  Proof.
    intros Hin. inv Hin; sets.
  Qed.

  Lemma add_global_funs_included_r G F V G' :
    add_global_funs G F V G' ->
    G' \subset G :|: F.
  Proof.
    intros Hin. inv Hin; sets.
  Qed.

  Definition is_gfuns (GFuns : Ensemble var) names (FVs : list var) GFuns' :=
    (FVs = [] /\ GFuns' \subset GFuns :|: names) \/
    (FVs <> [] /\ GFuns' \subset GFuns \\ names).

  Lemma add_global_funs_is_gfuns (GFuns : Ensemble var) names (FVs : list var) GFuns':
    add_global_funs GFuns names (FromList FVs) GFuns' ->
    is_gfuns GFuns names FVs GFuns'.
  Proof.
    intros Hin; destruct FVs; inv Hin; unfold is_gfuns; sets.
    - exfalso. eapply not_In_Empty_set. eapply H.
      now left.
    - right. split; sets. congruence.
  Qed.

  Lemma is_gfuns_setminus (GFuns : Ensemble var) names (FVs : list var) GFuns' x:
   is_gfuns GFuns (x |: names) FVs GFuns' ->
   is_gfuns GFuns names FVs (GFuns' \\ [set x]).
  Proof.
    intros [[H1 H2] | [H1 H2]]; subst; unfold is_gfuns in *.
    left; split; eauto.
    eapply Setminus_Included_Included_Union. eapply Included_trans. eassumption. sets.
    right; split; eauto.
    eapply Setminus_Included_Included_Union. eapply Included_trans. eassumption. sets.
  Qed.

  Lemma is_gfuns_included_r G F {_ : Decidable F} V G' :
    is_gfuns G F V G' ->
    G' \subset G :|: F.
  Proof.
    intros Hin. destruct Hin as [[? ?] | [? ?]]; subst; sets.
    eapply Included_trans. eassumption. sets.
  Qed.

  Lemma add_global_funs_is_gfuns_included (GFuns : Ensemble var) names (FVs : list var) GFuns' GFuns'' :
    add_global_funs GFuns names (FromList FVs) GFuns' ->
    is_gfuns GFuns names FVs GFuns'' ->
    GFuns'' \subset GFuns'.
  Proof.
    intros Hadd Hin; destruct Hin as [[? ?] | [? ?]]; inv Hadd; unfold is_gfuns; sets.
    - eapply Included_trans. eassumption. sets.
    - rewrite FromList_nil in H1. exfalso; eapply H1; reflexivity.
    - eapply Included_trans. eassumption. sets.
  Qed.

  (** * Lemmas about [extend_fundefs'] *)

  Lemma extend_fundefs'_get_s f B x z :
    z \in name_in_fundefs B ->
    extend_fundefs' f B x z = x.
  Proof.
    intros Heq. unfold extend_fundefs'.
    destruct (Dec z); eauto.
    exfalso; eauto.
  Qed.

  Lemma extend_fundefs'_get_o f B x z :
    ~ z \in name_in_fundefs B ->
    extend_fundefs' f B x z = f z.
  Proof.
    intros Heq. unfold extend_fundefs'.
    destruct (Dec z); eauto.
    exfalso; eauto.
  Qed.

  Lemma extend_fundefs'_image f B x :
    image (extend_fundefs' f B x) (name_in_fundefs B) \subset [set x].
  Proof.
    intros y Hin.
    destruct Hin as [z [Hin' Heq]].
    rewrite extend_fundefs'_get_s in Heq. subst; eauto.
    eassumption.
  Qed.

  Lemma extend_fundefs'_image_Included f B x S :
    image (extend_fundefs' f B x) S \subset x |: image f S.
  Proof.
    intros y Hin.
    destruct Hin as [z [Hin' Heq]].
    unfold extend_fundefs' in *.
    destruct (Dec z); subst; eauto.
    right. eexists; split; eauto.
  Qed.

  Lemma extend_fundefs'_image_Included' f B x S :
    image (extend_fundefs' f B x) S \subset x |: image f (S \\ name_in_fundefs B).
  Proof.
    intros y Hin.
    destruct Hin as [z [Hin' Heq]].
    unfold extend_fundefs' in *.
    destruct (Dec z); subst; eauto.
    right. eexists; split; eauto. constructor; eauto.
  Qed.

  Lemma extend_fundefs'_same_funs f B B' x :
    name_in_fundefs B <--> name_in_fundefs B' ->
    f_eq (extend_fundefs' f B x) (extend_fundefs' f B' x).
  Proof.
    intros Heq y. unfold extend_fundefs'. destruct Heq.
    destruct (@Dec _ (name_in_fundefs B) _ y);
      destruct (@Dec _ (name_in_fundefs B') _ y); eauto.
    eapply H in n. now exfalso; eauto.
    eapply H0 in n0. now exfalso; eauto.
  Qed.


  Lemma project_var_free_funs_in_exp Scope Funs GFuns c genv Γ FVs S x x' C S' B e:
    project_var clo_tag Scope Funs GFuns c genv Γ FVs S x x' C S' ->
    (funs_in_exp B (C |[ e ]|) <-> funs_in_exp B e).
  Proof.
    intros Hvar; inv Hvar; [ split; now eauto | |  |];
      try (split; intros Hf; [ now inv Hf | now constructor ]).
    - split; intros Hf.
      inv Hf. inv H6. eassumption.
      constructor. now constructor.
  Qed.

  Lemma project_vars_free_funs_in_exp Scope Funs GFuns c genv Γ FVs S xs xs' C S' B e:
    project_vars clo_tag Scope Funs GFuns c genv Γ FVs S xs xs' C S' ->
    (funs_in_exp B (C |[ e ]|) <-> funs_in_exp B e).
  Proof.
    intros Hvar; induction Hvar; [ now eauto |].
    rewrite <- app_ctx_f_fuse, project_var_free_funs_in_exp; eassumption.
  Qed.

  Lemma closure_conversion_fundefs_Same_set_image c Funs GFuns FVs B1 B2  :
    Closure_conversion_fundefs clo_tag Funs GFuns c FVs B1 B2 ->
    Same_set _ (name_in_fundefs B1) (name_in_fundefs B2).
  Proof.
    intros Hcc. induction Hcc.
    - simpl. rewrite IHHcc. sets.
    - simpl. sets.
  Qed.


  Lemma Setminus_eq_Included A (s1 s2 s3 : Ensemble A) {_ : Decidable s2} :
    s1 \\ s2 <--> s3 ->
    s1 \subset s2 :|: s3.
  Proof.
    intros H x Hin. rewrite <- H.
    destruct X. destruct (Dec x); eauto.
    right; constructor; eauto.
  Qed.

  Lemma add_global_funs_Dec G N F G' :
    add_global_funs G N F G' ->
    Decidable G ->
    Decidable N ->
    Decidable G'.
  Proof.
    intros Ha H1 H2. inv Ha; tci.
  Qed.

  Lemma Closure_conversion_occurs_free_pre_Included :
    (forall e Scope Funs GFuns {_ : Decidable GFuns} c genv Γ FVs e' C
       (Hcc : Closure_conversion clo_tag Scope Funs GFuns c genv Γ FVs e e' C),
        (occurs_free e) \subset (Scope :|: Funs :|: GFuns :|: FromList FVs)).
  Proof with now eauto with Ensembles_DB functions_BD.
    induction e using exp_ind'; intros; inv Hcc; normalize_occurs_free.
    - eapply Union_Included. eapply project_vars_In_Union. eassumption.
      eapply IHe in H15. eapply Setminus_Included_Included_Union.
      eapply Included_trans. eassumption. repeat (eapply Union_Included; sets).
      tci.
    - eapply Singleton_Included. eapply project_var_In_Union. eassumption.
    - eapply Union_Included.
      eapply Singleton_Included. eapply project_var_In_Union. eassumption.
      inv H13. destruct H3 as [Hfeq [C1 [e1 [Hceq Hcc]]]].
      eapply Union_Included.
      eapply IHe; eassumption.
      eapply IHe0; eauto. econstructor; eauto.
    - eapply Union_Included. eapply Singleton_Included. eapply project_var_In_Union. eassumption.
      eapply IHe in H16. eapply Setminus_Included_Included_Union.
      eapply Included_trans. eassumption. repeat (eapply Union_Included; sets). tci.
    - eapply Union_Included. rewrite <- FromList_cons. eapply project_vars_In_Union. eassumption.
      eapply IHe in H19. eapply Setminus_Included_Included_Union.
      eapply Included_trans. eassumption. repeat (eapply Union_Included; sets). tci.
    - eapply Union_Included.
      eapply Included_trans. eapply Setminus_eq_Included; [| eassumption ]. tci.
      eapply Union_Included. sets.
      eapply project_vars_In_Union. eassumption.
      eapply IHe in H19; tci. eapply Setminus_Included_Included_Union.
      eapply Included_trans. eassumption.
      eapply Union_Included; sets.
      eapply Union_Included; sets.
      now eapply Union_Included; sets.
      eapply Included_trans. eapply add_global_funs_included_r. eassumption. sets.
      eapply add_global_funs_Dec. eassumption. tci. tci.
    - eapply Included_trans; [| eapply project_vars_In_Union; eauto ].
      normalize_sets...
    - eapply IHe in H13. eapply Setminus_Included_Included_Union.
      eapply Included_trans. eassumption. repeat (eapply Union_Included; sets).
      tci.
    - eapply Union_Included. eapply project_vars_In_Union. eassumption.
      eapply IHe in H15. eapply Setminus_Included_Included_Union.
      eapply Included_trans. eassumption. repeat (eapply Union_Included; sets).
      tci.
    - eapply Singleton_Included. eapply project_var_In_Union. eassumption.
  Qed.

  Lemma Closure_conversion_occurs_free_Included_mut :
    (forall e Scope {Hd : Decidable Scope} Funs GFuns c genv Γ FVs e' C
       (Hcc : Closure_conversion clo_tag Scope Funs GFuns c genv Γ FVs e e' C)
       (Hun: fundefs_names_unique e),
        occurs_free (C |[ e' ]|) \subset (Scope :|: (Funs \\ Scope) :|: (GFuns \\ Scope) :|: image genv (Funs \\ Scope) :|: [set Γ])) /\
    (forall B Bg GFuns c FVs B'
       (Hcc: Closure_conversion_fundefs clo_tag Bg GFuns c FVs B B')
       (Hun: fundefs_names_unique_fundefs B),
       occurs_free_fundefs B' \subset (name_in_fundefs Bg :|: GFuns) \\ (name_in_fundefs B')).
  Proof with now eauto with Ensembles_DB functions_BD.
    exp_defs_induction IHe IHl IHB; intros; inv Hcc.
    - eapply project_vars_occurs_free_ctx_Included;
      [ eassumption | | reflexivity ].
      rewrite occurs_free_Econstr.
      apply Union_Included. now eauto with Ensembles_DB.
      apply Setminus_Included_Included_Union.
      eapply Included_trans. eapply IHe. 2:{ eassumption. } tci.
      intros f Hunf. eapply Hun. now constructor.
      rewrite Union_commut with (s2 := Singleton var v), !Union_assoc.
      eapply Union_Included; sets.
      eapply Union_Included; eauto 10 with Ensembles_DB functions_BD.
    - eapply project_var_occurs_free_ctx_Included;
        [ eassumption | | now apply Included_refl ]. inv H12.
      rewrite occurs_free_Ecase_nil. now apply Included_Union_r.
    - inv H12. destruct y as [c' e'].
      inv H2. simpl in H; subst. destruct H0 as [C' [e'' [Heq Hcce]]]. simpl in Heq; subst.
      eapply Included_trans. now eapply occurs_free_Ecase_ctx_app.
      apply Union_Included.
      + eapply project_var_occurs_free_ctx_Included;
        [ eassumption | | now apply Included_refl ].
        eapply Included_trans. eapply IHe. 2:{ eassumption. } tci.
        intros f Hunf. eapply Hun. econstructor. eassumption. now constructor.
        now apply Included_Union_l.
      + eapply IHl. 2:{ econstructor; eauto. } tci.
        intros f Hunf. eapply Hun. inv Hunf. econstructor 2. eassumption.
        econstructor 2. eassumption.
    - eapply project_var_occurs_free_ctx_Included;
      [ eassumption | | now apply Included_refl ].
      rewrite occurs_free_Eproj.
      rewrite Union_commut.
      apply Included_Union_compat; [| now apply Included_refl ].
      apply Setminus_Included_Included_Union.
      eapply Included_trans. eapply IHe. 2:{ eassumption. } tci.
      intros f Hunf. eapply Hun. now constructor.
      eapply Union_Included; [| now sets ].
      eapply Union_Included; [| now xsets ].
      eapply Union_Included; [| now xsets ].
      eauto 13 with Ensembles_DB functions_BD.
    - eapply project_vars_occurs_free_ctx_Included; [ eassumption | | now apply Included_refl ].
      repeat normalize_occurs_free. repeat normalize_sets.
      eapply Union_Included.
      now eauto with Ensembles_DB.
      eapply Setminus_Included_Included_Union.
      eapply Union_Included.
      now eauto with Ensembles_DB.
      eapply Setminus_Included_Included_Union.
      eapply Union_Included.
      eapply Union_Included; now eauto with Ensembles_DB.
      eapply Setminus_Included_Included_Union.
      eapply Included_trans. eapply IHe. 2:{ eassumption. } tci.
      intros h Hunf. eapply Hun. now constructor.
      eapply Union_Included; sets.
      eapply Union_Included; eauto 10 with Ensembles_DB functions_BD.
      eapply Union_Included.
      eapply Union_Included.
      eapply Union_Included; now xsets.
      now xsets.
      now xsets.
    - rewrite <- app_ctx_f_fuse.
      eapply project_vars_occurs_free_ctx_Included;
        [ eassumption | | now apply Included_refl ].
      simpl. rewrite occurs_free_Econstr.
      apply Union_Included. now apply Included_Union_r.
      rewrite occurs_free_Efun. apply Setminus_Included_Included_Union.
      eapply Union_Included.
      + eapply Included_trans. eapply IHB. eassumption.
        intros f Hunf. eapply Hun. now inv Hunf; eauto.
        eapply Setminus_Included_Included_Union.
        rewrite closure_conversion_fundefs_Same_set_image; [| eassumption ].
        eapply Union_Included; sets.
        eapply Included_trans. eapply add_global_funs_included_r; eauto.
        rewrite closure_conversion_fundefs_Same_set_image; [| eassumption ].
        eapply Union_Included; sets.
        eapply Included_trans. eapply Included_Union_Setminus with (s2 := Scope). now tci. now xsets.

      + eapply Setminus_Included_Included_Union.
        eapply Included_trans. eapply IHe. 2:{ eassumption. } now tci.
        intros f Hunf. eapply Hun. now constructor.
        eapply Union_Included; [| now sets ].
        eapply Union_Included.
        * rewrite <- closure_conversion_fundefs_Same_set_image with (B1 := f2) (B2 := B') at 1; [| eassumption ].
          eapply Union_Included. eapply Union_Included. now xsets.
          -- eapply Included_trans. eapply Setminus_Setminus_Included. tci.
             eapply Union_Included. rewrite Setminus_Union_distr. now xsets. now sets.
          -- eapply Included_trans. eapply Setminus_Setminus_Included. now tci.
             eapply Union_Included. eapply Included_trans. eapply Included_Setminus_compat.
             eapply add_global_funs_included_r; eauto. reflexivity. rewrite Setminus_Union_distr.
             eapply Union_Included; now xsets. now sets.
        * eapply Included_trans. eapply extend_fundefs'_image_Included'.
          eapply Union_Included; sets.
          rewrite !Setminus_Union_distr. rewrite Setminus_Included_Empty_set; sets.
          rewrite Union_Empty_set_neut_l.
          eapply Included_trans. eapply image_monotonic. eapply Included_Setminus_compat; [| reflexivity ].
          eapply Setminus_Setminus_Included. tci.
          rewrite Setminus_Union_distr. rewrite Setminus_Same_set_Empty_set, Union_Empty_set_neut_r.
          xsets.
    - eapply project_vars_occurs_free_ctx_Included;
      [ eassumption | | now apply Included_refl ].
      repeat normalize_occurs_free. repeat normalize_sets.
      apply Union_Included. eauto with Ensembles_DB.
      apply Setminus_Included_Included_Union.
      apply Union_Included. eauto with Ensembles_DB.
      apply Setminus_Included_Included_Union.
      eauto 7 with Ensembles_DB.
    - cbn. rewrite occurs_free_Eprim_val.
      (* apply Union_Included; [ now eauto with Ensembles_DB |].  *)
      apply Setminus_Included_Included_Union.
      eapply Included_trans. eapply IHe. 2:{ eassumption. } now tci.
      intros f Hunf. eapply Hun. now constructor.
      eapply Union_Included; [| now sets ].
      eapply Union_Included; [| now xsets ].
      eapply Union_Included; [| now xsets ].
      eapply Union_Included; [| now xsets ].
      eapply Union_Included; [| now xsets ].
      xsets.
    - eapply project_vars_occurs_free_ctx_Included;
      [ eassumption | | now apply Included_refl ].
      rewrite occurs_free_Eprim.
      apply Union_Included; [ now eauto with Ensembles_DB |].
      apply Setminus_Included_Included_Union.
      eapply Included_trans. eapply IHe. 2:{ eassumption. } now tci.
      intros f Hunf. eapply Hun. now constructor.
      eapply Union_Included; [| now sets ].
      eapply Union_Included; [| now xsets ].
      eapply Union_Included; [| now xsets ].
      eapply Union_Included; [| now xsets ].
      eapply Union_Included; [| now xsets ].
      xsets.
    - eapply project_var_occurs_free_ctx_Included; eauto.
      normalize_occurs_free... reflexivity.
    - rewrite occurs_free_fundefs_Fcons.
      apply Union_Included.
      + apply Setminus_Included_Included_Union.
        eapply Included_trans. eapply IHe. 2:{ eassumption. } now tci.
        intros f Hunf. eapply Hun. left. now eauto.
        rewrite FromList_cons. simpl.
        eapply Union_Included; sets.
        eapply Union_Included; sets.
        eapply Union_Included; sets.
        * rewrite <- (Union_Included_Union_Setminus _ _ (_ |: _)); tci; xsets.
        * rewrite <- (Union_Included_Union_Setminus _ _ (_ |: _)); tci; xsets.
        * eapply Included_trans. eapply image_monotonic. eapply Setminus_Included.
          eapply Included_trans. eapply extend_fundefs'_image. sets.
      + apply Setminus_Included_Included_Union.
        eapply Included_trans. eapply IHB. eassumption.
        intros f Hunf. inv Hunf; eauto.
        specialize (Hun (Fcons v t l e f5) (or_intror eq_refl)).
        now inv Hun; eauto.
        simpl. eapply Setminus_Included_Included_Union.
        rewrite <- Union_assoc, <- Union_Included_Union_Setminus;
          eauto with Ensembles_DB typeclass_instances.
    - rewrite occurs_free_fundefs_Fnil. now apply Included_Empty_set.
  Qed.

  (* TODO move *)
  Lemma Intersection_Union_Disjoint (A : Type) (S1 S2 S3 : Ensemble A) :
    Disjoint A S2 S3 -> (S1 :|: S2) :&: S3 <--> S1 :&: S3.
  Proof.
    intros Hd. split; eauto; intros x Hin; inv Hin; eauto.
    inv H; eauto. exfalso; eauto. eapply Hd; constructor; eauto.
  Qed.


  Lemma Closure_conversion_occurs_free_Included_alt_mut :
    (forall e Scope Funs GFuns c genv Γ FVs e' C
            (Hcc : Closure_conversion clo_tag Scope Funs GFuns c genv Γ FVs e e' C)
            {HD : Decidable Scope}
       (Hun: fundefs_names_unique e),
        occurs_free (C |[ e' ]|) \subset
        Scope :|: (occurs_free e :&: (Funs \\ Scope :|: (GFuns \\ Scope)) :|: image genv (Funs \\ Scope)) :|: [set Γ]) /\
    (forall B Bg GFuns c FVs B'
       (Hcc: Closure_conversion_fundefs clo_tag Bg GFuns c FVs B B')
       (Hun: fundefs_names_unique_fundefs B),
        occurs_free_fundefs B' \subset occurs_free_fundefs B :&: (name_in_fundefs Bg :|: GFuns)).
  Proof with now eauto with Ensembles_DB functions_BD.
    exp_defs_induction IHe IHl IHB; intros; inv Hcc.
    - eapply project_vars_occurs_free_ctx_alt_Included; [ eassumption | | sets ].
      repeat normalize_occurs_free.
      apply Union_Included. now eauto with Ensembles_DB. eapply Setminus_Included_Included_Union.
      eapply Included_trans. eapply IHe. eassumption. now tci. intros f Hfin. eapply Hun. now constructor.
      eapply Union_Included; [| now xsets ].
      eapply Union_Included. now sets.
      eapply Union_Included; [| now xsets ].

      do 3 eapply Included_Union_preserv_l. eapply Included_Union_preserv_r. eapply Included_Union_preserv_l.
      rewrite <- Intersection_Setmius_Disjoint with (S2 := [set v]).
      eapply Included_Intersection_compat; sets. now sets.

      eapply Union_Included; sets.
      eapply Union_Included; sets.
      normalize_occurs_free.  eapply Union_Included; sets.
      eapply Included_Union_preserv_l. eapply Included_Union_preserv_r. eapply Included_Union_preserv_l.
      eapply Included_Intersection_compat; sets.
    - eapply project_var_occurs_free_ctx_alt_Included; [ eassumption | | sets ]. inv H12.
      repeat normalize_occurs_free. sets.
      normalize_occurs_free...
    - inv H12. destruct y as [c' e'].
      inv H2. simpl in H; subst. destruct H0 as [C' [e'' [Heq Hcce]]]. simpl in Heq; subst.
      eapply Included_trans. now eapply occurs_free_Ecase_ctx_app.
      apply Union_Included.
      + eapply project_var_occurs_free_ctx_alt_Included; [ eassumption | | ].
        eapply Included_trans. eapply IHe. eassumption. now tci. intros f Hfin. eapply Hun. econstructor. eassumption. now left.
        normalize_occurs_free.
        eapply Union_Included; sets.
        eapply Union_Included; sets.
        eapply Union_Included; sets.
        do 2 eapply Included_Union_preserv_l. eapply Included_Union_preserv_r. eapply Included_Union_preserv_l.
        eapply Included_Intersection_compat; sets.

        eapply Union_Included; sets.
        eapply Union_Included; sets.
        eapply Union_Included; sets.
        eapply Included_Union_preserv_l. eapply Included_Union_preserv_r. eapply Included_Union_preserv_l.
        eapply Included_Intersection_compat; sets.
      + eapply Included_trans. eapply IHl. econstructor; eauto. now tci.
        intros f Hfin. eapply Hun. inv Hfin. econstructor. eassumption. right. eassumption.
        normalize_occurs_free.
        eapply Union_Included; sets.
        eapply Union_Included; sets.
        eapply Union_Included; sets.
        eapply Included_Union_preserv_l. eapply Included_Union_preserv_r. eapply Included_Union_preserv_l.
        eapply Included_Intersection_compat; sets.
    - eapply project_var_occurs_free_ctx_alt_Included; [ eassumption | | sets ].
      repeat normalize_occurs_free.
      apply Union_Included. now eauto with Ensembles_DB. eapply Setminus_Included_Included_Union.
      eapply Included_trans. eapply IHe. eassumption. now tci.
      intros f Hfin. eapply Hun. now constructor.
      eapply Union_Included; [| sets ].
      eapply Union_Included; [| sets ]. now sets.
      eapply Union_Included; sets.
      do 3 eapply Included_Union_preserv_l. eapply Included_Union_preserv_r. eapply Included_Union_preserv_l.
      rewrite <- Intersection_Setmius_Disjoint with (S2 := [set v]). eapply Included_Intersection_compat; sets.
      now sets. now xsets.
      eapply Union_Included; sets.
      eapply Union_Included; sets.
      normalize_occurs_free.
      eapply Union_Included; sets.
      eapply Included_Union_preserv_l. eapply Included_Union_preserv_r. eapply Included_Union_preserv_l.
      eapply Included_Intersection_compat; sets.
    - eapply project_vars_occurs_free_ctx_alt_Included; [ eassumption | | normalize_sets; normalize_occurs_free; sets ].
      repeat normalize_occurs_free. repeat normalize_sets.
      eapply Union_Included; sets.
      rewrite !Setminus_Union_distr.
      eapply Union_Included; sets.
      eapply Union_Included; sets.
      eapply Union_Included; sets.
      eapply Union_Included; sets.
      do 3 eapply Setminus_Included_Included_Union.
      eapply Included_trans. eapply IHe. eassumption.  now tci. intros g Hfin. eapply Hun. now constructor.
      eapply Union_Included; sets.
      eapply Union_Included; sets.
      eapply Union_Included; sets. now xsets. eapply Union_Included; sets.
      do 5 eapply Included_Union_preserv_l. eapply Included_Union_preserv_r. eapply Included_Union_preserv_l.
      rewrite <- Intersection_Setmius_Disjoint with (S2 := [set x]). eapply Included_Intersection_compat; sets.
      now sets. now xsets.
      eapply Union_Included; sets.
      eapply Union_Included; sets.
      eapply Union_Included; sets.
      eapply Included_Union_preserv_l. eapply Included_Union_preserv_r. eapply Included_Union_preserv_l.
      eapply Included_Intersection_compat; sets.
    - simpl. rewrite <- app_ctx_f_fuse.
      eapply project_vars_occurs_free_ctx_alt_Included; [ eassumption | | ].
      + simpl. repeat normalize_occurs_free.
        eapply Union_Included; sets. rewrite Setminus_Union_distr.
        eapply Union_Included; sets.
        * eapply Setminus_Included_Included_Union. eapply Included_trans.
          eapply IHB. eassumption.  intros f Hfin. inv Hfin; subst; now eauto.
          eapply Included_trans.
          eapply Included_Intersection_compat. reflexivity.
          eapply Union_Included; [| eapply add_global_funs_included_r; eassumption]. sets.
          rewrite Union_assoc. do 4 eapply Included_Union_preserv_l. rewrite (Union_commut Scope), Union_Intersection_distr.
          rewrite Intersection_commut. rewrite Intersection_Union_Disjoint.
          rewrite Intersection_commut.
          eapply Included_Intersection_compat; sets.
          eapply Included_trans. eapply Included_Union_Setminus with (s2 := Scope). now tci.
          now sets. now eapply occurs_free_fundefs_name_in_fundefs_Disjoint; eauto.
        * { do 2 eapply Setminus_Included_Included_Union. eapply Included_trans. eapply IHe. eassumption. now tci.
            intros f Hfin. eapply Hun. now constructor.
            eapply Union_Included; sets.
            eapply Union_Included; sets. xsets.
            - eapply Included_trans. eapply Included_Union_compat. reflexivity.
              eapply extend_fundefs'_image_Included'.
              assert (Hsub : name_in_fundefs f2 :|: Funs \\ (Scope \\ name_in_fundefs f2) \subset
                                                                   name_in_fundefs f2 :|: (Funs \\ Scope)).
              { eapply Included_trans. rewrite !Setminus_Union_distr. eapply Included_Union_compat.
                eapply Setminus_Setminus_Included. tci.
                eapply Setminus_Setminus_Included. tci. eapply Union_Included; sets. }

              eapply Union_Included; [| eapply Union_Included ]; sets.
              + eapply Included_trans.
                eapply Included_Intersection_compat. reflexivity. eapply Included_Union_compat.
                eassumption. reflexivity.
                eapply Included_trans
                  with (s2 :=  ((occurs_free_fundefs f2 :|: (occurs_free e \\ name_in_fundefs f2)) :&: (Funs \\ Scope :|: (GFuns \\ Scope))) :|: name_in_fundefs B'); [| xsets ].
                rewrite <- (closure_conversion_fundefs_Same_set_image) with (B2 := B'); [| eassumption ].
                rewrite Union_Intersection_distr. eapply Included_Intersection_compat.
                rewrite <- !Union_assoc. eapply Included_Union_preserv_r. sets.
                rewrite <- Union_Setminus; tci; sets.
                eapply Union_Included. sets.
                eapply Included_trans. eapply Setminus_Setminus_Included. now tci. eapply Union_Included; sets.
                eapply Included_trans. eapply Included_Setminus_compat.
                eapply add_global_funs_included_r. eassumption. reflexivity. rewrite Setminus_Union_distr. sets.

              + eapply Included_trans. eapply image_monotonic.
                eapply Included_Setminus_compat. eassumption. reflexivity.
                rewrite Setminus_Union_distr. rewrite Setminus_Same_set_Empty_set.
                xsets. }
      + rewrite <- H1, !Union_assoc.
        normalize_occurs_free. eapply Included_Union_compat; sets.
        eapply Included_Union_compat; sets.
        eapply Included_Union_compat; sets.
        eapply Included_Intersection_compat; sets.
    - eapply project_vars_occurs_free_ctx_alt_Included; [ eassumption | | normalize_sets; normalize_occurs_free; sets ].
      repeat normalize_occurs_free. repeat normalize_sets.
      eapply Union_Included; sets.
      rewrite !Setminus_Union_distr.
      eapply Union_Included; sets.
      eapply Union_Included; sets.
      eapply Union_Included; sets.
      eapply Union_Included; sets.
      eapply Union_Included; sets.
      eapply Union_Included; sets.
      do 1 eapply Included_Union_preserv_l. eapply Included_Union_preserv_r. eapply Included_Union_preserv_l.
      eapply Included_Intersection_compat; sets.

    - cbn. rewrite occurs_free_Eprim_val.
      repeat normalize_occurs_free.
      eapply Setminus_Included_Included_Union.
      eapply Included_trans. eapply IHe. eassumption. now tci.
      intros f Hfin. eapply Hun. now constructor.
      eapply Union_Included; [| sets ].
      eapply Union_Included; [| sets ].
      now sets.
      eapply Union_Included; [| now xsets ].

      do 2 eapply Included_Union_preserv_l. eapply Included_Union_preserv_r. eapply Included_Union_preserv_l.
      rewrite <- Intersection_Setmius_Disjoint with (S2 := [set v]). eapply Included_Intersection_compat; sets.
      sets.

    - eapply project_vars_occurs_free_ctx_alt_Included; [ eassumption | | sets ].
      repeat normalize_occurs_free.
      apply Union_Included. now eauto with Ensembles_DB. eapply Setminus_Included_Included_Union.
      eapply Included_trans. eapply IHe. eassumption. now tci.
      intros f Hfin. eapply Hun. now constructor.
      eapply Union_Included; [| sets ].
      eapply Union_Included; [| sets ].
      now sets.
      eapply Union_Included; [| now xsets ].
      do 3 eapply Included_Union_preserv_l. eapply Included_Union_preserv_r. eapply Included_Union_preserv_l.
      rewrite <- Intersection_Setmius_Disjoint with (S2 := [set v]). eapply Included_Intersection_compat; sets.
      sets.

      eapply Union_Included; sets.
      eapply Union_Included; sets. eapply Union_Included; sets.
      normalize_occurs_free.
      eapply Included_Union_preserv_l. eapply Included_Union_preserv_r. eapply Included_Union_preserv_l.
      eapply Included_Intersection_compat; sets.
    - eapply project_var_occurs_free_ctx_alt_Included; [ eassumption | | ].
      repeat normalize_occurs_free. sets.
      repeat normalize_occurs_free. sets.
    - normalize_occurs_free. eapply Union_Included.
      + eapply Setminus_Included_Included_Union. eapply Included_trans.
        eapply IHe. eassumption. now tci.
        intros f Hfin. eapply Hun. left. now constructor.
        rewrite occurs_free_fundefs_Fcons. normalize_sets.
        eapply Union_Included; sets.
        eapply Union_Included; sets.
        eapply Union_Included; sets.

        eapply Included_trans with (s2 := ((occurs_free e \\ (v |: (FromList l :|: name_in_fundefs f5))
                                                                :|: (occurs_free_fundefs f5 \\ [set v])) :&: (name_in_fundefs Bg :|: GFuns)) :|: [set v]
                                                :|: name_in_fundefs defs'); [| sets ].
        rewrite <- (closure_conversion_fundefs_Same_set_image) with (B2 := defs'); [| eassumption ].
        rewrite !Union_Intersection_distr.
        rewrite <- Intersection_Setmius_Disjoint with (S2 := FromList l); sets.
        eapply Included_Intersection_compat; sets. eapply Setminus_Included_Included_Union.
        rewrite <- !Union_assoc. rewrite <- Union_Included_Union_Setminus. sets. tci. sets. sets.

        eapply Included_trans. eapply image_monotonic. eapply Setminus_Included.
        eapply Included_trans. eapply extend_fundefs'_image. sets.
      + eapply IHB in H11. eapply Setminus_Included_Included_Union. eapply Included_trans. eassumption.
        normalize_occurs_free.
        rewrite Union_Intersection_distr. eapply Included_Intersection_compat; sets.
        rewrite <- !Union_assoc.
        rewrite <- Union_Setminus; tci; sets.
        intros x Hfun. inv Hfun; eauto.
        specialize (Hun (Fcons v t l e f5) (or_intror eq_refl)).
        now inv Hun; eauto.
    - rewrite occurs_free_fundefs_Fnil at 1. sets.
  Qed.

  Lemma Closure_conversion_occurs_free_fundefs_cor :
    (forall B GFuns {Hd : Decidable GFuns} c FVs B'
       (Hcc: Closure_conversion_fundefs clo_tag B GFuns c FVs B B')
       (Hun: fundefs_names_unique_fundefs B),
        occurs_free_fundefs B' \subset occurs_free_fundefs B :&: GFuns).
  Proof.
    intros. eapply Closure_conversion_occurs_free_Included_alt_mut in Hcc; eauto.
    eapply Included_trans. eassumption.
    rewrite Intersection_commut,Union_commut. rewrite Intersection_Union_Disjoint.
    rewrite Intersection_commut. reflexivity.
    eapply occurs_free_fundefs_name_in_fundefs_Disjoint.
  Qed.

  (* TODO move *)
  Lemma Included_Intersection_Included A (s1 s2 s3 : Ensemble A) :
    s1 \subset s3 ->
    s2 \subset s3 ->
    s1 :&: s2 :&: s3 \subset s1 :&: s2.
  Proof.
    intros H1 H2 x Hin. inv Hin. inv H; eauto.
  Qed.


  Definition funnames_in_exp (e : exp) :=
    fun f => exists B, funs_in_exp B e /\ f \in name_in_fundefs B.

  Definition funnames_in_fundefs (fds : fundefs) :=
    fun f => exists B, funs_in_fundef B fds /\ f \in name_in_fundefs B.

  (* FVs of function definitions are in G *)
  Definition fun_fv_in e G :=
    forall B, funs_in_exp B e -> occurs_free_fundefs B \subset G.

  Definition fun_fv_in_fundefs B G :=
    forall B', B = B' \/ funs_in_fundef B' B -> occurs_free_fundefs B' \subset G.


  Lemma Closure_conversion_closed_fundefs_mut :
    (forall e Scope Funs GFuns genv c Γ FVs e' C B
            (Hcc : Closure_conversion clo_tag Scope Funs GFuns c genv Γ FVs e e' C)
            (Hun: fundefs_names_unique e)
            (Hin : funs_in_exp B (C |[ e' ]|)),
        occurs_free_fundefs B \subset GFuns :|: funnames_in_exp e) /\
    (forall B Funs GFuns c FVs B' B''
            (Hcc: Closure_conversion_fundefs clo_tag Funs GFuns c FVs B B')
            (Hun: fundefs_names_unique_fundefs B)
            (Hin : funs_in_fundef B'' B'),
       occurs_free_fundefs B'' \subset GFuns :|: funnames_in_fundefs B).
  Proof.
    exp_defs_induction IHe IHl IHB; intros; inv Hcc.
    - rewrite project_vars_free_funs_in_exp in Hin; [| eassumption ]. inv Hin.
      eapply IHe in H14; [| | eassumption ].
      eapply Included_trans. eassumption.
      eapply Included_Union_compat. now sets.
      intros x Hin. inv Hin. inv H. eexists. split; eauto.
      intros B' H. eapply Hun. now constructor.
    - inv H12.
      rewrite project_var_free_funs_in_exp in Hin; [| eassumption ].
      inv Hin. inv H4.
    - inv H12. destruct H2 as [Heq [C' [e' [Heq' Hcc']]]]. destruct y as [t e''].
      simpl in *; subst.
      rewrite project_var_free_funs_in_exp in Hin; [| eassumption ].
      inv Hin. inv H5.
      + inv H. eapply IHe in Hcc'; [ | | eassumption ].
        eapply Included_trans. eassumption.
        eapply Included_Union_compat. now sets.
        intros x Hin. inv Hin. inv H. eexists. split; eauto. econstructor; eauto. now left.
        intros B' H. eapply Hun. econstructor. eassumption. now constructor.
      + eapply Included_trans. eapply IHl. now econstructor; eauto.
        intros B' HB'. eapply Hun. inv HB'. econstructor. eassumption.
        constructor 2. eassumption.
        rewrite project_var_free_funs_in_exp.
        econstructor; eassumption. eassumption.
        eapply Included_Union_compat. now sets.
        intros x Hin. inv Hin. inv H0. eexists. split; eauto. inv H2. eapply In_Case. eassumption. now right; eauto.
    - rewrite project_var_free_funs_in_exp in Hin; [| eassumption ]. inv Hin.
      eapply IHe in H15; [| | eassumption ].
      eapply Included_trans. eassumption.
      eapply Included_Union_compat. now sets.
      intros x Hin. inv Hin. inv H. eexists. split; eauto.
      intros B' H. eapply Hun. now constructor.
    - rewrite project_vars_free_funs_in_exp in Hin; [| eassumption ].
      inv Hin. inv H1. inv H2.
      eapply IHe in H18; [| | eassumption ].
      eapply Included_trans. eassumption.
      eapply Included_Union_compat. now sets.
      intros z Hin. inv Hin. inv H. eexists. split; eauto.
      intros B' H. eapply Hun. now constructor.
    - rewrite <- app_ctx_f_fuse in *.
      rewrite project_vars_free_funs_in_exp in Hin; [| eassumption ].
      inv Hin. inv H8.
      + assert (HB := H15). eapply Closure_conversion_occurs_free_Included_mut in H15.
        eapply Included_trans. eassumption. rewrite Setminus_Union_distr.
        rewrite closure_conversion_fundefs_Same_set_image; [| eassumption ].
        rewrite Setminus_Same_set_Empty_set. repeat normalize_sets.
        eapply Included_trans. eapply Included_Setminus_compat. eapply add_global_funs_included_r.
        eassumption. reflexivity.
        rewrite closure_conversion_fundefs_Same_set_image; [| eassumption ].
        rewrite Setminus_Union_distr, Setminus_Same_set_Empty_set. repeat normalize_sets. now sets.

        intros x Hin. eapply Hun. inv Hin; eauto.
      + eapply IHe in H18; [ | | eassumption ].
        eapply Included_trans. eassumption.
        eapply Included_trans. eapply Included_Union_compat. eapply add_global_funs_included_r.
        eassumption. reflexivity. rewrite <- Union_assoc.
        eapply Included_Union_compat. now sets.
        intros x Hin. inv Hin.

        eexists. split. eapply In_Fun1. eassumption.
        inv H. inv H0. eexists. split. eapply In_Fun2. eassumption. eassumption.

        intros B'' H. eapply Hun. now constructor.
      + eapply Included_trans. eapply IHB; [ eassumption | | eassumption ].
        intros B1 HB1. now inv HB1; eauto.

        eapply Included_trans. eapply Included_Union_compat. eapply add_global_funs_included_r.
        eassumption. reflexivity. rewrite <- Union_assoc.
        eapply Included_Union_compat. now sets.
        intros x Hin. inv Hin.

        eexists. split. eapply In_Fun1. eassumption.
        inv H. inv H0. eexists. split. eapply In_Fun3. eassumption. eassumption.

    - rewrite project_vars_free_funs_in_exp in Hin; [| eassumption ]. inv Hin. inv H1. inv H4.
    - inv Hin. eapply IHe in H12; [| | eassumption].
      eapply Included_trans. eassumption.
      eapply Included_Union_compat. now sets.
      intros x Hin. inv Hin. inv H. eexists. split; eauto.
      intros B' H. eapply Hun. now constructor.
    - rewrite project_vars_free_funs_in_exp in Hin; [| eassumption ]. inv Hin.
      eapply IHe in H14; [| | eassumption ].
      eapply Included_trans. eassumption.
      eapply Included_Union_compat. now sets.
      intros x Hin. inv Hin. inv H. eexists. split; eauto.
      intros B' H. eapply Hun. now constructor.
    - rewrite project_var_free_funs_in_exp in Hin; [| eassumption ]. inv Hin.
    - inv Hin.
      + eapply IHe in H12; [ | | eassumption ].
        eapply Included_trans. eassumption.
        eapply Included_Union_compat. now sets.
        intros z Hin. inv Hin. inv H. eexists. split; eauto.

        intros B' H. eapply Hun. left. now constructor.
      + eapply IHB in H11; [| | eassumption ].

        eapply Included_trans. eassumption.
        eapply Included_Union_compat. now sets.
        intros z Hin. inv Hin. inv H. eexists. split; eauto.
        intros B' H. inv H; eauto.
        specialize (Hun (Fcons v t l e f5) (or_intror eq_refl)). now inv Hun; eauto.
    - inv Hin.
  Qed.


  Lemma funnames_in_exp_Econstr x c ys e :
    funnames_in_exp (Econstr x c ys e) <-->  funnames_in_exp e.
  Proof.
    split.
    - intros z [B Hin]. destructAll. inv H. eexists; split; eauto.
    - intros z [B Hin]. destructAll. eexists; split; eauto.
  Qed.

  Lemma funnames_in_exp_Eproj x c n y e :
    funnames_in_exp (Eproj x c n y e) <--> funnames_in_exp e.
  Proof.
    split.
    - intros z [B Hin]. destructAll. inv H. eexists; split; eauto.
    - intros z [B Hin]. destructAll. eexists; split; eauto.
  Qed.

  Lemma funnames_in_exp_Ecase_nil x :
    funnames_in_exp (Ecase x []) <--> Empty_set _.
  Proof.
    split; sets.
    - intros z [B Hin]. destructAll. inv H. inv H5.
  Qed.

  Lemma funnames_in_exp_Ecase_cons x c e P :
    funnames_in_exp (Ecase x ((c, e) :: P)) <--> funnames_in_exp e :|: funnames_in_exp (Ecase x P).
  Proof.
    split.
    - intros z [B Hin]. destructAll. inv H. inv H5.
      + inv H. left. eexists; split; eauto.
      + right. eexists; split; eauto.
    - intros z Hin. inv Hin; destruct H; destructAll.
      + eexists. split. econstructor. eassumption. now left. eassumption.
      + eexists. split. inv H. econstructor. eassumption. now right; eauto. eassumption.
  Qed.


  Lemma funnames_in_exp_Eletapp x f c ys e :
    funnames_in_exp (Eletapp x f c ys e) <--> funnames_in_exp e.
  Proof.
    split.
    - intros z [B Hin]. destructAll. inv H. eexists; split; eauto.
    - intros z [B Hin]. destructAll. eexists; split; eauto.
  Qed.

  Lemma funnames_in_exp_Eapp f c xs :
    funnames_in_exp (Eapp f c xs) <--> Empty_set _.
  Proof.
    split; sets.
    - intros z [B Hin]. destructAll. inv H.
  Qed.

  Lemma funnames_in_exp_Ehalt x :
    funnames_in_exp (Ehalt x) <--> Empty_set _.
  Proof.
    split; sets.
    - intros z [B Hin]. destructAll. inv H.
  Qed.

  Lemma funnames_in_exp_Eprim_val x c e :
    funnames_in_exp (Eprim_val x c e) <-->  funnames_in_exp e.
  Proof.
    split.
    - intros z [B Hin]. destructAll. inv H. eexists; split; eauto.
    - intros z [B Hin]. destructAll. eexists; split; eauto.
  Qed.

  Lemma funnames_in_exp_Eprim x c ys e :
    funnames_in_exp (Eprim x c ys e) <-->  funnames_in_exp e.
  Proof.
    split.
    - intros z [B Hin]. destructAll. inv H. eexists; split; eauto.
    - intros z [B Hin]. destructAll. eexists; split; eauto.
  Qed.

  Lemma funnames_in_exp_Efun B e :
    funnames_in_exp (Efun B e) <-->  name_in_fundefs B :|: funnames_in_fundefs B :|: funnames_in_exp e.
  Proof.
    split.
    - intros z [B' Hin]. destructAll. inv H; eauto.
      + right. eexists; split; eauto.
      + left. right. eexists; split; eauto.
    - intros z Hin. inv Hin. inv H.
      + eexists. split. econstructor. eassumption.
      + inv H0. destructAll. eexists. split. eapply In_Fun3. eassumption. eassumption.
      + inv H. destructAll. eexists. split. eapply In_Fun2. eassumption. eassumption.
  Qed.


  Lemma funnames_in_fundefs_Fcons f t xs e B :
    funnames_in_fundefs (Fcons f t xs e B) <-->  funnames_in_exp e :|: funnames_in_fundefs B.
  Proof.
    split.
    - intros z [B' Hin]. destructAll. inv H; eauto.
      + left. eexists; split; eauto.
      + right. eexists; split; eauto.
    - intros z Hin. inv Hin. inv H.
      + inv H0. eexists. split. econstructor; eassumption. eassumption.
      + inv H. inv H0. eexists. split. eapply In_Fcons2. eassumption. eassumption.
  Qed.

  Lemma funnames_in_exp_Fnil :
    funnames_in_fundefs Fnil <--> Empty_set _.
  Proof.
    split; sets.
    - intros z [B Hin]. destructAll. inv H.
  Qed.


  Lemma project_var_funnnames_in_exp Scope Funs GFuns c genv Γ FVs S x y C Q e :
    project_var clo_tag Scope Funs GFuns c genv Γ FVs S x y C Q ->
    funnames_in_exp (C |[ e ]|) <-->  funnames_in_exp e.
  Proof.
    intros Hvars. inv Hvars.
    - reflexivity.
    - simpl. rewrite funnames_in_exp_Econstr. reflexivity.
    - simpl. do 2 rewrite funnames_in_exp_Econstr. reflexivity.
    - simpl. rewrite funnames_in_exp_Eproj. reflexivity.
  Qed.

  Lemma project_vars_funnnames_in_exp Scope Funs GFuns c genv Γ FVs S x y C Q e :
    project_vars clo_tag Scope Funs GFuns c genv Γ FVs S x y C Q ->
    funnames_in_exp (C |[ e ]|) <-->  funnames_in_exp e.
  Proof.
    intros Hvars. induction Hvars.
    - reflexivity.
    - simpl. rewrite <- app_ctx_f_fuse. rewrite project_var_funnnames_in_exp; [| eassumption ].
      eassumption.
  Qed.

  Lemma funnames_in_exp_Closure_Conversion :
    (forall e Scope Funs GFuns genv c Γ FVs e' C
            (Hcc : Closure_conversion clo_tag Scope Funs GFuns c genv Γ FVs e e' C),
            funnames_in_exp (C |[ e' ]|) <--> funnames_in_exp  e) /\
    (forall B Funs GFuns c FVs B'
            (Hcc: Closure_conversion_fundefs clo_tag Funs GFuns c FVs B B'),
       funnames_in_fundefs B' <--> funnames_in_fundefs B).
  Proof.
    exp_defs_induction IHe IHl IHB; intros; inv Hcc;
      (try (rewrite project_vars_funnnames_in_exp; [| eassumption ]));
      (try (rewrite project_var_funnnames_in_exp; [| eassumption ])).
    - rewrite !funnames_in_exp_Econstr. eauto.
    - inv H12. rewrite !funnames_in_exp_Ecase_nil. sets.
    - inv H12. destruct y. destructAll. simpl in *. subst. rewrite !funnames_in_exp_Ecase_cons.
      rewrite IHe; eauto.
      rewrite <- IHl. 2:{ econstructor; try eassumption. }
      rewrite project_var_funnnames_in_exp; [| eassumption ]. reflexivity.
    - rewrite !funnames_in_exp_Eproj. eauto.
    - rewrite !funnames_in_exp_Eproj. rewrite !funnames_in_exp_Eletapp. eauto.
    - rewrite <- app_ctx_f_fuse.
      rewrite project_vars_funnnames_in_exp; [| eassumption ].
      simpl. rewrite !funnames_in_exp_Econstr. rewrite !funnames_in_exp_Efun.
      rewrite IHe; [| eassumption ]. rewrite IHB; [| eassumption ].
      rewrite <- closure_conversion_fundefs_Same_set_image. reflexivity. eassumption.
    - rewrite !funnames_in_exp_Eproj. rewrite !funnames_in_exp_Eapp. sets.
    - cbn. eauto. rewrite !funnames_in_exp_Eprim_val. eauto.
    - rewrite !funnames_in_exp_Eprim. eauto.
    - rewrite !funnames_in_exp_Ehalt. sets.
    - rewrite !funnames_in_fundefs_Fcons. rewrite IHe; eauto. erewrite IHB; eauto. reflexivity.
    - rewrite !funnames_in_exp_Fnil. reflexivity.
  Qed.

  Lemma project_var_occurs_free_ctx_Included_no_env Scope Funs GFuns c genv Γ S x y C Q F e:
    project_var clo_tag Scope Funs GFuns c genv Γ [] S x y C Q ->
    (occurs_free e) \subset (F :|: [set y]) ->
    (Scope :|: ([set x] :&: (Funs \\ Scope :|: (GFuns \\ Scope))) :|: image genv (Funs \\ Scope)) \subset F ->
    (occurs_free (C |[ e ]|)) \subset F.
  Proof with now eauto with Ensembles_DB functions_BD.
    intros Hproj Hinc1 Hinc2. inv Hproj.
    - simpl. eapply Included_trans. eassumption.
      apply Union_Included. now apply Included_refl.
      eapply Included_trans; [| eassumption ].
      eauto with Ensembles_DB.
    - simpl.
      rewrite occurs_free_Econstr, !FromList_cons, FromList_nil,
      Union_Empty_set_neut_r.
      eapply Union_Included.
      + eapply Included_trans; [| now apply Hinc2 ].
        eapply Union_Included; sets. eapply Singleton_Included. left. right.
        constructor; eauto. left; constructor; eauto.
        eapply Singleton_Included. right.
        eapply In_image. constructor; eauto.
      + eauto with Ensembles_DB.
    - simpl.
      repeat normalize_occurs_free.
      rewrite FromList_cons, FromList_nil, Union_Empty_set_neut_l.
      rewrite FromList_singleton. rewrite !Setminus_Union_distr.
      rewrite Setminus_Same_set_Empty_set, Union_Empty_set_neut_r.
      eapply Union_Included.
      + eapply Included_trans; [| now apply Hinc2 ].
        eapply Setminus_Included_Included_Union.
        eapply Singleton_Included. left. left. right.
        econstructor; eauto. right. constructor; eauto.
      + eauto with Ensembles_DB.
    - simpl. inv H2.
  Qed.


  Lemma project_vars_occurs_free_ctx_Included_no_env Scope Funs GFuns c genv Γ
        S xs xs' C S' F e:
    project_vars clo_tag Scope Funs GFuns c genv Γ [] S xs xs' C S' ->
    Included _ (occurs_free e) (Union _ F (FromList xs')) ->
    Included _ (Scope :|: (FromList xs :&: (Funs \\ Scope :|: (GFuns \\ Scope))) :|: image genv (Funs \\ Scope)) F ->
    Included _ (occurs_free (C |[ e ]|)) F.
  Proof.
    revert C F xs' S S'. induction xs; intros C F xs' S S' Hproj Hinc1 Hinc2; inv Hproj; simpl in *; repeat normalize_sets.
    - eassumption.
    - rewrite <- app_ctx_f_fuse.
      eapply project_var_occurs_free_ctx_Included_no_env; [ eassumption | | ].
      eapply IHxs. eassumption. rewrite <- Union_assoc. eassumption.
      eapply Included_trans. eapply Included_trans; [| eapply Hinc2 ]; sets.
      eapply Included_Union_compat; sets.
      eapply Included_Union_compat; sets.
      eapply Included_Intersection_compat; sets. sets.
      eapply Included_trans; [| eassumption ].
      eapply Included_Union_compat; sets.
      eapply Included_Union_compat; sets.
      eapply Included_Intersection_compat; sets.
  Qed.

  Hint Resolve Included_Intersection_l Included_Intersection_r : Ensembles_DB.


  Lemma Closure_conversion_occurs_free_toplevel_aux :
    (forall e Scope Funs GFuns c genv Γ e' C
            (Hcc : Closure_conversion clo_tag Scope Funs GFuns c genv Γ [] e e' C)
            (HD : Decidable Scope)
        (Hun : fundefs_names_unique e),
        occurs_free (C |[ e' ]|) \subset Scope :|: (Funs \\ Scope :|: (GFuns \\ Scope)) :|: image genv (Funs \\ Scope)).
  Proof.
    induction e using exp_ind'; intros; inv Hcc.
    - eapply project_vars_occurs_free_ctx_Included_no_env; [ eassumption | | now sets ].
      rewrite occurs_free_Econstr.
      apply Union_Included. now eauto with Ensembles_DB.
      apply Setminus_Included_Included_Union.
      eapply Included_trans. eapply IHe. eassumption. now tci.
      intros f Hunf. eapply Hun. now constructor.
      rewrite Union_commut with (s2 := Singleton var v), !Union_assoc.
      eapply Union_Included; sets.
      eapply Union_Included; eauto 10 with Ensembles_DB functions_BD.
    - eapply project_var_occurs_free_ctx_Included_no_env;
        [ eassumption | | now sets ]. inv H12.
      rewrite occurs_free_Ecase_nil. now apply Included_Union_r.
    - inv H12. destruct y as [c' e'].
      inv H2. simpl in H; subst. destruct H0 as [C' [e'' [Heq Hcce]]]. simpl in Heq; subst.
      eapply Included_trans. now eapply occurs_free_Ecase_ctx_app.
      apply Union_Included.
      + eapply project_var_occurs_free_ctx_Included_no_env; [ eassumption | | now sets ].
        eapply Included_trans. eapply IHe. eassumption. now tci.
        intros f Hunf. eapply Hun. econstructor. eassumption. now constructor. now sets.
      + eapply IHe0. econstructor; eauto. now tci.
        intros f Hunf. eapply Hun. inv Hunf. econstructor 2. eassumption.
        econstructor 2. eassumption.
    - eapply project_var_occurs_free_ctx_Included_no_env; [ eassumption | | now sets ].
      rewrite occurs_free_Eproj.
      rewrite Union_commut.
      apply Included_Union_compat; [| now apply Included_refl ].
      apply Setminus_Included_Included_Union.
      eapply Included_trans. eapply IHe. eassumption. now tci.
      intros f Hunf. eapply Hun. now constructor.
      eapply Union_Included; [| now sets ].
      eapply Union_Included; [| now xsets ].
      eapply Union_Included; [| now sets ].
      xsets.
    - eapply project_vars_occurs_free_ctx_Included_no_env; [ eassumption | | now sets ].
      repeat normalize_occurs_free. repeat normalize_sets.
      eapply Union_Included.
      now eauto with Ensembles_DB.
      eapply Setminus_Included_Included_Union.
      eapply Union_Included.
      now eauto with Ensembles_DB.
      eapply Setminus_Included_Included_Union.
      eapply Union_Included.
      eapply Union_Included; now eauto with Ensembles_DB.
      eapply Setminus_Included_Included_Union.
      eapply Included_trans. eapply IHe. eassumption. now tci.
      intros h Hunf. eapply Hun. now constructor.
      eapply Union_Included; sets.
      eapply Union_Included; eauto 10 with Ensembles_DB functions_BD.
      eapply Union_Included; sets.
      now xsets.
    - rewrite <- app_ctx_f_fuse.
      eapply project_vars_occurs_free_ctx_Included_no_env;
        [ eassumption | | now sets ].
      simpl. rewrite occurs_free_Econstr.
      apply Union_Included. now apply Included_Union_r.
      rewrite occurs_free_Efun. apply Setminus_Included_Included_Union.
      eapply Union_Included.
      + eapply Included_trans. eapply Closure_conversion_occurs_free_Included_mut. eassumption.

        intros f Hunf. eapply Hun. now inv Hunf; eauto.
        rewrite Setminus_Union_distr.
        rewrite closure_conversion_fundefs_Same_set_image; [| eassumption ]. rewrite Setminus_Same_set_Empty_set.
        normalize_sets. eapply Setminus_Included_Included_Union.
        eapply Included_trans. eapply add_global_funs_included_r; eauto.
        rewrite closure_conversion_fundefs_Same_set_image; [| eassumption ].
        eapply Union_Included; [| now sets ].
        eapply Included_trans. eapply Included_Union_Setminus with (s2 := Scope); tci. now xsets.
      + eapply Setminus_Included_Included_Union.
        eapply Included_trans. eapply IHe. eassumption. now tci.
        intros f Hunf. eapply Hun. now constructor.
        eapply Union_Included.
        * rewrite <- closure_conversion_fundefs_Same_set_image with (B1 := f2) (B2 := B') at 1; [| eassumption ].
          eapply Union_Included. now xsets. eapply Union_Included.
          -- eapply Included_trans. eapply Setminus_Setminus_Included. tci.
             eapply Union_Included. rewrite Setminus_Union_distr. now xsets. now sets.
          -- eapply Included_trans. eapply Setminus_Setminus_Included. tci.
             eapply Union_Included; [| now sets ].
             eapply Included_trans. eapply Included_Setminus_compat.
             eapply add_global_funs_included_r; eauto. reflexivity.
             rewrite Setminus_Union_distr. eapply Union_Included; now xsets.
        * eapply Included_trans. eapply extend_fundefs'_image_Included'.
          eapply Union_Included; sets.
          rewrite !Setminus_Union_distr. rewrite Setminus_Included_Empty_set; sets.
          rewrite Union_Empty_set_neut_l.
          eapply Included_trans. eapply image_monotonic. eapply Included_Setminus_compat; [| reflexivity ].
          eapply Setminus_Setminus_Included. tci.
          rewrite Setminus_Union_distr. rewrite Setminus_Same_set_Empty_set, Union_Empty_set_neut_r.
          xsets.
    - eapply project_vars_occurs_free_ctx_Included_no_env;
      [ eassumption | | now sets ].
      repeat normalize_occurs_free. repeat normalize_sets.
      apply Union_Included. eauto with Ensembles_DB.
      apply Setminus_Included_Included_Union.
      apply Union_Included. eauto with Ensembles_DB.
      apply Setminus_Included_Included_Union.
      eauto 7 with Ensembles_DB.
    - cbn. rewrite occurs_free_Eprim_val.
      apply Setminus_Included_Included_Union.
      eapply Included_trans. eapply IHe. eassumption. now tci.
      intros f Hunf. eapply Hun. now constructor.
      eapply Union_Included; [| now xsets ].
      eapply Union_Included; [| now xsets ].
      eapply Union_Included; [| now xsets ]. xsets.
    - eapply project_vars_occurs_free_ctx_Included_no_env; [ eassumption | | now sets ].
      rewrite occurs_free_Eprim.
      apply Union_Included; [ now eauto with Ensembles_DB |].
      apply Setminus_Included_Included_Union.
      eapply Included_trans. eapply IHe. eassumption. now tci.
      intros f Hunf. eapply Hun. now constructor.
      eapply Union_Included; [| now xsets ].
      eapply Union_Included; [| now xsets ].
      eapply Union_Included; [| now xsets ]. xsets.
    - eapply project_var_occurs_free_ctx_Included_no_env; eauto.
      normalize_occurs_free... now sets. now sets.

      Unshelve. exact (Empty_set _).
  Qed.

  Corollary Closure_conversion_closed_fundefs e Scope Funs GFuns genv c Γ FVs e' C
        (Hcc : Closure_conversion clo_tag Scope Funs GFuns c genv Γ FVs e e' C)
        (Hun: fundefs_names_unique e) :
    fun_fv_in (C |[ e' ]|) (GFuns :|: funnames_in_exp (C |[ e' ]|)).
  Proof.
    intros B Hin. rewrite (proj1 funnames_in_exp_Closure_Conversion); [| eassumption ].
    eapply Closure_conversion_closed_fundefs_mut; eassumption.
  Qed.

  Lemma Closure_conversion_occurs_free_toplevel e Scope {_ : Decidable Scope} c genv Γ e' C
    (Hcc : Closure_conversion clo_tag Scope (Empty_set _) (Empty_set _) c genv Γ [] e e' C)
    (Hun : fundefs_names_unique e) :
    occurs_free (C |[ e' ]|) \subset Scope.

    eapply Included_trans. eapply Closure_conversion_occurs_free_toplevel_aux. eassumption.
    eassumption. eassumption. repeat normalize_sets. do 2 rewrite Setminus_Empty_set_abs_r at 1.
    repeat normalize_sets. rewrite image_Empty_set.
    now sets.
  Qed.

  (* TODO : move *)
  Lemma inclusion_trans {A} P1 P2 P3 :
    inclusion A P1 P2 ->
    inclusion A P2 P3 ->
    inclusion A P1 P3.
  Proof.
    now firstorder.
  Qed.

  (** * Lemmas about [Closure_conversion_fundefs] *)

  Lemma closure_conversion_fundefs_find_def c Bg GFuns FVs B1 B2 f t1 xs e1 :
    Closure_conversion_fundefs clo_tag Bg GFuns c FVs B1 B2 ->
    find_def f B1 = Some (t1, xs, e1) ->
    exists Γ' C e2,
      ~ In var (Union var (name_in_fundefs Bg :|: GFuns) (Union _ (FromList xs) (bound_var e1))) Γ' /\
      find_def f B2 = Some (t1, Γ' :: xs, (C |[ e2 ]|)) /\
      Closure_conversion clo_tag (FromList xs) (name_in_fundefs Bg) GFuns c
                         (extend_fundefs' id Bg Γ')  Γ' FVs e1 e2 C.
  Proof.
    intros Hcc Hdef. induction Hcc.
    - simpl in Hdef. destruct (M.elt_eq f f0) eqn:Heq; subst.
      + inv Hdef. repeat eexists; eauto.
        simpl.
        intros Hc. eapply H. now eauto.
        simpl. rewrite peq_true. reflexivity.
      + edestruct IHHcc as [Γ'' [C' [e2 [Hnin [Hfind Hcc']]]]]; eauto.
        repeat eexists; eauto. simpl. rewrite peq_false. eassumption.
        intros Hc. eapply n. eassumption.
    - inv Hdef.
  Qed.

  (** * Lemmas about [project_var] and [project_vars] *)

  Lemma project_var_free_set_Included Scope Funs GFuns c genv Γ FVs x x' C S S' :
    project_var clo_tag Scope GFuns Funs c genv Γ FVs S x x' C S' ->
    Included _ S' S.
  Proof with now eauto with Ensembles_DB.
    intros Hproj. inv Hproj...
  Qed.

  Lemma project_vars_free_set_Included Scope Funs GFuns c genv Γ FVs xs xs' C S S' :
    project_vars clo_tag Scope Funs GFuns c genv Γ FVs S xs xs' C S' ->
    Included _ S' S.
  Proof.
    intros Hproj. induction Hproj.
    - now apply Included_refl.
    - eapply Included_trans. eassumption.
      eapply project_var_free_set_Included. eassumption.
  Qed.

  Lemma project_var_not_In_free_set Scope Funs GFuns c genv Γ FVs x x' C S S'  :
    project_var clo_tag Scope Funs GFuns c genv Γ FVs S x x' C S' ->
    Disjoint _ S (Scope :|: (Funs \\ Scope) :|: (GFuns \\ Scope) :|: FromList FVs :|: [set Γ]) ->
    ~ In _ S' x'.
  Proof.
    intros Hproj Hd. inv Hproj; intros Hc.
    - eapply Hd. constructor; eauto.
    - inv Hc. exfalso. eauto.
    - inv Hc. inv H4; eauto.
    - inv Hc; eauto.
  Qed.

  Lemma project_vars_not_In_free_set Scope Funs GFuns c genv Γ FVs xs xs' C S S'  :
    project_vars clo_tag Scope Funs GFuns c genv Γ FVs S xs xs' C S' ->
    Disjoint _ S (Scope :|: (Funs \\ Scope) :|: (GFuns \\ Scope) :|: FromList FVs :|: [set Γ])  ->
    Disjoint _ S' (FromList xs').
  Proof.
    intros Hproj Hd. induction Hproj.
    - constructor. intros x Hc. inv Hc. rewrite FromList_nil in H0.
      eapply not_In_Empty_set. eassumption.
    - rewrite FromList_cons. eapply Disjoint_sym.
      eapply Union_Disjoint_l.
      + eapply Disjoint_Included_r_sym.
        eapply project_vars_free_set_Included; eassumption.
        eapply Disjoint_Singleton_r.
        eapply project_var_not_In_free_set; eassumption.
      + eapply Disjoint_sym. eapply IHHproj.
        eapply Disjoint_Included_l.
        eapply project_var_free_set_Included. eassumption.
        eassumption.
  Qed.

  Lemma project_var_get Scope Funs GFuns c genv Γ FVs S1 x x' C1 S2 rho1 rho2 y:
    project_var clo_tag Scope Funs GFuns c genv Γ FVs S1 x x' C1 S2 ->
    ctx_to_rho C1 rho1 rho2 ->
    ~ In _ S1 y ->
    M.get y rho1 = M.get y rho2.
  Proof.
    intros Hvar Hctx Hin. inv Hvar.
    - inv Hctx. reflexivity.
    - inv Hctx. inv H9.
      destruct (peq y x'); subst.
      contradiction.
      now rewrite M.gso.
    - inv Hctx. inv H11. inv H13.
      destruct (peq y x'); subst.
      contradiction. rewrite M.gso; eauto.
      destruct (peq y g_env); subst.
      exfalso. now inv H3; eauto.
      now rewrite M.gso; eauto.
    - inv Hctx; inv H12.
      destruct (peq y x'); subst.
      contradiction. inv H13.
      now rewrite M.gso.
  Qed.

  Lemma project_vars_get Scope Funs GFuns c genv Γ FVs S1 xs xs' C1 S2 rho1 rho2 y:
    project_vars clo_tag Scope Funs GFuns c genv Γ FVs S1 xs xs' C1 S2 ->
    ctx_to_rho C1 rho1 rho2 ->
    ~ In _ S1 y ->
    M.get y rho1 = M.get y rho2.
  Proof.
    revert Scope Funs Γ FVs S1 xs' C1 S2 rho1 rho2 y.
    induction xs; intros Scope Funs Γ FVs S1 xs' C1 S2 rho1 rho2 y Hproj Hctx Hnin.
    - inv Hproj. inv Hctx. reflexivity.
    - inv Hproj.
      edestruct ctx_to_rho_comp_ctx_l as [rho'' [Hctx1 Hctx2]]; eauto.
      rewrite <- comp_ctx_f_correct. reflexivity.
      eapply project_var_get in Hctx1; eauto.
      eapply IHxs in Hctx2; eauto.
      rewrite Hctx1, <- Hctx2. reflexivity.
      intros Hc. eapply Hnin.
      eapply project_var_free_set_Included; eassumption.
  Qed.

  Lemma project_var_get_list Scope Funs GFuns c genv Γ FVs S1 x x' C1 S2 rho1 rho2 ys :
    project_var clo_tag Scope Funs GFuns c genv Γ FVs S1 x x' C1 S2 ->
    ctx_to_rho C1 rho1 rho2 ->
    Disjoint _ S1 (FromList ys) ->
    get_list ys rho1 = get_list ys rho2.
  Proof.
    revert rho1 rho2; induction ys; intros rho1 rho2  Hproj Hctx Hnin.
    - reflexivity.
    - simpl.
      rewrite FromList_cons in Hnin. eapply Disjoint_sym in Hnin.
      erewrite project_var_get; eauto.
      erewrite IHys; eauto.
      eapply Disjoint_sym. eapply Disjoint_Union_r. eassumption.
      intros Hc. eapply Hnin. eauto.
  Qed.

  Lemma project_vars_get_list Scope Funs GFuns c genv Γ FVs S1 xs xs' C1 S2 rho1 rho2 ys :
    project_vars clo_tag Scope Funs GFuns c genv Γ FVs S1 xs xs' C1 S2 ->
    ctx_to_rho C1 rho1 rho2 ->
    Disjoint _ S1 (FromList ys) ->
    get_list ys rho1 = get_list ys rho2.
  Proof.
    revert rho1 rho2; induction ys; intros rho1 rho2  Hproj Hctx Hnin.
    - reflexivity.
    - simpl.
      rewrite FromList_cons in Hnin. eapply Disjoint_sym in Hnin.
      erewrite project_vars_get; eauto.
      erewrite IHys; eauto.
      eapply Disjoint_sym. eapply Disjoint_Union_r. eassumption.
      intros Hc. eapply Hnin. eauto.
  Qed.

  Lemma project_var_not_In Scope Funs GFuns c genv Γ FVs S x x' C S' :
    Disjoint _ S (Union var Scope
                        (Union var (Funs :|: GFuns)
                               (Union var (FromList FVs) (Singleton var Γ)))) ->

    project_var clo_tag Scope Funs GFuns c genv Γ FVs S x x' C S' ->
    ~ In _ S x.
  Proof.
    intros Hd  Hproj. inv Hproj; intros Hin; try now eapply Hd; eauto.
    eapply nthN_In in H2. eapply Hd. eauto.
  Qed.

  Lemma project_vars_Disjoint Scope Funs GFuns c genv Γ FVs S xs xs' C S' :
    Disjoint _ S (Union var Scope
                        (Union var (Funs :|: GFuns)
                               (Union var (FromList FVs) (Singleton var Γ)))) ->
    project_vars clo_tag Scope Funs GFuns c genv Γ FVs S xs xs' C S' ->
    Disjoint _ S (FromList xs).
  Proof.
    revert xs' C S S'; induction xs; intros xs' C S S' Hd Hproj.
    - rewrite FromList_nil. now eapply Disjoint_Empty_set_r.
    - inv Hproj. rewrite FromList_cons.
      eapply Union_Disjoint_r.
      eapply Disjoint_Singleton_r. eapply project_var_not_In; eauto.
      inv H9.
      + eapply IHxs; [| eassumption ]. eauto.
      + assert (Hd1 : Disjoint _ (Setminus var S (Singleton var y'))
                               (FromList xs))
          by (eapply IHxs; eauto with Ensembles_DB).
        eapply project_vars_In_Union in H13.
        eapply Disjoint_Included_r. eassumption.
        eauto 10 with Ensembles_DB.
      + assert (Hd1 : Disjoint _  (S \\ [set y'] \\ [set g_env])
                               (FromList xs))
          by (eapply IHxs; eauto with Ensembles_DB).
        eapply project_vars_In_Union in H13.
        eapply Disjoint_Included_r. eassumption.
        eauto 10 with Ensembles_DB.
      + assert (Hd1 : Disjoint _ (Setminus var S (Singleton var y'))
                               (FromList xs))
          by (eapply IHxs; eauto with Ensembles_DB).
        eapply project_vars_In_Union in H13.
        eapply Disjoint_Included_r. eassumption.
        eauto 10 with Ensembles_DB.
  Qed.

  (** Properties for context sizes *)

  Lemma project_var_sizeOf_ctx_exp (Scope Funs GFuns : Ensemble var)
        (c : ctor_tag) genv (Γ : var) (FVs : list var) (S : Ensemble var)
    (x x' : var) (C : exp_ctx) (S' : Ensemble var) :
    project_var clo_tag Scope Funs GFuns c genv Γ FVs S x x' C S' ->
    sizeOf_exp_ctx C <= 4.
  Proof.
    intros Hctx. inv Hctx; eauto.
  Qed.

  Lemma project_vars_sizeOf_ctx_exp (Scope Funs GFuns : Ensemble var)
    (c : ctor_tag) genv (Γ : var) (FVs : list var) (S : Ensemble var)
    (xs xs' : list var) (C : exp_ctx) (S' : Ensemble var)  :
    project_vars clo_tag Scope Funs GFuns c genv Γ FVs S xs xs' C S' ->
    sizeOf_exp_ctx C <= 4 * length xs.
  Proof.
    intros Hctx. induction Hctx; eauto.
    rewrite sizeOf_exp_ctx_comp_ctx. simpl.
    specialize (project_var_sizeOf_ctx_exp _ _ _ _ _ _ _ _ _ _ _ _ H).
    lia.
  Qed.

  Lemma Closure_conversion_fundefs_numOf_fundefs Funs (GFuns : Ensemble var) (σ : var -> var) (c : ctor_tag)
        (FVs : list var) (B1 B2 : fundefs) :
    Closure_conversion_fundefs clo_tag Funs GFuns c FVs B1 B2 ->
    numOf_fundefs B1 = numOf_fundefs B2.
  Proof.
    intros Hcc; induction Hcc; eauto; simpl. congruence.
  Qed.

  Lemma project_var_tag_inv Scope GFuns Funs c1 c2 genv Γ  S x x' C S' :
    project_var clo_tag Scope GFuns Funs c1 genv Γ [] S x  x' C S' ->
    project_var clo_tag Scope GFuns Funs c2 genv Γ [] S x  x' C S'.
  Proof.
    intros Hc; inv Hc; (try constructor; eauto).
    inv H2.
  Qed.

  Lemma project_vars_tag_inv Scope GFuns Funs c1 c2 genv Γ  S x x' C S' :
    project_vars clo_tag Scope GFuns Funs c1 genv Γ [] S x  x' C S' ->
    project_vars clo_tag Scope GFuns Funs c2 genv Γ [] S x  x' C S'.
  Proof.
    revert Scope GFuns Funs c1 c2 Γ  S x' C S'; induction x;
      intros Scope GFuns Funs c1 c2 Γ  S x' C S' Hvs; inv Hvs; try (constructor; eauto).
    econstructor. eapply project_var_tag_inv. eassumption.
    eapply IHx; eassumption.
  Qed.

  Lemma Closure_conversion_tag_inv Scope Funs GFuns c1 c2 genv Γ e e' C :
    Closure_conversion clo_tag Scope Funs GFuns c1 genv Γ [] e e' C ->
    Closure_conversion clo_tag Scope Funs GFuns c2 genv Γ [] e e' C.
  Proof.
    revert Scope Funs GFuns c1 c2 genv Γ e' C; induction e using exp_ind';
      intros Scope Funs GFuns c1 c2 genv Γ e' C Hcc; inv Hcc;
        try (econstructor; eauto; eapply project_vars_tag_inv; eassumption);
        try (econstructor; eauto; eapply project_var_tag_inv; eassumption).
    - econstructor; eauto.
      eapply project_var_tag_inv. eassumption. inv H12.
      constructor.
    - econstructor; eauto.
      eapply project_var_tag_inv. eassumption.
      inv H12. destruct H2 as [Heq [C' [e' [HeqC Hcc']]]].
      destruct y as [c2' e2]. simpl in *; subst.
      constructor; eauto.
      split; eauto. do 2 eexists; split; eauto. simpl. reflexivity.
      assert (Hcc1 : Closure_conversion clo_tag Scope Funs GFuns c2 genv Γ [] (Ecase v l) (Ecase x' l') C).
      { eapply IHe0. econstructor; eauto. }
      inv Hcc1. eassumption.
  Qed.



End Closure_conversion_util.
