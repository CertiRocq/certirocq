From Stdlib Require Import ZArith.ZArith Lists.List Strings.String micromega.Lia Arith
     Ensembles Relations.Relation_Definitions.
Require Import Common.AstCommon.
Require compcert.lib.Maps compcert.lib.Coqlib.
From Stdlib Require Import List Ensembles.
Import ListNotations.

Require Import LambdaBoxLocal.expression LambdaBoxLocal.fuel_sem.

(* From Stdlib Require Import Relations.Relation_Definitions. *)
(* From Stdlib Require Import Classes.Morphisms. *)
(* From Stdlib Require Import Classes.RelationClasses. *)

Require Import term cps_show eval ctx logical_relations
        List_util algebra alpha_conv functions Ensembles_util
        LambdaBoxLocal_to_LambdaANF LambdaANF.tactics identifiers term_util rename.

Require Import ExtLib.Data.Monads.OptionMonad ExtLib.Structures.Monads.

Import Monad.MonadNotation.

Open Scope monad_scope.

Section IP.

    Context (P : expression.exp -> Prop) (P0 : exps -> Prop) (P1 : efnlst -> Prop) (P2 : branches_e -> Prop).

    Context
      (H1 : forall n : N, P (Var_e n))
      (H2 : forall (n : name) (e : expression.exp), P e -> P (Lam_e n e))
      (H3: forall e : expression.exp, P e -> forall e0 : expression.exp, P e0 -> P (e $ e0))
      (H4 : forall (d : dcon) (e : exps), P0 e -> P (Con_e d e))
      (H5 : forall e : expression.exp, P e -> forall (pars : N) (b : branches_e), P2 b -> P (Match_e e pars b))
      (H6 : forall (n : name) (e : expression.exp), P e -> forall e0 : expression.exp, P e0 -> P (Let_e n e e0))
      (H7 : forall e : efnlst, P1 e -> forall n : N, P (Fix_e e n))
      (H9 : P Prf_e)
      (H10 : forall p, P (Prim_val_e p))
      (H11 : forall p : positive, P (Prim_e p))
      (H12 : P0 enil)
      (H13 : forall e : expression.exp, P e -> forall e0 : exps, P0 e0 -> P0 (econs e e0))
      (H14 : P1 eflnil)
      (H15 : forall (n : name) (e : expression.exp),
          (forall n' e', e = Lam_e n' e' ->  P e' -> forall e0 : efnlst, P1 e0 -> P1 (eflcons n e e0)) /\
          (~ isLambda e -> P e -> forall e0 : efnlst, P1 e0 -> P1 (eflcons n e e0)))
      (H16 : P2 brnil_e)
      (H17 : forall (d : dcon) (p : N * list name) (e : expression.exp), P e -> forall b : branches_e, P2 b -> P2 (brcons_e d p e b)).

    Lemma exp_ind_alt2 : forall e, P e
    with exps_ind_alt2 : forall es, P0 es
    with efnlst_ind_alt2 : forall fns, P1 fns
    with branches_ind_alt2 : forall brs, P2 brs.
    Proof.
      - intros. destruct e.
        + eapply H1.
        + eapply H2. eapply exp_ind_alt2.
        + eapply H3; eapply exp_ind_alt2.
        + eapply H4. eapply exps_ind_alt2.
        + eapply H5. eapply exp_ind_alt2. eapply branches_ind_alt2.
        + eapply H6; eapply exp_ind_alt2.
        + eapply H7. eapply efnlst_ind_alt2.
        + eapply H9.
        + eapply H10.
        + eapply H11.
      - intros. destruct es.
        + eapply H12.
        + eapply H13. eapply exp_ind_alt2.
          eapply exps_ind_alt2.
      - intros. destruct fns.
        + eapply H14.
        + assert (Hdec : isLambda e \/ ~ isLambda e).
          { destruct e; eauto. now left. }
          destruct Hdec.
          * destruct e; try contradiction.
            edestruct H15.
            eapply H0. reflexivity.
            eapply exp_ind_alt2; eauto.
            eapply efnlst_ind_alt2.
          * edestruct H15.
            eapply H8. eassumption.
            eapply exp_ind_alt2; eauto.
            eapply efnlst_ind_alt2.
      - intros brs. destruct brs.
        + eapply H16.
        + eapply H17.
          eapply exp_ind_alt2.
          eapply branches_ind_alt2.
    Qed.


    Lemma exp_ind_alt_2 :
      (forall e : expression.exp, P e) /\
      (forall e : exps, P0 e) /\
      (forall e : efnlst, P1 e) /\
      (forall b : branches_e, P2 b).
    Proof.
      repeat split.
      eapply exp_ind_alt2.
      eapply exps_ind_alt2.
      eapply efnlst_ind_alt2.
      eapply branches_ind_alt2.
    Qed.

  End IP.

Section SUBSETS.

  (** ** Subset lemmas *)
  Context (func_tag kon_tag default_tag : positive) (cnstrs : conId_map).


  Lemma Setminus_Included_preserv_alt:
    forall {A: Type} (S1 S2 S3: Ensemble A),
      S1 \subset S2 \\ S3 -> S1 \subset S2.
  Proof.
    intros A S1 S2 S3 H. unfold Included in *.
    intros x Hin. eapply H in Hin.
    unfold Setminus in Hin. unfold In in *. destruct Hin. eassumption.
  Qed.

  Definition cps_cvt_exp_subset_stmt :=
    forall e e' k1 vars1 S1 S2,
      cps_cvt_rel func_tag kon_tag default_tag S1 e vars1 k1 cnstrs S2 e' ->
      S2 \subset S1.

  Definition cps_cvt_exps_subset_stmt :=
    forall e e' k1 vars1 vs ks S1 S2,
      cps_cvt_rel_exps func_tag kon_tag default_tag S1 e vars1 k1 vs ks cnstrs S2 e' ->
      S2 \subset S1.

  Definition cps_cvt_efnlst_subset_stmt :=
    forall efns S1 vars1 nlst1 S2 fdefs1,
      cps_cvt_rel_efnlst func_tag kon_tag default_tag S1 efns vars1 nlst1 cnstrs S2 fdefs1 ->
      S2 \subset S1.

  Definition cps_cvt_branches_subset_stmt :=
    forall bs S1 vars1 k1 x1 S2 bs1,
      cps_cvt_rel_branches func_tag kon_tag default_tag S1 bs vars1 k1 x1 cnstrs S2 bs1 ->
      S2 \subset S1.


  Definition cps_cvt_rel_subset_stmt :=
    (cps_cvt_exp_subset_stmt) /\
    (cps_cvt_exps_subset_stmt) /\
    (cps_cvt_efnlst_subset_stmt) /\
    (cps_cvt_branches_subset_stmt).

  Lemma cps_cvt_rel_subset : cps_cvt_rel_subset_stmt.
  Proof.
    eapply exp_ind_alt_2.
    - (* Var_e *)
      intros n e' k1 vars1 S1 S2 Hrel.
      inv Hrel. eapply Included_refl.

    - (* Lam_e *)
      intros na e IH e' k1 vars1 S1 S2 Hrel.
      inv Hrel. eapply IH in H10.
      eapply Included_trans. eassumption. sets.

    - (* App_e *)
      intros e1 IHe1 e2 IHe2 e' k1 vars1 S1 S2 Hrel.
      inv Hrel. eapply IHe1 in H6. eapply IHe2 in H12.
      eapply Included_trans. eassumption. sets.
      eapply Included_trans. eassumption. sets.

    - (* Con_e *)
      intros dc es IH e' k1 vars1 S1 S2 Hrel.
      inv Hrel. eapply IH in H13.
      eapply Included_trans. eassumption. sets.

    - (* Match_e *)
      intros e IHe pars bs IHbs e' k1 vars1 S1 S2 Hrel.
      inv Hrel. eapply IHe in H10. eapply IHbs in H11.
      eapply Setminus_Included_preserv_alt in H10.
      eapply Setminus_Included_preserv_alt in H10.
      eapply Included_trans; eassumption.

    - (* Let_e *)
      intros na e1 IHe1 e2 IHe2 e' k1 vars1 S1 S2 Hrel.
      inv Hrel. eapply IHe1 in H11. eapply IHe2 in H10.
      eapply Setminus_Included_preserv_alt in H10.
      eapply Setminus_Included_preserv_alt in H10.
      eapply Included_trans; eassumption.

    - (* Fix_e *)
      intros efns IHefns n e' k1 vars1 S1 S2 Hrel.
      inv Hrel. eapply IHefns in H5.
      eapply Setminus_Included_preserv_alt in H5. eassumption.

    - (* Prf_e *)
      intros e' k1 vars1 S1 S2 Hrel. inv Hrel.
      eapply Setminus_Included.
    - (* Prim_val_e *)
      intros p e' k1 vars1 S1 S2 Hrel. inv Hrel. now eapply Setminus_Included_preserv_alt.

    - (* Prim_e *)
      intros p e' k1 vars1 S1 S2 Hrel. inv Hrel.

    - (* enil *)
      unfold cps_cvt_exps_subset_stmt.
      intros e' k1 vars vs ks S1 S2 Hrel. inv Hrel. eapply Included_refl.

    - (* econs *)
      intros e IHe es IHes e' k1 vars1 vs ks S1 S2 Hrel.
      inv Hrel. eapply IHe in H2. eapply IHes in H10.
      eapply Included_trans; eassumption.

    - (* eflnil *)
      intros S1 vars1 nlst1 S2 fdefs1 Hrel. inv Hrel. eapply Included_refl.

    - (* eflcons *)
      split.
      + intros na' e' Hlam IHe' efns IHefns S1 vars1 nlst1 S2 fdefs1 Hrel.
        inv Hrel. inv H0. eapply IHe' in H10. eapply IHefns in H11.
        eapply Included_trans. eassumption. sets.
        eapply Included_trans. eassumption. sets.
      + intros Hnot IHe efns IHefns S1 vars1 nlst1 S2 fdefs1 Hrel.
        inv Hrel. unfold isLambda in Hnot. contradiction.

    - (* brnil *)
      intros S1 vars1 k1 x1 S2 bs1 Hrel. inv Hrel. eapply Included_refl.

    - (* brcons *)
      intros dc p e IHe bs IHbs S1 vars1 k1 x1 S2 bs1 Hrel.
      inv Hrel. eapply IHe in H16. eapply IHbs in H15.
      eapply Setminus_Included_preserv_alt in H16.
      eapply Included_trans; eassumption.
  Qed.


  Corollary cps_cvt_exp_subset :
    cps_cvt_exp_subset_stmt.
  Proof. eapply (proj1 cps_cvt_rel_subset). Qed.

  Corollary cps_cvt_exps_subset :
    cps_cvt_exps_subset_stmt.
  Proof. eapply (proj1 (proj2 cps_cvt_rel_subset)). Qed.

  Corollary cps_cvt_efnlst_subset :
    cps_cvt_efnlst_subset_stmt.
  Proof. eapply (proj1 (proj2 (proj2 cps_cvt_rel_subset))). Qed.

  Corollary cps_cvt_branches_subset :
    cps_cvt_branches_subset_stmt.
  Proof. eapply (proj2 (proj2 (proj2 cps_cvt_rel_subset))). Qed.


End SUBSETS.


Section Post.

  Context {fuel : Type} {Hfuel : @fuel_resource fuel} {trace : Type}
          {Htrace : @trace_resource trace}.

    Context (P1 : PostT) (* Local *)
            (PG : PostGT) (* Global *)
            (cnstrs : conId_map)
            (cenv : ctor_env)
            (Hprops : Post_properties cenv P1 P1 PG)
            (HpropsG : Post_properties cenv PG PG PG)
            (Hincl : inclusion _ (comp P1 P1) P1)
            (HinclG : inclusion _ P1 PG)
            (pr_env : M.t (kername * string * nat)).

    Context (func_tag kon_tag default_tag default_itag : positive).

    Definition cps_cvt_rel := cps_cvt_rel func_tag kon_tag default_tag.
    Definition cps_cvt_rel_exps := cps_cvt_rel_exps func_tag kon_tag default_tag.
    Definition cps_cvt_rel_efnlst := cps_cvt_rel_efnlst func_tag kon_tag default_tag.
    Definition cps_cvt_rel_branches := cps_cvt_rel_branches func_tag kon_tag default_tag.


    Opaque preord_exp'.

    Lemma app_cons {A} (l1 l2 : list A) a :
      l1 ++ a :: l2 =  (l1 ++ [ a ]) ++ l2.
    Proof.
      simpl. rewrite <- app_assoc. reflexivity.
    Qed.


    Lemma ctx_bind_proj_alpha_equiv_gen k S f rho1 rho2 x1 x2 ctag proj_vars1 vars1 proj_vars2 vars2 e1 e2 n :
      preord_var_env cenv PG k rho1 rho2 x1 x2 ->

      preord_env_P_inj cenv PG (S :|: FromList vars1) k (f <{ vars1 ~> vars2 }>) rho1 rho2 ->

      List.length proj_vars1 = List.length proj_vars2 ->
      Datatypes.length vars1 = Datatypes.length vars2 ->

      NoDup proj_vars1 ->
      NoDup proj_vars2 ->

      Disjoint _ (FromList proj_vars1) (FromList vars1 :|: [set x1] :|: S) ->
      Disjoint _ (FromList proj_vars2) (FromList vars2 :|: [set x2] :|: image f S) ->

      (forall rho1' rho2' m,
          (m <= k)%nat ->
          preord_env_P_inj cenv PG (S :|: FromList (vars1 ++ proj_vars1)) m (f <{ vars1 ++ proj_vars1 ~> vars2 ++ proj_vars2 }>) rho1' rho2' ->
          preord_exp cenv P1 PG m (e1, rho1') (e2, rho2')) ->

      preord_exp cenv P1 PG k
                 (ctx_bind_proj ctag x1 proj_vars1 n |[ e1 ]|, rho1)
                 (ctx_bind_proj ctag x2 proj_vars2 n |[ e2 ]|, rho2).
    Proof.
      revert k S f rho1 rho2 x1 x2 ctag proj_vars2 vars1 vars2 e1 e2 n.
      induction proj_vars1;
        intros k S f rho1 rho2 x1 x2 ctag proj_vars2 vars1 vars2 e1 e2 n Hvar Henv Hlen Hlen' Hnd1 Hnd2 Hdis1 Hdis2 Hexp;
        destruct proj_vars2; simpl in *; try congruence.
      - eapply Hexp. lia. repeat normalize_sets. rewrite !app_nil_r. eauto.
      - simpl. inv Hnd1; inv Hnd2.
        eapply preord_exp_proj_compat.
        + eapply Hprops.
        + eapply Hprops.
        + eassumption.
        + repeat normalize_sets. intros. eapply IHproj_vars1 with (vars1 := vars1 ++ [ a ]) (vars2 := vars2 ++ [ v ]) (S := S).
          * eapply preord_var_env_extend_neq.
            eapply preord_var_env_monotonic. eassumption. lia.

            intros Hc1; subst. eapply Hdis1. now constructor; eauto.

            intros Hc2; subst. eapply Hdis2. now constructor; eauto.


          * rewrite !extend_lst_app; eauto. simpl. rewrite extend_extend_lst_commut with (x := a) (y := v); eauto.
            eapply preord_env_P_inj_set_alt; eauto.
            eapply preord_env_P_inj_antimon.
            eapply preord_env_P_inj_monotonic; [ | eassumption ].
            lia. repeat normalize_sets. now sets.

            -- intros Hc. eapply image_extend_lst_Included in Hc; eauto.
               inv Hc. repeat normalize_sets. eapply Hdis2. constructor. now left.
               right. eapply image_monotonic; eauto. sets.

               now eapply Hdis2; sets.


            -- intros Hc. eapply Hdis1; sets.

            -- intros Hc. eapply Hdis2; sets.

          * congruence.

          * rewrite !length_app. simpl. congruence.

          * congruence.
          * eassumption.
          * repeat normalize_sets. clear Hdis2.
            rewrite (Union_commut _ [set a]). rewrite <- !Union_assoc.
            eapply Union_Disjoint_r.

            eapply Disjoint_Singleton_r. eassumption.
            eapply Disjoint_Included; [ | | eapply Hdis1 ]; sets.

          * repeat normalize_sets. clear Hdis1.
            rewrite (Union_commut _ [set v]). rewrite <- !Union_assoc.
            eapply Union_Disjoint_r.

            eapply Disjoint_Singleton_r. eassumption.
            eapply Disjoint_Included; [ | | eapply Hdis2 ]; sets.

          * intros.
            eapply preord_exp_monotonic. eapply Hexp.
            2:{ rewrite !(app_cons vars1 proj_vars1).
                rewrite !(app_cons vars2 proj_vars2). eassumption. }

            lia.
            lia.
    Qed.



    Corollary ctx_bind_proj_alpha_equiv k S f rho1 rho2 x1 x2 ctag proj_vars1 proj_vars2 e1 e2 n :
      preord_var_env cenv PG k rho1 rho2 x1 x2 ->

      preord_env_P_inj cenv PG S k f rho1 rho2 ->

      List.length proj_vars1 = List.length proj_vars2 ->

      NoDup proj_vars1 ->
      NoDup proj_vars2 ->

      Disjoint _ (FromList proj_vars1) (x1 |: S) ->
      Disjoint _ (FromList proj_vars2) (x2 |: image f S) ->

      (forall rho1' rho2' m,
          (m <= k)%nat ->
          preord_env_P_inj cenv PG (S :|: FromList proj_vars1) m (f <{ proj_vars1 ~> proj_vars2 }>) rho1' rho2' ->
          preord_exp cenv P1 PG m (e1, rho1') (e2, rho2')) ->

      preord_exp cenv P1 PG k
                 (ctx_bind_proj ctag x1 proj_vars1 n |[ e1 ]|, rho1)
                 (ctx_bind_proj ctag x2 proj_vars2 n |[ e2 ]|, rho2).
    Proof.
      intros.
      eapply ctx_bind_proj_alpha_equiv_gen with (vars1 := []) (vars2 := []); try eassumption; simpl; repeat normalize_sets.
      eassumption.
      reflexivity.
      sets.
      sets.
    Qed.


    Lemma cps_cvt_rel_branches_ctor_tag S1 S2 S3 S4 bs vars1 vars2 k1 k2 x1 x2 bs1 bs2 :
      cps_cvt_rel_branches S1 bs vars1 k1 x1 cnstrs S2 bs1 ->
      cps_cvt_rel_branches S3 bs vars2 k2 x2 cnstrs S4 bs2 ->
      Forall2 (fun p p' : ctor_tag * exp => fst p = fst p') bs1 bs2.
    Proof.
      revert S1 S2 S3 S4 vars1 vars2 k1 k2 x1 x2 bs1 bs2.
      induction bs; intros S1 S2 S3 S4 vars1 vars2 k1 k2 x1 x2 bs1 bs2 Hrel1 Hrel2.

      inv Hrel1; inv Hrel2; eauto.

      inv Hrel1; inv Hrel2; eauto.
    Qed.

    Lemma cps_cvt_rel_efnlst_exists S1 efns vars1 nlst1 S2 B1 f1 m :
      cps_cvt_rel_efnlst S1 efns vars1 nlst1 cnstrs S2 B1 ->
      nth_error (all_fun_name B1) m = Some f1 ->
      NoDup (all_fun_name B1) ->
      exists k1 x1 na e1 e1' S1' S2',
        enthopt m efns = Some (Lam_e na e1) /\
        find_def f1 B1 = Some (func_tag, [k1; x1], e1') /\
        x1 \in S1 /\
               k1 \in S1 \\ [set x1] /\
                      S1' \subset S1 /\
                      cps_cvt_rel (S1' \\ [set x1] \\ [set k1]) e1 (x1 :: vars1) k1 cnstrs S2' e1'.
    Proof.
      intros Hrel. revert f1 m. induction Hrel; intros.
      - inv H. destruct m; inv H2.
      - simpl in H2. destruct m.
        + inv H2. do 7 eexists. split; [ | split; [ | split; [ | split; [ | split ]]]].
          * reflexivity.
          * simpl in *. rewrite Coqlib.peq_true. reflexivity.
          * eassumption.
          * eassumption.
          * reflexivity.
          * eassumption.
        + edestruct IHHrel; eauto. inv H3. eassumption. destructAll.
          do 7 eexists. split; [ | split; [ | split; [ | split; [ | split ]]]]; [ | | | | |  eassumption ].
          * eassumption.
          * simpl. rewrite Coqlib.peq_false. eassumption.
            inv H3. simpl in H2. intros Hc; subst. eapply H12.
            eapply nth_error_In. eassumption.
          * eapply cps_cvt_exp_subset in H1. eapply H1. eassumption.
          * inv H7. constructor; eauto.
            eapply cps_cvt_exp_subset in H1. eapply H1. eassumption.
          * eapply cps_cvt_exp_subset in H1.
            eapply Included_trans; eauto.
            eapply Included_trans; eauto. now sets.
    Qed.



    (** ** Alpha-equivalence statements *)

     Definition cps_cvt_exp_alpha_equiv k :=
       forall e e1 e2 m k1 k2 vars1 vars2 rho1 rho2 S1 S2 S3 S4,
         (m <= k)%nat ->
        cps_cvt_rel S1 e vars1 k1 cnstrs S2 e1 ->
        cps_cvt_rel S3 e vars2 k2 cnstrs S4 e2 ->
        NoDup vars1 -> (* TODO is this needed? *)
        ~(k1 \in (FromList vars1)) ->
        List.length vars1 = List.length vars2 ->

        Disjoint _ (k1 |: FromList vars1) S1 ->
        Disjoint _ (k2 |: FromList vars2) S3 ->

        preord_env_P_inj cenv PG (k1 |: FromList vars1) m
                         (id { k1 ~> k2 } <{ vars1 ~> vars2 }>) rho1 rho2 ->
        preord_exp cenv P1 PG m (e1, rho1) (e2, rho2).

     Definition cps_cvt_exps_alpha_equiv k :=
      forall es es1 es2 m k1 k2 vars1 vars2 xs1 xs2 ks1 ks2 ys1 ys2 rho1 rho2
             e_cont1 e_cont2 S1 S2 S3 S4,
        (m <= k)%nat ->
        cps_cvt_rel_exps S1 es vars1 e_cont1 xs1 ks1 cnstrs S2 es1 ->
        cps_cvt_rel_exps S3 es vars2 e_cont2 xs2 ks2 cnstrs S4 es2 ->

        NoDup vars1 ->
        NoDup xs1 ->
        NoDup xs2 ->
        NoDup ys1 ->
        NoDup ks1 ->


        (* TODO some of these might be redundant *)

        ~(k1 \in (FromList vars1 :|: FromList xs1 :|: FromList ys1 :|: FromList ks1)) ->
        Disjoint _ (FromList vars1) (FromList xs1 :|: FromList ys1 :|: FromList ks1) ->

        List.length vars1 = List.length vars2 ->
        List.length xs1 = List.length xs2 ->
        List.length ys1 = List.length ys2 ->

        Disjoint _ (k1 |: FromList vars1 :|: FromList xs1 :|: FromList ys1 :|: FromList ks1) S1 ->
        Disjoint _ (k2 |: FromList vars2 :|: FromList xs2 :|: FromList ys2 :|: FromList ks2) S3 ->
        Disjoint _ (FromList xs1 :|: FromList ks1) (FromList ys1) ->
        Disjoint _ (FromList xs2 :|: FromList ks2) (k2 |: FromList vars2 :|: FromList ys2) ->
        Disjoint _ (FromList xs1) (FromList ks1) ->
        Disjoint _ (FromList xs2) (FromList ks2) ->


        (forall rho1 rho2 m,
            preord_env_P_inj cenv PG (k1 |: FromList (ys1 ++ xs1)) m
                             (id { k1 ~> k2 } <{ ys1 ++ xs1 ~> ys2 ++ xs2 }>)
                             rho1 rho2 ->
            preord_exp cenv P1 PG m (e_cont1, rho1) (e_cont2, rho2)) ->

        preord_env_P_inj cenv PG (k1 |: FromList vars1 :|: FromList ys1 ) m
                         (id { k1 ~> k2 } <{ vars1 ~> vars2 }> <{ ys1 ~> ys2 }>)
                         rho1 rho2 ->

        preord_exp cenv P1 PG m (es1, rho1) (es2, rho2).


    Definition cps_cvt_efnlst_alpha_equiv k :=
      forall efns fdefs1 fdefs2 m k1 k2 vars1 vars2 vars1' vars2' nlst1 nlst2 rho1 rho2
             S1 S2 S3 S4,
        (m <= k)%nat ->
        cps_cvt_rel_efnlst S1 efns vars1 nlst1 cnstrs S2 fdefs1 ->
        cps_cvt_rel_efnlst S3 efns vars2 nlst2 cnstrs S4 fdefs2 ->

        vars1 = List.rev nlst1 ++ vars1' ->
        vars2 = List.rev nlst2 ++ vars2' ->

        NoDup vars1 ->
        NoDup (all_fun_name fdefs1) ->
        NoDup (all_fun_name fdefs2) ->

        List.length vars1' = List.length vars2' ->
        List.length (all_fun_name fdefs1) = List.length (all_fun_name fdefs2) ->

        Disjoint _ (k1 |: FromList vars1) S1 ->
        Disjoint _ (k2 |: FromList vars2) S3 ->

        Disjoint var (k2 |: FromList vars2') (name_in_fundefs fdefs2) ->

        preord_env_P_inj cenv PG (k1 |: FromList vars1') m
                         (id {k1 ~> k2 } <{ vars1' ~> vars2' }>) rho1 rho2 ->
        preord_env_P_inj cenv PG (k1 |: (FromList vars1 :|: FromList nlst1)) m
                         (id {k1 ~> k2 } <{ vars1' ~> vars2' }> <{ rev (all_fun_name fdefs1) ~> rev (all_fun_name fdefs2) }>)
                         (def_funs fdefs1 fdefs1 rho1 rho1)
                         (def_funs fdefs2 fdefs2 rho2 rho2).

        (* preord_val cenv PG k (Vfun rho1 fdefs1 f1) (Vfun rho2 fdefs2 f2). *)


    Definition cps_cvt_branches_alpha_equiv (k : nat) :=
      forall bs bs1 bs2 m k1 k2 vars1 vars2 x1 x2 rho1 rho2
             S1 S2 S3 S4,
        (m <= k)%nat ->
        cps_cvt_rel_branches S1 bs vars1 k1 x1 cnstrs S2 bs1 ->
        cps_cvt_rel_branches S3 bs vars2 k2 x2 cnstrs S4 bs2 ->
        NoDup vars1 ->
        ~(k1 \in (FromList vars1)) ->
        List.length vars1 = List.length vars2 ->

        Disjoint _ (k1 |: [set x1] :|: FromList vars1) S1 ->
        Disjoint _ (k2 |: [set x2] :|: FromList vars2) S3 ->

        preord_env_P_inj cenv PG (k1 |: FromList vars1) m
                         (id {k1 ~> k2 } <{ vars1 ~> vars2 }>) rho1 rho2 ->
        preord_var_env cenv PG m rho1 rho2 x1 x2 ->
        preord_exp cenv P1 PG m (Ecase x1 bs1, rho1)  (Ecase x2 bs2, rho2).


    Definition cps_cvt_alpha_equiv_statement k :=
      cps_cvt_exp_alpha_equiv k /\
      cps_cvt_exps_alpha_equiv k /\
      cps_cvt_efnlst_alpha_equiv k /\
      cps_cvt_branches_alpha_equiv k.

    Lemma cps_cvt_rel_efnlst_name_in_fundes S1 na vars nlst S2 B :
      cps_cvt_rel_efnlst S1 na vars nlst cnstrs S2 B ->
      name_in_fundefs B <--> FromList nlst.
    Proof.
      intros H. induction H.
      - normalize_sets. simpl. sets.
      - simpl. normalize_sets. sets.
    Qed.


    Lemma cps_cvt_rel_efnlst_all_fun_name S1 na vars nlst S2 B :
      cps_cvt_rel_efnlst S1 na vars nlst cnstrs S2 B ->
      all_fun_name B = nlst.
    Proof.
      intros H. induction H.
      - reflexivity.
      - simpl. congruence.
    Qed.

    Fixpoint in_efnlist (n : name) (e : expression.exp) (efns : efnlst) :=
      match efns with
      | eflnil => False
      | eflcons n' e' efns =>
        n = n' /\ e = e' \/ in_efnlist n e efns
      end.


    Lemma extend_lst_nth_error {A} f l (l' : list A) x n :
      NoDup l ->
      nth_error l n = Some x ->
      List.length l = List.length l' ->
      exists x', f <{ l ~> l' }> x = x' /\ nth_error l' n = Some x'.
    Proof.
      revert n l'; induction l; intros n l' Hnd Hnin Hlen; simpl; eauto.
      - destruct n; inv Hnin.
      - destruct l'; try discriminate. inv Hlen.
        destruct n; simpl in Hnin.
        + inv Hnin. rewrite extend_gss.
          eexists; split; eauto.
        + inv Hnd. rewrite extend_gso; eauto. edestruct IHl as [x' [Heq HIn]]; eauto.
          intros Hc. subst. eapply H2. eapply nth_error_In. eassumption.
    Qed.

    Lemma preord_env_P_inj_def_funs_Vfun S k f B1 B2 B1' B2' rho1 rho2 :
      preord_env_P_inj cenv PG (S \\ name_in_fundefs B1) k f rho1 rho2 ->

      List.length (all_fun_name B1) = List.length (all_fun_name B2) ->
      NoDup (all_fun_name B1) ->
      Disjoint _ (image f (S \\ name_in_fundefs B1)) (name_in_fundefs B2) ->

      (forall n f1 f2,
          nth_error (all_fun_name B1) n = Some f1 ->
          nth_error (all_fun_name B2) n = Some f2 ->
          preord_val cenv PG k (Vfun rho1 B1' f1) (Vfun rho2 B2' f2)) ->

      preord_env_P_inj cenv PG S k (f <{ all_fun_name B1 ~> all_fun_name B2 }>) (def_funs B1' B1 rho1 rho1) (def_funs B2' B2 rho2 rho2).
    Proof.
      intros Henv Hlen Hnd Hdis Hrel x Hin v Hget.
      destruct (Decidable_name_in_fundefs B1). destruct (Dec x).

      - edestruct In_nth_error. eapply Same_set_all_fun_name. eassumption.
        edestruct (@extend_lst_nth_error var); try eassumption. destructAll.

        eexists. rewrite def_funs_eq in *; eauto. split. reflexivity.
        inv Hget. eapply Hrel.
        eassumption. eassumption.

        eapply Same_set_all_fun_name. eapply nth_error_In. eassumption.

      - rewrite extend_lst_gso. rewrite def_funs_neq in *; eauto.

        eapply Henv. now constructor. eassumption.

        intros Hc. eapply Hdis. constructor; eauto.
        eapply In_image. now constructor; auto.

        rewrite <- Same_set_all_fun_name. eassumption.
    Qed.

    (* TODO move *)

    Lemma exp_ind_alt : forall (P : expression.exp -> Prop) (P0 : exps -> Prop) (P1 : efnlst -> Prop) (P2 : branches_e -> Prop),
        (forall n : N, P (Var_e n)) ->
        (forall (n : name) (e : expression.exp), P e -> P (Lam_e n e)) ->
        (forall e : expression.exp, P e -> forall e0 : expression.exp, P e0 -> P (e $ e0)) ->
        (forall (d : dcon) (e : exps), P0 e -> P (Con_e d e)) ->
        (forall e : expression.exp, P e -> forall (pars : N) (b : branches_e), P2 b -> P (Match_e e pars b)) ->
        (forall (n : name) (e : expression.exp), P e -> forall e0 : expression.exp, P e0 -> P (Let_e n e e0)) ->
        (forall e : efnlst, P1 e -> forall n : N, P (Fix_e e n)) ->
        P Prf_e ->
        (forall p, P (Prim_val_e p)) ->
        (forall p : positive, P (Prim_e p)) ->
        P0 enil ->
        (forall e : expression.exp, P e -> forall e0 : exps, P0 e0 -> P0 (econs e e0)) ->
        P1 eflnil ->
        (forall (n : name) (e : expression.exp) (efns : efnlst), in_efnlist n e efns -> P e -> P1 efns) ->
        P2 brnil_e ->
        (forall (d : dcon) (p : N * list name) (e : expression.exp),
            P e -> forall b : branches_e, P2 b -> P2 (brcons_e d p e b)) ->
        (forall e : expression.exp, P e) /\
        (forall e : exps, P0 e) /\
        (forall e : efnlst, P1 e) /\ (forall b : branches_e, P2 b).
    Proof.
      intros. eapply my_exp_ind; eauto.
      intros. eapply H12. now left. eassumption.
    Qed.


    Lemma FromList_rev {A} (l : list A) :
      FromList (List.rev l) <--> FromList l.
    Proof.
      induction l.
      - reflexivity.
      - simpl. repeat normalize_sets. sets.
    Qed.

    Lemma extend_lst_rev A (f : positive -> A) xs ys :
      NoDup xs ->
      NoDup ys ->
      List.length xs = List.length ys ->
      f_eq (f <{ rev xs ~> rev ys }>) (f <{ xs ~> ys }>).
    Proof.
      revert f ys. induction xs; intros f ys Hnd1 Hnd2 Hlen; simpl.
      - reflexivity.
      - inv Hnd1. destruct ys; simpl in *. congruence.
        inv Hnd2.
        simpl. rewrite extend_lst_app. simpl.
        rewrite extend_extend_lst_commut.
        rewrite IHxs; eauto. reflexivity.
        intros Hc. now eapply in_rev in Hc; eauto.
        intros Hc. now eapply in_rev in Hc; eauto.
        rewrite !length_rev. congruence.
        rewrite !length_rev. congruence.
    Qed.

    Ltac inv_setminus :=
      match goal with
      | [ H : In _ (?S \\ ?Q) _ |- _ ] => inv H; try inv_setminus
      end.


    Lemma cps_cvt_rel_exps_len S1 es vars1 k1 xs1 ks1 S2 es1 :
      cps_cvt_rel_exps S1 es vars1 k1 xs1 ks1 cnstrs S2 es1 ->
      List.length xs1 = N.to_nat (exps_length es).
    Proof.
      intros Hrel. induction Hrel; eauto.
      - simpl exps_length.
        destruct (exps_length es) in *.
        simpl; lia.
        simpl. rewrite IHHrel.
        destruct p; lia.
    Qed.

    Lemma cps_cvt_rel_exps_len_ks S1 es vars1 k1 xs1 ks1 S2 es1 :
      cps_cvt_rel_exps S1 es vars1 k1 xs1 ks1 cnstrs S2 es1 ->
      List.length ks1 = N.to_nat (exps_length es).
    Proof.
      intros Hrel. induction Hrel; eauto.
      - simpl exps_length.
        destruct (exps_length es) in *.
        simpl; lia.
        simpl. rewrite IHHrel.
        destruct p; lia.
    Qed.

    Lemma cps_cvt_alpha_equiv :
      forall k, cps_cvt_alpha_equiv_statement k.
    Proof.
      induction k using lt_wf_rec.
      eapply exp_ind_alt.
      - (* Var_e *)
        intros n e1 e2 m k1 k2 vars1 vars2 rho1 rho2
               S1 S2 S3 S4 Hlt He1 He2 Hdup Hnot Hlen Hdis1 Hdis2 Henv.
        inv He1. inv He2.
        eapply preord_exp_app_compat.
        + eapply Hprops. (* invariants *)
        + eapply Hprops. (* invariants *)
        + assert (Heq: k2 = ((id {k1 ~> k2}) <{ vars1 ~> vars2 }>) k1).
          { rewrite extend_lst_gso.
            rewrite extend_gss. reflexivity.
            eassumption. }
          rewrite Heq.
          eapply Henv. left. reflexivity.
        + econstructor; [ | now econstructor ].
          * assert (Heq: ((id {k1 ~> k2}) <{ vars1 ~> vars2 }>) v = v0).
            { eapply extend_lst_get_nth_error; eauto. }
            rewrite <- Heq. eapply Henv. right.
            eapply nth_FromList. eassumption.

      - (* Lam_e *)
        intros na e IH e1 e2 m k1 k2 vars1 vars2 rho1 rho2 S1 S2 S3 S4
               Hlt He1 He2 Hdup Hnot Hlen Hdis1 Hdis2 Henv.
        simpl in He1, He2. inv He1; inv He2.
        eapply preord_exp_fun_compat.
        + eapply Hprops. (* invariants *)
        + eapply Hprops. (* invariants *)
        + { eapply preord_exp_monotonic.
            simpl. eapply preord_exp_app_compat.
            - eapply Hprops. (* invariants *)
            - eapply Hprops. (* invariants *)
            - assert (Heq: k2 = ((id {k1 ~> k2}) <{ vars1 ~> vars2 }>) k1).
              { rewrite extend_lst_gso. rewrite extend_gss. reflexivity.
                eassumption. }
              rewrite Heq.
              inv H3; inv H5. inv H6; inv H8.

              eapply preord_env_P_inj_set_not_In_P_l.
              eapply preord_env_P_inj_set_not_In_P_r.
              eassumption.

              3:{ now left. }
              2:{ intros Hc. eapply Hdis1. constructor; [ | eapply H0 ]. eassumption. }

              intros Him. eapply image_extend_lst_Included in Him; eauto.
              rewrite image_extend_In_S in Him; eauto.

              assert (Hseq : k1 |: FromList vars1 \\ FromList vars1 \\ [set k1] <--> Empty_set _) by sets.

              rewrite Hseq, image_Empty_set in Him. repeat normalize_sets.
              now eapply Hdis2; sets.

              rewrite Setminus_Union_distr. left. rewrite Setminus_Disjoint. reflexivity.
              sets.

            - econstructor. 2: { econstructor. }
              simpl. unfold preord_var_env.
              intros v5 Hset.
              rewrite M.gss in Hset. inv Hset.
              eexists. split.
              rewrite M.gss. reflexivity. eapply preord_val_fun.
              simpl. rewrite Coqlib.peq_true. reflexivity.
              simpl. rewrite Coqlib.peq_true. reflexivity.

              intros. destruct vs1 as [ | ? [ | ? [ | ]] ]; simpl in *; try congruence.
              destruct vs2 as [ | ? [ | ? [ | ]] ]; simpl in *; try congruence.
              inv H1. eexists. split. reflexivity.

              intros Hlt' Hall.

              eapply preord_exp_post_monotonic. now eapply HinclG.
              eapply preord_exp_monotonic.
              edestruct (H j) as [ Hexp _ ]. lia.
              eapply Hexp.
              + reflexivity.
              + eassumption.
              + eassumption.
              + constructor. intros Hc. eapply Hdis1. now sets. eassumption.
              + repeat normalize_sets. inv H5. intros Hc. inv Hc.
                * inv H5. eauto.
                * eapply Hdis1. now sets.
              + simpl. congruence.
              + repeat normalize_sets. xsets. (* ^^ yay sets *)
              + repeat normalize_sets. xsets. (* ^^ yay sets *)
              + repeat normalize_sets. simpl.
                assert (Hfeq : f_eq (((id {k3 ~> k4}) <{ vars1 ~> vars2 }>) {x1 ~> x0})
                                    (((id <{ vars1 ~> vars2 }>) {x1 ~> x0}) {k3 ~> k4})).
                { rewrite extend_extend_lst_commut; eauto.
                  rewrite extend_commut; eauto. reflexivity.
                  - inv H5. intros Hc. subst. eauto.
                  - inv H8. intros Hc. subst. eauto.
                  - inv H5. intros Hc. eapply Hdis1. sets.
                  - inv H8. intros Hc. eapply Hdis2. sets. }

                rewrite Hfeq.

                inv Hall. inv H13. clear H16.

                eapply preord_env_P_inj_set_alt; eauto.
                eapply preord_env_P_inj_set_alt; eauto.
                eapply preord_env_P_inj_set_not_In_P_l.
                eapply preord_env_P_inj_set_not_In_P_r.

                eapply preord_env_P_inj_f_eq_subdomain.

                eapply preord_env_P_inj_antimon.
                eapply preord_env_P_inj_monotonic.
                2: { eassumption. } lia.
                now xsets.

                rewrite !Setminus_Union_distr. rewrite Setminus_Same_set_Empty_set. (* TODO add to normalize_sets *)
                repeat normalize_sets.
                rewrite Setminus_Union, (Union_commut [set k3]), <- Setminus_Union.
                rewrite Setminus_Same_set_Empty_set. repeat normalize_sets.
                eapply f_eq_subdomain_extend_lst.
                eassumption.

                eapply f_eq_subdomain_extend_not_In_S_l; [ | reflexivity ].

                * intros Hc. inv Hc. inv H1. inv H9. eauto.

                * intros Hc. eapply image_extend_lst_Included in Hc.
                  rewrite image_id in Hc. inv Hc. inv H1. inv H7. inv H1.
                  inv H7; eauto.  inv H1; eauto.
                  inv H6. eapply Hdis2. now sets. eassumption.

                * intros Hc. inv Hc. inv H1. inv H9; eauto. inv H1; eauto.
                  inv H3. eapply Hdis1. now sets.

                * intros Hc. eapply image_extend_lst_Included in Hc.
                  rewrite image_id in Hc. inv Hc. inv H1. inv H7. inv H1.
                  inv H7; eauto.  inv H1; eauto.
                  inv H6. eapply Hdis2. now sets. eassumption.

                * intros Hc. inv Hc. inv H1. inv H7; eauto. inv H1; eauto.
                  inv H7; eauto.

                  inv H1. rewrite extend_gss in H8. inv H8. now eauto.

                  rewrite extend_gso in H8.
                  2:{ intros Hc; subst. rewrite extend_gss in H8. inv H8. now eauto. }
                  edestruct (@extend_lst_gss var). eassumption. eassumption. inv H7.
                  eapply Hdis2. constructor. right. eassumption. inv H8. eassumption.


              + lia.

            - lia. }

      - (* App_e *)
        intros e1 IHe1 e2 IHe2 e1' e2' m k1 k2 vars1 vars2 rho1 rho2
               S1 S2 S3 S4 Hlt He1 He2 Hdup Hnot Hlen Hdis1 Hdis2 Henv.
        inv He1. inv He2.
        eapply preord_exp_fun_compat.
        + eapply Hprops. (* invariants *)
        + eapply Hprops. (* invariants *)
        + { eapply preord_exp_monotonic. eapply IHe1; try eassumption.
            - inv H3. intros Hc. eapply Hdis1. sets.
            - xsets.
            - xsets.
            - simpl.
              assert (Hfeq : f_eq ((id {k3 ~> k5}) <{ vars1 ~> vars2 }>)
                                  ((id <{ vars1 ~> vars2 }>) {k3 ~> k5})).
              { rewrite extend_extend_lst_commut; eauto. reflexivity.
                - inv H3. intros Hc. eapply Hdis1. sets.
                - inv H8. intros Hc. eapply Hdis2. sets. }

              rewrite Hfeq.

              eapply preord_env_P_inj_set_alt; eauto.

              + eapply preord_env_P_inj_f_eq_subdomain.
                eapply preord_env_P_inj_antimon. eassumption.
                now sets.
                rewrite !Setminus_Union_distr. rewrite Setminus_Same_set_Empty_set.
                normalize_sets.
                eapply f_eq_subdomain_extend_lst. eassumption.
                eapply f_eq_subdomain_extend_not_In_S_l.

                intros Hc. inv Hc. now inv H0.
                reflexivity.

              + eapply preord_val_fun.
                simpl. rewrite Coqlib.peq_true. reflexivity.
                simpl. rewrite Coqlib.peq_true. reflexivity.

                intros. destruct vs1 as [ | ? [ | ? [ | ]] ]; simpl in *; try congruence.
                destruct vs2 as [ | ? [ | ? [ | ]] ]; simpl in *; try congruence.
                inv H1. eexists. split. reflexivity.

                intros Hlt' Hall. simpl.
                { eapply preord_exp_fun_compat.

                  + eapply HpropsG. (* invariants *)
                  + eapply HpropsG. (* invariants *)
                  + { destruct H with (m := (j - 1)%nat) as [ IHe _]. lia.
                      eapply preord_exp_post_monotonic. eapply HinclG.
                      eapply IHe; try eassumption.
                      - lia.
                      - inv_setminus. intros Hc. eapply Hdis1; eauto.
                      - eapply Disjoint_Included_r.
                        eapply cps_cvt_exp_subset. eassumption.
                        eapply Union_Disjoint_l; sets.
                        xsets.
                      - eapply Disjoint_Included_r.
                        eapply cps_cvt_exp_subset. eassumption.
                        eapply Union_Disjoint_l; sets.
                        xsets.
                      - simpl.
                        assert (Hfeq' : f_eq ((id {k4 ~> k6}) <{ vars1 ~> vars2 }>)
                                            ((id <{ vars1 ~> vars2 }>) {k4 ~> k6})).
                        { rewrite extend_extend_lst_commut; eauto. reflexivity.
                          - inv_setminus. intros Hc. eapply Hdis1; eauto.
                          - inv_setminus. intros Hc. eapply Hdis2; eauto. }

                        rewrite Hfeq'. eapply preord_env_P_inj_set_alt; eauto.

                        + rewrite !Setminus_Union_distr. rewrite Setminus_Same_set_Empty_set.
                          normalize_sets.
                          eapply preord_env_P_inj_set_not_In_P_l.
                          eapply preord_env_P_inj_set_not_In_P_r.
                          eapply preord_env_P_inj_set_not_In_P_l.
                          eapply preord_env_P_inj_set_not_In_P_r.

                          eapply preord_env_P_inj_f_eq_subdomain.
                          eapply preord_env_P_inj_antimon.
                          eapply preord_env_P_inj_monotonic. 2:{ eassumption. } lia.
                          now sets.
                          eapply f_eq_subdomain_extend_lst. eassumption.
                          eapply f_eq_subdomain_extend_not_In_S_l; [ | reflexivity ].

                          * intros Hc. inv Hc. now inv H1.
                          * inv H8. intros Hc.  eapply image_extend_lst_Included in Hc.
                            rewrite image_id in Hc. inv Hc.
                            inv H8. now inv H14.
                            eapply Hdis2. now sets. eassumption.
                          * inv H3. intros Hc. inv Hc. eapply Hdis1. sets.
                          * inv H5. intros Hc.
                            eapply image_extend_lst_Included in Hc. rewrite image_id in Hc. inv Hc.
                            inv H5. now inv H14; eauto.
                            eapply Hdis2. constructor. now right. eassumption. eassumption.
                          * intros Hc. inv Hc. eapply Hdis1. sets.

                        + eapply preord_val_fun.
                          simpl. rewrite Coqlib.peq_true. reflexivity.
                          simpl. rewrite Coqlib.peq_true. reflexivity.

                          intros. destruct vs1 as [ | ? [ | ? [ | ]] ]; simpl in *; try congruence.
                          destruct vs2 as [ | ? [ | ? [ | ]] ]; simpl in *; try congruence.
                          inv H1. eexists. split. reflexivity.

                          intros Hlt'' Hall'. simpl.
                          { eapply preord_exp_app_compat.
                            - eapply HpropsG. (* invariants *)
                            - eapply HpropsG. (* invariants *)
                            - inv H11. eapply preord_var_env_extend_neq.
                              eapply preord_var_env_extend_neq.
                              eapply preord_var_env_extend_eq.
                              inv Hall. eapply preord_val_monotonic. eassumption. lia.

                              + intros Hc1; subst. inv_setminus. eauto.

                              + intros Hc1; subst. inv_setminus. eauto.

                              + intros Hc1; subst. inv_setminus. eauto.

                              + intros Hc1; subst. inv_setminus. eauto.

                            - inv H11. constructor; [ | constructor; eauto ].
                              + eapply preord_var_env_extend_neq.
                                eapply preord_var_env_extend_neq.
                                eapply preord_var_env_extend_neq.
                                eapply preord_var_env_extend_neq.
                                eapply preord_var_env_monotonic.
                                assert (Heq: k2 = ((id {k1 ~> k2}) <{ vars1 ~> vars2 }>) k1).
                                { rewrite extend_lst_gso. rewrite extend_gss. reflexivity.
                                  eassumption. }
                                rewrite Heq. eapply Henv. now left. lia.

                                * intros Hc; subst. inv H3. eapply Hdis1; eauto.
                                * intros Hc; subst. inv H8. eapply Hdis2; eauto.
                                * intros Hc; subst. eapply Hdis1; eauto.
                                * intros Hc; subst. eapply Hdis2; eauto.
                                * intros Hc; subst. inv_setminus.
                                  eapply Hdis1; eauto.
                                * intros Hc; subst. inv_setminus.
                                  eapply Hdis2; eauto.
                                * intros Hc; subst. inv_setminus.
                                  eapply Hdis1; eauto.
                                * intros Hc; subst. inv_setminus. eapply Hdis2; eauto.

                              + eapply preord_var_env_extend_eq.
                                inv Hall'. eassumption. }

                        + intros Hc. eapply image_extend_lst_Included in Hc; eauto. rewrite image_id in Hc. inv Hc.
                          inv_setminus. now inv H1; eauto.
                          inv_setminus. eapply Hdis2; eauto.  } }
              + intros Hc. eapply image_extend_lst_Included in Hc; eauto. rewrite image_id in Hc. inv Hc.
                inv H0. inv H1; eauto. now inv H0.
                inv H8. eapply Hdis2; eauto.
            - lia. }

      - (* Con_e *)
        intros dc es IH e1 e2 m k1 k2 vars1 vars2 rho1 rho2
               S1 S2 S3 S4 Hltm He1 He2 Hdup Hnot Hlen Hdis1 Hdis2 Henv.
        inv He1; inv He2.

        assert (Hlen' : Datatypes.length xs = Datatypes.length xs0).
        { erewrite cps_cvt_rel_exps_len; [ | eassumption ].
          erewrite cps_cvt_rel_exps_len; [ | eassumption ].
          reflexivity. }


        eapply IH with (ys1 := []) (ys2 := []) (k1 := k1) (k2 := k2);
          [ | eassumption | eassumption | | | | | | | | | | | | | | | | | | ]; try eassumption; eauto.
        + constructor.
        + repeat normalize_sets. intros Hc. inv Hc; eauto.
          inv H0; eauto. eapply H4 in H1.
          inv_setminus. now eapply Hdis1; eauto.
          eapply H5 in H0. inv_setminus. now eapply Hdis1; eauto.
        + repeat normalize_sets. sets.
          eapply Union_Disjoint_r; eapply Disjoint_Included_r; eauto; sets.
        + repeat normalize_sets.
          eapply Union_Disjoint_l; sets.
          eapply Union_Disjoint_l; sets.
        + repeat normalize_sets.
          eapply Union_Disjoint_l; sets.
          eapply Union_Disjoint_l; sets.
        + repeat normalize_sets. sets.
        + repeat normalize_sets.
          eapply Union_Disjoint_l; sets.
          eapply Disjoint_Included_l. eassumption. eapply Disjoint_sym.
          eapply Disjoint_Included; [ | | eapply Hdis2 ]; sets.
          eapply Disjoint_Included_l. eassumption. eapply Disjoint_sym.
          eapply Disjoint_Included; [ | | eapply Hdis2 ]; sets.
        + eapply Disjoint_Included_r. eassumption. sets.
        + eapply Disjoint_Included_r. eassumption. sets.
        + simpl. intros rho1' rho2' l Henv'.
          eapply preord_exp_constr_compat.
          * eapply Hprops.
          * eapply Hprops.
          * rewrite <- @map_extend_lst_same with (xs := xs) (xs' := xs0) (f := id {k1 ~> k2}).
            eapply Forall2_preord_var_env_map. eassumption. now sets.
            eassumption. eassumption.
          * intros m1 vs1 vs2 Hlt Hall.
            eapply preord_exp_app_compat.
            -- eapply Hprops.
            -- eapply Hprops.
            -- assert (Heq: k2 = ((id {k1 ~> k2}) <{ xs ~> xs0 }>) k1).
               { rewrite extend_lst_gso.
                 rewrite extend_gss. reflexivity.
                 intros Hc. eapply H4 in Hc.
                 inv_setminus. eapply Hdis1; eauto. }
               rewrite Heq.
               eapply preord_env_P_inj_set_not_In_P_l.
               eapply preord_env_P_inj_set_not_In_P_r.
               eapply preord_env_P_inj_monotonic.
               2 : { eassumption. }
               lia.

               ++ intros Hc. eapply image_extend_lst_Included in Hc.
                  inv Hc.

                  eapply image_extend_Included' in H0.
                  rewrite image_id in H0.

                  assert (Hseq: k1 |: FromList xs \\ FromList xs \\ [set k1] <--> Empty_set _).
                  { sets. }
                  rewrite Hseq in H0. inv H0. now inv H1. inv H1.
                  eapply Hdis2. now constructor; eauto.

                  eapply H9 in H0. inv_setminus. now eauto.
                  eassumption.

               ++ intros Hc.
                  inv Hc. inv H0.

                  now eapply Hdis1; eauto.
                  eapply H4 in H0. inv_setminus. now eauto.

               ++ now left.

            -- constructor; eauto.
               eapply preord_var_env_extend_eq.
               rewrite preord_val_eq. simpl.
               split. reflexivity. eassumption.

        + simpl. repeat normalize_sets. eassumption.

      - (* Match_e *)
        intros e IHe pars bs IHbs e1 e3 m k1 k2 vars1 vars2 rho1 rho2
               S1 S2 S3 S4 Hltm He1 He2 Hdup Hnot Hlen Hdis1 Hdis2 Henv.
        inv He1; inv He2.
        eapply preord_exp_fun_compat.
        + eapply Hprops.
        + eapply Hprops.
        + eapply preord_exp_monotonic.
          eapply IHe; try eassumption.
          * inv H5. intros Hc. eapply Hdis1. sets.
          * xsets.
          * xsets.
          * simpl. rewrite extend_extend_lst_commut.
            eapply preord_env_P_inj_set_alt.
            rewrite Setminus_Union_distr.
            rewrite Setminus_Same_set_Empty_set. normalize_sets.
            rewrite Setminus_Disjoint.
            eapply preord_env_P_inj_f_eq_subdomain.
            eapply preord_env_P_inj_antimon.
            eapply preord_env_P_inj_monotonic.
            reflexivity.
            eassumption.
            sets.

            eapply f_eq_subdomain_extend_lst. eassumption.
            rewrite Setminus_Same_set_Empty_set.
            intros x Hx. now inv Hx.
            inv H5. eapply Disjoint_Included_r.
            eapply Singleton_Included. eassumption. sets.

            { eapply preord_val_fun.
              simpl.
              simpl. rewrite Coqlib.peq_true. reflexivity.
              simpl. rewrite Coqlib.peq_true. reflexivity.

              intros. destruct vs1 as [ | ? [ | ? [ | ]] ]; simpl in *; try congruence.
              destruct vs2 as [ | ? [ | ? [ | ]] ]; simpl in *; try congruence.
              inv H1. eexists. split. reflexivity.

              intros Hlt Hall.

              eapply preord_exp_monotonic.
              eapply preord_exp_post_monotonic. eapply HinclG.
              edestruct (H j) as (_ & _ & _ & Hexp ). lia.
              eapply Hexp; try eassumption.
              + reflexivity.
              + eapply Disjoint_Included_r.
                eapply cps_cvt_exp_subset. eassumption. xsets.
              + eapply Disjoint_Included_r.
                eapply cps_cvt_exp_subset. eassumption. xsets.
              + eapply preord_env_P_inj_set_not_In_P_l.
                eapply preord_env_P_inj_set_not_In_P_r.
                eapply preord_env_P_inj_set_not_In_P_l.
                eapply preord_env_P_inj_set_not_In_P_r.
                eapply preord_env_P_inj_monotonic.
                2: { eassumption. } lia.

                * intros Hc. eapply image_extend_lst_Included in Hc.
                  inv Hc.

                  eapply image_extend_Included' in H1.
                  rewrite image_id in H1.

                  assert (Heq : k1 |: FromList vars1 \\ FromList vars1 \\ [set k1] <--> Empty_set  _) by now sets.
                  rewrite Heq in H1. repeat normalize_sets. inv H1.
                  inv H7. eapply Hdis2. now sets.
                  inv H7. eapply Hdis2. now sets.
                  eassumption.

                * intros Hc.
                  inv H5. eapply Hdis1. now sets.

                * intros Hc. eapply image_extend_lst_Included in Hc.
                  inv Hc.

                  eapply image_extend_Included' in H1.
                  rewrite image_id in H1.

                  assert (Heq : k1 |: FromList vars1 \\ FromList vars1 \\ [set k1] <--> Empty_set  _) by now sets.
                  rewrite Heq in H1. repeat normalize_sets. inv H1.
                  inv H7. eapply Hdis2. now sets.
                  inv H7. eapply Hdis2. now sets.
                  eassumption.

                * intros Hc.
                  inv H5. eapply Hdis1. now sets.

              + eapply preord_var_env_extend_eq. inv Hall. eassumption.

              + lia. }

            rewrite Setminus_Union_distr, Setminus_Same_set_Empty_set.
            repeat normalize_sets.
            intros Hc. eapply image_extend_lst_Included in Hc.
            inv Hc.

            assert (Heq : (FromList vars1 \\ [set k3] \\ FromList vars1) <--> Empty_set  _) by now sets.
            rewrite Heq, image_id in H0. now inv H0.
            inv H7. eapply Hdis2. now sets. eassumption.

            intros Hin. inv H5. eapply Hdis1. now sets.

            intros Hin. inv H7. eapply Hdis2. now sets.
            eassumption.

          * lia.

      - (* Let_e *)
        intros na e1 IHe1 e2 IHe2 m e1' e2' k1 k2 vars1 vars2 rho1 rho2
               S1 S2 S3 S4 Hm He1 He2 Hdup Hnot Hlen Hdis1 Hdis2 Henv.
        inv He1; inv He2.
        eapply preord_exp_fun_compat.
        + eapply Hprops. (* invariants *)
        + eapply Hprops. (* invariants *)
        + { eapply preord_exp_monotonic. eapply IHe1; try eassumption.
            - inv H5. intros Hc. eapply Hdis1. sets.
            - eapply Disjoint_Included_r.
              eapply cps_cvt_exp_subset. eassumption.
              xsets.
            - eapply Disjoint_Included_r.
              eapply cps_cvt_exp_subset. eassumption.
              xsets.
            - simpl.
              assert (Hfeq : f_eq ((id {k3 ~> k4}) <{ vars1 ~> vars2 }>)
                                  ((id <{ vars1 ~> vars2 }>) {k3 ~> k4})).
              { rewrite extend_extend_lst_commut; eauto. reflexivity.
                - inv H5. intros Hc. eapply Hdis1. sets.
                - inv H7. intros Hc. eapply Hdis2. sets. }

              rewrite Hfeq.

              eapply preord_env_P_inj_set_alt; eauto.

              + eapply preord_env_P_inj_f_eq_subdomain.
                eapply preord_env_P_inj_antimon. eassumption.
                now sets.
                rewrite !Setminus_Union_distr. rewrite Setminus_Same_set_Empty_set.
                normalize_sets.
                eapply f_eq_subdomain_extend_lst. eassumption.
                eapply f_eq_subdomain_extend_not_In_S_l.

                intros Hc. inv Hc. now inv H0.
                reflexivity.

              + eapply preord_val_fun.
                simpl. rewrite Coqlib.peq_true. reflexivity.
                simpl. rewrite Coqlib.peq_true. reflexivity.

                intros. destruct vs1 as [ | ? [ | ? [ | ]] ]; simpl in *; try congruence.
                destruct vs2 as [ | ? [ | ? [ | ]] ]; simpl in *; try congruence.
                inv H1. eexists. split. reflexivity.

                intros Hlt Hall.
                edestruct (H j) as [Hexp _]. lia.
                eapply preord_exp_post_monotonic. eapply HinclG.
                eapply Hexp; try eassumption.
                lia.
                constructor; try eassumption.
                intros Hc. eapply Hdis1; now sets.

                repeat normalize_sets. intros Hc.
                inv Hc. inv H1. eapply Hdis1. now sets.
                eapply Hdis1. now sets.
                simpl. congruence.

                repeat normalize_sets. now xsets.
                repeat normalize_sets. now xsets.

                simpl. repeat normalize_sets.


                eapply preord_env_P_inj_set_alt; eauto.

                * rewrite !Setminus_Union_distr. rewrite Setminus_Same_set_Empty_set.
                  repeat normalize_sets.
                  eapply preord_env_P_inj_set_not_In_P_l.
                  eapply preord_env_P_inj_set_not_In_P_r.

                  eapply preord_env_P_inj_antimon.
                  eapply preord_env_P_inj_monotonic. 2:{ eassumption. } lia.
                  now sets.

                  ** intros Hc. eapply image_extend_lst_Included in Hc.
                     inv Hc.
                     eapply image_extend_Included' in H1.
                     rewrite image_id in H1.
                     assert (Heq: [set k1] \\ [set x1] :|: (FromList vars1 \\ [set x1]) \\ FromList vars1 \\ [set k1] <--> Empty_set _) by sets.

                     rewrite Heq in H1. repeat normalize_sets. inv H1.
                     inv H7. eapply Hdis2. now sets.
                     inv H7. eapply Hdis2. now sets.
                     eassumption.

                  ** rewrite <- Setminus_Union_distr. intros Hc. inv Hc.
                     inv H5. eapply Hdis1; eauto.

                * inv Hall. eassumption.

                * intros Hc. eapply image_extend_lst_Included in Hc.
                  inv Hc.
                  eapply image_extend_Included' in H1.
                  rewrite image_id in H1.
                  assert (Heq: k1 |: (x1 |: FromList vars1) \\ [set x1] \\ FromList vars1 \\ [set k1] <--> Empty_set _) by xsets.
                  rewrite Heq in H1. repeat normalize_sets. inv H1.
                  eapply Hdis2. now sets.
                  eapply Hdis2. now sets.
                  eassumption.

              + rewrite !Setminus_Union_distr. rewrite Setminus_Same_set_Empty_set.
                normalize_sets.
                intros Hc. eapply image_extend_lst_Included in Hc.
                inv Hc.
                rewrite image_id in H0. inv H0. inv H1. now eauto.

                inv H7. eapply Hdis2. now sets. eassumption.

            - lia. }


      - (* Fix_e *)
        intros e IH na e1 e2 m k1 k2 vars1 vars2 rho1 rho2 S1 S2 S3 S4
               Hm He1 He2 Hdup Hnot Hlen Hdis1 Hdis2 Henv.
        simpl in He1, He2. inv He1; inv He2.
        eapply preord_exp_fun_compat.
        + eapply Hprops. (* invariants *)
        + eapply Hprops. (* invariants *)
        + { simpl. eapply preord_exp_app_compat.
            - eapply Hprops. (* invariants *)
            - eapply Hprops. (* invariants *)
            - eapply preord_var_env_monotonic.

              eapply preord_var_env_def_funs_not_In_l.

              rewrite cps_cvt_rel_efnlst_name_in_fundes; [ | eassumption ].
              intros Hin. eapply Hdis1. now constructor; eauto.

              eapply preord_var_env_def_funs_not_In_r.

              rewrite cps_cvt_rel_efnlst_name_in_fundes; [ | eassumption ].
              intros Hin. eapply Hdis2. now constructor; eauto.

              assert (Heq: k2 = ((id {k1 ~> k2}) <{ vars1 ~> vars2 }>) k1).
              { rewrite extend_lst_gso. rewrite extend_gss. reflexivity. eassumption. }
              rewrite Heq.
              eapply Henv. now left. lia.

            - set (Heq1 := cps_cvt_rel_efnlst_all_fun_name _ _ _ _ _ _ H6).
              set (Heq2 := cps_cvt_rel_efnlst_all_fun_name _ _ _ _ _ _ H10).
              constructor; eauto.

              eapply @preord_env_P_inj_def_funs with (f := id {k1 ~> k2} <{ vars1 ~> vars2 }>).
              rewrite Heq1. eassumption.
              rewrite Heq2. eassumption.
              congruence.
              rewrite Heq1. eassumption.
              rewrite Heq2. eassumption.

              2:{ eapply @preord_env_P_inj_monotonic with (k := m). lia.
                  rewrite <- extend_lst_rev.
                  eapply IH; try eassumption. reflexivity. reflexivity.

                  - eapply List_util.NoDup_app; eauto.
                    now eapply NoDup_rev; eauto.

                    eapply Disjoint_sym. rewrite FromList_rev.
                    eapply Disjoint_Included; [ | | eapply Hdis1 ]; now sets.

                  - rewrite Heq1. eassumption.
                  - rewrite Heq2. eassumption.

                  - congruence.

                  - normalize_sets. rewrite FromList_rev. now xsets.

                  - normalize_sets. rewrite FromList_rev. now xsets.

                  - rewrite Same_set_all_fun_name. rewrite Heq2. now xsets.

                  - rewrite Heq1. eassumption.
                  - rewrite Heq2. eassumption.
                  - rewrite Heq1, Heq2.
                    replace (@Datatypes.length positive) with (@Datatypes.length var); eauto. congruence.
              }

              + normalize_sets.
                rewrite cps_cvt_rel_efnlst_name_in_fundes; eauto. now sets. }

      - (* Prf_e *)
        intros e1 e2 m k1 k2 vars1 vars2 rho1 rho2 S1 S2 S3 S4
               Hlt He1 He2 Hdup Hnot Hlen Hdis1 Hdis2 Henv.
        inv He1; inv He2.
        eapply preord_exp_constr_compat.
        + eapply Hprops.
        + eapply Hprops.
        + constructor.
        + intros.
          eapply preord_exp_app_compat.
          * eapply Hprops.
          * eapply Hprops.
          *  assert (Heq: k2 = ((id {k1 ~> k2}) <{ vars1 ~> vars2 }>) k1).
             { rewrite extend_lst_gso. rewrite extend_gss. reflexivity. now eauto. }
             eapply preord_var_env_extend_neq.
             eapply preord_var_env_monotonic.
             rewrite Heq. eapply Henv. now left. lia.
             intros Hc; inv Hc; eapply Hdis1; now eauto.
             intros Hc; inv Hc; eapply Hdis2; now eauto.
          * constructor; eauto.
            eapply preord_var_env_extend_eq.
            rewrite preord_val_eq. simpl; split; eauto.

      - (* Prim_val_e *)
        intros p e1 e2 m k1 k2 vars1 vars2 rho1 rho2 S1 S2 S3 S4
               Hlt He1 He2 Hdup Hnot Hlen Hdis1 Hdis2 Henv.
        inv He1; inv He2.
        eapply preord_exp_prim_val_compat.
        eapply Hprops.


      - (* Prim_e *)
        intros p e1 e2 m k1 k2 vars1 vars2 rho1 rho2 S1 S2 S3 S4
               He1 He2 Hdup Hnot Hlen Hdis1 Hdis2 Henv.
        inv He1; inv He2.
        (* TODO add Prim_e to relation ? *)

      - (* enil *)
        intros es1 es2 m k1 k2 vars1 vars2 xs1 xs2 ks1 ks2 ys1 ys2 rho1 rho2 ek1 ek2 S1 S2 S3 S4
               Hm He1 He2 Hdup1 Hdup2 Hdup3 Hdup4 Hnd5 Hnot Hdis Hlen Hlen' Hlen''
               Hdis1 Hdis2 Hdis3 Hdis4 Hdis5 Hdis6 Hhyp Henv.
        inv He1; inv He2.
        eapply Hhyp. rewrite !app_nil_r.
        eapply preord_env_P_inj_f_eq_subdomain.
        eapply preord_env_P_inj_antimon. eassumption.
        now sets.
        eapply f_eq_subdomain_extend_lst. eassumption.
        eapply f_eq_subdomain_extend_lst_Disjoint.
        rewrite Setminus_Union_distr. rewrite Setminus_Same_set_Empty_set.
        rewrite Union_Empty_set_neut_r.
        eapply Disjoint_Included_r. eapply Setminus_Included.
        eapply Disjoint_Singleton_r.
        intros Hc. eapply Hnot. eauto.

      - (* econs *)
        intros e IHe es IHes e1 e2 m k1 k2 vars1 vars2 xs1 xs2 ks1 ks2 ys1 ys2 rho1 rho2
               e_cont1 e_cont2 S1 S2 S3 S4
               Hm He1 He2 Hdup1 Hdup2 Hdup3 Hdup4 Hnd5  Hnot Hdis Hlen Hlen' Hlen''
               Hdis1 Hdis2 Hdis3 Hdis4 Hdis5 Hdis6 Hhyp Henv.
        inv He1; inv He2.
        eapply preord_exp_fun_compat.
        + eapply Hprops. (* invariants *)
        + eapply Hprops. (* invariants *)
        + { simpl. eapply preord_exp_monotonic.
            eapply IHe; try eassumption.
            - repeat normalize_sets. intros Hc.
              eapply Hdis; eauto.
            - repeat normalize_sets. xsets.
            - repeat normalize_sets. xsets.
            -  simpl. rewrite extend_extend_lst_commut; eauto.
              + eapply preord_env_P_inj_set_alt.
                * rewrite Setminus_Union_distr.
                  rewrite Setminus_Same_set_Empty_set. normalize_sets.
                  eapply preord_env_P_inj_f_eq_subdomain.
                  eapply preord_env_P_inj_antimon.
                  eapply preord_env_P_inj_monotonic.
                  reflexivity. eassumption. now sets.

                  rewrite f_eq_subdomain_extend_lst_Disjoint.
                  eapply f_eq_subdomain_extend_lst. eassumption.

                  assert (Heq: FromList vars1 \\ [set k0] \\ FromList vars1 <--> Empty_set _) by sets.
                  rewrite Heq. intros x Hin. now inv Hin.
                  now sets.
                * { eapply preord_val_fun.
                    simpl. rewrite Coqlib.peq_true. reflexivity.
                    simpl. rewrite Coqlib.peq_true. reflexivity.

                    intros. destruct vs1 as [ | ? [ | ? [ | ]] ]; simpl in *; try congruence.
                    destruct vs2 as [ | ? [ | ? [ | ]] ]; simpl in *; try congruence.
                    inv H1. eexists. split. reflexivity.
                    intros Hlt Hall.

                    eapply preord_exp_monotonic.
                    eapply preord_exp_post_monotonic. eapply HinclG.
                    edestruct (H j) as (_ & Hexps & _ & _ ). lia.
                    (* rewrite <- MRList.app_tip_assoc in H11, H13. inv Hdup2. *)
                    (* repeat normalize_sets. *)
                    eapply Hexps with (k1 := k1) (k2 := k2) (ys1 := ys1 ++ [x1]) (ys2 := ys2 ++ [x0]);
                      [ reflexivity | eassumption | eassumption | | | | | | | | | | | | | | | | | | ].
                    - eassumption.
                    - inv Hdup2. eassumption.
                    - inv Hdup3. eassumption.
                    - apply List_util.NoDup_app. eassumption.
                      constructor. intros Hc. now inv Hc. now constructor.
                      repeat normalize_sets. sets.
                    - inv Hnd5. eassumption.
                    - repeat normalize_sets. intros Hc; inv Hc; eauto.
                      eapply Hnot. inv H1; eauto. inv H2; eauto.
                      inv H2; eauto.
                    - repeat normalize_sets. xsets.
                    - congruence.
                    - congruence.
                    - rewrite !length_app. simpl. congruence.
                    - repeat normalize_sets. eapply Disjoint_Included_r.
                      eapply cps_cvt_exp_subset. eassumption. repeat normalize_sets. xsets.

                    - repeat normalize_sets. eapply Disjoint_Included_r.
                      eapply cps_cvt_exp_subset. eassumption. repeat normalize_sets. xsets.

                    - repeat normalize_sets.
                      eapply Union_Disjoint_l; sets.
                      eapply Union_Disjoint_r; sets.
                      inv Hdup2. eapply Disjoint_Singleton_r. eassumption.
                      eapply Union_Disjoint_r; sets.
                      eapply Disjoint_sym. eapply Disjoint_Included; [ | | eapply Hdis5 ]; sets.
                    - repeat normalize_sets.
                      rewrite !Union_assoc.
                      eapply Union_Disjoint_r.
                      eapply Disjoint_Included; [ | | eapply Hdis4 ]; now sets.
                      inv Hdup3. eapply Disjoint_Singleton_r.
                      intros Hc; inv Hc; eauto.
                      now eapply Hdis6 ; eauto.
                    - repeat normalize_sets.
                      eapply Disjoint_Included; [ | | eapply Hdis5 ]; sets.
                    - repeat normalize_sets.
                      eapply Disjoint_Included; [ | | eapply Hdis6 ]; sets.
                    - intros. eapply Hhyp. rewrite !MRList.app_tip_assoc in H1.
                      eassumption.
                    - simpl. rewrite !extend_lst_app; eauto. simpl.
                      rewrite extend_extend_lst_commut.


                      + inv Hall. eapply preord_env_P_inj_set_alt; [ | eassumption | ].

                        eapply preord_env_P_inj_set_not_In_P_r.
                        eapply preord_env_P_inj_set_not_In_P_l.

                        eapply preord_env_P_inj_antimon.
                        eapply preord_env_P_inj_monotonic.
                        2: { eassumption. } lia.
                        repeat normalize_sets. now xsets.

                        * repeat normalize_sets.
                          intros Hc. inv Hnd5. inv Hc; eauto.
                          inv H1; eauto. inv H9; eauto. inv H1; now eauto.
                          now eapply Hdis; eauto.
                          inv H9; eauto. eapply Hdis3. eauto.

                        * intros Hc. eapply image_extend_lst_Included in Hc; eauto.
                          inv Hc; eauto.

                          eapply image_extend_lst_Included in H1; eauto.

                          inv H1.
                          eapply image_extend_Included' in H2.
                          rewrite image_id in H2.
                          repeat normalize_sets. inv H2.


                          assert (Heq : (k1 |: FromList vars1
                                            :|: (FromList ys1 :|: [set x1]) \\ [set x1] \\
                                            FromList ys1 \\ FromList vars1 \\ [set k1]) <--> Empty_set _) by xsets.

                          eapply Heq in H1. now inv H1.

                          inv H1. eapply Hdis4. constructor. right. now left. now left.
                          eapply Hdis4; eauto. constructor. right. now left. left. now right.
                          repeat normalize_sets. eapply Hdis4; eauto.

                        * intros Hc. eapply image_extend_lst_Included in Hc; eauto.
                          inv Hc; eauto.

                          eapply image_extend_lst_Included in H1; eauto.

                          inv H1.
                          eapply image_extend_Included' in H2.
                          rewrite image_id in H2.
                          repeat normalize_sets. inv H2.


                          assert (Heq : (k1 |: FromList vars1
                                            :|: (FromList ys1 :|: [set x1]) \\ [set x1] \\
                                            FromList ys1 \\ FromList vars1 \\ [set k1]) <--> Empty_set _) by xsets.

                          eapply  Heq in H1. now inv H1.
                          inv H1; eapply Hdis4. constructor. left. now left. now eauto.
                          eapply Hdis4. constructor. left. now left. now eauto.
                          eapply Hdis4. constructor. left. now left. now eauto.

                      + repeat normalize_sets. intros Hc; eapply Hdis3; eauto.

                      + repeat normalize_sets. intros Hc; eapply Hdis4; eauto.

                      + eassumption.

                    - lia. }

                * rewrite Setminus_Union_distr. rewrite Setminus_Same_set_Empty_set. repeat normalize_sets.
                  intros Hc.
                  eapply image_extend_lst_Included in Hc; eauto.
                  rewrite image_id in Hc. inv Hc.

                  inv H0. inv H1; now eauto.

                  eapply Hdis4. constructor. right. now left. now eauto.

              + repeat normalize_sets. intros Hc.
                eapply Hdis; eauto.

              + repeat normalize_sets. intros Hc. eapply Hdis4. constructor. right. now left. eauto.

            - lia. }

      - (* eflnil *)
        intros B1 B2 m k1 k2 vars1 vars2 vars1' vars2' nl1 nl2 rho1 rho2 S1 S2 S3 S4
               Hm He1 He2 Heq1 Heq2 Hnd Hnd1 Hnd2 Hlen1 Hlen2 Hdis1 Hdis2 Hdis3 Henv.
        inv He1. inv He2. simpl. repeat normalize_sets.
        simpl in *. repeat normalize_sets. eassumption.

      - (* eflcons *)
        intros n e efns Hin IHe B1 B2 m k1 k2 vars1 vars2 vars1' vars2' nl1 nl2 rho1 rho2 S1 S2 S3 S4
               Hm He1 He2 Heql1 Heql2 Hnd Hnd1 Hnd2 Hlen1 Hlen2 Hdis1 Hdis2 Hdis3 Henv.

        revert m Hm Henv.
        induction k using lt_wf_rec. intros m Hm Henv.

        assert (Heq1 : all_fun_name B1 = nl1). { eapply cps_cvt_rel_efnlst_all_fun_name; eauto. }

        assert (Heq2 : all_fun_name B2 = nl2). { eapply cps_cvt_rel_efnlst_all_fun_name; eauto. }

        rewrite extend_lst_rev; eauto.
        eapply preord_env_P_inj_def_funs_Vfun.

        + rewrite Same_set_all_fun_name. rewrite Heq1.
          eapply preord_env_P_inj_antimon. eassumption.
          rewrite !Setminus_Union_distr. rewrite Setminus_Same_set_Empty_set.
          subst. repeat normalize_sets. rewrite FromList_rev. xsets.

        + eassumption.

        + eassumption.

        + subst. rewrite Same_set_all_fun_name.
          eapply Disjoint_Included_l.
          eapply image_extend_lst_Included. eassumption.
          eapply Union_Disjoint_l.

          eapply Disjoint_Included_l.
          eapply image_extend_Included'.
          eapply Union_Disjoint_l.
          rewrite image_id.
          assert (Heq : k1 |: (FromList (rev (all_fun_name B1) ++ vars1') :|: FromList (all_fun_name B1)) \\
                           FromList (all_fun_name B1) \\ FromList vars1' \\ [set k1] <--> Empty_set _).
          { repeat normalize_sets. rewrite FromList_rev. now xsets. }

          rewrite Heq. now sets.

          rewrite Same_set_all_fun_name. repeat normalize_sets.

          rewrite <- Same_set_all_fun_name. now xsets.
          now sets.

        + { intros.
            edestruct cps_cvt_rel_efnlst_exists with (S1 := S1); try eassumption. destructAll.
            edestruct cps_cvt_rel_efnlst_exists with (S1 := S3); try eassumption. destructAll.

            eapply preord_val_fun.
            - eassumption.
            - eassumption.
            - intros rho1' j vs1 vs2 Hlen' Hset.
              destruct vs1 as [ | ? [ | ? [ | ]] ]; simpl in *; try congruence.
              destruct vs2 as [ | ? [ | ? [ | ]] ]; simpl in *; try congruence.
              inversion Hset. eexists. split. reflexivity.
              intros Hlt Hall. inv Hall. inv H21. clear H22.

              edestruct (H j) as [ Hexp _ ]. lia. repeat subst_exp.
              eapply preord_exp_post_monotonic. eapply HinclG.
              eapply Hexp.
              + lia.
              + eassumption.
              + eassumption.
              + constructor; [ | eassumption ]. repeat normalize_sets.
                intros Hc. eapply Hdis1.
                eapply in_app_or in Hc. inv Hc; eauto.
              + repeat normalize_sets. inv H6. intros Hc. inv Hc.
                * inv H6. eauto.
                * eapply Hdis1. now sets.
              + simpl. rewrite !length_app, !length_rev. congruence.
              + repeat normalize_sets.
                eapply Union_Disjoint_l; sets.
                eapply Union_Disjoint_l; sets.
                eapply Disjoint_Included; [ | | eapply Hdis1 ]; sets.
              + repeat normalize_sets.
                eapply Union_Disjoint_l; sets.
                eapply Union_Disjoint_l; sets.
                eapply Disjoint_Included; [ | | eapply Hdis2 ]; sets.
              + repeat normalize_sets. simpl.
                assert (Hfeq : f_eq (((id {x ~> x6}) <{ rev (all_fun_name B1) ++ vars1' ~> rev (all_fun_name B2) ++ vars2' }>) {x0 ~> x7})
                                    (((id <{ rev (all_fun_name B1) ++ vars1' ~> rev (all_fun_name B2) ++ vars2' }>) {x0 ~> x7}) {x ~> x6})).
                { rewrite extend_extend_lst_commut; eauto.
                  rewrite extend_commut; eauto. reflexivity.
                  - inv H6. intros Hc. subst. eauto.
                  - inv H12. intros Hc. subst. eauto.
                  - inv H6. intros Hc. eapply Hdis1. rewrite FromList_rev.
                    eapply in_app_or in Hc. inv Hc; eauto.
                    eapply in_rev in H6; eauto.
                  - inv H12. intros Hc. eapply Hdis2. rewrite FromList_rev.
                    eapply in_app_or in Hc. inv Hc; eauto.
                    eapply in_rev in H12; eauto.
                  - rewrite !length_app. rewrite !length_rev. congruence. }

                rewrite Hfeq.

                eapply preord_env_P_inj_set_alt; eauto.
                eapply preord_env_P_inj_set_alt; eauto.

                * eapply preord_env_P_inj_f_eq_subdomain.
                  eapply preord_env_P_inj_antimon.
                  { eapply H0 with (m := j).
                    - lia.
                    - intros. eapply H. lia.
                    - eauto.
                    - reflexivity.
                    - eapply preord_env_P_inj_antimon.
                      eapply preord_env_P_inj_monotonic. 2:{ eassumption. } lia.
                      repeat normalize_sets. sets. }

                  repeat normalize_sets. now xsets.

                  rewrite extend_lst_app.

                  eapply f_eq_subdomain_extend_lst. rewrite !length_rev.  eassumption.
                  eapply f_eq_subdomain_extend_lst. eassumption.


                  assert (Hfeq' : (x |: (x0 |: (FromList (rev (all_fun_name B1)) :|: FromList vars1')) \\ [set x] \\ [set x0] \\
                                     FromList (rev (all_fun_name B1)) \\ FromList vars1') <--> Empty_set _) by xsets.
                  rewrite Hfeq'. intros z Hinz. now inv Hinz. rewrite !length_rev. eassumption.

                * intros Hc. eapply image_extend_lst_Included in Hc; eauto.
                  rewrite image_id in Hc. inv Hc; eauto. inv H9; eauto. inv H15; eauto.
                  inv H9; eauto. inv H15; eauto. repeat normalize_sets. now inv H9; eauto.

                  repeat normalize_sets. eapply Hdis2. now sets.
                  rewrite !length_app, !length_rev. congruence.

                * intros Hc. eapply image_extend_Included' in Hc.
                  inv H12. inv Hc; eauto.

                  eapply image_extend_lst_Included in H12; eauto.
                  rewrite image_id in H12.

                  repeat normalize_sets.
                  assert (Heq :x |: (x0 |: (FromList (rev (all_fun_name B1)) :|: FromList vars1')) \\ [set x] \\ [set x0] \\
                                 (FromList (rev (all_fun_name B1)) :|: FromList vars1') <--> Empty_set _) by xsets.

                  rewrite Heq in H12. repeat normalize_sets.
                  now eapply Hdis2; eauto.
                  rewrite !length_app, !length_rev. congruence. }

      - (* brnil_e *)
        intros bs1 bs2 m k1 k2 vars1 vars2 x1 x2 rho1 rho2
               S1 S2 S3 S4 Hm He1 He2 Hdup Hnot Hlen Hdis1 Hdis2 Henv Hvar.
        inv He1; inv He2.
        eapply preord_exp_case_nil_compat.
        eapply Hprops.


      - (* brcons_e *)
        intros d p e IHe bs IHbs bs1 bs2 m k1 k2 vars1 vars2 x1 x2 rho1 rho2
               S1 S2 S3 S4 Hm He1 He2 Hdup Hnot Hlen Hdis1 Hdis2 Henv Hvar.
        inv He1; inv He2.
        eapply preord_exp_case_cons_compat.
        + eapply Hprops.
        + eapply Hprops.
        + eapply Hprops.
        + eapply cps_cvt_rel_branches_ctor_tag; eauto.
        + eassumption.
        + intros.
          assert (Hv1 :  FromList vars \subset S1).
          { eapply cps_cvt_rel_subset in H16. eapply Included_trans; sets. }
          assert (Hv2 :  FromList vars0 \subset S3).
          { eapply cps_cvt_rel_subset in H22. eapply Included_trans; sets. }

          eapply preord_exp_monotonic.
          * eapply ctx_bind_proj_alpha_equiv.
            -- eassumption.
            -- eassumption.
            -- congruence.
            -- eassumption.
            -- eassumption.
            -- eapply Disjoint_Included_l. eassumption. sets.
            -- eapply Disjoint_Included_l. eassumption.
               eapply Union_Disjoint_r. now sets.
               eapply Disjoint_Included_r.
               eapply image_extend_lst_Included. eassumption.
               eapply Union_Disjoint_r; sets.
               rewrite Setminus_Union_distr, Setminus_Same_set_Empty_set.
               repeat normalize_sets.
               eapply Disjoint_Included_r.
               eapply image_extend_Included'.
               eapply Union_Disjoint_r.
               rewrite image_id. now sets. now sets.

            -- intros. eapply IHe; try eassumption. lia.

               ++ eapply List_util.NoDup_app; eauto.
                  eapply Disjoint_Included_l. eassumption. sets.

               ++ repeat normalize_sets.
                  intros Hc. inv Hc; eauto. eapply Hdis1. now eauto.
               ++ rewrite !length_app. congruence.
               ++ eapply cps_cvt_rel_subset in H16.
                  repeat normalize_sets.
                  eapply Union_Disjoint_l; sets.

                  eapply Disjoint_Singleton_l. intros Hc.
                  inv Hc; eauto. eapply Hdis1. constructor. left. now left.
                  now eauto.
                  eapply Union_Disjoint_l; sets.
                  eapply Disjoint_Included; [ | | eapply Hdis1 ].
                  eapply Included_trans; [ | eapply H16 ]. now sets.
                  now sets.
               ++ eapply cps_cvt_rel_subset in H22.
                  repeat normalize_sets.
                  eapply Union_Disjoint_l; sets.

                  eapply Disjoint_Singleton_l. intros Hc.
                  inv Hc; eauto. eapply Hdis2. constructor. left. now left.
                  now eauto.
                  eapply Union_Disjoint_l; sets.
                  eapply Disjoint_Included; [ | | eapply Hdis2 ].
                  eapply Included_trans; [ | eapply H22 ]. now sets.
                  now sets.
               ++ rewrite extend_lst_app.
                  eapply preord_env_P_inj_antimon. eassumption.
                  repeat normalize_sets. now sets.
                  replace (@Datatypes.length positive) with (@Datatypes.length var); eauto. congruence.

          * lia.
        + eapply IHbs; try eassumption.

          Unshelve. eassumption.
    Qed.


    (** ** CPS value relation *)


    Definition cps_env_rel' (P : value -> val -> Prop) (vn : list var)
               (vs : list value) (rho : M.t val) :=
      Forall2 (fun v x => exists v',  M.get x rho = Some v' /\ P v v') vs vn.

    Inductive cps_fix_rel (fnames : list var) (names : list var) : Ensemble var -> list var -> efnlst -> fundefs -> Ensemble var -> Prop :=
    | fix_fnil :
        forall S, cps_fix_rel fnames names S [] eflnil Fnil S
    | fix_fcons :
        forall S1 S1' S2 S2' S3 fnames' e1 e2 n n' efns B f x k,
          Disjoint _ S1 (FromList fnames :|: FromList names) ->
          x \in S1 ->
          k \in S1 \\ [set x] ->
          S1' \subset S1 \\ [set x] \\ [set k] ->
          S2' \subset S2 ->
          (* ~ x \in k |: S1 :|: (FromList fnames :|: FromList names) -> *)
          (* ~ k \in S1 :|: (FromList fnames :|: FromList names) -> *)

          cps_cvt_rel S1'  e1 (x :: List.rev fnames ++ names) k cnstrs S2 e2 ->


          cps_fix_rel fnames names S2' fnames' efns B S3 ->
          cps_fix_rel fnames names S1 (f :: fnames') (eflcons n' (Lam_e n e1) efns) (Fcons f func_tag (k::x::nil) e2 B) S3.


    (** ** CPS value relation *)

    Inductive cps_val_rel : value -> val -> Prop :=
    | rel_Con :
        forall vs vs' dc c_tag,
          Forall2 (fun v v' => cps_val_rel v v') vs vs' ->
          dcon_to_tag default_tag dc cnstrs = c_tag ->
          cps_val_rel (Con_v dc vs) (Vconstr c_tag vs')
    | rel_Clos :
        forall vs rho names na k x f e e' S1 S2,
          cps_env_rel' cps_val_rel names vs rho ->

          NoDup names ->

          Disjoint var (k |: (x |: FromList names)) S1 ->

          ~ x \in k |: [set f] :|: FromList names ->
          ~ k \in f |: FromList names ->
          ~ f \in FromList names ->

          cps_cvt_rel S1 e (x :: names) k cnstrs S2 e' ->
          cps_val_rel (Clos_v vs na e)
                      (Vfun rho (Fcons f func_tag (k::x::nil) e' Fnil) f)
    | rel_ClosFix :
        forall S1 S2 names fnames vs rho efns Bs n f,
          cps_env_rel' cps_val_rel names vs rho ->

          NoDup names ->
          NoDup fnames ->

          Disjoint _ (FromList names :|: FromList fnames) S1 ->
          Disjoint _ (FromList names) (FromList fnames) ->

          nth_error fnames (N.to_nat n) = Some f ->

          cps_fix_rel fnames names S1 fnames efns Bs S2 ->

          cps_val_rel (ClosFix_v vs efns n) (Vfun rho Bs f).


    Definition cps_env_rel : list var -> list value -> M.t val -> Prop :=
      cps_env_rel' cps_val_rel.


    Definition cps_cvt_val_alpha_equiv_statement k :=
      forall v v1 v2,
        cps_val_rel v v1 ->
        cps_val_rel v v2 ->
        preord_val cenv PG k v1 v2.

    Definition cps_cvt_env_alpha_equiv_statement k :=
      forall names1 names2 vs rho1 rho2 f,
        cps_env_rel names1 vs rho1 ->
        cps_env_rel names2 vs rho2 ->

        preord_env_P_inj cenv PG (FromList names1) k (f <{ names1 ~> names2 }>) rho1 rho2.


    Lemma preord_env_P_inj_get S k f rho1 rho2 x y v1 v2 :

      preord_env_P_inj cenv PG (S \\ [set x]) k f rho1 rho2 ->

      M.get x rho1 = Some v1 ->
      M.get y rho2 = Some v2 ->

      preord_val cenv PG k v1 v2 ->

      preord_env_P_inj cenv PG S k (f {x ~> y}) rho1 rho2.
    Proof.
      intros Henv Hg1 Hg2 Hval z HS v Hgetz. destruct (Coqlib.peq x z).
      - subst. repeat subst_exp. rewrite extend_gss. eauto.
      - rewrite extend_gso; eauto. eapply Henv; eauto.
        constructor; eauto. intros Hc; inv Hc; eauto.
    Qed.


    Lemma cps_cvt_env_alpha_equiv_pre k :
      cps_cvt_val_alpha_equiv_statement k ->
      cps_cvt_env_alpha_equiv_statement k.
    Proof.
      intros IH n1 n2 vs.
      revert n1 n2. induction vs; intros n1 n2 rho1 rho2 f Hrel1 Hrel2.
      - inv Hrel1; inv Hrel2. simpl. repeat normalize_sets.
        intros x Hin. inv Hin.
      - inv Hrel1; inv Hrel2. destructAll.
        simpl. eapply preord_env_P_inj_get; eauto.
        repeat normalize_sets. eapply preord_env_P_inj_antimon.
        eapply IHvs. eassumption. eassumption. sets.
    Qed.


    Lemma cps_fix_rel_names fnames names S1 fnames' efns Bs S2 :
      cps_fix_rel fnames names S1 fnames' efns Bs S2 ->
      all_fun_name Bs = fnames'.
    Proof.
      intros Hcps. induction Hcps; eauto.
      simpl. congruence.
    Qed.

    Lemma cps_fix_rel_length fn n S1 names efns Bs S2 :
      cps_fix_rel fn n S1 names efns Bs S2 ->
      @List.length var names = efnlength efns.
    Proof.
      intros Hrel. induction Hrel; simpl in *; congruence.
    Qed.

    Lemma cps_fix_rel_exists fn n S1 names efns Bs S2 m f :
      cps_fix_rel fn n S1 names efns Bs S2 ->
      nth_error names m = Some f ->
      NoDup names ->
      exists k1 x1 na e1 e1' S1' S2',
        enthopt m efns = Some (Lam_e na e1) /\
        find_def f Bs = Some (func_tag, [k1; x1], e1') /\
        ~ x1 \in k1 |: S1' :|: (FromList fn :|: FromList n) /\
        ~ k1 \in S1' :|: (FromList fn :|: FromList n) /\
        S1' \subset S1 /\
        cps_cvt_rel S1' e1 (x1 :: rev fn ++ n) k1 cnstrs S2' e1'.
    Proof.
      intros Hrel. revert f m. induction Hrel; intros.
      - destruct m; inv H.
      - destruct m.
        + inv H5. inv H6. do 7 eexists. split; [ | split; [ | split; [ | split ; [ | split ]]]]; [ | | | | | eassumption ].
          * reflexivity.
          * simpl. rewrite Coqlib.peq_true. reflexivity.
          * inv_setminus. intros Hc. inv Hc. inv H1; eauto. now inv H7; eauto.
            eapply H2 in H7. inv H7. inv H1. now eauto.
            eapply H. constructor. eapply H0. eassumption.
          * inv_setminus. intros Hc. inv Hc.
            eapply H2 in H1. inv H1. now eauto.
            eapply H. constructor; eauto.
          * eapply Included_trans. eassumption. sets.
        + simpl in H5. inv H6. edestruct IHHrel; eauto. destructAll.
          do 7 eexists. split; [ | split; [ | split; [ | split; [ | split ]]]]; [ | | | | | eassumption ].
          * eassumption.
          * simpl. rewrite Coqlib.peq_false. eassumption.
            intros Hc; subst. eapply H9. eapply nth_error_In. eassumption.
          * eassumption.
          * eassumption.
          * eapply Included_trans. eassumption.
            eapply Included_trans. eassumption.
            eapply Included_trans. eapply cps_cvt_exp_subset. eassumption.
            eapply Included_trans. eassumption. sets.
    Qed.


    Lemma cps_cvt_val_alpha_equiv :
      forall k, cps_cvt_val_alpha_equiv_statement k.
    Proof.
      intros k. induction k as [k IHk] using lt_wf_rec1.  intros v.
      set (P := fun (v : value) => forall v1 v2 : val, cps_val_rel v v1 -> cps_val_rel v v2 -> preord_val cenv PG k v1 v2).

      eapply value_ind' with (P := P); subst P; simpl.

      - intros dcon vs IH v1 v2 Hrel1 Hrel2.
        inv Hrel1; inv Hrel2.
        rewrite preord_val_eq. simpl. split; eauto.
        revert vs' vs'0 H1 H2.
        induction IH; intros vs1 vs2 H1 H2.
        + inv H1. inv H2. constructor.
        + inv H1; inv H2. constructor; eauto.

      - intros vs1 na e Hall v1 v2 Hrel1 Hrel2.
        inv Hrel1; inv Hrel2.
        rewrite preord_val_eq. simpl. intros.
        rewrite Coqlib.peq_true in *. inv H0.
        destruct vs0 as [ | ? [ | ? [ | ] ] ]; simpl in *; try congruence. inv H1.
        destruct vs2 as [ | ? [ | ? [ | ] ] ]; simpl in *; try congruence.
        do 3 eexists. split. reflexivity. split. simpl. reflexivity.
        intros.

        assert (Hlen : Datatypes.length names = Datatypes.length names0).
        { unfold cps_env_rel' in *. eapply Forall2_length in H2.
          eapply Forall2_length in H7.
          replace (@Datatypes.length positive) with (@Datatypes.length var) in * by reflexivity.
          congruence. }

        assert (Hseq : (k0 |: (x |: FromList names) \\ [set k0] \\ [set x] \\ FromList names) <--> Empty_set _) by xsets.
        assert (Hseq' : (k1 |: (x0 |: FromList names0) \\ [set k1] \\ [set x0] \\ FromList names0) <--> Empty_set _) by xsets.

        eapply preord_exp_post_monotonic. eapply HinclG.
        destruct (cps_cvt_alpha_equiv j) as [Hexp  _].
        eapply Hexp.
        + lia.
        + eassumption.
        + eassumption.
        + constructor; eauto.
        + normalize_sets. intros Hc; inv Hc; eauto.
          inv H14; eauto.
        + simpl. congruence.
        + normalize_sets. sets.
        + normalize_sets. sets.
        + repeat normalize_sets. simpl. inv H1. inv H21.
          rewrite extend_extend_lst_commut; eauto.
          rewrite extend_commut; eauto.

          eapply preord_env_P_inj_set_alt; eauto.
          eapply preord_env_P_inj_set_alt; eauto.

          eapply preord_env_P_inj_set_not_In_P_l; eauto.
          eapply preord_env_P_inj_set_not_In_P_r; eauto.

          eapply preord_env_P_inj_antimon.
          eapply cps_cvt_env_alpha_equiv_pre; try eassumption. eapply IHk; eauto.
          now xsets.

          * intros Hc. eapply image_extend_lst_Included in Hc; eauto.
            rewrite image_id, Hseq in Hc. inv Hc. inv H1. eauto.

          * intros Hc. inv Hc. inv H1. inv H17. inv H1; eauto. inv H1; eauto.

          * intros Hc. eapply image_extend_lst_Included in Hc; eauto.
            rewrite image_id, Hseq in Hc. inv Hc. inv H1. eauto.

          * intros Hc.
            eapply image_extend_Included' in Hc. inv Hc; eauto.
            eapply image_extend_lst_Included in H1; eauto.
            inv H1; eauto.
            rewrite Hseq in H14.
            rewrite image_id in H14. inv H14. inv H1; eauto.

          * intros Hc; inv Hc; eauto.

          * intros Hc; inv Hc; eauto.

      - intros vs1 na e Hall v1 v2 Hrel1 Hrel2.

        inv Hrel1; inv Hrel2.

        assert (Hname := H9). eapply cps_fix_rel_names in Hname.
        assert (Hname' := H16). eapply cps_fix_rel_names in Hname'. subst.
        revert f f0 H8 H15. generalize (N.to_nat e). induction k as [m IHm] using lt_wf_rec.
        intros.

        edestruct cps_fix_rel_exists with (fn := all_fun_name Bs0) (f := f0); try eassumption.
        edestruct cps_fix_rel_exists with (fn := all_fun_name Bs) (f := f); try eassumption.
        destructAll.

        eapply preord_val_fun.
        eassumption. eassumption. intros rho1' j vs vs' Hlen Hset.
        destruct vs as [ | ? [ | ? [ | ? ] ] ]; simpl in * ; try congruence. inv Hset.
        destruct vs' as [ | ? [ | ? [ | ? ] ] ]; simpl in * ; try congruence. clear Hlen.


        assert (Hlen : @Datatypes.length var names = @Datatypes.length var names0).
        { unfold cps_env_rel' in *. eapply Forall2_length in H2. eapply Forall2_length in H7.
          replace (@Datatypes.length positive) with (@Datatypes.length var) in * by reflexivity.
          congruence. }

        assert (Hlen' : @Datatypes.length var (all_fun_name Bs) = @Datatypes.length var (all_fun_name Bs0)).
        { eapply cps_fix_rel_length in H9. eapply cps_fix_rel_length in H16. congruence. }

        eexists. split. reflexivity.
        intros Hlt Hall'. inv Hall'. inv H30. clear H32. repeat subst_exp.

        eapply preord_exp_post_monotonic. eapply HinclG.
        destruct (cps_cvt_alpha_equiv j) as [Hexp  _].
        eapply Hexp.
        + lia.
        + eassumption.
        + eassumption.
        + constructor; eauto.
          intros Hc. eapply in_app_or in Hc. inv Hc; eauto. now eapply in_rev in H0; eauto.
          eapply List_util.NoDup_app; eauto. eapply NoDup_rev. eassumption.
          rewrite FromList_rev. sets.
        + repeat normalize_sets. intros Hc; inv Hc; eauto.
          inv H0; eauto. rewrite FromList_rev in H0. eauto.
        + simpl. rewrite !length_app, !length_rev. congruence.
        + repeat normalize_sets.
          eapply Union_Disjoint_l; sets.
          eapply Union_Disjoint_l; sets.
          eapply Disjoint_Singleton_l. now eauto.
          eapply Disjoint_Included_r. eassumption.
          rewrite FromList_rev. sets.
        + repeat normalize_sets.
          eapply Union_Disjoint_l; sets.
          eapply Union_Disjoint_l; sets.
          eapply Disjoint_Singleton_l. now eauto.
          eapply Disjoint_Included_r. eassumption. rewrite FromList_rev. sets.
        + simpl. repeat normalize_sets.
          rewrite extend_extend_lst_commut; eauto.
          rewrite extend_commut; eauto.

          eapply preord_env_P_inj_set_alt; eauto.
          eapply preord_env_P_inj_set_alt; eauto.

          rewrite extend_lst_app. rewrite extend_lst_rev; eauto.

          eapply preord_env_P_inj_def_funs_Vfun; try eassumption.

          * eapply preord_env_P_inj_antimon.
            eapply cps_cvt_env_alpha_equiv_pre; try eassumption. eapply IHk; eauto.
            rewrite Same_set_all_fun_name. rewrite FromList_rev. now xsets.

          * eapply Disjoint_Included_l.
            eapply image_extend_lst_Included. eassumption.
            rewrite image_id. rewrite !Same_set_all_fun_name.
            rewrite FromList_rev.
            assert (Hseq : x0 |: (x1 |: (FromList (all_fun_name Bs) :|: FromList names)) \\ [set x0] \\ [set x1] \\
                              FromList (all_fun_name Bs) \\ FromList names <--> Empty_set _) by xsets.

            rewrite Hseq. eapply Union_Disjoint_l; sets.

          * intros. subst. repeat subst_exp. eapply IHm; eauto.
            intros. eapply IHk. lia.
            eapply Forall_impl; [ | eassumption ]. simpl. intros.
            eapply preord_val_monotonic. eapply H26. eassumption. eassumption. lia.

          * rewrite !length_rev. eassumption.

          * intros Hc. eapply image_extend_lst_Included in Hc. repeat normalize_sets. rewrite image_id in Hc.
            rewrite !FromList_rev in Hc.
            assert (Hseq : x0 |: (x1 |: (FromList (all_fun_name Bs) :|: FromList names)) \\ [set x0] \\ [set x1] \\
                              (FromList (all_fun_name Bs) :|: FromList names) <--> Empty_set _) by xsets.
            rewrite Hseq in Hc. repeat normalize_sets.
            now inv Hc; eauto.
            rewrite !length_app, !length_rev. congruence.

          * intros Hc. eapply image_extend_Included' in Hc.
            inv Hc; eauto. eapply image_extend_lst_Included in H0. repeat normalize_sets. rewrite image_id in H0.
            rewrite !FromList_rev in H0.
            assert (Hseq : x0 |: (x1 |: (FromList (all_fun_name Bs) :|: FromList names)) \\ [set x0] \\ [set x1] \\
                              (FromList (all_fun_name Bs) :|: FromList names) <--> Empty_set _) by xsets.
            rewrite Hseq in H0. repeat normalize_sets.
            now inv H0; eauto.
            rewrite !length_app, !length_rev. congruence.
            inv H0; eauto.

          * intros Hc; subst; eauto.

          * intros Hc; subst; eauto.

          * intros Hc. eapply in_app_or in Hc. inv Hc; eauto. eapply in_rev in H0; eauto.

          * intros Hc. eapply in_app_or in Hc. inv Hc; eauto. eapply in_rev in H0; eauto.

          * rewrite !length_app, !length_rev. congruence.
    Qed.


    Corollary cps_cvt_env_alpha_equiv k :
      cps_cvt_env_alpha_equiv_statement k.
    Proof.
      eapply cps_cvt_env_alpha_equiv_pre. eapply cps_cvt_val_alpha_equiv.
    Qed.

End Post.
