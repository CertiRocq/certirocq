(* Library extending ctx with a notion of bound on the stem of a context, as used in the proof of correctness of the shrink inliner *)

From Stdlib Require Import Lists.List SetoidList NArith.BinNat PArith.BinPos
        MSets.MSetRBT Lists.List Sets.Ensembles micromega.Lia Sorting.Permutation.
Require Import compcert.lib.Coqlib.
Require Import LambdaANF.cps LambdaANF.cps_util LambdaANF.ctx LambdaANF.set_util LambdaANF.Ensembles_util LambdaANF.List_util LambdaANF.size_cps LambdaANF.identifiers LambdaANF.tactics.
Import ListNotations.

(** bound_stem_ctx is the set of the variables bound on the stem of a context (from the root to the hole) *)
  Inductive bound_stem_ctx: exp_ctx -> Ensemble var  :=
  | SBound_Constr1_c:
      forall v t ys c, bound_stem_ctx (Econstr_c v t ys c) v
  | SBound_Constr2_c:
      forall c v v' t ys,
        bound_stem_ctx c v ->
        bound_stem_ctx (Econstr_c v' t ys c) v
  | SBound_Proj1_c:
      forall  t n r c v,
        bound_stem_ctx (Eproj_c v t n r c) v
  | SBound_Proj2_c:
      forall t n r c v' v,
        bound_stem_ctx c v' ->
        bound_stem_ctx (Eproj_c v t n r c) v'
  | SBound_Letapp1_c :
      forall (f : var) (ft : fun_tag) (xs : list var) (c : exp_ctx) (v : var),
        bound_stem_ctx (Eletapp_c v f ft xs c) v
  | SBound_Letapp2_c :
      forall (f : var) (ft : fun_tag) (xs : list var) (c : exp_ctx) (v' v : var),
        bound_stem_ctx c v' -> bound_stem_ctx (Eletapp_c v f ft xs c) v'
  | SBound_Prim_val1_c:
      forall x p c,
        bound_stem_ctx (Eprim_val_c x p c) x
  | SBound_Prim_val2_c:
      forall p c v' v,
        bound_stem_ctx c v' ->
        bound_stem_ctx (Eprim_val_c v p c) v'
| SBound_Prim1_c:
      forall x f ys c,
        bound_stem_ctx (Eprim_c x f ys c) x
  | SBound_Prim2_c:
      forall  t r c v' v,
        bound_stem_ctx c v' ->
        bound_stem_ctx (Eprim_c v t r c) v'
  | SBound_Case1_c:
      forall v v' lce t c lce',
        bound_stem_ctx c v' ->
        bound_stem_ctx (Ecase_c v lce t c lce') v'
  | SBound_Fun11_c:
      forall fds v c,
        name_in_fundefs fds v ->
        bound_stem_ctx (Efun1_c fds c) v
  | SBound_Fun12_c:
      forall fds v c,
        bound_stem_ctx c v ->
        bound_stem_ctx (Efun1_c fds c) v
  | SBound_Fun21_c:
      forall fds v c,
        names_in_fundefs_ctx fds v ->
        bound_stem_ctx (Efun2_c fds c) v
  | SBound_Fun2_c:
      forall cfds v e,
        bound_stem_fundefs_ctx cfds v ->
        bound_stem_ctx (Efun2_c cfds e) v
  with bound_stem_fundefs_ctx: fundefs_ctx -> Ensemble var :=
       | SBound_Fcons11_c:
           forall f t xs c fds v,
             List.In v xs ->
             bound_stem_fundefs_ctx (Fcons1_c f t xs c fds) v
       | SBound_Fcons12_c:
           forall f t xs c fds v,
             bound_stem_ctx c v ->
             bound_stem_fundefs_ctx (Fcons1_c f t xs c fds) v
       | SBound_Fcons2_c:
           forall f t xs e cfds v,
             bound_stem_fundefs_ctx cfds v ->
             bound_stem_fundefs_ctx (Fcons2_c f t xs e cfds) v.

  #[global] Hint Constructors bound_stem_ctx : core.
  #[global] Hint Constructors bound_stem_fundefs_ctx : core.


  Lemma bound_stem_Econstr_c x t ys c :
    Same_set _ (bound_stem_ctx (Econstr_c x t ys c))
             (Union var (bound_stem_ctx c) (Singleton _ x)).
  Proof.
    split; intros x' H; inv H; eauto. inv H0; eauto.
  Qed.

  Lemma bound_stem_Eproj_c v t n r c :
    Same_set _ (bound_stem_ctx (Eproj_c v t n r c))
             (Union var (bound_stem_ctx c) (Singleton _ v)).
  Proof.
    split; intros x' H; inv H; eauto. inv H0; eauto.
  Qed.

  Lemma bound_stem_Eletapp_c v f t ys c :
    Same_set _ (bound_stem_ctx (Eletapp_c v f t ys c))
             (Union var (bound_stem_ctx c) (Singleton _ v)).
  Proof.
    split; intros x' H; inv H; eauto; eauto. inv H0; eauto.
  Qed.

  Lemma bound_stem_Eprim_val_c x p c :
    Same_set _ (bound_stem_ctx (Eprim_val_c x p c))
             (Union var (bound_stem_ctx c) (Singleton _ x)).
  Proof.
    split; intros x' H; inv H; eauto. inv H0; eauto.
  Qed.

  Lemma bound_stem_Eprim_c x tau y c :
    Same_set _ (bound_stem_ctx (Eprim_c x tau y c))
             (Union var (bound_stem_ctx c) (Singleton _ x)).
  Proof.
    split; intros x' H; inv H; eauto. inv H0; eauto.
  Qed.

  Lemma bound_stem_Hole_c :
    Same_set _ (bound_stem_ctx Hole_c)
             (Empty_set var).
  Proof.
    split; intros x' H; inv H; eauto.
  Qed.

  Lemma bound_stem_Case_c :
    forall v  lce t c lce',
      Same_set _ (bound_stem_ctx (Ecase_c v lce t c lce'))
               (bound_stem_ctx c).
  Proof with eauto with Ensembles_DB.
    split; intros; intro; intros.
    - inversion H; subst; eauto.
    - constructor.
      auto.
  Qed.

  Lemma bound_stem_Fun1_c :
    forall fds c,
      Same_set _ (bound_stem_ctx (Efun1_c fds c))
               (Union _ (name_in_fundefs fds) (bound_stem_ctx c)).
  Proof.
    split; intros x H; inv H; eauto.
  Qed.

  Lemma bound_stem_Fun2_c :
    forall cfds e,
      Same_set _ (bound_stem_ctx (Efun2_c cfds e))
               (Union _ (names_in_fundefs_ctx cfds) (bound_stem_fundefs_ctx cfds)).
  Proof.
    split; intros x H; inv H; eauto.
  Qed.

  Lemma bound_stem_Fcons1_c :
    forall c v l e0 f,
      Same_set _ (bound_stem_fundefs_ctx (Fcons1_c v c l e0 f))
               (Union _ (bound_stem_ctx e0) (FromList l)).
  Proof.
    split; intros x H; inv H; eauto.
  Qed.

  Lemma bound_stem_Fcons2_c :
    forall c v l e0 f,
      Same_set _ (bound_stem_fundefs_ctx (Fcons2_c v c l e0 f))
               (bound_stem_fundefs_ctx f).
  Proof.
    split; intros x H; inv H; eauto.
  Qed.


  Ltac normalize_bound_stem_ctx :=
    match goal with
      | [ |- context[bound_stem_ctx Hole_c]] =>
        rewrite bound_stem_Hole_c
      | [|- context[bound_stem_ctx (Econstr_c _ _ _ _)]] =>
        rewrite bound_stem_Econstr_c
      | [|- context[bound_stem_ctx (Eproj_c _ _ _ _ _)]] =>
        rewrite bound_stem_Eproj_c
      | [|- context[bound_stem_ctx (Eletapp_c _ _ _ _ _)]] =>
        rewrite bound_stem_Eletapp_c
      | [|- context[bound_stem_ctx (Ecase_c _ _ _ _ _)]] =>
        rewrite bound_stem_Case_c
      | [ |- context[bound_stem_ctx (Efun1_c _ _)]] =>
        rewrite bound_stem_Fun1_c
      | [ |- context[bound_stem_ctx (Efun2_c _ _)] ] =>
        rewrite bound_stem_Fun2_c
      | [|- context[bound_stem_ctx (Eprim_val_c _ _ _)]] =>
        rewrite bound_stem_Eprim_val_c
      | [|- context[bound_stem_ctx (Eprim_c _ _ _ _)]] =>
        rewrite bound_stem_Eprim_c
      | [|- context[bound_stem_fundefs_ctx (Fcons1_c _ _ _ _ _)]] =>
        rewrite bound_stem_Fcons1_c
      | [|- context[bound_stem_fundefs_ctx (Fcons2_c _ _ _ _ _)]] =>
        rewrite bound_stem_Fcons2_c
    end.

  (*   Ltac normalize_bound_stem_ctx := *)
  (*   match goal with *)
  (*   | [|- context[bound_stem_ctx (Econstr_c _ _ _ _)]] => *)
  (*     rewrite bound_stem_Econstr_c *)
  (*   | [|- context[bound_stem_ctx (Eproj_c _ _ _ _ _)]] => *)
  (*     rewrite bound_stem_Eproj_c *)
  (*   | [|- context[bound_stem_ctx (Ecase_c _ _ _ _ _)]] => *)
  (*     rewrite bound_stem_Case_c *)
  (*   | [|- context[bound_stem_ctx (Eletapp_c _ _ _ _ _)]] => *)
  (*     rewrite bound_stem_Eletapp_c *)
  (*   | [|- context[bound_stem_ctx (Efun1_c _ _)]] => *)
  (*     rewrite bound_stem_Fun1_c *)
  (*   | [|- context[bound_stem_ctx (Efun2_c _ _)]] => *)
  (*     rewrite bound_stem_Fun2_c *)
  (*   | [|- context[bound_stem_ctx (Eprim_c _ _ _ _)]] => *)
  (*     rewrite bound_stem_Eprim_c *)
  (*   | [|- context[bound_stem_ctx Hole_c]] => *)
  (*     rewrite bound_stem_Hole_c *)
  (*   | [|- context[bound_stem_fundefs_ctx (Fcons1_c _ _ _ _ _)]] => *)
  (*     rewrite bound_stem_Fcons1_c *)
  (*   | [|- context[bound_stem_fundefs_ctx (Fcons2_c _ _ _ _ _)]] => *)
  (*     rewrite bound_stem_Fcons2_c *)
  (* end. *)

  Ltac normalize_bound_stem_ctx_in_ctx :=
    match goal with
      | [ H: context[bound_stem_ctx Hole_c] |- _] =>
        rewrite bound_stem_Hole_c in H
      | [ H : context[bound_stem_ctx (Econstr_c _ _ _ _)] |- _ ] =>
        rewrite bound_stem_Econstr_c in H
      | [ H : context[bound_stem_ctx (Eproj_c _ _ _ _ _)]  |- _ ] =>
        rewrite bound_stem_Eproj_c in H
      | [ H : context[bound_stem_ctx (Eletapp_c _ _ _ _ _)]  |- _ ] =>
        rewrite bound_stem_Eletapp_c in H
      | [H: context[bound_stem_ctx (Ecase_c _ _ _ _ _)] |- _] =>
        rewrite bound_stem_Case_c in H
      | [ H : context[bound_stem_ctx (Efun1_c _ _)] |- _ ] =>
        rewrite bound_stem_Fun1_c in H
      | [ H : context[bound_stem_ctx (Efun2_c _ _)] |- _ ] =>
        rewrite bound_stem_Fun2_c in H
      | [ H : context[bound_stem_ctx (Eprim_val_c _ _ _)] |- _ ] =>
        rewrite bound_stem_Eprim_val_c in H
      | [ H : context[bound_stem_ctx (Eprim_c _ _ _ _)] |- _ ] =>
        rewrite bound_stem_Eprim_c in H
      | [H:context[bound_stem_fundefs_ctx (Fcons1_c _ _ _ _ _)] |- _] =>
        rewrite bound_stem_Fcons1_c in H
      | [H: context[bound_stem_fundefs_ctx (Fcons2_c _ _ _ _ _)] |- _] =>
        rewrite bound_stem_Fcons2_c in H
    end.


  (* variables bound NOT  on the way to the hole *)
  Inductive bound_not_stem_ctx: exp_ctx -> Ensemble var  :=
  | NBound_Constr_c: forall c v v' t ys,
                       bound_not_stem_ctx c v ->
                       bound_not_stem_ctx (Econstr_c v' t ys c) v
  | NBound_Proj_c: forall  t n r c v' v,
                     bound_not_stem_ctx c v' ->
                     bound_not_stem_ctx (Eproj_c v t n r c) v'
  | NBound_Prim_val_c: forall p c v' v,
                     bound_not_stem_ctx c v' ->
                     bound_not_stem_ctx (Eprim_val_c v p c) v'
  | NBound_Prim_c: forall  t r c v' v,
                     bound_not_stem_ctx c v' ->
                     bound_not_stem_ctx (Eprim_c v t r c) v'
  | NBound_Letapp_c: forall f t ys c v' v,
                       bound_not_stem_ctx c v' ->
                       bound_not_stem_ctx (Eletapp_c v f t ys c) v'
  | NBound_Case2_c: forall v v' e lce t' t c lce',
                      bound_var e v' ->
                      List.In (t',e) lce ->
                      bound_not_stem_ctx (Ecase_c v lce t c lce') v'
  | NBound_Case3_c: forall v v' e lce t' t c lce',
                      bound_var e v' ->
                      List.In (t',e) lce' ->
                      bound_not_stem_ctx (Ecase_c v lce t c lce') v'
  | NBound_Case1_c: forall v v' lce t c lce',
                      bound_not_stem_ctx c v' ->
                      bound_not_stem_ctx (Ecase_c v lce t c lce') v'
  | NBound_Fun11_c: forall fds v c,
                      ~ name_in_fundefs fds v ->
                      bound_var_fundefs fds v ->
                      bound_not_stem_ctx (Efun1_c fds c) v
  | NBound_Fun12_c: forall fds v c,
                      bound_not_stem_ctx c v ->
                      bound_not_stem_ctx (Efun1_c fds c) v
  | NBound_Fun1_c: forall cfds v e,
                     bound_not_stem_fundefs_ctx cfds v ->
                     bound_not_stem_ctx (Efun2_c cfds e) v
  | NBound_Fun2_c: forall cfds e v,
                     bound_var e v ->
                     bound_not_stem_ctx (Efun2_c cfds e) v
  with bound_not_stem_fundefs_ctx: fundefs_ctx -> Ensemble var :=
       | NBound_Fcons11_c: forall f t xs c fds v,
                             bound_not_stem_ctx c v ->
                             bound_not_stem_fundefs_ctx (Fcons1_c f t xs c fds) v
       | NBound_Fcons12_c: forall f t xs c fds v,
                             ~ name_in_fundefs fds v ->
                             bound_var_fundefs fds v ->
                             bound_not_stem_fundefs_ctx (Fcons1_c f t xs c fds) v
       | NBound_Fcons21_c: forall f t xs e cfds v,
                             bound_not_stem_fundefs_ctx cfds v ->
                             bound_not_stem_fundefs_ctx (Fcons2_c f t xs e cfds) v
       | NBound_Fcons22_c: forall f t xs e cfds v,
                             bound_var e v ->
                             bound_not_stem_fundefs_ctx (Fcons2_c f t xs e cfds) v
       | NBound_Fcons23_c:
           forall f t xs e cfds v,
             FromList xs v ->
             bound_not_stem_fundefs_ctx (Fcons2_c f t xs e cfds) v.



  #[global] Hint Constructors bound_not_stem_ctx : core.
  #[global] Hint Constructors bound_not_stem_fundefs_ctx : core.

  Lemma bound_not_stem_Econstr_c x t ys c :
    Same_set _ (bound_not_stem_ctx (Econstr_c x t ys c))
             (bound_not_stem_ctx c).
  Proof.
    split; intros x' H;  eauto. inv H; eauto.
  Qed.

  Lemma bound_not_stem_Eproj_c v t n r c :
    Same_set _ (bound_not_stem_ctx (Eproj_c v t n r c))
             (bound_not_stem_ctx c).
  Proof.
    split; intros x' H; auto.  inv H; auto.
  Qed.

  Lemma bound_not_stem_Eletapp_c v f t ys c :
    Same_set _ (bound_not_stem_ctx (Eletapp_c v f t ys c))
             (bound_not_stem_ctx c).
  Proof.
    split; intros x' H; auto.  inv H; auto.
  Qed.

  Lemma bound_not_stem_Eprim_val_c x p c :
    Same_set _ (bound_not_stem_ctx (Eprim_val_c x p c))
             (bound_not_stem_ctx c).
  Proof.
    split; intros x' H; auto. inv H; auto.
  Qed.

  Lemma bound_not_stem_Eprim_c x tau y c :
    Same_set _ (bound_not_stem_ctx (Eprim_c x tau y c))
             (bound_not_stem_ctx c).
  Proof.
    split; intros x' H; auto. inv H; auto.
  Qed.

  Lemma bound_not_stem_Hole_c :
    Same_set _ (bound_not_stem_ctx Hole_c)
             (Empty_set var).
  Proof.
    split; intros x' H; inv H; eauto.
  Qed.

  Lemma bound_not_stem_Case_c :
    forall v  lce t c lce',
      Same_set _ (bound_not_stem_ctx (Ecase_c v lce t c lce'))
               (Union _ (bound_not_stem_ctx c) (Union _ (bound_var (Ecase v lce))
                                                      (bound_var (Ecase v lce')))).
  Proof with eauto with Ensembles_DB.
    split; intros; intro; intros.
    - inversion H; subst; eauto.
    - inv H; auto.
      inv H0. inv H.
      eapply NBound_Case2_c; eauto.
      inv H.
      eapply NBound_Case3_c; eauto.
  Qed.


  Lemma bound_not_stem_Fun1_c :
    forall fds c,
      Same_set _ (bound_not_stem_ctx (Efun1_c fds c))
               (Union _ (Setminus _ (bound_var_fundefs fds) (name_in_fundefs fds)) (bound_not_stem_ctx c)).
  Proof.
    split; intros x H; inv H; auto.
    left. split; auto.
    inv H0. auto.
  Qed.

  Lemma bound_not_stem_Fun2_c :
    forall cfds e,
      Same_set _ (bound_not_stem_ctx (Efun2_c cfds e))
               (Union _ (bound_var e) (bound_not_stem_fundefs_ctx cfds)).
  Proof.
    split; intros x H; inv H; eauto.
  Qed.

  Lemma bound_not_stem_Fcons1_c :
    forall c v l e0 f,
      Same_set _ (bound_not_stem_fundefs_ctx (Fcons1_c v c l e0 f))
               (Union _ (bound_not_stem_ctx e0) (Setminus _ (bound_var_fundefs f) (name_in_fundefs f))).
  Proof.
    split; intros x H; auto.
    inv H. auto. right; split; auto.
    inv H; auto. inv H0; auto.
  Qed.

  Lemma bound_not_stem_Fcons2_c :
    forall c v l e0 f,
      Same_set _ (bound_not_stem_fundefs_ctx (Fcons2_c v c l e0 f))
               (Union _ (Union _ (bound_var e0) (FromList l)) (bound_not_stem_fundefs_ctx f)).
  Proof.
    split; intros x H; inv H; eauto.
    inv H0; auto.
  Qed.

  Ltac normalize_bound_not_stem_ctx :=
    match goal with
    | [ |- context[bound_not_stem_ctx Hole_c]] =>
      rewrite bound_not_stem_Hole_c
    | [|- context[bound_not_stem_ctx (Econstr_c _ _ _ _)]] =>
      rewrite bound_not_stem_Econstr_c
    | [|- context[bound_not_stem_ctx (Eproj_c _ _ _ _ _)]] =>
      rewrite bound_not_stem_Eproj_c
    | [|- context[bound_not_stem_ctx (Eletapp_c _ _ _ _ _)]] =>
      rewrite bound_not_stem_Eletapp_c
    | [|- context[bound_not_stem_ctx (Ecase_c _ _ _ _ _)]] =>
      rewrite bound_not_stem_Case_c
    | [ |- context[bound_not_stem_ctx (Efun1_c _ _)]] =>
      rewrite bound_not_stem_Fun1_c
    | [ |- context[bound_not_stem_ctx (Efun2_c _ _)] ] =>
      rewrite bound_not_stem_Fun2_c
    | [|- context[bound_not_stem_ctx (Eprim_val_c _ _ _)]] =>
      rewrite bound_not_stem_Eprim_val_c
    | [|- context[bound_not_stem_ctx (Eprim_c _ _ _ _)]] =>
      rewrite bound_not_stem_Eprim_c
    | [|- context[bound_not_stem_fundefs_ctx (Fcons1_c _ _ _ _ _)]] =>
      rewrite bound_not_stem_Fcons1_c
    | [|- context[bound_not_stem_fundefs_ctx (Fcons2_c _ _ _ _ _)]] =>
      rewrite bound_not_stem_Fcons2_c
    end.

  Ltac normalize_bound_not_stem_ctx_in_ctx :=
    match goal with
    | [ H: context[bound_not_stem_ctx Hole_c] |- _] =>
      rewrite bound_not_stem_Hole_c in H
    | [ H : context[bound_not_stem_ctx (Econstr_c _ _ _ _)] |- _ ] =>
      rewrite bound_not_stem_Econstr_c in H
    | [ H : context[bound_not_stem_ctx (Eproj_c _ _ _ _ _)]  |- _ ] =>
      rewrite bound_not_stem_Eproj_c in H
    | [H: context[bound_not_stem_ctx (Ecase_c _ _ _ _ _)] |- _] =>
      rewrite bound_not_stem_Case_c in H
    | [ H : context[bound_not_stem_ctx (Efun1_c _ _)] |- _ ] =>
      rewrite bound_not_stem_Fun1_c in H
    | [ H : context[bound_not_stem_ctx (Efun2_c _ _)] |- _ ] =>
      rewrite bound_not_stem_Fun2_c in H
    | [ H : context[bound_not_stem_ctx (Eprim_val_c _ _ _)] |- _ ] =>
      rewrite bound_not_stem_Eprim_val_c in H
    | [ H : context[bound_not_stem_ctx (Eprim_c _ _ _ _)] |- _ ] =>
      rewrite bound_not_stem_Eprim_c in H
    | [H:context[bound_not_stem_fundefs_ctx (Fcons1_c _ _ _ _ _)] |- _] =>
      rewrite bound_not_stem_Fcons1_c in H
    | [H: context[bound_not_stem_fundefs_ctx (Fcons2_c _ _ _ _ _)] |- _] =>
      rewrite bound_not_stem_Fcons2_c in H
    end.


  Theorem bound_var_stem_or_not_stem_mut:
    (forall c, bound_var_ctx c <--> bound_not_stem_ctx c :|: bound_stem_ctx c) /\
    (forall f,bound_var_fundefs_ctx f <--> names_in_fundefs_ctx f :|: (bound_not_stem_fundefs_ctx f :|: bound_stem_fundefs_ctx f)).
  Proof.
    apply exp_fundefs_ctx_mutual_ind;
      intros; try normalize_bound_var_ctx; try normalize_bound_stem_ctx;
        try normalize_bound_not_stem_ctx; try rewrite H; eauto 25 with Ensembles_DB.
    - split; eauto 25 with Ensembles_DB.
    - assert (Hn := Decidable_name_in_fundefs f4).
      split; intro; intros. inv H0; eauto 25 with Ensembles_DB.
      inv Hn. specialize (Dec x). inv Dec; eauto. left. left. split; auto.
      inv H1; eauto with Ensembles_DB.
      inv H0. inv H1. inv H0; auto.
      auto. inv H1; auto.
      apply name_in_fundefs_bound_var_fundefs in H0. auto.
    - split; intro; intros H0; inv H0; eauto 25 with Ensembles_DB.
      inv H1; auto. inv H0; auto. inv H1; auto. inv H1; auto.
    - assert (Hf6 := Decidable_name_in_fundefs f6).
      split; intro; intros H0. inv H0.
      left; constructor; auto.
      inv H1. right; right; auto.
      inv H0; auto. inv H1; auto.
      inv Hf6. specialize (Dec x). inv Dec. left. constructor 2; auto.
      right. left. right.  split; auto.
      inv H0. inv H1. auto. apply name_in_fundefs_bound_var_fundefs in H0. auto.
      inv H1; auto. inv H0; auto. inv H1. auto.
      inv H0; auto.
    - split; intro; intros H0; inv H0; eauto 25 with Ensembles_DB.
      left; constructor; auto.
      inv H1; auto. inv H0; auto. inv H1; auto. left; constructor 2; auto.
      inv H0; auto.
      inv H1; auto.
      inv H1; auto. inv H0; auto. inv H1; auto. right. right. right. auto.
      right. right. right. auto.
  Qed.

  Theorem bound_stem_var:
    (forall c, bound_stem_ctx c \subset bound_var_ctx c) /\
    (forall fc, bound_stem_fundefs_ctx fc \subset bound_var_fundefs_ctx fc).
  Proof.
    apply exp_fundefs_ctx_mutual_ind; intros; normalize_bound_var_ctx'; normalize_bound_stem_ctx; eauto with Ensembles_DB.
    assert (Hf4 := name_in_fundefs_bound_var_fundefs f4).
    eauto with Ensembles_DB.

    assert (Hf5 := name_in_fundefs_ctx_bound_var_fundefs f5).
    eauto with Ensembles_DB.
  Qed.

  Theorem bound_var_stem_or_not_stem:
    forall c, bound_var_ctx c <--> (bound_not_stem_ctx c :|: bound_stem_ctx c).
  Proof.
    intros.
    apply bound_var_stem_or_not_stem_mut.
  Qed.

  Theorem bound_var_fundefs_stem_or_not_stem:
    forall f, bound_var_fundefs_ctx f <--> (names_in_fundefs_ctx f :|: (bound_not_stem_fundefs_ctx f :|: bound_stem_fundefs_ctx f)).
  Proof.
    intro.
    apply bound_var_stem_or_not_stem_mut.
  Qed.

  Theorem bound_stem_app_fundefs_ctx:
    forall c fd fd' f tau xs,
      (bound_stem_fundefs_ctx (app_fundefs_ctx fd (Fcons1_c f tau xs c fd'))) <--> (Union _ (bound_stem_ctx c) (FromList xs)) .
  Proof.
    induction fd; intros.
    - simpl.
      rewrite bound_stem_Fcons2_c. eapply IHfd.
    - simpl. rewrite bound_stem_Fcons1_c.
      reflexivity.
  Qed.

  Lemma bound_stem_ctx_dec:
    (forall c, Decidable (bound_stem_ctx c)).
  Proof.
    eapply ctx_exp_mut' with (P0 := fun c => Decidable (bound_stem_fundefs_ctx c));
    split; intro x.
    - right; intro; inv H.
    - destruct H as [Dec]; destruct (Dec x); auto.
      destruct (var_dec v x); subst; auto.
      right; intro Hbv; inv Hbv; auto.
    - destruct H as [Dec]; destruct (Dec x); auto.
      destruct (var_dec v x); subst; auto.
      right; intro Hbv; inv Hbv; auto.
    - destruct H as [Dec]; destruct (Dec x); auto.
      destruct (var_dec v x); subst; auto.
      right; intro Hbv; inv Hbv; auto.
    - destruct H as [Dec]; destruct (Dec x); auto.
      destruct (var_dec v x); subst; auto.
      right; intro Hbv; inv Hbv; auto.
    - destruct H as [Dec]; destruct (Dec x); auto.
      destruct (var_dec v x); subst; auto.
      right; intro Hbv; inv Hbv; auto.
    - destruct H as [Dec]; destruct (Dec x) as [Hin | Hnin]; auto.
      right. intro Hc. apply Hnin. inv Hc. auto.
    - destruct H as [Dec]; destruct (Dec x) as [Hin | Hnin]; auto.
      assert (Hn := Decidable_name_in_fundefs f).
      destruct Hn as [Decf]. destruct (Decf x); eauto.
      right. intro Hc. apply Hnin. inv Hc. exfalso; auto. auto.
    - destruct H as [Dec]; destruct (Dec x) as [Hin | Hnin]; auto.
      assert (Hf := Decidable_name_in_fundefs_ctx f).
      destruct Hf as [Decf]. destruct (Decf x); eauto.
      right. intro Hc. apply Hnin. inv Hc. exfalso; auto. auto.
    - destruct H as [Dec]; destruct (Dec x) as [Hin | Hnin]; auto.
      destruct (in_dec var_dec x l); auto.
      right. intro Hc. apply Hnin. inv Hc. exfalso; auto. auto.
    - destruct H as [Dec]; destruct (Dec x) as [Hin | Hnin]; auto.
      right. intro Hc. apply Hnin. inv Hc. exfalso; auto.
  Qed.

  Lemma bound_stem_fundefs_ctx_dec:
    (forall c, Decidable (bound_stem_fundefs_ctx c)).
  Proof.
    eapply ctx_fundefs_mut' with (P := fun c => Decidable (bound_stem_ctx c));
    split; intro x.
    - right; intro; inv H.
    - destruct H as [Dec]; destruct (Dec x); auto.
      destruct (var_dec v x); subst; auto.
      right; intro Hbv; inv Hbv; auto.
    - destruct H as [Dec]; destruct (Dec x); auto.
      destruct (var_dec v x); subst; auto.
      right; intro Hbv; inv Hbv; auto.
    - destruct H as [Dec]; destruct (Dec x); auto.
      destruct (var_dec v x); subst; auto.
      right; intro Hbv; inv Hbv; auto.
    - destruct H as [Dec]; destruct (Dec x); auto.
      destruct (var_dec v x); subst; auto.
      right; intro Hbv; inv Hbv; auto.
    - destruct H as [Dec]; destruct (Dec x); auto.
      destruct (var_dec v x); subst; auto.
      right; intro Hbv; inv Hbv; auto.
    - destruct H as [Dec]; destruct (Dec x) as [Hin | Hnin]; auto.
      right. intro Hc. apply Hnin. inv Hc. auto.
    - destruct H as [Dec]; destruct (Dec x) as [Hin | Hnin]; auto.
      assert (Hn := Decidable_name_in_fundefs f).
      destruct Hn as [Decf]. destruct (Decf x); eauto.
      right. intro Hc. apply Hnin. inv Hc. exfalso; auto. auto.
    - destruct H as [Dec]; destruct (Dec x) as [Hin | Hnin]; auto.
      assert (Hf := Decidable_name_in_fundefs_ctx f).
      destruct Hf as [Decf]. destruct (Decf x); eauto.
      right. intro Hc. apply Hnin. inv Hc. exfalso; auto. auto.
    - destruct H as [Dec]; destruct (Dec x) as [Hin | Hnin]; auto.
      destruct (in_dec var_dec x l); auto.
      right. intro Hc. apply Hnin. inv Hc. exfalso; auto. auto.
    - destruct H as [Dec]; destruct (Dec x) as [Hin | Hnin]; auto.
      right. intro Hc. apply Hnin. inv Hc. exfalso; auto.
  Qed.

  (** The set of bound variables of a composed context is equal to the union of the sets of bound variables of its constituents *)
  Theorem bound_stem_comp_ctx_mut:
    forall c', (forall c, (bound_stem_ctx c :|: bound_stem_ctx c') <--> (bound_stem_ctx (comp_ctx_f c c'))) /\
          (forall fc, (bound_stem_fundefs_ctx fc :|: bound_stem_ctx c') <--> (bound_stem_fundefs_ctx (comp_f_ctx_f fc c'))).
  Proof.
    intro c'; apply exp_fundefs_ctx_mutual_ind; intros; simpl; repeat normalize_bound_stem_ctx; eauto 25 with Ensembles_DB.
    -  rewrite <- H.
       rewrite <- Union_assoc.
       rewrite Union_commut with (s1 := [set v]).
       eauto 25 with Ensembles_DB.
    - rewrite <- H.
      rewrite <- Union_assoc.
      rewrite Union_commut with (s1 := [set v]).
      eauto 25 with Ensembles_DB.
    - rewrite <- H.
      rewrite <- Union_assoc.
      rewrite Union_commut with (s1 := [set v]).
      eauto 25 with Ensembles_DB.
    - rewrite <- H.
      rewrite <- Union_assoc.
      rewrite Union_commut with (s1 := [set v]).
      eauto 25 with Ensembles_DB.
    - rewrite <- H.
      rewrite <- Union_assoc.
      rewrite Union_commut with (s1 := [set v]).
      eauto 25 with Ensembles_DB.
    - rewrite <- H.
      rewrite <- Union_assoc.
      reflexivity.
    - assert (Hf5 := name_in_fundefs_ctx_comp c' f5).
      rewrite Hf5.
      rewrite <- H.
      eauto 25 with Ensembles_DB.
    - rewrite <- H.
      split;
        eauto 25 with Ensembles_DB.
  Qed.

  (** Free variables of a composed context come from the outer context
      or the inner context (minus variables bound by the outer). *)
  Lemma occurs_free_ctx_comp (C1 C2 : exp_ctx) :
    occurs_free_ctx (comp_ctx_f C1 C2) \subset
    occurs_free_ctx C1 :|: (occurs_free_ctx C2 \\ bound_stem_ctx C1).
  Proof.
    revert C2.
    eapply ctx_exp_mut with (P := fun C1 =>
                                    forall C2,
                                      occurs_free_ctx (comp_ctx_f C1 C2) \subset
                                                      occurs_free_ctx C1 :|: (occurs_free_ctx C2 \\ bound_stem_ctx C1))
                            (P0 := fun F =>
                                     forall C,
                                       occurs_free_fundefs_ctx (comp_f_ctx_f F C) \subset
                                                               occurs_free_fundefs_ctx F :|: (occurs_free_ctx C \\ (names_in_fundefs_ctx F :|: bound_stem_fundefs_ctx F))); intros.
    - simpl. normalize_occurs_free_ctx. normalize_bound_stem_ctx. sets.
    - simpl. repeat normalize_occurs_free_ctx.
      repeat normalize_bound_stem_ctx.
      eapply Union_Included. now sets.
      eapply Included_trans. eapply Included_Setminus_compat. eapply H. reflexivity.
      rewrite Setminus_Union_distr. now sets.
    - simpl. repeat normalize_occurs_free_ctx.
      repeat normalize_bound_stem_ctx. repeat normalize_bound_var.
      eapply Union_Included. now sets.
      eapply Included_trans. eapply Included_Setminus_compat. eapply H. reflexivity.
      rewrite Setminus_Union_distr. now sets.
    - simpl. repeat normalize_occurs_free_ctx.
      repeat normalize_bound_stem_ctx. repeat normalize_bound_var.
      eapply Included_trans. eapply Included_Setminus_compat. eapply H. reflexivity.
      rewrite Setminus_Union_distr.
      eapply Union_Included; now sets.
    - simpl. repeat normalize_occurs_free_ctx.
      repeat normalize_bound_stem_ctx. repeat normalize_bound_var.
      eapply Union_Included. now sets.
      eapply Included_trans. eapply Included_Setminus_compat. eapply H. reflexivity.
      rewrite Setminus_Union_distr.
      eapply Union_Included; now sets.
    - simpl. repeat normalize_occurs_free_ctx.
      repeat normalize_bound_stem_ctx. repeat normalize_bound_var.
      eapply Union_Included. now sets.
      eapply Included_trans. eapply Included_Setminus_compat. eapply H. reflexivity.
      rewrite Setminus_Union_distr.
      eapply Union_Included; now sets.
    - simpl. repeat normalize_occurs_free_ctx.
      repeat normalize_bound_stem_ctx. repeat normalize_bound_var.
      eapply Union_Included. now sets.
      eapply Union_Included.
      eapply Included_trans. eapply H. now sets.
      now sets.
    - simpl. repeat repeat normalize_occurs_free_ctx.
      repeat normalize_bound_stem_ctx. repeat normalize_bound_var.
      eapply Union_Included. now sets.
      eapply Included_trans. eapply Included_Setminus_compat. eapply H. reflexivity.
      rewrite Setminus_Union_distr.
      eapply Union_Included; now sets.
    - simpl. repeat normalize_occurs_free_ctx.
      repeat normalize_bound_stem_ctx. repeat normalize_bound_var.
      eapply Union_Included.
      eapply Included_trans. eapply H. now sets.
      rewrite name_in_fundefs_ctx_comp. now sets.
    - simpl. repeat normalize_occurs_free_ctx.
      eapply Union_Included; [ | now sets ].
      eapply Setminus_Included_Included_Union.
      eapply Included_trans. eapply H.
      eapply Union_Included.
      rewrite <- !Union_assoc.
      rewrite <- Union_Included_Union_Setminus with (s3 := (v |: (FromList l :|: name_in_fundefs f))).
      now sets. now tci. now sets.
      normalize_bound_stem_ctx.
      rewrite (Union_commut (bound_stem_ctx e) (FromList l)).
      rewrite !Union_assoc.
      rewrite (Union_commut _ (bound_stem_ctx e)).
      rewrite <- Setminus_Union with (s2 := bound_stem_ctx e).
      rewrite <- ! Union_assoc.
      rewrite <- Union_Included_Union_Setminus with (s3 := (v |: (name_in_fundefs f :|: FromList l))).
      now sets. now tci. now sets.
    - simpl. repeat normalize_occurs_free_ctx. repeat normalize_bound_stem_ctx.
      eapply Union_Included.
      + rewrite name_in_fundefs_ctx_comp. now sets.
      + eapply Included_trans. eapply Included_Setminus_compat. eapply H. reflexivity.
        rewrite !Setminus_Union_distr.
        eapply Union_Included. now sets. now xsets.
  Qed.

  (** Free variables of a context application are from the context
      or from the expression (minus variables bound by the context). *)
  Lemma occurs_free_ctx_app (C : exp_ctx) (e : exp) :
    occurs_free (C |[ e ]|) \subset
    occurs_free_ctx C :|: (occurs_free e \\ bound_stem_ctx C).
  Proof.
    revert e.
    eapply ctx_exp_mut with (P := fun C =>
                                    forall e,
                                      occurs_free (C |[ e ]|) \subset
                                      occurs_free_ctx C :|: (occurs_free e \\ bound_stem_ctx C))
                            (P0 := fun F =>
                                     forall e,
                                       occurs_free_fundefs (F <[ e ]>) \subset
                                        occurs_free_fundefs_ctx F :|: (occurs_free e \\ (names_in_fundefs_ctx F :|: bound_stem_fundefs_ctx F))); intros.
    - simpl. normalize_occurs_free_ctx. normalize_bound_stem_ctx. sets.
    - simpl. repeat normalize_occurs_free. repeat normalize_occurs_free_ctx.
      repeat normalize_bound_stem_ctx. repeat normalize_bound_var.
      eapply Union_Included. now sets.
      eapply Included_trans. eapply Included_Setminus_compat. eapply H. reflexivity.
      rewrite Setminus_Union_distr.
      eapply Union_Included; now sets.
    - simpl. repeat normalize_occurs_free. repeat normalize_occurs_free_ctx.
      repeat normalize_bound_stem_ctx. repeat normalize_bound_var.
      eapply Union_Included. now sets.
      eapply Included_trans. eapply Included_Setminus_compat. eapply H. reflexivity.
      rewrite Setminus_Union_distr.
      eapply Union_Included; now sets.
    - simpl. repeat normalize_occurs_free. repeat normalize_occurs_free_ctx.
      repeat normalize_bound_stem_ctx. repeat normalize_bound_var.
      eapply Included_trans. eapply Included_Setminus_compat. eapply H. reflexivity.
      rewrite Setminus_Union_distr.
      eapply Union_Included; now sets.
    - simpl. repeat normalize_occurs_free. repeat normalize_occurs_free_ctx.
      repeat normalize_bound_stem_ctx. repeat normalize_bound_var.
      eapply Union_Included. now sets.
      eapply Included_trans. eapply Included_Setminus_compat. eapply H. reflexivity.
      rewrite Setminus_Union_distr.
      eapply Union_Included; now sets.
    - simpl. repeat normalize_occurs_free. repeat normalize_occurs_free_ctx.
      repeat normalize_bound_stem_ctx. repeat normalize_bound_var.
      eapply Union_Included. now sets.
      eapply Included_trans. eapply Included_Setminus_compat. eapply H. reflexivity.
      rewrite Setminus_Union_distr.
      eapply Union_Included; now sets.
    - simpl. repeat normalize_occurs_free. repeat normalize_occurs_free_ctx.
      repeat normalize_bound_stem_ctx. repeat normalize_bound_var.
      eapply Union_Included. now sets.
      eapply Union_Included. now sets.
      eapply Union_Included.
      + eapply Included_trans. eapply H.
        eapply Union_Included; now sets.
      + now sets.
    - simpl. repeat normalize_occurs_free. repeat normalize_occurs_free_ctx.
      repeat normalize_bound_stem_ctx. repeat normalize_bound_var.
      eapply Union_Included. now sets.
      eapply Included_trans. eapply Included_Setminus_compat. eapply H. reflexivity.
      rewrite Setminus_Union_distr.
      eapply Union_Included; now sets.
    - simpl. repeat normalize_occurs_free. repeat normalize_occurs_free_ctx.
      repeat normalize_bound_stem_ctx. repeat normalize_bound_var.
      eapply Union_Included.
      + eapply Included_trans. eapply H. now sets.
      + rewrite <- name_in_fundefs_ctx_ctx at 1. now sets.
    - simpl. repeat normalize_occurs_free. repeat normalize_occurs_free_ctx.
      repeat normalize_bound_stem_ctx.
      eapply Union_Included; [ | now sets ].
      eapply Setminus_Included_Included_Union.
      eapply Included_trans. eapply H.
      eapply Union_Included.
      + rewrite <- !Union_assoc.
        rewrite <- Union_Included_Union_Setminus with (s3 := (v |: (FromList l :|: name_in_fundefs f))).
        now sets. now tci. now sets.
      + rewrite (Union_commut (bound_stem_ctx e) (FromList l)).
        rewrite !Union_assoc.
        rewrite (Union_commut _ (bound_stem_ctx e)).
        rewrite <- Setminus_Union with (s2 := bound_stem_ctx e).
        rewrite <- ! Union_assoc.
        rewrite <- Union_Included_Union_Setminus with (s3 := (v |: (name_in_fundefs f :|: FromList l))).
        now sets. now tci. now sets.
    - simpl. repeat normalize_occurs_free_ctx. repeat normalize_bound_stem_ctx.
      repeat normalize_occurs_free.
      eapply Union_Included.
      + rewrite <- name_in_fundefs_ctx_ctx. now sets.
      + eapply Included_trans. eapply Included_Setminus_compat. eapply H. reflexivity.
        rewrite !Setminus_Union_distr.
        eapply Union_Included. now sets. now xsets.
  Qed.
