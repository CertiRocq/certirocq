(* Definition and semantics preservation proof for alpha conversion. Part of the CertiRocq project.
 * Author: Anonymized, 2016
 *)


Require Import LambdaANF.term LambdaANF.ctx LambdaANF.term_util LambdaANF.set_util LambdaANF.identifiers LambdaANF.Ensembles_util LambdaANF.List_util
        LambdaANF.eval LambdaANF.logical_relations LambdaANF.functions LambdaANF.tactics LambdaANF.map_util LambdaANF.rename.
Require Import compcert.lib.Coqlib.
From Stdlib Require Import ZArith.Znumtheory Relations.Relations Arith.Wf_nat.
From Stdlib Require Import Lists.List MSets.MSets MSets.MSetRBT Numbers.BinNums
        NArith.BinNat PArith.BinPos Sets.Ensembles micromega.Lia.

Import ListNotations.

Open Scope ctx_scope.
Open Scope fun_scope.
Close Scope Z_scope.


Fixpoint extend_fundefs (f: var -> var) (B B' : fundefs) : (var -> var) :=
  match B with
    | Fnil => f
    | Fcons g _ _ _ B =>
      match B' with
        | Fnil => f
        | Fcons g' _ _ _ B' =>
          (extend_fundefs f B B'){g ~> g'}
      end
  end.

#[global] Instance Proper_extend_fundefs : Proper (f_eq ==> eq ==> eq ==> f_eq) extend_fundefs.
Proof.
  intros f1 f2 Hfeq y1 y2 Heq1 x1 x2 Heq2 z1.
  subst. revert x2; induction y2; intros x2; simpl; eauto.
  destruct x2; simpl; eauto.
  destruct (peq v z1); subst.
  - rewrite !extend_gss. reflexivity.
  - rewrite !extend_gso; eauto.
Qed.


Lemma extend_fundefs_name_in_fundefs f B1 B2 x :
  term_util.numOf_fundefs B1 = term_util.numOf_fundefs B2 ->
  x \in name_in_fundefs B1 ->
  exists y, extend_fundefs f B1 B2 x = y /\ y \in name_in_fundefs B2.
Proof.
  revert B2. induction B1; intros B2 Heq Hin; destruct B2; simpl in *; try congruence.
  - destruct (var_dec v x); subst.
    + eexists. rewrite extend_gss. split; eauto.
    + inv Hin. inv H. congruence.
      inv Heq. edestruct IHB1; eauto. destructAll.
      rewrite extend_gso; eauto.
  - inv Hin.
Qed.

Lemma extend_fundefs_not_name_in_fundefs f B1 B2 x :
  ~ x \in name_in_fundefs B1 ->
  extend_fundefs f B1 B2 x = f x.
Proof.
  revert B2. induction B1; intros B2 Hnin; destruct B2; simpl; eauto.
  simpl in *. rewrite extend_gso; eauto.

  intros Hc; subst. eauto.
Qed.


(* These are required to make sure that at every step of extending the function
   it is injective, which is useful for proofs with induction on the list or fundefs *)
Inductive construct_lst_injection : (var -> var) -> list var -> list var -> (var -> var) -> Prop :=
| Inj_nil :
    forall f, construct_lst_injection f [] [] f
| Inf_cons :
    forall f f' x xs y ys,
      construct_lst_injection f xs ys f' ->
      injective_subdomain (FromList (x :: xs)) (f' {x ~> y}) ->
      construct_lst_injection f (x :: xs) (y :: ys) (f' {x ~> y}).

Inductive construct_fundefs_injection : (var -> var) -> fundefs -> fundefs -> (var -> var) -> Prop :=
| Inj_Fnil :
    forall f, construct_fundefs_injection f Fnil Fnil f
| Inf_Fcons :
    forall f f' g1 t1 xs1 e1 B1 g2 t2 xs2 e2 B2,
      construct_fundefs_injection f B1 B2 f' ->
      injective_subdomain (g1 |: name_in_fundefs B1) (f' {g1 ~> g2}) ->
      construct_fundefs_injection f (Fcons g1 t1 xs1 e1 B1) (Fcons g2 t2 xs2 e2 B2) (f' {g1 ~> g2}).


(** α-equivalent terms *)
Inductive Alpha_conv :
  exp -> exp -> (* the two related expressions *)
  (var -> var) -> (* The current renaming of fvs *)
  Prop :=
| Alpha_Econstr :
    forall x x' t ys ys' e e' f,
      Forall2 (fun y y' => f y = y') ys ys' ->
      ~ x' \in image f (occurs_free e) :|: bound_var e ->
      Alpha_conv e e' (f {x ~> x'}) ->
      Alpha_conv (Econstr x t ys e) (Econstr x' t ys' e') f
| Alpha_Eproj :
    forall x x' tau N y y' e e' f,
      f y = y' ->
      ~ x' \in image f (occurs_free e) :|: bound_var e ->
      Alpha_conv e e' (f {x ~> x'}) ->
      Alpha_conv (Eproj x tau N y e) (Eproj x' tau N y' e') f
| Alpha_Eletapp :
    forall x x' g g' tau ys ys' e e' f,
      Forall2 (fun y y' => f y = y') ys ys' ->
      f g = g' ->
      ~ x' \in image f (occurs_free e) :|: bound_var e ->
      Alpha_conv e e' (f {x ~> x'}) ->
      Alpha_conv (Eletapp x g tau ys e) (Eletapp x' g' tau ys' e') f
| Alpha_Ecase :
    forall x x' pats pats' f,
      Forall2 (fun p p' => fst p = fst p' /\ Alpha_conv (snd p) (snd p') f) pats pats' ->
      f x = x' ->
      Alpha_conv (Ecase x pats) (Ecase x' pats') f
| Alpha_Eapp :
    forall g g' xs xs' f ft,
      Forall2 (fun y y' => f y = y') xs xs' ->
      f g = g' ->
      Alpha_conv (Eapp g ft xs) (Eapp g' ft xs') f
| Alpha_Eprim :
    forall x x' p ys ys' e e' f,
      Forall2 (fun y y' => f y = y') ys ys' ->
      ~ x' \in image f (occurs_free e) :|: bound_var e ->
      Alpha_conv e e' (f {x ~> x'}) ->
      Alpha_conv (Eprim x p ys e) (Eprim x' p ys' e') f
| Alpha_Efun :
    forall B B' e e' f f',
      Disjoint _ (name_in_fundefs B') (image f (occurs_free (Efun B e)) :|: bound_var (Efun B e)) ->
      construct_fundefs_injection f B B' f' ->
      Alpha_conv_fundefs B B' f' ->
      Alpha_conv e e' f' ->
      Alpha_conv (Efun B e) (Efun B' e') f
| Alpha_Ehalt :
    forall f x x',
      f x = x' ->
      Alpha_conv (Ehalt x) (Ehalt x') f
with Alpha_conv_fundefs : fundefs -> fundefs -> (var -> var) -> Prop :=
| Alpha_Fnil :
    forall f, Alpha_conv_fundefs Fnil Fnil f
| Alpha_Fcons :
    forall g g' t xs xs' e e' B B' f f',
      f g = g' ->
      Alpha_conv_fundefs B B' f ->

      Disjoint _ (FromList xs') (image f (occurs_free e) :|: bound_var e) ->
      construct_lst_injection f xs xs' f' ->
      Alpha_conv e e' f' ->

      Alpha_conv_fundefs (Fcons g t xs e B) (Fcons g' t xs' e' B') f.


Inductive Alpha_conv_val :
  val -> val -> (* the two related values *)
  (var -> var) -> (* the current renaming of fvs *)
  Prop :=
| Alpha_Vconstr :
    forall t vs vs' f,
      Forall2 (fun v v' => Alpha_conv_val v v' f) vs vs' ->
      Alpha_conv_val (Vconstr t vs) (Vconstr t vs') f
| Alpha_Vfun :
    forall rho rho' fdefs fdefs' x x' f,
      f x = x' ->
      Alpha_conv_fundefs fdefs fdefs' f ->
      (forall x v, x \in occurs_free_fundefs fdefs ->
                         M.get x rho = Some v ->
                         exists v', M.get (f x) rho' =
                                    Some v' /\ Alpha_conv_val v v' f) ->
      Alpha_conv_val (Vfun rho fdefs x) (Vfun rho' fdefs' x') f
| Alpha_Vprim :
    forall p f,
      Alpha_conv_val (Vprim p) (Vprim p) f
| Alpha_Vint :
    forall n f,
      Alpha_conv_val (Vint n) (Vint n) f.


Lemma construct_fundefs_injection_f_eq f f' B B' g :
  construct_fundefs_injection f B B' f' ->
  f_eq f g ->
  exists g',
    f_eq f' g' /\ construct_fundefs_injection g B B' g'.
Proof.
  intros H Heq. induction H.
  - eexists; split. eassumption. constructor.
  - edestruct IHconstruct_fundefs_injection as [g' [Heq' Hc]] .
    eassumption. eexists. split.
    apply f_eq_extend. eassumption.
    constructor. eauto. rewrite f_eq_extend. eassumption.
    now symmetry.
Qed.

Lemma construct_lst_injection_f_eq f f' l l' g :
  construct_lst_injection f l l' f' ->
  f_eq f g ->
  exists g',
    f_eq f' g' /\ construct_lst_injection g l l' g'.
Proof.
  intros H Heq. induction H.
  - eexists; split. eassumption. constructor.
  - edestruct IHconstruct_lst_injection as [g' [Heq' Hc]] .
    eassumption. eexists. split.
    apply f_eq_extend. eassumption.
    constructor. eauto. rewrite f_eq_extend. eassumption.
    now symmetry.
Qed.


(* To rewrite with extensionally equal functions *)
Lemma Alpha_conv_proper_mut :
  Proper (Logic.eq ==> Logic.eq ==> f_eq ==> iff) Alpha_conv /\
  Proper (Logic.eq ==> Logic.eq ==> f_eq ==> iff) Alpha_conv_fundefs.
Proof.
  eapply exp_def_mutual_ind; intros; split; intros H'; subst.
  - inv H'; constructor; eauto.
    + eapply Forall2_monotonic; [| eassumption ].
      intros x1 x2 Heq. rewrite <- H2. eassumption.
    + rewrite <- H2. eassumption.
    + eapply H; eauto. symmetry.
      eapply f_eq_extend. eassumption.
  - inv H'; constructor; eauto.
    + eapply Forall2_monotonic; [| eassumption ].
      intros x1 x2 Heq. rewrite H2. eassumption.
    + rewrite H2. eassumption.
    + eapply H; eauto. eapply f_eq_extend. eassumption.
  - inv H'. inv H2. constructor. constructor.
    rewrite H1. reflexivity.
  - inv H'. inv H2. constructor;  eauto.
  - inv H'; constructor; eauto. inv H4. destruct y as [c' e'].
    inv H5. simpl in H1; subst. constructor.
    split; eauto. eapply H; eauto. symmetry; eassumption.
    assert (Hsuf : Alpha_conv (Ecase v l) (Ecase (x0 v) l') y1).
    { eapply H0; eauto. symmetry; eassumption.
      constructor; eauto. }
      now inv Hsuf.
  - inv H'; constructor; eauto. inv H4. destruct y as [c' e'].
    inv H5. simpl in H1; subst. constructor.
    split; eauto. eapply H; eauto.
    assert (Hsuf : Alpha_conv (Ecase v l) (Ecase (y1 v) l') x0).
    { eapply H0; eauto. constructor; eauto. }
    now inv Hsuf.
  - inv H'; constructor; eauto.
    + rewrite <- H2. eassumption.
    + eapply H; eauto. symmetry.
      eapply f_eq_extend. eassumption.
  - inv H'; constructor; eauto.
    + rewrite H2; eassumption.
    + eapply H; eauto.
      eapply f_eq_extend. eassumption.
  - inv H'; constructor; eauto.
    + eapply Forall2_monotonic; [| eassumption ].
      intros x3 x4 Heq. rewrite <- H2. eassumption.
    + rewrite <- H2. eassumption.
    + eapply H; eauto. symmetry.
      eapply f_eq_extend. eassumption.
  - inv H'; constructor; eauto.
    + eapply Forall2_monotonic; [| eassumption ].
      intros x3 x4 Heq. rewrite H2. eassumption.
    + rewrite H2; eassumption.
    + eapply H; eauto. eapply f_eq_extend. eassumption.
  - inv H'. edestruct construct_fundefs_injection_f_eq as [g' [Heq Hinj]].
    eassumption. eassumption. symmetry in Heq.
    econstructor; (try rewrite <- H3 at 1); eauto.
    + eapply H; eauto.
    + eapply H0; eauto.
  - inv H'. edestruct construct_fundefs_injection_f_eq as [g' [Heq Hinj]].
    eassumption. symmetry. eassumption. symmetry in Heq.
    econstructor; (try rewrite H3 at 1); eauto.
    + eapply H; eauto.
    + eapply H0; eauto.
  - inv H'. constructor; eauto.
    eapply Forall2_monotonic; [| eassumption ].
    intros x1 x2 Heq. rewrite <- H1. eassumption.
  - inv H'. constructor; eauto.
    eapply Forall2_monotonic; [| eassumption ].
    intros x1 x2 Heq. rewrite H1. eassumption.
  - inv H'; constructor; eauto.
  - inv H'; constructor; eauto.
  - inv H'; constructor; eauto.
    + eapply Forall2_monotonic; [| eassumption ].
      intros x1 x2 Heq. rewrite <- H2. eassumption.
    + rewrite <- H2. eassumption.
    + eapply H; eauto. symmetry.
      eapply f_eq_extend. eassumption.
  - inv H'; constructor; eauto.
    + eapply Forall2_monotonic; [| eassumption ].
      intros x1 x2 Heq. rewrite H2. eassumption.
    + rewrite H2. eassumption.
    + eapply H; eauto. eapply f_eq_extend. eassumption.
  - inv H'; constructor; eauto.
  - inv H'; constructor; eauto.
  - inv H'. edestruct construct_lst_injection_f_eq as [g' [Heq Hinj]].
    eassumption. eassumption. econstructor; (try rewrite <- H3; eauto).
    eapply H0; eauto. now symmetry.
    eapply H; eauto. now symmetry.
  - inv H'. edestruct construct_lst_injection_f_eq as [g' [Heq Hinj]].
    eassumption. symmetry. eassumption. econstructor; (try rewrite H3; eauto).
    eapply H0; eauto.
    eapply H; eauto. now symmetry.
  - inv H'. constructor.
  - inv H'. constructor.
Qed.

#[global] Instance Alpha_conv_proper :
  Proper (Logic.eq ==> Logic.eq ==> f_eq ==> iff) Alpha_conv.
Proof.
  now apply Alpha_conv_proper_mut.
Qed.

#[global] Instance Alpha_conv_fundfes_proper :
  Proper (Logic.eq ==> Logic.eq ==> f_eq ==> iff) Alpha_conv_fundefs.
Proof.
  now apply Alpha_conv_proper_mut.
Qed.

(** Pair of contexts that preserves α-equivalence *)
Definition Alpha_conv_ctx C C' f :=
  forall e e',
    Alpha_conv e e' f ->
    Alpha_conv (C |[ e ]|) (C' |[ e']|) f.

#[global] Instance alpha_conv_ctx_Proper : Proper (eq ==> eq ==> f_eq ==> iff) Alpha_conv_ctx.
Proof.
  intros c1 c2 Heq1 c3 c4 Heq2 f1 f2 Hfeq; subst; split; intros H1 e1 e2 H2.
  rewrite <- Hfeq. rewrite <- Hfeq in H2. now eauto.
  rewrite Hfeq. rewrite Hfeq in H2. now eauto.
Qed.


Lemma construct_fundefs_injection_injective f B1 B2 f' :
  construct_fundefs_injection f B1 B2 f' ->
  injective_subdomain (name_in_fundefs B1) f'.
Proof.
  intros H1. inv H1; eauto.
  eapply injective_subdomain_Empty_set.
Qed.

Require Import LambdaANF.tactics.

Lemma construct_fundefs_injection_f_eq_subdomain S f B1 B2 f' :
  construct_fundefs_injection f B1 B2 f' ->
  Disjoint _ S (name_in_fundefs B1) ->
  f_eq_subdomain S f f'.
Proof.
  intros Hinj Hd. induction Hinj.
  - reflexivity.
  - eapply f_eq_subdomain_extend_not_In_S_r.
    eapply Disjoint_In_l.
    eapply Disjoint_sym. eassumption.
    simpl. now sets.
    eapply IHHinj. eapply Disjoint_Included_r; [| eassumption ].
    sets.
Qed.

Lemma construct_fundefs_injection_image_subset S f B B' f' :
  construct_fundefs_injection f B B' f' ->
  image f' (name_in_fundefs B :|: S) \subset
  name_in_fundefs B' :|: image f (S \\ name_in_fundefs B).
Proof.
  intros Hinj. revert S; induction Hinj; intros S.
  - simpl. sets.
  - rewrite <- Union_Setminus_Included; last reflexivity; tci.
    simpl.
    eapply Included_trans.
    eapply image_extend_Included'.
    rewrite !Setminus_Union_distr.
    eapply Union_Included; [| sets ].
    rewrite Setminus_Same_set_Empty_set, Union_Empty_set_neut_l.
    rewrite <- !Setminus_Union_distr.
    eapply Included_trans.
    eapply image_monotonic. eapply Setminus_Included.
    eapply Included_trans.
    eapply IHHinj. sets.
Qed.

Lemma construct_fundefs_injection_image_subset' f B B' f' :
  construct_fundefs_injection f B B' f' ->
  image f' (name_in_fundefs B) \subset name_in_fundefs B'.
Proof.
  intros Hinj.
  rewrite <- (Union_Empty_set_neut_r (name_in_fundefs B)).
  eapply Included_trans. eapply construct_fundefs_injection_image_subset.
  eassumption.
  rewrite Setminus_Empty_set_abs_r, image_Empty_set. sets.
Qed.

Lemma construct_fundefs_injection_injective_pres S f B1 B2 f' :
  construct_fundefs_injection f B1 B2 f' ->
  injective_subdomain (S \\ name_in_fundefs B1) f ->
  Disjoint _ (name_in_fundefs B2) (image f (S \\ name_in_fundefs B1)) ->
  injective_subdomain (name_in_fundefs B1 :|: S) f'.
Proof.
  intros H1 Hinj Hdis.
  assert (H1' := H1).
  eapply construct_fundefs_injection_injective in H1.
  rewrite <- Union_Setminus_Included; last reflexivity; tci.
  eapply injective_subdomain_Union; eauto.

  eapply injective_subdomain_f_eq_subdomain.
  eapply injective_subdomain_antimon. eassumption.
  simpl. xsets.
  eapply f_eq_subdomain_antimon;
    [| eapply construct_fundefs_injection_f_eq_subdomain; eauto ].
  reflexivity. now sets.
  eapply Disjoint_Included; [| | eassumption ].
  rewrite image_f_eq_subdomain. reflexivity.
  symmetry. eapply construct_fundefs_injection_f_eq_subdomain.
  eassumption. sets.

  eapply construct_fundefs_injection_image_subset'; eauto.
Qed.


Lemma construct_lst_injection_injective f xs ys f' :
  construct_lst_injection f xs ys f' ->
  injective_subdomain (FromList xs) f'.
Proof.
  intros H1.
  inv H1; eauto.
  normalize_sets. eapply injective_subdomain_Empty_set.
Qed.


Lemma construct_lst_injection_f_eq_subdomain S f xs ys f' :
  construct_lst_injection f xs ys f' ->
  Disjoint _ S (FromList xs) ->
  f_eq_subdomain S f f'.
Proof.
  intros Hinj Hd. induction Hinj.
  - reflexivity.
  - eapply f_eq_subdomain_extend_not_In_S_r.
    eapply Disjoint_In_l.
    eapply Disjoint_sym. eassumption.
    normalize_sets. now sets.
    eapply IHHinj. eapply Disjoint_Included_r; [| eassumption ].
    normalize_sets. sets.
Qed.

Lemma construct_lst_injection_image_subset S f xs ys f' :
  construct_lst_injection f xs ys f' ->
  image f' (FromList xs :|: S) \subset FromList ys :|: image f (S \\ FromList xs).
Proof.
  intros Hinj. revert S; induction Hinj; intros S.
  - rewrite !FromList_nil at 1. sets.
  - rewrite <- Union_Setminus_Included; last reflexivity; tci.
    rewrite !FromList_cons at 1.
    repeat normalize_sets.
    eapply Included_trans.
    eapply image_extend_Included'.
    rewrite !Setminus_Union_distr.
    eapply Union_Included; [| sets ].
    rewrite Setminus_Same_set_Empty_set, Union_Empty_set_neut_l.
    rewrite <- !Setminus_Union_distr.
    eapply Included_trans.
    eapply image_monotonic. eapply Setminus_Included.
    eapply Included_trans.
    eapply IHHinj. sets.
Qed.

Lemma construct_lst_injection_image_subset' f xs ys f' :
  construct_lst_injection f xs ys f' ->
  image f' (FromList xs) \subset FromList ys.
Proof.
  intros Hinj.
  rewrite <- (Union_Empty_set_neut_r (FromList xs)).
  eapply Included_trans. eapply construct_lst_injection_image_subset.
  eassumption.
  rewrite Setminus_Empty_set_abs_r, image_Empty_set. sets.
Qed.

Lemma construct_lst_injection_injective_pres  S f xs ys f' :
  construct_lst_injection f xs ys f' ->
  injective_subdomain (S \\ FromList xs) f ->
  Disjoint _ (FromList ys) (image f (S \\ FromList xs)) ->
  injective_subdomain (FromList xs :|: S) f'.
Proof.
  intros H1 Hinj Hdis.
  assert (H1' := H1).
  eapply construct_lst_injection_injective in H1.
  rewrite <- Union_Setminus_Included; last reflexivity; tci.
  eapply injective_subdomain_Union; eauto.

  eapply injective_subdomain_f_eq_subdomain.
  eapply injective_subdomain_antimon. eassumption. sets.
  eapply f_eq_subdomain_antimon;
    [| eapply construct_lst_injection_f_eq_subdomain; eauto ].
  reflexivity. now sets.

  eapply Disjoint_Included_l.
  eapply construct_lst_injection_image_subset'. eassumption.
  eapply Disjoint_Included_r; [| eassumption ].
  rewrite image_f_eq_subdomain. reflexivity.
  symmetry. eapply construct_lst_injection_f_eq_subdomain.
  eassumption. sets.
Qed.

(* TODO move *)
Lemma image_Setminus {A B} (g : A -> B) S1 S2:
  injective_subdomain (S1 :|: S2) g ->
  image g (S1 \\ S2) <--> image g S1 \\ image g S2.
Proof.
  intros Hinj. split.
  - intros z [z' [Hin Heq]]. inv Hin.
    constructor.
    now eapply In_image; eauto.
    intros [y' [Hin' Heq']].
    assert (Heq : y' = z').
    { eapply Hinj; eauto. }
    subst; contradiction.
  - intros z [[z' [Hin Heq]] H2]. subst.
    eapply In_image. constructor; eauto.
    intros Hc. eapply H2. eapply In_image. eassumption.
Qed.

Lemma image_extend_injective_subdomain { A } g x (y : A) S:
  injective_subdomain (x |: S) (g {x ~> y}) ->
  image g (S \\ [set x]) <--> image (g {x ~> y}) S \\ [set y].
Proof.
  intros Hinj. split.
  - intros z [z' [Hin Heq]]. inv Hin.
    constructor.
    eexists. split. eassumption.
    rewrite extend_gso. reflexivity.
    now intros Hc; subst; eapply H0; eauto.

    intros Hc. inv Hc.
    assert (Heq : x = z').
    { eapply Hinj; eauto.
      rewrite extend_gss. rewrite extend_gso; eauto.
      now intros Hc; subst; eapply H0; eauto. }
    subst. eapply H0; reflexivity.
  - intros z [[z' [Hin Heq]] H2]. subst.
    destruct (peq x z').
    + subst. rewrite extend_gss in H2.
      exfalso; eauto.
    + rewrite extend_gso; eauto.
      eapply In_image. constructor; eauto.
      intros Hc; inv Hc; eauto.
Qed.


Lemma construct_fundefs_injection_image_eq S g B1 B2 g':
  construct_fundefs_injection g B1 B2 g' ->
  injective_subdomain (S \\ name_in_fundefs B1) g ->
  Disjoint _ (name_in_fundefs B2) (image g (S \\ name_in_fundefs B1)) ->
  image g (S \\ name_in_fundefs B1) <--> image g' S \\ name_in_fundefs B2.
Proof.
  intros Hc. revert S. induction Hc; intros S Hinj Hdis.
  - simpl. rewrite !Setminus_Empty_set_neut_r. reflexivity.
  - simpl.
    rewrite <- !Setminus_Union.
    rewrite <- image_extend_injective_subdomain with (y := g2).
    + rewrite IHHc. reflexivity.
      eapply injective_subdomain_antimon. eassumption.
      simpl. sets. simpl in *.
      eapply Disjoint_Included; [ | | eassumption ].
      simpl. apply image_monotonic.
      xsets. sets.
    + eapply injective_subdomain_antimon.
      eapply construct_fundefs_injection_injective_pres
        with (B1 := Fcons g1 t1 xs1 e1 B1).
      now econstructor 2; eauto.
      eapply injective_subdomain_antimon. eassumption. sets.
      eapply Disjoint_Included_r; last eassumption.
      xsets.
      rewrite Union_Setminus_Included; sets. tci.
Qed.

Lemma construct_lst_injection_image_eq S g l1 l2 g':
  construct_lst_injection g l1 l2 g' ->
  injective_subdomain (S \\ FromList l1) g ->
  Disjoint _ (FromList l2) (image g (S \\ FromList l1)) ->
  image g (S \\ FromList l1) <--> image g' S \\ FromList l2.
Proof.
  intros Hc. revert S. induction Hc; intros S Hinj Hdis.
  - simpl. normalize_sets. rewrite !Setminus_Empty_set_neut_r. reflexivity.
  - simpl. repeat normalize_sets.
    rewrite <- !Setminus_Union.
    rewrite <- @image_extend_injective_subdomain with (y := y).
    + rewrite IHHc. reflexivity.
      eapply injective_subdomain_antimon. eassumption.
      simpl. sets.
      eapply Disjoint_Included; [ | | eassumption ].
      apply image_monotonic.
      xsets. sets.
    + eapply injective_subdomain_antimon.
      eapply construct_lst_injection_injective_pres with (xs := x :: xs).
      econstructor 2; eauto. normalize_sets. eassumption.
      eapply injective_subdomain_antimon. eassumption. sets.
      normalize_sets. eapply Disjoint_Included_r; last eassumption.
      xsets.
      normalize_sets.
      rewrite Union_Setminus_Included; sets. tci.
Qed.

Lemma Forall2_map {A B} (g : A -> B) l1 l2 :
  Forall2 (fun y y' => g y = y') l1 l2 ->
  l2 = map g l1.
Proof.
  intros Hall; induction Hall; subst; eauto.
Qed.

Lemma Alpha_conv_fundefs_image_eq B B' f :
  Alpha_conv_fundefs B B' f ->
  image f (name_in_fundefs B) <--> name_in_fundefs B'.
Proof.
  intros Ha. induction Ha.
  + rewrite image_Empty_set. reflexivity.
  + simpl. rewrite image_Union, image_Singleton.
    subst. rewrite IHHa. reflexivity.
Qed.


Lemma Alpha_conv_occurs_free_mut :
  (forall e e' f,
      Alpha_conv e e' f ->
      injective_subdomain (occurs_free e) f ->
      image f (occurs_free e) <--> occurs_free e') /\
  (forall B B' f,
      Alpha_conv_fundefs B B' f ->
      injective_subdomain (name_in_fundefs B :|: occurs_free_fundefs B) f ->
      image f (occurs_free_fundefs B ) <-->
      (occurs_free_fundefs B')).
Proof with now sets.
  exp_defs_induction IHe IHl IHB; try (intros tm g Ha Hinj; inv Ha);
    repeat normalize_occurs_free.
  - rewrite image_Union.
    assert (Hinj' : injective_subdomain (v |: occurs_free e) (g {v ~> x'})).
    { eapply injective_subdomain_extend'.
      - rewrite Setminus_Union_distr.
        rewrite Setminus_Same_set_Empty_set, Union_Empty_set_neut_l.
        eapply injective_subdomain_antimon. eassumption.
        normalize_occurs_free...
      - intros Hc. eapply H6. left. eapply image_monotonic; [| eassumption ].
        sets. }
    eapply Same_set_Union_compat.
    + eapply Forall2_map in H5. subst.
      rewrite FromList_map_image_FromList. reflexivity.
    + eapply IHe in H7.
      * rewrite <- H7.
        eapply image_extend_injective_subdomain.
        eassumption.
      * eapply injective_subdomain_antimon; eauto...
  - inv H1. normalize_occurs_free. rewrite image_Singleton.
    reflexivity.
  - destruct pats' as [| [c' e'] l']; inv H1. destruct H3 as [Heq Ha].
    simpl in *; subst.
    normalize_occurs_free. rewrite !image_Union.
    rewrite IHe, IHl; eauto. rewrite image_Singleton. reflexivity.
    constructor. eauto. reflexivity.
    eapply injective_subdomain_antimon. eassumption. normalize_occurs_free...
    eapply injective_subdomain_antimon. eassumption. normalize_occurs_free...
  - rewrite image_Union.
    assert (Hinj' : injective_subdomain (v |: occurs_free e) (g {v ~> x'})).
    { eapply injective_subdomain_extend'.
      - rewrite Setminus_Union_distr.
        rewrite Setminus_Same_set_Empty_set, Union_Empty_set_neut_l.
        eapply injective_subdomain_antimon. eassumption.
        normalize_occurs_free...
      - intros Hc. eapply H7. left. eapply image_monotonic; [| eassumption ].
        sets. }
    eapply Same_set_Union_compat.
    + rewrite image_Singleton. reflexivity.
    + eapply IHe in H8.
      * rewrite <- H8.
        eapply image_extend_injective_subdomain.
        eassumption.
      * eapply injective_subdomain_antimon; eauto...
  - rewrite !image_Union.
    assert (Hinj' : injective_subdomain (x |: occurs_free e) (g {x ~> x'})).
    { eapply injective_subdomain_extend'.
      - rewrite Setminus_Union_distr.
        rewrite Setminus_Same_set_Empty_set, Union_Empty_set_neut_l.
        eapply injective_subdomain_antimon. eassumption.
        normalize_occurs_free...
      - intros Hc. eapply H8. left. eapply image_monotonic; [| eassumption ].
        sets. }
    eapply Same_set_Union_compat.
    + rewrite image_Singleton.
      eapply Forall2_map in H6. subst.
      rewrite FromList_map_image_FromList. reflexivity.
    + eapply IHe in H9.
      * rewrite <- H9.
        eapply image_extend_injective_subdomain.
        eassumption.
      * eapply injective_subdomain_antimon; eauto...
  - rewrite image_Union.
    assert (Hinj' : injective_subdomain (name_in_fundefs f2 :|: occurs_free (Efun f2 e)) f').
    { eapply construct_fundefs_injection_injective_pres; eauto.
      - eapply injective_subdomain_antimon; eauto. sets.
      - eapply Disjoint_Included_r; [| eassumption ]. sets. }
    eapply Same_set_Union_compat.
    + rewrite image_f_eq_subdomain.
      2:{ eapply construct_fundefs_injection_f_eq_subdomain. eassumption.
          eapply Disjoint_sym. eapply occurs_free_fundefs_name_in_fundefs_Disjoint. }
      rewrite IHB; eauto.  reflexivity.
      eapply injective_subdomain_antimon. eassumption.
      normalize_occurs_free...
    + rewrite construct_fundefs_injection_image_eq; eauto.
      * rewrite IHe.
        reflexivity.
        eassumption.
        eapply injective_subdomain_antimon. eassumption. normalize_occurs_free.
        now rewrite !Union_assoc, Union_Setminus_Included; sets; tci.
      * eapply injective_subdomain_antimon. eassumption. normalize_occurs_free...
      * eapply Disjoint_Included_r; last eassumption.
        normalize_occurs_free. sets.
  - rewrite !image_Union. rewrite image_Singleton.
    eapply Forall2_map in H4. subst.
    rewrite FromList_map_image_FromList. reflexivity.
  - rewrite !image_Union.
    assert (Hinj' : injective_subdomain (v |: occurs_free e) (g {v ~> x'})).
    { eapply injective_subdomain_extend'.
      - rewrite Setminus_Union_distr.
        rewrite Setminus_Same_set_Empty_set, Union_Empty_set_neut_l.
        eapply injective_subdomain_antimon. eassumption.
        normalize_occurs_free...
      - intros Hc. eapply H6. left. eapply image_monotonic; [| eassumption ].
        sets. }
    eapply Same_set_Union_compat.
    + eapply Forall2_map in H5. subst.
      rewrite FromList_map_image_FromList. reflexivity.
    + eapply IHe in H7.
      * rewrite <- H7.
        eapply image_extend_injective_subdomain.
        eassumption.
      * eapply injective_subdomain_antimon; eauto...
  - rewrite image_Singleton...
  - rewrite !image_Union.
    rewrite Union_assoc. rewrite (Union_commut [set v]), <- Union_assoc.
    rewrite (Union_assoc [set g v]). rewrite (Union_commut [set (g v)]), <- Union_assoc.
    rewrite <- Setminus_Union.
    assert (Hsub_aux : occurs_free e \\ FromList l \subset
                                   v |: name_in_fundefs f5 :|: (occurs_free e \\ (v |: (FromList l :|: name_in_fundefs f5)))).
    { rewrite !Union_assoc.
      rewrite (Union_commut [set v] (FromList l)). rewrite <- (Union_assoc (FromList l)).
      rewrite <- Setminus_Union. rewrite Union_Setminus_Included; tci; sets. }

    rewrite image_Setminus.
    + rewrite image_f_eq_subdomain at 1.
      2:{ eapply construct_lst_injection_f_eq_subdomain. eassumption. sets. }
      rewrite <- Setminus_Union. eapply Same_set_Union_compat.
      * eapply Same_set_Setminus_compat.
        ++ rewrite image_f_eq_subdomain at 1.
           2:{ symmetry. eapply construct_lst_injection_f_eq_subdomain. eassumption. sets. }
           rewrite construct_lst_injection_image_eq; [| eassumption | |].
           rewrite IHe; [| eassumption |].
           ** reflexivity.
           ** eapply injective_subdomain_antimon; [| eapply Included_Union_r ].
              eapply construct_lst_injection_injective_pres.
              eassumption.
              eapply injective_subdomain_antimon. eassumption.
              normalize_occurs_free.
              simpl. eapply Included_trans. eassumption. sets.
              eapply Disjoint_Included_r; [| eassumption ]. sets.
           ** eapply injective_subdomain_antimon. eassumption.
              normalize_occurs_free.
              eapply Included_trans. eassumption. sets.
           ** eapply Disjoint_Included_r; [| eassumption ]. sets.
        ++ assert (Heq : v |: name_in_fundefs f5 = name_in_fundefs (Fcons v t l e f5)) by reflexivity .
           rewrite Heq, Alpha_conv_fundefs_image_eq; [| now econstructor; eauto ].
           reflexivity.
      * rewrite image_Setminus, image_Singleton.
        rewrite IHB. reflexivity. eassumption.
        eapply injective_subdomain_antimon. eassumption.
        normalize_occurs_free. rewrite !Union_assoc. rewrite Union_Setminus_Included; tci; sets.
        eapply injective_subdomain_antimon. eassumption.
        normalize_occurs_free. rewrite !Union_assoc. rewrite Union_Setminus_Included; tci; sets.
    + eapply injective_subdomain_antimon. eassumption.
      eapply Union_Included; sets.
      simpl. normalize_occurs_free. eapply Included_trans. eassumption. sets.
  - rewrite image_Empty_set. sets.
Qed.

Lemma Alpha_conv_occurs_free :
  forall e e' f,
    Alpha_conv e e' f ->
    injective_subdomain (occurs_free e) f ->
    image f (occurs_free e) <--> occurs_free e'.
Proof.
  eapply Alpha_conv_occurs_free_mut.
Qed.


Lemma Alpha_conv_occurs_free_fundefs :
  forall B B' f,
      Alpha_conv_fundefs B B' f ->
      injective_subdomain (name_in_fundefs B :|: occurs_free_fundefs B) f ->
      image f (occurs_free_fundefs B ) <--> (occurs_free_fundefs B').
Proof.
  eapply Alpha_conv_occurs_free_mut.
Qed.

Require Import LambdaANF.algebra.

Section Alpha_conv_correct.

  Context {fuel : Type} {Hf : @fuel_resource fuel} {trace : Type} {Ht : @trace_resource trace}.

  Definition PostT  : Type := @PostT fuel trace.
  Definition PostGT : Type := @PostGT fuel trace.

  Variable cenv : ctor_env.
  Context (P1 : PostT) (* Local *)
          (PG : PostGT) (* Global *)
          (Hcompat : Post_properties cenv P1 P1 PG).


  (** ** Environment relation up to renaming *)
  (* TODO move to log rel *)

  Definition preord_env_P_inj (S : Ensemble var) k f rho1 rho2 :=
    forall x : var, S x -> preord_var_env cenv PG k rho1 rho2 x (f x).

  Lemma preord_env_P_inj_set (S : Ensemble var) (rho1 rho2 : env)
        (k : nat) f (x y : var) (v1 v2 : val) :
    preord_env_P_inj  (S \\ [set x]) k f rho1 rho2 ->
    preord_val cenv PG k v1 v2 ->
    injective_subdomain (x |: S) (f {x ~> y}) ->
    preord_env_P_inj S k (f {x ~> y}) (M.set x v1 rho1) (M.set y v2 rho2).
  Proof.
    intros Henv Hv Hinj z HP. unfold extend.
    destruct (peq z x) as [| Hneq].
    - subst. intros z Hget.
      rewrite M.gss in Hget. inv Hget. eexists. rewrite M.gss; eauto.
    - intros z' Hget. rewrite M.gso in Hget; eauto.
      destruct (peq (f z) y).
      + exfalso. eapply Hneq. eapply Hinj. right. eassumption.
        now eauto.
        rewrite extend_gso; eauto.
        rewrite extend_gss. eassumption.
      + edestruct (Henv z); eauto.
        constructor; eauto. intros Hc. inv Hc. congruence.
        eexists. rewrite M.gso; eauto.
  Qed.

  Lemma preord_env_P_inj_set_alt (S : Ensemble var) (rho1 rho2 : env)
        (k : nat) f (x y : var) (v1 v2 : val) :
    preord_env_P_inj (S \\ [set x]) k f rho1 rho2 ->
    preord_val cenv PG k v1 v2 ->
    ~ In _ (image f (S \\ [set x])) y ->
    preord_env_P_inj S k (f {x ~> y}) (M.set x v1 rho1) (M.set y v2 rho2).
  Proof.
    intros Henv Hv Hnin z HP. unfold extend.
    destruct (peq z x) as [| Hneq].
    - subst. intros z Hget.
      rewrite M.gss in Hget. inv Hget. eexists. rewrite M.gss; eauto.
    - intros z' Hget. rewrite M.gso in Hget; eauto.
      destruct (peq (f z) y).
      + exfalso. eapply Hnin. eexists; eauto.
        split; eauto. constructor; eauto.
        intros Hc; inv Hc; congruence.
      + edestruct (Henv z); eauto.
        constructor; eauto. intros Hc. inv Hc. congruence.
        eexists. rewrite M.gso; eauto.
  Qed.

  Lemma preord_env_P_inj_set_alt' (S : Ensemble var) (rho1 rho2 : env)
        (k : nat) f (x y : var) (v1 v2 : val) :
    preord_env_P_inj (S \\ [set x]) k f rho1 rho2 ->
    preord_val cenv PG k v1 v2 ->
    ~ In _ (image f (Dom_map rho1)) y ->
    preord_env_P_inj S k (f {x ~> y}) (M.set x v1 rho1) (M.set y v2 rho2).
  Proof.
    intros Henv Hv Hnin z HP. unfold extend.
    destruct (peq z x) as [| Hneq].
    - subst. intros z Hget.
      rewrite M.gss in Hget. inv Hget. eexists. rewrite M.gss; eauto.
    - intros z' Hget. rewrite M.gso in Hget; eauto.
      destruct (peq (f z) y).
      + exfalso. eapply Hnin. eexists; eauto.
        split; eauto. eexists; eauto.
      + edestruct (Henv z); eauto.
        constructor; eauto. intros Hc. inv Hc. congruence.
        eexists. rewrite M.gso; eauto.
  Qed.


  Lemma preord_env_P_inj_set_l (S : Ensemble var) (rho1 rho2 : env)
        (k : nat) f (x y : var) (v1 v2 : val) :
    preord_env_P_inj (S \\ [set x]) k f rho1 rho2 ->
    preord_val cenv PG k v1 v2 ->
    M.get y rho2 = Some v2 ->
    preord_env_P_inj S k (f {x ~> y}) (M.set x v1 rho1) rho2.
  Proof.
    intros Henv Hv Hnin z HP. unfold extend.
    destruct (peq z x) as [| Hneq].
    - subst. intros z Hget.
      rewrite M.gss in Hget. inv Hget. eexists. split; eauto.
    - intros z' Hget. rewrite M.gso in Hget; eauto.
      eapply Henv. constructor; eauto. intros Hc; inv Hc; eauto.
      eassumption.
  Qed.

  Lemma preord_env_P_inj_antimon (S1 S2 : var -> Prop) (k : nat) (rho1 rho2 : env) f :
    preord_env_P_inj S2 k f rho1 rho2 ->
    S1 \subset S2 ->
    preord_env_P_inj S1 k f rho1 rho2.
  Proof.
    intros Henv Hi x HP. eapply Henv. now apply Hi.
  Qed.

  Lemma preord_env_P_inj_monotonic S (k j : nat) (rho1 rho2 : env) f :
    j <= k ->
    preord_env_P_inj S k f rho1 rho2 ->
    preord_env_P_inj S j f rho1 rho2.
  Proof.
    intros Hleq Hpre x HP v Hget.
    edestruct Hpre as [v2 [Heq Hpre2] ]; eauto.
    eexists; split; eauto. eapply preord_val_monotonic; eauto.
  Qed.

  Lemma preord_env_P_inj_extend_not_In_P_r k S σ rho1 rho2 x y :
    preord_env_P_inj S k σ rho1 rho2 ->
    ~ x \in S ->
    preord_env_P_inj S k (σ {x ~> y}) rho1 rho2.
  Proof.
    intros Hpre Hnin z Hp v1 Hget.
    edestruct Hpre as [v2 [Hget2 Hpre2]]; eauto.
    repeat eexists; eauto. rewrite extend_gso; eauto.
    intros Hc. subst. contradiction.
  Qed.

  Lemma preord_env_P_inj_extend_lst_not_In_P_r k S σ rho1 rho2 xs ys:
    preord_env_P_inj S k σ rho1 rho2 ->
    Disjoint _ (FromList xs) S ->
    preord_env_P_inj S k (σ <{xs ~> ys}>) rho1 rho2.
  Proof.
    revert k S σ rho1 rho2 ys. induction xs; intros.
    - simpl. eassumption.
    - destruct ys. eassumption.
      repeat normalize_sets. simpl. eapply preord_env_P_inj_extend_not_In_P_r.
      eapply IHxs. eassumption. now sets.
      intros Hc. eapply H0. constructor; eauto.
  Qed.

  Lemma preord_env_P_inj_extend_not_In_P_r_alt k S σ rho1 rho2 x y :
    preord_env_P_inj S k σ rho1 rho2 ->
    ~ x \in Dom_map rho1 ->
    preord_env_P_inj S k (σ {x ~> y}) rho1 rho2.
  Proof.
    intros Hpre Hnin z Hp v1 Hget.
    edestruct Hpre as [v2 [Hget2 Hpre2]]; eauto.
    repeat eexists; eauto. rewrite extend_gso; eauto.
    intros Hc. subst. apply Hnin. eexists; eauto.
  Qed.

  Lemma preord_env_P_inj_def_funs_neq_r_alt S k σ rho1 rho2 B0 B :
    preord_env_P_inj S k σ rho1 rho2->
    Disjoint _ (image σ (Dom_map rho1)) (name_in_fundefs B) ->
    preord_env_P_inj S k σ rho1 (def_funs B0 B rho2 rho2).
  Proof.
    intros Henv Hd x Hin v Hget.
    rewrite def_funs_neq. now eapply Henv.
    intros Hc. eapply Hd. constructor; eauto. eapply In_image.
    eexists; eauto.
  Qed.


  Lemma preord_env_P_inj_set_lists_not_In_P_r S k f rho1 rho2 rho2' xs vs :
    preord_env_P_inj S k f rho1 rho2 ->
    set_lists xs vs rho2 = Some rho2' ->
    Disjoint _(FromList xs) (image f (Dom_map rho1)) ->
    preord_env_P_inj S k f rho1 rho2'.
  Proof.
    intros Henv Hnin Hnin' z Hy v' Hget.
    edestruct Henv as [v'' [Hget' Hv]]; eauto.
    eexists; split; eauto. erewrite <- set_lists_not_In. eassumption.
    eassumption. intros Hc. eapply Hnin'. constructor. eassumption.
    eapply In_image. eexists; eauto.
  Qed.

  Lemma preord_env_P_inj_set_lists_l_Disjoint S k f rho1 rho2 rho1' xs vs :
    preord_env_P_inj S k f rho1 rho2 ->
    set_lists xs vs rho1 = Some rho1' ->
    Disjoint _(FromList xs) S ->
    preord_env_P_inj S k f rho1' rho2.
  Proof.
    intros Henv Hnin Hnin' z Hy v' Hget.
    edestruct Henv as [v'' [Hget' Hv]]; eauto.
    erewrite <- set_lists_not_In in Hget. eassumption.
    eassumption. intros Hc. eapply Hnin'. constructor; eauto.
  Qed.

  Lemma preord_env_P_inj_set_lists_r_Disjoint S k f rho1 rho2 rho2' xs vs :
    preord_env_P_inj S k f rho1 rho2 ->
    set_lists xs vs rho2 = Some rho2' ->
    Disjoint _ (FromList xs) (image f S) ->
    preord_env_P_inj S k f rho1 rho2'.
  Proof.
    intros Henv Hnin Hnin' z Hy v' Hget.
    edestruct Henv as [v'' [Hget' Hv]]; eauto. eexists.
    split.
    erewrite <- set_lists_not_In. eassumption.
    eassumption. intros Hc. eapply Hnin'. constructor; eauto.
    eapply In_image. eassumption. eassumption.
  Qed.


  Lemma preord_env_P_inj_extend_lst_not_In_P_r_alt k S σ rho1 rho2 xs ys:
    preord_env_P_inj S k σ rho1 rho2 ->
    Disjoint _ (FromList xs) (Dom_map rho1) ->
    preord_env_P_inj S k (σ <{xs ~> ys}>) rho1 rho2.
  Proof.
    revert k S σ rho1 rho2 ys. induction xs; intros.
    - simpl. eassumption.
    - destruct ys. eassumption.
      repeat normalize_sets. simpl. eapply preord_env_P_inj_extend_not_In_P_r_alt.
      eapply IHxs. eassumption. now sets.
      intros Hc. eapply H0. constructor; eauto.
  Qed.


  Lemma preord_env_P_inj_set_extend_not_In_P_r S k f rho1 rho2 x y v :
    preord_env_P_inj S k f rho1 rho2 ->
    ~ x \in S ->
    ~ y \in (image f S) ->
    preord_env_P_inj S k (f {x ~> y}) rho1 (M.set y v rho2).
  Proof.
    intros Henv Hnin Hnin' z Hy v' Hget.
    edestruct Henv as [v'' [Hget' Hv]]; eauto.
    eexists; split; eauto.
    rewrite extend_gso, M.gso. eassumption.
    intros Hc; subst. eapply Hnin'. now eexists; eauto.
    intros Hc. subst. contradiction.
  Qed.

  Lemma preord_env_P_inj_def_funs_neq_l S k σ rho1 rho2 B0 B :
    preord_env_P_inj S k σ rho1 rho2->
    Disjoint _ S (name_in_fundefs B) ->
    preord_env_P_inj S k σ (def_funs B0 B rho1 rho1) rho2.
  Proof.
    intros Henv Hd x Hin v Hget.
    rewrite def_funs_neq in Hget. now eapply Henv.
    intros Hc. eapply Hd. constructor; eauto.
  Qed.

  Lemma preord_env_P_inj_def_funs_neq_r S k σ rho1 rho2 B0 B :
    preord_env_P_inj S k σ rho1 rho2->
    Disjoint _ (image σ S) (name_in_fundefs B) ->
    preord_env_P_inj S k σ rho1 (def_funs B0 B rho2 rho2).
  Proof.
    intros Henv Hd x Hin v Hget.
    rewrite def_funs_neq. now eapply Henv.
    intros Hc. eapply Hd. constructor; eauto. now eapply In_image.
  Qed.

  Lemma preord_env_P_inj_f_eq_subdomain S k rho1 rho2 f f':
    preord_env_P_inj S k f rho1 rho2 ->
    f_eq_subdomain S f f' ->
    preord_env_P_inj S k f' rho1 rho2.
  Proof.
    intros Henv Hfeq y Hin. rewrite <- Hfeq; eauto.
  Qed.


  Lemma preord_env_P_inj_def_funs
        S (rho1 rho2 : env) (k : nat) (B1 B2 B1' B2' : fundefs)
        (f : var -> var) x1 x2 n :
    NoDup (all_fun_name B1) ->
    NoDup (all_fun_name B2) ->
    Datatypes.length (all_fun_name B1) = Datatypes.length (all_fun_name B2) ->

    nth_error (all_fun_name B1) n = Some x1 ->
    nth_error (all_fun_name B2) n = Some x2 ->

    name_in_fundefs B1 \subset S ->

    preord_env_P_inj S k (f <{ all_fun_name B1 ~> all_fun_name B2 }>)
                     (def_funs B1' B1 rho1 rho1) (def_funs B2' B2 rho2 rho2) ->
    preord_var_env cenv PG k (def_funs B1' B1 rho1 rho1) (def_funs B2' B2 rho2 rho2) x1 x2.
  Proof.
    intros Hun1 Hun2 Hlen Hn1 Hn2 Hin Henv x Hget.

    edestruct Henv; eauto. eapply Hin.

    eapply Same_set_all_fun_name. eapply nth_FromList. eassumption.

    erewrite extend_lst_get_nth_error in H; eauto.
  Qed.

  Lemma preord_env_P_inj_eq_r S S' sig k rho1 rho2 rho3 :
    preord_env_P_inj S k sig rho1 rho2 ->
    eq_env_P (image sig S') rho2 rho3 ->
    preord_env_P_inj (Intersection _ S  S') k sig rho1 rho3.
  Proof.
    intros Henv Heq x Hin v Hget. inv Hin.
    rewrite <- Heq; eauto. eapply Henv; eauto.
    eapply In_image. eassumption.
  Qed.

  Lemma preord_env_P_inj_eq_l S S' sig k rho1 rho2 rho3 :
      preord_env_P_inj S k sig rho1 rho2 ->
      eq_env_P S' rho1 rho3 ->
      preord_env_P_inj (Intersection _ S  S') k sig rho3 rho2.
  Proof.
    intros Henv Heq x Hin v Hget. inv Hin.
    rewrite <- Heq in Hget; eauto. eapply Henv; eauto.
  Qed.

  Instance preord_env_P_inj_proper  :
    Proper (Same_set var ==> Logic.eq ==> Logic.eq ==> Logic.eq ==> Logic.eq ==> iff)
           preord_env_P_inj.
  Proof.
    intros s1 s2 [H1 H2]; split; intros Hpre;
    eapply preord_env_P_inj_antimon; subst; eauto.
  Qed.

  Lemma preord_env_P_inj_eq_env_P S sig k rho1 rho2 rho3 rho4 :
    preord_env_P_inj S k sig rho1 rho2 ->
    eq_env_P S rho1 rho3 ->
    eq_env_P (image sig S) rho2 rho4 ->
    preord_env_P_inj S k sig rho3 rho4.
  Proof.
    intros Henv Heq1 Heq2.
    rewrite <- (Intersection_idempotent S).
    eapply preord_env_P_inj_eq_l; eauto.
    rewrite <- (Intersection_idempotent S).
    eapply preord_env_P_inj_eq_r; eauto.
  Qed.

  Lemma Alpha_conv_fundefs_find_def B1 B2 f g t xs1 e1 :
    Alpha_conv_fundefs B1 B2 f ->
    injective_subdomain (name_in_fundefs B1) f ->
    find_def g B1 = Some (t, xs1, e1) ->
    exists xs2 e2 f',
      find_def (f g) B2 = Some (t, xs2, e2) /\
      construct_lst_injection f xs1 xs2 f' /\
      Disjoint _ (FromList xs2) (image f (occurs_free e1) :|: bound_var e1) /\
      Alpha_conv e1 e2 f'.
  Proof.
    intros Ha Hinj Hdef. induction Ha.
    - inv Hdef.
    - simpl in Hdef. subst. destruct (M.elt_eq g g0).
      + subst. inv Hdef. exists xs', e', f'.
        simpl. rewrite peq_true; eauto.
      + edestruct IHHa as [xs2 [ e2 [Hf' [Hlen Ha'] ] ] ]; eauto.
        eapply injective_subdomain_antimon. eassumption. sets.
        do 3 eexists. split; eauto.
        edestruct (peq (f g) (f g0)).
        * eapply Hinj in e0. subst. congruence. right.
          eapply fun_in_fundefs_name_in_fundefs. eapply find_def_correct. eassumption.
          now left.
        * simpl. rewrite peq_false; eauto.
  Qed.

  (* TODO move *)
  Lemma set_lists_length2 (rho rho' rho1 : env) (xs1 xs2 : list var) (vs1 vs2 : list val) :
    length xs1 = length xs2 ->
    length vs1 = length vs2 ->
    set_lists xs1 vs1 rho = Some rho1 ->
    exists rho2 : M.t val, set_lists xs2 vs2 rho' = Some rho2.
  Proof.
    revert xs2 vs1 vs2 rho1.
    induction xs1 as [| x xs1 IHxs ]; intros xs2 vs1 vs2 rho1 Hlen1 Hlen2 Hset.
    - inv Hset. destruct vs1; try discriminate. inv H0.
      destruct vs2; try discriminate. destruct xs2; try discriminate.
      eexists; simpl; eauto.
    - destruct xs2; try discriminate.
      destruct vs1; try discriminate. destruct vs2; try discriminate.
      inv Hlen1. inv Hlen2. simpl in Hset.
      destruct (set_lists xs1 vs1 rho) eqn:Heq2; try discriminate. inv Hset.
      edestruct IHxs as [vs2' Hset2]; try eassumption.
      eexists. simpl; rewrite Hset2; eauto.
  Qed.

  Lemma preord_env_P_inj_set_lists (S1 : var -> Prop) (rho1 rho2 rho1' rho2' : env)
        (k : nat) (xs1 xs2 : list var) (vs1 vs2 : list val) f f':
    preord_env_P_inj (Setminus _ S1 (FromList xs1)) k f rho1 rho2 ->
    Forall2 (preord_val cenv PG k) vs1 vs2 ->

    injective_subdomain (S1 \\ FromList xs1) f ->
    Disjoint _ (FromList xs2) (image f (S1 \\ FromList xs1)) ->
    construct_lst_injection f xs1 xs2 f' ->

    set_lists xs1 vs1 rho1 = Some rho1' ->
    set_lists xs2 vs2 rho2 = Some rho2' ->

    preord_env_P_inj S1 k f' rho1' rho2'.
  Proof.
    revert S1 rho1 rho2 rho1' rho2' xs2 vs1 vs2 f f'.
    induction xs1;
      intros S1 rho1 rho2 rho1' rho2' xs2 vs1 vs2  f f'
             Hpre Hall Hinj Hdis Hlst Hset1 Hset2 x HP v Hget.
    - inv Hlst. destruct vs1; try discriminate.
      simpl in Hset1. inv Hset1.
      destruct vs2; try discriminate.
      simpl in Hset2. inv Hset2.
      eapply Hpre; eauto. constructor; eauto.
    - destruct vs1; try discriminate. inv Hall. assert (Hlst' := Hlst). inv Hlst.
      simpl in Hset1, Hset2.
      destruct (set_lists xs1 vs1 rho1) eqn:Heq1;
        destruct (set_lists ys l' rho2) eqn:Heq2; try discriminate.
      inv Hset1; inv Hset2. rewrite M.gsspec in Hget.
      destruct (peq x a); subst.
      + inv Hget. eexists.
        simpl. unfold extend. rewrite peq_true.
        rewrite M.gss. eauto.
      + edestruct IHxs1 with (S1 := Setminus var S1 (Singleton _ a)) as [v2 [Het' Hpre']];
          eauto.
        * rewrite Setminus_Union.
          rewrite FromList_cons in Hpre. eassumption.
        * eapply injective_subdomain_antimon. eassumption. normalize_sets. sets.
        * eapply Disjoint_Included; [| | eapply Hdis ].
          apply image_monotonic.
          normalize_sets. xsets.
          normalize_sets. xsets.
        * constructor; eauto. intros Hc; inv Hc; congruence.
        * eexists. rewrite extend_gso; eauto. split; eauto.
          rewrite M.gso; [ now eauto |].

          intros Heq. eapply n.

          eapply construct_lst_injection_injective_pres with (S := S1) in Hlst'; eauto.
          eapply Hlst'; eauto.
          normalize_sets. sets.
          rewrite extend_gss.
          rewrite extend_gso. eassumption. eassumption.
  Qed.


  Lemma preord_env_P_inj_set_lists_alt (S1 : var -> Prop) (rho1 rho2 rho1' rho2' : env)
        (k : nat) (xs1 xs2 : list var) (vs1 vs2 : list val) f :
    preord_env_P_inj (Setminus _ S1 (FromList xs1)) k f rho1 rho2 ->
    Forall2 (preord_val cenv PG k) vs1 vs2 ->
    NoDup xs1 -> NoDup xs2 ->
    length xs1 = length xs2 ->
    Disjoint _ (image f (Setminus _ S1 (FromList xs1))) (FromList xs2) ->
    set_lists xs1 vs1 rho1 = Some rho1' ->
    set_lists xs2 vs2 rho2 = Some rho2' ->
    preord_env_P_inj S1 k (f <{ xs1 ~> xs2 }>)  rho1' rho2'.
  Proof with now eauto with Ensembles_DB.
    revert S1 rho1 rho2 rho1' rho2' xs2 vs1 vs2 f.
    induction xs1;
      intros S1 rho1 rho2 rho1' rho2' xs2 vs1 vs2 f Hpre Hall
             Hnd1 Hnd2 Hlen HD Hset1 Hset2 x HP v Hget;
      destruct xs2; try discriminate;
      destruct vs1; try discriminate;
      destruct vs2; try discriminate.
    - rewrite FromList_nil in Hpre.
      inv Hset1. inv Hset2. eapply Hpre; eauto.
      constructor; eauto. eapply not_In_Empty_set.
    - inv Hall. inv Hlen. inv Hnd1. inv Hnd2. simpl in *.
      destruct (set_lists xs1 vs1 rho1) eqn:Heq1;
        destruct (set_lists xs2 vs2 rho2) eqn:Heq2; try discriminate.
      inv Hset1; inv Hset2. rewrite M.gsspec in Hget.
      destruct (peq x a); subst.
      + inv Hget. eexists.
        simpl. rewrite extend_gss.
        rewrite M.gss. eauto.
      + edestruct IHxs1 with (S1 := Setminus var S1 (Singleton _ a))
          as [v2' [Hget' Hpre']]; eauto.
        * rewrite Setminus_Union.
          rewrite FromList_cons in Hpre. eassumption.
        * eapply Disjoint_Included; [| | eassumption ].
          rewrite FromList_cons...
          rewrite FromList_cons, Setminus_Union. reflexivity.
        * constructor; eauto. intros Hc; inv Hc.
          congruence.
        * eexists. rewrite extend_gso; eauto.
          rewrite M.gso; [ now eauto |].
          rewrite !FromList_cons in HD. intros Heq.
          eapply HD.
          assert (Hnin : ~ List.In x xs1).
          { destruct (in_dec peq x xs1); eauto.
            edestruct (@extend_lst_gss var) as [y' [Heq' Hin]]; eauto.
            rewrite Heq' in Heq. subst v0. exfalso; eauto. }
          rewrite extend_lst_gso in Heq, Hget'; eauto.
          constructor; eauto.
          eexists. split; eauto. constructor; eauto.
          intros Hc; inv Hc. inv H; congruence.
          eauto.
  Qed.

  Lemma Forall2_preord_var_env_map k S σ rho rho' l :
    preord_env_P_inj S k σ rho rho' ->
    Included _ (FromList l) S ->
    Forall2 (preord_var_env cenv PG k rho rho') l (map σ l).
  Proof with now eauto with Ensembles_DB.
    induction l; intros Henv Hin; simpl; constructor.
    - eapply Henv. eapply Hin. rewrite FromList_cons...
    - eapply IHl; eauto.
      eapply Included_trans; [| eassumption ].
      rewrite FromList_cons...
  Qed.



  Lemma preord_env_P_inj_get_list_l (S : var -> Prop) k f rho1 rho2 xs vs1 :
    preord_env_P_inj S k f rho1 rho2 ->
    Included var (FromList xs) S ->
    get_list xs rho1 = Some vs1 ->
    exists vs2 : list val,
      get_list (map f xs) rho2 = Some vs2 /\ Forall2 (preord_val cenv PG k) vs1 vs2.
  Proof with now eauto with Ensembles_DB.
    revert vs1. induction xs; intros vs1 Henv Hinc Hget.
    - eexists; split; eauto. inv Hget. constructor.
    - simpl in *.
      destruct (M.get a rho1) eqn:Hgeta; try discriminate.
      destruct (get_list xs rho1) eqn:Hgetl; try discriminate.
      inv Hget.
      edestruct Henv with (x := a) as [x' [Hgetx' Hprex']]. eapply Hinc.
      rewrite FromList_cons...
      eassumption.
      edestruct IHxs as [l' [Hgetl' Hprel']]. eassumption.
      eapply Included_trans; [| eassumption ]. rewrite FromList_cons...
      reflexivity.
      eexists. rewrite Hgetx', Hgetl'. split.
      reflexivity.
      now constructor; eauto.
  Qed.

  Lemma preord_env_P_inj_set_l_apply_r S k rho1 rho2 m x y v v' :
    preord_env_P_inj (S \\ [set x]) k (apply_r m) rho1 rho2 ->
    M.get y rho2 = Some v' ->
    preord_val cenv PG k v v' ->
    preord_env_P_inj S k (apply_r (M.set x y m)) (map_util.M.set x v rho1) rho2.
  Proof.
    intros Henv Hg1 Hval z Hin v1 Hgetz.
    destruct (peq z x); subst.
    - eexists. unfold apply_r. rewrite M.gss in *. inv Hgetz. split; eauto.
    - unfold apply_r. rewrite M.gso in *; eauto.
      eapply Henv; eauto. constructor; eauto.
      intros Hc; inv Hc; eauto.
  Qed.

  Lemma preord_env_P_inj_set_lists_l S k rho1 rho1' rho2 xs ys vs1 vs2 :
    preord_env_P cenv PG (S \\ FromList xs) k rho1 rho2 ->

    set_lists xs vs1 rho1 = Some rho1'  ->
    get_list ys rho2 = Some vs2 ->
    Forall2 (preord_val cenv PG k) vs1 vs2 ->

    preord_env_P_inj S k (apply_r (set_list (combine xs ys) (M.empty var))) rho1' rho2.
  Proof.
    revert S k rho1 rho1' rho2 ys vs1 vs2; induction xs;
      intros S k rho1 rho1' rho2 ys vs1 vs2 Henv Hset Hget Hvall.
    - simpl in Hset. destruct vs1; try congruence. inv Hset.
      inv Hvall. destruct ys; simpl in Hget; try congruence.
      intros z Hin v1 Hgetz. unfold apply_r. rewrite M.gempty. eapply Henv.
      constructor; eauto. eassumption.

      destruct (M.get e rho2); try congruence.
      destruct (get_list ys rho2); try congruence.
    - simpl in Hset. destruct vs1; try congruence.
      destruct vs2 as [|v' vs2]; inv Hvall.
      destruct (set_lists xs vs1 rho1) eqn:Hset1'; try congruence. inv Hset.
      destruct ys as [| y ys]; simpl in Hget; try congruence.
      destruct (M.get y rho2) eqn:Hgety; try congruence.
      destruct (get_list ys rho2) eqn:Hgetys; try congruence.
      inv Hget. simpl.

      eapply preord_env_P_inj_set_l_apply_r; [| eassumption | eassumption ].

      eapply IHxs. eapply preord_env_P_antimon. eassumption.
      normalize_sets. rewrite Setminus_Union. sets.
      eassumption. eassumption. eassumption.
  Qed.

  Lemma preord_env_P_inj_set_lists_l' S k sig rho1 rho1' rho2 xs ys vs1 vs2 :
    preord_env_P_inj (S \\ FromList xs) k (apply_r sig) rho1 rho2 ->

    set_lists xs vs1 rho1 = Some rho1'  ->
    get_list ys rho2 = Some vs2 ->
    Forall2 (preord_val cenv PG k) vs1 vs2 ->

    preord_env_P_inj S k (apply_r (set_list (combine xs ys) sig)) rho1' rho2.
  Proof.
    revert S k rho1 rho1' rho2 ys vs1 vs2; induction xs;
      intros S k rho1 rho1' rho2 ys vs1 vs2 Henv Hset Hget Hvall.
    - simpl in Hset. destruct vs1; try congruence. inv Hset.
      inv Hvall. destruct ys; simpl in Hget; try congruence.
      simpl. repeat normalize_sets. eassumption.
      destruct (M.get e rho2); try congruence.
      destruct (get_list ys rho2); try congruence.
    - simpl in Hset. destruct vs1; try congruence.
      destruct vs2 as [|v' vs2]; inv Hvall.
      destruct (set_lists xs vs1 rho1) eqn:Hset1'; try congruence. inv Hset.
      destruct ys as [| y ys]; simpl in Hget; try congruence.
      destruct (M.get y rho2) eqn:Hgety; try congruence.
      destruct (get_list ys rho2) eqn:Hgetys; try congruence.
      inv Hget. simpl.

      eapply preord_env_P_inj_set_l_apply_r; [| eassumption | eassumption ].

      eapply IHxs. eapply preord_env_P_inj_antimon. eassumption.
      normalize_sets. rewrite Setminus_Union. sets.
      eassumption. eassumption. eassumption.
  Qed.

  Instance preord_env_P_inj_f_proper :
    Proper (eq ==> eq ==> f_eq ==> eq ==> eq ==> iff) preord_env_P_inj.
  Proof.
    constructor; subst; intros Hp.
    intros z Hz. rewrite <- H1. eauto.
    intros z Hz. rewrite H1. eauto.
  Qed.

  Lemma preord_env_P_inj_set_not_In_P_l S k f rho1 rho2 x v :
    preord_env_P_inj S k f rho1 rho2 ->
    ~ In _ S x ->
    preord_env_P_inj S k f (M.set x v rho1) rho2.
  Proof.
    intros Henv Hnin y Hy v' Hget. eapply Henv. eassumption.
    rewrite M.gso in Hget. eassumption. intros Hc; subst.
    eauto.
  Qed.

  Lemma preord_env_P_inj_set_not_In_P_r S k f rho1 rho2 x v :
    preord_env_P_inj S k f rho1 rho2 ->
    ~ In _ (image f S) x ->
    preord_env_P_inj S k f rho1 (M.set x v rho2).
  Proof.
    intros Henv Hnin y Hy v' Hget.
    edestruct Henv as [v'' [Hget' Hv]]; eauto.
    eexists; split; eauto.
    rewrite M.gso. eassumption. intros Hc; subst.
    eapply Hnin. eexists; eauto.
  Qed.

  Lemma preord_env_P_inj_reset S k f rho rho' x y v :
    M.get (f x) rho' = Some v ->
    ~ In _ (image f S) y ->
    preord_env_P_inj S k f rho rho' ->
    preord_env_P_inj S k (f {x ~> y}) rho (M.set y v rho').
  Proof.
    intros Hget Hnin Hpre z Hz v' Hget'.
    destruct (peq z x); subst.
    - rewrite extend_gss, M.gss.
      edestruct Hpre as [v2 [Hget'' Hpre2]]; eauto.
      rewrite Hget'' in Hget; inv Hget.
      eexists; eauto.
    - rewrite extend_gso, M.gso; eauto.
      eapply Hpre; eauto.
      intros Hc; subst. eapply Hnin; eexists; eauto.
  Qed.

  Lemma preord_env_P_inj_reset_lists S k f rho rho' rho'' xs ys vs :
    get_list (map f xs) rho' = Some vs ->
    Disjoint _ (image f S) (FromList ys) ->
    set_lists ys vs rho' = Some rho'' ->
    NoDup ys ->
    length xs = length ys ->
    preord_env_P_inj S k f rho rho' ->
    preord_env_P_inj S k (f <{xs ~> ys}>) rho rho''.
  Proof.
    revert rho'' ys vs; induction xs; intros rho'' ys vs Hget HD Hset Hdup Hlen Hpre.
    - simpl. destruct vs; try discriminate.
      destruct ys; try discriminate. inv Hset. eassumption.
    - simpl in *.
      destruct (M.get (f a) rho') eqn:Heqa; try discriminate.
      destruct (get_list (map f xs) rho') eqn:Hgetl; try discriminate.
      inv Hget.
      destruct ys; try discriminate. simpl in Hset.
      destruct (set_lists ys l rho') eqn:Hsetl; try discriminate.
      rewrite FromList_cons in HD. inv Hset.
      assert (Hpre' : preord_env_P_inj S k (f <{ xs ~> ys }>) rho t).
      { eapply IHxs. reflexivity.
        now eauto with Ensembles_DB.
        eassumption. now inv Hdup. now inv Hlen. eassumption. }
      intros z Hz v' Hget'.
      destruct (peq z a); subst.
      + rewrite extend_gss, M.gss.
        edestruct Hpre as [v2 [Hget'' Hpre2]]; eauto.
        rewrite Hget'' in Heqa; inv Heqa.
        eexists; eauto.
      + rewrite extend_gso, M.gso; eauto.
        eapply Hpre'; eauto.
        inv Hdup. intros Hc; subst.
        edestruct in_dec with (a := z) (l := xs) as [Hin | Hnin ].
        now apply peq.
        edestruct (@extend_lst_gss var f xs ys z) as [x' [Heq Hin']].
        eassumption. now inv Hlen. eapply H1.
        rewrite <- Heq in Hin'. eassumption.
        rewrite extend_lst_gso in H1; [| eassumption ].
        eapply HD. constructor; eauto.
        eexists; split; eauto. rewrite extend_lst_gso; [| eassumption ].
        reflexivity.
  Qed.

  Lemma construct_lst_injection_length f xs1 xs2 f' :
    construct_lst_injection f xs1 xs2 f' ->
    List.length xs1 = List.length xs2.
  Proof.
    intros Hinj. induction Hinj.
    - reflexivity.
    - simpl. congruence.
  Qed.

  Lemma preord_env_P_inj_def_funs_pre k S rho1 rho2 B1 B2 f h :
    (* The IH *)
    (forall m : nat,
       m < k ->
       forall (e1 e2 : exp) (rho1 rho2 : env) (f : var -> var),
         injective_subdomain (occurs_free e1) f ->
         Alpha_conv e1 e2 f ->
         preord_env_P_inj (occurs_free e1) m f rho1 rho2 ->
         preord_exp cenv P1 PG m (e1, rho1) (e2, rho2)) ->
    construct_fundefs_injection f B1 B2 h ->
    Disjoint _ (image f S) (name_in_fundefs B2) ->
    injective_subdomain S f ->
    occurs_free_fundefs B1 \subset S ->
    Alpha_conv_fundefs B1 B2 h  ->
    preord_env_P_inj S k f rho1 rho2 ->
    preord_env_P_inj (name_in_fundefs B1 :|: S) k h
                     (def_funs B1 B1 rho1 rho1) (def_funs B2 B2 rho2 rho2).
  Proof with now eauto with Ensembles_DB.
    revert S rho1 rho2 B1 B2 f h.
    induction k as [ k IH' ] using lt_wf_rec1.
    intros S rho1 rho2 B1 B2 f h IHe Hlst Hdis Hinj Hsub Ha Hpre; assert (Hc := Hcompat); destruct Hc.
    - intros x Hin v Hget.
      destruct (Decidable_name_in_fundefs B1) as [Dec].
      destruct (Dec x).
      + rewrite def_funs_eq in Hget; eauto. inv Hget.
        assert (Him : (h x) \in name_in_fundefs B2).
        { eapply Included_trans.
          eapply construct_fundefs_injection_image_subset'. eassumption.
          sets. eapply In_image. eassumption. }
        eexists. split.
        eapply def_funs_eq. eassumption.

        { rewrite preord_val_eq.
          intros vs1 vs2 j t1 xs1 e1 rho1' Hlen Hf1 Hs.
          edestruct Alpha_conv_fundefs_find_def
            as [xs2 [e2 [f'' [Hf' [Hinj''' [Hdis' Ha'' ] ] ] ] ] ]; eauto.
          now eapply construct_fundefs_injection_injective; eauto.
          assert (Hlen' := Hinj''').
          eapply construct_lst_injection_length in Hlen'.

          edestruct set_lists_length2 as [rho2' Hs']; eauto.
          exists xs2. exists e2. exists rho2'. split; eauto.
          split; [ now eauto |]. intros Hleq Hpre'.
          eapply preord_exp_post_monotonic. eassumption.

          assert (Hinjh : injective_subdomain (occurs_free e1 \\ FromList xs1) h).
          { eapply @injective_subdomain_antimon
              with (S := name_in_fundefs B1 :|: (occurs_free e1 \\ FromList xs1)); sets.
            eapply construct_fundefs_injection_injective_pres; first eassumption.
            * eapply injective_subdomain_antimon. eassumption.
              do 2 eapply Setminus_Included_Included_Union.
              eapply Included_trans.
              eapply occurs_free_in_fun. eapply find_def_correct. eassumption.
              sets.
            * eapply Disjoint_sym. eapply Disjoint_Included_l; [| eassumption ].
              eapply image_monotonic. eapply Included_trans; [| eassumption ].
              do 2 eapply Setminus_Included_Included_Union.
              eapply Included_trans.
              eapply occurs_free_in_fun. eapply find_def_correct. eassumption.
              sets. }

          eapply IHe.
          + eassumption.
          + eapply @injective_subdomain_antimon
              with (S :=  FromList xs1 :|: occurs_free e1); sets.
            eapply construct_lst_injection_injective_pres. eassumption.
            eassumption.
            eapply Disjoint_Included_r; [| eassumption ]. sets.
          + eassumption.
          + eapply preord_env_P_inj_set_lists;
              [ | eassumption | |  | now eauto | now eauto | now eauto ].
            eapply preord_env_P_inj_antimon.
            * eapply IH'; try eassumption.
              ** intros. eapply IHe; eauto. lia.
              ** eapply (preord_env_P_inj_monotonic _ k). lia.
                 eassumption.
            * eapply Setminus_Included_Included_Union.
              eapply Included_trans.
              eapply occurs_free_in_fun. eapply find_def_correct. eassumption.
              sets.
            * eassumption.
            * eapply Disjoint_Included_r; [| eassumption ].
              sets. }
      + inv Hin; try contradiction. setoid_rewrite def_funs_neq.
        assert (Hfeq : h x = f x).
        { erewrite <- construct_fundefs_injection_f_eq_subdomain
            with (S := S \\ name_in_fundefs B1);
            try eassumption; sets. constructor; eauto. }
        setoid_rewrite Hfeq. rewrite def_funs_neq in Hget; eauto.
        eapply Hpre; eauto.
        simpl. eapply Disjoint_In_l with (s1 := image h (S \\ name_in_fundefs B1)).
        rewrite image_f_eq_subdomain;
          [| symmetry; eapply construct_fundefs_injection_f_eq_subdomain; eauto ]; sets.
        eapply In_image. constructor; eauto.
  Qed.

  (** α-equivalence preserves semantics *)
  Lemma Alpha_conv_correct k rho1 rho2 e1 e2 g :
    injective_subdomain (occurs_free e1) g ->
    (* Disjoint _ (image g (occurs_free e1)) (bound_var e1) ->     *)
    Alpha_conv e1 e2 g ->
    preord_env_P_inj (occurs_free e1) k g rho1 rho2 ->
    preord_exp cenv P1 PG k (e1, rho1) (e2, rho2).
  Proof with now sets.
    revert e1 e2 rho1 rho2 g.
    induction k as [ k IH ] using lt_wf_rec1.
    induction e1 using exp_ind'; intros e2 rho1 rho2 g Hinj (* Hdis *) Ha Henv; assert (Hc := Hcompat); inv Hc; inv Ha.
    - (* Econstr *)
      eapply preord_exp_constr_compat; eauto; intros.
      + eapply Forall2_monotonic_strong; [ | eassumption ].
        intros x y Hin1 Hin2 Heq. specialize (Henv x).
        rewrite Heq in Henv. eapply Henv.
        now constructor.
      + assert (Hinj' : injective_subdomain (v |: occurs_free e1) (g {v ~> x'})).
        { eapply injective_subdomain_extend'.
          - rewrite Setminus_Union_distr.
            rewrite Setminus_Same_set_Empty_set, Union_Empty_set_neut_l.
            eapply injective_subdomain_antimon. eassumption. normalize_occurs_free...
          - intros Hc. eapply H6. left. eapply image_monotonic; [| eassumption ].
            sets. }
        eapply IH; try eassumption.
        * eapply injective_subdomain_antimon; eauto...
        * eapply preord_env_P_inj_set.
          eapply preord_env_P_inj_antimon. eapply preord_env_P_inj_monotonic; [| eassumption ].
          lia. normalize_occurs_free...
          rewrite preord_val_eq. constructor; eauto using Forall2_Forall2_asym_included.
          eassumption.
    - (* Ecase nil *)
      inv H1. eapply preord_exp_case_nil_compat. eauto.
    - (* Ecase cons *)
      inv H1. destruct H2 as [Heq Ha]. destruct y as [c' e2]. simpl in Heq; subst.
      eapply preord_exp_case_cons_compat; eauto.
      + eapply Forall2_monotonic; [| eassumption ]. intros x1 x2 H; now inv H.
      + intros m Hlt. eapply IH; eauto.
        * eapply injective_subdomain_antimon. eassumption.
          normalize_occurs_free...
        * eapply preord_env_P_inj_antimon. eapply preord_env_P_inj_monotonic; [| eassumption ].
          lia. normalize_occurs_free...
      + eapply IHe0.
        * eapply injective_subdomain_antimon. eassumption.
          normalize_occurs_free...
        * now constructor; eauto.
        * eapply preord_env_P_inj_antimon. eapply preord_env_P_inj_monotonic; [| eassumption ].
          lia. normalize_occurs_free...
    - (* Eproj *)
      eapply preord_exp_proj_compat; eauto; intros.
      assert (Hinj' : injective_subdomain (v |: occurs_free e1) (g {v ~> x'})).
      { eapply injective_subdomain_extend'.
        - rewrite Setminus_Union_distr.
          rewrite Setminus_Same_set_Empty_set, Union_Empty_set_neut_l.
          eapply injective_subdomain_antimon. eassumption. normalize_occurs_free...
        - intros Hc. eapply H7. left. eapply image_monotonic; [| eassumption ].
          sets. }
      eapply IH; try eassumption.
      * eapply injective_subdomain_antimon; eauto...
      * eapply preord_env_P_inj_set.
        eapply preord_env_P_inj_antimon. eapply preord_env_P_inj_monotonic; [| eassumption ].
        lia. normalize_occurs_free... eassumption. eassumption.
    - (* Eletapp *)
      eapply preord_exp_letapp_compat; eauto; intros.
      + eapply Henv. econstructor. now left.
      + eapply Forall2_monotonic_strong; [ | eassumption ].
        intros z y Hin1 Hin2 Heq. specialize (Henv z).
        rewrite Heq in Henv. eapply Henv.
        constructor. now right.
      + assert (Hinj' : injective_subdomain (x |: occurs_free e1) (g {x ~> x'})).
        { eapply injective_subdomain_extend'.
          - rewrite Setminus_Union_distr.
            rewrite Setminus_Same_set_Empty_set, Union_Empty_set_neut_l.
            eapply injective_subdomain_antimon. eassumption. normalize_occurs_free...
          - intros Hc. eapply H8. left. eapply image_monotonic; [| eassumption ].
            sets. }
        eapply IH; try eassumption.
        * eapply injective_subdomain_antimon; eauto...
        * eapply preord_env_P_inj_set.
          eapply preord_env_P_inj_antimon. eapply preord_env_P_inj_monotonic; [| eassumption ].
          lia. normalize_occurs_free... eassumption. eassumption.
    - (* Efun *)
      eapply preord_exp_fun_compat.
      + intros.
        assert (Heq : PS.cardinal (fundefs_fv B') =
                      PS.cardinal (@mset (FromList (map f' (PS.elements (fundefs_fv f2)))) _)).
        { rewrite !PS.cardinal_spec. eapply Same_set_FromList_length'.
          eapply NoDupA_NoDup. now eapply PS.elements_spec2w.
          eapply NoDupA_NoDup. now eapply PS.elements_spec2w.
          rewrite <- !FromSet_elements, <- !fundefs_fv_correct, <- mset_eq.
          rewrite FromList_map_image_FromList, <- !FromSet_elements, <- !fundefs_fv_correct.
          rewrite Alpha_conv_occurs_free_fundefs; [ reflexivity | eassumption | ].
          eapply construct_fundefs_injection_injective_pres. eassumption.
          eapply injective_subdomain_antimon. eassumption. normalize_occurs_free. sets.
          eapply Disjoint_Included_r; [| eassumption ]. normalize_occurs_free. sets. }
        now eauto.
      + now eauto.
      + eapply preord_exp_monotonic. eapply IHe1; [| eassumption |]. 3:{ lia. }
        * eapply injective_subdomain_antimon.
          eapply construct_fundefs_injection_injective_pres.
          eassumption.
          eapply injective_subdomain_antimon. eassumption.
          normalize_occurs_free. eapply Included_Union_r.
          eapply Disjoint_Included_r; [| eassumption ].
          normalize_occurs_free...
          now sets.
        * eapply preord_env_P_inj_antimon
            with (S2 := name_in_fundefs f2 :|: occurs_free (Efun f2 e1)).
          eapply preord_env_P_inj_def_funs_pre; eauto.
          ** eapply Disjoint_sym. eapply Disjoint_Included_r;[| eassumption ]...
          ** normalize_occurs_free...
          ** normalize_occurs_free.
             rewrite !Union_assoc, Union_Setminus_Included; sets. tci.
    - eapply preord_exp_app_compat; eauto.
      eapply Forall2_monotonic_strong; [| eassumption ].
      intros x y Hin1 Hin2 Heq. specialize (Henv x).
      rewrite Heq in Henv. eapply Henv.
      now constructor.
    - eapply preord_exp_prim_compat; eauto; intros.
      + eapply Forall2_monotonic_strong; [| eassumption ].
        intros x y Hin1 Hin2 Heq. specialize (Henv x).
        rewrite Heq in Henv. eapply Henv.
        now constructor.
  (* + assert (Hinj' : injective_subdomain (v |: occurs_free e1) (g {v ~> x'})).
        { eapply injective_subdomain_extend'.
          - rewrite Setminus_Union_distr.
            rewrite Setminus_Same_set_Empty_set, Union_Empty_set_neut_l.
            eapply injective_subdomain_antimon. eassumption. normalize_occurs_free...
          - intros Hc. eapply H6. left. eapply image_monotonic; [| eassumption ].
            sets. }
        eapply IH; try eassumption.
        * eapply injective_subdomain_antimon; eauto...
        * eapply preord_env_P_inj_set.
          eapply preord_env_P_inj_antimon. eapply preord_env_P_inj_monotonic; [| eassumption ].
          lia. normalize_occurs_free...
          eassumption. eassumption. *)
    - eapply preord_exp_halt_compat; eauto.
  Qed.

End Alpha_conv_correct.

#[global] Instance preord_env_P_inj_proper' fuel (Hfuel : fuel_resource) trace (Htrace : trace_resource) :
  Proper (Logic.eq ==> Logic.eq ==> Same_set var ==> Logic.eq ==> Logic.eq ==> Logic.eq ==> Logic.eq ==> iff)
         (@preord_env_P_inj fuel Hfuel trace Htrace).
Proof.
  repeat (intro; intros); subst.
  split; intros Hpre;
    eapply preord_env_P_inj_antimon; subst; eauto; eapply H1.
Qed.


#[global] Instance preord_env_P_inj_f_proper' fuel (Hfuel : fuel_resource) trace (Htrace : trace_resource) :
  Proper (Logic.eq ==> Logic.eq ==> Logic.eq ==> Logic.eq ==> f_eq ==> Logic.eq ==> Logic.eq ==> iff)
         (@preord_env_P_inj fuel Hfuel trace Htrace).
Proof.
  repeat (intro; intros); subst.
  split; intros Hpre.
  intro; intros. rewrite <- H3. eauto.
  intro; intros. rewrite H3. eauto.
Qed.



(* Close Scope fun_scope. *)
(* Close Scope ctx_scope. *)
