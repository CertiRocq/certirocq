(* Function library. Part of the CertiRocq project.
 * Author: Anonymized, 2016
 *)

From CertiRocq Require Import LambdaANF.Ensembles_util LambdaANF.tactics.
From compcert.lib Require Import Coqlib.
From Stdlib Require Import Numbers.BinNums NArith.BinNat PArith.BinPos Relations.Relations
     Classes.Morphisms Lists.List Sets.Ensembles Program.Basics micromega.Lia.

Import ListNotations.

Open Scope program_scope.

(** ** Usefull definitions and lemmas about functions. *)

Definition codomain {A B} (f : A -> B) : Ensemble B :=
  fun y => exists x, f x = y.

Definition image {A B} (f : A -> B) (S : Ensemble A) :=
  fun y => exists x, In _ S x /\ f x = y.

(** A function is injective in a subdomain *)
Definition injective_subdomain {A B} P (f : A -> B) :=
  forall x x', In _ P x -> In _ P x' -> f x = f x' -> x = x'.

Definition injective {A B} (f : A -> B) := injective_subdomain (Full_set _) f.

(** Extensional equality on a subdomain *)
Definition f_eq_subdomain {A B} S (f1 f2 : A -> B) :=
  forall x, In _ S x -> f1 x = f2 x.

(** Extensional equality *)
Definition f_eq  {A B} (f1 f2 : A -> B) : Prop :=  forall x, f1 x = f2 x.

(** Extend a function. Only works for positives to avoid parameterizing the definition with
  * the decidable equality proof. TODO: fix this *)
Definition extend {A} (f: positive -> A) (x : positive) (x' : A) : (positive -> A) :=
  fun z => if peq z x then x' else f z.

Declare Scope fun_scope.

(* Postfix, but at the level of the arguments it is applied to *)
#[warning="-postfix-notation-not-level-1"]
Notation " f '{' x '~>' y '}' " := (extend f x y) (at level 10, no associativity)
                                   : fun_scope.

Open Scope fun_scope.

Fixpoint extend_lst {A} (f: positive -> A) (xs : list positive) (xs' : list A)
: positive -> A :=
  match xs with
    | [] => f
    | x :: xs =>
      match xs' with
        | [] => f
        | x' :: xs' =>
          (extend_lst f xs xs') {x ~> x'}
      end
  end.


#[warning="-postfix-notation-not-level-1"]
Notation " f '<{' xs '~>' xs' '}>' " := (extend_lst f xs xs') (at level 10, no associativity)
                                        : fun_scope.

(** Apply a function n times *)
Fixpoint app {A} (f : A -> A) (n : nat) : A ->  A :=
  fun x =>
    match n with
      | 0%nat => x
      | S n' => f (app f n' x)
    end.

Infix "^" := app (at level 30, right associativity) : fun_scope.


(** ** Some support for partial functions *)

Definition domain {A B} (f : A -> option B) : Ensemble A :=
  fun x => exists y, f x = Some y.

Definition image' {A B} (f : A -> option B) S : Ensemble B :=
  fun y => exists x, In _ S x /\ f x = Some y.

Definition injective_subdomain' {A B} P (f : A -> option B) :=
  forall x x' v, In _ P x -> In _ P x' -> f x = Some v -> f x' = Some v -> x = x'.

Definition lift {A B} (f : A -> B) : option A -> option B :=
  fun x => match x with
          | Some x => Some (f x)
          | None => None
        end.

Definition inverse_subdomain {A B: Type} S (f : A -> B) g :=
  f_eq_subdomain (image f S) (f ∘ g) id /\
  f_eq_subdomain S (g ∘ f) id.

(** * Lemmas about [f_eq_subdomain] and [f_eq] *)

#[global] Instance equivalence_f_eq_subdomain {A B} S : Equivalence (@f_eq_subdomain A B S).
Proof.
  constructor; try now constructor.
  intros f1 f2 Heq x HS; rewrite Heq. reflexivity. eassumption.
  intros f1 f2 f3 Heq1 Heq2 x HS; rewrite Heq1. now eauto. eassumption.
Qed.

#[global] Instance equivalence_f_eq {A B} : Equivalence (@f_eq A B).
Proof.
  constructor; congruence.
Qed.

#[global] Instance f_eq_subdomain_Proper_Same_set {A B} :
  Proper (Same_set A ==> eq ==> eq ==> iff) (@f_eq_subdomain A B).
Proof.
  intros S1 S2 Hseq f1 f1' Heq1 f2 f2' Heq2; subst; split; intros Hfeq x HS;
  apply Hfeq; eapply Hseq; eassumption.
Qed.

#[global] Instance f_eq_subdomain_Proper_f_eq_l {A B} :
  Proper (eq ==> f_eq ==> eq ==> iff) (@f_eq_subdomain A B).
Proof.
  intros S1 S2 Heq f1 f1' Heq1 f2 f2' Heq2; subst; split; intros Hfeq x HS.
  now rewrite <- Heq1; eauto. now rewrite Heq1; eauto.
Qed.

#[global] Instance f_eq_subdomain_Proper_f_eq_r {A B} :
  Proper (eq ==> eq ==> f_eq ==> iff) (@f_eq_subdomain A B).
Proof.
  intros S1 S2 Heq f1 f1' Heq1 f2 f2' Heq2; subst; split; intros Hfeq x HS.
  now rewrite <- Heq2; eauto. now rewrite Heq2; eauto.
Qed.

#[global] Instance f_eq_Proper_f_eq_l {A B} :
  Proper (f_eq ==> eq ==> iff) (@f_eq A B).
Proof.
  intros  f1 f1' Heq1 f2 f2' Heq2; subst; split; intros Hfeq x.
  now rewrite <- Heq1; eauto. now rewrite Heq1; eauto.
Qed.

#[global] Instance f_eq_Proper_f_eq_r {A B} :
  Proper (eq ==> f_eq ==> iff) (@f_eq A B).
Proof.
  intros f1 f1' Heq1 f2 f2' Heq2; subst; split; intros Hfeq.
  now rewrite <- Heq2; eauto. now rewrite Heq2; eauto.
Qed.

#[global] Instance map_proper {A B} : Proper (f_eq ==> eq ==> eq) (@map A B).
Proof.
  intros f1 f2 Hfeq x1 x2 Heq; subst.
  induction x2; eauto.
  simpl. rewrite Hfeq. congruence.
Qed.

Lemma f_eq_subdomain_antimon {A B} S S' (f f' : A -> B) :
  Included _ S' S ->
  f_eq_subdomain S f f' ->
  f_eq_subdomain S' f f'.
Proof.
  intros Hinc Hfeq x Hin; eauto.
Qed.

Lemma f_eq_subdomain_Union {A B} P1 P2 (f1 f2 : A -> B) :
  f_eq_subdomain P1 f1 f2 ->
  f_eq_subdomain P2 f1 f2 ->
  f_eq_subdomain (Union _ P1 P2) f1 f2.
Proof.
  intros H1 H2 x1 HP; inv HP; eauto.
Qed.

Lemma f_eq_subdomain_compose_compat {A B C} S (f1 f2: A -> B) (g1 g2 : B -> C) :
  f_eq_subdomain S f1 f2 ->
  f_eq_subdomain (image f1 S) g1 g2 ->
  f_eq_subdomain S (g1 ∘ f1) (g2 ∘ f2).
Proof.
  intros Heq1 Heq2 x Hin. unfold compose.
  rewrite <- Heq1; eauto. rewrite Heq2. reflexivity.
  eexists; split; eauto.
Qed.


Lemma f_eq_subdomain_trans {A} S (f g h : positive -> A) :
  f_eq_subdomain S f g -> f_eq_subdomain S g h -> f_eq_subdomain S f h.
Proof.
  eapply equivalence_f_eq_subdomain.
Qed.


Lemma compose_extend_l S (C : Type) f (g : positive -> positive) (x : positive) (y : C) :
  injective_subdomain S g ->
  x \in S ->
  f_eq_subdomain S (f {g x ~> y} ∘ g) ((f ∘ g) {x ~> y}).
Proof.
  intros Hinj Hin z Hinz. unfold compose. simpl. compute.

  destruct (peq z x); subst; eauto.
  - rewrite peq_true. reflexivity.
  - rewrite peq_false. reflexivity.  intros Hc.
    eapply n. eapply Hinj; eassumption.
Qed.

Lemma map_f_eq_subdomain {A B} (f g : A -> B) l :
  f_eq_subdomain (FromList l) f g ->
  map f l = map g l.
Proof.
  intros Hf. induction l.
  - reflexivity.
  - simpl. rewrite IHl. rewrite Hf. reflexivity.
    now left. eapply f_eq_subdomain_antimon; [| eassumption ].
    normalize_sets; now eauto with Ensembles_DB.
Qed.

(** * Lemmas about [image] *)

#[global] Instance image_Proper_Same_set {A B} : Proper (eq ==> Same_set A ==> Same_set B) image.
Proof.
  intros x1 x2 Heq1 s1 s2 Hseq; subst; split; intros x [y [Hin Heq]]; subst;
  eexists; split; eauto; apply Hseq; eauto.
Qed.

#[global] Instance image_Proper_f_eq {A B} : Proper (f_eq ==> eq ==> Same_set B) (@image A B).
Proof.
  intros x1 x2 Heq1 s1 s2 Hseq2; subst; split; intros x [y [Hin Heq]]; subst;
  eexists; split; eauto; rewrite Heq1; eauto; now (constructor; eauto).
Qed.

Lemma image_Union {A B} S1 S2 (g : A -> B) :
  Same_set _ (image g (Union _ S1 S2)) (Union _ (image g S1) (image g S2)).
Proof.
  split; intros x Hi.
  - destruct Hi as [x' [Hin Heq]]; subst. inv Hin.
    left. eexists; eauto.
    right. eexists; eauto.
  - inv Hi; destruct H as [x' [Hin Heq]]; subst;
    eexists; split; eauto.
Qed.

Lemma image_id {A : Type} (S : Ensemble A) :
  image id S <--> S.
Proof.
  split; intros x.
  - intros [x' [Hin Heq]]. inv Heq.
    eassumption.
  - intros HS. eexists; split; eauto.
Qed.

Lemma image_compose {A B C : Type} (f : A -> B) (g : B -> C) (S : Ensemble A):
  image (g ∘ f) S <--> image g (image f S).
Proof.
  split.
  - intros c [a [Hin Heq]].
    eexists. split; eauto. eexists. split; eauto.
  - intros c [b' [[a [Hin Heqa]] Heqb]]. subst.
    eexists. split; eauto.
Qed.

Lemma image_Singleton {A B} x (g : A -> B) :
  Same_set _ (image g (Singleton _ x)) (Singleton _ (g x)).
Proof.
  split; intros y Hi.
  - destruct Hi as [x' [Hin Heq]]; subst. inv Hin.
    eauto.
  - destruct Hi. eexists; eauto.
Qed.

Lemma image_Empty_set {A B} (g : A -> B) :
  Same_set _ (image g (Empty_set _)) ((Empty_set _)).
Proof.
  split; intros y Hi.
  - destruct Hi as [x' [Hin Heq]]; subst. inv Hin.
  - inv Hi.
Qed.

Lemma image_f_eq_subdomain {A B} (f1 f2 : A -> B) S :
  f_eq_subdomain S f1 f2 ->
  Same_set _ (image f1 S) (image f2 S).
Proof.
  intros Heq; split; intros x [y [Hin Heq']]; subst;
  (eexists; split; [ now eauto |]); now rewrite Heq.
Qed.

Lemma image_monotonic {A B} (f : A -> B) S S' :
  Included _ S S' ->
  Included _ (image f S) (image f S').
Proof.
  intros Hin x [y [Hin' Heq]]; subst. eexists; eauto.
Qed.

Lemma FromList_map_image_FromList {A B} l (f : A -> B):
  Same_set B (FromList (map f l)) (image f (FromList l)).
Proof with now eauto with Ensembles_DB.
  induction l; simpl.
  - rewrite !FromList_nil, image_Empty_set...
  - rewrite !FromList_cons, image_Union, image_Singleton...
Qed.


(** * Lemmas about [extend] *)

#[global] Instance extend_Proper {A} : Proper (f_eq ==> Logic.eq ==> Logic.eq ==> f_eq) (@extend A).
Proof.
  intros f1 f2 Hfeq x1 x2 Heq1 x3 x4 Hfeq2; subst.
  intros x. unfold extend. destruct (peq x x2); eauto.
Qed.

Lemma extend_gss {A} f x (x' : A) :
  f {x ~> x'} x = x'.
Proof.
  unfold extend. rewrite peq_true. reflexivity.
Qed.

Lemma extend_gso {A} f x (x' : A) y :
  y <> x ->
  f {x ~> x'} y = f y.
Proof.
  intros Heq. unfold extend. rewrite peq_false; eauto.
Qed.

Lemma extend_same f x y :
  f x = x ->
  f {y ~> y} x = x.
Proof.
  unfold extend. destruct (peq x y); eauto.
Qed.

Lemma extend_commut {A} f y x x' (y' : A) :
  x' <> x -> y' <> y ->
  f_eq ((f {x ~> y}) {x' ~> y'}) ((f {x' ~> y'}) {x ~> y}).
Proof.
  intros Hnin Hnin' z.
  destruct (peq x z); subst.
  - rewrite extend_gss, extend_gso; eauto.
    now rewrite extend_gss.
  - destruct (peq x' z); subst.
    + rewrite extend_gss, (extend_gso _ x y z); eauto.
      now rewrite extend_gss.
    + repeat rewrite extend_gso; eauto.
Qed.

Lemma f_eq_extend {A} (f f' : positive -> A) x y :
  f_eq f f' ->
  f_eq (f{x ~> y}) (f'{x ~> y}).
Proof.
  intros Heq.
  unfold extend. intros z.
  destruct (peq z x); eauto.
Qed.

Lemma f_eq_extend_same {A} (f : positive -> A) x y :
  f x = y ->
  f_eq (f{x ~> y}) f.
Proof.
  intros Heq x'.
    unfold extend. destruct (peq x' x); eauto.
    congruence.
Qed.

Lemma f_eq_subdomain_extend {A} S (f f' : positive -> A) x y :
  f_eq_subdomain S f f' ->
  f_eq_subdomain (Union _ (Singleton _ x) S) (f{x ~> y}) (f'{x ~> y}).
Proof.
  intros Heq.
  unfold extend. intros z Hin.
  destruct (peq z x). now eauto.
  apply Heq. inv Hin; [| now eauto ]. inv H; congruence.
Qed.

Lemma f_eq_subdomain_extend_not_In_S_l {A} f1 S f2 x (x' : A)  :
  ~ In _ S x ->
  f_eq_subdomain S f1 f2 ->
  f_eq_subdomain S (f1{x~>x'}) f2.
Proof.
  intros Hin Hfeq y HIn.
  rewrite extend_gso. now eauto.
  intros Hc. subst. contradiction.
Qed.

Lemma f_eq_subdomain_extend_not_In_S_r' {A} P (f1 f2 : positive -> A) v v' :
  f_eq_subdomain (Union _ P (Singleton _ v)) f1 (f2 {v ~> v'}) ->
  ~ In _ P v ->
  f_eq_subdomain P f1 f2.
Proof.
  intros Heq Hin x y. erewrite <- (extend_gso f2).
  apply Heq; constructor; eauto.
  intros Hc. subst. eauto.
Qed.

Lemma f_eq_subdomain_extend_not_In_S_r {A} f1 S f2 x (x' : A) :
  ~ In _ S x ->
  f_eq_subdomain S f1 f2 ->
  f_eq_subdomain S f1 (f2{x~>x'}).
Proof.
  intros Hin Hfeq y HIn.
  rewrite extend_gso. now eauto.
  intros Hc. subst. contradiction.
Qed.

Lemma f_eq_subdomain_extend_lst_Disjoint {A} S xs vs (f : positive -> A) :
  Disjoint _ (FromList xs) S ->
  f_eq_subdomain S (f <{ xs ~> vs }>) f.
Proof.
  intros Hd. revert vs; induction xs; simpl; intros vs.
  - reflexivity.
  - destruct vs. reflexivity. normalize_sets.
    eapply f_eq_subdomain_extend_not_In_S_l.
    + intros Hc. eapply Hd. constructor; eauto.
    + eapply IHxs. now eauto with Ensembles_DB.
Qed.


Lemma map_extend_not_In {A} f l x (x' : A) :
  ~ In _ (FromList l) x ->
  map (f{x~>x'}) l = map f l.
Proof.
  induction l; intros Hnin; eauto.
  simpl. rewrite extend_gso.
  f_equal. eapply IHl.
  intros Hc; eapply Hnin; rewrite FromList_cons; eauto.
  intros Hc; eapply Hnin; subst; rewrite FromList_cons; eauto.
Qed.

Lemma image_extend_not_In_S {A} f x (x' : A) S :
  ~ In _ S x ->
  Same_set _ (image (f {x ~> x'} ) S) (image f S).
Proof.
  intros Hnin.
  split; intros y [y' [Hin Heq]]. rewrite extend_gso in Heq.
  now eexists; eauto. intros Hc. subst. contradiction.
  eexists; split; eauto. rewrite extend_gso. now eauto.
  intros Hc. subst. contradiction.
Qed.

Lemma image_extend_In_S f x (x' : positive) S :
  In _ S x ->
  Same_set _ (image (f {x ~> x'}) S)
           (Union _ (image f (Setminus _ S (Singleton _ x)))
                  (Singleton _ x')).
Proof.
  intros HinS. split.
  - intros y [y' [Hin Heq]]; subst.
    destruct (peq x y').
    + subst. rewrite extend_gss. eauto.
    + rewrite extend_gso; eauto. left.
      eexists; split; eauto. constructor; eauto.
      intros Hc; inv Hc; congruence.
  - intros y Hin.
    destruct (peq x' y); subst.
    + eexists; split; eauto. rewrite extend_gss; eauto.
    + inv Hin.
      * destruct H as [y' [Hin Heq]]; subst. inv Hin.
        eexists; split. now eauto. rewrite extend_gso; eauto.
        intros Heq; subst. eauto.
      * inv H. congruence.
Qed.

Lemma image_Setminus_extend f v (v' : positive) S :
  Included _ (image (f {v ~> v'}) (Setminus _ S  (Singleton positive v)))
           (image f S).
Proof.
  rewrite image_extend_not_In_S.
  apply image_monotonic.
  now apply Setminus_Included.
  intros Hc. inv Hc. eapply H0; eauto.
Qed.

Lemma image_extend_Included {A} f x (x' : A) S :
  Included _ (image (f {x ~> x'}) S) (Union _ (image f S) (Singleton _ x')).
Proof.
  intros y [y' [Hin Heq]]. unfold extend in Heq.
  destruct (peq y' x); subst; [ now eauto |] .
  left. eexists; eauto.
Qed.

Lemma image_extend_Included' {A} f x x' S :
  Included A (image (f {x ~> x'}) S)
           (Union A (image f (Setminus _ S (Singleton _ x))) (Singleton A x')).
Proof.
  intros y [y' [Hin Heq]]; subst.
  destruct (peq x y'); subst.
  - rewrite extend_gss. eauto.
  - left. rewrite extend_gso; eauto.
    eexists. split; eauto.
    constructor; eauto. intros Hc; inv Hc; congruence.
Qed.

Lemma In_image {A B} S f x:
  In A S x ->
  In B (image f S) (f x).
Proof.
  intros; repeat eexists; eauto.
Qed.

Lemma image_Setminus {A B} S1 S2 {Hd: Decidable S2} (f : A -> B) :
  image f S1 \\ image f S2 \subset image f (S1 \\ S2).
Proof.
  intros x Hin. inv Hin. destruct Hd as [D].
  destruct H as [y [Hin' Heq]]. subst. destruct (D y).
  - exfalso. eapply H0. eapply In_image. eassumption.
  - eapply In_image. constructor; eauto.
Qed.


Lemma Included_image_extend g S x (x' : positive) :
  ~ In _ S x ->
  Included _ (image g S)
           (image (g {x ~> x'}) (Union _ (Singleton _ x) S)).
Proof.
  intros H.
  eapply Included_trans.
  eapply image_extend_not_In_S. eassumption. eapply image_monotonic.
  now apply Included_Union_r.
Qed.

Lemma image_Setminus_Disjoint {A B} (f : A -> B) s1 s2 :
  Disjoint _ (image f (s1 \\ s2)) (image f s2)  ->
  image f (s1 \\ s2) <--> image f s1 \\ image f s2.
Proof.
  intros Hd; split; intros x Him.
  - destruct Him as [z [Hin Heq]]; subst.
    inv Hin. constructor. eexists; split; eauto. intros Hc.
    eapply Hd. constructor; eauto. eapply In_image. constructor; eauto.
  - inv Him.
    assert (Hs' := H). edestruct H as [z [Hin Heq]]; subst.
    eapply In_image. constructor; eauto.
    intros Hc. eapply H0. eapply In_image. eassumption.
Qed.

Create HintDb functions_BD.
#[global] Hint Constants Opaque : functions_BD.
#[global] Hint Projections Opaque : functions_BD.
#[global] Hint Variables Opaque : functions_BD.

#[global] Hint Resolve In_image Included_image_extend : functions_BD.


(** * Lemmas about [extend_lst]  *)

Lemma extend_lst_gso {A} f l (l' : list A) x :
  ~ In _ (FromList l) x ->
  f <{l ~> l' }> x = f x.
Proof.
  revert l'; induction l; intros l' Hnin; simpl; eauto.
  destruct l'; eauto. rewrite FromList_cons in Hnin.
  rewrite extend_gso. eapply IHl.
  intros Hc. eapply Hnin; eauto.
  intros Hc. subst; eapply Hnin; eauto.
Qed.

Lemma extend_lst_gss {A} f l (l' : list A) x :
  In _ (FromList l) x ->
  length l = length l' ->
  exists x', f <{ l ~> l' }> x = x' /\ List.In x' l'.
Proof.
  revert l'; induction l; intros l' Hnin Hlen; simpl; eauto.
  - inv Hnin.
  -  destruct l'; try discriminate. rewrite FromList_cons in Hnin.
     destruct (peq x a); subst.
     + rewrite extend_gss.
       eexists; split; eauto. now constructor.
     + rewrite extend_gso; eauto. edestruct IHl as [x' [Heq HIn]].
       inv Hnin; eauto. inv H; congruence.
       inv Hlen. eassumption.
       eexists; split; eauto. now constructor 2.
Qed.

Lemma f_eq_subdomain_extend_lst
      (A : Type) (S : Ensemble positive) (f f' : positive -> A)
      (xs : list positive) (ys : list A) :
  List.length xs = List.length ys ->
  f_eq_subdomain (S \\ FromList xs) f f' ->
  f_eq_subdomain S (f <{xs ~> ys}>) (f' <{xs ~> ys}>).
Proof.
  revert A S f f' ys.
  induction xs; intros.
  - simpl. repeat normalize_sets. eassumption.
  - destruct ys; simpl. inv H. inv H. simpl.
    normalize_sets. eapply f_eq_subdomain_antimon.
    2:{ eapply f_eq_subdomain_extend.
        eapply IHxs; eauto. rewrite <- Setminus_Union in H0.
        eassumption. }
    xsets.
    rewrite Union_Setminus_Included; tci; sets.
Qed.

Lemma extend_lst_get_nth_error :
  forall A vars1 vars2 n (f: positive -> A) v1 v2,
    List.length vars1 = List.length vars2 ->
    NoDup vars1 ->
    nth_error vars1 n = Some v1 ->
    nth_error vars2 n = Some v2 ->
    (f <{ vars1 ~> vars2 }>) v1 = v2.
Proof.
  intros A vars1. induction vars1; intros vars2 n f v1 v2 Hlen Hdup Hv1 Hv2.
  - destruct vars2 eqn:Hvars2.
    destruct n eqn:Hn; simpl in Hv1; inv Hv1.
    inv Hlen.
  - destruct vars2 eqn:Hvars2.
    inv Hlen.
    destruct n eqn:Hn.
    + simpl in Hv1, Hv2.
      inv Hv1. inv Hv2.
      simpl. rewrite extend_gss. reflexivity.
    + simpl in *.
      rewrite extend_gso.
      eapply IHvars1. lia.
      inv Hdup. eassumption.
      eassumption.
      eassumption.
      intros Heq.
      eapply nth_error_In in Hv1.
      inv Hdup. contradiction.
Qed.


Lemma extend_lst_app {A} (f : positive -> A) xs xs' ys ys' :
  length xs = length ys ->
  f_eq (f <{xs ++ xs' ~> ys ++ ys'}>)
       (f <{xs' ~> ys'}> <{xs ~> ys}>).
Proof.
  revert ys f. induction xs; intros ys f Hlen.
  - simpl. destruct ys; try discriminate. reflexivity.
  - destruct ys; try discriminate. simpl.
    eapply f_eq_extend.
    eapply IHxs. inv Hlen. reflexivity.
Qed.

Lemma image_extend_lst_Included {A} f S xs xs' :
  length xs = length xs' ->
  Included _ (image (f <{xs ~> xs'}>) S)
           (Union A (image f (Setminus _ S (FromList xs))) (FromList xs')).
Proof with now eauto with Ensembles_DB.
  revert xs' f S; induction xs; intros xs' f S Hlen.
  - simpl. rewrite FromList_nil, Setminus_Empty_set_neut_r...
  - destruct xs'; try discriminate. inv Hlen.
    simpl. eapply Included_trans.
    apply image_extend_Included'. rewrite !FromList_cons.
    eapply Union_Included; [| now eauto with Ensembles_DB ].
    eapply Included_trans. eapply IHxs; eauto.
    apply Included_Union_compat.
    eapply image_monotonic...
    now eauto with Ensembles_DB.
Qed.

Lemma FromList_image_exists {A B} (f : A -> B) l S :
  FromList l \subset image f S ->
  exists l', l = map f l'.
Proof with (now eauto with Ensembles_DB).
  revert S; induction l; intros S Heq; eauto.
  - eexists []. reflexivity.
  - rewrite FromList_cons in Heq.
    edestruct IHl as [l' Heql'].
    + eapply Included_trans; try eassumption...
    + edestruct Heq as [a' [Heqa Hina]]. now left.
      eexists (a' :: l'). simpl; f_equal; eauto.
Qed.

Lemma extend_extend_lst_commut {A} f ys xs x (y : A) :
  ~ List.In x xs ->
  ~ List.In y ys ->
  length xs = length ys ->
  f_eq ((f {x ~> y}) <{xs ~> ys}>) ((f <{xs ~> ys}>) {x ~> y}).
Proof.
  revert f ys; induction xs; intros f ys Hnin1 Hnin2 Hlen; simpl.
  - reflexivity.
  - destruct ys; try discriminate. inv Hlen.
    rewrite IHxs. rewrite extend_commut. reflexivity.
    intros Hc; subst. now eapply Hnin1; constructor.
    intros Hc; subst. now eapply Hnin2; constructor.
    intros Hc; subst. now eapply Hnin1; constructor 2.
    intros Hc; subst. now eapply Hnin2; constructor 2.
    eassumption.
Qed.

Lemma map_extend_lst_Disjoint {A} f l xs (xs' : list A) :
  Disjoint _ (FromList l) (FromList xs)  ->
  map (f <{xs ~> xs'}> ) l = map f l.
Proof.
  revert xs'; induction xs; intros xs' HD; eauto.
  destruct xs'; eauto. simpl.
  rewrite FromList_cons in HD.
  rewrite map_extend_not_In. eapply IHxs.
  now eauto with Ensembles_DB.
  intros Hc. eapply HD; eauto.
Qed.

Lemma map_extend_lst_same {A} f xs (xs' : list A) :
  NoDup xs ->
  length xs = length xs' ->
  map (f <{xs ~> xs'}> ) xs = xs'.
Proof.
  revert xs'; induction xs; intros xs' Hnd Hlen; eauto.
  - destruct xs'; try discriminate. reflexivity.
  - simpl. destruct xs'; try discriminate.
    inv Hnd. inv Hlen.
    rewrite extend_gss. f_equal.
    rewrite map_extend_not_In; eauto.
Qed.

#[global] Instance extend_lst_Proper {A} : Proper (f_eq ==> eq ==> eq ==> f_eq) (@extend_lst A).
Proof.
  intros f1 f2 f_eq l1 l2 Heq1 l1' l2' Heq2; subst.
  revert l2'. induction l2; simpl; intros l2'; eauto.
  destruct l2'; eauto. rewrite IHl2. reflexivity.
Qed.

(** * Lemmas about [injective_subdomain] and [injective] *)

#[global] Instance injective_subdomain_Proper_f_eq {A B} : Proper (eq ==> f_eq ==> iff)
                                                   (@injective_subdomain A B).
Proof.
  intros s1 s2 Hseq f1 f2 Hfeq; split; intros Hinj x y Hin1 Hin2 Heq; subst;
  eapply Hinj; eauto. now rewrite !Hfeq. now rewrite <- !Hfeq.
Qed.

#[global] Instance injective_subdomain_Proper_Same_set {A B} : Proper (Same_set _ ==> eq ==> iff)
                                                   (@injective_subdomain A B).
Proof.
  intros s1 s2 Hseq f1 f2 Hfeq; split; intros Hinj x y Hin1 Hin2 Heq; subst;
  eapply Hinj; eauto; now apply Hseq.
Qed.

#[global] Instance injective_Proper {A B} : Proper (f_eq ==> iff)
                                         (@injective A B).
Proof.
  now apply injective_subdomain_Proper_f_eq.
Qed.


Lemma injective_subdomain_antimon {A B} (σ : A -> B) S S' :
  injective_subdomain S σ ->
  Included _ S' S ->
  injective_subdomain S' σ .
Proof.
  intros Hinj Hinc x y Hin Hin' Heq. eauto.
Qed.

Lemma injective_subdomain_Union {A B} (f : A -> B) S1 S2 :
  injective_subdomain S1 f ->
  injective_subdomain S2 f ->
  Disjoint  _ (image f S1) (image f S2) ->
  injective_subdomain (Union A S1 S2) f.
Proof.
  intros Hinj1 Hinj2 HD x1 x2 Hin1 Hin2 Heq.
  inv Hin1; inv Hin2.
  - eauto.
  - exfalso. eapply HD. constructor; eexists; eauto.
  - exfalso. eapply HD. constructor; eexists; eauto.
  - eauto.
Qed.

Lemma injective_subdomain_Singleton {A B} (f : A -> B) x :
  injective_subdomain (Singleton _ x) f.
Proof.
  intros x1 x2 Hin1 Hin2 Heq. inv Hin1. inv Hin2.
  reflexivity.
Qed.

Lemma injective_subdomain_Empty_set {A B} (f : A -> B) :
  injective_subdomain (Empty_set _) f.
Proof.
  intros x1 x2 Hin1 Hin2 Heq. inv Hin1.
Qed.

Lemma injective_subdomain_extend {A} f x (x' : A) S :
  injective_subdomain S f ->
  ~ In _ (image f (Setminus _ S (Singleton _ x))) x' ->
  injective_subdomain (Union _ (Singleton _ x) S) (f {x~>x'}).
Proof.
  intros Hinj Hnin.
  intros y y' Hin1 Hin2.
  destruct (peq x y); subst.
  - rewrite extend_gss. intros Heq.
    destruct (peq y y'); [ now eauto | ].
    rewrite extend_gso in Heq; [| now eauto ].
    exfalso. eapply Hnin. eexists; split; [| now eauto ].
    inv Hin2. inv H. congruence.
    constructor; eauto. intros Hc; inv Hc; congruence.
  - rewrite extend_gso; [| now eauto ].
    destruct (peq x y'); subst.
    + rewrite extend_gss. intros Heq. subst.
      exfalso. apply Hnin. eexists.
      split; [| reflexivity ].
      inv Hin1. inv H; congruence.
      constructor; eauto. intros Hc; inv Hc; congruence.
    + rewrite extend_gso; [| now eauto ].
      intros Heq. eapply Hinj; eauto.
      inv Hin1. inv H; congruence. eassumption.
      inv Hin2. inv H; congruence. eassumption.
Qed.

Lemma injective_subdomain_extend'' {A} f x (x' : A) S :
  injective_subdomain S f ->
  ~ In _ (image f (Setminus _ S (Singleton _ x))) x' ->
  injective_subdomain S (f {x~>x'}).
Proof.
  intros Hinj Hnin.
  intros y y' Hin1 Hin2.
  destruct (peq x y); subst.
  - rewrite extend_gss. intros Heq.
    destruct (peq y y'); [ now eauto | ].
    rewrite extend_gso in Heq; [| now eauto ].
    exfalso. eapply Hnin. eexists; split; [| now eauto ].
    constructor; eauto. intros Hc; eapply n. now inv Hc.
  - rewrite extend_gso; [| now eauto ].
    destruct (peq x y'); subst.
    + rewrite extend_gss. intros Heq. subst.
      exfalso. apply Hnin. eexists.
      split; [| reflexivity ].
      constructor; eauto. intros Hc; eapply n. now inv Hc.
    + rewrite extend_gso; [| now eauto ].
      intros Heq. eapply Hinj; eauto.
Qed.

Lemma injective_subdomain_extend' S f x x' :
  injective_subdomain (Setminus _ S (Singleton _ x)) f ->
  ~ In positive (image f (Setminus positive S (Singleton _ x))) x' ->
  injective_subdomain S (f {x ~> x'}).
Proof.
  intros Hinj Hnin y z Hin Hin' Heq.
  destruct (peq x y); destruct (peq x z); subst; eauto;
  try rewrite extend_gss in Heq; try rewrite !extend_gso in Heq; eauto.
  - subst. exfalso. eapply Hnin. eexists; split; eauto.
    constructor; eauto.
    intros Hc; inv Hc; subst; congruence.
  - subst. exfalso. eapply Hnin. eexists; split; eauto.
    constructor; eauto.
    intros Hc; inv Hc; subst; congruence.
  - subst. eapply Hinj in Heq; eauto.
    constructor; eauto.
    intros Hc; inv Hc; subst; congruence.
    constructor; eauto.
    intros Hc; inv Hc; subst; congruence.
Qed.

Lemma injective_subdomain_extend_lst S f xs xs' :
  injective_subdomain (Setminus _ S (FromList xs)) f ->
  Disjoint positive (image f (Setminus positive S (FromList xs))) (FromList xs') ->
  NoDup xs' ->
  length xs = length xs' ->
  injective_subdomain S (f <{xs ~> xs'}>).
Proof with now eauto with Ensembles_DB.
  revert xs' f S. induction xs; intros xs' f S Hinj HD Hnd Hlen.
  - simpl. rewrite FromList_nil, Setminus_Empty_set_neut_r in Hinj. eassumption.
  - destruct xs'; try discriminate.
    inv Hlen. simpl.
    rewrite !FromList_cons in HD. rewrite !FromList_cons in Hinj. inv Hnd.
    eapply injective_subdomain_extend'.
    + eapply IHxs. rewrite Setminus_Union. eassumption.
      eapply Disjoint_Included; [ | | eassumption ].
      now eauto with Ensembles_DB.
      rewrite Setminus_Union. reflexivity.
      eassumption. eassumption.
    + intros Hc. eapply image_extend_lst_Included in Hc; eauto.
      inv Hc.
      eapply HD. constructor.
      rewrite <- Setminus_Union. eassumption.
      now eauto with Ensembles_DB.
      eapply H2; eassumption.
Qed.

Lemma injective_subdomain_compose {A B C} (S1 : Ensemble A) (f1 : A -> B) (f2 : B -> C) :
  injective_subdomain S1 f1 ->
  injective_subdomain (image f1 S1) f2 ->
  injective_subdomain S1 (f2 ∘ f1).
Proof.
  intros Hi1 Hi2 x y Hin1 Hin2 Heq.
  unfold compose in *. eapply Hi2 in Heq; eauto.
  eexists; split; [| reflexivity ]; eauto.
  eexists; split; [| reflexivity ]; eauto.
Qed.


Lemma injective_extend (f : positive -> positive) x y :
  injective f ->
  ~ In _ (codomain f) y ->
  injective (f{x ~> y}).
Proof.
  intros Hinj Hin x1 x2 __ _ Heq.
  unfold extend in *.
  edestruct (peq x1 x).
  - rewrite <- e in Heq.
    edestruct (peq x2 x1); [ now eauto |].
    exfalso. eapply Hin. eexists; eauto.
  - edestruct (peq x2 x).
    + exfalso. eapply Hin. eexists; eauto.
    + eapply Hinj; try now constructor; eauto.
      assumption.
Qed.

Lemma injective_subdomain_Union_not_In_image {A B} (f : A -> B) S1 S2 :
  injective_subdomain (Union _ S1 S2) f ->
  Disjoint _ S1 S2 ->
  Disjoint _ (image f S1) (image f S2).
Proof.
  intros Hinj. constructor; intros x Hin. inv Hin.
  destruct H0 as [y [Hin Heq]]. destruct H1 as [y' [Hin' Heq']].
  subst. eapply Hinj in Heq'; eauto. eapply H. subst; eauto.
Qed.

Lemma FromList_image_injective_exists (f : positive -> positive) l S :
  FromList l <--> image f S ->
  injective_subdomain S f ->
  exists l', l = map f l' /\ FromList l' <--> S.
Proof with (now eauto with Ensembles_DB).
  revert S; induction l; intros S Heq Hinj; eauto.
  - eexists []. split; eauto.
    rewrite !FromList_nil in Heq.
    rewrite FromList_nil.
    split; intros x Hin; try now inv Hin.
    assert (Hc : Empty_set _ (f x)).
    { eapply Heq. eexists; split; eauto. }
    inv Hc.
  - rewrite FromList_cons in Heq.
    assert (Ha : image f S a).
    { eapply Heq; now left. }
    destruct Ha as [a' [Heqa Hina]]. subst.

    destruct (Decidable_FromList l) as [Decl].
    destruct (Decl (f a')).
    + rewrite Union_Same_set in Heq;
        [| eapply Singleton_Included; now eauto ].
      edestruct IHl as [l' [Heql Heqs]]; eauto.
      subst.
      eexists (a' :: l'). split. now simpl; f_equal; eauto.
      rewrite FromList_cons.
      rewrite Union_Same_set. eassumption.
      rewrite Heqs. eapply Singleton_Included. eassumption.
    + assert (Heq' := Heq).
      rewrite (Union_Setminus_Same_set S [set a']) in Heq;
        [| eapply Singleton_Included; now eauto ].
      rewrite image_Union, image_Singleton in Heq.
      eapply Union_Same_set_Disjoint in Heq.
      * edestruct IHl as [l' [Heql Heqs]]; try now apply Heq; eauto; subst.
        eapply injective_subdomain_antimon; try eassumption...

        eexists (a' :: l'). split. now simpl; f_equal; eauto.
        rewrite FromList_cons.
        rewrite Heqs.
        rewrite <- (Union_Setminus_Same_set S [set a']);
          [| eapply Singleton_Included; now eauto ].
        reflexivity.
      * eapply Disjoint_Singleton_l. eauto.
      * rewrite <- image_Singleton.
        eapply injective_subdomain_Union_not_In_image.
        eapply injective_subdomain_antimon; try eassumption...
        eapply Disjoint_Singleton_l.
        intros Hc; inv Hc; eauto.
Qed.


(** * Lemmas about [domain] *)


#[global] Instance Proper_domain {A B} : Proper (f_eq ==> Same_set A) (@domain A B).
Proof.
  constructor; intros x' [y' H'].
  rewrite H in H'. repeat eexists; eauto.
  rewrite <- H in H'. repeat eexists; eauto.
Qed.

Lemma domain_extend_None {A} (f : positive -> option A) x :
  Included _ (domain f) (Union _ (Singleton _ x) (domain (f {x ~> None}))).
Proof.
  intros y [z Hin].
  destruct (peq x y); subst; eauto.
  right. eexists. rewrite extend_gso; eauto.
Qed.

Lemma domain_extend_Some (A : Type) (f : positive -> option A) (x : positive) y :
  Same_set positive
           (Union positive (Singleton positive x) (domain f))
           (domain (f {x ~> Some y})).
Proof.
  split.
  - intros z Hin. destruct (peq x z); subst.
    repeat eexists; eauto. rewrite extend_gss. reflexivity.
    inv Hin. inv H. congruence.
    edestruct H.
    repeat eexists; eauto. rewrite extend_gso; eauto.
  - intros z Hin. destruct (peq x z); subst; eauto.
    right. destruct Hin as [w H1]. rewrite extend_gso in H1; eauto.
    repeat eexists; eauto.
Qed.

Lemma domain_extend_is_Some_Same_set {A} f x (y : A) :
  domain (f {x ~> Some y}) <--> (domain f :|: [set x]).
Proof.
  split; intros z H.
  - destruct H as [w H'].
    destruct (peq x z); subst; eauto.
    rewrite extend_gso in H'; eauto. left.
    eexists; eauto.
  - destruct (peq x z); subst; eauto.
    + eexists. rewrite extend_gss; eauto.
    + inv H. destruct H0.
      eexists. rewrite extend_gso; eauto.
      inv H0; congruence.
Qed.

(** * Lemmas about [image'] *)

#[global] Instance Proper_image' {A B} :
  Proper (f_eq ==> Same_set _ ==> Same_set B) (@image' A B).
Proof.
  constructor; intros x' [y' [H1 H2]]; inv H0.
  rewrite H in H2. repeat eexists; eauto.
  rewrite <- H in H2. repeat eexists; eauto.
Qed.

Lemma image'_Empty_set {A B} (f : A -> option B) :
  image' f (Empty_set _) <--> Empty_set _.
Proof.
  firstorder.
Qed.

Lemma image'_Singleton_Some {A B} f (x : A) (y : B) :
  f x = Some y ->
  image' f [set x] <--> [set y].
Proof.
  intros Heq.
  split; intros z Hin.
  - destruct Hin as [z' [Hin Heq']]. inv Hin.
    rewrite Heq in Heq'. inv Heq'. reflexivity.
  - inv Hin. eexists; split; eauto.
Qed.

Lemma image'_Singleton_None {A B} (f : A -> option B) (x : A) :
  f x = None ->
  image' f [set x] <--> Empty_set _.
Proof.
  intros Heq.
  split; intros z Hin.
  - destruct Hin as [z' [Hin Heq']]. inv Hin.
    rewrite Heq in Heq'. congruence.
  - inv Hin.
Qed.


Lemma image'_monotonic {A B} (S1 S2 : Ensemble A) (f : A -> option B) :
  S1 \subset S2 ->
  image' f S1 \subset image' f S2.
Proof.
  firstorder.
Qed.

Lemma image'_Union (A B : Type) (S1 S2 : Ensemble A) (g : A -> option B) :
  image' g (S1 :|: S2) <--> image' g S1 :|: image' g S2.
Proof.
  split; intros x Hin.
  - destruct Hin as [y [Hin Heq]]; subst; inv Hin.
    left; eexists; split; eauto.
    right; eexists; split; eauto.
  - inv Hin.
    + destruct H as [z [Hin Heq]].
      eexists; split; eauto.
    + destruct H as [z [Hin Heq]].
      eexists; split; eauto.
Qed.

Lemma image'_extend_Included_Some (A : Type) (f : positive -> option A) (x : positive)
      (x' : A) (S : Ensemble positive):
  image' (f {x ~> Some x'}) S \subset image' f (S \\ [set x]) :|: [set x'].
Proof.
  intros z [y [Heq Hin]].
  destruct (peq x y); subst.
  - rewrite extend_gss in Hin. inv Hin; eauto.
  - rewrite extend_gso in Hin; eauto.
    left. eexists; split; eauto.
    constructor; eauto. intros Hc; inv Hc; eauto.
Qed.

Lemma image'_extend_Included_None (A : Type) (f : positive -> option A) (x : positive)
      (S : Ensemble positive):
  image' (f {x ~> None}) S \subset image' f (S \\ [set x]).
Proof.
  intros z [y [Heq Hin]].
  destruct (peq x y); subst.
  - rewrite extend_gss in Hin. inv Hin; eauto.
  - rewrite extend_gso in Hin; eauto.
    eexists; split; eauto.
    constructor; eauto. intros Hc; inv Hc; eauto.
Qed.

Lemma image'_extend_In_S (f : positive -> option positive) (x x' : positive)
      (S : Ensemble positive) :
  In positive S x ->
  image' (f {x ~> Some x'}) S <--> image' f (S \\ [set x]) :|: [set x'].
Proof.
  intros Hin; split; intros y Him.
  - destruct Him as [y' [Heq Him]].
    destruct (peq x y'); subst.
    + rewrite extend_gss in Him. inv Him.
      right. reflexivity.
    + rewrite extend_gso in Him.
      left. eexists; split; eauto. constructor; eauto.
      intros Hc; inv Hc; eauto.
      intros Hc; inv Hc; eauto.
  - destruct Him as [z [y' [Heq Him]] | z Heq ].
    + eexists. split. now eapply Heq.
      rewrite extend_gso. eassumption. intros Hc.
      subst. inv Heq; eauto.
    + eexists; split; eauto. inv Heq.
      rewrite extend_gss. reflexivity.
Qed.

Lemma image'_Singleton_is_Some {A B} (f : A -> option B) x y :
  f x = Some y ->
  (image' f ([set x])) <--> [set y].
Proof.
  split; intros z H'.
  - destruct H' as [w [Hin Heq ]].
    inv Hin. rewrite Heq in H; inv H. eauto.
  - inv H'. eexists; split; eauto.
Qed.

Lemma image'_extend_is_Some {B} f x y S :
  Included B (image' (f {x ~> Some y}) S)
           (Union _ (image' f (Setminus _ S (Singleton _ x))) (Singleton _ y)).
Proof.
  intros z H'.
  destruct H' as [w [Hin Heq ]].
  destruct (peq x w); subst.
  - rewrite extend_gss in Heq. inv Heq.
    eauto.
  - rewrite extend_gso in Heq; eauto.
    left. eexists; split; eauto.
    constructor; eauto. intros Hc; inv Hc; congruence.
Qed.

Lemma image'_extend_is_Some_In_P {B} f x y S :
  In _ S x ->
  Same_set B (image' (f {x ~> Some y}) S)
           (Union _ (image' f (Setminus _ S (Singleton _ x))) (Singleton _ y)).
Proof.
  intros Hin. split.
  - now apply image'_extend_is_Some; eauto.
  - intros z H'. inv H'.
    + destruct H as [w [Hin' Heq]].
      destruct (peq x w); subst.
      * inv Hin'. exfalso; eauto.
      * inv Hin'. eexists; split; eauto.
        rewrite extend_gso; eauto.
    + inv H. eexists; split; eauto.
      rewrite extend_gss; eauto.
Qed.

Lemma image'_extend_is_Some_not_In_P {B} f x y S :
  ~ In _ S x ->
  Same_set B (image' (f {x ~> Some y}) S) (image' f S).
Proof.
  intros Hnin. split.
  - intros z H'.
    destruct H' as [w [Hin Heq ]].
    destruct (peq x w); subst.
    + rewrite extend_gss in Heq. inv Heq. exfalso; eauto.
    + rewrite extend_gso in Heq; eauto.
      eexists; split; eauto.
  - intros z [w [Hin Heq]].
    destruct (peq x w); subst.
    + exfalso; eauto.
    + eexists; split; eauto. rewrite extend_gso; eauto.
Qed.

#[global] Instance Proper_image'_Same_set {A B} :
  Proper (eq ==> Same_set A ==> Same_set B) image'.
Proof.
  intros f1 f2 Hfeq s1 s2 Hseq; split; intros x [y [Hin Heq]];
    subst; eexists; split; eauto; eapply Hseq; eauto.
Qed.

Lemma image'_feq_subdomain {A B} (f1 f2 : A -> option B) S :
  f_eq_subdomain S f1 f2 ->
  image' f1 S <--> image' f2 S.
Proof.
  intros Heq; split; intros x [y [Hin Heq']]; eexists; split; eauto.
  now rewrite <- Heq; eauto. now rewrite Heq; eauto.
Qed.


(** * Lemmas about [injective_subdomain'] *)

Lemma injective_subdomain'_antimon {A B} P1 P2 (f : A -> option B) :
  injective_subdomain' P2 f ->
  P1 \subset P2 ->
  injective_subdomain' P1 f.
Proof.
  intros Hinj Hsub x1 x2 v Hin1 Hin2 Heq1 Heq2.
  eapply Hinj; eauto.
Qed.

#[global] Instance Proper_injective_subdomain' A B :
  Proper (Same_set A ==> eq ==> iff) (@injective_subdomain' A B).
Proof.
  intros s1 s2 Hseq f1 f2 Hfeq; subst; split; intros Hinj x y v Hin1 Hin2 Heq1 Heq2;
  eapply Hinj; try eassumption; eapply Hseq; eauto.
Qed.

(** * Lemmas about [compose] *)

Open Scope program_scope.

Lemma compose_id_neut_l {A B} (f : A -> B) :
  f_eq (id ∘ f) f.
Proof.
  firstorder.
Qed.

Lemma compose_id_neut_r {A B} (f : A -> B) :
  f_eq (f ∘ id) f.
Proof.
  firstorder.
Qed.

Lemma compose_extend {B C} (f : B -> C) (g : positive -> B) x y :
  f_eq (f ∘ g {x ~> y}) ((f ∘ g) {x ~> f y}).
Proof.
  intros z. unfold compose. simpl.
  destruct (peq x z); subst. simpl.
  - rewrite !extend_gss. reflexivity.
  - rewrite !extend_gso. reflexivity.
    now eauto. now eauto.
Qed.

Lemma compose_id_extend {B} S (f : B -> positive)  x y :
  ~ x \in image f S ->
          f_eq_subdomain S (id {x ~> y} ∘ f) f.
Proof.
  intros Hneq z Hin. unfold compose.
  rewrite extend_gso. reflexivity.
  intros Hc; eapply Hneq.
  eexists; split; eauto.
Qed.

Lemma compose_lift_id_extend {B} S (f : B -> option positive)  x y :
  ~ x \in image' f S ->
          f_eq_subdomain S (lift (id {x ~> y}) ∘ f) f.
Proof.
  intros Hneq z Hin. unfold compose, lift.
  destruct (f z) eqn:Heq; eauto.
  rewrite extend_gso. reflexivity.
  intros Hc; eapply Hneq.
  eexists; split; subst; eauto.
Qed.

#[global] Instance Proper_compose_l A B C : Proper (f_eq ==> eq ==> f_eq) (@compose A B C).
Proof.
  intros f1 f1' Hfeq f2 f2' Hfeq'; subst; firstorder.
Qed.

#[global] Instance Proper_compose_r A B C : Proper (eq ==> f_eq ==> f_eq) (@compose A B C).
Proof.
  intros f1 f1' Hfeq f2 f2' Hfeq'; subst. intros x; unfold compose; simpl.
  rewrite <- Hfeq'. reflexivity.
Qed.


(** * Lemmas about [app] *)

Lemma app_monotonic {A} (S1 S2 : Ensemble A) f n :
  (forall S1 S2, S1 \subset S2 -> f S1 \subset f S2) ->
  S1 \subset S2 ->
  (f ^ n) S1 \subset (f ^ n) S2.
Proof.
  induction n; intros H Hsub.
  - eassumption.
  - simpl. apply H. eapply IHn; eassumption.
Qed.

Lemma app_plus {A} (f : A -> A) m n :
  f_eq (f ^ (m + n)) ((f ^ m) ∘ (f ^ n)).
Proof.
  revert n; induction m; intros n; simpl.
  - rewrite compose_id_neut_l. reflexivity.
  - intros x. rewrite IHm. reflexivity.
Qed.

(** * Lemmas about [lift] *)

Lemma lift_id {A : Type} :
  f_eq (lift (@id A)) id.
Proof.
  intros x. destruct x; eauto.
Qed.

Lemma lift_compose {A B C : Type} (f2 : B -> C) (f1 : A -> B) :
  f_eq (lift (f2 ∘ f1)) (lift f2 ∘ lift f1).
Proof.
  intros [x|]; unfold lift, compose; simpl; reflexivity.
Qed.

(** * Properties of [inverse_subdomain] *)

Lemma inverse_subdomain_antimon {A B: Type} S S' (f : A -> B) g :
  inverse_subdomain S f g ->
  S' \subset S ->
  inverse_subdomain S' f g.
Proof.
  intros [Heq1 Heq2] Hsub.
  split; eapply f_eq_subdomain_antimon; eauto.
  eapply image_monotonic; eauto.
Qed.

#[global] Instance Proper_inverse_subdomain {A B} : Proper (Same_set A ==> eq ==> eq ==> iff) (@inverse_subdomain A B).
Proof.
  intros s1 s2 Hseq f1 f2 Hfeq g1 g2 Hgeq; subst.
  unfold inverse_subdomain. rewrite Hseq. reflexivity.
Qed.


Lemma inverse_subdomain_symm A B S (f1 : A -> B) (f2 : B -> A) :
  inverse_subdomain S f1 f2 ->
  inverse_subdomain (image f1 S) f2 f1.
Proof.
  intros [Hin1 Hin2]. split.
  rewrite <- image_compose.
  rewrite image_f_eq_subdomain; [| eassumption ].
  rewrite image_id. eassumption. eassumption.
Qed.

Lemma injective_subdomain_f_eq_subdomain {A B} S (f1 f2 : A -> B ) :
  injective_subdomain S f1 ->
  f_eq_subdomain S f1 f2 ->
  injective_subdomain S f2.
Proof.
  intros Hin1 Hsub x1 x2 H1 H2 Heq. eapply Hin1; eauto.
  rewrite !Hsub; eassumption.
Qed.


(** * left inverse properties *)

Definition left_inverse {A B} (f : A -> B) (h : B -> A) :=
  f_eq  (f ∘ h) id.


Parameter (M : nat).


Definition f (c : nat) := (c + M*c)%nat.

Definition h (x : nat) := (x/(1 + M))%nat.

Lemma left_inverse_f : left_inverse h f.
Proof.
  unfold left_inverse, f_eq, h, f, compose. intros x.
  replace x with (1 * x)%nat at 1 by lia.
  rewrite <- Nat.mul_add_distr_r.
  rewrite Nat.mul_comm.
  rewrite Nat.div_mul; try lia.
  reflexivity.
Qed.
