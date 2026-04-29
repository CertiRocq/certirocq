(* Relations library utilities. Part of the CertiRocq project.
 * Author: Anonymized, 2016
 *)

From Stdlib Require Import Relations.Relations Classes.RelationClasses.
From CertiRocq Require Import LambdaANF.term LambdaANF.ctx LambdaANF.tactics.

Section Relations.

  Variable (R : relation exp).
  (* TODO : abstract over exp ? *)

  Open Scope ctx_scope.

  Definition compose {A} (R1 : relation A) (R2 : relation A) : relation A :=
    fun x y => exists z, R1 x z /\ R2 z y.

  (** The compatible closure of R *)
  Inductive compat_closure : relation exp :=
  | Compat :
      forall e e' c,
        R e e' ->
        compat_closure (c |[ e ]|) (c |[ e' ]|).

  (** The reflexive transitive closure of R,
    * parametrized by the numbers of steps *)
  Inductive refl_trans_closure_n : nat -> relation exp :=
  | Trans :
      forall n e1 e2 e3,
        R e1 e2 ->
        refl_trans_closure_n n e2 e3 ->
        refl_trans_closure_n (S n) e1 e3
  | Refl :
      forall e, refl_trans_closure_n 0 e e.

  (** Compatible relation w.r.t to [f] *)
  Definition Compatible (R' : relation exp) :=
    forall e1 e2 c,
      R' e1 e2 -> R' (c |[ e1 ]|) (c |[ e2 ]|).

  (** Invariant w.r.t. a relation R *)
  Definition Invariant (R : relation exp) (I : exp -> Prop)  : Prop :=
    forall (e1 e2 : exp),
      I e1 -> R e1 e2 -> I e2.

  (* Better names for these two? *)

  (** If a property if true for [e] then it's true for it's subterms  *)
  Definition SubtermInvariant (I : exp -> Prop) :=
    forall c e,  I (c |[ e ]|) ->  I e.

  (** If a property if true for a term and we substitute a subterm [e] with a
    * term [e'] such that [R e e'], then it's true for the resulting term  *)
  Definition SubtermSubstInvariant (R : relation exp) (I : exp -> Prop) :=
    forall c e e', I (c |[ e ]|) -> R e e' ->  I (c |[ e' ]|).

  (** Lifting of an invariant w.r.t to a relation to the
    * reflexive transitive closure of the relation *)
  Lemma invariant_refl_trans_closure (I : exp -> Prop) n :
    Invariant R I ->
    Invariant (refl_trans_closure_n n) I.
  Proof.
    induction n.
    - intros HInv e1 e2 HI Hrw. inv Hrw; eauto.
    - intros HInv e1 e2 HI Hrw. inv Hrw.
      apply (IHn HInv e3 e2); eauto.
  Qed.

  (** Lifting of an invariant w.r.t to a relation to the
    * compatible closure of the relation *)
  Lemma invariant_compat_closure (R' : relation exp) (I : exp -> Prop) :
    Invariant R I ->
    SubtermInvariant I ->
    SubtermSubstInvariant (fun e e' => R' e e' /\ I e') I ->
    inclusion _ (fun e e' => R e e' /\ I e) R' ->
    Invariant compat_closure I.
  Proof.
    intros HInv HS1 HS2 HIn e1 e2 HI Hrw. inv Hrw.
    eapply HS2; eauto. split; eauto.
  Qed.

  Lemma refl_trans_closure_f_compat_strong n I e1 e2 f :
    Invariant R I ->
    (forall e1 e2, I e1 -> R e1 e2 -> R (f e1) (f e2)) ->
    I e1 ->
    refl_trans_closure_n n e1 e2 ->
    refl_trans_closure_n n (f e1) (f e2).
  Proof.
    intros Inv.
    revert e1 e2 f. induction n; intros e1 e2 f Hyp Hyp' H.
    - inv H. constructor.
    - inv H. econstructor. apply Hyp. eauto. eauto.
      apply IHn; eauto.
  Qed.


  Lemma refl_trans_closure_f_compat n e1 e2 f :
    (forall e1 e2, R e1 e2 -> R (f e1) (f e2)) ->
    refl_trans_closure_n n e1 e2 ->
    refl_trans_closure_n n (f e1) (f e2).
  Proof.
    intros.
    eapply refl_trans_closure_f_compat_strong with (I := fun _ => True); eauto.
    intros e1' e2'; eauto.
  Qed.

  Lemma refl_trans_closure_commut_strong n I (R' : relation exp) e1 e2 e1' :
    Invariant R I ->
    (forall e1 e2 e1',
       I e1 -> R' e1 e1' -> R e1 e2 ->
       exists e2', R e1' e2' /\ R' e2 e2') ->
    I e1 ->
    R' e1 e1' ->
    refl_trans_closure_n n e1 e2 ->
    exists e2',
      R' e2 e2' /\
      refl_trans_closure_n n e1' e2'.
  Proof.
    intros Inv.
    revert e1 e2 e1'. induction n; intros e1 e2 e1' Hyp Hyp' Hr1 H.
    - inv H. exists e1'. constructor; eauto. constructor.
    - inv H.
      edestruct Hyp as [e3' [Hrw' Hr3]]; eauto.
      edestruct IHn as [e2' [Hrw Hr2]]; [ | | | eauto |]; eauto.
      eexists. split; eauto. econstructor; eauto.
  Qed.

  Lemma refl_trans_closure_commut n (R' : relation exp) e1 e2 e1' :
    (forall e1 e2 e1',
       R' e1 e1' -> R e1 e2 ->
       exists e2', R e1' e2' /\ R' e2 e2') ->
    R' e1 e1' ->
    refl_trans_closure_n n e1 e2 ->
    exists e2',
      R' e2 e2' /\ refl_trans_closure_n n e1' e2'.
  Proof.
    intros.
    eapply refl_trans_closure_commut_strong with (I := fun _ => True); eauto.
    intros e1'' e2''; eauto.
  Qed.


  Lemma compat_closure_f_compat e1 e2 f :
    (forall e1 e2, R e1 e2 -> R (f e1) (f e2)) ->
    (forall c,  (exists c1, forall e, f (c |[ e ]|) = c1 |[ f e ]|) \/
                (exists c1, forall e, f (c |[ e ]|) = c1 |[ e ]|)) ->
    compat_closure e1 e2 ->
    compat_closure (f e1) (f e2).
  Proof.
    intros Hyp1 Hyp2 H. inv H.
    destruct (Hyp2 c) as [[c' Heq] | [c' Heq]]; rewrite !Heq; econstructor; eauto.
  Qed.

  Lemma compat_closure_f_compat_inv I (R' : relation exp) e1 e2 f :
    Invariant R I -> SubtermInvariant I -> SubtermSubstInvariant R' I ->
    (forall e1 e2, I e1 -> R e1 e2 -> R (f e1) (f e2)) ->
    (forall c,  (exists c1, forall e, f (c |[ e ]|) = c1 |[ f e ]|) \/
                (exists c1, forall e, f (c |[ e ]|) = c1 |[ e ]|)) ->
    I e1 ->
    inclusion _ R R' ->
    compat_closure e1 e2 ->
    compat_closure (f e1) (f e2).
  Proof.
    intros Inv HC1 HC2 Hyp1 Hyp2 HI Hinc H. inv H.
    destruct (Hyp2 c) as [[c' Heq] | [c' Heq]]; rewrite !Heq; econstructor; eauto.
  Qed.

(* (* How to call these two ?? *)
Definition rel_ctx_1 c (R : relation exp) :=
  exists c',
    (forall e e', R e e' -> R (c |[ e ]|) (c' |[ e' ]|)) /\
    (forall e e', R (c |[ e ]|) e' ->
                  exists e'', e' = c' |[ e'' ]| /\ R e e'').

 Definition rel_ctx_2 c (R : relation exp) :=
  exists c',
    (forall e, R (c |[ e ]|) (c' |[ e ]|)) /\
    (forall e e',
       R (c |[ e ]|) e' ->
       (exists e'', e' = c' |[ e'' ]| /\ R e e'') \/ (e' = c' |[ e ]|)).


Lemma compat_closure_R_compat I (R R' : relation exp) e1 e2 e1':
  invariant R I -> ctx_compat I ->
  (forall e1 e2 e1',
     I e1 -> R e1 e2 -> R' e1 e1' ->
     exists e2', R e1' e2' /\ R' e2 e2') ->
  (forall c, rel_ctx_1 c R' \/ rel_ctx_2 c R') ->
  I e1 ->
  R' e1 e1' ->
  compat_closure R e1 e2 ->
  exists e2', compat_closure R e1' e2' /\ R' e2 e2'.
Proof.
  intros Inv [HC1 HC2] Hyp1 Hyp2 HI Hr1 H. inv H.
  destruct (Hyp2 c) as [[c' [Hc1 Hc2]] | [c' [Hc1 Hc2]]].
  - destruct (Hc2 _ _ Hr1)  as [e1'' [Heq1 Hr1']]; subst.
    edestruct Hyp1 as [e2'' [Heq2 Hr2']]; subst.
    eapply HC2; eauto. eauto. eauto.
    eexists; split; eauto. constructor. eauto.
  - eapply Hc2 in Hr1. inv Hr1.
    + destruct H as [e'' [Heq Hr]]; subst.
      edestruct Hyp1 as [e2'' [Heq2 Hr2']]; subst.
Abort. *)

  Lemma refl_trans_closure_n_trans n m e1 e2 e3:
    refl_trans_closure_n n e1 e2 ->
    refl_trans_closure_n m e2 e3 ->
    refl_trans_closure_n (n+m) e1 e3.
  Proof.
    intros H1 H2. induction H1; eauto.
    econstructor 1; eauto.
  Qed.

  Lemma compat_closure_compat e1 e2 c :
    compat_closure e1 e2 ->
    compat_closure (c |[ e1 ]|) (c |[ e2 ]|).
  Proof.
    intros H. inv H. rewrite !app_ctx_f_fuse.
    constructor; eauto.
  Qed.

  (** If R is included R', and R' is compatible then the
      compatible closure of R is in R' *)
  Lemma relation_inclusion_compat (R' : relation exp) :
    inclusion _ R R' ->
    Compatible R' ->
    inclusion _ compat_closure R'.
  Proof.
    intros Hyp1 Hyp2 e1 e2 Hcomp. inv Hcomp. eauto.
  Qed.

  (** If R is included R', and R' is reflexive and transitive then the
      reflexive transitive closure of R is in R' *)
  Lemma relation_inclusion_refl_trans (R' : relation exp) n :
    (forall e1 e2, R e1 e2 -> R' e1 e2) ->
    Reflexive R' ->
    Transitive R' ->
    inclusion _ (refl_trans_closure_n n) R'.
  Proof.
    intros Hyp1 Hrefl Htrans e1 e2 Hstar. induction Hstar; eauto.
  Qed.

  (** If R is included R', and R' is compatible then the
      compatible closure of R is in R' *)
  Lemma relation_inclusion_compat_strong (Pre : exp -> Prop)
        (R' : relation exp) e1 e2 :
    (forall e1 e2, Pre e1 -> R e1 e2 -> R' e1 e2) ->
    Pre e1 ->
    SubtermInvariant Pre ->
    Compatible R' ->
    compat_closure e1 e2 ->
    R' e1 e2.
  Proof.
    intros H1 H2 H3 H4 Hcomp. inv Hcomp. eauto.
  Qed.

  (** If R is included R', and R' is reflexive and transitive then the
      reflexive transitive closure of R is in R' *)
  Lemma relation_inclusion_refl_trans_strong (Pre : exp -> Prop)
        (R' : relation exp) e1 e2 n :
    (forall e1 e2, Pre e1 -> R e1 e2 -> R' e1 e2) ->
    Pre e1 ->
    Invariant R Pre ->
    (forall e, Pre e -> R' e e) ->
    (forall e1 e2 e3, Pre e1 -> Pre e2 -> R' e1 e2 -> R' e2 e3 -> R' e1 e3) ->
    refl_trans_closure_n n e1 e2 ->
    R' e1 e2.
  Proof.
    intros H1 H2 H3 Hrefl Htrans Hstar. induction Hstar; eauto.
    eapply Htrans. eauto. eapply H3. eassumption. eassumption.
    now eauto. eapply IHHstar. eauto.
  Qed.

End Relations.
