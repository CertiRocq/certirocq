Require Import compcert.lib.Maps.
From Stdlib Require Import Relations.Relations.
From Stdlib Require Import Relations.
From Stdlib Require Import Setoid.
From Stdlib Require Import Morphisms.
Import RelationClasses.
Require Import Libraries.CpdtTactics ExtLib.Data.List.
From Stdlib Require Import Permutation NArith.BinNat.
(* Utility library for Compcert's Maps *)


Module M := Maps.PTree.
Definition var_dec := M.elt_eq.

Ltac destructAll :=
  match goal with
    | [ H : _ /\ _ |- _] => destruct H; destructAll
    | [ H : exists E, _ |- _ ] => destruct H; destructAll
    | _ => subst
  end.


Section DES.
  Arguments M.empty {A}.

  Theorem xelements_set_leaf {A}: forall  (v:A) i j acc,
    M.xelements' (M.set0 i v) j acc = ((M.prev_append j i), v)::acc.
    Proof.
      induction i; intros; simpl.
      - rewrite IHi. simpl. reflexivity.
      - rewrite IHi. simpl. reflexivity.
      - unfold M.prev.
        reflexivity.
    Qed.

    Theorem elements_set_leaf {A}: forall (v:A) i,
        M.elements (M.set i v M.empty) = cons (i,v) nil.
    Proof.
      intros. unfold M.elements. simpl.
      rewrite xelements_set_leaf. simpl. reflexivity.
  Qed.

    Lemma xelements_set_node_xI {A} i (v : A) l o r :
      M.set (xI i) v (M.Node l o r) = M.Node l o (M.set i v r).
    Proof.
      unfold M.set.
      destruct r; cbn; simpl;
      destruct l; destruct o; auto.
    Qed.


    Lemma xelements_set_node_xO {A} i (v : A) l o r :
      M.set (xO i) v (M.Node l o r) = M.Node (M.set i v l) o r.
    Proof.
      unfold M.set.
      destruct r; cbn; simpl;
      destruct l; destruct o; auto.
    Qed.

    Lemma xelements_set_node_xH {A} (v : A) l o r :
      M.set xH v (M.Node l o r) = M.Node l (Some v) r.
    Proof.
      unfold M.set.
      destruct r; cbn; simpl;
      destruct l; destruct o; auto.
    Qed.

    Theorem xelements_set_none:
    forall (A: Type) v (m: M.t A) i j,
      M.get i m = None ->
      exists l1 l2, M.xelements m j = app l1 l2 /\ M.xelements (M.set i v m) j =
        app l1 (cons (M.prev_append j i,v) l2).
    Proof.
      intros A v m.
      induction m using M.tree_ind; intros.
      - exists nil, nil.
        split; auto. cbn.
        unfold M.set; cbn. now rewrite xelements_set_leaf.
      - destruct i; simpl in *.
        + rewrite M.gNode in H0.
          rewrite xelements_set_node_xI, M.xelements_Node.
          apply IHm0 with (j:= xI j) in H0; do 3 (destruct H0).
          rewrite M.xelements_Node. cbn.
          rewrite H0.
          destruct o.
          * exists (M.xelements l (xO j) ++ ((M.prev j, a) :: x)), x0.
            split. cbn. now rewrite <- app_assoc.
            now rewrite <- app_assoc, H1.
          * exists ((M.xelements l (xO j)) ++ x), x0.
            split; auto. cbn.
            now rewrite <- app_assoc.
            now rewrite H1, <- app_assoc.
        + rewrite M.gNode in H0.
          rewrite xelements_set_node_xO, !M.xelements_Node.
          apply IHm with (j := xO j) in H0; destructAll.
          destruct o as [a|].
          * exists x, (x0 ++ ((M.prev j, a)::M.xelements r (xI j))).
            split; auto. now rewrite (app_assoc x x0), <- H0.
            cbn. now rewrite H1, <- app_assoc.
          * exists x, (x0 ++ M.xelements r (xI j)).
            split; auto. now rewrite (app_assoc x x0), <- H0.
            cbn. now rewrite H1, <- app_assoc.
        + rewrite M.gNode in H0. subst o.
          exists (M.xelements l (xO j)), (M.xelements r (xI j)).
          rewrite xelements_set_node_xH, !M.xelements_Node. split; auto.
    Qed.

  Theorem elements_set_none:
    forall (A: Type) v (m: M.t A) i ,
      M.get i m = None ->
      exists l1 l2, M.elements m = l1 ++ l2 /\ M.elements (M.set i v m) = l1 ++ (i,v)::l2.
  Proof.
    unfold M.elements.
    intros.
    apply xelements_set_none with (v:= v) (j := xH) (m := m) in H.
    simpl in H. apply H.
  Qed.

    Theorem xelements_set_some:
    forall (A: Type) v v' (m: M.t A) i j,
      M.get i m = Some v' ->
      exists l1 l2, M.xelements m j = l1 ++ (M.prev_append j i,v')::l2 /\ M.xelements (M.set i v m) j = l1 ++ (M.prev_append j i,v)::l2.
    Proof.
      intros A v v' m.
      induction m using M.tree_ind; intros.
      - rewrite M.gempty in H. congruence.
      - destruct i; simpl in *.
        + rewrite M.gNode in H0.
          rewrite xelements_set_node_xI, M.xelements_Node.
          apply IHm0 with (j:= xI j) in H0; do 3 (destruct H0).
          rewrite M.xelements_Node. cbn.
          rewrite H0.
          destruct o.
          * exists (M.xelements l (xO j) ++ ((M.prev j, a) :: x)), x0.
            split. cbn. now rewrite <- app_assoc.
            now rewrite <- app_assoc, H1.
          * exists ((M.xelements l (xO j)) ++ x), x0.
            split; auto. cbn.
            now rewrite <- app_assoc.
            now rewrite H1, <- app_assoc.
        + rewrite M.gNode in H0.
          rewrite xelements_set_node_xO, !M.xelements_Node.
          apply IHm with (j := xO j) in H0; destructAll.
          destruct o as [a|].
          * exists x, (x0 ++ ((M.prev j, a)::M.xelements r (xI j))).
            split; auto. cbn.
            change ((M.prev_append j (xO i), v') :: x0 ++ (M.prev j, a) :: M.xelements r (xI j))
              with (((M.prev_append j (xO i), v') :: nil) ++ x0 ++ (M.prev j, a) :: M.xelements r (xI j)).
            rewrite H0, !app_assoc. f_equal.
            now rewrite <- app_assoc.
            change ((M.prev_append j (xO i), v) :: x0 ++ (M.prev j, a) :: M.xelements r (xI j))
              with (((M.prev_append j (xO i), v) :: nil) ++ x0 ++ (M.prev j, a) :: M.xelements r (xI j)).
            rewrite H1, !app_assoc. cbn.
            rewrite <- app_assoc. simpl.
            now rewrite <- (app_assoc x _ x0).
          * exists x, (x0 ++ M.xelements r (xI j)).
            split; auto. simpl.
            now rewrite H0, <- app_assoc.
            now rewrite H1, <- app_assoc.
        + rewrite M.gNode in H0. subst o.
          exists (M.xelements l (xO j)), (M.xelements r (xI j)).
          rewrite xelements_set_node_xH, !M.xelements_Node. split; auto.
    Qed.

  Theorem elements_set_some:
    forall (A: Type) i v v' (m: M.t A),
      M.get i m = Some v'  ->
      exists l1 l2, M.elements m = l1 ++ (i, v') :: l2 /\ M.elements (M.set i v m) = l1 ++ (i,v)::l2.
  Proof.
    unfold M.elements. intros.
    eapply xelements_set_some with (j := xH) in H. simpl in H. apply H.
  Qed.


End DES.

Section EQMAP.

  Definition map_get_r: forall t, relation (M.t t) :=
    fun t => fun sub sub' => forall v, M.get v sub = M.get v sub'.

  Infix " <~m_get~> " := (map_get_r _) (at level 50).


  Theorem smg_refl: forall t, Reflexive (map_get_r t).
  Proof.
    intros; intro; intro; reflexivity.
Qed.


  Theorem smg_sym: forall t, Symmetric (map_get_r t).
  Proof.
    intro; intro; intros; intro; auto.
  Qed.


Theorem smg_trans: forall t, Transitive (map_get_r t).
Proof.
 intros t sub sub' sub''.  unfold map_get_r. intros. specialize (H v). specialize (H0 v). rewrite H. assumption.
Qed.


Instance map_get_r_equiv : forall t, Equivalence (map_get_r t).
Proof. intro. split;
[apply smg_refl |
apply smg_sym |
apply smg_trans].
Qed.




(* following two should be syntactically true *)
Theorem remove_empty: forall t x, map_get_r t (M.remove x (M.empty t)) (M.empty t).
Proof.
  unfold map_get_r; intros. now rewrite !M.gempty.
Qed.


Theorem remove_none: forall t v x, M.get x v = None -> map_get_r t (M.remove x v) v.
Proof.
  unfold map_get_r; intros.
 destruct (var_dec v0 x). subst. rewrite H. rewrite M.grs. reflexivity. rewrite M.gro. reflexivity. assumption.
Qed.


Theorem remove_set_1: forall t x v e, map_get_r t (M.remove x (M.set x e v)) (M.remove x v).
Proof.
 unfold map_get_r; intros.
 destruct (var_dec v0 x). subst. rewrite M.grs. rewrite M.grs. reflexivity.
                                 rewrite M.gro. rewrite M.gso. rewrite M.gro. reflexivity. assumption. assumption. assumption.
Qed.



Theorem remove_set_2: forall t x y v e, x <> y  -> map_get_r t (M.remove x (M.set y e v)) (M.set y e (M.remove x v)).
Proof.
  unfold map_get_r; intros.
  destruct (var_dec v0 x).
  - subst. rewrite M.grs. rewrite M.gso. rewrite M.grs. reflexivity. assumption.
  - rewrite M.gro. 2: assumption. destruct (var_dec v0 y).
    + subst. rewrite M.gss. rewrite M.gss. reflexivity.
    + rewrite M.gso. rewrite M.gso. rewrite M.gro. reflexivity. assumption. assumption. assumption.
Qed.




Theorem remove_remove: forall t x y sub, map_get_r t (M.remove x (M.remove y sub)) (M.remove y (M.remove x sub)).
Proof.
 unfold map_get_r; intros.
  destruct (var_dec v x); destruct (var_dec v y); subst.
  - subst. reflexivity.
  - rewrite M.grs. rewrite M.gro. rewrite M.grs. reflexivity. assumption.
  - rewrite M.gro. rewrite M.grs. rewrite M.grs. reflexivity. assumption.
  - rewrite M.gro. rewrite M.gro. rewrite M.gro. rewrite M.gro. reflexivity. assumption. assumption. assumption. assumption.
Qed.



Theorem set_set: forall t e e' x y sub, x <> y -> map_get_r t (M.set x e (M.set y e' sub)) (M.set y e' (M.set x e sub)).
Proof.
  unfold map_get_r; intros.
  destruct (var_dec v x); destruct (var_dec v y); try (subst x || subst y).
  - exfalso; auto.
  - rewrite M.gss. rewrite M.gso. rewrite M.gss. reflexivity. assumption.
  -  rewrite M.gso. rewrite M.gss. rewrite M.gss. reflexivity. assumption.
  - rewrite M.gso. rewrite M.gso. rewrite M.gso. rewrite M.gso. reflexivity. assumption. assumption. assumption. assumption.
Qed.




Theorem inv_set: forall t e sub sub' v,  map_get_r t (M.remove v sub) (M.remove v sub')  -> map_get_r t (M.set v e sub) (M.set v e sub').
Proof.
  unfold map_get_r; intros.
  specialize (H v0). destruct (var_dec v0 v).
  - subst. rewrite 2 M.gss. reflexivity.
    - rewrite 2 M.gso. rewrite 2 M.gro in H. assumption. assumption. assumption. assumption. assumption.
Qed.



Theorem set_remove: forall t x e sub,  map_get_r t (M.set x e (M.remove x sub)) (M.set x e sub).
Proof.
  unfold map_get_r; intros.
  destruct (var_dec v x).
  + subst. rewrite M.gss. rewrite M.gss. reflexivity.
  + rewrite M.gso. rewrite M.gro. rewrite M.gso. reflexivity. assumption. assumption. assumption.
Qed.



Theorem proper_remove: forall t v,  Proper (map_get_r t ==> map_get_r t) (M.remove v).
Proof.
  intros t v r. unfold map_get_r; intros. destruct (var_dec v0 v).
  - subst. rewrite 2 M.grs. reflexivity.
  - rewrite 2 M.gro. apply H. assumption. assumption.
Qed.



Theorem proper_set: forall t v e, Proper (map_get_r t ==> map_get_r t) (M.set v e).
Proof.
 intros t v e r. unfold map_get_r; intros. destruct (var_dec v0 v).
 - subst. rewrite 2 M.gss. reflexivity.
 - rewrite 2 M.gso. apply H. assumption. assumption.
Qed.





End EQMAP.

Section GETD.
  Definition getd {A:Type} (d:A) :=
  fun v sub => match M.get v sub with
               | None => d
               | Some e => e
               end.


  Theorem e_getd: forall A (d:A) v sub,
                  exists e, getd d v sub = e.
  Proof.
    unfold getd; intros; destruct (M.get v sub);
         [ exists a; reflexivity | exists d; reflexivity].
  Qed.

  Theorem getd_det: forall A v (a1 a2 d:A) sub,
                      getd d v sub  = a1 ->
                      getd d v sub = a2 ->
                      a1 = a2.
  Proof.
    unfold getd; intros; destruct (M.get v sub); subst; trivial.
  Qed.

  Theorem gdss: forall A (d:A) x c v,
         getd d x (M.set x v c) = v.
  Proof.
    intros. unfold getd. rewrite M.gss. reflexivity.
  Qed.

  Theorem gdso: forall A (d:A) x x' c v,
                  x <> x' -> getd d x (M.set x' v c) = getd d x c.
  Proof.
    unfold getd. intros. rewrite M.gso. reflexivity. assumption.
  Qed.

  Theorem gdempty: forall A (d:A) x,
             getd d x (M.empty A) = d.
  Proof.
    unfold getd. symmetry. rewrite M.gempty. reflexivity.
  Qed.


End GETD.

Section EQDMAP.


  Definition map_getd_r: forall t d, relation (M.t t) :=
    fun t d => fun sub sub' => forall v, getd d v sub = getd d v sub'.

  Theorem smgd_refl: forall t d, Reflexive (map_getd_r t d).
  Proof.
    do 4 intro; reflexivity.
  Qed.


  Theorem smgd_sym: forall t d, Symmetric (map_getd_r t d).
  Proof.
    do 6 intro; auto.
  Qed.


  Theorem smgd_trans: forall t d, Transitive (map_getd_r t d).
  Proof.
    intros t d sub sub' sub'';  unfold map_get_r; intros; intro;
    specialize (H v); specialize (H0 v); rewrite H; assumption.
  Qed.


  Instance map_getd_r_equiv : forall t d, Equivalence (map_getd_r t d).
  Proof. intro. split;
           [apply smgd_refl |
            apply smgd_sym |
            apply smgd_trans].
  Qed.


  Theorem remove_empty_d: forall t d x, map_getd_r t d (M.remove x (M.empty t)) (M.empty t).
  Proof.
    unfold map_getd_r; intros. unfold getd. rewrite M.gempty. destruct (var_dec v x). subst.
    rewrite M.gempty. reflexivity. rewrite M.gempty. reflexivity.
  Qed.

  Theorem remove_none_d: forall t d v x, M.get x v = None -> map_getd_r t d (M.remove x v) v.
    unfold map_getd_r; intros. unfold getd.
    destruct (var_dec v0 x). subst. rewrite H. rewrite M.grs. reflexivity. rewrite M.gro. reflexivity. assumption.
  Qed.

  Theorem remove_set_1_d: forall t d x v e, map_getd_r t d (M.remove x (M.set x e v)) (M.remove x v).
  Proof.
    unfold map_getd_r; unfold getd; intros.
    destruct (var_dec v0 x). subst. rewrite M.grs. rewrite M.grs. reflexivity.
    rewrite M.gro. rewrite M.gso. rewrite M.gro. reflexivity. assumption. assumption. assumption.
  Qed.

  Theorem remove_set_2_d: forall t d x y v e, x <> y  -> map_getd_r t d (M.remove x (M.set y e v)) (M.set y e (M.remove x v)).
  Proof.
    unfold map_getd_r; intros. unfold getd.
    destruct (var_dec v0 x).
    - subst. rewrite M.grs. rewrite M.gso. rewrite M.grs. reflexivity. assumption.
    - rewrite M.gro. 2: assumption. destruct (var_dec v0 y).
      + subst. rewrite M.gss. rewrite M.gss. reflexivity.
      + rewrite M.gso. rewrite M.gso. rewrite M.gro. reflexivity. assumption. assumption. assumption.
  Qed.

  Theorem remove_remove_d: forall t d x y sub, map_getd_r t d (M.remove x (M.remove y sub)) (M.remove y (M.remove x sub)).
  Proof.
    unfold map_getd_r; intros. unfold getd.
    destruct (var_dec v x); destruct (var_dec v y); subst.
    - subst. reflexivity.
    - rewrite M.grs. rewrite M.gro. rewrite M.grs. reflexivity. assumption.
    - rewrite M.gro. rewrite M.grs. rewrite M.grs. reflexivity. assumption.
    - rewrite M.gro. rewrite M.gro. rewrite M.gro. rewrite M.gro. reflexivity. assumption. assumption. assumption. assumption.
  Qed.

  Theorem set_set_d: forall t d e e' x y sub, x <> y -> map_getd_r t d (M.set x e (M.set y e' sub)) (M.set y e' (M.set x e sub)).
  Proof.
    unfold map_getd_r; intros. unfold getd.
    destruct (var_dec v x); destruct (var_dec v y); try (subst x || subst y).
    - exfalso; auto.
    - rewrite M.gss. rewrite M.gso. rewrite M.gss. reflexivity. assumption.
    -  rewrite M.gso. rewrite M.gss. rewrite M.gss. reflexivity. assumption.
    - rewrite M.gso. rewrite M.gso. rewrite M.gso. rewrite M.gso. reflexivity. assumption. assumption. assumption. assumption.
  Qed.

  Theorem inv_set_d: forall t d e sub sub' v,  map_getd_r t d (M.remove v sub) (M.remove v sub')  -> map_getd_r t d (M.set v e sub) (M.set v e sub').
  Proof.
    unfold map_getd_r; intros. unfold getd.
    specialize (H v0). destruct (var_dec v0 v).
    - subst. rewrite 2 M.gss. reflexivity.
    - rewrite 2 M.gso. unfold getd in H. rewrite 2 M.gro in H. assumption. assumption. assumption. assumption. assumption.
  Qed.

  Theorem set_remove_d: forall t d x e sub,  map_getd_r t d (M.set x e (M.remove x sub)) (M.set x e sub).
  Proof.
    unfold map_getd_r; unfold getd; intros.
    destruct (var_dec v x).
    + subst. rewrite M.gss. rewrite M.gss. reflexivity.
    + rewrite M.gso. rewrite M.gro. rewrite M.gso. reflexivity. assumption. assumption. assumption.
  Qed.

  Theorem proper_remove_d: forall t d v,  Proper (map_getd_r t d ==> map_getd_r t d) (M.remove v).
  Proof.
    intros t d v r. unfold map_getd_r; unfold getd. intros. destruct (var_dec v0 v).
    - subst. rewrite 2 M.grs. reflexivity.
    - rewrite 2 M.gro. apply H. assumption. assumption.
  Qed.


  Theorem proper_set_d: forall t d v e, Proper (map_getd_r t d ==> map_getd_r t d) (M.set v e).
  Proof.
    intros t d v e r. unfold map_getd_r; unfold getd. intros. destruct (var_dec v0 v).
    - subst. rewrite 2 M.gss. reflexivity.
    - rewrite 2 M.gso. apply H. assumption. assumption.
  Qed.


End EQDMAP.

Theorem gr_some : forall A x y s (a:A), M.get x (M.remove y s) = Some a -> M.get x s = Some a.
Proof.
  intros. destruct (var_dec x y).
  subst; rewrite M.grs in H; inversion H.
  rewrite M.gro in H; assumption.
Qed.

Theorem gr_none: forall A x y (s:M.t A), M.get x s = None -> M.get x (M.remove y s) = None.
Proof.
  intros. destruct (var_dec x y).
  subst; apply M.grs.
  rewrite M.gro; assumption.
Qed.
