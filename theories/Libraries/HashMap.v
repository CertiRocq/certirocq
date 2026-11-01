From Stdlib Require Import List.
From Stdlib Require Import ZArith.
From Stdlib Require Import Znumtheory.
From Stdlib Require Import Bool.
From Stdlib Require Import Nnat.
From Stdlib Require Import MSets.

(* A "hashmap" is a reversible mapping from
   [positive] to any totally ordered type;
   or, alternately, a hash-consing from the ordered type to [positive].
 *)

Module Type HASHMAP.
  Declare Module Domain : UsualOrderedType.
  Definition index : Type := positive.
  Parameter t : Type.
  Parameter empty : t.
  Parameter get: forall (i: index) (m: t), option Domain.t.
  Parameter hash: forall (v: Domain.t) (m: t), (index * t).
  Axiom gempty: forall i, get i empty = None.
  Axiom get_hash: forall i x m, get i m = Some x <-> hash x m = (i,m).
  Axiom get_hash_other:
    forall i m x i' m',
      get i m = Some x -> hash x m = (i',m') -> get i m' = Some x.
  Parameter elements: t -> list (index * Domain.t).
  Parameter elements_spec: forall i m v,
                              get i m = Some v <->
                              nth_error (elements m) (pred (Pos.to_nat i)) = Some (i,v).
End HASHMAP.

Module MakeHashMap (D: UsualOrderedType) <:
  HASHMAP with Module Domain := D.
  (* This is an inefficient reference implementation.
     The efficient implementation of HashMap should wait until
     module MMaps is implemented. *)
  Module Domain := D.
  Definition index := positive.
  Definition norepet (elems: list Domain.t) :=
    forall i j v,
      nth_error elems i = Some v ->
      nth_error elems j = Some v ->
      i=j.
  Record t' := Make { elems: list Domain.t; OK: norepet elems}.
  Definition t := t'.
  Lemma norepet_empty: norepet nil.
  Proof. hnf; intros.
         exfalso; clear - H. induction i; inversion H.
  Qed.
  Definition empty := Make _ norepet_empty.
  Definition get (i: index) (m: t) : option Domain.t :=
    nth_error m.(elems) (pred (Pos.to_nat i)).
  Fixpoint find (i: index) (v: Domain.t) (elems: list Domain.t) :
    sum index index :=
    match elems with
      | w::elems' => if Domain.eq_dec v w
                    then inl i
                    else find (Pos.succ i) v elems'
      | nil => inr i
    end.

  Lemma norepet_hash:
    forall i v m, find 1%positive v m = inr i ->
             norepet (m ++ v :: nil).
  Proof.
  Admitted.
  Definition hash (v: Domain.t) (m: t) : index * t :=
    match find 1%positive v (elems m) as s0
          return (find 1%positive v (elems m) = s0 -> index * t) with
      | inl i => fun _ : find 1%positive v (elems m) = inl i => (i, m)
      | inr i =>
        fun H0 : find 1%positive v (elems m) = inr i =>
          (i,
           {| elems := elems m ++ v :: nil; OK := norepet_hash i v (elems m) H0 |})
    end eq_refl.
  Lemma gempty: forall i, get i empty = None.
  Proof. intros. unfold get, empty;  simpl.
         induction (pred (Pos.to_nat i)); simpl; auto.
  Qed.

  Lemma get_hash: forall i x m, get i m = Some x <-> hash x m = (i,m).
  Proof.
  Admitted.

  Lemma get_hash_other:
    forall i m x i' m',
      get i m = Some x -> hash x m = (i',m') -> get i m' = Some x.
  Admitted.

  Fixpoint elements' (i: index) (el: list Domain.t) : list (index * Domain.t) :=
    match el with
      | nil => nil
      | v::el' => (i,v) :: elements' (Pos.succ i) el'
    end.

  Definition elements (m: t) : list (index * Domain.t) :=
    elements' 1%positive (elems m).
  Lemma elements_spec: forall i m v,
                         get i m = Some v <->
                         nth_error (elements m) (pred (Pos.to_nat i)) = Some (i,v).
  Admitted.
End MakeHashMap.
