From Stdlib Require Import List Arith Extraction Lia.
Notation "( x ; p )" := (exist _ x p).
Example nth {A} (l : list A) : {n : nat | n < length l} -> A.
Proof.
  intros n.
  induction l as [|l' Hl'].
  - destruct n as [n Hn].
    simpl in Hn.
    apply False_rect.
    inversion Hn.
    Set Printing Notations.
  - destruct n as [n Hn].
    destruct n as [|n'].
    + (* 0 *)
      exact l'.
    + (* S n' *)
      apply IHHl'.
      exists n'.
      simpl in Hn.
      apply Nat.succ_lt_mono. apply Hn.
Defined.

Print nth.

Extraction nth.

From CertiRocq.Plugin Require Import CertiRocq.
Set CertiRocq Build Directory "_build".

Import ListNotations.
Definition l : list nat := map (fun x => x * x) (repeat 3 4000).

Lemma nth_l : 3000 < length l.
Proof. unfold l. rewrite length_map. rewrite repeat_length. Admitted.

Definition test : nat := (nth l (3000; nth_l)).
(* Time Eval vm_compute in test. *)
(* 30 seconds, includes cost of building the intermediate n < length proofs  *)
(* Stack overflowing when replacing 4000 with 45000 for example? *)
(* CertiRocq Eval -debug -time test. *)
Definition largenat := 45000.
(* Stack overflowing? *)

Definition llength := length l.
CertiRocq Eval -debug -time llength.

Time Eval vm_compute in llength.
Time Eval native_compute in llength.
