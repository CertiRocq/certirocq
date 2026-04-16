From Coq Require Import Streams StreamMemo.
Require Import ZArith.
Open Scope Z_scope.

Fixpoint tfact (n: nat) :=
  match n with
   | O => 1
   | S n1 => Z.of_nat n * tfact n1
  end.

Definition lfact_list :=
  dimemo_list _ tfact (fun n z => (Z.of_nat (S  n) * z)).

Definition lfact n := dmemo_get _ tfact n lfact_list.

Theorem lfact_correct n: lfact n = tfact n.
Proof.
  unfold lfact, lfact_list.
  rewrite dimemo_get_correct; auto.
Qed.

Definition lazy_factorial := lfact 3.

Eval vm_compute in lazy_factorial.

CoFixpoint from (x : nat) : Stream nat := Cons x (from (S (S x))).

Definition get_from := Str_nth 10 (from 0).
