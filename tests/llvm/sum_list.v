(* A non-tail-recursive function: the sum of a list. *)
From CertiRocq.Plugin Require Import CertiRocq.
From CertiRocq.LLVMTests Require Import SExp.
From Stdlib Require Import List.

Fixpoint sum (l : list nat) : nat :=
  match l with
  | nil => 0
  | x :: l => x + sum l
  end.

Definition prog : nat := sum (seq 1 6).
CertiRocq Compile LLVM prog.
