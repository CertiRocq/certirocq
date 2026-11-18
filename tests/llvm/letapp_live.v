(* A let-bound non-tail call whose live variables must survive the call
   (spill/reload on the shadow stack), with the callee allocating enough to
   collect while the caller's boxed values are only reachable through its
   root frame. *)
From CertiRocq.Plugin Require Import CertiRocq.
From CertiRocq.LLVMTests Require Import SExp.
From Stdlib Require Import List NArith.
Import ListNotations.

(* Allocates ~3*n words of garbage, then returns a small value. *)
Fixpoint churn (n : nat) (acc : list nat) : nat :=
  match n with O => Nat.modulo (length acc) 5 | S n => churn n (n :: acc) end.

Definition step (a b : list nat) (k : nat) : list nat * list nat * nat :=
  let x := churn (k * 50000) nil in   (* non-tail call; a, b live *)
  let y := churn (k * 30000) a in     (* non-tail call; a, b, x live *)
  (b ++ a, x :: a, x + y).

Definition prog : list nat * list nat * nat := step [1; 2; 3] [4; 5] 2.
CertiRocq Compile LLVM prog.
