(* A mutually recursive pair. *)
From CertiRocq.Plugin Require Import CertiRocq.
From CertiRocq.LLVMTests Require Import SExp.
From Stdlib Require Import List.
Import ListNotations.

Fixpoint even (n : nat) : bool := match n with O => true | S n => odd n end
with odd (n : nat) : bool := match n with O => false | S n => even n end.

Definition prog : list bool * bool := (map even [0; 1; 2; 7; 10], odd 1001).
CertiRocq Compile LLVM prog.
