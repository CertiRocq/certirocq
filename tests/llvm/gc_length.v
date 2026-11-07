(* Enough allocation to trigger collections: build a list of 10^6 units
   (3 words per cell; the nursery is 2^16 words) and take its length, as an
   [N] (so the result is small).  Builder and length are tail recursive. *)
From CertiRocq.Plugin Require Import CertiRocq.
From CertiRocq.LLVMTests Require Import SExp.
From Stdlib Require Import List NArith.

Fixpoint build (n : nat) (acc : list unit) : list unit :=
  match n with O => acc | S n => build n (tt :: acc) end.

Fixpoint len (l : list unit) (acc : N) : N :=
  match l with nil => acc | _ :: l => len l (N.succ acc) end.

Definition million : nat := 1000 * 1000.

Definition prog : N := len (build million nil) 0%N.
CertiRocq Compile LLVM prog.
