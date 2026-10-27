(* Peano numbers: boxed one-field [S] cells ending in the unboxed [O]. *)
From CertiRocq.Plugin Require Import CertiRocq.
From CertiRocq.LLVMTests Require Import SExp.

Definition prog : nat := 2 + 3.
CertiRocq Compile LLVM prog.
