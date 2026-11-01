(* A list of 10 nats. *)
From CertiRocq.Plugin Require Import CertiRocq.
From CertiRocq.LLVMTests Require Import SExp.
From Stdlib Require Import List.

Definition prog : list nat := seq 0 10.
CertiRocq Compile LLVM prog.
