(* A nullary constructor: the result is an unboxed word. *)
From CertiRocq.Plugin Require Import CertiRocq.
From CertiRocq.LLVMTests Require Import SExp.

Inductive color := Red | Green | Blue.
#[export] Instance SExp_color : SExp color :=
  fun c => match c with Red => unboxed 0 | Green => unboxed 1 | Blue => unboxed 2 end.

Definition prog : color := Blue.
CertiRocq Compile LLVM prog.
