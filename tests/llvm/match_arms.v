(* A [match] with several arms, mixing unboxed (nullary) and boxed
   constructors, on several scrutinees. *)
From CertiRocq.Plugin Require Import CertiRocq.
From CertiRocq.LLVMTests Require Import SExp.
From Stdlib Require Import List.
Import ListNotations.

Inductive shape :=
| Dot                          (* unboxed 0 *)
| Circle (r : nat)             (* boxed 0 *)
| Nothing                      (* unboxed 1 *)
| Rect (w h : nat)             (* boxed 1 *)
| Tri (a b c : nat)            (* boxed 2 *)
| Empty.                       (* unboxed 2 *)

Definition classify (s : shape) : nat :=
  match s with
  | Dot => 1
  | Circle r => 10 + r
  | Nothing => 2
  | Rect w h => w + h
  | Tri a b c => a + b + c + 100
  | Empty => 3
  end.

Definition prog : list nat :=
  map classify [Dot; Circle 4; Nothing; Rect 2 3; Tri 1 1 1; Empty; Rect 0 0].
CertiRocq Compile LLVM prog.
