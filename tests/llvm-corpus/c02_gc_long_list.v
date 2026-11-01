(* GC pressure with a long-lived list of 10^6 cells (3M words = 24 MiB, ~46
   nursery overflows while it is built; all of it survives and is promoted).
   The list is built by [Pos.iter] (recursion depth log2(10^6) = 20; the
   iterated function [flip_cons] is passed as a closure) and then consumed by a tail-recursive fold.
   NOTE: tail calls ([Eapp]) are ordinary LLVM calls in the emitted code, so
   the fold uses ~10^6 machine-stack frames: run with `ulimit -s unlimited`.
   Targets: collector clause (roots_ok over a large old generation; room);
   closures (a function passed as an argument).
   Expected (Rocq): (D4, true)
   EXPECTED: (C0 4 1) *)
From Stdlib Require Import PArith.
Inductive d7 := D0 | D1 | D2 | D3 | D4 | D5 | D6.
Definition s7 (d : d7) : d7 :=
  match d with D0 => D1 | D1 => D2 | D2 => D3 | D3 => D4 | D4 => D5 | D5 => D6 | D6 => D0 end.

Definition flip_cons (l : list bool) : list bool :=
  match l with
  | nil => cons true nil
  | cons b _ => cons (negb b) l
  end.

Definition mk (n : positive) : list bool := Pos.iter flip_cons nil n.

Fixpoint fold (l : list bool) (acc : d7) (last : bool) : d7 * bool :=
  match l with
  | nil => (acc, last)
  | cons b l' => fold l' (if b then s7 acc else acc) b
  end.

Definition prog : d7 * bool := fold (mk 1000000) D0 true.

Example prog_expected : prog = (D4, true) := ltac:(vm_compute; reflexivity).
