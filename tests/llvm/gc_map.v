(* Collections in the middle of deep NON-tail recursion: [map] over a list of
   10^5 elements keeps 10^5 caller frames (and their shadow-stack frames) live
   while the nursery fills up; the result is then folded into a small value.
   Exercises root registration across many frames. *)
From CertiRocq.Plugin Require Import CertiRocq.
From CertiRocq.LLVMTests Require Import SExp.
From Stdlib Require Import List NArith.

Definition next (acc : list N) : N :=
  match acc with nil => 0%N | y :: _ => if N.eqb y 6 then 0%N else N.succ y end.

Fixpoint build (n : nat) (acc : list N) : list N :=
  match n with O => acc | S n => build n (next acc :: acc) end.

Fixpoint mymap (f : N -> N) (l : list N) : list N :=
  match l with nil => nil | x :: l => f x :: mymap f l end.

Fixpoint total (l : list N) (acc : N) : N :=
  match l with nil => acc | x :: l => total l (N.add x acc) end.

Definition prog : N * list N :=
  let l := mymap (fun x => N.mul x 3) (build 100000 nil) in
  (total l 0%N, firstn 8 l).
CertiRocq Compile LLVM prog.
