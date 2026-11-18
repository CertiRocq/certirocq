(* Eletapp chains: (1) 30 non-tail calls in a row, each result immediately
   dead after it is passed to the next call (root frames of size ~1);
   (2) 30 calls whose results all stay live until the end (the k-th call
   site registers k-1 earlier results: root frames of growing size, and
   every result produced before a collection must be forwarded).  Each call
   allocates a 2000-element list (6000 words), so collections happen at
   many different call sites of both chains.
   Targets: Eletapp safepoints (spill/reload, frame push/pop restoring the
   previous fp), roots_ok, shadow_stack.
   Expected (Rocq): (D1, D1, D5, D0)
   EXPECTED: (C0 (C0 (C0 1 1) 5) 0) *)
From Stdlib Require Import List PArith.
Import ListNotations.
Inductive d7 := D0 | D1 | D2 | D3 | D4 | D5 | D6.
Definition s7 (d : d7) : d7 :=
  match d with D0 => D1 | D1 => D2 | D2 => D3 | D3 => D4 | D4 => D5 | D5 => D6 | D6 => D0 end.
Definition add7 (x y : d7) : d7 :=
  match x with
  | D0 => y | D1 => s7 y | D2 => s7 (s7 y) | D3 => s7 (s7 (s7 y))
  | D4 => s7 (s7 (s7 (s7 y))) | D5 => s7 (s7 (s7 (s7 (s7 y))))
  | D6 => s7 (s7 (s7 (s7 (s7 (s7 y))))) end.

Fixpoint sum (l : list d7) (acc : d7) : d7 :=
  match l with [] => acc | y :: l' => sum l' (add7 y acc) end.

(* recursive, so not inlined: allocates 2000 cells, returns a 1-cell summary *)
Fixpoint g (n : nat) (x : d7) : list d7 :=
  match n with
  | O => let l := Pos.iter (fun l => match l with [] => [x] | y :: _ => s7 y :: l end) [] 2000 in
         [sum l x]
  | S m => g m x
  end.

Definition hd7 (l : list d7) : d7 := match l with [] => D0 | x :: _ => x end.

Definition chain_dead (x : d7) : d7 :=
  let a1 := g 0 x in let a2 := g 0 (hd7 a1) in let a3 := g 0 (hd7 a2) in
  let a4 := g 0 (hd7 a3) in let a5 := g 0 (hd7 a4) in let a6 := g 0 (hd7 a5) in
  let a7 := g 0 (hd7 a6) in let a8 := g 0 (hd7 a7) in let a9 := g 0 (hd7 a8) in
  let a10 := g 0 (hd7 a9) in let a11 := g 0 (hd7 a10) in let a12 := g 0 (hd7 a11) in
  let a13 := g 0 (hd7 a12) in let a14 := g 0 (hd7 a13) in let a15 := g 0 (hd7 a14) in
  let a16 := g 0 (hd7 a15) in let a17 := g 0 (hd7 a16) in let a18 := g 0 (hd7 a17) in
  let a19 := g 0 (hd7 a18) in let a20 := g 0 (hd7 a19) in let a21 := g 0 (hd7 a20) in
  let a22 := g 0 (hd7 a21) in let a23 := g 0 (hd7 a22) in let a24 := g 0 (hd7 a23) in
  let a25 := g 0 (hd7 a24) in let a26 := g 0 (hd7 a25) in let a27 := g 0 (hd7 a26) in
  let a28 := g 0 (hd7 a27) in let a29 := g 0 (hd7 a28) in let a30 := g 0 (hd7 a29) in
  hd7 a30.

Definition chain_live (x : d7) : d7 :=
  let a1 := g 0 x in let a2 := g 0 (s7 x) in let a3 := g 0 (hd7 a1) in
  let a4 := g 0 (hd7 a2) in let a5 := g 0 (hd7 a3) in let a6 := g 0 (hd7 a4) in
  let a7 := g 0 (hd7 a5) in let a8 := g 0 (hd7 a6) in let a9 := g 0 (hd7 a7) in
  let a10 := g 0 (hd7 a8) in let a11 := g 0 (hd7 a9) in let a12 := g 0 (hd7 a10) in
  let a13 := g 0 (hd7 a11) in let a14 := g 0 (hd7 a12) in let a15 := g 0 (hd7 a13) in
  let a16 := g 0 (hd7 a14) in let a17 := g 0 (hd7 a15) in let a18 := g 0 (hd7 a16) in
  let a19 := g 0 (hd7 a17) in let a20 := g 0 (hd7 a18) in let a21 := g 0 (hd7 a19) in
  let a22 := g 0 (hd7 a20) in let a23 := g 0 (hd7 a21) in let a24 := g 0 (hd7 a22) in
  let a25 := g 0 (hd7 a23) in let a26 := g 0 (hd7 a24) in let a27 := g 0 (hd7 a25) in
  let a28 := g 0 (hd7 a26) in let a29 := g 0 (hd7 a27) in let a30 := g 0 (hd7 a28) in
  sum (a1 ++ a2 ++ a3 ++ a4 ++ a5 ++ a6 ++ a7 ++ a8 ++ a9 ++ a10 ++ a11 ++ a12 ++ a13
       ++ a14 ++ a15 ++ a16 ++ a17 ++ a18 ++ a19 ++ a20 ++ a21 ++ a22 ++ a23 ++ a24
       ++ a25 ++ a26 ++ a27 ++ a28 ++ a29 ++ a30) D0.

Definition prog : d7 * d7 * d7 * d7 :=
  (chain_dead D1, chain_live D2, chain_dead D5, chain_live D6).

Example prog_expected : prog = (D1, D1, D5, D0) := ltac:(vm_compute; reflexivity).
