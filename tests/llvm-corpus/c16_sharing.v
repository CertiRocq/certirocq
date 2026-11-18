(* Sharing: [sh 60] is a DAG with 60 nodes that represents a complete binary
   tree with 2^60 leaves ([Node t t]).  It stays live across ~50
   collections (triggered by [churn]); a collector that copied it as a tree
   would need 2^60 words.  Then both spines are walked, and a small
   unshared copy is counted.
   Targets: roots_ok on DAGs (and the checker's memoised deep comparison);
   promotion of shared structure.
   Expected (Rocq): (D4, D4, D2, D0)
   EXPECTED: (C0 (C0 (C0 4 4) 2) 0) *)
From Stdlib Require Import PArith.
Inductive d7 := D0 | D1 | D2 | D3 | D4 | D5 | D6.
Definition s7 (d : d7) : d7 :=
  match d with D0 => D1 | D1 => D2 | D2 => D3 | D3 => D4 | D4 => D5 | D5 => D6 | D6 => D0 end.
Inductive tree := Leaf | Node (l r : tree).
Fixpoint sh (n : nat) : tree := match n with O => Leaf | S m => let t := sh m in Node t t end.
Fixpoint ldepth (t : tree) (acc : d7) : d7 := match t with Leaf => acc | Node l _ => ldepth l (s7 acc) end.
Fixpoint rdepth (t : tree) (acc : d7) : d7 := match t with Leaf => acc | Node _ r => rdepth r (s7 acc) end.
Fixpoint size (t : tree) (acc : d7) : d7 := match t with Leaf => s7 acc | Node l r => size r (size l acc) end.
Fixpoint churn (n : list unit) (acc : list unit) : d7 :=
  match n with nil => D0 | cons _ m => churn m (cons tt (cons tt acc)) end.
Definition prog : d7 * d7 * d7 * d7 :=
  let t := sh 60 in
  let c := churn (Pos.iter (cons tt) nil 500000) nil in
  (ldepth t c, rdepth t D0, size (sh 16) D0, c).

Example prog_expected : prog = (D4, D4, D2, D0) := ltac:(vm_compute; reflexivity).
