(* GC pressure with shallow recursion: a complete binary tree with 2^20
   (unboxed) leaves and 2^20 - 1 boxed nodes (3 words each: about 3.1M words
   = 24 MiB, ~48 nursery overflows), built and folded with recursion depth 20.  While a subtree is
   being built, its finished left sibling is a live root on the shadow stack
   (Eletapp around the recursive call), so every collection runs with ~20
   frames and live data in every generation.
   Targets: the collector clause of runtime_correct (roots_ok, room,
   shadow_stack preserved), promotion through several generations.
   Expected (Rocq): D4
   EXPECTED: 4 *)
Inductive d7 := D0 | D1 | D2 | D3 | D4 | D5 | D6.
Definition s7 (d : d7) : d7 :=
  match d with D0 => D1 | D1 => D2 | D2 => D3 | D3 => D4 | D4 => D5 | D5 => D6 | D6 => D0 end.

Inductive tree := Leaf | Node (l r : tree).

Fixpoint build (n : nat) : tree :=
  match n with
  | O => Node Leaf Leaf
  | S m => let l := build m in let r := build m in Node l r
  end.
(* Note: [build m] is called twice on purpose (no sharing): the tree is a
   real tree of 2^20 nodes, not a DAG of 20. *)

Fixpoint count (t : tree) (acc : d7) : d7 :=
  match t with
  | Leaf => s7 acc
  | Node l r => count r (count l acc)
  end.

(* [build n] has 2^(n+1) leaves, so [build 19] has 2^20. *)
Definition prog : d7 := count (build 19) D0.

Example prog_expected : prog = D4 := ltac:(vm_compute; reflexivity).
