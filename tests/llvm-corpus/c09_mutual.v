(* Mutual recursion: (1) a mutually inductive tree/forest with mutually
   recursive size/sum functions (non-tail, with GC pressure: about
   10^5 nodes); (2) even/odd on a 100000-element unary counter (mutual tail
   calls: ~10^5 machine-stack frames, run with `ulimit -s unlimited`).
   After closure conversion the mutual functions are top-level functions
   that call each other directly.
   Targets: Eapp/Eletapp between mutually recursive top-level functions,
   shadow_stack across alternating callers, roots_ok.
   Expected (Rocq): (D2, D3, false, true)
   EXPECTED: (C0 (C0 (C0 2 3) 0) 1) *)
From Stdlib Require Import PArith.
Inductive d7 := D0 | D1 | D2 | D3 | D4 | D5 | D6.
Definition s7 (d : d7) : d7 :=
  match d with D0 => D1 | D1 => D2 | D2 => D3 | D3 => D4 | D4 => D5 | D5 => D6 | D6 => D0 end.

Inductive tree := Node (x : d7) (f : forest)
with forest := FNil | FCons (t : tree) (f : forest).

(* building uses a nested [fix] (the guard checker rejects a mutual one) *)
Fixpoint mk_tree (n : nat) (x : d7) : tree :=
  match n with
  | O => Node x FNil
  | S m =>
      Node x ((fix mk_forest (w : nat) (y : d7) : forest :=
                 match w with O => FNil | S w' => FCons (mk_tree m y) (mk_forest w' (s7 y)) end)
                3 (s7 x))
  end.

Fixpoint size_t (t : tree) (acc : d7) : d7 :=
  match t with Node x f => size_f f (s7 acc) end
with size_f (f : forest) (acc : d7) : d7 :=
  match f with FNil => acc | FCons t f' => size_f f' (size_t t acc) end.

Fixpoint sum_t (t : tree) (acc : d7) : d7 :=
  match t with Node D0 f => sum_f f acc | Node _ f => sum_f f (s7 acc) end
with sum_f (f : forest) (acc : d7) : d7 :=
  match f with FNil => acc | FCons t f' => sum_f f' (sum_t t acc) end.

Fixpoint even (l : list unit) : bool := match l with nil => true | cons _ l' => odd l' end
with odd (l : list unit) : bool := match l with nil => false | cons _ l' => even l' end.

Definition prog : d7 * d7 * bool * bool :=
  let t := mk_tree 10 D0 in   (* (3^11 - 1)/2 = 88573 nodes *)
  let n := Pos.iter (cons tt) nil 100001 in
  (size_t t D0, sum_t t D0, even n, odd n).

Example prog_expected : prog = (D2, D3, false, true) := ltac:(vm_compute; reflexivity).
