(* Deep non-tail recursion: 50000 nested activations, each keeping four
   variables (two boxed, two unboxed) live across the recursive call
   ([Eletapp]) and allocating after it returns.  The shadow stack is 50000
   frames deep when the collections triggered near the bottom run, so the
   collector walks a long [prev] chain and forwards ~4 roots per frame.
   NOTE: needs ~50000 machine-stack frames (`ulimit -s unlimited` is safest).
   Targets: shadow_stack (long chains, frame structs untouched), roots_ok
   (unboxed roots unchanged, boxed roots forwarded), spill/reload around a
   non-tail call (Eletapp), room.
   Expected (Rocq): (D5, D5)
   EXPECTED: (C0 5 5) *)
From Stdlib Require Import PArith List.
Import ListNotations.
Inductive d7 := D0 | D1 | D2 | D3 | D4 | D5 | D6.
Definition s7 (d : d7) : d7 :=
  match d with D0 => D1 | D1 => D2 | D2 => D3 | D3 => D4 | D4 => D5 | D5 => D6 | D6 => D0 end.

(* A unary counter built in log depth. *)
Definition n_of (p : positive) : list unit := Pos.iter (cons tt) nil p.

Fixpoint deep (n : list unit) (a : d7) (b : option d7) (c : bool) (acc : list d7)
  : list d7 * d7 :=
  match n with
  | nil => (acc, a)
  | cons _ m =>
      (* [a], [b], [c], [m] are live across the call; the call allocates *)
      let '(r, z) := deep m (s7 a) (Some a) (negb c) (a :: acc) in
      let b' := match b with Some x => x | None => D0 end in
      ((if c then b' :: r else a :: r), (if c then s7 z else z))
  end.

Fixpoint sum (l : list d7) (acc : d7) : d7 :=
  match l with
  | nil => acc
  | cons x l' =>
      let acc' := match x with
                  | D0 => acc | D1 => s7 acc | D2 => s7 (s7 acc)
                  | D3 => s7 (s7 (s7 acc)) | D4 => s7 (s7 (s7 (s7 acc)))
                  | D5 => s7 (s7 (s7 (s7 (s7 acc))))
                  | D6 => s7 (s7 (s7 (s7 (s7 (s7 acc))))) end in
      sum l' acc'
  end.

Definition prog : d7 * d7 :=
  let '(l, z) := deep (n_of 50000) D3 None true nil in (sum l D0, z).

Example prog_expected : prog = (D5, D5) := ltac:(vm_compute; reflexivity).
