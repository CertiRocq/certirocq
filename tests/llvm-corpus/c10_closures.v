(* Closures and partial application.  After closure conversion every
   function value is a closure record (code pointer + environment) built
   with Econstr, and calls through it project the code pointer: so roots
   and heap fields hold CODE POINTERS (not heap objects), which the
   collector must leave untouched.  This program builds a chain of 20000
   nested closures with continuation-passing [fold_right], partially
   applies curried functions, stores closures in a list across
   collections, and composes them.
   Targets: Repr_fun / code pointers in roots and fields (the checker's
   "external pointer unchanged" check), closure environments surviving GC,
   Eletapp through unknown functions.
   Expected (Rocq): (D3, D4, D5, D1)
   EXPECTED: (C0 (C0 (C0 3 4) 5) 1) *)
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

Definition mkl (n : positive) (x : d7) : list d7 :=
  Pos.iter (fun l => match l with [] => [x] | y :: _ => s7 y :: l end) [] n.

(* CPS fold: builds 20000 nested closures [fun acc => k (add7 x acc)] *)
Definition cps_sum (l : list d7) : d7 :=
  fold_right (fun x (k : d7 -> d7) => fun acc => k (add7 x acc)) (fun acc => acc) l D0.

(* a list of partially applied functions, kept live across allocation *)
Definition adders (l : list d7) : list (d7 -> d7) := map add7 l.

Fixpoint apply_all (fs : list (d7 -> d7)) (x : d7) : d7 :=
  match fs with [] => x | f :: fs' => apply_all fs' (f x) end.

Fixpoint compose_all (fs : list (d7 -> d7)) : d7 -> d7 :=
  match fs with [] => fun x => x | f :: fs' => let g := compose_all fs' in fun x => g (f x) end.

Definition twice {A} (f : A -> A) : A -> A := fun x => f (f x).

Definition prog : d7 * d7 * d7 * d7 :=
  let l := mkl 20000 D3 in
  let fs := adders l in                         (* 20000 closures *)
  let a := cps_sum l in                         (* allocates 20000 more *)
  let b := apply_all fs D1 in
  let c := compose_all fs D2 in                 (* 20000 composed closures *)
  let d := twice (twice (twice (add7 D1))) D0 in
  (a, b, c, d).

Example prog_expected : prog = (D3, D4, D5, D1) := ltac:(vm_compute; reflexivity).
