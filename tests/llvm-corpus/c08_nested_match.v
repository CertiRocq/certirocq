(* Deeply nested matches: a depth-8 pattern over nested pairs/options/lists
   (the elaborated [Ecase] tree is 8+ levels deep, with projections between
   the levels), applied to 20000 generated inputs.
   Targets: Ecase nesting, Eproj chains, the emitted CFG's phi/dominance
   structure across many blocks.
   Expected (Rocq): D2
   EXPECTED: 2 *)
From Stdlib Require Import List PArith.
Import ListNotations.
Inductive d7 := D0 | D1 | D2 | D3 | D4 | D5 | D6.
Definition s7 (d : d7) : d7 :=
  match d with D0 => D1 | D1 => D2 | D2 => D3 | D3 => D4 | D4 => D5 | D5 => D6 | D6 => D0 end.

Definition shape := option (d7 * list (option (d7 * option d7))).

Fixpoint gen (n : nat) (x : d7) : shape :=
  match n with
  | O => None
  | S O => Some (x, [])
  | S (S O) => Some (x, [None])
  | S (S (S O)) => Some (x, [Some (x, None)])
  | S (S (S (S O))) => Some (x, [Some (x, Some (s7 x)); None])
  | S (S (S (S (S O)))) => Some (x, [Some (x, Some x); Some (s7 x, Some x)])
  | S (S (S (S (S (S n'))))) => gen n' (s7 x)
  end.

Definition classify (s : shape) : d7 :=
  match s with
  | None => D0
  | Some (a, []) => s7 a
  | Some (a, None :: []) => s7 (s7 a)
  | Some (_, Some (b, None) :: []) => b
  | Some (D3, Some (_, Some c) :: None :: []) => s7 c
  | Some (_, Some (_, Some c) :: None :: []) => c
  | Some (_, Some (D1, Some D1) :: Some (_, Some _) :: _) => D6
  | Some (_, Some (_, Some _) :: Some (D0, Some e) :: _) => s7 e
  | Some (_, Some (_, Some _) :: Some (_, Some e) :: _) => e
  | Some (a, _) => a
  end.

Fixpoint go (l : list unit) (k : nat) (x acc : d7) : d7 :=
  match l with
  | [] => acc
  | _ :: l' =>
      let k' := match k with S (S (S (S (S (S (S k')))))) => k' | _ => S k end in
      go l' k' (s7 x) (match classify (gen k x), acc with
                       | D0, a => a | D1, a => s7 a | D2, a => s7 (s7 a)
                       | _, D6 => D0 | _, a => s7 (s7 (s7 a)) end)
  end.

Definition prog : d7 := go (Pos.iter (cons tt) nil 20000) 0 D0 D0.

Example prog_expected : prog = D2 := ltac:(vm_compute; reflexivity).
