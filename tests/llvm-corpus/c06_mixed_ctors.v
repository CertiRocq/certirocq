(* A type with many nullary AND many non-nullary constructors, interleaved,
   so that the boxed and unboxed ordinals differ from the constructor
   indices: the emitted [Ecase] first tests the low bit, then switches on
   [ord] (unboxed: word >> 1; boxed: header & 1023) -- 12 unboxed and 12
   boxed arms, plus a default.  Values are produced by a recursive function
   so the optimizer cannot fold the matches.
   Targets: Ecase (boxed/unboxed dispatch), repr_val Repr_unboxed vs
   Repr_boxed, cenv_ok (ordinals distinct per kind).
   Expected (Rocq): (D1, B11 D4, N3, B2 (B0 D2))
   EXPECTED: (C0 (C0 (C0 1 (C11 4)) 3) (C2 (C0 2))) *)
Inductive d7 := D0 | D1 | D2 | D3 | D4 | D5 | D6.
Definition s7 (d : d7) : d7 :=
  match d with D0 => D1 | D1 => D2 | D2 => D3 | D3 => D4 | D4 => D5 | D5 => D6 | D6 => D0 end.

Inductive mix :=
| N0 | B0 (a : d7) | N1 | B1 (a b : d7) | N2 | B2 (a : mix) | N3 | B3 (a : d7) (m : mix)
| N4 | B4 (a : d7) | N5 | B5 (a b c : d7) | N6 | B6 (a : d7) | N7 | B7 (a : d7)
| N8 | B8 (a : d7) | N9 | B9 (a : d7) | N10 | B10 (a : d7) | N11 | B11 (a : d7).

(* the k-th constructor (k mod 24), with payload x *)
Fixpoint gen (k : nat) (x : d7) : mix :=
  match k with
  | 0 => N0 | 1 => B0 x | 2 => N1 | 3 => B1 x (s7 x) | 4 => N2 | 5 => B2 (B0 x)
  | 6 => N3 | 7 => B3 x N3 | 8 => N4 | 9 => B4 x | 10 => N5 | 11 => B5 x x x
  | 12 => N6 | 13 => B6 x | 14 => N7 | 15 => B7 x | 16 => N8 | 17 => B8 x
  | 18 => N9 | 19 => B9 x | 20 => N10 | 21 => B10 x | 22 => N11 | 23 => B11 x
  | S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S k')))))))))))))))))))))))
      => gen k' (s7 x)
  end.

(* A distinct score per constructor, mixing in the payload *)
Fixpoint score (m : mix) (acc : d7) : d7 :=
  match m with
  | N0 => acc | N1 => s7 acc | N2 => s7 (s7 acc) | N3 => s7 (s7 (s7 acc))
  | N4 => acc | N5 => s7 acc | N6 => s7 (s7 acc) | N7 => s7 (s7 (s7 acc))
  | N8 => acc | N9 => s7 acc | N10 => s7 (s7 acc) | N11 => s7 (s7 (s7 acc))
  | B0 a => s7 a | B1 a b => s7 (s7 b) | B2 m' => score m' (s7 acc)
  | B3 a m' => score m' a | B4 a => a | B5 a b c => s7 c | B6 a => s7 (s7 a)
  | B7 a => a | B8 a => s7 a | B9 a => a | B10 a => s7 a | B11 a => s7 (s7 a)
  end.

Fixpoint run (k : nat) (acc : d7) : d7 :=
  match k with O => acc | S k' => run k' (score (gen k' acc) acc) end.

Definition prog : d7 * mix * mix * mix :=
  (run 500 D0, gen 23 D4, gen 6 D0, gen 5 D2).

Example prog_expected : prog = (D1, B11 D4, N3, B2 (B0 D2)) := ltac:(vm_compute; reflexivity).
