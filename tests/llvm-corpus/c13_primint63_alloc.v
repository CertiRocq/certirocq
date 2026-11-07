(* Allocating PrimInt63 primitives ([addc] returns a [carry int], a boxed
   constructor allocated by the C runtime) in a loop that also allocates
   and keeps a growing list live.
   NOTE: outside the theorem ([body_ok] excludes [Eprim]).  The emitter does
   NOT register the caller's live values as roots around an allocating
   primitive call (see the NOTE at [Eprim] in LambdaANF_to_LLVM.v), while
   prim_int63.c's allocating functions call garbage_collect when the
   nursery is full.  So a collection triggered inside [addc] leaves [keep]
   (held in an SSA register, not on the shadow stack) dangling.  EXPECTED
   TO FAIL (wrong result, crash, or a checker violation at a later
   collection) until the emitter adds a safepoint around allocating prims.
   Expected (Rocq): (D1, 9223372036854675808, D2)
   EXPECTED: (C0 (C0 1 9223372036854675808) 2) *)
From Stdlib Require Import Uint63 List PArith.
Import ListNotations.
Open Scope uint63_scope.
Inductive d7 := D0 | D1 | D2 | D3 | D4 | D5 | D6.
Definition s7 (d : d7) : d7 :=
  match d with D0 => D1 | D1 => D2 | D2 => D3 | D3 => D4 | D4 => D5 | D5 => D6 | D6 => D0 end.

Fixpoint len7 (l : list d7) (acc : d7) : d7 :=
  match l with [] => acc | _ :: l' => len7 l' (s7 acc) end.

Fixpoint loop (n : list unit) (keep : list d7) (acc : int) (carries : d7) : d7 * int * d7 :=
  match n with
  | [] => (len7 keep D0, acc, carries)
  | _ :: m =>
      let c := addc acc 6148914691236517205 in      (* ~ 2^63 / 3: carries often *)
      let keep' := D1 :: keep in
      match c with
      | C0 r => loop m keep' r carries
      | C1 r => loop m keep' r (s7 carries)
      end
  end.

Definition prog : d7 * int * d7 := loop (Pos.iter (cons tt) nil 300000) [] 0 D0.

Example prog_expected : prog = (D1, 9223372036854675808, D2) := ltac:(vm_compute; reflexivity).
