(* Sanity: no allocation, no GC.  Unboxed nullary constructor result.
   Targets: the boxed/unboxed result representation (repr_val Repr_unboxed),
   make_tinfo (runtime_correct clause 1) only.
   Expected: true, which is ordinal 1 (Loader.v remaps bool to [1 0]).
   EXPECTED: 1 *)
Definition prog : bool := negb (negb true).

Example prog_expected : prog = true := ltac:(vm_compute; reflexivity).
