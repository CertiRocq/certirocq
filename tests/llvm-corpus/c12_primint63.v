(* PrimInt63 arithmetic (non-allocating primitives), including wrap-around.
   NOTE: primitive OPERATIONS ([Eprim]) are outside [body_ok]: the
   correctness theorem only covers primitive int VALUES ([Eprim_val]).  The
   emitter lowers non-allocating int63 ops to calls of the C runtime's
   [prim_int63_*] (runtime/prim_int63.c) on tagged words; this test checks
   that path end to end, not the theorem.
   The result is a list of ints; an int [n] is the unboxed word 2n+1 and is
   printed as [n] (unsigned, 0 <= n < 2^63).
   Expected (Rocq): [0; 9223372036853541241; 9223372036854775806; 5931159524472463201; 13871; 48; 0; 1234567; 1; 1234655; 1234654; 1357420771768532992; 0; 1; 154320; 0; 1; 1; 0]
   EXPECTED: (C0 0 (C0 9223372036853541241 (C0 9223372036854775806 (C0 5931159524472463201 (C0 13871 (C0 48 (C0 0 (C0 1234567 (C0 1 (C0 1234655 (C0 1234654 (C0 1357420771768532992 (C0 0 (C0 1 (C0 154320 (C0 0 (C0 1 (C0 1 (C0 0 0))))))))))))))))))) *)
From Stdlib Require Import Uint63 List.
Import ListNotations.
Open Scope uint63_scope.

Definition max : int := 9223372036854775807.   (* 2^63 - 1 *)

(* run-time inputs, so that nothing is constant-folded *)
Fixpoint hide {A} (n : nat) (a : A) : A := match n with O => a | S m => hide m a end.

Definition prog : list int :=
  let m := hide 0 max in
  let a := hide 0 1234567 in
  let b := hide 0 89 in
  [ m + 1                       (* wraps to 0 *)
  ; 0 - a                       (* 2^63 - 1234567 *)
  ; m * 2                       (* 2^63 - 2 *)
  ; a * a * a * a               (* wraps mod 2^63 *)
  ; a / b ; a mod b ; a / 0 ; a mod 0  (* x/0 = 0, x mod 0 = x *)
  ; a land b ; a lor b ; a lxor b
  ; a << 40 ; a << 63 ; m >> 62 ; a >> 3
  ; (if a <? b then 1 else 0) ; (if b <=? a then 1 else 0) ; (if a =? a then 1 else 0)
  ; (if m <? m + 1 then 1 else 0)   (* unsigned: max <? 0 = false *)
  ].

Example prog_expected : prog = [0; 9223372036853541241; 9223372036854775806; 5931159524472463201; 13871; 48; 0; 1234567; 1; 1234655; 1234654; 1357420771768532992; 0; 1; 154320; 0; 1; 1; 0] := ltac:(vm_compute; reflexivity).
