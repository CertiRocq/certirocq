From MetaRocq Require Import Show.
From MetaRocq.Utils Require Import bytestring.
From Corelib Require Import Numbers.Cyclic.Int63.PrimInt63 PrimString.
From CertiRocq.Plugin Require Import Loader PrimInt63 PrimString GMP.
From CertiRocq.Plugin Require Import RocqMsgFFI.
Set CertiRocq Build Directory "_build".

Import GMPNotations.
Local Open Scope gmp_scope.

Notation " f $ x " := (f x) (only parsing, at level 110, x at next level, left associativity).

Definition test_zarith := eq_refl : (CertiEval (equal (add zero one) (add one zero))) = true.

Open Scope bs.

Eval compute in CertiEval msg_info ("Length is " ++ (show (length (to_string (of_string "40"))))).
Eval compute in CertiEval show (add one (of_int Uint63Axioms.max_int)).
Eval compute in CertiEval show $ of_int Uint63Axioms.max_int.
Eval compute in CertiEval show $ pow (of_int 2) (of_int 64).
Eval compute in CertiEval show $ (of_int 64).
Eval compute in CertiEval show $ (2 ^ 64 + 2 ^ 64 == 2 ^ 65).
Eval compute in CertiEval show $ (2 ^ 64 * 2 ^ 64 == 2 ^ 128).
Eval compute in CertiEval show $ (2 ^ 64 / 2 == 2 ^ 63).
Eval compute in CertiEval show $ (2 ^ 64 / 4 == 2 ^ 62).
Eval compute in CertiEval show $ (1 - 2).
Eval compute in CertiEval show $ (0 - 2 ^ 64 + 2).
Eval compute in CertiEval (14 modulo 5 == 4).
