From MetaRocq Require Import Show.
From CertiRocq.Plugin Require Import CertiRocq.
From Corelib Require Import Nat BinNums PrimInt63 PrimString.
From Stdlib Require Import ZArith.
Set CertiRocq Build Directory "_build".
Definition test_gmp :=
  msg_info (show (GMP.nat_case_dummy GMP.zero (fun _ => GMP.zero) (fun _ => GMP.one))).

CertiRocq Eval -unsafe-erasure -time -debug test_gmp.

CertiRocq Extract Inductive To Constants [
  nat => [ [ GMP.zero GMP.succ | GMP.nat_case ] ] ].

Definition testzi :=
  let g := Uint63Axioms.to_Z 1000%uint63 in
  msg_info (show g).

CertiRocq Show IR -unsafe-erasure -debug testzi.
CertiRocq Eval -unsafe-erasure -debug testzi.

Notation " f $ x " := (f x) (only parsing, at level 100, x at next level, right associativity).

Eval compute in CertiEval msg_info (show $ Uint63Axioms.to_Z 100%uint63).

CertiRocq Extract Inductive To Constants [
  nat => [ [ GMP.zero GMP.succ | GMP.nat_case ] ] ].

Definition testzi2 :=
  let g := Uint63Axioms.to_Z 1000%uint63 in
  msg_info (show g).

CertiRocq Show IR -unsafe-erasure -typed-erasure -debug testzi2.
CertiRocq Eval -unsafe-erasure -typed-erasure -debug testzi2.

Definition testzib :=
  show (match Nat.add 2 3 with
  | 0 => 0
  | S n => n
  end).

CertiRocq Show IR -unsafe-erasure -typed-erasure -debug testzib.
CertiRocq Eval -unsafe-erasure -typed-erasure -debug testzib.

Eval compute in CertiEvalTyped testzib.

CertiRocq Register [
  Corelib.Init.Nat.pred => "z_nat_pred" with tinfo,
  Corelib.Init.Nat.add => "z_add" with tinfo
] Include [ ].

Definition test_add_override :=
  show (Nat.add 1 1005).

CertiRocq Show IR -unsafe-erasure -typed-erasure -debug test_add_override.
CertiRocq Eval -unsafe-erasure -typed-erasure -debug -time test_add_override.
