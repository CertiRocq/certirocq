From CertiRocq.Plugin Require Import Loader.
From CertiRocq.Plugin Require Import CertiRocq.
From MetaRocq.Utils Require Import utils.

Set CertiRocq Build Directory "_build".

Open Scope bs_scope.

Class Show (A : Type) := show : A -> string.

#[export] Instance nat_show : Show nat := string_of_nat.
Local Open Scope bs.
Definition string_of_bool b :=
  if (b : bool) then "true" else "false".
#[export] Instance bool_show : Show bool := string_of_bool.

Definition test := true.
CertiRocq Eval -time -debug test.

#[export] Instance list_show {A} {SA : Show A} : Show (list A) := string_of_list show.
From MetaRocq.Common Require Import Primitive.
From Stdlib Require Import PrimFloat PrimInt63.
#[export] Instance float_show : Show PrimFloat.float := string_of_float.
#[export] Instance prim_int_show : Show PrimInt63.int := string_of_prim_int.

Import SpecFloat.
Definition string_of_specfloat (f : SpecFloat.spec_float) :=
  match f with
  | S754_zero sign => if sign then "-0" else "0"
  | S754_infinity sign => if sign then "-infinity" else "infinity"
  | S754_nan => "nan"
  | S754_finite sign p z =>
  let num := string_of_positive p ++ "p" ++ string_of_Z z in
  if sign then "-" ++ num else num
  end.

#[export] Instance show_specfloat : Show SpecFloat.spec_float := string_of_specfloat.
#[export] Instance show_positive : Show positive := string_of_positive.
#[export] Instance show_Z : Show Z := string_of_Z.

Definition certirocqc2 := 5.
Definition certirocqc3 := msg_notice ("Hello world! " ++ show 100%nat).
 (* show (0%float == (-0)%float)). *)

Inductive three_ind := One | Two | Three.
Definition one := One.
Definition two := Two.
Definition three := Three.

Definition certirocqc4 :=  (List.map S [26; 20]).

Time Eval compute in certirocqc4.
Set Warnings "-primitive-turned-into-axiom".
Set Warnings "backtrace".
CertiRocq Eval -time -debug certirocqc4.

Definition largertag := S754_finite true xH 0%Z.
Definition otherlargertag := S754_infinity true.
CertiRocq Eval -time -debug otherlargertag.

Set Debug "certirocq-reify".
Time CertiRocq Eval -time one.
CertiRocq Eval -time two.
CertiRocq Eval -time -debug three.
Time CertiRocq Eval -time -debug three.

(*
Goal True.
  intros.
  certirocq_eval -build_dir "_build" certirocqc4 ltac:(fun c => assert (certirocqc4 = c) by reflexivity).
  exact I.
Qed. *)
