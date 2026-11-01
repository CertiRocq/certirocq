
From Stdlib Require Import Lists.List.
From Stdlib Require Import Strings.String.
From Stdlib Require Import Strings.Ascii.
From Stdlib Require Import Bool.Bool.
From Stdlib Require Import Bool.DecBool.
From Stdlib Require Import Arith.Arith.


Class Eq (A:Type) :=
  {
    eq_dec : forall (x y:A), {x = y} + {x<>y}
  }.

#[global] Instance NatEq: Eq nat := { eq_dec := eq_nat_dec }.
#[global] Instance AsciiEq: Eq ascii := { eq_dec:= ascii_dec }.
#[global] Instance StringEq: Eq string := { eq_dec:= string_dec }.
