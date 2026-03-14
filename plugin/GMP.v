From MetaRocq Require Import Show.
From MetaRocq.Utils Require Import bytestring.
From Corelib Require Import Numbers.Cyclic.Int63.PrimInt63 PrimString.
From CertiRocq.Plugin Require Import Loader PrimInt63 PrimString.

(** Remove metarocq warning, we know what we're doing! *)
Set Warnings "-primitive-turned-into-axiom".

(* https://github.com/ocaml/Zarith/blob/master/z.mli *)

(* Axiomatisation *)
Axiom t : Type.

Axiom zero : t.
Axiom one : t.
Axioms succ pred abs neg : t -> t.
Axioms add sub mul div rem : t -> t -> t.
Axiom pow : t -> t -> t.
Axiom equal : t -> t -> bool.
Axiom compare : t -> t -> int. (* int63 *)

Axiom of_int : int -> t.
Axiom of_string : string -> t.
Axiom to_string : t -> string.

Axioms logand logor logxor : t -> t -> t.
Axiom lognot : t -> t.

Axioms max min : t -> t -> t.
Axioms leq geq lt gt : t -> t -> bool.

(* Implicitely coerce from primitive ints *)
Coercion of_int : int >-> t.

(* Very inefficient *)
Definition of_nat (n : nat) := of_string (pstring_of_string (show n)).

Module GMPNotations.
  Declare Scope gmp_scope.
  Bind Scope gmp_scope with t.
  Delimit Scope gmp_scope with gmp.
  Infix "+" := add : gmp_scope.
  Infix "-" := sub : gmp_scope.
  Infix "*" := mul : gmp_scope.
  Infix "^" := pow : gmp_scope.
  Infix "/" := div : gmp_scope.
  Notation "x 'modulo' y" := (rem x y) (at level 40, left associativity) : gmp_scope.
  Infix "==" := equal (at level 70, no associativity) : gmp_scope.
  Infix "=?" := compare (at level 70, no associativity) : gmp_scope.
  Infix "'land'" := logand (at level 40, left associativity) : gmp_scope.
  Infix "'lor'" := logor (at level 40, left associativity) : gmp_scope.
  Infix "'lxor'" := logxor (at level 20, left associativity) : gmp_scope.
  Notation "'lnot' x" := (lognot x) (at level 10, no associativity) : gmp_scope.
  Notation "| x |" := (abs x%_gmp) (at level 10, no associativity, only printing) : gmp_scope.
  Infix "<" := lt : gmp_scope.
  Infix "≤" := leq (at level 70) : gmp_scope.
  Infix "≥" := geq (at level 70) : gmp_scope.
  Infix ">" := gt (at level 70) : gmp_scope.
End GMPNotations.
Import GMPNotations.
Local Open Scope gmp_scope.

CertiRocq Register [
  t => "erased",
  zero => "z_zero",
  one => "z_one",
  succ => "z_succ" with tinfo,
  pred => "z_pred" with tinfo,
  abs => "z_abs" with tinfo,
  neg => "z_neg" with tinfo,
  add => "z_add" with tinfo,
  sub => "z_sub" with tinfo,
  mul => "z_mul" with tinfo,
  div => "z_div" with tinfo,
  rem => "z_rem" with tinfo,
  pow => "z_pow" with tinfo,

  logand => "z_logand" with tinfo,
  logor => "z_logor" with tinfo,
  logxor => "z_logxor" with tinfo,
  lognot => "z_lognot" with tinfo,

  max => "z_max",
  min => "z_min",

  leq => "z_leq",
  geq => "z_geq",
  lt => "z_lt",
  gt => "z_gt",

  compare => "z_compare",

  of_int => "z_of_int",
  of_string => "z_of_string" with tinfo,
  to_string => "z_to_string" with tinfo,

  equal => "z_equal"
]
Include [ Library "certirocq_gmp.h", LibraryPath "/opt/homebrew/lib", Link "gmp" ].
(* TODO test presence of files/paths? *)

Definition compare_signed x y := wrap_int (compare x y).

Instance show_t : Show t := { show x := string_of_pstring (to_string x) }.
