(* The stack-of-frames one-hole contexts, with the right indices, are isomorphic to
   [term.exp_ctx] and [term.fundefs_ctx] *)

From Stdlib Require Import ZArith.ZArith Lists.List Sets.Ensembles Strings.String.
From Stdlib Require Import Lia.
Import ListNotations.
From CertiRocq Require Import Common.
From CertiRocq.LambdaANF Require Import
    Prototype term term_util ctx
    identifiers Ensembles_util.

From MetaRocq Require Import Template.All.

From CertiRocq.LambdaANF Require Import PrototypeGenFrame term.

MetaRocq Run (mk_Frame_ops
  (MPfile ["cps_proto_univ"; "LambdaANF"; "CertiRocq"])
  (MPfile ["term"; "LambdaANF"; "CertiRocq"], "exp")
  exp [var; fun_tag; ctor_tag; prim; N; list var; primitive_value]).
