From MetaRocq.Utils Require Import utils.
Open Scope bs_scope.

Require Import CertiRocq.Compiler.pipeline.
From CertiRocq.Common Require Import Pipeline_utils.
Require Import ExtLib.Structures.Monad.
Import Monads.
Import MonadNotation.
Import ListNotations.

(** * The main CertiRocq pipeline, with MetaRocq's erasure and C-code generation *)
Definition next_id := 100%positive.

Definition pipeline (p : Template.Ast.Env.program) :=
  CertiRocq.Compiler.pipeline.pipeline p.
  
Definition compile (opts : Options) (p : Template.Ast.Env.program) :=
  run_pipeline _ _ opts p pipeline.
  
Transparent CertiRocq.Compiler.pipeline.compile.

Definition certirocqc (opts : Options) (p : Template.Ast.Env.program) :=
  compile opts p.
