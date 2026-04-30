# Structure of the directory

This directory contains the CertiRocq λANF development: the IR itself,
its semantics, the main optimization and compilation passes, and their
correctness proofs.

## Core IR and semantics

* `term.v`: λANF syntax
* `eval.v`: operational semantics
* `identifiers.v`, `tags.v`: names and tags used throughout the IR
* `algebra.v`: algebraic structure used in the semantics and proofs
* `ctx.v`, `stemctx.v`: context structure and utilities
* `state.v`: the λANF compilation monad
* `term_util.v`, `cps_show.v`, `size_cps.v`: basic support code for
  manipulating and inspecting λANF terms

## Main transformations

* `closure_conversion*.v`: closure conversion implementation and proofs
* `shrink_cps*.v`: shrinking transformation and top-level theorem
* `uncurry*.v`: uncurrying development
* `lambda_lifting*.v`: lambda lifting implementation and proofs
* `dead_param_elim*.v`: dead-parameter elimination
* `inline*.v`: inlining support and correctness
* `hoisting.v`, `freshen.v`, `alpha_conv.v`, `bounds.v`: additional
  transformation support and invariants

## Proof frameworks and libraries

* `logical_relations.v`, `logical_relations_cc.v`: logical-relations
  developments
* `rel_comp.v`, `relations.v`, `ctx_approx.v`: relational reasoning
  infrastructure
* `functions.v`, `List_util.v`, `map_util.v`, `set_util.v`,
  `Ensembles_util.v`, `env.v`, `rename.v`, `tactics.v`:
  general-purpose libraries

## Rewriting framework

* `MockExpr.v`, `Prototype.v`, `PrototypeGenFrame.v`, `Rewriting.v`
* `Frame.v`, `cps_proto.v`, `cps_proto_univ.v`, `uncurry_proto.v`,
  `proto_util.v`

## Pipeline entry points

* `toplevel.v`: the λANF pipeline
* `toplevel_theorems.v`: top-level correctness theorems

## Archived development

* `CPS-old/`: the older LambdaBoxLocal-based CPS development retained
  for reference after the pipeline reorganization
