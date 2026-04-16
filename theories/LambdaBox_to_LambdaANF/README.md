# LambdaBox to LambdaANF

Transformation from MetaRocq's erased terms (`EAst.term`) to LambdaANF
(`cps.exp`). The transformation can be done as an A-normal form (ANF)
conversion or as a continuation-passing style (CPS) conversion.

The CPS conversion is not yet proved correct.

## File Guide

- **ANF.v** — The ANF translation, including both the executable converter and
  the relational specification.

- **CPS.v** — The CPS conversion, between the same intermediate languages.

- **common.v** — Shared definitions:
  constructor discriminants (`dcon`), constructor tag maps, `const_map`,
  primitive lookup, and environment conversion helpers.

- **fuel_sem.v** — Source fuel-based semantics for source terms and semantic
  facts used by the correctness proofs.

- **wf.v** — Source-side well-formedness infrastructure used by the ANF proofs.

- **anf_util.v** — Shared ANF proof utilities:
  value relations, alpha-equivalence lemmas, environment facts, and shared
  global-context lemmas.

- **anf_corresp.v** — Correspondence between the executable conversion and the
  relational specification.

- **anf_correct.v** — Main termination correctness proof for ANF conversion.
  This file proves that terminating source evaluations are preserved by the ANF
  conversion.

- **anf_divergence.v** — Divergence preservation for ANF conversion.

- **anf_global.v** — Global-environment correctness lemmas and coherence facts
  used to lift expression-level correctness to programs with translated global
  declarations.

- **anf_toplevel.v** — End-to-end theorems for the top-level executable
  ANF conversion.

## Design Notes

- Global constants (`tConst`) are translated through a `const_map` (`kername ->
  var`) mapping global constant names to ANF variables, passed as an input.
  Global declarations are converted into ANF binding contexts wrapped around the
  translated main expression, so translated globals are available in the
  LambdaANF environment during evaluation.

- The names of global constants are preserved in the generated ANF binding
  contexts, so the resulting program can be pretty-printed using the original
  global names.

- `tLazy`, `tForce`, and `tCoFix` are assumed absent. `tProj` is translated to
  `Eproj`, and `tPrim` is translated through `trans_prim_val` (primitive arrays
  remain unsupported).

- Divergence is proved separately from termination. `anf_correct.v` handles
  terminating source evaluations, while `anf_divergence.v` handles source
  OOT/divergence with the additional lower-bound structure needed by the target
  semantics.
