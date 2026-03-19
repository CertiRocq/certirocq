# LambdaBox to LambdaANF

Transformation from MetaRocq's erased terms (`EAst.term`) to LambdaANF (`cps.exp`).

## Files

- **common.v** — Shared definitions: constructor discriminants (`dcon`), constructor tag mapping (`conId_map`, `dcon_to_tag`), global constant map (`const_map`), primitive lookup, inductive environment processing (`convert_env`), primitive value translation (`trans_prim_val`).

- **ANF.v** — ANF conversion. Contains:
  - *Section Conversion*: Monadic ANF translation (`convert_anf`) and global environment conversion (`convert_global_decls`, `convert_top_anf`).
  - *Section Spec*: Declarative relational specification (`anf_cvt_rel`) used in correctness proofs.

- **CPS.v** — CPS conversion (`cps_cvt`, `convert_top_cps`).

- **anf_util.v** — Source value type (`value`: `Con_v`, `Clos_v`, `ClosFix_v`) and value relations (`anf_val_rel`, `anf_env_rel`, `anf_fix_rel`) connecting source evaluation results to LambdaANF values.

- **fuel_sem.v** — Environment-based big-step resource semantics for `EAst.term` (`eval_env_fuel`, `eval_env_step`). Uses the same resource algebra framework as LambdaANF (`LambdaANF.algebra`).

## Design

- Global constants (`tConst`) are translated to variable references via a `const_map` (`kername -> var`). Global environment bodies are converted to ANF binding contexts composed around the main expression, so all globals end up in the LambdaANF environment (`rho`) during evaluation.

- `tLazy`, `tForce`, `tCoFix` are assumed absent (can be enforced via preconditions). `tProj` is handled as `Eproj` (record field extraction). `tPrim` is translated via `trans_prim_val` (int, float, string; arrays unsupported).

- Global constant bodies are assumed to be values (lambdas, constructors, etc.), so their ANF conversion directly produces binding contexts without thunking.
