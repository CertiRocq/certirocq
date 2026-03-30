# Directions for Completing the ANF Correctness Proof

## Overview

The file `anf_correct.v` contains the semantic correctness proof for the ANF
conversion from MetaRocq Erasure (`EAst.term`) to LambdaANF. The old proof is in
`LambdaANF/LambdaBoxLocal_to_LambdaANF_anf_correct.v`.

## App Case: DONE (0 admits)

The `eval_App_step` case is fully proved. Key elements:
- IH1/IH2/IH3 chaining via `preord_exp_trans` with explicit `P1 := anf_bound (f3+2) (t3+2)`
- IH3 step index `(i+1)` so Ehalt consumes 1, leaving `preord_val` at step `i`
- Env bridge for x1≠x2: FromList → alpha-equiv, S → contradiction, cmap_vars → `In_dec` case split
- x1=x2 case: `preord_val_trans`, body transfer via `bstep_fuel_deterministic`, 160+ lines
- x1=x2 cmap-only: unified via `In_dec` on `FromList vnames`, target value from `Hglob` when not in `FromList`

## Key Design Decisions

### `kn_deps`-restricted `global_env_rel'`
Correctness predicates use `global_env_rel' (kn_deps e) rho` instead of `(fun _ => True)`.
- `anf_rel_Clos` stores `global_env_rel' (kn_deps body) rho_closure`
- IH3 in App: uses closure's `global_env_rel'` + weakening through `def_funs`/`M.set`
- IH1/IH2: `global_env_rel_mono` for domain weakening
- Shorthands: `kn_deps`, `kn_deps_list`, `kn_deps_mfix` in `common.v`

### `cmap_consistent` in `anf_val_rel`
Added `cmap_consistent names vs` to `anf_rel_Clos` and `anf_rel_ClosFix` in `anf_util.v`.
- Definition moved from `anf_correct.v` to `anf_util.v` (next to `env_consistent`)
- `anf_correct.v` uses a `Let` shorthand instantiating the `anf_util` version
- After `inv Hrel_clos`: extract with `assert (Hcmap_clos : cmap_consistent names rho') by assumption`
- `anf_cvt_val_alpha_equiv` (Qed) — fixed hypothesis shifts from the insertion

## What's Done in `anf_cvt_correct`

### Proved cases
- `eval_App_step` (0 admits), `eval_App_step_OOT1`, `eval_App_step_OOT2`
- `eval_Rel_fuel`, `eval_Lam_fuel`, `eval_Fix_fuel`, `eval_Box_fuel`
- `eval_OOT`, `eval_step`
- `eval_many_nil`

### `eval_LetIn_step` (1 admit)
Line ~1902: `eval_tConst_inv + value det` in cmap env bridge. Should be closable
with the same `In_dec` + `anf_cvt_cmap_result_in_deps` pattern used in App.

### Not yet written (7 admits)
FixApp, Construct, Case, Proj, Const, eval_many_cons, ClosFix alpha-equiv global_env_rel'.

## Admitted Helper Lemmas (4)

1. **`eval_val_det`** — Value determinism. Provable by mutual induction on eval.
2. **`eval_preserves_wf`** — Eval preserves well-formedness.
3. **`anf_cvt_disjoint_occurs_free_ctx`** — LetIn-specific context disjointness.
4. **`anf_cvt_disjoint_occurs_free_ctx_app`** — App-specific context disjointness.
   Both need `anf_cvt_occurs_free_ctx_subset` (~500 lines, port from old proof).
5. **`anf_cvt_cmap_result_in_deps`** — If ANF result ∈ cmap_vars and ∉ FromList vn,
   then k ∈ term_global_deps e. Structural, by induction on `anf_cvt_rel`.

## Helper Lemmas (Qed)

- `anf_env_rel_weaken` — M.set with x ∉ FromList vnames preserves `anf_env_rel`
- `global_env_rel_set_fresh` — M.set with x ∉ cmap_vars preserves `global_env_rel'`
- `global_env_rel_set` — General M.set weakening for `global_env_rel'`
- `global_env_rel_mono` — Domain monotonicity (D2 ⊆ D1)
- `anf_cvt_val_alpha_equiv` — Alpha-equivalence (Qed in anf_util.v)

## Technical Notes

### `anf_cvt_val_alpha_equiv` instantiation
```coq
eapply (@anf_cvt_val_alpha_equiv
  _ _ _ _ eq_fuel eq_fuel tgm cmap cenv
  eq_fuel_compat (fun _ _ H => H)
  nat LambdaBox_resource_fuel LambdaBox_resource_trace
  Σ box_dc Hglob_term func_tag default_tag)
```

### After `inv Hrel_clos`
- Save before: `pose proof Hrel_clos as Hrel_clos_saved`
- Extract cmap_consistent: `assert (Hcmap_clos : cmap_consistent names rho') by assumption`
- All H-numbered refs shift by 1 — use `match goal with` or `eassumption`

### Hypothesis naming after `destruct`/`injection`
Never reference variable names after `destruct`/`injection`. Use `match goal with`.

### `Disjoint` is Inductive
Use `constructor; intros z Hz; destruct Hz as [Ha Hb]`, not `intros z [Ha Hb]`.
