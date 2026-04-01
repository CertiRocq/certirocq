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

### `eval_FixApp_step` (0 admits)
Same structure as App but with `ClosFix_v`. Uses `anf_fix_rel_exists`,
`anf_env_rel_extend_fundefs`, `env_consistent_make_rec_env`, `cmap_consistent_make_rec_env`.

### `eval_Case_step` (4 admits)
Structure: Efun_red → IH_mch through C1 → Eletapp (calling case function) →
Ecase dispatch + ctx_bind_proj + IH_body → env bridge → BStept_letapp.
- `anf_trace_exp (tCase)` = `4 + max_branch_fields brs` (accounts for projection overhead)
- Concrete `P1 := anf_bound (f2 + length br_vars + 3) (t2 + length br_vars + 3)` for inner trans
- `find_branch_wellformed` / `find_branch_max_fields` helper lemmas
- `preord_exp_Ecase_red` uses `cenv_case_consistent` Context variable
- Remaining admits: see below

### Not yet written
Proj, Const, eval_many_cons, ClosFix alpha-equiv global_env_rel'.

## Admitted Helper Lemmas (4)

1. **`eval_val_det`** — Value determinism. Provable by mutual induction on eval.
2. **`eval_preserves_wf`** — Eval preserves well-formedness.
3. **`anf_cvt_disjoint_occurs_free_ctx`** — LetIn-specific context disjointness.
4. **`anf_cvt_disjoint_occurs_free_ctx_app`** — App-specific context disjointness.
   Both need `anf_cvt_occurs_free_ctx_subset` (~500 lines, port from old proof).
5. **`anf_cvt_cmap_result_in_deps`** — If ANF result ∈ cmap_vars and ∉ FromList vn,
   then k ∈ term_global_deps e. Structural, by induction on `anf_cvt_rel`.

### Case proof remaining admits (4)
1. **`Disjoint (occurs_free (Eletapp ...))` (line ~4252)** — IH_mch continuation disjointness.
   Depends on `anf_cvt_disjoint_occurs_free_ctx` (shared Admitted helper).
2. **`In body0 (map snd brs)` (line ~4396)** — Trivial from `find_branch`. 10-line induction.
3. **`Disjoint (occurs_free (Ehalt r_br))` (line ~4410)** — Trivially true ({r_br} disjoint
   from ... \\ {r_br}). Proof fails because `edestruct IH_body` leaves `e_k` as evar.
   Fix: assert the Disjoint before the `edestruct`, or specialize `IH_body` with
   `(Ehalt r_br)` before destructing.
4. **`preord_val ... v_z (Vconstr c_tag vs_anf)` (line ~4488)** — Alpha-equiv in env bridge
   (z = x1 ∈ vnames). Both values related to same source constructor. Provable via
   `anf_cvt_result_in_vnames_eval` + `anf_cvt_val_alpha_equiv`.

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
Never reference variable names after `destruct`/`injection`/`inv`/`subst`.
Use `match goal with` or `destruct` with named patterns.

### `Disjoint` is Inductive
Use `constructor; intros z Hz; destruct Hz as [Ha Hb]`, not `intros z [Ha Hb]`.

### `Intersection` destruct
`Intersection` is Inductive with constructor `Intersection_intro : forall x, B x -> C x -> ...`.
To destruct `Hc : Intersection _ B C z`, use `inversion Hc; subst` (NOT `destruct Hc as [H1 H2]`
which fails). Alternatively, `inv Hc` works if hypothesis names are acceptable.

### `occurs_free` has 17 constructors
Cannot use `inv` or `inversion` directly (may hang or generate 17 subgoals).
For specific expression forms like `Ehalt`, write a dedicated inversion lemma:
```coq
Lemma occurs_free_Ehalt_inv x z : occurs_free (Ehalt x) z -> z = x.
Proof. intros H. remember (Ehalt x) as eH. destruct H; congruence. Qed.
```
For `Eletapp`, use `remember (Eletapp ...) as e_let. destruct H; try congruence; injection ...`.

### `edestruct` leaves evars for later arguments
When using `edestruct (IH rho vnames C x S S' i) as [H1 _]`, the continuation `e_k`
(which comes after the 9 preconditions) remains as a unification variable. Goals that
depend on `e_k` (like `Disjoint (occurs_free e_k) ...`) cannot be proved because they
contain `?e_k` instead of a concrete expression.
**Fix**: either (a) prove such goals BEFORE the `edestruct`, or (b) `specialize` the IH
with the concrete continuation first, e.g., `specialize (IH ... (Ehalt r) Hdis_ehalt)`.

### `Setminus` destruct
`Setminus` is Inductive. Use `destruct H as [H1 H2]` to get `H1 : S x` and `H2 : ~ T x`.
For nested Setminus `(A \\ B) \\ C`, destruct twice.

### `comp_ctx_f` / `Efun1_c` stuck reductions
`app_ctx_f (comp_ctx_f C1 C2) e` does NOT reduce when `C1` is a variable.
Use `rewrite app_ctx_f_fuse` (direction: `C1 |[ C2 |[ e ]| ]| = comp_ctx_f C1 C2 |[ e ]|`)
or the helper `Efun1_c_comp_simpl`.
`app_ctx_f (Efun1_c B C) e` DOES reduce by computation to `Efun B (app_ctx_f C e)`.

### `Forall_app` direction
In this codebase, `Forall_app` gives `Forall P (l1 ++ l2) -> Forall P l1 /\ Forall P l2`
(forward only, NOT an iff). To build `Forall P (l1 ++ l2)`, use
`apply Forall_forall; intros v Hv; apply in_app_or in Hv; destruct ...`.

### `res` constructor order
`Inductive res := OOT | Res : A -> res`. `OOT` is the FIRST constructor, `Res` is SECOND.
So `destruct r as [| v]` gives OOT first, Res second.

### `anf_bound f t` has two components
`anf_bound f t` means `f1 + f <= f2 <= f1 + t` — the fuel `f` is a LOWER bound,
the trace `t` is an UPPER bound. Projection overhead (n_vars) is absorbed by the
trace upper bound (via `anf_trace_exp (tCase) = 4 + max_branch_fields brs`),
not the fuel lower bound.

### `preord_val_monotonic` argument order
`preord_val_monotonic : preord_val k v1 v2 -> j <= k -> preord_val j v1 v2`.
The proof term comes FIRST, then the inequality.
