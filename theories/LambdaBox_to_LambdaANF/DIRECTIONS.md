# Directions for Completing the ANF Correctness Proof

## Overview

The file `anf_correct.v` contains the semantic correctness proof for the ANF
conversion from MetaRocq Erasure (`EAst.term`) to LambdaANF. This is part of a
larger refactoring that removes LambdaBoxMut and LambdaBoxLocal intermediate
representations, going directly from MetaRocq Erasure to LambdaANF.

The old correctness proof is in
`LambdaANF/LambdaBoxLocal_to_LambdaANF_anf_correct.v` and serves as a
reference. The new proof adapts it to the MetaRocq pipeline, which introduces
`tConst` (global constants) — a construct not present in the old source language.

## Invariant Chain (DONE)

The `cmap_consistent` invariant and its interaction with `env_consistent` is
fully resolved. The following are all proved (Qed):

- **`cmap_consistent`** — definition tracking global constant provenance
- **`env_consistent_extend`** — trivial 4-line lemma
- **`cmap_consistent_extend`** — trivial analog
- **`anf_cvt_rel_var_lookup_and_cmap_eval`** — combined lemma proving BOTH
  var_lookup (Part 1) and cmap_eval (Part 2) simultaneously by eval induction.
  All 12 cases proved. Part 2 replaces the false `anf_cvt_result_cmap` and
  removes the need for `eval_tConst_inv`.
- **`anf_cvt_rel_var_lookup`** — corollary of Part 1
- **`anf_cvt_cmap_eval`** — corollary of Part 2
- **`env_consistent_extend_from_cvt`** — combines var_lookup + extend
- **`cmap_consistent_extend_from_cvt`** — uses cmap_eval + extend

Only admitted dependency: `eval_val_det` (value determinism).

### Key discovery: `anf_cvt_result_cmap` is FALSE

Counterexample: `tLetIn na (tConst k) (tRel 0)` — the result is a cmap
variable but the expression is not `tConst k`. Replaced by `anf_cvt_cmap_eval`
which directly gives `eval [] body_k (Val v)` without requiring `e = tConst k`.

### Key design: inner conjunction in combined lemma

The conjunction in `anf_cvt_rel_var_lookup_and_cmap_eval` is placed AFTER the
shared hypotheses (env_consistent, cmap_consistent, Disjoint, etc.) so that
`intros` works uniformly for both parts:
```coq
forall v, r = Val v -> forall S vn S' C x,
  anf_cvt_rel' S e vn S' C x -> Disjoint ... -> ... ->
  (forall i, nth_error vn i = Some x -> nth_error rho i = Some v) /\
  (forall k decl body, lookup_const cmap k = Some x -> ... -> exists f' t', ...)
```

## What's Done in `anf_cvt_correct`

### Proved cases (12 of 21)
- `eval_Rel_fuel`, `eval_Lam_fuel`, `eval_Fix_fuel`, `eval_Box_fuel`
- `eval_OOT`, `eval_step`
- All 6 OOT step cases (+ 2 App OOT cases)
- `eval_many_nil`

### `eval_LetIn_step` case (template)
Structurally complete with IH chaining. Two inline admits for `global_env_rel'`
contract when shadowing a cmap variable (lines ~1348, ~1408). These need
`anf_cvt_cmap_eval` + `eval_val_det` + `anf_cvt_val_alpha_equiv`.

### `eval_App_step` case (in progress)
**What's done:**
- IH1/IH2 chaining via `preord_exp_trans` (both complete)
- IH2 continuation disjointness fully proved (Free_Eletapp1/2 case analysis)
- Closure structure extracted via `inv Hrel_clos` (anf_rel_Clos)
- IH3 invocation skeleton with `env_consistent_extend_fresh` for body
- Body bstep extraction via Ehalt witness (`BStepf_run` + `BStept_halt`)
- OOT case handled trivially
- Res case: body result `v_bc_val` extracted with `preord_val` from `Hres_bc`
- Env bridge for continuation via `preord_exp_refl`
- `BStept_letapp` fully constructed for the `x1 ≠ x2` branch
- `Disjoint (FromList (x0::names)) S1` proved
- Ehalt r1 continuation disjointness proved

**Remaining admits (17 in App case):**
1. **x1 = x2 case** (~160 lines in old proof, lines 3249-3410). When x1 = x2,
   the argument shadows the closure. Need `preord_val_trans` to show v2' is
   also a valid Vfun. This is the HARDEST remaining piece.
2. **IH1 continuation disjointness** — App-specific context free-variable
   reasoning for `C2 |[ Eletapp ... e_k ]|`. Similar to the admitted
   `anf_cvt_disjoint_occurs_free_ctx` but for App structure.
3. **global_env_rel' for M.set x1 v1' rho** — same pattern as LetIn's admit.
4. **IH3 env construction** (6 admits) — well_formed_env, wellformed body0,
   cmap_consistent for closure, anf_env_rel with def_funs, global_env_rel'.
   All mechanical but need careful env/def_funs reasoning.
5. **Fuel/step-index bounds** (5 admits) — `1 <= i` from Res, `cin_ek <= i-1`,
   `preord_val` at reduced index, Post condition, preord_res, fuel composition.
6. **y ∉ {x1,x2} in env bridge** — from `Hdis_ek`.

### Not yet written
FixApp, Construct, Case, Proj, Const, eval_many_cons.

## Admitted Helper Lemmas

1. **`eval_val_det`** — Value determinism. Only admitted dependency of the
   invariant chain. Provable by mutual induction on eval.
2. **`eval_preserves_wf`** — Eval preserves well-formedness. Standard.
3. **`anf_cvt_disjoint_occurs_free_ctx`** — Free variables of context
   application avoid consumed vars. Structural. Also needed for App (IH1).

## Technical Notes

### Hypothesis naming after `destruct`/`injection`
`destruct Hcvt` on `anf_cvt_rel` renames variables to the constructor's
parameter names (e.g., `vn0 → vn`, `S0 → S1`, `x0 → x2`). NEVER reference
variable names after `destruct`/`injection`. Instead:
- Assert facts BEFORE `destruct` (e.g., `assert (Hin : x0 \in FromList vn0)`)
- Use `match goal with` for robust hypothesis selection
- Use hypothesis names (stable across destruct) not variable names

### `inv` on `occurs_free` with evars
`inv` on `occurs_free ?e_k` when `?e_k` is an evar matches ALL constructors.
Fix: prove disjointness assertions BEFORE `edestruct` so `?e_k` is unified.

### Conversion inversion hangs
`inv`/`inversion` on `anf_cvt_rel` (large mutual inductive) causes Coq to hang.
Use `remember` + `destruct` + `injection` instead (see CLAUDE.md).

### `eval_env_fuel_ind'` goal ordering
After `try (intros; exact I); try (intros; congruence)` consumes OOT/True:
P_step terminating (7): App, FixApp, LetIn, Construct, Case, Proj, Const.
P_fuel Val (4): Rel, Lam, Fix, Box.
P_fuel other (1): eval_step.

### Key tactic patterns
- `preord_exp_trans`: `eapply preord_exp_trans; [tci | exact eq_fuel_idemp | | ]`
- `preord_exp_refl` for env bridging: case split on `Pos.eq_dec y x`
- `BStept_letapp` needs 6 args: M.get f, get_list ys, find_def, set_lists, body bstep, cont bstep
- `Setminus` is Inductive: use bare `destruct`
- `Disjoint` proof: `constructor. intros z Hz. inv Hz. ...`

### App case: x1 = x2 issue
When e1 and e2 both return the same variable (e.g., both `tRel n`), `x1 = x2`.
Then `rho_app = M.set x1 v2' (M.set x1 v1' rho)` has `v2'` at x1, NOT `v1'`.
The `BStept_letapp` gets `v2'` as the function, not the closure `v1'`.
Old proof (lines 3249-3410) handles this via `preord_val_trans`:
show v2' is also a valid Vfun using `anf_cvt_val_alpha_equiv`.

## Section Parameters
```coq
func_tag kon_tag default_tag default_itag : positive
tgm : conId_map
cmap : const_map
cenv : ctor_env
Σ : EAst.global_context
{efl : EEnvFlags}
dcon_to_tag_inj : forall dc dc', dcon_to_tag ... dc = ... dc' -> dc = dc'
box_dc : dcon
box_tag : dcon_to_tag default_tag box_dc tgm = default_tag
cmap_inj : forall k1 k2 v, lookup_const cmap k1 = Some v ->
                             lookup_const cmap k2 = Some v -> k1 = k2
Hglob_term : globals_terminate_prop
```

## File Dependencies
```
common.v → ANF.v → fuel_sem.v → wf.v → anf_corresp.v → anf_util.v → anf_correct.v
```

## Old Proof Reference
`LambdaANF/LambdaBoxLocal_to_LambdaANF_anf_correct.v` — key lemmas:
- `anf_cvt_rel_var_lookup` (line ~2069): the key invariant lemma
- `env_consistent_extend` (line ~822): the trivial extension
- `env_consistent_extend_from_cvt` (line ~2231): combines the two
- The LetIn step case (line ~3515): template for IH chaining
- The App step case (line ~3075): x1=x2 case split at line ~3248
