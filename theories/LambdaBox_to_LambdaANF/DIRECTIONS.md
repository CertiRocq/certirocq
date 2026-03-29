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

## The Central Design Issue: Environment Invariants with Global Constants

### Background: the old proof structure

The old proof used two key lemmas for maintaining `env_consistent`:

1. **`anf_cvt_rel_var_lookup`** (eval induction): If `eval rho e (Val v)` and
   conversion gives result `x` with `vn[i] = x`, then `rho[i] = Some v`.
2. **`env_consistent_extend`** (trivial 4-line proof): Given `env_consistent vn rho`
   and the condition from (1), extend to `env_consistent (x::vn) (v::rho)`.

In the old proof, `anf_cvt_rel_var_lookup` worked because:
- **Rel**: `v = rho[n]` (lookup from local env), `x = vn[n]`. `env_consistent`
  connects `rho[i]` to `rho[n]`. Direct.
- **All others**: `x ∈ S` (fresh), contradicts `Disjoint (FromList vn) S`. Vacuous.
- **LetIn**: IH_b gives the condition for `env_consistent_extend`. IH_body with
  extended `env_consistent` gives the result.

### The problem with `tConst`

With `tConst k`, the ANF conversion result is `x = lookup_const cmap k ∈ cmap_vars`.
This is neither in `FromList vn` nor in `S`. The eval gives `v` from
`eval [] body_k (Val v)` — computed from the global body in the EMPTY env,
NOT looked up from the local env `rho`.

In `anf_cvt_rel_var_lookup`, the Const case needs `rho[i] = Some v` when
`vn[i] = x`. But `v` comes from outside `rho`, so `env_consistent` (which
relates values WITHIN `rho`) can't connect `v` to `rho[i]`. We need
`eval [] body_k (Val rho[i])` to apply `eval_val_det`, but nothing provides it.

**Analogy:** `tRel n` is a lookup from the LOCAL env → `env_consistent` handles it.
`tConst k` is a lookup from the GLOBAL env → needs a parallel invariant.

### The solution: `cmap_consistent`

Add an invariant tracking provenance for global constant values in `rho`:

```coq
Definition cmap_consistent vn rho :=
  forall i k decl body v_i,
    nth_error vn i = Some (lookup_const cmap k) ->
    nth_error rho i = Some v_i ->
    declared_constant Σ k decl ->
    decl.(cst_body) = Some body ->
    exists f t, src_eval [] body (Val v_i) f t.
```

"If position `i` in `vn` holds a cmap variable for constant `k`, then `rho[i]`
is the result of evaluating `k`'s body."

**How `anf_cvt_rel_var_lookup` uses it (Const case):**
`cmap_consistent` provides `eval [] body_k (Val rho[i])`. Combined with
`eval [] body_k (Val v)` (from current eval) and `eval_val_det`: `rho[i] = v`. Done.

**Why `cmap_consistent` is maintainable** (needs careful verification):
- **Top level**: `vn` has no cmap vars → vacuous.
- **LetIn + tConst k**: position 0 gets `eval [] body_k (Val v)` directly.
- **LetIn + tRel n**: value is `rho[n]`. If `vn[n] ∈ cmap_vars`,
  `cmap_consistent` at position `n` gives the eval. Inherited.
- **LetIn + fresh (x ∈ S)**: `x ∉ cmap_vars` (by `Disjoint cmap_vars S`). Vacuous.
- **LetIn body**: existing positions shift by 1, same values.

### Proof structure

Follow the old proof's decomposition. The current `env_consistent_extend` (proved
by `eval_env_fuel_ind'`) should be REPLACED with this cleaner structure:

1. **`anf_cvt_rel_var_lookup`** (eval induction) — the key lemma. Uses BOTH
   `env_consistent` AND `cmap_consistent`. Rel case uses `env_consistent`.
   Const case uses `cmap_consistent` + `eval_val_det`. LetIn case uses IH.
   See old proof at line ~2069 for reference.

2. **`env_consistent_extend`** — trivial 4-line lemma (same as old proof, line ~822).
   Takes the `forall k, vn[k] = x -> rho[k] = Some v` condition from (1).

3. **`cmap_consistent_extend`** — analogous to (2) for the cmap invariant.
   Needs eval inversion for tConst to extract `eval [] body (Val v)`.

`anf_cvt_rel_var_lookup` is also used in the old proof for:
- **`anf_cvt_rel_exps_var_lookup`** (line ~2247): variant for expression lists
  (constructor arguments in eval_many).
- **`anf_cvt_result_in_vnames_eval`** (line ~2436): connecting eval result to
  ANF env value when x ∈ FromList vn. Used in the env bridging (`y = x1` case).

**CRITICAL: Before implementing, verify end-to-end that:**
- `cmap_consistent` is provable at the initial call site of `anf_cvt_correct`
- `cmap_consistent` is preserved through ALL induction cases
- The LetIn case of `anf_cvt_correct` can provide both invariants to IH calls
- No new circularity is introduced

## What's Done

### Proved induction cases of `anf_cvt_correct` (12 of 21)
- `eval_Rel_fuel`, `eval_Lam_fuel`, `eval_Fix_fuel`, `eval_Box_fuel`
- `eval_OOT`, `eval_step`
- All 6 OOT step cases
- `eval_many_nil`

### `eval_LetIn_step` case
Structurally complete with full IH chaining (`preord_exp_trans` + `preord_exp_refl`
+ `env_consistent_weaken`). Zero inline admits. Depends on admitted helper lemmas.
This case serves as the TEMPLATE for all other terminating step cases.

### Proved helper lemmas (Qed)
- `anf_cvt_result_in_consumed` — 3-way disjunction for conversion result origin
- `wellformed_tLetIn` — wellformed inversion for tLetIn
- `anf_env_rel_set` — env relation through M.set
- `anf_env_rel_length` — Forall2 length preservation
- `Forall2_nth_error_l`, `Forall2_nth_error_r` — list indexing through Forall2
- `env_consistent_extend_fresh` — extension when x ∉ FromList vn
- `env_consistent_weaken` — projecting out intermediate binding
- `anf_cvt_rel_mfix_to_fix_rel` — mfix to fix relation conversion
- Reduction lemmas: `preord_exp_Efun_red`, `preord_exp_Econstr_red`, `preord_exp_Eproj_red`

### `cmap_consistent` + `anf_cvt_rel_var_lookup` decomposition (DONE)
The `cmap_consistent` invariant has been introduced and the proof restructured
following the old proof's decomposition:
- **`cmap_consistent`** — definition tracking global constant provenance in `rho`
- **`env_consistent_extend`** — trivial 4-line lemma (Qed)
- **`cmap_consistent_extend`** — trivial analog (Qed)
- **`anf_cvt_rel_var_lookup`** — key lemma by eval induction, all 12 cases proved (Qed).
  Uses `env_consistent` for Rel, `cmap_consistent` + `eval_val_det` for Const.
- **`env_consistent_extend_from_cvt`** — combines var_lookup + extend (Qed)
- **`cmap_consistent_extend_from_cvt`** — uses var_lookup + result_cmap + tConst_inv (Qed)
- Correctness predicates updated to carry `cmap_consistent` hypothesis
- LetIn case of `anf_cvt_correct` updated to pass both invariants to IH calls

## Admitted Helper Lemmas (Verify them very carefully)

1. **`eval_val_det`** — Value determinism. Standard, provable by mutual induction.
2. **`eval_preserves_wf`** — Eval preserves well-formedness. Standard.
3. **`anf_cvt_disjoint_occurs_free_ctx`** — Free variables of context application
   avoid consumed variables. Structural, independent of env invariant issue.
4. **`anf_cvt_result_cmap`** — Conversion inversion for cmap results.
5. **`eval_tConst_inv`** — Eval inversion for tConst.
6. **`anf_val_rel_exists`** (in `anf_corresp.v`) — Target value existence.

## Remaining Step Cases

Not yet written: App, FixApp, Construct, Case, Proj, Const, eval_many_cons.
All follow the LetIn template (IH chaining with `preord_exp_trans`).

## Technical Notes (Coq-specific)

### Conversion inversion hangs
`inv`/`inversion` on `anf_cvt_rel` (large mutual inductive) causes Coq to hang
(54+ minutes). Use:
```coq
remember (EAst.tXxx arg1 arg2) as e_x.
destruct Hcvt; try discriminate.
injection Heqe_x as <- <-.
```
Works for most constructors. For tConstruct/tCase, `destruct` may fail —
use `intros` first. IMPORTANT: `injection ... as <- <-` may clear hypotheses.
Save critical hypotheses with `rename` or `pose proof` before injection.

### `eval_env_fuel_ind'` goal ordering
After `try (intros; exact I)` consumes OOT/True cases, remaining goals are:
P_step terminating (7): App, FixApp, LetIn, Construct, Case, Proj, Const.
P_fuel Val (4): Rel, Lam, Fix, Box.
P_fuel other (2): OOT, eval_step.
Use explicit `-` bullets. Do NOT use goal selectors — numbering shifts.

### Resource instance ambiguity
Both `LambdaBox_resource_fuel` and `LambdaBox_resource_trace` are
`@LambdaBox_resource nat`. All shorthands use explicit `@` with both instances.

### Key tactic patterns
- `preord_exp_trans`: `eapply preord_exp_trans; [tci | exact eq_fuel_idemp | | ]`
- `preord_exp_post_monotonic`: `eapply (preord_exp_post_monotonic cenv _ eq_fuel)`
- `anf_cvt_val_alpha_equiv`: needs 15+ explicit parameters (see code)
- `Setminus` is Inductive: use bare `destruct`, not `as [? ?]`
- `FromList` is `fun x => List.In x l`: use `unfold FromList, Ensembles.In`
- `Disjoint` is Inductive: after `constructor; intros z Hz; destruct Hz`
- Nested `[A|[B|C]]` fails in `try solve`: use chained `destruct`

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
`anf_util.v` does NOT depend on `anf_corresp.v` (dependency removed;
`term_ind_fix_body` moved to `common.v`).

## Old Proof Reference
`LambdaANF/LambdaBoxLocal_to_LambdaANF_anf_correct.v` — key lemmas to study:
- `anf_cvt_rel_var_lookup` (line ~2069): the key invariant lemma
- `env_consistent_extend` (line ~822): the trivial extension
- `env_consistent_extend_from_cvt` (line ~2231): combines the two
- The LetIn step case (line ~3515): template for IH chaining
