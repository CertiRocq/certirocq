# Correctness of the LambdaANF → LLVM (Vellvm VIR) backend

This branch builds on CertiRocq PR #155 (`vir-llvm-backend`), which adds a
LambdaANF → LLVM backend emitting Vellvm's VIR AST. The correctness theorem
shipped with that PR rests on an axiom `refinement_runs` that states the
result, and on an abstract `Eval_to` unrelated to Vellvm's semantics. This
branch replaces it with a statement against Vellvm's executable semantics
and proves it: `LambdaANF_to_LLVM_correct` in
`theories/CodegenLLVM/LLVM_sim_exp.v` is closed (Qed) and depends only on
standard-library axioms.

## The theorem

The statement is `LambdaANF_to_LLVM_correct_statement : Prop` in
`theories/CodegenLLVM/LambdaANF_to_LLVM_statement.v`. `LLVM_toplevel_link.v`
proves `main_correct_of_sim : sim_exp_statement -> LambdaANF_to_LLVM_correct_statement`,
where `sim_exp_statement` is the explicit statement of the main simulation
lemma `sim_exp`. `LLVM_sim_exp.v` proves `sim_exp` by induction on `bstep_e`
from the cases in `LLVM_sim_cases_*.v` (`sim_exp_proof : sim_exp_statement`)
and states

    Theorem LambdaANF_to_LLVM_correct : LambdaANF_to_LLVM_correct_statement.
    Proof. exact (LLVM_toplevel_link.main_correct_of_sim sim_exp_proof). Qed.

`Print Assumptions LambdaANF_to_LLVM_correct` (Rocq 9.1) lists only
standard-library axioms and primitive types: `Classical_Prop.classic`,
`functional_extensionality_dep`, `proof_irrelevance`,
`Eqdep.Eq_rect_eq.eq_rect_eq`, `ClassicalDedekindReals.sig_forall_dec`,
`ClassicalDedekindReals.sig_not_dec`, and the primitives `PrimInt63.int`,
`PrimInt63.lsr`, `PrimInt63.land`, `PrimInt63.eqb`, `PrimFloat.float`,
`PrimString.string` (verbatim output at the end of `LLVM_sim_exp.v`). None
of the `CodegenLLVM` files in `_CoqProject` contains `Admitted` or `Axiom`,
and no section hypothesis remains in the theorem.

## The statement

- **Program.** The code the pipeline emits, `flatten_prog (compile_prog …)`, is
  linked with a runtime prelude, converted (`convert_types`), and run with
  Vellvm's `interp_mcfg`. The memory model is Vellvm's concrete model with
  64-bit finite pointers (`ParamsV IP64Bit`).
- **Conclusion.** Either the run ends in out-of-memory, or it returns
  (`eutt Ret`) a word that represents the source value in the final memory.
  The representation follows the C runtime's ABI from `values.h`; a boxed
  object's pointer is word-aligned (the emitted code tells boxed from
  unboxed values by the low bit).
- **Hypotheses.**
  - The runtime: the garbage collector and the `thread_info` set-up, which
    are linked as Vellvm library functions. Their specification
    (`runtime_correct`) is concrete. The runtime chooses a heap invariant
    `heap_inv`. A runtime state is well-formed (`rt_ok st tinfo fp rs`) when
    `heap_inv` holds, `thread_info` is well-formed (`tinfo_ok`: its fields
    are writable heap words, and the nursery `[alloc, limit)` is a writable
    heap region with both ends word-aligned), the memory is well-formed
    (`mem_ok_stmt`: heap addresses are allocated, stack-frame addresses are
    not heap addresses), the nursery does not overlap `thread_info`, and
    `fp` heads a shadow stack with root slots `rs`. `runtime_correct` has
    three clauses:
    1. `make_tinfo` runs out of memory, or returns a `thread_info` pointer
       in a well-formed state with an empty shadow stack (`fp = 0`), and
       `thread_info` (8232 bytes) fits in the 64-bit address space.
    2. Everything the generated code does to the heap preserves `heap_inv`:
       writing the nursery and the `alloc`/`fp`/`nalloc` fields, moving
       `alloc` forward within the nursery, word-aligned.
    3. The collector, called in a well-formed state whose roots represent
       values `vs`, with a request for `nalloc` words, `0 <= nalloc < 2^61`
       (the stored 64-bit word only determines `nalloc` modulo 2^64; the
       emitted code requests small constants), runs out of memory or
       returns with the state well-formed again (same `fp`, same root
       slots), the roots representing the same `vs`, `nalloc` words of
       room, and the memory frames unchanged (locals and globals are
       untouched by the signature). Moreover, outside the heap it only
       writes the root slots (a copying collector updates the roots and
       nothing else on the stack), every newly created heap address was
       unallocated before (new to-spaces are fresh `malloc`'d blocks), and
       the root slots keep their Vellvm allocation ids (the collector
       overwrites them in place; the generated code reloads them through the
       pointer it `alloca`'d). The collector may free heap blocks (a copying
       collector frees its from-space): nothing is said about the allocation
       ids of heap bytes.
  - The source program `Efun fds main` must satisfy
    `llvm_restricted cenv fds main`. `fds` and `main` are `body_ok`: no
    nested `Efun`, no `Eprim`, only integer primitive values; constructor
    tags are in `cenv` with ordinal below 251 and matching arity; every
    projection index is below the constructor's arity (`BO_proj`); every
    allocation chunk, the words requested by one limit check, is below 2^64
    bytes, as the limit check computes `8 * chunk_words` in 64-bit
    arithmetic. The program is closed with unique bindings, and `cenv_ok`
    holds: two distinct constructors of one inductive with the same ordinal
    are one nullary and one boxed. This matches the numbering of
    `LambdaBox_to_LambdaANF.common.convert_cnstrs`, which numbers nullary and
    boxed constructors with two counters both starting at 0, so that `O` and
    `S` share ordinal 0. The Wasm backend's `cenv_restricted` (in
    `toplevel_theorem.v`) forbids a boxed constructor from sharing its
    ordinal with any other constructor, which this numbering violates for
    every inductive with both kinds (`nat`, `list`, `option`).
    `LLVM_nonvacuity.nat_cenv_ok` shows that `cenv_ok` holds for a
    `nat`-shaped environment.
- **Not covered.** Divergence (the theorem is about terminating source
  runs), the printed `.ll` text (`Serialize.v` is outside the proof), clang,
  and the C runtime itself, which is related to `runtime_correct` only by
  the dynamic checks below.

## Runtime contract checking (dynamic)

`tests/llvm/` runs compiled programs end to end against the real C runtime
(`CertiRocq Compile LLVM`, a C driver printing the result as an
S-expression, compared with Rocq's `vm_compute`), also under ASan/UBSan.
`tests/llvm-corpus/` adds GC-stressing programs and
`runtime/gc_stack_checked.c`, a wrapper around the real collector that
asserts the clauses of `runtime_correct` at every collection
(`tests/llvm-corpus/CONTRACT.md` maps clauses to checks). Findings:

- Boxed constructor ordinals whose low byte is >= 251 are never scanned by
  the collector (`No_scan_tag`); `tag_ok` requires ordinals < 251, so such
  programs are outside `llvm_restricted`. The C backend has the same latent
  assumption.
- A single allocation chunk larger than the nursery (2^16 words) makes the
  runtime `exit(1)` ("Nursery is too small"), which is neither `room` nor
  `ends_in_oom`. Open: bound `chunk_words` by the nursery size in
  `llvm_restricted` (ties the statement to a runtime constant), split
  chunks in the emitter, or let the runtime grow the nursery.
- Tail calls are not eliminated by the emitter, so tail-recursive loops use
  machine stack proportional to their length; the harness runs programs on
  a large thread stack. The Vellvm semantics has an unbounded stack.
- `prim_int63.c` compared tagged words signed in `ltb`/`leb` (Rocq's are
  unsigned), so `max_int <? max_int + 1` was true (corpus c12). Fixed in
  `runtime/prim_int63.c`; the C backend links the same code.
- Allocating PrimInt63 primitives (`addc`, `mulc`, ...) call the collector
  from C without the caller's live values registered as roots (corpus c13,
  wrong result). This is outside the theorem (`body_ok` excludes `Eprim`);
  the emitter needs a safepoint around allocating primitives before such
  programs can be covered.

`tests/llvm/RESULTS.md` records the results, obtained on an unpublished
development branch and not reproduced on this one: the 9 end-to-end tests
pass in all 7 modes (plain, forced final GC, ASan+UBSan, -O2,
contract-checked, ASan+checked, checked with a 2^13-word nursery), with up
to 1343 collections per run; 14 of the 17 corpus programs pass in all
modes; the three failures are the two runtime gaps above (c07, c15) and the
out-of-theorem c13. ASan and UBSan report nothing.

## Non-vacuity

`theories/CodegenLLVM/LLVM_nonvacuity.v` and
`theories/CodegenLLVM/LLVM_nonvacuity_run.v`. The conclusion of the theorem is
"out of memory, or returns a word representing the value", so the theorem is
trivially true whenever the run is guaranteed to run out of memory, and
vacuous when its hypotheses cannot hold. The hypotheses that matter:

- `runtime_correct`, first clause. It allows `make_tinfo` to run out of
  memory. A `make_tinfo` that always does satisfies `runtime_correct` and
  makes every instance of the conclusion true through its OOM disjunct
  (`oom_runtime_correct`, `oom_runtime_vacuous`). The theorem is only
  informative for runtimes taking the `returns` branch. The witness
  `nv_make_tinfo` does: it `malloc`s (Vellvm's `malloc` intrinsic) a
  16432-byte block at address 0, places `thread_info` at address 8 and a
  1024-word nursery at 8240..16432, and stores `alloc`, `limit` and a null
  `fp`. `nv_make_tinfo_returns` proves the whole `returns` branch:
  `tinfo_ok`, empty shadow stack, `mem_ok_stmt`,
  `nursery_tinfo_disjoint_stmt` and the address bound.
  `nv_make_tinfo_not_oom` proves that it does not run out of memory.
- `runtime_correct`, second clause (`heap_inv` preserved by the mutator).
  It is met by `heap_inv := True`; the clause only constrains the runtime's
  own choice of invariant.
- `runtime_correct`, third clause (the collector). OOM is an allowed
  outcome. The witness `nv_gc` always runs out of memory, so with the
  witness runtime the theorem only says something about runs that never
  call the collector: programs that allocate at most 1024 words in total,
  headers included. A returning collector also meets the clause, since the
  request is bounded (so `room st' tinfo nalloc` is satisfiable) and the
  clause allows freeing from-space. `nv_gc_check` is such a collector: it
  loads `alloc`, `limit` and `nalloc` from `thread_info`; if
  `limit - alloc >= 8 * nalloc` (integer addresses, unsigned value of the
  `nalloc` word) it returns `inr DVALUE_None` without touching memory, and
  otherwise it runs out of memory. `nv_gc_check_run` symbolically runs the
  three loads and the comparison (`room` holds because the word read is
  `nalloc` by the bound, and the branch condition gives the inequality),
  and `nv_runtime_correct_check : runtime_correct cenv fds nv_heap_inv
  nv_gc_check nv_make_tinfo` takes `st' = st`, so every frame clause is
  trivial. This is not a model of CertiRocq's collector, which moves objects
  and updates the roots; it shows that the contract admits a collector that
  returns.
- `llvm_restricted` and `bstep_e`. Both hold for
  `Efun Fnil (Econstr x C [] (Ehalt x))` with a one-constructor `cenv`
  (`ex_restricted`, `ex_eval`). `ex_hypotheses` collects all three
  hypotheses for this program and the witness runtime. `ex_correct`
  instantiates `LambdaANF_to_LLVM_correct`: the compiled program runs out
  of memory or returns `1` (the encoding `0 * 2 + 1` of the nullary
  constructor). `LLVM_nonvacuity_run.v` proves that it returns `1`
  (`ex_returns`), so the OOM disjunct does not hold (`ex_not_oom`). The
  proof symbolically runs the whole program in Vellvm's concrete memory
  model (`ex_whole_runs`, for any collector, since the program never calls
  it). The steps are `nv_make_tinfo`, global initialisation (one 8-byte
  `alloca` per declared name), `push_call_frame` (a `mem_push` and a 0-byte
  varargs `alloca`), the single block `%-6 = shl 0, 1; %1 = or %-6, 1;
  ret %1` (a nullary constructor allocates nothing and needs no
  shadow-stack frame), and `pop_call_frame`. In the concrete model an
  allocation only runs out of memory when the next free address plus the
  size reaches `2^64` (`allocate_dtyp_exists`). The proof tracks an upper
  bound on the allocated addresses (`keys_below`; `blk_ok` records that the
  `malloc`'d block is the only allocated memory after `nv_make_tinfo`). The
  bound stays below `16432 + 32`. `G_ok` for the resulting global
  environment comes from the general `global_init`, because a run cannot
  also end in OOM (`truns_not_toom`, `truns_det`).

## Changes to the emitter (relative to PR #155)

- `LambdaANF_to_LLVM.v`: `Ptrtoint`/`Inttoptr` are wrapped in
  `CONV_Impure`, as required by the current Vellvm AST.
- `LambdaANF_to_LLVM.v`, `Flatten.v`: generated local names are disjoint by
  construction. `ntmp` uses `-(4n)`, `ssname` uses `-(4n+1)` with Cantor
  pairing, and `flat_id` uses `-(4n+2)`. Before, they could collide in very
  large functions.

## Files (`theories/CodegenLLVM/`)

| File | Content |
|---|---|
| `LambdaANF_to_LLVM_statement.v` | The statement `LambdaANF_to_LLVM_correct_statement` and its definitions (`run_program`, `runtime_correct`, `rt_ok`, `repr_val`, `llvm_restricted`, `body_ok`, `cenv_ok`); no proofs. `mem_ok_stmt`, `in_frames_stmt`, `frames_ptrs_stmt`, `nursery_tinfo_disjoint_stmt`, `slot_bytes_stmt` are copies of the `LLVM_sim.v` definitions (equivalence proved in `LLVM_toplevel_link.v`) |
| `LLVM_interp_lemmas.v` | Algebra of `interp_mcfg`, memory/local/global event lemmas |
| `LLVM_call_lemmas.v` | Call knot (`interp_mrec`), runtime library calls, OOM propagation |
| `LLVM_convert.v` | `convert_types` on the emitted program |
| `LLVM_exp_lemmas.v` | Integer arithmetic, pointer conversions, GEP, `exp_eval` for every expression form the emitter produces |
| `LLVM_mem_lemmas.v` | Vellvm's concrete memory model: reads, writes, frame lemmas, `alloca`, memory frame push/pop |
| `LLVM_emit_syntax.v` | Shape equations of `translate_cfg`, label/name discipline (`cfg_ok`), `compile_prog` structure |
| `LLVM_emit_facts.v` | Type-conversion equations for the emitter helpers (`store_fields`, `spill_code`, `reload_code`, phis, `call_args`, `header_word`) |
| `LLVM_instr_lemmas.v` | Execution lemmas (`runs`/`oom`) for every instruction, terminator and phi form the emitter produces, including `alloca` (`instr_alloca_*`, `alloc_post`), calls, `run_exc` commutation, function entry/exit (`push_call_frame_cases`, `pop_call_frame_runs`, `denote_function_runs`, OOM variants), and the straight-line helper sequences (`store_fields_run`, `spill_code_run`, `reload_code_run`) |
| `Flatten_sem.v` | Semantic transport of the flattening pass (`Flatten.v`): atomiser soundness, counter threading (`flat_codeP_app`), block structure (`flat_blockP_spec/prepend`), and transfer lemmas for instructions, calls, terminators and block tails, with OOM variants, up to `agree_except` on the fresh `flat_id` names |
| `LLVM_sim.v` | The invariant (`INV`, `env_rel`, `stable_repr`, `stack_ok`, `mem_ok`), the step relation `mstep` and their preservation lemmas (`INV_mstep`, `INV_link`, `INV_gc`, `stable_repr_boxed`, `stable_repr_even`, `env_rel_bind`, ...); the frame condition `keeps_stack`; the result of a function activation `sim_result`; the simulation statement `sim_stmt` |
| `LLVM_toplevel_link.v` | From Vellvm's top level (`run_program`: runtime set-up, `build_global_environment`, the `denote_mcfg` call knot, `@certirocq_main`) to `LLVM_sim`'s section hypotheses: global initialisation (`alloc_decls_spec`), the knot (`ctx_real_fun`, `ctx_real_gc`), the entry invariant (`INV0`), the activation of `@certirocq_main` (`main_activation`); `runtime_extra_of_correct` derives `LLVM_sim`'s runtime hypotheses from `runtime_correct`; `sim_exp_statement` and `main_correct_of_sim` |
| `LLVM_sim_cases_read.v` | The `Ehalt`, `Eproj`, `Eprim_val` and `Ecase` cases (`sim_case_halt/proj/prim_val/case`); `env_restrict` and the restriction lemmas used to pass `env_ok` to a continuation with fewer live variables |
| `LLVM_sim_cases_constr.v` | The `Econstr` case (`sim_case_constr`: nullary, chunk member, chunk head with limit check, allocation fast path and the spill/`garbage_collect`/reload path) |
| `LLVM_sim_cases_call.v` | The `Efun` (vacuous under `body_ok`), `Eapp` and `Eletapp` cases, proved for the variant `sim_stmt_fr` with the weaker environment premise `env_ok2` (`env_ok` is not preserved by safepoints) and bridged to `sim_stmt` by `sim_stmt_fr_of_sim_stmt` |
| `LLVM_sim_exp.v` | `sim_exp` by induction on `bstep_e` (`Eprim` is vacuous by `body_ok`), `sim_exp_proof`, and the theorem `LambdaANF_to_LLVM_correct` |
| `LLVM_nonvacuity.v` | The witness runtime and `nv_runtime_correct`, the returning collector `nv_gc_check` and `nv_runtime_correct_check`, the example program (`ex_hypotheses`, `ex_correct`), and the vacuous OOM instance (`oom_runtime_correct`, `oom_runtime_vacuous`) |
| `LLVM_nonvacuity_run.v` | Symbolic run of the compiled example program (`ex_whole_runs`, `ex_returns`, `ex_not_oom`) |

PR #155's earlier proof files (`MemoryLaws.v`,
`LambdaANF_to_LLVM_correct_v3.v`, `Construct_lemmas.v`, `Flatten_correct.v`,
`Instantiate_compile.v`), which were vacuous and did not build against the
current Vellvm, are removed. `theories/CodegenLLVM/LLIR/` (with its own
`_CoqProject`) is not in the build.

## Architecture of the proof

The main lemma (`sim_exp`, statement `LLVM_toplevel_link.sim_exp_statement`,
simulation relation `LLVM_sim.sim_stmt`) is proved by induction on the
source big-step relation `bstep_e`. It symbolically executes the code the
pipeline emits: the flattened, type-converted blocks
`flat_blockP (cblock b) c`, under `interp_mcfg (interp_mrec ctx _)` where
`ctx` is Vellvm's call knot. There is no separate (coinductive) simulation
between the flattened and unflattened programs through the call knot:
flattening is transported segment by segment inside the induction
(`Flatten_sem.v` proves that the flattening of a call-free code segment
behaves like the original up to the extra `flat_id` locals; a call
instruction is handled directly after evaluating its atomised operands).

The lemma speaks about the tail of the entry block of `translate_cfg e`
(its code and terminator, continued in the enclosing function's CFG `B`), and
assumes only that the other blocks of the translation are in `B` in flattened
form. This makes `prepend_code` (straight-line constructs consing code onto
the continuation's entry block) compositional: the caller of the induction
hypothesis has already executed the prefix.

The invariant threaded through the induction (`LLVM_sim.v`):

- `INV st fp rs vs`: the runtime's heap invariant, a well-formed
  `thread_info`, memory well-formedness, the current shadow-stack frame `fp`
  with root slots `rs` representing `vs`, and the fact that shadow-stack frames
  and slots live in (allocated, non-heap) stack memory;
- `env_rel S rho env sf st`: every live source variable in `S` is either a
  top-level function (a global) or held in the local `env x` as a word that
  stably represents its value (`stable_repr`: the representation survives
  any later change of the nursery and of `thread_info`);
- `room st tinfo chunk`: the chunk head's limit check covers the
  allocations of the chunk members.

Calls (`Eapp`, `Eletapp`) use the induction hypothesis for the callee's body,
wrapped in Vellvm's `push_call_frame`/`pop_call_frame`. The result of a
function activation (`sim_result`) is "out of memory, or a word stably
representing the value, with `INV` re-established, the memory frames only
extended by addresses that were not allocated stack memory before, and the
caller's stack kept (`keeps_stack`: allocated non-heap bytes stay allocated
and non-heap, keep their contents outside the root slots, and keep their
allocation ids)". After a collection the generated code reloads the roots
through the root array it `alloca`'d; these reads hit root-slot bytes, whose
allocation ids the collector clause of `runtime_correct` preserves.

## Open points

- Non-vacuity for programs that call the collector, end to end: the
  returning collector `nv_gc_check` exists, but no example program that
  calls the collector has been run to its result.
- Allocation chunks larger than the nursery, and allocating primitives
  (see the findings above).
- The plugins, extraction and benchmarks have not been built on this
  branch.

## Building

### Dependencies

`rocq-certirocq.opam` lists the dependencies, Vellvm included. The LLVM
backend needs Vellvm's current AST (`Ptrtoint`/`Inttoptr` are
`CONV_Impure`), and the proof needs `Semantics/TopLevel.v` and
`Theory/I2F/*`; no Vellvm release contains all of these (the latest,
`3.0.20260707`, predates `CONV_Impure`). The opam file therefore pins
`rocq-vellvm` to commit `b63a28a0` (`3.0.20260707-147-gb63a28a0`) with
`pin-depends`; the `vellvm/` submodule and the Nix overlay
`.nix/coq-overlays/vellvm` name the same commit. Once Vellvm tags a release
that includes it, the three are to be replaced by a version constraint.

```sh
opam pin add -n -y rocq-certirocq .    # also pins rocq-vellvm (pin-depends)
opam install --deps-only rocq-certirocq
```

Vellvm's opam file requires `coq-ext-lib < 0.14`. In a switch whose ext-lib
is newer (for instance `dev`), changing ext-lib would force a rebuild of the
packages depending on it; Vellvm builds against ext-lib `dev` as well, and
can then be installed from the submodule instead:

```sh
git submodule update --init vellvm
make -C vellvm/src rocq      # the Rocq library only; no extraction/executable
make -C vellvm/src install   # installs Vellvm into the current switch
```

`make install` writes to the switch whose `rocq` ran `rocq makefile`; do not
reuse a `RocqMakefile.conf` across switches.

The proof files have been built with Rocq 9.1.0 and 9.1.1, MetaRocq
1.5.1+9.1, CompCert 3.17, Equations 1.3.1+9.1, coq-ext-lib `dev` and 0.13.1,
coq-paco 4.2.3, coq-itree 5.2.1, and Vellvm `b63a28a0`.

### CertiRocq theories, up to the LLVM backend and its proof

```sh
make theories/Makefile libraries/Makefile
make -C libraries
make -C theories CodegenLLVM/LLVM_sim_exp.vo CodegenLLVM/LLVM_nonvacuity_run.vo
```

`Compiler/pipeline.v` requires `CodegenLLVM/toplevel.v`, so every build of
the compiler needs Vellvm. The longest file, `LLVM_nonvacuity.v`, takes
about 20 minutes and 2 GB of memory.
