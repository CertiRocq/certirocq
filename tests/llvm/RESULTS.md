# LLVM backend: results of the end-to-end harness

Run on 2026-10-07/08 on an unpublished development branch (`llvm-tests-run`,
based on commit 3fcdab0d), in a Rocq 9.1 switch, with clang on x86-64 Linux
(glibc). They have not been reproduced on this branch. The commands were:

    ./run.sh -m plain -m final-gc -m asan -m O2                 # the 9 tests
    TIMEOUT=3600 ./run.sh -m checked -m asan-checked -m checked-small
    TIMEOUT=3600 ./run.sh -c -m checked -m asan -m asan-checked -m checked-small
    ./run.sh -m checked -m asan -m asan-checked -m checked-small -m final-gc c12

Modes (see `run.sh`): `checked` links `runtime/gc_stack_checked.c` (the
contract checker, `../llvm-corpus/CONTRACT.md`) instead of `gc_stack.c`;
`asan` is `-fsanitize=address,undefined` with the real `gc_stack.c`;
`asan-checked` is both; `checked-small` is `checked` with a 2^13-word nursery
instead of 2^16 (`-DCERTIROCQ_LOG_NURSERY_SIZE=13`), so about 8x as many
collections. In the checked modes, corpus programs run with
`CERTIROCQ_CHECK_MIN_GC=1`, except c00, c06 and c12, which allocate less than
one nursery. Every run uses llvm_main.c's 4 GiB pthread stack.

Numbers are the GC counts (`gc_calls`, the same in every mode with a 2^16
nursery). `XFAIL` means the failure was predicted by the corpus author.

## The 9 tests in `tests/llvm/`

| test | plain | final-gc | asan | O2 | checked | asan-checked | checked-small (2^13) |
|---|---|---|---|---|---|---|---|
| gc_length   | ok 167 | ok 168 | ok 167 | ok 167 | ok 167 | ok 167 | ok 1343 |
| gc_map      | ok 52  | ok 53  | ok 52  | ok 52  | ok 52  | ok 52  | ok 423  |
| letapp_live | ok 20  | ok 21  | ok 20  | ok 20  | ok 20  | ok 20  | ok 166  |
| list10      | ok 0   | ok 1   | ok 0   | ok 0   | ok 0   | ok 0   | ok 0    |
| match_arms  | ok 0   | ok 1   | ok 0   | ok 0   | ok 0   | ok 0   | ok 0    |
| mutual      | ok 0   | ok 1   | ok 0   | ok 0   | ok 0   | ok 0   | ok 0    |
| nullary     | ok 0   | ok 1   | ok 0   | ok 0   | ok 0   | ok 0   | ok 0    |
| peano       | ok 0   | ok 1   | ok 0   | ok 0   | ok 0   | ok 0   | ok 0    |
| sum_list    | ok 0   | ok 1   | ok 0   | ok 0   | ok 0   | ok 0   | ok 0    |

There were no contract violations. A checked run of gc_length takes about
55 s (with 2^16) and 7 min (with 2^13), because the checker hashes the whole
reachable heap at every collection.

## The corpus `tests/llvm-corpus/cNN_*.v`

| program | plain | checked | asan | asan-checked | checked-small (2^13) |
|---|---|---|---|---|---|
| c00_sanity             | ok 0 | ok 0 | ok 0 | ok 0 | ok 0 |
| c01_gc_tree            | ok 48 | ok 48 | ok 48 | ok 48 | ok 384 |
| c02_gc_long_list       | ok 45 | ok 45 | ok 45 | ok 45 | ok 366 |
| c03_deep_nontail       | ok 10 | ok 10 | ok 10 | ok 10 | ok 85 |
| c04_big_ctor           | ok 10 | ok 10 | ok 10 | ok 10 | ok 81 |
| c05_many_live          | ok 468 | ok 468 | ok 468 | ok 468 | ok 3751 |
| c06_mixed_ctors        | ok 0 | ok 0 | ok 0 | ok 0 | ok 0 |
| c07_ord_ge_251         | MISMATCH (XFAIL) | VIOLATION `roots_ok / not_object` POST, GC #1 (XFAIL) | MISMATCH, 27 GCs (XFAIL) | VIOLATION, same, GC #1 (XFAIL) | VIOLATION, same, GC #1 (XFAIL) |
| c08_nested_match       | ok 4 | ok 4 | ok 4 | ok 4 | ok 34 |
| c09_mutual             | ok 16 | ok 16 | ok 16 | ok 16 | ok 130 |
| c10_closures           | ok 7 | ok 7 | ok 7 | ok 7 | ok 56 |
| c11_letapp_chains      | ok 11 | ok 11 | ok 11 | ok 11 | ok 88 |
| c12_primint63          | MISMATCH, 0 GCs | MISMATCH | MISMATCH | MISMATCH | MISMATCH |
| c13_primint63_alloc    | MISMATCH, 14 GCs (XFAIL) | MISMATCH, 14 GCs, checker OK (XFAIL) | MISMATCH (XFAIL) | MISMATCH, checker OK (XFAIL) | MISMATCH, 110 GCs, checker OK (XFAIL) |
| c14_chunk_large        | ok 3 | ok 3 | ok 3 | ok 3 | ok 39 |
| c15_chunk_over_nursery | ABORT "Nursery is too small" (XFAIL) | VIOLATION `room` POST, GC #1 (XFAIL) | ABORT, same (XFAIL) | VIOLATION, same (XFAIL) | VIOLATION, same (XFAIL) |
| c16_sharing            | ok 68 | ok 68 | ok 68 | ok 68 | ok 549 |

There were no ASan or UBSan reports, crashes or timeouts in any mode. The
whole corpus in all four modes takes about 10 min.

### Verbatim messages

c07, `checked` (the `asan-checked` and `checked-small` messages are the same
apart from the addresses):

    certirocq-contract: VIOLATION [roots_ok / not_object (object outside the nursery [alloc,limit) and allocated)] POST (gc call #1): field of a reachable object whose tag byte (ord & 0xFF) is >= No_scan_tag = 251; gc_stack.c does not scan the fields of such objects although tag_ok allows ord < 1024: object [0x7fdcedf84e80,0x7fdcedf84e98) (header 0x800) is not in the allocated part [0x7fdcedf7f010,0x7fdcedf7f010) of space 0 (dangling pointer, or object inside the free nursery [alloc,limit))

c07 output without the checker (`plain`, `asan`): `(C0 (C0 (C0 0 0) 1) 1)`.
Expected: `(C0 (C0 (C0 5 1) 1) 1)`.

c15, `checked` and `asan-checked`:

    certirocq-contract: VIOLATION [room (gc_stack.c cannot provide nalloc words: nursery too small; it would exit(1), which is neither room nor ends_in_oom)] POST (gc call #1): nalloc = 66000 words > nursery capacity 65536 words

(`checked-small`: `... > nursery capacity 8192 words`). Without the checker,
`gc_stack.c` prints `Nursery is too small for function's num_allocs` and
exits with status 1.

c13 output: `(C0 (C0 3 6148914691236512290) 0)` with a 2^16 nursery, and
`(C0 (C0 2 6148914691236516864) 0)` with 2^13. Expected:
`(C0 (C0 1 9223372036854675808) 2)`. The checker summary is
`certirocq-contract: OK gc_calls=14 ...`.

c12 output: the same as expected except the last element, which is 1
instead of 0:

    expected ... (C0 1 (C0 1 (C0 0 0)))))))))))))))))))
    got      ... (C0 1 (C0 1 (C0 1 0)))))))))))))))))))

## Interpretation

- **c07: predicted failure; a runtime bug against the contract.** The clause
  is `roots_ok`, checked as a POST conclusion of the collector clause
  (clause 3). This is CONTRACT.md "Places where gc_stack.c does not meet the
  contract", item 1. `tag_ok` allows boxed ordinals below 1024, but
  `gc_stack.c` reads the tag as `hd & 0xFF`, and `do_scan` skips the fields
  of objects with tag ≥ `No_scan_tag` = 251. The first collection therefore
  leaves a field of an ordinal-251/255 object pointing into the evacuated
  nursery. The checker catches this at GC #1. Without the checker the
  dangling field is read after the nursery has been reused, and the result is
  wrong (`(C0 (C0 (C0 0 0) 1) 1)`) without any crash. ASan cannot see it
  because the nursery is one live malloc block. Neither the emitter nor the
  driver is at fault.
- **c15: predicted failure; the runtime does not provide `room`.** This is
  the collector clause's `room` / `ends_in_oom` disjunction, CONTRACT.md
  item 2. The program needs one 66000-word allocation chunk, but
  `gc_stack.c` never grows its 65536-word nursery and `exit(1)`s in
  `resume()`. The checker reports this before calling the collector. The fix
  is in the runtime, or in tightening `llvm_restricted` so that the emitter
  splits chunks.
- **c13: predicted failure; outside the theorem (`Eprim`).** No violation is
  reported, but the result is wrong, and it depends on the nursery size. I
  confirmed in gdb that `prim_int63_addc` → `mk_C0` →
  `prim_int63_alloc_make_..._carry_C0` calls `garbage_collect` itself
  (`prim_int63.c:217`). At that point the emitted caller's live list `keep`
  is held only in an SSA register, not in a shadow-stack root slot, so the
  collector moves the list without updating the caller's pointer. The
  checker cannot see this: it checks only registered roots, and those are
  consistent. This is an emitter limitation, already noted at `Eprim` in
  `LambdaANF_to_LLVM.v`: it needs a safepoint (spill/reload of live
  variables) around allocating primitives.
- **c12: not predicted; a runtime bug in `prim_int63.c` (outside the
  theorem).** The emitter, the driver and the expected value are correct. The
  last element is `if max <? max + 1 then 1 else 0`. `max + 1` wraps to 0, so
  Rocq gives `false` and the element is 0. In gdb, `prim_int63_ltb` receives
  `x = 0xffffffffffffffff` (tagged `max`) and `y = 0x1` (tagged 0) and returns
  3 (`true`). The reason is that `primint` is `value` = `intnat`, which is
  signed, so `prim_int63_ltb` (`x < y`) and `prim_int63_leb` (`x <= y`)
  compare tagged words *signed*, while `Uint63.ltb`/`leb` are unsigned. They
  give wrong answers whenever exactly one operand is ≥ 2^62. The fix is to
  compare `(uintnat)x < (uintnat)y`. The C backend links the same
  `prim_int63.c`, so it has the same bug. All the other 18 primitive results
  in c12, including wrap-around, division by zero and shifts ≥ 63, are
  correct.
- Everything else passes in every mode, including under the contract
  checker, with ASan/UBSan, and with an 8x denser GC schedule. In total the
  checker covered about 6900 collections of the GC-using corpus programs,
  with deep root checks, stack-window checks and old-generation hashes.

## Conventions reconciled (driver vs. corpus `EXPECTED:` lines)

- Boxed values print as `(C<ord> fields…)` and unboxed values as `n` in both
  conventions. Tuples nest to the left in both.
- **bool**: the corpus README said `true` = 0, `false` = 1. This is wrong
  for this pipeline. The plugin's `Loader.v` registers
  `CertiRocq Extract Inductives [ bool => "bool" [ 1 0 ] ]`, which renumbers
  the ordinals, so `true` = 1 and `false` = 0. `SExp.v`, `mutual.v` and
  `prim_int63.c`'s `mk_bool` (true → word 3) agree on this. I fixed the
  `EXPECTED:` lines of c00 (`0` → `1`), c02 (`(C0 4 0)` → `(C0 4 1)`) and c09
  (`… 1) 0)` → `… 0) 1)`), and the README. run.sh prints a `NOTE` when the
  `EXPECTED:` line disagrees with `to_sexp prog`. c00 is the only corpus
  program whose type has `SExp` instances; for the others the `EXPECTED:`
  line is the reference.
- **PrimInt63**: `llvm_main.c` decoded unboxed words with an arithmetic
  shift, which prints ints ≥ 2^62 as negative numbers. It now uses a logical
  shift (unsigned, as in Rocq's `Uint63` and the corpus). This does not
  change any constructor ordinal.

## Harness changes needed to run the corpus

- Corpus files are wrapped into `_build/corpus/` (`CertiRocq.LLVMCorpus`).
  Rocq runs under `ulimit -s unlimited`, because OCaml 4.14 uses the C stack:
  on an 8 MiB stack, Rocq overflows on c15 and the plugin on c04.
- The emitted module calls `prim_int63_*` without declaring them. run.sh
  generates the `declare`s from the call sites, and every binary links
  `runtime/prim_int63.c`.
- **Checker false positive, fixed in `gc_stack_checked.c`**. The
  stack-window check ("outside the heap only the root slots are written")
  took the stack top from `pthread_getattr_np`. For a thread created with
  `pthread_create` (the driver's mutator thread), glibc places the static
  TLS and `struct pthread` at the top of that range. TLS words change during
  a GC (libc/malloc state), so shallow GCs reported spurious violations,
  e.g. c01 at GC #1:
  `stack word at 0x7f5e2917e600 changed from 0x1500000015 to 0x1000000010 during GC (not a root slot)`,
  0xc0 bytes below `pthread_self()`. The window now ends below
  `pthread_self()` minus the static TLS size (summed from `PT_TLS` via
  `dl_iterate_phdr`). The smoke tests run on the main thread, which is why
  they never hit this. They still pass.
- **GC-stress knob**: `-DCERTIROCQ_LOG_NURSERY_SIZE=k` in
  `gc_stack_checked.c`. `gc_stack.h` defines `LOG_NURSERY_SIZE`
  unconditionally, but it is include-guarded and `NURSERY_SIZE` is expanded
  lazily. So the checker includes `gc_stack.h` first, redefines
  `LOG_NURSERY_SIZE`, and then includes `gc_stack.c`. `MAX_SPACES` must be
  pinned to the length of the already-declared `struct heap` array: a first
  attempt without this overran `spaces[]` and crashed. k must cover the
  largest allocation chunk (gc_length: 4000 words, c14: 6000), so the
  default is 13. With k = 10, gc_length correctly reports a `room`
  violation.

## Update 2026-10-08

After fixing the signed comparison in `runtime/prim_int63.c` (`ltb`/`leb` now compare unsigned), c12 passes in `checked` and `asan` modes (0 GCs). c13 still fails as expected (allocating primitives collect without roots; outside the theorem).
