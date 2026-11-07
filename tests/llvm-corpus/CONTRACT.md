# Testing the runtime contract dynamically

The LambdaANF -> LLVM theorem (`LambdaANF_to_LLVM_correct_statement`) holds
under `runtime_correct cenv fds heap_inv gc make_tinfo`, defined in
`theories/CodegenLLVM/LambdaANF_to_LLVM_statement.v`. This file maps each
part of that contract to:

- the dynamic check in `runtime/gc_stack_checked.c`. Its violation messages
  quote the Rocq name in brackets. `PRE` means the emitted code broke a
  premise; `POST` means the runtime broke a conclusion.
- the corpus programs (`cNN_*.v`, see `README.md`) and the standalone smoke
  scenarios (`runtime-smoke/smoke_gc_contract.c`, run by
  `runtime-smoke/run_smoke.sh`) that exercise it.
- what cannot be tested from C, and why.

`gc_stack_checked.c` `#include`s `gc_stack.c` unmodified. It renames
`make_tinfo` and `garbage_collect` with `#define`, defines checking wrappers
around them, and routes `gc_stack.c`'s `malloc`/`free` through an observer.
Any change to `gc_stack.c` therefore shows up on the next build, so the two
files cannot drift apart. Link it in place of `gc_stack.o`.

## Static layout (hard-coded on the Rocq side)

| Rocq | C check |
|---|---|
| `off_alloc`=0, `off_limit`=8, `off_fp`=8216, `off_nalloc`=8224; `tinfo_struct_ty` (heap @16, args @24) | `_Static_assert(offsetof(...))` |
| frame `{roots_end @0; roots_start @8; prev @16}` (`shadow_stack`) | `_Static_assert` on `struct stack_frame` |
| `8232` in `not_object`, `nursery_tinfo_disjoint_stmt`, `tinfo + 8232 < 2^64` | `_Static_assert(offsetof(odata) == 8232)`, `sizeof == 8240` |

**Discrepancy (harmless):** `sizeof(struct thread_info)` is **8240**, not
8232, because the struct ends with an extra `void *odata` field. The Rocq
side uses 8232 only for (a) the region the nursery must not overlap, which
is weaker than the whole struct (the checker also tests the full 8240
bytes), and (b) a no-wrap bound that the 8240-byte block implies. The
generated code never touches `odata`.

## Clause 1: `make_tinfo`

| Rocq conjunct | C check (`make_tinfo` wrapper) | exercised by |
|---|---|---|
| `ends_in_oom \/ returns tinfo` | non-NULL. gc_stack.c `exit(1)`s when malloc fails, which is an OOM in spirit | all |
| `field st tinfo off_fp fp /\ ptr_to_int fp = 0` | `fp == NULL` | all |
| `tinfo_ok`: fields writable heap words | tinfo 8-aligned, not inside any GC space (it is its own malloc block) | all |
| `tinfo_ok`: `alloc mod 8 = 0`, `limit mod 8 = 0`, `alloc <= limit` | checked | all |
| `tinfo_ok`: `[alloc,limit)` in_heap and writable | `[alloc,limit)` lies inside the nursery's malloc'd block `[spaces[0].start, rem_limit)` | all |
| `nursery_tinfo_disjoint_stmt` | `[alloc,limit)` disjoint from `[tinfo, tinfo+8232)` (and from all 8240 bytes) | all |
| `tinfo + 8232 < 2^64` | no wrap-around | all |
| (C only) `nalloc == 0` | checked | all |
| `heap_inv st tinfo` | not testable: `heap_inv` is chosen existentially by the runtime. Clause 2 checks below stand in for it | n/a |
| `mem_ok_stmt` | see "Not testable" | n/a |

## Clause 2: the generated code preserves `heap_inv`

The premise `heap_agree_except st st2 (mutator_writes st tinfo)` restricts
the generated code to writing the nursery `[alloc,limit)` and the
`alloc`/`fp`/`nalloc` fields, and to moving `alloc` forward. The checker
records the state each time the runtime returns (from `make_tinfo` or
`garbage_collect`) and compares it at the next `garbage_collect` entry:

| check (`[runtime_correct clause 2 ...]`, PRE) | exercised by |
|---|---|
| `limit`, `heap`, `odata` unchanged | all GC tests; smoke `limit-write` |
| `alloc` moved forward, `<= limit` | all GC tests |
| hash of the allocated part of every older generation, of `struct heap` and of `tinfo->args` unchanged | all GC tests (c01, c02, c04, c16 have large old generations); smoke `old-write` |

Not checked: that a nursery object allocated since the last GC is never
rewritten after it is initialised. That would need write watchpoints (or
`mprotect` on a page-aligned nursery after every allocation, which is far
too slow). The emitted code writes each object exactly once, by
construction.

## Clause 3: the collector

Premises (checked at entry, reported as `PRE`):

| Rocq premise | C check | exercised by |
|---|---|---|
| `tinfo_ok st tinfo` | as in clause 1 | every GC |
| `nursery_tinfo_disjoint_stmt` | as in clause 1 | every GC |
| `shadow_stack st fp rs` | walks `fp`: frames 8-aligned, `root <= next`, `(next-root) % 8 == 0`, chain ends at NULL (no frame twice, depth < 2^26), frame structs and root arrays are not in the GC heap or `thread_info`, frame struct disjoint from its root array | c03 (50000 frames), c05, c09, c11; smoke `ok` (2000 frames), `bad-chain` |
| `roots_ok ... rs vs` | every root word is either odd (unboxed), or a pointer outside every GC space (a code pointer: `Repr_fun`, closures), or an 8-aligned pointer into the allocated part of a GC space with header `arity<<10|ord`, arity > 0, the whole object inside the space and **outside `[alloc,limit)` and `thread_info`** (`not_object`: the representation must not depend on those bytes). This is applied recursively to every reachable object (iterative, memoised, cycle check) | all; smoke `free-nursery` |
| `0 <= nalloc < 2^61` | checked | every GC; c14 (nalloc = 6000) |
| `heap_inv`, `mem_ok_stmt` | not testable (see below) | |

Conclusions (checked at exit, reported as `POST`):

| Rocq conclusion | C check | exercised by |
|---|---|---|
| `returns ... \/ ends_in_oom` | gc_stack.c `exit(1)`s in three cases. "Could not create the next generation" (malloc failed) is an OOM in spirit. "Ran out of generations" needs about 2^62 bytes. **"Nursery is too small for function's num_allocs"** fires when `nalloc` exceeds the fixed 65536-word nursery. That is neither room nor OOM, so the checker reports it as a `room` violation before calling the collector | **c15**; smoke `nalloc-huge` |
| `field st' tinfo off_fp fp` (same fp) | `ti->fp` unchanged | every GC |
| `shadow_stack st' fp rs` (same shadow stack) | same frames in the same order; each frame struct (`next`, `root`, `prev`) byte-for-byte unchanged | every GC; smoke selftest `frame` |
| `roots_ok st' tinfo rs vs` | unboxed roots and code-pointer roots unchanged. Boxed roots still point to well-formed objects outside the (now empty) nursery and `thread_info`, with the same header word. The structural hash of the value each root represents (the whole reachable DAG, with every field treated as a value, as in `repr_fields`) equals its hash before the GC | all GC tests; c16 (sharing), c10 (code pointers), **c07**; smoke `tag251`, selftests `unboxed`, `deep` |
| `room st' tinfo nalloc` | `limit - alloc >= 8 * nalloc` | every GC; c14 |
| `tinfo_ok st'`, `nursery_tinfo_disjoint_stmt st'` | as in clause 1 | every GC |
| outside the heap only the root slots are written | snapshot of a window (default 64 KiB, `CERTIROCQ_CHECK_STACK`) of the machine stack above `garbage_collect`'s frame. It covers the emitted code's frames, its allocas and its callers. After the GC every word must be equal, except root-slot words. Globals are not compared | every GC; smoke selftests `stack`, `frame` |
| `frames_of st' = frames_of st` | same stack window. The C stack pointer is restored by the ABI | every GC |
| new heap addresses were unallocated | `gc_stack.c`'s `malloc` is redirected (by `#define`) to an observer. Every block it returns *during* a GC must not overlap anything live at GC entry: `thread_info`, the GC spaces, the frame structs, the root arrays, the stack window | every GC that creates a generation (c01, c02, c16) |
| `nalloc` unchanged (C only) | checked | every GC |
| root slots keep their allocation ids | not testable in C (see below) | |
| `heap_inv st'`, `mem_ok_stmt st'` | not testable (see below) | |

`CERTIROCQ_CHECK_MIN_GC=N` makes a run fail (exit status 3) when fewer than
N collections happened. This guards against GC tests that never actually
collect.

## Not testable dynamically, and why

- **`heap_inv`**: an existential the runtime chooses. Nothing to observe;
  clause 2's checks approximate "the mutator does not break the runtime's
  invariant".
- **Allocation ids / provenance** ("the root slots keep their allocation
  ids", the ids of heap bytes, `mem_ok_stmt`'s "every heap address is
  allocated" and "no stack-frame address is a heap address"): these are
  concepts of Vellvm's memory model, and compiled C has no such ids. The C
  analogues are checked: frames and root arrays are not in the GC heap, the
  nursery is inside a malloc block, and ASan (`-fsanitize=address`, used by
  the smoke test) reports any access outside a live malloc block or stack
  object. Slot ids are kept by construction, since `forward` writes `*p` in
  place.
- **Locals and globals untouched (`ls`, `genv`)**: the emitted code's locals
  are SSA registers. Callee-saved registers are restored by the C calling
  convention, and spilled ones sit in the snapshotted stack window. Globals
  (code addresses, the emitted module's `@` symbols) are read-only in
  practice. One could also hash the writable data segment
  (`__data_start`..`_end`) around each GC. That is not done.
- **"New heap addresses were unallocated" for the whole program**: the
  in-file `#define malloc` only sees `gc_stack.c`'s allocations, which is
  the scope of the clause, since only the collector creates heap blocks
  during a GC. For process-wide evidence, an `LD_PRELOAD` shim could
  interpose `malloc`/`calloc`/`realloc`/`free`, keep an interval set of live
  blocks, and assert that no new block overlaps a live one or any stack
  range registered by the checker. glibc can also do it in-process through
  `__libc_malloc` wrappers. This is cheap to add but adds little over what
  ASan already enforces.
- **Divergence / OOM semantics**: `exit(1)` in the runtime cannot be told
  apart from a failure, so the checker flags the only reachable case
  (nursery too small) up front.

## Places where gc_stack.c (or the emitter) does not meet the contract

1. **Constructor ordinals >= 251** (`tag_ok` allows `ord < 1024`). Headers
   are `arity<<10 | ord`, but `gc_stack.c` reads the tag as `hd & 0xFF`, and
   `do_scan` skips the fields of objects with tag `>= No_scan_tag = 251`.
   An object whose boxed ordinal is in 251-255, 507-511, 763-767 or
   1019-1023 and whose field points into the from-space ends up holding a
   dangling pointer, which breaks `roots_ok`. Shown by smoke `tag251`
   (against the real collector) and by c07. Fix: either restrict `tag_ok`
   to `ord < 251` (as OCaml does) and make the pipeline reject wider types,
   or drop the No_scan convention from the GC for this backend. The C
   backend shares this header layout, so check it too.
2. **`nalloc` larger than the nursery** (65536 words). `resume()`
   `exit(1)`s, but the contract promises room or OOM for all
   `nalloc < 2^61`, and `llvm_restricted` only bounds a chunk below 2^61
   words. Shown by smoke `nalloc-huge` and c15 (a 66000-word chunk). Fix:
   make the collector satisfy large requests (grow the nursery or allocate
   directly in an older generation), or tighten `llvm_restricted` to
   `chunk_words <= 65536` and split chunks in the emitter.
3. `sizeof(thread_info)` = 8240 vs. the 8232 used in Rocq (harmless, see
   above).
4. `export_heap` stores the address of a local `stack_frame` in `ti->fp`
   and returns without restoring it (gcc warns `-Wdangling-pointer`). This
   is harmless unless a GC runs after `export_heap`.
5. `gc_stack.h` says `garbage_collect` initialises the heap when
   `ti->heap == NULL`, but it does not (it would crash). `make_tinfo`
   always creates the heap, so the contract is not affected.
6. Emitter, outside the theorem: allocating primitives (`addc`, `mulc`,
   `diveucl`, ...) call `garbage_collect` from C without the caller's live
   values registered (see the NOTE at `Eprim` in `LambdaANF_to_LLVM.v`).
   c13 is expected to fail.
