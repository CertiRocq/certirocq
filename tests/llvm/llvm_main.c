/* Driver for modules emitted by CertiRocq's LLVM backend
   (`CertiRocq Compile LLVM`).

   The emitted module defines
       define i64 @certirocq_main(ptr %tinfo)
   and calls (but does not define) `void @garbage_collect(ptr)`; the harness
   links it with `prelude.ll` (the declaration, i.e. the statement's
   `runtime_prelude`) and the real runtime `runtime/gc_stack.c`.

   This mirrors `run_program` of LambdaANF_to_LLVM_statement.v: call the
   runtime's `make_tinfo`, then `certirocq_main(tinfo)`, and decode the
   returned word with the representation `repr_val`:
     - odd word v        : unboxed; printed as the integer v >> 1 (logical,
                           i.e. unsigned: a nullary constructor's ordinal, or a
                           PrimInt63 value, which Rocq's Uint63 reads as an
                           unsigned 0 <= n < 2^63, as in the corpus'
                           EXPECTED: lines);
     - even word p       : boxed; header h = *(p - 8),
                           ordinal = h & 1023, arity = h >> 10,
                           field i at p + 8 i; printed as (C<ord> f0 ... fn-1).
   A function value (address of a top-level function) is even too and would be
   printed as garbage; tests only return first-order data.

   Output on stdout (compared textually by run.sh):
       <S-expression of the result>
   Diagnostics on stderr:
       gc_calls=<n> alloc=<p> limit=<p> nursery_free_words=<n>

   Environment knobs:
     CERTIROCQ_STACK_MB   size of the mutator thread's C stack in MiB
                          (default 4096; the emitted code does not use musttail,
                          so every tail call is a real C-stack frame).
     CERTIROCQ_FINAL_GC   if set, root the result in a shadow-stack frame,
                          run one extra collection, and print the (moved) result
                          a second time; both lines must be equal.

   The GC-call counter uses the linker's --wrap: the harness links with
   -Wl,--wrap=garbage_collect, so the emitted code's calls reach
   __wrap_garbage_collect, which counts and calls the real collector. */

#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>
#include <pthread.h>
#include "gc_stack.h"

extern int64_t certirocq_main(struct thread_info *tinfo);

/* ------------------------------------------------------------------ */
/* GC-call counter                                                      */

static unsigned long gc_calls = 0;
extern void __real_garbage_collect(struct thread_info *ti);

void __wrap_garbage_collect(struct thread_info *ti) {
  gc_calls++;
  __real_garbage_collect(ti);
}

/* ------------------------------------------------------------------ */
/* Printer: iterative along the last field (lists, peano numbers, ...)  */

static void print_val(FILE *out, uint64_t v) {
  unsigned long close = 0; /* pending ')' for the last-field spine */
  for (;;) {
    if (v & 1) {
      fprintf(out, "%llu", (unsigned long long)(v >> 1));
      break;
    }
    uint64_t *p = (uint64_t *)(uintptr_t)v;
    if (p == NULL) { fprintf(out, "<null>"); break; }
    uint64_t h = p[-1];
    uint64_t ord = h & 1023, arity = h >> 10;
    fprintf(out, "(C%llu", (unsigned long long)ord);
    if (arity == 0) { fputc(')', out); break; }
    for (uint64_t i = 0; i + 1 < arity; i++) {
      fputc(' ', out);
      print_val(out, p[i]);
    }
    fputc(' ', out);
    close++;
    v = p[arity - 1];
  }
  while (close--) fputc(')', out);
}

/* ------------------------------------------------------------------ */

struct run { struct thread_info *tinfo; int64_t result; };

static void *run_main(void *arg) {
  struct run *r = arg;
  r->result = certirocq_main(r->tinfo);
  return NULL;
}

int main(void) {
  struct run r;
  r.tinfo = make_tinfo();

  size_t stack_mb = 4096;
  const char *s = getenv("CERTIROCQ_STACK_MB");
  if (s && *s) stack_mb = strtoul(s, NULL, 10);

  pthread_attr_t attr;
  pthread_t th;
  pthread_attr_init(&attr);
  if (pthread_attr_setstacksize(&attr, stack_mb << 20) != 0) {
    fprintf(stderr, "llvm_main: cannot set stack size %zu MiB\n", stack_mb);
    return 2;
  }
  if (pthread_create(&th, &attr, run_main, &r) != 0) {
    fprintf(stderr, "llvm_main: pthread_create failed\n");
    return 2;
  }
  pthread_join(th, NULL);

  print_val(stdout, (uint64_t)r.result);
  fputc('\n', stdout);

  if (getenv("CERTIROCQ_FINAL_GC")) {
    /* Root the result in a one-slot shadow-stack frame and collect. */
    value root[1];
    struct stack_frame fr;
    root[0] = (value)r.result;
    fr.next = root + 1;
    fr.root = root;
    fr.prev = r.tinfo->fp;
    r.tinfo->fp = &fr;
    r.tinfo->nalloc = 0;
    __wrap_garbage_collect(r.tinfo);
    r.tinfo->fp = fr.prev;
    print_val(stdout, (uint64_t)root[0]);
    fputc('\n', stdout);
  }

  fprintf(stderr, "gc_calls=%lu alloc=%p limit=%p nursery_free_words=%ld fp=%p\n",
          gc_calls, (void *)r.tinfo->alloc, (void *)r.tinfo->limit,
          (long)(r.tinfo->limit - r.tinfo->alloc), (void *)r.tinfo->fp);
  return 0;
}
