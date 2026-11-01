/* Standalone smoke test of runtime/gc_stack_checked.c against the REAL
   collector (gc_stack.c), without the Rocq pipeline.

   The mutator below imitates the code emitted by
   theories/CodegenLLVM/LambdaANF_to_LLVM.v: bump allocation in
   [tinfo->alloc, tinfo->limit), a limit check per allocation chunk, and,
   at a GC point, a stack-allocated root array + stack_frame pushed on
   tinfo->fp, tinfo->nalloc := chunk words, garbage_collect(tinfo), reload,
   pop.  Non-tail calls register the caller's live values the same way.

   Usage: smoke_gc_contract [scenario]
     ok (default)  : must print "smoke: OK" and a contract summary with
                     gc_calls > 0, and exit 0;
     tag251        : a boxed constructor with ordinal 251 (allowed by the
                     Rocq [tag_ok]: ord < 1024) whose field points into the
                     nursery; the REAL collector does not scan it (No_scan),
                     the checker must report a roots_ok violation;
     misaligned    : alloc not 8-aligned at a GC call (PRE violation);
     free-nursery  : a root pointing into the free nursery [alloc,limit)
                     (PRE violation of roots_ok/not_object);
     bad-chain     : a frame with root > next (PRE violation of shadow_stack);
     nalloc-huge   : nalloc larger than the nursery (gc_stack.c would
                     exit(1); reported as a room violation);
     old-write     : the mutator writes an object of an older generation
                     between two collections (PRE violation of clause 2);
     limit-write   : the mutator writes tinfo->limit (clause 2);
   With -DCERTIROCQ_CHECK_SELFTEST, CERTIROCQ_CHECK_SELFTEST=stack|frame|
   unboxed|deep injects a fault after the real collection, to check the POST
   checks fire. */

#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include "m.h"
#include "config.h"
#include "values.h"
#include "gc_stack.h"

#define HDR(arity, ord) ((value)(((uintnat)(arity) << 10) | (uintnat)(ord)))
#define VAL_INT(n) ((value)(((uintnat)(n) << 1) | 1))
#define INT_VAL(v) ((long)((intnat)(v) >> 1))

static struct thread_info *ti;

/* a "code pointer" (Vfun / closure code) kept in a root: must be left alone */
static value some_code(struct thread_info *t, value a) { (void)t; return a; }

/* Unchecked allocation: the caller has ensured room. */
static value alloc_obj(uintnat ord, uintnat arity, const value *fields) {
  value *a = ti->alloc;
  if ((uintptr_t)(ti->limit - a) < 1 + arity) { fprintf(stderr, "smoke: no room\n"); abort(); }
  a[0] = HDR(arity, ord);
  for (uintnat i = 0; i < arity; i++) a[1 + i] = fields[i];
  ti->alloc = a + 1 + arity;
  return (value)(a + 1);
}

/* The GC point of an allocation chunk of [words] words with live values
   roots[0..n): exactly the emitted check/gc blocks. */
static void ensure(uintnat words, value *live, size_t n) {
  if ((uintptr_t)((char *)ti->limit - (char *)ti->alloc) >= 8 * words) return;
  value roots[n ? n : 1];
  struct stack_frame fr;
  for (size_t i = 0; i < n; i++) roots[i] = live[i];       /* spill */
  fr.next = roots + n; fr.root = roots; fr.prev = ti->fp;  /* link */
  ti->fp = &fr;
  ti->nalloc = words;
  garbage_collect(ti);
  for (size_t i = 0; i < n; i++) live[i] = roots[i];       /* reload */
  ti->fp = fr.prev;                                         /* pop */
}

/* cons(h, t) = C1 h t (ordinal 0 among the boxed ctors of list, arity 2);
   nil = unboxed 0 */
#define NIL VAL_INT(0)
static value cons(value h, value t) { value f[2] = { h, t }; return alloc_obj(0, 2, f); }

static long sum_list(value l) {
  long s = 0;
  while (!((uintnat)l & 1)) { s += INT_VAL(((value *)l)[0]); l = ((value *)l)[1]; }
  return s;
}

/* Non-tail recursion: depth levels, each with a frame holding 4 live values
   (acc list, a per-level record, an unboxed int, a code pointer) across the
   recursive call, and each allocating [per] cons cells (GC pressure while
   deep frames are live). */
static value build(int depth, int per, value acc) {
  value live[4];
  live[0] = acc;
  ensure(4, live, 1);
  { value f[3] = { VAL_INT(depth), VAL_INT(2 * depth), VAL_INT(3 * depth) };
    live[1] = alloc_obj(5, 3, f); }
  live[2] = VAL_INT(depth * 7);
  live[3] = (value)&some_code;
  for (int i = 0; i < per; i++) {
    ensure(3, live, 4);
    live[0] = cons(VAL_INT(1), live[0]);
  }
  if (depth > 0) {
    /* Eletapp: register live values around the call */
    value roots[4]; struct stack_frame fr;
    memcpy(roots, live, sizeof roots);
    fr.next = roots + 4; fr.root = roots; fr.prev = ti->fp; ti->fp = &fr;
    value r = build(depth - 1, per, roots[0]);
    memcpy(live, roots, sizeof roots);
    ti->fp = fr.prev;
    live[0] = r;
  }
  /* the per-level record and the unboxed/code roots must have survived */
  value *rec = (value *)live[1];
  if (((header_t *)rec)[-1] != (header_t)HDR(3, 5) || INT_VAL(rec[0]) != depth ||
      INT_VAL(rec[1]) != 2 * depth || INT_VAL(rec[2]) != 3 * depth ||
      INT_VAL(live[2]) != depth * 7 || live[3] != (value)&some_code) {
    fprintf(stderr, "smoke: per-level data corrupted at depth %d\n", depth); abort();
  }
  return live[0];
}

static int scenario_ok(void) {
  value live[4];
  /* a large constructor (arity 300) and a DAG with sharing, live throughout */
  value big[300];
  ensure(301, live, 0);
  for (int i = 0; i < 300; i++) big[i] = VAL_INT(i);
  live[0] = alloc_obj(3, 300, big);
  ensure(3, live, 1);
  live[1] = cons(VAL_INT(42), NIL);
  ensure(3, live, 2);
  { value f[2] = { live[1], live[1] }; live[2] = alloc_obj(1, 2, f); }  /* shared */
  live[3] = (value)&some_code;

  /* deep recursion with GC pressure; the four values above are registered
     around the call as the emitted Eletapp does */
  value roots[4]; struct stack_frame fr;
  memcpy(roots, live, sizeof roots);
  fr.next = roots + 4; fr.root = roots; fr.prev = ti->fp; ti->fp = &fr;
  int depth = 2000, per = 300;
  value l = build(depth, per, NIL);
  memcpy(live, roots, sizeof roots);
  ti->fp = fr.prev;

  long s = sum_list(l);
  long expect = (long)(depth + 1) * per;
  value *b = (value *)live[0];
  for (int i = 0; i < 300; i++)
    if (INT_VAL(b[i]) != i) { fprintf(stderr, "smoke: big ctor corrupted\n"); return 1; }
  value *sh = (value *)live[2];
  if (sh[0] != sh[1] || INT_VAL(((value *)sh[0])[0]) != 42) {
    fprintf(stderr, "smoke: sharing lost\n"); return 1;
  }
  if (s != expect) { fprintf(stderr, "smoke: sum %ld != %ld\n", s, expect); return 1; }
  printf("smoke: OK sum=%ld depth=%d\n", s, depth);
  return 0;
}

/* Force a collection with the given live values (ignoring the room test). */
static void force_gc(value *live, size_t n, uintnat nalloc) {
  value roots[n ? n : 1]; struct stack_frame fr;
  for (size_t i = 0; i < n; i++) roots[i] = live[i];
  fr.next = roots + n; fr.root = roots; fr.prev = ti->fp; ti->fp = &fr;
  ti->nalloc = nalloc;
  garbage_collect(ti);
  for (size_t i = 0; i < n; i++) live[i] = roots[i];
  ti->fp = fr.prev;
}

int main(int argc, char **argv) {
  const char *sc = argc > 1 ? argv[1] : "ok";
  ti = make_tinfo();
  if (!strcmp(sc, "ok")) return scenario_ok();
  if (!strcmp(sc, "tag251")) {
    value live[1];
    value c = cons(VAL_INT(7), NIL);                 /* in the nursery */
    live[0] = alloc_obj(251, 1, &c);                 /* ordinal 251, arity 1 */
    force_gc(live, 1, 2);
    value *o = (value *)live[0];
    printf("smoke: after GC, field of ord-251 object -> %p (header there: %#lx)\n",
           (void *)o[0], (unsigned long)((header_t *)o[0])[-1]);
    return 0;
  }
  if (!strcmp(sc, "misaligned")) {
    ti->alloc = (value *)((char *)ti->alloc + 4);
    force_gc(NULL, 0, 1);
    return 0;
  }
  if (!strcmp(sc, "free-nursery")) {
    value *a = ti->alloc;
    a[100] = HDR(1, 0); a[101] = VAL_INT(1);        /* a "header" in free space */
    value live[1] = { (value)(a + 101) };
    force_gc(live, 1, 1);
    return 0;
  }
  if (!strcmp(sc, "bad-chain")) {
    value roots[2] = { VAL_INT(1), VAL_INT(2) };
    struct stack_frame fr = { roots, roots + 2, NULL };  /* next < root */
    ti->fp = &fr; ti->nalloc = 1;
    garbage_collect(ti);
    return 0;
  }
  if (!strcmp(sc, "nalloc-huge")) {
    force_gc(NULL, 0, (uintnat)NURSERY_SIZE + 1);
    return 0;
  }
  if (!strcmp(sc, "old-write")) {   /* mutator writes a promoted object */
    value live[1];
    live[0] = cons(VAL_INT(1), NIL);
    force_gc(live, 1, 2);                          /* promoted to generation 1 */
    ((value *)live[0])[0] = VAL_INT(2);            /* not in mutator_writes */
    force_gc(live, 1, 2);
    return 0;
  }
  if (!strcmp(sc, "limit-write")) {   /* mutator writes tinfo->limit */
    force_gc(NULL, 0, 2);
    ti->limit -= 2;
    force_gc(NULL, 0, 2);
    return 0;
  }
  if (!strcmp(sc, "selftest")) {      /* used with CERTIROCQ_CHECK_SELFTEST */
    value live[3];
    live[0] = VAL_INT(5);
    { value f[2] = { VAL_INT(1), VAL_INT(2) }; live[1] = alloc_obj(0, 2, f); }
    live[2] = (value)&some_code;
    volatile long local = 12345;
    force_gc(live, 3, 4);
    printf("smoke: selftest survived (local=%ld)\n", (long)local);
    return 0;
  }
  fprintf(stderr, "unknown scenario %s\n", sc);
  return 2;
}
