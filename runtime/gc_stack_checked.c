/* gc_stack_checked.c -- the CertiRocq stack GC (gc_stack.c), wrapped with
   dynamic checks of the runtime contract that the LambdaANF -> LLVM
   correctness theorem assumes.

   The contract is [runtime_correct] in
   theories/CodegenLLVM/LambdaANF_to_LLVM_statement.v.  This file tests, on
   real executions, that the C runtime behaves as that Rocq statement says.

   HOW IT IS BUILT.  This file #includes gc_stack.c verbatim, after renaming
   (with the preprocessor) its two entry points
       make_tinfo      -> certirocq_real_make_tinfo
       garbage_collect -> certirocq_real_garbage_collect
   and its calls to malloc/free (to observe the blocks the collector creates).
   It then defines checking versions of [make_tinfo] and [garbage_collect]
   that call the real ones.  So:
     - gc_stack.c is not modified, and there is nothing to keep in sync: any
       change to gc_stack.c is picked up on the next build;
     - link THIS object INSTEAD OF gc_stack.o (it contains all of gc_stack.c):
         clang -I runtime -c runtime/gc_stack_checked.c
     - everything else (prim_int63.c, the driver, the emitted code) is linked
       unchanged; prim_int63.c's internal calls to garbage_collect are checked
       as well.

   ON VIOLATION: prints "certirocq-contract: VIOLATION [<clause>] ..." on
   stderr and calls abort().  <clause> is the Rocq name of the clause tested.
   A violation tagged PRE is a broken premise of the collector clause, i.e. a
   bug of the *emitted code* (or of the runtime's previous GC run); POST is a
   broken conclusion, i.e. a bug of the *runtime*.

   AT EXIT: prints a one-line summary on stderr, e.g.
     certirocq-contract: OK gc_calls=12 max_ss_depth=3 ...
   Environment variables:
     CERTIROCQ_CHECK_MIN_GC=N     fail (exit status 3) at exit if fewer than N
                                  collections ran;
     CERTIROCQ_CHECK_DEEP=0       disable the (O(live heap)) deep comparison of
                                  the values represented by the roots;
     CERTIROCQ_CHECK_STACK=BYTES  size of the window of the caller's machine
                                  stack that is snapshotted around every
                                  collection (default 65536; 0 disables);
     CERTIROCQ_CHECK_QUIET=1      no summary line unless something failed.
*/

#define _GNU_SOURCE 1
#include <stddef.h>
#include <unistd.h>
#include <stdint.h>
#include <string.h>
#include <stdlib.h>
#include <stdio.h>
#include <pthread.h>

/* ------------------------------------------------------------------ */
/* Include the real collector, with renamed entry points and observed
   malloc/free. */

#define make_tinfo      certirocq_real_make_tinfo
#define garbage_collect certirocq_real_garbage_collect
static void *cc_malloc(size_t n);
static void cc_free(void *p);
#define malloc(n) cc_malloc(n)
#define free(p)   cc_free(p)
/* GC-stress knob: -DCERTIROCQ_LOG_NURSERY_SIZE=k builds the collector with a
   2^k-word nursery instead of gc_stack.h's hard-coded 2^16 (more collections,
   more root checks).  gc_stack.h defines LOG_NURSERY_SIZE unconditionally,
   but it has an include guard and NURSERY_SIZE is expanded lazily, so
   including it first and redefining LOG_NURSERY_SIZE before gc_stack.c
   (whose own #include "gc_stack.h" is then a no-op) works without touching
   gc_stack.[ch].  MAX_SPACES also depends on LOG_NURSERY_SIZE, but
   struct heap's array was already declared with the original value, so it
   is pinned to that array's length (the largest generation is then
   2^(k-16) times smaller, still far beyond any real heap).  Only this
   translation unit sees the new values; nothing else uses NURSERY_SIZE or
   MAX_SPACES (the emitted code and llvm_main.c only use thread_info's
   fields; prim_int63.c only calls garbage_collect).  A chunk larger than the
   nursery makes resume() exit (reported as a [room] violation), so keep k
   large enough for the program's largest allocation chunk. */
#ifdef CERTIROCQ_LOG_NURSERY_SIZE
#include "gc_stack.h"
#undef LOG_NURSERY_SIZE
#define LOG_NURSERY_SIZE CERTIROCQ_LOG_NURSERY_SIZE
#undef MAX_SPACES
#define MAX_SPACES (sizeof(((struct heap *)0)->spaces) / sizeof(struct space))
#endif
#include "gc_stack.c"
#undef malloc
#undef free
#undef make_tinfo
#undef garbage_collect

struct thread_info *make_tinfo(void);
void garbage_collect(struct thread_info *ti);

/* ------------------------------------------------------------------ */
/* Layout of thread_info as hard-coded by the Rocq side
   ([off_alloc], [off_limit], [off_fp], [off_nalloc] in
   LambdaANF_to_LLVM_statement.v, [tinfo_struct_ty]/[gep_tinfo] in
   LambdaANF_to_LLVM.v) and of a shadow-stack frame
   ({ roots_end @0; roots_start @8; prev @16 } in [shadow_stack]). */

#define ROCQ_TINFO_SIZE 8232   /* the "8232" of not_object / nursery_tinfo_disjoint_stmt */

_Static_assert(sizeof(value) == 8, "64-bit words (Pa64)");
_Static_assert(sizeof(void *) == 8, "64-bit pointers (IP64Bit)");
_Static_assert(offsetof(struct thread_info, alloc)  == 0,    "off_alloc = 0");
_Static_assert(offsetof(struct thread_info, limit)  == 8,    "off_limit = 8");
_Static_assert(offsetof(struct thread_info, heap)   == 16,   "heap @16");
_Static_assert(offsetof(struct thread_info, args)   == 24,   "args @24");
_Static_assert(offsetof(struct thread_info, fp)     == 8216, "off_fp = 8216");
_Static_assert(offsetof(struct thread_info, nalloc) == 8224, "off_nalloc = 8224");
/* NOTE: the C struct has one more field, [odata] @8232, so
   sizeof(struct thread_info) == 8240, not 8232.  The Rocq statement only
   uses 8232 as the extent of the region that must be disjoint from the
   nursery (a weaker requirement than disjointness from all 8240 bytes, which
   we check below) and in the no-wrap-around bound (tinfo + 8232 < 2^64,
   implied by tinfo + 8240 not wrapping).  So the discrepancy is harmless,
   but we pin it down here so that a layout change is noticed. */
_Static_assert(offsetof(struct thread_info, odata)  == ROCQ_TINFO_SIZE, "odata just after the Rocq-visible part");
_Static_assert(sizeof(struct thread_info) == ROCQ_TINFO_SIZE + 8, "sizeof(thread_info) = 8232 + odata");
_Static_assert(offsetof(struct stack_frame, next) == 0,  "frame: roots_end @0");
_Static_assert(offsetof(struct stack_frame, root) == 8,  "frame: roots_start @8");
_Static_assert(offsetof(struct stack_frame, prev) == 16, "frame: prev @16");

/* ------------------------------------------------------------------ */
/* Reporting */

static unsigned long cc_gc_calls, cc_max_depth, cc_max_roots, cc_max_nalloc,
  cc_roots_checked, cc_boxed_roots, cc_objs_hashed, cc_new_blocks,
  cc_stack_bytes_checked, cc_tinfos;
static int cc_failed;

#define CC_PRE  "PRE"
#define CC_POST "POST"
#define CC_INIT "MAKE_TINFO"

static void cc_violation(const char *kind, const char *clause, const char *fmt, ...)
  __attribute__((format(printf, 3, 4), noreturn));

#include <stdarg.h>
static void cc_violation(const char *kind, const char *clause, const char *fmt, ...) {
  va_list ap;
  cc_failed = 1;
  fflush(stdout);
  fprintf(stderr, "certirocq-contract: VIOLATION [%s] %s (gc call #%lu): ",
          clause, kind, cc_gc_calls);
  va_start(ap, fmt);
  vfprintf(stderr, fmt, ap);
  va_end(ap);
  fprintf(stderr, "\n");
  fflush(stderr);
  abort();
}

#define CHECK(kind, clause, cond, ...) \
  do { if (!(cond)) cc_violation(kind, clause, __VA_ARGS__); } while (0)

static long cc_env_long(const char *name, long dflt) {
  const char *s = getenv(name);
  if (!s || !*s) return dflt;
  return strtol(s, NULL, 0);
}

static void cc_summary(void) {
  long min_gc = cc_env_long("CERTIROCQ_CHECK_MIN_GC", 0);
  int bad = cc_failed || (long)cc_gc_calls < min_gc;
  if (bad || !cc_env_long("CERTIROCQ_CHECK_QUIET", 0)) {
    fflush(stdout);
    fprintf(stderr,
            "certirocq-contract: %s gc_calls=%lu max_ss_depth=%lu max_roots=%lu "
            "max_nalloc=%lu roots_checked=%lu boxed_roots=%lu objs_hashed=%lu "
            "new_heap_blocks=%lu stack_bytes_checked=%lu nursery_words=%lu\n",
            bad ? "FAIL" : "OK", cc_gc_calls, cc_max_depth, cc_max_roots,
            cc_max_nalloc, cc_roots_checked, cc_boxed_roots, cc_objs_hashed,
            cc_new_blocks, cc_stack_bytes_checked, (unsigned long)NURSERY_SIZE);
    if ((long)cc_gc_calls < min_gc)
      fprintf(stderr, "certirocq-contract: expected at least %ld GC calls "
              "(CERTIROCQ_CHECK_MIN_GC), got %lu\n", min_gc, cc_gc_calls);
    fflush(stderr);
  }
  if (bad) _exit(3);
}

/* ------------------------------------------------------------------ */
/* malloc/free observation: every block the collector creates.
   Clause: "every heap address newly created was unallocated before"
   ([forall a, in_heap st' a -> in_heap st a \/ lookup a (mem_of st) = None]).
   In C we cannot see "unallocated" directly; what we can check is that a
   block returned by malloc during a collection does not overlap anything
   that was allocated before the collection and is still live: the
   thread_info, the GC spaces that existed at entry, the shadow-stack frame
   structs and root arrays, and the snapshotted window of the caller's
   stack. */

struct cc_range { uintptr_t lo, hi; const char *what; };
static struct cc_range *cc_live; static size_t cc_nlive, cc_caplive;
static int cc_in_gc;

static void cc_live_reset(void) { cc_nlive = 0; }
static void cc_live_add(uintptr_t lo, uintptr_t hi, const char *what) {
  if (hi <= lo) return;
  if (cc_nlive == cc_caplive) {
    cc_caplive = cc_caplive ? 2 * cc_caplive : 256;
    cc_live = realloc(cc_live, cc_caplive * sizeof *cc_live);
    if (!cc_live) { perror("certirocq-contract"); abort(); }
  }
  cc_live[cc_nlive++] = (struct cc_range){ lo, hi, what };
}

static void *cc_malloc(size_t n) {
  void *p = malloc(n);
  if (p && cc_in_gc) {
    uintptr_t lo = (uintptr_t)p, hi = lo + n;
    cc_new_blocks++;
    CHECK(CC_POST, "runtime_correct: new heap addresses were unallocated",
          hi >= lo, "malloc'd block [%p,+%zu) wraps around", p, n);
    for (size_t i = 0; i < cc_nlive; i++)
      CHECK(CC_POST, "runtime_correct: new heap addresses were unallocated",
            hi <= cc_live[i].lo || cc_live[i].hi <= lo,
            "block [%p,%p) malloc'd during GC overlaps live %s [%p,%p)",
            p, (void *)hi, cc_live[i].what, (void *)cc_live[i].lo,
            (void *)cc_live[i].hi);
  }
  return p;
}
static void cc_free(void *p) { free(p); }

/* ------------------------------------------------------------------ */
/* Heap geometry */

static int cc_overlap(uintptr_t a, uintptr_t b, uintptr_t c, uintptr_t d) {
  return a < d && c < b;
}

/* Index of the GC space whose malloc'd block [start, rem_limit) contains
   [lo, hi), or -1 if none does. */
static int cc_space_of(struct heap *h, uintptr_t lo, uintptr_t hi) {
  for (int i = 0; i < (int)MAX_SPACES; i++) {
    struct space *s = &h->spaces[i];
    if (s->start == NULL) continue;
    if ((uintptr_t)s->start <= lo && hi <= (uintptr_t)s->rem_limit) return i;
  }
  return -1;
}
static int cc_touches_heap(struct heap *h, uintptr_t lo, uintptr_t hi) {
  for (int i = 0; i < (int)MAX_SPACES; i++) {
    struct space *s = &h->spaces[i];
    if (s->start && cc_overlap(lo, hi, (uintptr_t)s->start, (uintptr_t)s->rem_limit))
      return 1;
  }
  return 0;
}

/* The well-formedness of thread_info and its nursery ([tinfo_ok],
   [nursery_tinfo_disjoint_stmt]); used at make_tinfo, GC entry and GC exit. */
static void cc_check_tinfo(const char *kind, struct thread_info *ti) {
  uintptr_t t = (uintptr_t)ti, a = (uintptr_t)ti->alloc, l = (uintptr_t)ti->limit;
  struct heap *h = ti->heap;
  CHECK(kind, "runtime_correct (tinfo + 8232 < 2^64)",
        t + sizeof(struct thread_info) > t, "thread_info at %p wraps around", (void *)ti);
  CHECK(kind, "tinfo_ok (alloc mod 8 = 0)", a % 8 == 0, "alloc = %p", (void *)a);
  CHECK(kind, "tinfo_ok (limit mod 8 = 0)", l % 8 == 0, "limit = %p", (void *)l);
  CHECK(kind, "tinfo_ok (alloc <= limit)", a <= l, "alloc = %p > limit = %p", (void *)a, (void *)l);
  CHECK(kind, "tinfo_ok (heap)", h != NULL, "tinfo->heap == NULL");
  /* [alloc, limit) is a writable malloc'd (heap) region: it lies inside the
     nursery block of the GC. */
  CHECK(kind, "tinfo_ok (nursery [alloc,limit) is in_heap and writable)",
        a == l || ((uintptr_t)h->spaces[0].start <= a && l <= (uintptr_t)h->spaces[0].rem_limit),
        "[alloc,limit) = [%p,%p) not inside the nursery block [%p,%p)",
        (void *)a, (void *)l, (void *)h->spaces[0].start, (void *)h->spaces[0].rem_limit);
  CHECK(kind, "nursery_tinfo_disjoint_stmt",
        !cc_overlap(a, l, t, t + ROCQ_TINFO_SIZE),
        "nursery [%p,%p) overlaps thread_info [%p,+8232)", (void *)a, (void *)l, (void *)ti);
  /* stronger, whole struct incl. odata */
  CHECK(kind, "nursery_tinfo_disjoint_stmt (whole struct)",
        !cc_overlap(a, l, t, t + sizeof(struct thread_info)),
        "nursery overlaps thread_info.odata");
  CHECK(kind, "not_object (thread_info is not part of any GC space)",
        !cc_touches_heap(h, t, t + sizeof(struct thread_info)),
        "thread_info [%p,+%zu) overlaps a GC space", (void *)ti, sizeof(struct thread_info));
}

/* ------------------------------------------------------------------ */
/* Clause 2 of [runtime_correct]: between two runtime calls, the generated
   code only writes the nursery and the alloc/fp/nalloc fields of
   thread_info ([mutator_writes]), and only moves alloc forward, within
   [alloc, limit], word-aligned.  We record the state when the runtime
   returns (make_tinfo / garbage_collect exit) and compare at the next
   garbage_collect entry: limit, heap and odata unchanged, alloc moved
   forward, and the bytes of the older generations' allocated parts (a hash;
   skipped with CERTIROCQ_CHECK_DEEP=0), of the heap descriptor and of
   tinfo->args unchanged.  Not checked: that objects allocated in the
   nursery since the last collection are not rewritten after their
   initialisation (that would need write watchpoints). */

static struct {
  struct thread_info *ti; value *alloc, *limit; struct heap *heap; void *odata;
  uint64_t old_hash; int valid;
} cc_last;
static int cc_deep = 1;

static uint64_t cc_bytes_hash(const void *p, size_t n) {
  const unsigned char *b = p; uint64_t x = 0xcbf29ce484222325ull;
  for (size_t i = 0; i < n; i++) { x ^= b[i]; x *= 0x100000001b3ull; }
  return x;
}

/* Everything of the heap that the generated code must not write: the
   allocated parts of the older generations, the [struct heap] descriptor,
   and thread_info's args array. */
static uint64_t cc_old_gen_hash(struct thread_info *ti) {
  struct heap *h = ti->heap;
  uint64_t acc = cc_bytes_hash(h, sizeof *h) * 31 + cc_bytes_hash(ti->args, sizeof ti->args);
  if (!cc_deep) return acc;
  for (int i = 1; i < (int)MAX_SPACES; i++) {
    struct space *sp = &h->spaces[i];
    if (!sp->start) continue;
    uint64_t x = 0x84222325cbf29ce4ull ^ (uint64_t)i;
    for (value *w = sp->start; w < sp->next; w++) {
      x ^= (uint64_t)*w; x *= 0x100000001b3ull; x ^= x >> 29;
    }
    acc = acc * 31 + x;
  }
  return acc;
}

static void cc_record_exit(struct thread_info *ti) {
  cc_last.ti = ti; cc_last.alloc = ti->alloc; cc_last.limit = ti->limit;
  cc_last.heap = ti->heap; cc_last.odata = ti->odata;
  cc_last.old_hash = cc_old_gen_hash(ti); cc_last.valid = 1;
}

static void cc_check_mutator(struct thread_info *ti) {
  const char *cl = "runtime_correct clause 2 (generated code only writes the nursery and "
                   "alloc/fp/nalloc; alloc moves forward within [alloc,limit])";
  if (!cc_last.valid || cc_last.ti != ti) return;
  CHECK(CC_PRE, cl, ti->limit == cc_last.limit, "limit changed from %p to %p between GCs",
        (void *)cc_last.limit, (void *)ti->limit);
  CHECK(CC_PRE, cl, ti->heap == cc_last.heap, "tinfo->heap changed between GCs");
  CHECK(CC_PRE, cl, ti->odata == cc_last.odata, "tinfo->odata changed between GCs");
  CHECK(CC_PRE, cl, cc_last.alloc <= ti->alloc && ti->alloc <= ti->limit,
        "alloc moved from %p to %p (limit %p)", (void *)cc_last.alloc, (void *)ti->alloc,
        (void *)ti->limit);
  CHECK(CC_PRE, cl, cc_old_gen_hash(ti) == cc_last.old_hash,
        "the older generations, the heap descriptor or tinfo->args were written between GCs");
}

/* ------------------------------------------------------------------ */
/* make_tinfo.  Clause 1 of [runtime_correct]. */

static void cc_init(void);
struct thread_info *make_tinfo(void) {
  cc_init();
  struct thread_info *ti = certirocq_real_make_tinfo();
  cc_tinfos++;
  CHECK(CC_INIT, "runtime_correct (make_tinfo returns a pointer)", ti != NULL, "NULL");
  CHECK(CC_INIT, "runtime_correct (thread_info word-aligned)", (uintptr_t)ti % 8 == 0,
        "tinfo = %p", (void *)ti);
  CHECK(CC_INIT, "runtime_correct (field fp = 0: empty shadow_stack)", ti->fp == NULL,
        "fp = %p", (void *)ti->fp);
  /* nalloc is not part of the Rocq clause (the generated code writes it
     before every GC call), but gc_stack.c initialises it to 0. */
  CHECK(CC_INIT, "make_tinfo (nalloc = 0)", ti->nalloc == 0, "nalloc = %lu", (unsigned long)ti->nalloc);
  cc_check_tinfo(CC_INIT, ti);
  cc_record_exit(ti);
  return ti;
}

/* ------------------------------------------------------------------ */
/* Snapshot of the shadow stack ([shadow_stack]) */

struct cc_frame { struct stack_frame *f, fcopy; size_t first_root, nroots; };
static struct cc_frame *cc_frames; static size_t cc_nframes, cc_capframes;
struct cc_root { value *slot; value before; header_t header; uint64_t hash; int kind; };
enum { R_UNBOXED, R_BOXED, R_EXTERNAL };
static struct cc_root *cc_roots; static size_t cc_nroots, cc_caproots;

static void *cc_grow(void *p, size_t *cap, size_t need, size_t elt) {
  if (need <= *cap) return p;
  size_t c = *cap ? *cap : 64;
  while (c < need) c *= 2;
  p = realloc(p, c * elt);
  if (!p) { perror("certirocq-contract"); abort(); }
  *cap = c;
  return p;
}

/* ------------------------------------------------------------------ */
/* Values ([repr_val]).
   A word w represents a value only if
     - w is odd (unboxed constructor or primitive int), or
     - w is even and points into the allocated part of a GC space, 8-aligned,
       with a header word arity<<10|ord, arity > 0, and the whole object
       [w-8, w+8*arity) in that space; and then, by [roots_ok], the object is
       outside the nursery [alloc,limit) and outside thread_info
       ([not_object]); its fields are recursively values;
     - or w is even and outside every GC space: a code pointer (a [Vfun]:
       after closure conversion, code pointers live in roots and in closure
       records) or static data.  The collector must leave it alone.
   The deep check computes a structural hash of the value represented by
   every root (an iterative post-order over the reachable DAG, memoised by
   address), before and after the collection, and compares.  The hash
   treats EVERY field as a value, as [repr_val]/[repr_fields] do; it does not
   use the C runtime's No_scan convention (tag >= 251), see below. */

struct cc_ent { uintptr_t key; uint64_t h; int state; };  /* state 1 = on stack, 2 = done */
static struct cc_ent *cc_tab; static size_t cc_tabcap, cc_tabn;
static uintptr_t *cc_stk; static size_t cc_stkcap;

static size_t cc_hash_addr(uintptr_t k) { return (size_t)((k >> 3) * 0x9E3779B97F4A7C15ull); }
static struct cc_ent *cc_lookup(uintptr_t k, int insert) {
  if (insert && 2 * (cc_tabn + 1) > cc_tabcap) {
    size_t oc = cc_tabcap; struct cc_ent *ot = cc_tab;
    cc_tabcap = oc ? 2 * oc : 1 << 12;
    cc_tab = calloc(cc_tabcap, sizeof *cc_tab);
    if (!cc_tab) { perror("certirocq-contract"); abort(); }
    cc_tabn = 0;
    for (size_t i = 0; i < oc; i++) if (ot[i].key) {
      size_t j = cc_hash_addr(ot[i].key) & (cc_tabcap - 1);
      while (cc_tab[j].key) j = (j + 1) & (cc_tabcap - 1);
      cc_tab[j] = ot[i]; cc_tabn++;
    }
    free(ot);
  }
  if (!cc_tabcap) return NULL;
  size_t j = cc_hash_addr(k) & (cc_tabcap - 1);
  while (cc_tab[j].key) {
    if (cc_tab[j].key == k) return &cc_tab[j];
    j = (j + 1) & (cc_tabcap - 1);
  }
  if (!insert) return NULL;
  cc_tab[j].key = k; cc_tab[j].state = 0; cc_tab[j].h = 0; cc_tabn++;
  return &cc_tab[j];
}
static void cc_tab_clear(void) { if (cc_tab) memset(cc_tab, 0, cc_tabcap * sizeof *cc_tab); cc_tabn = 0; }

static uint64_t cc_mix(uint64_t h, uint64_t x) {
  h ^= x + 0x9E3779B97F4A7C15ull + (h << 6) + (h >> 2);
  h *= 0xff51afd7ed558ccdull; h ^= h >> 33;
  return h;
}

/* Classification of a word that is not odd. */
static int cc_is_object_ptr(struct heap *h, value w) {
  return cc_space_of(h, (uintptr_t)w, (uintptr_t)w + 1) >= 0;
}

/* Checks that pointer w is a well-formed object (see above).  [alloc,limit)
   is the current nursery; [s0next] is the end of the allocated part of the
   nursery (= alloc at entry, = start after a collection). */
static void cc_check_object(const char *kind, struct thread_info *ti, value w, const char *where) {
  struct heap *h = ti->heap;
  uintptr_t p = (uintptr_t)w;
  int sp = cc_space_of(h, p - 8, p);
  CHECK(kind, "repr_val (Repr_boxed: ptr_to_int p mod 8 = 0)", p % 8 == 0,
        "%s: pointer %p into the GC heap is not word-aligned", where, (void *)p);
  CHECK(kind, "repr_val (Repr_boxed: header readable)", sp >= 0,
        "%s: header of %p not inside a GC space", where, (void *)p);
  header_t hd = ((header_t *)p)[-1];
  uintnat arity = hd >> 10;
  CHECK(kind, "repr_val (Repr_boxed: header arity<<10|ord, arity > 0)", hd != 0 && arity > 0,
        "%s: object %p has header %#lx (forwarded or garbage)", where, (void *)p, (unsigned long)hd);
  uintptr_t end = p + 8 * arity;
  CHECK(kind, "repr_val (repr_fields: fields readable)",
        end > p && cc_space_of(h, p - 8, end) == sp,
        "%s: object %p (arity %lu) extends past its GC space", where, (void *)p, (unsigned long)arity);
  /* The allocated part of the space: [start, next) for older generations,
     [start, alloc) for the nursery (its [next] field is stale at entry). */
  struct space *s = &h->spaces[sp];
  uintptr_t used_end = sp == 0 ? (uintptr_t)ti->alloc : (uintptr_t)s->next;
  CHECK(kind, "roots_ok / not_object (object outside the nursery [alloc,limit) and allocated)",
        end <= used_end,
        "%s: object [%p,%p) (header %#lx) is not in the allocated part [%p,%p) of space %d "
        "(dangling pointer, or object inside the free nursery [alloc,limit))",
        where, (void *)(p - 8), (void *)end, (unsigned long)hd, (void *)s->start,
        (void *)used_end, sp);
  CHECK(kind, "roots_ok / not_object (object outside thread_info)",
        !cc_overlap(p - 8, end, (uintptr_t)ti, (uintptr_t)ti + sizeof *ti),
        "%s: object %p overlaps thread_info", where, (void *)p);
}

static uint64_t cc_value_hash(const char *kind, struct thread_info *ti, value root) {
  struct heap *h = ti->heap;
  if ((uintnat)root & 1) return cc_mix(1, (uint64_t)root);
  if (!cc_is_object_ptr(h, root)) return cc_mix(2, (uint64_t)root);
  cc_check_object(kind, ti, root, "root");
  if (!cc_deep) return cc_mix(3, ((header_t *)root)[-1]);
  size_t sp = 0;
  cc_stk = cc_grow(cc_stk, &cc_stkcap, 1, sizeof *cc_stk);
  cc_stk[sp++] = (uintptr_t)root;
  while (sp) {
    uintptr_t p = cc_stk[sp - 1];
    struct cc_ent *e = cc_lookup(p, 1);
    if (e->state == 2) { sp--; continue; }
    header_t hd = ((header_t *)p)[-1];
    uintnat n = hd >> 10;
    if (e->state == 0) {
      e->state = 1;
      for (uintnat i = 0; i < n; i++) {
        value f = ((value *)p)[i];
        if (((uintnat)f & 1) || !cc_is_object_ptr(h, f)) continue;
        struct cc_ent *fe = cc_lookup((uintptr_t)f, 0);
        if (fe && fe->state == 2) continue;
        CHECK(kind, "repr_val (values are finite trees/DAGs)", !(fe && fe->state == 1),
              "cycle through object %p", (void *)f);
        cc_check_object(kind, ti, f, Tag_hd(hd) >= No_scan_tag
          ? "field of a reachable object whose tag byte (ord & 0xFF) is >= No_scan_tag = 251; "
            "gc_stack.c does not scan the fields of such objects although tag_ok allows ord < 1024"
          : "field of a reachable object");
        cc_stk = cc_grow(cc_stk, &cc_stkcap, sp + 1, sizeof *cc_stk);
        cc_stk[sp++] = (uintptr_t)f;
      }
      continue;
    }
    /* all children done */
    uint64_t hh = cc_mix(3, hd);
    for (uintnat i = 0; i < n; i++) {
      value f = ((value *)p)[i];
      if ((uintnat)f & 1) hh = cc_mix(hh, cc_mix(1, (uint64_t)f));
      else if (!cc_is_object_ptr(h, f)) hh = cc_mix(hh, cc_mix(2, (uint64_t)f));
      else hh = cc_mix(hh, cc_lookup((uintptr_t)f, 0)->h);
    }
    e = cc_lookup(p, 0);  /* table may have been rehashed */
    e->h = hh; e->state = 2;
    cc_objs_hashed++;
    sp--;
  }
  return cc_lookup((uintptr_t)root, 0)->h;
}

/* ------------------------------------------------------------------ */
/* The caller's machine stack ("outside the heap, only the root slots are
   written"; [frames_of st' = frames_of st]).  We snapshot a window of the
   stack above garbage_collect's own frame -- the frames of the emitted code
   (its allocas: shadow-stack frames, root arrays) and of its callers -- and
   compare it after the collection, ignoring the root-slot bytes. */

#if defined(__clang__)
#define CC_NO_SANITIZE __attribute__((no_sanitize("address", "memory")))
#else
#define CC_NO_SANITIZE __attribute__((no_sanitize_address))
#endif

static size_t cc_stack_window;
static unsigned char *cc_stack_copy; static size_t cc_stack_copycap;
static uintptr_t cc_stack_lo, cc_stack_hi, cc_stack_top;

CC_NO_SANITIZE __attribute__((noinline))
static void cc_copy_words(unsigned char *dst, uintptr_t lo, uintptr_t hi) {
  volatile const uint64_t *s = (volatile const uint64_t *)lo;
  uint64_t *d = (uint64_t *)dst;
  for (size_t i = 0; i < (hi - lo) / 8; i++) d[i] = s[i];
}
CC_NO_SANITIZE __attribute__((noinline))
static uintptr_t cc_first_diff(const unsigned char *old, uintptr_t lo, uintptr_t hi, uintptr_t from) {
  volatile const uint64_t *s = (volatile const uint64_t *)lo;
  const uint64_t *d = (const uint64_t *)old;
  for (size_t i = (from - lo) / 8; i < (hi - lo) / 8; i++)
    if (d[i] != s[i]) return lo + 8 * i;
  return 0;
}

static int cc_is_root_slot(uintptr_t a) {
  for (size_t i = 0; i < cc_nroots; i++)
    if ((uintptr_t)cc_roots[i].slot <= a && a < (uintptr_t)cc_roots[i].slot + 8) return 1;
  return 0;
}

#if defined(__linux__)
#include <link.h>
static int cc_tls_size_cb(struct dl_phdr_info *info, size_t size, void *data) {
  (void)size;
  for (int i = 0; i < info->dlpi_phnum; i++)
    if (info->dlpi_phdr[i].p_type == PT_TLS) {
      size_t a = info->dlpi_phdr[i].p_align ? info->dlpi_phdr[i].p_align : 1;
      *(size_t *)data += (info->dlpi_phdr[i].p_memsz + a - 1) / a * a + a;
    }
  return 0;
}
#endif

/* The top (highest address) of the current thread's stack frames, or 0 if
   unknown (then the stack window check is skipped).
   For a thread made by pthread_create, glibc puts the thread descriptor
   (struct pthread, at the thread pointer = pthread_self()) and the static
   TLS blocks (just below it on x86-64) at the TOP of the stack block, and
   pthread_getattr_np reports the whole block.  TLS words (libc's and
   malloc's per-thread state) legitimately change while the collector runs,
   so they must not be in the window: clamp the top to below the thread
   pointer minus the static TLS of all loaded modules.  (Without this,
   shallow-stack GCs on such threads reported spurious "outside the heap only
   the root slots are written" violations at an address ~0xc0 below
   pthread_self().)  The main thread's TLS is not on its stack. */
static void cc_stack_bounds(void) {
  if (cc_stack_top) return;
#if defined(__linux__)
  pthread_attr_t at; void *addr; size_t sz;
  if (pthread_getattr_np(pthread_self(), &at) == 0) {
    if (pthread_attr_getstack(&at, &addr, &sz) == 0) cc_stack_top = (uintptr_t)addr + sz;
    pthread_attr_destroy(&at);
  }
  uintptr_t tp = (uintptr_t)pthread_self();
  if (cc_stack_top && tp < cc_stack_top && cc_stack_top - tp < ((uintptr_t)1 << 20)) {
    size_t tls = 0;
    dl_iterate_phdr(cc_tls_size_cb, &tls);
    cc_stack_top = (tp - tls - 64) & ~(uintptr_t)63;
  }
#elif defined(__APPLE__)
  cc_stack_top = (uintptr_t)pthread_get_stackaddr_np(pthread_self());
#endif
}

__attribute__((noinline))
static void cc_stack_snapshot(uintptr_t frame_top) {
  cc_stack_lo = cc_stack_hi = 0;
  if (!cc_stack_window) return;
  cc_stack_bounds();
  if (!cc_stack_top) return;
  uintptr_t lo = (frame_top + 7) & ~(uintptr_t)7;
  uintptr_t hi = lo + cc_stack_window;
  if (hi > cc_stack_top || hi < lo) hi = cc_stack_top & ~(uintptr_t)7;
  if (hi <= lo) return;
  cc_stack_copy = cc_grow(cc_stack_copy, &cc_stack_copycap, hi - lo, 1);
  cc_copy_words(cc_stack_copy, lo, hi);
  cc_stack_lo = lo; cc_stack_hi = hi;
  cc_live_add(lo, hi, "caller stack window");
}

static void cc_stack_compare(void) {
  if (!cc_stack_hi) return;
  uintptr_t from = cc_stack_lo, d;
  while ((d = cc_first_diff(cc_stack_copy, cc_stack_lo, cc_stack_hi, from)) != 0) {
    if (!cc_is_root_slot(d) && !cc_is_root_slot(d + 7))
      cc_violation(CC_POST, "runtime_correct (outside the heap only the root slots are written)",
                   "stack word at %p changed from %#lx to %#lx during GC (not a root slot)",
                   (void *)d, (unsigned long)*(uint64_t *)(cc_stack_copy + (d - cc_stack_lo)),
                   (unsigned long)*(volatile uint64_t *)d);
    from = d + 8;
  }
  cc_stack_bytes_checked += cc_stack_hi - cc_stack_lo;
}

/* ------------------------------------------------------------------ */
/* garbage_collect.  Clause 3 of [runtime_correct]. */

static void cc_walk_shadow_stack(const char *kind, struct thread_info *ti) {
  struct heap *h = ti->heap;
  uintptr_t t = (uintptr_t)ti;
  size_t depth = 0;
  cc_nframes = cc_nroots = 0;
  for (struct stack_frame *f = ti->fp; f != NULL; f = f->prev) {
    uintptr_t fa = (uintptr_t)f;
    CHECK(kind, "shadow_stack (frame pointer aligned)", fa % 8 == 0, "frame %p", (void *)f);
    CHECK(kind, "shadow_stack (frames are not heap objects: mem_ok_stmt)",
          !cc_touches_heap(h, fa, fa + sizeof *f) && !cc_overlap(fa, fa + sizeof *f, t, t + sizeof *ti),
          "frame struct %p lies in the GC heap / thread_info", (void *)f);
    /* termination: a cycle would make the chain infinite; bounded here,
       and repeated frames are detected in garbage_collect for chains of
       fewer than 4096 frames. */
    CHECK(kind, "shadow_stack (chain terminates at NULL)", depth < (1u << 26),
          "more than 2^26 frames: cycle in the prev chain?");
    uintptr_t s = (uintptr_t)f->root, e = (uintptr_t)f->next;
    CHECK(kind, "shadow_stack / slots_from (roots_start <= roots_end, 8-byte slots)",
          s <= e && (e - s) % 8 == 0 && s % 8 == 0,
          "frame %p: root=%p next=%p", (void *)f, (void *)s, (void *)e);
    CHECK(kind, "shadow_stack (root arrays are not in the heap: mem_ok_stmt)",
          s == e || (!cc_touches_heap(h, s, e) && !cc_overlap(s, e, t, t + sizeof *ti)),
          "frame %p: root array [%p,%p) lies in the GC heap / thread_info",
          (void *)f, (void *)s, (void *)e);
    CHECK(kind, "shadow_stack (frame struct disjoint from root arrays)",
          !cc_overlap(fa, fa + sizeof *f, s, e), "frame %p overlaps its own roots", (void *)f);
    size_t n = (e - s) / 8;
    cc_frames = cc_grow(cc_frames, &cc_capframes, cc_nframes + 1, sizeof *cc_frames);
    cc_frames[cc_nframes++] = (struct cc_frame){ f, *f, cc_nroots, n };
    cc_roots = cc_grow(cc_roots, &cc_caproots, cc_nroots + n, sizeof *cc_roots);
    for (size_t i = 0; i < n; i++)
      cc_roots[cc_nroots++] = (struct cc_root){ (value *)s + i, ((value *)s)[i], 0, 0, 0 };
    depth++;
  }
  if (depth > cc_max_depth) cc_max_depth = depth;
  if (cc_nroots > cc_max_roots) cc_max_roots = cc_nroots;
}

static void cc_init(void) {
  static int init;
  if (init) return;
  init = 1;
  atexit(cc_summary);
  cc_deep = (int)cc_env_long("CERTIROCQ_CHECK_DEEP", 1);
  cc_stack_window = (size_t)cc_env_long("CERTIROCQ_CHECK_STACK", 65536) & ~(size_t)7;
}

void garbage_collect(struct thread_info *ti) {
  cc_init();
  cc_gc_calls++;
  CHECK(CC_PRE, "tinfo_ok", ti != NULL, "garbage_collect(NULL)");

  /* ---- premises ---- */
  cc_check_tinfo(CC_PRE, ti);
  cc_check_mutator(ti);
  uintnat nalloc = ti->nalloc;
  CHECK(CC_PRE, "runtime_correct (0 <= nalloc < 2^61)", nalloc < ((uintnat)1 << 61),
        "nalloc = %lu", (unsigned long)nalloc);
  if (nalloc > cc_max_nalloc) cc_max_nalloc = nalloc;
  /* gc_stack.c never grows the nursery: resume() calls
     abort_with("Nursery is too small ...") = exit(1) when nalloc exceeds it.
     [runtime_correct] demands "room for nalloc words, or out-of-memory" for
     EVERY 0 <= nalloc < 2^61; a plain exit(1) is neither, so this is a
     (known) gap between gc_stack.c and the contract.  Report it as such
     instead of letting the run die with a generic message. */
  {
    struct space *s0 = &ti->heap->spaces[0];
    uintnat cap = (uintnat)(s0->rem_limit - s0->start);
    CHECK(CC_POST, "room (gc_stack.c cannot provide nalloc words: nursery too small; "
          "it would exit(1), which is neither room nor ends_in_oom)",
          nalloc <= cap, "nalloc = %lu words > nursery capacity %lu words",
          (unsigned long)nalloc, (unsigned long)cap);
  }
  struct stack_frame *fp0 = ti->fp;
  cc_walk_shadow_stack(CC_PRE, ti);
  /* the same frame must not occur twice (cycle) */
  for (size_t i = 0; i + 1 < cc_nframes && cc_nframes < 4096; i++)
    for (size_t j = i + 1; j < cc_nframes; j++)
      CHECK(CC_PRE, "shadow_stack (chain terminates at NULL)", cc_frames[i].f != cc_frames[j].f,
            "frame %p occurs twice", (void *)cc_frames[i].f);
  cc_tab_clear();
  for (size_t i = 0; i < cc_nroots; i++) {
    struct cc_root *r = &cc_roots[i];
    value w = r->before;
    cc_roots_checked++;
    if ((uintnat)w & 1) r->kind = R_UNBOXED;
    else if (!cc_is_object_ptr(ti->heap, w)) r->kind = R_EXTERNAL;
    else {
      r->kind = R_BOXED; cc_boxed_roots++;
      r->header = ((header_t *)w)[-1];
    }
    r->hash = cc_value_hash(CC_PRE, ti, w);
  }
  /* Known mismatch between the Rocq ABI and gc_stack.c: [tag_ok] allows
     ordinals up to 1023, and the header is arity<<10 | ord, but gc_stack.c
     reads the tag as hd & 0xFF and does NOT scan the fields of objects
     whose tag is >= No_scan_tag = 251.  An object with ordinal in
     {251..255, 507..511, 763..767, 1019..1023} and a pointer field into a
     from-space therefore gets a dangling field after the collection.  The
     deep comparison below catches the consequence; here we only count. */

  /* ---- snapshot ---- */
  cc_live_reset();
  cc_live_add((uintptr_t)ti, (uintptr_t)ti + sizeof *ti, "thread_info");
  for (int i = 0; i < (int)MAX_SPACES; i++) {
    struct space *s = &ti->heap->spaces[i];
    if (s->start) cc_live_add((uintptr_t)s->start, (uintptr_t)s->rem_limit, "GC space");
  }
  for (size_t i = 0; i < cc_nframes; i++) {
    cc_live_add((uintptr_t)cc_frames[i].f, (uintptr_t)(cc_frames[i].f + 1), "shadow-stack frame");
    cc_live_add((uintptr_t)cc_frames[i].fcopy.root, (uintptr_t)cc_frames[i].fcopy.next, "root array");
  }
  cc_stack_snapshot((uintptr_t)__builtin_frame_address(0) + 16);

  /* ---- the real collector ---- */
  cc_in_gc = 1;
  certirocq_real_garbage_collect(ti);
  cc_in_gc = 0;

#ifdef CERTIROCQ_CHECK_SELFTEST
  /* Test-only fault injection, to validate the POST checks themselves
     (CERTIROCQ_CHECK_SELFTEST=stack|frame|unboxed|deep at run time). */
  {
    const char *m = getenv("CERTIROCQ_CHECK_SELFTEST");
    if (m && !strcmp(m, "stack") && cc_stack_hi) {
      for (uintptr_t a = cc_stack_lo; a < cc_stack_hi; a += 8)
        if (!cc_is_root_slot(a)) { *(volatile uint64_t *)a ^= 0x10; break; }
    } else if (m && !strcmp(m, "frame") && cc_nframes) {
      cc_frames[0].f->next = cc_frames[0].f->root;
    } else if (m && !strcmp(m, "unboxed")) {
      for (size_t i = 0; i < cc_nroots; i++)
        if (cc_roots[i].kind == R_UNBOXED) { *cc_roots[i].slot += 2; break; }
    } else if (m && !strcmp(m, "deep")) {
      for (size_t i = 0; i < cc_nroots; i++)
        if (cc_roots[i].kind == R_BOXED) {
          value *o = (value *)*cc_roots[i].slot;
          for (uintnat j = 0; j < (((header_t *)o)[-1] >> 10); j++)
            if ((uintnat)o[j] & 1) { o[j] += 2; goto injected; }
        }
    injected:;
    }
  }
#endif

  /* ---- conclusions ---- */
  cc_stack_compare();
  CHECK(CC_POST, "runtime_correct (field st' tinfo off_fp fp: same fp)", ti->fp == fp0,
        "fp changed from %p to %p", (void *)fp0, (void *)ti->fp);
  CHECK(CC_POST, "runtime_correct (nalloc unchanged)", ti->nalloc == nalloc,
        "nalloc changed from %lu to %lu", (unsigned long)nalloc, (unsigned long)ti->nalloc);
  cc_check_tinfo(CC_POST, ti);
  CHECK(CC_POST, "room (limit - alloc >= 8 * nalloc)",
        (uintptr_t)ti->limit - (uintptr_t)ti->alloc >= 8 * nalloc,
        "limit - alloc = %lu bytes < 8 * nalloc = %lu",
        (unsigned long)((uintptr_t)ti->limit - (uintptr_t)ti->alloc), (unsigned long)(8 * nalloc));
  /* same shadow stack: same frames, same frame-struct bytes */
  {
    size_t k = 0;
    for (struct stack_frame *f = ti->fp; f != NULL && k <= cc_nframes; f = f->prev, k++) {
      CHECK(CC_POST, "shadow_stack st' fp rs (same frames)", k < cc_nframes && f == cc_frames[k].f,
            "frame #%zu is %p, was %p", k, (void *)f, k < cc_nframes ? (void *)cc_frames[k].f : NULL);
      CHECK(CC_POST, "shadow_stack st' fp rs (frame struct bytes unchanged)",
            memcmp(f, &cc_frames[k].fcopy, sizeof *f) == 0,
            "frame %p: {next,root,prev} changed from {%p,%p,%p} to {%p,%p,%p}", (void *)f,
            (void *)cc_frames[k].fcopy.next, (void *)cc_frames[k].fcopy.root,
            (void *)cc_frames[k].fcopy.prev, (void *)f->next, (void *)f->root, (void *)f->prev);
    }
    CHECK(CC_POST, "shadow_stack st' fp rs (same number of frames)", k == cc_nframes,
          "%zu frames after GC, %zu before", k, cc_nframes);
  }
  /* roots represent the same values */
  cc_tab_clear();
  for (size_t i = 0; i < cc_nroots; i++) {
    struct cc_root *r = &cc_roots[i];
    value w = *r->slot;
    switch (r->kind) {
    case R_UNBOXED:
      CHECK(CC_POST, "roots_ok (unboxed root unchanged)", w == r->before,
            "root slot %p was unboxed %#lx, now %#lx", (void *)r->slot,
            (unsigned long)r->before, (unsigned long)w);
      break;
    case R_EXTERNAL:
      CHECK(CC_POST, "roots_ok (non-heap pointer root, e.g. code pointer, unchanged)",
            w == r->before, "root slot %p was %#lx, now %#lx", (void *)r->slot,
            (unsigned long)r->before, (unsigned long)w);
      break;
    case R_BOXED:
      CHECK(CC_POST, "roots_ok (boxed root still a heap pointer)",
            !((uintnat)w & 1) && cc_is_object_ptr(ti->heap, w),
            "root slot %p was heap pointer %#lx, now %#lx", (void *)r->slot,
            (unsigned long)r->before, (unsigned long)w);
      cc_check_object(CC_POST, ti, w, "root after GC");
      CHECK(CC_POST, "roots_ok (boxed root keeps its header: same arity/ordinal)",
            ((header_t *)w)[-1] == r->header,
            "root slot %p: header %#lx became %#lx", (void *)r->slot,
            (unsigned long)r->header, (unsigned long)((header_t *)w)[-1]);
      break;
    }
    uint64_t hh = cc_value_hash(CC_POST, ti, w);
    CHECK(CC_POST, "roots_ok (roots represent the same values)", hh == r->hash,
          "root slot %p (#%zu, before %#lx, after %#lx, header %#lx): the value it represents "
          "changed during GC%s", (void *)r->slot, i, (unsigned long)r->before, (unsigned long)w,
          (unsigned long)r->header,
          (r->kind == R_BOXED && Tag_hd(r->header) >= No_scan_tag)
            ? " -- root's tag byte >= 251 (No_scan): gc_stack.c did not scan its fields" : "");
  }
  cc_record_exit(ti);
}
