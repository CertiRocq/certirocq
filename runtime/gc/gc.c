#include <stdlib.h>
#include <stdio.h>
#include <assert.h>
#include "m.h"  /* use printm.c to create m.h */
#include "config.h"
#include "values.h"
#include "gc.h"

/* A version of GC that scans a stack in order to find the roots. It is useful
 * when compiling direct-style programs
 */


/* The following 5 functions should (in practice) compile correctly in CompCert,
   but the CompCert correctness specification does not _require_ that
   they compile correctly:  their semantics is "undefined behavior" in
   CompCert C (and in C11), but in practice they will work in any compiler. */

int test_int_or_ptr (value x) /* returns 1 if int, 0 if aligned ptr */ {
    return (int)(((intnat)x)&1);
}

intnat int_or_ptr_to_int (value x) /* precondition: is int */ {
    return (intnat)x;
}

void * int_or_ptr_to_ptr (value x) /* precond: is aligned ptr */ {
    return (void *)x;
}

value int_to_int_or_ptr(intnat x) /* precondition: is odd */ {
    return (value)x;
}

value ptr_to_int_or_ptr(void *x) /* precondition: is aligned */ {
    return (value)x;
}

int is_ptr(value x) {
    return test_int_or_ptr(x) == 0;
}

/* A "space" describes one generation of the generational collector. 
struct space {
  value *start, *next, *limit, *rem_limit;
  };*/
/* Either start==NULL (meaning that this generation has not yet been created),
   or start <= next <= limit.  The words in start..next  are allocated
   and initialized, and the words from next..limit are available to allocate. */

#ifndef RATIO
#define RATIO 2   /* size of generation i+1 / size of generation i */
/*  Using RATIO=2 is faster than larger ratios, empirically */
#endif

/* Rationale for LOG_NURSERY_SIZE = 16:  
   The size of generation 0 (the "nursery") should approximately match the
   size of the level-2 cache of the machine, according to:
      Cache Performance of Fast-Allocating Programs,
      by Marcelo J. R. Goncalves and Andrew W. Appel.
      7th Int'l Conf. on Functional Programming and Computer Architecture,
      pp. 293-305, ACM Press, June 1995.
   We estimate this as 256 kilobytes
     (which is the size of the Intel Core i7 per-core L2 cache).
    http://www.tomshardware.com/reviews/Intel-i7-nehalem-cpu,2041-10.html
    https://en.wikipedia.org/wiki/Nehalem_(microarchitecture)
   Empirical measurements on Intel Core i7 in 32-bit mode show that NURSERY_SIZE=64k 4-byte words works well
    (or anything in the range from 32k to 128k).
   Some machines are radically different, however:
      Mac M2 "big" core has 64-bit words, L1 cache 128kB, shared L2 cache 16MB
      Mac M2 "small" core has 64-bit words, L1 cache 64kB, shared L2 cache 4MB
   On such machines the Goncalves rule of thumb may not apply; would be worth measuring
   performance with different nursery sizes, on realistic workloads.

*/


/* The definition of MAX_SPACES allows the largest generation to be as big 
   as half the entire address space.
   Here's the math: 8*sizeof(value) is the number of bits per word.
   Counting the nursery as generation 0, the largest generation is MAX_SPACES-1,
   and generation i+1 is twice as big as generation i.
   Therefore the number of bytes in the largest generation is,
      WORDSIZE*2^(MAX_SPACES-1)*NURSERY_SIZE
   = 2^(LOG_WORDSIZE + MAX_SPACES-1 + LOG_NURSERY_SIZE)
   = 2^(LOG_WORDSIZE + 8*WORDSIZE - (2+LOG_WORDDSIZE+LOG_NURSERY_SIZE) + LOG_NURSERY_SIZE)
   = 2^(8*WORDSIZE - 2)
   On a 64-bit machine this is 2^(64-2) = 2^62;  on a 32-bit machine it is 4*2^26 = 2^30.

   On a 32-bit machine, that's actually a problem!  We would like the largest generation
   to be as big as 2^31, so the sum of all the generations could approach 2^32, and we use
   the entire address space.  To make that work, we would have to reason more carefully
   about pointer subtractions; see NOTE-POINTER-ARITH below.  This could probably be done.
*/

#ifndef DEPTH
#define DEPTH 0  /* how much depth-first search to do */
#endif

#ifdef DEBUG

int in_heap(struct heap *h, value v) {
  int i;
  for (i=0; i<MAX_SPACES; i++)
    if (h->spaces[i].start != NULL)
      if (h->spaces[i].start <= (value*)v &&
	  (value *)v <= h->spaces[i].limit)
	return 1;
  return 0;
}

void printtree(FILE *f, struct heap *h, value v) {
  if(is_ptr(v))
    if (in_heap(h,v)) {
      header_t hd = Field(v,-1);
      int sz = Wosize_hd(hd);
      int i;
      fprintf(f,"%d(", Tag_hd(hd));
      for(i=0; i<sz-1; i++) {
        printtree(f,h,Field(v,i));
        fprintf(f,",");
      }
      if (i<sz)
        printtree(f,h,Field(v,i));
      fprintf(f,")");
    }
    else {
      fprintf(f,"%p",(void*)v);
    }
  else fprintf(f,"%ld",v>>1);
}

// XXX todo update for roots arrays
/* void printroots (FILE *f, struct heap *h, */
/* 		  fun_info fi,   /\* which args contain live roots? *\/ */
/* 		  struct thread_info *ti) /\* where's the args array? *\/ */
/*  { */
/*    value *args; int n; uintnat i, *roots; */
/*    roots = fi+2; */
/*    n = fi[1]; */
/*    args = ti->args; */

/*   for(i = 0; i < n; i++) { */
/*     fprintf(f,"%d[%8x]:",roots[i],args[roots[i]]); */
/*     printtree(f, h, args[roots[i]]); */
/*     fprintf(f,"\n"); */
/*   } */
/*   fprintf(f,"\n"); */
/* } */

#endif

void abort_with(char *s) {
  fprintf(stderr, "%s", s);
  exit(1);
}

int Is_from(value* from_start, value * from_limit,  value * v) {
    return (from_start <= v && v < from_limit);
}
/* Assuming v is a pointer (is_ptr(v)), tests whether v points
   somewhere into the "from-space" defined by from_start and from_limit */

void forward (value *from_start,  /* beginning of from-space */
	      value *from_limit,  /* end of from-space */
	      value **next,       /* next available spot in to-space */
	      value *p,           /* location of word to forward */
	      int depth)          /* how much depth-first search to do */
/* What it does:  If *p is a pointer, AND it points into from-space,
   then make *p point at the corresponding object in to-space.
   If such an object did not already exist, create it at address *next
    (and increment *next by the size of the object).
   If *p is not a pointer into from-space, then leave it alone.

   The depth parameter may be set to 0 for ordinary breadth-first
   collection.  Setting depth to a small integer (perhaps 10)
   may improve the cache locality of the copied graph.
*/
{
  value * v;
  value va = *p;
  if(is_ptr(va)) {
    v = (value*)int_or_ptr_to_ptr(va);
    /* printf("Start: %lld end"" %lld word %lld \n", from_start, from_limit, v); */
    /* if  (v == 4360698480) printf ("Found it\n"); */
    if(Is_from(from_start, from_limit, v)) {
      /* printf("Moving\n"); */
      header_t hd = Hd_val(v);
      if(hd == 0) { /* already forwarded */
        *p = Field(v,0);
      } else {
        intnat i;
        intnat sz;
        value *newv;
        sz = Wosize_hd(hd);
        newv = *next+1;
        *next = newv+sz;
	/*        if (sz > 50) printf("Moving value %p with tag %ld with %d fields\n", (void*)v, hd, sz); */
        Hd_val(newv) = hd;
        for(i = 0; i < sz; i++) {
          /* printf("Moving field %d\n", i); */
          Field(newv, i) = Field(v, i);
        }
        Hd_val(v) = 0;
	Field(v, 0) = ptr_to_int_or_ptr((void *)newv);
	*p = ptr_to_int_or_ptr((void *)newv);
        /* printf("New %lld\n", newv); */
        /* if (*p == 73832) printf("Found it\n"); */
        if (depth>0)
	  if (!No_scan(Tag_hd(hd)))
          for (i=0; i<sz; i++)
            forward(from_start, from_limit, next, &Field(newv,i), depth-1);
      }
    }
  }
}
void forward_remset (struct space *from,  /* descriptor of from-space */
                     struct space *to,    /* descriptor of to-space */
                     value **next)        /* next available spot in to-space */
{
  value *from_start = from->start, *from_limit=from->limit, *from_rem_limit=from->rem_limit;
  value *q = from_limit;
  assert (from_rem_limit-from_limit <= to->limit-to->start);
  while (q != from_rem_limit) {
    value *p = *(value**)q;
    if (!(from_start <= p && p < from_limit)) {
      value oldp= *p, newp;
      forward(from_start, from_limit, next, p, DEPTH);
      newp= *p;
      if (oldp!=newp)
          *(--to->limit) = (value)p;
    }
    q++;
  }
}

void forward_roots (value *from_start,  /* beginning of from-space */
                    value *from_limit,  /* end of from-space */
                    value **next,       /* next available spot in to-space */
                    struct stack_frame *frames) /* data structure to find the roots */
/* Forward each live root in the stack */
 {
   struct stack_frame *frame = frames;
   value *start; size_t i, limit;
   /* Scan the stack by traversing the stack pointers */

   while (frame != NULL) {
     start = frame->root;
     limit = frame->next - start; /* See NOTE-POINTER-ARITH below */
     frame = frame->prev;
     for (i=0; i<limit; i++)
        forward(from_start, from_limit, next, start+i, DEPTH);
   }
}

void do_scan(value *from_start,  /* beginning of from-space */
	     value *from_limit,  /* end of from-space */
	     value *scan,        /* start of unforwarded part of to-space */
 	     value **next)       /* next available spot in to-space */
/* Forward each word in the to-space between scan and *next.
  In the process, next may increase, so keep doing it until scan catches up.
  Leave alone:  header words, and "no_scan" (nonpointer) data.
*/
{
  value *s;
  s = scan;
  /* printf("in scan \n"); */
  while(s < *next) {
    header_t hd = *((header_t*)s);
    mlsize_t sz = Wosize_hd(hd);
    int tag = Tag_hd(hd);
    if (!No_scan(tag)) {
      intnat j;
      for(j = 1; j <= sz; j++) {
        forward (from_start, from_limit, next, &Field(s, j), DEPTH);
        /* printf("after \n"); */
      }
    }
    s += 1+sz;
  }
}

void do_generation (struct space *from,  /* descriptor of from-space */
                    struct space *to,    /* descriptor of to-space */
                    struct stack_frame *fr)  /* where are the roots? */
/* Copy the live objects out of the "from" space, into the "to" space,
   using fi and ti to determine the roots of liveness. */
{
  value *p = to->next;
  /*  assert(from->next-from->start + from->rem_limit-from->limit <= to->limit-to->next); */
  forward_remset(from, to, &to->next);
  forward_roots(from->start, from->limit, &to->next, fr);
  do_scan(from->start, from->limit, p, &to->next);
  #ifdef CERTIROCQ_DEBUG_GC
  fprintf(stderr,"%5.3f%% occupancy\n",
	  (to->next-p)/(double)(from->next-from->start));
  #endif
  from->next=from->start;
  from->limit=from->rem_limit;
}

#if 0
/* This "gensize" function is only useful if the desired ratio is >2,
   but empirical measurements show that ratio=2 is better than ratio>2. */
uintnat gensize(uintnat words)
/* words is size of one generation; calculate size of the next generation */
{
  uintnat maxint = 0u-1u;
  uintnat n,d;
  /* The next few lines calculate a value "n" that's at least words*2,
     preferably words*RATIO, and without overflowing the size of an
     unsigned integer. */
  /* minor bug:  this assumes sizeof(uintnat)==sizeof(void*)==sizeof(value) */
  if (words > maxint/(2*sizeof(value)))
    abort_with("Next generation would be too big for address space\n");
  d = maxint/RATIO;
  if (words<d) d=words;
  n = d*RATIO;
  assert (n >= 2*words);
  return n;
}
#endif

void create_space(struct space *s,  /* which generation to create */
		  uintnat n) /* size of the generation */
  /* malloc an array of words for generation "s", and
     set s->start and s->next to the beginning, and s->limit to the end.
  */

 {
  value *p;
  p = (value *)malloc(n * sizeof(value));
  if (p==NULL)
    abort_with ("Could not create the next generation\n");
  /*  fprintf(stderr, "Created a generation of %d words\n", n); */
  s->start=p;
  s->next=p;
  s->limit = p+n;
  s->rem_limit = s->limit;
}

struct heap *create_heap()
/* To create a heap, first malloc the array of space-descriptors,
   then create only generation 0.  */
{
  int i;
  struct heap *h = (struct heap *)malloc(sizeof (struct heap));
  if (h==NULL)
    abort_with("Could not create the heap\n");
  create_space(h->spaces+0, NURSERY_SIZE);
  for(i=1; i<MAX_SPACES; i++) {
    h->spaces[i].start = NULL;
    h->spaces[i].next = NULL;
    h->spaces[i].limit = NULL;
    h->spaces[i].rem_limit = NULL;
  }
  return h;
}

struct thread_info *make_tinfo(void) {
  struct heap *h;
  struct thread_info *tinfo;
  h = create_heap();
  tinfo = (struct thread_info *)malloc(sizeof(struct thread_info));
  if (!tinfo) 
    abort_with("Could not allocate thread_info struct\n");

  tinfo->heap=h;
  tinfo->alloc=h->spaces[0].start;
  tinfo->limit=h->spaces[0].limit;
  tinfo->fp=NULL; /* the initial stack pointer is NULL */
  tinfo->nalloc=0;
  tinfo->odata=NULL;
  return tinfo;
}

void resume(struct thread_info *ti)
/* When the garbage collector is all done, inform the mutator
   of the new values for the alloc and limit pointers,
   and check that enough space has been freed  (ti->nalloc words).
*/
 {
  struct heap *h = ti->heap;
  value *lo, *hi;
  uintnat num_allocs = ti->nalloc;
  assert (h);
  lo = h->spaces[0].start;
  hi = h->spaces[0].limit;
  if (hi-lo < num_allocs)   /* See NOTE-POINTER-ARITH below */
    abort_with ("Nursery is too small for function's num_allocs\n");
  ti->alloc = lo;
  ti->limit = hi;
  /* printf ("end gc\n"); */
}

void garbage_collect(struct thread_info *ti)
/* See the header file for the interface-spec of this function. */
{
  struct heap *h = ti->heap;
  /* printf("In GC\n"); */
  int i;
  h->spaces[0].limit = ti->limit;
  h->spaces[0].next = ti->alloc; /* this line is probably unnecessary */
  for (i=0; i<MAX_SPACES-1; i++) {
      /* Starting with the youngest generation, collect each generation
         into the next-older generation.  Usually, when doing that,
         there will be enough space left in the next-older generation
         so that we can break the loop by resuming the mutator. */

      /* If the next generation does not yet exist, create it */
      if (h->spaces[i+1].start==NULL) {
        intnat w = h->spaces[i].rem_limit-h->spaces[i].start;    /* See NOTE-POINTER-ARITH below */
        create_space(h->spaces+(i+1), RATIO*w);
      }
      /* Copy all the objects in generation i, into generation i+1 */
      #ifdef CERTIROCQ_DEBUG_GC
      fprintf(stderr, "Generation %d:  ", i);
      #endif
      do_generation(h->spaces+i, h->spaces+(i+1), ti->fp);
      /* If there's enough space in gen i+1 to guarantee that the
         NEXT collection into i+1 will succeed, we can stop here.
         We need enough space in the (unlikely) scenario where
	 * all the data in gen i is live ([i].limit-[i].start), and
	 * all the remembered set in i is preserved ([i].rem_limit-[i].limit).
      */
      if (h->spaces[i].rem_limit - h->spaces[i].start    /* See NOTE-POINTER-ARITH below */
          <= h->spaces[i+1].limit - h->spaces[i+1].next) {
        resume(ti);
        return;
      }
    }

  /* If we get to i==MAX_SPACES, that's bad news */
  /*  assert (MAX_SPACES == i); */
  abort_with("Ran out of generations\n");
}

/* REMARK.  The generation-management policy in the garbage_collect function
   has a potential flaw.  Whenever a record is copied, it is promoted to
   a higher generation.  This is generally a good idea.  But there is
   a bounded number of generations.  A useful improvement would be:
   when it's time to collect the oldest generation (and we can tell
   it's the oldest, at least because create_space() fails), do some
   reorganization instead of failing.
*/

void reset_heap (struct heap *h) {
  fprintf(stderr, "Debug: in reset_heap\n");
  int i;
  for (i=0; i<MAX_SPACES; i++)
    h->spaces[i].next = h->spaces[i].start;
}


void free_heap (struct heap *h) {
  fprintf(stderr, "Debug: in free_heap\n");
  int i;
  for (i=0; i<MAX_SPACES; i++) {
    value *p = h->spaces[i].start;
    if (p!=NULL)
      free(p);
  }
  free (h);
}

int garbage_collect_all(struct thread_info *ti) {
  struct heap *h = ti->heap;
  if (h==NULL) {
    h = create_heap();
    ti->heap = h;
  }
  int i;

  h->spaces[0].limit = ti->limit;
  h->spaces[0].next = ti->alloc;  /* this line more necessary here than perhaps in garbage_collect() */
  for (i=0; i < MAX_SPACES - 1 && h->spaces[i+1].start != NULL; i++)
    do_generation(h->spaces+i, h->spaces+(i+1), ti->fp);

  return i;
}

/* export_heap (deep copy if boxed) from the given root */
void *export_heap(struct thread_info *ti, value root) {


  /* This block of 7 lines is new (appel 2023/06/27) and untested */
  struct stack_frame frame;
  value roots[1];
  roots[0]=root;
  frame.root=roots;
  frame.next=roots+1;
  frame.prev=NULL;
  ti->fp= &frame;
  
  /* if root is unboxed, return it */
  if(!is_ptr(root))
    return (void *)root;

  /* otherwise collect all that is reachable from it to the last generation, then compact it into value_sp */
  int gen_level = garbage_collect_all(ti);
  struct space* sp = ti->heap->spaces+gen_level;
  struct space* fake_sp = (struct space*)malloc(sizeof(struct space));

  create_space(fake_sp, sp->next - sp->start);
  do_generation(sp, fake_sp, ti->fp);

  struct space* value_sp = (struct space*)malloc(sizeof(struct space));
  create_space(value_sp, fake_sp->next - fake_sp->start);
  do_generation(fake_sp, value_sp, ti->fp);

  /* offset start by the header */
  void* result_block = (void *)(value_sp->start +1);

  free(fake_sp->start);
  free(fake_sp);
  free(value_sp);

  return result_block;
}

/* mutable write barrier */
void certirocq_modify(struct thread_info *ti, value *p_cell, value p_val) {
  assert (ti->alloc < ti->limit);
  *p_cell = p_val;
  if (is_ptr(p_val)) {
    *(value **)(--ti->limit) = p_cell;
  }
}

void print_heapsize(struct thread_info *ti) {
  for (int i = 0; i < MAX_SPACES; i++) {
    int allocated = (int)(ti->heap->spaces[i].next - ti->heap->spaces[i].start);
    int remembered = (int)(ti->heap->spaces[i].rem_limit - ti->heap->spaces[i].limit);
    if (!(allocated || remembered)) {
      continue;
    }
    printf("generation %d:\n", i);
    printf("  size: %d\n", (int)(ti->heap->spaces[i].rem_limit - ti->heap->spaces[i].start));
    printf("  allocated: %d\n", allocated);
    printf("  remembered: %d\n", remembered);
  }
}

/* NOTE-POINTER-ARITH:  In a few places, we do a pointer subtraction, such as
       h->spaces[i].limit - h->spaces[i].start.
 When p and q have type  *foo,  then this is much like  ((int)p-(int)q)/sizeof(foo).
 But note this is a SIGNED division, which makes it quite dangerous if ((int)p-(int)q)
 can be larger than the maximum signed integer.  So we have to be quite careful in
 the program and the proof, especially when (on a 32-bit machines) our largest generation 
 might be similar in size to the entire address space. 
*/

struct closure {
  value (*func)(struct thread_info *, value, value);
  value env;
};

value closure_call(struct thread_info *$tinfo, value $clo, value $arg)
{
  register value (*$f)(struct thread_info*, value, value);
  register value $envi;
  register value $tmp;
  $f = (*((struct closure *) $clo)).func;
  $envi = (*((struct closure *) $clo)).env;
  $tmp = $f($tinfo, $envi, $arg);
  return $tmp;
}
