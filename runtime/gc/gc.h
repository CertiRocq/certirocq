#ifndef CERTIROCQ_GC_STACK_H
#define CERTIROCQ_GC_STACK_H

/* Defining CERTIROCQ_GENERATIONAL_GC before including certirocq_runtime.h
 * makes the GC-only fields of thread_info (nalloc, heap, fp) and the
 * stack_frame struct visible. Including this header is the canonical
 * way to opt in. */
#define CERTIROCQ_GENERATIONAL_GC 1

#include "certirocq_runtime.h"

#if SIZEOF_VALUE != SIZEOF_PTR
#error "The generational GC currently requires SIZEOF_VALUE == SIZEOF_PTR"
#endif

/* A frame of the shadow stack used to keep track of live roots. */
struct stack_frame {
  value *next;
  value *root;
  struct stack_frame *prev;
};

/* EXPLANATION OF THE CERTIROCQ GENERATIONAL GARBAGE COLLECTOR.
 Andrew W. Appel, September 2016

The current Certirocq code generator uses Ocaml object formats,
as described in Chapter 20 of Real World Ocaml by Minsky et al.
https://realworldocaml.org/v1/en/html/memory-representation-of-values.html

That is:

       31   10 9       8 7        0
      +-------+---------+----------+
      | size  |  color  | tag byte |
      +-------+---------+----------+
v --> |              value[0]      |
      +----------------------------+
      |              value[1]      |
      +----------------------------+
      |                   .        |
      |                   .        |
      |                   .        |
      +----------------------------+
      |           value[size-1]    |
      +----------------------------+

This works for 32-bit or 64-bit words;
if 64-bit words, substitute "63" for "31" in the diagram above.
At present we'll assume 32-bit words.

The header file "values.h", from the OCaml distribution,
has macros (etc.) for accessing these fields and headers.

The important definitions we use from values.h are:

Is_block(v) : tests whether v is a pointer (even number)
Hd_val(v)   : contents of the header word, i.e., just before where v points to
Field(v,i)  : the i'th field of object v
Tag_hd(h)   : If h is a header-word, get the constructor-tag
Wosize_hd(h): If h is a header-word, get size of the object in words

We define the following ourselves, following Ocaml's format:

No_scan(t)  : If t is a constructor-tag, true if none of the object's
              data words are to be interpreted as pointers.
	      (For example, character-string data)

CALLING THE GARBAGE COLLECTOR (this part is NOT standard Ocaml):

The mutator runs in this environment:

                                 NURSERY              OLDER GENERATIONS
      +-------------+  start---->+-------------+      +-------------+
      |    args[0]  |            |             |      |             |
      +-------------+            | <-\         |  /-->|             |
      |    args[1] *----\        |   |       *---/    |             |
      +-------------+    \-----> | *-/         |      |             |
      |      .      |       +-+  |             |      |             |
      |      .      |  alloc|*-->+-------------+      |             |
      |      .      |       +-+  |             |      |             |
      +-------------+            |             |      |             |
      | args[argc-1]|       +-+  |             |      |             |
      +-------------+  limit|*-->+-------------+      |             |
                            +-+                       +-------------+

There is a global "args" array.  Certain words in "args" may
point into the heap (either the nursery or into older generations).
The nursery may point within itself, or into older generations.
Older generations may not point into the nursery.
The heap may not point into the args array.

The mutator creates a new object by using the N+1 words (including header)
starting at "alloc", and then adding N+1 to alloc.  This is only
permitted if alloc+N+1 <= limit.  Otherwise, the mutator must
first call the garbage collector.

The variables "alloc" and "limit" are owned by the mutator.
The "start" value is not actually a variable of the mutator,
but it was the value of "alloc" immediately after the most
recent collection.

To call the garbage collector, the mutator passes a thread_info,
as follows. */

/* ideally struct heap should be more abstract (opaque)
      struct heap;
  and ideally, the following definitions should live in gc.c rather than gc.h:
*/
#if SIZEOF_PTR == 8
#define LOG_WORDSIZE 3
#elif SIZEOF_PTR == 4
#define LOG_WORDSIZE 2
#else
#error "Unsupported SIZEOF_PTR for generational GC"
#endif
#define LOG_NURSERY_SIZE 16
#define NURSERY_SIZE (1<<LOG_NURSERY_SIZE)
#define MAX_SPACES (8*sizeof(value)-(2+LOG_WORDSIZE+LOG_NURSERY_SIZE)) /* how many generations */

struct space { value *start, *next, *limit, *rem_limit; };
struct heap {  struct space spaces[MAX_SPACES]; };
/* END of the stuff that would ideally be more opaque */

void garbage_collect(struct thread_info *ti);
/* Performs one garbage collection;
   or if ti->heap==NULL, initializes the heap.

 The returns in a state where
 (1) the "after" graph of nodes reachable from args[indices[0..num_args]]
    is isomorphic to the "before" graph; and
 (2) the alloc pointer points to N words of unallocated heap space
  (where N>=num_allocs), such that limit-alloc=N.
*/

void free_heap(struct heap *h);
/* Deallocates all heap data associated with h, and returns the
 * memory to the operating system (via the malloc/free system).
 * After calling this function, h is a dangling pointer and should not be used.
 */

void reset_heap(struct heap *h);
/* Empties the heap without freeing its storage.
 * After a complete execution of the mutator,
 * and after whoever invoked the mutator copies whatever result they want
 * out of the heap, one can call this function before starting
 * another mutator execution.  This saves the operating-system overhead of
 * free_heap() followed by the implicit create_heap that would have been
 * done in the first garbage_collect() call of the next execution.
 */

void* export_heap(struct thread_info *ti, value root);

void print_heapsize(struct thread_info *ti);

void certirocq_modify(struct thread_info *ti, value *p_cell, value p_val);

#endif /* CERTIROCQ_GC_STACK_H */
