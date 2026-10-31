#define _GNU_SOURCE /* for dl_iterate_phdr */
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include "gc_stack.h"
/* OCaml 5.2 defines Hd_val as a function, not a macro. */
#undef Hd_val
#include <caml/mlvalues.h>
#include <caml/memory.h>
#include <caml/alloc.h>
#include <caml/minor_gc.h>
#include <time.h>
#include <caml/callback.h>
#if defined(__APPLE__)
#include <dlfcn.h>
#include <mach-o/getsect.h>
#elif defined(__linux__)
#include <link.h>
#endif

extern value body(struct thread_info *);

extern value *call(struct thread_info *, value, value);

/* Besides blocks of the CertiRocq heap, the result of the compiler can point to OCaml values of
   the input, which are kept as they are, and to code: MetaRocq implements erased proofs (boxes)
   as closures. The OCaml side never inspects erased proofs, so pointers to code become unit. */
static struct heap *certirocq_heap;
static uintptr_t code_start, code_end;

static int in_certirocq_heap(value v) {
  size_t i;
  for (i = 0; i < MAX_SPACES; i++) {
    struct space *s = &certirocq_heap->spaces[i];
    if (s->start != NULL && (value *) v >= s->start && (value *) v < s->rem_limit)
      return 1;
  }
  return 0;
}

#if defined(__linux__)
static int find_code_segment(struct dl_phdr_info *info, size_t size, void *f) {
  int i;
  for (i = 0; i < info->dlpi_phnum; i++) {
    const ElfW(Phdr) *ph = &info->dlpi_phdr[i];
    uintptr_t start = info->dlpi_addr + ph->p_vaddr;
    if (ph->p_type == PT_LOAD && (ph->p_flags & PF_X) &&
        start <= (uintptr_t) f && (uintptr_t) f < start + ph->p_memsz) {
      code_start = start;
      code_end = start + ph->p_memsz;
      return 1;
    }
  }
  return 0;
}
#endif

/* Finds the code segment of the compiled compiler. */
static void find_code(void) {
#if defined(__APPLE__)
  Dl_info info;
  unsigned long size;
  if (dladdr((void *) body, &info)) {
    code_start = (uintptr_t) getsegmentdata((const struct mach_header_64 *) info.dli_fbase, "__TEXT", &size);
    code_end = code_start + size;
  }
#elif defined(__linux__)
  dl_iterate_phdr(find_code_segment, (void *) body);
#endif
}

value copy_value(value v) {
  CAMLparam0();
  CAMLlocal1 (result);

  if (Is_long(v)) {
    // printf ("Copying immediate int of value %i\n", Long_val(v));
    result = v;
  }
  else if (!in_certirocq_heap(v)) {
    result = ((uintptr_t) v >= code_start && (uintptr_t) v < code_end) ? Val_unit : v;
  }
  else {
    mlsize_t size = Wosize_val(v);
    unsigned char tag = Tag_val(v);
    
    // printf ("Copying object of tag %i and size %i \n", tag, size);
    
    result = caml_alloc(size, tag);
    int i;
    for (i = 0; i < size; i++) {
      // printf ("Copying field %i of block of tag %i\n", i, tag);
      Store_field(result, i, copy_value (Field(v, i)));
    }
  }
  
  CAMLreturn (result);
}

// external certirocq_pipeline : (coq_Options × ExtractedASTBaseQuoter.quoted_program) -> coq_Cprogram error * Bytestring.String.t = "certirocq_pipeline"
CAMLprim value certirocq_pipeline_wrapper(value opts, value prog) {
  CAMLparam2 (opts, prog);
  CAMLlocal1 (res);
  value closure;
  value restemp;
  struct thread_info* tinfo;
  clock_t start, end;
  double msec, sec;
  start = clock();
  
  // The result can point to the input, which must not move while the result is copied
  caml_minor_collection();

  // Run Coq program
  tinfo = make_tinfo();
  printf("about to call compiler\n");
  closure = body(tinfo);
  closure = call(tinfo, closure, opts);
  restemp = call(tinfo, closure, prog);
  printf("compiler returned a value\n");
  end = clock();

  sec = (double)(end - start)/CLOCKS_PER_SEC;
  msec = 1000*sec;
  printf("Time taken %f seconds %f milliseconds\n", sec, msec);

  printf("Copying value to OCaml heap\n");
  certirocq_heap = tinfo->heap;
  find_code();
  res = copy_value(restemp);
  free_heap(tinfo->heap);
  printf("Value copied to OCaml heap\n");
  
  CAMLreturn(res);
}
