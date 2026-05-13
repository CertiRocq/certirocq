#include <stdio.h>
#include <stdlib.h>
#include "gc/gc.h"
#include <caml/mlvalues.h>
#include <caml/memory.h>
#include <caml/alloc.h>
#include <time.h>
#include <caml/callback.h>

extern value body(struct thread_info *);

extern value *call(struct thread_info *, value, value);

value copy_value(value v) {
  CAMLparam0();
  CAMLlocal1 (result);

  if (Is_long(v)) {
    // printf ("Copying immediate int of value %i\n", Long_val(v));
    result = v;
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
  res = copy_value(restemp);
  free_heap(tinfo->heap);
  printf("Value copied to OCaml heap\n");
  
  CAMLreturn(res);
}
