#include <stdio.h>
#include <stdlib.h>
#include "values.h"
#include "gc/gc.h"
#include <caml/memory.h>
#include <time.h>
#include <caml/callback.h>

extern value body(struct thread_info *);

extern value *call(struct thread_info *, value, value);

// external : (coq_Options × ExtractedASTBaseQuoter.quoted_program) -> bool = "certirocqchk_wrapper"
CAMLprim value certirocqchk_wrapper(value prog) {
  CAMLparam1 (prog);
  CAMLlocal1 (res);
  value closure;
  struct thread_info* tinfo;
  clock_t start, end;
  double msec, sec;
  start = clock();
  
  // Run Coq program
  tinfo = make_tinfo();
  printf("about to call checker\n");
  closure = body(tinfo);
  // closure = call(tinfo, closure, opts); takes only a single program argument today
  res = call(tinfo, closure, prog);
  printf("checker returned a value\n");
  end = clock();

  sec = (double)(end - start)/CLOCKS_PER_SEC;
  msec = 1000*sec;
  printf("Time taken %f seconds %f milliseconds\n", sec, msec);

  CAMLreturn(res);
}
