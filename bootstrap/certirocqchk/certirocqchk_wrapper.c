#include <stdio.h>
#include <stdlib.h>
#include "values.h"
#include "gc.h"
/* OCaml 5.2 defines Hd_val as a function, not a macro. */
#undef Hd_val
#include <caml/memory.h>
#include <caml/minor_gc.h>
#include <time.h>
#include <caml/callback.h>
#include <caml/threads.h>
#include <pthread.h>

extern value body(struct thread_info *);

extern value *call(struct thread_info *, value, value);

/* The compiled checker recurses deeply, more than the main thread's stack allows on
   systems where it cannot be raised enough (it is capped at 64MB on macOS). We run it on
   a thread with a stack of CERTIROCQCHK_STACK_SIZE megabytes instead (4GB by default). */
#define DEFAULT_STACK_SIZE_MB 4096

struct checker_call {
  value prog, res; /* The result is a boolean, which needs no root */
  int ran;
};

static value run_checker(value prog);

static void *checker_thread(void *arg) {
  struct checker_call *c = arg;
  if (!caml_c_thread_register()) return NULL;
  caml_acquire_runtime_system();
  c->res = run_checker(c->prog);
  c->ran = 1;
  caml_release_runtime_system();
  caml_c_thread_unregister();
  return NULL;
}

static size_t checker_stack_size(void) {
  const char *s = getenv("CERTIROCQCHK_STACK_SIZE");
  size_t mb = s != NULL ? strtoul(s, NULL, 10) : 0;
  return (mb > 0 ? mb : DEFAULT_STACK_SIZE_MB) * 1024 * 1024;
}

// external : (coq_Options × ExtractedASTBaseQuoter.quoted_program) -> bool = "certirocqchk_wrapper"
CAMLprim value certirocqchk_wrapper(value prog) {
  CAMLparam1 (prog);
  struct checker_call c;
  pthread_attr_t attr;
  pthread_t thread;
  int created;

  // The checker reads the input, which must not move while it runs
  caml_minor_collection();

  // Only now that it has been promoted can the argument be read without the root
  c.prog = prog;
  c.res = Val_false;
  c.ran = 0;

  pthread_attr_init(&attr);
  created = pthread_attr_setstacksize(&attr, checker_stack_size()) == 0;
  caml_release_runtime_system();
  created = created && pthread_create(&thread, &attr, checker_thread, &c) == 0;
  if (created) pthread_join(thread, NULL);
  caml_acquire_runtime_system();
  pthread_attr_destroy(&attr);

  if (!c.ran) {
    printf("could not run the checker on a large stack, using the current one\n");
    c.res = run_checker(prog);
  }

  CAMLreturn(c.res);
}

static value run_checker(value prog) {
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
