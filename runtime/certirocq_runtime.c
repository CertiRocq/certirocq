#include "certirocq_runtime.h"

/* A closure is a heap-allocated block whose first two words are a code
 * pointer and an environment value. closure_call reads those two words
 * and dispatches; it does not inspect the header. */
struct closure {
  value (*func)(struct thread_info *, value, value);
  value env;
};

value closure_call(struct thread_info *tinfo, value clo, value arg) {
  struct closure *c = (struct closure *) clo;
  return c->func(tinfo, c->env, arg);
}
