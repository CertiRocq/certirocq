#ifndef CERTIROCQ_RUNTIME_H
#define CERTIROCQ_RUNTIME_H

#include "values.h"

#define MAX_ARGS 1024

struct heap;

#ifdef CERTIROCQ_GENERATIONAL_GC
struct stack_frame;
#endif

struct thread_info {
  value *alloc;
  value *limit;
  struct heap *heap;
  value args[MAX_ARGS];
  uintnat nalloc;
  void *odata;
#ifdef CERTIROCQ_GENERATIONAL_GC
  struct stack_frame *fp;
#endif
};

struct thread_info *make_tinfo(void);

value closure_call(struct thread_info *, value, value);

#endif /* CERTIROCQ_RUNTIME_H */
