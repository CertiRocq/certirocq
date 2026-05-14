#ifndef CERTIROCQ_RUNTIME_H
#define CERTIROCQ_RUNTIME_H

#include "values.h"

#ifndef CERTIROCQ_MAX_ARGS
#ifdef MAX_ARGS
#define CERTIROCQ_MAX_ARGS MAX_ARGS
#else
#define CERTIROCQ_MAX_ARGS 1024
#endif
#endif

#if CERTIROCQ_MAX_ARGS <= 0
#error "CERTIROCQ_MAX_ARGS must be positive"
#endif

#if SIZEOF_CODE_PTR <= 0
#error "SIZEOF_CODE_PTR must be defined and positive"
#endif

#if SIZEOF_VALUE < SIZEOF_CODE_PTR
#error "SIZEOF_VALUE must be at least SIZEOF_CODE_PTR"
#endif

#ifndef MAX_ARGS
#define MAX_ARGS CERTIROCQ_MAX_ARGS
#endif

struct thread_info;

#ifdef CERTIROCQ_GENERATIONAL_GC
struct heap;
struct stack_frame;
#endif

/* Current closure ABI: the first closure field stores a C code pointer in one
 * value slot. Targets whose code pointers do not fit in value need a different
 * closure ABI, such as a generated code table. */
typedef value (*certirocq_closure_fun)(struct thread_info *, value, value);

struct thread_info {
  value *alloc;
  value *limit;
  value args[CERTIROCQ_MAX_ARGS];
#ifdef CERTIROCQ_GENERATIONAL_GC
  struct heap *heap;
  size_t nalloc;
  struct stack_frame *fp;
#endif
};

struct thread_info *make_tinfo(void);

value closure_call(struct thread_info *, value, value);

#endif /* CERTIROCQ_RUNTIME_H */
