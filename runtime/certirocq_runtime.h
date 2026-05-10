#ifndef CERTIROCQ_RUNTIME_H
#define CERTIROCQ_RUNTIME_H

#include "values.h"

#define No_scan_tag 251
#define No_scan(t) ((t) >= No_scan_tag)

#define MAX_ARGS 1024

struct heap;

/* A frame of the shadow stack used to keep track of live roots. */
struct stack_frame {
  value *next;
  value *root;
  struct stack_frame *prev;
};

struct thread_info {
  value *alloc;
  value *limit;
  struct heap *heap;
  value args[MAX_ARGS];
  struct stack_frame *fp;
  uintnat nalloc;
  void *odata;
};

struct thread_info *make_tinfo(void);

void certirocq_modify(struct thread_info *ti, value *p_cell, value p_val);

value closure_call(struct thread_info *, value, value);

#endif /* CERTIROCQ_RUNTIME_H */
