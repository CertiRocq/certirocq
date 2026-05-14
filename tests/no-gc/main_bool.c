#include <stdio.h>

#include "certirocq_no_gc.h"

#define ARENA_WORDS 4096

extern value body(struct thread_info *);

static value arena[ARENA_WORDS];

int main(void) {
  struct thread_info tinfo;
  value result;
  value expected;

  certirocq_no_gc_init(&tinfo, arena, ARENA_WORDS);

  result = body(&tinfo);
  expected = Val_long(1);
  if (result != expected) {
    fprintf(stderr, "expected true (%lld), got %lld\n",
            (long long)expected, (long long)result);
    return 1;
  }

  return 0;
}
