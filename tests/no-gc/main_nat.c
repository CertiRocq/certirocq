#include <stdio.h>

#include "certirocq_no_gc.h"

#define ARENA_WORDS 4096
#define EXPECTED_NAT 26

extern value body(struct thread_info *);

static value arena[ARENA_WORDS];

static int nat_value(value v, int *out) {
  int n = 0;

  while (Is_block(v)) {
    if (Wosize_val(v) != 1) {
      return 0;
    }
    n++;
    if (n > EXPECTED_NAT) {
      return 0;
    }
    v = Field(v, 0);
  }

  if (v != Val_long(0)) {
    return 0;
  }

  *out = n;
  return 1;
}

int main(void) {
  struct thread_info tinfo;
  value result;
  int n = 0;

  certirocq_no_gc_init(&tinfo, arena, ARENA_WORDS);

  result = body(&tinfo);
  if (!nat_value(result, &n)) {
    fprintf(stderr, "result is not a valid nat encoding\n");
    return 1;
  }
  if (n != EXPECTED_NAT) {
    fprintf(stderr, "expected nat %d, got %d\n", EXPECTED_NAT, n);
    return 1;
  }

  return 0;
}
