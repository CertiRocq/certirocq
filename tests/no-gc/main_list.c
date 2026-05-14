#include <stdio.h>

#include "certirocq_no_gc.h"

#define ARENA_WORDS 4096
#define EXPECTED_LENGTH 8

extern value body(struct thread_info *);

static value arena[ARENA_WORDS];

int main(void) {
  struct thread_info tinfo;
  value list;
  int length = 0;

  certirocq_no_gc_init(&tinfo, arena, ARENA_WORDS);

  list = body(&tinfo);
  while (Is_block(list)) {
    if (Wosize_val(list) != 2) {
      fprintf(stderr, "expected cons block with 2 fields, got %llu\n",
              (unsigned long long)Wosize_val(list));
      return 1;
    }
    if (Field(list, 0) != Val_long(1)) {
      fprintf(stderr, "expected true list element, got %lld\n",
              (long long)Field(list, 0));
      return 1;
    }
    length++;
    if (length > EXPECTED_LENGTH) {
      fprintf(stderr, "list longer than expected\n");
      return 1;
    }
    list = Field(list, 1);
  }

  if (list != Val_long(0)) {
    fprintf(stderr, "expected nil, got %lld\n", (long long)list);
    return 1;
  }
  if (length != EXPECTED_LENGTH) {
    fprintf(stderr, "expected length %d, got %d\n", EXPECTED_LENGTH, length);
    return 1;
  }

  return 0;
}
