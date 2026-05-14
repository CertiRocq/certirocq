#include "certirocq_no_gc.h"

void certirocq_no_gc_init(struct thread_info *tinfo,
                          value *arena,
                          size_t arena_words) {
  tinfo->alloc = arena;
  tinfo->limit = arena + arena_words;
}
