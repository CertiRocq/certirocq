#include "certirocq_no_gc.h"

void certirocq_no_gc_init(struct thread_info *tinfo,
                          value *arena,
                          mlsize_t arena_words) {
  tinfo->alloc = arena;
  tinfo->limit = arena + arena_words;
  tinfo->heap = 0;
  tinfo->nalloc = 0;
#ifdef CERTIROCQ_GENERATIONAL_GC
  tinfo->fp = 0;
#endif
}
