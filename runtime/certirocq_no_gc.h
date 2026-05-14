#ifndef CERTIROCQ_NO_GC_H
#define CERTIROCQ_NO_GC_H

#include "certirocq_runtime.h"

void certirocq_no_gc_init(struct thread_info *tinfo,
                          value *arena,
                          size_t arena_words);

#endif /* CERTIROCQ_NO_GC_H */
