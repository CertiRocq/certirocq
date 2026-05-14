#include "certirocq_runtime.h"

value closure_call(struct thread_info *tinfo, value clo, value arg) {
  certirocq_closure_fun func = (certirocq_closure_fun) Field(clo, 0);
  return func(tinfo, Field(clo, 1), arg);
}
