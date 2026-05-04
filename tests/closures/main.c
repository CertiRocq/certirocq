#include <stdio.h>
#include <stdlib.h>
#include "gc_stack.h"

extern value body(struct thread_info *);

int main(int argc, char *argv[]) {
  struct thread_info *tinfo;

  tinfo = make_tinfo();
  body(tinfo);

  return 0;
}
