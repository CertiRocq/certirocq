#include <stdio.h>
#include <stdlib.h>
#include "gc/gc.h"
#include <time.h>

extern value body(struct thread_info *);

extern value args[];

int main(int argc, char *argv[]) {
  value val;
  struct thread_info* tinfo;

  tinfo = make_tinfo();
  val = body(tinfo);

  return 0;
}
