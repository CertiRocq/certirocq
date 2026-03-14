#include <stdio.h>
#include <stdlib.h>
#include "gc_stack.h"
#include <time.h>

extern void body(struct thread_info *);

extern value args[];

extern void init_gmp_alloc(struct thread_info *tinfo);

int main(int argc, char *argv[]) {
  // value val;
  struct thread_info* tinfo;
  clock_t start, end;
  double msec, sec;

  start = clock();
  tinfo = make_tinfo();
  /* init_gmp_alloc(tinfo); */
  body(tinfo);
  end = clock();

  // val = tinfo -> args[1];

  sec = (double)(end - start)/CLOCKS_PER_SEC;
  msec = 1000*sec;
  printf("Time taken %f seconds %f milliseconds\n", sec, msec);

  return 0;
}
