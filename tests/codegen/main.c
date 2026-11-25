#include <stdio.h>
#include "gc_stack.h"
#include "glue.h"

extern value body(struct thread_info *);

/* Prints a list of natural numbers, one per line */
int main(int argc, char *argv[]) {
  struct thread_info *tinfo;
  value l, n;
  unsigned long long k;

  tinfo = make_tinfo();
  l = body(tinfo);

  while (get_Corelib_Init_Datatypes_list_tag(l) > 0) {
    n = *((value *) get_args(l) + 0);
    k = 0;
    while (get_Corelib_Init_Datatypes_nat_tag(n) > 0) {
      ++k;
      n = *((value *) get_args(n) + 0);
    }
    printf("%llu\n", k);
    l = *((value *) get_args(l) + 1);
  }

  return 0;
}
