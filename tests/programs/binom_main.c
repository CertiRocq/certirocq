#include <stdio.h>
#include "gc_stack.h"
#include "glue_binom.h"


extern value body(struct thread_info *);

int main(int argc, char *argv[]) {
  value val;
  struct thread_info* tinfo;

  tinfo = make_tinfo();
  val = body(tinfo);

  unsigned long long num = 0;
  unsigned long long tag = get_Corelib_Init_Datatypes_nat_tag(val);

  while (tag > 0) {
    ++num;
    val = *((value *) get_args(val) + 0);
    tag = get_Corelib_Init_Datatypes_nat_tag(val);
  }
  printf("%d\n", num);

  return 0;
}
