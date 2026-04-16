#include <stdio.h>
#include "gc_stack.h"
#include "glue_rec_clos2.h"


extern value body(struct thread_info *);

int main(int argc, char *argv[]) {
  value val;
  struct thread_info* tinfo;

  tinfo = make_tinfo();
  val = body(tinfo);

  print_Corelib_Init_Datatypes_list(val, print_Corelib_Init_Datatypes_nat);
  printf("\n");

  return 0;
}
