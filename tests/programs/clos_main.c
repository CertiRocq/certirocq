#include <stdio.h>
#include "gc_stack.h"
#include "glue_clos.h"

extern value body(struct thread_info *);

int main(int argc, char *argv[]) {
  value val;
  struct thread_info* tinfo;

  tinfo = make_tinfo();
  val = body(tinfo);

  // TODO : fold over nat to print the C int
  print_Corelib_Init_Datatypes_nat(val);
  printf("\n");

  return 0;
}
