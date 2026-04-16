#include <stdio.h>
#include "gc_stack.h"
#include "glue_color.h"

extern value body(struct thread_info *);

int main(int argc, char *argv[]) {
  value val;
  struct thread_info* tinfo;

  tinfo = make_tinfo();
  val = body(tinfo);

  // TODO : fold over nat to print the C int
  print_Corelib_Init_Datatypes_prod(val, print_Corelib_Numbers_BinNums_Z, print_Corelib_Numbers_BinNums_Z);
  printf("\n");

  return 0;
}
