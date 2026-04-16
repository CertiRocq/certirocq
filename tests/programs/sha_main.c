#include <stdio.h>
#include "gc_stack.h"
#include "sha_glue.h"


extern value body(struct thread_info *);

int main(int argc, char *argv[]) {
  value val;
  struct thread_info* tinfo;

  tinfo = make_tinfo();
  val = body(tinfo);

  /* TODO write string printers */
  /* val = tinfo -> args[1]; */
  /* print_Corelib_Init_Datatypes_list(val, print_Corelib_Init_Datatypes_bool); */
  /* printf("\n"); */

  return 0;
}
