#include <stdio.h>
#include "gc.h"


extern void body(struct thread_info *);

extern void print_Corelib_Init_Datatypes_bool(unsigned long long);

extern void print_CertiRocq_Tests_lib_vs_space_atom(unsigned long long);

extern unsigned int get_Corelib_Init_Datatypes_list_tag(unsigned long long);

extern value args[];

extern void print_Corelib_Init_Datatypes_list(unsigned long long, void (*)(unsigned long long));

extern void print_CertiRocq_Tests_lib_vs_clause(unsigned long long);

void print_elem(unsigned long long v)
{
  printf(".");
}

void print_list(unsigned long long l)
{
  print_Corelib_Init_Datatypes_list(l, print_elem);
  printf("\n");
}

void print_list_space_atom(unsigned long long l)
{
  print_Corelib_Init_Datatypes_list(l, print_CertiRocq_Tests_lib_vs_space_atom);
  printf("\n");
}

void print_list_clause(unsigned long long l)
{
  print_Corelib_Init_Datatypes_list(l, print_CertiRocq_Tests_lib_vs_clause);
  printf("\n");
}



int main(int argc, char *argv[]) {
  value val;
  struct thread_info* tinfo;

  tinfo = make_tinfo();
  body(tinfo);

  val = tinfo -> args[1];
  // TODO : fold over nat to print the C int
  print_Corelib_Init_Datatypes_bool(val);
  printf("\n");

  return 0;
}
