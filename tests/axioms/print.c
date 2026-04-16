#include "print.h"
#include "glue.h"

void print_gallina_nat(value v) {
  int n = 0;
  value *args;
  value val = v;
  
  unsigned long long tag = (get_Corelib_Init_Datatypes_nat_tag)(val);
  
  while (tag > 0) {
      n++;
      args = get_args(val);
      val = *args;
      tag = get_Corelib_Init_Datatypes_nat_tag(val);
    };

  printf("%d", n);
}

void print_new_line(value v) {
  printf("\n");
} 


void print_gallina_ascii(value chr) {
  int c = 0;
  unsigned long long d;

  value *args = get_args(chr);
  
  for (int i=7; i>=0; i--){
    c=c<<1;
    d = get_Corelib_Init_Datatypes_bool_tag(*(args + i));
    c+=d;
  }
  printf("%c", c);
}


void print_gallina_string(value str) {
  value *args;

  value chr;  
  value val = str;  

  unsigned long long tag = (get_Stdlib_Strings_String_string_tag)(val);
  
  while (tag > 0) {
      args = get_args(val);
      chr = *args;
      print_gallina_ascii(chr);
      val = *(args + 1);
      tag = get_Corelib_Init_Datatypes_nat_tag(val);
  };

}
