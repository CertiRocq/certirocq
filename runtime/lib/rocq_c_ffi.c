#include <stdio.h>
#include <stdlib.h>
#include "rocq_c_ffi.h"
#include "gc/gc.h"
#include "values.h"

unsigned long long length_of_coq_string(value s) {
  unsigned long long ptr = s;
  register unsigned long long len = 0;
  while (Is_block(ptr)) {
    len += 1;
    ptr = (*((unsigned long long *) ptr + 1));
  }
  return len;
}

char* string_of_coq_string(value s) {
  register unsigned long long len = 0;
  unsigned long long ptr = s;
  unsigned long long chr;
  char * str;
  size_t size = (length_of_coq_string(s) + 1) * sizeof(char);
  str = (char *) malloc(size);
  if (str == NULL)
		fprintf(stderr, "malloc of %lu bytes failed:", size);
  while (Is_block(ptr)) {
    chr = (*((unsigned long long *) ptr));
    *(str + len) = (char) (chr >> 1LLU);
    len += 1;
    ptr = *((unsigned long long *) ptr + 1);
  }
  str[len] = '\0';
  return str;
}

value rocq_msg_info(value msg) {
  char *str = string_of_coq_string(msg);
  puts(str);
  free(str);
  return 1;
}

value rocq_user_error(value msg) {
  char *str = string_of_coq_string(msg);
  fputs(str, stderr);
  free(str);
  exit(1);
}

value rocq_msg_debug(value msg) {
  char *str = string_of_coq_string(msg);
  fputs(str, stdout);
  free(str);
  return 1;
}

value rocq_msg_notice(value msg) {
  char *str = string_of_coq_string(msg);
  fputs(str, stdout);
  free(str);
  return 1;
}
