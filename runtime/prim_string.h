#include "values.h"
#include "prim_int63.h"

#ifndef PRIM_STRING_H
#define PRIM_STRING_H 1

#define String_tag 252

typedef value primstring;

intnat prim_strlen(primstring s);

// Encodes the string as a block, with special padding
value mk_ocaml_string (struct thread_info *tinfo, char* str);


extern value prim_string_compare(primstring x);
extern primint prim_string_get(primstring x, primint y);
extern primint prim_string_length(primstring x);
extern primint prim_string_max_length();
extern primstring prim_string_make(primint x, primint ch);
extern primstring prim_string_sub(primstring x, primint from, primint len);
extern primstring prim_string_cat(primstring x, primstring y);

#endif // PRIM_STRING_H
