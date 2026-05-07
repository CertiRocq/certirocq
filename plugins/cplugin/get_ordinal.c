#include "gc_stack.h"
#include <stdio.h>

value get_unboxed_ordinal(value $v)
{
  return Val_long($v);
}

intnat get_boxed_ordinal(value $v)
{
  return *((unsigned long long *) $v + 18446744073709551615LLU) & 255LLU;
}
