#include <assert.h>
#include <stdio.h>
#include <string.h>
#include <stdlib.h>
#include "gc_stack.h"
#include "prim_int63.h"

#define String_tag 252

typedef value primstring;

#define trace(...) printf(__VA_ARGS__)

intnat prim_strlen(primstring s) {
  // number_of_words_in_block * sizeof(word) - last_byte_of_block - 1
  /* returns a number of bytes (chars) */
  intnat temp;
  temp = Bosize_val(s) - 1;
  return temp - Byte (s, temp);
}

value prim_string_compare(primstring x, primstring y)
{
  trace("Calling prim_string_compare\n");
  intnat lenx = prim_strlen(x);
  intnat leny = prim_strlen(y);
  intnat cmp = 0;
  if (lenx == leny) {
    for (intnat i = 0; i < lenx; i++) {
      cmp = Byte(x, i) - Byte (y, i);
      if (cmp != 0) { return cmp; };
    }
    return 0;
  }
  { return Val_long (lenx - leny); }
}

primint prim_string_get(primstring x, primint i)
{
  return Val_long(Byte(x, Long_val(i)));
}

primint prim_string_length(primstring x)
{
  return Val_long(prim_strlen(x));
}

primint prim_string_max_length() {
  return Val_long(0xfffff);
}

value mk_ocaml_string (struct thread_info *tinfo, char* str) {
  register value *$alloc;
  register value *$limit;
  unsigned long long len = strlen(str); // bytes
  unsigned int words = (len / 8) + 1;
  $limit = (*tinfo).limit;
  $alloc = (*tinfo).alloc;
  if (!(words + 1 <= $limit - $alloc)) {
    /*skip*/;
    (*tinfo).nalloc = words + 1;
    garbage_collect(tinfo);
    /*skip*/;
    $alloc = (*tinfo).alloc;
    $limit = (*tinfo).limit;
  }
  assert (words + 1 <= $limit - $alloc);
  *($alloc + 0LLU) = String_tag | (words << 10);
  int i = 0;
  char *strp = (char*) ($alloc + 1LLU);
  for (i = 0; i < len; i++) {
    strp[i] = str[i];
  }
  // Fill remaining bytes with 0s. End with the number of 0s to trim to compute the length
  int j = i;
  for (; ((j + 1) / 8) < words; j++)
  { strp[j] = (char) 0; }
  strp[j] = (char) (j - i);
  (*tinfo).alloc = (*tinfo).alloc + words + 1;
  return (value) ((unsigned long long *) $alloc + 1LLU);
}

primstring prim_string_make(struct thread_info* tinfo, primint bytes, primint d) {
  register value *$alloc;
  register value *$limit;
  char ch = (char) d; // Truncate to char
  $limit = (*tinfo).limit;
  $alloc = (*tinfo).alloc;
  unsigned long long words = (bytes / 8) + 1;
  if (!(words <= $limit - $alloc)) {
    /*skip*/;
    (*tinfo).nalloc = words;
    garbage_collect(tinfo);
    /*skip*/;
    $alloc = (*tinfo).alloc;
    $limit = (*tinfo).limit;
  }
  assert (words <= $limit - $alloc);
  *($alloc + 0LLU) = String_tag | (words << 10);
  int i = 0;
  char *strp = (char*) ($alloc + 1LLU);
  for (i = 0; i < bytes; i++) {
    strp[i] = ch;
  }
  // Fill remaining bytes with 0s.
  // End with the number of 0s to trim to compute the length
  int j = i;
  for (; ((j + 1) / 8) < words; j++)
  { strp[j] = (char) 0; }
  strp[j] = j - i;
  (*tinfo).alloc = (*tinfo).alloc + words;
  return (value) ((unsigned long long *) $alloc + 1LLU);
}

primstring prim_string_sub(struct thread_info* tinfo, primstring x,
                           primint from, primint len) {
  register value *$alloc;
  register value *$limit;
  $limit = (*tinfo).limit;
  $alloc = (*tinfo).alloc;
  unsigned long long words = (len / 8) + 1;
  if (!(words <= $limit - $alloc)) {
    /*skip*/;
    (*tinfo).nalloc = words;
    garbage_collect(tinfo);
    /*skip*/;
    $alloc = (*tinfo).alloc;
    $limit = (*tinfo).limit;
  }
  assert (words <= $limit - $alloc);
  *($alloc + 0LLU) = String_tag | (words << 10);
  int i = 0;
  char *strp = (char*) ($alloc + 1LLU);
  for (i = 0; i < len; i++) {
    strp[i] = Bp_val(x)[from + i];
  }
  // Fill remaining bytes with 0s.
  // End with the number of 0s to trim to compute the length
  int j = i;
  for (; ((j + 1) / 8) < words; j++)
  { strp[j] = (char) 0; }
  strp[j] = j - i;
  (*tinfo).alloc = (*tinfo).alloc + words;
  return (value) ((unsigned long long *) $alloc + 1LLU);
}

primstring prim_string_cat(struct thread_info* tinfo, primstring x, primstring y) {
  register value *$alloc;
  register value *$limit;
  $limit = (*tinfo).limit;
  $alloc = (*tinfo).alloc;
  size_t lenx = prim_strlen(x);
  size_t leny = prim_strlen(y);
  unsigned long long words = ((lenx + leny) / 8) + 1;
  if (!(words <= $limit - $alloc)) {
    /*skip*/;
    (*tinfo).nalloc = words;
    garbage_collect(tinfo);
    /*skip*/;
    $alloc = (*tinfo).alloc;
    $limit = (*tinfo).limit;
  }
  assert (words <= $limit - $alloc);
  *($alloc + 0LLU) = String_tag | (words << 10);
  int i = lenx + leny;
  char *strp = (char*) ($alloc + 1LLU);
  memcpy(strp, Bp_val(x), lenx);
  memcpy(strp + lenx, Bp_val(y), leny);
  // Fill remaining bytes with 0s.
  // End with the number of 0s to trim to compute the length
  int j = lenx + leny;
  for (; ((j + 1) / 8) < words; j++)
  { strp[j] = (char) 0; }
  strp[j] = j - i;
  (*tinfo).alloc = (*tinfo).alloc + words;
  return (value) ((unsigned long long *) $alloc + 1LLU);
}
