#include <assert.h>
#include <string.h>
#include <stdio.h>
#include <stdlib.h>
#include <math.h>
#include <gmp.h>
#include "values.h"
#include "gc_stack.h"
#include "prim_int63.h"
#include "prim_string.h"

typedef value gmp_int;
typedef value primint;
typedef value primstring;
typedef value primintcarry;
typedef value primintpair;

#define trace(...) printf(__VA_ARGS__)

#define MPZ_val(x) (*(mpz_ptr*) (Op_val(x)))

mpz_ptr mpz_of_value(gmp_int x) {
  if (Is_long (x))
  { mpz_ptr res;
    res = malloc(sizeof(__mpz_struct));
    trace("found a long value\n");
    mpz_init_set_ui (res, Long_val (x));
    return res; }
  { trace("found a structured mpz value at %p\n", (void*) x);
    return MPZ_val(x); }
}

void print_mpz(mpz_ptr x) {
   char* str = NULL;
   str = mpz_get_str(NULL, 10, MPZ_val(x));
   trace("%p (%p) is a GMP value %s\n", (void*) x, (void*) MPZ_val(x), str);
}

void print_gmp_int(gmp_int x) {
  if (Is_long (x)) {
    trace("%p is a long int %lu", (void*) x, Val_long(x));
  } else { char* str = NULL;
    str = mpz_get_str(NULL, 10, MPZ_val(x));
    trace("%p (%p) is a GMP value %s\n", (void*) x, (void*) MPZ_val(x), str);
  }
}


gmp_int mk_gmp_int (struct thread_info *tinfo, mpz_ptr x) {
  char* str = NULL;
  trace("mk_gmp_int called with %p\n", x);
  str = mpz_get_str(NULL, 10, x);
  trace("Calling mk_gmp_int with %s\n", str);
  /* free(str); */
  register value *$alloc;
  register value *$limit;
  $limit = (*tinfo).limit;
  $alloc = (*tinfo).alloc;
  if (!(2LLU <= $limit - $alloc)) {
    /*skip*/;
    (*tinfo).nalloc = 2LLU;
    garbage_collect(tinfo);
    /*skip*/;
    $alloc = (*tinfo).alloc;
    $limit = (*tinfo).limit;
  }
  *($alloc + 0LLU) = No_scan_tag | (1 << 10);
  *((mpz_ptr*) ($alloc + 1LLU)) = x;
  (*tinfo).alloc = (*tinfo).alloc + 2LLU;
  print_gmp_int((value) ((unsigned long long *) $alloc + 1LLU));
  return (value) ((unsigned long long *) $alloc + 1LLU);
}

gmp_int z_zero() {
  return (Val_long (0));
}

gmp_int z_one() {
  return (Val_long (1));
}

gmp_int gmp_succ(struct thread_info *tinfo, mpz_t x) {
  mpz_ptr res = malloc(sizeof(__mpz_struct));
  mpz_init(res);
  mpz_add_ui(res, x, 1);
  return mk_gmp_int(tinfo, res);
}

gmp_int z_succ(struct thread_info *tinfo, gmp_int x) {
  if (Is_long(x)) {
    intnat y = Long_val(x);
    if (y < Max_long) { return (Val_long (y + 1)); }
    { return gmp_succ(tinfo, mpz_of_value(x)); }
  }
  return gmp_succ(tinfo, mpz_of_value(x)); }

gmp_int gmp_pred(struct thread_info *tinfo, mpz_t x) {
  mpz_ptr res = malloc(sizeof(__mpz_struct));
  mpz_init(res);
  mpz_add_ui(res, x, -1);
  return mk_gmp_int(tinfo, res);
}

gmp_int z_pred(struct thread_info *tinfo, gmp_int x) {
  if (Is_long(x)) {
    intnat y = Long_val(x);
    if (y > Min_long) { return (Val_long (y - 1)); }
    { return gmp_pred(tinfo, mpz_of_value(x)); }
  }
  return gmp_pred(tinfo, mpz_of_value(x));
}

gmp_int gmp_abs(struct thread_info *tinfo, mpz_t x) {
  mpz_ptr res = malloc(sizeof(__mpz_struct));
  mpz_init(res);
  mpz_abs(res, x);
  return mk_gmp_int(tinfo, res);
}

gmp_int z_abs(struct thread_info *tinfo, gmp_int x) {
  if (Is_long(x)) {
    return (Long_val (labs (Val_long(x))));
  }
  return gmp_abs(tinfo, MPZ_val(x));
}

gmp_int gmp_neg(struct thread_info *tinfo, mpz_t x) {
  mpz_ptr res = malloc(sizeof(__mpz_struct));
  mpz_init(res);
  mpz_neg(res, x);
  return mk_gmp_int(tinfo, res);
}

gmp_int z_neg(struct thread_info *tinfo, gmp_int x) {
  if (Is_long(x)) {
    intnat y = Long_val(x);
    if (y < Max_long) { return (Val_long (- y)); }
    { mpz_ptr res = malloc(sizeof(__mpz_struct));
      mpz_init_set_si(res, y);
      return gmp_neg(tinfo, res); }
  }
  return gmp_neg(tinfo, MPZ_val(x));
}

gmp_int gmp_add(struct thread_info *tinfo, mpz_t x, mpz_t y) {
  mpz_ptr res = malloc(sizeof(__mpz_struct));
  mpz_add(res, x, y);
  return mk_gmp_int(tinfo, res);
}

gmp_int z_add(struct thread_info *tinfo, gmp_int x, gmp_int y) {
  if (Is_long (x) && Is_long(y)) {
    // TODO Overflow
    unsigned long long z = Long_val (x) + Long_val(y);
    if (((1LLU << 63) & z) > 0) {
      trace ("no overflow in z_add: 0x%080llx\n", z);
      return Val_long(z);
    } else {
      trace ("overflow in z_add\n");
      return gmp_add(tinfo, mpz_of_value(x), mpz_of_value(y));
    }
  } else {
    return gmp_add(tinfo, mpz_of_value(x), mpz_of_value(y));
  }
}

gmp_int gmp_sub(struct thread_info *tinfo, mpz_t x, mpz_t y) {
  mpz_ptr res = malloc(sizeof(__mpz_struct));
  mpz_init(res);
  mpz_sub(res, x, y);
  return mk_gmp_int(tinfo, res);
}

gmp_int z_sub(struct thread_info *tinfo, gmp_int x, gmp_int y) {
  if (Is_long (x) && Is_long(y)) {
    // TODO Overflow
    return (Val_long (Long_val (x) - Long_val(y)));
  } else {
    return gmp_sub(tinfo, mpz_of_value(x), mpz_of_value(y));
  }
}

gmp_int gmp_mul(struct thread_info *tinfo, mpz_t x, mpz_t y) {
  mpz_ptr res = malloc(sizeof(__mpz_struct));
  mpz_init(res);
  mpz_mul(res, x, y);
  return mk_gmp_int(tinfo, res);
}

gmp_int z_mul(struct thread_info *tinfo, gmp_int x, gmp_int y) {
  //if (Is_long (x) && Is_long(y))
    // TODO Overflow
    //{ return (Val_long (Long_val (x) * Long_val(y))); }
  //  {
  return gmp_mul(tinfo, mpz_of_value(x), mpz_of_value(y));
}

gmp_int gmp_div(struct thread_info *tinfo, mpz_t x, mpz_t y) {
  mpz_ptr res = malloc(sizeof(__mpz_struct));
  mpz_init(res);
  mpz_cdiv_q(res, x, y);
  return mk_gmp_int(tinfo, res);
}

gmp_int z_div(struct thread_info *tinfo, gmp_int x, gmp_int y) {
  if (Is_long (x) && Is_long(y))
    // TODO Overflow
    { return (Val_long (Long_val (x) / Long_val(y))); }
  { return gmp_div(tinfo, mpz_of_value(x), mpz_of_value(y)); }
}

gmp_int gmp_rem(struct thread_info *tinfo, mpz_t x, mpz_t y) {
  mpz_ptr res = malloc(sizeof(__mpz_struct));
  mpz_init(res);
  mpz_cdiv_r(res, x, y);
  return mk_gmp_int(tinfo, res);
}

gmp_int z_rem(struct thread_info *tinfo, gmp_int x, gmp_int y) {
  if (Is_long (x) && Is_long(y))
    // TODO Overflow
    { return (Val_long (Long_val (x) % Long_val(y))); }
  { return gmp_add(tinfo, mpz_of_value(x), mpz_of_value(y)); }
}

// Truncate y to an unsigned long int
gmp_int gmp_pow(struct thread_info *tinfo, mpz_t x, mpz_t y) {
  mpz_ptr res = malloc(sizeof(__mpz_struct));
  mpz_init(res);
  mpz_pow_ui(res, x, mpz_get_ui(y));
  return mk_gmp_int(tinfo, res);
}

gmp_int z_pow(struct thread_info *tinfo, gmp_int x, gmp_int y) {
  return gmp_pow(tinfo, mpz_of_value(x), mpz_of_value(y));
}

gmp_int gmp_logand(struct thread_info *tinfo, mpz_t x, mpz_t y) {
  mpz_ptr res = malloc(sizeof(__mpz_struct));
  mpz_init(res);
  mpz_and(res, x, y);
  return mk_gmp_int(tinfo, res);
}

gmp_int z_logand(struct thread_info *tinfo, gmp_int x, gmp_int y) {
  if (Is_long (x) && Is_long(y)) {
    return (Val_long (Long_val(x) & Long_val(y)));
  } else {
    return gmp_logand(tinfo, mpz_of_value(x), mpz_of_value(y));
  }
}

gmp_int gmp_logor(struct thread_info *tinfo, mpz_t x, mpz_t y) {
  mpz_ptr res = malloc(sizeof(__mpz_struct));
  mpz_init(res);
  mpz_ior(res, x, y);
  return mk_gmp_int(tinfo, res);
}

gmp_int z_logor(struct thread_info *tinfo, gmp_int x, gmp_int y) {
  if (Is_long (x) && Is_long(y)) {
    return (Val_long (Long_val (x) | Long_val(y)));
  } else {
    return gmp_logor(tinfo, mpz_of_value(x), mpz_of_value(y));
  }
}

gmp_int gmp_logxor(struct thread_info *tinfo, mpz_t x, mpz_t y)  {
  mpz_ptr res = malloc(sizeof(__mpz_struct));
  mpz_init(res);
  mpz_xor(res, x, y);
  return mk_gmp_int(tinfo, res);
}

gmp_int z_logxor(struct thread_info *tinfo, gmp_int x, gmp_int y) {
  if (Is_long (x) && Is_long(y)) {
    return (Val_long (Long_val (x) ^ Long_val(y)));
  } else {
    return gmp_logxor(tinfo, mpz_of_value(x), mpz_of_value(y));
  }
}

gmp_int gmp_lognot(struct thread_info *tinfo, mpz_t x) {
  mpz_ptr res = malloc(sizeof(__mpz_struct));
  mpz_init(res);
  mpz_com(res, x);
  return mk_gmp_int(tinfo, res);
}

gmp_int z_lognot(struct thread_info *tinfo, gmp_int x) {
  if (Is_long (x)) {
    return Val_long (~(Long_val (x)));
  } else {
    return gmp_lognot(tinfo, mpz_of_value(x));
  }
}

primint gmp_compare(mpz_t x, mpz_t y) {
  return (Val_long (mpz_cmp (x, y)));
}

primint z_compare(gmp_int x, gmp_int y) {
  if (Is_long (x) && Is_long(y)) {
    return prim_int63_compares(x, y);
  } else {
    return gmp_compare(mpz_of_value(x), mpz_of_value(y));
  }
}

primbool gmp_equal(mpz_t x, mpz_t y) {
  return (mk_bool (mpz_cmp (x, y) == 0));
}

primint z_equal(gmp_int x, gmp_int y) {
  if (Is_long (x) && Is_long(y)) {
    return (mk_bool (x == y));
  } else {
    return gmp_equal(mpz_of_value(x), mpz_of_value(y));
  }
}

primbool gmp_leq(mpz_t x, mpz_t y) {
  return (mk_bool (mpz_cmp (x, y) ? 0 : 1));
}

primbool z_leq(gmp_int x, gmp_int y) {
  if (Is_long (x) && Is_long(y)) {
    return prim_int63_lesb(x, y);
  } else {
    return gmp_leq(mpz_of_value(x), mpz_of_value(y));
  }
}

primbool gmp_geq(mpz_t x, mpz_t y) {
  int cmp = mpz_cmp (x, y);
  return (mk_bool (cmp >= 0));
}

primbool z_geq(gmp_int x, gmp_int y) {
  if (Is_long (x) && Is_long(y)) {
    return prim_int63_lesb(y, x);
  } else {
    return gmp_geq(mpz_of_value(x), mpz_of_value(y));
  }
}

primbool gmp_gt(mpz_t x, mpz_t y) {
  int cmp = mpz_cmp (x, y);
  return (mk_bool (cmp > 0));
}

primbool z_gt(gmp_int x, gmp_int y) {
  if (Is_long (x) && Is_long(y)) {
    return prim_int63_ltsb (y, x); }
  { return gmp_gt(mpz_of_value(x), mpz_of_value(y)); }
}

primbool gmp_lt(mpz_t x, mpz_t y) {
  int cmp = mpz_cmp (x, y);
  return (mk_bool (cmp < 0));
}

primbool z_lt(gmp_int x, gmp_int y) {
  if (Is_long (x) && Is_long(y))
    // Correct ?
    { return (mk_bool (x < y)); }
  { return gmp_lt(mpz_of_value(x), mpz_of_value(y)); }
}

gmp_int z_max(gmp_int x, gmp_int y) {
  if (Is_long (x) && Is_long(y))
    // Correct ?
    { return (Long_val(x) > Long_val(y) ? x : y); }
  { int cmp = mpz_cmp (mpz_of_value(x), mpz_of_value(y));
    return (cmp ? x : y); }
}

gmp_int z_min(gmp_int x, gmp_int y) {
  if (Is_long (x) && Is_long(y))
    // Correct ?
    { return (Long_val(x) < Long_val(y) ? x : y); }
  { int cmp = mpz_cmp (mpz_of_value(x), mpz_of_value(y));
    return (cmp ? y : x); }
}

gmp_int gmp_of_int(primint x) {
  return x;
}

gmp_int z_of_int(primint x) {
  return x;
}

gmp_int z_of_string(struct thread_info *tinfo, primstring x) {
  mpz_ptr res = NULL;
  res = malloc(sizeof(__mpz_struct));
  size_t len = prim_strlen(x); // bytes
  char* cp = malloc(len + 1);
  assert (cp != NULL);
  int i = 0;
  for (;i < len; i++) {
    cp[i] = Byte (x, i);
  }
  cp[i] = 0;
  trace("copied string: %s.\n", cp);
  int code = mpz_set_str (res, cp, 10);
  trace("of_string allocated: %p with code %i\n", res, code);
  if (code == 0) {
    // free(cp); Should it be freed?
    return mk_gmp_int(tinfo, res); }
  { exit(code); }
}

primstring z_to_string(struct thread_info *tinfo, gmp_int x) {
  print_gmp_int(x);
  char* str = NULL;
  if (Is_long(x)) {
    trace("z_to_string: long\n");
    int length = snprintf(NULL, 0, "%li", Long_val(x));
    str = malloc(length + 1);
    snprintf(str, length + 1, "%li", Long_val(x));
    return mk_ocaml_string(tinfo, str);
  } else {
    trace("z_to_string: GMP\n");
    /* print_gmp_int(x); */
    str = mpz_get_str(NULL, 10, MPZ_val(x));
    if (str == NULL) { trace("mpz_get_str failed"); exit(1); }
    value pstr = mk_ocaml_string(tinfo, str);
    printf("new string length: %li", prim_strlen(pstr));
    return pstr;
  }
}

struct thread_info *global_tinfo;

void *allocate_function (size_t alloc_size) {
  value *$alloc;
  value *$limit;
  trace("allocate_function called\n");
  struct thread_info *tinfo = global_tinfo;
  $limit = (*tinfo).limit;
  $alloc = (*tinfo).alloc;
  unsigned long long words;
  if (alloc_size % sizeof(value) == 0) {
    words = (alloc_size / sizeof(value)) + 1;
  } else {
    words = (alloc_size / sizeof(value)) + 2;
  }
  if (!(words <= $limit - $alloc)) {
    /*skip*/;
    (*tinfo).nalloc = words;
    garbage_collect(tinfo);
    /*skip*/;
    $alloc = (*tinfo).alloc;
    $limit = (*tinfo).limit;
  }
  trace("allocate called, %p: %zu, words: %llu\n", $alloc, alloc_size, words);
  assert (words <= $limit - $alloc);
  unsigned long long hd = No_scan_tag | ((words - 1) << 10);
  *($alloc + 0LLU) = hd;
  memset((void *) ($alloc + 1LLU), 0, (words - 1) * sizeof(value));
  /* trace("allocate made block of header: %llx\n", (unsigned long long) (words << 10)); */
  trace("allocate made block of header: 0x%08llx, pointer is %p\n", hd, ((void *) ($alloc + 1LLU)));

  return ((void *) ($alloc + 1LLU));
}

void *reallocate_function (void *ptr, size_t old_size, size_t new_size) {
  trace("reallocate called: %p: %zu to %zu\n", ptr, old_size, new_size);
  void *newptr = allocate_function(new_size);
  size_t cpsize = old_size > new_size ? new_size : old_size;
  memcpy(newptr, ptr, cpsize);
  return newptr;
}

void free_function (void *ptr, size_t size) {
  trace("free called: %p: %zu\n", ptr, size);
  return;
}

void init_gmp_alloc(struct thread_info *tinfo) {
  global_tinfo = tinfo;
  mp_set_memory_functions(allocate_function,reallocate_function,free_function);
}
