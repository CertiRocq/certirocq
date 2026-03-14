#include <stdio.h>
#include <stdlib.h>
#include "gc_stack.h"

typedef value primint;
typedef value primbool;
typedef value primintcarry;
typedef value primintpair;

#define trace(...) // printf(__VA_ARGS__)

#define maxuint63 0x7FFFFFFFFFFFFFFF

primint prim_int63_add(primint x, primint y)
{
  // trace("Calling prim_int63_add\n");
  return (Val_long (Unsigned_long_val(x) + Unsigned_long_val(y)));
}

primint prim_int63_sub(primint x, primint y)
{ 
  unsigned long long xr = Unsigned_long_val(x);
  unsigned long long yr = Unsigned_long_val(y);
  trace("Calling prim_int63_sub on %llu and %llu: %llu\n", xr, yr, xr - yr);
  return (Val_long (xr - yr));
}

primint prim_int63_mul(primint x, primint y)
{ 
  // trace("Calling prim_int63_mul\n");
  return (Val_long (Unsigned_long_val(x) * Unsigned_long_val(y)));
}

primint prim_int63_mod(primint x, primint y)
{ 
  // trace("Calling prim_int63_mod\n");
  unsigned long long yr = Unsigned_long_val(y);
  if (yr == 0) return x;
  else return (Val_long (Unsigned_long_val(x) % Unsigned_long_val(y)));
}

primint prim_int63_div(primint x, primint y)
{ 
  // trace("Calling prim_int63_div\n");
  unsigned long long yr = Unsigned_long_val(y);
  if (yr == 0) return Val_long(0);
  else return (Val_long (Unsigned_long_val(x) / Unsigned_long_val(y)));
}

primint prim_int63_mods(primint x, primint y)
{
  // trace("Calling prim_int63_mod\n");
  signed long long yr = Long_val(y);
  if (yr == 0) return x;
  else return (Val_long (Unsigned_long_val(x) % Unsigned_long_val(y)));
}

primint prim_int63_divs(primint x, primint y)
{
  // trace("Calling prim_int63_div\n");
  signed long long yr = Long_val(y);
  if (yr == 0) return Val_long(0);
  else return (Val_long (Long_val(x) / yr));
}

primint prim_int63_land(primint x, primint y)
{ 
  unsigned long long xr = Unsigned_long_val(x);
  unsigned long long yr = Unsigned_long_val(y);
  trace("Calling prim_int63_land on %llu (%p) and %llu (%p): %llu, %llu \n", xr, (void*)x, yr, (void*)y, xr & yr, (unsigned long long) (x & y));
  return (Val_long (xr & yr));
}
primint prim_int63_lsl(primint x, primint y)
{
  unsigned long long xr = Unsigned_long_val(x);
  unsigned long long yr = Unsigned_long_val(y);
  trace("Calling prim_int63_lsl on %llu and %llu: %llu \n", xr, yr, xr << yr);
  if (0 <= yr && yr < 63) return (Val_long ((xr << yr)));
  else return (Val_long(0));
}

primint prim_int63_lsr(primint x, primint y)
{ 
  unsigned long long xr = Unsigned_long_val(x);
  unsigned long long yr = Unsigned_long_val(y);
  trace("Calling prim_int63_lsr on %llu and %llu: %llu \n", xr, yr, xr >> yr);
  if (0 <= yr && yr < 63) return (Val_long ((xr >> yr)));
  else return (Val_long(0));
}

primint prim_int63_asr(primint x, primint y)
{ 
  signed long long xr = Unsigned_long_val(x);
  unsigned long long yr = Unsigned_long_val(y);
  if (0 <= yr && yr < 63) return (Val_long ((xr >> yr)));
  else return (Val_long(0));
}

primint prim_int63_lor(primint x, primint y)
{ 
  return (Val_long (Unsigned_long_val(x) | Unsigned_long_val(y)));
}
primint prim_int63_lxor(primint x, primint y)
{
  return (Val_long (Unsigned_long_val(x) ^ Unsigned_long_val(y)));
}

primint prim_int63_head0(primint init)
{
  unsigned long long r = 0;
  unsigned long long x = Unsigned_long_val (init);
  if ((x & 0x7FFFFFFF00000000) == 0) { r = r + 31; }
  else { x = x >> 31; }
  if ((x & 0xFFFF0000) == 0) { x = (x << 16) & maxuint63; r = r + 16; };
  if ((x & 0xFF000000) == 0) { x = (x << 8) & maxuint63; r = r + 8; };
  if ((x & 0xF0000000) == 0) { x = (x << 4) & maxuint63; r = r + 4; };
  if ((x & 0xC0000000) == 0) { x = (x << 2) & maxuint63; r = r + 2; };
  if ((x & 0x80000000) == 0) { x = (x << 1) & maxuint63; r = r + 1; };
  if ((x & 0x80000000) == 0) { r = r + 1; };
  trace("Calling prim_int63_head0 on %llu: %llu\n", x, r);
  return Val_long(r);
}

primint prim_int63_tail0(primint init)
{
  trace("Calling prim_int63_tail0\n");
  unsigned long long r = 0;
  unsigned long long x = Unsigned_long_val (init);
  if ((x & 0xFFFFFFFF) == 0) { x = x >> 32; r = r + 32; };
  if ((x & 0xFFFF) == 0)     { x = x >> 16; r = r + 16; };
  if ((x & 0xFF) == 0)       { x = x >> 8; r = r + 8; };
  if ((x & 0xF) == 0)        { x = x >> 4; r = r + 4; };
  if ((x & 0x3) == 0)        { x = x >> 2; r = r + 2; };
  if ((x & 0x1) == 0)        { r = r + 1; };
  return Val_long(r);
}

primbool mk_bool(int b)
{
  if (b) return 3;
  else return 1;
}

primbool prim_int63_eqb(primint x, primint y)
{
  unsigned long long xr = Unsigned_long_val(x);
  unsigned long long yr = Unsigned_long_val(y);
  trace("Calling prim_int63_eqb on %llu and %llu: %i, %i \n", xr, yr, xr == yr, x == y);
  return (mk_bool (xr == yr));
}
primbool prim_int63_leb(primint x, primint y)
{ 
  trace("Calling prim_int63_leb\n");
  return (mk_bool (x <= y));
}

// Beware, the fact is is an arithmetic right shift is implementation dependent
#define SLong_val(x) ((signed long long)(x) >> 1)
primbool prim_int63_lesb(primint x, primint y)
{
  trace("Calling prim_int63_leb\n");
  return (mk_bool (SLong_val(x) <= SLong_val(y)));
}
primbool prim_int63_ltb(primint x, primint y)
{
  trace("Calling prim_int63_ltb\n");
  return (mk_bool (x < y));
}
primbool prim_int63_ltsb(primint x, primint y)
{
  trace("Calling prim_int63_ltsb\n");
  return (mk_bool (SLong_val(x) < SLong_val(y)));
}

value prim_int63_compare(primint x, primint y)
{
  register signed long long xr = Unsigned_long_val(x);
  register signed long long yr = Unsigned_long_val(y);
  register signed long long result = xr - yr;
  trace("Calling prim_int63_compare\n");
  trace("Calling prim_int63_compare on %llu and %llu: %lli \n", xr, yr, result);
  if (result == 0) return 1;
  else if (result < 0) return 3;
  else return 5;
}

primbool prim_int63_compares(primint x, primint y)
{
  register signed long long xr = SLong_val(x);
  register signed long long yr = SLong_val(y);
  register signed long long result = xr - yr;
  trace("Calling prim_int63_compares\n");
  trace("Calling prim_int63_compares on %llu and %llu: %lli \n", xr, yr, result);
  if (result == 0) return 1;
  else if (result < 0) return 3;
  else return 5;
}

unsigned long long prim_int63_make_Coq_Numbers_Cyclic_Abstract_CarryType_carry_C0(unsigned long long $arg0, unsigned long long *$argv)
{
  *((unsigned long long *) $argv + 0LLU) = 1024LLU;
  *((unsigned long long *) $argv + 1LLU) = $arg0;
  return ((unsigned long long) $argv) + 1LLU;
}

value prim_int63_alloc_make_Coq_Numbers_Cyclic_Abstract_CarryType_carry_C0(struct thread_info *$tinfo, unsigned long long $arg0)
{
  // trace("Calling mkC0 with %llu (%p)\n", Unsigned_long_val($arg0), (void*)$arg0);
  register value *$alloc;
  register value *$limit;
  $limit = (*$tinfo).limit;
  $alloc = (*$tinfo).alloc;
 if (!(2LLU <= $limit - $alloc)) {
    /*skip*/;
    (*$tinfo).nalloc = 2LLU;
    garbage_collect($tinfo);
    /*skip*/;
    $alloc = (*$tinfo).alloc;
    $limit = (*$tinfo).limit;
  }
  *($alloc + 0LLU) = 1024LLU;
  *($alloc + 1LLU) = $arg0;
  (*$tinfo).alloc = (*$tinfo).alloc + 2LLU;
  // trace ("addc returns adress: %p", (void*)(((unsigned long long *) $alloc) + 1LLU));
  return (value) ((unsigned long long *) $alloc + 1LLU);
}

value prim_int63_make_Coq_Numbers_Cyclic_Abstract_CarryType_carry_C1(unsigned long long $arg0, unsigned long long *$argv)
{
  *((unsigned long long *) $argv + 0LLU) = 1025LLU;
  *((unsigned long long *) $argv + 1LLU) = $arg0;
  return ((unsigned long long) $argv) + 1LLU;
}

value prim_int63_alloc_make_Coq_Numbers_Cyclic_Abstract_CarryType_carry_C1(struct thread_info *$tinfo, unsigned long long $arg0)
{
  // trace("Calling mkC1\n");
  register value *$alloc;
  register value *$limit;
  $limit = (*$tinfo).limit;
  $alloc = (*$tinfo).alloc;
  if (!(2LLU <= $limit - $alloc)) {
    (*$tinfo).nalloc = 2LLU;
    garbage_collect($tinfo);
    $alloc = (*$tinfo).alloc;
    $limit = (*$tinfo).limit;
  }
  *($alloc + 0LLU) = 1025LLU;
  *($alloc + 1LLU) = $arg0;
  (*$tinfo).alloc = (*$tinfo).alloc + 2LLU;
  return (value) ($alloc + 1LLU);
}

primintcarry mk_C0(struct thread_info *ti, primint x)
{
  return prim_int63_alloc_make_Coq_Numbers_Cyclic_Abstract_CarryType_carry_C0(ti, x);
}

primintcarry mk_C1(struct thread_info *ti, primint x)
{
  return prim_int63_alloc_make_Coq_Numbers_Cyclic_Abstract_CarryType_carry_C1(ti, x);
}

value prim_int63_make_Coq_Init_Datatypes_prod_pair(unsigned long long $arg0, unsigned long long $arg1, value *$argv)
{
  *($argv + 0LLU) = 2048LLU;
  *($argv + 1LLU) = $arg0;
  *($argv + 2LLU) = $arg1;
  return (value) ($argv + 1LLU);
}

value prim_int63_alloc_make_Coq_Init_Datatypes_prod_pair(struct thread_info *$tinfo, unsigned long long $arg0, unsigned long long $arg1)
{
  register value *$argv;
  $argv = (*$tinfo).alloc;
  *($argv + 0LLU) = 2048LLU;
  *($argv + 1LLU) = $arg0;
  *($argv + 2LLU) = $arg1;
  (*$tinfo).alloc = (*$tinfo).alloc + 3LLU;
  return (value) ($argv + 1LLU);
}

primintpair mk_pair(struct thread_info *ti, primint x, primint y)
{
  // trace("Calling prim_int63_mk_pair on %lu and %lu\n", Unsigned_long_val(x), Unsigned_long_val(y));
  return prim_int63_alloc_make_Coq_Init_Datatypes_prod_pair(ti, x, y);
}

primintcarry prim_int63_addc(struct thread_info *ti, primint x, primint y)
{
  unsigned long long xr = Unsigned_long_val(x);
  unsigned long long yr = Unsigned_long_val(y);
  trace("Calling prim_int63_addc on %llu and %llu\n", xr, yr);
  register unsigned long long r = xr + yr;
  trace("Result: %llu\n", r);
  if (r < xr) { return mk_C1(ti, Val_long (r)); }
  else { return mk_C0(ti, Val_long (r)); }
}

primintcarry prim_int63_addcarryc(struct thread_info *ti, primint x, primint y)
{
  trace("Calling prim_int63_addcarryc\n");
  register primint r = (Unsigned_long_val(x) + Unsigned_long_val(y) + 1);
  if (r <= x) { return mk_C1(ti, Val_long(r)); }
  else { return mk_C0(ti, Val_long(r)); }
}

primintcarry prim_int63_subc(struct thread_info *ti, primint x, primint y)
{ 
  unsigned long long xr = Unsigned_long_val(x);
  unsigned long long yr = Unsigned_long_val(y);
  register unsigned long long r = xr - yr;
  trace("Calling prim_int63_subc on %llu and %llu: %llu\n", xr, yr, r);
  if (y <= x) { return mk_C0(ti, Val_long(r)); }
  else { return mk_C1(ti, Val_long(r)); }
}

primintcarry prim_int63_subcarryc(struct thread_info *ti, primint x, primint y)
{
  trace("Calling prim_int63_subccarryc\n");
  register primint r = (Unsigned_long_val(x) - Unsigned_long_val(y) - 1);
  if (y < x) { return mk_C0(ti, Val_long(r)); }
  else { return mk_C1(ti, Val_long(r)); }
}

#define maxuint31 0x7FFFFFFF

// precondiition : (x lsr 62 = 0 || y lsr 62 = 0)
primintpair mulc_aux(struct thread_info *ti, unsigned long long x, unsigned long long y) {
  unsigned long lx = x & maxuint31;
  unsigned long ly = y & maxuint31;
  unsigned long hx = x >> 31;
  unsigned long hy = y >> 31;
  // trace("Multiplication mulc_aux lx = %lu, ly = %lu, hx = %lu, hy = %lu)\n", lx, ly, hx, hy);
  // hx and hy are 32 bits value but at most one is 32
  unsigned long long hxy = hx * hy; // 63 bits
  unsigned long long hxly = hx * ly; // 63 bits
  unsigned long long lxhy = lx * hy; // 63 bits
  unsigned long long lxy  = lx * ly; // 62 bits
  unsigned long long l  = lxy | (hxy << 62); // 63 bits
  unsigned long long h  = hxy >> 1; // 62 bits
  unsigned long long hl = (hxly + lxhy) & maxuint63; // We can have a carry
  if (hl < hxly) h = h + (1ULL << 31);
  unsigned long long hl2 = (hl << 31) & maxuint63;
  l = (l + hl2) & maxuint63;
  if (l < hl2) h = h + 1;
  h  = h + (hl >> 32);
  trace("Multiplication mulc_aux gives: (%llu, %llu)\n", h, l);
  return mk_pair (ti, Val_long(h),Val_long(l));
}

primintpair prim_int63_mulc (struct thread_info *ti, primint xp, primint yp) {
  unsigned long long x = Unsigned_long_val(xp);
  unsigned long long y = Unsigned_long_val(yp);
  trace("Calling prim_int63_mulc on %llu (%p) and %llu (%p)\n", x, (void*)xp, y, (void*)yp);  
  if (x >> 62 == 0 || y >> 62 == 0) 
    return (mulc_aux(ti, x, y));
  else {
    unsigned long long yl = y ^ (1ULL << 62);
    value p = mulc_aux(ti,x,yl);
    unsigned long long h = Unsigned_long_val(*((unsigned long long*) p + 0));
    unsigned long long l = Unsigned_long_val(*((unsigned long long*) p + 1));
    /* h << 63 + l = x * yl
       x * y = x * (1 << 62 + yl)  =
       x << 62 + x*yl = x << 62 + h << 63 + l */
    unsigned long long l2 = l + (x << 62);
    if (l2 < l) h = h + 1;
    h = h + (x >> 1);
    trace("Multiplication gives: (%llu, %llu)\n", h, l2);
    return (mk_pair (ti, Val_long(h), Val_long(l2)));
  }
}

/* [div21 xh xl y] returns [q % 2^63, r]
    s.t. [xh * 2^63 + xl = q * y + r] and [r < y].
    When [y] is [0], returns [0, 0]. */

/* division of two numbers by one
   precondition: xh < y *)
  outputs: q, r s.t. x = q * y + r, r < y */

primintpair prim_int63_diveucl_21_long(struct thread_info *ti, unsigned long long xh, unsigned long long xl, 
  unsigned long long y)
{   
  trace("Calling prim_int63_diveucl_21 with %llu, %llu and %llu\n", xh, xl, y);
  /* nh might temporarily grow as large as 2*y - 1 in the loop body,
     so we store it as a 64-bit unsigned integer */
  unsigned long long nh = xh & maxuint63;
  unsigned long long nl = xl & maxuint63;
  unsigned long long q = 0;
  unsigned int i = 0;
  if (((nh & (1LLU << 63)) != 0)) trace("msb is set\n");
  for (i = 0; i < 63; i++) {
    /* invariants: 0 <= nh < y, nl = (xl*2^i) % 2^63,
       (q*y + nh) * 2^(63-i) + (xl % 2^(63-i)) = (xh%y) * 2^63 + xl */
    nh = (nh << 1) | (nl >> 62);
    nl = (nl << 1) & maxuint63;
    q = q << 1;
    if (nh >= y) { q = q | 1LLU; nh = nh - y; }
  }
  trace("Result: %llu, %llu\n", q, nh & 18446744073709551615ULL);
  return mk_pair(ti, Val_long(q), Val_long(nh & 18446744073709551615ULL));
}

primintpair prim_int63_diveucl_21(struct thread_info *ti, primint xh, primint xl, primint y) {
  unsigned long long xhl = Unsigned_long_val(xh);
  unsigned long long xll = Unsigned_long_val(xl);
  unsigned long long yl = Unsigned_long_val(y);
  if (yl <= xhl) return mk_pair (ti, Val_long(0), Val_long(0));
  else
    return prim_int63_diveucl_21_long(ti, xhl, xll, yl);
}

primintpair prim_int63_diveucl(struct thread_info *ti, primint xp, primint yp)
{
  unsigned long long x = Unsigned_long_val(xp);
  unsigned long long y = Unsigned_long_val(yp);
  trace("Calling prim_int63_diveucl\n");
  if (y == 0) return (mk_pair (ti, Val_long(0), Val_long(x)));
  else 
    return (mk_pair (ti, Val_long(x / y), Val_long(x % y)));
}

#define uint_size 63

primint prim_int63_addmuldiv(primint pp, primint xp, primint yp)
{
  trace("Calling prim_int63_addmuldiv\n");
  unsigned long long p = Unsigned_long_val(pp);
  unsigned long long x = Unsigned_long_val(xp);
  unsigned long long y = Unsigned_long_val(yp);
  if (63 < p) return Val_long(0);
  else { 
    unsigned long long r = ((x << p) & maxuint63) | y >> (uint_size - p);
    trace("Calling addmuldiv with %llu, %llu and %llu: %llu\n", p, x, y, r);
    return Val_long(r);
  }
}
