#include "values.h"

#ifndef PRIM_INT63_H
#define PRIM_INT63_H

typedef value primint;
typedef value primbool;
typedef value primintcarry;
typedef value primintpair;
typedef primint primcompare; // Lt (-1) | Eq (0) | Gt (1) (as primints)

extern primbool mk_bool(int);
extern value mk_pair(struct thread_info *ti, value x, value y);

extern primint prim_int63_add(primint x, primint y);
extern primint prim_int63_sub(primint x, primint y);
extern primint prim_int63_mul(primint x, primint y);
extern primint prim_int63_mod(primint x, primint y);
extern primint prim_int63_div(primint x, primint y);
extern primint prim_int63_mods(primint x, primint y);
extern primint prim_int63_divs(primint x, primint y);

extern primint prim_int63_land(primint x, primint y);
extern primint prim_int63_lsl(primint x, primint y);
extern primint prim_int63_lsr(primint x, primint y);
extern primint prim_int63_lor(primint x, primint y);
extern primint prim_int63_lxor(primint x, primint y);
extern primint prim_int63_asr(primint x, primint y);

extern primint prim_int63_head0(primint x);
extern primint prim_int63_tail0(primint x);
    
extern primbool prim_int63_eqb(primint x, primint y);
extern primbool prim_int63_leb(primint x, primint y);
extern primbool prim_int63_ltb(primint x, primint y);
extern primbool prim_int63_lesb(primint x, primint y);
extern primbool prim_int63_ltsb(primint x, primint y);
extern value prim_int63_compare(primint x, primint y); // Unsigned comparison
extern value prim_int63_compares(primint x, primint y); // Signed comparison

extern primintcarry prim_int63_addc(struct thread_info *, primint x, primint y);
extern primintcarry prim_int63_addcarryc(struct thread_info *, primint x, primint y);
extern primintcarry prim_int63_subc(struct thread_info *, primint x, primint y);
extern primintcarry prim_int63_subcarryc(struct thread_info *, primint x, primint y);
extern primintpair prim_int63_mulc(struct thread_info *, primint x, primint y);

/* [div21 xh xl y] returns [q % 2^63, r]
    s.t. [xh * 2^63 + xl = q * y + r] and [r < y].
    When [y] is [0], returns [0, 0]. */
extern primintpair prim_int63_diveucl_21(struct thread_info *, primint x, primint y, primint z);
extern primintpair prim_int63_diveucl(struct thread_info *, primint x, primint y);

extern primint prim_int63_addmuldiv(primint x, primint y, primint z);

#endif /* PRIM_INT63_H */
