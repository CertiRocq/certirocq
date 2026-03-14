#include "values.h"
#include "prim_int63.h"
#include "prim_string.h"

#ifndef CERTIROCQ_GMP_H
#define CERTIROCQ_GMP_H

typedef value gmp_int;
typedef value primint;
typedef value primbool;
typedef value primstring;
typedef value primintcarry;
typedef value primintpair;

extern gmp_int z_zero();
extern gmp_int z_one();
extern gmp_int z_succ(struct thread_info* tinfo, gmp_int x);
extern gmp_int z_pred(struct thread_info* tinfo, gmp_int x);
extern gmp_int z_abs(struct thread_info* tinfo, gmp_int x);
extern gmp_int z_neg(struct thread_info* tinfo, gmp_int x);
extern gmp_int z_add(struct thread_info* tinfo, gmp_int x, gmp_int y);
extern gmp_int z_sub(struct thread_info* tinfo, gmp_int x, gmp_int y);
extern gmp_int z_mul(struct thread_info* tinfo, gmp_int x, gmp_int y);
extern gmp_int z_div(struct thread_info* tinfo, gmp_int x, gmp_int y);
extern gmp_int z_rem(struct thread_info* tinfo, gmp_int x, gmp_int y);
extern gmp_int z_pow(struct thread_info* tinfo, gmp_int x, gmp_int y);
extern gmp_int z_logand(struct thread_info* tinfo, gmp_int x, gmp_int y);
extern gmp_int z_logor(struct thread_info* tinfo, gmp_int x, gmp_int y);
extern gmp_int z_logxor(struct thread_info* tinfo, gmp_int x, gmp_int y);
extern gmp_int z_lognot(struct thread_info* tinfo, gmp_int x);

extern gmp_int z_max(gmp_int x, gmp_int y);
extern gmp_int z_min(gmp_int x, gmp_int y);

extern primbool z_leq(gmp_int x, gmp_int y);
extern primbool z_geq(gmp_int x, gmp_int y);
extern primbool z_gt(gmp_int x, gmp_int y);
extern primbool z_lt(gmp_int x, gmp_int y);

extern primint z_compare(gmp_int x, gmp_int y);
extern primbool z_equal(gmp_int x, gmp_int y);

extern gmp_int z_of_int(primint x);
extern gmp_int z_of_string(struct thread_info* tinfo, primstring x);
extern primstring z_to_string(struct thread_info* tinfo, gmp_int x);

#endif /* CERTIROCQ_GMP_H */
