#include "values.h"
#include "prim_int63.h"
#include <math.h>

#ifndef PRIM_FLOATS_H
#define PRIM_FLOATS_H 1

typedef value primfloat;
typedef value primfloatintpair;
typedef value primfloat_class;
typedef value primfloat_comparison;

#define inf INFINITY // OCaml name for infinity

extern primfloat_comparison prim_float_compare(primfloat x, primfloat y);
extern primbool prim_float_eqb(primfloat x, primfloat y);
extern primbool prim_float_ltb(primfloat x, primfloat y);
extern primbool prim_float_leb(primfloat x, primfloat y);

extern primfloatintpair prim_float_frshiftexp(struct thread_info *ti, primfloat x);
extern primfloat prim_float_ldshiftexp(struct thread_info *ti, primfloat x, primint exp);

extern primint prim_float_normfr_mantissa(primfloat x);
extern primfloat_class prim_float_classify(primfloat x);

extern primfloat prim_float_div(struct thread_info *ti, primfloat x, primfloat y);
extern primfloat prim_float_abs(struct thread_info *ti, primfloat x);
extern primfloat prim_float_sqrt(struct thread_info *ti, primfloat x);
extern primfloat prim_float_opp(struct thread_info *ti, primfloat x);
extern primfloat prim_float_mul(struct thread_info *ti, primfloat x, primfloat y);
extern primfloat prim_float_add(struct thread_info *ti, primfloat x, primfloat y);
extern primfloat prim_float_sub(struct thread_info *ti, primfloat x, primfloat y);
extern primfloat prim_float_of_uint63(struct thread_info *, primint);
extern primfloat prim_float_next_up(struct thread_info *, primfloat);
extern primfloat prim_float_next_down(struct thread_info *, primfloat);

#endif // PRIM_FLOATS_H
