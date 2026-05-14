#ifndef VALUES_H
#define VALUES_H

#include "m.h"
#include <stddef.h>
#include <stdint.h>

#ifdef __cplusplus
extern "C" {
#endif

/* Value layout follows OCaml's low-bit tagged representation:
 *  value  : either an immediate integer with the low bit set, or a pointer
 *           to the first field of a block.
 *  block  : a header word followed by N word-sized fields.
 *  header : encodes word size, two color bits (reserved for OCaml's GC;
 *           unused by the CertiRocq generational GC, which signals
 *           forwarded blocks by overwriting the header with 0), and a
 *           constructor tag. */

#if SIZEOF_PTR <= 0
#error "SIZEOF_PTR must be defined and positive"
#endif

#if SIZEOF_VALUE <= 0
#error "SIZEOF_VALUE must be defined and positive"
#endif

#if SIZEOF_VALUE < SIZEOF_PTR
#error "SIZEOF_VALUE must be at least SIZEOF_PTR"
#endif

/* certirocq_value_bits is the unsigned raw-bits view of a value slot. It is
 * used only for representation-level operations such as tag tests, shifts,
 * and header decoding. Runtime code should use value and the macros below. */
#if SIZEOF_VALUE == 2
#  if !defined(INT16_MAX) || !defined(UINT16_MAX)
#    error "SIZEOF_VALUE=2 requires int16_t and uint16_t"
#  endif
typedef int16_t value;
typedef uint16_t certirocq_value_bits;
#elif SIZEOF_VALUE == 4
#  if !defined(INT32_MAX) || !defined(UINT32_MAX)
#    error "SIZEOF_VALUE=4 requires int32_t and uint32_t"
#  endif
typedef int32_t value;
typedef uint32_t certirocq_value_bits;
#elif SIZEOF_VALUE == 8
#  if !defined(INT64_MAX) || !defined(UINT64_MAX)
#    error "SIZEOF_VALUE=8 requires int64_t and uint64_t"
#  endif
typedef int64_t value;
typedef uint64_t certirocq_value_bits;
#else
#error "SIZEOF_VALUE must be 2, 4, or 8"
#endif

/* Conversion between a C pointer and the integer slot used for Rocq values.
 * The slot may be wider than a data pointer on small targets; it must never
 * be narrower. */
#define Val_ptr(p) ((value) (uintptr_t) (p))
#define Ptr_val(v) ((value *) (uintptr_t) (certirocq_value_bits) (v))
#define Bp_val(v)  ((char *) (uintptr_t) (certirocq_value_bits) (v))

/* Long vs block discrimination (tag bit). */
#define Is_long(x)   ((((certirocq_value_bits) (x)) & 1) != 0)
#define Is_block(x)  ((((certirocq_value_bits) (x)) & 1) == 0)

/* Long encoding. */
#define Val_long(x)          ((value) ((((certirocq_value_bits)(x)) << 1) + 1))
#define Long_val(x)          ((x) >> 1)
#define Unsigned_long_val(x) ((certirocq_value_bits)(x) >> 1)
#define Max_long             ((value) (((certirocq_value_bits)1 << (8 * sizeof(value) - 2)) - 1))
#define Min_long             (-((value) ((certirocq_value_bits)1 << (8 * sizeof(value) - 2))))

/* Header layout (OCaml-compatible):
 *     +--------+-------+-----+
 *     | wosize | color | tag |
 *     +--------+-------+-----+
 * bits   N..10   9..8    7..0
 */
#define Tag_hd(hd)    ((unsigned int) ((certirocq_value_bits) (hd) & 0xFF))
#define Wosize_hd(hd) ((size_t) ((certirocq_value_bits) (hd) >> 10))

/* Header / field accessors. v points at the first field; header is at v[-1]. */
#define Hd_val(val)   (Ptr_val(val) [-1])

#define Op_val(x)     (Ptr_val(x))
#define Field(x, i)   (Ptr_val(x) [i])
#define Byte(x, i)    (Bp_val(x) [i])

#define Wosize_val(val) (Wosize_hd (Hd_val (val)))
#define Bosize_val(val) (Wosize_val(val) * sizeof(value))

/* Block tags. */
#define No_scan_tag 251
#define String_tag  252
#define No_scan(t)  ((t) >= No_scan_tag)

/* Boxed double payload (no_scan block whose data is a raw double). */
#define Double_val(v) (* (double *) Ptr_val(v))

#ifdef __cplusplus
}
#endif

#endif /* VALUES_H */
