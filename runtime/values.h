/**************************************************************************/
/*                                                                        */
/*                                 OCaml                                  */
/*                                                                        */
/*          Xavier Leroy and Damien Doligez, INRIA Rocquencourt           */
/*                                                                        */
/*   Copyright 1996 Institut National de Recherche en Informatique et     */
/*     en Automatique.                                                    */
/*                                                                        */
/*   All rights reserved.  This file is distributed under the terms of    */
/*   the GNU Lesser General Public License version 2.1, with the          */
/*   special exception on linking described in the file LICENSE.          */
/*                                                                        */
/**************************************************************************/

#ifndef VALUES_H
#define VALUES_H

#include "config.h"

#ifdef __cplusplus
extern "C" {
#endif

/* Value layout follows OCaml's:
 *  value  : either a long with the low bit set, or a pointer to the
 *           first field of a block.
 *  block  : a header word followed by N word-sized fields.
 *  header : encodes word size, two color bits (reserved for OCaml's GC;
 *           unused by the CertiRocq generational GC, which signals
 *           forwarded blocks by overwriting the header with 0), and a
 *           constructor tag. */

typedef intnat  value;
typedef uintnat header_t;
typedef uintnat mlsize_t;

/* Long vs block discrimination (tag bit). */
#define Is_long(x)   (((x) & 1) != 0)
#define Is_block(x)  (((x) & 1) == 0)

/* Long encoding. */
#define Val_long(x)          ((intnat) (((uintnat)(x) << 1)) + 1)
#define Long_val(x)          ((x) >> 1)
#define Unsigned_long_val(x) ((uintnat)(x) >> 1)
#define Max_long             (((intnat)1 << (8 * sizeof(value) - 2)) - 1)
#define Min_long             (-((intnat)1 << (8 * sizeof(value) - 2)))

/* Header layout (OCaml-compatible):
 *     +--------+-------+-----+
 *     | wosize | color | tag |
 *     +--------+-------+-----+
 * bits   N..10   9..8    7..0
 */
#define Tag_hd(hd)    ((unsigned int) ((hd) & 0xFF))
#define Wosize_hd(hd) ((mlsize_t) ((hd) >> 10))

/* Header / field accessors. v points at the first field; header is at v[-1]. */
#define Hd_val(val)   (((header_t *) (val)) [-1])

#define Op_val(x)     ((value *) (x))
#define Field(x, i)   (((value *)(x)) [i])
#define Bp_val(v)     ((char *) (v))
#define Byte(x, i)    (((char *) (x)) [i])

#define Wosize_val(val) (Wosize_hd (Hd_val (val)))
#define Bosize_val(val) (Wosize_val(val) * sizeof(value))

/* Block tags. */
#define No_scan_tag 251
#define String_tag  252
#define No_scan(t)  ((t) >= No_scan_tag)

/* Boxed double payload (no_scan block whose data is a raw double). */
#define Double_val(v) (* (double *)(v))

#ifdef __cplusplus
}
#endif

#endif /* VALUES_H */
