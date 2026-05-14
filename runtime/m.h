#ifndef M_H
#define M_H

/* Architecture-dependent sizes (in bytes).
 *
 * SIZEOF_PTR is the C data-pointer width for the target. SIZEOF_CODE_PTR is
 * the generated closure code-pointer width; override it for targets where
 * code pointers differ from data pointers. SIZEOF_VALUE is the width of a
 * Rocq value slot; it may be larger than pointers on small targets. */

#ifndef SIZEOF_PTR
#  ifdef __SIZEOF_POINTER__
#    define SIZEOF_PTR __SIZEOF_POINTER__
#  else
#    error "SIZEOF_PTR is not defined; pass -DSIZEOF_PTR=<bytes> for this target"
#  endif
#endif

#ifndef SIZEOF_VALUE
#  define SIZEOF_VALUE SIZEOF_PTR
#endif

#ifndef SIZEOF_CODE_PTR
#  define SIZEOF_CODE_PTR SIZEOF_PTR
#endif

#endif /* M_H */
