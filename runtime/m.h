#ifndef M_H
#define M_H

/* Architecture-dependent sizes (in bytes).
 *
 * Auto-detected from the __SIZEOF_*__ macros that GCC and Clang predefine.
 * If the toolchain does not expose them, override SIZEOF_PTR / SIZEOF_LONG
 * / SIZEOF_INT on the command line; the fallbacks below assume a 64-bit
 * LP64 host and are unlikely to be right on smaller targets. */

#ifndef SIZEOF_PTR
#  ifdef __SIZEOF_POINTER__
#    define SIZEOF_PTR __SIZEOF_POINTER__
#  else
#    define SIZEOF_PTR 8
#  endif
#endif

#ifndef SIZEOF_LONG
#  ifdef __SIZEOF_LONG__
#    define SIZEOF_LONG __SIZEOF_LONG__
#  else
#    define SIZEOF_LONG SIZEOF_PTR
#  endif
#endif

#ifndef SIZEOF_INT
#  ifdef __SIZEOF_INT__
#    define SIZEOF_INT __SIZEOF_INT__
#  else
#    define SIZEOF_INT 4
#  endif
#endif

#endif /* M_H */
