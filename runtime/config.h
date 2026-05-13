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

#ifndef CONFIG_H
#define CONFIG_H

#include <stdint.h>
#include "m.h"

#if SIZEOF_PTR <= 0
#error "SIZEOF_PTR must be defined and positive"
#endif

#if SIZEOF_PTR == SIZEOF_LONG
typedef long intnat;
typedef unsigned long uintnat;
#elif SIZEOF_PTR == SIZEOF_INT
typedef int intnat;
typedef unsigned int uintnat;
#elif SIZEOF_PTR == 8
typedef int64_t intnat;
typedef uint64_t uintnat;
#else
#error "No integer type available to represent pointers"
#endif

#endif /* CONFIG_H */
