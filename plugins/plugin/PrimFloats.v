From CertiRocq.Plugin Require Import Loader.
From Corelib Require Import PrimFloat.

CertiRocq Register [
  Corelib.Floats.PrimFloat.float => "erased",
  Corelib.Floats.PrimFloat.compare => "prim_float_compare",
  Corelib.Floats.PrimFloat.eqb => "prim_float_eqb",
  Corelib.Floats.PrimFloat.ltb => "prim_float_ltb",
  Corelib.Floats.PrimFloat.leb => "prim_float_leb",
  Corelib.Floats.PrimFloat.frshiftexp => "prim_float_frshiftexp" with tinfo,
  Corelib.Floats.PrimFloat.ldshiftexp => "prim_float_ldshiftexp" with tinfo,
  Corelib.Floats.PrimFloat.normfr_mantissa => "prim_float_normfr_mantissa",
  Corelib.Floats.PrimFloat.classify => "prim_float_classify",
  Corelib.Floats.PrimFloat.abs => "prim_float_abs" with tinfo,
  Corelib.Floats.PrimFloat.sqrt => "prim_float_sqrt" with tinfo,
  Corelib.Floats.PrimFloat.opp => "prim_float_opp" with tinfo,
  Corelib.Floats.PrimFloat.div => "prim_float_div" with tinfo,
  Corelib.Floats.PrimFloat.mul => "prim_float_mul" with tinfo,
  Corelib.Floats.PrimFloat.add => "prim_float_add" with tinfo,
  Corelib.Floats.PrimFloat.sub => "prim_float_sub" with tinfo,
  Corelib.Floats.PrimFloat.of_uint63 => "prim_float_of_uint63" with tinfo,
  Corelib.Floats.PrimFloat.next_up => "prim_float_next_up" with tinfo,
  Corelib.Floats.PrimFloat.next_down => "prim_float_next_down" with tinfo ]
Include [ Library "prim_floats.h"  ].
