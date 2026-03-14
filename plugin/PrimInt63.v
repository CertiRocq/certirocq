From CertiRocq.Plugin Require Import Loader.
From Corelib Require Import Numbers.Cyclic.Int63.PrimInt63.

CertiRocq Register [
  Corelib.Numbers.Cyclic.Int63.PrimInt63.int => "erased",
  Corelib.Numbers.Cyclic.Int63.PrimInt63.add => "prim_int63_add",
  Corelib.Numbers.Cyclic.Int63.PrimInt63.land => "prim_int63_land",
  Corelib.Numbers.Cyclic.Int63.PrimInt63.lor => "prim_int63_lor",
  Corelib.Numbers.Cyclic.Int63.PrimInt63.lxor => "prim_int63_lxor",
  Corelib.Numbers.Cyclic.Int63.PrimInt63.lsr => "prim_int63_lsr",
  Corelib.Numbers.Cyclic.Int63.PrimInt63.lsl => "prim_int63_lsl",
  Corelib.Numbers.Cyclic.Int63.PrimInt63.eqb => "prim_int63_eqb",
  Corelib.Numbers.Cyclic.Int63.PrimInt63.head0 => "prim_int63_head0",
  Corelib.Numbers.Cyclic.Int63.PrimInt63.tail0 => "prim_int63_tail0",
  Corelib.Numbers.Cyclic.Int63.PrimInt63.compare => "prim_int63_compare",
  Corelib.Numbers.Cyclic.Int63.PrimInt63.compares => "prim_int63_compare",
  Corelib.Numbers.Cyclic.Int63.PrimInt63.asr => "prim_int63_asr",
  Corelib.Numbers.Cyclic.Int63.PrimInt63.subc => "prim_int63_subc" with tinfo,
  Corelib.Numbers.Cyclic.Int63.PrimInt63.sub => "prim_int63_sub",
  Corelib.Numbers.Cyclic.Int63.PrimInt63.addc => "prim_int63_addc" with tinfo,
  Corelib.Numbers.Cyclic.Int63.PrimInt63.addcarryc => "prim_int63_addcarryc" with tinfo,
  Corelib.Numbers.Cyclic.Int63.PrimInt63.subcarryc => "prim_int63_subcarryc" with tinfo,
  Corelib.Numbers.Cyclic.Int63.PrimInt63.mulc => "prim_int63_mulc" with tinfo,
  Corelib.Numbers.Cyclic.Int63.PrimInt63.mul => "prim_int63_mul",
  Corelib.Numbers.Cyclic.Int63.PrimInt63.div => "prim_int63_div",
  Corelib.Numbers.Cyclic.Int63.PrimInt63.divs => "prim_int63_divs",
  Corelib.Numbers.Cyclic.Int63.PrimInt63.mod => "prim_int63_mod",
  Corelib.Numbers.Cyclic.Int63.PrimInt63.mods => "prim_int63_mods",
  Corelib.Numbers.Cyclic.Int63.PrimInt63.diveucl_21 => "prim_int63_diveucl_21" with tinfo,
  Corelib.Numbers.Cyclic.Int63.PrimInt63.diveucl => "prim_int63_diveucl" with tinfo,
  Corelib.Numbers.Cyclic.Int63.PrimInt63.addmuldiv => "prim_int63_addmuldiv",
  Corelib.Numbers.Cyclic.Int63.PrimInt63.leb => "prim_int63_leb",
  Corelib.Numbers.Cyclic.Int63.PrimInt63.ltb => "prim_int63_ltb",
  Corelib.Numbers.Cyclic.Int63.PrimInt63.lesb => "prim_int63_lesb",
  Corelib.Numbers.Cyclic.Int63.PrimInt63.ltsb => "prim_int63_ltsb"
]
Include [ Library "prim_int63.h" ].
