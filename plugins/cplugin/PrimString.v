From CertiRocq.VanillaPlugin Require Import Loader.
From Corelib Require Import PrimString.

CertiRocq Register [
  Corelib.Strings.PrimString.compare => "prim_string_compare",
  Corelib.Strings.PrimString.get => "prim_string_get",
  Corelib.Strings.PrimString.length => "prim_string_length",
  Corelib.Strings.PrimString.max_length => "prim_string_max_length",
  Corelib.Strings.PrimString.make => "prim_string_make" with tinfo,
  Corelib.Strings.PrimString.sub => "prim_string_sub" with tinfo,
  Corelib.Strings.PrimString.cat => "prim_string_cat" with tinfo
]
Include [ Library "prim_string.h" ].
