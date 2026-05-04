From MetaRocq Require Import Show.
From MetaRocq.Utils Require Import bytestring MRString.
From CertiRocq.Plugin Require Import Loader PrimInt63.
From Corelib Require Import PrimInt63 PrimString PrimStringAxioms.

Definition string_of_pstring (s : string) : bytestring.string :=
  MRString.string_of_list_aux char63_to_string ""%bs (PrimStringAxioms.to_list s).

(* Very inefficient!, we're concatenating each char. No other way with the current API.
   Would need `make_from_fun : int63 -> (int63 -> char63) -> string` *)

Fixpoint pstring_of_string (s : bytestring.string) : string :=
  match s with
  | String.EmptyString       => ""%pstring
  | String.String b cs => cat (make 1 (Uint63Axioms.of_Z (IntDef.Z.of_N (Byte.to_N b))))
                            (pstring_of_string cs)
  end.

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
