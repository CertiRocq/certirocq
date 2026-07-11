(** * CodegenLLVM.Serialize — render the emitter's [LLVMAst] output to [.ll] text.
    The textual analogue of the Wasm backend's [binary_of_module]: map Vellvm's
    pretty-printer [show_tle] over the emitted top-level entities and join with
    newlines. [serialize_program] yields a [list Byte.byte] for the pipeline's
    bytestring [String.parse], exactly as the Wasm backend feeds [binary_of_module]. *)

From Vellvm Require Import Syntax.LLVMAst Syntax.ShowAST.
From Stdlib Require Import List String Ascii.
Import ListNotations.
Open Scope string_scope.

Definition ll_newline : string := String (Ascii.ascii_of_nat 10) EmptyString.

Definition serialize_definition
    (d : definition typ (block typ * list (block typ))) : string :=
  show_tle (TLE_Definition d).

Definition serialize_string
    (tles : list (toplevel_entity typ (block typ * list (block typ)))) : string :=
  String.concat ll_newline (List.map show_tle tles).

Definition serialize_program
    (tles : list (toplevel_entity typ (block typ * list (block typ)))) :=
  List.map Ascii.byte_of_ascii (list_ascii_of_string (serialize_string tles)).
