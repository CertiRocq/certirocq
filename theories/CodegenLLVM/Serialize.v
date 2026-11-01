(** * CodegenLLVM.Serialize — render the emitter's [LLVMAst] output to [.ll] text.
    The textual analogue of the Wasm backend's [binary_of_module]: map Vellvm's
    pretty-printer [show_tle] over the emitted top-level entities and join with
    newlines. [serialize_program] yields a [list Byte.byte] (as the Wasm
    backend's [binary_of_module]); the pipeline uses the equivalent, stack-safe
    [serialize_bytestring] (see below).

    Before printing, every numeric identifier is renamed to a [Name]
    ([rename_tles]).  Vellvm's printer shows both [Anon n] (the emitter's
    block labels and top-level functions) and [Raw n] (ANF variables) as the
    bare number [n], so the text would conflate [Anon n] with [Raw n], and
    LLVM's parser rejects numbered values and labels that are not defined in
    increasing order ("label expected to be numbered 'k' or greater").  The
    renaming [Anon n -> "A<n>"], [Raw z -> "R<z>"] (e.g. [%R-6]),
    [Name s -> s] is injective on the emitted names (which never start with
    [A]/[R] followed by a digit or [-]), so it is an alpha-renaming; it only
    affects the text, not the AST [emitted] that the correctness theorem is
    about. *)

From Vellvm Require Import Syntax.LLVMAst Syntax.ShowAST Syntax.Traversal.
From Stdlib Require Import List String Ascii BinInt DecimalString.
From MetaRocq.Utils Require bytestring.
Import ListNotations.
Open Scope string_scope.

Definition Z_to_string (z : Z) : string := NilZero.string_of_int (Z.to_int z).

Definition rename_raw_id (r : raw_id) : raw_id :=
  match r with
  | Name s => Name s
  | Anon n => Name ("A" ++ Z_to_string n)
  | Raw n => Name ("R" ++ Z_to_string n)
  end.

Definition rename_tles
  : list (toplevel_entity typ (block typ * list (block typ))) ->
    list (toplevel_entity typ (block typ * list (block typ))) :=
  let _ : Endo raw_id := rename_raw_id in endo.

Definition ll_newline : string := String (Ascii.ascii_of_nat 10) EmptyString.

Definition serialize_definition
    (d : definition typ (block typ * list (block typ))) : string :=
  show_tle (TLE_Definition d).

Definition serialize_string
    (tles : list (toplevel_entity typ (block typ * list (block typ)))) : string :=
  String.concat ll_newline (List.map show_tle (rename_tles tles)).

Definition serialize_program
    (tles : list (toplevel_entity typ (block typ * list (block typ)))) :=
  List.map Ascii.byte_of_ascii (list_ascii_of_string (serialize_string tles)).

(** Stack-safe variant used by the pipeline ([pipeline.compile_LLVM]).
    [serialize_program] followed by [bytestring.String.parse] recurses once
    per output character (Stdlib's [String.concat], [list_ascii_of_string],
    [List.map] and [String.parse] are not tail recursive); a module of a few
    hundred kilobytes then overflows the 8 MiB default stack of [rocq c]
    ("Error: Stack overflow.").  Here every loop is tail recursive: each
    entity is shown separately ([show_tle] is itself built on Vellvm's
    tail-recursive [DString]), its characters are pushed in reverse onto an
    accumulator, and the bytestring is built back to front. *)
Fixpoint push_rev (s : string) (acc : list Byte.byte) : list Byte.byte :=
  match s with
  | EmptyString => acc
  | String c s' => push_rev s' (Ascii.byte_of_ascii c :: acc)
  end.

Definition serialize_bytestring
    (tles : list (toplevel_entity typ (block typ * list (block typ))))
  : bytestring.String.t :=
  let rev_bytes :=
    List.fold_left
      (fun acc '(i, tle) =>
         push_rev (show_tle tle)
           (if Nat.eqb i 0 then acc else push_rev ll_newline acc))
      (List.combine (List.seq 0 (List.length tles)) (rename_tles tles)) [] in
  List.fold_left (fun bs b => bytestring.String.String b bs) rev_bytes
    bytestring.String.EmptyString.
