Require compcert.common.AST
        compcert.common.Errors
        compcert.common.Values
        compcert.lib.Integers
        compcert.cfrontend.Cop
        compcert.cfrontend.Ctypes
        compcert.cfrontend.Clight
        compcert.cfrontend.Csyntax
        compcert.lib.Coqlib
        compcert.lib.Floats
        compcert.common.Globalenvs
    (*    Int31*).

Require Glue.glue
        Compiler.pipeline.

From Stdlib Require Import extraction.Extraction.
Require Import VanillaExtrOCamlInt63 VanillaExtrOCamlFloats.
From Stdlib Require Import ExtrOCamlPString.
(* Standard lib *)

(** Extraction to Ocaml : use of basic Ocaml types: be careful that this should
  the representation in ML should exactly match the one of certirocq.
  E.g. no constructor swapping allowed.
  *)

Extract Inductive bool => bool [ true false ]. (* Swaps the constructors *)
Extract Inductive unit => unit [ "()" ].
Extract Inductive list => list [ "[]" "( :: )" ].
Extract Inductive prod => "( * )" [ "" ].

(** NB: The "" above is a hack, but produce nicer code than "(,)" *)

(** Restore laziness of andb, orb.
    NB: without these Extract Constant, andb/orb would be inlined
    by extraction in order to have laziness, producing inelegant
    (if ... then ... else false) and (if ... then true else ...).
*)

Extract Inlined Constant andb => "(&&)".
Extract Inlined Constant orb => "(||)".

From Stdlib Require Import ZArith NArith.

Extraction Inline Program.Wf.Fix_F_sub.
Extraction Inline Program.Wf.Fix_sub.

Set Extraction KeepSingleton.

(* Coqlib *)
(* Extract Inlined Constant Coqlib.proj_sumbool => "(fun x -> x)". *)

(* LambdaANF_to_Clight *)
(* Extract Constant pipeline.print_Clight => "PrintClight.print_if". *)
(* Extract Constant LambdaANF_to_Clight.print_Clight_dest => "PrintClight.print_dest". *)
(* Extract Constant LambdaANF_to_Clight.print_Clight_dest_names => "PrintClight.print_dest_names". *)
(* Extract Constant pipeline.print_Clight_names_dest_imports => "PrintClight.print_dest_names_imports". *)
(* Extract Constant pipeline.print => "print_string". *)


(* Time each phase, print to debug channel *)

Extract Constant AstCommon.timePhase =>
"(fun c x a -> let time = Unix.gettimeofday() in
               let temp = x a in
               let time = (Unix.gettimeofday() -. time) in
               Feedback.msg_debug (Pp.str (Printf.sprintf ""Time elapsed in %s:  %f"" (Caml_bytestring.caml_string_of_bytestring c) time));
               temp)".

Extract Inductive Decimal.int => "decimal_int" [ "DecimalPos" "DecimalNeg" ] "(fun hp hn d -> match d with DecimalPos p -> hp p | DecimalNeg p -> hn p)".
Extract Inductive Hexadecimal.int => "hexadecimal_int" [ "HexadecimalPos" "HexadecimalNeg" ] "(fun hp hn d -> match d with HexadecimalPos p -> hp p | HexadecimalNeg p -> hn p)".
Extract Inductive Number.int => "number_int" [ "IntDecimal" "IntHexadecimal" ] "(fun hp hn d -> match d with IntDecimal p -> hp p | IntHexadecimal p -> hn p)".

Extraction Inline Equations.Prop.Classes.noConfusion.
Extraction Inline Equations.Prop.Logic.eq_elim.
Extraction Inline Equations.Prop.Logic.eq_elim_r.
Extraction Inline Equations.Prop.Logic.transport.
Extraction Inline Equations.Prop.Logic.transport_r.
Extraction Inline Equations.Prop.Logic.False_rect_dep.
Extraction Inline Equations.Prop.Logic.True_rect_dep.
Extraction Inline Equations.Init.pr1.
Extraction Inline Equations.Init.pr2.
Extraction Inline Equations.Init.hidebody.
Extraction Inline Equations.Prop.DepElim.solution_left.

(* Avoid name clashes with OCaml or Coq module names *)
Extraction Blacklist config List String Nat Int Ast Universes UnivSubst Typing Retyping
           OrderedType Logic Common Equality Char char uGraph
           Instances Classes Term Monad Coqlib Errors Compile Checker Eq Classes0 Numeral
           Uint63 Number Values.

Set Warnings "-extraction-reserved-identifier".
Set Warnings "-extraction-opaque-accessed".

Set Extraction Output Directory ".".

(* Extraction Library Zeven. *)
(* Extraction Library Zeven. *)
(* Extraction Library ZArith_dec. *)
(* Extraction Library Sumbool. *)
(* Extraction Library Zbool. *)
(* Extraction Library SpecFloat. *)
Separate Extraction FloatOps.Prim2SF.

Cd "ExtractionVanilla".
Separate Extraction
         Ctypes.merge_attributes Ctypes.remove_attributes Ctypes.build_composite_env
         Csyntax
         Clight
         Ctypes.make_program
         AST.signature_main
         Floats.Float32.from_parsed Floats.Float.from_parsed
         Floats.Float32.of_bits Floats.Float.of_bits
         Floats.Float32.to_bits Floats.Float.to_bits
         String.length
         Compiler.pipeline.make_opts
         Compiler.pipeline.compile
         Erasure.default_dearging_config
         Glue.glue.generate_glue
         term.M.elements
         Compiler.pipeline.show_IR.

Recursive Extraction Library Ascii.
Recursive Extraction Library BinPos.
Recursive Extraction Library OrdersTac.

Cd "..".
