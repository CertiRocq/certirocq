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
       (* Int63*).

Require Glue.glue
        Compiler.pipeline.

From MetaRocq.ErasurePlugin Require Import Erasure.
(* Standard lib *)
From Stdlib Require Import ExtrOcamlBasic ExtrOCamlFloats ExtrOCamlInt63 ExtrOCamlPString.
From Stdlib Require Import extraction.Extraction.
From Stdlib Require Import ZArith NArith.

Extraction Inline Program.Wf.Fix_F_sub.
Extraction Inline Program.Wf.Fix_sub.

(* Coqlib *)
Extract Inlined Constant Coqlib.proj_sumbool => "(fun x -> x)".

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

(* Int31
Extract Inductive Int31.digits => "bool" [ "false" "true" ].
Extract Inductive Int31.int31 => "int" [ "Camlrocq.Int31.constr" ] "Camlrocq.Int31.destr".
Extract Constant Int31.twice => "Camlrocq.Int31.twice".
Extract Constant Int31.twice_plus_one => "Camlrocq.Int31.twice_plus_one".
Extract Constant Int31.compare31 => "Camlrocq.Int31.compare".
Extract Constant Int31.On => "0".
Extract Constant Int31.In => "1". *)

(* Extract Inductive Decimal.int => "decimal_int" [ "DecimalPos" "DecimalNeg" ] "(fun hp hn d -> match d with DecimalPos p -> hp p | DecimalNeg p -> hn p)". *)
(* Extract Inductive Hexadecimal.int => "hexadecimal_int" [ "HexadecimalPos" "HexadecimalNeg" ] "(fun hp hn d -> match d with HexadecimalPos p -> hp p | HexadecimalNeg p -> hn p)". *)
(* Extract Inductive Number.int => "number_int" [ "IntDecimal" "IntHexadecimal" ] "(fun hp hn d -> match d with IntDecimal p -> hp p | IntHexadecimal p -> hn p)". *)

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

(* Cutting the dependency to R.
Extract Inlined Constant Fcore_defs.F2R => "fun _ -> assert false".
Extract Inlined Constant Fappli_IEEE.FF2R => "fun _ -> assert false".
Extract Inlined Constant Fappli_IEEE.B2R => "fun _ -> assert false".
Extract Inlined Constant Fappli_IEEE.round_mode => "fun _ -> assert false".
Extract Inlined Constant Fcalc_bracket.inbetween_loc => "fun _ -> assert false". *)

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

Cd "Extraction".
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
         Glue.ffi.generate_ffi
         term.M.elements
         Compiler.pipeline.show_IR
         Compiler.pipeline.compile_Wasm.

Recursive Extraction Library Ascii.
Recursive Extraction Library BinPos.
Recursive Extraction Library OrdersTac.

Cd "..".
