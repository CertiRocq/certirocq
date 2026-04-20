(**********************************************************************)
(* CertiRocq                                                           *)
(* Copyright (c) 2017                                                 *)
(**********************************************************************)

open Pp
open Printer
open Metarocq_template_plugin.Ast_quoter
open ExceptionMonad
open AstCommon
open Plugin_utils

module MLCompiler : Certirocq.CompilerInterface with
  type name_env = BasicAst.name Term0.M.t
  = struct
  type name_env = BasicAst.name Term0.M.t
  let compile = Certirocqc_plugin_wrapper.compile
  let printProg prog names (dest : string) (imports : import list) =
    let imports' = List.map (fun i -> match i with
      | FromRelativePath s -> "#include \"" ^ s ^ "\""
      | FromLibrary (s, _) -> "#include <" ^ s ^ ">"
      | FromAbsolutePath s ->
          failwith "Import with absolute path should have been filled") imports in
    PrintClight.print_dest_names_imports prog (Term0.M.elements names) dest imports'

  let generate_glue = Glue.generate_glue
  let generate_ffi = Ffi.generate_ffi
end

module CCompile = Certirocq.CompileFunctor (MLCompiler)
include CCompile
