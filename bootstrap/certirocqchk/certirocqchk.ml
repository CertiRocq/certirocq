(**********************************************************************)
(* CertiRocq                                                           *)
(* Copyright (c) 2022                                                 *)
(**********************************************************************)

open Pp
open Printer
open Metarocq_template_plugin.Ast_quoter
open AstCommon
open Plugin_utils

let quote ~opaque_access gr =
  let env = Global.env () in
  let sigma = Evd.from_env env in
  let sigma, c = Evd.fresh_global env sigma gr in
  let term = Metarocq_template_plugin.Ast_quoter.quote_term_rec
               ~bypass:true ~opaque_access env sigma (EConstr.to_constr sigma c) in
  term

let check ~opaque_access gr =
  (* Quote Coq term *)
  let p = quote ~opaque_access gr in
  let b = Certirocqchk_plugin_wrapper.check (Obj.magic p) (* Go through a type equality *) in
  if b then () else CErrors.user_err Pp.(str"The program does not typecheck")
