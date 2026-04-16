From Stdlib Require Import Arith List String ZArith.
Require Import CertiRocq.Tests.lib.vs.
Require Import CertiRocq.Tests.lib.Binom.
Require Import CertiRocq.Tests.lib.Color.
Require Import CertiRocq.Tests.lib.sha256.

From CertiRocq.Plugin Require Import CertiRocq.

From MetaRocq.Erasure Require Import EProgram.
From MetaRocq.ErasurePlugin Require Import Erasure Loader.
Require Import MetaRocq.Utils.bytestring.

Open Scope bs_scope.

Axiom (msg_info : string -> unit).
Axiom (msg_debug : string -> unit).

Set MetaRocq Timing.

Local Existing Instance config.extraction_checker_flags.

Program Definition erase (p : Ast.Env.program) : eprogram :=
  run_erase_program default_erasure_config (nil, p) (MRUtils.todo "wf_env and welltyped term").

Program Definition erase_and_print_template_program (p : Ast.Env.program) : unit :=
  let _ := msg_info ("Erasing program.") in
  let prprog := msg_info (Pretty.print_program false 2 p) in
  let eprog := run_erase_program default_erasure_config (nil, p) (MRUtils.todo "wf_env and welltyped term") in
  let _ := msg_info "Erasure terminated with: " in
  msg_info (EPretty.print_program eprog).

Definition metarocq_erasure (p : Ast.Env.program) :=
  erase_and_print_template_program p.

CertiRocq Compile -time -O 1 metarocq_erasure
Extract Constants [
  (* rocq_msg_debug => "print_msg_debug", *)
  msg_info => "rocq_msg_info",
  PCUICWfEnvImpl.guard_impl => "metarocq_guard_impl" ]
Include [ "print.h" ].

(*
From MetaRocq.SafeChecker Require Import PCUICSafeChecker.

(*Extract Constant PCUICTyping.guard_checking =>
"{ guard = (fun _ _ _ _ -> true) }". *)

CertiRocq Compile -O 0 typecheck_program
Extract Constants [
  (* rocq_msg_debug => "print_msg_debug", *)
  PCUICTyping.guard_checking => "print_msg_info",
  rocq_msg_info => "print_msg_info"
   ]
Include [ "print.h" ].*)
