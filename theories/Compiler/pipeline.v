Require Export L1g.toplevel L2k.toplevel L4.toplevel L6.toplevel L7.toplevel.
Require Import compcert.lib.Maps.
Require Import ZArith.
Require Import Common.Common Common.compM Common.Pipeline_utils.
Require Import String.
Require Import maps_util.
Require Import Glue.glue.
Require Import ExtLib.Structures.Monad.

Import Monads.
Import MonadNotation.

(** * Compiler Pipeline *)

(* NOTE : The ANF and CPS pipeline should be unified when we have the L4 -> L6 CPS translation *)
Definition pipeline_CPS (p : Template.Ast.program) :=
  p <- compile_L1g p ;;
  p <- compile_L2k p ;;
  p <- compile_L2k_eta p ;;
  p <- compile_L4 p ;;
  p <- compile_L4_2 p ;;
  p <- compile_L4_5 p ;;
  p <- compile_L5 p ;;
  p <- compile_L6_CPS p ;;
  L6_trans p.

Definition pipeline_ANF (p : Template.Ast.program) :=
  p <- compile_L1g p ;;
  p <- compile_L2k p ;;
  p <- compile_L2k_eta p ;;
  p <- compile_L4 p ;;
  p <- compile_L6_ANF p ;;
  L6_trans p.
  
Definition pipeline (p : Template.Ast.program) :=
  o <- get_options ;;
  p <- (if direct o then
         pipeline_ANF p
       else
         pipeline_CPS p) ;;
  compile_Clight p.

(* TODO better notation for threading the program, maybe monad for
   CertiCoq trans *)

Definition default_opts : Options :=
  {| direct := false;
     c_args := 5;
     show_anf := false;
     o_level := 0;
     time := false;
     debug := false;
     dev := 0 |}.

Definition make_opts (cps : bool) (args : nat) (o_level : nat) (time : bool) (debug : bool) : Options :=
  {| direct := negb cps;
     c_args := args;
     show_anf := false;
     o_level := o_level;
     time := time;
     debug := debug;
     dev := 0 |}.

Definition printProg :=
  fun prog file =>
    L6_to_Clight.print_Clight_dest_names (snd prog) (cps.M.elements (fst prog)) file.

Definition compile (opts : Options) (p : Template.Ast.program) :=
  run_pipeline _ _ opts p pipeline.


Definition show_IR (opts : Options) (p : Template.Ast.program) : (error string * string) :=
  let (perr, log) :=
      if direct opts then
        run_pipeline _ _ opts p pipeline_ANF
      else
        run_pipeline _ _ opts p pipeline_CPS
  in
  match perr with
  | Ret p =>
    let '(pr, cenv, _, _, nenv, fenv, _,  e) := p in
    (Ret (cps_show.show_exp nenv cenv false e), log)
  | Err s => (Err s, log)
  end.
 


(** * Glue Code *)

Definition make_glue (opts : Options) (p : Template.Ast.program)
  : error (cps_util.name_env * Clight.program * Clight.program * list string)  :=
  match generate_glue opts p with
  | Ret (nenv, Some hdr, Some prg, logs) =>
    Ret (nenv, hdr, prg, logs)
  | _ => Err "Error in generating glue code"
  end.
