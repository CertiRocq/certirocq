From Wasm Require Import binary_format_printer.

Require Export LambdaBoxMut.toplevel LambdaBoxLocal.toplevel LambdaANF.toplevel Codegen.toplevel CodegenWasm.toplevel.
Require Import compcert.lib.Maps.
From Stdlib Require Import ZArith.
Require Import Common.Common Common.compM Common.Pipeline_utils.
From Stdlib Require Import List.
Require Import maps_util.
Require Import Glue.glue.
Require Import Glue.ffi.
Require Import ExtLib.Structures.Monad.
Require Import MetaRocq.Common.BasicAst.
From MetaRocq.Utils Require Import MRString.

Import Monads.
Import MonadNotation.
Import ListNotations.

(* Axioms that are only realized in ocaml *)
Axiom (print_Clight : Clight.program -> Datatypes.unit).
Axiom (print_Clight_names_dest_imports : Clight.program -> list (positive * name) -> String.string -> list String.string -> Datatypes.unit).
Axiom (print : String.string -> Datatypes.unit).

(** * Constants realized in the target code *)

(* Picks an identifier for each primitive for internal representation *)
Fixpoint pick_prim_ident (id : positive) (prs : primitives)
  : list (primitive * positive) * positive :=
  match prs with
  | [] => ([], id)
  | pr :: prs =>
    let next_id := (id + 1)%positive in
    let (prs', id') := pick_prim_ident next_id prs in
    ((pr, id) :: prs', id')
  end.

Definition register_prims (id : positive) (env : Ast.Env.global_declarations) : pipelineM (list (primitive * positive) * positive) :=
  o <- get_options ;;
  ret (pick_prim_ident id (prims o)).

(** * CertiRocq's Compilation Pipeline, without code generation *)

Section Pipeline.

  Context (next_id : positive)
          (prims : list (primitive * positive))
          (debug : bool).

  Fixpoint find_axioms {T} acc (env : environ T) :=
    match env with
    | [] => acc
    | (kn, d) :: decls =>
      match d with
      | ecTrm _ => find_axioms acc decls
      | ecTyp 0 [] =>
        if List.find (fun prim => ReflectEq.eqb kn (fst prim).(prim_name)) prims then find_axioms acc decls
        else find_axioms (kn :: acc) decls
      | ecTyp _ _ => find_axioms acc decls
      end
    end.

  Definition check_axioms (p : Program (compile.Term)) : pipelineM Datatypes.unit :=
    match find_axioms [] p.(env) with
    | [] => ret tt
    | l => failwith ("Axioms found, use Extract Constant to realize them in C: " ++ newline ++
      print_list string_of_kername ", " l)%bs
    end.

  Definition CertiRocq_pipeline (p : Ast.Env.program) :=
    o <- get_options ;;
    p <- compile_LambdaBoxMut o.(erasure_config) o.(inductives_mapping) p ;;
    check_axioms p ;;
    p <- compile_LambdaBoxLocal prims p ;;
    p <- (if direct o then compile_LambdaANF_ANF next_id prims p else compile_LambdaANF_CPS next_id prims p) ;;
    if debug then compile_LambdaANF_debug next_id p  (* For debugging intermediate states of the λanf pipeline *)
    else compile_LambdaANF next_id p.


End Pipeline.

Definition next_id := 100%positive.

(** * The main CertiRocq pipeline, with MetaRocq's erasure and C-code generation *)

Definition pipeline (p : Template.Ast.Env.program) :=
  let genv := fst p in
  '(prs, next_id) <- register_prims next_id genv.(Ast.Env.declarations) ;;
(*   p <- erase_PCUIC p ;;
 *)  p <- CertiRocq_pipeline next_id prs false p ;;
  compile_Clight prs p.

Definition pipeline_Wasm (p : Template.Ast.Env.program) :=
  let genv := fst p in
  '(prs, next_id) <- register_prims next_id genv.(Ast.Env.declarations) ;;
(*   p <- erase_PCUIC p ;;
 *)  p <- CertiRocq_pipeline next_id prs false p ;;
     compile_LambdaANF_to_Wasm prs p.

Definition default_opts : Options :=
  {| erasure_config := Erasure.default_erasure_config;
     inductives_mapping := [];
     direct := false;
     c_args := 5;
     anf_conf := 0;
     show_anf := false;
     o_level := 0;
     time := false;
     time_anf := false;
     debug := false;
     dev := 0;
     Pipeline_utils.prefix := "";
     Pipeline_utils.body_name := "body";
     prims := [];
  |}.

Definition make_opts
           (erasure_config : Erasure.erasure_configuration)
           (im : EProgram.inductives_mapping)
           (cps : bool)                              (* CPS or direct *)
           (args : nat)                              (* number of C args *)
           (conf : nat)                              (* λ_ANF configuration *)
           (o_level : nat)                           (* optimization level *)
           (time : bool) (time_anf : bool)           (* timing options *)
           (debug : bool)                            (* Debug log *)
           (dev : nat)                               (* Extra flag for development purposes *)
           (prefix : string)                         (* Prefix for the FFI. Check why is this needed in the pipeline and not just the plugin *)
           (toplevel_name : string)                  (* Name of the toplevel function ("body" by default) *)
           (prims : list primitive)  (* list of extracted constants *)
  : Options :=
  {| erasure_config := erasure_config;
     inductives_mapping := im;
     direct := negb cps;
     c_args := args;
     anf_conf := conf;
     show_anf := false;
     o_level := o_level;
     time := time;
     time_anf := time_anf;
     debug := debug;
     dev := dev;
     Pipeline_utils.prefix := prefix;
     Pipeline_utils.body_name := toplevel_name;
     prims :=  prims |}.


Definition compile (opts : Options) (p : Template.Ast.Env.program) :=
  run_pipeline _ _ opts p pipeline.


(** * For compiling to λ_ANF and printing out the code *)

Definition show_IR (opts : Options) (p : Template.Ast.Env.program) : (error string * string) :=
  let genv := fst p in
  let ir_term p :=
      o <- get_options ;;
      '(prims, next_id) <- register_prims next_id genv.(Ast.Env.declarations) ;;
      (* The flag -dev 3 *)
      (* p <- erase_PCUIC p ;; *) CertiRocq_pipeline next_id prims (dev o =? 3)%nat p
  in
  let (perr, log) := run_pipeline _ _ opts p ir_term in
  match perr with
  | Ret p =>
    let '(pr, cenv, _, _, nenv, fenv, _,  e) := p in
    (Ret (cps_show.show_exp nenv cenv false e), log)
  | Err s => (Err s, log)
  end.


(** * For compiling lambda_ANF to Wasm *)
Definition compile_Wasm (opts : Options) (p : Template.Ast.Env.program) : (error string * string) :=
let (perr, log) := run_pipeline _ _ opts p pipeline_Wasm in
  match perr with
  | Ret p => (Ret (String.parse (binary_of_module p)), log)
  | Err s => (Err s, log)
  end.
