Require Export L2k.toplevel L4.toplevel L6.toplevel L7.toplevel.
Require Import compcert.lib.Maps.
Require Import ZArith.
Require Import Common.Common Common.compM Common.Pipeline_utils.
Require Import List.
Require Import maps_util.
Require Import Glue.glue.
Require Import Glue.ffi.
Require Import ExtLib.Structures.Monad.
Require Import MetaCoq.Template.BasicAst.
From MetaCoq.Template Require Import MCString.

Import Monads.
Import MonadNotation.
Import ListNotations.

(* Axioms that are only realized in ocaml *)
Axiom (print_Clight : Clight.program -> Datatypes.unit).
Axiom (print_Clight_names_dest_imports : Clight.program -> list (positive * name) -> String.string -> list String.string -> Datatypes.unit).
Axiom (print : String.string -> Datatypes.unit).

(** * Constants realized in the target code *)

(* Each constant that is realized in the backend must have an associated arrity.
 * We find the arity of the extracted constant from its type in [global_env]
 * after reification. Assumes that the type is in some normal form.
 *)

Fixpoint find_arrity (tau : Ast.term) : nat :=
  match tau with
  | Ast.tProd na ty body => 1 + find_arrity body
  | _ => 0
  end.

Definition find_global_decl_arrity (gd : Ast.Env.global_decl) : error nat :=
  match gd with
  | Ast.Env.ConstantDecl bd => Ret (find_arrity (Ast.Env.cst_type bd))
  | Ast.Env.InductiveDecl _ => Err ("Expected ConstantDecl but found InductiveDecl")
  end.


Fixpoint find_prim_arrity (env : Ast.Env.global_declarations) (pr : kername) : error nat :=
  match env with
  | [] => Err ("Constant " ++ string_of_kername pr ++ " not found in environment")
  | (n, gd) :: env =>
    if eq_kername pr n then find_global_decl_arrity  gd
    else find_prim_arrity env pr
  end.

Fixpoint find_prim_arrities (env : Ast.Env.global_declarations) (prs : list (kername * string * bool)) : error (list (kername * string * bool * nat * positive)) :=
  match prs with
  | [] => Ret []
  | ((pr, s), b) :: prs =>
    arr <- find_prim_arrity env pr ;;
    prs' <- find_prim_arrities env prs ;;
    Ret ((pr, s, b, arr, 1%positive) :: prs')
  end.

(* Picks an identifier for each primitive for internal representation *)
Fixpoint pick_prim_ident (id : positive) (prs : list (kername * string * bool * nat * positive))
: (list (kername * string * bool * nat * positive) * positive) :=
  match prs with
  | [] => ([], id)
  | (pr, s, b, a, _) :: prs =>
    let next_id := (id + 1)%positive in
    let (prs', id') := pick_prim_ident next_id prs in
    ((pr, s, b, a, id) :: prs', id')
  end.


Definition register_prims (id : positive) (env : Ast.Env.global_declarations) : pipelineM (list (kername * string * bool * nat * positive) * positive) :=
  o <- get_options ;;
  match find_prim_arrities env (prims o) with
  | Ret prs =>
    ret (pick_prim_ident id prs)
  | Err s => failwith s
  end.

(** * CertiCoq's Compilation Pipeline, without code generation *)

Section Pipeline.

  Context (next_id : positive)
          (prims : list (kername * string * bool * nat * positive))
          (debug : bool).

  Fixpoint find_axioms {T} acc (env : environ T) := 
    match env with
    | [] => acc
    | (kn, d) :: decls => 
      match d with
      | ecTrm _ => find_axioms acc decls
      | ecTyp 0 [] => find_axioms (kn :: acc) decls
      | ecTyp _ _ => find_axioms acc decls
      end 
    end.

  Definition check_axioms (p : Program (compile.Term)) : pipelineM Datatypes.unit :=
    match find_axioms [] p.(env) with
    | [] => ret tt 
    | l => debug_msg ("Axioms found, use Extract Constants to realize them in C: " ++ newline ++
      print_list string_of_kername ", " l)%bs
    end.

  Definition CertiCoq_pipeline (p : Ast.Env.program) :=
    o <- get_options ;;
    p <- compile_L2k p ;;
    check_axioms p ;;
    p <- compile_L4 prims p ;;
    p <- (if direct o then compile_L6_ANF next_id prims p else compile_L6_CPS next_id prims p) ;;
    if debug then compile_L6_debug next_id p  (* For debugging intermediate states of the λanf pipeline *)
    else compile_L6 next_id p.
    

End Pipeline.

Definition next_id := 100%positive.

(** * The main CertiCoq pipeline, with MetaCoq's erasure and C-code generation *)

Definition pipeline (p : Template.Ast.Env.program) :=
  let genv := fst p in
  '(prs, next_id) <- register_prims next_id genv.(Ast.Env.declarations) ;;
(*   p <- erase_PCUIC p ;;
 *)  p <- CertiCoq_pipeline next_id prs false p ;;
  compile_Clight prs p.
 

Definition default_opts : Options :=
  {| direct := false;
     c_args := 5;
     anf_conf := 0;
     show_anf := false;
     o_level := 0;
     time := false;
     time_anf := false;
     debug := false;
     dev := 0;
     Pipeline_utils.prefix := "";
     prims := [];
  |}.

Definition make_opts
           (cps : bool)                              (* CPS or direct *)
           (args : nat)                              (* number of C args *)
           (conf : nat)                              (* λ_ANF configuration *)
           (o_level : nat)                           (* optimization level *)
           (time : bool) (time_anf : bool)           (* timing options *)
           (debug : bool)                            (* Debug log *)
           (dev : nat)                               (* Extra flag for development purposes *)
           (prefix : string)                         (* Prefix for the FFI. Check why is this needed in the pipeline and not just the plugin *)
           (prims : list (kername * string * bool))  (* list of extracted constants *)
  : Options :=
  {| direct := negb cps;
     c_args := args;
     anf_conf := conf;
     show_anf := false;
     o_level := o_level;
     time := time;
     time_anf := time_anf;
     debug := debug;
     dev := dev;
     Pipeline_utils.prefix := prefix;
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
      (* p <- erase_PCUIC p ;; *) CertiCoq_pipeline next_id prims (dev o =? 3)%nat p
  in
  let (perr, log) := run_pipeline _ _ opts p ir_term in
  match perr with
  | Ret p =>
    let '(pr, cenv, _, _, nenv, fenv, _,  e) := p in
    (Ret (cps_show.show_exp nenv cenv false e), log)
  | Err s => (Err s, log)
  end.
