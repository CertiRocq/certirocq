Require Export L1g.toplevel L2k.toplevel L4.toplevel L6.toplevel L7.toplevel.
Require Import compcert.lib.Maps.
Require Import ZArith.
Require Import Common.Common Common.compM Common.Pipeline_utils.
Require Import String List.
Require Import maps_util.
Require Import Glue.glue.
Require Import Glue.ffi.
Require Import ExtLib.Structures.Monad.
Require Import MetaCoq.Template.BasicAst.

Import Monads.
Import MonadNotation.
Import ListNotations.

(** * Constants realized in the target code *) 

(* Each constant that is realized in the backend must have an associated arrity.
 * We find the arity of the extracted constant from its type in [global_env]
 * after reification. Assumes that the type is in some normal form.
 *)

Fixpoint find_arrity (tau : Ast.term) : nat :=
  match tau with
  | tProd na ty body => 1 + find_arrity body
  | _ => 0
  end.

Fixpoint find_global_decl_arrity (gd : Ast.global_decl) : error nat :=
  match gd with
  | Ast.ConstantDecl bd => Ret (find_arrity (Ast.cst_type bd))
  | Ast.InductiveDecl _ => Err ("Expected ConstantDecl but found InductiveDecl")
  end.
    

Fixpoint find_prim_arrity (env : global_env) (pr : kername) : error nat :=
  match env with
  | [] => Err ("Constant " ++ string_of_kername pr ++ " not found in environment")
  | (n, gd) :: env =>    
    if eq_kername pr n then find_global_decl_arrity  gd
    else find_prim_arrity env pr
  end.

Fixpoint find_prim_arrities (env : global_env) (prs : list (kername * string)) : error (list (kername * string * nat * positive)) :=
  match prs with
  | [] => Ret []
  | (pr, s) :: prs =>
    arr <- find_prim_arrity env pr ;;
    prs' <- find_prim_arrities env prs ;;
    Ret ((pr, s, arr, 1%positive) :: prs')
  end.

(* Picks an identifier for each primitive for internal representation *)
Fixpoint pick_prim_ident (id : positive) (prs : list (kername * string * nat * positive))
: (list (kername * string * nat * positive) * positive) :=
  match prs with
  | [] => ([], id)
  | (pr, s, a, _) :: prs =>
    let next_id := (id + 1)%positive in
    let (prs', id') := pick_prim_ident next_id prs in
    ((pr, s, a, id) :: prs', id')
  end.


Definition register_prims (id : positive) (env : global_env) : pipelineM (list (kername * string * nat * positive) * positive) :=
  o <- get_options ;;
  match find_prim_arrities env (prims o) with
  | Ret prs =>
    ret (pick_prim_ident id prs)
  | Err s => failwith s
  end.  
  
(** * CertiCoq's Compilation Pipeline, without code generation *)

Section Pipeline.

  Context (next_id : positive)
          (prims : list (kername * string * nat * positive))
          (debug : bool).
  
  Definition CertiCoq_pipeline (p : global_context * term) :=  
    o <- get_options ;;
    p <- compile_L1g p ;;
    p <- compile_L2k p ;;
    p <- compile_L2k_eta p ;;
    p <- compile_L4 prims p ;;
    p <- (if direct o then compile_L6_ANF next_id prims p else compile_L6_CPS next_id prims p) ;; 
    if debug then compile_L6_debug next_id p  (* For debugging intermediate states of the λanf pipeline *)
    else compile_L6 next_id p.


End Pipeline. 

Let next_id := 10%positive.

(** * The main CertiCoq pipeline, with MetaCoq's erasure and C-code generation *)

Definition pipeline (p : Template.Ast.program) :=
  let genv := fst p in
  '(prs, next_id) <- register_prims next_id genv ;;
  p <- erase_PCUIC p ;; 
  p <- CertiCoq_pipeline next_id prs false p ;;
  compile_Clight p.


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
           (cps : bool)                            (* CPS or direct *)
           (args : nat)                            (* number of C args *)
           (conf : nat)                            (* λ_ANF configuration *)
           (o_level : nat)                         (* optimization level *)
           (time : bool) (time_anf : bool)         (* timing options *)
           (debug : bool)                          (* Debug log *)
           (dev : nat)                             (* Extra flag for development purposes *)
           (prefix : string)                       (* Prefix for the FFI. Check why is this needed in the pipeline and not just the plugin *)
           (prims : list (kername * string)) (* list of extracted constants *)
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

Definition printProg :=
  fun prog file =>
    L6_to_Clight.print_Clight_dest_names (snd prog) (cps.M.elements (fst prog)) file.

Definition compile (opts : Options) (p : Template.Ast.program) :=
  run_pipeline _ _ opts p pipeline.


(** * For compiling to λ_ANF and printing out the code *)

Definition show_IR (opts : Options) (p : Template.Ast.program) : (error string * string) :=
  let genv := fst p in
  let ir_term p :=
      o <- get_options ;;
      '(prims, next_id) <- register_prims next_id genv ;;
      (* The flag -dev 3 *)
      p <- erase_PCUIC p ;; CertiCoq_pipeline next_id prims (dev o =? 3)%nat p
  in 
  let (perr, log) := run_pipeline _ _ opts p ir_term in
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
  | Ret (nenv, _, _, logs) =>
      Err "No Clight program generated"
  | Err s => Err s
  end.

Definition make_ffi (opts : Options) (p : Template.Ast.program)
  : error (cps_util.name_env * Clight.program * Clight.program * list string)  :=
  match generate_ffi opts p with
  | Ret (nenv, Some hdr, Some prg, logs) =>
      Ret (nenv, hdr, prg, logs)
  | Ret (nenv, _, _, logs) =>
      Err "No Clight program generated"
  | Err s => Err s
  end.
