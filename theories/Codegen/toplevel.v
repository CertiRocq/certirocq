From Stdlib Require Import ZArith.
From CertiCoq Require Import LambdaANF.toplevel Codegen.LambdaANF_to_Clight Codegen.LambdaANF_to_Clight_stack.
Require Import Common.Common Common.compM Common.Pipeline_utils.
Require Import ExtLib.Structures.Monad.

Import MonadNotation.

(* Identifiers *)
Definition argsIdent:positive := 26.
Definition allocIdent:positive := 28.
Definition nallocIdent:positive := 92.
Definition limitIdent:positive := 29.
Definition gcIdent:positive := 80.
Definition mainIdent:positive := 81.
Definition bodyIdent:positive := 90.
Definition threadInfIdent:positive := 31.
Definition tinfIdent:positive := 91.
Definition heapInfIdent:positive := 95.
Definition numArgsIdent:positive := 97.
Definition isptrIdent:positive := 82.
Definition caseIdent:positive := 83.
Definition resultIdent:positive := 93.

Definition stackframeTIdent:positive := 78. (* the stack_frame type *)
Definition frameIdent:positive := 79. (* the stack frame of the current function *)
Definition rootIdent:positive := 84. (* live roots array *)
Definition spIdent:positive := 85. (* stack pointer *)
Definition fpIdent:positive := 86. (* frame pointer *)
(* Fields of stack_frame struct *)
Definition nextFld:positive := 87.
Definition rootFld:positive := 88.
Definition prevFld:positive := 89.


Definition Cprogram := (cps_util.name_env * Clight.program * Clight.program)%type.

Definition add_prim_names (prims : list (kername * string * bool * nat * positive)) (nenv : LambdaBoxLocal_to_LambdaANF.name_env) : LambdaBoxLocal_to_LambdaANF.name_env :=
  List.fold_left (fun map '(k, s, b, ar, p) => cps.M.set p (nNamed s) map) prims nenv.


Definition Clight_trans (bodyName : string) (prims : list (kername * string * bool * nat * positive)) (args : nat) (t : toplevel.LambdaANF_FullTerm) : error Cprogram :=
  let '(_, p_env, cenv, ctag, itag, nenv, fenv, _, prog) := t in
  let p := LambdaANF_to_Clight.compile
             argsIdent allocIdent limitIdent gcIdent mainIdent bodyIdent bodyName threadInfIdent
             tinfIdent heapInfIdent numArgsIdent isptrIdent caseIdent
             args p_env prog cenv nenv in
  match p with
  | exceptionMonad.Ret (nenv, prog, head) =>
    Ret (add_prim_names prims nenv, stripOption mainIdent prog, stripOption mainIdent head)
  | Exc s => Err s
  end.


(* TODO unify with the one above, propagate errors *)
Definition Clight_trans_fast (bodyName : string) (prims : list (kername * string * bool * nat * positive)) (args : nat) (t : toplevel.LambdaANF_FullTerm) : error Cprogram :=
  let '(_, p_env, cenv, ctag, itag, nenv, fenv, _, prog) := t in
  let '(nenv, prog, head) := LambdaANF_to_Clight.compile_fast
                               argsIdent allocIdent limitIdent gcIdent mainIdent bodyIdent bodyName threadInfIdent
                               tinfIdent heapInfIdent numArgsIdent isptrIdent caseIdent
                               args p_env prog cenv nenv in
  Ret (add_prim_names prims nenv, stripOption mainIdent prog, stripOption mainIdent head).


Definition Clight_trans_ANF bodyName (prims : list (kername * string * bool * nat * positive)) (args : nat) (t : toplevel.LambdaANF_FullTerm) : error Cprogram * string :=
  let '(_, pr_env, cenv, ctag, itag, nenv, fenv, _, prog) := t in
  let '(p, str) := LambdaANF_to_Clight_stack.compile
                     argsIdent allocIdent nallocIdent limitIdent gcIdent mainIdent bodyIdent bodyName threadInfIdent
                     tinfIdent heapInfIdent numArgsIdent isptrIdent caseIdent resultIdent
                     args
                     pr_env
                     stackframeTIdent frameIdent rootIdent fpIdent nextFld rootIdent prevFld
                     false (* args optimization *)
                     prog cenv nenv in
  match p with
  | Ret (nenv, prog, head) =>
    (Ret (add_prim_names prims nenv, prog, head), str)
  | Err s => (Err s, str)
  end.


Definition compile_Clight (prims : list (kername * string * bool * nat * positive)) : CertiCoqTrans toplevel.LambdaANF_FullTerm Cprogram :=
  fun s =>
    debug_msg "Translating from LambdaANF to C" ;;
    opts <- get_options ;;
    let args := c_args opts in
    let cps := negb (direct opts) in
    if cps then
      LiftErrorCertiCoqTrans "Codegen" (Clight_trans opts.(body_name) prims args) s
    else
      LiftErrorLogCertiCoqTrans "Codegen" (Clight_trans_ANF opts.(body_name) prims args) s.
