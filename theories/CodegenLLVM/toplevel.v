(** * CodegenLLVM.toplevel — pipeline registration for the LambdaANF -> LLVM backend.
    The LLVM analogue of [CodegenWasm/toplevel.v] and [Codegen/toplevel.v]: unpack
    the [LambdaANF_FullTerm], run the emitter [compile_prog], and lift the
    (always-successful) result into a [CertiRocqTrans]. *)

From Vellvm Require Import Syntax.LLVMAst.

From Stdlib Require Import ZArith List.
Require Import Common.Common Common.compM Common.Pipeline_utils.
Require Import LambdaANF.cps_show LambdaANF.toplevel.
Require Import LambdaANF.cps.
Require Import CodegenLLVM.LambdaANF_to_LLVM.   (* compile_prog *)
Require Import CodegenLLVM.Flatten.              (* flatten_prog *)
Require Export CodegenLLVM.Serialize.            (* serialize_program *)

From MetaRocq.Utils Require Import bytestring.  (* String.to_string for prim names *)
Require Import ExtLib.Structures.Monad.
Import MonadNotation.

Notation LLVMmodule := (list (toplevel_entity typ (block typ * list (block typ)))) (only parsing).

(** ctor-env projections: recover a constructor's ordinal / arity from [cenv]. *)
Definition ord_of   (cenv : ctor_env) (t : ctor_tag) : N :=
  match M.get t cenv with Some info => ctor_ordinal info | None => 0%N end.
Definition arity_of (cenv : ctor_env) (t : ctor_tag) : N :=
  match M.get t cenv with Some info => ctor_arity info | None => 0%N end.

(** Resolve a primitive id to its runtime target name (as a Coq string, for
    Vellvm's [Name]) and whether it allocates.  The [prims] table maps each
    [primitive] record to its [positive] id; [prim_target] is a bytestring
    converted with [String.to_string]. *)
Definition prim_of (prims : list (primitive * positive)) (p : positive) :=
  match List.find (fun pr => Pos.eqb (snd pr) p) prims with
  | Some (pr, _) => Some (bytestring.String.to_string pr.(prim_target), pr.(prim_alloc))
  | None => None
  end.

Definition LambdaANF_to_LLVM_Wrapper
    (prims : list (primitive * positive)) (args : nat)
    (t : toplevel.LambdaANF_FullTerm) : error LLVMmodule * string :=
  let '(_, _, cenv, _, _, _, _, _, prog) := t in
  (Ret (flatten_prog (compile_prog (ord_of cenv) (arity_of cenv) (prim_of prims) prog)), "").

Definition compile_LambdaANF_to_LLVM (prims : list (primitive * positive))
  : CertiRocqTrans toplevel.LambdaANF_FullTerm LLVMmodule :=
  fun s =>
    debug_msg "Translating from LambdaANF to LLVM" ;;
    opts <- get_options ;;
    let args := c_args opts in
    LiftErrorLogCertiRocqTrans "CodegenLLVM" (LambdaANF_to_LLVM_Wrapper prims args) s.
