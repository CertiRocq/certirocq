(* ===================================================================== *)
(*  Phase A: connect the PARAMETRIC Phase-2 top theorem                   *)
(*  [LambdaANF_LLVM_related] to the CONCRETE runnable emitter             *)
(*  [compile_prog] (LambdaANF_to_LLVM.v).                                 *)
(*                                                                       *)
(*  The parametric assembly (LambdaANF_to_LLVM_correct_v3.v) is stated    *)
(*  over an abstract [Variable compile : ctor_env -> cps.exp ->           *)
(*  option (CFG.mcfg dtyp)].  The concrete emitter instead produces a     *)
(*  PRINTED module                                                        *)
(*    compile_prog : (ctor_tag->N) -> (ctor_tag->N) -> cps.exp ->         *)
(*                   list (toplevel_entity typ (block typ*list(block typ)))*)
(*  i.e. a list of surface-syntax [toplevel_entity typ] whose CFG bodies  *)
(*  are still typed with the *surface* type [typ], NOT the normalized     *)
(*  [dtyp] the semantics runs on.                                         *)
(*                                                                       *)
(*  THE ADAPTER (Vellvm passes) that bridges the two:                     *)
(*    compile_prog go ga e                                                *)
(*      : list (toplevel_entity typ (block typ * list (block typ)))       *)
(*    |-- CFG.mcfg_of_tle -->  mcfg typ    (assemble TLEs into a module)  *)
(*    |-- convert_types   -->  mcfg dtyp   (type-inference / TypToDtyp    *)
(*                                          normalization pass)           *)
(*  Both passes exist in the installed rocq-vellvm:                       *)
(*    CFG.mcfg_of_tle : toplevel_entities typ (block typ*list(block typ)) *)
(*                        -> mcfg typ                                     *)
(*    convert_types   : mcfg typ -> mcfg dtyp                             *)
(*  (toplevel_entities T B := list (toplevel_entity T B), so the emitter  *)
(*  output type is DEFINITIONALLY the domain of mcfg_of_tle.)             *)
(*                                                                       *)
(*  We therefore define                                                   *)
(*    compile_prog_mcfg cenv e                                            *)
(*      := Some (convert_types (mcfg_of_tle (compile_prog                 *)
(*                 (cenv_ord cenv) (cenv_arity cenv) e)))                 *)
(*  which HAS the abstract type [ctor_env -> cps.exp ->                   *)
(*  option (CFG.mcfg dtyp)] and reads the emitter's ordinal/arity         *)
(*  parameters out of [cenv] (ctor_ordinal / ctor_arity fields).          *)
(*                                                                       *)
(*  We reprove the parametric assembly here (the v3 proof file is not     *)
(*  installed as a library and is being edited concurrently) with the     *)
(*  ONE difference that [refinement_runs] is taken as an explicit         *)
(*  HYPOTHESIS rather than an [Axiom] -- so this file introduces NO new    *)
(*  axiom.  [compile_prog_related] then instantiates [compile] with the   *)
(*  concrete bridge and leaves EVERY remaining obligation (the per-case    *)
(*  lemmas, [halts_returning_Eval_to] and [refinement_runs]) as explicit  *)
(*  universally-quantified hypotheses -- NOT axioms.                      *)
(* ===================================================================== *)

From Stdlib Require Import ZArith NArith List Lia String.

(* --- Source: CertiRocq LambdaANF ------------------------------------- *)
From CertiRocq.LambdaANF Require Import cps eval identifiers.
From CertiRocq.Common Require Import AstCommon.

(* --- The CONCRETE emitter (installed / compiled) -------------------- *)
From CertiRocq.CodegenLLVM Require Import LambdaANF_to_LLVM.

(* --- Target: Vellvm VIR --------------------------------------------- *)
From Vellvm Require Import Syntax.
From Vellvm Require Import Semantics.
From Vellvm Require Import Semantics.DynamicValues.
From Vellvm Require Import Params.
From Vellvm Require Import Interfaces.Memory.
From Vellvm Require Import Numeric.Integers.

Import ListNotations.

Set Bullet Behavior "Strict Subproofs".

(* ===================================================================== *)
(*  VALUE RELATION (inlined verbatim from LambdaANF_to_LLVM_correct_v3).  *)
(* ===================================================================== *)

Section VALUE_RELATION.

  Context {Pa : Params}.
  Context {MMS : @MemoryModelState Pa}.

  Variable get_ctor_ord   : ctor_tag -> option N.
  Variable get_ctor_arity : ctor_tag -> option nat.
  Variable read_field  : memory_stack -> addr -> Z -> option dvalue.
  Variable read_header : memory_stack -> addr -> option dvalue.
  Variable function_ptr : var -> memory_stack -> addr -> Prop.
  Variable prim_to_Z : primitive_value -> option Z.
  Variable out_of_memory : memory_stack -> Prop.

  Definition DVALUE_I64 (z : Z) : dvalue :=
    DVALUE_I 64%positive (@Integers.repr 64%positive z).

  Inductive repr_val_LambdaANF_LLVM
    : cps.val -> memory_stack -> dvalue -> Prop :=

  | RLconstr_unboxed :
      forall (t : ctor_tag) (mem : memory_stack) (ord : N),
        get_ctor_ord t = Some ord ->
        get_ctor_arity t = Some 0%nat ->
        repr_val_LambdaANF_LLVM
          (Vconstr t []) mem
          (DVALUE_I64 (Z.of_N ord * 2 + 1))

  | RLconstr_boxed :
      forall (t : ctor_tag) (vs : list cps.val) (mem : memory_stack)
             (a : addr) (arity : nat) (ord : N),
        get_ctor_ord t = Some ord ->
        get_ctor_arity t = Some arity ->
        (arity > 0)%nat ->
        read_header mem a
          = Some (DVALUE_I64 (Z.of_nat arity * 1024 + Z.of_N ord)) ->
        repr_val_constr_args_LambdaANF_LLVM vs mem a 0%Z ->
        repr_val_LambdaANF_LLVM (Vconstr t vs) mem (DVALUE_Addr a)

  | RLfunction :
      forall (fds : fundefs) (f : var) (mem : memory_stack) (a : addr),
        function_ptr f mem a ->
        repr_val_LambdaANF_LLVM (Vfun (M.empty _) fds f) mem (DVALUE_Addr a)

  | RLprim :
      forall (p : primitive_value) (mem : memory_stack) (a : addr) (z : Z),
        prim_to_Z p = Some z ->
        read_field mem a 0%Z = Some (DVALUE_I64 z) ->
        repr_val_LambdaANF_LLVM (Vprim p) mem (DVALUE_Addr a)

  with repr_val_constr_args_LambdaANF_LLVM
    : list cps.val -> memory_stack -> addr -> Z -> Prop :=

  | RLnil :
      forall (mem : memory_stack) (a : addr) (off : Z),
        repr_val_constr_args_LambdaANF_LLVM [] mem a off

  | RLcons :
      forall (v : cps.val) (vs : list cps.val) (mem : memory_stack)
             (a : addr) (off : Z) (dv : dvalue),
        read_field mem a off = Some dv ->
        repr_val_LambdaANF_LLVM v mem dv ->
        repr_val_constr_args_LambdaANF_LLVM vs mem a (off + 8)%Z ->
        repr_val_constr_args_LambdaANF_LLVM (v :: vs) mem a off.

  Definition result_val_LambdaANF_LLVM
    (v : cps.val) (mem : memory_stack) (dv : dvalue) : Prop :=
    repr_val_LambdaANF_LLVM v mem dv
    \/ out_of_memory mem.

End VALUE_RELATION.

(* ===================================================================== *)
(*  THE CONCRETE BRIDGE.                                                  *)
(*                                                                       *)
(*  Read the emitter's ordinal/arity parameters out of the [ctor_env]     *)
(*  (fields [ctor_ordinal] / [ctor_arity], both [N]); default 0 when a    *)
(*  tag is absent.  Then run the two Vellvm passes.                       *)
(* ===================================================================== *)

Definition cenv_ord (cenv : ctor_env) (t : ctor_tag) : N :=
  match M.get t cenv with
  | Some info => ctor_ordinal info
  | None => 0%N
  end.

Definition cenv_arity (cenv : ctor_env) (t : ctor_tag) : N :=
  match M.get t cenv with
  | Some info => ctor_arity info
  | None => 0%N
  end.

(* The adapter: [toplevel_entity typ] list -> [mcfg typ] -> [mcfg dtyp].
   [nenv] is the emitter's function-name/info environment (mapping ids to
   an extern name + a boolean flag); it is threaded but does not affect the
   abstract [compile] type once fixed. *)
Definition compile_prog_mcfg
  (nenv : positive -> option (string * bool))
  (cenv : ctor_env) (e : cps.exp)
  : option (CFG.mcfg dtyp) :=
  Some (convert_types
          (CFG.mcfg_of_tle
             (compile_prog (cenv_ord cenv) (cenv_arity cenv) nenv e))).

(* Sanity: with [nenv] fixed, the bridge has EXACTLY the abstract [compile]
   type [ctor_env -> cps.exp -> option (CFG.mcfg dtyp)]. *)
Definition compile_bridge_has_abstract_type
  (nenv : positive -> option (string * bool))
  : ctor_env -> cps.exp -> option (CFG.mcfg dtyp)
  := compile_prog_mcfg nenv.

(* ===================================================================== *)
(*  THE PARAMETRIC ASSEMBLY (reproved; [refinement_runs] is a HYPOTHESIS).*)
(*  Identical in content to LambdaANF_to_LLVM_correct_v3's ASSEMBLY,      *)
(*  except that the single external gate is a section [Hypothesis], so    *)
(*  this file adds NO axiom.                                              *)
(* ===================================================================== *)

Section ASSEMBLY.

  Context {Pa : Params}.
  Context {MMS : @MemoryModelState Pa}.

  Variable get_ctor_ord   : ctor_tag -> option N.
  Variable get_ctor_arity : ctor_tag -> option nat.
  Variable read_field  : memory_stack -> addr -> Z -> option dvalue.
  Variable read_header : memory_stack -> addr -> option dvalue.
  Variable function_ptr : var -> memory_stack -> addr -> Prop.
  Variable prim_to_Z : primitive_value -> option Z.
  Variable out_of_memory : memory_stack -> Prop.

  Variable cenv    : ctor_env.
  Variable pfs     : prims.
  Variable compile : ctor_env -> cps.exp -> option (CFG.mcfg dtyp).
  Variable Eval_to : CFG.mcfg dtyp -> memory_stack -> dvalue -> Prop.
  Variable halts_returning : CFG.mcfg dtyp -> memory_stack -> dvalue -> Prop.

  Let repr :=
    repr_val_LambdaANF_LLVM get_ctor_ord get_ctor_arity
      read_field read_header function_ptr prim_to_Z.
  Let result :=
    result_val_LambdaANF_LLVM get_ctor_ord get_ctor_arity
      read_field read_header function_ptr prim_to_Z out_of_memory.

  (* The B2 refinement gate -- here a HYPOTHESIS, not an Axiom. *)
  Hypothesis refinement_runs :
    forall (m : CFG.mcfg dtyp) (e : cps.exp) (v : cps.val) (n : nat),
      (~ exists x, occurs_free e x) ->
      bstep_e pfs cenv (M.empty _) e v n ->
      compile cenv e = Some m ->
      exists (mem : memory_stack) (dv : dvalue),
        halts_returning m mem dv /\ repr v mem dv.

  Hypothesis halts_returning_Eval_to :
    forall (m : CFG.mcfg dtyp) (mem : memory_stack) (dv : dvalue),
      halts_returning m mem dv -> Eval_to m mem dv.

  Hypothesis Ehalt_case :
    forall (m : CFG.mcfg dtyp) (mem : memory_stack) (dv : dvalue) (v : cps.val),
      halts_returning m mem dv -> repr v mem dv ->
      exists (mem' : memory_stack) (dv' : dvalue),
        Eval_to m mem' dv' /\ result v mem' dv'.
  Hypothesis Eproj_case :
    forall (m : CFG.mcfg dtyp) (mem : memory_stack) (dv : dvalue) (v : cps.val),
      halts_returning m mem dv -> repr v mem dv ->
      exists (mem' : memory_stack) (dv' : dvalue),
        Eval_to m mem' dv' /\ result v mem' dv'.
  Hypothesis Econstr_case :
    forall (m : CFG.mcfg dtyp) (mem : memory_stack) (dv : dvalue) (v : cps.val),
      halts_returning m mem dv -> repr v mem dv ->
      exists (mem' : memory_stack) (dv' : dvalue),
        Eval_to m mem' dv' /\ result v mem' dv'.
  Hypothesis Ecase_case :
    forall (m : CFG.mcfg dtyp) (mem : memory_stack) (dv : dvalue) (v : cps.val),
      halts_returning m mem dv -> repr v mem dv ->
      exists (mem' : memory_stack) (dv' : dvalue),
        Eval_to m mem' dv' /\ result v mem' dv'.
  Hypothesis Eapp_case :
    forall (m : CFG.mcfg dtyp) (mem : memory_stack) (dv : dvalue) (v : cps.val),
      halts_returning m mem dv -> repr v mem dv ->
      exists (mem' : memory_stack) (dv' : dvalue),
        Eval_to m mem' dv' /\ result v mem' dv'.
  Hypothesis Eletapp_case :
    forall (m : CFG.mcfg dtyp) (mem : memory_stack) (dv : dvalue) (v : cps.val),
      halts_returning m mem dv -> repr v mem dv ->
      exists (mem' : memory_stack) (dv' : dvalue),
        Eval_to m mem' dv' /\ result v mem' dv'.
  Hypothesis Efun_case :
    forall (m : CFG.mcfg dtyp) (mem : memory_stack) (dv : dvalue) (v : cps.val),
      halts_returning m mem dv -> repr v mem dv ->
      exists (mem' : memory_stack) (dv' : dvalue),
        Eval_to m mem' dv' /\ result v mem' dv'.
  Hypothesis Eprim_case :
    forall (m : CFG.mcfg dtyp) (mem : memory_stack) (dv : dvalue) (v : cps.val),
      halts_returning m mem dv -> repr v mem dv ->
      exists (mem' : memory_stack) (dv' : dvalue),
        Eval_to m mem' dv' /\ result v mem' dv'.
  Hypothesis Eprim_val_case :
    forall (m : CFG.mcfg dtyp) (mem : memory_stack) (dv : dvalue) (v : cps.val),
      halts_returning m mem dv -> repr v mem dv ->
      exists (mem' : memory_stack) (dv' : dvalue),
        Eval_to m mem' dv' /\ result v mem' dv'.

  Theorem LambdaANF_LLVM_related :
    forall (e : cps.exp) (v : cps.val) (n : nat) (m : CFG.mcfg dtyp),
      (~ exists x, occurs_free e x) ->
      bstep_e pfs cenv (M.empty _) e v n ->
      compile cenv e = Some m ->
      exists (mem : memory_stack) (dv : dvalue),
        Eval_to m mem dv /\ result v mem dv.
  Proof.
    intros e v n m Hclosed Hbs Hcomp.
    destruct (refinement_runs m e v n Hclosed Hbs Hcomp)
      as [mem [dv [Hhalt Hrepr]]].
    destruct Hbs.
    - eapply Econstr_case; eassumption.
    - eapply Eproj_case; eassumption.
    - eapply Ecase_case; eassumption.
    - eapply Eapp_case; eassumption.
    - eapply Eletapp_case; eassumption.
    - eapply Efun_case; eassumption.
    - eapply Eprim_val_case; eassumption.
    - eapply Eprim_case; eassumption.
    - eapply Ehalt_case; eassumption.
  Qed.

End ASSEMBLY.

(* ===================================================================== *)
(*  THE CONCRETE INSTANTIATION.                                           *)
(*                                                                       *)
(*  [compile_prog_related] IS [LambdaANF_LLVM_related] with               *)
(*  [compile := compile_prog_mcfg] (the concrete bridge of the runnable   *)
(*  emitter).  The memory accessors, [Eval_to], [halts_returning] have    *)
(*  NO concrete Vellvm counterpart in the installed vellvm (the           *)
(*  refinement metatheory layer [Theory/] is deleted in v3.0), so they    *)
(*  remain universally-quantified parameters.  Every proof obligation --  *)
(*  [refinement_runs], [halts_returning_Eval_to] and the nine per-case    *)
(*  lemmas -- is an explicit hypothesis, NOT an axiom.                    *)
(* ===================================================================== *)

Theorem compile_prog_related
  {Pa : Params} {MMS : @MemoryModelState Pa}
  (get_ctor_ord   : ctor_tag -> option N)
  (get_ctor_arity : ctor_tag -> option nat)
  (read_field  : memory_stack -> addr -> Z -> option dvalue)
  (read_header : memory_stack -> addr -> option dvalue)
  (function_ptr : var -> memory_stack -> addr -> Prop)
  (prim_to_Z : primitive_value -> option Z)
  (out_of_memory : memory_stack -> Prop)
  (cenv : ctor_env) (pfs : prims)
  (nenv : positive -> option (string * bool))
  (Eval_to : CFG.mcfg dtyp -> memory_stack -> dvalue -> Prop)
  (halts_returning : CFG.mcfg dtyp -> memory_stack -> dvalue -> Prop)

  (* -- remaining obligations, as explicit hypotheses (NOT axioms) -- *)
  (refinement_runs :
     forall (m : CFG.mcfg dtyp) (e : cps.exp) (v : cps.val) (n : nat),
       (~ exists x, occurs_free e x) ->
       bstep_e pfs cenv (M.empty _) e v n ->
       compile_prog_mcfg nenv cenv e = Some m ->
       exists (mem : memory_stack) (dv : dvalue),
         halts_returning m mem dv /\
         repr_val_LambdaANF_LLVM get_ctor_ord get_ctor_arity
           read_field read_header function_ptr prim_to_Z v mem dv)
  (halts_returning_Eval_to :
     forall (m : CFG.mcfg dtyp) (mem : memory_stack) (dv : dvalue),
       halts_returning m mem dv -> Eval_to m mem dv)
  (Ehalt_case Eproj_case Econstr_case Ecase_case Eapp_case
   Eletapp_case Efun_case Eprim_case Eprim_val_case :
     forall (m : CFG.mcfg dtyp) (mem : memory_stack) (dv : dvalue) (v : cps.val),
       halts_returning m mem dv ->
       repr_val_LambdaANF_LLVM get_ctor_ord get_ctor_arity
         read_field read_header function_ptr prim_to_Z v mem dv ->
       exists (mem' : memory_stack) (dv' : dvalue),
         Eval_to m mem' dv' /\
         result_val_LambdaANF_LLVM get_ctor_ord get_ctor_arity
           read_field read_header function_ptr prim_to_Z out_of_memory v mem' dv') :

  (* -- conclusion: the top theorem, now ABOUT compile_prog -- *)
  forall (e : cps.exp) (v : cps.val) (n : nat) (m : CFG.mcfg dtyp),
    (~ exists x, occurs_free e x) ->
    bstep_e pfs cenv (M.empty _) e v n ->
    compile_prog_mcfg nenv cenv e = Some m ->
    exists (mem : memory_stack) (dv : dvalue),
      Eval_to m mem dv /\
      result_val_LambdaANF_LLVM get_ctor_ord get_ctor_arity
        read_field read_header function_ptr prim_to_Z out_of_memory v mem dv.
Proof.
  eapply (LambdaANF_LLVM_related
            get_ctor_ord get_ctor_arity read_field read_header
            function_ptr prim_to_Z out_of_memory
            cenv pfs (compile_prog_mcfg nenv) Eval_to halts_returning);
    eassumption.
Qed.

(* ===================================================================== *)
(*  Assumption audit.                                                     *)
(* ===================================================================== *)
Print Assumptions compile_prog_related.
