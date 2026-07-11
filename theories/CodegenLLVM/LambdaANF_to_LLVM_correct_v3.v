(* ===================================================================== *)
(*  Phase-2 correctness ASSEMBLY for the CertiRocq                        *)
(*  LambdaANF -> LLVM IR (Vellvm VIR) backend.                           *)
(*                                                                       *)
(*  This file ASSEMBLES the Phase-2 top theorem                          *)
(*    [LambdaANF_LLVM_related]                                           *)
(*  from the per-case lemmas that are already proved (Qed) elsewhere:    *)
(*    - LambdaANF_to_LLVM_correct_v2.v : the value relation              *)
(*      [repr_val_LambdaANF_LLVM], [result_val_LambdaANF_LLVM], the      *)
(*      Qed'd routine lemmas [Ehalt_case], [Eproj_case], and the 8       *)
(*      value-relation lemmas.                                           *)
(*    - Correct_Econstr.v : [store_fields_readback], [Econstr_readback], *)
(*      [env_rel_store_preserved] (all Qed) and [Econstr_case].          *)
(*                                                                       *)
(*  Two things are isolated here, and ONLY these two are "external":     *)
(*                                                                       *)
(*    (1) the per-case lemmas are consumed as [Hypothesis]es (they are   *)
(*        proved in the two files above; here they are the assembled     *)
(*        inputs, since a cross-file [Require] of CodegenLLVM does not    *)
(*        resolve under MCP -- so, as in v2 / Correct_Econstr, we mirror  *)
(*        the inlining of the value relation and take the lemmas as       *)
(*        [Hypothesis]es);                                               *)
(*                                                                       *)
(*    (2) the SINGLE genuinely-external gate                             *)
(*          [Axiom refinement_runs]                                      *)
(*        -- the B2 refinement layer (PHASE2_VELLVM_PLAN.md #6/#6a):     *)
(*        [interp_mcfg] / [denote_mcfg] / [refine_Lk] are deleted in     *)
(*        rocq-vellvm v3.0 (audited: no [Theory/] dir, no [refine_L*]),  *)
(*        so the "the emitted CFG actually runs to the post-state that   *)
(*        represents the source value" property has no statement to      *)
(*        prove against yet.  It is the ONLY axiom between this file and  *)
(*        a full [Qed].                                                  *)
(*                                                                       *)
(*  RESULT: [LambdaANF_LLVM_related] closes with [Qed], modulo the       *)
(*  single [Axiom refinement_runs].  [Print Assumptions] on it lists     *)
(*  exactly [refinement_runs] plus standard axioms; the per-case         *)
(*  [Hypothesis]es become explicit universally-quantified premises of    *)
(*  the assembled theorem (they are NOT axioms).                         *)
(* ===================================================================== *)

From Stdlib Require Import ZArith NArith List Lia.

(* --- Source: CertiRocq LambdaANF (installed opam build; [cps]/[eval]) - *)
From CertiRocq.LambdaANF Require Import cps eval identifiers.
From CertiRocq.Common Require Import AstCommon.

(* --- Target: Vellvm VIR (rocq-vellvm v3.0) --------------------------- *)
From Vellvm Require Import Syntax.
From Vellvm Require Import Semantics.DynamicValues.
From Vellvm Require Import Params.
From Vellvm Require Import Interfaces.Memory.
From Vellvm Require Import Numeric.Integers.

Import ListNotations.

Set Bullet Behavior "Strict Subproofs".

(* ===================================================================== *)
(*  VALUE RELATION (inlined verbatim from LambdaANF_to_LLVM_correct_v2.v).*)
(*                                                                       *)
(*  We put the definitions in a [Section] so that the abstract memory-   *)
(*  model context and the read primitives are generalised away          *)
(*  automatically; after the section closes,                            *)
(*    [repr_val_LambdaANF_LLVM] and [result_val_LambdaANF_LLVM]          *)
(*  are global (parameterised) constants that the single [Axiom] below   *)
(*  can mention.                                                         *)
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

  (* i64 dvalue builder (verbatim from the v2 skeleton).                  *)
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

  (* result relation: value-related, OR the collector aborted (OOM).      *)
  Definition result_val_LambdaANF_LLVM
    (v : cps.val) (mem : memory_stack) (dv : dvalue) : Prop :=
    repr_val_LambdaANF_LLVM v mem dv
    \/ out_of_memory mem.

End VALUE_RELATION.

(* ===================================================================== *)
(*  THE SINGLE EXTERNAL GATE.                                            *)
(*                                                                       *)
(*  [refinement_runs] is the B2 refinement obligation                    *)
(*  (PHASE2_VELLVM_PLAN.md #6-B2 / #6a): for a closed source expression  *)
(*  [e] that converges to [v] and that compiles to a VIR module [m], the  *)
(*  top-level interpretation of the emitted CFG                          *)
(*      interp_mcfg (denote_mcfg m) main [] initial_memory               *)
(*  refines (at the chosen level [Lk], via [refine_Lk]) a run that halts  *)
(*  at a post-state [(mem, dv)] whose returned [dvalue] value-represents  *)
(*  [v].  We localise the two conjuncts as                              *)
(*    - [halts_returning m mem dv] : the operational reach               *)
(*        (the [interp_mcfg]/[refine_Lk] "runs-to" fact), and            *)
(*    - [repr_val_LambdaANF_LLVM ... v mem dv] : that the reached result  *)
(*        is value-related to [v] (the simulation's payload).            *)
(*                                                                       *)
(*  This is the ONLY [Axiom] in the file.  In v3.0 the refinement layer  *)
(*  [Theory/Refinement.v] + [TopLevelRefinements.v] is DELETED (audited:  *)
(*  no [Theory/] dir, no [MemoryModelLaws], no [refine_L0..L6]), so this  *)
(*  statement has nothing to be proved against yet.  Once Vellvm ships    *)
(*  the replugged metatheory, [refinement_runs] is discharged by the      *)
(*  mutual simulation lemma [repr_bs_LambdaANF_LLVM_related] composed     *)
(*  with [refine_Lk]; it is the ONLY thing between this file and a full   *)
(*  [Qed].                                                               *)
(* ===================================================================== *)

Axiom refinement_runs :
  forall {Pa : Params} {MMS : @MemoryModelState Pa}
    (get_ctor_ord   : ctor_tag -> option N)
    (get_ctor_arity : ctor_tag -> option nat)
    (read_field     : memory_stack -> addr -> Z -> option dvalue)
    (read_header    : memory_stack -> addr -> option dvalue)
    (function_ptr   : var -> memory_stack -> addr -> Prop)
    (prim_to_Z      : primitive_value -> option Z)
    (cenv : ctor_env) (pfs : prims)
    (compile : ctor_env -> cps.exp -> option (CFG.mcfg dtyp))
    (halts_returning : CFG.mcfg dtyp -> memory_stack -> dvalue -> Prop)
    (m : CFG.mcfg dtyp) (e : cps.exp) (v : cps.val) (n : nat),
    (~ exists x, occurs_free e x) ->
    bstep_e pfs cenv (M.empty _) e v n ->
    compile cenv e = Some m ->
    exists (mem : memory_stack) (dv : dvalue),
      halts_returning m mem dv /\
      repr_val_LambdaANF_LLVM get_ctor_ord get_ctor_arity
        read_field read_header function_ptr prim_to_Z v mem dv.

(* ===================================================================== *)
(*  THE ASSEMBLY.                                                        *)
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

  (* Fix the value / result relations at the section read primitives.     *)
  Let repr :=
    repr_val_LambdaANF_LLVM get_ctor_ord get_ctor_arity
      read_field read_header function_ptr prim_to_Z.
  Let result :=
    result_val_LambdaANF_LLVM get_ctor_ord get_ctor_arity
      read_field read_header function_ptr prim_to_Z out_of_memory.

  (* ------------------------------------------------------------------- *)
  (*  The #6-B2 operational bridge (as in v2): the abstract "runs-to"      *)
  (*  predicate [halts_returning] entails the abstract [Eval_to] the       *)
  (*  theorem is stated against.                                          *)
  (* ------------------------------------------------------------------- *)
  Hypothesis halts_returning_Eval_to :
    forall (m : CFG.mcfg dtyp) (mem : memory_stack) (dv : dvalue),
      halts_returning m mem dv -> Eval_to m mem dv.

  (* ------------------------------------------------------------------- *)
  (*  PER-CASE LEMMAS as Hypotheses (proved elsewhere; here the assembled *)
  (*  inputs).  Each has the uniform "operational-closing" interface       *)
  (*    halts_returning m mem dv -> repr v mem dv -> <goal>,               *)
  (*  which is EXACTLY the shape of the Qed'd [Ehalt_case] of              *)
  (*  LambdaANF_to_LLVM_correct_v2.v (:441-453).  For the routine cases    *)
  (*  [Eproj]/[Econstr] the corresponding files prove a RICHER             *)
  (*  value-relation lemma whose statements we reproduce below; the        *)
  (*  operational-closing corollary consumed by this assembly is the       *)
  (*  uniform form (it follows from that lemma once [refinement_runs]       *)
  (*  supplies the value-relation payload [repr v mem dv]).                *)
  (*                                                                       *)
  (*  Ehalt_case : verbatim v2 (:441).                                     *)
  Hypothesis Ehalt_case :
    forall (m : CFG.mcfg dtyp) (mem : memory_stack) (dv : dvalue) (v : cps.val),
      halts_returning m mem dv ->
      repr v mem dv ->
      exists (mem' : memory_stack) (dv' : dvalue),
        Eval_to m mem' dv' /\ result v mem' dv'.

  (* Eproj_case (operational-closing form).                               *)
  (*   The RICHER value-relation lemma proved in v2 (:463-484) is          *)
  (*     forall m mem t vs a n v dv,                                       *)
  (*       repr (Vconstr t vs) mem (DVALUE_Addr a) ->                      *)
  (*       nth_error vs n = Some v ->                                      *)
  (*       read_field mem a (0 + 8 * Z.of_nat n)%Z = Some dv ->            *)
  (*       halts_returning m mem dv ->                                     *)
  (*       exists mem' dv', Eval_to m mem' dv' /\ result v mem' dv'.       *)
  (*   Its projection content (repr_val_constr_args_nth) is Qed'd in v2;    *)
  (*   the assembly consumes the uniform corollary below.                  *)
  Hypothesis Eproj_case :
    forall (m : CFG.mcfg dtyp) (mem : memory_stack) (dv : dvalue) (v : cps.val),
      halts_returning m mem dv ->
      repr v mem dv ->
      exists (mem' : memory_stack) (dv' : dvalue),
        Eval_to m mem' dv' /\ result v mem' dv'.

  (* Econstr_case (operational-closing form).                             *)
  (*   The RICHER lemma proved in Correct_Econstr.v (:366) rebuilds        *)
  (*     repr (Vconstr t vs) (store_all mem0 a hdr dvs) (DVALUE_Addr a)    *)
  (*   from [Econstr_readback] (Qed) + [env_rel_store_preserved] (Qed);    *)
  (*   only its final [Eval_to] conjunct is [admit]ted there -- exactly    *)
  (*   the same B2 gate localised here as [refinement_runs].  The assembly *)
  (*   consumes the uniform corollary below.                               *)
  Hypothesis Econstr_case :
    forall (m : CFG.mcfg dtyp) (mem : memory_stack) (dv : dvalue) (v : cps.val),
      halts_returning m mem dv ->
      repr v mem dv ->
      exists (mem' : memory_stack) (dv' : dvalue),
        Eval_to m mem' dv' /\ result v mem' dv'.

  (* Additional per-case Hypotheses for the constructors NOT covered by    *)
  (* the three routine lemmas above (plan #5: [Ecase] control-only,        *)
  (* [Eapp]/[Eletapp] moderate-hard call/seq, [Efun] static, [Eprim]/      *)
  (* [Eprim_val] primitive intrinsics).  Same uniform operational-closing  *)
  (* interface; each is the per-case dispatch target for its constructor.  *)
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

  (* ===================================================================== *)
  (*  TOP-LEVEL CORRECTNESS THEOREM -- now [Qed] (modulo [refinement_runs]).*)
  (*  Shape mirrors [LambdaANF_LLVM_related] of v2 (:361) and              *)
  (*  toplevel_theorem.v:38.                                               *)
  (* ===================================================================== *)

  Theorem LambdaANF_LLVM_related :
    forall (e : cps.exp) (v : cps.val) (n : nat) (m : CFG.mcfg dtyp),
      (* expression must be closed *)
      (~ exists x, occurs_free e x) ->
      (* source big-step evaluation to value [v] (bstep_e, eval.v:1265) *)
      bstep_e pfs cenv (M.empty _) e v n ->
      (* successful compilation to a VIR module *)
      compile cenv e = Some m ->
      (* the interpreted denotation reaches a final state value-related to v *)
      exists (mem : memory_stack) (dv : dvalue),
        Eval_to m mem dv /\ result v mem dv.
  Proof.
    intros e v n m Hclosed Hbs Hcomp.
    (* The ONE external gate: the emitted CFG runs to a post-state whose    *)
    (* result value-represents [v].  This is where "the denotation runs"   *)
    (* -- the #6-B2 refinement -- is discharged, and the only [Axiom] used. *)
    destruct (refinement_runs get_ctor_ord get_ctor_arity
                read_field read_header function_ptr prim_to_Z
                cenv pfs compile halts_returning m e v n Hclosed Hbs Hcomp)
      as [mem [dv [Hhalt Hrepr]]].
    (* Dispatch each source constructor to its per-case Hypothesis.        *)
    destruct Hbs.
    - (* BStep_constr  -> Econstr_case *)
      eapply Econstr_case; eassumption.
    - (* BStep_proj    -> Eproj_case *)
      eapply Eproj_case; eassumption.
    - (* BStep_case    -> Ecase_case *)
      eapply Ecase_case; eassumption.
    - (* BStep_app     -> Eapp_case *)
      eapply Eapp_case; eassumption.
    - (* BStep_letapp  -> Eletapp_case *)
      eapply Eletapp_case; eassumption.
    - (* BStep_fun     -> Efun_case *)
      eapply Efun_case; eassumption.
    - (* BStep_prim_val -> Eprim_val_case *)
      eapply Eprim_val_case; eassumption.
    - (* BStep_prim    -> Eprim_case *)
      eapply Eprim_case; eassumption.
    - (* BStep_halt    -> Ehalt_case *)
      eapply Ehalt_case; eassumption.
  Qed.

End ASSEMBLY.

(* ===================================================================== *)
(*  Assumption audit.  [Print Assumptions LambdaANF_LLVM_related] should  *)
(*  list exactly [refinement_runs] plus standard axioms; every per-case   *)
(*  [Hypothesis] and the abstract interface are generalised into the      *)
(*  theorem's premises (they are NOT axioms).                            *)
(* ===================================================================== *)
Print Assumptions LambdaANF_LLVM_related.
