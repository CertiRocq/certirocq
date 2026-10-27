(** * The main simulation lemma [sim_exp] and the top-level theorem.

    [sim_exp] (bstep_e evaluation implies [LLVM_sim.sim_stmt]) is proved by
    induction on [bstep_e], each case being one of the case lemmas:
    - [LLVM_sim_cases_read.v]: [Ehalt], [Eproj], [Eprim_val], [Ecase];
    - [LLVM_sim_cases_constr.v]: [Econstr] (allocation, garbage collection);
    - [LLVM_sim_cases_call.v]: [Efun] (vacuous), [Eapp], [Eletapp].
    The [Eprim] case is vacuous: [body_ok] excludes [Eprim].

    The Section re-declares the context of [LLVM_sim.Simulation] (same names
    and order), so that the closed [sim_exp] is exactly
    [LLVM_toplevel_link.sim_exp_statement].  The top-level theorem
    [LambdaANF_to_LLVM_correct : LambdaANF_to_LLVM_correct_statement] is then
    [LLVM_toplevel_link.main_correct_of_sim] applied to it. *)

From Stdlib Require Import ZArith NArith List Lia String Program Morphisms.
From ITree Require Import ITree Eq.Eqit.
From ExtLib Require Import Structures.Monads.

From CertiRocq.LambdaANF Require Import term term_util eval identifiers.
From CertiRocq.CodegenLLVM Require Import LambdaANF_to_LLVM Flatten
     LambdaANF_to_LLVM_statement LLVM_exp_lemmas LLVM_mem_lemmas LLVM_sim.
From CertiRocq.CodegenLLVM Require LLVM_toplevel_link
     LLVM_sim_cases_read LLVM_sim_cases_constr LLVM_sim_cases_call.

From Vellvm Require Import
  Utils Syntax Params
  Interfaces.Memory Implementations.Memory
  Semantics.DynamicValues Semantics.LLVMEvents Semantics.Denotation
  Semantics.InterpretationStack Semantics.TopLevel Handlers.
From Vellvm Require Import Utils.IntMaps.

Import ListNotations.
Import MonadNotation.
Open Scope monad_scope.
Open Scope Z_scope.

Unset Implicit Arguments.
Set Bullet Behavior "Strict Subproofs".

Section SimExp.

  Variable cenv : ctor_env.
  Variable pfs : prims.
  Variable prim_of : positive -> option (string * bool).
  Variable fds : fundefs.
  Variable heap_inv : state -> ptr -> Prop.
  Variable gc : list dvalue -> MCFGtop (exc + dvalue).
  Variable G : global_env.
  Variable ctx : CallE ~> itree (CallE +' MCFGEtop).
  Variable tinfo : ptr.

  Hypothesis Hmut : forall st st2 alloc alloc2 limit,
       heap_inv st tinfo -> tinfo_ok st tinfo ->
       heap_agree_except st st2 (mutator_writes st tinfo) ->
       field st tinfo off_alloc alloc -> field st tinfo off_limit limit ->
       field st2 tinfo off_alloc alloc2 ->
       (ptr_to_int alloc <= ptr_to_int alloc2 <= ptr_to_int limit)%Z ->
       (ptr_to_int alloc2 mod 8 = 0)%Z ->
       heap_inv st2 tinfo.
  Hypothesis Hgc : forall (st : state) ls fp rs vs nalloc,
       heap_inv st tinfo -> tinfo_ok st tinfo -> mem_ok st -> nursery_tinfo_disjoint st tinfo ->
       field st tinfo off_fp fp ->
       shadow_stack st fp rs ->
       roots_ok cenv fds G st tinfo rs vs ->
       0 <= nalloc < 2 ^ 61 ->
       (exists a, ptr_off tinfo off_nalloc a /\ reads_word st a nalloc) ->
       ends_in_oom (interp_mcfg (gc [Ptr tinfo]) (st, (ls, G)))
       \/ exists st',
           returns (interp_mcfg (gc [Ptr tinfo]) (st, (ls, G)))
                   ((st', (ls, G)), inr (DVALUE_Base DVALUE_None)) /\
           frames_of st' = frames_of st /\
           heap_inv st' tinfo /\ tinfo_ok st' tinfo /\ mem_ok st' /\ nursery_tinfo_disjoint st' tinfo /\
           field st' tinfo off_fp fp /\
           shadow_stack st' fp rs /\
           roots_ok cenv fds G st' tinfo rs vs /\
           room st' tinfo nalloc /\
           (forall a, ~ in_heap st a -> ~ slot_bytes rs a ->
                      IntMaps.lookup a (mem_of st') = IntMaps.lookup a (mem_of st)) /\
           (forall a, in_heap st' a -> in_heap st a \/ IntMaps.lookup a (mem_of st) = None) /\
           (forall a, slot_bytes rs a -> aid_at st' a = aid_at st a).
  Hypothesis Htinfo_range : ptr_to_int tinfo + 8232 < 2^64.
  Hypothesis ctx_fun : forall f ft xs e fp,
    fun_in_fundefs fds (f, ft, xs, e) ->
    RM.find (Anon (Zpos f)) G = Some (Ptr fp) ->
    forall dt p args, ptr_to_int p = ptr_to_int fp ->
      ctx _ (Call dt (Ptr p) args) ≈ denote_function (fun_def cenv prim_of fds f xs e) args.
  Hypothesis ctx_gc : forall gp,
    RM.find (Name "garbage_collect") G = Some (Ptr gp) ->
    forall dt p args, ptr_to_int p = ptr_to_int gp ->
      ctx _ (Call dt (Ptr p) args) ≈ lift_top (gc args).
  Hypothesis G_funs : forall f, In f (fun_ids fds) -> exists fp, RM.find (Anon (Zpos f)) G = Some (Ptr fp).
  Hypothesis G_gc : exists gp, RM.find (Name "garbage_collect") G = Some (Ptr gp).
  Variable main : term.exp.
  Hypothesis Hprog : llvm_restricted cenv fds main.

  Theorem sim_exp : forall rho e v n,
    bstep_e pfs cenv rho e v n -> sim_stmt cenv prim_of fds heap_inv G ctx tinfo main rho e v.
  Proof using All.
    induction 1.
    - (* Econstr *) subst.
      eapply LLVM_sim_cases_constr.sim_case_constr; eassumption.
    - (* Eproj *) eapply LLVM_sim_cases_read.sim_case_proj; eassumption.
    - (* Ecase *) eapply LLVM_sim_cases_read.sim_case_case; eassumption.
    - (* Eapp *) eapply LLVM_sim_cases_call.sim_case_app; eassumption.
    - (* Eletapp *) eapply LLVM_sim_cases_call.sim_case_letapp; eassumption.
    - (* Efun *) eapply LLVM_sim_cases_call.sim_case_fun; eassumption.
    - (* Eprim_val *) subst.
      eapply LLVM_sim_cases_read.sim_case_prim_val; eassumption.
    - (* Eprim: vacuous, [body_ok] excludes it *)
      intros ? ? ? ? ? ? ? ? ? ? ? ? ? ? Hok. inversion Hok.
    - (* Ehalt *) eapply LLVM_sim_cases_read.sim_case_halt; eassumption.
  Qed.

End SimExp.

Definition sim_exp_proof : LLVM_toplevel_link.sim_exp_statement := sim_exp.

(** The correctness of the LambdaANF -> LLVM backend. *)
Theorem LambdaANF_to_LLVM_correct : LambdaANF_to_LLVM_correct_statement.
Proof. exact (LLVM_toplevel_link.main_correct_of_sim sim_exp_proof). Qed.

(** [Print Assumptions LambdaANF_to_LLVM_correct] (Rocq 9.1) prints only
    standard-library axioms and primitive types:
<<
Axioms:
PrimString.string : Set
ClassicalDedekindReals.sig_not_dec : forall P : Prop, {~ ~ P} + {~ P}
ClassicalDedekindReals.sig_forall_dec :
  forall P : nat -> Prop,
  (forall n : nat, {P n} + {~ P n}) ->
  {n : nat | ~ P n} + {forall n : nat, P n}
proof_irrelevance : forall (P : Prop) (p1 p2 : P), p1 = p2
PrimInt63.lsr : PrimInt63.int -> PrimInt63.int -> PrimInt63.int
PrimInt63.land : PrimInt63.int -> PrimInt63.int -> PrimInt63.int
PrimInt63.int : Set
functional_extensionality_dep :
  forall (A : Type) (B : A -> Type) (f g : forall x : A, B x),
  (forall x : A, f x = g x) -> f = g
PrimFloat.float : Set
PrimInt63.eqb : PrimInt63.int -> PrimInt63.int -> bool
Eqdep.Eq_rect_eq.eq_rect_eq :
  forall (U : Type) (p : U) (Q : U -> Type) (x : Q p) (h : p = p),
  x = eq_rect p Q x p h
Classical_Prop.classic : forall P : Prop, P \/ ~ P
>>
*)
