(* Top-level theorems for the C code generator *)

From Stdlib Require Import ZArith.ZArith Lists.List Sets.Ensembles micromega.Lia.
From compcert Require Import lib.Coqlib lib.Maps lib.Integers common.AST common.Values
     common.Memory common.Events common.Globalenvs common.Smallstep
     cfrontend.Ctypes cfrontend.Clight Clightdefs.
From CertiRocq.Common Require Import compM Pipeline_utils.
From CertiRocq.LambdaANF Require Import term term_util identifiers Ensembles_util algebra eval.
From CertiRocq.Codegen Require Import LambdaANF_to_C LambdaANF_to_C_rel LambdaANF_to_C_memory
     LambdaANF_to_C_correct.

Import ListNotations.
Local Open Scope Z_scope.

Section Refinement.

  Context {fuel : Type} {Hf : @fuel_resource fuel} {trace : Type} {Ht : @trace_resource trace}.

  Context (cenv : ctor_env).

  (* The C program *)
  Context (p : Clight.program).

  Local Notation ge := (globalenv p).

  (* Its collector, with the invariant [gc_inv], and its pointer test meet their
     specifications *)
  Context (gc_inv : heap -> mem -> block -> Z -> Prop)
          (Hgc : collector_ok cenv ge gc_inv)
          (Hptr : is_ptr_spec ge).

  (* The thread info at [tb, tofs] is set up in the memory [m] *)
  Context (tb : block) (tofs : Z) (h : heap) (fs : list frame) (m : mem)
          (Htinfo : tinfo_ok cenv ge gc_inv h fs m tb tofs).

  (* Value refinement: [w] is the layout of [v] in the memory [m']. Functions are not
     compared. *)
  Definition value_ref_C (v : val) (m' : mem) (w : Values.val) : Prop :=
    exists h', repr_val cenv ge (fun _ _ => True) h' m' v w.

  (* The function [body], called with the thread info from the memory [m], returns [w] and
     the memory [m']. [k] is what its caller does next. *)
  Definition call_evaluates (w : Values.val) (m' : mem) : Prop :=
    exists b fd,
      Genv.find_symbol ge bodyId = Some b /\
      Genv.find_funct_ptr ge b = Some fd /\
      forall k, is_call_cont k ->
                star step2 ge (Callstate fd [Vptr tb (Ptrofs.repr tofs)] k m) E0
                     (Returnstate w k m').

  (* The same call makes [n] steps, for every [n] *)
  Definition call_diverges : Prop :=
    exists b fd,
      Genv.find_symbol ge bodyId = Some b /\
      Genv.find_funct_ptr ge b = Some fd /\
      forall n k, is_call_cont k ->
                  exists s, starN step2 ge n (Callstate fd [Vptr tb (Ptrofs.repr tofs)] k m) E0 s.

  (* The C program refines the behavior of [e] *)
  Definition refines_C (e : exp) : Prop :=
    forall (v : val) (c : fuel) (t : trace),
      bstep_fuel cenv (M.empty val) e c (Res v) t ->
      exists (w : Values.val) (m' : mem),
        call_evaluates w m' /\
        value_ref_C v m' w.

  Theorem compile_top_correct body_name nparam prims e nenv names header prog :
    closed_exp e ->
    unique_bindings e ->
    (forall x, x \in bound_var e -> (100 <= x)%positive) ->
    no_prims e ->
    compile body_name nparam prims e cenv nenv = Ret (names, header, prog) ->
    make_program composites (prog_defs prog) = Ret p ->
    refines_C e.
  Proof.
    intros Hcl Hub Hid Hnp Hcomp Hmk.
    destruct (compile_correct (fuel := fuel) (trace := trace)
                              _ _ _ _ _ _ _ _ _ _ gc_inv Hcomp Hmk Hid Hub Hcl Hnp Hgc Hptr)
      as (b & body & Hb & Hbody & _ & Hcorrect).
    intros v c t Hstep.
    destruct (Hcorrect (Res v) c t Hstep 0%nat tb tofs h fs m Htinfo)
      as (w & h' & m' & Hsteps & Hres & _).
    exists w, m'. split.
    - exists b, (Internal body). split; [exact Hb |]. split; [exact Hbody |].
      intros k Hk. destruct (Hsteps k Hk) as (j & _ & Hs). eapply starN_star. exact Hs.
    - exists h'. eapply repr_val_mono; [| apply heap_le_refl | exact Hres]. auto.
  Qed.

  (* The first [n] steps of a longer run *)
  Lemma starN_prefix n j s s' :
    starN step2 ge (n + j) s E0 s' -> exists s1, starN step2 ge n s E0 s1.
  Proof.
    revert s. induction n as [| n IH]; intros s H.
    - exists s. constructor.
    - simpl in H. inversion H as [| ? ? ? t1 s2 t2 ? Hstep Hrest Heq]; subst.
      destruct (Eapp_E0_inv _ _ (eq_sym Heq)) as [-> ->].
      destruct (IH _ Hrest) as [s1 Hs1]. exists s1.
      eapply starN_step; [exact Hstep | exact Hs1 | reflexivity].
  Qed.

  Theorem compile_top_divergence_correct body_name nparam prims e nenv names header prog :
    closed_exp e ->
    unique_bindings e ->
    (forall x, x \in bound_var e -> (100 <= x)%positive) ->
    no_prims e ->
    compile body_name nparam prims e cenv nenv = Ret (names, header, prog) ->
    make_program composites (prog_defs prog) = Ret p ->
    diverge cenv (M.empty val) e ->
    call_diverges.
  Proof.
    intros Hcl Hub Hid Hnp Hcomp Hmk Hdiv.
    destruct (compile_correct (fuel := fuel) (trace := trace)
                              _ _ _ _ _ _ _ _ _ _ gc_inv Hcomp Hmk Hid Hub Hcl Hnp Hgc Hptr)
      as (b & body & Hb & Hbody & _ & Hcorrect).
    exists b, (Internal body). split; [exact Hb |]. split; [exact Hbody |].
    intros n k Hk. destruct (fuel_for_steps e n) as [c Hc]. destruct (Hdiv c) as [t Hstep].
    destruct (Hcorrect OOT c t Hstep 0%nat tb tofs h fs m Htinfo k Hk) as (s & j & Hj & Hs).
    apply (starN_prefix n (j - n) _ s). replace (n + (j - n))%nat with j by lia. exact Hs.
  Qed.

End Refinement.
