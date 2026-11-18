(** * Algebra of Vellvm's [interp_mcfg], used to symbolically execute emitted code. *)

From Stdlib Require Import Program Morphisms.
From ITree Require Import ITree Eq.Eqit Events.State Events.StateFacts.
From ExtLib Require Import Structures.Monads.

From Vellvm Require Import
  Utils Syntax Params
  Interfaces.Memory Implementations.Memory
  Semantics.DynamicValues Semantics.LLVMEvents
  Semantics.InterpretationStack Handlers.
From CertiRocq.CodegenLLVM Require Import LambdaANF_to_LLVM_statement.

Import MonadNotation.
Open Scope monad_scope.

Section InterpLemmas.




  Lemma interp_mcfg_ret {R} (r : R) s :
    interp_mcfg (Ret r) s ≈ Ret (s, r).
  Proof.
    unfold interp_mcfg.
    rewrite interp_intrinsics_ret.
    rewrite interp_state_ret.
    reflexivity.
  Qed.

  Lemma interp_mcfg_bind {R S} (t : MCFGtop R) (k : R -> MCFGtop S) s :
    interp_mcfg (ITree.bind t k) s ≈
      ITree.bind (interp_mcfg t s) (fun '(s', r) => interp_mcfg (k r) s').
  Proof.
    unfold interp_mcfg.
    rewrite interp_intrinsics_bind.
    rewrite interp_state_bind.
    apply eutt_eq_bind; intros [s' r]; reflexivity.
  Qed.

  Lemma interp_mcfg_tau {R} (t : MCFGtop R) s :
    interp_mcfg (Tau t) s ≈ interp_mcfg t s.
  Proof.
    unfold interp_mcfg.
    rewrite interp_intrinsics_Tau.
    rewrite interp_state_tau.
    rewrite tau_eutt.
    reflexivity.
  Qed.

  #[global] Instance interp_mcfg_proper {R} :
    Proper (eutt eq ==> eq ==> eutt eq)%signature (@interp_mcfg _ R).
  Proof.
    intros t t' Ht s s' <-.
    unfold interp_mcfg.
    rewrite Ht.
    reflexivity.
  Qed.


  (** A deterministic memory computation is interpreted as its result. *)
  Lemma memM_interp_runs {E} `{FailureE -< E} `{UBE -< E} `{OOME -< E}
        {X} st (m : memM X) st' x :
    memS_runs st m st' x ->
    @memM_interp _ E _ _ _ X m st ≈ Ret (st', x).
  Proof.
    induction 1; cbn; [reflexivity | assumption | assumption].
  Qed.

  Lemma interp_mcfg_memory {X} (e : MemoryE X) st rest st' x :
    memS_runs st (handle_memoryM e) st' x ->
    interp_mcfg (ITree.trigger (subevent _ e)) (st, rest) ≈ Ret ((st', rest), x).
  Proof.
    intros Hrun.
    unfold interp_mcfg.
    rewrite interp_intrinsics_trigger.
    cbn. unfold F_trigger.
    rewrite interp_state_trigger.
    cbn.
    unfold on_mem, handle_memory.
    rewrite (memM_interp_runs Hrun).
    cbn; rewrite Eqit.bind_ret_l.
    reflexivity.
  Qed.

  (** Local variables live in the top stack frame. *)
  Lemma interp_mcfg_lwrite id v st sf stk g :
    interp_mcfg (ITree.trigger (subevent _ (LocalWrite id v))) (st, ((sf, stk), g))
    ≈ Ret ((st, ((upd_local_sf sf (Maps.add id v (stack_vars sf)), stk), g)), tt).
  Proof.
    unfold interp_mcfg.
    rewrite interp_intrinsics_trigger.
    cbn. unfold F_trigger.
    rewrite interp_state_trigger.
    cbn. unfold on_ls, handle_local_stack, handle_local_debug.
    cbn. repeat (rewrite Eqit.bind_ret_l; cbn).
    reflexivity.
  Qed.

  Lemma interp_mcfg_lread id v st sf stk g :
    RM.find id (stack_vars sf) = Some v ->
    interp_mcfg (ITree.trigger (subevent _ (LocalRead id))) (st, ((sf, stk), g))
    ≈ Ret ((st, ((upd_local_sf sf (stack_vars sf), stk), g)), v).
  Proof.
    intros Hl.
    unfold interp_mcfg.
    rewrite interp_intrinsics_trigger.
    cbn. unfold F_trigger.
    rewrite interp_state_trigger.
    cbn. unfold on_ls, handle_local_stack, handle_local_debug.
    cbn. rewrite Hl.
    repeat (rewrite Eqit.bind_ret_l; cbn).
    reflexivity.
  Qed.

  Lemma interp_mcfg_gread id v st ls g :
    RM.find id g = Some v ->
    interp_mcfg (ITree.trigger (subevent _ (GlobalRead id))) (st, (ls, g))
    ≈ Ret ((st, (ls, g)), v).
  Proof.
    intros Hl.
    unfold interp_mcfg.
    rewrite interp_intrinsics_trigger.
    cbn. unfold F_trigger.
    rewrite interp_state_trigger.
    cbn. unfold on_genv, handle_global_debug.
    cbn. rewrite Hl.
    repeat (rewrite Eqit.bind_ret_l; cbn).
    reflexivity.
  Qed.

  Lemma interp_mcfg_lift_ret {X} (x : X) s :
    interp_mcfg (EOU_to_itree (EOU.raise_ret x)) s ≈ Ret (s, x).
  Proof.
    cbn. apply interp_mcfg_ret.
  Qed.

  Lemma upd_local_sf_id sf : upd_local_sf sf (stack_vars sf) = sf.
  Proof. destruct sf; reflexivity. Qed.

End InterpLemmas.
