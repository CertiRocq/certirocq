(** * Reasoning about Vellvm's call knot ([mrec] in [denote_mcfg]). *)

From Stdlib Require Import Program Morphisms.
From ITree Require Import ITree Eq.Eqit Interp.InterpFacts Interp.RecursionFacts
     Events.State Events.StateFacts.
From ExtLib Require Import Structures.Monads.

From Vellvm Require Import
  Utils Syntax Params
  Interfaces.Memory Implementations.Memory
  Semantics.DynamicValues Semantics.LLVMEvents Semantics.Denotation
  Semantics.InterpretationStack Handlers.
From CertiRocq.CodegenLLVM Require Import LambdaANF_to_LLVM_statement LLVM_interp_lemmas.

Import MonadNotation.
Open Scope monad_scope.

Section CallLemmas.

  Variable ctx : CallE ~> itree (CallE +' MCFGEtop).

  (** A runtime library function has no internal calls: the call knot leaves
      it unchanged. *)
  Lemma interp_mrec_lift_top {R} (t : MCFGtop R) :
    interp_mrec ctx (lift_top t) ≈ t.
  Proof.
    unfold lift_top.
    rewrite interp_mrec_as_interp.
    rewrite interp_translate.
    cbn.
    setoid_rewrite <- (interp_id_h t) at 2.
    apply eutt_interp; [| reflexivity].
    intros T e. cbn. unfold id_. reflexivity.
  Qed.

  Lemma interp_mrec_ret {R} (r : R) :
    interp_mrec ctx (Ret r : itree (CallE +' MCFGEtop) R) ≈ Ret r.
  Proof.
    rewrite unfold_interp_mrec. cbn. reflexivity.
  Qed.

  Lemma interp_mrec_bind' {U T} (t : itree (CallE +' MCFGEtop) U) (k : U -> itree _ T) :
    interp_mrec ctx (ITree.bind t k) ≈ ITree.bind (interp_mrec ctx t) (fun x => interp_mrec ctx (k x)).
  Proof.
    rewrite interp_mrec_bind. reflexivity.
  Qed.

  (** An internal call unfolds to the callee's body, under the knot. *)
  Lemma interp_mrec_call T (c : CallE T) :
    interp_mrec ctx (ITree.trigger (inl1 c)) ≈ interp_mrec ctx (ctx c).
  Proof.
    rewrite interp_mrec_trigger. cbn.
    unfold mrecursive, mrec. cbn. reflexivity.
  Qed.

  (** Any other event is passed through. *)
  Lemma interp_mrec_event T (e : MCFGEtop T) :
    interp_mrec ctx (ITree.trigger (inr1 e)) ≈ ITree.trigger e.
  Proof.
    rewrite interp_mrec_trigger. cbn. reflexivity.
  Qed.

  (** Out-of-memory is preserved by sequencing. *)
  Lemma ends_in_oom_bind {R S} (t : MCFGbot R) (k : R -> MCFGbot S) :
    ends_in_oom t -> ends_in_oom (ITree.bind t k).
  Proof.
    intros [k0 Ht].
    exists (fun v => ITree.bind (k0 v) k).
    rewrite Ht, bind_vis.
    reflexivity.
  Qed.

End CallLemmas.
