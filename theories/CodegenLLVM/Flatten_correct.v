(** * CodegenLLVM.Flatten_correct — structural correctness invariants for [Flatten].

    The [Flatten] pass ([theories/CodegenLLVM/Flatten.v]) linearises the
    emitter's tree-structured VIR: every compound operand (an
    [OP_IBinop]/[OP_ICmp]/[OP_Conversion]/[OP_GetElementPtr] used as an operand)
    is lifted to its own [INSTR_Op] binding under a fresh SSA name
    [flat_id c = Raw (Zneg (16 * c))].  The pass is currently tested-but-unproved.

    WHAT LEVEL OF SEMANTICS IS AVAILABLE.  The installed Vellvm (v3.0,
    [rocq-vellvm.v3.0.20260707]) ships the *denotation* functions
    ([Semantics/Denotation.v]: [denote_exp], [denote_instr], [denote_code],
    [denote_block]) but NO denotation metatheory: there is no [Theory/] directory
    and not a single equational lemma about [denote_code]/[denote_exp] anywhere in
    the install ([denote_code_cons], [denote_code_app], the [OP_IBinop] denotation
    equation, etc. were all deleted).  Moreover [denote_code] operates on
    [code dtyp] (post [typ->dtyp] conversion), whereas [Flatten] operates on
    [code typ].  A full "flattening preserves denotation" theorem would require
    reasoning that "execute the extra [INSTR_Op] code, then read the fresh
    register" equals "denote the operand inline" — i.e. the local-environment
    read-after-write law of the interpreter, plus freshness of the written name.
    That is exactly the interpreter/handler metatheory that is absent, so the
    itree-level equivalence is BLOCKED (see the closing note).

    We therefore prove the strongest *structural* invariants the pass relies on,
    with real [Qed] and no axioms:

    - Part 1: the fresh names are disjoint from every name the emitter can
      produce (the [16*c] vs [seed*16+k] argument, and vs the ANF variables).
    - Part 2: [atomize]/[atomize_op] produce LEGAL LLVM — the operand becomes
      atomic and [atomize_op] keeps a top-level [OP_] form.
    - Part 3: the fresh-name counter is monotone through the whole pass, which is
      the freshness backbone: threaded with Part 1 it guarantees the generated
      names never collide with each other or with emitter names. *)

From CertiRocq.CodegenLLVM Require Import Flatten.
From Vellvm Require Import Syntax.LLVMAst.
From Vellvm Require Import Syntax.AstLib.
From Stdlib Require Import BinNums BinPos ZArith List Lia.
Import ListNotations.

(* ================================================================= *)
(** * Part 1 — fresh-name arithmetic: disjointness / injectivity      *)
(* ================================================================= *)

(** By definition [flat_id c = Raw (Zneg (16 * c))]. *)
Lemma flat_id_eq : forall c, flat_id c = Raw (Zneg (16 * c)).
Proof. reflexivity. Qed.

(** Distinct counters give distinct fresh names. *)
Lemma flat_id_inj : forall c1 c2, flat_id c1 = flat_id c2 -> c1 = c2.
Proof. unfold flat_id. intros c1 c2 H. injection H as H. lia. Qed.

(** The emitter's own temporaries are [ntmp seed k = Raw (Zneg (seed*16 + k))]
    with [1 <= k] (see [LambdaANF_to_LLVM.ntmp]; the only [k] the emitter uses is
    [k = 1]).  Since [16*c] is a multiple of sixteen and [seed*16 + k] is not
    (for [0 < k < 16]), no fresh name coincides with an emitter temporary.  We
    state it directly on the arithmetic form to avoid coupling this file to the
    concurrently-edited emitter; [Raw (Zneg (seed*16 + k))] is definitionally
    [ntmp seed k]. *)
Lemma flat_id_disjoint_tmp : forall c seed k,
  (k < 16)%positive -> flat_id c <> Raw (Zneg (seed * 16 + k)).
Proof. unfold flat_id. intros c seed k Hk H. injection H as H. lia. Qed.

(** Real ANF variables serialise as [Raw (Zpos v)] (see [evar]/[base_env]); the
    fresh names live in the [Zneg] range and are therefore disjoint from them. *)
Lemma flat_id_disjoint_anf : forall c v, flat_id c <> Raw (Zpos v).
Proof. unfold flat_id. intros c v H. discriminate H. Qed.

(* ================================================================= *)
(** * Part 2 — legality: [atomize] atomises, [atomize_op] keeps an op *)
(* ================================================================= *)

(** The four operand shapes the pass decomposes. *)
Definition is_flat_op {T} (e : exp T) : Prop :=
  match e with
  | OP_IBinop _ _ _ _ => True
  | OP_ICmp _ _ _ _ _ => True
  | OP_Conversion _ _ _ _ => True
  | OP_GetElementPtr _ _ _ => True
  | _ => False
  end.

(** [atomize] returns an ATOMIC operand: either a fresh local register
    [EXP_Ident (ID_Local (flat_id n))], or the input expression unchanged (when
    it was not one of the decomposed operation forms).  This is precisely the
    property that makes the printed [.ll] legal — an operand is never itself a
    compound [OP_] form. *)
Lemma atomize_atomic : forall (e : exp typ) c,
  (exists n, snd (fst (atomize e c)) = EXP_Ident (ID_Local (flat_id n)))
  \/ snd (fst (atomize e c)) = e.
Proof.
  intros e c. destruct e; try (right; reflexivity).
  - cbn [atomize]. destruct (atomize e1 c) as [[c1 a1] n1].
    destruct (atomize e2 n1) as [[c2 a2] n2]. left. exists n2. reflexivity.
  - cbn [atomize]. destruct (atomize e1 c) as [[c1 a1] n1].
    destruct (atomize e2 n1) as [[c2 a2] n2]. left. exists n2. reflexivity.
  - cbn [atomize]. destruct (atomize e c) as [[c1 a1] n1]. left. exists n1. reflexivity.
  - cbn [atomize]. destruct ptrval as [pt pe].
    destruct (atomize pe c) as [[cp ape] np].
    match goal with |- context [ match ?X with | _ => _ end ] => destruct X as [[cidx aidxs] ni] end.
    left. exists ni. reflexivity.
Qed.

(** [atomize_op] keeps the top-level operator (LLVM requires the RHS of an
    [INSTR_Op] to be an [OP_] form) while atomising its immediate operands. *)
Lemma atomize_op_preserves : forall (e : exp typ) c,
  is_flat_op e -> is_flat_op (snd (fst (atomize_op e c))).
Proof.
  intros e c H. destruct e; try contradiction.
  - cbn [atomize_op]. destruct (atomize e1 c) as [[c1 a1] n1].
    destruct (atomize e2 n1) as [[c2 a2] n2]. exact I.
  - cbn [atomize_op]. destruct (atomize e1 c) as [[c1 a1] n1].
    destruct (atomize e2 n1) as [[c2 a2] n2]. exact I.
  - cbn [atomize_op]. destruct (atomize e c) as [[c1 a1] n1]. exact I.
  - cbn [atomize_op]. destruct ptrval as [pt pe].
    destruct (atomize pe c) as [[cp ape] np].
    destruct (atomize_idxs idxs np) as [[cidx aidxs] ni]. exact I.
Qed.

(* ================================================================= *)
(** * Part 3 — the fresh-name counter is monotone through the pass    *)
(* ================================================================= *)

(** List of GEP indices, taking per-element [atomize] monotonicity as a
    hypothesis (this is what the [exp] induction supplies in the GEP case). *)
Lemma atomize_idxs_mono_h : forall (l : list (typ * exp typ)) k,
  (forall p, In p l -> forall c, (c <= snd (atomize (snd p) c))%positive) ->
  (k <= snd (atomize_idxs l k))%positive.
Proof.
  induction l as [| [it ie] rest IH]; intros k H.
  - cbn. apply Pos.le_refl.
  - cbn [atomize_idxs].
    specialize (H (it, ie) (or_introl eq_refl)) as Hie. specialize (Hie k). cbn in Hie.
    destruct (atomize ie k) as [[ci ai] k1] eqn:Eie. cbn in Hie.
    destruct (atomize_idxs rest k1) as [[cr ar] k2] eqn:Erest.
    assert (Hrest : (k1 <= snd (atomize_idxs rest k1))%positive).
    { apply IH. intros p Hp. apply H. right. exact Hp. }
    rewrite Erest in Hrest. cbn in Hrest. cbn. lia.
Qed.

(** Core: [atomize] never decreases the counter.  Proved with Vellvm's strong
    [exp] induction ([AstLib.exp_ind]); the GEP case folds the anonymous inner
    fixpoint back to [atomize_idxs] (they are convertible) and appeals to the
    helper above. *)
Lemma atomize_mono : forall (e : exp typ) c, (c <= snd (atomize e c))%positive.
Proof.
  intros e. induction e using AstLib.exp_ind with (Q := fun _ : metadata typ => True);
    try (intros c; cbn [atomize]; apply Pos.le_refl); try exact I.
  - (* IBinop *) intros c. cbn [atomize].
    specialize (IHe1 c). destruct (atomize e1 c) as [[c1 a1] n1] eqn:E1. cbn in IHe1.
    specialize (IHe2 n1). destruct (atomize e2 n1) as [[c2 a2] n2] eqn:E2. cbn in IHe2.
    cbn. lia.
  - (* ICmp *) intros c. cbn [atomize].
    specialize (IHe1 c). destruct (atomize e1 c) as [[c1 a1] n1] eqn:E1. cbn in IHe1.
    specialize (IHe2 n1). destruct (atomize e2 n1) as [[c2 a2] n2] eqn:E2. cbn in IHe2.
    cbn. lia.
  - (* Conversion *) intros c. cbn [atomize].
    specialize (IHe c). destruct (atomize e c) as [[c1 a1] n1] eqn:E1. cbn in IHe.
    cbn. lia.
  - (* GetElementPtr *) intros c. cbn [atomize]. destruct ptrval as [pt pe].
    specialize (IHe c). destruct (atomize pe c) as [[cp ape] np] eqn:Epe. cbn in IHe.
    match goal with |- context [ ?F idxs np ] =>
      replace (F idxs np) with (atomize_idxs idxs np) by reflexivity end.
    destruct (atomize_idxs idxs np) as [[cidx aidxs] ni] eqn:Eidx.
    assert (Hni : (np <= snd (atomize_idxs idxs np))%positive).
    { apply atomize_idxs_mono_h. intros p Hp. apply H. exact Hp. }
    rewrite Eidx in Hni. cbn in Hni. rewrite Epe in IHe. cbn in IHe. cbn. lia.
Qed.

(** Downstream monotonicity for every counter-threading function in the pass. *)

Lemma atomize_idxs_mono : forall l k, (k <= snd (atomize_idxs l k))%positive.
Proof. intros l k. apply atomize_idxs_mono_h. intros p _ c. apply atomize_mono. Qed.

Lemma atomize_texp_mono : forall te c, (c <= snd (atomize_texp te c))%positive.
Proof.
  intros [t e] c. unfold atomize_texp.
  destruct (atomize e c) as [[cc ae] n] eqn:E.
  pose proof (atomize_mono e c) as Hm. rewrite E in Hm. cbn in Hm. cbn. exact Hm.
Qed.

Lemma atomize_op_mono : forall (e : exp typ) c, (c <= snd (atomize_op e c))%positive.
Proof.
  intros e c. destruct e; try (cbn [atomize_op]; apply Pos.le_refl).
  - cbn [atomize_op].
    pose proof (atomize_mono e1 c) as H1. destruct (atomize e1 c) as [[c1 a1] n1] eqn:E1. cbn in H1.
    pose proof (atomize_mono e2 n1) as H2. destruct (atomize e2 n1) as [[c2 a2] n2] eqn:E2. cbn in H2.
    cbn. lia.
  - cbn [atomize_op].
    pose proof (atomize_mono e1 c) as H1. destruct (atomize e1 c) as [[c1 a1] n1] eqn:E1. cbn in H1.
    pose proof (atomize_mono e2 n1) as H2. destruct (atomize e2 n1) as [[c2 a2] n2] eqn:E2. cbn in H2.
    cbn. lia.
  - cbn [atomize_op].
    pose proof (atomize_mono e c) as H1. destruct (atomize e c) as [[c1 a1] n1] eqn:E1. cbn in H1.
    cbn. lia.
  - cbn [atomize_op]. destruct ptrval as [pt pe].
    pose proof (atomize_mono pe c) as H1. destruct (atomize pe c) as [[cp ape] np] eqn:Epe. cbn in H1.
    pose proof (atomize_idxs_mono idxs np) as H2.
    destruct (atomize_idxs idxs np) as [[cidx aidxs] ni] eqn:Eidx. cbn in H2.
    cbn. lia.
Qed.

Lemma atomize_args_mono : forall l k, (k <= snd (atomize_args l k))%positive.
Proof.
  induction l as [| [te pa] rest IH]; intros k.
  - cbn. apply Pos.le_refl.
  - cbn [atomize_args].
    pose proof (atomize_texp_mono te k) as H1.
    destruct (atomize_texp te k) as [[cc te'] k1] eqn:E1. cbn in H1.
    pose proof (IH k1) as H2.
    destruct (atomize_args rest k1) as [[cr ar] k2] eqn:E2. cbn in H2.
    cbn. lia.
Qed.

Lemma flat_code_mono : forall l c, (c <= snd (flat_code l c))%positive.
Proof.
  induction l as [| [[id i] md] rest IH]; intros c.
  - cbn. apply Pos.le_refl.
  - cbn [flat_code].
    destruct i as [ msg | op | fn args anns obs | aty aanns | lt ptr lanns
                  | val ptr sanns | sy o | cx | armw | va vt | rt cu cs ];
      (* the 7 instruction forms Flatten leaves untouched keep the counter *)
      try (pose proof (IH c) as Hr; destruct (flat_code rest c) as [cr n2] eqn:Er;
           cbn in Hr; cbn; lia).
    + (* Op *)
      pose proof (atomize_op_mono op c) as Ho.
      destruct (atomize_op op c) as [[cc op'] n1] eqn:Eo. cbn in Ho.
      pose proof (IH n1) as Hr. destruct (flat_code rest n1) as [cr n2] eqn:Er. cbn in Hr.
      cbn. lia.
    + (* Call *)
      pose proof (atomize_texp_mono fn c) as Hf.
      destruct (atomize_texp fn c) as [[c1 fn'] m1] eqn:Ef. cbn in Hf.
      pose proof (atomize_args_mono args m1) as Ha.
      destruct (atomize_args args m1) as [[c2 args'] m2] eqn:Ea. cbn in Ha.
      pose proof (IH m2) as Hr. destruct (flat_code rest m2) as [cr n2] eqn:Er. cbn in Hr.
      cbn. lia.
    + (* Load *)
      pose proof (atomize_texp_mono ptr c) as Hp.
      destruct (atomize_texp ptr c) as [[cc ptr'] n1] eqn:Ep. cbn in Hp.
      pose proof (IH n1) as Hr. destruct (flat_code rest n1) as [cr n2] eqn:Er. cbn in Hr.
      cbn. lia.
    + (* Store *)
      pose proof (atomize_texp_mono val c) as Hv.
      destruct (atomize_texp val c) as [[c1 val'] m1] eqn:Ev. cbn in Hv.
      pose proof (atomize_texp_mono ptr m1) as Hp.
      destruct (atomize_texp ptr m1) as [[c2 ptr'] m2] eqn:Ep. cbn in Hp.
      pose proof (IH m2) as Hr. destruct (flat_code rest m2) as [cr n2] eqn:Er. cbn in Hr.
      cbn. lia.
Qed.

Lemma flat_term_mono : forall tm c, (c <= snd (flat_term tm c))%positive.
Proof.
  intros tm c. destruct tm; try (cbn [flat_term]; apply Pos.le_refl).
  - cbn [flat_term]. pose proof (atomize_texp_mono v c) as H.
    destruct (atomize_texp v c) as [[cc v'] n] eqn:E. cbn in H. cbn. exact H.
  - cbn [flat_term]. pose proof (atomize_texp_mono v c) as H.
    destruct (atomize_texp v c) as [[cc v'] n] eqn:E. cbn in H. cbn. exact H.
  - cbn [flat_term]. pose proof (atomize_texp_mono v c) as H.
    destruct (atomize_texp v c) as [[cc v'] n] eqn:E. cbn in H. cbn. exact H.
Qed.

Lemma flat_block_mono : forall b c, (c <= snd (flat_block b c))%positive.
Proof.
  intros b c. unfold flat_block.
  pose proof (flat_code_mono (blk_code b) c) as Hc.
  destruct (flat_code (blk_code b) c) as [cc n1] eqn:Ec. cbn in Hc.
  destruct (blk_term b) as [[tid tm] tmd].
  pose proof (flat_term_mono tm n1) as Ht.
  destruct (flat_term tm n1) as [[tc tm'] n2] eqn:Et. cbn in Ht.
  cbn. lia.
Qed.
