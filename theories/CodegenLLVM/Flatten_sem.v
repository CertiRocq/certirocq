(** * CodegenLLVM.Flatten_sem — semantic preservation of [Flatten].

    [Flatten.flatten_prog] lifts nested operand expressions into fresh
    [INSTR_Op] bindings named [flat_id c].  This file proves that this
    preserves the semantics (Vellvm's [interp_mcfg] after the call knot
    [interp_mrec]), up to the extra writes to the fresh locals.

    Overview.
    - Part 1 (syntax): a [T]-polymorphic copy of the flattener ([atomizeP],
      [flat_codeP], [flat_blockP], ...), its agreement with [Flatten] on [typ],
      and its commutation with [tfmap] (hence with [convert_typ], i.e. with the
      [typ] -> [dtyp] conversion).
    - Part 2 (semantics, on [dtyp]): frames are related by
      [agree_except lo hi] (equal except at fresh names [flat_id k],
      [lo <= k < hi]).  Expression-level: [atomizeP_sound],
      [atomize_texpP_sound], [atomize_idxsP_sound], [atomize_opP_sound],
      [atomize_argsP_sound] (the atomisation prefix runs to [Ret], only
      writing fresh names, and the atoms evaluate to the original values).
      Instruction-level: [flat_instr_transfer] (eutt up to [agree_except]
      for Op/Load/Store/Alloca, with corollaries [flat_instr_runs],
      [flat_instr_oom]) and [flat_call_transfer] (calls: pure prefix, then
      an atomised call whose operands evaluate to the same values).
      Terminators: [flat_term_transfer].  Blocks: [flat_block_tail] and the
      [flat_tail_*] stepping lemmas for the [tail_of]-shape
      "code ;; terminator >>= K" of [fst (flat_blockP b c)].

    The source code must satisfy a light well-formedness condition
    ([noflat_exp], [instr_ok], [term_ok]: source never mentions fresh names,
    operands are of the forms the emitter produces) and the operand
    evaluations must succeed ([instr_evals], [term_evals]).  The latter is
    needed because flattening moves the evaluation of an atomic operand
    after that of the compound operands that follow it (e.g.
    [store %x, (gep %p, 1)]); if the atomic operand could fail while the
    compound one raises a different abortive event (UB, out-of-memory),
    the two programs would be observably different.
*)

From Stdlib Require Import ZArith List Lia Program Morphisms.
From ITree Require Import ITree ITreeFacts Eq.Eqit Interp.InterpFacts
     Interp.RecursionFacts Events.State Events.StateFacts.
From ExtLib Require Import Structures.Monads.
From Paco Require Import paco.
From Vellvm Require Import
  Utils Syntax Params
  Interfaces.Memory Implementations.Memory
  Semantics.DynamicValues Semantics.LLVMEvents Semantics.Denotation
  Semantics.InterpretationStack Semantics.Operations Handlers.
From CertiRocq.CodegenLLVM Require Import Flatten LambdaANF_to_LLVM LambdaANF_to_LLVM_statement
     LLVM_interp_lemmas LLVM_call_lemmas LLVM_convert LLVM_exp_lemmas.

Import ListNotations.
Import MonadNotation.
Open Scope monad_scope.

(* ================================================================== *)
(** * Part 1: a [T]-polymorphic flattener *)

Section FlatP.
  Context {T : Set}.

  Fixpoint atomizeP (e : exp T) (c : positive) {struct e}
    : code T * exp T * positive :=
    match e with
    | OP_IBinop op t e1 e2 =>
        let '(c1, a1, n1) := atomizeP e1 c in
        let '(c2, a2, n2) := atomizeP e2 n1 in
        let fid := flat_id n2 in
        ((c1 ++ c2 ++ [(IId fid, INSTR_Op (OP_IBinop op t a1 a2), [])])%list,
         EXP_Ident (ID_Local fid), Pos.succ n2)
    | OP_ICmp ss cmp t e1 e2 =>
        let '(c1, a1, n1) := atomizeP e1 c in
        let '(c2, a2, n2) := atomizeP e2 n1 in
        let fid := flat_id n2 in
        ((c1 ++ c2 ++ [(IId fid, INSTR_Op (OP_ICmp ss cmp t a1 a2), [])])%list,
         EXP_Ident (ID_Local fid), Pos.succ n2)
    | OP_Conversion cv t1 e1 t2 =>
        let '(c1, a1, n1) := atomizeP e1 c in
        let fid := flat_id n1 in
        ((c1 ++ [(IId fid, INSTR_Op (OP_Conversion cv t1 a1 t2), [])])%list,
         EXP_Ident (ID_Local fid), Pos.succ n1)
    | OP_GetElementPtr t ptr idxs =>
        let '(pt, pe) := ptr in
        let '(cp, ape, np) := atomizeP pe c in
        let fix aidx (l : list (T * exp T)) (k : positive) {struct l}
              : code T * list (T * exp T) * positive :=
            match l with
            | [] => ([], [], k)
            | (it, ie) :: rest =>
                let '(ci, ai, k1) := atomizeP ie k in
                let '(cr, ar, k2) := aidx rest k1 in
                ((ci ++ cr)%list, (it, ai) :: ar, k2)
            end in
        let '(cidx, aidxs, ni) := aidx idxs np in
        let fid := flat_id ni in
        ((cp ++ cidx ++ [(IId fid, INSTR_Op (OP_GetElementPtr t (pt, ape) aidxs), [])])%list,
         EXP_Ident (ID_Local fid), Pos.succ ni)
    | _ => ([], e, c)
    end.

  Fixpoint atomize_idxsP (l : list (T * exp T)) (k : positive) {struct l}
    : code T * list (T * exp T) * positive :=
    match l with
    | [] => ([], [], k)
    | (it, ie) :: rest =>
        let '(ci, ai, k1) := atomizeP ie k in
        let '(cr, ar, k2) := atomize_idxsP rest k1 in
        ((ci ++ cr)%list, (it, ai) :: ar, k2)
    end.

  Definition atomize_texpP (te : T * exp T) (c : positive)
    : code T * (T * exp T) * positive :=
    let '(t, e) := te in
    let '(cc, ae, n) := atomizeP e c in
    (cc, (t, ae), n).

  Definition atomize_opP (e : exp T) (c : positive) : code T * exp T * positive :=
    match e with
    | OP_IBinop op t e1 e2 =>
        let '(c1, a1, n1) := atomizeP e1 c in
        let '(c2, a2, n2) := atomizeP e2 n1 in
        ((c1 ++ c2)%list, OP_IBinop op t a1 a2, n2)
    | OP_ICmp ss cmp t e1 e2 =>
        let '(c1, a1, n1) := atomizeP e1 c in
        let '(c2, a2, n2) := atomizeP e2 n1 in
        ((c1 ++ c2)%list, OP_ICmp ss cmp t a1 a2, n2)
    | OP_Conversion cv t1 e1 t2 =>
        let '(c1, a1, n1) := atomizeP e1 c in
        (c1, OP_Conversion cv t1 a1 t2, n1)
    | OP_GetElementPtr t ptr idxs =>
        let '(pt, pe) := ptr in
        let '(cp, ape, np) := atomizeP pe c in
        let '(cidx, aidxs, ni) := atomize_idxsP idxs np in
        ((cp ++ cidx)%list, OP_GetElementPtr t (pt, ape) aidxs, ni)
    | _ => ([], e, c)
    end.

  Fixpoint atomize_argsP (l : list (texp T * list param_attr)) (k : positive)
           {struct l} : code T * list (texp T * list param_attr) * positive :=
    match l with
    | [] => ([], [], k)
    | (te, pa) :: rest =>
        let '(cc, te', k1) := atomize_texpP te k in
        let '(cr, ar, k2) := atomize_argsP rest k1 in
        ((cc ++ cr)%list, (te', pa) :: ar, k2)
    end.

  (** The per-instruction body of [Flatten.flat_code].  NB: for calls the
      callee is atomized before the arguments (as in [Flatten]), although
      Vellvm's [denote_instr] evaluates the arguments first; this is harmless
      because the emitted operand expressions are pure (see Part 2). *)
  Definition flat_instrP (x : instr_id * instr T * list (metadata T)) (c : positive)
    : code T * positive :=
    let '(id, i, md) := x in
    match i with
    | INSTR_Op e =>
        let '(cc, e', n) := atomize_opP e c in
        ((cc ++ [(id, INSTR_Op e', md)])%list, n)
    | INSTR_Load t ptr anns =>
        let '(cc, ptr', n) := atomize_texpP ptr c in
        ((cc ++ [(id, INSTR_Load t ptr' anns, md)])%list, n)
    | INSTR_Store val ptr anns =>
        let '(c1, val', n1) := atomize_texpP val c in
        let '(c2, ptr', n2) := atomize_texpP ptr n1 in
        ((c1 ++ c2 ++ [(id, INSTR_Store val' ptr' anns, md)])%list, n2)
    | INSTR_Call fn args anns obs =>
        let '(c1, fn', n1) := atomize_texpP fn c in
        let '(c2, args', n2) := atomize_argsP args n1 in
        ((c1 ++ c2 ++ [(id, INSTR_Call fn' args' anns obs, md)])%list, n2)
    | _ => ([(id, i, md)], c)
    end.

  Fixpoint flat_codeP (l : code T) (c : positive) {struct l} : code T * positive :=
    match l with
    | [] => ([], c)
    | x :: rest =>
        let '(ci, n1) := flat_instrP x c in
        let '(cr, n2) := flat_codeP rest n1 in
        ((ci ++ cr)%list, n2)
    end.

  Definition flat_termP (tm : terminator T) (c : positive)
    : code T * terminator T * positive :=
    match tm with
    | TERM_Ret v      => let '(cc, v', n) := atomize_texpP v c in (cc, TERM_Ret v', n)
    | TERM_Br v b1 b2 => let '(cc, v', n) := atomize_texpP v c in (cc, TERM_Br v' b1 b2, n)
    | TERM_Switch v d brs =>
        let '(cc, v', n) := atomize_texpP v c in (cc, TERM_Switch v' d brs, n)
    | _ => ([], tm, c)
    end.

  Definition flat_blockP (b : LLVMAst.block T) (c : positive) : LLVMAst.block T * positive :=
    let '(cc, n1) := flat_codeP (blk_code b) c in
    let '(tid, tm, tmd) := blk_term b in
    let '(tc, tm', n2) := flat_termP tm n1 in
    (mk_block (blk_id b) (blk_phis b) (cc ++ tc)%list (tid, tm', tmd) (blk_comments b), n2).

  Fixpoint flat_blocksP (bs : list (LLVMAst.block T)) (c : positive) {struct bs}
    : list (LLVMAst.block T) * positive :=
    match bs with
    | [] => ([], c)
    | b :: rest =>
        let '(b', n1) := flat_blockP b c in
        let '(rs, n2) := flat_blocksP rest n1 in
        (b' :: rs, n2)
    end.

  (** Custom induction principle following [atomizeP]'s recursion. *)
  Definition compound (e : exp T) : bool :=
    match e with
    | OP_IBinop _ _ _ _ | OP_ICmp _ _ _ _ _ | OP_Conversion _ _ _ _
    | OP_GetElementPtr _ _ _ => true
    | _ => false
    end.

  Lemma exp_indP (P : exp T -> Prop)
        (HA : forall e, compound e = false -> P e)
        (HB : forall op t e1 e2, P e1 -> P e2 -> P (OP_IBinop op t e1 e2))
        (HC : forall ss cmp t e1 e2, P e1 -> P e2 -> P (OP_ICmp ss cmp t e1 e2))
        (HD : forall cv t1 e1 t2, P e1 -> P (OP_Conversion cv t1 e1 t2))
        (HG : forall t pt pe idxs, P pe -> Forall (fun te => P (snd te)) idxs ->
                              P (OP_GetElementPtr t (pt, pe) idxs)) :
    forall e, P e.
  Proof.
    fix F 1. intros e. destruct e; try (apply HA; reflexivity).
    - apply HB; apply F.
    - apply HC; apply F.
    - apply HD; apply F.
    - match goal with |- P (OP_GetElementPtr _ ?p ?l) => destruct p as [pt pe]; revert l end.
      intros idxs. apply HG; [apply F|].
      revert idxs. fix G 1. intros [|[it ie] r]; constructor; [apply F | apply G].
  Qed.

  Lemma atomizeP_atomic e c : compound e = false -> atomizeP e c = ([], e, c).
  Proof. destruct e; cbn; congruence. Qed.

  Lemma aidx_eq (idxs : list (T * exp T)) k :
    (fix aidx (l : list (T * exp T)) (k : positive) {struct l}
       : code T * list (T * exp T) * positive :=
       match l with
       | [] => ([], [], k)
       | (it, ie) :: rest =>
           let '(ci, ai, k1) := atomizeP ie k in
           let '(cr, ar, k2) := aidx rest k1 in
           ((ci ++ cr)%list, (it, ai) :: ar, k2)
       end) idxs k = atomize_idxsP idxs k.
  Proof.
    revert k; induction idxs as [|[it ie] r IH]; intros k; cbn; [reflexivity|].
    destruct (atomizeP ie k) as [[ci ai] k1].
    rewrite IH. reflexivity.
  Qed.

  Lemma atomizeP_GEP t pt pe idxs c :
    atomizeP (OP_GetElementPtr t (pt, pe) idxs) c =
      let '(cp, ape, np) := atomizeP pe c in
      let '(cidx, aidxs, ni) := atomize_idxsP idxs np in
      let fid := flat_id ni in
      ((cp ++ cidx ++ [(IId fid, INSTR_Op (OP_GetElementPtr t (pt, ape) aidxs), [])])%list,
       EXP_Ident (ID_Local fid), Pos.succ ni).
  Proof.
    cbn [atomizeP]. destruct (atomizeP pe c) as [[cp ape] np].
    rewrite aidx_eq. reflexivity.
  Qed.

End FlatP.

(** ** Agreement with [Flatten] (on [typ]) *)

Lemma atomize_eq (e : exp typ) c : Flatten.atomize e c = atomizeP e c.
Proof.
  revert c. induction e using exp_indP; intros c.
  - destruct e; cbn in *; congruence.
  - cbn. rewrite IHe1. destruct (atomizeP e1 c) as [[c1 a1] n1].
    rewrite IHe2. reflexivity.
  - cbn. rewrite IHe1. destruct (atomizeP e1 c) as [[c1 a1] n1].
    rewrite IHe2. reflexivity.
  - cbn. rewrite IHe. reflexivity.
  - cbn [Flatten.atomize]. rewrite atomizeP_GEP. rewrite IHe.
    destruct (atomizeP e c) as [[cp ape] np].
    match goal with
    | |- context [?F idxs np] =>
        match F with
        | context [Flatten.atomize] =>
            assert (Hf : forall k, F idxs k = atomize_idxsP idxs k)
        end
    end.
    { clear -H. induction H as [|[it ie] r Hie Hr IH]; intros k; cbn; [reflexivity|].
      cbn in Hie. rewrite Hie. destruct (atomizeP ie k) as [[ci ai] k1].
      rewrite IH. reflexivity. }
    rewrite Hf. reflexivity.
Qed.

Lemma atomize_idxs_eq (l : list (typ * exp typ)) k :
  Flatten.atomize_idxs l k = atomize_idxsP l k.
Proof.
  revert k; induction l as [|[it ie] r IH]; intros k; cbn; [reflexivity|].
  rewrite atomize_eq. destruct (atomizeP ie k) as [[ci ai] k1].
  rewrite IH. reflexivity.
Qed.

Lemma atomize_texp_eq (te : typ * exp typ) c :
  Flatten.atomize_texp te c = atomize_texpP te c.
Proof. destruct te; cbn. rewrite atomize_eq. reflexivity. Qed.

Lemma atomize_op_eq (e : exp typ) c : Flatten.atomize_op e c = atomize_opP e c.
Proof.
  destruct e; cbn; try reflexivity;
    try match goal with p : (typ * exp typ)%type |- _ => destruct p end;
    rewrite ?atomize_eq;
    repeat (match goal with |- context [atomizeP ?e ?c] =>
                              destruct (atomizeP e c) as [[? ?] ?] end;
            rewrite ?atomize_eq, ?atomize_idxs_eq);
    reflexivity.
Qed.

Lemma atomize_args_eq l k : Flatten.atomize_args l k = atomize_argsP l k.
Proof.
  revert k; induction l as [|[te pa] r IH]; intros k; cbn; [reflexivity|].
  rewrite atomize_texp_eq. destruct (atomize_texpP te k) as [[cc te'] k1].
  rewrite IH. reflexivity.
Qed.

Lemma flat_code_eq (l : code typ) c : Flatten.flat_code l c = flat_codeP l c.
Proof.
  revert c; induction l as [|[[id i] md] r IH]; intros c;
    cbn [Flatten.flat_code flat_codeP]; [reflexivity|].
  assert (Hi : (match i with
           | INSTR_Op e =>
               let '(cc, e', n) := Flatten.atomize_op e c in
               ((cc ++ [(id, INSTR_Op e', md)])%list, n)
           | INSTR_Load t ptr anns =>
               let '(cc, ptr', n) := Flatten.atomize_texp ptr c in
               ((cc ++ [(id, INSTR_Load t ptr' anns, md)])%list, n)
           | INSTR_Store val ptr anns =>
               let '(c1, val', n1) := Flatten.atomize_texp val c in
               let '(c2, ptr', n2) := Flatten.atomize_texp ptr n1 in
               ((c1 ++ c2 ++ [(id, INSTR_Store val' ptr' anns, md)])%list, n2)
           | INSTR_Call fn args anns obs =>
               let '(c1, fn', n1) := Flatten.atomize_texp fn c in
               let '(c2, args', n2) := Flatten.atomize_args args n1 in
               ((c1 ++ c2 ++ [(id, INSTR_Call fn' args' anns obs, md)])%list, n2)
           | _ => ([(id, i, md)], c)
           end) = flat_instrP (id, i, md) c).
  { destruct i; cbn -[Flatten.atomize_op atomize_opP Flatten.atomize_texp atomize_texpP
                      Flatten.atomize_args atomize_argsP]; try reflexivity.
    all: try (rewrite atomize_op_eq; reflexivity).
    all: try (rewrite atomize_texp_eq; reflexivity).
    all: try (rewrite atomize_texp_eq;
              match goal with |- context [atomize_texpP ?v ?c0] =>
                                destruct (atomize_texpP v c0) as [[c1 v'] n1] end;
              rewrite ?atomize_texp_eq, ?atomize_args_eq; reflexivity). }
  rewrite Hi. destruct (flat_instrP (id, i, md) c) as [ci n1].
  rewrite IH. reflexivity.
Qed.

Lemma flat_term_eq (tm : terminator typ) c : Flatten.flat_term tm c = flat_termP tm c.
Proof. destruct tm; cbn; rewrite ?atomize_texp_eq; reflexivity. Qed.

Lemma flat_block_eq (b : LLVMAst.block typ) c : Flatten.flat_block b c = flat_blockP b c.
Proof.
  unfold Flatten.flat_block, flat_blockP. rewrite flat_code_eq.
  destruct (flat_codeP (blk_code b) c) as [cc n1]. destruct (blk_term b) as [[tid tm] tmd].
  rewrite flat_term_eq. reflexivity.
Qed.

Lemma flat_blocks_eq (bs : list (LLVMAst.block typ)) c :
  Flatten.flat_blocks bs c = flat_blocksP bs c.
Proof.
  revert c; induction bs as [|b r IH]; intros c; cbn; [reflexivity|].
  rewrite flat_block_eq. destruct (flat_blockP b c) as [b' n1]. rewrite IH. reflexivity.
Qed.

(** ** Commutation with type conversion ([tfmap], hence [convert_typ]) *)

Section TFmap.
  Context {U V : Set} (f : U -> V).

  Notation fe := (@tfmap exp _ U V f).
  Notation fc := (@tfmap code _ U V f).

  Lemma fc_app (a b : code U) : fc (a ++ b)%list = (fc a ++ fc b)%list.
  Proof. unfold tfmap, TFunctor_code, tfmap, TFunctor_list. apply map_app. Qed.

  Lemma compound_tfmap e : compound (fe e) = compound e.
  Proof. destruct e; reflexivity. Qed.

  Lemma atomizeP_tfmap e c :
    atomizeP (fe e) c = let '(cc, a, n) := atomizeP e c in (fc cc, fe a, n).
  Proof.
    revert c. induction e using exp_indP; intros c.
    - rewrite !atomizeP_atomic by (rewrite ?compound_tfmap; assumption). reflexivity.
    - change (fe (OP_IBinop op t e1 e2)) with (OP_IBinop op (f t) (fe e1) (fe e2)).
      cbn [atomizeP]. rewrite IHe1. destruct (atomizeP e1 c) as [[c1 a1] n1].
      rewrite IHe2. destruct (atomizeP e2 n1) as [[c2 a2] n2].
      cbv beta iota zeta; rewrite !fc_app. reflexivity.
    - change (fe (OP_ICmp ss cmp t e1 e2)) with (OP_ICmp ss cmp (f t) (fe e1) (fe e2)).
      cbn [atomizeP]. rewrite IHe1. destruct (atomizeP e1 c) as [[c1 a1] n1].
      rewrite IHe2. destruct (atomizeP e2 n1) as [[c2 a2] n2].
      cbv beta iota zeta; rewrite !fc_app. reflexivity.
    - change (fe (OP_Conversion cv t1 e t2)) with (OP_Conversion cv (f t1) (fe e) (f t2)).
      cbn [atomizeP]. rewrite IHe. destruct (atomizeP e c) as [[c1 a1] n1].
      cbv beta iota zeta; rewrite !fc_app. reflexivity.
    - change (fe (OP_GetElementPtr t (pt, e) idxs))
        with (OP_GetElementPtr (f t) (f pt, fe e) (map (fun te => (f (fst te), fe (snd te))) idxs)).
      rewrite !atomizeP_GEP. rewrite IHe. destruct (atomizeP e c) as [[cp ape] np].
      assert (Hi : forall k, atomize_idxsP (map (fun te => (f (fst te), fe (snd te))) idxs) k =
                        let '(ci, ai, n) := atomize_idxsP idxs k in
                        (fc ci, map (fun te => (f (fst te), fe (snd te))) ai, n)).
      { clear -H. induction H as [|[it ie] r Hie Hr IH]; intros k; cbn [map atomize_idxsP fst snd];
          [reflexivity|].
        cbn in Hie. rewrite Hie. destruct (atomizeP ie k) as [[ci ai] k1].
        rewrite IH. destruct (atomize_idxsP r k1) as [[cr ar] k2].
        rewrite fc_app. reflexivity. }
      rewrite Hi. destruct (atomize_idxsP idxs np) as [[ci ai] ni].
      cbv beta iota zeta; rewrite !fc_app. reflexivity.
  Qed.

  Notation ft := (fun te : U * exp U => (f (fst te), fe (snd te))).

  Lemma atomize_idxsP_tfmap idxs k :
    atomize_idxsP (map ft idxs) k =
      let '(ci, ai, n) := atomize_idxsP idxs k in (fc ci, map ft ai, n).
  Proof.
    revert k; induction idxs as [|[it ie] r IH]; intros k; cbn [map atomize_idxsP fst snd];
      [reflexivity|].
    rewrite atomizeP_tfmap. destruct (atomizeP ie k) as [[ci ai] k1].
    rewrite IH. destruct (atomize_idxsP r k1) as [[cr ar] k2].
    cbv beta iota zeta; rewrite fc_app. reflexivity.
  Qed.

  Notation ft' := (fun te : U * exp U => let '(t, e) := te in (f t, fe e)).

  Lemma atomize_texpP_tfmap te c :
    atomize_texpP (ft' te) c = let '(cc, a, n) := atomize_texpP te c in (fc cc, ft' a, n).
  Proof.
    destruct te as [t e]. cbn [atomize_texpP fst snd]. rewrite atomizeP_tfmap.
    destruct (atomizeP e c) as [[cc a] n]. reflexivity.
  Qed.

  Lemma atomize_opP_tfmap e c :
    atomize_opP (fe e) c = let '(cc, a, n) := atomize_opP e c in (fc cc, fe a, n).
  Proof.
    destruct e; try reflexivity.
    - change (fe (OP_IBinop iop t e1 e2)) with (OP_IBinop iop (f t) (fe e1) (fe e2)).
      cbn [atomize_opP]. rewrite atomizeP_tfmap. destruct (atomizeP e1 c) as [[c1 a1] n1].
      rewrite atomizeP_tfmap. destruct (atomizeP e2 n1) as [[c2 a2] n2].
      cbv beta iota zeta; rewrite !fc_app. reflexivity.
    - change (fe (OP_ICmp samesign cmp t e1 e2)) with (OP_ICmp samesign cmp (f t) (fe e1) (fe e2)).
      cbn [atomize_opP]. rewrite atomizeP_tfmap. destruct (atomizeP e1 c) as [[c1 a1] n1].
      rewrite atomizeP_tfmap. destruct (atomizeP e2 n1) as [[c2 a2] n2].
      cbv beta iota zeta; rewrite !fc_app. reflexivity.
    - change (fe (OP_Conversion conv t_from e t_to)) with (OP_Conversion conv (f t_from) (fe e) (f t_to)).
      cbn [atomize_opP]. rewrite atomizeP_tfmap. destruct (atomizeP e c) as [[c1 a1] n1].
      reflexivity.
    - destruct ptrval as [pt pe].
      change (fe (OP_GetElementPtr t (pt, pe) idxs))
        with (OP_GetElementPtr (f t) (f pt, fe pe) (map ft idxs)).
      cbn [atomize_opP]. rewrite atomizeP_tfmap. destruct (atomizeP pe c) as [[cp ape] np].
      rewrite atomize_idxsP_tfmap. destruct (atomize_idxsP idxs np) as [[ci ai] ni].
      cbv beta iota zeta; rewrite !fc_app. reflexivity.
  Qed.

  Notation fa := (fun x : texp U * list param_attr => let '(te, a) := x in (ft' te, a)).

  Lemma atomize_argsP_tfmap l k :
    atomize_argsP (map fa l) k =
      let '(ci, ai, n) := atomize_argsP l k in (fc ci, map fa ai, n).
  Proof.
    revert k; induction l as [|[te pa] r IH]; intros k; cbn [map atomize_argsP];
      [reflexivity|].
    rewrite atomize_texpP_tfmap. destruct (atomize_texpP te k) as [[ci ai] k1].
    rewrite IH. destruct (atomize_argsP r k1) as [[cr ar] k2].
    cbv beta iota zeta; rewrite fc_app. reflexivity.
  Qed.

  Notation fx := (fun x : instr_id * instr U * list (metadata U) =>
                    let '(id, i, l) := x in (@endo instr_id _ id, @tfmap instr _ U V f i, @tfmap (fun T => list (metadata T)) _ U V f l)).

  Lemma fc_map (l : code U) : fc l = map fx l.
  Proof. reflexivity. Qed.

  Lemma tfmap_instr_Op op : @tfmap instr _ U V f (INSTR_Op op) = INSTR_Op (fe op).
  Proof. reflexivity. Qed.
  Lemma tfmap_instr_Call fn args anns obs :
    @tfmap instr _ U V f (INSTR_Call fn args anns obs)
    = INSTR_Call (ft' fn) (map fa args) (tfmap f anns) (tfmap f obs).
  Proof. reflexivity. Qed.
  Lemma tfmap_instr_Load t ptr anns :
    @tfmap instr _ U V f (INSTR_Load t ptr anns)
    = INSTR_Load (f t) (ft' ptr) (tfmap f anns).
  Proof. reflexivity. Qed.
  Lemma tfmap_instr_Store val ptr anns :
    @tfmap instr _ U V f (INSTR_Store val ptr anns)
    = INSTR_Store (ft' val) (ft' ptr) (tfmap f anns).
  Proof. reflexivity. Qed.

  Lemma flat_instrP_tfmap x c :
    flat_instrP (fx x) c = let '(cc, n) := flat_instrP x c in (fc cc, n).
  Proof.
    destruct x as [[id i] md].
    destruct i; try reflexivity.
    - (* INSTR_Op *)
      rewrite tfmap_instr_Op.
      cbn [flat_instrP]. rewrite atomize_opP_tfmap. destruct (atomize_opP op c) as [[c1 a1] n1].
      cbv beta iota zeta; rewrite !fc_app; reflexivity.
    - (* INSTR_Call *)
      rewrite tfmap_instr_Call.
      cbn [flat_instrP]. rewrite atomize_texpP_tfmap. destruct (atomize_texpP fn c) as [[c1 a1] n1].
      rewrite atomize_argsP_tfmap. destruct (atomize_argsP args n1) as [[c2 a2] n2].
      cbv beta iota zeta; rewrite !fc_app; reflexivity.
    - (* INSTR_Load *)
      rewrite tfmap_instr_Load.
      cbn [flat_instrP]. rewrite atomize_texpP_tfmap. destruct (atomize_texpP ptr c) as [[c1 a1] n1].
      cbv beta iota zeta; rewrite !fc_app; reflexivity.
    - (* INSTR_Store *)
      rewrite tfmap_instr_Store.
      cbn [flat_instrP]. rewrite atomize_texpP_tfmap. destruct (atomize_texpP val c) as [[c1 a1] n1].
      rewrite atomize_texpP_tfmap. destruct (atomize_texpP ptr n1) as [[c2 a2] n2].
      cbv beta iota zeta; rewrite !fc_app; reflexivity.
  Qed.

  Lemma flat_codeP_tfmap l c :
    flat_codeP (fc l) c = let '(cc, n) := flat_codeP l c in (fc cc, n).
  Proof.
    revert c; induction l as [|x r IH]; intros c; [reflexivity|].
    change (fc (x :: r)) with (fx x :: fc r).
    cbn [flat_codeP]. rewrite flat_instrP_tfmap. destruct (flat_instrP x c) as [ci n1].
    rewrite IH. destruct (flat_codeP r n1) as [cr n2].
    cbv beta iota zeta; rewrite !fc_app. reflexivity.
  Qed.

  Notation ftm := (@tfmap terminator _ U V f).

  Lemma flat_termP_tfmap tm c :
    flat_termP (ftm tm) c = let '(cc, tm', n) := flat_termP tm c in (fc cc, ftm tm', n).
  Proof.
    destruct tm; try reflexivity.
    - change (ftm (TERM_Ret v)) with (TERM_Ret (ft' v)). cbn [flat_termP].
      rewrite atomize_texpP_tfmap. destruct (atomize_texpP v c) as [[c1 a1] n1]. reflexivity.
    - change (ftm (TERM_Br v br1 br2)) with (TERM_Br (ft' v) br1 br2). cbn [flat_termP].
      rewrite atomize_texpP_tfmap. destruct (atomize_texpP v c) as [[c1 a1] n1]. reflexivity.
    - change (ftm (TERM_Switch v default_dest brs))
        with (TERM_Switch (ft' v) (@endo block_id _ default_dest) (@endo (list (tint_literal * block_id)) _ brs)).
      cbn [flat_termP].
      rewrite atomize_texpP_tfmap. destruct (atomize_texpP v c) as [[c1 a1] n1]. reflexivity.
  Qed.

  Notation fb := (@tfmap LLVMAst.block _ U V f).

  Lemma blk_code_fb b : blk_code (fb b) = fc (blk_code b).
  Proof. reflexivity. Qed.
  Lemma blk_term_fb b :
    blk_term (fb b) = let '(id, t, md) := blk_term b in (@endo instr_id _ id, ftm t, tfmap f md).
  Proof. reflexivity. Qed.

  Lemma flat_blockP_tfmap b c :
    flat_blockP (fb b) c = let '(b', n) := flat_blockP b c in (fb b', n).
  Proof.
    unfold flat_blockP. rewrite blk_code_fb, blk_term_fb.
    destruct (blk_term b) as [[tid tm] tmd].
    rewrite flat_codeP_tfmap. destruct (flat_codeP (blk_code b) c) as [cc n1].
    rewrite flat_termP_tfmap. destruct (flat_termP tm n1) as [[tc tm'] n2].
    cbv beta iota zeta. rewrite <- fc_app. reflexivity.
  Qed.

  Lemma flat_blocksP_tfmap bs c :
    flat_blocksP (map fb bs) c = let '(bs', n) := flat_blocksP bs c in (map fb bs', n).
  Proof.
    revert c; induction bs as [|b r IH]; intros c; [reflexivity|].
    cbn [map flat_blocksP]. rewrite flat_blockP_tfmap. destruct (flat_blockP b c) as [b' n1].
    rewrite IH. destruct (flat_blocksP r n1) as [rs n2]. reflexivity.
  Qed.

End TFmap.

(** ** The flattened, type-converted definitions seen by the semantics *)

Lemma cblock_tfmap (b : LLVMAst.block typ) : cblock b = tfmap cty b.
Proof. reflexivity. Qed.

Lemma flat_blockP_fst_snd {T : Set} (b : LLVMAst.block T) c :
  flat_blockP b c = (fst (flat_blockP b c), snd (flat_blockP b c)).
Proof. destruct (flat_blockP b c); reflexivity. Qed.

Lemma flat_blockP_id {T : Set} (b : LLVMAst.block T) c : blk_id (fst (flat_blockP b c)) = blk_id b.
Proof.
  unfold flat_blockP. destruct (flat_codeP (blk_code b) c) as [cc n1].
  destruct (blk_term b) as [[tid tm] tmd]. destruct (flat_termP tm n1) as [[tc tm'] n2]. reflexivity.
Qed.

Lemma flat_blockP_phis {T : Set} (b : LLVMAst.block T) c : blk_phis (fst (flat_blockP b c)) = blk_phis b.
Proof.
  unfold flat_blockP. destruct (flat_codeP (blk_code b) c) as [cc n1].
  destruct (blk_term b) as [[tid tm] tmd]. destruct (flat_termP tm n1) as [[tc tm'] n2]. reflexivity.
Qed.

(** ** Counter threading and block structure *)

(** Flattening [c1 ++ c2] at [c] is flattening [c1] at [c], then [c2] at the
    resulting counter. *)
Lemma flat_codeP_app {T : Set} (c1 c2 : code T) c :
  flat_codeP (c1 ++ c2)%list c =
  (fst (flat_codeP c1 c) ++ fst (flat_codeP c2 (snd (flat_codeP c1 c))),
   snd (flat_codeP c2 (snd (flat_codeP c1 c))))%list.
Proof.
  revert c. induction c1 as [|x r IH]; intros c; cbn.
  - destruct (flat_codeP c2 c); reflexivity.
  - destruct (flat_instrP x c) as [ci n1]. rewrite IH.
    destruct (flat_codeP r n1) as [cr n2]. cbn.
    destruct (flat_codeP c2 n2) as [cs n3]. cbn. rewrite app_assoc. reflexivity.
Qed.

Lemma flat_codeP_cons {T : Set} (x : instr_id * instr T * list (metadata T)) r c :
  flat_codeP (x :: r) c =
  (fst (flat_instrP x c) ++ fst (flat_codeP r (snd (flat_instrP x c))),
   snd (flat_codeP r (snd (flat_instrP x c))))%list.
Proof. cbn. destruct (flat_instrP x c) as [ci n1]. cbn [fst snd]. destruct (flat_codeP r n1). reflexivity. Qed.

(** The structure of a flattened block: same label, phis and comments; its
    code is the flattened code followed by the terminator's atomisation code;
    its terminator is the atomised terminator. *)
Lemma flat_blockP_spec {T : Set} (b : LLVMAst.block T) c :
  let '(cc, n1) := flat_codeP (blk_code b) c in
  let '(tc, tm', n2) := flat_termP (snd (fst (blk_term b))) n1 in
  flat_blockP b c =
  (mk_block (blk_id b) (blk_phis b) (cc ++ tc)%list (fst (fst (blk_term b)), tm', snd (blk_term b))
            (blk_comments b), n2).
Proof.
  unfold flat_blockP. destruct (flat_codeP (blk_code b) c) as [cc n1].
  destruct (blk_term b) as [[tid tm] tmd]. cbn [fst snd].
  destruct (flat_termP tm n1) as [[tc tm'] n2]. reflexivity.
Qed.

Lemma flat_blockP_code {T : Set} (b : LLVMAst.block T) c :
  blk_code (fst (flat_blockP b c)) =
  (fst (flat_codeP (blk_code b) c) ++
   fst (fst (flat_termP (snd (fst (blk_term b))) (snd (flat_codeP (blk_code b) c)))))%list.
Proof.
  pose proof (flat_blockP_spec b c) as H.
  destruct (flat_codeP (blk_code b) c) as [cc n1]. cbn [fst snd] in *. destruct (flat_termP _ n1) as [[tc tm'] n2].
  rewrite H. reflexivity.
Qed.

Lemma flat_blockP_term {T : Set} (b : LLVMAst.block T) c :
  blk_term (fst (flat_blockP b c)) =
  (fst (fst (blk_term b)),
   snd (fst (flat_termP (snd (fst (blk_term b))) (snd (flat_codeP (blk_code b) c)))),
   snd (blk_term b)).
Proof.
  pose proof (flat_blockP_spec b c) as H.
  destruct (flat_codeP (blk_code b) c) as [cc n1]. cbn [fst snd] in *. destruct (flat_termP _ n1) as [[tc tm'] n2].
  rewrite H. reflexivity.
Qed.

Lemma flat_blockP_comments {T : Set} (b : LLVMAst.block T) c :
  blk_comments (fst (flat_blockP b c)) = blk_comments b.
Proof.
  pose proof (flat_blockP_spec b c) as H.
  destruct (flat_codeP (blk_code b) c) as [cc n1]. cbn [fst snd] in *. destruct (flat_termP _ n1) as [[tc tm'] n2].
  rewrite H. reflexivity.
Qed.

(** Compositionality with [prepend_code]: flattening a block whose code is
    [x ++ blk_code b] flattens [x] first, then the block [b]. *)
Lemma flat_blockP_prepend {T : Set} (x : code T) (b : LLVMAst.block T) c :
  flat_blockP (mk_block (blk_id b) (blk_phis b) (x ++ blk_code b)%list (blk_term b) (blk_comments b)) c =
  (let fb := fst (flat_blockP b (snd (flat_codeP x c))) in
   mk_block (blk_id fb) (blk_phis fb) (fst (flat_codeP x c) ++ blk_code fb)%list (blk_term fb) (blk_comments fb),
   snd (flat_blockP b (snd (flat_codeP x c)))).
Proof.
  unfold flat_blockP at 1. cbn [blk_code blk_id blk_phis blk_term blk_comments].
  rewrite flat_codeP_app.
  pose proof (flat_blockP_spec b (snd (flat_codeP x c))) as H.
  destruct (flat_codeP x c) as [cx n0]. cbn [fst snd] in *.
  destruct (flat_codeP (blk_code b) n0) as [cc n1]. cbn [fst snd].
  destruct (blk_term b) as [[tid tm] tmd]. cbn [fst snd] in *.
  destruct (flat_termP tm n1) as [[tc tm'] n2]. rewrite H. cbn. rewrite app_assoc. reflexivity.
Qed.

Lemma atomize_argsP_atomic {T : Set} (args : list (texp T * list param_attr)) k :
  Forall (fun a => compound (snd (fst a)) = false) args -> atomize_argsP args k = ([], args, k).
Proof.
  induction 1 as [|[[t e] pa] r He Hr IH]; [reflexivity|].
  cbn in He. cbn [atomize_argsP atomize_texpP]. rewrite atomizeP_atomic by exact He. rewrite IH. reflexivity.
Qed.

(** A call whose callee and arguments are already atomic is left unchanged. *)
Lemma flat_instrP_call_atomic {T : Set} id dt (ef : exp T) args anns obs md c :
  compound ef = false -> Forall (fun a => compound (snd (fst a)) = false) args ->
  flat_instrP (id, INSTR_Call (dt, ef) args anns obs, md) c = ([(id, INSTR_Call (dt, ef) args anns obs, md)], c).
Proof.
  intros He Ha. cbn [flat_instrP atomize_texpP]. rewrite atomizeP_atomic by exact He.
  rewrite atomize_argsP_atomic by exact Ha. reflexivity.
Qed.


Lemma flat_blocksP_ids {T : Set} (bs : list (LLVMAst.block T)) c :
  map blk_id (fst (flat_blocksP bs c)) = map blk_id bs.
Proof.
  revert c; induction bs as [|b r IH]; intros c; cbn; [reflexivity|].
  pose proof (flat_blockP_id b c) as Hb. destruct (flat_blockP b c) as [b' n1].
  specialize (IH n1). destruct (flat_blocksP r n1) as [rs n2]. cbn in *. f_equal; assumption.
Qed.

(** [conv_def (flat_def d)] in terms of the [dtyp]-level flattener applied to
    the converted blocks: the semantics only ever sees
    [fst (flat_blockP (cblock b) c)]. *)
Lemma conv_def_flat_def (d : Ldef) :
  let entry := fst (df_instrs d) in
  let rest := snd (df_instrs d) in
  conv_def (flat_def d) =
  mk_definition (cdecl (df_prototype d)) (df_args d)
    {| CFG.init := blk_id entry;
       CFG.blks := fst (flat_blockP (cblock entry) 1%positive)
                   :: fst (flat_blocksP (map cblock rest) (snd (flat_blockP (cblock entry) 1%positive)));
       CFG.args := df_args d |}.
Proof.
  intros entry rest. unfold conv_def. rewrite flat_def_eq. cbn [df_prototype df_args df_instrs fst snd].
  fold entry rest. rewrite flat_block_eq, flat_blocks_eq.
  rewrite !cblock_tfmap. change (map cblock rest) with (map (tfmap cty) rest). rewrite flat_blockP_tfmap.
  rewrite (flat_blockP_fst_snd entry). cbn [fst snd].
  rewrite flat_blocksP_tfmap. destruct (flat_blocksP rest _) as [rs n2]. cbn [fst snd map].
  rewrite flat_blockP_id. f_equal.
Qed.

(* ================================================================== *)
(** * Part 2: semantic transport (on [dtyp] code) *)

(* NB: an imported file sets [Implicit Arguments] globally; keep arguments explicit here. *)
Unset Implicit Arguments.

(** ** Generic ITree facts *)

Lemma eutt_Ret_inv_l {E R1 R2} (RR : R1 -> R2 -> Prop) (r1 : R1) (t2 : itree E R2) :
  eutt RR (Ret r1) t2 -> exists r2, t2 ≈ Ret r2 /\ RR r1 r2.
Proof.
  intros H. punfold H. red in H. cbn in H.
  cut (exists r2, go (observe t2) ≈ Ret r2 /\ RR r1 r2).
  { intros [r2 [H1 H2]]. exists r2. split; [|assumption]. rewrite (itree_eta t2). exact H1. }
  remember (observe t2) as ot2. clear Heqot2 t2.
  remember (RetF r1) as ot1.
  induction H; try discriminate.
  - inversion Heqot1; subst. exists r2. split; [reflexivity|assumption].
  - subst. destruct (IHeqitF eq_refl) as [r2 [H1 H2]]. exists r2. split; [|assumption].
    rewrite tau_eutt. rewrite (itree_eta t2). exact H1.
Qed.

Lemma eutt_Vis_inv_l {E R1 R2} (RR : R1 -> R2 -> Prop) {X} (e : E X) (k1 : X -> itree E R1) (t2 : itree E R2) :
  eutt RR (Vis e k1) t2 -> exists k2, t2 ≈ Vis e k2.
Proof.
  intros H. punfold H. red in H. cbn in H.
  cut (exists k2, go (observe t2) ≈ Vis e k2).
  { intros [k2 H1]. exists k2. rewrite (itree_eta t2). exact H1. }
  remember (observe t2) as ot2. clear Heqot2 t2.
  remember (VisF e k1) as ot1.
  induction H; try discriminate.
  - match goal with
    | Heq : VisF ?e0 ?k0 = VisF e k1, REL : forall v, _ |- exists _, go (VisF ?e0 ?k3) ≈ _ =>
        assert (HV : eqitF RR true true id (upaco2 (eqit_ RR true true id) bot2) (VisF e k1) (VisF e0 k3))
          by (rewrite <- Heq; constructor; exact REL)
    end.
    apply eqitF_inv_VisF_weak in HV. destruct HV as [p [He Hk]]. destruct p. cbn in He. subst.
    eexists. reflexivity.
  - subst. destruct (IHeqitF eq_refl) as [k2 H1]. exists k2.
    rewrite tau_eutt. rewrite (itree_eta t2). exact H1.
Qed.

Lemma vis_void_eutt {E R1 R2} (RR : R1 -> R2 -> Prop) {X} (e : E X) (k1 : X -> itree E R1) (k2 : X -> itree E R2) :
  (X -> False) -> eutt RR (Vis e k1) (Vis e k2).
Proof. intros HX. apply eqit_Vis. intros u. destruct (HX u). Qed.

(** ** Names *)

Definition is_flat (r : raw_id) : bool :=
  match r with Raw (Zneg (xO (xI _))) => true | _ => false end.

Lemma is_flat_flat_id c : is_flat (flat_id c) = true.
Proof. reflexivity. Qed.
Lemma is_flat_pos x : is_flat (Raw (Zpos x)) = false.
Proof. reflexivity. Qed.
Lemma is_flat_ntmp s k : is_flat (ntmp s k) = false.
Proof. reflexivity. Qed.
Lemma is_flat_ssname s k : is_flat (ssname s k) = false.
Proof. reflexivity. Qed.
Lemma is_flat_Name s : is_flat (Name s) = false.
Proof. reflexivity. Qed.
Lemma is_flat_Anon z : is_flat (Anon z) = false.
Proof. reflexivity. Qed.
Lemma is_flat_true r : is_flat r = true -> exists c, r = flat_id c.
Proof.
  unfold is_flat. destruct r as [s|z|z]; try discriminate.
  destruct z as [|p|p]; try discriminate. destruct p as [p|p|]; try discriminate.
  destruct p as [p|p|]; try discriminate. intros _. exists p. reflexivity.
Qed.
Lemma flat_id_inj c c' : flat_id c = flat_id c' -> c = c'.
Proof. unfold flat_id. intros H. injection H. auto. Qed.

Definition flat_in (lo hi : positive) (r : raw_id) : Prop :=
  exists k, r = flat_id k /\ (lo <= k < hi)%positive.

Lemma flat_in_noflat lo hi r : is_flat r = false -> ~ flat_in lo hi r.
Proof. intros H [k [-> _]]. rewrite is_flat_flat_id in H. discriminate. Qed.
Lemma flat_in_out lo hi k : ~ (lo <= k < hi)%positive -> ~ flat_in lo hi (flat_id k).
Proof. intros H [k' [E Hk]]. apply flat_id_inj in E. subst. auto. Qed.
Lemma flat_in_mono lo hi lo' hi' r :
  (lo <= lo')%positive -> (hi' <= hi)%positive -> flat_in lo' hi' r -> flat_in lo hi r.
Proof. intros H1 H2 [k [-> Hk]]. exists k. split; [reflexivity|lia]. Qed.
Lemma flat_in_dec lo hi r : flat_in lo hi r \/ ~ flat_in lo hi r.
Proof.
  destruct (is_flat r) eqn:E.
  - apply is_flat_true in E as [k ->].
    destruct (Pos.leb lo k) eqn:E1; destruct (Pos.ltb k hi) eqn:E2;
      try (left; exists k; split; [reflexivity|lia]);
      right; apply flat_in_out; lia.
  - right. apply flat_in_noflat, E.
Qed.

(** ** Frames agreeing outside the fresh names [flat_id k], [lo <= k < hi] *)

Definition agree_except (lo hi : positive) (sf sf' : stack_frame) : Prop :=
  stack_exc sf' = stack_exc sf /\ stack_loc sf' = stack_loc sf /\
  forall r, ~ flat_in lo hi r -> RM.find r (stack_vars sf') = RM.find r (stack_vars sf).

Lemma agree_except_refl lo hi sf : agree_except lo hi sf sf.
Proof. split; [|split]; reflexivity. Qed.

Lemma agree_except_mono lo hi lo' hi' sf sf' :
  (lo <= lo')%positive -> (hi' <= hi)%positive ->
  agree_except lo' hi' sf sf' -> agree_except lo hi sf sf'.
Proof.
  intros H1 H2 (A & B & C). split; [|split]; auto.
  intros r Hr. apply C. intros Hr'. apply Hr. eapply (@flat_in_mono lo hi lo' hi'); auto.
Qed.

Lemma agree_except_trans lo1 hi1 lo2 hi2 lo hi sf sf' sf'' :
  (lo <= lo1)%positive -> (hi1 <= hi)%positive -> (lo <= lo2)%positive -> (hi2 <= hi)%positive ->
  agree_except lo1 hi1 sf sf' -> agree_except lo2 hi2 sf' sf'' -> agree_except lo hi sf sf''.
Proof.
  intros ? ? ? ? (A1 & B1 & C1) (A2 & B2 & C2). split; [|split]; [congruence|congruence|].
  intros r Hr.
  assert (Hr1 : ~ flat_in lo1 hi1 r) by (intros Hr'; apply Hr; eapply (@flat_in_mono lo hi lo1 hi1); auto).
  assert (Hr2 : ~ flat_in lo2 hi2 r) by (intros Hr'; apply Hr; eapply (@flat_in_mono lo hi lo2 hi2); auto).
  rewrite (C2 r Hr2), (C1 r Hr1). reflexivity.
Qed.

Lemma agree_except_noflat lo hi sf sf' r :
  agree_except lo hi sf sf' -> is_flat r = false ->
  RM.find r (stack_vars sf') = RM.find r (stack_vars sf).
Proof. intros (_ & _ & C) H. apply C, flat_in_noflat, H. Qed.

Lemma agree_except_out lo hi sf sf' k :
  agree_except lo hi sf sf' -> ~ (lo <= k < hi)%positive ->
  RM.find (flat_id k) (stack_vars sf') = RM.find (flat_id k) (stack_vars sf).
Proof. intros (_ & _ & C) H. apply C, flat_in_out, H. Qed.

Lemma find_add_eq {V} r (v : V) m : RM.find r (RM.add r v m) = Some v.
Proof. apply RMF.F.add_eq_o. reflexivity. Qed.
Lemma find_add_neq {V} r r' (v : V) m : r <> r' -> RM.find r' (RM.add r v m) = RM.find r' m.
Proof. intros H. apply RMF.F.add_neq_o. exact H. Qed.

(** The frame after [LocalWrite r v] (see [interp_mcfg_lwrite]). *)
Definition upd_add (sf : stack_frame) (r : raw_id) (v : dvalue) : stack_frame :=
  upd_local_sf sf (RM.add r v (stack_vars sf)).

Lemma upd_add_eq sf r v : upd_local_sf sf (Maps.add r v (stack_vars sf)) = upd_add sf r v.
Proof. reflexivity. Qed.

Lemma agree_except_add lo hi sf sf' r v :
  ~ flat_in lo hi r -> agree_except lo hi sf sf' ->
  agree_except lo hi (upd_add sf r v) (upd_add sf' r v).
Proof.
  intros Hr (A & B & C). split; [exact A|split; [exact B|]]. intros r' Hr'. unfold upd_add; cbn [stack_vars upd_local_sf].
  destruct (RawIDOrd.eq_dec r r') as [<-|Hne].
  - rewrite !find_add_eq. reflexivity.
  - rewrite !find_add_neq by exact Hne. apply C, Hr'.
Qed.

Lemma agree_except_add_flat lo hi sf sf' k v :
  (lo <= k < hi)%positive -> agree_except lo hi sf sf' ->
  agree_except lo hi sf (upd_add sf' (flat_id k) v).
Proof.
  intros Hk (A & B & C). split; [exact A|split; [exact B|]]. intros r Hr. unfold upd_add; cbn [stack_vars upd_local_sf].
  rewrite find_add_neq; [apply C, Hr|]. intros E. apply Hr. exists k. split; [symmetry; exact E|exact Hk].
Qed.

Lemma find_upd_add_eq sf r v : RM.find r (stack_vars (upd_add sf r v)) = Some v.
Proof. unfold upd_add; cbn [stack_vars upd_local_sf]. apply find_add_eq. Qed.
Lemma find_upd_add_neq sf r r' v : r <> r' -> RM.find r' (stack_vars (upd_add sf r v)) = RM.find r' (stack_vars sf).
Proof. unfold upd_add; cbn [stack_vars upd_local_sf]. apply find_add_neq. Qed.

(** ** Relating results of two runs *)

Definition RR {X} (P : stack_frame -> stack_frame -> Prop) (r1 r2 : Res X) : Prop :=
  let '((st1, ((sf1, stk1), g1)), x1) := r1 in
  let '((st2, ((sf2, stk2), g2)), x2) := r2 in
  st1 = st2 /\ stk1 = stk2 /\ g1 = g2 /\ x1 = x2 /\ P sf1 sf2.

Definition res_mod (lo hi : positive) {X} : Res X -> Res X -> Prop := RR (agree_except lo hi).

Lemma RR_intro {X} P st sf sf' stk g (x : X) :
  P sf sf' -> RR P ((st, ((sf, stk), g)), x) ((st, ((sf', stk), g)), x).
Proof. intros H. cbn. auto. Qed.

(** ** Absorbing computations (errors, UB, out-of-memory) *)

Definition absorbs {R} (t : MCFGbot R) : Prop :=
  exists X (e : MCFGEbot X) (k : X -> MCFGbot R), (X -> False) /\ t ≈ Vis e k.

(** The same absorbing event from every state. *)
Definition absorbs_uniform {R} (f : FusedS -> MCFGbot R) : Prop :=
  exists X (e : MCFGEbot X), (X -> False) /\ forall s, exists k, f s ≈ Vis e k.

#[global] Instance absorbs_proper {R} : Proper (eutt eq ==> iff) (@absorbs R).
Proof.
  intros t t' Ht. unfold absorbs. split; intros (X & e & k & HX & H); exists X, e, k; split; auto.
  - rewrite <- Ht. exact H.
  - rewrite Ht. exact H.
Qed.

#[global] Instance ends_in_oom_proper {R} : Proper (eutt eq ==> iff) (@ends_in_oom R).
Proof.
  intros t t' Ht. unfold ends_in_oom. split; intros (k & H); exists k.
  - rewrite <- Ht. exact H.
  - rewrite Ht. exact H.
Qed.

Lemma absorbs_uniform_absorbs {R} (f : FusedS -> MCFGbot R) s : absorbs_uniform f -> absorbs (f s).
Proof. intros (X & e & HX & H). destruct (H s) as [k Hk]. exists X, e, k. auto. Qed.

Lemma absorbs_bind {R S} (t : MCFGbot R) (k : R -> MCFGbot S) :
  absorbs t -> absorbs (ITree.bind t k).
Proof.
  intros (X & e & k0 & HX & Ht). exists X, e, (fun x => ITree.bind (k0 x) k). split; [exact HX|].
  rewrite Ht, bind_vis. reflexivity.
Qed.

Lemma absorbs_not_ret {R} (t : MCFGbot R) r : absorbs t -> t ≈ Ret r -> False.
Proof.
  intros (X & e & k0 & HX & Ht) Hr. rewrite Ht in Hr. apply eqit_inv in Hr. cbn in Hr. exact Hr.
Qed.

Lemma absorbs_uniform_eutt {R1 R2} (RR : R1 -> R2 -> Prop) f1 f2 s1 s2 :
  absorbs_uniform f1 -> absorbs_uniform f2 ->
  (exists X (e : MCFGEbot X) k1 k2, f1 s1 ≈ Vis e k1 /\ f2 s2 ≈ Vis e k2) -> eutt RR (f1 s1) (f2 s2).
Proof.
  intros (X & e & HX & Ht) _ (X' & e' & k1 & k2 & H1 & H2).
  rewrite H1, H2. apply eqit_Vis. intros u.
  destruct (Ht s1) as [k Hk]. rewrite H1 in Hk. apply eqit_inv in Hk. cbn in Hk.
  destruct Hk as [p _]. destruct p. destruct (HX u).
Qed.

Lemma oom_absorbs {R} (t : MCFGbot R) : ends_in_oom t -> absorbs t.
Proof. intros [k H]. eexists _, _, _. split; [|exact H]. exact (fun x : void => match x with end). Qed.

Lemma oom_eutt {R1 R2} (RR : R1 -> R2 -> Prop) (t1 : MCFGbot R1) (t2 : MCFGbot R2) :
  ends_in_oom t1 -> eutt RR t1 t2 -> ends_in_oom t2.
Proof.
  intros [k H] He. rewrite H in He. apply eutt_Vis_inv_l in He as [k2 H2]. exists k2. exact H2.
Qed.

Lemma ret_eutt {R1 R2} (RR : R1 -> R2 -> Prop) (t1 : MCFGbot R1) (t2 : MCFGbot R2) r1 :
  t1 ≈ Ret r1 -> eutt RR t1 t2 -> exists r2, t2 ≈ Ret r2 /\ RR r1 r2.
Proof. intros H He. rewrite H in He. apply eutt_Ret_inv_l. exact He. Qed.

(** ** [interp_mcfg] on the events of call-free code *)

Lemma interp_mcfg_raise_u {X} msg : absorbs_uniform (fun s => interp_mcfg (@raise MCFGEtop X _ msg) s).
Proof.
  exists void. eexists. split; [exact (fun x => match x with end)|]. intros s. eexists.
  unfold raise, trigger_cast'. unfold interp_mcfg.
  rewrite interp_intrinsics_bind, interp_intrinsics_trigger. cbn. unfold F_trigger.
  rewrite interp_state_bind, interp_state_trigger. cbn.
  rewrite bind_trigger, bind_vis. reflexivity.
Qed.

Lemma interp_mcfg_raiseUB_u {X} msg : absorbs_uniform (fun s => interp_mcfg (@raiseUB MCFGEtop _ X msg) s).
Proof.
  exists void. eexists. split; [exact (fun x => match x with end)|]. intros s. eexists.
  unfold raiseUB, trigger_cast'. unfold interp_mcfg.
  rewrite interp_intrinsics_bind, interp_intrinsics_trigger. cbn. unfold F_trigger.
  rewrite interp_state_bind, interp_state_trigger. cbn.
  rewrite bind_trigger, bind_vis. reflexivity.
Qed.

Lemma interp_mcfg_raiseOOM {X} msg s : ends_in_oom (interp_mcfg (@raiseOOM MCFGEtop _ X msg) s).
Proof.
  unfold raiseOOM, trigger_cast'. unfold interp_mcfg.
  rewrite interp_intrinsics_bind, interp_intrinsics_trigger. cbn. unfold F_trigger.
  rewrite interp_state_bind, interp_state_trigger. cbn.
  rewrite bind_trigger, bind_vis. eexists. reflexivity.
Qed.

Lemma interp_mcfg_raiseOOM_u {X} msg : absorbs_uniform (fun s => interp_mcfg (@raiseOOM MCFGEtop _ X msg) s).
Proof.
  exists void. eexists. split; [exact (fun x => match x with end)|]. intros s. eexists.
  unfold raiseOOM, trigger_cast'. unfold interp_mcfg.
  rewrite interp_intrinsics_bind, interp_intrinsics_trigger. cbn. unfold F_trigger.
  rewrite interp_state_bind, interp_state_trigger. cbn.
  rewrite bind_trigger, bind_vis. reflexivity.
Qed.

Lemma interp_mcfg_mem {X} (e : MemoryE X) st rest :
  interp_mcfg (ITree.trigger (subevent _ e)) (st, rest)
  ≈ ITree.bind (memM_interp (handle_memoryM e) st) (fun '(st', x) => Ret ((st', rest), x)).
Proof.
  unfold interp_mcfg. rewrite interp_intrinsics_trigger. cbn. unfold F_trigger.
  rewrite interp_state_trigger. cbn. unfold on_mem, handle_memory.
  apply eutt_eq_bind. intros [st' x]. reflexivity.
Qed.

Lemma interp_mcfg_draw dt s :
  interp_mcfg (ITree.trigger (subevent _ (Draw dt))) s
  ≈ ITree.bind (EOU_to_itree (default_dvalue_of_dtyp dt)) (fun x => Ret (s, x)).
Proof.
  unfold interp_mcfg. rewrite interp_intrinsics_trigger. cbn. unfold F_trigger.
  rewrite interp_state_trigger. cbn. reflexivity.
Qed.

Lemma interp_mcfg_lread_none_u id :
  exists X (e : MCFGEbot X), (X -> False) /\
  forall st sf stk g, RM.find id (stack_vars sf) = None ->
    exists k, interp_mcfg (ITree.trigger (subevent _ (LocalRead id))) (st, ((sf, stk), g)) ≈ Vis e k.
Proof.
  exists void. eexists. split; [exact (fun x => match x with end)|].
  intros st sf stk g Hl. eexists.
  unfold interp_mcfg. rewrite interp_intrinsics_trigger. cbn. unfold F_trigger.
  rewrite interp_state_trigger. cbn. unfold on_ls, handle_local_stack, handle_local_debug.
  cbn. rewrite Hl. unfold raise, trigger_cast'. rewrite bind_trigger, !bind_vis.
  reflexivity.
Qed.

Lemma interp_mcfg_gread_none_u id :
  exists X (e : MCFGEbot X), (X -> False) /\
  forall st ls g, RM.find id g = None ->
    exists k, interp_mcfg (ITree.trigger (subevent _ (GlobalRead id))) (st, (ls, g)) ≈ Vis e k.
Proof.
  exists void. eexists. split; [exact (fun x => match x with end)|].
  intros st ls g Hl. eexists.
  unfold interp_mcfg. rewrite interp_intrinsics_trigger. cbn. unfold F_trigger.
  rewrite interp_state_trigger. cbn. unfold on_genv, handle_global_debug.
  cbn. rewrite Hl. unfold raise, trigger_cast'. rewrite bind_trigger, !bind_vis.
  reflexivity.
Qed.

Lemma eutt_vis_void {R1 R2} (RR : R1 -> R2 -> Prop) {X} (e : MCFGEbot X)
      (t1 : MCFGbot R1) (t2 : MCFGbot R2) k1 k2 :
  (X -> False) -> t1 ≈ Vis e k1 -> t2 ≈ Vis e k2 -> eutt RR t1 t2.
Proof. intros HX H1 H2. rewrite H1, H2. apply vis_void_eutt, HX. Qed.

(** ** Running call-free code under the call knot *)

Section Sem.
  Variable ctx : CallE ~> itree (CallE +' MCFGEtop).
  Variable va : option ptr.

  Definition run {R} (t : CFGtop R) (s : FusedS) : MCFGbot (Res R) :=
    interp_mcfg (interp_mrec ctx t) s.

  #[global] Instance interp_mrec_ctx_proper {R} :
    Proper (eutt eq ==> eutt eq) (fun t : itree (CallE +' MCFGEtop) R => interp_mrec ctx t).
  Proof. intros t t' Ht. eapply Proper_interp_mrec; [intros ? ?; reflexivity | exact Ht]. Qed.

  #[global] Instance run_proper {R} : Proper (eutt eq ==> eq ==> eutt eq) (@run R).
  Proof.
    intros t t' Ht s s' <-. unfold run.
    apply interp_mcfg_proper; [|reflexivity]. apply interp_mrec_ctx_proper, Ht.
  Qed.

  Lemma run_ret {R} (r : R) s : run (Ret r) s ≈ Ret (s, r).
  Proof. unfold run. rewrite interp_mrec_ret. apply interp_mcfg_ret. Qed.

  Lemma run_bind {R S} (t : CFGtop R) (k : R -> CFGtop S) s :
    run (ITree.bind t k) s ≈ ITree.bind (run t s) (fun '(s', r) => run (k r) s').
  Proof. unfold run. rewrite interp_mrec_bind'. apply interp_mcfg_bind. Qed.

  Lemma run_event {X} (e : MCFGEtop X) s :
    run (ITree.trigger (inr1 e)) s ≈ interp_mcfg (ITree.trigger e) s.
  Proof. unfold run. rewrite interp_mrec_event. reflexivity. Qed.

  Lemma run_lift_top {R} (t : MCFGtop R) s : run (lift_top t) s ≈ interp_mcfg t s.
  Proof. unfold run. rewrite interp_mrec_lift_top. reflexivity. Qed.

  Lemma denote_exp'_lift t e : denote_exp' t e = lift_top (denote_exp t e).
  Proof. reflexivity. Qed.

  Lemma run_exp' st sf stk g t e v :
    exp_eval st sf stk g t e v ->
    run (denote_exp' t e) (st, ((sf, stk), g)) ≈ Ret ((st, ((sf, stk), g)), v).
  Proof. intros H. rewrite denote_exp'_lift, run_lift_top. exact H. Qed.

  (** The [CFGEtop] injections of the events of call-free code. *)
  Lemma sub_local X (e : LocalE X) :
    (@subevent LocalE CFGEtop _ X e) = inr1 (@subevent LocalE MCFGEtop _ X e).
  Proof. reflexivity. Qed.
  Lemma sub_global X (e : GlobalE X) :
    (@subevent GlobalE CFGEtop _ X e) = inr1 (@subevent GlobalE MCFGEtop _ X e).
  Proof. reflexivity. Qed.
  Lemma sub_mem X (e : MemoryE X) :
    (@subevent MemoryE CFGEtop _ X e) = inr1 (@subevent MemoryE MCFGEtop _ X e).
  Proof. reflexivity. Qed.
  Lemma sub_draw X (e : DrawE X) :
    (@subevent DrawE CFGEtop _ X e) = inr1 (@subevent DrawE MCFGEtop _ X e).
  Proof. reflexivity. Qed.
  Lemma sub_ub X (e : UBE X) :
    (@subevent UBE CFGEtop _ X e) = inr1 (@subevent UBE MCFGEtop _ X e).
  Proof. reflexivity. Qed.
  Lemma sub_fail X (e : FailureE X) :
    (@subevent FailureE CFGEtop _ X e) = inr1 (@subevent FailureE MCFGEtop _ X e).
  Proof. reflexivity. Qed.
  Lemma sub_oom X (e : OOME X) :
    (@subevent OOME CFGEtop _ X e) = inr1 (@subevent OOME MCFGEtop _ X e).
  Proof. reflexivity. Qed.

  Lemma run_lwrite id v st sf stk g :
    run (lwrite id v) (st, ((sf, stk), g)) ≈ Ret ((st, ((upd_add sf id v, stk), g)), tt).
  Proof. unfold lwrite. rewrite sub_local, run_event, interp_mcfg_lwrite, upd_add_eq. reflexivity. Qed.

  Lemma run_raise_u {X} msg : absorbs_uniform (fun s => run (@raise CFGEtop X _ msg) s).
  Proof.
    destruct (@interp_mcfg_raise_u X msg) as (Y & e & HY & H). exists Y, e. split; [exact HY|].
    intros s. destruct (H s) as [k Hk]. exists k. rewrite <- Hk.
    unfold raise, trigger_cast'. unfold run. rewrite interp_mrec_bind'. rewrite sub_fail, interp_mrec_event.
    apply interp_mcfg_proper; [|reflexivity]. apply eutt_eq_bind. intros [].
  Qed.

  Lemma run_raiseUB_u {X} msg : absorbs_uniform (fun s => run (@raiseUB CFGEtop _ X msg) s).
  Proof.
    destruct (@interp_mcfg_raiseUB_u X msg) as (Y & e & HY & H). exists Y, e. split; [exact HY|].
    intros s. destruct (H s) as [k Hk]. exists k. rewrite <- Hk.
    unfold raiseUB, trigger_cast'. unfold run. rewrite interp_mrec_bind'. rewrite sub_ub, interp_mrec_event.
    apply interp_mcfg_proper; [|reflexivity]. apply eutt_eq_bind. intros [].
  Qed.

  Lemma run_raiseOOM_u {X} msg : absorbs_uniform (fun s => run (@raiseOOM CFGEtop _ X msg) s).
  Proof.
    destruct (@interp_mcfg_raiseOOM_u X msg) as (Y & e & HY & H). exists Y, e. split; [exact HY|].
    intros s. destruct (H s) as [k Hk]. exists k. rewrite <- Hk.
    unfold raiseOOM, trigger_cast'. unfold run. rewrite interp_mrec_bind'. rewrite sub_oom, interp_mrec_event.
    apply interp_mcfg_proper; [|reflexivity]. apply eutt_eq_bind. intros [].
  Qed.

  (* ---------------------------------------------------------------- *)
  (** ** Frame-insensitivity: the same computation from two frames related by [P] *)

  Definition simM {R} (P : stack_frame -> stack_frame -> Prop) (t : MCFGtop R) : Prop :=
    forall st sf sf' stk g, P sf sf' ->
      eutt (RR P) (interp_mcfg t (st, ((sf, stk), g))) (interp_mcfg t (st, ((sf', stk), g))).

  Definition sim {R} (P : stack_frame -> stack_frame -> Prop) (t : CFGtop R) : Prop :=
    forall st sf sf' stk g, P sf sf' ->
      eutt (RR P) (run t (st, ((sf, stk), g))) (run t (st, ((sf', stk), g))).

  Lemma simM_eutt {R} P (t t' : MCFGtop R) : t ≈ t' -> simM P t -> simM P t'.
  Proof. intros E H st sf sf' stk g HP. rewrite <- E. apply H, HP. Qed.
  Lemma sim_eutt {R} P (t t' : CFGtop R) : t ≈ t' -> sim P t -> sim P t'.
  Proof. intros E H st sf sf' stk g HP. rewrite <- E. apply H, HP. Qed.

  Lemma simM_ret {R} P (r : R) : simM P (Ret r).
  Proof. intros st sf sf' stk g HP. rewrite !interp_mcfg_ret. apply eqit_Ret, RR_intro, HP. Qed.
  Lemma sim_ret {R} P (r : R) : sim P (Ret r).
  Proof. intros st sf sf' stk g HP. rewrite !run_ret. apply eqit_Ret, RR_intro, HP. Qed.

  Lemma RR_inv {X} P (r1 r2 : Res X) (Q : Prop) :
    RR P r1 r2 ->
    (forall st sf sf' stk g x, P sf sf' -> r1 = ((st, ((sf, stk), g)), x) -> r2 = ((st, ((sf', stk), g)), x) -> Q) ->
    Q.
  Proof.
    destruct r1 as [[st1 [[sf1 stk1] g1]] x1], r2 as [[st2 [[sf2 stk2] g2]] x2].
    intros (-> & -> & -> & -> & HP) H. eapply H; eauto.
  Qed.

  Lemma simM_bind {R S} P (t : MCFGtop R) (k : R -> MCFGtop S) :
    simM P t -> (forall x, simM P (k x)) -> simM P (ITree.bind t k).
  Proof.
    intros Ht Hk st sf sf' stk g HP. rewrite !interp_mcfg_bind.
    eapply eutt_clo_bind; [apply Ht, HP|].
    intros r1 r2 HR. eapply RR_inv; [exact HR|]. intros ? ? ? ? ? ? HP' -> ->. apply Hk, HP'.
  Qed.
  Lemma sim_bind {R S} P (t : CFGtop R) (k : R -> CFGtop S) :
    sim P t -> (forall x, sim P (k x)) -> sim P (ITree.bind t k).
  Proof.
    intros Ht Hk st sf sf' stk g HP. rewrite !run_bind.
    eapply eutt_clo_bind; [apply Ht, HP|].
    intros r1 r2 HR. eapply RR_inv; [exact HR|]. intros ? ? ? ? ? ? HP' -> ->. apply Hk, HP'.
  Qed.

  Lemma simM_absorbs {R} P (t : MCFGtop R) :
    absorbs_uniform (fun s => interp_mcfg t s) -> simM P t.
  Proof.
    intros H st sf sf' stk g HP. pose proof H as (X & e & HX & Ht).
    eapply (absorbs_uniform_eutt _ (fun s => interp_mcfg t s) (fun s => interp_mcfg t s)); auto.
    destruct (Ht (st, ((sf, stk), g))) as [k1 H1]. destruct (Ht (st, ((sf', stk), g))) as [k2 H2].
    eauto 6.
  Qed.
  Lemma sim_absorbs {R} P (t : CFGtop R) :
    absorbs_uniform (fun s => run t s) -> sim P t.
  Proof.
    intros H st sf sf' stk g HP. pose proof H as (X & e & HX & Ht).
    eapply (absorbs_uniform_eutt _ (fun s => run t s) (fun s => run t s)); auto.
    destruct (Ht (st, ((sf, stk), g))) as [k1 H1]. destruct (Ht (st, ((sf', stk), g))) as [k2 H2].
    eauto 6.
  Qed.

  Lemma simM_raise {X} P msg : simM P (@raise MCFGEtop X _ msg).
  Proof. apply simM_absorbs, interp_mcfg_raise_u. Qed.
  Lemma simM_raiseUB {X} P msg : simM P (@raiseUB MCFGEtop _ X msg).
  Proof. apply simM_absorbs, interp_mcfg_raiseUB_u. Qed.
  Lemma simM_raiseOOM {X} P msg : simM P (@raiseOOM MCFGEtop _ X msg).
  Proof. apply simM_absorbs, interp_mcfg_raiseOOM_u. Qed.
  Lemma sim_raise {X} P msg : sim P (@raise CFGEtop X _ msg).
  Proof. apply sim_absorbs, run_raise_u. Qed.
  Lemma sim_raiseUB {X} P msg : sim P (@raiseUB CFGEtop _ X msg).
  Proof. apply sim_absorbs, run_raiseUB_u. Qed.
  Lemma sim_raiseOOM {X} P msg : sim P (@raiseOOM CFGEtop _ X msg).
  Proof. apply sim_absorbs, run_raiseOOM_u. Qed.

  Lemma simM_lift {X} P (m : @EOU.EOU X) : simM P (EOU_to_itree m).
  Proof.
    destruct m; cbn.
    - apply simM_raise. - apply simM_raiseOOM. - apply simM_raiseUB. - apply simM_ret.
  Qed.
  Lemma sim_lift {X} P (m : @EOU.EOU X) : sim P (EOU_to_itree m).
  Proof.
    destruct m; cbn.
    - apply sim_raise. - apply sim_raiseOOM. - apply sim_raiseUB. - apply sim_ret.
  Qed.

  Lemma sim_of_simM {R} P (t : MCFGtop R) : simM P t -> sim P (lift_top t).
  Proof. intros H st sf sf' stk g HP. rewrite !run_lift_top. apply H, HP. Qed.

  Lemma sim_event {X} P (e : MCFGEtop X) :
    simM P (ITree.trigger e) -> sim P (ITree.trigger (inr1 e)).
  Proof. intros H st sf sf' stk g HP. rewrite !run_event. apply H, HP. Qed.

  Lemma simM_lread P id :
    (forall a b, P a b -> RM.find id (stack_vars a) = RM.find id (stack_vars b)) ->
    simM P (lread id).
  Proof.
    intros Hag st sf sf' stk g HP. pose proof (Hag _ _ HP) as E. unfold lread.
    destruct (RM.find id (stack_vars sf)) as [v|] eqn:E1.
    - rewrite interp_mcfg_lread by exact E1. rewrite interp_mcfg_lread by (rewrite <- E; reflexivity).
      rewrite !upd_local_sf_id. apply eqit_Ret, RR_intro, HP.
    - destruct (interp_mcfg_lread_none_u id) as (X & e & HX & H).
      destruct (H st sf stk g E1) as [k1 H1]. destruct (H st sf' stk g ltac:(rewrite <- E; reflexivity)) as [k2 H2].
      eapply eutt_vis_void; eauto.
  Qed.

  Lemma simM_gread P id : simM P (gread id).
  Proof.
    intros st sf sf' stk g HP. unfold gread.
    destruct (RM.find id g) as [v|] eqn:E1.
    - rewrite !interp_mcfg_gread by exact E1. apply eqit_Ret, RR_intro, HP.
    - destruct (interp_mcfg_gread_none_u id) as (X & e & HX & H).
      destruct (H st (sf, stk) g E1) as [k1 H1]. destruct (H st (sf', stk) g E1) as [k2 H2].
      eapply eutt_vis_void; eauto.
  Qed.

  Lemma simM_lwrite P id v :
    (forall a b, P a b -> P (upd_add a id v) (upd_add b id v)) ->
    simM P (lwrite id v).
  Proof.
    intros Hw st sf sf' stk g HP. unfold lwrite. rewrite !interp_mcfg_lwrite, !upd_add_eq.
    apply eqit_Ret, RR_intro, Hw, HP.
  Qed.

  Lemma simM_mem {X} P (e : MemoryE X) : simM P (ITree.trigger (subevent _ e)).
  Proof.
    intros st sf sf' stk g HP. rewrite !interp_mcfg_mem.
    eapply eutt_clo_bind with (UU := eq); [reflexivity|].
    intros [st1 x] ? <-. apply eqit_Ret, RR_intro, HP.
  Qed.

  Lemma simM_draw P dt : simM P (draw dt).
  Proof.
    intros st sf sf' stk g HP. unfold draw. rewrite !interp_mcfg_draw.
    eapply eutt_clo_bind with (UU := eq); [reflexivity|].
    intros x ? <-. apply eqit_Ret, RR_intro, HP.
  Qed.

  Lemma simM_map_monad {A B} P (f : A -> MCFGtop B) (l : list A) :
    Forall (fun x => simM P (f x)) l -> simM P (map_monad f l).
  Proof.
    induction 1 as [|a l Ha Hl IH].
    - cbn. apply simM_ret.
    - cbn [map_monad bind Monad_itree ret]. apply simM_bind; [exact Ha|]. intros b.
      apply simM_bind; [exact IH|]. intros bs. apply simM_ret.
  Qed.
  Lemma sim_map_monad {A B} P (f : A -> CFGtop B) (l : list A) :
    Forall (fun x => sim P (f x)) l -> sim P (map_monad f l).
  Proof.
    induction 1 as [|a l Ha Hl IH].
    - cbn. apply sim_ret.
    - cbn [map_monad bind Monad_itree ret]. apply sim_bind; [exact Ha|]. intros b.
      apply sim_bind; [exact IH|]. intros bs. apply sim_ret.
  Qed.

  Lemma simM_freeze P v : simM P (freeze v : MCFGtop dvalue).
  Proof.
    induction v using dvalue_ind.
    - cbn [freeze freeze_base]. destruct dv; cbn.
      all: try (unfold ITree.map; apply simM_bind; [apply simM_ret|intros; apply simM_ret]).
      apply simM_draw.
    - cbn [freeze]. apply simM_bind; [apply simM_map_monad, IH|]. intros; apply simM_ret.
    - cbn [freeze]. apply simM_bind; [apply simM_map_monad, IH|]. intros; apply simM_ret.
  Qed.

  Lemma sim_lwrite P id v :
    (forall a b, P a b -> P (upd_add a id v) (upd_add b id v)) -> sim P (lwrite id v).
  Proof. intros H. unfold lwrite. rewrite sub_local. apply sim_event, simM_lwrite, H. Qed.
  Lemma sim_lread P id :
    (forall a b, P a b -> RM.find id (stack_vars a) = RM.find id (stack_vars b)) -> sim P (lread id).
  Proof. intros H. unfold lread. rewrite sub_local. apply sim_event, simM_lread, H. Qed.
  Lemma sim_gread P id : sim P (gread id).
  Proof. unfold gread. rewrite sub_global. apply sim_event, simM_gread. Qed.
  Lemma sim_mem {X} P (e : MemoryE X) : sim P (ITree.trigger (@subevent MemoryE CFGEtop _ X e)).
  Proof. rewrite sub_mem. apply sim_event, simM_mem. Qed.
  Lemma sim_load P dt a : sim P (load dt a).
  Proof. unfold load. apply sim_mem. Qed.
  Lemma sim_store P dt a v : sim P (store dt a v).
  Proof. unfold store. apply sim_mem. Qed.
  Lemma sim_alloca P dt n al : sim P (alloca dt n al).
  Proof. unfold alloca. apply sim_mem. Qed.
  Lemma sim_draw P dt : sim P (draw dt).
  Proof. unfold draw. rewrite sub_draw. apply sim_event, simM_draw. Qed.

  Lemma sim_freeze P v : sim P (freeze v : CFGtop dvalue).
  Proof.
    induction v using dvalue_ind.
    - cbn [freeze freeze_base]. destruct dv; cbn.
      all: try (unfold ITree.map; apply sim_bind; [apply sim_ret|intros; apply sim_ret]).
      apply sim_draw.
    - cbn [freeze]. apply sim_bind; [apply sim_map_monad, IH|]. intros; apply sim_ret.
    - cbn [freeze]. apply sim_bind; [apply sim_map_monad, IH|]. intros; apply sim_ret.
  Qed.

End Sem.

(* ------------------------------------------------------------------ *)
(** ** The expression forms of the emitter *)

(** Locals must satisfy [ok]; the shapes are exactly those [translate_cfg]
    produces (after [convert_typ]). *)
Fixpoint exp_ok (ok : raw_id -> Prop) (e : exp dtyp) : Prop :=
  match e with
  | EXP_Ident (ID_Local r) => ok r
  | EXP_Ident (ID_Global _) => True
  | EXP_Integer _ => True
  | OP_IBinop _ _ e1 e2 => exp_ok ok e1 /\ exp_ok ok e2
  | OP_ICmp _ _ _ e1 e2 => exp_ok ok e1 /\ exp_ok ok e2
  | OP_Conversion _ _ e1 _ => exp_ok ok e1
  | OP_GetElementPtr _ (_, pe) idxs =>
      exp_ok ok pe /\
      (fix all (l : list (dtyp * exp dtyp)) : Prop :=
         match l with
         | [] => True
         | (_, ie) :: r => exp_ok ok ie /\ all r
         end) idxs
  | _ => False
  end.

Definition noflat (r : raw_id) : Prop := is_flat r = false.
Definition noflat_exp : exp dtyp -> Prop := exp_ok noflat.

Lemma exp_ok_gep ok t pt pe idxs :
  exp_ok ok (OP_GetElementPtr t (pt, pe) idxs) <->
  exp_ok ok pe /\ Forall (fun te => exp_ok ok (snd te)) idxs.
Proof.
  cbn. split; intros [H1 H2]; split; auto.
  - induction idxs as [|[it ie] r IH]; [constructor|]. destruct H2. constructor; auto.
  - induction H2 as [|[it ie] r Hx Hr IH]; [exact I|]. split; auto.
Qed.

Lemma exp_ok_mono (ok ok' : raw_id -> Prop) e :
  (forall r, ok r -> ok' r) -> exp_ok ok e -> exp_ok ok' e.
Proof.
  intros Hok. induction e using exp_indP.
  - intros Hc. destruct e; cbn; try discriminate; auto. destruct id; auto.
  - cbn. intuition.
  - cbn. intuition.
  - cbn. auto.
  - rewrite !exp_ok_gep. intros [H1 H2]. split; auto.
    revert H2. induction H as [|[it ie] r Hx Hr IH]; intros H2; [constructor|].
    inversion H2; subst. constructor; auto.
Qed.

(* ------------------------------------------------------------------ *)
(** ** Purity of expression evaluation *)

Definition pureM {R} (t : MCFGtop R) : Prop :=
  forall s s' v, interp_mcfg t s ≈ Ret (s', v) -> s' = s.

Lemma mcfg_ret_inv {R} (r : R) s s' v : interp_mcfg (Ret r) s ≈ Ret (s', v) -> s' = s /\ v = r.
Proof. rewrite interp_mcfg_ret. intros H. apply eqit_inv_Ret in H. injection H. auto. Qed.

Lemma mcfg_bind_ret_inv {R S} (t : MCFGtop R) (k : R -> MCFGtop S) s s2 v :
  interp_mcfg (ITree.bind t k) s ≈ Ret (s2, v) ->
  exists s1 r, interp_mcfg t s ≈ Ret (s1, r) /\ interp_mcfg (k r) s1 ≈ Ret (s2, v).
Proof.
  intros H. rewrite interp_mcfg_bind in H. apply eutt_inv_bind_ret in H as [[s1 r] [H1 H2]].
  exists s1, r. split; [exact H1|exact H2].
Qed.

Lemma pure_bind_ret_inv {R S} (t : MCFGtop R) (k : R -> MCFGtop S) s s2 v :
  pureM t -> interp_mcfg (ITree.bind t k) s ≈ Ret (s2, v) ->
  exists r, interp_mcfg t s ≈ Ret (s, r) /\ interp_mcfg (k r) s ≈ Ret (s2, v).
Proof.
  intros Hp H. apply mcfg_bind_ret_inv in H as (s1 & r & H1 & H2).
  pose proof (Hp _ _ _ H1) as ->. exists r. auto.
Qed.

Lemma lift_ret_inv {X} (m : @EOU.EOU X) s s' v :
  interp_mcfg (EOU_to_itree m) s ≈ Ret (s', v) -> m = EOU.raise_ret v /\ s' = s.
Proof.
  destruct m; cbn; intros H.
  - exfalso. eapply absorbs_not_ret; [|exact H]. eapply absorbs_uniform_absorbs, interp_mcfg_raise_u.
  - exfalso. eapply absorbs_not_ret; [|exact H]. eapply absorbs_uniform_absorbs, interp_mcfg_raiseOOM_u.
  - exfalso. eapply absorbs_not_ret; [|exact H]. eapply absorbs_uniform_absorbs, interp_mcfg_raiseUB_u.
  - apply mcfg_ret_inv in H as [-> ->]. auto.
Qed.

Lemma pureM_ret {R} (r : R) : pureM (Ret r).
Proof. intros s s' v H. apply mcfg_ret_inv in H. tauto. Qed.

Lemma pureM_bind {R S} (t : MCFGtop R) (k : R -> MCFGtop S) :
  pureM t -> (forall x, pureM (k x)) -> pureM (ITree.bind t k).
Proof.
  intros Ht Hk s s' v H. apply pure_bind_ret_inv in H as (r & H1 & H2); [|exact Ht].
  eapply Hk, H2.
Qed.

Lemma pureM_absorbs {R} (t : MCFGtop R) : absorbs_uniform (fun s => interp_mcfg t s) -> pureM t.
Proof. intros H s s' v Hr. exfalso. eapply absorbs_not_ret; [|exact Hr]. eapply absorbs_uniform_absorbs, H. Qed.

Lemma pureM_raise {X} msg : pureM (@raise MCFGEtop X _ msg).
Proof. apply pureM_absorbs, interp_mcfg_raise_u. Qed.
Lemma pureM_raiseUB {X} msg : pureM (@raiseUB MCFGEtop _ X msg).
Proof. apply pureM_absorbs, interp_mcfg_raiseUB_u. Qed.
Lemma pureM_raiseOOM {X} msg : pureM (@raiseOOM MCFGEtop _ X msg).
Proof. apply pureM_absorbs, interp_mcfg_raiseOOM_u. Qed.

Lemma pureM_lift {X} (m : @EOU.EOU X) : pureM (EOU_to_itree m).
Proof. intros s s' v H. apply lift_ret_inv in H. tauto. Qed.

Lemma pureM_lread id : pureM (lread id).
Proof.
  intros [st [[sf stk] g]] s' v H. unfold lread in H.
  destruct (RM.find id (stack_vars sf)) as [w|] eqn:E.
  - rewrite interp_mcfg_lread in H by exact E. rewrite upd_local_sf_id in H.
    apply eqit_inv_Ret in H. injection H. auto.
  - exfalso. destruct (interp_mcfg_lread_none_u id) as (X & e & HX & HU).
    destruct (HU st sf stk g E) as [k Hk]. rewrite Hk in H. apply eqit_inv in H. exact H.
Qed.

Lemma pureM_gread id : pureM (gread id).
Proof.
  intros [st [ls g]] s' v H. unfold gread in H.
  destruct (RM.find id g) as [w|] eqn:E.
  - rewrite interp_mcfg_gread in H by exact E. apply eqit_inv_Ret in H. injection H. auto.
  - exfalso. destruct (interp_mcfg_gread_none_u id) as (X & e & HX & HU).
    destruct (HU st ls g E) as [k Hk]. rewrite Hk in H. apply eqit_inv in H. exact H.
Qed.

Lemma pureM_map_monad {A B} (f : A -> MCFGtop B) (l : list A) :
  Forall (fun x => pureM (f x)) l -> pureM (map_monad f l).
Proof.
  induction 1 as [|a l Ha Hl IH].
  - cbn. apply pureM_ret.
  - cbn [map_monad bind Monad_itree ret]. apply pureM_bind; [exact Ha|]. intros b.
    apply pureM_bind; [exact IH|]. intros bs. apply pureM_ret.
Qed.

(** Memory computations without writes. *)
Fixpoint noput {S A P X} (m : memS S A P X) : Prop :=
  match m with
  | Mret _ | Moom _ | Mub _ | Merr _ => True
  | Mget k => forall σ, noput (k σ)
  | Mput _ _ | Mchoose _ _ => False
  end.

Lemma noput_bind {S A P X Y} (m : memS S A P X) (k : X -> memS S A P Y) :
  noput m -> (forall x, noput (k x)) -> noput (memS_bind m k).
Proof. induction m; cbn; intros Hm Hk; auto; intros σ; apply H; auto. Qed.

Lemma noput_lift {S A P X} (e : @EOU.EOU X) : noput (@lift S A P X e).
Proof. destruct e; exact I. Qed.

Lemma noput_map_monad {S A P X Y} (f : X -> memS S A P Y) (l : list X) :
  (forall x, noput (f x)) -> noput (map_monad f l).
Proof.
  intros Hf. induction l as [|a l IH]; cbn [map_monad bind memS_mon ret]; [exact I|].
  apply noput_bind; [apply Hf|]. intros b. apply noput_bind; [exact IH|]. intros bs. exact I.
Qed.

Lemma memM_interp_noput {X} (m : memM X) σ σ' x :
  noput m -> @memM_interp _ MCFGEbot _ _ _ X m σ ≈ Ret (σ', x) -> σ' = σ.
Proof.
  revert σ σ' x. induction m; cbn; intros σ1 σ2 y Hn Hr; try contradiction.
  - apply eqit_inv_Ret in Hr. injection Hr. auto.
  - exfalso. unfold raiseOOM, trigger_cast' in Hr. rewrite bind_trigger in Hr. apply eqit_inv in Hr. exact Hr.
  - exfalso. unfold raiseUB, trigger_cast' in Hr. rewrite bind_trigger in Hr. apply eqit_inv in Hr. exact Hr.
  - exfalso. unfold raise, trigger_cast' in Hr. rewrite bind_trigger in Hr. apply eqit_inv in Hr. exact Hr.
  - eapply H; eauto.
Qed.

Lemma pureM_mem {X} (e : MemoryE X) :
  noput (handle_memoryM e) -> pureM (ITree.trigger (subevent _ e)).
Proof.
  intros Hn [st rest] s' v H. rewrite interp_mcfg_mem in H.
  apply eutt_inv_bind_ret in H as [[st1 x] [H1 H2]].
  apply memM_interp_noput in H1; [|exact Hn]. subst st1.
  apply eqit_inv_Ret in H2. injection H2. auto.
Qed.

Lemma noput_convert_impure_base ct t1 dv t2 : noput (convert_impure_base ct t1 dv t2).
Proof.
  destruct ct; cbn.
  - unfold assert_inttoptr_types_ok. destruct t1, t2; cbn; try exact I.
    all: apply noput_lift.
  - destruct dv, t2; cbn; try exact I; apply noput_lift.
  - destruct dv, t2; cbn; try exact I; apply noput_lift.
  - exact I.
Qed.

Lemma noput_convert_impure ct t1 v t2 : noput (convert_impure ct t1 v t2).
Proof.
  destruct v as [dv|p fields|vb vt elts]; cbn.
  - destruct (get_base_conversion_type t1 t2) as [[t1' t2']|]; cbn; [|exact I].
    apply noput_bind; [apply noput_convert_impure_base|]. intros; exact I.
  - exact I.
  - destruct vb; [|exact I]. destruct vt; try exact I. cbn.
    destruct vector; [|exact I].
    destruct (get_vector_conversion_type t1 t2) as [[t1' t2']|]; cbn; [|exact I].
    apply noput_bind; [apply noput_lift|]. intros l.
    apply noput_bind; [apply noput_map_monad; intros; apply noput_convert_impure_base|].
    intros; exact I.
Qed.

Lemma pureM_conv ct t1 v t2 : pureM (conv ct t1 v t2).
Proof. unfold conv. apply pureM_mem. cbn. apply noput_convert_impure. Qed.

Lemma pureM_convert ct t1 v t2 : pureM (convert ct t1 v t2).
Proof.
  destruct ct; cbn [convert].
  - destruct (dtyp_eqb t1 t2); [apply pureM_ret|]. destruct (_ =? _)%N; [apply pureM_lift|apply pureM_raise].
  - apply pureM_lift.
  - apply pureM_conv.
Qed.

Lemma exp_pure ok e : exp_ok ok e -> forall t, pureM (denote_exp t e).
Proof.
  induction e using exp_indP; intros He tp.
  - destruct e; cbn in He; try contradiction; try discriminate.
    + destruct id; cbn; [apply pureM_gread | apply pureM_lread].
    + cbn. destruct tp; [apply pureM_lift | apply pureM_raise].
  - destruct He as [H1 H2]. cbn [denote_exp bind Monad_itree].
    apply pureM_bind; [apply IHe1, H1|]. intros v1. apply pureM_bind; [apply IHe2, H2|]. intros v2.
    apply pureM_lift.
  - destruct He as [H1 H2]. cbn [denote_exp bind Monad_itree].
    apply pureM_bind; [apply IHe1, H1|]. intros v1. apply pureM_bind; [apply IHe2, H2|]. intros v2.
    apply pureM_lift.
  - cbn [denote_exp bind Monad_itree]. apply pureM_bind; [apply IHe, He|]. intros v. apply pureM_convert.
  - apply exp_ok_gep in He as [H1 H2]. cbn [denote_exp bind Monad_itree].
    apply pureM_bind; [apply IHe, H1|]. intros vp.
    apply pureM_bind; [|intros; apply pureM_lift].
    apply pureM_map_monad. clear H1. induction H as [|[it ie] r Hx Hr IH]; [constructor|].
    inversion H2; subst. constructor; [apply Hx; assumption | apply IH; assumption].
Qed.

Lemma exp_eval_pure ok e t st sf stk g s' v :
  exp_ok ok e -> interp_mcfg (denote_exp t e) (st, ((sf, stk), g)) ≈ Ret (s', v) ->
  s' = (st, ((sf, stk), g)) /\ exp_eval st sf stk g t e v.
Proof.
  intros He H. pose proof (exp_pure ok e He t _ _ _ H) as ->. split; [reflexivity|exact H].
Qed.

(* ------------------------------------------------------------------ *)
(** ** Frame-insensitivity of expressions (E0) *)

Section ExpSim.
  Variable ctx : CallE ~> itree (CallE +' MCFGEtop).

  Lemma exp_simM ok P e :
    exp_ok ok e ->
    (forall a b, P a b -> forall r, ok r -> RM.find r (stack_vars a) = RM.find r (stack_vars b)) ->
    forall t, simM P (denote_exp t e).
  Proof.
    intros He HP. revert He. induction e using exp_indP; intros He tp.
    - destruct e; cbn in He; try contradiction; try discriminate.
      + destruct id; cbn; [apply simM_gread | apply simM_lread; intros; apply HP; auto].
      + cbn. destruct tp; [apply simM_lift | apply simM_raise].
    - destruct He as [H1 H2]. cbn [denote_exp bind Monad_itree].
      apply simM_bind; [apply IHe1, H1|]. intros v1. apply simM_bind; [apply IHe2, H2|]. intros v2.
      apply simM_lift.
    - destruct He as [H1 H2]. cbn [denote_exp bind Monad_itree].
      apply simM_bind; [apply IHe1, H1|]. intros v1. apply simM_bind; [apply IHe2, H2|]. intros v2.
      apply simM_lift.
    - cbn [denote_exp bind Monad_itree]. apply simM_bind; [apply IHe, He|]. intros v.
      destruct cv; cbn [convert].
      + destruct (dtyp_eqb t1 t2); [apply simM_ret|]. destruct (_ =? _)%N; [apply simM_lift|apply simM_raise].
      + apply simM_lift.
      + unfold conv. apply simM_mem.
    - apply exp_ok_gep in He as [H1 H2]. cbn [denote_exp bind Monad_itree].
      apply simM_bind; [apply IHe, H1|]. intros vp.
      apply simM_bind; [|intros; apply simM_lift].
      apply simM_map_monad. clear H1. induction H as [|[it ie] r Hx Hr IH]; [constructor|].
      inversion H2; subst. constructor; [apply Hx; assumption | apply IH; assumption].
  Qed.

  (** Evaluation is preserved by changing the frame at names outside [ok]. *)
  Lemma exp_eval_ok_agree ok e t v st sf sf' stk g :
    exp_ok ok e ->
    (forall r, ok r -> RM.find r (stack_vars sf') = RM.find r (stack_vars sf)) ->
    exp_eval st sf stk g t e v -> exp_eval st sf' stk g t e v.
  Proof.
    intros He Hag H.
    pose proof (exp_simM ok (fun a b => a = sf /\ b = sf') e He
                  ltac:(intros a b [-> ->] r Hr; symmetry; apply Hag, Hr) t st sf sf' stk g (conj eq_refl eq_refl)) as HS.
    unfold exp_eval in H. eapply ret_eutt in HS; [|exact H].
    destruct HS as [r2 [H2 HR]]. eapply RR_inv; [exact HR|].
    intros ? ? ? ? ? ? [-> ->] E1 ->. injection E1; intros; subst. exact H2.
  Qed.

  Lemma exp_eval_agree lo hi e t v st sf sf' stk g :
    noflat_exp e -> agree_except lo hi sf sf' ->
    exp_eval st sf stk g t e v -> exp_eval st sf' stk g t e v.
  Proof.
    intros He Hag. apply exp_eval_ok_agree with (ok := noflat); [exact He|].
    intros r Hr. eapply agree_except_noflat; eauto.
  Qed.

  Lemma exp_eval_flat_out lo hi k t v st sf sf' stk g :
    agree_except lo hi sf sf' -> ~ (lo <= k < hi)%positive ->
    exp_eval st sf stk g t (EXP_Ident (ID_Local (flat_id k))) v ->
    exp_eval st sf' stk g t (EXP_Ident (ID_Local (flat_id k))) v.
  Proof.
    intros Hag Hk. apply exp_eval_ok_agree with (ok := fun r => r = flat_id k); [reflexivity|].
    intros r ->. eapply agree_except_out; eauto.
  Qed.
End ExpSim.

(* ------------------------------------------------------------------ *)
(** ** Soundness of atomization (E1) *)

(** Frames agreeing on all non-fresh names. *)
Definition agree_noflat (sf sf' : stack_frame) : Prop :=
  forall r, is_flat r = false -> RM.find r (stack_vars sf') = RM.find r (stack_vars sf).

Lemma agree_noflat_refl sf : agree_noflat sf sf.
Proof. intros r _. reflexivity. Qed.
Lemma agree_noflat_except lo hi sf sf' sf2 :
  agree_noflat sf sf' -> agree_except lo hi sf' sf2 -> agree_noflat sf sf2.
Proof. intros H1 H2 r Hr. rewrite (agree_except_noflat _ _ _ _ _ H2 Hr). apply H1, Hr. Qed.
Lemma agree_except_noflat' lo hi sf sf' : agree_except lo hi sf sf' -> agree_noflat sf sf'.
Proof. intros H r Hr. eapply agree_except_noflat; eauto. Qed.

(** Names an atomized operand may mention: non-fresh, or fresh in [c, c'). *)
Definition atom_ok (c c' : positive) (r : raw_id) : Prop := is_flat r = false \/ flat_in c c' r.

Lemma atom_ok_mono c c' d d' r : (d <= c)%positive -> (c' <= d')%positive -> atom_ok c c' r -> atom_ok d d' r.
Proof. intros H1 H2 [H|H]; [left; exact H|right; eapply flat_in_mono; eauto]. Qed.
Lemma noflat_atom_ok c c' r : noflat r -> atom_ok c c' r.
Proof. left; exact H. Qed.

(** Reads of [atom_ok c c'] names survive code that only writes [flat_id k], [k >= c']. *)
Lemma atom_ok_agree c c' n sf sf' r :
  (c' <= n)%positive -> agree_except c' n sf sf' -> atom_ok c c' r ->
  RM.find r (stack_vars sf') = RM.find r (stack_vars sf).
Proof.
  intros Hn Hag [H|[k [-> Hk]]].
  - eapply agree_except_noflat; eauto.
  - eapply agree_except_out; eauto. lia.
Qed.

Section Transport.
  Variable ctx : CallE ~> itree (CallE +' MCFGEtop).
  Variable va : option ptr.
  Notation RUN t s := (run ctx t s).

  Lemma run_code_nil s : RUN (denote_code [] va) s ≈ Ret (s, tt).
  Proof. unfold denote_code. cbn [loop_monad ret Monad_itree]. apply run_ret. Qed.

  Lemma run_code_cons i l s :
    RUN (denote_code (i :: l) va) s
    ≈ ITree.bind (RUN (denote_instr i va) s) (fun '(s', _) => RUN (denote_code l va) s').
  Proof.
    unfold denote_code. cbn [loop_monad bind Monad_itree]. rewrite run_bind. apply eutt_eq_bind. intros [s' []]. reflexivity.
  Qed.

  Lemma run_code_app (a b : code dtyp) s :
    RUN (denote_code (a ++ b)%list va) s
    ≈ ITree.bind (RUN (denote_code a va) s) (fun '(s', _) => RUN (denote_code b va) s').
  Proof.
    revert s. induction a as [|i a IH]; intros s.
    - cbn [app]. rewrite run_code_nil, Eqit.bind_ret_l. reflexivity.
    - cbn [app]. rewrite !run_code_cons, Eqit.bind_bind. apply eutt_eq_bind. intros [s' []]. apply IH.
  Qed.

  Lemma run_code_single i s : RUN (denote_code [i] va) s ≈ RUN (denote_instr i va) s.
  Proof.
    rewrite run_code_cons. rewrite <- (Eqit.bind_ret_r (RUN (denote_instr i va) s)) at 2.
    apply eutt_eq_bind. intros [s' []]. apply run_code_nil.
  Qed.

  Lemma run_instr_op id e md st sf stk g v :
    exp_eval st sf stk g None e v ->
    RUN (denote_instr (IId id, INSTR_Op e, md) va) (st, ((sf, stk), g))
    ≈ Ret ((st, ((upd_add sf id v, stk), g)), tt).
  Proof.
    intros H. cbn [denote_instr bind Monad_itree ret]. rewrite run_bind, (run_exp' ctx) by exact H. rewrite Eqit.bind_ret_l.
    cbv beta iota. rewrite run_bind, run_lwrite, Eqit.bind_ret_l. cbv beta iota. apply run_ret.
  Qed.

  (** Transfer of a [Ret]-run across frames, via [simM]. *)
  Lemma simM_transfer {R} (t : MCFGtop R) st sf sf' stk g v :
    simM (fun a b => a = sf /\ b = sf') t ->
    interp_mcfg t (st, ((sf, stk), g)) ≈ Ret ((st, ((sf, stk), g)), v) ->
    interp_mcfg t (st, ((sf', stk), g)) ≈ Ret ((st, ((sf', stk), g)), v).
  Proof.
    intros HS H. specialize (HS st sf sf' stk g (conj eq_refl eq_refl)).
    eapply ret_eutt in HS; [|exact H]. destruct HS as [r2 [H2 HR]].
    eapply RR_inv; [exact HR|]. intros ? ? ? ? ? ? [-> ->] E1 ->. injection E1; intros; subst. exact H2.
  Qed.

  Lemma simM_convert P cv t1 v t2 : simM P (convert cv t1 v t2).
  Proof.
    destruct cv; cbn [convert].
    - destruct (dtyp_eqb t1 t2); [apply simM_ret|]. destruct (_ =? _)%N; [apply simM_lift|apply simM_raise].
    - apply simM_lift.
    - unfold conv. apply simM_mem.
  Qed.

  Lemma convert_transfer cv t1 v1 t2 st sf sf' stk g v :
    interp_mcfg (convert cv t1 v1 t2) (st, ((sf, stk), g)) ≈ Ret ((st, ((sf, stk), g)), v) ->
    interp_mcfg (convert cv t1 v1 t2) (st, ((sf', stk), g)) ≈ Ret ((st, ((sf', stk), g)), v).
  Proof. apply simM_transfer, simM_convert. Qed.

  (** Inversion of the evaluation of a GEP's index list. *)
  Lemma map_monad_eval_inv ok (idxs : list (dtyp * exp dtyp)) st sf stk g s' vs :
    Forall (fun te => exp_ok ok (snd te)) idxs ->
    interp_mcfg (map_monad (fun '(dt, index) => denote_exp (Some dt) index) idxs) (st, ((sf, stk), g))
    ≈ Ret (s', vs) ->
    s' = (st, ((sf, stk), g)) /\
    Forall2 (fun '(dt, e) v => exp_eval st sf stk g (Some dt) e v) idxs vs.
  Proof.
    intros Hok. revert vs. induction Hok as [|[dt e] r He Hr IH]; intros vs H.
    - cbn in H. apply mcfg_ret_inv in H as [-> ->]. split; [reflexivity|constructor].
    - cbn [map_monad bind Monad_itree ret] in H.
      apply pure_bind_ret_inv in H as (v & H1 & H2); [|eapply exp_pure; exact He].
      apply pure_bind_ret_inv in H2 as (vs' & H2 & H3); [|apply pureM_map_monad].
      + apply mcfg_ret_inv in H3 as [-> ->]. destruct (IH _ H2) as [_ HF].
        split; [reflexivity|constructor; [exact H1|exact HF]].
      + clear -Hr. induction Hr as [|[dt' e'] r' He' Hr' IH']; constructor; [eapply exp_pure; exact He'|exact IH'].
  Qed.

  Lemma exp_eval_ibinop_inv st sf stk g t op dt e1 e2 v :
    noflat_exp e1 -> noflat_exp e2 ->
    exp_eval st sf stk g t (OP_IBinop op dt e1 e2) v ->
    exists v1 v2, exp_eval st sf stk g (Some dt) e1 v1 /\ exp_eval st sf stk g (Some dt) e2 v2 /\
             eval_iop op v1 v2 = EOU.raise_ret v.
  Proof.
    intros H1 H2 H. unfold exp_eval in H. cbn [denote_exp bind Monad_itree] in H.
    apply pure_bind_ret_inv in H as (v1 & E1 & H); [|eapply exp_pure; exact H1].
    apply pure_bind_ret_inv in H as (v2 & E2 & H); [|eapply exp_pure; exact H2].
    apply lift_ret_inv in H as [H _]. eauto.
  Qed.

  Lemma exp_eval_icmp_inv st sf stk g t ss cmp dt e1 e2 v :
    noflat_exp e1 -> noflat_exp e2 ->
    exp_eval st sf stk g t (OP_ICmp ss cmp dt e1 e2) v ->
    exists v1 v2, exp_eval st sf stk g (Some dt) e1 v1 /\ exp_eval st sf stk g (Some dt) e2 v2 /\
             eval_icmp ss cmp v1 v2 = EOU.raise_ret v.
  Proof.
    intros H1 H2 H. unfold exp_eval in H. cbn [denote_exp bind Monad_itree] in H.
    apply pure_bind_ret_inv in H as (v1 & E1 & H); [|eapply exp_pure; exact H1].
    apply pure_bind_ret_inv in H as (v2 & E2 & H); [|eapply exp_pure; exact H2].
    apply lift_ret_inv in H as [H _]. eauto.
  Qed.

  Lemma exp_eval_conv_inv st sf stk g t cv t1 e1 t2 v :
    noflat_exp e1 ->
    exp_eval st sf stk g t (OP_Conversion cv t1 e1 t2) v ->
    exists v1, exp_eval st sf stk g (Some t1) e1 v1 /\
          interp_mcfg (convert cv t1 v1 t2) (st, ((sf, stk), g)) ≈ Ret ((st, ((sf, stk), g)), v).
  Proof.
    intros H1 H. unfold exp_eval in H. cbn [denote_exp bind Monad_itree] in H.
    apply pure_bind_ret_inv in H as (v1 & E1 & H); [|eapply exp_pure; exact H1].
    eauto.
  Qed.

  Lemma exp_eval_gep_inv st sf stk g t dt1 dt2 ep idxs v :
    noflat_exp ep -> Forall (fun te => noflat_exp (snd te)) idxs ->
    exp_eval st sf stk g t (OP_GetElementPtr dt1 (dt2, ep) idxs) v ->
    exists vp vs, exp_eval st sf stk g (Some dt2) ep vp /\
             Forall2 (fun '(dt, e) v => exp_eval st sf stk g (Some dt) e v) idxs vs /\
             eval_gep dt1 vp vs = EOU.raise_ret v.
  Proof.
    intros H1 H2 H. unfold exp_eval in H. cbn [denote_exp bind Monad_itree] in H.
    apply pure_bind_ret_inv in H as (vp & E1 & H); [|eapply exp_pure; exact H1].
    apply mcfg_bind_ret_inv in H as (s1 & vs & H & H3).
    apply map_monad_eval_inv with (ok := noflat) in H as [-> HF]; [|exact H2].
    apply lift_ret_inv in H3 as [H3 _]. eauto.
  Qed.

  (** The conversion-free, state-free evaluation of an atomized compound. *)
  Lemma exp_eval_conv_atom st sf stk g t cv t1 a t2 v1 v :
    exp_eval st sf stk g (Some t1) a v1 ->
    interp_mcfg (convert cv t1 v1 t2) (st, ((sf, stk), g)) ≈ Ret ((st, ((sf, stk), g)), v) ->
    exp_eval st sf stk g t (OP_Conversion cv t1 a t2) v.
  Proof.
    intros H1 H2. unfold exp_eval in *. cbn [denote_exp bind Monad_itree].
    rewrite interp_mcfg_bind, H1, Eqit.bind_ret_l. cbv beta iota. exact H2.
  Qed.

  Lemma Forall2_eval_agree c c' n st stk g sf sf' (ai : list (dtyp * exp dtyp)) vs :
    (c' <= n)%positive -> agree_except c' n sf sf' ->
    Forall (fun te => exp_ok (atom_ok c c') (snd te)) ai ->
    Forall2 (fun '(dt, e) v => exp_eval st sf stk g (Some dt) e v) ai vs ->
    Forall2 (fun '(dt, e) v => exp_eval st sf' stk g (Some dt) e v) ai vs.
  Proof.
    intros Hn Hag Hok HF. revert Hok. induction HF as [|[dt e] v ai vs He HF IH]; intros Hok; constructor.
    - inversion Hok; subst. eapply exp_eval_ok_agree; [exact H1| |exact He].
      intros r Hr. eapply atom_ok_agree; eauto.
    - inversion Hok; subst. apply IH; assumption.
  Qed.

  Definition atomized (c c' : positive) (a : exp dtyp) : Prop :=
    compound a = false /\ exp_ok (atom_ok c c') a.

  Lemma atomized_mono c c' d d' a : (d <= c)%positive -> (c' <= d')%positive -> atomized c c' a -> atomized d d' a.
  Proof. intros H1 H2 [Ha Hok]. split; [exact Ha|]. eapply exp_ok_mono; [|exact Hok]. intros r; apply atom_ok_mono; auto. Qed.

  (** (E1) Soundness of [atomizeP]. *)
  Lemma atomizeP_sound st stk g e :
    noflat_exp e ->
    forall c t v sf, exp_eval st sf stk g t e v ->
    forall sf', agree_noflat sf sf' ->
    let '(cc, a, c') := atomizeP e c in
    (c <= c')%positive /\ exists sf2,
      RUN (denote_code cc va) (st, ((sf', stk), g)) ≈ Ret ((st, ((sf2, stk), g)), tt) /\
      agree_except c c' sf' sf2 /\ atomized c c' a /\ exp_eval st sf2 stk g t a v.
  Proof.
    induction e using exp_indP; intros He c tp v sf Hev sf' Hag.
    - (* atomic *)
      rewrite atomizeP_atomic by assumption. split; [lia|]. exists sf'. split; [apply run_code_nil|].
      split; [apply agree_except_refl|]. split.
      + split; [assumption|]. eapply exp_ok_mono; [|exact He]. intros r Hr. left; exact Hr.
      + eapply exp_eval_ok_agree; [exact He| |exact Hev]. intros r Hr. apply Hag, Hr.
    - (* ibinop *)
      destruct He as [He1 He2].
      apply exp_eval_ibinop_inv in Hev as (v1 & v2 & Hv1 & Hv2 & Hop); try assumption.
      cbn [atomizeP].
      specialize (IHe1 He1 c (Some t) v1 sf Hv1 sf' Hag).
      destruct (atomizeP e1 c) as [[c1 a1] n1]. destruct IHe1 as (Hc1 & sf1 & Hrun1 & Hag1 & Hat1 & Hev1).
      specialize (IHe2 He2 n1 (Some t) v2 sf Hv2 sf1 (agree_noflat_except _ _ _ _ _ Hag Hag1)).
      destruct (atomizeP e2 n1) as [[c2 a2] n2]. destruct IHe2 as (Hc2 & sf2 & Hrun2 & Hag2 & Hat2 & Hev2).
      split; [lia|]. exists (upd_add sf2 (flat_id n2) v).
      assert (Hev1' : exp_eval st sf2 stk g (Some t) a1 v1).
      { destruct Hat1 as [_ Hok1]. eapply exp_eval_ok_agree; [exact Hok1| |exact Hev1].
        intros r Hr. eapply atom_ok_agree; eauto. }
      split; [|split; [|split]].
      + rewrite run_code_app, Hrun1, Eqit.bind_ret_l. cbv beta iota. rewrite run_code_app, Hrun2, Eqit.bind_ret_l. cbv beta iota.
        rewrite run_code_single. apply run_instr_op. eapply exp_eval_ibinop; eauto.
      + apply agree_except_add_flat; [lia|]. apply (@agree_except_mono c (Pos.succ n2) c n2); [lia|lia|].
        eapply (@agree_except_trans c n1 n1 n2 c n2); [lia|lia|lia|lia|exact Hag1|exact Hag2].
      + split; [reflexivity|]. cbn. right. exists n2. split; [reflexivity|lia].
      + apply exp_eval_local. apply find_upd_add_eq.
    - (* icmp *)
      destruct He as [He1 He2].
      apply exp_eval_icmp_inv in Hev as (v1 & v2 & Hv1 & Hv2 & Hop); try assumption.
      cbn [atomizeP].
      specialize (IHe1 He1 c (Some t) v1 sf Hv1 sf' Hag).
      destruct (atomizeP e1 c) as [[c1 a1] n1]. destruct IHe1 as (Hc1 & sf1 & Hrun1 & Hag1 & Hat1 & Hev1).
      specialize (IHe2 He2 n1 (Some t) v2 sf Hv2 sf1 (agree_noflat_except _ _ _ _ _ Hag Hag1)).
      destruct (atomizeP e2 n1) as [[c2 a2] n2]. destruct IHe2 as (Hc2 & sf2 & Hrun2 & Hag2 & Hat2 & Hev2).
      split; [lia|]. exists (upd_add sf2 (flat_id n2) v).
      assert (Hev1' : exp_eval st sf2 stk g (Some t) a1 v1).
      { destruct Hat1 as [_ Hok1]. eapply exp_eval_ok_agree; [exact Hok1| |exact Hev1].
        intros r Hr. eapply atom_ok_agree; eauto. }
      split; [|split; [|split]].
      + rewrite run_code_app, Hrun1, Eqit.bind_ret_l. cbv beta iota. rewrite run_code_app, Hrun2, Eqit.bind_ret_l. cbv beta iota.
        rewrite run_code_single. apply run_instr_op. eapply exp_eval_icmp; eauto.
      + apply agree_except_add_flat; [lia|]. apply (@agree_except_mono c (Pos.succ n2) c n2); [lia|lia|].
        eapply (@agree_except_trans c n1 n1 n2 c n2); [lia|lia|lia|lia|exact Hag1|exact Hag2].
      + split; [reflexivity|]. cbn. right. exists n2. split; [reflexivity|lia].
      + apply exp_eval_local. apply find_upd_add_eq.
    - (* conversion *)
      apply exp_eval_conv_inv in Hev as (v1 & Hv1 & Hcv); [|exact He].
      cbn [atomizeP].
      specialize (IHe He c (Some t1) v1 sf Hv1 sf' Hag).
      destruct (atomizeP e c) as [[c1 a1] n1]. destruct IHe as (Hc1 & sf1 & Hrun1 & Hag1 & Hat1 & Hev1).
      split; [lia|]. exists (upd_add sf1 (flat_id n1) v).
      split; [|split; [|split]].
      + rewrite run_code_app, Hrun1, Eqit.bind_ret_l. cbv beta iota.
        rewrite run_code_single. apply run_instr_op. eapply exp_eval_conv_atom; [exact Hev1|].
        apply convert_transfer with (sf := sf). exact Hcv.
      + apply agree_except_add_flat; [lia|]. apply (@agree_except_mono c (Pos.succ n1) c n1); [lia|lia|exact Hag1].
      + split; [reflexivity|]. cbn. right. exists n1. split; [reflexivity|lia].
      + apply exp_eval_local. apply find_upd_add_eq.
    - (* gep *)
      apply exp_ok_gep in He as [Hep Hidx].
      apply exp_eval_gep_inv in Hev as (vp & vs & Hvp & Hvs & Hgep); try assumption.
      rewrite atomizeP_GEP.
      specialize (IHe Hep c (Some pt) vp sf Hvp sf' Hag).
      destruct (atomizeP e c) as [[cp ape] np]. destruct IHe as (Hcp & sfp & Hrunp & Hagp & Hatp & Hevp).
      (* the index list *)
      assert (HI : forall k sfk, agree_noflat sf sfk ->
                let '(ci, ai, k2) := atomize_idxsP idxs k in
                (k <= k2)%positive /\ exists sf2,
                  RUN (denote_code ci va) (st, ((sfk, stk), g)) ≈ Ret ((st, ((sf2, stk), g)), tt) /\
                  agree_except k k2 sfk sf2 /\
                  Forall (fun te => atomized k k2 (snd te)) ai /\
                  Forall2 (fun '(dt, a) v => exp_eval st sf2 stk g (Some dt) a v) ai vs).
      { clear Hvp Hgep Hrunp Hagp Hatp Hevp Hep Hcp. revert vs Hvs Hidx.
        induction H as [|[it ie] r Hie Hr IH]; intros vs Hvs Hidx k sfk Hagk.
        - inversion Hvs; subst. cbn. split; [lia|]. exists sfk. split; [apply run_code_nil|].
          split; [apply agree_except_refl|]. split; constructor.
        - inversion Hidx as [|x0 r0 Hie_ok Hr_ok]; subst. inversion Hvs as [|x1 y l1 vs' Hy Hvs']; subst.
          cbn [atomize_idxsP]. cbn in Hie, Hie_ok.
          specialize (Hie Hie_ok k (Some it) y sf Hy sfk Hagk).
          destruct (atomizeP ie k) as [[ci ai] k1]. destruct Hie as (Hk1 & sf1 & Hrun1 & Hag1 & Hat1 & Hev1).
          specialize (IH vs' Hvs' Hr_ok k1 sf1 (agree_noflat_except _ _ _ _ _ Hagk Hag1)).
          destruct (atomize_idxsP r k1) as [[cr ar] k2]. destruct IH as (Hk2 & sf2 & Hrun2 & Hag2 & Hat2 & Hev2).
          split; [lia|]. exists sf2. split; [|split; [|split]].
          + rewrite run_code_app, Hrun1, Eqit.bind_ret_l. cbv beta iota. exact Hrun2.
          + eapply (@agree_except_trans k k1 k1 k2 k k2); [lia|lia|lia|lia|exact Hag1|exact Hag2].
          + constructor; [eapply atomized_mono; [| |exact Hat1]; lia|].
            eapply Forall_impl; [|exact Hat2]. intros te; apply atomized_mono; lia.
          + constructor; [|exact Hev2]. destruct Hat1 as [_ Hok1].
            eapply exp_eval_ok_agree; [exact Hok1| |exact Hev1]. intros r0 Hr0. eapply atom_ok_agree; eauto. }
      specialize (HI np sfp (agree_noflat_except _ _ _ _ _ Hag Hagp)).
      destruct (atomize_idxsP idxs np) as [[cidx aidxs] ni]. destruct HI as (Hni & sf2 & Hrun2 & Hag2 & Hat2 & Hev2).
      split; [lia|]. exists (upd_add sf2 (flat_id ni) v).
      assert (Hevp' : exp_eval st sf2 stk g (Some pt) ape vp).
      { destruct Hatp as [_ Hokp]. eapply exp_eval_ok_agree; [exact Hokp| |exact Hevp].
        intros r Hr. eapply atom_ok_agree; eauto. }
      split; [|split; [|split]].
      + rewrite run_code_app, Hrunp, Eqit.bind_ret_l. cbv beta iota. rewrite run_code_app, Hrun2, Eqit.bind_ret_l. cbv beta iota.
        rewrite run_code_single. apply run_instr_op. eapply exp_eval_gep; eauto.
      + apply agree_except_add_flat; [lia|]. apply (@agree_except_mono c (Pos.succ ni) c ni); [lia|lia|].
        eapply (@agree_except_trans c np np ni c ni); [lia|lia|lia|lia|exact Hagp|exact Hag2].
      + split; [reflexivity|]. cbn. right. exists ni. split; [reflexivity|lia].
      + apply exp_eval_local. apply find_upd_add_eq.
  Qed.

  (** (E1') Soundness of the index-list, typed-expression, operand and
      argument-list atomisers, in the style of [atomizeP_sound]. *)
  Lemma atomize_idxsP_sound st stk g sf (idxs : list (dtyp * exp dtyp)) vs :
    Forall (fun te => noflat_exp (snd te)) idxs ->
    Forall2 (fun '(dt, e) v => exp_eval st sf stk g (Some dt) e v) idxs vs ->
    forall k sfk, agree_noflat sf sfk ->
    let '(ci, ai, k2) := atomize_idxsP idxs k in
    (k <= k2)%positive /\ exists sf2,
      RUN (denote_code ci va) (st, ((sfk, stk), g)) ≈ Ret ((st, ((sf2, stk), g)), tt) /\
      agree_except k k2 sfk sf2 /\
      Forall (fun te => atomized k k2 (snd te)) ai /\
      map fst ai = map fst idxs /\
      Forall2 (fun '(dt, a) v => exp_eval st sf2 stk g (Some dt) a v) ai vs.
  Proof.
    intros Hidx Hvs. revert Hidx. induction Hvs as [|[it ie] y r vs' Hy Hvs' IH]; intros Hidx k sfk Hagk.
    - cbn. split; [lia|]. exists sfk. split; [apply run_code_nil|].
      split; [apply agree_except_refl|]. split; [constructor|]. split; [reflexivity|constructor].
    - inversion Hidx as [|x0 r0 Hie_ok Hr_ok]; subst. cbn [atomize_idxsP]. cbn in Hie_ok.
      pose proof (atomizeP_sound st stk g ie Hie_ok k (Some it) y sf Hy sfk Hagk) as Hie.
      destruct (atomizeP ie k) as [[ci ai] k1]. destruct Hie as (Hk1 & sf1 & Hrun1 & Hag1 & Hat1 & Hev1).
      specialize (IH Hr_ok k1 sf1 (agree_noflat_except _ _ _ _ _ Hagk Hag1)).
      destruct (atomize_idxsP r k1) as [[cr ar] k2]. destruct IH as (Hk2 & sf2 & Hrun2 & Hag2 & Hat2 & Hty & Hev2).
      split; [lia|]. exists sf2. split; [|split; [|split; [|split]]].
      + rewrite run_code_app, Hrun1, Eqit.bind_ret_l. cbv beta iota. exact Hrun2.
      + eapply (@agree_except_trans k k1 k1 k2 k k2); [lia|lia|lia|lia|exact Hag1|exact Hag2].
      + constructor; [eapply atomized_mono; [| |exact Hat1]; lia|].
        eapply Forall_impl; [|exact Hat2]. intros te; apply atomized_mono; lia.
      + cbn. f_equal. exact Hty.
      + constructor; [|exact Hev2]. destruct Hat1 as [_ Hok1].
        eapply exp_eval_ok_agree; [exact Hok1| |exact Hev1]. intros r0 Hr0. eapply (atom_ok_agree k k1 k2 sf1 sf2); [lia|exact Hag2|exact Hr0].
  Qed.

  Lemma atomize_texpP_sound st stk g sf (te : dtyp * exp dtyp) v c sf' :
    noflat_exp (snd te) ->
    exp_eval st sf stk g (Some (fst te)) (snd te) v ->
    agree_noflat sf sf' ->
    let '(cc, te', c') := atomize_texpP te c in
    (c <= c')%positive /\ fst te' = fst te /\ exists sf2,
      RUN (denote_code cc va) (st, ((sf', stk), g)) ≈ Ret ((st, ((sf2, stk), g)), tt) /\
      agree_except c c' sf' sf2 /\ atomized c c' (snd te') /\
      exp_eval st sf2 stk g (Some (fst te')) (snd te') v.
  Proof.
    destruct te as [t e]. cbn [fst snd]. intros He Hev Hag. unfold atomize_texpP.
    pose proof (atomizeP_sound st stk g e He c (Some t) v sf Hev sf' Hag) as H.
    destruct (atomizeP e c) as [[cc a] c']. destruct H as (Hc & sf2 & H1 & H2 & H3 & H4).
    split; [exact Hc|]. split; [reflexivity|]. exists sf2. auto.
  Qed.

  Lemma atomize_opP_sound st stk g sf e t v c sf' :
    noflat_exp e ->
    exp_eval st sf stk g t e v ->
    agree_noflat sf sf' ->
    let '(cc, e', c') := atomize_opP e c in
    (c <= c')%positive /\ exists sf2,
      RUN (denote_code cc va) (st, ((sf', stk), g)) ≈ Ret ((st, ((sf2, stk), g)), tt) /\
      agree_except c c' sf' sf2 /\ exp_ok (atom_ok c c') e' /\ compound e' = compound e /\
      exp_eval st sf2 stk g t e' v.
  Proof.
    intros He Hev Hag.
    destruct (compound e) eqn:Hce.
    2:{ assert (E : atomize_opP e c = ([], e, c)) by (destruct e; cbn in Hce |- *; try reflexivity; discriminate).
        rewrite E. split; [lia|]. exists sf'. split; [apply run_code_nil|]. split; [apply agree_except_refl|].
        split; [eapply exp_ok_mono; [|exact He]; intros r Hr; left; exact Hr|]. split; [exact Hce|].
        eapply exp_eval_ok_agree; [exact He| |exact Hev]. intros r Hr. apply Hag, Hr. }
    destruct e; cbn in Hce; try discriminate; clear Hce.
    - (* ibinop *)
      destruct He as [He1 He2].
      apply exp_eval_ibinop_inv in Hev as (v1 & v2 & Hv1 & Hv2 & Hop); try assumption.
      cbn [atomize_opP].
      pose proof (atomizeP_sound st stk g e1 He1 c _ v1 sf Hv1 sf' Hag) as IH1.
      destruct (atomizeP e1 c) as [[c1 a1] n1]. destruct IH1 as (Hc1 & sf1 & Hrun1 & Hag1 & Hat1 & Hev1).
      pose proof (atomizeP_sound st stk g e2 He2 n1 _ v2 sf Hv2 sf1 (agree_noflat_except _ _ _ _ _ Hag Hag1)) as IH2.
      destruct (atomizeP e2 n1) as [[c2 a2] n2]. destruct IH2 as (Hc2 & sf2 & Hrun2 & Hag2 & Hat2 & Hev2).
      split; [lia|]. exists sf2.
      assert (Hev1' : exp_eval st sf2 stk g (Some t0) a1 v1).
      { destruct Hat1 as [_ Hok1]. eapply exp_eval_ok_agree; [exact Hok1| |exact Hev1].
        intros r Hr. eapply atom_ok_agree; eauto. }
      split; [|split; [|split; [|split]]].
      + rewrite run_code_app, Hrun1, Eqit.bind_ret_l. cbv beta iota. exact Hrun2.
      + eapply (@agree_except_trans c n1 n1 n2 c n2); [lia|lia|lia|lia|exact Hag1|exact Hag2].
      + split; [eapply exp_ok_mono; [|apply Hat1]|eapply exp_ok_mono; [|apply Hat2]];
          intros r; apply atom_ok_mono; lia.
      + reflexivity.
      + eapply exp_eval_ibinop; eauto.
    - (* icmp *)
      destruct He as [He1 He2].
      apply exp_eval_icmp_inv in Hev as (v1 & v2 & Hv1 & Hv2 & Hop); try assumption.
      cbn [atomize_opP].
      pose proof (atomizeP_sound st stk g e1 He1 c _ v1 sf Hv1 sf' Hag) as IH1.
      destruct (atomizeP e1 c) as [[c1 a1] n1]. destruct IH1 as (Hc1 & sf1 & Hrun1 & Hag1 & Hat1 & Hev1).
      pose proof (atomizeP_sound st stk g e2 He2 n1 _ v2 sf Hv2 sf1 (agree_noflat_except _ _ _ _ _ Hag Hag1)) as IH2.
      destruct (atomizeP e2 n1) as [[c2 a2] n2]. destruct IH2 as (Hc2 & sf2 & Hrun2 & Hag2 & Hat2 & Hev2).
      split; [lia|]. exists sf2.
      assert (Hev1' : exp_eval st sf2 stk g (Some t0) a1 v1).
      { destruct Hat1 as [_ Hok1]. eapply exp_eval_ok_agree; [exact Hok1| |exact Hev1].
        intros r Hr. eapply atom_ok_agree; eauto. }
      split; [|split; [|split; [|split]]].
      + rewrite run_code_app, Hrun1, Eqit.bind_ret_l. cbv beta iota. exact Hrun2.
      + eapply (@agree_except_trans c n1 n1 n2 c n2); [lia|lia|lia|lia|exact Hag1|exact Hag2].
      + split; [eapply exp_ok_mono; [|apply Hat1]|eapply exp_ok_mono; [|apply Hat2]];
          intros r; apply atom_ok_mono; lia.
      + reflexivity.
      + eapply exp_eval_icmp; eauto.
    - (* conversion *)
      apply exp_eval_conv_inv in Hev as (v1 & Hv1 & Hcv); [|exact He].
      cbn [atomize_opP].
      pose proof (atomizeP_sound st stk g e He c _ v1 sf Hv1 sf' Hag) as IH.
      destruct (atomizeP e c) as [[c1 a1] n1]. destruct IH as (Hc1 & sf1 & Hrun1 & Hag1 & Hat1 & Hev1).
      split; [lia|]. exists sf1. split; [exact Hrun1|]. split; [exact Hag1|].
      split; [apply Hat1|]. split; [reflexivity|].
      eapply exp_eval_conv_atom; [exact Hev1|]. apply convert_transfer with (sf := sf). exact Hcv.
    - (* gep *)
      destruct ptrval as [pt ep].
      apply exp_ok_gep in He as [Hep Hidx].
      apply exp_eval_gep_inv in Hev as (vp & vs & Hvp & Hvs & Hgep); try assumption.
      cbn [atomize_opP].
      pose proof (atomizeP_sound st stk g ep Hep c _ vp sf Hvp sf' Hag) as IH.
      destruct (atomizeP ep c) as [[cp ape] np]. destruct IH as (Hcp & sfp & Hrunp & Hagp & Hatp & Hevp).
      pose proof (atomize_idxsP_sound st stk g sf idxs vs Hidx Hvs np sfp (agree_noflat_except _ _ _ _ _ Hag Hagp)) as HI.
      destruct (atomize_idxsP idxs np) as [[cidx aidxs] ni]. destruct HI as (Hni & sf2 & Hrun2 & Hag2 & Hat2 & Hty & Hev2).
      split; [lia|]. exists sf2.
      assert (Hevp' : exp_eval st sf2 stk g (Some pt) ape vp).
      { destruct Hatp as [_ Hokp]. eapply exp_eval_ok_agree; [exact Hokp| |exact Hevp].
        intros r Hr. eapply atom_ok_agree; eauto. }
      split; [|split; [|split; [|split]]].
      + rewrite run_code_app, Hrunp, Eqit.bind_ret_l. cbv beta iota. exact Hrun2.
      + eapply (@agree_except_trans c np np ni c ni); [lia|lia|lia|lia|exact Hagp|exact Hag2].
      + apply exp_ok_gep. split.
        * eapply exp_ok_mono; [|apply Hatp]. intros r; apply atom_ok_mono; lia.
        * eapply Forall_impl; [|exact Hat2]. intros te Hte. eapply exp_ok_mono; [|apply Hte].
          intros r; apply atom_ok_mono; lia.
      + reflexivity.
      + eapply exp_eval_gep; eauto.
  Qed.

  Lemma atomize_argsP_sound st stk g sf (args : list (texp dtyp * list param_attr)) dvs :
    Forall (fun a => noflat_exp (snd (fst a))) args ->
    Forall2 (fun '(t, e) v => exp_eval st sf stk g (Some t) e v) (map fst args) dvs ->
    forall k sfk, agree_noflat sf sfk ->
    let '(ca, args', k2) := atomize_argsP args k in
    (k <= k2)%positive /\
    map (fun a => (fst (fst a), snd a)) args' = map (fun a => (fst (fst a), snd a)) args /\
    exists sf2,
      RUN (denote_code ca va) (st, ((sfk, stk), g)) ≈ Ret ((st, ((sf2, stk), g)), tt) /\
      agree_except k k2 sfk sf2 /\
      Forall (fun a => atomized k k2 (snd (fst a))) args' /\
      Forall2 (fun '(t, e) v => exp_eval st sf2 stk g (Some t) e v) (map fst args') dvs.
  Proof.
    intros Hok. revert dvs. induction args as [|[[t e] pa] rest IH]; intros dvs Hvs k sfk Hagk.
    - inversion Hvs; subst. cbn. split; [lia|]. split; [reflexivity|]. exists sfk.
      split; [apply run_code_nil|]. split; [apply agree_except_refl|]. split; constructor.
    - inversion Hok as [|x0 r0 He_ok Hr_ok]; subst. cbn in Hvs.
      inversion Hvs as [|x1 y l1 dvs' Hy Hvs']; subst.
      cbn [atomize_argsP].
      pose proof (atomize_texpP_sound st stk g sf (t, e) y k sfk He_ok Hy Hagk) as H1.
      destruct (atomize_texpP (t, e) k) as [[c1 [t' a]] k1]. cbn [fst snd] in H1.
      destruct H1 as (Hk1 & -> & sf1 & Hrun1 & Hag1 & Hat1 & Hev1).
      specialize (IH Hr_ok dvs' Hvs' k1 sf1 (agree_noflat_except _ _ _ _ _ Hagk Hag1)).
      destruct (atomize_argsP rest k1) as [[cr ar] k2]. destruct IH as (Hk2 & Hty & sf2 & Hrun2 & Hag2 & Hat2 & Hev2).
      split; [lia|]. split; [cbn; f_equal; exact Hty|]. exists sf2. split; [|split; [|split]].
      + rewrite run_code_app, Hrun1, Eqit.bind_ret_l. cbv beta iota. exact Hrun2.
      + eapply (@agree_except_trans k k1 k1 k2 k k2); [lia|lia|lia|lia|exact Hag1|exact Hag2].
      + constructor; [cbn; eapply atomized_mono; [| |exact Hat1]; lia|].
        eapply Forall_impl; [|exact Hat2]. intros te; apply atomized_mono; lia.
      + cbn. constructor; [|exact Hev2]. destruct Hat1 as [_ Hok1].
        eapply exp_eval_ok_agree; [exact Hok1| |exact Hev1]. intros r0 Hr0. eapply (atom_ok_agree k k1 k2 sf1 sf2); [lia|exact Hag2|exact Hr0].
  Qed.

  (* ---------------------------------------------------------------- *)
  (** *** Instruction transfer *)

  Lemma run_exp_bind {R} t e v (k : dvalue -> CFGtop R) st sf stk g :
    exp_eval st sf stk g t e v ->
    RUN (ITree.bind (denote_exp' t e) k) (st, ((sf, stk), g)) ≈ RUN (k v) (st, ((sf, stk), g)).
  Proof. intros H. rewrite run_bind. rewrite run_exp' by exact H. rewrite Eqit.bind_ret_l. reflexivity. Qed.

  Lemma sim_exp' lo hi t e : noflat_exp e -> sim ctx (agree_except lo hi) (denote_exp' t e).
  Proof.
    intros He. rewrite denote_exp'_lift. apply sim_of_simM.
    apply exp_simM with (ok := noflat); [exact He|].
    intros a b Hab r Hr. symmetry. eapply agree_except_noflat; eauto.
  Qed.

  (** Instructions the transfer lemma covers: the non-call forms the emitter
      produces, with non-fresh destination and operands. *)
  Definition alloca_ok (anns : list (annotation dtyp)) : Prop :=
    forall a, In a anns -> match a with ANN_num_elements (_, e) => noflat_exp e | _ => True end.

  Definition instr_ok (i : instr_id * instr dtyp * list (metadata dtyp)) : Prop :=
    match i with
    | (IId id, INSTR_Op e, _) => noflat id /\ noflat_exp e
    | (IId id, INSTR_Load _ (_, p) _, _) => noflat id /\ noflat_exp p
    | (IVoid _, INSTR_Store (_, v) (_, p) _, _) => noflat_exp v /\ noflat_exp p
    | (IId id, INSTR_Alloca _ anns, _) => noflat id /\ alloca_ok anns
    | _ => False
    end.

  (** The operands evaluate (the premises of the [instr_*] lemmas). *)
  Definition instr_evals st sf stk g (i : instr_id * instr dtyp * list (metadata dtyp)) : Prop :=
    match i with
    | (_, INSTR_Op e, _) => exists v, exp_eval st sf stk g None e v
    | (_, INSTR_Load _ (pt, p) _, _) => exists a, exp_eval st sf stk g (Some pt) p a
    | (_, INSTR_Store (dt, v) (pt, p) _, _) =>
        (exists x, exp_eval st sf stk g (Some dt) v x) /\ (exists a, exp_eval st sf stk g (Some pt) p a)
    | _ => True
    end.

  Lemma sim_alloca_instr P id dt anns md :
    (forall a b, P a b -> forall v, P (upd_add a id v) (upd_add b id v)) ->
    (forall t e, In (ANN_num_elements (t, e)) anns -> sim ctx P (denote_exp' (Some t) e)) ->
    sim ctx P (denote_instr (IId id, INSTR_Alloca dt anns, md) va).
  Proof.
    intros HP He. cbn [denote_instr bind Monad_itree].
    apply sim_bind; [|intros; apply sim_ret].
    destruct (find _ anns) as [an|] eqn:Hf.
    - apply find_some in Hf as [Hin Hb]. destruct an; try discriminate; cbn.
      + destruct t as [t e]. apply sim_bind; [apply He, Hin|intros n].
        apply sim_bind; [apply sim_lift|intros n'].
        apply sim_bind; [apply sim_alloca|intros v]. apply sim_lwrite. intros a b H; apply HP, H.
    - cbn. apply sim_bind; [apply sim_alloca|intros v]. apply sim_lwrite. intros a b H; apply HP, H.
  Qed.

  (** (I1) Transfer for non-call instructions: running the flattened code
      from a frame [sf'] agreeing with [sf] outside [[lo, c)] is [eutt]
      to running the original instruction from [sf], up to agreement outside
      [[lo, c')]. *)
  Lemma flat_instr_transfer lo c i st sf sf' stk g :
    instr_ok i -> instr_evals st sf stk g i ->
    (lo <= c)%positive -> agree_except lo c sf sf' ->
    (c <= snd (flat_instrP i c))%positive /\
    eutt (res_mod lo (snd (flat_instrP i c)))
         (RUN (denote_instr i va) (st, ((sf, stk), g)))
         (RUN (denote_code (fst (flat_instrP i c)) va) (st, ((sf', stk), g))).
  Proof.
    intros Hok Hev Hlo Hag. pose proof (agree_except_noflat' _ _ _ _ Hag) as Hnf.
    destruct i as [[[id|n] ins] md]; destruct ins; cbn in Hok; try contradiction.
    - (* Op *)
      destruct Hok as [Hid He]. destruct Hev as [v Hv]. cbn [flat_instrP].
      pose proof (atomize_opP_sound st stk g sf op None v c sf' He Hv Hnf) as H.
      destruct (atomize_opP op c) as [[cc e'] c']. destruct H as (Hc & sf2 & Hrun & Hag2 & _ & _ & Hev').
      cbn [fst snd]. split; [exact Hc|].
      rewrite run_code_app, Hrun, Eqit.bind_ret_l. cbv beta iota. rewrite run_code_single.
      rewrite (run_instr_op _ _ _ _ _ _ _ _ Hv), (run_instr_op _ _ _ _ _ _ _ _ Hev').
      apply eqit_Ret. apply RR_intro. apply agree_except_add; [apply flat_in_noflat, Hid|].
      eapply (@agree_except_trans lo c c c' lo c'); [lia|lia|lia|lia|exact Hag|exact Hag2].
    - (* Alloca *)
      destruct Hok as [Hid Hal]. cbn [flat_instrP fst snd]. split; [lia|].
      rewrite run_code_single.
      match goal with |- eutt _ (RUN ?t _) (RUN ?t _) => assert (Hs : sim ctx (agree_except lo c) t) end.
      { apply sim_alloca_instr.
        - intros a b H v. apply agree_except_add; [apply flat_in_noflat, Hid|exact H].
        - intros t0 e Hin. apply sim_exp'. exact (Hal _ Hin). }
      apply Hs, Hag.
    - (* Load *)
      destruct ptr as [pt p]. destruct Hok as [Hid Hp]. destruct Hev as [a Ha]. cbn [flat_instrP].
      pose proof (atomize_texpP_sound st stk g sf (pt, p) a c sf' Hp Ha Hnf) as H.
      destruct (atomize_texpP (pt, p) c) as [[cc [pt' a']] c']. cbn [fst snd] in H.
      destruct H as (Hc & -> & sf2 & Hrun & Hag2 & _ & Hev'). cbn [fst snd]. split; [exact Hc|].
      rewrite run_code_app, Hrun, Eqit.bind_ret_l. cbv beta iota. rewrite run_code_single.
      cbn [denote_instr bind Monad_itree].
      rewrite (run_exp_bind _ _ _ _ _ _ _ _ Ha), (run_exp_bind _ _ _ _ _ _ _ _ Hev'). cbv beta.
      assert (Hag' : agree_except lo c' sf sf2)
        by (eapply (@agree_except_trans lo c c c' lo c'); [lia|lia|lia|lia|exact Hag|exact Hag2]).
      assert (Hid' : ~ flat_in lo c' id) by (apply flat_in_noflat, Hid).
      match goal with |- eutt _ (RUN ?t _) (RUN ?t _) => assert (Hs : sim ctx (agree_except lo c') t) end.
      { apply sim_bind; [apply sim_load|intros v]. apply sim_bind; [apply sim_freeze|intros v'].
        apply sim_lwrite. intros ? ? ?; apply agree_except_add; assumption. }
      apply Hs, Hag'.
    - (* Store *)
      destruct val as [dt ev]. destruct ptr as [pt ep]. destruct Hok as [Hv Hp].
      destruct Hev as [[x Hx] [a Ha]]. cbn [flat_instrP].
      pose proof (atomize_texpP_sound st stk g sf (dt, ev) x c sf' Hv Hx Hnf) as H1.
      destruct (atomize_texpP (dt, ev) c) as [[c1 [dt' a1]] n1]. cbn [fst snd] in H1.
      destruct H1 as (Hc1 & -> & sf1 & Hrun1 & Hag1 & Hat1 & Hev1).
      pose proof (atomize_texpP_sound st stk g sf (pt, ep) a n1 sf1 Hp Ha (agree_noflat_except _ _ _ _ _ Hnf Hag1)) as H2.
      destruct (atomize_texpP (pt, ep) n1) as [[c2 [pt' a2]] n2]. cbn [fst snd] in H2.
      destruct H2 as (Hc2 & -> & sf2 & Hrun2 & Hag2 & _ & Hev2).
      assert (Hev1' : exp_eval st sf2 stk g (Some dt) a1 x).
      { destruct Hat1 as [_ Hok1]. eapply exp_eval_ok_agree; [exact Hok1| |exact Hev1].
        intros r Hr. eapply (atom_ok_agree c n1 n2 sf1 sf2); [lia|exact Hag2|exact Hr]. }
      cbn [fst snd]. split; [lia|].
      rewrite run_code_app, Hrun1, Eqit.bind_ret_l. cbv beta iota.
      rewrite run_code_app, Hrun2, Eqit.bind_ret_l. cbv beta iota. rewrite run_code_single.
      cbn [denote_instr bind Monad_itree].
      rewrite (run_exp_bind _ _ _ _ _ _ _ _ Hx), (run_exp_bind _ _ _ _ _ _ _ _ Hev1'). cbv beta.
      rewrite (run_exp_bind _ _ _ _ _ _ _ _ Ha), (run_exp_bind _ _ _ _ _ _ _ _ Hev2). cbv beta.
      assert (Hag' : agree_except lo n2 sf sf2).
      { eapply (@agree_except_trans lo n1 n1 n2 lo n2); [lia|lia|lia|lia| |exact Hag2].
        eapply (@agree_except_trans lo c c n1 lo n1); [lia|lia|lia|lia|exact Hag|exact Hag1]. }
      match goal with |- eutt _ (RUN ?t _) (RUN ?t _) => assert (Hs : sim ctx (agree_except lo n2) t) end.
      { apply sim_bind; [|intros; apply sim_ret].
        destruct a as [d| |]; [destruct d| |]; first [apply sim_store | apply sim_raiseUB]. }
      apply Hs, Hag'.
  Qed.

  Lemma flat_instr_runs lo c i st sf sf' stk g st1 sf1 stk1 g1 :
    instr_ok i -> instr_evals st sf stk g i ->
    (lo <= c)%positive -> agree_except lo c sf sf' ->
    RUN (denote_instr i va) (st, ((sf, stk), g)) ≈ Ret ((st1, ((sf1, stk1), g1)), tt) ->
    (c <= snd (flat_instrP i c))%positive /\ exists sf1',
      RUN (denote_code (fst (flat_instrP i c)) va) (st, ((sf', stk), g)) ≈ Ret ((st1, ((sf1', stk1), g1)), tt) /\
      agree_except lo (snd (flat_instrP i c)) sf1 sf1'.
  Proof.
    intros Hok Hev Hlo Hag Hr. destruct (flat_instr_transfer lo c i st sf sf' stk g Hok Hev Hlo Hag) as [Hc He].
    split; [exact Hc|].
    eapply ret_eutt in He; [|exact Hr]. destruct He as [r2 [H2 HR]].
    eapply RR_inv; [exact HR|]. intros ? ? ? ? ? ? HP E1 E2. injection E1; intros; subst.
    eexists; split; [exact H2|exact HP].
  Qed.

  Lemma flat_instr_oom lo c i st sf sf' stk g :
    instr_ok i -> instr_evals st sf stk g i ->
    (lo <= c)%positive -> agree_except lo c sf sf' ->
    ends_in_oom (RUN (denote_instr i va) (st, ((sf, stk), g))) ->
    ends_in_oom (RUN (denote_code (fst (flat_instrP i c)) va) (st, ((sf', stk), g))).
  Proof.
    intros Hok Hev Hlo Hag H. destruct (flat_instr_transfer lo c i st sf sf' stk g Hok Hev Hlo Hag) as [_ He].
    eapply oom_eutt; [exact H|exact He].
  Qed.

  (** Calls: the flattened code is a pure prefix followed by the call with
      atomised callee and arguments, which evaluate to the same values in the
      frame reached by the prefix; the [instr_call] lemmas then apply to it. *)
  Lemma atomizeP_compound (e : exp dtyp) c :
    compound e = true -> exists k, snd (fst (atomizeP e c)) = EXP_Ident (ID_Local (flat_id k)).
  Proof.
    intros H. destruct e; cbn in H; try discriminate.
    - cbn [atomizeP]. destruct (atomizeP e1 c) as [[? ?] n1]. destruct (atomizeP e2 n1) as [[? ?] n2]. cbn. eauto.
    - cbn [atomizeP]. destruct (atomizeP e1 c) as [[? ?] n1]. destruct (atomizeP e2 n1) as [[? ?] n2]. cbn. eauto.
    - cbn [atomizeP]. destruct (atomizeP e c) as [[? ?] n1]. cbn. eauto.
    - destruct ptrval as [pt pe]. rewrite atomizeP_GEP. destruct (atomizeP pe c) as [[? ?] n1].
      destruct (atomize_idxsP idxs n1) as [[? ?] n2]. cbn. eauto.
  Qed.

  Lemma intrinsic_atomizeP (e : exp dtyp) c :
    IntrinsicsDefinitions.intrinsic_exp (snd (fst (atomizeP e c))) = IntrinsicsDefinitions.intrinsic_exp e.
  Proof.
    destruct (compound e) eqn:H.
    - destruct (atomizeP_compound e c H) as [k ->]. destruct e; cbn in H |- *; try discriminate; reflexivity.
    - rewrite atomizeP_atomic by exact H. reflexivity.
  Qed.

  Lemma flat_call_transfer id dt ef args anns obs md c st sf sf' stk g fv dvs :
    noflat_exp ef -> Forall (fun a => noflat_exp (snd (fst a))) args ->
    exp_eval st sf stk g None ef fv ->
    Forall2 (fun '(t, e) v => exp_eval st sf stk g (Some t) e v) (map fst args) dvs ->
    agree_noflat sf sf' ->
    let '(ci, c') := flat_instrP (id, INSTR_Call (dt, ef) args anns obs, md) c in
    (c <= c')%positive /\ exists pre af args' sf2,
      ci = (pre ++ [(id, INSTR_Call (dt, af) args' anns obs, md)])%list /\
      RUN (denote_code pre va) (st, ((sf', stk), g)) ≈ Ret ((st, ((sf2, stk), g)), tt) /\
      agree_except c c' sf' sf2 /\
      IntrinsicsDefinitions.intrinsic_exp af = IntrinsicsDefinitions.intrinsic_exp ef /\
      (compound ef = false -> af = ef) /\
      exp_eval st sf2 stk g None af fv /\
      map (fun a => (fst (fst a), snd a)) args' = map (fun a => (fst (fst a), snd a)) args /\
      Forall2 (fun '(t, e) v => exp_eval st sf2 stk g (Some t) e v) (map fst args') dvs.
  Proof.
    intros Hef Hargs Hf Hvs Hnf. cbn [flat_instrP atomize_texpP].
    pose proof (atomizeP_sound st stk g ef Hef c None fv sf Hf sf' Hnf) as H1.
    pose proof (intrinsic_atomizeP ef c) as Hi.
    pose proof (fun H => f_equal (fun x => snd (fst x)) (atomizeP_atomic ef c H)) as Ha.
    destruct (atomizeP ef c) as [[c1 af] n1]. cbn [fst snd] in Hi, Ha.
    destruct H1 as (Hc1 & sf1 & Hrun1 & Hag1 & Hat1 & Hev1).
    pose proof (atomize_argsP_sound st stk g sf args dvs Hargs Hvs n1 sf1 (agree_noflat_except _ _ _ _ _ Hnf Hag1)) as H2.
    destruct (atomize_argsP args n1) as [[c2 args'] n2]. destruct H2 as (Hc2 & Hty & sf2 & Hrun2 & Hag2 & _ & Hev2).
    split; [lia|]. exists (c1 ++ c2)%list, af, args', sf2. split; [rewrite app_assoc; reflexivity|].
    split; [rewrite run_code_app, Hrun1, Eqit.bind_ret_l; cbv beta iota; exact Hrun2|].
    split; [eapply (@agree_except_trans c n1 n1 n2 c n2); [lia|lia|lia|lia|exact Hag1|exact Hag2]|].
    split; [exact Hi|]. split; [exact Ha|]. split.
    - destruct Hat1 as [_ Hok1]. eapply exp_eval_ok_agree; [exact Hok1| |exact Hev1].
      intros r Hr. eapply (atom_ok_agree c n1 n2 sf1 sf2); [lia|exact Hag2|exact Hr].
    - split; [exact Hty|exact Hev2].
  Qed.

  (* ---------------------------------------------------------------- *)
  (** *** Terminator transfer *)

  Definition term_ok (tm : terminator dtyp) : Prop :=
    match tm with
    | TERM_Ret (_, e) | TERM_Br (_, e) _ _ | TERM_Switch (_, e) _ _ => noflat_exp e
    | TERM_Ret_void | TERM_Br_1 _ | TERM_Unreachable => True
    | _ => False
    end.

  Definition term_evals st sf stk g (tm : terminator dtyp) : Prop :=
    match tm with
    | TERM_Ret (t, e) | TERM_Br (t, e) _ _ | TERM_Switch (t, e) _ _ => exists v, exp_eval st sf stk g (Some t) e v
    | _ => True
    end.

  Lemma flat_term_transfer lo c tid tm tmd st sf sf' stk g :
    term_ok tm -> term_evals st sf stk g tm ->
    (lo <= c)%positive -> agree_except lo c sf sf' ->
    (c <= snd (flat_termP tm c))%positive /\
    eutt (res_mod lo (snd (flat_termP tm c)))
         (RUN (denote_terminator (tid, tm, tmd)) (st, ((sf, stk), g)))
         (RUN (ITree.bind (denote_code (fst (fst (flat_termP tm c))) va)
                          (fun _ => denote_terminator (tid, snd (fst (flat_termP tm c)), tmd)))
              (st, ((sf', stk), g))).
  Proof.
    intros Hok Hev Hlo Hag. pose proof (agree_except_noflat' _ _ _ _ Hag) as Hnf.
    destruct tm; cbn in Hok; try contradiction;
      try (cbn [flat_termP fst snd]; split; [lia|];
           rewrite run_bind, run_code_nil, Eqit.bind_ret_l; cbv beta iota;
           match goal with |- eutt _ (RUN ?t _) (RUN ?t _) => assert (Hs : sim ctx (agree_except lo c) t) end;
           [cbn [denote_terminator]; first [apply sim_ret | apply sim_raiseUB] | apply Hs, Hag]).
    all: destruct v as [t e]; destruct Hev as [v Hv]; cbn [flat_termP].
    all: pose proof (atomize_texpP_sound st stk g sf (t, e) v c sf' Hok Hv Hnf) as H;
      destruct (atomize_texpP (t, e) c) as [[cc [t' a]] c']; cbn [fst snd] in H |- *;
      destruct H as (Hc & -> & sf2 & Hrun & Hag2 & _ & Hev'); split; [exact Hc| ];
      rewrite run_bind, Hrun, Eqit.bind_ret_l; cbv beta iota;
      cbn [denote_terminator bind Monad_itree];
      rewrite (run_exp_bind _ _ _ _ _ _ _ _ Hv), (run_exp_bind _ _ _ _ _ _ _ _ Hev'); cbv beta;
      assert (Hag' : agree_except lo c' sf sf2)
        by (eapply (@agree_except_trans lo c c c' lo c'); [lia|lia|lia|lia|exact Hag|exact Hag2]);
      match goal with |- eutt _ (RUN ?t _) (RUN ?t _) => assert (Hs : sim ctx (agree_except lo c') t) end;
      [|apply Hs, Hag'].
    - apply sim_ret.
    - destruct v as [d| |]; [destruct d| |];
        try match goal with |- sim _ _ (raise _) => apply sim_raise | |- sim _ _ (raiseUB _) => apply sim_raiseUB end.
      destruct sz as [p|p|]; cbv iota beta; [apply sim_raise|apply sim_raise|].
      destruct (VellvmIntegers.equ _ _); apply sim_ret.
    - destruct (dvalue_is_poison v); [apply sim_raiseUB|].
      apply sim_bind; [apply sim_lift|intros; apply sim_ret].
  Qed.


  (* ---------------------------------------------------------------- *)
  (** *** Stepping through a flattened block

      [flat_tail l tmt c K] is the "code then terminator then K" tree of
      the flattening (at counter [c]) of a block with code [l] and
      terminator [tmt].  [flat_block_tail] identifies the [tail_of]-shape
      of [fst (flat_blockP b c)] with [flat_tail (blk_code b) (blk_term b) c];
      the [flat_tail_*] lemmas then step through it one original
      instruction (resp. the terminator) at a time. *)

  Definition flat_tail {R} (l : code dtyp) (tmt : instr_id * terminator dtyp * list (metadata dtyp))
             (c : positive) (K : block_id + dvalue -> CFGtop R) : CFGtop R :=
    ITree.bind
      (ITree.bind (denote_code (fst (flat_codeP l c)) va) (fun _ =>
       ITree.bind (denote_code (fst (fst (flat_termP (snd (fst tmt)) (snd (flat_codeP l c))))) va) (fun _ =>
       denote_terminator (fst (fst tmt), snd (fst (flat_termP (snd (fst tmt)) (snd (flat_codeP l c)))), snd tmt))))
      K.

  Lemma flat_block_tail {R} (b : LLVMAst.block dtyp) c (K : block_id + dvalue -> CFGtop R) s :
    RUN (ITree.bind (denote_code (blk_code (fst (flat_blockP b c))) va ;;
                     denote_terminator (blk_term (fst (flat_blockP b c)))) K) s
    ≈ RUN (flat_tail (blk_code b) (blk_term b) c K) s.
  Proof.
    unfold flat_tail. rewrite flat_blockP_code, flat_blockP_term. cbn [bind Monad_itree].
    rewrite !run_bind. apply eutt_eq_bind'.
    - rewrite run_code_app, Eqit.bind_bind. apply eutt_eq_bind. intros [s' []].
      rewrite run_bind. reflexivity.
    - intros [s' r]. reflexivity.
  Qed.

  Lemma flat_tail_cons {R} i l tmt c (K : block_id + dvalue -> CFGtop R) s :
    RUN (flat_tail (i :: l) tmt c K) s
    ≈ ITree.bind (RUN (denote_code (fst (flat_instrP i c)) va) s)
                 (fun '(s', _) => RUN (flat_tail l tmt (snd (flat_instrP i c)) K) s').
  Proof.
    unfold flat_tail. rewrite flat_codeP_cons. cbn [fst snd].
    rewrite !run_bind, run_code_app, !Eqit.bind_bind. apply eutt_eq_bind. intros [s' []].
    rewrite !run_bind, !Eqit.bind_bind. apply eutt_eq_bind. intros [s'' []]. reflexivity.
  Qed.

  Lemma ends_in_oom_bind {A B} (t : MCFGbot A) (k : A -> MCFGbot B) :
    ends_in_oom t -> ends_in_oom (ITree.bind t k).
  Proof.
    intros [k0 H]. exists (fun x => ITree.bind (k0 x) k). rewrite H, bind_vis. reflexivity.
  Qed.

  (** One non-call instruction: the original runs from [sf] to [sf1];
      the flattened tail from any [sf'] agreeing with [sf] off
      [[lo, c)] steps to the rest of the tail, in a frame agreeing with
      [sf1] off [[lo, c')]. *)
  Lemma flat_tail_instr {R} lo c i l tmt (K : block_id + dvalue -> CFGtop R)
        st sf sf' stk g st1 sf1 stk1 g1 :
    instr_ok i -> instr_evals st sf stk g i ->
    (lo <= c)%positive -> agree_except lo c sf sf' ->
    RUN (denote_instr i va) (st, ((sf, stk), g)) ≈ Ret ((st1, ((sf1, stk1), g1)), tt) ->
    (c <= snd (flat_instrP i c))%positive /\ exists sf1',
      agree_except lo (snd (flat_instrP i c)) sf1 sf1' /\
      RUN (flat_tail (i :: l) tmt c K) (st, ((sf', stk), g))
      ≈ RUN (flat_tail l tmt (snd (flat_instrP i c)) K) (st1, ((sf1', stk1), g1)).
  Proof.
    intros Hok Hev Hlo Hag Hr.
    destruct (flat_instr_runs lo c i st sf sf' stk g st1 sf1 stk1 g1 Hok Hev Hlo Hag Hr) as (Hc & sf1' & H1 & H2).
    split; [exact Hc|]. exists sf1'. split; [exact H2|].
    rewrite flat_tail_cons, H1, Eqit.bind_ret_l. reflexivity.
  Qed.

  Lemma flat_tail_instr_oom {R} lo c i l tmt (K : block_id + dvalue -> CFGtop R) st sf sf' stk g :
    instr_ok i -> instr_evals st sf stk g i ->
    (lo <= c)%positive -> agree_except lo c sf sf' ->
    ends_in_oom (RUN (denote_instr i va) (st, ((sf, stk), g))) ->
    ends_in_oom (RUN (flat_tail (i :: l) tmt c K) (st, ((sf', stk), g))).
  Proof.
    intros Hok Hev Hlo Hag H.
    pose proof (flat_instr_oom lo c i st sf sf' stk g Hok Hev Hlo Hag H) as H1.
    rewrite flat_tail_cons. apply ends_in_oom_bind, H1.
  Qed.

  (** A call: the atomisation prefix runs purely; what remains is the
      atomised call [INSTR_Call (dt, af) args'] in frame [sf2], whose
      operands evaluate to the original values (so [instr_call] /
      [oom_instr_call] apply to it), followed by the rest of the tail. *)
  Lemma flat_tail_call {R} id dt ef args anns obs md l tmt c (K : block_id + dvalue -> CFGtop R)
        st sf sf' stk g fv dvs :
    noflat_exp ef -> Forall (fun a => noflat_exp (snd (fst a))) args ->
    exp_eval st sf stk g None ef fv ->
    Forall2 (fun '(t, e) v => exp_eval st sf stk g (Some t) e v) (map fst args) dvs ->
    agree_noflat sf sf' ->
    let c' := snd (flat_instrP (id, INSTR_Call (dt, ef) args anns obs, md) c) in
    (c <= c')%positive /\ exists af args' sf2,
      agree_except c c' sf' sf2 /\
      IntrinsicsDefinitions.intrinsic_exp af = IntrinsicsDefinitions.intrinsic_exp ef /\
      (compound ef = false -> af = ef) /\
      exp_eval st sf2 stk g None af fv /\
      map (fun a => (fst (fst a), snd a)) args' = map (fun a => (fst (fst a), snd a)) args /\
      Forall2 (fun '(t, e) v => exp_eval st sf2 stk g (Some t) e v) (map fst args') dvs /\
      RUN (flat_tail ((id, INSTR_Call (dt, ef) args anns obs, md) :: l) tmt c K) (st, ((sf', stk), g))
      ≈ ITree.bind (RUN (denote_instr (id, INSTR_Call (dt, af) args' anns obs, md) va) (st, ((sf2, stk), g)))
                   (fun '(s', _) => RUN (flat_tail l tmt c' K) s').
  Proof.
    intros Hef Hargs Hf Hvs Hnf c'.
    pose proof (flat_call_transfer id dt ef args anns obs md c st sf sf' stk g fv dvs Hef Hargs Hf Hvs Hnf) as H.
    subst c'.
    destruct (flat_instrP (id, INSTR_Call (dt, ef) args anns obs, md) c) as [ci n] eqn:E. cbn [fst snd].
    destruct H as (Hc & pre & af & args' & sf2 & -> & Hrun & Hag & Hi & Ha & Hev & Hty & Hevs).
    split; [exact Hc|]. exists af, args', sf2. repeat (split; [assumption|]).
    rewrite flat_tail_cons, E. cbn [fst snd]. rewrite run_code_app, Hrun, Eqit.bind_ret_l. cbv beta iota.
    rewrite run_code_single. reflexivity.
  Qed.

  (** The terminator (after all code has been stepped). *)
  Lemma flat_tail_term {R} lo c tid tm tmd (K : block_id + dvalue -> CFGtop R)
        st sf sf' stk g st1 sf1 stk1 g1 r :
    term_ok tm -> term_evals st sf stk g tm ->
    (lo <= c)%positive -> agree_except lo c sf sf' ->
    RUN (denote_terminator (tid, tm, tmd)) (st, ((sf, stk), g)) ≈ Ret ((st1, ((sf1, stk1), g1)), r) ->
    (c <= snd (flat_termP tm c))%positive /\ exists sf1',
      agree_except lo (snd (flat_termP tm c)) sf1 sf1' /\
      RUN (flat_tail [] (tid, tm, tmd) c K) (st, ((sf', stk), g)) ≈ RUN (K r) (st1, ((sf1', stk1), g1)).
  Proof.
    intros Hok Hev Hlo Hag Hr.
    destruct (flat_term_transfer lo c tid tm tmd st sf sf' stk g Hok Hev Hlo Hag) as [Hc He].
    destruct (ret_eutt _ _ _ _ Hr He) as (r2 & Hr2 & HRR).
    split; [exact Hc|].
    apply (RR_inv _ _ _ _ HRR). intros st0 sfa sfb stk0 g0 x HP E1 E2.
    inversion E1; subst. exists sfb. split; [exact HP|].
    unfold flat_tail. cbn [flat_codeP fst snd].
    rewrite run_bind, run_bind, run_code_nil, Eqit.bind_ret_l. cbv beta iota.
    rewrite Hr2, Eqit.bind_ret_l. reflexivity.
  Qed.

  Lemma flat_tail_term_oom {R} lo c tid tm tmd (K : block_id + dvalue -> CFGtop R) st sf sf' stk g :
    term_ok tm -> term_evals st sf stk g tm ->
    (lo <= c)%positive -> agree_except lo c sf sf' ->
    ends_in_oom (RUN (denote_terminator (tid, tm, tmd)) (st, ((sf, stk), g))) ->
    ends_in_oom (RUN (flat_tail [] (tid, tm, tmd) c K) (st, ((sf', stk), g))).
  Proof.
    intros Hok Hev Hlo Hag H.
    destruct (flat_term_transfer lo c tid tm tmd st sf sf' stk g Hok Hev Hlo Hag) as [_ He].
    pose proof (oom_eutt _ _ _ H He) as H1.
    unfold flat_tail. cbn [flat_codeP fst snd].
    rewrite run_bind, run_bind, run_code_nil, Eqit.bind_ret_l. cbv beta iota.
    apply ends_in_oom_bind, H1.
  Qed.

End Transport.
