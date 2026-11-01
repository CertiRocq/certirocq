From Stdlib Require Import ZArith List Lia Program Morphisms DecimalPos DecimalNat DecimalZ DecimalFacts.
From ITree Require Import ITree Eq.Eqit Events.State Events.StateFacts.
From ExtLib Require Import Structures.Monads.
From Vellvm Require Import
  Utils Syntax Params Numeric.Integers
  Interfaces.Memory Implementations.Memory
  Semantics.DynamicValues Semantics.LLVMEvents Semantics.Denotation Semantics.Operations
  Semantics.InterpretationStack Handlers.
From CertiRocq.CodegenLLVM Require Import LambdaANF_to_LLVM_statement LLVM_interp_lemmas.
Import MonadNotation.
Open Scope monad_scope.
Open Scope Z_scope.

Lemma modulus64 : @Integers.modulus 64 = 2^64.
Proof. rewrite Integers.modulus_def. reflexivity. Qed.

Lemma unsigned_repr64 z : @Integers.unsigned 64 (Integers.repr z) = z mod 2^64.
Proof. rewrite Integers.unsigned_repr_eq, modulus64. reflexivity. Qed.

Lemma I64_eq a b : a mod 2^64 = b mod 2^64 -> I64 a = I64 b.
Proof.
  intros H. unfold I64. f_equal. f_equal.
  rewrite <- (Integers.repr_unsigned (Integers.repr a)), <- (Integers.repr_unsigned (Integers.repr b)).
  rewrite !unsigned_repr64, H. reflexivity.
Qed.

Lemma repr_mod64 a : @Integers.repr 64 (a mod 2^64) = Integers.repr a.
Proof.
  rewrite <- (Integers.repr_unsigned (Integers.repr a)),
          <- (Integers.repr_unsigned (Integers.repr (a mod 2^64))).
  rewrite !unsigned_repr64, Z.mod_mod by lia. reflexivity.
Qed.

Lemma repr_eq64 a b : a mod 2^64 = b mod 2^64 -> @Integers.repr 64 a = Integers.repr b.
Proof. intros H. rewrite <- repr_mod64, H, repr_mod64. reflexivity. Qed.

Lemma int_shl1 a : @Integers.shl 64 (Integers.repr a) (Integers.repr 1) = Integers.repr (2*a).
Proof.
  unfold Integers.shl. rewrite !unsigned_repr64. change (1 mod 2^64) with 1.
  rewrite Z.shiftl_mul_pow2 by lia. apply repr_eq64.
  rewrite Z.mul_comm. change (2^1) with 2. rewrite Z.mul_mod_idemp_r by lia. reflexivity.
Qed.

Lemma int_or1_even a : @Integers.or 64 (Integers.repr (2*a)) (Integers.repr 1) = Integers.repr (2*a+1).
Proof.
  unfold Integers.or. rewrite !unsigned_repr64. change (1 mod 2^64) with 1.
  assert (Hl : Z.land ((2*a) mod 2^64) 1 = 0).
  { change 1 with (Z.ones 1). rewrite Z.land_ones by lia. change (2^1) with 2.
    rewrite <- Zmod_div_mod; try lia. exists (2^63). reflexivity. }
  pose proof (Z.add_lor_land ((2*a) mod 2^64) 1) as E. rewrite Hl, Z.add_0_r in E.
  rewrite E. apply repr_eq64. rewrite Z.add_mod_idemp_l by lia. reflexivity.
Qed.

Lemma int_and1 a : @Integers.and 64 (Integers.repr a) (Integers.repr 1) = Integers.repr (a mod 2).
Proof.
  unfold Integers.and. rewrite !unsigned_repr64. change (1 mod 2^64) with 1.
  change 1 with (Z.ones 1). rewrite Z.land_ones by lia. change (2^1) with 2.
  rewrite <- Zmod_div_mod; try lia; try reflexivity. exists (2^63). reflexivity.
Qed.

Lemma int_and1023 a : @Integers.and 64 (Integers.repr a) (Integers.repr 1023) = Integers.repr (a mod 1024).
Proof.
  unfold Integers.and. rewrite !unsigned_repr64. change (1023 mod 2^64) with 1023.
  change 1023 with (Z.ones 10). rewrite Z.land_ones by lia. change (2^10) with 1024.
  rewrite <- Zmod_div_mod; try lia; try reflexivity. exists (2^54). reflexivity.
Qed.

Lemma int_sub a b : @Integers.sub 64 (Integers.repr a) (Integers.repr b) = Integers.repr (a - b).
Proof.
  unfold Integers.sub. rewrite !unsigned_repr64. apply repr_eq64.
  rewrite Zminus_mod_idemp_l, Zminus_mod_idemp_r. reflexivity.
Qed.

Lemma signed_repr64 a : -2^63 <= a < 2^63 -> @Integers.signed 64 (Integers.repr a) = a.
Proof.
  intros H. apply Integers.signed_repr.
  unfold Integers.min_signed, Integers.max_signed, Integers.half_modulus. cbn. lia.
Qed.

Lemma half_modulus64 : @Integers.half_modulus 64 = 2^63.
Proof. reflexivity. Qed.

Lemma int_shr1 a : @Integers.shr 64 (Integers.repr a) (Integers.repr 1)
                   = Integers.repr (@Integers.signed 64 (Integers.repr a) / 2).
Proof.
  unfold Integers.shr. rewrite (unsigned_repr64 1). change (1 mod 2^64) with 1.
  rewrite Z.shiftr_div_pow2 by lia. reflexivity.
Qed.

Lemma int_eq64 a b : @Integers.eq 64 (Integers.repr a) (Integers.repr b) = Z.eqb (a mod 2^64) (b mod 2^64).
Proof.
  unfold Integers.eq. rewrite !unsigned_repr64.
  destruct (Rocqlib.zeq _ _) as [E|E]; symmetry; [apply Z.eqb_eq|apply Z.eqb_neq]; auto.
Qed.

Lemma int_ltu64 a b : @Integers.ltu 64 (Integers.repr a) (Integers.repr b) = Z.ltb (a mod 2^64) (b mod 2^64).
Proof.
  unfold Integers.ltu. rewrite !unsigned_repr64.
  destruct (Rocqlib.zlt _ _) as [E|E]; symmetry; [apply Z.ltb_lt|apply Z.ltb_ge]; lia.
Qed.


(** ** Values *)

Definition I1 (b : bool) : dvalue :=
  DVALUE_Base (DVALUE_I 1 (if b then @Integers.one 1 else @Integers.zero 1)).
Definition I32 (z : Z) : dvalue := DVALUE_Base (DVALUE_I 32 (@Integers.repr 32 z)).
Definition Ptr (p : ptr) : dvalue := DVALUE_Base (DVALUE_Pointer p).

(** ** Pure operations on i64 *)

Lemma eval_shl1 a : eval_iop (Shl false false) (I64 a) (I64 1) = EOU.raise_ret (I64 (2*a)).
Proof. unfold I64. cbn -[Z.mul Integers.shl]. rewrite int_shl1. reflexivity. Qed.

Lemma eval_or1_even a : eval_iop (Or false) (I64 (2*a)) (I64 1) = EOU.raise_ret (I64 (2*a+1)).
Proof. unfold I64. cbn -[Z.mul Z.add Integers.or]. rewrite int_or1_even. reflexivity. Qed.

Lemma eval_and1 a : eval_iop And (I64 a) (I64 1) = EOU.raise_ret (I64 (a mod 2)).
Proof. unfold I64. cbn -[Z.modulo Integers.and]. rewrite int_and1. reflexivity. Qed.

(** The tag of a header word sits in its low 10 bits. *)
Lemma eval_and1023 a : eval_iop And (I64 a) (I64 1023) = EOU.raise_ret (I64 (a mod 1024)).
Proof. unfold I64. cbn -[Z.modulo Integers.and]. rewrite int_and1023. reflexivity. Qed.

(** [header_word]: [(ga << 10) | go], so its low 10 bits are [go] when [go < 1024]. *)
Lemma header_word_tag (ga go : nat) :
  (go < 1024)%nat -> Z.of_nat (Nat.lor (Nat.shiftl ga 10) go) mod 1024 = Z.of_nat go.
Proof.
  intros Hgo. change 1024 with (Z.of_nat 1024). rewrite <- Nat2Z.inj_mod. f_equal.
  change 1024%nat with (2 ^ 10)%nat in *.
  apply Nat.bits_inj. intros i.
  rewrite <- (Nat.mod_small go (2 ^ 10)) at 2 by exact Hgo.
  destruct (Nat.lt_ge_cases i 10) as [Hi|Hi].
  - rewrite !Nat.mod_pow2_bits_low by exact Hi. rewrite Nat.lor_spec, Nat.shiftl_spec_low by exact Hi.
    reflexivity.
  - rewrite !Nat.mod_pow2_bits_high by exact Hi. reflexivity.
Qed.

Lemma eval_ashr1 a :
  eval_iop (AShr false) (I64 a) (I64 1) = EOU.raise_ret (I64 (@Integers.signed 64 (Integers.repr a) / 2)).
Proof. unfold I64. cbn -[Z.div Integers.shr Integers.signed]. rewrite int_shr1. reflexivity. Qed.

Lemma eval_ashr1_small a : -2^63 <= a < 2^63 ->
  eval_iop (AShr false) (I64 a) (I64 1) = EOU.raise_ret (I64 (a / 2)).
Proof. intros H. rewrite eval_ashr1, signed_repr64 by exact H. reflexivity. Qed.

Lemma eval_sub a b : eval_iop (Sub false false) (I64 a) (I64 b) = EOU.raise_ret (I64 (a - b)).
Proof. unfold I64. cbn -[Z.sub Integers.sub]. rewrite int_sub. reflexivity. Qed.

Lemma eval_icmp_eq a b :
  eval_icmp false Eq (I64 a) (I64 b) = EOU.raise_ret (I1 (Z.eqb (a mod 2^64) (b mod 2^64))).
Proof.
  unfold I64, I1. cbn -[Z.modulo Z.pow Integers.eq]. rewrite int_eq64.
  destruct (_ =? _); reflexivity.
Qed.

Lemma eval_icmp_uge a b :
  eval_icmp false Uge (I64 a) (I64 b) = EOU.raise_ret (I1 (Z.leb (b mod 2^64) (a mod 2^64))).
Proof.
  unfold I64, I1. cbn -[Z.modulo Z.pow Integers.ltu]. rewrite int_ltu64.
  rewrite <- Z.leb_antisym. destruct (_ <=? _); reflexivity.
Qed.


(** ** Pointers and integers *)

Lemma int_to_ptr_total z pr : 0 <= z < 2^64 ->
  exists q, int_to_ptr z pr = EOU.raise_ret q /\ ptr_to_int q = z /\ ptr_provenance q = pr.
Proof.
  intros Hz.
  assert (Hq : int_to_ptr z pr = EOU.raise_ret ((@Integers.repr 64 z, pr) : ptr)).
  { cbn. unfold IPtrFinite.from_Z_bits.
    assert (E : (z <=? @Integers.max_unsigned 64) && (z >=? 0) = true).
    { unfold Integers.max_unsigned. rewrite modulus64.
      apply andb_true_intro; split; [apply Z.leb_le|apply Z.geb_le]; lia. }
    rewrite E. reflexivity. }
  eexists; split; [exact Hq|split].
  - eapply ptr_to_int_int_to_ptr; eauto.
  - eapply int_to_ptr_provenance; eauto.
Qed.

Lemma conv_ptrtoint st p :
  memS_runs st (handle_memoryM (Conv Ptrtoint DTYPE_Pointer (Ptr p) (DTYPE_I 64))) st (I64 (ptr_to_int p)).
Proof. cbn. exact (MR_ret _ _). Qed.

Lemma conv_inttoptr st z q :
  int_to_ptr (z mod 2^64) wildcard_prov = EOU.raise_ret q ->
  memS_runs st (handle_memoryM (Conv Inttoptr (DTYPE_I 64) (I64 z) DTYPE_Pointer)) st (Ptr q).
Proof.
  intros H. cbn -[int_to_ptr Integers.unsigned Integers.repr wildcard_prov].
  rewrite unsigned_repr64.
  match goal with |- context [int_to_ptr ?x ?y] =>
    replace (int_to_ptr x y) with (EOU.raise_ret q) by (rewrite <- H; reflexivity) end.
  cbn. exact (MR_ret _ _).
Qed.

(** ** GEP *)

Definition tinfo_dt : dtyp :=
  DTYPE_Struct false [(DTYPE_Pointer : dtyp); (DTYPE_Pointer : dtyp); (DTYPE_Pointer : dtyp);
                      DTYPE_Array false 1024 (DTYPE_I 64); (DTYPE_Pointer : dtyp); (DTYPE_I 64 : dtyp)].
Definition frame_dt : dtyp :=
  DTYPE_Struct false [(DTYPE_Pointer : dtyp); (DTYPE_Pointer : dtyp); (DTYPE_Pointer : dtyp)].

Ltac gep_finish H q :=
  match goal with |- context [int_to_ptr ?x ?y] =>
    replace (int_to_ptr x y) with (EOU.raise_ret (X := ptr) q) by (rewrite <- H; f_equal; first [lia | reflexivity | (rewrite ?Z.mul_0_r; cbn -[Z.mul Z.add]; lia)])
  end; reflexivity.

Ltac gep_cbn :=
  cbn -[int_to_ptr ptr_to_int ptr_provenance];
  repeat match goal with |- context [Pos.to_nat ?k] =>
    let v := eval vm_compute in (Pos.to_nat k) in change (Pos.to_nat k) with v end;
  cbn -[int_to_ptr ptr_to_int ptr_provenance].

Lemma eval_gep_i64 p i q : -2^63 <= i < 2^63 -> ptr_off p (8 * i) q ->
  eval_gep (DTYPE_I 64) (Ptr p) [I64 i] = EOU.raise_ret (Ptr q).
Proof.
  intros Hi H. unfold ptr_off in H. unfold I64, Ptr.
  cbn -[int_to_ptr ptr_to_int ptr_provenance Integers.signed Integers.repr Z.mul].
  rewrite signed_repr64 by exact Hi. gep_finish H q.
Qed.

Lemma eval_gep_tinfo p n off q :
  (n, off) = (0%nat, 0) \/ (n, off) = (1%nat, 8) \/ (n, off) = (4%nat, 8216) \/ (n, off) = (5%nat, 8224) ->
  ptr_off p off q ->
  eval_gep tinfo_dt (Ptr p) [I32 0; I32 (Z.of_nat n)] = EOU.raise_ret (Ptr q).
Proof.
  intros Hn H. unfold ptr_off in H. unfold I32, Ptr.
  destruct Hn as [E|[E|[E|E]]]; inversion E; subst; clear E.
  all: gep_cbn; gep_finish H q.
Qed.

Lemma eval_gep_frame p n q :
  (n <= 2)%nat -> ptr_off p (8 * Z.of_nat n) q ->
  eval_gep frame_dt (Ptr p) [I32 0; I32 (Z.of_nat n)] = EOU.raise_ret (Ptr q).
Proof.
  intros Hn H. unfold ptr_off in H. unfold I32, Ptr.
  destruct n as [|[|[|n]]]; try lia;
  gep_cbn; gep_finish H q.
Qed.

Lemma eval_gep_arr p n i q : -2^63 <= i < 2^63 -> ptr_off p (8 * i) q ->
  eval_gep (DTYPE_Array false n (DTYPE_I 64)) (Ptr p) [I32 0; I64 i] = EOU.raise_ret (Ptr q).
Proof.
  intros Hi H. unfold ptr_off in H. unfold I64, I32, Ptr.
  cbn -[int_to_ptr ptr_to_int ptr_provenance Integers.signed Integers.repr Z.mul].
  rewrite signed_repr64 by exact Hi. change (@Integers.signed 32 (Integers.repr 0)) with 0. gep_finish H q.
Qed.

(** ** Integer literals *)

Lemma DecimalPos_of_lu_nat d :
  DecimalPos.Unsigned.of_lu d = N.of_nat (DecimalNat.Unsigned.of_lu d).
Proof. induction d; cbn [DecimalPos.Unsigned.of_lu DecimalNat.Unsigned.of_lu]; lia. Qed.

Lemma denote_int_syntax_nat n : denote_int_syntax (Nat.to_num_int n) = Z.of_nat n.
Proof.
  unfold denote_int_syntax. cbn. unfold Z.of_uint.
  rewrite DecimalPos.Unsigned.of_uint_alt, DecimalNat.Unsigned.to_uint_alt, DecimalFacts.rev_rev.
  rewrite DecimalPos_of_lu_nat, DecimalNat.Unsigned.of_to_lu. lia.
Qed.

Lemma denote_int_syntax_Z z : denote_int_syntax (Z.to_num_int z) = z.
Proof. unfold denote_int_syntax. cbn. apply DecimalZ.of_to. Qed.

(** ** Expression evaluation *)

(** [e] evaluates to [v] at type [t], leaving all of the state unchanged. *)
Definition exp_eval (st : state) (sf : stack_frame) (stk : stack) (g : global_env)
           (t : option dtyp) (e : exp dtyp) (v : dvalue) : Prop :=
  interp_mcfg (denote_exp t e) (st, ((sf, stk), g)) ≈ Ret ((st, ((sf, stk), g)), v).

Section ExpEval.
  Context (st : state) (sf : stack_frame) (stk : stack) (g : global_env).
  Notation EE := (exp_eval st sf stk g).

  Lemma exp_eval_local t id v :
    RM.find id (stack_vars sf) = Some v -> EE t (EXP_Ident (ID_Local id)) v.
  Proof.
    intros H. unfold exp_eval. cbn. unfold lread.
    rewrite interp_mcfg_lread by eauto. rewrite upd_local_sf_id. reflexivity.
  Qed.

  Lemma exp_eval_global t id v :
    RM.find id g = Some v -> EE t (EXP_Ident (ID_Global id)) v.
  Proof.
    intros H. unfold exp_eval. cbn. unfold gread.
    rewrite interp_mcfg_gread by eauto. reflexivity.
  Qed.

  Lemma exp_eval_int64 x :
    EE (Some (DTYPE_I 64 : dtyp)) (EXP_Integer x) (I64 (denote_int_syntax x)).
  Proof. unfold exp_eval. cbn. apply interp_mcfg_ret. Qed.

  Lemma exp_eval_int32 x :
    EE (Some (DTYPE_I 32 : dtyp)) (EXP_Integer x) (I32 (denote_int_syntax x)).
  Proof. unfold exp_eval. cbn. apply interp_mcfg_ret. Qed.

  Lemma exp_eval_lit64 n :
    EE (Some (DTYPE_I 64 : dtyp)) (EXP_Integer (Nat.to_num_int n)) (I64 (Z.of_nat n)).
  Proof. rewrite <- denote_int_syntax_nat. apply exp_eval_int64. Qed.

  Lemma exp_eval_lit32 n :
    EE (Some (DTYPE_I 32 : dtyp)) (EXP_Integer (Nat.to_num_int n)) (I32 (Z.of_nat n)).
  Proof. rewrite <- denote_int_syntax_nat. apply exp_eval_int32. Qed.

  Lemma exp_eval_litZ z :
    EE (Some (DTYPE_I 64 : dtyp)) (EXP_Integer (Z.to_num_int z)) (I64 z).
  Proof. rewrite <- (denote_int_syntax_Z z) at 2. apply exp_eval_int64. Qed.

  Lemma exp_eval_ibinop t iop dt e1 e2 v1 v2 v :
    EE (Some dt) e1 v1 -> EE (Some dt) e2 v2 ->
    eval_iop iop v1 v2 = EOU.raise_ret v ->
    EE t (OP_IBinop iop dt e1 e2) v.
  Proof.
    intros H1 H2 Hop. unfold exp_eval in *. cbn [denote_exp bind Monad_itree].
    rewrite interp_mcfg_bind, H1, Eqit.bind_ret_l. cbn beta iota.
    rewrite interp_mcfg_bind, H2, Eqit.bind_ret_l. cbn beta iota.
    rewrite Hop. apply interp_mcfg_lift_ret.
  Qed.

  Lemma exp_eval_icmp t ss cmp dt e1 e2 v1 v2 v :
    EE (Some dt) e1 v1 -> EE (Some dt) e2 v2 ->
    eval_icmp ss cmp v1 v2 = EOU.raise_ret v ->
    EE t (OP_ICmp ss cmp dt e1 e2) v.
  Proof.
    intros H1 H2 Hop. unfold exp_eval in *. cbn [denote_exp bind Monad_itree].
    rewrite interp_mcfg_bind, H1, Eqit.bind_ret_l. cbn beta iota.
    rewrite interp_mcfg_bind, H2, Eqit.bind_ret_l. cbn beta iota.
    rewrite Hop. apply interp_mcfg_lift_ret.
  Qed.

  (** Impure conversions are [Conv] memory events; [memS_runs] with the same
      state on both sides says that they do not touch the memory. *)
  Lemma exp_eval_conv_impure t ct t1 e t2 v v' :
    EE (Some t1) e v ->
    memS_runs st (handle_memoryM (Conv ct t1 v t2)) st v' ->
    EE t (OP_Conversion (CONV_Impure ct) t1 e t2) v'.
  Proof.
    intros H Hc. unfold exp_eval in *. cbn [denote_exp bind Monad_itree].
    rewrite interp_mcfg_bind, H, Eqit.bind_ret_l. cbn beta iota.
    cbn [convert]. unfold conv. apply interp_mcfg_memory. exact Hc.
  Qed.

  Lemma exp_eval_map_monad (idxs : list (dtyp * exp dtyp)) vs :
    Forall2 (fun '(dt, e) v => EE (Some dt) e v) idxs vs ->
    interp_mcfg (map_monad (fun '(dt, index) => denote_exp (Some dt) index) idxs)
                (st, ((sf, stk), g))
    ≈ Ret ((st, ((sf, stk), g)), vs).
  Proof.
    induction 1 as [|[dt e] v idxs vs Hx Hxs IH].
    - cbn. apply interp_mcfg_ret.
    - cbv beta iota in Hx. unfold exp_eval in Hx. cbn [map_monad bind Monad_itree ret].
      rewrite interp_mcfg_bind, Hx, Eqit.bind_ret_l. cbn beta iota.
      rewrite interp_mcfg_bind, IH, Eqit.bind_ret_l. cbn beta iota.
      apply interp_mcfg_ret.
  Qed.

  Lemma exp_eval_gep t dt1 dt2 ep idxs vp vs v :
    EE (Some dt2) ep vp ->
    Forall2 (fun '(dt, e) v => EE (Some dt) e v) idxs vs ->
    eval_gep dt1 vp vs = EOU.raise_ret v ->
    EE t (OP_GetElementPtr dt1 (dt2, ep) idxs) v.
  Proof.
    intros Hp Hi Hg. unfold exp_eval in *. cbn [denote_exp bind Monad_itree].
    rewrite interp_mcfg_bind, Hp, Eqit.bind_ret_l. cbn beta iota.
    rewrite interp_mcfg_bind, exp_eval_map_monad by exact Hi.
    rewrite Eqit.bind_ret_l. cbn beta iota.
    rewrite Hg. apply interp_mcfg_lift_ret.
  Qed.
End ExpEval.

(** ** The expression forms of the emitter (after [typ] -> [dtyp] conversion) *)

Notation i64 := (DTYPE_I 64 : dtyp) (only parsing).
Notation i32 := (DTYPE_I 32 : dtyp) (only parsing).
Notation dptr := (DTYPE_Pointer : dtyp) (only parsing).
Notation elit n := (EXP_Integer (Nat.to_num_int n)) (only parsing).

Section Forms.
  Context (st : state) (sf : stack_frame) (stk : stack) (g : global_env).
  Notation EE := (exp_eval st sf stk g).

  (** [val_long]: [(e << 1) | 1]. *)
  Lemma exp_eval_val_long t e z :
    EE (Some i64) e (I64 z) ->
    EE t (OP_IBinop (Or false) i64 (OP_IBinop (Shl false false) i64 e (elit 1)) (elit 1))
       (I64 (2 * z + 1)).
  Proof.
    intros H. eapply exp_eval_ibinop; [|apply exp_eval_lit64|apply eval_or1_even].
    eapply exp_eval_ibinop; [exact H|apply exp_eval_lit64|apply eval_shl1].
  Qed.

  (** [long_val]: [e >>a 1]. *)
  Lemma exp_eval_long_val t e z :
    EE (Some i64) e (I64 z) ->
    EE t (OP_IBinop (AShr false) i64 e (elit 1)) (I64 (@Integers.signed 64 (Integers.repr z) / 2)).
  Proof.
    intros H. eapply exp_eval_ibinop; [exact H|apply exp_eval_lit64|apply eval_ashr1].
  Qed.

  Lemma exp_eval_long_val_small t e z :
    -2^63 <= z < 2^63 ->
    EE (Some i64) e (I64 z) ->
    EE t (OP_IBinop (AShr false) i64 e (elit 1)) (I64 (z / 2)).
  Proof.
    intros Hz H. eapply exp_eval_ibinop; [exact H|apply exp_eval_lit64|apply eval_ashr1_small, Hz].
  Qed.

  (** [is_block]: [(e & 1) == 0]. *)
  Lemma exp_eval_is_block t e z :
    EE (Some i64) e (I64 z) ->
    EE t (OP_ICmp false Eq i64 (OP_IBinop And i64 e (elit 1)) (elit 0)) (I1 (Z.eqb (z mod 2) 0)).
  Proof.
    intros H. eapply exp_eval_icmp.
    - eapply exp_eval_ibinop; [exact H|apply exp_eval_lit64|apply eval_and1].
    - apply exp_eval_lit64.
    - rewrite eval_icmp_eq. rewrite (Z.mod_small (z mod 2)) by (pose proof (Z.mod_pos_bound z 2); lia).
      reflexivity.
  Qed.

  (** The tag of a header: [e & 1023]. *)
  Lemma exp_eval_and1023 t e z :
    EE (Some i64) e (I64 z) ->
    EE t (OP_IBinop And i64 e (elit 1023)) (I64 (z mod 1024)).
  Proof.
    intros H. eapply exp_eval_ibinop; [exact H|apply exp_eval_lit64|apply eval_and1023].
  Qed.

  Lemma exp_eval_sub t e1 e2 a b :
    EE (Some i64) e1 (I64 a) -> EE (Some i64) e2 (I64 b) ->
    EE t (OP_IBinop (Sub false false) i64 e1 e2) (I64 (a - b)).
  Proof. intros H1 H2. eapply exp_eval_ibinop; [exact H1|exact H2|apply eval_sub]. Qed.

  Lemma exp_eval_uge t e1 e2 a b :
    EE (Some i64) e1 (I64 a) -> EE (Some i64) e2 (I64 b) ->
    EE t (OP_ICmp false Uge i64 e1 e2) (I1 (Z.leb (b mod 2^64) (a mod 2^64))).
  Proof. intros H1 H2. eapply exp_eval_icmp; [exact H1|exact H2|apply eval_icmp_uge]. Qed.

  Lemma exp_eval_ptrtoint t e p :
    EE (Some dptr) e (Ptr p) ->
    EE t (OP_Conversion (CONV_Impure Ptrtoint) dptr e i64) (I64 (ptr_to_int p)).
  Proof. intros H. eapply exp_eval_conv_impure; [exact H|apply conv_ptrtoint]. Qed.

  Lemma exp_eval_inttoptr t e z q :
    EE (Some i64) e (I64 z) ->
    int_to_ptr (z mod 2^64) wildcard_prov = EOU.raise_ret q ->
    EE t (OP_Conversion (CONV_Impure Inttoptr) i64 e dptr) (Ptr q).
  Proof. intros H Hq. eapply exp_eval_conv_impure; [exact H|apply conv_inttoptr, Hq]. Qed.

  (** [inttoptr] never fails: the result has address [z mod 2^64] and the
      wildcard provenance. *)
  Lemma exp_eval_inttoptr' t e z :
    EE (Some i64) e (I64 z) ->
    exists q, ptr_to_int q = z mod 2^64 /\ ptr_provenance q = wildcard_prov /\
         EE t (OP_Conversion (CONV_Impure Inttoptr) i64 e dptr) (Ptr q).
  Proof.
    intros H. destruct (@int_to_ptr_total (z mod 2^64) wildcard_prov) as (q & Hq & Hi & Hp).
    - apply Z.mod_pos_bound. lia.
    - exists q. split; [exact Hi|split; [exact Hp|]]. eapply exp_eval_inttoptr; eauto.
  Qed.

  (** [gep_at]: [gep i64, ptr e, i64 n]. *)
  Lemma exp_eval_gep_at t dt e p n q :
    (Z.of_nat n < 2^63) ->
    EE (Some dt) e (Ptr p) ->
    ptr_off p (8 * Z.of_nat n) q ->
    EE t (OP_GetElementPtr i64 (dt, e) [(i64, elit n)]) (Ptr q).
  Proof.
    intros Hn H Hq. eapply exp_eval_gep; [exact H| |].
    - constructor; [apply exp_eval_lit64|constructor].
    - apply eval_gep_i64; [lia|exact Hq].
  Qed.

  (** [gep_tinfo n] for the fields used by the emitter. *)
  Lemma exp_eval_gep_tinfo t dt e p n off q :
    (n, off) = (0%nat, 0) \/ (n, off) = (1%nat, 8) \/ (n, off) = (4%nat, 8216) \/ (n, off) = (5%nat, 8224) ->
    EE (Some dt) e (Ptr p) ->
    ptr_off p off q ->
    EE t (OP_GetElementPtr tinfo_dt (dt, e) [(i32, elit 0); (i32, elit n)]) (Ptr q).
  Proof.
    intros Hn H Hq. eapply exp_eval_gep; [exact H| |].
    - constructor; [apply exp_eval_lit32|constructor; [apply exp_eval_lit32|constructor]].
    - eapply eval_gep_tinfo; eauto.
  Qed.

  (** [gep_struct frame_ty base j], [j <= 2]. *)
  Lemma exp_eval_gep_frame t dt e p n q :
    (n <= 2)%nat ->
    EE (Some dt) e (Ptr p) ->
    ptr_off p (8 * Z.of_nat n) q ->
    EE t (OP_GetElementPtr frame_dt (dt, e) [(i32, elit 0); (i32, elit n)]) (Ptr q).
  Proof.
    intros Hn H Hq. eapply exp_eval_gep; [exact H| |].
    - constructor; [apply exp_eval_lit32|constructor; [apply exp_eval_lit32|constructor]].
    - eapply eval_gep_frame; eauto.
  Qed.

  (** [gep_arr (array n i64) base i]. *)
  Lemma exp_eval_gep_arr t dt e p sz i q :
    (Z.of_nat i < 2^63) ->
    EE (Some dt) e (Ptr p) ->
    ptr_off p (8 * Z.of_nat i) q ->
    EE t (OP_GetElementPtr (DTYPE_Array false sz i64) (dt, e) [(i32, elit 0); (i64, elit i)]) (Ptr q).
  Proof.
    intros Hi H Hq. eapply exp_eval_gep; [exact H| |].
    - constructor; [apply exp_eval_lit32|constructor; [apply exp_eval_lit64|constructor]].
    - apply eval_gep_arr; [lia|exact Hq].
  Qed.
End Forms.
