(* ===================================================================== *)
(*  Per-construct STRUCTURAL / value-representation lemmas for the        *)
(*  CONCRETE emitter [compile_prog] / [translate_cfg]                      *)
(*    (CertiRocq.CodegenLLVM.LambdaANF_to_LLVM).                          *)
(*                                                                       *)
(*  This file discharges — with real [Qed] — the STRAIGHT-LINE, pure     *)
(*  content of the tractable per-construct obligations:                   *)
(*                                                                       *)
(*    Ehalt : the emitted entry block returns exactly [gvar fs env x]     *)
(*            (= the SSA local [env x] for a non-function [x]); given the  *)
(*            value in that local represents the source value [v], the    *)
(*            returned dvalue value-represents [v].                        *)
(*    Eproj : the emitted [load_field env y n] addresses [Field(y,n)]     *)
(*            correctly: its GEP index [n] (i64-typed) is byte offset      *)
(*            [8*n], matching [values.h]'s [Field(x,i) = ((value* )x)[i]]  *)
(*            and the value relation's field read at offset [0 + 8*n].     *)
(*    Ecase : the boxed/unboxed dispatch partition by [get_arity] and the *)
(*            tag decoders — the unboxed switch key [Long_val y] recovers  *)
(*            the ordinal, and the boxed tag mask [header & 1023] recovers *)
(*            [get_ord] from the packed header [(arity<<10)|ord].          *)
(*                                                                       *)
(*  Everything here needs ONLY integer / pointer arithmetic and the       *)
(*  value-representation relation [repr_val_LambdaANF_LLVM] (inlined       *)
(*  verbatim from LambdaANF_to_LLVM_correct_v2/v3.v — a cross-file         *)
(*  [Require] of the correctness sections does not resolve, so, exactly    *)
(*  as v3 does, the relation is reproduced here so the lemmas are stated   *)
(*  against it).                                                          *)
(*                                                                       *)
(*  The CONCRETE emitter IS imported (not mirrored): the emitter-shape     *)
(*  lemmas below are proved against the real [translate_cfg] / [load_field]*)
(*  / [gep_field] / [val_long] / [long_val] / [header_word].               *)
(*                                                                       *)
(*  The OPERATIONAL residual of each case — that the emitted block, run    *)
(*  through the Vellvm denotation ([denote_instr]/[denote_terminator] /    *)
(*  [interp_mcfg] / [Eval_to]), actually reaches the post-state whose      *)
(*  returned/loaded/branched value is the one addressed above — is NOT     *)
(*  proved here; it is isolated as an explicit [Variable]/[Hypothesis]     *)
(*  ([halts_returning] + [halts_returning_Eval_to]).  That is exactly the  *)
(*  [refinement_runs]-blocked B2 layer of                                  *)
(*  LambdaANF_to_LLVM_correct_v3.v (deleted [Theory/Refinement.v] in       *)
(*  rocq-vellvm v3.0).                                                     *)
(*                                                                       *)
(*  NO [admit] / [Admitted] / [Axiom].                                     *)
(* ===================================================================== *)

From Stdlib Require Import ZArith NArith List Lia String.

(* --- Source: CertiRocq LambdaANF ------------------------------------- *)
From CertiRocq.LambdaANF Require Import cps eval identifiers.
From CertiRocq.Common Require Import AstCommon.

(* --- The CONCRETE emitter (imported, reasoned against directly) ------- *)
From CertiRocq.CodegenLLVM Require Import LambdaANF_to_LLVM.

(* --- Target: Vellvm VIR (rocq-vellvm v3.0) --------------------------- *)
From Vellvm Require Import Syntax.
From Vellvm Require Import Semantics.DynamicValues.
From Vellvm Require Import Params.
From Vellvm Require Import Interfaces.Memory.
From Vellvm Require Import Numeric.Integers.

Import ListNotations.
Set Bullet Behavior "Strict Subproofs".

(* ===================================================================== *)
(*  PART A -- EMITTER-STRUCTURAL SHAPE LEMMAS (concrete [translate_cfg]).  *)
(*  Pure: they only unfold the emitter and need no memory model.          *)
(* ===================================================================== *)

(** [Ehalt x] emits a single entry block whose terminator returns exactly
    [gvar fs env x].  This is the "returns [env x]'s value" fact. *)
Lemma translate_cfg_Ehalt :
  forall (get_ord get_arity : ctor_tag -> N)
         (prim_of : positive -> option (string * bool))
         (fs : list positive) (env : nenv) (chunk : N)
         (x : var) (fresh : positive),
    translate_cfg get_ord get_arity prim_of fs env chunk (Ehalt x) fresh
    = ( [ mk_block (Anon (Zpos fresh)) [] []
            (IVoid 1%Z, TERM_Ret (val_ty, gvar fs env x), []) None ],
        Pos.succ fresh ).
Proof. reflexivity. Qed.

(** For a variable that is NOT a top-level function, [gvar] is the SSA
    local named by the current [nenv]. *)
Lemma gvar_local :
  forall (fs : list positive) (env : nenv) (x : var),
    is_fun fs x = false ->
    gvar fs env x = EXP_Ident (ID_Local (env x)).
Proof. intros fs env x H. unfold gvar. rewrite H. reflexivity. Qed.

(** Under the identity name environment [base_env] and no top-level
    functions, [Ehalt x] returns precisely [evar x]. *)
Lemma gvar_base_env :
  forall (x : var), gvar [] base_env x = evar x.
Proof. intro x. reflexivity. Qed.

Corollary translate_cfg_Ehalt_returns_evar :
  forall (get_ord get_arity : ctor_tag -> N)
         (prim_of : positive -> option (string * bool))
         (x : var) (fresh : positive),
    translate_cfg get_ord get_arity prim_of [] base_env 0%N (Ehalt x) fresh
    = ( [ mk_block (Anon (Zpos fresh)) [] []
            (IVoid 1%Z, TERM_Ret (val_ty, evar x), []) None ],
        Pos.succ fresh ).
Proof.
  intros. rewrite translate_cfg_Ehalt. rewrite gvar_base_env. reflexivity.
Qed.

(** [Eproj x t n y e'] prepends the single [load_field env y n] instruction
    (binding SSA local [x]) onto the entry of the continuation's CFG, and
    leaves the fresh-counter of the continuation untouched. *)
Lemma translate_cfg_Eproj :
  forall (get_ord get_arity : ctor_tag -> N)
         (prim_of : positive -> option (string * bool))
         (fs : list positive) (env : nenv) (chunk : N)
         (x : var) (t : ctor_tag) (n : N) (y : var) (e' : cps.exp) (fresh : positive),
    translate_cfg get_ord get_arity prim_of fs env chunk (Eproj x t n y e') fresh
    = ( prepend_code [ (IId (Raw (Zpos x)), load_field env y n, []) ]
          (fst (translate_cfg get_ord get_arity prim_of fs env chunk e' fresh)),
        snd (translate_cfg get_ord get_arity prim_of fs env chunk e' fresh) ).
Proof.
  intros. cbn [translate_cfg].
  destruct (translate_cfg get_ord get_arity prim_of fs env chunk e' fresh)
    as [blks f'].
  reflexivity.
Qed.

(** The emitted [Field(y,n)] load: a load through [inttoptr (env y)] GEP'd by
    the field index [n] (i64-typed, so byte offset [8*n]).  This is exactly
    [values.h]'s [Field(x,i) = ((value* )x)[i]]. *)
Lemma load_field_unfold :
  forall (env : nenv) (y : var) (n : N),
    load_field env y n
    = INSTR_Load val_ty
        (ptr_ty,
         OP_GetElementPtr val_ty
           (ptr_ty, OP_Conversion Inttoptr val_ty (nvar env y) ptr_ty)
           [(val_ty, lit (N.to_nat n))]) [].
Proof. reflexivity. Qed.

(* ===================================================================== *)
(*  PART B -- ABI ARITHMETIC (encoding <-> value-relation numerics).       *)
(*  Pure integer arithmetic tying the emitter's ABI encodings to the       *)
(*  numeric encodings baked into [repr_val_LambdaANF_LLVM].                *)
(* ===================================================================== *)

Open Scope Z_scope.

(** Unboxed switch key.  The emitter's [long_val] is an arithmetic shift
    right by 1; on the unboxed immediate [Val_long ord = ord*2+1] the value
    relation stores ([RLconstr_unboxed]), it recovers the ordinal. *)
Lemma long_val_recovers_ord :
  forall (ord : N), Z.shiftr (Z.of_N ord * 2 + 1) 1 = Z.of_N ord.
Proof.
  intro ord. rewrite Z.shiftr_div_pow2 by lia.
  replace (2 ^ 1) with 2 by reflexivity.
  rewrite Z.div_add_l by lia.
  replace (1 / 2) with 0 by reflexivity. lia.
Qed.

(** Boxed tag mask.  The emitter's boxed switch keys on [header & 1023];
    on the packed header [(arity<<10) | ord = arity*1024 + ord] the value
    relation stores ([RLconstr_boxed]), the mask recovers [ord] whenever the
    ordinal fits the low 10 bits. *)
Lemma header_mask_selects_ord :
  forall (arity : nat) (ord : N),
    Z.of_N ord < 1024 ->
    Z.land (Z.of_nat arity * 1024 + Z.of_N ord) 1023 = Z.of_N ord.
Proof.
  intros arity ord Hlt.
  replace 1023 with (Z.ones 10) by reflexivity.
  rewrite Z.land_ones by lia.
  replace (2 ^ 10) with 1024 by reflexivity.
  rewrite Z.add_comm.
  rewrite Z.mod_add by lia.
  apply Z.mod_small. lia.
Qed.

(** GEP field-index bridge: the emitter's field index [n : N] (literal
    [N.to_nat n]) and the value relation's byte offset [8 * n] agree. *)
Lemma field_index_bridge :
  forall (n : N), Z.of_nat (N.to_nat n) = Z.of_N n.
Proof. intro n. rewrite N_nat_Z. reflexivity. Qed.

Lemma field_offset_bridge :
  forall (n : N), (0 + 8 * Z.of_nat (N.to_nat n))%Z = (8 * Z.of_N n)%Z.
Proof. intro n. rewrite field_index_bridge. ring. Qed.

(** Partition of the [Ecase] arm-edges by arity is exhaustive: every arm
    lands in exactly one of the unboxed ([arity =? 0]) / boxed ([arity <> 0])
    switches the emitter builds.  This is the structural correctness of the
    [get_arity] partition (independent of the tag payload type). *)
Lemma case_partition_complete :
  forall (A : Type) (aedges : list (N * A)) (e : N * A),
    List.In e aedges ->
    ( (N.eqb (Datatypes.fst e) 0%N = true) /\
        List.In (Datatypes.snd e)
          (List.map Datatypes.snd
             (List.filter (fun ae => N.eqb (Datatypes.fst ae) 0%N) aedges)) )
    \/
    ( (N.eqb (Datatypes.fst e) 0%N = false) /\
        List.In (Datatypes.snd e)
          (List.map Datatypes.snd
             (List.filter (fun ae => negb (N.eqb (Datatypes.fst ae) 0%N)) aedges)) ).
Proof.
  intros A aedges e Hin.
  destruct (N.eqb (Datatypes.fst e) 0%N) eqn:Harity.
  - left. split; [reflexivity|].
    apply List.in_map_iff. exists e. split; [reflexivity|].
    apply List.filter_In. split; [exact Hin | exact Harity].
  - right. split; [reflexivity|].
    apply List.in_map_iff. exists e. split; [reflexivity|].
    apply List.filter_In. split; [exact Hin|]. rewrite Harity. reflexivity.
Qed.

Close Scope Z_scope.

(* ===================================================================== *)
(*  PART C -- VALUE RELATION (inlined verbatim from                        *)
(*  LambdaANF_to_LLVM_correct_v2.v:122-194 / v3.v:86-140) plus the pure    *)
(*  value-relation lemmas and the per-construct glue.                      *)
(* ===================================================================== *)

Section DISPATCH.

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

  (* ------------------------------------------------------------------- *)
  (*  Pure value-relation lemmas (verbatim from v2, all [Qed]).           *)
  (* ------------------------------------------------------------------- *)

  Lemma repr_val_boxed_inv :
    forall (t : ctor_tag) (vs : list cps.val) (mem : memory_stack) (a : addr),
      repr_val_LambdaANF_LLVM (Vconstr t vs) mem (DVALUE_Addr a) ->
      exists (arity : nat) (ord : N),
        get_ctor_ord t = Some ord
        /\ get_ctor_arity t = Some arity
        /\ (arity > 0)%nat
        /\ read_header mem a
             = Some (DVALUE_I64 (Z.of_nat arity * 1024 + Z.of_N ord))
        /\ repr_val_constr_args_LambdaANF_LLVM vs mem a 0%Z.
  Proof.
    intros t vs mem a H. inversion H; subst.
    do 2 eexists; repeat split; eassumption.
  Qed.

  Lemma repr_val_unboxed_pin :
    forall (t : ctor_tag) (mem : memory_stack) (dv : dvalue),
      get_ctor_arity t = Some 0%nat ->
      repr_val_LambdaANF_LLVM (Vconstr t []) mem dv ->
      exists ord, get_ctor_ord t = Some ord
                  /\ dv = DVALUE_I64 (Z.of_N ord * 2 + 1).
  Proof.
    intros t mem dv Harity H. inversion H; subst.
    - eexists; split; [ eassumption | reflexivity ].
    - exfalso.
      match goal with
      | Ha : get_ctor_arity t = Some ?a, Hgt : (?a > 0)%nat |- _ =>
          rewrite Harity in Ha; inversion Ha; subst; lia
      end.
  Qed.

  Lemma repr_val_constr_args_nth :
    forall (vs : list cps.val) (mem : memory_stack) (a : addr) (off : Z)
           (n : nat) (v : cps.val),
      repr_val_constr_args_LambdaANF_LLVM vs mem a off ->
      nth_error vs n = Some v ->
      exists dv, read_field mem a (off + 8 * Z.of_nat n)%Z = Some dv
                 /\ repr_val_LambdaANF_LLVM v mem dv.
  Proof.
    intros vs mem a off n v Hargs. revert n v.
    induction Hargs as
      [ mem0 a0 off0
      | v0 vs0 mem0 a0 off0 dv0 Hrd Hrepr Hrest IH ];
      intros n v Hnth.
    - destruct n; simpl in Hnth; discriminate.
    - destruct n as [|n]; simpl in Hnth.
      + inversion Hnth; subst.
        exists dv0; split.
        * replace (off0 + 8 * Z.of_nat 0)%Z with off0 by lia. exact Hrd.
        * exact Hrepr.
      + destruct (IH n v Hnth) as [dv [Hread Hrepr']].
        exists dv; split.
        * replace (off0 + 8 * Z.of_nat (S n))%Z
             with ((off0 + 8) + 8 * Z.of_nat n)%Z by lia.
          exact Hread.
        * exact Hrepr'.
  Qed.

  (* ------------------------------------------------------------------- *)
  (*  Ehalt -- value-relation content.                                    *)
  (*  The emitted block returns the dvalue held in local [env x]          *)
  (*  (Part A, [translate_cfg_Ehalt]).  If that dvalue value-represents    *)
  (*  the source value [v], then the returned result satisfies the        *)
  (*  result relation (its LEFT disjunct).  This is the whole pure         *)
  (*  content of [Ehalt_case]; the reach is the operational residual.      *)
  (* ------------------------------------------------------------------- *)
  Lemma Ehalt_value_relation :
    forall (v : cps.val) (mem : memory_stack) (dv : dvalue),
      repr_val_LambdaANF_LLVM v mem dv ->
      result_val_LambdaANF_LLVM v mem dv.
  Proof. intros v mem dv Hrepr. left. exact Hrepr. Qed.

  (* ------------------------------------------------------------------- *)
  (*  Eproj -- field-addressing correctness.                              *)
  (*  The emitter's [load_field env y n] GEPs field index [n] (Part A),    *)
  (*  i.e. byte offset [8*n] (Part B [field_offset_bridge]).  From a boxed  *)
  (*  constructor's args relation, that cell reads to a dvalue             *)
  (*  value-representing the n-th source value.  Pure: no memory-model      *)
  (*  frame lemma is used (the read facts are those recorded by [RLcons]). *)
  (* ------------------------------------------------------------------- *)

  (** Direct form on the args relation, keyed by the emitter's [N] index. *)
  Lemma Eproj_field_addressing :
    forall (vs : list cps.val) (mem : memory_stack) (a : addr)
           (n : N) (v : cps.val),
      repr_val_constr_args_LambdaANF_LLVM vs mem a 0%Z ->
      nth_error vs (N.to_nat n) = Some v ->
      exists dv, read_field mem a (8 * Z.of_N n)%Z = Some dv
                 /\ repr_val_LambdaANF_LLVM v mem dv.
  Proof.
    intros vs mem a n v Hargs Hnth.
    destruct (repr_val_constr_args_nth vs mem a 0%Z (N.to_nat n) v Hargs Hnth)
      as [dv [Hread Hrepr]].
    exists dv. split; [| exact Hrepr].
    rewrite field_offset_bridge in Hread. exact Hread.
  Qed.

  (** Top form on a boxed [Vconstr]: the [Field(y,n)] address the emitter
      computes holds a dvalue value-representing the n-th field value. *)
  Lemma Eproj_addresses_field :
    forall (t : ctor_tag) (vs : list cps.val) (mem : memory_stack) (a : addr)
           (n : N) (v : cps.val),
      repr_val_LambdaANF_LLVM (Vconstr t vs) mem (DVALUE_Addr a) ->
      nth_error vs (N.to_nat n) = Some v ->
      exists dv, read_field mem a (8 * Z.of_N n)%Z = Some dv
                 /\ repr_val_LambdaANF_LLVM v mem dv.
  Proof.
    intros t vs mem a n v Hconstr Hnth.
    apply repr_val_boxed_inv in Hconstr.
    destruct Hconstr as [arity [ord [_ [_ [_ [_ Hargs]]]]]].
    eapply Eproj_field_addressing; eauto.
  Qed.

  (* ------------------------------------------------------------------- *)
  (*  Ecase -- dispatch structural correctness (value-relation side).      *)
  (* ------------------------------------------------------------------- *)

  (** Boxed arm: the header read by the value relation is the packed word
      [(arity<<10)|ord], and the emitter's [header & 1023] mask recovers the
      ordinal that keys the boxed switch. *)
  Lemma Ecase_boxed_tag :
    forall (t : ctor_tag) (vs : list cps.val) (mem : memory_stack) (a : addr),
      repr_val_LambdaANF_LLVM (Vconstr t vs) mem (DVALUE_Addr a) ->
      exists (arity : nat) (ord : N),
        get_ctor_ord t = Some ord
        /\ get_ctor_arity t = Some arity
        /\ (arity > 0)%nat
        /\ read_header mem a
             = Some (DVALUE_I64 (Z.of_nat arity * 1024 + Z.of_N ord))
        /\ ((Z.of_N ord < 1024)%Z ->
            Z.land (Z.of_nat arity * 1024 + Z.of_N ord) 1023 = Z.of_N ord).
  Proof.
    intros t vs mem a Hconstr.
    apply repr_val_boxed_inv in Hconstr.
    destruct Hconstr as [arity [ord [Hord [Har [Hgt [Hhdr Hargs]]]]]].
    exists arity, ord. repeat split; try assumption.
    intro Hlt. apply header_mask_selects_ord. exact Hlt.
  Qed.

  (** Unboxed arm: the immediate the value relation stores is [ord*2+1], and
      the emitter's [Long_val] switch key recovers the ordinal. *)
  Lemma Ecase_unboxed_tag :
    forall (t : ctor_tag) (mem : memory_stack) (dv : dvalue),
      get_ctor_arity t = Some 0%nat ->
      repr_val_LambdaANF_LLVM (Vconstr t []) mem dv ->
      exists ord, get_ctor_ord t = Some ord
                  /\ dv = DVALUE_I64 (Z.of_N ord * 2 + 1)
                  /\ Z.shiftr (Z.of_N ord * 2 + 1) 1 = Z.of_N ord.
  Proof.
    intros t mem dv Har Hrepr.
    destruct (repr_val_unboxed_pin t mem dv Har Hrepr) as [ord [Hord Hdv]].
    exists ord. repeat split; try assumption.
    apply long_val_recovers_ord.
  Qed.

  (* ------------------------------------------------------------------- *)
  (*  OPERATIONAL RESIDUALS (the [refinement_runs]-blocked B2 conjunct).   *)
  (*                                                                       *)
  (*  Each per-construct obligation of v3 has the uniform shape            *)
  (*    halts_returning m mem dv -> repr v mem dv                          *)
  (*      -> exists mem' dv', Eval_to m mem' dv' /\ result v mem' dv'.     *)
  (*  The value-relation payload [repr v mem dv] is supplied by the pure    *)
  (*  lemmas above (Ehalt: identity; Eproj: [Eproj_addresses_field];        *)
  (*  Ecase: [Ecase_boxed_tag]/[Ecase_unboxed_tag]).  The ONLY thing left   *)
  (*  is the operational reach [halts_returning m mem dv] -> [Eval_to ...], *)
  (*  i.e. that the emitted CFG, run through [interp_mcfg]/[denote_mcfg],    *)
  (*  actually halts at [(mem,dv)].  That is [Eval_to]/[denote]/[interp],   *)
  (*  which rocq-vellvm v3.0 has DELETED (no [Theory/Refinement.v]); it is   *)
  (*  localised as [halts_returning_Eval_to] and is precisely the           *)
  (*  [refinement_runs] gate of v3.  With that hypothesis the routine       *)
  (*  cases close by [Qed], the value-relation side being entirely proved   *)
  (*  above.                                                                *)
  (* ------------------------------------------------------------------- *)

  Variable Eval_to : CFG.mcfg dtyp -> memory_stack -> dvalue -> Prop.
  Variable halts_returning : CFG.mcfg dtyp -> memory_stack -> dvalue -> Prop.
  Hypothesis halts_returning_Eval_to :
    forall (m : CFG.mcfg dtyp) (mem : memory_stack) (dv : dvalue),
      halts_returning m mem dv -> Eval_to m mem dv.

  (** [Ehalt] routine case: value-relation side is the identity, closed. *)
  Lemma Ehalt_case :
    forall (m : CFG.mcfg dtyp) (mem : memory_stack) (dv : dvalue) (v : cps.val),
      halts_returning m mem dv ->
      repr_val_LambdaANF_LLVM v mem dv ->
      exists (mem' : memory_stack) (dv' : dvalue),
        Eval_to m mem' dv' /\ result_val_LambdaANF_LLVM v mem' dv'.
  Proof.
    intros m mem dv v Hhalt Hrepr.
    exists mem, dv. split.
    - apply halts_returning_Eval_to; exact Hhalt.
    - apply Ehalt_value_relation; exact Hrepr.
  Qed.

  (** [Eproj] routine case: value-relation side is [Eproj_addresses_field]
      (the loaded cell value-represents the projected value); closed. *)
  Lemma Eproj_case :
    forall (m : CFG.mcfg dtyp) (mem : memory_stack)
           (t : ctor_tag) (vs : list cps.val) (a : addr)
           (n : N) (v : cps.val) (dv : dvalue),
      repr_val_LambdaANF_LLVM (Vconstr t vs) mem (DVALUE_Addr a) ->
      nth_error vs (N.to_nat n) = Some v ->
      read_field mem a (8 * Z.of_N n)%Z = Some dv ->
      halts_returning m mem dv ->
      exists (mem' : memory_stack) (dv' : dvalue),
        Eval_to m mem' dv' /\ result_val_LambdaANF_LLVM v mem' dv'.
  Proof.
    intros m mem t vs a n v dv Hconstr Hnth Hread Hhalt.
    destruct (Eproj_addresses_field t vs mem a n v Hconstr Hnth)
      as [dv0 [Hread0 Hrepr0]].
    assert (dv0 = dv) as -> by congruence.
    exists mem, dv. split.
    - apply halts_returning_Eval_to; exact Hhalt.
    - left; exact Hrepr0.
  Qed.

End DISPATCH.
