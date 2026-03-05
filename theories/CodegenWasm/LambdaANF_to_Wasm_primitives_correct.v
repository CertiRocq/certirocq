From Stdlib Require Import
  Program.Equality
  Logic.Decidable Lists.ListDec
  Relations.Relations Relations.Relation_Operators Lia
  EqdepFacts
  List Nnat Uint63.

From CertiCoq Require Import
  LambdaANF.cps
  LambdaANF.cps_util
  LambdaANF.eval
  LambdaANF.identifiers
  CodegenWasm.LambdaANF_to_Wasm
  CodegenWasm.LambdaANF_to_Wasm_utils
  CodegenWasm.LambdaANF_to_Wasm_correct
  CodegenWasm.LambdaANF_to_Wasm_primitives
  CodegenWasm.LambdaANF_to_Wasm_restrictions.

From MetaRocq Require Import Common.Kernames.

From compcert Require Import
  Coqlib common.Memory.

From Wasm Require Import
  datatypes operations host memory_list opsem
  type_preservation properties common numerics.

Import ssreflect eqtype ssrbool eqtype.
Import LambdaANF.toplevel LambdaANF.cps compM.
Import bytestring.
Import ExtLib.Structures.Monad MonadNotation.
Import bytestring.
Import ListNotations SigTNotations.
Import seq.
Import Wasm_int.

(* Avoid unfolding during proofs *)
Opaque Uint63.to_Z.

Open Scope nat_scope.

Section LambdaANF_PRIMITIVE_WRAPPERS.

(* **** Define LambdaANF wrapper functions for Coq's 63 bit integer operators  **** *)

(* LambdaANF constructor values 'Vconstr t vs' hold the tag 't' of the constructor and a list of values 'vs'.
   The tag is NOT the same as the ordinal used in the translation section above,
   and the tag of a specific constructor is NOT guaranteed to always be the same,
   it depends on the program being extracted.

   For the proof, we define 'wrapper' functions for the primitive operators,
   and for primitive operators that return a constructor value, the wrapper function is parameterized over the tags
   since we don't know the concrete values of the tags.

   For convenience, we define the tags as section variables.
 *)
Variables true_tag false_tag eq_tag lt_tag gt_tag c0_tag c1_tag pair_tag : ctor_tag.

Definition LambdaANF_primInt_arith_fun (f : uint63 -> uint63 -> uint63) (x y : uint63) := Vprim (primInt (f x y)).

Definition LambdaANF_primInt_bool_fun (f : uint63 -> uint63 -> bool) x y :=
  if f x y then
    Vconstr true_tag []
  else
    Vconstr false_tag [].

Definition LambdaANF_primInt_compare_fun (f : uint63 -> uint63 -> comparison) x y :=
  match f x y with
  | Datatypes.Eq => Vconstr eq_tag []
  | Datatypes.Lt => Vconstr lt_tag []
  | Datatypes.Gt => Vconstr gt_tag []
  end.

Definition LambdaANF_primInt_carry_fun (f : uint63 -> uint63 -> carry uint63) x y :=
  match f x y with
  | C0 z => Vconstr c0_tag [ Vprim (primInt z) ]
  | C1 z => Vconstr c1_tag [ Vprim (primInt z) ]
  end.

Definition LambdaANF_primInt_prod_fun (f : uint63 -> uint63 -> prod uint63 uint63) x y :=
  let p := f x y in
  Vconstr pair_tag [ Vprim (primInt (fst p)) ; Vprim (primInt (snd p)) ].

Definition LambdaANF_primInt_unop_fun (f : uint63 -> uint63) x := Vprim (primInt (f x)).

(* TODO: Consider what to do for the case where xh < y
   When the dividend (xh * 2^63 + xl) is too large, the quotient will overflow,
   but the behavior of diveucl_21 in that case is not specified as an axiom,
   but all VM/ native implementations return (0, 0) *)
Definition LambdaANF_primInt_diveucl_21 xh xl y :=
  if (y <=? xh)%uint63 then
    Vconstr pair_tag [ Vprim (primInt 0%uint63) ; Vprim (primInt 0%uint63) ]
  else
    Vconstr pair_tag [ Vprim (primInt (fst (diveucl_21 xh xl y))) ; Vprim (primInt (snd (diveucl_21 xh xl y))) ].

Definition LambdaANF_primInt_addmuldiv p x y := Vprim (primInt (addmuldiv p x y)).

(* Define a partial function for applying a primitive operator.
   The result is only defined if the operator is supported and the arguments
   match the type of the Coq operator.
   E.g 'add' has the type 'uint63 -> uint63 -> uint63' so the arguments must be
   2 primitive integer values and the return value is a primitive integer. *)
Definition apply_LambdaANF_primInt_operator op (vs : list cps.val) : option cps.val :=
  match vs with
  | [ Vprim (primInt x) ] =>
      match op with
      | PrimInt63head0 => Some (LambdaANF_primInt_unop_fun Uint63.head0 x)
      | PrimInt63tail0 => Some (LambdaANF_primInt_unop_fun Uint63.tail0 x)
      | _ => None
      end
  | [ Vprim (primInt x) ; Vprim (primInt y) ] =>
      match op with
      | PrimInt63add => Some (LambdaANF_primInt_arith_fun Uint63.add x y)
      | PrimInt63sub => Some (LambdaANF_primInt_arith_fun Uint63.sub x y)
      | PrimInt63mul => Some (LambdaANF_primInt_arith_fun Uint63.mul x y)
      | PrimInt63div => Some (LambdaANF_primInt_arith_fun Uint63.div x y)
      | PrimInt63mod => Some (LambdaANF_primInt_arith_fun Uint63.mod x y)
      | PrimInt63lsl => Some (LambdaANF_primInt_arith_fun Uint63.lsl x y)
      | PrimInt63lsr => Some (LambdaANF_primInt_arith_fun Uint63.lsr x y)
      | PrimInt63land => Some (LambdaANF_primInt_arith_fun Uint63.land x y)
      | PrimInt63lor => Some (LambdaANF_primInt_arith_fun Uint63.lor x y)
      | PrimInt63lxor => Some (LambdaANF_primInt_arith_fun Uint63.lxor x y)
      | PrimInt63eqb => Some (LambdaANF_primInt_bool_fun Uint63.eqb x y)
      | PrimInt63ltb => Some (LambdaANF_primInt_bool_fun Uint63.ltb x y)
      | PrimInt63leb => Some (LambdaANF_primInt_bool_fun Uint63.leb x y)
      | PrimInt63compare => Some (LambdaANF_primInt_compare_fun Uint63.compare x y)
      | PrimInt63addc => Some (LambdaANF_primInt_carry_fun Uint63.addc x y)
      | PrimInt63addcarryc => Some (LambdaANF_primInt_carry_fun Uint63.addcarryc x y)
      | PrimInt63subc => Some (LambdaANF_primInt_carry_fun Uint63.subc x y)
      | PrimInt63subcarryc => Some (LambdaANF_primInt_carry_fun Uint63.subcarryc x y)
      | PrimInt63mulc => Some (LambdaANF_primInt_prod_fun Uint63.mulc x y)
      | PrimInt63diveucl => Some (LambdaANF_primInt_prod_fun Uint63.diveucl x y)
      | _ => None
      end
  | [ Vprim (primInt x) ; Vprim (primInt y) ; Vprim (primInt z) ] =>
      match op with
      | PrimInt63diveucl_21 => Some (LambdaANF_primInt_diveucl_21 x y z)
      | PrimInt63addmuldiv => Some (LambdaANF_primInt_addmuldiv x y z)
      | _ => None
      end
  | _ => None
  end.

End LambdaANF_PRIMITIVE_WRAPPERS.

Section PRIMITIVE_TRANSLATION_CORRECT.

Notation i32_glob gidx := (In gidx [ glob_result ; glob_out_of_mem ; glob_mem_ptr ; glob_cap ]).
Notation i64_glob gidx := (In gidx [ glob_tmp1 ; glob_tmp2 ; glob_tmp3 ; glob_tmp4 ]).


Variable cenv:LambdaANF.cps.ctor_env.
Variable funenv : fun_env.
Variable fenv   : fname_env.
Variable nenv : LambdaANF.cps_show.name_env.
Variable penv : LambdaANF.toplevel.prim_env.

Context `{ho : host}.

(* Misc. tactics (most duplicated from main proof file) *)

Ltac simpl_eq :=
  repeat lazymatch goal with
  | H: nat_to_i32 _ = nat_to_i32 _ |- _ =>
        injection H as H
  | H: N_to_i32 _ = N_to_i32 _ |- _ =>
        injection H as H
  | H: _ = Wasm_int.Int32.Z_mod_modulus _ |- _ =>
         rewrite Wasm_int.Int32.Z_mod_modulus_id in H; last lia
  | H: Wasm_int.Int32.Z_mod_modulus _ = _ |- _ =>
          rewrite Wasm_int.Int32.Z_mod_modulus_id in H; last lia
  | H: Z.of_nat _ = Z.of_nat _ |- _ =>
         apply Nat2Z.inj in H
  | H: Z.of_N _ = Z.of_N _ |- _ =>
         apply N2Z.inj in H
  end.

Ltac solve_eq_global x y :=
  assert (x = y); first
    (try assert (N_to_i32 x = N_to_i32 y) by congruence; simpl_eq; done); subst y.

(* TODO add case when global was updated etc. *)
Ltac solve_eq_mem m1 m2 :=
  assert (m1 = m2) by congruence; subst m2.

(* proves and substitutes equality on given vars, the first one is kept *)
Ltac solve_eq x y :=
  lazymatch goal with
  (* equality on global mems *)
  | H: smem ?s _ = Some x |- _ => solve_eq_mem x y
  (* equality on globals *)
  | H: _ |- _ => solve_eq_global x y
  end.

Local Ltac reduce_under_label:=
  eapply rt_trans;
  [try apply app_trans|];
  [try apply app_trans_const; auto|];
  [try eapply reduce_trans_label1|].

Ltac Zify.zify_post_hook ::= Z.div_mod_to_equations.

Definition local_holds_address_to_i64 (sr : store_record) (fr : frame) (l : localidx) addr val (m : meminst) bs : Prop :=
    lookup_N fr.(f_locs) l = Some (VAL_num (VAL_int32 addr))
    /\ load m (N_of_uint i32m addr) 0%N (tnum_length T_i64) = Some bs
    /\ wasm_deserialise bs T_i64 = (VAL_int64 val).

(* Main reduction related lemmas *)

(* only used for primitives, thus specialized to 52 bytes of mem usage *)
Lemma store_preserves_INV (sr : store_record) : forall fr m addr off v,
  INV fenv nenv sr fr ->
  smem sr (f_inst fr) = Some m ->
  (off + 8 <= 52)%N ->
  (Z.of_N addr + Z.of_N 52 <= Z.of_N (mem_length m) < Int32.modulus)%Z ->
  exists sr' m',
    smem sr' (f_inst fr) = Some m'
    /\ mem_length m = mem_length m'
    /\ store m addr off (serialise_num v) (length (serialise_num v)) = Some m'
    /\ smem_store sr (f_inst fr) addr off v (typeof_num v) = Some sr'
    /\ INV fenv nenv sr' fr
    /\ (forall a, (a + 4 <= (addr + off))%N -> load_i32 m a = load_i32 m' a)
    /\ (forall a, (a + 8 <= (addr + off))%N -> load_i64 m a = load_i64 m' a)
    /\ s_funcs sr = s_funcs sr'
    /\ (forall g gv, sglob_val sr (f_inst fr) g = gv -> sglob_val sr' (f_inst fr) g = gv)
    /\ (Z.of_N addr + Z.of_N 52 <= Z.of_N (mem_length m') < Int32.modulus)%Z.
Proof.
  intros fr m addr off v HINV Hm Hoff Haddr.
  unfold page_size in *. simpl_modulus_in Haddr.
  have I := HINV. destruct I as [_ [_ [_ [_ [_ [_ [[Hmeminst [m0 [Hmem0 [size Hm0size]]]] _]]]]]]].
  replace m0 with m in * by congruence. clear Hmem0.
  destruct Hm0size as [Hmemsize [Hmemmaxsize Hsizebound]].
  assert (Hsrmem: lookup_N (s_mems sr) 0 = Some m)
      by now unfold smem in Hm; rewrite Hmeminst in Hm; cbn in Hm; destruct (s_mems sr).
  assert (Hstore: exists m', store m addr off (serialise_num v) (length (serialise_num v)) = Some m').
  { destruct v; apply notNone_Some, enough_space_to_store; cbn in *; unfold_serialise; cbn; lia. }
  destruct Hstore as [m' Hstore].
  remember (upd_s_mem sr (set_nth m' sr.(s_mems) (N.to_nat 0) m')) as sr'.
  assert (Hsmem_store : smem_store sr (f_inst fr) addr off v (typeof_num v) = Some sr'). {
    unfold smem_store; rewrite Hmeminst; cbn.
    destruct (s_mems sr). now cbn in Hsrmem.
    replace m1 with m in * by now cbn in *.
    cbn.
    replace (ssrnat.nat_of_bin (tnum_length (typeof_num v))) with (Datatypes.length (serialise_num v))
         by now destruct v.
    now rewrite Hstore Heqsr'. }
  assert (Hmemlength': mem_length m = mem_length m'). {
    unfold store in Hstore.
    destruct (addr + off + N.of_nat (Datatypes.length (serialise_num v)) <=? mem_length m)%N=>//.
    now edestruct (write_bytes_meminst_preserve_type). }
  exists sr', m'; auto.

  split.
  { unfold smem_store in Hsmem_store. rewrite Hmeminst in Hsmem_store. cbn in *.
    rewrite Hsrmem in Hsmem_store. unfold smem.
    rewrite Hmeminst Heqsr'.
    now destruct (s_mems sr). }

  do 4 (split; auto). { (* INV *)
    apply update_mem_preserves_INV with (vd:=m') (s:=sr) (m:=m) (m':=m'); auto.
    - lia.
    - rewrite store_offset_eq in Hstore. eapply store_lim_max in Hstore.
      congruence.
    - exists size. split; auto.
      now rewrite /mem_size -Hmemlength'.
  }
  split. { (* all i32 values in mem are preserved *)
    intros.
    assert (exists v', load_i32 m a = Some v') as Hex. by apply enough_space_to_load; lia.
    destruct Hex as [v' Hv']; rewrite Hv'; symmetry; destruct v; rewrite store_offset_eq in Hstore.
    - now eapply load_store_load_i32 in Hstore.
    - now eapply load_store_load_i32' in Hstore.
    - now eapply load_store_load_i32 in Hstore.
    - now eapply load_store_load_i32' in Hstore.
  }
  split. { (* all i64 values in mem are preserved *)
    intros.
    assert (exists v', load_i64 m a = Some v') as Hex by now apply enough_space_to_load_i64; lia.
    destruct Hex as [v' Hv']; rewrite Hv'; symmetry; destruct v; rewrite store_offset_eq in Hstore.
    - now eapply load_store_load_i64 in Hstore.
    - now eapply load_store_load_i64' in Hstore.
    - now eapply load_store_load_i64 in Hstore.
    - now eapply load_store_load_i64' in Hstore.
  }
  unfold smem_store in Hsmem_store.
  destruct (lookup_N (inst_mems (f_inst fr)) 0). 2: discriminate.
  destruct (lookup_N (s_mems sr) m1)=>//.
  destruct (store m2 addr off (serialise_num v) (ssrnat.nat_of_bin (tnum_length (typeof_num v))))=>//.
  rewrite -Hmemlength'.
  by inv Hsmem_store.
Qed.

Lemma make_carry_reduce (ord : N) : forall state sr fr m gmp res,
  INV fenv nenv sr fr ->
  smem sr (f_inst fr) = Some m ->
  sglob_val sr (f_inst fr) glob_mem_ptr = Some (VAL_num (VAL_int32 (N_to_i32 gmp))) ->
  (Z.of_N gmp + Z.of_N 52 <= Z.of_N (mem_length m) < Int32.modulus)%Z ->
  sglob_val sr (f_inst fr) glob_tmp1 = Some (VAL_num (VAL_int64 (Int64.repr res))) ->
  exists (sr': store_record) m',
    reduce_trans
      (state, sr, fr, map AI_basic (make_carry glob_mem_ptr ord glob_tmp1))
      (state, sr', fr, [$VN (VAL_int32 (N_to_i32 (gmp + 8)%N))])
    /\ INV fenv nenv sr' fr
    /\ smem sr' (f_inst fr) = Some m'
    /\ sglob_val sr' (f_inst fr) glob_mem_ptr = Some (VAL_num (VAL_int32 (N_to_i32 (gmp + 16))))
    (* address gmp points to i64 result *)
    /\ load_i64 m' gmp = Some (VAL_int64 (Int64.repr res))
    (* address gmp + 8 points to ordinal *)
    /\ load_i32 m' (gmp + 8)%N = Some (VAL_int32 (N_to_i32 ord))
    (* address gmp + 12 points to the address of the result (gmp) *)
    /\ load_i32 m' (gmp + 12)%N = Some (VAL_int32 (N_to_i32 gmp))
    (* Values in memory below gmp are preserved *)
    /\ (forall a, (a + 4 <= gmp)%N -> load_i32 m a = load_i32 m' a)
    /\ (forall a, (a + 8 <= gmp)%N -> load_i64 m a = load_i64 m' a)
    /\ s_funcs sr = s_funcs sr'
    /\ mem_length m = mem_length m'.
Proof with eassumption.
  intros state sr fr m gmp res HINV Hmem Hgmp HenoughMem Hres.
  assert (0 + 8 <= page_size)%N as Hoff1 by now unfold page_size.
  assert (8 + 8 <= page_size)%N as Hoff2 by now unfold page_size.
  assert (12 + 8 <= page_size)%N as Hoff3 by now unfold page_size.
  remember (VAL_int64 (Int64.repr res)) as res_val.
  assert (HdesRes: wasm_deserialise (serialise_num res_val) T_i64 = res_val) by now apply deserialise_serialise; subst res_val.
  remember (VAL_int32 (Int32.repr (Z.of_N gmp))) as res_addr.
  assert (HdesResAddr: wasm_deserialise (serialise_num res_addr) T_i32 = res_addr) by now apply deserialise_serialise; subst res_addr.
  remember (VAL_int32 (Int32.repr (Z.of_N ord))) as ord_val.
  assert (HdesOrd: wasm_deserialise (serialise_num ord_val) T_i32 = ord_val) by now apply deserialise_serialise; subst ord_val.
  remember (VAL_int32 (Int32.repr (Z.of_N (gmp + 8)))) as ord_addr.
  remember (VAL_int32 (Int32.repr (Z.of_N (gmp + 12)))) as arg_addr.
  remember (VAL_num (VAL_int32 (N_to_i32 (gmp + 16)))) as newgmp.
  (* Store the 63-bit result at gmp *)
  destruct (store_preserves_INV sr fr m gmp 0%N res_val HINV Hmem Hoff1 HenoughMem)
  as [sr1 [m1 [Hmem1 [Hmemlength1 [Hstore1 [Hsmem_store1 [HINV1 [Hpres32_1 [Hpres64_1 [Hsfs1 [HglobPres1 HenoughMem1]]]]]]]]]]].

  (* Store the ordinal (e.g. C0 or C1) at gmp + 8 *)
  destruct (store_preserves_INV sr1 fr m1 gmp 8%N ord_val HINV1 Hmem1 Hoff2 HenoughMem1)
  as [sr2 [m2 [Hmem2 [Hmemlength2 [Hstore2 [Hsmem_store2 [HINV2 [Hpres32_2 [Hpres64_2 [Hsfs2 [HglobPres2 HenoughMem2]]]]]]]]]]].

  (* Store the _address_ of the result (gmp) at gmp + 12 *)
  destruct (store_preserves_INV sr2 fr m2 gmp 12%N res_addr HINV2 Hmem2 Hoff2 HenoughMem2)
  as [sr3 [m3 [Hmem3 [Hmemlength3 [Hstore3 [Hsmem_store3 [HINV3 [Hpres32_3 [Hpres64_3 [Hsfs_3 [HglobPres3 _]]]]]]]]]]].

  have I := HINV3. destruct I as [_ [_ [_ [HgmpWritable _]]]].
  have I := HINV. destruct I as [_ [_ [_ [_ [_ [_ [_ [_ [_ [_ [_ [_ [_ [Hmult2 _]]]]]]]]]]]]]].

  (* Increment gmp by 16 to point to next free address *)
  destruct (HgmpWritable (VAL_int32 (N_to_i32 (gmp + 16)))) as [sr'  Hupdgmp].
  assert (HINV' : INV fenv nenv sr' fr). {
    apply update_global_preserves_INV with (sr:=sr3) (i:=glob_mem_ptr) (m:=m3) (num:=(VAL_int32 (N_to_i32 (gmp+16))))=> //. now cbn.
    move => _ n [Heqn Hrangen].
    replace n with (gmp + 16)%N by (inv Heqn; simpl_eq; lia).
    unfold page_size in *. lia.
    move => _ n [Heqn Hrangen].
    replace n with (gmp + 16)%N by (inv Heqn; simpl_eq; lia).
    assert (-1 < Z.of_N gmp < Wasm_int.Int32.modulus)%Z by lia.
    destruct (Hmult2 _ _ Hmem Hgmp H) as (n0 & Hn0).
    now exists (n0 + 8)%N. }
  assert (Hgmp' : sglob_val sr' (f_inst fr) glob_mem_ptr = Some newgmp). {
    apply HglobPres1, HglobPres2, HglobPres3 in Hgmp.
    subst newgmp. now apply update_global_get_same with (sr:=sr3). }
  (* All i32 values below gmp are preserved *)
  assert (Hpres32: forall a, (a + 4 <= gmp)%N -> load_i32 m a = load_i32 m3 a). {
    intros. rewrite ->Hpres32_1, ->Hpres32_2, ->Hpres32_3; auto; lia. }
  (* All i64 values below gmp are preserved *)
  assert (Hpres64: forall a, (a + 8 <= gmp)%N -> load_i64 m a = load_i64 m3 a). {
    intros. rewrite ->Hpres64_1, ->Hpres64_2, -> Hpres64_3; auto; lia. }
  exists sr', m3.
  split. { (* make_carry instructions reduce *)
    intros.
    assert (HrewriteGmp : N_of_uint i32m (N_to_i32 gmp) = gmp). {
      cbn. rewrite Int32.Z_mod_modulus_id; lia. }
    unfold make_carry.
    separate_instr.
    dostep_nary 0. apply r_global_get...
    dostep_nary_eliml 0 1. apply r_global_get...
    dostep_nary 2. apply r_store_success; rewrite HrewriteGmp; subst res_val...
    dostep_nary 0. apply r_global_get; apply HglobPres1 in Hgmp...
    dostep_nary 2. apply r_store_success; rewrite HrewriteGmp; subst ord_val...
    dostep_nary 0. apply r_global_get; apply HglobPres1, HglobPres2 in Hgmp...
    dostep_nary_eliml 0 1. apply r_global_get; apply HglobPres1, HglobPres2 in Hgmp...
    dostep_nary 2. apply r_store_success; rewrite HrewriteGmp; subst res_addr...
    dostep_nary 0. apply r_global_get; apply HglobPres1, HglobPres2, HglobPres3 in Hgmp...
    dostep_nary 2. constructor. apply rs_binop_success; first done.
      cbn; unfold Int32.iadd, Int32.add, Int32.unsigned; cbn.
      rewrite Int32.Z_mod_modulus_id; last lia.
      replace 8%Z with (Z.of_N 8) by now cbn.
      rewrite -N2Z.inj_add. reflexivity.
    dostep_nary_eliml 0 1. apply r_global_get; apply HglobPres1, HglobPres2, HglobPres3 in Hgmp...
    dostep_nary_eliml 2 1. constructor. apply rs_binop_success; first done.
      cbn; unfold Int32.iadd, Int32.add, Int32.unsigned; cbn.
      rewrite Int32.Z_mod_modulus_id; last lia.
      replace 16%Z with (Z.of_N 16) by now cbn.
      rewrite <-N2Z.inj_add. reflexivity.
    dostep_nary_eliml 1 1. apply r_global_set'...
    now apply rt_refl. }
  replace (smem sr' (f_inst fr)) with (smem sr3 (f_inst fr))
       by now eapply update_global_preserves_memory.
  repeat (split; auto).
  - (* Result can be loaded as an i64 from address gmp *)
    rewrite <-Hpres64_3, <-Hpres64_2, <-HdesRes; try lia.
    now eapply store_load_i64 with (m:=m); subst res_val.
  - (* The ordinal can be loaded as an i32 from address gmp + 8 *)
    replace (VAL_int32 (N_to_i32 ord)) with ord_val by now cbn.
    rewrite <-Hpres32_3, <-HdesOrd; try lia.
    now apply store_load_i32 with (m:=m1); subst ord_val; rewrite store_offset_eq in Hstore2.
  - (* The address of the result (gmp) can be loaded from address gmp + 12 *)
    replace (VAL_int32 (N_to_i32 gmp)) with res_addr by auto.
    rewrite <-HdesResAddr; try lia.
    now apply store_load_i32 with (m:=m2); subst res_addr; rewrite store_offset_eq in Hstore3.
  - (* Functions in the store are preserved*)
    rewrite Hsfs1 Hsfs2 Hsfs_3. now eapply update_global_preserves_funcs.
  - (* Length of memory is preserved *)
    now rewrite Hmemlength1 Hmemlength2 Hmemlength3.
Qed.

Lemma addc_reduce (x y : localidx) :
  forall state sr fr m gmp addrx addry bsx bsy n1 n2 c0_tag c1_tag it_carry v,
    INV fenv nenv sr fr ->
    M.get c0_tag cenv = Some (Build_ctor_ty_info (Common.BasicAst.nNamed "C0") (Common.BasicAst.nNamed "carry") it_carry 1%N C0_ord) ->
    M.get c1_tag cenv = Some (Build_ctor_ty_info (Common.BasicAst.nNamed "C1") (Common.BasicAst.nNamed "carry") it_carry 1%N C1_ord) ->
    LambdaANF_primInt_carry_fun c0_tag c1_tag addc n1 n2 = v ->
    (* ((~ (to_Z (n1 + n2) < to_Z n1)%Z /\ v = Vconstr c0_tag [Vprim (AstCommon.primInt ; (n1 + n2)%uint63)]) \/ ((to_Z (n1 + n2) < to_Z n1)%Z /\ v = Vconstr c1_tag [Vprim (AstCommon.primInt ; (n1 + n2)%uint63)])) -> *)
    smem sr (f_inst fr) = Some m ->
    (* Local x holds address to 1st i64 *)
    local_holds_address_to_i64 sr fr x addrx (Int64.repr (to_Z n1)) m bsx ->
    (* Local y holds address to 2nd i64 *)
    local_holds_address_to_i64 sr fr y addry (Int64.repr (to_Z n2)) m bsy ->
    (* There is enough free memory available *)
    (Z.of_N gmp + Z.of_N 52 <= Z.of_N (mem_length m) < Int32.modulus)%Z ->
    sglob_val sr (f_inst fr) glob_mem_ptr = Some (VAL_num (VAL_int32 (N_to_i32 gmp))) ->
    exists (sr': store_record) m',
      (forall instrs,
          reduce_trans
            (state, sr, fr, map AI_basic (apply_add_carry_operation glob_mem_ptr glob_tmp1 x y false) ++ instrs)
            (state, sr', fr, ($VN (VAL_int32 (N_to_i32 (gmp + 8)%N))) :: instrs))
      /\ INV fenv nenv sr' fr
      /\ smem sr' (f_inst fr) = Some m'
      (* gmp points to next free segment of memory *)
      /\ sglob_val sr' (f_inst fr) glob_mem_ptr = Some (VAL_num (VAL_int32 (N_to_i32 (gmp + 16))))
      /\ s_funcs sr = s_funcs sr'
      /\ mem_length m = mem_length m'
      /\ repr_val_LambdaANF_Wasm cenv fenv nenv penv v sr' (f_inst fr) (Val_ptr (gmp + 8)%N)
      (* Values are preserved *)
      /\ (forall (wal : wasm_value) (val : cps.val),
             repr_val_LambdaANF_Wasm cenv fenv nenv penv val sr (f_inst fr) wal ->
             repr_val_LambdaANF_Wasm cenv fenv nenv penv val sr' (f_inst fr) wal).
Proof with eassumption.
  intros ??????????????? HINV Hc0 Hc1 Hv Hmem [Hxinframe  [Hloadx Hdesx]] [Hyinframe [Hloady Hdesy]] HgmpBounds Hgmp.
  have I := HINV. destruct I as [_ [_ [_ [_ [_ [_ [_ [_ [_ [_ [HnoGlobDups [_ [_ [Hmult2 [_ Hi64tempsW]]]]]]]]]]]]]]].
  assert (Hglob_tmp1: i64_glob glob_tmp1) by now constructor.
  destruct (Hi64tempsW _ Hglob_tmp1 (VAL_int64 (Int64.repr (to_Z (n1 + n2)%uint63))))
        as [sr1 Hsr1].
  assert (HINV1 : INV fenv nenv sr1 fr)
      by now apply update_global_preserves_INV with (sr:=sr) (i:=glob_tmp1) (m:=m)
                           (num:=(VAL_int64 (Int64.repr (to_Z (n1 + n2)%uint63)))).
  assert (Hsfs1 : s_funcs sr = s_funcs sr1) by now eapply update_global_preserves_funcs.
  assert (Hmem1 : smem sr1 (f_inst fr) = Some m)
      by now apply update_global_preserves_memory in Hsr1.
  assert (Hgmp1 : sglob_val sr1 (f_inst fr) glob_mem_ptr = Some (VAL_num (VAL_int32 (N_to_i32 gmp)))). {
    now apply update_global_get_other with (j:=glob_tmp1) (sr:=sr) (num:=(VAL_int64 (Int64.repr (to_Z (n1 + n2)%uint63)))). }
  assert (HresVal : sglob_val sr1 (f_inst fr) glob_tmp1 = Some (VAL_num (VAL_int64 (Int64.repr (to_Z (n1 + n2)%uint63)))))
      by now apply update_global_get_same with (sr:=sr).

  assert (-1 < Z.of_N gmp < Int32.modulus)%Z by lia.

  destruct (Hmult2 _ _ Hmem Hgmp H) as [n Hgmpmult2]; clear H.

  have HcarryRedC0 := make_carry_reduce C0_ord state sr1 fr m _ _ HINV1 Hmem1 Hgmp1 HgmpBounds HresVal.
  destruct HcarryRedC0 as [sr_C0 [m_C0 [Hmake_carry_red_C0 [HINV_C0 [Hmem_C0 [Hgmp_C0 [HloadRes_C0 [ HloadOrd_C0 [HloadArg_C0 [Hpres64_C0 [Hpres32_C0 [Hsfs_C0 Hmemlength_C0]]]]]]]]]]]].

  assert (HnewgmpBoundsC0: (Z.of_N (gmp + 16) + 8 <= Z.of_N (mem_length m_C0) < Int32.modulus)%Z) by lia.

  assert (HconstrArgsC0: repr_val_constr_args_LambdaANF_Wasm cenv fenv nenv penv [:: Vprim (AstCommon.primInt; (n1 + n2)%uint63)] sr_C0 (f_inst fr) (4 + (gmp+8))%N). {
    eapply Rcons_l with (wal:=(Val_ptr gmp)) (gmp:=(gmp+16)%N); eauto; try lia.
    now replace (4 + (gmp + 8))%N with (gmp + 12)%N by lia.
    eapply Rprim_v with (gmp:=(gmp + 16)%N); try lia; eauto.
    now constructor. }

  assert (HvalC0: repr_val_LambdaANF_Wasm cenv fenv nenv penv (Vconstr c0_tag [Vprim (AstCommon.primInt ; (n1 + n2)%uint63)]) sr_C0 (f_inst fr) (Val_ptr (gmp + 8)%N)). {
      eapply Rconstr_boxed_v with (v:=Int32.repr (Z.of_N C0_ord)) (sr:=sr_C0) (m:=m_C0) (gmp:=(gmp+16)%N) (addr:=(gmp + 8)%N) (arity:=1) (ord:=C0_ord); auto; try lia.
      - unfold get_ctor_ord; now rewrite Hc0.
      - unfold get_ctor_arity; now rewrite Hc0.
      - now exists (n+4)%N. }

  have HcarryRedC1 := make_carry_reduce C1_ord state sr1 fr m _ _ HINV1 Hmem1 Hgmp1 HgmpBounds HresVal.
  destruct HcarryRedC1 as [sr_C1 [m_C1 [Hmake_carry_red_C1 [HINV_C1 [Hmem_C1 [Hgmp_C1 [HloadRes_C1 [ HloadOrd_C1 [HloadArg_C1 [Hpres64_C1 [Hpres32_C1 [Hsfs_C1 Hmemlength_C1]]]]]]]]]]]].

  assert (HnewgmpBoundsC1: (Z.of_N (gmp + 16) + 8 <= Z.of_N (mem_length m_C1) < Int32.modulus)%Z) by lia.

  assert (HconstrArgsC1: repr_val_constr_args_LambdaANF_Wasm cenv fenv nenv penv [:: Vprim (AstCommon.primInt; (n1 + n2)%uint63)] sr_C1  (f_inst fr) (4 + (gmp+8))%N). {
    eapply Rcons_l with (wal:=(Val_ptr gmp)) (gmp:=(gmp+16)%N); eauto; try lia.
    now replace (4 + (gmp + 8))%N with (gmp + 12)%N by lia.
    eapply Rprim_v with (gmp:=(gmp + 16)%N); try lia; eauto.
    now constructor. }

  assert (HvalC1: repr_val_LambdaANF_Wasm cenv fenv nenv penv (Vconstr c1_tag [Vprim (AstCommon.primInt ; (n1 + n2)%uint63)]) sr_C1 (f_inst fr) (Val_ptr (gmp + 8)%N)). {
    eapply Rconstr_boxed_v with (v:=Int32.repr (Z.of_N C1_ord)) (t:=c1_tag) (sr:=sr_C1) (m:=m_C1) (gmp:=(gmp+16)%N) (addr:=(gmp + 8)%N) (arity:=1) (ord:=C1_ord); auto; try lia.
    - unfold get_ctor_ord; now rewrite Hc1.
    - unfold get_ctor_arity; now rewrite Hc1.
    - now exists (n+4)%N. }

  unfold LambdaANF_primInt_carry_fun in Hv.
  destruct (Z_lt_dec (to_Z (n1 + n2)%uint63) (to_Z n1)) as [Hlt | Hlt].
  { rewrite addc_def_spec in Hv. unfold addc_def in Hv.
    replace (n1 + n2 <? n1)%uint63 with true in Hv by lia.
    exists sr_C1, m_C1.
    split. {
      intros; unfold apply_add_carry_operation.
      (* remember to avoid unfolding *)
      remember ((make_carry glob_mem_ptr C1_ord glob_tmp1)) as carryInstrsC1;
        remember ((make_carry glob_mem_ptr C0_ord glob_tmp1)) as carryInstrsC0;
        separate_instr.
      (* Load and deserialise value of x *)
      dostep_nary 0. eapply r_local_get...
      dostep_nary 1. eapply r_load_success...
      rewrite Hdesx.
      (* Load and deserialise value of y *)
      dostep_nary_eliml 0 1. eapply r_local_get...
      dostep_nary_eliml 1 1. eapply r_load_success...
      rewrite Hdesy.
      (* Apply addition binary operation *)
      dostep_nary 2. constructor; apply rs_binop_success=>//.
      (* Apply bitmask *)
      dostep_nary 2. constructor; apply rs_binop_success=>//.
      rewrite ->uint63_add_i64_add.
      (* Temporarily store the result in a global *)
      dostep_nary 1. eapply r_global_set'...
      (* Put the result on the stack again *)
      dostep_nary 0. eapply r_global_get...
      (* Load and deserialise value of x *)
      dostep_nary_eliml 0 1. eapply r_local_get...
      dostep_nary_eliml 1 1. eapply r_load_success...
      rewrite Hdesx.
      (* Check for overflow, step into the if-branch and reduce the make_carry instructions *)
      dostep_nary 2. constructor. apply rs_relop=>//.
      dostep_nary 1. constructor. apply rs_if_true; rewrite uint63_lt_int64_lt=>//.
      dostep_nary 0. eapply r_block with (t1s:=[::]) (t2s:=[:: T_num T_i32])(vs:=[::]); auto.
      reduce_under_label. subst carryInstrsC1; apply Hmake_carry_red_C1.
      dostep_nary 0. constructor; apply rs_label_const; auto.
      now apply rt_refl. }
    repeat (split; first congruence).
    intros.
    eapply val_relation_depends_on_mem_smaller_than_gmp_and_funcs with (sr:=sr) (m:=m) (gmp:=gmp) (gmp':=(gmp + 16)%N);
      eauto; try lia.
    now rewrite Hsfs1. }
  { (* There is overflow <-> x + y < x *)
    rewrite addc_def_spec in Hv. unfold addc_def in Hv.
    replace (n1 + n2 <? n1)%uint63 with false in Hv by lia.
    exists sr_C0, m_C0.
    split. {
      intros. unfold apply_add_carry_operation.
      remember (make_carry glob_mem_ptr C1_ord glob_tmp1) as carryInstrsC1.
      remember (make_carry glob_mem_ptr C0_ord glob_tmp1) as carryInstrsC0.
      separate_instr.
      dostep_nary 0. eapply r_local_get...
      dostep_nary 1. eapply r_load_success...
      rewrite Hdesx.
      dostep_nary_eliml 0 1. eapply r_local_get...
      dostep_nary_eliml 1 1. eapply r_load_success...
      rewrite Hdesy.
      dostep_nary 2. constructor; apply rs_binop_success=>//.
      dostep_nary 2. constructor; apply rs_binop_success=>//.
      rewrite ->uint63_add_i64_add.
      dostep_nary 1. eapply r_global_set'...
      dostep_nary 0. eapply r_global_get...
      dostep_nary_eliml 0 1. eapply r_local_get...
      dostep_nary_eliml 1 1. eapply r_load_success...
      rewrite Hdesx.
      dostep_nary 2. constructor; apply rs_relop=>//.
      dostep_nary 1. constructor; apply rs_if_false; rewrite uint63_nlt_int64_nlt; auto.
      dostep_nary 0. eapply r_block with (t1s:=[::]) (t2s:=[:: T_num T_i32])(vs:=[::]); auto.
      reduce_under_label. subst carryInstrsC0; apply Hmake_carry_red_C0.
      dostep_nary 0. constructor; apply rs_label_const; auto.
      now apply rt_refl. }
    repeat (split; first congruence).
    intros.
    eapply val_relation_depends_on_mem_smaller_than_gmp_and_funcs
      with (sr:=sr) (m:=m) (gmp:=gmp) (gmp':=(gmp + 16)%N); eauto; try lia.
      now rewrite Hsfs1. }
Qed.

Lemma addcarryc_reduce (x y : localidx) :
  forall state sr fr m gmp addrx addry bsx bsy n1 n2 c0_tag c1_tag it_carry v,
    INV fenv nenv sr fr ->
    M.get c0_tag cenv = Some (Build_ctor_ty_info (Common.BasicAst.nNamed "C0") (Common.BasicAst.nNamed "carry") it_carry 1%N C0_ord) ->
    M.get c1_tag cenv = Some (Build_ctor_ty_info (Common.BasicAst.nNamed "C1") (Common.BasicAst.nNamed "carry") it_carry 1%N C1_ord) ->
    LambdaANF_primInt_carry_fun c0_tag c1_tag addcarryc n1 n2 = v ->
    smem sr (f_inst fr) = Some m ->
    (* Local x holds address to 1st i64 *)
    local_holds_address_to_i64 sr fr x addrx (Int64.repr (to_Z n1)) m bsx ->
    (* Local y holds address to 2nd i64 *)
    local_holds_address_to_i64 sr fr y addry (Int64.repr (to_Z n2)) m bsy ->
    (* There is enough free memory available *)
    (Z.of_N gmp + Z.of_N 52 <= Z.of_N (mem_length m) < Int32.modulus)%Z ->
    sglob_val sr (f_inst fr) glob_mem_ptr = Some (VAL_num (VAL_int32 (N_to_i32 gmp))) ->
    exists (sr': store_record) m',
      (forall instrs,
          reduce_trans
            (state, sr, fr, map AI_basic (apply_add_carry_operation glob_mem_ptr glob_tmp1 x y true) ++ instrs)
            (state, sr', fr, ($VN (VAL_int32 (N_to_i32 (gmp + 8)%N))) :: instrs))
      /\ INV fenv nenv sr' fr
      /\ smem sr' (f_inst fr) = Some m'
      (* gmp points to next free segment of memory *)
      /\ sglob_val sr' (f_inst fr) glob_mem_ptr = Some (VAL_num (VAL_int32 (N_to_i32 (gmp + 16))))
      /\ s_funcs sr = s_funcs sr'
      /\ mem_length m = mem_length m'
      /\ repr_val_LambdaANF_Wasm cenv fenv nenv penv v sr' (f_inst fr) (Val_ptr (gmp + 8)%N)
      (* Values are preserved *)
      /\ (forall (wal : wasm_value) (val : cps.val),
             repr_val_LambdaANF_Wasm cenv fenv nenv penv val sr (f_inst fr) wal ->
             repr_val_LambdaANF_Wasm cenv fenv nenv penv val sr' (f_inst fr) wal).
Proof with eassumption.
  intros ??????????????? HINV Hc0 Hc1 Hv Hmem [Hxinframe  [Hloadx Hdesx]] [Hyinframe [Hloady Hdesy]] HgmpBounds Hgmp.
  have I := HINV. destruct I as [_ [_ [_ [_ [_ [_ [_ [_ [_ [_ [HnoGlobDups [_ [_ [Hmult2 [_ Hi64tempsW]]]]]]]]]]]]]]].
  assert (Hglob_tmp1: i64_glob glob_tmp1) by now constructor.
  destruct (Hi64tempsW _ Hglob_tmp1 (VAL_int64 (Int64.repr (to_Z (n1 + n2 + 1)%uint63)))) as [sr1 Hsr1].
  assert (HINV1 : INV fenv nenv sr1 fr). {
    apply update_global_preserves_INV with (sr:=sr) (i:=glob_tmp1) (m:=m) (num:=(VAL_int64 (Int64.repr (to_Z (n1 + n2 + 1)%uint63))))=>/=//. tauto. }
  assert (Hsfs1 : s_funcs sr = s_funcs sr1)
      by now eapply update_global_preserves_funcs; eauto.
  assert (Hmem1 : smem sr1 (f_inst fr) = Some m)
      by now apply update_global_preserves_memory in Hsr1.
  assert (Hgmp1 : sglob_val sr1 (f_inst fr) glob_mem_ptr = Some (VAL_num (VAL_int32 (N_to_i32 gmp)))). {
    now apply update_global_get_other with (j:=glob_tmp1) (sr:=sr) (num:=(VAL_int64 (Int64.repr (to_Z (n1 + n2 + 1)%uint63)))). }
  assert (HresVal : sglob_val sr1 (f_inst fr) glob_tmp1 = Some (VAL_num (VAL_int64 (Int64.repr (to_Z (n1 + n2 + 1)%uint63)))))
      by now apply update_global_get_same with (sr:=sr); auto.

  assert (-1 < Z.of_N gmp < Int32.modulus)%Z by lia.

  destruct (Hmult2 _ _ Hmem Hgmp H) as [n Hgmpmult2]; clear H.

  have HcarryRedC0 := make_carry_reduce C0_ord state sr1 fr m _ _ HINV1 Hmem1 Hgmp1 HgmpBounds HresVal.
  destruct HcarryRedC0 as [sr_C0 [m_C0 [Hmake_carry_red_C0 [HINV_C0 [Hmem_C0 [Hgmp_C0 [HloadRes_C0 [ HloadOrd_C0 [HloadArg_C0 [Hpres64_C0 [Hpres32_C0 [Hsfs_C0 Hmemlength_C0]]]]]]]]]]]].

  assert (HnewgmpBoundsC0: (Z.of_N (gmp + 16) + 8 <= Z.of_N (mem_length m_C0) < Int32.modulus)%Z) by lia.

  assert (HconstrArgsC0: repr_val_constr_args_LambdaANF_Wasm cenv fenv nenv penv [:: Vprim (AstCommon.primInt; (n1 + n2 + 1)%uint63)] sr_C0 (f_inst fr) (4 + (gmp+8))%N). {
    eapply Rcons_l with (wal:=(Val_ptr gmp)) (gmp:=(gmp+16)%N); try lia; eauto.
    unfold wasm_value_to_i32, wasm_value_to_u32; replace (4 + (gmp + 8))%N with (gmp +12)%N;[auto|lia].
    eapply Rprim_v with (gmp:=(gmp + 16)%N); try lia; eauto.
    now constructor. }

  assert (HvalC0: repr_val_LambdaANF_Wasm cenv fenv nenv penv (Vconstr c0_tag [Vprim (AstCommon.primInt ; (n1 + n2 + 1)%uint63)]) sr_C0 (f_inst fr) (Val_ptr (gmp + 8)%N)). {
      eapply Rconstr_boxed_v with (v:=Int32.repr (Z.of_N C0_ord)) (t:=c0_tag) (sr:=sr_C0) (m:=m_C0) (gmp:=(gmp+16)%N) (addr:=(gmp + 8)%N) (arity:=1) (ord:=C0_ord); auto; try lia.
      - now rewrite /get_ctor_ord Hc0.
      - now rewrite /get_ctor_arity Hc0.
      - now exists (n+4)%N. }

  have HcarryRedC1 := make_carry_reduce C1_ord state sr1 fr m _ _ HINV1 Hmem1 Hgmp1 HgmpBounds HresVal.
  destruct HcarryRedC1 as [sr_C1 [m_C1 [Hmake_carry_red_C1 [HINV_C1 [Hmem_C1 [Hgmp_C1 [HloadRes_C1 [ HloadOrd_C1 [HloadArg_C1 [Hpres64_C1 [Hpres32_C1 [Hsfs_C1 Hmemlength_C1]]]]]]]]]]]].

  assert (HnewgmpBoundsC1: (Z.of_N (gmp + 16) + 8 <= Z.of_N (mem_length m_C1) < Int32.modulus)%Z) by lia.

  assert (HconstrArgsC1: repr_val_constr_args_LambdaANF_Wasm cenv fenv nenv penv [:: Vprim (AstCommon.primInt; (n1 + n2 + 1)%uint63)] sr_C1  (f_inst fr) (4 + (gmp+8))%N). {
    eapply Rcons_l with (wal:=(Val_ptr gmp)) (gmp:=(gmp+16)%N); try lia; eauto.
    now replace (4 + (gmp + 8))%N with (gmp + 12)%N by lia.
    eapply Rprim_v with (gmp:=(gmp + 16)%N); try lia; eauto.
    now constructor. }

  assert (HvalC1: repr_val_LambdaANF_Wasm cenv fenv nenv penv (Vconstr c1_tag [Vprim (AstCommon.primInt ; (n1 + n2 + 1)%uint63)]) sr_C1 (f_inst fr) (Val_ptr (gmp + 8)%N)). {
    eapply Rconstr_boxed_v with (v:=Int32.repr (Z.of_N C1_ord)) (t:=c1_tag) (sr:=sr_C1) (m:=m_C1) (gmp:=(gmp+16)%N) (addr:=(gmp + 8)%N) (arity:=1) (ord:=C1_ord); auto; try lia.
      - now rewrite /get_ctor_ord Hc1.
      - now rewrite /get_ctor_arity Hc1.
      - now exists (n+4)%N. }

  unfold LambdaANF_primInt_carry_fun in Hv.
  destruct (Z_le_dec (to_Z (n1 + n2 + 1)%uint63) (to_Z n1)) as [Hlt | Hlt].
  { rewrite addcarryc_def_spec in Hv. unfold addcarryc_def, addcarry in Hv.
    replace (n1 + n2 + 1 <=? n1)%uint63 with true in Hv by lia.
    exists sr_C1, m_C1.
    split. {
      intros; unfold apply_add_carry_operation.
      (* remember to avoid unfolding *)
      remember (make_carry glob_mem_ptr C1_ord glob_tmp1) as carryInstrsC1.
      remember (make_carry glob_mem_ptr C0_ord glob_tmp1) as carryInstrsC0.
      separate_instr.
      (* Load and deserialise value of x *)
      dostep_nary 0. eapply r_local_get...
      dostep_nary 1. eapply r_load_success...
      rewrite Hdesx.
      (* Load and deserialise value of y *)
      dostep_nary_eliml 0 1. eapply r_local_get...
      dostep_nary_eliml 1 1. eapply r_load_success...
      rewrite Hdesy.
      (* Apply addition binary operation *)
      dostep_nary 2. constructor; apply rs_binop_success=>//.
      dostep_nary 2. constructor; apply rs_binop_success=>//.
      (* Apply bitmask *)
      dostep_nary 2. constructor; apply rs_binop_success=>//.
      replace 1%Z with (to_Z 1) by auto. rewrite ->uint63_add_i64_add'.
      (* Temporarily store the result in a global *)
      dostep_nary 1. eapply r_global_set'...
      (* Put the result on the stack again *)
      dostep_nary 0. eapply r_global_get...
      (* Load and deserialise value of x *)
      dostep_nary_eliml 0 1. eapply r_local_get...
      dostep_nary_eliml 1 1. eapply r_load_success...
      rewrite Hdesx.
      (* Check for overflow, step into the if-branch and reduce the make_carry instructions *)
      dostep_nary 2. constructor; apply rs_relop=>//.
      dostep_nary 1. constructor. apply rs_if_true. rewrite uint63_le_int64_le=>//.
      dostep_nary 0. eapply r_block with (t1s:=[::]) (t2s:=[:: T_num T_i32])(vs:=[::]); auto.
      reduce_under_label. subst carryInstrsC1; apply Hmake_carry_red_C1.
      dostep_nary 0. constructor; apply rs_label_const; auto.
      now apply rt_refl. }
    repeat (split; first congruence).
    intros. eapply val_relation_depends_on_mem_smaller_than_gmp_and_funcs with (sr:=sr) (m:=m) (gmp:=gmp) (gmp':=(gmp + 16)%N);
     eauto; try lia.
     now rewrite Hsfs1. }
  { (* There is overflow <-> x + y < x *)
    rewrite addcarryc_def_spec in Hv. unfold addcarryc_def, addcarry in Hv.
    replace (n1 + n2 + 1 <=? n1)%uint63 with false in Hv by lia.
    exists sr_C0, m_C0.
    split. {
      intros; unfold apply_add_carry_operation.
      remember (make_carry glob_mem_ptr C1_ord glob_tmp1) as carryInstrsC1.
      remember (make_carry glob_mem_ptr C0_ord glob_tmp1) as carryInstrsC0.
      separate_instr.
      dostep_nary 0. eapply r_local_get...
      dostep_nary 1. eapply r_load_success...
      rewrite Hdesx.
      dostep_nary_eliml 0 1. eapply r_local_get...
      dostep_nary_eliml 1 1. eapply r_load_success...
      rewrite Hdesy.
      dostep_nary 2. constructor; apply rs_binop_success=>//.
      dostep_nary 2. constructor; apply rs_binop_success=>//.
      dostep_nary 2. constructor; apply rs_binop_success=>//.
      replace 1%Z with (to_Z 1) by now cbn. rewrite ->uint63_add_i64_add'.
      dostep_nary 1. eapply r_global_set'...
      dostep_nary 0. eapply r_global_get...
      dostep_nary_eliml 0 1. eapply r_local_get...
      dostep_nary_eliml 1 1. eapply r_load_success...
      rewrite Hdesx.
      dostep_nary 2. constructor; apply rs_relop=>//.
      dostep_nary 1. constructor; apply rs_if_false. rewrite uint63_nle_int64_nle; auto.
      dostep_nary 0. eapply r_block with (t1s:=[::]) (t2s:=[:: T_num T_i32])(vs:=[::]); auto.
      reduce_under_label. subst carryInstrsC0. apply Hmake_carry_red_C0.
      dostep_nary 0. constructor; apply rs_label_const; auto.
      now apply rt_refl. }
    repeat (split; first congruence).
    intros; eapply val_relation_depends_on_mem_smaller_than_gmp_and_funcs with (sr:=sr) (m:=m) (gmp:=gmp) (gmp':=(gmp + 16)%N);
      eauto; try lia.
    now rewrite Hsfs1. }
Qed.

Lemma subc_reduce (x y : localidx) :
  forall state sr fr m gmp addrx addry bsx bsy n1 n2 c0_tag c1_tag it_carry v,
    INV fenv nenv sr fr ->
    M.get c0_tag cenv = Some (Build_ctor_ty_info (Common.BasicAst.nNamed "C0") (Common.BasicAst.nNamed "carry") it_carry 1%N C0_ord) ->
    M.get c1_tag cenv = Some (Build_ctor_ty_info (Common.BasicAst.nNamed "C1") (Common.BasicAst.nNamed "carry") it_carry 1%N C1_ord) ->
    LambdaANF_primInt_carry_fun c0_tag c1_tag subc n1 n2 = v ->
    smem sr (f_inst fr) = Some m ->
    local_holds_address_to_i64 sr fr x addrx (Int64.repr (to_Z n1)) m bsx ->
    local_holds_address_to_i64 sr fr y addry (Int64.repr (to_Z n2)) m bsy ->
    (Z.of_N gmp + Z.of_N 52 <= Z.of_N (mem_length m) < Int32.modulus)%Z ->
    sglob_val sr (f_inst fr) glob_mem_ptr = Some (VAL_num (VAL_int32 (N_to_i32 gmp))) ->
    exists (sr': store_record) m',
      (forall instrs,
          reduce_trans
            (state, sr, fr, map AI_basic (apply_sub_carry_operation glob_mem_ptr glob_tmp1 x y false) ++ instrs)
            (state, sr', fr, ($VN (VAL_int32 (N_to_i32 (gmp + 8)%N))) :: instrs))
      /\ INV fenv nenv sr' fr
      /\ smem sr' (f_inst fr) = Some m'
      /\ sglob_val sr' (f_inst fr) glob_mem_ptr = Some (VAL_num (VAL_int32 (N_to_i32 (gmp + 16))))
      /\ s_funcs sr = s_funcs sr'
      /\ mem_length m = mem_length m'
      /\ repr_val_LambdaANF_Wasm cenv fenv nenv penv v sr' (f_inst fr) (Val_ptr (gmp + 8)%N)
      /\ (forall (wal : wasm_value) (val : cps.val),
             repr_val_LambdaANF_Wasm cenv fenv nenv penv val sr (f_inst fr) wal ->
             repr_val_LambdaANF_Wasm cenv fenv nenv penv val sr' (f_inst fr) wal).
Proof with eassumption.
  intros ??????????????? HINV Hc0 Hc1 Hv Hmem [Hxinframe [Hloadx Hdesx]] [Hyinframe [Hloady Hdesy]] HgmpBounds Hgmp.
  have I := HINV. destruct I as [_ [_ [_ [_ [_ [_ [_ [_ [_ [_ [HnoGlobDups [_ [_ [Hmult2 [_ Hi64tempsW]]]]]]]]]]]]]]].
  assert (Hglob_tmp1: i64_glob glob_tmp1) by now constructor.
  destruct (Hi64tempsW _ Hglob_tmp1 (VAL_int64 (Int64.repr (to_Z (n1 - n2)%uint63)))) as [sr1 Hsr1].
  assert (HINV1 : INV fenv nenv sr1 fr). {
    apply update_global_preserves_INV with (sr:=sr) (i:=glob_tmp1) (m:=m) (num:=(VAL_int64 (Int64.repr (to_Z (n1 - n2 )%uint63))))=> /=//. tauto. }
  assert (Hsfs1 : s_funcs sr = s_funcs sr1) by now eapply update_global_preserves_funcs; eauto.
  assert (Hmem1 : smem sr1 (f_inst fr) = Some m)
      by now apply update_global_preserves_memory in Hsr1.
  assert (Hgmp1 : sglob_val sr1 (f_inst fr) glob_mem_ptr = Some (VAL_num (VAL_int32 (N_to_i32 gmp)))). {
    apply update_global_get_other with (j:=glob_tmp1) (sr:=sr) (num:=(VAL_int64 (Int64.repr (to_Z (n1 - n2)%uint63)))); auto. discriminate. }
  assert (HresVal : sglob_val sr1 (f_inst fr) glob_tmp1 = Some (VAL_num (VAL_int64 (Int64.repr (to_Z (n1 - n2)%uint63)))))
      by now apply update_global_get_same with (sr:=sr); auto.

  assert (-1 < Z.of_N gmp < Int32.modulus)%Z by lia.

  destruct (Hmult2 _ _ Hmem Hgmp H) as [n Hgmpmult2]; clear H.

  have HcarryRedC0 := make_carry_reduce C0_ord state sr1 fr m _ _ HINV1 Hmem1 Hgmp1 HgmpBounds HresVal.
  destruct HcarryRedC0 as [sr_C0 [m_C0 [Hmake_carry_red_C0 [HINV_C0 [Hmem_C0 [Hgmp_C0 [HloadRes_C0 [ HloadOrd_C0 [HloadArg_C0 [Hpres64_C0 [Hpres32_C0 [Hsfs_C0 Hmemlength_C0]]]]]]]]]]]].

  assert (HnewgmpBoundsC0: (Z.of_N (gmp + 16) + 8 <= Z.of_N (mem_length m_C0) < Int32.modulus)%Z) by lia.

  assert (HconstrArgsC0: repr_val_constr_args_LambdaANF_Wasm cenv fenv nenv penv [:: Vprim (AstCommon.primInt; (n1 - n2)%uint63)] sr_C0 (f_inst fr) (4 + (gmp+8))%N). {
    eapply Rcons_l with (wal:=(Val_ptr gmp)) (gmp:=(gmp+16)%N); try lia; eauto.
    unfold wasm_value_to_i32, wasm_value_to_u32; replace (4 + (gmp + 8))%N with (gmp +12)%N;[auto|lia].
    eapply Rprim_v with (gmp:=(gmp + 16)%N); try lia; eauto.
    now constructor. }

  assert (HvalC0: repr_val_LambdaANF_Wasm cenv fenv nenv penv (Vconstr c0_tag [Vprim (AstCommon.primInt ; (n1 - n2)%uint63)]) sr_C0 (f_inst fr) (Val_ptr (gmp + 8)%N)). {
      eapply Rconstr_boxed_v with (v:=Int32.repr (Z.of_N C0_ord)) (t:=c0_tag) (sr:=sr_C0) (m:=m_C0) (gmp:=(gmp+16)%N) (addr:=(gmp + 8)%N) (arity:=1) (ord:=C0_ord); auto; try lia.
      - now rewrite /get_ctor_ord Hc0.
      - now rewrite /get_ctor_arity Hc0.
      - now exists (n+4)%N. }

  have HcarryRedC1 := make_carry_reduce C1_ord state sr1 fr m _ _ HINV1 Hmem1 Hgmp1 HgmpBounds HresVal.
  destruct HcarryRedC1 as [sr_C1 [m_C1 [Hmake_carry_red_C1 [HINV_C1 [Hmem_C1 [Hgmp_C1 [HloadRes_C1 [ HloadOrd_C1 [HloadArg_C1 [Hpres64_C1 [Hpres32_C1 [Hsfs_C1 Hmemlength_C1]]]]]]]]]]]].

  assert (HnewgmpBoundsC1: (Z.of_N (gmp + 16) + 8 <= Z.of_N (mem_length m_C1) < Int32.modulus)%Z) by lia.

  assert (HconstrArgsC1: repr_val_constr_args_LambdaANF_Wasm cenv fenv nenv penv [:: Vprim (AstCommon.primInt; (n1 - n2)%uint63)] sr_C1  (f_inst fr) (4 + (gmp+8))%N). {
    eapply Rcons_l with (wal:=(Val_ptr gmp)) (gmp:=(gmp+16)%N); try lia; eauto.
    now replace (4 + (gmp + 8))%N with (gmp + 12)%N by lia.
    eapply Rprim_v with (gmp:=(gmp + 16)%N); eauto; try lia.
    now constructor. }

  assert (HvalC1: repr_val_LambdaANF_Wasm cenv fenv nenv penv (Vconstr c1_tag [Vprim (AstCommon.primInt ; (n1 - n2)%uint63)]) sr_C1 (f_inst fr) (Val_ptr (gmp + 8)%N)). {
    eapply Rconstr_boxed_v with (v:=Int32.repr (Z.of_N C1_ord)) (t:=c1_tag) (sr:=sr_C1) (m:=m_C1) (gmp:=(gmp+16)%N) (addr:=(gmp + 8)%N) (arity:=1) (ord:=C1_ord); auto; try lia.
    - unfold get_ctor_ord. now rewrite Hc1.
    - unfold get_ctor_arity. now rewrite Hc1.
    - now exists (n+4)%N. }

  unfold LambdaANF_primInt_carry_fun in Hv.
  destruct (Z_le_dec (to_Z n2) (to_Z n1)) as [Hlt | Hlt].
  { (* There is no underflow <-> y <= x *)
    rewrite subc_def_spec in Hv. unfold subc_def in Hv.
    replace (n2 <=? n1)%uint63 with true in Hv by lia.
    exists sr_C0, m_C0.
    split. {
      intros; unfold apply_sub_carry_operation.
      remember (make_carry glob_mem_ptr C1_ord glob_tmp1) as carryInstrsC1.
      remember (make_carry glob_mem_ptr C0_ord glob_tmp1) as carryInstrsC0.
      separate_instr.
      dostep_nary 0. eapply r_local_get...
      dostep_nary 1. eapply r_load_success...
      rewrite Hdesx.
      dostep_nary_eliml 0 1. eapply r_local_get...
      dostep_nary_eliml 1 1. eapply r_load_success...
      rewrite Hdesy.
      dostep_nary 2. constructor; apply rs_binop_success=>//.
      dostep_nary 2. constructor; apply rs_binop_success=>//.
      rewrite ->uint63_sub_i64_sub.
      dostep_nary 1. eapply r_global_set'...
      dostep_nary 0. eapply r_local_get...
      dostep_nary 1. eapply r_load_success...
      rewrite Hdesy.
      dostep_nary_eliml 0 1. eapply r_local_get...
      dostep_nary_eliml 1 1. eapply r_load_success...
      rewrite Hdesx.
      dostep_nary 2. constructor; apply rs_relop=>//.
      dostep_nary 1. constructor. apply rs_if_true. rewrite uint63_le_int64_le; auto. discriminate.
      dostep_nary 0. eapply r_block with (t1s:=[::]) (t2s:=[:: T_num T_i32])(vs:=[::]); auto.
      reduce_under_label. subst carryInstrsC0; apply Hmake_carry_red_C0.
      dostep_nary 0. constructor; apply rs_label_const; auto.
      now apply rt_refl. }
    repeat (split; first congruence).
    intros. eapply val_relation_depends_on_mem_smaller_than_gmp_and_funcs with (sr:=sr) (m:=m) (gmp:=gmp) (gmp':=(gmp + 16)%N);
      eauto; try lia.
    now rewrite Hsfs1. }
  { (* There is underflow <-> x < y *)
    rewrite subc_def_spec in Hv. unfold subc_def in Hv.
    replace (n2 <=? n1)%uint63 with false in Hv by now apply to_Z_nle_uint63_leb_false in Hlt.
    exists sr_C1, m_C1.
    split. {
      intros. unfold apply_sub_carry_operation.
      remember (make_carry glob_mem_ptr C1_ord glob_tmp1) as carryInstrsC1.
      remember (make_carry glob_mem_ptr C0_ord glob_tmp1) as carryInstrsC0.
      separate_instr.
      dostep_nary 0. eapply r_local_get...
      dostep_nary 1. eapply r_load_success...
      rewrite Hdesx.
      dostep_nary_eliml 0 1. eapply r_local_get...
      dostep_nary_eliml 1 1. eapply r_load_success...
      rewrite Hdesy.
      dostep_nary 2. constructor; apply rs_binop_success=>//.
      dostep_nary 2. constructor; apply rs_binop_success=>//.
      rewrite ->uint63_sub_i64_sub.
      dostep_nary 1. eapply r_global_set'...
      dostep_nary 0. eapply r_local_get...
      dostep_nary 1. eapply r_load_success...
      rewrite Hdesy.
      dostep_nary_eliml 0 1. eapply r_local_get...
      dostep_nary_eliml 1 1. eapply r_load_success...
      rewrite Hdesx.
      dostep_nary 2. constructor; apply rs_relop=>//.
      dostep_nary 1. constructor. apply rs_if_false. rewrite uint63_nle_int64_nle; auto.
      dostep_nary 0. eapply r_block with (t1s:=[::]) (t2s:=[:: T_num T_i32])(vs:=[::]); auto.
      reduce_under_label. subst carryInstrsC1; apply Hmake_carry_red_C1.
      dostep_nary 0. constructor; apply rs_label_const; auto.
      now apply rt_refl. }
    repeat (split; first congruence).
    intros. eapply val_relation_depends_on_mem_smaller_than_gmp_and_funcs with (sr:=sr) (m:=m) (gmp:=gmp) (gmp':=(gmp + 16)%N);
      eauto; try lia.
    now rewrite Hsfs1. }
Qed.

Lemma subcarryc_reduce (x y : localidx) :
  forall state sr fr m gmp addrx addry bsx bsy n1 n2 c0_tag c1_tag it_carry v,
    INV fenv nenv sr fr ->
    M.get c0_tag cenv = Some (Build_ctor_ty_info (Common.BasicAst.nNamed "C0") (Common.BasicAst.nNamed "carry") it_carry 1%N C0_ord) ->
    M.get c1_tag cenv = Some (Build_ctor_ty_info (Common.BasicAst.nNamed "C1") (Common.BasicAst.nNamed "carry") it_carry 1%N C1_ord) ->
    LambdaANF_primInt_carry_fun c0_tag c1_tag subcarryc n1 n2 = v ->
    smem sr (f_inst fr) = Some m ->
    local_holds_address_to_i64 sr fr x addrx (Int64.repr (to_Z n1)) m bsx ->
    local_holds_address_to_i64 sr fr y addry (Int64.repr (to_Z n2)) m bsy ->
    (Z.of_N gmp + Z.of_N 52 <= Z.of_N (mem_length m) < Int32.modulus)%Z ->
    sglob_val sr (f_inst fr) glob_mem_ptr = Some (VAL_num (VAL_int32 (N_to_i32 gmp))) ->
    exists (sr': store_record) m',
      (forall instrs,
          reduce_trans
            (state, sr, fr, map AI_basic (apply_sub_carry_operation glob_mem_ptr glob_tmp1 x y true) ++ instrs)
            (state, sr', fr, ($VN (VAL_int32 (N_to_i32 (gmp + 8)%N))) :: instrs))
      /\ INV fenv nenv sr' fr
      /\ smem sr' (f_inst fr) = Some m'
      /\ sglob_val sr' (f_inst fr) glob_mem_ptr = Some (VAL_num (VAL_int32 (N_to_i32 (gmp + 16))))
      /\ s_funcs sr = s_funcs sr'
      /\ mem_length m = mem_length m'
      /\ repr_val_LambdaANF_Wasm cenv fenv nenv penv v sr' (f_inst fr) (Val_ptr (gmp + 8)%N)
      /\ (forall (wal : wasm_value) (val : cps.val),
             repr_val_LambdaANF_Wasm cenv fenv nenv penv val sr (f_inst fr) wal ->
             repr_val_LambdaANF_Wasm cenv fenv nenv penv val sr' (f_inst fr) wal).
Proof with eassumption.
  intros ??????????????? HINV Hc0 Hc1 Hv Hmem [Hxinframe  [Hloadx Hdesx]] [Hyinframe [Hloady Hdesy]] HgmpBounds Hgmp.
  have I := HINV. destruct I as [_ [_ [_ [_ [_ [_ [_ [_ [_ [_ [HnoGlobDups [_ [_ [Hmult2 [_ Hi64tempsW]]]]]]]]]]]]]]].
  assert (Hglob_tmp1: i64_glob glob_tmp1) by now constructor.
  destruct (Hi64tempsW _ Hglob_tmp1 (VAL_int64 (Int64.repr (to_Z (n1 - n2 - 1)%uint63)))) as [sr1 Hsr1].
  assert (HINV1 : INV fenv nenv sr1 fr). {
    apply update_global_preserves_INV with (sr:=sr) (i:=glob_tmp1) (m:=m) (num:=(VAL_int64 (Int64.repr (to_Z (n1 - n2 - 1)%uint63))))=>/=//. tauto. }
  assert (Hsfs1 : s_funcs sr = s_funcs sr1)
      by now eapply update_global_preserves_funcs.
  assert (Hmem1 : smem sr1 (f_inst fr) = Some m)
      by now apply update_global_preserves_memory in Hsr1.
  assert (Hgmp1 : sglob_val sr1 (f_inst fr) glob_mem_ptr = Some (VAL_num (VAL_int32 (N_to_i32 gmp))))
      by now apply update_global_get_other with (j:=glob_tmp1) (sr:=sr) (num:=(VAL_int64 (Int64.repr (to_Z (n1 - n2 - 1)%uint63)))).
  assert (HresVal : sglob_val sr1 (f_inst fr) glob_tmp1 = Some (VAL_num (VAL_int64 (Int64.repr (to_Z (n1 - n2 - 1)%uint63)))))
      by now apply update_global_get_same with (sr:=sr).

  assert (-1 < Z.of_N gmp < Int32.modulus)%Z by lia.

  destruct (Hmult2 _ _ Hmem Hgmp H) as [n Hgmpmult2]; clear H.

  have HcarryRedC0 := make_carry_reduce C0_ord state sr1 fr m _ _ HINV1 Hmem1 Hgmp1 HgmpBounds HresVal.
  destruct HcarryRedC0 as [sr_C0 [m_C0 [Hmake_carry_red_C0 [HINV_C0 [Hmem_C0 [Hgmp_C0 [HloadRes_C0 [ HloadOrd_C0 [HloadArg_C0 [Hpres64_C0 [Hpres32_C0 [Hsfs_C0 Hmemlength_C0]]]]]]]]]]]].

  assert (HnewgmpBoundsC0: (Z.of_N (gmp + 16) + 8 <= Z.of_N (mem_length m_C0) < Int32.modulus)%Z) by lia.

  assert (HconstrArgsC0: repr_val_constr_args_LambdaANF_Wasm cenv fenv nenv penv [:: Vprim (AstCommon.primInt; (n1 - n2 - 1)%uint63)] sr_C0 (f_inst fr) (4 + (gmp+8))%N). {
    eapply Rcons_l with (wal:=(Val_ptr gmp)) (gmp:=(gmp+16)%N); try lia; eauto.
    now replace (4 + (gmp + 8))%N with (gmp +12)%N by lia.
    eapply Rprim_v with (gmp:=(gmp + 16)%N); try lia; eauto.
    now constructor. }

  assert (HvalC0: repr_val_LambdaANF_Wasm cenv fenv nenv penv (Vconstr c0_tag [Vprim (AstCommon.primInt ; (n1 - n2 - 1)%uint63)]) sr_C0 (f_inst fr) (Val_ptr (gmp + 8)%N)). {
    eapply Rconstr_boxed_v with (v:=Int32.repr (Z.of_N C0_ord)) (t:=c0_tag) (sr:=sr_C0) (m:=m_C0) (gmp:=(gmp+16)%N) (addr:=(gmp + 8)%N) (arity:=1) (ord:=C0_ord); auto; try lia.
    - unfold get_ctor_ord; now rewrite Hc0.
    - unfold get_ctor_arity; now rewrite Hc0.
    - now exists (n+4)%N.  }

  have HcarryRedC1 := make_carry_reduce C1_ord state sr1 fr m _ _ HINV1 Hmem1 Hgmp1 HgmpBounds HresVal.
  destruct HcarryRedC1 as [sr_C1 [m_C1 [Hmake_carry_red_C1 [HINV_C1 [Hmem_C1 [Hgmp_C1 [HloadRes_C1 [ HloadOrd_C1 [HloadArg_C1 [Hpres64_C1 [Hpres32_C1 [Hsfs_C1 Hmemlength_C1]]]]]]]]]]]].

  assert (HnewgmpBoundsC1: (Z.of_N (gmp + 16) + 8 <= Z.of_N (mem_length m_C1) < Int32.modulus)%Z) by lia.

  assert (HconstrArgsC1: repr_val_constr_args_LambdaANF_Wasm cenv fenv nenv penv [:: Vprim (AstCommon.primInt; (n1 - n2 - 1)%uint63)] sr_C1  (f_inst fr) (4 + (gmp+8))%N). {
    eapply Rcons_l with (wal:=(Val_ptr gmp)) (gmp:=(gmp+16)%N); try lia; eauto.
    now replace (4 + (gmp + 8))%N with (gmp + 12)%N by lia.
    eapply Rprim_v with (gmp:=(gmp + 16)%N); try lia; eauto.
    now constructor. }

  assert (HvalC1: repr_val_LambdaANF_Wasm cenv fenv nenv penv (Vconstr c1_tag [Vprim (AstCommon.primInt ; (n1 - n2 - 1)%uint63)]) sr_C1 (f_inst fr) (Val_ptr (gmp + 8)%N)). {
    eapply Rconstr_boxed_v with (v:=Int32.repr (Z.of_N C1_ord)) (t:=c1_tag) (sr:=sr_C1) (m:=m_C1) (gmp:=(gmp+16)%N) (addr:=(gmp + 8)%N) (arity:=1) (ord:=C1_ord); auto; try lia.
    - unfold get_ctor_ord; now rewrite Hc1.
    - unfold get_ctor_arity; now rewrite Hc1.
    - now exists (n+4)%N.  }

  unfold LambdaANF_primInt_carry_fun in Hv.
  destruct (Z_lt_dec (to_Z n2) (to_Z n1)) as [Hlt | Hlt].
  { (* There is no underflow <-> y < x *)
    rewrite subcarryc_def_spec in Hv. unfold subcarryc_def, subcarry in Hv.
    replace (n2 <? n1)%uint63 with true in Hv by lia.
    exists sr_C0, m_C0.
    split. {
      intros. unfold apply_sub_carry_operation.
      remember (make_carry glob_mem_ptr C1_ord glob_tmp1) as carryInstrsC1.
      remember (make_carry glob_mem_ptr C0_ord glob_tmp1) as carryInstrsC0.
      separate_instr.
      dostep_nary 0. eapply r_local_get...
      dostep_nary 1. eapply r_load_success...
      rewrite Hdesx.
      dostep_nary_eliml 0 1. eapply r_local_get...
      dostep_nary_eliml 1 1. eapply r_load_success...
      rewrite Hdesy.
      dostep_nary 2. constructor; apply rs_binop_success=>//.
      dostep_nary 2. constructor; apply rs_binop_success=>//.
      dostep_nary 2. constructor; apply rs_binop_success=>//.
      replace 1%Z with (to_Z 1) by now cbn. rewrite ->uint63_sub_i64_sub'.
      dostep_nary 1. eapply r_global_set'...
      dostep_nary 0. eapply r_local_get...
      dostep_nary 1. eapply r_load_success...
      rewrite Hdesy.
      dostep_nary_eliml 0 1. eapply r_local_get...
      dostep_nary_eliml 1 1. eapply r_load_success...
      rewrite Hdesx.
      dostep_nary 2. constructor; apply rs_relop=>//.
      dostep_nary 1. constructor. apply rs_if_true. rewrite uint63_lt_int64_lt=>//.
      dostep_nary 0. eapply r_block with (t1s:=[::]) (t2s:=[:: T_num T_i32])(vs:=[::]); auto.
      reduce_under_label. subst carryInstrsC0; apply Hmake_carry_red_C0.
      dostep_nary 0. constructor; apply rs_label_const; auto.
      now apply rt_refl. }
    repeat (split; first congruence).
    intros. eapply val_relation_depends_on_mem_smaller_than_gmp_and_funcs with (sr:=sr) (m:=m) (gmp:=gmp) (gmp':=(gmp + 16)%N);
     eauto; try lia.
     now rewrite Hsfs1. }
  { (* There is underflow <-> x <= y *)
    rewrite subcarryc_def_spec in Hv. unfold subcarryc_def, subcarry in Hv.
    replace (n2 <? n1)%uint63 with false in Hv by lia.
    exists sr_C1, m_C1.
    split. {
      intros. unfold apply_sub_carry_operation.
      remember (make_carry glob_mem_ptr C1_ord glob_tmp1) as carryInstrsC1.
      remember (make_carry glob_mem_ptr C0_ord glob_tmp1) as carryInstrsC0.
      separate_instr.
      dostep_nary 0. eapply r_local_get...
      dostep_nary 1. eapply r_load_success...
      rewrite Hdesx.
      dostep_nary_eliml 0 1. eapply r_local_get...
      dostep_nary_eliml 1 1. eapply r_load_success...
      rewrite Hdesy.
      dostep_nary 2. constructor; apply rs_binop_success=>//.
      dostep_nary 2. constructor; apply rs_binop_success=>//.
      dostep_nary 2. constructor; apply rs_binop_success=>//.
      replace 1%Z with (to_Z 1) by now cbn. rewrite ->uint63_sub_i64_sub'.
      dostep_nary 1. eapply r_global_set'...
      dostep_nary 0. eapply r_local_get...
      dostep_nary 1. eapply r_load_success...
      rewrite Hdesy.
      dostep_nary_eliml 0 1. eapply r_local_get...
      dostep_nary_eliml 1 1. eapply r_load_success...
      rewrite Hdesx.
      dostep_nary 2. constructor; apply rs_relop=>//.
      dostep_nary 1. constructor. apply rs_if_false. rewrite uint63_nlt_int64_nlt; auto.
      dostep_nary 0. eapply r_block with (t1s:=[::]) (t2s:=[:: T_num T_i32])(vs:=[::]); auto.
      reduce_under_label. subst carryInstrsC1; apply Hmake_carry_red_C1.
      dostep_nary 0. constructor; apply rs_label_const; auto.
      now apply rt_refl. }
    repeat (split; first congruence).
    intros.
    eapply val_relation_depends_on_mem_smaller_than_gmp_and_funcs with (sr:=sr) (m:=m) (gmp:=gmp) (gmp':=(gmp + 16)%N);
      eauto; try lia.
    now rewrite Hsfs1. }
Qed.

Lemma make_product_reduce (gidx1 gidx2 : globalidx) :
  forall state sr fr m gmp p1 p2,
    i64_glob gidx1 ->
    i64_glob gidx2 ->
    INV fenv nenv sr fr ->
    smem sr (f_inst fr) = Some m ->
    sglob_val sr (f_inst fr) glob_mem_ptr = Some (VAL_num (VAL_int32 (N_to_i32 gmp))) ->
    (Z.of_N gmp + Z.of_N 52 <= Z.of_N (mem_length m) < Int32.modulus)%Z ->
    sglob_val sr (f_inst fr) gidx1 = Some (VAL_num (VAL_int64 (Int64.repr p1))) ->
    sglob_val sr (f_inst fr) gidx2 = Some (VAL_num (VAL_int64 (Int64.repr p2))) ->
    exists (sr': store_record) m',
      reduce_trans
        (state, sr, fr, map AI_basic (make_product glob_mem_ptr gidx1 gidx2))
        (state, sr', fr, [$VN (VAL_int32 (N_to_i32 (gmp + 16)%N))])
      /\ INV fenv nenv sr' fr
      /\ smem sr' (f_inst fr) = Some m'
      /\ sglob_val sr' (f_inst fr) glob_mem_ptr = Some (VAL_num (VAL_int32 (N_to_i32 (gmp + 28))))
      /\ load_i64 m' gmp = Some (VAL_int64 (Int64.repr p1))
      /\ load_i64 m' (gmp + 8) = Some (VAL_int64 (Int64.repr p2))
      /\ load_i32 m' (gmp + 16)%N = Some (VAL_int32 (N_to_i32 pair_ord))
      /\ load_i32 m' (gmp + 20)%N = Some (VAL_int32 (N_to_i32 gmp))
      /\ load_i32 m' (gmp + 24)%N = Some (VAL_int32 (N_to_i32 (gmp + 8)))
      /\ (forall a, (a + 4 <= gmp)%N -> load_i32 m a = load_i32 m' a)
      /\ (forall a, (a + 8 <= gmp)%N -> load_i64 m a = load_i64 m' a)
      /\ s_funcs sr = s_funcs sr'
      /\ mem_length m = mem_length m'.
Proof with eassumption.
  intros ??????? Hgidx1 Hgidx2 HINV Hmem Hgmp HenoughMem Hp1 Hp2.
  assert (0 + 8 <= page_size)%N as Hoff1 by now unfold page_size.
  assert (8 + 8 <= page_size)%N as Hoff2 by now unfold page_size.
  assert (16 + 8 <= page_size)%N as Hoff3 by now unfold page_size.
  assert (20 + 8 <= page_size)%N as Hoff4 by now unfold page_size.
  assert (24 + 8 <= page_size)%N as Hoff5 by now unfold page_size.
  assert (Hdesp1: wasm_deserialise (serialise_num (VAL_int64 (Int64.repr p1))) T_i64 = VAL_int64 (Int64.repr p1))
      by now apply deserialise_serialise.
  assert (Hdesp2: wasm_deserialise (serialise_num (VAL_int64 (Int64.repr p2))) T_i64 = VAL_int64 (Int64.repr p2))
      by now apply deserialise_serialise.
  assert (Hdesp1Addr: wasm_deserialise (serialise_num (VAL_int32 (N_to_i32 gmp))) T_i32 = VAL_int32 (N_to_i32 gmp))
      by now apply deserialise_serialise.
  assert (Hdesp2Addr: wasm_deserialise (serialise_num (VAL_int32 (N_to_i32 (gmp + 8)))) T_i32 = VAL_int32 (N_to_i32 (gmp + 8)))
      by now apply deserialise_serialise.
  assert (HdesOrd: wasm_deserialise (serialise_num (VAL_int32 (N_to_i32 pair_ord))) T_i32 = VAL_int32 (N_to_i32 pair_ord))
      by now apply deserialise_serialise.
  (* Store p1 at gmp *)
  destruct (store_preserves_INV sr fr m gmp 0%N (VAL_int64 (Int64.repr p1)) HINV Hmem Hoff1 HenoughMem)
        as [sr1 [m1 [Hmem1 [Hmemlength1 [Hstore1 [Hsmem_store1 [HINV1 [Hpres32_1 [Hpres64_1 [Hsfs1 [HglobPres1 HenoughMem1]]]]]]]]]]].
  (* Store p2 at gmp+8 *)
  destruct (store_preserves_INV sr1 fr m1 gmp 8%N (VAL_int64 (Int64.repr p2)) HINV1 Hmem1 Hoff2 HenoughMem1)
        as [sr2 [m2 [Hmem2 [Hmemlength2 [Hstore2 [Hsmem_store2 [HINV2 [Hpres32_2 [Hpres64_2 [Hsfs2 [HglobPres2 HenoughMem2]]]]]]]]]]].
  (* Store the ordinal at gmp+16 *)
  destruct (store_preserves_INV sr2 fr m2 gmp 16%N (VAL_int32 (N_to_i32 pair_ord)) HINV2 Hmem2 Hoff3 HenoughMem2)
         as [sr3 [m3 [Hmem3 [Hmemlength3 [Hstore3 [Hsmem_store3 [HINV3 [Hpres32_3 [Hpres64_3 [Hsfs3 [HglobPres3 HenoughMem3]]]]]]]]]]].
  (* Store gmp at gmp+20 *)
  destruct (store_preserves_INV sr3 fr m3 gmp 20%N (VAL_int32 (N_to_i32 gmp)) HINV3 Hmem3 Hoff4 HenoughMem3)
        as [sr4 [m4 [Hmem4 [Hmemlength4 [Hstore4 [Hsmem_store4 [HINV4 [Hpres32_4 [Hpres64_4 [Hsfs_4 [HglobPres4 HenoughMem4]]]]]]]]]]].
  (* Store gmp at gmp+20 *)
  destruct (store_preserves_INV sr4 fr m4 gmp 24%N (VAL_int32 (N_to_i32 (gmp+8))) HINV4 Hmem4 Hoff5 HenoughMem4)
        as [sr5 [m5 [Hmem5 [Hmemlength5 [Hstore5 [Hsmem_store5 [HINV5 [Hpres32_5 [Hpres64_5 [Hsfs_5 [HglobPres5 _]]]]]]]]]]].

  have I := HINV5. destruct I as [_ [_ [_ [HgmpWritable _]]]].
  have I := HINV. destruct I as [_ [_ [_ [_ [_ [_ [_ [_ [_ [_ [_ [_ [_ [Hmult2 _]]]]]]]]]]]]]].

  (* Increment gmp by 16 to point to next free address *)
  destruct (HgmpWritable (VAL_int32 (N_to_i32 (gmp + 28)))) as [sr'  Hupdgmp].
  assert (HINV' : INV fenv nenv sr' fr). {
    apply update_global_preserves_INV with (sr:=sr5) (i:=glob_mem_ptr) (m:=m5) (num:=(VAL_int32 (N_to_i32 (gmp+28))))=>//. cbn; tauto.
    move => _ n [Heqn Hrangen].
    replace n with (gmp + 28)%N by (inv Heqn; simpl_eq; lia). lia.
    move => _ n [Heqn Hrangen].
    replace n with (gmp + 28)%N by (inv Heqn; simpl_eq; lia).
    assert (-1 < Z.of_N gmp < Wasm_int.Int32.modulus)%Z by lia.
    destruct (Hmult2 _ _ Hmem Hgmp H) as (n0 & Hn0).
    now exists (n0 + 14)%N. }
  assert (Hgmp' : sglob_val sr' (f_inst fr) glob_mem_ptr = Some (VAL_num (VAL_int32 (N_to_i32 (gmp + 28)))))
      by now apply HglobPres1, HglobPres2, HglobPres3, HglobPres4, HglobPres5 in Hgmp;
         apply update_global_get_same with (sr:=sr5).
  (* All i32 values below gmp are preserved *)
  assert (Hpres32: forall a, (a + 4 <= gmp)%N -> load_i32 m a = load_i32 m5 a)
      by now intros; rewrite ->Hpres32_1, ->Hpres32_2, ->Hpres32_3, ->Hpres32_4, ->Hpres32_5; try lia.
  (* All i64 values below gmp are preserved *)
  assert (Hpres64: forall a, (a + 8 <= gmp)%N -> load_i64 m a = load_i64 m5 a)
      by now intros; rewrite ->Hpres64_1, ->Hpres64_2, -> Hpres64_3, ->Hpres64_4, ->Hpres64_5; try lia.
  exists sr', m5.
  split. { (* make_product instructions reduce *)
    intros.
    assert (HrewriteGmp : N_of_uint i32m (N_to_i32 gmp) = gmp) by now cbn;
      rewrite Int32.Z_mod_modulus_id;[now rewrite N2Z.id|lia].
    unfold make_product.
    separate_instr.
    dostep_nary 0. apply r_global_get...
    dostep_nary_eliml 0 1. apply r_global_get...
    dostep_nary 2.
    apply r_store_success; rewrite HrewriteGmp...
    dostep_nary 0. apply r_global_get; apply HglobPres1 in Hgmp...
    dostep_nary_eliml 0 1. apply r_global_get. apply HglobPres1 in Hp2...
    dostep_nary 2.
    apply r_store_success; rewrite HrewriteGmp...
    dostep_nary 0. apply r_global_get. apply HglobPres1, HglobPres2 in Hgmp...
    dostep_nary 2.
    apply r_store_success; rewrite HrewriteGmp...
    dostep_nary 0. apply r_global_get. apply HglobPres1, HglobPres2, HglobPres3 in Hgmp...
    dostep_nary_eliml 0 1. apply r_global_get. apply HglobPres1, HglobPres2, HglobPres3 in Hgmp...
    dostep_nary 2. apply r_store_success; rewrite HrewriteGmp...
    dostep_nary 0. apply r_global_get. apply HglobPres1, HglobPres2, HglobPres3, HglobPres4 in Hgmp...
    dostep_nary_eliml 0 1. apply HglobPres1, HglobPres2, HglobPres3, HglobPres4 in Hgmp. apply r_global_get...
    dostep_nary_eliml 2 1. constructor. apply rs_binop_success; first done.
    cbn; unfold Int32.iadd, Int32.add, Int32.unsigned; cbn.
    rewrite Int32.Z_mod_modulus_id; last lia.
    replace 8%Z with (Z.of_N 8) by now cbn. rewrite -N2Z.inj_add. reflexivity.
    dostep_nary 2. apply r_store_success; rewrite HrewriteGmp...
    dostep_nary 0. apply r_global_get. apply HglobPres1, HglobPres2, HglobPres3, HglobPres4, HglobPres5 in Hgmp...
    dostep_nary 2. constructor. apply rs_binop_success; first done.
    cbn. unfold Int32.iadd, Int32.add, Int32.unsigned; cbn.
    rewrite Int32.Z_mod_modulus_id; last lia.
    replace 16%Z with (Z.of_N 16) by now cbn. rewrite <-N2Z.inj_add. reflexivity.
    dostep_nary_eliml 0 1. apply r_global_get. apply HglobPres1, HglobPres2, HglobPres3, HglobPres4, HglobPres5 in Hgmp...
    dostep_nary_eliml 2 1. constructor. apply rs_binop_success; first done.
    cbn. unfold Int32.iadd, Int32.add, Int32.unsigned; cbn.
    rewrite Int32.Z_mod_modulus_id; last lia.
    replace 28%Z with (Z.of_N 28) by now cbn. rewrite <-N2Z.inj_add. reflexivity.
    dostep_nary_eliml 1 1. apply r_global_set'...
    now apply rt_refl. }
  replace (smem sr' (f_inst fr)) with (smem sr5 (f_inst fr))
       by now eapply update_global_preserves_memory; eassumption.
  repeat (split; auto).
  - (* Load p1 *)
    rewrite <-Hpres64_5, <-Hpres64_4, <-Hpres64_3, <-Hpres64_2, <-Hdesp1; try lia.
    eapply store_load_i64 with (m:=m); auto.
  - (* Load p2 *)
    rewrite <-Hpres64_5, <-Hpres64_4, <-Hpres64_3, <-Hdesp2; try lia.
    eapply store_load_i64 with (m:=m1); rewrite store_offset_eq in Hstore2; auto.
  - (* The ordinal can be loaded as an i32 from address gmp + 16 *)
    rewrite <-Hpres32_5, <-Hpres32_4, <-HdesOrd; try lia.
    eapply store_load_i32 with (m:=m2); rewrite store_offset_eq in Hstore3; auto.
  - (* The address of the result (gmp) can be loaded from address gmp + 20 *)
    rewrite <-Hpres32_5, <-Hdesp1Addr; try lia.
    apply store_load_i32 with (m:=m3); rewrite store_offset_eq in Hstore4; eauto.
  - (* The address of the result (gmp) can be loaded from address gmp + 20 *)
    rewrite <-Hdesp2Addr; try lia.
    apply store_load_i32 with (m:=m4); rewrite store_offset_eq in Hstore5; eauto.
  - (* Functions in the store are preserved*)
    rewrite Hsfs1 Hsfs2 Hsfs3 Hsfs_4 Hsfs_5; eapply update_global_preserves_funcs; eassumption.
  - (* Length of memory is preserved *)
    congruence.
Qed.

Ltac dep_destruct_primint v p x :=
  try dependent destruction v; try discriminate;
  dependent destruction p; dependent destruction x; try discriminate.

(* Arguments to primitive operations can only be primInts
   (Eventually adapt for floats) *)
Lemma apply_primop_only_defined_on_primInts :
  forall op vs v true_tag false_tag eq_tag lt_tag gt_tag c0_tag c1_tag pair_tag,
    apply_LambdaANF_primInt_operator true_tag false_tag eq_tag lt_tag gt_tag c0_tag c1_tag pair_tag op vs = Some v ->
    forall v',
      List.In v' vs -> exists n, v' = Vprim (primInt n).
Proof.
  intros.
  unfold apply_LambdaANF_primInt_operator in H.
  destruct vs=>//. destruct vs, v0=>//; destruct p =>//; destruct x =>//.
  destruct H0=>//. now exists p.
  destruct vs, v1=>//; destruct p0 =>//; destruct x =>//.
  destruct H0. now exists p. destruct H0. now exists p0. destruct H0.
  destruct vs, v0=>//; destruct p1 =>//; destruct x =>//.
  destruct H0. now exists p. destruct H0. now exists p0. destruct H0=>//. now exists p1.
Qed.

(* Well-formedness of the primitive function (and constructor) environment:
   Applying a (supported) primitive operator evaluates to a (LambdaANF) value,
   and the constructor environment contains all constructors that may be returned,
   and the constructors have the expected ordinals (i.e. the ones used in the translation section).
 *)
Definition prim_funs_env_wellformed (cenv : ctor_env) (penv : prim_env) (prim_funs : M.t (list cps.val -> option cps.val)) : Prop :=
  forall p op_name s b n op f vs v,
    M.get p penv = Some (op_name, s, b, n) ->       (* penv = primitive function environment obtained from previous pipeline stage *)
    KernameMap.find op_name primop_map = Some op -> (* primop_map = environment of supported primitive operations *)
    M.get p prim_funs = Some f ->                   (* from lambdaANF operational semantics *)
    f vs = Some v ->
    exists true_tag false_tag it_bool eq_tag lt_tag gt_tag it_comparison c0_tag c1_tag it_carry pair_tag it_prod,
      (* This links operational semantics to primitive operators in penv *)
      apply_LambdaANF_primInt_operator true_tag false_tag eq_tag lt_tag gt_tag c0_tag c1_tag pair_tag op vs = Some v
      (* Constructor tags (bools, comparison, carry and prod) used by prim ops *)
      /\ M.get true_tag cenv = Some (Build_ctor_ty_info (Common.BasicAst.nNamed "true") (Common.BasicAst.nNamed "bool") it_bool 0%N true_ord)
      /\ M.get false_tag cenv = Some (Build_ctor_ty_info (Common.BasicAst.nNamed "false") (Common.BasicAst.nNamed "bool") it_bool 0%N false_ord)
      /\ M.get eq_tag cenv = Some (Build_ctor_ty_info (Common.BasicAst.nNamed "Eq") (Common.BasicAst.nNamed "comparison") it_comparison 0%N Eq_ord)
      /\ M.get lt_tag cenv = Some (Build_ctor_ty_info (Common.BasicAst.nNamed "Lt") (Common.BasicAst.nNamed "comparison") it_comparison 0%N Lt_ord)
      /\ M.get gt_tag cenv = Some (Build_ctor_ty_info (Common.BasicAst.nNamed "Gt") (Common.BasicAst.nNamed "comparison") it_comparison 0%N Gt_ord)
      /\ M.get c0_tag cenv = Some (Build_ctor_ty_info (Common.BasicAst.nNamed "C0") (Common.BasicAst.nNamed "carry") it_carry 1%N C0_ord)
      /\ M.get c1_tag cenv = Some (Build_ctor_ty_info (Common.BasicAst.nNamed "C1") (Common.BasicAst.nNamed "carry") it_carry 1%N C1_ord)
      /\ M.get pair_tag cenv = Some (Build_ctor_ty_info (Common.BasicAst.nNamed "pair") (Common.BasicAst.nNamed "prod") it_prod 2%N pair_ord).

(* Application of primitive operators can never evaluate to a function value *)
Lemma primop_value_not_funval :
  forall p pfs f' vs v op op_name str b op_arr,
    prim_funs_env_wellformed cenv penv pfs ->
    M.get p pfs = Some f' ->
    M.get p penv = Some (op_name, str, b, op_arr) ->
    KernameMap.find op_name primop_map = Some op ->
    f' vs = Some v ->
    forall rho fds f0, ~ subval_or_eq (Vfun rho fds f0) v.
Proof.
  intros.
  destruct (H p op_name str b op_arr op f' vs v H1 H2 H0 H3) as
    [true_tag [false_tag [it_bool [eq_tag [lt_tag [gt_tag [it_comparison [c0_tag [c1_tag [it_carry [pair_tag [it_prod [Happ _]]]]]]]]]]]]].
  clear H2.
  assert (H' : forall p', (Vfun rho fds f0) <> Vprim p') by now intros.
  assert (forall tag p', ~ subval_or_eq (Vfun rho fds f0) (Vconstr tag [Vprim p']))
      as HunaryConstr. {
    intros. intro Hcontra.
    destruct (rt_then_t_or_eq _ _ _ _ Hcontra); try discriminate.
    destruct (subval_v_constr _ _ _ H2) as [? [Hsubconst Hin]].
    destruct Hin;[subst x; now destruct (subval_or_eq_fun_not_prim _ p' H')|destruct H4]. }
  assert (HbinaryConstr : forall tag p1 p2, ~ subval_or_eq (Vfun rho fds f0) (Vconstr tag [Vprim p1 ; Vprim p2])). {
    intros. intro Hcontra.
    destruct (rt_then_t_or_eq _ _ _ _ Hcontra)=>//.
    destruct (subval_v_constr _ _ _ H2) as [? [Hsubconst Hin]].
    destruct Hin as [Hx|Hin].
    - destruct (subval_or_eq_fun_not_prim _ p1 H')=>//.
      now subst x.
    - destruct Hin=>//. subst x.
      now destruct (subval_or_eq_fun_not_prim _ p2 H'). }
  destruct vs eqn:Hvs1. now unfold apply_LambdaANF_primInt_operator in Happ.
  destruct l. { (* Unary operators *)
    destruct op; unfold apply_LambdaANF_primInt_operator in Happ;
      dep_destruct_primint v0 p0 x;
      unfold LambdaANF_primInt_unop_fun in Happ;
      inversion Happ;
      now apply subval_or_eq_fun_not_prim. }
  destruct l. { (* Binary operators *)
    destruct op; unfold apply_LambdaANF_primInt_operator in Happ;
      dep_destruct_primint v0 p0 x; dep_destruct_primint v1 p1 x;
      unfold LambdaANF_primInt_arith_fun, LambdaANF_primInt_bool_fun, LambdaANF_primInt_compare_fun,
         LambdaANF_primInt_carry_fun, LambdaANF_primInt_prod_fun in Happ;
      inversion Happ;
      try now apply subval_or_eq_fun_not_prim.
    - destruct (p0 =? p1)%uint63; intro Hcontra;
        destruct (rt_then_t_or_eq _ _ _ _ Hcontra)=>//.
      1,2: now destruct (subval_v_constr _ _ _ H2).
    - destruct (p0 <? p1)%uint63; intro Hcontra;
        destruct (rt_then_t_or_eq _ _ _ _ Hcontra)=>//.
      1,2: now destruct (subval_v_constr _ _ _ H2).
    - destruct (p0 <=? p1)%uint63; intro Hcontra;
        destruct (rt_then_t_or_eq _ _ _ _ Hcontra)=>//.
      1,2: now destruct (subval_v_constr _ _ _ H2).
    - destruct (p0 ?= p1)%uint63; intro Hcontra;
        destruct (rt_then_t_or_eq _ _ _ _ Hcontra)=>//.
      1,2,3: now destruct (subval_v_constr _ _ _ H2).
    - destruct (p0 +c p1)%uint63; eapply HunaryConstr.
    - destruct (addcarryc p0 p1)%uint63; eapply HunaryConstr.
    - destruct (p0 -c p1)%uint63; eapply HunaryConstr.
    - destruct (subcarryc p0 p1)%uint63; eapply HunaryConstr.
    - eapply HbinaryConstr.
    - eapply HbinaryConstr. }
  destruct l. { (* Ternary operators *)
    destruct op; unfold apply_LambdaANF_primInt_operator in Happ;
      dep_destruct_primint v0 p0 x;
      dep_destruct_primint v1 p1 x;
      dep_destruct_primint v2 p2 x;
      unfold LambdaANF_primInt_diveucl_21, LambdaANF_primInt_addmuldiv in Happ;
      inversion Happ.
    - now destruct (p2 <=? p0)%uint63, (diveucl_21 p0 p1 p2).
    - now apply subval_or_eq_fun_not_prim. }
  (* There are no operators with arity > 3 *)
  destruct op; unfold apply_LambdaANF_primInt_operator in Happ;
    dep_destruct_primint v0 p0 x;
    dep_destruct_primint v1 p1 x;
    dep_destruct_primint v2 p2 x.
Qed.


Definition div21_loop_invariant sr fr i xh xl xh' xl' y q :=
  sglob_val sr (f_inst fr) glob_tmp1 = Some (VAL_num (VAL_int64 (Int64.repr xh')))
  /\ sglob_val sr (f_inst fr) glob_tmp2 = Some (VAL_num (VAL_int64 (Int64.repr xl')))
  /\ sglob_val sr (f_inst fr) glob_tmp3 = Some (VAL_num (VAL_int64 (Int64.repr y)))
  /\ sglob_val sr (f_inst fr) glob_tmp4 = Some (VAL_num (VAL_int64 (Int64.repr q)))
  /\ (0 <= y < 2^63)%Z
  /\ (0 <= xh' < y)%Z
  /\ (0 <= q < 2^i)%Z
  /\ (xl' mod 2^64 = (xl * 2^i) mod 2^64)%Z
  /\ ((q * y + xh') * 2^(63 - i) + (xl mod 2^(63 - i)) = (xh mod y) * 2^63 + xl)%Z.

Lemma div21_loop_reduce_stop : forall state sr fr i,
    sglob_val sr (f_inst fr) glob_cap = Some (VAL_num (VAL_int32 (Int32.repr i))) ->
    (-1 < i < Int32.modulus)%Z ->
    ~ (i < 63)%Z ->
    reduce_trans
      (state, sr, fr,
        [ AI_basic (BI_loop (BT_valtype None) (diveucl_21_loop glob_cap glob_tmp1 glob_tmp2 glob_tmp3 glob_tmp4 63%Z))])
      (state, sr, fr, []).
Proof.
  intros state sr fr i Hival Hi Hlt.
  remember (diveucl_21_loop glob_cap glob_tmp1 glob_tmp2 glob_tmp3 glob_tmp4 63%Z) as es.
  apply rt_trans with (y:=(state, sr, fr, [AI_label 0 [:: AI_basic (BI_loop (BT_valtype None) es)] (to_e_list es)])).
  apply rt_step. eapply r_loop with (vs:=[]); cbn; auto.
  remember (LH_rec [] 0 [:: AI_basic (BI_loop (BT_valtype None) es)] (LH_base [] []) [])
        as lh eqn:Hlh.
  assert (Hlfill : lfill lh (to_e_list es) = [:: AI_label 0 [:: AI_basic (BI_loop (BT_valtype None) es)] (to_e_list es)]).
  subst lh. simpl. rewrite cats0. reflexivity.
  apply rt_trans with (y:=(state, sr, fr, [AI_label 0 [:: AI_basic (BI_loop (BT_valtype None) es)] []])).
  rewrite <- Hlfill.
  replace [AI_label 0 [:: AI_basic (BI_loop (BT_valtype None) es)] []]
     with (lfill lh []) by (subst lh; reflexivity).
  apply reduce_trans_label.
  subst es.
  separate_instr.
  dostep_nary' 0. eapply r_global_get; eauto.
  dostep_nary' 2. constructor. apply rs_relop=>//.
  dostep_nary' 1. constructor. apply rs_if_false.
    unfold Int32.ltu. cbn.
    rewrite zlt_false=>//.
    rewrite Int32.Z_mod_modulus_id; lia.
  dostep_nary' 0. eapply r_block with (vs:=[]); cbn; eauto.
  apply rt_step. apply r_simple. now apply rs_label_const.
  apply rt_step. apply r_simple. now apply rs_label_const.
Qed.

Lemma div21_loop_reduce_continue : forall state sr sr' fr m gmp i xh xl xh0' xl0' xh1' xl1' q0 q1 y,
    sglob_val sr (f_inst fr) glob_cap = Some (VAL_num (VAL_int32 (Int32.repr i))) ->
    (0 <= i < 63)%Z ->
    div21_loop_invariant sr fr i xh xl xh0' xl0' y q0 ->
    reduce_trans
      (state, sr, fr, to_e_list (diveucl_21_loop_body glob_tmp1 glob_tmp2 glob_tmp3 glob_tmp4))
      (state, sr', fr, []) ->
    div21_loop_invariant sr' fr (i + 1)%Z xh xl xh1' xl1' y q1 ->
    INV fenv nenv sr' fr ->
    smem sr' (f_inst fr) = Some m ->
    s_funcs sr = s_funcs sr' ->
    sglob_val sr' (f_inst fr) glob_mem_ptr = Some (VAL_num (VAL_int32 (N_to_i32 gmp))) ->
    sglob_val sr' (f_inst fr) glob_cap  = Some (VAL_num (VAL_int32 (Int32.repr i))) ->
    exists sr'',
      reduce_trans
        (state, sr, fr,
          [ AI_basic (BI_loop (BT_valtype None) (diveucl_21_loop glob_cap glob_tmp1 glob_tmp2 glob_tmp3 glob_tmp4 63%Z))])
        (state, sr'', fr,
          [ AI_basic (BI_loop (BT_valtype None) (diveucl_21_loop glob_cap glob_tmp1 glob_tmp2 glob_tmp3 glob_tmp4 63%Z))])
      /\ div21_loop_invariant sr'' fr (i + 1)%Z xh xl xh1' xl1' y q1
      /\ sglob_val sr'' (f_inst fr) glob_cap  = Some (VAL_num (VAL_int32 (Int32.repr (i + 1))))
      /\ INV fenv nenv sr'' fr
      /\ smem sr'' (f_inst fr) = Some m
      /\ s_funcs sr = s_funcs sr''
      /\ sglob_val sr'' (f_inst fr) glob_mem_ptr = Some (VAL_num (VAL_int32 (N_to_i32 gmp))).
Proof.
  intros state sr sr' fr m gmp i xh xl xh0' xl0' xh1' xl1' q0 q1 y.
  intros Hival Hi HLoopINVpre HredBody HLoopINVpost HINV Hmem Hsfs Hgmp Hival'.
  remember (diveucl_21_loop glob_cap glob_tmp1 glob_tmp2 glob_tmp3 glob_tmp4 63%Z) as loop.
  remember (LH_rec [] 0 [:: AI_basic (BI_loop (BT_valtype None) loop)] (LH_base [] []) []) as lh eqn:Hlh.
  assert (Hlfill : lfill lh (to_e_list loop) =
                     [:: AI_label 0 [:: AI_basic (BI_loop (BT_valtype None) loop)] (to_e_list loop)]). {
    subst lh. cbn. rewrite cats0. reflexivity. }
  have I := HINV. destruct I as [_ [_ [_ [_ [Hcap [_ [[Hmem1 [m' [Hmem2 [size [Hmem3 Hmem5 ]]]]] [_ [_ [_ [HnoDups _]]]]]]]]]]].
  destruct (Hcap (VAL_int32 (Int32.repr (i + 1)))) as [sr'' Hupd].
  assert (Hival'' : sglob_val sr'' (f_inst fr) glob_cap = Some (VAL_num (VAL_int32 (Int32.repr (i + 1))))).
  by now eapply update_global_get_same; eauto.
  assert (HINV' : INV fenv nenv sr'' fr).
  eapply update_global_preserves_INV; eauto. cbn; tauto.
  discriminate. now intro. now intro.
  exists sr''.
  split; auto.
  dostep'. eapply r_loop with (t1s:=[::]) (t2s:=[:: ])(vs:=[::]); eauto. simpl.
  rewrite <- Hlfill.
  eapply rt_trans. eapply reduce_trans_label.
  subst loop.
  unfold diveucl_21_loop.
  remember (diveucl_21_loop_body glob_tmp1 glob_tmp2 glob_tmp3 glob_tmp4) as body.
  separate_instr.
  dostep_nary' 0. eapply r_global_get; eauto.
  dostep_nary' 2. constructor. apply rs_relop=>//.
  dostep_nary' 1. constructor. apply rs_if_true.
    unfold Int32.ltu; cbn.
    rewrite zlt_true=>//.
    rewrite Int32.Z_mod_modulus_id; first lia.
    simpl_modulus. cbn. lia.
  dostep_nary' 0.
  eapply r_block with (t1s:=[::]) (t2s:=[::])(vs:=[::]); eauto.
  simpl.
  apply reduce_trans_label0.
  rewrite to_e_list_cat.
  eapply rt_trans. eapply app_trans. apply HredBody.
  dostep_nary' 0. eapply r_global_get; eauto.
  dostep_nary' 2. constructor. apply rs_binop_success; first done.
    cbn; unfold Int32.iadd, Int32.add; cbn.
    rewrite Int32.Z_mod_modulus_id. reflexivity.
    simpl_modulus. cbn. lia.
  dostep_nary' 1. eapply r_global_set'; eassumption.
  apply rt_refl.
  subst lh. simpl.
  apply rt_step. apply r_simple.
  remember (LH_rec [] 0 [] (LH_base [] []) []) as lh'.
  apply rs_br with (vs:=[]) (lh:=lh'); subst lh'; auto.
  split.
  { destruct HLoopINVpost as [Hg1 [Hg2 [Hg3 [Hg4 HLoopINVpost]]]].
    split.
    eapply update_global_get_other; eauto. discriminate.
    split.
    eapply update_global_get_other; eauto. discriminate.
    split.
    eapply update_global_get_other; eauto. discriminate.
    split; auto.
    eapply update_global_get_other; eauto. discriminate. }
  do 3 (split; auto).
  now erewrite <-(update_global_preserves_memory sr' sr'').
  split.
  now erewrite <-(update_global_preserves_funcs sr' sr''); eauto.
  now eapply update_global_get_other; eauto.
Qed.

Ltac Zify.zify_post_hook ::= Z.div_mod_to_equations.

(** Try to clear everything except some hypothesis *)
Ltac clear_except hyp :=
  repeat match goal with [ H : _ |- _ ] =>
           match H with
             | hyp => fail 1
             | _ => clear H
           end
         end.

Ltac clear_all :=
  repeat match goal with [ H : _ |- _ ] => clear H
         end.

(* for trivial facts that don't need any assumptions *)
Ltac liat := clear_all; lia.

Lemma div21_loop_arith_lemma : forall i y xh0' xh1' q0 q1 xl0' xl1' xl xh,
 (0 <= i < 63 ->
  0 <= y < 2 ^ 63 ->
  0 <= xh0' < y ->
  0 <= q0 < 2 ^ i ->
  xl0' mod 2 ^ 64 = (xl * 2 ^ i) mod 2 ^ 64 ->
  (q0 * y + xh0') * 2 ^ (63 - i) + xl mod 2 ^ (63 - i) = xh mod y * 2 ^ 63 + xl ->
  xh1' = xh0' * 2 + xl1' mod 2 ^ 64 / 2 ^ 63 ->
  xl1' = xl0' mod 2 ^ 64 * 2 ->
  q1 = q0 * 2 ->
  (q1 * y + xh1') * 2 ^ (63 - (i + 1)) + xl mod 2 ^ (63 - (i + 1)) = xh mod y * 2 ^ 63 + xl)%Z.
Proof.
  intros ?????????? Hi Hli1 Hli2 Hli3 Hli4 Hli5 Hxh1' Hxl1' Hq1.
  assert ((xl * 2 ^ (i + 1)) mod 2 ^ 64 = ((xl * 2^(i + 1)) mod 2^65) mod 2^64)%Z
      by liat.
  subst q1. subst xh1'.
  replace (q0 * 2 * y + (xh0' * 2 + xl1' mod 2 ^ 64 / 2 ^ 63))%Z
     with (2 * (q0 * y + xh0') + xl1' mod 2 ^ 64 / 2 ^ 63)%Z by liat.
  replace ((2 * (q0 * y + xh0') + xl1' mod 2 ^ 64 / 2 ^ 63) * 2^(63 - (i + 1)))%Z
     with (2 * (q0 * y + xh0') * 2^(63 - (i + 1)) + (xl1' mod 2 ^ 64 / 2 ^ 63) * 2^(63 - (i + 1)))%Z by liat.
    replace (2 * (q0 * y + xh0') * 2^(63 - (i + 1)))%Z with ((q0 * y + xh0') * 2^(63-i))%Z.
    2: { rewrite (Z.mul_comm (2 * _)) Z.mul_assoc.
         replace (2^(63 - (i + 1)) * 2)%Z with (2^1 * 2^(63 - (i + 1)))%Z by liat.
         rewrite <- Z.pow_add_r; clear_except Hi; try lia.
         replace (1 + (63 - (i + 1)))%Z with (63 - i)%Z by lia. lia. }
    subst xl1'.
    rewrite Hli4.
    replace ((xl * 2 ^ i) mod 2 ^ 64 * 2)%Z with ((xl * 2 ^ (i + 1)) mod (2 ^ 65))%Z.
    2: { rewrite <- Z.mul_mod_distr_r; try liat.
         rewrite Z.pow_add_r; try liat. apply Hi. }
    rewrite <-H.
    replace ((xl * 2 ^ (i + 1)) mod 2 ^ 64 / 2 ^ 63)%Z with ((xl mod 2 ^ (63 - i)) / 2 ^ (63 - (i + 1)))%Z.
    2: {
      assert (2^(i + 1) * (xl mod 2^(64 - (i + 1))) = (xl * 2^(i + 1) mod 2^64))%Z. {
        rewrite -Z.mul_mod_distr_l; try (clear_except Hi; lia).
        rewrite Z.mul_comm.
        replace (2 ^ (i + 1) * 2 ^ (64 - (i + 1)))%Z with (2 ^ (i + 1 + (64 - (i + 1))))%Z.
        2: { clear_except Hi. rewrite <-Z.pow_add_r; lia. }
        replace (i + 1 + (64 - (i + 1)))%Z with 64%Z by liat=>//. reflexivity. }

      rewrite -H0. clear H H0.
      replace (64 - (i + 1))%Z with (63 - i)%Z by liat.
      replace (2^63)%Z with (2^(i + 1) * 2^(63 - (i + 1)))%Z.
      2: { rewrite <-Z.pow_add_r; try (clear_except Hi; lia).
           replace (i + 1 + (63 - (i + 1)))%Z with 63%Z by liat. reflexivity. }
      clear_except Hi. rewrite Z.div_mul_cancel_l; lia. }

    have Hxldivmod := Z_div_mod_eq_full (xl mod 2^(63-i))%Z (2^(63 - (i + 1)))%Z.
    assert (xl mod 2^(63 - (i + 1)) = (xl mod 2^(63 - i)) mod 2^(63-(i+1)))%Z. {
      clear_except Hi.
      replace (2 ^ (63 - i))%Z with (2 * 2^(63 - (i + 1)))%Z.
      2: { replace (2 * 2^(63 - (i + 1)))%Z with (2^1 * 2 ^ (63 - (i  + 1)))%Z by lia.
           rewrite <-Z.pow_add_r; try lia.
           replace (1 + (63 - (i + 1)))%Z with (63 - i)%Z by lia. reflexivity. }
      rewrite Zaux.Zmod_mod_mult; lia. }

    rewrite H0.
    replace ((q0 * y + xh0') * 2 ^ (63 - i) + xl mod 2 ^ (63 - i) / 2 ^ (63 - (i + 1)) * 2 ^ (63 - (i + 1)) +
  (xl mod 2 ^ (63 - i)) mod 2 ^ (63 - (i + 1)))%Z
       with ((q0 * y + xh0') * 2 ^ (63 - i) + xl mod 2^(63-i))%Z=>//.
    rewrite <- Z.add_assoc.
    rewrite [(xl mod 2 ^ (63 - i) / 2 ^ (63 - (i + 1)) * 2 ^ (63 - (i + 1)))%Z] Z.mul_comm.
    rewrite <- Hxldivmod. reflexivity.
Qed.


Lemma div21_loop_body_reduce (gidx : globalidx) :
  forall state sr fr m gmp i xh xl xh0' xl0' q0 y,
    INV fenv nenv sr fr ->
    smem sr (f_inst fr) = Some m ->
    sglob_val sr (f_inst fr) glob_mem_ptr = Some (VAL_num (VAL_int32 (N_to_i32 gmp))) ->
    sglob_val sr (f_inst fr) glob_cap = Some (VAL_num (VAL_int32 (Int32.repr i))) ->
    (0 <= i < 63)%Z ->
    div21_loop_invariant sr fr i xh xl xh0' xl0' y q0 ->
    exists sr' xh1' xl1' q1,
    reduce_trans
      (state, sr, fr, to_e_list (diveucl_21_loop_body glob_tmp1 glob_tmp2 glob_tmp3 glob_tmp4))
      (state, sr', fr, [])
    /\ INV fenv nenv sr' fr
    /\ s_funcs sr = s_funcs sr'
    /\ smem sr' (f_inst fr) = Some m
    /\ sglob_val sr' (f_inst fr) glob_mem_ptr = Some (VAL_num (VAL_int32 (N_to_i32 gmp)))
    /\ div21_loop_invariant sr' fr (i + 1) xh xl xh1' xl1' y q1
    /\ sglob_val sr' (f_inst fr) glob_cap = Some (VAL_num (VAL_int32 (Int32.repr i))).
Proof with eassumption.
  intros state sr fr m gmp i xh xl xh0' xl0' q0 y.
  intros HINV Hmem Hgmp Hival Hi HLoopINV.
  destruct HLoopINV as [Hxh0' [Hxl0' [Hy [Hq0 [Hli1 [Hli2 [Hli3 [Hli4 Hli5]]]]]]]].
  have I := HINV. destruct I as [_ [_ [_ [_ [_ [_ [_ [_ [_ [_ [HnoDups [_ [_ [_ [_ Hw]]]]]]]]]]]]]]].
  assert (Hglob_tmp1: i64_glob glob_tmp1) by now cbn; tauto.
  assert (Hglob_tmp2: i64_glob glob_tmp2) by now cbn; tauto.
  assert (Hglob_tmp3: i64_glob glob_tmp3) by now cbn; tauto.
  assert (Hglob_tmp4: i64_glob glob_tmp4) by now cbn; tauto.

  set (xl1' := (xl0' mod 2^64 * 2)%Z).
  destruct (Hw glob_tmp2 Hglob_tmp2 (VAL_int64 (Int64.repr xl1'))) as [s0 Hupd0].
  assert (Hg1v : sglob_val s0 (f_inst fr) glob_tmp2 = Some (VAL_num (VAL_int64 (Int64.repr xl1')))).
  { by eapply update_global_get_same; eauto. }
  have Hs0m := update_global_preserves_memory _ _ _ _ _ Hupd0.
  symmetry in Hs0m. rewrite Hmem in Hs0m.
  assert (HINV0: INV fenv nenv s0 fr). {
    eapply update_global_preserves_INV; eauto; cbn=>//. tauto. }
  clear Hw.

  set (xh1' := (xh0' * 2 + (xl1' mod 2^64 / (2^63)))%Z).
  have I := HINV0. destruct I as [_ [_ [_ [_ [_ [_ [_ [_ [_ [_ [_ [_ [_ [_ [_ Hw]]]]]]]]]]]]]]].
  destruct (Hw glob_tmp1 Hglob_tmp1 (VAL_int64 (Int64.repr xh1'))) as [s1 Hupd1].
  assert (Hg2v : sglob_val s1 (f_inst fr) glob_tmp1 = Some (VAL_num (VAL_int64 (Int64.repr xh1'))))
      by now eapply update_global_get_same; eauto.
  have Hs1m := update_global_preserves_memory _ _ _ _ _ Hupd1. symmetry in Hs1m. rewrite Hs0m in Hs1m.
  assert (HINV1 : INV fenv nenv s1 fr). {
    eapply update_global_preserves_INV; eauto; cbn=>//. tauto. }
  clear Hw.

  set (q1 := (q0 * 2)%Z).
  have I := HINV1. destruct I as [_ [_ [_ [_ [_ [_ [_ [_ [_ [_ [_ [_ [_ [_ [_ Hw]]]]]]]]]]]]]]].
  destruct (Hw glob_tmp4 Hglob_tmp4 (VAL_int64 (Int64.repr q1))) as [s2 Hupd2].
  assert (Hg3v : sglob_val s2 (f_inst fr) glob_tmp4 = Some (VAL_num (VAL_int64 (Int64.repr q1))))
      by now eapply update_global_get_same; eauto.
  have Hs2m := update_global_preserves_memory _ _ _ _ _ Hupd2. symmetry in Hs2m. rewrite Hs1m in Hs2m.
  assert (HINV2 : INV fenv nenv s2 fr). {
    eapply update_global_preserves_INV; eauto; cbn=>//. tauto. }
  clear Hw.

  assert (sglob_val s0 (f_inst fr) glob_tmp1 = Some (VAL_num (VAL_int64 (Int64.repr xh0')))). {
    eapply update_global_get_other with (sr:=sr) (j:=glob_tmp2); eauto. discriminate. }

  assert (sglob_val s1 (f_inst fr) glob_tmp2 = Some (VAL_num (VAL_int64 (Int64.repr xl1')))). {
    eapply update_global_get_other with (sr:=s0) (j:=glob_tmp1); eauto. discriminate. }

  assert (sglob_val s1 (f_inst fr) glob_tmp4 = Some (VAL_num (VAL_int64 (Int64.repr q0)))). {
    eapply update_global_get_other with (sr:=s0) (j:=glob_tmp1); eauto. discriminate.
    eapply update_global_get_other with (sr:=sr) (j:=glob_tmp2); eauto. discriminate. }

  assert (sglob_val s2 (f_inst fr) glob_tmp1 = Some (VAL_num (VAL_int64 (Int64.repr xh1')))). {
   eapply update_global_get_other with (sr:=s1) (j:=glob_tmp4); eauto. discriminate. }

  assert (sglob_val s2 (f_inst fr) glob_tmp2 = Some (VAL_num (VAL_int64 (Int64.repr xl1')))). {
    eapply update_global_get_other with (sr:=s1) (j:=glob_tmp4); eauto. discriminate. }

  assert (sglob_val s2 (f_inst fr) glob_tmp3 = Some (VAL_num (VAL_int64 (Int64.repr y)))). {
    eapply update_global_get_other with (sr:=s1) (j:=glob_tmp4); eauto. discriminate.
    eapply update_global_get_other with (sr:=s0) (j:=glob_tmp1); eauto. discriminate.
    eapply update_global_get_other with (sr:=sr) (j:=glob_tmp2); eauto. discriminate. }

  assert (s_funcs sr = s_funcs s2). {
    erewrite <-(update_global_preserves_funcs s1 s2 fr); eauto.
    erewrite <-(update_global_preserves_funcs s0 s1 fr); eauto.
    erewrite <-(update_global_preserves_funcs sr s0 fr); eauto. }

  assert (sglob_val s2 (f_inst fr) glob_mem_ptr = Some (VAL_num (VAL_int32 (N_to_i32 gmp)))). {
    eapply update_global_get_other with (sr:=s1) (j:=glob_tmp4); eauto. discriminate.
    eapply update_global_get_other with (sr:=s0) (j:=glob_tmp1); eauto. discriminate.
    eapply update_global_get_other with (sr:=sr) (j:=glob_tmp2); eauto. discriminate. }

  assert (Hred' :
     reduce_trans
       (state, sr, fr, to_e_list (diveucl_21_loop_body glob_tmp1 glob_tmp2 glob_tmp3 glob_tmp4))
       (state, s2, fr,
          [:: $VN (VAL_int64 (Int64.repr xh1')) ] ++
          [:: $VN (VAL_int64 (Int64.repr y)) ] ++
          [:: AI_basic (BI_relop T_i64 (Relop_i (ROI_ge SX_U)))] ++
          [:: AI_basic (BI_if (BT_valtype None)
                ([:: BI_global_get glob_tmp4] ++
                 [:: BI_const_num (LambdaANF_to_Wasm_primitives.Z_to_i64val_co 1)] ++
                 [:: BI_binop T_i64 (Binop_i BOI_or)] ++
                 [:: BI_global_set glob_tmp4] ++
                 [:: BI_global_get glob_tmp1] ++
                 [:: BI_global_get glob_tmp3] ++
                 [:: BI_binop T_i64 (Binop_i BOI_sub)] ++ [:: BI_global_set glob_tmp1])
                [::])
          ])). {
    dostep_nary' 0. eapply r_global_get...
    dostep_nary' 2. apply r_simple. apply rs_binop_success; first done. cbn.
      unfold Int64.ishl, Int64.shl.
      rewrite Z.shiftl_mul_pow2; last done.
      cbn. rewrite Int64.Z_mod_modulus_eq.
      now rewrite int64_modulus_eq_pow64.
    dostep_nary' 1. eapply r_global_set'...
    dostep_nary' 0. eapply r_global_get...
    dostep_nary' 2. apply r_simple. apply rs_binop_success=>//.
    dostep_nary_eliml 0 1. eapply r_global_get...
    dostep_nary_eliml 2 1. apply r_simple. apply rs_binop_success; first done.
      cbn; unfold Int64.ishr_u, Int64.shru; simpl.
      rewrite Int64.Z_mod_modulus_eq Z.shiftr_div_pow2=>//.
    dostep_nary' 2. apply r_simple. apply rs_binop_success; first done.
      simpl. unfold Int64.ior.
      rewrite Int64.shifted_or_is_add. unfold two_p, two_power_pos. cbn.
      rewrite lt_pow64_mod_modulus_id. rewrite lt_pow64_mod_modulus_id.
      rewrite int64_modulus_eq_pow64. reflexivity.
      rewrite int64_modulus_eq_pow64. subst xh1'; liat.
      cbn in Hli1. lia. cbn; liat.
      cbn; unfold two_power_pos; cbn.
      rewrite lt_pow64_mod_modulus_id.
      rewrite int64_modulus_eq_pow64. lia.
      rewrite int64_modulus_eq_pow64. lia.
    dostep_nary' 1. eapply r_global_set'...
    dostep_nary' 0. eapply r_global_get...
    dostep_nary' 2. apply r_simple. apply rs_binop_success; first done.
      cbn; unfold Int64.ishl, Int64.shl. rewrite Z.shiftl_mul_pow2. cbn.
      rewrite Int64.Z_mod_modulus_id=>//. rewrite int64_modulus_eq_pow64.
      split. clear_except Hli3; lia.
      assert (2^i < 2^64)%Z. { clear_except Hi. apply Z.pow_lt_mono_r; lia. }
      lia. by cbn.
    dostep_nary' 1. eapply r_global_set'...
    dostep_nary' 0. eapply r_global_get...
    dostep_nary_eliml 0 1. eapply r_global_get...
    apply rt_refl. }


  destruct (Z_lt_dec xh1' y) as [Hlt | Hge].
  { (* xh1' < y *)
    exists s2, xh1', xl1', q1.
    split. {
      eapply rt_trans with (y:=(state, s2, fr, ?[es])).
      apply Hred'.
      dostep_nary' 2. apply r_simple. apply rs_relop=>//.
      dostep_nary' 1. apply r_simple. apply rs_if_false. cbn.
      unfold Int64.ltu. rewrite zlt_true. reflexivity.
      cbn. rewrite Int64.Z_mod_modulus_id. rewrite Int64.Z_mod_modulus_id. auto.
      rewrite int64_modulus_eq_pow64. clear_except Hli1; lia.
      rewrite int64_modulus_eq_pow64; lia.
      dostep_nary' 0. eapply r_block with (t1s:=[::]) (t2s:=[:: ])(vs:=[::]); eauto.
      dostep_nary' 0. apply r_simple. apply rs_label_const; cbn; auto. apply rt_refl. }
    do 5! (split; auto).
    {
      do 6! (split; auto). lia.
      split.
        split. clear_except Hli3; lia.
        subst q1.
        replace (2^(i + 1))%Z with (2^i * 2)%Z. clear_except Hli3; lia.
        rewrite Z.pow_add_r=>//. clear_except Hi; lia.
      split.
        subst xl1'. rewrite Hli4.
        rewrite [((xl * 2^i) mod 2^64 * 2)%Z] Z.mul_comm.
        rewrite <-Zmult_mod_distr_l.
        rewrite [(2 * (xl * 2^i))%Z] Z.mul_comm.
        replace (xl * 2^i * 2)%Z with (xl * (2^i * 2^1))%Z by liat.
        clear_except Hi. rewrite <- Z.pow_add_r; lia.
      by eapply div21_loop_arith_lemma; eauto. }
    eapply update_global_get_other with (sr:=s1) (j:=glob_tmp4); eauto. discriminate.
    eapply update_global_get_other with (sr:=s0) (j:=glob_tmp1); eauto. discriminate.
    eapply update_global_get_other with (sr:=sr) (j:=glob_tmp2); eauto. discriminate. }
  { (* xh1' >= y *)
    set (q2 := (q1 + 1)%Z).
    have I := HINV2. destruct I as [_ [_ [_ [_ [_ [_ [_ [_ [_ [_ [_ [_ [_ [_ [_  Hw]]]]]]]]]]]]]]].
    destruct (Hw glob_tmp4 Hglob_tmp4 (VAL_int64 (Int64.repr q2))) as [s3 Hupd3].
    assert (Hg4v : sglob_val s3 (f_inst fr) glob_tmp4 = Some (VAL_num (VAL_int64 (Int64.repr q2)))).
    by eapply update_global_get_same; eauto.
    have Hs3m := update_global_preserves_memory _ _ _ _ _ Hupd3.
    symmetry in Hs3m. rewrite Hs2m in Hs3m.
    assert (HINV3: INV fenv nenv s3 fr). {
      eapply update_global_preserves_INV with (sr:=s2) (i:=glob_tmp4) (num:=(VAL_int64 (Int64.repr q2)))=>//. cbn; tauto. eassumption. }
    clear Hw.

    set (xh2' := (xh1' - y)%Z).
    have I := HINV3. destruct I as [_ [_ [_ [_ [_ [_ [_ [_ [_ [_ [_ [_ [_ [_ [_ Hw]]]]]]]]]]]]]]].
    destruct (Hw glob_tmp1 Hglob_tmp1 (VAL_int64 (Int64.repr xh2'))) as [s4 Hupd4].
    assert (Hg5v : sglob_val s4 (f_inst fr) glob_tmp1 = Some (VAL_num (VAL_int64 (Int64.repr xh2')))).
    by eapply update_global_get_same; eauto.
    have Hs4m := update_global_preserves_memory _ _ _ _ _ Hupd4.
    symmetry in Hs4m. rewrite Hs3m in Hs4m.
    assert (HINV4 : INV fenv nenv s4 fr). {
      eapply update_global_preserves_INV with (sr:=s3) (i:=glob_tmp1) (num:=(VAL_int64 (Int64.repr xh2'))); eauto. discriminate. now intros. now intros. }
    clear Hw.

    assert (sglob_val s3 (f_inst fr) glob_tmp1 = Some (VAL_num (VAL_int64 (Int64.repr xh1')))). {
      eapply update_global_get_other with (sr:=s2) (j:=glob_tmp4); eauto. discriminate. }
    assert (sglob_val s3 (f_inst fr) glob_tmp3 = Some (VAL_num (VAL_int64 (Int64.repr y)))). {
      eapply update_global_get_other with (sr:=s2) (j:=glob_tmp4); eauto. discriminate. }

    exists s4, xh2', xl1', q2.
    split. {
      eapply rt_trans with (y:=(state, s2, fr, ?[es])). apply Hred'.
      dostep_nary' 2. apply r_simple. apply rs_relop=>//.
      dostep_nary' 1. apply r_simple. apply rs_if_true. cbn.
        unfold Int64.ltu. rewrite zlt_false. discriminate.
        cbn. rewrite Int64.Z_mod_modulus_id. rewrite Int64.Z_mod_modulus_id; auto.
        rewrite int64_modulus_eq_pow64. cbn in Hli1. lia.
        rewrite int64_modulus_eq_pow64. cbn in Hli1. lia.
      dostep_nary' 0. eapply r_block with (t1s:=[::]) (t2s:=[:: ])(vs:=[::]); eauto.
      eapply rt_trans. apply reduce_trans_label0.
      dostep_nary' 0. eapply r_global_get...
      dostep_nary' 2. apply r_simple. apply rs_binop_success; first done.
        cbn. unfold Int64.ior.
        replace (Int64.repr q1) with (Int64.shl (Int64.repr q0) (Int64.repr 1)).
        rewrite Int64.shifted_or_is_add. unfold two_p, two_power_pos. cbn.
        rewrite Int64.Z_mod_modulus_id. reflexivity.
        rewrite int64_modulus_eq_pow64.
        split. clear_except Hli3; lia.
        assert (2^i < 2^64)%Z. { clear_except Hi. apply Z.pow_lt_mono_r; lia. }
        lia. by cbn. by cbn. unfold Int64.shl. rewrite Z.shiftl_mul_pow2. cbn.
        rewrite Int64.Z_mod_modulus_id. reflexivity.
        rewrite int64_modulus_eq_pow64.
        split. lia.
        assert (2^i < 2^64)%Z. { clear_except Hi. apply Z.pow_lt_mono_r; lia. } lia. by cbn.
      dostep_nary' 1. replace (q0 * 2 + 1)%Z with q2 by auto. eapply r_global_set'...
      dostep_nary' 0. eapply r_global_get...
      dostep_nary_eliml 0 1. eapply r_global_get...
      dostep_nary' 2. apply r_simple. apply rs_binop_success; first done. cbn.
        unfold Int64.isub. unfold Int64.sub.
        cbn. rewrite Int64.Z_mod_modulus_id. rewrite Int64.Z_mod_modulus_id. reflexivity.
        rewrite int64_modulus_eq_pow64. lia.
        rewrite int64_modulus_eq_pow64. lia.
      dostep_nary' 1. eapply r_global_set'...
      apply rt_refl.
      apply rt_step. apply r_simple. now apply rs_label_const. }
    split; auto.
    split.
    { erewrite <-(update_global_preserves_funcs s3 s4 fr); eauto.
      erewrite <-(update_global_preserves_funcs s2 s3 fr); eauto. }
    split; auto.
    split.
    { eapply update_global_get_other with (sr:=s3) (j:=glob_tmp1); eauto. discriminate.
      eapply update_global_get_other with (sr:=s2) (j:=glob_tmp4); eauto. discriminate. }
    split; first last.
    { eapply update_global_get_other with (sr:=s3) (j:=glob_tmp1); eauto. discriminate.
      eapply update_global_get_other with (sr:=s2) (j:=glob_tmp4); eauto. discriminate.
      eapply update_global_get_other with (sr:=s1) (j:=glob_tmp4); eauto. discriminate.
      eapply update_global_get_other with (sr:=s0) (j:=glob_tmp1); eauto. discriminate.
      eapply update_global_get_other with (sr:=sr) (j:=glob_tmp2); eauto. discriminate. }
    split; auto.
    split.
    { eapply update_global_get_other with (sr:=s3) (j:=glob_tmp1); eauto. discriminate.
      eapply update_global_get_other with (sr:=s2) (j:=glob_tmp4); eauto. discriminate. }
    split.
    { eapply update_global_get_other with (sr:=s3) (j:=glob_tmp1); eauto. discriminate. }
    split.
    { eapply update_global_get_other with (sr:=s3) (j:=glob_tmp1); eauto. discriminate. }
    split. lia.
    split. lia.
    split.
    { subst q1. replace (2^(i + 1))%Z with (2^i * 2)%Z. lia.
      clear_except Hi. rewrite Z.pow_add_r; lia. }
    split.
    { subst xl1'. rewrite Hli4.
      rewrite [((xl * 2^i) mod 2^64 * 2)%Z] Z.mul_comm.
      rewrite <-Zmult_mod_distr_l. clear_except Hi.
      rewrite [(2 * (xl * 2^i))%Z] Z.mul_comm.
      replace (xl * 2^i * 2)%Z with (xl * (2^i * 2^1))%Z by lia.
      rewrite <- Z.pow_add_r; lia. }
    replace (q1 * y + y + (xh1' - y))%Z with (q1 * y + xh1')%Z by liat.
    erewrite <- div21_loop_arith_lemma with (q1:=q1); eauto.
    f_equal. subst xl1'. lia. }
Qed.

Lemma div21_loop_reduce_full :
  forall d state sr fr m gmp i xh xl xh0' xl0' q0 y,
    INV fenv nenv sr fr ->
    smem sr (f_inst fr) = Some m ->
    sglob_val sr (f_inst fr) glob_mem_ptr = Some (VAL_num (VAL_int32 (N_to_i32 gmp))) ->
    div21_loop_invariant sr fr i xh xl xh0' xl0' y q0 ->
    sglob_val sr (f_inst fr) glob_cap = Some (VAL_num (VAL_int32 (Int32.repr i))) ->
    (0 <= i <= 63)%Z ->
    d = Z.to_nat (63 - i) ->
    exists sr' xh1' xl1' q1,
      reduce_trans
        (state, sr, fr,
          [ AI_basic (BI_loop (BT_valtype None) (diveucl_21_loop glob_cap glob_tmp1 glob_tmp2 glob_tmp3 glob_tmp4 63%Z))])
        (state, sr', fr, [])
      /\ INV fenv nenv sr' fr
      /\ s_funcs sr = s_funcs sr'
      /\ smem sr' (f_inst fr) = Some m
      /\ sglob_val sr' (f_inst fr) glob_mem_ptr = Some (VAL_num (VAL_int32 (N_to_i32 gmp)))
      /\ div21_loop_invariant sr' fr 63%Z xh xl xh1' xl1' y q1
      /\ sglob_val sr' (f_inst fr) glob_cap = Some (VAL_num (VAL_int32 (Int32.repr 63))).
Proof.
  induction d as [|d'] => state sr fr m gmp i xh xl xh0' xl0' q0 y HINV Hmem Hgmp HLoopINV Hival Hi Hd.
  - assert (Heq : i = 63) by lia. subst i.
    exists sr, xh0', xl0', q0.
    split. eapply div21_loop_reduce_stop; eauto. simpl_modulus. cbn; lia. lia.
    by repeat (split; auto).
  - assert (Hi' : (i < 63)%Z) by lia.
    destruct (div21_loop_body_reduce
                glob_tmp1 (* TODO: remove *)
                state sr fr m gmp i xh xl xh0' xl0' q0 y)
          as [sr' [xh1' [xl1' [q1 [HredBody [HINV' [Hsfs' [Hmem' [Hgmp' [HLoopINV' Hival']]]]]]]]]]; auto. lia.
    destruct (div21_loop_reduce_continue state sr sr' fr m gmp i xh xl xh0' xl0' xh1' xl1' q0 q1 y)
          as [sr'' [HredLoop [HLoopInvariant'' [Hival'' [HINV'' [Hmem'' [Hsfs'' Hgmp'']]]]]]]; auto. lia.
    destruct (IHd' state sr'' fr m gmp (i + 1)%Z xh xl xh1' xl1' q1 y)
          as [srIH [xh2' [xl2' [q2 [HredIH [HINV_IH [HsfsIH [HgmpIH [HLoopInvIH HivalIH]]]]]]]]]; auto; try lia.
    exists srIH, xh2', xl2', q2.
    split.
    { eapply rt_trans.
      apply HredLoop.
      apply HredIH. }
    by rewrite Hsfs'' HsfsIH.
Qed.

Lemma simple_arith_binop_reduce : forall state sr1 sr2 sr3 fr1 gmpv mem1 mem2 lx ly addrx addry bsx bsy vx vy bop u63_arith_fun mask w l,
  N.to_nat l < Datatypes.length (f_locs fr1) ->
  local_holds_address_to_i64 sr1 fr1 lx addrx (Int64.repr (to_Z vx)) mem1 bsx ->
  local_holds_address_to_i64 sr1 fr1 ly addry (Int64.repr (to_Z vy)) mem1 bsy ->
  smem sr1 (f_inst fr1) = Some mem1 ->
  sglob_val sr1 (f_inst fr1) glob_mem_ptr = Some (VAL_num (VAL_int32 (N_to_i32 gmpv))) ->
  sr2 = upd_s_mem sr1 (set_nth mem2 (s_mems sr1) 0 mem2) ->
  smem_store sr1 (f_inst fr1) (N_of_uint i32m (N_to_i32 gmpv)) 0%N
    (VAL_int64 (Int64.repr (to_Z (u63_arith_fun vx vy)))) T_i64 = Some sr2 ->
  app_binop (Binop_i bop) (VAL_int64 (Int64.repr (to_Z vx))) (VAL_int64 (Int64.repr (to_Z vy))) = Some (VAL_int64 w) ->
  (mask = true -> Int64.iand w (Int64.repr maxuint63) = Int64.repr (to_Z (u63_arith_fun vx vy))) ->
  (mask = false -> w = Int64.repr (to_Z (u63_arith_fun vx vy))) ->
  supdate_glob sr2 (f_inst fr1) glob_mem_ptr
    (VAL_num (VAL_int32 (Int32.iadd (N_to_i32 gmpv) (nat_to_i32 8)))) = Some sr3 ->
  reduce_trans
    (state, sr1, fr1, map AI_basic (apply_binop_and_store_i64 glob_mem_ptr bop lx ly mask ++ [ BI_local_set l ]))
    (state, sr3, {| f_locs := set_nth (VAL_num (VAL_int32 (N_to_i32 gmpv))) (f_locs fr1)
                           (N.to_nat l) (VAL_num (VAL_int32 (N_to_i32 gmpv)));
                       f_inst := f_inst fr1 |}, []).
Proof with eassumption.
  intros state1 sr1 sr2 sr3 fr1 gmpv mem1 mem2 lx ly addrx addry bsx bsy vx vy bop u63_arith_fun mask w l.
  intros Hl [Hlocx [Hloadx Hdesx]] [Hlocy [Hloady Hdesy]] Hmem1' Hgmp1 Hsr2 Hstore1 Happ Hmaskt Hmaskf Hupd1.
  simpl.
  dostep_nary 0. apply r_global_get...
  eapply rt_trans. apply app_trans_const=>//.
  dostep_nary 0. apply r_local_get...
  dostep_nary 1. eapply r_load_success...
  rewrite Hdesx.
  dostep_nary_eliml 0 1. apply r_local_get...
  dostep_nary_eliml 1 1. apply r_load_success with (m:=mem1)...
  rewrite Hdesy.
  dostep_nary 2. apply r_simple. apply rs_binop_success; first done.
    rewrite Happ=>//.
    destruct mask.
    - unfold bitmask_instrs.
      dostep_nary 2. apply r_simple. apply rs_binop_success; first done. simpl.
      rewrite (Hmaskt Logic.eq_refl). reflexivity. apply rt_refl.
    - rewrite (Hmaskf Logic.eq_refl). apply rt_refl.
  dostep_nary 2. apply r_store_success...
  dostep_nary 0. apply r_global_get.
    eapply update_memory_preserves_globals...
  dostep_nary_eliml 0 1. apply r_global_get.
    eapply update_memory_preserves_globals...
  dostep_nary_eliml 2 1. apply r_simple. apply rs_binop_success=>//.
  dostep_nary_eliml 1 1. apply r_global_set'...
  apply rt_step. eapply r_local_set'=>//.
  now apply /ssrnat.leP.
Qed.


Theorem primitive_operation_reduces_proof : forall pfs,
    prim_funs_env_wellformed cenv penv pfs ->
    primitive_operation_reduces cenv fenv nenv penv pfs.
Proof.
  intros pfs Hpfs.
  unfold primitive_operation_reduces.
  intros ????????????????????? Hf' Hpenv Hop HlenvInjective Hdisjoint HfenvWf
    HlocsInBounds Hrepr_x HrelE HprimRepr Hinv HenoughM Hys_vs HprimResSome.

  have I := Hinv. destruct I as [_ [_ [_ [Hgmp_w [_ [Hmut [Hlinmem _]]]]]]].
  destruct Hlinmem as [Hmem1 [m [Hmem2 [size [<- [Hmem4 Hmem5]]]]]].
  destruct (i32_glob_implies_i32_val _ _ _ (gmp_i32_glob cenv fenv nenv penv) Hgmp_w Hmut)
        as [g' Hgmp].
  destruct (i32_exists_N g') as [gmp_v [-> HgmpBound]].
  have HenoughM' := HenoughM _ _ Hmem2 Hgmp HgmpBound.
  have Hnofunval := primop_value_not_funval _ _ _ _ _ _ _ _ _ _ Hpfs Hf' Hpenv Hop HprimResSome.
  have Hpfs' := Hpfs _ _ _ _ _ _ _ vs v Hpenv Hop Hf' HprimResSome.
  clear Hop.
  rename x into x0, x' into x0'.
  inv HprimRepr.
  { (* Unary operations *)
    assert (forall w, exists mem, store m (Wasm_int.N_of_uint i32m (N_to_i32 gmp_v)) 0%N
                                          (serialise_num (VAL_int64 w)) 8 = Some mem)
        as Htest. {
      intros. apply notNone_Some, enough_space_to_store. cbn.
      rewrite length_serialise_num_i64. cbn.
      rewrite Wasm_int.Int32.Z_mod_modulus_id; lia. }

    rename H into Hrepr_arg1, H0 into Hrepr_primop.
    assert (exists xp, rho ! x = Some (Vprim (primInt xp))
                    /\ vs = [ Vprim (primInt xp) ]). {
      destruct Hpfs' as  [? [? [? [? [? [? [? [? [? [? [? [? [Hres _]]]]]]]]]]]]].
      unfold get_list in *.
      destruct (rho ! x) eqn:Hrho_x=>//.
      assert (Hin1 : List.In v0 vs) by (inv Hys_vs; now constructor).
      destruct (apply_primop_only_defined_on_primInts _ vs v _ _ _ _ _ _ _ _ Hres v0 Hin1)
            as [xp Hxp].
      exists xp.
      split; subst; auto.
      congruence. }
    destruct H as [xp [Hrho_x Hvs]].
    assert (exists walx,
        stored_in_locals (lenv:=lenv) nenv x walx f
     /\ repr_val_LambdaANF_Wasm cenv fenv nenv penv  (Vprim ( primInt xp)) s (f_inst f) walx). {
      destruct HrelE as [_ [_ Hvars]].
      assert (occurs_free (Eprim x0 p [:: x ] e) x) by now (constructor; constructor).
      assert (HfdsNone_x: find_def x fds = None). {
        inv Hrepr_arg1.
        unfold translate_var in H0.
        destruct (lenv ! x) eqn:Hx. 2: now rewrite Hx in H0.
        unfold domains_disjoint in Hdisjoint.
        apply Hdisjoint in Hx.
        apply HfenvWf_None with (f:=x) in HfenvWf. now rewrite HfenvWf.
      }
      have Hx := Hvars _ H HfdsNone_x. destruct Hx as [vx' [wx [Hrho_x' [Hloc_x Hval_x]]]].
      exists wx.
 split; auto.
      rewrite Hrho_x in Hrho_x'.
      now inv Hrho_x'. }
    destruct H as [walx [Hloc_x Hval_x]].
    destruct Hloc_x as [? [Htrans Hx']].
    assert (x1 = x'). { eapply repr_var_det; eassumption. }
    subst x1. clear Htrans.
    assert (Hrv1: exists addrx, walx = Val_ptr addrx
                                /\ load_i64 m addrx = Some (VAL_int64 (Z_to_i64 (to_Z xp)))). {
      inv Hval_x. replace m with m0 by congruence. exists addr. split; auto.
      remember (primInt n) as p1; remember (primInt xp) as p2.
      inversion H5; subst p1 p2.
      now replace xp with n by now apply Classical_Prop.EqdepTheory.inj_pair2 in H7.
    }
    destruct Hrv1 as [addrx Hloadx].
    destruct Hloadx as [? Hloadx]. subst walx.
    unfold load_i64 in Hloadx. destruct (load m addrx 0%N 8) eqn:Hloadx'. 2: discriminate.
    assert (Haddrx: addrx = (Wasm_int.N_of_uint i32m (wasm_value_to_i32 (Val_ptr addrx)))). {
      cbn. rewrite Wasm_int.Int32.Z_mod_modulus_id. now rewrite N2Z.id.
      inv Hval_x. lia. }
    destruct Hpfs' as
      [true_tag [false_tag [bool_tag [eq_tag [lt_tag [gt_tag [comp_tag [c0_tag [c1_tag [carry_tag [pair_tag [prod_tag [Hres [Htrue [Hfalse [Heq [Hlt [Hgt [Hc0 [Hc1 Hpair]]]]]]]]]]]]]]]]]]]].
    assert (Hflocs: N.to_nat x0' < Datatypes.length (f_locs f)) by now eapply HlocsInBounds; eauto.
    assert (HgmpBounds: (Z.of_N gmp_v + Z.of_N 52 <= Z.of_N (mem_length m) < Int32.modulus)%Z). {
      apply mem_length_upper_bound in Hmem5. cbn in Hmem5.
      simpl_modulus. cbn. cbn in HenoughM. lia. }
    rewrite Hvs in Hres.
    unfold apply_LambdaANF_primInt_operator in Hres.
    assert (forall n,
             exists s' s_final fr m' wal,
               s' = upd_s_mem s (set_nth m' s.(s_mems) 0 m')
               /\ smem_store s (f_inst f) (Wasm_int.N_of_uint i32m (N_to_i32 gmp_v)) 0%N
                    (VAL_int64 (Z_to_i64 (to_Z n))) T_i64 = Some s'
               /\ fr ={| f_locs := set_nth (VAL_num (VAL_int32 (wasm_value_to_i32 wal))) (f_locs f) (N.to_nat x0') (VAL_num (VAL_int32 (wasm_value_to_i32 wal)))
                      ; f_inst := f_inst f
                      |}
               /\ smem s' (f_inst fr) = Some m'
               /\ reduce_trans (state, s', f, map AI_basic [ BI_global_get glob_mem_ptr
                                                             ; BI_global_get glob_mem_ptr
                                                             ; BI_const_num (nat_to_value 8)
                                                             ; BI_binop T_i32 (Binop_i BOI_add)
                                                             ; BI_global_set glob_mem_ptr
                                                             ; BI_local_set x0'
                    ])
                    (state, s_final, fr, [::])

               /\ INV fenv nenv s' fr
               /\ supdate_glob s' (f_inst f) glob_mem_ptr
                    (VAL_num (VAL_int32 (Wasm_int.Int32.iadd (N_to_i32 gmp_v) (nat_to_i32 8)))) = Some s_final
               /\ INV fenv nenv s_final fr
               /\ f_inst f = f_inst fr
               /\ s_funcs s = s_funcs s_final
               /\ min_available_memory s_final (f_inst f) mem
               /\ rel_env_LambdaANF_Wasm (lenv:=lenv) cenv fenv nenv penv e (M.set x0 (Vprim (primInt n)) rho) s_final fr fds
               /\ (forall (wal : wasm_value) (v : val),
                      repr_val_LambdaANF_Wasm cenv fenv nenv penv v s (f_inst f) wal -> repr_val_LambdaANF_Wasm cenv fenv nenv penv v s_final (f_inst fr) wal)
               /\ (exists wal,
                      fr ={| f_locs := set_nth (VAL_num (VAL_int32 (wasm_value_to_i32 wal))) (f_locs f) (N.to_nat x0') (VAL_num (VAL_int32 (wasm_value_to_i32 wal)))
                          ; f_inst := f_inst f |}
                      /\ repr_val_LambdaANF_Wasm cenv fenv nenv penv (Vprim (primInt n)) s_final (f_inst fr) wal)). {
      intros.
      destruct (Htest (Z_to_i64 (to_Z n))) as [m' Hm'].
      remember (upd_s_mem s (set_nth m' s.(s_mems) 0 m')) as s'.
      exists s'.
      assert (Hm'': smem_store s (f_inst f) (Wasm_int.N_of_uint i32m (N_to_i32 gmp_v)) 0%N
                      (VAL_int64 (Z_to_i64 (to_Z n))) T_i64 = Some s'). {
        unfold smem_store. rewrite Hmem1. cbn. subst s'.
        unfold smem in Hmem2. rewrite Hmem1 in Hmem2. destruct (s_mems s)=>//.
        injection Hmem2 as ->. now rewrite Hm'. }
      assert (Hinv' : INV fenv nenv s' f). {
        subst.
        assert (mem_length m = mem_length m'). {
          apply store_length in Hm'. congruence. }
        assert (m.(meminst_type).(lim_max) = m'.(meminst_type).(lim_max)). {
          apply store_lim_max in Hm'. congruence. }
        eapply update_mem_preserves_INV; auto. apply Hinv. eassumption. erewrite <- H. lia.
        congruence. exists (mem_size m); split; auto. unfold mem_size. congruence. }
      have I := Hinv'. destruct I as [_ [_ [_ [Hgmp_w' [_ [Hglob_mut [Hlinmem' [Hgmp' [_ [_ [_ [_ [_ [Hgmp_mult_two _]]]]]]]]]]]]]].
      destruct Hlinmem' as [Hmem1' [m'' [Hmem2' [size' [Hmem3' [Hmem4' Hmem5']]]]]].
      destruct (Hgmp_w' (VAL_int32 (Wasm_int.Int32.iadd (N_to_i32 gmp_v) (nat_to_i32 8)))) as [s_final Hupd_glob].
      assert (smem s' (f_inst f) = Some m'). {
        subst s'. unfold smem, lookup_N. cbn.
        rewrite Hmem1'. apply set_nth_nth_error_same with (e:=m).
        unfold smem in Hmem2. rewrite Hmem1 in Hmem2.
        destruct (s_mems s)=>//. }
      assert (m' = m'') by congruence. subst m''.
      assert (HgmpBound': (gmp_v + 8 + 8 < mem_length m')%N). {
        assert (mem_length m = mem_length m') by
          now apply store_length in Hm'.
        replace (mem_length m') with (mem_length m).
        now unfold page_size in *. }
      remember {| f_locs := set_nth (VAL_num (N_to_value gmp_v)) (f_locs f) (N.to_nat x0') (VAL_num (N_to_value gmp_v))
               ; f_inst := f_inst f
               |} as fr.
      assert (Hinv'': INV fenv nenv s' fr). {
        now apply update_local_preserves_INV with (f:=f) (x':=N.to_nat x0') (v:=N_to_i32 gmp_v).
      }
      assert (Hsglobval_s':sglob_val s' (f_inst f) glob_mem_ptr = Some (VAL_num (VAL_int32 (N_to_i32 gmp_v)))) by
        now apply (update_memory_preserves_globals s f) with m'.
      assert (Hgmp_w'' : INV_glob_mem_ptr_writable s' f) by now destruct Hinv'.
      assert (Z.of_N (gmp_v + 8)%N < Wasm_int.Int32.modulus)%Z as HgmpModulus by now
          apply mem_length_upper_bound in Hmem5; simpl_modulus; cbn in Hmem5 |- *.
      assert (HfsEq: s_funcs s = s_funcs s') by now subst.
      assert (HfsEq': s_funcs s' = s_funcs s_final) by now apply update_global_preserves_funcs in Hupd_glob.
      assert (HfsEq'': s_funcs s = s_funcs s_final) by now subst.
      assert (HgmpBound'': (-1 < Z.of_N (gmp_v + 8) < Wasm_int.Int32.modulus)%Z). {
        apply mem_length_upper_bound in Hmem5. simpl_modulus_in Hmem5. cbn in Hmem5.
        simpl_modulus. cbn. lia.
      }

      assert (HenoughM'': (gmp_v + 52 < mem_length m')%N). {
        assert (mem_length m = mem_length m') by
          now apply store_length in Hm'.
        replace (mem_length m') with (mem_length m). lia. }

      assert (Hinv_final : INV fenv nenv s_final fr). {
        eapply update_global_preserves_INV with (sr:=s') (i:=glob_mem_ptr) (num:=(VAL_int32 (N_to_i32 (gmp_v + 8)))); eauto.
        left. split. apply gmp_i32_glob; auto. now cbn. discriminate.
        now subst fr.
        move => _. intros.
        destruct Hgmp_mult_two with (gmp_v:=gmp_v) (m:=m') as [n0' Hn0]. assumption.
        now subst s'.
        lia.
        destruct H0 as [Heqn0 Hboundn0].
        replace n0 with (gmp_v + 8)%N. lia.
        inv Heqn0.
        simpl_eq. lia.
        move => _. intros.
        destruct Hgmp_mult_two with (gmp_v:=gmp_v) (m:=m') as [n0' Hn0]. assumption.
        now subst s'.
        lia.
        destruct H0 as [Heqn0 Hboundn0].
        replace n0 with (gmp_v + 8)%N.
        exists (n0' + 4)%N; lia.
        inv Heqn0.
        simpl_eq. lia.
        unfold Wasm_int.Int32.iadd, Wasm_int.Int32.add in Hupd_glob.
        rewrite Heqfr. cbn in Hupd_glob |- *.
        rewrite Wasm_int.Int32.Z_mod_modulus_id in Hupd_glob; last lia.
        unfold N_to_i32.
        now replace (Z.of_N gmp_v + 8)%Z with (Z.of_N (gmp_v + 8))%Z in Hupd_glob by lia.
      }

      destruct (Hgmp_w' (VAL_int32 (Int32.repr (Z.of_N (gmp_v + 8)%N)))) as [sr' Hglob_sr'].

      assert (Hinv_sr' : INV fenv nenv sr' fr). {
        eapply update_global_preserves_INV with (sr:=s') (i:=glob_mem_ptr) (num:=(VAL_int32 (N_to_i32 (gmp_v+8)))); eauto.
        left. split. apply gmp_i32_glob; auto. now cbn. discriminate.
        now subst fr.
        move => _.
        intros n0 [Heqn0 Hboundn0].
        replace n0 with (gmp_v + 8)%N. lia.
        inversion Heqn0.
        simpl_eq. lia.
        move => _.
        destruct Hgmp_mult_two with (gmp_v:=gmp_v) (m:=m') as [n0' Hn0]; auto.
        intros n0 [Heqn0 Hboundn0].
        replace n0 with (gmp_v + 8)%N.
        exists (n0' + 4)%N. lia.
        inversion Heqn0.
        simpl_eq. lia.
        now subst fr.
      }

      assert (Hrepr_val : repr_val_LambdaANF_Wasm cenv fenv nenv penv (Vprim (primInt n)) sr' (f_inst fr) (Val_ptr gmp_v)). {
        apply Rprim_v with (gmp:=(gmp_v+8)%N) (m:=m'); auto.
        subst fr. eapply update_global_get_same. eassumption.
        lia.
        destruct Hgmp_mult_two with (gmp_v:=gmp_v) (m:=m') as [n0 Hn0].
        assumption. assumption. lia. exists n0. lia.
        replace (smem sr' (f_inst fr)) with (smem s' (f_inst fr)) by now subst fr; eapply update_global_preserves_memory.
        now subst fr.
        assert ((wasm_deserialise (serialise_num (VAL_int64 (Z_to_i64 (to_Z n)))) T_i64) = (VAL_int64 (Z_to_i64 (to_Z n)))) by now apply deserialise_serialise.
        rewrite -H0.
        apply (store_load_i64 m m' gmp_v (serialise_num (VAL_int64 (Z_to_i64 (to_Z n))))); auto.
        assert (Wasm_int.N_of_uint i32m (N_to_i32 gmp_v) = gmp_v). {
          cbn. rewrite Wasm_int.Int32.Z_mod_modulus_id; lia. }
        rewrite -H1.
        apply Hm'. }
      assert (HvalsPreserved : forall (wal : wasm_value) (v : val),
                 repr_val_LambdaANF_Wasm cenv fenv nenv penv v s (f_inst f) wal -> repr_val_LambdaANF_Wasm cenv fenv nenv penv v sr' (f_inst fr) wal). {
        intros.
        apply val_relation_depends_on_mem_smaller_than_gmp_and_funcs with (sr:=s) (m:=m) (m':=m') (gmp:=gmp_v) (gmp':=(gmp_v + 8)%N); auto.
        replace (s_funcs s) with (s_funcs s') by auto.
        now apply update_global_preserves_funcs in Hglob_sr'.
        now subst fr.
        replace (smem sr' (f_inst fr)) with (smem s' (f_inst fr)) by now subst fr; eapply update_global_preserves_memory.
        now subst fr.
        now subst fr.
        { simpl_modulus. cbn. simpl_modulus_in H0. cbn in H0. simpl_modulus_in HgmpBound.
          apply mem_length_upper_bound in Hmem5.
          unfold page_size, max_mem_pages in *. lia. }
        apply update_global_get_same with (sr:=s').
        now subst fr.
        { simpl_modulus. cbn.
          subst size'.
          apply mem_length_upper_bound in Hmem5'.
          unfold page_size, max_mem_pages in *.
          lia. }
        lia.
        { intros.
          assert (Hex: exists v, load_i32 m a = Some v). {
            apply enough_space_to_load. subst.
            simpl_modulus_in HenoughM'.
            apply store_length in Hm'. lia. }
          destruct Hex as [v' Hv'].
          rewrite Hv'.
          symmetry.
          apply (load_store_load_i32' m m' a (Wasm_int.N_of_uint i32m (N_to_i32 gmp_v)) v' (serialise_num (VAL_int64 (Z_to_i64 (to_Z n))))); auto.
          cbn. rewrite Wasm_int.Int32.Z_mod_modulus_id; lia. }
        { intros a Ha.
          assert (Hex: exists v, load_i64 m a = Some v). {
            apply enough_space_to_load_i64. lia. }
          destruct Hex as [v' Hv'].
          rewrite Hv'. symmetry.
          apply (load_store_load_i64' m m' a (Wasm_int.N_of_uint i32m (N_to_i32 gmp_v)) v' (serialise_num (VAL_int64 (Z_to_i64 (to_Z n))))); auto.
          cbn. rewrite Wasm_int.Int32.Z_mod_modulus_id; lia.
        }
        now subst fr. }
      assert (HrelE' : rel_env_LambdaANF_Wasm (lenv:=lenv)  cenv fenv nenv penv e (M.set x0 (Vprim (primInt n)) rho) sr' fr fds). {
        have Hl := HlocsInBounds _ _ Hrepr_x.
        apply nth_error_Some in Hl.
        apply notNone_Some in Hl. destruct Hl as [? Hlx].
        unfold rel_env_LambdaANF_Wasm.
        destruct HrelE as [Hfun1 [Hfun2 Hvar]].
        split.
        { (* funs1 *)
          intros ????? Hrho Hv'.
          destruct (var_dec x0 x2).
          - (* x = x1 *)
            subst x2. rewrite M.gss in Hrho. inv Hrho.
            assert (~ subval_or_eq (Vfun rho' fds' f0) (Vprim (primInt n))).
            { now apply subval_or_eq_fun_not_prim. }
            contradiction.
          - (* x <> x1 *)
            now rewrite M.gso in Hrho; eauto.
        }
        split.
        { intros ? Hnfd. apply Hfun2 in Hnfd.
          destruct Hnfd as [i' [Htrans Hval]].
          exists i'. split. assumption.
          apply val_relation_func_depends_on_funcs with (s:=s); auto.
          replace (s_funcs s) with (s_funcs s') by auto.
          now apply update_global_preserves_funcs in Hglob_sr'.
          now subst fr.
        }
        intros. destruct (var_dec x0 x2).
        { (* x = x1 *)
          subst x2. exists (Vprim (primInt n)), (Val_ptr gmp_v).
          rewrite M.gss. split; auto.
          split.
          exists x0'. cbn. split. assumption.
          unfold lookup_N; cbn; auto.
          subst fr. cbn. erewrite set_nth_nth_error_same; eauto.
          now subst fr.
        }
        { (* x <> x1 *)
          assert (Hocc : occurs_free (Eprim x0 p [:: x ] e) x2) by now apply Free_Eprim2.
          have H' := Hvar _ Hocc H1.
          destruct H' as [val' [wal' [Hrho [Hloc Hval]]]].
          exists val', wal'. split.
          rewrite M.gso; auto. split.
           destruct Hloc as [i' [Hl1 Hl2]].
          unfold stored_in_locals. exists i'. split; auto.
          subst fr. unfold lookup_N.
          rewrite set_nth_nth_error_other; auto.

          intro. assert (x0' = i') by lia. subst x0'.
          have Hcontra := repr_var_inj _ _ _ _ HlenvInjective Hl1 Hrepr_x.
          contradiction.

          now apply HvalsPreserved.
        }
      }
      exists sr', fr, m', (Val_ptr gmp_v).
      try repeat (split; auto). all: subst fr; auto.
      assert (sglob_val s' (f_inst f) glob_mem_ptr =
                Some (VAL_num (VAL_int32 (N_to_i32 gmp_v)))) by now subst s'.
      separate_instr.
      dostep_nary 0. eapply r_global_get.
      eassumption.
      eapply rt_trans
        with (y:=(state, sr', f, [$V VAL_num (VAL_int32 (N_to_i32 gmp_v))] ++ [AI_basic (BI_local_set x0')])).
      eapply app_trans_const; auto.
      dostep_nary 0. apply r_global_get; eassumption.
      dostep_nary 2. constructor; apply rs_binop_success; reflexivity.
      cbn; unfold Wasm_int.Int32.iadd, Wasm_int.Int32.add; cbn.
      rewrite Wasm_int.Int32.Z_mod_modulus_id. 2: lia.
      dostep_nary 1. rewrite N2Z.inj_add in Hglob_sr'. eapply r_global_set'; eauto.
      cbn; apply rt_refl.
      cbn. dostep_nary' 1. eapply r_local_set' with (f':={|f_locs := set_nth (VAL_num (N_to_value gmp_v)) (f_locs f) (N.to_nat x0') (VAL_num (N_to_value gmp_v)); f_inst := f_inst f|}). reflexivity.
      apply /ssrnat.leP.
      apply HlocsInBounds in Hrepr_x. lia.
      reflexivity.
      now apply rt_refl.
      cbn; unfold Wasm_int.Int32.iadd, Wasm_int.Int32.add; cbn.
      rewrite Wasm_int.Int32.Z_mod_modulus_id; [|lia].
      unfold N_to_i32 in Hglob_sr'.
      replace 8%Z with (Z.of_N 8) by now cbn.
      rewrite -N2Z.inj_add.
      assumption.
      replace (s_funcs s) with (s_funcs s') by auto.
      now apply update_global_preserves_funcs in Hglob_sr'.

      (* minimum mem *)
      intros ?????.
      assert (m0 = m'). { apply update_global_preserves_memory in Hglob_sr'. now solve_eq m0 m'. }
      subst m0.
      assert (gmp = gmp_v + 8)%N. {
        apply update_global_get_same in Hglob_sr'.
        rewrite Hglob_sr' in H1.
        inv H1. now simpl_eq. } subst gmp.
      apply store_length in Hm'. lia.

      exists (Val_ptr gmp_v).
      split; auto. }
    destruct op=>//.
    { (* head0 *)
      rename H into Hrelations.
      inversion Hres as [Hv_un]. simpl.
      destruct (Hrelations (head0 xp)) as [s' [s_final [fr [m' [wal [Hs' [Hstore [Hfr [Hsmem [Hstep [Hinv1 [Hupd_glob Hr]]]]]]]]]]]].
      exists s_final, fr. simpl in Hv_un. unfold LambdaANF_primInt_unop_fun in Hv_un.
      clear Hrelations Htrue Hfalse Hc0 Hc1 Hpair Heq Hlt Hgt Htest Hnofunval HfenvWf HlenvInjective Hdisjoint. unfold LambdaANF_primInt_unop_fun.

      replace v with (Vprim ( AstCommon.primInt ; (head0 xp))) in * by congruence.
      split; auto.
      inversion Hrepr_primop.
      unfold head0_instrs.
      dostep_nary 0. eapply r_global_get; eassumption.
      eapply rt_trans. eapply app_trans_const with (es':=[$VN (VAL_int64 (Int64.repr (to_Z (head0 xp))))] ++ ?[es_after]); eauto.
      dostep_nary 0. eapply r_local_get; eassumption.
      dostep_nary 1. eapply r_load_success; eauto. rewrite <- Haddrx. simpl; eauto.
      replace (wasm_deserialise b0 T_i64) with (VAL_int64 (Int64.repr (to_Z xp))) by now inversion Hloadx.
      dostep_nary 1. apply r_simple. apply rs_unop; first done.
      eapply rt_trans with (y:=(state, s, f, [ $VN VAL_int64 (Int64.repr (to_Z (head0 xp)))] ++ ?[es_after'])).
      destruct (Z.eq_dec (to_Z xp) (to_Z 0)) as [Heq0 | Hneq0].
      dostep_nary 2. apply r_simple. apply rs_binop_success; first done. simpl.
      unfold Int64.isub, Int64.sub. replace (Int64.unsigned (Int64.repr 1)) with 1%Z by now cbn.
      rewrite Heq0. replace (Int64.clz (Int64.repr (to_Z 0))) with (Int64.repr 64). simpl.
      replace (Int64.repr 63) with (Int64.repr (to_Z (head0 0))). reflexivity.
      rewrite head00_spec. unfold digits. reflexivity. reflexivity.
      rewrite to_Z_0. unfold Int64.clz. reflexivity. apply to_Z_inj in Heq0. rewrite Heq0.
      apply rt_refl.
      dostep_nary 2. apply r_simple. apply rs_binop_success; first done. simpl.
      unfold Int64.isub, Int64.sub. replace (Int64.unsigned (Int64.repr 1)) with 1%Z by now cbn.
      rewrite to_Z_0 in Hneq0. rewrite <-head0_int64_clz. reflexivity. have Hboundedx := (to_Z_bounded xp). lia.
      apply rt_refl. apply rt_refl.
      dostep_nary 2. eapply r_store_success; eauto.
      apply Hstep.
    }
    { (* tail0 *)
      rename H into Hrelations.
      inversion Hres as [Hv_un]. simpl.
      destruct (Hrelations (tail0 xp)) as [s' [s_final [fr [m' [wal [Hs' [Hstore [Hfr [Hsmem [Hstep [Hinv1 [Hupd_glob Hr]]]]]]]]]]]].
      exists s_final, fr. simpl in Hv_un. unfold LambdaANF_primInt_unop_fun in Hv_un.
      clear Hrelations Htrue Hfalse Hc0 Hc1 Hpair Heq Hlt Hgt Htest Hnofunval HfenvWf HlenvInjective Hdisjoint.
      replace v with (Vprim ( AstCommon.primInt ; (tail0 xp))) in * by congruence.
      split; auto.
      inversion Hrepr_primop.
      unfold tail0_instrs.
      dostep_nary 0. eapply r_global_get; eassumption.
      eapply rt_trans. eapply app_trans_const with (es':=[$VN (VAL_int64 (Int64.repr (to_Z (tail0 xp))))] ++ ?[es_after]); eauto.
      dostep_nary 0. eapply r_local_get; eassumption.
      dostep_nary 1. eapply r_load_success; eauto. rewrite <- Haddrx. simpl; eauto.
      replace (wasm_deserialise b0 T_i64) with (VAL_int64 (Int64.repr (to_Z xp))) by now inversion Hloadx.
      dostep_nary 1. apply r_simple. constructor.
      eapply rt_trans with (y:=(state, s, f, [ $VN VAL_int64 (Int64.repr (to_Z (tail0 xp)))] ++ ?[es_after'])).
      destruct (Z.eq_dec (to_Z xp) (to_Z 0)) as [Heq0 | Hneq0].
      dostep_nary 1. apply r_simple. apply rs_if_true. simpl.
      rewrite Heq0. unfold Int64.eq. rewrite to_Z_0. cbn. discriminate.
      dostep_nary 0. eapply r_block with (t1s:=[::]) (t2s:=[:: T_num T_i64])(vs:=[::]); auto.
      dostep_nary 0. apply r_simple. apply rs_label_const; auto.
      replace 63%Z with (to_Z (tail0 xp)).
      apply rt_refl.
      rewrite tail00_spec. unfold digits. cbn. reflexivity. rewrite to_Z_0 in Heq0. exact.
      dostep_nary 1. apply r_simple. apply rs_if_false. simpl.
      unfold Int64.eq. rewrite zeq_false. reflexivity.
      rewrite uint63_unsigned_id. cbn. rewrite to_Z_0 in Hneq0. lia.
      dostep_nary 0. eapply r_block with (t1s:=[::]) (t2s:=[:: T_num T_i64])(vs:=[::]); auto.
      separate_instr.
      reduce_under_label.
      dostep_nary 0. eapply r_local_get; eassumption.
      dostep_nary 1. eapply r_load_success; eauto. rewrite <- Haddrx. simpl; eauto.
      replace (wasm_deserialise b0 T_i64) with (VAL_int64 (Int64.repr (to_Z xp))) by now inversion Hloadx.
      dostep_nary' 1. apply r_simple. apply rs_unop; first done.
      apply rt_refl.
      dostep_nary 0. apply r_simple. apply rs_label_const; auto.
      rewrite tail0_int64_ctz; eauto.
      apply rt_refl.
      have Hb := to_Z_bounded xp.
      rewrite to_Z_0 in Hneq0. lia.
      apply rt_refl.
      dostep_nary 2. eapply r_store_success; eauto.
      apply Hstep. } }
  { (* Binary operations *)
    assert (forall w,
             exists mem, store m (Wasm_int.N_of_uint i32m (N_to_i32 gmp_v)) 0%N
                           (serialise_num (VAL_int64 w))
                           8 = Some mem) as Htest. {
      intros.
      apply notNone_Some, enough_space_to_store. cbn.
      rewrite length_serialise_num_i64. cbn.
      rewrite Wasm_int.Int32.Z_mod_modulus_id; lia. }

    (* TODO cleanup *)
    assert (forall n,
             exists s' s_final fr m' wal,
               wal = Val_ptr gmp_v
                 /\ s' = upd_s_mem s (set_nth m' s.(s_mems) 0 m')
                 /\ smem_store s (f_inst f) (Wasm_int.N_of_uint i32m (N_to_i32 gmp_v)) 0%N
                      (VAL_int64 (Z_to_i64 (to_Z n))) T_i64 = Some s'
                 /\ fr ={| f_locs := set_nth (VAL_num (VAL_int32 (wasm_value_to_i32 wal))) (f_locs f) (N.to_nat x0') (VAL_num (VAL_int32 (wasm_value_to_i32 wal)))
                        ; f_inst := f_inst f
                        |}
                 /\ smem s' (f_inst fr) = Some m'
                 /\ reduce_trans (state, s', f, map AI_basic [ BI_global_get glob_mem_ptr
                                                               ; BI_global_get glob_mem_ptr
                                                               ; BI_const_num (nat_to_value 8)
                                                               ; BI_binop T_i32 (Binop_i BOI_add)
                                                               ; BI_global_set glob_mem_ptr
                                                               ; BI_local_set x0'
                      ])
                      (state, s_final, fr, [::])

                 /\ INV fenv nenv s' fr
                 /\ supdate_glob s' (f_inst f) glob_mem_ptr
                      (VAL_num (VAL_int32 (Wasm_int.Int32.iadd (N_to_i32 gmp_v) (nat_to_i32 8)))) = Some s_final
                 /\ INV fenv nenv s_final fr
                 /\ f_inst f = f_inst fr
                 /\ s_funcs s = s_funcs s_final
                 /\ min_available_memory s_final (f_inst f) mem
                 /\ rel_env_LambdaANF_Wasm (lenv:=lenv) cenv fenv nenv penv e (M.set x0 (Vprim (primInt n)) rho) s_final fr fds
                 /\ (forall (wal : wasm_value) (v : val),
                        repr_val_LambdaANF_Wasm cenv fenv nenv penv v s (f_inst f) wal -> repr_val_LambdaANF_Wasm cenv fenv nenv penv v s_final (f_inst fr) wal)
                 /\ (exists wal,
                        fr ={| f_locs := set_nth (VAL_num (VAL_int32 (wasm_value_to_i32 wal))) (f_locs f) (N.to_nat x0') (VAL_num (VAL_int32 (wasm_value_to_i32 wal)))
                            ; f_inst := f_inst f |}
                        /\ repr_val_LambdaANF_Wasm cenv fenv nenv penv (Vprim (primInt n)) s_final (f_inst fr) wal)). {
      intros.
      destruct (Htest (Z_to_i64 (to_Z n))) as [m' Hm'].
      remember (upd_s_mem s (set_nth m' s.(s_mems) 0 m')) as s'.
      exists s'.
      assert (Hm'': smem_store s (f_inst f) (Wasm_int.N_of_uint i32m (N_to_i32 gmp_v)) 0%N
                      (VAL_int64 (Z_to_i64 (to_Z n))) T_i64 = Some s'). {
        unfold smem_store. rewrite Hmem1. cbn. subst s'.
        unfold smem in Hmem2. rewrite Hmem1 in Hmem2. destruct (s_mems s)=>//.
        injection Hmem2 as ->. now rewrite Hm'. }
      assert (Hinv' : INV fenv nenv s' f). {
        subst.
        assert (mem_length m = mem_length m'). {
          apply store_length in Hm'. congruence. }
        assert (m.(meminst_type).(lim_max) = m'.(meminst_type).(lim_max)). {
          apply store_lim_max in Hm'. congruence. }
        eapply update_mem_preserves_INV; auto. apply Hinv. eassumption. erewrite <- H2. lia.
        congruence. exists (mem_size m); split; auto. unfold mem_size. congruence. }
      have I := Hinv'. destruct I as [_ [_ [_ [Hgmp_w' [_ [Hglob_mut [Hlinmem' [Hgmp' [_ [_ [_ [_ [_ [Hgmp_mult_two]]]]]]]]]]]]]].
      destruct Hlinmem' as [Hmem1' [m'' [Hmem2' [size' [Hmem3' [Hmem4' Hmem5']]]]]].
      destruct (Hgmp_w' (VAL_int32 (Wasm_int.Int32.iadd (N_to_i32 gmp_v) (nat_to_i32 8)))) as [s_final Hupd_glob].
      assert (smem s' (f_inst f) = Some m'). {
        subst s'. unfold smem, lookup_N. cbn.
        rewrite Hmem1'. apply set_nth_nth_error_same with (e:=m).
        unfold smem in Hmem2. rewrite Hmem1 in Hmem2.
        destruct (s_mems s)=>//. }
      assert (m' = m'') by congruence. subst m''.
      assert (HgmpBound': (gmp_v + 8 + 8 < mem_length m')%N). {
        assert (mem_length m = mem_length m') by
          now apply store_length in Hm'.
        replace (mem_length m') with (mem_length m).
        now unfold page_size in *. }
      remember {| f_locs := set_nth (VAL_num (N_to_value gmp_v)) (f_locs f) (N.to_nat x0') (VAL_num (N_to_value gmp_v))
               ; f_inst := f_inst f
               |} as fr.
      assert (Hinv'': INV fenv nenv s' fr). {
        now apply update_local_preserves_INV with (f:=f) (x':=N.to_nat x0') (v:=N_to_i32 gmp_v).
      }
      assert (Hsglobval_s':sglob_val s' (f_inst f) glob_mem_ptr = Some (VAL_num (VAL_int32 (N_to_i32 gmp_v)))) by
        now apply (update_memory_preserves_globals s f) with m'.
      assert (Hgmp_w'' : INV_glob_mem_ptr_writable s' f) by now destruct Hinv'.
      assert (Z.of_N (gmp_v + 8)%N < Wasm_int.Int32.modulus)%Z as HgmpModulus by now
          apply mem_length_upper_bound in Hmem5; simpl_modulus; cbn in Hmem5 |- *.
      assert (HfsEq: s_funcs s = s_funcs s') by now subst.
      assert (HfsEq': s_funcs s' = s_funcs s_final) by now apply update_global_preserves_funcs in Hupd_glob.
      assert (HfsEq'': s_funcs s = s_funcs s_final) by now subst.
      assert (HgmpBound'': (-1 < Z.of_N (gmp_v + 8) < Wasm_int.Int32.modulus)%Z). {
        apply mem_length_upper_bound in Hmem5. simpl_modulus_in Hmem5. cbn in Hmem5.
        simpl_modulus. cbn. lia.
      }

      assert (HenoughM'': (gmp_v + 52 < mem_length m')%N). {
        assert (mem_length m = mem_length m') by
          now apply store_length in Hm'.
        replace (mem_length m') with (mem_length m). lia. }

      assert (Hinv_final : INV fenv nenv s_final fr). {
        eapply update_global_preserves_INV with (sr:=s') (i:=glob_mem_ptr) (num:=(VAL_int32 (N_to_i32 (gmp_v + 8)))); eauto.
        left. split. apply gmp_i32_glob; auto. now cbn. discriminate.
        now subst fr.
        move => _. intros.
        destruct Hgmp_mult_two with (gmp_v:=gmp_v) (m:=m') as [n0' Hn0]. assumption.
        now subst s'.
        lia.
        destruct H4 as [Heqn0 Hboundn0].
        replace n0 with (gmp_v + 8)%N. lia.
        inv Heqn0.
        simpl_eq. lia.
        move => _. intros.
        destruct Hgmp_mult_two with (gmp_v:=gmp_v) (m:=m') as [n0' Hn0]. assumption.
        now subst s'.
        lia.
        destruct H4 as [Heqn0 Hboundn0].
        replace n0 with (gmp_v + 8)%N.
        exists (n0' + 4)%N; lia.
        inv Heqn0.
        simpl_eq. lia.
        unfold Wasm_int.Int32.iadd, Wasm_int.Int32.add in Hupd_glob.
        rewrite Heqfr. cbn in Hupd_glob |- *.
        rewrite Wasm_int.Int32.Z_mod_modulus_id in Hupd_glob; last lia.
        unfold N_to_i32.
        now replace (Z.of_N gmp_v + 8)%Z with (Z.of_N (gmp_v + 8))%Z in Hupd_glob by lia.
      }

      destruct (Hgmp_w' (VAL_int32 (Int32.repr (Z.of_N (gmp_v + 8)%N)))) as [sr' Hglob_sr'].

      assert (Hinv_sr' : INV fenv nenv sr' fr). {
        eapply update_global_preserves_INV with (sr:=s') (i:=glob_mem_ptr) (num:=(VAL_int32 (N_to_i32 (gmp_v+8)))); eauto.
        left. split. apply gmp_i32_glob; auto. reflexivity. discriminate.
        now subst fr.
        move => _.
        intros n0 [Heqn0 Hboundn0].
        replace n0 with (gmp_v + 8)%N. lia.
        inversion Heqn0.
        simpl_eq. lia.
        move => _.
        destruct Hgmp_mult_two with (gmp_v:=gmp_v) (m:=m') as [n0' Hn0]; auto.
        intros n0 [Heqn0 Hboundn0].
        replace n0 with (gmp_v + 8)%N.
        exists (n0' + 4)%N. lia.
        inversion Heqn0.
        simpl_eq. lia.
        now subst fr.
      }

      assert (Hrepr_val : repr_val_LambdaANF_Wasm cenv fenv nenv penv  (Vprim (primInt n)) sr' (f_inst fr) (Val_ptr gmp_v)). {
        apply Rprim_v with (gmp:=(gmp_v+8)%N) (m:=m'); auto.
        subst fr. eapply update_global_get_same. eassumption.
        lia.
        destruct Hgmp_mult_two with (gmp_v:=gmp_v) (m:=m') as [n0 Hn0].
        assumption. assumption. lia. exists n0. lia.
        replace (smem sr' (f_inst fr)) with (smem s' (f_inst fr)) by now subst fr; eapply update_global_preserves_memory.
        now subst fr.
        assert ((wasm_deserialise (serialise_num (VAL_int64 (Z_to_i64 (to_Z n)))) T_i64) = (VAL_int64 (Z_to_i64 (to_Z n)))) by now apply deserialise_serialise.
        rewrite -H4.
        apply (store_load_i64 m m' gmp_v (serialise_num (VAL_int64 (Z_to_i64 (to_Z n))))); auto.
        assert (Wasm_int.N_of_uint i32m (N_to_i32 gmp_v) = gmp_v). {
          cbn. rewrite Wasm_int.Int32.Z_mod_modulus_id; lia. }
        rewrite -H5.
        apply Hm'. }
      assert (HvalsPreserved : forall (wal : wasm_value) (v : val),
                 repr_val_LambdaANF_Wasm cenv fenv nenv penv v s (f_inst f) wal -> repr_val_LambdaANF_Wasm cenv fenv nenv penv v sr' (f_inst fr) wal). {
        intros.
        apply val_relation_depends_on_mem_smaller_than_gmp_and_funcs with (sr:=s) (m:=m) (m':=m') (gmp:=gmp_v) (gmp':=(gmp_v + 8)%N); auto.
        replace (s_funcs s) with (s_funcs s') by auto.
        now apply update_global_preserves_funcs in Hglob_sr'.
        now subst fr.
        replace (smem sr' (f_inst fr)) with (smem s' (f_inst fr)) by now subst fr; eapply update_global_preserves_memory.
        now subst fr.
        now subst fr.
        { simpl_modulus. cbn. simpl_modulus_in H1. cbn in H1. simpl_modulus_in HgmpBound.
          apply mem_length_upper_bound in Hmem5.
          unfold page_size, max_mem_pages in *. lia. }
        apply update_global_get_same with (sr:=s').
        now subst fr.
        { simpl_modulus. cbn.
          subst size'.
          apply mem_length_upper_bound in Hmem5'.
          unfold page_size, max_mem_pages in *.
          lia. }
        lia.
        { intros.
          assert (Hex: exists v, load_i32 m a = Some v). {
            apply enough_space_to_load. subst.
            simpl_modulus_in HenoughM'.
            apply store_length in Hm'. lia. }
          destruct Hex as [v' Hv'].
          rewrite Hv'.
          symmetry.
          apply (load_store_load_i32' m m' a (Wasm_int.N_of_uint i32m (N_to_i32 gmp_v)) v' (serialise_num (VAL_int64 (Z_to_i64 (to_Z n))))); auto.
          cbn. rewrite Wasm_int.Int32.Z_mod_modulus_id; lia. }
        { intros a Ha.
          assert (Hex: exists v, load_i64 m a = Some v). {
            apply enough_space_to_load_i64. lia. }
          destruct Hex as [v' Hv'].
          rewrite Hv'. symmetry.
          apply (load_store_load_i64' m m' a (Wasm_int.N_of_uint i32m (N_to_i32 gmp_v)) v' (serialise_num (VAL_int64 (Z_to_i64 (to_Z n))))); auto.
          cbn. rewrite Wasm_int.Int32.Z_mod_modulus_id; lia.
        }
        now subst fr. }
      assert (HrelE' : rel_env_LambdaANF_Wasm (lenv:=lenv) cenv fenv nenv penv e (M.set x0 (Vprim (primInt n)) rho) sr' fr fds). {
        have Hl := HlocsInBounds _ _ Hrepr_x.
        apply nth_error_Some in Hl.
        apply notNone_Some in Hl. destruct Hl as [? Hlx].
        unfold rel_env_LambdaANF_Wasm.
        destruct HrelE as [Hfun1 [Hfun2 Hvar]].
        split.
        { (* funs1 *)
          intros ????? Hrho Hv'.
          destruct (var_dec x0 x2).
          - (* x = x1 *)
            subst x2. rewrite M.gss in Hrho. inv Hrho.
            assert (~ subval_or_eq (Vfun rho' fds' f0) (Vprim (primInt n))).
            { now apply subval_or_eq_fun_not_prim. }
            contradiction.
          - (* x <> x1 *)
            now rewrite M.gso in Hrho; eauto.
        } split.
        { intros ? Hnfd. apply Hfun2 in Hnfd.
          destruct Hnfd as [i' [Htrans Hval]].
          exists i'. split. assumption.
          apply val_relation_func_depends_on_funcs with (s:=s); auto.
          replace (s_funcs s) with (s_funcs s') by auto.
          now apply update_global_preserves_funcs in Hglob_sr'.
          now subst fr.
        }
        intros. destruct (var_dec x0 x2).
        { (* x = x1 *)
          subst x2. exists (Vprim (primInt n)), (Val_ptr gmp_v).
          rewrite M.gss. split; auto.
          split.
          exists x0'. cbn. split. assumption.
          unfold lookup_N; cbn; auto.
          subst fr. cbn. erewrite set_nth_nth_error_same; eauto.
          now subst fr.
        }
        { (* x <> x1 *)
          assert (Hocc : occurs_free (Eprim x0 p [:: x ; y] e) x2)
              by now apply Free_Eprim2.
          have H' := Hvar _ Hocc H5.
          destruct H' as [val' [wal' [Hrho [Hloc Hval]]]].
          exists val', wal'. split.
          rewrite M.gso; auto. split.
          destruct Hloc as [i' [Hl1 Hl2]].
          unfold stored_in_locals. exists i'. split; auto.
          subst fr. unfold lookup_N.
          rewrite set_nth_nth_error_other; auto.

          intro. assert (x0' = i') by lia. subst x0'.
          have Hcontra := repr_var_inj _ _ _ _ HlenvInjective Hl1 Hrepr_x.
          contradiction.

          apply nth_error_Some. congruence.
          now apply HvalsPreserved.
        }
      }
      exists sr', fr, m', (Val_ptr gmp_v).
      try repeat (split; auto). all: subst fr; auto.
      assert (sglob_val s' (f_inst f) glob_mem_ptr =
                Some (VAL_num (VAL_int32 (N_to_i32 gmp_v)))) by now subst s'.
      separate_instr.
      dostep_nary 0. eapply r_global_get.
      eassumption.
      eapply rt_trans with (y:=(state, sr', f, ?[e1] ++ ?[e2])).
      eapply app_trans_const; auto.
      dostep_nary 0. apply r_global_get; eassumption.
      dostep_nary 2. constructor; apply rs_binop_success; reflexivity.
      cbn; unfold Wasm_int.Int32.iadd, Wasm_int.Int32.add; cbn.
      rewrite Wasm_int.Int32.Z_mod_modulus_id. 2: lia.
      dostep_nary 1. rewrite N2Z.inj_add in Hglob_sr'. eapply r_global_set'; eauto.
      cbn; apply rt_refl.
      cbn. dostep_nary' 1. eapply r_local_set' with (f':={|f_locs := set_nth (VAL_num (N_to_value gmp_v)) (f_locs f) (N.to_nat x0') (VAL_num (N_to_value gmp_v)); f_inst := f_inst f|}). reflexivity.
      apply /ssrnat.leP.
      apply HlocsInBounds in Hrepr_x. lia.
      reflexivity.
      now apply rt_refl.
      cbn; unfold Wasm_int.Int32.iadd, Wasm_int.Int32.add; cbn.
      rewrite Wasm_int.Int32.Z_mod_modulus_id; [|lia].
      unfold N_to_i32 in Hglob_sr'.
      replace 8%Z with (Z.of_N 8) by now cbn.
      rewrite -N2Z.inj_add.
      assumption.
      replace (s_funcs s) with (s_funcs s') by auto.
      now apply update_global_preserves_funcs in Hglob_sr'.

      (* minimum mem *)
      intros ?????.
      assert (m0 = m'). { apply update_global_preserves_memory in Hglob_sr'. now solve_eq m0 m'. }
      subst m0.
      assert (gmp = gmp_v + 8)%N. {
        apply update_global_get_same in Hglob_sr'.
        rewrite Hglob_sr' in H5.
        inv H5. now simpl_eq. } subst gmp.
      apply store_length in Hm'. lia.

      exists (Val_ptr gmp_v).
      split; auto. }

    assert (HunaryConstrValRelEnv: forall sr fr t ord p addr,
               v = Vconstr t [Vprim (AstCommon.primInt ; p)] ->
               get_ctor_arity cenv t = Ret 1 ->
               get_ctor_ord cenv t = Ret ord ->
               fr = {|f_locs := set_nth (VAL_num (VAL_int32 (wasm_value_to_i32 (Val_ptr (gmp_v + 8)%N)))) (f_locs f) (N.to_nat x0') (VAL_num (VAL_int32 (wasm_value_to_i32 (Val_ptr (gmp_v + 8)%N))));
                   f_inst := f_inst f|} ->
               repr_val_LambdaANF_Wasm cenv fenv nenv penv v sr (f_inst fr) (Val_ptr addr) ->
               s_funcs s = s_funcs sr ->
               nth_error (f_locs fr) (N.to_nat x0') = Some (VAL_num (VAL_int32 (wasm_value_to_i32 (Val_ptr addr)))) ->
               (Z.of_N ord < Wasm_int.Int32.half_modulus)%Z ->
               (forall (wal0 : wasm_value) (v0 : val),
                   repr_val_LambdaANF_Wasm cenv fenv nenv penv v0 s (f_inst f) wal0 -> repr_val_LambdaANF_Wasm cenv fenv nenv penv v0 sr (f_inst fr) wal0) ->
               rel_env_LambdaANF_Wasm (lenv:=lenv) cenv fenv nenv penv e (M.set x0 v rho) sr fr fds). {
      intros.
      subst fr.
      have Hl := HlocsInBounds _ _ Hrepr_x.
      apply nth_error_Some in Hl.
      apply notNone_Some in Hl. destruct Hl as [? Hlx].
      destruct HrelE as [Hfun1 [Hfun2 Hvar]].
      split. {
        intros ????? Hrho Hv'.
        destruct (var_dec x0 x2).
        - (* x0 = x1 *)
          (* v0 can never be a function value, by assumption on primops *)
          subst x2. rewrite M.gss in Hrho; eauto.
          inversion Hrho. subst v0.
          have H'' := Hnofunval rho' fds' f0.
          contradiction.
        - (* x0 <> x1 *)
          rewrite M.gso in Hrho; eauto.
      } split. {
        intros ? Hnfd. apply Hfun2 in Hnfd.
        destruct Hnfd as [i' [Htrans HvalFun]].
        exists i'. split. assumption.
        apply val_relation_func_depends_on_funcs with (s:=s); auto.
      }
      intros x2 Hx2free Hx2notfun.
      destruct (var_dec x0 x2).
      { (* x = x1 *)
        subst x2.
        exists v, (Val_ptr addr).
        rewrite M.gss. split; auto.
        split.
        exists x0'. cbn. split. assumption.
        unfold lookup_N; cbn; auto.
        assumption.
      }
      { (* x <> x1 *)
        assert (Hocc : occurs_free (Eprim x0 p [:: x ; y] e) x2)
            by now apply Free_Eprim2.
        have H' := Hvar _ Hocc Hx2notfun.
        destruct H' as [val' [wal' [Hrho [Hloc Hval']]]].
        exists val', wal'. split.
        rewrite M.gso; auto. split.
        destruct Hloc as [i' [Hl1 Hl2]].
        unfold stored_in_locals. exists i'. split; auto.
        unfold lookup_N.
        rewrite set_nth_nth_error_other; eauto.

        intro. assert (x0' = i') by lia. subst x0'.
        have Hcontra := repr_var_inj _ _ _ _ HlenvInjective Hl1 Hrepr_x.
        contradiction.

        now apply H11.
      } }

    (* TODO cleanup *)
    assert (forall t ord,
               v = Vconstr t [] ->
               get_ctor_arity cenv t = Ret 0 ->
               get_ctor_ord cenv t = Ret ord ->
               (Z.of_N ord < Wasm_int.Int32.half_modulus)%Z ->
               exists fr wal,
                 INV fenv nenv s fr
                 /\ fr = {| f_locs := set_nth (VAL_num (VAL_int32 (wasm_value_to_i32 wal))) (f_locs f) (N.to_nat x0') (VAL_num (VAL_int32 (wasm_value_to_i32 wal)))
                         ; f_inst := f_inst f
                         |}
                 /\ repr_val_LambdaANF_Wasm cenv fenv nenv penv v s (f_inst fr) wal
                 /\ rel_env_LambdaANF_Wasm (lenv:=lenv) cenv fenv nenv penv e (M.set x0 v rho) s fr fds
                 /\ (forall (wal0 : wasm_value) (v : val),
                        repr_val_LambdaANF_Wasm cenv fenv nenv penv v s (f_inst f) wal0 -> repr_val_LambdaANF_Wasm cenv fenv nenv penv v s (f_inst fr) wal0)
                 /\ reduce_trans (state, s, f,
                        [ (v_to_e (VAL_num (VAL_int32 (wasm_value_to_i32 wal))))
                          ; AI_basic (BI_local_set x0') ]) (state, s, fr, [::])). {
      intros.
      remember {| f_locs := set_nth (VAL_num (N_to_value (2 * ord + 1))) (f_locs f) (N.to_nat x0') (VAL_num (N_to_value (2 * ord + 1)))
               ; f_inst := f_inst f
               |} as fr.
      assert (Hinv' : INV fenv nenv s fr). {
        now apply update_local_preserves_INV with (f:=f) (x':=N.to_nat x0') (v:=(N_to_i32 (2 * ord + 1))). }

      assert (HvalsPreserved: forall (wal0 : wasm_value) (v0 : val),
               repr_val_LambdaANF_Wasm cenv fenv nenv penv v0 s (f_inst f) wal0 ->
               repr_val_LambdaANF_Wasm cenv fenv nenv penv v0 s (f_inst fr) wal0)
          by now subst fr.

      assert (HreprVal: repr_val_LambdaANF_Wasm cenv fenv nenv penv v s (f_inst fr) (Val_unboxed (2 * ord + 1)%N)). {
        rewrite H3.
        apply Rconstr_unboxed_v with (ord:=ord); auto.
        now rewrite N.mul_comm.
        simpl_modulus. simpl_modulus_in H6.
        cbn.
        destruct ord; lia.
      }

      assert (HrelE' : rel_env_LambdaANF_Wasm  (lenv:=lenv) cenv fenv nenv penv e (map_util.M.set x0 v rho) s fr fds). {
        have Hl := HlocsInBounds _ _ Hrepr_x.
        apply nth_error_Some in Hl.
        apply notNone_Some in Hl. destruct Hl as [? Hlx].

        destruct HrelE as [Hfun1 [Hfun2 Hvar]]. unfold rel_env_LambdaANF_Wasm.
        split.
        { intros. destruct (var_dec x0 x2).
          - subst x2. rewrite M.gss in H7. injection H7 as <-. subst v.
            apply subval_or_eq_fun in H8.
            destruct H8 as [v1 [Hr1 Hr2]]. now inv Hr2.
          - by rewrite M.gso in H7; eauto.
        }
        split.
        { intros ? Hnfd. apply Hfun2 in Hnfd.
          destruct Hnfd as [i [Htrans Hval]].
          exists i. split. assumption. now subst fr.
        }
        intros. destruct (var_dec x0 x2).
        { (* x0 = x2 *)
          subst x2.
          assert ( (Wasm_int.Int32.half_modulus < Wasm_int.Int32.modulus)%Z )
              by now rewrite Wasm_int.Int32.half_modulus_modulus.
          exists (Vconstr t []), (Val_unboxed (2 * ord + 1)%N).
          rewrite M.gss. split. congruence.
          split.
          - unfold stored_in_locals. exists x0'.
            split. assumption.
            subst fr.
            unfold lookup_N, nat_to_value, nat_to_i32, wasm_value_to_i32.
            simpl. now erewrite set_nth_nth_error_same; eauto.
          - econstructor; eauto; try lia.
            now inv HreprVal.
        }
        { (* x0 <> x2 *)
          assert (Hocc: occurs_free (Eprim x0 p [:: x; y] e) x2). { now apply Free_Eprim2. }
          have H' := Hvar _ Hocc H8.
          destruct H' as [val' [wal' [Hrho [Hloc Hval]]]].
          exists val', wal'.
          split. rewrite M.gso; auto.
          split. 2: now subst fr.
          destruct Hloc as [i [Hl1 Hl2]].
          unfold stored_in_locals. exists i. split; auto.
          subst fr.
          unfold lookup_N.
          rewrite set_nth_nth_error_other; auto.

          intro. assert (x0' = i) by lia. subst x0'.
          have Hcontra := repr_var_inj _ _ _ _ HlenvInjective Hl1 Hrepr_x.
          contradiction.

          apply nth_error_Some. congruence.
        }
      }
      exists fr, (Val_unboxed (2 * ord + 1)%N).
      try repeat (split; auto).
      subst fr.
      apply rt_step. eapply r_local_set. reflexivity.
      apply /ssrnat.leP.
      apply HlocsInBounds in Hrepr_x. lia.
      reflexivity. }

    assert (exists n1 n2,
               rho ! x = Some (Vprim (primInt n1))
               /\ rho ! y = Some (Vprim (primInt n2))
               /\ vs = [ Vprim (primInt n1) ; Vprim (primInt n2) ]
           ). {
      clear H3 H2.
      destruct Hpfs' as  [? [? [? [? [? [? [? [? [? [? [? [? [Hres _]]]]]]]]]]]]].
      unfold get_list in *.
      destruct (rho ! x) eqn:Hrho_x. 2: discriminate.
      destruct (rho ! y) eqn:Hrho_y. 2: discriminate.
      assert (List.In v0 vs) by (inv Hys_vs; now constructor).
      assert (List.In v1 vs) by (inv Hys_vs; right; now constructor).
      destruct (apply_primop_only_defined_on_primInts _ vs v _ _ _ _ _ _ _ _ Hres v0 H2) as [n1 Hn1].
      destruct (apply_primop_only_defined_on_primInts _ vs v _ _ _ _ _ _ _ _ Hres v1 H3) as [n2 Hn2].
      exists n1, n2.
      split; subst; auto.
      split; subst; auto.
      congruence. }
    destruct H4 as [n1 [n2 [Hrho_x [Hrho_y Hvs]]]].
    assert (exists wal1,
               stored_in_locals (lenv:=lenv) nenv x wal1 f /\ repr_val_LambdaANF_Wasm cenv fenv nenv penv (Vprim ( primInt n1)) s (f_inst f) wal1). {
      destruct HrelE as [_ [_ Hvars]].
      assert (occurs_free (Eprim x0 p [:: x ; y ] e) x) by now (constructor; constructor).
      assert (HfdsNone_x: find_def x fds = None). {
        inv H.
        unfold translate_var in H5.
        destruct (lenv ! x) eqn:Hx. 2: now rewrite Hx in H5.
        unfold domains_disjoint in Hdisjoint.
        apply Hdisjoint in Hx.
        apply HfenvWf_None with (f:=x) in HfenvWf. now rewrite HfenvWf.
      }
      have Hx := Hvars _ H4 HfdsNone_x. destruct Hx as [v1' [w1 [Hrho_x' [Hloc_x Hval_x]]]].
      exists w1; split; auto.
      now replace v1' with (Vprim (primInt n1)) in Hval_x by now rewrite Hrho_x in Hrho_x'; inv Hrho_x'.
    }
    destruct H4 as [wal1 [Hloc_x Hval_x]].
    assert (exists wal2,
               stored_in_locals (lenv:=lenv) nenv y wal2 f
            /\ repr_val_LambdaANF_Wasm cenv fenv nenv penv (Vprim (primInt n2)) s (f_inst f) wal2). {
      destruct HrelE as [_ [_ Hvars]].
      assert (occurs_free (Eprim x0 p [:: x ; y ] e) y) by now (constructor; right; constructor).
      assert (HfdsNone_y: find_def y fds = None). {
        inv H0.
        unfold translate_var in H5.
        destruct (lenv ! y) eqn:Hy. 2: now rewrite Hy in H5.
        unfold domains_disjoint in Hdisjoint.
        apply Hdisjoint in Hy.
        apply HfenvWf_None with (f:=y) in HfenvWf. now rewrite HfenvWf.
      }
      have Hy := Hvars _ H4 HfdsNone_y. destruct Hy as [v2' [w2 [Hrho_y' [Hloc_y Hval_y]]]].
      exists w2; split; auto.
      now replace v2' with (Vprim (primInt n2)) in Hval_y by now rewrite Hrho_y in Hrho_y'; inv Hrho_y'.
    }
    destruct H4 as [wal2 [Hloc_y Hval_y]].
    destruct Hloc_x as [? [Htrans Hx']].
    assert (x1 = x'). { eapply repr_var_det; eassumption. } subst x1. clear Htrans.
    destruct Hloc_y as [? [Htrans Hy']].
    assert (x1 = y'). { eapply repr_var_det; eassumption. } subst x1. clear Htrans.
    assert (Hrv1: exists addr1, wal1 = Val_ptr addr1
               /\ load_i64 m addr1 = Some (VAL_int64 (Z_to_i64 (to_Z n1)))). {
      inv Hval_x. replace m with m0 by congruence. exists addr. split; auto.
      remember (primInt n) as p1; remember (primInt n1) as p2.
      inversion H10; subst p1 p2.
      now replace n1 with n by now apply Classical_Prop.EqdepTheory.inj_pair2 in H12.
    }
    destruct Hrv1 as [addr1 Hload1].
    destruct Hload1 as [? Hload1]. subst wal1.
    unfold load_i64 in Hload1. destruct (load m addr1 0%N 8) eqn:Hload1'. 2: discriminate.
    assert (Haddr1: addr1 = (Wasm_int.N_of_uint i32m (wasm_value_to_i32 (Val_ptr addr1)))). {
      cbn. rewrite Wasm_int.Int32.Z_mod_modulus_id. now rewrite N2Z.id.
      inv Hval_x. lia. }
    assert (Hrv2: exists addr2, wal2 = Val_ptr addr2
               /\ load_i64 m addr2 = Some (VAL_int64 (Z_to_i64 (to_Z n2)))). {
      inv Hval_y. replace m with m0 by congruence. exists addr. split; auto.
      remember (primInt n) as p1; remember (primInt n2) as p2.
      inversion H10; subst p1 p2.
      now replace n2 with n by now apply Classical_Prop.EqdepTheory.inj_pair2 in H12.
    }
    destruct Hrv2 as [addr2 Hload2].
    destruct Hload2 as [? Hload2]. subst wal2.
    unfold load_i64 in Hload2. destruct (load m addr2 0%N 8) eqn:Hload2'. 2: discriminate.
    assert (addr2 = (Wasm_int.N_of_uint i32m (wasm_value_to_i32 (Val_ptr addr2)))). {
      cbn. rewrite Wasm_int.Int32.Z_mod_modulus_id. now rewrite N2Z.id.
      inv Hval_y. lia. }
    assert (HloadStep1: forall es,
               reduce_trans
                 (state, s, f, ([:: AI_basic (BI_local_get x')] ++
                                [:: AI_basic (BI_load T_i64 None {| memarg_offset:=0%N; memarg_align:=2%N |})] ++
                                es))
                 (state, s, f, ([:: $V VAL_num (VAL_int64 (Z_to_i64 (to_Z n1))) ] ++ es))). {
      intros.
      dostep_nary 0. apply r_local_get. eassumption.
      dostep_nary 1. eapply r_load_success; try eassumption.
      rewrite -Haddr1. apply Hload1'.
      replace (wasm_deserialise b0 T_i64) with (VAL_int64 (Z_to_i64 (to_Z n1))) by congruence.
      now apply rt_refl. }
    assert (HloadStep2: forall es,
               reduce_trans
                 (state, s, f, ([:: AI_basic (BI_local_get y')] ++
                                [:: AI_basic (BI_load T_i64 None {| memarg_offset:=0%N; memarg_align:=2%N |})] ++
                                es))
                 (state, s, f, ([:: $V VAL_num (VAL_int64 (Z_to_i64 (to_Z n2))) ] ++ es))). {
      intros.
      dostep_nary 0. apply r_local_get. eassumption.
      dostep_nary 1. eapply r_load_success; try eassumption. rewrite -H4. apply Hload2'.
      replace (wasm_deserialise b1 T_i64) with (VAL_int64 (Z_to_i64 (to_Z n2))) by congruence.
      now apply rt_refl. }
    assert (HloadStep': forall es,
               reduce_trans
                 (state, s, f, ([:: AI_basic (BI_local_get x')] ++
                                [:: AI_basic (BI_load T_i64 None {| memarg_offset:=0%N; memarg_align:=2%N |})] ++
                                [:: AI_basic (BI_local_get y')] ++
                                [:: AI_basic (BI_load T_i64 None {| memarg_offset:=0%N; memarg_align:=2%N |})] ++
                                es))
                 (state, s, f, ([:: $V VAL_num (VAL_int64 (Z_to_i64 (to_Z n1))) ; $V VAL_num (VAL_int64 (Z_to_i64 (to_Z n2))) ] ++ es))). {
      intros.
      eapply rt_trans.
      apply HloadStep1.
      eapply rt_trans.
      apply app_trans_const; auto.
      now apply rt_refl.
    }
    destruct Hpfs' as
      [true_tag [false_tag [bool_tag [eq_tag [lt_tag [gt_tag [comp_tag [c0_tag [c1_tag [carry_tag [pair_tag [prod_tag [Hres [Htrue [Hfalse [Heq [Hlt [Hgt [Hc0 [Hc1 Hpair]]]]]]]]]]]]]]]]]]]].
    assert (Htrue_arr: get_ctor_arity cenv true_tag = Ret 0) by now unfold get_ctor_arity; rewrite Htrue.
    assert (Htrue_ord: get_ctor_ord cenv true_tag = Ret 1%N) by now unfold get_ctor_ord; rewrite Htrue.
    assert (Hfalse_arr: get_ctor_arity cenv false_tag = Ret 0) by now unfold get_ctor_arity; rewrite Hfalse.
    assert (Hfalse_ord: get_ctor_ord cenv false_tag = Ret 0%N) by now unfold get_ctor_ord; rewrite Hfalse.

    (* TODO: Added for carry ops, remove/ clean up when moving/ refactoring *)
    assert (Hflocs: N.to_nat x0' < Datatypes.length (f_locs f)) by now eapply HlocsInBounds; eauto.
    rewrite Haddr1 in Hload1'.
    rewrite H4 in Hload2'.
    replace 8 with (N.to_nat (tnum_length T_i64)) in Hload1', Hload2' by now cbn.
    assert (Hbsx : wasm_deserialise b0 T_i64 = Z_to_VAL_i64 φ (n1)%uint63) by congruence.
    assert (Hbsy : wasm_deserialise b1 T_i64 = Z_to_VAL_i64 φ (n2)%uint63) by congruence.
    assert (HgmpBounds: (Z.of_N gmp_v + Z.of_N 52 <= Z.of_N (mem_length m) < Int32.modulus)%Z). {
      apply mem_length_upper_bound in Hmem5. cbn in Hmem5.
      simpl_modulus. cbn. cbn in HenoughM. lia. }
    remember {|f_locs := set_nth (VAL_num (VAL_int32 (wasm_value_to_i32 (Val_ptr (gmp_v + 8)%N)))) (f_locs f) (N.to_nat x0') (VAL_num (VAL_int32 (wasm_value_to_i32 (Val_ptr (gmp_v + 8)%N))));
               f_inst := f_inst f|} as fr_carry_ops.

    assert (local_holds_address_to_i64 s f x' (N_to_i32 addr1) (Z_to_i64 φ (n1)%uint63) m b0) as Hlocalx.
    by unfold local_holds_address_to_i64; auto.
    assert (local_holds_address_to_i64 s f y' (N_to_i32 addr2) (Z_to_i64 φ (n2)%uint63) m b1) as Hlocaly.
    by unfold local_holds_address_to_i64; auto.

    rewrite Hvs in Hres.
    unfold apply_LambdaANF_primInt_operator in Hres.
    destruct op;
    ltac:(match goal with | [ H : None = Some _  |- _ ] => discriminate | _ => idtac end);
    unfold LambdaANF_primInt_arith_fun in Hres.
    (* TODO cleanup *)
    - (* add *)
      inversion H1. remember (apply_binop_and_store_i64 glob_mem_ptr BOI_add x' y' true) as instrs'.
      destruct (H2 (Uint63.add n1 n2)) as [s' [s_final [fr [m' [wal [Hwal [Hs' [Hstore [Hfr [Hsmem [Hstep [Hinv1 [Hupd_glob Hr]]]]]]]]]]]]].
      exists s_final, fr.
      replace v with (Vprim (AstCommon.primInt ; (Uint63.add n1 n2))) in * by congruence.
      split; auto. rewrite Heqinstrs' Hfr Hwal.
      apply (simple_arith_binop_reduce state s s' _ f gmp_v m m' x' y' (N_to_i32 addr1) (N_to_i32 addr2) b0 b1 n1 n2 BOI_add Uint63.add true (Int64.iadd (Int64.repr (to_Z n1)) (Int64.repr (to_Z n2))) x0'); auto.
      intro. rewrite uint63_add_i64_add. reflexivity.
      intro; discriminate.
    - (* sub *)
      inversion H1. remember (apply_binop_and_store_i64 glob_mem_ptr BOI_sub x' y' true) as instrs'.
      destruct (H2 (Uint63.sub n1 n2)) as [s' [s_final [fr [m' [wal [Hwal [Hs' [Hstore [Hfr [Hsmem [Hstep [Hinv1 [Hupd_glob Hr]]]]]]]]]]]]].
      exists s_final, fr.
      replace v with (Vprim (AstCommon.primInt ; (Uint63.sub n1 n2))) in * by congruence.
      split; auto. rewrite Heqinstrs' Hfr Hwal.
      apply (simple_arith_binop_reduce state s s' _ f gmp_v m m' x' y' (N_to_i32 addr1) (N_to_i32 addr2) b0 b1 n1 n2 BOI_sub Uint63.sub true (Int64.isub (Int64.repr (to_Z n1)) (Int64.repr (to_Z n2))) x0'); auto.
      intro. rewrite uint63_sub_i64_sub. reflexivity.
      intro; discriminate.
    - (* mul *)
      inversion H1. remember (apply_binop_and_store_i64 glob_mem_ptr BOI_mul x' y' true) as instrs'.
      destruct (H2 (Uint63.mul n1 n2)) as [s' [s_final [fr [m' [wal [Hwal [Hs' [Hstore [Hfr [Hsmem [Hstep [Hinv1 [Hupd_glob Hr]]]]]]]]]]]]].
      exists s_final, fr.
      replace v with (Vprim (AstCommon.primInt ; (Uint63.mul n1 n2))) in * by congruence.
      split; auto. rewrite Heqinstrs' Hfr Hwal.
      apply (simple_arith_binop_reduce state s s' _ f gmp_v m m' x' y' (N_to_i32 addr1) (N_to_i32 addr2) b0 b1 n1 n2 BOI_mul Uint63.mul true (Int64.imul (Int64.repr (to_Z n1)) (Int64.repr (to_Z n2))) x0'); auto.
      intro. rewrite uint63_mul_i64_mul. reflexivity.
      intro; discriminate.
    - { (* div *)
      inv H1; simpl.
      destruct (H2 (n1 / n2)%uint63) as [s' [s_final [fr [m' [wal [Hwal [Hs' [Hstore [Hfr [Hsmem [Hstep [Hinv1 [Hupd_glob Hr]]]]]]]]]]]]].
      replace v with (Vprim (primInt (n1 / n2)%uint63)) in * by congruence.
      exists s_final, fr.
      split; auto.
      dostep_nary 0. eapply r_global_get; eassumption.
      eapply rt_trans.
      apply app_trans_const; auto.
      destruct (Z.eq_dec (to_Z n2) (to_Z 0)).
      { (* n2 = 0 *)
        dostep_nary_eliml 1 1. constructor; apply rs_testop_i64.
        dostep_nary_eliml 1 1. constructor; apply rs_if_true; unfold wasm_bool.
        replace Wasm_int.Int64.zero with (Z_to_i64 (to_Z 0)) by now rewrite to_Z_0.
        rewrite uint63_eq_int64_eq. discriminate. now rewrite e0.
        dostep_nary_eliml 0 1. eapply r_block with (t1s:=[::]) (t2s:=[:: T_num T_i64])(vs:=[::]); auto.
        dostep_nary_eliml 0 1. constructor; apply rs_label_const; auto.
        dostep_nary 2. eapply r_store_success.
        rewrite uint63_div0 in Hstore; auto.
        eassumption.
        now apply Hstep. }
      { (* n2 <> 0 *)
        dostep_nary_eliml 1 1. constructor; apply rs_testop_i64.
        dostep_nary_eliml 1 1. constructor; apply rs_if_false; unfold wasm_bool; auto.
        replace Wasm_int.Int64.zero with (Z_to_i64 (to_Z 0)) by now rewrite to_Z_0.
        rewrite uint63_neq_int64_neq; auto.
        dostep_nary_eliml 0 1. eapply r_block with (t1s:=[::]) (t2s:=[:: T_num T_i64])(vs:=[::]); auto.
        rewrite catA.
        reduce_under_label.
        apply HloadStep'.
        reduce_under_label.
        apply rt_step. constructor. apply rs_binop_success; first done. simpl.
        rewrite uint63_div_i64_div; simpl; auto.
        dostep_nary_eliml 0 1. constructor; apply rs_label_const; auto.
        dostep_nary 2. eapply r_store_success.
        eassumption.
        eassumption. } }
    - { (* mod *)
      inv H1; simpl.
      destruct (H2 (n1 mod n2)%uint63) as [s' [s_final [fr [m' [wal [Hwal [Hs' [Hstore [Hfr [Hsmem [Hstep [Hinv1 [Hupd_glob Hr]]]]]]]]]]]]].
      replace v with (Vprim (primInt (n1 mod n2)%uint63)) in * by congruence.
      exists s_final, fr.
      split; auto.
      dostep_nary 0. eapply r_global_get; eassumption.
      eapply rt_trans.
      apply app_trans_const; auto.
      destruct (Z.eq_dec (to_Z n2) (to_Z 0)).
      { (* n2 = 0 *)
        dostep_nary_eliml 1 1. constructor; apply rs_testop_i64.
        dostep_nary_eliml 1 1. constructor; apply rs_if_true; unfold wasm_bool.
        replace Wasm_int.Int64.zero with (Z_to_i64 (to_Z 0)) by now rewrite to_Z_0.
        rewrite uint63_eq_int64_eq. discriminate. now rewrite e0.
        dostep_nary_eliml 0 1. eapply r_block with (t1s:=[::]) (t2s:=[:: T_num T_i64])(vs:=[::]); auto.
        rewrite catA.
        reduce_under_label.
        apply HloadStep1.
        dostep_nary_eliml 0 1. constructor. apply rs_label_const; auto.
        dostep_nary 2. eapply r_store_success.
        rewrite uint63_mod0 in Hstore; eauto.
        eassumption. }
      { (* n2 <> 0 *)
        dostep_nary_eliml 1 1. constructor; apply rs_testop_i64.
        dostep_nary_eliml 1 1. constructor; apply rs_if_false; unfold wasm_bool; auto.
        replace Wasm_int.Int64.zero with (Z_to_i64 (to_Z 0)) by now rewrite to_Z_0.
        rewrite uint63_neq_int64_neq; auto.
        dostep_nary_eliml 0 1. eapply r_block with (t1s:=[::]) (t2s:=[:: T_num T_i64])(vs:=[::]); auto.
        rewrite catA.
        reduce_under_label.
        apply HloadStep'.
        reduce_under_label.
        apply rt_step. constructor. apply rs_binop_success; first done.
          cbn. now rewrite uint63_mod_i64_mod.
        dostep_nary_eliml 0 1. constructor. now apply rs_label_const.
        dostep_nary 2. eapply r_store_success.
        eassumption.
        eassumption. } }
    (* TODO: Factor out helper lemma for shifts *)
    - { (* lsl *)
        inv H1; simpl.
        destruct (H2 (n1 << n2)%uint63) as [s' [s_final [fr [m' [wal [Hwal [Hs' [Hstore [Hfr [Hsmem [Hstep [Hinv1 [Hupd_glob Hr]]]]]]]]]]]]].
        replace v with (Vprim (primInt (n1 << n2)%uint63)) in * by congruence.
        exists s_final, fr.
        split; auto.
        dostep_nary 0. eapply r_global_get; eassumption.
        eapply rt_trans.
        apply app_trans_const; auto.
        destruct (Z_lt_dec (to_Z n2) (to_Z 63)).
        { (* n2 < 63 *)
          dostep_nary_eliml 2 1. constructor. apply rs_relop=>//.
          dostep_nary_eliml 1 1. constructor; apply rs_if_true; unfold wasm_bool.
          replace (Z_to_i64 63) with (Z_to_i64 (to_Z 63)) by now cbn.
          rewrite uint63_lt_int64_lt; auto. discriminate.
          dostep_nary_eliml 0 1. eapply r_block with (t1s:=[::]) (t2s:=[:: T_num T_i64])(vs:=[::]); auto.
          rewrite catA.
          reduce_under_label.
          apply HloadStep'.
          reduce_under_label.
          dostep_nary 2; constructor; apply rs_binop_success; reflexivity.
          reduce_under_label.
          apply rt_step. constructor; apply rs_binop_success; reflexivity. cbn.
          rewrite uint63_lsl_i64_shl; simpl; auto.
          dostep_nary_eliml 0 1. constructor. apply rs_label_const; auto.
          dostep_nary 2. eapply r_store_success.
          eassumption.
          eassumption. }
        { (* n2 <= 63 *)
          dostep_nary_eliml 2 1. constructor. apply rs_relop=>//.
          dostep_nary_eliml 1 1. constructor; apply rs_if_false; unfold wasm_bool.
          replace (Z_to_i64 63) with (Z_to_i64 (to_Z 63)) by now cbn.
          rewrite uint63_nlt_int64_nlt; auto.
          dostep_nary_eliml 0 1. eapply r_block with (t1s:=[::]) (t2s:=[:: T_num T_i64])(vs:=[::]); auto.
          dostep_nary_eliml 0 1. constructor; apply rs_label_const; auto.
          dostep_nary 2. eapply r_store_success.
          assert (to_Z 63 <= to_Z n2)%Z as Hle by now destruct (Z.lt_ge_cases (to_Z n2) (to_Z 63)).
          rewrite (uint63_lsl63 _ _ Hle) in Hstore; eauto.
          eassumption. } }
    - { (* lsr *)
        inv H1; simpl.
        destruct (H2 (n1 >> n2)%uint63) as [s' [s_final [fr [m' [wal [Hwal [Hs' [Hstore [Hfr [Hsmem [Hstep [Hinv1 [Hupd_glob Hr]]]]]]]]]]]]].
        replace v with (Vprim (primInt (n1 >> n2)%uint63)) in * by congruence.
        exists s_final, fr.
        split; auto.
        dostep_nary 0. eapply r_global_get; eassumption.
        eapply rt_trans.
        apply app_trans_const; auto.
        destruct (Z_lt_dec (to_Z n2) (to_Z 63)).
        { (* n2 < 63 *)
          dostep_nary_eliml 2 1. constructor. apply rs_relop=>//.
          dostep_nary_eliml 1 1. constructor; apply rs_if_true; unfold wasm_bool.
          replace (Z_to_i64 63) with (Z_to_i64 (to_Z 63)) by now cbn.
          rewrite uint63_lt_int64_lt; auto. discriminate.
          dostep_nary_eliml 0 1. eapply r_block with (t1s:=[::]) (t2s:=[:: T_num T_i64])(vs:=[::]); auto.
          rewrite catA.
          reduce_under_label.
          apply HloadStep'.
          reduce_under_label.
          apply rt_step. constructor; apply rs_binop_success; first done. simpl.
          rewrite uint63_lsr_i64_shr; simpl; auto.
          dostep_nary_eliml 0 1. constructor; apply rs_label_const; auto.
          dostep_nary 2. eapply r_store_success.
          eassumption.
          eassumption. }
        { (* n2 <= 63 *)
          dostep_nary_eliml 2 1. constructor; apply rs_relop; first done.
          dostep_nary_eliml 1 1. constructor; apply rs_if_false; unfold wasm_bool.
          replace (Z_to_i64 63) with (Z_to_i64 (to_Z 63)) by now cbn.
          rewrite uint63_nlt_int64_nlt; auto.
          dostep_nary_eliml 0 1. eapply r_block with (t1s:=[::]) (t2s:=[:: T_num T_i64])(vs:=[::]); auto.
          dostep_nary_eliml 0 1. constructor; apply rs_label_const; auto.
          dostep_nary 2. eapply r_store_success.
          assert (to_Z 63 <= to_Z n2)%Z as Hle by now destruct (Z.lt_ge_cases (to_Z n2) (to_Z 63)).
          rewrite (uint63_lsr63 _ _ Hle) in Hstore; eauto.
          eassumption. } }
    - (* land *)
      inversion H1. remember (apply_binop_and_store_i64 glob_mem_ptr BOI_and x' y' false) as instrs'.
      destruct (H2 (Uint63.land n1 n2)) as [s' [s_final [fr [m' [wal [Hwal [Hs' [Hstore [Hfr [Hsmem [Hstep [Hinv1 [Hupd_glob Hr]]]]]]]]]]]]].
      exists s_final, fr.
      replace v with (Vprim (AstCommon.primInt ; (Uint63.land n1 n2))) in * by congruence.
      split; auto. rewrite Heqinstrs' Hfr Hwal.
      apply (simple_arith_binop_reduce state s s' _ f gmp_v m m' x' y' (N_to_i32 addr1) (N_to_i32 addr2) b0 b1 n1 n2 BOI_and Uint63.land false (Int64.iand (Int64.repr (to_Z n1)) (Int64.repr (to_Z n2))) x0'); auto.
      intro; discriminate.
      intro. rewrite uint63_land_i64_and. reflexivity.
    - (* lor *)
      inversion H1. remember (apply_binop_and_store_i64 glob_mem_ptr BOI_or x' y' false) as instrs'.
      destruct (H2 (Uint63.lor n1 n2)) as [s' [s_final [fr [m' [wal [Hwal [Hs' [Hstore [Hfr [Hsmem [Hstep [Hinv1 [Hupd_glob Hr]]]]]]]]]]]]].
      exists s_final, fr.
      replace v with (Vprim (AstCommon.primInt ; (Uint63.lor n1 n2))) in * by congruence.
      split; auto. rewrite Heqinstrs' Hfr Hwal.
      apply (simple_arith_binop_reduce state s s' _ f gmp_v m m' x' y' (N_to_i32 addr1) (N_to_i32 addr2) b0 b1 n1 n2 BOI_or Uint63.lor false (Int64.ior (Int64.repr (to_Z n1)) (Int64.repr (to_Z n2))) x0'); auto.
      intro; discriminate.
      intro. rewrite uint63_lor_i64_or. reflexivity.
    - (* lxor *)
      inversion H1. remember (apply_binop_and_store_i64 glob_mem_ptr BOI_xor x' y' false) as instrs'.
      destruct (H2 (Uint63.lxor n1 n2)) as [s' [s_final [fr [m' [wal [Hwal [Hs' [Hstore [Hfr [Hsmem [Hstep [Hinv1 [Hupd_glob Hr]]]]]]]]]]]]].
      exists s_final, fr.
      replace v with (Vprim (AstCommon.primInt ; (Uint63.lxor n1 n2))) in * by congruence.
      split; auto. rewrite Heqinstrs' Hfr Hwal.
      apply (simple_arith_binop_reduce state s s' _ f gmp_v m m' x' y' (N_to_i32 addr1) (N_to_i32 addr2) b0 b1 n1 n2 BOI_xor Uint63.lxor false (Int64.ixor (Int64.repr (to_Z n1)) (Int64.repr (to_Z n2))) x0'); auto.
      intro; discriminate.
      intro. rewrite uint63_lxor_i64_xor. reflexivity.
    (* TODO: Factor out helper lemma for booleans *)
    - { (* eqb *)
        inv H1; simpl.
        destruct (Z.eq_dec (to_Z n1) (to_Z n2)).
        { (* n1 = n2 *)
          assert (Hv_true: v = Vconstr true_tag []) by now unfold LambdaANF_primInt_bool_fun in Hres; rewrite (reflect_iff _ _ (Uint63.eqbP n1 n2)) in e0; rewrite e0 in Hres.
          destruct (H3 _ _ Hv_true Htrue_arr Htrue_ord) as [fr [wal [Hinv' [Hfr [HreprVal [HrelE' [HvalsPreserved Hstep]]]]]]].
          simpl_modulus; simpl_modulus; cbn; lia.
          exists s, fr.
          split. {
            separate_instr.
            eapply rt_trans.
            apply HloadStep'.
            dostep_nary 2. constructor. apply rs_relop=>//.
            dostep_nary 1. constructor. apply rs_if_true.
            rewrite uint63_eq_int64_eq; [discriminate|now rewrite e0].
            dostep_nary 0. eapply r_block with (t1s:=[::]) (t2s:=[:: T_num T_i32])(vs:=[::]); eauto.
            dostep_nary 0. constructor; apply rs_label_const; auto.
            replace [:: $VN VAL_int32 (Wasm_int.Int32.repr 3)] with [:: $V VAL_num (VAL_int32 (wasm_value_to_i32 wal))]; auto.
            inv HreprVal; try discriminate.
            - now replace ord with 1%N by congruence.
            - replace t with true_tag in * by congruence. rewrite Htrue_arr in H7; inv H7; lia.
          }
          try repeat (split; auto). all: subst fr; auto.

          (* minimum mem *)
          intros ?????.
          solve_eq m m0.
          solve_eq gmp gmp_v. lia.

          exists wal; auto. }
        { (* n1 <> n2 *)
          assert (Hv_false: v = Vconstr false_tag []) by now unfold LambdaANF_primInt_bool_fun in Hres; rewrite (to_Z_neq_uint63_eqb_false _ _ n) in Hres.
          destruct (H3 _ _ Hv_false Hfalse_arr Hfalse_ord) as [fr [wal [Hinv' [Hfr [HreprVal [HrelE' [HvalsPreserved Hstep]]]]]]].
          simpl_modulus; simpl_modulus; cbn; lia.
          exists s, fr.
          split. {
            separate_instr.
            eapply rt_trans.
            apply HloadStep'.
            dostep_nary 2. constructor. apply rs_relop=>//.
            dostep_nary 1. constructor. apply rs_if_false.
            rewrite uint63_neq_int64_neq; [reflexivity|assumption].
            dostep_nary 0. eapply r_block with (t1s:=[::]) (t2s:=[:: T_num T_i32])(vs:=[::]); eauto.
            dostep_nary 0. constructor; apply rs_label_const; auto.
            replace [:: $VN VAL_int32 (Wasm_int.Int32.repr 1)] with [:: $V VAL_num (VAL_int32 (wasm_value_to_i32 wal))]; auto.
            inv HreprVal; try discriminate.
            - now replace ord with 0%N by congruence.
            - replace t with false_tag in * by congruence. rewrite Hfalse_arr in H7; inv H7; lia.
          }
          try repeat (split; auto). all: subst fr; auto.

          (* minimum mem *)
          intros ?????.
          solve_eq m m0.
          solve_eq gmp gmp_v. lia.

          exists wal; auto. } }
    - { (* ltb *)
        inv H1; simpl.
        destruct (Z_lt_dec (to_Z n1) (to_Z n2)).
        { (* n1 < n2 *)
          assert (Hv_true: v = Vconstr true_tag []) by now unfold LambdaANF_primInt_bool_fun in Hres; rewrite (reflect_iff _ _ (Uint63.ltbP n1 n2)) in l; rewrite l in Hres.
          destruct (H3 _ _ Hv_true Htrue_arr Htrue_ord) as [fr [wal [Hinv' [Hfr [HreprVal [HrelE' [HvalsPreserved Hstep]]]]]]].
          simpl_modulus; simpl_modulus; cbn; lia.
          exists s, fr.
          split. {
            separate_instr.
            eapply rt_trans.
            apply HloadStep'.
            dostep_nary 2. constructor. apply rs_relop=>//.
            dostep_nary 1. constructor. apply rs_if_true.
            rewrite uint63_lt_int64_lt; [discriminate|assumption].
            dostep_nary 0. eapply r_block with (t1s:=[::]) (t2s:=[:: T_num T_i32])(vs:=[::]); eauto.
            dostep_nary 0. constructor; apply rs_label_const; auto.
            replace [:: $VN VAL_int32 (Wasm_int.Int32.repr 3)] with [:: $V VAL_num (VAL_int32 (wasm_value_to_i32 wal))]; auto.
            inv HreprVal; try discriminate.
            - now replace ord with 1%N by congruence.
            - replace t with true_tag in * by congruence. rewrite Htrue_arr in H7; inv H7; lia.
          }
          try repeat (split; auto). all: subst fr; auto.

          (* minimum mem *)
          intros ?????.
          solve_eq m m0.
          solve_eq gmp gmp_v. lia.

          exists wal; auto. }
        { (* ~ (n1 < n2) *)
          assert (Hv_false: v = Vconstr false_tag []) by now unfold LambdaANF_primInt_bool_fun in Hres; rewrite (to_Z_nlt_uint63_ltb_false _ _ n) in Hres.
          destruct (H3 _ _ Hv_false Hfalse_arr Hfalse_ord) as [fr [wal [Hinv' [Hfr [HreprVal [HrelE' [HvalsPreserved Hstep]]]]]]].
          simpl_modulus; simpl_modulus; cbn; lia.
          exists s, fr.
          split. {
            separate_instr.
            eapply rt_trans.
            apply HloadStep'.
            dostep_nary 2. constructor. apply rs_relop=>//.
            dostep_nary 1. constructor. apply rs_if_false.
            rewrite uint63_nlt_int64_nlt; [reflexivity|assumption].
            dostep_nary 0. eapply r_block with (t1s:=[::]) (t2s:=[:: T_num T_i32])(vs:=[::]); eauto.
            dostep_nary 0. constructor; apply rs_label_const; auto.
            replace [:: $VN VAL_int32 (Wasm_int.Int32.repr 1)] with [:: $V VAL_num (VAL_int32 (wasm_value_to_i32 wal))]; auto.
            inv HreprVal; try discriminate.
            - now replace ord with 0%N by congruence.
            - replace t with false_tag in * by congruence. rewrite Hfalse_arr in H7; inv H7; lia.
          }
          try repeat (split; auto). all: subst fr; auto.

          (* minimum mem *)
          intros ?????.
          solve_eq m m0.
          solve_eq gmp gmp_v. lia.

          exists wal; auto. } }
    - { (* leb *)
        inv H1; simpl.
        destruct (Z_le_dec (to_Z n1) (to_Z n2)).
        { (* n1 < n2 *)
          assert (Hv_true: v = Vconstr true_tag []) by now unfold LambdaANF_primInt_bool_fun in Hres; rewrite (reflect_iff _ _ (Uint63.lebP n1 n2)) in l; rewrite l in Hres.
          destruct (H3 _ _ Hv_true Htrue_arr Htrue_ord) as [fr [wal [Hinv' [Hfr [HreprVal [HrelE' [HvalsPreserved Hstep]]]]]]].
          simpl_modulus; simpl_modulus; cbn; lia.
          exists s, fr.
          split. {
            separate_instr.
            eapply rt_trans.
            apply HloadStep'.
            dostep_nary 2. constructor. apply rs_relop=>//.
            dostep_nary 1. constructor. apply rs_if_true.
            rewrite uint63_le_int64_le; [discriminate|assumption].
            dostep_nary 0. eapply r_block with (t1s:=[::]) (t2s:=[:: T_num T_i32])(vs:=[::]); eauto.
            dostep_nary 0. constructor; apply rs_label_const; auto.
            replace [:: $VN VAL_int32 (Wasm_int.Int32.repr 3)] with [:: $V VAL_num (VAL_int32 (wasm_value_to_i32 wal))]; auto.
            inv HreprVal; try discriminate.
            - now replace ord with 1%N by congruence.
            - replace t with true_tag in * by congruence. rewrite Htrue_arr in H7; inv H7; lia.
          }
          try repeat (split; auto). all: subst fr; auto.

          (* minimum mem *)
          intros ?????.
          solve_eq m m0.
          solve_eq gmp gmp_v. lia.

          exists wal; auto. }
        { (* ~ (n1 < n2) *)
          assert (Hv_false: v = Vconstr false_tag []) by now unfold LambdaANF_primInt_bool_fun in Hres; rewrite (to_Z_nle_uint63_leb_false _ _ n) in Hres.
          destruct (H3 _ _ Hv_false Hfalse_arr Hfalse_ord) as [fr [wal [Hinv' [Hfr [HreprVal [HrelE' [HvalsPreserved Hstep]]]]]]].
          simpl_modulus; simpl_modulus; cbn; lia.
          exists s, fr.
          split. {
            separate_instr.
            eapply rt_trans.
            apply HloadStep'.
            dostep_nary 2. constructor. apply rs_relop=>//.
            dostep_nary 1. constructor. apply rs_if_false.
            rewrite uint63_nle_int64_nle; [reflexivity|assumption].
            dostep_nary 0. eapply r_block with (t1s:=[::]) (t2s:=[:: T_num T_i32])(vs:=[::]); eauto.
            dostep_nary 0. constructor; apply rs_label_const; auto.
            replace [:: $VN VAL_int32 (Wasm_int.Int32.repr 1)] with [:: $V VAL_num (VAL_int32 (wasm_value_to_i32 wal))]; auto.
            inv HreprVal; try discriminate.
            - now replace ord with 0%N by congruence.
            - replace t with false_tag in * by congruence. rewrite Hfalse_arr in H7; inv H7; lia.
          }
          try repeat (split; auto). all: subst fr; auto.

          (* minimum mem *)
          intros ?????.
          solve_eq m m0.
          solve_eq gmp gmp_v. lia.

          exists wal; auto. } }
    - { (* compare *)
        inv H1; simpl.
        destruct (Z_lt_dec (to_Z n1) (to_Z n2)).
        { (* n1 < n2 *)
          assert (Hv_lt: v = Vconstr lt_tag [])
            by now unfold LambdaANF_primInt_compare_fun in Hres;
            inversion Hres as [Hcomp]; rewrite compare_def_spec; unfold compare_def;
            rewrite (reflect_iff _ _ (Uint63.ltbP n1 n2)) in l; rewrite l.
          assert (Hlt_arr: get_ctor_arity cenv lt_tag = Ret 0) by now unfold get_ctor_arity; rewrite Hlt.
          assert (Hlt_ord: get_ctor_ord cenv lt_tag = Ret 1%N) by now unfold get_ctor_ord; rewrite Hlt.
          destruct (H3 _ _ Hv_lt Hlt_arr Hlt_ord) as [fr [wal [Hinv' [Hfr [HreprVal [HrelE' [HvalsPreserved Hstep]]]]]]].
          simpl_modulus; simpl_modulus; cbn; lia.
          exists s, fr.
          split. {
            separate_instr.
            eapply rt_trans.
            apply HloadStep'.
            dostep_nary 2. constructor. apply rs_relop=>//.
            dostep_nary 1. constructor. apply rs_if_true; unfold wasm_bool.
            rewrite uint63_lt_int64_lt;[discriminate|assumption].
            dostep_nary 0. eapply r_block with (t1s:=[::]) (t2s:=[:: T_num T_i32])(vs:=[::]); eauto.
            dostep_nary 0. constructor. apply rs_label_const; auto.
            replace [:: $VN VAL_int32 (Wasm_int.Int32.repr 3)] with [:: $V VAL_num (VAL_int32 (wasm_value_to_i32 wal))]; auto.
            inv HreprVal; try discriminate.
            - now replace ord with 1%N by congruence.
            - replace t with lt_tag in * by congruence; rewrite Hlt_arr in H7;inv H7; lia.
          }
          try repeat (split; auto). subst fr; auto.

          (* minimum mem *)
          intros ?????.
          solve_eq m m0.
          solve_eq gmp gmp_v. lia.

          exists wal; auto. }
        { (* ~ (n1 < n2) *)
          destruct (Z.eq_dec (to_Z n1) (to_Z n2)).
          { (* n1 = n2 *)
            assert (Hv_eq: v = Vconstr eq_tag [])
              by now  unfold LambdaANF_primInt_compare_fun in Hres;
              inversion Hres as [Hcomp];
              rewrite compare_def_spec; unfold compare_def;
              rewrite (to_Z_nlt_uint63_ltb_false _ _ n);
              rewrite (reflect_iff _ _ (Uint63.eqbP n1 n2)) in e0; rewrite e0.
            assert (Heq_arr: get_ctor_arity cenv eq_tag = Ret 0) by now unfold get_ctor_arity; rewrite Heq.
            assert (Heq_ord: get_ctor_ord cenv eq_tag = Ret 0%N) by now unfold get_ctor_ord; rewrite Heq.
            destruct (H3 _ _ Hv_eq Heq_arr Heq_ord) as [fr [wal [Hinv' [Hfr [HreprVal [HrelE' [HvalsPreserved Hstep]]]]]]].
          simpl_modulus; simpl_modulus; cbn; lia.
          exists s, fr.
          split. {
            separate_instr.
            eapply rt_trans.
            apply HloadStep'.
            dostep_nary 2. constructor. apply rs_relop=>//.
            dostep_nary 1. constructor. apply rs_if_false; unfold wasm_bool.
            rewrite uint63_nlt_int64_nlt;[reflexivity|assumption].
            dostep_nary 0. eapply r_block with (t1s:=[::]) (t2s:=[:: T_num T_i32])(vs:=[::]); eauto.
            rewrite catA.
            reduce_under_label.
            apply HloadStep'.
            reduce_under_label.
            dostep_nary 2. constructor. apply rs_relop=>//.
            apply rt_step. constructor. apply rs_if_true; unfold wasm_bool.
            cbn; rewrite uint63_eq_int64_eq;[discriminate|assumption].
            reduce_under_label.
            apply rt_step. eapply r_block with (t1s:=[::]) (t2s:=[:: T_num T_i32])(vs:=[::]); eauto.
            reduce_under_label.
            apply rt_step. constructor. apply rs_label_const; auto.
            dostep_nary 0. constructor. apply rs_label_const; auto.
            replace [:: $VN VAL_int32 (Wasm_int.Int32.repr 1)] with [:: $V VAL_num (VAL_int32 (wasm_value_to_i32 wal))]; auto.
            inv HreprVal; try (replace t with eq_tag in *; [rewrite Heq_arr in H7; inv H7; lia|congruence]); try discriminate.
            now replace ord with 0%N by congruence.
          }
          try repeat (split; auto). subst fr; auto.

          (* minimum mem *)
          intros ?????.
          solve_eq m m0.
          solve_eq gmp gmp_v. lia.

          exists wal; auto. }
          { (* n1 <> n2 *)
            assert (Hv_gt: v = Vconstr gt_tag [])
              by now unfold LambdaANF_primInt_compare_fun in Hres; inversion Hres as [Hcomp];
              rewrite compare_def_spec; unfold compare_def;
              rewrite (to_Z_nlt_uint63_ltb_false _ _ n);
              now rewrite (to_Z_neq_uint63_eqb_false _ _ n0).
            assert (Hgt_arr: get_ctor_arity cenv gt_tag = Ret 0) by now unfold get_ctor_arity; rewrite Hgt.
            assert (Hgt_ord: get_ctor_ord cenv gt_tag = Ret 2%N) by now unfold get_ctor_ord; rewrite Hgt.
            destruct (H3 _ _ Hv_gt Hgt_arr Hgt_ord) as [fr [wal [Hinv' [Hfr [HreprVal [HrelE' [HvalsPreserved Hstep]]]]]]].
          simpl_modulus; simpl_modulus; cbn; lia.
          exists s, fr.
          split. {
            separate_instr.
            eapply rt_trans.
            apply HloadStep'.
            dostep_nary 2. constructor. apply rs_relop=>//.
            dostep_nary 1. constructor. apply rs_if_false; unfold wasm_bool.
            rewrite uint63_nlt_int64_nlt;[reflexivity|assumption].
            dostep_nary 0. eapply r_block with (t1s:=[::]) (t2s:=[:: T_num T_i32])(vs:=[::]); eauto.
            separate_instr.
            rewrite catA.
            reduce_under_label.
            apply HloadStep'.
            reduce_under_label.
            dostep_nary 2. constructor. apply rs_relop=>//.
            apply rt_step. constructor. apply rs_if_false; unfold wasm_bool.
            cbn. rewrite uint63_neq_int64_neq;[reflexivity|assumption].
            reduce_under_label.
            apply rt_step. eapply r_block with (t1s:=[::]) (t2s:=[:: T_num T_i32])(vs:=[::]); eauto.
            reduce_under_label.
            apply rt_step; constructor; apply rs_label_const; auto.
            dostep_nary 0. constructor; apply rs_label_const; auto.
            replace [:: $VN VAL_int32 (Wasm_int.Int32.repr 5)] with [:: $V VAL_num (VAL_int32 (wasm_value_to_i32 wal))]; auto.
            inv HreprVal; try (replace t with gt_tag in *; [rewrite Hgt_arr in H7; inv H7; lia|congruence]); try discriminate.
            now replace ord with 2%N by congruence.
          }
          repeat (split; auto). subst fr; auto.

          (* minimum mem *)
          intros ?????.
          solve_eq m m0.
          solve_eq gmp gmp_v. lia.

          now exists wal. } } }
    - { (* addc
           TODO: reduce duplication *)
        inversion H1; subst x1 y0.
        assert (HaddcApp: LambdaANF_primInt_carry_fun c0_tag c1_tag addc n1 n2 = v) by congruence.
        have HaddcRed :=  addc_reduce x' y' state s f m gmp_v (wasm_value_to_i32 (Val_ptr addr1)) (wasm_value_to_i32 (Val_ptr addr2)) b0 b1 n1 n2 c0_tag c1_tag carry_tag v Hinv Hc0 Hc1 HaddcApp Hmem2 (conj Hx' (conj Hload1' Hbsx)) (conj Hy' (conj Hload2' Hbsy)) HgmpBounds Hgmp.

        destruct HaddcRed as [sr' [m' [HinstrsRed [HINV_sr' [Hmem_sr' [Hgmp_sr' [Hsfuncs_sr' [Hmemlen_m' [Hval_sr' HvalsPreserved]]]]]]]]].
        exists sr', fr_carry_ops.
        split. { (* Instructions reduce *)
          eapply rt_trans. apply HinstrsRed.
          dostep_nary' 1. eapply r_local_set' with (f':=fr_carry_ops); subst fr_carry_ops; eauto.
          apply /ssrnat.leP.
          apply HlocsInBounds in Hrepr_x. lia. reflexivity.
          now apply rt_refl. }
        split. eapply update_local_preserves_INV with (f':=fr_carry_ops); eauto.
        split. now subst fr_carry_ops.
        split; auto.
        split. { (* minimum mem *)
          intros ?????.
          solve_eq m' m0.
          assert (gmp = gmp_v + 16)%N. {
            rewrite Hgmp_sr' in H6.
            inv H6. now simpl_eq. } subst gmp.
          lia.
        }
        split. {
          unfold LambdaANF_primInt_carry_fun in Hres.
          rewrite addc_def_spec in Hres;
          unfold addc_def in Hres.
          subst fr_carry_ops.
          destruct ((n1 + n2) <? n1)%uint63 eqn:Haddc;
          inversion Hres as [Hvconstr]; rewrite Hvconstr;
          eapply HunaryConstrValRelEnv; eauto;
          unfold get_ctor_arity; unfold get_ctor_ord; cbn;
          try rewrite Hc1;
          try rewrite Hc0;
          try rewrite nth_error_set_eq;
          auto.
          all: cbn; lia. }
        subst fr_carry_ops; cbn; repeat (split; auto).
        now exists (Val_ptr (gmp_v + 8)%N). }
    - { (* addcarryc
           TODO: reduce duplication *)
        inversion H1; subst x1 y0.
        assert (HaddcarrycApp: LambdaANF_primInt_carry_fun c0_tag c1_tag addcarryc n1 n2 = v) by congruence.
        have HaddcarrycRed :=  addcarryc_reduce x' y' state s f m gmp_v (wasm_value_to_i32 (Val_ptr addr1)) (wasm_value_to_i32 (Val_ptr addr2)) b0 b1 n1 n2 c0_tag c1_tag carry_tag v Hinv Hc0 Hc1 HaddcarrycApp Hmem2 (conj Hx' (conj Hload1' Hbsx)) (conj Hy' (conj Hload2' Hbsy)) HgmpBounds Hgmp.

        destruct HaddcarrycRed as [sr' [m' [HinstrsRed [HINV_sr' [Hmem_sr' [Hgmp_sr' [Hsfuncs_sr' [Hmemlen_m' [Hval_sr' HvalsPreserved]]]]]]]]].
        exists sr', fr_carry_ops.
        split. { (* Instructions reduce *)
          eapply rt_trans. apply HinstrsRed.
          dostep_nary' 1. eapply r_local_set' with (f':=fr_carry_ops); subst fr_carry_ops; eauto.
          apply /ssrnat.leP.
          apply HlocsInBounds in Hrepr_x. lia. reflexivity.
          now apply rt_refl. }
        split. eapply update_local_preserves_INV with (f':=fr_carry_ops); eauto.
        split. now subst fr_carry_ops.
        split; auto.
        split. { (* minimum mem *)
          intros ?????.
          solve_eq m' m0.
          assert (gmp = gmp_v + 16)%N. {
            rewrite Hgmp_sr' in H6.
            inv H6. now simpl_eq. } subst gmp.
          lia.
        }
        split. {
          unfold LambdaANF_primInt_carry_fun in Hres.
          rewrite addcarryc_def_spec in Hres;
          unfold addcarryc_def, addcarry in Hres.
          subst fr_carry_ops.
          destruct ((n1 + n2 + 1) <=? n1)%uint63 eqn:Haddcarryc;
          inversion Hres as [Hvconstr]; rewrite Hvconstr;
          eapply HunaryConstrValRelEnv; eauto;
          unfold get_ctor_arity; unfold get_ctor_ord; cbn;
          try rewrite Hc1;
          try rewrite Hc0;
          try rewrite nth_error_set_eq;
          auto.
          all: cbn; lia. }
        subst fr_carry_ops; cbn; repeat (split; auto).
        now exists (Val_ptr (gmp_v + 8)%N). }
    - { (* subc
           TODO: reduce duplication *)
        inversion H1; subst x1 y0.
        assert (HsubcApp: LambdaANF_primInt_carry_fun c0_tag c1_tag subc n1 n2 = v) by congruence.
        have HsubcRed :=  subc_reduce x' y' state s f m gmp_v (wasm_value_to_i32 (Val_ptr addr1)) (wasm_value_to_i32 (Val_ptr addr2)) b0 b1 n1 n2 c0_tag c1_tag carry_tag v Hinv Hc0 Hc1 HsubcApp Hmem2 (conj Hx' (conj Hload1' Hbsx)) (conj Hy' (conj Hload2' Hbsy)) HgmpBounds Hgmp.
        destruct HsubcRed as [sr' [m' [HinstrsRed [HINV_sr' [Hmem_sr' [Hgmp_sr' [Hsfuncs_sr' [Hmemlen_m' [Hval_sr' HvalsPreserved]]]]]]]]].
        exists sr', fr_carry_ops.
        split. { (* Instructions reduce *)
          eapply rt_trans. apply HinstrsRed.
          dostep_nary' 1. eapply r_local_set' with (f':=fr_carry_ops); subst fr_carry_ops; eauto.
          apply /ssrnat.leP.
          apply HlocsInBounds in Hrepr_x. lia. reflexivity.
          now apply rt_refl. }
        split. eapply update_local_preserves_INV with (f':=fr_carry_ops); eauto.
        split. now subst fr_carry_ops.
        split; auto.
        split. { (* minimum mem *)
          intros ?????.
          solve_eq m' m0.
          assert (gmp = gmp_v + 16)%N. {
            rewrite Hgmp_sr' in H6.
            inv H6. now simpl_eq. } subst gmp.
          lia.
        }
        split. {
          unfold LambdaANF_primInt_carry_fun in Hres.
          rewrite subc_def_spec in Hres;
          unfold subc_def in Hres.
          subst fr_carry_ops.
          destruct (n2 <=? n1)%uint63 eqn:Hsubc;
          inversion Hres as [Hvconstr]; rewrite Hvconstr;
          eapply HunaryConstrValRelEnv; eauto;
          unfold get_ctor_arity; unfold get_ctor_ord; cbn;
          try rewrite Hc1;
          try rewrite Hc0;
          try rewrite nth_error_set_eq;
          auto.
          all: cbn; lia. }
        subst fr_carry_ops; cbn; repeat (split; auto).
        now exists (Val_ptr (gmp_v + 8)%N). }
    - { (* subcarryc
           TODO: reduce duplication *)
        inversion H1; subst x1 y0.
        assert (HsubcarrycApp: LambdaANF_primInt_carry_fun c0_tag c1_tag subcarryc n1 n2 = v) by congruence.
        have HsubcarrycRed :=  subcarryc_reduce x' y' state s f m gmp_v (wasm_value_to_i32 (Val_ptr addr1)) (wasm_value_to_i32 (Val_ptr addr2)) b0 b1 n1 n2 c0_tag c1_tag carry_tag v Hinv Hc0 Hc1 HsubcarrycApp Hmem2 (conj Hx' (conj Hload1' Hbsx)) (conj Hy' (conj Hload2' Hbsy)) HgmpBounds Hgmp.
        destruct HsubcarrycRed as [sr' [m' [HinstrsRed [HINV_sr' [Hmem_sr' [Hgmp_sr' [Hsfuncs_sr' [Hmemlen_m' [Hval_sr' HvalsPreserved]]]]]]]]].
        exists sr', fr_carry_ops.
        split. { (* Instructions reduce *)
          eapply rt_trans. apply HinstrsRed.
          dostep_nary' 1. eapply r_local_set' with (f':=fr_carry_ops); subst fr_carry_ops; eauto.
          apply /ssrnat.leP.
          apply HlocsInBounds in Hrepr_x. lia. reflexivity.
          now apply rt_refl. }
        split. eapply update_local_preserves_INV with (f':=fr_carry_ops); eauto.
        split. now subst fr_carry_ops.
        split; auto.
        split. { (* minimum mem *)
          intros ?????.
          solve_eq m' m0.
          assert (gmp = gmp_v + 16)%N. {
            rewrite Hgmp_sr' in H6.
            inv H6. now simpl_eq. } subst gmp.
          lia.
        }
        split. {
          unfold LambdaANF_primInt_carry_fun in Hres.
          rewrite subcarryc_def_spec in Hres;
          unfold subcarryc_def, subcarry in Hres.
          subst fr_carry_ops.
          destruct (n2 <? n1)%uint63 eqn:Hsubcarryc;
          inversion Hres as [Hvconstr]; rewrite Hvconstr;
          eapply HunaryConstrValRelEnv; eauto;
          unfold get_ctor_arity; unfold get_ctor_ord; cbn;
          try rewrite Hc1;
          try rewrite Hc0;
          try rewrite nth_error_set_eq;
          auto.
          all: cbn; lia. }
        subst fr_carry_ops; cbn; repeat (split; auto).
        now exists (Val_ptr (gmp_v + 8)%N). }
    - { (* mulc *)
        inversion H1; subst x1 y0.
        inversion Hres as [Hv_mulc].
        have I := Hinv. destruct I as [_ [_ [_ [_ [_ [_ [_ [_ [_ [_ [HnoGlobDups [_ [_ [Hmult2 [_ Hi64tempsW]]]]]]]]]]]]]]].
        assert (Hglob_tmp1: i64_glob glob_tmp1) by now constructor.
        assert (Hglob_tmp2: i64_glob glob_tmp2) by now right; constructor.
        assert (Hglob_tmp3: i64_glob glob_tmp3) by now right; right; constructor.
        assert (Hglob_tmp4: i64_glob glob_tmp4) by now right; right; right; constructor.
        remember (cross (to_Z n1) (to_Z n2))%Z as crs eqn:Hcrs.
        remember (lower (to_Z n1) (to_Z n2))%Z as lo64 eqn:Hlo64.
        remember (upper (to_Z n1) (to_Z n2))%Z as hi64 eqn:Hhi64.
        remember ((upper (to_Z n1) (to_Z n2)) * 2 + (lower (to_Z n1) (to_Z n2) mod 2^64) / 2^63)%Z as hi63 eqn:Hhi63.
        remember (lower (to_Z n1) (to_Z n2) mod 2^63)%Z as lo63 eqn:Hlo63.

        (* Due to the use of globals for storing intermediate values,
           we need a series of store_records, and we need to show that
           the invariants, memory, values of the other globals etc. are preserved
           every time we write to a global.
           At the moment, this is done manually/ naively, as witnessed below.
          TODO: Clean up/ automate.*)
        destruct (Hi64tempsW glob_tmp1 Hglob_tmp1 (VAL_int64 (Int64.repr (lo (to_Z n1) * lo (to_Z n2))%Z))) as [sr1 HupdGlob1].
        assert (HINV1: INV fenv nenv sr1 f) by now eapply update_global_preserves_INV with (sr:=s) (sr':=sr1) (i:=glob_tmp1) (num:=(VAL_int64 (Int64.repr (lo (to_Z n1) * lo (to_Z n2))%Z))); eauto; [discriminate|now intros|now intros].
        have Hmem_sr1 := update_global_preserves_memory _ _ _ _ _ HupdGlob1. symmetry in Hmem_sr1. rewrite Hmem2 in Hmem_sr1.
        have I := HINV1. destruct I as [_ [_ [_ [_ [_ [_ [_ [_ [_ [_ [_ [_ [_ [_ [_ Hi64tempsW1]]]]]]]]]]]]]]].
        destruct (Hi64tempsW1 glob_tmp2 Hglob_tmp2 (VAL_int64 (Int64.repr (hi (to_Z n1) * lo (to_Z n2))%Z))) as [sr2 HupdGlob2].
        assert (HINV2: INV fenv nenv sr2 f) by now eapply update_global_preserves_INV with (sr:=sr1) (sr':=sr2) (i:=glob_tmp2) (num:=(VAL_int64 (Int64.repr (hi (to_Z n1) * lo (to_Z n2))%Z))); eauto; [discriminate|now intros|now intros].
        have Hmem_sr2 := update_global_preserves_memory _ _ _ _ _ HupdGlob2. symmetry in Hmem_sr2.
        rewrite Hmem_sr1 in Hmem_sr2.
        have I := HINV2. destruct I as [_ [_ [_ [_ [_ [_ [_ [_ [_ [_ [_ [_ [_ [_ [_ Hi64tempsW2]]]]]]]]]]]]]]].
        destruct (Hi64tempsW2 glob_tmp3 Hglob_tmp3 (VAL_int64 (Int64.repr (lo (to_Z n1) * hi (to_Z n2))%Z))) as [sr3 HupdGlob3].
        assert (HINV3: INV fenv nenv sr3 f) by now eapply update_global_preserves_INV with (sr:=sr2) (sr':=sr3) (i:=glob_tmp3) (num:=(VAL_int64 (Int64.repr (lo (to_Z n1) * hi (to_Z n2))%Z))); eauto; [discriminate|now intros|now intros].
        have Hmem_sr3 := update_global_preserves_memory _ _ _ _ _ HupdGlob3. symmetry in Hmem_sr3.
        rewrite Hmem_sr2 in Hmem_sr3.
        have I := HINV3. destruct I as [_ [_ [_ [_ [_ [_ [_ [_ [_ [_ [_ [_ [_ [_ [_ Hi64tempsW3]]]]]]]]]]]]]]].
        destruct (Hi64tempsW3 glob_tmp4 Hglob_tmp4 (VAL_int64 (Int64.repr (hi (to_Z n1) * hi (to_Z n2))%Z))) as [sr4 HupdGlob4].
        assert (HINV4: INV fenv nenv sr4 f) by now eapply update_global_preserves_INV with (sr:=sr3) (sr':=sr4) (i:=glob_tmp4) (num:=(VAL_int64 (Int64.repr (hi (to_Z n1) * hi (to_Z n2))%Z))); eauto; [discriminate|now intros|now intros].
        have Hmem_sr4 := update_global_preserves_memory _ _ _ _ _ HupdGlob4. symmetry in Hmem_sr4.
        rewrite Hmem_sr3 in Hmem_sr4.
        have I := HINV4. destruct I as [_ [_ [_ [_ [_ [_ [_ [_ [_ [_ [_ [_ [_ [_ [_ Hi64tempsW4]]]]]]]]]]]]]]].
        destruct (Hi64tempsW4 glob_tmp3 Hglob_tmp3 (VAL_int64 (Int64.repr crs))) as [sr5 HupdGlob5].
        assert (HINV5: INV fenv nenv sr5 f) by now eapply update_global_preserves_INV with (sr:=sr4) (sr':=sr5) (i:=glob_tmp3) (num:=(VAL_int64 (Int64.repr crs))); eauto; [discriminate|now intros|now intros].
        have Hmem_sr5 := update_global_preserves_memory _ _ _ _ _ HupdGlob5. symmetry in Hmem_sr5.
        rewrite Hmem_sr4 in Hmem_sr5.
        have I := HINV5. destruct I as [_ [_ [_ [_ [_ [_ [_ [_ [_ [_ [_ [_ [_ [_ [_ Hi64tempsW5]]]]]]]]]]]]]]].
        destruct (Hi64tempsW5 glob_tmp2 Hglob_tmp2 (VAL_int64 (Int64.repr hi64))) as [sr6 HupdGlob6].
        assert (HINV6: INV fenv nenv sr6 f) by now eapply update_global_preserves_INV with (sr:=sr5) (sr':=sr6) (i:=glob_tmp2) (num:=(VAL_int64 (Int64.repr hi64))); eauto; [discriminate|now intros|now intros].
        have Hmem_sr6 := update_global_preserves_memory _ _ _ _ _ HupdGlob6. symmetry in Hmem_sr6.
        rewrite Hmem_sr5 in Hmem_sr6.
        have I := HINV6. destruct I as [_ [_ [_ [_ [_ [_ [_ [_ [_ [_ [_ [_ [_ [_ [_ Hi64tempsW6]]]]]]]]]]]]]]].
        destruct (Hi64tempsW6 glob_tmp1 Hglob_tmp1 (VAL_int64 (Int64.repr lo64))) as [sr7 HupdGlob7].
        assert (HINV7: INV fenv nenv sr7 f) by now eapply update_global_preserves_INV with (sr:=sr6) (sr':=sr7) (i:=glob_tmp1) (num:=(VAL_int64 (Int64.repr lo64))); eauto; [discriminate|now intros|now intros].
        have Hmem_sr7 := update_global_preserves_memory _ _ _ _ _ HupdGlob7. symmetry in Hmem_sr7.
        rewrite Hmem_sr6 in Hmem_sr7.
        have I := HINV7. destruct I as [_ [_ [_ [_ [_ [_ [_ [_ [_ [_ [_ [_ [_ [_ [_ Hi64tempsW7]]]]]]]]]]]]]]].
        destruct (Hi64tempsW7 glob_tmp2 Hglob_tmp2 (VAL_int64 (Int64.repr hi63))) as [sr8 HupdGlob8].
        assert (HINV8: INV fenv nenv sr8 f) by now eapply update_global_preserves_INV with (sr:=sr7) (sr':=sr8) (i:=glob_tmp2) (num:=(VAL_int64 (Int64.repr hi63))); eauto; [discriminate|now intros|now intros].
        have Hmem_sr8 := update_global_preserves_memory _ _ _ _ _ HupdGlob8. symmetry in Hmem_sr8.
        rewrite Hmem_sr7 in Hmem_sr8.
        have I := HINV8. destruct I as [_ [_ [_ [_ [_ [_ [_ [_ [_ [_ [_ [_ [_ [_ [_ Hi64tempsW8]]]]]]]]]]]]]]].
        destruct (Hi64tempsW8 glob_tmp1 Hglob_tmp1 (VAL_int64 (Int64.repr lo63))) as [sr9 HupdGlob9].
        assert (HINV9: INV fenv nenv sr9 f) by now eapply update_global_preserves_INV with (sr:=sr8) (sr':=sr9) (i:=glob_tmp1) (num:=(VAL_int64 (Int64.repr lo63))); eauto; [discriminate|now intros|now intros].
        have Hmem_sr9 := update_global_preserves_memory _ _ _ _ _ HupdGlob9. symmetry in Hmem_sr9.
        rewrite Hmem_sr8 in Hmem_sr9.
        unfold INV_inst_globals_nodup in HnoGlobDups.
        assert (Hgmp_sr1 : sglob_val sr1 (f_inst f) glob_mem_ptr = Some (VAL_num (VAL_int32 (N_to_i32 gmp_v)))) by now eapply update_global_get_other; eauto; discriminate.
        assert (Hgmp_sr2 : sglob_val sr2 (f_inst f) glob_mem_ptr = Some (VAL_num (VAL_int32 (N_to_i32 gmp_v)))) by now eapply update_global_get_other; eauto; discriminate.
        assert (Hgmp_sr3 : sglob_val sr3 (f_inst f) glob_mem_ptr = Some (VAL_num (VAL_int32 (N_to_i32 gmp_v)))) by now eapply update_global_get_other; eauto; discriminate.
        assert (Hgmp_sr4 : sglob_val sr4 (f_inst f) glob_mem_ptr = Some (VAL_num (VAL_int32 (N_to_i32 gmp_v)))) by now eapply update_global_get_other; eauto; discriminate.
        assert (Hgmp_sr5 : sglob_val sr5 (f_inst f) glob_mem_ptr = Some (VAL_num (VAL_int32 (N_to_i32 gmp_v)))) by now eapply update_global_get_other; eauto; discriminate.
        assert (Hgmp_sr6 : sglob_val sr6 (f_inst f) glob_mem_ptr = Some (VAL_num (VAL_int32 (N_to_i32 gmp_v)))) by now eapply update_global_get_other; eauto; discriminate.
        assert (Hgmp_sr7 : sglob_val sr7 (f_inst f) glob_mem_ptr = Some (VAL_num (VAL_int32 (N_to_i32 gmp_v)))) by now eapply update_global_get_other; eauto; discriminate.
        assert (Hgmp_sr8 : sglob_val sr8 (f_inst f) glob_mem_ptr = Some (VAL_num (VAL_int32 (N_to_i32 gmp_v)))) by now eapply update_global_get_other; eauto; discriminate.
        assert (Hgmp_sr9 : sglob_val sr9 (f_inst f) glob_mem_ptr = Some (VAL_num (VAL_int32 (N_to_i32 gmp_v)))) by now eapply update_global_get_other; eauto; discriminate.
        assert (Hgv1 : sglob_val sr1 (f_inst f) glob_tmp1 = Some (VAL_num (VAL_int64 (Int64.repr (lo (to_Z n1) * lo (to_Z n2))%Z)))) by now eapply update_global_get_same; eauto; discriminate.
        assert (Hgv2 : sglob_val sr2 (f_inst f) glob_tmp2 = Some (VAL_num (VAL_int64 (Int64.repr (hi (to_Z n1) * lo (to_Z n2))%Z)))) by now eapply update_global_get_same; eauto; discriminate.
        assert (Hgv2' : sglob_val sr2 (f_inst f) glob_tmp1 = Some (VAL_num (VAL_int64 (Int64.repr (lo (to_Z n1) * lo (to_Z n2))%Z)))) by now eapply update_global_get_other; eauto; discriminate.
        assert (Hgv3 : sglob_val sr3 (f_inst f) glob_tmp3 = Some (VAL_num (VAL_int64 (Int64.repr (lo (to_Z n1) * hi (to_Z n2))%Z)))) by now eapply update_global_get_same; eauto; discriminate.
        assert (Hgv3' : sglob_val sr3 (f_inst f) glob_tmp1 = Some (VAL_num (VAL_int64 (Int64.repr (lo (to_Z n1) * lo (to_Z n2))%Z)))) by now eapply update_global_get_other; eauto; discriminate.
        assert (Hgv3'' : sglob_val sr3 (f_inst f) glob_tmp2 = Some (VAL_num (VAL_int64 (Int64.repr (hi (to_Z n1) * lo (to_Z n2))%Z)))) by now eapply update_global_get_other; eauto; discriminate.
        assert (Hgv4 : sglob_val sr4 (f_inst f) glob_tmp4 = Some (VAL_num (VAL_int64 (Int64.repr (hi (to_Z n1) * hi (to_Z n2))%Z)))) by now eapply update_global_get_same; eauto; discriminate.
        assert (Hgv4' : sglob_val sr4 (f_inst f) glob_tmp1 = Some (VAL_num (VAL_int64 (Int64.repr (lo (to_Z n1) * lo (to_Z n2))%Z)))) by now eapply update_global_get_other; eauto; discriminate.
        assert (Hgv4'' : sglob_val sr4 (f_inst f) glob_tmp2 = Some (VAL_num (VAL_int64 (Int64.repr (hi (to_Z n1) * lo (to_Z n2))%Z)))) by now eapply update_global_get_other; eauto; discriminate.
        assert (Hgv4''' : sglob_val sr4 (f_inst f) glob_tmp3 = Some (VAL_num (VAL_int64 (Int64.repr (lo (to_Z n1) * hi (to_Z n2))%Z)))) by now eapply update_global_get_other; eauto; discriminate.
        assert (Hgv5 : sglob_val sr5 (f_inst f) glob_tmp3 = Some (VAL_num (VAL_int64 (Int64.repr crs)))) by now eapply update_global_get_same; eauto; discriminate.
        assert (Hgv5' : sglob_val sr5 (f_inst f) glob_tmp1 = Some (VAL_num (VAL_int64 (Int64.repr (lo (to_Z n1) * lo (to_Z n2))%Z)))) by now eapply update_global_get_other; eauto; discriminate.
        assert (Hgv5'' : sglob_val sr5 (f_inst f) glob_tmp2 = Some (VAL_num (VAL_int64 (Int64.repr (hi (to_Z n1) * lo (to_Z n2))%Z)))) by now eapply update_global_get_other; eauto; discriminate.
        assert (Hgv5''' : sglob_val sr5 (f_inst f) glob_tmp4 = Some (VAL_num (VAL_int64 (Int64.repr (hi (to_Z n1) * hi (to_Z n2))%Z)))) by now eapply update_global_get_other; eauto; discriminate.
        assert (Hgv6 : sglob_val sr6 (f_inst f) glob_tmp2 = Some (VAL_num (VAL_int64 (Int64.repr hi64)))) by now eapply update_global_get_same; eauto; discriminate.
        assert (Hgv6' : sglob_val sr6 (f_inst f) glob_tmp1 = Some (VAL_num (VAL_int64 (Int64.repr (lo (to_Z n1) * lo (to_Z n2))%Z)))) by now eapply update_global_get_other; eauto; discriminate.
        assert (Hgv6'' : sglob_val sr6 (f_inst f) glob_tmp3 = Some (VAL_num (VAL_int64 (Int64.repr crs)))) by now eapply update_global_get_other; eauto; discriminate.
        assert (Hgv6''' : sglob_val sr6 (f_inst f) glob_tmp4 = Some (VAL_num (VAL_int64 (Int64.repr (hi (to_Z n1) * hi (to_Z n2))%Z)))) by now eapply update_global_get_other; eauto; discriminate.
        assert (Hgv7 : sglob_val sr7 (f_inst f) glob_tmp1 = Some (VAL_num (VAL_int64 (Int64.repr lo64)))) by now eapply update_global_get_same; eauto; discriminate.
        assert (Hgv7' : sglob_val sr7 (f_inst f) glob_tmp2 = Some (VAL_num (VAL_int64 (Int64.repr hi64)))) by now eapply update_global_get_other; eauto; discriminate.
        assert (Hgv7'' : sglob_val sr7 (f_inst f) glob_tmp3 = Some (VAL_num (VAL_int64 (Int64.repr crs)))) by now eapply update_global_get_other; eauto; discriminate.
        assert (Hgv7''' : sglob_val sr7 (f_inst f) glob_tmp4 = Some (VAL_num (VAL_int64 (Int64.repr (hi (to_Z n1) * hi (to_Z n2))%Z)))) by now eapply update_global_get_other; eauto; discriminate.
        assert (Hgv8 : sglob_val sr8 (f_inst f) glob_tmp2 = Some (VAL_num (VAL_int64 (Int64.repr hi63)))) by now eapply update_global_get_same; eauto; discriminate.
        assert (Hgv8' : sglob_val sr8 (f_inst f) glob_tmp1 = Some (VAL_num (VAL_int64 (Int64.repr lo64)))) by now eapply update_global_get_other; eauto; discriminate.
        assert (Hgv9 : sglob_val sr9 (f_inst f) glob_tmp1 = Some (VAL_num (VAL_int64 (Int64.repr lo63)))) by now eapply update_global_get_same; eauto; discriminate.
        assert (Hgv9' : sglob_val sr9 (f_inst f) glob_tmp2 = Some (VAL_num (VAL_int64 (Int64.repr hi63)))) by now eapply update_global_get_other; eauto; discriminate.
        assert (HenoughMem : (Z.of_N gmp_v + Z.of_N 52 <= Z.of_N (mem_length m) < Int32.modulus)%Z) by lia.
        replace lo63 with (to_Z (snd (mulc n1 n2))) in Hgv9 by now rewrite mulc_snd.
        replace hi63 with (to_Z (fst (mulc n1 n2))) in Hgv9' by now rewrite mulc_fst.
        have HmakeProdReduce := make_product_reduce  glob_tmp2 glob_tmp1 state sr9 f m gmp_v (to_Z (fst (mulc n1 n2))) (to_Z (snd (mulc n1 n2)))
                                  Hglob_tmp2 Hglob_tmp1 HINV9 Hmem_sr9 Hgmp_sr9 HenoughMem Hgv9' Hgv9.

        destruct HmakeProdReduce as [sr' [m' [Hred [HINV' [Hmem' [Hgmp' [Hloadp1 [Hloadp2 [Hloadord [Hloadp1addr [Hloadp2addr [Hloadi32s [Hloadi64s [Hsfuncs Hmemlen']]]]]]]]]]]]]].
        assert (Hsfs': s_funcs s = s_funcs sr'). {
          apply update_global_preserves_funcs in HupdGlob1, HupdGlob2, HupdGlob3, HupdGlob4,
                                      HupdGlob5, HupdGlob6, HupdGlob7, HupdGlob8, HupdGlob9.
          congruence. }
        assert (Hlocx0' : N.to_nat x0' < length (f_locs f))
            by now apply (HlocsInBounds x0 x0' Hrepr_x).
        destruct (Hmult2 gmp_v m Hmem2 Hgmp HgmpBound) as [n0 Hn0].
        remember
       {| f_locs :=
           set_nth (VAL_num (VAL_int32 (wasm_value_to_i32 (Val_ptr (gmp_v + 16)%N)))) (f_locs f) (N.to_nat x0') (VAL_num (VAL_int32 (wasm_value_to_i32 (Val_ptr (gmp_v + 16)%N))));
         f_inst := f_inst f
       |} as fr'.
        assert (f_inst f = f_inst fr') by now subst fr'.
        assert (Hlocx0'_fr' : N.to_nat x0' < length (f_locs fr')). {
          assert (length (f_locs fr') = length (f_locs f)). {
            subst fr'.
            apply set_nth_length.
            apply /ssrnat.leP. apply Hlocx0'. }
          replace (length (f_locs fr')) with (length (f_locs f)).
          now eapply (HlocsInBounds x0 x0' Hrepr_x). }
        assert (HlocsLe: ssrnat.leq (S (N.to_nat x0')) (Datatypes.length (f_locs f))).
           by now apply /ssrnat.leP; assumption.
        assert (HnewframeLoc: f_locs fr' = set_nth (VAL_num (VAL_int32 (wasm_value_to_i32 (Val_ptr (gmp_v + 16)%N)))) (f_locs f) (N.to_nat x0') (VAL_num (VAL_int32 (wasm_value_to_i32 (Val_ptr (gmp_v + 16)%N))))) by now subst fr'.
        assert (HvalRelp1 : repr_val_LambdaANF_Wasm cenv fenv nenv penv (Vprim (AstCommon.primInt ; fst (mulc n1 n2))) sr' (f_inst fr') (Val_ptr gmp_v)). {
          unfold page_size in *.
          apply Rprim_v with (sr:=sr') (gmp:=(gmp_v + 28)%N) (m:=m') (addr:=gmp_v); subst fr'; auto; try (clear_except HenoughMem; lia).
          exists n0; apply Hn0. }

        assert (HvalRelp2 : repr_val_LambdaANF_Wasm cenv fenv nenv penv (Vprim (AstCommon.primInt ; snd (mulc n1 n2))) sr' (f_inst fr') (Val_ptr (gmp_v + 8)%N)). {
          unfold page_size in *.
          apply Rprim_v with (sr:=sr') (gmp:=(gmp_v + 28)%N) (m:=m') (addr:=(gmp_v+8)%N); subst fr'; auto; try (clear_except HenoughMem; lia).
          exists (n0+4)%N. clear_except Hn0. lia. }

        assert (HvalsPreserved : forall wal val,
                   repr_val_LambdaANF_Wasm cenv fenv nenv penv val s (f_inst f) wal -> repr_val_LambdaANF_Wasm cenv fenv nenv penv val sr' (f_inst fr') wal). {
          intros.
          eapply val_relation_depends_on_mem_smaller_than_gmp_and_funcs; subst fr'; eauto;
            try rewrite -Hmemlen'; clear_except HenoughMem; lia. }
        assert (HvalRelPair : repr_val_LambdaANF_Wasm cenv fenv nenv penv (LambdaANF_primInt_prod_fun pair_tag mulc n1 n2) sr' (f_inst fr') (Val_ptr (gmp_v + 16)%N)). {
          apply Rconstr_boxed_v with (v:=N_to_i32 pair_ord) (gmp:=(gmp_v+28)%N) (m:=m') (arity:=2) (ord:=0%N); subst fr'; auto; try (clear_except HenoughMem; lia).
          unfold get_ctor_ord; now rewrite Hpair.
          unfold get_ctor_arity; now rewrite Hpair.
          exists (n0 + 8)%N. clear_except Hn0; lia.
          apply Rcons_l with (wal:=Val_ptr gmp_v) (m:=m') (addr:=(4 + (gmp_v+16))%N) (gmp:=(gmp_v+28)%N); auto; try (clear_except HenoughMem; lia).
          replace (4 + (gmp_v + 16))%N with (gmp_v + 20)%N by liat.
          unfold wasm_value_to_i32, wasm_value_to_u32. now unfold N_to_i32 in Hloadp1addr.
          apply Rcons_l with (wal:=Val_ptr (gmp_v + 8)%N) (m:=m') (addr:=(4 + (4 + (gmp_v+16)))%N) (gmp:=(gmp_v+28)%N); auto; try (clear_except HenoughMem; lia).
          replace (4 + (4 + (gmp_v + 16)))%N with (gmp_v + 24)%N by liat.
          unfold wasm_value_to_i32, wasm_value_to_u32. now unfold N_to_i32 in Hloadp2addr.
          now apply Rnil_l. }

        assert (HINV'' : INV fenv nenv sr' fr') by now eapply update_local_preserves_INV; eauto.
        assert (rel_env_LambdaANF_Wasm (lenv:=lenv) cenv fenv nenv penv e (M.set x0 (LambdaANF_primInt_prod_fun pair_tag mulc n1 n2) rho) sr' fr' fds). {
          have Hl := HlocsInBounds _ _ Hrepr_x.
          apply nth_error_Some in Hl.
          apply notNone_Some in Hl. destruct Hl as [? Hlx].
          unfold rel_env_LambdaANF_Wasm.
          destruct HrelE as [Hfun1 [Hfun2 Hvar]].
          split. {
            intros ????? Hrho Hv'.
            destruct (var_dec x0 x2).
            - (* x0 = x1 *) (* v0 can never be a function value, by assumption on primops *)
              subst x2. rewrite M.gss in Hrho; eauto.
              inversion Hrho as [Hv_mulc']. subst v0. rewrite Hv_mulc in Hv'.
              have H'' := Hnofunval rho' fds' f0.
              contradiction.
            - (* x0 <> x1 *) rewrite M.gso in Hrho; eauto.
          } split. {
            intros ? Hnfd. apply Hfun2 in Hnfd.
            destruct Hnfd as [i' [Htrans HvalFun]].
            exists i'. split. assumption.
            apply val_relation_func_depends_on_funcs with (s:=s); subst fr'; auto.
          }
          intros x2 Hx2free Hx2notfun.
          destruct (var_dec x0 x2).
          { (* x = x1 *)
            subst x2.
            exists v, (Val_ptr (gmp_v+16)%N).
            rewrite M.gss. split; auto.
            split.
            exists x0'. cbn. split. assumption.
            unfold lookup_N; cbn; auto.
            subst fr'. cbn.
            eapply set_nth_nth_error_same; eauto. rewrite <-Hv_mulc. assumption.
          }
          { (* x <> x1 *)
            assert (Hocc : occurs_free (Eprim x0 p [:: x ; y] e) x2) by now apply Free_Eprim2.
            have H' := Hvar _ Hocc Hx2notfun.
            destruct H' as [val' [wal' [Hrho [Hloc Hval']]]].
            exists val', wal'. split.
            rewrite M.gso; auto. split.
            destruct Hloc as [i' [Hl1 Hl2]].
            unfold stored_in_locals. exists i'. split; auto.
            unfold lookup_N.
            subst fr'; rewrite set_nth_nth_error_other; auto.

            intro. assert (x0' = i') by (clear_except H6; lia). subst x0'.
            have Hcontra := repr_var_inj _ _ _ _ HlenvInjective Hl1 Hrepr_x.
            contradiction.

            now apply HvalsPreserved.
          }
        }
        exists sr', fr'.
        have Hb1 := to_Z_bounded n1. cbn in Hb1.
        have Hb2 := to_Z_bounded n2. cbn in Hb2.
        assert (0 <= to_Z n1 < 2^64)%Z as Hn1bounded64 by lia.
        assert (0 <= to_Z n2 < 2^64)%Z as Hn2bounded64 by lia.
        split. { (* Instructions reduce *)
          unfold mulc_instrs.
          remember (make_product glob_mem_ptr glob_tmp2 glob_tmp1) as make_product_instrs.
          separate_instr.
          eapply rt_trans. apply HloadStep1.
          dostep_nary 2. apply low32step; auto.
          dostep_nary_eliml 0 1. eapply r_local_get; eassumption.
          dostep_nary_eliml 1 1. eapply r_load_success; eassumption.
          rewrite Hbsy.
          dostep_nary_eliml 2 1. apply low32step; auto.
          dostep_nary 2. constructor. apply rs_binop_success; first done. cbn.
          rewrite max32bit_mul_modulo64_id; try apply low32_max_int32; reflexivity.
          dostep_nary 1. eapply r_global_set'; eassumption.
          dostep_nary 0. eapply r_local_get; eassumption.
          dostep_nary 1. eapply r_load_success; eassumption.
          rewrite Hbsx.
          dostep_nary 2. apply high32step; auto.
          dostep_nary_eliml 0 1. eapply r_local_get; eassumption.
          dostep_nary_eliml 1 1. eapply r_load_success; eassumption.
          rewrite Hbsy.
          dostep_nary_eliml 2 1. apply low32step; auto.
          dostep_nary 2. constructor. apply rs_binop_success; first done. cbn.
          rewrite max32bit_mul_modulo64_id; try apply low32_max_int32. reflexivity.
          unfold hi. apply high32_max_int32; auto.
          dostep_nary 1. eapply r_global_set'; eassumption.
          dostep_nary 0. eapply r_local_get; eassumption.
          dostep_nary 1. eapply r_load_success; eassumption.
          rewrite Hbsx.
          dostep_nary 2. apply low32step; auto.
          dostep_nary_eliml 0 1. eapply r_local_get; eassumption.
          dostep_nary_eliml 1 1. eapply r_load_success; eassumption.
          rewrite Hbsy.
          dostep_nary_eliml 2 1. apply high32step; auto.
          dostep_nary 2. constructor. apply rs_binop_success; first done. cbn.
          rewrite max32bit_mul_modulo64_id; try apply low32_max_int32. reflexivity.
          unfold hi. apply high32_max_int32; auto.
          dostep_nary 1. eapply r_global_set'; eassumption.
          dostep_nary 0. eapply r_local_get; eassumption.
          dostep_nary 1. eapply r_load_success; eassumption.
          rewrite Hbsx.
          dostep_nary 2. apply high32step; auto.
          dostep_nary_eliml 0 1. eapply r_local_get; eassumption.
          dostep_nary_eliml 1 1. eapply r_load_success; eassumption.
          rewrite Hbsy.
          dostep_nary_eliml 2 1. apply high32step; auto.
          dostep_nary 2. constructor. apply rs_binop_success; first done. cbn.
          rewrite max32bit_mul_modulo64_id; auto.
          unfold hi; apply high32_max_int32; auto. unfold hi; apply high32_max_int32; auto.
          dostep_nary 1. eapply r_global_set'; eassumption.
          dostep_nary 0. eapply r_global_get; eassumption.
          dostep_nary 2. constructor. apply rs_binop_success; first done. cbn.
          rewrite int64_high32; auto. have Hb := lo_lo_product_63bit _ _ Hb1 Hb2; lia.
          replace ((lo (to_Z n1) * lo (to_Z n2))%Z / 2^32)%Z with (hi (lo (to_Z n1) * lo (to_Z n2))%Z) by auto.
          dostep_nary_eliml 0 1. eapply r_global_get; eassumption.
          dostep_nary_eliml 2 1. constructor. apply rs_binop_success; first done. cbn.
          rewrite int64_low32'; auto. have Hb := hi_lo_product_63bit _ _ Hb1 Hb2; lia.
          replace ((hi (to_Z n1) * lo (to_Z n2))%Z mod 2^32)%Z with (lo ((hi (to_Z n1) * lo (to_Z n2))%Z)) by auto.
          dostep_nary 2. constructor. apply rs_binop_success; first done. cbn.
          rewrite sum1_i64; auto.
          dostep_nary_eliml 0 1. eapply r_global_get; eassumption.
          dostep_nary 2. constructor. apply rs_binop_success; first done. cbn.
          rewrite cross_i64; auto.
          replace (hi (lo (to_Z n1) * lo (to_Z n2))%Z + lo (hi (to_Z n1) * lo (to_Z n2))%Z + (lo (to_Z n1) * hi (to_Z n2))%Z)%Z with crs.
          dostep_nary 1. eapply r_global_set'; eassumption.
          dostep_nary 0. eapply r_global_get; eassumption.
          dostep_nary 2. apply high32step; auto.
          have Hb := hi_lo_product_63bit _ _ Hb1 Hb2; lia.
          dostep_nary_eliml 0 1. eapply r_global_get; eassumption.
          dostep_nary_eliml 2 1. apply high32step; auto.
          have Hb := cross_range _ _ Hb1 Hb2. lia.
          dostep_nary 2. constructor. apply rs_binop_success; first done. cbn.
          rewrite Hcrs. rewrite sum2_i64; auto.
          dostep_nary_eliml 0 1. eapply r_global_get; eassumption.
          dostep_nary 2. constructor. apply rs_binop_success; first done. cbn.
          rewrite upper_i64; auto.
          replace (hi (hi (to_Z n1) * lo (to_Z n2))%Z + hi (cross (to_Z n1) (to_Z n2)) + (hi (to_Z n1) * hi (to_Z n2))%Z)%Z with hi64.
          dostep_nary 1. eapply r_global_set'; eassumption.
          dostep_nary 0. eapply r_global_get; eassumption.
          dostep_nary 2. constructor. apply rs_binop_success; first done. cbn.
          unfold Int64.ishl.
          replace (Int64.unsigned (Z_to_i64 32)) with 32%Z by now cbn.
          replace (32 mod Int64.wordsize)%Z with 32%Z by now cbn.
          reflexivity.
          dostep_nary_eliml 0 1. eapply r_global_get; eassumption.
          dostep_nary_eliml 2 1. apply low32step.
          have Hb := lo_lo_product_63bit _ _ Hb1 Hb2; lia.
          dostep_nary 2. constructor. apply rs_binop_success; first done. cbn.
          rewrite Hcrs. rewrite lower_or_i64; auto.
          replace (cross (to_Z n1) (to_Z n2) * 2 ^ 32 + lo (lo (to_Z n1) * lo (to_Z n2))%Z)%Z with lo64.
          dostep_nary 1. eapply r_global_set'; eauto.
          dostep_nary 0. eapply r_global_get; eauto.
          dostep_nary 2. constructor. apply rs_binop_success; first done. cbn.
          rewrite Hhi64. rewrite upper_shifted_i64; auto.
          dostep_nary_eliml 0 1. eapply r_global_get; eauto.
          dostep_nary_eliml 2 1. constructor. apply rs_binop_success; first done. cbn.
          rewrite Hlo64. rewrite lower_shifted_i64; auto.
          dostep_nary 2. constructor. apply rs_binop_success; first done.
          cbn. rewrite upper63_i64; auto.
          replace (upper (to_Z n1) (to_Z n2) * 2 + lower (to_Z n1) (to_Z n2) mod 2 ^ 64 / 2 ^ 63)%Z with hi63.
          dostep_nary 1. eapply r_global_set'; eassumption.
          dostep_nary 0. eapply r_global_get; eassumption.
          dostep_nary 2. constructor. apply rs_binop_success; first done. cbn.
          rewrite int64_bitmask_modulo.
          replace (lo64 mod wB)%Z with lo63; auto.
          rewrite Hlo63 Hlo64. reflexivity.
          dostep_nary 1. eapply r_global_set'; eassumption.
          simpl. rewrite map_cat. eapply rt_trans. apply app_trans. apply Hred.
          dostep_nary' 1. eapply r_local_set' with (f':=fr'); eauto.
          now apply rt_refl. }
        repeat (split; auto).
        { (* minimum mem *)
          intros ?????.
          solve_eq m' m0.
          assert (gmp = gmp_v + 28)%N. {
            rewrite Hgmp' in H9.
            inv H9. now simpl_eq. } subst gmp.
          lia.
        }
        now exists (Val_ptr (gmp_v + 16)%N). }
    - { (* diveucl *)
        inversion H1; subst x1 y0.
        inversion Hres as [Hv_diveucl].
        have I := Hinv. destruct I as [_ [_ [_ [_ [_ [_ [_ [_ [_ [_ [HnoGlobDups [_ [_ [Hmult2 [_ Hi64tempsW]]]]]]]]]]]]]]].
        assert (Hglob_tmp1: i64_glob glob_tmp1) by now constructor. assert (Hglob_tmp2: i64_glob glob_tmp2) by now right; constructor.
        destruct (Hi64tempsW glob_tmp1 Hglob_tmp1 (VAL_int64 (Int64.repr (to_Z (fst (diveucl n1 n2)%uint63))))) as [sr1 HupdGlob1].
        assert (HINV1: INV fenv nenv sr1 f) by now eapply update_global_preserves_INV with (sr:=s) (sr':=sr1) (i:=glob_tmp1) (num:=(VAL_int64 (Int64.repr (to_Z (fst (diveucl n1 n2)%uint63))))); eauto; [discriminate|now intros|now intros].
        have Hmem_sr1 := update_global_preserves_memory _ _ _ _ _ HupdGlob1. symmetry in Hmem_sr1. rewrite Hmem2 in Hmem_sr1.
        have I := HINV1. destruct I as [_ [_ [_ [_ [_ [_ [_ [_ [_ [_ [_ [_ [_ [_ [_ Hi64tempsW1]]]]]]]]]]]]]]].
        destruct (Hi64tempsW1 glob_tmp2 Hglob_tmp2 (VAL_int64 (Int64.repr (to_Z (snd (diveucl n1 n2)%uint63))))) as [sr2 HupdGlob2].
        assert (Hrange' : (-1 < Z.of_N gmp_v < Int32.modulus)%Z) by lia.
        destruct (Hmult2 gmp_v m Hmem2 Hgmp Hrange') as [n0 Hn0].
        assert (HINV2: INV fenv nenv sr2 f). {
          eapply update_global_preserves_INV; eauto.
          right; split; [right; now constructor|now cbn]. discriminate.
          now intros.
          now intros. }
        have Hmem_sr2 := update_global_preserves_memory _ _ _ _ _ HupdGlob2. symmetry in Hmem_sr2. rewrite Hmem_sr1 in Hmem_sr2.
        unfold INV_inst_globals_nodup in HnoGlobDups.
        assert (Hgmp_sr1 : sglob_val sr1 (f_inst f) glob_mem_ptr = Some (VAL_num (VAL_int32 (N_to_i32 gmp_v)))) by now eapply update_global_get_other; eauto; discriminate.
        assert (Hgmp_sr2 : sglob_val sr2 (f_inst f) glob_mem_ptr = Some (VAL_num (VAL_int32 (N_to_i32 gmp_v)))) by now eapply update_global_get_other; eauto; discriminate.
        assert (HenoughMem : (Z.of_N gmp_v + Z.of_N 52 <= Z.of_N (mem_length m) < Int32.modulus)%Z) by now unfold page_size in *; lia.
        assert (Htmp1_sr1 : sglob_val sr1 (f_inst f) glob_tmp1 = Some (VAL_num (VAL_int64 (Int64.repr (to_Z (fst (diveucl n1 n2)%uint63)))))) by now eapply update_global_get_same with (sr:=s); eauto.
        assert (Htmp1_sr2 : sglob_val sr2 (f_inst f) glob_tmp1 = Some (VAL_num (VAL_int64 (Int64.repr (to_Z (fst (diveucl n1 n2)%uint63)))))) by now eapply update_global_get_other with(sr:=sr1); eauto.
        assert (Htmp2_sr2 : sglob_val sr2 (f_inst f) glob_tmp2 = Some (VAL_num (VAL_int64 (Int64.repr (to_Z (snd (diveucl n1 n2)%uint63)))))) by now eapply update_global_get_same with(sr:=sr1); eauto.

        have HmakeProdReduce := make_product_reduce glob_tmp1 glob_tmp2 state sr2 f m gmp_v (to_Z (fst (diveucl n1 n2))) (to_Z (snd (diveucl n1 n2)))
                                  Hglob_tmp1 Hglob_tmp2 HINV2 Hmem_sr2 Hgmp_sr2 HenoughMem Htmp1_sr2 Htmp2_sr2.

        destruct HmakeProdReduce as [sr' [m' [Hred [HINV' [Hmem' [Hgmp' [Hloadp1 [Hloadp2 [Hloadord [Hloadp1addr [Hloadp2addr [Hloadi32s [Hloadi64s [Hsfuncs Hmemlen']]]]]]]]]]]]]].
        assert (Hsfs': s_funcs s = s_funcs sr'). {
          apply update_global_preserves_funcs in HupdGlob1.
          apply update_global_preserves_funcs in HupdGlob2.
          now rewrite ->HupdGlob1, ->HupdGlob2. }
        assert (Hlocx0' : N.to_nat x0' < length (f_locs f)) by now eapply (HlocsInBounds x0 x0' Hrepr_x).

        remember
       {| f_locs :=
           set_nth (VAL_num (VAL_int32 (wasm_value_to_i32 (Val_ptr (gmp_v + 16)%N)))) (f_locs f) (N.to_nat x0') (VAL_num (VAL_int32 (wasm_value_to_i32 (Val_ptr (gmp_v + 16)%N))));
         f_inst := f_inst f
       |} as fr'.
        assert (f_inst f = f_inst fr') by now subst fr'.
        assert (Hlocx0'_fr' : N.to_nat x0' < length (f_locs fr')). {
          assert (length (f_locs fr') = length (f_locs f)). {
            subst fr'.
            eapply set_nth_length.
            apply /ssrnat.leP. lia. }
          replace (length (f_locs fr')) with (length (f_locs f)).
          now eapply (HlocsInBounds x0 x0' Hrepr_x). }
        assert (HlocsLe: ssrnat.leq (S (N.to_nat x0')) (Datatypes.length (f_locs f))) by now apply /ssrnat.leP; lia.
        assert (HnewframeLoc: f_locs fr' = set_nth (VAL_num (VAL_int32 (wasm_value_to_i32 (Val_ptr (gmp_v + 16)%N)))) (f_locs f) (N.to_nat x0') (VAL_num (VAL_int32 (wasm_value_to_i32 (Val_ptr (gmp_v + 16)%N))))) by now subst fr'.
        assert (HvalRelp1 : repr_val_LambdaANF_Wasm cenv fenv nenv penv (Vprim (AstCommon.primInt ; fst (diveucl n1 n2))) sr' (f_inst fr') (Val_ptr gmp_v)). {
          unfold page_size in *.
          apply Rprim_v with (sr:=sr') (gmp:=(gmp_v + 28)%N) (m:=m') (addr:=gmp_v); subst fr'; auto; try lia.
          exists n0; lia. }

        assert (HvalRelp2 : repr_val_LambdaANF_Wasm cenv fenv nenv penv (Vprim (AstCommon.primInt ; snd (diveucl n1 n2))) sr' (f_inst fr') (Val_ptr (gmp_v + 8)%N)). {
          unfold page_size in *.
          apply Rprim_v with (sr:=sr') (gmp:=(gmp_v + 28)%N) (m:=m') (addr:=(gmp_v+8)%N); subst fr'; auto; try lia.
          exists (n0+4)%N; lia. }

        assert (HvalsPreserved : forall wal val,
                   repr_val_LambdaANF_Wasm cenv fenv nenv penv val s (f_inst f) wal -> repr_val_LambdaANF_Wasm cenv fenv nenv penv val sr' (f_inst fr') wal). {
          intros.
          unfold page_size in *.
          eapply val_relation_depends_on_mem_smaller_than_gmp_and_funcs with (sr:=s) (m:=m) (gmp:=gmp_v) (gmp':=(gmp_v + 28)%N); subst fr'; eauto; try lia.  }
        assert (HvalRelPair : repr_val_LambdaANF_Wasm cenv fenv nenv penv (LambdaANF_primInt_prod_fun pair_tag diveucl n1 n2) sr' (f_inst fr') (Val_ptr (gmp_v + 16)%N)). {
          unfold page_size in *.
          apply Rconstr_boxed_v with (v:=N_to_i32 pair_ord) (gmp:=(gmp_v+28)%N) (m:=m') (arity:=2) (ord:=0%N); subst fr'; auto; try lia.
          unfold get_ctor_ord; now rewrite Hpair.
          unfold get_ctor_arity; now rewrite Hpair.
          exists (n0 + 8)%N; lia.
          apply Rcons_l with (wal:=Val_ptr gmp_v) (m:=m') (addr:=(4 + (gmp_v+16))%N) (gmp:=(gmp_v+28)%N); auto; try lia.
          replace (4 + (gmp_v + 16))%N with (gmp_v + 20)%N by lia. unfold wasm_value_to_i32, wasm_value_to_u32. now unfold N_to_i32 in Hloadp1addr.
          apply Rcons_l with (wal:=Val_ptr (gmp_v + 8)%N) (m:=m') (addr:=(4 + (4 + (gmp_v+16)))%N) (gmp:=(gmp_v+28)%N); auto; try lia.
          replace (4 + (4 + (gmp_v + 16)))%N with (gmp_v + 24)%N by lia. unfold wasm_value_to_i32, wasm_value_to_u32. now unfold N_to_i32 in Hloadp2addr.
          now apply Rnil_l. }

        assert (HINV'' : INV fenv nenv sr' fr') by now eapply update_local_preserves_INV; eauto.
        assert (rel_env_LambdaANF_Wasm (lenv:=lenv)  cenv fenv nenv penv e (M.set x0 (LambdaANF_primInt_prod_fun pair_tag diveucl n1 n2) rho) sr' fr' fds). {
          have Hl := HlocsInBounds _ _ Hrepr_x.
          apply nth_error_Some in Hl.
          apply notNone_Some in Hl. destruct Hl as [? Hlx].
          unfold rel_env_LambdaANF_Wasm.
          destruct HrelE as [Hfun1 [Hfun2 Hvar]].
          split. {
            intros ????? Hrho Hv'.
            destruct (var_dec x0 x2).
            - (* x0 = x1 *) (* v0 can never be a function value, by assumption on primops *)
              subst x2. rewrite M.gss in Hrho; eauto.
              inversion Hrho as [Hv_diveucl']. subst v0. rewrite Hv_diveucl in Hv'.
              have H'' := Hnofunval rho' fds' f0.
              contradiction.
            - (* x0 <> x1 *) rewrite M.gso in Hrho; eauto.
          } split. {
            intros ? Hnfd. apply Hfun2 in Hnfd.
            destruct Hnfd as [i' [Htrans HvalFun]].
            exists i'. split. assumption.
            apply val_relation_func_depends_on_funcs with (s:=s); subst fr'; auto.
          }
          intros x2 Hx2free Hx2notfun.
          destruct (var_dec x0 x2).
          { (* x = x1 *)
            subst x2.
            exists v, (Val_ptr (gmp_v+16)%N).
            rewrite M.gss. split; auto.
            split.
            exists x0'. cbn. split. assumption.
            unfold lookup_N; cbn; auto.
            subst fr'. cbn.
            eapply set_nth_nth_error_same; eauto. rewrite <-Hv_diveucl. assumption.
          }
          { (* x <> x1 *)
            assert (Hocc : occurs_free (Eprim x0 p [:: x ; y] e) x2) by now apply Free_Eprim2.
            have H' := Hvar _ Hocc Hx2notfun.
            destruct H' as [val' [wal' [Hrho [Hloc Hval']]]].
            exists val', wal'. split.
            rewrite M.gso; auto. split.
            destruct Hloc as [i' [Hl1 Hl2]].
            unfold stored_in_locals. exists i'. split; auto.
            unfold lookup_N.
            subst fr'; rewrite set_nth_nth_error_other; auto.

            intro. assert (x0' = i') by lia. subst x0'.
            have Hcontra := repr_var_inj _ _ _ _ HlenvInjective Hl1 Hrepr_x.
            contradiction.

            now apply HvalsPreserved.
          }
        }
        exists sr', fr'.
        split. { (* Instructions reduce *)
          unfold diveucl_instrs.
          remember (make_product glob_mem_ptr glob_tmp1 glob_tmp2) as make_product_instrs.
          separate_instr.
          eapply rt_trans. apply HloadStep1.
          dostep_nary 1. constructor. apply rs_testop_i64.
          destruct (Z.eq_dec (to_Z n1) (to_Z 0)) as [Hn1eq0 | Hn1eq0].
          {
            assert (to_Z (fst (diveucl n1 n2)) = 0%Z /\ to_Z (snd (diveucl n1 n2)) = 0%Z). { rewrite diveucl_def_spec. unfold diveucl_def. rewrite div_spec. rewrite mod_spec. rewrite Hn1eq0. unfold Z.div, Z.div_eucl. split; reflexivity. }
            destruct H7 as [Hfst0 Hsnd0].
            dostep_nary 1. constructor. apply rs_if_true. unfold wasm_bool.
            replace Int64.zero with (Int64.repr (to_Z 0)) by now cbn.
            rewrite uint63_eq_int64_eq; auto. discriminate.
            rewrite Hfst0 in HupdGlob1.
            dostep_nary 0. eapply r_block with (t1s:=[::]) (t2s:=[::])(vs:=[::]); eauto.
            eapply rt_trans. eapply app_trans.
            apply reduce_trans_label0.
            dostep_nary 1. eapply r_global_set'; eauto.
            dostep_nary' 1. rewrite Hsnd0 in HupdGlob2. eapply r_global_set'; eauto.
            apply rt_refl.
            dostep_nary 0. constructor. apply rs_label_const; auto.
            simpl. rewrite map_cat. eapply rt_trans. apply app_trans. apply Hred.
            dostep_nary' 1. eapply r_local_set' with (f':=fr'); eauto.
            now apply rt_refl. }
          {
            dostep_nary 1. constructor. apply rs_if_false. unfold wasm_bool.
            replace Int64.zero with (Int64.repr (to_Z 0)) by now cbn.
            rewrite uint63_neq_int64_neq. auto. auto.
            dostep_nary 0. eapply r_block with (t1s:=[::]) (t2s:=[::])(vs:=[::]); eauto.
            eapply rt_trans. eapply app_trans.
            separate_instr.
            apply reduce_trans_label0.
            eapply rt_trans. apply HloadStep2.
            dostep_nary 1. constructor. apply rs_testop_i64.
            destruct (Z.eq_dec (to_Z n2) (to_Z 0)) as [Hn2eq0 | Hn2eq0].
            {
              destruct (uint63_diveucl_0 n1 n2 Hn2eq0) as [Hfst0 Hsnd0].
              dostep_nary' 1. constructor. apply rs_if_true. unfold wasm_bool.
              replace Int64.zero with (Int64.repr (to_Z 0)) by now cbn.
              rewrite uint63_eq_int64_eq; auto. discriminate.
              rewrite Hfst0 in HupdGlob1.
              dostep_nary' 0. eapply r_block with (t1s:=[::]) (t2s:=[::])(vs:=[::]); eauto.
              separate_instr.
              apply reduce_trans_label0.
              dostep_nary' 1. eapply r_global_set'; eauto.
              separate_instr.
              dostep_nary' 0. eapply r_local_get; eauto.
              dostep_nary' 1. eapply r_load_success; eauto. rewrite Hbsx.
              dostep_nary' 1. rewrite Hsnd0 in HupdGlob2. eapply r_global_set'; eauto.
              apply rt_refl. }
            {
              assert (Hdiveucl_n2neq0 : to_Z (fst (diveucl n1 n2)) = to_Z (n1 / n2) /\ to_Z (snd (diveucl n1 n2)) = to_Z (n1 mod n2)) by now rewrite diveucl_def_spec; unfold diveucl_def; simpl.
              destruct Hdiveucl_n2neq0 as [Hfst Hsnd].
              dostep_nary' 1. constructor. apply rs_if_false. unfold wasm_bool.
              replace Int64.zero with (Int64.repr (to_Z 0)) by now cbn.
              rewrite uint63_neq_int64_neq; auto.
              dostep_nary' 0. eapply r_block with (t1s:=[::]) (t2s:=[::])(vs:=[::]); eauto.
              apply reduce_trans_label0.
              dostep_nary' 0. eapply r_local_get; eassumption.
              dostep_nary' 1. eapply r_load_success; eauto. rewrite Hbsx.
              dostep_nary_eliml 0 1. eapply r_local_get; eassumption.
              dostep_nary_eliml 1 1. eapply r_load_success; eassumption. rewrite Hbsy.
              dostep_nary' 2. constructor. apply rs_binop_success; first done. simpl.
              rewrite uint63_div_i64_div; simpl; auto.
              rewrite Hfst in HupdGlob1.
              dostep_nary' 1. eapply r_global_set'; eassumption.
              dostep_nary' 0. eapply r_local_get; eassumption.
              dostep_nary' 1. eapply r_load_success; eassumption. rewrite Hbsx.
              dostep_nary_eliml 0 1. eapply r_local_get; eassumption.
              dostep_nary_eliml 1 1. eapply r_load_success; eassumption. rewrite Hbsy.
              dostep_nary' 2. constructor. apply rs_binop_success; first done. simpl.
              rewrite uint63_mod_i64_mod; simpl; auto.
              rewrite Hsnd in HupdGlob2.
              dostep_nary' 1. eapply r_global_set'; eassumption.
              apply rt_refl. }
            reduce_under_label.
            apply reduce_trans_label0.
            dostep_nary' 0. constructor. apply rs_label_const; auto. apply rt_refl.
            dostep_nary' 0. constructor. apply rs_label_const; auto.
            rewrite map_cat. simpl.
            eapply rt_trans with (y:=(state, sr', f, ?[es1] ++ ?[es2])).
            apply app_trans. apply Hred.
            apply rt_step. eapply r_local_set'; eauto. } }
        repeat (split; auto).
        { (* minimum mem *)
           intros ?????.
           solve_eq m' m0.
           assert (gmp = gmp_v + 28)%N. {
             rewrite Hgmp' in H9.
             inv H9. now simpl_eq. } subst gmp.
           lia.
         }
        now exists (Val_ptr (gmp_v + 16)%N). } }
  {
    (* Ternary operations *)
    rename H into Hrepr_arg1, H0 into Hrepr_arg2, H1 into Hrepr_arg3, H2 into Hrepr_primop.
    assert (exists n1 n2 n3,
               rho ! x = Some (Vprim (primInt n1))
               /\ rho ! y = Some (Vprim (primInt n2))
               /\ rho ! z = Some (Vprim (primInt n3))
               /\ vs = [ Vprim (primInt n1) ; Vprim (primInt n2) ; Vprim (primInt n3) ]
           ). {
      destruct Hpfs' as  [? [? [? [? [? [? [? [? [? [? [? [? [Hres _]]]]]]]]]]]]].
      unfold get_list in *.
      destruct (rho ! x) eqn:Hrho_x. 2: discriminate.
      destruct (rho ! y) eqn:Hrho_y. 2: discriminate.
      destruct (rho ! z) eqn:Hrho_z. 2: discriminate.
      assert (Hin1 : List.In v0 vs) by (inv Hys_vs; now constructor).
      assert (Hin2 : List.In v1 vs) by (inv Hys_vs; right; now constructor).
      assert (Hin3 : List.In v2 vs) by (inv Hys_vs; right; right; now constructor).
      destruct (apply_primop_only_defined_on_primInts _ vs v _ _ _ _ _ _ _ _ Hres v0 Hin1) as [n1 Hn1].
      destruct (apply_primop_only_defined_on_primInts _ vs v _ _ _ _ _ _ _ _ Hres v1 Hin2) as [n2 Hn2].
      destruct (apply_primop_only_defined_on_primInts _ vs v _ _ _ _ _ _ _ _ Hres v2 Hin3) as [n3 Hn3].
      exists n1, n2, n3.
      split; subst; auto.
      split; subst; auto.
      split; subst; auto.
      congruence. }
    destruct H as [n1 [n2 [n3 [Hrho_x [Hrho_y [Hrho_z Hvs]]]]]].
    assert (exists wal1,
               stored_in_locals (lenv:=lenv) nenv x wal1 f /\ repr_val_LambdaANF_Wasm  cenv fenv nenv penv (Vprim ( primInt n1)) s (f_inst f) wal1). {
      destruct HrelE as [_ [_ Hvars]].
      assert (occurs_free (Eprim x0 p [:: x ; y ; z ] e) x) by now (constructor; constructor).
      assert (HfdsNone_x: find_def x fds = None). {
        inv Hrepr_arg1.
        unfold translate_var in H0.
        destruct (lenv ! x) eqn:Hx. 2: now rewrite Hx in H0.
        unfold domains_disjoint in Hdisjoint.
        apply Hdisjoint in Hx.
        apply HfenvWf_None with (f:=x) in HfenvWf. now rewrite HfenvWf.
      }
      have Hx := Hvars _ H HfdsNone_x. destruct Hx as [v1' [w1 [Hrho_x' [Hloc_x Hval_x]]]].
      exists w1; split; auto.
      now replace v1' with (Vprim (primInt n1)) in Hval_x by now rewrite Hrho_x in Hrho_x'; inv Hrho_x'.
    }
    destruct H as [wal1 [Hloc_x Hval_x]].
    assert (exists wal2,
               stored_in_locals (lenv:=lenv) nenv  y wal2 f /\ repr_val_LambdaANF_Wasm  cenv fenv nenv penv (Vprim (primInt n2)) s (f_inst f) wal2). {
      destruct HrelE as [_ [_ Hvars]].
      assert (occurs_free (Eprim x0 p [:: x ; y ; z ] e) y) by now (constructor; right; constructor).
      assert (HfdsNone_y: find_def y fds = None). {
        inv Hrepr_arg2.
        unfold translate_var in H0.
        destruct (lenv ! y) eqn:Hy. 2: now rewrite Hy in H0.
        unfold domains_disjoint in Hdisjoint.
        apply Hdisjoint in Hy.
        apply HfenvWf_None with (f:=y) in HfenvWf. now rewrite HfenvWf.
      }
      have Hy := Hvars _ H HfdsNone_y. destruct Hy as [v2' [w2 [Hrho_y' [Hloc_y Hval_y]]]].
      exists w2; split; auto.
      now replace v2' with (Vprim (primInt n2)) in Hval_y by now rewrite Hrho_y in Hrho_y'; inv Hrho_y'.
    }
    destruct H as [wal2 [Hloc_y Hval_y]].
    assert (exists wal3,
               stored_in_locals (lenv:=lenv) nenv z wal3 f /\ repr_val_LambdaANF_Wasm  cenv fenv nenv penv (Vprim (primInt n3)) s (f_inst f) wal3). {
      destruct HrelE as [_ [_ Hvars]].
      assert (occurs_free (Eprim x0 p [:: x ; y ; z ] e) z) by now (constructor; right; right; constructor).
      assert (HfdsNone_z: find_def z fds = None). {
        inv Hrepr_arg3.
        unfold translate_var in H0.
        destruct (lenv ! z) eqn:Hz. 2: now rewrite Hz in H0.
        unfold domains_disjoint in Hdisjoint.
        apply Hdisjoint in Hz.
        apply HfenvWf_None with (f:=z) in HfenvWf. now rewrite HfenvWf.
      }
      have Hz := Hvars _ H HfdsNone_z. destruct Hz as [v3' [w3 [Hrho_z' [Hloc_z Hval_z]]]].
      exists w3; split; auto.
      now replace v3' with (Vprim (primInt n3)) in Hval_z by now rewrite Hrho_z in Hrho_z'; inv Hrho_z'.
    }
    destruct H as [wal3 [Hloc_z Hval_z]].
    destruct Hloc_x as [? [Htrans Hx']].
    assert (x1 = x'). { eapply repr_var_det; eassumption. } subst x1. clear Htrans.
    destruct Hloc_y as [? [Htrans Hy']].
    assert (x1 = y'). { eapply repr_var_det; eassumption. }  subst x1. clear Htrans.
    destruct Hloc_z as [? [Htrans Hz']].
    assert (x1 = z'). { eapply repr_var_det; eassumption. } subst x1. clear Htrans.
    assert (Hrv1: exists addr1, wal1 = Val_ptr addr1
               /\ load_i64 m addr1 = Some (VAL_int64 (Z_to_i64 (to_Z n1)))). {
      inv Hval_x. replace m with m0 by congruence. exists addr. split; auto.
      remember (primInt n) as p1; remember (primInt n1) as p2.
      inversion H5; subst p1 p2.
      now replace n1 with n by now apply Classical_Prop.EqdepTheory.inj_pair2 in H7.
    }
    destruct Hrv1 as [addr1 Hload1].
    destruct Hload1 as [? Hload1]. subst wal1.
    unfold load_i64 in Hload1. destruct (load m addr1 0%N 8) eqn:Hload1'. 2: discriminate.
    assert (Haddr1: addr1 = (Wasm_int.N_of_uint i32m (wasm_value_to_i32 (Val_ptr addr1)))). {
      cbn. rewrite Wasm_int.Int32.Z_mod_modulus_id. now rewrite N2Z.id.
      inv Hval_x. lia. }
    assert (Hrv2: exists addr2, wal2 = Val_ptr addr2
               /\ load_i64 m addr2 = Some (VAL_int64 (Z_to_i64 (to_Z n2)))). {
      inv Hval_y. replace m with m0 by congruence. exists addr. split; auto.
      remember (primInt n) as p1; remember (primInt n2) as p2.
      inversion H5; subst p1 p2.
      now replace n2 with n by now apply Classical_Prop.EqdepTheory.inj_pair2 in H7.
    }
    destruct Hrv2 as [addr2 Hload2].
    destruct Hload2 as [? Hload2]. subst wal2.
    unfold load_i64 in Hload2. destruct (load m addr2 0%N 8) eqn:Hload2'. 2: discriminate.
    assert (Haddr2: addr2 = (Wasm_int.N_of_uint i32m (wasm_value_to_i32 (Val_ptr addr2)))). {
      cbn. rewrite Wasm_int.Int32.Z_mod_modulus_id. now rewrite N2Z.id.
      inv Hval_y. lia. }
    assert (Hrv3: exists addr3, wal3 = Val_ptr addr3
               /\ load_i64 m addr3 = Some (VAL_int64 (Z_to_i64 (to_Z n3)))). {
      inv Hval_z. replace m with m0 by congruence. exists addr. split; auto.
      remember (primInt n) as p1; remember (primInt n3) as p2.
      inversion H5; subst p1 p2.
      now replace n3 with n by now apply Classical_Prop.EqdepTheory.inj_pair2 in H7.
    }
    destruct Hrv3 as [addr3 Hload3].
    destruct Hload3 as [? Hload3]. subst wal3.
    unfold load_i64 in Hload3. destruct (load m addr3 0%N 8) eqn:Hload3'. 2: discriminate.
    assert (Haddr3 : addr3 = (Wasm_int.N_of_uint i32m (wasm_value_to_i32 (Val_ptr addr3)))). {
      cbn. rewrite Wasm_int.Int32.Z_mod_modulus_id. now rewrite N2Z.id.
      inv Hval_z. lia. }
    destruct Hpfs' as
      [true_tag [false_tag [bool_tag [eq_tag [lt_tag [gt_tag [comp_tag [c0_tag [c1_tag [carry_tag [pair_tag [prod_tag [Hres [Htrue [Hfalse [Heq [Hlt [Hgt [Hc0 [Hc1 Hpair]]]]]]]]]]]]]]]]]]]].
    assert (Hflocs: N.to_nat x0' < Datatypes.length (f_locs f)) by now eapply HlocsInBounds; eauto.
    assert (HgmpBounds: (Z.of_N gmp_v + Z.of_N 52 <= Z.of_N (mem_length m) < Int32.modulus)%Z). {
      apply mem_length_upper_bound in Hmem5. cbn in Hmem5.
      simpl_modulus. cbn. cbn in HenoughM. lia. }
    rewrite Hvs in Hres.
    unfold apply_LambdaANF_primInt_operator in Hres.
    destruct op;
      ltac:(match goal with | [ H : None = Some _  |- _ ] => discriminate | _ => idtac end).
    { (* diveucl_21 *)
      inversion Hres as [Hv_div21].
      clear Hres.
      clear Htrue Hfalse Hc0 Hc1 Heq Hlt Hgt true_tag false_tag bool_tag eq_tag lt_tag gt_tag comp_tag carry_tag c0_tag c1_tag.
      rename x into arg1, y into arg2, z into arg3.
      rename n1 into xh, n2 into xl, n3 into y.
      have I := Hinv. destruct I as [_ [_ [_ [_ [_ [_ [_ [_ [_ [_ [HnoGlobDups [_ [_ [Hmult2 [_ Hi64tempsW]]]]]]]]]]]]]]].
      assert (Hglob_tmp1: i64_glob glob_tmp1) by (cbn; tauto).
      assert (Hglob_tmp2: i64_glob glob_tmp2) by (cbn; tauto).
      assert (Hglob_tmp3: i64_glob glob_tmp3) by (cbn; tauto).
      assert (Hglob_tmp4: i64_glob glob_tmp4) by (cbn; tauto).
      assert (Hrelations : forall sr gidx1 gidx2 quot rem,
                 INV fenv nenv sr f ->
                 i64_glob gidx1 -> i64_glob gidx2 ->
                 v = Vconstr pair_tag [Vprim (AstCommon.primInt ; quot) ; Vprim (AstCommon.primInt ; rem)] ->
                 sglob_val sr (f_inst f) gidx1 = Some (VAL_num (VAL_int64 (Int64.repr (to_Z quot)))) ->
                 sglob_val sr (f_inst f) gidx2 = Some (VAL_num (VAL_int64 (Int64.repr (to_Z rem)))) ->
                 sglob_val sr (f_inst f) glob_mem_ptr = Some (VAL_num (VAL_int32 (N_to_i32 gmp_v))) ->
                 s_funcs s = s_funcs sr ->
                 smem sr (f_inst f) = Some m ->
                 exists s' fr,
                   reduce_trans
                        (state, sr, f, map AI_basic (make_product glob_mem_ptr gidx1 gidx2))
                        (state, s', f, [:: $V VAL_num (VAL_int32 (N_to_i32 (gmp_v + 16)))])
                   /\ reduce_trans
                        (state, s', f, [:: $V VAL_num (VAL_int32 (N_to_i32 (gmp_v + 16)))] ++ [AI_basic (BI_local_set x0')])
                        (state, s', fr, [])
                   /\ INV fenv nenv s' fr
                   /\ f_inst f = f_inst fr
                   /\ s_funcs s = s_funcs s'
                   /\ min_available_memory s' (f_inst f) mem
                   /\    rel_env_LambdaANF_Wasm (lenv:=lenv) cenv fenv nenv penv e
                           (M.set x0 v rho) s' fr fds
                   /\  (forall (wal : wasm_value) (val : val),
                         repr_val_LambdaANF_Wasm  cenv fenv nenv penv val s (f_inst f) wal ->
                         repr_val_LambdaANF_Wasm  cenv fenv nenv penv val s' (f_inst fr) wal)
                   /\ (exists wal : wasm_value,
                          fr =
                            {| f_locs :=
                                set_nth (VAL_num (VAL_int32 (wasm_value_to_i32 wal)))
                                  (f_locs f) (N.to_nat x0') (VAL_num (VAL_int32 (wasm_value_to_i32 wal)));
                              f_inst := f_inst f
                            |}
                          /\
                            repr_val_LambdaANF_Wasm  cenv fenv nenv penv v s'
                              (f_inst fr) wal)).
      { intros sr gidx1 gidx2 quot rem HINV_sr Hgidx1 Hgidx2 Hv Hp1 Hp2 Hgmp_sr Hsf_sr Hmem_sr.
        have HmakeProdReduce := make_product_reduce gidx1 gidx2 state sr f m gmp_v _ _ Hgidx1 Hgidx2 HINV_sr Hmem_sr Hgmp_sr HgmpBounds Hp1 Hp2.
        destruct HmakeProdReduce as [sr' [m' [Hred [HINV' [Hmem' [Hgmp' [Hloadp1 [Hloadp2 [Hloadord [Hloadp1addr [Hloadp2addr [Hloadi32s [Hloadi64s [Hsfuncs Hmemlen']]]]]]]]]]]]]].
        rewrite <- Hsf_sr in Hsfuncs.
      assert (Hrange' : (-1 < Z.of_N gmp_v < Int32.modulus)%Z) by lia.
      destruct (Hmult2 gmp_v m Hmem2 Hgmp Hrange') as [n0 Hn0].
        remember
       {| f_locs :=
           set_nth (VAL_num (VAL_int32 (wasm_value_to_i32 (Val_ptr (gmp_v + 16)%N)))) (f_locs f) (N.to_nat x0') (VAL_num (VAL_int32 (wasm_value_to_i32 (Val_ptr (gmp_v + 16)%N))));
         f_inst := f_inst f
       |} as fr'.
        assert (f_inst f = f_inst fr') by now subst fr'.
        assert (Hlocx0'_fr' : N.to_nat x0' < length (f_locs fr')). {
          assert (length (f_locs fr') = length (f_locs f)). {
            subst fr'.
            eapply set_nth_length.
            apply /ssrnat.leP. lia. }
          replace (length (f_locs fr')) with (length (f_locs f)).
          now eapply (HlocsInBounds x0 x0' Hrepr_x). }
        assert (HlocsLe: ssrnat.leq (S (N.to_nat x0')) (Datatypes.length (f_locs f))) by now apply /ssrnat.leP; lia.
        assert (HnewframeLoc: f_locs fr' = set_nth (VAL_num (VAL_int32 (wasm_value_to_i32 (Val_ptr (gmp_v + 16)%N)))) (f_locs f) (N.to_nat x0') (VAL_num (VAL_int32 (wasm_value_to_i32 (Val_ptr (gmp_v + 16)%N))))) by now subst fr'.
        assert (HvalRelp1 : repr_val_LambdaANF_Wasm  cenv fenv nenv penv (Vprim (AstCommon.primInt ; quot)) sr' (f_inst fr') (Val_ptr gmp_v)). {
          unfold page_size in *.
          apply Rprim_v with (sr:=sr') (gmp:=(gmp_v + 28)%N) (m:=m') (addr:=gmp_v); subst fr'; auto; try lia.
          exists n0; lia. }
        assert (HvalRelp2 : repr_val_LambdaANF_Wasm  cenv fenv nenv penv (Vprim (AstCommon.primInt ; rem)) sr' (f_inst fr') (Val_ptr (gmp_v + 8)%N)). {
          unfold page_size in *.
          apply Rprim_v with (sr:=sr') (gmp:=(gmp_v + 28)%N) (m:=m') (addr:=(gmp_v+8)%N); subst fr'; auto; try lia.
          exists (n0+4)%N; lia. }
        assert (HvalsPreserved : forall wal val,
                   repr_val_LambdaANF_Wasm  cenv fenv nenv penv val s (f_inst f) wal -> repr_val_LambdaANF_Wasm  cenv fenv nenv penv val sr' (f_inst fr') wal). {
          intros.
          unfold page_size in *.
          eapply val_relation_depends_on_mem_smaller_than_gmp_and_funcs with (sr:=s) (m:=m) (gmp:=gmp_v) (gmp':=(gmp_v + 28)%N); subst fr'; eauto; try lia.  }
        assert (HvalRelPair : repr_val_LambdaANF_Wasm  cenv fenv nenv penv v sr' (f_inst fr') (Val_ptr (gmp_v + 16)%N)). {
          unfold page_size in *.
          rewrite Hv.
          apply Rconstr_boxed_v with (v:=N_to_i32 pair_ord) (gmp:=(gmp_v+28)%N) (m:=m') (arity:=2) (ord:=0%N); subst fr'; auto; try lia.
          unfold get_ctor_ord; now rewrite Hpair.
          unfold get_ctor_arity; now rewrite Hpair.
          exists (n0 + 8)%N; lia.
          apply Rcons_l with (wal:=Val_ptr gmp_v) (m:=m') (addr:=(4 + (gmp_v+16))%N) (gmp:=(gmp_v+28)%N); auto; try lia.
          replace (4 + (gmp_v + 16))%N with (gmp_v + 20)%N by lia. unfold wasm_value_to_i32, wasm_value_to_u32. now unfold N_to_i32 in Hloadp1addr.
          apply Rcons_l with (wal:=Val_ptr (gmp_v + 8)%N) (m:=m') (addr:=(4 + (4 + (gmp_v+16)))%N) (gmp:=(gmp_v+28)%N); auto; try lia.
          replace (4 + (4 + (gmp_v + 16)))%N with (gmp_v + 24)%N by lia. unfold wasm_value_to_i32, wasm_value_to_u32. now unfold N_to_i32 in Hloadp2addr.
          now apply Rnil_l. }
        assert (HINV'' : INV fenv nenv sr' fr') by now eapply update_local_preserves_INV; eauto.
        assert (HrelE' : rel_env_LambdaANF_Wasm (lenv:=lenv)  cenv fenv nenv penv e (M.set x0 v rho) sr' fr' fds). {
          have Hl := HlocsInBounds _ _ Hrepr_x.
          apply nth_error_Some in Hl.
          apply notNone_Some in Hl. destruct Hl as [? Hlx].
          unfold rel_env_LambdaANF_Wasm.
          destruct HrelE as [Hfun1 [Hfun2 Hvar]].
          split. {
            intros ????? Hrho Hv'.
            destruct (var_dec x0 x1).
            - (* x0 = x1 *) (* v0 can never be a function value, by assumption on primops *)
              subst x1. rewrite M.gss in Hrho; eauto.
              inversion Hrho as [Hv_diveucl_21']. subst v0. subst v. (* rewrite Hv in Hv'. *)
              have H'' := Hnofunval rho' fds' f0.
              contradiction.
            - (* x0 <> x1 *)
              rewrite M.gso in Hrho; eauto.
          } split. {
            intros ? Hnfd. apply Hfun2 in Hnfd.
            destruct Hnfd as [i' [Htrans HvalFun]].
            exists i'. split. assumption.
            apply val_relation_func_depends_on_funcs with (s:=s); subst fr'; auto.
          }
          intros x2 Hx2free Hx2notfun.
          destruct (var_dec x0 x2).
          { (* x = x1 *)
            subst x2.
            exists v, (Val_ptr (gmp_v+16)%N).
            rewrite M.gss. split; auto.
            split.
            exists x0'. cbn. split. assumption.
            unfold lookup_N; cbn; auto.
            subst fr'. cbn.
            eapply set_nth_nth_error_same; eauto. assumption.
          }
          { (* x <> x1 *)
            assert (Hocc : occurs_free (Eprim x0 p [:: arg1 ; arg2 ; arg3] e) x2) by now apply Free_Eprim2.
            have H' := Hvar _ Hocc Hx2notfun.
            destruct H' as [val' [wal' [Hrho [Hloc Hval']]]].
            exists val', wal'. split.
            rewrite M.gso; auto. split.
            destruct Hloc as [i' [Hl1 Hl2]].
            unfold stored_in_locals. exists i'. split; auto.
            unfold lookup_N.
            subst fr'; rewrite set_nth_nth_error_other; auto.

            intro. assert (x0' = i') by lia. subst x0'.
            have Hcontra := repr_var_inj _ _ _ _ HlenvInjective Hl1 Hrepr_x.
            contradiction.

            now apply HvalsPreserved.
          }
        }
        exists sr', fr'.
        split; auto.
        split. apply rt_step. eapply r_local_set; eauto.
        repeat (split; auto).
        { (* minimum mem *)
           intros ?????.
           solve_eq m' m0.
           assert (gmp = gmp_v + 28)%N. {
             rewrite Hgmp' in H1.
             inv H1. now simpl_eq. } subst gmp.
           lia.
        }
        now exists (Val_ptr (gmp_v + 16)%N). }
      destruct (Z_le_dec (to_Z y) (to_Z xh)) as [Hle | Hnle].
      { (* y <= xh *)
        destruct (Hi64tempsW glob_tmp1 Hglob_tmp1 (VAL_int64 (Int64.repr (to_Z 0)))) as [s0 Hupd].
        assert (Hgvals : sglob_val s0 (f_inst f) glob_tmp1 = Some (VAL_num (VAL_int64 (Int64.repr (to_Z 0))))). by eapply update_global_get_same; eauto.
        assert (y <=? xh)%uint63. rewrite (reflect_iff _ _ (Uint63.lebP y xh)) in Hle. auto.
        unfold LambdaANF_primInt_diveucl_21 in Hv_div21.
        rewrite H in Hv_div21.
        destruct (Hrelations s0 glob_tmp1 glob_tmp1 0%uint63 0%uint63) as [sr' [fr' [Hred1 [Hred2 Hresult]]]]; auto.
        eapply update_global_preserves_INV with (sr:=s) (sr':=s0) (i:=glob_tmp1) (num:=(VAL_int64 (Int64.repr (to_Z 0)))); eauto; [discriminate|now intros|now intros].
        eapply update_global_get_other; eauto. discriminate.
        eapply update_global_preserves_funcs; eauto.
        rewrite <-Hmem2. symmetry.
        eapply update_global_preserves_memory; eauto.
        exists sr', fr'.
        unfold LambdaANF_primInt_diveucl_21. rewrite H. rewrite Hv_div21.
        split; auto.
        { inversion Hrepr_primop.
          unfold diveucl_21_instrs.
          remember (make_product glob_mem_ptr glob_tmp1 glob_tmp1) as mkprod_instrs.
          remember (make_product glob_mem_ptr glob_tmp4 glob_tmp1) as mkprod_instrs'.
          remember (diveucl_21_loop glob_cap glob_tmp1 glob_tmp2 glob_tmp3 glob_tmp4 63) as loop_instrs.
          separate_instr.
          dostep_nary 0. eapply r_local_get; eauto.
          dostep_nary 1. eapply r_load_success; eauto.
          rewrite <-Haddr3. simpl. apply Hload3'. replace (wasm_deserialise b2 T_i64) with (VAL_int64 (Int64.repr (to_Z y))) by congruence.
          dostep_nary_eliml 0 1.  eapply r_local_get; eauto.
          dostep_nary_eliml 1 1. eapply r_load_success; eauto.
          rewrite <-Haddr1. simpl. apply Hload1'. replace (wasm_deserialise b0 T_i64) with (VAL_int64 (Int64.repr (to_Z xh))) by congruence.
          dostep_nary 2. apply r_simple. apply rs_relop; first done. simpl.
          dostep_nary 1. apply r_simple. apply rs_if_true. simpl.
          unfold Int64.ltu. rewrite zlt_false. discriminate.
          rewrite uint63_unsigned_id uint63_unsigned_id. lia.
          dostep_nary 0. rewrite <-cat0s. eapply r_block with (t1s:=[::]) (t2s:=[T_num T_i32])(vs:=[::]); eauto.
          simpl. rewrite <-cat1s.
          eapply rt_trans with (y:=(state, sr', f, [AI_label 1 [] [:: $V (VAL_num (VAL_int32 (N_to_i32 (gmp_v + 16))))]] ++ [AI_basic (BI_local_set x0')])).
          apply app_trans.
          apply reduce_trans_label1.
          separate_instr.
          dostep_nary 1. eapply r_global_set'; eauto.
          replace (to_e_list mkprod_instrs) with (map AI_basic mkprod_instrs) by (subst mkprod_instrs; reflexivity).
          apply Hred1.
          dostep_nary 0. apply r_simple. apply rs_label_const; auto.
          apply Hred2. } }
      { (* xh < y *)
        destruct (Hi64tempsW glob_tmp1 Hglob_tmp1 (VAL_int64 (Int64.repr (to_Z xh)))) as [s0 Hupd0].
        assert (Hg1v : sglob_val s0 (f_inst f) glob_tmp1 = Some (VAL_num (VAL_int64 (Int64.repr (to_Z xh))))).
        by eapply update_global_get_same; eauto.
        have Hs0m := update_global_preserves_memory _ _ _ _ _ Hupd0. symmetry in Hs0m. rewrite Hmem2 in Hs0m.
        have : INV fenv nenv s0 f.
        eapply update_global_preserves_INV; eauto. right; split; auto. discriminate. now intros. now intros.
        intros HINV0. have I := HINV0. destruct I as [_ [_ [_ [_ [_ [_ [_ [_ [_ [_ [_ [_ [_ [_ [_ Hi64w0]]]]]]]]]]]]]]].
        destruct (Hi64w0 glob_tmp2 Hglob_tmp2 (VAL_int64 (Int64.repr (to_Z xl)))) as [s1 Hupd1]. clear Hi64w0.
        have Hs1m := update_global_preserves_memory _ _ _ _ _ Hupd1. symmetry in Hs1m. rewrite Hs0m in Hs1m.
        have : INV fenv nenv s1 f.
        eapply update_global_preserves_INV with (sr:=s0) (i:=glob_tmp2) (num:=VAL_int64 (Int64.repr (to_Z xl))); eauto.
        discriminate. now intros. now intros.
        intros HINV1. have I := HINV1. destruct I as [_ [_ [_ [_ [_ [_ [_ [_ [_ [_ [_ [_ [_ [_ [_ Hi64w1]]]]]]]]]]]]]]].
        destruct (Hi64w1 glob_tmp3 Hglob_tmp3 (VAL_int64 (Int64.repr (to_Z y)))) as [s2 Hupd2]. clear Hi64w1.
        have Hs2m := update_global_preserves_memory _ _ _ _ _ Hupd2. symmetry in Hs2m. rewrite Hs1m in Hs2m.
        have : INV fenv nenv s2 f.
        eapply update_global_preserves_INV with (sr:=s1) (i:=glob_tmp3) (num:=VAL_int64 (Int64.repr (to_Z y))); eauto.
        discriminate. now intros. now intros.
        intros HINV2. have I := HINV2. destruct I as [_ [_ [_ [_ [_ [_ [_ [_ [_ [_ [_ [_ [_ [_ [_ Hi64w2]]]]]]]]]]]]]]].
        destruct (Hi64w2 glob_tmp4 Hglob_tmp4 (VAL_int64 (Int64.repr 0))) as [s3 Hupd3]. clear Hi64w2.
        have Hs3m := update_global_preserves_memory _ _ _ _ _ Hupd3. symmetry in Hs3m. rewrite Hs2m in Hs3m.
        have : INV fenv nenv s3 f.
        eapply update_global_preserves_INV with (sr:=s2) (i:=glob_tmp4) (num:=VAL_int64 (Int64.repr 0)); eauto.
        discriminate. now intros. now intros.
        intros HINV3. have I := HINV3. destruct I as [_ [_ [_ [_ [Hcap _]]]]].
        destruct (Hcap (VAL_int32 (Int32.repr 0))) as [s4 Hupd4]. clear Hcap.
        have Hs4m := update_global_preserves_memory _ _ _ _ _ Hupd4. symmetry in Hs4m. rewrite Hs3m in Hs4m.
        have : INV fenv nenv s4 f.
        eapply update_global_preserves_INV with (sr:=s3) (i:=glob_cap) (num:=VAL_int32 (Int32.repr 0)); eauto.
        left; split; auto. apply cap_i32_glob; auto. discriminate. now intros. now intros.
        intro HINV4.
        have : (sglob_val s4 (f_inst f) glob_tmp1 = Some (VAL_num (VAL_int64 (Int64.repr (to_Z xh))))).
        eapply update_global_get_other with (sr:=s3) (j:=glob_cap); eauto. discriminate.
        eapply update_global_get_other with (sr:=s2) (j:=glob_tmp4); eauto. discriminate.
        eapply update_global_get_other with (sr:=s1) (j:=glob_tmp3); eauto. discriminate.
        eapply update_global_get_other with (sr:=s0) (j:=glob_tmp2); eauto. discriminate.
        have : (sglob_val s4 (f_inst f) glob_tmp2 = Some (VAL_num (VAL_int64 (Int64.repr (to_Z xl))))).
        eapply update_global_get_other with (sr:=s3) (j:=glob_cap); eauto. discriminate.
        eapply update_global_get_other with (sr:=s2) (j:=glob_tmp4); eauto. discriminate.
        eapply update_global_get_other with (sr:=s1) (j:=glob_tmp3); eauto. discriminate.
        eapply update_global_get_same; eauto.
        have : (sglob_val s4 (f_inst f) glob_tmp3 = Some (VAL_num (VAL_int64 (Int64.repr (to_Z y))))).
        eapply update_global_get_other with (sr:=s3) (j:=glob_cap); eauto. discriminate.
        eapply update_global_get_other with (sr:=s2) (j:=glob_tmp4); eauto. discriminate.
        eapply update_global_get_same; eauto.
        have : (sglob_val s4 (f_inst f) glob_tmp4 = Some (VAL_num (VAL_int64 (Int64.repr 0)))).
        eapply update_global_get_other with (sr:=s3) (j:=glob_cap); eauto. discriminate.
        eapply update_global_get_same; eauto.
        have : (sglob_val s4 (f_inst f) glob_cap = Some (VAL_num (VAL_int32 (Int32.repr 0)))).
        eapply update_global_get_same; eauto.
        intros Hg_counter Hg_q Hg_y Hg_xl Hg_xh.
        have : (sglob_val s4 (f_inst f) glob_mem_ptr = Some (VAL_num (VAL_int32 (N_to_i32 gmp_v)))).
        eapply update_global_get_other with (sr:=s3) (j:=glob_cap); eauto. discriminate.
        eapply update_global_get_other with (sr:=s2) (j:=glob_tmp4); eauto. discriminate.
        eapply update_global_get_other with (sr:=s1) (j:=glob_tmp3); eauto. discriminate.
        eapply update_global_get_other with (sr:=s0) (j:=glob_tmp2); eauto. discriminate.
        eapply update_global_get_other with (sr:=s) (j:=glob_tmp1); eauto. discriminate.
        intro Hgmps4.
        destruct (div21_loop_reduce_full 63 state s4 f m gmp_v 0%Z (to_Z xh) (to_Z xl) (to_Z xh) (to_Z xl) 0%Z (to_Z y)) as [sr' [xh' [xl' [q HloopRed]]]]; auto.
        split; auto.
        split; auto.
        split; auto.
        split; auto.
        split; auto. apply to_Z_bounded.
        split; auto. split. apply to_Z_bounded. lia.
        split; auto. lia.
        split; auto. lia.
        cbn.
        rewrite Z.mod_small.
        replace ((to_Z xh) mod (to_Z y))%Z with (to_Z xh).
        reflexivity.
        rewrite Z.mod_small. reflexivity. split. apply to_Z_bounded. lia.
        apply to_Z_bounded. lia.
        destruct HloopRed as [HloopRed [HINVLoop [HsfsLoop [HmemLoop [HgmpLoop [HLoopInvariant _]]]]]].
        unfold div21_loop_invariant in HLoopInvariant.
        destruct HLoopInvariant as [Hxh' [Hxl' [Hy [Hq' [_ [Hxh_lt_y [Hq_range [Hxl_eq Hdivmod]]]]]]]].
        have Hdiv21_spec := (diveucl_21_spec xh xl y).
        destruct (diveucl_21 xh xl y) as [d21_q d21_r] eqn:Hd21.
        replace d21_q with (fst (diveucl_21 xh xl y)) in * by now rewrite Hd21.
        replace d21_r with (snd (diveucl_21 xh xl y)) in * by now rewrite Hd21.
        have : (to_Z xh < to_Z y)%Z. lia.
        intro Hxh_lt_y'.
        destruct (Z.div_eucl ((to_Z xh) * wB + (to_Z xl)) (to_Z y)) as [dq' dr'] eqn:Hde.
        destruct (Hdiv21_spec Hxh_lt_y') as [Hd21_fst Hd21_snd].
        simpl in Hdivmod. replace ((to_Z xl) mod 1)%Z with 0%Z in Hdivmod by lia.
        rewrite Z.add_0_r in Hdivmod. rewrite Z.mul_1_r in Hdivmod.
        replace (Z.pow_pos 2 63)%Z with wB in Hdivmod by now cbn.
        rewrite Z.mod_small in Hdivmod. 2: split; [by destruct (to_Z_bounded xh)|lia].
        have Hdivmod' := Z_div_mod ((to_Z xh) * wB + (to_Z xl)) (to_Z y).
        rewrite Hde in Hdivmod'.
        assert (to_Z y > 0)%Z by lia.
        destruct (Hdivmod' H) as [Hquot Hrem].
        replace dq' with q in Hd21_fst by (rewrite Hquot in Hdivmod; nia).
        replace dr' with xh' in Hd21_snd by lia.
        clear Hdiv21_spec Hdivmod Hdivmod' Hquot H Hrem Hd21.
        assert ((y <=? xh)%uint63 = false).
        assert (~ (to_Z y <= to_Z xh))%Z. lia.
        now apply to_Z_nle_uint63_leb_false.
        unfold LambdaANF_primInt_diveucl_21 in Hv_div21. rewrite H in Hv_div21.
        destruct (Hrelations sr' glob_tmp4 glob_tmp1 (fst (diveucl_21 xh xl y)) (snd (diveucl_21 xh xl y))) as [sr_prod [fr' [Hred1 [Hred2 Hresult]]]]; auto; auto.
        simpl. rewrite Hd21_fst; auto.
        simpl. rewrite Hd21_snd; auto.
        erewrite <-(update_global_preserves_funcs s3 s4) in HsfsLoop; eauto.
        erewrite <-(update_global_preserves_funcs s2 s3) in HsfsLoop; eauto.
        erewrite <-(update_global_preserves_funcs s1 s2) in HsfsLoop; eauto.
        erewrite <-(update_global_preserves_funcs s0 s1) in HsfsLoop; eauto.
        erewrite <-(update_global_preserves_funcs s s0) in HsfsLoop; eauto.
        unfold LambdaANF_primInt_diveucl_21. rewrite H. rewrite Hv_div21.
        exists sr_prod, fr'.
        split. { inversion Hrepr_primop.
          unfold diveucl_21_instrs.
          remember (make_product glob_mem_ptr glob_tmp1 glob_tmp1) as mkprod_instrs.
          remember (make_product glob_mem_ptr glob_tmp4 glob_tmp1) as mkprod_instrs'.
          remember (diveucl_21_loop glob_cap glob_tmp1 glob_tmp2 glob_tmp3 glob_tmp4 63) as loop_instrs.
          separate_instr.
          dostep_nary 0. eapply r_local_get; eassumption.
          dostep_nary 1. eapply r_load_success; eauto.
            rewrite <-Haddr3. simpl. apply Hload3'.
          replace (wasm_deserialise b2 T_i64) with (VAL_int64 (Int64.repr (to_Z y))) by congruence.
          dostep_nary_eliml 0 1.  eapply r_local_get; eassumption.
          dostep_nary_eliml 1 1. eapply r_load_success; eauto.
            rewrite <-Haddr1. simpl. apply Hload1'.
          replace (wasm_deserialise b0 T_i64) with (VAL_int64 (Int64.repr (to_Z xh))) by congruence.
          dostep_nary 2. apply r_simple. apply rs_relop; first done. simpl.
          dostep_nary 1. apply r_simple. apply rs_if_false. simpl.
          unfold Int64.ltu. rewrite zlt_true. reflexivity.
          rewrite uint63_unsigned_id uint63_unsigned_id. lia.
          dostep_nary 0. rewrite <-cat0s. eapply r_block with (t1s:=[::]) (t2s:=[T_num T_i32])(vs:=[::]); eauto.
          simpl. rewrite <-cat1s.
          eapply rt_trans.
          apply app_trans.
          apply reduce_trans_label1.
          separate_instr.
          dostep_nary 0. eapply r_local_get; eauto.
          dostep_nary 1. eapply r_load_success; eauto.
          rewrite <-Haddr1. simpl. apply Hload1'. replace (wasm_deserialise b0 T_i64) with (VAL_int64 (Int64.repr (to_Z xh))) by congruence.
          dostep_nary 1. eapply r_global_set'; eauto.
          dostep_nary 0. eapply r_local_get; eauto.
          dostep_nary 1. eapply r_load_success; eauto.
          rewrite <-Haddr2. simpl. apply Hload2'. replace (wasm_deserialise b1 T_i64) with (VAL_int64 (Int64.repr (to_Z xl))) by congruence.
          dostep_nary 1. eapply r_global_set'; eauto.
          dostep_nary 0. eapply r_local_get; eauto.
          dostep_nary 1. eapply r_load_success; eauto.
          rewrite <-Haddr3. simpl. apply Hload3'. replace (wasm_deserialise b2 T_i64) with (VAL_int64 (Int64.repr (to_Z y))) by congruence.
          dostep_nary 1. eapply r_global_set'; eauto.
          dostep_nary 1. eapply r_global_set'; eauto.
          dostep_nary 1. eapply r_global_set'; eauto.
          rewrite cat0s.
          eapply rt_trans. apply app_trans.
          apply HloopRed.
          rewrite cat0s.
          apply Hred1.
          dostep_nary' 0. apply r_simple. apply rs_label_const; auto.
          apply Hred2. }
        auto. } }
    { (* addmuldiv *)
      assert (forall w,
               exists mem, store m (Wasm_int.N_of_uint i32m (N_to_i32 gmp_v)) 0%N
                           (serialise_num (VAL_int64 w))
                           8 = Some mem) as Htest. {
      intros.
      apply notNone_Some, enough_space_to_store. cbn.
      rewrite length_serialise_num_i64. cbn.
      rewrite Wasm_int.Int32.Z_mod_modulus_id; lia. }

    (* TODO cleanup *)
    assert (forall n,
               exists s' s_final fr m' wal,
                 s' = upd_s_mem s (set_nth m' s.(s_mems) 0 m')
                 /\ smem_store s (f_inst f) (Wasm_int.N_of_uint i32m (N_to_i32 gmp_v)) 0%N
                      (VAL_int64 (Z_to_i64 (to_Z n))) T_i64 = Some s'
                 /\ fr ={| f_locs := set_nth (VAL_num (VAL_int32 (wasm_value_to_i32 wal))) (f_locs f) (N.to_nat x0') (VAL_num (VAL_int32 (wasm_value_to_i32 wal)))
                        ; f_inst := f_inst f
                        |}
                 /\ smem s' (f_inst fr) = Some m'
                 /\ reduce_trans (state, s', f, map AI_basic [ BI_global_get glob_mem_ptr
                                                               ; BI_global_get glob_mem_ptr
                                                               ; BI_const_num (nat_to_value 8)
                                                               ; BI_binop T_i32 (Binop_i BOI_add)
                                                               ; BI_global_set glob_mem_ptr
                                                               ; BI_local_set x0'
                      ])
                      (state, s_final, fr, [::])

                 /\ INV fenv nenv s' fr
                 /\ supdate_glob s' (f_inst f) glob_mem_ptr
                      (VAL_num (VAL_int32 (Wasm_int.Int32.iadd (N_to_i32 gmp_v) (nat_to_i32 8)))) = Some s_final
                 /\ INV fenv nenv s_final fr
                 /\ f_inst f = f_inst fr
                 /\ s_funcs s = s_funcs s_final
                 /\ min_available_memory s_final (f_inst f) mem
                 /\ rel_env_LambdaANF_Wasm (lenv:=lenv) cenv fenv nenv penv e (M.set x0 (Vprim (primInt n)) rho) s_final fr fds
                 /\ (forall (wal : wasm_value) (v : val),
                        repr_val_LambdaANF_Wasm cenv fenv nenv penv v s (f_inst f) wal -> repr_val_LambdaANF_Wasm cenv fenv nenv penv v s_final (f_inst fr) wal)
                 /\ (exists wal,
                        fr ={| f_locs := set_nth (VAL_num (VAL_int32 (wasm_value_to_i32 wal))) (f_locs f) (N.to_nat x0') (VAL_num (VAL_int32 (wasm_value_to_i32 wal)))
                            ; f_inst := f_inst f |}
                        /\ repr_val_LambdaANF_Wasm  cenv fenv nenv penv (Vprim (primInt n)) s_final (f_inst fr) wal)). {
        intros.
        clear Htrue Hfalse Hc0 Hc1 Hlt Hgt Heq Hpair.
      destruct (Htest (Z_to_i64 (to_Z n))) as [m' Hm'].
      remember (upd_s_mem s (set_nth m' s.(s_mems) 0 m')) as s'.
      exists s'.
      assert (Hm'': smem_store s (f_inst f) (Wasm_int.N_of_uint i32m (N_to_i32 gmp_v)) 0%N
                      (VAL_int64 (Z_to_i64 (to_Z n))) T_i64 = Some s'). {
        unfold smem_store. rewrite Hmem1. cbn. subst s'.
        unfold smem in Hmem2. rewrite Hmem1 in Hmem2. destruct (s_mems s)=>//.
        injection Hmem2 as ->. now rewrite Hm'. }
      assert (Hinv' : INV fenv nenv s' f). {
        subst.
        assert (mem_length m = mem_length m'). {
          apply store_length in Hm'. congruence. }
        assert (m.(meminst_type).(lim_max) = m'.(meminst_type).(lim_max)). {
          apply store_lim_max in Hm'. congruence. }
        eapply update_mem_preserves_INV; auto. apply Hinv. eassumption. erewrite <- H. lia.
        congruence. exists (mem_size m); split; auto. unfold mem_size. congruence. }
      have I := Hinv'. destruct I as [_ [_ [_ [Hgmp_w' [_ [Hglob_mut [Hlinmem' [Hgmp' [_ [_ [_ [_ [_ [Hgmp_mult_two _]]]]]]]]]]]]]].
      destruct Hlinmem' as [Hmem1' [m'' [Hmem2' [size' [Hmem3' [Hmem4' Hmem5']]]]]].
      destruct (Hgmp_w' (VAL_int32 (Wasm_int.Int32.iadd (N_to_i32 gmp_v) (nat_to_i32 8)))) as [s_final Hupd_glob].
      assert (smem s' (f_inst f) = Some m'). {
        subst s'. unfold smem, lookup_N. cbn.
        rewrite Hmem1'. apply set_nth_nth_error_same with (e:=m).
        unfold smem in Hmem2. rewrite Hmem1 in Hmem2.
        destruct (s_mems s)=>//. }
      assert (m' = m'') by congruence. subst m''.
      assert (HgmpBound': (gmp_v + 8 + 8 < mem_length m')%N). {
        assert (mem_length m = mem_length m') by
          now apply store_length in Hm'.
        replace (mem_length m') with (mem_length m).
        now unfold page_size in *. }
      remember {| f_locs := set_nth (VAL_num (N_to_value gmp_v)) (f_locs f) (N.to_nat x0') (VAL_num (N_to_value gmp_v))
               ; f_inst := f_inst f
               |} as fr.
      assert (Hinv'': INV fenv nenv s' fr). {
        now apply update_local_preserves_INV with (f:=f) (x':=N.to_nat x0') (v:=N_to_i32 gmp_v).
      }
      assert (Hsglobval_s':sglob_val s' (f_inst f) glob_mem_ptr = Some (VAL_num (VAL_int32 (N_to_i32 gmp_v)))) by
        now apply (update_memory_preserves_globals s f) with m'.
      assert (Hgmp_w'' : INV_glob_mem_ptr_writable s' f) by now destruct Hinv'.
      assert (Z.of_N (gmp_v + 8)%N < Wasm_int.Int32.modulus)%Z as HgmpModulus by lia.
      assert (HfsEq: s_funcs s = s_funcs s') by now subst.
      assert (HfsEq': s_funcs s' = s_funcs s_final) by now apply update_global_preserves_funcs in Hupd_glob.
      assert (HfsEq'': s_funcs s = s_funcs s_final) by now subst.
      assert (HgmpBound'': (-1 < Z.of_N (gmp_v + 8) < Wasm_int.Int32.modulus)%Z). {
        apply mem_length_upper_bound in Hmem5. simpl_modulus_in Hmem5. cbn in Hmem5.
        simpl_modulus. cbn. lia.
      }

      assert (HenoughM'': (gmp_v + 52 < mem_length m')%N). {
        assert (mem_length m = mem_length m') by
          now apply store_length in Hm'.
        replace (mem_length m') with (mem_length m). lia. }

      assert (Hinv_final : INV fenv nenv s_final fr). {
        eapply update_global_preserves_INV with (sr:=s') (i:=glob_mem_ptr) (num:=(VAL_int32 (N_to_i32 (gmp_v + 8)))); eauto.
        left. split. apply gmp_i32_glob; auto. now cbn. discriminate.
        now subst fr.
        move => _. intros.
        destruct Hgmp_mult_two with (gmp_v:=gmp_v) (m:=m') as [n0' Hn0]. assumption.
        now subst s'.
        lia.
        destruct H0 as [Heqn0 Hboundn0].
        replace n0 with (gmp_v + 8)%N. lia.
        inv Heqn0.
        simpl_eq. lia.
        move => _. intros.
        destruct Hgmp_mult_two with (gmp_v:=gmp_v) (m:=m') as [n0' Hn0]. assumption.
        now subst s'.
        lia.
        destruct H0 as [Heqn0 Hboundn0].
        replace n0 with (gmp_v + 8)%N.
        exists (n0' + 4)%N; lia.
        inv Heqn0.
        simpl_eq. lia.
        unfold Wasm_int.Int32.iadd, Wasm_int.Int32.add in Hupd_glob.
        rewrite Heqfr. cbn in Hupd_glob |- *.
        rewrite Wasm_int.Int32.Z_mod_modulus_id in Hupd_glob; last lia.
        unfold N_to_i32.
        now replace (Z.of_N gmp_v + 8)%Z with (Z.of_N (gmp_v + 8))%Z in Hupd_glob by lia.
      }

      destruct (Hgmp_w' (VAL_int32 (Int32.repr (Z.of_N (gmp_v + 8)%N)))) as [sr' Hglob_sr'].

      assert (Hinv_sr' : INV fenv nenv sr' fr). {
        eapply update_global_preserves_INV with (sr:=s') (i:=glob_mem_ptr) (num:=(VAL_int32 (N_to_i32 (gmp_v+8)))); eauto.
        left. split. apply gmp_i32_glob; auto. now cbn. discriminate.
        now subst fr.
        move => _.
        intros n0 [Heqn0 Hboundn0].
        replace n0 with (gmp_v + 8)%N. lia.
        inversion Heqn0.
        simpl_eq. lia.
        move => _.
        destruct Hgmp_mult_two with (gmp_v:=gmp_v) (m:=m') as [n0' Hn0]; auto.
        intros n0 [Heqn0 Hboundn0].
        replace n0 with (gmp_v + 8)%N.
        exists (n0' + 4)%N. lia.
        inversion Heqn0.
        simpl_eq. lia.
        now subst fr.
      }

      assert (Hrepr_val : repr_val_LambdaANF_Wasm  cenv fenv nenv penv (Vprim (primInt n)) sr' (f_inst fr) (Val_ptr gmp_v)). {
        apply Rprim_v with (gmp:=(gmp_v+8)%N) (m:=m'); auto.
        subst fr. eapply update_global_get_same. eassumption.
        lia.
        destruct Hgmp_mult_two with (gmp_v:=gmp_v) (m:=m') as [n0 Hn0].
        assumption. assumption. lia. exists n0. lia.
        replace (smem sr' (f_inst fr)) with (smem s' (f_inst fr)) by now subst fr; eapply update_global_preserves_memory.
        now subst fr.
        assert ((wasm_deserialise (serialise_num (VAL_int64 (Z_to_i64 (to_Z n)))) T_i64) = (VAL_int64 (Z_to_i64 (to_Z n)))) by now apply deserialise_serialise.
        rewrite -H0.
        apply (store_load_i64 m m' gmp_v (serialise_num (VAL_int64 (Z_to_i64 (to_Z n))))); auto.
        assert (Wasm_int.N_of_uint i32m (N_to_i32 gmp_v) = gmp_v). {
          cbn. rewrite Wasm_int.Int32.Z_mod_modulus_id; lia. }
        rewrite -H1.
        apply Hm'. }
      assert (HvalsPreserved : forall (wal : wasm_value) (v : val),
                 repr_val_LambdaANF_Wasm cenv fenv nenv penv v s (f_inst f) wal -> repr_val_LambdaANF_Wasm  cenv fenv nenv penv v sr' (f_inst fr) wal). {
        intros.
        apply val_relation_depends_on_mem_smaller_than_gmp_and_funcs with (sr:=s) (m:=m) (m':=m') (gmp:=gmp_v) (gmp':=(gmp_v + 8)%N); auto.
        replace (s_funcs s) with (s_funcs s') by auto.
        now apply update_global_preserves_funcs in Hglob_sr'.
        now subst fr.
        replace (smem sr' (f_inst fr)) with (smem s' (f_inst fr)) by now subst fr; eapply update_global_preserves_memory.
        now subst fr.
        now subst fr.
        { simpl_modulus. cbn. simpl_modulus_in H0. cbn in H0. simpl_modulus_in HgmpBound.
          apply mem_length_upper_bound in Hmem5.
          unfold page_size, max_mem_pages in *. lia. }
        apply update_global_get_same with (sr:=s').
        now subst fr.
        { simpl_modulus. cbn.
          subst size'.
          apply mem_length_upper_bound in Hmem5'.
          unfold page_size, max_mem_pages in *.
          lia. }
        lia.
        { intros.
          assert (Hex: exists v, load_i32 m a = Some v). {
            apply enough_space_to_load. subst.
            simpl_modulus_in HenoughM'.
            apply store_length in Hm'. lia. }
          destruct Hex as [v' Hv'].
          rewrite Hv'.
          symmetry.
          apply (load_store_load_i32' m m' a (Wasm_int.N_of_uint i32m (N_to_i32 gmp_v)) v' (serialise_num (VAL_int64 (Z_to_i64 (to_Z n))))); auto.
          cbn. rewrite Wasm_int.Int32.Z_mod_modulus_id; lia. }
        { intros a Ha.
          assert (Hex: exists v, load_i64 m a = Some v). {
            apply enough_space_to_load_i64. lia. }
          destruct Hex as [v' Hv'].
          rewrite Hv'. symmetry.
          apply (load_store_load_i64' m m' a (Wasm_int.N_of_uint i32m (N_to_i32 gmp_v)) v' (serialise_num (VAL_int64 (Z_to_i64 (to_Z n))))); auto.
          cbn. rewrite Wasm_int.Int32.Z_mod_modulus_id; lia.
        }
        now subst fr. }
      assert (HrelE' : rel_env_LambdaANF_Wasm (lenv:=lenv) cenv fenv nenv penv e (M.set x0 (Vprim (primInt n)) rho) sr' fr fds). {
        have Hl := HlocsInBounds _ _ Hrepr_x.
        apply nth_error_Some in Hl.
        apply notNone_Some in Hl. destruct Hl as [? Hlx].
        unfold rel_env_LambdaANF_Wasm.
        destruct HrelE as [Hfun1 [Hfun2 Hvar]].
        split.
        { (* funs1 *)
          intros ????? Hrho Hv'.
          destruct (var_dec x0 x2).
          - (* x = x1 *)
            subst x2. rewrite M.gss in Hrho. inv Hrho.
            assert (~ subval_or_eq (Vfun rho' fds' f0) (Vprim (primInt n))).
                by now apply subval_or_eq_fun_not_prim.
            contradiction.
          - (* x <> x1 *)
            now rewrite M.gso in Hrho; eauto.
        } split.
        { intros ? Hnfd. apply Hfun2 in Hnfd.
          destruct Hnfd as [i' [Htrans Hval]].
          exists i'. split. assumption.
          apply val_relation_func_depends_on_funcs with (s:=s); auto.
          replace (s_funcs s) with (s_funcs s') by auto.
          now apply update_global_preserves_funcs in Hglob_sr'.
          now subst fr.
        }
        intros. destruct (var_dec x0 x2).
        { (* x = x1 *)
          subst x2. exists (Vprim (primInt n)), (Val_ptr gmp_v).
          rewrite M.gss. split; auto.
          split.
          exists x0'. cbn. split. assumption.
          unfold lookup_N; cbn; auto.
          subst fr. cbn. erewrite set_nth_nth_error_same; eauto.
          now subst fr.
        }
        { (* x <> x1 *)
          assert (Hocc : occurs_free (Eprim x0 p [:: x ; y ; z] e) x2)
              by now apply Free_Eprim2.
          have H' := Hvar _ Hocc H1.
          destruct H' as [val' [wal' [Hrho [Hloc Hval]]]].
          exists val', wal'. split.
          rewrite M.gso; auto. split.
          destruct Hloc as [i' [Hl1 Hl2]].
          unfold stored_in_locals. exists i'. split; auto.
          subst fr. unfold lookup_N.
          rewrite set_nth_nth_error_other; auto.

          intro. assert (x0' = i') by lia. subst x0'.
          have Hcontra := repr_var_inj _ _ _ _ HlenvInjective Hl1 Hrepr_x.
          contradiction.

          now apply HvalsPreserved.
        }
      }
      exists sr', fr, m', (Val_ptr gmp_v).
      try repeat (split; auto). all: subst fr; auto.
      assert (sglob_val s' (f_inst f) glob_mem_ptr =
                Some (VAL_num (VAL_int32 (N_to_i32 gmp_v)))) by now subst s'.
      separate_instr.
      dostep_nary 0. eapply r_global_get.
      eassumption.
      eapply rt_trans
        with (y:=(state, sr', f, [$V VAL_num (VAL_int32 (N_to_i32 gmp_v))] ++ [AI_basic (BI_local_set x0')])).
      eapply app_trans_const; auto.
      dostep_nary 0. apply r_global_get; eassumption.
      dostep_nary 2. constructor; apply rs_binop_success; first done; reflexivity.
      cbn; unfold Wasm_int.Int32.iadd, Wasm_int.Int32.add; cbn.
      rewrite Wasm_int.Int32.Z_mod_modulus_id. 2: lia.
      dostep_nary 1. rewrite N2Z.inj_add in Hglob_sr'. eapply r_global_set'; eauto.
      cbn; apply rt_refl.
      cbn. dostep_nary' 1. eapply r_local_set' with (f':={|f_locs := set_nth (VAL_num (N_to_value gmp_v)) (f_locs f) (N.to_nat x0') (VAL_num (N_to_value gmp_v)); f_inst := f_inst f|}). reflexivity.
      apply /ssrnat.leP.
      apply HlocsInBounds in Hrepr_x. lia.
      reflexivity.
      now apply rt_refl.
      cbn; unfold Wasm_int.Int32.iadd, Wasm_int.Int32.add; cbn.
      rewrite Wasm_int.Int32.Z_mod_modulus_id; [|lia].
      unfold N_to_i32 in Hglob_sr'.
      replace 8%Z with (Z.of_N 8) by now cbn.
      rewrite -N2Z.inj_add.
      assumption.
      replace (s_funcs s) with (s_funcs s') by auto.
      now apply update_global_preserves_funcs in Hglob_sr'.

      (* minimum mem *)
      intros ?????.
      assert (m0 = m'). { apply update_global_preserves_memory in Hglob_sr'. now solve_eq m0 m'. }
      subst m0.
      assert (gmp = gmp_v + 8)%N. {
        apply update_global_get_same in Hglob_sr'.
        rewrite Hglob_sr' in H1.
        inv H1. now simpl_eq. } subst gmp.
      apply store_length in Hm'. lia.

      exists (Val_ptr gmp_v).
      split; auto. }
      clear Htrue Hfalse Heq Hlt Hgt Hc0 Hc1 Hpair. clear true_tag false_tag bool_tag eq_tag lt_tag gt_tag comp_tag c0_tag c1_tag carry_tag pair_tag prod_tag.
            rename H into Hrelations.
      inversion Hres as [Hv_ternop]. simpl.
      destruct (Hrelations (addmuldiv n1 n2 n3)) as [s' [s_final [fr [m' [wal [Hs' [Hstore [Hfr [Hsmem [Hstep [Hinv1 [Hupd_glob Hr]]]]]]]]]]]].
      exists s_final, fr. unfold LambdaANF_primInt_addmuldiv in Hv_ternop.
      replace v with (Vprim ( AstCommon.primInt ; (addmuldiv n1 n2 n3))) in * by congruence.
      split; auto.
      inversion Hrepr_primop.
      unfold addmuldiv_instrs.
      separate_instr.
      dostep_nary 0. eapply r_global_get; eauto.
      eapply rt_trans. eapply app_trans_const with (hs':=state) (s':=s) (f':=f) (es':=[$VN (VAL_int64 (Int64.repr (to_Z (addmuldiv n1 n2 n3))))] ++ ?[es_after]); eauto.
      dostep_nary 0. eapply r_local_get; eauto.
      dostep_nary 1. eapply r_load_success; eauto. rewrite <-Haddr1. simpl. apply Hload1'.
      replace (wasm_deserialise b0 T_i64) with (VAL_int64 (Int64.repr (to_Z n1))) by now inversion Hload1.
      eapply rt_trans with (y:=(state, s, f, [$VN (VAL_int64 (Int64.repr (to_Z (addmuldiv n1 n2 n3))))] ++ ?[es_after'])).
      destruct (Z_le_dec (to_Z n1) 63) as [Hle | Hgt].
      { have Hn1bounded := to_Z_bounded n1.
        assert (0 <= to_Z 63 - to_Z n1 <= 63)%Z. replace (to_Z 63) with 63%Z by now cbn. split. lia. lia.
        assert ((to_Z n1) mod Int64.wordsize = to_Z n1)%Z.
        rewrite Z.mod_small. reflexivity. unfold Int64.wordsize, Integers.Wordsize_64.wordsize. lia.
        assert (((to_Z 63) - (to_Z n1)) mod Int64.wordsize = 63 - (to_Z n1))%Z.
        rewrite Z.mod_small. reflexivity. unfold Int64.wordsize, Integers.Wordsize_64.wordsize. lia.
        assert (Int64.unsigned (Int64.repr ((to_Z 63) - (to_Z n1))) = (to_Z 63) - (to_Z n1))%Z.
        cbn. rewrite Int64.Z_mod_modulus_id. reflexivity. rewrite int64_modulus_eq_pow64. lia.
        have Hn3bounded := to_Z_bounded n3. unfold wB in Hn3bounded. cbn in Hn3bounded.
        assert (0 <= (to_Z n3) / 2^(to_Z 63 - to_Z n1))%Z. apply Z_div_nonneg_nonneg.
        by destruct (to_Z_bounded n3). lia.
        assert ((to_Z n3) / 2^(to_Z 63 - to_Z n1) < Int64.modulus)%Z.
        rewrite int64_modulus_eq_pow64. unfold wB in Hn1bounded. cbn in Hn1bounded. lia.
        dostep_nary 2. apply r_simple. apply rs_relop=>//.
        dostep_nary 1. apply r_simple. apply rs_if_false.
        assert (~ (to_Z 63 < to_Z n1)%Z).
        replace (to_Z 63) with 63%Z.
        lia.
        reflexivity. simpl.
        replace 63%Z with (to_Z 63) by now cbn.
        rewrite uint63_nlt_int64_nlt. reflexivity.
        auto.
        dostep_nary 0. eapply r_block with (t1s:=[::]) (t2s:=[T_num T_i64])(vs:=[::]); eauto.
        eapply rt_trans with (y:=(state, s, f, [AI_label 1 [] [:: $VN VAL_int64 (Int64.repr (to_Z (addmuldiv n1 n2 n3)))]] ++ ?[es_after''])).
        apply app_trans.
        apply reduce_trans_label1.
        dostep_nary 0. eapply r_local_get; eassumption.
        dostep_nary 1. eapply r_load_success; eauto.
          rewrite <-Haddr2. simpl. apply Hload2'.
        replace (wasm_deserialise b1 T_i64) with (VAL_int64 (Int64.repr (to_Z n2))) by now inversion Hload2.
        dostep_nary_eliml 0 1. eapply r_local_get; eassumption.
        dostep_nary_eliml 1 1. eapply r_load_success; eauto.
          rewrite <-Haddr1. simpl. apply Hload1'.
        replace (wasm_deserialise b0 T_i64) with (VAL_int64 (Int64.repr (to_Z n1))) by now inversion Hload1.
        dostep_nary 2. apply r_simple. apply rs_binop_success; first done.
        simpl. reflexivity.
        dostep_nary_eliml 0 1. eapply r_local_get; eassumption.
        dostep_nary_eliml 1 1. eapply r_load_success; eauto.
          rewrite <-Haddr3. simpl. apply Hload3'.
        replace (wasm_deserialise b2 T_i64) with (VAL_int64 (Int64.repr (to_Z n3))) by now inversion Hload3.
        dostep_nary_eliml 0 3. eapply r_local_get; eassumption.
        dostep_nary_eliml 1 3. eapply r_load_success; eauto.
          rewrite <-Haddr1. simpl. apply Hload1'.
        replace (wasm_deserialise b0 T_i64) with (VAL_int64 (Int64.repr (to_Z n1))) by now inversion Hload1.
        dostep_nary_eliml 2 2. apply r_simple. apply rs_binop_success; first done.
        simpl. unfold Int64.isub, Int64.sub. replace 63%Z with (to_Z 63) by now cbn.
        rewrite uint63_unsigned_id. rewrite uint63_unsigned_id. reflexivity.
        dostep_nary_eliml 2 1. apply r_simple. apply rs_binop_success; first done.
        simpl. unfold Int64.ishr_u. unfold Int64.shru.
        rewrite H6. rewrite H5. rewrite H6. rewrite uint63_unsigned_id.
        rewrite Z.shiftr_div_pow2. reflexivity. lia.
        dostep_nary' 2. apply r_simple. apply rs_binop_success; first done. cbn.
        unfold Int64.ishl. rewrite uint63_unsigned_id. rewrite H4.
        unfold Int64.ior. rewrite Int64.shifted_or_is_add.
        reflexivity. unfold Int64.zwordsize. unfold Int64.wordsize, Integers.Wordsize_64.wordsize. lia.
        rewrite two_p_equiv.
        assert (to_Z n3 < 2^ (to_Z 63 - to_Z n1) * 2^(to_Z n1))%Z. {
          rewrite <-Z.pow_add_r. replace (to_Z 63 - to_Z n1 + to_Z n1)%Z with (to_Z 63) by liat.
          replace (2^(to_Z 63))%Z with wB by now cbn. by destruct (to_Z_bounded n3).
          lia. lia. }
          cbn. rewrite Int64.Z_mod_modulus_id.
          apply Z.div_lt_upper_bound. lia. lia. lia.
        dostep_nary' 2. apply r_simple. apply rs_binop_success; first done.
          simpl. rewrite int64_bitmask_modulo.
          rewrite uint63_mod_modulus_id.
          rewrite Int64.Z_mod_modulus_id.
          have Haddmuldiv := addmuldiv_spec n2 n3 n1.
          replace (to_Z digits) with 63%Z in Haddmuldiv.
          specialize (Haddmuldiv Hle).
          rewrite two_p_equiv.
          replace (to_Z 63) with 63%Z by now cbn.
          rewrite <- Haddmuldiv. reflexivity. reflexivity.
          lia.
        apply rt_refl.
        dostep_nary 0. apply  r_simple. apply rs_label_const; auto. apply rt_refl. }
      dostep_nary 2. apply r_simple. apply rs_relop=>//.
      dostep_nary 1. apply r_simple. apply rs_if_true.
      assert (to_Z 63 < to_Z n1)%Z. replace (to_Z 63) with 63%Z by now cbn.
      lia. replace 63%Z with (to_Z 63) by reflexivity.
      rewrite uint63_lt_int64_lt. discriminate.
      lia.
      dostep_nary 0.
      eapply r_block with (t1s:=[::]) (t2s:=[T_num T_i64])(vs:=[::]); eauto.
      dostep_nary 0. apply r_simple. apply rs_label_const; auto.
      replace 0%Z with (to_Z (addmuldiv n1 n2 n3)).
      apply rt_refl.
      rewrite addmuldiv_def_spec. unfold addmuldiv_def.
      assert (to_Z 63 < to_Z n1)%Z. replace (to_Z 63) with 63%Z by now cbn. lia.
      rewrite lor_spec'.
      rewrite uint63_lsl63.
      assert (to_Z 63 <= to_Z (digits - n1))%Z.
      rewrite [(to_Z (digits - n1))] sub_spec.
      unfold digits.
      replace (to_Z 63) with 63%Z in H |- * by reflexivity.
      assert (0 <= (63 - to_Z n1) mod wB < wB)%Z. apply Z_mod_lt. by cbn.
      assert (- (to_Z n1 - 63) = (63 - to_Z n1))%Z. lia.
      rewrite <-H5.
      assert (0 < to_Z n1 - 63)%Z. lia.
      assert ((-(to_Z n1 - 63)) mod wB = wB - (to_Z n1 - 63) mod wB)%Z. {
        apply Z_mod_nz_opp_full.
        rewrite Z.mod_small. lia.
        have Hn1bounded := (to_Z_bounded n1). lia. }
      assert (0 < wB - (to_Z n1 - 63))%Z.
      have Hn1bounded := (to_Z_bounded n1). lia.
      assert (wB - (to_Z n1 - 63) < wB)%Z. lia.
      rewrite H7.
      rewrite Z.mod_small.
      rewrite Z.sub_sub_distr.
      apply Z.le_sub_le_add_r.
      replace (63 - 63)%Z with 0%Z.
      have Hn1bounded := (to_Z_bounded n1). lia.
      lia.
      have Hn1bounded := (to_Z_bounded n1). lia.
      rewrite uint63_lsr63. rewrite to_Z_0. now cbn. lia. lia.
      apply rt_refl.
      dostep_nary' 2. eapply r_store_success; eauto.
      apply Hstep. } }
Qed.


End PRIMITIVE_TRANSLATION_CORRECT.
