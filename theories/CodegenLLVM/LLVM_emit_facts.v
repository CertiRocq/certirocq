(** * Syntactic facts about the emitter's helpers, for the simulation proof.

    - the root lists of safepoints ([hd_roots], [la_roots]) versus the free
      variables of the continuation;
    - the SSA environments after a safepoint ([env_set_list], [safepoint_env],
      [la_env]);
    - the [dtyp] shapes ([convert_typ]) of the emitter's expression and
      instruction helpers. *)

From Stdlib Require Import ZArith NArith List Lia String SetoidList Bool.
From CertiRocq.LambdaANF Require Import term term_util identifiers set_util Ensembles_util.
From CertiRocq.Common Require Import AstCommon.
From CertiRocq.CodegenLLVM Require Import LambdaANF_to_LLVM LLVM_convert LLVM_emit_syntax.
From Vellvm Require Import Syntax Semantics.DynamicValues.

Import ListNotations.
Open Scope Z_scope.

Unset Implicit Arguments.
Set Bullet Behavior "Strict Subproofs".

(* ------------------------------------------------------------------ *)
(** ** Free variables as a list *)

Lemma In_elements_fv e x : In x (PS.elements (exp_fv e)) <-> occurs_free e x.
Proof.
  destruct (exp_fv_correct e) as [H1 H2]. split; intros H.
  - apply H2. unfold Ensembles.In, FromSet, FromList. exact H.
  - apply H1 in H. unfold Ensembles.In, FromSet, FromList in H. exact H.
Qed.

Lemma hd_roots_spec fs x ys e' r :
  In r (hd_roots fs x ys e') <->
  is_fun fs r = false /\ ((occurs_free e' r /\ r <> x) \/ In r ys).
Proof.
  unfold hd_roots. rewrite filter_In, nodup_In, in_app_iff, negb_true_iff.
  split.
  - intros [[H|H] Hf]; split; auto. left. apply in_remove in H. rewrite In_elements_fv in H. exact H.
  - intros [Hf [[H1 H2]|H]]; split; auto. left. apply in_in_remove; auto. apply In_elements_fv. exact H1.
Qed.

Lemma la_roots_spec fs x e' r :
  In r (la_roots fs x e') <-> is_fun fs r = false /\ occurs_free e' r /\ r <> x.
Proof.
  unfold la_roots. rewrite filter_In, nodup_In, negb_true_iff.
  split.
  - intros [H Hf]. apply in_remove in H. rewrite In_elements_fv in H. tauto.
  - intros [Hf [H1 H2]]. split; auto. apply in_in_remove; auto. apply In_elements_fv. exact H1.
Qed.

Lemma hd_roots_nodup fs x ys e' : NoDup (hd_roots fs x ys e').
Proof. apply NoDup_filter. apply NoDup_nodup. Qed.

Lemma la_roots_nodup fs x e' : NoDup (la_roots fs x e').
Proof. apply NoDup_filter. apply NoDup_nodup. Qed.

(* ------------------------------------------------------------------ *)
(** ** SSA environments after a safepoint *)

Lemma env_set_list_notin env vs rs v : ~ In v vs -> env_set_list env vs rs v = env v.
Proof.
  revert rs. induction vs as [|w vs IH]; intros rs Hn; [reflexivity|].
  destruct rs as [|r rs]; [reflexivity|]. simpl. unfold env_set.
  destruct (Pos.eqb v w) eqn:E.
  - apply Pos.eqb_eq in E. subst. exfalso. apply Hn. left. reflexivity.
  - apply IH. intros Hin. apply Hn. right. exact Hin.
Qed.

Lemma env_set_list_nth env vs rs i v r :
  NoDup vs -> nth_error vs i = Some v -> nth_error rs i = Some r ->
  env_set_list env vs rs v = r.
Proof.
  revert rs i. induction vs as [|w vs IH]; intros rs i Hnd Hv Hr; [destruct i; discriminate|].
  destruct rs as [|r0 rs]; [destruct i; discriminate|].
  inversion Hnd as [|? ? Hw Hnd']; subst.
  destruct i as [|i]; simpl in Hv, Hr.
  - injection Hv as <-. injection Hr as <-. simpl. unfold env_set. rewrite Pos.eqb_refl. reflexivity.
  - simpl. unfold env_set. destruct (Pos.eqb v w) eqn:E.
    + apply Pos.eqb_eq in E. subst. exfalso. apply Hw. eapply nth_error_In; eauto.
    + eapply IH; eauto.
Qed.

Lemma nth_error_map_seq (f : nat -> raw_id) n i :
  (i < n)%nat -> nth_error (map f (seq 0 n)) i = Some (f i).
Proof.
  intros Hi. rewrite nth_error_map, nth_error_seq.
  apply Nat.ltb_lt in Hi. rewrite Hi. reflexivity.
Qed.

Lemma safepoint_env_root env seed roots i r :
  NoDup roots -> nth_error roots i = Some r ->
  safepoint_env env seed roots r = ssname seed (2000 + i).
Proof.
  intros Hnd Hr. unfold safepoint_env. apply (env_set_list_nth env roots _ i r); auto.
  apply (nth_error_map_seq (fun i => ssname seed (2000 + i))). apply nth_error_Some. rewrite Hr. discriminate.
Qed.

Lemma safepoint_env_other env seed roots r :
  ~ In r roots -> safepoint_env env seed roots r = env r.
Proof. intros H. unfold safepoint_env. apply env_set_list_notin. exact H. Qed.

Lemma la_env_root fs env fresh x e' i r :
  nth_error (la_roots fs x e') i = Some r ->
  la_env fs env fresh x e' r = ssname fresh (1000 + i).
Proof.
  intros Hr. unfold la_env. apply (env_set_list_nth env (la_roots fs x e') _ i r); auto; [apply la_roots_nodup|].
  apply (nth_error_map_seq (fun i => ssname fresh (1000 + i))). apply nth_error_Some. rewrite Hr. discriminate.
Qed.

Lemma la_env_other fs env fresh x e' r :
  ~ In r (la_roots fs x e') -> la_env fs env fresh x e' r = env r.
Proof. intros H. unfold la_env. apply env_set_list_notin. exact H. Qed.

(* ------------------------------------------------------------------ *)
(** ** [dtyp] shapes of the emitter's helpers *)

Definition i64 : dtyp := DTYPE_I 64.
Definition dptr : dtyp := DTYPE_Pointer.
Definition i32 : dtyp := DTYPE_I 32.
Definition dlit (n : nat) : LLVMAst.exp dtyp := EXP_Integer (Nat.to_num_int n).
Definition dlitZ (z : Z) : LLVMAst.exp dtyp := EXP_Integer (Z.to_num_int z).


Ltac conv :=
  cbn [store_fields spill_code reload_code phi_list];
  unfold load_field, load_header;
  unfold val_long, long_val, is_block, gep_field, gep_at, gep_tinfo, gep_arr, gep_struct, header_word,
    lit, litZ, nvar, evar, etinfo;
  repeat (rewrite ?cexp_Conversion, ?cexp_IBinop, ?cexp_ICmp, ?cexp_GEP, ?cexp_Ident, ?cexp_Integer,
          ?ccode_nil, ?ccode_cons, ?cinstr_Load, ?cinstr_Store, ?cinstr_Op, ?cty_val, ?cty_ptr, ?cty_tinfo, ?cty_i1, ?cty_i32,
          ?cty_val_array, ?cty_Pointer; unfold ctexp; cbn [fst snd map]);
  reflexivity.

Lemma cexp_lit n : cexp (lit n) = dlit n.
Proof. conv. Qed.

Lemma cexp_litZ z : cexp (litZ z) = dlitZ z.
Proof. conv. Qed.

Lemma cexp_nvar env v : cexp (nvar env v) = EXP_Ident (ID_Local (env v)).
Proof. conv. Qed.

Lemma cexp_evar v : cexp (evar v) = EXP_Ident (ID_Local (Raw (Zpos v))).
Proof. conv. Qed.

Lemma cexp_etinfo : cexp etinfo = EXP_Ident (ID_Local (Name "tinfo")).
Proof. conv. Qed.

Lemma cexp_gvar_fun fs env v :
  is_fun fs v = true ->
  cexp (gvar fs env v) =
  OP_Conversion (CONV_Impure Ptrtoint) dptr (EXP_Ident (ID_Global (Anon (Zpos v)))) i64.
Proof. intros H. unfold gvar. rewrite H. conv. Qed.

Lemma cexp_gvar_local fs env v :
  is_fun fs v = false -> cexp (gvar fs env v) = EXP_Ident (ID_Local (env v)).
Proof. intros H. unfold gvar. rewrite H. conv. Qed.

Lemma cexp_gcallee_fun fs env f :
  is_fun fs f = true -> cexp (gcallee fs env f) = EXP_Ident (ID_Global (Anon (Zpos f))).
Proof. intros H. unfold gcallee. rewrite H. conv. Qed.

Lemma cexp_gcallee_local fs env f :
  is_fun fs f = false ->
  cexp (gcallee fs env f) =
  OP_Conversion (CONV_Impure Inttoptr) i64 (EXP_Ident (ID_Local (env f))) dptr.
Proof. intros H. unfold gcallee. rewrite H. conv. Qed.

Lemma cexp_val_long e :
  cexp (val_long e) = OP_IBinop (Or false) i64 (OP_IBinop (Shl false false) i64 (cexp e) (dlit 1)) (dlit 1).
Proof. conv. Qed.

Lemma cexp_long_val e : cexp (long_val e) = OP_IBinop (AShr false) i64 (cexp e) (dlit 1).
Proof. conv. Qed.

Lemma cexp_is_block e :
  cexp (is_block e) = OP_ICmp false Eq i64 (OP_IBinop And i64 (cexp e) (dlit 1)) (dlit 0).
Proof. conv. Qed.

Lemma cexp_gep_field base n :
  cexp (gep_field base n) =
  OP_GetElementPtr i64
    (dptr, OP_Conversion (CONV_Impure Inttoptr) i64 (cexp base) dptr)
    [(i64, dlit (N.to_nat n))].
Proof. conv. Qed.

Lemma cexp_gep_at base n :
  cexp (gep_at base n) = OP_GetElementPtr i64 (dptr, cexp base) [(i64, dlit (N.to_nat n))].
Proof. conv. Qed.

Lemma cexp_gep_tinfo n :
  cexp (gep_tinfo n) =
  OP_GetElementPtr (cty tinfo_struct_ty) (dptr, EXP_Ident (ID_Local (Name "tinfo")))
    [(i32, dlit 0); (i32, dlit n)].
Proof. conv. Qed.

Lemma cexp_gep_arr n base i :
  cexp (gep_arr (TYPE_Array n val_ty) base i) =
  OP_GetElementPtr (DTYPE_Array false n i64) (dptr, cexp base) [(i32, dlit 0); (i64, dlit i)].
Proof. conv. Qed.

Lemma cexp_gep_struct base j :
  cexp (gep_struct frame_ty base j) =
  OP_GetElementPtr (cty frame_ty) (dptr, cexp base) [(i32, dlit 0); (i32, dlit j)].
Proof. conv. Qed.

Lemma cexp_header_word go ga t :
  cexp (header_word go ga t) = dlit (Nat.lor (Nat.shiftl (N.to_nat (ga t)) 10) (N.to_nat (go t))).
Proof. conv. Qed.

Lemma cinstr_load_field env y n :
  cinstr (load_field env y n) = INSTR_Load i64 (dptr, cexp (gep_field (nvar env y) n)) [].
Proof. conv. Qed.

Lemma cinstr_load_header env y :
  cinstr (load_header env y) =
  INSTR_Load i64
    (dptr,
     OP_Conversion (CONV_Impure Inttoptr) i64
       (OP_IBinop (Sub false false) i64 (EXP_Ident (ID_Local (env y))) (dlit 8)) dptr) [].
Proof. conv. Qed.

Lemma ccode_store_fields_nil fs env vp i : ccode (store_fields fs env vp i []) = [].
Proof. conv. Qed.

Lemma ccode_store_fields_cons fs env vp i y ys :
  ccode (store_fields fs env vp i (y :: ys)) =
  (IVoid (Z.of_N i), INSTR_Store (i64, cexp (gvar fs env y)) (dptr, cexp (gep_at vp i)) [], [])
    :: ccode (store_fields fs env vp (N.succ i) ys).
Proof. conv. Qed.

Lemma ccode_spill_nil env rootsp arr_ty i : ccode (spill_code env rootsp arr_ty i []) = [].
Proof. conv. Qed.

Lemma ccode_spill_cons env rootsp arr_ty i r rs :
  ccode (spill_code env rootsp arr_ty i (r :: rs)) =
  (IVoid 0%Z, INSTR_Store (i64, EXP_Ident (ID_Local (env r))) (dptr, cexp (gep_arr arr_ty rootsp i)) [], [])
    :: ccode (spill_code env rootsp arr_ty (S i) rs).
Proof. conv. Qed.

Lemma ccode_reload_nil seed rootsp arr_ty i : ccode (reload_code seed rootsp arr_ty i []) = [].
Proof. conv. Qed.

Lemma ccode_reload_cons seed rootsp arr_ty i r rs :
  ccode (reload_code seed rootsp arr_ty i (r :: rs)) =
  (IId (ssname seed (1000 + i)), INSTR_Load i64 (dptr, cexp (gep_arr arr_ty rootsp i)) [], [])
    :: ccode (reload_code seed rootsp arr_ty (S i) rs).
Proof. conv. Qed.

Lemma call_args_conv fs env ys :
  map (fun '(te, a) => (ctexp te, a)) (call_args fs env ys) =
  ((dptr, EXP_Ident (ID_Local (Name "tinfo"))), @nil param_attr)
    :: map (fun y => ((i64, cexp (gvar fs env y)), @nil param_attr)) ys.
Proof.
  unfold call_args. cbn [map]. f_equal.
  - unfold ctexp, etinfo; cbn [fst snd]. rewrite cty_tinfo, cexp_Ident. reflexivity.
  - rewrite map_map. apply map_ext. intros y. unfold ctexp; cbn [fst snd]. rewrite cty_val. reflexivity.
Qed.

Lemma cphis_nil env seed chk gc i : map (fun '(id, ph, md) => (id, tfmap cty ph, tfmap cty md)) (phi_list env seed chk gc i []) = [].
Proof. conv. Qed.

Lemma cphis_cons env seed chk gc i r rs :
  map (fun '(id, ph, md) => (id, tfmap cty ph, tfmap cty md)) (phi_list env seed chk gc i (r :: rs)) =
  (ssname seed (2000 + i),
   Phi i64 [(chk, EXP_Ident (ID_Local (env r))); (gc, EXP_Ident (ID_Local (ssname seed (1000 + i))))], [])
    :: map (fun '(id, ph, md) => (id, tfmap cty ph, tfmap cty md)) (phi_list env seed chk gc (S i) rs).
Proof.
  cbn [phi_list map]. f_equal. rewrite cphi_eq, cty_val. cbn [map]. unfold nvar. rewrite !cexp_Ident. reflexivity.
Qed.
