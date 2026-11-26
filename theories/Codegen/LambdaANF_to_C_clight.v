(* What the expressions and statements that [LambdaANF_to_C] emits do in Clight. *)

From Stdlib Require Import ZArith.ZArith Lists.List micromega.Lia.
From compcert Require Import lib.Coqlib lib.Maps lib.Integers common.AST common.Values
     common.Errors common.Memory common.Events common.Globalenvs common.Smallstep
     cfrontend.Ctypes cfrontend.Cop cfrontend.Clight Clightdefs.
From CertiRocq.Common Require Import compM.
From CertiRocq.LambdaANF Require Import term.
From CertiRocq.Codegen Require Import LambdaANF_to_C LambdaANF_to_C_static LambdaANF_to_C_rel
     LambdaANF_to_C_memory.

Import ListNotations.
Local Open Scope Z_scope.

Local Arguments Z.mul : simpl never.
Local Arguments Z.add : simpl never.
Local Arguments Z.sub : simpl never.

(** * Machine integers *)

Lemma ptrofs_max_unsigned : Ptrofs.max_unsigned = 18446744073709551615.
Proof. reflexivity. Qed.
Lemma ptrofs_max_signed : Ptrofs.max_signed = 9223372036854775807.
Proof. reflexivity. Qed.
Lemma ptrofs_min_signed : Ptrofs.min_signed = -9223372036854775808.
Proof. reflexivity. Qed.
Lemma int64_max_unsigned : Int64.max_unsigned = 18446744073709551615.
Proof. reflexivity. Qed.
Lemma int64_max_signed : Int64.max_signed = 9223372036854775807.
Proof. reflexivity. Qed.
Lemma int64_min_signed : Int64.min_signed = -9223372036854775808.
Proof. reflexivity. Qed.

(* Arithmetic with the bounds of machine integers *)
Ltac int_lia :=
  rewrite ?ptrofs_max_unsigned, ?ptrofs_max_signed, ?ptrofs_min_signed,
          ?int64_max_unsigned, ?int64_max_signed, ?int64_min_signed in *; lia.

Lemma ptrofs_add_repr a b :
  Ptrofs.add (Ptrofs.repr a) (Ptrofs.repr b) = Ptrofs.repr (a + b).
Proof.
  unfold Ptrofs.add. apply Ptrofs.eqm_samerepr.
  apply Ptrofs.eqm_add; apply Ptrofs.eqm_sym, Ptrofs.eqm_unsigned_repr.
Qed.

Lemma ptrofs_mul_repr a b :
  Ptrofs.mul (Ptrofs.repr a) (Ptrofs.repr b) = Ptrofs.repr (a * b).
Proof.
  unfold Ptrofs.mul. apply Ptrofs.eqm_samerepr.
  apply Ptrofs.eqm_mult; apply Ptrofs.eqm_sym, Ptrofs.eqm_unsigned_repr.
Qed.

Lemma ptrofs_of_int64_repr z :
  Ptrofs.of_int64 (Int64.repr z) = Ptrofs.repr z.
Proof.
  unfold Ptrofs.of_int64. apply Ptrofs.eqm_samerepr.
  unfold Ptrofs.eqm. rewrite (Ptrofs.modulus_eq64 ptr64).
  apply Int64.eqm_sym, Int64.eqm_unsigned_repr.
Qed.

Lemma ptrofs_add_repr_r ofs z :
  Ptrofs.add ofs (Ptrofs.repr z) = Ptrofs.repr (Ptrofs.unsigned ofs + z).
Proof.
  rewrite <- (Ptrofs.repr_unsigned ofs) at 1. apply ptrofs_add_repr.
Qed.

(* The types and constants of the generator on a 64-bit target *)
Lemma const_eq z t : const z t = Econst_long (Int64.repr z) t.
Proof. reflexivity. Qed.

(* A word can be cast between the types of values, integers and pointers *)
Definition is_word (v : Values.val) : Prop :=
  match v with
  | Vptr _ _ | Vlong _ => True
  | _ => False
  end.

Lemma sem_cast_word v t1 t2 m :
  classify_cast t1 t2 = cast_case_pointer -> is_word v -> sem_cast v t1 t2 m = Some v.
Proof.
  intros Hc Hw. unfold sem_cast. rewrite Hc. destruct v; try contradiction; reflexivity.
Qed.

Lemma statement_eq_skip (s : statement) : {s = Sskip} + {s <> Sskip}.
Proof. destruct s; (left; reflexivity) || (right; discriminate). Qed.

(* The structs of [composites] are structs of the program. It may have others. *)
Definition structs_ok (ge : genv) : Prop :=
  exists ce, build_composite_env composites = OK ce /\
             forall id co, ce ! id = Some co -> (genv_cenv ge) ! id = Some co.

Section Clight.

  Context (ge : genv).
  Hypothesis Hstructs : structs_ok ge.

  (** * The structs *)

  Lemma tinfo_struct :
    exists co, (genv_cenv ge) ! threadInfoId = Some co /\
               field_offset ge allocId (co_members co) = OK (alloc_ofs, Full) /\
               field_offset ge limitId (co_members co) = OK (limit_ofs, Full) /\
               field_offset ge argsId (co_members co) = OK (args_ofs, Full) /\
               field_offset ge fpId (co_members co) = OK (fp_ofs, Full).
  Proof.
    pose proof Hstructs as (ce & Hce & Hsub).
    destruct (build_composite_env_charact threadInfoId Struct
                [ Member_plain allocId (tptr tvalue);
                  Member_plain limitId (tptr tvalue);
                  Member_plain heapId (tptr (Tstruct heapId noattr));
                  Member_plain argsId (tarray tvalue max_args);
                  Member_plain fpId (tptr frameT);
                  Member_plain nallocId tuintnat;
                  Member_plain odataId (tptr tvoid) ] noattr _ _ Hce)
      as (co & Hco & Hm & _).
    { right. left. reflexivity. }
    exists co. split; [apply Hsub; exact Hco |]. rewrite Hm. repeat split; reflexivity.
  Qed.

  Lemma frame_struct :
    exists co, (genv_cenv ge) ! stackFrameId = Some co /\
               field_offset ge nextId (co_members co) = OK (next_ofs, Full) /\
               field_offset ge rootId (co_members co) = OK (root_ofs, Full) /\
               field_offset ge prevId (co_members co) = OK (prev_ofs, Full) /\
               co_sizeof co = 24.
  Proof.
    pose proof Hstructs as (ce & Hce & Hsub).
    destruct (build_composite_env_charact stackFrameId Struct
                [ Member_plain nextId (tptr tvalue);
                  Member_plain rootId (tptr tvalue);
                  Member_plain prevId (tptr frameT) ] noattr _ _ Hce)
      as (co & Hco & Hm & Ha & Hsu).
    { left. reflexivity. }
    exists co. split; [apply Hsub; exact Hco |]. rewrite Hm. repeat split; try reflexivity.
    pose proof (build_composite_env_consistent _ _ Hce _ _ Hco) as Hcons.
    rewrite (co_consistent_sizeof _ _ Hcons), (co_consistent_alignof _ _ Hcons), Hm, Ha, Hsu.
    reflexivity.
  Qed.

  Lemma sizeof_frame : sizeof ge frameT = 24.
  Proof.
    destruct frame_struct as (co & Hco & _ & _ & _ & Hs). simpl. rewrite Hco. auto.
  Qed.

  Lemma sizeof_roots n : sizeof ge (tarray tvalue n) = 8 * Z.max 0 n.
  Proof. reflexivity. Qed.

  (** * Expressions *)

  Section Expr.

    Context (e : env) (le : temp_env) (m : mem).

    Lemma eval_const z t : eval_expr ge e le m (const z t) (Vlong (Int64.repr z)).
    Proof. rewrite const_eq. constructor. Qed.

    (* The address of a field of the thread info *)
    Lemma eval_tinfo_field tb tofs f t delta :
      le ! tinfoId = Some (Vptr tb (Ptrofs.repr tofs)) ->
      (forall co, (genv_cenv ge) ! threadInfoId = Some co ->
                  field_offset ge f (co_members co) = OK (delta, Full)) ->
      eval_lvalue ge e le m (tinfo_field f t) tb (Ptrofs.repr (tofs + delta)) Full.
    Proof.
      intros Hle Hf. destruct tinfo_struct as (co & Hco & _).
      rewrite <- ptrofs_add_repr. unfold tinfo_field.
      eapply eval_Efield_struct; eauto.
      - eapply eval_Elvalue.
        + apply eval_Ederef. apply eval_Etempvar. eauto.
        + apply deref_loc_copy. reflexivity.
      - reflexivity.
    Qed.

    Lemma eval_tinfo_alloc tb tofs :
      le ! tinfoId = Some (Vptr tb (Ptrofs.repr tofs)) ->
      eval_lvalue ge e le m tinfo_alloc tb (Ptrofs.repr (tofs + alloc_ofs)) Full.
    Proof.
      intros. eapply eval_tinfo_field; eauto.
      intros co Hco. destruct tinfo_struct as (co' & Hco' & H1 & _). congruence.
    Qed.

    Lemma eval_tinfo_limit tb tofs :
      le ! tinfoId = Some (Vptr tb (Ptrofs.repr tofs)) ->
      eval_lvalue ge e le m tinfo_limit tb (Ptrofs.repr (tofs + limit_ofs)) Full.
    Proof.
      intros. eapply eval_tinfo_field; eauto.
      intros co Hco. destruct tinfo_struct as (co' & Hco' & _ & H1 & _). congruence.
    Qed.

    Lemma eval_tinfo_fp tb tofs :
      le ! tinfoId = Some (Vptr tb (Ptrofs.repr tofs)) ->
      eval_lvalue ge e le m tinfo_fp tb (Ptrofs.repr (tofs + fp_ofs)) Full.
    Proof.
      intros. eapply eval_tinfo_field; eauto.
      intros co Hco. destruct tinfo_struct as (co' & Hco' & _ & _ & _ & H1). congruence.
    Qed.

    (* Reading a word at an address *)
    Lemma eval_load a b ofs v :
      eval_lvalue ge e le m a b ofs Full ->
      access_mode (typeof a) = By_value Mptr ->
      Mem.load Mptr m b (Ptrofs.unsigned ofs) = Some v ->
      eval_expr ge e le m a v.
    Proof.
      intros Hlv Ham Hl. eapply eval_Elvalue; eauto. eapply deref_loc_value; eauto.
    Qed.

    (* The address of [a[i]], where the elements of [a] are words *)
    Lemma eval_index a i t b ofs :
      eval_expr ge e le m a (Vptr b ofs) ->
      classify_add (typeof a) tintnat = add_case_pl t ->
      sizeof ge t = 8 ->
      eval_lvalue ge e le m (index a i t) b (Ptrofs.add ofs (Ptrofs.repr (8 * i))) Full.
    Proof.
      intros Ha Hc Hs. unfold index. apply eval_Ederef.
      eapply eval_Ebinop; eauto using eval_const.
      rewrite const_eq. simpl. unfold sem_add. rewrite Hc. simpl.
      rewrite Hs, ptrofs_of_int64_repr, ptrofs_mul_repr. reflexivity.
    Qed.

    (* The address of [tinfo->args[i]] *)
    Lemma eval_arg tb tofs i :
      le ! tinfoId = Some (Vptr tb (Ptrofs.repr tofs)) ->
      eval_lvalue ge e le m (arg i) tb (Ptrofs.repr (tofs + args_ofs + 8 * Z.of_nat i)) Full.
    Proof.
      intros Hle. unfold arg.
      replace (Ptrofs.repr (tofs + args_ofs + 8 * Z.of_nat i))
        with (Ptrofs.add (Ptrofs.repr (tofs + args_ofs)) (Ptrofs.repr (8 * Z.of_nat i)))
        by apply ptrofs_add_repr.
      apply eval_index; try reflexivity.
      eapply eval_Elvalue.
      - eapply eval_tinfo_field with (delta := args_ofs); eauto.
        intros co Hco. destruct tinfo_struct as (co' & Hco' & _ & _ & H1 & _). congruence.
      - apply deref_loc_reference. reflexivity.
    Qed.

    (* The address of the word number [i] of the block at [b, ofs] *)
    Lemma eval_field x i b ofs :
      eval_expr ge e le m x (Vptr b ofs) ->
      classify_cast (typeof x) (tptr tvalue) = cast_case_pointer ->
      eval_lvalue ge e le m (field x i) b (Ptrofs.add ofs (Ptrofs.repr (8 * i))) Full.
    Proof.
      intros Hx Hc. unfold field. apply eval_index; try reflexivity.
      eapply eval_Ecast; eauto. apply sem_cast_word; simpl; auto.
    Qed.

    (* The address of the header of the block at [b, ofs] *)
    Lemma eval_header x b ofs :
      eval_expr ge e le m x (Vptr b ofs) ->
      classify_cast (typeof x) (tptr tuintnat) = cast_case_pointer ->
      eval_lvalue ge e le m (header x) b (Ptrofs.add ofs (Ptrofs.repr (8 * -1))) Full.
    Proof.
      intros Hx Hc. unfold header. apply eval_index; try reflexivity.
      eapply eval_Ecast; eauto. apply sem_cast_word; simpl; auto.
    Qed.

    (* The low bits of the header of the block that [x] points to *)
    Lemma eval_tag x b ofs hdr :
      eval_expr ge e le m x (Vptr b ofs) ->
      classify_cast (typeof x) (tptr tuintnat) = cast_case_pointer ->
      8 <= Ptrofs.unsigned ofs ->
      Mem.load Mptr m b (Ptrofs.unsigned ofs - 8) = Some (Vlong hdr) ->
      eval_expr ge e le m (tag x) (Vlong (Int64.and hdr (Int64.repr 255))).
    Proof.
      intros Hx Hc Hofs Hload. unfold tag. eapply eval_Ebinop.
      - eapply eval_load.
        + apply eval_header; eauto.
        + reflexivity.
        + rewrite ptrofs_add_repr_r. rewrite Ptrofs.unsigned_repr.
          * replace (Ptrofs.unsigned ofs + 8 * -1) with (Ptrofs.unsigned ofs - 8) by lia.
            exact Hload.
          * pose proof (Ptrofs.unsigned_range_2 ofs). lia.
      - apply eval_const.
      - rewrite const_eq. reflexivity.
    Qed.

    Lemma switch_arg_long n : sem_switch_arg (Vlong n) tuintnat = Some (Int64.unsigned n).
    Proof. reflexivity. Qed.

    (** Variables *)

    Context (nparam : nat) (fenv : M.t nat).

    (* The word that the variable [x] stands for: a function is the address of its symbol,
       any other variable is a C variable *)
    Definition var_val (x : var) (w : Values.val) : Prop :=
      match M.get x fenv with
      | Some _ => exists b, Genv.find_symbol ge x = Some b /\ w = Vptr b Ptrofs.zero
      | None => le ! x = Some w
      end.

    Lemma eval_var_expr x w :
      var_val x w -> is_word w ->
      (M.get x fenv <> None -> e ! x = None) ->
      eval_expr ge e le m (var_expr nparam fenv x) w.
    Proof.
      unfold var_val, var_expr. intros Hv Hw He. destruct (M.get x fenv) as [n |].
      - destruct Hv as (b & Hb & ->).
        eapply eval_Ecast.
        + eapply eval_Elvalue.
          * apply eval_Evar_global; [apply He; discriminate | eassumption].
          * apply deref_loc_reference. reflexivity.
        + reflexivity.
      - apply eval_Etempvar. auto.
    Qed.

    Lemma typeof_var_expr x : typeof (var_expr nparam fenv x) = tvalue.
    Proof. unfold var_expr. destruct (M.get x fenv); reflexivity. Qed.

    (* The arguments of a call *)
    Lemma eval_var_exprs : forall ys ws,
        Forall2 var_val ys ws -> Forall is_word ws ->
        (forall y, In y ys -> M.get y fenv <> None -> e ! y = None) ->
        eval_exprlist ge e le m (map (var_expr nparam fenv) ys) (repeat tvalue (length ys)) ws.
    Proof.
      induction 1 as [| y w ys ws Hy Hys IH]; intros Hw He.
      - constructor.
      - inv Hw. cbn [map length repeat]. econstructor.
        + apply eval_var_expr; eauto. intros Hfy. apply He; auto. now left.
        + rewrite typeof_var_expr. apply sem_cast_word; auto.
        + apply IH; auto. intros z Hz. apply He. now right.
    Qed.

    (** The frame and the roots of the function *)

    Context (fb rb : block) (nroots : Z).
    Hypothesis Hframe : e ! frameId = Some (fb, frameT).
    Hypothesis Hroots : e ! rootsId = Some (rb, tarray tvalue nroots).

    Lemma eval_roots : eval_expr ge e le m (roots nroots) (Vptr rb Ptrofs.zero).
    Proof.
      eapply eval_Elvalue.
      - apply eval_Evar_local. eauto.
      - apply deref_loc_reference. reflexivity.
    Qed.

    (* The address of [roots[i]] *)
    Lemma eval_root i :
      eval_lvalue ge e le m (root nroots i) rb (Ptrofs.repr (8 * Z.of_nat i)) Full.
    Proof.
      unfold root. rewrite <- (Ptrofs.add_zero_l (Ptrofs.repr (8 * Z.of_nat i))).
      apply eval_index; try reflexivity. apply eval_roots.
    Qed.

    (* [roots + k] *)
    Lemma eval_roots_plus k :
      eval_expr ge e le m (Ebinop Oadd (roots nroots) (const k tintnat) (tptr tvalue))
                (Vptr rb (Ptrofs.repr (8 * k))).
    Proof.
      assert (Hc : classify_add (tarray tvalue nroots) tintnat = add_case_pl tvalue)
        by reflexivity.
      eapply eval_Ebinop; eauto using eval_roots, eval_const.
      rewrite const_eq. simpl. unfold sem_add. rewrite Hc. simpl.
      change (sizeof ge tvalue) with 8.
      rewrite ptrofs_of_int64_repr, ptrofs_mul_repr, Ptrofs.add_zero_l. reflexivity.
    Qed.

    Lemma eval_frame_addr :
      eval_expr ge e le m (Eaddrof LambdaANF_to_C.frame (tptr frameT)) (Vptr fb Ptrofs.zero).
    Proof. apply eval_Eaddrof. apply eval_Evar_local. eauto. Qed.

    (* The address of a field of [frame] *)
    Lemma eval_frame_field f t delta :
      (forall co, (genv_cenv ge) ! stackFrameId = Some co ->
                  field_offset ge f (co_members co) = OK (delta, Full)) ->
      eval_lvalue ge e le m (frame_field f t) fb (Ptrofs.repr delta) Full.
    Proof.
      intros Hf. destruct frame_struct as (co & Hco & _).
      rewrite <- (Ptrofs.add_zero_l (Ptrofs.repr delta)). unfold frame_field.
      eapply eval_Efield_struct; eauto.
      - eapply eval_Elvalue.
        + apply eval_Evar_local. eauto.
        + apply deref_loc_copy. reflexivity.
      - reflexivity.
    Qed.

    Lemma eval_frame_next :
      eval_lvalue ge e le m (frame_field nextId (tptr tvalue)) fb (Ptrofs.repr next_ofs) Full.
    Proof.
      apply eval_frame_field. intros co Hco.
      destruct frame_struct as (co' & Hco' & H1 & _). congruence.
    Qed.

    Lemma eval_frame_root :
      eval_lvalue ge e le m (frame_field rootId (tptr tvalue)) fb (Ptrofs.repr root_ofs) Full.
    Proof.
      apply eval_frame_field. intros co Hco.
      destruct frame_struct as (co' & Hco' & _ & H1 & _). congruence.
    Qed.

    Lemma eval_frame_prev :
      eval_lvalue ge e le m (frame_field prevId (tptr frameT)) fb (Ptrofs.repr prev_ofs) Full.
    Proof.
      apply eval_frame_field. intros co Hco.
      destruct frame_struct as (co' & Hco' & _ & _ & H1 & _). congruence.
    Qed.

  End Expr.

  Lemma bool_val_of_bool b m : bool_val (Val.of_bool b) tint m = Some b.
  Proof. destruct b; reflexivity. Qed.

  (* [tinfo->limit - alloc < n]: whether fewer than [n] words are free *)
  Lemma eval_room_test e le m ab a lim n :
    0 <= a <= lim -> lim <= Ptrofs.max_unsigned -> lim - a <= Ptrofs.max_signed ->
    0 <= n <= Int64.max_signed ->
    eval_expr ge e le m tinfo_limit (Vptr ab (Ptrofs.repr lim)) ->
    le ! allocId = Some (Vptr ab (Ptrofs.repr a)) ->
    eval_expr ge e le m
              (Ebinop Olt (Ebinop Osub tinfo_limit alloc tintnat) (const n tintnat) tint)
              (Val.of_bool (if zlt ((lim - a) / 8) n then true else false)).
  Proof.
    intros Ha Hlim Hsz Hn Hl Hal.
    assert (Hq : 0 <= (lim - a) / 8 <= lim - a).
    { split; [apply Z.div_pos; lia |]. apply Z.div_le_upper_bound; lia. }
    eapply eval_Ebinop.
    - eapply eval_Ebinop; [exact Hl | apply eval_Etempvar; exact Hal |].
      assert (Hc : classify_sub (tptr tvalue) (tptr tvalue) = sub_case_pp tvalue) by reflexivity.
      simpl. unfold sem_sub. change (typeof tinfo_limit) with (tptr tvalue). rewrite Hc.
      change (sizeof ge tvalue) with 8. rewrite dec_eq_true. simpl. reflexivity.
    - apply eval_const.
    - rewrite const_eq.
      assert (Hcmp : forall x y, sem_cmp Clt (Vlong x) tintnat (Vlong y) tintnat m
                                 = Some (Val.of_bool (Int64.lt x y))) by reflexivity.
      match goal with
      | [ |- sem_binary_operation _ _ (Vptrofs ?X) _ _ _ _ = _ ] =>
        change (sem_cmp Clt (Vlong (Ptrofs.to_int64 X)) tintnat (Vlong (Int64.repr n)) tintnat m
                = Some (Val.of_bool (if zlt ((lim - a) / 8) n then true else false)))
      end.
      rewrite Hcmp. f_equal. f_equal.
      unfold Ptrofs.divs, Ptrofs.sub.
      rewrite !Ptrofs.unsigned_repr by int_lia.
      rewrite (Ptrofs.signed_repr (lim - a)) by int_lia.
      rewrite (Ptrofs.signed_repr 8) by int_lia.
      rewrite Z.quot_div_nonneg by lia.
      unfold Ptrofs.to_int64. rewrite Ptrofs.unsigned_repr by int_lia.
      unfold Int64.lt. rewrite !Int64.signed_repr by int_lia.
      destruct (zlt ((lim - a) / 8) n); reflexivity.
  Qed.

  (** * Statements *)

  (* The statement [s] runs from [le, m] to [le', m'] and falls through *)
  Definition runs (f : function) (e : env) (s : statement) (le : temp_env) (m : mem)
             (le' : temp_env) (m' : mem) : Prop :=
    (forall k, star step2 ge (Clight.State f s k e le m) E0 (Clight.State f Sskip k e le' m')) /\
    (s = Sskip -> le' = le /\ m' = m).

  Lemma runs_skip f e le m : runs f e Sskip le m le m.
  Proof. split; auto. intros. apply star_refl. Qed.

  Lemma runs_seq f e s1 s2 le m le1 m1 le2 m2 :
    runs f e s1 le m le1 m1 -> runs f e s2 le1 m1 le2 m2 ->
    runs f e (seq s1 s2) le m le2 m2.
  Proof.
    intros [H1 E1] [H2 E2].
    destruct (statement_eq_skip s1) as [-> | N1].
    { destruct (E1 eq_refl); subst. simpl. split; auto. }
    destruct (statement_eq_skip s2) as [-> | N2].
    { destruct (E2 eq_refl); subst. replace (seq s1 Sskip) with s1 by (destruct s1; reflexivity).
      split; auto. }
    replace (seq s1 s2) with (Ssequence s1 s2) by (destruct s1; try congruence; destruct s2; try congruence; reflexivity).
    split; [| discriminate]. intros k.
    eapply star_step; [apply step_seq | | reflexivity].
    eapply star_trans; [apply H1 | | reflexivity].
    eapply star_step; [apply step_skip_seq | apply H2 | reflexivity].
  Qed.

  (* After [s1] the statement [seq s1 s2] continues with [s2] *)
  Lemma seq_star f e s1 s2 k le m le1 m1 :
    runs f e s1 le m le1 m1 ->
    star step2 ge (Clight.State f (seq s1 s2) k e le m) E0 (Clight.State f s2 k e le1 m1).
  Proof.
    intros [H1 E1].
    destruct (statement_eq_skip s1) as [-> | N1].
    { destruct (E1 eq_refl); subst. simpl. apply star_refl. }
    destruct (statement_eq_skip s2) as [-> | N2].
    { replace (seq s1 Sskip) with s1 by (destruct s1; reflexivity). apply H1. }
    replace (seq s1 s2) with (Ssequence s1 s2) by (destruct s1; try congruence; destruct s2; try congruence; reflexivity).
    eapply star_step; [apply step_seq | | reflexivity].
    eapply star_trans; [apply H1 | | reflexivity].
    eapply star_step; [apply step_skip_seq | apply star_refl | reflexivity].
  Qed.

  Lemma runs_set f e x a le m v :
    eval_expr ge e le m a v ->
    runs f e (Sset x a) le m (PTree.set x v le) m.
  Proof.
    intros Ha. split; [| discriminate]. intros k. apply star_one. constructor. auto.
  Qed.

  (* A store of a word *)
  Lemma runs_assign f e a1 a2 le m b ofs v m' :
    eval_lvalue ge e le m a1 b ofs Full ->
    eval_expr ge e le m a2 v ->
    access_mode (typeof a1) = By_value Mptr ->
    classify_cast (typeof a2) (typeof a1) = cast_case_pointer ->
    is_word v ->
    Mem.store Mptr m b (Ptrofs.unsigned ofs) v = Some m' ->
    runs f e (Sassign a1 a2) le m le m'.
  Proof.
    intros Hlv Hv Ham Hc Hw Hst. split; [| discriminate]. intros k. apply star_one.
    eapply step_assign; eauto.
    - apply sem_cast_word; auto.
    - eapply assign_loc_value; eauto.
  Qed.

  Lemma runs_ifthenelse f e a s1 s2 le m v b le' m' :
    eval_expr ge e le m a v ->
    bool_val v (typeof a) m = Some b ->
    runs f e (if b then s1 else s2) le m le' m' ->
    runs f e (Sifthenelse a s1 s2) le m le' m'.
  Proof.
    intros Ha Hb [Hr _]. split; [| discriminate]. intros k.
    eapply star_step; [eapply step_ifthenelse; eauto | apply Hr | reflexivity].
  Qed.

  (* A call whose callee returns [w] *)
  Lemma runs_call f e le m optid a al tyargs tyres cc vf vargs fd w m' :
    classify_fun (typeof a) = fun_case_f tyargs tyres cc ->
    eval_expr ge e le m a vf ->
    eval_exprlist ge e le m al tyargs vargs ->
    Genv.find_funct ge vf = Some fd ->
    type_of_fundef fd = Tfunction tyargs tyres cc ->
    (forall k, is_call_cont k ->
               star step2 ge (Callstate fd vargs k m) E0 (Returnstate w k m')) ->
    runs f e (Scall optid a al) le m (set_opttemp optid w le) m'.
  Proof.
    intros Hc Ha Hal Hf Hty Hcall. split; [| discriminate]. intros k.
    eapply star_step; [eapply step_call; eauto | | reflexivity].
    eapply star_trans; [apply Hcall; exact I | | reflexivity].
    apply star_one. apply step_returnstate.
  Qed.

  (* A [return] frees the variables of the function *)
  Lemma star_return f a k e le m v m' :
    eval_expr ge e le m a v ->
    sem_cast v (typeof a) (fn_return f) m = Some v ->
    Mem.free_list m (blocks_of_env ge e) = Some m' ->
    star step2 ge (Clight.State f (Sreturn (Some a)) k e le m) E0 (Returnstate v (call_cont k) m').
  Proof.
    intros. apply star_one. eapply step_return_1; eauto.
  Qed.

  (* A switch goes to the first case with the key of the value *)
  Lemma star_switch f e le m a l v z s k :
    eval_expr ge e le m a v ->
    sem_switch_arg v (typeof a) = Some z ->
    first_key l z s ->
    exists k', star step2 ge (Clight.State f (switch a l) k e le m) E0 (Clight.State f s k' e le m) /\
               (k' = k \/ exists rest, k' = Kseq rest (Kswitch k)).
  Proof.
    intros Ha Hz Hk.
    assert (Hsw : star step2 ge (Clight.State f (Sswitch a (labeled l)) k e le m) E0
                       (Clight.State f s (Kseq (seq_of_labeled_statement
                                                  (match select_switch z (labeled l) with
                                                   | LScons _ _ ls => ls
                                                   | LSnil => LSnil
                                                   end)) (Kswitch k)) e le m)).
    { destruct (select_switch_labeled l z s Hk) as (o & ls & Hsel).
      eapply star_step; [eapply step_switch; eauto | | reflexivity].
      rewrite Hsel. simpl. apply star_one. apply step_seq. }
    destruct l as [| [z0 s0] l].
    - destruct Hk as (pre & post & H & _). destruct pre; discriminate.
    - destruct l as [| c l].
      + apply first_key_single in Hk. subst s0. exists k. split; [apply star_refl | now left].
      + eexists. split; [exact Hsw | right; eauto].
  Qed.

  (** * Words in memory *)

  Lemma store_words_exists ws : forall m b o,
      Mem.range_perm m b o (o + 8 * Z.of_nat (length ws)) Cur Writable -> (8 | o) ->
      exists m', store_words m b o ws = Some m'.
  Proof.
    induction ws as [| w ws IH]; simpl; intros m b o Hp Ha; [eauto |].
    destruct (Mem.valid_access_store m Mptr b o w) as [m1 Hm1].
    { split; auto. intros i Hi. apply Hp. change (size_chunk Mptr) with 8 in Hi. lia. }
    rewrite Hm1. apply IH.
    - intros i Hi. eapply Mem.perm_store_1; eauto. apply Hp. lia.
    - apply Z.divide_add_r; auto. apply Z.divide_refl.
  Qed.

  (** * Arguments in the thread info *)

  Section Args.

    Context (nparam : nat) (fenv : M.t nat) (f : function) (e : env).
    Context (tb : block) (tofs : Z).
    Hypothesis Htofs : 0 <= tofs /\ tofs + tinfo_size <= Ptrofs.max_unsigned.

    Lemma arg_address i :
      Z.of_nat i < max_args ->
      Ptrofs.unsigned (Ptrofs.repr (tofs + args_ofs + 8 * Z.of_nat i))
      = tofs + args_ofs + 8 * Z.of_nat i.
    Proof. intros. apply Ptrofs.unsigned_repr. ofs_lia. Qed.

    (* [tinfo->args[i] = y] for the variables [ys] *)
    Lemma runs_store_args le : forall ys i ws m m',
        le ! tinfoId = Some (Vptr tb (Ptrofs.repr tofs)) ->
        Forall2 (var_val le fenv) ys ws -> Forall is_word ws ->
        (forall y, In y ys -> M.get y fenv <> None -> e ! y = None) ->
        Z.of_nat i + Z.of_nat (length ys) <= max_args ->
        store_words m tb (tofs + args_ofs + 8 * Z.of_nat i) ws = Some m' ->
        runs f e (store_args nparam fenv i ys) le m le m'.
    Proof.
      induction ys as [| y ys IH]; intros i ws m m' Hle Hv Hw He Hn Hst; inv Hv.
      - inv Hst. apply runs_skip.
      - simpl in Hst. destruct (Mem.store Mptr m tb _ y0) as [m1 |] eqn:Hm1; [| discriminate].
        inv Hw. cbn [store_args]. simpl in Hn. eapply runs_seq.
        + eapply runs_assign.
          * apply eval_arg. eauto.
          * apply eval_var_expr; eauto. intros. apply He; auto. now left.
          * reflexivity.
          * rewrite typeof_var_expr. reflexivity.
          * auto.
          * rewrite arg_address by lia. eauto.
        + apply IH with (ws := l'); auto.
          * intros. apply He; auto. now right.
          * lia.
          * rewrite <- Hst. f_equal. lia.
    Qed.

    (* [tinfo->args[i] = x] for the C variables [xs] *)
    Lemma runs_save_args le : forall xs i ws m m',
        le ! tinfoId = Some (Vptr tb (Ptrofs.repr tofs)) ->
        Forall2 (fun x w => le ! x = Some w) xs ws -> Forall is_word ws ->
        Z.of_nat i + Z.of_nat (length xs) <= max_args ->
        store_words m tb (tofs + args_ofs + 8 * Z.of_nat i) ws = Some m' ->
        runs f e (save_args i xs) le m le m'.
    Proof.
      induction xs as [| x xs IH]; intros i ws m m' Hle Hv Hw Hn Hst; inv Hv.
      - inv Hst. apply runs_skip.
      - simpl in Hst. destruct (Mem.store Mptr m tb _ y) as [m1 |] eqn:Hm1; [| discriminate].
        inv Hw. cbn [save_args]. simpl in Hn. eapply runs_seq.
        + eapply runs_assign.
          * apply eval_arg. eauto.
          * apply eval_Etempvar. eauto.
          * reflexivity.
          * reflexivity.
          * auto.
          * rewrite arg_address by lia. eauto.
        + apply IH with (ws := l'); auto.
          * lia.
          * rewrite <- Hst. f_equal. lia.
    Qed.

    (* Assigns the words [ws] to the C variables [xs] *)
    Fixpoint set_temps (xs : list ident) (ws : list Values.val) (le : temp_env) : temp_env :=
      match xs, ws with
      | x :: xs', w :: ws' => set_temps xs' ws' (PTree.set x w le)
      | _, _ => le
      end.

    Lemma set_temps_other : forall xs ws le y,
        ~ In y xs -> (set_temps xs ws le) ! y = le ! y.
    Proof.
      induction xs as [| x xs IH]; intros ws le y Hy; [reflexivity |].
      destruct ws as [| w ws]; [reflexivity |]. simpl.
      rewrite IH by (intros H; apply Hy; now right).
      apply PTree.gso. intros ->. apply Hy. now left.
    Qed.

    Lemma set_temps_nth : forall xs ws le j x w,
        NoDup xs -> nth_error xs j = Some x -> nth_error ws j = Some w ->
        (set_temps xs ws le) ! x = Some w.
    Proof.
      induction xs as [| x0 xs IH]; intros ws le j x w Hnd Hx Hw; [destruct j; discriminate |].
      destruct ws as [| w0 ws]; [destruct j; discriminate |]. inv Hnd.
      destruct j as [| j]; simpl in *.
      - inv Hx. inv Hw. rewrite set_temps_other by auto. apply PTree.gss.
      - eapply IH; eauto.
    Qed.

    Lemma set_temps_app : forall xs1 ws1 xs2 ws2 le,
        length xs1 = length ws1 ->
        set_temps (xs1 ++ xs2) (ws1 ++ ws2) le = set_temps xs2 ws2 (set_temps xs1 ws1 le).
    Proof.
      induction xs1 as [| x xs1 IH]; intros ws1 xs2 ws2 le Hlen.
      - destruct ws1; [reflexivity | discriminate].
      - destruct ws1 as [| w ws1]; [discriminate |]. simpl. apply IH. simpl in Hlen. lia.
    Qed.

    (* The C parameters [xs] take the arguments [ws] *)
    Lemma bind_parameter_temps_set : forall xs ws le,
        length xs = length ws ->
        bind_parameter_temps (map (fun x => (x, tvalue)) xs) ws le = Some (set_temps xs ws le).
    Proof.
      induction xs as [| x xs IH]; intros ws le Hlen.
      - destruct ws; [reflexivity | discriminate].
      - destruct ws as [| w ws]; [discriminate |]. simpl. apply IH. simpl in Hlen. lia.
    Qed.

    (* [x = tinfo->args[i]] for the C variables [xs] *)
    Lemma runs_load_args m : forall xs i ws le,
        le ! tinfoId = Some (Vptr tb (Ptrofs.repr tofs)) -> ~ In tinfoId xs ->
        length ws = length xs ->
        (forall j w, nth_error ws j = Some w ->
                     Mem.load Mptr m tb (tofs + args_ofs + 8 * Z.of_nat (i + j)) = Some w) ->
        Z.of_nat i + Z.of_nat (length xs) <= max_args ->
        runs f e (load_args i xs) le m (set_temps xs ws le) m.
    Proof.
      induction xs as [| x xs IH]; intros i ws le Hle Hni Hlen Hl Hn.
      - apply runs_skip.
      - destruct ws as [| w ws]; [discriminate |]. cbn [load_args set_temps].
        simpl in Hlen, Hn, Hni. eapply runs_seq.
        + apply runs_set. eapply eval_load.
          * apply eval_arg. eauto.
          * reflexivity.
          * rewrite arg_address by lia. specialize (Hl 0%nat w eq_refl).
            rewrite Nat.add_0_r in Hl. exact Hl.
        + apply IH.
          * rewrite PTree.gso; auto.
          * tauto.
          * lia.
          * intros j w' Hj. specialize (Hl (S j) w' Hj).
            rewrite <- Hl. do 2 f_equal. lia.
          * lia.
    Qed.

  End Args.

  (** * Blocks *)

  Section Blocks.

    Context (nparam : nat) (fenv : M.t nat) (f : function) (e : env).

    Lemma field_address ofs i :
      0 <= i -> Ptrofs.unsigned ofs + 8 * i <= Ptrofs.max_unsigned ->
      Ptrofs.unsigned (Ptrofs.add ofs (Ptrofs.repr (8 * i))) = Ptrofs.unsigned ofs + 8 * i.
    Proof.
      intros. rewrite ptrofs_add_repr_r. apply Ptrofs.unsigned_repr.
      pose proof (Ptrofs.unsigned_range ofs). lia.
    Qed.

    (* Stores the variables [ys] in the words of the block [x], from word number [i] *)
    Lemma runs_store_fields le x b ofs : forall ys i ws m m',
        le ! x = Some (Vptr b ofs) ->
        Forall2 (var_val le fenv) ys ws -> Forall is_word ws ->
        (forall y, In y ys -> M.get y fenv <> None -> e ! y = None) ->
        Ptrofs.unsigned ofs + 8 * (Z.of_nat i + Z.of_nat (length ys)) <= Ptrofs.max_unsigned ->
        store_words m b (Ptrofs.unsigned ofs + 8 * Z.of_nat i) ws = Some m' ->
        runs f e (store_fields x i (map (var_expr nparam fenv) ys)) le m le m'.
    Proof.
      induction ys as [| y ys IH]; intros i ws m m' Hle Hv Hw He Hn Hst; inv Hv.
      - inv Hst. apply runs_skip.
      - simpl in Hst. destruct (Mem.store Mptr m b _ y0) as [m1 |] eqn:Hm1; [| discriminate].
        inv Hw. cbn [store_fields map]. simpl in Hn. eapply runs_seq.
        + eapply runs_assign.
          * apply eval_field; [apply eval_Etempvar; eauto | reflexivity].
          * apply eval_var_expr; eauto. intros. apply He; auto. now left.
          * reflexivity.
          * rewrite typeof_var_expr. reflexivity.
          * auto.
          * rewrite field_address by lia. eauto.
        + apply IH with (ws := l'); auto.
          * intros. apply He; auto. now right.
          * lia.
          * rewrite <- Hst. f_equal. lia.
    Qed.

    (* Takes [words + 1] words at [alloc] for the block [x] and writes its header *)
    Lemma runs_new_block le m x hdr words ab a m' :
      le ! allocId = Some (Vptr ab (Ptrofs.repr a)) -> x <> allocId ->
      0 <= a -> 0 <= words -> a + 8 * (words + 1) <= Ptrofs.max_unsigned ->
      Mem.store Mptr m ab a (Vlong (Int64.repr hdr)) = Some m' ->
      runs f e (new_block x hdr words) le m
           (PTree.set allocId (Vptr ab (Ptrofs.repr (a + 8 * (words + 1))))
                      (PTree.set x (Vptr ab (Ptrofs.repr (a + 8))) le)) m'.
    Proof.
      intros Hal Hx Ha Hw Hmax Hst. unfold new_block.
      assert (Hadd : forall le0 n, le0 ! allocId = Some (Vptr ab (Ptrofs.repr a)) ->
                eval_expr ge e le0 m (Ebinop Oadd alloc (const n tintnat) (tptr tvalue))
                          (Vptr ab (Ptrofs.repr (a + 8 * n)))).
      { intros le0 n Hle0.
        assert (Hc : classify_add (tptr tvalue) tintnat = add_case_pl tvalue) by reflexivity.
        eapply eval_Ebinop; [apply eval_Etempvar; eauto | apply eval_const |].
        rewrite const_eq. simpl. unfold sem_add. rewrite Hc. simpl.
        change (sizeof ge tvalue) with 8.
        rewrite ptrofs_of_int64_repr, ptrofs_mul_repr, ptrofs_add_repr. reflexivity. }
      eapply runs_seq; [| eapply runs_seq].
      - apply runs_set. eapply eval_Ecast; [apply Hadd; eauto |]. reflexivity.
      - apply runs_set. apply Hadd. rewrite PTree.gso; auto.
      - replace (a + 8 * 1) with (a + 8) by lia.
        eapply runs_assign.
        + apply eval_header; [| reflexivity]. apply eval_Etempvar.
          rewrite PTree.gso by auto. apply PTree.gss.
        + apply eval_const.
        + reflexivity.
        + reflexivity.
        + exact I.
        + rewrite ptrofs_add_repr. replace (a + 8 + 8 * -1) with a by lia.
          rewrite Ptrofs.unsigned_repr by lia. exact Hst.
    Qed.

  End Blocks.

  (** * Roots *)

  Section Roots.

    Context (f : function) (e : env) (rb : block) (nroots : Z).
    Hypothesis Hroots : e ! rootsId = Some (rb, tarray tvalue nroots).

    Lemma root_address i :
      8 * Z.of_nat i <= Ptrofs.max_unsigned ->
      Ptrofs.unsigned (Ptrofs.repr (8 * Z.of_nat i)) = 8 * Z.of_nat i.
    Proof. intros. apply Ptrofs.unsigned_repr. lia. Qed.

    (* [x = roots[i]] for the variables of [slots] that [keep] selects *)
    Lemma runs_read_roots m keep : forall slots i le,
        (forall j x, nth_error slots j = Some x -> keep x = true ->
                     exists w, Mem.load Mptr m rb (8 * Z.of_nat (i + j)) = Some w) ->
        8 * (Z.of_nat i + Z.of_nat (length slots)) <= Ptrofs.max_unsigned ->
        exists le',
          runs f e (read_roots nroots keep i slots) le m le' m /\
          (forall y, ~ (In y slots /\ keep y = true) -> le' ! y = le ! y) /\
          (NoDup slots ->
           forall j x, nth_error slots j = Some x -> keep x = true ->
                       exists w, Mem.load Mptr m rb (8 * Z.of_nat (i + j)) = Some w /\
                                 le' ! x = Some w).
    Proof.
      induction slots as [| x slots IH]; intros i le Hl Hn.
      - exists le. split; [apply runs_skip |]. split; auto.
        intros _ j x Hj. destruct j; discriminate.
      - simpl in Hn. cbn [read_roots].
        assert (Hl' : forall j y, nth_error slots j = Some y -> keep y = true ->
                                  exists w, Mem.load Mptr m rb (8 * Z.of_nat (S i + j)) = Some w).
        { intros j y Hj Hk. destruct (Hl (S j) y Hj Hk) as [w Hw]. exists w.
          rewrite <- Hw. do 2 f_equal. lia. }
        destruct (keep x) eqn:Hk.
        + destruct (Hl 0%nat x eq_refl Hk) as [w Hw]. rewrite Nat.add_0_r in Hw.
          destruct (IH (S i) (PTree.set x w le) Hl') as (le' & Hrun & Hother & Hset); [lia |].
          exists le'. split; [| split].
          * eapply runs_seq; [| exact Hrun]. apply runs_set.
            eapply eval_load; [eapply eval_root; eauto | reflexivity |].
            rewrite root_address by lia. exact Hw.
          * intros y Hy. rewrite Hother.
            -- apply PTree.gso. intros ->. apply Hy. split; [now left | auto].
            -- intros [Hin Hky]. apply Hy. split; [now right | auto].
          * intros Hnd j y Hj Hky. inv Hnd. destruct j as [| j]; simpl in Hj.
            -- inv Hj. exists w. rewrite Nat.add_0_r. split; auto.
               rewrite Hother; [apply PTree.gss | tauto].
            -- destruct (Hset H2 j y Hj Hky) as (w' & Hw' & Hle').
               exists w'. split; auto. rewrite <- Hw'. do 2 f_equal. lia.
        + destruct (IH (S i) le Hl') as (le' & Hrun & Hother & Hset); [lia |].
          exists le'. split; [| split].
          * eapply runs_seq; [apply runs_skip | exact Hrun].
          * intros y Hy. apply Hother. intros [Hin Hky]. apply Hy. split; [now right | auto].
          * intros Hnd j y Hj Hky. inv Hnd. destruct j as [| j]; simpl in Hj.
            -- inv Hj. congruence.
            -- destruct (Hset H2 j y Hj Hky) as (w' & Hw' & Hle').
               exists w'. split; auto. rewrite <- Hw'. do 2 f_equal. lia.
    Qed.

    (* Writes the variables [new] to [roots] from position [i], except those that are in
       place. The word [src x] of a stale variable is read from its root, which is after
       the positions that are written. *)
    Lemma runs_write_roots le st (src : var -> Values.val) K : forall new old i m,
        (i + length new = K)%nat ->
        8 * Z.of_nat K <= Ptrofs.max_unsigned ->
        Mem.range_perm m rb 0 (8 * Z.of_nat K) Cur Writable ->
        (forall p x, nth_error new p = Some x -> nth_error old p <> Some x ->
                     is_word (src x) /\
                     if in_list x (st_stale st)
                     then exists j, index_of x (st_slots st) = Some j /\ (K <= j)%nat /\
                                    8 * Z.of_nat j <= Ptrofs.max_unsigned /\
                                    Mem.load Mptr m rb (8 * Z.of_nat j) = Some (src x)
                     else le ! x = Some (src x)) ->
        exists m',
          runs f e (write_roots nroots st i old new) le m le m' /\
          Mem.unchanged_on (fun b o => ~ (b = rb /\ 8 * Z.of_nat i <= o < 8 * Z.of_nat K)) m m' /\
          (forall b, keeps_perm m m' b) /\
          (forall p x, nth_error new p = Some x -> nth_error old p <> Some x ->
                       Mem.load Mptr m' rb (8 * Z.of_nat (i + p)) = Some (src x)) /\
          (forall p x, nth_error new p = Some x -> nth_error old p = Some x ->
                       Mem.load Mptr m' rb (8 * Z.of_nat (i + p))
                       = Mem.load Mptr m rb (8 * Z.of_nat (i + p))).
    Proof.
      induction new as [| x new IH]; intros old i m HK Hmax Hperm Hsrc.
      - exists m. split; [apply runs_skip |]. split; [apply Mem.unchanged_on_refl |].
        split; [intros b o k p Hp; exact Hp |].
        split; intros p x Hp; destruct p; discriminate.
      - simpl in HK. subst K. cbn [write_roots].
        assert (Hvalid : Mem.valid_block m rb).
        { eapply Mem.perm_valid_block. apply (Hperm (8 * Z.of_nat i)). lia. }
        destruct (nth_error old 0) as [y |] eqn:Hy0;
          [destruct (Pos.eq_dec x y) as [-> | Hxy] |].
        + (* in place *)
          destruct old as [| y0 old]; [discriminate |]. simpl in Hy0.
          injection Hy0 as Hy0. subst y0.
          rewrite Pos.eqb_refl. simpl tl.
          destruct (IH old (S i) m) as (m' & Hrun & Hun & Hk & Hw & Hs).
          { lia. }
          { exact Hmax. }
          { exact Hperm. }
          { intros p x Hp Hne. apply (Hsrc (S p) x); auto. }
          exists m'. split; [eapply runs_seq; [apply runs_skip | exact Hrun] |].
          split; [| split; [exact Hk | split]].
          * eapply Mem.unchanged_on_implies; [exact Hun |]. intros b o Hn _ [Hb Ho]. apply Hn. lia.
          * intros p x Hp Hne. destruct p as [| p]; simpl in Hp, Hne; [congruence |].
            replace (i + S p)%nat with (S i + p)%nat by lia. auto.
          * intros p x Hp He. destruct p as [| p]; simpl in Hp, He.
            -- rewrite Nat.add_0_r. eapply Mem.load_unchanged_on_1; eauto.
               intros o Ho [_ Hr]. change (size_chunk Mptr) with 8 in Ho. lia.
            -- replace (i + S p)%nat with (S i + p)%nat by lia. exact (Hs p x Hp He).
        + (* another variable is at this position *)
          destruct old as [| y0 old]; [discriminate |]. simpl in Hy0.
          injection Hy0 as Hy0. subst y0.
          apply Pos.eqb_neq in Hxy. rewrite Hxy. simpl tl. apply Pos.eqb_neq in Hxy.
          destruct (Hsrc 0%nat x eq_refl) as [Hword Hx]; [simpl; congruence |].
          destruct (Mem.valid_access_store m Mptr rb (8 * Z.of_nat i) (src x)) as [m1 Hm1].
          { split; [| apply Z.divide_factor_l]. intros o Ho. apply Hperm.
            change (size_chunk Mptr) with 8 in Ho. lia. }
          destruct (IH old (S i) m1) as (m' & Hrun & Hun & Hk & Hw & Hs).
          { lia. }
          { exact Hmax. }
          { intros o Ho. eapply Mem.perm_store_1; eauto. }
          { intros p z Hp Hne. destruct (Hsrc (S p) z) as [Hwz Hz]; auto. split; auto.
            destruct (in_list z (st_stale st)); [| exact Hz].
            destruct Hz as (j & Hj & HKj & Hjm & Hl). exists j. repeat split; auto.
            rewrite <- Hl. eapply Mem.load_store_other; eauto.
            right. right. change (size_chunk Mptr) with 8. lia. }
          exists m'. split; [| split; [| split; [| split]]].
          * eapply runs_seq; [| exact Hrun].
            eapply runs_assign with (v := src x).
            -- eapply eval_root; eauto.
            -- unfold root_source. destruct (in_list x (st_stale st)).
               ++ destruct Hx as (j & Hj & HKj & Hjm & Hl). rewrite Hj.
                  eapply eval_load; [eapply eval_root; eauto | reflexivity |].
                  rewrite root_address by lia. exact Hl.
               ++ apply eval_Etempvar. exact Hx.
            -- reflexivity.
            -- unfold root_source. destruct (in_list x (st_stale st)); [| reflexivity].
               destruct (index_of x (st_slots st)); reflexivity.
            -- exact Hword.
            -- rewrite root_address by lia. exact Hm1.
          * eapply Mem.unchanged_on_trans.
            -- eapply Mem.store_unchanged_on; eauto.
               intros o Ho Hn. apply Hn. change (size_chunk Mptr) with 8 in Ho. split; auto. lia.
            -- eapply Mem.unchanged_on_implies; [exact Hun |].
               intros b o Hn _ [Hb Ho]. apply Hn. lia.
          * intros b o k p Hp. apply Hk. eapply Mem.perm_store_1; eauto.
          * intros p z Hp Hne. destruct p as [| p]; simpl in Hp, Hne.
            -- assert (Hzx : x = z) by congruence. subst z. rewrite Nat.add_0_r.
               eapply Mem.load_unchanged_on; [exact Hun | |].
               ++ intros o Ho [_ Hr]. change (size_chunk Mptr) with 8 in Ho. lia.
               ++ erewrite Mem.load_store_same; eauto. f_equal.
                  destruct (src x); try contradiction; reflexivity.
            -- replace (i + S p)%nat with (S i + p)%nat by lia. auto.
          * intros p z Hp He. destruct p as [| p]; simpl in Hp, He; [congruence |].
            replace (i + S p)%nat with (S i + p)%nat by lia. rewrite (Hs p z Hp He).
            eapply Mem.load_store_other; eauto.
            right. right. change (size_chunk Mptr) with 8. lia.
        + (* no variable is at this position *)
          destruct old as [| y0 old]; [| discriminate]. simpl tl.
          destruct (Hsrc 0%nat x eq_refl) as [Hword Hx]; [simpl; congruence |].
          destruct (Mem.valid_access_store m Mptr rb (8 * Z.of_nat i) (src x)) as [m1 Hm1].
          { split; [| apply Z.divide_factor_l]. intros o Ho. apply Hperm.
            change (size_chunk Mptr) with 8 in Ho. lia. }
          destruct (IH [] (S i) m1) as (m' & Hrun & Hun & Hk & Hw & Hs).
          { lia. }
          { exact Hmax. }
          { intros o Ho. eapply Mem.perm_store_1; eauto. }
          { intros p z Hp Hne. destruct (Hsrc (S p) z) as [Hwz Hz]; auto.
            { destruct p; simpl; congruence. }
            split; auto.
            destruct (in_list z (st_stale st)); [| exact Hz].
            destruct Hz as (j & Hj & HKj & Hjm & Hl). exists j. repeat split; auto.
            rewrite <- Hl. eapply Mem.load_store_other; eauto.
            right. right. change (size_chunk Mptr) with 8. lia. }
          exists m'. split; [| split; [| split; [| split]]].
          * eapply runs_seq; [| exact Hrun].
            eapply runs_assign with (v := src x).
            -- eapply eval_root; eauto.
            -- unfold root_source. destruct (in_list x (st_stale st)).
               ++ destruct Hx as (j & Hj & HKj & Hjm & Hl). rewrite Hj.
                  eapply eval_load; [eapply eval_root; eauto | reflexivity |].
                  rewrite root_address by lia. exact Hl.
               ++ apply eval_Etempvar. exact Hx.
            -- reflexivity.
            -- unfold root_source. destruct (in_list x (st_stale st)); [| reflexivity].
               destruct (index_of x (st_slots st)); reflexivity.
            -- exact Hword.
            -- rewrite root_address by lia. exact Hm1.
          * eapply Mem.unchanged_on_trans.
            -- eapply Mem.store_unchanged_on; eauto.
               intros o Ho Hn. apply Hn. change (size_chunk Mptr) with 8 in Ho. split; auto. lia.
            -- eapply Mem.unchanged_on_implies; [exact Hun |].
               intros b o Hn _ [Hb Ho]. apply Hn. lia.
          * intros b o k p Hp. apply Hk. eapply Mem.perm_store_1; eauto.
          * intros p z Hp Hne. destruct p as [| p]; simpl in Hp.
            -- assert (Hzx : x = z) by congruence. subst z. rewrite Nat.add_0_r.
               eapply Mem.load_unchanged_on; [exact Hun | |].
               ++ intros o Ho [_ Hr]. change (size_chunk Mptr) with 8 in Ho. lia.
               ++ erewrite Mem.load_store_same; eauto. f_equal.
                  destruct (src x); try contradiction; reflexivity.
            -- replace (i + S p)%nat with (S i + p)%nat by lia. apply Hw; auto.
               destruct p; simpl; congruence.
          * intros p z Hp He. destruct p; discriminate.
    Qed.

  End Roots.

  (** * Moves of variables *)

  Section Moves.

    Context (nparam : nat) (f : function) (e : env) (m : mem).

    Lemma var_val_fun fenv le x w1 w2 :
      var_val le fenv x w1 -> var_val le fenv x w2 -> w1 = w2.
    Proof.
      unfold var_val. destruct (M.get x fenv).
      - intros (b1 & H1 & ->) (b2 & H2 & ->). congruence.
      - congruence.
    Qed.

    (* A C variable that is not [x] keeps its word when [x] is set *)
    Lemma var_val_set fenv le x w y wy :
      y <> x -> var_val le fenv y wy -> var_val (PTree.set x w le) fenv y wy.
    Proof.
      unfold var_val. intros Hne. destruct (M.get y fenv); auto.
      intros H. rewrite PTree.gso; auto.
    Qed.

    Lemma vars_val_set fenv le x w ys ws :
      ~ In x ys -> Forall2 (var_val le fenv) ys ws ->
      Forall2 (var_val (PTree.set x w le) fenv) ys ws.
    Proof.
      intros Hx H. induction H as [| y wy ys ws Hy Hys IH]; constructor.
      - apply var_val_set; auto. intros ->. apply Hx. now left.
      - apply IH. intros Hin. apply Hx. now right.
    Qed.

    (* [p = y] for the moves [(p, y)] of [l]: no source is a target *)
    Lemma runs_moves fenv : forall (l : list (ident * var)) le,
        (forall mv, In mv l -> exists w, var_val le fenv (snd mv) w /\ is_word w) ->
        (forall mv, In mv l -> M.get (snd mv) fenv <> None -> e ! (snd mv) = None) ->
        NoDup (map fst l) ->
        (forall mv, In mv l -> ~ In (snd mv) (map fst l)) ->
        exists le',
          runs f e (fold_right (fun mv s => seq (Sset (fst mv) (var_expr nparam fenv (snd mv))) s)
                               Sskip l) le m le' m /\
          (forall mv w, In mv l -> var_val le fenv (snd mv) w -> le' ! (fst mv) = Some w) /\
          (forall x, ~ In x (map fst l) -> le' ! x = le ! x).
    Proof.
      induction l as [| [p y] l IH]; intros le Hw He Hnd Hsrc.
      - exists le. split; [apply runs_skip |]. split; [intros mv w [] | auto].
      - simpl in Hnd. inv Hnd.
        destruct (Hw (p, y) (or_introl eq_refl)) as (w & Hvw & Hword). simpl in Hvw.
        assert (Hy_ne : forall mv, In mv ((p, y) :: l) -> snd mv <> p).
        { intros mv Hin Heq. apply (Hsrc mv Hin). rewrite Heq. now left. }
        destruct (IH (PTree.set p w le)) as (le' & Hrun & Hset & Hother); auto.
        { intros mv Hin. destruct (Hw mv (or_intror Hin)) as (w' & Hv' & Hw').
          exists w'. split; auto. apply var_val_set; auto. apply Hy_ne. now right. }
        { intros mv Hin. apply He. now right. }
        { intros mv Hin Hin'. apply (Hsrc mv (or_intror Hin)). now right. }
        exists le'. split; [| split].
        + cbn [fold_right fst snd]. eapply runs_seq; [| exact Hrun].
          apply runs_set. apply eval_var_expr; auto. intros Hf. apply (He (p, y)); auto. now left.
        + intros mv w' [Heq | Hin] Hv'.
          * subst mv. simpl in *. rewrite Hother by auto. rewrite PTree.gss.
            f_equal. eapply var_val_fun; eauto.
          * apply Hset; auto. apply var_val_set; auto. apply Hy_ne. now right.
        + intros x Hx. simpl in Hx. rewrite Hother by tauto. apply PTree.gso.
          intros ->. apply Hx. now left.
    Qed.

    Lemma fold_right_map {A B} (g : A -> B) (F : B -> statement -> statement)
          (F' : A -> statement -> statement) (l : list A) :
      (forall a s, F' a s = F (g a) s) ->
      fold_right F' Sskip l = fold_right F Sskip (map g l).
    Proof. intros H. induction l; simpl; [auto | rewrite H; congruence]. Qed.

    Lemma combine_In_r {A B} : forall (l1 : list A) (l2 : list B) b,
        (length l2 <= length l1)%nat -> In b l2 -> exists a, In (a, b) (combine l1 l2).
    Proof.
      induction l1 as [| a l1 IH]; intros l2 b Hlen Hin.
      - destruct l2; [contradiction | simpl in Hlen; lia].
      - destruct l2 as [| b0 l2]; [contradiction |]. simpl in *.
        destruct Hin as [-> | Hin]; [eauto |].
        destruct (IH l2 b) as [a' Ha']; [lia | auto |]. eauto.
    Qed.

    Lemma combine_fst_incl {A B} : forall (l1 : list A) (l2 : list B) x,
        In x (map fst (combine l1 l2)) -> In x l1.
    Proof.
      intros l1 l2 x H. apply in_map_iff in H. destruct H as ([a b] & <- & Hin).
      eapply in_combine_l; eauto.
    Qed.

    Lemma combine_fst_NoDup {A B} : forall (l1 : list A) (l2 : list B),
        NoDup l1 -> NoDup (map fst (combine l1 l2)).
    Proof.
      induction l1 as [| a l1 IH]; intros l2 Hnd; [constructor |].
      destruct l2 as [| b l2]; [constructor |]. inv Hnd. simpl. constructor; auto.
      intros Hin. apply combine_fst_incl in Hin. contradiction.
    Qed.

    (* The parameters [ps] take the words of [ys] *)
    Lemma runs_assign_params fenv tmps ps ys le :
      NoDup ps -> NoDup tmps -> length ps = length ys -> (length ps <= length tmps)%nat ->
      (forall y, In y ys -> exists w, var_val le fenv y w /\ is_word w) ->
      (forall y, In y ys -> M.get y fenv <> None -> e ! y = None) ->
      (forall p, In p ps -> M.get p fenv = None) ->
      (forall t, In t tmps -> ~ In t ps /\ ~ In t ys) ->
      exists le',
        runs f e (assign_params nparam fenv tmps ps ys) le m le' m /\
        (forall j p y w, nth_error ps j = Some p -> nth_error ys j = Some y ->
                         var_val le fenv y w -> le' ! p = Some w) /\
        (forall x, ~ In x ps -> ~ In x tmps -> le' ! x = le ! x).
    Proof.
      intros Hps Htmps Hlen Hlt Hw He Hpf Ht. unfold assign_params. cbv zeta.
      match goal with
      | [ |- context [List.filter ?F (combine ps ys)] ] =>
        set (moves := List.filter F (combine ps ys))
      end.
      assert (Hmv_in : forall mv, In mv moves -> In mv (combine ps ys) /\ fst mv <> snd mv).
      { intros mv Hin. apply filter_In in Hin. destruct Hin as [Hin Hne]. split; auto.
        apply negb_true_iff, Pos.eqb_neq in Hne. auto. }
      assert (Hmv_ps : forall mv, In mv moves -> In (fst mv) ps /\ In (snd mv) ys).
      { intros [p y] Hin. destruct (Hmv_in _ Hin) as [Hc _]. simpl.
        split; [eapply in_combine_l | eapply in_combine_r]; eauto. }
      assert (Hmv_nd : NoDup (map fst moves)).
      { unfold moves. clear - Hps. revert ys. induction ps as [| p ps IH]; intros ys; [constructor |].
        inv Hps. destruct ys as [| y ys]; [constructor |]. simpl.
        destruct (negb (Pos.eqb p y)); simpl; auto. constructor; auto.
        intros Hin. apply in_map_iff in Hin. destruct Hin as ([p' y'] & Heq & Hin). simpl in Heq.
        subst p'. apply filter_In in Hin. destruct Hin as [Hin _].
        apply in_combine_l in Hin. contradiction. }
      (* the word of a parameter after the moves *)
      assert (Hfinal : forall le',
                 (forall mv w, In mv moves -> var_val le fenv (snd mv) w ->
                               le' ! (fst mv) = Some w) ->
                 (forall x, ~ In x (map fst moves) -> ~ In x tmps -> le' ! x = le ! x) ->
                 forall j p y w, nth_error ps j = Some p -> nth_error ys j = Some y ->
                                 var_val le fenv y w -> le' ! p = Some w).
      { intros le' Hset Hother j p y w Hp Hy Hv.
        assert (Hin : In (p, y) (combine ps ys)).
        { clear - Hp Hy. revert ys j Hp Hy. induction ps as [| p0 ps IH]; intros ys j Hp Hy.
          - destruct j; discriminate.
          - destruct ys as [| y0 ys]; [destruct j; discriminate |].
            destruct j; simpl in *; [left; congruence | right; eauto]. }
        destruct (Pos.eq_dec p y) as [-> | Hne].
        - rewrite Hother.
          + unfold var_val in Hv. rewrite (Hpf y) in Hv; auto. eapply nth_error_In; eauto.
          + intros Hin'. apply in_map_iff in Hin'. destruct Hin' as ([p' y'] & Heq & Hin').
            simpl in Heq. subst p'. destruct (Hmv_in _ Hin') as [Hc Hne]. simpl in Hne.
            clear - Hps Hc Hin Hne. revert ys Hc Hin. induction ps as [| p0 ps IH]; intros ys Hc Hin.
            * contradiction.
            * destruct ys as [| y0 ys]; [contradiction |]. inv Hps. simpl in *.
              destruct Hc as [Hc | Hc]; destruct Hin as [Hin | Hin].
              -- congruence.
              -- inv Hc. apply in_combine_l in Hin. contradiction.
              -- inv Hin. apply in_combine_l in Hc. contradiction.
              -- eauto.
          + intros Hin'. destruct (Ht y Hin') as [Hnp _]. apply Hnp. eapply nth_error_In; eauto.
        - apply (Hset (p, y)); auto. apply filter_In. split; auto.
          apply negb_true_iff, Pos.eqb_neq. auto. }
      match goal with
      | [ |- context [if ?c then _ else _] ] => destruct c eqn:Hex
      end.
      - (* through the spare variables *)
        set (tm := combine tmps moves).
        assert (Htm_len : (length moves <= length tmps)%nat).
        { unfold moves. etransitivity; [apply filter_length_le |].
          rewrite length_combine. lia. }
        rewrite (fold_right_map (fun mv : ident * (ident * var) => (fst mv, snd (snd mv)))
                   (fun mv s => seq (Sset (fst mv) (var_expr nparam fenv (snd mv))) s) _ tm)
          by reflexivity.
        rewrite (fold_right_map (fun mv : ident * (ident * var) => (fst (snd mv), fst mv))
                   (fun mv s => seq (Sset (fst mv) (var_expr nparam (M.empty nat) (snd mv))) s)
                   _ tm) by reflexivity.
        assert (Htm_t : forall t mv, In (t, mv) tm -> In t tmps /\ In mv moves).
        { intros t mv Hin. split; [eapply in_combine_l | eapply in_combine_r]; eauto. }
        destruct (runs_moves fenv (map (fun mv : ident * (ident * var) => (fst mv, snd (snd mv))) tm) le)
          as (le1 & Hrun1 & Hset1 & Hother1).
        { intros mv Hin. apply in_map_iff in Hin. destruct Hin as ([t [p y]] & <- & Hin). simpl.
          apply Hw. apply (Hmv_ps (p, y)). eapply Htm_t; eauto. }
        { intros mv Hin. apply in_map_iff in Hin. destruct Hin as ([t [p y]] & <- & Hin). simpl.
          apply He. apply (Hmv_ps (p, y)). eapply Htm_t; eauto. }
        { rewrite map_map. simpl. apply combine_fst_NoDup. auto. }
        { intros mv Hin Hin'. apply in_map_iff in Hin. destruct Hin as ([t [p y]] & <- & Hin).
          simpl in Hin'. rewrite map_map in Hin'. simpl in Hin'.
          apply combine_fst_incl in Hin'. destruct (Ht _ Hin') as [_ Hny]. apply Hny.
          apply (Hmv_ps (p, y)). eapply Htm_t; eauto. }
        destruct (runs_moves (M.empty nat)
                             (map (fun mv : ident * (ident * var) => (fst (snd mv), fst mv)) tm) le1)
          as (le2 & Hrun2 & Hset2 & Hother2).
        { intros mv Hin. apply in_map_iff in Hin. destruct Hin as ([t [p y]] & <- & Hin). simpl.
          destruct (Hw y) as (w & Hv & Hword). { apply (Hmv_ps (p, y)). eapply Htm_t; eauto. }
          exists w. split; auto. unfold var_val. rewrite M.gempty.
          apply (Hset1 (t, y)); auto. apply in_map_iff. exists (t, (p, y)). auto. }
        { intros mv _ Hc. rewrite M.gempty in Hc. congruence. }
        { rewrite map_map. simpl.
          assert (Heq : map (fun x : ident * (ident * var) => fst (snd x)) tm
                        = map fst (map snd tm)) by (rewrite map_map; reflexivity).
          rewrite Heq. unfold tm.
          assert (Hsnd : map snd (combine tmps moves) = moves).
          { clear - Htm_len. revert tmps Htm_len. induction moves as [| mv l IH]; intros tmps Hl.
            - destruct tmps; reflexivity.
            - destruct tmps as [| t tmps]; [simpl in Hl; lia |]. simpl. f_equal. apply IH.
              simpl in Hl. lia. }
          rewrite Hsnd. exact Hmv_nd. }
        { intros mv Hin Hin'. apply in_map_iff in Hin. destruct Hin as ([t [p y]] & <- & Hin).
          simpl in Hin'. rewrite map_map in Hin'. simpl in Hin'.
          apply in_map_iff in Hin'. destruct Hin' as ([t' [p' y']] & Heq & Hin'). simpl in Heq.
          destruct (Htm_t _ _ Hin) as [Htt _]. destruct (Ht _ Htt) as [Hnp _]. apply Hnp.
          subst t. apply (Hmv_ps (p', y')). eapply Htm_t; eauto. }
        exists le2. split; [| split].
        + eapply runs_seq; eauto.
        + apply Hfinal.
          * intros [p y] w Hin Hv. simpl in *.
            destruct (combine_In_r tmps moves (p, y) Htm_len Hin) as [t Hint].
            apply (Hset2 (p, t)).
            -- apply in_map_iff. exists (t, (p, y)). auto.
            -- unfold var_val. rewrite M.gempty. simpl.
               apply (Hset1 (t, y)); auto. apply in_map_iff. exists (t, (p, y)). auto.
          * intros x Hx Hxt. rewrite Hother2, Hother1; auto.
            -- rewrite map_map. simpl. intros Hin. apply combine_fst_incl in Hin. contradiction.
            -- rewrite map_map. simpl. intros Hin. apply Hx.
               apply in_map_iff in Hin. destruct Hin as ([t [p y]] & <- & Hin). simpl.
               apply in_map_iff. exists (p, y). split; auto. eapply Htm_t; eauto.
        + intros x Hxp Hxt. rewrite Hother2, Hother1; auto.
          * rewrite map_map. simpl. intros Hin. apply combine_fst_incl in Hin. contradiction.
          * rewrite map_map. simpl. intros Hin.
            apply in_map_iff in Hin. destruct Hin as ([t [p y]] & <- & Hin). simpl in Hxp.
            apply Hxp. apply (Hmv_ps (p, y)). eapply Htm_t; eauto.
      - (* directly *)
        destruct (runs_moves fenv moves le) as (le1 & Hrun1 & Hset1 & Hother1).
        { intros mv Hin. apply Hw. apply (Hmv_ps mv Hin). }
        { intros mv Hin. apply He. apply (Hmv_ps mv Hin). }
        { exact Hmv_nd. }
        { intros mv Hin Hin'.
          match type of Hex with
          | ?c = false => assert (Hf : c = true)
          end.
          { apply existsb_exists. exists mv. split; auto. apply in_list_In. auto. }
          congruence. }
        exists le1. split; [exact Hrun1 |]. split.
        + apply Hfinal; auto.
        + intros x Hxp Hxt. apply Hother1. intros Hin. apply Hxp.
          apply in_map_iff in Hin. destruct Hin as (mv & <- & Hin). apply (Hmv_ps mv Hin).
    Qed.

  End Moves.

End Clight.
