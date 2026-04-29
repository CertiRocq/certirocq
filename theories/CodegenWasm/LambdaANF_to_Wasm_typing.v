Set Printing Compact Contexts.

(* This file contains the proof that the generated function bodies are well-typed
*)

From compcert Require Import
  Coqlib.

From CertiRocq Require Import
  LambdaANF.term LambdaANF.term_util
  CodegenWasm.LambdaANF_to_Wasm
  CodegenWasm.LambdaANF_to_Wasm_correct
  CodegenWasm.LambdaANF_to_Wasm_primitives
  CodegenWasm.LambdaANF_to_Wasm_restrictions.

From Wasm Require Import
  datatypes operations host
  type_preservation opsem properties common.

From Stdlib Require Import List.

Import LambdaANF.toplevel.
Import ListNotations.
Import seq ssreflect.

Section FUNCTION_BODY_TYPING.

Variable cenv   : ctor_env.
Variable funenv : fun_env.
Variable fenv   : fname_env.
Variable nenv   : name_env.
Variable penv   : prim_env.
Let repr_expr_LambdaANF_Wasm := @repr_expr_LambdaANF_Wasm cenv fenv nenv penv.

Ltac separate_instr :=
  cbn;
  repeat match goal with
  |- context C [?x :: ?l] =>
     lazymatch l with [::] => fail | _ => rewrite -(cat1s x l) end
  end.

(* for main function, translated fns *)
Definition context_restr (lenv: localvar_env) (c: t_context) :=
  (* locals in bound, i32 *)
  (forall x x', @repr_var nenv lenv x x' -> lookup_N (tc_locals c) x' = Some (T_num T_i32)) /\
  (* globals i32, mut *)
  (forall var, In var [glob_mem_ptr; glob_cap; glob_result; glob_out_of_mem] ->
    lookup_N (tc_globals c) var = Some {| tg_mut:= MUT_var; tg_t:= T_num T_i32|}) /\
  (* globals i64, mut *)
  (forall var, In var [glob_tmp1; glob_tmp2; glob_tmp3; glob_tmp4] ->
    lookup_N (tc_globals c) var = Some {| tg_mut:= MUT_var; tg_t:= T_num T_i64|}) /\
  (* no return value *)
  (tc_return c = Some []) /\
  (* mem exists *)
  (tc_mems c <> []) /\ (* TODO consider better automation for mem, table *)
  (* table *)
  (exists t, lookup_N (tc_tables c) 0%N = Some t /\ tt_elem_type t = T_funcref) /\
  (* function types *)
  (Z.of_nat (length (tc_types c)) > max_function_args)%Z /\
  (forall i, (Z.of_nat i <= max_function_args)%Z -> lookup_N (tc_types c) (N.of_nat i) = Some (Tf (repeat (T_num T_i32) i) [::])).

Lemma update_label_preserves_context_restr lenv c :
  context_restr lenv c ->
  context_restr lenv (upd_label c ([:: [::]] ++ tc_labels c)%list).
Proof. auto. Qed.

(* Prove that a list of basic instructions is well-typed, context_restr is required to hold *)
Ltac solve_bet Hcontext :=
  let Hglob := fresh "Hglob" in
  simpl; try rewrite List.app_nil_r;
  match goal with
  | |- be_typing _ [::] (Tf [::] _) => by apply bet_empty
  | |- be_typing _ [:: BI_return] _ => apply bet_return with (t1s:=[::]); by apply Hcontext
  | |- be_typing _ [:: BI_unreachable] _ => by apply bet_unreachable
  (* globals *)
  | |- be_typing ?context [:: BI_global_get ?var] _ =>
         assert (lookup_N (tc_globals context) var = Some {| tg_mut:= MUT_var; tg_t := T_num T_i32 |}) as Hglob by
          (apply Hcontext; now cbn); eapply bet_global_get with (t:=T_num T_i32); [eassumption | now cbn]
  | |- be_typing ?context [:: BI_global_set ?var] _ =>
         assert (lookup_N (tc_globals context) var = Some {| tg_mut:= MUT_var; tg_t := T_num T_i32 |}) as Hglob by
          (apply Hcontext; now cbn); eapply bet_global_set with (t:=T_num T_i32); [eassumption | now cbn | now cbn]
  | |- be_typing ?context [:: BI_global_get ?var] (Tf ?tin _) =>
         assert (lookup_N (tc_globals context) var = Some {| tg_mut:= MUT_var; tg_t := T_num T_i64 |}) as Hglob by
        (apply Hcontext; now cbn);
         (match tin with
          | [:: ] => idtac
          | [:: T_num T_i64 ] => apply bet_weakening with (ts:=[::T_num T_i64])
          | [:: T_num T_i64; T_num T_i64 ] => apply bet_weakening with (ts:=[::T_num T_i64 ; T_num T_i64])
          | [:: T_num T_i64; T_num T_i64; T_num T_i64 ] => apply bet_weakening with (ts:=[::T_num T_i64 ; T_num T_i64; T_num T_i64])
          | [:: T_num T_i64; T_num T_i64; T_num T_i64; T_num T_i64 ] => apply bet_weakening with (ts:=[::T_num T_i64 ; T_num T_i64; T_num T_i64; T_num T_i64])
          end);
         eapply bet_global_get with (t:=T_num T_i64); [eassumption | now cbn]
  | |- be_typing ?context [:: BI_global_set ?var] (Tf ?tin _) =>
         assert (lookup_N (tc_globals context) var = Some {| tg_mut:= MUT_var; tg_t := T_num T_i64 |}) as Hglob by
        (apply Hcontext; now cbn);
         (match tin with
          | [:: T_num T_i64 ] => idtac
          | [:: T_num T_i64; T_num T_i64 ] => apply bet_weakening with (ts:=[::T_num T_i64])
          | [:: T_num T_i64; T_num T_i64; T_num T_i64 ] => apply bet_weakening with (ts:=[::T_num T_i64 ; T_num T_i64])
          | [:: T_num T_i64; T_num T_i64; T_num T_i64; T_num T_i64 ] => apply bet_weakening with (ts:=[::T_num T_i64 ; T_num T_i64; T_num T_i64])
          end);
         eapply bet_global_set with (t:=T_num T_i64); [eassumption | now cbn | now cbn]
  (* locals with mapping *)
  | H: repr_var _ _ ?x' |- be_typing _ [:: BI_local_get ?x'] (Tf [::] _) => apply bet_local_get; eapply Hcontext; eassumption
  | H: repr_var _ _ ?x' |- be_typing _ [:: BI_local_set ?x'] (Tf [::_] _) => apply bet_local_set; eapply Hcontext; eassumption
  (* locals without mapping (e.g. grow_mem) *)
  | |- be_typing ?context [:: BI_local_set 0%N] _ => apply bet_local_set; eassumption
  | |- be_typing ?context [:: BI_local_get 0%N] _ => apply bet_local_get; eassumption
  (* arithmetic *)
  | |- be_typing _ [:: BI_const_num _] (Tf [::] _) => apply bet_const_num
  | |- be_typing _ [:: BI_testop T_i32 _] (Tf [:: T_num T_i32] _) => apply bet_testop; by simpl
  | |- be_typing _ [:: BI_testop T_i64 _] (Tf ([:: T_num T_i32; T_num T_i64]) _) => apply bet_weakening with (ts:=[::T_num T_i32]); apply bet_testop; by simpl
  | |- be_typing _ [:: BI_testop T_i64 _] (Tf ([:: T_num T_i64]) _) => apply bet_testop; by simpl
  | |- be_typing _ [:: BI_unop T_i64 _] (Tf [:: T_num T_i32; T_num T_i64] _) => apply bet_weakening with (ts:=[::T_num T_i32]); by apply bet_unop
  | |- be_typing _ [:: BI_unop T_i64 _] (Tf [:: T_num T_i64] _) => by apply bet_unop
  | |- be_typing _ [:: BI_binop T_i32 _] (Tf [:: T_num T_i32; T_num T_i32] _) => by apply bet_binop
  | |- be_typing _ [:: BI_binop T_i64 _] (Tf ?tin _) =>
         (match tin with
          | [:: T_num T_i64; T_num T_i64 ] => idtac
          | [:: T_num T_i64; T_num T_i64; T_num T_i64 ] => apply bet_weakening with (ts:=[::T_num T_i64])
          | [:: T_num T_i64; T_num T_i64; T_num T_i64; T_num T_i64 ] => apply bet_weakening with (ts:=[::T_num T_i64 ; T_num T_i64])
          | [:: T_num T_i64; T_num T_i64; T_num T_i64; T_num T_i64; T_num T_i64 ] => apply bet_weakening with (ts:=[::T_num T_i64 ; T_num T_i64; T_num T_i64])
          end);
         by apply bet_binop
  | |- be_typing _ [:: BI_binop T_i64 _] (Tf [:: T_num T_i64; T_num T_i64; T_num T_i64] _) => apply bet_weakening with (ts:=[::T_num T_i64]); by apply bet_binop
  | |- be_typing _ [:: BI_relop T_i32 _] (Tf [:: T_num T_i32; T_num T_i32] _) => by apply bet_relop
  | |- be_typing _ [:: BI_relop T_i64 _] (Tf [:: T_num T_i64; T_num T_i64] _) => by apply bet_relop
(* memory *)
  | H: lookup_N (tc_mems _) 0 = Some _ |- be_typing _ [:: BI_memory_size] (Tf [::] _) => eapply bet_memory_size; apply H
  | H: lookup_N (tc_mems _) 0 = Some _ |- be_typing _ [:: BI_memory_grow] (Tf [:: T_num T_i32] _) => eapply bet_memory_grow; apply H
  | |- be_typing _ [:: BI_store _ None _] (Tf [:: T_num _; T_num _] _) => by eapply bet_store; first eassumption; cbn=>//
  | |- be_typing _ [:: BI_load _ None _] (Tf [:: T_num _] _) => by eapply bet_load; first eassumption; cbn=>//
  (* simple if statement *)
  | |- be_typing _ [:: BI_if (BT_valtype None) _ _] _ =>
         apply bet_if_wasm with (tn:=[])=>//; separate_instr; repeat rewrite catA; repeat eapply bet_composition'; try solve_bet Hcontext
  | |- be_typing _ [:: BI_if (BT_valtype (Some (T_num T_i32))) [:: BI_const_num (nat_to_value _)] [:: BI_const_num (nat_to_value _)]] _ =>
         apply bet_if_wasm with (tn:=[])=>//; try solve_bet Hcontext
  | H: context_restr ?lenv ?context |- be_typing _ [:: BI_if (BT_valtype (Some (T_num T_i32))) _ _] (Tf [:: T_num T_i32] _) =>
      let Hcontext' := fresh "Hcontext" in
      (assert (Hcontext': context_restr lenv (upd_label context ([:: [:: T_num T_i32]] ++ tc_labels context))) by now inv Hcontext);
         apply bet_if_wasm with (tn:=[])=>//; separate_instr; repeat rewrite catA; repeat eapply bet_composition'; try solve_bet Hcontext'
  | H: context_restr ?lenv ?context |- be_typing _ [:: BI_if (BT_valtype (Some (T_num T_i64))) _ _] (Tf ?tin _) =>
      let Hcontext' := fresh "Hcontext" in
      (match tin with
       | [:: T_num T_i32] => idtac
       | [:: T_num T_i32; T_num T_i32 ] => apply bet_weakening with (ts:=[::T_num T_i32])
       end);
      (assert (Hcontext': context_restr lenv (upd_label context ([:: [:: T_num T_i64]] ++ tc_labels context))) by now inv Hcontext);
         apply bet_if_wasm with (tn:=[])=>//; separate_instr; repeat rewrite catA; repeat eapply bet_composition'; try solve_bet Hcontext'
  (* if above failed, try to frame the leading const *)
  | |- be_typing _ _ (Tf [:: T_num T_i64; T_num T_i64; T_num T_i64; T_num T_i64] _) => apply bet_weakening with (ts:=[::T_num T_i64; T_num T_i64; T_num T_i64; T_num T_i64]); by solve_bet Hcontext
  | |- be_typing _ _ (Tf [:: T_num T_i64; T_num T_i64; T_num T_i64] _) => apply bet_weakening with (ts:=[::T_num T_i64; T_num T_i64; T_num T_i64]); by solve_bet Hcontext
  | |- be_typing _ _ (Tf [:: T_num T_i64; T_num T_i64; T_num T_i64; T_num T_i32] _) => apply bet_weakening with (ts:=[::T_num T_i64; T_num T_i64; T_num T_i64]); by solve_bet Hcontext
  | |- be_typing _ _ (Tf [:: T_num T_i32] _) => apply bet_weakening with (ts:=[::T_num T_i32]); by solve_bet Hcontext
  | |- be_typing _ _ (Tf [:: T_num T_i64] _) => apply bet_weakening with (ts:=[::T_num T_i64]); by solve_bet Hcontext
  | |- be_typing _ _ (Tf [:: T_num T_i32; T_num T_i32] _) => apply bet_weakening with (ts:=[::T_num T_i32]); by solve_bet Hcontext
  | |- be_typing _ _ (Tf [:: T_num T_i64; T_num T_i32] _) => apply bet_weakening with (ts:=[::T_num T_i64]); by solve_bet Hcontext
  | |- be_typing _ _ (Tf [:: T_num T_i32; T_num T_i32; T_num T_i32] _) =>
         apply bet_weakening with (ts:=[::T_num T_i32; T_num T_i32]); by solve_bet Hcontext
  | |- be_typing _ _ (Tf [:: T_num T_i32; T_num T_i64] _) => apply bet_weakening with (ts:=[::T_num T_i32; T_num T_i64]); by solve_bet Hcontext
  | |- be_typing _ _ (Tf [:: T_num T_i32; T_num T_i64; T_num T_i64] _) => apply bet_weakening with (ts:=[::T_num T_i32]); by solve_bet Hcontext
  | |- be_typing _ _ (Tf [:: T_num T_i32; T_num T_i64; T_num T_i32] _) => apply bet_weakening with (ts:=[::T_num T_i32; T_num T_i64]); by solve_bet Hcontext
  | |- be_typing _ [:: BI_binop T_i32 _] (Tf [:: T_num T_i32; T_num T_i32; T_num T_i32] _) =>
         apply bet_weakening with (ts:=[::T_num T_i32]); by apply bet_binop
  | |- be_typing _ _ (Tf [:: T_num T_i64; T_num T_i64] _) => apply bet_weakening with (ts:=[::T_num T_i64]); by solve_bet Hcontext
  end.

Ltac prepare_solve_bet :=
  separate_instr; repeat rewrite catA; repeat eapply bet_composition'.

(* Translated expressions (all functions bodies other than the first few) have type (Tf [::] [::]) *)

Lemma grow_memory_if_necessary_typing {lenv} : forall c,
  context_restr lenv c ->
  be_typing c grow_memory_if_necessary (Tf [::] [::]).
Proof.
  intros c Hcontext. unfold grow_memory_if_necessary.
  assert (exists m, lookup_N (tc_mems c) 0 = Some m) as [m Hm]. {
    destruct (tc_mems c) eqn:Hc; cbn; eauto. exfalso. by apply Hcontext. }
  prepare_solve_bet; solve_bet Hcontext.
Qed.

Lemma call_grow_mem_if_necessary_typing {lenv} : forall c mem bytes mem' instrs,
  context_restr lenv c ->
  repr_call_grow_mem_if_necessary mem bytes mem' instrs ->
  be_typing c instrs (Tf [::] [::]).
Proof.
  intros. inv H0.
  - by solve_bet Hcontext.
  - by apply (@grow_memory_if_necessary_typing lenv).
Qed.

Lemma constr_args_store_typing {lenv} : forall args n instr c,
  @context_restr lenv c ->
  Forall_statements_in_seq' (@store_nth_constr_arg fenv nenv lenv) args instr n ->
  be_typing c instr (Tf [::] [::]).
Proof.
  induction args; intros ??? Hcontext Hargs.
  - inv Hargs. apply bet_empty.
  - inv Hargs. inv H5.
    assert (exists m, lookup_N (tc_mems c) 0 = Some m) as [m Hm]. {
        destruct (tc_mems c) eqn:Hc; cbn; eauto. by apply Hcontext in Hc. }
    inv H.
    + (* local var *)
      apply update_label_preserves_context_restr in Hcontext.
      prepare_solve_bet. all: try solve_bet Hcontext.
      by eapply IHargs; eauto.
    + (* fn idx *)
      apply update_label_preserves_context_restr in Hcontext.
      prepare_solve_bet. all: try solve_bet Hcontext.
      by eapply IHargs; eauto.
Qed.

Lemma fun_args_typing {lenv} : forall l args' c,
  @context_restr lenv c ->
  @repr_fun_args_Wasm fenv nenv lenv l args' ->
  be_typing c args' (Tf [::] (repeat (T_num T_i32) (length l))).
Proof.
  induction l; intros ?? Hcontext Hargs =>/=.
  - inv Hargs. apply bet_empty.
  - inv Hargs.
    + (* var *)
      prepare_solve_bet. solve_bet Hcontext.
      apply bet_weakening with (ts:=[::T_num T_i32]). by apply IHl.
    + (* fun idx *)
      prepare_solve_bet. solve_bet Hcontext.
      apply bet_weakening with (ts:=[::T_num T_i32]). by apply IHl.
Qed.

Lemma increment_glob_mem_ptr_typing {lenv} : forall c n,
  context_restr lenv c ->
  be_typing c (increment_glob_mem_ptr glob_mem_ptr n) (Tf [:: T_num T_i32] [:: T_num T_i32]).
Proof.
  intros c n Hc.
  unfold increment_glob_mem_ptr.
  prepare_solve_bet; solve_bet Hc.
Qed.

Lemma apply_binop_and_store_i64_typing {lenv} : forall c m x x' y y' bop mask,
  context_restr lenv c ->
  @repr_var nenv lenv x x' ->
  @repr_var nenv lenv y y' ->
  lookup_N (tc_mems c) 0 = Some m ->
  be_typing c (apply_binop_and_store_i64 glob_mem_ptr bop x' y' mask) (Tf [::] [:: T_num T_i32]).
Proof.
  intros c m x x' y y' bop mask Hc Hx Hy Hm.
  unfold apply_binop_and_store_i64.
  destruct mask; prepare_solve_bet; try by solve_bet Hc.
  all: now eapply increment_glob_mem_ptr_typing.
Qed.

Lemma prim_op_typing {lenv} : forall c ys op instrs,
  @context_restr lenv c ->
  @repr_primitive_operation nenv lenv op ys instrs ->
  be_typing c instrs (Tf [::] [:: T_num T_i32]).
Proof.
  intros c ys op instrs Hcontext Hinstrs.
  assert (exists m, lookup_N (tc_mems c) 0 = Some m) as [m Hmem]. {
    destruct Hcontext as (_ & _ & _ & _ & Hmems &_), (tc_mems c); now eexists. }
  assert (Hcontext': context_restr lenv (upd_label c ([:: [:: T_num T_i32]] ++ tc_labels c)))
      by now inv Hcontext.
  assert (Hmem' : lookup_N (tc_mems (upd_label c ([:: [:: T_num T_i32]] ++ tc_labels c))) 0 = Some m)
      by now unfold tc_mems.
  (* Assert some helpers for instruction sequences that are repeated many times *)

  assert (Hin1: In glob_tmp1 [:: glob_tmp1; glob_tmp2; glob_tmp3; glob_tmp4]) by (cbn; auto).
  assert (Hin2: In glob_tmp2 [:: glob_tmp1; glob_tmp2; glob_tmp3; glob_tmp4]) by (cbn; auto).
  assert (Hin3: In glob_tmp3 [:: glob_tmp1; glob_tmp2; glob_tmp3; glob_tmp4]) by (cbn; auto).
  assert (Hin4: In glob_tmp4 [:: glob_tmp1; glob_tmp2; glob_tmp3; glob_tmp4]) by (cbn; auto).
  inv Hinstrs.
  { (* Unary operations *)
    inv H0; unfold head0_instrs, tail0_instrs; prepare_solve_bet; solve_bet Hcontext || eapply increment_glob_mem_ptr_typing; eauto. }
  { (* Binary operations *)
    inversion H1; unfold div_instrs, mod_instrs, shift_instrs, make_boolean_valued_comparison,
      compare_instrs, mulc_instrs, diveucl_instrs, apply_add_carry_operation, apply_sub_carry_operation, bitmask_instrs, load_local_i64;
      prepare_solve_bet.
   all: try solve_bet Hcontext'. (* takes a while, 20 left *)
   all: try by (eapply increment_glob_mem_ptr_typing; eauto).
   all: eapply apply_binop_and_store_i64_typing; eauto.
  }
  { (* Ternary operations *)
    inv H2; unfold addmuldiv_instrs, diveucl_21_instrs, load_local_i64.
    - (* diveucl_21 *) {
      remember (diveucl_21_loop glob_cap glob_tmp1 glob_tmp2 glob_tmp3 glob_tmp4 63) as loop_es.
      (* Avoid unfolding too much to avoid slowdown *)

      repeat match goal with
             | |- context C [?x :: ?l] => lazymatch l with [::] => fail | _ => rewrite -(cat1s x l) end
             end;
        repeat rewrite catA; repeat eapply bet_composition';
        try solve_bet Hcontext'; eauto.
      1,3: now eapply increment_glob_mem_ptr_typing.

      subst loop_es.
      eapply bet_loop with (tn:=[]). reflexivity.
      cbn. unfold diveucl_21_loop.
      prepare_solve_bet; try (solve_bet Hcontext0; eauto). cbn.
      eapply bet_br with (t1s:=[]) (ts:=[]) (t2s:=[]). reflexivity. }
    - (* addmuldiv *)
      prepare_solve_bet; (eapply increment_glob_mem_ptr_typing; eauto) || solve_bet Hcontext'; eauto.  }
Unshelve. all: by repeat constructor.
Qed.

Theorem repr_expr_LambdaANF_Wasm_typing {lenv} : forall e e' mem c,
  @context_restr lenv c ->
  expression_restricted cenv e ->
  @repr_expr_LambdaANF_Wasm lenv e mem e' ->
  be_typing c e' (Tf [::] [::]).
Proof.
  intros ???? Hcontext Hrestr Hexpr.
  have IH := repr_expr_LambdaANF_Wasm_mut cenv fenv nenv penv lenv
  (fun (e: exp) (mem : N) (e': list basic_instruction) (H: repr_expr_LambdaANF_Wasm lenv e mem e') =>
    forall c,
      @context_restr lenv c ->
      expression_restricted cenv e ->
      be_typing c e' (Tf [::] [::]))
  (fun y' cl mem brs1 brs2 (H: repr_branches cenv fenv nenv penv y' cl mem brs1 brs2) =>
    forall y c brs1' brs2',
      @context_restr lenv c ->
      expression_restricted cenv (Ecase y cl) ->
      @repr_var nenv lenv y y' ->
      repr_case_boxed y' brs1 brs1' ->
      repr_case_unboxed y' brs2 brs2' ->
         be_typing c brs1' (Tf [::] [::])
      /\ be_typing c brs2' (Tf [::] [::])).
  apply IH with (c:=c) in Hexpr; clear IH; auto.
  - (* Ehalt *)
    intros ????? Hcontext' Hrestr'.
    by prepare_solve_bet; try solve_bet Hcontext'.
  - (* Eproj *)
    intros ????????? Hexpr' IH ??? Hcontext' Hrestr'.
    assert (exists m, lookup_N (tc_mems c0) 0 = Some m) as [m Hm]. {
    destruct (tc_mems c0) eqn:Hc; cbn; eauto. by apply Hcontext' in Hc. }
    prepare_solve_bet; try solve_bet Hcontext'. inv Hrestr'. now apply IH.
  - (* Econstr *)
    intros ???????????????? Hexpr' IH ? Hargs ? Hcontext' Hrestr'.
    eapply bet_composition'. eapply call_grow_mem_if_necessary_typing; eassumption.
    inv Hargs.
    + (* boxed constr. *)
      assert (exists m, lookup_N (tc_mems c0) 0 = Some m) as [m Hm]. {
        destruct (tc_mems c0) eqn:Hc; cbn; eauto. by apply Hcontext' in Hc. }
      prepare_solve_bet; try solve_bet Hcontext'.
      * now eapply constr_args_store_typing.
      * inv Hrestr'. now eapply IH.
    + (* unboxed constr. *)
      prepare_solve_bet; try solve_bet Hcontext'. inv Hrestr'. now apply IH.
  - (* Ecase *)
    intros ????????? Hbranch IH ??? Hcontext' Hrestr'.
    have Hcontext'' := Hcontext'. apply update_label_preserves_context_restr in Hcontext''.
    have Htyping := IH _ _ _ _ Hcontext'' Hrestr' r r0 r1. destruct Htyping as [Hty1 Hty2]. clear IH Hcontext''.
    by prepare_solve_bet; solve_bet Hcontext'.
  - (* Eapp *)
    intros ?????? Hargs Hv ? Hcontext' Hrestr'.
    assert (be_typing c0 [::instr] (Tf [::] [::T_num T_i32])) as Ht. { inv Hv; solve_bet Hcontext'. }
    prepare_solve_bet. inv Hrestr'. now eapply fun_args_typing.
    apply bet_weakening with (ts:=(repeat (T_num T_i32) (Datatypes.length args))) in Ht.
    now rewrite cats0 in Ht. inv Hrestr'.
    assert (exists t, lookup_N (tc_tables c0) 0%N = Some t /\ tt_elem_type t = T_funcref) as [t' [Ht1' Ht2']] by apply Hcontext'.
    eapply bet_return_call_indirect with (t3s:=[::]); try apply Hcontext'; eauto.
  - (* Eletapp *)
    intros ??????????? Hexpr' IH Hargs Hv ? Hcontext' Hrestr'.
    assert (be_typing c0 [::instr] (Tf [::] [::T_num T_i32])) as Ht. { inv Hv; solve_bet Hcontext'. }
    prepare_solve_bet; try solve_bet Hcontext'. now eapply fun_args_typing.
    apply bet_weakening with (ts:=(repeat (T_num T_i32) (Datatypes.length args))) in Ht.
    now rewrite cats0 in Ht. inv Hrestr'.
    assert (exists t, lookup_N (tc_tables c0) 0%N = Some t /\ tt_elem_type t = T_funcref) as [t' [Ht1' Ht2']] by apply Hcontext'.
    eapply bet_call_indirect; (try by apply Hcontext'); eauto.
    inv Hrestr'. now eapply IH.
  - (* Eprim_val *)
    intros ????????? Hvar Hexpr' IH Hprim Hgrow ? Hcontext' Hrestr'.
    eapply bet_composition'. eapply call_grow_mem_if_necessary_typing; eassumption.
    assert (exists m, lookup_N (tc_mems c0) 0 = Some m) as [m Hm]. {
      destruct (tc_mems c0) eqn:Hc; cbn; eauto. by apply Hcontext' in Hc. }
    eapply bet_composition'. prepare_solve_bet; try solve_bet Hcontext'.
    inv Hrestr'. by apply IH.
  - (* Eprim *)
    intros ??????????????? Hvar Hexpr' IH Hp Hop HprimOp Hgrow ? Hcontext' Hrestr'.
    (* Remove the assumption 'KernameMap.find op_name primop_map = Some op' from the context
       as this causes e.g. discriminate to hang *)
    clear Hop.
    assert (exists m, lookup_N (tc_mems c0) 0 = Some m) as [m Hm]. {
      destruct (tc_mems c0) eqn:Hc; cbn; eauto. by apply Hcontext' in Hc. }
    eapply bet_composition'. eapply call_grow_mem_if_necessary_typing; eassumption.
    eapply bet_composition'. prepare_solve_bet; try solve_bet Hcontext'.
    eapply prim_op_typing; eauto.
    prepare_solve_bet. solve_bet Hcontext'.
    inv Hrestr'; by apply IH.
  - (* repr_branches nil *)
    intros ?????? Hcontext' Hrestr' Hvar Hboxed Hunboxed.
    inv Hboxed. inv Hunboxed. by split; solve_bet Hcontext'.
  - (* repr_branches cons_boxed *)
    intros ?????????? Hbranch IH1 ??? Hexpr' IH2 ???? Hcontext' Hrestr' Hvar Hboxed Hunboxed.
    inv Hboxed. split. 2:{ inv Hrestr'. inv H1. eapply IH1; eauto. by constructor. }
    assert (exists m, lookup_N (tc_mems c0) 0 = Some m) as [m Hm]. {
      destruct (tc_mems c0) eqn:Hc; cbn; eauto. by apply Hcontext' in Hc. }
    prepare_solve_bet; try solve_bet Hcontext'.
    + apply IH2=>//. inv Hrestr'. now inv H1.
    + eapply IH1 in H4; last apply Hunboxed; first (now destruct H4); eauto.
      inv Hrestr'. inv H1. by constructor.
  - (* repr_branches cons_unboxed *)
    intros ?????????? Hbranch IH1 ??? Hexpr' IH2 ???? Hcontext' Hrestr' Hvar Hboxed Hunboxed.
    inv Hunboxed.
    split. { eapply IH1 in Hboxed; eauto. now destruct Hboxed. inv Hrestr'. inv H1. by constructor. }
    prepare_solve_bet; try solve_bet Hcontext'.
    + apply IH2=>//. inv Hrestr'. now inv H1.
    + eapply IH1 in H4; first (now destruct H4); eauto.
      inv Hrestr'. inv H1. by constructor.
Qed.

End FUNCTION_BODY_TYPING.
