From Stdlib Require Import
  Lists.ListDec
  ZArith Lia List.

From CertiRocq Require Import
  LambdaANF.Ensembles_util
  LambdaANF.term
  LambdaANF.term_util
  LambdaANF.eval
  LambdaANF.identifiers
  CodegenWasm.LambdaANF_to_Wasm
  CodegenWasm.LambdaANF_to_Wasm_utils
  CodegenWasm.LambdaANF_to_Wasm_correct
  CodegenWasm.LambdaANF_to_Wasm_primitives_correct
  CodegenWasm.LambdaANF_to_Wasm_instantiation
  CodegenWasm.LambdaANF_to_Wasm_restrictions.

From Wasm Require Import
  opsem.

Import Lia.
Import Relations.Relation_Operators.
Import ssreflect eqtype.
Import LambdaANF.term compM.
Import ListNotations.
Import seq.

Section TOPLEVEL.

Variable cenv:LambdaANF.term.ctor_env.
Variable funenv:LambdaANF.term.fun_env.
Variable nenv : LambdaANF.cps_show.name_env.
Variable penv : LambdaANF.toplevel.prim_env.

Context `{ho : host}.

(* TOPLEVEL CORRECTNESS THEOREM *)
Theorem LambdaANF_Wasm_related :
  forall (v : term.val) (e : exp) (n : nat)
         (hs : host_state) module fenv lenv (pfs : M.t (list val -> option val)),
  (* primitive env well-formed *)
  prim_funs_env_returns_no_funvalues pfs ->
  prim_funs_env_wellformed cenv penv pfs ->

  (* constructors well-formed *)
  correct_cenv_of_exp cenv e ->
  cenv_restricted cenv ->

  (* vars unique (guaranteed by previous stage) *)
  NoDup ((collect_all_local_variables e) ++ (collect_function_vars e))%list ->

  (* expression must be closed *)
  (~ exists x, occurs_free e x ) ->

  (* evaluation of LambdaANF expression *)
  bstep_e pfs cenv (M.empty _) e v n ->

  (* compilation to Wasm module *)
  LambdaANF_to_Wasm nenv cenv penv e = Ret (module, fenv, lenv) ->

  exists sr fr,
    (* instantiation *)
    instantiate' module hs sr fr /\

    exists sr',
    (* execute main function *)
    reduce_trans (hs, sr,  (Build_frame [] (f_inst fr)), [ AI_basic (BI_call main_function_idx) ])
                 (hs, sr', (Build_frame [] (f_inst fr)), [])    /\
    (* result variable has the correct value set *)
    result_val_LambdaANF_Wasm cenv fenv nenv penv v sr' (f_inst fr).
Proof.
  intros ???????? HprimFunsRet HprimFunsRelated Hcenv HcenvRestr HvarsNodup Hfreevars Hstep LANF2Wasm.
  assert (exists fds e', e = Efun fds e') as [fds [e' ->]]. {
    unfold LambdaANF_to_Wasm in LANF2Wasm.
    destruct (check_restrictions cenv e)=>//.
    destruct e =>//. eauto.
  } rename e' into e.

  assert (HeRestr: expression_restricted cenv (Efun fds e)).
  { unfold LambdaANF_to_Wasm in LANF2Wasm. destruct (check_restrictions cenv _) eqn:HeRestr.
    inv LANF2Wasm. destruct u. eapply check_restrictions_expression_restricted; eauto.
    apply rt_refl. }

  assert (Hmaxfuns : (Z.of_nat (numOf_fundefs fds) <= max_num_functions)%Z). {
    unfold max_num_functions.
    inv HeRestr. assumption.
  }

  assert (Hnodup': NoDup (collect_function_vars (Efun fds e))). {
    now eapply NoDup_app_remove_l in HvarsNodup.
  }

  have HI := @instantiation_combined_INV_and_more _ _ _ _ _ _ _ _ _ _ _ _ hs Hnodup' HeRestr
               Hcenv Logic.eq_refl Hmaxfuns LANF2Wasm.
  destruct HI as [sr [fr [Hinst [Hinv [HinstFuncs [HfVal [main_fn [e' [fns [-> [Hfuncs [Hexpr' Hfns']]]]]]]]]]]].

  exists sr, fr.
  split. assumption.

  remember (Build_frame (repeat (VAL_num (nat_to_value 0)) (length (collect_local_variables e))) (f_inst fr)) as f_before_IH.

  unfold LambdaANF_to_Wasm in LANF2Wasm.
  remember (list_function_types (Z.to_nat max_function_args)) as ftypes.
  destruct (check_restrictions cenv _). inv LANF2Wasm.
  destruct (translate_functions _ _ _ _ _) eqn:Hfuns=>//. simpl in LANF2Wasm.
  destruct (translate_body _ _ _ _ _) eqn:Hexpr. inv LANF2Wasm. rename l into fns'. rename l0 into wasm_main_instr.
  inv LANF2Wasm.

  (* from lemma module_instantiate_INV_and_more_hold *)
  assert (e' = wasm_main_instr) by congruence. subst e'. clear Hexpr'.
  assert (fns = fns') by congruence. subst fns'. clear Hfns'.

  remember (Build_frame (repeat (VAL_num (nat_to_value 0)) (length (collect_local_variables e))) (f_inst fr)) as f_before_IH.
  remember (create_local_variable_mapping (collect_local_variables e)) as lenv.
  remember (create_fname_mapping (Efun fds e)) as fenv.

   assert (HlocInBound: (forall (var : positive) (varIdx : funcidx),
          repr_var (lenv:=lenv) nenv var varIdx -> N.to_nat varIdx < Datatypes.length (f_locs f_before_IH))).
   { intros ? ? Hvar. subst f_before_IH. cbn. rewrite repeat_length. inv Hvar.
     eapply var_mapping_list_lt_length. eassumption. }

  assert (Hinv_before_IH: INV fenv nenv sr f_before_IH). {
    subst f_before_IH fenv.
    now eapply init_locals_preserves_INV with (args:=[]).
  }

  assert (HmemAvail: min_available_memory sr (f_inst f_before_IH) 0). {
    intros ????.
    destruct Hinv_before_IH as [_[_[_[_[_[_[_[HgmpInM _]]]]]]]].
    eapply HgmpInM in H0; eauto.
    lia. }

  inversion Hstep. subst fl v0 c rho. clear Hstep. rename H4 into Hstep.

  eapply translate_body_correct in Hexpr; try eassumption.
  2:{ eapply Forall_constructors_subterm. eassumption. constructor.
      apply dsubterm_fds2. }

  (* prepare IH *)

  assert (HlenvInjective : map_injective lenv). {
    subst lenv.
    intros x y x' y' Hneq Hx Hy Heq. subst y'.
    apply NoDup_app_remove_r in HvarsNodup. cbn in HvarsNodup.
    apply NoDup_app_remove_r in HvarsNodup.
    cbn in Hx, Hy.
    have H' := create_local_variable_mapping_injective _ 0%N HvarsNodup _ _ _ _ Hneq Hx Hy. auto. }

  assert (HenvsDisjoint : domains_disjoint lenv fenv). {
    rewrite Heqfenv. subst lenv. eapply variable_mappings_nodup_disjoint; eauto.
    cbn in HvarsNodup. rewrite <-catA in HvarsNodup.
    now eapply NoDup_app_remove_middle in HvarsNodup.
  }

  assert (Hnodup'': NoDup (collect_local_variables e ++
                          collect_function_vars (Efun fds e))). {
    cbn in HvarsNodup. rewrite <-catA in HvarsNodup.
    now eapply NoDup_app_remove_middle in HvarsNodup.
  }

  assert (HfenvWf: (forall f : var,
       (exists res : fun_tag * seq var * exp,
          find_def f fds = Some res) <->
       (exists i : funcidx,
          fenv ! f = Some i))). {
    subst fenv. intros; split; intros.
    - apply notNone_Some in H.
      rewrite find_def_in_collect_function_vars in H.
      apply notNone_Some. apply variable_mapping_In_Some.
      + now eapply NoDup_app_remove_l in HvarsNodup.
      + assumption.
    - destruct H as [i H]. apply variable_mapping_Some_In in H; auto.
      rewrite <- find_def_in_collect_function_vars in H.
      now apply notNone_Some.
  }

  assert (HfenvRho: (forall (a : positive) (v0 : term.val),
       (def_funs fds fds (M.empty _) (M.empty _)) ! a = Some v0 ->
       find_def a fds <> None -> v0 = Vfun (M.empty _) fds a)). {
    intros ? ? H H1. eapply def_funs_find_def in H1; eauto. now erewrite H in H1. }

  assert (HeRestr' : expression_restricted cenv e). { now inv HeRestr. }

  assert (HfdsRestr : fds_restricted cenv fds). {
    intros ?????.
    split. { inv HeRestr. eapply H5. eassumption. }
    split. { intros x Hocc.
    assert (Hdec: decidable_eq var). {
      intros n' m'. unfold Decidable.decidable. now destruct (var_dec n' m'). }
    have H' := In_decidable Hdec x ys. destruct H'. now left.
    right. intro Hcontra'.
    exfalso. apply Hfreevars. exists x. apply Free_Efun2.
    eapply find_def_is_Some_occurs_free_fundefs; eauto.
    intro Hfd. revert Hcontra'.
    apply name_in_fundefs_find_def_is_Some in Hfd.
    now destruct Hfd as [? [? [? ?]]]. }
    rewrite catA. eapply NoDup_collect_all_local_variables_find_def; eauto.
  }

  assert (Hunbound: (forall x : var,
       In x (collect_local_variables e) ->
       (def_funs fds fds (M.empty _) (M.empty _)) ! x = None)). {
    intros. eapply def_funs_not_find_def; eauto.
    destruct (find_def x fds) eqn:Hdec; auto. exfalso.
    assert (Hdec': find_def x fds <> None) by congruence. clear Hdec p.
    apply find_def_in_collect_function_vars with (e:=e) in Hdec'.
    cbn in HvarsNodup. rewrite <- catA in HvarsNodup.
    eapply NoDup_app_remove_middle in HvarsNodup; eauto.
    by eapply NoDup_app_In in H; eauto.
  }

  assert (Hfds : fds_translated_correctly cenv fenv nenv penv fds sr (f_inst f_before_IH)). {
    intros ???? Hcontra.
    assert (Hc: find_def a fds <> None) by congruence.
    apply HfVal in Hc; auto.
    destruct Hc as [fidx [HtransF Hval]].
    exists fidx. split. assumption. subst f_before_IH.
    eapply val_relation_func_depends_on_funcs. 2: apply Hval.
    congruence.
  }

  assert (HrelE : @rel_env_LambdaANF_Wasm cenv fenv nenv penv
                   _ _ (create_local_variable_mapping (collect_local_variables e)) e (def_funs fds fds (M.empty _) (M.empty _))
          sr f_before_IH fds). {
    split.
    { (* funs1 (follows from previous Hfds) *)
      intros ? ? ? ? ? Hdf Hval. have H' := Hdf.
      apply def_funs_spec in Hdf.
      destruct Hdf as [[? ?] | [? H]]. 2: inv H.
      rewrite def_funs_eq in H'. 2: assumption.
      inv H'. apply subval_fun in Hval. 2: assumption.
      destruct Hval as [? [Hval ?]]. inv Hval => //.
    } split.
    { (* funs2 *)
      intros ? Hnfd. apply name_in_fundefs_find_def_is_Some in Hnfd.
      destruct Hnfd as [? [? [? Hfd]]]. apply Hfds in Hfd.
      destruct Hfd as [i [Htrans Hval]]. eauto. }
    { (* vars *)
      intros x Hocc Hfd. exfalso. apply Hfreevars. exists x. constructor; auto.
      intro Hcontra. apply name_in_fundefs_find_def_is_Some in Hcontra.
      now destruct Hcontra as [? [? [? ?H]]]. }
  }

  (* eval context after fn entry: one label for the main fn block *)
  remember (LH_rec [] 0 [] (LH_base [] []) []) as lh.
  remember ({| f_locs := [::]; f_inst := f_inst fr |}) as frameInit.

  subst lenv.
  have HMAIN := repr_bs_LambdaANF_Wasm_related cenv fenv nenv penv _
                   _ _ _ _ _ _ _ _ frameInit _ lh (primitive_operation_reduces_proof cenv fenv nenv penv _ HprimFunsRelated) HcenvRestr HprimFunsRet HlenvInjective
                  HenvsDisjoint Logic.eq_refl Hnodup'' HfenvWf HfenvRho
                  HeRestr' HfdsRestr Hunbound Hstep hs sr _ _ Hfds HlocInBound Hinv_before_IH HmemAvail Hexpr HrelE.
  destruct HMAIN as [s' [f' [k' [lh' [Hred [Hval [Hfinst _]]]]]]]. cbn. subst frameInit.
  exists s'. split.
  dostep'. apply r_call. cbn.
  rewrite HinstFuncs. reflexivity.
  dostep'. eapply r_invoke_native with (ves:=[]) (vs:=[]); eauto.
  rewrite Hfuncs. subst f_before_IH.  cbn. rewrite Hfinst. reflexivity. reflexivity.
  erewrite <-map_repeat_eq. by apply default_vals_i32_Some.
  subst f_before_IH. cbn. subst lh. cbn in Hred. rewrite <- Hfinst. rewrite cats0 in Hred.
  eapply rt_trans. cbn. unfold to_e_list. apply Hred.
  dostep'. constructor. apply rs_return with (lh:=lh') (vs:=[::]) =>//. apply rt_refl.
  subst f_before_IH. apply Hval.
Unshelve. all: auto.
Qed.

(* Eval compute in "Assumptions of 'LambdaANF_Wasm_related' (Wasm backend, main correctness)"%bs. *)
(* Print Assumptions LambdaANF_Wasm_related. *)

(* TODO investigate
   FunctionalExtensionality, Classical_Prop.classic,
   ClassicalDedekindReals.sig_not_dec, ClassicalDedekindReals.sig_forall_dec
   plus all the axioms for 63-bit primitive objects and operations *)

End TOPLEVEL.
