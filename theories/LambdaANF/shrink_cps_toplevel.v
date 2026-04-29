Require compcert.lib.Maps compcert.lib.Coqlib.
From Stdlib Require Import Relation_Definitions Ensembles micromega.Lia micromega.Zify PArith.BinPos.
Require Import LambdaANF.Ensembles_util LambdaANF.term LambdaANF.rename LambdaANF.ctx LambdaANF.logical_relations LambdaANF.tactics LambdaANF.term_util
        LambdaANF.List_util LambdaANF.shrink_cps LambdaANF.eval LambdaANF.set_util LambdaANF.identifiers LambdaANF.stemctx LambdaANF.shrink_cps_correct
        LambdaANF.shrink_cps_corresp LambdaANF.inline_letapp LambdaANF.algebra LambdaANF.Ensembles_util
        LambdaANF.rel_comp LambdaANF.functions.


Section Srink_top_correct.

  Variable pr : prims.
  Variable cenv : ctor_env.

  Context {fuel : Type} {Hfuel : @fuel_resource fuel} {trace : Type} {Htrace : @trace_resource trace}.

  Variable (P1 : nat ->  @PostT fuel trace) (PG : @PostGT fuel trace)
           (HPost : forall n, n <= 1 -> Post_properties cenv (P1 n) (P1 n) PG)
           (HPost' : Post_properties cenv PG PG PG)

           (Hless_steps_app : forall f ft ys rho1 e2 rho2, post_Eapp_l (P1 0) (P1 1) f ft ys rho1 e2 rho2)
           (Hless_steps_letapp : remove_steps_letapp cenv (P1 0) (P1 0) (P1 1))
           (Hless_steps_letapp_OOT : remove_steps_letapp_OOT cenv (P1 0) (P1 1)).

  Context (Hless_steps_ctx :
             forall C e1 rho1 (rho1' : env) (e2 : exp) (rho2 : env) (cin1 cin2 : fuel)
                    (cout1 cout2 : trace),
               ctx_to_rho C rho1 rho1' ->
               len_exp_ctx C = 1 ->
               P1 0 (e1, rho1', cin1, cout1) (e2, rho2, cin2, cout2) ->
               P1 1 (C |[ e1 ]|, rho1, cin1 <+> one (C |[ e1 ]|), cout1 <+> one (C |[ e1 ]|)) (e2, rho2, cin2, cout2)).

  Context (Hless_steps_case :
             forall x cl t e n rho1 rho2 cin1 cout1 cin2 cout2,
               find_tag_nth cl t e n ->
               P1 0 (e, rho1, cin1, cout1) (e, rho2, cin2, cout2) ->
               P1 1 (Ecase x cl, rho1, cin1 <+> one (Ecase x cl), cout1 <+> one (Ecase x cl)) (e, rho2, cin2, cout2)).

  Context (Hubound1 : post_upper_bound (P1 1))
          (Hubound2 : post_upper_bound PG).


  (* XXX duplicate definitions *)
  Definition well_scoped e :=
    unique_bindings e /\ Disjoint _ (bound_var e) (occurs_free e).

  Definition wf_pres e1 e2 :=
    occurs_free e2 \subset occurs_free e1.

  Definition post_prop P1 PG :=
    Post_properties cenv P1 P1 PG /\
    post_upper_bound P1.

  (* To handle terms with disjoint bv and of instead of closed, used this with xs = fv (e) : *)
  Theorem gsr_clos_unwrap :
    forall s f t xs e  e',
      gsr_clos s (Efun (Fcons f t xs e Fnil) (Ehalt f)) e' ->
      exists e'', e' = (Efun (Fcons f t xs e'' Fnil) (Ehalt f)) /\
                  gsr_clos s e e''.
  Proof.
    intros s f t xs e  e' H.
    assert (Heq : Efun (Fcons f t xs e Fnil) (Ehalt f) = Efun (Fcons f t xs e Fnil) (Ehalt f)).
    reflexivity.

    revert H Heq.
    generalize (Efun (Fcons f t xs e Fnil) (Ehalt f)) at 1 3.
    intros e0 H. revert f t xs e.
    induction H.
    + intros.
      subst. eapply sr_unwrap_halt in H. destructAll.
      edestruct IHgsr_clos. reflexivity. destructAll.
      eexists. split; eauto.
      econstructor; eassumption.
    + intros. subst. eexists. split; eauto.
      constructor.
  Qed.

  Theorem shrink_corresp_top e:
    unique_bindings e ->
    Disjoint var (bound_var e) (occurs_free e) ->
    let (e', n) := shrink_top e in
    (exists m, m >= n /\ preord_exp_n cenv wf_pres post_prop m e e') /\
    unique_bindings e' /\
    Disjoint _ (occurs_free e') (bound_var e') /\
    occurs_free e' \subset occurs_free e /\
    bound_var e' \subset bound_var e.
  Proof.
    intros Hun Hdis.

    unfold shrink_top.

    remember (contract (M.empty var) (init_census _) _ (M.empty svalue)
                       (M.empty bool)) as s.
    destruct s as [[[[ ? ? ] ? ] ? ] ?]. symmetry in Heqs.

    eapply shrink_corresp with (c:= Hole_c) in Heqs; simpl; destructAll.
    rewrite <- (proj1 rename_all_ns_empty) in *; auto.

    simpl in *.  eapply gsr_clos_unwrap in H. destructAll.
    edestruct gsr_clos_preserves. eassumption. eassumption. eassumption.
    eapply gsr_clos_in_rw in H3; eauto. destructAll.

    { destructAll.
      split; [| split; [| split; [| split ]]].
      + clear H2 H1 H0 Hun Hdis. revert n H3. induction H5; intros n' H3.
        { edestruct IHrefl_trans_closure_n with (n := n).
          eassumption. eassumption. lia. destructAll.
          eexists. split.
          2:{ eapply preord_exp_n_trans; [| eassumption ].
              econstructor. intros. eapply gen_rw_correct; eauto.
              eapply grw_preserves_fv. eassumption.
              split. now eauto. eassumption. }
          lia. }

        exists 1. split. lia.
        econstructor. intros. eapply preord_exp_refl.
        eassumption. eassumption.
        clear. firstorder.
        split. eassumption. eassumption.
      + eassumption.
      + sets.
      + eapply gr_clos_preserves_fv. eassumption.
      + eapply gr_clos_preserves_bv. eassumption. }

    - rewrite <- (proj1 rename_all_ns_empty) in *; auto.
      econstructor. now econstructor.
      2:{ repeat normalize_bound_var. sets. }

      econstructor.
      + intros Hc. eapply bound_var_leq_max_var with (y := 1%positive) in Hc.
        zify. lia.
      + intros Hc. inv Hc.
      + rewrite <- FromSet_elements. rewrite <- exp_fv_correct. sets.
      + normalize_bound_var. sets.
      + normalize_bound_var. sets.
      + intros Hc. eapply FromSet_elements in Hc.
        rewrite <- exp_fv_correct in Hc.
        eapply occurs_free_leq_max_var with (y := 1%positive) in Hc.
        zify. lia.
      + eapply NoDupA_NoDup. eapply PS.elements_spec2w.
      + eassumption.
      + now constructor.
    - unfold closed_exp. split; sets.
      repeat normalize_occurs_free.
      rewrite <- (proj1 rename_all_ns_empty) in *; auto.
      simpl. repeat normalize_sets.
      rewrite <- image_Singleton at 1. rewrite apply_r_empty.
      rewrite image_Singleton. rewrite Setminus_Same_set_Empty_set.
      normalize_sets. rewrite <- FromSet_elements.
      rewrite exp_fv_correct. sets.
    - rewrite <- (proj1 rename_all_ns_empty), apply_r_empty in *; auto.
      eapply init_census_correct.
    - apply empty_view_hole.
    -  intro.
       intro.
       unfold get_b in H.
       rewrite M.gempty in H. inv H.
    - intro. intros.
      rewrite M.gempty in H. inv H.
  Qed.

End Srink_top_correct.
