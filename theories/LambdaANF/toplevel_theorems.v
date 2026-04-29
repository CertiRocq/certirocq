
From Stdlib Require Import NArith.BinNat Relations.Relations MSets.MSets MSets.MSetRBT
        Lists.List micromega.Lia Sets.Ensembles.

Require Import LambdaANF.term LambdaANF.eval LambdaANF.term_util LambdaANF.identifiers LambdaANF.ctx LambdaANF.set_util
        LambdaANF.Ensembles_util LambdaANF.List_util LambdaANF.size_cps LambdaANF.tactics LambdaANF.relations LambdaANF.rel_comp
        LambdaANF.uncurry LambdaANF.uncurry_proto LambdaANF.bounds LambdaANF.shrink_cps LambdaANF.shrink_cps_toplevel
        LambdaANF.closure_conversion LambdaANF.closure_conversion_util LambdaANF.hoisting
        LambdaANF.lambda_lifting LambdaANF.lambda_lifting_correct LambdaANF.uncurry_correct
        LambdaANF.dead_param_elim LambdaANF.dead_param_elim_correct.
Require Export LambdaANF.logical_relations LambdaANF.logical_relations_cc LambdaANF.alpha_conv
        LambdaANF.inline_letapp LambdaANF.inline LambdaANF.inline_correct LambdaANF.algebra LambdaANF.state.
Require Import Common.compM.
Require Import compcert.lib.Coqlib.

Import ListNotations.

Close Scope Z_scope.



Section ToplevelTheorems.

  Context (cenv : ctor_env).
  Context (clo_tag : ctor_tag).
  Context (clo_itag : ind_tag).

  (* TODO use John's definition  *)
  Definition well_scoped e :=
    unique_bindings e /\ Disjoint _ (bound_var e) (occurs_free e).

  Definition fv_pres e1 e2 :=
    occurs_free e2 \subset occurs_free e1.


  Definition post_prop P1 PG :=
    Post_properties cenv P1 P1 PG /\
    post_upper_bound P1.

  (** Correctness spec for (composition of) "identity" transformations *)

  Definition correct (trans :  exp -> comp_data -> error exp * comp_data) :=
    forall e c,
      well_scoped e ->                                            (* src is well-scoped *)
      max_var e 1 < state.next_var c ->                           (* the pool of identifiers is fresh *)
      exists (e' : exp) (c' : state.comp_data),
        trans e c = (Ret e', c') /\                               (* the transformation successfully terminates *)
        well_scoped e' /\                                         (* trg is well-scoped *)
        max_var e' 1 < state.next_var c' /\                       (* the pool of identifiers is fresh for the target *)
        exists n, preord_exp_n cenv wf_pres post_prop n e e'.     (* src and trg are in the logical relation  *)

  (** Correctness spec for closure conversion tranformations *)

  Definition correct_cc (trans : exp -> comp_data ->  error exp * comp_data) :=
    forall e c,
      well_scoped e ->                                            (* src is well-scoped *)
      max_var e 1 < state.next_var c ->                           (* the pool of identifiers is fresh *)
      exists (e' : exp) (c' : state.comp_data),
        trans e c = (Ret e', c') /\                               (* the transformation successfully terminates *)
        well_scoped e' /\                                         (* trg is well-scoped *)
        max_var e' 1 < state.next_var c' /\                       (* the pool of identifiers is fresh for the target *)
        exists n m,  R_n_exp cenv clo_tag wf_pres post_prop       (* src and trg are in the logical relation  *)
                             (simple_bound 0) (simple_bound 0) n m e e'.



Section Inline.

 Lemma inline_correct St IH e d st c z :
   well_scoped e ->
   exists (e' : exp) (c' : state.comp_data) click,
     inline_top' St IH z d st e c = (Ret e', c', click) /\
     wf_pres e e' /\
     well_scoped e' /\
     max_var e' 1 < state.next_var c' /\
     (forall (k : nat) (rho1 rho2 : env),
         preord_env_P cenv (inline_bound d d) (occurs_free e) k rho1 rho2 ->
         preord_exp cenv (inline_bound d d) (inline_bound d d) k (e, rho1) (e', rho2)).
 Proof.
   intros H.
   edestruct inline_correct_top with (P1 := fun L => inline_bound L d)
                                     (PG := inline_bound d d).
   - intros. eapply inline_bound_compat. eassumption.
   - intros. eapply inline_bound_post_Eapp_l.
   - intros. eapply inline_bound_remove_steps_letapp.
   - intros. rewrite Nat.add_comm. eapply inline_bound_remove_steps_letapp_OOT.
   - reflexivity.
   - intro; intros. exact H0.
   - eapply H.
   - eapply H.
   - destructAll. do 3 eexists. split. eassumption.
     split. eassumption. split.
     split; eassumption. split. eassumption.
     eassumption.
 Qed.


 Corollary inline_correct_cor St IH d st z :
   correct (inline_top St IH z d st).
 Proof.
   intro; intros.
   edestruct inline_correct; eauto. destructAll.
   do 2 eexists. split.

   unfold inline_top. rewrite H1. reflexivity.
   repeat (split; [ eassumption | ]).
   eexists. econstructor. now eauto. eassumption.
   split.
   unfold inline_bound_top. eapply inline_bound_compat. lia.
   eapply inline_bound_post_upper_bound.
 Qed.


 Corollary inline_uncurry_cor x n m :
   correct (inline_uncurry x n m).
 Proof.
   intro; intros.
   edestruct inline_correct; eauto. destructAll.
   do 2 eexists. split.

   unfold inline_uncurry, inline_top. rewrite H1. reflexivity.
   repeat (split; [ eassumption | ]).
   eexists. econstructor. now eauto. eassumption.
   split.
   unfold inline_bound_top. eapply inline_bound_compat. lia.
   eapply inline_bound_post_upper_bound.
 Qed.


End Inline.


Section LambdaLift.

  Lemma lambda_lift_correct e c k l b :
   well_scoped e ->
   max_var e 1 < state.next_var c ->
   exists (e' : exp) (c' : state.comp_data),
     lambda_lift k l b e c = (Ret e', c') /\
     max_var e' 1 < state.next_var c' /\
     wf_pres e e' /\
     well_scoped e'  /\
     (forall (k : nat) (rho1 rho2 : env),
         preord_env_P cenv (ll_bound 0) (occurs_free e) k rho1 rho2 ->
         binding_in_map (occurs_free e) rho1 ->
         preord_exp cenv (ll_bound 0) (ll_bound 0) k (e, rho1) (e', rho2)).
  Proof.
    intros.
    edestruct lambda_lift_correct_top with (P1 := ll_bound)
                                           (PG := ll_bound 0).
    - intros. eapply ll_bound_compat.
    - intros. eapply ll_bound_compat.
      exact (M.empty _). exact 0%nat.
    - eapply ll_bound_mon. lia.
    - intros. eapply ll_bound_local_steps; eauto.
    - intros. eapply ll_bound_local_app.
    - intros. eapply ll_bound_local_steps_let_app; eauto.
    - intros. eapply ll_bound_local_steps_let_app_OOT; eauto.
    - intros. eapply ll_bound_local_steps_app; eauto.
    - intros. eapply ll_bound_ctx_r; eauto.
    - eapply H.
    - eassumption.
    - eapply H.
    - destructAll. do 2 eexists. split. eassumption.
      split. eassumption.
      split. eassumption. split.
      split; eassumption.
      eassumption.
  Qed.

  Corollary lambda_lift_correct_corr k l b :
    correct (lambda_lift k l b).
  Proof.
    intro; intros.
    edestruct lambda_lift_correct; eauto. destructAll.
    do 2 eexists. repeat (split; [ eassumption | ]).
    eexists. econstructor. now eauto. eassumption. split.
    eapply ll_bound_compat. eapply simple_bound_post_upper_bound.
  Qed.



End LambdaLift.


(* TODO move *)
Section Refl.

  Context (wf_pres : exp -> exp -> Prop)
          (wf_pres_refl : forall e, wf_pres e e)
          (lf : var).

  Context (fuel trace : Type)  {Hf : @fuel_resource fuel} {Ht : @trace_resource trace}.

  Lemma preord_exp_n_refl e :
    preord_exp_n cenv wf_pres post_prop 1 e e.
  Proof.
    econstructor; eauto.
    2:{ split. eapply simple_bound_compat. eapply simple_bound_post_upper_bound. }
    intros.
    eapply preord_exp_refl; eauto.
    eapply simple_bound_compat.
  Qed.

End Refl.

Section CCHoist.


  Lemma closure_conversion_hoist_correct :
    correct_cc (closure_conversion_hoist clo_tag clo_itag).
  Proof.
    intros e c Hws Hmvar.
    edestruct closure_conversion_correct.exp_closure_conv_correct
      with (boundL := simple_bound) (boundG := simple_bound 0).
    (* CC bounds *)
    - eapply simple_bound_compat.
    - eapply Hpost_locals_r.
    - eapply Hpost_locals_l.
    - eapply Hpost_locals_l0.
    - eapply HOOT.
    - eapply HPost_letapp_cc.
    - eapply HPost_letapp_OOT_cc.
    - eapply bounds.HPost_app.
    - eapply Hbase.
    (* scoping *)
    - eapply Hws.
    - eapply Hws.
    - eassumption.
    - destructAll.

      edestruct (exp_hoist x) as [e' m] eqn:Hhoist.

      edestruct exp_hoist_correct_top with
          (e := x)
          (P1 := fun n =>  hoisting_bound n m)
          (P2 := hoisting_bound m m)
          (PG := hoisting_bound m m).

      (* Hoisting bounds *)
      + intros. eapply hoisting_bound_compat. eassumption.
      + intros. eapply hoisting_bound_mon. eassumption.
      + intros. eapply hoisting_bound_post_Efun_l.
      + intros. eapply hoisting_bound_post_Efun_r. eassumption.
      + eapply hoisting_bound_compat; eauto.
      + intros. eapply hoisting_bound_mon. eassumption.
      + reflexivity.
      (* scoping *)
      + easy.
      + eapply Disjoint_sym. eassumption.
      + eassumption.
      + eassumption.
      + destructAll. do 2 eexists. split; [| split; [| split ] ].
        * unfold closure_conversion_hoist. rewrite H. rewrite Hhoist. simpl. reflexivity.
        * split. eassumption. sets.
        * eapply Pos.le_lt_trans; [| eassumption ].
          eapply dead_param_elim_correct.max_var_le. eapply Included_Union_compat. eassumption. eassumption.
        * do 2 eexists. econstructor. split.
          ++ eapply preord_exp_n_refl.
             clear; firstorder.
          ++ eexists. split. split.
             2:{ eassumption. }
             2:{ econstructor. intros. eapply H6. eassumption.
                 eassumption.
                 split. eapply hoisting_bound_compat. lia.
                 eapply hoisting_bound_post_upper_bound. }
             intros. eassumption.
  Qed.

End CCHoist.

Section Shrink.

  Lemma shrink_top_correct e e' m :
    well_scoped e ->
    shrink_top e = (e', m) ->
    exists m,
      well_scoped e' /\
      occurs_free e' \subset occurs_free e /\
      bound_var e' \subset bound_var e /\
      preord_exp_n cenv wf_pres post_prop m e e'.
  Proof.
    intros.
    intros. intros.
    assert (Hs := shrink_corresp_top cenv (fun L => inline_bound L 1) (inline_bound 1 1)).
    inv H.

    assert (Ha : let (e', n) := shrink_top e in
                 (exists m : nat,
                     (m >= n)%nat /\
                     preord_exp_n cenv shrink_cps_toplevel.wf_pres (shrink_cps_toplevel.post_prop cenv) m e e') /\
                 unique_bindings e' /\
                 Disjoint var (occurs_free e') (bound_var e') /\
                 occurs_free e' \subset occurs_free e /\ bound_var e' \subset bound_var e).
    { eapply Hs.

      - intros. eapply inline_bound_compat. eassumption.
      - intros. eapply inline_bound_compat. lia.
      - intros. eapply inline_bound_post_Eapp_l.
      - eapply inline_bound_remove_steps_letapp.
      - assert (Hs' := inline_bound_remove_steps_letapp_OOT cenv 0 0 1).
        eassumption.
      - eapply inline_bound_ctx1.
      - eapply inline_bound_Ecase.
      - eapply inline_bound_post_upper_bound.
      - eapply inline_bound_post_upper_bound.
      - eassumption.
      - eassumption. }

    rewrite H0 in Ha. destructAll. eexists. split.
    split. eassumption. sets.
    eauto.
  Qed.


  Corollary shrink_err_correct :
    correct shrink_err.
  Proof.
    intro; intros.
    destruct (shrink_top e) eqn:Hres.
    exists e0, c.
    edestruct shrink_top_correct; eauto. destructAll.
    eexists.
    unfold shrink_err.
    unfold shrink_err. rewrite Hres. reflexivity.
    split; [| split ]; eauto.

    eapply Pos.le_lt_trans. eapply max_var_le. 2: eassumption.

    sets.
  Qed.


End Shrink.

Section InlineLoop.


  Lemma inline_loop_correct z bound d :
    correct (inline_shrink_loop z bound d).
  Proof.
    intros e c. unfold inline_shrink_loop, inline_loop.
    revert e c. generalize 1000%nat.
    induction n; intros.
   - simpl. do 2 eexists.
     split. reflexivity.
     split. eassumption. split. eassumption.
     eexists. eapply preord_exp_n_refl.
     intros. unfold wf_pres. sets.
   - destructAll. simpl.
     edestruct inline_correct with (e := e). eassumption.
     destructAll.
     destruct (shrink_top x) eqn:Hshrink.
     edestruct shrink_top_correct; [| eassumption | ]. eassumption.
     destructAll.
     destruct x1.
     + edestruct (IHn e0). eassumption.
       eapply Pos.le_lt_trans. eapply max_var_le. 2: eassumption. sets.
       destructAll.
       do 2 eexists. erewrite H1. split; [| split ].
       rewrite Hshrink. simpl. eassumption. eassumption.
       split. eassumption. eexists.
       econstructor 2.
       * econstructor 1. now eauto. eassumption.
         split. eapply inline_bound_compat. lia.
         eapply inline_bound_post_upper_bound.
       * econstructor 2. eassumption. eassumption.
     + do 2 eexists. rewrite H1.
       split. reflexivity.
       split. rewrite Hshrink. eassumption.
       split. rewrite Hshrink.
       eapply Pos.le_lt_trans. eapply max_var_le. 2: eassumption. sets.
       rewrite Hshrink. eexists. simpl.
       econstructor 2.
       * econstructor 1. now eauto. eassumption.
         split. eapply inline_bound_compat. lia.
         eapply inline_bound_post_upper_bound.
       * eassumption.
  Qed.

End InlineLoop.

Section Uncurry.

  Lemma test : (forall b e c r, uncurry_top b e c = r -> uncurry_top b e c = r).
  Proof. intros. Abort.

  Lemma uncurry_top_correct e c b :
   well_scoped e ->
   max_var e 1 < state.next_var c ->
   exists (e' : exp) (c' : state.comp_data),
     uncurry_top b e c = (Ret e', c') /\
     max_var e' 1 < state.next_var c' /\
     wf_pres e e' /\
     well_scoped e'  /\
     (forall (k : nat) (rho1 rho2 : env),
         preord_env_P cenv (simple_bound 0) (occurs_free e) k rho1 rho2 ->
         binding_in_map (occurs_free e) rho1 ->
         preord_exp cenv (simple_bound 0) (simple_bound 0) k (e, rho1) (e', rho2)).
  Proof.
    intros.
    edestruct (@uncurry_correct_top cenv nat _ (nat * nat) _ (simple_bound 0)
                                    (simple_bound 0)) with (cps := b).
    - intros. eapply simple_bound_compat.
    - intros. eapply simple_bound_compat.
    - eapply Hpost_curry.
    - eapply Hpost_idemp.
    - clear. unfold comp, simple_bound. intro; intros.
      destructAll.
      destruct x as [[[? ?] ?] [? ? ]].
      destruct y as [[[? ?] ?] [? ? ]].
      destruct x0 as [[[? ?] ?] [? ? ]]. lia.
    - inv H. eassumption.
    - inv H. eassumption.
    - eassumption.
    - destructAll. exists x, x0.
      split. assumption.
      split. eassumption.
      split. eassumption.
      split. split; eassumption.
      now eauto.
  Qed.

  Corollary uncurry_top_correct_corr b :
    correct (uncurry_top b).
  Proof.
    intro; intros.
    edestruct uncurry_top_correct. eassumption. eassumption.
    destructAll.
    do 2 eexists. split.
    eassumption.
    repeat (split; [ eassumption | ]).
    eexists. econstructor. now eauto. eassumption. split.
    eapply simple_bound_compat. eapply simple_bound_post_upper_bound.
  Qed.


End Uncurry.


Section DPE.

  Lemma DPE_correct e c :
    well_scoped e ->
    max_var e 1 < state.next_var c ->
    exists (e' : exp) (c' : state.comp_data),
      DPE e c = (Ret e', c') /\
      max_var e' 1 < state.next_var c' /\
      wf_pres e e' /\
      well_scoped e'  /\
      (forall (k : nat) (rho1 rho2 : env),
          preord_env_P cenv (ll_bound 0) (occurs_free e) k rho1 rho2 ->
          binding_in_map (occurs_free e) rho1 ->
          preord_exp cenv (simple_bound 0) (simple_bound 0) k (e, rho1) (e', rho2)).
  Proof.
    intros.
    edestruct DPE_correct_top with (PL := simple_bound 0)
                                   (PG := simple_bound 0).
    - intros. eapply simple_bound_compat.
    - eapply H.
    - eassumption.
    - eapply H.
    - destructAll. do 2 eexists. split. eassumption.
      split. eassumption.
      split. eassumption. split.
      split; eassumption.
      eassumption.
  Qed.

  Corollary DPE_correct_corr :
    correct DPE.
  Proof.
    intro; intros.
    edestruct DPE_correct; eauto. destructAll.
    do 2 eexists. repeat (split; [ eassumption | ]).
    eexists. econstructor. now eauto. eassumption. split.
    eapply simple_bound_compat. eapply simple_bound_post_upper_bound.
  Qed.

End DPE.

End ToplevelTheorems.

Require Import ExtLib.Structures.Monad LambdaANF.toplevel.
Import MonadNotation.


Section Compose.

  Context (cenv : ctor_env).

  Transparent bind.

  Lemma correct_compose (t1 t2 : anf_trans) :
    correct cenv t1 ->
    correct cenv t2 ->
    correct cenv (fun e => e <- t1 e;; t2 e).
  Proof.
    intros Ht1 Ht2. intro; intros.
    edestruct Ht1; eauto. destructAll.
    edestruct Ht2. eapply H2. eassumption. destructAll.
    do 2 eexists. split; [| split; [| split ]].
    - simpl. unfold bind; cbn.
      rewrite H1. rewrite H5. reflexivity.
    - eassumption.
    - assumption.
    - eexists. econstructor 2; eauto.
  Qed.


  Lemma correct_cc_compose_l (t1 t2 : anf_trans) :
    correct cenv t1 ->
    correct_cc cenv clo_tag t2 ->
    correct_cc cenv clo_tag (fun e => e <- t1 e;; t2 e).
  Proof.
    intros Ht1 Ht2. intro; intros.
    edestruct Ht1; eauto. destructAll.
    edestruct Ht2. eapply H2. eassumption. destructAll.
    do 2 eexists. split; [| split; [| split ]].
    - simpl. unfold bind; cbn.
      rewrite H1. rewrite H5. reflexivity.
    - eassumption.
    - assumption.
    - inv H8. destructAll. inv H9. destructAll.
      do 3 eexists. split.
      econstructor 2. eassumption. eassumption.
      eexists. split. split; [| eassumption ]. eassumption.
      eassumption.
  Qed.


  Lemma correct_cc_compose_r (t1 t2 : anf_trans) :
    correct_cc cenv clo_tag t1 ->
    correct cenv t2 ->
    correct_cc cenv clo_tag (fun e => e <- t1 e;; t2 e).
  Proof.
    intros Ht1 Ht2. intro; intros.
    edestruct Ht1; eauto. destructAll.
    edestruct Ht2. eapply H2. eassumption. destructAll.
    do 2 eexists. split; [| split; [| split ]].
    - simpl. unfold bind; cbn.
      rewrite H1. rewrite H5. reflexivity.
    - eassumption.
    - assumption.
    - inv H4. destructAll. inv H9. destructAll.
      do 3 eexists. split. eassumption.
      eexists. split. split; [| eassumption ]. eassumption.
      econstructor 2; eassumption.
  Qed.


  Lemma correct_time (t : anf_trans) o s :
    correct cenv t ->
    correct cenv (time_anf o s t).
  Proof.
    unfold time_anf.
    intros.
    destruct (time o); eauto.
  Qed.

  Lemma correct_cc_time (t : anf_trans) o s :
    correct_cc cenv clo_tag t ->
    correct_cc cenv clo_tag (time_anf o s t).
  Proof.
    unfold time_anf.
    intros.
    destruct (time o); eauto.
  Qed.

  Opaque uncurry_top.

  Lemma correct_id_trans :
    correct cenv id_trans.
  Proof.
    intro; intros.
    do 2 eexists. split. reflexivity.
    split. eassumption.
    split. eassumption.
    eexists. econstructor 1.
    3:{ split. eapply simple_bound_compat. eapply simple_bound_post_upper_bound. }
    intros. eapply preord_exp_refl.
    eapply simple_bound_compat. eassumption.
    clear. firstorder.
  Qed.

  Theorem anf_pipeline_correct opts v :
    correct_cc cenv clo_tag (anf_pipeline v opts).
  Proof.
    intros Heq.
    unfold anf_pipeline.
    eapply correct_cc_compose_l.

    eapply correct_time.
    now eapply shrink_err_correct.

    eapply correct_cc_compose_l.

    eapply correct_time. now eapply uncurry_top_correct_corr.

    eapply correct_cc_compose_l.

    eapply correct_time.
    now eapply inline_uncurry_cor.

    eapply correct_cc_compose_l.

    destruct (inl_before opts).
    eapply correct_time. now eapply inline_loop_correct.
    now eapply correct_id_trans.

    eapply correct_cc_compose_l.

    destruct (do_lambda_lift opts).
    eapply correct_time. now eapply lambda_lift_correct_corr.
    now eapply correct_id_trans.

    eapply correct_cc_compose_l.

    eapply correct_time. now eapply shrink_err_correct.

    eapply correct_cc_compose_r.

    eapply correct_cc_time. now eapply closure_conversion_hoist_correct.

    eapply correct_compose.

    eapply correct_time. now eapply shrink_err_correct.

    eapply correct_compose.

    destruct (inl_after opts).
    eapply correct_time. now eapply inline_loop_correct.
    now eapply correct_id_trans.

    eapply correct_compose.

    destruct (dpe opts).

    eapply correct_time. now eapply DPE_correct_corr.
    now eapply correct_id_trans.

    eapply correct_compose.

    eapply correct_time. now eapply shrink_err_correct.

    eapply correct_compose.

    destruct (inl_known opts).
    eapply correct_time.
    unfold inline_lifted. now eapply inline_correct_cor.
    now eapply correct_id_trans.

    now eapply correct_id_trans.
  Qed.



  (* Top-level correctness for whole programs *)
  Corollary anf_pipeline_whole_program_correct var opts e c :

    closed_exp e ->

    well_scoped e ->
    (max_var e 1 < state.next_var c)%positive ->

    exists (e' : exp) (c' : state.comp_data),
      anf_pipeline var opts e c = (Ret e', c') /\

      refines cenv value_ref_cc e e'.
  Proof.
    intros.
    edestruct anf_pipeline_correct; eauto. destructAll.
    do 2 eexists.

    split. eassumption.

    eapply R_n_exp_in_refines; eauto.

    clear; now firstorder.
    clear; now firstorder.
    eapply simple_bound_post_upper_bound.
  Qed.


  Lemma preord_exp_n_wf_mon wf1 wf2 p k e1 e2 :
    inclusion _ wf1 wf2 ->
    preord_exp_n cenv wf1 p k e1 e2 ->
    preord_exp_n cenv wf2 p k e1 e2.
  Proof.
    intros H1 H2. induction H2; eauto.
    now econstructor 1; eauto.
    now econstructor 2; eauto.
  Qed.

  Lemma R_n_exp_wf_mon ctag wf1 wf2 p P PG k m e1 e2 :
    inclusion _ wf1 wf2 ->
    R_n_exp cenv ctag wf1 p P PG k m e1 e2 ->
    R_n_exp cenv ctag wf2 p P PG k m e1 e2.
  Proof.
    intros H1 H2. inv H2. inv H. inv H2. destructAll.
    eexists. split. now eapply preord_exp_n_wf_mon.
    eexists. split; eauto. now eapply preord_exp_n_wf_mon.
  Qed.


  (* Top-level correctness for linking *)
  Corollary anf_pipeline_linking_correct lf x v1 v2 o1 o2 e1 e2 c1 c2 :

    closed_exp e1 ->
    well_scoped e1 ->
    (max_var e1 1 < state.next_var c1)%positive ->

    occurs_free e2 \subset [set x] ->
    well_scoped e2 ->
    (max_var e2 1 < state.next_var c2)%positive ->

    exists (e1' e2' : exp) (c1' c2' : state.comp_data),
      anf_pipeline v1 o1 e1 c1 = (Ret e1', c1') /\
      anf_pipeline v2 o2 e2 c2 = (Ret e2', c2') /\

      refines cenv value_ref_cc (link lf x e1 e2) (link lf x e1' e2').
  Proof.
    intros.
    edestruct anf_pipeline_correct with (e := e1) (opts := o1); eauto. destructAll.
    edestruct anf_pipeline_correct with (e := e2) (opts := o2); eauto. destructAll.

    do 4 eexists.

    split. eassumption.
    split. eassumption.

    eapply R_n_exp_in_refines.

    6:{ eapply Rel_exp_n_preserves_linking; eauto.
        - intros. eapply H13.
        - eapply simple_bound_compat. }

    now eauto.
    clear; now firstorder.
    clear; now firstorder.
    eapply simple_bound_post_upper_bound.

    eapply link_closed; eauto.
  Qed.


End Compose.

(* Print Assumptions anf_pipeline_whole_program_correct. *)
(* Print Assumptions anf_pipeline_linking_correct. *)

(*

Prints :

Axioms:
ProofIrrelevance.proof_irrelevance : forall (P : Prop) (p1 p2 : P), p1 = p2
FunctionalExtensionality.functional_extensionality_dep : forall (A : Type) (B : A -> Type)
                                                           (f g : forall x : A, B x),
                                                         (forall x : A, f x = g x) -> f = g
*)
