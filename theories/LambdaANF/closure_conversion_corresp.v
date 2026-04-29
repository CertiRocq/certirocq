(* Correspondence of the computational definition and the declarative
   spec for closure conversion. Part of the CertiRocq project.  *)

Require Import LambdaANF.closure_conversion LambdaANF.closure_conversion_util.
From CertiRocq.LambdaANF Require Import term term_util set_util identifiers ctx Ensembles_util
     List_util functions logical_relations eval state.
Require Import compcert.lib.Coqlib.
From Stdlib Require Import ZArith.Znumtheory Relations.Relations Arith.Wf_nat.
From Stdlib Require Import Lists.List MSets.MSets MSets.MSetRBT Numbers.BinNums
               NArith.BinNat PArith.BinPos Sets.Ensembles micromega.Lia.
Require Import ExtLib.Structures.Monads ExtLib.Data.Monads.StateMonad.
Require Import MetaRocq.Utils.bytestring.
Import Common.compM.
Import ListNotations.

Open Scope ctx_scope.
Open Scope fun_scope.

(** * Correspondence of the relational and the computational definitions of closure conversion *)

Section CC_correct.

  Variable (clo_tag : ctor_tag).
  Variable (pr : prims).
  Variable (cenv : ctor_env).

  (** Free variable map invariant *)
  Definition FVmap_inv (FVmap : VarInfoMap) Scope Funs GFuns FVs : Prop :=
    Same_set _ Scope (fun x => M.get x FVmap = Some BoundVar) /\
    Same_set _ (Setminus _ Funs Scope)
             (fun x => exists x', M.get x FVmap = Some (MRFun x')) /\
    forall N x, (nthN FVs N = Some x /\ ~ In _ Scope x /\ ~ In _ Funs x /\ ~ In _ GFuns x) <->
           (M.get x FVmap = Some (FVar N)).

  (** Global function map invariant: gfuns agrees with GFuns *)
  Definition gfuns_inv (gfuns : GFunMap) GFuns : Prop :=
    GFuns <--> (fun x => M.get x gfuns = Some GFun).

  (** Map function name to environment *)
  Definition to_env (FVmap : VarInfoMap) x : var :=
    match M.get x FVmap with
      | Some (MRFun x') => x'
      | _ => x
    end.

  (** A function that corresponds to an evaluation context *)
  Definition is_exp_ctx (f : exp -> exp) C : Prop :=
    forall e, f e = app_ctx_f C e.

  (** Set of variables not in the map *)
  Definition binding_not_in_map {A} (S : Ensemble M.elt) (map : M.t A) :=
    forall x : M.elt, In M.elt S x -> M.get x map = None.


  (* TODO move to state *)
  Lemma get_named_str_fresh
     : forall (A : Type) (S : Ensemble var) (str : string),
       {{fun (_ : unit) (s : comp_data * A) => fresh S (next_var (fst s))}} get_named_str str
       {{fun (_ : unit) (s : comp_data * A) (x : var) (s' : comp_data * A) =>
         In var S x /\
         In var (Range (next_var (fst s)) (next_var (fst s'))) x /\
         (next_var (fst s) < next_var (fst s'))%positive /\ fresh (S \\ [set x]) (next_var (fst s'))}}.
  Proof.
    intros.
    eapply pre_post_mp_l.
    eapply bind_triple. now eapply get_triple.
    intros [[] w1] [[] w2].
    eapply pre_post_mp_l.
    eapply bind_triple. now eapply put_triple.
    intros x [r3 w3].
    eapply return_triple.
    intros ? [r4 w4] H2. inv H2. intros [H1 H2]. inv H1; inv H2. intros.
    split. eapply H. reflexivity. split. unfold Range, Ensembles.In. simpl. zify. lia.
    simpl. split. zify; lia.
    intros z Hin. constructor. eapply H; eauto. simpl. zify. lia.
    intros Hc. inv Hc. zify; lia.
  Qed.

  Lemma FVmap_inv_set_bound FVmap Scope Funs GFuns FVs x :
    FVmap_inv FVmap Scope Funs GFuns FVs ->
    FVmap_inv (M.set x BoundVar FVmap) (Union _ (Singleton _ x) Scope) Funs GFuns FVs.
  Proof.
    intros [H1 [H2 H3]]. repeat split.
    - intros y Hin. destruct (peq y x); subst.
      + unfold In. now rewrite M.gss.
      + inv Hin. inv H; congruence.
        eapply H1 in H. edestruct H.
        unfold In. rewrite M.gso; now eauto.
    - intros y Hin. destruct (peq y x); subst.
      + eauto.
      + unfold In in Hin. rewrite M.gso in Hin; [| now eauto ].
        right. eapply H1. eauto.
    - intros y Hin. inv Hin. destruct (peq y x); subst.
      + exfalso. eauto.
      + edestruct H2 as [H2' _].
        edestruct H2' as [x' Heq].
        * constructor; eauto.
        * eexists. rewrite M.gso; eauto.
    - eapply H2. destruct H as [x' Heq].
      destruct (peq x x0); subst.
      + rewrite M.gss in Heq. congruence.
      + repeat eexists. rewrite M.gso in Heq; eauto.
    - intros Hc. destruct H as [x' Heq].
      destruct (peq x0 x); subst.
      + rewrite M.gss in Heq. congruence.
      + inv Hc. inv H; congruence.
        eapply H2; eauto. repeat eexists.
        rewrite M.gso in Heq; eauto.
    - intros [Hnth [Hnin1 [Hnin2 Hnin3]]].
      destruct (peq x0 x); subst.
      + exfalso. eauto.
      + edestruct H3 as [Heq _].
        rewrite M.gso; eauto. eapply Heq; repeat split; eauto.
    - destruct (peq x0 x); subst.
      + rewrite M.gss in H. congruence.
      + eapply H3; eauto.
        rewrite M.gso in H; eauto.
    - destruct (peq x0 x); subst.
      + rewrite M.gss in H. congruence.
      + intros Hc. inv Hc. inv H0; congruence.
        rewrite M.gso in H; eauto.
        edestruct H3 as [_ [_ [Hc _]]].
        eapply H3 in H0; eauto. contradiction.
    - destruct (peq x0 x); subst.
      + rewrite M.gss in H. congruence.
      + intros Hc.
        rewrite M.gso in H; eauto.
        edestruct H3 as [_ [_ [_ [Hc' _]]]].
        eapply H3 in Hc; eauto. contradiction.
    - destruct (peq x0 x); subst.
      + rewrite M.gss in H. congruence.
      + intros Hc.
        rewrite M.gso in H; eauto.
        edestruct H3 as [_ [_ [_ [_ Hc']]]].
        eapply H3 in Hc; eauto. contradiction.
  Qed.

  Lemma FVmap_inv_set_funs FVmap Scope Funs GFuns FVs x x' :
    ~ In _ Scope x ->
    FVmap_inv FVmap Scope Funs GFuns FVs ->
    FVmap_inv (M.set x (MRFun x') FVmap) Scope (Union _ (Singleton _ x) Funs) GFuns FVs.
  Proof.
    intros Hnin [H1 [H2 H3]]. repeat split.
    - intros y Hin. destruct (peq y x); subst.
      + contradiction.
      + eapply H1 in Hin. edestruct Hin.
        unfold In. rewrite M.gso; eauto.
    - intros y Hin. destruct (peq y x); subst.
      + unfold In in Hin. rewrite M.gss in Hin; congruence.
      + unfold In in Hin. rewrite M.gso in Hin; [| now eauto ].
        now eapply H1.
    - intros y Hin. inv Hin. destruct (peq y x); subst.
      + repeat eexists. rewrite M.gss. reflexivity.
      + edestruct H2 as [H2' _].
        edestruct H2' as [x'' Heq].
        inv H. inv H4; congruence. constructor; eassumption.
        repeat eexists. rewrite M.gso; eassumption.
    - destruct (peq x0 x); subst; eauto. right.
      eapply H2. edestruct H as [x'' Hget].
      rewrite M.gso in Hget; [| now eauto ].
      repeat eexists; eauto.
    - destruct H as [x'' Hget].
      destruct (peq x0 x); subst; eauto.
      rewrite M.gso in Hget; [| now eauto ].
      intros Hc. apply H1 in Hc. congruence.
    - intros [Hnth [Hnin1 [Hnin2 Hnin3]]].
      destruct (peq x0 x); subst.
      + exfalso. eauto.
      + edestruct H3 as [Heq _].
        rewrite M.gso; eauto. eapply Heq; repeat split; eauto.
    - destruct (peq x0 x); subst.
      + rewrite M.gss in H. congruence.
      + eapply H3; eauto. rewrite M.gso in H; eauto.
    - destruct (peq x0 x); subst.
      + rewrite M.gss in H. congruence.
      + intros Hc. rewrite M.gso in H; eauto.
        eapply H1 in Hc. congruence.
    - destruct (peq x0 x); subst.
      + rewrite M.gss in H. congruence.
      + intros Hc. rewrite M.gso in H; eauto.
        inv Hc. inv H0; congruence.
        edestruct H2 as [H2' _].  edestruct (H2' x0) as [y Hge'].
        constructor. eauto. intros Hc. eapply H1 in Hc.
        congruence. congruence.
    - destruct (peq x0 x); subst.
      + rewrite M.gss in H. congruence.
      + rewrite M.gso in H; eauto.
        rewrite <- H3 in H; easy.
  Qed.

  Ltac splits := repeat match goal with |- _ /\ _ => split end.

  Lemma make_record_ctor_tag_preserves_prop n P :
    {{ fun _ s => P (next_var (fst s)) }}
      make_record_ctor_tag n
    {{ fun _ s _ (s' : comp_data * unit) => P (next_var (fst s')) /\ next_var (fst s') = next_var (fst s) }}.
  Proof.
    eapply pre_post_mp_l. eapply bind_triple. eapply get_triple.
    intros [[x1 c1 f1 e1 m1] []] [[x2 c2 f2 e2 m2] []].
    apply pre_post_mp_l. eapply bind_triple. now apply put_triple.
    intros [] s. eapply return_triple. intros _ s'. intros <-. intros [H1 H2]; subst. inv H1.
    intros; split; eauto.
  Qed.

  (* TODO: move to Ensembles_util *)
  Lemma Disjoint_sym {A} S1 S2 : Disjoint A S1 S2 -> Disjoint A S2 S1.
  Proof. eauto with Ensembles_DB. Qed.

  Lemma Disjoint_Union {A} S1 S2 S3 :
    Disjoint A S1 (S2 :|: S3) -> Disjoint A S1 S2 /\ Disjoint A S1 S3.
  Proof. eauto with Ensembles_DB. Qed.

  Ltac solve_Union_Inc :=
    repeat match goal with |- _ :|: _ \subset _ => apply Union_Included end; eauto with Ensembles_DB.
  Ltac decomp_Disjoint :=
    repeat match goal with
    | H : Disjoint _ _ (_ :|: _) |- _ => apply Disjoint_Union in H; destruct H
    | H : Disjoint _ (_ :|: _) _ |- _ => apply Disjoint_sym in H
    end.
  Ltac splits_Disjoint :=
    repeat match goal with
    | |- Disjoint _ _ (_ :|: _) => apply Union_Disjoint_r
    | |- Disjoint _ (_ :|: _) _ => apply Union_Disjoint_l
    end.

  (** Spec for [get_var] *)
  Lemma get_var_project_var_sound Scope Funs GFuns gfuns c Γ FVs FVmap S x :
    (* Disjoint _ GFuns (FromList FVs) ->*)
    [set x] \subset Scope :|: Funs :|: GFuns :|: FromList FVs ->
    (* binding_not_in_map (Union _ S (Singleton _ Γ)) FVmap -> *)
    FVmap_inv FVmap Scope Funs GFuns FVs ->
    gfuns_inv gfuns GFuns ->
    {{ fun _ s => fresh S (next_var (fst s)) }}
      get_var clo_tag x FVmap gfuns c Γ
    {{ fun _ s t s' =>
         exists C S',
           (let '(x', f) := t in
           project_var clo_tag Scope Funs GFuns c (to_env FVmap) Γ FVs S x x' C S' /\
           is_exp_ctx f C /\ unique_bindings_c C) /\
           fresh S' (next_var (fst s')) /\
           bound_var_ctx C \subset Range (next_var (fst s)) (next_var (fst s')) /\
           (next_var (fst s') >= next_var (fst s))%positive
    }}.
  Proof.
    intros Hin Minv Hgfuns. destruct Minv as [Minv1 [Minv2 Minv3]].
    unfold get_var.
    destruct (FVmap ! x) as [[] |] eqn:Hx.
    - eapply bind_triple.
      + eapply get_name_spec.
      + intros x' s. eapply return_triple. intros _ s' [Hx' [Hrange [Hf Hf']]].
        eexists (Eproj_c x' _ n Γ Hole_c).
        edestruct Minv3 as [H1 [H2 [H3 [H4 H5]]]]. now repeat eexists; eauto.
        eexists; splits. econstructor 4.
        all: auto.
        { unfold is_exp_ctx; reflexivity. }
        { repeat constructor. inversion 1. }
        { intros arb; repeat normalize_bound_var_ctx; normalize_sets.
          intros Harb; inv Harb. unfold In, Range in *; zify; lia. }
        { zify; lia. }
    - eapply bind_triple.
      + eapply get_name_spec.
      + intros x' s. eapply return_triple. intros _ s' [Hx' [Hrange [Hf Hf']]].
        edestruct Minv2 as [H1 H2]; eauto.
        exists (Econstr_c x' clo_tag [x; v] Hole_c). eexists; splits.
        { replace v with (to_env FVmap x) by (unfold to_env; now rewrite Hx).
          specialize (H2 x); unfold In, Setminus in H2; destruct H2 as [HFuns HScope]; [now exists v|].
          econstructor 2; auto. }
        { unfold is_exp_ctx; reflexivity. }
        { repeat constructor; inversion 1. }
        { auto. }
        { intros arb; repeat normalize_bound_var_ctx; normalize_sets.
          intros Harb; inv Harb. unfold In, Range in *; zify; lia. }
        { zify; lia. }
    - eapply return_triple. intros _ [s d] Hin'.
      exists Hole_c. eexists; splits.
      { constructor; eapply Minv1. eauto. }
      { unfold is_exp_ctx; reflexivity. }
      { constructor. }
      { auto. }
      { intros arb; repeat normalize_bound_var_ctx. intros Harb; inv Harb. }
      { zify; lia. }
    - assert (HScope : ~ x \in Scope). {
        intros Hc; apply Minv1 in Hc; congruence. }
      assert (HFuns : ~ x \in Funs). {
        intros Hc. edestruct (proj1 Minv2) as [x' Hx'].
        constructor; eassumption.
        congruence. }
      destruct (gfuns ! x) as [[] |] eqn:Hx_gfuns.
      + eapply bind_triple'.
        { eapply pre_strenghtening.
          2: eapply post_weakening.
          3: apply make_record_ctor_tag_preserves_prop with (P := fun x => fresh S x).
          { auto. }
          { simpl. intros ? ? ? ? Hfresh [? Heq]; exact (conj Hfresh Heq). } }
        intros c_env s_c_env.
        apply pre_curry_l; intros HS_c_env.
        eapply bind_triple'.
        { eapply pre_strenghtening.
          { intros st s H; rewrite <- H in HS_c_env. exact (conj H HS_c_env). }
          apply frame_rule, get_name_spec. }
        intros y s_y.
        apply pre_curry_l; intros HS_s_y.
        apply pre_curry_l; intros HS_y.
        eapply bind_triple'.
        { eapply pre_strenghtening.
          { intros st s H; pose (H' := H); clearbody H'; destruct H' as [? [? Hres]]; exact (conj H Hres). }
          apply frame_rule, get_name_spec. }
        intros g_env s_g_env.
        apply return_triple.
        intros _ s_final [[Hran_y [Hinc_y Hfresh_y]] [HS_g_env [Hran_g_env [Hinc_g_env Hfresh_g_env]]]].
        exists (Econstr_c g_env c_env [] (Econstr_c y clo_tag [x; g_env] Hole_c)); eexists; splits; eauto.
        * apply Var_in_GFuns; auto.
          apply Hgfuns. apply Hx_gfuns.
        * unfold is_exp_ctx; reflexivity.
        * constructor; [|constructor; [|constructor]];
            change (~ ?S ?x) with (~ x \in S) in *; normalize_bound_var_ctx;
              eauto with Ensembles_DB.
          rewrite Union_demorgan; split; try normalize_bound_var_ctx; eauto with Ensembles_DB.
          intros Hc; inv Hc; unfold In, Range in *; zify; lia.
        * repeat normalize_bound_var_ctx; normalize_sets; solve_Union_Inc.
          -- eapply Included_trans; [apply Singleton_Included, Hran_y|].
             intros arb Harb; unfold Range, In in *; zify; lia.
          -- eapply Included_trans; [apply Singleton_Included, Hran_g_env|].
             intros arb Harb; unfold Range, In in *; zify; lia.
        * unfold Range, In in *; zify; lia.
      + specialize (Hin x (In_singleton _ x)).
        rewrite !In_or_Iff_Union in Hin.
        assert (HGFuns : ~ x \in GFuns). {
          intros Hc; apply Hgfuns in Hc; congruence. }
        assert (HFVs : ~ x \in FromList FVs). {
          intros Hc.
          apply In_nthN in Hc; destruct Hc as [n Hc].
          specialize (Minv3 n x); destruct Minv3 as [Minv3 _].
          specialize (Minv3 (conj Hc (conj HScope (conj HFuns HGFuns)))).
          congruence. }
        firstorder.
  Qed.

  (* TODO: move to compM *)
  Lemma pre_post_mp_l' {R W} {A} (P : @Pre R W) (Q : @Post R W A) e :
    {{ fun r w => P r w }} e {{ fun r w x w' => P r w -> Q r w x w' }} ->
    {{ fun r w => P r w }} e {{ fun r w x w' => Q r w x w' }}.
  Proof.
    intros H.
    eapply post_weakening; [| eapply pre_strenghtening; [| eassumption ] ];
    simpl; eauto.
  Qed.
  Lemma pre_post_mp_l_inv' {R W} {A} (P P' : @Pre R W) (Q : @Post R W A) e :
    (forall r w, P r w -> P' r w) ->
    {{ fun r w => P r w }} e {{ fun r w x w' => Q r w x w' }} ->
    {{ fun r w => P r w }} e {{ fun r w x w' => P' r w -> Q r w x w' }}.
  Proof.
    intros H Hpre.
    eapply post_weakening; [| eapply pre_strenghtening; [| eassumption ] ];
    simpl; eauto.
  Qed.

  Lemma bind_triple' {R W A B} (m : compM R W A) (f : A -> compM R W B)
        (P : Pre) (Q : Post B) (Q' : Post A) :
    {{ P }} m {{ Q' }} ->
    (forall (x : A) w, {{ fun r w' => P r w /\ Q' r w x w' }} f x {{ fun r _ x' w' => Q r w x' w' }}) ->
    {{ P }} bind m f {{ Q }}.
  Proof.
    simpl. unfold triple; simpl.
    intros H1 H2 r w HP.

    (* pose (Hm := H1 st s HP). *)
    destruct m as [fm].
    unfold runState in *; simpl in *.
    destruct (fm r w) eqn:Heq_fm, e; auto.
    specialize (H1 r w HP). rewrite Heq_fm in H1. eassumption.
    specialize (H1 r w HP). rewrite Heq_fm in H1.
    eapply H2. split; eassumption.
  Qed.

  Fixpoint unique_bindings_c_comp C D {struct C} :
    unique_bindings_c C ->
    unique_bindings_c D ->
    Disjoint _ (bound_var_ctx C) (bound_var_ctx D) ->
    unique_bindings_c (ctx.comp_ctx_f C D)
  with unique_bindings_fundefs_c_comp C D {struct C} :
    unique_bindings_fundefs_c C ->
    unique_bindings_c D ->
    Disjoint _ (bound_var_fundefs_ctx C) (bound_var_ctx D) ->
    unique_bindings_fundefs_c (ctx.comp_f_ctx_f C D).
  Proof.
    all: intros HC HD Hdis; destruct C; simpl; inv HC; normalize_bound_var_ctx_in_ctx;
      repeat match goal with
      | H : Disjoint _ (_ :|: _) _ |- _ => apply Disjoint_sym in H
      | H : Disjoint _ _ (_ :|: _) |- _ => apply Disjoint_Union in H; destruct H
      end.
    - apply HD.
    - constructor; change (~ ?S ?x) with (~ x \in S) in *.
      + rewrite (proj1 bound_var_ctx_comp_ctx).
        intros Hc; destruct Hc; auto.
        destruct H0 as [Hdis]; now contradiction (Hdis x).
      + apply unique_bindings_c_comp; try assumption. now apply Disjoint_sym.
    - constructor; change (~ ?S ?x) with (~ x \in S) in *.
      + rewrite (proj1 bound_var_ctx_comp_ctx).
        intros Hc; destruct Hc; auto.
        destruct H0 as [Hdis]; now contradiction (Hdis x).
      + apply unique_bindings_c_comp; try assumption. now apply Disjoint_sym.
    - constructor; change (~ ?S ?x) with (~ x \in S) in *.
      + rewrite (proj1 bound_var_ctx_comp_ctx).
        intros Hc; destruct Hc; auto.
        destruct H0 as [Hdis]; now contradiction (Hdis x).
      + apply unique_bindings_c_comp; try assumption. now apply Disjoint_sym.
    - constructor; change (~ ?S ?x) with (~ x \in S) in *.
      + rewrite (proj1 bound_var_ctx_comp_ctx).
        intros Hc; destruct Hc; auto.
        destruct H0 as [Hdis]; now contradiction (Hdis x).
      + apply unique_bindings_c_comp; try assumption. now apply Disjoint_sym.
    - constructor; change (~ ?S ?x) with (~ x \in S) in *.
      + rewrite (proj1 bound_var_ctx_comp_ctx).
        intros Hc; destruct Hc; auto.
        destruct H0 as [Hdis]; now contradiction (Hdis x).
      + apply unique_bindings_c_comp; try assumption. now apply Disjoint_sym.
    - constructor; try assumption.
      + apply unique_bindings_c_comp; try assumption.
        now apply Disjoint_sym.
      + rewrite (proj1 bound_var_ctx_comp_ctx); apply Union_Disjoint_l; try assumption.
        normalize_bound_var; apply Union_Disjoint_r; assumption.
    - constructor; change (~ ?S ?x) with (~ x \in S) in *; try assumption.
      + apply unique_bindings_c_comp; try assumption. now apply Disjoint_sym.
      + rewrite (proj1 bound_var_ctx_comp_ctx).
        apply Union_Disjoint_l; assumption.
    - constructor; change (~ ?S ?x) with (~ x \in S) in *; try assumption.
      + apply unique_bindings_fundefs_c_comp; try assumption. now apply Disjoint_sym.
      + rewrite (proj2 bound_var_ctx_comp_ctx).
        apply Union_Disjoint_r; try assumption.
        apply Disjoint_sym; assumption.
    - constructor; change (~ ?S ?x) with (~ x \in S) in *; try assumption.
      + rewrite (proj1 bound_var_ctx_comp_ctx). intros Hc; destruct Hc; auto.
        destruct H as [Hdis]; now contradiction (Hdis x).
      + rewrite (proj1 bound_var_ctx_comp_ctx); apply Union_Disjoint_l; assumption.
      + rewrite (proj1 bound_var_ctx_comp_ctx); apply Union_Disjoint_l; assumption.
      + apply unique_bindings_c_comp; try assumption. now apply Disjoint_sym.
    - constructor; change (~ ?S ?x) with (~ x \in S) in *; try assumption.
      + rewrite (proj2 bound_var_ctx_comp_ctx). intros Hc; destruct Hc; auto.
        destruct H as [Hdis]; now contradiction (Hdis x).
      + rewrite (proj2 bound_var_ctx_comp_ctx); apply Union_Disjoint_l; assumption.
      + rewrite (proj2 bound_var_ctx_comp_ctx); apply Union_Disjoint_r; try assumption.
        now apply Disjoint_sym.
      + apply unique_bindings_fundefs_c_comp; try assumption. now apply Disjoint_sym.
  Qed.

  Fixpoint unique_bindings_c_comp_inv C D {struct C} :
    unique_bindings_c (ctx.comp_ctx_f C D) ->
    unique_bindings_c C /\
    unique_bindings_c D /\
    Disjoint _ (bound_var_ctx C) (bound_var_ctx D)
  with unique_bindings_fundefs_c_comp_inv C D {struct C} :
    unique_bindings_fundefs_c (ctx.comp_f_ctx_f C D) ->
    unique_bindings_fundefs_c C /\
    unique_bindings_c D /\
    Disjoint _ (bound_var_fundefs_ctx C) (bound_var_ctx D).
  Proof.
    all: destruct C; simpl; intros Huniq.
    - splits; try solve [constructor|assumption]. constructor; intros x Hx; now inv Hx.
    - inv Huniq; splits.
      + constructor; change (~ ?S ?x) with (~ x \in S) in *.
        * intros Hc; contradiction H1; normalize_bound_var_ctx; now left.
        * clear unique_bindings_fundefs_c_comp_inv; specialize (unique_bindings_c_comp_inv _ _ H4); intuition.
      + clear unique_bindings_fundefs_c_comp_inv; specialize (unique_bindings_c_comp_inv _ _ H4); intuition.
      + clear unique_bindings_fundefs_c_comp_inv; specialize (unique_bindings_c_comp_inv _ _ H4).
        destruct unique_bindings_c_comp_inv as [HuniqC [HuniqD Hdis]].
        normalize_bound_var_ctx; apply Union_Disjoint_l; auto.
        constructor; intros x Hx; inv Hx. inv H.
        contradiction H1. change (?S ?x) with (x \in S). normalize_bound_var_ctx.
        now right.
    - inv Huniq; splits.
      + constructor; change (~ ?S ?x) with (~ x \in S) in *.
        * intros Hc; contradiction H1; normalize_bound_var_ctx; now left.
        * clear unique_bindings_fundefs_c_comp_inv; specialize (unique_bindings_c_comp_inv _ _ H5); intuition.
      + clear unique_bindings_fundefs_c_comp_inv; specialize (unique_bindings_c_comp_inv _ _ H5); intuition.
      + clear unique_bindings_fundefs_c_comp_inv; specialize (unique_bindings_c_comp_inv _ _ H5).
        destruct unique_bindings_c_comp_inv as [HuniqC [HuniqD Hdis]].
        normalize_bound_var_ctx; apply Union_Disjoint_l; auto.
        constructor; intros x Hx; inv Hx. inv H.
        contradiction H1. change (?S ?x) with (x \in S). normalize_bound_var_ctx.
        now right.
    - inv Huniq; splits.
      + constructor; change (~ ?S ?x) with (~ x \in S) in *.
        * intros Hc; contradiction H1; normalize_bound_var_ctx; now left.
        * clear unique_bindings_fundefs_c_comp_inv; specialize (unique_bindings_c_comp_inv _ _ H3); intuition.
      + clear unique_bindings_fundefs_c_comp_inv; specialize (unique_bindings_c_comp_inv _ _ H3); intuition.
      + clear unique_bindings_fundefs_c_comp_inv; specialize (unique_bindings_c_comp_inv _ _ H3).
        destruct unique_bindings_c_comp_inv as [HuniqC [HuniqD Hdis]].
        normalize_bound_var_ctx; apply Union_Disjoint_l; auto.
        constructor; intros x Hx; inv Hx. inv H.
        contradiction H1. change (?S ?x) with (x \in S). normalize_bound_var_ctx.
        now right.
    - inv Huniq; splits.
      + constructor; change (~ ?S ?x) with (~ x \in S) in *.
        * intros Hc; contradiction H1; normalize_bound_var_ctx; now left.
        * clear unique_bindings_fundefs_c_comp_inv; specialize (unique_bindings_c_comp_inv _ _ H4); intuition.
      + clear unique_bindings_fundefs_c_comp_inv; specialize (unique_bindings_c_comp_inv _ _ H4); intuition.
      + clear unique_bindings_fundefs_c_comp_inv; specialize (unique_bindings_c_comp_inv _ _ H4).
        destruct unique_bindings_c_comp_inv as [HuniqC [HuniqD Hdis]].
        normalize_bound_var_ctx; apply Union_Disjoint_l; auto.
        constructor; intros x Hx; inv Hx. inv H.
        contradiction H1. change (?S ?x) with (x \in S). normalize_bound_var_ctx.
        now right.
    - inv Huniq; splits.
      + constructor; change (~ ?S ?x) with (~ x \in S) in *.
        * intros Hc; contradiction H1; normalize_bound_var_ctx; now left.
        * clear unique_bindings_fundefs_c_comp_inv; specialize (unique_bindings_c_comp_inv _ _ H5); intuition.
      + clear unique_bindings_fundefs_c_comp_inv; specialize (unique_bindings_c_comp_inv _ _ H5); intuition.
      + clear unique_bindings_fundefs_c_comp_inv; specialize (unique_bindings_c_comp_inv _ _ H5).
        destruct unique_bindings_c_comp_inv as [HuniqC [HuniqD Hdis]].
        normalize_bound_var_ctx; apply Union_Disjoint_l; auto.
        constructor; intros x Hx; inv Hx. inv H.
        contradiction H1. change (?S ?x) with (x \in S). normalize_bound_var_ctx.
        now right.
    - inv Huniq; splits.
      + constructor; change (~ ?S ?x) with (~ x \in S) in *.
        * assumption.
        * clear unique_bindings_fundefs_c_comp_inv; specialize (unique_bindings_c_comp_inv _ _ H5); intuition.
        * eapply Disjoint_Included_l; [|eassumption]. normalize_bound_var_ctx; eauto with Ensembles_DB.
      + clear unique_bindings_fundefs_c_comp_inv; specialize (unique_bindings_c_comp_inv _ _ H5); intuition.
      + normalize_bound_var_ctx. eapply Union_Disjoint_l; [|apply Union_Disjoint_l].
        * apply Disjoint_sym; eapply Disjoint_Included_l; [|eapply Disjoint_Included_r; [|eassumption]].
          -- normalize_bound_var_ctx; now right.
          -- rewrite bound_var_Ecase_app; now left.
        * clear unique_bindings_fundefs_c_comp_inv; specialize (unique_bindings_c_comp_inv _ _ H5); intuition.
        * apply Disjoint_sym; eapply Disjoint_Included_l; [|eapply Disjoint_Included_r; [|eassumption]].
          -- normalize_bound_var_ctx; now right.
          -- rewrite bound_var_Ecase_app; now right.
    - inv Huniq; splits.
      + constructor; change (~ ?S ?x) with (~ x \in S) in *.
        * clear unique_bindings_fundefs_c_comp_inv; specialize (unique_bindings_c_comp_inv _ _ H1); intuition.
        * assumption.
        * eapply Disjoint_Included_l; [|eassumption]. normalize_bound_var_ctx; eauto with Ensembles_DB.
      + clear unique_bindings_fundefs_c_comp_inv; specialize (unique_bindings_c_comp_inv _ _ H1); intuition.
      + normalize_bound_var_ctx. eapply Union_Disjoint_l.
        * apply Disjoint_sym; eapply Disjoint_Included_l; [|eassumption].
          normalize_bound_var_ctx; eauto with Ensembles_DB.
        * clear unique_bindings_fundefs_c_comp_inv; specialize (unique_bindings_c_comp_inv _ _ H1); intuition.
    - inv Huniq; splits.
      + constructor; change (~ ?S ?x) with (~ x \in S) in *.
        * clear unique_bindings_c_comp_inv; specialize (unique_bindings_fundefs_c_comp_inv _ _ H2); intuition.
        * clear unique_bindings_c_comp_inv; specialize (unique_bindings_fundefs_c_comp_inv _ _ H2); intuition.
        * eapply Disjoint_Included_r; [|eassumption].
          rewrite (proj2 bound_var_ctx_comp_ctx); eauto with Ensembles_DB.
      + clear unique_bindings_c_comp_inv; specialize (unique_bindings_fundefs_c_comp_inv _ _ H2); intuition.
      + normalize_bound_var_ctx. eapply Union_Disjoint_l.
        * clear unique_bindings_c_comp_inv; specialize (unique_bindings_fundefs_c_comp_inv _ _ H2); intuition.
        * eapply Disjoint_Included_r; [|eassumption].
          rewrite (proj2 bound_var_ctx_comp_ctx); eauto with Ensembles_DB.
    - inv Huniq; splits.
      + constructor; change (~ ?S ?x) with (~ x \in S) in *; auto.
        * intros Hc; contradiction H4; normalize_bound_var_ctx. now left.
        * eapply Disjoint_Included_l; [|apply H6].
          normalize_bound_var_ctx; eauto with Ensembles_DB.
        * eapply Disjoint_Included_l; [|apply H8].
          normalize_bound_var_ctx; eauto with Ensembles_DB.
        * clear unique_bindings_fundefs_c_comp_inv; specialize (unique_bindings_c_comp_inv _ _ H11); intuition.
      + clear unique_bindings_fundefs_c_comp_inv; specialize (unique_bindings_c_comp_inv _ _ H11); intuition.
      + normalize_bound_var_ctx. apply Union_Disjoint_l; [|apply Union_Disjoint_l; [|apply Union_Disjoint_l]].
        * constructor; intros x Hx; inv Hx. inv H.
          change (~ ?S ?x) with (~ x \in S) in *; contradiction H4.
          normalize_bound_var_ctx; now right.
        * apply Disjoint_sym. eapply Disjoint_Included_l; [|apply H6].
          normalize_bound_var_ctx; eauto with Ensembles_DB.
        * clear unique_bindings_fundefs_c_comp_inv; specialize (unique_bindings_c_comp_inv _ _ H11); intuition.
        * apply Disjoint_sym. eapply Disjoint_Included_l; [|apply H8].
          normalize_bound_var_ctx; eauto with Ensembles_DB.
    - inv Huniq; splits.
      + constructor; change (~ ?S ?x) with (~ x \in S) in *; auto.
        * intros Hc; contradiction H5.
          rewrite (proj2 bound_var_ctx_comp_ctx); eauto with Ensembles_DB.
        * eapply Disjoint_Included_l; [|apply H7].
          rewrite (proj2 bound_var_ctx_comp_ctx); eauto with Ensembles_DB.
        * eapply Disjoint_Included_r; [|apply H8].
          rewrite (proj2 bound_var_ctx_comp_ctx); eauto with Ensembles_DB.
        * clear unique_bindings_c_comp_inv; specialize (unique_bindings_fundefs_c_comp_inv _ _ H12); intuition.
      + clear unique_bindings_c_comp_inv; specialize (unique_bindings_fundefs_c_comp_inv _ _ H12); intuition.
      + normalize_bound_var_ctx. apply Union_Disjoint_l; [|apply Union_Disjoint_l; [|apply Union_Disjoint_l]].
        * constructor; intros x Hx; inv Hx. inv H.
          change (~ ?S ?x) with (~ x \in S) in *; contradiction H5.
          rewrite (proj2 bound_var_ctx_comp_ctx); now right.
        * apply Disjoint_sym. eapply Disjoint_Included_l; [|apply H7].
          rewrite (proj2 bound_var_ctx_comp_ctx); now right.
        * eapply Disjoint_Included_r; [|apply H8].
          rewrite (proj2 bound_var_ctx_comp_ctx); now right.
        * clear unique_bindings_c_comp_inv; specialize (unique_bindings_fundefs_c_comp_inv _ _ H12); intuition.
  Qed.

  (** Spec for [get_vars] *)
  Lemma get_vars_project_vars_sound' Scope Funs GFuns gfuns c Γ FVs FVmap S xs S_pre s_pre :
    FromList xs \subset Scope :|: Funs :|: GFuns :|: FromList FVs ->
    FVmap_inv FVmap Scope Funs GFuns FVs ->
    gfuns_inv gfuns GFuns ->
    {{ fun _ s => fresh S (next_var (fst s)) /\ S_pre \subset Range s_pre (next_var (fst s))
               /\ (next_var (fst s) >= s_pre)%positive }}
      get_vars clo_tag xs FVmap gfuns c Γ
    {{ fun _ s t s' =>
         exists C S',
           (let '(xs', f) := t in
           project_vars clo_tag Scope Funs GFuns c (to_env FVmap) Γ FVs S xs xs' C S' /\
           is_exp_ctx f C /\
           unique_bindings_c C) /\
           fresh S' (next_var (fst s')) /\
           bound_var_ctx C \subset Range (next_var (fst s)) (next_var (fst s')) /\
           (next_var (fst s') >= next_var (fst s))%positive }}.
  Proof.
    intros Hb Hfv Hgfuns.
    revert S S_pre s_pre Hb Hfv Hgfuns. induction xs; intros S S_pre s_pre Hb Hfv Hgfuns.
    - eapply return_triple. intros _ s [Hf _].
      eexists Hole_c. eexists; splits.
      + constructor.
      + unfold is_exp_ctx; reflexivity. + constructor.
      + auto.
      + intros x; inversion 1.
      + zify; lia.
    - eapply bind_triple.
      + eapply pre_strenghtening; [|eapply get_var_project_var_sound; eauto].
        { simpl; intros ? ? [Hleft ?]; exact Hleft. }
        intros x Hin. eapply Hb.
        inv Hin. constructor. eauto.
      + intros [x f] s1.
        eapply pre_existential. intros C.
        eapply pre_existential. intros S'.
        eapply pre_curry_l. intros [Hproj [Hctx Huniq]].
        apply pre_post_mp_l'.
        eapply bind_triple.
        eapply (IHxs S'); eauto.
        { intros y Hin. eapply Hb. constructor 2. eassumption. }
        intros [xs' f'] s2. eapply return_triple.
        intros _ s [C' [S'' [[Hproj' [Hctx' Huniq']] [Hf' [Hran' Hinc']]]]] [Hf [Hran Hinc]].
        exists (comp_ctx_f C C'), S''; splits; auto.
        * econstructor; eauto.
        * unfold is_exp_ctx; intros e.
          now rewrite Hctx, Hctx', app_ctx_f_fuse.
        * apply unique_bindings_c_comp; auto.
          eapply Disjoint_Included_l; [apply Hran|].
          eapply Disjoint_Included_r; [apply Hran'|].
          constructor; intros arb Harb; inv Harb; unfold In, Range in *; zify; lia.
        * normalize_bound_var_ctx.
          apply Union_Included; eapply Included_trans; try eassumption.
          all: intros arb Harb; unfold Range, In in *; zify; lia.
        * zify; lia.
  Qed.

  Corollary get_vars_project_vars_sound Scope Funs GFuns gfuns c Γ FVs FVmap S xs :
    FromList xs \subset Scope :|: Funs :|: GFuns :|: FromList FVs ->
    FVmap_inv FVmap Scope Funs GFuns FVs ->
    gfuns_inv gfuns GFuns ->
    {{ fun _ s => fresh S (next_var (fst s)) }}
      get_vars clo_tag xs FVmap gfuns c Γ
    {{ fun _ s t s' =>
         exists C S',
           (let '(xs', f) := t in
           project_vars clo_tag Scope Funs GFuns c (to_env FVmap) Γ FVs S xs xs' C S' /\
           is_exp_ctx f C /\
           unique_bindings_c C) /\
           fresh S' (next_var (fst s')) /\
           bound_var_ctx C \subset Range (next_var (fst s)) (next_var (fst s')) /\
           (next_var (fst s') >= next_var (fst s))%positive }}.
  Proof.
    intros Hb Hfv Hgfuns.
    eapply pre_strenghtening.
    2: apply get_vars_project_vars_sound' with (S_pre := Empty_set _) (s_pre := 1%positive); auto.
    intros st s Hfresh; split; auto; split; eauto with Ensembles_DB; zify; lia.
  Qed.

  Lemma to_env_BoundVar_f_eq_subdomain FVmap x S :
    f_eq_subdomain S ((to_env FVmap) {x ~> x}) (to_env (M.set x BoundVar FVmap)).
  Proof.
    intros x'. unfold to_env, extend. rewrite M.gsspec.
    destruct (peq x' x). now eauto. reflexivity.
  Qed.

  Lemma to_env_BoundVar_f_eq FVmap x :
    f_eq ((to_env FVmap) {x ~> x}) (to_env (M.set x BoundVar FVmap)).
  Proof.
    intros x'. unfold to_env, extend. rewrite M.gsspec.
    destruct (peq x' x). now eauto. reflexivity.
  Qed.

  Lemma Disjoint_free_set FVmap Scope Funs GFuns FVs S :
    binding_not_in_map S FVmap ->
    Disjoint _ GFuns S ->
    FVmap_inv FVmap Scope Funs GFuns FVs ->
    Disjoint _ S (Union var Scope
                        (Union var Funs (FromList FVs))).
  Proof.
    intros Hb Hdis [Hinv1 [Hinv2 Hinv3]].
    constructor. intros x Hc. inv Hc.
    assert (Hdec1 : Decidable Scope).
    { eapply Decidable_Same_set. apply Same_set_sym. eassumption.
      constructor. intros x'. destruct (M.get x' FVmap).
      - destruct v; eauto;
        right; intros; congruence.
      - right. intros; congruence. }
    assert (Hdec2 : Decidable (Setminus _ Funs Scope)).
    { eapply Decidable_Same_set. apply Same_set_sym. eassumption.
      constructor. intros x'. destruct (M.get x' FVmap).
      - destruct v; eauto;
        right; intros [y Hc]; congruence.
      - right. intros [y Hc]; congruence. }
    destruct Hdec1, Hdec2. destruct (Dec x) as [Hin | Hnin].
    - eapply Hinv1 in Hin.
      unfold In in Hin. rewrite Hb in Hin; eauto. congruence.
    - destruct (Dec0 x) as [Hin' | Hnin'].
      + eapply Hinv2 in Hin'. destruct Hin' as [y Heq].
        rewrite Hb in Heq; eauto. congruence.
      + unfold binding_not_in_map in Hb.
        inv H0; try contradiction.
        inv H1. now eapply Hnin'; constructor; eauto.
        unfold In, FromList in H0.
        edestruct In_nthN as [N Hnth]; [ eassumption |].
        destruct (Hinv3 N x) as [Hinv3' _].
        rewrite Hb in Hinv3'; [| eassumption ].
        assert (H3 : ~ Funs x) by (intros Hc; eapply Hnin'; constructor; eauto).
        assert (Hgfuns : ~ GFuns x). {
          intros Hc; destruct Hdis as [Hdis]; specialize (Hdis x).
          apply Hdis; now constructor. }
        specialize (Hinv3' (conj Hnth (conj Hnin (conj H3 Hgfuns)))). congruence.
  Qed.

  Lemma binding_not_in_map_antimon (A : Type) (S S' : Ensemble M.elt) (rho : M.t A):
    Included M.elt S' S -> binding_not_in_map S rho -> binding_not_in_map S' rho.
  Proof.
    intros Hin Hb x Hin'. eauto.
  Qed.

  Lemma binding_not_in_map_set_not_In_S {A} S map x (v : A) :
    binding_not_in_map S map ->
    ~ In _ S x ->
    binding_not_in_map S (M.set x v map).
  Proof.
    intros HB Hnin x' Hin.
    rewrite M.gsspec. destruct (peq x' x); subst; try contradiction.
    eauto.
  Qed.

  Import MonadNotation.

  Transparent bind ret.

  (** This identity is very useful to make the computation of the IH to appear
      as a subcomputation in the goal *)
  Lemma st_eq_Ecase {S} m1 (m2 : @compM' S (var * (exp -> exp))) y :
    st_eq
      (ys <- m1 ;;
       ys' <- ret (y :: ys) ;;
       t1 <- m2 ;;
       let '(x, f) := t1 in
       ret (Ecase x ys', f))
      (fe <- (ys <- m1 ;;
             t1 <- m2 ;;
             let '(x, f1) := t1 in
             ret (Ecase x ys, f1)) ;;
       match fe with
         | (Ecase x ys, f) =>
           ret (Ecase x (y :: ys), f)
         | _ => ret fe
       end).
  Proof.
    unfold bind, ret.
    intros r s. simpl. destruct (runState m1 r s).
    destruct e; simpl; auto.
    destruct (runState m2 r p).
    destruct e; simpl; auto.
    destruct p1 as [x f]; simpl; auto.
  Qed.

  Global Opaque bind ret.

  Global Instance FVmap_inv_Scope_Proper :
    Proper (Logic.eq ==> Same_set var ==> Logic.eq ==> Logic.eq ==> Logic.eq ==> iff) FVmap_inv.
  Proof.
    intros M1 M2 Heq1 S1 S2 Heq2 S3 S4 Heq3 S5 S6 Heq6 l1 l2 Heq4; subst; split; intros [H1 [H2 H3]].
    - (split; [| split ]); try rewrite <- Heq2; eauto.
      split. intros [Hnth [Hnin1 [Hnin2 Hnin3]]]. eapply H3. repeat split; eauto.
      now rewrite Heq2.
      intros H. rewrite <- Heq2. eapply H3. eassumption.
    - (split; [| split ]); try rewrite Heq2; eauto.
      split. intros [Hnth [Hnin1 [Hnin2 Hnin3]]]. eapply H3. repeat split; eauto.
      now rewrite <- Heq2.
      intros H. rewrite Heq2. eapply H3. eassumption.
  Qed.

  Global Instance FVmap_inv_Funs_Proper :
    Proper (Logic.eq ==> Logic.eq ==> Same_set var ==> Logic.eq ==> Logic.eq ==> iff) FVmap_inv.
  Proof.
    intros M1 M2 Heq1 S1 S2 Heq2 S3 S4 Heq3 S5 S6 Heq6 l1 l2 Heq4; subst; split; intros [H1 [H2 H3]].
    - (split; [| split ]); try rewrite <- Heq3; eauto.
      split. intros [Hnth [Hnin1 [Hnin2 Hnin3]]]. eapply H3. repeat split; eauto.
      now rewrite Heq3.
      intros H. rewrite <- Heq3. eapply H3. eassumption.
    - (split; [| split ]); try rewrite Heq3; eauto.
      split. intros [Hnth [Hnin1 [Hnin2 Hnin3]]]. eapply H3. repeat split; eauto.
      now rewrite <- Heq3.
      intros H. rewrite Heq3. eapply H3. eassumption.
  Qed.

  Global Instance FVmap_inv_GFuns_Proper :
    Proper (Logic.eq ==> Logic.eq ==> Logic.eq ==> Same_set var ==> Logic.eq ==> iff) FVmap_inv.
  Proof.
    intros M1 M2 Heq1 S1 S2 Heq2 S3 S4 Heq3 S5 S6 Heq6 l1 l2 Heq4; subst; split; intros [H1 [H2 H3]].
    - unfold FVmap_inv; splits; auto.
      intros; rewrite <- Heq6; auto.
    - unfold FVmap_inv; splits; auto.
      intros; rewrite Heq6; auto.
  Qed.

  Lemma FVmapInv_add_params FVmap xs Scope Funs GFuns FVs :
    FVmap_inv FVmap Scope Funs GFuns FVs ->
    FVmap_inv (add_params xs FVmap) (Union _ Scope (FromList xs)) Funs GFuns FVs.
  Proof.
    revert FVmap Scope. induction xs; intros FVmap Scope Hinv.
    - rewrite FromList_nil, Union_Empty_set_neut_r. eauto.
    - rewrite FromList_cons.
      rewrite Union_assoc, Union_commut with (s2 := Singleton M.elt a), <- Union_assoc.
      eapply FVmap_inv_set_bound; eauto.
  Qed.

  Lemma binding_in_map_add_params S FVmap xs :
    binding_in_map S FVmap ->
    binding_in_map (Union _ S  (FromList xs)) (add_params xs FVmap).
  Proof.
    revert S FVmap. induction xs; intros S FVmap Hb.
    - intros x. rewrite FromList_nil, Union_Empty_set_neut_r. eauto.
    - intros x. rewrite FromList_cons.
      rewrite Union_commut with (s2 := FromList xs), Union_assoc.
      simpl. eapply binding_in_map_set; eauto.
  Qed.

  Lemma binding_not_in_map_add_params S FVmap xs :
    binding_not_in_map S FVmap ->
    Disjoint _ S (FromList xs) ->
    binding_not_in_map S (add_params xs FVmap).
  Proof.
    revert S FVmap. induction xs; intros S FVmap Hb Hd.
    - eauto.
    - rewrite FromList_cons in Hd.
      eapply binding_not_in_map_set_not_In_S; eauto.
      + eapply IHxs. eassumption.
        constructor. intros x Hc. inv Hc. eapply Hd. now constructor; eauto.
      + intros Hc. eapply Hd. eauto.
  Qed.

  Lemma FVmap_inv_empty GFuns :
    FVmap_inv (Maps.PTree.empty VarInfo) (Empty_set M.elt) (Empty_set M.elt) GFuns [].
  Proof.
    repeat split; (try now intros Hc; inv Hc); (try now intros x Hc; inv Hc).
    destruct H as [x' Hget]. rewrite M.gempty in Hget. now inv Hget.
    rewrite M.gempty in H. now inv H.
    rewrite M.gempty in H. now inv H.
  Qed.

  Lemma FVmap_inv_set_free_var FVmap Scope Funs GFuns FVs x n:
    FVmap_inv FVmap Scope Funs GFuns FVs ->
    N.of_nat (length FVs) = n ->
    ~ In _ Scope x -> ~ In  _ Funs x -> ~ In _ GFuns x -> ~ List.In x FVs ->
    FVmap_inv (Maps.PTree.set x (FVar n) FVmap) Scope Funs GFuns (FVs ++ [x]).
  Proof.
    intros [H1 [H2 H3]] Hlen Hnin1 Hnin2 Hnin3.
    split; [| split ].
    - split.
      + intros x' Hin. assert (Hin' := Hin). eapply H1 in Hin.
        destruct (peq x' x).
        subst; contradiction.
        unfold In. now rewrite M.gso; eauto.
      + intros x' Hget. eapply H1.
        unfold In in Hget. rewrite M.gsspec in Hget. destruct (peq x' x).
        subst; congruence. now eauto.
    - split.
      + intros x' Hin. assert (Hin' := Hin). inv Hin'.
        eapply H2 in Hin. edestruct Hin as [y Heq].
        destruct (peq x' x).
        subst; contradiction.
        eexists. rewrite M.gso; eauto.
      + intros x' [y Hget]. eapply H2.
        rewrite M.gsspec in Hget. destruct (peq x' x).
        subst; congruence.
        now eauto.
    - intros N x'. split.
      + intros [Hnth [Hnin1' [Hnin2' Hnin3']]].
        destruct (nthN_app FVs [x] N) as [Hn | [Hn Hlen']].
        * destruct (peq x' x); subst.
          exfalso. eapply H. eapply nthN_In. rewrite <- Hnth. now eauto.
          edestruct H3 as [Hget _].
          rewrite M.gso; eauto. eapply Hget. repeat split; eauto.
          rewrite <- Hnth. now eauto.
        * subst. rewrite Hnth in Hn. eapply nthN_is_Some_length in Hnth.
          rewrite length_app in Hnth. simpl length in *.
          destruct (N - N.of_nat (length FVs))%N eqn:Heq; simpl in Hn; try congruence.
          inv Hn. rewrite M.gss; eauto.
          repeat f_equal. zify. lia.
      + subst. intros Hget.
        rewrite M.gsspec in Hget. destruct (peq x' x).
        * subst. inv Hget. repeat split; eauto.
          rewrite nthN_app_geq. rewrite N.sub_diag. reflexivity.
          zify; lia.
        * edestruct H3 as [_ [H1' [H2' [H3' H4']]]].
          eassumption.
          repeat split; eauto. apply nthN_is_Some_app. eassumption.
  Qed.

  Lemma make_env_spec fv FVmap_o c Γ_n Γ_o Scope Funs GFuns gfuns FVs S :
    (* binding_in_map (FromList fv) FVmap_o -> *)
    FromList fv \subset Scope :|: Funs :|: GFuns :|: FromList FVs ->
    binding_not_in_map (Union M.elt S (Singleton M.elt Γ_o)) FVmap_o ->
    FVmap_inv FVmap_o Scope Funs GFuns FVs ->
    gfuns_inv gfuns GFuns ->
    Disjoint _ GFuns (FromList fv) ->
    NoDup fv ->
    ~ Γ_n \in S ->
    {{ fun _ s => fresh S (next_var (fst s)) }}
      make_env clo_tag fv (Maps.PTree.empty VarInfo) FVmap_o c Γ_n Γ_o gfuns
    {{ fun _ s t  s' =>
         let '(c', FVmap_n, f) := t in
         exists C S' FVs',
           ((forall x, to_env FVmap_n x = x) /\
           project_vars clo_tag Scope Funs GFuns c (to_env FVmap_o) Γ_o FVs S fv FVs' C S' /\
           is_exp_ctx f (comp_ctx_f C (Econstr_c Γ_n c' FVs' Hole_c)) /\
           unique_bindings_c (comp_ctx_f C (Econstr_c Γ_n c' FVs' Hole_c))) /\
           bound_var_ctx C \subset Range (next_var (fst s)) (next_var (fst s')) /\
           fresh S' (next_var (fst s')) /\
           (next_var (fst s') >= next_var (fst s))%positive /\
           binding_in_map (FromList fv) FVmap_n /\
           binding_not_in_map (Complement _ (FromList fv)) FVmap_n /\
           FVmap_inv FVmap_n (Empty_set _) (Empty_set _) GFuns fv
     }}.
  Proof.
    intros Hb1 Hb2 Minv Hgfuns Hdis Hdup Hnin. unfold make_env.
    destruct ((fix
                 add_fvs (l : list M.elt) (n : N) (map : Maps.PTree.tree VarInfo)
                 {struct l} : Maps.PTree.tree VarInfo * N :=
                 match l with
                   | [] => (map, n)
                   | x :: xs => add_fvs xs (n + 1)%N (PTree.set x (FVar n) map)
                 end)
                fv 0%N (Maps.PTree.empty VarInfo)) as [map_new n] eqn:Heq.
    apply pre_post_mp_l'. eapply bind_triple.
    - eapply get_vars_project_vars_sound; eauto.
    - intros [xs f] s1.
      eapply pre_existential. intros C1. eapply pre_existential. intros S'.
      eapply pre_curry_l. intros [Hvars [Hctx Huniq]].
      eapply bind_triple.
      apply make_record_ctor_tag_preserves_prop with (n := n)
        (P := fun x => fresh S' x /\
          bound_var_ctx C1 \subset Range (next_var (fst s1)) x /\
          (x >= next_var (fst s1))%positive).
      intros tau s2. eapply return_triple.
      intros _ s3 [[Hf [Hran Hinc]] Hst_eq] Hfresh.
      do 3 eexists. split; [splits|split; [|split; [|split]]]; try eassumption.
      + clear - Heq.
        assert (Hnin : forall x, to_env (PTree.empty VarInfo) x = x) by (intros; unfold to_env; now rewrite M.gempty).
        remember (PTree.empty VarInfo) as map_old eqn:Hold; clear Hold.
        remember 0%N as n_init eqn:Hold; clear Hold.
        generalize dependent map_old. revert n_init.
        induction fv as [|fv fvs IHfvs]; intros n_init map_old Hmap_eq Hnin.
        * now inv Hmap_eq.
        * simpl in *.
          specialize (IHfvs (n_init + 1)%N _ Hmap_eq).
          apply IHfvs; intros x.
          unfold to_env.
          destruct (peq fv x); [subst; now rewrite M.gss|rewrite M.gso by auto].
          rewrite <- Hnin; unfold to_env; reflexivity.
      + intros e. rewrite Hctx. rewrite <- app_ctx_f_fuse. now f_equal.
      + apply unique_bindings_c_comp; auto.
        { repeat constructor; inversion 1. }
        repeat normalize_bound_var_ctx; normalize_sets.
        constructor; intros arb Harb; inv Harb. inv H0.
        contradiction Hnin.
        apply Hran in H.
        apply Hfresh.
        unfold In, Range in *; zify; lia.
      + replace map_new with
        (fst ((fix
                add_fvs (l : list M.elt) (n : N)
                (map : Maps.PTree.tree VarInfo) {struct l} :
                Maps.PTree.tree VarInfo * N :=
                match l with
                  | [] => (map, n)
                  | x :: xs => add_fvs xs (n + 1)%N (Maps.PTree.set x (FVar n) map)
                end) fv 0%N (Maps.PTree.empty VarInfo)))
          by (rewrite Heq; eauto).
        clear - Hdis Hdup.
        assert (He : FVmap_inv (Maps.PTree.empty VarInfo)
                               (Empty_set M.elt) (Empty_set M.elt) GFuns [])
          by apply FVmap_inv_empty.
        assert (Hb : binding_in_map (FromList (@nil PS.elt)) (Maps.PTree.empty VarInfo))
          by (intros x H; inv H).
        assert (Hb' : binding_not_in_map (Complement _ (FromList ((@nil PS.elt))))
                                         (Maps.PTree.empty VarInfo))
          by (intros x H; rewrite Maps.PTree.gempty; reflexivity).
        assert (Hlen : N.of_nat (@length PS.elt []) = 0%N) by eauto.
        assert (Hnin : forall x, List.In x fv -> ~ List.In x [])
          by (intros x H1 H2; inv H2).
        replace fv with ([] ++ fv) at 1 3 6 by reflexivity.
        revert Hlen He Hb Hb' Hnin Hdis Hdup. generalize (Maps.PTree.empty VarInfo) as FVmap_i.
        unfold PS.elt, map_util.M.elt in *.
        generalize (@nil positive). generalize 0%N.
        induction fv as [|v fv IHfv]; intros n vars FVmap_i Hlen Hinv Hb Hb' Hnin Hdis Hdup.
        * simpl. rewrite app_nil_r. eauto.
        * simpl. replace (vars ++ v :: fv) with ((vars ++ [v]) ++ fv). simpl.
          eapply IHfv. rewrite length_app. simpl. zify. lia.
          eapply FVmap_inv_set_free_var. now eauto. eassumption.
          now intros Hc; inv Hc. now intros Hc; inv Hc.
          { normalize_sets. apply Disjoint_sym, Disjoint_Union_l in Hdis.
            intros Hc; destruct Hdis as [Hdis]; now contradiction (Hdis v). }
          { eapply Hnin. constructor. reflexivity. }
          { intros x H. eapply binding_in_map_set. eassumption.
            rewrite FromList_app, FromList_cons, FromList_nil, Union_Empty_set_neut_r in H.
            eassumption. }
          { eapply binding_not_in_map_set_not_In_S.
            eapply binding_not_in_map_antimon; [| eassumption ].
            eapply Complement_antimon. rewrite FromList_app. now apply Included_Union_l.
            intros Hc. eapply Hc.
            rewrite FromList_app, FromList_cons, FromList_nil. now eauto. }
          { intros x Hin Hc. eapply Hnin.
            - now constructor 2; eauto.
            - inv Hdup. apply Coqlib.in_app in Hc. inv Hc; eauto. inv H.
              exfalso. eapply H1. eauto. now inv H0. }
          { normalize_sets.
            now apply Disjoint_sym, Disjoint_Union_r, Disjoint_sym in Hdis. }
          { now inv Hdup. }
          { now rewrite <- app_assoc. }
  Qed.

  Lemma to_env_MRFun_f_eq (FVmap : VarInfoMap) (x x' : var) :
    f_eq ((to_env FVmap) {x ~> x'}) (to_env (M.set x (MRFun x') FVmap)).
  Proof.
    unfold to_env. intros y. unfold extend.
    rewrite M.gsspec. destruct (peq y x); eauto.
  Qed.

  Global Instance extend_fundefs'_Proper S :
    Proper (f_eq_subdomain S ==> eq ==> eq ==> f_eq_subdomain S) extend_fundefs'.
  Proof.
    intros σ σ' Hσ B B' HB Γ Γ' HΓ; unfold extend_fundefs'; intros g Hg; subst;
      destruct (Dec g) as [Hin|Hnin]; auto.
  Qed.

  Lemma extend_fundefs'_eq_subdomain S σ σ' B Γ :
    f_eq_subdomain S σ σ' ->
    f_eq_subdomain (name_in_fundefs B :|: S) (extend_fundefs' σ B Γ) (extend_fundefs' σ' B Γ).
  Proof.
    unfold extend_fundefs'; intros Hσ g Hg.
    destruct (Dec g) as [Hin|Hnin]; auto.
    rewrite Hσ; auto.
    now destruct Hg.
  Qed.

  Lemma add_closures_spec B FVmap Γ :
    f_eq_subdomain (fun _ => True) (to_env (add_closures B FVmap Γ)) (extend_fundefs' (to_env FVmap) B Γ).
  Proof.
    induction B as [f ft xs e B IHB|].
    - intros x _; simpl. unfold to_env at 1.
      destruct (Pos.eq_dec f x) as [Heq|Hne]; subst; [rewrite M.gss|rewrite M.gso by auto].
      + unfold extend_fundefs'. destruct (@Dec _ (name_in_fundefs _) _ x) as [Hin|Hnin]; auto.
        contradiction Hnin; now left.
      + unfold f_eq_subdomain, to_env at 1 in IHB. rewrite IHB by auto. unfold extend_fundefs'.
        destruct (@Dec _ (name_in_fundefs B) _ x) as [HinB|HninB];
        destruct (@Dec _ (name_in_fundefs _) _ x) as [HinC|HninC]; auto.
        * contradiction HninC; now right.
        * contradiction Hne; inv HinC; [now inv H|easy].
    - intros x _; simpl; unfold extend_fundefs'.
      destruct (@Dec _ (name_in_fundefs Fnil) _ x) as [Hin|]; [inv Hin|]; auto.
  Qed.

  Lemma FVmap_inv_add_closures_open B :
    forall FVmap FVmap' Scope Funs GFuns FVs Γ
    (Hmap : FVmap_inv FVmap Scope Funs GFuns FVs)
    (Heq : FVmap' = add_closures B FVmap Γ),
    FVmap_inv (add_closures B FVmap Γ)
              (Scope \\ name_in_fundefs B)
              (name_in_fundefs B :|: Funs) GFuns FVs.
  Proof.
    induction B as [f ft xs e B IHB|]; intros.
    - simpl in *.
      specialize (IHB FVmap _ _ _ _ _ Γ Hmap eq_refl).
      destruct Hmap as [HFuns [HScope Hfree]].
      destruct IHB as [IHFuns [IHScope IHfree]].
      unfold FVmap_inv; splits.
      + rewrite Union_commut.
        rewrite <- Setminus_Union.
        rewrite IHFuns.
        rewrite Ensemble_iff_In_iff; intros arb.
        rewrite not_In_Setminus.
        unfold In; split; intros Harb.
        * destruct Harb as [Hget Hne'].
          assert (Hne : f <> arb) by (intros Hc; subst; now apply Hne').
          now rewrite M.gso by auto.
        * destruct (Pos.eq_dec f arb); [subst|]; [rewrite M.gss in Harb|rewrite M.gso in Harb by auto].
          1: now inv Harb.
          split; [auto|now intros Hc; inv Hc].
      + split; intros arb Harb.
        * unfold In. inv Harb.
          rewrite <- Union_assoc in H.
          destruct (Pos.eq_dec f arb); [subst; rewrite M.gss; now eexists|rewrite M.gso by auto].
          apply IHScope; constructor.
          -- inv H; auto. now inv H1.
          -- intros Hc; inv Hc. contradiction H0; constructor; auto.
             intros Hc; inv Hc; auto. now inv H3.
        * unfold In in Harb.
          destruct (Pos.eq_dec f arb); [subst; rewrite M.gss in Harb|rewrite M.gso in Harb by auto].
          -- destruct Harb as [? Harb]; inv Harb. constructor; [now do 2 left|].
             intros Hc; inv Hc; contradiction H0; now left.
          -- apply IHScope in Harb. inv Harb.
             constructor. rewrite <- Union_assoc. now right.
             intros Hc; inv Hc. contradiction H0. constructor; auto.
      + intros N x; split.
        * intros [Hnth [HnScope [HnFuns HnGFuns]]].
          assert (Hne : f <> x) by (intros Hc; subst; contradiction HnFuns; now do 2 left).
          rewrite M.gso by auto.
          apply IHfree; splits; auto.
          -- intros Hc; inv Hc. contradiction HnScope; constructor; auto.
          -- intros Hc; contradiction HnFuns; rewrite <- Union_assoc; auto.
        * destruct (Pos.eq_dec f x); [subst; now rewrite M.gss|rewrite M.gso by auto].
          intros Hget. apply IHfree in Hget. destruct Hget as [Hnth [HnScope [HnFuns HnGFuns]]].
          splits; auto.
          -- intros Hc; inv Hc. contradiction HnScope; constructor; auto.
          -- rewrite <- Union_assoc. intros Hc; inv Hc.
             ++ now inv H.
             ++ contradiction HnFuns; auto.
    - simpl in *; subst.
      now repeat normalize_sets.
  Qed.

  Lemma add_closures_not_in B FVmap Γ x :
    ~ x \in name_in_fundefs B ->
    (add_closures B FVmap Γ) ! x = FVmap ! x.
  Proof.
    induction B as [f ft xs e B IHB|]; intros.
    - simpl in *.
      destruct (peq f x); [subst|]; [rewrite M.gss|rewrite M.gso by auto; auto].
      contradiction H; now left.
    - reflexivity.
  Qed.

  Lemma FVmap_inv_add_closures_closed B :
    forall FVmap FVmap' Scope Funs GFuns GFuns' FVs Γ
    (Hmap : FVmap_inv FVmap Scope Funs GFuns FVs)
    (Heq : FVmap' = add_closures B FVmap Γ)
    (Hclos : GFuns' <--> GFuns :|: name_in_fundefs B),
    FVmap_inv (add_closures B FVmap Γ)
              (Scope \\ name_in_fundefs B)
              (name_in_fundefs B :|: Funs) GFuns' FVs.
  Proof.
    induction B as [f ft xs e B IHB|]; intros.
    - simpl in *.
      specialize (IHB FVmap _ _ _ _ (GFuns :|: name_in_fundefs B) _ Γ Hmap eq_refl (Same_set_refl _ _)).
      destruct Hmap as [HFuns [HScope Hfree]].
      destruct IHB as [IHFuns [IHScope IHfree]].
      unfold FVmap_inv; splits.
      + rewrite Union_commut.
        rewrite <- Setminus_Union.
        rewrite IHFuns.
        rewrite Ensemble_iff_In_iff; intros arb.
        rewrite not_In_Setminus.
        unfold In; split; intros Harb.
        * destruct Harb as [Hget Hne'].
          assert (Hne : f <> arb) by (intros Hc; subst; now apply Hne').
          now rewrite M.gso by auto.
        * destruct (Pos.eq_dec f arb); [subst|]; [rewrite M.gss in Harb|rewrite M.gso in Harb by auto].
          1: now inv Harb.
          split; [auto|now intros Hc; inv Hc].
      + split; intros arb Harb.
        * unfold In. inv Harb.
          rewrite <- Union_assoc in H.
          destruct (Pos.eq_dec f arb); [subst; rewrite M.gss; now eexists|rewrite M.gso by auto].
          apply IHScope; constructor.
          -- inv H; auto. now inv H1.
          -- intros Hc; inv Hc. contradiction H0; constructor; auto.
             intros Hc; inv Hc; auto. now inv H3.
        * unfold In in Harb.
          destruct (Pos.eq_dec f arb); [subst; rewrite M.gss in Harb|rewrite M.gso in Harb by auto].
          -- destruct Harb as [? Harb]; inv Harb. constructor; [now do 2 left|].
             intros Hc; inv Hc; contradiction H0; now left.
          -- apply IHScope in Harb. inv Harb.
             constructor. rewrite <- Union_assoc. now right.
             intros Hc; inv Hc. contradiction H0. constructor; auto.
      + intros N x; split.
        * intros [Hnth [HnScope [HnFuns HnGFuns]]].
          assert (Hne : f <> x) by (intros Hc; subst; contradiction HnFuns; now do 2 left).
          rewrite M.gso by auto.
          destruct (Decidable_name_in_fundefs B) as [Hdec], (Hdec x) as [Hin|Hnin].
          -- contradiction HnFuns; left; now right.
          -- rewrite add_closures_not_in by auto.
             apply Hfree; splits; auto.
             ++ intros Hc. contradiction HnScope; constructor; auto.
             ++ rewrite Hclos in HnGFuns; intros Hc; contradiction HnGFuns; now left.
        * destruct (Pos.eq_dec f x); [subst; now rewrite M.gss|rewrite M.gso by auto].
          intros Hget. apply IHfree in Hget. destruct Hget as [Hnth [HnScope [HnFuns HnGFuns]]].
          splits; auto.
          -- intros Hc; inv Hc. contradiction HnScope; constructor; auto.
          -- rewrite <- Union_assoc. intros Hc; inv Hc.
             ++ now inv H.
             ++ contradiction HnFuns; auto.
          -- rewrite Hclos; intros Hc; apply HnGFuns; inv Hc.
             { now left. }
             inv H.
             { now inv H0. }
             now right.
    - simpl in *; subst.
      repeat normalize_sets.
      unfold FVmap_inv in *; destruct Hmap as [H1 [H2 H3]]; splits; auto.
      intros N x; rewrite Hclos; auto.
  Qed.

  Lemma add_closures_gfuns_open B gfuns :
    add_closures_gfuns B gfuns false = gfuns.
  Proof. induction B as [f ft xs e B IHB|]; simpl in *; congruence. Qed.

  Lemma add_closures_gfuns_closed B gfuns Funs GFuns
        (HFuns : Funs <--> name_in_fundefs B)
        (HGFuns : gfuns_inv gfuns GFuns) :
    gfuns_inv (add_closures_gfuns B gfuns true) (Funs :|: GFuns).
  Proof.
    generalize dependent Funs; induction B as [f ft xs e B IHB|]; intros Funs HFuns.
    - simpl in *; unfold gfuns_inv in *.
      specialize IHB with (Funs := name_in_fundefs B).
      rewrite HFuns, <- Union_assoc, IHB by eauto with Ensembles_DB.
      split; intros x Hx.
      + inv Hx; unfold In in *; [inv H; now rewrite M.gss|].
        destruct (Pos.eq_dec f x); subst; [rewrite M.gss|rewrite M.gso by auto]; auto.
      + unfold In in *; destruct (Pos.eq_dec f x); subst;
          [rewrite M.gss in Hx|rewrite M.gso in Hx by auto]; [now left|now right].
    - unfold gfuns_inv. rewrite HFuns; simpl; normalize_sets; apply HGFuns.
  Qed.

  Inductive squash A : Prop := mk_squash : A -> squash A.
  Lemma add_closures_gfuns_spec B gfuns is_closed Funs FVs GFuns :
    reflect (FVs <--> Empty_set _) is_closed ->
    Funs <--> name_in_fundefs B ->
    Disjoint _ Funs GFuns ->
    gfuns_inv gfuns GFuns -> exists GFuns',
    (if is_closed then GFuns' <--> Funs :|: GFuns else GFuns' <--> GFuns \\ Funs) /\
    gfuns_inv (add_closures_gfuns B gfuns is_closed) GFuns' /\
    squash (add_global_funs GFuns Funs FVs GFuns').
  Proof.
    destruct is_closed.
    - intros Hclos HFuns Hdis Hgfuns.
      exists (Funs :|: GFuns); splits; eauto with Ensembles_DB.
      + now apply add_closures_gfuns_closed.
      + constructor; constructor. now inv Hclos.
    - intros Hclos HFuns Hdis Hgfuns; inv Hclos; exists (GFuns \\ Funs); splits; eauto with Ensembles_DB.
      + rewrite add_closures_gfuns_open.
        apply Disjoint_sym, Setminus_Disjoint in Hdis.
        unfold gfuns_inv. rewrite Hdis. apply Hgfuns.
      + constructor. now constructor.
  Qed.

  (* Rewrite does not exactly works for these two, but they are still useful as lemmas *)
  Global Instance project_var_Proper Scope Funs GFuns c :
    Proper
      (f_eq_subdomain (Funs \\ Scope) ==> eq ==> eq ==> eq ==> eq ==> eq ==> eq ==> eq ==> iff)
      (project_var clo_tag Scope Funs GFuns c).
  Proof.
    constructor; subst; intros Hproj; inv Hproj; try (now constructor; eauto).
    - rewrite H; now econstructor; eauto.
    - rewrite <- H; now econstructor; eauto.
  Qed.

  Global Instance project_vars_Proper Scope Funs GFuns c :
    Proper
      (f_eq_subdomain (Funs \\ Scope) ==> eq ==> eq ==> eq ==> eq ==> eq ==> eq ==> eq ==> iff)
      (project_vars clo_tag Scope Funs GFuns c).
  Proof.
      constructor; subst; intros Hproj; induction Hproj; try (now constructor; eauto).
      - econstructor. eapply project_var_Proper; eauto.
        now symmetry. now eauto.
      - econstructor. now eapply project_var_Proper; eauto. now eauto.
  Qed.

  Lemma Closure_conversion_f_eq_subdomain_mut :
    (forall e Scope Funs GFuns σ σ' c FVs Γ e' C
       (Hcc : Closure_conversion clo_tag Scope Funs GFuns c σ Γ FVs e e' C)
       (Hfeq : f_eq_subdomain (Setminus _ Funs Scope) σ σ'),
       Closure_conversion clo_tag Scope Funs GFuns c σ' Γ FVs e e' C) /\
    (forall B Funs GFuns c FVs B'
       (Hinc : Included _ (name_in_fundefs B) (name_in_fundefs Funs))
       (Hcc : Closure_conversion_fundefs clo_tag Funs GFuns c FVs B B'),
       Closure_conversion_fundefs clo_tag Funs GFuns c FVs B B').
  Proof with now eauto with Ensembles_DB.
    eapply exp_def_mutual_ind; intros; inv Hcc.
    - econstructor; try reflexivity.
      rewrite <- image_f_eq_subdomain; eassumption.
      eapply project_vars_Proper; [symmetry; eassumption |..]; try reflexivity. eassumption.
      eapply H. eassumption. eapply f_eq_subdomain_antimon; [| eassumption ]...
    - econstructor; try reflexivity. rewrite <- image_f_eq_subdomain; eassumption.
      eapply project_var_Proper; [symmetry; eassumption |..]; try reflexivity; eassumption.
      inv H12; constructor.
    - econstructor; try reflexivity. rewrite <- image_f_eq_subdomain; eassumption.
      eapply project_var_Proper; [symmetry; eassumption |..]; try reflexivity; eassumption.
      inv H14. inv H4. simpl in H1; subst. destruct H2 as [C' [e' [Heq Hcc]]].
      constructor. now split; eauto.
      assert (Hcc' : Closure_conversion clo_tag Scope Funs GFuns c0 σ' Γ FVs
                                        (Ecase v l)  (Ecase x' l') C).
      { eapply H0. econstructor; eauto. eassumption. }
      now inv Hcc'.
    - econstructor; try reflexivity. rewrite <- image_f_eq_subdomain; eassumption.
      eapply project_var_Proper; [symmetry; eassumption |..]; try reflexivity; eassumption.
      eapply H. eassumption. eapply f_eq_subdomain_antimon; [| eassumption ]...
    - rewrite image_f_eq_subdomain in H5 by eassumption.
      econstructor; try reflexivity. { eassumption. }
      { eapply project_vars_Proper; [symmetry; eassumption |..]; try reflexivity; eassumption. }
      { eassumption. } { eassumption. } { eassumption. }
      eapply H; eauto.
      eapply f_eq_subdomain_antimon; [| eassumption ]...
    - econstructor; try reflexivity; try eassumption.
      { rewrite <- image_f_eq_subdomain; eassumption. }
      { eapply project_vars_Proper; [symmetry; eassumption |..]; try reflexivity; eassumption. }
      { rewrite <- image_f_eq_subdomain by eassumption. eassumption. }
      { rewrite <- image_f_eq_subdomain by eassumption. eassumption. }
      { eapply H0; [eassumption|].
        eapply f_eq_subdomain_antimon; [|apply extend_fundefs'_eq_subdomain; eassumption].
        rewrite Union_commut.
        rewrite <- Union_Setminus_Setminus_Union; [|auto with Decidable_DB].
        eauto with Ensembles_DB. }
    - econstructor; try reflexivity.
      { rewrite <- image_f_eq_subdomain; eassumption. }
      { eapply project_vars_Proper; [symmetry; eassumption |..]; try reflexivity; eassumption. }
      { assumption. } { assumption. } { assumption. }
    - econstructor. rewrite <- image_f_eq_subdomain; eassumption.
      eapply H; eauto. eapply f_eq_subdomain_antimon; [|eassumption]...
    - econstructor. rewrite <- image_f_eq_subdomain; eassumption.
      { eapply project_vars_Proper; [symmetry; eassumption |..]; try reflexivity; eassumption. }
      eapply H; [eassumption|].
      eapply f_eq_subdomain_antimon; [|eassumption]...
    - econstructor. rewrite <- image_f_eq_subdomain; eassumption.
      eapply project_var_Proper; [symmetry; eassumption |..]; try reflexivity; eassumption.
    - econstructor; try eassumption.
    - constructor.
  Qed.

  Corollary Closure_conversion_f_eq_subdomain :
    forall e Scope Funs GFuns σ σ' c FVs Γ e' C
       (Hcc : Closure_conversion clo_tag Scope Funs GFuns c σ Γ FVs e e' C)
       (Hfeq : f_eq_subdomain (Setminus _ Funs Scope) σ σ'),
       Closure_conversion clo_tag Scope Funs GFuns c σ' Γ FVs e e' C.
  Proof.
    now apply Closure_conversion_f_eq_subdomain_mut.
  Qed.

  Corollary Closure_conversion_fundefs_f_eq_subdomain :
    forall B Funs GFuns c FVs B'
       (Hinc : Included _ (name_in_fundefs B) (name_in_fundefs Funs))
       (Hcc : Closure_conversion_fundefs clo_tag Funs GFuns c FVs B B'),
       Closure_conversion_fundefs clo_tag Funs GFuns c FVs B B'.
  Proof.
    now apply Closure_conversion_f_eq_subdomain_mut.
  Qed.

(*
  Lemma subst_add_params_f_eq_subdomain S l FVmap :
    Disjoint _ (FromList l) S ->
    f_eq_subdomain S
     (subst (add_params l FVmap)) (subst FVmap).
  Proof.
    intros Hd. induction l.
    - simpl. reflexivity.
    - simpl. rewrite <- subst_BoundVar_f_eq_subdomain.
      eapply f_eq_subdomain_extend_not_In_S_l.
      intros H. eapply Hd. constructor. rewrite FromList_cons.
      now left. eassumption.
      eapply IHl. eapply Disjoint_Included_l; [| eassumption ].
      rewrite FromList_cons. now apply Included_Union_r.
  Qed.

  Hint Resolve image_Setminus_extend : functions_BD.
 *)

  (* TODO: move to compM *)
  Lemma pre_curry_rr {R W A} (P1 P2 : @Pre R W) (Q : Post A) (P' : Prop) e :
    (P' -> {{ fun st s => P1 st s /\ P2 st s }} e {{ Q }}) ->
    {{ fun st s => P1 st s /\ P2 st s /\ P' }} e {{ Q }}.
  Proof.
    intros Hyp st s [Hpre HP]. eapply Hyp; tauto.
  Qed.

  Lemma pre_curry_rrr {R W A} (P1 P2 P3 : @Pre R W) (Q : Post A) (P' : Prop) e :
    (P' -> {{ fun st s => P1 st s /\ P2 st s /\ P3 st s }} e {{ Q }}) ->
    {{ fun st s => P1 st s /\ P2 st s /\ P3 st s /\ P' }} e {{ Q }}.
  Proof.
    intros Hyp st s [Hpre HP]. eapply Hyp; tauto.
  Qed.

  Lemma pre_curry_rrrr {R W A} (P1 P2 P3 P4 : @Pre R W) (Q : Post A) (P' : Prop) e :
    (P' -> {{ fun st s => P1 st s /\ P2 st s /\ P3 st s /\ P4 st s }} e {{ Q }}) ->
    {{ fun st s => P1 st s /\ P2 st s /\ P3 st s /\ P4 st s /\ P' }} e {{ Q }}.
  Proof.
    intros Hyp st s [Hpre HP]. eapply Hyp; tauto.
  Qed.


  Lemma pre_curry_rl {R W A} (P1 P2 : @Pre R W) (Q : Post A) (P' : Prop) e :
    (P' -> {{ fun st s => P1 st s /\ P2 st s }} e {{ Q }}) ->
    {{ fun st s => P1 st s /\ P' /\ P2 st s }} e {{ Q }}.
  Proof.
    intros Hyp st s [Hpre HP]. eapply Hyp; tauto.
  Qed.

  Lemma pre_and_swap {R W A} (P1 P2 : @Pre R W) (Q : Post A) e :
    {{ fun st s => P2 st s /\ P1 st s }} e {{ Q }} ->
    {{ fun st s => P1 st s /\ P2 st s }} e {{ Q }}.
  Proof.
    intros Hyp st s [Hpre HP]. eapply Hyp; tauto.
  Qed.

  Lemma pre_existential_r {R W A B} (P1 : @Pre R W) (P2 : B -> @Pre R W) (Q : Post A) e :
    (forall b, {{ fun st s => P1 st s /\ P2 b st s }} e {{ Q }}) ->
    {{ fun st s => P1 st s /\ exists b, P2 b st s }} e {{ Q }}.
  Proof.
    intros Hyp st s [Hpre HP]. destruct HP; eapply Hyp; eauto.
  Qed.

  (* move to proper file *)
  Lemma fresh_inc S x y : (y >= x)%positive -> fresh S x -> fresh S y.
  Proof. unfold fresh, In; intros Hyx Hx; intros; apply Hx; zify; lia. Qed.

  Lemma fundefs_append_used_vars : forall B1 B2 B3,
    fundefs_append B1 B2 = B3 ->
    used_vars_fundefs B3 <--> used_vars_fundefs B1 :|: used_vars_fundefs B2.
  Proof.
    induction B1 as [f ft xs e B1 IHB1|]; intros B2 B3 Happ.
    - simpl in *. subst B3. normalize_used_vars. rewrite IHB1 by reflexivity.
      normalize_used_vars. eauto with Ensembles_DB.
    - subst. simpl; normalize_used_vars; normalize_sets. eauto with Ensembles_DB.
  Qed.

  Lemma filter_NoDup A f (xs : list A) : NoDup xs -> NoDup (filter f xs).
  Proof.
    induction xs as [|x xs IHxs]; [constructor|intros Hdup; inv Hdup; simpl].
    destruct (f x); auto; constructor; auto.
    intros Hin. apply filter_In in Hin. now destruct Hin.
  Qed.

  Lemma filter_sub A f (xs : list A) : FromList (filter f xs) \subset FromList xs.
  Proof.
    intros x Hx; unfold In, FromList in *.
    now apply filter_In in Hx.
  Qed.

  Lemma filter_setminus gfuns GFuns fvs :
    gfuns_inv gfuns GFuns ->
    FromList (filter (fun x => match gfuns ! x with Some _ => false | None => true end) fvs) <-->
    FromList fvs \\ GFuns.
  Proof.
    intros Hgfuns.
    split; intros x Hx.
    - constructor.
      + eapply filter_sub; eauto.
      + intros Hc.
        apply filter_In in Hx.
        destruct Hx as [_ Hget].
        unfold gfuns_inv in Hgfuns.
        destruct Hgfuns as [Hlr Hrl].
        specialize (Hlr x); specialize (Hrl x).
        specialize (Hlr Hc).
        now rewrite Hlr in Hget.
    - inv Hx. rename H into Hin, H0 into Hnin.
      unfold gfuns_inv in Hgfuns.
      assert (Hnone : gfuns ! x = None). {
        destruct Hgfuns as [Hlr Hrl].
        specialize (Hlr x); specialize (Hrl x).
        unfold In in *.
        destruct (gfuns ! x); [|reflexivity].
        destruct g. contradiction Hnin. now apply Hrl. }
      unfold FromList, In.
      rewrite filter_In; split; [|now rewrite Hnone].
      apply Hin.
  Qed.

  Lemma Disjoint_Complement : forall (A : Type) (S1 S2 : Ensemble A),
    Disjoint A S1 S2 ->
    S1 \subset Complement A S2.
  Proof.
    intros A S1 S2 Hdis x Hin1 Hin2; destruct Hdis as [Hdis]; contradiction (Hdis x).
    now constructor.
  Qed.

  Lemma add_params_irrelevant S xs FVmap :
    Disjoint _ S (FromList xs) ->
    f_eq_subdomain S (to_env (add_params xs FVmap)) (to_env FVmap).
  Proof.
    induction xs as [|x xs IHxs]; intros Hdis x' HS; [auto|].
    simpl. unfold to_env.
    destruct (peq x x') as [Heq|Hne]; [subst; rewrite M.gss|rewrite M.gso by auto].
    - destruct Hdis as [Hdis]; contradiction (Hdis x'); constructor; auto; now left.
    - unfold f_eq_subdomain, to_env in IHxs.
      rewrite IHxs; auto.
      eapply Disjoint_Included_r; [|eassumption].
      normalize_sets; eauto with Ensembles_DB.
  Qed.

  Lemma FV_preserves_disjoint_inv S_used S FVmap Scope Funs GFuns FVs Γ :
    FVmap_inv FVmap Scope Funs GFuns FVs ->
    binding_not_in_map (S :|: [set Γ]) FVmap ->
    Disjoint _ S (Funs \\ Scope :|: GFuns :|: S_used :|: [set Γ]
                       :|: image (to_env FVmap) (Funs \\ Scope)) ->
    Disjoint _ S (Scope :|: (Funs \\ Scope) :|: GFuns
                        :|: image (to_env FVmap) (Funs \\ Scope)
                        :|: (FromList FVs :|: [set Γ])).
  Proof.
    intros Hinv Hnotin Hdis.
    assert (HFunsScope : Disjoint _ S (Funs \\ Scope)) by now decomp_Disjoint.
    assert (HGFuns : Disjoint _ S GFuns) by now decomp_Disjoint.
    assert (Himage : Disjoint _ S (image (to_env FVmap) (Funs \\ Scope))) by now decomp_Disjoint.
    assert (HΓ : Disjoint _ S [set Γ]) by now decomp_Disjoint.
    assert (HScope : Disjoint _ S Scope). {
      constructor; intros x Hx; inv Hx.
      rename H into HS, H0 into HScope.
      destruct Hinv as [[Hinv _] _].
      apply Hinv in HScope; unfold In in HScope.
      specialize (Hnotin x).
      rewrite Hnotin in HScope; [easy|].
      now left. }
    splits_Disjoint; auto.
    constructor; intros x Hx; inv Hx; rename H into HS, H0 into HFVs.
    destruct Hinv as [_ [_ Hinv]].
    assert (HScope' : ~ x \in Scope) by (eapply Disjoint_In_l; eauto).
    assert (HFuns' : ~ x \in Funs). {
      intros HFuns.
      destruct HFunsScope as [HFunsScope]; contradiction (HFunsScope x).
      constructor; auto; constructor; auto. }
    assert (HGFuns' : ~ x \in GFuns) by (eapply Disjoint_In_l; eauto).
    apply In_nthN in HFVs. destruct HFVs as [n HFVs].
    specialize (Hinv n x).
    destruct Hinv as [Hinv _].
    specialize (Hinv (conj HFVs (conj HScope' (conj HFuns' HGFuns')))).
    specialize (Hnotin x).
    rewrite Hnotin in Hinv; [easy|].
    now left.
  Qed.

  Lemma FVmap_inv_empty' FVmap S GFuns :
    FVmap_inv FVmap (Empty_set _) (Empty_set _) GFuns [] ->
    FVmap_inv FVmap (Empty_set _) (Empty_set _) (S :|: GFuns) [].
  Proof.
    intros [HScope [HFuns HFVs]]; split; [|split].
    - now rewrite <- HScope.
    - now rewrite <- HFuns.
    - assert (Hempty : forall x, FVmap ! x = None). {
        intros x.
        - destruct (FVmap ! x) as [y|] eqn:Hget; [|easy].
          destruct y.
          + rewrite <- HFVs in Hget.
            destruct Hget as [Hget _]; simpl in Hget; easy.
          + normalize_sets.
            destruct HFuns as [_ HFuns]; edestruct HFuns; unfold In; eexists; eassumption.
          + normalize_sets.
            destruct HScope as [_ HScope]; edestruct HScope; unfold In; eassumption. }
      intros; split; intros H.
      + now rewrite Hempty.
      + now rewrite Hempty in H.
  Qed.

  Lemma binding_in_map_add_closures S FVmap B Γ :
    binding_in_map S FVmap ->
    binding_in_map (S :|: name_in_fundefs B) (add_closures B FVmap Γ).
  Proof.
    revert FVmap S; induction B as [f ft xs e B IHB|]; intros FVmap S Hbin.
    - simpl. intros x Hx.
      destruct (peq f x) as [?|Hne]; [subst; rewrite M.gss; eauto|rewrite M.gso by auto].
      inv Hx.
      + specialize (IHB _ _ Hbin).
        edestruct IHB as [v Hv]; [left; eassumption|].
        rewrite Hv; eauto.
      + inv H; [now inv H0|].
        specialize (IHB _ _ Hbin).
        edestruct IHB as [v Hv]; [right; eassumption|].
        rewrite Hv; eauto.
    - simpl; now normalize_sets.
  Qed.

  Lemma add_closures_image B FVmap Γ :
    image (to_env (add_closures B FVmap Γ)) (name_in_fundefs B) \subset [set Γ].
  Proof.
    induction B as [f ft xs e B IHB|].
    - simpl; unfold image; intros x Hx.
      unfold In in Hx. destruct Hx as [y [Hy Heq]].
      destruct (peq f y); [subst; unfold to_env; now rewrite M.gss|].
      subst; unfold to_env; rewrite M.gso by auto.
      apply IHB.
      inv Hy. { now inv H. }
      unfold In, image, to_env.
      eauto.
    - simpl. rewrite image_Empty_set. eauto with Ensembles_DB.
  Qed.

  Lemma add_closures_minus_names_image B FVmap Γ S :
    image (to_env (add_closures B FVmap Γ)) (S \\ name_in_fundefs B) \subset
    image (to_env FVmap) S.
  Proof.
    erewrite image_f_eq_subdomain.
    2: { eapply f_eq_subdomain_antimon; [|apply add_closures_spec]; constructor. }
    intros x Hx; unfold image, extend_fundefs', In in *.
    destruct Hx as [y [Hin Heq]]; subst. inv Hin.
    destruct (@Dec _ (name_in_fundefs B) _ y) as [HinB|HninB]; [easy|].
    eauto.
  Qed.

  Lemma add_params_irrelevant' x xs FVmap :
    ~ List.In x xs ->
    (add_params xs FVmap) ! x = FVmap ! x.
  Proof.
    induction xs as [|x' xs IHxs]; intros Hnotin; simpl; auto.
    assert (Hne : x <> x') by (intros Hc; subst; contradiction Hnotin; now left).
    rewrite M.gso by auto.
    apply IHxs; intros Hin; contradiction Hnotin; now right.
  Qed.

  Lemma add_closures_irrelevant B FVmap Γ x :
    ~ x \in name_in_fundefs B ->
    (add_closures B FVmap Γ) ! x = FVmap ! x.
  Proof.
    induction B as [f ft xs e B IHB|]; intros Hnotin; simpl; auto.
    assert (Hne : f <> x) by (intros Hc; subst; contradiction Hnotin; simpl; now left).
    rewrite M.gso by auto.
    apply IHB; intros Hin; contradiction Hnotin; now right.
  Qed.

  Lemma add_params_image xs FVmap S :
    image (to_env (add_params xs FVmap)) S \subset FromList xs :|: image (to_env FVmap) S.
  Proof.
    induction xs as [|x xs IHxs]; simpl; repeat normalize_sets; [eauto with Ensembles_DB|].
    intros y Hy.
    destruct (peq x y) as [|Hne]; [subst; now do 2 left|].
    rewrite <- Union_assoc; right; apply IHxs.
    clear IHxs; unfold In, image, to_env in *.
    destruct Hy as [x' [Hx' Hyeq]].
    destruct (peq x x'); [subst; now rewrite M.gss in Hne|].
    rewrite M.gso in Hyeq by auto.
    eauto.
  Qed.

  Lemma add_closures_image' B FVmap Γ S :
    image (to_env (add_closures B FVmap Γ)) S \subset [set Γ] :|: image (to_env FVmap) S.
  Proof.
    induction B as [f ft xs e B IHB|].
    - simpl. intros x Hx.
      destruct (peq f x) as [|Hne]; [subst|].
      { unfold In, image, to_env in Hx.
        destruct Hx as [x0 [Hx0 Hx_eq]].
        destruct (peq x x0); [subst; rewrite M.gss in Hx_eq; subst; now left|].
        rewrite M.gso in Hx_eq by auto.
        apply IHB; unfold In, image, to_env; eauto. }
      { unfold In, image, to_env in Hx.
        destruct Hx as [x0 [Hx0 Hx_eq]].
        destruct (peq f x0); [subst; rewrite M.gss in *; now left|].
        rewrite M.gso in Hx_eq by auto.
        apply IHB; unfold In, image, to_env; eauto. }
    - simpl; now right.
  Qed.

  Lemma exp_closure_conv_Closure_conv_sound :
    (forall e Scope Funs GFuns gfuns c Γ FVs FVmap S
       (* The invariant that relates [FVmap] and [Scope], [Funs], [GFuns], [FV] *)
       (Minv : FVmap_inv FVmap Scope Funs GFuns FVs)
       (Hbin1 : occurs_free e \subset Scope :|: Funs :|: GFuns :|: FromList FVs)
       (* [FVmap] does not contain the variables in [S] or [Γ] *)
       (Hbin2 : binding_not_in_map (S :|: [set Γ]) FVmap)
       (* [gfuns] relates to [GFuns] *)
       (Hgfuns : gfuns_inv gfuns GFuns)
       (Huniq : unique_bindings e)
       (Hdis1 : Disjoint _ Funs Scope)
       (Hdis2 : Disjoint _ (Funs :|: GFuns) (bound_var e))
       (* [S] is disjoint with the free and bound variables of [e] and [Γ] and ran(to_env FVmap) *)
       (HD1 : Disjoint _ S ((Funs \\ Scope) :|: GFuns :|: used_vars e :|: [set Γ]
                                            :|: image (to_env FVmap) (Funs \\ Scope)))
       (* The current environment argument is fresh *)
       (HD2 : ~ In _ (used_vars e) Γ),
       {{ fun _ s => fresh S (next_var (fst s)) }}
         exp_closure_conv clo_tag e FVmap gfuns c Γ
       {{ fun _ s ef s' =>
            fresh S (next_var (fst s')) /\
            exists C, is_exp_ctx (snd ef) C /\
              Closure_conversion clo_tag Scope Funs GFuns c (to_env FVmap) Γ FVs e (fst ef) C /\
              bound_var_ctx C \subset Range (next_var (fst s)) (next_var (fst s')) /\
              (next_var (fst s') >= next_var (fst s))%positive /\
              bound_var (fst ef) \subset bound_var e :|: Range (next_var (fst s)) (next_var (fst s')) /\
              unique_bindings (C |[ fst ef ]|)
       }}) /\
    (forall B Bg Bl FVmap Funs GFuns gfuns FVs S c
       (HB : Bg = fundefs_append Bl B)
       (HFuns : Funs <--> name_in_fundefs Bg)
       (HGFuns : gfuns_inv gfuns GFuns)
       (Minv : FVmap_inv FVmap (Empty_set _) (Empty_set _) GFuns FVs)
       (Hbin1 : occurs_free_fundefs Bg \subset GFuns :|: FromList FVs)
       (Hbin2 : binding_not_in_map S FVmap)
       (Huniq : unique_bindings_fundefs Bg)
       (HD1 : Disjoint _ S (used_vars_fundefs Bg :|: image (to_env FVmap) Funs :|: GFuns))
       (HD2 : Disjoint _ GFuns (bound_var_fundefs Bg \\ name_in_fundefs Bg)),
       {{ fun _ s => fresh S (next_var (fst s)) }}
         fundefs_closure_conv clo_tag Bg B FVmap gfuns c
       {{ fun _ s B' s' =>
          fresh S (next_var (fst s')) /\
          Closure_conversion_fundefs clo_tag Bg GFuns c FVs B B' /\
          bound_var_fundefs B' \subset bound_var_fundefs B :|: Range (next_var (fst s)) (next_var (fst s')) /\
          (next_var (fst s') >= next_var (fst s))%positive /\
          unique_bindings_fundefs B'
       }}).
  Proof with now eauto with Ensembles_DB functions_BD.
    eapply exp_def_mutual_ind; intros; simpl. Opaque exp_closure_conv.
    - apply pre_post_mp_l'; eapply bind_triple.
      + eapply get_vars_project_vars_sound; try eassumption.
        intros x Hx. eapply Hbin1. eauto.
      + intros [xs f] s. eapply pre_existential. intros C.
        eapply pre_existential. intros S'.
        eapply pre_curry_l. intros [Hproj [Hctx Huniq']].
        apply pre_post_mp_l'.
        eapply bind_triple.
        eapply pre_strenghtening.
        { intros ? ? [Hleft ?]; exact Hleft. }
        eapply H with (Scope := Union var (Singleton var v) Scope)
                      (S := S')
                      (FVmap := Maps.PTree.set v BoundVar FVmap).
        * eapply FVmap_inv_set_bound. eassumption.
        * (* x is the only new binding *) clear - Hbin1.
          normalize_occurs_free_in_ctx.
          intros x Hx. specialize (Hbin1 x).
          rewrite !In_or_Iff_Union in *.
          rewrite not_In_Setminus in Hbin1.
          unfold In in *.
          destruct (peq v x); [subst; left; left; left; now left|].
          assert (~ [set v] x) by (intros Hc; inv Hc; congruence).
          tauto.
        * eapply binding_not_in_map_antimon.
          apply Included_Union_compat.
          eapply project_vars_free_set_Included; now eauto.
          now apply Included_refl.
          eapply binding_not_in_map_set_not_In_S. eassumption.
          intros Hc; inv Hc.
          { unfold used_vars in HD1. eapply HD1; constructor; [eassumption|].
            left; left; right; left; eauto. }
          { inv H0; eapply HD2; unfold used_vars; eauto. }
        * assumption.
        * now inv Huniq.
        * normalize_bound_var_in_ctx. decomp_Disjoint. eauto with Ensembles_DB.
        * normalize_bound_var_in_ctx.
          decomp_Disjoint; splits_Disjoint; eauto with Ensembles_DB.
          now apply Disjoint_sym.
        * eapply Disjoint_Included_l.
          eapply project_vars_free_set_Included; now eauto.
          eapply Disjoint_Included_r; [| eassumption ].
          apply Included_Union_compat.
          -- apply Included_Union_compat; [|now apply Included_refl].
             normalize_used_vars; rewrite Union_assoc.
             apply Included_Union_compat; [|now apply Included_refl].
             eauto with Ensembles_DB.
          -- intros x Hx; unfold image, In in *.
             destruct Hx as [y [Hy Hyeqn]].
             exists y; split.
             ++ inv Hy; constructor; auto.
             ++ assert (v <> y). { intros Hc; subst; inv Hy. contradiction H1; now left. }
                unfold to_env in *. rewrite M.gso in Hyeqn by auto. auto.
        * intros Hc. inv Hc; eapply HD2; eauto; normalize_used_vars.
          right; now left.
          right; now right.
        * intros e' s'.
          eapply return_triple.
          intros _ s'' [Hfresh [C' [Hctx' [Hcc [Hran'' [Hinc'' [Hbv'' Huniq'']]]]]]] [Hf' [Hran' Hinc']] Hf; eauto.
          split; [|exists C; splits]; auto.
          -- eapply fresh_inc; [|eassumption]; zify; lia.
          -- rewrite Hctx'; simpl. econstructor; [|eassumption|].
             ++ eapply FV_preserves_disjoint_inv; eauto.
             ++ eapply Closure_conversion_f_eq_subdomain; [eassumption|].
                rewrite <- to_env_BoundVar_f_eq. apply f_eq_subdomain_extend_not_In_S_l.
                intros Hc. inv Hc. now eauto. reflexivity.
          -- eapply Included_trans; try eassumption.
             intros arb Harb; unfold Range, In in *; zify; lia.
          -- zify; lia.
          -- simpl. rewrite Hctx'. repeat normalize_bound_var.
             rewrite bound_var_app_ctx.
             apply Union_Included; auto with Ensembles_DB. apply Union_Included.
             ++ (* BV(C') ⊆ [s', s'') by Hran'' and [s', s'') ⊆ [s, s'') by Hinc' *)
                eapply Included_trans; [apply Hran''|].
                intros x Hx; right; unfold In, Range in *; zify; lia.
             ++ (* BV(C') ⊆ BV(e) ∪ {v} ∪ [s', s'') by Hbv'' and [s', s'') ⊆ [s, s'') by Hinc' *)
                eapply Included_trans; [apply Hbv''|].
                rewrite <- Union_assoc. apply Included_Union_compat; [apply Included_refl|].
                intros x Hx; right; unfold In, Range in *; zify; lia.
          -- simpl. rewrite Hctx'.
             (* UB(C[Econstr v t xs (C'[e'])])
                  <=> UB(C) /\ UB(C') /\ UB(e') /\ (BV(C) # {v} # BV(C') # BV(e'))
                Have UB(C) by Huniq', UB(C') /\ UB(e') by Huniq'', leaving
                  BV(C) # {v} # BV(C') # BV(e')
                Have v ∉ BV(C) because BV(C) ⊆ [s, s') ⊆ S (by Hran', Hf) and v ∉ S (by HD1)
                Have v ∉ BV(C') because BV(C') ⊆ [s', s'') ⊆ S (by Hran'', Hinc', Hf) and v ∉ S
                Have v ∉ BV(e') because BV(e') ⊆ BV(e) ∪ [s', s'') (by Hbv'') and
                  v ∉ BV(e) by Huniq
                  v ∉ [s', s'') because [s', s'') ⊆ S
                This leaves
                  BV(C) # BV(C') # BV(e')
                Have BV(C) # BV(C') because BV(C) ⊆ [s, s') by Hran' and BV(C') ⊆ [s', s'') by Hran''
                Have BV(C) # BV(e') because BV(e') ⊆ BV(e) ∪ [s', s'') by Hbv'' and
                  BV(C) ⊆ [s, s') by Hran' and [s, s') # [s', s'')
                  BV(C) ⊆ [s, s') ⊆ S # BV(e) by Hran', Hf, HD1
                Similarly BV(C') # BV(e') *)
             rewrite (proj1 (ub_app_ctx_f _)); splits; auto.
             ++ constructor; auto.
                change (~ ?S ?x) with (~ x \in S); rewrite bound_var_app_ctx.
                intros Hc; inv Hc.
                ** apply Hran'' in H0.
                   destruct HD1 as [HD1]. contradiction (HD1 v).
                   constructor; [|normalize_used_vars; left; left; right; left; now left].
                   apply Hf; unfold Range, In in *; zify; lia.
                ** apply Hbv'' in H0. inv H0.
                   --- now inv Huniq.
                   --- destruct HD1 as [HD1]. contradiction (HD1 v).
                       constructor; [|normalize_used_vars; left; left; right; left; now left].
                       apply Hf; unfold Range, In in *; zify; lia.
             ++ normalize_bound_var.
                rewrite bound_var_app_ctx.
                decomp_Disjoint; splits_Disjoint.
                ** eapply Disjoint_Included_l; [|eapply Disjoint_Included_r]; try eassumption.
                   constructor; intros x; intros Hc; inv Hc; unfold In, Range in *; zify; lia.
                ** eapply Disjoint_Included_l; [|eapply Disjoint_Included_r]; try eassumption.
                   apply Union_Disjoint_r.
                   --- assert (HSdis : Range (next_var (fst s)) (next_var (fst s')) \subset S). {
                         intros x Hx; apply Hf; unfold Range, In in *; zify; lia. }
                       eapply Disjoint_Included_l; [apply HSdis|].
                       unfold used_vars in *.
                       eapply Disjoint_Included_r; [|apply H3].
                       normalize_bound_var...
                   --- constructor; intros x Hx; inv Hx; unfold Range, In in *; zify; lia.
                ** eapply Disjoint_Included_l; [apply Hran'|].
                   constructor; intros x Hx; inv Hx. inv H8. destruct H3 as [Hc].
                   contradiction (Hc x); constructor.
                   --- apply Hf; unfold Range, In in *; zify; lia.
                   --- normalize_used_vars; left; now left.
    - setoid_rewrite left_id.
      eapply bind_triple'.
      + apply get_var_project_var_sound; eauto.
        intros x Hx. eapply Hbin1. rewrite occurs_free_Ecase_nil. eassumption.
      + intros [x f] s. eapply return_triple.
        intros _ s' [Hfresh [C [S' [[Hproj [Hctx Huniq']] [Hf' [Hran Hinc]]]]]].
        split; [eapply fresh_inc; [|eassumption]; zify; lia|]; exists C; splits; auto.
        { econstructor; [| eassumption | constructor].
          eapply FV_preserves_disjoint_inv; eauto. }
        { simpl; normalize_bound_var; eauto with Ensembles_DB. }
        { simpl. rewrite (proj1 (ub_app_ctx_f _)). splits; auto.
          - constructor.
          - normalize_bound_var... }
    - setoid_rewrite assoc. eapply bind_triple'.
      + eapply H; try eassumption.
        * (* FV(e) ⊆ FV(Ecase v ((c, e) :: l)) *)
          clear - Hbin1.
          normalize_occurs_free_in_ctx.
          intros x Hx. specialize (Hbin1 x).
          rewrite !In_or_Iff_Union in *.
          unfold In in *.
          tauto.
        * now inv Huniq.
        * repeat normalize_bound_var_in_ctx.
          decomp_Disjoint; splits_Disjoint; auto; apply Disjoint_sym; auto.
        * eapply Disjoint_Included_r; [| eassumption ].
          apply Included_Union_compat. 2: now apply Included_refl.
          normalize_used_vars.
          eauto with Ensembles_DB.
        * (* Follows from HD2 *)
          intros Hc; contradiction HD2; normalize_used_vars; now left.
      + intros [e' f'] s'. setoid_rewrite assoc. simpl.
        setoid_rewrite st_eq_Ecase.
        apply pre_curry_l; intros Hfresh.
        eapply pre_existential_r. intros C. apply pre_curry_rl; intros Hctx.
        apply pre_curry_rl; intros Hcc. eapply bind_triple'.
        eapply pre_strenghtening.
        2: eapply H0 with (FVmap := FVmap) (Γ := Γ) (c := c0); try eassumption.
        { simpl. intros _ s Hconj; decompose [and] Hconj. intros arb Harb.
          apply Hfresh. zify; lia. }
        * (* FV(Ecase v l) ⊆ FV(Ecase v ((c, e) :: l)) *)
          clear - Hbin1; normalize_occurs_free_in_ctx.
          intros x Hx. specialize (Hbin1 x).
          rewrite !In_or_Iff_Union in Hbin1|-*.
          rewrite !In_or_Iff_Union in Hbin1.
          tauto.
        * now inv Huniq.
        * (* Follows from Hdis2 *)
          repeat normalize_bound_var_in_ctx.
          decomp_Disjoint; splits_Disjoint; auto; apply Disjoint_sym; auto.
        * eapply Disjoint_Included_r; [| eassumption ].
          normalize_used_vars.
          solve_Union_Inc.
        * (* Follows from HD2 *)
          intros Hc; contradiction HD2; repeat normalize_used_vars; now right.
        * intros [e'' f] s''.
          edestruct e''; eapply return_triple;
            intros _ s''' [Hpre [Hfresh_s''' [C2 [Hctx2 [Hcc2' Hf2]]]]]; inv Hcc2'.
          destruct Hf2 as [HbvC2 [Hinc'' [Hbv_case Huniq'']]], Hpre as [HbvC [Hinc' [Hbv_e Huniq_e]]].
          split; [eapply fresh_inc; [|eassumption]; zify; lia|]; eexists; splits.
          { eassumption. }
          { econstructor; try eassumption.
            constructor; auto; splits; auto; simpl.
            rewrite Hctx; repeat eexists; eauto. }
          { (* Follows from HbvC2, Hinc' *)
            eapply Included_trans; [apply HbvC2|].
            intros x Hx; unfold In, Range in *; zify; lia. }
          { zify; lia. }
          { simpl; repeat normalize_bound_var. rewrite Hctx.
            rewrite bound_var_app_ctx.
            (* Follows from HbvC, Hinc'', Hbv_e, Hbv_case *)
            solve_Union_Inc.
            - eapply Included_trans; [apply Hinc'|].
              intros x Hx; right; unfold In, Range in *; zify; lia.
            - eapply Included_trans; [apply Huniq_e|]; solve_Union_Inc.
              intros x Hx; right; unfold In, Range in *; zify; lia.
            - eapply Included_trans; [apply Hbv_case|]; solve_Union_Inc.
              intros x Hx; right; unfold In, Range in *; zify; lia. }
          { simpl. unfold is_exp_ctx in Hctx. rewrite Hctx.
             rewrite (proj1 (ub_app_ctx_f _)); splits.
             - rewrite (proj1 (ub_app_ctx_f _)) in Huniq''.
               destruct Huniq'' as [HuniqC2 [Huniqf HdisC2]]; auto.
             - constructor; [|now destruct Huniq_e|].
               + rewrite (proj1 (ub_app_ctx_f _)) in Huniq''.
                 now destruct Huniq'' as [? [Hres ?]].
               + rewrite bound_var_app_ctx. splits_Disjoint.
                 eapply Disjoint_Included_l; [apply Hinc'|].
                 eapply Disjoint_Included_r; [apply Hbv_case|].
                 splits_Disjoint.
                 * constructor; intros x Hx; inv Hx.
                   destruct HD1 as [HD1]; contradiction (HD1 x).
                   constructor.
                   -- apply Hfresh; unfold In, Range in *; zify; lia.
                   -- unfold used_vars; normalize_bound_var; left; left; right; left; now right.
                 * constructor; intros x Hx; inv Hx; unfold In, Range in *; zify; lia.
                 * destruct Huniq_e as [Hbve' Huniq_e].
                   eapply Disjoint_Included_l; [apply Hbve'|].
                   eapply Disjoint_Included_r; [apply Hbv_case|].
                   splits_Disjoint.
                   -- now inv Huniq.
                   -- constructor; intros x Hx; inv Hx.
                      destruct HD1 as [HD1]; contradiction (HD1 x).
                      constructor.
                      ++ apply Hfresh; unfold In, Range in *; zify; lia.
                      ++ unfold used_vars; normalize_bound_var; left; left; right; left; now right.
                   -- constructor; intros x Hx; inv Hx.
                      destruct HD1 as [HD1]; contradiction (HD1 x).
                      constructor.
                      ++ apply Hfresh; unfold In, Range in *; zify; lia.
                      ++ unfold used_vars; normalize_bound_var; left; left; right; left; now left.
                   -- constructor; intros x Hx; inv Hx; unfold In, Range in *; zify; lia.
             - normalize_bound_var. rewrite bound_var_app_ctx; splits_Disjoint.
               + eapply Disjoint_Included_l; [apply HbvC2|].
                 eapply Disjoint_Included_r; [apply Hinc'|].
                 constructor; intros x Hx; inv Hx; unfold In, Range in *; zify; lia.
               + eapply Disjoint_Included_l; [apply HbvC2|].
                 destruct Huniq_e as [Hbv_e' Huniq'].
                 eapply Disjoint_Included_r; [apply Hbv_e'|]; splits_Disjoint.
                 * constructor; intros x Hx; inv Hx.
                   destruct HD1 as [HD1]; contradiction (HD1 x).
                   constructor.
                   -- apply Hfresh; unfold In, Range in *; zify; lia.
                   -- unfold used_vars; normalize_bound_var; left; left; right; left; now left.
                 * constructor; intros x Hx; inv Hx.
                   unfold In, Range in *; zify; lia.
               + rewrite (proj1 (ub_app_ctx_f _)) in Huniq''.
                 now destruct Huniq'' as [HunqiC2 [Huniqcase HdisC2]]. }
    - eapply bind_triple'.
      + eapply get_var_project_var_sound; try eassumption.
        intros x Hx. inv Hx. eapply Hbin1. eauto.
      + intros [x f] s.
        apply pre_curry_l; intros Hfresh.
        eapply pre_existential. intros C.
        eapply pre_existential. intros S'.
        eapply pre_curry_l. intros [Hproj [Hctx Huniq']].
        apply pre_post_mp_l'.
        eapply bind_triple.
        eapply pre_strenghtening.
        2: eapply H with (Scope := Union var (Singleton var v) Scope)
                      (S := S')
                      (FVmap := Maps.PTree.set v BoundVar FVmap).
        { clear; tauto. }
        * eapply FVmap_inv_set_bound. eassumption.
        * (* v is the only new binding *)
          clear - Hbin1. normalize_occurs_free_in_ctx.
          intros x Hx. specialize (Hbin1 x).
          rewrite !In_or_Iff_Union in *.
          rewrite not_In_Setminus in Hbin1.
          unfold In in *.
          destruct (peq v x); [subst; left; left; left; now left|].
          assert (~ [set v] x) by (intros Hc; inv Hc; congruence).
          tauto.
        * eapply binding_not_in_map_antimon.
          apply Included_Union_compat. now eapply project_var_free_set_Included; eauto.
          now apply Included_refl.
          eapply binding_not_in_map_set_not_In_S. eassumption.
          intros Hc; inv Hc.
          { eapply HD1; eauto.
            constructor; try eassumption.
            normalize_used_vars. left; left; right; now left. }
          { inv H0; eapply HD2; normalize_used_vars. now left. }
        * assumption.
        * now inv Huniq.
        * normalize_bound_var_in_ctx; decomp_Disjoint; eauto with Ensembles_DB.
        * normalize_bound_var_in_ctx; decomp_Disjoint; splits_Disjoint; eauto with Ensembles_DB.
          now apply Disjoint_sym.
        * eapply Disjoint_Included_l. eapply project_var_free_set_Included; now eauto.
          rewrite <- to_env_BoundVar_f_eq.
          eapply Disjoint_Included_r; [| eassumption ].
          apply Included_Union_compat.
          2: rewrite (Union_commut (Singleton _ _)), <- Setminus_Union.
          2: now eapply image_Setminus_extend.
          apply Included_Union_compat; [| now apply Included_refl ].
          normalize_used_vars; solve_Union_Inc.
        * (* Follows from HD2 *)
          intros Hc; contradiction HD2; normalize_used_vars; right; now right.
        * intros e' s'. eapply return_triple.
          intros _ s'' [Hfresh' [C' [Hctx' [Hcc [HbvC' [Hinc' [Hbv' Huniq'']]]]]]] [Hfresh'' [HbvC Hinc]].
          split; [eapply fresh_inc; [|eassumption]; zify; lia|].
          eexists; splits. { eassumption. }
          { simpl. rewrite Hctx'. econstructor; try eassumption.
            - eapply Disjoint_free_set in Minv.
              + decomp_Disjoint; splits_Disjoint; eauto with Ensembles_DB.
              + eapply binding_not_in_map_antimon; [| eassumption ].
                now apply Included_Union_l.
              + (* Follows from HD1 *)
                apply Disjoint_sym.
                eapply Disjoint_Included_r; [|apply HD1]; eauto with Ensembles_DB.
            - eapply Closure_conversion_f_eq_subdomain. eassumption.
              rewrite <- to_env_BoundVar_f_eq. apply f_eq_subdomain_extend_not_In_S_l.
              + intros Hc. inv Hc. now eauto.
              + reflexivity. }
          { eapply Included_trans; [apply HbvC|]. intros x' Hx; unfold In, Range in *; zify; lia. }
          { zify; lia. }
          { simpl; repeat normalize_bound_var. rewrite Hctx'.
            rewrite bound_var_app_ctx.
            solve_Union_Inc.
            - eapply Included_trans; [apply HbvC'|].
              intros x' Hx; right; unfold In, Range in *; zify; lia.
            - eapply Included_trans; [apply Hbv'|]; solve_Union_Inc.
              intros x' Hx; right; unfold In, Range in *; zify; lia. }
          { simpl; rewrite Hctx'.
             rewrite (proj1 (ub_app_ctx_f _)); splits; auto.
             ++ constructor; auto.
                change (~ ?S ?x) with (~ x \in S); rewrite bound_var_app_ctx.
                intros Hc; inv Hc.
                ** apply HbvC' in H0.
                   destruct HD1 as [HD1]. contradiction (HD1 v).
                   constructor; [|normalize_used_vars; left; left; right; now left].
                   apply Hfresh; unfold Range, In in *; zify; lia.
                ** apply Hbv' in H0. inv H0.
                   --- now inv Huniq.
                   --- destruct HD1 as [HD1]. contradiction (HD1 v).
                       constructor; [|normalize_used_vars; left; left; right; now left].
                       apply Hfresh; unfold Range, In in *; zify; lia.
             ++ normalize_bound_var.
                rewrite bound_var_app_ctx.
                decomp_Disjoint; splits_Disjoint.
                ** eapply Disjoint_Included_l; [|eapply Disjoint_Included_r]; try eassumption.
                   constructor; intros x'; intros Hc; inv Hc; unfold In, Range in *; zify; lia.
                ** eapply Disjoint_Included_l; [|eapply Disjoint_Included_r]; try eassumption.
                   apply Union_Disjoint_r.
                   --- assert (HSdis : Range (next_var (fst s)) (next_var (fst s')) \subset S). {
                         intros x' Hx; apply Hfresh; unfold Range, In in *; zify; lia. }
                       eapply Disjoint_Included_l; [apply HSdis|].
                       unfold used_vars in *.
                       eapply Disjoint_Included_r; [|apply H3].
                       normalize_bound_var...
                   --- constructor; intros x' Hx; inv Hx; unfold Range, In in *; zify; lia.
                ** eapply Disjoint_Included_l; [apply HbvC|].
                   constructor; intros x' Hx; inv Hx. inv H8. destruct H3 as [Hc].
                   contradiction (Hc x'); constructor.
                   --- apply Hfresh; unfold Range, In in *; zify; lia.
                   --- normalize_used_vars; now left. }
    - eapply bind_triple'; [apply get_var_project_var_sound; try eassumption|].
      { (* f ∈ FV(let x = f(ys) in e) *)
        eapply Included_trans; [|apply Hbin1].
        normalize_occurs_free... }
      intros [f' Cf] s.
      apply pre_curry_l; intros Hfresh.
      apply pre_existential; intros C_f.
      apply pre_existential; intros S_f.
      apply pre_curry_l; intros [Hproj [Hctx Huniq']].
      eapply bind_triple'.
      eapply pre_strenghtening; [|apply get_vars_project_vars_sound; try eassumption].
      { simpl; intros ? ? [Hres ?]; exact Hres. }
      { (* Hbin1 *)
        eapply Included_trans; [|apply Hbin1].
        normalize_occurs_free... }
      intros [ys' Cys] s'.
      apply pre_curry_l; intros [Hfresh_f [HbvC_f Hinc_f]].
      apply pre_existential; intros C_ys; apply pre_existential; intros S_ys.
      apply pre_curry_l; intros [Hprojs [Hctx_ys Huniq_ys]].
      eapply bind_triple'; [eapply pre_strenghtening; [|apply get_name_spec] |].
      { intros ? ? [Hres ?]; exact Hres. }
      intros ptr s_ptr; apply pre_curry_l; intros [Hfresh_ys [HbvC_ys Hinc_ys]].
      eapply bind_triple'; [eapply pre_strenghtening; [|apply get_name_spec] |].
      { intros ? ? [? [? [? Hres]]]; exact Hres. }
      intros Γ' s_Γ'; apply pre_curry_l; intros [HS_ptr [Hptr_ran [Hs_ptr Hfresh_ptr]]].
      apply pre_curry_l; intros HS_Γ'.
      eapply bind_triple'; [eapply pre_strenghtening|].
      { simpl; intros ? ? [? [? Hres]]; exact Hres. }
      { eapply H with (Scope := x |: Scope)
                      (FVmap := Maps.PTree.set x BoundVar FVmap); try eassumption.
        - eapply FVmap_inv_set_bound. eassumption.
        - (* Hbin1 *)
          clear - Hbin1.
          normalize_occurs_free_in_ctx.
          intros arb Harb. specialize (Hbin1 arb).
          rewrite !In_or_Iff_Union in *.
          rewrite not_In_Setminus in Hbin1.
          unfold In in *.
          destruct (peq x arb); [subst; left; left; left; now left|].
          assert (~ [set x] arb) by (intros Hc; inv Hc; congruence).
          tauto.
        - eapply binding_not_in_map_antimon with (S := S :|: [set Γ]).
          + assert (Hsub_ys : S_ys \subset S_f). { eapply project_vars_free_set_Included; eauto. }
            assert (Hsub_f : S_f \subset S). { eapply project_var_free_set_Included; eauto. }
            apply Included_Union_compat; [|apply Included_refl].
            do 2 apply Setminus_Included_Included_Union.
            eapply Included_trans; [eassumption|].
            eapply Included_trans; [eassumption|]...
          + eapply binding_not_in_map_set_not_In_S.
            { eapply binding_not_in_map_antimon; [|eassumption]... }
            intros Hc; inv Hc.
            { eapply HD1; constructor; [eassumption|]. normalize_used_vars... }
            { inv H0. apply HD2. normalize_used_vars... }
        - now inv Huniq.
        - normalize_bound_var_in_ctx; decomp_Disjoint...
        - normalize_bound_var_in_ctx; decomp_Disjoint; splits_Disjoint; eauto with Ensembles_DB.
          now apply Disjoint_sym.
        - (* Can ignore Γ'.
             S_ys\{ptr}\{Γ'} ⊆ S_ys ⊆ S_f ⊆ S.
             S # Funs\({x}∪Scope) by HD1.
             FVmap[x↦BVar](Funs\({x}∪Scope)) ⊆ FVmap(Funs\Scope) # S by HD1.
             GFuns, used_vars e # S by HD1. *)
          assert (HS_sub : S_ys \\ [set ptr] \\ [set Γ'] \subset S). {
            apply Setminus_Included_preserv.
            apply Setminus_Included_preserv.
            assert (Hys_sub : S_ys \subset S_f)
              by (eapply project_vars_free_set_Included; eauto).
            assert (Hf_sub : S_f \subset S)
              by (eapply project_var_free_set_Included; eauto).
            eapply Included_trans; [|eassumption].
            eapply Included_trans; [|eassumption].
            eapply Included_refl. }
          decomp_Disjoint; splits_Disjoint.
          + eapply Disjoint_Included_l; [apply HS_sub|].
            eapply Disjoint_Included_r; [|apply H0].
            rewrite <- Setminus_Union; eauto with Ensembles_DB.
          + eapply Disjoint_Included_l; [apply HS_sub|]; auto.
          + eapply Disjoint_Included_l; [apply HS_sub|]; auto.
            eapply Disjoint_Included_r; [|apply H3].
            normalize_used_vars; eauto with Ensembles_DB.
          + eapply Disjoint_Included_l; [apply HS_sub|]; auto.
          + eapply Disjoint_Included_l; [apply HS_sub|]; auto.
            constructor; intros arb Harb; inv Harb.
            rename H7 into HS_arb, H8 into Himage_arb.
            unfold In, image in Himage_arb.
            destruct Himage_arb as [arb' [Harb' Henv_eq]].
            unfold to_env in Henv_eq.
            destruct (peq x arb'); [subst arb'; rewrite M.gss in Henv_eq|rewrite M.gso in Henv_eq by auto].
            * inv Harb'. contradiction H8; now left.
            * assert (Harb'_dom : arb' \in Funs \\ Scope). {
                constructor; inv Harb'; auto. }
              assert (Harb_im : arb \in image (to_env FVmap) (Funs \\ Scope)). {
                unfold to_env, image, In; eexists. rewrite Henv_eq. now split. }
              assert (Harb_notin_S : ~ arb \in S). {
                intros Hc; destruct H1 as [H1]; contradiction (H1 arb).
                constructor; auto. }
              easy.
        - intros Hc; apply HD2; normalize_used_vars... }
      intros e' s_e'; apply pre_curry_l; intros [HΓ' [Hinc_Γ' Hfresh_Γ']].
      apply pre_existential_r; intros C_e'; apply pre_curry_rl; intros Hctx_e'.
      apply pre_curry_rl; intros Hcc_e'.
      apply return_triple.
      intros _ s_final [Hfresh_final [HbvC_e' [Hinc_e' [Hbv_e' Huniq_e']]]].
      split; [eapply fresh_inc; [|eassumption]; zify; lia|]; exists (comp_ctx_f C_f C_ys); splits.
      { unfold is_exp_ctx; simpl; intros ?. now rewrite Hctx, Hctx_ys, app_ctx_f_fuse. }
      { simpl. unfold is_exp_ctx in Hctx_e'; rewrite Hctx_e'.
        eapply CC_Eletapp with (S := S).
        - eapply FV_preserves_disjoint_inv; eauto.
        - econstructor; eassumption.
        - auto.
        - now inv HS_Γ'.
        - intros Hc; subst; unfold In, Range in *; zify; lia. (* ptr ∈ [s_ptr, s_Γ') while Γ' ∈ [s_Γ', s_e') *)
        - eapply Closure_conversion_f_eq_subdomain. eassumption.
          rewrite <- to_env_BoundVar_f_eq. apply f_eq_subdomain_extend_not_In_S_l.
          + intros Hc. inv Hc. now eauto.
          + reflexivity. }
        { (* Follows from HbvC, Hinc' *)
          normalize_bound_var_ctx; solve_Union_Inc.
          - eapply Included_trans; [apply HbvC_f|]; intros x' Hx; unfold In, Range in *; zify; lia.
          - eapply Included_trans; [apply HbvC_ys|]; intros x' Hx; unfold In, Range in *; zify; lia. }
        { zify; lia. }
        { simpl; repeat normalize_bound_var. rewrite Hctx_e'.
          rewrite bound_var_app_ctx.
          solve_Union_Inc.
          - eapply Included_trans; [apply HbvC_e'|]; intros x' Hx; right; unfold In, Range in *; zify; lia.
          - eapply Included_trans; [apply Hbv_e'|]; solve_Union_Inc.
            intros x' Hx; right; unfold In, Range in *; zify; lia.
          - intros x' Hx; inv Hx; right; unfold In, Range in *; zify; lia.
          - intros x' Hx; inv Hx; right; unfold In, Range in *; zify; lia. }
        { simpl; rewrite Hctx_e'.
          rewrite (proj1 (ub_app_ctx_f _)); splits.
          - apply unique_bindings_c_comp; auto.
            eapply Disjoint_Included_l; [apply HbvC_f|].
            eapply Disjoint_Included_r; [apply HbvC_ys|].
            constructor; intros x' Hx; inv Hx; unfold In, Range in *; zify; lia.
          - constructor; auto.
            { change (~ ?S ?x) with (~ x \in S).
              repeat normalize_bound_var. rewrite bound_var_app_ctx.
              rewrite !Union_demorgan; splits.
              - intros Hc; apply HbvC_e' in Hc. unfold Range, In in *; zify; lia.
              - intros Hc; apply Hbv_e' in Hc.
                inv Hc; [|unfold Range, In in *; zify; lia].
                destruct HD1 as [HD1]; contradiction (HD1 ptr).
                constructor.
                + apply Hfresh; unfold Range, In in *; zify; lia.
                + unfold used_vars; normalize_bound_var; left; left; right; left; now left.
              - intros Hc; inv Hc.
                destruct HD1 as [HD1]; contradiction (HD1 ptr).
                constructor.
                + apply Hfresh; unfold Range, In in *; zify; lia.
                + unfold used_vars; normalize_bound_var; left; left; right; left; now right.
              - intros Hc; inv Hc. unfold Range, In in *; zify; lia. }
            constructor; auto.
            { change (~ ?S ?x) with (~ x \in S).
              repeat normalize_bound_var; rewrite bound_var_app_ctx.
              rewrite !Union_demorgan; splits.
              - intros Hc; apply HbvC_e' in Hc. unfold Range, In in *; zify; lia.
              - intros Hc; apply Hbv_e' in Hc.
                inv Hc; [|unfold Range, In in *; zify; lia].
                destruct HD1 as [HD1]; contradiction (HD1 Γ').
                constructor.
                + apply Hfresh; unfold Range, In in *; zify; lia.
                + unfold used_vars; normalize_bound_var; left; left; right; left; now left.
              - intros Hc; inv Hc.
                destruct HD1 as [HD1]; contradiction (HD1 Γ').
                constructor.
                + apply Hfresh; unfold Range, In in *; zify; lia.
                + unfold used_vars; normalize_bound_var; left; left; right; left; now right. }
            constructor; auto.
            { change (~ ?S ?x) with (~ x \in S).
              rewrite bound_var_app_ctx, Union_demorgan; splits.
              - intros Hc; apply HbvC_e' in Hc.
                destruct HD1 as [HD1]; contradiction (HD1 x).
                constructor.
                + apply Hfresh; unfold Range, In in *; zify; lia.
                + unfold used_vars; normalize_bound_var; left; left; right; left; now right.
              - intros Hc; apply Hbv_e' in Hc. inv Hc.
                + now inv Huniq.
                + destruct HD1 as [HD1]; contradiction (HD1 x).
                  constructor.
                  * apply Hfresh; unfold Range, In in *; zify; lia.
                  * unfold used_vars; normalize_bound_var; left; left; right; left; now right. }
          - normalize_bound_var_ctx. repeat normalize_bound_var.
            rewrite bound_var_app_ctx. splits_Disjoint.
            + eapply Disjoint_Included_l; [apply HbvC_f|].
              eapply Disjoint_Included_r; [apply HbvC_e'|].
              constructor; intros x' Hx; inv Hx; unfold Range, In in *; zify; lia.
            + eapply Disjoint_Included_l; [apply HbvC_ys|].
              eapply Disjoint_Included_r; [apply HbvC_e'|].
              constructor; intros x' Hx; inv Hx; unfold Range, In in *; zify; lia.
            + eapply Disjoint_Included_l; [apply HbvC_f|].
              eapply Disjoint_Included_r; [apply Hbv_e'|].
              splits_Disjoint; [|constructor; intros x' Hx; inv Hx; unfold Range, In in *; zify; lia].
              constructor; intros x' Hx; inv Hx. destruct HD1 as [HD1]; contradiction (HD1 x').
              constructor.
              * apply Hfresh; unfold In, Range in *; zify; lia.
              * unfold used_vars; normalize_bound_var; left; left; right; left; now left.
            + eapply Disjoint_Included_l; [apply HbvC_ys|].
              eapply Disjoint_Included_r; [apply Hbv_e'|].
              splits_Disjoint; [|constructor; intros x' Hx; inv Hx; unfold Range, In in *; zify; lia].
              constructor; intros x' Hx; inv Hx. destruct HD1 as [HD1]; contradiction (HD1 x').
              constructor.
              * apply Hfresh; unfold In, Range in *; zify; lia.
              * unfold used_vars; normalize_bound_var; left; left; right; left; now left.
            + eapply Disjoint_Included_l; [apply HbvC_f|].
              constructor; intros x' Hx; inv Hx. inv H1.
              destruct HD1 as [HD1]; contradiction (HD1 x').
              constructor.
              * apply Hfresh; unfold In, Range in *; zify; lia.
              * unfold used_vars; normalize_bound_var; left; left; right; left; now right.
            + eapply Disjoint_Included_l; [apply HbvC_ys|].
              constructor; intros x' Hx; inv Hx. inv H1.
              destruct HD1 as [HD1]; contradiction (HD1 x').
              constructor.
              * apply Hfresh; unfold In, Range in *; zify; lia.
              * unfold used_vars; normalize_bound_var; left; left; right; left; now right.
            + eapply Disjoint_Included_l; [apply HbvC_f|].
              constructor; intros x' Hx; inv Hx. inv H1.
              unfold In, Range in *; zify; lia.
            + eapply Disjoint_Included_l; [apply HbvC_ys|].
              constructor; intros x' Hx; inv Hx. inv H1.
              unfold In, Range in *; zify; lia.
            + eapply Disjoint_Included_l; [apply HbvC_f|].
              constructor; intros x' Hx; inv Hx. inv H1.
              unfold In, Range in *; zify; lia.
            + eapply Disjoint_Included_l; [apply HbvC_ys|].
              constructor; intros x' Hx; inv Hx. inv H1.
              unfold In, Range in *; zify; lia. }
    - remember (filter _ _) as FVs_pre eqn:HFVs_pre.
      remember (match FVs_pre with [] => true | _ :: _ => false end) as is_closed eqn:Hclos.
      assert (HFVs_pre_eq : FromList FVs_pre <--> occurs_free_fundefs f2 \\ GFuns). {
        subst FVs_pre. rewrite filter_setminus; eauto.
        apply Same_set_Setminus_compat; eauto with Ensembles_DB.
        rewrite fundefs_fv_correct; reflexivity. }
      assert (HGFuns_eq : GFuns \\ name_in_fundefs f2 <--> GFuns). {
        split.
        - intros x Hx; now inv Hx.
        - intros x Hx; constructor; auto.
          intros Hc; destruct Hdis2 as [Hdis2]; contradiction (Hdis2 x); constructor; auto.
          normalize_bound_var; left; apply name_in_fundefs_bound_var_fundefs; auto. }
      eapply bind_triple'; [ eapply get_named_str_fresh |].
      intros Γ' s_Γ'. eapply pre_curry_l. intros HS_Γ'.
      eapply bind_triple'.
      { eapply pre_strenghtening; [|eapply make_env_spec].
        { intros ? ? [? [? [? Hres]]]; exact Hres. }
        all: try eassumption.
        - (* Hbin1, HFVs_pre_eq, HGFuns_eq *)
          rewrite HFVs_pre_eq; eapply Included_trans; [apply Setminus_Included|].
          eapply Included_trans; [|apply Hbin1].
          normalize_occurs_free...
        - eapply binding_not_in_map_antimon; [| eassumption ]...
        - (* GFuns # (filter (not . member gfuns) _) because dom(gfuns) = GFuns *)
          rewrite HFVs_pre_eq; eauto with Ensembles_DB.
        - (* NoDup (filter _ (PS.elements xs))
               <== NoDup (PS.elements xs)
               <== NoDupA eq (PS.elements xs) (by NoDupA_NoDup)
               qed (by PS.elements_spec2w) *)
          subst FVs_pre.
          apply filter_NoDup, NoDupA_NoDup, PS.elements_spec2w.
        - intros Hc; inv Hc; auto. }
      intros [[c' FVmap'] f] s_env.
      remember (add_closures f2 FVmap Γ') as FVmap_n eqn:HFVmap_n.
      remember (add_closures_gfuns f2 gfuns is_closed) as gfuns' eqn:Hgfuns'.
      apply pre_curry_l; intros [HΓ' [Hran_Γ' [Hinc_Γ' Hfresh_Γ']]].
      eapply pre_existential; intros C_env.
      eapply pre_existential; intros S_env.
      eapply pre_existential; intros FVs'.
      destruct (add_closures_gfuns_spec f2 gfuns is_closed (name_in_fundefs f2) (FromList FVs_pre) GFuns)
        as [GFuns' [HGFuns'_eq [HGFuns' [Hsquash]]]]; eauto with Ensembles_DB.
      { destruct is_closed, FVs_pre; inv Hclos; constructor; normalize_sets; eauto with Ensembles_DB.
        intros [Hc _]. specialize (Hc p); destruct Hc; now left. }
      { clear - Hdis2. normalize_bound_var_in_ctx. decomp_Disjoint.
        eapply Disjoint_Included_l; [apply name_in_fundefs_bound_var_fundefs|]; auto. }
      apply pre_curry_l; intros [HFVmap' [Hproj_env [Hctx_env Huniq_env]]].
      eapply bind_triple'.
      apply pre_curry_rrr; intros [Hbin1' [Hbin2' Minv']].
      eapply pre_strenghtening; [|eapply H with (Bl := Fnil) (FVs := FVs_pre)].
      { intros ? ? [? [Hres ?]]; exact Hres. }
      { reflexivity. }
      { reflexivity. }
      { subst gfuns'; apply HGFuns'. }
      { (* GFuns' = if is_closed then GFuns ∪ names(f2) else GFuns.
           If not is_closed then follows from Hinv'.
           Else follows from names(f2) # dom(FVmap'). *)
        destruct is_closed.
        - rewrite HGFuns'_eq.
          destruct FVs_pre; [|easy].
          now apply FVmap_inv_empty'.
        - assert (HGFuns_setminus : GFuns \\ name_in_fundefs f2 <--> GFuns). {
            apply Setminus_Disjoint.
            eapply Disjoint_Included_l; [|eapply Disjoint_Included_r; [|apply Hdis2]];
              eauto with Ensembles_DB.
            normalize_bound_var; eapply Included_trans; [apply name_in_fundefs_bound_var_fundefs|].
            eauto with Ensembles_DB. }
          now rewrite HGFuns'_eq, HGFuns_setminus. }
      { (* GFuns' ∪ FVs_pre = GFuns' ∪ (FV(f2) \ GFuns) ⊇ GFuns ∪ (FV(f2) \ GFuns) = FV(f2) *)
        assert (HGFuns_sub : GFuns \subset GFuns'). {
          destruct is_closed; rewrite HGFuns'_eq, ?HGFuns_eq; eauto with Ensembles_DB. }
        eapply Included_trans; [|apply Included_Union_compat; [apply HGFuns_sub|apply Included_refl]].
        rewrite HFVs_pre_eq.
        intros x Hx.
        destruct (gfuns ! x) as [[] |] eqn:Hget_gfuns.
        - left; apply Hgfuns, Hget_gfuns.
        - right; constructor; auto.
          intros Hc; apply Hgfuns in Hc.
          congruence. }
      { eapply binding_not_in_map_antimon; [|eassumption].
        (* ∀ S T, S ⊆ ¬T <==> S ∩ T ⊆ ∅ <==> S # T
           S_env ⊆ S\{Γ'} ⊆ S # FV(Efun f2 e) ⊇ FV(f2) ⊇ filter _ (FV(f2)) = FVs_pre *)
        apply Disjoint_Complement.
        rewrite HFVs_pre_eq.
        assert (HS_env_sub : S_env \subset S \\ [set Γ']). {
          eapply project_vars_free_set_Included; eauto. }
        eapply Disjoint_Included_l; [apply HS_env_sub|].
        eapply Disjoint_Included_l; [apply Setminus_Included|].
        eapply Disjoint_Included_r; [|apply HD1].
        eapply Included_trans; [apply Setminus_Included|].
        unfold used_vars; normalize_occurs_free.
        left; left; right; right; now left. }
      { now inv Huniq. }
      { simpl.
        (* S_env ⊆ S # vars(f2) by HD1.
           FVmap'(names(f2)) = names(f2) because dom(FVmap') = FVs_pre.
           So S # vars(f2) ⊇ names(f2). *)
        assert (Himage : image (to_env FVmap') (name_in_fundefs f2) <--> name_in_fundefs f2). {
          unfold image. apply Ensemble_iff_In_iff; intros arb; unfold In.
          split; intros Hin.
          - destruct Hin as [? [HIn Henv]]. rewrite HFVmap' in Henv; now subst.
          - exists arb; split; auto; now rewrite HFVmap'. }
        rewrite Himage.
        assert (Hused_sub : used_vars_fundefs f2 :|: name_in_fundefs f2 \subset used_vars_fundefs f2). {
          solve_Union_Inc; unfold used_vars_fundefs.
          eapply Included_trans; [apply name_in_fundefs_bound_var_fundefs|]; eauto with Ensembles_DB. }
        eapply Disjoint_Included_r; [eapply Included_Union_compat; [apply Hused_sub|apply Included_refl] |].
        eapply Disjoint_Included_l; [eapply project_vars_free_set_Included; eauto|].
        eapply Disjoint_Included_l; [apply Setminus_Included|].
        splits_Disjoint.
        - eapply Disjoint_Included_r; [|apply HD1].
          normalize_used_vars; eauto with Ensembles_DB.
        - destruct is_closed; rewrite HGFuns'_eq, ?HGFuns_eq; splits_Disjoint; eauto with Ensembles_DB.
          eapply Disjoint_Included_r; [|apply HD1].
          eapply Included_trans; [apply name_in_fundefs_bound_var_fundefs|].
          unfold used_vars; normalize_bound_var; eauto with Ensembles_DB. }
      { simpl.
        (* GFuns' = if is_closed then GFuns ∪ names(f2) else GFuns.
           If not is_closed then follows from Hdis2.
           Else need to show GFuns ∪ names(f2) # BV(f2)\names(f2)
             GFuns # BV(f2)\names(f2) by Hdis2
             names(f2) # BV(f2)\names(f2) by some lemma about Setminus *)
        destruct is_closed; rewrite HGFuns'_eq.
        - splits_Disjoint; eauto with Ensembles_DB.
          normalize_bound_var_in_ctx.
          decomp_Disjoint. apply Disjoint_sym. eauto with Ensembles_DB.
        - eapply Disjoint_Included_l; [apply Setminus_Included|].
          eapply Disjoint_Included_r; [apply Setminus_Included|].
          normalize_bound_var_in_ctx.
          decomp_Disjoint. apply Disjoint_sym. eauto with Ensembles_DB. }
      intros B' s_B'.
      apply pre_curry_l. intros [HbvC_env [Hfresh_B' [Hinc_B' [Hbin1' [Hbin2' Minv']]]]].
      apply pre_curry_rl. intros Hcc_B; simpl in Hcc_B.
      eapply bind_triple'; [eapply pre_strenghtening;
        [|apply H0 with (Funs := name_in_fundefs f2 :|: Funs) (GFuns := GFuns')
            (Scope := Scope \\ name_in_fundefs f2) (FVs := FVs)] |].
      { intros ? ? [Hres ?]; exact Hres. }
      { subst FVmap_n.
        destruct is_closed.
        - rewrite HGFuns'_eq. eapply FVmap_inv_add_closures_closed; eauto with Ensembles_DB.
        - rewrite HGFuns'_eq. eapply FVmap_inv_add_closures_open; eauto with Ensembles_DB.
          rewrite HGFuns_eq; auto. }
      { (* Hbin1 *)
        assert (HGFuns_sub : GFuns \subset GFuns'). {
          destruct is_closed; rewrite HGFuns'_eq, ?HGFuns_eq; eauto with Ensembles_DB. }
        eapply Included_trans.
        2: { apply Included_Union_compat; [|apply Included_refl].
             apply Included_Union_compat; [apply Included_refl|].
             apply HGFuns_sub. }
        clear - Hbin1.
        normalize_occurs_free_in_ctx.
        intros x Hx. specialize (Hbin1 x).
        rewrite !In_or_Iff_Union in *.
        rewrite not_In_Setminus in Hbin1|-*.
        unfold In in *.
        destruct (Decidable_name_in_fundefs f2) as [Hdec].
        destruct (Hdec x) as [Hin|Hnin]; tauto. }
      { (* S_env ∪ {Γ} ⊆ S ∪ {Γ} # dom(FVmap) by Hbin2
           S ∪ {Γ} # names(f2) by HD1, HD2 *)
        assert (HS_sub : S_env \subset S). {
          assert (Henv_sub : S_env \subset S \\ [set Γ'])
            by (eapply project_vars_free_set_Included; eauto).
          eapply Included_trans; [apply Henv_sub|].
          apply Setminus_Included. }
        intros x Hx.
        assert (Hnotin : ~ x \in name_in_fundefs f2). {
          intros Hc. inv Hx.
          - apply HS_sub in H1.
            destruct HD1 as [HD1]; contradiction (HD1 x); constructor; auto.
            left; left; right; unfold used_vars; normalize_bound_var; left; left.
            now apply name_in_fundefs_bound_var_fundefs.
          - inv H1. contradiction HD2. unfold used_vars; normalize_bound_var; left; left.
            now apply name_in_fundefs_bound_var_fundefs. }
        subst FVmap_n.
        eapply add_closures_not_in in Hnotin.
        rewrite Hnotin.
        apply Hbin2.
        inv Hx; [left|right]; auto. }
      { subst gfuns'; apply HGFuns'. }
      { now inv Huniq. }
      { splits_Disjoint; eauto with Ensembles_DB. }
      { (* GFuns' ⊆ GFuns ∪ names(f2)
           So sufficient to show (names(f2) ∪ Funs ∪ GFuns # BV(e))
           Funs ∪ GFuns # BV(e) by Hdis2
           names(f2) # BV(e) by Huniq *)
        assert (HGFuns'_sub : GFuns' \subset GFuns :|: name_in_fundefs f2). {
          destruct is_closed; rewrite HGFuns'_eq, ?HGFuns_eq; eauto with Ensembles_DB. }
        eapply Disjoint_Included_l.
        { apply Included_Union_compat; [apply Included_refl|apply HGFuns'_sub]. }
        splits_Disjoint.
        - eapply Disjoint_Included_l; [apply name_in_fundefs_bound_var_fundefs|].
          apply Disjoint_sym; now inv Huniq.
        - eapply Disjoint_Included_l; [|eapply Disjoint_Included_r; [|apply Hdis2]];
            try normalize_bound_var; eauto with Ensembles_DB.
        - eapply Disjoint_Included_l; [|eapply Disjoint_Included_r; [|apply Hdis2]];
            try normalize_bound_var; eauto with Ensembles_DB.
        - eapply Disjoint_Included_l; [apply name_in_fundefs_bound_var_fundefs|].
          apply Disjoint_sym; now inv Huniq. }
      { (* S_env ⊆ S
           GFuns' ⊆ GFuns ∪ names(f2)
           FVmap_n(names(f2) ∪ Funs\(Scope\names(f2)))
             = FVmap_n(names(f2)) ∪ FVmap_n(Funs\(Scope\names(f2)))
             ⊆ FVmap_n(names(f2)) ∪ FVmap_n(Funs\Scope) ∪ FVmap_n(names(f2)) (Setminus_Setminus_Included)
             = FVmap_n(Funs\Scope) ∪ FVmap_n(names(f2))
             = FVmap(Funs\Scope) ∪ {Γ'} (by HFVmap_n and fact that names(f2) # Funs\Scope by Hdis2)
           names(f2) ∪ Funs\(Scope\names(f2)) ∪ GFuns' ∪ vars(e) ∪ {Γ} ∪ FVmap(Funs\Scope) # S by HD1
           Γ' ∉ S_env by Hran_Γ', Hfresh_B', Hinc_B' *)
        assert (HS_sub : S_env \subset S). {
          assert (Henv_sub : S_env \subset S \\ [set Γ'])
            by (eapply project_vars_free_set_Included; eauto).
          eapply Included_trans; [apply Henv_sub|].
          apply Setminus_Included. }
        assert (HGFuns'_sub : GFuns' \subset GFuns :|: name_in_fundefs f2). {
          destruct is_closed; rewrite HGFuns'_eq, ?HGFuns_eq; eauto with Ensembles_DB. }
        assert (Hsub : (name_in_fundefs f2 :|: Funs \\ (Scope \\ name_in_fundefs f2))
                         \subset name_in_fundefs f2 :|: (Funs \\ Scope)). {
          eapply Included_trans; [apply Setminus_Setminus_Included|]; eauto with Decidable_DB.
          rewrite Setminus_Union_distr.
          rewrite <- Union_assoc, Union_commut, <- Union_assoc.
          rewrite Union_commut with (s2 := _ \\ _).
          rewrite Union_Same_set with (s1 := _ \\ _) (s2 := name_in_fundefs f2) by eauto with Ensembles_DB.
          eauto with Ensembles_DB. }
        splits_Disjoint.
        - eapply Disjoint_Included_l; [apply HS_sub|].
          eapply Disjoint_Included_r; [apply Hsub|].
          splits_Disjoint.
          + eapply Disjoint_Included_r; [|apply HD1].
            unfold used_vars; normalize_bound_var.
            eapply Included_trans; [apply name_in_fundefs_bound_var_fundefs|]; eauto with Ensembles_DB.
          + now decomp_Disjoint.
        - eapply Disjoint_Included_l; [apply HS_sub|].
          eapply Disjoint_Included_r; [apply HGFuns'_sub|]; splits_Disjoint.
          + decomp_Disjoint; eauto.
          + eapply Disjoint_Included_r; [|apply HD1]; unfold used_vars.
            normalize_bound_var; eapply Included_trans; [apply name_in_fundefs_bound_var_fundefs|].
            eauto with Ensembles_DB.
        - eapply Disjoint_Included_l; [apply HS_sub|].
          eapply Disjoint_Included_r; [|apply HD1].
          normalize_used_vars; eauto with Ensembles_DB.
        - eapply Disjoint_Included_l; [apply HS_sub|].
          eapply Disjoint_Included_r; [|apply HD1]; eauto with Ensembles_DB.
        - eapply Disjoint_Included_r.
          { apply image_monotonic. apply Hsub. }
          assert (Hset_eq : name_in_fundefs f2 :|: (Funs \\ Scope) <-->
            name_in_fundefs f2 :|: ((Funs \\ Scope) \\ name_in_fundefs f2)). {
            split; intros x Hx.
            - inv Hx; auto.
              destruct (Decidable_name_in_fundefs f2) as [Hdec].
              destruct (Hdec x) as [Hin|Hnin]; [now left|right].
              constructor; auto.
            - inv Hx; auto.
              right; inv H1; auto. }
          rewrite Hset_eq.
          rewrite image_Union.
          splits_Disjoint.
          + subst FVmap_n. eapply Disjoint_Included_r; [apply add_closures_image|].
            eapply Disjoint_Included_l; [eapply project_vars_free_set_Included; eauto|].
            eauto with Ensembles_DB.
          + subst FVmap_n. eapply Disjoint_Included_r; [apply add_closures_minus_names_image|].
            eapply Disjoint_Included_l; [apply HS_sub|].
            now decomp_Disjoint. }
      { (* HD2 *) intros Hc; apply HD2; normalize_used_vars; now right. }
      intros e' s_e'; apply return_triple.
      intros _ s_final [[Hfresh_e' [HbvB' [Hinc_e' Huniq_B']]]
                          [Hfresh_final [C_e' [Hctx_e' [Hcc_e' [HbvC_e' [Hinc_final [Hbv_e' Huniq_e']]]]]]]].
      split; [eapply fresh_inc; [|eassumption]; zify; lia|].
      exists (comp_ctx_f C_env (Econstr_c Γ' c' FVs' Hole_c)); splits.
      + simpl; unfold is_exp_ctx; intros expr. now rewrite Hctx_env.
      + simpl. unfold is_exp_ctx in Hctx_e'; rewrite Hctx_e'.
        eapply CC_Efun with (GFuns' := GFuns') (FVs' := FVs_pre) (S1 := S \\ [set Γ']) (S1' := S_env)
                            (S3 := [set Γ'])
                            (S2 := Empty_set _).
        * (* HFVs_pre *) now rewrite HFVs_pre_eq.
        * (* PS.elements produces (NoDupA eq) lists *)
          subst; apply filter_NoDup, NoDupA_NoDup, PS.elements_spec2w.
        * (* Funs\Scope # S, GFuns # S, FVmap(Funs\Scope) # S, {Γ} # S by HD1
             Scope # S by Minv, Hbin2
             Sufficient to show FVs\Scope\Funs\GFuns # S, which follows from Hbin2 and Minv *)
          eapply Disjoint_Included_l; [apply Setminus_Included|].
          eapply FV_preserves_disjoint_inv; eauto.
        * assumption.
        * (* Γ' ∈ S
             S # BV(Efun f2 e) ∪ GFuns ∪ FVmap(Funs\Scope) ∪ {Γ} by HD1
             S # Scope ∪ FVs by similar argument as 2 cases above *)
          eapply Disjoint_Included_l; [apply Singleton_Included; apply HΓ'|].
          assert (HFunsScope : Disjoint _ S (Funs \\ Scope)) by now decomp_Disjoint.
          assert (HGFuns : Disjoint _ S GFuns) by now decomp_Disjoint.
          assert (Himage : Disjoint _ S (image (to_env FVmap) (Funs \\ Scope))) by now decomp_Disjoint.
          assert (HΓ : Disjoint _ S [set Γ]) by now decomp_Disjoint.
          assert (HScope : Disjoint _ S Scope). {
            constructor; intros x Hx; inv Hx.
            rename H1 into HS, H2 into HScope.
            destruct Minv as [[Hinv _] _].
            apply Hinv in HScope; unfold In in HScope.
            specialize (Hbin2 x).
            rewrite Hbin2 in HScope; [easy|].
            now left. }
          splits_Disjoint; auto.
          -- unfold used_vars in HD1; now decomp_Disjoint.
          -- constructor; intros x Hx; inv Hx; rename H1 into HS, H2 into HFVs.
             destruct Minv as [_ [_ Hinv]].
             assert (HScope' : ~ x \in Scope) by (eapply Disjoint_In_l; eauto).
             assert (HFuns' : ~ x \in Funs). {
               intros HFuns.
               destruct HFunsScope as [HFunsScope]; contradiction (HFunsScope x).
               constructor; auto; constructor; auto. }
             assert (HGFuns'' : ~ x \in GFuns) by (eapply Disjoint_In_l; eauto).
             apply In_nthN in HFVs. destruct HFVs as [n HFVs].
             specialize (Hinv n x).
             destruct Hinv as [Hinv _].
             specialize (Hinv (conj HFVs (conj HScope' (conj HFuns' HGFuns'')))).
             specialize (Hbin2 x).
             rewrite Hbin2 in Hinv; [easy|].
             now left.
        * constructor.
        * eauto with Ensembles_DB.
        * assumption.
        * assumption.
        * assert (Hmap_eq : f_eq_subdomain ((name_in_fundefs f2 :|: Funs) \\ (Scope \\ name_in_fundefs f2))
              (to_env FVmap_n) (extend_fundefs' (to_env FVmap) f2 Γ')). {
            subst FVmap_n. eapply f_eq_subdomain_antimon; [|apply add_closures_spec].
            intros x Hx; unfold In; auto. }
          eapply Closure_conversion_f_eq_subdomain; [|eassumption].
          eassumption.
      + repeat normalize_bound_var_ctx; normalize_sets.
        (* BV(C_env) ⊆ [s_Γ', s_final) by HbvC_env
           {Γ'} ⊆ [s_Γ', s_env) ⊆ [s_Γ', s_final) by Hran_Γ' and Hinc* *)
        solve_Union_Inc.
        * eapply Included_trans; [apply HbvC_env|]. intros x Hx; unfold In, Range in *; zify; lia.
        * intros x Hx; inv Hx; unfold In, Range in *; zify; lia.
      + zify; lia.
      + simpl; unfold is_exp_ctx in Hctx_e'; rewrite Hctx_e'; repeat normalize_bound_var.
        rewrite bound_var_app_ctx.
        solve_Union_Inc.
        * eapply Included_trans; [apply HbvB'|]; solve_Union_Inc.
          intros x Hx; right; unfold In, Range in *; zify; lia.
        * eapply Included_trans; [apply HbvC_e'|]; solve_Union_Inc.
          intros x Hx; right; unfold In, Range in *; zify; lia.
        * eapply Included_trans; [apply Hbv_e'|]; solve_Union_Inc.
          intros x Hx; right; unfold In, Range in *; zify; lia.
      + simpl; unfold is_exp_ctx in Hctx_e'; rewrite Hctx_e'.
        rewrite <- app_ctx_f_fuse; simpl.
        rewrite (proj1 (ub_app_ctx_f _)); splits; auto.
        * apply unique_bindings_c_comp_inv in Huniq_env.
          destruct Huniq_env as [HuniqC_env [HuniqC_constr Hdis_env]]; auto.
        * constructor; auto.
          2: constructor; auto.
          1: change (~ ?S ?x) with (~ x \in S).
          all: repeat normalize_bound_var; rewrite bound_var_app_ctx.
          -- rewrite !Union_demorgan; splits.
             ++ intros Hc. apply HbvB' in Hc. inv Hc.
                ** destruct HD1 as [HD1]; contradiction (HD1 Γ').
                   constructor; [apply HS_Γ'; unfold Range, In in *; zify; lia|].
                   unfold used_vars; normalize_bound_var; constructor; left; right; left; now left.
                ** unfold In, Range in *; zify; lia.
             ++ intros Hc; apply HbvC_e' in Hc; unfold In, Range in *; zify; lia.
             ++ intros Hc; apply Hbv_e' in Hc; inv Hc.
                ** destruct HD1 as [HD1]; contradiction (HD1 Γ').
                   constructor; [apply HS_Γ'; unfold Range, In in *; zify; lia|].
                   unfold used_vars; normalize_bound_var; constructor; left; right; left; now right.
                ** unfold In, Range in *; zify; lia.
          -- splits_Disjoint.
             ++ eapply Disjoint_Included_l; [apply HbvC_e'|].
                eapply Disjoint_Included_r; [apply HbvB'|]; splits_Disjoint.
                ** constructor; intros x Hx; inv Hx.
                   destruct HD1 as [HD1]; contradiction (HD1 x).
                   constructor; [apply HS_Γ'; unfold Range, In in *; zify; lia|].
                   unfold used_vars; normalize_bound_var; constructor; left; right; left; now left.
                ** constructor; intros x Hx; inv Hx; unfold Range, In in *; zify; lia.
             ++ eapply Disjoint_Included_l; [apply Hbv_e'|].
                eapply Disjoint_Included_r; [apply HbvB'|]; splits_Disjoint.
                ** now inv Huniq.
                ** constructor; intros x Hx; inv Hx.
                   destruct HD1 as [HD1]; contradiction (HD1 x).
                   constructor; [apply HS_Γ'; unfold Range, In in *; zify; lia|].
                   unfold used_vars; normalize_bound_var; constructor; left; right; left; now left.
                ** constructor; intros x Hx; inv Hx.
                   destruct HD1 as [HD1]; contradiction (HD1 x).
                   constructor; [apply HS_Γ'; unfold Range, In in *; zify; lia|].
                   unfold used_vars; normalize_bound_var; constructor; left; right; left; now right.
                ** constructor; intros x Hx; inv Hx; unfold Range, In in *; zify; lia.
        * repeat normalize_bound_var; rewrite bound_var_app_ctx.
          splits_Disjoint.
          -- eapply Disjoint_Included_l; [apply HbvC_env|].
             eapply Disjoint_Included_r; [apply HbvB'|].
             splits_Disjoint.
             ++ constructor; intros x Hx; inv Hx.
                destruct HD1 as [HD1]; contradiction (HD1 x).
                constructor; [apply HS_Γ'; unfold Range, In in *; zify; lia|].
                unfold used_vars; normalize_bound_var; constructor; left; right; left; now left.
             ++ constructor; intros x Hx; inv Hx; unfold Range, In in *; zify; lia.
          -- eapply Disjoint_Included_l; [apply HbvC_env|].
             eapply Disjoint_Included_r; [apply HbvC_e'|].
             constructor; intros x Hx; inv Hx; unfold Range, In in *; zify; lia.
          -- eapply Disjoint_Included_l; [apply HbvC_env|].
             eapply Disjoint_Included_r; [apply Hbv_e'|].
             splits_Disjoint.
             ++ constructor; intros x Hx; inv Hx.
                destruct HD1 as [HD1]; contradiction (HD1 x).
                constructor; [apply HS_Γ'; unfold Range, In in *; zify; lia|].
                unfold used_vars; normalize_bound_var; constructor; left; right; left; now right.
             ++ constructor; intros x Hx; inv Hx; unfold Range, In in *; zify; lia.
          -- eapply Disjoint_Included_l; [apply HbvC_env|].
             constructor; intros x Hx; inv Hx. inv H2. unfold In, Range in *; zify; lia.
    - eapply bind_triple'.
      + eapply get_var_project_var_sound; try eassumption.
        eapply Included_trans; [|apply Hbin1].
        normalize_occurs_free...
      + intros [x f] s1.
        apply pre_curry_l; intros Hfresh.
        eapply pre_existential. intros C1.
        eapply pre_existential. intros S'.
        eapply pre_curry_l. intros [Hvar [Hctx1 Huniq1]].
        eapply bind_triple'.
        * eapply pre_strenghtening; [|eapply get_vars_project_vars_sound].
          { intros ? ? [Hres ?]; exact Hres. }
          all: try eassumption.
          eapply Included_trans; [|apply Hbin1].
          normalize_occurs_free...
        * intros [xs f'] s2.
          eapply pre_curry_l. intros Hfresh'.
          eapply pre_existential. intros C2.
          eapply pre_existential. intros S''.
          eapply pre_curry_l. intros [Hvars [Hctx2 Huniq2]].
          eapply bind_triple'.
          eapply pre_strenghtening; [|eapply get_name_spec].
          { intros ? ? [Hres ?]; exact Hres. }
          intros x' i. eapply pre_curry_l. intros [Hfresh'' Hf1].
          eapply bind_triple'; [eapply pre_strenghtening; [|eapply get_name_spec] |].
          { intros ? ? [? [? [? Hres]]]; exact Hres. }
          intros x'' s3. eapply pre_curry_l. intros Hf2.
          eapply return_triple.
          intros _ s5 Hf5. simpl.
          split; [eapply fresh_inc; [|eassumption]; zify; lia|].
          exists (comp_ctx_f C1 C2); splits.
          { intros e. rewrite <- app_ctx_f_fuse. congruence. }
          { eapply CC_Eapp with (S := S).
            - eapply FV_preserves_disjoint_inv; eauto.
            - econstructor; eassumption.
            - intuition.
            - (* Hf5 *) destruct Hf5 as [Hf5 _]. now inv Hf5.
            - (* Ranges in Hf2, Hf5 *) intros Hc; subst; decompose [and] Hf2; decompose [and] Hf5.
              unfold Range, In in *; zify; lia. }
          { (* Ranges and Hf1, HF5 *)
            normalize_bound_var_ctx; solve_Union_Inc.
            - eapply Included_trans; [apply (proj1 (proj2 Hfresh'))|].
              intros x''' Hx; unfold Range, In in *; zify; lia.
            - eapply Included_trans; [apply (proj1 Hf1)|].
              intros x''' Hx; unfold Range, In in *; zify; lia. }
          { zify; lia. }
          { repeat normalize_bound_var; repeat normalize_sets.
            (* Ranges in Hf2, Hf5 *)
            solve_Union_Inc; intros arb Harb; inv Harb; unfold In, Range in *; zify; lia. }
          { rewrite <- app_ctx_f_fuse.
            destruct Hfresh' as [Hfresh' [HbvC1 HincC1]].
            destruct Hf1 as [HbvC2 HincC2].
            destruct Hf2 as [Hx' [Hran_x' [Hinc_x' Hfresh_x']]].
            destruct Hf5 as [Hx'' [Hran_x'' [Hinc_x'' Hfresh_x'']]].
            rewrite (proj1 (ub_app_ctx_f _)); splits; auto.
            rewrite (proj1 (ub_app_ctx_f _)); splits; auto.
            - constructor; auto.
              2: constructor; auto.
              3: constructor.
              all: change (~ ?S ?x) with (~ x \in S); repeat normalize_bound_var; repeat normalize_sets.
              + intros Hc; inv Hc. inv Hx''. now contradiction H0.
              + inversion 1.
            - repeat normalize_bound_var; repeat normalize_sets; splits_Disjoint.
              + eapply Disjoint_Included_l; [apply HbvC2|].
                constructor; intros arb Harb; inv Harb. inv H0. unfold In, Range in *; zify; lia.
              + eapply Disjoint_Included_l; [apply HbvC2|].
                constructor; intros arb Harb; inv Harb. inv H0. unfold In, Range in *; zify; lia.
            - rewrite bound_var_app_ctx; repeat normalize_bound_var; repeat normalize_sets.
              splits_Disjoint.
              + eapply Disjoint_Included_l; [apply HbvC1|].
                eapply Disjoint_Included_r; [apply HbvC2|].
                constructor; intros arb Harb; inv Harb; unfold In, Range in *; zify; lia.
              + eapply Disjoint_Included_l; [apply HbvC1|].
                constructor; intros arb Harb; inv Harb. inv H0. unfold In, Range in *; zify; lia.
              + eapply Disjoint_Included_l; [apply HbvC1|].
                constructor; intros arb Harb; inv Harb. inv H0. unfold In, Range in *; zify; lia. }
    - eapply bind_triple'.
      + eapply H with (Scope := Union var (Singleton var v) Scope)
        (S := S)
        (FVmap := Maps.PTree.set v BoundVar FVmap).
        * eapply FVmap_inv_set_bound. eassumption.
        * (* Hbin1 *)
          clear - Hbin1.
          normalize_occurs_free_in_ctx.
          intros x Hx. specialize (Hbin1 x).
          rewrite !In_or_Iff_Union in *.
          rewrite not_In_Setminus in Hbin1.
          unfold In in *.
          destruct (peq v x); [subst; left; left; left; now left|].
          assert (~ [set v] x) by (intros Hc; inv Hc; congruence).
          tauto.
        * eapply binding_not_in_map_antimon.
          now apply Included_refl.
          eapply binding_not_in_map_set_not_In_S. eassumption.
          intros Hc; inv Hc.
          { eapply HD1; eauto. constructor; eauto.
            normalize_used_vars; left; left; right; now left. }
          { inv H0; contradiction HD2; normalize_used_vars. now left. }
        * assumption.
        * now inv Huniq.
        * splits_Disjoint; auto.
          constructor; intros x Hx; inv Hx. inv H1.
          destruct Hdis2 as [Hdis2]; contradiction (Hdis2 x); constructor; auto.
        * eapply Disjoint_Included_r; [|apply Hdis2]; normalize_bound_var; eauto with Ensembles_DB.
        * eapply Disjoint_Included_l. now apply Included_refl.
          eapply Disjoint_Included_r; [| eassumption ].
          apply Included_Union_compat.
          -- normalize_used_vars. solve_Union_Inc.
          -- rewrite <- to_env_BoundVar_f_eq, Union_commut, <- Setminus_Union.
             now eapply image_Setminus_extend.
        * (* Follows from HD2 *)
          intros Hc; contradiction HD2; normalize_used_vars; now right.
      + intros e' s'. eapply return_triple.
        intros _ s'' [Hfresh' [Hfresh'' [C' [Hctx' [Hcc [HbvC' [Hinc' [Hbve' Huniq'']]]]]]]]; eauto.
        split; [eapply fresh_inc; [|eassumption]; zify; lia|].
        cbn. exists Hole_c; splits.
        { cbn. red. reflexivity. }
        { simpl. unfold is_exp_ctx in Hctx'. rewrite Hctx'. econstructor.
          - eapply FV_preserves_disjoint_inv; eauto.
          - eapply Closure_conversion_f_eq_subdomain. eassumption.
            rewrite <- to_env_BoundVar_f_eq. apply f_eq_subdomain_extend_not_In_S_l.
            intros Hc. inv Hc. now eauto. reflexivity. }
        { (* HbvC and s'' > s' *)
           intros x Hx. inv Hx. }
        { zify; lia. }
        { simpl; normalize_bound_var. unfold is_exp_ctx in Hctx'; rewrite Hctx'.
          rewrite bound_var_app_ctx. solve_Union_Inc.
          eapply Included_trans; [apply Hbve'|]; normalize_bound_var; solve_Union_Inc. }
        { simpl. rewrite Hctx'.
          constructor; eauto.
          change (~ ?S ?x) with (~ x \in S); rewrite bound_var_app_ctx.
          intros Hc; inv Hc.
          ** apply HbvC' in H0.
             destruct HD1 as [HD1]. contradiction (HD1 v).
             constructor; [|normalize_used_vars; left; left; right; now left].
             apply Hfresh'. unfold Range, In in *; lia.
          ** apply Hbve' in H0. inv H0.
             --- now inv Huniq.
             --- destruct HD1 as [HD1]. contradiction (HD1 v).
                 constructor; [|normalize_used_vars; left; left; right; now left].
                 apply Hfresh'; unfold Range, In in *; zify; lia. }

    - eapply bind_triple'.
      + eapply get_vars_project_vars_sound; try eassumption.
        intros x Hx. eapply Hbin1. eauto.
      + intros [xs f] s.
        eapply pre_curry_l; intros Hfresh.
        eapply pre_existential. intros C1.
        eapply pre_existential. intros S'.
        eapply pre_curry_l. intros [Hproj [Hctx Huniq']].
        eapply bind_triple'; [eapply pre_strenghtening|].
        { intros ? ? [Hres ?]; exact Hres. }
        eapply H with (Scope := Union var (Singleton var v) Scope)
                      (S := S')
                      (FVmap := Maps.PTree.set v BoundVar FVmap).
        * eapply FVmap_inv_set_bound. eassumption.
        * (* Hbin1 *)
          clear - Hbin1.
          normalize_occurs_free_in_ctx.
          intros x Hx. specialize (Hbin1 x).
          rewrite !In_or_Iff_Union in *.
          rewrite not_In_Setminus in Hbin1.
          unfold In in *.
          destruct (peq v x); [subst; left; left; left; now left|].
          assert (~ [set v] x) by (intros Hc; inv Hc; congruence).
          tauto.
        * eapply binding_not_in_map_antimon.
          apply Included_Union_compat.
          eapply project_vars_free_set_Included; now eauto.
          now apply Included_refl.
          eapply binding_not_in_map_set_not_In_S. eassumption.
          intros Hc; inv Hc.
          { eapply HD1; eauto. constructor; eauto.
            normalize_used_vars; left; left; right; left; now left. }
          { inv H0; contradiction HD2; normalize_used_vars; now do 2 left. }
        * assumption.
        * now inv Huniq.
        * splits_Disjoint; auto.
          constructor; intros x Hx; inv Hx. inv H1.
          destruct Hdis2 as [Hdis2]; contradiction (Hdis2 x); constructor; auto.
        * eapply Disjoint_Included_r; [|apply Hdis2]; normalize_bound_var; eauto with Ensembles_DB.
        * eapply Disjoint_Included_l. eapply project_vars_free_set_Included; now eauto.
          eapply Disjoint_Included_r; [| eassumption ].
          apply Included_Union_compat.
          -- normalize_used_vars. solve_Union_Inc.
          -- rewrite <- to_env_BoundVar_f_eq, Union_commut, <- Setminus_Union.
             now eapply image_Setminus_extend.
        * (* Follows from HD2 *)
          intros Hc; contradiction HD2; normalize_used_vars; now right.
        * intros e' s'. eapply return_triple.
          intros _ s'' [[Hfresh' [HbvC Hinc]] [Hfresh'' [C' [Hctx' [Hcc [HbvC' [Hinc' [Hbve' Huniq'']]]]]]]]; eauto.
          split; [eapply fresh_inc; [|eassumption]; zify; lia|].
          eexists; splits.
          { now eapply Hctx. }
          { simpl. unfold is_exp_ctx in Hctx'. rewrite Hctx'. econstructor; [| eassumption |].
            - eapply FV_preserves_disjoint_inv; eauto.
            - eapply Closure_conversion_f_eq_subdomain. eassumption.
              rewrite <- to_env_BoundVar_f_eq. apply f_eq_subdomain_extend_not_In_S_l.
              intros Hc. inv Hc. now eauto. reflexivity. }
          { (* HbvC and s'' > s' *)
            eapply Included_trans; [apply HbvC|]; intros x Hx; unfold Range, In in *; zify; lia. }
          { zify; lia. }
          { simpl; normalize_bound_var. unfold is_exp_ctx in Hctx'; rewrite Hctx'.
            rewrite bound_var_app_ctx. solve_Union_Inc.
            - eapply Included_trans; [apply HbvC'|]. right; unfold Range, In in *; zify; lia.
            - eapply Included_trans; [apply Hbve'|]; normalize_bound_var; solve_Union_Inc.
              right; unfold Range, In in *; zify; lia. }
          { simpl. rewrite Hctx'.
             rewrite (proj1 (ub_app_ctx_f _)); splits; auto.
             ++ constructor; auto.
                change (~ ?S ?x) with (~ x \in S); rewrite bound_var_app_ctx.
                intros Hc; inv Hc.
                ** apply HbvC' in H0.
                   destruct HD1 as [HD1]. contradiction (HD1 v).
                   constructor; [|normalize_used_vars; left; left; right; left; now left].
                   apply Hfresh. unfold Range, In in *; zify; lia.
                ** apply Hbve' in H0. inv H0.
                   --- now inv Huniq.
                   --- destruct HD1 as [HD1]. contradiction (HD1 v).
                       constructor; [|normalize_used_vars; left; left; right; left; now left].
                       apply Hfresh; unfold Range, In in *; zify; lia.
             ++ normalize_bound_var.
                rewrite bound_var_app_ctx.
                decomp_Disjoint; splits_Disjoint.
                ** eapply Disjoint_Included_l; [|eapply Disjoint_Included_r]; try eassumption.
                   constructor; intros x'; intros Hc; inv Hc; unfold In, Range in *; zify; lia.
                ** eapply Disjoint_Included_l; [|eapply Disjoint_Included_r]; try eassumption.
                   apply Union_Disjoint_r.
                   --- assert (HSdis : Range (next_var (fst s)) (next_var (fst s')) \subset S). {
                         intros x' Hx; apply Hfresh; unfold Range, In in *; zify; lia. }
                       eapply Disjoint_Included_l; [apply HSdis|].
                       unfold used_vars in *.
                       eapply Disjoint_Included_r; [|apply H3].
                       normalize_bound_var...
                   --- constructor; intros x' Hx; inv Hx; unfold Range, In in *; zify; lia.
                ** eapply Disjoint_Included_l; [apply HbvC|].
                   constructor; intros x' Hx; inv Hx. inv H8. destruct H3 as [Hc].
                   contradiction (Hc x'); constructor.
                   --- apply Hfresh; unfold Range, In in *; zify; lia.
                   --- normalize_used_vars; left; now left. }
    - eapply bind_triple'. eapply get_var_project_var_sound; eauto.
      { eapply Included_trans; [|apply Hbin1]. normalize_occurs_free... }
      intros [x f] s1. apply return_triple.
      intros _ s2 [Hfresh [C [S' [[Hproj [Hctx Huniq']] Hf]]]].
      split; [eapply fresh_inc; [|eassumption]; zify; lia|].
      eexists; splits.
      + eassumption.
      + simpl. econstructor; try eassumption.
        eapply FV_preserves_disjoint_inv; eauto.
      + intuition.
      + zify; lia.
      + simpl; normalize_bound_var; eauto with Ensembles_DB.
      + simpl. rewrite (proj1 (ub_app_ctx_f _)); splits; auto.
        * constructor.
        * normalize_bound_var; eauto with Ensembles_DB.
    - eapply bind_triple'; [apply get_named_str_fresh|].
      intros Γ s_Γ. apply pre_curry_l; intros Hfresh_Γ.
      apply pre_curry_l; intros HS_Γ.
      pose (Huniq_whole := Huniq); clearbody Huniq_whole.
      eapply fundefs_append_unique_bindings_l in Huniq; [|symmetry; apply HB].
      destruct Huniq as [Huniq_Bl [Huniq Hdis_Bl]].
      eapply bind_triple'; [eapply pre_strenghtening;
        [|eapply H with (FVs := FVs) (Funs := name_in_fundefs Bg) (Scope := FromList l)] |].
      { intros ? ? [? [? Hres]]; exact Hres. }
      { rewrite <- (FVmap_inv_Scope_Proper _ _ eq_refl _ _ (Union_Empty_set_neut_l _ _)
                                          _ _ eq_refl _ _ eq_refl _ _ eq_refl).
        apply FVmapInv_add_params.
        eapply FVmap_inv_add_closures_open with (Γ := Γ) (B := Bg) in Minv; [|reflexivity].
        repeat normalize_sets. apply Minv. }
      { (* Follows from Hbin1. useful lemma: occurs_free_in_fun *)
        eapply Included_trans; [eapply (occurs_free_in_fun v t l e Bg)|].
        - subst Bg.
          change (?f ?x) with (x \in f).
          rewrite fundefs_append_fun_in_fundefs by reflexivity.
          right; now left.
        - solve_Union_Inc.
          eapply Included_trans; [apply Hbin1|]; eauto with Ensembles_DB. }
      { (* S\{Γ} ∪ {Γ} ⊆ S ∪ {Γ} ⊆ S by HS_Γ
           S # l ∪ names(Bg) ∪ dom(FVmap) ⊇ dom(add_params l (add_closures f5 FVmap)) by HD1 *)
        assert (Hsub : S \\ [set Γ] :|: [set Γ] \subset S). {
          intros x Hx; inv Hx; now inv H1. }
        eapply binding_not_in_map_antimon; [apply Hsub|].
        intros x Hx.
        destruct (Decidable_FromList l) as [Hdec_l]; destruct (Hdec_l x) as [Hin_l|Hnin_l].
        { destruct HD1 as [HD1]; contradiction (HD1 x); constructor; auto.
          subst Bg; rewrite fundefs_append_used_vars by reflexivity; normalize_used_vars.
          left; left; right; left; left; now right. }
        rewrite add_params_irrelevant' by auto.
        rewrite add_closures_irrelevant.
        - now apply Hbin2.
        - intros Hc. destruct HD1 as [HD1]; contradiction (HD1 x); constructor; auto.
          left; left; left; apply name_in_fundefs_bound_var_fundefs; auto. }
      { eassumption. }
      { now inv Huniq. }
      { subst Bg. rewrite fundefs_append_name_in_fundefs; [|reflexivity].
        splits_Disjoint.
        - eapply Disjoint_Included_l; [apply name_in_fundefs_bound_var_fundefs|].
          eapply Disjoint_Included_r; [|apply Hdis_Bl].
          normalize_bound_var; eauto with Ensembles_DB.
        - simpl. inv Huniq. splits_Disjoint; eauto with Ensembles_DB.
          eapply Disjoint_Included_l; [apply name_in_fundefs_bound_var_fundefs|]; auto. }
      { splits_Disjoint.
        - subst Bg. rewrite fundefs_append_name_in_fundefs by reflexivity.
          splits_Disjoint.
          + eapply Disjoint_Included_l; [apply name_in_fundefs_bound_var_fundefs|].
            eapply Disjoint_Included_r; [|apply Hdis_Bl].
            normalize_bound_var; eauto with Ensembles_DB.
          + simpl. inv Huniq. splits_Disjoint; eauto with Ensembles_DB.
            eapply Disjoint_Included_l; [apply name_in_fundefs_bound_var_fundefs|].
            now apply Disjoint_sym.
        - eapply Disjoint_Included_r; [|apply HD2].
          intros x Hx; constructor.
          + subst Bg. rewrite fundefs_append_bound_vars by reflexivity.
            right; normalize_bound_var; right; right; now left.
          + intros Hc. subst Bg; rewrite fundefs_append_name_in_fundefs in Hc by reflexivity.
            inv Hc.
            * destruct Hdis_Bl as [Hdis_Bl]; contradiction (Hdis_Bl x); constructor; auto.
              now apply name_in_fundefs_bound_var_fundefs.
            * inv Huniq. simpl in H1. inv H1.
              -- now inv H2.
              -- destruct H11 as [Hoops]; contradiction (Hoops x); constructor; auto.
                 now apply name_in_fundefs_bound_var_fundefs. }
      { (* S # names(Bg), S # GFuns, S # vars(e) by HD1
           S\{Γ] # {Γ} by some setminus lemma
           Finally (add_params l (add_closures Bg FVmap Γ))(names(Bg)) ⊆ {Γ} ∪ names(Bg)
             S\{Γ} # {Γ} as above
             S # names(Bg) by HD1 *)
        splits_Disjoint.
        - eapply Disjoint_Included_l; [|eapply Disjoint_Included_r; [|apply HD1]]; eauto with Ensembles_DB.
          apply Setminus_Included_Included_Union.
          eapply Included_trans; [apply name_in_fundefs_bound_var_fundefs|].
          unfold used_vars_fundefs...
        - eapply Disjoint_Included_l; [|eapply Disjoint_Included_r; [|apply HD1]]; eauto with Ensembles_DB.
        - eapply Disjoint_Included_l; [|eapply Disjoint_Included_r; [|apply HD1]]; eauto with Ensembles_DB.
          subst Bg; rewrite fundefs_append_used_vars by reflexivity; normalize_used_vars...
        - eauto with Ensembles_DB.
        - eapply Disjoint_Included_r; [apply add_params_image|].
          eapply Disjoint_Included_r.
          { apply Included_Union_compat; [apply Included_refl|apply add_closures_image']. }
          splits_Disjoint.
          + eapply Disjoint_Included_l; [|eapply Disjoint_Included_r; [|apply HD1]]; eauto with Ensembles_DB.
            subst Bg; rewrite fundefs_append_used_vars by reflexivity; normalize_used_vars.
            eauto 10 with Ensembles_DB.
          + eauto with Ensembles_DB.
          + eapply Disjoint_Included_l; [|eapply Disjoint_Included_r; [|apply HD1]]; eauto with Ensembles_DB.
            eapply Included_trans; [apply image_monotonic, Setminus_Included|].
            rewrite HFuns... }
      { (* HS_Γ, HD1 *)
        intros Hc; destruct HD1 as [HD1]; contradiction (HD1 Γ); constructor; auto.
        subst Bg. rewrite fundefs_append_used_vars by reflexivity. normalize_used_vars.
        left; left. right. left. now right. }
      intros e' s_e'.
      apply pre_curry_l. intros [HΓ_ran [Hinc_e' Hfresh_e']].
      apply pre_existential_r; intros C_e.
      apply pre_curry_rl; intros Hctx_e.
      apply pre_curry_rl; intros Hcc_e.
      eapply bind_triple'; [eapply pre_strenghtening;
        [|eapply H0 with (FVs := FVs) (Bg := Bg) (Bl := fundefs_append Bl (Fcons v t l e Fnil))] |].
      { intros ? ? [Hres ?]; exact Hres. }
      { rewrite <- fundefs_append_assoc; simpl. now subst Bg. }
      { eassumption. }
      { eassumption. }
      { eassumption. }
      { eassumption. }
      { eapply binding_not_in_map_antimon; [|eassumption]. eauto with Ensembles_DB. }
      { assumption. }
      { eapply Disjoint_Included_l; eauto... }
      { assumption. }
      intros B' s_B'; apply return_triple.
      intros _ s_final [[Hfresh_B' [HbvC_e [Hinc_B' [Hbv_e' Huniq_e']]]]
                          [Hfresh_final [Hcc_B' [Hbv_B' [Hinc_final' Huniq_B']]]]].
      split; [eapply fresh_inc; [|eassumption]; zify; lia|].
      unfold is_exp_ctx in Hctx_e; rewrite Hctx_e.
      splits.
      + eapply CC_Fcons with (FVs := FVs); auto.
        * (* HS_Γ, HD1 *)
          assert (HΓ_sub : [set Γ] \subset S). {
            intros x Hx; inv Hx. apply HS_Γ. }
          eapply Disjoint_Included_l; [apply HΓ_sub|].
          decomp_Disjoint; splits_Disjoint; eauto with Ensembles_DB.
          -- eapply Disjoint_Included_r; [apply name_in_fundefs_bound_var_fundefs|].
             eapply Disjoint_Included_r; [|apply H1].
             unfold used_vars_fundefs; eauto with Ensembles_DB.
          -- eapply Disjoint_Included_r; [|apply H1].
             subst Bg; rewrite fundefs_append_used_vars by reflexivity.
             normalize_used_vars; eauto with Ensembles_DB.
          -- eapply Disjoint_Included_r; [|apply H1].
             subst Bg; rewrite fundefs_append_used_vars by reflexivity.
             normalize_used_vars; eauto with Ensembles_DB.
        * (* We can get rid of (add_params l) because domain excludes l *)
          assert (Hfeq : f_eq_subdomain (name_in_fundefs Bg \\ FromList l)
                                        (to_env (add_params l (add_closures Bg FVmap Γ)))
                                        (extend_fundefs' id Bg Γ)). {
            rewrite add_params_irrelevant; [|eauto with Ensembles_DB].
            intros x Hx. rewrite add_closures_spec by auto.
            unfold extend_fundefs'.
            destruct (Dec x); auto.
            now inv Hx. }
          eapply Closure_conversion_f_eq_subdomain; [|apply Hfeq]; auto.
      + repeat normalize_bound_var; normalize_sets; rewrite bound_var_app_ctx.
        decomp_Disjoint; solve_Union_Inc.
        * (* HΓ_ran *) intros x Hx; inv Hx. right. unfold In, Range in *; zify; lia.
        * (* HbvC_e + ranges *)
          eapply Included_trans; [apply HbvC_e|]; right; unfold In, Range in *; zify; lia.
        * (* Hbv_e' + ranges *)
          eapply Included_trans; [apply Hbv_e'|].
          solve_Union_Inc.
          right; unfold In, Range in *; zify; lia.
        * (* Hbv_B' + ranges *)
          eapply Included_trans; [apply Hbv_B'|].
          solve_Union_Inc.
          right; unfold In, Range in *; zify; lia.
      + zify; lia.
      + constructor; auto; change (~ ?S ?x) with (~ x \in S);
          rewrite ?bound_var_app_ctx, ?Union_demorgan; splits; splits_Disjoint.
        * intros Hc; apply HbvC_e in Hc.
          destruct HD1 as [HD1]; contradiction (HD1 v).
          constructor.
          -- apply Hfresh_Γ; unfold In, Range in *; zify; lia.
          -- subst Bg. unfold used_vars_fundefs.
             rewrite fundefs_append_bound_vars with (B3 := fundefs_append Bl (Fcons v t l e f5))
               by reflexivity.
             normalize_bound_var; left; left; left; right; now left.
        * intros Hc; apply Hbv_e' in Hc. inv Hc.
          -- now inv Huniq.
          -- destruct HD1 as [HD1]; contradiction (HD1 v).
             constructor.
             ++ apply Hfresh_Γ; unfold In, Range in *; zify; lia.
             ++ unfold used_vars_fundefs.
                rewrite fundefs_append_bound_vars with (B3 := fundefs_append Bl (Fcons v t l e f5))
                  by reflexivity.
                normalize_bound_var; left; left; left; right; now left.
        * intros Hc; apply Hbv_B' in Hc. inv Hc.
          -- now inv Huniq.
          -- destruct HD1 as [HD1]; contradiction (HD1 v).
             constructor.
             ++ apply Hfresh_Γ; unfold In, Range in *; zify; lia.
             ++ unfold used_vars_fundefs.
                rewrite fundefs_append_bound_vars with (B3 := fundefs_append Bl (Fcons v t l e f5))
                  by reflexivity.
                normalize_bound_var; left; left; left; right; now left.
        * normalize_sets; splits_Disjoint.
          -- eapply Disjoint_Included_l; [apply HbvC_e|].
             constructor; intros x Hx; inv Hx. inv H2.
             unfold In, Range in *; zify; lia.
          -- eapply Disjoint_Included_l; [apply HbvC_e|].
             constructor; intros x Hx; inv Hx.
             destruct HD1 as [HD1]; contradiction (HD1 x).
             constructor.
             ++ apply Hfresh_Γ; unfold In, Range in *; zify; lia.
             ++ unfold used_vars_fundefs.
                rewrite fundefs_append_bound_vars with (B3 := fundefs_append Bl (Fcons v t l e f5))
                  by reflexivity.
                normalize_bound_var; left; left; left; right; right; now left.
        * normalize_sets; splits_Disjoint.
          -- eapply Disjoint_Included_l; [apply Hbv_e'|]; splits_Disjoint.
             ++ constructor; intros x Hx; inv Hx. inv H2.
                destruct HD1 as [HD1]; contradiction (HD1 x).
                constructor.
                ** apply Hfresh_Γ; unfold In, Range in *; zify; lia.
                ** unfold used_vars_fundefs.
                   rewrite fundefs_append_bound_vars with (B3 := fundefs_append Bl (Fcons v t l e f5))
                     by reflexivity.
                   normalize_bound_var; left; left; left; right; right; right; now left.
             ++ constructor; intros x Hx; inv Hx. inv H2.
                unfold In, Range in *; zify; lia.
          -- eapply Disjoint_Included_l; [apply Hbv_e'|]; splits_Disjoint.
             ++ now inv Huniq.
             ++ constructor; intros x Hx; inv Hx.
                destruct HD1 as [HD1]; contradiction (HD1 x).
                constructor.
                ** apply Hfresh_Γ; unfold In, Range in *; zify; lia.
                ** unfold used_vars_fundefs.
                   rewrite fundefs_append_bound_vars with (B3 := fundefs_append Bl (Fcons v t l e f5))
                     by reflexivity.
                   normalize_bound_var; left; left; left; right; right; now left.
        * normalize_sets; splits_Disjoint.
          -- eapply Disjoint_Included_l; [apply Hbv_B'|]; splits_Disjoint.
             ++ constructor; intros x Hx; inv Hx. inv H2.
                destruct HD1 as [HD1]; contradiction (HD1 x).
                constructor.
                ** apply Hfresh_Γ; unfold In, Range in *; zify; lia.
                ** unfold used_vars_fundefs.
                   rewrite fundefs_append_bound_vars with (B3 := fundefs_append Bl (Fcons v t l e f5))
                     by reflexivity.
                   normalize_bound_var; left; left; left; right; right; right; now right.
             ++ constructor; intros x Hx; inv Hx. inv H2.
                unfold In, Range in *; zify; lia.
          -- eapply Disjoint_Included_l; [apply Hbv_B'|]; splits_Disjoint.
             ++ now inv Huniq.
             ++ constructor; intros x Hx; inv Hx.
                destruct HD1 as [HD1]; contradiction (HD1 x).
                constructor.
                ** apply Hfresh_Γ; unfold In, Range in *; zify; lia.
                ** unfold used_vars_fundefs.
                   rewrite fundefs_append_bound_vars with (B3 := fundefs_append Bl (Fcons v t l e f5))
                     by reflexivity.
                   normalize_bound_var; left; left; left; right; right; now left.
        * eapply Disjoint_Included_l; [apply HbvC_e|].
          eapply Disjoint_Included_r; [apply Hbv_B'|].
          splits_Disjoint.
          -- constructor; intros x Hx; inv Hx.
             destruct HD1 as [HD1]; contradiction (HD1 x).
             constructor.
             ** apply Hfresh_Γ; unfold In, Range in *; zify; lia.
             ** unfold used_vars_fundefs.
                rewrite fundefs_append_bound_vars with (B3 := fundefs_append Bl (Fcons v t l e f5))
                  by reflexivity.
                normalize_bound_var; left; left; left; right; right; right; now right.
          -- constructor; intros x Hx; inv Hx; unfold In, Range in *; zify; lia.
        * eapply Disjoint_Included_l; [apply Hbv_e'|].
          eapply Disjoint_Included_r; [apply Hbv_B'|]; splits_Disjoint.
          -- now inv Huniq.
          -- constructor; intros x Hx; inv Hx.
             destruct HD1 as [HD1]; contradiction (HD1 x).
             constructor.
             ** apply Hfresh_Γ; unfold In, Range in *; zify; lia.
             ** unfold used_vars_fundefs.
                rewrite fundefs_append_bound_vars with (B3 := fundefs_append Bl (Fcons v t l e f5))
                  by reflexivity.
                normalize_bound_var; left; left; left; right; right; right; now right.
          -- constructor; intros x Hx; inv Hx.
             destruct HD1 as [HD1]; contradiction (HD1 x).
             constructor.
             ** apply Hfresh_Γ; unfold In, Range in *; zify; lia.
             ** unfold used_vars_fundefs.
                rewrite fundefs_append_bound_vars with (B3 := fundefs_append Bl (Fcons v t l e f5))
                  by reflexivity.
                normalize_bound_var; left; left; left; right; right; right; now left.
          -- constructor; intros x Hx; inv Hx. unfold In, Range in *; zify; lia.
        * normalize_sets; rewrite Union_demorgan; split; intros Hc.
          -- inv Hc.
             destruct HD1 as [HD1]; contradiction (HD1 v).
             constructor.
             ** apply Hfresh_Γ; unfold In, Range in *; zify; lia.
             ** unfold used_vars_fundefs.
                rewrite fundefs_append_bound_vars with (B3 := fundefs_append Bl (Fcons v t l e f5))
                  by reflexivity.
                normalize_bound_var; left; left; left; right; now left.
          -- now inv Huniq.
        * constructor.
          intros Hc.
          destruct HD1 as [HD1]; contradiction (HD1 Γ).
          constructor.
          ** apply Hfresh_Γ; unfold In, Range in *; zify; lia.
          ** subst Bg. unfold used_vars_fundefs.
             rewrite fundefs_append_bound_vars with (B3 := fundefs_append Bl (Fcons v t l e f5))
               by reflexivity.
             normalize_bound_var; left; left; left; right; right; now left.
          ** now inv Huniq.
    - eapply return_triple. intros _ s Hf.
      splits; auto.
      + constructor.
      + eauto with Ensembles_DB.
      + zify; lia.
      + constructor.
  Qed.

  Transparent exp_closure_conv.
(*
  (** Correctness of [exp_closure_conv] *)
  Corollary exp_closure_conv_correct k rho rho' S e c Γ FVmap Scope Funs FVs :
    (* [Scope], [Funs] and [FVs] are uniquely identified by [FVmap] *)
    FVmap_inv FVmap Scope Funs FVs ->
    (* [Γ] (the current environment parameter) is fresh in e *)
    ~ In _ (Union _ (bound_var e) (occurs_free e)) Γ ->
    (* The free variables of e are defined in the environment *)
    binding_in_map (occurs_free e) rho ->
    (* [FVmap] contains all the free variables *)
    binding_in_map (occurs_free e) FVmap ->
    (* The blocks of functions have unique function names *)
    fundefs_names_unique e ->
    (* [FVmap] does not contain the variables in [S] or [Γ] *)
    binding_not_in_map (Union _ S (Singleton _ Γ)) FVmap ->
    (* [Scope] invariant *)
    cc_approx_env_P pr cenv clo_tag Scope k boundG rho rho' ->
    (* [Fun] invariant *)
    Fun_inv pr cenv clo_tag k rho rho' Scope Funs (subst FVmap) c Γ ->
    (* Free variables invariant *)
    FV_inv pr cenv clo_tag k rho rho' Scope Funs c Γ FVs ->
    (* The function name substitution is injective *)
    injective_subdomain Funs (subst FVmap) ->
    (* function renaming codomain is not shadowed by other vars *)
    Disjoint _ (image (subst FVmap) (Setminus _ Funs Scope)) (bound_var e) ->
    (* [S] is disjoint with the free and bound variables of [e] and [Γ] *)
    Disjoint _ S (Union _ (image (subst FVmap) (Setminus _ Funs Scope))
                        (Union _ (bound_var e)
                               (Union _ (occurs_free e) (Singleton _ Γ)))) ->
    {{ fun s => fresh S (next_var s) }}
      exp_closure_conv clo_tag e FVmap c Γ
    {{ fun s ef s' =>
         let '(e', f) := ef in
         cc_approx_exp pr cenv clo_tag k (boundL k e rho) boundG (e, rho) (f e', rho')
    }}.
  Proof.
    intros IFVmap HGamma Hin_map_rho Hin_map_FVmap Hun
           Hnot_in_map Hcc IFun IFVs Hinj HD1 HD2.
    eapply post_weakening; [| eapply exp_closure_conv_Closure_conv_sound; eassumption ].
    intros s [e' f] s' Hf [C [Hctx [Hclo _]]]. simpl in Hctx, Hclo.
    replace (f e') with (C |[ e' ]|); [| now eauto].
    eapply Closure_conversion_correct; try eassumption.
    intros Hc. eapply HGamma; eauto.
  Qed.

  Lemma get_var_is_exp_ctx  x FVmap c Γ :
    {{ fun s => True }}
      get_var clo_tag x FVmap c Γ
    {{ fun s t s' =>
         let (x', f) := t in
         (exists C, is_exp_ctx f C)
     }}.
  Proof with now eauto with Ensembles_DB.
    unfold get_var. destruct (Maps.PTree.get x FVmap) eqn:Heq.
    - destruct v.
      + eapply bind_triple. apply post_trivial.
        intros x' i. apply return_triple.
        intros _ _.
        eexists (Eproj_c x' c n Γ Hole_c).
        intros e. reflexivity.
      + eapply bind_triple. apply post_trivial.
        intros x' i. apply return_triple.
        intros _ _.
        eexists (Econstr_c x' clo_tag [v; Γ] Hole_c).
        intros e'. reflexivity.
      + apply return_triple.
        intros _ _. exists Hole_c. intros ?; reflexivity.
    - apply return_triple.
      intros _ _. exists Hole_c. intros ?; reflexivity.
  Qed.

  Lemma get_vars_is_exp_ctx  xs FVmap c Γ :
    {{ fun s => True }}
      get_vars clo_tag xs FVmap c Γ
    {{ fun s t s' =>
         let (xs', f) := t in
         (exists C, is_exp_ctx f C)
     }}.
  Proof with now eauto with Ensembles_DB.
    induction xs.
    - apply return_triple. intros _ _.
      exists Hole_c; intros ?; reflexivity.
    - eapply bind_triple.
      + apply get_var_is_exp_ctx.
      + intros [x f] i. apply pre_post_mp_l.
        eapply bind_triple.
        * apply IHxs.
        * intros [xs' f'] i'. apply return_triple.
          intros i'' [C2 Hctx] [C1 Hctx'].
          exists (comp_ctx_f C1 C2). intros e.
          rewrite <- app_ctx_f_fuse. congruence.
  Qed.

  Lemma make_env_is_exp_ctx FVset FVmap FVmap' c Γ Γ' :
    {{ fun s => True }}
      make_env clo_tag FVset FVmap FVmap' c Γ Γ'
    {{ fun s t s' =>
         let '(_, _, f) := t in
         (exists C, is_exp_ctx f C)
     }}.
  Proof with now eauto with Ensembles_DB.
    unfold make_env.
    destruct
      ((fix add_fvs (l : list M.elt)
            (n : N)
            (map : Maps.PTree.t VarInfo)
            {struct l} :
          Maps.PTree.t VarInfo * N :=
          match l with
            | [] => (map, n)
            | x :: xs =>
              add_fvs xs
                      (n + 1)%N
                      (Maps.PTree.set x
                                      (FVar n) map)
          end) (PS.elements FVset) 0%N
               (Maps.PTree.empty VarInfo)).
    eapply bind_triple.
    + apply get_vars_is_exp_ctx.
    + intros [xs f] i. apply pre_post_mp_l.
      eapply bind_triple. apply post_trivial.
      intros. eapply return_triple. intros _ _ [C Hctx].
      eexists (comp_ctx_f C (Econstr_c Γ x xs Hole_c)).
      intros e. rewrite <- app_ctx_f_fuse, Hctx.
      reflexivity.
  Qed.

  Lemma exp_closure_conv_is_exp_ctx e c Γ FVmap :
    {{ fun s => True }}
      exp_closure_conv clo_tag e FVmap c Γ
    {{ fun s ef s' =>
         exists C, is_exp_ctx (snd ef) C
     }}.
  Proof.
    destruct e.
    - eapply bind_triple.
      now apply get_vars_is_exp_ctx.
      intros [? ?]; intros. eapply pre_post_mp_l.
      eapply bind_triple; [ now apply post_trivial | intros].
      now eapply return_triple.
    - eapply bind_triple; [ now apply post_trivial | intros].
      eapply bind_triple. now apply get_var_is_exp_ctx.
      intros [? ?]; intros.
      now eapply return_triple.
    - unfold exp_closure_conv.
      eapply bind_triple. now apply get_var_is_exp_ctx.
      intros [? ?]; intros. eapply pre_post_mp_l.
      eapply bind_triple; [ now apply post_trivial | intros].
      now eapply return_triple.
    - eapply bind_triple; [ now apply post_trivial | intros].
      eapply bind_triple. now apply make_env_is_exp_ctx.
      intros [[? ?] ?]; intros. eapply pre_post_mp_l.
      eapply bind_triple; [ now apply post_trivial | intros].
      destruct x0 as [[? ?] ?].
      eapply bind_triple; [ now apply post_trivial | intros].
      eapply bind_triple; [ now apply post_trivial | intros].
      now eapply return_triple.
    - eapply bind_triple. now apply get_var_is_exp_ctx.
      intros [? ?]; intros. eapply pre_post_mp_l.
      eapply bind_triple. now apply get_vars_is_exp_ctx.
      intros [? ?]; intros. eapply pre_post_mp_l.
      eapply bind_triple; [ now apply post_trivial | intros].
      eapply bind_triple; [ now apply post_trivial | intros].
      eapply return_triple. intros _ _ [C1 H1] [C2 H2].
      simpl. eexists (comp_ctx_f C2 C1). intros e'.
      rewrite <- app_ctx_f_fuse. congruence.
    - eapply bind_triple.
      now apply get_vars_is_exp_ctx.
      intros [? ?]; intros. eapply pre_post_mp_l.
      eapply bind_triple; [ now apply post_trivial | intros].
      now eapply return_triple.
    - eapply bind_triple. now apply get_var_is_exp_ctx.
      intros [? ?]; intros.
      eapply return_triple. now eauto.
  Qed.

  Lemma get_var_bound_var_Included  x FVmap c Γ S S':
    ~ In _ S x ->
    {{ fun s => fresh S (next_var s) }}
      get_var clo_tag x FVmap c Γ
    {{ fun s t s' =>
         let (x', f) := t in
         (forall e,
            (Included _ (bound_var e) (Union _ S' ((Setminus _ S (Singleton _ x')))) ->
             Included _ (bound_var (f e)) (Union _ S' S))) /\
         fresh (Setminus _ S (Singleton _ x')) (next_var s')
     }}.
  Proof with now eauto with Ensembles_DB.
    intros Hnin.
    unfold get_var. destruct (Maps.PTree.get x FVmap) eqn:Heq.
    - destruct v.
      + eapply bind_triple. apply get_name_spec.
        intros x' i. apply return_triple.
        intros i' [Hf Hf']. split; [| eassumption].
        intros e Hin. rewrite bound_var_Eproj.
        apply Union_Included. eapply Included_trans; [ eassumption |]...
        apply Singleton_Included. right. eapply Hf. zify; lia.
      + eapply bind_triple. apply get_name_spec.
        intros x' i. apply return_triple.
        intros i' [Hf Hf']. split; [| eassumption].
        intros e Hin'. rewrite bound_var_Econstr.
        apply Union_Included. eapply Included_trans; [ eassumption |]...
        apply Singleton_Included. right. eapply Hf. zify; lia.
      + apply return_triple.
        intros i' Hf. split.
        * intros e Hin'. eapply Included_trans; [ eassumption |]...
        * intros x' Hleq. constructor. now eauto.
          intros Hc; inv Hc. now eauto.
    - apply return_triple; simpl. intros i Hf. split.
      + intros e Hin'. eapply Included_trans; [ eassumption |]...
      + intros x' Hleq. constructor. now eauto.
        intros Hc; inv Hc. now eauto.
  Qed.

  Lemma get_vars_bound_var_Included xs FVmap c Γ S S':
    Disjoint _ S (FromList xs) ->
    {{ fun s => fresh S (next_var s) }}
      get_vars clo_tag xs FVmap c Γ
    {{ fun s t s' =>
         let (xs', f) := t in
         (forall e,
            Included _ (bound_var e) (Union _ S' (Setminus _ S (FromList xs'))) ->
            Included _ (bound_var (f e)) (Union _ S' S)) /\
           fresh (Setminus _ S (FromList xs')) (next_var s')
     }}.
  Proof.
    revert S S'; induction xs; intros S S' Hd.
    - apply return_triple. intros i Hf.
      split;
        intros ?; rewrite !FromList_nil, !Setminus_Empty_set_neut_r in *; eauto.
    - eapply bind_triple.
      + apply get_var_bound_var_Included.
        intros Hin'. eapply Hd. constructor; eauto.
        rewrite FromList_cons. left; eauto.
      + intros [x f] i. apply pre_curry_l. intros Hx.
        eapply bind_triple.
        * apply IHxs. eapply Disjoint_Included_l.
          now apply Setminus_Included.
          eapply Disjoint_Included_r; [| eassumption ].
          rewrite FromList_cons. now apply Included_Union_r.
        * intros [xs' f'] i'. apply return_triple.
          intros i'' [Hxs Hf']. split.
          intros e Hin'. eapply Hx. eapply Hxs.
          rewrite FromList_cons in Hin'. rewrite Setminus_Union. eassumption.
          rewrite FromList_cons, <- Setminus_Union. eassumption.
  Qed.

  Lemma make_full_closure_bound_var_Included B m1 m2 Γ S :
    {{ fun s => fresh S (next_var s) }}
      make_full_closure clo_tag B m1 m2 Γ
    {{ fun s t s' =>
         let '(m1', _, f) := t in
         (forall e,
            Same_set _ (bound_var (f e)) (Union _ (bound_var  e) (name_in_fundefs B))) /\
         Included _ (image (subst m1') (name_in_fundefs B)) S /\
         fresh S (next_var s')
     }}.
  Proof with now eauto with Ensembles_DB.
    revert S; induction B; intros S.
    - eapply bind_triple. now apply get_name_spec.
      intros x s1. apply pre_curry_l. intros Hf1.
      eapply bind_triple. now eapply IHB.
      intros [[m1' m2'] f1] _. apply return_triple.
      intros s2 [Hinc [Him Hf]]. split; [| split ].
      + intros e'. rewrite bound_var_Econstr; simpl.
        rewrite Hinc...
      + rewrite <- subst_MRFun_f_eq. rewrite image_extend_In_S.
        simpl. apply Union_Included.
        eapply Included_trans.
        rewrite Setminus_Union_distr, Setminus_Same_set_Empty_set,
        Union_Empty_set_neut_l.
        apply image_monotonic. now apply Setminus_Included.
        eapply Included_trans. eassumption. now apply Setminus_Included.
        apply Singleton_Included. eapply Hf1. zify; lia.
        now left; eauto.
      + eapply fresh_monotonic; [| eassumption ].
        now apply Setminus_Included.
    - apply return_triple. intros s Hf.
      simpl. split; [ |  split; [| now eauto] ].
      intros e. now rewrite Union_Empty_set_neut_r.
      rewrite image_Empty_set. now apply Included_Empty_set.
  Qed.

  Lemma exp_closure_conv_bound_var_Included_mut :
    (forall e c Γ FVmap S
       (HD: Disjoint _ S (Union _ (bound_var e) (occurs_free e))),
       {{ fun s => fresh S (next_var s) }}
         exp_closure_conv clo_tag e FVmap c Γ
       {{ fun s ef s' =>
            Included _ (bound_var ((snd ef) (fst ef)))
                     (Union _ (bound_var e) S) /\
            fresh S (next_var s')
        }}) /\
    (forall B FVmap S c
       (HD : Disjoint _ S (Union _ (bound_var_fundefs B) (occurs_free_fundefs B))),
       {{ fun s => fresh S (next_var s) }}
         fundefs_closure_conv clo_tag B FVmap c
       {{ fun s B' s' =>
            Included _ (bound_var_fundefs B')
                     (Union _ (bound_var_fundefs B)
                            (Union _ S (image (subst FVmap) (name_in_fundefs B)))) /\
            fresh S (next_var s')
        }}).
  Proof with now eauto with Ensembles_DB.
    exp_defs_induction IHe IHl IHB; intros.
    - eapply bind_triple.
      + eapply get_vars_bound_var_Included.
        eapply Disjoint_Included_r; [| eassumption ].
        rewrite occurs_free_Econstr...
      + intros [xs f] i. apply pre_curry_l; intros Hf.
        eapply bind_triple. eapply IHe.
        eapply Disjoint_Included_l. now apply Setminus_Included.
        eapply Disjoint_Included_r; [| eassumption ].
        now apply bound_var_occurs_free_Econstr_Included.
        intros [e' f'] i'. apply return_triple.
        intros i''. intros [He' Hf'']. split.
        simpl in *. eapply Hf. rewrite !bound_var_Econstr.
        rewrite <- Union_assoc, Union_commut with (s2 := Setminus _ _ _), Union_assoc.
        apply Included_Union_compat; [ eassumption | now apply Included_refl].
        eapply fresh_monotonic; [| eassumption ]...
    - eapply bind_triple with (post' := fun _ P i =>  P = [] /\  fresh S (next_var i)) .
      now apply return_triple.
      intros P' i. apply pre_curry_l. intros Heq; subst.
      eapply bind_triple. apply get_var_bound_var_Included.
      intros Hc. eapply HD. now constructor; eauto.
      intros [x f] _. apply return_triple. intros i'.
      intros [He Hf]. split. simpl.
      eapply He. rewrite !bound_var_Ecase_nil.
      now apply Included_Empty_set.
      eapply fresh_monotonic; [| eassumption ]...
    - unfold exp_closure_conv. setoid_rewrite assoc.
      eapply bind_triple.
      + eapply IHe. eapply Disjoint_Included_r; [| eassumption ].
        eapply bound_var_occurs_free_Ecase_Included. now constructor.
      + intros [e' f'] s'. simpl. setoid_rewrite assoc. simpl.
        setoid_rewrite st_eq_Ecase. eapply pre_curry_l; intros He'.
        eapply bind_triple.
        { eapply post_conj.
          - eapply IHl with (FVmap := FVmap) (Γ := Γ) (c := c0).
            eapply Disjoint_Included_r; [| eassumption ].
            now eapply bound_var_occurs_free_Ecase_cons_Included.
          - eapply pre_strenghtening;
            [ | now eapply exp_closure_conv_is_exp_ctx
                with (e := (Ecase v l)) (c := c0) (Γ := Γ) (FVmap := FVmap)].
            intros. simpl; eauto. }
        intros [e'' f''] s''.
        destruct e''; apply return_triple;
        try (intros s''' [[Hin Hf] _]; split; eauto;
             eapply Included_trans; [ eassumption |]; normalize_bound_var;
             now eauto with Ensembles_DB).
        intros s''' [[Hin Hf] [C Hctx]]; split; eauto. simpl in *.
        rewrite Hctx. rewrite bound_var_ctx_app_Ecase_cons, bound_var_Ecase_cons.
        apply Union_Included.
        * eapply Included_trans. eassumption. eauto with Ensembles_DB.
        * rewrite <- Hctx. eapply Included_trans. eassumption.
          eauto with Ensembles_DB.
    - eapply bind_triple.
      + eapply get_var_bound_var_Included. intros Hc. eapply HD; eauto.
      + intros [xs f] i. apply pre_curry_l. intros Hf.
        eapply bind_triple.
        apply IHe.
        eapply Disjoint_Included_l. now apply Setminus_Included.
        eapply Disjoint_Included_r; [| eassumption ].
        now apply bound_var_occurs_free_Eproj_Included.
        intros [e' f'] i'. apply return_triple.
        intros i''. intros [He' Hf'']. split.
        simpl in *. eapply Hf. rewrite !bound_var_Eproj.
        rewrite <- Union_assoc, Union_commut with (s2 := Setminus _ _ _), Union_assoc...
        eapply fresh_monotonic; [| eassumption ]...
    - eapply bind_triple. now apply get_named_str_fresh.
      intros Γ' s1. eapply pre_curry_l. intros Hf1.
      eapply bind_triple with
      (post' :=
         fun _ t s' =>
           let '(_, f) := t in
           (forall e0 : exp,
              Included var (bound_var e0)
                       (Union var (bound_var (Efun f2 e)) S) ->
              Included var (bound_var (f e0))
                       (Union var (bound_var (Efun f2 e)) S)) /\
           fresh (Setminus var S (Singleton var Γ')) (next_var s')).
      + unfold make_env.
        destruct
          ((fix
              add_fvs (l : list M.elt) (n : N) (map : Maps.PTree.t VarInfo)
              {struct l} : Maps.PTree.t VarInfo * N :=
              match l with
                | [] => (map, n)
                | x :: xs => add_fvs xs (n + 1)%N (Maps.PTree.set x (FVar n) map)
              end) _ _ _ ) as [m1' n].
        eapply bind_triple.
        apply get_vars_bound_var_Included with (S' := Union _ (bound_var (Efun f2 e)) S).
        assert (Heq : (@FromList var (PS.elements (fundefs_fv f2))) = FromSet (fundefs_fv f2)) by reflexivity.
        rewrite Heq, <- fundefs_fv_correct.
        eapply Disjoint_Included_l. now apply Setminus_Included.
        eapply Disjoint_Included_r; [| eassumption ].
        apply Included_Union_preserv_r. normalize_occurs_free...
        intros [xs f] s2. apply pre_curry_l. intros He.
        eapply bind_triple. apply make_record_ctor_tag_preserves_prop.
        intros c' s3. apply return_triple. intros s4 Hf. split.
        intros e' He'.
        rewrite <- Union_Same_set with (s6 := S),
                Union_commut with (s6 := S), Union_assoc.
        eapply He. rewrite bound_var_Econstr.
        apply Union_Included.
        eapply Included_trans; [ eassumption |]...
        apply Included_Union_preserv_l. apply Included_Union_preserv_r.
        apply Singleton_Included. apply Hf1. zify; lia.
        now apply Setminus_Included.
        eapply fresh_monotonic; [| eassumption ]...
      + intros [[c' map'] f] _. apply pre_curry_l.
        intros He. eapply bind_triple.
        now apply make_full_closure_bound_var_Included.
        intros [[map_n map_o] f'] _. apply pre_curry_l.
        intros He'. eapply pre_curry_l. intros Him.
        eapply bind_triple. eapply IHe.
        eapply Disjoint_Included_l. now apply Setminus_Included.
        eapply Disjoint_Included_r; [| eassumption ].
        now apply bound_var_occurs_free_Efun_Included.
        intros [e' f''] s. apply pre_curry_l. intros He''.
        eapply bind_triple. apply IHB.
        eapply Disjoint_Included_l. now apply Setminus_Included.
        eapply Disjoint_Included_r; [| eassumption ].
        now apply bound_var_occurs_free_fundefs_Efun_Included.
        intros B' s2. apply return_triple. intros s3 [HB Hf].
        simpl in *. split.
        eapply He. rewrite !bound_var_Efun.
        apply Union_Included.
        eapply Included_trans. eassumption.
        apply Union_Included. eauto with Ensembles_DB.
        apply Union_Included. eauto with Ensembles_DB.
        eapply Included_trans. eassumption. eauto with Ensembles_DB.
        rewrite <- Union_Same_set with (s5 := (Union _ (Union _ _ _) _)),
                                      Union_commut.
        rewrite He'. apply Union_Included.
        eapply Included_trans. eassumption. apply Union_Included.
        now eauto with Ensembles_DB. now eauto with Ensembles_DB.
        do 3 apply Included_Union_preserv_l.
        now apply name_in_fundefs_bound_var_fundefs.
        eauto with Ensembles_DB.
        eapply fresh_monotonic; [| eassumption ]...
    - eapply bind_triple.
      eapply get_var_bound_var_Included.
      intros Hc. now eapply HD; eauto.
      intros [g f] s1. apply pre_curry_l. intros He.
      eapply bind_triple.
      eapply get_vars_bound_var_Included.
      eapply Disjoint_Included_l. now apply Setminus_Included.
      eapply Disjoint_Included_r; [| eassumption ].
      rewrite occurs_free_Eapp...
      intros [xs f'] s2. apply pre_curry_l. intros He'.
      eapply bind_triple. now apply get_name_spec.
      intros ptr s3. apply pre_curry_l. intros Hf.
      eapply bind_triple. now apply get_name_spec.
      intros env s4. apply pre_curry_l. intros Hf'.
      apply return_triple. intros s5. intros Hf''.
      simpl in *. split.
      eapply He. eapply He'.
      rewrite !bound_var_Eproj, !bound_var_Eapp, !Union_Empty_set_neut_l.
      apply Union_Included. eapply Singleton_Included.
      eapply Hf'. zify; lia.
      eapply Singleton_Included. eapply Hf. zify; lia.
      eapply fresh_monotonic; [| eassumption ]...
    - eapply bind_triple.
      + eapply get_vars_bound_var_Included.
        eapply Disjoint_Included_r; [| eassumption ].
        rewrite occurs_free_Eprim...
      + intros [xs f] i.
        apply pre_curry_l. intros Hf.
        eapply bind_triple.
        apply IHe.
        eapply Disjoint_Included_l. now apply Setminus_Included.
        eapply Disjoint_Included_r; [| eassumption ].
        now apply bound_var_occurs_free_Eprim_Included.
        intros [e' f'] i'. apply return_triple.
        intros i''. intros [He' Hf'']. split.
        simpl in *. eapply Hf. rewrite !bound_var_Eprim.
        rewrite <- Union_assoc, Union_commut with (s2 := Setminus _ _ _), Union_assoc...
        eapply fresh_monotonic; [| eassumption ]...
    - eapply bind_triple.
      apply get_var_bound_var_Included. intros Hc.
      eapply HD. now constructor; eauto.
      intros [x f] _. apply return_triple. intros s [Hin Hf].
      split.
      eapply Included_trans. now eapply Hin. reflexivity.
      eapply fresh_monotonic; [| eassumption ]...
    - eapply bind_triple.
      now apply get_name_spec.
      intros env s1. apply pre_curry_l; intros Hf.
      eapply bind_triple. eapply IHe.
      eapply Disjoint_Included_l. now apply Setminus_Included.
      eapply Disjoint_Included_r; [| eassumption ].
      now apply bound_var_occurs_free_Fcons_Included.
      intros [e' f] s2. apply pre_curry_l. intros He.
      eapply bind_triple. eapply IHB.
      eapply Disjoint_Included_l. now apply Setminus_Included.
      eapply Disjoint_Included_r; [| eassumption ].
      now apply bound_var_occurs_free_fundefs_Fcons_Included.
      intros B s3. eapply return_triple.
      intros s4 [Hin Hf']. split. simpl.
      rewrite !bound_var_fundefs_Fcons.
      apply Union_Included.
      destruct (Maps.PTree.get v FVmap) as [v' | ] eqn:Heq;
        try destruct v'; eauto with Ensembles_DB.
      do 2 apply Included_Union_preserv_r.
      rewrite image_Union, image_Singleton. apply Included_Union_preserv_l.
      unfold subst. rewrite Heq. now eauto.
      apply Union_Included. rewrite FromList_cons.
      apply Union_Included. apply Included_Union_preserv_r.
      apply Included_Union_preserv_l. apply Singleton_Included.
      eapply Hf. zify; lia. now eauto with Ensembles_DB.
      apply Union_Included. eapply Included_trans; [ eassumption |]...
      eauto with Ensembles_DB.
      eapply Included_trans; [ eassumption |].
      apply Union_Included. now eauto with Ensembles_DB.
      apply Union_Included. now eauto with Ensembles_DB.
      do 2 apply Included_Union_preserv_r.
      apply image_monotonic. now apply Included_Union_r.
      eapply fresh_monotonic; [|  eassumption ]...
    - apply return_triple. intros. split; eauto.
      now apply Included_Union_l.
  Qed.

  Lemma get_var_bound_var_Included' x FVmap c Γ S :
    ~ In _ S x ->
    {{ fun s => fresh S (next_var s) }}
      get_var clo_tag x FVmap c Γ
    {{ fun s t s' =>
         let (x', f) := t in
         (forall e,
            Included _ (bound_var (f e)) (Union _ (bound_var e) (Singleton _ x'))) /\
         fresh (Setminus _ S (Singleton _ x')) (next_var s')
     }}.
  Proof with now eauto with Ensembles_DB.
    intros Hnin.
    unfold get_var. destruct (Maps.PTree.get x FVmap) eqn:Heq.
    - destruct v.
      + eapply bind_triple. apply get_name_spec.
        intros x' i. apply return_triple.
        intros i' [Hf Hf']. split; [| eassumption].
        intros e. rewrite bound_var_Eproj...
      + eapply bind_triple. apply get_name_spec.
        intros x' i. apply return_triple.
        intros i' [Hf Hf']. split; [| eassumption].
        intros e. rewrite bound_var_Econstr...
      + apply return_triple.
        intros i' Hf. split.
        * intros e...
        * intros x' Hleq. constructor. now eauto.
          intros Hc; inv Hc. now eauto.
    - apply return_triple; simpl. intros i Hf. split.
      + intros e...
      + intros x' Hleq. constructor. now eauto.
        intros Hc; inv Hc. now eauto.
  Qed.

  Lemma get_vars_bound_var_Included' xs FVmap c Γ S:
    Disjoint _ S (FromList xs) ->
    {{ fun s => fresh S (next_var s) }}
      get_vars clo_tag xs FVmap c Γ
    {{ fun s t s' =>
         let (xs', f) := t in
         (forall e,
            Included _ (bound_var (f e)) (Union _ (bound_var e) (FromList xs'))) /\
           fresh (Setminus _ S (FromList xs')) (next_var s')
     }}.
  Proof with now eauto with Ensembles_DB.
    revert S; induction xs; intros S Hd.
    - apply return_triple. intros i Hf.
      split.
      intros ?; rewrite !FromList_nil...
      intros ?; rewrite !FromList_nil, !Setminus_Empty_set_neut_r in *; eauto.
    - eapply bind_triple.
      + apply get_var_bound_var_Included'.
        intros Hin'. eapply Hd. constructor; eauto.
        rewrite FromList_cons. left; eauto.
      + intros [x f] i. apply pre_curry_l. intros Hx.
        eapply bind_triple.
        * apply IHxs. eapply Disjoint_Included_l.
          now apply Setminus_Included.
          eapply Disjoint_Included_r; [| eassumption ].
          rewrite FromList_cons. now apply Included_Union_r.
        * intros [xs' f'] i'. apply return_triple.
          intros i'' [Hxs Hf']. split.
          intros e. eapply Included_trans. eapply Hx.
          eapply Included_trans. eapply Included_Union_compat. eapply Hxs.
          now apply Included_refl. rewrite FromList_cons...
          rewrite FromList_cons, <- Setminus_Union. eassumption.
  Qed.

  Lemma get_var_occurs_free_Included' x FVmap c Γ S Scope Funs FVs :
    FVmap_inv FVmap Scope Funs FVs ->
    ~ In _ S x ->
    {{ fun s => fresh S (next_var s) }}
      get_var clo_tag x FVmap c Γ
    {{ fun s t s' =>
         let (x', f) := t in
         (forall e,
            Included _ (occurs_free (f e))
                     (Union _ (occurs_free e)
                            (Union _ (image (subst FVmap) (Setminus _ Funs Scope))
                                   (Singleton _ Γ)))) /\
         fresh (Setminus _ S (Singleton _ x')) (next_var s')
     }}.
  Proof with now eauto with Ensembles_DB.
    intros Hinv Hnin.
    unfold get_var. destruct (Maps.PTree.get x FVmap) eqn:Heq.
    - destruct v.
      + eapply bind_triple. apply get_name_spec.
        intros x' i. apply return_triple.
        intros i' [Hf Hf']. split; [| eassumption].
        intros e. normalize_occurs_free...
      + eapply bind_triple. apply get_name_spec.
        intros x' i. apply return_triple.
        intros i' [Hf Hf']. split; [| eassumption].
        intros e. normalize_occurs_free. rewrite FromList_cons, FromList_singleton.
        apply Union_Included.
        apply Union_Included.
        apply Included_Union_preserv_r. apply Included_Union_preserv_l.
        apply Singleton_Included. exists x.
        split. eapply Hinv. now eexists; eauto.
        unfold subst. now rewrite Heq.
        now eauto with Ensembles_DB.
        now eauto with Ensembles_DB.
      + apply return_triple.
        intros i' Hf. split.
        * intros e...
        * intros x' Hleq. constructor. now eauto.
          intros Hc; inv Hc. now eauto.
    - apply return_triple; simpl. intros i Hf. split.
      + intros e...
      + intros x' Hleq. constructor. now eauto.
        intros Hc; inv Hc. now eauto.
  Qed.

   Lemma get_var_occurs_free_Included x FVmap c Γ S Scope :
    FVmap_inv FVmap Scope (Empty_set var) [] ->
    ~ In _ S x ->
    {{ fun s => fresh S (next_var s) }}
      get_var clo_tag x FVmap c Γ
    {{ fun s t s' =>
         let (x', f) := t in
         (forall e,
            Included _ (occurs_free (f e)) (occurs_free e)) /\
            x = x' /\
         fresh (Setminus _ S (Singleton _ x')) (next_var s')
    }}.
  Proof with now eauto with Ensembles_DB.
    intros Hinv Hnin.
    unfold get_var. destruct (Maps.PTree.get x FVmap) eqn:Heq.
    - destruct v.
      + eapply bind_triple. apply get_name_spec.
        intros x' i. apply return_triple.
        intros i' [Hf Hf'].
        eapply Hinv in Heq. inv Heq. inv H.
      + eapply bind_triple. apply get_name_spec.
        intros x' i. apply return_triple.
        intros i' [Hf Hf'].
        assert (Hc : In _ (Setminus _ (Empty_set var) Scope) x)
          by (eapply Hinv; eexists; eauto).
        inv Hc. inv H.
      + apply return_triple.
        intros i' Hf. split; [| split ].
        * intros e...
        * reflexivity.
        * intros x' Hleq. constructor. now eauto.
          intros Hc; inv Hc. now eauto.
    - apply return_triple; simpl. intros i Hf. split; [| split ].
      + intros e...
      + reflexivity.
      + intros x' Hleq. constructor. now eauto.
        intros Hc; inv Hc. now eauto.
  Qed.

  Lemma get_vars_occurs_free_Included xs FVmap c Γ S Scope :
    FVmap_inv FVmap Scope (Empty_set var) [] ->
    Disjoint _ S (FromList xs) ->
    {{ fun s => fresh S (next_var s) }}
      get_vars clo_tag xs FVmap c Γ
    {{ fun s t s' =>
         let (xs', f) := t in
         (forall e,
            Included _ (occurs_free (f e)) (occurs_free e)) /\
         xs = xs' /\
         fresh (Setminus _ S (FromList xs')) (next_var s')
     }}.
  Proof.
    revert S; induction xs; intros S S' Hd.
    - apply return_triple. intros i Hf.
      split. now eauto with Ensembles_DB.
      now rewrite !FromList_nil, !Setminus_Empty_set_neut_r in *; eauto.
    - eapply bind_triple.
      + eapply get_var_occurs_free_Included.
        eassumption.
        intros Hin'. eapply Hd. constructor; eauto.
        rewrite FromList_cons. left; eauto.
      + intros [x f] i. apply pre_curry_l. intros Hx.
        apply pre_curry_l. intros Heq; subst.
        eapply bind_triple.
        * apply IHxs. eassumption. eapply Disjoint_Included_l.
          now apply Setminus_Included.
          eapply Disjoint_Included_r; [| eassumption ].
          rewrite FromList_cons. now apply Included_Union_r.
        * intros [xs' f'] i'. apply return_triple.
          intros i'' [Hxs [Heq Hf']]. subst. split.
          intros e. now eapply Included_trans; eauto.
          split. reflexivity.
          rewrite FromList_cons, <- Setminus_Union. eassumption.
  Qed.

  Lemma make_full_closure_occurs_free_Included B m1 m2 Γ S :
    unique_functions B ->
    {{ fun s => fresh S (next_var s) }}
      make_full_closure clo_tag B m1 m2 Γ
    {{ fun s t s' =>
         let '(m1', _, f) := t in
         (forall e,
            Included _ (occurs_free (f e))
                     (Union _ (Singleton _ Γ)
                            (Union _ (image (subst m1') (name_in_fundefs B))
                                   (Setminus _ (occurs_free e) (name_in_fundefs B))))) /\
         fresh S (next_var s')
     }}.
  Proof with now eauto with Ensembles_DB.
    revert S; induction B; intros S Hun.
    - inv Hun. eapply bind_triple. now apply get_name_spec.
      intros x s1. apply pre_curry_l. intros Hf1.
      eapply bind_triple. now eapply IHB.
      intros [[m1' m2'] f1] _. apply return_triple.
      intros s2 [Hinc Hf]. split.
      + intros e'. normalize_occurs_free.
        rewrite FromList_cons, FromList_singleton.
        simpl. rewrite <- subst_MRFun_f_eq.
        apply Union_Included.
        apply Union_Included.
        apply Included_Union_preserv_r. apply Included_Union_preserv_l.
        rewrite image_Union, image_Singleton, extend_gss...
        now eauto with Ensembles_DB.
        eapply Included_trans.
        eapply Included_Setminus_compat. now eapply Hinc.
        reflexivity.
        rewrite !Setminus_Union_distr.
        apply Union_Included. now eauto with Ensembles_DB.
        simpl. apply Union_Included.
        apply Included_Union_preserv_r. apply Included_Union_preserv_l.
        eapply Included_trans. now apply Setminus_Included.
        eapply Included_image_extend. eassumption.
        rewrite Setminus_Union...
      + eapply fresh_monotonic; [| eassumption ].
        now apply Setminus_Included.
    - apply return_triple. intros s Hf.
      simpl. split.
      intros e... eassumption.
  Qed.

  Lemma make_env_occurs_free_Included FVs m1 m2 c Γ' Γ S Scope :
    FVmap_inv m2 Scope (Empty_set var) [] ->
    Disjoint var S (FromList (PS.elements FVs)) ->
    {{ fun s => fresh S (next_var s) }}
      make_env clo_tag FVs m1 m2 c Γ' Γ
    {{ fun _ t s' =>
         let '(xs, f) := t in
         (forall e : exp,
            Included var (occurs_free (f e))
                     (Union _ (FromList (PS.elements FVs))
                            (Setminus _ (occurs_free e) (Singleton _ Γ')))) /\
         fresh S (next_var s') }}.
  Proof with now eauto with Ensembles_DB.
    intros Hi HD. unfold make_env.
    destruct
      ((fix
          add_fvs (l : list M.elt) (n : N) (map : Maps.PTree.t VarInfo)
          {struct l} : Maps.PTree.t VarInfo * N :=
          match l with
            | [] => (map, n)
            | x :: xs => add_fvs xs (n + 1)%N (Maps.PTree.set x (FVar n) map)
          end) _ _ _ ) as [m1' n].
    eapply bind_triple.
    eapply get_vars_occurs_free_Included.
    eassumption. eassumption.
    intros [xs f] s2. apply pre_curry_l. intros He.
    apply pre_curry_l. intros Heq. subst.
    eapply bind_triple. apply make_record_ctor_tag_preserves_prop.
    intros c' s3. apply return_triple. intros s4 Hf. split.
    intros e'.
    eapply Included_trans; [ now apply He |].
    repeat normalize_occurs_free. reflexivity.
    eapply fresh_monotonic; [| eassumption ]...
  Qed.

  Corollary exp_closure_conv_closed_fundefs  e c Γ FVmap S Scope :
    FVmap_inv FVmap Scope (Empty_set var) [] ->
    Disjoint _ S (Union _ (bound_var e) (occurs_free e)) ->
    binding_in_map (occurs_free e) FVmap ->
    binding_not_in_map (Union M.elt S (Singleton M.elt Γ)) FVmap ->
    Disjoint M.elt S
             (Union var (bound_var e)
                    (Union var (occurs_free e) (Singleton M.elt Γ))) ->
    ~ In var (Union var (bound_var e) (occurs_free e)) Γ ->
    fundefs_names_unique e ->
    {{ fun s => fresh S (next_var s) }}
      exp_closure_conv clo_tag e FVmap c Γ
    {{ fun s ef s' =>
         closed_fundefs_in_exp ((snd ef) (fst ef))
    }}.
  Proof.
    intros Hinv HD1 Hin Hnin HD2 Hnin' Hun.
    eapply post_weakening; [| eapply exp_closure_conv_Closure_conv_sound; try eassumption ].
    intros s [e' f] s' _ [C [Hctx [Hcc _]]].
    simpl. rewrite Hctx. eapply Closure_conversion_closed_fundefs_mut.
    eassumption. eassumption.
    rewrite Setminus_Empty_set_abs_r, image_Empty_set, Union_Empty_set_neut_l.
    eauto with Ensembles_DB.
  Qed.

  Lemma funs_in_exp_ctx_app_mut :
    (forall C e B, funs_in_exp B e -> funs_in_exp B (C |[ e ]|)) /\
    (forall fC e B, funs_in_exp B e -> funs_in_fundef B (fC <[ e ]>)).
  Proof.
    exp_fundefs_ctx_induction IHe IHB;
    try now (intros e' B' Hfin; eauto; constructor; eauto).
    intros P e' B Hfin. simpl. econstructor.
    eapply IHe. eassumption.
    eapply in_or_app. right. now constructor.
  Qed.

  Corollary funs_in_exp_ctx_app C e B :
    funs_in_exp B e -> funs_in_exp B (C |[ e ]|).
  Proof.
    now apply funs_in_exp_ctx_app_mut.
  Qed.

  Corollary funs_in_fundefs_ctx_app fC e B :
    funs_in_exp B e -> funs_in_fundef B (fC <[ e ]>).
  Proof.
    now apply funs_in_exp_ctx_app_mut.
  Qed.

  Lemma fundefs_closure_conv_in_image_subst_map B map c :
    {{ fun _ => True }}
      fundefs_closure_conv clo_tag B map c
    {{ fun _ B' _ =>
         Same_set _ (name_in_fundefs B') (image (subst map) (name_in_fundefs B)) }}.
  Proof with now eauto with Ensembles_DB.
    induction B.
    - eapply bind_triple. now apply post_trivial.
      intros x s1. eapply bind_triple. now apply post_trivial.
      intros e' s2. eapply bind_triple. now apply IHB.
      intros B' s3. apply return_triple. intros _ Hseq.
      simpl. rewrite image_Union, image_Singleton...
    - apply return_triple. simpl. intros.
      rewrite image_Empty_set...
  Qed.

  Lemma exp_closure_conv_occurs_free_Included  e c Γ FVmap S Scope :
    FVmap_inv FVmap Scope (Empty_set var) [] ->
    Disjoint _ S (Union _ (bound_var e) (occurs_free e)) ->
    binding_in_map (occurs_free e) FVmap ->
    binding_not_in_map (Union M.elt S (Singleton M.elt Γ)) FVmap ->
    Disjoint M.elt S
             (Union var (bound_var e)
                    (Union var (occurs_free e) (Singleton M.elt Γ))) ->
    ~ In var (Union var (bound_var e) (occurs_free e)) Γ ->
    fundefs_names_unique e ->
    {{ fun s => fresh S (next_var s) }}
      exp_closure_conv clo_tag e FVmap c Γ
    {{ fun s ef s' =>
         Included _ (occurs_free ((snd ef) (fst ef))) (occurs_free e) /\
         fresh S (next_var s')
     }}.
  Proof with now eauto with Ensembles_DB.
    revert S Scope FVmap; induction e using exp_ind';
    intros S Scope FVmap Hinv HD1 Hin Hnin HD2 Hnin' Hun; simpl.
    Opaque exp_closure_conv fundefs_closure_conv.
    - eapply bind_triple.
      + eapply get_vars_occurs_free_Included.
        eassumption. eapply Disjoint_Included_r; [| eassumption ].
        rewrite occurs_free_Econstr...
      + intros [xs f] i. apply pre_curry_l; intros Hin1.
        apply pre_curry_l; intros Heq. subst.
        eapply bind_triple. eapply IHe.
        now eapply FVmap_inv_set_bound; eauto.
        eapply Disjoint_Included_l. now apply Setminus_Included.
        eapply Disjoint_Included_r; [| eassumption ].
        rewrite Union_assoc. apply Included_Union_preserv_l.
        now apply bound_var_occurs_free_Econstr_Included.
        eapply binding_in_map_antimon; [| eapply binding_in_map_set; eassumption ].
        normalize_occurs_free. rewrite <- Union_assoc.
        now rewrite <- Union_Setminus; eauto with Ensembles_DB typeclass_instances.
        eapply binding_not_in_map_set_not_In_S.
        eapply binding_not_in_map_antimon; [| eassumption ]...
        intros Hc. inv Hc.
        eapply HD1. constructor; [| now eauto ]. now eapply Setminus_Included; eauto.
        inv H. now eapply Hnin'; eauto.
        eapply Disjoint_Included_l. now apply Setminus_Included.
        eapply Disjoint_Included_r; [| eassumption ].
        rewrite !Union_assoc. apply Included_Union_compat.
        now apply bound_var_occurs_free_Econstr_Included.
        reflexivity.
        intros Hc.  eapply Hnin'. now eapply bound_var_occurs_free_Econstr_Included.
        now intros B Hfe; eapply Hun; eauto.
        intros [e' f'] i'. apply return_triple.
        intros i''. simpl. intros [Hin2 Hf2]. split.
        simpl in *. eapply Included_trans. eapply Hin1.
        repeat normalize_occurs_free...
        eapply fresh_monotonic; [| eassumption ]...
    - eapply bind_triple with (post' := fun _ P i =>  P = [] /\  fresh S (next_var i)) .
      now apply return_triple.
      intros P' i. apply pre_curry_l. intros Heq; subst.
      eapply bind_triple. eapply get_var_occurs_free_Included.
      eassumption.
      intros Hc. eapply HD1. now constructor; eauto.
      intros [x f] _. apply return_triple. intros i'.
      intros [He [Heq Hf]]. subst. split. simpl.
      eapply Included_trans. eapply He.
      repeat normalize_occurs_free...
      eapply fresh_monotonic; [| eassumption ]...
    - setoid_rewrite assoc. eapply bind_triple.
      + eapply IHe. eassumption.
        eapply Disjoint_Included_r; [| eassumption ].
        rewrite Union_assoc. apply Included_Union_preserv_l.
        eapply bound_var_occurs_free_Ecase_Included. now constructor.
        eapply binding_in_map_antimon; [| eassumption ].
        normalize_occurs_free...
        eapply binding_not_in_map_antimon; [| eassumption ]...
        eapply Disjoint_Included_r; [| eassumption ].
        rewrite !Union_assoc. eapply Included_Union_compat.
        eapply bound_var_occurs_free_Ecase_Included. now constructor.
        reflexivity.
        intros Hc. eapply Hnin'. eapply bound_var_occurs_free_Ecase_Included.
        constructor. reflexivity. eassumption.
        intros B Hfe. eapply Hun. econstructor. now eauto. now constructor.
      + intros [e' f'] s'. simpl. setoid_rewrite assoc. simpl.
        setoid_rewrite st_eq_Ecase. eapply pre_curry_l; intros He'.
        eapply bind_triple. eapply post_conj.
        * eapply IHe0 with (FVmap := FVmap).
          eassumption.
          eapply Disjoint_Included_r; [| eassumption ].
          rewrite Union_assoc. apply Included_Union_preserv_l.
          now eapply bound_var_occurs_free_Ecase_cons_Included.
          eapply binding_in_map_antimon; [| eassumption ].
          normalize_occurs_free...
          eapply binding_not_in_map_antimon; [| eassumption ]...
          eapply Disjoint_Included_r; [| eassumption ].
          rewrite !Union_assoc. eapply Included_Union_compat.
          now eapply bound_var_occurs_free_Ecase_cons_Included.
          reflexivity.
          intros Hc. eapply Hnin'.
          now eapply bound_var_occurs_free_Ecase_cons_Included.
          intros B Hfe. eapply Hun. inv Hfe. econstructor. now eauto.
          constructor 2. now eauto.
        * assert (Ht := exp_closure_conv_is_exp_ctx (Ecase v l) c Γ FVmap).
          eapply pre_strenghtening; [| now apply Ht ].
          intros; simpl; now eauto.
        * intros [e'' f''] s''; destruct e'';
          try (apply return_triple; intros s''' [[Hin1 Hf1] _];
               simpl in *; split;
               [ eapply Included_trans;
                 [ eassumption | normalize_occurs_free; now eauto with Ensembles_DB ]
               | eassumption ]).
          apply return_triple; intros s''' [[Hin1 Hf1] [C Hctx]].
          simpl in *; split; [| eassumption ].
          rewrite Hctx. eapply Included_trans.
          apply occurs_free_Ecase_ctx_app'. rewrite <- Hctx.
          repeat normalize_occurs_free...
    - eapply bind_triple.
      + eapply get_var_occurs_free_Included.
        eassumption.
        intros Hc. eapply HD1. constructor; eauto.
      + intros [xs f] i. apply pre_curry_l; intros Hin1.
        apply pre_curry_l; intros Heq. subst.
        eapply bind_triple. eapply IHe.
        now eapply FVmap_inv_set_bound; eauto.
        eapply Disjoint_Included_l. now apply Setminus_Included.
        eapply Disjoint_Included_r; [| eassumption ].
        rewrite Union_assoc. apply Included_Union_preserv_l.
        now apply bound_var_occurs_free_Eproj_Included.
        eapply binding_in_map_antimon; [| eapply binding_in_map_set; eassumption ].
        normalize_occurs_free. rewrite <- Union_assoc.
        now rewrite <- Union_Setminus; eauto with Ensembles_DB typeclass_instances.
        eapply binding_not_in_map_set_not_In_S.
        eapply binding_not_in_map_antimon; [| eassumption ]...
        intros Hc. inv Hc.
        eapply HD1.
        constructor; [ eapply Setminus_Included; eassumption | now eauto ].
        inv H. now eapply Hnin'; eauto.
        eapply Disjoint_Included_l. now apply Setminus_Included.
        eapply Disjoint_Included_r; [| eassumption ].
        rewrite !Union_assoc. apply Included_Union_compat.
        now apply bound_var_occurs_free_Eproj_Included.
        reflexivity.
        intros Hc. eapply Hnin'. now eapply bound_var_occurs_free_Eproj_Included.
        intros B Hfe. eapply Hun. now eauto.
        intros [e' f'] i'. apply return_triple.
        intros i''. intros [Hin2 Hf2]. split.
        simpl in *. eapply Included_trans. eapply Hin1.
        repeat normalize_occurs_free...
        eapply fresh_monotonic; [| eassumption ]...
    - eapply post_mp.
      eapply exp_closure_conv_closed_fundefs with (e := Efun f2 e); eassumption.
      eapply bind_triple. now eapply get_named_str_fresh.
      intros Γ' s1. eapply pre_curry_l. intros Hf1.
      eapply bind_triple.
      + eapply post_conj.
        * eapply make_env_spec.
          eapply binding_in_map_antimon; [| eassumption ].
          intros x Hfv. eapply occurs_free_Efun. left.
          eapply fundefs_fv_correct. eassumption.
          eapply binding_not_in_map_antimon; [| eassumption ]...
          eassumption.
        * eapply make_env_occurs_free_Included. eassumption.
          assert (Heq : (FromList (PS.elements (fundefs_fv f2))) = FromSet (fundefs_fv f2)) by reflexivity.
          rewrite Heq, <- fundefs_fv_correct.
          eapply Disjoint_Included_l. now apply Setminus_Included.
          eapply Disjoint_Included_r; [| eassumption ].
          normalize_occurs_free...
      + intros [[c' FVmap'] f] _. eapply pre_strenghtening.
        intros s [H H'].
        match type of H with
          | @ex ?t1 (fun C => (@ex ?t2 (fun S' => @ex ?t3 (fun l => ?H1 /\ ?H2)))) =>
            assert (H6 : @ex t1 (fun C => (@ex t2 (fun S' => @ex t3 (fun l => H2)))))
              by (edestruct H as [C1 [S1 [l1 [_ H4']]]]; eauto)
        end.
        exact (conj H6 H').
        apply pre_curry_l. intros [C [S1 [l1 [Hproj [Hctx [Hbin [Hbnin Hinv']]]]]]].
        eapply pre_curry_l. intros He.
        eapply bind_triple.
        * eapply post_conj.
          eapply make_full_closure_spec; eassumption.
          eapply make_full_closure_occurs_free_Included.
          eapply Hun. now eauto.
        * intros [[FVmap_n FVmap_o] f'] _. eapply pre_strenghtening.
          intros s [H H'].
          match type of H with
            | @ex ?t1 (fun C => (@ex ?t2 (fun S' => ?H1 /\ ?H2))) =>
              assert (H6 : @ex t1 (fun C => (@ex t2 (fun S' => H2))))
                by (edestruct H as [C1 [S1' [_ H4']]]; eauto)
          end.
          exact (conj H6 H').
          apply pre_curry_l. intros [C' [S2 [Hproj' [Hctx' [Hfeq [Hbin1' [Hbin2' [Hbnin1' [Hbnin2' [Hinv1' Hinv2']]]]]]]]]].
          eapply pre_curry_l. intros He'.
          eapply bind_triple.
          eapply IHe. eassumption.
          eapply Disjoint_Included_l. now apply Setminus_Included.
          eapply Disjoint_Included_r; [| eassumption ].
          rewrite !Union_assoc. apply Included_Union_preserv_l.
          now apply bound_var_occurs_free_Efun_Included.
          eapply binding_in_map_antimon; [| eassumption ].
          now apply occurs_free_Efun_Included.
          eapply binding_not_in_map_antimon; [| eassumption ].
          rewrite <- (Included_Setminus_Disjoint _ (name_in_fundefs f2)).
          now eauto with Ensembles_DB.
          eapply Union_Disjoint_l.
          eapply Disjoint_Included_r; [| eassumption ].
          normalize_bound_var. do 2 apply Included_Union_preserv_l.
          now apply name_in_fundefs_bound_var_fundefs.
          eapply Disjoint_Singleton_l. intros Hc. eapply Hnin'.
          left. constructor. now apply name_in_fundefs_bound_var_fundefs.
          eapply Disjoint_Included_l. now apply Setminus_Included.
          eapply Disjoint_Included_r; [| eassumption ].
          rewrite !Union_assoc.
          eapply Included_Union_compat; [| now apply Included_refl ].
          now apply bound_var_occurs_free_Efun_Included.
          intros Hc. eapply Hnin'.
          now apply bound_var_occurs_free_Efun_Included.
          intros B Hfe. eapply Hun. now eauto.
          intros [e' f''] s2. eapply pre_curry_l. intros He''.
          eapply bind_triple.
          eapply post_conj.
          eapply pre_strenghtening;
            [| now eapply fundefs_closure_conv_in_image_subst_map ].
          now simpl; eauto.
          (* a silly way to obtain [fresh S (next_var s4)] but. Too bored
           * to prove it independently now *)
          eapply exp_closure_conv_bound_var_Included_mut.
          eapply Disjoint_Included_l. now apply Setminus_Included.
          eapply Disjoint_Included_r; [| eassumption ].
          rewrite Union_assoc. apply Included_Union_preserv_l.
          now apply bound_var_occurs_free_fundefs_Efun_Included.
          intros B' s3. eapply return_triple. simpl in *.
          intros s4 [Hseq [_ Hf4]] Hclo. split.
          eapply Included_trans. eapply He.
          assert (Heq : (FromList (PS.elements (fundefs_fv f2))) = FromSet (fundefs_fv f2)) by reflexivity.
          rewrite Heq, <- fundefs_fv_correct.
          normalize_occurs_free.
          rewrite Hctx, <- app_ctx_f_fuse in Hclo. simpl in Hclo.
          assert (Hclo' : Same_set _ (occurs_free_fundefs B') (Empty_set _))
            by (eapply Hclo; apply funs_in_exp_ctx_app; eauto).
          rewrite Hclo', Union_Empty_set_neut_l.
          repeat normalize_occurs_free. apply Union_Included.
          now eauto with Ensembles_DB.
          do 2 eapply Setminus_Included_Included_Union.
          eapply Included_trans. eapply He'.
          apply Union_Included. now eauto with Ensembles_DB.
          apply Union_Included. rewrite <- Hseq...
          eapply Setminus_Included_Included_Union.
          eapply Included_trans. eassumption.
          rewrite Union_commut, (Union_commut (occurs_free_fundefs f2)), !Union_assoc.
          do 3 apply Included_Union_preserv_l.
          rewrite Union_Setminus_Included; now eauto with Ensembles_DB typeclass_instances.
          eapply fresh_monotonic; [| eassumption ]...
    - eapply bind_triple.
      + eapply get_var_occurs_free_Included. eassumption.
        intros Hc.  eapply HD1. now constructor; eauto.
      + intros [x f] s1.
        apply pre_curry_l. intros He. apply pre_curry_l; intros Heq; subst.
        eapply bind_triple.
        eapply get_vars_occurs_free_Included. eassumption.
        eapply Disjoint_Included_l. now apply Setminus_Included.
        repeat normalize_occurs_free_in_ctx...
        intros [xs f'] s2.
        apply pre_curry_l. intros He'. apply pre_curry_l; intros Heq; subst.
        eapply bind_triple. now apply get_name_spec.
        intros y s3. apply pre_curry_l. intros Hfy.
        eapply bind_triple. now apply get_name_spec.
        intros z s4. apply pre_curry_l. intros Hfz.
        apply return_triple. intros s5 Hf.
        split.
        simpl. eapply Included_trans. apply He.
        eapply Included_trans. apply He'.
        repeat normalize_occurs_free. rewrite FromList_cons.
        now eauto 20 with Ensembles_DB. (* takes some time... *)
        eapply fresh_monotonic; [| eassumption ]...
    -  eapply bind_triple.
      + eapply get_vars_occurs_free_Included.
        eassumption. eapply Disjoint_Included_r; [| eassumption ].
        rewrite occurs_free_Eprim...
      + intros [xs f] i. apply pre_curry_l; intros Hin1.
        apply pre_curry_l; intros Heq. subst.
        eapply bind_triple. eapply IHe.
        now eapply FVmap_inv_set_bound; eauto.
        eapply Disjoint_Included_l. now apply Setminus_Included.
        eapply Disjoint_Included_r; [| eassumption ].
        rewrite Union_assoc. apply Included_Union_preserv_l.
        now apply bound_var_occurs_free_Eprim_Included.
        eapply binding_in_map_antimon; [| eapply binding_in_map_set; eassumption ].
        normalize_occurs_free. rewrite <- Union_assoc.
        now rewrite <- Union_Setminus; eauto with Ensembles_DB typeclass_instances.
        eapply binding_not_in_map_set_not_In_S.
        eapply binding_not_in_map_antimon; [| eassumption ]...
        intros Hc. inv Hc.
        eapply HD1. constructor; [| now eauto ]. now eapply Setminus_Included; eauto.
        inv H. now eapply Hnin'; eauto.
        eapply Disjoint_Included_l. now apply Setminus_Included.
        eapply Disjoint_Included_r; [| eassumption ].
        rewrite !Union_assoc. apply Included_Union_compat.
        now apply bound_var_occurs_free_Eprim_Included.
        reflexivity.
        intros Hc.  eapply Hnin'. now eapply bound_var_occurs_free_Eprim_Included.
        now intros B Hfe; eapply Hun; eauto.
        intros [e' f'] i'. apply return_triple.
        intros i''. simpl. intros [Hin2 Hf2]. split.
        simpl in *. eapply Included_trans. eapply Hin1.
        repeat normalize_occurs_free...
        eapply fresh_monotonic; [| eassumption ]...
    - eapply bind_triple.
      eapply get_var_occurs_free_Included. eassumption.
      intros Hc. eapply HD1. now constructor; eauto.
      intros [x f] _. apply return_triple.
      intros s1 [He [Heq Hf]]. subst. split.
      now apply He.
      eapply fresh_monotonic; [| eassumption ]...
  Qed.

  Transparent exp_closure_conv fundefs_closure_conv.

  Lemma get_var_unique_bindings x FVmap c Γ S S' :
    ~ In _ S x ->
    {{ fun s => fresh S (next_var s) }}
      get_var clo_tag x FVmap c Γ
    {{ fun s t s' =>
         let (x', f) := t in
         (forall e,
            Included _ (bound_var e) (Union _ S' (Setminus _ S (Singleton _ x'))) ->
            Disjoint _ S' S  ->
            unique_bindings e ->
            unique_bindings (f e)) /\
         fresh (Setminus _ S (Singleton _ x')) (next_var s')
     }}.
  Proof with now eauto with Ensembles_DB.
    intros Hnin. unfold get_var. destruct (Maps.PTree.get x FVmap) eqn:Heq.
    - destruct v.
      + eapply bind_triple. apply get_name_spec.
        intros x' i. apply return_triple.
        intros i' [Hf Hf']. split; [| eassumption].
        intros e Hin Hd Hun. constructor; [| eassumption ].
        intros Hc. eapply Hd.
        eapply Hin in Hc. inv Hc. constructor. eauto.
        eapply Hf. zify; lia. inv H. exfalso; eauto.
      + eapply bind_triple. apply get_name_spec.
        intros x' i. apply return_triple.
        intros i' [Hf Hf']. split; [| eassumption].
        intros e Hin Hd Hun. constructor; [| eassumption ].
        intros Hc. eapply Hd.
        eapply Hin in Hc. inv Hc. constructor. eauto.
        eapply Hf. zify; lia. inv H. exfalso; eauto.
      + apply return_triple.
        intros i' Hf. split.
        intros e Hin Hd Hun. eassumption.
        intros x' Hleq. constructor. now eauto.
        intros Hc; inv Hc. now eauto.
    - apply return_triple; simpl. intros i Hf. split.
      intros e Hin Hd Hun. eassumption.
      intros x' Hleq. constructor. now eauto.
      intros Hc; inv Hc. now eauto.
  Qed.

  Lemma get_vars_unique_bindings xs FVmap c Γ S S' :
    Disjoint _ S (FromList xs) ->
    {{ fun s => fresh S (next_var s) }}
      get_vars clo_tag xs FVmap c Γ
    {{ fun s t s' =>
         let (xs', f) := t in
         (forall e,
            Included _ (bound_var e) (Union _ S' (Setminus _ S (FromList xs'))) ->
            Disjoint _ S' S  ->
            unique_bindings e ->
            unique_bindings (f e)) /\
         fresh (Setminus _ S (FromList xs')) (next_var s')
     }}.
  Proof with now eauto with Ensembles_DB.
    revert S S'; induction xs; intros S S' Hd.
    - apply return_triple. intros i Hf.
      split;
        intros ?; rewrite !FromList_nil, !Setminus_Empty_set_neut_r in *; eauto.
    - eapply bind_triple.
      + apply get_var_unique_bindings;
        intros Hin'; eapply Hd; constructor; eauto;
        rewrite FromList_cons; left; eauto.
      + intros [x f] i.
        apply pre_curry_l. intros Hx.
        eapply bind_triple.
        * rewrite FromList_cons in Hd.
          eapply post_conj;
          [apply get_vars_bound_var_Included | apply IHxs ]...
        * intros [xs' f'] i'. apply return_triple.
          intros i'' [[Hxs1 _] [Hxs2 Hf']]. split.
          intros e Hin' Hd' Hun. eapply Hx.
          eapply Hxs1. eapply Included_trans. eassumption.
          rewrite FromList_cons. apply Included_Union_compat. now apply Included_refl.
          eauto with Ensembles_DB.
          eassumption.
          eapply Hxs2. eapply Included_trans. eassumption.
          apply Included_Union_compat. now apply Included_refl.
          rewrite FromList_cons... eauto with Ensembles_DB.
          eassumption. rewrite FromList_cons, <- Setminus_Union...
  Qed.

  Lemma make_full_closure_unique_bindings B m1 m2 Γ S :
    unique_functions B ->
    {{ fun s => fresh S (next_var s) }}
      make_full_closure clo_tag B m1 m2 Γ
    {{ fun s t s' =>
         let '(m1', _, f) := t in
         (forall e,
            Disjoint _ (bound_var e) (bound_var_fundefs B) ->
            unique_bindings e ->
            unique_bindings (f e)) /\
         fresh (Setminus _ S (image (subst m1') (name_in_fundefs B)))
               (next_var s')
     }}.
  Proof with now eauto with Ensembles_DB.
    revert S; induction B; intros S Hun.
    - eapply bind_triple. now apply get_name_spec.
      intros x s1. apply pre_curry_l. intros Hf1. inv Hun.
      eapply bind_triple. eapply post_conj. now eapply IHB.
      now apply make_full_closure_bound_var_Included.
      intros [[m1' m2'] f1] _. apply return_triple.
      intros s2 [[Hun Hf] [Heq [Hinc _]]]. split.
      + intros e' Hun1 Hin1. constructor.
        intros Hb. eapply Hun1.
        constructor. apply Heq in Hb. inv Hb; eauto.
        exfalso. now eauto. rewrite bound_var_fundefs_Fcons...
        eapply Hun; eauto.
        rewrite bound_var_fundefs_Fcons in Hun1.
        eauto with Ensembles_DB.
      + eapply fresh_monotonic; [| eassumption ].
        rewrite <- subst_MRFun_f_eq. simpl.
        rewrite image_extend_In_S.  rewrite Setminus_Union.
        apply Included_Setminus_compat. reflexivity.
        rewrite Union_commut. eapply Included_Union_compat.
        reflexivity. apply image_monotonic...
        now eauto.
    - apply return_triple. intros s Hf.
      simpl. split. now eauto.
      rewrite image_Empty_set, Setminus_Empty_set_neut_r. eassumption.
  Qed.

  Lemma make_full_closure_injective S B m1 m2 Γ :
    Disjoint var S (name_in_fundefs B) ->
    unique_functions B ->
    {{ fun s => fresh S (next_var s) }}
      make_full_closure clo_tag B m1 m2 Γ
    {{ fun s p s' =>
         let '(m1', m2', f) := p in
         injective_subdomain (name_in_fundefs B) (subst m1') /\
         fresh S (next_var s')
     }}.
  Proof with now eauto with Ensembles_DB.
    revert S. induction B; intros S HD Hun.
    - eapply bind_triple. now apply get_name_spec.
      intros v' s1. apply pre_curry_l. intros Hfv'.
      eapply bind_triple.
      + eapply post_conj.
        * eapply IHB.
          eapply Disjoint_Included_l. now apply Setminus_Included.
          now eauto with Ensembles_DB. inv Hun. eassumption.
        * eapply make_full_closure_bound_var_Included.
      + intros [[m1' m2'] f'] _.
        apply return_triple. intros s2 [[HInj Hf] [_ [Hinc _]]].
        split.
        * simpl. apply injective_subdomain_Union.
          now apply injective_subdomain_Singleton.
          rewrite <- subst_MRFun_f_eq. eapply injective_subdomain_extend'.
          eapply injective_subdomain_antimon; [ eassumption |]...
          intros Hc. eapply Hinc. eapply image_monotonic; [| eassumption ].
          now eapply Setminus_Included. now eauto.
          rewrite image_Singleton.
          unfold subst at 1. rewrite M.gss, <- subst_MRFun_f_eq.
          rewrite image_extend_not_In_S.
          eapply Disjoint_Included_r. eassumption.
          eapply Disjoint_Setminus_r. reflexivity.
          inv Hun. eassumption.
        * eapply fresh_monotonic; [| eassumption ].
          now apply Setminus_Included.
    - eapply return_triple. intros s1 Hf. split; [| eassumption ].
      now apply injective_subdomain_Empty_set.
  Qed.


  Lemma exp_closure_conv_unique_bindings_mut :
    (forall e c Γ FVmap S
       (HD: Disjoint _ S (Union _ (bound_var e) (occurs_free e)))
       (Hun : unique_bindings e),
       {{ fun s => fresh S (next_var s) }}
         exp_closure_conv clo_tag e FVmap c Γ
       {{ fun s ef s' =>
            unique_bindings ((snd ef) (fst ef)) /\
            fresh (Setminus _ S (bound_var ((snd ef) (fst ef)))) (next_var s')
        }}) /\
    (forall B FVmap S c
       (HD : Disjoint _ S (Union _ (bound_var_fundefs B) (occurs_free_fundefs B)))
       (HD' : Disjoint _  (image (subst FVmap) (name_in_fundefs B))
                       (Union _ (bound_var_fundefs B) S))
       (Hun : unique_bindings_fundefs B)
       (Hinj : injective_subdomain (name_in_fundefs B) (subst FVmap)),
       {{ fun s => fresh S (next_var s) }}
         fundefs_closure_conv clo_tag B FVmap c
       {{ fun s B' s' =>
            unique_bindings_fundefs B' /\
            Disjoint _ (name_in_fundefs B) (bound_var_fundefs B') /\
            fresh (Setminus _ S (bound_var_fundefs B')) (next_var s')
        }}).
  Proof with now eauto with Ensembles_DB.
    exp_defs_induction IHe IHl IHB; intros.
    - eapply bind_triple.
      + eapply post_conj;
        [ eapply get_vars_unique_bindings | eapply get_vars_bound_var_Included' ];
        (eapply Disjoint_Included_r; [| eassumption ]);
        rewrite occurs_free_Econstr...
      + intros [xs f] i.
        eapply pre_strenghtening. intros ? [[Hun' _] [Hin Hf]].
        exact (conj (conj Hun' Hin) Hf).
        apply pre_curry_l; intros [Hun' Hin'].
        eapply bind_triple. inv Hun.
        eapply post_conj;
          [ eapply IHe; eauto | eapply exp_closure_conv_bound_var_Included_mut ];
        (eapply Disjoint_Included_l;
         [ now apply Setminus_Included |
           eapply Disjoint_Included_r;
             [ now apply bound_var_occurs_free_Econstr_Included | eassumption ]]).
        intros [e' f'] i'. apply return_triple.
        intros i''. intros [[Hun'' Hf''] [Hinc _]]. split.
        simpl in *. inv Hun. eapply Hun'. rewrite bound_var_Econstr.
        apply Union_Included;
          [ | apply Included_Union_preserv_l; now apply Included_Union_l ].
        rewrite <- Union_assoc...
        repeat normalize_bound_var_in_ctx. now eauto with Ensembles_DB.
        constructor; [| eassumption ]. intros Hc. eapply Hinc in Hc.
        inv Hc. now eauto. inv H. eapply HD. constructor. now eauto. now left; eauto.
        eapply fresh_monotonic; [| eassumption ]. simpl in *.
        rewrite Setminus_Union.
        rewrite <- (Setminus_Disjoint (Setminus _ _ _) (Singleton _ v)), Setminus_Union.
        apply Included_Setminus_compat. now eauto with Ensembles_DB.
        eapply Included_trans. eapply Hin'. rewrite bound_var_Econstr...
        eapply Setminus_Disjoint_preserv_l...
    - eapply bind_triple with (post' := fun _ P i =>  P = [] /\  fresh S (next_var i)) .
      now apply return_triple.
      intros P' i. apply pre_curry_l. intros Heq; subst.
      eapply bind_triple.
       eapply post_conj;
        [ eapply get_var_unique_bindings | eapply get_var_bound_var_Included' ];
        intros Hc; eapply HD; now constructor; eauto.
       intros [x f] _. apply return_triple. intros i' [[He _] [Hin Hf]].
       split; eauto. simpl. eapply He; try now constructor.
       rewrite bound_var_Ecase_nil... eauto with Ensembles_DB.
       eapply fresh_monotonic; [| eassumption ]. simpl.
       eapply Included_Setminus_compat. reflexivity.
       eapply Included_trans. eapply Hin. rewrite bound_var_Ecase_nil...
    - unfold exp_closure_conv. setoid_rewrite assoc.
      inv Hun. eapply bind_triple.
      + eapply post_conj.
        * eapply IHe. eapply Disjoint_Included_r; [| eassumption ].
          eapply bound_var_occurs_free_Ecase_Included. now constructor.
          eassumption.
        * eapply exp_closure_conv_bound_var_Included_mut.
          eapply Disjoint_Included_r; [| eassumption ].
          eapply bound_var_occurs_free_Ecase_Included. now constructor.
      + intros [e' f'] s'. simpl. setoid_rewrite assoc. simpl.
        setoid_rewrite st_eq_Ecase.
        eapply pre_strenghtening. intros i [[Hun' Hf] [Hin _]].
        exact (conj (conj Hun' Hin) Hf).
        eapply pre_curry_l; intros [He' Hin].
        eapply bind_triple.
        { eapply post_conj.
          - eapply IHl with (FVmap := FVmap) (Γ := Γ) (c := c0).
            eapply Disjoint_Included_l. now apply Setminus_Included.
            eapply Disjoint_Included_r; [| eassumption ].
            now eapply bound_var_occurs_free_Ecase_cons_Included.
            eassumption.
          - eapply post_conj.
            + eapply pre_strenghtening;
              [ | now eapply exp_closure_conv_is_exp_ctx
                  with (e := (Ecase v l)) (c := c0) (Γ := Γ) (FVmap := FVmap)].
              intros. simpl; eauto.
            + eapply exp_closure_conv_bound_var_Included_mut
              with (e := (Ecase v l)) (c := c0) (Γ := Γ) (FVmap := FVmap).
              eapply Disjoint_Included_l. now apply Setminus_Included.
              eapply Disjoint_Included_r; [| eassumption ].
              now eapply bound_var_occurs_free_Ecase_cons_Included. }
        intros [e'' f''] s''.
        destruct e''; apply return_triple;
        try now (intros ? [[? Hf] [? [? ?]]]; split;
                 [ now eauto | eapply fresh_monotonic; [| now apply Hf ];
                               eauto with Ensembles_DB ]).
        intros s''' [[Hin' Hf'] [[C Hctx] [Hin'' Hf'']]]; split; eauto. simpl in *.
        rewrite Hctx. apply unique_bindings_ctx_app_Ecase_cons.
        eassumption. now rewrite <- Hctx.
        rewrite <- Hctx. eapply Disjoint_Included_r. eassumption.
        eapply Union_Disjoint_r. eapply Disjoint_Included_l. eassumption.
        repeat normalize_bound_var_in_ctx...
        now eauto with Ensembles_DB.
        simpl in *. rewrite Hctx in *. rewrite bound_var_ctx_app_Ecase_cons.
        rewrite <- Setminus_Union. eassumption.
    - eapply bind_triple.
      + eapply post_conj;
        [ eapply get_var_unique_bindings | eapply get_var_bound_var_Included' ];
        intros Hc; eapply HD; eauto.
      + intros [xs f] i. eapply pre_strenghtening. intros ? [[Hun' _] [Hin Hf]].
        exact (conj (conj Hun' Hin) Hf).
        apply pre_curry_l; intros [Hun' Hin']. inv Hun.
        eapply bind_triple.
        * eapply post_conj.
          eapply IHe. eapply Setminus_Disjoint_preserv_l.
          eapply Disjoint_Included_r; [| eassumption ].
          now eapply bound_var_occurs_free_Eproj_Included.
          eassumption.
          eapply exp_closure_conv_bound_var_Included_mut.
          eapply Setminus_Disjoint_preserv_l.
          eapply Disjoint_Included_r; [| eassumption ].
          now eapply bound_var_occurs_free_Eproj_Included.
        * intros [e' f'] s'. simpl. apply return_triple.
          intros i''. intros [[Hun'' Hf''] [Hinc _]]. split.
          simpl in *. eapply Hun'. rewrite bound_var_Eproj.
          apply Union_Included;
            [ | apply Included_Union_preserv_l; now apply Included_Union_l ].
        rewrite <- Union_assoc...
        repeat normalize_bound_var_in_ctx...
        constructor; [| eassumption ]. intros Hc. eapply Hinc in Hc.
        inv Hc. now eauto. inv H. eapply HD. constructor. now eauto. now left; eauto.
        eapply fresh_monotonic; [| eassumption ]. simpl in *.
        rewrite Setminus_Union.
        rewrite <- (Setminus_Disjoint (Setminus _ _ _) (Singleton _ v)), Setminus_Union.
        apply Included_Setminus_compat. now eauto with Ensembles_DB.
        eapply Included_trans. eapply Hin'. rewrite bound_var_Eproj...
        eapply Setminus_Disjoint_preserv_l...
    - eapply bind_triple. now apply get_named_str_fresh.
      intros Γ' s1. eapply pre_curry_l. intros Hf1. unfold make_env.
      assert (Heqel : (@FromList var (PS.elements (fundefs_fv f2))) = FromSet (fundefs_fv f2)) by reflexivity.
      destruct
        ((fix
            add_fvs (l : list M.elt) (n : N) (map : Maps.PTree.t VarInfo)
            {struct l} : Maps.PTree.t VarInfo * N :=
            match l with
              | [] => (map, n)
              | x :: xs => add_fvs xs (n + 1)%N (Maps.PTree.set x (FVar n) map)
            end) _ _ _ ) as [m1' n].
      setoid_rewrite assoc.
      eapply bind_triple.
      eapply post_conj;
        [ eapply get_vars_unique_bindings | eapply get_vars_bound_var_Included' ];
        eapply Setminus_Disjoint_preserv_l;
        (eapply Disjoint_Included_r; [| eassumption ]);
        rewrite Heqel, <- fundefs_fv_correct; rewrite occurs_free_Efun...
      intros [xs f1] s2. eapply pre_strenghtening. intros ? [[Hun1 _] [Hin Hf]].
      exact (conj (conj Hun1 Hin) Hf).
      apply pre_curry_l; intros [Hun1 Hin1]. inv Hun.
      setoid_rewrite assoc.
      eapply bind_triple. now apply make_record_ctor_tag_preserves_prop.
      intros c1 s3.  eapply bind_triple.
      now eapply return_triple with
      (Post := fun s r s' =>
                 fresh (Setminus var (Setminus var S (Singleton var Γ')) (FromList xs))
                       (next_var s') /\
                 r = (c1, m1', fun e0 : exp => f1 (Econstr Γ' c1 xs e0))).
      intros [[c' m] f] s4. eapply pre_curry_r; intros Heq; inv Heq.
      eapply bind_triple.
      eapply post_conj;
        [ eapply make_full_closure_unique_bindings |
          eapply post_conj;
            [ eapply make_full_closure_bound_var_Included
            | eapply make_full_closure_injective ]].
      now apply unique_bindings_fundefs_unique_functions.
      eapply Disjoint_Included_l; [ now apply Setminus_Included | ].
      eapply Disjoint_Included_l; [ now apply Setminus_Included | ].
      eapply Disjoint_Included_r. now apply name_in_fundefs_bound_var_fundefs.
      repeat normalize_bound_var_in_ctx...
      now eapply unique_bindings_fundefs_unique_functions.
      intros [[m m'] f'] s5. eapply pre_strenghtening.
      intros ? [[Hun2 Hf] [[Hseq [Hin2 _]] [Hinj _]]].
      exact (conj (conj Hun2 (conj Hin2 (conj Hseq Hinj))) Hf).
      apply pre_curry_l; intros [Hun2 [Hin2 [Hseq Hinj]]].
      eapply bind_triple.
      + eapply post_conj.
         eapply IHe. rewrite Setminus_Union.
         rewrite Setminus_Union.
         eapply Disjoint_Included_l; [ now apply Setminus_Included | ].
         eapply Disjoint_Included_r; [| eassumption ].
         now eapply bound_var_occurs_free_Efun_Included. eassumption.
         eapply exp_closure_conv_bound_var_Included_mut. rewrite Setminus_Union.
         rewrite Setminus_Union.
         eapply Disjoint_Included_l; [ now apply Setminus_Included | ].
         eapply Disjoint_Included_r; [| eassumption ].
         now eapply bound_var_occurs_free_Efun_Included.
      + intros [e' f''] s6. eapply pre_strenghtening. intros ? [[Hun3 Hf] [Hin3 _]].
        exact (conj (conj Hun3 Hin3) Hf). eapply pre_curry_l. intros [Hun3 Hin3]. simpl in *.
        eapply bind_triple.
        * eapply post_conj.
          eapply IHB. rewrite !Setminus_Union.
          eapply Disjoint_Included_l; [ now apply Setminus_Included | ].
          eapply Disjoint_Included_r; [| eassumption ].
          now eapply bound_var_occurs_free_fundefs_Efun_Included.
          apply Union_Disjoint_r.
          eapply Disjoint_Included_l. eassumption.
          eapply Disjoint_Included_l; [ now apply Setminus_Included | ].
          eapply Disjoint_Included_l; [ now apply Setminus_Included | ].
          normalize_bound_var_in_ctx...
          apply Setminus_Disjoint_preserv_r. now apply Disjoint_Setminus_r.
          eassumption. eassumption.
          eapply post_conj.
          eapply exp_closure_conv_bound_var_Included_mut. rewrite !Setminus_Union.
          eapply Disjoint_Included_l; [ now apply Setminus_Included | ].
          eapply Disjoint_Included_r; [| eassumption ].
          now eapply bound_var_occurs_free_fundefs_Efun_Included.
          eapply pre_strenghtening; [| eapply fundefs_closure_conv_in_image_subst_map ].
          now intros; simpl; eauto.
        * intros B' s7. apply return_triple.
          intros s8 [[Hun4 [Hd Hf']] [[Hinc4 _] Hin5]]. simpl in *.
          split. eapply Hun1. repeat normalize_bound_var.
          rewrite Hseq. repeat apply Union_Included.
          eapply Included_trans. eassumption.
          repeat apply Union_Included. eapply Included_Union_preserv_l.
          now eapply (Included_Union_l _ (Union _ (bound_var e) (Singleton _ Γ'))).
          eapply Included_Union_preserv_r... rewrite <- Hin5.
          eapply Included_trans. now eapply name_in_fundefs_bound_var_fundefs.
          eapply Included_trans. eassumption.
          now eauto with Ensembles_DB.
          eapply Included_trans. eassumption.
          now eauto with Ensembles_DB.
          do 2 eapply Included_Union_preserv_l.
          now apply name_in_fundefs_bound_var_fundefs.
          now eauto with Ensembles_DB.
          rewrite Union_assoc. eapply Union_Disjoint_l.
          repeat normalize_bound_var_in_ctx.
          eapply Disjoint_Included_r. now apply Setminus_Included.
          eapply Disjoint_Included_l_sym; [| eassumption ]...
          eapply Disjoint_Setminus_r...
          constructor. intros Hc. eapply bound_var_Efun in Hc.
          inv Hc. eapply Hinc4 in H. inv H.
          eapply HD with (x := Γ'). constructor. eapply Hf1. zify; lia.
          now eauto.
          inv H0. inv H. inv H0. inv H. inv H0. now eauto.
          eapply Hin2 in H. inv H. inv H0. now eauto.
          rewrite Hseq in H. inv H. eapply Hin3 in H0.
          inv H0. eapply HD with (x := Γ'). constructor. eapply Hf1. zify; lia.
          now repeat normalize_bound_var; eauto. inv H.
          inv H0. inv H. now eauto.
          eapply HD with (x := Γ'). constructor. eapply Hf1. zify; lia.
          left. rewrite bound_var_Efun. left. now eapply name_in_fundefs_bound_var_fundefs.
          constructor. eapply Hun2. eapply Disjoint_Included_l. eassumption.
          eapply Union_Disjoint_l. eassumption.
          eapply (Disjoint_Included_l _ _ S). now eauto with Ensembles_DB.
          repeat normalize_bound_var_in_ctx...
          eassumption. eassumption.
          rewrite Hseq. apply Union_Disjoint_l; [| eassumption ].
          eapply Disjoint_Included_r. eassumption.
          eapply Union_Disjoint_r.
          eapply Disjoint_Included_l. eassumption.
          eapply Union_Disjoint_l. eassumption.
          do 3 eapply Setminus_Disjoint_preserv_l.
          repeat normalize_bound_var_in_ctx...
          apply Union_Disjoint_r. now eauto with Ensembles_DB.
          eapply Disjoint_Included_l. eassumption. eapply Union_Disjoint_l.
          eapply Disjoint_Included_r. eassumption.
          do 2 eapply Setminus_Disjoint_preserv_r.
          repeat normalize_bound_var_in_ctx...
          now eauto with Ensembles_DB.
          eapply fresh_monotonic; [| eassumption ].
          rewrite !Setminus_Union.
          eapply Included_trans;
            [| eapply Included_Setminus_compat;
               [ now apply Included_refl | now eapply Hin1 ] ].
          repeat normalize_bound_var. rewrite Hseq.
          rewrite <- !Union_assoc, (Union_commut (name_in_fundefs f2) _), <- !Setminus_Union.
          rewrite <- (Included_Setminus_Disjoint _ (name_in_fundefs f2)).
          rewrite !Setminus_Union.
          eapply Included_Setminus_compat;
            [ now apply Included_refl  | now eauto 10 with Ensembles_DB ].
          do 4 eapply Setminus_Disjoint_preserv_l.
          eapply Disjoint_Included_r. now apply name_in_fundefs_bound_var_fundefs.
          repeat normalize_bound_var_in_ctx...
    - eapply bind_triple.
      + eapply post_conj;
        [ eapply get_var_unique_bindings |
          eapply post_conj;
            [ eapply get_var_bound_var_Included with (S' := Empty_set _) |
              eapply get_var_bound_var_Included' ]];
        intros Hc; eapply HD; eauto.
      + intros [x f] s1. eapply pre_strenghtening.
        intros ? [[Hun1 _] [[Hin Hf] [Hin' _]]].
        exact (conj (conj Hun1 (conj Hin Hin')) Hf).
        eapply pre_curry_l; intros [Hun1 [Hin1 Hin1']]. eapply bind_triple.
        eapply post_conj;
          [ eapply get_vars_unique_bindings |
            eapply post_conj;
              [ eapply get_vars_bound_var_Included |
                eapply get_vars_bound_var_Included' ]];
        normalize_bound_var_in_ctx; normalize_occurs_free_in_ctx...
        intros [xs f'] s2. eapply pre_strenghtening.
        intros ? [[Hun2 _] [[Hin2 Hf2] [Hin2' _]]].
        exact (conj (conj Hun2 (conj Hin2 Hin2')) Hf2).
        eapply pre_curry_l; intros [Hun2 [Hin2 Hin2']].
        eapply bind_triple. now apply get_name_spec.
        intros g' s3. eapply pre_curry_l. intros Hg'.
        eapply bind_triple. now apply get_name_spec.
        intros Γ' s4. eapply pre_curry_l. intros HΓ'.
        apply return_triple. intros s5. intros Hfs5. simpl. split.
        eapply Hun1.
        eapply Included_trans. eapply Hin2.
        repeat normalize_bound_var. rewrite Union_Empty_set_neut_l.
        apply Union_Included.
        apply Included_Union_preserv_r. eapply Singleton_Included.
        eapply HΓ'. zify; lia.
        apply Included_Union_preserv_r. eapply Singleton_Included.
        eapply Hg'. zify; lia.
        now apply Included_refl. apply Disjoint_sym. eassumption.
        eapply Hun2. repeat normalize_bound_var. rewrite Union_Empty_set_neut_l.
        apply Union_Included.
        apply Included_Union_preserv_r. eapply Singleton_Included.
        eapply HΓ'. zify; lia.
        apply Included_Union_preserv_r. eapply Singleton_Included.
        eapply Hg'. zify; lia.
        eapply Disjoint_sym. eapply Disjoint_Included_l; [| eassumption ]...
        constructor.
        intros Hc. inv Hc. eapply HΓ' with (y := g'). zify; lia.
        now eauto. now inv H5.
        constructor. intros Hc. now inv Hc.
        now constructor.
        eapply fresh_monotonic; [| eassumption ]. rewrite !Setminus_Union.
        apply Included_Setminus_compat. reflexivity.
        eapply Included_trans. now apply Hin1'.
        apply Union_Included; [| now eauto with Ensembles_DB ].
        eapply Included_trans. now apply Hin2'.
        apply Union_Included; [| now eauto with Ensembles_DB ].
        repeat normalize_bound_var...
    - eapply bind_triple.
      + eapply post_conj;
        [ eapply get_vars_unique_bindings | eapply get_vars_bound_var_Included' ];
        (eapply Disjoint_Included_r; [| eassumption ]);
        rewrite occurs_free_Eprim...
      + intros [xs f] i.
        eapply pre_strenghtening. intros ? [[Hun' _] [Hin Hf]].
        exact (conj (conj Hun' Hin) Hf).
        apply pre_curry_l; intros [Hun' Hin'].
        eapply bind_triple. inv Hun.
        eapply post_conj;
          [ eapply IHe; eauto | eapply exp_closure_conv_bound_var_Included_mut ];
        (eapply Disjoint_Included_l;
         [ now apply Setminus_Included |
           eapply Disjoint_Included_r;
             [ now apply bound_var_occurs_free_Eprim_Included | eassumption ]]).
        intros [e' f'] i'. apply return_triple.
        intros i''. intros [[Hun'' Hf''] [Hinc _]]. split.
        simpl in *. inv Hun. eapply Hun'. rewrite bound_var_Eprim.
        apply Union_Included;
          [ | apply Included_Union_preserv_l; now apply Included_Union_l ].
        rewrite <- Union_assoc...
        repeat normalize_bound_var_in_ctx. now eauto with Ensembles_DB.
        constructor; [| eassumption ]. intros Hc. eapply Hinc in Hc.
        inv Hc. now eauto. inv H. eapply HD. constructor. now eauto. now left; eauto.
        eapply fresh_monotonic; [| eassumption ]. simpl in *.
        rewrite Setminus_Union.
        rewrite <- (Setminus_Disjoint (Setminus _ _ _) (Singleton _ v)), Setminus_Union.
        apply Included_Setminus_compat. now eauto with Ensembles_DB.
        eapply Included_trans. eapply Hin'. rewrite bound_var_Eprim...
        eapply Setminus_Disjoint_preserv_l...
    - eapply bind_triple.
      + eapply post_conj;
        [ eapply get_var_unique_bindings |
          eapply get_var_bound_var_Included' ];
        intros Hc; eapply HD; eauto.
      + intros [x f] s1. apply return_triple.
        intros s2 [[Hun' Hf] [Hin' Hf']].
        split. simpl. eapply Hun'. rewrite bound_var_Ehalt.
        now apply Included_Union_l. now eauto with Ensembles_DB.
        now constructor.
        simpl. eapply fresh_monotonic; [| eassumption ].
        eapply Included_Setminus_compat. reflexivity.
        eapply Included_trans. now apply Hin'.
        normalize_bound_var...
    - eapply bind_triple. now apply get_name_spec.
      intros x s1. eapply pre_curry_l. intros Hfx. inv Hun. eapply bind_triple.
      + eapply post_conj;
        [ eapply IHe; eauto | eapply exp_closure_conv_bound_var_Included_mut ];
        (eapply Disjoint_Included_l;
         [ now apply Setminus_Included |
           eapply Disjoint_Included_r;
             [ now apply bound_var_occurs_free_Fcons_Included  | eassumption ]]).
      + intros [e' f] s2.
        eapply pre_strenghtening. intros ? [[Hun Hf] [Hin _]].
        exact (conj (conj Hun Hin) Hf).
        apply pre_curry_l; intros [Hun Hin].
        eapply bind_triple.
        eapply post_conj.
        eapply IHB.
        eapply Disjoint_Included_l; [ now apply Setminus_Included | ].
        eapply Disjoint_Included_l; [ now apply Setminus_Included | ].
        eapply Disjoint_Included_r; [| eassumption ].
        now eapply bound_var_occurs_free_fundefs_Fcons_Included.
        simpl in *.
        eapply Disjoint_Included; [| | now apply HD' ].
        normalize_bound_var... apply image_monotonic...
        eassumption.
        eapply injective_subdomain_antimon. eassumption.
        now eauto with Ensembles_DB.
        eapply post_conj.
        eapply exp_closure_conv_bound_var_Included_mut.
        eapply Disjoint_Included_l; [ now apply Setminus_Included | ].
        eapply Disjoint_Included_l; [ now apply Setminus_Included | ].
        eapply Disjoint_Included_r; [| eassumption ].
        now eapply bound_var_occurs_free_fundefs_Fcons_Included.
        eapply pre_strenghtening; [| eapply fundefs_closure_conv_in_image_subst_map ].
        now intros; simpl; eauto.
        intros B' s3. eapply return_triple. intros s4 [[Hun' [HD'' Hf4]] [[Hin' _] Hseq]].
        simpl in *. split.
        * constructor; eauto. intros Hb. eapply Hin in Hb.
          destruct (Maps.PTree.get v FVmap) as [v' |] eqn:Heq; try destruct v';
          try (inv Hb; [ now eauto |]; inv H; eapply HD;
               constructor; [ eassumption |
                              normalize_bound_var; now eauto with Ensembles_DB ]).
          eapply HD'. constructor. now eexists; eauto.
          unfold subst. rewrite Heq. normalize_bound_var. inv Hb.
          now eauto. right. now eapply H.
          intros Hb. eapply Hin' in Hb.
          destruct (Maps.PTree.get v FVmap) as [v' |] eqn:Heq; try destruct v';
          try (inv Hb; [ now eauto |
                         inv H; [ inv H0; inv H; eapply HD; constructor;
                                  [ eassumption
                                  | normalize_bound_var; now eauto with Ensembles_DB ]
                                |  eapply HD'; constructor;
                                   [ eapply image_monotonic; [| eassumption ];
                                     eauto with Ensembles_DB
                                   | normalize_bound_var; now eauto with Ensembles_DB ]
                                ]]).
          eapply HD'. constructor. now eexists; eauto.
          unfold subst. rewrite Heq. normalize_bound_var. inv Hb.
          now eauto. inv H. right. now eapply H0.
          exfalso. destruct H0 as [v' [Hv' Heq']].
          assert (Heq'': v = v').
          { eapply Hinj; eauto. rewrite Heq'. unfold subst. now rewrite Heq. }
          subst. eapply H5. now apply name_in_fundefs_bound_var_fundefs.
          eapply Disjoint_Included_l. eassumption.
          eapply Union_Disjoint_l. rewrite FromList_cons.
          eapply Union_Disjoint_r; [| eassumption ].
          eapply Disjoint_Singleton_r. intros H. eapply HD with (x := x).
          constructor. eapply Hfx. zify. lia.
          normalize_bound_var...
          rewrite FromList_cons. eapply Union_Disjoint_r.
          eapply Disjoint_Setminus_l...
          eapply Disjoint_Included_l. now apply Setminus_Included.
          eapply Disjoint_Included_r; [| eassumption ].
          normalize_bound_var...
          rewrite FromList_cons.
          eapply Disjoint_Included_l. eassumption.
          apply Union_Disjoint_l.
          apply Union_Disjoint_r; [| eassumption ].
          eapply Disjoint_Included_r with (s6 := S).
          apply Singleton_Included. eapply Hfx. zify; lia.
          eapply Disjoint_Included_l_sym; [| eassumption ].
          normalize_bound_var...
          apply Union_Disjoint_l. apply Union_Disjoint_r.
          rewrite Setminus_Union. eapply Disjoint_Setminus_l...
          eapply Disjoint_Included_l. now apply Setminus_Included.
          eapply Disjoint_Included_l. now apply Setminus_Included.
          eapply Disjoint_Included_r; [| eassumption ].
          normalize_bound_var...
          apply Union_Disjoint_r.
          eapply Disjoint_Included; [| | now apply HD' ].
          apply Included_Union_preserv_r. apply Singleton_Included.
          apply Hfx. zify; lia.
          apply image_monotonic...
          eapply Disjoint_Included; [| | now apply HD' ].
          apply Included_Union_preserv_l.
          normalize_bound_var...
          apply image_monotonic...
          eapply Disjoint_Included_r; [ eassumption  |  ].
          apply Union_Disjoint_r.
          eapply Disjoint_Included_l; [ eassumption  |  ].
          apply Union_Disjoint_l. eassumption.
          eapply Disjoint_Included_l. now apply Setminus_Included.
          eapply Disjoint_Included_r; [| eassumption ].
          normalize_bound_var...
          apply Union_Disjoint_r.
          apply Disjoint_Setminus_r...
          eapply Disjoint_Included_l; [ eassumption  |  ].
          apply Disjoint_sym. eapply Disjoint_Included; [| | now apply HD' ].
          normalize_bound_var...
          apply image_monotonic...
          intros Hc. apply FromList_cons in Hc.
          destruct (Maps.PTree.get v FVmap) as [v' |] eqn:Heq; try destruct v';
          try (inv Hc; [ inv H; eapply HD with (x := v);
                         constructor; [ eapply Hfx; zify; lia | now eauto ]
                       | now eauto ]).
          inv Hc.
          inv H. eapply HD'. constructor. now eexists; eauto.
          unfold subst. rewrite Heq. right. eapply Hfx. zify; lia.
          eapply HD'. constructor. now eexists; eauto.
          unfold subst. rewrite Heq. now left; eauto.
          constructor; eauto. intros Hinl.
          eapply HD with (x := x). constructor. eapply Hfx. zify; lia.
          left. normalize_bound_var...
        * split. normalize_bound_var.
          apply Union_Disjoint_r. apply Disjoint_Singleton_r.
          intros Hc.
          destruct (Maps.PTree.get v FVmap) as [v' |] eqn:Heq; try destruct v';
          try (eapply HD'; constructor;
               [ now eexists; eauto | now unfold subst; rewrite Heq; eauto ]).
          inv Hc. inv H. eapply HD'. constructor. now eexists; eauto.
          unfold subst; rewrite Heq; eauto.
          eapply HD' with (x := v0). constructor. eexists; eauto. split.
          now left; eauto. unfold subst; rewrite Heq; now eauto.
          normalize_bound_var. left. do 3 right. now apply name_in_fundefs_bound_var_fundefs.
          apply Union_Disjoint_r. rewrite FromList_cons. apply Union_Disjoint_l.
          apply Union_Disjoint_r. apply Disjoint_Singleton_r. intros Hc; inv Hc.
          eapply HD. constructor; [| now eauto ]. eapply Hfx; zify; lia.
          now eauto with Ensembles_DB.
          eapply Disjoint_Included_l. now apply name_in_fundefs_bound_var_fundefs.
          apply Union_Disjoint_r. apply Disjoint_Singleton_r. intros Hc.
          eapply HD. constructor; [| now eauto ]. apply Hfx; zify; lia.
          eassumption.
          apply Union_Disjoint_r.
          eapply Disjoint_Included_r. eassumption.
          apply Union_Disjoint_r. apply Union_Disjoint_l.
          now apply Disjoint_Singleton_l.
          eapply Disjoint_Included_l_sym. now apply name_in_fundefs_bound_var_fundefs.
          eassumption.
          apply Union_Disjoint_l. apply Disjoint_Singleton_l.
          intros Hc. eapply HD. constructor; [| now eauto ].
          eapply Setminus_Included. eassumption.
          eapply Disjoint_Included_l_sym. now apply name_in_fundefs_bound_var_fundefs.
          eapply Disjoint_Included_l. now apply Setminus_Included.
          repeat normalize_bound_var_in_ctx...
          apply Union_Disjoint_l; [| eassumption ].
          eapply Disjoint_Included_r. eassumption.
          apply Union_Disjoint_r. now apply Disjoint_Singleton_l.
          apply Union_Disjoint_r. do 2 apply Setminus_Disjoint_preserv_r.
          repeat normalize_bound_var_in_ctx...
          eapply Disjoint_Included_r. apply image_monotonic.
          apply Included_Union_r.
          repeat normalize_bound_var_in_ctx...
          eapply fresh_monotonic; [| eassumption ].
          normalize_bound_var. rewrite !Setminus_Union, FromList_cons.
          rewrite (Union_commut _ (FromList _)), <- !Union_assoc.
          rewrite (Union_assoc (Singleton _ _) (FromList _)), (Union_commut (Union _ (Singleton _ _) (FromList _))).
          rewrite <- (Setminus_Union _ _ (Union _ (Singleton _ _) (FromList _))).
          rewrite <- (Included_Setminus_Disjoint _ (Union _ (Singleton _ _) (FromList _))).
          reflexivity.
          eapply Disjoint_Included_l. now apply Setminus_Included.
          apply Union_Disjoint_r.
          apply Disjoint_Singleton_r. intros Hc.
          destruct (Maps.PTree.get v FVmap) as [v' |] eqn:Heq; try destruct v';
          now (eapply HD'; constructor;
               [ now eexists; eauto | now unfold subst; rewrite Heq; eauto ]).
          repeat normalize_bound_var_in_ctx...
    - apply return_triple. intros s2 Hf. split. now constructor.
      split. now eauto with Ensembles_DB. normalize_bound_var.
      rewrite Setminus_Empty_set_neut_r. eassumption.
  Qed.

  (** Correctness of [exp_closure_conv] and invariant preservation *)
  Corollary exp_closure_conv_correct_inv k rho rho' S e c Γ FVmap Scope :
    (* [Scope], [Funs] and [FVs] are uniquely identified by [FVmap] *)
    FVmap_inv FVmap Scope (Empty_set _) [] ->
    (* [Γ] (the current environment parameter) is fresh in e *)
    ~ In _ (Union _ (bound_var e) (occurs_free e)) Γ ->
    (* The free variables of e are defined in the environment *)
    binding_in_map (occurs_free e) rho ->
    (* [FVmap] contains all the free variables *)
    binding_in_map (occurs_free e) FVmap ->
    (* [e] has unique bindings *)
    unique_bindings e ->
    (* [FVmap] does not contain the variables in [S] or [Γ] *)
    binding_not_in_map (Union _ S (Singleton _ Γ)) FVmap ->
    (* [Scope] invariant *)
    cc_approx_env_P pr cenv clo_tag Scope k boundG rho rho' ->
    (* [S] is disjoint with the free and bound variables of [e] and [Γ] *)
    Disjoint _ S  (Union _ (bound_var e)
                         (Union _ (occurs_free e) (Singleton _ Γ))) ->
    {{ fun s => fresh S (next_var s) }}
      exp_closure_conv clo_tag e FVmap c Γ
    {{ fun s ef s' =>
         cc_approx_exp pr cenv clo_tag k (boundL k e rho) boundG (e, rho) ((snd ef) (fst ef), rho') /\
         Included _ (occurs_free ((snd ef) (fst ef))) (occurs_free e) /\
         unique_bindings ((snd ef) (fst ef)) /\
         closed_fundefs_in_exp ((snd ef) (fst ef)) /\
         Included _ (bound_var ((snd ef) (fst ef)))
                  (Union _ (bound_var e) S)
    }}.
  Proof with now eauto with Ensembles_DB.
    intros IFVmap HGamma Hin_map_rho Hin_map_FVmap Hun
           Hnot_in_map Hcc HD.
    eapply post_conj; [| eapply post_conj; [| eapply post_conj; [| eapply post_conj ]]].
    - eapply post_weakening; [| eapply exp_closure_conv_Closure_conv_sound; try eassumption ].
      intros s [e' f] s' Hf [C [Hctx [Hclo _]]]. simpl in Hctx, Hclo.
      simpl. replace (f e') with (C |[ e' ]|); [| now eauto].
      eapply Closure_conversion_correct; try eassumption.
      intros Hc. eapply HGamma; eauto.
      intros B Hin. eapply unique_bindings_fundefs_unique_functions.
      eapply unique_bindings_funs_in_exp. eassumption. eassumption.
      now apply injective_subdomain_Empty_set.
      rewrite Setminus_Empty_set_abs_r, image_Empty_set...
      intros f' v Hnin Hin. now inv Hin.
      intros x N v Hnin Hin Hnth. eapply nthN_In in Hnth. now inv Hnth.
      rewrite Setminus_Empty_set_abs_r, image_Empty_set, Union_Empty_set_neut_l.
      now eauto with Ensembles_DB.
    - eapply post_weakening; [| eapply exp_closure_conv_occurs_free_Included; try eassumption ].
      now simpl; intros s [x f] s' _ [Hin _]; eauto.
      now eauto with Ensembles_DB.
      intros B Hin. eapply unique_bindings_fundefs_unique_functions.
      eapply unique_bindings_funs_in_exp. eassumption. eassumption.
    - eapply post_weakening; [| eapply exp_closure_conv_unique_bindings_mut; try eassumption ].
      now simpl; intros s [x f] s' _ [Hin _]; eauto.
      now eauto with Ensembles_DB.
    - eapply post_weakening; [| eapply exp_closure_conv_closed_fundefs; try eassumption ].
      now simpl; eauto.
      now eauto with Ensembles_DB.
      intros B Hin. eapply unique_bindings_fundefs_unique_functions.
      eapply unique_bindings_funs_in_exp. eassumption. eassumption.
    - eapply post_weakening; [| eapply exp_closure_conv_bound_var_Included_mut; try eassumption ].
      now simpl; eauto.
      now eauto with Ensembles_DB.
  Qed.

  Lemma populate_map_FVmap_inv l map Scope Funs FVs:
    FVmap_inv map Scope Funs FVs ->
    FVmap_inv (populate_map l map) (Union _ (FromList (List.map fst l)) Scope) Funs FVs.
  Proof.
    unfold populate_map. revert Scope map. induction l as [| [x v] l IHl ]; intros Scope map Hinv.
    - simpl. rewrite FromList_nil, Union_Empty_set_neut_l. eassumption.
    - simpl in *. rewrite FromList_cons, (Union_commut (Singleton _ _) _), <- Union_assoc.
      eapply IHl. apply FVmap_inv_set_bound. eassumption.
  Qed.

  Lemma populate_map_binding_in_map S l map :
    binding_in_map S map ->
    binding_in_map (Union _ (FromList (List.map fst l)) S) (populate_map l map).
  Proof.
    revert S map. induction l; intros S map Hin.
    - simpl. intros x Hc.
      rewrite FromList_nil, Union_Empty_set_neut_l in Hc.
      now eauto.
    - simpl. intros x Hc.
      rewrite FromList_cons, (Union_commut (Singleton _ _) _), <- Union_assoc in Hc.
      eapply IHl; [| eassumption ].
      intros x' Hc'. eapply binding_in_map_set. eassumption.
      inv Hc'; eauto.
  Qed.

  Lemma populate_map_binding_not_in_map S l map :
    binding_not_in_map S map ->
    Disjoint _ S (FromList (List.map fst l)) ->
    binding_not_in_map S (populate_map l map).
  Proof.
    revert S map. induction l; intros S map Hnin HD.
    - simpl. intros x Hc. eapply Hnin. eassumption.
    - simpl in *. intros x Hc.
      eapply IHl. eapply binding_not_in_map_set_not_In_S. eassumption.
      intros Hc'. eapply HD. constructor. eassumption.
      rewrite FromList_cons. now eauto.
      rewrite FromList_cons in HD. now eauto with Ensembles_DB.
      eassumption.
  Qed.
 *)

End CC_correct.
