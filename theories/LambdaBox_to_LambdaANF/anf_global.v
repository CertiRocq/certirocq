(* Correctness of the global environment let-binding step.
   Proves that [convert_global_decls] produces a binding context [C_env]
   that, when composed around the main expression, establishes the
   [global_env_rel'] required by [anf_cvt_correct]. *)

(** Stdlib *)
From Stdlib Require Import ZArith.ZArith Lists.List micromega.Lia Arith
     Ensembles Relations.Relation_Definitions.

(** MetaRocq *)
From MetaRocq.Erasure Require Import
  EAst EAstUtils EGlobalEnv EWellformed EPrimitive EExtends EProgram
  ErasureFunction.
From MetaRocq.Common Require Import BasicAst Kernames.

(** CompCert *)
From compcert Require Import lib.Maps lib.Coqlib.

(** CertiRocq *)
From CertiRocq.Common Require Import AstCommon.
From CertiRocq Require Import Pipeline_utils.
From CertiRocq.LambdaANF Require Import
  cps cps_show eval ctx logical_relations
  List_util algebra alpha_conv functions Ensembles_util
  tactics identifiers bounds cps_util rename set_util stemctx.
From MetaRocq.Utils Require Import All_Forall.
From CertiRocq.LambdaBox_to_LambdaANF Require Import
  common ANF fuel_sem wf anf_corresp anf_util anf_correct.

Import ListNotations.


(* ================================================================= *)
(** * Weakening anf_val_rel: from full cmap/Σ to partial cm/Σ_tail    *)
(* ================================================================= *)

Section ValRelWeaken.

  Context (func_tag default_tag : positive)
          (tgm : conId_map).

  Context {efl : EEnvFlags}.

  Context (box_dc : dcon)
          (box_tag : dcon_to_tag default_tag box_dc tgm = default_tag).

  Let Hf_src := LambdaBox_resource_fuel default_tag tgm box_dc box_tag.
  Let Ht_src := LambdaBox_resource_trace default_tag tgm box_dc box_tag.

  (** Full (source) parameters *)
  Context (cmap_full : const_map) (Σ_full : EAst.global_context).

  (** Partial (target) parameters *)
  Context (cm : const_map) (Σ_tail : EAst.global_context).

  (** Relationship between full and partial *)
  Context (Hwf_tail : EWellformed.wf_glob Σ_tail).
  Context (Hext : EGlobalEnv.extends Σ_tail Σ_full).
  Context (Hcm_sub : forall s v, lookup_const cm s = Some v ->
                                  lookup_const cmap_full s = Some v).
  Context (Hcm_agree : forall s v, lookup_const cmap_full s = Some v ->
                                    lookup_const cm s <> None ->
                                    lookup_const cm s = Some v).
  Context (Hcm_complete : forall s d,
    EGlobalEnv.declared_constant Σ_tail s d -> lookup_const cm s <> None).
  Context (Hcm_sound : forall k v, lookup_const cm k = Some v ->
    exists decl, EGlobalEnv.declared_constant Σ_tail k decl).

  Let anf_val_rel_full :=
    @anf_val_rel func_tag default_tag tgm cmap_full nat Hf_src Ht_src Σ_full box_dc.
  Let anf_val_rel_part :=
    @anf_val_rel func_tag default_tag tgm cm nat Hf_src Ht_src Σ_tail box_dc.

  (* Helper: transfer Forall2 using pointwise IH + a generic side condition Q *)
  Lemma forall2_val_rel_weaken (Q : fuel_sem.value -> Prop) vs :
    Forall (fun v => Q v ->
                     forall v', anf_val_rel_full v v' -> anf_val_rel_part v v') vs ->
    forall vs',
    Forall2 (fun v v' => anf_val_rel_full v v') vs vs' ->
    Forall Q vs ->
    Forall2 (fun v v' => anf_val_rel_part v v') vs vs'.
  Proof.
    induction 1 as [| v0 vs0 IHv0 _ IHvs]; intros vs' Hf2 Hwf_vs.
    - inversion Hf2. constructor.
    - inversion Hf2 as [| ? ? ? ? Hrel0 Hf2']. subst.
      inversion Hwf_vs as [| ? ? Hwf0 Hwf_rest]. subst.
      constructor; [exact (IHv0 Hwf0 _ Hrel0) | exact (IHvs _ Hf2' Hwf_rest)].
  Qed.

  (* Helper: transfer anf_env_rel' using pointwise IH + a generic side condition Q *)
  Lemma env_rel_val_rel_weaken (Q : fuel_sem.value -> Prop) vs :
    Forall (fun v => Q v ->
                     forall v', anf_val_rel_full v v' -> anf_val_rel_part v v') vs ->
    forall names rho,
    anf_env_rel' anf_val_rel_full names vs rho ->
    Forall Q vs ->
    anf_env_rel' anf_val_rel_part names vs rho.
  Proof.
    unfold anf_env_rel' in *.
    induction 1 as [| v0 vs0 IHv0 _ IHvs]; intros names rho Henv Hwf_vs.
    - inversion Henv. constructor.
    - destruct names as [| n0 ns0]; [inversion Henv |].
      inversion Henv as [| ? ? ? ? [anf_v0 [Hget0 Hrel0]] Henv']. subst.
      inversion Hwf_vs as [| ? ? Hwf0 Hwf_rest]. subst.
      constructor.
      + exists anf_v0. split; [exact Hget0 | exact (IHv0 Hwf0 _ Hrel0)].
      + exact (IHvs _ _ Henv' Hwf_rest).
  Qed.

  (* Helper: weaken cmap_consistent from (cmap_full, Σ_full) to (cm, Σ_tail) *)
  Lemma cmap_consistent_weaken names vs :
    @cmap_consistent cmap_full _ Hf_src Ht_src Σ_full box_dc names vs ->
    @cmap_consistent cm _ Hf_src Ht_src Σ_tail box_dc names vs.
  Proof.
    intros Hcm_c i x k decl body Hnth Hlk Hdecl Hbody.
    (* Bridge lookups: cm → cmap_full, Σ_tail → Σ_full *)
    pose proof (Hcm_sub _ _ Hlk) as Hlk_full.
    pose proof (Hext _ _ Hdecl) as Hdecl_full.
    destruct (Hcm_c i x k decl body Hnth Hlk_full Hdecl_full Hbody)
      as [v_i [f0 [t0 [Hnth_rho Heval_full]]]].
    exists v_i, f0, t0. split; [exact Hnth_rho |].
    (* Restrict eval from Σ_full to Σ_tail *)
    assert (Hwf_body : wellformed Σ_tail 0 body = true).
    { exact (wf_glob_globals_wf Σ_tail Hwf_tail _ _ _ Hdecl Hbody). }
    exact (proj1 (@eval_env_fuel_restrict _ _ Hf_src Ht_src Σ_full box_dc Σ_tail
                    [] body (fuel_sem.Val v_i) f0 t0 Hwf_tail Hext
                    ltac:(constructor) Hwf_body Heval_full)).
  Qed.

  (* Helper: weaken anf_cvt_rel from cmap_full to cm.
     Requires that all constants in e are in domain(cm). *)
  Lemma anf_cvt_rel_cmap_weaken :
    forall S e vn S' C x,
      anf_cvt_rel func_tag default_tag tgm cmap_full S e vn S' C x ->
      wellformed Σ_tail (List.length vn) e = true ->
      anf_cvt_rel func_tag default_tag tgm cm S e vn S' C x.
  Proof.
    intros S e vn S' C x Hcvt.
    revert Hcvt.
    apply (@anf_cvt_rel_ind' func_tag default_tag tgm cmap_full
      (fun S e vn S' C x =>
        wellformed Σ_tail (List.length vn) e = true ->
        anf_cvt_rel func_tag default_tag tgm cm S e vn S' C x)
      (fun S es vn S' C xs =>
        Forall (fun e0 => wellformed Σ_tail (List.length vn) e0 = true) es ->
        anf_cvt_rel_args func_tag default_tag tgm cm S es vn S' C xs)
      (fun Sset mfix vn fnames S' fdefs =>
        Forall (fun d => wellformed Σ_tail (List.length vn) (EAst.dbody d) = true) mfix ->
        anf_cvt_rel_mfix func_tag default_tag tgm cm Sset mfix vn fnames S' fdefs)
      (fun S ind brs n vn r S' pats =>
        Forall (fun br => wellformed Σ_tail (List.length vn + List.length (fst br))
                                            (snd br) = true) brs ->
        anf_cvt_rel_branches func_tag default_tag tgm cm S ind brs n vn r S' pats)).
    - (* anf_Rel *) intros S0 v0 vn0 n Hnth Hwf.
      apply (@anf_Rel func_tag default_tag tgm cm). exact Hnth.
    - (* anf_Lam *) intros S0 Send na e1 C1 r1 x1 f vn0 Hx1 Hf Hcvt IH Hwf.
      apply (@anf_Lam func_tag default_tag tgm cm) with (S := S0) (S' := Send); try assumption.
      apply IH. apply (wellformed_tLambda Σ_tail) in Hwf. exact Hwf.
    - (* anf_App *) intros S1 S2 S3 u C1 x1 v0 C2 x2 r vn0 Hcvt1 IH1 Hcvt2 IH2 Hr Hwf.
      apply (wellformed_tApp Σ_tail) in Hwf as [Hwf1 Hwf2].
      eapply (@anf_App func_tag default_tag tgm cm); eauto.
    - (* anf_Construct *) intros S1 S2 c_tag ind c args0 Cargs xs x0 vn0 Htag Hx Hcvt IH Hwf.
      apply (wellformed_tConstruct Σ_tail) in Hwf.
      eapply (@anf_Construct func_tag default_tag tgm cm); eauto.
    - (* anf_LetIn *) intros S1 S2 S3 na b t C1 x1 C2 x2 vn0 Hcvt1 IH1 Hcvt2 IH2 Hwf.
      apply (wellformed_tLetIn Σ_tail) in Hwf as [Hwfb Hwft].
      eapply (@anf_LetIn func_tag default_tag tgm cm); eauto.
    - (* anf_Case *) intros S1 S2 S3 ind npars mch C1 x1 brs pats f y r vn0
                            Hf Hy Hcvt_mch IH_mch Hcvt_brs IH_brs Hr Hwf.
      pose proof (wellformed_tCase_mch Σ_tail _ _ _ _ _ Hwf) as Hwf_mch.
      eapply (@anf_Case func_tag default_tag tgm cm); eauto.
      apply IH_brs.
      (* Decompose wellformed_tCase to get branches Forall *)
      simpl in Hwf. apply andb_true_iff in Hwf as [_ Hwf'].
      apply andb_true_iff in Hwf' as [_ Hwf_brs'].
      apply Forall_forall. intros [bnames bbody] Hb_in.
      rewrite forallb_forall in Hwf_brs'.
      pose proof (Hwf_brs' _ Hb_in) as Hwf_b. simpl in Hwf_b.
      simpl. rewrite Nat.add_comm. exact Hwf_b.
    - (* anf_Fix *) intros S1 S2 mfix idx f fnames vn0 fdefs Hsub Hnd Hlen Hcvt_mfix IH_mfix Hnth Hwf.
      apply (wellformed_tFix Σ_tail) in Hwf as [Hidx Hwf_mfix].
      eapply (@anf_Fix func_tag default_tag tgm cm); eauto.
      apply IH_mfix.
      apply Forall_forall. intros d Hd_in.
      rewrite Forall_forall in Hwf_mfix. specialize (Hwf_mfix d Hd_in).
      destruct Hwf_mfix as [_ Hwf_d].
      rewrite length_app, length_rev, Hlen. exact Hwf_d.
    - (* anf_Box *) intros S0 vn0 x0 Hx Hwf.
      apply (@anf_Box func_tag default_tag tgm cm). exact Hx.
    - (* anf_Const *) intros S0 vn0 s v0 Hlk Hwf.
      apply (@anf_Const func_tag default_tag tgm cm).
      destruct (wellformed_tConst_lookup Σ_tail _ _ Hwf) as [d Hlk_d].
      unfold lookup_constant in Hlk_d.
      destruct (lookup_env Σ_tail s) as [gd|] eqn:He; [| discriminate].
      destruct gd as [cb | ind]; [| discriminate].
      simpl in Hlk_d. injection Hlk_d as <-.
      apply Hcm_agree; [assumption |]. eapply Hcm_complete. exact He.
    - (* anf_Proj *) intros S1 S2 p c0 C0 x0 y vn0 c_tag Htag Hcvt IH Hy Hwf.
      apply (wellformed_tProj Σ_tail) in Hwf.
      eapply (@anf_Proj func_tag default_tag tgm cm); eauto.
    - (* anf_Prim *) intros S0 vn0 p pv x0 Htrans Hx Hwf.
      apply (@anf_Prim func_tag default_tag tgm cm); assumption.
    - (* anf_Args_nil *) intros S0 vn0 _.
      apply (@anf_Args_nil func_tag default_tag tgm cm).
    - (* anf_Args_cons *) intros S1 S2 S3 vn0 t ts C1 x1 C2 xs Hcvt IH Hcvt_args IH_args Hwf_all.
      inversion Hwf_all as [| ? ? Hwf_t Hwf_ts]. subst.
      eapply (@anf_Args_cons func_tag default_tag tgm cm); eauto.
    - (* anf_Mfix_nil *) intros S0 vn0 _.
      apply (@anf_Mfix_nil func_tag default_tag tgm cm).
    - (* anf_Mfix_cons *) intros S1 S2 S3 vn0 fnames d mfix' C1 r1 fdefs na e1 x1 f_name
                                 Hbody Hx1 Hcvt IH Hcvt_mfix IH_mfix Hwf_all.
      inversion Hwf_all as [| ? ? Hwf_d Hwf_rest]. subst.
      eapply (@anf_Mfix_cons func_tag default_tag tgm cm).
      * exact Hbody.
      * exact Hx1.
      * apply IH. rewrite Hbody in Hwf_d.
        apply (wellformed_tLambda Σ_tail) in Hwf_d.
        simpl. exact Hwf_d.
      * apply IH_mfix. exact Hwf_rest.
    - (* anf_Branches_nil *) intros S0 ind vn0 r n _.
      apply (@anf_Branches_nil func_tag default_tag tgm cm).
    - (* anf_Branches_cons *) intros S1 S2 S3 ind vn0 r lnames eb brs' pats' C1 r1 vars
                                       ctx_p tg n Htag Hcvt_brs IH_brs Hsub Hnd Hlen Hctx Hcvt IH Hwf_all.
      inversion Hwf_all as [| ? ? Hwf_e Hwf_rest]. subst.
      eapply (@anf_Branches_cons func_tag default_tag tgm cm); eauto.
      apply IH.
      rewrite length_app. rewrite Hlen. rewrite Nat.add_comm. exact Hwf_e.
  Qed.

  (* Helper: weaken anf_fix_rel from cmap_full to cm.
     Only the recursive anf_cvt_rel' calls touch cmap. *)
  Lemma anf_fix_rel_cmap_weaken :
    forall fnames names S1 fnames' mfix B S3,
      anf_fix_rel func_tag default_tag tgm cmap_full
                   fnames names S1 fnames' mfix B S3 ->
      Forall (fun d => wellformed Σ_tail
                         (List.length (List.rev fnames ++ names))
                         (EAst.dbody d) = true) mfix ->
      anf_fix_rel func_tag default_tag tgm cm
                   fnames names S1 fnames' mfix B S3.
  Proof.
    intros fnames names S1 fnames' mfix B S3 Hfix.
    induction Hfix; intro Hwf_all.
    - constructor.
    - inversion Hwf_all as [| ? ? Hwf_d Hwf_rest]. subst.
      eapply (@anf_fix_fcons func_tag default_tag tgm cm); try eassumption.
      + (* anf_cvt_rel for body *)
        eapply anf_cvt_rel_cmap_weaken; [eassumption |].
        rewrite H in Hwf_d.
        apply (wellformed_tLambda Σ_tail) in Hwf_d.
        simpl. exact Hwf_d.
      + apply IHHfix. exact Hwf_rest.
  Qed.


  (** Strengthened weakening: well-formedness can be in any sub-context
      [Σ0 ⊆ Σ_tail]. The proof inducts on [wf_glob Σ0] (outer) and on the
      value structure (inner). The outer wf_glob induction is what makes
      the global_env_rel' case work: when destructuring the global env's
      stored value [src_v], we obtain [well_formed_val Σ' src_v] by
      [eval_preserves_wf_restricted] applied at the smaller [Σ'], which
      lets us invoke the outer IH. *)
  Lemma anf_val_rel_weaken_gen :
    forall Σ0 (Hwf0 : EWellformed.wf_glob Σ0)
           (Hext0 : EGlobalEnv.extends Σ0 Σ_tail),
    forall v, well_formed_val Σ0 v ->
    forall v', anf_val_rel_full v v' ->
    anf_val_rel_part v v'.
  Proof.
    intros Σ0 Hwf0.
    induction Hwf0 as [| kn d Σ' Hwf' IH Hwfd Hfresh].

    (* ============ BASE: Σ0 = [] ============ *)
    - intros Hext0 v.
      induction v using fuel_sem.value_ind';
        intros Hwf v' Hrel.
      + (* Con_v *)
        inversion Hwf as [? ? Hwf_vs| |]; subst.
        inversion Hrel; subst.
        apply (@anf_rel_Con func_tag default_tag tgm cm _ Hf_src Ht_src Σ_tail box_dc);
          [| reflexivity].
        eapply (forall2_val_rel_weaken (well_formed_val [])); eassumption.
      + (* Clos_v *)
        inversion Hwf as [|? ? ? Hwf_vs Hwf_body|]; subst.
        inversion Hrel; subst.
        eapply (@anf_rel_Clos func_tag default_tag tgm cm _ Hf_src Ht_src Σ_tail box_dc);
          try eassumption.
        * (* anf_env_rel' *)
          eapply (env_rel_val_rel_weaken (well_formed_val []));
            [exact H | eassumption | exact Hwf_vs].
        * eapply cmap_consistent_weaken. eassumption.
        * (* Disjoint (cmap_vars cm) S1 *)
          eapply Disjoint_Included_l; [| eassumption].
          intros z [s Hlk]. exists s. exact (Hcm_sub s z Hlk).
        * intro Hc. match goal with H : ~ ?y \in cmap_vars cmap_full |- _ =>
            apply H; destruct Hc as [s Hlk]; exists s; exact (Hcm_sub s y Hlk) end.
        * intro Hc. match goal with H : ~ ?y \in cmap_vars cmap_full |- _ =>
            apply H; destruct Hc as [s Hlk]; exists s; exact (Hcm_sub s y Hlk) end.
        * (* anf_cvt_rel[cm] — bridge wellformed [] → wellformed Σ_tail *)
          eapply anf_cvt_rel_cmap_weaken; [eassumption |].
          assert (Hlen : Datatypes.length vs = Datatypes.length names).
          { match goal with He : anf_env_rel' _ _ _ _ |- _ =>
              unfold anf_env_rel' in He; eapply Forall2_length; exact He end. }
          replace (Datatypes.length (x :: names)) with (Datatypes.S (Datatypes.length vs))
            by (simpl; rewrite Hlen; reflexivity).
          eapply EWellformed.extends_wellformed; [exact Hwf_tail | exact Hext0 | exact Hwf_body].
        * (* global_env_rel' part — vacuous since kn_deps must be empty *)
          intros k v_g Hkdep _.
          exfalso.
          exact (kn_deps_declared [] _ e k Hwf_body Hkdep).
      + (* ClosFix_v *)
        inversion Hwf as [| |? ? ? Hwf_vs Hidx Hwf_mfix]; subst.
        inversion Hrel; subst.
        eapply (@anf_rel_ClosFix func_tag default_tag tgm cm _ Hf_src Ht_src Σ_tail box_dc);
          try eassumption.
        * eapply (env_rel_val_rel_weaken (well_formed_val []));
            [exact H | eassumption | exact Hwf_vs].
        * eapply cmap_consistent_weaken. eassumption.
        * eapply Disjoint_Included_l; [| eassumption].
          intros z [s Hlk]. exists s. exact (Hcm_sub s z Hlk).
        * match goal with H : Disjoint _ (cmap_vars cmap_full) (FromList fnames) |- _ =>
            eapply Disjoint_Included_l; [| exact H] end.
          intros z [s Hlk]. exists s. exact (Hcm_sub s z Hlk).
        * (* anf_fix_rel cm version *)
          eapply anf_fix_rel_cmap_weaken; [eassumption |].
          (* Length arithmetic + extends_wellformed *)
          assert (Hlen_n : Datatypes.length vs = Datatypes.length names).
          { match goal with He : anf_env_rel' _ _ _ _ |- _ =>
              unfold anf_env_rel' in He; eapply Forall2_length; exact He end. }
          assert (Hlen_f : Datatypes.length fnames = Datatypes.length mfix).
          { eapply anf_fix_rel_fnames_length. eassumption. }
          eapply Forall_impl; [exact Hwf_mfix |].
          intros d0 [Hlam Hwf_d]. simpl.
          rewrite length_app, length_rev, Hlen_f, <- Hlen_n.
          eapply EWellformed.extends_wellformed; [exact Hwf_tail | exact Hext0 | exact Hwf_d].
        * (* global_env_rel' part — vacuous: all bodies have empty kn_deps *)
          intros k v_g Hkdep _.
          exfalso.
          unfold kn_deps_mfix in Hkdep.
          apply Exists_exists in Hkdep.
          destruct Hkdep as [d0 [Hd0_in Hk_dep]].
          eapply Forall_forall in Hwf_mfix; [| exact Hd0_in].
          destruct Hwf_mfix as [_ Hwf_d].
          exact (kn_deps_declared [] _ _ _ Hwf_d Hk_dep).

    (* ============ STEP: Σ0 = (kn, d) :: Σ' ============ *)
    - intros Hext0.
      assert (Hext' : EGlobalEnv.extends Σ' Σ_tail).
      { intros k' d' Hlk. apply Hext0. simpl.
        destruct (ReflectEq.eqb k' kn) eqn:Heq; [| exact Hlk].
        apply ReflectEq.eqb_eq in Heq. subst k'.
        exfalso. exact (EGlobalEnv.lookup_env_Some_fresh Hlk Hfresh). }
      specialize (IH Hext').
      assert (Hext_full : EGlobalEnv.extends Σ' Σ_full).
      { intros ? ? Hlk. apply Hext. apply Hext'. exact Hlk. }
      intro v.
      induction v using fuel_sem.value_ind';
        intros Hwf v' Hrel.
      + (* Con_v *)
        inversion Hwf as [? ? Hwf_vs| |]; subst.
        inversion Hrel; subst.
        apply (@anf_rel_Con func_tag default_tag tgm cm _ Hf_src Ht_src Σ_tail box_dc);
          [| reflexivity].
        eapply (forall2_val_rel_weaken (well_formed_val ((kn, d) :: Σ'))); eassumption.
      + (* Clos_v *)
        inversion Hwf as [|? ? ? Hwf_vs Hwf_body|]; subst.
        inversion Hrel; subst.
        eapply (@anf_rel_Clos func_tag default_tag tgm cm _ Hf_src Ht_src Σ_tail box_dc);
          try eassumption.
        * eapply (env_rel_val_rel_weaken (well_formed_val ((kn, d) :: Σ')));
            [exact H | eassumption | exact Hwf_vs].
        * eapply cmap_consistent_weaken. eassumption.
        * eapply Disjoint_Included_l; [| eassumption].
          intros z [s Hlk]. exists s. exact (Hcm_sub s z Hlk).
        * intro Hc. match goal with H : ~ ?y \in cmap_vars cmap_full |- _ =>
            apply H; destruct Hc as [s Hlk]; exists s; exact (Hcm_sub s y Hlk) end.
        * intro Hc. match goal with H : ~ ?y \in cmap_vars cmap_full |- _ =>
            apply H; destruct Hc as [s Hlk]; exists s; exact (Hcm_sub s y Hlk) end.
        * (* anf_cvt_rel[cm] *)
          eapply anf_cvt_rel_cmap_weaken; [eassumption |].
          assert (Hlen : Datatypes.length vs = Datatypes.length names).
          { match goal with He : anf_env_rel' _ _ _ _ |- _ =>
              unfold anf_env_rel' in He; eapply Forall2_length; exact He end. }
          replace (Datatypes.length (x :: names)) with (Datatypes.S (Datatypes.length vs))
            by (simpl; rewrite Hlen; reflexivity).
          eapply EWellformed.extends_wellformed; [exact Hwf_tail | exact Hext0 | exact Hwf_body].
        * (* global_env_rel' part — use OUTER IH *)
          match goal with H : global_env_rel' _ _ _ _ _ _ |- _ =>
            rename H into Hglob end.
          intros k v_g Hkdep Hlk_cm.
          pose proof (Hcm_sub _ _ Hlk_cm) as Hlk_full.
          destruct (Hglob k v_g Hkdep Hlk_full)
            as [decl [body [anf_v [Hdecl_full [Hbody [Hget Hrel_glob]]]]]].
          (* Bridge: declared_constant Σ_full → declared_constant Σ_tail *)
          (* k is declared in Σ0 (by kn_deps_declared), so in Σ_tail by Hext0 *)
          assert (Hlk0_some : exists gd, EGlobalEnv.lookup_env ((kn, d) :: Σ') k = Some gd).
          { pose proof (kn_deps_declared _ _ e k Hwf_body Hkdep) as Hin.
            simpl in Hin |- *.
            destruct (ReflectEq.eqb k kn) eqn:Hkkn; [exists d; reflexivity |].
            assert (Hin' : List.In k (map fst Σ')).
            { destruct Hin as [Heq | Hin']; [| exact Hin'].
              subst kn. rewrite ReflectEq.eqb_refl in Hkkn. discriminate. }
            clear Hin Hkkn.
            (* Find lookup in Σ' *)
            assert (Haux : forall l, List.In k (map fst l) ->
                                      exists gd, EGlobalEnv.lookup_env l k = Some gd).
            { clear. induction l as [| [k' d'] l' IH']; intros Hin0;
                [contradiction |].
              simpl in Hin0 |- *.
              destruct (ReflectEq.eqb k k') eqn:Hkk'; [exists d'; reflexivity |].
              destruct Hin0 as [Heq | Hin0].
              - subst k'. rewrite ReflectEq.eqb_refl in Hkk'. discriminate.
              - exact (IH' Hin0). }
            destruct (Haux _ Hin') as [gd Hgd]. exact (ex_intro _ gd Hgd). }
          destruct Hlk0_some as [gd Hlk_some].
          pose proof (Hext0 _ _ Hlk_some) as Hlk_tail.
          (* gd = ConstantDecl decl by lookup determinism via Hext *)
          pose proof (Hext _ _ Hlk_tail) as Hlk_full'.
          unfold declared_constant in Hdecl_full.
          rewrite Hlk_full' in Hdecl_full. injection Hdecl_full as Hgd_eq.
          subst gd.
          (* Now Hlk_tail : lookup_env Σ_tail k = Some (ConstantDecl decl) *)
          assert (Hdecl_tail : declared_constant Σ_tail k decl)
            by exact Hlk_tail.
          exists decl, body, anf_v.
          split; [exact Hdecl_tail |]. split; [exact Hbody |]. split; [exact Hget |].
          intros src_v f0 t0 Heval_tail.
          (* Lift eval Σ_tail → eval Σ_full *)
          assert (Heval_full : @eval_env_fuel _ Hf_src Ht_src Σ_full box_dc []
                                body (fuel_sem.Val src_v) f0 t0).
          { exact (@eval_env_fuel_extends _ Hf_src Ht_src Σ_full box_dc
                     Σ_tail [] body _ f0 t0 Hext Heval_tail). }
          pose proof (Hrel_glob src_v f0 t0 Heval_full) as Hrel_full.
          (* Establish wellformed Σ' 0 body for use in eval_preserves_wf_restricted *)
          assert (Hwf_body_Σ' : wellformed Σ' 0 body = true).
          { simpl in Hlk_some. destruct (ReflectEq.eqb k kn) eqn:Hkeq.
            - (* k = kn: gd = d *)
              injection Hlk_some as Heq_d. subst d.
              simpl in Hwfd. rewrite Hbody in Hwfd. exact Hwfd.
            - (* k ∈ Σ': use wf_glob_globals_wf for Σ' *)
              eapply (wf_glob_globals_wf Σ' Hwf' k decl body); [| exact Hbody].
              unfold declared_constant. exact Hlk_some. }
          (* Apply eval_preserves_wf_restricted to get well_formed_val Σ' *)
          assert (Hwf_src : well_formed_val Σ' src_v).
          { eapply (@eval_preserves_wf_restricted _ _ Hf_src Ht_src Σ_full box_dc Σ');
              [exact Hwf' | exact Hext_full | constructor | exact Hwf_body_Σ' | exact Heval_full]. }
          (* Apply outer IH *)
          eapply IH; [exact Hwf_src | exact Hrel_full].
      + (* ClosFix_v *)
        inversion Hwf as [| |? ? ? Hwf_vs Hidx Hwf_mfix]; subst.
        inversion Hrel; subst.
        eapply (@anf_rel_ClosFix func_tag default_tag tgm cm _ Hf_src Ht_src Σ_tail box_dc);
          try eassumption.
        * eapply (env_rel_val_rel_weaken (well_formed_val ((kn, d) :: Σ')));
            [exact H | eassumption | exact Hwf_vs].
        * eapply cmap_consistent_weaken. eassumption.
        * eapply Disjoint_Included_l; [| eassumption].
          intros z [s Hlk]. exists s. exact (Hcm_sub s z Hlk).
        * match goal with H : Disjoint _ (cmap_vars cmap_full) (FromList fnames) |- _ =>
            eapply Disjoint_Included_l; [| exact H] end.
          intros z [s Hlk]. exists s. exact (Hcm_sub s z Hlk).
        * (* anf_fix_rel cm version *)
          eapply anf_fix_rel_cmap_weaken; [eassumption |].
          assert (Hlen_n : Datatypes.length vs = Datatypes.length names).
          { match goal with He : anf_env_rel' _ _ _ _ |- _ =>
              unfold anf_env_rel' in He; eapply Forall2_length; exact He end. }
          assert (Hlen_f : Datatypes.length fnames = Datatypes.length mfix).
          { eapply anf_fix_rel_fnames_length. eassumption. }
          eapply Forall_impl; [exact Hwf_mfix |].
          intros d0 [Hlam Hwf_d]. simpl.
          rewrite length_app, length_rev, Hlen_f, <- Hlen_n.
          eapply EWellformed.extends_wellformed; [exact Hwf_tail | exact Hext0 | exact Hwf_d].
        * (* global_env_rel' part — use OUTER IH (same logic as Clos) *)
          match goal with H : global_env_rel' _ _ _ _ _ _ |- _ =>
            rename H into Hglob end.
          intros k v_g Hkdep Hlk_cm.
          pose proof (Hcm_sub _ _ Hlk_cm) as Hlk_full.
          destruct (Hglob k v_g Hkdep Hlk_full)
            as [decl [body [anf_v [Hdecl_full [Hbody [Hget Hrel_glob]]]]]].
          (* k ∈ kn_deps_mfix mfix → k declared in some d0 ∈ mfix *)
          unfold kn_deps_mfix in Hkdep.
          apply Exists_exists in Hkdep.
          destruct Hkdep as [d0 [Hd0_in Hk_dep]].
          assert (Hwf_d0 : wellformed ((kn, d) :: Σ') (List.length mfix + List.length vs)
                                       (EAst.dbody d0) = true).
          { eapply Forall_forall in Hwf_mfix; [| exact Hd0_in].
            destruct Hwf_mfix as [_ Hwf_d]. exact Hwf_d. }
          assert (Hlk0_some : exists gd, EGlobalEnv.lookup_env ((kn, d) :: Σ') k = Some gd).
          { pose proof (kn_deps_declared _ _ _ k Hwf_d0 Hk_dep) as Hin.
            simpl in Hin |- *.
            destruct (ReflectEq.eqb k kn) eqn:Hkkn; [exists d; reflexivity |].
            assert (Hin' : List.In k (map fst Σ')).
            { destruct Hin as [Heq | Hin']; [| exact Hin'].
              subst kn. rewrite ReflectEq.eqb_refl in Hkkn. discriminate. }
            clear Hin Hkkn.
            assert (Haux : forall l, List.In k (map fst l) ->
                                      exists gd, EGlobalEnv.lookup_env l k = Some gd).
            { clear. induction l as [| [k' d'] l' IH']; intros Hin0;
                [contradiction |].
              simpl in Hin0 |- *.
              destruct (ReflectEq.eqb k k') eqn:Hkk'; [exists d'; reflexivity |].
              destruct Hin0 as [Heq | Hin0].
              - subst k'. rewrite ReflectEq.eqb_refl in Hkk'. discriminate.
              - exact (IH' Hin0). }
            destruct (Haux _ Hin') as [gd Hgd]. exact (ex_intro _ gd Hgd). }
          destruct Hlk0_some as [gd Hlk_some].
          pose proof (Hext0 _ _ Hlk_some) as Hlk_tail.
          pose proof (Hext _ _ Hlk_tail) as Hlk_full'.
          unfold declared_constant in Hdecl_full.
          rewrite Hlk_full' in Hdecl_full. injection Hdecl_full as Hgd_eq.
          subst gd.
          assert (Hdecl_tail : declared_constant Σ_tail k decl)
            by exact Hlk_tail.
          exists decl, body, anf_v.
          split; [exact Hdecl_tail |]. split; [exact Hbody |]. split; [exact Hget |].
          intros src_v f0 t0 Heval_tail.
          assert (Heval_full : @eval_env_fuel _ Hf_src Ht_src Σ_full box_dc []
                                body (fuel_sem.Val src_v) f0 t0).
          { exact (@eval_env_fuel_extends _ Hf_src Ht_src Σ_full box_dc
                     Σ_tail [] body _ f0 t0 Hext Heval_tail). }
          pose proof (Hrel_glob src_v f0 t0 Heval_full) as Hrel_full.
          assert (Hwf_body_Σ' : wellformed Σ' 0 body = true).
          { simpl in Hlk_some. destruct (ReflectEq.eqb k kn) eqn:Hkeq.
            - injection Hlk_some as Heq_d. subst d.
              simpl in Hwfd. rewrite Hbody in Hwfd. exact Hwfd.
            - eapply (wf_glob_globals_wf Σ' Hwf' k decl body); [| exact Hbody].
              unfold declared_constant. exact Hlk_some. }
          assert (Hwf_src : well_formed_val Σ' src_v).
          { eapply (@eval_preserves_wf_restricted _ _ Hf_src Ht_src Σ_full box_dc Σ');
              [exact Hwf' | exact Hext_full | constructor | exact Hwf_body_Σ' | exact Heval_full]. }
          eapply IH; [exact Hwf_src | exact Hrel_full].
  Qed.

  (** Weakening: anf_val_rel with bigger cmap/Σ implies anf_val_rel with
      smaller cmap/Σ, given well-formedness of the source value. *)
  Lemma anf_val_rel_weaken :
    forall v,
    well_formed_val Σ_tail v ->
    forall v',
    anf_val_rel_full v v' ->
    anf_val_rel_part v v'.
  Proof.
    intros v Hwf v' Hrel.
    eapply anf_val_rel_weaken_gen with (Σ0 := Σ_tail).
    - exact Hwf_tail.
    - intros ? ? Hlk; exact Hlk.
    - exact Hwf.
    - exact Hrel.
  Qed.

End ValRelWeaken.


(* ================================================================= *)
(** * Operational correctness of global binding contexts *)
(* ================================================================= *)

Section GlobalBindingsCorrect.

  Context (func_tag kon_tag default_tag default_itag : positive)
          (tgm : conId_map)
          (cmap : const_map)
          (cenv : ctor_env)
          (Σ : EAst.global_context).

  Context {efl : EEnvFlags}.
  Context (HnoAxioms : has_axioms = false).

  Context (dcon_to_tag_inj :
    forall dc dc',
      dcon_to_tag default_tag dc tgm = dcon_to_tag default_tag dc' tgm -> dc = dc').

  Context (box_dc : dcon)
          (box_tag : dcon_to_tag default_tag box_dc tgm = default_tag).

  Context (cenv_case_consistent : forall P ctag, caseConsistent cenv P ctag).

  Let Hf_src := LambdaBox_resource_fuel default_tag tgm box_dc box_tag.
  Let Ht_src := LambdaBox_resource_trace default_tag tgm box_dc box_tag.

  Context (Hcmap_eval_coherent :
    @cmap_eval_coherent cmap _ Hf_src Ht_src Σ box_dc).

  Let anf_val_rel' :=
    @anf_val_rel func_tag default_tag tgm cmap nat Hf_src Ht_src Σ box_dc.

  Let anf_cvt_rel' :=
    anf_cvt_rel func_tag default_tag tgm cmap.

  Let global_env_rel' :=
    @global_env_rel func_tag default_tag tgm cmap nat Hf_src Ht_src Σ box_dc.

  Let anf_env_rel' :=
    @anf_env_rel func_tag default_tag tgm cmap nat Hf_src Ht_src Σ box_dc.

  Let src_eval := @eval_env_fuel nat Hf_src Ht_src Σ box_dc.

  (** Per-(cm,Σ') versions of the value, env, and global env relations. *)
  Local Notation val_rel_at cm0 Σ0 :=
    (@anf_val_rel func_tag default_tag tgm cm0 nat Hf_src Ht_src Σ0 box_dc).
  Local Notation env_rel_at cm0 Σ0 :=
    (@anf_env_rel func_tag default_tag tgm cm0 nat Hf_src Ht_src Σ0 box_dc).
  Local Notation glob_rel_at cm0 Σ0 :=
    (@global_env_rel func_tag default_tag tgm cm0 nat Hf_src Ht_src Σ0 box_dc).
  Local Notation cvt_rel_at cm0 :=
    (@anf_cvt_rel func_tag default_tag tgm cm0).
  Local Notation eval_at Σ0 :=
    (@eval_env_fuel nat Hf_src Ht_src Σ0 box_dc).

  Context (Hglob_term :
    forall k decl body,
      declared_constant Σ k decl ->
      decl.(EAst.cst_body) = Some body ->
      exists src_v f t, src_eval [] body (Val src_v) f t).
  Context (Hglob_fuel_zero :
    forall k decl body src_v f t,
      declared_constant Σ k decl ->
      decl.(EAst.cst_body) = Some body ->
      src_eval [] body (Val src_v) f t ->
      f = 0).

  Context (Hglob_wf :
    forall k decl body,
      declared_constant Σ k decl ->
      decl.(EAst.cst_body) = Some body ->
      wellformed Σ 0 body = true).

  (* Hypotheses for anf_val_rel_exists *)
  Context (prim_map : M.t primitive)
          (prims : list (primitive * positive)).
  Context (Hwf_glob : wf_glob Σ).
  Context (HnoVar : has_tVar = false)
          (HnoEvar : has_tEvar = false)
          (HnoCoFix : has_tCoFix = false)
          (HnoLazy : has_tLazy_Force = false)
          (Hblocks : cstr_as_blocks = true)
          (HnoArray : has_primarray = false).
  Context (no_prims : forall s, find_prim prims s = None).
  Context (cmap_complete : forall s d,
    lookup_constant Σ s = Some d -> lookup_const cmap s <> None).
  Context (cmap_sound : forall k v,
    lookup_const cmap k = Some v ->
    exists decl body,
      declared_constant Σ k decl /\ decl.(EAst.cst_body) = Some body).
  Context (cmap_nodup_keys : NoDup (map fst cmap)).

  Let val_rel_exists :=
    @anf_val_rel_exists func_tag default_tag prim_map tgm prims cmap
      _ Σ box_dc nat Hf_src Ht_src
      Hglob_term Hwf_glob
      HnoVar HnoEvar HnoCoFix HnoLazy Hblocks HnoArray
      no_prims cmap_complete cmap_sound cmap_nodup_keys Hcmap_eval_coherent.

  Let cvt_correct :=
    @anf_cvt_correct func_tag default_tag kon_tag
      tgm cmap cenv Σ _ dcon_to_tag_inj box_dc box_tag
      cenv_case_consistent Hcmap_eval_coherent
      Hglob_term Hglob_fuel_zero Hglob_wf val_rel_exists.

  Lemma in_map_fst_exists (l : list (kername * EAst.global_decl)) k :
    List.In k (map fst l) ->
    exists d, List.In (k, d) l.
  Proof.
    induction l as [| [k' d'] l' IH]; simpl.
    - contradiction.
    - intros [Heq | Hin].
      + subst k'. exists d'. left. reflexivity.
      + destruct (IH Hin) as [d Hin_d].
        exists d. right. exact Hin_d.
  Qed.

  Lemma suffix_extends prefix Σ0 :
    EWellformed.wf_glob (prefix ++ Σ0) ->
    EGlobalEnv.extends Σ0 (prefix ++ Σ0).
  Proof.
    intro Hwf.
    eapply EExtends.extends_prefix_extends.
    - exists prefix. reflexivity.
    - exact Hwf.
  Qed.

  Lemma anf_cvt_rel_cmap_lift :
    forall cm_acc,
      (forall s v, lookup_const cm_acc s = Some v -> lookup_const cmap s = Some v) ->
      forall S e vn S' C x,
        cvt_rel_at cm_acc S e vn S' C x ->
        anf_cvt_rel' S e vn S' C x.
  Proof.
    intros cm_acc Hcm_sub.
    apply (@anf_cvt_rel_ind' func_tag default_tag tgm cm_acc
      (fun S e vn S' C x => anf_cvt_rel' S e vn S' C x)
      (fun S es vn S' C xs =>
        anf_cvt_rel_args func_tag default_tag tgm cmap S es vn S' C xs)
      (fun Sset mfix vn fnames S' fdefs =>
        anf_cvt_rel_mfix func_tag default_tag tgm cmap Sset mfix vn fnames S' fdefs)
      (fun S ind brs n vn r S' pats =>
        anf_cvt_rel_branches func_tag default_tag tgm cmap S ind brs n vn r S' pats)).
    - intros. econstructor; eauto.
    - intros. econstructor; eauto.
    - intros. econstructor; eauto.
    - intros. econstructor; eauto.
    - intros. econstructor; eauto.
    - intros. econstructor; eauto.
    - intros. econstructor; eauto.
    - intros. econstructor; eauto.
    - intros S0 vn0 s v Hlk.
      apply (@anf_Const func_tag default_tag tgm cmap).
      now apply Hcm_sub.
    - intros. econstructor; eauto.
    - intros. econstructor; eauto.
    - intros. econstructor; eauto.
    - intros. econstructor; eauto.
    - intros. econstructor; eauto.
    - intros. econstructor; eauto.
    - intros. econstructor; eauto.
    - intros. econstructor; eauto.
  Qed.

  Lemma wellformed_dep_in_cm_acc :
    forall cm_acc Σ_proc body k v,
      EWellformed.wf_glob Σ_proc ->
      EGlobalEnv.extends Σ_proc Σ ->
      (forall s d, lookup_constant Σ_proc s = Some d ->
                   lookup_const cm_acc s <> None) ->
      wellformed Σ_proc 0 body = true ->
      kn_deps body k ->
      lookup_const cmap k = Some v ->
      lookup_const cm_acc k <> None.
  Proof.
    intros cm_acc Σ_proc body k v Hwf_proc Hext_proc Hcm_complete_proc
           Hwf_body Hdep Hlk_full.
    destruct (cmap_sound _ _ Hlk_full) as [decl [body0 [Hdecl_full Hbody0]]].
    assert (Hin_proc_fst : List.In k (map fst Σ_proc)).
    { eapply term_global_deps_fresh; eauto. }
    destruct (in_map_fst_exists Σ_proc k Hin_proc_fst) as [d_proc Hin_proc].
    assert (Hlookup_proc : lookup_env Σ_proc k = Some d_proc).
    { pose proof (EExtends.lookup_env_In efl (k, d_proc) Σ_proc Hwf_proc) as Hiff.
      exact ((proj2 Hiff) Hin_proc). }
    pose proof (Hext_proc _ _ Hlookup_proc) as Hlookup_full_from_proc.
    unfold declared_constant in Hdecl_full.
    rewrite Hdecl_full in Hlookup_full_from_proc.
    injection Hlookup_full_from_proc as <-.
    eapply Hcm_complete_proc.
    exact (EGlobalEnv.declared_constant_lookup Hlookup_proc).
  Qed.

  Lemma global_body_correct_acc :
    forall cm_acc Σ_proc,
      EWellformed.wf_glob Σ_proc ->
      EGlobalEnv.extends Σ_proc Σ ->
      (forall s v, lookup_const cm_acc s = Some v -> lookup_const cmap s = Some v) ->
      (forall s d, lookup_constant Σ_proc s = Some d ->
                   lookup_const cm_acc s <> None) ->
      (forall k v, lookup_const cm_acc k = Some v ->
                   exists decl body,
                     declared_constant Σ_proc k decl /\
                     decl.(EAst.cst_body) = Some body) ->
      NoDup (map fst cm_acc) ->
      @cmap_eval_coherent cm_acc _ Hf_src Ht_src Σ_proc box_dc ->
      forall body v C S S' rho src_v f t,
        wellformed Σ_proc 0 body = true ->
        cvt_rel_at cm_acc S body [] S' C v ->
        Disjoint _ (cmap_vars cm_acc) S ->
        glob_rel_at cm_acc Σ_proc (kn_deps body) rho ->
        eval_at Σ_proc [] body (Val src_v) f t ->
        exists anf_v,
          anf_val_rel' src_v anf_v /\
          forall e_k i,
            Disjoint _ (occurs_free e_k) ((S \\ S') \\ [set v]) ->
            preord_exp cenv (anf_bound f t) eq_fuel i
              (e_k, M.set v anf_v rho) (C |[ e_k ]|, rho).
  Proof.
    intros cm_acc Σ_proc Hwf_proc Hext_proc Hcm_sub
           Hcm_complete_proc Hcm_sound_proc Hnd_acc Hcoh_acc
           body v C S S' rho src_v f t
           Hwf Hcvt Hdis Hglob Heval.
    assert (Hcm_agree :
      forall s v0, lookup_const cmap s = Some v0 ->
                   lookup_const cm_acc s <> None ->
                   lookup_const cm_acc s = Some v0).
    { intros s v0 Hlk_full Hlk_some.
      destruct (lookup_const cm_acc s) as [v1|] eqn:Hlk_acc; [| contradiction].
      pose proof (Hcm_sub _ _ Hlk_acc) as Hlk_full_acc.
      rewrite Hlk_full in Hlk_full_acc. injection Hlk_full_acc as Heq.
      subst v1.
      reflexivity. }
    assert (Hcm_complete_decl :
      forall s decl, declared_constant Σ_proc s decl -> lookup_const cm_acc s <> None).
    { intros s decl Hdecl.
      eapply Hcm_complete_proc.
      exact (EGlobalEnv.declared_constant_lookup Hdecl). }
    assert (Hcm_sound_decl :
      forall k v0, lookup_const cm_acc k = Some v0 ->
                   exists decl, declared_constant Σ_proc k decl).
    { intros k v0 Hlk.
      destruct (Hcm_sound_proc _ _ Hlk) as [decl [body0 [Hdecl _]]].
      exists decl. exact Hdecl. }
    assert (Hglob_term_proc :
      forall k decl body0,
        declared_constant Σ_proc k decl ->
        decl.(EAst.cst_body) = Some body0 ->
        exists src_v0 f0 t0,
          eval_at Σ_proc [] body0 (Val src_v0) f0 t0).
    { intros k decl body0 Hdecl Hbody0.
      pose proof Hdecl as Hlk_proc.
      unfold declared_constant in Hlk_proc.
      pose proof (Hext_proc _ _ Hlk_proc) as Hlk_full.
      destruct (Hglob_term _ _ _ Hlk_full Hbody0) as [src_v0 [f0 [t0 Heval_full]]].
      assert (Hwf_body0 : wellformed Σ_proc 0 body0 = true).
      { eapply wf_glob_globals_wf; eauto. }
      pose proof (proj1 (@eval_env_fuel_restrict _ _ Hf_src Ht_src
                           Σ box_dc Σ_proc
                           [] body0 (fuel_sem.Val src_v0) f0 t0
                           Hwf_proc Hext_proc ltac:(constructor)
                           Hwf_body0 Heval_full))
        as Heval_proc.
      exists src_v0, f0, t0. exact Heval_proc. }
    assert (Hglob_fuel_zero_proc :
      forall k decl body0 src_v0 f0 t0,
        declared_constant Σ_proc k decl ->
        decl.(EAst.cst_body) = Some body0 ->
        eval_at Σ_proc [] body0 (Val src_v0) f0 t0 ->
        f0 = 0).
    { intros k decl body0 src_v0 f0 t0 Hdecl Hbody0 Heval_proc.
      pose proof Hdecl as Hdecl_proc.
      unfold declared_constant in Hdecl_proc.
      pose proof (Hext_proc _ _ Hdecl_proc) as Hdecl_full.
      pose proof (@eval_env_fuel_extends _ Hf_src Ht_src
                    Σ box_dc Σ_proc
                    [] body0 (fuel_sem.Val src_v0) f0 t0
                    Hext_proc Heval_proc) as Heval_full.
      eapply Hglob_fuel_zero.
      - exact Hdecl_full.
      - exact Hbody0.
      - exact Heval_full. }
    assert (Hglob_wf_proc :
      forall k decl body0,
        declared_constant Σ_proc k decl ->
        decl.(EAst.cst_body) = Some body0 ->
        wellformed Σ_proc 0 body0 = true).
    { intros k decl body0 Hdecl Hbody0.
      eapply wf_glob_globals_wf; eauto. }
    assert (Hval_rel_exists_acc :
      forall src_v0,
        well_formed_val Σ_proc src_v0 ->
        exists anf_v0, val_rel_at cm_acc Σ_proc src_v0 anf_v0).
    { intros src_v0 Hwf_src0.
      assert (Hwf_src_full : well_formed_val Σ src_v0).
      { eapply well_formed_val_extends; eauto. }
      destruct (val_rel_exists src_v0 Hwf_src_full) as [anf_v0 Hrel_full].
      exists anf_v0.
      eapply anf_val_rel_weaken; eauto.
    }
    assert (Hcons : @env_consistent [] []).
    { intros i0 j0 x0 Hi. rewrite nth_error_nil in Hi. discriminate. }
    assert (Hcmap_c : @cmap_consistent cm_acc _ Hf_src Ht_src Σ_proc box_dc [] []).
    { intros i0 x0 k0 decl0 body0 Hnth. rewrite nth_error_nil in Hnth. discriminate. }
    assert (Hdis_fn : Disjoint _ (FromList []) S).
    { rewrite FromList_nil. now apply Disjoint_Empty_set_l. }
    assert (Henv : env_rel_at cm_acc Σ_proc [] [] rho) by constructor.
    assert (Hwfe : well_formed_env Σ_proc []) by constructor.
    assert (Hwf_src : well_formed_val Σ_proc src_v).
    { eapply eval_preserves_wf; [exact Hglob_wf_proc | constructor | exact Hwf | exact Heval]. }
    assert (Hwf_src_full : well_formed_val Σ src_v).
    { eapply well_formed_val_extends; eauto. }
    destruct (val_rel_exists src_v Hwf_src_full) as [anf_v Hrel_v].
    assert (Hrel_v_acc : val_rel_at cm_acc Σ_proc src_v anf_v).
    { eapply anf_val_rel_weaken; eauto. }
    pose proof (@anf_cvt_correct
                  func_tag default_tag kon_tag
                  tgm cm_acc cenv Σ_proc _ dcon_to_tag_inj box_dc box_tag
                  cenv_case_consistent Hcoh_acc
                  Hglob_term_proc Hglob_fuel_zero_proc Hglob_wf_proc Hval_rel_exists_acc
                  [] body (fuel_sem.Val src_v) f t Heval)
      as Hcorrect.
    unfold anf_cvt_correct_exp in Hcorrect.
    exists anf_v. split; [exact Hrel_v |].
    intros e_k i Hdis_ek.
    exact ((Hcorrect rho [] C v S S' i Hwfe Hwf Hcons Hcmap_c Hdis_fn Hdis Henv Hglob Hcvt e_k Hdis_ek)
             src_v anf_v eq_refl Hrel_v_acc).
  Qed.


  (* ----------------------------------------------------------------- *)
  (** ** Composed global context correctness *)
  (* ----------------------------------------------------------------- *)

  (* Helper: S' \subset S for anf_cvt_rel_global, by induction on the
     relation. Each step either preserves S or shrinks it via the body's
     anf_cvt_rel. *)
  Lemma anf_cvt_global_subset :
    forall S gd cm_acc cm C_env S',
      anf_cvt_rel_global func_tag default_tag tgm S gd cm_acc cm C_env S' ->
      S' \subset S.
  Proof.
    intros S gd cm_acc cm C_env S' Hcvt.
    induction Hcvt as
      [ S0 cm0
      | S0 S1 S2 k0 body0 gd0 cm0 cm1 C0 C_rest0 v0 Hbody Hrest IH
      | S0 S0' k0 gd0 cm0 cm1 C_rest0 Hrest IH
      | S0 S0' k0 ind0 gd0 cm0 cm1 C_rest0 Hrest IH ].
    - apply Included_refl.
    - eapply Included_trans; [exact IH |].
      eapply anf_cvt_exp_subset. exact Hbody.
    - exact IH.
    - exact IH.
  Qed.

  Lemma anf_cvt_global_disjoint_acc :
    forall S gd cm_acc cm C_env S',
      anf_cvt_rel_global func_tag default_tag tgm S gd cm_acc cm C_env S' ->
      Disjoint _ (cmap_vars cm_acc) S ->
      Disjoint _ (cmap_vars cm) S'.
  Proof.
    intros S gd cm_acc cm C_env S' Hcvt.
    induction Hcvt as
      [ S0 cm0
      | S0 S1 S2 k body gd0 cm0 cm1 C0 C_rest0 v0 Hbody Hrest IH
      | S0 S0' k gd0 cm0 cm1 C_rest0 Hrest IH
      | S0 S0' k ind0 gd0 cm0 cm1 C_rest0 Hrest IH ];
      intros Hdis_acc.
    - exact Hdis_acc.
    - assert (Hdis_cm1 : Disjoint _ (cmap_vars ((k, v0) :: cm0)) S1).
      { constructor. intros z Hc.
        inversion Hc as [? Hzcm HzS1]; subst; clear Hc.
        destruct Hzcm as [s Hlk].
        simpl in Hlk.
        destruct (eq_kername s k) eqn:Hsk.
        + apply eq_kername_bool_eq in Hsk. subst s.
          injection Hlk as <-.
          eapply (anf_cvt_result_not_in_output
                    func_tag default_tag tgm cm0
                    S0 body [] S1 C0 v0 Hbody).
          * rewrite FromList_nil. now apply Disjoint_Empty_set_l.
          * exact Hdis_acc.
          * exact HzS1.
        + eapply Hdis_acc.
          constructor.
          * exists s. exact Hlk.
          * eapply anf_cvt_exp_subset; [exact Hbody | exact HzS1].
      }
      eapply IH. exact Hdis_cm1.
    - eapply IH. exact Hdis_acc.
    - eapply IH. exact Hdis_acc.
  Qed.

  Lemma anf_cvt_global_cmap_vars :
    forall S gd cm_acc cm C_env S',
      anf_cvt_rel_global func_tag default_tag tgm S gd cm_acc cm C_env S' ->
      cmap_vars cm \subset cmap_vars cm_acc :|: S.
  Proof.
    intros S gd cm_acc cm C_env S' Hcvt.
    induction Hcvt as
      [ S0 cm0
      | S0 S1 S2 k body gd0 cm0 cm1 C0 C_rest0 v0 Hbody Hrest IH
      | S0 S0' k gd0 cm0 cm1 C_rest0 Hrest IH
      | S0 S0' k ind0 gd0 cm0 cm1 C_rest0 Hrest IH ].
    - intros z Hz. left. exact Hz.
    - intros z Hz.
      specialize (IH _ Hz).
      inversion IH as [z' Hzacc | z' HzS1]; subst.
      + inversion Hzacc as [s Hlk]; subst.
        simpl in Hlk.
        destruct (eq_kername s k) eqn:Hsk.
        * apply eq_kername_bool_eq in Hsk. subst s.
          injection Hlk as <-.
          destruct (@anf_cvt_result_in_consumed
                      func_tag default_tag tgm cm0
                      S0 body [] S1 C0 v0 Hbody)
            as [Hin_vn | [Hin_s | Hin_cm]].
          -- rewrite FromList_nil in Hin_vn. contradiction.
          -- right. exact Hin_s.
          -- left. exact Hin_cm.
        * left. exists s. exact Hlk.
      + right. eapply anf_cvt_exp_subset; [exact Hbody | exact HzS1].
    - intros z Hz. eapply IH. exact Hz.
    - intros z Hz. eapply IH. exact Hz.
  Qed.

  Lemma comp_anf_bound_inclusion f1 t1 f2 t2 :
    inclusion (comp (anf_bound f1 t1) (anf_bound f2 t2))
      (anf_bound (f1 + f2) (t1 + t2)).
  Proof.
    unfold inclusion, comp, anf_bound.
    intros x z [y [Hxy Hyz]].
    destruct x as [[[e1 r1] f1'] t1'].
    destruct y as [[[e2 r2] f2'] t2'].
    destruct z as [[[e3 r3] f3'] t3'].
    simpl in *. lia.
  Qed.

  Lemma declared_constant_from_in Σ0 k decl :
    EWellformed.wf_glob Σ0 ->
    List.In (k, EAst.ConstantDecl decl) Σ0 ->
    declared_constant Σ0 k decl.
  Proof.
    intros Hwf0 Hin.
    pose proof (EExtends.lookup_env_In efl (k, EAst.ConstantDecl decl) Σ0 Hwf0) as Hiff.
    exact ((proj2 Hiff) Hin).
  Qed.

  Lemma declared_constant_in_map_fst Σ0 k decl :
    EWellformed.wf_glob Σ0 ->
    declared_constant Σ0 k decl ->
    List.In k (map fst Σ0).
  Proof.
    intros Hwf0 Hdecl.
    pose proof (EExtends.lookup_env_In efl (k, EAst.ConstantDecl decl) Σ0 Hwf0) as Hiff.
    exact (in_map fst _ _ ((proj1 Hiff) Hdecl)).
  Qed.

  Lemma declared_constant_cons_neq kn d Σ0 kn' decl :
    kn <> kn' ->
    declared_constant Σ0 kn' decl ->
    declared_constant ((kn, d) :: Σ0) kn' decl.
  Proof.
    intros Hneq Hdecl.
    unfold declared_constant in *.
    simpl. rewrite eq_kername_bool_neq; eauto.
  Qed.

  Lemma declared_constant_cons_inv_neq kn d Σ0 kn' decl :
    kn <> kn' ->
    declared_constant ((kn, d) :: Σ0) kn' decl ->
    declared_constant Σ0 kn' decl.
  Proof.
    intros Hneq Hdecl.
    unfold declared_constant in *.
    simpl in Hdecl. rewrite eq_kername_bool_neq in Hdecl; eauto.
  Qed.

  Lemma anf_cvt_rel_global_lookup_preserved :
    forall S gd cm_acc cm C_env S' k v,
      anf_cvt_rel_global func_tag default_tag tgm S gd cm_acc cm C_env S' ->
      lookup_const cm_acc k = Some v ->
      ~ List.In k (map fst gd) ->
      lookup_const cm k = Some v.
  Proof.
    intros S gd cm_acc cm C_env S' k v Hcvt.
    induction Hcvt; intros Hlk Hnotin.
    - exact Hlk.
    - simpl in Hnotin.
      assert (Hneq : k <> k0).
      { intro Heq. apply Hnotin. left. symmetry. exact Heq. }
      assert (Hnotin' : ~ List.In k (map fst gd')).
      { intro Hin. apply Hnotin. right. exact Hin. }
      simpl. destruct (eq_kername k k0) eqn:Hkk0.
      { exfalso. apply Hneq. now apply eq_kername_bool_eq in Hkk0. }
      { eapply IHHcvt.
        - simpl. rewrite Hkk0. exact Hlk.
        - exact Hnotin'. }
    - eapply IHHcvt; eauto.
      simpl in Hnotin. intro Hin. apply Hnotin. right. exact Hin.
    - eapply IHHcvt; eauto.
      simpl in Hnotin. intro Hin. apply Hnotin. right. exact Hin.
  Qed.

  Lemma cmap_eval_coherent_lift_head cm Σ_tail k d :
    EWellformed.wf_glob ((k, d) :: Σ_tail) ->
    (forall k0 v0, lookup_const cm k0 = Some v0 ->
       exists decl body,
         declared_constant Σ_tail k0 decl /\
         decl.(EAst.cst_body) = Some body) ->
    @cmap_eval_coherent cm _ Hf_src Ht_src Σ_tail box_dc ->
    @cmap_eval_coherent cm _ Hf_src Ht_src ((k, d) :: Σ_tail) box_dc.
  Proof.
    intros Hwf_cons Hcm_sound_tail Hcoh
           k1 k2 x decl1 body1 decl2 body2 src_v f t
           Hlk1 Hlk2 Hdecl1 Hbody1 Hdecl2 Hbody2 Heval1.
    assert (Hwf_tail : EWellformed.wf_glob Σ_tail).
    { eapply suffix_wf with (prefix := [(k, d)]). exact Hwf_cons. }
    assert (Hext_tail :
      EGlobalEnv.extends Σ_tail ((k, d) :: Σ_tail)).
    { eapply suffix_extends with (prefix := [(k, d)]). exact Hwf_cons. }
    assert (Hnotin_tail : ~ List.In k (map fst Σ_tail)).
    { eapply key_not_in_suffix with (prefix := []) (decl := d). exact Hwf_cons. }
    assert (Hneq1 : k1 <> k).
    { intro Heq. subst k1.
      destruct (Hcm_sound_tail _ _ Hlk1) as [decl [body [Hdecl _]]].
      apply Hnotin_tail.
      eapply declared_constant_in_map_fst; [exact Hwf_tail | exact Hdecl]. }
    assert (Hneq2 : k2 <> k).
    { intro Heq. subst k2.
      destruct (Hcm_sound_tail _ _ Hlk2) as [decl [body [Hdecl _]]].
      apply Hnotin_tail.
      eapply declared_constant_in_map_fst; [exact Hwf_tail | exact Hdecl]. }
    assert (Hdecl1_tail : declared_constant Σ_tail k1 decl1).
    { eapply declared_constant_cons_inv_neq; eauto. }
    assert (Hdecl2_tail : declared_constant Σ_tail k2 decl2).
    { eapply declared_constant_cons_inv_neq; eauto. }
    assert (Hwf_body1_tail : wellformed Σ_tail 0 body1 = true).
    { exact (wf_glob_globals_wf Σ_tail Hwf_tail _ _ _ Hdecl1_tail Hbody1). }
    pose proof (proj1 (@eval_env_fuel_restrict _ _ Hf_src Ht_src
                         ((k, d) :: Σ_tail) box_dc Σ_tail
                         [] body1 (fuel_sem.Val src_v) f t
                         Hwf_tail Hext_tail ltac:(constructor)
                         Hwf_body1_tail Heval1))
      as Heval1_tail.
    destruct (Hcoh _ _ _ _ _ _ _ _ _ _ Hlk1 Hlk2
                    Hdecl1_tail Hbody1 Hdecl2_tail Hbody2 Heval1_tail)
      as [f' [t' Heval2_tail]].
    exists f', t'. eapply eval_env_fuel_extends; eauto.
  Qed.

  Lemma global_ctx_correct_strong :
    forall (Σ_proc : EAst.global_context) gd cm_acc cm C_env S S',
      anf_cvt_rel_global func_tag default_tag tgm
        S gd cm_acc cm C_env S' ->
      Σ = List.rev gd ++ Σ_proc ->
      (* visible bindings in [cm_acc] agree with the section's full cmap *)
      (forall s v, lookup_const cm_acc s = Some v -> lookup_const cmap s = Some v) ->
      (* visible bindings in the final [cm] also agree with the section's full cmap *)
      (forall s v, lookup_const cm s = Some v -> lookup_const cmap s = Some v) ->
      (* [cm_acc] already contains all body-bearing constants from [Σ_proc] *)
      (forall s d, lookup_constant Σ_proc s = Some d ->
                   lookup_const cm_acc s <> None) ->
      (* visible bindings in [cm_acc] come from [Σ_proc] *)
      (forall k v, lookup_const cm_acc k = Some v ->
                   exists decl body,
                     declared_constant Σ_proc k decl /\
                     decl.(EAst.cst_body) = Some body) ->
      NoDup (map fst cm_acc) ->
      Disjoint _ (cmap_vars cm_acc) S ->
      @cmap_eval_coherent cm_acc _ Hf_src Ht_src Σ_proc box_dc ->
      forall rho_init,
        global_env_rel' (fun k => lookup_const cm_acc k <> None) rho_init ->
        exists rho_g F T,
        global_env_rel' (fun k => lookup_const cm k <> None) rho_g /\
          occurs_free_ctx C_env \subset (S \\ S') :|: cmap_vars cm_acc /\
          forall e_k i,
            Disjoint _ (occurs_free e_k) ((S \\ S') \\ cmap_vars cm) ->
            preord_exp cenv (anf_bound F T) eq_fuel i
              (e_k, rho_g) (C_env |[ e_k ]|, rho_init).
  Proof.
    intros Σ_proc gd cm_acc cm C_env S S' Hcvt.
    revert Σ_proc.
    induction Hcvt as
      [ S0 cm0
      | S0 S1 S2 k body gd' cm0 cm' C C_rest v Hbody_cvt Hrest IHrest
      | S0 S0' k gd' cm0 cm' C_rest Hrest IHrest
      | S0 S0' k ind gd' cm0 cm' C_rest Hrest IHrest ];
      intros Σ_proc HΣ_eq Hcm_sub Hcm_sub_final
             Hcm_complete_proc Hcm_sound_proc Hnd_acc Hdis_acc Hcoh_acc
             rho_init Hglob.
    - exists rho_init, 0, 0. split; [exact Hglob |]. split.
      + rewrite occurs_free_Hole_c. sets.
      + intros e_k i _. simpl.
        intros v1 c1 cout1 Hle1 Hstep1.
        exists v1, c1, cout1. split; [exact Hstep1 |]. split.
        * unfold anf_bound. lia.
        * unfold preord_res. destruct v1; [exact I |].
          eapply preord_val_refl. tci.
    - simpl in HΣ_eq.
      assert (Hwf_split : EWellformed.wf_glob
          (List.rev gd' ++ (k, EAst.ConstantDecl {| EAst.cst_body := Some body |}) :: Σ_proc)).
      { replace (List.rev gd' ++ (k, EAst.ConstantDecl {| EAst.cst_body := Some body |}) :: Σ_proc)
          with ((List.rev gd' ++ [(k, EAst.ConstantDecl {| EAst.cst_body := Some body |})]) ++ Σ_proc).
        2:{ rewrite <- app_assoc. simpl. reflexivity. }
        rewrite <- HΣ_eq. exact Hwf_glob. }
      assert (HΣ_rest : Σ = List.rev gd' ++
          ((k, EAst.ConstantDecl {| EAst.cst_body := Some body |}) :: Σ_proc)).
      { replace (List.rev gd' ++
                   ((k, EAst.ConstantDecl {| EAst.cst_body := Some body |}) :: Σ_proc))
          with ((List.rev gd' ++ [(k, EAst.ConstantDecl {| EAst.cst_body := Some body |})]) ++ Σ_proc).
        2:{ rewrite <- app_assoc. simpl. reflexivity. }
        exact HΣ_eq. }
      assert (Hwf_proc1 : EWellformed.wf_glob
          ((k, EAst.ConstantDecl {| EAst.cst_body := Some body |}) :: Σ_proc)).
      { eapply suffix_wf with (prefix := List.rev gd'). exact Hwf_split. }
      assert (Hwf_proc : EWellformed.wf_glob Σ_proc).
      { eapply suffix_wf with
          (prefix := List.rev gd' ++ [(k, EAst.ConstantDecl {| EAst.cst_body := Some body |})]).
        rewrite <- HΣ_eq. exact Hwf_glob. }
      assert (Hext_proc : EGlobalEnv.extends Σ_proc Σ).
      { pose proof Hwf_glob as Hwf_app.
        rewrite HΣ_eq.
        eapply suffix_extends with
          (prefix := List.rev gd' ++ [(k, EAst.ConstantDecl {| EAst.cst_body := Some body |})]).
        rewrite HΣ_eq in Hwf_app. exact Hwf_app. }
      assert (Hwf_body_proc : wellformed Σ_proc 0 body = true).
      { eapply wf_glob_head_const_some_wf. exact Hwf_proc1. }
      assert (Hext_proc_small :
        EGlobalEnv.extends Σ_proc ((k, EAst.ConstantDecl {| EAst.cst_body := Some body |}) :: Σ_proc)).
      { eapply suffix_extends with
          (prefix := [(k, EAst.ConstantDecl {| EAst.cst_body := Some body |})]).
        exact Hwf_proc1. }
      assert (Hnotin_proc : ~ List.In k (map fst Σ_proc)).
      { eapply key_not_in_suffix with
          (prefix := List.rev gd')
          (decl := EAst.ConstantDecl {| EAst.cst_body := Some body |}).
        exact Hwf_split. }
      assert (Hnotin_rev_gd' : ~ List.In k (map fst (List.rev gd'))).
      { eapply key_not_in_prefix with
          (decl := EAst.ConstantDecl {| EAst.cst_body := Some body |})
          (suffix := Σ_proc).
        exact Hwf_split. }
      assert (Hnotin_gd' : ~ List.In k (map fst gd')).
      { intro Hin. apply Hnotin_rev_gd'. rewrite map_rev. rewrite <- in_rev. exact Hin. }
      assert (Hdecl_cur_full : declared_constant Σ k {| EAst.cst_body := Some body |}).
      { eapply declared_constant_from_in; [exact Hwf_glob |].
        rewrite HΣ_rest. apply in_or_app. right. simpl. left. reflexivity. }
      assert (Hwf_body_full : wellformed Σ 0 body = true).
      { eapply Hglob_wf; [exact Hdecl_cur_full | reflexivity]. }
      assert (Hdeps_cur :
        forall k0 v0, kn_deps body k0 ->
                      lookup_const cmap k0 = Some v0 ->
                      lookup_const cm0 k0 <> None).
      { intros k0 v0 Hdep Hlk.
        eapply wellformed_dep_in_cm_acc
          with (Σ_proc := Σ_proc) (body := body); eauto. }
      assert (Hlk_cm_k : lookup_const cm' k = Some v).
      { eapply anf_cvt_rel_global_lookup_preserved with
          (S := S1) (gd := gd') (cm_acc := (k, v) :: cm0) (C_env := C_rest) (S' := S2);
          eauto.
        simpl. rewrite eq_kername_refl. reflexivity. }
      assert (Hlk_cmap_k : lookup_const cmap k = Some v).
      { eapply Hcm_sub_final. exact Hlk_cm_k. }
      destruct (Hglob_term k {| EAst.cst_body := Some body |} body Hdecl_cur_full eq_refl)
        as [src_v [f [t Heval_cur]]].
      assert (Hcm_agree_proc :
        forall s v0, lookup_const cmap s = Some v0 ->
                     lookup_const cm0 s <> None ->
                     lookup_const cm0 s = Some v0).
      { intros s v0 Hlk_full Hsome.
        destruct (lookup_const cm0 s) as [v1 |] eqn:Hlk_acc; [| contradiction].
        pose proof (Hcm_sub _ _ Hlk_acc) as Hlk_full_acc.
        rewrite Hlk_full in Hlk_full_acc. injection Hlk_full_acc as <-.
        reflexivity. }
      assert (Hcm_complete_decl_proc :
        forall s decl, declared_constant Σ_proc s decl -> lookup_const cm0 s <> None).
      { intros s decl Hdecl.
        eapply Hcm_complete_proc.
        exact (EGlobalEnv.declared_constant_lookup Hdecl). }
      assert (Hcm_sound_decl_proc :
        forall k0 v0, lookup_const cm0 k0 = Some v0 ->
                      exists decl, declared_constant Σ_proc k0 decl).
      { intros k0 v0 Hlk.
        destruct (Hcm_sound_proc _ _ Hlk) as [decl [body0 [Hdecl0 _]]].
        exists decl. exact Hdecl0. }
      assert (Hglob_proc_all :
        glob_rel_at cm0 Σ_proc (fun k0 => lookup_const cm0 k0 <> None) rho_init).
      { intros k0 v0 Hd Hlk_cm0.
        pose proof (Hcm_sub _ _ Hlk_cm0) as Hlk_full.
        destruct (Hglob k0 v0 Hd Hlk_full)
          as [decl_full [body_full [anf_v0 [Hdecl_full [Hbody_full [Hget0 Hrel0]]]]]].
        destruct (Hcm_sound_proc _ _ Hlk_cm0)
          as [decl_proc [body_proc [Hdecl_proc Hbody_proc0]]].
        pose proof (Hext_proc _ _ Hdecl_proc) as Hdecl_full_from_proc.
        unfold declared_constant in Hdecl_full, Hdecl_full_from_proc.
        rewrite Hdecl_full in Hdecl_full_from_proc.
        injection Hdecl_full_from_proc as <-.
        assert (Hbody_eq : body_proc = body_full).
        { rewrite Hbody_proc0 in Hbody_full. injection Hbody_full as <-. reflexivity. }
        subst body_proc.
        exists decl_full, body_full, anf_v0.
        split; [exact Hdecl_proc |].
        split; [exact Hbody_full |].
        split; [exact Hget0 |].
        intros src_v1 f1 t1 Heval_proc.
        assert (Heval_full :
          @eval_env_fuel _ Hf_src Ht_src Σ box_dc []
            body_full (fuel_sem.Val src_v1) f1 t1).
        { eapply eval_env_fuel_extends; eauto. }
        pose proof (Hrel0 _ _ _ Heval_full) as Hrel_full.
        assert (Hwf_src1 : well_formed_val Σ_proc src_v1).
        { eapply eval_preserves_wf; [exact (wf_glob_globals_wf Σ_proc Hwf_proc) | constructor | | exact Heval_proc].
          exact (wf_glob_globals_wf Σ_proc Hwf_proc _ _ _ Hdecl_proc Hbody_full). }
        assert (Hrel_part : val_rel_at cm0 Σ_proc src_v1 anf_v0).
        { exact (@anf_val_rel_weaken
                   func_tag default_tag tgm efl
                   box_dc box_tag
                   cmap Σ
                   cm0 Σ_proc
                   Hwf_proc Hext_proc
                   Hcm_sub Hcm_agree_proc
                   Hcm_complete_decl_proc
                   src_v1 Hwf_src1 anf_v0 Hrel_full). }
        exact Hrel_part. }
      assert (Hglob_body_proc :
        glob_rel_at cm0 Σ_proc (kn_deps body) rho_init).
      { intros k0 v0 _ Hlk.
        eapply Hglob_proc_all.
        - intro Hnone. rewrite Hlk in Hnone. discriminate.
        - exact Hlk. }
      assert (Heval_cur_proc : eval_at Σ_proc [] body (Val src_v) f t).
      { pose proof (proj1 (@eval_env_fuel_restrict _ _ Hf_src Ht_src
                           Σ box_dc Σ_proc
                           [] body (fuel_sem.Val src_v) f t
                           Hwf_proc Hext_proc ltac:(constructor)
                           Hwf_body_proc Heval_cur))
          as Heval_proc.
        exact Heval_proc. }
      destruct (global_body_correct_acc cm0 Σ_proc
                 Hwf_proc Hext_proc Hcm_sub Hcm_complete_proc Hcm_sound_proc
                 Hnd_acc Hcoh_acc
                 body v C S0 S1 rho_init src_v f t
                 Hwf_body_proc Hbody_cvt Hdis_acc Hglob_body_proc Heval_cur_proc)
        as [anf_v [Hrel_v Hpre_body]].
      assert (Hnotin_cm0 : ~ List.In k (map fst cm0)).
      { intro Hin.
        destruct (in_map_fst_nodup_lookup_const_exists cm0 Hnd_acc k Hin)
          as [v0 Hlk0].
        destruct (Hcm_sound_proc _ _ Hlk0) as [decl0 [body0 [Hdecl0 _]]].
        apply Hnotin_proc.
        eapply declared_constant_in_map_fst; [exact Hwf_proc | exact Hdecl0]. }
      assert (Hnd_acc1 : NoDup (map fst ((k, v) :: cm0))).
      { constructor; [exact Hnotin_cm0 | exact Hnd_acc]. }
      assert (Hdis_acc1 : Disjoint _ (cmap_vars ((k, v) :: cm0)) S1).
      { constructor. intros z Hc.
        inversion Hc as [? Hzcm HzS1]; subst; clear Hc.
        destruct Hzcm as [s Hlk].
        simpl in Hlk.
        destruct (eq_kername s k) eqn:Hsk.
        - apply eq_kername_bool_eq in Hsk. subst s.
          injection Hlk as <-.
          eapply (anf_cvt_result_not_in_output
                    func_tag default_tag tgm cm0
                    S0 body [] S1 C v Hbody_cvt).
          + rewrite FromList_nil. now apply Disjoint_Empty_set_l.
          + exact Hdis_acc.
          + exact HzS1.
        - eapply Hdis_acc.
          constructor.
          + exists s. exact Hlk.
          + eapply anf_cvt_exp_subset; [exact Hbody_cvt | exact HzS1].
      }
      assert (Hcoh_old1 :
        @cmap_eval_coherent cm0 _ Hf_src Ht_src
          ((k, EAst.ConstantDecl {| EAst.cst_body := Some body |}) :: Σ_proc) box_dc).
      { eapply cmap_eval_coherent_lift_head; eauto. }
      assert (Hcoh_proc1 :
        @cmap_eval_coherent ((k, v) :: cm0) _ Hf_src Ht_src
          ((k, EAst.ConstantDecl {| EAst.cst_body := Some body |}) :: Σ_proc) box_dc).
      { intros k1 k2 x decl1 body1 decl2 body2 src_v0 f0 t0
               Hlk1 Hlk2 Hdecl1 Hbody1 Hdecl2 Hbody2 Heval1.
        simpl in Hlk1, Hlk2.
        destruct (eq_kername k1 k) eqn:Hk1;
        destruct (eq_kername k2 k) eqn:Hk2.
        - apply eq_kername_bool_eq in Hk1. apply eq_kername_bool_eq in Hk2.
          subst k1 k2. injection Hlk1 as <-.
          unfold declared_constant in Hdecl1, Hdecl2.
          simpl in Hdecl1, Hdecl2.
          rewrite eq_kername_refl in Hdecl1, Hdecl2.
          injection Hdecl1 as <-. injection Hdecl2 as <-.
          rewrite Hbody1 in Hbody2. injection Hbody2 as <-.
          exists f0, t0. exact Heval1.
        - apply eq_kername_bool_eq in Hk1. subst k1.
          injection Hlk1 as <-.
          unfold declared_constant in Hdecl1.
          simpl in Hdecl1. rewrite eq_kername_refl in Hdecl1.
          injection Hdecl1 as <-.
          simpl in Hbody1. injection Hbody1 as <-.
          assert (Hlk2_tail : lookup_const cm0 k2 = Some v).
          { exact Hlk2. }
          assert (Hdecl2_tail : declared_constant Σ_proc k2 decl2).
          { eapply declared_constant_cons_inv_neq.
            - intro Heq. apply (eq_kername_bool_neq_inv Hk2). symmetry. exact Heq.
            - exact Hdecl2. }
          pose proof (proj1 (@eval_env_fuel_restrict _ _ Hf_src Ht_src
                               ((k, EAst.ConstantDecl {| EAst.cst_body := Some body |}) :: Σ_proc)
                               box_dc Σ_proc
                               [] body (fuel_sem.Val src_v0) f0 t0
                               Hwf_proc Hext_proc_small ltac:(constructor)
                               Hwf_body_proc Heval1))
            as Heval1_tail.
          assert (Hdis_nil : Disjoint _ (FromList []) S0).
          { rewrite FromList_nil. now apply Disjoint_Empty_set_l. }
          assert (Hcons_nil : @env_consistent [] []).
          { intros i0 j0 x0 Hi. rewrite nth_error_nil in Hi. discriminate. }
          assert (Hcmap_nil : @cmap_consistent cm0 _ Hf_src Ht_src Σ_proc box_dc [] []).
          { intros i0 x0 k0 decl0 body0 Hnth. rewrite nth_error_nil in Hnth. discriminate. }
          destruct (@anf_cvt_cmap_eval func_tag default_tag tgm cm0 Σ_proc box_dc
                      box_tag Hcoh_acc
                      [] body src_v0 f0 t0 Heval1_tail
                      S0 [] S1 C v k2 decl2 body2
                      Hbody_cvt Hdis_nil Hdis_acc Hcons_nil Hcmap_nil
                      Hlk2_tail Hdecl2_tail Hbody2)
            as [f' [t' Heval2_tail]].
          exists f', t'. exact (@eval_env_fuel_extends _ Hf_src Ht_src
                                 ((k, EAst.ConstantDecl {| EAst.cst_body := Some body |}) :: Σ_proc)
                                 box_dc Σ_proc [] body2 (fuel_sem.Val src_v0) f' t'
                                 Hext_proc_small Heval2_tail).
        - apply eq_kername_bool_eq in Hk2. subst k2.
          injection Hlk2 as <-.
          unfold declared_constant in Hdecl2.
          simpl in Hdecl2. rewrite eq_kername_refl in Hdecl2.
          injection Hdecl2 as <-.
          simpl in Hbody2. injection Hbody2 as <-.
          assert (Hlk1_tail : lookup_const cm0 k1 = Some v).
          { exact Hlk1. }
          assert (Hdecl1_tail : declared_constant Σ_proc k1 decl1).
          { eapply declared_constant_cons_inv_neq.
            - intro Heq. apply (eq_kername_bool_neq_inv Hk1). symmetry. exact Heq.
            - exact Hdecl1. }
          assert (Hwf_body1_tail : wellformed Σ_proc 0 body1 = true).
          { exact (wf_glob_globals_wf Σ_proc Hwf_proc _ _ _ Hdecl1_tail Hbody1). }
          pose proof (proj1 (@eval_env_fuel_restrict _ _ Hf_src Ht_src
                               ((k, EAst.ConstantDecl {| EAst.cst_body := Some body |}) :: Σ_proc)
                               box_dc Σ_proc
                               [] body1 (fuel_sem.Val src_v0) f0 t0
                               Hwf_proc Hext_proc_small ltac:(constructor)
                               Hwf_body1_tail Heval1))
            as Heval1_tail.
          destruct (Hglob_term k {| EAst.cst_body := Some body |} body Hdecl_cur_full eq_refl)
            as [src_v_new [f_new [t_new Heval_new_full]]].
          pose proof (proj1 (@eval_env_fuel_restrict _ _ Hf_src Ht_src
                               Σ box_dc Σ_proc
                               [] body (fuel_sem.Val src_v_new) f_new t_new
                               Hwf_proc Hext_proc ltac:(constructor)
                               Hwf_body_proc Heval_new_full))
            as Heval_new_tail.
          assert (Hdis_nil : Disjoint _ (FromList []) S0).
          { rewrite FromList_nil. now apply Disjoint_Empty_set_l. }
          assert (Hcons_nil : @env_consistent [] []).
          { intros i0 j0 x0 Hi. rewrite nth_error_nil in Hi. discriminate. }
          assert (Hcmap_nil : @cmap_consistent cm0 _ Hf_src Ht_src Σ_proc box_dc [] []).
          { intros i0 x0 k0 decl0 body0 Hnth. rewrite nth_error_nil in Hnth. discriminate. }
          destruct (@anf_cvt_cmap_eval func_tag default_tag tgm cm0 Σ_proc box_dc
                      box_tag Hcoh_acc
                      [] body src_v_new f_new t_new Heval_new_tail
                      S0 [] S1 C v k1 decl1 body1
                      Hbody_cvt Hdis_nil Hdis_acc Hcons_nil Hcmap_nil
                      Hlk1_tail Hdecl1_tail Hbody1)
            as [f' [t' Heval1_from_new]].
          assert (src_v_new = src_v0) by (eapply eval_val_det; eassumption).
          subst src_v_new.
          exists f_new, t_new. exact (@eval_env_fuel_extends _ Hf_src Ht_src
                                 ((k, EAst.ConstantDecl {| EAst.cst_body := Some body |}) :: Σ_proc)
                                 box_dc Σ_proc [] body (fuel_sem.Val src_v0) f_new t_new
                                 Hext_proc_small Heval_new_tail).
        - assert (Hlk1_tail : lookup_const cm0 k1 = Some x) by exact Hlk1.
          assert (Hlk2_tail : lookup_const cm0 k2 = Some x) by exact Hlk2.
          exact (Hcoh_old1 _ _ _ _ _ _ _ _ _ _ Hlk1_tail Hlk2_tail
                           Hdecl1 Hbody1 Hdecl2 Hbody2 Heval1).
      }
      assert (Hglob_mid :
        global_env_rel' (fun k0 => lookup_const ((k, v) :: cm0) k0 <> None)
          (M.set v anf_v rho_init)).
      { intros k0 v0 Hd Hlk0.
        simpl in Hlk0. destruct (eq_kername k0 k) eqn:Hk0k.
        - apply eq_kername_bool_eq in Hk0k. subst k0.
          rewrite Hlk_cmap_k in Hlk0. injection Hlk0 as <-.
          exists {| EAst.cst_body := Some body |}, body, anf_v.
          repeat split; try reflexivity.
          + exact Hdecl_cur_full.
          + apply M.gss.
          + intros src_v0 f0 t0 Heval0.
            assert (src_v0 = src_v) by (eapply eval_val_det; eassumption).
            subst src_v0. exact Hrel_v.
        - assert (Hd_old : lookup_const cm0 k0 <> None).
          { intro Hnone. apply Hd. simpl. rewrite Hk0k. exact Hnone. }
          destruct (Hglob k0 v0 Hd_old Hlk0)
            as [decl0 [body0 [anf_v0 [Hdecl0 [Hbody0 [Hget0 Hrel0]]]]]].
          destruct (M.elt_eq v0 v) as [Heqv | Hneqv].
          + subst v0.
            exists decl0, body0, anf_v.
            repeat split; try exact Hdecl0; try exact Hbody0.
            * apply M.gss.
            * intros src_v0 f0 t0 Heval0.
              destruct (Hcmap_eval_coherent
                          k0 k v decl0 body0
                          {| EAst.cst_body := Some body |} body src_v0 f0 t0
                          Hlk0 Hlk_cmap_k Hdecl0 Hbody0 Hdecl_cur_full eq_refl Heval0)
                as [f1 [t1 Heval1]].
              assert (src_v0 = src_v)
                by (eapply eval_val_det; eassumption).
              subst src_v0. exact Hrel_v.
          + exists decl0, body0, anf_v0.
            repeat split; try exact Hdecl0; try exact Hbody0; try exact Hrel0.
            rewrite M.gso; [exact Hget0 | exact Hneqv]. }
      assert (Hcm_sub_rest :
        forall s v0, lookup_const ((k, v) :: cm0) s = Some v0 -> lookup_const cmap s = Some v0).
      { intros s v0 Hlk.
        simpl in Hlk. destruct (eq_kername s k) eqn:Hsk.
        - apply eq_kername_bool_eq in Hsk. subst s.
          injection Hlk as <-. exact Hlk_cmap_k.
        - exact (Hcm_sub _ _ Hlk). }
      assert (Hcm_complete_proc1 :
        forall s d, lookup_constant
                      ((k, EAst.ConstantDecl {| EAst.cst_body := Some body |}) :: Σ_proc) s = Some d ->
                    lookup_const ((k, v) :: cm0) s <> None).
      { intros s d Hlk.
        simpl in Hlk. simpl. destruct (eq_kername s k) eqn:Hsk.
        - discriminate.
        - unfold lookup_constant in Hlk. simpl in Hlk. rewrite Hsk in Hlk.
          eapply Hcm_complete_proc. exact Hlk. }
      assert (Hcm_sound_proc1 :
        forall k0 v0, lookup_const ((k, v) :: cm0) k0 = Some v0 ->
                      exists decl body0,
                        declared_constant
                          ((k, EAst.ConstantDecl {| EAst.cst_body := Some body |}) :: Σ_proc) k0 decl /\
                        decl.(EAst.cst_body) = Some body0).
      { intros k0 v0 Hlk.
        simpl in Hlk. destruct (eq_kername k0 k) eqn:Hk0k.
        - apply eq_kername_bool_eq in Hk0k. subst k0.
          injection Hlk as <-.
          exists {| EAst.cst_body := Some body |}, body.
          split.
          + unfold declared_constant. simpl. rewrite eq_kername_refl. reflexivity.
          + reflexivity.
        - destruct (Hcm_sound_proc _ _ Hlk) as [decl [body0 [Hdecl0 Hbody0]]].
          exists decl, body0. split.
          + eapply declared_constant_cons_neq; [| exact Hdecl0 ].
            intro Heq. apply (eq_kername_bool_neq_inv Hk0k). symmetry. exact Heq.
          + exact Hbody0. }
      destruct (IHrest ((k, EAst.ConstantDecl {| EAst.cst_body := Some body |}) :: Σ_proc) HΣ_rest
                 Hcm_sub_rest Hcm_sub_final Hcm_complete_proc1 Hcm_sound_proc1
                 Hnd_acc1 Hdis_acc1 Hcoh_proc1
                 (M.set v anf_v rho_init) Hglob_mid)
        as [rho_g [F_rest [T_rest [Hglob_g [Hctx_rest Hpre_rest]]]]].
      exists rho_g, (F_rest + f), (T_rest + t). split; [exact Hglob_g |]. split.
      + assert (HS2_S1 : S2 \subset S1).
        { eapply anf_cvt_global_subset. exact Hrest. }
        assert (HS1_S0 : S1 \subset S0).
        { eapply anf_cvt_exp_subset. exact Hbody_cvt. }
        assert (Hdis_nil : Disjoint _ (FromList []) S0).
        { constructor. intros z Hz. inversion Hz as [? Hzl _]. unfold FromList, Ensembles.In in Hzl. contradiction. }
        assert (Hctx_body0 :
          occurs_free_ctx C \subset FromList [] :|: (S0 \\ S1) :|: cmap_vars cm0).
        { exact (@anf_cvt_occurs_free_ctx_exp
                   func_tag default_tag tgm cm0 Σ_proc box_dc box_tag
                   S0 body [] S1 C v
                   Hbody_cvt Hdis_nil Hdis_acc). }
        assert (Hctx_body : occurs_free_ctx C \subset (S0 \\ S1) :|: cmap_vars cm0).
        { rewrite FromList_nil, Union_Empty_set_neut_l in Hctx_body0.
          exact Hctx_body0. }
        eapply Included_trans; [eapply occurs_free_ctx_comp |].
        eapply Union_Included.
        * intros z Hz.
          specialize (Hctx_body _ Hz) as Htmp.
          inversion Htmp as [z' Hss1 | z' Hzc]; subst.
          -- left. constructor.
             ++ exact (proj1 Hss1).
             ++ intro HzS2. apply (proj2 Hss1). eapply HS2_S1. exact HzS2.
          -- right. exact Hzc.
        * eapply Included_trans; [eapply Setminus_Included |].
          intros z Hz.
          specialize (Hctx_rest _ Hz) as Htmp.
          inversion Htmp as [z' Hs1s2 | z' Hzc]; subst.
          -- left. constructor.
             ++ eapply HS1_S0. exact (proj1 Hs1s2).
             ++ exact (proj2 Hs1s2).
          -- destruct Hzc as [s Hlk].
             simpl in Hlk.
             destruct (eq_kername s k) eqn:Hsk.
             ++ apply eq_kername_bool_eq in Hsk. subst s.
                injection Hlk as <-.
                destruct (@anf_cvt_result_in_consumed
                            func_tag default_tag tgm cm0
                            S0 body [] S1 C v Hbody_cvt)
                  as [Hin_vn | [Hin_s | Hin_cm]].
                ** rewrite FromList_nil in Hin_vn. contradiction.
                ** left. constructor.
                   { exact Hin_s. }
                   { intro HzS2.
                     eapply (anf_cvt_result_not_in_output
                               func_tag default_tag tgm cm0
                               S0 body [] S1 C v Hbody_cvt).
                     - rewrite FromList_nil. now apply Disjoint_Empty_set_l.
                     - exact Hdis_acc.
                     - eapply HS2_S1. exact HzS2. }
                ** right. exact Hin_cm.
             ++ right. exists s. exact Hlk.
	        + intros e_k i Hdis_ek.
		        assert (HS1_S0 : S1 \subset S0).
		        { eapply anf_cvt_exp_subset. exact Hbody_cvt. }
		        assert (HS2_S1 : S2 \subset S1).
		        { eapply anf_cvt_global_subset. exact Hrest. }
		        assert (Hdis_ek_rest : Disjoint _ (occurs_free e_k) ((S1 \\ S2) \\ cmap_vars cm')).
		        { eapply Disjoint_Included_r.
		          - eapply Included_Setminus_compat.
                + eapply Included_Setminus_compat.
                  * exact HS1_S0.
                  * eapply Included_refl.
                + eapply Included_refl.
		          - exact Hdis_ek. }
		        assert (Hcm_vars_rest :
              cmap_vars cm' \subset cmap_vars ((k, v) :: cm0) :|: S1).
        { eapply anf_cvt_global_cmap_vars. exact Hrest. }
		        assert (Hdis_cont :
		          Disjoint _ (occurs_free (C_rest |[ e_k ]|)) ((S0 \\ S1) \\ [set v])).
	        { constructor. intros z Hz.
	          inversion Hz as [? Hzf Hzt]; subst; clear Hz.
	          apply occurs_free_ctx_app in Hzf. inversion Hzf; subst.
	          - specialize (Hctx_rest _ H).
	            inversion Hctx_rest as [z0 Hzs | z0 Hzc]; subst.
	            + destruct Hzs as [HzS1 HznotS2].
	              destruct Hzt as [[HzS0 HznotS1] Hznotv].
	              apply HznotS1. exact HzS1.
	            + destruct Hzc as [s Hlk].
	              simpl in Hlk.
		              destruct (eq_kername s k) eqn:Hsk.
		              * apply eq_kername_bool_eq in Hsk. subst s.
		                injection Hlk as <-.
		                destruct Hzt as [_ Hznotv].
		                apply Hznotv. constructor.
		              * eapply Hdis_acc.
		                constructor.
		                -- exists s. exact Hlk.
		                -- exact (proj1 (proj1 Hzt)).
		          - assert (Hdis_ek' :
			               Disjoint _ (occurs_free e_k) ((S0 \\ S1) \\ [set v])).
		            { constructor. intros y Hy.
		              inversion Hy as [? Hyf Hyt]; subst; clear Hy.
		              destruct Hyt as [[HzS0 HznotS1] Hznotv].
		              assert (HnotS2 : ~ y \in S2).
		              { intro HzS2. apply HznotS1. eapply HS2_S1. exact HzS2. }
		              assert (Hnotcm : ~ y \in cmap_vars cm').
		              { intro Hzcm.
		                specialize (Hcm_vars_rest _ Hzcm) as Htmp.
		                inversion Htmp as [z' Hzacc | z' HzS1]; subst.
		                - inversion Hzacc as [s Hlk]. subst.
		                  simpl in Hlk.
		                  destruct (eq_kername s k) eqn:Hsk.
		                  + apply eq_kername_bool_eq in Hsk. subst s.
		                    injection Hlk as <-.
		                    apply Hznotv. constructor.
		                  + eapply Hdis_acc.
		                    constructor.
		                    * exists s. exact Hlk.
		                    * exact HzS0.
		                - exact (HznotS1 HzS1). }
		              eapply Hdis_ek.
		              unfold Setminus, Ensembles.In in *.
		              repeat split; eauto. }
		            eapply Disjoint_In_l.
		            + exact Hdis_ek'.
		            + exact (proj1 H).
	            + exact Hzt. }
		        eapply preord_exp_post_monotonic.
		        2:{ eapply preord_exp_trans; [tci | exact eq_fuel_idemp | | ].
	            - exact (Hpre_rest e_k i Hdis_ek_rest).
	            - intros m. rewrite <- app_ctx_f_fuse.
	              exact (Hpre_body (C_rest |[ e_k ]|) m Hdis_cont). }
        exact (comp_anf_bound_inclusion F_rest T_rest f t).
    - simpl in HΣ_eq.
      assert (Hwf_split : EWellformed.wf_glob (List.rev gd' ++ (k, EAst.ConstantDecl {| EAst.cst_body := None |}) :: Σ_proc)).
      { replace (List.rev gd' ++ (k, EAst.ConstantDecl {| EAst.cst_body := None |}) :: Σ_proc)
          with ((List.rev gd' ++ [(k, EAst.ConstantDecl {| EAst.cst_body := None |})]) ++ Σ_proc).
        2:{ rewrite <- app_assoc. simpl. reflexivity. }
        rewrite <- HΣ_eq. exact Hwf_glob. }
      assert (Hwf_proc1 : EWellformed.wf_glob ((k, EAst.ConstantDecl {| EAst.cst_body := None |}) :: Σ_proc)).
      { eapply suffix_wf with (prefix := List.rev gd'). exact Hwf_split. }
      exfalso.
      eapply (@wf_glob_head_const_none_absurd efl HnoAxioms Σ_proc k).
      exact Hwf_proc1.
    - simpl in HΣ_eq.
      assert (Hwf_split : EWellformed.wf_glob (List.rev gd' ++ (k, EAst.InductiveDecl ind) :: Σ_proc)).
      { replace (List.rev gd' ++ (k, EAst.InductiveDecl ind) :: Σ_proc)
          with ((List.rev gd' ++ [(k, EAst.InductiveDecl ind)]) ++ Σ_proc).
        2:{ rewrite <- app_assoc. simpl. reflexivity. }
        rewrite <- HΣ_eq. exact Hwf_glob. }
	      assert (HΣ_rest : Σ = List.rev gd' ++ ((k, EAst.InductiveDecl ind) :: Σ_proc)).
	      { replace (List.rev gd' ++ ((k, EAst.InductiveDecl ind) :: Σ_proc))
	          with ((List.rev gd' ++ [(k, EAst.InductiveDecl ind)]) ++ Σ_proc).
	        2:{ rewrite <- app_assoc. simpl. reflexivity. }
	        exact HΣ_eq. }
	      assert (Hwf_proc1 : EWellformed.wf_glob ((k, EAst.InductiveDecl ind) :: Σ_proc)).
	      { eapply suffix_wf with (prefix := List.rev gd'). exact Hwf_split. }
	      assert (Hwf_proc : EWellformed.wf_glob Σ_proc).
	      { eapply suffix_wf with (prefix := List.rev gd' ++ [(k, EAst.InductiveDecl ind)]).
	        rewrite <- HΣ_eq. exact Hwf_glob. }
      assert (Hnotin_proc : ~ List.In k (map fst Σ_proc)).
      { eapply key_not_in_suffix with (prefix := List.rev gd') (decl := EAst.InductiveDecl ind).
        exact Hwf_split. }
	      assert (Hcm_complete_proc1 :
	        forall s d, lookup_constant ((k, EAst.InductiveDecl ind) :: Σ_proc) s = Some d ->
	                    lookup_const cm0 s <> None).
	      { intros s d Hlk.
	        unfold lookup_constant in Hlk. simpl in Hlk.
	        destruct (eq_kername s k) eqn:Hsk.
	        { apply eq_kername_bool_eq in Hsk. subst s. discriminate. }
	        { change (lookup_constant Σ_proc s = Some d) in Hlk.
	          eapply Hcm_complete_proc. exact Hlk. } }
	      assert (Hcm_sound_proc1 :
	        forall k0 v0, lookup_const cm0 k0 = Some v0 ->
	                      exists decl body,
	                        declared_constant ((k, EAst.InductiveDecl ind) :: Σ_proc) k0 decl /\
	                        decl.(EAst.cst_body) = Some body).
	      { intros k0 v0 Hlk.
	        destruct (Hcm_sound_proc _ _ Hlk) as [decl [body0 [Hdecl0 Hbody0]]].
	        assert (Hneq : k <> k0).
	        { intro Heq. subst k0.
	          apply Hnotin_proc.
	          eapply declared_constant_in_map_fst; eauto. }
	        exists decl, body0. split.
	        { eapply declared_constant_cons_neq; [exact Hneq | exact Hdecl0]. }
	        { exact Hbody0. } }
	      assert (Hcoh_proc1 :
	        @cmap_eval_coherent cm0 _ Hf_src Ht_src
	          ((k, EAst.InductiveDecl ind) :: Σ_proc) box_dc).
	      { eapply cmap_eval_coherent_lift_head.
	        - exact Hwf_proc1.
	        - exact Hcm_sound_proc.
	        - exact Hcoh_acc. }
      eapply IHrest with (Σ_proc := (k, EAst.InductiveDecl ind) :: Σ_proc); eauto.
  Qed.

  (** The composed binding context [C_env] from [anf_cvt_rel_global],
      when evaluated starting from [rho_init], produces an environment
      where all new global bindings are correctly related.

      [Σ_proc] tracks the part of [Σ] already processed; [gd] is the
      remaining part, in oldest-first order. The invariant
      [Σ = rev gd ++ Σ_proc] captures their relationship and lets us
      derive wellformedness and freshness facts from [wf_glob Σ].

      The proof goes by induction on [anf_cvt_rel_global]:
      - Base: [C_env = Hole_c], [rho_g = rho_init], nothing to prove.
      - Const step: [C_env = comp_ctx_f C C_rest].
        [global_body_correct_full] gives a [preord_exp] for [C],
        the IH gives one for [C_rest], and [preord_exp_trans] chains them.
      - No-body step: impossible when [has_axioms = false].
      - Inductive step: pass through to IH unchanged. *)
  Lemma global_ctx_correct :
    forall (Σ_proc : EAst.global_context) gd cm_acc cm C_env S S',
      anf_cvt_rel_global func_tag default_tag tgm
        S gd cm_acc cm C_env S' ->
      (* gd is the unprocessed prefix of [rev Σ]; Σ_proc is what's done *)
      Σ = List.rev gd ++ Σ_proc ->
      (* visible bindings in [cm_acc] agree with the section's full cmap *)
      (forall s v, lookup_const cm_acc s = Some v -> lookup_const cmap s = Some v) ->
      (* visible bindings in the final [cm] also agree with the section's full cmap *)
      (forall s v, lookup_const cm s = Some v -> lookup_const cmap s = Some v) ->
      (* [cm_acc] covers exactly Σ_proc's constant bodies *)
      (forall s d, lookup_constant Σ_proc s = Some d ->
                   lookup_const cm_acc s <> None) ->
      (forall k v, lookup_const cm_acc k = Some v ->
                   exists decl body,
                     declared_constant Σ_proc k decl /\
                     decl.(EAst.cst_body) = Some body) ->
      NoDup (map fst cm_acc) ->
      Disjoint _ (cmap_vars cm_acc) S ->
      @cmap_eval_coherent cm_acc _ Hf_src Ht_src Σ_proc box_dc ->
      forall rho_init,
        global_env_rel' (fun k => lookup_const cm_acc k <> None) rho_init ->
        exists rho_g F T,
          global_env_rel' (fun k => lookup_const cm k <> None) rho_g /\
          forall e_k i,
            Disjoint _ (occurs_free e_k) ((S \\ S') \\ cmap_vars cm) ->
            preord_exp cenv (anf_bound F T) eq_fuel i
              (e_k, rho_g) (C_env |[ e_k ]|, rho_init).
  Proof.
    intros Σ_proc gd cm_acc cm C_env S S' Hcvt
           HΣ_eq Hcm_sub Hcm_sub_final Hcm_complete_proc Hcm_sound_proc
           Hnd_acc Hdis Hcoh_acc rho_init Hglob.
    destruct (global_ctx_correct_strong Σ_proc gd cm_acc cm C_env S S'
                Hcvt HΣ_eq Hcm_sub Hcm_sub_final
                Hcm_complete_proc Hcm_sound_proc Hnd_acc Hdis Hcoh_acc
                rho_init Hglob)
      as [rho_g [F [T [Hglob_g [_ Hpre]]]]].
    exists rho_g, F, T. split; [exact Hglob_g | exact Hpre].
  Qed.

End GlobalBindingsCorrect.


(* ================================================================= *)
(** * Coherence of [cmap] by construction                           *)
(* ================================================================= *)

Section GlobalBindingsCoherence.

  Context (func_tag default_tag : positive)
          (tgm : conId_map)
          (cmap : const_map)
          (Σ : EAst.global_context).

  Context {efl : EEnvFlags}.
  Context (HnoAxioms : has_axioms = false).

  Context (box_dc : dcon)
          (box_tag : dcon_to_tag default_tag box_dc tgm = default_tag).

  Let Hf_src := LambdaBox_resource_fuel default_tag tgm box_dc box_tag.
  Let Ht_src := LambdaBox_resource_trace default_tag tgm box_dc box_tag.

  Local Notation cvt_rel_at cm0 :=
    (@anf_cvt_rel func_tag default_tag tgm cm0).
  Local Notation eval_at Σ0 :=
    (@eval_env_fuel nat Hf_src Ht_src Σ0 box_dc).

  Context (Hglob_term :
    forall k decl body,
      declared_constant Σ k decl ->
      decl.(EAst.cst_body) = Some body ->
      exists src_v f t, eval_at Σ [] body (Val src_v) f t).
  Context (Hglob_fuel_zero :
    forall k decl body src_v f t,
      declared_constant Σ k decl ->
      decl.(EAst.cst_body) = Some body ->
      eval_at Σ [] body (Val src_v) f t ->
      f = 0).

  Context (Hwf_glob : wf_glob Σ).

  Lemma coh_declared_constant_from_in Σ0 k decl :
    EWellformed.wf_glob Σ0 ->
    List.In (k, EAst.ConstantDecl decl) Σ0 ->
    declared_constant Σ0 k decl.
  Proof.
    intros Hwf0 Hin.
    pose proof (EExtends.lookup_env_In efl (k, EAst.ConstantDecl decl) Σ0 Hwf0) as Hiff.
    exact ((proj2 Hiff) Hin).
  Qed.

  Lemma coh_declared_constant_in_map_fst Σ0 k decl :
    EWellformed.wf_glob Σ0 ->
    declared_constant Σ0 k decl ->
    List.In k (map fst Σ0).
  Proof.
    intros Hwf0 Hdecl.
    pose proof (EExtends.lookup_env_In efl (k, EAst.ConstantDecl decl) Σ0 Hwf0) as Hiff.
    exact (in_map fst _ _ ((proj1 Hiff) Hdecl)).
  Qed.

  Lemma coh_declared_constant_cons_neq kn d Σ0 kn' decl :
    kn <> kn' ->
    declared_constant Σ0 kn' decl ->
    declared_constant ((kn, d) :: Σ0) kn' decl.
  Proof.
    intros Hneq Hdecl.
    unfold declared_constant in *.
    simpl. rewrite eq_kername_bool_neq; eauto.
  Qed.

  Lemma coh_declared_constant_cons_inv_neq kn d Σ0 kn' decl :
    kn <> kn' ->
    declared_constant ((kn, d) :: Σ0) kn' decl ->
    declared_constant Σ0 kn' decl.
  Proof.
    intros Hneq Hdecl.
    unfold declared_constant in *.
    simpl in Hdecl. rewrite eq_kername_bool_neq in Hdecl; eauto.
  Qed.

  Lemma coh_suffix_wf prefix Σ0 :
    EWellformed.wf_glob (prefix ++ Σ0) ->
    EWellformed.wf_glob Σ0.
  Proof.
    intros Hwf.
    eapply EExtends.extends_wf_glob.
    - exists prefix. reflexivity.
    - exact Hwf.
  Qed.

  Lemma coh_suffix_extends prefix Σ0 :
    EWellformed.wf_glob (prefix ++ Σ0) ->
    EGlobalEnv.extends Σ0 (prefix ++ Σ0).
  Proof.
    intro Hwf.
    eapply EExtends.extends_prefix_extends.
    - exists prefix. reflexivity.
    - exact Hwf.
  Qed.

  Lemma coh_key_not_in_prefix prefix k decl suffix :
    EWellformed.wf_glob (prefix ++ (k, decl) :: suffix) ->
    ~ List.In k (map fst prefix).
  Proof.
    intros Hwf Hin.
    pose proof (EProgram.wf_glob_fresh _ Hwf) as Hfg.
    apply EnvMap.EnvMap.fresh_globals_iff_NoDup in Hfg.
    rewrite map_app in Hfg. simpl in Hfg.
    assert (Hnotin : ~ List.In k (map fst prefix ++ map fst suffix)).
    { eapply NoDup_remove_2. exact Hfg. }
    apply Hnotin. apply in_or_app. left. exact Hin.
  Qed.

  Lemma coh_key_not_in_suffix prefix k decl suffix :
    EWellformed.wf_glob (prefix ++ (k, decl) :: suffix) ->
    ~ List.In k (map fst suffix).
  Proof.
    intros Hwf Hin.
    pose proof (EProgram.wf_glob_fresh _ Hwf) as Hfg.
    apply EnvMap.EnvMap.fresh_globals_iff_NoDup in Hfg.
    rewrite map_app in Hfg. simpl in Hfg.
    assert (Hnotin : ~ List.In k (map fst prefix ++ map fst suffix)).
    { eapply NoDup_remove_2. exact Hfg. }
    apply Hnotin. apply in_or_app. right. exact Hin.
  Qed.

  Lemma coh_wf_glob_head_const_some_wf Σ0 k body :
    EWellformed.wf_glob ((k, EAst.ConstantDecl {| EAst.cst_body := Some body |}) :: Σ0) ->
    wellformed Σ0 0 body = true.
  Proof.
    intros Hwf0.
    inversion Hwf0 as [| ? ? ? Hwf_tail Hwd Hfresh]; subst.
    simpl in Hwd. exact Hwd.
  Qed.

  Lemma coh_wf_glob_head_const_none_absurd Σ0 k :
    EWellformed.wf_glob ((k, EAst.ConstantDecl {| EAst.cst_body := None |}) :: Σ0) ->
    False.
  Proof.
    intros Hwf0.
    inversion Hwf0 as [| ? ? ? Hwf_tail Hwd Hfresh]; subst.
    simpl in Hwd. rewrite HnoAxioms in Hwd. discriminate.
  Qed.

  Lemma coh_anf_cvt_rel_global_lookup_preserved :
    forall S gd cm_acc cm C_env S' k v,
      anf_cvt_rel_global func_tag default_tag tgm S gd cm_acc cm C_env S' ->
      lookup_const cm_acc k = Some v ->
      ~ List.In k (map fst gd) ->
      lookup_const cm k = Some v.
  Proof.
    intros S gd cm_acc cm C_env S' k v Hcvt.
    induction Hcvt; intros Hlk Hnotin.
    - exact Hlk.
    - simpl in Hnotin.
      assert (Hneq : k <> k0).
      { intro Heq. apply Hnotin. left. symmetry. exact Heq. }
      assert (Hnotin' : ~ List.In k (map fst gd')).
      { intro Hin. apply Hnotin. right. exact Hin. }
      simpl. destruct (eq_kername k k0) eqn:Hkk0.
      { exfalso. apply Hneq. now apply eq_kername_bool_eq in Hkk0. }
      { eapply IHHcvt.
        - simpl. rewrite Hkk0. exact Hlk.
        - exact Hnotin'. }
    - eapply IHHcvt; eauto.
      simpl in Hnotin. intro Hin. apply Hnotin. right. exact Hin.
    - eapply IHHcvt; eauto.
      simpl in Hnotin. intro Hin. apply Hnotin. right. exact Hin.
  Qed.

  Lemma coh_cmap_eval_coherent_lift_head cm Σ_tail k d :
    EWellformed.wf_glob ((k, d) :: Σ_tail) ->
    (forall k0 v0, lookup_const cm k0 = Some v0 ->
       exists decl body,
         declared_constant Σ_tail k0 decl /\
         decl.(EAst.cst_body) = Some body) ->
    @cmap_eval_coherent cm _ Hf_src Ht_src Σ_tail box_dc ->
    @cmap_eval_coherent cm _ Hf_src Ht_src ((k, d) :: Σ_tail) box_dc.
  Proof.
    intros Hwf_cons Hcm_sound_tail Hcoh
           k1 k2 x decl1 body1 decl2 body2 src_v f t
           Hlk1 Hlk2 Hdecl1 Hbody1 Hdecl2 Hbody2 Heval1.
    assert (Hwf_tail : EWellformed.wf_glob Σ_tail).
    { eapply coh_suffix_wf with (prefix := [(k, d)]). exact Hwf_cons. }
    assert (Hext_tail :
      EGlobalEnv.extends Σ_tail ((k, d) :: Σ_tail)).
    { eapply coh_suffix_extends with (prefix := [(k, d)]). exact Hwf_cons. }
    assert (Hnotin_tail : ~ List.In k (map fst Σ_tail)).
    { eapply coh_key_not_in_suffix with (prefix := []) (decl := d). exact Hwf_cons. }
    assert (Hneq1 : k1 <> k).
    { intro Heq. subst k1.
      destruct (Hcm_sound_tail _ _ Hlk1) as [decl [body [Hdecl _]]].
      apply Hnotin_tail.
      eapply coh_declared_constant_in_map_fst; [exact Hwf_tail | exact Hdecl]. }
    assert (Hneq2 : k2 <> k).
    { intro Heq. subst k2.
      destruct (Hcm_sound_tail _ _ Hlk2) as [decl [body [Hdecl _]]].
      apply Hnotin_tail.
      eapply coh_declared_constant_in_map_fst; [exact Hwf_tail | exact Hdecl]. }
    assert (Hdecl1_tail : declared_constant Σ_tail k1 decl1).
    { eapply coh_declared_constant_cons_inv_neq; eauto. }
    assert (Hdecl2_tail : declared_constant Σ_tail k2 decl2).
    { eapply coh_declared_constant_cons_inv_neq; eauto. }
    assert (Hwf_body1_tail : wellformed Σ_tail 0 body1 = true).
    { exact (wf_glob_globals_wf Σ_tail Hwf_tail _ _ _ Hdecl1_tail Hbody1). }
    pose proof (proj1 (@eval_env_fuel_restrict _ _ Hf_src Ht_src
                         ((k, d) :: Σ_tail) box_dc Σ_tail
                         [] body1 (fuel_sem.Val src_v) f t
                         Hwf_tail Hext_tail ltac:(constructor)
                         Hwf_body1_tail Heval1))
      as Heval1_tail.
    destruct (Hcoh _ _ _ _ _ _ _ _ _ _ Hlk1 Hlk2
                    Hdecl1_tail Hbody1 Hdecl2_tail Hbody2 Heval1_tail)
      as [f' [t' Heval2_tail]].
    exists f', t'. eapply eval_env_fuel_extends; eauto.
  Qed.

  Lemma global_ctx_cmap_eval_coherent_strong_by_construction :
    forall (Σ_proc : EAst.global_context) gd cm_acc C_env S S',
      anf_cvt_rel_global func_tag default_tag tgm
        S gd cm_acc cmap C_env S' ->
      Σ = List.rev gd ++ Σ_proc ->
      EWellformed.wf_glob Σ_proc ->
      (forall s v, lookup_const cm_acc s = Some v -> lookup_const cmap s = Some v) ->
      (forall k v, lookup_const cm_acc k = Some v ->
                   exists decl body,
                     declared_constant Σ_proc k decl /\
                     decl.(EAst.cst_body) = Some body) ->
      Disjoint _ (cmap_vars cm_acc) S ->
      @cmap_eval_coherent cm_acc _ Hf_src Ht_src Σ_proc box_dc ->
      @cmap_eval_coherent cmap _ Hf_src Ht_src Σ box_dc.
  Proof.
    intros Σ_proc gd cm_acc C_env S S' Hcvt.
    revert Σ_proc.
    induction Hcvt as
      [ S0 cm0
      | S0 S1 S2 k body gd' cm0 cm' C C_rest v Hbody_cvt Hrest IHrest
      | S0 S0' k gd' cm0 cm' C_rest Hrest IHrest
      | S0 S0' k ind gd' cm0 cm' C_rest Hrest IHrest ];
      intros Σ_proc HΣ_eq Hwf_proc Hcm_sub Hcm_sound_proc Hdis_acc Hcoh_acc.
    - simpl in HΣ_eq. symmetry in HΣ_eq. subst Σ_proc. exact Hcoh_acc.
    - simpl in HΣ_eq.
      assert (Hwf_split : EWellformed.wf_glob
          (List.rev gd' ++ (k, EAst.ConstantDecl {| EAst.cst_body := Some body |}) :: Σ_proc)).
      { replace (List.rev gd' ++ (k, EAst.ConstantDecl {| EAst.cst_body := Some body |}) :: Σ_proc)
          with ((List.rev gd' ++ [(k, EAst.ConstantDecl {| EAst.cst_body := Some body |})]) ++ Σ_proc).
        2:{ rewrite <- app_assoc. simpl. reflexivity. }
        rewrite <- HΣ_eq. exact Hwf_glob. }
      assert (HΣ_rest : Σ = List.rev gd' ++
          ((k, EAst.ConstantDecl {| EAst.cst_body := Some body |}) :: Σ_proc)).
      { replace (List.rev gd' ++
                   ((k, EAst.ConstantDecl {| EAst.cst_body := Some body |}) :: Σ_proc))
          with ((List.rev gd' ++ [(k, EAst.ConstantDecl {| EAst.cst_body := Some body |})]) ++ Σ_proc).
        2:{ rewrite <- app_assoc. simpl. reflexivity. }
        exact HΣ_eq. }
      assert (Hwf_proc1 : EWellformed.wf_glob
          ((k, EAst.ConstantDecl {| EAst.cst_body := Some body |}) :: Σ_proc)).
      { eapply coh_suffix_wf with (prefix := List.rev gd'). exact Hwf_split. }
      assert (Hwf_split_app : EWellformed.wf_glob
          ((List.rev gd' ++ [(k, EAst.ConstantDecl {| EAst.cst_body := Some body |})]) ++ Σ_proc)).
      { replace
          ((List.rev gd' ++ [(k, EAst.ConstantDecl {| EAst.cst_body := Some body |})]) ++ Σ_proc)
          with (List.rev gd' ++ (k, EAst.ConstantDecl {| EAst.cst_body := Some body |}) :: Σ_proc)
          by (rewrite <- app_assoc; simpl; reflexivity).
        exact Hwf_split. }
      assert (Hwf_body_proc : wellformed Σ_proc 0 body = true).
      { eapply coh_wf_glob_head_const_some_wf. exact Hwf_proc1. }
      assert (Hext_proc_small :
        EGlobalEnv.extends Σ_proc ((k, EAst.ConstantDecl {| EAst.cst_body := Some body |}) :: Σ_proc)).
      { eapply coh_suffix_extends with
          (prefix := [(k, EAst.ConstantDecl {| EAst.cst_body := Some body |})]).
        exact Hwf_proc1. }
      assert (Hext_proc_full : EGlobalEnv.extends Σ_proc Σ).
      { rewrite HΣ_eq.
        eapply coh_suffix_extends with
          (prefix := List.rev gd' ++ [(k, EAst.ConstantDecl {| EAst.cst_body := Some body |})]).
        exact Hwf_split_app. }
      assert (Hnotin_proc : ~ List.In k (map fst Σ_proc)).
      { eapply coh_key_not_in_suffix
          with (prefix := List.rev gd')
               (decl := EAst.ConstantDecl {| EAst.cst_body := Some body |}).
        exact Hwf_split. }
      assert (Hnotin_rev_gd' : ~ List.In k (map fst (List.rev gd'))).
      { eapply coh_key_not_in_prefix with
          (decl := EAst.ConstantDecl {| EAst.cst_body := Some body |})
          (suffix := Σ_proc).
        exact Hwf_split. }
      assert (Hnotin_gd' : ~ List.In k (map fst gd')).
      { intro Hin. apply Hnotin_rev_gd'. rewrite map_rev. rewrite <- in_rev. exact Hin. }
      assert (Hlk_cmap_k : lookup_const cm' k = Some v).
      { eapply coh_anf_cvt_rel_global_lookup_preserved with
          (S := S1) (gd := gd') (cm_acc := (k, v) :: cm0) (C_env := C_rest) (S' := S2).
        - exact Hrest.
        - simpl. rewrite eq_kername_refl. reflexivity.
        - exact Hnotin_gd'. }
      assert (Hdis_cm0 : Disjoint _ (cmap_vars cm0) S0).
      { exact Hdis_acc. }
      assert (Hdis_nil : Disjoint _ (FromList []) S0).
      { rewrite FromList_nil. now apply Disjoint_Empty_set_l. }
      assert (Hcons_nil : @env_consistent [] []).
      { intros i j x Hi. rewrite nth_error_nil in Hi. discriminate. }
      assert (Hcmap_nil : @cmap_consistent cm0 _ Hf_src Ht_src Σ_proc box_dc [] []).
      { intros i x k0 decl0 body0 Hnth. rewrite nth_error_nil in Hnth. discriminate. }
      assert (Hcoh_old1 :
        @cmap_eval_coherent cm0 _ Hf_src Ht_src
          ((k, EAst.ConstantDecl {| EAst.cst_body := Some body |}) :: Σ_proc) box_dc).
      { eapply coh_cmap_eval_coherent_lift_head; eauto. }
      assert (Hdecl_cur_full :
        declared_constant Σ k {| EAst.cst_body := Some body |}).
      { eapply coh_declared_constant_from_in; [exact Hwf_glob |].
        rewrite HΣ_rest. apply in_or_app. right. simpl. left. reflexivity. }
      assert (Hcm_sound_proc1 :
        forall k0 v0, lookup_const ((k, v) :: cm0) k0 = Some v0 ->
                      exists decl body0,
                        declared_constant
                          ((k, EAst.ConstantDecl {| EAst.cst_body := Some body |}) :: Σ_proc) k0 decl /\
                        decl.(EAst.cst_body) = Some body0).
      { intros k0 v0 Hlk.
        simpl in Hlk. destruct (eq_kername k0 k) eqn:Hk0k.
        - apply eq_kername_bool_eq in Hk0k. subst k0.
          injection Hlk as <-.
          exists {| EAst.cst_body := Some body |}, body.
          split.
          + unfold declared_constant. simpl. rewrite eq_kername_refl. reflexivity.
          + reflexivity.
        - destruct (Hcm_sound_proc _ _ Hlk) as [decl [body0 [Hdecl0 Hbody0]]].
          exists decl, body0. split.
          + eapply coh_declared_constant_cons_neq; [| exact Hdecl0 ].
            intro Heq. apply (eq_kername_bool_neq_inv Hk0k). symmetry. exact Heq.
          + exact Hbody0. }
      assert (Hcoh_proc1 :
        @cmap_eval_coherent ((k, v) :: cm0) _ Hf_src Ht_src
          ((k, EAst.ConstantDecl {| EAst.cst_body := Some body |}) :: Σ_proc) box_dc).
      { intros k1 k2 x decl1 body1 decl2 body2 src_v f t
               Hlk1 Hlk2 Hdecl1 Hbody1 Hdecl2 Hbody2 Heval1.
        simpl in Hlk1, Hlk2.
        destruct (eq_kername k1 k) eqn:Hk1;
        destruct (eq_kername k2 k) eqn:Hk2.
        - apply eq_kername_bool_eq in Hk1. apply eq_kername_bool_eq in Hk2.
          subst k1 k2. injection Hlk1 as <-.
          unfold declared_constant in Hdecl1, Hdecl2.
          simpl in Hdecl1, Hdecl2.
          rewrite eq_kername_refl in Hdecl1, Hdecl2.
          injection Hdecl1 as <-. injection Hdecl2 as <-.
          rewrite Hbody1 in Hbody2. injection Hbody2 as <-.
          exists f, t. exact Heval1.
        - apply eq_kername_bool_eq in Hk1. subst k1.
          injection Hlk1 as <-.
          unfold declared_constant in Hdecl1.
          simpl in Hdecl1. rewrite eq_kername_refl in Hdecl1.
          injection Hdecl1 as <-.
          simpl in Hbody1. injection Hbody1 as <-.
          assert (Hlk2_tail : lookup_const cm0 k2 = Some v).
          { exact Hlk2. }
          assert (Hdecl2_tail : declared_constant Σ_proc k2 decl2).
          { eapply coh_declared_constant_cons_inv_neq.
            - intro Heq. apply (eq_kername_bool_neq_inv Hk2). symmetry. exact Heq.
            - exact Hdecl2. }
          pose proof (proj1 (@eval_env_fuel_restrict _ _ Hf_src Ht_src
                               ((k, EAst.ConstantDecl {| EAst.cst_body := Some body |}) :: Σ_proc)
                               box_dc Σ_proc
                               [] body (fuel_sem.Val src_v) f t
                               Hwf_proc Hext_proc_small ltac:(constructor)
                               Hwf_body_proc Heval1))
            as Heval1_tail.
          destruct (@anf_cvt_cmap_eval func_tag default_tag tgm cm0 Σ_proc box_dc
                      box_tag Hcoh_acc
                      [] body src_v f t Heval1_tail
                      S0 [] S1 C v k2 decl2 body2
                      Hbody_cvt Hdis_nil Hdis_cm0 Hcons_nil Hcmap_nil
                      Hlk2_tail Hdecl2_tail Hbody2)
            as [f' [t' Heval2_tail]].
          exists f', t'. exact (@eval_env_fuel_extends _ Hf_src Ht_src
                                 ((k, EAst.ConstantDecl {| EAst.cst_body := Some body |}) :: Σ_proc)
                                 box_dc Σ_proc [] body2 (fuel_sem.Val src_v) f' t'
                                 Hext_proc_small Heval2_tail).
        - apply eq_kername_bool_eq in Hk2. subst k2.
          injection Hlk2 as <-.
          unfold declared_constant in Hdecl2.
          simpl in Hdecl2. rewrite eq_kername_refl in Hdecl2.
          injection Hdecl2 as <-.
          simpl in Hbody2. injection Hbody2 as <-.
          assert (Hlk1_tail : lookup_const cm0 k1 = Some v).
          { exact Hlk1. }
          assert (Hdecl1_tail : declared_constant Σ_proc k1 decl1).
          { eapply coh_declared_constant_cons_inv_neq.
            - intro Heq. apply (eq_kername_bool_neq_inv Hk1). symmetry. exact Heq.
            - exact Hdecl1. }
          assert (Hwf_body1_tail : wellformed Σ_proc 0 body1 = true).
          { exact (wf_glob_globals_wf Σ_proc Hwf_proc _ _ _ Hdecl1_tail Hbody1). }
          pose proof (proj1 (@eval_env_fuel_restrict _ _ Hf_src Ht_src
                               ((k, EAst.ConstantDecl {| EAst.cst_body := Some body |}) :: Σ_proc)
                               box_dc Σ_proc
                               [] body1 (fuel_sem.Val src_v) f t
                               Hwf_proc Hext_proc_small ltac:(constructor)
                               Hwf_body1_tail Heval1))
            as Heval1_tail.
          destruct (Hglob_term k {| EAst.cst_body := Some body |} body Hdecl_cur_full eq_refl)
            as [src_v_new [f_new [t_new Heval_new_full]]].
          pose proof (proj1 (@eval_env_fuel_restrict _ _ Hf_src Ht_src
                               Σ box_dc Σ_proc
                               [] body (fuel_sem.Val src_v_new) f_new t_new
                               Hwf_proc Hext_proc_full ltac:(constructor)
                               Hwf_body_proc Heval_new_full))
            as Heval_new_tail.
          destruct (@anf_cvt_cmap_eval func_tag default_tag tgm cm0 Σ_proc box_dc
                      box_tag Hcoh_acc
                      [] body src_v_new f_new t_new Heval_new_tail
                      S0 [] S1 C v k1 decl1 body1
                      Hbody_cvt Hdis_nil Hdis_cm0 Hcons_nil Hcmap_nil
                      Hlk1_tail Hdecl1_tail Hbody1)
            as [f' [t' Heval1_from_new]].
          assert (src_v_new = src_v) by (eapply eval_val_det; eassumption).
          subst src_v_new.
          exists f_new, t_new.
          exact (@eval_env_fuel_extends _ Hf_src Ht_src
                   ((k, EAst.ConstantDecl {| EAst.cst_body := Some body |}) :: Σ_proc)
                   box_dc Σ_proc [] body (fuel_sem.Val src_v) f_new t_new
                   Hext_proc_small Heval_new_tail).
        - assert (Hlk1_tail : lookup_const cm0 k1 = Some x) by exact Hlk1.
          assert (Hlk2_tail : lookup_const cm0 k2 = Some x) by exact Hlk2.
          exact (Hcoh_old1 _ _ _ _ _ _ _ _ _ _ Hlk1_tail Hlk2_tail
                           Hdecl1 Hbody1 Hdecl2 Hbody2 Heval1). }
      assert (Hcm_sub_rest :
        forall s v0, lookup_const ((k, v) :: cm0) s = Some v0 -> lookup_const cm' s = Some v0).
      { intros s v0 Hlk.
        simpl in Hlk. destruct (eq_kername s k) eqn:Hsk.
        - apply eq_kername_bool_eq in Hsk. subst s.
          injection Hlk as <-. exact Hlk_cmap_k.
        - exact (Hcm_sub _ _ Hlk). }
      assert (Hdis_cm1 : Disjoint _ (cmap_vars ((k, v) :: cm0)) S1).
      { constructor. intros z Hc.
        inversion Hc as [? Hzcm HzS1]; subst; clear Hc.
        destruct Hzcm as [s Hlk].
        simpl in Hlk.
        destruct (eq_kername s k) eqn:Hsk.
        + apply eq_kername_bool_eq in Hsk. subst s.
          injection Hlk as <-.
          eapply (anf_cvt_result_not_in_output
                    func_tag default_tag tgm cm0
                    S0 body [] S1 C v Hbody_cvt).
          * rewrite FromList_nil. now apply Disjoint_Empty_set_l.
          * exact Hdis_acc.
          * exact HzS1.
        + eapply Hdis_acc.
          constructor.
          * exists s. exact Hlk.
          * eapply anf_cvt_exp_subset; [exact Hbody_cvt | exact HzS1].
      }
	      eapply IHrest with
	        (Σ_proc := (k, EAst.ConstantDecl {| EAst.cst_body := Some body |}) :: Σ_proc); eauto.
    - simpl in HΣ_eq.
      assert (Hwf_split : EWellformed.wf_glob
          (List.rev gd' ++ (k, EAst.ConstantDecl {| EAst.cst_body := None |}) :: Σ_proc)).
      { replace (List.rev gd' ++ (k, EAst.ConstantDecl {| EAst.cst_body := None |}) :: Σ_proc)
          with ((List.rev gd' ++ [(k, EAst.ConstantDecl {| EAst.cst_body := None |})]) ++ Σ_proc).
        2:{ rewrite <- app_assoc. simpl. reflexivity. }
        rewrite <- HΣ_eq. exact Hwf_glob. }
      assert (Hwf_proc1 : EWellformed.wf_glob
          ((k, EAst.ConstantDecl {| EAst.cst_body := None |}) :: Σ_proc)).
      { eapply coh_suffix_wf with (prefix := List.rev gd'). exact Hwf_split. }
      exfalso. eapply coh_wf_glob_head_const_none_absurd. exact Hwf_proc1.
    - simpl in HΣ_eq.
      assert (Hwf_split : EWellformed.wf_glob
          (List.rev gd' ++ (k, EAst.InductiveDecl ind) :: Σ_proc)).
      { replace (List.rev gd' ++ (k, EAst.InductiveDecl ind) :: Σ_proc)
          with ((List.rev gd' ++ [(k, EAst.InductiveDecl ind)]) ++ Σ_proc).
        2:{ rewrite <- app_assoc. simpl. reflexivity. }
        rewrite <- HΣ_eq. exact Hwf_glob. }
      assert (HΣ_rest : Σ = List.rev gd' ++ ((k, EAst.InductiveDecl ind) :: Σ_proc)).
      { replace (List.rev gd' ++ ((k, EAst.InductiveDecl ind) :: Σ_proc))
          with ((List.rev gd' ++ [(k, EAst.InductiveDecl ind)]) ++ Σ_proc).
        2:{ rewrite <- app_assoc. simpl. reflexivity. }
        exact HΣ_eq. }
      assert (Hwf_proc1 : EWellformed.wf_glob ((k, EAst.InductiveDecl ind) :: Σ_proc)).
      { eapply coh_suffix_wf with (prefix := List.rev gd'). exact Hwf_split. }
      assert (Hcm_sound_proc1 :
        forall k0 v0, lookup_const cm0 k0 = Some v0 ->
                      exists decl body0,
                        declared_constant ((k, EAst.InductiveDecl ind) :: Σ_proc) k0 decl /\
                        decl.(EAst.cst_body) = Some body0).
      { intros k0 v0 Hlk.
        destruct (Hcm_sound_proc _ _ Hlk) as [decl [body0 [Hdecl0 Hbody0]]].
        assert (Hneq : k <> k0).
        { intro Heq. subst k0.
          assert (Hnotin : ~ List.In k (map fst Σ_proc)).
          { eapply coh_key_not_in_suffix with
              (prefix := List.rev gd')
              (decl := EAst.InductiveDecl ind).
            exact Hwf_split. }
          apply Hnotin.
          eapply coh_declared_constant_in_map_fst; [exact Hwf_proc | exact Hdecl0]. }
        exists decl, body0. split.
        - eapply coh_declared_constant_cons_neq; [exact Hneq | exact Hdecl0].
        - exact Hbody0. }
      assert (Hcoh_proc1 :
        @cmap_eval_coherent cm0 _ Hf_src Ht_src
          ((k, EAst.InductiveDecl ind) :: Σ_proc) box_dc).
      { eapply coh_cmap_eval_coherent_lift_head; eauto. }
      eapply IHrest with (Σ_proc := (k, EAst.InductiveDecl ind) :: Σ_proc); eauto.
  Qed.

  Lemma global_ctx_cmap_eval_coherent_top_by_construction :
    forall C_env S S',
      anf_cvt_rel_global func_tag default_tag tgm
        S (List.rev Σ) [] cmap C_env S' ->
      @cmap_eval_coherent cmap _ Hf_src Ht_src Σ box_dc.
  Proof.
    intros C_env S S' Hcvt.
    assert (HΣ_top : Σ = List.rev (List.rev Σ) ++ []).
    { rewrite rev_involutive. rewrite app_nil_r. reflexivity. }
    assert (Hcm_acc_sub :
      forall s v, lookup_const ([] : const_map) s = Some v -> lookup_const cmap s = Some v).
    { intros s v Hlk. discriminate. }
    assert (Hcm_acc_sound :
      forall k v, lookup_const ([] : const_map) k = Some v ->
                  exists decl body,
                    declared_constant ([] : EAst.global_context) k decl /\
                    decl.(EAst.cst_body) = Some body).
    { intros k v Hlk. discriminate. }
	    assert (Hcoh_empty :
	      @cmap_eval_coherent ([] : const_map) _ Hf_src Ht_src ([] : EAst.global_context) box_dc).
	    { intros k1 k2 x decl1 body1 decl2 body2 src_v f t Hlk1. discriminate. }
	    assert (Hdis_empty : Disjoint _ (cmap_vars ([] : const_map)) S).
	    { constructor. intros z Hc.
	      inversion Hc as [? Hz _]; subst; clear Hc.
	      destruct Hz as [k Hlk]. discriminate. }
    eapply global_ctx_cmap_eval_coherent_strong_by_construction
      with (Σ_proc := []) (gd := List.rev Σ) (cm_acc := []) (C_env := C_env)
           (S := S) (S' := S').
    - exact Hcvt.
    - exact HΣ_top.
    - constructor.
    - exact Hcm_acc_sub.
    - exact Hcm_acc_sound.
    - exact Hdis_empty.
    - exact Hcoh_empty.
  Qed.

End GlobalBindingsCoherence.


(* ================================================================= *)
(** * Top-level packaging for global binding contexts                 *)
(* ================================================================= *)

Section GlobalBindingsTopLevel.

  Context (func_tag kon_tag default_tag default_itag : positive)
          (tgm : conId_map)
          (cmap : const_map)
          (cenv : ctor_env)
          (Σ : EAst.global_context).

  Context {efl : EEnvFlags}.
  Context (HnoAxioms : has_axioms = false).

  Context (dcon_to_tag_inj :
    forall dc dc',
      dcon_to_tag default_tag dc tgm = dcon_to_tag default_tag dc' tgm -> dc = dc').

  Context (box_dc : dcon)
          (box_tag : dcon_to_tag default_tag box_dc tgm = default_tag).

  Context (cenv_case_consistent : forall P ctag, caseConsistent cenv P ctag).
  Let Hf_src := LambdaBox_resource_fuel default_tag tgm box_dc box_tag.
  Let Ht_src := LambdaBox_resource_trace default_tag tgm box_dc box_tag.

  Let global_env_rel' :=
    @global_env_rel func_tag default_tag tgm cmap nat Hf_src Ht_src Σ box_dc.

  Let src_eval := @eval_env_fuel nat Hf_src Ht_src Σ box_dc.

  Context (Hglob_term :
    forall k decl body,
      declared_constant Σ k decl ->
      decl.(EAst.cst_body) = Some body ->
      exists src_v f t, src_eval [] body (Val src_v) f t).
  Context (Hglob_fuel_zero :
    forall k decl body src_v f t,
      declared_constant Σ k decl ->
      decl.(EAst.cst_body) = Some body ->
      src_eval [] body (Val src_v) f t ->
      f = 0).

  Context (Hglob_wf :
    forall k decl body,
      declared_constant Σ k decl ->
      decl.(EAst.cst_body) = Some body ->
      wellformed Σ 0 body = true).

  Context (prim_map : M.t primitive)
          (prims : list (primitive * positive)).
  Context (Hwf_glob : wf_glob Σ).
  Context (HnoVar : has_tVar = false)
          (HnoEvar : has_tEvar = false)
          (HnoCoFix : has_tCoFix = false)
          (HnoLazy : has_tLazy_Force = false)
          (Hblocks : cstr_as_blocks = true)
          (HnoArray : has_primarray = false).
  Context (no_prims : forall s, find_prim prims s = None).

  Lemma global_ctx_cmap_eval_coherent_top :
    forall C_env S S',
      anf_cvt_rel_global func_tag default_tag tgm
        S (List.rev Σ) [] cmap C_env S' ->
      @cmap_eval_coherent cmap _ Hf_src Ht_src Σ box_dc.
  Proof.
    intros C_env S S' Hcvt.
    exact (@global_ctx_cmap_eval_coherent_top_by_construction
             func_tag default_tag tgm cmap Σ efl HnoAxioms
             box_dc box_tag Hglob_term Hglob_fuel_zero Hwf_glob
             C_env S S' Hcvt).
  Qed.

  Lemma global_env_rel_empty_acc rho :
    global_env_rel' (fun k => lookup_const ([] : const_map) k <> None) rho.
  Proof.
    intros k v Hk. simpl in Hk. contradiction.
  Qed.

  (** Top-level form of [global_ctx_correct]:
      start from the initial call to [anf_cvt_rel_global], with
      an empty accumulator and the whole global context still to process.

      Since [Σ = rev (rev Σ) ++ []], the processed suffix is [[]].
      The initial global-domain assumption is empty, so it holds for any
      starting environment [rho_init]. *)
  Lemma global_ctx_correct_init :
    forall C_env S S',
      anf_cvt_rel_global func_tag default_tag tgm
        S (List.rev Σ) [] cmap C_env S' ->
      forall rho_init,
        exists rho_g F T,
          global_env_rel' (fun k => lookup_const cmap k <> None) rho_g /\
          forall e_k i,
            Disjoint _ (occurs_free e_k) ((S \\ S') \\ cmap_vars cmap) ->
            preord_exp cenv (anf_bound F T) eq_fuel i
              (e_k, rho_g) (C_env |[ e_k ]|, rho_init).
  Proof.
    intros C_env S S' Hcvt rho_init.
    pose proof (@anf_cvt_rel_global_complete_top
                  func_tag default_tag tgm efl Σ Hwf_glob HnoAxioms
                  S cmap C_env S' Hcvt)
      as Hcmap_complete.
    pose proof (@anf_cvt_rel_global_sound_top
                  func_tag default_tag tgm efl Σ Hwf_glob
                  S cmap C_env S' Hcvt)
      as Hcmap_sound.
    pose proof (@anf_cvt_rel_global_nodup_keys_top
                  func_tag default_tag tgm efl Σ Hwf_glob HnoAxioms
                  S cmap C_env S' Hcvt)
      as Hcmap_nodup_keys.
    pose proof (global_ctx_cmap_eval_coherent_top C_env S S' Hcvt)
      as Hcmap_eval_coherent.
    assert (HΣ_top : Σ = List.rev (List.rev Σ) ++ []).
    { rewrite rev_involutive. rewrite app_nil_r. reflexivity. }
    assert (Hcm_acc_sub :
      forall s v, lookup_const ([] : const_map) s = Some v -> lookup_const cmap s = Some v).
    { intros s v Hlk. discriminate. }
    assert (Hcm_acc_complete :
      forall s d, lookup_constant ([] : EAst.global_context) s = Some d ->
                  lookup_const ([] : const_map) s <> None).
    { intros s d Hlk. discriminate. }
    assert (Hcm_acc_sound :
      forall k v, lookup_const ([] : const_map) k = Some v ->
                  exists decl body,
                    declared_constant ([] : EAst.global_context) k decl /\
                    decl.(EAst.cst_body) = Some body).
    { intros k v Hlk. discriminate. }
	    assert (Hnd_empty : NoDup (map fst ([] : const_map))).
	    { constructor. }
	    assert (Hdis_empty : Disjoint _ (cmap_vars ([] : const_map)) S).
	    { constructor. intros z Hc.
	      inversion Hc as [? Hz _]; subst; clear Hc.
	      destruct Hz as [k Hlk]. discriminate. }
    assert (Hcoh_empty :
      @cmap_eval_coherent ([] : const_map) _ Hf_src Ht_src ([] : EAst.global_context) box_dc).
    { intros k1 k2 x decl1 body1 decl2 body2 src_v f t Hlk1. discriminate. }
    destruct (@global_ctx_correct
                func_tag kon_tag default_tag default_itag
                tgm cmap cenv Σ efl
                HnoAxioms
                dcon_to_tag_inj
                box_dc box_tag
                cenv_case_consistent Hcmap_eval_coherent
                Hglob_term Hglob_fuel_zero Hglob_wf
                prim_map prims Hwf_glob
                HnoVar HnoEvar HnoCoFix HnoLazy Hblocks HnoArray
                no_prims Hcmap_complete Hcmap_sound Hcmap_nodup_keys
                [] (List.rev Σ) [] cmap C_env S S'
                Hcvt HΣ_top Hcm_acc_sub (fun s v Hlk => Hlk)
                Hcm_acc_complete Hcm_acc_sound Hnd_empty Hdis_empty
                Hcoh_empty rho_init
                (global_env_rel_empty_acc rho_init))
      as [rho_g [F [T [Hglob_g Hpre]]]].
    exists rho_g, F, T. split; [exact Hglob_g | exact Hpre].
  Qed.

  (** Common top-level corollary: the relational run starts from [[]]
      and produces the section's final [cmap]. *)
  Lemma global_ctx_correct_top :
    forall C_env S S',
      anf_cvt_rel_global func_tag default_tag tgm
        S (List.rev Σ) [] cmap C_env S' ->
      forall rho_init,
        exists rho_g F T,
          global_env_rel' (fun k => lookup_const cmap k <> None) rho_g /\
          forall e_k i,
            Disjoint _ (occurs_free e_k) ((S \\ S') \\ cmap_vars cmap) ->
            preord_exp cenv (anf_bound F T) eq_fuel i
              (e_k, rho_g) (C_env |[ e_k ]|, rho_init).
  Proof.
    intros C_env S S' Hcvt rho_init.
    eapply global_ctx_correct_init; eauto.
  Qed.

End GlobalBindingsTopLevel.
