(* Top-level correctness theorems for ANF conversion from LambdaBox. *)

From Stdlib Require Import ZArith.ZArith Lists.List micromega.Lia Arith
     Ensembles Relations.Relation_Definitions.
From MetaRocq.Erasure Require Import
  EAst EAstUtils EGlobalEnv EWellformed EPrimitive.
From MetaRocq.Common Require Import BasicAst Kernames.
From compcert Require Import lib.Maps lib.Coqlib.
From ExtLib Require Import Structures.Monads.
From CertiRocq.Common Require Import AstCommon compM.
From CertiRocq Require Import Pipeline_utils.
From CertiRocq.LambdaANF Require Import
  cps cps_show eval ctx logical_relations
  List_util algebra alpha_conv functions Ensembles_util
  tactics identifiers bounds cps_util rename set_util stemctx.
From MetaRocq.Utils Require Import All_Forall.
From CertiRocq.LambdaBox_to_LambdaANF Require Import
  common ANF fuel_sem wf anf_corresp anf_util anf_correct anf_global
  anf_divergence.

Import ListNotations.
Import Monad.MonadNotation.
Open Scope monad_scope.

Section Refinement.

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

  Let anf_val_rel' :=
    @anf_val_rel func_tag default_tag tgm cmap nat Hf_src Ht_src Σ box_dc.
  Let anf_env_rel0 :=
    @anf_env_rel func_tag default_tag tgm cmap nat Hf_src Ht_src Σ box_dc.

  Let global_env_rel' :=
    @global_env_rel func_tag default_tag tgm cmap nat Hf_src Ht_src Σ box_dc.

  Let src_eval := @eval_env_fuel nat Hf_src Ht_src Σ box_dc.
  Let src_diverge := @fuel_sem.diverge nat Hf_src Ht_src Σ box_dc.
  Let src_diverge_not_stuck := @fuel_sem.diverge_not_stuck nat Hf_src Ht_src Σ box_dc.
  Let cmap_consistent' :=
    @cmap_consistent cmap nat Hf_src Ht_src Σ box_dc.

  Lemma anf_bound_post_upper_bound f_src t_src :
    post_upper_bound (anf_bound f_src t_src).
  Proof.
    intros e1 rho1 e2 rho2.
    exists (fun cin => cin).
    intros cin1 cin2 cout1 cout2 Hbound.
    unfold anf_bound in Hbound. simpl in Hbound.
    destruct Hbound as [Hlb _].
    exists (cin2 - cin1).
    symmetry.
    apply Nat.sub_add.
    lia.
  Qed.

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

  Fixpoint value_ref' (v1 : fuel_sem.value) (v2 : val) : Prop :=
    let fix Forall2_aux vs1 vs2 :=
        match vs1, vs2 with
        | [], [] => True
        | v1' :: vs1', v2' :: vs2' =>
          value_ref' v1' v2' /\ Forall2_aux vs1' vs2'
        | _, _ => False
        end
    in
    match v1, v2 with
    | fuel_sem.Con_v c1 vs1, Vconstr c2 vs2 =>
      dcon_to_tag default_tag c1 tgm = c2 /\ Forall2_aux vs1 vs2
    | fuel_sem.Clos_v _ _ _, Vfun _ _ _ => True
    | fuel_sem.ClosFix_v _ _ _, Vfun _ _ _ => True
    | _, _ => False
    end.

  Definition value_ref (v1 : fuel_sem.value) (v2 : val) : Prop :=
    match v1, v2 with
    | fuel_sem.Con_v c1 vs1, Vconstr c2 vs2 =>
      dcon_to_tag default_tag c1 tgm = c2 /\ Forall2 value_ref' vs1 vs2
    | fuel_sem.Clos_v _ _ _, Vfun _ _ _ => True
    | fuel_sem.ClosFix_v _ _ _, Vfun _ _ _ => True
    | _, _ => False
    end.

  Lemma value_ref_eq v1 v2 :
    value_ref' v1 v2 <-> value_ref v1 v2.
  Proof.
    induction v1; try easy.

    destruct v2; simpl; try easy.

    revert l0. induction l; intros l'.
    - split; intros [H1 H2]. split; eauto; destruct l'; eauto.
      inv H2. split; eauto.
    - split; intros [H1 H2].
      + split; eauto. destruct l'; inv H2.
        constructor; eauto. eapply IHl. split; eauto.
      + split; eauto. destruct l'; inv H2.
        constructor; eauto. eapply IHl. split; eauto.
  Qed.

  Definition refines (M : nat) (e_src : EAst.term) (e_tgt : exp) : Prop :=
    forall (v_src : fuel_sem.value) (f_src t_src : nat),
      src_eval [] e_src (Val v_src) f_src t_src ->
      exists (v_tgt : val) (c_tgt : nat),
        bstep_fuel cenv (M.empty val) e_tgt c_tgt (Res v_tgt) tt /\
        (c_tgt <= t_src + M)%nat /\
        value_ref v_src v_tgt.

  Definition anf_rel_top (e : EAst.term) (Sg : Ensemble var) (e_tgt : exp) :=
    exists Sg' S' C_env C r,
      anf_cvt_rel_global func_tag default_tag tgm
        Sg (List.rev Σ) [] cmap C_env Sg' /\
      anf_cvt_rel func_tag default_tag tgm cmap
        Sg' e [] S' C r /\
      e_tgt = C_env |[ C |[ Ehalt r ]| ]|.

  Lemma anf_val_comp k v1 v2 v3 :
    anf_val_rel' v1 v2 ->
    preord_val cenv eq_fuel k v2 v3 ->
    value_ref v1 v3.
  Proof.
    revert v2 v3.
    induction v1 using fuel_sem.value_ind'; intros v2 v3 Hval Hpre; inv Hval.
    - rewrite preord_val_eq in Hpre.
      destruct v3; try contradiction. inv Hpre.
      simpl. split. reflexivity.

      revert l vs' H2 H1.
      induction H; intros.
      + inv H2. inv H1. constructor.
      + inv H2. inv H1. constructor; eauto.
        eapply value_ref_eq. eauto.
    - rewrite preord_val_eq in Hpre.
      destruct v3; try contradiction.
      simpl. exact I.
    - rewrite preord_val_eq in Hpre.
      destruct v3; try contradiction.
      simpl. exact I.
  Qed.

  Theorem anf_correct_top_explicit e Sg Sg' S' C_env C r :
    wellformed Σ 0 e = true ->
    anf_cvt_rel_global func_tag default_tag tgm
      Sg (List.rev Σ) [] cmap C_env Sg' ->
    anf_cvt_rel func_tag default_tag tgm cmap
      Sg' e [] S' C r ->
    exists M, refines M e (C_env |[ C |[ Ehalt r ]| ]|).
  Proof.
    intros Hwf Hglob_cvt Hmain_cvt.
    pose proof (@anf_cvt_rel_global_complete_top
                  func_tag default_tag tgm efl Σ Hwf_glob HnoAxioms
                  Sg cmap C_env Sg' Hglob_cvt)
      as Hcmap_complete.
    pose proof (@anf_cvt_rel_global_sound_top
                  func_tag default_tag tgm efl Σ Hwf_glob
                  Sg cmap C_env Sg' Hglob_cvt)
      as Hcmap_sound.
    pose proof (@anf_cvt_rel_global_nodup_keys_top
                  func_tag default_tag tgm efl Σ Hwf_glob HnoAxioms
                  Sg cmap C_env Sg' Hglob_cvt)
      as Hcmap_nodup_keys.
    pose proof (@global_ctx_cmap_eval_coherent_top
                  func_tag default_tag tgm cmap Σ efl HnoAxioms
                  box_dc box_tag Hglob_term Hglob_fuel_zero Hwf_glob
                  C_env Sg Sg' Hglob_cvt)
      as Hcmap_eval_coherent.
    pose (val_rel_exists :=
      @anf_val_rel_exists func_tag default_tag prim_map tgm prims cmap
        _ Σ box_dc nat Hf_src Ht_src
        Hglob_term Hwf_glob
        HnoVar HnoEvar HnoCoFix HnoLazy Hblocks HnoArray
        no_prims Hcmap_complete Hcmap_sound Hcmap_nodup_keys Hcmap_eval_coherent).
    destruct (@global_ctx_correct_top
                func_tag kon_tag default_tag default_itag
                tgm cmap cenv Σ efl
                HnoAxioms
                dcon_to_tag_inj
                box_dc box_tag
                cenv_case_consistent
                Hglob_term Hglob_fuel_zero Hglob_wf
                prim_map prims Hwf_glob
                HnoVar HnoEvar HnoCoFix HnoLazy Hblocks HnoArray
                no_prims
                C_env Sg Sg'
                Hglob_cvt (M.empty val))
      as [rho_g [F_glob [T_glob [Hglob_rho Hpre_glob]]]].
    exists (T_glob + 1).
    intros src_v f t Heval.

    pose proof (@anf_cvt_correct
                  func_tag default_tag default_itag
                  tgm cmap cenv Σ efl
                  dcon_to_tag_inj
                  box_dc box_tag
                  cenv_case_consistent Hcmap_eval_coherent
                  Hglob_term Hglob_fuel_zero Hglob_wf val_rel_exists
                  [] e (Val src_v) f t Heval)
      as Hcorr.
    unfold anf_cvt_correct_exp in Hcorr.

    assert (Hwf_nil : well_formed_env Σ []) by constructor.
    assert (Hcons_nil : env_consistent [] []).
    { intros i j y Hi. destruct i; discriminate. }
    assert (Hcmap_nil : cmap_consistent' [] []).
    { intros i x k decl body Hi. destruct i; discriminate. }
    assert (Hdis_nil : Disjoint _ (FromList []) Sg').
    { rewrite FromList_nil. now apply Disjoint_Empty_set_l. }
	    assert (Hdis_main : Disjoint _ (cmap_vars cmap) Sg').
	    { eapply anf_cvt_global_disjoint_acc.
	      - exact Hglob_cvt.
	      - constructor. intros z Hc.
	        inversion Hc as [? Hz _]; subst; clear Hc.
	        destruct Hz as [k Hlk]. discriminate. }
    assert (Henv_nil : anf_env_rel0 [] [] rho_g) by constructor.
    assert (Hglob_main : global_env_rel' (kn_deps e) rho_g).
    { intros k v Hdep Hlk.
      eapply Hglob_rho.
      - intro Hnone. rewrite Hlk in Hnone. discriminate.
      - exact Hlk. }

    specialize (Hcorr rho_g [] C r Sg' S' 1%nat
                  Hwf_nil Hwf Hcons_nil Hcmap_nil
                  Hdis_nil Hdis_main Henv_nil Hglob_main Hmain_cvt).

    assert (Hdis_ehalt :
      Disjoint _ (occurs_free (Ehalt r)) ((Sg' \\ S') \\ [set r])).
    { rewrite occurs_free_Ehalt.
      eapply Disjoint_Singleton_l.
      intro Hin.
      inv Hin.
      match goal with
      | [ Hnot : ~ _ \in [set _] |- _ ] => now apply Hnot; constructor
      end. }

    specialize (Hcorr (Ehalt r) Hdis_ehalt).
    destruct Hcorr as [Hterm _].

    assert (Hwf_src_v : well_formed_val Σ src_v).
    { eapply eval_preserves_wf; [exact Hglob_wf | exact Hwf_nil | exact Hwf | exact Heval]. }
    destruct (val_rel_exists src_v Hwf_src_v) as [v_anf Hrel_anf].
    specialize (Hterm src_v v_anf eq_refl Hrel_anf).

    assert (Hctx_main0 :
      occurs_free_ctx C \subset FromList [] :|: (Sg' \\ S') :|: cmap_vars cmap).
    { exact (@anf_cvt_occurs_free_ctx_exp
               func_tag default_tag tgm cmap Σ box_dc box_tag
               Sg' e [] S' C r Hmain_cvt Hdis_nil Hdis_main). }
    assert (Hctx_main :
      occurs_free_ctx C \subset (Sg' \\ S') :|: cmap_vars cmap).
    { rewrite FromList_nil, Union_Empty_set_neut_l in Hctx_main0.
      exact Hctx_main0. }

    assert (Hr_not_old_non_cmap : ~ r \in ((Sg \\ Sg') \\ cmap_vars cmap)).
    { intro Hin_old.
      destruct (@anf_cvt_result_in_consumed
                  func_tag default_tag tgm cmap
                  Sg' e [] S' C r Hmain_cvt)
        as [Hin_vn | [Hin_s | Hin_cm]].
      - rewrite FromList_nil in Hin_vn. contradiction.
      - exact ((proj2 (proj1 Hin_old)) Hin_s).
      - exact ((proj2 Hin_old) Hin_cm). }

    assert (Hdis_cont :
      Disjoint _ (occurs_free (C |[ Ehalt r ]|)) ((Sg \\ Sg') \\ cmap_vars cmap)).
	    { eapply Disjoint_Included_l.
	      - eapply occurs_free_ctx_app.
	      - eapply Union_Disjoint_l.
	        + eapply Disjoint_Included_l.
	          * exact Hctx_main.
	          * eapply Union_Disjoint_l.
	            -- constructor. intros z Hz.
	               inversion Hz as [? Hleft Hright]; subst; clear Hz.
	               exact ((proj2 (proj1 Hright)) (proj1 Hleft)).
	            -- constructor. intros z Hz.
	               inversion Hz as [? Hleft Hright]; subst; clear Hz.
	               exact ((proj2 Hright) Hleft).
	        + eapply Disjoint_Included_l.
	          * rewrite occurs_free_Ehalt. eapply Setminus_Included.
	          * eapply Disjoint_Singleton_l. exact Hr_not_old_non_cmap. }

	    assert (Hpre_full :
	      preord_exp cenv (comp (anf_bound f t) (anf_bound F_glob T_glob))
	        eq_fuel 1
	        (Ehalt r, M.set r v_anf rho_g)
	        (C_env |[ C |[ Ehalt r ]| ]|, M.empty val)).
	    { eapply preord_exp_trans; [tci | exact eq_fuel_idemp | | ].
	      - exact Hterm.
	      - intros m. exact (Hpre_glob (C |[ Ehalt r ]|) m Hdis_cont). }

	    assert (Hehalt :
	      bstep_fuel cenv (M.set r v_anf rho_g) (Ehalt r)
	        (<0> <+> (<1> (Ehalt r))) (Res v_anf) (<0> <+> (<1> (Ehalt r)))).
    { econstructor 2. econstructor. rewrite M.gss. reflexivity. }
	    assert (Hle_halt : (to_nat (<0> <+> (<1> (Ehalt r))) <= 1)%nat).
	    { simpl. unfold algebra.one, one_i. simpl. lia. }

	    destruct (Hpre_full (Res v_anf) (<0> <+> (<1> (Ehalt r))) (<0> <+> (<1> (Ehalt r)))
	               Hle_halt Hehalt)
	      as [res_fin [c_fin [cout_fin [Hstep_fin [Hbound Hres_fin]]]]].
	    destruct res_fin; try contradiction.
	    destruct Hbound as [mid_cfg [Hbound_main Hbound_glob]].
	    destruct mid_cfg as [[[e_mid rho_mid] c_mid] t_mid].
	    unfold anf_bound in Hbound_main, Hbound_glob.
	    simpl in Hbound_main, Hbound_glob.
	    destruct cout_fin.

	    exists v, c_fin. split; [exact Hstep_fin |]. split.
	    - lia.
	    - eapply anf_val_comp; eauto.
  Qed.

  Theorem anf_correct_top e Sg e_tgt :
    wellformed Σ 0 e = true ->
    anf_rel_top e Sg e_tgt ->
    exists M, refines M e e_tgt.
  Proof.
    intros Hwf [Sg' [S' [C_env [C [r [Hglob [Hmain ->]]]]]]].
    eapply anf_correct_top_explicit; eauto.
  Qed.

  Theorem anf_divergence_top_explicit e Sg Sg' S' C_env C r :
    wellformed Σ 0 e = true ->
    anf_cvt_rel_global func_tag default_tag tgm
      Sg (List.rev Σ) [] cmap C_env Sg' ->
    anf_cvt_rel func_tag default_tag tgm cmap
      Sg' e [] S' C r ->
    src_diverge [] e ->
    eval.diverge cenv (M.empty val) (C_env |[ C |[ Ehalt r ]| ]|).
  Proof.
    intros Hwf Hglob_cvt Hmain_cvt Hdiv_src.
    pose proof (@anf_cvt_rel_global_complete_top
                  func_tag default_tag tgm efl Σ Hwf_glob HnoAxioms
                  Sg cmap C_env Sg' Hglob_cvt)
      as Hcmap_complete.
    pose proof (@anf_cvt_rel_global_sound_top
                  func_tag default_tag tgm efl Σ Hwf_glob
                  Sg cmap C_env Sg' Hglob_cvt)
      as Hcmap_sound.
    pose proof (@anf_cvt_rel_global_nodup_keys_top
                  func_tag default_tag tgm efl Σ Hwf_glob HnoAxioms
                  Sg cmap C_env Sg' Hglob_cvt)
      as Hcmap_nodup_keys.
    pose proof (@global_ctx_cmap_eval_coherent_top
                  func_tag default_tag tgm cmap Σ efl HnoAxioms
                  box_dc box_tag Hglob_term Hglob_fuel_zero Hwf_glob
                  C_env Sg Sg' Hglob_cvt)
      as Hcmap_eval_coherent.
    pose (val_rel_exists :=
      @anf_val_rel_exists func_tag default_tag prim_map tgm prims cmap
        _ Σ box_dc nat Hf_src Ht_src
        Hglob_term Hwf_glob
        HnoVar HnoEvar HnoCoFix HnoLazy Hblocks HnoArray
        no_prims Hcmap_complete Hcmap_sound Hcmap_nodup_keys Hcmap_eval_coherent).
    destruct (@global_ctx_correct_top
                func_tag kon_tag default_tag default_itag
                tgm cmap cenv Σ efl
                HnoAxioms
                dcon_to_tag_inj
                box_dc box_tag
                cenv_case_consistent
                Hglob_term Hglob_fuel_zero Hglob_wf
                prim_map prims Hwf_glob
                HnoVar HnoEvar HnoCoFix HnoLazy Hblocks HnoArray
                no_prims
                C_env Sg Sg'
                Hglob_cvt (M.empty val))
      as [rho_g [F_glob [T_glob [Hglob_rho Hpre_glob]]]].

    assert (Hwf_nil : well_formed_env Σ []) by constructor.
    assert (Hcons_nil : env_consistent [] []).
    { intros i j y Hi. destruct i; discriminate. }
    assert (Hcmap_nil : cmap_consistent' [] []).
    { intros i x k decl body Hi. destruct i; discriminate. }
    assert (Hdis_nil : Disjoint _ (FromList []) Sg').
    { rewrite FromList_nil. now apply Disjoint_Empty_set_l. }
    assert (Hdis_main : Disjoint _ (cmap_vars cmap) Sg').
    { eapply anf_cvt_global_disjoint_acc.
      - exact Hglob_cvt.
      - constructor. intros z Hc.
        inversion Hc as [? Hz _]; subst; clear Hc.
        destruct Hz as [k Hlk]. discriminate. }
    assert (Henv_nil : anf_env_rel0 [] [] rho_g) by constructor.
    assert (Hglob_main : global_env_rel' (kn_deps e) rho_g).
    { intros k v Hdep Hlk.
      eapply Hglob_rho.
      - intro Hnone. rewrite Hlk in Hnone. discriminate.
      - exact Hlk. }

    assert (Hdis_ehalt :
      Disjoint _ (occurs_free (Ehalt r)) ((Sg' \\ S') \\ [set r])).
    { rewrite occurs_free_Ehalt.
      eapply Disjoint_Singleton_l.
      intro Hin.
      inv Hin.
      match goal with
      | [ Hnot : ~ _ \in [set _] |- _ ] => now apply Hnot; constructor
      end. }

    assert (Hmain_div : eval.diverge cenv rho_g (C |[ Ehalt r ]|)).
    { intros cin.
      destruct (Hdiv_src cin) as [t Hoot].
      pose proof (@anf_cvt_correct_oot_lower_bound
                    func_tag default_tag default_itag
                    tgm cmap cenv Σ efl
                    dcon_to_tag_inj
                    box_dc box_tag
                    cenv_case_consistent Hcmap_eval_coherent
                    Hglob_term Hglob_fuel_zero Hglob_wf val_rel_exists
                    [] e cin t Hoot)
        as Hcorr_oot.
      unfold anf_cvt_correct_oot_lower_bound_goal in Hcorr_oot.
      specialize (Hcorr_oot rho_g [] C r Sg' S'
                    Hwf_nil Hwf Hcons_nil Hcmap_nil
                    Hdis_nil Hdis_main Henv_nil Hglob_main Hmain_cvt
                    (Ehalt r) Hdis_ehalt).
      specialize (Hcorr_oot (src_diverge_not_stuck [] e Hdiv_src)).
      destruct Hcorr_oot as [c [Hle Hbsf]].
      destruct (Nat.le_exists_sub _ _ Hle) as [d Hd].
      assert (Hc_eq : c = d + cin) by lia.
      rewrite Hc_eq in Hbsf.
      eapply bstep_fuel_OOT_monotonic in Hbsf.
      destruct Hbsf as [cout' [c' [Hbsf _]]].
      exact (ex_intro _ cout' Hbsf). }

    assert (Hctx_main0 :
      occurs_free_ctx C \subset FromList [] :|: (Sg' \\ S') :|: cmap_vars cmap).
    { exact (@anf_cvt_occurs_free_ctx_exp
               func_tag default_tag tgm cmap Σ box_dc box_tag
               Sg' e [] S' C r Hmain_cvt Hdis_nil Hdis_main). }
    assert (Hctx_main :
      occurs_free_ctx C \subset (Sg' \\ S') :|: cmap_vars cmap).
    { rewrite FromList_nil, Union_Empty_set_neut_l in Hctx_main0.
      exact Hctx_main0. }

    assert (Hr_not_old_non_cmap : ~ r \in ((Sg \\ Sg') \\ cmap_vars cmap)).
    { intro Hin_old.
      destruct (@anf_cvt_result_in_consumed
                  func_tag default_tag tgm cmap
                  Sg' e [] S' C r Hmain_cvt)
        as [Hin_vn | [Hin_s | Hin_cm]].
      - rewrite FromList_nil in Hin_vn. contradiction.
      - exact ((proj2 (proj1 Hin_old)) Hin_s).
      - exact ((proj2 Hin_old) Hin_cm). }

    assert (Hdis_cont :
      Disjoint _ (occurs_free (C |[ Ehalt r ]|)) ((Sg \\ Sg') \\ cmap_vars cmap)).
    { eapply Disjoint_Included_l.
      - eapply occurs_free_ctx_app.
      - eapply Union_Disjoint_l.
        + eapply Disjoint_Included_l.
          * exact Hctx_main.
          * eapply Union_Disjoint_l.
            -- constructor. intros z Hz.
               inversion Hz as [? Hleft Hright]; subst; clear Hz.
               exact ((proj2 (proj1 Hright)) (proj1 Hleft)).
            -- constructor. intros z Hz.
               inversion Hz as [? Hleft Hright]; subst; clear Hz.
               exact ((proj2 Hright) Hleft).
        + eapply Disjoint_Included_l.
          * rewrite occurs_free_Ehalt. eapply Setminus_Included.
          * eapply Disjoint_Singleton_l. exact Hr_not_old_non_cmap. }

    eapply preord_exp_preserves_divergence.
    - eapply anf_bound_post_upper_bound.
    - intros i. exact (Hpre_glob (C |[ Ehalt r ]|) i Hdis_cont).
    - exact Hmain_div.
  Qed.

  Theorem anf_divergence_top e Sg e_tgt :
    wellformed Σ 0 e = true ->
    anf_rel_top e Sg e_tgt ->
    src_diverge [] e ->
    eval.diverge cenv (M.empty val) e_tgt.
  Proof.
    intros Hwf [Sg' [S' [C_env [C [r [Hglob [Hmain ->]]]]]]] Hdiv.
    eapply anf_divergence_top_explicit; eauto.
  Qed.

End Refinement.

Section ComputationalCorrespondence.

  Context (func_tag default_tag default_itag : positive)
          (tgm : conId_map)
          (Σ : EAst.global_context).

  Context {efl : EEnvFlags}.
  Context (HnoAxioms : has_axioms = false).

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

  Lemma convert_top_anf_prog_corresp e Sg :
    wellformed Σ 0 e = true ->
    compM.triple
      (fun _ s => fresh Sg (state.next_var (fst s)))
      ('(cm, C_env) <- convert_global_decls func_tag default_tag prim_map tgm prims (fun _ => None) (List.rev Σ) [] ;;
       '(r, C) <- convert_anf func_tag default_tag prim_map tgm prims cm e new_var_map None ;;
       ret (C_env |[ C |[ Ehalt r ]| ]|))
      (fun _ _ e_tgt _ =>
         exists cm Sg' S' C_env C r,
           anf_cvt_rel_global func_tag default_tag tgm
             Sg (List.rev Σ) [] cm C_env Sg' /\
           anf_cvt_rel func_tag default_tag tgm cm
             Sg' e [] S' C r /\
           e_tgt = C_env |[ C |[ Ehalt r ]| ]|).
  Proof.
    intros Hwf.
    assert (HΣ_top : Σ = List.rev (List.rev Σ) ++ []).
    { rewrite rev_involutive. rewrite app_nil_r. reflexivity. }
    assert (Hcm_empty :
      forall s d, lookup_constant ([] : EAst.global_context) s = Some d ->
                  lookup_const ([] : const_map) s <> None).
    { intros s d Hlk. discriminate. }
    eapply bind_triple.
    { eapply (@anf_cvt_global_corresp
                func_tag default_tag prim_map tgm prims
                efl Σ Hwf_glob HnoAxioms
                HnoVar HnoEvar HnoCoFix HnoLazy Hblocks HnoArray
                no_prims
                (List.rev Σ) [] [] Sg
                HΣ_top Hcm_empty). }
    intros [cm C_env] w.
    eapply pre_existential; intros Sg'.
    eapply pre_curry_l; intros Hglob_cvt.
    eapply pre_strenghtening.
    { intros ? ? [Hcm_complete Hfresh_main].
      exact (conj Hfresh_main Hcm_complete). }
    eapply pre_curry_l; intros Hcm_complete.
    eapply bind_triple.
    { eapply (@anf_cvt_exp_corresp
                func_tag default_tag prim_map tgm prims cm
                efl Σ
                HnoVar HnoEvar HnoCoFix HnoLazy Hblocks HnoArray
                no_prims Hcm_complete
                e [] new_var_map Sg'
                Hwf var_map_correct_nil). }
    intros [r C] w'.
    eapply pre_existential; intros S'.
    eapply pre_curry_l; intros Hmain_cvt.
    eapply return_triple. intros _ s _.
    exists cm, Sg', S', C_env, C, r.
    repeat split; assumption.
  Qed.

  Lemma convert_top_anf_corresp next_id ie e e_tgt comp_d' :
    wellformed Σ 0 e = true ->
    convert_top_anf func_tag default_tag prim_map default_itag next_id tgm prims
      (fun _ => None)
      ie (List.rev Σ) e = (compM.Ret e_tgt, comp_d') ->
    exists cm Sg' S' C_env C r,
      anf_cvt_rel_global func_tag default_tag tgm
        (fun x => (next_id <= x)%positive) (List.rev Σ) [] cm C_env Sg' /\
      anf_cvt_rel func_tag default_tag tgm cm
        Sg' e [] S' C r /\
      e_tgt = C_env |[ C |[ Ehalt r ]| ]|.
  Proof.
    intros Hwf Hrun.
    unfold convert_top_anf in Hrun.
    destruct (convert_env default_tag default_itag ie)
      as [[[[ienv0 cenv0] ctag] itag] dcm].
    simpl in Hrun.
    set (ftag := (func_tag + 1)%positive).
    pose (fenv := M.set func_tag (1%N, (0%N :: nil)) (M.empty _) : fun_env).
    set (comp_d := state.pack_data next_id ctag itag ftag cenv0 fenv (M.empty _) (M.empty nat) []).
    set (Sg := fun x => (next_id <= x)%positive).
    set (prog :=
      '(cm, C_env) <- convert_global_decls func_tag default_tag prim_map tgm prims (fun _ => None) (List.rev Σ) [] ;;
      '(r, C) <- convert_anf func_tag default_tag prim_map tgm prims cm e new_var_map None ;;
      ret (C_env |[ C |[ Ehalt r ]| ]|)).
    assert (Hprog_corresp :
      compM.triple
        (fun _ s => fresh Sg (state.next_var (fst s)))
        prog
        (fun _ _ e_out _ =>
           exists cm Sg' S' C_env C r,
             anf_cvt_rel_global func_tag default_tag tgm
               Sg (List.rev Σ) [] cm C_env Sg' /\
             anf_cvt_rel func_tag default_tag tgm cm
               Sg' e [] S' C r /\
             e_out = C_env |[ C |[ Ehalt r ]| ]|)).
    { unfold prog. eapply convert_top_anf_prog_corresp. exact Hwf. }
    pose proof Hprog_corresp as Hprog.
    unfold triple in Hprog.
    assert (Hfresh : fresh Sg (state.next_var comp_d)).
    { unfold Sg, comp_d, fresh, Ensembles.In. simpl. lia. }
    specialize (Hprog tt (comp_d, tt) Hfresh).
    unfold state.run_compM in Hrun.
    change
      ((let '(res_err, (comp_d'', _)) := compM.runState prog tt (comp_d, tt)
        in (res_err, comp_d'')) = (compM.Ret e_tgt, comp_d')) in Hrun.
    remember (compM.runState prog tt (comp_d, tt)) as top_run eqn:Htop_run.
    destruct top_run as [res [comp_d_fin u]].
    simpl in Hrun, Hprog.
    destruct res; try discriminate.
    inversion Hrun; subst; clear Hrun.
    exact Hprog.
  Qed.

End ComputationalCorrespondence.

Section ComputationalRefinement.

  Context (func_tag kon_tag default_tag default_itag : positive)
          (tgm : conId_map)
          (Σ : EAst.global_context).

  Context {efl : EEnvFlags}.
  Context (HnoAxioms : has_axioms = false).

  Context (dcon_to_tag_inj :
    forall dc dc',
      dcon_to_tag default_tag dc tgm = dcon_to_tag default_tag dc' tgm -> dc = dc').

  Context (box_dc : dcon)
          (box_tag : dcon_to_tag default_tag box_dc tgm = default_tag).

  Context (Hglob_term :
    forall k decl body,
      declared_constant Σ k decl ->
      decl.(EAst.cst_body) = Some body ->
      exists src_v f t, @eval_env_fuel nat
        (LambdaBox_resource_fuel default_tag tgm box_dc box_tag)
        (LambdaBox_resource_trace default_tag tgm box_dc box_tag)
        Σ box_dc [] body (Val src_v) f t).
  Context (Hglob_fuel_zero :
    forall k decl body src_v f t,
      declared_constant Σ k decl ->
      decl.(EAst.cst_body) = Some body ->
      @eval_env_fuel nat
        (LambdaBox_resource_fuel default_tag tgm box_dc box_tag)
        (LambdaBox_resource_trace default_tag tgm box_dc box_tag)
        Σ box_dc [] body (Val src_v) f t ->
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

  Definition top_cenv (ie : ienv) : ctor_env :=
    match convert_env default_tag default_itag ie with
    | (_, cenv, _, _, _) => cenv
    end.

  Definition refines_top (ie : ienv) (M : nat) (e_src : EAst.term) (e_tgt : exp) : Prop :=
    refines default_tag tgm (top_cenv ie) Σ box_dc box_tag M e_src e_tgt.

  Context (ie : ienv).
  Context (cenv_case_consistent_top :
    forall P ctag, caseConsistent (top_cenv ie) P ctag).

  Theorem convert_top_anf_correct next_id e e_tgt comp_d' :
    wellformed Σ 0 e = true ->
    convert_top_anf func_tag default_tag prim_map default_itag next_id tgm prims
      (fun _ => None)
      ie (List.rev Σ) e = (compM.Ret e_tgt, comp_d') ->
    exists M, refines_top ie M e e_tgt.
  Proof.
    intros Hwf Hrun.
    edestruct (@convert_top_anf_corresp
                 func_tag default_tag default_itag
                 tgm Σ efl HnoAxioms
                 prim_map prims Hwf_glob
                 HnoVar HnoEvar HnoCoFix HnoLazy Hblocks HnoArray
                 no_prims
                 next_id ie e e_tgt comp_d' Hwf Hrun)
      as [cm [Sg' [S' [C_env [C [r [Hglob_cvt [Hmain_cvt ->]]]]]]]].
    eapply (@anf_correct_top_explicit
              func_tag kon_tag default_tag default_itag
              tgm cm (top_cenv ie) Σ efl
              HnoAxioms
              dcon_to_tag_inj
              box_dc box_tag
              cenv_case_consistent_top
              Hglob_term Hglob_fuel_zero Hglob_wf
              prim_map prims Hwf_glob
              HnoVar HnoEvar HnoCoFix HnoLazy Hblocks HnoArray
              no_prims
              e (fun x => (next_id <= x)%positive) Sg' S'
              C_env C r); eauto.
  Qed.

  Theorem convert_top_anf_divergence_correct next_id e e_tgt comp_d' :
    wellformed Σ 0 e = true ->
    convert_top_anf func_tag default_tag prim_map default_itag next_id tgm prims
      (fun _ => None)
      ie (List.rev Σ) e = (compM.Ret e_tgt, comp_d') ->
    @fuel_sem.diverge nat
      (LambdaBox_resource_fuel default_tag tgm box_dc box_tag)
      (LambdaBox_resource_trace default_tag tgm box_dc box_tag)
      Σ box_dc [] e ->
    eval.diverge (top_cenv ie) (M.empty val) e_tgt.
  Proof.
    intros Hwf Hrun Hdiv.
    edestruct (@convert_top_anf_corresp
                 func_tag default_tag default_itag
                 tgm Σ efl HnoAxioms
                 prim_map prims Hwf_glob
                 HnoVar HnoEvar HnoCoFix HnoLazy Hblocks HnoArray
                 no_prims
                 next_id ie e e_tgt comp_d' Hwf Hrun)
      as [cm [Sg' [S' [C_env [C [r [Hglob_cvt [Hmain_cvt ->]]]]]]]].
    eapply (@anf_divergence_top_explicit
              func_tag kon_tag default_tag default_itag
              tgm cm (top_cenv ie) Σ efl
              HnoAxioms
              dcon_to_tag_inj
              box_dc box_tag
              cenv_case_consistent_top
              Hglob_term Hglob_fuel_zero Hglob_wf
              prim_map prims Hwf_glob
              HnoVar HnoEvar HnoCoFix HnoLazy Hblocks HnoArray
              no_prims
              e (fun x => (next_id <= x)%positive) Sg' S'
              C_env C r); eauto.
  Qed.

End ComputationalRefinement.
