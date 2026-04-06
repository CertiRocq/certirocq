(* Top-level correctness theorems for ANF conversion from LambdaBox. *)

From Stdlib Require Import ZArith.ZArith Lists.List micromega.Lia Arith
     Ensembles Relations.Relation_Definitions.
From MetaRocq.Erasure Require Import
  EAst EAstUtils EGlobalEnv EWellformed EPrimitive.
From MetaRocq.Common Require Import BasicAst Kernames.
From compcert Require Import lib.Maps lib.Coqlib.
From CertiRocq.Common Require Import AstCommon.
From CertiRocq Require Import Pipeline_utils.
From CertiRocq.LambdaANF Require Import
  cps cps_show eval ctx logical_relations
  List_util algebra alpha_conv functions Ensembles_util
  tactics identifiers bounds cps_util rename set_util stemctx.
From MetaRocq.Utils Require Import All_Forall.
From CertiRocq.LambdaBox_to_LambdaANF Require Import
  common ANF fuel_sem wf anf_corresp anf_util anf_correct anf_global.

Import ListNotations.

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
  Context (cmap_inj : forall k1 k2 v,
    lookup_const cmap k1 = Some v ->
    lookup_const cmap k2 = Some v -> k1 = k2).

  Let Hf_src := LambdaBox_resource_fuel default_tag tgm box_dc box_tag.
  Let Ht_src := LambdaBox_resource_trace default_tag tgm box_dc box_tag.

  Let anf_val_rel' :=
    @anf_val_rel func_tag default_tag tgm cmap nat Hf_src Ht_src Σ box_dc.
  Let anf_env_rel0 :=
    @anf_env_rel func_tag default_tag tgm cmap nat Hf_src Ht_src Σ box_dc.

  Let global_env_rel' :=
    @global_env_rel func_tag default_tag tgm cmap nat Hf_src Ht_src Σ box_dc.

  Let src_eval := @eval_env_fuel nat Hf_src Ht_src Σ box_dc.
  Let cmap_consistent' :=
    @cmap_consistent cmap nat Hf_src Ht_src Σ box_dc.

  Context (Hglob_term :
    forall k decl body,
      declared_constant Σ k decl ->
      decl.(EAst.cst_body) = Some body ->
      exists src_v f t, src_eval [] body (Val src_v) f t).

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
  Context (cmap_complete : forall s d,
    lookup_constant Σ s = Some d -> lookup_const cmap s <> None).
  Context (cmap_sound : forall k v,
    lookup_const cmap k = Some v ->
    exists decl body,
      declared_constant Σ k decl /\ decl.(EAst.cst_body) = Some body).
  Context (cmap_nodup_vals : NoDup (map snd cmap)).

  Let val_rel_exists :=
    @anf_val_rel_exists func_tag default_tag prim_map tgm prims cmap
      _ Σ box_dc nat Hf_src Ht_src
      Hglob_term Hwf_glob
      HnoVar HnoEvar HnoCoFix HnoLazy Hblocks HnoArray
      no_prims cmap_complete cmap_sound cmap_nodup_vals.

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
    Disjoint _ (cmap_vars cmap) Sg ->
    exists M, refines M e (C_env |[ C |[ Ehalt r ]| ]|).
  Proof.
    intros Hwf Hglob_cvt Hmain_cvt Hdis_glob.
    destruct (@global_ctx_correct_top
                func_tag kon_tag default_tag default_itag
                tgm cmap cenv Σ efl
                HnoAxioms
                dcon_to_tag_inj
                box_dc box_tag
                cenv_case_consistent cmap_inj
                Hglob_term Hglob_wf
                prim_map prims Hwf_glob
                HnoVar HnoEvar HnoCoFix HnoLazy Hblocks HnoArray
                no_prims cmap_complete cmap_sound cmap_nodup_vals
                C_env Sg Sg'
                Hglob_cvt Hdis_glob (M.empty val))
      as [rho_g [F_glob [T_glob [Hglob_rho Hpre_glob]]]].
    exists (T_glob + 1).
    intros src_v f t Heval.

    pose proof (@anf_cvt_correct
                  func_tag default_tag default_itag
                  tgm cmap cenv Σ efl
                  dcon_to_tag_inj
                  box_dc box_tag
                  cenv_case_consistent cmap_inj
                  Hglob_term Hglob_wf
                  prim_map prims Hwf_glob
                  HnoVar HnoEvar HnoCoFix HnoLazy Hblocks HnoArray
                  no_prims cmap_complete cmap_sound cmap_nodup_vals
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
    { eapply Disjoint_Included_r.
      - eapply anf_cvt_global_subset. exact Hglob_cvt.
      - exact Hdis_glob. }
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

    assert (Hr_not_old : ~ r \in (Sg \\ Sg')).
    { intro Hin_old.
      destruct (@anf_cvt_result_in_consumed
                  func_tag default_tag tgm cmap
                  Sg' e [] S' C r Hmain_cvt)
        as [Hin_vn | [Hin_s | Hin_cm]].
      - rewrite FromList_nil in Hin_vn. contradiction.
      - exact ((proj2 Hin_old) Hin_s).
      - eapply (Disjoint_In_l _ _ _ Hdis_glob Hin_cm). exact (proj1 Hin_old). }

    assert (Hdis_cont :
      Disjoint _ (occurs_free (C |[ Ehalt r ]|)) (Sg \\ Sg')).
    { eapply Disjoint_Included_l.
      - eapply occurs_free_ctx_app.
      - eapply Union_Disjoint_l.
        + eapply Disjoint_Included_l.
	          * exact Hctx_main.
	          * eapply Union_Disjoint_l.
	            -- constructor. intros z Hz. inv Hz.
	               match goal with
	               | [ Hleft : z \in (Sg' \\ S'), Hright : z \in (Sg \\ Sg') |- _ ] =>
	                 inv Hleft; inv Hright; contradiction
	               end.
	            -- eapply Disjoint_Included_r.
	               ++ eapply Setminus_Included.
	               ++ exact Hdis_glob.
        + eapply Disjoint_Included_l.
          * rewrite occurs_free_Ehalt. eapply Setminus_Included.
          * eapply Disjoint_Singleton_l. exact Hr_not_old. }

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
    Disjoint _ (cmap_vars cmap) Sg ->
    anf_rel_top e Sg e_tgt ->
    exists M, refines M e e_tgt.
  Proof.
    intros Hwf Hdis [Sg' [S' [C_env [C [r [Hglob [Hmain ->]]]]]]].
    eapply anf_correct_top_explicit; eauto.
  Qed.

End Refinement.
