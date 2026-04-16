(* Separate divergence lemmas for the LambdaBox-to-LambdaANF ANF proof. *)

(** Stdlib *)
From Stdlib Require Import ZArith.ZArith Lists.List micromega.Lia Arith
     Logic.Classical_Prop
     Ensembles Relations.Relation_Definitions Wellfounded
     Lexicographic_Product Wf_nat.

(** MetaRocq *)
From MetaRocq.Erasure Require Import EAst EAstUtils EGlobalEnv EWellformed EPrimitive.
From MetaRocq.Erasure Require Import EInduction.
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

Section Divergence.

  Context (func_tag kon_tag default_tag default_itag : positive)
          (tgm : conId_map)
          (cmap : const_map)
          (cenv : ctor_env)
          (Σ : EAst.global_context).

  Context {efl : EEnvFlags}.

  Context (dcon_to_tag_inj :
    forall dc dc',
      dcon_to_tag default_tag dc tgm = dcon_to_tag default_tag dc' tgm -> dc = dc').

  Context (box_dc : dcon)
          (box_tag : dcon_to_tag default_tag box_dc tgm = default_tag).

  Context (cenv_case_consistent : forall P ctag,
    caseConsistent cenv P ctag).

  Context (Hcmap_eval_coherent :
    @cmap_eval_coherent cmap nat
                        (LambdaBox_resource_fuel default_tag tgm box_dc box_tag)
                        (LambdaBox_resource_trace default_tag tgm box_dc box_tag)
                        Σ box_dc).

  Context (Hglob_term : globals_terminate_prop default_tag tgm Σ box_dc box_tag).
  Context (Hglob_fuel_zero : globals_zero_fuel_prop default_tag tgm Σ box_dc box_tag).

  Context (Hglob_wf : forall k decl body,
    declared_constant Σ k decl ->
    decl.(EAst.cst_body) = Some body ->
    wellformed Σ 0 body = true).

  Context (val_rel_exists :
    forall v,
      well_formed_val Σ v ->
      exists v',
        @anf_val_rel func_tag default_tag tgm cmap
                     nat
                     (LambdaBox_resource_fuel default_tag tgm box_dc box_tag)
                     (LambdaBox_resource_trace default_tag tgm box_dc box_tag)
                     Σ box_dc v v').

  Let anf_cvt_rel' := anf_cvt_rel func_tag default_tag tgm cmap.
  Let anf_cvt_rel_args' := anf_cvt_rel_args func_tag default_tag tgm cmap.
  Let cmap_consistent' :=
    @cmap_consistent cmap nat
                     (LambdaBox_resource_fuel default_tag tgm box_dc box_tag)
                     (LambdaBox_resource_trace default_tag tgm box_dc box_tag)
                     Σ box_dc.
  Let anf_val_rel' :=
    @anf_val_rel func_tag default_tag tgm cmap
                 nat
                 (LambdaBox_resource_fuel default_tag tgm box_dc box_tag)
                 (LambdaBox_resource_trace default_tag tgm box_dc box_tag)
                 Σ box_dc.
  Let anf_env_rel' :=
    @anf_env_rel func_tag default_tag tgm cmap
                 nat
                 (LambdaBox_resource_fuel default_tag tgm box_dc box_tag)
                 (LambdaBox_resource_trace default_tag tgm box_dc box_tag)
                 Σ box_dc.
  Let global_env_rel' :=
    @global_env_rel func_tag default_tag tgm cmap
                    nat
                    (LambdaBox_resource_fuel default_tag tgm box_dc box_tag)
                    (LambdaBox_resource_trace default_tag tgm box_dc box_tag)
                    Σ box_dc.
  Let src_eval :=
    @eval_env_fuel nat
                   (LambdaBox_resource_fuel default_tag tgm box_dc box_tag)
                   (LambdaBox_resource_trace default_tag tgm box_dc box_tag)
                   Σ box_dc.
  Let src_fuel_res : @LambdaBox_resource nat :=
    LambdaBox_resource_fuel default_tag tgm box_dc box_tag.
  #[local] Existing Instance src_fuel_res.
  Let src_trace_res : @LambdaBox_resource nat :=
    LambdaBox_resource_trace default_tag tgm box_dc box_tag.
  Let src_one :=
    @one_i EAst.term nat (@HRes _ src_fuel_res).
  Let src_diverge :=
    @fuel_sem.diverge nat
                      (LambdaBox_resource_fuel default_tag tgm box_dc box_tag)
                      (LambdaBox_resource_trace default_tag tgm box_dc box_tag)
                      Σ box_dc.
  Let src_not_stuck :=
    @fuel_sem.not_stuck nat
                        (LambdaBox_resource_fuel default_tag tgm box_dc box_tag)
                        (LambdaBox_resource_trace default_tag tgm box_dc box_tag)
                        Σ box_dc.
  Let eq_fuel_compat' :=
    @eq_fuel_compat func_tag default_tag tgm cmap cenv Σ box_dc box_tag.

  Definition anf_cvt_correct_exps'
             (vs_env : fuel_sem.env) (es : list EAst.term)
             (vs1 : list fuel_sem.value) (f t : nat) :=
    forall rho vnames C xs S S' i,
      well_formed_env Σ vs_env ->
      Forall (fun e => wellformed Σ (List.length vnames) e = true) es ->
      env_consistent vnames vs_env ->
      cmap_consistent' vnames vs_env ->
      Disjoint _ (FromList vnames) S ->
      Disjoint _ (cmap_vars cmap) S ->
      anf_env_rel' vnames vs_env rho ->
      global_env_rel' (kn_deps_list es) rho ->
      anf_cvt_rel_args' S es vnames S' C xs ->
      forall e_k vs',
        Forall2 anf_val_rel' vs1 vs' ->
        Disjoint _ (occurs_free e_k) ((S \\ S') \\ FromList xs) ->
        preord_exp cenv (anf_bound f t) eq_fuel i
                   (e_k, set_many xs vs' rho)
                   (C |[ e_k ]|, rho).

  Lemma eval_val_exact_det rho e v1 v2 f1 t1 f2 t2 :
    src_eval rho e (fuel_sem.Val v1) f1 t1 ->
    src_eval rho e (fuel_sem.Val v2) f2 t2 ->
    v1 = v2 /\ f1 = f2 /\ t1 = t2.
  Proof. apply fuel_sem.eval_val_exact_det. Qed.

  Lemma src_eval_val_gt_oot rho0 e0 v0 f_val t_val :
    src_eval rho0 e0 (fuel_sem.Val v0) f_val t_val ->
    forall f_oot t_oot,
      src_eval rho0 e0 fuel_sem.OOT f_oot t_oot ->
      f_oot < f_val.
  Proof.
    intros Hval.
    set (Pstep := fun (rho : fuel_sem.env) (e : EAst.term)
                      (r : fuel_sem.result) (f : nat) (t : nat) =>
      match r with
      | fuel_sem.Val _ =>
        forall f_oot t_oot,
          @eval_env_step _ src_fuel_res src_trace_res
                         Σ box_dc rho e fuel_sem.OOT f_oot t_oot ->
          f_oot < f
      | fuel_sem.OOT => True
      end).
    set (Pmany := fun (rho : fuel_sem.env) (es : list EAst.term)
                      (vs : list fuel_sem.value) (fs : nat) (ts : nat) =>
      forall args_done e args_rest vs_done fs' f_oot t_oot ts',
        es = args_done ++ e :: args_rest ->
        @eval_fuel_many _ src_fuel_res src_trace_res
                        Σ box_dc rho args_done vs_done fs' ts' ->
        src_eval rho e fuel_sem.OOT f_oot t_oot ->
        fs' + f_oot < fs).
    set (Pfuel := fun (rho : fuel_sem.env) (e : EAst.term)
                      (r : fuel_sem.result) (f : nat) (t : nat) =>
      match r with
      | fuel_sem.Val _ =>
        forall f_oot t_oot,
          src_eval rho e fuel_sem.OOT f_oot t_oot ->
          f_oot < f
      | fuel_sem.OOT => True
      end).
    enough (Haux : Pfuel rho0 e0 (fuel_sem.Val v0) f_val t_val) by exact Haux.
    eapply (@eval_env_fuel_ind'
              nat src_fuel_res src_trace_res
              Σ box_dc Pstep Pmany Pfuel); try exact Hval;
      unfold Pstep, Pmany, Pfuel; simpl in *.
    - intros n rho v Hnth f_oot t_oot Hoot.
      remember (EAst.tRel n) as e_rel in Hoot.
      remember fuel_sem.OOT as r_oot in Hoot.
      destruct Hoot; try discriminate.
    - intros body rho na f_oot t_oot Hoot.
      remember (EAst.tLambda na body) as e_lam in Hoot.
      remember fuel_sem.OOT as r_oot in Hoot.
      destruct Hoot; try discriminate.
    - intros mfix idx rho f_oot t_oot Hoot.
      remember (EAst.tFix mfix idx) as e_fix in Hoot.
      remember fuel_sem.OOT as r_oot in Hoot.
      destruct Hoot; try discriminate.
    - intros rho f_oot t_oot Hoot.
      remember EAst.tBox as e_box in Hoot.
      remember fuel_sem.OOT as r_oot in Hoot.
      destruct Hoot; try discriminate.
    - intros e1 e2 body v2 r na rho rho' f1 f2 f3 t1 t2 t3
             He1 IH1 He2 IH2 Hbody IH3.
      destruct r as [v_r |]; [| exact I].
      intros f_oot t_oot Hoot.
      remember (EAst.tApp e1 e2) as e_app in Hoot.
      remember fuel_sem.OOT as r_oot in Hoot.
      destruct Hoot; try discriminate.
      + injection Heqe_app as <- <-. subst.
        pose proof (eval_val_exact_det _ _ _ _
                      _ _ _ _ He1 H) as [Heq1 [-> ->]].
        injection Heq1 as <- <- <-.
        pose proof (eval_val_exact_det _ _ _ _
                      _ _ _ _ He2 H0) as [-> [-> ->]].
        pose proof (IH3 _ _ H1) as Hlt_body. simpl in *. lia.
      + injection Heqe_app as <- <-. subst.
        specialize (IH1 _ _ H). lia.
      + injection Heqe_app as <- <-. subst.
        pose proof (eval_val_exact_det _ _ _ _
                      _ _ _ _ He1 H) as [_ [-> ->]].
        pose proof (IH2 _ _ H0) as Hlt_arg. simpl in *. lia.
      + injection Heqe_app as <- <-. subst.
        pose proof (eval_val_exact_det _ _ _ _
                      _ _ _ _ He1 H) as [Heq1 _].
        discriminate.
    - intros e1 e2 rho f1 t1 He1 IH1. exact I.
    - intros e1 e2 v rho f1 f2 t1 t2 He1 IH1 He2 IH2. exact I.
    - intros e1 e2 body rho rho' rho'' idx na mfix v2 r f1 f2 f3 t1 t2 t3
             He1 IH1 Hfix Hrec He2 IH2 Hbody IH3.
      destruct r as [v_r |]; [| exact I].
      intros f_oot t_oot Hoot.
      remember (EAst.tApp e1 e2) as e_app in Hoot.
      remember fuel_sem.OOT as r_oot in Hoot.
      destruct Hoot; try discriminate.
      + injection Heqe_app as <- <-. subst.
        pose proof (eval_val_exact_det _ _ _ _
                      _ _ _ _ He1 H) as [Heq1 _].
        discriminate.
      + injection Heqe_app as <- <-. subst.
        pose proof (IH1 _ _ H) as Hlt_fun. simpl in *. lia.
      + injection Heqe_app as <- <-. subst.
        pose proof (eval_val_exact_det _ _ _ _
                      _ _ _ _ He1 H) as [_ [-> ->]].
        pose proof (IH2 _ _ H0) as Hlt_arg. simpl in *. lia.
      + injection Heqe_app as <- <-. subst.
        rename H into He1_2. rename H0 into Hfix2.
        rename H2 into He2_2. rename H3 into Hbody2.
        pose proof (eval_val_exact_det _ _ _ _
                      _ _ _ _ He1 He1_2) as [Heq1 [-> ->]].
        injection Heq1 as <- <- <-.
        rewrite Hfix in Hfix2. injection Hfix2 as <- <-.
        pose proof (eval_val_exact_det _ _ _ _
                      _ _ _ _ He2 He2_2) as [-> [-> ->]].
        pose proof (IH3 _ _ Hbody2) as Hlt_body. simpl in *. lia.
    - intros na b t v1 r rho f1 f2 t1 t2
             Heb IHb Het IHt.
      destruct r as [v_r |]; [| exact I].
      intros f_oot t_oot Hoot.
      remember (EAst.tLetIn na b t) as e_let in Hoot.
      remember fuel_sem.OOT as r_oot in Hoot.
      destruct Hoot; try discriminate.
      + injection Heqe_let as <- <- <-. subst.
        pose proof (eval_val_exact_det _ _ _ _
                      _ _ _ _ Heb H) as [-> [-> ->]].
        pose proof (IHt _ _ H0) as Hlt_body. simpl in *. lia.
      + injection Heqe_let as <- <- <-. subst.
        pose proof (IHb _ _ H) as Hlt_bind. simpl in *. lia.
    - intros na b t rho f1 t1 Heb IHb.
      exact I.
    - intros ind c args vs rho dc fs ts Hdc Hmany IHmany f_oot t_oot Hoot.
      remember (EAst.tConstruct ind c args) as e_con in Hoot.
      remember fuel_sem.OOT as r_oot in Hoot.
      destruct Hoot; try discriminate.
      injection Heqe_con as <- <- <-. subst.
      eapply IHmany; eauto.
    - intros ind c args args_done args_rest e vs rho fs f t ts
             Hargs Hdone IHdone Hoot IHoot.
      exact I.
    - intros ind npars mch brs rho dc vs body c r f1 f2 t1 t2
             Hmch IHmch Hdc Hfind Hbody IHbody.
      destruct r as [v_r |]; [| exact I].
      intros f_oot t_oot Hoot.
      remember (EAst.tCase (ind, npars) mch brs) as e_case in Hoot.
      remember fuel_sem.OOT as r_oot in Hoot.
      destruct Hoot; try discriminate.
      + injection Heqe_case as <- <- <-. subst.
        pose proof (eval_val_exact_det _ _ _ _
                      _ _ _ _ Hmch H) as [Heq1 [-> ->]].
        inversion Heq1; subst.
        apply Nnat.Nat2N.inj in H3. subst c0.
        rewrite Hfind in H1. injection H1 as <-.
        pose proof (IHbody _ _ H2) as Hlt_body. simpl in *. lia.
      + injection Heqe_case as <- <- <-. subst.
        pose proof (IHmch _ _ H) as Hlt_mch. simpl in *. lia.
    - intros ind npars mch brs rho f1 t1 Hmch IHmch.
      exact I.
    - intros p c rho vs v f1 t1 Hc IHc Hnth f_oot t_oot Hoot.
      remember (EAst.tProj p c) as e_proj in Hoot.
      remember fuel_sem.OOT as r_oot in Hoot.
      destruct Hoot; try discriminate.
      injection Heqe_proj as <- <-. subst.
      specialize (IHc _ _ H). lia.
    - intros p c rho f1 t1 Hc IHc.
      exact I.
    - intros k body v decl rho f t Hdecl Hbody Hbody_eval IHbody f_oot t_oot Hoot.
      remember (EAst.tConst k) as e_const in Hoot.
      remember fuel_sem.OOT as r_oot in Hoot.
      destruct Hoot; try discriminate.
    - intros rho args_done e args_rest vs_done fs' f_oot t_oot ts'
             Hargs Hdone Hoot.
      destruct args_done; simpl in Hargs; discriminate.
    - intros rho e es v vs f fs t ts He IH_e Hes IH_es
             args_done e' args_rest vs_done fs' f_oot t_oot ts'
             Hargs Hdone Hoot.
      destruct args_done as [| a args_done'].
      + simpl in Hargs. inversion Hargs; subst.
        inversion Hdone; subst.
        specialize (IH_e _ _ Hoot).
        change (0 + f_oot < f + fs)%nat.
        lia.
      + inversion Hdone; subst.
        assert (Ha : a = e /\ es = args_done' ++ e' :: args_rest).
        { simpl in Hargs. inversion Hargs. subst. split; reflexivity. }
        destruct Ha as [-> Hargs'].
        pose proof (eval_val_exact_det _ _ _ _
                      _ _ _ _ He H2) as [_ [-> ->]].
        specialize (IH_es _ _ _ _ _ _ _ _ Hargs' H6 Hoot).
        simpl in *. lia.
    - intros rho e f Hlt0.
      exact I.
    - intros rho e r f t Hstep IHstep.
      destruct r as [v|]; [| exact I].
      intros f_oot t_oot Hoot.
      remember e as e_cur in Hoot.
      remember fuel_sem.OOT as r_oot in Hoot.
      destruct Hoot; try discriminate.
      + subst. simpl in *. lia.
      + subst.
        specialize (IHstep _ _ H). simpl in *. lia.
  Qed.

  Lemma anf_cvt_rel_var_lookup rho e v f t :
    src_eval rho e (fuel_sem.Val v) f t ->
    forall S vn S' C x i,
      anf_cvt_rel' S e vn S' C x ->
      Disjoint _ (FromList vn) S ->
      Disjoint _ (cmap_vars cmap) S ->
      env_consistent vn rho ->
      cmap_consistent' vn rho ->
      nth_error vn i = Some x ->
      nth_error rho i = Some v.
  Proof.
    intros Heval S vn S' C x i Hcvt Hdis Hdis_cm Hcons Hcmap Hnth.
    eapply anf_correct.anf_cvt_rel_var_lookup; eauto.
  Qed.

  Lemma anf_cvt_cmap_eval rho e v f t :
    src_eval rho e (fuel_sem.Val v) f t ->
    forall S vn S' C x k decl body,
      anf_cvt_rel' S e vn S' C x ->
      Disjoint _ (FromList vn) S ->
      Disjoint _ (cmap_vars cmap) S ->
      env_consistent vn rho ->
      cmap_consistent' vn rho ->
      lookup_const cmap k = Some x ->
      declared_constant Σ k decl ->
      decl.(EAst.cst_body) = Some body ->
      exists f' t', src_eval [] body (fuel_sem.Val v) f' t'.
  Proof.
    intros Heval S vn S' C x k decl body
           Hcvt Hdis Hdis_cm Hcons Hcmap Hlk Hdecl Hbody.
    eapply anf_correct.anf_cvt_cmap_eval; eauto.
  Qed.

  Lemma src_eval_app_val_fun rho e1 e2 v_app f t :
    src_eval rho (EAst.tApp e1 e2) (fuel_sem.Val v_app) f t ->
    exists v1 f1 t1,
      src_eval rho e1 (fuel_sem.Val v1) f1 t1.
  Proof.
    intros Happ.
    inversion Happ; subst; try discriminate.
    remember (EAst.tApp e1 e2) as e_app in H.
    remember (fuel_sem.Val v_app) as r_app in H.
    inversion H; subst; try discriminate.
    - match goal with
      | [ Heq : EAst.tApp _ _ = EAst.tApp _ _ |- _ ] =>
          injection Heq as <- <-; subst
      end.
      eexists _, _, _. exact H0.
    - match goal with
      | [ Heq : EAst.tApp _ _ = EAst.tApp _ _ |- _ ] =>
          injection Heq as <- <-; subst
      end.
      eexists _, _, _. exact H0.
  Qed.

  Lemma src_eval_app_oot_fun_if_no_fun_val rho e1 e2 f t :
    (forall src_v f' t', ~ src_eval rho e1 (fuel_sem.Val src_v) f' t') ->
    src_eval rho (EAst.tApp e1 e2) fuel_sem.OOT (Datatypes.S f) t ->
    exists t1, src_eval rho e1 fuel_sem.OOT f t1.
  Proof.
    intros Hnoval Hoot_app.
    inversion Hoot_app; subst.
    - simpl in H. lia.
    - inversion H3; subst; try discriminate.
      + exfalso. eapply Hnoval. exact H2.
      + assert (f0 = f) by lia. subst.
        exists t0. exact H2.
      + exfalso. eapply Hnoval. exact H4.
      + exfalso. eapply Hnoval. exact H2.
  Qed.

  Lemma src_not_stuck_app_fun rho e1 e2 :
    src_not_stuck rho (EAst.tApp e1 e2) ->
    src_not_stuck rho e1.
  Proof.
    intros Hns.
      destruct (classic (exists src_v f t, src_eval rho e1 (fuel_sem.Val src_v) f t))
      as [Hval | Hnoval].
    - left. exact Hval.
    - right. intros f.
      destruct Hns as [Happ_val | Hdiv_app].
      + exfalso.
        destruct Happ_val as [src_v [f_app [t_app Happ_val]]].
        destruct (src_eval_app_val_fun _ _ _ _ _ _ Happ_val)
          as [v1 [f1 [t1 Hfun]]].
        eapply Hnoval. eexists _, _, _. exact Hfun.
      + destruct (Hdiv_app (Datatypes.S f)) as [t_app Hoot_app].
        eapply src_eval_app_oot_fun_if_no_fun_val.
        * intros src_v f' t' Hval_e1.
          apply Hnoval. eexists _, _, _. exact Hval_e1.
        * exact Hoot_app.
  Qed.

  Lemma src_eval_app_val_arg rho e1 e2 v_app f t :
    src_eval rho (EAst.tApp e1 e2) (fuel_sem.Val v_app) f t ->
    exists v2 f2 t2,
      src_eval rho e2 (fuel_sem.Val v2) f2 t2.
  Proof.
    intros Happ.
    inversion Happ; subst; try discriminate.
    remember (EAst.tApp e1 e2) as e_app in H.
    remember (fuel_sem.Val v_app) as r_app in H.
    inversion H; subst; try discriminate.
    - injection H4 as <- <-. subst.
      eexists _, _, _. exact H1.
    - injection H6 as <- <-. subst.
      eexists _, _, _. exact H3.
  Qed.

  Lemma src_eval_app_oot_arg_if_fun_val_no_arg_val rho e1 e2 v1 f1 t1 f t :
    src_eval rho e1 (fuel_sem.Val v1) f1 t1 ->
    (forall src_v f' t', ~ src_eval rho e2 (fuel_sem.Val src_v) f' t') ->
    src_eval rho (EAst.tApp e1 e2) fuel_sem.OOT (f1 + f + 1) t ->
    exists t2, src_eval rho e2 fuel_sem.OOT f t2.
  Proof.
    intros He1 Hnoval2 Hoot_app.
    inversion Hoot_app; subst.
    - simpl in H. lia.
    - inversion H3; subst; try discriminate.
      + exfalso. eapply Hnoval2. exact H5.
      + pose proof (src_eval_val_gt_oot
                      _ _ _ _ _ He1 _ _ H2) as Hlt.
        lia.
      + pose proof (eval_val_exact_det _ _ _ _ _ _ _ _ He1 H4)
          as [_ [-> ->]].
        simpl in H.
        assert (Hff : f = f3) by lia.
        rewrite Hff.
        exists t3. exact H5.
      + exfalso. eapply Hnoval2. exact H7.
  Qed.

  Lemma src_not_stuck_app_arg rho e1 e2 v1 f1 t1 :
    src_eval rho e1 (fuel_sem.Val v1) f1 t1 ->
    src_not_stuck rho (EAst.tApp e1 e2) ->
    src_not_stuck rho e2.
  Proof.
    intros He1 Hns.
    destruct (classic (exists src_v f t, src_eval rho e2 (fuel_sem.Val src_v) f t))
      as [Hval | Hnoval].
    - left. exact Hval.
    - right. intros f.
      destruct Hns as [Happ_val | Hdiv_app].
      + exfalso.
        destruct Happ_val as [src_v [f_app [t_app Happ_val]]].
        destruct (src_eval_app_val_arg _ _ _ _ _ _ Happ_val)
          as [v2 [f2 [t2 Harg]]].
        apply Hnoval. eexists _, _, _. exact Harg.
      + destruct (Hdiv_app (f1 + f + 1)) as [t_app Hoot_app].
        eapply src_eval_app_oot_arg_if_fun_val_no_arg_val.
        * exact He1.
        * intros src_v f' t' Hval_e2.
          apply Hnoval. eexists _, _, _. exact Hval_e2.
        * exact Hoot_app.
  Qed.

  (** Source-side fuel monotonicity towards [OOT].

      This is proved in the concrete nat-instantiated divergence development
      rather than in [fuel_sem], because here the source fuel resource is
      definitionally ordinary addition and [lia] can reason about the
      decompositions created by app/case/construct steps. *)
  Lemma src_eval_lt_OOT_any rho0 e0 r0 f0 t0 :
    src_eval rho0 e0 r0 f0 t0 ->
    forall f', f' < f0 ->
    exists t', src_eval rho0 e0 fuel_sem.OOT f' t'.
  Proof.
    intros Heval.
    set (Pstep := fun (rho : fuel_sem.env) (e : EAst.term)
                      (r : fuel_sem.result) (f : nat) (t : nat) =>
      forall f', f' < f ->
      exists t', @eval_env_step _ src_fuel_res src_trace_res
                                 Σ box_dc rho e fuel_sem.OOT f' t').
    set (Pmany := fun (rho : fuel_sem.env) (es : list EAst.term)
                      (vs : list fuel_sem.value) (fs : nat) (ts : nat) =>
      forall f',
        f' < fs ->
        exists args_done e args_rest vs_done fs' f_oot t_oot ts',
          es = args_done ++ e :: args_rest /\
          @eval_fuel_many _ src_fuel_res src_trace_res
                          Σ box_dc rho args_done vs_done fs' ts' /\
          src_eval rho e fuel_sem.OOT f_oot t_oot /\
          f' = fs' + f_oot).
    set (Pfuel := fun (rho : fuel_sem.env) (e : EAst.term)
                      (r : fuel_sem.result) (f : nat) (t : nat) =>
      forall f', f' < f ->
      exists t', src_eval rho e fuel_sem.OOT f' t').
    enough (Haux : Pfuel rho0 e0 r0 f0 t0) by exact Haux.
    eapply (@eval_env_fuel_ind'
              nat src_fuel_res src_trace_res
              Σ box_dc Pstep Pmany Pfuel); try exact Heval;
      unfold Pstep, Pmany, Pfuel;
      simpl in *.
    - intros n rho v Hnth f' Hlt. exfalso. lia.
    - intros body rho na f' Hlt. exfalso. lia.
    - intros mfix idx rho f' Hlt. exfalso. lia.
    - intros rho f' Hlt. exfalso. lia.
    - intros e1 e2 body v2 r na rho rho' f1 f2 f3 t1 t2 t3
             He1 IH1 He2 IH2 Hbody IH3 f' Hlt.
      destruct (Nat.lt_ge_cases f' f1) as [Hlt1 | Hge1].
      + destruct (IH1 _ Hlt1) as [t_oot Hoot].
        exists t_oot. now eapply fuel_sem.eval_App_step_OOT1.
      + assert (Hlt23 : f' - f1 < f2 + f3) by lia.
        destruct (Nat.lt_ge_cases (f' - f1) f2) as [Hlt2 | Hge2].
        * destruct (IH2 _ Hlt2) as [t_oot Hoot].
          exists (t1 + t_oot).
          assert (Heqf : f' = (f1 + (f' - f1))) by lia.
          rewrite Heqf.
          exact (@fuel_sem.eval_App_step_OOT2
                   nat src_fuel_res src_trace_res
                   Σ box_dc e1 e2 (fuel_sem.Clos_v rho' na body) rho
                   f1 (f' - f1) t1 t_oot He1 Hoot).
        * assert (Hlt3 : f' - f1 - f2 < f3) by lia.
          destruct (IH3 _ Hlt3) as [t_oot Hoot].
          exists (t1 + t2 + t_oot).
          assert (Heqf : f' = (f1 + f2 + (f' - f1 - f2))) by lia.
          rewrite Heqf.
          exact (@fuel_sem.eval_App_step
                   nat src_fuel_res src_trace_res
                   Σ box_dc e1 e2 body v2 fuel_sem.OOT na rho rho'
                   f1 f2 (f' - f1 - f2) t1 t2 t_oot
                   He1 He2 Hoot).
    - intros e1 e2 rho f1 t1 He1 IH1 f' Hlt.
      destruct (IH1 _ Hlt) as [t_oot Hoot].
      exists t_oot. now eapply fuel_sem.eval_App_step_OOT1.
    - intros e1 e2 v rho f1 f2 t1 t2 He1 IH1 He2 IH2 f' Hlt.
      destruct (Nat.lt_ge_cases f' f1) as [Hlt1 | Hge1].
      + destruct (IH1 _ Hlt1) as [t_oot Hoot].
        exists t_oot. now eapply fuel_sem.eval_App_step_OOT1.
      + assert (Hlt2 : f' - f1 < f2) by lia.
        destruct (IH2 _ Hlt2) as [t_oot Hoot].
        exists (t1 + t_oot).
        assert (Heqf : f' = (f1 + (f' - f1))) by lia.
        rewrite Heqf.
        exact (@fuel_sem.eval_App_step_OOT2
                 nat src_fuel_res src_trace_res
                 Σ box_dc e1 e2 v rho f1 (f' - f1) t1 t_oot He1 Hoot).
    - intros e1 e2 body rho rho' rho'' idx na mfix v2 r f1 f2 f3 t1 t2 t3
             He1 IH1 Hfix Hrec He2 IH2 Hbody IH3 f' Hlt.
      destruct (Nat.lt_ge_cases f' f1) as [Hlt1 | Hge1].
      + destruct (IH1 _ Hlt1) as [t_oot Hoot].
        exists t_oot. now eapply fuel_sem.eval_App_step_OOT1.
      + assert (Hlt23 : f' - f1 < f2 + f3) by lia.
        destruct (Nat.lt_ge_cases (f' - f1) f2) as [Hlt2 | Hge2].
        * destruct (IH2 _ Hlt2) as [t_oot Hoot].
          exists (t1 + t_oot).
          assert (Heqf : f' = (f1 + (f' - f1))) by lia.
          rewrite Heqf.
          exact (@fuel_sem.eval_App_step_OOT2
                   nat src_fuel_res src_trace_res
                   Σ box_dc e1 e2 (fuel_sem.ClosFix_v rho' mfix idx) rho
                   f1 (f' - f1) t1 t_oot He1 Hoot).
        * assert (Hlt3 : f' - f1 - f2 < f3) by lia.
          destruct (IH3 _ Hlt3) as [t_oot Hoot].
          exists (t1 + t2 + t_oot).
          assert (Heqf : f' = (f1 + f2 + (f' - f1 - f2))) by lia.
          rewrite Heqf.
          exact (@fuel_sem.eval_FixApp_step
                   nat src_fuel_res src_trace_res
                   Σ box_dc e1 e2 body rho rho' rho'' idx na mfix v2
                   fuel_sem.OOT f1 f2 (f' - f1 - f2) t1 t2 t_oot
                   He1 Hfix Hrec He2 Hoot).
    - intros na b t v1 r rho f1 f2 t1 t2
             Heb IHb Het IHt f' Hlt.
      destruct (Nat.lt_ge_cases f' f1) as [Hlt1 | Hge1].
      + destruct (IHb _ Hlt1) as [t_oot Hoot].
        exists t_oot. now eapply fuel_sem.eval_LetIn_step_OOT.
      + assert (Hlt2 : f' - f1 < f2) by lia.
        destruct (IHt _ Hlt2) as [t_oot Hoot].
        exists (t1 + t_oot).
        assert (Heqf : f' = (f1 + (f' - f1))) by lia.
        rewrite Heqf.
        exact (@fuel_sem.eval_LetIn_step
                 nat src_fuel_res src_trace_res
                 Σ box_dc na b t v1 fuel_sem.OOT rho f1 (f' - f1) t1 t_oot
                 Heb Hoot).
    - intros na b t rho f1 t1 Heb IHb f' Hlt.
      destruct (IHb _ Hlt) as [t_oot Hoot].
      exists t_oot. now eapply fuel_sem.eval_LetIn_step_OOT.
    - intros ind c args vs rho dc fs ts Hdc Hmany IHmany f' Hlt.
      destruct (IHmany _ Hlt) as
        (args_done & e & args_rest & vs_done & fs' & f_oot & t_oot & ts' &
         Hargs & Hmany_done & Hoot & Hfuel).
      subst.
      exists (ts' + t_oot).
      exact (@fuel_sem.eval_Construct_step_OOT
               nat src_fuel_res src_trace_res
               Σ box_dc ind c (args_done ++ e :: args_rest)
               args_done args_rest e vs_done rho fs' f_oot t_oot ts'
               eq_refl Hmany_done Hoot).
    - intros ind c args args_done args_rest e vs rho fs f t ts
             Hargs Hdone IHdone Hoot IHoot f' Hlt.
      destruct (Nat.lt_ge_cases f' fs) as [Hlt_done | Hge_done].
      + destruct (IHdone _ Hlt_done) as
          (args_done' & e' & args_rest' & vs_done & fs' & f_oot & t_oot & ts' &
           Hargs' & Hmany_done & Hoot' & Hfuel).
        exists (ts' + t_oot).
        assert (Hargs_total :
                  args = args_done' ++ e' :: (args_rest' ++ e :: args_rest)).
        { rewrite Hargs. rewrite Hargs'. rewrite <- app_assoc. reflexivity. }
        rewrite Hfuel.
        exact (@fuel_sem.eval_Construct_step_OOT
                 nat src_fuel_res src_trace_res
                 Σ box_dc ind c args
                 args_done' (args_rest' ++ e :: args_rest) e'
                 vs_done rho fs' f_oot t_oot ts'
                 Hargs_total Hmany_done Hoot').
      + assert (Hlt_oot : f' - fs < f) by lia.
        destruct (IHoot _ Hlt_oot) as [t_oot' Hoot'].
        exists (ts + t_oot').
        assert (Heqf : f' = (fs + (f' - fs))) by lia.
        rewrite Heqf.
        exact (@fuel_sem.eval_Construct_step_OOT
                 nat src_fuel_res src_trace_res
                 Σ box_dc ind c args
                 args_done args_rest e vs rho fs (f' - fs) t_oot' ts
                 Hargs Hdone Hoot').
    - intros ind npars mch brs rho dc vs body c r f1 f2 t1 t2
             Hmch IHmch Hdc Hfind Hbody IHbody f' Hlt.
      destruct (Nat.lt_ge_cases f' f1) as [Hlt1 | Hge1].
      + destruct (IHmch _ Hlt1) as [t_oot Hoot].
        exists t_oot. now eapply fuel_sem.eval_Case_step_OOT.
      + assert (Hlt2 : f' - f1 < f2) by lia.
        destruct (IHbody _ Hlt2) as [t_oot Hoot].
        exists (t1 + t_oot).
        assert (Heqf : f' = (f1 + (f' - f1))) by lia.
        rewrite Heqf.
        exact (@fuel_sem.eval_Case_step
                 nat src_fuel_res src_trace_res
                 Σ box_dc ind npars mch brs rho dc vs body c fuel_sem.OOT
                 f1 (f' - f1) t1 t_oot
                 Hmch Hdc Hfind Hoot).
    - intros ind npars mch brs rho f1 t1 Hmch IHmch f' Hlt.
      destruct (IHmch _ Hlt) as [t_oot Hoot].
      exists t_oot. now eapply fuel_sem.eval_Case_step_OOT.
    - intros p c rho vs v f1 t1 Hc IHc Hnth f' Hlt.
      destruct (IHc _ Hlt) as [t_oot Hoot].
      exists t_oot. now eapply fuel_sem.eval_Proj_step_OOT.
    - intros p c rho f1 t1 Hc IHc f' Hlt.
      destruct (IHc _ Hlt) as [t_oot Hoot].
      exists t_oot. now eapply fuel_sem.eval_Proj_step_OOT.
    - intros k body v decl rho f t Hdecl Hbody Hbody_eval IHbody f' Hlt.
      assert (Hf_zero : f = 0).
      { eapply Hglob_fuel_zero; eauto. }
      exfalso. lia.
    - intros rho f' Hlt. exfalso. lia.
    - intros rho e es v vs f fs t ts He IH_e Hes IH_es f' Hlt.
      destruct (Nat.lt_ge_cases f' f) as [Hlt_hd | Hge_hd].
      + destruct (IH_e _ Hlt_hd) as [t_oot Hoot].
        exists [], e, es, [], 0, f', t_oot, 0.
        split.
        * reflexivity.
        * split.
          -- constructor.
          -- split.
             ++ exact Hoot.
             ++ lia.
      + assert (Hlt_tl : f' - f < fs) by lia.
        destruct (IH_es _ Hlt_tl) as
          (args_done & e' & args_rest & vs_done & fs' & f_oot & t_oot & ts' &
           Hes' & Hmany_done & Hoot & Hfuel).
        exists (e :: args_done), e', args_rest, (v :: vs_done),
               (f + fs'), f_oot, t_oot, (t + ts').
        split.
        * simpl. now rewrite Hes'.
        * split.
          -- exact (@fuel_sem.eval_many_cons
                      nat src_fuel_res src_trace_res
                      Σ box_dc rho e args_done v vs_done f fs' t ts'
                      He Hmany_done).
          -- split.
             ++ exact Hoot.
             ++ lia.
    - intros rho e f Hlt0 f' Hlt.
      exists 0%nat.
      assert (Hlt0' : (f' < fuel_exp e)%nat) by lia.
      exact (@fuel_sem.eval_OOT
               nat src_fuel_res src_trace_res
               Σ box_dc rho e f' Hlt0').
    - intros rho e r f t Hstep IHstep f' Hlt.
      destruct (Nat.lt_ge_cases f' (fuel_exp e)) as [Hlt0 | Hge0].
      + exists 0%nat.
        exact (@fuel_sem.eval_OOT
                 nat src_fuel_res src_trace_res
                 Σ box_dc rho e f' Hlt0).
      + assert (Hlt_step : f' - fuel_exp e < f) by lia.
        destruct (IHstep _ Hlt_step) as [t_oot Hoot].
        exists (t_oot + anf_trace_exp e).
        assert (Heqf : f' = ((f' - fuel_exp e) + fuel_exp e)) by lia.
        rewrite Heqf.
        exact (@fuel_sem.eval_step
                 nat src_fuel_res src_trace_res
                 Σ box_dc rho e fuel_sem.OOT (f' - fuel_exp e) t_oot Hoot).
  Qed.

  Lemma src_eval_lt_OOT rho e v f t f' :
    src_eval rho e (fuel_sem.Val v) f t ->
    f' < f ->
    exists t', src_eval rho e fuel_sem.OOT f' t'.
  Proof.
    intros Heval Hlt. eapply src_eval_lt_OOT_any; eauto.
  Qed.

  Lemma src_eval_val_oot_absurd rho0 e0 v0 f0 t_val t_oot :
    src_eval rho0 e0 (fuel_sem.Val v0) f0 t_val ->
    src_eval rho0 e0 fuel_sem.OOT f0 t_oot ->
    False.
  Proof.
    intros Hval Hoot.
    pose proof (src_eval_val_gt_oot _ _ _ _ _ Hval _ _ Hoot).
    lia.
  Qed.

  Lemma src_eval_app_oot_body_if_fun_arg_val_no_body_val
        rho e1 e2 rho' na body v2 f1 t1 f2 t2 f t :
    src_eval rho e1 (fuel_sem.Val (fuel_sem.Clos_v rho' na body)) f1 t1 ->
    src_eval rho e2 (fuel_sem.Val v2) f2 t2 ->
    (forall src_v f' t',
        ~ src_eval (v2 :: rho') body (fuel_sem.Val src_v) f' t') ->
    src_eval rho (EAst.tApp e1 e2) fuel_sem.OOT (f1 + f2 + f + 1) t ->
    exists t3, src_eval (v2 :: rho') body fuel_sem.OOT f t3.
  Proof.
    intros He1 He2 Hnoval Hoot_app.
    inversion Hoot_app; subst.
    - simpl in H. lia.
    - remember (EAst.tApp e1 e2) as e_app in H3.
      remember fuel_sem.OOT as r_oot in H3.
      destruct H3; try discriminate.
      + injection Heqe_app as <- <-. subst.
        pose proof (eval_val_exact_det _ _ _ _ _ _ _ _ He1 H0)
          as [Heq1 [-> ->]].
        injection Heq1 as <- <- <-.
        pose proof (eval_val_exact_det _ _ _ _ _ _ _ _ He2 H1)
          as [-> [-> ->]].
        assert (Hff : f = f4).
        { simpl in H. lia. }
        rewrite Hff. exists t4. exact H2.
      + injection Heqe_app as <- <-. subst.
        pose proof (src_eval_val_gt_oot _ _ _ _ _ He1 _ _ H0) as Hlt_fun.
        simpl in H. lia.
      + injection Heqe_app as <- <-. subst.
        pose proof (eval_val_exact_det _ _ _ _ _ _ _ _ He1 H0)
          as [_ [-> ->]].
        pose proof (src_eval_val_gt_oot _ _ _ _ _ He2 _ _ H1) as Hlt_arg.
        simpl in H. lia.
      + injection Heqe_app as <- <-. subst.
        pose proof (eval_val_exact_det _ _ _ _ _ _ _ _ He1 H0)
          as [Heq1 _].
        discriminate.
  Qed.

  Lemma src_not_stuck_app_body rho e1 e2 rho' na body v2 f1 t1 f2 t2 :
    src_eval rho e1 (fuel_sem.Val (fuel_sem.Clos_v rho' na body)) f1 t1 ->
    src_eval rho e2 (fuel_sem.Val v2) f2 t2 ->
    src_not_stuck rho (EAst.tApp e1 e2) ->
    src_not_stuck (v2 :: rho') body.
  Proof.
    intros He1 He2 Hns.
    destruct (classic (exists src_v f t,
               src_eval (v2 :: rho') body (fuel_sem.Val src_v) f t))
      as [Hval | Hnoval].
    - left. exact Hval.
    - right. intros f.
      destruct Hns as [Happ_val | Hdiv_app].
      + exfalso.
        destruct Happ_val as [src_v [f_app [t_app Happ_val]]].
        destruct (@fuel_sem.src_eval_app_val_body
                    nat src_fuel_res src_trace_res
                    Σ box_dc rho e1 e2 rho' na body v2 src_v
                    f1 t1 f2 t2 f_app t_app He1 He2 Happ_val)
          as [f3 [t3 Hbody_val]].
        apply Hnoval. eexists _, _, _. exact Hbody_val.
      + destruct (Hdiv_app (f1 + f2 + f + 1)) as [t_app Hoot_app].
        eapply src_eval_app_oot_body_if_fun_arg_val_no_body_val.
        * exact He1.
        * exact He2.
        * intros src_v f' t' Hbody_val.
          apply Hnoval. eexists _, _, _. exact Hbody_val.
        * exact Hoot_app.
  Qed.

  Lemma src_eval_fixapp_oot_body_if_fun_arg_val_no_body_val
        rho e1 e2 rho' idx na mfix body v2 f1 t1 f2 t2 f t :
    src_eval rho e1 (fuel_sem.Val (fuel_sem.ClosFix_v rho' mfix idx)) f1 t1 ->
    fuel_sem.fix_body mfix idx = Some (EAst.tLambda na body) ->
    src_eval rho e2 (fuel_sem.Val v2) f2 t2 ->
    (forall src_v f' t',
        ~ src_eval (v2 :: fuel_sem.make_rec_env mfix rho') body
                   (fuel_sem.Val src_v) f' t') ->
    src_eval rho (EAst.tApp e1 e2) fuel_sem.OOT (f1 + f2 + f + 1) t ->
    exists t3, src_eval (v2 :: fuel_sem.make_rec_env mfix rho') body fuel_sem.OOT f t3.
  Proof.
    intros He1 Hfix He2 Hnoval Hoot_app.
    rename Hfix into Hfix_saved.
    inversion Hoot_app; subst.
    - simpl in H. lia.
    - remember (EAst.tApp e1 e2) as e_app in H3.
      remember fuel_sem.OOT as r_oot in H3.
      destruct H3; try discriminate.
      + injection Heqe_app as <- <-. subst.
        pose proof (eval_val_exact_det _ _ _ _ _ _ _ _ He1 H0)
          as [Heq1 _].
        discriminate.
      + injection Heqe_app as <- <-. subst.
        pose proof (src_eval_val_gt_oot _ _ _ _ _ He1 _ _ H0) as Hlt_fun.
        simpl in H. lia.
      + injection Heqe_app as <- <-. subst.
        pose proof (eval_val_exact_det _ _ _ _ _ _ _ _ He1 H0)
          as [_ [-> ->]].
        pose proof (src_eval_val_gt_oot _ _ _ _ _ He2 _ _ H1) as Hlt_arg.
        simpl in H. lia.
      + injection Heqe_app as <- <-. subst.
        pose proof (eval_val_exact_det _ _ _ _ _ _ _ _ He1 H0)
          as [Heq1 [-> ->]].
        injection Heq1 as Hrho Hmfix Hidx.
        rewrite <- Hidx in H1.
        rewrite <- Hmfix in H1.
        rewrite <- Hrho in H4.
        rewrite <- Hmfix in H4.
        rewrite Hfix_saved in H1. injection H1 as <- <-.
        pose proof (eval_val_exact_det _ _ _ _ _ _ _ _ He2 H3)
          as [-> [-> ->]].
        assert (Hff : f = f4).
        { simpl in H. lia. }
        rewrite Hff. exists t4. exact H4.
  Qed.

  Lemma src_not_stuck_fixapp_body rho e1 e2 rho' rho'' idx na mfix body v2 f1 t1 f2 t2 :
    src_eval rho e1 (fuel_sem.Val (fuel_sem.ClosFix_v rho' mfix idx)) f1 t1 ->
    fuel_sem.fix_body mfix idx = Some (EAst.tLambda na body) ->
    fuel_sem.make_rec_env mfix rho' = rho'' ->
    src_eval rho e2 (fuel_sem.Val v2) f2 t2 ->
    src_not_stuck rho (EAst.tApp e1 e2) ->
    src_not_stuck (v2 :: rho'') body.
  Proof.
    intros He1 Hfix Hrec He2 Hns.
    destruct (classic (exists src_v f t,
               src_eval (v2 :: rho'') body (fuel_sem.Val src_v) f t))
      as [Hval | Hnoval].
    - left. exact Hval.
    - right. intros f.
      destruct Hns as [Happ_val | Hdiv_app].
      + exfalso.
        destruct Happ_val as [src_v [f_app [t_app Happ_val]]].
        destruct (@fuel_sem.src_eval_fixapp_val_body
                    nat src_fuel_res src_trace_res
                    Σ box_dc rho e1 e2 rho' idx na mfix body v2 src_v
                    f1 t1 f2 t2 f_app t_app He1 Hfix He2 Happ_val)
          as [f3 [t3 Hbody_val]].
        rewrite Hrec in Hbody_val.
        apply Hnoval. eexists _, _, _. exact Hbody_val.
      + destruct (Hdiv_app (f1 + f2 + f + 1)) as [t_app Hoot_app].
        assert (Hnoval_body :
                  forall src_v f' t',
                    ~ src_eval (v2 :: fuel_sem.make_rec_env mfix rho') body
                               (fuel_sem.Val src_v) f' t').
        { intros src_v f' t' Hbody_val.
          rewrite Hrec in Hbody_val.
          apply Hnoval. eexists _, _, _. exact Hbody_val. }
        destruct (src_eval_fixapp_oot_body_if_fun_arg_val_no_body_val
                    _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
                    He1 Hfix He2 Hnoval_body Hoot_app)
          as [t_body Hbody_oot].
        rewrite Hrec in Hbody_oot.
        exists t_body. exact Hbody_oot.
  Qed.

  Lemma src_eval_case_oot_mch_if_no_mch_val
        rho ind npars mch brs f t :
    (forall src_v f' t', ~ src_eval rho mch (fuel_sem.Val src_v) f' t') ->
    src_eval rho (EAst.tCase (ind, npars) mch brs) fuel_sem.OOT (S f) t ->
    exists t1, src_eval rho mch fuel_sem.OOT f t1.
  Proof.
    intros Hnoval Hoot_case.
    inversion Hoot_case; subst.
    - simpl in H. lia.
    - match goal with
      | [ Hstep : @eval_env_step _ _ _ Σ box_dc rho
                     (EAst.tCase (ind, npars) mch brs) fuel_sem.OOT _ _ |- _ ] =>
          remember (EAst.tCase (ind, npars) mch brs) as e_case in Hstep;
          remember fuel_sem.OOT as r_oot in Hstep;
          destruct Hstep; try discriminate
      end.
      + injection Heqe_case as <- <- <-.
        exfalso. eapply Hnoval. exact H0.
      + injection Heqe_case as <- <- <-.
        assert (f1 = f).
        { cbv [one_i fuel_resource_LambdaBox fuel_exp] in Hoot_case. simpl in Hoot_case. lia. }
        subst f1. exists t1. exact H0.
  Qed.

  Lemma src_not_stuck_case_mch rho ind npars mch brs :
    src_not_stuck rho (EAst.tCase (ind, npars) mch brs) ->
    src_not_stuck rho mch.
  Proof.
    intros Hns.
    destruct (classic (exists src_v f t, src_eval rho mch (fuel_sem.Val src_v) f t))
      as [Hval | Hnoval].
    - left. exact Hval.
    - right. intros f.
      destruct Hns as [Hcase_val | Hdiv_case].
      + exfalso.
        destruct Hcase_val as [src_v [f_case [t_case Hcase_val]]].
        destruct (@fuel_sem.src_eval_case_val_scrut
                    nat src_fuel_res src_trace_res
                    Σ box_dc rho ind npars mch brs src_v f_case t_case Hcase_val)
          as [dc [vs [f1 [t1 Hmch_val]]]].
        apply Hnoval. eexists _, _, _. exact Hmch_val.
      + destruct (Hdiv_case (S f)) as [t_case Hoot_case].
        eapply src_eval_case_oot_mch_if_no_mch_val.
        * intros src_v f' t' Hmch_val. apply Hnoval. eexists _, _, _. exact Hmch_val.
        * exact Hoot_case.
  Qed.

  Lemma src_eval_case_oot_body_if_mch_val_no_body_val
        rho ind npars mch brs dc vs body c f1 t1 f t :
    src_eval rho mch (fuel_sem.Val (fuel_sem.Con_v dc vs)) f1 t1 ->
    dc = dcon_of_con ind c ->
    find_branch ind c (List.length vs) brs = Some body ->
    (forall src_v f' t',
        ~ src_eval ((List.rev vs) ++ rho) body (fuel_sem.Val src_v) f' t') ->
    src_eval rho (EAst.tCase (ind, npars) mch brs) fuel_sem.OOT (f1 + f + 1) t ->
    exists t2, src_eval ((List.rev vs) ++ rho) body fuel_sem.OOT f t2.
  Proof.
    intros Hmch Hdc Hfind Hnoval Hoot_case.
    inversion Hoot_case; subst.
    - simpl in H. lia.
    - match goal with
      | [ Hstep : @eval_env_step _ _ _ Σ box_dc rho
                     (EAst.tCase (ind, npars) mch brs) fuel_sem.OOT _ _ |- _ ] =>
          remember (EAst.tCase (ind, npars) mch brs) as e_case in Hstep;
          remember fuel_sem.OOT as r_oot in Hstep;
          destruct Hstep; try discriminate
      end.
      + injection Heqe_case as <- <- <-.
        pose proof (eval_val_exact_det _ _ _ _ _ _ _ _ Hmch H0)
          as [Heq_con [-> ->]].
        assert (vs0 = vs) by congruence. subst vs0.
        assert (c0 = c).
        { assert (Hde : dcon_of_con ind0 c = dcon_of_con ind0 c0) by congruence.
          unfold dcon_of_con in Hde. injection Hde as HN.
          now apply Nnat.Nat2N.inj. }
        subst c0.
        subst brs0.
        rewrite Hfind in H2. injection H2 as <-.
        rewrite Heqr_oot in H3.
        assert (f2 = f).
        { cbv [one_i fuel_resource_LambdaBox fuel_exp] in Hoot_case. simpl in Hoot_case.
          simpl in H. lia. }
        subst f2. exists t2. exact H3.
      + injection Heqe_case as <- <- <-.
        pose proof (src_eval_val_gt_oot _ _ _ _ _ Hmch _ _ H0) as Hlt_mch.
        cbv [one_i fuel_resource_LambdaBox fuel_exp] in Hoot_case. simpl in Hoot_case. lia.
  Qed.

  Lemma src_not_stuck_case_body
        rho ind npars mch brs dc vs body c f1 t1 :
    src_eval rho mch (fuel_sem.Val (fuel_sem.Con_v dc vs)) f1 t1 ->
    dc = dcon_of_con ind c ->
    find_branch ind c (List.length vs) brs = Some body ->
    src_not_stuck rho (EAst.tCase (ind, npars) mch brs) ->
    src_not_stuck ((List.rev vs) ++ rho) body.
  Proof.
    intros Hmch Hdc Hfind Hns.
    destruct (classic (exists src_v f t,
               src_eval ((List.rev vs) ++ rho) body (fuel_sem.Val src_v) f t))
      as [Hval | Hnoval].
    - left. exact Hval.
    - right. intros f.
      destruct Hns as [Hcase_val | Hdiv_case].
      + exfalso.
        destruct Hcase_val as [src_v [f_case [t_case Hcase_val]]].
        destruct (@fuel_sem.src_eval_case_val_body
                    nat src_fuel_res src_trace_res
                    Σ box_dc rho ind npars mch brs dc vs body c src_v
                    f1 t1 f_case t_case Hmch Hdc Hfind Hcase_val)
          as [f2 [t2 Hbody_val]].
        apply Hnoval. eexists _, _, _. exact Hbody_val.
      + destruct (Hdiv_case (f1 + f + 1)) as [t_case Hoot_case].
        eapply src_eval_case_oot_body_if_mch_val_no_body_val.
        * exact Hmch.
        * exact Hdc.
        * exact Hfind.
        * intros src_v f' t' Hbody_val. apply Hnoval. eexists _, _, _. exact Hbody_val.
        * exact Hoot_case.
  Qed.

  Lemma src_eval_proj_oot_scrut_if_no_scrut_val rho p c f t :
    (forall src_v f' t', ~ src_eval rho c (fuel_sem.Val src_v) f' t') ->
    src_eval rho (EAst.tProj p c) fuel_sem.OOT (S f) t ->
    exists t1, src_eval rho c fuel_sem.OOT f t1.
  Proof.
    intros Hnoval Hoot_proj.
    inversion Hoot_proj; subst.
    - simpl in H. lia.
    - match goal with
      | [ Hstep : @eval_env_step _ _ _ Σ box_dc rho
                     (EAst.tProj p c) fuel_sem.OOT _ _ |- _ ] =>
          remember (EAst.tProj p c) as e_proj in Hstep;
          remember fuel_sem.OOT as r_oot in Hstep;
          destruct Hstep; try discriminate
      end.
      + injection Heqe_proj as <- <-.
        assert (f1 = f).
        { cbv [one_i fuel_resource_LambdaBox fuel_exp] in Hoot_proj. simpl in Hoot_proj. lia. }
        subst f1. exists t1. exact H0.
  Qed.

  Lemma src_not_stuck_proj_scrut rho p c :
    src_not_stuck rho (EAst.tProj p c) ->
    src_not_stuck rho c.
  Proof.
    intros Hns.
    destruct (classic (exists src_v f t, src_eval rho c (fuel_sem.Val src_v) f t))
      as [Hval | Hnoval].
    - left. exact Hval.
    - right. intros f.
      destruct Hns as [Hproj_val | Hdiv_proj].
      + exfalso.
        destruct Hproj_val as [src_v [f_proj [t_proj Hproj_val]]].
        destruct (@fuel_sem.src_eval_proj_val_scrut
                    nat src_fuel_res src_trace_res
                    Σ box_dc rho p c src_v f_proj t_proj Hproj_val)
          as [vs [f1 [t1 Hc_val]]].
        apply Hnoval. eexists _, _, _. exact Hc_val.
      + destruct (Hdiv_proj (S f)) as [t_proj Hoot_proj].
        eapply src_eval_proj_oot_scrut_if_no_scrut_val.
        * intros src_v f' t' Hc_val. apply Hnoval. eexists _, _, _. exact Hc_val.
        * exact Hoot_proj.
  Qed.

  Lemma compare_marked_splits {A}
        (done1 done2 rest1 rest2 : list A) (x y : A) :
    done1 ++ x :: rest1 = done2 ++ y :: rest2 ->
    (exists prefix, done1 = done2 ++ y :: prefix) \/
    (done1 = done2 /\ x = y /\ rest1 = rest2) \/
    (exists prefix, done2 = done1 ++ x :: prefix).
  Proof.
    revert done2.
    induction done1 as [| a done1 IH]; intros done2 Heq.
    - destruct done2 as [| b done2].
      + simpl in Heq. injection Heq as <- <-.
        right. left. repeat split; reflexivity.
      + simpl in Heq. injection Heq as <- _.
        right. right. exists done2. reflexivity.
    - destruct done2 as [| b done2].
      + simpl in Heq. injection Heq as <- _.
        left. exists done1. reflexivity.
      + simpl in Heq. injection Heq as <- Heq'.
        specialize (IH _ Heq').
        destruct IH as [Hearly | [Hsame | Hlate]].
        * left. destruct Hearly as [prefix Hprefix].
          exists prefix. simpl. now rewrite Hprefix.
        * destruct Hsame as [-> [-> ->]].
          right. left. repeat split; reflexivity.
        * right. right. destruct Hlate as [prefix Hprefix].
          exists prefix. simpl. now rewrite Hprefix.
  Qed.

  Lemma src_eval_construct_oot_arg_if_prefix_val_no_arg_val
        (rho : fuel_sem.env) (ind : inductive) (c : nat)
        (args_done : list EAst.term) (e : EAst.term) (args_rest : list EAst.term)
        (vs_done : list fuel_sem.value) (fs ts f t : nat) :
    @fuel_sem.eval_fuel_many nat src_fuel_res src_trace_res
                             Σ box_dc rho args_done vs_done fs ts ->
    (forall src_v f' t', ~ src_eval rho e (fuel_sem.Val src_v) f' t') ->
    src_eval rho (EAst.tConstruct ind c (args_done ++ e :: args_rest))
                 fuel_sem.OOT (fs + f + 1) t ->
    exists t_e, src_eval rho e fuel_sem.OOT f t_e.
  Proof.
    intros Hdone Hnoval Hoot_con.
    inversion Hoot_con; subst.
    - simpl in H. lia.
    - remember (EAst.tConstruct ind c (args_done ++ e :: args_rest)) as e_con in H3.
      remember fuel_sem.OOT as r_oot in H3.
      destruct H3; try discriminate;
        try match goal with
            | [ Hr : fuel_sem.Val _ = fuel_sem.OOT |- _ ] => discriminate
            end.
      inversion Heqe_con; subst; clear Heqe_con.
      destruct (compare_marked_splits args_done args_done0 args_rest args_rest0 e e0 (eq_sym H6))
        as [Hearly | [Hsame | Hlate]].
      + destruct Hearly as [prefix Hprefix].
        rewrite Hprefix in Hdone.
        edestruct (@fuel_sem.eval_many_app_inv
                      nat src_fuel_res src_trace_res
                      Σ box_dc rho args_done0 e0 prefix _ _ _ Hdone)
          as (vs_before & v_bad & vs_after & fs_before & f_val & fs_after &
              ts_before & t_val & ts_after &
              _ & Hmany_before & Hval_bad & Hmany_after & Hfs_done & _).
        pose proof (@fuel_sem.eval_many_exact_det
                      nat src_fuel_res src_trace_res
                      Σ box_dc rho args_done0 _ _ _ _ _ _ H1 Hmany_before)
          as [_ [Hfs_prefix _]].
        pose proof (src_eval_val_gt_oot _ _ _ _ _ Hval_bad _ _ H2) as Hlt_bad.
        rewrite <- Hfs_prefix in Hfs_done.
        rewrite Hfs_done in H.
        simpl in H. lia.
      + destruct Hsame as [-> [-> ->]].
        pose proof (@fuel_sem.eval_many_exact_det
                      nat src_fuel_res src_trace_res
                      Σ box_dc rho _ _ _ _ _ _ _ H1 Hdone)
          as [_ [Hfs_eq _]].
        simpl in H. subst fs0.
        assert (Hff : f = f0) by lia.
        rewrite Hff. exists t. exact H2.
      + destruct Hlate as [prefix Hprefix].
        rewrite Hprefix in H1.
        edestruct (@fuel_sem.eval_many_app_inv
                      nat src_fuel_res src_trace_res
                      Σ box_dc rho args_done e prefix _ _ _ H1)
          as (vs_before & v_bad & vs_after & fs_before & f_val & fs_after &
              ts_before & t_val & ts_after &
              _ & _ & Hval_bad & _ & _ & _).
        exfalso. eapply Hnoval. exact Hval_bad.
  Qed.

  Lemma src_not_stuck_construct_arg
        (rho : fuel_sem.env) (ind : inductive) (c : nat)
        (args_done : list EAst.term) (e : EAst.term) (args_rest : list EAst.term)
        (vs_done : list fuel_sem.value) (fs ts : nat) :
    @fuel_sem.eval_fuel_many nat src_fuel_res src_trace_res
                             Σ box_dc rho args_done vs_done fs ts ->
    src_not_stuck rho (EAst.tConstruct ind c (args_done ++ e :: args_rest)) ->
    src_not_stuck rho e.
  Proof.
    intros Hdone Hns.
    destruct (classic (exists src_v f t, src_eval rho e (fuel_sem.Val src_v) f t))
      as [Hval | Hnoval].
    - left. exact Hval.
    - right. intros f.
      destruct Hns as [Hcon_val | Hdiv_con].
      + exfalso.
        destruct Hcon_val as [src_v [f_con [t_con Hcon_val]]].
        destruct (@fuel_sem.src_eval_construct_val_arg
                    nat src_fuel_res src_trace_res
                    Σ box_dc rho ind c args_done e args_rest src_v
                    f_con t_con Hcon_val)
          as [v_e [f_e [t_e Hval_e]]].
        apply Hnoval. eexists _, _, _. exact Hval_e.
      + destruct (Hdiv_con (fs + f + 1)) as [t_con Hoot_con].
        eapply src_eval_construct_oot_arg_if_prefix_val_no_arg_val.
        * exact Hdone.
        * intros src_v f' t' Hval_e.
          apply Hnoval. eexists _, _, _. exact Hval_e.
        * exact Hoot_con.
  Qed.

  (* This is the actual target statement for the separate divergence proof.
     It is generalized over the target continuation [e_k], because the
     application/fixpoint recursive calls need non-trivial continuations rather
     than just [Ehalt x]. *)
  Definition anf_cvt_correct_oot_lower_bound_goal
             (vs : fuel_sem.env) (e : EAst.term) (f : nat) :=
    forall rho vnames C x S S',
      well_formed_env Σ vs ->
      wellformed Σ (List.length vnames) e = true ->
      env_consistent vnames vs ->
      cmap_consistent' vnames vs ->
      Disjoint _ (FromList vnames) S ->
      Disjoint _ (cmap_vars cmap) S ->
      anf_env_rel' vnames vs rho ->
      global_env_rel' (kn_deps e) rho ->
      anf_cvt_rel' S e vnames S' C x ->
      forall e_k,
        Disjoint _ (occurs_free e_k) ((S \\ S') \\ [set x]) ->
        src_not_stuck vs e ->
        exists c,
          f <= c /\
          bstep_fuel cenv rho (C |[ e_k ]|) c eval.OOT tt.

  Lemma Forall_val_rel_exists vs :
    Forall (well_formed_val Σ) vs ->
    exists vs', Forall2 anf_val_rel' vs vs'.
  Proof.
    intros Hwf_vs.
    induction Hwf_vs as [| v vs Hwf_v Hwf_vs IH].
    - exists []. constructor.
    - destruct (val_rel_exists v Hwf_v) as [v' Hv'].
      destruct IH as [vs' Hvs'].
      exists (v' :: vs'). constructor; assumption.
  Qed.

  Lemma eval_fuel_many_preserves_wf rho es vs f t :
    well_formed_env Σ rho ->
    Forall (fun e => wellformed Σ (List.length rho) e = true) es ->
    @eval_fuel_many nat src_fuel_res src_trace_res
                    Σ box_dc rho es vs f t ->
    Forall (well_formed_val Σ) vs.
  Proof.
    intros Hwf_env Hwf_es Hmany.
    revert Hwf_env Hwf_es.
    induction Hmany; intros Hwf_env Hwf_es.
    - constructor.
    - inversion Hwf_es; subst.
      constructor.
      + eapply eval_preserves_wf; eauto.
      + eapply IHHmany; eauto.
  Qed.

  Lemma anf_cvt_rel_args_app_inv S es1 es2 vn S' C xs :
    anf_cvt_rel_args' S (es1 ++ es2) vn S' C xs ->
    exists S'' C1 C2 xs1 xs2,
      xs = xs1 ++ xs2 /\
      C = comp_ctx_f C1 C2 /\
      anf_cvt_rel_args' S es1 vn S'' C1 xs1 /\
      anf_cvt_rel_args' S'' es2 vn S' C2 xs2.
  Proof.
    revert S vn S' C xs es2.
    induction es1 as [| e es1 IH]; intros S vn S' C xs es2 Hcvt.
    - exists S, Hole_c, C, [], xs.
      simpl. repeat split; try reflexivity; try assumption.
      constructor.
    - simpl in Hcvt.
      inversion Hcvt
        as [| S1 S2 S3 vn0 t ts C1 x1 C2 xs0 Hcvt_hd Hcvt_tl];
        subst.
      destruct (IH _ _ _ _ _ _ Hcvt_tl)
        as [S'' [C1' [C2' [xs1 [xs2 [Hxs [HC [Hrel1 Hrel2]]]]]]]].
      exists S'', (comp_ctx_f C1 C1'), C2', (x1 :: xs1), xs2.
      split; [simpl; now rewrite Hxs |].
      split; [rewrite HC; symmetry; apply comp_ctx_f_assoc |].
      split; [econstructor; eauto | exact Hrel2].
  Qed.

  Lemma anf_cvt_occurs_free_ctx_args_local S es vn S' C xs :
    anf_cvt_rel_args' S es vn S' C xs ->
    Disjoint _ (FromList vn) S ->
    Disjoint _ (cmap_vars cmap) S ->
    occurs_free_ctx C \subset FromList vn :|: (S \\ S') :|: cmap_vars cmap.
  Proof.
    intros Hcvt. revert S S' C xs Hcvt.
    induction es as [| e0 es' IH]; intros S S' C xs Hcvt Hdis Hdis_cm.
    - remember ([] : list EAst.term) as es_nil.
      destruct Hcvt; try discriminate.
      rewrite occurs_free_Hole_c. intros z Hz. inv Hz.
    - remember (e0 :: es') as es_cons.
      destruct Hcvt; try discriminate.
      injection Heqes_cons as <- <-.
      match goal with
      | [ Hh : anf_cvt_rel _ _ _ _ _ _ _ ?S2m _ _,
          Ht : anf_cvt_rel_args _ _ _ _ ?S2m _ _ _ _ _ |- _ ] =>
        rename Hh into Hcvt_h; rename Ht into Hcvt_t
      end.
      eapply Included_trans; [eapply occurs_free_ctx_comp |].
      eapply Union_Included.
      + eapply Included_trans; [eapply anf_cvt_occurs_free_ctx_exp; eassumption |].
        eapply Included_Union_compat;
          [eapply Included_Union_compat;
            [eapply Included_refl
            | eapply Included_Setminus_compat;
                [eapply Included_refl | eapply anf_cvt_args_subset; eassumption]]
          | eapply Included_refl].
      + eapply Included_trans; [eapply Setminus_Included |].
        match goal with
        | [ Ht : anf_cvt_rel_args _ _ _ _ ?S2m _ _ _ _ _ |- _ ] =>
          eapply Included_trans;
            [eapply IH; [exact Ht
            | eapply Disjoint_Included_r;
                [eapply anf_cvt_exp_subset; eassumption | exact Hdis]
            | eapply Disjoint_Included_r;
                [eapply anf_cvt_exp_subset; eassumption | exact Hdis_cm]] |]
        end.
        eapply Included_Union_compat;
          [eapply Included_Union_compat;
            [eapply Included_refl
            | eapply Included_Setminus_compat;
                [eapply anf_cvt_exp_subset; eassumption | eapply Included_refl]]
          | eapply Included_refl].
  Qed.

  Lemma anf_cvt_correct_exps_proof
        vs_env es vs1 f t :
    @eval_fuel_many nat src_fuel_res src_trace_res
                    Σ box_dc vs_env es vs1 f t ->
    anf_cvt_correct_exps' vs_env es vs1 f t.
  Proof.
    intros Hmany.
    induction Hmany as [| rho0 e0 es0 v0 vs0 f0 fs0 t0 ts0 Heval_e Hmany IH_es].
    - unfold anf_cvt_correct_exps'.
      intros rho_tgt vnames C xs S S' i Hwf _ Hcons Hcmap Hdis Hdis_cmap
             Henv Hglob Hrel e_k vs' Hvs' Hdis_ek.
      inversion Hrel; subst. inversion Hvs'; subst.
      change (Hole_c |[ e_k ]|) with e_k.
      change (set_many [] [] rho_tgt) with rho_tgt.
      eapply (preord_exp_post_monotonic cenv _ eq_fuel).
      { intros [[[? ?] ?] ?] [[[? ?] ?] ?] Heq.
        unfold anf_bound, eq_fuel in *. cbn in *. lia. }
      eapply preord_exp_refl. exact eq_fuel_compat'.
      intros y Hy v1 Hget. eexists. split; [exact Hget |].
      eapply preord_val_refl. tci.
    - unfold anf_cvt_correct_exps' in IH_es |- *.
      intros rho_tgt vnames C xs S S' i Hwf Hwfe Hcons Hcmap Hdis Hdis_cmap
             Henv Hglob Hrel e_k vs' Hvs' Hdis_ek.
      inv Hrel. inv Hvs'.
      match goal with
      | [ Hc : anf_cvt_rel _ _ _ _ S e0 vnames _ _ _ |- _ ] =>
          rename Hc into Hcvt_head
      end.
      match goal with
      | [ Hc : anf_cvt_rel_args _ _ _ _ _ _ _ _ _ _ |- _ ] =>
          rename Hc into Hcvt_tail
      end.
      match goal with
      | [ Hr : anf_val_rel' v0 ?vh |- _ ] => rename Hr into Hrel_head
      end.
      match goal with
      | [ HF : Forall2 anf_val_rel' vs0 ?vs_tl |- _ ] => rename HF into Hrel_tail
      end.
      rewrite <- app_ctx_f_fuse.
      eapply preord_exp_post_monotonic.
      2:{
        eapply preord_exp_trans; [tci | exact eq_fuel_idemp | | ].
        2:{
          intros m.
          assert (Hwfe_e0 : wellformed Σ (Datatypes.length vnames) e0 = true).
          { inversion Hwfe; assumption. }
          assert (Hglob_e0 : global_env_rel' (kn_deps e0) rho_tgt).
          { eapply global_env_rel_mono; [exact Hglob |].
            intros k0 Hk0. unfold kn_deps_list. constructor. exact Hk0. }
          pose proof (anf_cvt_correct
                        func_tag default_tag default_itag tgm cmap cenv Σ
                        dcon_to_tag_inj box_dc box_tag cenv_case_consistent
                        Hcmap_eval_coherent Hglob_term Hglob_fuel_zero Hglob_wf val_rel_exists
                        rho0 e0 (fuel_sem.Val v0) f0 t0 Heval_e)
            as Hcorr_head.
          unfold anf_cvt_correct_exp in Hcorr_head.
          specialize (Hcorr_head rho_tgt vnames C1 x1 S S2 m
                                  Hwf Hwfe_e0 Hcons Hcmap Hdis Hdis_cmap
                                  Henv Hglob_e0 Hcvt_head
                                  (C2 |[ e_k ]|)).
          assert (Hdis_ctx :
                    Disjoint _ (occurs_free (C2 |[ e_k ]|))
                             ((S \\ S2) \\ [set x1])).
          { constructor. intros z Hz.
            inversion Hz as [? Hfree Hset]; subst; clear Hz.
            unfold Ensembles.In in Hfree, Hset.
            destruct Hset as [Hz_SS2 Hneq_x1]. destruct Hz_SS2 as [HS HnS2].
            apply (occurs_free_ctx_app C2 e_k) in Hfree. inv Hfree.
            + match goal with Hctx_z : Ensembles.In _ (occurs_free_ctx _) _ |- _ =>
                assert (Hinc := anf_cvt_occurs_free_ctx_args_local _ _ _ _ _ _
                  Hcvt_tail
                  (Disjoint_Included_r _ _ _ (anf_cvt_exp_subset _ _ _ _ _ _ _ _ _ _ Hcvt_head) Hdis)
                  (Disjoint_Included_r _ _ _ (anf_cvt_exp_subset _ _ _ _ _ _ _ _ _ _ Hcvt_head) Hdis_cmap));
                specialize (Hinc _ Hctx_z); inv Hinc end.
              * match goal with H : Ensembles.In _ _ _ |- _ => inv H end.
                -- match goal with H : Ensembles.In _ (FromList _) _ |- _ =>
                     eapply Hdis; constructor; [exact H | exact HS] end.
                -- match goal with H : Ensembles.In _ (Setminus _ _ _) _ |- _ =>
                     unfold Ensembles.In in H; destruct H as [H _]; exact (HnS2 H) end.
              * match goal with H : Ensembles.In _ (cmap_vars _) _ |- _ =>
                  eapply Hdis_cmap; constructor; [exact H | exact HS] end.
            + match goal with H : Ensembles.In _ (Setminus _ _ _) _ |- _ =>
                unfold Ensembles.In in H; destruct H as [Hfree_ek _] end.
              assert (HnS' : ~ z \in S')
                by (intros Hc; apply HnS2;
                    eapply anf_cvt_args_subset; eassumption).
              assert (Hnxs : ~ z \in FromList xs0).
              { intros Hin_xs.
                unfold FromList, Ensembles.In in Hin_xs.
                destruct (In_nth_error _ _ Hin_xs) as [j Hj].
                change positive with var in Hj.
                destruct (@anf_correct.anf_cvt_rel_args_In_range
                            func_tag default_tag tgm cmap
                            xs0 S2 es0 vnames S' C2
                            Hcvt_tail z (nth_error_In _ _ Hj))
                  as [Hvn | [HS2 | Hcm]].
                - eapply Hdis. constructor; [exact Hvn | exact HS].
                - exact (HnS2 HS2).
                - eapply Hdis_cmap. constructor; [exact Hcm | exact HS]. }
              eapply Hdis_ek. constructor; [exact Hfree_ek |].
              constructor.
              * constructor; [exact HS | exact HnS'].
              * simpl. intros [Heq | Hin]; [subst; apply Hneq_x1; constructor | exact (Hnxs Hin)]. }
          specialize (Hcorr_head Hdis_ctx).
          eapply Hcorr_head; eauto. }
        eapply preord_exp_trans; [tci | exact eq_fuel_idemp | | ].
        2:{
          intros m.
          eapply (IH_es (M.set x1 y rho_tgt) vnames C2 xs0 S2 S' m).
          - exact Hwf.
          - match goal with
            | [ HF : Forall _ (e0 :: es0) |- _ ] => inversion HF; assumption
            end.
          - exact Hcons.
          - exact Hcmap.
          - eapply Disjoint_Included_r;
              [eapply anf_cvt_exp_subset; eassumption | exact Hdis].
          - eapply Disjoint_Included_r;
              [eapply anf_cvt_exp_subset; eassumption | exact Hdis_cmap].
          - eapply anf_env_rel_set; [exact Henv |].
            intros k Hk.
            assert (Hek : nth_error rho0 k = Some v0).
            { eapply anf_cvt_rel_var_lookup;
                [exact Heval_e | exact Hcvt_head
                | exact Hdis | exact Hdis_cmap | exact Hcons | exact Hcmap | exact Hk]. }
            exists v0. split; [exact Hek | exact Hrel_head].
          - intros kn vn0 Hd Hl.
            assert (Hd' : kn_deps_list (e0 :: es0) kn).
            { unfold kn_deps_list. apply Exists_cons_tl. exact Hd. }
            destruct (Hglob kn vn0 Hd' Hl)
              as [d1 [b1 [av [Hd1 [Hb1 [Hgv Hd3]]]]]].
            destruct (Pos.eq_dec vn0 x1) as [-> | Hneq_vn].
            + exists d1, b1, y. repeat (split; [assumption |]).
              split; [rewrite M.gss; reflexivity |].
              intros src_v f' t' Heval_src.
              destruct (anf_cvt_cmap_eval rho0 e0 v0 f0 t0 Heval_e
                          _ _ _ _ _ kn d1 b1
                          Hcvt_head Hdis Hdis_cmap Hcons Hcmap Hl Hd1 Hb1)
                as [f1' [t1' Heval_body_v0]].
              assert (Heq_sv : src_v = v0)
                by (eapply eval_val_exact_det; eassumption).
              subst src_v. exact Hrel_head.
            + exists d1, b1, av. repeat (split; [assumption |]).
              split; [rewrite M.gso; [exact Hgv | exact Hneq_vn] | exact Hd3].
          - exact Hcvt_tail.
          - exact Hrel_tail.
          - eapply Disjoint_Included_r; [| exact Hdis_ek].
            intros z Hz. destruct Hz as [[Hz1 Hz2] Hz3].
            constructor.
            + constructor;
                [eapply anf_cvt_exp_subset; [exact Hcvt_head | exact Hz1] | exact Hz2].
            + simpl. intros [Heq | Hin].
              * subst.
                eapply (@anf_util.anf_cvt_result_not_in_output
                          func_tag default_tag tgm cmap
                          S e0 vnames S2 C1 _); eauto.
              * exact (Hz3 Hin). }
        eapply preord_exp_refl. exact eq_fuel_compat'.
        intros z Hz.
        unfold preord_var_env. intros w Hget.
        destruct (Pos.eq_dec z x1) as [Heq_zx1 | Hneq_zx1].
        * subst z. simpl in Hget. rewrite M.gss in Hget. injection Hget as <-.
          destruct (In_dec Pos.eq_dec x1 xs0) as [Hin_x1 | Hni_x1].
          -- assert (Hlen : Datatypes.length xs0 = Datatypes.length l').
             { transitivity (Datatypes.length es0).
               - eapply anf_cvt_rel_args_length; eassumption.
               - transitivity (Datatypes.length vs0);
                 [symmetry; eapply eval_fuel_many_length; eassumption
                 | eapply Forall2_length; exact Hrel_tail]. }
             destruct (@anf_correct.set_many_get_in
                         func_tag default_tag tgm cmap Σ box_dc box_tag
                         x1 xs0 l' (M.set x1 y rho_tgt) Hin_x1 Hlen)
               as [v_sm Hget_sm].
             eexists. split. { exact Hget_sm. }
             destruct (In_nth_error _ _ Hin_x1) as [k0 Hk0_xs].
             change positive with var in Hk0_xs.
             assert (Hk0_lt : k0 < Datatypes.length xs0).
             { apply (proj1 (nth_error_Some xs0 k0)). rewrite Hk0_xs. discriminate. }
             assert (Hk0_es : exists e_k0, nth_error es0 k0 = Some e_k0).
             { destruct (nth_error es0 k0) eqn:Heq; [eexists; reflexivity | exfalso].
               apply nth_error_None in Heq.
               rewrite (@anf_correct.anf_cvt_rel_args_length
                          func_tag default_tag tgm cmap
                          S2 es0 vnames S' C2 xs0 Hcvt_tail) in Hk0_lt.
               lia. }
             destruct Hk0_es as [e_k0 He_k0].
             assert (Hk0_vs : exists v_k0, nth_error vs0 k0 = Some v_k0).
             { destruct (nth_error vs0 k0) eqn:Heq; [eexists; reflexivity | exfalso].
               apply nth_error_None in Heq.
               pose proof (@anf_correct.anf_cvt_rel_args_length
                             func_tag default_tag tgm cmap
                             S2 es0 vnames S' C2 xs0 Hcvt_tail).
               pose proof (@anf_correct.eval_fuel_many_length
                             default_tag tgm Σ box_dc box_tag
                             rho0 es0 vs0 fs0 ts0 Hmany).
               lia. }
             destruct Hk0_vs as [v_k0 Hv_k0].
             destruct (@anf_correct.anf_cvt_rel_args_nth_cvt
                         func_tag default_tag tgm cmap
                         S2 es0 vnames S' C2 xs0
                         Hcvt_tail k0 e_k0 x1 He_k0 Hk0_xs)
               as [S_k [S_k' [C_k [Hcvt_k Hsub_k]]]].
             destruct (@anf_correct.eval_fuel_many_nth
                         default_tag tgm Σ box_dc box_tag
                         rho0 es0 vs0 fs0 ts0 k0 e_k0 v_k0
                         Hmany He_k0 Hv_k0)
               as [f_k [t_k Heval_k]].
             assert (Hv_eq : v0 = v_k0).
             { destruct (@anf_correct.anf_cvt_result_in_consumed
                           func_tag default_tag tgm cmap
                           S e0 vnames S2 C1 x1 Hcvt_head)
                 as [Hin_vn | [Hin_S | Hin_cm]].
               - unfold FromList, Ensembles.In in Hin_vn.
                 destruct (In_nth_error _ _ Hin_vn) as [i0 Hi0].
                 change positive with var in Hi0.
                 assert (Hv0_i := anf_cvt_rel_var_lookup _ _ _ _ _
                   Heval_e _ _ _ _ _ i0 Hcvt_head Hdis Hdis_cmap Hcons Hcmap Hi0).
                 assert (Hsub_k_S : S_k \subset S)
                   by (eapply Included_trans;
                         [exact Hsub_k | eapply anf_cvt_exp_subset; exact Hcvt_head]).
                 assert (Hvk_i := anf_cvt_rel_var_lookup _ _ _ _ _
                   Heval_k _ _ _ _ _ i0 Hcvt_k
                   (Disjoint_Included_r _ _ _ Hsub_k_S Hdis)
                   (Disjoint_Included_r _ _ _ Hsub_k_S Hdis_cmap)
                   Hcons Hcmap Hi0).
                 congruence.
               - exfalso.
                 assert (Hni : ~ x1 \in S2)
                   by (eapply (@anf_util.anf_cvt_result_not_in_output
                                 func_tag default_tag tgm cmap
                                 S e0 vnames S2 C1 _); eauto).
                 destruct (@anf_correct.anf_cvt_result_in_consumed
                             func_tag default_tag tgm cmap
                             S_k e_k0 vnames S_k' C_k x1 Hcvt_k)
                   as [Hk_vn | [Hk_S | Hk_cm]].
                 + eapply Hdis. constructor; [exact Hk_vn | exact Hin_S].
                 + exact (Hni (Hsub_k _ Hk_S)).
                 + eapply Hdis_cmap. constructor; [exact Hk_cm | exact Hin_S].
               - assert (Hsub_k_S : S_k \subset S)
                   by (eapply Included_trans;
                         [exact Hsub_k | eapply anf_cvt_exp_subset; exact Hcvt_head]).
                 destruct (In_dec Pos.eq_dec x1 vnames) as [Hin_vn' | Hni_vn].
                 + apply In_nth_error in Hin_vn'.
                   destruct Hin_vn' as [i0 Hi0]. change positive with var in Hi0.
                   assert (Hv0_i := anf_cvt_rel_var_lookup _ _ _ _ _
                     Heval_e _ _ _ _ _ i0 Hcvt_head Hdis Hdis_cmap Hcons Hcmap Hi0).
                   assert (Hvk_i := anf_cvt_rel_var_lookup _ _ _ _ _
                     Heval_k _ _ _ _ _ i0 Hcvt_k
                     (Disjoint_Included_r _ _ _ Hsub_k_S Hdis)
                     (Disjoint_Included_r _ _ _ Hsub_k_S Hdis_cmap)
                     Hcons Hcmap Hi0).
                   congruence.
                 + destruct (@anf_correct.anf_cvt_cmap_result_in_deps
                               func_tag default_tag tgm cmap
                               S e0 vnames S2 C1 x1
                               Hcvt_head Hin_cm Hdis Hdis_cmap Hni_vn)
                     as [kn_x [Hlk_x Hdep_x]].
                   assert (Hkn_deps : kn_deps_list (e0 :: es0) kn_x).
                   { unfold kn_deps_list. constructor. exact Hdep_x. }
                   destruct (Hglob kn_x x1 Hkn_deps Hlk_x)
                     as (decl_x & body_x & anf_vx & Hdecl_x & Hbody_x & Hget_x & Hrel_x).
                   assert (Heval_body_e : exists f_ce t_ce,
                     src_eval [] body_x (fuel_sem.Val v0) f_ce t_ce).
                   { eapply anf_cvt_cmap_eval;
                       [exact Heval_e | exact Hcvt_head | exact Hdis | exact Hdis_cmap
                       | exact Hcons | exact Hcmap | exact Hlk_x
                       | exact Hdecl_x | exact Hbody_x]. }
                   assert (Heval_body_k : exists f_ck t_ck,
                     src_eval [] body_x (fuel_sem.Val v_k0) f_ck t_ck).
                   { eapply anf_cvt_cmap_eval;
                       [exact Heval_k | exact Hcvt_k
                       | exact (Disjoint_Included_r _ _ _ Hsub_k_S Hdis)
                       | exact (Disjoint_Included_r _ _ _ Hsub_k_S Hdis_cmap)
                       | exact Hcons | exact Hcmap | exact Hlk_x
                       | exact Hdecl_x | exact Hbody_x]. }
                   destruct Heval_body_e as [f_ce [t_ce Heval_ce]].
                   destruct Heval_body_k as [f_ck [t_ck Heval_ck]].
                   eapply eval_val_det; eassumption. }
             subst v_k0.
             destruct (@anf_correct.set_many_In_nth
                         func_tag default_tag tgm cmap Σ box_dc box_tag
                         x1 xs0 l' (M.set x1 y rho_tgt) v_sm Hget_sm Hin_x1 Hlen)
               as [j [Hj_xs Hj_vs]].
             assert (Hj_vs0 : exists v_j, nth_error vs0 j = Some v_j /\ anf_val_rel' v_j v_sm).
             { eapply Forall2_nth_error_r; [exact Hrel_tail | exact Hj_vs]. }
             destruct Hj_vs0 as [v_j [Hv_j Hrel_j]].
             assert (Hj_lt : j < Datatypes.length xs0).
             { apply (proj1 (nth_error_Some xs0 j)). rewrite Hj_xs. discriminate. }
             assert (Hj_es : exists e_j, nth_error es0 j = Some e_j).
             { destruct (nth_error es0 j) eqn:Heq; [eexists; reflexivity | exfalso].
               apply nth_error_None in Heq.
               rewrite (@anf_correct.anf_cvt_rel_args_length
                          func_tag default_tag tgm cmap
                          S2 es0 vnames S' C2 xs0 Hcvt_tail) in Hj_lt.
               lia. }
             destruct Hj_es as [e_j He_j].
             assert (Hv_j_eq : v0 = v_j).
             { destruct (@anf_correct.anf_cvt_rel_args_nth_cvt
                           func_tag default_tag tgm cmap
                           S2 es0 vnames S' C2 xs0
                           Hcvt_tail j e_j x1 He_j Hj_xs)
                 as [S_j [S_j' [C_j [Hcvt_j Hsub_j]]]].
               destruct (@anf_correct.eval_fuel_many_nth
                           default_tag tgm Σ box_dc box_tag
                           rho0 es0 vs0 fs0 ts0 j e_j v_j
                           Hmany He_j Hv_j)
                 as [f_j [t_j Heval_j]].
               assert (Hsub_j_S : S_j \subset S)
                 by (eapply Included_trans;
                       [exact Hsub_j | eapply anf_cvt_exp_subset; exact Hcvt_head]).
               destruct (@anf_correct.anf_cvt_result_in_consumed
                           func_tag default_tag tgm cmap
                           S e0 vnames S2 C1 x1 Hcvt_head)
                 as [Hin_vn | [Hin_S | Hin_cm]].
               - unfold FromList, Ensembles.In in Hin_vn.
                 destruct (In_nth_error _ _ Hin_vn) as [i0 Hi0].
                 change positive with var in Hi0.
                 assert (Hv0_i := anf_cvt_rel_var_lookup _ _ _ _ _
                   Heval_e _ _ _ _ _ i0 Hcvt_head Hdis Hdis_cmap Hcons Hcmap Hi0).
                 assert (Hvj_i := anf_cvt_rel_var_lookup _ _ _ _ _
                   Heval_j _ _ _ _ _ i0 Hcvt_j
                   (Disjoint_Included_r _ _ _ Hsub_j_S Hdis)
                   (Disjoint_Included_r _ _ _ Hsub_j_S Hdis_cmap)
                   Hcons Hcmap Hi0).
                 congruence.
               - exfalso.
                 assert (Hni : ~ x1 \in S2)
                   by (eapply (@anf_util.anf_cvt_result_not_in_output
                                 func_tag default_tag tgm cmap
                                 S e0 vnames S2 C1 _); eauto).
                 destruct (@anf_correct.anf_cvt_result_in_consumed
                             func_tag default_tag tgm cmap
                             S_j e_j vnames S_j' C_j x1 Hcvt_j)
                   as [Hj_vn | [Hj_S | Hj_cm]].
                 + eapply Hdis. constructor; [exact Hj_vn | exact Hin_S].
                 + exact (Hni (Hsub_j _ Hj_S)).
                 + eapply Hdis_cmap. constructor; [exact Hj_cm | exact Hin_S].
               - destruct (In_dec Pos.eq_dec x1 vnames) as [Hin_vn' | Hni_vn].
                 + apply In_nth_error in Hin_vn'.
                   destruct Hin_vn' as [i0 Hi0]. change positive with var in Hi0.
                   assert (Hv0_i := anf_cvt_rel_var_lookup _ _ _ _ _
                     Heval_e _ _ _ _ _ i0 Hcvt_head Hdis Hdis_cmap Hcons Hcmap Hi0).
                   assert (Hvj_i := anf_cvt_rel_var_lookup _ _ _ _ _
                     Heval_j _ _ _ _ _ i0 Hcvt_j
                     (Disjoint_Included_r _ _ _ Hsub_j_S Hdis)
                     (Disjoint_Included_r _ _ _ Hsub_j_S Hdis_cmap)
                     Hcons Hcmap Hi0).
                   congruence.
                 + destruct (@anf_correct.anf_cvt_cmap_result_in_deps
                               func_tag default_tag tgm cmap
                               S e0 vnames S2 C1 x1
                               Hcvt_head Hin_cm Hdis Hdis_cmap Hni_vn)
                     as [kn_x [Hlk_x Hdep_x]].
                   assert (Hkn_deps : kn_deps_list (e0 :: es0) kn_x).
                   { unfold kn_deps_list. constructor. exact Hdep_x. }
                   destruct (Hglob kn_x x1 Hkn_deps Hlk_x)
                     as (decl_x & body_x & anf_vx & Hdecl_x & Hbody_x & Hget_x & Hrel_x).
                   assert (Heval_body_e : exists f_ce t_ce,
                     src_eval [] body_x (fuel_sem.Val v0) f_ce t_ce).
                   { eapply anf_cvt_cmap_eval;
                       [exact Heval_e | exact Hcvt_head | exact Hdis | exact Hdis_cmap
                       | exact Hcons | exact Hcmap | exact Hlk_x
                       | exact Hdecl_x | exact Hbody_x]. }
                   assert (Heval_body_j : exists f_cj t_cj,
                     src_eval [] body_x (fuel_sem.Val v_j) f_cj t_cj).
                   { eapply anf_cvt_cmap_eval;
                       [exact Heval_j | exact Hcvt_j
                       | exact (Disjoint_Included_r _ _ _ Hsub_j_S Hdis)
                       | exact (Disjoint_Included_r _ _ _ Hsub_j_S Hdis_cmap)
                       | exact Hcons | exact Hcmap | exact Hlk_x
                       | exact Hdecl_x | exact Hbody_x]. }
                   destruct Heval_body_e as [f_ce [t_ce Heval_ce]].
                   destruct Heval_body_j as [f_cj [t_cj Heval_cj]].
                   eapply eval_val_det; eassumption. }
             subst v_j.
             eapply (@anf_cvt_val_alpha_equiv
                       _ _ _ _ eq_fuel eq_fuel tgm cmap cenv
                       eq_fuel_compat' (fun _ _ H => H)
                       nat src_fuel_res src_trace_res
                       Σ box_dc Hglob_term func_tag default_tag);
               [exact Hrel_head | exact Hrel_j].
          -- eexists. split.
            { rewrite (@anf_correct.set_many_get_notin
                         x1 xs0 l' (M.set x1 y rho_tgt)); [| exact Hni_x1].
              rewrite M.gss. reflexivity. }
             eapply preord_val_refl. tci.
        * simpl in Hget. rewrite M.gso in Hget; [| exact Hneq_zx1].
          eexists. split.
          { rewrite set_many_set_neq_base; [| exact Hneq_zx1]. exact Hget. }
          eapply preord_val_refl. tci. }
      { unfold inclusion, comp, anf_bound, eq_fuel.
        intros [[[? ?] ?] ?] [[[? ?] ?] ?] Hcomp.
        repeat match goal with
        | [ H : exists _, _ |- _ ] => destruct H
        | [ H : _ /\ _ |- _ ] => destruct H
        | [ p : _ * _ * _ * _ |- _ ] => destruct p
        end.
        repeat match goal with
        | [ p : _ * _ |- _ ] => destruct p
        end.
        unfold zero, one_ctx, algebra.one, one_i, algebra.HRes,
               HRexp_f, fuel_res, fuel_res_exp, fuel_res_pre,
               HRexp_t, trace_res, trace_res_exp, trace_res_pre in *.
        cbn in *. lia. }
  Qed.

  Lemma anf_env_rel_set_many_args
        rho_src es vs_src f t :
    @eval_fuel_many nat src_fuel_res src_trace_res
                    Σ box_dc rho_src es vs_src f t ->
    forall rho_tgt vnames S S' C xs vs_tgt,
      env_consistent vnames rho_src ->
      cmap_consistent' vnames rho_src ->
      Disjoint _ (FromList vnames) S ->
      Disjoint _ (cmap_vars cmap) S ->
      anf_env_rel' vnames rho_src rho_tgt ->
      anf_cvt_rel_args' S es vnames S' C xs ->
      Forall2 anf_val_rel' vs_src vs_tgt ->
      anf_env_rel' vnames rho_src (set_many xs vs_tgt rho_tgt).
  Proof.
    intros Hmany.
    induction Hmany as
        [| rho0 e0 es0 v0 vs0 f0 fs0 t0 ts0 Heval_e Hmany IH];
      intros rho_tgt vnames S S' C xs vs_tgt
             Hcons Hcmap Hdis Hdis_cmap Henv Hrel Hvs_tgt.
    - inv Hrel. inv Hvs_tgt. exact Henv.
    - inv Hrel. inv Hvs_tgt.
      eapply anf_env_rel_set.
      + eapply IH.
        * exact Hcons.
        * exact Hcmap.
        * eapply Disjoint_Included_r;
            [eapply anf_cvt_exp_subset; eassumption | exact Hdis].
        * eapply Disjoint_Included_r;
            [eapply anf_cvt_exp_subset; eassumption | exact Hdis_cmap].
        * exact Henv.
        * exact H7.
        * exact H4.
      + intros k Hk.
        assert (Hsrc : nth_error rho0 k = Some v0).
        { eapply anf_cvt_rel_var_lookup;
            [exact Heval_e | exact H2
            | exact Hdis | exact Hdis_cmap | exact Hcons | exact Hcmap | exact Hk]. }
        exists v0. split; [exact Hsrc | exact H1].
  Qed.

  Lemma global_env_rel_set_many_args
        rho_src es vs_src f t :
    @eval_fuel_many nat src_fuel_res src_trace_res
                    Σ box_dc rho_src es vs_src f t ->
    forall rho_tgt vnames S S' C xs vs_tgt D,
      env_consistent vnames rho_src ->
      cmap_consistent' vnames rho_src ->
      Disjoint _ (FromList vnames) S ->
      Disjoint _ (cmap_vars cmap) S ->
      global_env_rel' D rho_tgt ->
      anf_cvt_rel_args' S es vnames S' C xs ->
      Forall2 anf_val_rel' vs_src vs_tgt ->
      global_env_rel' D (set_many xs vs_tgt rho_tgt).
  Proof.
    intros Hmany.
    induction Hmany as
        [| rho0 e0 es0 v0 vs0 f0 fs0 t0 ts0 Heval_e Hmany IH];
      intros rho_tgt vnames S S' C xs vs_tgt D
             Hcons Hcmap Hdis Hdis_cmap Hglob Hrel Hvs_tgt.
    - inv Hrel. inv Hvs_tgt. exact Hglob.
    - inv Hrel. inv Hvs_tgt.
      eapply global_env_rel_set.
      + eapply IH.
        * exact Hcons.
        * exact Hcmap.
        * eapply Disjoint_Included_r;
            [eapply anf_cvt_exp_subset; eassumption | exact Hdis].
        * eapply Disjoint_Included_r;
            [eapply anf_cvt_exp_subset; eassumption | exact Hdis_cmap].
        * exact Hglob.
        * exact H7.
        * exact H4.
      + intros kn Hd Hlk decl body Hdecl Hbody src_v f_s t_s Heval_src.
        destruct (anf_cvt_cmap_eval rho0 e0 v0 f0 t0 Heval_e
                    _ _ _ _ _ kn decl body
                    H2 Hdis Hdis_cmap Hcons Hcmap Hlk Hdecl Hbody)
          as [f_body [t_body Heval_body]].
        assert (src_v = v0) by (eapply eval_val_exact_det; eassumption).
        subst src_v. exact H1.
  Qed.

  Lemma anf_cvt_correct_exps_oot
        vs_env es vs1 f t rho vnames C xs S S' e_k vs' c :
    @eval_fuel_many nat src_fuel_res src_trace_res
                    Σ box_dc vs_env es vs1 f t ->
    well_formed_env Σ vs_env ->
    Forall (fun e => wellformed Σ (List.length vnames) e = true) es ->
    env_consistent vnames vs_env ->
    cmap_consistent' vnames vs_env ->
    Disjoint _ (FromList vnames) S ->
    Disjoint _ (cmap_vars cmap) S ->
    anf_env_rel' vnames vs_env rho ->
    global_env_rel' (kn_deps_list es) rho ->
    anf_cvt_rel_args' S es vnames S' C xs ->
    Forall2 anf_val_rel' vs1 vs' ->
    Disjoint _ (occurs_free e_k) ((S \\ S') \\ FromList xs) ->
    bstep_fuel cenv (set_many xs vs' rho) e_k c eval.OOT tt ->
    exists c',
      (f + c <= c')%nat /\
      bstep_fuel cenv rho (C |[ e_k ]|) c' eval.OOT tt.
  Proof.
    intros Hmany Hwf Hwfe Hcons Hcmap Hdis Hdis_cmap Henv Hglob Hrel
           Hvs' Hdis_ek Hoot.
    pose proof (anf_cvt_correct_exps_proof _ _ _ _ _ Hmany) as Hcorr.
    unfold anf_cvt_correct_exps' in Hcorr.
    destruct (Hcorr rho vnames C xs S S' c
                    Hwf Hwfe Hcons Hcmap Hdis Hdis_cmap Henv Hglob Hrel
                    e_k vs' Hvs' Hdis_ek
                    eval.OOT c tt (le_n _) Hoot)
      as [vres [c' [cout [Hbstep [Hpost Hres]]]]].
    destruct vres.
    - destruct cout.
      exists c'. split; [| exact Hbstep].
      unfold anf_bound in Hpost. simpl in Hpost. lia.
    - simpl in Hres. contradiction.
  Qed.

  (* This is the termination bridge used by the separate lower-bound OOT proof:
     a successful source prefix can be plugged into any target continuation. *)
  Lemma anf_cvt_correct_val_cont
        vs e v f t rho vnames C x S S' i e_k v' :
    well_formed_env Σ vs ->
    wellformed Σ (List.length vnames) e = true ->
    env_consistent vnames vs ->
    cmap_consistent' vnames vs ->
    Disjoint _ (FromList vnames) S ->
    Disjoint _ (cmap_vars cmap) S ->
    anf_env_rel' vnames vs rho ->
    global_env_rel' (kn_deps e) rho ->
    anf_cvt_rel' S e vnames S' C x ->
    Disjoint _ (occurs_free e_k) ((S \\ S') \\ [set x]) ->
    src_eval vs e (fuel_sem.Val v) f t ->
    anf_val_rel' v v' ->
    preord_exp cenv (anf_bound f t) eq_fuel i
               (e_k, M.set x v' rho) (C |[ e_k ]|, rho).
  Proof.
    intros Hwf Hwfe Hcons Hcmap Hdis Hdis_cmap Henv Hglob Hrel Hdis_ek Heval Hvrel.
    pose proof (anf_cvt_correct
                  func_tag default_tag default_itag tgm cmap cenv Σ
                  dcon_to_tag_inj box_dc box_tag cenv_case_consistent
                  Hcmap_eval_coherent Hglob_term Hglob_fuel_zero Hglob_wf val_rel_exists
                  vs e (fuel_sem.Val v) f t Heval)
      as Hcorr.
    unfold anf_cvt_correct_exp in Hcorr.
    specialize (Hcorr rho vnames C x S S' i
                      Hwf Hwfe Hcons Hcmap Hdis Hdis_cmap Henv Hglob Hrel
                      e_k Hdis_ek).
    eapply Hcorr; eauto.
  Qed.

  (* Wrapping a source value prefix around a target OOT continuation contributes
     exactly the source prefix fuel to the lower bound on the target witness. *)
  Lemma anf_cvt_correct_val_cont_oot
        vs e v f t rho vnames C x S S' i e_k v' c_oot :
    to_nat c_oot <= i ->
    well_formed_env Σ vs ->
    wellformed Σ (List.length vnames) e = true ->
    env_consistent vnames vs ->
    cmap_consistent' vnames vs ->
    Disjoint _ (FromList vnames) S ->
    Disjoint _ (cmap_vars cmap) S ->
    anf_env_rel' vnames vs rho ->
    global_env_rel' (kn_deps e) rho ->
    anf_cvt_rel' S e vnames S' C x ->
    Disjoint _ (occurs_free e_k) ((S \\ S') \\ [set x]) ->
    src_eval vs e (fuel_sem.Val v) f t ->
    anf_val_rel' v v' ->
    bstep_fuel cenv (M.set x v' rho) e_k c_oot eval.OOT tt ->
    exists c,
      (c_oot + f <= c)%nat /\
      bstep_fuel cenv rho (C |[ e_k ]|) c eval.OOT tt.
  Proof.
    intros Hle_i Hwf Hwfe Hcons Hcmap Hdis Hdis_cmap Henv Hglob Hrel
           Hdis_ek Heval Hvrel Hoot.
    pose proof (anf_cvt_correct_val_cont
                  vs e v f t rho vnames C x S S' i e_k v'
                  Hwf Hwfe Hcons Hcmap Hdis Hdis_cmap Henv Hglob Hrel
                  Hdis_ek Heval Hvrel)
      as Hval.
    destruct (Hval eval.OOT c_oot tt Hle_i Hoot)
      as [vres [c [cout [Hbstep [Hpost Hres]]]]].
    destruct vres.
    - destruct cout.
      exists c. split; [| exact Hbstep].
      unfold anf_bound in Hpost. simpl in Hpost. lia.
    - simpl in Hres. exfalso. exact Hres.
  Qed.

  Lemma anf_cvt_correct_val_halt_run
        vs e v f t rho vnames C x S S' i v' :
    1 <= i ->
    well_formed_env Σ vs ->
    wellformed Σ (List.length vnames) e = true ->
    env_consistent vnames vs ->
    cmap_consistent' vnames vs ->
    Disjoint _ (FromList vnames) S ->
    Disjoint _ (cmap_vars cmap) S ->
    anf_env_rel' vnames vs rho ->
    global_env_rel' (kn_deps e) rho ->
    anf_cvt_rel' S e vnames S' C x ->
    src_eval vs e (fuel_sem.Val v) f t ->
    anf_val_rel' v v' ->
    exists v_tgt c cout,
      bstep_fuel cenv rho (C |[ Ehalt x ]|) c (eval.Res v_tgt) cout /\
      (f + 1 <= c)%nat.
  Proof.
    intros Hi Hwf Hwfe Hcons Hcmap Hdis Hdis_cmap Henv Hglob Hrel Heval Hvrel.
    assert (Hdis_ehalt : Disjoint var (occurs_free (Ehalt x))
                             ((S \\ S') \\ [set x])).
    { constructor. intros z Hc. inversion Hc; subst; clear Hc.
      apply occurs_free_Ehalt_inv in H. subst z.
      destruct H0 as [_ Habs]. apply Habs. constructor. }
    pose proof (anf_cvt_correct_val_cont
                  vs e v f t rho vnames C x S S' i (Ehalt x) v'
                  Hwf Hwfe Hcons Hcmap Hdis Hdis_cmap Henv Hglob Hrel
                  Hdis_ehalt Heval Hvrel)
      as Hval.
    assert (Hehalt : bstep_fuel cenv (M.set x v' rho) (Ehalt x)
                    (<0> <+> <1> (Ehalt x))
                    (eval.Res v')
                    (<0> <+> <1> (Ehalt x))).
    { apply BStepf_run. apply BStept_halt. rewrite M.gss. reflexivity. }
    assert (H1_le_i : to_nat (<0> <+> <1> (Ehalt x)) <= i).
    { rewrite plus_zero. unfold one. rewrite to_nat_one. lia. }
    destruct (Hval (eval.Res v') _ _ H1_le_i Hehalt)
      as [vres [c [cout [Hbstep [Hpost Hres]]]]].
    destruct vres as [| v_tgt].
    { simpl in Hres. destruct Hres. }
    exists v_tgt, c, cout. split; [exact Hbstep |].
    unfold anf_bound in Hpost. simpl in Hpost. lia.
  Qed.

  (* This is the value branch of the separate lower-bound OOT proof: if the
     source also returns a value at a larger fuel, the target must OOT at the
     smaller source OOT fuel. *)
  Lemma anf_cvt_correct_val_implies_target_oot
        vs e v f_val t_val f_oot rho vnames C x S S' i v' :
    1 <= i ->
    f_oot < f_val ->
    well_formed_env Σ vs ->
    wellformed Σ (List.length vnames) e = true ->
    env_consistent vnames vs ->
    cmap_consistent' vnames vs ->
    Disjoint _ (FromList vnames) S ->
    Disjoint _ (cmap_vars cmap) S ->
    anf_env_rel' vnames vs rho ->
    global_env_rel' (kn_deps e) rho ->
    anf_cvt_rel' S e vnames S' C x ->
    src_eval vs e (fuel_sem.Val v) f_val t_val ->
    anf_val_rel' v v' ->
    exists cout,
      bstep_fuel cenv rho (C |[ Ehalt x ]|) f_oot eval.OOT cout.
  Proof.
    intros Hi Hlt Hwf Hwfe Hcons Hcmap Hdis Hdis_cmap Henv Hglob Hrel Heval Hvrel.
    destruct (anf_cvt_correct_val_halt_run
                vs e v f_val t_val rho vnames C x S S' i v'
                Hi Hwf Hwfe Hcons Hcmap Hdis Hdis_cmap Henv Hglob Hrel Heval Hvrel)
      as [v_tgt [c [cout_res [Hres Hlb]]]].
    assert (Hlt_c : f_oot < c) by lia.
    edestruct bstep_fuel_lt_OOT as [cout_oot [c_gap [Hoot _]]].
    { exact Hres. }
    { exact Hlt_c. }
    exists cout_oot. exact Hoot.
  Qed.

  Lemma anf_cvt_correct_oot_from_source_value
        vs e v f_oot t_oot f_val t_val rho vnames C x S S' :
    well_formed_env Σ vs ->
    wellformed Σ (List.length vnames) e = true ->
    env_consistent vnames vs ->
    cmap_consistent' vnames vs ->
    Disjoint _ (FromList vnames) S ->
    Disjoint _ (cmap_vars cmap) S ->
    anf_env_rel' vnames vs rho ->
    global_env_rel' (kn_deps e) rho ->
    anf_cvt_rel' S e vnames S' C x ->
    src_eval vs e fuel_sem.OOT f_oot t_oot ->
    src_eval vs e (fuel_sem.Val v) f_val t_val ->
    exists cout,
      bstep_fuel cenv rho (C |[ Ehalt x ]|) f_oot eval.OOT cout.
  Proof.
    intros Hwf Hwfe Hcons Hcmap Hdis Hdis_cmap Henv Hglob Hrel Hoot_src Hval_src.
    assert (Hlen_env : List.length vs = List.length vnames).
    { exact (@anf_env_rel_length func_tag default_tag tgm cmap Σ box_dc box_tag
                                 _ _ _ Henv). }
    assert (Hlt : f_oot < f_val).
    { eapply src_eval_val_gt_oot; eauto. }
    assert (Hwf_v : well_formed_val Σ v).
    { eapply eval_preserves_wf.
      - exact Hglob_wf.
      - exact Hwf.
      - rewrite Hlen_env. exact Hwfe.
      - exact Hval_src. }
    destruct (val_rel_exists v Hwf_v) as [v' Hvrel].
    eapply anf_cvt_correct_val_implies_target_oot with (v := v) (f_val := f_val)
                                                     (t_val := t_val) (i := 1) (v' := v');
      eauto; lia.
  Qed.

  Lemma anf_cvt_correct_oot_lower_bound_goal_if_value
        vs e f_oot t_oot :
    src_eval vs e fuel_sem.OOT f_oot t_oot ->
    (exists v f_val t_val, src_eval vs e (fuel_sem.Val v) f_val t_val) ->
    anf_cvt_correct_oot_lower_bound_goal vs e f_oot.
  Proof.
    intros Hoot_src [v [f_val [t_val Hval_src]]].
    intros rho vnames C x S S'
           Hwf Hwfe Hcons Hcmap Hdis Hdis_cmap Henv Hglob Hrel
           e_k Hdis_ek _.
    assert (Hlen_env : List.length vs = List.length vnames).
    { exact (@anf_env_rel_length func_tag default_tag tgm cmap Σ box_dc box_tag
                                 _ _ _ Henv). }
    assert (Hlt : f_oot < f_val).
    { eapply src_eval_val_gt_oot; eauto. }
    assert (Hwf_v : well_formed_val Σ v).
    { eapply eval_preserves_wf.
      - exact Hglob_wf.
      - exact Hwf.
      - rewrite Hlen_env. exact Hwfe.
      - exact Hval_src. }
    destruct (val_rel_exists v Hwf_v) as [v' Hvrel].
    destruct (anf_cvt_correct_val_cont_oot
                vs e v f_val t_val rho vnames C x S S' 0 e_k v' 0
                (le_n _)
                Hwf Hwfe Hcons Hcmap Hdis Hdis_cmap Henv Hglob Hrel
                Hdis_ek Hval_src Hvrel
                (bstep_fuel_zero_OOT cenv (M.set x v' rho) e_k))
      as [c [Hlb Hoot]].
    exists c. split; [lia | exact Hoot].
  Qed.


  Lemma anf_cvt_correct_oot_lower_bound_goal_eval_OOT
        vs e f :
    (f < src_one e)%nat ->
    anf_cvt_correct_oot_lower_bound_goal vs e f.
  Proof.
    intros Hfuel_lt.
    intros rho vnames C x S S'
           Hwf Hwfe Hcons Hcmap Hdis Hdis_cmap Henv Hglob Hrel
           e_k Hdis_ek _.
    assert (Hf0 : f = 0).
    { destruct e; vm_compute in Hfuel_lt; lia. }
    subst f.
    exists 0. split; [lia | exact (bstep_fuel_zero_OOT cenv rho (C |[ e_k ]|))].
  Qed.

  Definition div_measure (p : nat * EAst.term) : { n : nat & nat } :=
    existT _ (fst p) (EInduction.size (snd p)).

  Definition div_lt (p1 p2 : nat * EAst.term) : Prop :=
    @Relation_Operators.lexprod nat (fun _ => nat) lt (fun _ => lt)
                                 (div_measure p1) (div_measure p2).

  Lemma div_lt_wf : well_founded div_lt.
  Proof.
    unfold div_lt, div_measure.
    eapply (@wf_inverse_image
              (nat * EAst.term)
              { n : nat & nat }
              (@Relation_Operators.lexprod nat (fun _ => nat) lt (fun _ => lt))
              (fun p => existT (fun _ => nat) (fst p) (EInduction.size (snd p)))).
    eapply wf_lexprod.
    - apply Wf_nat.lt_wf.
    - intro x. apply Wf_nat.lt_wf.
  Qed.

  Lemma anf_cvt_correct_oot_lower_bound
        vs e f t :
    src_eval vs e fuel_sem.OOT f t ->
    anf_cvt_correct_oot_lower_bound_goal vs e f.
  Proof.
    intros Hoot_init.
    set (P := fun p : nat * EAst.term =>
      forall vs0 t0,
        src_eval vs0 (snd p) fuel_sem.OOT (fst p) t0 ->
        anf_cvt_correct_oot_lower_bound_goal vs0 (snd p) (fst p)).
    assert (Hmain : forall p : nat * EAst.term, P p).
    { refine (well_founded_induction_type div_lt_wf P _).
      intros [f0 e0] IH vs0 t0 Hoot.
      unfold P, anf_cvt_correct_oot_lower_bound_goal.
      intros rho vnames C x S S'
             Hwf Hwfe Hcons Hcmap Hdis Hdis_cmap Henv Hglob Hrel
             e_k Hdis_ek Hns.
      unfold src_not_stuck, fuel_sem.not_stuck in Hns.
      destruct Hns as [Hval | Hdiv].
      { exact (anf_cvt_correct_oot_lower_bound_goal_if_value
                 vs0 e0 f0 t0 Hoot Hval
                 rho vnames C x S S'
                 Hwf Hwfe Hcons Hcmap Hdis Hdis_cmap Henv Hglob Hrel
                 e_k Hdis_ek (or_introl Hval)). }
      inversion Hoot; subst.
      - eapply anf_cvt_correct_oot_lower_bound_goal_eval_OOT; eauto.
        right. exact Hdiv.
      - remember (snd (f0, e0)) as e_cur in H.
        remember fuel_sem.OOT as r_cur in H.
        destruct H; try discriminate.
        + (* eval_App_step *)
          rewrite <- Heqe_cur in Hrel, Hwfe, Hglob, Hdiv |- *.
          match goal with
          | [ Heqf : _ = fst (f0, e0) |- _ ] => rename Heqf into Hfuel_app
          end.
          subst r.
          rename rho' into rho_clos.
          rename na into na_clos.
          rename body into body_clos.
          rename v2 into varg.
          rename H into Heval1.
          rename H0 into Heval2.
          rename H1 into Hoot_body.
          rename f1 into f1_app.
          rename t1 into t1_app.
          rename f2 into f2_app.
          rename t2 into t2_app.
          rename f3 into f3_body.
          rename t3 into t3_body.
          inv Hrel.
          match goal with
          | [ He1 : anf_cvt_rel _ _ _ _ S e1 vnames ?S2 ?C1 ?x1,
              He2 : anf_cvt_rel _ _ _ _ ?S2 e2 vnames ?S3 ?C2 ?x2,
              Hr : x \in ?S3 |- _ ] =>
              rename He1 into Hcvt_e1;
              rename He2 into Hcvt_e2;
              rename Hr into Hx_in_S3
          end.
          rewrite <- !app_ctx_f_fuse.
          assert (Hwfe1 : wellformed Σ (Datatypes.length vnames) e1 = true).
          { eapply proj1. eapply wellformed_tApp. exact Hwfe. }
          assert (Hwfe2 : wellformed Σ (Datatypes.length vnames) e2 = true).
          { eapply proj2. eapply wellformed_tApp. exact Hwfe. }
          assert (Hwf_clos : well_formed_val Σ (fuel_sem.Clos_v rho_clos na_clos body_clos)).
          { eapply eval_preserves_wf; [exact Hglob_wf | exact Hwf | | exact Heval1].
            pose proof Henv as Henv_len.
            unfold anf_env_rel' in Henv_len.
            apply Forall2_length in Henv_len.
            rewrite Henv_len.
            exact Hwfe1. }
          assert (Hwf_v2 : well_formed_val Σ varg).
          { eapply eval_preserves_wf; [exact Hglob_wf | exact Hwf | | exact Heval2].
            pose proof Henv as Henv_len.
            unfold anf_env_rel' in Henv_len.
            apply Forall2_length in Henv_len.
            rewrite Henv_len.
            exact Hwfe2. }
          destruct (val_rel_exists (fuel_sem.Clos_v rho_clos na_clos body_clos) Hwf_clos)
            as [v1' Hrel_clos].
          destruct (val_rel_exists varg Hwf_v2) as [v2' Hrel_v2].
          assert (Hglob_e1 : global_env_rel' (kn_deps e1) rho).
          { eapply global_env_rel_mono; [exact Hglob |].
            intros k Hk.
            unfold kn_deps. simpl.
            apply KernameSet.union_spec. left. exact Hk. }
          assert (Hdis_ek1 :
                    Disjoint _
                             (occurs_free
                                (C2 |[ Eletapp x x1 func_tag [x2] e_k ]|))
                             ((S \\ S2) \\ [set x1])).
          { eapply anf_cvt_disjoint_occurs_free_ctx_app; eauto. }
          assert (Hdis_eletapp :
            Disjoint _ (occurs_free (Eletapp x x1 func_tag [x2] e_k))
                       ((S2 \\ S3) \\ [set x2])).
          { assert (HS2_S : S2 \subset S).
            { eapply anf_cvt_exp_subset. exact Hcvt_e1. }
            assert (HS3_S2 : S3 \subset S2).
            { eapply anf_cvt_exp_subset. exact Hcvt_e2. }
            pose proof (anf_cvt_result_not_in_output _ _ _ _ _ _ _ _ _ _
                         Hcvt_e1 Hdis Hdis_cmap) as Hx1_not_S2.
            constructor. intros z Hz.
            assert (Hz_of : occurs_free (Eletapp x x1 func_tag [x2] e_k) z)
              by (inversion Hz; assumption).
            assert (Hz_sm : ((S2 \\ S3) \\ [set x2]) z)
              by (inversion Hz; assumption).
            clear Hz.
            destruct Hz_sm as [[Hz_S2 Hz_not_S3] Hz_not_x2].
            assert (Hz_cases :
              z = x1 \/ z = x2 \/ (occurs_free e_k z /\ z <> x)).
            { apply (proj1 (occurs_free_Eletapp _ _ _ _ _)) in Hz_of.
              inversion Hz_of as [z' Hz_head | z' Hz_tail]; subst.
              - inversion Hz_head as [z'' Hz_x1 | z'' Hz_x2]; subst.
                + inversion Hz_x1; subst. left. reflexivity.
                + unfold FromList, Ensembles.In in Hz_x2. simpl in Hz_x2.
                  destruct Hz_x2 as [-> | []]. right. left. reflexivity.
              - destruct Hz_tail as [Hz_ek Hz_not_x].
                right. right. split; [exact Hz_ek |].
                intros Hz_x. subst. exact (Hz_not_x (In_singleton _ _)). }
            destruct Hz_cases as [-> | [-> | [Hz_ek Hz_not_x]]].
            - exact (Hx1_not_S2 Hz_S2).
            - exact (Hz_not_x2 (In_singleton _ _)).
            - eapply Hdis_ek. constructor.
              + exact Hz_ek.
              + constructor.
                * constructor.
                  -- eapply HS2_S. exact Hz_S2.
                  -- intros [Hz_S3 _]. exact (Hz_not_S3 Hz_S3).
                * intros Hz_x. apply Hz_not_x. inv Hz_x. reflexivity. }
          assert (Henv_e2 : anf_env_rel' vnames rho0 (M.set x1 v1' rho)).
          { eapply anf_env_rel_set; [exact Henv |].
            intros k Hk.
            assert (Hek : nth_error rho0 k = Some (fuel_sem.Clos_v rho_clos na_clos body_clos)).
            { change positive with var in Hk.
              eapply anf_cvt_rel_var_lookup;
                [exact Heval1 | exact Hcvt_e1
                | exact Hdis | exact Hdis_cmap | exact Hcons | exact Hcmap | exact Hk]. }
            exists (fuel_sem.Clos_v rho_clos na_clos body_clos). split; [exact Hek | exact Hrel_clos]. }
          assert (Hglob_e2_base : global_env_rel' (kn_deps e2) rho).
          { eapply global_env_rel_mono; [exact Hglob |].
            intros k Hk.
            unfold kn_deps. simpl.
            apply KernameSet.union_spec. right. exact Hk. }
          assert (Hglob_e2 : global_env_rel' (kn_deps e2) (M.set x1 v1' rho)).
          { eapply global_env_rel_set; [exact Hglob_e2_base |].
            intros k_g Hdep_g Hlk_g decl_g body_g Hdecl_g Hbody_g
                   src_vg f_g t_g Heval_g.
            destruct (anf_cvt_cmap_eval rho0 e1 (fuel_sem.Clos_v rho_clos na_clos body_clos)
                        f1_app t1_app Heval1
                        _ _ _ _ _ k_g decl_g body_g
                        Hcvt_e1 Hdis Hdis_cmap Hcons Hcmap Hlk_g Hdecl_g Hbody_g)
              as [f1' [t1' Heval_body_clos]].
            pose proof (eval_val_exact_det _ _ _ _ _ _ _ _ Heval_body_clos Heval_g)
              as [Heq_src _].
            subst src_vg. exact Hrel_clos. }
          assert (Hdis_vn_S2 : Disjoint _ (FromList vnames) S2).
          { eapply Disjoint_Included_r;
              [eapply anf_cvt_exp_subset; eassumption | exact Hdis]. }
          assert (Hdis_cmap_S2 : Disjoint _ (cmap_vars cmap) S2).
          { eapply Disjoint_Included_r;
              [eapply anf_cvt_exp_subset; eassumption | exact Hdis_cmap]. }
          pose proof Hrel_clos as Hrel_clos_saved.
          inv Hrel_clos.
          rename H2 into Henv_clos.
          rename H3 into Hcons_clos.
          rename H4 into Hcmap_clos.
          rename H5 into Hdis_clos.
          rename H6 into Hdis_cmap_clos.
          rename H7 into Hx0_not_cmap.
          rename H8 into Hf0_not_cmap.
          rename H9 into Hx0_not_names.
          rename H10 into Hf0_not_names.
          rename H12 into Hcvt_body.
          rename H13 into Hglob_body0.
          set (defs_cc := Fcons f1 func_tag [x0] (C0 |[ Ehalt r1 ]|) Fnil).
          set (rho_bc := M.set x0 v2' (def_funs defs_cc defs_cc rho1 rho1)).
          assert (Hwf_body : wellformed Σ (Datatypes.S (Datatypes.length names)) body_clos = true).
          { inversion Hwf_clos; subst.
            rewrite <- (@anf_env_rel_length func_tag default_tag tgm cmap Σ box_dc box_tag
                                         _ _ _ Henv_clos).
            exact H3. }
          assert (Hcons_body : env_consistent (x0 :: names) (varg :: rho_clos)).
          { apply env_consistent_extend_fresh.
            - exact Hcons_clos.
            - intro Hc. apply Hx0_not_names. right. exact Hc. }
          assert (Hcmap_body : cmap_consistent' (x0 :: names) (varg :: rho_clos)).
          { apply cmap_consistent_extend.
            - exact Hcmap_clos.
            - intros k_c decl_c body_c Hlk_c Hdecl_c Hbody_c. exfalso.
              apply Hx0_not_cmap. exists k_c. exact Hlk_c. }
          assert (Hdis_names_S1 : Disjoint _ (FromList (x0 :: names)) S1).
          { rewrite FromList_cons. eapply Union_Disjoint_l.
            - eapply Disjoint_Singleton_l.
              intro Hin.
              destruct Hdis_clos as [Hd].
              apply (Hd x0). constructor; [left; constructor | exact Hin].
            - eapply Disjoint_Included_l.
              + intros z Hz. apply Union_intror. apply Union_intror. exact Hz.
              + exact Hdis_clos. }
          assert (Henv_body : anf_env_rel' (x0 :: names) (varg :: rho_clos) rho_bc).
          { unfold rho_bc, defs_cc. simpl.
            constructor.
            - exists v2'. split; [rewrite M.gss; reflexivity | exact Hrel_v2].
            - eapply anf_env_rel_weaken;
                [| intro Hc; apply Hx0_not_names; right; exact Hc].
              eapply anf_env_rel_weaken; [exact Henv_clos |].
              exact Hf0_not_names. }
          assert (Hglob_body : global_env_rel' (kn_deps body_clos) rho_bc).
          { unfold rho_bc, defs_cc. simpl.
            eapply global_env_rel_set_fresh; [| exact Hx0_not_cmap].
            eapply global_env_rel_set_fresh; [| exact Hf0_not_cmap].
            exact Hglob_body0. }
          assert (Hdis_ehalt :
            Disjoint _ (occurs_free (Ehalt r1)) ((S1 \\ S0) \\ [set r1])).
          { constructor. intros z Hz. inv Hz.
            inv H. destruct H0 as [_ Hnot]. apply Hnot. constructor. }
          assert (Hns_body : src_not_stuck (varg :: rho_clos) body_clos).
          { eapply src_not_stuck_app_body
                      with (rho := rho0) (e1 := e1) (e2 := e2)
                           (rho' := rho_clos) (na := na_clos)
                           (body := body_clos) (v2 := varg)
                           (f1 := f1_app) (t1 := t1_app)
                           (f2 := f2_app) (t2 := t2_app);
              [exact Heval1 | exact Heval2 |].
            right. exact Hdiv. }
          assert (Hlt_body : div_lt (f3_body, body_clos) (f0, e0)).
          { unfold div_lt, div_measure.
            apply Relation_Operators.left_lex.
            assert (Hlt_f : f3_body < f0).
            { rewrite <- Heqe_cur in Hfuel_app.
              cbv [one_i fuel_resource_LambdaBox fuel_exp] in Hfuel_app.
              simpl in Hfuel_app. lia. }
            exact Hlt_f. }
          pose proof (IH (f3_body, body_clos) Hlt_body (varg :: rho_clos) t3_body Hoot_body)
            as IHbody.
          unfold anf_cvt_correct_oot_lower_bound_goal in IHbody.
          assert (Hwf_body_env : well_formed_env Σ (varg :: rho_clos)).
          { constructor; [exact Hwf_v2 |].
            inversion Hwf_clos; subst. exact H1. }
          destruct (IHbody rho_bc (x0 :: names) C0 r1 S1 S0
                           Hwf_body_env
                           Hwf_body
                           Hcons_body
                           Hcmap_body
                           Hdis_names_S1
                           Hdis_cmap_clos
                           Henv_body
                           Hglob_body
                           Hcvt_body
                           (Ehalt r1)
                           Hdis_ehalt
                           Hns_body)
            as [c3 [Hlb3 Hoot3]].
          set (rho_app := M.set x2 v2' (M.set x1 (Vfun rho1 defs_cc f1) rho)).
          destruct (Pos.eq_dec x1 x2) as [Heq_x1x2 | Hneq_x1x2].
          * subst x2.
            assert (Hrel_rho_ex : exists v_rho,
              M.get x1 rho = Some v_rho /\
              anf_val_rel' (Clos_v rho_clos na_clos body_clos) v_rho /\
              anf_val_rel' varg v_rho /\
              Clos_v rho_clos na_clos body_clos = varg).
            { destruct (In_dec Pos.eq_dec x1 vnames) as [Hin_vn | Hni_vn].
              - apply In_nth_error in Hin_vn. destruct Hin_vn as [k0 Hk0].
                assert (Heval1_k : nth_error rho0 k0 = Some (Clos_v rho_clos na_clos body_clos)).
                { eapply anf_cvt_rel_var_lookup;
                    [exact Heval1 | exact Hcvt_e1 | exact Hdis | exact Hdis_cmap
                    | exact Hcons | exact Hcmap | exact Hk0]. }
                assert (Heval2_k : nth_error rho0 k0 = Some varg).
                { eapply anf_cvt_rel_var_lookup;
                    [exact Heval2 | exact Hcvt_e2
                    | eapply Disjoint_Included_r;
                        [eapply anf_cvt_exp_subset; exact Hcvt_e1 | exact Hdis]
                    | eapply Disjoint_Included_r;
                        [eapply anf_cvt_exp_subset; exact Hcvt_e1 | exact Hdis_cmap]
                    | exact Hcons | exact Hcmap | exact Hk0]. }
                destruct (Forall2_nth_error_r _ _ _ _ _ Henv Hk0)
                  as [v_src [Hsrc [v_rho [Hget Hrel]]]].
                assert (v_src = Clos_v rho_clos na_clos body_clos) by congruence.
                subst v_src.
                assert (Heq_varg : Clos_v rho_clos na_clos body_clos = varg) by congruence.
                exists v_rho. split; [exact Hget |]. split; [exact Hrel |].
                split; [subst varg; exact Hrel | exact Heq_varg].
              - destruct (@anf_cvt_result_in_consumed
                            func_tag default_tag tgm cmap
                            S e1 vnames S2 C1 x1 Hcvt_e1)
                  as [Hin1 | [Hin1 | Hin1]].
                + contradiction.
                + exfalso.
                  destruct (@anf_cvt_result_in_consumed
                              func_tag default_tag tgm cmap
                              S2 e2 vnames S3 C2 x1 Hcvt_e2)
                    as [Hin2 | [Hin2 | Hin2]].
                  * contradiction.
                  * eapply anf_cvt_result_not_in_output;
                      [exact Hcvt_e1 | exact Hdis | exact Hdis_cmap | exact Hin2].
                  * destruct Hdis_cmap as [Hdc]. apply (Hdc x1).
                    constructor; [exact Hin2 | exact Hin1].
                + destruct (@anf_cvt_cmap_result_in_deps
                              func_tag default_tag tgm cmap
                              S e1 vnames S2 C1 x1 Hcvt_e1 Hin1
                              Hdis Hdis_cmap Hni_vn)
                    as [k_c1 [Hlk1 Hdep1]].
                  assert (Hkc_deps : kn_deps (EAst.tApp e1 e2) k_c1).
                  { unfold kn_deps. simpl. apply KernameSet.union_spec. left. exact Hdep1. }
                  destruct (Hglob k_c1 x1 Hkc_deps Hlk1)
                    as (decl_g & body_g & v_rho & Hdecl_g & Hbody_g & Hget_g & Hrel_g).
                  exists v_rho. split; [exact Hget_g |].
                  assert (Heval1_cmap : exists f_c t_c,
                    src_eval [] body_g (fuel_sem.Val (Clos_v rho_clos na_clos body_clos)) f_c t_c).
                  { eapply anf_cvt_cmap_eval;
                      [exact Heval1 | exact Hcvt_e1 | exact Hdis | exact Hdis_cmap
                      | exact Hcons | exact Hcmap | exact Hlk1 | exact Hdecl_g | exact Hbody_g]. }
                  destruct Heval1_cmap as [f_c1 [t_c1 Hev1]].
                  assert (Heval2_cmap : exists f_c t_c,
                    src_eval [] body_g (fuel_sem.Val varg) f_c t_c).
                  { eapply anf_cvt_cmap_eval;
                      [exact Heval2 | exact Hcvt_e2
                      | eapply Disjoint_Included_r;
                          [eapply anf_cvt_exp_subset; exact Hcvt_e1 | exact Hdis]
                      | eapply Disjoint_Included_r;
                          [eapply anf_cvt_exp_subset; exact Hcvt_e1 | exact Hdis_cmap]
                      | exact Hcons | exact Hcmap | exact Hlk1 | exact Hdecl_g | exact Hbody_g]. }
                  destruct Heval2_cmap as [f_c2 [t_c2 Hev2]].
                  split; [exact (Hrel_g _ _ _ Hev1) |].
                  split; [exact (Hrel_g _ _ _ Hev2) |].
                  pose proof (eval_val_exact_det _ _ _ _ _ _ _ _ Hev1 Hev2) as [Heq_src _].
                  exact Heq_src. }
            destruct Hrel_rho_ex as [v_rho [Hget_rho [Hrel_rho [Hrel_rho_v2 Heq_varg]]]].
            assert (Hpv_cv : forall j, preord_val cenv eq_fuel j
                      (Vfun rho1 defs_cc f1) v2').
            { intro j.
              eapply preord_val_trans; [tci | exact eq_fuel_idemp | | ].
              - eapply (@anf_cvt_val_alpha_equiv
                  _ _ _ _ eq_fuel eq_fuel tgm cmap cenv
                  eq_fuel_compat' (fun _ _ H0 => H0)
                  nat src_fuel_res src_trace_res
                  Σ box_dc Hglob_term func_tag default_tag).
                exact Hrel_clos_saved.
                exact Hrel_rho.
              - intros m0.
                eapply (@anf_cvt_val_alpha_equiv
                  _ _ _ _ eq_fuel eq_fuel tgm cmap cenv
                  eq_fuel_compat' (fun _ _ H0 => H0)
                  nat src_fuel_res src_trace_res
                  Σ box_dc Hglob_term func_tag default_tag).
                rewrite Heq_varg in Hrel_rho. exact Hrel_rho.
                exact Hrel_v2. }
            assert (Hpv_inst := Hpv_cv (c3 + 1)%nat).
            rewrite preord_val_eq in Hpv_inst.
            destruct v2' as [ | rho2_fc B2 f2_v | | ];
              try (simpl in Hpv_inst; contradiction).
            assert (Hfind_cc : find_def f1 defs_cc =
              Some (func_tag, [x0], C0 |[ Ehalt r1 ]|)).
            { unfold defs_cc. simpl.
              destruct (M.elt_eq f1 f1); [reflexivity | congruence]. }
            assert (Hset_cc : Some rho_bc =
              set_lists [x0] [Vfun rho2_fc B2 f2_v] (def_funs defs_cc defs_cc rho1 rho1)).
            { unfold rho_bc. reflexivity. }
            edestruct Hpv_inst as (xs2_pc & e2_body & rho2_body &
              Hfind_v2 & Hset_v2 & Hbody_preord).
            { reflexivity. }
            { exact Hfind_cc. }
            { exact Hset_cc. }
            assert (Hbody_pe : preord_exp' cenv (preord_val cenv) eq_fuel eq_fuel
                      c3 (C0 |[ Ehalt r1 ]|, rho_bc) (e2_body, rho2_body)).
            { apply Hbody_preord. lia.
              constructor; [| constructor ].
              eapply preord_val_refl. tci. }
            destruct (Hbody_pe eval.OOT c3 tt (le_n _) Hoot3) as
              [v2_body_res [cin2_bc [cout2_bc [Hbstep2_bc [Hpost2_bc Hres2_bc]]]]].
            destruct cout2_bc.
            destruct v2_body_res as [|v2_body_val];
              [unfold eq_fuel in Hpost2_bc; simpl in Hpost2_bc; subst cin2_bc
              | simpl in Hres2_bc; contradiction].
            assert (Hoot_letapp :
              bstep_fuel cenv rho_app
                (Eletapp x x1 func_tag [x1] e_k) (Datatypes.S c3) eval.OOT tt).
            { unfold rho_app.
              assert (Hget_fun :
                M.get x1 (M.set x1 (Vfun rho2_fc B2 f2_v) (M.set x1 (Vfun rho1 defs_cc f1) rho)) =
                Some (Vfun rho2_fc B2 f2_v)).
              { rewrite M.gss. reflexivity. }
              assert (Hget_args :
                get_list [x1] (M.set x1 (Vfun rho2_fc B2 f2_v)
                                  (M.set x1 (Vfun rho1 defs_cc f1) rho)) =
                Some [Vfun rho2_fc B2 f2_v]).
              { simpl. rewrite M.gss. reflexivity. }
              pose proof
                (BStepf_run cenv
                   (M.set x1 (Vfun rho2_fc B2 f2_v) (M.set x1 (Vfun rho1 defs_cc f1) rho))
                   (Eletapp x x1 func_tag [x1] e_k) eval.OOT c3 tt
                   (BStept_letapp_oot cenv rho2_fc B2 f2_v [Vfun rho2_fc B2 f2_v] xs2_pc
                      e2_body e_k rho2_body
                      (M.set x1 (Vfun rho2_fc B2 f2_v) (M.set x1 (Vfun rho1 defs_cc f1) rho))
                      x x1 func_tag [x1]
                      c3 tt Hget_fun Hget_args Hfind_v2 (eq_sym Hset_v2) Hbstep2_bc))
                as Hbsf.
              unfold one, one_i in Hbsf.
              simpl in Hbsf.
              replace (c3 + 1)%nat with (Datatypes.S c3) in Hbsf by lia.
              exact Hbsf. }
            destruct (anf_cvt_correct_val_cont_oot
                        rho0 e2 varg f2_app t2_app
                        (M.set x1 (Vfun rho1 defs_cc f1) rho) vnames C2 x1 S2 S3
                        (Datatypes.S c3)
                        (Eletapp x x1 func_tag [x1] e_k)
                        (Vfun rho2_fc B2 f2_v) (Datatypes.S c3)
                        (le_n _)
                        Hwf
                        Hwfe2
                        Hcons
                        Hcmap
                        Hdis_vn_S2
                        Hdis_cmap_S2
                        Henv_e2
                        Hglob_e2
                        Hcvt_e2
                        Hdis_eletapp
                        Heval2
                        Hrel_v2
                        Hoot_letapp)
              as [c2 [Hlb2 Hoot2]].
            destruct (anf_cvt_correct_val_cont_oot
                        rho0 e1 (fuel_sem.Clos_v rho_clos na_clos body_clos) f1_app t1_app
                        rho vnames C1 x1 S S2 c2
                        (C2 |[ Eletapp x x1 func_tag [x1] e_k ]|)
                        (Vfun rho1 defs_cc f1) c2
                        (le_n _)
                        Hwf
                        Hwfe1
                        Hcons
                        Hcmap
                        Hdis
                        Hdis_cmap
                        Henv
                        Hglob_e1
                        Hcvt_e1
                        Hdis_ek1
                        Heval1
                        Hrel_clos_saved
                        Hoot2)
              as [c [Hlb Hoot_tgt]].
            exists c. split.
            { rewrite <- Heqe_cur in Hfuel_app.
              cbv [one_i fuel_resource_LambdaBox fuel_exp] in Hfuel_app.
              simpl in Hfuel_app, Hlb, Hlb2, Hlb3 |- *.
              lia. }
            exact Hoot_tgt.
          * assert (Hoot_letapp :
                bstep_fuel cenv rho_app
                  (Eletapp x x1 func_tag [x2] e_k) (Datatypes.S c3) eval.OOT tt).
            { unfold rho_app.
              assert (Hget_fun :
                M.get x1 (M.set x2 v2' (M.set x1 (Vfun rho1 defs_cc f1) rho)) =
                Some (Vfun rho1 defs_cc f1)).
              { rewrite M.gso; [rewrite M.gss; reflexivity | exact Hneq_x1x2]. }
              assert (Hget_args :
                get_list [x2] (M.set x2 v2' (M.set x1 (Vfun rho1 defs_cc f1) rho)) =
                Some [v2']).
              { simpl. rewrite M.gss. reflexivity. }
              assert (Hset_lists :
                set_lists [x0] [v2'] (def_funs defs_cc defs_cc rho1 rho1) = Some rho_bc).
              { unfold rho_bc, defs_cc. reflexivity. }
              assert (Hfind_def :
                find_def f1 defs_cc = Some (func_tag, [x0], C0 |[ Ehalt r1 ]|)).
              { unfold defs_cc. simpl.
                destruct (M.elt_eq f1 f1); [reflexivity | congruence]. }
              pose proof
                (BStepf_run cenv
                   (M.set x2 v2' (M.set x1 (Vfun rho1 defs_cc f1) rho))
                   (Eletapp x x1 func_tag [x2] e_k) eval.OOT c3 tt
                   (BStept_letapp_oot cenv rho1 defs_cc f1 [v2'] [x0]
                      (C0 |[ Ehalt r1 ]|) e_k rho_bc
                      (M.set x2 v2' (M.set x1 (Vfun rho1 defs_cc f1) rho))
                      x x1 func_tag [x2]
                      c3 tt Hget_fun Hget_args Hfind_def Hset_lists Hoot3))
                as Hbsf.
              unfold one, one_i in Hbsf.
              simpl in Hbsf.
              replace (c3 + 1)%nat with (Datatypes.S c3) in Hbsf by lia.
              exact Hbsf. }
            destruct (anf_cvt_correct_val_cont_oot
                        rho0 e2 varg f2_app t2_app
                        (M.set x1 (Vfun rho1 defs_cc f1) rho) vnames C2 x2 S2 S3
                        (Datatypes.S c3)
                        (Eletapp x x1 func_tag [x2] e_k) v2' (Datatypes.S c3)
                        (le_n _)
                        Hwf
                        Hwfe2
                        Hcons
                        Hcmap
                        Hdis_vn_S2
                        Hdis_cmap_S2
                        Henv_e2
                        Hglob_e2
                        Hcvt_e2
                        Hdis_eletapp
                        Heval2
                        Hrel_v2
                        Hoot_letapp)
              as [c2 [Hlb2 Hoot2]].
            destruct (anf_cvt_correct_val_cont_oot
                        rho0 e1 (fuel_sem.Clos_v rho_clos na_clos body_clos) f1_app t1_app
                        rho vnames C1 x1 S S2 c2
                        (C2 |[ Eletapp x x1 func_tag [x2] e_k ]|)
                        (Vfun rho1 defs_cc f1) c2
                        (le_n _)
                        Hwf
                        Hwfe1
                        Hcons
                        Hcmap
                        Hdis
                        Hdis_cmap
                        Henv
                        Hglob_e1
                        Hcvt_e1
                        Hdis_ek1
                        Heval1
                        Hrel_clos_saved
                        Hoot2)
              as [c [Hlb Hoot_tgt]].
            exists c. split.
            { cbv [one_i fuel_resource_LambdaBox fuel_exp] in Hfuel_app.
              simpl in Hfuel_app, Hlb, Hlb2, Hlb3 |- *.
              lia. }
            exact Hoot_tgt.
        + (* eval_App_step_OOT1 *)
          rewrite <- Heqe_cur in Hrel, Hwfe, Hglob, Hdiv, H3 |- *.
          inv Hrel.
          match goal with
          | [ He1 : anf_cvt_rel _ _ _ _ S e1 vnames ?S2 ?C1 ?x1,
              He2 : anf_cvt_rel _ _ _ _ ?S2 e2 vnames ?S3 ?C2 ?x2,
              Hr : x \in ?S3 |- _ ] =>
              rename He1 into Hcvt_e1;
              rename He2 into Hcvt_e2;
              rename Hr into Hx_in_S3
          end.
          rewrite <- !app_ctx_f_fuse.
          assert (Hwfe1 : wellformed Σ (Datatypes.length vnames) e1 = true).
          { eapply proj1. eapply wellformed_tApp. exact Hwfe. }
          assert (Hglob_e1 : global_env_rel' (kn_deps e1) rho).
          { eapply global_env_rel_mono; [exact Hglob |].
            intros k Hk.
            unfold kn_deps. simpl.
            apply KernameSet.union_spec. left. exact Hk. }
          assert (Hdis_ek1 :
                    Disjoint _
                             (occurs_free
                                (C2 |[ Eletapp x x1 func_tag [x2] e_k ]|))
                             ((S \\ S2) \\ [set x1])).
          { eapply anf_cvt_disjoint_occurs_free_ctx_app; eauto. }
          assert (Hns_e1 : src_not_stuck rho0 e1).
          { eapply src_not_stuck_app_fun. right. exact Hdiv. }
          assert (Hlt_e1 : div_lt (Datatypes.S f1, e1) (f0, e0)).
          { unfold div_lt, div_measure.
            replace f0 with (Datatypes.S f1).
            - cbn in Heqe_cur. rewrite <- Heqe_cur.
              apply Relation_Operators.right_lex. simpl. lia.
            - cbv [one_i fuel_resource_LambdaBox fuel_exp] in H3.
              simpl in H3. lia. }
          destruct Hns_e1 as [[src_v [fv [tv Hval1]]] | Hdiv_e1].
          * pose proof (src_eval_val_gt_oot rho0 e1 src_v fv tv Hval1 f1 t1 H)
              as Hlt_oot.
            destruct (Nat.eq_dec fv (Datatypes.S f1)) as [Hfv | Hneq_fv].
            -- subst fv.
               assert (Hwf_src_v : well_formed_val Σ src_v).
               { eapply eval_preserves_wf;
                   [exact Hglob_wf | exact Hwf | | exact Hval1].
                 pose proof Henv as Henv_len.
                 unfold anf_env_rel' in Henv_len.
                 apply Forall2_length in Henv_len.
                 rewrite Henv_len.
                 exact Hwfe1. }
               destruct (val_rel_exists src_v Hwf_src_v) as [src_v' Hrel_v].
               destruct (anf_cvt_correct_val_cont_oot
                           rho0 e1 src_v (Datatypes.S f1) tv
                           rho vnames C1 x1 S S2 0
                           (C2 |[ Eletapp x x1 func_tag [x2] e_k ]|)
                           src_v' 0
                           (le_n _)
                           Hwf
                           Hwfe1
                           Hcons
                           Hcmap
                           Hdis
                           Hdis_cmap
                           Henv
                           Hglob_e1
                           Hcvt_e1
                           Hdis_ek1
                           Hval1
                           Hrel_v
                           (bstep_fuel_zero_OOT cenv
                              (M.set x1 src_v' rho)
                              (C2 |[ Eletapp x x1 func_tag [x2] e_k ]|)))
                 as [c [Hlb Hoot_tgt]].
               exists c. split.
               { cbv [one_i fuel_resource_LambdaBox fuel_exp] in H3.
                 cbv [one_i fuel_resource_LambdaBox fuel_exp].
                 simpl in Hlb |- *.
                 lia. }
               exact Hoot_tgt.
            -- assert (Datatypes.S f1 < fv) as Hlt_succ by lia.
               destruct (src_eval_lt_OOT rho0 e1 src_v fv tv (Datatypes.S f1) Hval1 Hlt_succ)
                 as [t1' Hoot1'].
               pose proof (IH (Datatypes.S f1, e1) Hlt_e1 rho0 t1' Hoot1')
                 as IHe1.
               unfold anf_cvt_correct_oot_lower_bound_goal in IHe1.
               destruct (IHe1 rho vnames C1 x1 S S2
                              Hwf
                              Hwfe1
                              Hcons
                              Hcmap
                              Hdis
                              Hdis_cmap
                              Henv
                              Hglob_e1
                              Hcvt_e1
                              (C2 |[ Eletapp x x1 func_tag [x2] e_k ]|)
                              Hdis_ek1
                              (or_introl
                                 (ex_intro _ src_v
                                    (ex_intro _ fv
                                       (ex_intro _ tv Hval1)))))
                 as [c [Hlb Hoot_tgt]].
               exists c. split.
               { cbv [one_i fuel_resource_LambdaBox fuel_exp] in H3.
                 cbv [one_i fuel_resource_LambdaBox fuel_exp].
                 simpl in Hlb |- *.
                 lia. }
               exact Hoot_tgt.
          * destruct (Hdiv_e1 (Datatypes.S f1)) as [t1' Hoot1'].
            pose proof (IH (Datatypes.S f1, e1) Hlt_e1 rho0 t1' Hoot1')
              as IHe1.
            unfold anf_cvt_correct_oot_lower_bound_goal in IHe1.
            assert (Hns_e1' : src_not_stuck rho0 e1).
            { right. exact Hdiv_e1. }
            destruct (IHe1 rho vnames C1 x1 S S2
                           Hwf
                           Hwfe1
                           Hcons
                           Hcmap
                           Hdis
                           Hdis_cmap
                           Henv
                           Hglob_e1
                           Hcvt_e1
                           (C2 |[ Eletapp x x1 func_tag [x2] e_k ]|)
                           Hdis_ek1
                           Hns_e1')
              as [c [Hlb Hoot_tgt]].
            exists c. split.
            { cbv [one_i fuel_resource_LambdaBox fuel_exp] in H3.
              cbv [one_i fuel_resource_LambdaBox fuel_exp].
              simpl in Hlb |- *.
              lia. }
            exact Hoot_tgt.
        + (* eval_App_step_OOT2 *)
          rewrite <- Heqe_cur in Hrel, Hwfe, Hglob, Hdiv, H3 |- *.
          inv Hrel.
          match goal with
          | [ He1 : anf_cvt_rel _ _ _ _ S e1 vnames ?S2 ?C1 ?x1,
              He2 : anf_cvt_rel _ _ _ _ ?S2 e2 vnames ?S3 ?C2 ?x2,
              Hr : x \in ?S3 |- _ ] =>
              rename He1 into Hcvt_e1;
              rename He2 into Hcvt_e2;
              rename Hr into Hx_in_S3
          end.
          rewrite <- !app_ctx_f_fuse.
          rename v into v1.
          assert (Hwfe1 : wellformed Σ (Datatypes.length vnames) e1 = true).
          { eapply proj1. eapply wellformed_tApp. exact Hwfe. }
          assert (Hwfe2 : wellformed Σ (Datatypes.length vnames) e2 = true).
          { eapply proj2. eapply wellformed_tApp. exact Hwfe. }
          assert (Hwf_v1 : well_formed_val Σ v1).
          { eapply eval_preserves_wf; [exact Hglob_wf | exact Hwf | | exact H].
            pose proof Henv as Henv_len.
            unfold anf_env_rel' in Henv_len.
            apply Forall2_length in Henv_len.
            rewrite Henv_len.
            exact Hwfe1. }
          destruct (val_rel_exists v1 Hwf_v1) as [v1' Hrel1].
          assert (Hdis_eletapp :
            Disjoint _ (occurs_free (Eletapp x x1 func_tag [x2] e_k))
                       ((S2 \\ S3) \\ [set x2])).
          { assert (HS2_S : S2 \subset S).
            { eapply anf_cvt_exp_subset. exact Hcvt_e1. }
            assert (HS3_S2 : S3 \subset S2).
            { eapply anf_cvt_exp_subset. exact Hcvt_e2. }
            pose proof (anf_cvt_result_not_in_output _ _ _ _ _ _ _ _ _ _
                         Hcvt_e1 Hdis Hdis_cmap) as Hx1_not_S2.
            constructor. intros z Hz.
            assert (Hz_of : occurs_free (Eletapp x x1 func_tag [x2] e_k) z)
              by (inversion Hz; assumption).
            assert (Hz_sm : ((S2 \\ S3) \\ [set x2]) z)
              by (inversion Hz; assumption).
            clear Hz.
            destruct Hz_sm as [[Hz_S2 Hz_not_S3] Hz_not_x2].
            assert (Hz_cases :
              z = x1 \/ z = x2 \/ (occurs_free e_k z /\ z <> x)).
            { apply (proj1 (occurs_free_Eletapp _ _ _ _ _)) in Hz_of.
              inversion Hz_of as [z' Hz_head | z' Hz_tail]; subst.
              - inversion Hz_head as [z'' Hz_x1 | z'' Hz_x2]; subst.
                + inversion Hz_x1; subst. left. reflexivity.
                + unfold FromList, Ensembles.In in Hz_x2. simpl in Hz_x2.
                  destruct Hz_x2 as [-> | []]. right. left. reflexivity.
              - destruct Hz_tail as [Hz_ek Hz_not_x].
                right. right. split; [exact Hz_ek |].
                intros Hz_x. subst. exact (Hz_not_x (In_singleton _ _)). }
            destruct Hz_cases as [-> | [-> | [Hz_ek Hz_not_x]]].
            - exact (Hx1_not_S2 Hz_S2).
            - exact (Hz_not_x2 (In_singleton _ _)).
            - eapply Hdis_ek. constructor.
              + exact Hz_ek.
              + constructor.
                * constructor.
                  -- eapply HS2_S. exact Hz_S2.
                  -- intros [Hz_S3 _]. exact (Hz_not_S3 Hz_S3).
                * intros Hz_x. apply Hz_not_x. inv Hz_x. reflexivity. }
          assert (Henv_e2 : anf_env_rel' vnames rho0 (M.set x1 v1' rho)).
          { eapply anf_env_rel_set; [exact Henv |].
            intros k Hk.
            assert (Hek : nth_error rho0 k = Some v1).
            { change positive with var in Hk.
              eapply anf_cvt_rel_var_lookup;
                [exact H | exact Hcvt_e1
                | exact Hdis | exact Hdis_cmap | exact Hcons | exact Hcmap | exact Hk]. }
            exists v1. split; [exact Hek | exact Hrel1]. }
          assert (Hglob_e1 : global_env_rel' (kn_deps e1) rho).
          { eapply global_env_rel_mono; [exact Hglob |].
            intros k Hk.
            unfold kn_deps. simpl.
            apply KernameSet.union_spec. left. exact Hk. }
          assert (Hdis_ek1 :
                    Disjoint _
                             (occurs_free
                                (C2 |[ Eletapp x x1 func_tag [x2] e_k ]|))
                             ((S \\ S2) \\ [set x1])).
          { eapply anf_cvt_disjoint_occurs_free_ctx_app; eauto. }
          assert (Hglob_e2_base : global_env_rel' (kn_deps e2) rho).
          { eapply global_env_rel_mono; [exact Hglob |].
            intros k Hk.
            unfold kn_deps. simpl.
            apply KernameSet.union_spec. right. exact Hk. }
          assert (Hglob_e2 : global_env_rel' (kn_deps e2) (M.set x1 v1' rho)).
          { eapply global_env_rel_set; [exact Hglob_e2_base |].
            intros k_g _ Hlk_g decl_g body_g Hdecl_g Hbody_g src_vg f_g t_g Heval_g.
            destruct (anf_cvt_cmap_eval rho0 e1 v1 f1 t1 H
                        _ _ _ _ _ k_g decl_g body_g
                        Hcvt_e1 Hdis Hdis_cmap Hcons Hcmap Hlk_g Hdecl_g Hbody_g)
              as [f1' [t1' Heval_body_v1]].
            pose proof (eval_val_exact_det _ _ _ _ _ _ _ _ Heval_body_v1 Heval_g)
              as [Heq_src _].
            subst src_vg. exact Hrel1. }
          assert (Hdis_vn_S2 : Disjoint _ (FromList vnames) S2).
          { eapply Disjoint_Included_r;
              [eapply anf_cvt_exp_subset; eassumption | exact Hdis]. }
          assert (Hdis_cmap_S2 : Disjoint _ (cmap_vars cmap) S2).
          { eapply Disjoint_Included_r;
              [eapply anf_cvt_exp_subset; eassumption | exact Hdis_cmap]. }
          assert (Hns_e2 : src_not_stuck rho0 e2).
          { eapply src_not_stuck_app_arg; [exact H |].
            right. exact Hdiv. }
          assert (Hlt_e2 : div_lt (Datatypes.S f2, e2) (f0, e0)).
          { unfold div_lt, div_measure.
            destruct f1 as [| f1'].
            - replace f0 with (Datatypes.S f2).
              + cbn in Heqe_cur. rewrite <- Heqe_cur.
                apply Relation_Operators.right_lex. simpl. lia.
              + cbv [one_i fuel_resource_LambdaBox fuel_exp] in H3.
                simpl in H3. lia.
            - apply Relation_Operators.left_lex.
              assert (Hlt_f : Datatypes.S f2 < f0).
              { cbv [one_i fuel_resource_LambdaBox fuel_exp] in H3.
                simpl in H3. lia. }
              exact Hlt_f. }
          destruct Hns_e2 as [[src_v2 [fv [tv Hval2]]] | Hdiv_e2].
          * pose proof (src_eval_val_gt_oot rho0 e2 src_v2 fv tv Hval2 f2 t2 H0)
              as Hlt_oot2.
            destruct (Nat.eq_dec fv (Datatypes.S f2)) as [Hfv | Hneq_fv].
            -- subst fv.
               assert (Hwf_v2 : well_formed_val Σ src_v2).
               { eapply eval_preserves_wf;
                   [exact Hglob_wf | exact Hwf | | exact Hval2].
                 pose proof Henv as Henv_len.
                 unfold anf_env_rel' in Henv_len.
                 apply Forall2_length in Henv_len.
                 rewrite Henv_len.
                 exact Hwfe2. }
               destruct (val_rel_exists src_v2 Hwf_v2) as [v2' Hrel2].
               destruct (anf_cvt_correct_val_cont_oot
                           rho0 e2 src_v2 (Datatypes.S f2) tv
                           (M.set x1 v1' rho) vnames C2 x2 S2 S3 0
                           (Eletapp x x1 func_tag [x2] e_k) v2' 0
                           (le_n _)
                           Hwf
                           Hwfe2
                           Hcons
                           Hcmap
                           Hdis_vn_S2
                           Hdis_cmap_S2
                           Henv_e2
                           Hglob_e2
                           Hcvt_e2
                           Hdis_eletapp
                           Hval2
                           Hrel2
                           (bstep_fuel_zero_OOT cenv
                              (M.set x2 v2' (M.set x1 v1' rho))
                              (Eletapp x x1 func_tag [x2] e_k)))
                 as [c2 [Hlb2 Hoot2]].
               destruct (anf_cvt_correct_val_cont_oot
                           rho0 e1 v1 f1 t1
                           rho vnames C1 x1 S S2 c2
                           (C2 |[ Eletapp x x1 func_tag [x2] e_k ]|) v1' c2
                           (le_n _)
                           Hwf
                           Hwfe1
                           Hcons
                           Hcmap
                           Hdis
                           Hdis_cmap
                           Henv
                           Hglob_e1
                           Hcvt_e1
                           Hdis_ek1
                           H
                           Hrel1
                           Hoot2)
                 as [c [Hlb Hoot_tgt]].
               exists c. split.
               { cbv [one_i fuel_resource_LambdaBox fuel_exp] in H3.
                 simpl in H3, Hlb, Hlb2 |- *.
                 lia. }
               exact Hoot_tgt.
            -- assert (Datatypes.S f2 < fv) as Hlt_succ2 by lia.
               destruct (src_eval_lt_OOT rho0 e2 src_v2 fv tv (Datatypes.S f2) Hval2 Hlt_succ2)
                 as [t2' Hoot2'].
               pose proof (IH (Datatypes.S f2, e2) Hlt_e2 rho0 t2' Hoot2')
                 as IHe2.
               unfold anf_cvt_correct_oot_lower_bound_goal in IHe2.
               destruct (IHe2 (M.set x1 v1' rho) vnames C2 x2 S2 S3
                              Hwf
                              Hwfe2
                              Hcons
                              Hcmap
                              Hdis_vn_S2
                              Hdis_cmap_S2
                              Henv_e2
                              Hglob_e2
                              Hcvt_e2
                              (Eletapp x x1 func_tag [x2] e_k)
                              Hdis_eletapp
                              (or_introl
                                 (ex_intro _ src_v2
                                    (ex_intro _ fv
                                       (ex_intro _ tv Hval2)))))
                 as [c2 [Hlb2 Hoot2]].
               destruct (anf_cvt_correct_val_cont_oot
                           rho0 e1 v1 f1 t1
                           rho vnames C1 x1 S S2 c2
                           (C2 |[ Eletapp x x1 func_tag [x2] e_k ]|) v1' c2
                           (le_n _)
                           Hwf
                           Hwfe1
                           Hcons
                           Hcmap
                           Hdis
                           Hdis_cmap
                           Henv
                           Hglob_e1
                           Hcvt_e1
                           Hdis_ek1
                           H
                           Hrel1
                           Hoot2)
                 as [c [Hlb Hoot_tgt]].
               exists c. split.
               { cbv [one_i fuel_resource_LambdaBox fuel_exp] in H3.
                 simpl in H3, Hlb, Hlb2 |- *.
                 lia. }
               exact Hoot_tgt.
          * destruct (Hdiv_e2 (Datatypes.S f2)) as [t2' Hoot2'].
            pose proof (IH (Datatypes.S f2, e2) Hlt_e2 rho0 t2' Hoot2')
              as IHe2.
            unfold anf_cvt_correct_oot_lower_bound_goal in IHe2.
            assert (Hns_e2' : src_not_stuck rho0 e2).
            { right. exact Hdiv_e2. }
            destruct (IHe2 (M.set x1 v1' rho) vnames C2 x2 S2 S3
                           Hwf
                           Hwfe2
                           Hcons
                           Hcmap
                           Hdis_vn_S2
                           Hdis_cmap_S2
                           Henv_e2
                           Hglob_e2
                           Hcvt_e2
                           (Eletapp x x1 func_tag [x2] e_k)
                           Hdis_eletapp
                           Hns_e2')
              as [c2 [Hlb2 Hoot2]].
            destruct (anf_cvt_correct_val_cont_oot
                        rho0 e1 v1 f1 t1
                        rho vnames C1 x1 S S2 c2
                        (C2 |[ Eletapp x x1 func_tag [x2] e_k ]|) v1' c2
                        (le_n _)
                        Hwf
                        Hwfe1
                        Hcons
                        Hcmap
                        Hdis
                        Hdis_cmap
                        Henv
                        Hglob_e1
                        Hcvt_e1
                        Hdis_ek1
                        H
                        Hrel1
                        Hoot2)
              as [c [Hlb Hoot_tgt]].
            exists c. split.
            { cbv [one_i fuel_resource_LambdaBox fuel_exp] in H3.
              simpl in H3, Hlb, Hlb2 |- *.
              lia. }
            exact Hoot_tgt.
        + (* eval_FixApp_step *)
          subst r. subst rho''.
          rewrite <- Heqe_cur in Hrel, Hwfe, Hglob, Hdiv, H3 |- *.
          inv Hrel.
          match goal with
          | [ He1 : anf_cvt_rel _ _ _ _ _ e1 vnames _ _ _,
              He2 : anf_cvt_rel _ _ _ _ _ e2 vnames _ _ _,
              Hr : x \in _ |- _ ] =>
              rename He1 into Hcvt_e1;
              rename He2 into Hcvt_e2;
              rename Hr into Hx_in_S3
          end.
          rewrite <- !app_ctx_f_fuse.
          assert (Hwfe1 : wellformed Σ (Datatypes.length vnames) e1 = true).
          { eapply proj1. eapply wellformed_tApp. exact Hwfe. }
          assert (Hwfe2 : wellformed Σ (Datatypes.length vnames) e2 = true).
          { eapply proj2. eapply wellformed_tApp. exact Hwfe. }
          assert (Hwf_fix : well_formed_val Σ (fuel_sem.ClosFix_v rho' mfix idx)).
          { eapply eval_preserves_wf; [exact Hglob_wf | exact Hwf | | exact H].
            pose proof Henv as Henv_len.
            unfold anf_env_rel' in Henv_len.
            apply Forall2_length in Henv_len.
            rewrite Henv_len.
            exact Hwfe1. }
          assert (Hwf_v2 : well_formed_val Σ v2).
          { eapply eval_preserves_wf; [exact Hglob_wf | exact Hwf | | exact H2].
            pose proof Henv as Henv_len.
            unfold anf_env_rel' in Henv_len.
            apply Forall2_length in Henv_len.
            rewrite Henv_len.
            exact Hwfe2. }
          destruct (val_rel_exists (fuel_sem.ClosFix_v rho' mfix idx) Hwf_fix)
            as [fix_v' Hrel_fix].
          destruct (val_rel_exists v2 Hwf_v2) as [v2' Hrel_v2].
          pose proof Hrel_fix as Hrel_fix_saved.
          inv Hrel_fix.
          assert (Hdis_eletapp :
            Disjoint _ (occurs_free (Eletapp x x1 func_tag [x2] e_k))
                       ((S2 \\ S3) \\ [set x2])).
          { assert (HS2_S : S2 \subset S).
            { eapply anf_cvt_exp_subset. exact Hcvt_e1. }
            assert (HS3_S2 : S3 \subset S2).
            { eapply anf_cvt_exp_subset. exact Hcvt_e2. }
            pose proof (anf_cvt_result_not_in_output _ _ _ _ _ _ _ _ _ _
                         Hcvt_e1 Hdis Hdis_cmap) as Hx1_not_S2.
            constructor. intros z Hz.
            assert (Hz_of : occurs_free (Eletapp x x1 func_tag [x2] e_k) z)
              by (inversion Hz; assumption).
            assert (Hz_sm : ((S2 \\ S3) \\ [set x2]) z)
              by (inversion Hz; assumption).
            clear Hz.
            destruct Hz_sm as [[Hz_S2 Hz_not_S3] Hz_not_x2].
            assert (Hz_cases :
              z = x1 \/ z = x2 \/ (occurs_free e_k z /\ z <> x)).
            { apply (proj1 (occurs_free_Eletapp _ _ _ _ _)) in Hz_of.
              inversion Hz_of as [z' Hz_head | z' Hz_tail]; subst.
              - inversion Hz_head as [z'' Hz_x1 | z'' Hz_x2]; subst.
                + inversion Hz_x1; subst. left. reflexivity.
                + unfold FromList, Ensembles.In in Hz_x2. simpl in Hz_x2.
                  destruct Hz_x2 as [-> | []]. right. left. reflexivity.
              - destruct Hz_tail as [Hz_ek Hz_not_x].
                right. right. split; [exact Hz_ek |].
                intros Hz_x. subst. exact (Hz_not_x (In_singleton _ _)). }
            destruct Hz_cases as [-> | [-> | [Hz_ek Hz_not_x]]].
            - exact (Hx1_not_S2 Hz_S2).
            - exact (Hz_not_x2 (In_singleton _ _)).
            - eapply Hdis_ek. constructor.
              + exact Hz_ek.
              + constructor.
                * constructor.
                  -- eapply HS2_S. exact Hz_S2.
                  -- intros [Hz_S3 _]. exact (Hz_not_S3 Hz_S3).
                * intros Hz_x. apply Hz_not_x. inv Hz_x. reflexivity. }
          assert (Henv_e2 :
            anf_env_rel' vnames rho0 (M.set x1 (Vfun rho1 Bs f4) rho)).
          { eapply anf_env_rel_set; [exact Henv |].
            intros k Hk.
            assert (Hek : nth_error rho0 k = Some (fuel_sem.ClosFix_v rho' mfix idx)).
            { change positive with var in Hk.
              eapply anf_cvt_rel_var_lookup;
                [exact H | exact Hcvt_e1
                | exact Hdis | exact Hdis_cmap | exact Hcons | exact Hcmap | exact Hk]. }
            exists (fuel_sem.ClosFix_v rho' mfix idx).
            split; [exact Hek | exact Hrel_fix_saved]. }
          assert (Hglob_e1 : global_env_rel' (kn_deps e1) rho).
          { eapply global_env_rel_mono; [exact Hglob |].
            intros k Hk.
            unfold kn_deps. simpl.
            apply KernameSet.union_spec. left. exact Hk. }
          assert (Hdis_ek1 :
            Disjoint _ (occurs_free (C2 |[ Eletapp x x1 func_tag [x2] e_k ]|))
                       ((S \\ S2) \\ [set x1])).
          { eapply anf_cvt_disjoint_occurs_free_ctx_app; eauto. }
          assert (Hglob_e2_base : global_env_rel' (kn_deps e2) rho).
          { eapply global_env_rel_mono; [exact Hglob |].
            intros k Hk.
            unfold kn_deps. simpl.
            apply KernameSet.union_spec. right. exact Hk. }
          assert (Hglob_e2 :
            global_env_rel' (kn_deps e2) (M.set x1 (Vfun rho1 Bs f4) rho)).
          { eapply global_env_rel_set; [exact Hglob_e2_base |].
            intros k_g _ Hlk_g decl_g body_g Hdecl_g Hbody_g src_vg f_g t_g Heval_g.
            assert (Heval_g' : exists fg tg,
              src_eval [] body_g (fuel_sem.Val (fuel_sem.ClosFix_v rho' mfix idx)) fg tg).
            { eapply anf_cvt_cmap_eval;
                [exact H | exact Hcvt_e1 | exact Hdis | exact Hdis_cmap
                | exact Hcons | exact Hcmap | exact Hlk_g | exact Hdecl_g | exact Hbody_g]. }
            destruct Heval_g' as [fg [tg Heval_g']].
            pose proof (eval_val_exact_det _ _ _ _ _ _ _ _ Heval_g Heval_g')
              as [Heq_src _].
            subst src_vg. exact Hrel_fix_saved. }
          assert (Hdis_vn_S2 : Disjoint _ (FromList vnames) S2).
          { eapply Disjoint_Included_r;
              [eapply anf_cvt_exp_subset; eassumption | exact Hdis]. }
          assert (Hdis_cmap_S2 : Disjoint _ (cmap_vars cmap) S2).
          { eapply Disjoint_Included_r;
              [eapply anf_cvt_exp_subset; eassumption | exact Hdis_cmap]. }
          unfold fuel_sem.fix_body in H0.
          destruct (nth_error mfix idx) as [d0|] eqn:Hnth_d; [| discriminate].
          injection H0 as Hbody_eq.
          assert (Hfix_ex : exists d na0 e_body x_pc C_bc r_bc S_body1 S_body2,
            nth_error mfix idx = Some d /\
            EAst.dbody d = EAst.tLambda na0 e_body /\
            find_def f4 Bs = Some (func_tag, [x_pc], C_bc |[ Ehalt r_bc ]|) /\
            anf_cvt_rel' S_body1 e_body (x_pc :: List.rev fnames ++ names) S_body2 C_bc r_bc /\
            Disjoint _ (x_pc |: (FromList fnames :|: FromList names)) S_body1 /\
            ~ x_pc \in (FromList fnames :|: FromList names) /\
            x_pc \in S1 /\ S_body1 \subset S1).
          { eapply anf_fix_rel_exists; eassumption. }
          destruct Hfix_ex as
            (d0' & na0' & e_body & x_pc & C_bc & r_bc & S_body1 & S_body2 &
             Hnth_d' & Hbody_d' & Hfind_fc & Hcvt_bc &
             Hdis_xpc & Hfresh_xpc & Hxpc_in_S1 & Hsbody_sub).
          assert (d0' = d0) by congruence. subst d0'.
          rewrite Hbody_eq in Hbody_d'. injection Hbody_d' as <- <-.
          set (rho_bc := M.set x_pc v2' (def_funs Bs Bs rho1 rho1)).
          assert (Hwf_body :
            wellformed Σ (Datatypes.S (Datatypes.length (List.rev fnames ++ names))) body = true).
          { rewrite length_app, length_rev.
            assert (Hfl : Datatypes.length fnames = Datatypes.length mfix)
              by (eapply anf_fix_rel_fnames_length; exact H17).
            assert (Hle : Datatypes.length names = Datatypes.length rho').
            { symmetry. exact (@anf_env_rel_length func_tag default_tag tgm cmap Σ box_dc box_tag
                                               _ _ _ H7). }
            rewrite Hfl, Hle.
            inversion Hwf_fix as [| | ? ? ? Hwf_rho' Hidx_bound Hwf_mfix_bodies].
            subst.
            eapply Forall_forall in Hwf_mfix_bodies;
              [| eapply nth_error_In; exact Hnth_d].
            destruct Hwf_mfix_bodies as [_ Hwf_bod].
            rewrite Hbody_eq in Hwf_bod.
            cbn [wellformed] in Hwf_bod.
            rewrite Bool.andb_true_iff in Hwf_bod.
            exact (proj2 Hwf_bod). }
          assert (Hwf_body_env : well_formed_env Σ (v2 :: fuel_sem.make_rec_env mfix rho')).
          { constructor; [exact Hwf_v2 |].
            inversion Hwf_fix as [| | ? ? ? Hwf_rho' Hidx_bound Hwf_mfix_bodies].
            subst.
            eapply well_formed_env_make_rec_env; eauto. }
          assert (Hcons_body :
            env_consistent (x_pc :: List.rev fnames ++ names)
                           (v2 :: fuel_sem.make_rec_env mfix rho')).
          { eapply (env_consistent_extend_fresh
                      x_pc (List.rev fnames ++ names) v2
                      (fuel_sem.make_rec_env mfix rho')).
            - eapply (@anf_correct.env_consistent_make_rec_env
                        func_tag default_tag tgm cmap Σ box_dc box_tag
                        fnames names mfix rho');
                [exact H10 | exact H8 | exact H14 |].
              eapply anf_fix_rel_fnames_length. exact H17.
            - intro Hc. apply Hfresh_xpc.
              rewrite FromList_app, FromList_rev in Hc. exact Hc. }
          assert (Hcmap_body :
            cmap_consistent' (x_pc :: List.rev fnames ++ names)
                             (v2 :: fuel_sem.make_rec_env mfix rho')).
          { eapply cmap_consistent_extend.
            - eapply (@anf_correct.cmap_consistent_make_rec_env
                        func_tag default_tag tgm cmap Σ box_dc box_tag
                        fnames names mfix rho');
                [exact H9 | exact H13 |].
              eapply anf_fix_rel_fnames_length. exact H17.
            - intros k_c decl_c body_c Hlk_c Hdecl_c Hbody_c. exfalso.
              destruct H12 as [Hdc]. apply (Hdc x_pc).
              constructor; [exists k_c; exact Hlk_c | exact Hxpc_in_S1]. }
          assert (Hdis_names_S1 :
            Disjoint _ (FromList (x_pc :: List.rev fnames ++ names)) S_body1).
          { rewrite FromList_cons, FromList_app, FromList_rev.
            eapply Disjoint_Included_l; [| exact Hdis_xpc].
            apply Included_refl. }
          assert (Hdis_cmap_body : Disjoint _ (cmap_vars cmap) S_body1).
          { eapply Disjoint_Included_r; [exact Hsbody_sub | exact H12]. }
          assert (Henv_body :
            anf_env_rel' (x_pc :: List.rev fnames ++ names)
                         (v2 :: fuel_sem.make_rec_env mfix rho') rho_bc).
          { unfold rho_bc.
            constructor.
            - exists v2'. split; [rewrite M.gss; reflexivity | exact Hrel_v2].
            - eapply anf_env_rel_weaken.
              + eapply anf_env_rel_extend_fundefs; eassumption.
              + intro Hc. apply Hfresh_xpc.
                rewrite FromList_app, FromList_rev in Hc. exact Hc. }
          assert (Hglob_body : global_env_rel' (kn_deps body) rho_bc).
          { unfold rho_bc.
            eapply global_env_rel_set_fresh.
            - eapply global_env_rel_def_funs.
              + eapply global_env_rel_mono; [exact H18 |].
                intros kn Hkn.
                unfold kn_deps_mfix.
                apply Exists_exists.
                exists d0. split.
                * eapply nth_error_In. exact Hnth_d.
                * rewrite Hbody_eq. simpl. exact Hkn.
              + rewrite (Same_set_all_fun_name Bs).
                erewrite anf_fix_rel_names by exact H17. exact H13.
            - intro Hcm. destruct H12 as [Hdc]. apply (Hdc x_pc).
              constructor; [exact Hcm | exact Hxpc_in_S1]. }
          assert (Hdis_ehalt :
            Disjoint _ (occurs_free (Ehalt r_bc)) ((S_body1 \\ S_body2) \\ [set r_bc])).
          { eapply Disjoint_Included_l; [| eapply Disjoint_Singleton_l].
            - intros z Hz. remember (Ehalt r_bc) as eh.
              destruct Hz; try discriminate.
              injection Heqeh as ->. constructor.
            - intro Habs. destruct Habs as [_ Hc]. apply Hc. constructor. }
          assert (Hfix_body :
            fuel_sem.fix_body mfix idx = Some (EAst.tLambda na body)).
          { unfold fuel_sem.fix_body. rewrite Hnth_d. now rewrite Hbody_eq. }
          assert (Hns_body :
            src_not_stuck (v2 :: fuel_sem.make_rec_env mfix rho') body).
          { eapply src_not_stuck_fixapp_body
                      with (rho := rho0) (e1 := e1) (e2 := e2)
                           (rho' := rho')
                           (rho'' := fuel_sem.make_rec_env mfix rho')
                           (idx := idx) (na := na) (mfix := mfix)
                           (body := body) (v2 := v2)
                           (f1 := f1) (t1 := t1) (f2 := f2) (t2 := t2);
              [exact H | exact Hfix_body | reflexivity | exact H2 |].
            right. exact Hdiv. }
          assert (Hlt_body : div_lt (f3, body) (f0, e0)).
          { unfold div_lt, div_measure.
            apply Relation_Operators.left_lex.
            assert (Hlt_f : f3 < f0).
            { cbv [one_i fuel_resource_LambdaBox fuel_exp] in H3.
              simpl in H3. lia. }
            exact Hlt_f. }
          pose proof (IH (f3, body) Hlt_body
                         (v2 :: fuel_sem.make_rec_env mfix rho') t3 H4) as IHbody.
          unfold anf_cvt_correct_oot_lower_bound_goal in IHbody.
          destruct (IHbody rho_bc (x_pc :: List.rev fnames ++ names) C_bc r_bc S_body1 S_body2
                           Hwf_body_env
                           Hwf_body
                           Hcons_body
                           Hcmap_body
                           Hdis_names_S1
                           Hdis_cmap_body
                           Henv_body
                           Hglob_body
                           Hcvt_bc
                           (Ehalt r_bc)
                           Hdis_ehalt
                           Hns_body)
            as [c3 [Hlb3 Hoot3]].
          set (rho_app := M.set x2 v2' (M.set x1 (Vfun rho1 Bs f4) rho)).
          destruct (Pos.eq_dec x1 x2) as [Heq_x1x2 | Hneq_x1x2].
          * subst x2.
            assert (Hrel_rho_ex : exists v_rho,
              M.get x1 rho = Some v_rho /\
              anf_val_rel' (fuel_sem.ClosFix_v rho' mfix idx) v_rho /\
              anf_val_rel' v2 v_rho /\
              fuel_sem.ClosFix_v rho' mfix idx = v2).
            { destruct (In_dec Pos.eq_dec x1 vnames) as [Hin_vn | Hni_vn].
              - apply In_nth_error in Hin_vn. destruct Hin_vn as [k0 Hk0].
                assert (Heval1_k : nth_error rho0 k0 = Some (fuel_sem.ClosFix_v rho' mfix idx)).
                { eapply anf_cvt_rel_var_lookup;
                    [exact H | exact Hcvt_e1 | exact Hdis | exact Hdis_cmap
                    | exact Hcons | exact Hcmap | exact Hk0]. }
                assert (Heval2_k : nth_error rho0 k0 = Some v2).
                { eapply anf_cvt_rel_var_lookup;
                    [exact H2 | exact Hcvt_e2
                    | eapply Disjoint_Included_r;
                        [eapply anf_cvt_exp_subset; exact Hcvt_e1 | exact Hdis]
                    | eapply Disjoint_Included_r;
                        [eapply anf_cvt_exp_subset; exact Hcvt_e1 | exact Hdis_cmap]
                    | exact Hcons | exact Hcmap | exact Hk0]. }
                destruct (Forall2_nth_error_r _ _ _ _ _ Henv Hk0)
                  as [v_src [Hsrc [v_rho [Hget Hrel_rho0]]]].
                assert (v_src = fuel_sem.ClosFix_v rho' mfix idx) by congruence.
                subst v_src.
                assert (Heq_v2 : fuel_sem.ClosFix_v rho' mfix idx = v2) by congruence.
                exists v_rho. split; [exact Hget |]. split; [exact Hrel_rho0 |].
                split; [subst v2; exact Hrel_rho0 | exact Heq_v2].
              - destruct (@anf_cvt_result_in_consumed
                            func_tag default_tag tgm cmap
                            S e1 vnames S2 C1 x1 Hcvt_e1)
                  as [Hin1 | [Hin1 | Hin1]].
                + contradiction.
                + exfalso.
                  destruct (@anf_cvt_result_in_consumed
                              func_tag default_tag tgm cmap
                              S2 e2 vnames S3 C2 x1 Hcvt_e2)
                    as [Hin2 | [Hin2 | Hin2]].
                  * contradiction.
                  * eapply anf_cvt_result_not_in_output;
                      [exact Hcvt_e1 | exact Hdis | exact Hdis_cmap | exact Hin2].
                  * destruct Hdis_cmap as [Hdc]. apply (Hdc x1).
                    constructor; [exact Hin2 | exact Hin1].
                + destruct (@anf_cvt_cmap_result_in_deps
                              func_tag default_tag tgm cmap
                              S e1 vnames S2 C1 x1 Hcvt_e1 Hin1
                              Hdis Hdis_cmap Hni_vn)
                    as [k_c1 [Hlk1 Hdep1]].
                  assert (Hkc_deps : kn_deps (EAst.tApp e1 e2) k_c1).
                  { unfold kn_deps. simpl. apply KernameSet.union_spec. left. exact Hdep1. }
                  destruct (Hglob k_c1 x1 Hkc_deps Hlk1)
                    as (decl_g & body_g & v_rho & Hdecl_g & Hbody_g & Hget_g & Hrel_g).
                  exists v_rho. split; [exact Hget_g |].
                  assert (Heval1_cmap : exists f_c t_c,
                    src_eval [] body_g (fuel_sem.Val (fuel_sem.ClosFix_v rho' mfix idx)) f_c t_c).
                  { eapply anf_cvt_cmap_eval;
                      [exact H | exact Hcvt_e1 | exact Hdis | exact Hdis_cmap
                      | exact Hcons | exact Hcmap | exact Hlk1 | exact Hdecl_g | exact Hbody_g]. }
                  destruct Heval1_cmap as [f_c1 [t_c1 Hev1]].
                  assert (Heval2_cmap : exists f_c t_c,
                    src_eval [] body_g (fuel_sem.Val v2) f_c t_c).
                  { eapply anf_cvt_cmap_eval;
                      [exact H2 | exact Hcvt_e2
                      | eapply Disjoint_Included_r;
                          [eapply anf_cvt_exp_subset; exact Hcvt_e1 | exact Hdis]
                      | eapply Disjoint_Included_r;
                          [eapply anf_cvt_exp_subset; exact Hcvt_e1 | exact Hdis_cmap]
                      | exact Hcons | exact Hcmap | exact Hlk1 | exact Hdecl_g | exact Hbody_g]. }
                  destruct Heval2_cmap as [f_c2 [t_c2 Hev2]].
                  split; [exact (Hrel_g _ _ _ Hev1) |].
                  split; [exact (Hrel_g _ _ _ Hev2) |].
                  pose proof (eval_val_exact_det _ _ _ _ _ _ _ _ Hev1 Hev2) as [Heq_src _].
                  exact Heq_src. }
            destruct Hrel_rho_ex as [v_rho [Hget_rho [Hrel_rho [Hrel_rho_v2 Heq_v2]]]].
            assert (Hpv_cv : forall j, preord_val cenv eq_fuel j
                      (Vfun rho1 Bs f4) v2').
            { intro j.
              eapply preord_val_trans; [tci | exact eq_fuel_idemp | | ].
              - eapply (@anf_cvt_val_alpha_equiv
                  _ _ _ _ eq_fuel eq_fuel tgm cmap cenv
                  eq_fuel_compat' (fun _ _ H0 => H0)
                  nat src_fuel_res src_trace_res
                  Σ box_dc Hglob_term func_tag default_tag).
                exact Hrel_fix_saved.
                exact Hrel_rho.
              - intros m0.
                eapply (@anf_cvt_val_alpha_equiv
                  _ _ _ _ eq_fuel eq_fuel tgm cmap cenv
                  eq_fuel_compat' (fun _ _ H0 => H0)
                  nat src_fuel_res src_trace_res
                  Σ box_dc Hglob_term func_tag default_tag).
                rewrite Heq_v2 in Hrel_rho. exact Hrel_rho.
                exact Hrel_v2. }
            assert (Hpv_inst := Hpv_cv (c3 + 1)%nat).
            rewrite preord_val_eq in Hpv_inst.
            destruct v2' as [ | rho2_fc B2 f2_v | | ];
              try (simpl in Hpv_inst; contradiction).
            assert (Hset_fc :
              Some rho_bc =
              set_lists [x_pc] [Vfun rho2_fc B2 f2_v] (def_funs Bs Bs rho1 rho1)).
            { unfold rho_bc. reflexivity. }
            edestruct Hpv_inst as (xs2_pc & e2_body & rho2_body &
              Hfind_v2 & Hset_v2 & Hbody_preord).
            { reflexivity. }
            { exact Hfind_fc. }
            { exact Hset_fc. }
            assert (Hbody_pe : preord_exp' cenv (preord_val cenv) eq_fuel eq_fuel
                      c3 (C_bc |[ Ehalt r_bc ]|, rho_bc) (e2_body, rho2_body)).
            { apply Hbody_preord. lia.
              constructor; [| constructor ].
              eapply preord_val_refl. tci. }
            destruct (Hbody_pe eval.OOT c3 tt (le_n _) Hoot3) as
              [v2_body_res [cin2_bc [cout2_bc [Hbstep2_bc [Hpost2_bc Hres2_bc]]]]].
            destruct cout2_bc.
            destruct v2_body_res as [|v2_body_val];
              [unfold eq_fuel in Hpost2_bc; simpl in Hpost2_bc; subst cin2_bc
              | simpl in Hres2_bc; contradiction].
            assert (Hoot_letapp :
              bstep_fuel cenv rho_app
                (Eletapp x x1 func_tag [x1] e_k) (Datatypes.S c3) eval.OOT tt).
            { unfold rho_app.
              assert (Hget_fun :
                M.get x1 (M.set x1 (Vfun rho2_fc B2 f2_v) (M.set x1 (Vfun rho1 Bs f4) rho)) =
                Some (Vfun rho2_fc B2 f2_v)).
              { rewrite M.gss. reflexivity. }
              assert (Hget_args :
                get_list [x1] (M.set x1 (Vfun rho2_fc B2 f2_v)
                                  (M.set x1 (Vfun rho1 Bs f4) rho)) =
                Some [Vfun rho2_fc B2 f2_v]).
              { simpl. rewrite M.gss. reflexivity. }
              pose proof
                (BStepf_run cenv
                   (M.set x1 (Vfun rho2_fc B2 f2_v) (M.set x1 (Vfun rho1 Bs f4) rho))
                   (Eletapp x x1 func_tag [x1] e_k) eval.OOT c3 tt
                   (BStept_letapp_oot cenv rho2_fc B2 f2_v [Vfun rho2_fc B2 f2_v] xs2_pc
                      e2_body e_k rho2_body
                      (M.set x1 (Vfun rho2_fc B2 f2_v) (M.set x1 (Vfun rho1 Bs f4) rho))
                      x x1 func_tag [x1]
                      c3 tt Hget_fun Hget_args Hfind_v2 (eq_sym Hset_v2) Hbstep2_bc))
                as Hbsf.
              unfold one, one_i in Hbsf.
              simpl in Hbsf.
              replace (c3 + 1)%nat with (Datatypes.S c3) in Hbsf by lia.
              exact Hbsf. }
            destruct (anf_cvt_correct_val_cont_oot
                        rho0 e2 v2 f2 t2
                        (M.set x1 (Vfun rho1 Bs f4) rho) vnames C2 x1 S2 S3
                        (Datatypes.S c3)
                        (Eletapp x x1 func_tag [x1] e_k)
                        (Vfun rho2_fc B2 f2_v) (Datatypes.S c3)
                        (le_n _)
                        Hwf
                        Hwfe2
                        Hcons
                        Hcmap
                        Hdis_vn_S2
                        Hdis_cmap_S2
                        Henv_e2
                        Hglob_e2
                        Hcvt_e2
                        Hdis_eletapp
                        H2
                        Hrel_v2
                        Hoot_letapp)
              as [c2 [Hlb2 Hoot2]].
            destruct (anf_cvt_correct_val_cont_oot
                        rho0 e1 (fuel_sem.ClosFix_v rho' mfix idx) f1 t1
                        rho vnames C1 x1 S S2 c2
                        (C2 |[ Eletapp x x1 func_tag [x1] e_k ]|)
                        (Vfun rho1 Bs f4) c2
                        (le_n _)
                        Hwf
                        Hwfe1
                        Hcons
                        Hcmap
                        Hdis
                        Hdis_cmap
                        Henv
                        Hglob_e1
                        Hcvt_e1
                        Hdis_ek1
                        H
                        Hrel_fix_saved
                        Hoot2)
              as [c [Hlb Hoot_tgt]].
            exists c. split.
            { cbv [one_i fuel_resource_LambdaBox fuel_exp] in H3.
              simpl in H3, Hlb, Hlb2, Hlb3 |- *.
              lia. }
            exact Hoot_tgt.
          * assert (Hoot_letapp :
              bstep_fuel cenv rho_app
                (Eletapp x x1 func_tag [x2] e_k) (Datatypes.S c3) eval.OOT tt).
            { unfold rho_app.
              assert (Hget_fun :
                M.get x1 (M.set x2 v2' (M.set x1 (Vfun rho1 Bs f4) rho)) =
                Some (Vfun rho1 Bs f4)).
              { rewrite M.gso by exact Hneq_x1x2. rewrite M.gss. reflexivity. }
              assert (Hget_args :
                get_list [x2] (M.set x2 v2' (M.set x1 (Vfun rho1 Bs f4) rho)) =
                Some [v2']).
              { simpl. rewrite M.gss. reflexivity. }
              assert (Hset_fc :
                set_lists [x_pc] [v2'] (def_funs Bs Bs rho1 rho1) = Some rho_bc).
              { unfold rho_bc. reflexivity. }
              pose proof
                (BStepf_run cenv
                   (M.set x2 v2' (M.set x1 (Vfun rho1 Bs f4) rho))
                   (Eletapp x x1 func_tag [x2] e_k) eval.OOT c3 tt
                   (BStept_letapp_oot cenv rho1 Bs f4 [v2'] [x_pc]
                      (C_bc |[ Ehalt r_bc ]|) e_k rho_bc
                      (M.set x2 v2' (M.set x1 (Vfun rho1 Bs f4) rho))
                      x x1 func_tag [x2]
                      c3 tt Hget_fun Hget_args Hfind_fc Hset_fc Hoot3))
                as Hbsf.
              unfold one, one_i in Hbsf.
              simpl in Hbsf.
              replace (c3 + 1)%nat with (Datatypes.S c3) in Hbsf by lia.
              exact Hbsf. }
            destruct (anf_cvt_correct_val_cont_oot
                        rho0 e2 v2 f2 t2
                        (M.set x1 (Vfun rho1 Bs f4) rho) vnames C2 x2 S2 S3
                        (Datatypes.S c3)
                        (Eletapp x x1 func_tag [x2] e_k)
                        v2' (Datatypes.S c3)
                        (le_n _)
                        Hwf
                        Hwfe2
                        Hcons
                        Hcmap
                        Hdis_vn_S2
                        Hdis_cmap_S2
                        Henv_e2
                        Hglob_e2
                        Hcvt_e2
                        Hdis_eletapp
                        H2
                        Hrel_v2
                        Hoot_letapp)
              as [c2 [Hlb2 Hoot2]].
            destruct (anf_cvt_correct_val_cont_oot
                        rho0 e1 (fuel_sem.ClosFix_v rho' mfix idx) f1 t1
                        rho vnames C1 x1 S S2 c2
                        (C2 |[ Eletapp x x1 func_tag [x2] e_k ]|)
                        (Vfun rho1 Bs f4) c2
                        (le_n _)
                        Hwf
                        Hwfe1
                        Hcons
                        Hcmap
                        Hdis
                        Hdis_cmap
                        Henv
                        Hglob_e1
                        Hcvt_e1
                        Hdis_ek1
                        H
                        Hrel_fix_saved
                        Hoot2)
              as [c [Hlb Hoot_tgt]].
            exists c. split.
            { cbv [one_i fuel_resource_LambdaBox fuel_exp] in H3.
              simpl in H3, Hlb, Hlb2, Hlb3 |- *.
              lia. }
            exact Hoot_tgt.
        + (* eval_LetIn_step *)
          subst r.
          rewrite <- Heqe_cur in Hrel, Hwfe, Hglob, Hdiv, H3 |- *.
          inv Hrel.
          match goal with
          | [ Hb : anf_cvt_rel _ _ _ _ S b vnames ?S2 ?C1 ?x1,
              Ht : anf_cvt_rel _ _ _ _ ?S2 t0 (x1 :: vnames) S' ?C2 x |- _ ] =>
              rename Hb into Hcvt_b;
              rename Ht into Hcvt_t
          end.
          rewrite <- app_ctx_f_fuse.
          assert (Hdis_ctx :
                    Disjoint _ (occurs_free (C2 |[ e_k ]|))
                             ((S \\ S2) \\ [set x1])).
          { eapply anf_cvt_disjoint_occurs_free_ctx; eauto. }
          assert (Hwfb : wellformed Σ (Datatypes.length vnames) b = true).
          { unfold wellformed in Hwfe |- *.
            simpl in Hwfe. fold (@wellformed efl) in Hwfe.
            apply andb_true_iff in Hwfe as [Hwf1 Hwft].
            apply andb_true_iff in Hwf1 as [_ Hwfb].
            exact Hwfb. }
          assert (Hwft : wellformed Σ (Datatypes.S (Datatypes.length vnames)) t0 = true).
          { unfold wellformed in Hwfe |- *.
            simpl in Hwfe. fold (@wellformed efl) in Hwfe.
            apply andb_true_iff in Hwfe as [_ Hwft].
            exact Hwft. }
          assert (Hwf_v1 : well_formed_val Σ v1).
          { pose proof Henv as Henv_len.
            unfold anf_env_rel' in Henv_len.
            apply Forall2_length in Henv_len.
            eapply eval_preserves_wf; [exact Hglob_wf | exact Hwf | | exact H].
            rewrite Henv_len.
            exact Hwfb. }
          destruct (val_rel_exists v1 Hwf_v1) as [v1' Hrel1].
          assert (Hns_t : src_not_stuck (v1 :: rho0) t0).
          { destruct (classic (exists (src_v : fuel_sem.value) (f' : nat) (t' : nat),
                          src_eval (v1 :: rho0) t0 (fuel_sem.Val src_v) f' t'))
              as [Hval_t | Hnoval_t].
            - left. exact Hval_t.
            - right. intros f'.
              destruct (Hdiv (f1 + f')) as [t_let Hoot_let].
              inversion Hoot_let; subst.
              + exfalso.
                cbv [one_i fuel_resource_LambdaBox fuel_exp] in H1.
                simpl in H1. lia.
              + remember (EAst.tLetIn na b t0) as e_let in H6.
                remember fuel_sem.OOT as r_oot in H6.
                destruct H6; try discriminate.
                * injection Heqe_let as <- <- <-.
                  assert (Heq_bind : v1 = v0 /\ f1 = f3 /\ t1 = t4)
                    by (eapply (@fuel_sem.eval_val_exact_det
                                  nat
                                  (LambdaBox_resource_fuel
                                     default_tag tgm box_dc box_tag)
                                  (LambdaBox_resource_trace
                                     default_tag tgm box_dc box_tag)
                                  Σ box_dc); eauto).
                  destruct Heq_bind as [-> [-> ->]].
                  assert (f4 = f') by (simpl in H1; lia).
                  subst f4. rewrite Heqr_oot in H4. exists t5. exact H4.
                * injection Heqe_let as <- <- <-.
                  assert (f3 < f1) as Hlt_bind.
                  { eapply src_eval_val_gt_oot; eauto. }
                  lia. }
          assert (Hlt_t : div_lt (f2, t0) (f0, e0)).
          { unfold div_lt, div_measure.
            destruct f1 as [| f1'].
            - replace f0 with f2 by (simpl in H3; lia).
              cbn in Heqe_cur. rewrite <- Heqe_cur.
              apply Relation_Operators.right_lex. simpl. lia.
            - apply Relation_Operators.left_lex.
              assert (Hlt_f : f2 < f0).
              { cbv [one_i fuel_resource_LambdaBox fuel_exp] in H3.
                simpl in H3. lia. }
              exact Hlt_f. }
          assert (Hcons_t : env_consistent (x1 :: vnames) (v1 :: rho0)).
          { eapply env_consistent_extend_from_cvt; eauto. }
          assert (Hcmap_t : cmap_consistent' (x1 :: vnames) (v1 :: rho0)).
          { eapply cmap_consistent_extend_from_cvt; eauto. }
          assert (Hdis_vn_t : Disjoint _ (FromList (x1 :: vnames)) S2).
          { assert (Hx1_not_S2 : ~ x1 \in S2)
              by (eapply anf_cvt_result_not_in_output; eassumption).
            assert (Hvn_S2 : Disjoint _ (FromList vnames) S2).
            { eapply Disjoint_Included_r;
                [exact (anf_cvt_exp_subset _ _ _ _ _ _ _ _ _ _ Hcvt_b) | exact Hdis]. }
            constructor. intros z Hz. inv Hz.
            lazymatch goal with
            | [ Hmem : Ensembles.In _ (FromList (x1 :: vnames)) z,
                HS2 : Ensembles.In _ S2 z |- _ ] =>
                unfold FromList, Ensembles.In in Hmem;
                simpl in Hmem;
                destruct Hmem as [Hzx1 | Hin_vn];
                [ subst z; exact (Hx1_not_S2 HS2)
                | eapply Hvn_S2; constructor; [exact Hin_vn | exact HS2] ]
            end. }
          assert (Hdis_cmap_t : Disjoint _ (cmap_vars cmap) S2).
          { eapply Disjoint_Included_r;
              [exact (anf_cvt_exp_subset _ _ _ _ _ _ _ _ _ _ Hcvt_b) | exact Hdis_cmap]. }
          assert (Henv_t : anf_env_rel' (x1 :: vnames) (v1 :: rho0) (M.set x1 v1' rho)).
          { constructor.
            - exists v1'. split; [rewrite M.gss; reflexivity | exact Hrel1].
            - eapply anf_env_rel_set; [exact Henv |].
              intros k Hk.
              assert (Hek : nth_error rho0 k = Some v1).
              { change positive with var in Hk.
                eapply anf_cvt_rel_var_lookup;
                  [exact H | exact Hcvt_b
                  | exact Hdis | exact Hdis_cmap | exact Hcons | exact Hcmap | exact Hk]. }
              exists v1. split; [exact Hek | exact Hrel1]. }
          assert (Hglob_t :
                    global_env_rel' (kn_deps t0) (M.set x1 v1' rho)).
          { unfold global_env_rel' in *. intros kn vn0 Hd Hl.
            assert (Hd' : kn_deps (EAst.tLetIn na b t0) kn).
            { unfold kn_deps. simpl. apply KernameSet.union_spec. right. exact Hd. }
            destruct (Hglob kn vn0 Hd' Hl)
              as [d1 [b1 [av [Hd1 [Hd2 [Hgv Hd3]]]]]].
            destruct (Pos.eq_dec vn0 x1) as [-> | Hneq_vn].
            - exists d1, b1, v1'. repeat (split; [assumption |]).
              split; [rewrite M.gss; reflexivity |].
              intros src_v f' t' Heval_src.
              destruct (anf_cvt_cmap_eval _ _ _ _ _ H
                          _ _ _ _ _ kn d1 b1
                          Hcvt_b Hdis Hdis_cmap Hcons Hcmap Hl Hd1 Hd2)
                as [f1' [t1' Heval_body_v1]].
              assert (src_v = v1) by (eapply eval_val_det; eassumption).
              subst src_v. exact Hrel1.
            - exists d1, b1, av. repeat (split; [assumption |]).
              split; [rewrite M.gso; [exact Hgv | exact Hneq_vn] | exact Hd3]. }
          assert (Hdis_ek_t :
                    Disjoint _ (occurs_free e_k) ((S2 \\ S') \\ [set x])).
          { eapply Disjoint_Included_r; [| exact Hdis_ek].
            intros z Hz. destruct Hz as [[Hz1 Hz2] Hz3].
            constructor.
            - constructor; [| exact Hz2].
              eapply anf_cvt_exp_subset; [exact Hcvt_b | exact Hz1].
            - exact Hz3. }
          assert (Hglob_b : global_env_rel' (kn_deps b) rho).
          { eapply global_env_rel_mono; [exact Hglob |].
            intros k Hk.
            unfold kn_deps. simpl.
            apply KernameSet.union_spec. left. exact Hk. }
          pose proof (IH (f2, t0) Hlt_t (v1 :: rho0) t2 H0) as IHt.
          unfold anf_cvt_correct_oot_lower_bound_goal in IHt.
          destruct (IHt (M.set x1 v1' rho) (x1 :: vnames) C2 x S2 S'
                        (Forall_cons _ Hwf_v1 Hwf)
                        Hwft
                        Hcons_t
                        Hcmap_t
                        Hdis_vn_t
                        Hdis_cmap_t
                        Henv_t
                        Hglob_t
                        Hcvt_t
                        e_k
                        Hdis_ek_t
                        Hns_t)
            as [c2 [Hlb2 Hoot2]].
          destruct (anf_cvt_correct_val_cont_oot
                      rho0 b v1 f1 t1 rho vnames C1 x1 S S2 c2
                      (C2 |[ e_k ]|) v1' c2
                      (le_n _)
                      Hwf
                      Hwfb
                      Hcons
                      Hcmap
                      Hdis
                      Hdis_cmap
                      Henv
                      Hglob_b
                      Hcvt_b
                      Hdis_ctx
                      H
                      Hrel1
                      Hoot2)
            as [c [Hlb Hoot_tgt]].
          exists c. split.
          { simpl in Hlb, Hlb2 |- *. lia. }
          { exact Hoot_tgt. }
        + (* eval_LetIn_step_OOT *)
          rewrite <- Heqe_cur in Hrel, Hwfe, Hglob, Hdiv, H3 |- *.
          inv Hrel.
          match goal with
          | [ Hb : anf_cvt_rel _ _ _ _ S b vnames ?S2 ?C1 ?x1,
              Ht : anf_cvt_rel _ _ _ _ ?S2 t0 (x1 :: vnames) S' ?C2 x |- _ ] =>
              rename Hb into Hcvt_b;
              rename Ht into Hcvt_t
          end.
          rewrite <- app_ctx_f_fuse.
          assert (Hdis_ctx :
                    Disjoint _ (occurs_free (C2 |[ e_k ]|))
                             ((S \\ S2) \\ [set x1])).
          { eapply anf_cvt_disjoint_occurs_free_ctx; eauto. }
          assert (Hns_b : src_not_stuck rho0 b).
          { destruct (classic (exists (src_v : fuel_sem.value) (f' : nat) (t' : nat),
                        src_eval rho0 b (fuel_sem.Val src_v) f' t'))
              as [Hval_b | Hnoval_b].
            - left. exact Hval_b.
            - right. intros f'.
              destruct (Hdiv f') as [t_let Hoot_let].
              inversion Hoot_let; subst.
              + simpl in H0. lia.
              + remember (EAst.tLetIn na b t0) as e_let in H0.
                remember fuel_sem.OOT as r_oot in H0.
                destruct H0; try discriminate.
                * injection Heqe_let as <- <- <-.
                  exfalso. apply Hnoval_b. eexists _, _, _. exact H0.
                * injection Heqe_let as <- <- <-.
                  exists t3.
                  cbv [one_i fuel_resource_LambdaBox fuel_exp].
                  simpl.
                  replace (f2 + 0)%nat with f2 by lia.
                  exact H0. }
          assert (Hlt_b : div_lt (f1, b) (f0, e0)).
          { unfold div_lt, div_measure.
            replace f0 with f1 by (simpl in H3; lia).
            cbn in Heqe_cur.
            rewrite <- Heqe_cur.
            apply Relation_Operators.right_lex.
            simpl. lia. }
          assert (Hglob_b : global_env_rel' (kn_deps b) rho).
          { eapply global_env_rel_mono; [exact Hglob |].
            intros k Hk.
            unfold kn_deps. simpl.
            apply KernameSet.union_spec. left. exact Hk. }
          pose proof (IH (f1, b) Hlt_b rho0 t1 H)
            as IHb.
          unfold anf_cvt_correct_oot_lower_bound_goal in IHb.
          assert (Hwfb : wellformed Σ (Datatypes.length vnames) b = true).
          { unfold wellformed in Hwfe |- *.
            simpl in Hwfe. fold (@wellformed efl) in Hwfe.
            apply andb_true_iff in Hwfe as [Hwf1 _].
            apply andb_true_iff in Hwf1 as [_ Hwfb].
            exact Hwfb. }
          destruct (IHb rho vnames C1 x1 S S2
                      Hwf
                      Hwfb
                      Hcons
                      Hcmap
                      Hdis
                      Hdis_cmap
                      Henv
                      Hglob_b
                      Hcvt_b
                      (C2 |[ e_k ]|)
                      Hdis_ctx
                      Hns_b)
            as [c [Hlb Hoot_tgt]].
          exists c. split.
          { simpl in Hlb |- *. lia. }
          { exact Hoot_tgt. }
        + (* eval_Construct_step_OOT *)
          rewrite <- Heqe_cur in Hrel, Hwfe, Hglob, Hdiv, H3 |- *.
          inv Hrel.
          rename H12 into Hx_in_S.
          rename H13 into Hcvt_args.
          rename C0 into C_args.
          rename xs into xs_args.
          destruct (anf_cvt_rel_args_app_inv (S \\ [set x]) args_done (e1 :: args_rest)
                                             vnames S' C_args xs_args Hcvt_args)
            as (S_mid0 & C_done & C_tail & xs_done & xs_tail &
                Hxs_args & HC_args & Hcvt_done & Hcvt_tail0).
          remember (e1 :: args_rest) as args_tail in Hcvt_tail0.
          destruct Hcvt_tail0; try discriminate.
          injection Heqargs_tail as <- <-.
          match goal with
          | [ Hhd : anf_cvt_rel _ _ _ _ _ ?e_bad ?vn0 ?S_mid ?C_e1 ?x_e1,
              Htl : anf_cvt_rel_args _ _ _ _ ?S_mid ?args_rest0 ?vn0 ?S_end ?C_rest ?xs_rest |- _ ] =>
              rename Hhd into Hcvt_e1;
              rename Htl into Hcvt_rest;
              rename e_bad into e1;
              rename args_rest0 into args_rest;
              rename S_mid into S_mid;
              rename C_e1 into C_e1;
              rename x_e1 into x_e1;
              rename C_rest into C_rest;
              rename xs_rest into xs_rest
          end.
          rewrite HC_args.
          rewrite <- !app_ctx_f_fuse.
          assert (Hsub_done : S1 \subset (S \\ [set x])).
          { eapply anf_cvt_args_subset. exact Hcvt_done. }
          assert (Hsub_e1 : S2 \subset S1).
          { eapply anf_cvt_exp_subset. exact Hcvt_e1. }
          assert (Hsub_rest : S3 \subset S2).
          { eapply anf_cvt_args_subset. exact Hcvt_rest. }
          assert (Hdis_x :
                    Disjoint _ (FromList vn) (S \\ [set x])).
          { eapply Disjoint_Included_r; [eapply Setminus_Included | exact Hdis]. }
          assert (Hdis_cmap_x :
                    Disjoint _ (cmap_vars cmap) (S \\ [set x])).
          { eapply Disjoint_Included_r; [eapply Setminus_Included | exact Hdis_cmap]. }
          assert (Hdis_S1 : Disjoint _ (FromList vn) S1).
          { eapply Disjoint_Included_r; [exact Hsub_done | exact Hdis_x]. }
          assert (Hdis_cmap_S1 : Disjoint _ (cmap_vars cmap) S1).
          { eapply Disjoint_Included_r; [exact Hsub_done | exact Hdis_cmap_x]. }
          assert (Hctx_e1_inc :
                    occurs_free_ctx C1 \subset
                      FromList vn :|: (S1 \\ S2) :|: cmap_vars cmap).
          { eapply anf_cvt_occurs_free_ctx_exp; eauto. }
          assert (Hctx_rest_inc :
                    occurs_free_ctx C2 \subset
                      FromList vn :|: (S2 \\ S3) :|: cmap_vars cmap).
          { eapply anf_cvt_occurs_free_ctx_args_local.
            - exact Hcvt_rest.
            - eapply Disjoint_Included_r; [exact Hsub_e1 | exact Hdis_S1].
            - eapply Disjoint_Included_r; [exact Hsub_e1 | exact Hdis_cmap_S1]. }
          assert (Hxs_rest_inc :
                    FromList xs \subset FromList vn :|: S2 :|: cmap_vars cmap).
          { intros z Hz.
            destruct (@anf_cvt_rel_args_In_range
                        func_tag default_tag tgm cmap
                        xs S2 args_rest vn S3 C2 Hcvt_rest z Hz)
              as [Hz_vn | [Hz_S2 | Hz_cm]];
              [now left | now left; right | now right]. }
          assert (Hxs_done_not_S1 : Disjoint _ (FromList xs_done) S1).
          { constructor. intros z Hc.
            inversion Hc as [z0 Hz_done Hz_S1]; subst.
            eapply (@anf_cvt_rel_args_results_not_in_output
                      func_tag default_tag tgm cmap
                      xs_done (S \\ [set x]) args_done vn S1 C_done
                      Hcvt_done Hdis_x Hdis_cmap_x z Hz_done); exact Hz_S1. }
          assert (Hx1_loc : x1 \in FromList vn \/ x1 \in S1 \/ x1 \in cmap_vars cmap).
          { eapply anf_cvt_result_in_consumed. exact Hcvt_e1. }
          assert (Hx1_not_S2 : ~ x1 \in S2).
          { eapply anf_cvt_result_not_in_output; eauto. }
          assert (Hwf_args :
                    Forall (fun e => wellformed Σ (Datatypes.length vn) e = true)
                           (args_done ++ e1 :: args_rest)).
          { eapply wellformed_tConstruct. exact Hwfe. }
          apply Forall_app in Hwf_args.
          destruct Hwf_args as [Hwf_done Hwf_tail].
          pose proof (Forall_inv Hwf_tail) as Hwfe1.
          assert (Hlen_env : Datatypes.length rho0 = Datatypes.length vn).
          { exact (@anf_env_rel_length
                     func_tag default_tag tgm cmap Σ box_dc box_tag
                     vn rho0 rho Henv). }
          assert (Hwf_done_rho :
                    Forall (fun e => wellformed Σ (Datatypes.length rho0) e = true)
                           args_done).
          { rewrite Hlen_env. exact Hwf_done. }
          assert (Hwf_done_vals : Forall (well_formed_val Σ) vs0).
          { eapply eval_fuel_many_preserves_wf.
            - exact Hwf.
            - exact Hwf_done_rho.
            - exact H0. }
          destruct (Forall_val_rel_exists _ Hwf_done_vals) as [vs_done' Hrel_done_vals].
          assert (Henv_done :
                    anf_env_rel' vn rho0 (set_many xs_done vs_done' rho)).
          { eapply anf_env_rel_set_many_args with
                (rho_src := rho0) (es := args_done) (vs_src := vs0)
                (f := fs) (t := ts)
                (rho_tgt := rho) (vnames := vn)
                (S := (S \\ [set x])) (S' := S1)
                (C := C_done) (xs := xs_done) (vs_tgt := vs_done');
              eauto. }
          assert (Hglob_done : global_env_rel' (kn_deps_list args_done) rho).
          { eapply global_env_rel_mono; [exact Hglob |].
            intros k Hk.
            eapply kn_deps_list_subset_construct.
            unfold kn_deps_list in *.
            apply Exists_app. now left. }
          assert (Hglob_e1_base : global_env_rel' (kn_deps e1) rho).
          { eapply global_env_rel_mono; [exact Hglob |].
            intros k Hk.
            eapply kn_deps_list_subset_construct.
            unfold kn_deps_list.
            apply Exists_exists.
            exists e1. split.
            - apply in_or_app. right. simpl. auto.
            - exact Hk. }
          assert (Hglob_e1 :
                    global_env_rel' (kn_deps e1) (set_many xs_done vs_done' rho)).
          { eapply global_env_rel_set_many_args with
                (rho_tgt := rho) (vnames := vn)
                (S := (S \\ [set x])) (S' := S1)
                (C := C_done) (xs := xs_done)
                (vs_tgt := vs_done') (D := kn_deps e1); eauto. }
          assert (Hns_e1 : src_not_stuck rho0 e1).
          { eapply src_not_stuck_construct_arg
                      with (rho := rho0) (ind := ind) (c := c)
                           (args_done := args_done) (e := e1)
                           (args_rest := args_rest) (vs_done := vs0)
                           (fs := fs) (ts := ts);
              [exact H0 | right; exact Hdiv]. }
          assert (Hlt_e1 : div_lt (Datatypes.S f1, e1) (f0, e0)).
          { unfold div_lt, div_measure.
            destruct (Nat.eq_dec f0 (Datatypes.S f1)) as [Heq_f | Hneq_f].
            - rewrite Heq_f.
              cbn in Heqe_cur. subst e0.
              change (@Relation_Operators.lexprod nat (fun _ => nat) lt (fun _ => lt)
                        (existT (fun _ => nat) (Datatypes.S f1) (EInduction.size e1))
                        (existT (fun _ => nat) (Datatypes.S f1)
                           (EInduction.size
                              (EAst.tConstruct ind c (args_done ++ e1 :: args_rest))))).
              refine (@Relation_Operators.right_lex
                        nat (fun _ => nat) lt (fun _ => lt)
                        (Datatypes.S f1)
                        (EInduction.size e1)
                        (EInduction.size
                           (EAst.tConstruct ind c (args_done ++ e1 :: args_rest)))
                        _).
              simpl.
              rewrite MRList.list_size_app.
              simpl. lia.
            - refine (@Relation_Operators.left_lex
                        nat (fun _ => nat) lt (fun _ => lt)
                        (Datatypes.S f1) f0
                        (EInduction.size e1) (EInduction.size e0)
                        _).
              assert (Datatypes.S f1 < f0).
              { cbv [one_i fuel_resource_LambdaBox fuel_exp] in H3.
                simpl in H3. lia. }
              exact H. }
          set (c_tag := dcon_to_tag default_tag (dcon_of_con ind c) tgm) in *.
          set (e_k_inner :=
                 C2 |[ Econstr x c_tag (xs_done ++ x1 :: xs) e_k ]|) in *.
          set (e_k_done := C1 |[ e_k_inner ]|) in *.
          assert (HA_inner_sub :
                    ((S1 \\ S2) \\ [set x1]) \subset
                    ((S \\ S3) \\ [set x])).
          { intros z Hz.
            destruct Hz as [Hz12 Hzx1].
            destruct Hz12 as [HzS1 HnotS2].
            constructor.
            - constructor.
              + destruct (Hsub_done _ HzS1) as [HzS _]. exact HzS.
              + intros HzS3. apply HnotS2. eapply Hsub_rest. exact HzS3.
            - intros Hzx. inversion Hzx; subst.
              pose proof (Hsub_done _ HzS1) as HzSx.
              destruct HzSx as [_ Hnotx]. exact (Hnotx (In_singleton _ _)). }
          assert (HB_done_sub :
                    (((S \\ [set x]) \\ S1) \\ FromList xs_done) \subset
                    ((S \\ S3) \\ [set x])).
          { intros z Hz.
            destruct Hz as [HzS1' Hznot_xs].
            destruct HzS1' as [HzSx HnotS1].
            constructor.
            - constructor.
              + destruct HzSx as [HzS _]. exact HzS.
              + intros HzS3. apply HnotS1. eapply Hsub_e1. eapply Hsub_rest. exact HzS3.
            - intros Hzx. inversion Hzx; subst.
              destruct HzSx as [_ Hnotx]. exact (Hnotx (In_singleton _ _)). }
          assert (Hdis_ek_inner :
                    Disjoint _ (occurs_free e_k_inner) ((S1 \\ S2) \\ [set x1])).
          { set (U_inner :=
                   FromList vn :|:
                   (S2 :|:
                    (cmap_vars cmap :|:
                     (FromList xs_done :|:
                      ([set x1] :|: occurs_free e_k))))).
            assert (Hocc_inner_inc : occurs_free e_k_inner \subset U_inner).
            { unfold e_k_inner, U_inner.
              eapply Included_trans; [eapply occurs_free_ctx_app|].
              eapply Union_Included.
              - intros z Hz.
                specialize (Hctx_rest_inc _ Hz) as Hctxz.
                inversion Hctxz; subst; clear Hctxz.
                + inversion H; subst; clear H.
                  * match goal with
                    | [ Hz_vn : Ensembles.In _ (FromList vn) z |- _ ] =>
                        left; exact Hz_vn
                    end.
                  * match goal with
                    | [ Hz_s23 : Ensembles.In _ (S2 \\ S3) z |- _ ] =>
                        destruct Hz_s23 as [Hz_S2 _];
                        right; left; exact Hz_S2
                    end.
                + match goal with
                  | [ Hz_cm : Ensembles.In _ (cmap_vars cmap) z |- _ ] =>
                      right; right; left; exact Hz_cm
                  end.
              - eapply Included_trans; [eapply Setminus_Included|].
                rewrite occurs_free_Econstr.
                rewrite FromList_app, FromList_cons.
                eapply Union_Included.
                + eapply Union_Included.
                  * intros z Hz. right. right. right. left. exact Hz.
                  * eapply Union_Included.
                    -- intros z Hz. right. right. right. right. left. exact Hz.
                    -- intros z Hz.
                       specialize (Hxs_rest_inc _ Hz) as Hinc.
                       inversion Hinc; subst; clear Hinc.
                       { inversion H; subst; clear H.
                         - match goal with
                           | [ Hz_vn : Ensembles.In _ (FromList vn) z |- _ ] =>
                               left; exact Hz_vn
                           end.
                         - match goal with
                           | [ Hz_s2 : Ensembles.In _ S2 z |- _ ] =>
                               right; left; exact Hz_s2
                           end. }
                       { match goal with
                         | [ Hz_cm : Ensembles.In _ (cmap_vars cmap) z |- _ ] =>
                             right; right; left; exact Hz_cm
                         end. }
                + intros z Hz.
                  destruct Hz as [Hz_ek _].
                  right. right. right. right. right. exact Hz_ek. }
            eapply Disjoint_Included_l; [exact Hocc_inner_inc|].
            unfold U_inner.
            repeat eapply Union_Disjoint_l.
            - eapply Disjoint_Included_r; [eapply Setminus_Included|].
              eapply Disjoint_Included_r.
              2:{ exact Hdis_x. }
              intros z Hz. eapply Hsub_done. eapply Setminus_Included. exact Hz.
            - constructor. intros z Hc.
              inversion Hc; subst; clear Hc.
              match goal with
              | [ HzS2 : Ensembles.In _ S2 z,
                  HzA : Ensembles.In _ ((S1 \\ S2) \\ [set x1]) z |- _ ] =>
                  inversion HzA; subst; clear HzA;
                  match goal with
                  | [ Hz12 : Ensembles.In _ (S1 \\ S2) z |- _ ] =>
                      inversion Hz12; subst; clear Hz12;
                      match goal with
                      | [ HnotS2 : ~ Ensembles.In _ S2 z |- _ ] =>
                          exact (HnotS2 HzS2)
                      end
                  end
              end.
            - eapply Disjoint_Included_r; [eapply Setminus_Included|].
              eapply Disjoint_Included_r.
              2:{ exact Hdis_cmap_x. }
              intros z Hz. eapply Hsub_done. eapply Setminus_Included. exact Hz.
            - eapply Disjoint_Included_r; [eapply Setminus_Included|].
              eapply Disjoint_Included_r.
              + eapply Setminus_Included.
              + exact Hxs_done_not_S1.
            - constructor. intros z Hc.
              inversion Hc; subst; clear Hc.
              repeat match goal with
                     | H : Ensembles.In _ (_ \\ _) _ |- _ =>
                         inversion H; subst; clear H
                     | H : Ensembles.In _ [set _] _ |- _ =>
                         inversion H; subst; clear H
                     end.
              match goal with
              | [ Hnotx1 : ~ Ensembles.In _ [set ?y] ?y |- _ ] =>
                  exact (Hnotx1 (In_singleton _ _))
              end.
            - eapply Disjoint_Included_r; [exact HA_inner_sub | exact Hdis_ek]. }
          assert (Hdis_ek_done :
                    Disjoint _ (occurs_free e_k_done)
                             (((S \\ [set x]) \\ S1) \\ FromList xs_done)).
          { set (U_done :=
                   FromList vn :|:
                   (S1 :|:
                    (S2 :|:
                     (cmap_vars cmap :|:
                      (FromList xs_done :|:
                       ([set x1] :|: occurs_free e_k)))))).
            assert (Hocc_done_inc : occurs_free e_k_done \subset U_done).
            { unfold e_k_done, U_done.
              eapply Included_trans; [eapply occurs_free_ctx_app|].
              eapply Union_Included.
              - intros z Hz.
                specialize (Hctx_e1_inc _ Hz) as Hctxz.
                inversion Hctxz; subst; clear Hctxz.
                + inversion H; subst; clear H.
                  * match goal with
                    | [ Hz_vn : Ensembles.In _ (FromList vn) z |- _ ] =>
                        left; exact Hz_vn
                    end.
                  * match goal with
                    | [ Hz_s12 : Ensembles.In _ (S1 \\ S2) z |- _ ] =>
                        destruct Hz_s12 as [Hz_S1 _];
                        right; left; exact Hz_S1
                    end.
                + match goal with
                  | [ Hz_cm : Ensembles.In _ (cmap_vars cmap) z |- _ ] =>
                      right; right; right; left; exact Hz_cm
                  end.
              - eapply Included_trans; [eapply Setminus_Included|].
                unfold e_k_inner in Hdis_ek_inner |- *.
                set (U_inner :=
                       FromList vn :|:
                       (S2 :|:
                        (cmap_vars cmap :|:
                         (FromList xs_done :|:
                          ([set x1] :|: occurs_free e_k)))) ) in *.
                assert (occurs_free
                          (C2 |[ Econstr x c_tag (xs_done ++ x1 :: xs) e_k ]|) \subset U_inner).
                { unfold U_inner.
                  eapply Included_trans; [eapply occurs_free_ctx_app|].
                  eapply Union_Included.
                  - intros z Hz.
                    specialize (Hctx_rest_inc _ Hz) as Hctxz.
                    inversion Hctxz; subst; clear Hctxz.
                    + inversion H; subst; clear H.
                      * match goal with
                        | [ Hz_vn : Ensembles.In _ (FromList vn) z |- _ ] =>
                            left; exact Hz_vn
                        end.
                      * match goal with
                        | [ Hz_s23 : Ensembles.In _ (S2 \\ S3) z |- _ ] =>
                            destruct Hz_s23 as [Hz_S2 _];
                            right; left; exact Hz_S2
                        end.
                    + match goal with
                      | [ Hz_cm : Ensembles.In _ (cmap_vars cmap) z |- _ ] =>
                          right; right; left; exact Hz_cm
                      end.
                  - eapply Included_trans; [eapply Setminus_Included|].
                    rewrite occurs_free_Econstr.
                    rewrite FromList_app, FromList_cons.
                    eapply Union_Included.
                    + eapply Union_Included.
                      * intros z Hz. right. right. right. left. exact Hz.
                      * eapply Union_Included.
                        -- intros z Hz. right. right. right. right. left. exact Hz.
                        -- intros z Hz.
                           specialize (Hxs_rest_inc _ Hz) as Hinc.
                           inversion Hinc; subst; clear Hinc.
                           { inversion H; subst; clear H.
                             - match goal with
                               | [ Hz_vn : Ensembles.In _ (FromList vn) z |- _ ] =>
                                   left; exact Hz_vn
                               end.
                             - match goal with
                               | [ Hz_s2 : Ensembles.In _ S2 z |- _ ] =>
                                   right; left; exact Hz_s2
                               end. }
                           { match goal with
                             | [ Hz_cm : Ensembles.In _ (cmap_vars cmap) z |- _ ] =>
                                 right; right; left; exact Hz_cm
                             end. }
                    + intros z Hz.
                      destruct Hz as [Hz_ek _].
                      right. right. right. right. right. exact Hz_ek. }
                intros z Hz.
                specialize (H _ Hz) as Hinner.
                unfold U_inner in Hinner.
                inversion Hinner; subst; clear Hinner.
                + left. assumption.
                + match goal with
                  | Hs2_rest : Ensembles.In _ (_ :|: _) z |- _ =>
                      inversion Hs2_rest; subst; clear Hs2_rest
                  end.
                  * right. right. left. assumption.
                  * match goal with
                    | Hcm_rest : Ensembles.In _ (_ :|: _) z |- _ =>
                        inversion Hcm_rest; subst; clear Hcm_rest
                    end.
                    -- right. right. right. left. assumption.
                    -- match goal with
                       | Hxs_rest : Ensembles.In _ (_ :|: _) z |- _ =>
                           inversion Hxs_rest; subst; clear Hxs_rest
                       end.
                       ++ right. right. right. right. left. assumption.
                       ++ match goal with
                          | Htail : Ensembles.In _ (_ :|: _) z |- _ =>
                              inversion Htail; subst; clear Htail
                          end.
                          ** right. right. right. right. right. left. assumption.
                          ** right. right. right. right. right. right. assumption. }
            eapply Disjoint_Included_l; [exact Hocc_done_inc|].
            unfold U_done.
            repeat eapply Union_Disjoint_l.
            - eapply Disjoint_Included_r; [eapply Setminus_Included|].
              eapply Disjoint_Included_r.
              + eapply Setminus_Included.
              + exact Hdis_x.
            - constructor. intros z Hc.
              inversion Hc; subst; clear Hc.
              match goal with
              | [ HzS1 : Ensembles.In _ S1 z,
                  HzB : Ensembles.In _ ((S \\ [set x]) \\ S1 \\ FromList xs_done) z |- _ ] =>
                  inversion HzB; subst; clear HzB;
                  match goal with
                  | [ HzS1' : Ensembles.In _ ((S \\ [set x]) \\ S1) z |- _ ] =>
                      inversion HzS1'; subst; clear HzS1';
                      match goal with
                      | [ HnotS1 : ~ Ensembles.In _ S1 z |- _ ] =>
                          exact (HnotS1 HzS1)
                      end
                  end
              end.
            - constructor. intros z Hc.
              inversion Hc; subst; clear Hc.
              match goal with
              | [ HzS2 : Ensembles.In _ S2 z,
                  HzB : Ensembles.In _ ((S \\ [set x]) \\ S1 \\ FromList xs_done) z |- _ ] =>
                  inversion HzB; subst; clear HzB;
                  match goal with
                  | [ HzS1' : Ensembles.In _ ((S \\ [set x]) \\ S1) z |- _ ] =>
                      inversion HzS1'; subst; clear HzS1';
                      match goal with
                      | [ HnotS1 : ~ Ensembles.In _ S1 z |- _ ] =>
                          exact (HnotS1 (Hsub_e1 _ HzS2))
                      end
                  end
              end.
            - eapply Disjoint_Included_r; [eapply Setminus_Included|].
              eapply Disjoint_Included_r.
              + eapply Setminus_Included.
              + exact Hdis_cmap_x.
            - constructor. intros z Hc.
              inversion Hc; subst; clear Hc.
              match goal with
              | [ Hzxs : Ensembles.In _ (FromList xs_done) z,
                  HzB : Ensembles.In _ ((S \\ [set x]) \\ S1 \\ FromList xs_done) z |- _ ] =>
                  inversion HzB; subst; clear HzB;
                  match goal with
                  | [ Hnotxs : ~ Ensembles.In _ (FromList xs_done) z |- _ ] =>
                      exact (Hnotxs Hzxs)
                  end
              end.
            - constructor. intros z Hc.
              inversion Hc as [z0 Hzx1 HzB]; subst.
              inversion Hzx1; subst; clear Hzx1.
              destruct Hx1_loc as [Hx1_vn | [Hx1_S1 | Hx1_cm]].
              + eapply Hdis_x. constructor; [exact Hx1_vn |].
                eapply Setminus_Included. eapply Setminus_Included.
                exact HzB.
              + inversion HzB; subst; clear HzB.
                match goal with
                | [ HzS1' : Ensembles.In _ ((S \\ [set x]) \\ S1) ?y |- _ ] =>
                    inversion HzS1'; subst; clear HzS1';
                    match goal with
                    | [ HnotS1 : ~ Ensembles.In _ S1 ?y |- _ ] =>
                        exact (HnotS1 Hx1_S1)
                    end
                end.
              + eapply Hdis_cmap_x. constructor; [exact Hx1_cm |].
                eapply Setminus_Included. eapply Setminus_Included.
                exact HzB.
            - eapply Disjoint_Included_r; [exact HB_done_sub | exact Hdis_ek]. }
          destruct Hns_e1 as [[src_v [fv [tv Hval1]]] | Hdiv_e1].
          * pose proof (src_eval_val_gt_oot rho0 e1 src_v fv tv Hval1 f1 t0 H1)
              as Hlt_oot.
            destruct (Nat.eq_dec fv (Datatypes.S f1)) as [Hfv | Hneq_fv].
            -- subst fv.
               assert (Hwf_src_v : well_formed_val Σ src_v).
               { eapply eval_preserves_wf;
                   [exact Hglob_wf | exact Hwf | | exact Hval1].
                 pose proof Henv as Henv_len.
                 unfold anf_env_rel' in Henv_len.
                 apply Forall2_length in Henv_len.
                 rewrite Henv_len.
                 exact Hwfe1. }
               destruct (val_rel_exists src_v Hwf_src_v) as [src_v' Hrel_v].
               destruct (anf_cvt_correct_val_cont_oot
                           rho0 e1 src_v (Datatypes.S f1) tv
                           (set_many xs_done vs_done' rho) vn C1 x1 S1 S2 0
                           e_k_inner src_v' 0
                           (le_n _)
                           Hwf
                           Hwfe1
                           Hcons
                           Hcmap
                           Hdis_S1
                           Hdis_cmap_S1
                           Henv_done
                           Hglob_e1
                           Hcvt_e1
                           Hdis_ek_inner
                           Hval1
                           Hrel_v
                           (bstep_fuel_zero_OOT cenv
                              (M.set x1 src_v' (set_many xs_done vs_done' rho))
                              e_k_inner))
                 as [c1' [Hlb1 Hoot1']].
               destruct (anf_cvt_correct_exps_oot
                           rho0 args_done vs0 fs ts rho vn C_done xs_done
                           (S \\ [set x]) S1 e_k_done vs_done' c1'
                           H0 Hwf Hwf_done Hcons Hcmap Hdis_x Hdis_cmap_x
                           Henv Hglob_done Hcvt_done Hrel_done_vals
                           Hdis_ek_done Hoot1')
                 as [c0 [Hlb0 Hoot0]].
	               exists c0. split.
	               { cbv [one_i fuel_resource_LambdaBox fuel_exp] in H3.
	                 simpl in H3, Hlb0, Hlb1 |- *. lia. }
	               unfold e_k_done, e_k_inner in Hoot0.
	               rewrite Hxs_args.
	               cbn.
	               exact Hoot0.
            -- assert (Datatypes.S f1 < fv) as Hlt_succ by lia.
               destruct (src_eval_lt_OOT rho0 e1 src_v fv tv (Datatypes.S f1) Hval1 Hlt_succ)
                 as [t1' Hoot1'].
	            pose proof (IH (Datatypes.S f1, e1) Hlt_e1 rho0 t1' Hoot1')
	              as IHe1.
	            unfold anf_cvt_correct_oot_lower_bound_goal in IHe1.
	            assert (Hns_e1' : src_not_stuck rho0 e1).
	            { left. eexists. eexists. eexists. exact Hval1. }
	            destruct (IHe1 (set_many xs_done vs_done' rho) vn C1 x1 S1 S2
	                           Hwf
	                           Hwfe1
	                              Hcons
                              Hcmap
                              Hdis_S1
                              Hdis_cmap_S1
                              Henv_done
	                              Hglob_e1
	                              Hcvt_e1
	                              e_k_inner
	                              Hdis_ek_inner
	                              (or_introl
	                                 (ex_intro _ src_v
	                                    (ex_intro _ fv
	                                       (ex_intro _ tv Hval1)))))
	                 as [c1' [Hlb1 Hoot1'']].
               destruct (anf_cvt_correct_exps_oot
                           rho0 args_done vs0 fs ts rho vn C_done xs_done
                           (S \\ [set x]) S1 e_k_done vs_done' c1'
                           H0 Hwf Hwf_done Hcons Hcmap Hdis_x Hdis_cmap_x
                           Henv Hglob_done Hcvt_done Hrel_done_vals
                           Hdis_ek_done Hoot1'')
                 as [c0 [Hlb0 Hoot0]].
	               exists c0. split.
	               { cbv [one_i fuel_resource_LambdaBox fuel_exp] in H3.
	                 simpl in H3, Hlb0, Hlb1 |- *. lia. }
	               unfold e_k_done, e_k_inner in Hoot0.
	               rewrite Hxs_args.
	               cbn.
	               exact Hoot0.
          * destruct (Hdiv_e1 (Datatypes.S f1)) as [t1' Hoot1'].
            pose proof (IH (Datatypes.S f1, e1) Hlt_e1 rho0 t1' Hoot1')
              as IHe1.
	            unfold anf_cvt_correct_oot_lower_bound_goal in IHe1.
	            assert (Hns_e1' : src_not_stuck rho0 e1).
	            { right. exact Hdiv_e1. }
		            destruct (IHe1 (set_many xs_done vs_done' rho) vn C1 x1 S1 S2
	                           Hwf
	                           Hwfe1
	                           Hcons
                           Hcmap
                           Hdis_S1
                           Hdis_cmap_S1
                           Henv_done
	                           Hglob_e1
	                           Hcvt_e1
	                           e_k_inner
	                           Hdis_ek_inner
	                           Hns_e1')
	              as [c1' [Hlb1 Hoot1'']].
            destruct (anf_cvt_correct_exps_oot
                        rho0 args_done vs0 fs ts rho vn C_done xs_done
                        (S \\ [set x]) S1 e_k_done vs_done' c1'
                        H0 Hwf Hwf_done Hcons Hcmap Hdis_x Hdis_cmap_x
                        Henv Hglob_done Hcvt_done Hrel_done_vals
                        Hdis_ek_done Hoot1'')
              as [c0 [Hlb0 Hoot0]].
	            exists c0. split.
	            { cbv [one_i fuel_resource_LambdaBox fuel_exp] in H3.
	              simpl in H3, Hlb0, Hlb1 |- *. lia. }
	            unfold e_k_done, e_k_inner in Hoot0.
	            rewrite Hxs_args.
	            cbn.
	            exact Hoot0.
        + (* eval_Case_step *)
          rewrite <- Heqe_cur in Hrel, Hwfe, Hglob, Hdiv, H3 |- *.
          subst r.
          inv Hrel.
          match goal with
          | [ Hf : Ensembles.In _ S ?fcase,
              Hy : Ensembles.In _ (S \\ [set ?fcase]) ?ycase,
              Hm : anf_cvt_rel _ _ _ _ (S \\ [set ?fcase] \\ [set ?ycase]) mch vnames ?S2 ?C1 ?x1,
              Hb : anf_cvt_rel_branches _ _ _ _ ?S2 ind brs 0 vnames ?ycase ?S3 ?pats,
              Hx : Ensembles.In _ ?S3 x |- _ ] =>
              rename Hf into Hfcase_in_S;
              rename Hy into Hy_in_S;
              rename Hm into Hcvt_mch;
              rename Hb into Hcvt_brs;
              rename Hx into Hx_in_S3
          end.
          rewrite Efun1_c_comp_simpl. simpl (Eletapp_c _ _ _ _ _ |[ _ ]|).
          assert (Hwfe_mch : wellformed Σ (Datatypes.length vnames) mch = true).
          { simpl in Hwfe.
            apply Bool.andb_true_iff in Hwfe as [_ Hwfe_rest].
            apply Bool.andb_true_iff in Hwfe_rest as [Hwfe_lhs _].
            apply Bool.andb_true_iff in Hwfe_lhs as [_ Hwfe_m].
            exact Hwfe_m. }
          assert (Hlen_env : Datatypes.length rho0 = Datatypes.length vnames).
          { exact (@anf_env_rel_length func_tag default_tag tgm cmap Σ box_dc box_tag
                                       _ _ _ Henv). }
          assert (Hwf_con : well_formed_val Σ (fuel_sem.Con_v (dcon_of_con ind c) vs0)).
          { eapply eval_preserves_wf; [exact Hglob_wf | exact Hwf | | exact H].
            rewrite Hlen_env. exact Hwfe_mch. }
          destruct (val_rel_exists (fuel_sem.Con_v (dcon_of_con ind c) vs0) Hwf_con)
            as [v_con Hcon_rel_saved].
          remember (fuel_sem.Con_v (dcon_of_con ind c) vs0) as cv in Hcon_rel_saved.
          destruct Hcon_rel_saved; try discriminate.
          injection Heqcv as Heq_dc Heq_vs. subst.
          match goal with
          | [ HF : Forall2 _ vs0 ?vs_tgt |- _ ] =>
              rename HF into HF2_vs;
              set (vs_anf := vs_tgt) in *
          end.
          set (c_tag := dcon_to_tag default_tag (dcon_of_con ind c) tgm) in *.
          assert (Hcon_rel : anf_val_rel' (fuel_sem.Con_v (dcon_of_con ind c) vs0)
                                        (Vconstr c_tag vs_anf)).
          { constructor; [exact HF2_vs | reflexivity]. }
          edestruct (@anf_cvt_rel_branches_find_branch
                       func_tag default_tag tgm cmap Σ dcon_to_tag_inj box_dc box_tag
                       S2 ind brs 0%N vnames y S3 pats c (Datatypes.length vs0) body
                       Hcvt_brs H1)
            as (br_vars & S_br & S_br_out & C_br & r_br & ctx_br & m_br &
                Hbr_sub & Hbr_len & Hbr_nd & Hctx_br_eq &
                Hfind_tag & Hcvt_body & HS_br_sub).
          simpl in Hfind_tag, Hcvt_body, Hctx_br_eq.
          replace (c + 0) with c in Hfind_tag by lia.
          replace (c + 0) with c in Hctx_br_eq by lia.
          set (f_fun := f3).
          set (defs := Fcons f_fun func_tag [y] (Ecase y pats) Fnil).
          set (rho_efun := def_funs defs defs rho rho).
          set (rho_match := M.set y (Vconstr c_tag vs_anf) (def_funs defs defs rho rho)).
          assert (Hdis_prefix : Disjoint _ (FromList vnames) (S \\ [set f_fun] \\ [set y])).
          { eapply Disjoint_Included_r; [| exact Hdis].
            eapply Included_trans; apply Setminus_Included. }
          assert (Hdis_cmap_prefix : Disjoint _ (cmap_vars cmap) (S \\ [set f_fun] \\ [set y])).
          { eapply Disjoint_Included_r; [| exact Hdis_cmap].
            eapply Included_trans; apply Setminus_Included. }
          assert (Hdis_eletapp : Disjoint var
            (occurs_free (Eletapp x f_fun func_tag [x1] e_k))
            (S \\ [set f_fun] \\ [set y] \\ S2 \\ [set x1])).
          { constructor. intros z Hz.
            inversion Hz as [z' Hfree Hsm]; subst; clear Hz.
            destruct Hsm as [[[[Hz_S Hz_nffun] Hz_ny] Hz_nS2] Hz_nx1].
            apply (proj1 (occurs_free_Eletapp _ _ _ _ _)) in Hfree.
            inversion Hfree as [z0 Hhead | z0 Htail]; subst.
            - inversion Hhead as [z1 Hfun | z1 Hargs]; subst.
              + exact (Hz_nffun Hfun).
              + unfold FromList, Ensembles.In in Hargs. simpl in Hargs.
                destruct Hargs as [<- | []]. apply Hz_nx1. constructor.
            - destruct Htail as [Hz_ek Hz_neq_x].
              destruct Hdis_ek as [Hdis_ek'].
              eapply (Hdis_ek' z).
              constructor; [exact Hz_ek |].
              constructor.
              + constructor; [exact Hz_S |].
                intros [Hc _]. apply Hz_nS2.
                eapply anf_cvt_branches_subset; [exact Hcvt_brs | exact Hc].
              + exact Hz_neq_x. }
          assert (Henv_efun : anf_env_rel' vnames rho0 rho_efun).
          { unfold rho_efun, defs. simpl.
            apply anf_env_rel_weaken; [exact Henv |].
            intros Hc. inv Hdis. eapply H0.
            constructor; [exact Hc | exact Hfcase_in_S]. }
          assert (Hglob_mch : global_env_rel' (kn_deps mch) rho_efun).
          { unfold rho_efun, defs. simpl.
            eapply global_env_rel_set_fresh.
            - eapply global_env_rel_mono; [exact Hglob |].
              intros k0 Hk0. unfold kn_deps in *. simpl.
              apply KernameSet.union_spec. right.
              assert (Hfold : forall base (l : list (list name * term)),
                KernameSet.In k0 base ->
                KernameSet.In k0
                  (fold_left (fun acc x => KernameSet.union (term_global_deps (snd x)) acc) l base)).
              { intros base l. revert base. induction l as [| [? ?] l' IH'];
                  intros base Hin; simpl; [exact Hin |].
                apply IH'. apply KernameSet.union_spec. right. exact Hin. }
              exact (Hfold _ _ Hk0).
            - intros Hc. inv Hdis_cmap. eapply H0.
              constructor; [exact Hc | exact Hfcase_in_S]. }
          assert (Hwf_body_env : well_formed_env Σ (rev vs0 ++ rho0)).
          { unfold well_formed_env. apply Forall_forall.
            intros v0 Hv0. apply in_app_or in Hv0.
            destruct Hv0 as [Hv0 | Hv0].
            - apply in_rev in Hv0. inv Hwf_con.
              match goal with
              | [ HF : Forall _ vs0 |- _ ] =>
                  rewrite Forall_forall in HF; exact (HF _ Hv0)
              end.
            - unfold well_formed_env in Hwf.
              rewrite Forall_forall in Hwf. exact (Hwf _ Hv0). }
          assert (Hwf_body : wellformed Σ (Datatypes.length (br_vars ++ vnames)) body = true).
          { rewrite length_app.
            replace (Datatypes.length br_vars + Datatypes.length vnames)
              with (Datatypes.length vnames + Datatypes.length vs0)
              by (rewrite Hbr_len; lia).
            eapply (@anf_correct.find_branch_wellformed
                      default_tag tgm efl box_dc box_tag
                      Σ (Datatypes.length vnames) ind npars mch brs
                      c (Datatypes.length vs0) body);
              [exact Hwfe | exact H1]. }
          assert (Hcons_body : env_consistent (br_vars ++ vnames) (rev vs0 ++ rho0)).
          { eapply (@env_consistent_app
                      func_tag default_tag tgm cmap Σ box_dc box_tag
                      br_vars vnames (rev vs0) rho0).
            - exact Hbr_nd.
            - exact Hcons.
            - eapply Disjoint_Included_l; [| eapply Disjoint_sym; exact Hdis].
              eapply Included_trans; [exact Hbr_sub |].
              eapply Included_trans; [exact HS_br_sub |].
              eapply Included_trans;
                [eapply anf_cvt_exp_subset; exact Hcvt_mch |].
              eapply Included_trans; apply Setminus_Included.
            - rewrite Hbr_len. rewrite length_rev. reflexivity. }
          assert (Hcmap_body : cmap_consistent' (br_vars ++ vnames) (rev vs0 ++ rho0)).
          { eapply (@cmap_consistent_app
                      func_tag default_tag tgm cmap Σ box_dc box_tag
                      br_vars vnames (rev vs0) rho0).
            - exact Hcmap.
            - eapply Disjoint_Included_r; [| exact Hdis_cmap].
              eapply Included_trans; [exact Hbr_sub |].
              eapply Included_trans; [exact HS_br_sub |].
              eapply Included_trans;
                [eapply anf_cvt_exp_subset; exact Hcvt_mch |].
              eapply Included_trans; apply Setminus_Included.
            - rewrite Hbr_len. rewrite length_rev. reflexivity. }
          assert (Hdis_body : Disjoint _ (FromList (br_vars ++ vnames)) (S_br \\ FromList br_vars)).
          { rewrite FromList_app. eapply Union_Disjoint_l.
            - eapply Disjoint_Setminus_r. eapply Included_refl.
            - eapply Disjoint_Included_r; [| exact Hdis].
              eapply Included_trans; [apply Setminus_Included |].
              eapply Included_trans; [exact HS_br_sub |].
              eapply Included_trans;
                [eapply anf_cvt_exp_subset; exact Hcvt_mch |].
              eapply Included_trans; apply Setminus_Included. }
          assert (Hdis_cmap_body : Disjoint _ (cmap_vars cmap) (S_br \\ FromList br_vars)).
          { eapply Disjoint_Included_r; [| exact Hdis_cmap].
            eapply Included_trans; [apply Setminus_Included |].
            eapply Included_trans; [exact HS_br_sub |].
            eapply Included_trans;
              [eapply anf_cvt_exp_subset; exact Hcvt_mch |].
            eapply Included_trans; apply Setminus_Included. }
          assert (Hset_proj : exists rho_proj,
            set_lists (rev br_vars) vs_anf rho_match = Some rho_proj).
          { apply (set_lists_length3 rho_match).
            rewrite length_rev, Hbr_len.
            exact (Forall2_length HF2_vs). }
          destruct Hset_proj as [rho_proj Hset_proj].
          assert (Henv_body : anf_env_rel' (br_vars ++ vnames) (rev vs0 ++ rho0) rho_proj).
          { eapply anf_env_rel_extend_setlists_rev.
            - unfold rho_match, defs. simpl.
              apply anf_env_rel_weaken.
              2:{ intros Hc.
                  destruct Hdis as [Hdis_vn_S].
                  eapply Hdis_vn_S. constructor; [exact Hc |].
                  destruct Hy_in_S as [Hy_S _]. exact Hy_S. }
              apply anf_env_rel_weaken; [exact Henv |].
              intros Hc.
              destruct Hdis as [Hdis_vn_S].
              eapply Hdis_vn_S. constructor; [exact Hc | exact Hfcase_in_S].
            - exact Hset_proj.
            - exact HF2_vs.
            - eapply Disjoint_Included_l; [| eapply Disjoint_sym; exact Hdis].
              eapply Included_trans; [exact Hbr_sub |].
              eapply Included_trans; [exact HS_br_sub |].
              eapply Included_trans;
                [eapply anf_cvt_exp_subset; exact Hcvt_mch |].
              eapply Included_trans; apply Setminus_Included.
            - exact Hbr_nd. }
          assert (Hglob_body : global_env_rel' (kn_deps body) rho_proj).
          { eapply global_env_rel_weaken_setlists.
            - eapply global_env_rel_set_fresh.
              + eapply global_env_rel_set_fresh.
                * eapply global_env_rel_mono; [exact Hglob |].
                  intros k0 Hk0. unfold kn_deps in *. simpl.
                  apply KernameSet.union_spec. right.
                  assert (Hfold_in : forall (l : list (list name * term)) body0' base,
                    In body0' (map snd l) ->
                    KernameSet.In k0 (term_global_deps body0') ->
                    KernameSet.In k0 (fold_left (fun acc x =>
                      KernameSet.union (term_global_deps (snd x)) acc) l base)).
                  { intros l. induction l as [| [? ?] l' IH']; intros b' base Hin Hdep.
                    - destruct Hin.
                    - simpl in Hin. destruct Hin as [<- | Hin].
                      + simpl.
                        assert (Hbase : forall (ll : list (list name * term)) acc,
                          KernameSet.In k0 acc ->
                          KernameSet.In k0 (fold_left (fun a x => KernameSet.union (term_global_deps (snd x)) a) ll acc)).
                        { intros ll. induction ll as [| [? ?] ll' IHll]; intros acc Hacc;
                            simpl; [exact Hacc | apply IHll; apply KernameSet.union_spec; right; exact Hacc]. }
                        apply Hbase. apply KernameSet.union_spec. left. exact Hdep.
                      + simpl. exact (IH' _ _ Hin Hdep). }
                  eapply Hfold_in; [| exact Hk0].
                  exact (find_branch_In _ _ _ _ _ H1).
                * intros Hc.
                  destruct Hdis_cmap as [Hdis_cmap_S].
                  eapply Hdis_cmap_S. constructor; [exact Hc | exact Hfcase_in_S].
              + intros Hc.
                destruct Hdis_cmap as [Hdis_cmap_S].
                eapply Hdis_cmap_S. constructor; [exact Hc |].
                destruct Hy_in_S as [Hy_S _]. exact Hy_S.
            - exact Hset_proj.
            - eapply Disjoint_Included_l; [| eapply Disjoint_sym; exact Hdis_cmap].
              rewrite FromList_rev.
              eapply Included_trans; [exact Hbr_sub |].
              eapply Included_trans; [exact HS_br_sub |].
              eapply Included_trans;
                [eapply anf_cvt_exp_subset; exact Hcvt_mch |].
              eapply Included_trans; apply Setminus_Included. }
          assert (Hdis_ehalt :
            Disjoint _ (occurs_free (Ehalt r_br)) ((S_br \\ FromList br_vars) \\ [set r_br])).
          { eapply Disjoint_Included_l; [| eapply Disjoint_Singleton_l].
            - intros z Hz. remember (Ehalt r_br) as eh.
              destruct Hz; try discriminate.
              injection Heqeh as ->. constructor.
            - intro Habs. destruct Habs as [_ Hc]. apply Hc. constructor. }
          assert (Hns_body : src_not_stuck (rev vs0 ++ rho0) body).
          { eapply src_not_stuck_case_body
                      with (rho := rho0) (ind := ind) (npars := npars)
                           (mch := mch) (brs := brs)
                           (dc := dcon_of_con ind c) (vs := vs0)
                           (body := body) (c := c)
                           (f1 := f1) (t1 := t1).
            - exact H.
            - reflexivity.
            - exact H1.
            - right. exact Hdiv. }
          assert (Hlt_body : div_lt (f2, body) (f0, e0)).
          { unfold div_lt, div_measure.
            apply Relation_Operators.left_lex.
            assert (Hlt_f : f2 < f0).
            { cbv [one_i fuel_resource_LambdaBox fuel_exp] in H3.
              simpl in H3. lia. }
            exact Hlt_f. }
          assert (Hdis_ehalt_body :
            Disjoint _ (occurs_free (Ehalt r_br))
              ((S_br \\ FromList br_vars) \\ S_br_out \\ [set r_br])).
          { eapply Disjoint_Included_l; [| eapply Disjoint_Singleton_l].
            - intros z Hz. remember (Ehalt r_br) as eh.
              destruct Hz; try discriminate.
              injection Heqeh as ->. constructor.
            - intro Habs. destruct Habs as [_ Hc]. apply Hc. constructor. }
          pose proof (IH (f2, body) Hlt_body (rev vs0 ++ rho0) t2 H2) as IHbody.
          unfold anf_cvt_correct_oot_lower_bound_goal in IHbody.
          destruct (IHbody rho_proj (br_vars ++ vnames) C_br r_br
                           (S_br \\ FromList br_vars) S_br_out
                           Hwf_body_env
                           Hwf_body
                           Hcons_body
                           Hcmap_body
                           Hdis_body
                           Hdis_cmap_body
                           Henv_body
                           Hglob_body
                           Hcvt_body
                           (Ehalt r_br)
                           Hdis_ehalt_body
                           Hns_body)
            as [c3 [Hlb3 Hoot3]].
          assert (Hpre_ctx : preord_exp cenv
                     (eq_fuel_n (Datatypes.length br_vars)) eq_fuel c3
                     (C_br |[ Ehalt r_br ]|, rho_proj)
                     (ctx_br |[ C_br |[ Ehalt r_br ]| ]|, rho_match)).
          { subst ctx_br.
            eapply (@anf_correct.ctx_bind_proj_preord_exp
                      func_tag default_tag tgm cmap cenv Σ box_dc box_tag
                      br_vars
                      (ctx_bind_proj c_tag y br_vars (Datatypes.length br_vars))
                      c3 y (Datatypes.length br_vars)
                      (C_br |[ Ehalt r_br ]|) rho_match rho_proj vs_anf [] c_tag).
            - reflexivity.
            - intros Hy_in_bv.
              assert (Hy_in_S2 : y \in S2).
              { eapply HS_br_sub. eapply Hbr_sub. exact Hy_in_bv. }
              assert (Hy_in_Sfy :=
                anf_cvt_exp_subset func_tag default_tag tgm cmap
                  _ _ _ _ _ _ Hcvt_mch _ Hy_in_S2).
              destruct Hy_in_Sfy as [Hy_Sf Hy_ny].
              destruct Hy_Sf as [_ Hy_nffun].
              apply Hy_ny. constructor.
            - reflexivity.
            - unfold rho_match. rewrite M.gss. rewrite app_nil_r. reflexivity.
            - exact Hset_proj. }
          destruct (Hpre_ctx eval.OOT c3 tt (le_n _) Hoot3)
            as [r_ctx [c_ctx [cout_ctx [Hbstep_ctx [Hpost_ctx Hres_ctx]]]]].
          destruct r_ctx as [| v_ctx]; [| simpl in Hres_ctx; contradiction].
          destruct cout_ctx.
          assert (Hpre_case : preord_exp cenv one_step eq_fuel c_ctx
                     (ctx_br |[ C_br |[ Ehalt r_br ]| ]|, rho_match)
                     (Ecase y pats, rho_match)).
          { eapply (@preord_exp_Ecase_red
                      func_tag default_tag tgm cmap cenv Σ box_dc box_tag
                      cenv_case_consistent c_ctx rho_match c_tag vs_anf pats
                      (ctx_br |[ C_br |[ Ehalt r_br ]| ]|) m_br y).
            - unfold rho_match. rewrite M.gss. reflexivity.
            - exact Hfind_tag. }
          destruct (Hpre_case eval.OOT c_ctx tt (le_n _) Hbstep_ctx)
            as [r_case [c_case [cout_case [Hbstep_case [Hpost_case Hres_case]]]]].
          destruct r_case as [| v_case]; [| simpl in Hres_case; contradiction].
          destruct cout_case.
          assert (Hneq_f_fun_x1 : f_fun <> x1).
          { intro Heq. subst x1.
            destruct (@anf_cvt_result_in_consumed
                        func_tag default_tag tgm cmap
                        (S \\ [set f_fun] \\ [set y]) mch vnames S2 C1 f_fun
                        Hcvt_mch) as [Hc | [Hc | Hc]].
            - destruct Hdis as [Hdis_vn_S].
              eapply Hdis_vn_S. constructor; [exact Hc | exact Hfcase_in_S].
            - destruct Hc as [[_ Hnot_f_fun] _].
              apply Hnot_f_fun. constructor.
            - destruct Hdis_cmap as [Hdis_cmap_S].
              eapply Hdis_cmap_S. constructor; [exact Hc | exact Hfcase_in_S]. }
          assert (Hget_f_fun :
            M.get f_fun (M.set x1 (Vconstr c_tag vs_anf) rho_efun) = Some (Vfun rho defs f_fun)).
          { unfold rho_efun, defs. simpl.
            rewrite M.gso; [| exact Hneq_f_fun_x1].
            rewrite M.gss. reflexivity. }
          assert (Hget_x1 : get_list [x1] (M.set x1 (Vconstr c_tag vs_anf) rho_efun) = Some [Vconstr c_tag vs_anf]).
          { simpl. rewrite M.gss. reflexivity. }
          assert (Hfind_f_fun : find_def f_fun defs = Some (func_tag, [y], Ecase y pats)).
          { unfold defs, f_fun. simpl. destruct (M.elt_eq f3 f3); [reflexivity | contradiction]. }
          assert (Hset_body : set_lists [y] [Vconstr c_tag vs_anf] (def_funs defs defs rho rho) = Some rho_match).
          { unfold rho_match, defs. simpl. reflexivity. }
          assert (Hoot_letapp :
            bstep_fuel cenv (M.set x1 (Vconstr c_tag vs_anf) rho_efun)
                       (Eletapp x f_fun func_tag [x1] e_k)
                       (Datatypes.S c_case) eval.OOT tt).
          { pose proof
              (BStepf_run cenv
                 (M.set x1 (Vconstr c_tag vs_anf) rho_efun)
                 (Eletapp x f_fun func_tag [x1] e_k) eval.OOT c_case tt
                 (BStept_letapp_oot cenv rho defs f_fun [Vconstr c_tag vs_anf] [y]
                    (Ecase y pats) e_k rho_match
                    (M.set x1 (Vconstr c_tag vs_anf) rho_efun)
                    x f_fun func_tag [x1]
                    c_case tt Hget_f_fun Hget_x1 Hfind_f_fun Hset_body Hbstep_case))
              as Hbsf.
            unfold one, one_i in Hbsf. simpl in Hbsf.
            replace (c_case + 1)%nat with (Datatypes.S c_case) in Hbsf by lia.
            exact Hbsf. }
          destruct (anf_cvt_correct_val_cont_oot
                      rho0 mch (fuel_sem.Con_v (dcon_of_con ind c) vs0) f1 t1
                      rho_efun vnames C1 x1
                      (S \\ [set f_fun] \\ [set y]) S2
                      (Datatypes.S c_case)
                      (Eletapp x f_fun func_tag [x1] e_k)
                      (Vconstr c_tag vs_anf) (Datatypes.S c_case)
                      (le_n _)
                      Hwf
                      Hwfe_mch
                      Hcons
                      Hcmap
                      Hdis_prefix
                      Hdis_cmap_prefix
                      Henv_efun
                      Hglob_mch
                      Hcvt_mch
                      Hdis_eletapp
                      H
                      Hcon_rel
                      Hoot_letapp)
            as [c_mid [Hlb_mid Hoot_mid]].
          assert (Hoot_fun :
            bstep_fuel cenv rho (Efun defs (C1 |[ Eletapp x f_fun func_tag [x1] e_k ]|))
                       (Datatypes.S c_mid) eval.OOT tt).
          { pose proof
              (BStepf_run cenv rho
                 (Efun defs (C1 |[ Eletapp x f_fun func_tag [x1] e_k ]|))
                 eval.OOT c_mid tt
                 (BStept_fun cenv rho defs
                    (C1 |[ Eletapp x f_fun func_tag [x1] e_k ]|) eval.OOT c_mid tt
                    Hoot_mid))
              as Hbsf.
            unfold one, one_i in Hbsf. simpl in Hbsf.
            replace (c_mid + 1)%nat with (Datatypes.S c_mid) in Hbsf by lia.
            exact Hbsf. }
          exists (Datatypes.S c_mid). split.
          { unfold eq_fuel_n in Hpost_ctx.
            unfold one_step, eq_fuel in Hpost_case.
            simpl in Hpost_ctx, Hpost_case.
            cbv [one_i fuel_resource_LambdaBox fuel_exp] in H3.
            simpl in H3, Hlb3, Hlb_mid |- *.
            subst c_ctx c_case. lia. }
          exact Hoot_fun.
        + (* eval_Case_step_OOT *)
          rewrite <- Heqe_cur in Hrel, Hwfe, Hglob, Hdiv, H3 |- *.
          inv Hrel.
          rewrite Efun1_c_comp_simpl. simpl (Eletapp_c _ _ _ _ _ |[ _ ]|).
          assert (Hwfe_mch : wellformed Σ (Datatypes.length vnames) mch = true).
          { simpl in Hwfe.
            apply Bool.andb_true_iff in Hwfe as [_ Hwfe_rest].
            apply Bool.andb_true_iff in Hwfe_rest as [Hwfe_lhs _].
            apply Bool.andb_true_iff in Hwfe_lhs as [_ Hwfe_m].
            exact Hwfe_m. }
          set (defs := Fcons f2 func_tag [y] (Ecase y pats) Fnil).
          set (rho_efun := def_funs defs defs rho rho).
          assert (Hdis_prefix : Disjoint _ (FromList vnames) (S \\ [set f2] \\ [set y])).
          { eapply Disjoint_Included_r; [| exact Hdis].
            eapply Included_trans; apply Setminus_Included. }
          assert (Hdis_cmap_prefix : Disjoint _ (cmap_vars cmap) (S \\ [set f2] \\ [set y])).
          { eapply Disjoint_Included_r; [| exact Hdis_cmap].
            eapply Included_trans; apply Setminus_Included. }
          assert (Hdis_eletapp : Disjoint var
            (occurs_free (Eletapp x f2 func_tag [x1] e_k))
            (S \\ [set f2] \\ [set y] \\ S2 \\ [set x1])).
          { constructor. intros z Hz. inversion Hz; subst; clear Hz.
            destruct H1 as [[[[Hz_S Hz_nf2] Hz_ny] Hz_nS2] Hz_nx1].
            apply (proj1 (occurs_free_Eletapp _ _ _ _ _)) in H0.
            inv H0.
            - inv H1.
              + exact (Hz_nf2 H0).
              + unfold FromList, Ensembles.In in H0. simpl in H0.
                destruct H0 as [<- | []]. apply Hz_nx1. constructor.
            - destruct H1 as [Hz_ek Hz_neq_x].
              inv Hdis_ek. eapply H0.
              constructor; [exact Hz_ek |].
              constructor.
              + constructor; [exact Hz_S |].
                intros [Hc _]. apply Hz_nS2.
                eapply anf_cvt_branches_subset; [exact H13 | exact Hc].
              + exact Hz_neq_x. }
          assert (Henv_efun : anf_env_rel' vnames rho0 rho_efun).
          { unfold rho_efun, defs. simpl.
            apply anf_env_rel_weaken; [exact Henv |].
            intros Hc. inv Hdis. eapply H0.
            constructor; [exact Hc | exact H5]. }
          assert (Hglob_mch : global_env_rel' (kn_deps mch) rho_efun).
          { unfold rho_efun, defs. simpl.
            eapply global_env_rel_set_fresh.
            - eapply global_env_rel_mono; [exact Hglob |].
              intros k0 Hk0. unfold kn_deps in *. simpl.
              apply KernameSet.union_spec. right.
              assert (Hfold : forall base (l : list (list name * term)),
                KernameSet.In k0 base ->
                KernameSet.In k0
                  (fold_left (fun acc x => KernameSet.union (term_global_deps (snd x)) acc) l base)).
              { intros base l. revert base. induction l as [| [? ?] l' IH'];
                  intros base Hin; simpl; [exact Hin |].
                apply IH'. apply KernameSet.union_spec. right. exact Hin. }
              exact (Hfold _ _ Hk0).
            - intros Hc. inv Hdis_cmap. eapply H0.
              constructor; [exact Hc | exact H5]. }
          assert (Hns_mch : src_not_stuck rho0 mch).
          { eapply src_not_stuck_case_mch
                      with (rho := rho0) (ind := ind) (npars := npars)
                           (mch := mch) (brs := brs).
            right. exact Hdiv. }
          assert (Hlt_mch : div_lt (Datatypes.S f1, mch) (f0, e0)).
          { unfold div_lt, div_measure.
            replace f0 with (Datatypes.S f1).
            - cbn in Heqe_cur. rewrite <- Heqe_cur.
              apply Relation_Operators.right_lex. simpl. lia.
            - cbv [one_i fuel_resource_LambdaBox fuel_exp] in H3.
              simpl in H3. lia. }
          destruct Hns_mch as [[src_v [fv [tv Hval_mch]]] | Hdiv_mch].
          * pose proof (src_eval_val_gt_oot rho0 mch src_v fv tv Hval_mch f1 t1 H)
              as Hlt_oot.
            destruct (Nat.eq_dec fv (Datatypes.S f1)) as [Hfv | Hneq_fv].
            -- subst fv.
               assert (Hwf_src_v : well_formed_val Σ src_v).
               { eapply eval_preserves_wf;
                   [exact Hglob_wf | exact Hwf | | exact Hval_mch].
                 pose proof Henv as Henv_len.
                 unfold anf_env_rel' in Henv_len.
                 apply Forall2_length in Henv_len.
                 rewrite Henv_len.
                 exact Hwfe_mch. }
               destruct (val_rel_exists src_v Hwf_src_v) as [src_v' Hrel_v].
               destruct (anf_cvt_correct_val_cont_oot
                           rho0 mch src_v (Datatypes.S f1) tv
                           rho_efun vnames C1 x1
                           (S \\ [set f2] \\ [set y]) S2 0
                           (Eletapp x f2 func_tag [x1] e_k)
                           src_v' 0
                           (le_n _)
                           Hwf
                           Hwfe_mch
                           Hcons
                           Hcmap
                           Hdis_prefix
                           Hdis_cmap_prefix
                           Henv_efun
                           Hglob_mch
                           H12
                           Hdis_eletapp
                           Hval_mch
                           Hrel_v
                           (bstep_fuel_zero_OOT cenv
                              (M.set x1 src_v' rho_efun)
                              (Eletapp x f2 func_tag [x1] e_k)))
                 as [c1 [Hlb1 Hoot_mid]].
               assert (Hoot_fun :
                 bstep_fuel cenv rho (Efun defs (C1 |[ Eletapp x f2 func_tag [x1] e_k ]|))
                            (Datatypes.S c1) eval.OOT tt).
               { pose proof
                   (BStepf_run cenv rho
                      (Efun defs (C1 |[ Eletapp x f2 func_tag [x1] e_k ]|))
                      eval.OOT c1 tt
                      (BStept_fun cenv rho defs
                         (C1 |[ Eletapp x f2 func_tag [x1] e_k ]|) eval.OOT c1 tt
                         Hoot_mid))
                   as Hbsf.
                 unfold one, one_i in Hbsf. simpl in Hbsf.
                 replace (c1 + 1)%nat with (Datatypes.S c1) in Hbsf by lia.
                 exact Hbsf. }
               exists (Datatypes.S c1). split.
               { cbv [one_i fuel_resource_LambdaBox fuel_exp] in H3.
                 simpl in H3, Hlb1 |- *. lia. }
               exact Hoot_fun.
            -- assert (Datatypes.S f1 < fv) as Hlt_succ by lia.
               destruct (src_eval_lt_OOT rho0 mch src_v fv tv (Datatypes.S f1) Hval_mch Hlt_succ)
                 as [t1' Hoot_mch'].
               pose proof (IH (Datatypes.S f1, mch) Hlt_mch rho0 t1' Hoot_mch')
                 as IHmch.
               unfold anf_cvt_correct_oot_lower_bound_goal in IHmch.
               destruct (IHmch rho_efun vnames C1 x1
                         (S \\ [set f2] \\ [set y]) S2
                         Hwf
                         Hwfe_mch
                         Hcons
                         Hcmap
                         Hdis_prefix
                         Hdis_cmap_prefix
                         Henv_efun
                         Hglob_mch
                         H12
                         (Eletapp x f2 func_tag [x1] e_k)
                         Hdis_eletapp
                         (or_introl
                            (ex_intro _ src_v
                               (ex_intro _ fv
                                  (ex_intro _ tv Hval_mch)))))
                 as [c1 [Hlb1 Hoot_mid]].
               assert (Hoot_fun :
                 bstep_fuel cenv rho (Efun defs (C1 |[ Eletapp x f2 func_tag [x1] e_k ]|))
                            (Datatypes.S c1) eval.OOT tt).
               { pose proof
                   (BStepf_run cenv rho
                      (Efun defs (C1 |[ Eletapp x f2 func_tag [x1] e_k ]|))
                      eval.OOT c1 tt
                      (BStept_fun cenv rho defs
                         (C1 |[ Eletapp x f2 func_tag [x1] e_k ]|) eval.OOT c1 tt
                         Hoot_mid))
                   as Hbsf.
                 unfold one, one_i in Hbsf. simpl in Hbsf.
                 replace (c1 + 1)%nat with (Datatypes.S c1) in Hbsf by lia.
                 exact Hbsf. }
               exists (Datatypes.S c1). split.
               { cbv [one_i fuel_resource_LambdaBox fuel_exp] in H3.
                 simpl in H3, Hlb1 |- *. lia. }
               exact Hoot_fun.
          * destruct (Hdiv_mch (Datatypes.S f1)) as [t1' Hoot_mch'].
            pose proof (IH (Datatypes.S f1, mch) Hlt_mch rho0 t1' Hoot_mch')
              as IHmch.
            unfold anf_cvt_correct_oot_lower_bound_goal in IHmch.
            assert (Hns_mch' : src_not_stuck rho0 mch).
            { right. exact Hdiv_mch. }
            destruct (IHmch rho_efun vnames C1 x1
                      (S \\ [set f2] \\ [set y]) S2
                      Hwf
                      Hwfe_mch
                      Hcons
                      Hcmap
                      Hdis_prefix
                      Hdis_cmap_prefix
                      Henv_efun
                      Hglob_mch
                      H12
                      (Eletapp x f2 func_tag [x1] e_k)
                      Hdis_eletapp
                      Hns_mch')
              as [c1 [Hlb1 Hoot_mid]].
            assert (Hoot_fun :
              bstep_fuel cenv rho (Efun defs (C1 |[ Eletapp x f2 func_tag [x1] e_k ]|))
                         (Datatypes.S c1) eval.OOT tt).
            { pose proof
                (BStepf_run cenv rho
                   (Efun defs (C1 |[ Eletapp x f2 func_tag [x1] e_k ]|))
                   eval.OOT c1 tt
                   (BStept_fun cenv rho defs
                      (C1 |[ Eletapp x f2 func_tag [x1] e_k ]|) eval.OOT c1 tt
                      Hoot_mid))
                as Hbsf.
              unfold one, one_i in Hbsf. simpl in Hbsf.
              replace (c1 + 1)%nat with (Datatypes.S c1) in Hbsf by lia.
              exact Hbsf. }
            exists (Datatypes.S c1). split.
            { cbv [one_i fuel_resource_LambdaBox fuel_exp] in H3.
              simpl in H3, Hlb1 |- *. lia. }
            exact Hoot_fun.
        + (* eval_Proj_step_OOT *)
          rewrite <- Heqe_cur in Hrel, Hwfe, Hglob, Hdiv, H3 |- *.
          inv Hrel.
          rewrite <- app_ctx_f_fuse.
          assert (Hwfc : wellformed Σ (Datatypes.length vnames) c = true).
          { eapply wellformed_tProj. exact Hwfe. }
          assert (Hglob_c : global_env_rel' (kn_deps c) rho).
          { eapply global_env_rel_mono; [exact Hglob |].
            intros k Hk. unfold kn_deps. simpl.
            apply KernameSet.union_spec. right. exact Hk. }
          assert (Hdis_eproj :
            Disjoint _
                     (occurs_free
                        (Eproj x
                           (dcon_to_tag default_tag (dcon_of_con (proj_ind p) 0) tgm)
                           (N.of_nat (proj_arg p)) x0 e_k))
                     ((S \\ S2) \\ [set x0])).
          { eapply Disjoint_Included_l;
              [eapply (proj1 (occurs_free_Eproj _ _ _ _ _)) |].
            eapply Union_Disjoint_l.
            - constructor. intros z Hz.
              inversion Hz as [? Hs Hset]; subst.
              inv Hs. destruct Hset as [_ Habs]. apply Habs. constructor.
            - constructor. intros z Hz.
              inversion Hz as [? Hset1 Hset2]; subst.
              destruct Hset1 as [Hfree_ek Hneq_x].
              destruct Hset2 as [[HS HnS2] Hneq_x0].
              eapply Hdis_ek. constructor; [exact Hfree_ek |].
              constructor.
              + constructor; [exact HS |].
                intros HinS2x. destruct HinS2x as [HinS2 _].
                exact (HnS2 HinS2).
              + exact Hneq_x. }
          assert (Hns_c : src_not_stuck rho0 c).
          { eapply src_not_stuck_proj_scrut
                      with (rho := rho0) (p := p) (c := c).
            right. exact Hdiv. }
          assert (Hlt_c : div_lt (Datatypes.S f1, c) (f0, e0)).
          { unfold div_lt, div_measure.
            replace f0 with (Datatypes.S f1).
            - cbn in Heqe_cur. rewrite <- Heqe_cur.
              apply Relation_Operators.right_lex. simpl. lia.
            - cbv [one_i fuel_resource_LambdaBox fuel_exp] in H3.
              simpl in H3. lia. }
          destruct Hns_c as [[src_v [fv [tv Hval_c]]] | Hdiv_c].
          * pose proof (src_eval_val_gt_oot rho0 c src_v fv tv Hval_c f1 t1 H)
              as Hlt_oot.
            destruct (Nat.eq_dec fv (Datatypes.S f1)) as [Hfv | Hneq_fv].
            -- subst fv.
               assert (Hwf_src_v : well_formed_val Σ src_v).
               { eapply eval_preserves_wf;
                   [exact Hglob_wf | exact Hwf | | exact Hval_c].
                 pose proof Henv as Henv_len.
                 unfold anf_env_rel' in Henv_len.
                 apply Forall2_length in Henv_len.
                 rewrite Henv_len.
                 exact Hwfc. }
               destruct (val_rel_exists src_v Hwf_src_v) as [src_v' Hrel_v].
               destruct (anf_cvt_correct_val_cont_oot
                           rho0 c src_v (Datatypes.S f1) tv
                           rho vnames C0 x0 S S2 0
                           (Eproj x
                              (dcon_to_tag default_tag (dcon_of_con (proj_ind p) 0) tgm)
                              (N.of_nat (proj_arg p)) x0 e_k)
                           src_v' 0
                           (le_n _)
                           Hwf
                           Hwfc
                           Hcons
                           Hcmap
                           Hdis
                           Hdis_cmap
                           Henv
                           Hglob_c
                           H5
                           Hdis_eproj
                           Hval_c
                           Hrel_v
                           (bstep_fuel_zero_OOT cenv
                              (M.set x0 src_v' rho)
                              (Eproj x
                                 (dcon_to_tag default_tag (dcon_of_con (proj_ind p) 0) tgm)
                                 (N.of_nat (proj_arg p)) x0 e_k)))
                 as [c0 [Hlb Hoot_tgt]].
               exists c0. split.
               { cbv [one_i fuel_resource_LambdaBox fuel_exp] in H3.
                 cbv [one_i fuel_resource_LambdaBox fuel_exp].
                 simpl in Hlb |- *. lia. }
               exact Hoot_tgt.
            -- assert (Datatypes.S f1 < fv) as Hlt_succ by lia.
               destruct (src_eval_lt_OOT rho0 c src_v fv tv (Datatypes.S f1) Hval_c Hlt_succ)
                 as [t1' Hoot_c'].
               pose proof (IH (Datatypes.S f1, c) Hlt_c rho0 t1' Hoot_c') as IHc.
               unfold anf_cvt_correct_oot_lower_bound_goal in IHc.
               destruct (IHc rho vnames C0 x0 S S2
                            Hwf
                            Hwfc
                            Hcons
                            Hcmap
                            Hdis
                            Hdis_cmap
                            Henv
                            Hglob_c
                            H5
                            (Eproj x
                               (dcon_to_tag default_tag (dcon_of_con (proj_ind p) 0) tgm)
                               (N.of_nat (proj_arg p)) x0 e_k)
                            Hdis_eproj
                            (or_introl
                               (ex_intro _ src_v
                                  (ex_intro _ fv
                                     (ex_intro _ tv Hval_c)))))
                 as [c0 [Hlb Hoot_tgt]].
               exists c0. split.
               { cbv [one_i fuel_resource_LambdaBox fuel_exp] in H3.
                 cbv [one_i fuel_resource_LambdaBox fuel_exp].
                 simpl in Hlb |- *. lia. }
               exact Hoot_tgt.
          * destruct (Hdiv_c (Datatypes.S f1)) as [t1' Hoot_c'].
            pose proof (IH (Datatypes.S f1, c) Hlt_c rho0 t1' Hoot_c') as IHc.
            unfold anf_cvt_correct_oot_lower_bound_goal in IHc.
            assert (Hns_c' : src_not_stuck rho0 c).
            { right. exact Hdiv_c. }
            destruct (IHc rho vnames C0 x0 S S2
                          Hwf
                          Hwfc
                          Hcons
                          Hcmap
                          Hdis
                          Hdis_cmap
                          Henv
                          Hglob_c
                          H5
                          (Eproj x
                             (dcon_to_tag default_tag (dcon_of_con (proj_ind p) 0) tgm)
                             (N.of_nat (proj_arg p)) x0 e_k)
                          Hdis_eproj
                          Hns_c')
              as [c0 [Hlb Hoot_tgt]].
            exists c0. split.
            { cbv [one_i fuel_resource_LambdaBox fuel_exp] in H3.
              cbv [one_i fuel_resource_LambdaBox fuel_exp].
              simpl in Hlb |- *. lia. }
            exact Hoot_tgt.
    }
    exact (Hmain (f, e) vs t Hoot_init).
  Qed.

End Divergence.
