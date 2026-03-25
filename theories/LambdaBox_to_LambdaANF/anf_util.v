(* Value relations, alpha-equivalence, and utility lemmas for ANF correctness.
   Adapts LambdaBoxLocal_to_LambdaANF_anf_util.v to the new MetaRocq pipeline. *)

From Stdlib Require Import ZArith.ZArith Lists.List micromega.Lia Arith
     Ensembles Relations.Relation_Definitions.
From MetaRocq.Erasure Require Import EAst.
From MetaRocq.Common Require Import BasicAst Kernames.
From MetaRocq.Utils Require Import bytestring.
From compcert Require Import lib.Maps lib.Coqlib.
From CertiRocq.Common Require Import AstCommon.
From CertiRocq Require Import Pipeline_utils.
From CertiRocq.LambdaANF Require Import
  cps cps_show eval ctx logical_relations
  List_util algebra alpha_conv functions Ensembles_util
  tactics identifiers bounds cps_util rename set_util.
From MetaRocq.Utils Require Import All_Forall.
From CertiRocq.LambdaBox_to_LambdaANF Require Import common ANF fuel_sem anf_corresp.

Import ListNotations.


Section ANF_Val.

  Context (func_tag default_tag : positive)
          (tgm : conId_map)
          (cmap : const_map).

  Let anf_cvt_rel' := anf_cvt_rel func_tag default_tag tgm cmap.

(* ================================================================= *)
(** * Value and Environment Relations                                  *)
(* ================================================================= *)

  Definition anf_env_rel' (P : fuel_sem.value -> val -> Prop)
             (vn : list var) (vs : list fuel_sem.value) (rho : M.t val) :=
    Forall2 (fun v x => exists v', M.get x rho = Some v' /\ P v v') vs vn.

  Inductive anf_fix_rel (fnames : list var) (names : list var)
    : Ensemble var -> list var ->
      list (EAst.def EAst.term) -> fundefs -> Ensemble var -> Prop :=
  | anf_fix_fnil :
      forall S,
        anf_fix_rel fnames names S [] [] Fnil S
  | anf_fix_fcons :
      forall S1 S1' S2 S2' S3 fnames' d mfix' C1 r1 na e1 B f x,
        d.(EAst.dbody) = EAst.tLambda na e1 ->
        Disjoint _ S1 (FromList fnames :|: FromList names) ->
        x \in S1 ->
        S1' \subset S1 \\ [set x] ->
        S2' \subset S2 ->
        anf_cvt_rel' S1' e1 (x :: List.rev fnames ++ names) S2 C1 r1 ->
        anf_fix_rel fnames names S2' fnames' mfix' B S3 ->
        anf_fix_rel fnames names S1 (f :: fnames')
                    (d :: mfix')
                    (Fcons f func_tag [x] (C1 |[ Ehalt r1 ]|) B) S3.

  Definition env_consistent (vn : list var) (rho : list fuel_sem.value) : Prop :=
    forall i j x,
      nth_error vn i = Some x ->
      nth_error vn j = Some x ->
      nth_error rho i = nth_error rho j.

  Inductive anf_val_rel : fuel_sem.value -> val -> Prop :=
  | anf_rel_Con :
      forall vs vs' dc c_tag,
        Forall2 (fun v v' => anf_val_rel v v') vs vs' ->
        dcon_to_tag default_tag dc tgm = c_tag ->
        anf_val_rel (Con_v dc vs) (Vconstr c_tag vs')
  | anf_rel_Clos :
      forall vs rho names na x f e C1 r1 S1 S2,
        anf_env_rel' anf_val_rel names vs rho ->
        env_consistent names vs ->
        Disjoint var (x |: (f |: FromList names)) S1 ->
        Disjoint _ (cmap_vars cmap) S1 ->
        ~ x \in f |: FromList names ->
        ~ f \in FromList names ->
        anf_cvt_rel' S1 e (x :: names) S2 C1 r1 ->
        anf_val_rel (Clos_v vs na e)
                    (Vfun rho (Fcons f func_tag [x] (C1 |[ Ehalt r1 ]|) Fnil) f)
  | anf_rel_ClosFix :
      forall S1 S2 names fnames vs rho mfix Bs n f,
        anf_env_rel' anf_val_rel names vs rho ->
        env_consistent names vs ->
        NoDup fnames ->
        Disjoint _ (FromList names :|: FromList fnames) S1 ->
        Disjoint _ (cmap_vars cmap) S1 ->
        Disjoint _ (FromList names) (FromList fnames) ->
        nth_error fnames n = Some f ->
        anf_fix_rel fnames names S1 fnames mfix Bs S2 ->
        anf_val_rel (ClosFix_v vs mfix n) (Vfun rho Bs f).

  Definition anf_env_rel : list var -> list fuel_sem.value -> M.t val -> Prop :=
    anf_env_rel' anf_val_rel.


(* ================================================================= *)
(** * Fix Relation Helpers                                            *)
(* ================================================================= *)

  Lemma anf_fix_rel_fnames_length fnames names S1 fnames_list mfix Bs S2 :
    anf_fix_rel fnames names S1 fnames_list mfix Bs S2 ->
    List.length fnames_list = List.length mfix.
  Proof.
    intros Hrel. induction Hrel; simpl; congruence.
  Qed.

  Lemma anf_fix_rel_names fnames names S1 fnames_list mfix Bs S2 :
    anf_fix_rel fnames names S1 fnames_list mfix Bs S2 ->
    all_fun_name Bs = fnames_list.
  Proof.
    intros H. induction H; simpl; congruence.
  Qed.

  Lemma anf_fix_rel_find_def :
    forall fnames0 names0 S1 fnames_list mfix Bs S2 idx f d na e_body,
      anf_fix_rel fnames0 names0 S1 fnames_list mfix Bs S2 ->
      nth_error fnames_list idx = Some f ->
      nth_error mfix idx = Some d ->
      d.(EAst.dbody) = EAst.tLambda na e_body ->
      NoDup fnames_list ->
      exists x_pc C_body r_body S_body1 S_body2,
        find_def f Bs = Some (func_tag, [x_pc], C_body |[ Ehalt r_body ]|) /\
        anf_cvt_rel' S_body1 e_body
                     (x_pc :: List.rev fnames0 ++ names0) S_body2 C_body r_body.
  Proof.
    intros fnames0 names0 S1 fnames_list mfix Bs S2 idx f d na e_body
           Hrel Hnth_f Hnth_d Hbody Hnd.
    revert idx f d na e_body Hnth_f Hnth_d Hbody Hnd.
    induction Hrel; intros idx0 f0 d0 na0 e_body0 Hnth_f Hnth_d Hbody0 Hnd.
    - destruct idx0; discriminate.
    - destruct idx0 as [| idx'].
      + simpl in Hnth_f, Hnth_d. inv Hnth_f. inv Hnth_d.
        rewrite Hbody0 in H. inv H.
        do 5 eexists. split.
        * simpl. destruct (M.elt_eq f0 f0); [reflexivity | congruence].
        * eassumption.
      + simpl in Hnth_f, Hnth_d.
        match goal with H : NoDup (_ :: _) |- _ =>
          inversion H as [| ? ? Hnotin Hnd_tl]; subst end.
        edestruct IHHrel as (xp & Cb & rb & Sb1 & Sb2 & Hfind & Hcvt);
          [exact Hnth_f | exact Hnth_d | exact Hbody0 | exact Hnd_tl |].
        do 5 eexists. split.
        * simpl. destruct (M.elt_eq f0 f) as [Heq | Hneq].
          -- exfalso. subst. apply Hnotin. eapply nth_error_In. exact Hnth_f.
          -- exact Hfind.
        * exact Hcvt.
  Qed.


(* ================================================================= *)
(** * Subset Lemmas                                                   *)
(* ================================================================= *)

  Local Ltac subset_case :=
    unfold Ensembles.In; intros;
    first [ reflexivity
          | assumption
          | apply Setminus_Included
          | (eapply Setminus_Included_preserv; eassumption)
          | (eapply Setminus_Included_preserv;
             eapply Included_trans; [eassumption | eassumption])
          | (eapply Setminus_Included_preserv;
             eapply Included_trans; [eassumption |];
             eapply Included_trans; [eassumption |];
             eapply Included_trans; apply Setminus_Included)
          | (eapply Included_trans; [eassumption |]; apply Setminus_Included)
          | (eapply Included_trans; [eassumption |]; eassumption)
          | (eapply Included_trans; [eassumption |];
             eapply Included_trans; [eassumption |]; apply Setminus_Included)
          | (eapply Included_trans; [eassumption |];
             eapply Included_trans; apply Setminus_Included)
          | (eapply Setminus_Included_preserv; eassumption)
          | (eapply Included_trans; [eassumption |];
             eapply Included_trans; [apply Setminus_Included |]; eassumption) ].

  Local Notation P_sub := (fun S0 _ _ S0' _ _ => Included _ S0' S0).
  Local Notation P0_sub := (fun S0 _ _ S0' _ _ => Included _ S0' S0).
  Local Notation P1_sub := (fun S0 _ _ _ S0' _ => Included _ S0' S0).
  Local Notation P2_sub := (fun S0 _ _ _ _ _ S0' _ => Included _ S0' S0).

  Lemma anf_cvt_exp_subset :
    forall S e vn S' C x,
      anf_cvt_rel' S e vn S' C x -> S' \subset S.
  Proof.
    apply (anf_cvt_rel_ind' func_tag default_tag tgm cmap
             P_sub P0_sub P1_sub P2_sub); subset_case.
  Qed.

  Lemma anf_cvt_args_subset :
    forall S es vn S' C xs,
      anf_cvt_rel_args func_tag default_tag tgm cmap S es vn S' C xs -> S' \subset S.
  Proof.
    apply (anf_cvt_rel_args_ind' func_tag default_tag tgm cmap
             P_sub P0_sub P1_sub P2_sub); subset_case.
  Qed.

  Lemma anf_cvt_mfix_subset :
    forall S mfix vn fnames S' fdefs,
      anf_cvt_rel_mfix func_tag default_tag tgm cmap S mfix vn fnames S' fdefs -> S' \subset S.
  Proof.
    apply (anf_cvt_rel_mfix_ind' func_tag default_tag tgm cmap
             P_sub P0_sub P1_sub P2_sub); subset_case.
  Qed.

  Lemma anf_cvt_branches_subset :
    forall S ind brs n vn r S' pats,
      anf_cvt_rel_branches func_tag default_tag tgm cmap S ind brs n vn r S' pats -> S' \subset S.
  Proof.
    apply (anf_cvt_rel_branches_ind' func_tag default_tag tgm cmap
             P_sub P0_sub P1_sub P2_sub); subset_case.
  Qed.


  (* The result variable is NOT in the output fresh set.
     For tRel: x ∈ vn and vn ⊥ S, so x ∉ S = S'.
     For tConst: x ∈ cmap_vars and cmap_vars ⊥ S, so x ∉ S = S'.
     For other cases: x ∈ S and S' ⊆ S \\ {x}. *)
  Lemma anf_cvt_result_not_in_output :
    forall S e vn S' C x,
      anf_cvt_rel' S e vn S' C x ->
      Disjoint _ (FromList vn) S ->
      Disjoint _ (cmap_vars cmap) S ->
      ~ x \in S'.
  Proof.
    apply (anf_cvt_rel_ind' func_tag default_tag tgm cmap
      (fun S0 _ vn S' _ x => Disjoint _ (FromList vn) S0 ->
                              Disjoint _ (cmap_vars cmap) S0 -> ~ x \in S')
      (fun _ _ _ _ _ _ => True)
      (fun _ _ _ _ _ _ => True)
      (fun _ _ _ _ _ _ _ _ => True)).
    (* anf_Rel *)
    - intros S0 v vn0 n Hnth Hdis Hdis_cm Hin.
      eapply Hdis. constructor; [eapply nth_error_In; eassumption | exact Hin].
    (* anf_Lam *)
    - intros ? ? ? ? ? ? ? ? ? ? Hf Hcvt _ Hdis Hdis_cm Hin.
      apply (anf_cvt_exp_subset _ _ _ _ _ _ Hcvt) in Hin. inv Hin.
      match goal with H : ~ _ |- _ => apply H; constructor end.
    (* anf_App *)
    - intros S0 S2 S3 u C0 x0 v C1 x1 r vn0 _ IH1 _ IH2 Hr Hdis Hdis_cm Hin.
      inv Hin. match goal with H : ~ _ |- _ => apply H; constructor end.
    (* anf_Construct *)
    - intros ? ? ? ? ? ? ? ? ? ? ? Hx Hargs _ Hdis Hdis_cm Hin.
      eapply anf_cvt_args_subset in Hargs. eapply Hargs in Hin. inv Hin.
      match goal with H : ~ _ |- _ => apply H; constructor end.
    (* anf_LetIn *)
    - intros ? ? ? ? ? ? ? ? ? ? ? Hcvt1 IH1 Hcvt2 IH2 Hdis Hdis_cm.
      eapply IH2.
      + rewrite FromList_cons. eapply Union_Disjoint_l.
        * eapply Disjoint_Singleton_l. eapply IH1; assumption.
        * eapply Disjoint_Included_r; [exact (anf_cvt_exp_subset _ _ _ _ _ _ Hcvt1) | assumption].
      + eapply Disjoint_Included_r; [exact (anf_cvt_exp_subset _ _ _ _ _ _ Hcvt1) | assumption].
    (* anf_Case *)
    - intros S0 S2 S3 ind npars mch C0 x0 brs pats f y r vn0
             Hf Hy _ IH_mch _ IH_brs Hr Hdis Hdis_cm Hin.
      inv Hin. match goal with H : ~ _ |- _ => apply H; constructor end.
    (* anf_Fix: f ∈ FromList fnames, S2 ⊆ S1 \\ FromList fnames, so f ∉ S2 *)
    - intros ? ? ? ? ? ? ? ? _ _ _ Hmfix _ Hnth Hdis Hdis_cm Hin.
      assert (Hsub_mfix : _ \subset _) by (eapply anf_cvt_mfix_subset; exact Hmfix).
      apply Hsub_mfix in Hin. inv Hin.
      match goal with H : ~ _ |- _ => apply H; eapply nth_error_In; eassumption end.
    (* anf_Box *)
    - intros S0 vn0 x0 Hx Hdis Hdis_cm Hin. inv Hin.
      match goal with H : ~ _ |- _ => apply H; constructor end.
    (* anf_Const *)
    - intros S0 vn0 s v Hlookup Hdis Hdis_cm Hin.
      eapply Hdis_cm. constructor; [exists s; eassumption | exact Hin].
    (* anf_Proj *)
    - intros S0 S2 p c C0 x0 y vn0 ctag Htag _ IH Hy Hdis Hdis_cm Hin.
      inv Hin. match goal with H : ~ _ |- _ => apply H; constructor end.
    (* anf_Prim *)
    - intros S0 vn0 p pv x0 Hpv Hx Hdis Hdis_cm Hin. inv Hin.
      match goal with H : ~ _ |- _ => apply H; constructor end.
    - intros; exact I.
    - intros; exact I.
    - intros; exact I.
    - intros; exact I.
    - intros; exact I.
    - intros; exact I.
  Qed.

(* ================================================================= *)
(** * env_consistent                                                  *)
(* ================================================================= *)

  Lemma NoDup_env_consistent (vn : list var) (rho : list fuel_sem.value) :
    NoDup vn -> env_consistent vn rho.
  Proof.
    intros Hnd i j x Hi Hj.
    assert (Heq : i = j).
    { clear rho. revert j vn Hnd Hi Hj. induction i; intros j vn Hnd Hi Hj.
      - destruct vn; simpl in *; [discriminate |]. inv Hi.
        destruct j; [reflexivity |].
        simpl in Hj. inv Hnd. exfalso. apply H1. eapply nth_error_In. eassumption.
      - destruct vn; simpl in *; [discriminate |].
        destruct j; simpl in *.
        + inv Hnd. inv Hj. exfalso. apply H1. eapply nth_error_In. eassumption.
        + inv Hnd. f_equal. eapply IHi; eassumption. }
    subst. reflexivity.
  Qed.

End ANF_Val.


Section AlphaEquiv.

(* ================================================================= *)
(** * Alpha-Equivalence                                               *)
(* ================================================================= *)

  Context {fuel : Type} {Hfuel : @fuel_resource fuel}
          {trace : Type} {Htrace : @trace_resource trace}.

  Context (P1 : PostT) (PG : PostGT)
          (tgm : conId_map) (cmap : const_map)
          (cenv : ctor_env)
          (Hprops : Post_properties cenv P1 P1 PG)
          (HpropsG : Post_properties cenv PG PG PG)
          (Hincl : inclusion (comp P1 P1) P1)
          (HinclG : inclusion P1 PG).

  Context (func_tag default_tag : positive).

  Let anf_cvt_rel' := anf_cvt_rel func_tag default_tag tgm cmap.
  Let anf_cvt_rel_args' := anf_cvt_rel_args func_tag default_tag tgm cmap.
  Let anf_cvt_rel_mfix' := anf_cvt_rel_mfix func_tag default_tag tgm cmap.
  Let anf_cvt_rel_branches' := anf_cvt_rel_branches func_tag default_tag tgm cmap.
  Let anf_val_rel' := anf_val_rel func_tag default_tag tgm cmap.


(* ----------------------------------------------------------------- *)
(** ** Helper Lemmas                                                  *)
(* ----------------------------------------------------------------- *)

  Lemma Forall2_preord_var_env_monotonic k j rho1 rho2 vars1 vars2 :
    (j <= k)%nat ->
    Forall2 (preord_var_env cenv PG k rho1 rho2) vars1 vars2 ->
    Forall2 (preord_var_env cenv PG j rho1 rho2) vars1 vars2.
  Proof.
    intros Hle. eapply Forall2_monotonic.
    intros x y Hpve. eapply preord_var_env_monotonic; eassumption.
  Qed.

  Lemma Forall2_preord_var_env_set k rho1 rho2 x1 x2 v1 v2 vars1 vars2 :
    Forall2 (preord_var_env cenv PG k rho1 rho2) vars1 vars2 ->
    ~ x1 \in FromList vars1 ->
    ~ x2 \in FromList vars2 ->
    Forall2 (preord_var_env cenv PG k (M.set x1 v1 rho1) (M.set x2 v2 rho2))
            vars1 vars2.
  Proof.
    intros HF Hni1 Hni2. induction HF.
    - constructor.
    - constructor.
      + eapply preord_var_env_extend_neq.
        * exact H.
        * intros Heq. apply Hni1. subst. now left.
        * intros Heq. apply Hni2. subst. now left.
      + eapply IHHF.
        * intros Hc. apply Hni1. now right.
        * intros Hc. apply Hni2. now right.
  Qed.

  Lemma Forall2_preord_var_env_def_funs k B1 B2 rho1 rho2 vars1 vars2 :
    Forall2 (preord_var_env cenv PG k rho1 rho2) vars1 vars2 ->
    Disjoint _ (FromList vars1) (name_in_fundefs B1) ->
    Disjoint _ (FromList vars2) (name_in_fundefs B2) ->
    Forall2 (preord_var_env cenv PG k
               (def_funs B1 B1 rho1 rho1) (def_funs B2 B2 rho2 rho2))
            vars1 vars2.
  Proof.
    intros HF Hd1 Hd2. induction HF.
    - constructor.
    - constructor.
      + eapply preord_var_env_def_funs_not_In_r.
        * intros Hc. eapply Hd2. constructor. now left. exact Hc.
        * eapply preord_var_env_def_funs_not_In_l.
          -- intros Hc. eapply Hd1. constructor. now left. exact Hc.
          -- exact H.
      + eapply IHHF.
        * eapply Disjoint_Included_l; [| exact Hd1].
          intros z Hz. now right.
        * eapply Disjoint_Included_l; [| exact Hd2].
          intros z Hz. now right.
  Qed.

  (* preord_env_P is preserved through def_funs + M.set on both sides,
     when S is disjoint from the fundefs names and the set variables. *)
  Lemma preord_env_P_def_funs_set k S0 B1 B2 rho1 rho2 x1 x2 v1 v2 :
    preord_env_P cenv PG S0 k rho1 rho2 ->
    Disjoint _ S0 (name_in_fundefs B1) ->
    Disjoint _ S0 (name_in_fundefs B2) ->
    ~ x1 \in S0 ->
    ~ x2 \in S0 ->
    preord_env_P cenv PG S0 k
      (M.set x1 v1 (def_funs B1 B1 rho1 rho1))
      (M.set x2 v2 (def_funs B2 B2 rho2 rho2)).
  Proof.
    intros Henv Hdis_B1 Hdis_B2 Hni1 Hni2 z Hz.
    eapply preord_var_env_extend_neq.
    - eapply preord_var_env_def_funs_not_In_r.
      + intros Hc. eapply Hdis_B2. constructor; eassumption.
      + eapply preord_var_env_def_funs_not_In_l.
        * intros Hc. eapply Hdis_B1. constructor; eassumption.
        * eapply Henv. exact Hz.
    - intros Heq. subst. contradiction.
    - intros Heq. subst. contradiction.
  Qed.

  Lemma ctx_bind_proj_Forall2_compat k rho1 rho2 x1 x2 ctag
        proj_vars1 proj_vars2 acc1 acc2 e1 e2 n :
    preord_var_env cenv PG k rho1 rho2 x1 x2 ->
    Forall2 (preord_var_env cenv PG k rho1 rho2) acc1 acc2 ->
    List.length proj_vars1 = List.length proj_vars2 ->
    NoDup proj_vars1 ->
    NoDup proj_vars2 ->
    Disjoint _ (FromList proj_vars1) (FromList acc1 :|: [set x1]) ->
    Disjoint _ (FromList proj_vars2) (FromList acc2 :|: [set x2]) ->
    (forall rho1' rho2' m',
        (m' <= k)%nat ->
        Forall2 (preord_var_env cenv PG m' rho1' rho2')
                proj_vars1 proj_vars2 ->
        Forall2 (preord_var_env cenv PG m' rho1' rho2')
                acc1 acc2 ->
        preord_var_env cenv PG m' rho1' rho2' x1 x2 ->
        (* Variables outside proj_vars ∪ acc ∪ {x} are preserved *)
        (forall a b, preord_var_env cenv PG k rho1 rho2 a b ->
                     ~ a \in (FromList proj_vars1 :|: FromList acc1 :|: [set x1]) ->
                     ~ b \in (FromList proj_vars2 :|: FromList acc2 :|: [set x2]) ->
                     preord_var_env cenv PG m' rho1' rho2' a b) ->
        preord_exp cenv P1 PG m' (e1, rho1') (e2, rho2')) ->
    preord_exp cenv P1 PG k
               (ctx_bind_proj ctag x1 proj_vars1 n |[ e1 ]|, rho1)
               (ctx_bind_proj ctag x2 proj_vars2 n |[ e2 ]|, rho2).
  Proof.
    revert k rho1 rho2 x1 x2 ctag proj_vars2 acc1 acc2 e1 e2 n.
    induction proj_vars1;
      intros k rho1 rho2 x1 x2 ctag proj_vars2 acc1 acc2 e1 e2 n
             Hvar Hacc Hlen Hnd1 Hnd2 Hdis1 Hdis2 Hexp.
    - destruct proj_vars2; [| simpl in Hlen; congruence].
      cbn [ctx_bind_proj app_ctx_f].
      eapply Hexp; [lia | constructor | exact Hacc | exact Hvar |].
      intros a b Hab _ _. eapply preord_var_env_monotonic with (k := k); [exact Hab | lia].
    - destruct proj_vars2 as [| v proj_vars2]; [simpl in Hlen; congruence |].
      simpl in Hlen. cbn [ctx_bind_proj app_ctx_f].
      inv Hnd1. inv Hnd2.
      eapply preord_exp_proj_compat.
      + eapply Hprops.
      + eapply Hprops.
      + exact Hvar.
      + intros m v1 v2 Hlt Hval.
        eapply IHproj_vars1 with (acc1 := a :: acc1) (acc2 := v :: acc2).
        * eapply preord_var_env_extend_neq.
          -- eapply preord_var_env_monotonic. exact Hvar. lia.
          -- intros Hc. subst. eapply Hdis1. constructor. now left. right. constructor.
          -- intros Hc. subst. eapply Hdis2. constructor. now left. right. constructor.
        * constructor.
          -- eapply preord_var_env_extend_eq. exact Hval.
          -- eapply Forall2_preord_var_env_set.
             ++ eapply Forall2_preord_var_env_monotonic; [| exact Hacc]. lia.
             ++ intros Hc. eapply Hdis1. constructor. now left. left. exact Hc.
             ++ intros Hc. eapply Hdis2. constructor. now left. left. exact Hc.
        * congruence.
        * assumption.
        * assumption.
        * eapply Disjoint_Included_r with
            (s2 := [set a] :|: (FromList acc1 :|: [set x1])).
          { rewrite FromList_cons. now sets. }
          eapply Union_Disjoint_r.
          -- eapply Disjoint_Singleton_r. assumption.
          -- eapply Disjoint_Included_l; [| exact Hdis1].
             repeat normalize_sets. now sets.
        * eapply Disjoint_Included_r with
            (s2 := [set v] :|: (FromList acc2 :|: [set x2])).
          { rewrite FromList_cons. now sets. }
          eapply Union_Disjoint_r.
          -- eapply Disjoint_Singleton_r. assumption.
          -- eapply Disjoint_Included_l; [| exact Hdis2].
             repeat normalize_sets. now sets.
        * (* Inner continuation *)
          intros rho1' rho2' m' Hm' Hpv Hacc' Hvar' Htransfer_inner.
          inversion Hacc' as [| ? ? ? ? Hhd Htl]; subst.
          eapply Hexp.
          -- lia.
          -- constructor; [exact Hhd | exact Hpv].
          -- exact Htl.
          -- exact Hvar'.
          -- (* Transfer: chain extend_neq + inner transfer *)
             intros a0 b0 Hab Hni1 Hni2.
             eapply Htransfer_inner.
             ++ (* preord_var_env in M.set env: extend_neq from original *)
                eapply preord_var_env_extend_neq.
                ** eapply preord_var_env_monotonic with (k := k). exact Hab. lia.
                ** intros Heq. subst. apply Hni1. repeat normalize_sets. left. now left.
                ** intros Heq. subst. apply Hni2. repeat normalize_sets. left. now left.
             ++ intros Hc. apply Hni1.
                repeat normalize_sets.
                (* Hc: a0 ∈ (FromList proj_vars1 :|: (a |: FromList acc1)) :|: {x1}
                   Goal: a0 ∈ ((a |: FromList proj_vars1) :|: FromList acc1) :|: {x1} *)
                inv Hc.
                ** inv H.
                   --- left. left. right. assumption.
                   --- inv H0.
                       +++ left. left. left. assumption.
                       +++ left. right. assumption.
                ** right. assumption.
             ++ intros Hc. apply Hni2.
                repeat normalize_sets.
                inv Hc.
                ** inv H.
                   --- left. left. right. assumption.
                   --- inv H0.
                       +++ left. left. left. assumption.
                       +++ left. right. assumption.
                ** right. assumption.
  Qed.


(* ----------------------------------------------------------------- *)
(** ** Alpha-Equivalence Definitions                                  *)
(* ----------------------------------------------------------------- *)

  (** Two ANF conversions of the same term [e], with different fresh
      variable sets and name mappings, produce [preord_exp]-related results.

      The statement is continuation-passing: given that the continuations
      [e_k1] and [e_k2] are related (under appropriate conditions on
      results and environments), the full expressions [C1|[e_k1]|] and
      [C2|[e_k2]|] are related. This generalization is needed to compose
      contexts (e.g. [comp_ctx_f C1 C2] for [tLetIn] and [tApp]). *)
  Definition anf_cvt_exp_alpha_equiv_for (e : EAst.term) k :=
    forall C1 C2 r1 r2 m vars1 vars2 rho1 rho2 S1 S2 S3 S4 e_k1 e_k2,
      (* Step index bound *)
      (m <= k)%nat ->
      (* Two relational derivations for the same source term [e] *)
      anf_cvt_rel' S1 e vars1 S2 C1 r1 ->
      anf_cvt_rel' S3 e vars2 S4 C2 r2 ->
      (* Local variable names are disjoint from the fresh sets *)
      Disjoint _ (FromList vars1) S1 ->
      Disjoint _ (FromList vars2) S3 ->
      (* Global constant variables are disjoint from the fresh sets *)
      Disjoint _ (cmap_vars cmap) S1 ->
      Disjoint _ (cmap_vars cmap) S3 ->
      (* Local variable bindings are pairwise related *)
      Forall2 (preord_var_env cenv PG m rho1 rho2) vars1 vars2 ->
      (* Global constant bindings are related *)
      preord_env_P cenv PG (cmap_vars cmap) m rho1 rho2 ->
      (* Continuation hypothesis: if the result variables [r1 ~ r2] are
         related, local bindings are preserved, and variables not consumed
         by this conversion are transferred, then [e_k1 ~ e_k2] *)
      (forall j rho1' rho2',
        (j <= m)%nat ->
        preord_var_env cenv PG j rho1' rho2' r1 r2 ->
        Forall2 (preord_var_env cenv PG j rho1' rho2') vars1 vars2 ->
        (forall x y, preord_var_env cenv PG m rho1 rho2 x y ->
                     ~ x \in S1 -> ~ y \in S3 ->
                     preord_var_env cenv PG j rho1' rho2' x y) ->
        preord_exp cenv P1 PG j (e_k1, rho1') (e_k2, rho2')) ->
      preord_exp cenv P1 PG m (C1 |[ e_k1 ]|, rho1) (C2 |[ e_k2 ]|, rho2).

  Definition anf_cvt_exp_alpha_equiv k :=
    forall e, anf_cvt_exp_alpha_equiv_for e k.

  (** Same as [anf_cvt_exp_alpha_equiv_for] but for argument lists.
      The continuation receives [Forall2] on the result variable lists. *)
  Definition anf_cvt_args_alpha_equiv_for (args : list EAst.term) k :=
    forall C1 C2 xs1 xs2 m vars1 vars2 rho1 rho2 S1 S2 S3 S4 e_k1 e_k2,
      (m <= k)%nat ->
      anf_cvt_rel_args' S1 args vars1 S2 C1 xs1 ->
      anf_cvt_rel_args' S3 args vars2 S4 C2 xs2 ->
      Disjoint _ (FromList vars1) S1 ->
      Disjoint _ (FromList vars2) S3 ->
      Disjoint _ (cmap_vars cmap) S1 ->
      Disjoint _ (cmap_vars cmap) S3 ->
      Forall2 (preord_var_env cenv PG m rho1 rho2) vars1 vars2 ->
      preord_env_P cenv PG (cmap_vars cmap) m rho1 rho2 ->
      (forall j rho1' rho2',
        (j <= m)%nat ->
        Forall2 (preord_var_env cenv PG j rho1' rho2') xs1 xs2 ->
        Forall2 (preord_var_env cenv PG j rho1' rho2') vars1 vars2 ->
        (forall x y, preord_var_env cenv PG m rho1 rho2 x y ->
                     ~ x \in S1 -> ~ y \in S3 ->
                     preord_var_env cenv PG j rho1' rho2' x y) ->
        preord_exp cenv P1 PG j (e_k1, rho1') (e_k2, rho2')) ->
      preord_exp cenv P1 PG m (C1 |[ e_k1 ]|, rho1) (C2 |[ e_k2 ]|, rho2).

  (** Two ANF conversions of the same mutual fixpoint produce
      [Forall2 (preord_var_env ...)] on function names in [def_funs] environments. *)
  Definition anf_cvt_mfix_alpha_equiv_for
             (mfix : list (EAst.def EAst.term)) k :=
    forall B1 B2 fnames1 fnames2 m outer_vars1 outer_vars2 rho1 rho2
           S1 S2 S3 S4,
      (m <= k)%nat ->
      anf_cvt_rel_mfix' S1 mfix (List.rev fnames1 ++ outer_vars1) fnames1 S2 B1 ->
      anf_cvt_rel_mfix' S3 mfix (List.rev fnames2 ++ outer_vars2) fnames2 S4 B2 ->
      NoDup fnames1 -> NoDup fnames2 ->
      List.length fnames1 = List.length fnames2 ->
      List.length outer_vars1 = List.length outer_vars2 ->
      Disjoint _ (FromList fnames1 :|: FromList outer_vars1) S1 ->
      Disjoint _ (FromList fnames2 :|: FromList outer_vars2) S3 ->
      Disjoint _ (cmap_vars cmap) S1 ->
      Disjoint _ (cmap_vars cmap) S3 ->
      Disjoint _ (FromList fnames1) (FromList outer_vars1) ->
      Disjoint _ (FromList fnames2) (FromList outer_vars2) ->
      Forall2 (preord_var_env cenv PG m rho1 rho2) outer_vars1 outer_vars2 ->
      preord_env_P cenv PG (cmap_vars cmap) m rho1 rho2 ->
      Forall2 (preord_var_env cenv PG m
                 (def_funs B1 B1 rho1 rho1) (def_funs B2 B2 rho2 rho2))
              fnames1 fnames2.

  (** Two ANF conversions of the same case branches produce
      [preord_exp]-related [Ecase] expressions. *)
  Definition anf_cvt_branches_alpha_equiv_for
             (ind : inductive) (brs : list (list name * EAst.term)) (n : N) k :=
    forall pats1 pats2 m y1 y2 vars1 vars2 rho1 rho2 S1 S2 S3 S4,
      (m <= k)%nat ->
      anf_cvt_rel_branches' S1 ind brs n vars1 y1 S2 pats1 ->
      anf_cvt_rel_branches' S3 ind brs n vars2 y2 S4 pats2 ->
      Disjoint _ ([set y1] :|: FromList vars1) S1 ->
      Disjoint _ ([set y2] :|: FromList vars2) S3 ->
      Disjoint _ (cmap_vars cmap) S1 ->
      Disjoint _ (cmap_vars cmap) S3 ->
      Forall2 (preord_var_env cenv PG m rho1 rho2) vars1 vars2 ->
      preord_var_env cenv PG m rho1 rho2 y1 y2 ->
      preord_env_P cenv PG (cmap_vars cmap) m rho1 rho2 ->
      preord_exp cenv P1 PG m (Ecase y1 pats1, rho1) (Ecase y2 pats2, rho2).

  (* Value-level alpha-equiv *)
  Definition anf_cvt_val_alpha_equiv_statement k :=
    forall v v1 v2,
      anf_val_rel' v v1 -> anf_val_rel' v v2 ->
      preord_val cenv PG k v1 v2.


  Lemma anf_cvt_env_alpha_equiv_Forall2 k :
    anf_cvt_val_alpha_equiv_statement k ->
    forall vs nms_a nms_b rho_a rho_b,
      anf_env_rel' anf_val_rel' nms_a vs rho_a ->
      anf_env_rel' anf_val_rel' nms_b vs rho_b ->
      Forall2 (preord_var_env cenv PG k rho_a rho_b) nms_a nms_b.
  Proof.
    intros Hval. induction vs; intros nms_a nms_b rho_a rho_b Hrel1 Hrel2.
    - inv Hrel1. inv Hrel2. constructor.
    - inv Hrel1. inv Hrel2.
      match goal with
      | [ H1 : exists _, M.get ?x1 rho_a = Some _ /\ _,
          H2 : exists _, M.get ?x2 rho_b = Some _ /\ _ |- _ ] =>
        destruct H1 as [v1 [Hg1 Hv1]]; destruct H2 as [v2 [Hg2 Hv2]]
      end.
      constructor.
      + intros w Hgetw. rewrite Hg1 in Hgetw. inv Hgetw.
        eexists. split. exact Hg2. eapply Hval; eassumption.
      + eapply IHvs; eassumption.
  Qed.

  (* Derives args alpha-equiv assuming exp alpha-equiv for each element *)
  Lemma anf_cvt_args_alpha_from_all k args :
    All (fun t => anf_cvt_exp_alpha_equiv_for t k) args ->
    anf_cvt_args_alpha_equiv_for args k.
  Proof.
    intros Hall. unfold anf_cvt_args_alpha_equiv_for.
    induction args as [| t args' IHargs];
    intros C1 C2 xs1 xs2 m vars1 vars2 rho1 rho2 S1 S2 S3 S4 e_k1 e_k2
           Hm Hrel1 Hrel2 Hdis1 Hdis2 Hdis_cm1 Hdis_cm2 Henv Hglob Hcont.
    - (* nil *)
      inv Hrel1. inv Hrel2. simpl.
      eapply Hcont; [lia | constructor | assumption | intros; assumption].
    - (* cons *)
      inv Hrel1. inv Hrel2.
      inversion Hall as [| ? ? IH_hd IH_tl]; subst.
      rewrite <- !app_ctx_f_fuse.
      (* IH for head t *)
      eapply IH_hd; [lia | eassumption | eassumption | assumption | assumption
                     | assumption | assumption | assumption | assumption |].
      (* Continuation: after head, convert tail *)
      intros j rho1' rho2' Hj Hvar_hd Henv' Htransfer.
      eapply IHargs; [exact IH_tl | lia | eassumption | eassumption
                      | eapply Disjoint_Included_r; [eapply anf_cvt_exp_subset; eassumption | assumption]
                      | eapply Disjoint_Included_r; [eapply anf_cvt_exp_subset; eassumption | assumption]
                      | eapply Disjoint_Included_r; [eapply anf_cvt_exp_subset; eassumption | assumption]
                      | eapply Disjoint_Included_r; [eapply anf_cvt_exp_subset; eassumption | assumption]
                      | exact Henv'
                      | intros v0 Hv0; eapply Htransfer;
                        [eapply Hglob; exact Hv0
                        | intros Hc; eapply Hdis_cm1; constructor; eassumption
                        | intros Hc; eapply Hdis_cm2; constructor; eassumption]
                      |].
      (* Continuation: combine head and tail results *)
      intros j' rho1'' rho2'' Hj' Hxs_tl Henv'' Htransfer'.
      eapply Hcont.
      + lia.
      + constructor; [| exact Hxs_tl].
        eapply Htransfer'.
        * eapply preord_var_env_monotonic with (k := j). exact Hvar_hd. lia.
        * eapply anf_cvt_result_not_in_output; eassumption.
        * eapply anf_cvt_result_not_in_output; eassumption.
      + exact Henv''.
      + intros a b0 Hab Ha Hb.
        eapply Htransfer'. eapply Htransfer; eassumption.
        * intros Hc. apply Ha. eapply anf_cvt_exp_subset; eassumption.
        * intros Hc. apply Hb. eapply anf_cvt_exp_subset; eassumption.
  Qed.

  (* Two branches derivations for the same source produce matching constructor tags *)
  Lemma anf_cvt_rel_branches_ctor_tag S1 S2 S3 S4 ind brs n vn1 vn2 y1 y2 pats1 pats2 :
    anf_cvt_rel_branches' S1 ind brs n vn1 y1 S2 pats1 ->
    anf_cvt_rel_branches' S3 ind brs n vn2 y2 S4 pats2 ->
    Forall2 (fun p p' : ctor_tag * exp => fst p = fst p') pats1 pats2.
  Proof.
    revert S1 S2 S3 S4 n vn1 vn2 y1 y2 pats1 pats2.
    induction brs as [| [lnames e_br] brs' IH];
      intros S1 S2 S3 S4 n vn1 vn2 y1 y2 pats1 pats2 Hrel1 Hrel2.
    - inv Hrel1; inv Hrel2; constructor.
    - inv Hrel1; inv Hrel2; constructor; [simpl; congruence | eapply IH; eassumption].
  Qed.

  (* Derives branches alpha-equiv assuming exp alpha-equiv for each branch body *)
  Lemma anf_cvt_branches_alpha_from_all k ind brs n :
    All (fun br : list name * EAst.term =>
           anf_cvt_exp_alpha_equiv_for (snd br) k) brs ->
    anf_cvt_branches_alpha_equiv_for ind brs n k.
  Proof.
    intros Hall. unfold anf_cvt_branches_alpha_equiv_for.
    induction brs as [| [lnames e_br] brs' IHbrs];
    intros pats1 pats2 m y1 y2 vars1 vars2 rho1 rho2 S1 S2 S3 S4
           Hm Hrel1 Hrel2 Hdis1 Hdis2 Hdis_cm1 Hdis_cm2 Henv Hvar_y Hglob.
    - (* nil *)
      inv Hrel1. inv Hrel2.
      eapply preord_exp_case_nil_compat. eapply Hprops.
    - (* cons *)
      inv Hrel1. inv Hrel2.
      inversion Hall as [| ? ? IH_hd IH_tl]; subst. simpl in IH_hd.
      eapply preord_exp_case_cons_compat.
      + eapply Hprops.
      + eapply Hprops.
      + eapply Hprops.
      + eapply anf_cvt_rel_branches_ctor_tag; eassumption.
      + exact Hvar_y.
      + (* head branch body *)
        intros m' Hlt.
        eapply preord_exp_monotonic.
        * assert (Hlen_eq : Datatypes.length vars = Datatypes.length vars0).
          { match goal with
            | [H1 : Datatypes.length vars = _, H2 : Datatypes.length vars0 = _ |- _] =>
              congruence
            end. }
          rewrite <- Hlen_eq in *.
          eapply ctx_bind_proj_Forall2_compat with (acc1 := vars1) (acc2 := vars2).
          -- eapply preord_var_env_monotonic with (k := m). exact Hvar_y.
             apply Nat.lt_le_incl. exact Hlt.
          -- eapply Forall2_preord_var_env_monotonic with (k := m); [| exact Henv].
             apply Nat.lt_le_incl. exact Hlt.
          -- exact Hlen_eq.
          -- assumption. (* NoDup vars *)
          -- assumption. (* NoDup vars0 *)
          -- (* Disjoint pvars from vars :|: {y1} *)
             eapply Disjoint_Included_l.
             ++ match goal with H : FromList ?vs \subset _ |- _ =>
                  eapply Included_trans; [exact H | eapply anf_cvt_branches_subset; eassumption] end.
             ++ eapply Disjoint_Included_r; [| eapply Disjoint_sym; exact Hdis1].
                rewrite Union_commut. eapply Included_refl.
          -- eapply Disjoint_Included_l.
             ++ match goal with H : FromList ?vs \subset _ |- _ =>
                  eapply Included_trans; [exact H | eapply anf_cvt_branches_subset; eassumption] end.
             ++ eapply Disjoint_Included_r; [| eapply Disjoint_sym; exact Hdis2].
                rewrite Union_commut. eapply Included_refl.
          -- (* continuation: body alpha equiv after projections *)
             intros rho1' rho2' m'' Hle Hpvs Hvars Hvar' Htransfer_proj.
             eapply IH_hd.
             ++ lia.
             ++ eassumption.
             ++ eassumption.
             ++ (* Disjoint (pvars ++ vars1) S_body1 *)
                rewrite FromList_app. eapply Union_Disjoint_l.
                ** eapply Disjoint_Setminus_r. eapply Included_refl.
                ** eapply Disjoint_Included_r.
                   --- eapply Included_trans. eapply Setminus_Included.
                       eapply anf_cvt_branches_subset. eassumption.
                   --- eapply Disjoint_Included_l; [| exact Hdis1].
                       intros z Hz. right. exact Hz.
             ++ rewrite FromList_app. eapply Union_Disjoint_l.
                ** eapply Disjoint_Setminus_r. eapply Included_refl.
                ** eapply Disjoint_Included_r.
                   --- eapply Included_trans. eapply Setminus_Included.
                       eapply anf_cvt_branches_subset. eassumption.
                   --- eapply Disjoint_Included_l; [| exact Hdis2].
                       intros z Hz. right. exact Hz.
             ++ (* Disjoint cmap S_body1 *)
                eapply Disjoint_Included_r.
                ** eapply Included_trans. eapply Setminus_Included.
                   eapply anf_cvt_branches_subset. eassumption.
                ** exact Hdis_cm1.
             ++ eapply Disjoint_Included_r.
                ** eapply Included_trans. eapply Setminus_Included.
                   eapply anf_cvt_branches_subset. eassumption.
                ** exact Hdis_cm2.
             ++ eapply Forall2_app; eassumption.
             ++ (* preord_env_P cmap_vars: cmap vars not in proj_vars ∪ vars ∪ {y},
                   so they're preserved through ctx_bind_proj *)
                admit.
             ++ (* body continuation: Ehalt *)
                intros j rho1'' rho2'' Hle' Hvar_r Henv_body Hpres.
                eapply preord_exp_halt_compat;
                  [eapply Hprops | eapply Hprops | exact Hvar_r].
        * lia.
      + (* tail: recursive *)
        admit.
  Admitted.

  (* Derives mfix alpha-equiv assuming exp alpha-equiv for each body
     and at strictly smaller step indices (for closure values) *)
  Lemma anf_cvt_mfix_alpha_from_all k mfix :
    All (fun d : EAst.def EAst.term =>
           match EAst.dbody d with
           | EAst.tLambda _ e1 => anf_cvt_exp_alpha_equiv_for e1 k
           | _ => True
           end) mfix ->
    (forall j, (j < k)%nat -> forall e, anf_cvt_exp_alpha_equiv_for e j) ->
    anf_cvt_mfix_alpha_equiv_for mfix k.
  Proof. admit. Admitted.


(* ----------------------------------------------------------------- *)
(** ** Main Theorems                                                   *)
(* ----------------------------------------------------------------- *)

  Lemma anf_cvt_alpha_equiv :
    forall k e, anf_cvt_exp_alpha_equiv_for e k.
  Proof.
    intros k. induction k as [k IHk] using lt_wf_rec1.
    intros e. induction e using term_ind_fix_body;
    unfold anf_cvt_exp_alpha_equiv_for;
    intros C1 C2 r1 r2 m vars1 vars2 rho1 rho2 S1 S2 S3 S4 e_k1 e_k2
           Hm Hrel1 Hrel2 Hdis1 Hdis2 Hdis_cm1 Hdis_cm2 Henv Hglob Hcont.

    { (* tBox *)
      inv Hrel1. inv Hrel2. simpl.
      eapply preord_exp_constr_compat.
      - eapply Hprops.
      - eapply Hprops.
      - constructor.
      - intros m0 vs1 vs2 Hlt Hvals.
        eapply Hcont.
        + lia.
        + intros v1 Hg1. rewrite M.gss in Hg1. inv Hg1.
          eexists. split. { rewrite M.gss. reflexivity. }
          rewrite preord_val_eq. simpl. split; [reflexivity | eassumption].
        + eapply Forall2_preord_var_env_set.
          * eapply Forall2_preord_var_env_monotonic; [| eassumption]. lia.
          * intros Hin. eapply Hdis1. constructor; eassumption.
          * intros Hin. eapply Hdis2. constructor; eassumption.
        + intros a b Hvar Ha Hb.
          eapply preord_var_env_extend_neq.
          * eapply preord_var_env_monotonic. eassumption. lia.
          * intros Heq. subst. eapply Ha. eassumption.
          * intros Heq. subst. eapply Hb. eassumption. }

    { (* tRel *)
      inv Hrel1. inv Hrel2. simpl.
      eapply Hcont; [lia | | assumption |].
      - eapply Forall2_nth_error in Henv; [exact Henv | |]; eassumption.
      - intros; assumption. }

    (* tVar — impossible *) 1: inv Hrel1.
    (* tEvar — impossible *) 1: inv Hrel1.

    { (* tLambda na body: Efun1_c (Fcons f func_tag [x] (C|[Ehalt r]|) Fnil) Hole_c *)
      inv Hrel1. inv Hrel2. simpl.
      eapply preord_exp_fun_compat.
      - eapply Hprops.
      - eapply Hprops.
      - eapply Hcont.
        + lia.
        + (* preord_var_env for f1 ~ f2 as closures in def_funs *)
          intros v Hg.
          rewrite def_funs_eq in Hg. 2: { simpl; now left. }
          inv Hg.
          eexists. split. { rewrite def_funs_eq. reflexivity. simpl; now left. }
          eapply preord_val_fun.
          * simpl. rewrite Coqlib.peq_true. reflexivity.
          * simpl. rewrite Coqlib.peq_true. reflexivity.
          * intros rho_b j' vs1 vs2 Hlen Hset.
            destruct vs1 as [| v_arg1 [| ? ?]]; simpl in *; try congruence.
            destruct vs2 as [| v_arg2 [| ? ?]]; simpl in *; try congruence.
            inv Hset.
            eexists. split. { reflexivity. }
            intros Hlt' Hall_args. inv Hall_args.
            eapply preord_exp_post_monotonic. { now eapply HinclG. }
            eapply IHe; [lia | eassumption | eassumption | | | | | | |].
            -- rewrite FromList_cons. eapply Union_Disjoint_l.
               ++ eapply Disjoint_Singleton_l. intros Hc.
                  inv Hc. inv H. match goal with H : ~ _ |- _ => apply H; constructor end.
               ++ eapply Disjoint_Included_r. apply Setminus_Included.
                  eapply Disjoint_Included_r. apply Setminus_Included. exact Hdis1.
            -- rewrite FromList_cons. eapply Union_Disjoint_l.
               ++ eapply Disjoint_Singleton_l. intros Hc.
                  inv Hc. inv H. match goal with H : ~ _ |- _ => apply H; constructor end.
               ++ eapply Disjoint_Included_r. apply Setminus_Included.
                  eapply Disjoint_Included_r. apply Setminus_Included. exact Hdis2.
            -- eapply Disjoint_Included_r. apply Setminus_Included.
               eapply Disjoint_Included_r. apply Setminus_Included. exact Hdis_cm1.
            -- eapply Disjoint_Included_r. apply Setminus_Included.
               eapply Disjoint_Included_r. apply Setminus_Included. exact Hdis_cm2.
            -- constructor.
               ++ eapply preord_var_env_extend_eq. eassumption.
               ++ eapply Forall2_preord_var_env_set.
                  ** eapply Forall2_preord_var_env_set.
                     --- eapply Forall2_preord_var_env_monotonic with (k := m);
                           [lia | exact Henv].
                     --- intros Hc. eapply Hdis1. constructor; [exact Hc |].
                         eapply Setminus_Included. eassumption.
                     --- intros Hc. eapply Hdis2. constructor; [exact Hc |].
                         eapply Setminus_Included. eassumption.
                  ** intros Hc. eapply Hdis1. constructor; [exact Hc | eassumption].
                  ** intros Hc. eapply Hdis2. constructor; [exact Hc | eassumption].
            -- (* preord_env_P cmap_vars in closure body env:
                  rho_body = M.set x_arg v_arg (def_funs B B rho rho).
                  cmap vars are in rho, preserved through def_funs and M.set
                  because they're disjoint from fundefs names and arg var. *)
               intros v0 Hv0.
               (* Forward: Hglob → monotonic → def_funs_l → def_funs_r → extend_neq *)
               assert (Hpv0 : preord_var_env cenv PG j' rho1 rho2 v0 v0).
               { eapply preord_var_env_monotonic with (k := m).
                 eapply Hglob. exact Hv0. lia. }
               (* Goal: preord_var_env j' (M.set x1 v1 (M.set f1 vf1 rho1))
                                           (M.set x2 v2 (M.set f2 vf2 rho2)) v0 v0
                  v0 ∈ cmap_vars. v0 ≠ x1, x2 (disjoint from S ∋ x1,x2).
                  v0 ≠ f1, f2 (disjoint from S \\ {x} ∋ f). So M.gso twice. *)
               eapply preord_var_env_extend_neq;
                 [| intros Heq; subst; eapply Hdis_cm1; constructor; [exact Hv0 | eassumption]
                  | intros Heq; subst; eapply Hdis_cm2; constructor; [exact Hv0 | eassumption]].
               eapply preord_var_env_extend_neq;
                 [| intros Heq; subst; eapply Hdis_cm1; constructor; [exact Hv0 |];
                    eapply Setminus_Included; eassumption
                  | intros Heq; subst; eapply Hdis_cm2; constructor; [exact Hv0 |];
                    eapply Setminus_Included; eassumption].
               eapply preord_var_env_monotonic with (k := m).
               eapply Hglob. exact Hv0. lia.
            -- intros j0 rho1'' rho2'' _ Hvar_cont _ _.
               eapply preord_exp_halt_compat;
                 [eapply Hprops | eapply Hprops | exact Hvar_cont].
        + (* Forall2 vars in def_funs env *)
          eapply Forall2_preord_var_env_set.
          * eapply Forall2_preord_var_env_monotonic with (k := m); [lia | exact Henv].
          * intros Hc. eapply Hdis1. constructor; [exact Hc |].
            eapply Setminus_Included. eassumption.
          * intros Hc. eapply Hdis2. constructor; [exact Hc |].
            eapply Setminus_Included. eassumption.
        + intros a b0 Hab Ha Hb.
          eapply preord_var_env_extend_neq.
          * eapply preord_var_env_monotonic with (k := m). exact Hab. lia.
          * intros Heq. subst. apply Ha. eapply Setminus_Included. eassumption.
          * intros Heq. subst. apply Hb. eapply Setminus_Included. eassumption. }
    { (* tLetIn na b t: comp_ctx_f C_b C_t *)
      inv Hrel1. inv Hrel2.
      rewrite <- !app_ctx_f_fuse.
      (* IH1 for binding b *)
      eapply IHe1; [lia | eassumption | eassumption | assumption | assumption
                    | assumption | assumption | assumption | assumption |].
      (* Continuation: after b converted, convert t in extended env *)
      intros j rho1' rho2' Hj Hvar_x Henv' Htransfer.
      eapply IHe2; [lia | eassumption | eassumption | | | | | | |].
      - (* Disjoint (x1::vars1) S_mid1 *)
        rewrite FromList_cons. eapply Union_Disjoint_l.
        + eapply Disjoint_Singleton_l.
          eapply anf_cvt_result_not_in_output; eassumption.
        + eapply Disjoint_Included_r; [eapply anf_cvt_exp_subset; eassumption | assumption].
      - rewrite FromList_cons. eapply Union_Disjoint_l.
        + eapply Disjoint_Singleton_l.
          eapply anf_cvt_result_not_in_output; eassumption.
        + eapply Disjoint_Included_r; [eapply anf_cvt_exp_subset; eassumption | assumption].
      - (* Disjoint cmap S_mid1 *)
        eapply Disjoint_Included_r; [eapply anf_cvt_exp_subset; eassumption | assumption].
      - eapply Disjoint_Included_r; [eapply anf_cvt_exp_subset; eassumption | assumption].
      - (* Forall2 (x1::vars1) (x2::vars2) *)
        constructor; [exact Hvar_x | exact Henv'].
      - (* preord_env_P cmap_vars: transfer from Hglob via Htransfer *)
        intros v Hv_in.
        eapply Htransfer.
        + eapply Hglob. exact Hv_in.
        + intros Hc. eapply Hdis_cm1. constructor; eassumption.
        + intros Hc. eapply Hdis_cm2. constructor; eassumption.
      - (* Continuation for t: chain to Hcont *)
        intros j' rho1'' rho2'' Hj' Hvar_r Henv'' Htransfer'.
        eapply Hcont.
        + lia.
        + exact Hvar_r.
        + match goal with H : Forall2 _ (_ :: _) (_ :: _) |- _ => inv H end. assumption.
        + intros a b0 Hab Ha Hb.
          eapply Htransfer'.
          * eapply Htransfer; eassumption.
          * intros Hc. apply Ha.
            eapply anf_cvt_exp_subset in Hc; [exact Hc |]; eassumption.
          * intros Hc. apply Hb.
            eapply anf_cvt_exp_subset in Hc; [exact Hc |]; eassumption. }
    { (* tApp u v: comp_ctx_f C1 (comp_ctx_f C2 (Eletapp_c r x1 func_tag [x2] Hole_c)) *)
      inv Hrel1. inv Hrel2.
      rewrite <- !app_ctx_f_fuse. simpl.
      (* IH1 for function u *)
      eapply IHe1; [lia | eassumption | eassumption | assumption | assumption
                    | assumption | assumption | assumption | assumption |].
      intros j rho1' rho2' Hj Hvar_x1 Henv' Htransfer1.
      (* IH2 for argument v *)
      eapply IHe2; [lia | eassumption | eassumption
                    | eapply Disjoint_Included_r; [eapply anf_cvt_exp_subset; eassumption | assumption]
                    | eapply Disjoint_Included_r; [eapply anf_cvt_exp_subset; eassumption | assumption]
                    | eapply Disjoint_Included_r; [eapply anf_cvt_exp_subset; eassumption | assumption]
                    | eapply Disjoint_Included_r; [eapply anf_cvt_exp_subset; eassumption | assumption]
                    | exact Henv'
                    | intros v0 Hv0; eapply Htransfer1;
                      [eapply Hglob; exact Hv0
                      | intros Hc; eapply Hdis_cm1; constructor; eassumption
                      | intros Hc; eapply Hdis_cm2; constructor; eassumption]
                    |].
      intros j' rho1'' rho2'' Hj' Hvar_x2 Henv'' Htransfer2.
      (* letapp compatibility *)
      eapply preord_exp_letapp_compat.
      - eapply Hprops.
      - eapply Hprops.
      - eapply Hprops.
      - (* function x1 preserved through C2 *)
        eapply Htransfer2.
        + eapply preord_var_env_monotonic with (k := j).
          exact Hvar_x1. lia.
        + eapply anf_cvt_result_not_in_output; eassumption.
        + eapply anf_cvt_result_not_in_output; eassumption.
      - (* arg list [x2] *)
        constructor; [exact Hvar_x2 | constructor].
      - (* callback: r bound to call result *)
        intros m'' v1 v2 Hlt Hval.
        eapply Hcont.
        + lia.
        + intros w1 Hgr1. rewrite M.gss in Hgr1. inv Hgr1.
          eexists. split; [rewrite M.gss; reflexivity |].
          eapply preord_val_monotonic; [exact Hval | lia].
        + eapply Forall2_preord_var_env_set.
          * eapply Forall2_preord_var_env_monotonic with (k := j'); [lia | exact Henv''].
          * intros Hin. eapply Hdis1. constructor; [exact Hin |].
            eapply anf_cvt_exp_subset; [eassumption |].
            eapply anf_cvt_exp_subset; eassumption.
          * intros Hin. eapply Hdis2. constructor; [exact Hin |].
            eapply anf_cvt_exp_subset; [eassumption |].
            eapply anf_cvt_exp_subset; eassumption.
        + intros a b0 Hab Ha Hb.
          eapply preord_var_env_extend_neq.
          * eapply preord_var_env_monotonic with (k := j').
            -- eapply Htransfer2;
                 [eapply Htransfer1; eassumption
                 | intros Hc; apply Ha; eapply anf_cvt_exp_subset; eassumption
                 | intros Hc; apply Hb; eapply anf_cvt_exp_subset; eassumption].
            -- lia.
          * intros Heq. subst. apply Ha.
            eapply anf_cvt_exp_subset; [eassumption |].
            eapply anf_cvt_exp_subset; eassumption.
          * intros Heq. subst. apply Hb.
            eapply anf_cvt_exp_subset; [eassumption |].
            eapply anf_cvt_exp_subset; eassumption. }

    { (* tConst s *)
      inv Hrel1. inv Hrel2. simpl.
      match goal with
      | [H1 : lookup_const cmap ?s = Some ?v1,
         H2 : lookup_const cmap ?s = Some ?v2 |- _] =>
        rewrite H1 in H2; inv H2
      end.
      eapply Hcont.
      - lia.
      - eapply Hglob. exists s. eassumption.
      - assumption.
      - intros; assumption. }

    { (* tConstruct ind c args: comp_ctx_f C_args (Econstr_c x ctag xs Hole_c) *)
      inv Hrel1. inv Hrel2.
      rewrite <- !app_ctx_f_fuse.
      (* Use args helper with X *)
      eapply anf_cvt_args_alpha_from_all;
        [exact X | lia | eassumption | eassumption
        | eapply Disjoint_Included_r; [apply Setminus_Included | exact Hdis1]
        | eapply Disjoint_Included_r; [apply Setminus_Included | exact Hdis2]
        | eapply Disjoint_Included_r; [apply Setminus_Included | exact Hdis_cm1]
        | eapply Disjoint_Included_r; [apply Setminus_Included | exact Hdis_cm2]
        | exact Henv
        | intros v0 Hv0; eapply Hglob; exact Hv0
        |].
      (* Continuation: after args converted, build constructor *)
      intros j rho1' rho2' Hj Hxs Henvvars Htransfer.
      eapply preord_exp_constr_compat.
      - eapply Hprops.
      - eapply Hprops.
      - exact Hxs.
      - intros m0 vs1 vs2 Hlt Hvals.
        eapply Hcont.
        + lia.
        + intros v0 Hg1. rewrite M.gss in Hg1. inv Hg1.
          eexists. split; [rewrite M.gss; reflexivity |].
          rewrite preord_val_eq. simpl. split; [reflexivity | exact Hvals].
        + eapply Forall2_preord_var_env_set.
          * eapply Forall2_preord_var_env_monotonic with (k := j); [lia | exact Henvvars].
          * intros Hin. eapply Hdis1. constructor; [exact Hin | eassumption].
          * intros Hin. eapply Hdis2. constructor; [exact Hin | eassumption].
        + intros a b0 Hab Ha Hb.
          eapply preord_var_env_extend_neq.
          * eapply preord_var_env_monotonic with (k := j).
            -- eapply Htransfer.
               ++ exact Hab.
               ++ intros Hc. apply Ha. inv Hc. assumption.
               ++ intros Hc. apply Hb. inv Hc. assumption.
            -- lia.
          * intros Heq. subst. apply Ha. eassumption.
          * intros Heq. subst. apply Hb. eassumption. }
    { (* tCase (ind,npars) mch brs:
         Efun1_c (Fcons f func_tag [y] (Ecase y pats) Fnil)
                 (comp_ctx_f C_mch (Eletapp_c r f func_tag [x_mch] Hole_c)) *)
      inv Hrel1. inv Hrel2. simpl. rewrite <- !app_ctx_f_fuse.
      (* Efun1_c: case function *)
      eapply preord_exp_fun_compat.
      - eapply Hprops.
      - eapply Hprops.
      - (* IHe for scrutinee mch, in def_funs env with f bound *)
        admit. (* ~80 lines: IHe + letapp + val_fun + branches *) }
    { (* tProj p c: comp_ctx_f C_c (Eproj_c y ctag n x Hole_c) *)
      inv Hrel1. inv Hrel2.
      rewrite <- !app_ctx_f_fuse. simpl.
      (* Use IHe for sub-expression c *)
      eapply IHe; [lia | eassumption | eassumption | assumption | assumption | assumption | assumption | assumption | assumption |].
      (* Continuation: after c is converted, project the field *)
      intros j rho1' rho2' Hj Hvar_c Henv' Htransfer.
      eapply preord_exp_proj_compat.
      - eapply Hprops.
      - eapply Hprops.
      - exact Hvar_c.
      - (* After projection: call Hcont with extended env *)
        intros m' v1 v2 Hlt Hval.
        eapply Hcont.
        + lia.
        + (* r1 ~ r2: both bound to projected values *)
          eapply preord_var_env_extend_eq. exact Hval.
        + (* Forall2 vars: preserved since r1/r2 ∉ vars (r1 ∈ S_mid ⊆ S1, vars ⊥ S1) *)
          eapply Forall2_preord_var_env_set.
          * eapply (Forall2_preord_var_env_monotonic j); [lia | exact Henv'].
          * intros Hin. eapply Hdis1. constructor; [exact Hin |].
            match goal with H : _ \in ?S2 |- _ \in ?S1 =>
              eapply anf_cvt_exp_subset in H; [exact H |]; eassumption end.
          * intros Hin. eapply Hdis2. constructor; [exact Hin |].
            match goal with H : _ \in ?S4 |- _ \in ?S3 =>
              eapply anf_cvt_exp_subset in H; [exact H |]; eassumption end.
        + (* Transfer: chain through IHe's transfer, then extend_neq *)
          intros a b Hab Ha Hb.
          eapply preord_var_env_extend_neq.
          * eapply preord_var_env_monotonic with (k := j).
            -- eapply Htransfer; eassumption.
            -- lia.
          * intros Heq. subst. eapply Ha.
            match goal with H : _ \in ?S2 |- _ =>
              eapply anf_cvt_exp_subset in H; [exact H |]; eassumption end.
          * intros Heq. subst. eapply Hb.
            match goal with H : _ \in ?S4 |- _ =>
              eapply anf_cvt_exp_subset in H; [exact H |]; eassumption end. }
    { (* tFix *) admit. }

    (* tCoFix — impossible *) 1: inv Hrel1.

    { (* tPrim: Eprim_val_c x pv Hole_c *)
      inv Hrel1. inv Hrel2. simpl.
      (* Equate the two pv from trans_prim_val *)
      match goal with
      | [H1 : trans_prim_val ?p = Some ?pv1,
         H2 : trans_prim_val ?p = Some ?pv2 |- _] =>
        rewrite H1 in H2; inv H2
      end.
      eapply preord_exp_prim_val_compat. eapply Hprops. }

    (* tLazy — impossible *) 1: inv Hrel1.
    (* tForce — impossible *) 1: inv Hrel1.
  Admitted.

  Corollary anf_cvt_exp_alpha_equiv_holds :
    forall k, anf_cvt_exp_alpha_equiv k.
  Proof. intros k e. exact (anf_cvt_alpha_equiv k e). Qed.

  Corollary anf_cvt_args_alpha_equiv k :
    forall args, anf_cvt_args_alpha_equiv_for args k.
  Proof. admit. Admitted.

  Corollary anf_cvt_branches_alpha_equiv k :
    forall ind brs n, anf_cvt_branches_alpha_equiv_for ind brs n k.
  Proof. admit. Admitted.

  Corollary anf_cvt_mfix_alpha_equiv k :
    forall mfix, anf_cvt_mfix_alpha_equiv_for mfix k.
  Proof. admit. Admitted.

  Lemma anf_cvt_val_alpha_equiv :
    forall k, anf_cvt_val_alpha_equiv_statement k.
  Proof. admit. Admitted.

End AlphaEquiv.
