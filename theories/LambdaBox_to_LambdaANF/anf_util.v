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


(* ================================================================= *)
(** * Value and Environment Relations                                  *)
(* ================================================================= *)

Section ANF_Val.

  Context (func_tag default_tag : positive)
          (tgm : conId_map)
          (cmap : const_map).

  Let anf_cvt_rel' := anf_cvt_rel func_tag default_tag tgm cmap.

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


(* ================================================================= *)
(** * Alpha-Equivalence                                               *)
(* ================================================================= *)

Section AlphaEquiv.

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
      eapply Hexp; [lia | constructor | exact Hacc | exact Hvar].
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
          intros rho1' rho2' m' Hm' Hpv Hacc' Hvar'.
          inversion Hacc' as [| ? ? ? ? Hhd Htl]; subst.
          eapply Hexp.
          -- lia.
          -- constructor; [exact Hhd | exact Hpv].
          -- exact Htl.
          -- exact Hvar'.
  Qed.


(* ----------------------------------------------------------------- *)
(** ** Alpha-Equivalence Definitions                                  *)
(* ----------------------------------------------------------------- *)

  Let anf_cvt_rel_args' := anf_cvt_rel_args func_tag default_tag tgm cmap.
  Let anf_cvt_rel_mfix' := anf_cvt_rel_mfix func_tag default_tag tgm cmap.
  Let anf_cvt_rel_branches' := anf_cvt_rel_branches func_tag default_tag tgm cmap.

  (** Two ANF conversions of the same term [e], with different fresh
      variables and name mappings, produce [preord_exp]-related results.
      Continuation-passing: given related continuations [e_k1 ~ e_k2],
      the composed contexts [C1|[e_k1]| ~ C2|[e_k2]|] are related. *)
  Definition anf_cvt_exp_alpha_equiv_for (e : EAst.term) k :=
    forall C1 C2 r1 r2 m vars1 vars2 rho1 rho2 S1 S2 S3 S4 e_k1 e_k2,
      (m <= k)%nat ->
      anf_cvt_rel' S1 e vars1 S2 C1 r1 ->
      anf_cvt_rel' S3 e vars2 S4 C2 r2 ->
      Disjoint _ (FromList vars1) S1 ->
      Disjoint _ (FromList vars2) S3 ->
      Forall2 (preord_var_env cenv PG m rho1 rho2) vars1 vars2 ->
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
      Forall2 (preord_var_env cenv PG m rho1 rho2) vars1 vars2 ->
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
      Disjoint _ (FromList fnames1) (FromList outer_vars1) ->
      Disjoint _ (FromList fnames2) (FromList outer_vars2) ->
      Forall2 (preord_var_env cenv PG m rho1 rho2) outer_vars1 outer_vars2 ->
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
      Forall2 (preord_var_env cenv PG m rho1 rho2) vars1 vars2 ->
      preord_var_env cenv PG m rho1 rho2 y1 y2 ->
      preord_exp cenv P1 PG m (Ecase y1 pats1, rho1) (Ecase y2 pats2, rho2).

  (* Value-level alpha-equiv *)
  Definition anf_cvt_val_alpha_equiv_statement k :=
    forall v v1 v2,
      anf_val_rel' v v1 -> anf_val_rel' v v2 ->
      preord_val cenv PG k v1 v2.


(* ----------------------------------------------------------------- *)
(** ** Environment Alpha-Equivalence                                  *)
(* ----------------------------------------------------------------- *)

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

(* ----------------------------------------------------------------- *)
(** ** Term-Level Alpha-Equiv for Lists                               *)
(* ----------------------------------------------------------------- *)

  (* Derives args alpha-equiv assuming exp alpha-equiv for each element *)
  Lemma anf_cvt_args_alpha_from_all k args :
    All (fun t => anf_cvt_exp_alpha_equiv_for t k) args ->
    anf_cvt_args_alpha_equiv_for args k.
  Proof. admit. Admitted.

  (* Derives branches alpha-equiv assuming exp alpha-equiv for each branch body *)
  Lemma anf_cvt_branches_alpha_from_all k ind brs n :
    All (fun br : list name * EAst.term =>
           anf_cvt_exp_alpha_equiv_for (snd br) k) brs ->
    anf_cvt_branches_alpha_equiv_for ind brs n k.
  Proof. admit. Admitted.

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
(** ** Main Theorem                                                   *)
(* ----------------------------------------------------------------- *)

  Lemma anf_cvt_alpha_equiv :
    forall k e, anf_cvt_exp_alpha_equiv_for e k.
  Proof.
    intros k. induction k as [k IHk] using lt_wf_rec1.
    intros e. induction e using term_ind_fix_body;
    unfold anf_cvt_exp_alpha_equiv_for;
    intros C1 C2 r1 r2 m vars1 vars2 rho1 rho2 S1 S2 S3 S4 e_k1 e_k2
           Hm Hrel1 Hrel2 Hdis1 Hdis2 Henv Hcont;
    inv Hrel1;
    try (inv Hrel2);
    (* Simple Hole_c cases (tRel, tConst) *)
    try (simpl;
         eapply Hcont; [lia | | assumption |];
         [| intros; assumption];
         match goal with
         | [H1 : nth_error vars1 ?n = Some r1,
            H2 : nth_error vars2 ?n = Some r2,
            Henv : Forall2 _ vars1 vars2 |- _] =>
           eapply Forall2_nth_error in Henv; [| exact H1 | exact H2]; exact Henv
         end).
    (* tBox *) - admit.
    (* tLambda *) - admit.
    (* tLetIn *) - admit.
    (* tApp *) - admit.
    (* tConstruct *) - admit. (* uses anf_cvt_args_alpha_from_all with X *)
    (* tCase *) - admit. (* uses anf_cvt_branches_alpha_from_all with X *)
    (* tProj *) - admit.
    (* tFix *) - admit. (* uses anf_cvt_mfix_alpha_from_all with X and IHk *)
    (* tPrim *) - admit.
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

End AlphaEquiv.
