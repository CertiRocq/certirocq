(* Utility definitions and lemmas for ANF correctness proof.
   Defines source value type, value relations between EAst evaluation
   results and LambdaANF values. *)

(** Stdlib *)
From Stdlib Require Import ZArith.ZArith Lists.List Arith Ensembles
     Relations.Relation_Definitions micromega.Lia.

(** MetaRocq *)
From MetaRocq.Erasure Require Import EAst EGlobalEnv EAstUtils.
From MetaRocq.Common Require Import BasicAst Kernames.

(** CompCert *)
From compcert Require lib.Maps lib.Coqlib.

(** CertiRocq *)
From MetaRocq.Utils Require Import All_Forall.
From CertiRocq.LambdaANF Require Import
  cps ctx eval Ensembles_util logical_relations alpha_conv
  rename List_util identifiers algebra tactics functions.
From CertiRocq.LambdaBox_to_LambdaANF Require Import common ANF fuel_sem.

Import ListNotations.


(** * ANF Value Relation *)

Section ANF_Val.

  Context
    (* LambdaANF tags *)
    (func_tag default_tag : positive)
    (* constructor tag map *)
    (cnstrs : conId_map)
    (* global constant map: kername → LambdaANF variable *)
    (cmap : const_map)
    (* source fuel and trace resource instances *)
    (Hf Ht : @LambdaBox_resource nat)
    (* MetaRocq erased global context *)
    (Σ : EAst.global_context)
    (* all constant bodies in Σ evaluate to a value *)
    (global_env_evaluates :
      forall k decl body,
        declared_constant Σ k decl ->
        decl.(EAst.cst_body) = Some body ->
        exists src_v f t, @eval_env_fuel _ Hf Ht Σ [] body (fuel_sem.Val src_v) f t).

  (** Shorthand for the relational spec, partially applied with tags *)
  Definition anf_cvt_rel' (tgm : conId_map) (cmap : const_map) :=
    ANF.anf_cvt_rel func_tag default_tag tgm cmap.
  Definition anf_cvt_rel_args' (tgm : conId_map) (cmap : const_map) :=
    ANF.anf_cvt_rel_args func_tag default_tag tgm cmap.
  Definition anf_cvt_rel_mfix' (tgm : conId_map) (cmap : const_map) :=
    ANF.anf_cvt_rel_mfix func_tag default_tag tgm cmap.
  Definition anf_cvt_rel_branches' (tgm : conId_map) (cmap : const_map) :=
    ANF.anf_cvt_rel_branches func_tag default_tag tgm cmap.

  Definition cmap_vars : Ensemble var :=
    fun v => exists k, lookup_const cmap k = Some v.

  (** Image of a kername set under [cmap] *)
  Definition cmap_vars_of (D : kername -> Prop) : Ensemble var :=
    fun v => exists k, D k /\ lookup_const cmap k = Some v.


  (** ** Environment and consistency relations *)

  Definition anf_env_rel' (P : value -> val -> Prop) (vn : list var)
             (vs : list value) (rho : M.t val) :=
    Forall2 (fun v x => exists v', M.get x rho = Some v' /\ P v v') vs vn.

  Definition env_consistent (vn : list var) (rho : list value) : Prop :=
    forall i j x,
      nth_error vn i = Some x ->
      nth_error vn j = Some x ->
      nth_error rho i = nth_error rho j.


  (** ** Global environment relation *)

  (** Relates cmap variables to their ANF values in a target environment,
      restricted to a set [D] of kernames. Parametric in the value relation
      [val_rel] so it can be used inside [anf_val_rel] without circularity. *)
  Definition global_env_rel (val_rel : value -> val -> Prop)
             (D : kername -> Prop) (rho : M.t val) : Prop :=
    forall k v,
      D k ->
      lookup_const cmap k = Some v ->
      exists decl body anf_v,
        declared_constant Σ k decl /\
        decl.(EAst.cst_body) = Some body /\
        M.get v rho = Some anf_v /\
        (forall src_v f t,
           @eval_env_fuel _ Hf Ht Σ [] body (fuel_sem.Val src_v) f t ->
           val_rel src_v anf_v).


  (** ** Fix relation *)

  Inductive anf_fix_rel (fnames : list var) (names : list var)
    : Ensemble var -> list var -> list (EAst.def EAst.term) -> fundefs -> Ensemble var -> Prop :=
  | anf_fix_fnil :
      forall S, anf_fix_rel fnames names S [] [] Fnil S
  | anf_fix_fcons :
      forall S1 S1' S2 S2' S3 fnames' d mfix' C1 r1 na e1 f x Bs,
        d.(EAst.dbody) = EAst.tLambda na e1 ->
        Disjoint _ S1 (FromList fnames :|: FromList names) ->
        x \in S1 ->
        S1' \subset S1 \\ [set x] ->
        S2' \subset S2 ->

        anf_cvt_rel' cnstrs cmap S1' e1 (x :: List.rev fnames ++ names) S2 C1 r1 ->

        anf_fix_rel fnames names S2' fnames' mfix' Bs S3 ->
        anf_fix_rel fnames names S1 (f :: fnames') (d :: mfix')
                    (Fcons f func_tag [x] (C1 |[ Ehalt r1 ]|) Bs) S3.


  (** Global deps of a mutual fixpoint *)
  Definition mfix_global_deps (mfix : list (EAst.def EAst.term)) : KernameSet.t :=
    List.fold_left
      (fun acc d => KernameSet.union (term_global_deps d.(EAst.dbody)) acc)
      mfix KernameSet.empty.

  (** ** Value relation *)

  Inductive anf_val_rel : value -> val -> Prop :=
  | anf_rel_Con :
      forall vs vs' dc c_tag,
        Forall2 (fun v v' => anf_val_rel v v') vs vs' ->
        dcon_to_tag default_tag dc cnstrs = c_tag ->
        anf_val_rel (Con_v dc vs) (Vconstr c_tag vs')
  | anf_rel_Clos :
      forall vs rho names na x f e C1 r1 S1 S2,
        anf_env_rel' anf_val_rel names vs rho ->

        env_consistent names vs ->

        Disjoint var (x |: (f |: FromList names)) S1 ->

        ~ x \in f |: FromList names ->
        ~ f \in FromList names ->

        (* cmap variables are disjoint from closure variables and fresh set *)
        Disjoint _ cmap_vars (x |: (f |: FromList names)) ->
        Disjoint _ cmap_vars S1 ->

        global_env_rel anf_val_rel (fun k => KernameSet.In k (term_global_deps e)) rho ->

        anf_cvt_rel' cnstrs cmap S1 e (x :: names) S2 C1 r1 ->
        anf_val_rel (Clos_v vs na e)
                    (Vfun rho (Fcons f func_tag [x] (C1 |[ Ehalt r1 ]|) Fnil) f)
  | anf_rel_ClosFix :
      forall S1 S2 names fnames vs rho mfix Bs n f,
        anf_env_rel' anf_val_rel names vs rho ->

        env_consistent names vs ->
        NoDup fnames ->

        Disjoint _ (FromList names :|: FromList fnames) S1 ->
        Disjoint _ (FromList names) (FromList fnames) ->

        Disjoint _ cmap_vars (FromList names :|: FromList fnames) ->
        Disjoint _ cmap_vars S1 ->

        nth_error fnames n = Some f ->

        global_env_rel anf_val_rel (fun k => KernameSet.In k (mfix_global_deps mfix)) rho ->

        anf_fix_rel fnames names S1 fnames mfix Bs S2 ->

        anf_val_rel (ClosFix_v vs mfix n) (Vfun rho Bs f).


  Definition anf_env_rel : list var -> list value -> M.t val -> Prop :=
    anf_env_rel' anf_val_rel.


  (** ** Fix relation helper lemmas *)

  Lemma anf_fix_rel_fnames_length fnames names S1 fnames_list mfix Bs S2 :
    anf_fix_rel fnames names S1 fnames_list mfix Bs S2 ->
    List.length fnames_list = List.length mfix.
  Proof.
    intros Hrel. induction Hrel; simpl; congruence.
  Qed.

  (** Extract a specific function definition from a fix relation bundle.
      Given the idx-th function name and the idx-th source body (which must
      be a lambda), [find_def] locates the corresponding ANF function. *)
  Lemma anf_fix_rel_find_def :
    forall fnames0 names0 S1 fnames_list mfix Bs S2 idx f na e_body d,
      anf_fix_rel fnames0 names0 S1 fnames_list mfix Bs S2 ->
      nth_error fnames_list idx = Some f ->
      nth_error mfix idx = Some d ->
      d.(EAst.dbody) = EAst.tLambda na e_body ->
      NoDup fnames_list ->
      exists x_pc C_body r_body S_body1 S_body2,
        find_def f Bs = Some (func_tag, [x_pc], C_body |[ Ehalt r_body ]|) /\
        anf_cvt_rel' cnstrs cmap S_body1 e_body
                     (x_pc :: List.rev fnames0 ++ names0) S_body2 C_body r_body.
  Proof.
    intros fnames0 names0 S1 fnames_list mfix Bs S2 idx f na e_body d
      Hrel Hnth_f Hnth_d Hbody Hnd.
    revert idx f na e_body d Hnth_f Hnth_d Hbody Hnd.
    induction Hrel; intros idx0 f0 na0 e_body0 d0 Hnth_f Hnth_d Hbody0 Hnd.
    - (* anf_fix_fnil *)
      destruct idx0; discriminate.
    - (* anf_fix_fcons *)
      destruct idx0 as [ | idx'].
      + (* idx = 0: this function *)
        simpl in Hnth_f. inv Hnth_f.
        simpl in Hnth_d. inv Hnth_d.
        rewrite Hbody0 in H. inv H.
        do 5 eexists. split.
        * simpl. destruct (M.elt_eq f0 f0); [ reflexivity | congruence ].
        * eassumption.
      + (* idx = S idx': later function *)
        simpl in Hnth_f. simpl in Hnth_d.
        inversion Hnd as [ | ? ? Hnotin Hnd']; subst.
        edestruct IHHrel as (x_pc' & C_body' & r_body' & S_body1' & S_body2' & Hfind' & Hcvt').
        * exact Hnth_f.
        * exact Hnth_d.
        * exact Hbody0.
        * assumption.
        * do 5 eexists. split.
          -- simpl. destruct (M.elt_eq f0 f) as [Heq | Hneq].
             ++ exfalso. subst. apply Hnotin. eapply nth_error_In. exact Hnth_f.
             ++ exact Hfind'.
          -- exact Hcvt'.
  Qed.

  (** Extended version that also provides the disjointness and freshness
      properties for the function's parameter variable. *)
  Lemma anf_fix_rel_find_def_ext :
    forall fnames0 names0 S1 fnames_list mfix Bs S2 idx f na e_body d,
      anf_fix_rel fnames0 names0 S1 fnames_list mfix Bs S2 ->
      nth_error fnames_list idx = Some f ->
      nth_error mfix idx = Some d ->
      d.(EAst.dbody) = EAst.tLambda na e_body ->
      NoDup fnames_list ->
      exists x_pc C_body r_body S_body1 S_body2,
        find_def f Bs = Some (func_tag, [x_pc], C_body |[ Ehalt r_body ]|) /\
        anf_cvt_rel' cnstrs cmap S_body1 e_body
                     (x_pc :: List.rev fnames0 ++ names0) S_body2 C_body r_body /\
        Disjoint _ (x_pc |: (FromList fnames0 :|: FromList names0)) S_body1 /\
        ~ x_pc \in (FromList fnames0 :|: FromList names0).
  Proof.
    intros fnames0 names0 S1 fnames_list mfix Bs S2 idx f na e_body d
      Hrel Hnth_f Hnth_d Hbody0 Hnd.
    revert idx f na e_body d Hnth_f Hnth_d Hbody0 Hnd.
    induction Hrel; intros idx0 f0 na0 e_body0 d0 Hnth_f Hnth_d Hbody0 Hnd.
    - destruct idx0; discriminate.
    - destruct idx0 as [ | idx'].
      + simpl in Hnth_f. inv Hnth_f.
        simpl in Hnth_d. inv Hnth_d.
        rewrite Hbody0 in H. inv H.
        do 5 eexists. split; [ | split; [ | split ] ].
        * simpl. destruct (M.elt_eq f0 f0); [ reflexivity | congruence ].
        * eassumption.
        * eapply Disjoint_Included_r; [ eassumption | ].
          eapply Union_Disjoint_l.
          -- eapply Disjoint_Singleton_l. intros Hc. destruct Hc as [_ Hc]. apply Hc. constructor.
          -- eapply Disjoint_Included_r; [ eapply Setminus_Included | ].
             eapply Disjoint_sym. assumption.
        * intros Habs.
          match goal with
          | [ Hdis : Disjoint _ _ (_ :|: _),
              Hin : _ \in _ |- _ ] =>
            eapply Hdis; constructor; [ exact Hin | exact Habs ]
          end.
      + simpl in Hnth_f. simpl in Hnth_d.
        inversion Hnd as [ | ? ? Hnotin Hnd']; subst.
        edestruct IHHrel as (x_pc' & C_body' & r_body' & S_body1' & S_body2' &
                              Hfind' & Hcvt' & Hdis' & Hfresh').
        * exact Hnth_f.
        * exact Hnth_d.
        * exact Hbody0.
        * assumption.
        * do 5 eexists. split; [ | split; [ | split ] ].
          -- simpl. destruct (M.elt_eq f0 f) as [Heq | Hneq].
             ++ exfalso. subst. apply Hnotin. eapply nth_error_In. exact Hnth_f.
             ++ exact Hfind'.
          -- exact Hcvt'.
          -- exact Hdis'.
          -- exact Hfresh'.
  Qed.

  (** Given [anf_fix_rel] and a valid function-name index, extract the
      corresponding [mfix] entry and show its body is a lambda. *)
  Lemma anf_fix_rel_nth_lambda :
    forall fnames0 names0 S1 fnames_list mfix Bs S2 idx f,
      anf_fix_rel fnames0 names0 S1 fnames_list mfix Bs S2 ->
      nth_error fnames_list idx = Some f ->
      exists d na e_body,
        nth_error mfix idx = Some d /\
        d.(EAst.dbody) = EAst.tLambda na e_body.
  Proof.
    intros fnames0 names0 S1 fnames_list mfix Bs S2 idx f Hrel.
    revert idx f.
    induction Hrel; intros idx0 f0 Hnth.
    - destruct idx0; discriminate.
    - destruct idx0 as [ | idx'].
      + simpl in Hnth. inv Hnth. do 3 eexists. split; [ reflexivity | eassumption ].
      + simpl in Hnth. edestruct IHHrel as (d' & na' & e_body' & Hm & Hb).
        * exact Hnth.
        * do 3 eexists. split; [ simpl; exact Hm | exact Hb ].
  Qed.

  (** [name_in_fundefs] of a bundle built by [anf_fix_rel] equals [FromList]
      of the function-name list. *)
  Lemma anf_fix_rel_name_in_fundefs :
    forall fnames0 names0 S1 fnames_list mfix Bs S2,
      anf_fix_rel fnames0 names0 S1 fnames_list mfix Bs S2 ->
      Same_set _ (name_in_fundefs Bs) (FromList fnames_list).
  Proof.
    intros fnames0 names0 S1 fnames_list mfix Bs S2 Hrel.
    induction Hrel.
    - simpl. split; intros z Hz; inv Hz.
    - simpl. rewrite FromList_cons.
      destruct IHHrel as [Hsub1 Hsub2]. split; intros z Hz; inv Hz;
        try (left; assumption);
        try (left; constructor);
        try (right; (apply Hsub1 + apply Hsub2); assumption).
  Qed.

  (** ** Subset lemma: ANF conversion shrinks the fresh set *)

  Lemma anf_cvt_exp_subset S e vn S' C x :
    anf_cvt_rel' cnstrs cmap S e vn S' C x -> S' \subset S.
  Proof.
    unfold anf_cvt_rel'.
    intros H.
    eapply (ANF.anf_cvt_rel_ind' func_tag default_tag cnstrs cmap
      (fun S e vn S' C x => S' \subset S)
      (fun S args vn S' C xs => S' \subset S)
      (fun S mfix vn fnames S' fdefs => S' \subset S)
      (fun S ind brs n vn r S' pats => S' \subset S));
    try eassumption; clear; intros.
    (* anf_Rel *)
    - eapply Included_refl.
    (* anf_Lam *)
    - eapply Included_trans; [ eassumption | ].
      eapply Included_trans; eapply Setminus_Included.
    (* anf_App *)
    - eapply Included_trans; [ eapply Setminus_Included | ].
      eapply Included_trans; eassumption.
    (* anf_Construct *)
    - eapply Included_trans; [ eassumption | eapply Setminus_Included ].
    (* anf_LetIn *)
    - eapply Included_trans; eassumption.
    (* anf_Case *)
    - eapply Included_trans; [ eapply Setminus_Included | ].
      eapply Included_trans; [ eassumption | ].
      eapply Included_trans; [ eassumption | ].
      eapply Included_trans; eapply Setminus_Included.
    (* anf_Fix *)
    - eapply Included_trans; [ eassumption | eapply Setminus_Included ].
    (* anf_Box *)
    - eapply Setminus_Included.
    (* anf_Const *)
    - eapply Included_refl.
    (* anf_Proj *)
    - eapply Included_trans; [ eapply Setminus_Included | eassumption ].
    (* anf_Prim *)
    - eapply Setminus_Included.
    (* anf_Args_nil *)
    - eapply Included_refl.
    (* anf_Args_cons *)
    - eapply Included_trans; eassumption.
    (* anf_Mfix_nil *)
    - eapply Included_refl.
    (* anf_Mfix_cons *)
    - eapply Included_trans; [ eassumption | ].
      eapply Included_trans; [ eassumption | eapply Setminus_Included ].
    (* anf_Branches_nil *)
    - eapply Included_refl.
    (* anf_Branches_cons:
       IH_branches: S2 ⊆ S1, IH_body: S3 ⊆ S2 \\ FromList vars.
       Need: S3 ⊆ S1. *)
    - eapply Included_trans; [ eassumption | ].
      eapply Included_trans; [ eapply Setminus_Included | eassumption ].
  Qed.

  Lemma anf_cvt_args_subset S args vn S' C xs :
    anf_cvt_rel_args' cnstrs cmap S args vn S' C xs -> S' \subset S.
  Proof.
    unfold anf_cvt_rel_args'. intros H.
    induction H.
    - eapply Included_refl.
    - eapply Included_trans; [ eassumption | ].
      eapply anf_cvt_exp_subset. eassumption.
  Qed.

  Lemma anf_cvt_mfix_subset S mfix vn fnames S' fdefs :
    anf_cvt_rel_mfix' cnstrs cmap S mfix vn fnames S' fdefs -> S' \subset S.
  Proof.
    unfold anf_cvt_rel_mfix'. intros H.
    induction H.
    - eapply Included_refl.
    - eapply Included_trans; [ eassumption | ].
      eapply Included_trans; [ eapply anf_cvt_exp_subset; eassumption | ].
      eapply Setminus_Included.
  Qed.

  Lemma anf_cvt_branches_subset S ind brs n vn r S' pats :
    anf_cvt_rel_branches' cnstrs cmap S ind brs n vn r S' pats -> S' \subset S.
  Proof.
    unfold anf_cvt_rel_branches'. intros H.
    induction H.
    - eapply Included_refl.
    - eapply Included_trans; [ eapply anf_cvt_exp_subset; eassumption | ].
      eapply Included_trans; [ eapply Setminus_Included | eassumption ].
  Qed.


  (** The outer fresh set in anf_fix_rel is a superset of S2 *)
  Lemma anf_fix_rel_subset fnames0 names0 S1 fnames_list mfix Bs S2 :
    anf_fix_rel fnames0 names0 S1 fnames_list mfix Bs S2 -> S2 \subset S1.
  Proof.
    intros Hrel. induction Hrel.
    - eapply Included_refl.
    - eapply Included_trans; [ eassumption | ].
      eapply Included_trans; [ eassumption | ].
      eapply Included_trans; [ eapply anf_cvt_exp_subset; eassumption | ].
      eapply Included_trans; [ eassumption | ].
      eapply Setminus_Included.
  Qed.

  (** Extended version of anf_fix_rel_find_def_ext that also provides
      cmap disjointness for the body's fresh set.
      (Defined after anf_cvt_exp_subset so we can track the subset chain.) *)
  Lemma anf_fix_rel_find_def_full :
    forall fnames0 names0 S1 fnames_list mfix Bs S2 idx f na e_body d,
      anf_fix_rel fnames0 names0 S1 fnames_list mfix Bs S2 ->
      nth_error fnames_list idx = Some f ->
      nth_error mfix idx = Some d ->
      d.(EAst.dbody) = EAst.tLambda na e_body ->
      NoDup fnames_list ->
      Disjoint _ cmap_vars S1 ->
      exists x_pc C_body r_body S_body1 S_body2,
        find_def f Bs = Some (func_tag, [x_pc], C_body |[ Ehalt r_body ]|) /\
        anf_cvt_rel' cnstrs cmap S_body1 e_body
                     (x_pc :: List.rev fnames0 ++ names0) S_body2 C_body r_body /\
        Disjoint _ (x_pc |: (FromList fnames0 :|: FromList names0)) S_body1 /\
        ~ x_pc \in (FromList fnames0 :|: FromList names0) /\
        Disjoint _ cmap_vars S_body1 /\
        ~ x_pc \in cmap_vars.
  Proof.
    intros fnames0 names0 S1 fnames_list mfix Bs S2 idx f na e_body d
      Hrel Hnth_f Hnth_d Hbody0 Hnd Hdis_cm.
    revert idx f na e_body d Hnth_f Hnth_d Hbody0 Hnd Hdis_cm.
    induction Hrel; intros idx0 f0 na0 e_body0 d0 Hnth_f Hnth_d Hbody0 Hnd Hdis_cm.
    - destruct idx0; discriminate.
    - destruct idx0 as [ | idx'].
      + simpl in Hnth_f. inv Hnth_f.
        simpl in Hnth_d. inv Hnth_d.
        rewrite Hbody0 in H. inv H.
        do 5 eexists. split; [ | split; [ | split; [ | split; [ | split ] ] ] ].
        * simpl. destruct (M.elt_eq f0 f0); [ reflexivity | congruence ].
        * eassumption.
        * eapply Disjoint_Included_r; [ eassumption | ].
          eapply Union_Disjoint_l.
          -- eapply Disjoint_Singleton_l. intros Hc. destruct Hc as [_ Hc]. apply Hc. constructor.
          -- eapply Disjoint_Included_r; [ eapply Setminus_Included | ].
             eapply Disjoint_sym. assumption.
        * intros Habs.
          match goal with
          | [ Hdis : Disjoint _ _ (_ :|: _),
              Hin : _ \in _ |- _ ] =>
            eapply Hdis; constructor; [ exact Hin | exact Habs ]
          end.
        * eapply Disjoint_Included_r; [ | exact Hdis_cm ].
          eapply Included_trans; [ eassumption | eapply Setminus_Included ].
        * (* ~ x ∈ cmap_vars: x ∈ S1 and Disjoint cmap_vars S1 *)
          intros Hcm. eapply Hdis_cm. constructor; eassumption.
      + simpl in Hnth_f. simpl in Hnth_d.
        inversion Hnd as [ | ? ? Hnotin Hnd']; subst.
        edestruct IHHrel as (x_pc' & C_body' & r_body' & S_body1' & S_body2' &
                              Hfind' & Hcvt' & Hdis' & Hfresh' & Hdis_cm' & Hcm_xpc').
        * exact Hnth_f.
        * exact Hnth_d.
        * exact Hbody0.
        * assumption.
        * eapply Disjoint_Included_r; [ | exact Hdis_cm ].
          eapply Included_trans; [ eassumption | ].
          eapply Included_trans; [ eapply anf_cvt_exp_subset; eassumption | ].
          eapply Included_trans; [ eassumption | eapply Setminus_Included ].
        * do 5 eexists. split; [ | split; [ | split; [ | split; [ | split ] ] ] ].
          -- simpl. destruct (M.elt_eq f0 f) as [Heq | Hneq].
             ++ exfalso. subst. apply Hnotin. eapply nth_error_In. exact Hnth_f.
             ++ exact Hfind'.
          -- exact Hcvt'.
          -- exact Hdis'.
          -- exact Hfresh'.
          -- exact Hdis_cm'.
          -- exact Hcm_xpc'.
  Qed.

  (** ** Result variable is consumed from S *)

  Lemma anf_cvt_result_not_in_output S e vn S' C x :
    anf_cvt_rel' cnstrs cmap S e vn S' C x ->
    Disjoint _ (FromList vn) S ->
    Disjoint _ cmap_vars S ->
    ~ x \in S'.
  Proof.
    unfold anf_cvt_rel'. intros Hcvt Hdis Hdis_cm.
    induction Hcvt; intros Hin.
    - (* anf_Rel *)
      eapply Hdis. constructor; [ eapply nth_error_In; eassumption | exact Hin ].
    - (* anf_Lam *)
      assert (Hsub : S' \subset S \\ [set x1] \\ [set f])
        by (eapply anf_cvt_exp_subset; eassumption).
      apply Hsub in Hin. destruct Hin as [_ Habs]. apply Habs. constructor.
    - (* anf_App *)
      inv Hin. eauto.
    - (* anf_Construct *)
      assert (Hsub : S2 \subset S1 \\ [set x])
        by (eapply anf_cvt_args_subset; eassumption).
      apply Hsub in Hin. destruct Hin as [_ Habs]. apply Habs. constructor.
    - (* anf_LetIn *)
      eapply IHHcvt2; [ | | exact Hin ].
      + rewrite FromList_cons. eapply Union_Disjoint_l.
        * eapply Disjoint_Singleton_l.
          eapply IHHcvt1; eassumption.
        * eapply Disjoint_Included_r; [ eapply anf_cvt_exp_subset; eassumption | exact Hdis ].
      + eapply Disjoint_Included_r; [ eapply anf_cvt_exp_subset; eassumption | exact Hdis_cm ].
    - (* anf_Case *)
      inv Hin. eauto.
    - (* anf_Fix *)
      assert (Hsub : S2 \subset S1 \\ FromList fnames)
        by (eapply anf_cvt_mfix_subset; eassumption).
      apply Hsub in Hin. destruct Hin as [_ Habs].
      apply Habs. eapply nth_error_In. eassumption.
    - (* anf_Box *)
      inv Hin. eauto.
    - (* anf_Const: x = v from cmap, S' = S *)
      eapply Hdis_cm. constructor; [ | exact Hin ].
      match goal with
      | [ Hl : lookup_const _ ?kn = Some _ |- _ ] => exists kn; exact Hl
      end.
    - (* anf_Proj *)
      inv Hin. eauto.
    - (* anf_Prim *)
      inv Hin. eauto.
  Qed.


  (** ** Lookup in related environments *)

  Lemma Forall2_nth_error_l {A B} (R : A -> B -> Prop) l1 l2 k a :
    Forall2 R l1 l2 ->
    nth_error l1 k = Some a ->
    exists b, nth_error l2 k = Some b /\ R a b.
  Proof.
    intros HF. revert k. induction HF; intros k Hn.
    - destruct k; discriminate.
    - destruct k as [ | k']; simpl in Hn.
      + inv Hn. eexists. split; [reflexivity | assumption].
      + eapply IHHF. exact Hn.
  Qed.

  Lemma anf_env_rel_nth_error vnames vs rho n v x :
    anf_env_rel' anf_val_rel vnames vs rho ->
    nth_error vs n = Some v ->
    nth_error vnames n = Some x ->
    exists v', M.get x rho = Some v' /\ anf_val_rel v v'.
  Proof.
    revert vnames n. induction vs as [ | v0 vs' IH]; intros vnames n Henv Hnth_v Hnth_x.
    - destruct n; discriminate.
    - inv Henv. destruct n as [ | n'].
      + simpl in Hnth_v, Hnth_x. inv Hnth_v. inv Hnth_x.
        match goal with
        | [ H : exists _, _ |- _ ] => destruct H as [v' [Hget Hrel]]
        end.
        eexists. split; eassumption.
      + simpl in Hnth_v, Hnth_x.
        eapply IH; eassumption.
  Qed.

  Lemma anf_env_rel_length vnames vs rho :
    anf_env_rel' anf_val_rel vnames vs rho ->
    List.length vnames = List.length vs.
  Proof.
    intros H. symmetry. eapply Forall2_length. exact H.
  Qed.

  (** ** Helper: all_fun_name agrees with fnames *)

  Lemma anf_cvt_mfix_all_fun_name S mfix vn fnames S' fdefs :
    anf_cvt_rel_mfix' cnstrs cmap S mfix vn fnames S' fdefs ->
    all_fun_name fdefs = fnames.
  Proof.
    unfold anf_cvt_rel_mfix'. intros H.
    induction H.
    - reflexivity.
    - simpl. f_equal. exact IHanf_cvt_rel_mfix.
  Qed.

  (** ** Helper: extract find_def from anf_cvt_rel_mfix *)

  Lemma anf_cvt_mfix_find_def S mfix vn fnames S' fdefs :
    anf_cvt_rel_mfix' cnstrs cmap S mfix vn fnames S' fdefs ->
    NoDup fnames ->
    forall i fi,
      nth_error fnames i = Some fi ->
      exists d na e_body xi C_body ri Si1 Si2,
        nth_error mfix i = Some d /\
        d.(EAst.dbody) = EAst.tLambda na e_body /\
        find_def fi fdefs = Some (func_tag, [xi], C_body |[ Ehalt ri ]|) /\
        anf_cvt_rel' cnstrs cmap (Si1 \\ [set xi]) e_body (xi :: vn) Si2 C_body ri /\
        xi \in Si1 /\ Si1 \subset S.
  Proof.
    unfold anf_cvt_rel_mfix', anf_cvt_rel'. intros Hrel Hnd.
    induction Hrel; intros i fi Hnth.
    - destruct i; discriminate.
    - inversion Hnd as [ | ? ? Hnotin Hnd']; subst.
      destruct i as [ | i'].
      + simpl in Hnth. inv Hnth.
        do 8 eexists. split; [ | split; [ | split; [ | split; [ | split ] ] ] ].
        * reflexivity.
        * eassumption.
        * simpl. rewrite Coqlib.peq_true. reflexivity.
        * eassumption.
        * eassumption.
        * eapply Included_refl.
      + simpl in Hnth.
        edestruct IHHrel as (d' & na' & e_body' & xi' & C_body' & ri' & Si1' & Si2' &
                              Hmfix & Hbody' & Hfind & Hcvt_body & Hxi & Hsub).
        * eassumption.
        * exact Hnth.
        * do 8 eexists. split; [ | split; [ | split; [ | split; [ | split ] ] ] ].
          -- simpl. exact Hmfix.
          -- exact Hbody'.
          -- simpl.
             destruct (M.elt_eq fi f_name) as [Heq | Hneq].
             ++ exfalso. subst. apply Hnotin. eapply nth_error_In. exact Hnth.
             ++ exact Hfind.
          -- exact Hcvt_body.
          -- exact Hxi.
          -- eapply Included_trans; [ exact Hsub | ].
             eapply Included_trans; [ eapply anf_cvt_exp_subset; eassumption | ].
             eapply Setminus_Included.
  Qed.

  (** ** Helper: branches ctor_tag agreement *)

  Lemma anf_cvt_branches_ctor_tag S1 S2 S3 S4 ind brs n vn1 vn2 y1 y2 pats1 pats2 :
    anf_cvt_rel_branches' cnstrs cmap S1 ind brs n vn1 y1 S2 pats1 ->
    anf_cvt_rel_branches' cnstrs cmap S3 ind brs n vn2 y2 S4 pats2 ->
    Forall2 (fun p p' : ctor_tag * exp => fst p = fst p') pats1 pats2.
  Proof.
    unfold anf_cvt_rel_branches'.
    revert S1 S2 S3 S4 n vn1 vn2 y1 y2 pats1 pats2.
    induction brs; intros S1 S2 S3 S4 n vn1 vn2 y1 y2 pats1 pats2 Hrel1 Hrel2.
    - inv Hrel1; inv Hrel2; constructor.
    - destruct a. inv Hrel1; inv Hrel2. constructor.
      + simpl. congruence.
      + eapply IHbrs; eassumption.
  Qed.

  (** ** Utility: Forall2 from pointwise nth_error *)

  Lemma Forall2_from_nth_error {A B : Type} (R : A -> B -> Prop)
        (l1 : list A) (l2 : list B) :
      Datatypes.length l1 = Datatypes.length l2 ->
      (forall k a b, nth_error l1 k = Some a -> nth_error l2 k = Some b -> R a b) ->
      Forall2 R l1 l2.
  Proof.
    revert l2. induction l1 as [ | x xs IH]; intros l2 Hlen Hnth.
    - destruct l2; [constructor | simpl in Hlen; discriminate].
    - destruct l2 as [ | y ys]; [simpl in Hlen; discriminate | ].
      constructor.
      + apply (Hnth 0%nat); reflexivity.
      + apply IH.
        * simpl in Hlen. lia.
        * intros k a b Hk1 Hk2. apply (Hnth (S k)); assumption.
  Qed.


  (** ** KernameSet fold_left helpers *)

  Lemma fold_left_kset_union_base {A} (f : A -> KernameSet.t) (l : list A) (base : KernameSet.t) k :
    KernameSet.In k base ->
    KernameSet.In k (List.fold_left (fun acc x => KernameSet.union (f x) acc) l base).
  Proof.
    revert base. induction l; simpl; intros base Hin.
    - exact Hin.
    - apply IHl. apply KernameSet.union_spec. right. exact Hin.
  Qed.

  Lemma fold_left_kset_union_elem {A} (f : A -> KernameSet.t) (l : list A) (base : KernameSet.t) x k :
    List.In x l ->
    KernameSet.In k (f x) ->
    KernameSet.In k (List.fold_left (fun acc x => KernameSet.union (f x) acc) l base).
  Proof.
    revert base. induction l; simpl; intros base Hin Hk.
    - destruct Hin as [].
    - destruct Hin as [<- | Hin].
      + apply fold_left_kset_union_base. apply KernameSet.union_spec. left. exact Hk.
      + apply IHl; assumption.
  Qed.

  Lemma fold_left_kset_union_mono {A} (f : A -> KernameSet.t) (l : list A)
    (base1 base2 : KernameSet.t) :
    (forall k, KernameSet.In k base1 -> KernameSet.In k base2) ->
    forall k,
    KernameSet.In k (List.fold_left (fun acc x => KernameSet.union (f x) acc) l base1) ->
    KernameSet.In k (List.fold_left (fun acc x => KernameSet.union (f x) acc) l base2).
  Proof.
    revert base1 base2. induction l; simpl; intros base1 base2 Hsub k Hin.
    - exact (Hsub k Hin).
    - eapply IHl; [ | exact Hin ].
      intros k0 Hk0. apply KernameSet.union_spec.
      apply KernameSet.union_spec in Hk0. destruct Hk0 as [Hk0 | Hk0].
      + left. exact Hk0.
      + right. exact (Hsub k0 Hk0).
  Qed.

  (** ** Alpha-equivalence for ANF values *)

  Section Alpha_Equiv.

  Context {fuel : Type} {Hfuel : @fuel_resource fuel}
          {trace : Type} {Htrace : @trace_resource trace}.
  Context (P1 : @PostT fuel trace) (PG : @PostGT fuel trace)
          (cenv : ctor_env)
          (Hprops : Post_properties cenv P1 P1 PG)
          (HpropsG : Post_properties cenv PG PG PG)
          (Hincl : inclusion _ (comp P1 P1) P1)
          (HinclG : inclusion _ P1 PG).
  Context (dcon_to_tag_inj :
            forall tgm dc dc',
              dcon_to_tag default_tag dc tgm = dcon_to_tag default_tag dc' tgm -> dc = dc').

  Definition anf_cvt_val_alpha_equiv_statement k :=
    forall v v1 v2,
      anf_val_rel v v1 -> anf_val_rel v v2 ->
      preord_val cenv PG k v1 v2.

  Definition anf_cvt_env_alpha_equiv_statement k :=
    forall names1 names2 vs rho1 rho2 f,
      anf_env_rel names1 vs rho1 ->
      anf_env_rel names2 vs rho2 ->
      preord_env_P_inj cenv PG (FromList names1) k (f <{ names1 ~> names2 }>) rho1 rho2.

  Lemma preord_env_P_inj_get S k f rho1 rho2 x y v1 v2 :
    preord_env_P_inj cenv PG (S \\ [set x]) k f rho1 rho2 ->
    M.get x rho1 = Some v1 ->
    M.get y rho2 = Some v2 ->
    preord_val cenv PG k v1 v2 ->
    preord_env_P_inj cenv PG S k (f {x ~> y}) rho1 rho2.
  Proof.
    intros Henv Hg1 Hg2 Hval z HS v Hgetz. destruct (Coqlib.peq x z).
    - subst. repeat subst_exp. rewrite extend_gss. eauto.
    - rewrite extend_gso; eauto. eapply Henv; eauto.
      constructor; eauto. intros Hc; inv Hc; eauto.
  Qed.

  Lemma anf_cvt_env_alpha_equiv_pre k :
    anf_cvt_val_alpha_equiv_statement k ->
    anf_cvt_env_alpha_equiv_statement k.
  Proof.
    intros IH n1 n2 vs.
    revert n1 n2. induction vs; intros n1 n2 rho1 rho2 f Hrel1 Hrel2.
    - inv Hrel1; inv Hrel2. simpl. repeat normalize_sets.
      intros x Hin. inv Hin.
    - inv Hrel1; inv Hrel2. destructAll.
      simpl. eapply preord_env_P_inj_get; eauto.
      repeat normalize_sets. eapply preord_env_P_inj_antimon.
      eapply IHvs. eassumption. eassumption. sets.
  Qed.

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
        * eapply Disjoint_Included_l; [ | exact Hd1 ]. intros z Hz. now right.
        * eapply Disjoint_Included_l; [ | exact Hd2 ]. intros z Hz. now right.
  Qed.

  (** Projection bindings compatibility for case branches *)
  Lemma ctx_bind_proj_Forall2_compat k rho1 rho2 x1 x2 ctag
        proj_vars1 proj_vars2 acc1 acc2 e1 e2 n
        (S_extra : Ensemble var) :
    preord_var_env cenv PG k rho1 rho2 x1 x2 ->
    Forall2 (preord_var_env cenv PG k rho1 rho2) acc1 acc2 ->
    preord_env_P cenv PG S_extra k rho1 rho2 ->
    List.length proj_vars1 = List.length proj_vars2 ->
    NoDup proj_vars1 -> NoDup proj_vars2 ->
    Disjoint _ (FromList proj_vars1) (FromList acc1 :|: [set x1]) ->
    Disjoint _ (FromList proj_vars2) (FromList acc2 :|: [set x2]) ->
    Disjoint _ S_extra (FromList proj_vars1 :|: FromList proj_vars2) ->
    (forall rho1' rho2' m',
        (m' <= k)%nat ->
        Forall2 (preord_var_env cenv PG m' rho1' rho2') proj_vars1 proj_vars2 ->
        Forall2 (preord_var_env cenv PG m' rho1' rho2') acc1 acc2 ->
        preord_var_env cenv PG m' rho1' rho2' x1 x2 ->
        preord_env_P cenv PG S_extra m' rho1' rho2' ->
        preord_exp cenv P1 PG m' (e1, rho1') (e2, rho2')) ->
    preord_exp cenv P1 PG k
               (ctx_bind_proj ctag x1 proj_vars1 n |[ e1 ]|, rho1)
               (ctx_bind_proj ctag x2 proj_vars2 n |[ e2 ]|, rho2).
  Proof.
    revert k rho1 rho2 x1 x2 ctag proj_vars2 acc1 acc2 e1 e2 n S_extra.
    induction proj_vars1;
      intros k rho1 rho2 x1 x2 ctag proj_vars2 acc1 acc2 e1 e2 n S_extra
             Hvar Hacc Hextra Hlen Hnd1 Hnd2 Hdis1 Hdis2 Hdis_extra Hexp.
    - destruct proj_vars2 as [ | v proj_vars2]; [ | simpl in Hlen; congruence ].
      cbn [ctx_bind_proj app_ctx_f].
      eapply Hexp; [ lia | constructor | exact Hacc | exact Hvar | ].
      eapply preord_env_P_monotonic; [ | exact Hextra ]. lia.
    - destruct proj_vars2 as [ | v proj_vars2]; [ simpl in Hlen; congruence | ].
      simpl in Hlen.
      cbn [ctx_bind_proj app_ctx_f].
      inv Hnd1. inv Hnd2.
      eapply preord_exp_proj_compat.
      + eapply Hprops.
      + eapply Hprops.
      + exact Hvar.
      + intros m v1 v2 Hlt Hval.
        eapply IHproj_vars1 with (acc1 := a :: acc1) (acc2 := v :: acc2).
        * eapply preord_var_env_extend_neq.
          -- eapply preord_var_env_monotonic. exact Hvar. lia.
          -- intros Heq. subst. eapply Hdis1. constructor. now left. right. constructor.
          -- intros Heq. subst. eapply Hdis2. constructor. now left. right. constructor.
        * constructor.
          -- eapply preord_var_env_extend_eq. exact Hval.
          -- eapply Forall2_preord_var_env_set.
             ++ eapply Forall2_preord_var_env_monotonic; [ | exact Hacc ]. lia.
             ++ intros Hc. eapply Hdis1. constructor. now left. left. exact Hc.
             ++ intros Hc. eapply Hdis2. constructor. now left. left. exact Hc.
        * (* preord_env_P S_extra preserved through M.set a/v *)
          eapply preord_env_P_set_not_in_P_l.
          eapply preord_env_P_set_not_in_P_r.
          -- eapply preord_env_P_monotonic; [ | exact Hextra ]. lia.
          -- eapply Disjoint_Singleton_r. intros Hc.
             eapply Hdis_extra. constructor. exact Hc. right. now left.
          -- eapply Disjoint_Singleton_r. intros Hc.
             eapply Hdis_extra. constructor. exact Hc. left. now left.
        * congruence.
        * eassumption.
        * eassumption.
        * rewrite FromList_cons. rewrite <- Union_assoc.
          eapply Union_Disjoint_r.
          -- eapply Disjoint_Singleton_r. eassumption.
          -- eapply Disjoint_Included; [ | | eapply Hdis1 ]; now sets.
        * rewrite FromList_cons. rewrite <- Union_assoc.
          eapply Union_Disjoint_r.
          -- eapply Disjoint_Singleton_r. eassumption.
          -- eapply Disjoint_Included; [ | | eapply Hdis2 ]; now sets.
        * (* Disjoint S_extra from remaining proj vars *)
          eapply Disjoint_Included_r; [ | exact Hdis_extra ].
          intros z Hz. inv Hz; [ left; right; exact H | right; right; exact H ].
        * intros rho1' rho2' m' Hle Hpvars Haccs Hvar' Hextra'.
          eapply Hexp.
          -- lia.
          -- inv Hpvars. constructor; eassumption.
          -- inv Haccs. eassumption.
          -- exact Hvar'.
          -- exact Hextra'.
  Qed.

  Lemma anf_cvt_env_alpha_equiv_Forall2 k :
    anf_cvt_val_alpha_equiv_statement k ->
    forall vs nms_a nms_b rho_a rho_b,
      anf_env_rel' anf_val_rel nms_a vs rho_a ->
      anf_env_rel' anf_val_rel nms_b vs rho_b ->
      Forall2 (preord_var_env cenv PG k rho_a rho_b) nms_a nms_b.
  Proof.
    intros Hval. induction vs; intros nms_a nms_b rho_a rho_b Hrel1 Hrel2.
    - inv Hrel1. inv Hrel2. constructor.
    - inv Hrel1. inv Hrel2. destructAll. constructor.
      + intros v1 Hget1.
        match goal with
        | [ H1 : M.get ?x1 rho_a = Some ?w1,
            H2 : M.get ?x2 rho_b = Some ?w2,
            Hv1 : anf_val_rel a ?w1,
            Hv2 : anf_val_rel a ?w2 |- _ ] =>
          rewrite H1 in Hget1; inv Hget1;
          eexists; split; [ exact H2 | eapply Hval; eassumption ]
        end.
      + eapply IHvs; eassumption.
  Qed.

  (** The main alpha-equiv theorems. These require mutual induction
      over the relational spec combined with well-founded induction on k.
      The proofs follow the structure of the old LambdaBoxLocal version. *)

  (* Statements for the four mutual parts *)
  Definition anf_cvt_exp_alpha_equiv k :=
    forall e C1 C2 r1 r2 m vars1 vars2 rho1 rho2 S1 S2 S3 S4 e_k1 e_k2,
      (m <= k)%nat ->
      anf_cvt_rel' cnstrs cmap S1 e vars1 S2 C1 r1 ->
      anf_cvt_rel' cnstrs cmap S3 e vars2 S4 C2 r2 ->
      Disjoint _ (FromList vars1) S1 ->
      Disjoint _ (FromList vars2) S3 ->
      Disjoint _ cmap_vars S1 ->
      Disjoint _ cmap_vars S3 ->
      Forall2 (preord_var_env cenv PG m rho1 rho2) vars1 vars2 ->
      preord_env_P cenv PG (cmap_vars_of (fun k => KernameSet.In k (term_global_deps e))) m rho1 rho2 ->
      (forall j rho1' rho2',
        (j <= m)%nat ->
        preord_var_env cenv PG j rho1' rho2' r1 r2 ->
        Forall2 (preord_var_env cenv PG j rho1' rho2') vars1 vars2 ->
        (forall x y, preord_var_env cenv PG m rho1 rho2 x y ->
                     ~ x \in S1 -> ~ y \in S3 ->
                     preord_var_env cenv PG j rho1' rho2' x y) ->
        preord_exp cenv P1 PG j (e_k1, rho1') (e_k2, rho2')) ->
      preord_exp cenv P1 PG m (C1 |[ e_k1 ]|, rho1) (C2 |[ e_k2 ]|, rho2).

  Definition anf_cvt_exp_alpha_equiv_at k e :=
    forall C1 C2 r1 r2 m vars1 vars2 rho1 rho2 S1 S2 S3 S4 e_k1 e_k2,
      (m <= k)%nat ->
      anf_cvt_rel' cnstrs cmap S1 e vars1 S2 C1 r1 ->
      anf_cvt_rel' cnstrs cmap S3 e vars2 S4 C2 r2 ->
      Disjoint _ (FromList vars1) S1 ->
      Disjoint _ (FromList vars2) S3 ->
      Disjoint _ cmap_vars S1 ->
      Disjoint _ cmap_vars S3 ->
      Forall2 (preord_var_env cenv PG m rho1 rho2) vars1 vars2 ->
      preord_env_P cenv PG (cmap_vars_of (fun k => KernameSet.In k (term_global_deps e))) m rho1 rho2 ->
      (forall j rho1' rho2',
        (j <= m)%nat ->
        preord_var_env cenv PG j rho1' rho2' r1 r2 ->
        Forall2 (preord_var_env cenv PG j rho1' rho2') vars1 vars2 ->
        (forall x y, preord_var_env cenv PG m rho1 rho2 x y ->
                     ~ x \in S1 -> ~ y \in S3 ->
                     preord_var_env cenv PG j rho1' rho2' x y) ->
        preord_exp cenv P1 PG j (e_k1, rho1') (e_k2, rho2')) ->
      preord_exp cenv P1 PG m (C1 |[ e_k1 ]|, rho1) (C2 |[ e_k2 ]|, rho2).

  Definition anf_cvt_args_alpha_equiv k :=
    forall args C1 C2 xs1 xs2 m vars1 vars2 rho1 rho2 S1 S2 S3 S4 e_k1 e_k2,
      All (anf_cvt_exp_alpha_equiv_at k) args ->
      (m <= k)%nat ->
      anf_cvt_rel_args' cnstrs cmap S1 args vars1 S2 C1 xs1 ->
      anf_cvt_rel_args' cnstrs cmap S3 args vars2 S4 C2 xs2 ->
      Disjoint _ (FromList vars1) S1 ->
      Disjoint _ (FromList vars2) S3 ->
      Disjoint _ cmap_vars S1 ->
      Disjoint _ cmap_vars S3 ->
      Forall2 (preord_var_env cenv PG m rho1 rho2) vars1 vars2 ->
      preord_env_P cenv PG (cmap_vars_of (fun k0 => KernameSet.In k0
          (List.fold_left (fun acc x => KernameSet.union (term_global_deps x) acc)
                          args KernameSet.empty))) m rho1 rho2 ->
      (forall j rho1' rho2',
        (j <= m)%nat ->
        Forall2 (preord_var_env cenv PG j rho1' rho2') xs1 xs2 ->
        Forall2 (preord_var_env cenv PG j rho1' rho2') vars1 vars2 ->
        (forall x y, preord_var_env cenv PG m rho1 rho2 x y ->
                     ~ x \in S1 -> ~ y \in S3 ->
                     preord_var_env cenv PG j rho1' rho2' x y) ->
        preord_exp cenv P1 PG j (e_k1, rho1') (e_k2, rho2')) ->
      preord_exp cenv P1 PG m (C1 |[ e_k1 ]|, rho1) (C2 |[ e_k2 ]|, rho2).

  Lemma anf_cvt_args_alpha_equiv_proof :
    forall k, anf_cvt_args_alpha_equiv k.
  Proof.
    intros k. unfold anf_cvt_args_alpha_equiv.
    intros args. induction args as [| a0 args' IHargs'];
    intros C1 C2 xs1 xs2 m vars1 vars2 rho1 rho2 S1 S2 S3 S4 e_k1 e_k2
           HAll Hm Hrel1 Hrel2 Hdis1 Hdis2 Hdis_cm1 Hdis_cm2 Henv Hcmap_env Hk.
    - (* nil *)
      inv Hrel1. inv Hrel2. simpl.
      eapply Hk; [lia | constructor | eassumption | intros ? ? Hpv _ _; exact Hpv].
    - (* cons *)
      inv Hrel1. inv Hrel2. inv HAll.
      rewrite <- !app_ctx_f_fuse.
      match goal with
      | [ IH_head : anf_cvt_exp_alpha_equiv_at k a0,
          IH_tail : All _ args' |- _ ] =>
        eapply IH_head
      end.
      + exact Hm.
      + eassumption.
      + eassumption.
      + exact Hdis1.
      + exact Hdis2.
      + exact Hdis_cm1.
      + exact Hdis_cm2.
      + exact Henv.
      + eapply preord_env_P_antimon; [ exact Hcmap_env | ].
        intros v Hv. destruct Hv as [kk [Hkin Hlk]].
        exists kk. split; [ | exact Hlk ].
        eapply fold_left_kset_union_elem with (x := a0).
        * left. reflexivity.
        * exact Hkin.
      + intros j rho1' rho2' Hle Hvar_x1 Henv_vars Hpres.
        eapply IHargs'.
        * match goal with | [ HA : All _ args' |- _ ] => exact HA end.
        * lia.
        * eassumption.
        * eassumption.
        * eapply Disjoint_Included_r;
            [eapply anf_cvt_exp_subset; eassumption | exact Hdis1].
        * eapply Disjoint_Included_r;
            [eapply anf_cvt_exp_subset; eassumption | exact Hdis2].
        * eapply Disjoint_Included_r;
            [eapply anf_cvt_exp_subset; eassumption | exact Hdis_cm1].
        * eapply Disjoint_Included_r;
            [eapply anf_cvt_exp_subset; eassumption | exact Hdis_cm2].
        * exact Henv_vars.
        * (* cmap_vars_of for tail — lift through Hpres *)
          intros v Hv.
          eapply Hpres.
          -- eapply Hcmap_env.
             destruct Hv as [kk [Hkin Hlk]]. exists kk. split; [ | exact Hlk ].
             simpl.
             eapply fold_left_kset_union_mono with (base1 := KernameSet.empty).
             { intros k0 Hk0. exfalso. apply (KernameSet.empty_spec Hk0). }
             exact Hkin.
          -- intros Hc. eapply Hdis_cm1. constructor.
             { destruct Hv as [kk [_ Hlk]]. exists kk. exact Hlk. }
             exact Hc.
          -- intros Hc. eapply Hdis_cm2. constructor.
             { destruct Hv as [kk [_ Hlk]]. exists kk. exact Hlk. }
             exact Hc.
        * intros j' rho1'' rho2'' Hle' Hxs_tail Henv_vars' Hpres'.
          eapply Hk.
          -- lia.
          -- constructor.
             ++ eapply Hpres'.
                ** eapply preord_var_env_monotonic. exact Hvar_x1. lia.
                ** eapply anf_cvt_result_not_in_output; eassumption.
                ** eapply anf_cvt_result_not_in_output; eassumption.
             ++ exact Hxs_tail.
          -- exact Henv_vars'.
          -- intros a1 b Hvar_ab Ha Hb.
             eapply Hpres'.
             ++ eapply Hpres. exact Hvar_ab. exact Ha. exact Hb.
             ++ intro Hc. apply Ha.
                eapply anf_cvt_exp_subset; eassumption.
             ++ intro Hc. apply Hb.
                eapply anf_cvt_exp_subset; eassumption.
  Qed.

  Definition anf_cvt_branches_alpha_equiv k :=
    forall ind brs n pats1 pats2 m y1 y2 vars1 vars2 rho1 rho2 S1 S2 S3 S4,
      (m <= k)%nat ->
      anf_cvt_rel_branches' cnstrs cmap S1 ind brs n vars1 y1 S2 pats1 ->
      anf_cvt_rel_branches' cnstrs cmap S3 ind brs n vars2 y2 S4 pats2 ->
      Disjoint _ ([set y1] :|: FromList vars1) S1 ->
      Disjoint _ ([set y2] :|: FromList vars2) S3 ->
      Disjoint _ cmap_vars S1 ->
      Disjoint _ cmap_vars S3 ->
      Forall2 (preord_var_env cenv PG m rho1 rho2) vars1 vars2 ->
      preord_var_env cenv PG m rho1 rho2 y1 y2 ->
      preord_exp cenv P1 PG m (Ecase y1 pats1, rho1) (Ecase y2 pats2, rho2).

  Definition anf_cvt_mfix_alpha_equiv k :=
    forall mfix fnames1 fnames2 m vars1 vars2 rho1 rho2
           S1 S2 S3 S4 fdefs1 fdefs2,
      (m <= k)%nat ->
      anf_cvt_rel_mfix' cnstrs cmap S1 mfix (List.rev fnames1 ++ vars1) fnames1 S2 fdefs1 ->
      anf_cvt_rel_mfix' cnstrs cmap S3 mfix (List.rev fnames2 ++ vars2) fnames2 S4 fdefs2 ->
      NoDup fnames1 -> NoDup fnames2 ->
      List.length fnames1 = List.length fnames2 ->
      Disjoint _ (FromList fnames1 :|: FromList vars1) S1 ->
      Disjoint _ (FromList fnames2 :|: FromList vars2) S3 ->
      Disjoint _ cmap_vars S1 ->
      Disjoint _ cmap_vars S3 ->
      Disjoint _ (FromList fnames1) (FromList vars1) ->
      Disjoint _ (FromList fnames2) (FromList vars2) ->
      Forall2 (preord_var_env cenv PG m rho1 rho2) vars1 vars2 ->
      Forall2 (preord_var_env cenv PG m
                 (def_funs fdefs1 fdefs1 rho1 rho1) (def_funs fdefs2 fdefs2 rho2 rho2))
              fnames1 fnames2.

  Definition anf_cvt_alpha_equiv_statement k :=
    anf_cvt_exp_alpha_equiv k /\
    anf_cvt_branches_alpha_equiv k /\
    anf_cvt_mfix_alpha_equiv k.

  Lemma anf_cvt_alpha_equiv :
    forall k, anf_cvt_alpha_equiv_statement k.
  Proof.
    intros k. induction k as [k IHk] using lt_wf_rec1.
    unfold anf_cvt_alpha_equiv_statement. split; [ | split ].
    { (* anf_cvt_exp_alpha_equiv *)
    unfold anf_cvt_exp_alpha_equiv.
    intros e. induction e using EInduction.term_forall_list_ind;
    intros C1 C2 r1 r2 mk vars1 vars2 rho1 rho2 S1 S2 S3 S4 e_k1 e_k2
           Hmk Hcvt1 Hcvt2 Hdis1 Hdis2 Hdis_cm1 Hdis_cm2 Henv Hcmap_env Hk;
    inv Hcvt1; inv Hcvt2.
    (* The induction on term gives us IHs for sub-terms.
       The inversions on anf_cvt_rel match up the same constructor. *)

    - (* tBox -> anf_Box *)
      simpl.
      eapply preord_exp_constr_compat.
      + eapply Hprops.
      + eapply Hprops.
      + constructor.
      + intros m0 vs1 vs2 Hlt Hvals.
        eapply Hk.
        * lia.
        * intros v1 Hg1. rewrite M.gss in Hg1. inv Hg1.
          eexists. split. { rewrite M.gss. reflexivity. }
          rewrite preord_val_eq. simpl. split; [reflexivity | eassumption].
        * eapply Forall2_preord_var_env_set.
          -- eapply Forall2_preord_var_env_monotonic; [ | eassumption ]. lia.
          -- intros Hin. eapply Hdis1. constructor; eassumption.
          -- intros Hin. eapply Hdis2. constructor; eassumption.
        * intros a b Hvar Ha Hb.
          eapply preord_var_env_extend_neq.
          -- eapply preord_var_env_monotonic. eassumption. lia.
          -- intros Heq. subst. eapply Ha. eassumption.
          -- intros Heq. subst. eapply Hb. eassumption.

    - (* tRel -> anf_Rel *)
      simpl.
      eapply Hk; [ lia | | exact Henv | intros ? ? Hpv _ _; exact Hpv ].
      match goal with
      | [ Hfa : Forall2 _ vars1 _, Hn : nth_error vars1 _ = Some _ |- _ ] =>
        destruct (Forall2_nth_error_l _ _ _ _ _ Hfa Hn) as [? [Hn2 ?]]
      end.
      match goal with
      | [ H1 : nth_error vars2 ?idx = Some ?a, H2 : nth_error vars2 ?idx = Some ?b |- _ ] =>
        rewrite H1 in H2; inv H2
      end. assumption.

    (* tVar, tEvar - impossible, no anf_cvt_rel constructors *)

    - (* tLambda -> anf_Lam *)
      simpl.
      eapply preord_exp_fun_compat.
      + eapply Hprops.
      + eapply Hprops.
      + eapply Hk.
        * lia.
        * (* r1/f1 and r2/f2 are related Vfun closures in def_funs *)
          intros v Hg.
          rewrite def_funs_eq in Hg. 2: { simpl; now left. }
          inv Hg.
          eexists. split. { rewrite def_funs_eq. reflexivity. simpl; now left. }
          eapply preord_val_fun.
          -- simpl. rewrite Coqlib.peq_true. reflexivity.
          -- simpl. rewrite Coqlib.peq_true. reflexivity.
          -- intros rho_b j' vs1 vs2 Hlen Hset.
             destruct vs1 as [ | v_arg1 [ | ? ? ] ]; simpl in *; try congruence.
             destruct vs2 as [ | v_arg2 [ | ? ? ] ]; simpl in *; try congruence.
             inv Hset.
             eexists. split. { reflexivity. }
             intros Hlt' Hall_args. inv Hall_args.
             eapply preord_exp_post_monotonic. { now eapply HinclG. }
             eapply (IHk j' ltac:(lia)).
             ++ lia.
             ++ eassumption.
             ++ eassumption.
             ++ (* Disjoint (FromList (x :: vars)) from S *)
                rewrite FromList_cons.
                eapply Union_Disjoint_l.
                ** eapply Disjoint_Singleton_l. intro Hc.
                   destruct Hc as [Hc' _]. destruct Hc' as [_ Hn].
                   apply Hn. constructor.
                ** eapply Disjoint_Included_r. apply Setminus_Included.
                   eapply Disjoint_Included_r. apply Setminus_Included. exact Hdis1.
             ++ rewrite FromList_cons.
                eapply Union_Disjoint_l.
                ** eapply Disjoint_Singleton_l. intro Hc.
                   destruct Hc as [Hc' _]. destruct Hc' as [_ Hn].
                   apply Hn. constructor.
                ** eapply Disjoint_Included_r. apply Setminus_Included.
                   eapply Disjoint_Included_r. apply Setminus_Included. exact Hdis2.
             ++ (* Disjoint cmap_vars *)
                eapply Disjoint_Included_r. apply Setminus_Included.
                eapply Disjoint_Included_r. apply Setminus_Included. exact Hdis_cm1.
             ++ eapply Disjoint_Included_r. apply Setminus_Included.
                eapply Disjoint_Included_r. apply Setminus_Included. exact Hdis_cm2.
             ++ constructor.
                ** eapply preord_var_env_extend_eq. eassumption.
                ** eapply Forall2_preord_var_env_set.
                   --- eapply Forall2_preord_var_env_set.
                       +++ eapply Forall2_preord_var_env_monotonic with (k := mk);
                           [ lia | exact Henv ].
                       +++ intro Hc. eapply Hdis1. constructor.
                           exact Hc. eapply Setminus_Included. eassumption.
                       +++ intro Hc. eapply Hdis2. constructor.
                           exact Hc. eapply Setminus_Included. eassumption.
                   --- intro Hx_vars. eapply Hdis1. constructor. exact Hx_vars.
                       eassumption.
                   --- intro Hx_vars. eapply Hdis2. constructor. exact Hx_vars.
                       eassumption.
             ++ (* preord_env_P (cmap_vars_of ...) — same deps since tLambda na e = term_global_deps e *)
                eapply preord_env_P_set_not_in_P_l.
                eapply preord_env_P_set_not_in_P_r.
                eapply preord_env_P_set_not_in_P_l.
                eapply preord_env_P_set_not_in_P_r.
                ** eapply preord_env_P_monotonic; [ | eassumption ]. lia.
                ** (* ~ r2/f2 \in cmap_vars_of ... *)
                   eapply Disjoint_Singleton_r. intros [kk [_ Hlk]].
                   eapply Hdis_cm2. constructor.
                   { exists kk. exact Hlk. }
                   eapply Setminus_Included. eassumption.
                ** (* ~ r1/f1 \in cmap_vars_of ... *)
                   eapply Disjoint_Singleton_r. intros [kk [_ Hlk]].
                   eapply Hdis_cm1. constructor.
                   { exists kk. exact Hlk. }
                   eapply Setminus_Included. eassumption.
                ** (* ~ x0 \in cmap_vars_of ... *)
                   eapply Disjoint_Singleton_r. intros [kk [_ Hlk]].
                   eapply Hdis_cm2. constructor.
                   { exists kk. exact Hlk. }
                   eassumption.
                ** (* ~ x1 \in cmap_vars_of ... *)
                   eapply Disjoint_Singleton_r. intros [kk [_ Hlk]].
                   eapply Hdis_cm1. constructor.
                   { exists kk. exact Hlk. }
                   eassumption.
             ++ intros j0 rho1'' rho2'' _ Hvar_cont _ _.
                eapply preord_exp_halt_compat;
                  [ eapply Hprops | eapply Hprops | exact Hvar_cont ].
        * eapply Forall2_preord_var_env_set.
          -- eapply Forall2_preord_var_env_monotonic with (k := mk); [ lia | exact Henv ].
          -- intro Hc. eapply Hdis1. constructor. exact Hc.
             eapply Setminus_Included. eassumption.
          -- intro Hc. eapply Hdis2. constructor. exact Hc.
             eapply Setminus_Included. eassumption.
        * intros a b Hvar Ha Hb.
          eapply preord_var_env_extend_neq.
          -- eapply preord_var_env_monotonic. exact Hvar. lia.
          -- intros Heq. subst. apply Ha.
             eapply Setminus_Included. eassumption.
          -- intros Heq. subst. apply Hb.
             eapply Setminus_Included. eassumption.

    - (* tLetIn -> anf_LetIn *)
      rewrite <- !app_ctx_f_fuse.
      eapply IHe1.
      + exact Hmk.
      + eassumption.
      + eassumption.
      + exact Hdis1.
      + exact Hdis2.
      + exact Hdis_cm1.
      + exact Hdis_cm2.
      + exact Henv.
      + (* cmap_vars_of for b ⊆ cmap_vars_of for tLetIn *)
        eapply preord_env_P_antimon; [ exact Hcmap_env | ].
        intros v Hv. destruct Hv as [kk [Hkin Hlk]].
        exists kk. split; [ | exact Hlk ].
        simpl. apply KernameSet.union_spec. left. exact Hkin.
      + intros j rho1' rho2' Hle Hvar_x1 Henv_vars Hpres.
        eapply IHe2.
        * lia.
        * eassumption.
        * eassumption.
        * rewrite FromList_cons. eapply Union_Disjoint_l.
          -- eapply Disjoint_Singleton_l.
             eapply anf_cvt_result_not_in_output; eassumption.
          -- eapply Disjoint_Included_r; [eapply anf_cvt_exp_subset; eassumption | exact Hdis1].
        * rewrite FromList_cons. eapply Union_Disjoint_l.
          -- eapply Disjoint_Singleton_l.
             eapply anf_cvt_result_not_in_output; eassumption.
          -- eapply Disjoint_Included_r; [eapply anf_cvt_exp_subset; eassumption | exact Hdis2].
        * eapply Disjoint_Included_r; [eapply anf_cvt_exp_subset; eassumption | exact Hdis_cm1].
        * eapply Disjoint_Included_r; [eapply anf_cvt_exp_subset; eassumption | exact Hdis_cm2].
        * constructor.
          -- exact Hvar_x1.
          -- exact Henv_vars.
        * (* cmap_vars_of for t — lift through Hpres *)
          intros v Hv.
          eapply Hpres.
          -- eapply Hcmap_env.
             destruct Hv as [kk [Hkin Hlk]]. exists kk. split; [ | exact Hlk ].
             simpl. apply KernameSet.union_spec. right. exact Hkin.
          -- intros Hc. eapply Hdis_cm1. constructor.
             { destruct Hv as [kk [_ Hlk]]. exists kk. exact Hlk. }
             exact Hc.
          -- intros Hc. eapply Hdis_cm2. constructor.
             { destruct Hv as [kk [_ Hlk]]. exists kk. exact Hlk. }
             exact Hc.
        * intros j' rho1'' rho2'' Hle' Hvar_r2 Henv_vars2 Hpres'.
          eapply Hk.
          -- lia.
          -- exact Hvar_r2.
          -- inv Henv_vars2. eassumption.
          -- intros a b Hvar_ab Ha Hb.
             eapply Hpres'.
             ++ eapply Hpres. exact Hvar_ab. exact Ha. exact Hb.
             ++ intro Hc. apply Ha.
                assert (Hsub1 : _ \subset S1) by (eapply anf_cvt_exp_subset; eassumption).
                exact (Hsub1 _ Hc).
             ++ intro Hc. apply Hb.
                assert (Hsub2 : _ \subset S3) by (eapply anf_cvt_exp_subset; eassumption).
                exact (Hsub2 _ Hc).

    - (* tApp -> anf_App *)
      rewrite <- !app_ctx_f_fuse. simpl.
      eapply IHe1.
      + exact Hmk.
      + eassumption.
      + eassumption.
      + exact Hdis1.
      + exact Hdis2.
      + exact Hdis_cm1.
      + exact Hdis_cm2.
      + exact Henv.
      + (* cmap_vars_of for u ⊆ cmap_vars_of for tApp u v *)
        eapply preord_env_P_antimon; [ exact Hcmap_env | ].
        intros v Hv. destruct Hv as [kk [Hkin Hlk]].
        exists kk. split; [ | exact Hlk ].
        simpl. apply KernameSet.union_spec. left. exact Hkin.
      + intros j rho1' rho2' Hle Hvar_x1 Henv_vars Hpres1.
        eapply IHe2.
        * lia.
        * eassumption.
        * eassumption.
        * eapply Disjoint_Included_r;
          [eapply anf_cvt_exp_subset; eassumption | exact Hdis1].
        * eapply Disjoint_Included_r;
          [eapply anf_cvt_exp_subset; eassumption | exact Hdis2].
        * eapply Disjoint_Included_r;
          [eapply anf_cvt_exp_subset; eassumption | exact Hdis_cm1].
        * eapply Disjoint_Included_r;
          [eapply anf_cvt_exp_subset; eassumption | exact Hdis_cm2].
        * exact Henv_vars.
        * (* cmap_vars_of for v — lift through Hpres1 *)
          intros v Hv.
          eapply Hpres1.
          -- eapply Hcmap_env.
             destruct Hv as [kk [Hkin Hlk]]. exists kk. split; [ | exact Hlk ].
             simpl. apply KernameSet.union_spec. right. exact Hkin.
          -- intros Hc. eapply Hdis_cm1. constructor.
             { destruct Hv as [kk [_ Hlk]]. exists kk. exact Hlk. }
             exact Hc.
          -- intros Hc. eapply Hdis_cm2. constructor.
             { destruct Hv as [kk [_ Hlk]]. exists kk. exact Hlk. }
             exact Hc.
        * intros j' rho1'' rho2'' Hle' Hvar_x2 Henv_vars' Hpres2.
          eapply preord_exp_letapp_compat.
          -- now eapply Hprops.
          -- now eapply Hprops.
          -- now eapply Hprops.
          -- (* function: x1 preserved through C2 using Hpres2 *)
             eapply Hpres2.
             ++ eapply preord_var_env_monotonic. exact Hvar_x1. lia.
             ++ eapply anf_cvt_result_not_in_output; eassumption.
             ++ eapply anf_cvt_result_not_in_output; eassumption.
          -- constructor. exact Hvar_x2. constructor.
          -- (* letapp callback *)
             intros m'' v1 v2 Hlt Hval.
             eapply Hk.
             ++ lia.
             ++ intros w1 Hgr1. rewrite M.gss in Hgr1. inv Hgr1.
                eexists. split. rewrite M.gss. reflexivity.
                eapply preord_val_monotonic. exact Hval. lia.
             ++ eapply Forall2_preord_var_env_set.
                ** eapply Forall2_preord_var_env_monotonic with (k := j'); [lia | exact Henv_vars'].
                ** intros Hr1_vars.
                   match goal with
                   | [ Hcvt_e1 : anf_cvt_rel _ _ _ _ S1 _ _ _ _ _,
                       Hcvt_e2 : anf_cvt_rel _ _ _ _ _ _ _ ?S6 _ _,
                       Hin : _ \in ?S6 |- _ ] =>
                     assert (H65 : S6 \subset _) by (eapply anf_cvt_exp_subset; exact Hcvt_e2);
                     assert (H51 : _ \subset S1) by (eapply anf_cvt_exp_subset; exact Hcvt_e1);
                     eapply Hdis1; constructor; [ exact Hr1_vars | apply H51; apply H65; exact Hin ]
                   end.
                ** intros Hr2_vars.
                   match goal with
                   | [ Hcvt_e1 : anf_cvt_rel _ _ _ _ S3 _ _ _ _ _,
                       Hcvt_e2 : anf_cvt_rel _ _ _ _ _ _ _ ?S7 _ _,
                       Hin : _ \in ?S7 |- _ ] =>
                     assert (H72 : S7 \subset _) by (eapply anf_cvt_exp_subset; exact Hcvt_e2);
                     assert (H23 : _ \subset S3) by (eapply anf_cvt_exp_subset; exact Hcvt_e1);
                     eapply Hdis2; constructor; [ exact Hr2_vars | apply H23; apply H72; exact Hin ]
                   end.
             ++ intros a b Hvar_ab Ha Hb.
                eapply preord_var_env_extend_neq.
                ** eapply preord_var_env_monotonic.
                   --- eapply Hpres2.
                       +++ eapply Hpres1. exact Hvar_ab. exact Ha. exact Hb.
                       +++ intro Hc. apply Ha.
                           assert (Hs51 : _ \subset S1) by (eapply anf_cvt_exp_subset; eassumption).
                           exact (Hs51 _ Hc).
                       +++ intro Hc. apply Hb.
                           assert (Hs23 : _ \subset S3) by (eapply anf_cvt_exp_subset; eassumption).
                           exact (Hs23 _ Hc).
                   --- lia.
                ** intros Heq. subst. apply Ha.
                   match goal with
                   | [ Hcvt_e1 : anf_cvt_rel _ _ _ _ S1 _ _ _ _ _,
                       Hcvt_e2 : anf_cvt_rel _ _ _ _ _ _ _ ?S6 _ _,
                       Hin : _ \in ?S6 |- _ ] =>
                     assert (H65 : S6 \subset _) by (eapply anf_cvt_exp_subset; exact Hcvt_e2);
                     assert (H51 : _ \subset S1) by (eapply anf_cvt_exp_subset; exact Hcvt_e1);
                     apply H51; apply H65; exact Hin
                   end.
                ** intros Heq. subst. apply Hb.
                   match goal with
                   | [ Hcvt_e1 : anf_cvt_rel _ _ _ _ S3 _ _ _ _ _,
                       Hcvt_e2 : anf_cvt_rel _ _ _ _ _ _ _ ?S7 _ _,
                       Hin : _ \in ?S7 |- _ ] =>
                     assert (H72 : S7 \subset _) by (eapply anf_cvt_exp_subset; exact Hcvt_e2);
                     assert (H23 : _ \subset S3) by (eapply anf_cvt_exp_subset; exact Hcvt_e1);
                     apply H23; apply H72; exact Hin
                   end.

    - (* tConst -> anf_Const *)
      simpl.
      match goal with
      | [ H1 : lookup_const _ ?s = Some ?v1,
          H2 : lookup_const _ ?s = Some ?v2 |- _ ] =>
        rewrite H1 in H2; inv H2
      end.
      eapply Hk; [ lia | | exact Henv | intros ? ? Hpv _ _; exact Hpv ].
      (* Need: preord_var_env cenv PG mk rho1 rho2 v v, where v is a cmap var *)
      intros v1 Hget_v.
      eapply Hcmap_env.
      { match goal with
        | [ Hl : lookup_const _ ?s = Some ?vv |- _ ] =>
          unfold cmap_vars_of; exists s; split;
          [ apply KernameSet.singleton_spec; reflexivity | exact Hl ]
        end. }
      exact Hget_v.

    - (* tConstruct -> anf_Construct *)
      rewrite <- !app_ctx_f_fuse.
      match goal with
      | [ HA : All _ ?args |- _ ] =>
        eapply (anf_cvt_args_alpha_equiv_proof k args)
      end.
      + eassumption.
      + exact Hmk.
      + eassumption.
      + eassumption.
      + eapply Disjoint_Included_r; [apply Setminus_Included | exact Hdis1].
      + eapply Disjoint_Included_r; [apply Setminus_Included | exact Hdis2].
      + eapply Disjoint_Included_r; [apply Setminus_Included | exact Hdis_cm1].
      + eapply Disjoint_Included_r; [apply Setminus_Included | exact Hdis_cm2].
      + exact Henv.
      + (* cmap_vars_of for args ⊆ cmap_vars_of for tConstruct *)
        eapply preord_env_P_antimon; [ exact Hcmap_env | ].
        intros v Hv. destruct Hv as [kk [Hkin Hlk]].
        exists kk. split; [ | exact Hlk ].
        simpl. destruct i.
        eapply fold_left_kset_union_mono with (base1 := KernameSet.empty).
        { intros k0 Hk0. exfalso. apply (KernameSet.empty_spec Hk0). }
        exact Hkin.
      + intros j rho1' rho2' Hle Hxs_F2 Hvars_F2 Hpres.
        eapply preord_exp_constr_compat.
        * eapply Hprops.
        * eapply Hprops.
        * exact Hxs_F2.
        * intros m0 vs1 vs2 Hlt Hvals.
          eapply Hk.
          -- lia.
          -- intros v0 Hg1. rewrite M.gss in Hg1. inv Hg1.
             eexists. split. rewrite M.gss. reflexivity.
             rewrite preord_val_eq. simpl. split; [congruence | exact Hvals].
          -- eapply Forall2_preord_var_env_set.
             ++ eapply Forall2_preord_var_env_monotonic with (k := j); [lia | exact Hvars_F2].
             ++ intros Hx1_vars. eapply Hdis1. constructor; eassumption.
             ++ intros Hx2_vars. eapply Hdis2. constructor; eassumption.
          -- intros a b Hvar Ha Hb.
             eapply preord_var_env_extend_neq.
             ++ eapply preord_var_env_monotonic.
                eapply Hpres. exact Hvar.
                ** intro Hc. apply Ha. inv Hc. assumption.
                ** intro Hc. apply Hb. inv Hc. assumption.
                ** lia.
             ++ intros Heq. subst. apply Ha. eassumption.
             ++ intros Heq. subst. apply Hb. eassumption.

    - (* tCase -> anf_Case *)
      simpl. rewrite <- !app_ctx_f_fuse.
      eapply preord_exp_fun_compat.
      + eapply Hprops.
      + eapply Hprops.
      + eapply IHe.
        * lia.
        * eassumption.
        * eassumption.
        * eapply Disjoint_Included_r. apply Setminus_Included.
          eapply Disjoint_Included_r. apply Setminus_Included. exact Hdis1.
        * eapply Disjoint_Included_r. apply Setminus_Included.
          eapply Disjoint_Included_r. apply Setminus_Included. exact Hdis2.
        * eapply Disjoint_Included_r. apply Setminus_Included.
          eapply Disjoint_Included_r. apply Setminus_Included. exact Hdis_cm1.
        * eapply Disjoint_Included_r. apply Setminus_Included.
          eapply Disjoint_Included_r. apply Setminus_Included. exact Hdis_cm2.
        * eapply Forall2_preord_var_env_set.
          -- eapply Forall2_preord_var_env_monotonic with (k := mk); [lia | exact Henv].
          -- intro Hc. eapply Hdis1. constructor. exact Hc. eassumption.
          -- intro Hc. eapply Hdis2. constructor. exact Hc. eassumption.
        * (* cmap_vars_of for scrutinee ⊆ for tCase *)
          eapply preord_env_P_set_not_in_P_l.
          eapply preord_env_P_set_not_in_P_r.
          ** eapply preord_env_P_antimon; [ eapply preord_env_P_monotonic; [ | exact Hcmap_env ]; lia | ].
             intros v Hv. destruct Hv as [kk0 [Hkin Hlk]].
             exists kk0. split; [ | exact Hlk ].
             simpl.
             apply KernameSet.union_spec. right.
             apply fold_left_kset_union_base. exact Hkin.
          ** eapply Disjoint_Singleton_r. intros [kk0 [_ Hlk]].
             eapply Hdis_cm2. constructor. { exists kk0. exact Hlk. } eassumption.
          ** eapply Disjoint_Singleton_r. intros [kk0 [_ Hlk]].
             eapply Hdis_cm1. constructor. { exists kk0. exact Hlk. } eassumption.
        * (* continuation: Eletapp r f func_tag [x_scr] e_k *)
          intros j rho1' rho2' Hle Hvar_xscr Henvvars Hpres.
          eapply preord_exp_letapp_compat.
          -- now eapply Hprops.
          -- now eapply Hprops.
          -- now eapply Hprops.
          -- (* f1 f2 related *)
             eapply Hpres.
             ++ intros v Hg. rewrite def_funs_eq in Hg. 2: { simpl; now left. }
                inv Hg.
                eexists. split. { rewrite def_funs_eq. reflexivity. simpl; now left. }
                eapply preord_val_fun.
                +++ simpl. rewrite Coqlib.peq_true. reflexivity.
                +++ simpl. rewrite Coqlib.peq_true. reflexivity.
                +++ intros rho_b j' vs1 vs2 Hlen Hset.
                    destruct vs1 as [ | v1 [ | ? ? ] ]; simpl in *; try congruence.
                    destruct vs2 as [ | v2 [ | ? ? ] ]; simpl in *; try congruence.
                    inv Hset.
                    eexists. split. { reflexivity. }
                    intros Hlt Hall. inv Hall.
                    eapply preord_exp_post_monotonic. { now eapply HinclG. }
                    destruct (IHk j' ltac:(lia)) as [_ Hbrs_j].
                    eapply (proj1 (proj2 (IHk j' ltac:(lia)))); try lia; try eassumption.
                    (* Disjoint ([set y] :|: FromList vars1) S_mid *)
                    +++ match goal with
                        | [ Hcvt_scr : anf_cvt_rel' _ _ _ ?Smid _ _ _ |- Disjoint _ _ ?Smid ] =>
                          eapply Disjoint_Included_r; [ eapply anf_cvt_exp_subset; exact Hcvt_scr | ]
                        end.
                        eapply Union_Disjoint_l.
                        ---- eapply Disjoint_Singleton_l. intro Hc. destruct Hc as [_ Hn]. apply Hn. constructor.
                        ---- eapply Disjoint_Included_r; [ apply Setminus_Included | ].
                             eapply Disjoint_Included_r; [ apply Setminus_Included | exact Hdis1 ].
                    +++ match goal with
                        | [ Hcvt_scr : anf_cvt_rel' _ _ _ ?Smid _ _ _ |- Disjoint _ _ ?Smid ] =>
                          eapply Disjoint_Included_r; [ eapply anf_cvt_exp_subset; exact Hcvt_scr | ]
                        end.
                        eapply Union_Disjoint_l.
                        ---- eapply Disjoint_Singleton_l. intro Hc. destruct Hc as [_ Hn]. apply Hn. constructor.
                        ---- eapply Disjoint_Included_r; [ apply Setminus_Included | ].
                             eapply Disjoint_Included_r; [ apply Setminus_Included | exact Hdis2 ].
                    +++ match goal with
                        | [ Hcvt_scr : anf_cvt_rel' _ _ _ ?Smid _ _ _ |- Disjoint _ cmap_vars ?Smid ] =>
                          eapply Disjoint_Included_r; [ eapply anf_cvt_exp_subset; exact Hcvt_scr | ]
                        end.
                        eapply Disjoint_Included_r; [ apply Setminus_Included | ].
                        eapply Disjoint_Included_r; [ apply Setminus_Included | exact Hdis_cm1 ].
                    +++ match goal with
                        | [ Hcvt_scr : anf_cvt_rel' _ _ _ ?Smid _ _ _ |- Disjoint _ cmap_vars ?Smid ] =>
                          eapply Disjoint_Included_r; [ eapply anf_cvt_exp_subset; exact Hcvt_scr | ]
                        end.
                        eapply Disjoint_Included_r; [ apply Setminus_Included | ].
                        eapply Disjoint_Included_r; [ apply Setminus_Included | exact Hdis_cm2 ].
                    +++ eapply Forall2_preord_var_env_set.
                        ---- eapply Forall2_preord_var_env_set.
                             ++++ eapply Forall2_preord_var_env_monotonic with (k := mk); [lia | exact Henv].
                             ++++ intro Hc. eapply Hdis1. constructor. exact Hc. eassumption.
                             ++++ intro Hc. eapply Hdis2. constructor. exact Hc. eassumption.
                        ---- intro Hc. eapply Hdis1. constructor. exact Hc. eapply Setminus_Included. eassumption.
                        ---- intro Hc. eapply Hdis2. constructor. exact Hc. eapply Setminus_Included. eassumption.
                    +++ eapply preord_var_env_extend_eq. eassumption.
             ++ intro Hc. destruct Hc as [Hc1 _]. destruct Hc1 as [_ Hn].
                apply Hn. constructor.
             ++ intro Hc. destruct Hc as [Hc1 _]. destruct Hc1 as [_ Hn].
                apply Hn. constructor.
          -- (* args *)
             constructor. exact Hvar_xscr. constructor.
          -- (* letapp continuation *)
             intros m' v1 v2 Hlt Hval.
             eapply Hk.
             ++ lia.
             ++ intros w Hg. rewrite M.gss in Hg. inv Hg.
                eexists. split. { rewrite M.gss. reflexivity. }
                eapply preord_val_monotonic. exact Hval. lia.
             ++ eapply Forall2_preord_var_env_set.
                ** eapply Forall2_preord_var_env_monotonic with (k := j);
                   [lia | exact Henvvars].
                ** intro Hr. apply (Disjoint_In_l _ _ _ Hdis1 Hr).
                   eapply Setminus_Included. eapply Setminus_Included.
                   eapply anf_cvt_exp_subset. eassumption.
                   eapply anf_cvt_branches_subset. eassumption.
                   eassumption.
                ** intro Hr. apply (Disjoint_In_l _ _ _ Hdis2 Hr).
                   eapply Setminus_Included. eapply Setminus_Included.
                   eapply anf_cvt_exp_subset. eassumption.
                   eapply anf_cvt_branches_subset. eassumption.
                   eassumption.
             ++ intros a b Hvar Ha Hb.
                eapply preord_var_env_extend_neq.
                ** eapply preord_var_env_monotonic.
                   --- eapply Hpres.
                       +++ eapply preord_var_env_extend_neq.
                           *** eapply preord_var_env_monotonic. exact Hvar. lia.
                           *** intros Heq. subst. apply Ha. eassumption.
                           *** intros Heq. subst. apply Hb. eassumption.
                       +++ intro Hc. apply Ha.
                           eapply Setminus_Included. eapply Setminus_Included. exact Hc.
                       +++ intro Hc. apply Hb.
                           eapply Setminus_Included. eapply Setminus_Included. exact Hc.
                   --- lia.
                ** intros Heq. subst. apply Ha.
                   eapply Setminus_Included. eapply Setminus_Included.
                   eapply anf_cvt_exp_subset. eassumption.
                   eapply anf_cvt_branches_subset. eassumption.
                   eassumption.
                ** intros Heq. subst. apply Hb.
                   eapply Setminus_Included. eapply Setminus_Included.
                   eapply anf_cvt_exp_subset. eassumption.
                   eapply anf_cvt_branches_subset. eassumption.
                   eassumption.

    - (* tProj -> anf_Proj *)
      rewrite <- !app_ctx_f_fuse.
      eapply IHe.
      + exact Hmk.
      + eassumption.
      + eassumption.
      + exact Hdis1.
      + exact Hdis2.
      + exact Hdis_cm1.
      + exact Hdis_cm2.
      + exact Henv.
      + (* cmap_vars_of for c ⊆ cmap_vars_of for tProj p c *)
        eapply preord_env_P_antimon; [ exact Hcmap_env | ].
        intros v Hv. destruct Hv as [kk [Hkin Hlk]].
        exists kk. split; [ | exact Hlk ].
        simpl. apply KernameSet.union_spec. right. exact Hkin.
      + intros j rho1' rho2' Hle Hvar_xscr Henvvars Hpres.
        eapply preord_exp_proj_compat; [ eapply Hprops | eapply Hprops | exact Hvar_xscr | ].
        * intros m' v1 v2 Hlt Hval.
          eapply Hk.
          -- lia.
          -- intros w1 Hg1. rewrite M.gss in Hg1. inv Hg1.
             eexists. split. rewrite M.gss. reflexivity.
             eapply preord_val_monotonic. exact Hval. lia.
          -- eapply Forall2_preord_var_env_set.
             ++ eapply Forall2_preord_var_env_monotonic with (k := j); [lia | exact Henvvars].
             ++ intros Hr. eapply Hdis1. constructor. exact Hr.
                eapply anf_cvt_exp_subset; eassumption.
             ++ intros Hr. eapply Hdis2. constructor. exact Hr.
                eapply anf_cvt_exp_subset; eassumption.
          -- intros a b Hvar_ab Ha Hb.
             eapply preord_var_env_extend_neq.
             ++ eapply preord_var_env_monotonic.
                eapply Hpres. exact Hvar_ab. exact Ha. exact Hb. lia.
             ++ intros Heq. subst. apply Ha.
                eapply anf_cvt_exp_subset; eassumption.
             ++ intros Heq. subst. apply Hb.
                eapply anf_cvt_exp_subset; eassumption.

    - (* tFix -> anf_Fix *)
      simpl.
      (* Get Forall2 for all fnames using the mfix part of IHk *)
      assert (Hafn1 : all_fun_name fdefs = fnames) by
        (eapply anf_cvt_mfix_all_fun_name; eassumption).
      assert (Hafn2 : all_fun_name fdefs0 = fnames0) by
        (eapply anf_cvt_mfix_all_fun_name; eassumption).
      assert (Hfn_env : Forall2
        (preord_var_env cenv PG (mk - 1)
           (def_funs fdefs fdefs rho1 rho1) (def_funs fdefs0 fdefs0 rho2 rho2))
        fnames fnames0).
      { eapply (proj2 (proj2 (IHk (mk - 1) ltac:(lia)))); try lia; try eassumption.
        - eapply Union_Disjoint_l.
          + eapply Disjoint_Setminus_r. eapply Included_refl.
          + eapply Disjoint_Included_r; [ eapply Setminus_Included | exact Hdis1 ].
        - eapply Union_Disjoint_l.
          + eapply Disjoint_Setminus_r. eapply Included_refl.
          + eapply Disjoint_Included_r; [ eapply Setminus_Included | exact Hdis2 ].
        - eapply Disjoint_Included_r; [ eapply Setminus_Included | exact Hdis_cm1 ].
        - eapply Disjoint_Included_r; [ eapply Setminus_Included | exact Hdis_cm2 ].
        - eapply Disjoint_Included_l; [ eassumption | eapply Disjoint_sym; exact Hdis1 ].
        - eapply Disjoint_Included_l; [ eassumption | eapply Disjoint_sym; exact Hdis2 ].
        - eapply Forall2_preord_var_env_monotonic with (k := mk); [ lia | exact Henv ]. }
      eapply preord_exp_fun_compat.
      + eapply Hprops.
      + eapply Hprops.
      + eapply Hk.
        * lia.
        * (* preord_var_env r1 r2: extract from Hfn_env *)
          match goal with
          | [ Hn1 : nth_error fnames _ = Some r1,
              Hn2 : nth_error fnames0 _ = Some r2 |- _ ] =>
            destruct (Forall2_nth_error_l _ _ _ _ _ Hfn_env Hn1)
              as [r2' [Hn2' Hr12]];
            rewrite Hn2 in Hn2'; inv Hn2'; exact Hr12
          end.
        * (* Forall2 for outer vars under def_funs *)
          eapply Forall2_preord_var_env_def_funs.
          -- eapply Forall2_preord_var_env_monotonic with (k := mk); [ lia | exact Henv ].
          -- eapply Disjoint_Included_r.
             exact (proj1 (Same_set_all_fun_name _)).
             rewrite Hafn1.
             eapply Disjoint_Included_r; [ eassumption | exact Hdis1 ].
          -- eapply Disjoint_Included_r.
             exact (proj1 (Same_set_all_fun_name _)).
             rewrite Hafn2.
             eapply Disjoint_Included_r; [ eassumption | exact Hdis2 ].
        * (* preservation *)
          intros a b Hvar Ha Hb.
          eapply preord_var_env_def_funs_not_In_r.
          { intros Hc. apply Hb.
            match goal with
            | [ Hsub : FromList fnames0 \subset _ |- _ ] => apply Hsub end.
            rewrite <- Hafn2.
            exact ((proj1 (Same_set_all_fun_name _)) _ Hc). }
          eapply preord_var_env_def_funs_not_In_l.
          { intros Hc. apply Ha.
            match goal with
            | [ Hsub : FromList fnames \subset _ |- _ ] => apply Hsub end.
            rewrite <- Hafn1.
            exact ((proj1 (Same_set_all_fun_name _)) _ Hc). }
          eapply preord_var_env_monotonic. exact Hvar. lia.

    (* tCoFix - impossible *)
    - (* tPrim -> anf_Prim *)
      simpl.
      match goal with
      | [ H1 : trans_prim_val ?p = Some ?pv1,
          H2 : trans_prim_val ?p = Some ?pv2 |- _ ] =>
        rewrite H1 in H2; inv H2
      end.
      eapply preord_exp_prim_val_compat. eapply Hprops.

    (* tLazy, tForce - impossible *)
    }
    { (* anf_cvt_branches_alpha_equiv *)
      unfold anf_cvt_branches_alpha_equiv.
      intros ind brs. induction brs as [| [lnames e_br] brs' IHbrs];
      intros n pats1 pats2 m y1 y2 vars1 vars2 rho1 rho2 S1 S2 S3 S4
             Hm Hbr1 Hbr2 Hdis1 Hdis2 Hdis_cm1 Hdis_cm2 Henv Hvar_y.
      - (* nil *)
        inv Hbr1. inv Hbr2. eapply preord_exp_case_nil_compat. eapply Hprops.
      - (* cons *)
        inv Hbr1. inv Hbr2.
        eapply preord_exp_case_cons_compat.
        + eapply Hprops.
        + eapply Hprops.
        + eapply Hprops.
        + (* Forall2 ctor tags for tail *)
          eapply anf_cvt_branches_ctor_tag; eassumption.
        + exact Hvar_y.
        + (* head branch body *)
          intros m' Hlt.
          eapply preord_exp_monotonic.
          * eapply ctx_bind_proj_Forall2_compat with
              (acc1 := vars1) (acc2 := vars2)
              (S_extra := cmap_vars_of (fun k0 => KernameSet.In k0 (term_global_deps (EAst.tCase (ind, n0) (EAst.tRel 0) ((lnames, e_br) :: brs'))))).
            -- eapply preord_var_env_monotonic; [ exact Hvar_y | lia ].
            -- eapply Forall2_preord_var_env_monotonic; [ | exact Henv ]. lia.
            -- eapply preord_env_P_monotonic; [ | exact Hcmap_env ]. lia.
            -- congruence.
            -- eassumption.
            -- eassumption.
            -- eapply Disjoint_Included_l.
               { match goal with [ H : FromList ?vs \subset _ |- _ ] =>
                   eapply Included_trans; [ exact H | ] end.
                 eapply anf_cvt_branches_subset. eassumption. }
               eapply Disjoint_Included_r; [ | eapply Disjoint_sym; exact Hdis1 ].
               rewrite Union_commut. eapply Included_refl.
            -- eapply Disjoint_Included_l.
               { match goal with [ H : FromList ?vs \subset _ |- _ ] =>
                   eapply Included_trans; [ exact H | ] end.
                 eapply anf_cvt_branches_subset. eassumption. }
               eapply Disjoint_Included_r; [ | eapply Disjoint_sym; exact Hdis2 ].
               rewrite Union_commut. eapply Included_refl.
            -- (* Disjoint cmap_vars_of from proj vars *)
               eapply Disjoint_Included_l.
               { intros z [kk [_ Hlk]]. exists kk. exact Hlk. }
               eapply Disjoint_Included_r.
               { intros z Hz. inv Hz.
                 - match goal with [ H : FromList ?vs \subset _ |- _ ] =>
                     eapply (Included_trans H); eapply anf_cvt_branches_subset; eassumption end.
                   exact H.
                 - match goal with [ H : FromList ?vs \subset _ |- _ ] =>
                     eapply (Included_trans H); eapply anf_cvt_branches_subset; eassumption end.
                   exact H. }
               eapply Union_Disjoint_r; [ exact Hdis_cm1 | exact Hdis_cm2 ].
            -- intros rho1' rho2' m'' Hle Hpvs Hvars Hvar' Hextra'.
               eapply (proj1 (IHk m'' ltac:(lia))); try lia; try eassumption.
               ++ rewrite FromList_app. eapply Union_Disjoint_l.
                  ** eapply Disjoint_Setminus_r. eapply Included_refl.
                  ** eapply Disjoint_Included_r.
                     { eapply Included_trans. eapply Setminus_Included.
                       eapply anf_cvt_branches_subset. eassumption. }
                     eapply Disjoint_Included_l; [ | exact Hdis1 ].
                     intros z Hz. right. exact Hz.
               ++ rewrite FromList_app. eapply Union_Disjoint_l.
                  ** eapply Disjoint_Setminus_r. eapply Included_refl.
                  ** eapply Disjoint_Included_r.
                     { eapply Included_trans. eapply Setminus_Included.
                       eapply anf_cvt_branches_subset. eassumption. }
                     eapply Disjoint_Included_l; [ | exact Hdis2 ].
                     intros z Hz. right. exact Hz.
               ++ eapply Disjoint_Included_r.
                  { eapply Included_trans. eapply Setminus_Included.
                    eapply anf_cvt_branches_subset. eassumption. }
                  exact Hdis_cm1.
               ++ eapply Disjoint_Included_r.
                  { eapply Included_trans. eapply Setminus_Included.
                    eapply anf_cvt_branches_subset. eassumption. }
                  exact Hdis_cm2.
               ++ eapply Forall2_app; eassumption.
               ++ eapply preord_env_P_antimon; [ exact Hextra' | ].
                  intros v Hv. exact Hv.
               ++ intros j rho1'' rho2'' Hle' Hvar_r Henv_body Hpres.
                  eapply preord_exp_halt_compat;
                    [ eapply Hprops | eapply Hprops | exact Hvar_r ].
          * lia.
        + (* tail *)
          eapply IHbrs; try eassumption.
          * eapply Disjoint_Included_l.
            { intros z Hz. inv Hz; [ left; exact H | right; exact H ]. }
            eapply Disjoint_Included_r.
            { match goal with [ H : anf_cvt_rel' _ _ _ _ _ _ _ |- _ ] =>
                eapply Included_trans; [ eapply Setminus_Included | eapply anf_cvt_exp_subset; exact H ] end. }
            exact Hdis1.
          * eapply Disjoint_Included_l.
            { intros z Hz. inv Hz; [ left; exact H | right; exact H ]. }
            eapply Disjoint_Included_r.
            { match goal with [ H : anf_cvt_rel' _ _ _ _ _ _ _ |- _ ] =>
                eapply Included_trans; [ eapply Setminus_Included | eapply anf_cvt_exp_subset; exact H ] end. }
            exact Hdis2.
          * eapply Disjoint_Included_r.
            { match goal with [ H : anf_cvt_rel' _ _ _ _ _ _ _ |- _ ] =>
                eapply Included_trans; [ eapply Setminus_Included | eapply anf_cvt_exp_subset; exact H ] end. }
            exact Hdis_cm1.
          * eapply Disjoint_Included_r.
            { match goal with [ H : anf_cvt_rel' _ _ _ _ _ _ _ |- _ ] =>
                eapply Included_trans; [ eapply Setminus_Included | eapply anf_cvt_exp_subset; exact H ] end. }
            exact Hdis_cm2.
    }
  Qed.

  Lemma anf_cvt_val_alpha_equiv :
    forall k, anf_cvt_val_alpha_equiv_statement k.
  Proof.
    intro k. induction k as [k IHk] using lt_wf_rec1.
    unfold anf_cvt_val_alpha_equiv_statement.
    intros v. induction v using value_ind'; intros v1 v2 Hrel1 Hrel2.
    - (* Con_v dc vs *)
      inv Hrel1. inv Hrel2.
      rewrite preord_val_eq. simpl.
      split; [ congruence | ].
      (* H : Forall (fun v => forall v1 v2, anf_val_rel v v1 -> anf_val_rel v v2 -> preord_val cenv PG k v1 v2) vs
         H2 : Forall2 anf_val_rel vs vs'
         H3 : Forall2 anf_val_rel vs vs'0
         Goal : Forall2 (preord_val cenv PG k) vs' vs'0

         Proof: induct on H2, invert H3 at each step to get the pair of
         anf_val_rel hypotheses, invert H to get the componentwise IH,
         then apply the IH to produce preord_val for each component. *)
      clear -H H2 H3.
      revert vs' vs'0 H2 H3.
      induction vs as [| v0 vs_tl IHvs]; intros vs1 vs2 Hrel1 Hrel2.
      + inv Hrel1. inv Hrel2. constructor.
      + inv Hrel1. inv Hrel2. inv H. constructor.
        * match goal with
          | [ IH_head : forall v1 v2, anf_val_rel ?v v1 -> anf_val_rel ?v v2 -> _,
              Ha : anf_val_rel ?v ?a, Hb : anf_val_rel ?v ?b |- _ ] =>
            eapply IH_head; [ exact Ha | exact Hb ]
          end.
        * eapply IHvs; eassumption.
    - (* Clos_v *)
      inv Hrel1. inv Hrel2.
      eapply preord_val_fun.
      + simpl. rewrite Coqlib.peq_true. reflexivity.
      + simpl. rewrite Coqlib.peq_true. reflexivity.
      + intros rho1' j vs1 vs2 Hlen Hset1.
        destruct vs1 as [ | v_arg1 [ | ? ? ] ]; simpl in *; try congruence.
        destruct vs2 as [ | v_arg2 [ | ? ? ] ]; simpl in *; try congruence.
        inv Hset1.
        eexists. split; [reflexivity | ].
        intros Hlt Hall_args. inv Hall_args.
        eapply preord_exp_post_monotonic. now eapply HinclG.
        eapply (anf_cvt_alpha_equiv j); [lia | eassumption | eassumption | | | | | | | ].
        * (* Disjoint side 1: Disjoint (FromList (x :: names)) S1 *)
          rewrite FromList_cons.
          match goal with
          | [ Hdis : Disjoint _ (_ |: (_ |: _)) ?S |- Disjoint _ (_ :|: _) ?S ] =>
            eapply Disjoint_Included_l; [ | exact Hdis ];
            intros z Hz; inv Hz; [ left; assumption | do 2 right; assumption ]
          end.
        * (* Disjoint side 2 *)
          rewrite FromList_cons.
          match goal with
          | [ Hdis : Disjoint _ (_ |: (_ |: _)) ?S |- Disjoint _ (_ :|: _) ?S ] =>
            eapply Disjoint_Included_l; [ | exact Hdis ];
            intros z Hz; inv Hz; [ left; assumption | do 2 right; assumption ]
          end.
        * (* Disjoint cmap_vars S1 — now available from anf_rel_Clos *)
          eassumption.
        * eassumption.
        * (* Forall2 for x :: names and x0 :: names0 *)
          constructor.
          -- eapply preord_var_env_extend_eq. eassumption.
          -- eapply Forall2_preord_var_env_set.
             ++ eapply Forall2_preord_var_env_set.
                ** eapply anf_cvt_env_alpha_equiv_Forall2.
                   --- eapply IHk. lia.
                   --- eassumption.
                   --- eassumption.
                ** assumption.
                ** assumption.
             ++ match goal with
                | [ H : ~ ?y \in _ |: FromList ?ns |- ~ ?y \in FromList ?ns ] =>
                  intros Hc; apply H; right; exact Hc
                end.
             ++ match goal with
                | [ H : ~ ?y \in _ |: FromList ?ns |- ~ ?y \in FromList ?ns ] =>
                  intros Hc; apply H; right; exact Hc
                end.
        * (* preord_env_P (cmap_vars_of ...) for the closure body *)
          (* For each cmap var v with dep in e:
             Both global_env_rels give the same source body, same eval,
             so anf_val_rel src anf_v1 and anf_val_rel src anf_v2.
             By IHk: preord_val j anf_v1 anf_v2.
             Then peeling the M.set layers. *)
          eapply preord_env_P_set_not_in_P_l.
          eapply preord_env_P_set_not_in_P_r.
          eapply preord_env_P_set_not_in_P_l.
          eapply preord_env_P_set_not_in_P_r.
          ** (* Core: preord_env_P for cmap vars in rho/rho0 *)
             intros cv Hcv v1' Hget1.
             destruct Hcv as [kk [Hkin Hlk]].
             match goal with
             | [ Hge1 : global_env_rel _ _ ?rho1_,
                 Hge2 : global_env_rel _ _ ?rho2_ |- _ ] =>
               destruct (Hge1 kk cv Hkin Hlk) as (decl1 & body1 & av1 & Hdecl1 & Hbody1 & Hget_av1 & Hval_rel1);
               destruct (Hge2 kk cv Hkin Hlk) as (decl2 & body2 & av2 & Hdecl2 & Hbody2 & Hget_av2 & Hval_rel2)
             end.
             rewrite Hget_av1 in Hget1. inv Hget1.
             eexists. split; [ exact Hget_av2 | ].
             assert (Heq_decl : decl1 = decl2)
               by (unfold declared_constant in *; congruence).
             subst decl2.
             assert (Heq_body : body1 = body2) by congruence. subst body2.
             (* Use global_env_evaluates to get an eval witness *)
             destruct (global_env_evaluates kk decl1 body1 Hdecl1 Hbody1)
               as [src_v [fv [tv Heval_witness]]].
             eapply (IHk j Hlt src_v).
             ++ exact (Hval_rel1 src_v fv tv Heval_witness).
             ++ exact (Hval_rel2 src_v fv tv Heval_witness).
          Ltac solve_cmap_disj' :=
            eapply Disjoint_Singleton_r; intros [?kk [_ ?Hlk]];
            match goal with
            | [ Hd : Disjoint _ cmap_vars (_ |: _) |- _ ] =>
              first [
                eapply Hd; constructor; [ eexists; eassumption | left; reflexivity ] |
                eapply Hd; constructor; [ eexists; eassumption | right; left; reflexivity ] ]
            end.
          ** solve_cmap_disj'.
          ** solve_cmap_disj'.
          ** solve_cmap_disj'.
          ** solve_cmap_disj'.
        * (* Continuation: Ehalt *)
          intros j0 rho1'' rho2'' Hle Hvar_cont Henv_cont _.
          eapply preord_exp_halt_compat.
          -- eapply Hprops.
          -- eapply Hprops.
          -- exact Hvar_cont.
    - (* ClosFix_v *)
      inversion Hrel1; subst.
      (* Save global_env_rel for side 1 before second inversion overwrites it *)
      match goal with
      | [ Hge : global_env_rel _ _ ?r |- _ ] => rename Hge into Hge_rho1
      end.
      inversion Hrel2; subst.
      (* We need preord_val for f/f0 in their respective Bs/Bs0 bundles.
         Both sides come from the same mfix at the same index n. *)
      (* Extract find_def for both sides using anf_fix_rel_find_def_ext *)
      assert (Hval_IH : forall j, j < k -> anf_cvt_val_alpha_equiv_statement j)
        by (intros; eapply IHk; lia).
      (* We prove preord_val for ALL function pairs in the bundle simultaneously.
         For each index i, fnames[i]/fnames0[i] map to related closures. *)
      (* Prove preord_val for ALL function pairs in the bundle simultaneously.
         We need well-founded induction on the step index to handle mutual
         recursion: at step j, the fixpoint closures are related at j because
         preord_val_fun at level j only needs body proofs at j' < j. *)
      assert (Hfix_val : forall j_fix, j_fix <= k -> forall i g1 g2,
        nth_error fnames i = Some g1 ->
        nth_error fnames0 i = Some g2 ->
        preord_val cenv PG j_fix (Vfun rho Bs g1) (Vfun rho0 Bs0 g2)).
      { intro j_fix. induction j_fix as [j_fix IHj_fix] using lt_wf_rec1.
        intros Hle_fix i g1 g2 Hg1 Hg2.
        (* Find the two anf_fix_rel and NoDup hypotheses *)
        match goal with
        | [ Hfr1 : anf_fix_rel _ _ _ _ _ Bs _,
            Hfr2 : anf_fix_rel _ _ _ _ _ Bs0 _,
            Hnd1 : NoDup fnames, Hnd2 : NoDup fnames0,
            Hdcm1 : Disjoint _ cmap_vars S1,
            Hdcm2 : Disjoint _ cmap_vars ?S0_ |- _ ] =>
        destruct (anf_fix_rel_nth_lambda _ _ _ _ _ _ _ _ _ Hfr1 Hg1)
          as (d_i & na_i & e_body_i & Hnth_mfix_i & Hbody_i);
        destruct (anf_fix_rel_find_def_full _ _ _ _ _ _ _ _ _ _ _ _ Hfr1 Hg1 Hnth_mfix_i Hbody_i Hnd1 Hdcm1)
          as (x1_i & C1_i & r1_i & Sb1_i & Sb2_i & Hfind1_i & Hcvt1_i & Hdis_b1_i & Hfresh_b1_i & Hdis_cm_b1_i & Hcm_x1_i);
        destruct (anf_fix_rel_find_def_full _ _ _ _ _ _ _ _ _ _ _ _ Hfr2 Hg2 Hnth_mfix_i Hbody_i Hnd2 Hdcm2)
          as (x2_i & C2_i & r2_i & Sb3_i & Sb4_i & Hfind2_i & Hcvt2_i & Hdis_b2_i & Hfresh_b2_i & Hdis_cm_b2_i & Hcm_x2_i)
        end.
        eapply preord_val_fun.
        - exact Hfind1_i.
        - exact Hfind2_i.
        - intros rho1' j vs1 vs2 Hlen Hset1.
          destruct vs1 as [ | va1 [ | ? ? ] ]; simpl in *; try congruence.
          destruct vs2 as [ | va2 [ | ? ? ] ]; simpl in *; try congruence.
          inv Hset1.
          eexists. split; [reflexivity | ].
          intros Hlt Hall_args. inv Hall_args.
          eapply preord_exp_post_monotonic. now eapply HinclG.
          eapply (anf_cvt_alpha_equiv j); [lia | exact Hcvt1_i | exact Hcvt2_i | | | | | | | ].
          + (* Disjoint (FromList (x1_i :: rev fnames ++ names)) Sb1_i *)
            eapply Disjoint_Included_l; [ | exact Hdis_b1_i ].
            intros z Hz.
            unfold FromList, In in Hz. simpl in Hz.
            destruct Hz as [Heq | Hin_app].
            * subst. left. reflexivity.
            * apply List.in_app_iff in Hin_app. destruct Hin_app as [Hin_rev | Hin_names].
              -- right. left. unfold FromList, Ensembles.In. exact (proj2 (List.in_rev _ _) Hin_rev).
              -- right. right. exact Hin_names.
          + (* Disjoint side 2 *)
            eapply Disjoint_Included_l; [ | exact Hdis_b2_i ].
            intros z Hz.
            unfold FromList, In in Hz. simpl in Hz.
            destruct Hz as [Heq | Hin_app].
            * subst. left. reflexivity.
            * apply List.in_app_iff in Hin_app. destruct Hin_app as [Hin_rev | Hin_names].
              -- right. left. unfold FromList, Ensembles.In. exact (proj2 (List.in_rev _ _) Hin_rev).
              -- right. right. exact Hin_names.
          + (* Disjoint cmap_vars Sb1_i *)
            exact Hdis_cm_b1_i.
          + (* Disjoint cmap_vars Sb3_i *)
            exact Hdis_cm_b2_i.
          + (* Forall2 for x1_i :: rev fnames ++ names / x2_i :: rev fnames0 ++ names0 *)
            constructor.
            * eapply preord_var_env_extend_eq. eassumption.
            * eapply Forall2_preord_var_env_set.
              -- eapply Forall2_app.
                 ++ (* rev fnames / rev fnames0: mutual fixpoints *)
                    eapply All_Forall.Forall2_rev.
                    eapply Forall2_from_nth_error.
                    ** (* length fnames = length fnames0 *)
                       match goal with
                       | [ Hfrl : anf_fix_rel _ _ _ ?fl1 _ _ _,
                           Hfr2 : anf_fix_rel _ _ _ ?fl2 _ _ _ |- _ ] =>
                         assert (Hlen_eq :
                           Datatypes.length fl1 = Datatypes.length fl2)
                           by (erewrite anf_fix_rel_fnames_length by exact Hfrl;
                               erewrite anf_fix_rel_fnames_length by exact Hfr2;
                               reflexivity);
                         exact Hlen_eq
                       end.
                    ** intros idx fa fb Hfa Hfb.
                       intros va Hget_va.
                       rewrite def_funs_eq in Hget_va.
                       2: { eapply anf_fix_rel_name_in_fundefs. eassumption.
                            eapply nth_error_In. exact Hfa. }
                       inv Hget_va.
                       eexists. split.
                       { rewrite def_funs_eq. reflexivity.
                         eapply anf_fix_rel_name_in_fundefs. eassumption.
                         eapply nth_error_In. exact Hfb. }
                       eapply IHj_fix; try lia; eassumption.
                 ++ (* names / names0: captured env *)
                    eapply Forall2_preord_var_env_def_funs.
                    ** eapply anf_cvt_env_alpha_equiv_Forall2.
                       --- eapply Hval_IH. lia.
                       --- eassumption.
                       --- eassumption.
                    ** (* names disjoint from name_in_fundefs Bs *)
                       eapply Disjoint_Included_r.
                       --- eapply anf_fix_rel_name_in_fundefs. eassumption.
                       --- match goal with
                           | [ H : Disjoint _ (FromList names) (FromList fnames) |- _ ] =>
                             exact H
                           end.
                    ** (* names0 disjoint from name_in_fundefs Bs0 *)
                       eapply Disjoint_Included_r.
                       --- eapply anf_fix_rel_name_in_fundefs. eassumption.
                       --- match goal with
                           | [ H : Disjoint _ (FromList names0) (FromList fnames0) |- _ ] =>
                             exact H
                           end.
              -- (* ~ x1_i \in FromList (rev fnames ++ names) *)
                 intros Hin. apply Hfresh_b1_i.
                 unfold FromList, Ensembles.In in *. apply List.in_app_iff in Hin.
                 destruct Hin as [Hin | Hin].
                 ++ left. exact (proj2 (List.in_rev _ _) Hin).
                 ++ right. exact Hin.
              -- intros Hin. apply Hfresh_b2_i.
                 unfold FromList, Ensembles.In in *. apply List.in_app_iff in Hin.
                 destruct Hin as [Hin | Hin].
                 ++ left. exact (proj2 (List.in_rev _ _) Hin).
                 ++ right. exact Hin.
          + (* preord_env_P cmap_vars_of ... *)
            eapply preord_env_P_set_not_in_P_l.
            eapply preord_env_P_set_not_in_P_r.
            * (* Core: preord_env_P for cmap vars in rho / rho0 *)
              intros cv Hcv v1' Hget1.
              destruct Hcv as [kk [Hkin Hlk]].
              (* term_global_deps e_body_i ⊆ mfix_global_deps mfix *)
              assert (Hkin_mfix : KernameSet.In kk (mfix_global_deps mfix)).
              { unfold mfix_global_deps.
                eapply fold_left_kset_union_elem with (x := d_i).
                - eapply nth_error_In. exact Hnth_mfix_i.
                - simpl. rewrite Hbody_i. simpl. exact Hkin. }
              destruct (Hge_rho1 kk cv Hkin_mfix Hlk) as (decl1 & body1 & av1 & Hdecl1 & Hbody1 & Hget_av1 & Hval_rel1).
              match goal with
              | [ Hge2 : global_env_rel _ _ ?r2 |- _ ] =>
                destruct (Hge2 kk cv Hkin_mfix Hlk) as (decl2 & body2 & av2 & Hdecl2 & Hbody2 & Hget_av2 & Hval_rel2)
              end.
              (* cv is a cmap variable, hence not in name_in_fundefs *)
              rewrite def_funs_neq in Hget1.
              2: { intros Hc. match goal with
                   | [ Hd : Disjoint _ cmap_vars (FromList names :|: FromList fnames) |- _ ] =>
                     eapply Hd; constructor; [ exists kk; exact Hlk |
                     right; eapply anf_fix_rel_name_in_fundefs; [eassumption | exact Hc ]]
                   end. }
              rewrite Hget_av1 in Hget1. inv Hget1.
              eexists. split.
              { rewrite def_funs_neq.
                - exact Hget_av2.
                - intros Hc. match goal with
                  | [ Hd : Disjoint _ cmap_vars (FromList names0 :|: FromList fnames0) |- _ ] =>
                    eapply Hd; constructor; [ exists kk; exact Hlk |
                    right; eapply anf_fix_rel_name_in_fundefs; [eassumption | exact Hc ]]
                  end. }
              assert (Heq_decl : decl1 = decl2)
                by (unfold declared_constant in *; congruence).
              subst decl2.
              assert (Heq_body : body1 = body2) by congruence. subst body2.
              destruct (global_env_evaluates kk decl1 body1 Hdecl1 Hbody1)
                as [src_v [fv [tv Heval_witness]]].
              eapply (Hval_IH j ltac:(lia) src_v).
              ++ exact (Hval_rel1 src_v fv tv Heval_witness).
              ++ exact (Hval_rel2 src_v fv tv Heval_witness).
            * (* ~ x2_i ∈ cmap_vars_of *)
              eapply Disjoint_Singleton_r. intros [kk0 [_ Hlk0]].
              apply Hcm_x2_i. exists kk0. exact Hlk0.
            * (* ~ x1_i ∈ cmap_vars_of *)
              eapply Disjoint_Singleton_r. intros [kk0 [_ Hlk0]].
              apply Hcm_x1_i. exists kk0. exact Hlk0.
          + (* Continuation: Ehalt *)
            intros j0 rho1'' rho2'' Hle Hvar_cont Henv_cont _.
            eapply preord_exp_halt_compat.
            * eapply Hprops.
            * eapply Hprops.
            * exact Hvar_cont. }
      (* Now use Hfix_val at index n *)
      match goal with
      | [ Hn1 : nth_error fnames ?n = Some ?f1,
          Hn2 : nth_error fnames0 ?n = Some ?f2 |- _ ] =>
        exact (Hfix_val k (Nat.le_refl k) n f1 f2 Hn1 Hn2)
      end.
  Qed.

  End Alpha_Equiv.

End ANF_Val.
