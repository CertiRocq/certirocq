(* Utility definitions and lemmas for ANF correctness proof.
   Defines source value type, value relations between EAst evaluation
   results and LambdaANF values. *)

(** Stdlib *)
From Stdlib Require Import ZArith.ZArith Lists.List Arith Ensembles
     Relations.Relation_Definitions micromega.Lia.

(** MetaRocq *)
From MetaRocq.Erasure Require Import EAst.
From MetaRocq.Common Require Import BasicAst.

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

  Context (func_tag default_tag : positive)
          (cnstrs : conId_map)
          (cmap : const_map).

  (** Shorthand for the relational spec, partially applied with tags *)
  Definition anf_cvt_rel' (tgm : conId_map) (cmap : const_map) :=
    ANF.anf_cvt_rel func_tag default_tag tgm cmap.
  Definition anf_cvt_rel_args' (tgm : conId_map) (cmap : const_map) :=
    ANF.anf_cvt_rel_args func_tag default_tag tgm cmap.
  Definition anf_cvt_rel_mfix' (tgm : conId_map) (cmap : const_map) :=
    ANF.anf_cvt_rel_mfix func_tag default_tag tgm cmap.
  Definition anf_cvt_rel_branches' (tgm : conId_map) (cmap : const_map) :=
    ANF.anf_cvt_rel_branches func_tag default_tag tgm cmap.


  (** ** Environment and consistency relations *)

  Definition anf_env_rel' (P : value -> val -> Prop) (vn : list var)
             (vs : list value) (rho : M.t val) :=
    Forall2 (fun v x => exists v', M.get x rho = Some v' /\ P v v') vs vn.

  Definition env_consistent (vn : list var) (rho : list value) : Prop :=
    forall i j x,
      nth_error vn i = Some x ->
      nth_error vn j = Some x ->
      nth_error rho i = nth_error rho j.


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

        nth_error fnames n = Some f ->

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


  (** ** Result variable is consumed from S *)

  Lemma anf_cvt_result_not_in_output S e vn S' C x :
    anf_cvt_rel' cnstrs cmap S e vn S' C x ->
    Disjoint _ (FromList vn) S ->
    Disjoint _ (fun v => exists k, lookup_const cmap k = Some v) S ->
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

  Definition anf_cvt_alpha_equiv_statement k :=
    anf_cvt_exp_alpha_equiv k.

  Lemma anf_cvt_alpha_equiv :
    forall k, anf_cvt_alpha_equiv_statement k.
  Proof.
    (* This proof requires ~800 lines of mutual induction.
       It follows the old proof at LambdaBoxLocal_to_LambdaANF_anf_util.v:899-1667.
       The proof uses well-founded induction on k, then induction on the
       first anf_cvt_rel derivation. Each case inverts the second derivation
       and uses compatibility lemmas from logical_relations.v. *)
    admit.
  Admitted.

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
    - (* Clos_v vs na e:
         Both anf_val_rel inversions give Vfun with Fcons structure.
         preord_val for Vfun requires: when called with related args at j < k,
         the bodies produce related results.
         The body proof uses anf_cvt_alpha_equiv at step j < k, which relates
         the two ANF conversions of the closure body e. *)
      inv Hrel1. inv Hrel2.
      rewrite preord_val_eq. simpl.
      (* Goal: for all related args at j < k, find_def matches and
         bodies are related after set_lists + def_funs *)
      intros vs1 vs2 j t xs1' e1' rho1' Hlen Hfind1 Hset1.
      (* find_def for Fcons f func_tag [x] body Fnil = Some (func_tag, [x], body) when queried at f *)
      simpl in Hfind1.
      destruct (M.elt_eq _ _) as [_ | Hneq]; [ | congruence ].
      inv Hfind1.
      (* set_lists [x1] vs1 (def_funs ... rho1 rho1) = Some rho1' *)
      destruct vs1 as [ | v_arg1 [ | ? ?]]; simpl in Hset1; try congruence.
      inv Hset1.
      (* Now find corresponding f2 side *)
      simpl.
      destruct (M.elt_eq _ _) as [_ | Hneq2]; [ | congruence ].
      destruct vs2 as [ | v_arg2 [ | ? ?]]; [ simpl in Hlen; congruence | | simpl in Hlen; lia ].
      simpl.
      do 3 eexists. split; [ reflexivity | ]. split; [ reflexivity | ].
      intros Hlt Hargs.
      (* Convert goal from preord_exp PG PG to preord_exp P1 PG *)
      eapply preord_exp_post_monotonic. exact HinclG.
      (* Now apply anf_cvt_alpha_equiv at step j (j < k, so j ≤ j) *)
      eapply (anf_cvt_alpha_equiv j); [ lia | eassumption | eassumption | | | | ].
      + (* Disjoint (FromList (x :: names)) S1
           H5: Disjoint ({x} ∪ ({f} ∪ FromList names)) S1
           FromList (x::names) = {x} ∪ FromList names ⊆ {x} ∪ ({f} ∪ FromList names) *)
        rewrite FromList_cons.
        eapply Disjoint_Included_l; [ | eassumption ].
        intros z Hz. inv Hz.
        * left. assumption.
        * do 2 right. assumption.
      + (* Disjoint (FromList (x0 :: names0)) S0 *)
        rewrite FromList_cons.
        eapply Disjoint_Included_l; [ | eassumption ].
        intros z Hz. inv Hz.
        * left. assumption.
        * do 2 right. assumption.
      + (* Forall2 (preord_var_env PG j rho1' rho2') (x :: names) (x0 :: names0)
           rho1' = M.set x v_arg1 (M.set f vf1 rho)
           rho2' = M.set x0 v_arg2 (M.set f0 vf2 rho0)
           Head: x↦v_arg1 and x0↦v_arg2 are related (from Hargs)
           Tail: names/names0 unaffected by the sets (disjointness),
                 related via anf_cvt_env_alpha_equiv_Forall2 + IHk *)
        inv Hargs.
        constructor.
        * (* preord_var_env PG j rho1' rho2' x x0 *)
          intros v1' Hget1. rewrite M.gss in Hget1. inv Hget1.
          eexists. split; [ rewrite M.gss; reflexivity | ].
          eapply preord_val_monotonic; [ eassumption | lia ].
        * (* Forall2 (preord_var_env PG j rho1' rho2') names names0 *)
          eapply Forall2_preord_var_env_set.
          2:{ intros Hc. match goal with [ H : ~ _ \in _ |: FromList _ |- _ ] => apply H; right; exact Hc end. }
          2:{ intros Hc. match goal with [ H : ~ _ \in _ |: FromList _ |- _ ] => apply H; right; exact Hc end. }
          eapply Forall2_preord_var_env_set; [ | assumption | assumption ].
          eapply anf_cvt_env_alpha_equiv_Forall2.
          -- eapply IHk. exact Hlt.
          -- eassumption.
          -- eassumption.
      + (* Continuation: preord_exp P1 PG j0 (Ehalt r1, rho1') (Ehalt r0, rho2')
           Follows from preord_exp_halt_compat since r1/r0 are related in rho1'/rho2'. *)
        intros j0 rho1'' rho2'' Hle Hvar_r _ _.
        eapply preord_exp_halt_compat.
        * (* post_OOT' *)
          eapply Hprops.
        * (* post_base' *)
          eapply Hprops.
        * exact Hvar_r.
    - (* ClosFix_v vs mfix n:
         Both anf_val_rel inversions give Vfun rho Bs f where Bs are mutual
         function definitions from anf_fix_rel. preord_val for Vfun requires
         that when called with related args at j < k, the bodies produce
         related results.
         Strategy: invert both relations, extract the nth function via
         anf_fix_rel_find_def_ext, then use anf_cvt_alpha_equiv + nested
         well-founded induction on the fix index for the Forall2 of the
         mutual functions. *)
      inv Hrel1. inv Hrel2.
      rewrite preord_val_eq. simpl.
      (* Goal: for all related args at j < k, find_def matches and bodies related *)
      intros vs1 vs2 j t xs1' e1' rho1' Hlen Hfind1 Hset1.
      (* Extract nth mfix entry and its lambda body *)
      match goal with
      | [ Hfix1 : anf_fix_rel ?fn ?nm ?S1 ?fn ?mx ?Bs1 ?S2,
          Hnth1 : nth_error ?fn ?n = Some ?f1 |- _ ] =>
        edestruct (anf_fix_rel_nth_lambda _ _ _ _ _ _ _ _ _ Hfix1 Hnth1)
          as (d_fix & na_fix & e_body_fix & Hmfix_nth & Hbody_lam)
      end.
      (* Use anf_fix_rel_find_def_ext on first side *)
      match goal with
      | [ Hfix1 : anf_fix_rel fnames names _ fnames mfix Bs _,
          Hnth_fn : nth_error fnames n = Some f,
          Hnd1 : NoDup fnames |- _ ] =>
        edestruct (anf_fix_rel_find_def_ext _ _ _ _ _ _ _ _ _ _ _ _
                     Hfix1 Hnth_fn Hmfix_nth Hbody_lam Hnd1)
          as (x_pc1 & C_body1 & r_body1 & S_b1_1 & S_b1_2 &
              Hfdef1 & Hcvt1 & Hdis_b1 & Hfresh1)
      end.
      (* Match find_def result with Hfind1 *)
      rewrite Hfdef1 in Hfind1. inv Hfind1.
      (* Process set_lists on first side: xs1' = [x_pc1], vs1 must be singleton *)
      destruct vs1 as [ | v_arg1 [ | ? ?]]; simpl in Hset1; try congruence.
      inv Hset1.
      (* Use anf_fix_rel_find_def_ext on second side *)
      match goal with
      | [ Hfix2 : anf_fix_rel fnames0 names0 _ fnames0 mfix Bs0 _,
          Hnth_fn2 : nth_error fnames0 n = Some f0,
          Hnd2 : NoDup fnames0 |- _ ] =>
        edestruct (anf_fix_rel_find_def_ext _ _ _ _ _ _ _ _ _ _ _ _
                     Hfix2 Hnth_fn2 Hmfix_nth Hbody_lam Hnd2)
          as (x_pc2 & C_body2 & r_body2 & S_b2_1 & S_b2_2 &
              Hfdef2 & Hcvt2 & Hdis_b2 & Hfresh2)
      end.
      (* Provide existentials for second side *)
      destruct vs2 as [ | v_arg2 [ | ? ?]]; [ simpl in Hlen; congruence | | simpl in Hlen; lia ].
      simpl.
      do 3 eexists. split; [ exact Hfdef2 | ]. split; [ reflexivity | ].
      intros Hlt Hargs.
      (* Convert goal from preord_exp PG PG to preord_exp P1 PG *)
      eapply preord_exp_post_monotonic. exact HinclG.
      (* Apply anf_cvt_alpha_equiv at step j *)
      eapply (anf_cvt_alpha_equiv j); [ lia | eassumption | eassumption | | | | ].
      + (* Disjoint (FromList (x_pc1 :: rev fnames ++ names)) S_b1_1 *)
        eapply Disjoint_Included_l; [ | exact Hdis_b1 ].
        intros z Hz. unfold FromList, In in Hz. simpl in Hz.
        destruct Hz as [Heq | Hz].
        * subst. left. constructor.
        * right. apply in_app_iff in Hz. destruct Hz as [Hz | Hz].
          -- left. unfold FromList, In. apply in_rev. assumption.
          -- right. unfold FromList, In. assumption.
      + (* Disjoint (FromList (x_pc2 :: rev fnames0 ++ names0)) S_b2_1 *)
        eapply Disjoint_Included_l; [ | exact Hdis_b2 ].
        intros z Hz. unfold FromList, In in Hz. simpl in Hz.
        destruct Hz as [Heq | Hz].
        * subst. left. constructor.
        * right. apply in_app_iff in Hz. destruct Hz as [Hz | Hz].
          -- left. unfold FromList, In. apply in_rev. assumption.
          -- right. unfold FromList, In. assumption.
      + (* Forall2 (preord_var_env PG j rho1' rho2')
              (x_pc1 :: rev fnames ++ names) (x_pc2 :: rev fnames0 ++ names0) *)
        inv Hargs.
        constructor.
        * (* Head: x_pc1 ↦ v_arg1, x_pc2 ↦ v_arg2 *)
          intros v1' Hget1. rewrite M.gss in Hget1. inv Hget1.
          eexists. split; [ rewrite M.gss; reflexivity | ].
          eapply preord_val_monotonic; [ eassumption | lia ].
        * (* Tail: rev fnames ++ names / rev fnames0 ++ names0 *)
          eapply Forall2_preord_var_env_set.
          2:{ intros Hc. apply Hfresh1.
              unfold FromList, In in Hc. apply in_app_iff in Hc.
              destruct Hc as [Hc | Hc].
              - left. unfold FromList, In. apply in_rev. assumption.
              - right. unfold FromList, In. assumption. }
          2:{ intros Hc. apply Hfresh2.
              unfold FromList, In in Hc. apply in_app_iff in Hc.
              destruct Hc as [Hc | Hc].
              - left. unfold FromList, In. apply in_rev. assumption.
              - right. unfold FromList, In. assumption. }
          (* Now need Forall2 over (rev fnames ++ names) (rev fnames0 ++ names0)
             in def_funs environment *)
          eapply Forall2_app.
          -- (* rev fnames / rev fnames0: mutual fixpoints *)
             (* Each fname maps to a ClosFix_v value via anf_val_rel on both sides,
                so we can use IHk to get preord_val *)
             eapply All_Forall.Forall2_rev.
             eapply Forall2_from_nth_error.
             ++ match goal with
                | [ Hfix1 : anf_fix_rel _ _ _ fnames mfix _ _,
                    Hfix2 : anf_fix_rel _ _ _ fnames0 mfix _ _ |- _ ] =>
                  pose proof (anf_fix_rel_fnames_length _ _ _ _ _ _ _ Hfix1) as Hlen1;
                  pose proof (anf_fix_rel_fnames_length _ _ _ _ _ _ _ Hfix2) as Hlen2;
                  lia
                end.
             ++ intros idx fi1 fi2 Hnth_fi1 Hnth_fi2.
                intros v1' Hget1.
                (* fi1 is a fname, so in def_funs Bs Bs rho rho, M.get fi1 = Some (Vfun rho Bs fi1) *)
                assert (Hget1' : M.get fi1 (def_funs Bs Bs rho rho) = Some (Vfun rho Bs fi1)).
                { eapply def_funs_eq.
                  match goal with
                  | [ Hfix1 : anf_fix_rel _ _ _ fnames mfix Bs _ |- _ ] =>
                    eapply (anf_fix_rel_name_in_fundefs _ _ _ _ _ _ _ Hfix1)
                  end.
                  eapply nth_error_In. exact Hnth_fi1. }
                rewrite Hget1' in Hget1. inv Hget1.
                eexists. split.
                ** eapply def_funs_eq.
                   match goal with
                   | [ Hfix2 : anf_fix_rel _ _ _ fnames0 mfix Bs0 _ |- _ ] =>
                     eapply (anf_fix_rel_name_in_fundefs _ _ _ _ _ _ _ Hfix2)
                   end.
                   eapply nth_error_In. exact Hnth_fi2.
                ** eapply IHk; [ exact Hlt | | ].
                   --- match goal with
                       | [ He : anf_env_rel' _ names vs rho,
                           Hec : env_consistent names vs,
                           Hnd : NoDup fnames,
                           Hd1 : Disjoint _ (FromList names :|: FromList fnames) _,
                           Hd2 : Disjoint _ (FromList names) (FromList fnames),
                           Hfr : anf_fix_rel fnames names _ fnames mfix Bs _ |- _ ] =>
                         eapply (anf_rel_ClosFix _ _ _ _ _ _ _ _ idx fi1);
                           [ exact He | exact Hec | exact Hnd | exact Hd1 | exact Hd2
                           | exact Hnth_fi1 | exact Hfr ]
                       end.
                   --- match goal with
                       | [ He : anf_env_rel' _ names0 vs rho0,
                           Hec : env_consistent names0 vs,
                           Hnd : NoDup fnames0,
                           Hd1 : Disjoint _ (FromList names0 :|: FromList fnames0) _,
                           Hd2 : Disjoint _ (FromList names0) (FromList fnames0),
                           Hfr : anf_fix_rel fnames0 names0 _ fnames0 mfix Bs0 _ |- _ ] =>
                         eapply (anf_rel_ClosFix _ _ _ _ _ _ _ _ idx fi2);
                           [ exact He | exact Hec | exact Hnd | exact Hd1 | exact Hd2
                           | exact Hnth_fi2 | exact Hfr ]
                       end.
          -- (* names / names0: environment variables *)
             eapply Forall2_preord_var_env_def_funs.
             ++ eapply anf_cvt_env_alpha_equiv_Forall2.
                ** eapply IHk. exact Hlt.
                ** match goal with [ H : anf_env_rel' _ names vs rho |- _ ] => exact H end.
                ** match goal with [ H : anf_env_rel' _ names0 vs rho0 |- _ ] => exact H end.
             ++ match goal with
                | [ Hfix1 : anf_fix_rel _ _ _ fnames mfix Bs _,
                    Hdis : Disjoint _ (FromList names) (FromList fnames) |- _ ] =>
                  eapply Disjoint_Included_r;
                    [ eapply (anf_fix_rel_name_in_fundefs _ _ _ _ _ _ _ Hfix1) | exact Hdis ]
                end.
             ++ match goal with
                | [ Hfix2 : anf_fix_rel _ _ _ fnames0 mfix Bs0 _,
                    Hdis : Disjoint _ (FromList names0) (FromList fnames0) |- _ ] =>
                  eapply Disjoint_Included_r;
                    [ eapply (anf_fix_rel_name_in_fundefs _ _ _ _ _ _ _ Hfix2) | exact Hdis ]
                end.
      + (* Continuation: Ehalt *)
        intros j0 rho1'' rho2'' Hle Hvar_r _ _.
        eapply preord_exp_halt_compat.
        * eapply Hprops.
        * eapply Hprops.
        * exact Hvar_r.
  Qed.

  End Alpha_Equiv.

End ANF_Val.
