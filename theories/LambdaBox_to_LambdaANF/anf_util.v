(* Utility definitions and lemmas for ANF correctness proof.
   Defines source value type, value relations between EAst evaluation
   results and LambdaANF values. *)

(** Stdlib *)
From Stdlib Require Import ZArith.ZArith Lists.List Arith Ensembles.

(** MetaRocq *)
From MetaRocq.Erasure Require Import EAst.
From MetaRocq.Common Require Import BasicAst.

(** CompCert *)
From compcert Require lib.Maps.

(** CertiRocq *)
From CertiRocq.LambdaANF Require Import cps ctx Ensembles_util.
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

End ANF_Val.
