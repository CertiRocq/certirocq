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
From CertiRocq.LambdaBox_to_LambdaANF Require Import common ANF fuel_sem.

Import ListNotations.


(** * ANF Value Relation *)

Section ANF_Val.

  Context (func_tag default_tag : positive)
          (tgm : conId_map)
          (cmap : const_map).

  (* Shorthands for the relational specs from ANF.v *)
  Let anf_cvt_rel' := anf_cvt_rel func_tag default_tag tgm cmap.
  Let anf_cvt_rel_args' := anf_cvt_rel_args func_tag default_tag tgm cmap.
  Let anf_cvt_rel_mfix' := anf_cvt_rel_mfix func_tag default_tag tgm cmap.
  Let anf_cvt_rel_branches' := anf_cvt_rel_branches func_tag default_tag tgm cmap.

  (** Generic environment relation: each source value at position i
      is related (via P) to the target value stored at variable vn[i]. *)
  Definition anf_env_rel' (P : fuel_sem.value -> val -> Prop)
             (vn : list var) (vs : list fuel_sem.value) (rho : M.t val) :=
    Forall2 (fun v x => exists v', M.get x rho = Some v' /\ P v v') vs vn.

  (** Fixpoint relation: relates a list of mutually recursive source definitions
      (each of which must be a lambda) to ANF fundefs.
      Each body is converted in a context extended with all fix names and
      a fresh argument variable. *)
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

  (** Environment consistency: if the same variable appears at two positions
      in the name list, the corresponding source values must be equal. *)
  Definition env_consistent (vn : list var) (rho : list fuel_sem.value) : Prop :=
    forall i j x,
      nth_error vn i = Some x ->
      nth_error vn j = Some x ->
      nth_error rho i = nth_error rho j.

  (** Main value relation. Relates source values to ANF target values.
      - Constructors: tag correspondence + recursive relation on fields
      - Closures: body has a relational derivation in extended context
      - Fix closures: all mutual bodies related via anf_fix_rel *)
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


  (** * Helper lemmas for anf_fix_rel *)

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

  (* Extract find_def from anf_fix_rel given nth_error on names and bodies *)
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


  (** * Subset lemmas for anf_cvt_rel *)

  (* Shared tactic for all 17 cases of the subset proof.
     Each case: S' ⊆ S by chaining IHs with Included_trans
     and dropping Setminus via Setminus_Included. *)
  Local Ltac subset_case :=
    unfold Ensembles.In; intros;
    first [ reflexivity
          | assumption
          | apply Setminus_Included
          | (eapply Setminus_Included_preserv; eassumption)
          | (eapply Setminus_Included_preserv;
             eapply Included_trans; [eassumption | eassumption])
          | (eapply Included_trans; [eassumption | eassumption])
          | (eapply Included_trans; [eassumption | apply Setminus_Included])
          | (eapply Included_trans; [eassumption |];
             eapply Included_trans; apply Setminus_Included)
          | (eapply Setminus_Included_preserv;
             eapply Included_trans; [eassumption |];
             eapply Included_trans; [eassumption |];
             eapply Included_trans; apply Setminus_Included)
          | (eapply Included_trans; [eassumption |];
             eapply Included_trans; [eassumption |]; apply Setminus_Included)
          | (eapply Included_trans; [eassumption |];
             eapply Included_trans; [apply Setminus_Included | eassumption]) ].

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
      anf_cvt_rel_args' S es vn S' C xs -> S' \subset S.
  Proof.
    apply (anf_cvt_rel_args_ind' func_tag default_tag tgm cmap
             P_sub P0_sub P1_sub P2_sub); subset_case.
  Qed.

  Lemma anf_cvt_mfix_subset :
    forall S mfix vn fnames S' fdefs,
      anf_cvt_rel_mfix' S mfix vn fnames S' fdefs -> S' \subset S.
  Proof.
    apply (anf_cvt_rel_mfix_ind' func_tag default_tag tgm cmap
             P_sub P0_sub P1_sub P2_sub); subset_case.
  Qed.

  Lemma anf_cvt_branches_subset :
    forall S ind brs n vn r S' pats,
      anf_cvt_rel_branches' S ind brs n vn r S' pats -> S' \subset S.
  Proof.
    apply (anf_cvt_rel_branches_ind' func_tag default_tag tgm cmap
             P_sub P0_sub P1_sub P2_sub); subset_case.
  Qed.


  (** * env_consistent lemmas *)

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
