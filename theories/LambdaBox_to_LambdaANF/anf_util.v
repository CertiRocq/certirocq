(* Value relations, alpha-equivalence, and utility lemmas for ANF correctness.
   Adapts LambdaBoxLocal_to_LambdaANF_anf_util.v to the new MetaRocq pipeline. *)

From Stdlib Require Import ZArith.ZArith Lists.List micromega.Lia Arith
     Ensembles Relations.Relation_Definitions.
From MetaRocq.Erasure Require Import EAst EAstUtils EGlobalEnv.
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

  Context {src_trace : Type}
          {Hf_src : @LambdaBox_resource nat}
          {Ht_src : @LambdaBox_resource src_trace}.

  Context (Σ : EAst.global_context).

  Let anf_cvt_rel' := anf_cvt_rel func_tag default_tag tgm cmap.

(* ================================================================= *)
(** * Value and Environment Relations                                  *)
(* ================================================================= *)

  Definition anf_env_rel' (P : fuel_sem.value -> val -> Prop)
             (vn : list var) (vs : list fuel_sem.value) (rho : M.t val) :=
    Forall2 (fun v x => exists v', M.get x rho = Some v' /\ P v v') vs vn.

  (** Relates cmap variables to their ANF values in a target environment,
      restricted to a set [D] of kernames. Parametric in the value relation
      [val_rel] so it can be used inside [anf_val_rel] (tie-the-knot pattern).
      States: if the global body evaluates to a value, that value is related
      to the target binding. Termination is assumed separately. *)
  Definition global_env_rel' (val_rel : fuel_sem.value -> val -> Prop)
             (D : kername -> Prop) (rho : M.t val) : Prop :=
    forall k v,
      D k ->
      lookup_const cmap k = Some v ->
      exists decl body anf_v,
        declared_constant Σ k decl /\
        decl.(EAst.cst_body) = Some body /\
        M.get v rho = Some anf_v /\
        (forall src_v f t,
           @eval_env_fuel _ Hf_src Ht_src Σ [] body (fuel_sem.Val src_v) f t ->
           val_rel src_v anf_v).

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
        ~ x \in cmap_vars cmap ->
        ~ f \in cmap_vars cmap ->
        ~ x \in f |: FromList names ->
        ~ f \in FromList names ->
        anf_cvt_rel' S1 e (x :: names) S2 C1 r1 ->
        global_env_rel' anf_val_rel
          (fun k => KernameSet.In k (term_global_deps e)) rho ->
        anf_val_rel (Clos_v vs na e)
                    (Vfun rho (Fcons f func_tag [x] (C1 |[ Ehalt r1 ]|) Fnil) f)
  | anf_rel_ClosFix :
      forall S1 S2 names fnames vs rho mfix Bs n f,
        anf_env_rel' anf_val_rel names vs rho ->
        env_consistent names vs ->
        NoDup fnames ->
        Disjoint _ (FromList names :|: FromList fnames) S1 ->
        Disjoint _ (cmap_vars cmap) S1 ->
        Disjoint _ (cmap_vars cmap) (FromList fnames) ->
        Disjoint _ (FromList names) (FromList fnames) ->
        nth_error fnames n = Some f ->
        anf_fix_rel fnames names S1 fnames mfix Bs S2 ->
        global_env_rel' anf_val_rel
          (fun k => Exists
            (fun d => KernameSet.In k (term_global_deps d.(EAst.dbody))) mfix) rho ->
        anf_val_rel (ClosFix_v vs mfix n) (Vfun rho Bs f).

  Definition anf_env_rel : list var -> list fuel_sem.value -> M.t val -> Prop :=
    anf_env_rel' anf_val_rel.

  Definition global_env_rel := global_env_rel' anf_val_rel.


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

  (* Like [anf_fix_rel_find_def] but derives the [nth_error mfix] and
     [dbody] facts from the [anf_fix_rel] induction. Also gives
     disjointness and freshness for the lambda parameter. *)
  Lemma anf_fix_rel_exists :
    forall fnames0 names0 S1 fnames_list mfix Bs S2 idx f,
      anf_fix_rel fnames0 names0 S1 fnames_list mfix Bs S2 ->
      nth_error fnames_list idx = Some f ->
      NoDup fnames_list ->
      exists (d : EAst.def EAst.term) (na : name) (e_body : EAst.term) (x_pc : var)
             (C_body : exp_ctx) (r_body : var)
             (S_body1 S_body2 : Ensemble var),
        nth_error mfix idx = Some d /\
        d.(EAst.dbody) = EAst.tLambda na e_body /\
        find_def f Bs = Some (func_tag, [x_pc], C_body |[ Ehalt r_body ]|) /\
        anf_cvt_rel' S_body1 e_body
                     (x_pc :: List.rev fnames0 ++ names0) S_body2 C_body r_body /\
        Disjoint var (x_pc |: (FromList fnames0 :|: FromList names0)) S_body1 /\
        ~ x_pc \in (FromList fnames0 :|: FromList names0).
  Proof.
    intros fnames0 names0 S1 fnames_list mfix Bs S2 idx f Hrel Hnth Hnd.
    revert idx f Hnth Hnd.
    induction Hrel; intros idx0 f0 Hnth Hnd.
    - destruct idx0; discriminate.
    - destruct idx0 as [| idx'].
      + simpl in Hnth. injection Hnth as Heq. subst.
        exists d, na, e1, x, C1, r1, S1', S2.
        split; [reflexivity | split; [eassumption | split; [| split; [| split]]]].
        * simpl. destruct (M.elt_eq f0 f0); [reflexivity | congruence].
        * eassumption.
        * (* Disjoint (x |: (FromList fnames0 :|: FromList names0)) S1' *)
          (* S1' ⊆ S1 \\ {x}, so x ∉ S1' and (fnames :|: names) ⊥ S1' *)
          eapply Union_Disjoint_l.
          -- (* {x} ⊥ S1': x ∉ S1' because S1' ⊆ S1 \\ {x} *)
             eapply Disjoint_Singleton_l.
             intro Hx. apply H2 in Hx. destruct Hx as [_ Hc].
             apply Hc. constructor.
          -- (* (fnames :|: names) ⊥ S1': from (fnames :|: names) ⊥ S1 and S1' ⊆ S1 *)
             eapply Disjoint_sym.
             eapply Disjoint_Included_l; [|eassumption].
             eapply Included_trans; [eassumption |]. eapply Setminus_Included.
        * intro Hc. eapply H0. constructor; [exact H1 | exact Hc].
      + simpl in Hnth.
        match goal with H : NoDup (_ :: _) |- _ =>
          inversion H as [| ? ? Hnotin Hnd_tl]; subst end.
        edestruct IHHrel as (d' & na' & e' & xp & Cp & rp & Sp1 & Sp2 &
                             Hnth_d & Hbod & Hfind & Hcvt & Hdis_p & Hfresh_p);
          [exact Hnth | exact Hnd_tl |].
        exists d', na', e', xp, Cp, rp, Sp1, Sp2.
        split; [simpl; exact Hnth_d | split; [exact Hbod |
        split; [| split; [| split]]]]; try assumption.
        simpl. destruct (M.elt_eq f0 f) as [Heq | Hneq].
        * exfalso. subst. apply Hnotin. eapply nth_error_In. exact Hnth.
        * exact Hfind.
  Qed.

  (* Build Forall2 from pointwise proof + length equality *)
  Lemma Forall2_from_nth_error {A B : Type} (R : A -> B -> Prop)
        (l1 : list A) (l2 : list B) :
    Datatypes.length l1 = Datatypes.length l2 ->
    (forall k a b, nth_error l1 k = Some a -> nth_error l2 k = Some b -> R a b) ->
    Forall2 R l1 l2.
  Proof.
    revert l2. induction l1; intros l2 Hlen H.
    - destruct l2; [constructor | simpl in Hlen; congruence].
    - destruct l2 as [| b l2']; [simpl in Hlen; congruence |].
      constructor.
      + apply (H 0); reflexivity.
      + apply IHl1.
        * simpl in Hlen. congruence.
        * intros k a' b' Ha' Hb'. exact (H (S k) a' b' Ha' Hb').
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

(* ----------------------------------------------------------------- *)
(** ** Relational Mfix Helpers                                        *)
(* ----------------------------------------------------------------- *)

  Lemma anf_cvt_rel_mfix_all_fun_name S mfix vn fnames S' fdefs :
    anf_cvt_rel_mfix func_tag default_tag tgm cmap S mfix vn fnames S' fdefs ->
    all_fun_name fdefs = fnames.
  Proof.
    intros H. induction H; simpl; congruence.
  Qed.

  Lemma anf_cvt_rel_mfix_find_def S mfix vn fnames S' fdefs :
    anf_cvt_rel_mfix func_tag default_tag tgm cmap S mfix vn fnames S' fdefs ->
    NoDup fnames ->
    forall i fi,
      nth_error fnames i = Some fi ->
      exists d na e_body xi C_body ri Si1 Si2,
        nth_error mfix i = Some d /\
        d.(EAst.dbody) = EAst.tLambda na e_body /\
        find_def fi fdefs = Some (func_tag, [xi], C_body |[ Ehalt ri ]|) /\
        anf_cvt_rel func_tag default_tag tgm cmap
                    (Si1 \\ [set xi]) e_body (xi :: vn) Si2 C_body ri /\
        xi \in Si1 /\ Si1 \subset S.
  Proof.
    intros Hrel Hnd.
    induction Hrel; intros i fi Hnth.
    - destruct i; discriminate.
    - destruct i as [| i'].
      + simpl in Hnth. inv Hnth.
        do 8 eexists.
        repeat split; try eassumption.
        * simpl. destruct (M.elt_eq fi fi); [reflexivity | congruence].
        * eapply Included_refl.
      + simpl in Hnth.
        match goal with H : NoDup (_ :: _) |- _ =>
          inversion H as [| ? ? Hnotin Hnd_tl]; subst end.
        edestruct IHHrel as (d' & na' & e' & xi' & C' & ri' & Si1' & Si2' &
                             Hnth_d & Hbody & Hfind & Hcvt & Hxi_in & Hsi_sub);
          [exact Hnd_tl | exact Hnth |].
        do 8 eexists.
        repeat split; try eassumption.
        * simpl. match goal with |- context [M.elt_eq fi ?f] =>
            destruct (M.elt_eq fi f) as [Heq | Hneq] end.
          -- exfalso. subst. apply Hnotin. eapply nth_error_In. exact Hnth.
          -- exact Hfind.
        * eapply Included_trans; [exact Hsi_sub |].
          eapply Included_trans; [eapply anf_cvt_exp_subset; eassumption |].
          eapply Setminus_Included.
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

  Context {src_trace : Type}
          {Hf_src : @LambdaBox_resource nat}
          {Ht_src : @LambdaBox_resource src_trace}.
  Context (Σ : EAst.global_context).

  Context (globals_terminate :
    forall k decl body,
      declared_constant Σ k decl ->
      decl.(EAst.cst_body) = Some body ->
      exists src_v f t,
        @eval_env_fuel _ Hf_src Ht_src Σ [] body (fuel_sem.Val src_v) f t).

  Context (func_tag default_tag : positive).

  Let anf_cvt_rel' := anf_cvt_rel func_tag default_tag tgm cmap.
  Let anf_cvt_rel_args' := anf_cvt_rel_args func_tag default_tag tgm cmap.
  Let anf_cvt_rel_mfix' := anf_cvt_rel_mfix func_tag default_tag tgm cmap.
  Let anf_cvt_rel_branches' := anf_cvt_rel_branches func_tag default_tag tgm cmap.
  Let anf_val_rel' := anf_val_rel func_tag default_tag tgm cmap Σ.


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
        proj_vars1 proj_vars2 acc1 acc2 e1 e2 n (S_extra : Ensemble var) :
    preord_var_env cenv PG k rho1 rho2 x1 x2 ->
    Forall2 (preord_var_env cenv PG k rho1 rho2) acc1 acc2 ->
    List.length proj_vars1 = List.length proj_vars2 ->
    NoDup proj_vars1 ->
    NoDup proj_vars2 ->
    Disjoint _ (FromList proj_vars1) (FromList acc1 :|: [set x1]) ->
    Disjoint _ (FromList proj_vars2) (FromList acc2 :|: [set x2]) ->
    (* Extra environment relation threaded through projection bindings *)
    preord_env_P cenv PG S_extra k rho1 rho2 ->
    Disjoint _ S_extra (FromList proj_vars1) ->
    Disjoint _ S_extra (FromList proj_vars2) ->
    (forall rho1' rho2' m',
        (m' <= k)%nat ->
        Forall2 (preord_var_env cenv PG m' rho1' rho2')
                proj_vars1 proj_vars2 ->
        Forall2 (preord_var_env cenv PG m' rho1' rho2')
                acc1 acc2 ->
        preord_var_env cenv PG m' rho1' rho2' x1 x2 ->
        preord_env_P cenv PG S_extra m' rho1' rho2' ->
        preord_exp cenv P1 PG m' (e1, rho1') (e2, rho2')) ->
    preord_exp cenv P1 PG k
               (ctx_bind_proj ctag x1 proj_vars1 n |[ e1 ]|, rho1)
               (ctx_bind_proj ctag x2 proj_vars2 n |[ e2 ]|, rho2).
  Proof.
    revert k rho1 rho2 x1 x2 ctag proj_vars2 acc1 acc2 e1 e2 n.
    induction proj_vars1;
      intros k rho1 rho2 x1 x2 ctag proj_vars2 acc1 acc2 e1 e2 n
             Hvar Hacc Hlen Hnd1 Hnd2 Hdis1 Hdis2
             Henv_extra Hdis_e1 Hdis_e2 Hexp.
    - (* Base: proj_vars1 = [] *)
      destruct proj_vars2; [| simpl in Hlen; congruence].
      cbn [ctx_bind_proj app_ctx_f].
      eapply Hexp; [lia | constructor | exact Hacc | exact Hvar |].
      intros v0 Hv0.
      eapply preord_var_env_monotonic; [eapply Henv_extra; exact Hv0 | lia].
    - (* Step: a :: proj_vars1 *)
      destruct proj_vars2 as [| v proj_vars2]; [simpl in Hlen; congruence |].
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
        * (* preord_env_P S_extra in extended env *)
          intros v0 Hv0.
          eapply preord_var_env_extend_neq.
          -- eapply preord_var_env_monotonic.
             ++ eapply Henv_extra. exact Hv0.
             ++ lia.
          -- intros Heq. subst. eapply Hdis_e1. constructor; [exact Hv0 | now left].
          -- intros Heq. subst. eapply Hdis_e2. constructor; [exact Hv0 | now left].
        * (* Disjoint S_extra (FromList proj_vars1) — tail *)
          eapply Disjoint_Included_r; [| exact Hdis_e1].
          intros z Hz. now right.
        * (* Disjoint S_extra (FromList proj_vars2) — tail *)
          eapply Disjoint_Included_r; [| exact Hdis_e2].
          intros z Hz. now right.
        * (* Inner continuation *)
          intros rho1' rho2' m' Hm' Hpv Hacc' Hvar' Henv_extra_inner.
          inversion Hacc' as [| ? ? ? ? Hhd Htl]; subst.
          eapply Hexp.
          -- lia.
          -- constructor; [exact Hhd | exact Hpv].
          -- exact Htl.
          -- exact Hvar'.
          -- exact Henv_extra_inner.
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
      (* Global constant bindings are related (restricted to deps of [e]) *)
      preord_env_P cenv PG (cmap_deps cmap e) m rho1 rho2 ->
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
      preord_env_P cenv PG (cmap_deps_list cmap args) m rho1 rho2 ->
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
      Disjoint _ (cmap_vars cmap) (FromList fnames1) ->
      Disjoint _ (cmap_vars cmap) (FromList fnames2) ->
      Disjoint _ (FromList fnames1) (FromList outer_vars1) ->
      Disjoint _ (FromList fnames2) (FromList outer_vars2) ->
      Forall2 (preord_var_env cenv PG m rho1 rho2) outer_vars1 outer_vars2 ->
      preord_env_P cenv PG (cmap_deps_mfix cmap mfix) m rho1 rho2 ->
      Forall2 (preord_var_env cenv PG m
                 (def_funs B1 B1 rho1 rho1) (def_funs B2 B2 rho2 rho2))
              fnames1 fnames2.

  (** Two ANF conversions of the same case branches produce
      [preord_exp]-related [Ecase] expressions. *)
  Definition anf_cvt_branches_alpha_equiv_for
             (ind : inductive) (brs : list (list name * EAst.term))
             (n : N) k :=
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
      preord_env_P cenv PG (cmap_deps_brs cmap brs) m rho1 rho2 ->
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
      (* IH for head t: need cmap_deps cmap t ⊆ cmap_deps_list cmap (t::args') *)
      eapply IH_hd; [lia | eassumption | eassumption | assumption | assumption
                     | assumption | assumption | assumption
                     | eapply preord_env_P_antimon; [exact Hglob |];
                       eapply cmap_vars_of_monotone; intros kn Hkn; apply Exists_cons_hd; exact Hkn
                     |].
      (* Continuation: after head, convert tail *)
      intros j rho1' rho2' Hj Hvar_hd Henv' Htransfer.
      eapply IHargs; [exact IH_tl | lia | eassumption | eassumption
                      | eapply Disjoint_Included_r; [eapply anf_cvt_exp_subset; eassumption | assumption]
                      | eapply Disjoint_Included_r; [eapply anf_cvt_exp_subset; eassumption | assumption]
                      | eapply Disjoint_Included_r; [eapply anf_cvt_exp_subset; eassumption | assumption]
                      | eapply Disjoint_Included_r; [eapply anf_cvt_exp_subset; eassumption | assumption]
                      | exact Henv'
                      (* cmap_deps_list cmap args' ⊆ cmap_deps_list cmap (t::args') *)
                      | intros v0 Hv0; eapply Htransfer;
                        [eapply Hglob; eapply cmap_vars_of_monotone;
                         [| exact Hv0]; intros kn Hkn; apply Exists_cons_tl; exact Hkn
                        | intros Hc; eapply Hdis_cm1; constructor;
                          [eapply cmap_vars_of_subset; exact Hv0 | exact Hc]
                        | intros Hc; eapply Hdis_cm2; constructor;
                          [eapply cmap_vars_of_subset; exact Hv0 | exact Hc]]
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
    revert n Hall.
    induction brs as [| [lnames e_br] brs' IHbrs];
    intros n Hall pats1 pats2 m y1 y2 vars1 vars2 rho1 rho2 S1 S2 S3 S4
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
          eapply ctx_bind_proj_Forall2_compat
            with (acc1 := vars1) (acc2 := vars2)
                 (S_extra := cmap_deps_brs cmap ((lnames, e_br) :: brs')).
          -- eapply preord_var_env_monotonic with (k := m). exact Hvar_y.
             apply Nat.lt_le_incl. exact Hlt.
          -- eapply Forall2_preord_var_env_monotonic with (k := m); [| exact Henv].
             apply Nat.lt_le_incl. exact Hlt.
          -- exact Hlen_eq.
          -- assumption. (* NoDup vars *)
          -- assumption. (* NoDup vars0 *)
          -- (* Disjoint pvars1 from vars1 :|: {y1} *)
             eapply Disjoint_Included_l.
             ++ match goal with H : FromList ?vs \subset _ |- _ =>
                  eapply Included_trans; [exact H | eapply anf_cvt_branches_subset; eassumption] end.
             ++ eapply Disjoint_Included_r; [| eapply Disjoint_sym; exact Hdis1].
                rewrite Union_commut. eapply Included_refl.
          -- (* Disjoint pvars2 from vars2 :|: {y2} *)
             eapply Disjoint_Included_l.
             ++ match goal with H : FromList ?vs \subset _ |- _ =>
                  eapply Included_trans; [exact H | eapply anf_cvt_branches_subset; eassumption] end.
             ++ eapply Disjoint_Included_r; [| eapply Disjoint_sym; exact Hdis2].
                rewrite Union_commut. eapply Included_refl.
          -- (* preord_env_P (cmap_deps_brs cmap ((lnames,e_br)::brs')) at step m' *)
             intros v0 Hv0.
             eapply preord_var_env_monotonic; [eapply Hglob; exact Hv0 | lia].
          -- (* Disjoint (cmap_deps_brs ...) (FromList vars): via cmap_vars_of_subset *)
             eapply Disjoint_Included_l; [eapply cmap_vars_of_subset |].
             eapply Disjoint_Included_r; [| exact Hdis_cm1].
             match goal with H : FromList ?vs \subset _ |- _ =>
               eapply Included_trans; [exact H | eapply anf_cvt_branches_subset; eassumption] end.
          -- (* Disjoint (cmap_deps_brs ...) (FromList vars0): via cmap_vars_of_subset *)
             eapply Disjoint_Included_l; [eapply cmap_vars_of_subset |].
             eapply Disjoint_Included_r; [| exact Hdis_cm2].
             match goal with H : FromList ?vs \subset _ |- _ =>
               eapply Included_trans; [exact H | eapply anf_cvt_branches_subset; eassumption] end.
          -- (* continuation: body alpha equiv after projections *)
             intros rho1' rho2' m'' Hle Hpvs Hvars Hvar' Henv_extra_proj.
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
             (* IH_hd needs cmap_deps cmap e_br ⊆ cmap_deps_brs cmap ((lnames,e_br)::brs') *)
             ++ eapply preord_env_P_antimon; [exact Henv_extra_proj |].
                eapply cmap_vars_of_monotone. intros kn Hkn. apply Exists_cons_hd. exact Hkn.
             ++ (* body continuation: Ehalt *)
                intros j rho1'' rho2'' Hle' Hvar_r Henv_body Hpres.
                eapply preord_exp_halt_compat;
                  [eapply Hprops | eapply Hprops | exact Hvar_r].
        * lia.
      + (* tail: cmap_deps_brs cmap brs' ⊆ cmap_deps_brs cmap ((lnames,e_br)::brs') *)
        eapply (IHbrs (n + 1)%N IH_tl); try eassumption.
        eapply preord_env_P_antimon; [exact Hglob |].
        eapply cmap_vars_of_monotone. intros kn Hkn. apply Exists_cons_tl. exact Hkn.
  Qed.

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
  Proof.
    intros Hall HIHk.
    unfold anf_cvt_mfix_alpha_equiv_for.
    intros B1 B2 fnames1 fnames2 m outer_vars1 outer_vars2 rho1 rho2
           S1 S2 S3 S4
           Hm Hrel1 Hrel2 Hnd1 Hnd2 Hlen_fn Hlen_ov
           Hdis1 Hdis2 Hdis_cm1 Hdis_cm2
           Hdis_cm_fn1 Hdis_cm_fn2
           Hdis_fn_ov1 Hdis_fn_ov2 Henv Hglob.
    (* Well-founded induction on m *)
    revert m Hm Henv Hglob.
    induction m as [m IHm] using lt_wf_rec1.
    intros Hm Henv Hglob.
    (* Build Forall2 pointwise *)
    eapply Forall2_from_nth_error.
    - exact Hlen_fn.
    - intros i fi fi' Hn_fi Hn_fi'.
      (* fi ∈ name_in_fundefs B1, fi' ∈ name_in_fundefs B2 *)
      assert (Hni1 : name_in_fundefs B1 fi).
      { apply (proj2 (Same_set_all_fun_name _)).
        erewrite anf_cvt_rel_mfix_all_fun_name by eassumption.
        unfold FromList, Ensembles.In. eapply nth_error_In. exact Hn_fi. }
      assert (Hni2 : name_in_fundefs B2 fi').
      { apply (proj2 (Same_set_all_fun_name _)).
        erewrite anf_cvt_rel_mfix_all_fun_name by eassumption.
        unfold FromList, Ensembles.In. eapply nth_error_In. exact Hn_fi'. }
      (* Unfold def_funs lookups *)
      intros v1 Hget1.
      rewrite (def_funs_eq _ _ _ _ _ Hni1) in Hget1. inv Hget1.
      eexists. split. { exact (def_funs_eq _ _ _ _ _ Hni2). }
      (* Extract find_def and body derivations *)
      edestruct (anf_cvt_rel_mfix_find_def _ _ _ _ _ _ _ _ _ _ Hrel1 Hnd1 i fi Hn_fi)
        as (d1 & na1 & e_body & xi1 & Ci1 & ri1 & Si1_1 & Si2_1 &
            Hnth_d1 & Hbody1 & Hfind1 & Hcvt1 & Hxi1_in & Hsi1_sub).
      edestruct (anf_cvt_rel_mfix_find_def _ _ _ _ _ _ _ _ _ _ Hrel2 Hnd2 i fi' Hn_fi')
        as (d2 & na2 & e_body' & xi2 & Ci2 & ri2 & Si1_2 & Si2_2 &
            Hnth_d2 & Hbody2 & Hfind2 & Hcvt2 & Hxi2_in & Hsi2_sub).
      (* Both derivations convert the same source term *)
      assert (Hd_eq : d1 = d2) by congruence. subst d2.
      assert (Hbody_eq : e_body = e_body')
        by (assert (Htmp : EAst.tLambda na1 e_body = EAst.tLambda na2 e_body') by congruence;
            congruence).
      subst e_body'.
      (* preord_val via preord_val_fun *)
      eapply preord_val_fun.
      + exact Hfind1.
      + exact Hfind2.
      + intros rho1' j vs1 vs2 Hlen_vs Hset1.
        (* xs = [xi], so vs must be singletons *)
        destruct vs1 as [| v_arg1 [| ? ?]]; simpl in *; try congruence.
        destruct vs2 as [| v_arg2 [| ? ?]]; simpl in *; try congruence.
        inv Hset1.
        eexists. split. { reflexivity. }
        intros Hlt Hall_args. inv Hall_args.
        match goal with H : Forall2 _ [] [] |- _ => clear H end.
        (* rho1' = M.set xi1 v_arg1 (def_funs B1 B1 rho1 rho1)
           rho2' = M.set xi2 v_arg2 (def_funs B2 B2 rho2 rho2) *)
        eapply preord_exp_post_monotonic. { exact HinclG. }
        (* Forall2 at step j for all function names *)
        assert (Hfn_env_j :
          Forall2 (preord_var_env cenv PG j
                     (def_funs B1 B1 rho1 rho1) (def_funs B2 B2 rho2 rho2))
                  fnames1 fnames2).
        { eapply IHm; [lia | lia
                       | eapply Forall2_preord_var_env_monotonic; [| exact Henv]; lia
                       | intros v0 Hv0; eapply preord_var_env_monotonic;
                         [eapply Hglob; exact Hv0 | lia]]. }
        (* Body alpha-equiv at step j *)
        eapply (HIHk j ltac:(lia) e_body).
        * lia.
        * exact Hcvt1.
        * exact Hcvt2.
        * (* Disjoint (FromList (xi1 :: rev fnames1 ++ outer_vars1)) (Si1_1 \\ {xi1}) *)
          rewrite FromList_cons. eapply Union_Disjoint_l.
          -- eapply Disjoint_Singleton_l. intros [_ Hc]. apply Hc. constructor.
          -- eapply Disjoint_Included_r.
             ++ eapply Included_trans; [eapply Setminus_Included | exact Hsi1_sub].
             ++ eapply Disjoint_Included_l; [| exact Hdis1].
                intros z Hz. unfold FromList, Ensembles.In in *.
                apply in_app_or in Hz. destruct Hz as [Hz | Hz].
                ** left. apply in_rev in Hz. exact Hz.
                ** right. exact Hz.
        * rewrite FromList_cons. eapply Union_Disjoint_l.
          -- eapply Disjoint_Singleton_l. intros [_ Hc]. apply Hc. constructor.
          -- eapply Disjoint_Included_r.
             ++ eapply Included_trans; [eapply Setminus_Included | exact Hsi2_sub].
             ++ eapply Disjoint_Included_l; [| exact Hdis2].
                intros z Hz. unfold FromList, Ensembles.In in *.
                apply in_app_or in Hz. destruct Hz as [Hz | Hz].
                ** left. apply in_rev in Hz. exact Hz.
                ** right. exact Hz.
        * (* Disjoint cmap (Si1_1 \\ {xi1}) *)
          eapply Disjoint_Included_r; [| exact Hdis_cm1].
          eapply Included_trans; [eapply Setminus_Included | exact Hsi1_sub].
        * eapply Disjoint_Included_r; [| exact Hdis_cm2].
          eapply Included_trans; [eapply Setminus_Included | exact Hsi2_sub].
        * (* Forall2 for (xi1 :: rev fnames1 ++ outer_vars1) in extended envs *)
          constructor.
          -- (* xi1/xi2: argument binding *)
             eapply preord_var_env_extend_eq. eassumption.
          -- (* rev fnames ++ outer_vars *)
             eapply Forall2_preord_var_env_set.
             ++ eapply Forall2_app.
                ** (* rev fnames: from Hfn_env_j through def_funs *)
                   eapply All_Forall.Forall2_rev. exact Hfn_env_j.
                ** (* outer_vars: from Henv through def_funs *)
                   eapply Forall2_preord_var_env_def_funs.
                   --- eapply Forall2_preord_var_env_monotonic; [| exact Henv]. lia.
                   --- eapply Disjoint_Included_r.
                       +++ exact (proj1 (Same_set_all_fun_name _)).
                       +++ erewrite anf_cvt_rel_mfix_all_fun_name by eassumption.
                           eapply Disjoint_sym. exact Hdis_fn_ov1.
                   --- eapply Disjoint_Included_r.
                       +++ exact (proj1 (Same_set_all_fun_name _)).
                       +++ erewrite anf_cvt_rel_mfix_all_fun_name by eassumption.
                           eapply Disjoint_sym. exact Hdis_fn_ov2.
             ++ (* xi1 ∉ FromList (rev fnames1 ++ outer_vars1) *)
                rewrite FromList_app.
                intros Hin. inv Hin.
                ** eapply Hdis1. constructor.
                   --- left. unfold FromList, Ensembles.In in *. apply in_rev in H. exact H.
                   --- exact (Hsi1_sub _ Hxi1_in).
                ** eapply Hdis1. constructor.
                   --- right. exact H.
                   --- exact (Hsi1_sub _ Hxi1_in).
             ++ rewrite FromList_app.
                intros Hin. inv Hin.
                ** eapply Hdis2. constructor.
                   --- left. unfold FromList, Ensembles.In in *. apply in_rev in H. exact H.
                   --- exact (Hsi2_sub _ Hxi2_in).
                ** eapply Hdis2. constructor.
                   --- right. exact H.
                   --- exact (Hsi2_sub _ Hxi2_in).
        * (* preord_env_P (cmap_deps cmap e_body): antimon from cmap_deps_mfix *)
          eapply preord_env_P_def_funs_set.
          -- eapply preord_env_P_antimon.
             ++ intros v0 Hv0.
                eapply preord_var_env_monotonic; [eapply Hglob; exact Hv0 | lia].
             ++ (* cmap_deps cmap e_body ⊆ cmap_deps_mfix cmap mfix *)
                eapply cmap_vars_of_monotone. intros kn Hkn.
                apply Exists_exists. exists d1. split.
                ** eapply nth_error_In. exact Hnth_d1.
                ** rewrite Hbody1. simpl. exact Hkn.
          -- (* Disjoint (cmap_deps cmap e_body) (name_in_fundefs B1) *)
             eapply Disjoint_Included_l; [eapply cmap_vars_of_subset |].
             eapply Disjoint_Included_r; [exact (proj1 (Same_set_all_fun_name _)) |].
             erewrite anf_cvt_rel_mfix_all_fun_name by eassumption. exact Hdis_cm_fn1.
          -- (* Disjoint (cmap_deps cmap e_body) (name_in_fundefs B2) *)
             eapply Disjoint_Included_l; [eapply cmap_vars_of_subset |].
             eapply Disjoint_Included_r; [exact (proj1 (Same_set_all_fun_name _)) |].
             erewrite anf_cvt_rel_mfix_all_fun_name by eassumption. exact Hdis_cm_fn2.
          -- intros Hc. eapply Hdis_cm1. constructor;
               [eapply cmap_vars_of_subset; exact Hc | exact (Hsi1_sub _ Hxi1_in)].
          -- intros Hc. eapply Hdis_cm2. constructor;
               [eapply cmap_vars_of_subset; exact Hc | exact (Hsi2_sub _ Hxi2_in)].
        * (* Continuation: Ehalt *)
          intros j' rho1'' rho2'' Hle' Hvar_r Henv_body Hpres.
          eapply preord_exp_halt_compat;
            [eapply Hprops | eapply Hprops | exact Hvar_r].
  Qed.


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
                 [| intros Heq; subst; eapply Hdis_cm1; constructor;
                    [eapply cmap_vars_of_subset; exact Hv0 | eassumption]
                  | intros Heq; subst; eapply Hdis_cm2; constructor;
                    [eapply cmap_vars_of_subset; exact Hv0 | eassumption]].
               eapply preord_var_env_extend_neq;
                 [| intros Heq; subst; eapply Hdis_cm1; constructor;
                    [eapply cmap_vars_of_subset; exact Hv0 |];
                    eapply Setminus_Included; eassumption
                  | intros Heq; subst; eapply Hdis_cm2; constructor;
                    [eapply cmap_vars_of_subset; exact Hv0 |];
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
      (* IH1 for binding b: cmap_deps cmap b ⊆ cmap_deps cmap (tLetIn na b t) *)
      eapply IHe1; [lia | eassumption | eassumption | assumption | assumption
                    | assumption | assumption | assumption
                    | eapply preord_env_P_antimon; [exact Hglob |];
                      eapply cmap_vars_of_monotone; intros kn Hkn;
                      apply KernameSet.union_spec; left; exact Hkn
                    |].
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
      - (* preord_env_P cmap_deps t: cmap_deps t ⊆ cmap_deps (tLetIn ..), via Htransfer *)
        intros v Hv_in.
        eapply Htransfer.
        + eapply Hglob.
          eapply cmap_vars_of_monotone; [| exact Hv_in].
          intros kn Hkn. apply KernameSet.union_spec. right. exact Hkn.
        + intros Hc. eapply Hdis_cm1. constructor;
            [eapply cmap_vars_of_subset; exact Hv_in | exact Hc].
        + intros Hc. eapply Hdis_cm2. constructor;
            [eapply cmap_vars_of_subset; exact Hv_in | exact Hc].
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
      (* IH1 for function u: cmap_deps cmap u ⊆ cmap_deps cmap (tApp u v) *)
      eapply IHe1; [lia | eassumption | eassumption | assumption | assumption
                    | assumption | assumption | assumption
                    | eapply preord_env_P_antimon; [exact Hglob |];
                      eapply cmap_vars_of_monotone; intros kn Hkn;
                      apply KernameSet.union_spec; left; exact Hkn
                    |].
      intros j rho1' rho2' Hj Hvar_x1 Henv' Htransfer1.
      (* IH2 for argument v: cmap_deps cmap v ⊆ cmap_deps cmap (tApp u v) *)
      eapply IHe2; [lia | eassumption | eassumption
                    | eapply Disjoint_Included_r; [eapply anf_cvt_exp_subset; eassumption | assumption]
                    | eapply Disjoint_Included_r; [eapply anf_cvt_exp_subset; eassumption | assumption]
                    | eapply Disjoint_Included_r; [eapply anf_cvt_exp_subset; eassumption | assumption]
                    | eapply Disjoint_Included_r; [eapply anf_cvt_exp_subset; eassumption | assumption]
                    | exact Henv'
                    | intros v0 Hv0; eapply Htransfer1;
                      [eapply Hglob; eapply cmap_vars_of_monotone;
                       [| exact Hv0]; intros kn Hkn; apply KernameSet.union_spec; right; exact Hkn
                      | intros Hc; eapply Hdis_cm1; constructor;
                        [eapply cmap_vars_of_subset; exact Hv0 | exact Hc]
                      | intros Hc; eapply Hdis_cm2; constructor;
                        [eapply cmap_vars_of_subset; exact Hv0 | exact Hc]]
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
      - eapply Hglob. exists s. split.
        + apply KernameSet.singleton_spec. reflexivity.
        + eassumption.
      - assumption.
      - intros; assumption. }

    { (* tConstruct ind c args: comp_ctx_f C_args (Econstr_c x ctag xs Hole_c) *)
      inv Hrel1. inv Hrel2.
      rewrite <- !app_ctx_f_fuse.
      (* Use args helper with X: cmap_deps_list cmap args ⊆ cmap_deps cmap (tConstruct ...) *)
      eapply anf_cvt_args_alpha_from_all;
        [exact X | lia | eassumption | eassumption
        | eapply Disjoint_Included_r; [apply Setminus_Included | exact Hdis1]
        | eapply Disjoint_Included_r; [apply Setminus_Included | exact Hdis2]
        | eapply Disjoint_Included_r; [apply Setminus_Included | exact Hdis_cm1]
        | eapply Disjoint_Included_r; [apply Setminus_Included | exact Hdis_cm2]
        | exact Henv
        | eapply preord_env_P_antimon; [exact Hglob |];
          eapply cmap_vars_of_monotone; intros kname Hkname;
          destruct ind as [ind_mind ind_idx]; simpl;
          apply Exists_fold_left_union; exact Hkname
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
        eapply IHe.
        + lia.
        + eassumption.
        + eassumption.
        + eapply Disjoint_Included_r; [eapply Setminus_Included |].
          eapply Disjoint_Included_r; [eapply Setminus_Included | exact Hdis1].
        + eapply Disjoint_Included_r; [eapply Setminus_Included |].
          eapply Disjoint_Included_r; [eapply Setminus_Included | exact Hdis2].
        + eapply Disjoint_Included_r; [eapply Setminus_Included |].
          eapply Disjoint_Included_r; [eapply Setminus_Included | exact Hdis_cm1].
        + eapply Disjoint_Included_r; [eapply Setminus_Included |].
          eapply Disjoint_Included_r; [eapply Setminus_Included | exact Hdis_cm2].
        + (* Forall2 vars in M.set f (Vfun ..) rho — f ∉ vars *)
          eapply Forall2_preord_var_env_set.
          * eapply Forall2_preord_var_env_monotonic with (k := m); [lia | exact Henv].
          * intro Hc. eapply Hdis1. constructor; [exact Hc | eassumption].
          * intro Hc. eapply Hdis2. constructor; [exact Hc | eassumption].
        + (* preord_env_P (cmap_deps cmap mch) in M.set f rho:
             cmap_deps cmap mch ⊆ cmap_deps cmap (tCase ...) via fold_left *)
          intros v0 Hv0. eapply preord_var_env_extend_neq.
          * eapply preord_var_env_monotonic.
            -- eapply Hglob.
               eapply cmap_vars_of_monotone; [| exact Hv0]. intros kn Hkn.
               apply KernameSet.union_spec. right.
               apply fold_left_union_In. exact Hkn.
            -- lia.
          * intros Heq. subst. eapply Hdis_cm1.
            constructor; [eapply cmap_vars_of_subset; exact Hv0 | eassumption].
          * intros Heq. subst. eapply Hdis_cm2.
            constructor; [eapply cmap_vars_of_subset; exact Hv0 | eassumption].
        + (* Continuation: Eletapp r f func_tag [x_mch] e_k *)
          intros j rho1' rho2' Hle Hvar_xscr Henvvars Hpres.
          eapply preord_exp_letapp_compat.
          * now eapply Hprops.
          * now eapply Hprops.
          * now eapply Hprops.
          * (* f1 f2 related in continuation env *)
            eapply Hpres.
            -- (* preord_var_env in def_funs env for f *)
               intros v Hg. rewrite def_funs_eq in Hg. 2: { simpl; now left. }
               inv Hg.
               eexists. split. { rewrite def_funs_eq. reflexivity. simpl; now left. }
               eapply preord_val_fun.
               ++ simpl. rewrite Coqlib.peq_true. reflexivity.
               ++ simpl. rewrite Coqlib.peq_true. reflexivity.
               ++ intros rho_b j' vs1 vs2 Hlen Hset.
                  destruct vs1 as [| v1 [| ? ?]]; simpl in *; try congruence.
                  destruct vs2 as [| v2 [| ? ?]]; simpl in *; try congruence.
                  inv Hset.
                  eexists. split. { reflexivity. }
                  intros Hlt Hall. inv Hall.
                  eapply preord_exp_post_monotonic. { exact HinclG. }
                  (* Branches alpha-equiv at step j' *)
                  assert (Hall_j : All (fun br : list name * EAst.term =>
                            anf_cvt_exp_alpha_equiv_for (snd br) j') brs).
                  { clear - IHk Hlt Hle Hm.
                    induction brs; constructor; [eapply IHk; lia | eapply IHbrs]. }
                  eapply (anf_cvt_branches_alpha_from_all j' ind brs 0%N Hall_j).
                  ** lia.
                  ** eassumption.
                  ** eassumption.
                  ** (* Disjoint ([set y] :|: FromList vars1) S_brs1 *)
                     eapply Disjoint_Included_r; [eapply anf_cvt_exp_subset; eassumption |].
                     eapply Union_Disjoint_l.
                     --- eapply Disjoint_Singleton_l. intros [_ Hn]. apply Hn. constructor.
                     --- eapply Disjoint_Included_r; [eapply Setminus_Included |].
                         eapply Disjoint_Included_r; [eapply Setminus_Included | exact Hdis1].
                  ** eapply Disjoint_Included_r; [eapply anf_cvt_exp_subset; eassumption |].
                     eapply Union_Disjoint_l.
                     --- eapply Disjoint_Singleton_l. intros [_ Hn]. apply Hn. constructor.
                     --- eapply Disjoint_Included_r; [eapply Setminus_Included |].
                         eapply Disjoint_Included_r; [eapply Setminus_Included | exact Hdis2].
                  ** (* Disjoint cmap S_brs *)
                     eapply Disjoint_Included_r; [eapply anf_cvt_exp_subset; eassumption |].
                     eapply Disjoint_Included_r; [eapply Setminus_Included |].
                     eapply Disjoint_Included_r; [eapply Setminus_Included | exact Hdis_cm1].
                  ** eapply Disjoint_Included_r; [eapply anf_cvt_exp_subset; eassumption |].
                     eapply Disjoint_Included_r; [eapply Setminus_Included |].
                     eapply Disjoint_Included_r; [eapply Setminus_Included | exact Hdis_cm2].
                  ** (* Forall2 vars in M.set y (M.set f rho) *)
                     eapply Forall2_preord_var_env_set.
                     --- eapply Forall2_preord_var_env_set.
                         +++ eapply Forall2_preord_var_env_monotonic with (k := m);
                               [lia | exact Henv].
                         +++ intro Hc. eapply Hdis1. constructor; [exact Hc | eassumption].
                         +++ intro Hc. eapply Hdis2. constructor; [exact Hc | eassumption].
                     --- intro Hc. eapply Hdis1. constructor; [exact Hc |].
                         match goal with H : Ensembles.In _ (Setminus _ _ _) _ |- _ =>
                           eapply Setminus_Included; exact H end.
                     --- intro Hc. eapply Hdis2. constructor; [exact Hc |].
                         match goal with H : Ensembles.In _ (Setminus _ _ _) _ |- _ =>
                           eapply Setminus_Included; exact H end.
                  ** (* preord_var_env y1 y2 *)
                     eapply preord_var_env_extend_eq. eassumption.
                  ** (* preord_env_P (cmap_deps_brs cmap brs) in M.set y (M.set f rho):
                        cmap_deps_brs brs ⊆ cmap_deps (tCase ..) via fold_left *)
                     intros v0 Hv0.
                     eapply preord_var_env_extend_neq.
                     --- eapply preord_var_env_extend_neq.
                         +++ eapply preord_var_env_monotonic.
                             *** eapply Hglob.
                                 eapply cmap_vars_of_monotone; [| exact Hv0].
                                 intros kn Hkn. apply KernameSet.union_spec. right.
                                 apply Exists_fold_left_union. exact Hkn.
                             *** lia.
                         +++ intros Heq. subst. eapply Hdis_cm1.
                             constructor; [eapply cmap_vars_of_subset; exact Hv0 | eassumption].
                         +++ intros Heq. subst. eapply Hdis_cm2.
                             constructor; [eapply cmap_vars_of_subset; exact Hv0 | eassumption].
                     --- intros Heq. subst. eapply Hdis_cm1.
                         constructor; [eapply cmap_vars_of_subset; exact Hv0 |].
                         match goal with H : Ensembles.In _ (Setminus _ _ _) _ |- _ =>
                           eapply Setminus_Included; exact H end.
                     --- intros Heq. subst. eapply Hdis_cm2.
                         constructor; [eapply cmap_vars_of_subset; exact Hv0 |].
                         match goal with H : Ensembles.In _ (Setminus _ _ _) _ |- _ =>
                           eapply Setminus_Included; exact H end.
            -- (* f ∉ S1 \\ {f} \\ {y} — absurd since f ∈ S1 but f ∉ S1\\{f} *)
               intros [Hc _]. inv Hc. match goal with H : ~ _ |- _ => apply H; constructor end.
            -- intros [Hc _]. inv Hc. match goal with H : ~ _ |- _ => apply H; constructor end.
          * (* args: [x_scr] *)
            constructor; [exact Hvar_xscr | constructor].
          * (* letapp continuation: Hcont *)
            intros m' v1 v2 Hlt' Hval.
            eapply Hcont.
            -- lia.
            -- intros w Hg. rewrite M.gss in Hg. inv Hg.
               eexists. split. { rewrite M.gss. reflexivity. }
               eapply preord_val_monotonic. exact Hval. lia.
            -- eapply Forall2_preord_var_env_set.
               ++ eapply (Forall2_preord_var_env_monotonic j); [lia | exact Henvvars].
               ++ intro Hr. apply (Disjoint_In_l _ _ _ Hdis1 Hr).
                  eapply Setminus_Included. eapply Setminus_Included.
                  eapply anf_cvt_exp_subset. eassumption.
                  eapply anf_cvt_branches_subset. eassumption. eassumption.
               ++ intro Hr. apply (Disjoint_In_l _ _ _ Hdis2 Hr).
                  eapply Setminus_Included. eapply Setminus_Included.
                  eapply anf_cvt_exp_subset. eassumption.
                  eapply anf_cvt_branches_subset. eassumption. eassumption.
            -- intros a b Hvar Ha Hb.
               eapply preord_var_env_extend_neq.
               ++ eapply preord_var_env_monotonic.
                  ** eapply Hpres.
                     --- eapply preord_var_env_extend_neq.
                         +++ eapply preord_var_env_monotonic. exact Hvar. lia.
                         +++ intros Heq. subst. apply Ha. eassumption.
                         +++ intros Heq. subst. apply Hb. eassumption.
                     --- intro Hc. apply Ha.
                         eapply Setminus_Included. eapply Setminus_Included. exact Hc.
                     --- intro Hc. apply Hb.
                         eapply Setminus_Included. eapply Setminus_Included. exact Hc.
                  ** lia.
               ++ intros Heq. subst. apply Ha.
                  eapply Setminus_Included. eapply Setminus_Included.
                  eapply anf_cvt_exp_subset. eassumption.
                  eapply anf_cvt_branches_subset. eassumption. eassumption.
               ++ intros Heq. subst. apply Hb.
                  eapply Setminus_Included. eapply Setminus_Included.
                  eapply anf_cvt_exp_subset. eassumption.
                  eapply anf_cvt_branches_subset. eassumption. eassumption. }
    { (* tProj p c: comp_ctx_f C_c (Eproj_c y ctag n x Hole_c) *)
      inv Hrel1. inv Hrel2.
      rewrite <- !app_ctx_f_fuse. simpl.
      (* Use IHe for sub-expression c: cmap_deps cmap c ⊆ cmap_deps cmap (tProj p c) *)
      eapply IHe; [lia | eassumption | eassumption | assumption | assumption | assumption | assumption | assumption
                  | eapply preord_env_P_antimon; [exact Hglob |];
                    eapply cmap_vars_of_monotone; intros kn Hkn;
                    apply KernameSet.union_spec; right; exact Hkn
                  |].
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
    { (* tFix mfix idx: Efun1_c fdefs Hole_c, result = fnames[idx] *)
      (* Save original derivations before inversion *)
      pose proof Hrel1 as Horig1. pose proof Hrel2 as Horig2.
      inv Hrel1. inv Hrel2. simpl.
      (* Get Forall2 for all function names at step m-1 *)
      assert (Hfn_env : Forall2 (preord_var_env cenv PG (m - 1)
                (def_funs fdefs fdefs rho1 rho1) (def_funs fdefs0 fdefs0 rho2 rho2))
                fnames fnames0).
      { eapply anf_cvt_mfix_alpha_from_all.
        - exact X.
        - intros j0 Hj0 e0. eapply IHk. lia.
        - lia.
        - eassumption.
        - eassumption.
        - eassumption.
        - eassumption.
        - match goal with
          | [H1 : Datatypes.length ?f1 = _, H2 : Datatypes.length ?f2 = _ |- _] => congruence
          end.
        - eapply Forall2_length. exact Henv.
        - (* Disjoint (fnames :|: vars1) (S1 \\ FromList fnames) *)
          eapply Union_Disjoint_l.
          + eapply Disjoint_Setminus_r. eapply Included_refl.
          + eapply Disjoint_Included_r; [eapply Setminus_Included | exact Hdis1].
        - eapply Union_Disjoint_l.
          + eapply Disjoint_Setminus_r. eapply Included_refl.
          + eapply Disjoint_Included_r; [eapply Setminus_Included | exact Hdis2].
        - (* Disjoint cmap (S1 \\ FromList fnames) *)
          eapply Disjoint_Included_r; [eapply Setminus_Included | exact Hdis_cm1].
        - eapply Disjoint_Included_r; [eapply Setminus_Included | exact Hdis_cm2].
        - (* Disjoint cmap (FromList fnames) *)
          match goal with H : FromList ?fn \subset _ |- _ =>
            eapply Disjoint_Included_r; [exact H | exact Hdis_cm1] end.
        - match goal with H : FromList ?fn \subset _ |- _ =>
            eapply Disjoint_Included_r; [exact H | exact Hdis_cm2] end.
        - (* Disjoint fnames vars1 *)
          match goal with H : FromList ?fn \subset _ |- _ =>
            eapply Disjoint_Included_l; [exact H | eapply Disjoint_sym; exact Hdis1] end.
        - match goal with H : FromList ?fn \subset _ |- _ =>
            eapply Disjoint_Included_l; [exact H | eapply Disjoint_sym; exact Hdis2] end.
        - eapply Forall2_preord_var_env_monotonic with (k := m); [lia | exact Henv].
        (* cmap_deps_mfix cmap mfix ⊆ cmap_deps cmap (tFix mfix idx) *)
        - intros v0 Hv0. eapply preord_var_env_monotonic.
          + eapply Hglob.
            eapply cmap_vars_of_monotone; [| exact Hv0]. intros kn Hkn.
            simpl. apply Exists_fold_left_union. exact Hkn.
          + lia. }
      eapply preord_exp_fun_compat.
      - eapply Hprops.
      - eapply Hprops.
      - (* name_in_fundefs ⊆ FromList fnames for both sides *)
        assert (Hafn1 : all_fun_name fdefs = fnames).
        { match goal with H : anf_cvt_rel_mfix _ _ _ _ _ _ _ _ _ _ |- _ =>
            exact (anf_cvt_rel_mfix_all_fun_name _ _ _ _ _ _ _ _ _ _ H) end. }
        assert (Hafn2 : all_fun_name fdefs0 = fnames0).
        { match goal with
          | [H1 : anf_cvt_rel_mfix _ _ _ _ _ _ _ fnames _  _,
             H2 : anf_cvt_rel_mfix _ _ _ _ _ _ _ fnames0 _ _ |- _] =>
            exact (anf_cvt_rel_mfix_all_fun_name _ _ _ _ _ _ _ _ _ _ H2)
          end. }
        assert (Hni_sub1 : name_in_fundefs fdefs \subset FromList fnames).
        { intros z Hz. apply (proj1 (Same_set_all_fun_name _)) in Hz.
          rewrite Hafn1 in Hz. exact Hz. }
        assert (Hni_sub2 : name_in_fundefs fdefs0 \subset FromList fnames0).
        { intros z Hz. apply (proj1 (Same_set_all_fun_name _)) in Hz.
          rewrite Hafn2 in Hz. exact Hz. }
        eapply Hcont.
        + lia.
        + (* preord_var_env for result: extract from Hfn_env via nth_error *)
          eapply Forall2_nth_error; [exact Hfn_env | eassumption | eassumption].
        + (* Forall2 for vars1/vars2 under def_funs *)
          eapply Forall2_preord_var_env_def_funs.
          * eapply Forall2_preord_var_env_monotonic with (k := m); [lia | exact Henv].
          * eapply Disjoint_Included_r; [exact Hni_sub1 |].
            match goal with H : FromList fnames \subset _ |- _ =>
              eapply Disjoint_Included_r; [exact H | exact Hdis1] end.
          * eapply Disjoint_Included_r; [exact Hni_sub2 |].
            match goal with H : FromList fnames0 \subset _ |- _ =>
              eapply Disjoint_Included_r; [exact H | exact Hdis2] end.
        + (* transfer: def_funs_not_In since x ∉ S1 ⊇ fnames ⊇ name_in_fundefs *)
          intros a b Hvar Ha Hb.
          eapply preord_var_env_def_funs_not_In_r.
          * intros Hc. apply Hb.
            match goal with H : FromList fnames0 \subset _ |- _ => apply H end.
            exact (Hni_sub2 _ Hc).
          * eapply preord_var_env_def_funs_not_In_l.
            -- intros Hc. apply Ha.
               match goal with H : FromList fnames \subset _ |- _ => apply H end.
               exact (Hni_sub1 _ Hc).
            -- eapply preord_var_env_monotonic. exact Hvar. lia. }

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
  Qed.

  Corollary anf_cvt_exp_alpha_equiv_holds :
    forall k, anf_cvt_exp_alpha_equiv k.
  Proof. intros k e. exact (anf_cvt_alpha_equiv k e). Qed.

  Corollary anf_cvt_args_alpha_equiv k :
    forall args, anf_cvt_args_alpha_equiv_for args k.
  Proof.
    intros args. eapply anf_cvt_args_alpha_from_all.
    induction args; constructor; [exact (anf_cvt_alpha_equiv k a) | exact IHargs].
  Qed.

  Corollary anf_cvt_branches_alpha_equiv k :
    forall ind brs n, anf_cvt_branches_alpha_equiv_for ind brs n k.
  Proof.
    intros ind brs n. eapply anf_cvt_branches_alpha_from_all.
    induction brs; constructor; [exact (anf_cvt_alpha_equiv k (snd a)) | exact IHbrs].
  Qed.

  Corollary anf_cvt_mfix_alpha_equiv k :
    forall mfix, anf_cvt_mfix_alpha_equiv_for mfix k.
  Proof.
    intros mfix. eapply anf_cvt_mfix_alpha_from_all.
    - induction mfix as [| d mfix' IH]; constructor.
      + destruct (EAst.dbody d) eqn:Hd; try exact I.
        exact (anf_cvt_alpha_equiv k t).
      + exact IH.
    - intros j _ e. exact (anf_cvt_alpha_equiv j e).
  Qed.

  Lemma anf_cvt_val_alpha_equiv :
    forall k, anf_cvt_val_alpha_equiv_statement k.
  Proof.
    intros k. induction k as [k IHk] using lt_wf_rec1. intros v.
    set (P := fun (v : fuel_sem.value) =>
      forall v1 v2 : val,
        anf_val_rel' v v1 -> anf_val_rel' v v2 ->
        preord_val cenv PG k v1 v2).
    eapply value_ind' with (P := P); subst P; simpl.

    - (* Con_v *)
      intros dcon vs IH v1 v2 Hrel1 Hrel2.
      inv Hrel1; inv Hrel2.
      rewrite preord_val_eq. simpl. split.
      + congruence.
      + match goal with
        | [ H1 : Forall2 _ vs ?vs1, H2 : Forall2 _ vs ?vs2 |- Forall2 _ ?vs1 ?vs2 ] =>
          revert vs1 vs2 H1 H2;
          induction IH; intros vs1 vs2 Hvs1 Hvs2;
            [ inv Hvs1; inv Hvs2; constructor
            | inv Hvs1; inv Hvs2; constructor; eauto ]
        end.

    - (* Clos_v *)
      intros vs_clos na e_body Hall v1 v2 Hrel1 Hrel2.
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
        eapply preord_exp_post_monotonic. exact HinclG.
        eapply (anf_cvt_alpha_equiv j e_body).
        * lia.
        * eassumption.
        * eassumption.
        * (* Disjoint side 1 *)
          match goal with H : Disjoint _ (_ |: (_ |: _)) _ |- _ =>
            eapply Disjoint_Included_l; [| exact H];
            normalize_sets; now sets end.
        * match goal with H : Disjoint _ (_ |: (_ |: _)) _ |- _ =>
            eapply Disjoint_Included_l; [| exact H];
            normalize_sets; now sets end.
        * eassumption.
        * eassumption.
        * (* Forall2 for x :: names *)
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
        * (* preord_env_P (cmap_deps cmap e_body) from global_env_rel' *)
          intros v0 Hv0.
          destruct Hv0 as [k0 [Hk0 Hlk0]].
          (* Save v0 ∈ cmap_vars before extraction modifies context *)
          assert (Hv0_cmap : v0 \in cmap_vars cmap)
            by (exists k0; exact Hlk0).
          (* Extract from both global_env_rel' hypotheses *)
          match goal with H : global_env_rel' _ _ _ _ _ |- _ =>
            pose proof (H k0 v0 Hk0 Hlk0) as Hg1_ex; clear H end.
          match goal with H : global_env_rel' _ _ _ _ _ |- _ =>
            pose proof (H k0 v0 Hk0 Hlk0) as Hg2_ex; clear H end.
          destruct Hg1_ex as (decl1 & body1 & anf_v1 & Hdecl1 & Hbody1 & Hget1 & Hvrel1).
          destruct Hg2_ex as (decl2 & body2 & anf_v2 & Hdecl2 & Hbody2 & Hget2 & Hvrel2).
          assert (decl1 = decl2) by (unfold declared_constant in *; congruence).
          subst decl2.
          assert (body1 = body2) by congruence. subst body2.
          destruct (globals_terminate _ _ _ Hdecl1 Hbody1)
            as (src_v & f_ev & t_ev & Heval).
          specialize (Hvrel1 _ _ _ Heval).
          specialize (Hvrel2 _ _ _ Heval).
          eapply preord_var_env_extend_neq.
          -- eapply preord_var_env_extend_neq.
             ++ intros w Hw.
                first
                  [rewrite Hget1 in Hw; injection Hw as <-;
                   eexists; split; [exact Hget2 |];
                   eapply IHk; [lia | exact Hvrel1 | exact Hvrel2]
                  |rewrite Hget2 in Hw; injection Hw as <-;
                   eexists; split; [exact Hget1 |];
                   eapply IHk; [lia | exact Hvrel2 | exact Hvrel1]].
             ++ (* v0 ≠ f: from ~ f \in cmap_vars after inv *)
                intros Heq. subst.
                match goal with H : ~ Ensembles.In _ (cmap_vars _) _ |- _ =>
                  exact (H Hv0_cmap) end.
             ++ intros Heq. subst.
                match goal with H : ~ Ensembles.In _ (cmap_vars _) _ |- _ =>
                  exact (H Hv0_cmap) end.
          -- (* v0 ≠ x: from ~ x \in cmap_vars after inv *)
             intros Heq. subst.
             match goal with H : ~ Ensembles.In _ (cmap_vars _) _ |- _ =>
               exact (H Hv0_cmap) end.
          -- intros Heq. subst.
             match goal with H : ~ Ensembles.In _ (cmap_vars _) _ |- _ =>
               exact (H Hv0_cmap) end.
        * (* Continuation: Ehalt *)
          intros j0 rho1'' rho2'' Hle Hvar_cont Henv_cont _.
          eapply preord_exp_halt_compat.
          -- eapply Hprops.
          -- eapply Hprops.
          -- exact Hvar_cont.

    - (* ClosFix_v *)
      intros vs_clos fnl n_idx Hall v1 v2 Hrel1 Hrel2.
      inv Hrel1. inv Hrel2.

      (* Save global_env_rel' before any rename *)
      match goal with H : global_env_rel' _ _ _ _ _ |- _ =>
        rename H into Hglob_fix1 end.
      match goal with H : global_env_rel' _ _ _ _ _ |- _ =>
        rename H into Hglob_fix2 end.

      (* Extract find_def for the idx-th function from both fix relations *)
      match goal with
      | [Hf : anf_fix_rel _ _ _ _ _ _ _ _ _ ?Bs _,
         Hn : nth_error _ _ = Some ?g
         |- preord_val _ _ _ (Vfun _ ?Bs ?g) _] =>
        rename Hf into Hfix1; rename Hn into Hnth1
      end.
      match goal with
      | [Hf : anf_fix_rel _ _ _ _ _ _ _ _ _ ?Bs _,
         Hn : nth_error _ _ = Some ?g
         |- preord_val _ _ _ _ (Vfun _ ?Bs ?g)] =>
        rename Hf into Hfix2; rename Hn into Hnth2
      end.

      edestruct anf_fix_rel_exists
        as (d1 & na1 & e1 & x1 & C_1 & r_1 & S_b1 & S_b1' &
            Hnth_d1 & Hbod1 & Hfind1 & Hcvt1 & Hdis_b1 & Hfresh_b1);
        [exact Hfix1 | exact Hnth1 | eassumption |].
      edestruct anf_fix_rel_exists
        as (d2 & na2 & e2 & x2 & C_2 & r_2 & S_b2 & S_b2' &
            Hnth_d2 & Hbod2 & Hfind2 & Hcvt2 & Hdis_b2 & Hfresh_b2);
        [exact Hfix2 | exact Hnth2 | eassumption |].

      eapply preord_val_fun.
      + exact Hfind1.
      + exact Hfind2.
      + intros rho1' j vs1 vs2 Hlen Hset1.
        destruct vs1 as [| v_arg1 [| ? ?]]; simpl in *; try congruence.
        destruct vs2 as [| v_arg2 [| ? ?]]; simpl in *; try congruence.
        inv Hset1. eexists. split. { reflexivity. }
        intros Hlt Hall_args. inv Hall_args.
        eapply preord_exp_post_monotonic. exact HinclG.

        (* Use IHk j for body alpha-equiv *)
        eapply (anf_cvt_alpha_equiv j).
        * lia.
        * eassumption.
        * (* e1 = e2: same fnl, same index → same d → same body *)
          assert (d1 = d2) by congruence. subst d2.
          assert (EAst.tLambda na1 e1 = EAst.tLambda na2 e2) by congruence.
          match goal with H : EAst.tLambda _ _ = EAst.tLambda _ _ |- _ =>
            injection H as <- <- end.
          eassumption.
        * (* Disjoint (FromList (x1 :: rev fnames ++ names)) S_b1 *)
          eapply Disjoint_Included_l; [| exact Hdis_b1].
          rewrite FromList_cons, FromList_app.
          intros z Hz. inv Hz; [left; assumption |].
          match goal with H : Ensembles.In _ (Union _ _ _) z |- _ => inv H end;
            [right; left; unfold FromList, Ensembles.In in *;
             match goal with H : In z _ |- _ => apply in_rev in H; exact H end
            |right; right; assumption].
        * eapply Disjoint_Included_l; [| exact Hdis_b2].
          rewrite FromList_cons, FromList_app.
          intros z Hz. inv Hz; [left; assumption |].
          match goal with H : Ensembles.In _ (Union _ _ _) z |- _ => inv H end;
            [right; left; unfold FromList, Ensembles.In in *;
             match goal with H : In z _ |- _ => apply in_rev in H; exact H end
            |right; right; assumption].
        * (* Disjoint cmap S_b1: need S_b1 ⊆ S1, cmap ⊥ S1 *)
          admit.
        * admit.
        * (* Forall2 for x :: rev fnames ++ names *)
          constructor.
          -- (* x1/x2: argument values *)
             eapply preord_var_env_extend_eq. eassumption.
          -- (* rev fnames ++ names in def_funs + M.set env *)
             eapply Forall2_preord_var_env_set.
             ++ eapply Forall2_app.
                ** (* rev fnames: fixpoint closures related via IHk j *)
                   eapply All_Forall.Forall2_rev.
                   assert (Hafn1 := anf_fix_rel_names _ _ _ _ _ _ _ _ _ _ _ Hfix1).
                   assert (Hafn2 := anf_fix_rel_names _ _ _ _ _ _ _ _ _ _ _ Hfix2).
                   assert (Hlen_fn : Datatypes.length (all_fun_name Bs) =
                                     Datatypes.length (all_fun_name Bs0)).
                   { rewrite Hafn1, Hafn2.
                     erewrite anf_fix_rel_fnames_length by exact Hfix1.
                     erewrite anf_fix_rel_fnames_length by exact Hfix2.
                     reflexivity. }
                   eapply Forall2_from_nth_error.
                   --- rewrite <- Hafn1, <- Hafn2. exact Hlen_fn.
                   --- intros i fi fi' Hni Hni'.
                       intros w Hget_w.
                       assert (Hni_fd : name_in_fundefs Bs fi).
                       { apply (proj2 (Same_set_all_fun_name Bs)).
                         rewrite Hafn1. unfold FromList, Ensembles.In.
                         eapply nth_error_In. eassumption. }
                       rewrite (def_funs_eq _ _ _ _ _ Hni_fd) in Hget_w.
                       inv Hget_w.
                       assert (Hni_fd0 : name_in_fundefs Bs0 fi').
                       { apply (proj2 (Same_set_all_fun_name Bs0)).
                         erewrite anf_fix_rel_names by exact Hfix2.
                         unfold FromList, Ensembles.In.
                         eapply nth_error_In. eassumption. }
                       eexists. split.
                       { match goal with H : name_in_fundefs ?Bs fi' |- _ =>
                           exact (def_funs_eq _ _ _ _ _ H) end. }
                       (* preord_val j via IHk: reconstruct anf_rel_ClosFix *)
                       eapply (IHk j Hlt (ClosFix_v vs_clos fnl i));
                         (econstructor; try eassumption; admit).
                ** (* names: captured env related via IHk j *)
                   eapply Forall2_preord_var_env_def_funs.
                   --- eapply anf_cvt_env_alpha_equiv_Forall2.
                       +++ eapply IHk. lia.
                       +++ eassumption.
                       +++ eassumption.
                   --- eapply Disjoint_Included_r;
                         [exact (proj1 (Same_set_all_fun_name _)) |].
                       erewrite anf_fix_rel_names by eassumption.
                       eassumption.
                   --- eapply Disjoint_Included_r;
                         [exact (proj1 (Same_set_all_fun_name _)) |].
                       erewrite anf_fix_rel_names by eassumption.
                       eassumption.
             ++ (* ~ x1 \in FromList (rev fnames ++ names): x1 fresh *) admit.
             ++ admit.
        * (* preord_env_P cmap_deps_mfix: same pattern as Clos_v *)
          unfold cmap_deps_mfix, cmap_vars_of.
          intros v0 [k0 [Hk0 Hlk0]].
          assert (Hv0_cmap : v0 \in cmap_vars cmap)
            by (exists k0; exact Hlk0).
          (* preord_env_P cmap_deps_mfix: same as Clos_v *)
          (* Goal is preord_var_env for a single v0.
             v0, k0, Hk0, Hlk0, Hv0_cmap already in context. *)
          admit.
        * (* Continuation: Ehalt *)
          intros j0 rho1'' rho2'' Hle Hvar_cont Henv_cont _.
          eapply preord_exp_halt_compat;
            [eapply Hprops | eapply Hprops | exact Hvar_cont].
  Admitted.

End AlphaEquiv.
