(* Semantic correctness of the ANF conversion from MetaRocq Erasure to LambdaANF.
   Adapts LambdaBoxLocal_to_LambdaANF_anf_correct.v to the new MetaRocq pipeline. *)

(** Stdlib *)
From Stdlib Require Import ZArith.ZArith Lists.List micromega.Lia Arith
     Ensembles Relations.Relation_Definitions.

(** MetaRocq *)
From MetaRocq.Erasure Require Import EAst EAstUtils EGlobalEnv EWellformed.
From MetaRocq.Common Require Import BasicAst Kernames.

(** CompCert *)
From compcert Require Import lib.Maps lib.Coqlib.

(** CertiRocq *)
From CertiRocq.Common Require Import AstCommon.
From CertiRocq Require Import Pipeline_utils.
From CertiRocq.LambdaANF Require Import
  cps cps_show eval ctx logical_relations
  List_util algebra alpha_conv functions Ensembles_util
  tactics identifiers bounds cps_util rename set_util.
From MetaRocq.Utils Require Import All_Forall.
From CertiRocq.LambdaBox_to_LambdaANF Require Import common ANF fuel_sem wf anf_corresp anf_util.

Import ListNotations.


Section Correct.

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

  Context (cmap_inj : forall k1 k2 v,
    lookup_const cmap k1 = Some v ->
    lookup_const cmap k2 = Some v ->
    k1 = k2).


  (** ** Source fuel and trace for EAst.term *)

  Definition fuel_exp (e : EAst.term) : nat :=
    match e with
    | EAst.tLetIn _ _ _ => 0
    | _ => 1
    end.

  Definition anf_trace_exp (e : EAst.term) : nat :=
    match e with
    | EAst.tRel _ => 1
    | EAst.tLambda _ _ => 2
    | EAst.tApp _ _ => 2
    | EAst.tLetIn _ _ _ => 0
    | EAst.tFix _ _ => 2
    | EAst.tConstruct _ _ _ => 2
    | EAst.tCase _ _ _ => 4  (* simplified; may need branch overhead *)
    | EAst.tBox => 2
    | EAst.tConst _ => 1
    | EAst.tProj _ _ => 2
    | EAst.tPrim _ => 2
    | _ => 1  (* tVar, tEvar, tCoFix, tLazy, tForce — shouldn't appear *)
    end.

  Program Instance fuel_resource_LambdaBox : @resource EAst.term nat :=
    { zero := 0;
      one_i := fuel_exp;
      plus := Nat.add
    }.
  Next Obligation. lia. Qed.
  Next Obligation. lia. Qed.
  Next Obligation. lia. Qed.

  Program Instance trace_resource_LambdaBox : @resource EAst.term nat :=
    { zero := 0;
      one_i := anf_trace_exp;
      plus := Nat.add
    }.
  Next Obligation. lia. Qed.
  Next Obligation. lia. Qed.
  Next Obligation. lia. Qed.

  Global Instance LambdaBox_resource_fuel : @LambdaBox_resource nat.
  Proof. constructor. exact fuel_resource_LambdaBox. Defined.

  Global Instance LambdaBox_resource_trace : @LambdaBox_resource nat.
  Proof. constructor. exact trace_resource_LambdaBox. Defined.


  (** ** Global termination *)

  (** All global constant bodies terminate. Used for val alpha-equiv
      and correctness of tConst. Defined here so it can be shared
      between [anf_util] and [anf_correct]. *)
  Definition globals_terminate_prop :=
    forall k decl body,
      declared_constant Σ k decl ->
      decl.(EAst.cst_body) = Some body ->
      exists src_v f t,
        @eval_env_fuel _ LambdaBox_resource_fuel LambdaBox_resource_trace
                       Σ box_dc [] body (fuel_sem.Val src_v) f t.


  (** ** LambdaANF trivial trace *)

  Global Program Instance trace_res_pre : @resource fin unit :=
    { zero := tt;
      one_i fin := tt;
      plus x y := tt; }.
  Next Obligation. destruct x. reflexivity. Qed.
  Next Obligation. destruct x; destruct y. reflexivity. Qed.

  Global Program Instance trace_res_exp : @exp_resource unit :=
    { HRes := trace_res_pre }.

  Global Instance trace_res : @trace_resource unit.
  Proof. econstructor. exact trace_res_exp. Defined.


  (** ** Fuel postconditions *)

  Definition eq_fuel : @PostT nat unit :=
    fun '(e1, r1, f1, t1) '(e2, r2, f2, t2) => f1 = f2.

  Definition anf_bound (f_src t_src : nat) : @PostT nat unit :=
    fun '(e1, r1, f1, t1) '(e2, r2, f2, t2) =>
      (f1 + f_src <= f2)%nat /\
      (f2 <= f1 + t_src)%nat.


  (** ** Shorthands *)

  Let anf_cvt_rel' := anf_cvt_rel func_tag default_tag tgm cmap.
  Let anf_cvt_rel_args' := anf_cvt_rel_args func_tag default_tag tgm cmap.
  Let anf_val_rel' :=
    @anf_val_rel func_tag default_tag tgm cmap nat
                 LambdaBox_resource_fuel LambdaBox_resource_trace Σ box_dc.
  Let anf_env_rel' :=
    @anf_env_rel func_tag default_tag tgm cmap nat
                 LambdaBox_resource_fuel LambdaBox_resource_trace Σ box_dc.
  Let global_env_rel' :=
    @global_env_rel func_tag default_tag tgm cmap nat
                    LambdaBox_resource_fuel LambdaBox_resource_trace Σ box_dc.

  (* Shorthand for the source evaluation relation.
     Must be explicit about both resource instances since both are
     [@LambdaBox_resource nat] and Coq's instance resolution can't
     distinguish them by type. *)
  Let src_eval := @eval_env_fuel nat LambdaBox_resource_fuel
                                     LambdaBox_resource_trace Σ box_dc.


  (** ** Helpers *)

  Fixpoint set_many (xs : list var) (vs : list val) (rho : M.t val) : M.t val :=
    match xs, vs with
    | x :: xs', v :: vs' => M.set x v (set_many xs' vs' rho)
    | _, _ => rho
    end.

  Lemma Forall2_nth_error_l {A B} (R : A -> B -> Prop) l1 l2 k a :
    Forall2 R l1 l2 ->
    nth_error l1 k = Some a ->
    exists b, nth_error l2 k = Some b /\ R a b.
  Proof.
    intros HF2 Hk. revert k Hk.
    induction HF2 as [ | a' b' l1' l2' Hab HF2' IH]; intros k Hk.
    - destruct k; simpl in Hk; discriminate.
    - destruct k as [ | k']; simpl in Hk.
      + inv Hk. exists b'. split; [ reflexivity | exact Hab ].
      + exact (IH k' Hk).
  Qed.

  Lemma Forall2_nth_error_r {A B} (R : A -> B -> Prop) l1 l2 k b :
    Forall2 R l1 l2 ->
    nth_error l2 k = Some b ->
    exists a, nth_error l1 k = Some a /\ R a b.
  Proof.
    intros HF2 Hk. revert k Hk.
    induction HF2 as [ | a' b' l1' l2' Hab HF2' IH]; intros k Hk.
    - destruct k; simpl in Hk; discriminate.
    - destruct k as [ | k']; simpl in Hk.
      + inv Hk. exists a'. split; [ reflexivity | exact Hab ].
      + exact (IH k' Hk).
  Qed.


  Lemma anf_cvt_rel_mfix_to_fix_rel fnames_all names0 :
    forall mfix S fnames S' fdefs,
      anf_cvt_rel_mfix func_tag default_tag tgm cmap
        S mfix (List.rev fnames_all ++ names0) fnames S' fdefs ->
      Disjoint _ S (FromList fnames_all :|: FromList names0) ->
      anf_fix_rel func_tag default_tag tgm cmap
        fnames_all names0 S fnames mfix fdefs S'.
  Proof.
    intros mfix. induction mfix; intros S fnames S' fdefs Hcvt Hdis.
    - inv Hcvt. constructor.
    - inv Hcvt.
      eapply anf_fix_fcons.
      1: eassumption.  (* dbody = tLambda *)
      1: exact Hdis.   (* Disjoint *)
      1: eassumption.  (* x1 ∈ S *)
      1: apply Included_refl. (* S1' ⊆ S \\ {x} *)
      1: apply Included_refl. (* S2' ⊆ S2 *)
      1: eassumption.  (* anf_cvt_rel *)
      eapply IHmfix; [ eassumption | ].
      eapply Disjoint_Included_l; [ | exact Hdis ].
      eapply Included_trans.
      * eapply (anf_cvt_exp_subset func_tag default_tag tgm cmap). eassumption.
      * eapply Setminus_Included.
  Qed.


  (* The result variable of an ANF conversion is in [FromList vn]
     (Rel case), in [S] (Lam/App/Fix/Construct/Case/Proj/Box/Prim),
     or in [cmap_vars cmap] (Const case). *)
  Lemma anf_cvt_result_in_consumed :
    forall S e vn S' C x,
      anf_cvt_rel func_tag default_tag tgm cmap S e vn S' C x ->
      x \in FromList vn \/ x \in S \/ x \in cmap_vars cmap.
  Proof.
    apply (anf_cvt_rel_ind' func_tag default_tag tgm cmap
      (fun S _ vn S' _ x => x \in FromList vn \/ x \in S \/ x \in cmap_vars cmap)
      (fun _ _ _ _ _ _ => True)
      (fun _ _ _ _ _ _ => True)
      (fun _ _ _ _ _ _ _ _ => True));
    try (intros; exact I).
    - (* Rel *) intros. left. eapply nth_error_In. eassumption.
    - (* Lam *) intros ? ? ? ? ? ? ? ? ? ? Hf.
      right; left. destruct Hf. assumption.
    - (* App: result r ∈ S3, chain S3 ⊆ S2 ⊆ S1 *)
      intros ? ? ? ? ? ? ? ? ? ? ? Hcvt1 _ Hcvt2 _ Hin.
      right; left. eapply (anf_cvt_exp_subset _ _ _ _ _ _ _ _ _ _ Hcvt1).
      eapply (anf_cvt_exp_subset _ _ _ _ _ _ _ _ _ _ Hcvt2). exact Hin.
    all: try (intros; right; left; eassumption).
    all: try (intros; right; right; match goal with
      | [ Hl : lookup_const _ _ = Some _ |- _ ] => exists _; exact Hl end).
    all: try (intros; right; left; match goal with
      | [ Hsub : FromList _ \subset _, Hnth : nth_error _ _ = Some _ |- _ ] =>
        eapply Hsub; eapply nth_error_In; eassumption end).
    all: try (intros; match goal with
    | [ IH : _ \/ _ \/ _ |- _ ] =>
      destruct IH as [?Hvn | [?Hs | ?Hcm]];
      [ unfold FromList, Ensembles.In in *; simpl in *;
        match goal with
        | [ H : _ = _ \/ _ |- _ ] =>
          destruct H as [<- | ?]; [left; assumption | left; assumption]
        | _ => left; assumption
        end
      | right; left; eapply anf_cvt_exp_subset; eassumption
      | right; right; assumption ]
    end).
    (* Construct: x ∈ S1 is a premise *)
    - intros. right; left. assumption.
    (* LetIn: x2 from body conversion *)
    - intros ? ? ? ? ? ? ? ? ? ? ? ? IH1 ? IH2.
      destruct IH2 as [Hin_vn | [Hin_S2 | Hin_cm]].
      + unfold FromList, Ensembles.In in Hin_vn. simpl in Hin_vn.
        destruct Hin_vn as [<- | ?]; [exact IH1 | left; assumption].
      + right; left. eapply anf_cvt_exp_subset; eassumption.
      + right; right. exact Hin_cm.
    all: try solve [intros; right; left; assumption].
    all: try solve [intros; right; left;
      match goal with
      | [Hsub : FromList _ \subset _, Hnth : nth_error _ _ = Some _ |- _] =>
        eapply Hsub; eapply nth_error_In; eassumption end].
    all: try solve [intros; right; right;
      match goal with
      | [Hl : lookup_const _ _ = Some _ |- _] => exists _; exact Hl end].
    all: try solve [intros; right; left; eapply anf_cvt_exp_subset; eassumption].
    (* Case: r ∈ S3 ⊆ S2 ⊆ S1\\f\\y ⊆ S1 *)
    - intros. right; left.
      assert (Hsub_exp : _ \subset _) by (eapply anf_cvt_exp_subset; eassumption).
      assert (Hsub_brs : _ \subset _) by (eapply anf_cvt_branches_subset; eassumption).
      apply Hsub_brs in H5. apply Hsub_exp in H5.
      destruct H5. destruct H5. assumption.
    (* Fix: f ∈ fnames ⊆ S1 *)
    - intros. right; left. apply H. eapply nth_error_In. exact H4.
    - intros. right; left. assumption.
    - intros. right; right. eexists. eassumption.
    - intros. right; left. eapply anf_cvt_exp_subset; eassumption.
    - intros. right; left. assumption.
  Qed.

  Lemma wellformed_tLetIn n na b t' :
    wellformed Σ n (EAst.tLetIn na b t') = true ->
    wellformed Σ n b = true /\ wellformed Σ (S n) t' = true.
  Proof.
    unfold wellformed. simpl. fold (@wellformed efl).
    intro H. apply andb_true_iff in H. destruct H as [H1 H2].
    apply andb_true_iff in H1. destruct H1 as [H1a H1b].
    split; assumption.
  Qed.


  Lemma anf_env_rel_set vnames vs0 x v' rho :
    anf_env_rel' vnames vs0 rho ->
    (forall k, nth_error vnames k = Some x ->
      exists v0, nth_error vs0 k = Some v0 /\ anf_val_rel' v0 v') ->
    anf_env_rel' vnames vs0 (M.set x v' rho).
  Proof.
    unfold anf_env_rel'.
    intros Henv Hdup.
    revert vs0 Henv Hdup.
    induction vnames as [ | y vnames' IH]; intros vs0 Henv Hdup.
    - inv Henv. constructor.
    - destruct vs0 as [ | v_s vs']; [inv Henv | ].
      inv Henv. constructor.
      + destruct (Pos.eq_dec y x) as [-> | Hneq].
        * rewrite M.gss.
          destruct (Hdup 0%nat eq_refl) as [v_src [Hnth Hrel]].
          simpl in Hnth. inv Hnth.
          eexists; eauto.
        * match goal with H : exists _, _ |- _ =>
            destruct H as [w [Hgw Hrw]]; exists w; split; [| exact Hrw];
            rewrite M.gso; [exact Hgw | exact Hneq]
          end.
      + eapply IH; [assumption | ].
        intros k Hnth. exact (Hdup (S k) Hnth).
  Qed.

  Lemma anf_env_rel_length vnames vs0 rho :
    anf_env_rel' vnames vs0 rho ->
    Datatypes.length vs0 = Datatypes.length vnames.
  Proof.
    unfold anf_env_rel'. intro H. eapply Forall2_length in H. exact H.
  Qed.





  (** Value determinism: if source evaluation terminates,
      the value is unique (fuel/trace may differ). *)
  Lemma eval_val_det rho0 e0 v1 v2 f1 t1 f2 t2 :
    src_eval rho0 e0 (fuel_sem.Val v1) f1 t1 ->
    src_eval rho0 e0 (fuel_sem.Val v2) f2 t2 ->
    v1 = v2.
  Proof. admit. Admitted.

  (** Evaluation preserves well-formedness of values. *)
  Lemma eval_preserves_wf rho0 e0 v0 f0 t0 :
    well_formed_env Σ rho0 ->
    wellformed Σ (List.length rho0) e0 = true ->
    src_eval rho0 e0 (fuel_sem.Val v0) f0 t0 ->
    well_formed_val Σ v0.
  Proof. admit. Admitted.

  (** Weakening: env_consistent over an extended list implies
      env_consistent over the original list with the first and last entries. *)
  Lemma env_consistent_weaken x x1 vn v v_b rho :
    env_consistent (x :: x1 :: vn) (v :: v_b :: rho) ->
    env_consistent vn rho ->
    env_consistent (x :: vn) (v :: rho).
  Proof.
    intros Hext Horig i j y Hi Hj.
    destruct i as [|i'], j as [|j']; simpl in *.
    - reflexivity.
    - (* i=0, j=S j': x = vn[j'], need v = rho[j'].
         Use Hext with i=0 and j=j'+2. *)
      apply (Hext 0 (S (S j')) y Hi Hj).
    - apply (Hext (S (S i')) 0 y Hi Hj).
    - exact (Horig i' j' y Hi Hj).
  Qed.

  (** Combined: eval preserves env_consistent when extending.
      Proved by eval induction. The LetIn case uses IH(b) to extend,
      then IH(body), then weakening to project out the intermediate binding. *)
  (* Helper: when x ∉ FromList vn, env_consistent extension is trivial *)
  Lemma env_consistent_extend_fresh x vn v rho :
    env_consistent vn rho ->
    ~ x \in FromList vn ->
    env_consistent (x :: vn) (v :: rho).
  Proof.
    intros Hcons Hni i j y Hi Hj.
    destruct i as [|i'], j as [|j']; simpl in *.
    - reflexivity.
    - injection Hi as <-. exfalso. apply Hni. eapply nth_error_In. exact Hj.
    - injection Hj as <-. exfalso. apply Hni. eapply nth_error_In. exact Hi.
    - exact (Hcons i' j' y Hi Hj).
  Qed.

  Lemma env_consistent_extend x1 vnames0 v1 rho0 b0 S0 S2 C1 f1 t1 :
    env_consistent vnames0 rho0 ->
    Disjoint _ (FromList vnames0) S0 ->
    Disjoint _ (cmap_vars cmap) S0 ->
    anf_cvt_rel' S0 b0 vnames0 S2 C1 x1 ->
    src_eval rho0 b0 (fuel_sem.Val v1) f1 t1 ->
    env_consistent (x1 :: vnames0) (v1 :: rho0).
  Proof.
    intros Hcons Hdis_vn Hdis_cm Hcvt.
    revert vnames0 S0 S2 C1 x1 Hcons Hdis_vn Hdis_cm Hcvt.
    revert rho0 b0 f1 t1.
    (* We prove a stronger statement by eval induction:
       for any eval producing Val, env_consistent extends. *)
    cut (forall rho0 b0 r f1 t1,
           src_eval rho0 b0 r f1 t1 ->
           forall vn S0 S2 C1 x1,
             anf_cvt_rel' S0 b0 vn S2 C1 x1 ->
             env_consistent vn rho0 ->
             Disjoint _ (FromList vn) S0 ->
             Disjoint _ (cmap_vars cmap) S0 ->
             match r with
             | fuel_sem.Val v => env_consistent (x1 :: vn) (v :: rho0)
             | fuel_sem.OOT => True
             end).
    { intros H rho0 b0 f1 t1 vn S0 S2 C1 x1 Hcons Hdis_vn Hdis_cm Hcvt Heval.
      exact (H rho0 b0 _ f1 t1 Heval vn S0 S2 C1 x1 Hcvt Hcons Hdis_vn Hdis_cm). }
    intros rho0 b0 r f1 t1 Heval.
    eapply (@eval_env_fuel_ind'
              nat LambdaBox_resource_fuel LambdaBox_resource_trace Σ box_dc
              (* P_step *)
              (fun rho e r f t =>
                 forall vn S0 S2 C1 x1,
                   anf_cvt_rel' S0 e vn S2 C1 x1 ->
                   env_consistent vn rho ->
                   Disjoint _ (FromList vn) S0 ->
                   Disjoint _ (cmap_vars cmap) S0 ->
                   match r with
                   | fuel_sem.Val v => env_consistent (x1 :: vn) (v :: rho)
                   | fuel_sem.OOT => True
                   end)
              (* P_many *)
              (fun _ _ _ _ _ => True)
              (* P_fuel = same as P_step *)
              (fun rho e r f t =>
                 forall vn S0 S2 C1 x1,
                   anf_cvt_rel' S0 e vn S2 C1 x1 ->
                   env_consistent vn rho ->
                   Disjoint _ (FromList vn) S0 ->
                   Disjoint _ (cmap_vars cmap) S0 ->
                   match r with
                   | fuel_sem.Val v => env_consistent (x1 :: vn) (v :: rho)
                   | fuel_sem.OOT => True
                   end));
      try (intros; exact I).

    (* ================================================================ *)
    (* P_step cases                                                      *)
    (* ================================================================ *)

    (* For most cases, the result variable x1 is fresh (∈ S), so
       env_consistent_extend_fresh handles it. The key non-trivial cases are
       eval_Rel_fuel (x1 ∈ FromList vn) and eval_LetIn_step (recursive).
       We handle them individually; all others are dispatched by automation. *)

    (* All 21 cases handled with explicit bullets *)
    (* The `try (intros; exact I)` above consumed: OOT step cases (6),
       P_many (2), eval_OOT (1). Remaining 12 goals in order:
       P_step terminating: App, FixApp, LetIn, Construct, Case, Proj, Const (7)
       P_fuel Val: Rel, Lam, Fix, Box (4)
       P_fuel: eval_step (1) *)
    - (* App *)
      intros ? ? ? ? ? ? ? ? ? ? ? ? ? ? Heval1 IH1 Heval2 IH2 Heval3 IH3
             vn0 S0 S2' C1' x0 Hcvt Hcons0 Hdv Hdc.
      remember (EAst.tApp _ _) as e_app.
      destruct Hcvt; try discriminate.
      injection Heqe_app as <- <-.
      destruct r0; [| exact I].
      apply env_consistent_extend_fresh; [assumption |].
      intro Hc. eapply Hdv. constructor; [exact Hc |].
      eapply anf_cvt_exp_subset; [eassumption|].
      eapply anf_cvt_exp_subset; [eassumption|]. assumption.
    - (* FixApp — same as App *)
      intros ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? Heval1 IH1 ? ? Heval2 IH2 Heval3 IH3
             vn0 S0 S2' C1' x0 Hcvt Hcons0 Hdv Hdc.
      remember (EAst.tApp _ _) as e_app.
      destruct Hcvt; try discriminate.
      injection Heqe_app as <- <-.
      destruct r0; [| exact I].
      apply env_consistent_extend_fresh; [assumption |].
      intro Hc. eapply Hdv. constructor; [exact Hc |].
      eapply anf_cvt_exp_subset; [eassumption|].
      eapply anf_cvt_exp_subset; [eassumption|]. assumption.
    - (* LetIn *)
      intros na_l b_l t_l v_b r_l rho_l fb ft tb tt
             Heval_b IH_b Heval_t IH_t
             vn0 S0 S2' C1' x0 Hcvt Hcons0 Hdv Hdc.
      (* Invert conversion for tLetIn using remember+destruct *)
      remember (EAst.tLetIn na_l b_l t_l) as e_l.
      destruct Hcvt; try discriminate.
      (* After destruct, only anf_LetIn case remains.
         Use eassumption to find sub-conversions. *)
      injection Heqe_l as <- <- <-.
      specialize (IH_b _ _ _ _ _ ltac:(eassumption) Hcons0 Hdv Hdc).
      assert (Hdv2 : Disjoint _ (FromList (x1 :: vn)) S2).
      { constructor. intros z Hz. destruct Hz.
        unfold FromList, Ensembles.In in H. simpl in H.
        destruct H as [<- | Hin_vn].
        - eapply (anf_cvt_result_not_in_output _ _ _ _ _ _ _ _ _ _ Hcvt1 Hdv Hdc). assumption.
        - eapply Hdv. constructor; [exact Hin_vn |].
          eapply (anf_cvt_exp_subset _ _ _ _ _ _ _ _ _ _ Hcvt1). assumption. }
      assert (Hdc2 : Disjoint _ (cmap_vars cmap) S2).
      { eapply Disjoint_Included_r; [eapply anf_cvt_exp_subset; eassumption | exact Hdc]. }
      specialize (IH_t _ _ _ _ _ ltac:(eassumption) IH_b Hdv2 Hdc2).
      destruct r_l as [v_res |]; [| exact I].
      eapply env_consistent_weaken; [exact IH_t | exact Hcons0].
    - (* Construct *) intros.
      remember (EAst.tConstruct _ _ _) as e_c.
      destruct H2; try discriminate. clear Heqe_c.
      apply env_consistent_extend_fresh; [assumption |].
      intro Hc. eapply H4. constructor; [exact Hc | assumption].
    - (* Case *) intros. destruct r0; [| exact I].
      remember (EAst.tCase _ _ _) as e_case.
      destruct H5; try discriminate. clear Heqe_case.
      (* x1 = r, which is in S3 ⊆ S2 ⊆ S0\\f\\y ⊆ S0 *)
      apply env_consistent_extend_fresh; [assumption |].
      intro Hc. eapply H7. constructor; [exact Hc |].
      assert (Hs3 : Ensembles.In _ S2 r0).
      { eapply anf_cvt_branches_subset; eassumption. }
      assert (Hs2 : Ensembles.In _ (S1 \\ [set f] \\ [set y]) r0).
      { eapply anf_cvt_exp_subset; eassumption. }
      destruct Hs2. destruct H13. assumption.
    - (* Proj *) intros.
      remember (EAst.tProj _ _) as e_p.
      destruct H2; try discriminate. clear Heqe_p.
      (* x1 = y ∈ S2, S2 ⊆ S0 via anf_cvt_exp_subset *)
      apply env_consistent_extend_fresh; [assumption |].
      intro Hc. eapply H4. constructor; [exact Hc |].
      eapply anf_cvt_exp_subset; eassumption.
    - (* Const — depends on eval_val_det *) intros. admit.
    - (* Rel *)
      intros n rho_r v Hnth_rho vn_r S0_r S2_r C1_r x_r Hcvt Hcons_r Hdv_r Hdc_r.
      remember (EAst.tRel n) as e_r.
      destruct Hcvt; try discriminate.
      (* H : nth_error vn_r ? = Some x_r. Save before injection clears n. *)
      rename H into Hnth_vn.
      injection Heqe_r as <-.
      intros i j y Hi Hj.
      destruct i as [|i'], j as [|j']; simpl in *.
      + reflexivity.
      + injection Hi as <-. f_equal.
        rewrite <- Hnth_rho. exact (Hcons_r _ j' _ Hnth_vn Hj).
      + injection Hj as <-. f_equal.
        rewrite (Hcons_r i' _ _ Hi Hnth_vn). exact Hnth_rho.
      + exact (Hcons_r i' j' y Hi Hj).
    - (* Lam *)
      intros ? ? ?
             vn0 S0 S2' C1' x0 Hcvt Hcons0 Hdv Hdc.
      remember (EAst.tLambda _ _) as e_lam.
      destruct Hcvt; try discriminate.
      injection Heqe_lam as <- <-.
      apply env_consistent_extend_fresh; [assumption |].
      intro Hc. eapply Hdv. constructor; [exact Hc |].
      destruct H0. assumption.
    - (* Fix *)
      intros ? ? ?
             vn0 S0 S2' C1' x0 Hcvt Hcons0 Hdv Hdc.
      remember (EAst.tFix _ _) as e_fix.
      destruct Hcvt; try discriminate.
      injection Heqe_fix as <- <-.
      apply env_consistent_extend_fresh; [assumption |].
      intro Hc. eapply Hdv. constructor; [exact Hc |].
      eapply H. eapply nth_error_In. eassumption.
    - (* Box *)
      intros ?
             vn0 S0 S2' C1' x0 Hcvt Hcons0 Hdv Hdc.
      remember EAst.tBox as e_box.
      destruct Hcvt; try discriminate.
      clear Heqe_box.
      apply env_consistent_extend_fresh; [assumption |].
      intro Hc. eapply Hdv. constructor; [exact Hc | assumption].
    - intros ? ? ? ? ? ? IH. exact IH. (* eval_step *)
    - exact Heval.
  Admitted.


  (** Free variables of a context application don't include variables
      consumed by a preceding conversion. *)
  Lemma anf_cvt_disjoint_occurs_free_ctx S1 S2 S3 e1 e2 vn C1 C2 x1 x2 e_k :
    anf_cvt_rel' S1 e1 vn S2 C1 x1 ->
    anf_cvt_rel' S2 e2 (x1 :: vn) S3 C2 x2 ->
    Disjoint _ (FromList vn) S1 ->
    Disjoint _ (cmap_vars cmap) S1 ->
    Disjoint _ (occurs_free e_k) ((S1 \\ S3) \\ [set x2]) ->
    Disjoint _ (occurs_free (C2 |[ e_k ]|)) ((S1 \\ S2) \\ [set x1]).
  Proof. admit. Admitted.

  (** If the result of a conversion is in [cmap_vars] but not in [FromList vn]
      or [S], the source must be [tConst]. *)
  Lemma anf_cvt_result_cmap S0 e0 vn0 S0' C0 x0 k :
    anf_cvt_rel' S0 e0 vn0 S0' C0 x0 ->
    lookup_const cmap k = Some x0 ->
    ~ x0 \in FromList vn0 ->
    ~ x0 \in S0 ->
    e0 = EAst.tConst k /\ C0 = Hole_c /\ S0' = S0.
  Proof.
    intros Hcvt Hlook Hni_vn Hni_S.
    (* x0 ∉ S0 and x0 ∉ FromList vn0. By anf_cvt_result_in_consumed,
       x0 ∈ FromList vn0 ∨ x0 ∈ S0 ∨ x0 ∈ cmap_vars. The first two are ruled out.
       So x0 ∈ cmap_vars, meaning lookup_const cmap k' = Some x0 for some k'.
       By cmap_inj, k' = k. And the only constructor producing cmap results is anf_Const. *)
    destruct (anf_cvt_result_in_consumed _ _ _ _ _ _ Hcvt) as [? | [? | [k' Hlk']]].
    - contradiction.
    - contradiction.
    - assert (k' = k) by (eapply cmap_inj; eassumption). subst k'.
      (* x0 ∉ S0 and x0 ∉ FromList vn0 and x0 ∈ cmap_vars.
         Only anf_Const produces x0 ∈ cmap_vars directly. All other constructors
         put x0 in S0 or FromList vn0. So e0 = tConst k.
         This is provable by induction on the conversion but we admit it
         as it requires a large case analysis. *)
      admit.
  Admitted.

  (** Inversion of source evaluation for [tConst]. *)
  Lemma eval_tConst_inv rho0 k0 v0 f0 t0 :
    src_eval rho0 (EAst.tConst k0) (fuel_sem.Val v0) f0 t0 ->
    exists decl body f' t',
      declared_constant Σ k0 decl /\
      decl.(EAst.cst_body) = Some body /\
      src_eval [] body (fuel_sem.Val v0) f' t'.
  Proof. admit. Admitted.


  Context (Hglob_term : globals_terminate_prop).

  (** ** Post_properties instances *)

  Ltac unfold_all :=
    try unfold zero in *;
    try unfold one_ctx in *;
    try unfold algebra.one in *;
    try unfold one_i in *;
    try unfold algebra.HRes in *;
    try unfold HRexp_f in *; try unfold fuel_res in *;
    try unfold fuel_res_exp in *; try unfold fuel_res_pre in *;
    try unfold HRexp_t in *; try unfold trace_res in *;
    try unfold trace_res_exp in *; try unfold trace_res_pre in *.

  Global Instance eq_fuel_compat :
    @Post_properties cenv nat _ unit _ eq_fuel eq_fuel eq_fuel.
  Proof.
    unfold eq_fuel. constructor;
    try now (intro; intros; intro; intros; unfold_all; simpl; lia).
    - intro; intros. unfold post_base'. unfold_all; simpl. lia.
    - firstorder.
  Qed.

  Lemma eq_fuel_idemp :
    forall x y, comp eq_fuel eq_fuel x y -> eq_fuel x y.
  Proof.
    unfold comp, eq_fuel. intro; intros.
    destruct x as [[[? ?] ?] ?].
    destruct y as [[[? ?] ?] ?]. destructAll.
    destruct x as [[[? ?] ?] ?]. congruence.
  Qed.


  (** ** Reduction lemmas *)

  Definition one_step : @PostT nat unit :=
    fun '(e1, r1, f1, t1) '(e2, r2, f2, t2) => (f1 + 1)%nat = f2.

  Lemma preord_exp_Efun_red k e B rho :
    preord_exp cenv one_step eq_fuel k (e, def_funs B B rho rho) (Efun B e, rho).
  Proof.
    intros r cin cout Hleq Hbstep.
    do 3 eexists. split. econstructor 2. econstructor. eassumption.
    split. simpl. unfold_all. lia.
    eapply preord_res_refl; tci.
  Qed.

  Lemma preord_exp_Econstr_red k x ctag ys e rho vs :
    get_list ys rho = Some vs ->
    preord_exp cenv one_step eq_fuel k
      (e, M.set x (Vconstr ctag vs) rho) (Econstr x ctag ys e, rho).
  Proof.
    intros Hgvs r cin cout Hleq Hbstep.
    do 3 eexists. split. econstructor 2. econstructor; eauto.
    split. simpl. unfold_all. lia.
    eapply preord_res_refl; tci.
  Qed.

  Lemma preord_exp_Eproj_red k x ctag n y e rho v vs :
    M.get y rho = Some (Vconstr ctag vs) ->
    nthN vs n = Some v ->
    preord_exp cenv one_step eq_fuel k (e, M.set x v rho) (Eproj x ctag n y e, rho).
  Proof.
    intros Hget Hnth r cin cout Hleq Hbstep.
    do 3 eexists. split. econstructor 2. econstructor; eauto.
    split. simpl. unfold_all. lia.
    eapply preord_res_refl; tci.
  Qed.


  (** ** Correctness predicates *)

  (** P_fuel: Correctness for a single expression at top level.
      If the source evaluates to result [r] consuming [f] fuel and [t] trace,
      then the ANF conversion [C, x] simulates the source. *)
  Definition anf_cvt_correct_exp
             (vs : fuel_sem.env) (e : EAst.term)
             (r : fuel_sem.result) (f t : nat) :=
    forall rho vnames C x S S' i,
      well_formed_env Σ vs ->
      wellformed Σ (List.length vnames) e = true ->
      env_consistent vnames vs ->
      Disjoint _ (FromList vnames) S ->
      Disjoint _ (cmap_vars cmap) S ->
      anf_env_rel' vnames vs rho ->
      global_env_rel' (fun _ => True) rho ->
      anf_cvt_rel' S e vnames S' C x ->
      forall e_k,
        Disjoint _ (occurs_free e_k) ((S \\ S') \\ [set x]) ->
        (* Source terminates *)
        (forall v v', r = fuel_sem.Val v -> anf_val_rel' v v' ->
         preord_exp cenv (anf_bound f t) eq_fuel i
                    (e_k, M.set x v' rho) (C |[ e_k ]|, rho)) /\
        (* Source diverges *)
        (r = fuel_sem.OOT ->
         exists c, bstep_fuel cenv rho (C |[ e_k ]|) c eval.OOT tt).

  (** P_step: Correctness for a computation step.
      Same as [anf_cvt_correct_exp] but the fuel bound accounts for
      the step's own fuel consumption [one_i e]. *)
  Definition anf_cvt_correct_exp_step
             (vs : fuel_sem.env) (e : EAst.term)
             (r : fuel_sem.result) (f t : nat) :=
    forall rho vnames C x S S' i,
      well_formed_env Σ vs ->
      wellformed Σ (List.length vnames) e = true ->
      env_consistent vnames vs ->
      Disjoint _ (FromList vnames) S ->
      Disjoint _ (cmap_vars cmap) S ->
      anf_env_rel' vnames vs rho ->
      global_env_rel' (fun _ => True) rho ->
      anf_cvt_rel' S e vnames S' C x ->
      forall e_k,
        Disjoint _ (occurs_free e_k) ((S \\ S') \\ [set x]) ->
        (* Source terminates *)
        (forall v v', r = fuel_sem.Val v -> anf_val_rel' v v' ->
         preord_exp cenv
                    (anf_bound (f <+> @one_i _ _ fuel_resource_LambdaBox e)
                               (t <+> @one_i _ _ trace_resource_LambdaBox e))
                    eq_fuel i
                    (e_k, M.set x v' rho) (C |[ e_k ]|, rho)) /\
        (* Source diverges *)
        (r = fuel_sem.OOT ->
         exists c, bstep_fuel cenv rho (C |[ e_k ]|) c eval.OOT tt).

  (** P_many: Correctness for argument lists.
      If each argument evaluates, the ANF-converted arguments produce
      related values in the target env via [set_many]. *)
  Definition anf_cvt_correct_exps
             (vs_env : fuel_sem.env) (es : list EAst.term)
             (vs1 : list fuel_sem.value) (f t : nat) :=
    forall rho vnames C xs S S' i,
      well_formed_env Σ vs_env ->
      Forall (fun e => wellformed Σ (List.length vnames) e = true) es ->
      env_consistent vnames vs_env ->
      Disjoint _ (FromList vnames) S ->
      Disjoint _ (cmap_vars cmap) S ->
      anf_env_rel' vnames vs_env rho ->
      global_env_rel' (fun _ => True) rho ->
      anf_cvt_rel_args' S es vnames S' C xs ->
      forall e_k vs',
        Forall2 anf_val_rel' vs1 vs' ->
        Disjoint _ (occurs_free e_k) ((S \\ S') \\ FromList xs) ->
        preord_exp cenv (anf_bound f t) eq_fuel i
                   (e_k, set_many xs vs' rho)
                   (C |[ e_k ]|, rho).


  (** ** Main correctness theorem *)

  (** The proof proceeds by mutual induction using [eval_env_fuel_ind'].
      The scheme generates goals in order:
        P  (eval_env_step):  13 cases (App, FixApp, LetIn, Construct,
                             Case, Proj, Const + OOT variants)
        P0 (eval_fuel_many): 2 cases (nil, cons)
        P1 (eval_env_fuel):  6 cases (Rel, Lam, Fix, Box, OOT, Step) *)

  Lemma anf_cvt_correct :
    forall vs e r f t,
      src_eval vs e r f t ->
      anf_cvt_correct_exp vs e r f t.
  Proof.
    intros vs e r f t Heval.
    eapply (@eval_env_fuel_ind'
              nat LambdaBox_resource_fuel LambdaBox_resource_trace Σ box_dc
              (fun vs e r f t => anf_cvt_correct_exp_step vs e r f t)
              (fun vs es vs1 f t => anf_cvt_correct_exps vs es vs1 f t)).

    (* ================================================================ *)
    (* P cases: eval_env_step (13 cases)                                *)
    (* ================================================================ *)

    (* eval_App_step *)
    - intros e1 e2 body0 v2 r0 na0 rho0 rho' f1 f2 f3 t1 t2 t3
             Heval1 IH1 Heval2 IH2 Heval3 IH3.
      unfold anf_cvt_correct_exp_step.
      intros rho vnames C x S S' i Hwf Hwfe Hcons Hdis Hdis_cmap
             Henv Hglob Hrel e_k Hdis_ek.
      inv Hrel.
      split.
      + intros v v' Heq Hrel'. subst r0.
        admit. (* App termination: IH chaining *)
      + intros _. exists 0. eapply bstep_fuel_zero_OOT.

    (* eval_App_step_OOT1 *)
    - intros e1 e2 rho0 f1 t1 Heval1 IH1.
      unfold anf_cvt_correct_exp_step.
      intros rho vnames C x S S' i Hwf Hwfe Hcons Hdis Hdis_cmap Henv Hglob Hrel e_k Hdis_ek.
      split; [intros; congruence |
              intros _; exists 0; eapply bstep_fuel_zero_OOT].

    (* eval_App_step_OOT2 *)
    - intros e1 e2 v rho0 f1 f2 t1 t2 Heval1 IH1 Heval2 IH2.
      unfold anf_cvt_correct_exp_step.
      intros rho vnames C x S S' i Hwf Hwfe Hcons Hdis Hdis_cmap Henv Hglob Hrel e_k Hdis_ek.
      split; [intros; congruence |
              intros _; exists 0; eapply bstep_fuel_zero_OOT].

    (* eval_FixApp_step *)
    - intros e1 e2 body0 rho0 rho' rho'' idx0 na0 mfix0 v2 r0
             f1 f2 f3 t1 t2 t3
             Heval1 IH1 Hbody Hrec Heval2 IH2 Heval3 IH3.
      unfold anf_cvt_correct_exp_step.
      intros rho vnames C x S S' i Hwf Hwfe Hcons Hdis Hdis_cmap
             Henv Hglob Hrel e_k Hdis_ek.
      inv Hrel.
      split.
      + intros v v' Heq Hrel'. subst r0.
        admit. (* FixApp termination: IH chaining *)
      + intros _. exists 0. eapply bstep_fuel_zero_OOT.

    (* eval_LetIn_step *)
    - intros na0 b0 t0 v1 r0 rho0 f1 f2 t1 t2
             Heval1 IH1 Heval2 IH2.
      unfold anf_cvt_correct_exp_step.
      intros rho vnames C x S S' i Hwf Hwfe Hcons Hdis Hdis_cmap
             Henv Hglob Hrel e_k Hdis_ek.
      inv Hrel.
      (* After inv (anf_LetIn):
         C = comp_ctx_f C1 C2
         H8 : anf_cvt_rel' S b0 vnames S2 C1 x1
         H10 : anf_cvt_rel' S2 t0 (x1::vnames) S' C2 x *)
      match goal with
      | [ He1 : anf_cvt_rel _ _ _ _ _ b0 vnames _ _ _,
          He2 : anf_cvt_rel _ _ _ _ _ t0 (_ :: vnames) _ _ _ |- _ ] =>
        rename He1 into Hcvt_b; rename He2 into Hcvt_t
      end.
      rewrite <- app_ctx_f_fuse.
      split.
      + (* Termination *)
        intros v v' Heq Hrel'. subst r0.
        (* Need a target witness v1' for the intermediate value v1 *)
        assert (Hwf_v1 : well_formed_val Σ v1).
        { eapply eval_preserves_wf; [exact Hwf | | exact Heval1].
          rewrite (anf_env_rel_length _ _ _ Henv).
          exact (proj1 (wellformed_tLetIn _ _ _ _ Hwfe)). }
        destruct (@anf_val_rel_exists func_tag default_tag tgm cmap _ Σ box_dc
                    nat LambdaBox_resource_fuel LambdaBox_resource_trace
                    v1 Hwf_v1)
          as [v1' Hrel1].
        (* Chain: post_monotonic + trans(IH1, trans(IH2, refl)) *)
        eapply preord_exp_post_monotonic.
        2:{ eapply preord_exp_trans; [tci | exact eq_fuel_idemp | | ].
            (* Second chain: IH1 for b0 with continuation C2|[e_k]| *)
            2:{ intros m.
                edestruct IH1 as [IH1_val _].
                - exact Hwf.
                - exact (proj1 (wellformed_tLetIn _ _ _ _ Hwfe)).
                - exact Hcons.
                - exact Hdis.
                - exact Hdis_cmap.
                - exact Henv.
                - exact Hglob.
                - exact Hcvt_b.
                - eapply anf_cvt_disjoint_occurs_free_ctx; eassumption.
                - eapply IH1_val; eauto. }
            (* First chain: IH2 for t0 in extended env, composed with env bridge *)
            eapply preord_exp_trans; [tci | exact eq_fuel_idemp | | ].
            2:{ intros m.
                assert (Hwfe_t : wellformed Σ (Datatypes.length (x1 :: vnames)) t0 = true).
                { simpl. exact (proj2 (wellformed_tLetIn _ _ _ _ Hwfe)). }
                edestruct IH2 as [IH2_val _].
                - constructor; [exact Hwf_v1 | exact Hwf].
                - exact Hwfe_t.
                - eapply env_consistent_extend; eassumption.
                - (* Disjoint (FromList (x1::vnames)) S2 *)
                  assert (Hx1_not_S2 : ~ x1 \in S2)
                    by (eapply anf_cvt_result_not_in_output; eassumption).
                  assert (Hvn_S2 : Disjoint _ (FromList vnames) S2).
                  { eapply Disjoint_Included_r;
                    [exact (anf_cvt_exp_subset _ _ _ _ _ _ _ _ _ _ Hcvt_b) | exact Hdis]. }
                  constructor. intros z Hz. inv Hz.
                  unfold FromList, Ensembles.In in H. simpl in H.
                  destruct H as [<- | Hin_vn].
                  + exact (Hx1_not_S2 H0).
                  + eapply Hvn_S2. constructor; [exact Hin_vn | exact H0].
                - (* Disjoint (cmap_vars cmap) S2 *)
                  eapply Disjoint_Included_r;
                    [exact (anf_cvt_exp_subset _ _ _ _ _ _ _ _ _ _ Hcvt_b) | exact Hdis_cmap].
                - (* anf_env_rel' (x1::vnames) (v1::rho0) (M.set x1 v1' rho) *)
                  constructor.
                  + exists v1'. split; [rewrite M.gss; reflexivity | exact Hrel1].
                  + eapply anf_env_rel_set; [exact Henv |].
                    intros k Hk.
                    (* vnames[k] = x1. By env_consistent_extend, rho0[k] = v1 *)
                    assert (Hek : Some v1 = nth_error rho0 k).
                    { assert (Hcons_ext := env_consistent_extend
                                x1 vnames v1 rho0 b0 S S2 C1 f1 t1
                                Hcons Hdis Hdis_cmap Hcvt_b Heval1).
                      change var with positive in Hk.
                      exact (Hcons_ext 0 (Datatypes.S k) x1 eq_refl Hk). }
                    exists v1. split; [symmetry; exact Hek | exact Hrel1].
                - (* global_env_rel' for M.set x1 v1' rho *)
                  unfold global_env_rel' in *. intros kn vn0 Hd Hl.
                  destruct (Hglob kn vn0 Hd Hl) as [d1 [b1 [av [Hd1 [Hd2 [Hgv Hd3]]]]]].
                  destruct (Pos.eq_dec vn0 x1) as [-> | Hneq_vn].
                  + (* vn0 = x1: shadowed, but v1' satisfies the contract *)
                    exists d1, b1, v1'. repeat (split; [assumption |]).
                    split; [rewrite M.gss; reflexivity |].
                    (* v1' satisfies global contract: x1 is a cmap variable
                       from b0 = tConst kn', so v1 evaluates from the same
                       constant body, and value determinism gives src_v = v1 *)
                    intros src_v f' t' Heval_src.
                    (* v1' satisfies global contract for kn.
                       Uses: eval_tConst_inv, cmap_inj, eval_val_det. *)
                    admit. (* needs eval_tConst_inv + value det *)
                  + (* vn0 ≠ x1: M.gso *)
                    exists d1, b1, av. repeat (split; [assumption |]).
                    split; [rewrite M.gso; [exact Hgv | exact Hneq_vn] | exact Hd3].
                - exact Hcvt_t.
                - (* Disjoint (occurs_free e_k) ((S2 \\ S') \\ [set x]) *)
                  eapply Disjoint_Included_r; [| exact Hdis_ek].
                  intros z Hz. destruct Hz as [[Hz1 Hz2] Hz3].
                  constructor.
                  + constructor; [| exact Hz2].
                    eapply anf_cvt_exp_subset; [exact Hcvt_b | exact Hz1].
                  + exact Hz3.
                - eapply IH2_val; eauto. }
            (* Env bridge: M.set x v' rho ≤ M.set x v' (M.set x1 v1' rho) *)
            eapply preord_exp_refl. now eapply eq_fuel_compat.
            intros y Hy.
            destruct (Pos.eq_dec y x) as [-> | Hneq2].
            * (* y = x *)
              intros v1x Hget. rewrite M.gss in Hget. inv Hget.
              eexists. split. rewrite M.gss. reflexivity.
              eapply preord_val_refl. tci.
            * (* y ≠ x *)
              intros v1x Hget. rewrite M.gso in Hget; auto.
              destruct (Pos.eq_dec y x1) as [-> | Hneq1].
              -- (* y = x1: LHS has M.get x1 rho, RHS has v1'.
                    Both related to v1 via anf_val_rel', so preord_val by alpha-equiv. *)
                 (* M.get x1 rho must have a binding related to v1 *)
                 assert (Hget_x1 : exists w, M.get x1 rho = Some w /\ anf_val_rel' v1 w).
                 { destruct (anf_cvt_result_in_consumed _ _ _ _ _ _ Hcvt_b)
                     as [Hin_vn | [Hin_S | Hin_cm]].
                   - (* x1 ∈ FromList vnames: use env relation + env_consistent *)
                     unfold FromList, Ensembles.In in Hin_vn.
                     destruct (In_nth_error _ _ Hin_vn) as [k Hk].
                     change positive with var in Hk.
                     eapply (Forall2_nth_error_r _ _ _ k) in Henv; [| exact Hk].
                     destruct Henv as [v_k [Hnth_k [w' [Hget_w' Hrel_w']]]].
                     exists w'. split; [exact Hget_w' |].
                     (* rho0[k] = v1 by env_consistent *)
                     assert (Hcons_ext := env_consistent_extend
                               x1 vnames v1 rho0 b0 S S2 C1 f1 t1
                               Hcons Hdis Hdis_cmap Hcvt_b Heval1).
                     assert (Hek : Some v1 = nth_error rho0 k).
                     { change var with positive in Hk.
                       exact (Hcons_ext 0 (Datatypes.S k) x1 eq_refl Hk). }
                     rewrite <- Hek in Hnth_k. injection Hnth_k as <-.
                     exact Hrel_w'.
                   - (* x1 ∈ S: contradiction — x1 ∈ occurs_free e_k ∩ (S\\S'\\{x}) *)
                     exfalso. eapply Hdis_ek. constructor; [exact Hy |].
                     constructor.
                     * constructor.
                       -- exact Hin_S.
                       -- intro Hin_S'.
                          eapply (anf_cvt_result_not_in_output _ _ _ _ _ _ _ _ _ _ Hcvt_b Hdis Hdis_cmap).
                          eapply (anf_cvt_exp_subset _ _ _ _ _ _ _ _ _ _ Hcvt_t). exact Hin_S'.
                     * intro Habs. inv Habs. exact (Hneq2 eq_refl).
                   - (* x1 ∈ cmap_vars: use global_env_rel' *)
                     destruct Hin_cm as [kn_x Hlk_x].
                     unfold global_env_rel' in Hglob.
                     destruct (Hglob kn_x x1 I Hlk_x) as [dx [bx [avx [Hdx [Hbx [Hgx Hrx]]]]]].
                     exists avx. split; [exact Hgx |].
                     (* anf_val_rel' v1 avx: uses eval_tConst_inv + value det *)
                     admit. (* needs eval_tConst_inv + value det *)
                 }
                 destruct Hget_x1 as [w [Hget_w Hrel_w]].
                 rewrite Hget_w in Hget. injection Hget as <-.
                 eexists. split.
                 { rewrite M.gso; auto. rewrite M.gss. reflexivity. }
                 eapply (@anf_cvt_val_alpha_equiv
                           _ _ _ _ eq_fuel eq_fuel tgm cmap cenv
                           eq_fuel_compat (fun _ _ H => H)
                           nat LambdaBox_resource_fuel LambdaBox_resource_trace
                           Σ box_dc Hglob_term func_tag default_tag);
                   [exact Hrel_w | exact Hrel1].
              -- (* y ≠ x1 *)
                 eexists. split.
                 { rewrite M.gso; auto. rewrite M.gso; eauto. }
                 eapply preord_val_refl. tci. }
        (* inclusion *)
        unfold inclusion, comp, eq_fuel, anf_bound.
        intros [[[? ?] ?] ?] [[[? ?] ?] ?] Hcomp.
        repeat match goal with
        | [ H : exists _, _ |- _ ] => destruct H
        | [ H : _ /\ _ |- _ ] => destruct H
        | [ p : _ * _ * _ * _ |- _ ] => destruct p
        end.
        repeat match goal with
        | [ p : _ * _ |- _ ] => destruct p
        end.
        unfold_all. cbn in *. lia.
      + (* Divergence *)
        intros _. exists 0. eapply bstep_fuel_zero_OOT.

    (* eval_LetIn_step_OOT *)
    - intros na b t0 rho0 f1 t1 Heval1 IH1.
      unfold anf_cvt_correct_exp_step.
      intros rho vnames C x S S' i Hwf Hwfe Hcons Hdis Hdis_cmap Henv Hglob Hrel e_k Hdis_ek.
      split; [intros; congruence |
              intros _; exists 0; eapply bstep_fuel_zero_OOT].

    (* eval_Construct_step *)
    - intros ind c args vs0 rho0 dc fs ts
             Hdc Heval_args IH_args.
      unfold anf_cvt_correct_exp_step.
      intros rho vnames C x S S' i Hwf Hwfe Hcons Hdis Hdis_cmap
             Henv Hglob Hrel e_k Hdis_ek.
      inv Hrel.
      split.
      + intros v v' Heq Hrel'. injection Heq as <-.
        admit. (* Construct termination *)
      + intros Habs. congruence.

    (* eval_Construct_step_OOT *)
    - intros ind c args args_done args_rest e0 vs0 rho0 fs f0 t0 ts
             Hargs_eq Heval_done IH_done Heval_oot IH_oot.
      unfold anf_cvt_correct_exp_step.
      intros rho vnames C x S S' i Hwf Hwfe Hcons Hdis Hdis_cmap Henv Hglob Hrel e_k Hdis_ek.
      split; [intros; congruence |
              intros _; exists 0; eapply bstep_fuel_zero_OOT].

    (* eval_Case_step *)
    - intros ind npars mch brs rho0 dc vs0 body0 c0 r0
             f1 f2 t1 t2
             Heval_mch IH_mch Hdc Hbranch Heval_body IH_body.
      unfold anf_cvt_correct_exp_step.
      intros rho vnames C x S S' i Hwf Hwfe Hcons Hdis Hdis_cmap
             Henv Hglob Hrel e_k Hdis_ek.
      inv Hrel.
      split.
      + intros v v' Heq Hrel'. subst r0.
        admit. (* Case termination: IH chaining *)
      + intros _. exists 0. eapply bstep_fuel_zero_OOT.

    (* eval_Case_step_OOT *)
    - intros ind npars mch brs rho0 f1 t1 Heval1 IH1.
      unfold anf_cvt_correct_exp_step.
      intros rho vnames C x S S' i Hwf Hwfe Hcons Hdis Hdis_cmap Henv Hglob Hrel e_k Hdis_ek.
      split; [intros; congruence |
              intros _; exists 0; eapply bstep_fuel_zero_OOT].

    (* eval_Proj_step *)
    - intros p0 c0 rho0 dc vs0 v0 f1 t1
             Heval_c IH_c Hnth_proj.
      unfold anf_cvt_correct_exp_step.
      intros rho vnames C x S S' i Hwf Hwfe Hcons Hdis Hdis_cmap
             Henv Hglob Hrel e_k Hdis_ek.
      inv Hrel.
      split.
      + intros v v' Heq Hrel'. injection Heq as <-.
        (* ANF: comp_ctx_f C_sub (Eproj_c y c_tag (N.of_nat proj_arg) x_sub Hole_c) *)
        (* Chain: IH for c0 + Eproj reduction + env bridging *)
        admit. (* Proj: follows LetIn pattern with IH + Eproj_red *)
      + intros Habs. congruence.

    (* eval_Proj_step_OOT *)
    - intros p c rho0 f1 t1 Heval1 IH1.
      unfold anf_cvt_correct_exp_step.
      intros rho vnames C x S S' i Hwf Hwfe Hcons Hdis Hdis_cmap Henv Hglob Hrel e_k Hdis_ek.
      split; [intros; congruence |
              intros _; exists 0; eapply bstep_fuel_zero_OOT].

    (* eval_Const_step *)
    - intros k0 body0 decl0 rho0 r0 f0 t0
             Hdecl Hbody Heval_body IH_body.
      unfold anf_cvt_correct_exp_step.
      intros rho vnames C x S S' i Hwf Hwfe Hcons Hdis Hdis_cmap
             Henv Hglob Hrel e_k Hdis_ek.
      inv Hrel.
      (* anf_Const: C = Hole_c, x = v from lookup_const cmap k0 *)
      split.
      + intros v v' Heq Hrel'. subst r0.
        admit. (* Const: needs special treatment — bound is anf_bound (f0+1) (t0+1) but target is free *)
      + intros _. exists 0. eapply bstep_fuel_zero_OOT.

    (* ================================================================ *)
    (* P0 cases: eval_fuel_many (2 cases)                               *)
    (* ================================================================ *)

    (* eval_many_nil *)
    - intros rho0.
      unfold anf_cvt_correct_exps.
      intros rho vnames C xs S S' i Hwf Hwfe Hcons Hdis Hdis_cmap
             Henv Hglob Hrel e_k vs' Hvs' Hdis_ek.
      inversion Hrel; subst. inversion Hvs'; subst.
      (* C = Hole_c, xs = [], vs' = [] *)
      change (Hole_c |[ e_k ]|) with e_k.
      change (set_many [] [] rho) with rho.
      eapply (preord_exp_post_monotonic cenv _ eq_fuel).
      { intros [[[? ?] ?] ?] [[[? ?] ?] ?] Heq.
        unfold anf_bound, eq_fuel in *. cbn in *. lia. }
      eapply preord_exp_refl. exact eq_fuel_compat.
      intros y Hy v1 Hget. eexists. split; [exact Hget |].
      eapply preord_val_refl. tci.
    (* eval_many_cons *)
    - intros rho0 e0 es0 v0 vs0 f0 fs0 t0 ts0
             Heval_e IH_e Heval_es IH_es.
      unfold anf_cvt_correct_exps.
      intros rho vnames C xs S S' i Hwf Hwfe Hcons Hdis Hdis_cmap
             Henv Hglob Hrel e_k vs' Hvs' Hdis_ek.
      inv Hrel. inv Hvs'.
      admit. (* Cons case: IH chaining *)

    (* ================================================================ *)
    (* P1 cases: eval_env_fuel (6 cases)                                *)
    (* ================================================================ *)

    (* eval_Rel_fuel *)
    - intros n rho0 v Hnth.
      unfold anf_cvt_correct_exp.
      intros rho vnames C x S S' i Hwf Hwfe Hcons Hdis Hdis_cmap Henv Hglob Hrel e_k Hdis_ek.
      inv Hrel. split.
      + (* Termination *)
        intros v0 v' Heq Hvrel. injection Heq as <-.
        change (Hole_c |[ e_k ]|) with e_k.
        eapply (preord_exp_post_monotonic cenv _ eq_fuel).
        { intros [[[? ?] ?] ?] [[[? ?] ?] ?] Heq.
          unfold anf_bound, eq_fuel in *. cbn in *. lia. }
        eapply preord_exp_refl. exact eq_fuel_compat.
        (* preord_env_P eq_fuel (occurs_free e_k) i (M.set x v' rho) rho *)
        intros y Hy.
        destruct (Pos.eq_dec y x) as [-> | Hneq].
        * (* y = x: v' and rho(x) both related to v *)
          unfold preord_var_env. intros w Hget.
          rewrite M.gss in Hget. inv Hget.
          match goal with
          | [ Henv : anf_env_rel' _ _ _ |- _ ] =>
            unfold anf_env_rel' in Henv;
            eapply Forall2_nth_error_l in Henv; [| exact Hnth]
          end.
          destruct Henv as [x0 [Hnth_x [w' [Hget' Hvrel']]]].
          change positive with var in Hnth_x.
          rewrite H1 in Hnth_x. inv Hnth_x.
          eexists. split. exact Hget'.
          eapply (@anf_cvt_val_alpha_equiv
                    _ _ _ _ eq_fuel eq_fuel tgm cmap cenv
                    eq_fuel_compat (fun _ _ H => H)
                    nat LambdaBox_resource_fuel LambdaBox_resource_trace
                    Σ box_dc Hglob_term func_tag default_tag);
            eassumption.
        * (* y ≠ x: M.gso, reflexivity *)
          unfold preord_var_env. intros w Hget.
          rewrite M.gso in Hget; [| exact Hneq].
          eexists. split. exact Hget.
          eapply preord_val_refl. exact eq_fuel_compat.
      + (* Divergence: Val ≠ OOT *)
        intros Heq. discriminate.
    (* eval_Lam_fuel *)
    - intros body0 rho0 na0.
      unfold anf_cvt_correct_exp.
      intros rho vnames C x S S' i Hwf Hwfe Hcons Hdis Hdis_cmap Henv Hglob Hrel e_k Hdis_ek.
      inv Hrel.
      (* After inv (anf_Lam):
         C = Efun1_c (Fcons f func_tag [x1] (C1 |[ Ehalt r1 ]|) Fnil) Hole_c
         x = f, S' = S'0
         H5 : x1 \in S, H7 : f \in S \\ [set x1]
         H9 : anf_cvt_rel' (S \\ [set x1] \\ [set f]) body0 (x1::vnames) S'0 C1 r1 *)
      split.
      + (* Termination *)
        intros v0 v' Heq Hvrel. injection Heq as <-.
        eapply preord_exp_post_monotonic.
        2:{ eapply preord_exp_trans; [tci | exact eq_fuel_idemp | | ].
            2:{ intros m. eapply preord_exp_Efun_red. }
            eapply preord_exp_refl. now eapply eq_fuel_compat.
            intros y Hy.
            destruct (Pos.eq_dec y x) as [Heq | Hneq].
            - subst. intros v1 Hget. rewrite M.gss in Hget. inv Hget.
              eexists. split.
              { cbn [def_funs]. rewrite M.gss. reflexivity. }
              eapply (@anf_cvt_val_alpha_equiv
                        _ _ _ _ eq_fuel eq_fuel tgm cmap cenv
                        eq_fuel_compat (fun _ _ H => H)
                        nat LambdaBox_resource_fuel LambdaBox_resource_trace
                        Σ box_dc Hglob_term func_tag default_tag).
              + eassumption.
              + eapply anf_rel_Clos
                  with (names := vnames) (S1 := S \\ [set x1] \\ [set x]);
                  try eassumption.
                (* Disjoint (x1 |: (x |: FromList vnames)) (S \\ {x1} \\ {x}) *)
                * { eapply Union_Disjoint_l.
                    - eapply Disjoint_Singleton_l.
                      intros [[_ Habs] _]. apply Habs. constructor.
                    - eapply Union_Disjoint_l.
                      + eapply Disjoint_Singleton_l.
                        intros [_ Habs]. apply Habs. constructor.
                      + eapply Disjoint_Included_r.
                        { eapply Included_trans; eapply Setminus_Included. }
                        exact Hdis. }
                (* Disjoint (cmap_vars cmap) (S \\ {x1} \\ {x}) *)
                * { eapply Disjoint_Included_r.
                    - eapply Included_trans; eapply Setminus_Included.
                    - exact Hdis_cmap. }
                (* ~ x1 ∈ cmap_vars cmap *)
                * { intro Hc. eapply Hdis_cmap. constructor; [exact Hc | exact H1]. }
                (* ~ x ∈ cmap_vars cmap *)
                * { intro Hc. destruct H3.
                    eapply Hdis_cmap. constructor; [exact Hc | assumption]. }
                (* ~ x1 ∈ x |: FromList vnames *)
                * { intro Hc. inv Hc.
                    - (* x1 ∈ {x}, i.e. x1 = x *)
                      inv H. destruct H3 as [_ Habs]. apply Habs. constructor.
                    - (* x1 ∈ FromList vnames *)
                      eapply Hdis. constructor; [exact H | exact H1]. }
                (* ~ x ∈ FromList vnames *)
                * { intro Hc. destruct H3.
                    eapply Hdis. constructor; [exact Hc | assumption]. }
                (* global_env_rel' restricted to term_global_deps body0 *)
                * { unfold anf_util.global_env_rel', global_env_rel' in *.
                    intros k v0 Hdep Hlook.
                    eapply Hglob; [exact I | exact Hlook]. }
            - intros v1 Hget. rewrite M.gso in Hget; eauto.
              eexists. split.
              { cbn [def_funs]. rewrite M.gso; eauto. }
              eapply preord_val_refl. tci. }
        unfold inclusion, comp, eq_fuel, one_step, anf_bound.
        intros [[[? ?] ?] ?] [[[? ?] ?] ?] [[[[? ?] ?] ?] [? ?]].
        unfold_all. cbn in *. lia.
      + (* Divergence: Val ≠ OOT *)
        intros Habs. congruence.
    (* eval_Fix_fuel *)
    - intros mfix0 idx0 rho0.
      unfold anf_cvt_correct_exp.
      intros rho vnames C x S S' i Hwf Hwfe Hcons Hdis Hdis_cmap Henv Hglob Hrel e_k Hdis_ek.
      inv Hrel.
      (* anf_Fix: C = Efun1_c fdefs Hole_c, x = f *)
      split.
      + intros v0 v' Heq Hvrel. injection Heq as <-.
        eapply preord_exp_post_monotonic.
        2:{ eapply preord_exp_trans; [tci | exact eq_fuel_idemp | | ].
            2:{ intros m. eapply preord_exp_Efun_red. }
            eapply preord_exp_refl. now eapply eq_fuel_compat.
            intros y Hy.
            destruct (Pos.eq_dec y x) as [Heq | Hneq].
            - subst. intros v1 Hget. rewrite M.gss in Hget. inv Hget.
              eexists. split.
              { eapply def_funs_eq.
                apply (proj2 (Same_set_all_fun_name _)).
                erewrite anf_cvt_rel_mfix_all_fun_name by eassumption.
                eapply nth_error_In. eassumption. }
              eapply (@anf_cvt_val_alpha_equiv
                        _ _ _ _ eq_fuel eq_fuel tgm cmap cenv
                        eq_fuel_compat (fun _ _ H => H)
                        nat LambdaBox_resource_fuel LambdaBox_resource_trace
                        Σ box_dc Hglob_term func_tag default_tag).
              + eassumption.
              + eapply anf_rel_ClosFix
                  with (names := vnames) (S1 := S \\ FromList fnames);
                  try eassumption.
                (* Disjoint (FromList vnames :|: FromList fnames) (S \\ FromList fnames) *)
                * { eapply Union_Disjoint_l.
                    - eapply Disjoint_Included_r; [eapply Setminus_Included | exact Hdis].
                    - eapply Disjoint_Setminus_r. eapply Included_refl. }
                (* Disjoint (cmap_vars cmap) (S \\ FromList fnames) *)
                * { eapply Disjoint_Included_r; [eapply Setminus_Included | exact Hdis_cmap]. }
                (* Disjoint (cmap_vars cmap) (FromList fnames) *)
                * { eapply Disjoint_Included_r; [exact H1 | exact Hdis_cmap]. }
                (* Disjoint (FromList vnames) (FromList fnames) *)
                * { eapply Disjoint_Included_r; [exact H1 | exact Hdis]. }
                (* anf_fix_rel *)
                * { eapply anf_cvt_rel_mfix_to_fix_rel; [ eassumption | ].
                    eapply Disjoint_sym. eapply Union_Disjoint_l.
                    - eapply Disjoint_Setminus_r. eapply Included_refl.
                    - eapply Disjoint_Included_r; [eapply Setminus_Included |].
                      exact Hdis. }
                (* global_env_rel' *)
                * { unfold anf_util.global_env_rel', global_env_rel' in *.
                    intros k v0 Hdep Hlook.
                    eapply Hglob; [exact I | exact Hlook]. }
            - intros v1 Hget. rewrite M.gso in Hget; eauto.
              eexists. split.
              { rewrite def_funs_neq; eauto.
                intros Hc. apply (proj1 (Same_set_all_fun_name _)) in Hc.
                erewrite anf_cvt_rel_mfix_all_fun_name in Hc by eassumption.
                eapply Hdis_ek. constructor; [exact Hy |].
                constructor.
                - constructor; [eapply H1; exact Hc |].
                  intros Hin_S'.
                  assert (Hsub_mfix : S' \subset S \\ FromList fnames)
                    by (eapply anf_cvt_mfix_subset; eassumption).
                  apply Hsub_mfix in Hin_S'. destruct Hin_S' as [_ Habs].
                  apply Habs. exact Hc.
                - intro Habs. inv Habs. contradiction. }
              eapply preord_val_refl. tci. }
        unfold inclusion, comp, eq_fuel, one_step, anf_bound.
        intros [[[? ?] ?] ?] [[[? ?] ?] ?] [[[[? ?] ?] ?] [? ?]].
        unfold_all. cbn in *. lia.
      + intros Habs. congruence.
    (* eval_Box_fuel *)
    - intros rho0.
      unfold anf_cvt_correct_exp.
      intros rho vnames C x S S' i Hwf Hwfe Hcons Hdis Hdis_cmap Henv Hglob Hrel e_k Hdis_ek.
      inv Hrel.
      (* anf_Box: C = Econstr_c x default_tag nil Hole_c *)
      split.
      + intros v0 v' Heq Hvrel. injection Heq as <-.
        eapply preord_exp_post_monotonic.
        2:{ eapply preord_exp_trans; [tci | exact eq_fuel_idemp | | ].
            2:{ intros m. eapply preord_exp_Econstr_red.
                simpl. reflexivity. }
            eapply preord_exp_refl. now eapply eq_fuel_compat.
            intros y Hy.
            destruct (Pos.eq_dec y x) as [Heq | Hneq].
            - subst. intros v1 Hget. rewrite M.gss in Hget. inv Hget.
              eexists. split. rewrite M.gss. reflexivity.
              (* v' related to Con_v box_dc [], target is Vconstr default_tag [] *)
              (* Design issue: needs dcon_to_tag default_tag box_dc tgm = default_tag.
                 Requires either fixing box_dc in eval_Box_fuel or
                 adding a well-formedness constraint. *)
              inv Hvrel.
              match goal with
              | [ H : Forall2 _ [] ?vs |- _ ] => inv H
              end.
              rewrite preord_val_eq. simpl. split; [| constructor].
              exact box_tag.
            - intros v1 Hget. rewrite M.gso in Hget; eauto.
              eexists. split. rewrite M.gso; eauto.
              eapply preord_val_refl. tci. }
        unfold inclusion, comp, eq_fuel, one_step, anf_bound.
        intros [[[? ?] ?] ?] [[[? ?] ?] ?] [[[[? ?] ?] ?] [? ?]].
        unfold_all. cbn in *. lia.
      + intros Habs. congruence.
    (* eval_OOT *)
    - intros rho0 e0 f0 t0 Hfuel_lt.
      unfold anf_cvt_correct_exp.
      intros rho vnames C x S S' i Hwf Hwfe Hcons Hdis Hdis_cmap Henv Hglob Hrel e_k Hdis_ek.
      split.
      + (* Termination: vacuous — OOT ≠ Val *)
        intros v v' Heq. discriminate.
      + (* Divergence: target OOTs with fuel 0 *)
        intros _.
        exists 0. eapply bstep_fuel_zero_OOT.
    (* eval_step *)
    - intros rho0 e0 r0 f0 t0 Hstep IH_step.
      unfold anf_cvt_correct_exp, anf_cvt_correct_exp_step in *.
      intros. eapply IH_step; eassumption.

    - exact Heval.
  Admitted.

End Correct.
