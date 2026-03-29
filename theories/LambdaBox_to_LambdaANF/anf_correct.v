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

  Lemma wellformed_tApp n e1 e2 :
    wellformed Σ n (EAst.tApp e1 e2) = true ->
    wellformed Σ n e1 = true /\ wellformed Σ n e2 = true.
  Proof.
    unfold wellformed. simpl. fold (@wellformed efl).
    intro H. apply andb_true_iff in H. destruct H as [H1 H2].
    apply andb_true_iff in H1. destruct H1 as [H1a H1b].
    split; assumption.
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

  (* Weakening: if x ∉ FromList vnames, adding x to rho preserves anf_env_rel *)
  Lemma anf_env_rel_weaken vnames vs0 x v rho :
    anf_env_rel' vnames vs0 rho ->
    ~ x \in FromList vnames ->
    anf_env_rel' vnames vs0 (M.set x v rho).
  Proof.
    intros Henv Hni.
    eapply anf_env_rel_set; [exact Henv |].
    intros k Hk. exfalso. apply Hni. eapply nth_error_In. exact Hk.
  Qed.

  (* global_env_rel' weakening: if x is not a cmap variable, M.set preserves it *)
  Lemma global_env_rel_set_fresh D rho x w :
    global_env_rel' D rho ->
    ~ x \in cmap_vars cmap ->
    global_env_rel' D (M.set x w rho).
  Proof.
    intros Hglob Hni k v Hd Hlk.
    assert (Hneq : v <> x).
    { intro Heq. subst. apply Hni. exists k. exact Hlk. }
    destruct (Hglob k v Hd Hlk) as (decl & body & anf_v & Hdecl & Hbody & Hget & Hrel).
    exists decl, body, anf_v. repeat split; try assumption.
    rewrite M.gso; [exact Hget | exact Hneq].
  Qed.

  (* global_env_rel' under M.set: general case where x may be a cmap variable *)
  Lemma global_env_rel_set D rho x w :
    global_env_rel' D rho ->
    (forall k, D k -> lookup_const cmap k = Some x ->
      forall decl body, declared_constant Σ k decl ->
      decl.(EAst.cst_body) = Some body ->
      forall src_v f_s t_s, src_eval [] body (fuel_sem.Val src_v) f_s t_s ->
      anf_val_rel' src_v w) ->
    global_env_rel' D (M.set x w rho).
  Proof.
    intros Hglob Hx k v Hd Hlk.
    destruct (Pos.eq_dec v x) as [-> | Hneq].
    - destruct (Hglob k x Hd Hlk) as (decl & body & anf_v & Hdecl & Hbody & Hget & Hrel).
      exists decl, body, w. repeat split; try assumption.
      + rewrite M.gss. reflexivity.
      + intros src_v f_s t_s Heval_s. eapply Hx; eassumption.
    - destruct (Hglob k v Hd Hlk) as (decl & body & anf_v & Hdecl & Hbody & Hget & Hrel).
      exists decl, body, anf_v. repeat split; try assumption.
      rewrite M.gso; [exact Hget | exact Hneq].
  Qed.

  (* global_env_rel' monotonicity: weaken the domain *)
  Lemma global_env_rel_mono D1 D2 rho :
    global_env_rel' D1 rho ->
    D2 \subset D1 ->
    global_env_rel' D2 rho.
  Proof.
    intros Hglob Hsub k v Hd Hlk. exact (Hglob k v (Hsub k Hd) Hlk).
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

  (** ** cmap_consistent: provenance invariant for global constants.
      If position [i] in [vn] holds a cmap variable for constant [k],
      then [rho[i]] exists and is the result of evaluating [k]'s body. *)
  Definition cmap_consistent (vn : list var) (rho : list fuel_sem.value) : Prop :=
    forall i x k decl body,
      nth_error vn i = Some x ->
      lookup_const cmap k = Some x ->
      declared_constant Σ k decl ->
      decl.(EAst.cst_body) = Some body ->
      exists v_i f t,
        nth_error rho i = Some v_i /\
        src_eval [] body (fuel_sem.Val v_i) f t.

  (** env_consistent extends when all duplicates of x1 map to v1 in rho.
      Same as old proof (trivial 4-line lemma). *)
  Lemma env_consistent_extend vn rho x1 v1 :
    env_consistent vn rho ->
    (forall k, nth_error vn k = Some x1 -> nth_error rho k = Some v1) ->
    env_consistent (x1 :: vn) (v1 :: rho).
  Proof.
    intros Hcons Hx1 i j y Hi Hj.
    destruct i as [|i'], j as [|j']; simpl in *.
    - reflexivity.
    - injection Hi as <-. specialize (Hx1 j' Hj). rewrite Hx1. reflexivity.
    - injection Hj as <-. specialize (Hx1 i' Hi). rewrite Hx1. reflexivity.
    - eapply Hcons; eassumption.
  Qed.

  (** cmap_consistent extends when the new binding satisfies the condition. *)
  Lemma cmap_consistent_extend vn rho x1 v1 :
    cmap_consistent vn rho ->
    (forall k decl body,
      lookup_const cmap k = Some x1 ->
      declared_constant Σ k decl ->
      decl.(EAst.cst_body) = Some body ->
      exists f t, src_eval [] body (fuel_sem.Val v1) f t) ->
    cmap_consistent (x1 :: vn) (v1 :: rho).
  Proof.
    intros Hcm Hx1 i x k decl body Hnth_vn Hlk Hdecl Hbody.
    destruct i as [|i']; simpl in *.
    - injection Hnth_vn as <-.
      destruct (Hx1 k decl body Hlk Hdecl Hbody) as [f [t Hev]].
      exists v1, f, t. split; [reflexivity | exact Hev].
    - exact (Hcm i' x k decl body Hnth_vn Hlk Hdecl Hbody).
  Qed.

  (** Combined lemma proving both var_lookup and cmap_eval simultaneously.
      Part 1 (var lookup): if vn[i] = x then rho[i] = v.
      Part 2 (cmap eval): if lookup_const cmap k = Some x then eval [] body_k (Val v).
      Both are needed simultaneously because the LetIn case builds
      cmap_consistent using Part 2's IH for the binding.
      The conjunction is placed after the shared hypotheses so that
      intros works uniformly for both parts in each case. *)
  Lemma anf_cvt_rel_var_lookup_and_cmap_eval :
    forall rho e r f t,
      src_eval rho e r f t ->
      forall v, r = fuel_sem.Val v ->
      forall S vn S' C x,
        anf_cvt_rel' S e vn S' C x ->
        Disjoint _ (FromList vn) S ->
        Disjoint _ (cmap_vars cmap) S ->
        env_consistent vn rho ->
        cmap_consistent vn rho ->
        (* Part 1 *) (forall i, nth_error vn i = Some x -> nth_error rho i = Some v) /\
        (* Part 2 *) (forall k decl body,
                        lookup_const cmap k = Some x ->
                        declared_constant Σ k decl ->
                        decl.(EAst.cst_body) = Some body ->
                        exists f' t', src_eval [] body (fuel_sem.Val v) f' t').
  Proof.
    pose (Pcombined := fun (rho : list fuel_sem.value) (e : EAst.term)
                            (r : fuel_sem.result) (f : nat) (t : nat) =>
      forall v, r = fuel_sem.Val v ->
      forall S vn S' C x,
        anf_cvt_rel' S e vn S' C x ->
        Disjoint _ (FromList vn) S ->
        Disjoint _ (cmap_vars cmap) S ->
        env_consistent vn rho ->
        cmap_consistent vn rho ->
        (forall i, nth_error vn i = Some x -> nth_error rho i = Some v) /\
        (forall k decl body,
           lookup_const cmap k = Some x ->
           declared_constant Σ k decl ->
           decl.(EAst.cst_body) = Some body ->
           exists f' t', src_eval [] body (fuel_sem.Val v) f' t')).
    intros rho e r f t Heval.
    eapply (@eval_env_fuel_ind'
              nat LambdaBox_resource_fuel LambdaBox_resource_trace Σ box_dc
              Pcombined
              (fun _ _ _ _ _ => True)
              Pcombined);
    unfold Pcombined; clear Pcombined;
      try (intros; exact I);
      try (intros; congruence).

    (* Remaining 12 goals. Each case intros shared hypotheses, then splits. *)

    - (* App: x ∈ S3 ⊆ S2 ⊆ S, contradiction *)
      intros ? ? ? ? ? ? ? ? ? ? ? ? ? ?
             ? IH1 ? IH2 ? IH3
             v Hv S0 vn0 S0' C0 x0 Hcvt Hdis Hdis_cm Hcons Hcmap.
      subst.
      remember (EAst.tApp _ _) as e_app.
      destruct Hcvt; try discriminate.
      injection Heqe_app as <- <-.
      split.
      + intros i Hnth_i. exfalso. eapply Hdis. constructor.
        * eapply nth_error_In. exact Hnth_i.
        * eapply anf_cvt_exp_subset; [eassumption |].
          eapply anf_cvt_exp_subset; [eassumption |]. assumption.
      + intros k_f decl_f body_f Hlk_f _ _. exfalso. eapply Hdis_cm. constructor.
        * exists k_f. exact Hlk_f.
        * eapply anf_cvt_exp_subset; [eassumption |].
          eapply anf_cvt_exp_subset; [eassumption |]. assumption.

    - (* FixApp *)
      intros ? ? ? ? ? ? ? ? ? ? ?
             ? ? ? ? ? ? ? IH1 ? ? ? IH2 ? IH3
             v Hv S0 vn0 S0' C0 x0 Hcvt Hdis Hdis_cm Hcons Hcmap.
      subst.
      remember (EAst.tApp _ _) as e_app.
      destruct Hcvt; try discriminate.
      injection Heqe_app as <- <-.
      split.
      + intros i Hnth_i. exfalso. eapply Hdis. constructor.
        * eapply nth_error_In. exact Hnth_i.
        * eapply anf_cvt_exp_subset; [eassumption |].
          eapply anf_cvt_exp_subset; [eassumption |]. assumption.
      + intros k_f decl_f body_f Hlk_f _ _. exfalso. eapply Hdis_cm. constructor.
        * exists k_f. exact Hlk_f.
        * eapply anf_cvt_exp_subset; [eassumption |].
          eapply anf_cvt_exp_subset; [eassumption |]. assumption.

    - (* LetIn: the key recursive case *)
      intros na_l b_l t_l v_b r_l rho_l f_b f_t t_b t_t
             Heval_b IH_b Heval_t IH_t
             v Hv S0 vn0 S0' C0 x0 Hcvt Hdis Hdis_cm Hcons Hcmap.
      subst r_l.
      remember (EAst.tLetIn na_l b_l t_l) as e_l.
      destruct Hcvt; try discriminate.
      injection Heqe_l as <- <- <-.
      (* Hcvt1 : anf_cvt_rel' S1 b vn S2 C1 x1
         Hcvt2 : anf_cvt_rel' S2 t0 (x1::vn) S3 C2 x2 *)
      assert (Hdis2 : Disjoint _ (FromList (x1 :: vn)) S2).
      { rewrite FromList_cons. eapply Union_Disjoint_l.
        - eapply Disjoint_Singleton_l.
          eapply anf_cvt_result_not_in_output; eassumption.
        - eapply Disjoint_Included_r.
          eapply anf_cvt_exp_subset. eassumption. eassumption. }
      assert (Hdis_cm2 : Disjoint _ (cmap_vars cmap) S2).
      { eapply Disjoint_Included_r;
          [eapply anf_cvt_exp_subset; eassumption | exact Hdis_cm]. }
      assert (Hcons2 : env_consistent (x1 :: vn) (v_b :: rho_l)).
      { eapply env_consistent_extend; [exact Hcons |].
        intros k Hk.
        exact (proj1 (IH_b v_b eq_refl _ _ _ _ _ Hcvt1 Hdis Hdis_cm Hcons Hcmap) k Hk). }
      assert (Hcmap2 : cmap_consistent (x1 :: vn) (v_b :: rho_l)).
      { eapply cmap_consistent_extend; [exact Hcmap |].
        intros k decl body Hlk Hdecl Hbody.
        exact (proj2 (IH_b v_b eq_refl _ _ _ _ _ Hcvt1 Hdis Hdis_cm Hcons Hcmap)
                      k decl body Hlk Hdecl Hbody). }
      destruct (IH_t v eq_refl _ _ _ _ _ Hcvt2 Hdis2 Hdis_cm2 Hcons2 Hcmap2)
        as [IH_t_lookup IH_t_cmap].
      split.
      + (* Part 1: var lookup at index i in original vn *)
        intros i Hnth. exact (IH_t_lookup (Datatypes.S i) Hnth).
      + (* Part 2: cmap eval *)
        exact IH_t_cmap.

    - (* Construct *)
      intros ? ? ? ? ? ? ? ? ? ? ?
             v Hv S0 vn0 S0' C0 x0 Hcvt Hdis Hdis_cm Hcons Hcmap.
      injection Hv as <-.
      remember (EAst.tConstruct _ _ _) as e_c.
      destruct Hcvt; try discriminate. clear Heqe_c.
      split.
      + intros i Hnth_i. exfalso. eapply Hdis. constructor.
        * eapply nth_error_In. exact Hnth_i.
        * assumption.
      + intros k_f decl_f body_f Hlk_f _ _. exfalso. eapply Hdis_cm. constructor.
        * exists k_f. exact Hlk_f.
        * assumption.

    - (* Case *)
      intros ? ? ? ? ? ? ? ? ? ? ? ? ? ?
             ? IH_mch ? ? ? IH_body
             v Hv S0 vn0 S0' C0 x0 Hcvt Hdis Hdis_cm Hcons Hcmap.
      subst.
      remember (EAst.tCase _ _ _) as e_case.
      destruct Hcvt; try discriminate. clear Heqe_case.
      split.
      + intros i Hnth_i. exfalso. eapply Hdis. constructor.
        * eapply nth_error_In. exact Hnth_i.
        * eapply Setminus_Included. eapply Setminus_Included.
          eapply anf_cvt_exp_subset; [eassumption |].
          eapply anf_cvt_branches_subset; eassumption.
      + intros k_f decl_f body_f Hlk_f _ _. exfalso. eapply Hdis_cm. constructor.
        * exists k_f. exact Hlk_f.
        * eapply Setminus_Included. eapply Setminus_Included.
          eapply anf_cvt_exp_subset; [eassumption |].
          eapply anf_cvt_branches_subset; eassumption.

    - (* Proj *)
      intros ? ? ? ? ? ? ? ? ? IH_c ?
             v Hv S0 vn0 S0' C0 x0 Hcvt Hdis Hdis_cm Hcons Hcmap.
      injection Hv as <-.
      remember (EAst.tProj _ _) as e_p.
      destruct Hcvt; try discriminate. clear Heqe_p.
      split.
      + intros i Hnth_i. exfalso. eapply Hdis. constructor.
        * eapply nth_error_In. exact Hnth_i.
        * eapply anf_cvt_exp_subset; eassumption.
      + intros k_f decl_f body_f Hlk_f _ _. exfalso. eapply Hdis_cm. constructor.
        * exists k_f. exact Hlk_f.
        * eapply anf_cvt_exp_subset; eassumption.

    - (* Const *)
      intros k0 body0 decl0 rho0 r0 f0 t0
             Hdecl0 Hbody0 Heval_body IH_body
             v Hv S0 vn0 S0' C0 x0 Hcvt Hdis Hdis_cm Hcons Hcmap.
      subst r0.
      remember (EAst.tConst k0) as e_const.
      destruct Hcvt; try discriminate.
      rename H into Hlk0.
      injection Heqe_const as <-.
      split.
      + (* Part 1: var lookup — use cmap_consistent + eval_val_det *)
        intros i Hnth.
        edestruct Hcmap as [v_i [f' [t' [Hnth_rho Hev_body]]]];
          [exact Hnth | exact Hlk0 | exact Hdecl0 | exact Hbody0 | ].
        assert (v = v_i) by (eapply eval_val_det; eassumption).
        subst. exact Hnth_rho.
      + (* Part 2: cmap eval — direct from eval constructor *)
        intros k decl body_k Hlk Hdecl_k Hbody_k.
        assert (Heq_k := cmap_inj _ _ _ Hlk Hlk0). subst.
        unfold declared_constant in Hdecl0, Hdecl_k.
        rewrite Hdecl0 in Hdecl_k. injection Hdecl_k as <-.
        rewrite Hbody0 in Hbody_k. injection Hbody_k as <-.
        exists f0, t0. exact Heval_body.

    - (* Rel *)
      intros n rho_r v0 Hnth_rho
             v Hv S0 vn0 S0' C0 x0 Hcvt Hdis Hdis_cm Hcons Hcmap.
      injection Hv as <-.
      remember (EAst.tRel n) as e_r.
      destruct Hcvt; try discriminate.
      rename H into Hnth_src.
      injection Heqe_r as <-.
      split.
      + (* Part 1: env_consistent *)
        intros i Hnth_vn.
        unfold env_consistent in Hcons.
        rewrite (Hcons _ _ _ Hnth_vn Hnth_src). exact Hnth_rho.
      + (* Part 2: cmap_consistent *)
        intros k decl body_k Hlk Hdecl Hbody.
        edestruct Hcmap as [v_i [f' [t' [Hnth_i Hev]]]];
          [exact Hnth_src | exact Hlk | exact Hdecl | exact Hbody |].
        rewrite Hnth_rho in Hnth_i. injection Hnth_i as <-.
        exists f', t'. exact Hev.

    - (* Lam *)
      intros ? ? ?
             v Hv S0 vn0 S0' C0 x0 Hcvt Hdis Hdis_cm Hcons Hcmap.
      injection Hv as <-.
      remember (EAst.tLambda _ _) as e_lam.
      destruct Hcvt; try discriminate.
      injection Heqe_lam as <- <-.
      split.
      + intros i Hnth_i. exfalso. eapply Hdis. constructor.
        * eapply nth_error_In. exact Hnth_i.
        * eapply Setminus_Included.
          match goal with [ H : _ \in _ |- _ ] => exact H end.
      + intros k_f decl_f body_f Hlk_f _ _. exfalso. eapply Hdis_cm. constructor.
        * exists k_f. exact Hlk_f.
        * eapply Setminus_Included.
          match goal with [ H : _ \in _ |- _ ] => exact H end.

    - (* Fix *)
      intros ? ? ?
             v Hv S0 vn0 S0' C0 x0 Hcvt Hdis Hdis_cm Hcons Hcmap.
      injection Hv as <-.
      remember (EAst.tFix _ _) as e_fix.
      destruct Hcvt; try discriminate.
      injection Heqe_fix as <- <-.
      split.
      + intros i Hnth_i. exfalso. eapply Hdis. constructor.
        * eapply nth_error_In. exact Hnth_i.
        * match goal with
          | [ H : FromList _ \subset _ |- _ ] =>
            eapply H; eapply nth_error_In; eassumption
          end.
      + intros k_f decl_f body_f Hlk_f _ _. exfalso. eapply Hdis_cm. constructor.
        * exists k_f. exact Hlk_f.
        * match goal with
          | [ H : FromList _ \subset _ |- _ ] =>
            eapply H; eapply nth_error_In; eassumption
          end.

    - (* Box *)
      intros ?
             v Hv S0 vn0 S0' C0 x0 Hcvt Hdis Hdis_cm Hcons Hcmap.
      injection Hv as <-.
      remember EAst.tBox as e_box.
      destruct Hcvt; try discriminate. clear Heqe_box.
      split.
      + intros i Hnth_i. exfalso. eapply Hdis. constructor.
        * eapply nth_error_In. exact Hnth_i.
        * assumption.
      + intros k_f decl_f body_f Hlk_f _ _. exfalso. eapply Hdis_cm. constructor.
        * exists k_f. exact Hlk_f.
        * assumption.

    - (* eval_step: delegate *)
      intros rho0 e0 r0 f0 t0 Hstep IH. exact IH.
    - exact Heval.
  Unshelve. all: exact 0%nat.
  Qed.

  Lemma anf_cvt_rel_var_lookup :
    forall rho e v f t,
      src_eval rho e (fuel_sem.Val v) f t ->
      forall S vn S' C x i,
        anf_cvt_rel' S e vn S' C x ->
        Disjoint _ (FromList vn) S ->
        Disjoint _ (cmap_vars cmap) S ->
        env_consistent vn rho ->
        cmap_consistent vn rho ->
        nth_error vn i = Some x ->
        nth_error rho i = Some v.
  Proof.
    intros rho e v f t Heval S vn S' C x i Hcvt Hdis Hdis_cm Hcons Hcmap Hnth.
    exact (proj1 (anf_cvt_rel_var_lookup_and_cmap_eval
                    _ _ _ _ _ Heval v eq_refl S vn S' C x Hcvt Hdis Hdis_cm Hcons Hcmap)
                  i Hnth).
  Qed.

  Lemma anf_cvt_cmap_eval :
    forall rho e v f t,
      src_eval rho e (fuel_sem.Val v) f t ->
      forall S vn S' C x k decl body,
        anf_cvt_rel' S e vn S' C x ->
        Disjoint _ (FromList vn) S ->
        Disjoint _ (cmap_vars cmap) S ->
        env_consistent vn rho ->
        cmap_consistent vn rho ->
        lookup_const cmap k = Some x ->
        declared_constant Σ k decl ->
        decl.(EAst.cst_body) = Some body ->
        exists f' t', src_eval [] body (fuel_sem.Val v) f' t'.
  Proof.
    intros rho e v f t Heval S vn S' C x k decl body
           Hcvt Hdis Hdis_cm Hcons Hcmap Hlk Hdecl Hbody.
    exact (proj2 (anf_cvt_rel_var_lookup_and_cmap_eval
                    _ _ _ _ _ Heval v eq_refl S vn S' C x Hcvt Hdis Hdis_cm Hcons Hcmap)
                  k decl body Hlk Hdecl Hbody).
  Qed.

  (** Combined: eval preserves env_consistent when extending.
      Uses [anf_cvt_rel_var_lookup] for the lookup condition. *)
  Lemma env_consistent_extend_from_cvt vn vs S e S' C x v f t :
    env_consistent vn vs ->
    cmap_consistent vn vs ->
    anf_cvt_rel' S e vn S' C x ->
    Disjoint _ (FromList vn) S ->
    Disjoint _ (cmap_vars cmap) S ->
    src_eval vs e (fuel_sem.Val v) f t ->
    env_consistent (x :: vn) (v :: vs).
  Proof.
    intros Hc Hcm Hcvt Hdis Hdis_cm Heval.
    apply env_consistent_extend; [ exact Hc | ].
    intros k Hk.
    eapply anf_cvt_rel_var_lookup;
      [ exact Heval | exact Hcvt
      | exact Hdis | exact Hdis_cm | exact Hc | exact Hcm | exact Hk ].
  Qed.

  (** Combined: eval preserves cmap_consistent when extending.
      Uses [anf_cvt_cmap_eval] for the position-0 condition. *)
  Lemma cmap_consistent_extend_from_cvt vn vs S e S' C x v f t :
    cmap_consistent vn vs ->
    env_consistent vn vs ->
    anf_cvt_rel' S e vn S' C x ->
    Disjoint _ (FromList vn) S ->
    Disjoint _ (cmap_vars cmap) S ->
    src_eval vs e (fuel_sem.Val v) f t ->
    cmap_consistent (x :: vn) (v :: vs).
  Proof.
    intros Hcm Hc Hcvt Hdis Hdis_cm Heval.
    apply cmap_consistent_extend; [ exact Hcm | ].
    intros k decl body Hlk Hdecl Hbody.
    eapply anf_cvt_cmap_eval;
      [ exact Heval | exact Hcvt
      | exact Hdis | exact Hdis_cm | exact Hc | exact Hcm
      | exact Hlk | exact Hdecl | exact Hbody ].
  Qed.


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
      cmap_consistent vnames vs ->
      Disjoint _ (FromList vnames) S ->
      Disjoint _ (cmap_vars cmap) S ->
      anf_env_rel' vnames vs rho ->
      global_env_rel' (kn_deps e) rho ->
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
      cmap_consistent vnames vs ->
      Disjoint _ (FromList vnames) S ->
      Disjoint _ (cmap_vars cmap) S ->
      anf_env_rel' vnames vs rho ->
      global_env_rel' (kn_deps e) rho ->
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
      cmap_consistent vnames vs_env ->
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
      intros rho vnames C x S S' i Hwf Hwfe Hcons Hcmap Hdis Hdis_cmap
             Henv Hglob Hrel e_k Hdis_ek.
      inv Hrel.
      (* After inv (anf_App):
         Hcvt_e1 : anf_cvt_rel' S e1 vnames S2 C1 x1
         Hcvt_e2 : anf_cvt_rel' S2 e2 vnames S3 C2 x2
         Hr_in_S3 : r ∈ S3
         C = comp_ctx_f C1 (comp_ctx_f C2 (Eletapp_c r x1 func_tag [x2] Hole_c))
         S' = S3 \\ [set r], x = r *)
      match goal with
      | [ He1 : anf_cvt_rel _ _ _ _ _ e1 vnames _ _ _,
          He2 : anf_cvt_rel _ _ _ _ _ e2 vnames _ _ _ |- _ ] =>
        rename He1 into Hcvt_e1; rename He2 into Hcvt_e2
      end.
      rewrite <- !app_ctx_f_fuse.
      split.
      + (* Termination *)
        intros v v' Heq Hrel'. subst r0.
        (* Well-formedness of intermediate values *)
        assert (Hwf_clos : well_formed_val Σ (Clos_v rho' na0 body0)).
        { eapply eval_preserves_wf; [exact Hwf | | exact Heval1].
          rewrite (anf_env_rel_length _ _ _ Henv).
          exact (proj1 (wellformed_tApp _ _ _ Hwfe)). }
        assert (Hwf_v2 : well_formed_val Σ v2).
        { eapply eval_preserves_wf; [exact Hwf | | exact Heval2].
          rewrite (anf_env_rel_length _ _ _ Henv).
          exact (proj2 (wellformed_tApp _ _ _ Hwfe)). }
        (* Target witnesses for closure and argument *)
        destruct (@anf_val_rel_exists func_tag default_tag tgm cmap _ Σ box_dc
                    nat LambdaBox_resource_fuel LambdaBox_resource_trace
                    (Clos_v rho' na0 body0) Hwf_clos)
          as [v1' Hrel_clos].
        destruct (@anf_val_rel_exists func_tag default_tag tgm cmap _ Σ box_dc
                    nat LambdaBox_resource_fuel LambdaBox_resource_trace
                    v2 Hwf_v2)
          as [v2' Hrel_v2].
        (* Chain: post_monotonic + trans(IH1, trans(IH2, Eletapp + body)) *)
        eapply preord_exp_post_monotonic.
        2:{ eapply preord_exp_trans; [tci | exact eq_fuel_idemp | | ].
            (* IH1: evaluate e1 via C1 *)
            2:{ intros m.
                edestruct (IH1 rho vnames C1 x1 S S2 m) as [IH1_val _].
                - exact Hwf.
                - exact (proj1 (wellformed_tApp _ _ _ Hwfe)).
                - exact Hcons.
                - exact Hcmap.
                - exact Hdis.
                - exact Hdis_cmap.
                - exact Henv.
                - eapply global_env_rel_mono; [exact Hglob |].
                  intros k0 Hk0. unfold kn_deps in *. simpl.
                  apply KernameSet.union_spec. left. exact Hk0.
                - exact Hcvt_e1.
                - admit. (* Disjoint continuation for IH1: needs App-specific context disjointness *)
                - eapply IH1_val; eauto. }
            eapply preord_exp_trans with (P1 := anf_bound (f3 + 2) (t3 + 2)).
            tci. exact eq_fuel_idemp.
            (* IH2: evaluate e2 via C2 *)
            2:{ intros m.
                (* Prove Eletapp continuation disjointness before edestruct *)
                assert (Hdis_eletapp :
                  Disjoint _ (occurs_free (Eletapp x x1 func_tag [x2] e_k))
                             ((S2 \\ S3) \\ [set x2])).
                { constructor. intros z Hz. inv Hz.
                  (* H : occurs_free (...) z, H0 : (...\\...\\...) z *)
                  destruct H0. destruct H0.
                  (* Now: H0 : S2 z, H2 : ~S3 z, H1 : ~[set x2] z *)
                  (* Debug: use exact I to see if we're on track *)
                  inv H.
                  - (* Free_Eletapp1: H10 : In z [x1; x2] *)
                    simpl in H10. destruct H10 as [-> | [-> | []]].
                    + eapply (anf_cvt_result_not_in_output _ _ _ _ _ _ _ _ _ _
                                Hcvt_e1 Hdis Hdis_cmap). exact H0.
                    + apply H1. constructor.
                  - (* Free_Eletapp2: H10 : x ≠ z, H11 : occurs_free e_k z *)
                    eapply Hdis_ek. constructor; [exact H11 |].
                    constructor.
                    + constructor.
                      * eapply anf_cvt_exp_subset; [exact Hcvt_e1 | exact H0].
                      * intro Habs. destruct Habs. apply H2. assumption.
                    + intro Habs. inv Habs. exact (H10 eq_refl). }
                edestruct (IH2 (M.set x1 v1' rho) vnames C2 x2 S2 S3 m) as [IH2_val _].
                - exact Hwf.
                - exact (proj2 (wellformed_tApp _ _ _ Hwfe)).
                - exact Hcons.
                - exact Hcmap.
                - eapply Disjoint_Included_r;
                    [eapply anf_cvt_exp_subset; eassumption | exact Hdis].
                - eapply Disjoint_Included_r;
                    [eapply anf_cvt_exp_subset; eassumption | exact Hdis_cmap].
                - eapply anf_env_rel_set; [exact Henv |].
                  intros k Hk.
                  assert (Hek : nth_error rho0 k = Some (Clos_v rho' na0 body0)).
                  { change positive with var in Hk.
                    eapply anf_cvt_rel_var_lookup;
                      [exact Heval1 | exact Hcvt_e1
                      | exact Hdis | exact Hdis_cmap | exact Hcons | exact Hcmap | exact Hk]. }
                  exists (Clos_v rho' na0 body0). split; [exact Hek | exact Hrel_clos].
                - (* global_env_rel' (kn_deps e2) for M.set x1 v1' rho *)
                  assert (Hglob_e2 : global_env_rel' (kn_deps e2) rho).
                  { eapply global_env_rel_mono; [exact Hglob |].
                    intros k0 Hk0. unfold kn_deps. simpl.
                    apply KernameSet.union_spec. right. exact Hk0. }
                  eapply global_env_rel_set; [exact Hglob_e2 |].
                  intros k_g _ Hlk_g decl_g body_g Hdecl_g Hbody_g src_vg f_g t_g Heval_g.
                  (* From cmap_eval: eval [] body_g gives Clos_v rho' na0 body0 *)
                  assert (Heval_g' : exists fg tg,
                    src_eval [] body_g (fuel_sem.Val (Clos_v rho' na0 body0)) fg tg).
                  { eapply anf_cvt_cmap_eval;
                      [exact Heval1 | exact Hcvt_e1 | exact Hdis | exact Hdis_cmap
                      | exact Hcons | exact Hcmap | exact Hlk_g | exact Hdecl_g | exact Hbody_g]. }
                  destruct Heval_g' as [fg [tg Heval_g']].
                  assert (src_vg = Clos_v rho' na0 body0)
                    by (eapply eval_val_det; [exact Heval_g | exact Heval_g']).
                  subst src_vg.
                  exact Hrel_clos.
                - exact Hcvt_e2.
                - exact Hdis_eletapp.
                - eapply IH2_val; eauto. }
            (* Stage 3: Eletapp + IH3 + env bridge.
               Goal: preord_exp ?P1 eq_fuel i
                 (e_k, M.set x v' rho)
                 (Eletapp x x1 func_tag [x2] e_k, M.set x2 v2' (M.set x1 v1' rho))
               The target needs to:
               1. Look up x1 → v1' (closure), x2 → v2' (argument)
               2. Apply the closure: find_def, set_lists, step body
               3. Bind result to x, continue with e_k *)
            (* Step 1: Extract closure structure from anf_val_rel.
               After inv Hrel_clos (anf_rel_Clos):
               v1' = Vfun rho1 (Fcons f0 func_tag [x0] (C0|[Ehalt r1]|) Fnil) f0
               rho1 = target closure env
               names = captured var names
               x0 = parameter var, f0 = function name var
               C0 = body context, r1 = body result var
               H2 : anf_env_rel names rho' rho1
               H3 : env_consistent names rho'
               H12 : anf_cvt_rel' S1 body0 (x0::names) S0 C0 r1
               + disjointness/cmap hypotheses *)
            (* Save Hrel_clos before inv clears it — needed in env bridge *)
            pose proof Hrel_clos as Hrel_clos_saved.
            inv Hrel_clos.
            (* Define target defs and body env *)
            set (defs_cc := Fcons f0 func_tag [x0] (C0 |[ Ehalt r1 ]|) Fnil).
            set (rho_bc := M.set x0 v2' (def_funs defs_cc defs_cc rho1 rho1)).
            (* Apply IH3 to the closure body.
               Use step index (S i) so that after consuming 1 for Ehalt,
               the residual preord_val is at step i, matching the overall index. *)
            assert (IH3_full :
              (forall v0 v'0, fuel_sem.Val v = fuel_sem.Val v0 ->
               anf_val_rel' v0 v'0 ->
               preord_exp cenv (anf_bound f3 t3) eq_fuel (i + 1)
                 (Ehalt r1, M.set r1 v'0 rho_bc)
                 (C0 |[ Ehalt r1 ]|, rho_bc)) /\
              (fuel_sem.Val v = fuel_sem.OOT ->
               exists c, bstep_fuel cenv rho_bc (C0 |[ Ehalt r1 ]|) c eval.OOT tt)).
            { eapply (IH3 rho_bc (x0 :: names) C0 r1 S1 S0 (i + 1)).
              - (* well_formed_env (v2 :: rho') *)
                constructor; [exact Hwf_v2 |].
                inv Hwf_clos. assumption.
              - (* wellformed body0: Wf_Clos gives wellformed (S (length rho')) body0,
                   and length rho' = length names from anf_env_rel *)
                inv Hwf_clos.
                simpl. rewrite <- (anf_env_rel_length _ _ _ H2). assumption.
              - (* env_consistent (x0::names) (v2::rho') *)
                apply env_consistent_extend_fresh; [exact H3 |].
                intro Hc. apply H9. right. exact Hc.
              - (* cmap_consistent (x0::names) (v2::rho') *)
                apply cmap_consistent_extend; [admit (* cmap_consistent names rho' *) |].
                (* x0 is NOT a cmap variable (H6), so the condition is vacuous *)
                intros k_c decl_c body_c Hlk_c Hdecl_c Hbody_c.
                exfalso. apply H6. exists k_c. exact Hlk_c.
              - (* Disjoint (FromList (x0::names)) S1 *)
                rewrite FromList_cons. eapply Union_Disjoint_l.
                + eapply Disjoint_Singleton_l.
                  eapply Disjoint_In_l. exact H4. left. constructor.
                + eapply Disjoint_Included_l; [| exact H4].
                  intros z Hz. right. right. exact Hz.
              - exact H5. (* Disjoint (cmap_vars cmap) S1 *)
              - (* anf_env_rel (x0::names) (v2::rho') rho_bc *)
                unfold rho_bc. constructor.
                + (* x0 → v2' *)
                  exists v2'. split; [rewrite M.gss; reflexivity | exact Hrel_v2].
                + (* names → rho' via rho1, weakened through def_funs and M.set x0 *)
                  eapply anf_env_rel_weaken; [| intro Hc; apply H9; right; exact Hc].
                  eapply anf_env_rel_weaken; [exact H2 | exact H10].
              - (* global_env_rel' (kn_deps body0) rho_bc.
                   H13 gives it for rho1; weaken through def_funs (f0) and M.set x0. *)
                unfold rho_bc.
                eapply global_env_rel_set_fresh; [| exact H6].
                eapply global_env_rel_set_fresh; [| exact H7].
                exact H13.
              - exact H12. (* anf_cvt_rel' S1 body0 (x0::names) S0 C0 r1 *)
              - (* Disjoint for Ehalt r1 *)
                constructor. intros z Hz. inv Hz.
                inv H. destruct H0. apply H0. constructor.
            }
            destruct IH3_full as [IH3_val _].
            specialize (IH3_val v v' eq_refl Hrel').
            (* Step 2: Extract body bstep from IH3 via Ehalt witness *)
            (* Ehalt r1 in (M.set r1 v' rho_bc) steps in 1 fuel to (Res v') *)
            assert (Hehalt : bstep_fuel cenv (M.set r1 v' rho_bc)
                               (Ehalt r1) (<0> <+> <1> (Ehalt r1)) (eval.Res v') (<0> <+> <1> (Ehalt r1))).
            { apply BStepf_run. apply BStept_halt. rewrite M.gss. reflexivity. }
            (* Introduce source reduction.
               Do NOT destruct v_ek into OOT/Res — handle uniformly.
               The body bstep from IH3 and env bridge both work for any v_ek. *)
            intros v_ek cin_ek cout_ek Hle_ek Hbstep_ek.
            (* Extract body bstep from IH3 *)
            assert (H1_le_Si : to_nat (<0> <+> <1> (Ehalt r1)) <= i + 1).
            { unfold_all. simpl. lia. }
            destruct (IH3_val (eval.Res v') (<0> <+> <1> (Ehalt r1)) (<0> <+> <1> (Ehalt r1))
                        H1_le_Si Hehalt)
              as [v_bc [cin_bc [cout_bc [Hbstep_bc [Hpost_bc Hres_bc]]]]].
            destruct v_bc as [| v_bc_val].
            { exfalso. exact Hres_bc. }
            (* Hbstep_bc : bstep_fuel rho_bc (C0|[Ehalt r1]|) cin_bc (Res v_bc_val) cout_bc
               Hres_bc : preord_val cenv eq_fuel i v' v_bc_val *)
            set (rho_app := M.set x2 v2' (M.set x1 (Vfun rho1 defs_cc f0) rho)).
            (* Case split on x1 =? x2 BEFORE env bridge *)
            destruct (Pos.eq_dec x1 x2) as [Heq_x1x2 | Hneq_x1x2].
            { (* x1 = x2: argument shadows closure.
                 In rho_app, M.get x1 gives v2' (arg), NOT the closure.
                 Need to show v2' is also a valid Vfun via preord_val_trans. *)
              subst x2.
              (* Step 1: x1 ∈ FromList vnames (not in S, since result of e2 from S2) *)
              assert (Hx1_in_vn : x1 \in FromList vnames).
              { destruct (anf_cvt_result_in_consumed _ _ _ _ _ _ Hcvt_e2)
                  as [Hin | [Hin | Hin]].
                - exact Hin.
                - exfalso. eapply anf_cvt_result_not_in_output.
                  exact Hcvt_e1. exact Hdis. exact Hdis_cmap. exact Hin.
                - (* x1 ∈ cmap_vars: get FromList from e1's result *)
                  destruct (anf_cvt_result_in_consumed _ _ _ _ _ _ Hcvt_e1)
                    as [Hin1 | [Hin1 | Hin1]].
                  + exact Hin1.
                  + exfalso. destruct Hdis_cmap as [Hdc].
                    apply (Hdc x1). constructor; [exact Hin | exact Hin1].
                  + (* Both e1 and e2 give x1 ∈ cmap_vars only.
                       Need x1 ∈ FromList vnames — requires cmap vars
                       to have been bound in the name list.
                       This should follow from global_env_rel' + anf_env_rel
                       but needs a helper lemma. *)
                    admit.
              }
              (* Step 2: get original target value at x1 from anf_env_rel *)
              assert (Hx1_list : List.In x1 vnames) by exact Hx1_in_vn.
              apply In_nth_error in Hx1_list. destruct Hx1_list as [k0 Hk0].
              destruct (Forall2_nth_error_r _ _ _ _ _ Henv Hk0)
                as [v_src_k [Hk0_src [v_rho [Hget_rho Hrel_rho]]]].
              (* Establish v_src_k = Clos_v rho' na0 body0 before splitting *)
              assert (Heval1_k : nth_error rho0 k0 = Some (Clos_v rho' na0 body0)).
              { eapply anf_cvt_rel_var_lookup;
                  [exact Heval1 | exact Hcvt_e1 | exact Hdis | exact Hdis_cmap
                  | exact Hcons | exact Hcmap | exact Hk0]. }
              assert (Heq_src : v_src_k = Clos_v rho' na0 body0) by congruence.
              subst v_src_k.
              (* Also: v2 = Clos_v rho' na0 body0 (same position, same env) *)
              assert (Heval2_k : nth_error rho0 k0 = Some v2).
              { eapply anf_cvt_rel_var_lookup;
                  [exact Heval2 | exact Hcvt_e2
                  | eapply Disjoint_Included_r;
                      [eapply anf_cvt_exp_subset; exact Hcvt_e1 | exact Hdis]
                  | eapply Disjoint_Included_r;
                      [eapply anf_cvt_exp_subset; exact Hcvt_e1 | exact Hdis_cmap]
                  | exact Hcons | exact Hcmap | exact Hk0]. }
              assert (Heq_v2 : Clos_v rho' na0 body0 = v2) by congruence.
              (* Now Hrel_rho : anf_val_rel (Clos_v rho' na0 body0) v_rho *)
              (* Step 3: preord_val (Vfun rho1 defs_cc f0) v2' via alpha-equiv + trans *)
              assert (Hpv_cv : forall j, preord_val cenv eq_fuel j
                        (Vfun rho1 defs_cc f0) v2').
              { intro j. eapply preord_val_trans; [tci | exact eq_fuel_idemp | | ].
                - eapply (@anf_cvt_val_alpha_equiv
                    _ _ _ _ eq_fuel eq_fuel tgm cmap cenv
                    eq_fuel_compat (fun _ _ H => H)
                    nat LambdaBox_resource_fuel LambdaBox_resource_trace
                    Σ box_dc Hglob_term func_tag default_tag).
                  exact Hrel_clos_saved.
                  exact Hrel_rho.
                - intros m0.
                  eapply (@anf_cvt_val_alpha_equiv
                    _ _ _ _ eq_fuel eq_fuel tgm cmap cenv
                    eq_fuel_compat (fun _ _ H => H)
                    nat LambdaBox_resource_fuel LambdaBox_resource_trace
                    Σ box_dc Hglob_term func_tag default_tag).
                  rewrite Heq_v2 in Hrel_rho. exact Hrel_rho.
                  exact Hrel_v2. }
              (* Step 4: extract Vfun structure of v2' from preord_val *)
              assert (Hpv_inst := Hpv_cv (cin_bc + i + 1)%nat).
              rewrite preord_val_eq in Hpv_inst.
              destruct v2' as [ | rho2_fc B2 f2_v | | ];
                try (simpl in Hpv_inst; contradiction).
              (* v2' = Vfun rho2_fc B2 f2_v *)
              (* Step 5: get body correspondence *)
              assert (Hfind_cc : find_def f0 defs_cc =
                Some (func_tag, [x0], C0 |[ Ehalt r1 ]|)).
              { unfold defs_cc. simpl.
                destruct (M.elt_eq f0 f0); [ reflexivity | congruence ]. }
              assert (Hset_cc : Some rho_bc = set_lists [x0]
                [Vfun rho2_fc B2 f2_v] (def_funs defs_cc defs_cc rho1 rho1)).
              { unfold rho_bc. reflexivity. }
              edestruct Hpv_inst as (xs2_pc & e2_body & rho2_body &
                Hfind_v2 & Hset_v2 & Hbody_preord).
              { reflexivity. }
              { exact Hfind_cc. }
              { exact Hset_cc. }
              (* Step 6: transfer body evaluation via preord_exp' *)
              assert (Hbody_pe : preord_exp' cenv (preord_val cenv) eq_fuel eq_fuel
                        (cin_bc + i)%nat
                        (C0 |[ Ehalt r1 ]|, rho_bc) (e2_body, rho2_body)).
              { apply Hbody_preord. lia.
                constructor; [ | constructor ].
                eapply preord_val_refl. tci. }
              destruct (Hbody_pe (eval.Res v_bc_val) cin_bc cout_bc) as
                (v2_body_res & cin2_bc & cout2_bc & Hbstep2_bc & Hpost2_bc & Hres2_bc).
              { simpl. lia. }
              { exact Hbstep_bc. }
              destruct v2_body_res as [ | v2_bc ].
              { simpl in Hres2_bc. contradiction. }
              simpl in Hres2_bc.
              (* Step 7: forall m', preord_val m' v_bc_val v2_bc
                 using Hpv_cv at varying indices + bstep determinism *)
              assert (Hpv_all : forall m', preord_val cenv eq_fuel m' v_bc_val v2_bc).
              { intro m'.
                pose proof (Hpv_cv (cin_bc + m' + 1)%nat) as Hpv_m.
                rewrite preord_val_eq in Hpv_m.
                edestruct Hpv_m as (xs2_m & e2_m & rho2_m &
                  Hfind_m & Hset_m & Hbp_m).
                { reflexivity. }
                { exact Hfind_cc. }
                { exact Hset_cc. }
                replace e2_m with e2_body in * by congruence.
                replace xs2_m with xs2_pc in * by congruence.
                replace rho2_m with rho2_body in *.
                2:{ congruence. }
                assert (Hba_m : preord_exp' cenv (preord_val cenv) eq_fuel eq_fuel
                          (cin_bc + m')%nat
                          (C0 |[ Ehalt r1 ]|, rho_bc) (e2_body, rho2_body)).
                { apply Hbp_m. lia.
                  constructor; [ | constructor ].
                  eapply preord_val_refl. tci. }
                destruct (Hba_m (eval.Res v_bc_val) cin_bc cout_bc) as
                  (v2_m & cin2_m & cout2_m & Hbs2_m & _ & Hres2_m).
                { simpl. lia. }
                { exact Hbstep_bc. }
                destruct v2_m as [ | v2_m_val ].
                { simpl in Hres2_m. contradiction. }
                simpl in Hres2_m.
                eapply bstep_fuel_deterministic in Hbs2_m.
                2:{ exact Hbstep2_bc. }
                destruct Hbs2_m as [Hv_eq [_ _]]. subst v2_m_val.
                replace (cin_bc + m' - cin_bc)%nat with m' in Hres2_m by lia.
                exact Hres2_m. }
              (* Step 8: preord_val i v' v2_bc via transitivity *)
              assert (Hpv_direct : preord_val cenv eq_fuel i v' v2_bc).
              { eapply preord_val_trans; [tci | exact eq_fuel_idemp | | ].
                - eapply preord_val_monotonic. exact Hres_bc. unfold_all. simpl. lia.
                - exact Hpv_all. }
              (* Step 9: continuation env bridge *)
              assert (Hx_neq_x1 : x <> x1).
              { intro Heq. subst x.
                destruct Hdis as [Hdis']. apply (Hdis' x1).
                constructor.
                - exact Hx1_in_vn.
                - eapply anf_cvt_exp_subset. exact Hcvt_e1.
                  eapply anf_cvt_exp_subset. exact Hcvt_e2.
                  match goal with Hr : x1 \in S3 |- _ => exact Hr end. }
              assert (Hrefl : preord_exp cenv eq_fuel eq_fuel i
                        (e_k, M.set x v' rho)
                        (e_k, M.set x v2_bc
                          (M.set x1 (Vfun rho2_fc B2 f2_v)
                            (M.set x1 (Vfun rho1 defs_cc f0) rho)))).
              { eapply preord_exp_refl. now eapply eq_fuel_compat.
                intros y Hy.
                destruct (Pos.eq_dec y x) as [-> | Hneq_x].
                - intros v0 Hget0. rewrite M.gss in Hget0. inv Hget0.
                  eexists. split. rewrite M.gss. reflexivity. exact Hpv_direct.
                - intros v0 Hget0. rewrite M.gso in Hget0; [| exact Hneq_x].
                  destruct (Pos.eq_dec y x1) as [-> | Hneq_x1].
                  + (* y = x1 *)
                    eexists. split.
                    { rewrite M.gso; [| exact Hneq_x]. rewrite M.gss. reflexivity. }
                    eapply (@anf_cvt_val_alpha_equiv
                      _ _ _ _ eq_fuel eq_fuel tgm cmap cenv
                      eq_fuel_compat (fun _ _ H => H)
                      nat LambdaBox_resource_fuel LambdaBox_resource_trace
                      Σ box_dc Hglob_term func_tag default_tag).
                    * assert (Heval2_k' : nth_error rho0 k0 = Some v2).
                      { eapply anf_cvt_rel_var_lookup;
                          [exact Heval2 | exact Hcvt_e2
                          | eapply Disjoint_Included_r;
                              [eapply anf_cvt_exp_subset; exact Hcvt_e1 | exact Hdis]
                          | eapply Disjoint_Included_r;
                              [eapply anf_cvt_exp_subset; exact Hcvt_e1 | exact Hdis_cmap]
                          | exact Hcons | exact Hcmap | exact Hk0]. }
                      assert (v0 = v_rho) by congruence. subst v0.
                      rewrite Heq_v2 in Hrel_rho. exact Hrel_rho.
                    * exact Hrel_v2.
                  + (* y ≠ x, y ≠ x1 *)
                    eexists. split.
                    { rewrite M.gso; [| exact Hneq_x].
                      rewrite M.gso; [| exact Hneq_x1].
                      rewrite M.gso; [exact Hget0 | exact Hneq_x1]. }
                    eapply preord_val_refl. tci. }
              (* Step 10: extract continuation and construct BStept_letapp *)
              edestruct Hrefl as (v_cont & cin_cont & cout_cont &
                Hbstep_cont & Heq_cont & Hres_cont).
              { exact Hle_ek. }
              { exact Hbstep_ek. }
              do 3 eexists. split.
              { econstructor 2. eapply BStept_letapp.
                - (* M.get x1 rho_app: x1=x2, so M.gss gives v2' = Vfun rho2_fc B2 f2_v *)
                  unfold rho_app. rewrite M.gss. reflexivity.
                - simpl. unfold rho_app. rewrite M.gss. reflexivity.
                - exact Hfind_v2.
                - symmetry. exact Hset_v2.
                - exact Hbstep2_bc.
                - exact Hbstep_cont. }
              split.
              { unfold anf_bound in Hpost_bc, Hpost2_bc |- *.
                unfold eq_fuel in Heq_cont, Hpost2_bc. simpl in Heq_cont, Hpost_bc, Hpost2_bc.
                destruct Hpost_bc as [Hlb_bc Hub_bc].
                destruct Hpost2_bc as [Hlb2_bc Hub2_bc].
                unfold_all. simpl in *. split; lia. }
              { exact Hres_cont. } }
            (* x1 ≠ x2: standard case *)
            (* Env bridge: M.set x v' rho ≈ M.set x v_bc_val rho_app
               on occurs_free e_k. For y=x use preord_val from Hres_bc.
               For y=x1/x2, case split on FromList vnames vs S vs cmap_vars. *)
            assert (Hrefl : preord_exp cenv eq_fuel eq_fuel i
              (e_k, M.set x v' rho)
              (e_k, M.set x v_bc_val rho_app)).
            { eapply preord_exp_refl. exact eq_fuel_compat.
              intros y Hy.
              destruct (Pos.eq_dec y x) as [-> | Hneq_x].
              - (* y = x *)
                intros w Hget. rewrite M.gss in Hget. inv Hget.
                eexists. split. rewrite M.gss. reflexivity.
                eapply preord_val_monotonic. exact Hres_bc. unfold_all. simpl. lia.
              - (* y ≠ x *)
                intros w Hget. rewrite M.gso in Hget; [| exact Hneq_x].
                destruct (Pos.eq_dec y x2) as [-> | Hneq_x2].
                + (* y = x2 *)
                  destruct (anf_cvt_result_in_consumed _ _ _ _ _ _ Hcvt_e2)
                    as [Hin_vn | [Hin_S2 | Hin_cm]].
                  * (* x2 ∈ FromList vnames: use alpha-equiv *)
                    eexists. split.
                    { unfold rho_app. rewrite M.gso; [rewrite M.gss; reflexivity | exact Hneq_x]. }
                    assert (Hin_list : List.In x2 vnames) by exact Hin_vn.
                    apply In_nth_error in Hin_list. destruct Hin_list as [k0 Hk0].
                    assert (Heval2_k : nth_error rho0 k0 = Some v2).
                    { eapply anf_cvt_rel_var_lookup; [exact Heval2 | exact Hcvt_e2 | | | | | exact Hk0].
                      - eapply Disjoint_Included_r;
                          [eapply anf_cvt_exp_subset; exact Hcvt_e1 | exact Hdis].
                      - eapply Disjoint_Included_r;
                          [eapply anf_cvt_exp_subset; exact Hcvt_e1 | exact Hdis_cmap].
                      - exact Hcons.
                      - exact Hcmap. }
                    destruct (Forall2_nth_error_r _ _ _ _ _ Henv Hk0)
                      as [v_src [Hk0_src Hrel_k0]].
                    destruct Hrel_k0 as [w_k0 [Hget_k0 Hrel_k0]].
                    assert (v_src = v2) by (rewrite Heval2_k in Hk0_src; congruence).
                    subst v_src.
                    assert (w_k0 = w) by congruence. subst w_k0.
                    eapply (@anf_cvt_val_alpha_equiv
                              _ _ _ _ eq_fuel eq_fuel tgm cmap cenv
                              eq_fuel_compat (fun _ _ H => H)
                              nat LambdaBox_resource_fuel LambdaBox_resource_trace
                              Σ box_dc Hglob_term func_tag default_tag);
                      [exact Hrel_k0 | exact Hrel_v2].
                  * (* x2 ∈ S2: contradiction via Hdis_ek *)
                    exfalso.
                    assert (Hx2_not_S3 : ~ x2 \in S3).
                    { eapply anf_cvt_result_not_in_output; [exact Hcvt_e2 | |].
                      - eapply Disjoint_Included_r;
                          [eapply anf_cvt_exp_subset; exact Hcvt_e1 | exact Hdis].
                      - eapply Disjoint_Included_r;
                          [eapply anf_cvt_exp_subset; exact Hcvt_e1 | exact Hdis_cmap]. }
                    match goal with Hr : x \in S3 |- _ =>
                      assert (Hx2_ne_x : x2 <> x) by (intro; subst; exact (Hx2_not_S3 Hr)) end.
                    destruct Hdis_ek as [Hdis_ek'].
                    apply (Hdis_ek' x2). constructor; [exact Hy |].
                    constructor.
                    -- constructor.
                       ++ eapply anf_cvt_exp_subset. exact Hcvt_e1. exact Hin_S2.
                       ++ intro Habs. destruct Habs. exact (Hx2_not_S3 H).
                    -- intro Habs. inv Habs. exact (Hx2_ne_x eq_refl).
                  * (* x2 ∈ cmap_vars: use alpha-equiv via global_env_rel' *)
                    eexists. split.
                    { unfold rho_app. rewrite M.gso; [rewrite M.gss; reflexivity | exact Hneq_x]. }
                    destruct Hin_cm as [k_c Hlk_c].
                    assert (Hkc_deps : kn_deps (EAst.tApp e1 e2) k_c) by admit.
                    destruct (Hglob k_c x2 Hkc_deps Hlk_c)
                      as (decl_c & body_c & anf_vc & Hdecl_c & Hbody_c & Hget_c & Hrel_c).
                    assert (anf_vc = w) by congruence. subst anf_vc.
                    assert (Heval2_body : exists f_c t_c,
                      src_eval [] body_c (fuel_sem.Val v2) f_c t_c).
                    { eapply anf_cvt_cmap_eval;
                        [exact Heval2 | exact Hcvt_e2 | | | | | exact Hlk_c | exact Hdecl_c | exact Hbody_c].
                      - eapply Disjoint_Included_r;
                          [eapply anf_cvt_exp_subset; exact Hcvt_e1 | exact Hdis].
                      - eapply Disjoint_Included_r;
                          [eapply anf_cvt_exp_subset; exact Hcvt_e1 | exact Hdis_cmap].
                      - exact Hcons.
                      - exact Hcmap. }
                    destruct Heval2_body as [f_c [t_c Heval2_c]].
                    eapply (@anf_cvt_val_alpha_equiv
                              _ _ _ _ eq_fuel eq_fuel tgm cmap cenv
                              eq_fuel_compat (fun _ _ H => H)
                              nat LambdaBox_resource_fuel LambdaBox_resource_trace
                              Σ box_dc Hglob_term func_tag default_tag);
                      [exact (Hrel_c v2 f_c t_c Heval2_c) | exact Hrel_v2].
                + destruct (Pos.eq_dec y x1) as [-> | Hneq_x1].
                  * (* y = x1 *)
                    destruct (anf_cvt_result_in_consumed _ _ _ _ _ _ Hcvt_e1)
                      as [Hin_vn1 | [Hin_S1 | Hin_cm1]].
                    -- (* x1 ∈ FromList vnames: use alpha-equiv *)
                       eexists. split.
                       { unfold rho_app. rewrite M.gso; [| exact Hneq_x].
                         rewrite M.gso; [rewrite M.gss; reflexivity | exact Hneq_x1x2]. }
                       assert (Hin_list1 : List.In x1 vnames) by exact Hin_vn1.
                       apply In_nth_error in Hin_list1. destruct Hin_list1 as [k1 Hk1].
                       assert (Heval1_k : nth_error rho0 k1 = Some (Clos_v rho' na0 body0)).
                       { eapply anf_cvt_rel_var_lookup;
                           [exact Heval1 | exact Hcvt_e1 | exact Hdis | exact Hdis_cmap
                           | exact Hcons | exact Hcmap | exact Hk1]. }
                       destruct (Forall2_nth_error_r _ _ _ _ _ Henv Hk1)
                         as [v_src1 [Hk1_src Hrel_k1]].
                       destruct Hrel_k1 as [w_k1 [Hget_k1 Hrel_k1]].
                       assert (v_src1 = Clos_v rho' na0 body0) by congruence. subst v_src1.
                       assert (w_k1 = w) by congruence. subst w_k1.
                       eapply (@anf_cvt_val_alpha_equiv
                                 _ _ _ _ eq_fuel eq_fuel tgm cmap cenv
                                 eq_fuel_compat (fun _ _ H => H)
                                 nat LambdaBox_resource_fuel LambdaBox_resource_trace
                                 Σ box_dc Hglob_term func_tag default_tag);
                         [exact Hrel_k1 | exact Hrel_clos_saved].
                    -- (* x1 ∈ S: contradiction via Hdis_ek *)
                       exfalso.
                       assert (Hx1_not_S2 : ~ x1 \in S2).
                       { eapply anf_cvt_result_not_in_output; eassumption. }
                       assert (Hx1_not_S3 : ~ x1 \in S3).
                       { intro Hin. apply Hx1_not_S2.
                         eapply anf_cvt_exp_subset. exact Hcvt_e2. exact Hin. }
                       match goal with Hr : x \in S3 |- _ =>
                         assert (Hx1_ne_x : x1 <> x)
                           by (intro; subst; exact (Hx1_not_S3 Hr)) end.
                       destruct Hdis_ek as [Hdis_ek'].
                       apply (Hdis_ek' x1). constructor; [exact Hy |].
                       constructor.
                       ++ constructor; [exact Hin_S1 |].
                          intro Habs. destruct Habs. exact (Hx1_not_S3 H).
                       ++ intro Habs. inv Habs. exact (Hx1_ne_x eq_refl).
                    -- (* x1 ∈ cmap_vars: use alpha-equiv via global_env_rel' *)
                       eexists. split.
                       { unfold rho_app. rewrite M.gso; [| exact Hneq_x].
                         rewrite M.gso; [rewrite M.gss; reflexivity | exact Hneq_x1x2]. }
                       destruct Hin_cm1 as [k_c1 Hlk_c1].
                       assert (Hkc1_deps : kn_deps (EAst.tApp e1 e2) k_c1) by admit.
                       destruct (Hglob k_c1 x1 Hkc1_deps Hlk_c1)
                         as (decl_c1 & body_c1 & anf_vc1 & Hdecl_c1 & Hbody_c1 & Hget_c1 & Hrel_c1).
                       assert (anf_vc1 = w) by congruence. subst anf_vc1.
                       assert (Heval1_body : exists f_c1 t_c1,
                         src_eval [] body_c1 (fuel_sem.Val (Clos_v rho' na0 body0)) f_c1 t_c1).
                       { eapply anf_cvt_cmap_eval;
                           [exact Heval1 | exact Hcvt_e1 | exact Hdis | exact Hdis_cmap
                           | exact Hcons | exact Hcmap | exact Hlk_c1 | exact Hdecl_c1 | exact Hbody_c1]. }
                       destruct Heval1_body as [f_c1 [t_c1 Heval1_c1]].
                       eapply (@anf_cvt_val_alpha_equiv
                                 _ _ _ _ eq_fuel eq_fuel tgm cmap cenv
                                 eq_fuel_compat (fun _ _ H => H)
                                 nat LambdaBox_resource_fuel LambdaBox_resource_trace
                                 Σ box_dc Hglob_term func_tag default_tag);
                         [exact (Hrel_c1 (Clos_v rho' na0 body0) f_c1 t_c1 Heval1_c1) | exact Hrel_clos_saved].
                  * (* y ≠ x, ≠ x1, ≠ x2 *)
                    eexists. split.
                    { unfold rho_app. rewrite M.gso; [| exact Hneq_x].
                      rewrite M.gso; [| exact Hneq_x2].
                      rewrite M.gso; [exact Hget | exact Hneq_x1]. }
                    eapply preord_val_refl. tci. }
            (* Extract continuation bstep from bridge *)
            edestruct Hrefl as (v_cont & cin_cont & cout_cont &
              Hbstep_cont & Hpost_cont & Hres_cont).
            { exact Hle_ek. }
            { exact Hbstep_ek. }
            (* Construct BStept_letapp *)
            do 3 eexists. split.
            { econstructor 2. eapply BStept_letapp.
              - (* M.get x1 rho_app *)
                unfold rho_app. rewrite M.gso; [rewrite M.gss; reflexivity | exact Hneq_x1x2].
              - (* get_list [x2] rho_app *)
                simpl. unfold rho_app. rewrite M.gss. reflexivity.
              - (* find_def f0 defs_cc *)
                unfold defs_cc. simpl.
                destruct (M.elt_eq f0 f0); [reflexivity | contradiction].
              - (* set_lists *)
                simpl. reflexivity.
              - (* body bstep *)
                exact Hbstep_bc.
              - (* continuation bstep *)
                exact Hbstep_cont. }
            split.
            { (* Post: fuel bounds *)
              unfold anf_bound in Hpost_bc |- *.
              unfold eq_fuel in Hpost_cont. simpl in Hpost_cont, Hpost_bc.
              destruct Hpost_bc as [Hlb_bc Hub_bc].
              unfold_all. simpl in *. split; lia. }
            { exact Hres_cont. }
        }
        (* inclusion: comp (comp (anf_bound (f3+2) (t3+2)) (anf_bound f2 t2)) (anf_bound f1 t1)
           ⊆ anf_bound (f1+f2+f3+1) (t1+t2+t3+2) *)
        { unfold inclusion, comp, eq_fuel, anf_bound.
          intros [[[? ?] ?] ?] [[[? ?] ?] ?].
          intros [[[[? ?] ?] ?] [[[[[? ?] ?] ?] [[? ?] [? ?]]] [? ?]]].
          unfold_all. simpl in *. split; lia. }
      + (* Divergence *)
        intros _. exists 0. eapply bstep_fuel_zero_OOT.

    (* eval_App_step_OOT1 *)
    - intros e1 e2 rho0 f1 t1 Heval1 IH1.
      unfold anf_cvt_correct_exp_step.
      intros rho vnames C x S S' i Hwf Hwfe Hcons Hcmap Hdis Hdis_cmap Henv Hglob Hrel e_k Hdis_ek.
      split; [intros; congruence |
              intros _; exists 0; eapply bstep_fuel_zero_OOT].

    (* eval_App_step_OOT2 *)
    - intros e1 e2 v rho0 f1 f2 t1 t2 Heval1 IH1 Heval2 IH2.
      unfold anf_cvt_correct_exp_step.
      intros rho vnames C x S S' i Hwf Hwfe Hcons Hcmap Hdis Hdis_cmap Henv Hglob Hrel e_k Hdis_ek.
      split; [intros; congruence |
              intros _; exists 0; eapply bstep_fuel_zero_OOT].

    (* eval_FixApp_step *)
    - intros e1 e2 body0 rho0 rho' rho'' idx0 na0 mfix0 v2 r0
             f1 f2 f3 t1 t2 t3
             Heval1 IH1 Hbody Hrec Heval2 IH2 Heval3 IH3.
      unfold anf_cvt_correct_exp_step.
      intros rho vnames C x S S' i Hwf Hwfe Hcons Hcmap Hdis Hdis_cmap
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
      intros rho vnames C x S S' i Hwf Hwfe Hcons Hcmap Hdis Hdis_cmap
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
                - exact Hcmap.
                - exact Hdis.
                - exact Hdis_cmap.
                - exact Henv.
                - eapply global_env_rel_mono; [exact Hglob |].
                  intros k0 Hk0. unfold kn_deps. simpl.
                  apply KernameSet.union_spec. left. exact Hk0.
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
                - eapply env_consistent_extend_from_cvt; eassumption.
                - eapply cmap_consistent_extend_from_cvt; eassumption.
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
                    (* vnames[k] = x1. By anf_cvt_rel_var_lookup, rho0[k] = v1 *)
                    assert (Hek : nth_error rho0 k = Some v1).
                    { change positive with var in Hk.
                      eapply anf_cvt_rel_var_lookup;
                        [exact Heval1 | exact Hcvt_b
                        | exact Hdis | exact Hdis_cmap | exact Hcons | exact Hcmap | exact Hk]. }
                    exists v1. split; [exact Hek | exact Hrel1].
                - (* global_env_rel' for M.set x1 v1' rho *)
                  unfold global_env_rel' in *. intros kn vn0 Hd Hl.
                  assert (Hd' : kn_deps (EAst.tLetIn na0 b0 t0) kn).
                  { unfold kn_deps. simpl. apply KernameSet.union_spec. right. exact Hd. }
                  destruct (Hglob kn vn0 Hd' Hl) as [d1 [b1 [av [Hd1 [Hd2 [Hgv Hd3]]]]]].
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
                     (* rho0[k] = v1 by anf_cvt_rel_var_lookup *)
                     assert (Hek : nth_error rho0 k = Some v1).
                     { change positive with var in Hk.
                       eapply anf_cvt_rel_var_lookup;
                         [exact Heval1 | exact Hcvt_b
                         | exact Hdis | exact Hdis_cmap | exact Hcons | exact Hcmap | exact Hk]. }
                     rewrite Hek in Hnth_k. injection Hnth_k as <-.
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
                     assert (Hknx_deps : kn_deps (EAst.tLetIn na0 b0 t0) kn_x) by admit.
                     destruct (Hglob kn_x x1 Hknx_deps Hlk_x)
                       as [dx [bx [avx [Hdx [Hbx [Hgx Hrx]]]]]].
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
      intros rho vnames C x S S' i Hwf Hwfe Hcons Hcmap Hdis Hdis_cmap Henv Hglob Hrel e_k Hdis_ek.
      split; [intros; congruence |
              intros _; exists 0; eapply bstep_fuel_zero_OOT].

    (* eval_Construct_step *)
    - intros ind c args vs0 rho0 dc fs ts
             Hdc Heval_args IH_args.
      unfold anf_cvt_correct_exp_step.
      intros rho vnames C x S S' i Hwf Hwfe Hcons Hcmap Hdis Hdis_cmap
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
      intros rho vnames C x S S' i Hwf Hwfe Hcons Hcmap Hdis Hdis_cmap Henv Hglob Hrel e_k Hdis_ek.
      split; [intros; congruence |
              intros _; exists 0; eapply bstep_fuel_zero_OOT].

    (* eval_Case_step *)
    - intros ind npars mch brs rho0 dc vs0 body0 c0 r0
             f1 f2 t1 t2
             Heval_mch IH_mch Hdc Hbranch Heval_body IH_body.
      unfold anf_cvt_correct_exp_step.
      intros rho vnames C x S S' i Hwf Hwfe Hcons Hcmap Hdis Hdis_cmap
             Henv Hglob Hrel e_k Hdis_ek.
      inv Hrel.
      split.
      + intros v v' Heq Hrel'. subst r0.
        admit. (* Case termination: IH chaining *)
      + intros _. exists 0. eapply bstep_fuel_zero_OOT.

    (* eval_Case_step_OOT *)
    - intros ind npars mch brs rho0 f1 t1 Heval1 IH1.
      unfold anf_cvt_correct_exp_step.
      intros rho vnames C x S S' i Hwf Hwfe Hcons Hcmap Hdis Hdis_cmap Henv Hglob Hrel e_k Hdis_ek.
      split; [intros; congruence |
              intros _; exists 0; eapply bstep_fuel_zero_OOT].

    (* eval_Proj_step *)
    - intros p0 c0 rho0 dc vs0 v0 f1 t1
             Heval_c IH_c Hnth_proj.
      unfold anf_cvt_correct_exp_step.
      intros rho vnames C x S S' i Hwf Hwfe Hcons Hcmap Hdis Hdis_cmap
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
      intros rho vnames C x S S' i Hwf Hwfe Hcons Hcmap Hdis Hdis_cmap Henv Hglob Hrel e_k Hdis_ek.
      split; [intros; congruence |
              intros _; exists 0; eapply bstep_fuel_zero_OOT].

    (* eval_Const_step *)
    - intros k0 body0 decl0 rho0 r0 f0 t0
             Hdecl Hbody Heval_body IH_body.
      unfold anf_cvt_correct_exp_step.
      intros rho vnames C x S S' i Hwf Hwfe Hcons Hcmap Hdis Hdis_cmap
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
      intros rho vnames C xs S S' i Hwf Hwfe Hcons Hcmap Hdis Hdis_cmap
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
      intros rho vnames C xs S S' i Hwf Hwfe Hcons Hcmap Hdis Hdis_cmap
             Henv Hglob Hrel e_k vs' Hvs' Hdis_ek.
      inv Hrel. inv Hvs'.
      admit. (* Cons case: IH chaining *)

    (* ================================================================ *)
    (* P1 cases: eval_env_fuel (6 cases)                                *)
    (* ================================================================ *)

    (* eval_Rel_fuel *)
    - intros n rho0 v Hnth.
      unfold anf_cvt_correct_exp.
      intros rho vnames C x S S' i Hwf Hwfe Hcons Hcmap Hdis Hdis_cmap Henv Hglob Hrel e_k Hdis_ek.
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
      intros rho vnames C x S S' i Hwf Hwfe Hcons Hcmap Hdis Hdis_cmap Henv Hglob Hrel e_k Hdis_ek.
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
                (* global_env_rel': kn_deps matches via try eassumption above *)
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
      intros rho vnames C x S S' i Hwf Hwfe Hcons Hcmap Hdis Hdis_cmap Henv Hglob Hrel e_k Hdis_ek.
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
                (* global_env_rel' for ClosFix *)
                * admit.
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
      intros rho vnames C x S S' i Hwf Hwfe Hcons Hcmap Hdis Hdis_cmap Henv Hglob Hrel e_k Hdis_ek.
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
      intros rho vnames C x S S' i Hwf Hwfe Hcons Hcmap Hdis Hdis_cmap Henv Hglob Hrel e_k Hdis_ek.
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
