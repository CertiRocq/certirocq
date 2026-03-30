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

  Lemma set_many_get_notin y xs vs (rho : M.t val) :
    ~ List.In y xs ->
    M.get y (set_many xs vs rho) = M.get y rho.
  Proof.
    revert vs. induction xs as [ | a xs' IH]; intros vs Hnin.
    - reflexivity.
    - destruct vs as [ | v vs']. { reflexivity. }
      simpl. rewrite M.gso by (intro; apply Hnin; left; auto).
      apply IH. intro; apply Hnin; right; auto.
  Qed.

  Lemma set_many_get_in x xs vs rho :
    List.In x xs ->
    Datatypes.length xs = Datatypes.length vs ->
    exists v, M.get x (set_many xs vs rho) = Some v.
  Proof.
    revert vs. induction xs as [ | a xs' IH]; intros vs Hin Hlen.
    - destruct Hin.
    - destruct vs as [ | v vs']. { simpl in Hlen; lia. }
      simpl. destruct Hin as [-> | Hin'].
      + exists v. apply M.gss.
      + destruct (Pos.eq_dec x a) as [-> | Hneq].
        * exists v. apply M.gss.
        * rewrite M.gso by auto. apply IH. assumption. simpl in Hlen; lia.
  Qed.

  Lemma set_many_set_neq_base z x v xs vs rho :
    z <> x ->
    M.get z (set_many xs vs (M.set x v rho)) = M.get z (set_many xs vs rho).
  Proof.
    revert vs. induction xs as [ | a xs' IH]; intros vs Hneq.
    - simpl. rewrite M.gso; auto.
    - destruct vs as [ | va vs'].
      + simpl. rewrite M.gso; auto.
      + simpl. destruct (Pos.eq_dec z a) as [-> | Hza].
        * rewrite !M.gss. reflexivity.
        * rewrite !M.gso by auto. apply IH. exact Hneq.
  Qed.

  Lemma first_occurrence_exists (xs : list var) (k : nat) (x : var) :
    nth_error xs k = Some x ->
    exists k0, (k0 <= k)%nat /\ nth_error xs k0 = Some x /\
               forall j, (j < k0)%nat -> nth_error xs j <> Some x.
  Proof.
    revert k. induction xs as [ | a xs' IH]; intros k Hk.
    - destruct k; simpl in Hk; discriminate.
    - destruct k as [ | k'].
      + exists 0%nat. simpl in *. split; [ lia | split; [ exact Hk | ] ].
        intros j Hj. lia.
      + simpl in Hk.
        destruct (Pos.eq_dec a x) as [Heq | Hneq].
        * subst. exists 0%nat. simpl. split; [ lia | split; [ reflexivity | ] ].
          intros j Hj. lia.
        * destruct (IH k' Hk) as [k0 [Hle [Hk0 Hfirst]]].
          exists (S k0). simpl. split; [ lia | split; [ exact Hk0 | ] ].
          intros j Hj. destruct j as [ | j']; simpl.
          -- intros Heq'. inv Heq'. contradiction.
          -- apply Hfirst. lia.
  Qed.

  Lemma set_many_get_first xs vs rho x k :
    Datatypes.length xs = Datatypes.length vs ->
    nth_error xs k = Some x ->
    (forall (j : nat), (j < k)%nat -> nth_error xs j <> Some x) ->
    exists v, nth_error vs k = Some v /\
      M.get x (set_many xs vs rho) = Some v.
  Proof.
    revert vs k. induction xs as [ | a xs' IH]; intros vs k Hlen Hnth Hfirst.
    - destruct k; simpl in Hnth; discriminate.
    - destruct vs as [ | v0 vs']. { simpl in Hlen; lia. }
      simpl in Hlen.
      destruct k as [ | k'].
      + simpl in Hnth. inv Hnth. simpl.
        rewrite M.gss. eexists; eauto.
      + simpl in Hnth. simpl.
        assert (Ha_neq : a <> x).
        { intros ->. eapply (Hfirst 0%nat). lia. simpl. reflexivity. }
        rewrite M.gso by (now apply not_eq_sym).
        apply IH.
        * lia.
        * exact Hnth.
        * intros j Hj. apply (Hfirst (S j)). lia.
  Qed.

  Lemma get_list_exists xs (rho : M.t val) :
    (forall x, List.In x xs -> exists v, M.get x rho = Some v) ->
    exists vs, get_list xs rho = Some vs.
  Proof.
    induction xs as [ | a xs' IH]; intros Hbound.
    - exists []. reflexivity.
    - assert (Ha : exists v, M.get a rho = Some v)
        by (apply Hbound; left; reflexivity).
      destruct Ha as [v Hv].
      assert (IH_pre : forall x, List.In x xs' -> exists v0, M.get x rho = Some v0)
        by (intros x Hx; apply Hbound; right; exact Hx).
      destruct (IH IH_pre) as [vs_rest Hvs].
      exists (v :: vs_rest). simpl. rewrite Hv, Hvs. reflexivity.
  Qed.

  Lemma get_list_set_many_exists xs vs rho :
    Datatypes.length xs = Datatypes.length vs ->
    exists vs', get_list xs (set_many xs vs rho) = Some vs'.
  Proof.
    intros Hlen. eapply get_list_exists.
    intros y Hy. eapply set_many_get_in; eauto.
  Qed.

  Lemma get_list_nth_error (xs : list var) (vs : list val) (rho : M.t val)
        (k : nat) (x : var) :
    get_list xs rho = Some vs ->
    nth_error xs k = Some x ->
    nth_error vs k = M.get x rho.
  Proof.
    revert vs k. induction xs as [ | a xs' IH]; intros vs k Hgl Hnth.
    - destruct k; simpl in Hnth; discriminate.
    - simpl in Hgl.
      destruct (M.get a rho) eqn:Ha; [ | discriminate ].
      destruct (get_list xs' rho) eqn:Hrest; [ | discriminate ].
      inv Hgl.
      destruct k as [ | k'].
      + simpl in Hnth. inv Hnth. simpl. symmetry. exact Ha.
      + simpl in Hnth. simpl. exact (IH l k' eq_refl Hnth).
  Qed.

  (* list_consistent: if a key appears multiple times in a list,
     all corresponding values are related by R. *)
  Definition list_consistent {A : Type} (R : A -> A -> Prop)
             (keys : list var) (vals : list A) : Prop :=
    forall i j x vi vj,
      nth_error keys i = Some x ->
      nth_error keys j = Some x ->
      nth_error vals i = Some vi ->
      nth_error vals j = Some vj ->
      R vi vj.

  Lemma Forall2_from_nth_error {A B : Type} (R : A -> B -> Prop)
        (l1 : list A) (l2 : list B) :
    Datatypes.length l1 = Datatypes.length l2 ->
    (forall k a b, nth_error l1 k = Some a -> nth_error l2 k = Some b -> R a b) ->
    Forall2 R l1 l2.
  Proof.
    revert l2. induction l1 as [ | a l1' IH]; intros l2 Hlen Hpw.
    - destruct l2; [ constructor | simpl in Hlen; lia ].
    - destruct l2 as [ | b l2']; [ simpl in Hlen; lia | ].
      constructor.
      + exact (Hpw 0%nat a b eq_refl eq_refl).
      + apply IH.
        * simpl in Hlen; lia.
        * intros k a' b' Ha' Hb'. exact (Hpw (S k) a' b' Ha' Hb').
  Qed.

  Lemma get_list_set_many_consistent (R : val -> val -> Prop) xs vs (rho : M.t val) :
    (forall x, R x x) ->
    Datatypes.length xs = Datatypes.length vs ->
    list_consistent R xs vs ->
    exists vs', get_list xs (set_many xs vs rho) = Some vs' /\
                Forall2 R vs vs'.
  Proof.
    intros Hrefl Hlen Hcons.
    destruct (get_list_set_many_exists xs vs rho Hlen) as [vs' Hvs'].
    exists vs'. split; [ exact Hvs' | ].
    assert (Hlen' : Datatypes.length vs = Datatypes.length vs').
    { assert (H : Datatypes.length xs = Datatypes.length vs')
        by (eapply get_list_length_eq; exact Hvs').
      rewrite Hlen in H. exact H. }
    eapply Forall2_from_nth_error; [ exact Hlen' | ].
    intros k vk v'k Hvk Hv'k.
    destruct (nth_error xs k) as [x | ] eqn:Hx.
    2: { exfalso.
         apply nth_error_None in Hx.
         assert (Hlt : (k < Datatypes.length vs')%nat).
         { apply nth_error_Some. intro Habs. rewrite Habs in Hv'k. discriminate. }
         lia. }
    destruct (first_occurrence_exists xs k x Hx) as [k0 [Hle [Hk0 Hfirst]]].
    destruct (set_many_get_first xs vs rho x k0 Hlen Hk0 Hfirst) as [v0 [Hvk0 Hget]].
    assert (Hv'eq : nth_error vs' k = Some v0).
    { erewrite get_list_nth_error; [ | exact Hvs' | exact Hx ]. exact Hget. }
    assert (Heq : v'k = v0) by congruence. subst v'k.
    exact (Hcons k k0 x vk v0 Hx Hk0 Hvk Hvk0).
  Qed.

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

  (* Each element's deps are contained in the fold_left union. *)
  Lemma fold_left_KernameSet_In (l : list EAst.term) (init : KernameSet.t) (k : kername) :
    KernameSet.In k init \/ Exists (fun e => KernameSet.In k (term_global_deps e)) l ->
    KernameSet.In k (fold_left (fun acc x => KernameSet.union (term_global_deps x) acc) l init).
  Proof.
    revert init. induction l as [| e es IH]; intros init [Hinit | Hex].
    - exact Hinit.
    - inversion Hex.
    - apply IH. left. apply KernameSet.union_spec. right. exact Hinit.
    - inversion Hex; subst.
      + apply IH. left. apply KernameSet.union_spec. left. assumption.
      + apply IH. right. assumption.
  Qed.

  Lemma kn_deps_list_subset_construct ind c args k :
    kn_deps_list args k ->
    KernameSet.In k (term_global_deps (EAst.tConstruct ind c args)).
  Proof.
    intros Hk. destruct ind as [kn_ind idx_ind]. simpl.
    apply fold_left_KernameSet_In. right. exact Hk.
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

  (** ** Helpers for [anf_cvt_rel_args] and [eval_fuel_many] *)

  (* Extract individual evaluation from eval_fuel_many at position k. *)
  Lemma eval_fuel_many_nth rho es vs f t k e v :
    @eval_fuel_many _ LambdaBox_resource_fuel LambdaBox_resource_trace
                    Σ box_dc rho es vs f t ->
    nth_error es k = Some e ->
    nth_error vs k = Some v ->
    exists f_k t_k, src_eval rho e (fuel_sem.Val v) f_k t_k.
  Proof.
    intros Hmany. revert k.
    induction Hmany as [ | rho0 e0 es0 v0 vs0 f0 fs0 t0 ts0 Heval Hmany IH];
      intros k Hes Hvs.
    - destruct k; simpl in Hes; discriminate.
    - destruct k as [|k']; simpl in Hes, Hvs.
      + injection Hes as <-. injection Hvs as <-.
        exists f0, t0. exact Heval.
      + exact (IH k' Hes Hvs).
  Qed.

  Lemma eval_fuel_many_length vs es vs1 f1 t1 :
    @eval_fuel_many _ LambdaBox_resource_fuel LambdaBox_resource_trace
                    Σ box_dc vs es vs1 f1 t1 ->
    Datatypes.length vs1 = Datatypes.length es.
  Proof.
    intros Hrel. induction Hrel.
    - reflexivity.
    - simpl. f_equal. exact IHHrel.
  Qed.

  Lemma anf_cvt_rel_args_length S es vn S' C xs :
    anf_cvt_rel_args' S es vn S' C xs ->
    Datatypes.length xs = Datatypes.length es.
  Proof.
    intros H. induction H as [ | ? ? ? ? ? ? ? ? ? ? Hcvt_e Hcvt_rest IH].
    - reflexivity.
    - simpl. f_equal. exact IH.
  Qed.

  (* Extract individual anf_cvt_rel from anf_cvt_rel_args at position k. *)
  Lemma anf_cvt_rel_args_nth_cvt :
    forall S es vn S' C xs,
      anf_cvt_rel_args' S es vn S' C xs ->
      forall k e_k x_k,
        nth_error es k = Some e_k ->
        nth_error xs k = Some x_k ->
        exists S_k S_k' C_k,
          anf_cvt_rel' S_k e_k vn S_k' C_k x_k /\
          S_k \subset S.
  Proof.
    intros S es vn S' C xs Hcvt.
    induction Hcvt as [ | S1 S2 S3 vn0 t ts C1 x1 C2 xs0
                         Hcvt_hd Hcvt_tl IH];
      intros k e_k x_k Hes Hxs.
    - destruct k; simpl in Hes; discriminate.
    - destruct k as [|k']; simpl in Hes, Hxs.
      + injection Hes as <-. injection Hxs as <-.
        exists S1, S2, C1. split; [exact Hcvt_hd | apply Included_refl].
      + destruct (IH k' e_k x_k Hes Hxs) as [S_k [S_k' [C_k [Hcvt_k Hsub_k]]]].
        exists S_k, S_k', C_k. split; [exact Hcvt_k |].
        eapply Included_trans; [exact Hsub_k |].
        eapply (anf_cvt_exp_subset func_tag default_tag tgm cmap). exact Hcvt_hd.
  Qed.

  (* Every result variable of anf_cvt_rel_args is in FromList vn, S, or cmap_vars. *)
  Lemma anf_cvt_rel_args_In_range :
    forall xs S es vn S' C,
      anf_cvt_rel_args' S es vn S' C xs ->
      forall x, List.In x xs -> x \in FromList vn \/ x \in S \/ x \in cmap_vars cmap.
  Proof.
    induction xs as [ | x1 xs' IH]; intros S es vn S' C Hcvt x Hin.
    - destruct Hin.
    - remember (x1 :: xs') as xxs.
      destruct Hcvt; try discriminate.
      injection Heqxxs as Heq1 Heq2. subst.
      destruct Hin as [Heq | Hin].
      + subst. eapply anf_cvt_result_in_consumed. eassumption.
      + match goal with
        | [ Hcvt_rest : anf_cvt_rel_args _ _ _ _ _ _ _ _ _ _ |- _ ] =>
          destruct (IH _ _ _ _ _ Hcvt_rest x Hin) as [Hvn | [HS2 | Hcm]];
          [ left; exact Hvn
          | right; left;
            eapply (anf_cvt_exp_subset func_tag default_tag tgm cmap); eassumption
          | right; right; exact Hcm ]
        end.
  Qed.

  (* Result variables of anf_cvt_rel_args are not in the output set S'. *)
  Lemma anf_cvt_rel_args_results_not_in_output :
    forall xs S es vn S' C,
      anf_cvt_rel_args' S es vn S' C xs ->
      Disjoint _ (FromList vn) S ->
      Disjoint _ (cmap_vars cmap) S ->
      forall x, List.In x xs -> ~ x \in S'.
  Proof.
    induction xs as [ | x1 xs' IH]; intros S es vn S' C Hcvt Hdis Hdis_cm x Hin.
    - destruct Hin.
    - remember (x1 :: xs') as xxs.
      destruct Hcvt; try discriminate.
      injection Heqxxs as <- <-.
      destruct Hin as [<- | Hin'].
      + (* x = x1: result of head conversion, not in S2.
           S' ⊆ S2 by anf_cvt_args_subset, so x ∉ S'. *)
        intro HxS'.
        eapply anf_cvt_result_not_in_output; try eassumption.
        eapply (anf_cvt_args_subset func_tag default_tag tgm cmap); eassumption.
      + (* x ∈ xs': by IH, x ∉ S3 = S' *)
        eapply IH; try eassumption.
        * eapply Disjoint_Included_r;
            [eapply (anf_cvt_exp_subset func_tag default_tag tgm cmap); eassumption
            | exact Hdis].
        * eapply Disjoint_Included_r;
            [eapply (anf_cvt_exp_subset func_tag default_tag tgm cmap); eassumption
            | exact Hdis_cm].
  Qed.

  (* Fresh variables (not in vn, not in cmap_vars) appear at most once in xs. *)
  Lemma anf_cvt_rel_args_unique_fresh :
    forall xs S es vn S' C,
      anf_cvt_rel_args' S es vn S' C xs ->
      Disjoint _ (FromList vn) S ->
      Disjoint _ (cmap_vars cmap) S ->
      forall i j x,
        nth_error xs i = Some x -> nth_error xs j = Some x ->
        ~ x \in FromList vn ->
        ~ x \in cmap_vars cmap ->
        i = j.
  Proof.
    induction xs as [ | x1 xs' IH];
      intros S es vn S' C Hcvt Hdis Hdis_cm i j x Hxi Hxj Hx_not_vn Hx_not_cm.
    - destruct i; simpl in Hxi; discriminate.
    - remember (x1 :: xs') as xxs.
      destruct Hcvt; try discriminate.
      injection Heqxxs as Heq1 Heq2. subst.
      destruct i as [ | i'], j as [ | j']; simpl in Hxi, Hxj.
      + reflexivity.
      + exfalso.
        assert (Heq_x1 : x1 = x) by (simpl in Hxi; congruence). subst x1.
        assert (Hx_not_S2 : ~ x \in S2).
        { eapply anf_cvt_result_not_in_output; eassumption. }
        destruct (anf_cvt_rel_args_In_range _ _ _ _ _ _ Hcvt x (nth_error_In _ _ Hxj))
          as [Hvn | [HS2 | Hcm]].
        * exact (Hx_not_vn Hvn).
        * exact (Hx_not_S2 HS2).
        * exact (Hx_not_cm Hcm).
      + exfalso.
        assert (Heq_x1 : x1 = x) by (simpl in Hxj; congruence). subst x1.
        assert (Hx_not_S2 : ~ x \in S2).
        { eapply anf_cvt_result_not_in_output; eassumption. }
        destruct (anf_cvt_rel_args_In_range _ _ _ _ _ _ Hcvt x (nth_error_In _ _ Hxi))
          as [Hvn | [HS2 | Hcm]].
        * exact (Hx_not_vn Hvn).
        * exact (Hx_not_S2 HS2).
        * exact (Hx_not_cm Hcm).
      + f_equal.
        match goal with
        | [ Hcvt1 : anf_cvt_rel _ _ _ _ _ ?S2 _ _ _ _ |- _ ] =>
          eapply (IH _ _ _ _ _ Hcvt); try eassumption;
          [ eapply Disjoint_Included_r;
            [eapply anf_cvt_exp_subset; eassumption | exact Hdis]
          | eapply Disjoint_Included_r;
            [eapply anf_cvt_exp_subset; eassumption | exact Hdis_cm] ]
        end.
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

  Lemma wellformed_tConstruct n ind c args :
    wellformed Σ n (EAst.tConstruct ind c args) = true ->
    Forall (fun e => wellformed Σ n e = true) args.
  Proof.
    unfold wellformed. simpl. fold (@wellformed efl).
    intro H. apply List.Forall_forall. intros e He.
    destruct cstr_as_blocks.
    - apply Bool.andb_true_iff in H. destruct H as [_ Hwf_args].
      apply Bool.andb_true_iff in Hwf_args. destruct Hwf_args as [_ Hwf_args].
      rewrite forallb_forall in Hwf_args. exact (Hwf_args e He).
    - apply Bool.andb_true_iff in H. destruct H as [_ Hnil].
      destruct args; [inv He | simpl in Hnil; discriminate].
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

  (** cmap_consistent shorthand — instantiates the definition from anf_util. *)
  Let cmap_consistent :=
    @anf_util.cmap_consistent cmap nat
      LambdaBox_resource_fuel LambdaBox_resource_trace Σ box_dc.

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


  (* Position tracking for args: if xs[j] = vn[i] = x, then vs[j] = rho[i]. *)
  Lemma anf_cvt_rel_args_var_lookup rho es vs f t :
    @eval_fuel_many _ LambdaBox_resource_fuel LambdaBox_resource_trace
                    Σ box_dc rho es vs f t ->
    forall S vn S' C xs,
      anf_cvt_rel_args' S es vn S' C xs ->
      Disjoint _ (FromList vn) S ->
      Disjoint _ (cmap_vars cmap) S ->
      env_consistent vn rho ->
      cmap_consistent vn rho ->
      forall j i x,
        nth_error xs j = Some x ->
        nth_error vn i = Some x ->
        exists v, nth_error vs j = Some v /\ nth_error rho i = Some v.
  Proof.
    intros Hmany. induction Hmany as [ | rho0 e0 es0 v0 vs0 f0 fs0 t0 ts0 Heval Hmany IH].
    - intros S vn S' C xs Hcvt Hdis Hdis_cm Hcons Hcmap j i x Hj Hi.
      remember (@nil EAst.term) as ees.
      destruct Hcvt; try discriminate. destruct j; simpl in Hj; discriminate.
    - intros S vn S' C xs Hcvt Hdis Hdis_cm Hcons Hcmap j i x Hj Hi.
      remember (e0 :: es0) as ees.
      destruct Hcvt; try discriminate.
      injection Heqees as <- <-.
      destruct j as [ | j']; simpl in Hj.
      + inv Hj. exists v0. split; [ reflexivity | ].
        eapply anf_cvt_rel_var_lookup;
          [ exact Heval | eassumption | exact Hdis | exact Hdis_cm
          | exact Hcons | exact Hcmap | exact Hi ].
      + match goal with
        | [ Hcvt1 : anf_cvt_rel _ _ _ _ _ _ _ ?S2 _ _,
            Hcvt_rest : anf_cvt_rel_args _ _ _ _ ?S2 _ _ _ _ _ |- _ ] =>
          eapply IH; [ eassumption
                      | eapply Disjoint_Included_r;
                        [eapply anf_cvt_exp_subset; eassumption | exact Hdis]
                      | eapply Disjoint_Included_r;
                        [eapply anf_cvt_exp_subset; eassumption | exact Hdis_cm]
                      | exact Hcons | exact Hcmap | exact Hj | exact Hi ]
        end.
  Qed.

  (* If x ∈ FromList vn and the conversion result is x, then
     the ANF-env value at x is related to the evaluation result. *)
  Lemma anf_cvt_result_in_vnames_eval S e vn S' C x vs rho v f t v' :
    anf_env_rel' vn vs rho ->
    env_consistent vn vs ->
    cmap_consistent vn vs ->
    Disjoint _ (FromList vn) S ->
    Disjoint _ (cmap_vars cmap) S ->
    anf_cvt_rel' S e vn S' C x ->
    x \in FromList vn ->
    src_eval vs e (fuel_sem.Val v) f t ->
    M.get x rho = Some v' ->
    anf_val_rel' v v'.
  Proof.
    intros Hrel Hcons Hcmap Hdis Hdis_cm Hcvt Hin Heval Hget.
    destruct (In_nth_error _ _ Hin) as [k Hk].
    assert (Hvk := anf_cvt_rel_var_lookup _ _ _ _ _ Heval _ _ _ _ _ k
                      Hcvt Hdis Hdis_cm Hcons Hcmap Hk).
    unfold anf_env_rel' in Hrel.
    destruct (Forall2_nth_error_r _ _ _ k _ Hrel Hk)
      as [v_src [Hvsrc [v'' [Hget' Hvrel]]]].
    rewrite Hvk in Hvsrc. inv Hvsrc.
    rewrite Hget in Hget'. inv Hget'. exact Hvrel.
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

  (** App-specific: free variables of C2|[Eletapp ...]| avoid (S\\S2)\\{x1}. *)
  Lemma anf_cvt_disjoint_occurs_free_ctx_app S e1 vn S2 C1 x1
        e2 S3 C2 x2 r e_k :
    anf_cvt_rel' S e1 vn S2 C1 x1 ->
    anf_cvt_rel' S2 e2 vn S3 C2 x2 ->
    r \in S3 ->
    Disjoint _ (FromList vn) S ->
    Disjoint _ (cmap_vars cmap) S ->
    Disjoint _ (occurs_free e_k) ((S \\ (S3 \\ [set r])) \\ [set r]) ->
    Disjoint _ (occurs_free (C2 |[ Eletapp r x1 func_tag [x2] e_k ]|))
               ((S \\ S2) \\ [set x1]).
  Proof. admit. Admitted.

  (** If the ANF conversion result is a cmap variable not in [FromList vn],
      the associated constant appears in [term_global_deps e]. *)
  Lemma anf_cvt_cmap_result_in_deps S e vn S' C x k :
    anf_cvt_rel' S e vn S' C x ->
    lookup_const cmap k = Some x ->
    Disjoint _ (FromList vn) S ->
    Disjoint _ (cmap_vars cmap) S ->
    ~ x \in FromList vn ->
    KernameSet.In k (term_global_deps e).
  Proof.
    intros Hcvt Hlk Hdis Hdis_cm Hni.
    revert k Hlk Hdis Hdis_cm Hni.
    revert S e vn S' C x Hcvt.
    apply (anf_cvt_rel_ind' func_tag default_tag tgm cmap
      (fun S e vn S' C x =>
        forall k, lookup_const cmap k = Some x ->
        Disjoint _ (FromList vn) S ->
        Disjoint _ (cmap_vars cmap) S ->
        ~ x \in FromList vn ->
        KernameSet.In k (term_global_deps e))
      (fun _ _ _ _ _ _ => True)
      (fun _ _ _ _ _ _ => True)
      (fun _ _ _ _ _ _ _ _ => True));
    try (intros; exact I).
    (* Rel: x ∈ FromList vn → contradiction *)
    - intros S0 v vn0 n Hnth k0 Hlk Hdis Hdis_cm Hni.
      exfalso. apply Hni. eapply nth_error_In. exact Hnth.
    (* Lam: x = f ∈ S → cmap ∩ S contradiction *)
    - intros S0 S0' na e1 C1 r1 x1 f vn0 Hx1 Hf Hcvt1 IH1
             k0 Hlk Hdis Hdis_cm Hni.
      exfalso. eapply Hdis_cm. constructor.
      + exists k0. exact Hlk.
      + eapply Setminus_Included. exact Hf.
    (* App: x = r ∈ S3 ⊆ S → contradiction *)
    - intros S1 S2 S3 u C1 x1 v C2 x2 r vn0
             Hcvt1 IH1 Hcvt2 IH2 Hr
             k0 Hlk Hdis Hdis_cm Hni.
      exfalso. eapply Hdis_cm. constructor.
      + exists k0. exact Hlk.
      + eapply (anf_cvt_exp_subset func_tag default_tag tgm cmap). exact Hcvt1.
        eapply (anf_cvt_exp_subset func_tag default_tag tgm cmap). exact Hcvt2.
        exact Hr.
    (* Construct: x ∈ S → contradiction *)
    - intros. exfalso.
      match goal with
      | [ Hdcm : Disjoint _ (cmap_vars _) _,
          Hlk : lookup_const _ ?k_ = Some _,
          Hx : Ensembles.In _ _ _ |- _ ] =>
        eapply Hdcm; constructor; [exists k_; exact Hlk | exact Hx] end.
    (* LetIn: x2 from body. Use IH on binding or body. *)
    - intros S1 S2 S3 na b t0 C1 x1 C2 x2 vn0
             Hcvt1 IH1 Hcvt2 IH2
             k0 Hlk Hdis Hdis_cm Hni.
      simpl. apply KernameSet.union_spec.
      destruct (@Dec _ _ (Decidable_FromList (x1 :: vn0)) x2) as [Hin_ext | Hnin_ext].
      + unfold FromList, Ensembles.In in Hin_ext. simpl in Hin_ext.
        destruct Hin_ext as [<- | Hin_vn].
        * (* x2 = x1: use IH1 on the binding *)
          left. apply IH1; assumption.
        * (* x2 ∈ FromList vn0: contradicts Hni *)
          exfalso. exact (Hni Hin_vn).
      + (* x2 ∉ FromList (x1::vn0): use IH2 on the body *)
        right. apply IH2; try assumption.
        * rewrite FromList_cons. apply Union_Disjoint_l.
          -- apply Disjoint_Singleton_l.
             eapply anf_cvt_result_not_in_output; eassumption.
          -- eapply Disjoint_Included_r.
             eapply (anf_cvt_exp_subset func_tag default_tag tgm cmap). exact Hcvt1.
             exact Hdis.
        * eapply Disjoint_Included_r.
          eapply (anf_cvt_exp_subset func_tag default_tag tgm cmap). exact Hcvt1.
          exact Hdis_cm.
    (* Case: r ∈ S → contradiction *)
    - intros. exfalso.
      match goal with
      | [ Hdcm : Disjoint _ (cmap_vars _) _,
          Hlk : lookup_const _ ?k_ = Some _ |- _ ] =>
        eapply Hdcm; constructor; [exists k_; exact Hlk |] end.
      eapply Setminus_Included. eapply Setminus_Included.
      eapply (anf_cvt_exp_subset func_tag default_tag tgm cmap); [eassumption |].
      eapply (anf_cvt_branches_subset func_tag default_tag tgm cmap); eassumption.
    (* Fix: x ∈ FromList fnames ⊆ S → contradiction *)
    - intros. exfalso.
      match goal with
      | [ Hdcm : Disjoint _ (cmap_vars _) _,
          Hlk : lookup_const _ ?k_ = Some _,
          Hsub : FromList _ \subset _,
          Hnth : nth_error _ _ = Some _ |- _ ] =>
        eapply Hdcm; constructor; [exists k_; exact Hlk |];
        eapply Hsub; eapply nth_error_In; exact Hnth end.
    (* Box: x ∈ S → contradiction *)
    - intros S0 vn0 x0 Hx0 k0 Hlk Hdis Hdis_cm Hni.
      exfalso. eapply Hdis_cm. constructor.
      + exists k0. exact Hlk.
      + exact Hx0.
    (* Const: k = s by cmap_inj. k ∈ {s}. *)
    - intros S0 vn0 s v Hlk_s k0 Hlk_k Hdis Hdis_cm Hni.
      assert (k0 = s) by (eapply cmap_inj; eassumption). subst.
      simpl. apply KernameSet.singleton_spec. reflexivity.
    (* Proj: y ∈ S2 ⊆ S → contradiction *)
    - intros. exfalso.
      match goal with
      | [ Hdcm : Disjoint _ (cmap_vars _) _,
          Hlk : lookup_const _ ?k_ = Some _,
          Hcvt_c : anf_cvt_rel _ _ _ _ _ _ _ _ _ _,
          Hy : Ensembles.In _ _ _ |- _ ] =>
        eapply Hdcm; constructor; [exists k_; exact Hlk |];
        eapply (anf_cvt_exp_subset func_tag default_tag tgm cmap); [exact Hcvt_c | exact Hy] end.
    (* Prim: x ∈ S → contradiction *)
    - intros. exfalso.
      match goal with
      | [ Hdcm : Disjoint _ (cmap_vars _) _,
          Hlk : lookup_const _ ?k_ = Some _,
          Hx : Ensembles.In _ _ _ |- _ ] =>
        eapply Hdcm; constructor; [exists k_; exact Hlk | exact Hx] end.
  Qed.

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


  (* list_consistent: ANF args conversion preserves consistency.
     Duplicate xs positions map to the same source variable via var_lookup,
     so their target values are related via alpha-equiv. *)
  Lemma anf_cvt_args_consistent k rho_src es vs_src f t
        S vn S' C xs vs_tgt (rho_tgt : M.t val) :
    @eval_fuel_many _ LambdaBox_resource_fuel LambdaBox_resource_trace
                    Σ box_dc rho_src es vs_src f t ->
    anf_cvt_rel_args' S es vn S' C xs ->
    Disjoint _ (FromList vn) S ->
    Disjoint _ (cmap_vars cmap) S ->
    env_consistent vn rho_src ->
    cmap_consistent vn rho_src ->
    Forall2 anf_val_rel' vs_src vs_tgt ->
    global_env_rel' (kn_deps_list es) rho_tgt ->
    list_consistent (preord_val cenv eq_fuel k) xs vs_tgt.
  Proof.
    intros Hmany Hcvt Hdis Hdis_cm Hcons Hcmap HF2 Hglob_args
           i j x vi vj Hxi Hxj Hvi Hvj.
    destruct (Nat.eq_dec i j) as [Heq | Hneq].
    - (* i = j: reflexivity *)
      subst j. replace vj with vi by congruence.
      eapply preord_val_refl. tci.
    - (* i ≠ j: case split on x *)
      destruct (@Dec _ _ (Decidable_FromList vn) x) as [Hin_vn | Hnin_vn].
      + (* x ∈ FromList vn: var_lookup gives same source value *)
        destruct (In_nth_error _ _ Hin_vn) as [i_vn Hi_vn].
        destruct (anf_cvt_rel_args_var_lookup _ _ _ _ _ Hmany _ _ _ _ _
                    Hcvt Hdis Hdis_cm Hcons Hcmap _ _ _ Hxi Hi_vn)
          as [v_src_i [Hvsi Hrhoi]].
        destruct (anf_cvt_rel_args_var_lookup _ _ _ _ _ Hmany _ _ _ _ _
                    Hcvt Hdis Hdis_cm Hcons Hcmap _ _ _ Hxj Hi_vn)
          as [v_src_j [Hvsj Hrhoj]].
        rewrite Hrhoi in Hrhoj. injection Hrhoj as <-.
        destruct (Forall2_nth_error_l _ _ _ _ _ HF2 Hvsi) as [vt_i [Hvti Hrel_i]].
        destruct (Forall2_nth_error_l _ _ _ _ _ HF2 Hvsj) as [vt_j [Hvtj Hrel_j]].
        rewrite Hvi in Hvti. injection Hvti as <-.
        rewrite Hvj in Hvtj. injection Hvtj as <-.
        eapply (@anf_cvt_val_alpha_equiv
                  _ _ _ _ eq_fuel eq_fuel tgm cmap cenv
                  eq_fuel_compat (fun _ _ H0 => H0)
                  nat LambdaBox_resource_fuel LambdaBox_resource_trace
                  Σ box_dc Hglob_term func_tag default_tag); eassumption.
      + (* x ∉ FromList vn: use In_range to split S vs cmap *)
        destruct (anf_cvt_rel_args_In_range _ _ _ _ _ _ Hcvt x (nth_error_In _ _ Hxi))
          as [Hvn | [HS | Hcm]].
        * (* x ∈ FromList vn: contradicts Hnin_vn *)
          exfalso. exact (Hnin_vn Hvn).
        * (* x ∈ S: fresh, not in cmap_vars → unique in xs *)
          exfalso. apply Hneq.
          eapply anf_cvt_rel_args_unique_fresh; try eassumption.
          intro Hcm. eapply Hdis_cm. constructor; [exact Hcm | exact HS].
        * (* x ∈ cmap_vars: both produce the same cmap variable.
             Route through anf_cvt_cmap_eval to show both source values
             equal the evaluation of the same constant body in []. *)
          (* Get source values *)
          destruct (Forall2_nth_error_r _ _ _ i _ HF2 Hvi) as [v_src_i [Hvsi Hrel_i]].
          destruct (Forall2_nth_error_r _ _ _ j _ HF2 Hvj) as [v_src_j [Hvsj Hrel_j]].
          (* Get es positions from xs positions via length equality *)
          assert (Hlen_xs_es := anf_cvt_rel_args_length _ _ _ _ _ _ Hcvt).
          assert (Hi_range : (i < Datatypes.length es)%nat).
          { rewrite <- Hlen_xs_es. apply nth_error_Some. intro Habs. rewrite Habs in Hxi. discriminate. }
          assert (Hj_range : (j < Datatypes.length es)%nat).
          { rewrite <- Hlen_xs_es. apply nth_error_Some. intro Habs. rewrite Habs in Hxj. discriminate. }
          destruct (nth_error es i) as [e_i|] eqn:Hes_i; [| exfalso; apply nth_error_None in Hes_i; lia].
          destruct (nth_error es j) as [e_j|] eqn:Hes_j; [| exfalso; apply nth_error_None in Hes_j; lia].
          (* Get individual evals *)
          destruct (eval_fuel_many_nth _ _ _ _ _ _ _ _ Hmany Hes_i Hvsi) as [fi [ti Heval_i]].
          destruct (eval_fuel_many_nth _ _ _ _ _ _ _ _ Hmany Hes_j Hvsj) as [fj [tj Heval_j]].
          (* x ∈ cmap_vars → ∃ kn, lookup_const cmap kn = Some x *)
          destruct Hcm as [kn Hlk_kn].
          (* Extract individual anf_cvt_rel for es[i] and es[j] *)
          destruct (anf_cvt_rel_args_nth_cvt _ _ _ _ _ _ Hcvt _ _ _ Hes_i Hxi)
            as [Si [Si' [Ci [Hcvt_i Hsub_i]]]].
          destruct (anf_cvt_rel_args_nth_cvt _ _ _ _ _ _ Hcvt _ _ _ Hes_j Hxj)
            as [Sj [Sj' [Cj [Hcvt_j Hsub_j]]]].
          (* kn ∈ kn_deps_list es via anf_cvt_cmap_result_in_deps *)
          assert (Hkn_deps : kn_deps_list es kn).
          { unfold kn_deps_list. apply Exists_exists.
            exists e_i. split.
            - eapply nth_error_In. exact Hes_i.
            - eapply anf_cvt_cmap_result_in_deps; [ exact Hcvt_i | exact Hlk_kn | | | exact Hnin_vn ].
              + eapply Disjoint_Included_r; [exact Hsub_i | exact Hdis].
              + eapply Disjoint_Included_r; [exact Hsub_i | exact Hdis_cm]. }
          (* Get declared_constant from global_env_rel' *)
          destruct (Hglob_args kn x Hkn_deps Hlk_kn)
            as [decl [body [anf_v [Hdecl [Hbody [Hget Hrel_glob]]]]]].
          (* anf_cvt_cmap_eval on each: src_eval [] body (Val v_src_i/j) *)
          destruct (anf_cvt_cmap_eval _ _ _ _ _ Heval_i _ _ _ _ _ kn decl body
                      Hcvt_i
                      (Disjoint_Included_r _ _ _ Hsub_i Hdis)
                      (Disjoint_Included_r _ _ _ Hsub_i Hdis_cm)
                      Hcons Hcmap Hlk_kn Hdecl Hbody)
            as [fi' [ti' Heval_body_i]].
          destruct (anf_cvt_cmap_eval _ _ _ _ _ Heval_j _ _ _ _ _ kn decl body
                      Hcvt_j
                      (Disjoint_Included_r _ _ _ Hsub_j Hdis)
                      (Disjoint_Included_r _ _ _ Hsub_j Hdis_cm)
                      Hcons Hcmap Hlk_kn Hdecl Hbody)
            as [fj' [tj' Heval_body_j]].
          (* eval_val_det on body: v_src_i = v_src_j *)
          assert (Heq_v : v_src_i = v_src_j) by (eapply eval_val_det; eassumption).
          subst v_src_j.
          (* alpha_equiv *)
          eapply (@anf_cvt_val_alpha_equiv
                    _ _ _ _ eq_fuel eq_fuel tgm cmap cenv
                    eq_fuel_compat (fun _ _ H0 => H0)
                    nat LambdaBox_resource_fuel LambdaBox_resource_trace
                    Σ box_dc Hglob_term func_tag default_tag); eassumption.
  Qed.


  (** ** FixApp helper lemmas *)

  (* make_rec_env aux: length is n + length rho *)
  Lemma make_rec_env_aux_length mfix rho n :
    let make_env_aux :=
      fix f (n : nat) :=
        match n with O => rho | S n' => ClosFix_v rho mfix n' :: f n' end in
    Datatypes.length (make_env_aux n) = (n + Datatypes.length rho)%nat.
  Proof.
    simpl. induction n as [| n' IH]; simpl; lia.
  Qed.

  Lemma make_rec_env_length mfix rho :
    Datatypes.length (make_rec_env mfix rho) =
    (Datatypes.length mfix + Datatypes.length rho)%nat.
  Proof.
    unfold make_rec_env. apply make_rec_env_aux_length.
  Qed.

  (* nth_error into make_rec_env: closure part *)
  Lemma make_rec_env_aux_nth_closure mfix rho n i :
    let make_env_aux :=
      fix f (n : nat) :=
        match n with O => rho | S n' => ClosFix_v rho mfix n' :: f n' end in
    (i < n)%nat ->
    nth_error (make_env_aux n) i = Some (ClosFix_v rho mfix (n - 1 - i)).
  Proof.
    simpl. revert i. induction n as [| n' IH]; intros i Hi.
    - lia.
    - destruct i as [| i']; simpl.
      + replace (n' - 0 - 0)%nat with n' by lia. reflexivity.
      + replace (n' - 0 - S i')%nat with (n' - 1 - i')%nat by lia.
        apply IH. lia.
  Qed.

  Lemma make_rec_env_nth_closure mfix rho i :
    (i < Datatypes.length mfix)%nat ->
    nth_error (make_rec_env mfix rho) i = Some (ClosFix_v rho mfix (Datatypes.length mfix - 1 - i)).
  Proof.
    unfold make_rec_env. apply make_rec_env_aux_nth_closure.
  Qed.

  (* nth_error into make_rec_env: original env part *)
  Lemma make_rec_env_aux_nth_orig mfix rho n i :
    let make_env_aux :=
      fix f (n : nat) :=
        match n with O => rho | S n' => ClosFix_v rho mfix n' :: f n' end in
    nth_error (make_env_aux n) (n + i) = nth_error rho i.
  Proof.
    simpl. induction n as [| n' IH]; simpl; auto.
  Qed.

  Lemma make_rec_env_nth_orig mfix rho i :
    nth_error (make_rec_env mfix rho) (Datatypes.length mfix + i) = nth_error rho i.
  Proof.
    unfold make_rec_env. apply make_rec_env_aux_nth_orig.
  Qed.

  (* well_formed_env for make_rec_env *)
  Lemma well_formed_env_make_rec_env mfix rho :
    Forall (well_formed_val Σ) rho ->
    Forall (fun d =>
              EAst.isLambda d.(EAst.dbody) = true /\
              wellformed Σ (Datatypes.length mfix + Datatypes.length rho) d.(EAst.dbody) = true)
           mfix ->
    well_formed_env Σ (make_rec_env mfix rho).
  Proof.
    intros Hwf_rho Hwf_mfix.
    unfold well_formed_env, make_rec_env.
    set (n := Datatypes.length mfix).
    assert (Hn : (n <= Datatypes.length mfix)%nat) by lia.
    clearbody n. revert Hn.
    induction n as [| n' IH]; intros Hn.
    - simpl. exact Hwf_rho.
    - simpl. constructor.
      + apply Wf_ClosFix.
        * exact Hwf_rho.
        * lia.
        * exact Hwf_mfix.
      + apply IH. lia.
  Qed.

  (* env_consistent for concatenated lists:
     NoDup on left half + env_consistent on right half
     + disjointness + length match *)
  Lemma env_consistent_app l1 l2 v1 v2 :
    NoDup l1 ->
    env_consistent l2 v2 ->
    Disjoint _ (FromList l1) (FromList l2) ->
    Datatypes.length l1 = Datatypes.length v1 ->
    env_consistent (l1 ++ l2) (v1 ++ v2).
  Proof.
    intros Hnd Hcons Hdis Hlen i j y Hi Hj.
    destruct (Nat.lt_ge_cases i (Datatypes.length l1)) as [Hli | Hli],
             (Nat.lt_ge_cases j (Datatypes.length l1)) as [Hlj | Hlj].
    - (* both in l1 *)
      rewrite nth_error_app1 in Hi by lia.
      rewrite nth_error_app1 in Hj by lia.
      assert (i = j).
      { apply (proj1 (NoDup_nth_error l1) Hnd i j Hli).
        rewrite Hi, Hj. reflexivity. }
      subst j. reflexivity.
    - (* i in l1, j in l2 — contradiction *)
      rewrite nth_error_app1 in Hi by lia.
      rewrite nth_error_app2 in Hj by lia.
      exfalso. destruct Hdis as [Hd]. apply (Hd y). constructor.
      + eapply nth_error_In. exact Hi.
      + eapply nth_error_In. exact Hj.
    - (* i in l2, j in l1 — contradiction *)
      rewrite nth_error_app2 in Hi by lia.
      rewrite nth_error_app1 in Hj by lia.
      exfalso. destruct Hdis as [Hd]. apply (Hd y). constructor.
      + eapply nth_error_In. exact Hj.
      + eapply nth_error_In. exact Hi.
    - (* both in l2 *)
      rewrite nth_error_app2 in Hi by lia.
      rewrite nth_error_app2 in Hj by lia.
      assert (Hli' : (Datatypes.length v1 <= i)%nat) by lia.
      assert (Hlj' : (Datatypes.length v1 <= j)%nat) by lia.
      rewrite nth_error_app2 by exact Hli'.
      rewrite nth_error_app2 by exact Hlj'.
      replace (i - Datatypes.length v1)%nat with (i - Datatypes.length l1)%nat by lia.
      replace (j - Datatypes.length v1)%nat with (j - Datatypes.length l1)%nat by lia.
      eapply Hcons; eassumption.
  Qed.

  (* NoDup implies env_consistent (any rho) *)
  Lemma NoDup_env_consistent' vn rho :
    NoDup vn -> env_consistent vn rho.
  Proof.
    intros Hnd i j x Hi Hj.
    assert (Hib : (i < Datatypes.length vn)%nat)
      by (apply nth_error_Some; congruence).
    assert (i = j).
    { apply (proj1 (NoDup_nth_error vn) Hnd i j Hib). rewrite Hi, Hj. reflexivity. }
    subst j. reflexivity.
  Qed.

  (* cmap_consistent extends to l1 ++ l2 when l1 ∩ cmap_vars = ∅ *)
  Lemma cmap_consistent_app l1 l2 v1 v2 :
    cmap_consistent l2 v2 ->
    Disjoint _ (cmap_vars cmap) (FromList l1) ->
    Datatypes.length l1 = Datatypes.length v1 ->
    cmap_consistent (l1 ++ l2) (v1 ++ v2).
  Proof.
    intros Hcm Hdis Hlen i x k decl body Hi Hlk Hdecl Hbody.
    destruct (Nat.lt_ge_cases i (Datatypes.length l1)) as [Hli | Hli].
    - (* i in l1: l1[i] = x is a cmap var, contradicts disjointness *)
      rewrite nth_error_app1 in Hi by lia.
      exfalso. destruct Hdis as [Hd]. apply (Hd x).
      constructor.
      + exists k. exact Hlk.
      + eapply nth_error_In. exact Hi.
    - (* i in l2 *)
      rewrite nth_error_app2 in Hi by lia.
      destruct (Hcm _ _ _ _ _ Hi Hlk Hdecl Hbody) as (v_i & f_i & t_i & Hnth_i & Heval_i).
      exists v_i, f_i, t_i. split; [| exact Heval_i].
      rewrite nth_error_app2 by lia.
      replace (i - Datatypes.length v1)%nat with (i - Datatypes.length l1)%nat by lia.
      exact Hnth_i.
  Qed.

  (* anf_env_rel' extends through def_funs / make_rec_env *)
  Lemma anf_env_rel_extend_fundefs fnames0 names0 S1 mfix Bs S2 rho_s rho_t :
    anf_env_rel' names0 rho_s rho_t ->
    anf_fix_rel func_tag default_tag tgm cmap
      fnames0 names0 S1 fnames0 mfix Bs S2 ->
    NoDup fnames0 ->
    env_consistent names0 rho_s ->
    cmap_consistent names0 rho_s ->
    Disjoint _ (FromList names0 :|: FromList fnames0) S1 ->
    Disjoint _ (cmap_vars cmap) S1 ->
    Disjoint _ (cmap_vars cmap) (FromList fnames0) ->
    Disjoint _ (FromList names0) (FromList fnames0) ->
    global_env_rel' (kn_deps_mfix mfix) rho_t ->
    anf_env_rel' (rev fnames0 ++ names0)
                  (make_rec_env mfix rho_s)
                  (def_funs Bs Bs rho_t rho_t).
  Proof.
    intros Henv Hfix Hnd Hcons Hcmap_c Hdis1 Hdis_cm Hdis_cm_fn Hdis_nf Hglob_fix.
    unfold anf_env_rel'.
    assert (Hflen : Datatypes.length fnames0 = Datatypes.length mfix).
    { eapply anf_fix_rel_fnames_length. exact Hfix. }
    assert (Henames : all_fun_name Bs = fnames0).
    { eapply anf_fix_rel_names. exact Hfix. }
    (* Decompose make_rec_env into closures ++ rho_s.
       We prove this by showing nth_error agreement at all positions. *)
    assert (Hdecomp : exists cls,
      make_rec_env mfix rho_s = cls ++ rho_s /\
      Datatypes.length cls = Datatypes.length mfix /\
      forall i, (i < Datatypes.length mfix)%nat ->
        nth_error cls i = Some (ClosFix_v rho_s mfix (Datatypes.length mfix - 1 - i))).
    { unfold make_rec_env. generalize (Datatypes.length mfix) as n.
      induction n as [| n' IH].
      - exists []. simpl. repeat split; auto. intros; lia.
      - destruct IH as [cls' [Hd' [Hl' Hn']]].
        exists (ClosFix_v rho_s mfix n' :: cls'). simpl. rewrite Hd'.
        repeat split.
        + simpl. lia.
        + intros i Hi. destruct i as [| i'].
          * simpl. replace (n' - 0 - 0)%nat with n' by lia. reflexivity.
          * simpl. rewrite Hn' by lia.
            replace (n' - 0 - S i')%nat with (n' - 1 - i')%nat by lia.
            reflexivity. }
    destruct Hdecomp as [cls [Hdecomp [Hlen_cls Hnth_cls]]].
    rewrite Hdecomp.
    (* Split into fnames part and names part *)
    apply Forall2_app.
    - (* Part 1: rev fnames0 vs fix closures *)
      apply Forall2_from_nth_error.
      + rewrite length_rev. lia.
      + (* k-th element: v_src from cls, fname from rev fnames0 *)
        intros k v_src fname Hv Hk.
        assert (Hk_bound : (k < Datatypes.length cls)%nat).
        { apply nth_error_Some. congruence. }
        assert (Hk_bound' : (k < Datatypes.length fnames0)%nat) by lia.
        assert (Hv' := Hnth_cls k ltac:(lia)).
        rewrite Hv' in Hv. injection Hv as <-.
        (* fname = fnames0[len - 1 - k] via nth_error rev *)
        assert (Hfn_idx : nth_error fnames0 (Datatypes.length fnames0 - 1 - k) = Some fname).
        { pose proof (nth_error_rev k fnames0) as Hr.
          rewrite Hr in Hk.
          destruct (Nat.ltb_spec k (Datatypes.length fnames0)); [| discriminate].
          replace (Datatypes.length fnames0 - 1 - k)%nat
            with (Datatypes.length fnames0 - S k)%nat by lia.
          exact Hk. }
        (* Target: M.get fname (def_funs Bs Bs rho_t rho_t) = Vfun rho_t Bs fname *)
        eexists. split.
        { apply def_funs_eq.
          eapply (proj2 (Same_set_all_fun_name Bs)).
          rewrite Henames. eapply nth_error_In. exact Hfn_idx. }
        (* Build anf_rel_ClosFix *)
        rewrite Hflen in Hfn_idx.
        exact (@anf_rel_ClosFix _ _ _ _ _ _ _ _ _ S1 S2 names0 fnames0
                  rho_s rho_t mfix Bs
                  (Datatypes.length mfix - 1 - k) fname
                  Henv Hcons Hcmap_c Hnd Hdis1 Hdis_cm Hdis_cm_fn Hdis_nf
                  Hfn_idx Hfix Hglob_fix).
    - (* Part 2: names0 vs original env, through def_funs *)
      eapply Forall2_monotonic_strong; [| exact Henv].
      intros v_src x_name _ Hx_in [v_tgt [Hget Hval]].
      eexists. split; [| exact Hval].
      rewrite def_funs_neq; [exact Hget |].
      intros Hc. apply (proj1 (Same_set_all_fun_name _)) in Hc.
      rewrite Henames in Hc.
      destruct Hdis_nf as [Hd]. apply (Hd x_name). constructor; assumption.
  Qed.

  (* global_env_rel' preserved through def_funs when fnames ∩ cmap_vars = ∅ *)
  Lemma global_env_rel_def_funs D Bs rho :
    global_env_rel' D rho ->
    Disjoint _ (cmap_vars cmap) (name_in_fundefs Bs) ->
    global_env_rel' D (def_funs Bs Bs rho rho).
  Proof.
    intros Hglob Hdis k v Hd Hlk.
    assert (Hneq : ~ name_in_fundefs Bs v).
    { intro Hc. destruct Hdis as [Hd']. apply (Hd' v). constructor.
      - exists k. exact Hlk.
      - exact Hc. }
    destruct (Hglob k v Hd Hlk) as (decl & body & anf_v & Hdecl & Hbody & Hget & Hrel).
    exists decl, body, anf_v. repeat split; try assumption.
    rewrite def_funs_neq; [exact Hget | exact Hneq].
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
                - eapply anf_cvt_disjoint_occurs_free_ctx_app;
                    [exact Hcvt_e1 | exact Hcvt_e2
                    | match goal with Hr : x \in S3 |- _ => exact Hr end
                    | exact Hdis | exact Hdis_cmap | exact Hdis_ek].
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
            (* Extract cmap_consistent from inv *)
            assert (Hcmap_clos : cmap_consistent names rho') by assumption.
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
                apply env_consistent_extend_fresh.
                + match goal with H : env_consistent _ _ |- _ => exact H end.
                + intro Hc.
                  match goal with H : ~ Ensembles.In _ (_ |: FromList _) _ |- _ =>
                    apply H end. right. exact Hc.
              - (* cmap_consistent (x0::names) (v2::rho') *)
                apply cmap_consistent_extend; [exact Hcmap_clos |].
                (* x0 is NOT a cmap variable, so the condition is vacuous *)
                intros k_c decl_c body_c Hlk_c Hdecl_c Hbody_c.
                exfalso.
                match goal with H : ~ Ensembles.In _ (cmap_vars cmap) x0 |- _ =>
                  apply H end. exists k_c. exact Hlk_c.
              - (* Disjoint (FromList (x0::names)) S1 *)
                rewrite FromList_cons. eapply Union_Disjoint_l.
                + eapply Disjoint_Singleton_l.
                  intro Hin.
                  match goal with Hd : Disjoint var (_ |: _) S1 |- _ =>
                    destruct Hd as [Hd']; apply (Hd' x0);
                    constructor; [left; constructor | exact Hin] end.
                + eapply Disjoint_Included_l.
                  * intros z Hz. apply Union_intror. apply Union_intror. exact Hz.
                  * match goal with Hd : Disjoint var (_ |: _) S1 |- _ => exact Hd end.
              - (* Disjoint (cmap_vars cmap) S1 *) eassumption.
              - (* anf_env_rel (x0::names) (v2::rho') rho_bc *)
                unfold rho_bc. constructor.
                + exists v2'. split; [rewrite M.gss; reflexivity | exact Hrel_v2].
                + eapply anf_env_rel_weaken;
                    [| intro Hc;
                       match goal with H : ~ Ensembles.In var (_ |: _) x0 |- _ =>
                         apply H; right; exact Hc end].
                  eapply anf_env_rel_weaken; [eassumption |].
                  match goal with H : ~ Ensembles.In var (FromList _) f0 |- _ => exact H end.
              - (* global_env_rel' (kn_deps body0) rho_bc *)
                unfold rho_bc.
                eapply global_env_rel_set_fresh;
                  [| match goal with H : ~ Ensembles.In var (cmap_vars cmap) x0 |- _ => exact H end].
                eapply global_env_rel_set_fresh;
                  [| match goal with H : ~ Ensembles.In var (cmap_vars cmap) f0 |- _ => exact H end].
                eassumption.
              - (* anf_cvt_rel' *) eassumption.
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
              (* Step 1: get v_rho at x1 with anf_val_rel for both source values.
                 Two sub-cases: x1 ∈ FromList vnames (use anf_env_rel)
                 or x1 ∈ cmap_vars only (use global_env_rel'). *)
              assert (Hrel_rho_ex : exists v_rho,
                M.get x1 rho = Some v_rho /\
                anf_val_rel' (Clos_v rho' na0 body0) v_rho /\
                anf_val_rel' v2 v_rho /\
                Clos_v rho' na0 body0 = v2).
              { destruct (In_dec Pos.eq_dec x1 vnames) as [Hin_vn | Hni_vn].
                - (* x1 ∈ FromList vnames: from anf_env_rel *)
                  apply In_nth_error in Hin_vn. destruct Hin_vn as [k0 Hk0].
                  assert (Heval1_k : nth_error rho0 k0 = Some (Clos_v rho' na0 body0)).
                  { eapply anf_cvt_rel_var_lookup;
                      [exact Heval1 | exact Hcvt_e1 | exact Hdis | exact Hdis_cmap
                      | exact Hcons | exact Hcmap | exact Hk0]. }
                  assert (Heval2_k : nth_error rho0 k0 = Some v2).
                  { eapply anf_cvt_rel_var_lookup;
                      [exact Heval2 | exact Hcvt_e2
                      | eapply Disjoint_Included_r;
                          [eapply anf_cvt_exp_subset; exact Hcvt_e1 | exact Hdis]
                      | eapply Disjoint_Included_r;
                          [eapply anf_cvt_exp_subset; exact Hcvt_e1 | exact Hdis_cmap]
                      | exact Hcons | exact Hcmap | exact Hk0]. }
                  destruct (Forall2_nth_error_r _ _ _ _ _ Henv Hk0)
                    as [v_src [Hsrc [v_rho [Hget Hrel]]]].
                  assert (v_src = Clos_v rho' na0 body0) by congruence. subst v_src.
                  assert (Heq_v2' : Clos_v rho' na0 body0 = v2) by congruence.
                  exists v_rho. split; [exact Hget |]. split; [exact Hrel |].
                  split; [subst v2; exact Hrel | exact Heq_v2'].
                - (* x1 ∉ FromList vnames: from global_env_rel' + cmap *)
                  destruct (anf_cvt_result_in_consumed _ _ _ _ _ _ Hcvt_e1)
                    as [Hin1 | [Hin1 | Hin1]].
                  + contradiction.
                  + exfalso. destruct (anf_cvt_result_in_consumed _ _ _ _ _ _ Hcvt_e2)
                      as [Hin2 | [Hin2 | Hin2]].
                    * contradiction.
                    * eapply anf_cvt_result_not_in_output;
                        [exact Hcvt_e1 | exact Hdis | exact Hdis_cmap | exact Hin2].
                    * destruct Hdis_cmap as [Hdc]. apply (Hdc x1).
                      constructor; [exact Hin2 | exact Hin1].
                  +
                  destruct Hin1 as [k_c1 Hlk1].
                  assert (Hkc_deps : kn_deps (EAst.tApp e1 e2) k_c1).
                  { unfold kn_deps. simpl. apply KernameSet.union_spec. left.
                    eapply anf_cvt_cmap_result_in_deps;
                      [exact Hcvt_e1 | exact Hlk1 | exact Hdis | exact Hdis_cmap | exact Hni_vn]. }
                  destruct (Hglob k_c1 x1 Hkc_deps Hlk1)
                    as (decl_g & body_g & v_rho & Hdecl_g & Hbody_g & Hget_g & Hrel_g).
                  exists v_rho. split; [exact Hget_g |].
                  assert (Heval1_cmap : exists f_c t_c,
                    src_eval [] body_g (fuel_sem.Val (Clos_v rho' na0 body0)) f_c t_c).
                  { eapply anf_cvt_cmap_eval;
                      [exact Heval1 | exact Hcvt_e1 | exact Hdis | exact Hdis_cmap
                      | exact Hcons | exact Hcmap | exact Hlk1 | exact Hdecl_g | exact Hbody_g]. }
                  destruct Heval1_cmap as [f_c1 [t_c1 Hev1]].
                  assert (Heval2_cmap : exists f_c t_c,
                    src_eval [] body_g (fuel_sem.Val v2) f_c t_c).
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
                  eapply eval_val_det; [exact Hev1 | exact Hev2]. }
              destruct Hrel_rho_ex as [v_rho [Hget_rho [Hrel_rho [Hrel_rho_v2 Heq_v2]]]].
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
                (* x1 ∈ S (from x ∈ S3 ⊆ S2 ⊆ S), but x1 ∉ S
                   since x1 ∈ FromList vnames ∨ cmap_vars, both disjoint from S *)
                assert (Hx1_in_S : x1 \in S).
                { eapply anf_cvt_exp_subset. exact Hcvt_e1.
                  eapply anf_cvt_exp_subset. exact Hcvt_e2.
                  match goal with Hr : x1 \in S3 |- _ => exact Hr end. }
                destruct (anf_cvt_result_in_consumed _ _ _ _ _ _ Hcvt_e1)
                  as [Hin1 | [Hin1 | Hin1]].
                - eapply Hdis. constructor; eassumption.
                - (* x1 ∈ S: x1 ∉ S2 (from result_not_in_output on e1), but x1 ∈ S3 ⊆ S2 *)
                  assert (Hx1_not_S2 : ~ x1 \in S2).
                  { eapply anf_cvt_result_not_in_output; eassumption. }
                  apply Hx1_not_S2. eapply anf_cvt_exp_subset; [exact Hcvt_e2 |].
                  match goal with Hr : x1 \in S3 |- _ => exact Hr end.
                - eapply Hdis_cmap. constructor; eassumption. }
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
                    * assert (v0 = v_rho) by congruence. subst v0.
                      exact Hrel_rho_v2.
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
                  * (* x2 ∈ cmap_vars: case split on x2 ∈ FromList vnames *)
                    destruct (In_dec Pos.eq_dec x2 vnames) as [Hin2_vn | Hni2_vn].
                    -- (* x2 also in FromList: use alpha-equiv *)
                       eexists. split.
                       { unfold rho_app. rewrite M.gso; [rewrite M.gss; reflexivity | exact Hneq_x]. }
                       apply In_nth_error in Hin2_vn. destruct Hin2_vn as [k0' Hk0'].
                       assert (Heval2_k' : nth_error rho0 k0' = Some v2).
                       { eapply anf_cvt_rel_var_lookup; [exact Heval2 | exact Hcvt_e2 | | | | | exact Hk0'].
                         - eapply Disjoint_Included_r;
                             [eapply anf_cvt_exp_subset; exact Hcvt_e1 | exact Hdis].
                         - eapply Disjoint_Included_r;
                             [eapply anf_cvt_exp_subset; exact Hcvt_e1 | exact Hdis_cmap].
                         - exact Hcons. - exact Hcmap. }
                       destruct (Forall2_nth_error_r _ _ _ _ _ Henv Hk0')
                         as [v_src' [Hk0_src' [w_k0' [Hget_k0' Hrel_k0']]]].
                       assert (v_src' = v2) by congruence. subst v_src'.
                       assert (w_k0' = w) by congruence. subst w_k0'.
                       eapply (@anf_cvt_val_alpha_equiv
                                 _ _ _ _ eq_fuel eq_fuel tgm cmap cenv
                                 eq_fuel_compat (fun _ _ H => H)
                                 nat LambdaBox_resource_fuel LambdaBox_resource_trace
                                 Σ box_dc Hglob_term func_tag default_tag);
                         [exact Hrel_k0' | exact Hrel_v2].
                    -- (* x2 not in FromList: use global_env_rel' *)
                       eexists. split.
                       { unfold rho_app. rewrite M.gso; [rewrite M.gss; reflexivity | exact Hneq_x]. }
                       destruct Hin_cm as [k_c Hlk_c].
                       assert (Hkc_deps : kn_deps (EAst.tApp e1 e2) k_c).
                       { unfold kn_deps. simpl. apply KernameSet.union_spec. right.
                         eapply anf_cvt_cmap_result_in_deps;
                           [exact Hcvt_e2 | exact Hlk_c
                           | eapply Disjoint_Included_r;
                               [eapply anf_cvt_exp_subset; exact Hcvt_e1 | exact Hdis]
                           | eapply Disjoint_Included_r;
                               [eapply anf_cvt_exp_subset; exact Hcvt_e1 | exact Hdis_cmap]
                           | exact Hni2_vn]. }
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
                         - exact Hcons. - exact Hcmap. }
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
                    -- (* x1 ∈ cmap_vars: case split on x1 ∈ FromList vnames *)
                       destruct (In_dec Pos.eq_dec x1 vnames) as [Hin1_vn | Hni1_vn].
                       ++ (* x1 also in FromList: use alpha-equiv *)
                          eexists. split.
                          { unfold rho_app. rewrite M.gso; [| exact Hneq_x].
                            rewrite M.gso; [rewrite M.gss; reflexivity | exact Hneq_x1x2]. }
                          apply In_nth_error in Hin1_vn. destruct Hin1_vn as [k1' Hk1'].
                          assert (Heval1_k' : nth_error rho0 k1' = Some (Clos_v rho' na0 body0)).
                          { eapply anf_cvt_rel_var_lookup;
                              [exact Heval1 | exact Hcvt_e1 | exact Hdis | exact Hdis_cmap
                              | exact Hcons | exact Hcmap | exact Hk1']. }
                          destruct (Forall2_nth_error_r _ _ _ _ _ Henv Hk1')
                            as [v_src1' [Hk1_src' [w_k1' [Hget_k1' Hrel_k1']]]].
                          assert (v_src1' = Clos_v rho' na0 body0) by congruence. subst v_src1'.
                          assert (w_k1' = w) by congruence. subst w_k1'.
                          eapply (@anf_cvt_val_alpha_equiv
                                    _ _ _ _ eq_fuel eq_fuel tgm cmap cenv
                                    eq_fuel_compat (fun _ _ H => H)
                                    nat LambdaBox_resource_fuel LambdaBox_resource_trace
                                    Σ box_dc Hglob_term func_tag default_tag);
                            [exact Hrel_k1' | exact Hrel_clos_saved].
                       ++ (* x1 not in FromList: use global_env_rel' *)
                          eexists. split.
                          { unfold rho_app. rewrite M.gso; [| exact Hneq_x].
                            rewrite M.gso; [rewrite M.gss; reflexivity | exact Hneq_x1x2]. }
                          destruct Hin_cm1 as [k_c1 Hlk_c1].
                          assert (Hkc1_deps : kn_deps (EAst.tApp e1 e2) k_c1).
                          { unfold kn_deps. simpl. apply KernameSet.union_spec. left.
                            eapply anf_cvt_cmap_result_in_deps;
                              [exact Hcvt_e1 | exact Hlk_c1
                              | exact Hdis | exact Hdis_cmap | exact Hni1_vn]. }
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
      subst rho''. inv Hrel.
      match goal with
      | [ He1 : anf_cvt_rel _ _ _ _ _ e1 vnames _ _ _,
          He2 : anf_cvt_rel _ _ _ _ _ e2 vnames _ _ _ |- _ ] =>
        rename He1 into Hcvt_e1; rename He2 into Hcvt_e2
      end.
      rewrite <- !app_ctx_f_fuse.
      split.
      + intros v v' Heq Hrel'. subst r0.
        (* Well-formedness of intermediate values *)
        assert (Hwf_fix : well_formed_val Σ (ClosFix_v rho' mfix0 idx0)).
        { eapply eval_preserves_wf; [exact Hwf | | exact Heval1].
          rewrite (anf_env_rel_length _ _ _ Henv).
          exact (proj1 (wellformed_tApp _ _ _ Hwfe)). }
        assert (Hwf_v2 : well_formed_val Σ v2).
        { eapply eval_preserves_wf; [exact Hwf | | exact Heval2].
          rewrite (anf_env_rel_length _ _ _ Henv).
          exact (proj2 (wellformed_tApp _ _ _ Hwfe)). }
        destruct (@anf_val_rel_exists func_tag default_tag tgm cmap _ Σ box_dc
                    nat LambdaBox_resource_fuel LambdaBox_resource_trace
                    (ClosFix_v rho' mfix0 idx0) Hwf_fix) as [fix_v' Hrel_fix].
        destruct (@anf_val_rel_exists func_tag default_tag tgm cmap _ Σ box_dc
                    nat LambdaBox_resource_fuel LambdaBox_resource_trace
                    v2 Hwf_v2) as [v2' Hrel_v2].
        pose proof Hrel_fix as Hrel_fix_saved.
        (* Invert ClosFix structure *)
        remember (ClosFix_v rho' mfix0 idx0) as fix_val eqn:Heqfix.
        destruct Hrel_fix; try discriminate.
        injection Heqfix as -> -> ->. subst.
        (* H : env_rel names rho' rho1, H0 : env_consistent names rho'
           H1 : cmap_consistent, H2 : NoDup fnames, H3-H6 : disjointness
           H7 : nth_error fnames idx0 = Some f0, H9 : anf_fix_rel
           H10 : global_env_rel' (kn_deps_mfix mfix0) rho1 *)
        (* IH chaining: same as App case *)
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
                - eapply anf_cvt_disjoint_occurs_free_ctx_app;
                    [exact Hcvt_e1 | exact Hcvt_e2 | exact H8
                    | exact Hdis | exact Hdis_cmap | exact Hdis_ek].
                - eapply IH1_val; eauto. }
            eapply preord_exp_trans with (P1 := anf_bound (f3 + 2) (t3 + 2)).
            tci. exact eq_fuel_idemp.
            (* IH2: evaluate e2 via C2 *)
            2:{ intros m.
                assert (Hdis_eletapp :
                  Disjoint _ (occurs_free (Eletapp x x1 func_tag [x2] e_k))
                             ((S2 \\ S3) \\ [set x2])).
                { admit. }
                edestruct (IH2 (M.set x1 (Vfun rho1 Bs f0) rho) vnames C2 x2 S2 S3 m) as [IH2_val _].
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
                  assert (Hek : nth_error rho0 k = Some (ClosFix_v rho' mfix0 idx0)).
                  { change positive with var in Hk.
                    eapply anf_cvt_rel_var_lookup;
                      [exact Heval1 | exact Hcvt_e1
                      | exact Hdis | exact Hdis_cmap | exact Hcons | exact Hcmap | exact Hk]. }
                  exists (ClosFix_v rho' mfix0 idx0). split; [exact Hek | exact Hrel_fix_saved].
                - (* global_env_rel' (kn_deps e2) for M.set x1 fix_v' rho *)
                  assert (Hglob_e2 : global_env_rel' (kn_deps e2) rho).
                  { eapply global_env_rel_mono; [exact Hglob |].
                    intros k0 Hk0. unfold kn_deps. simpl.
                    apply KernameSet.union_spec. right. exact Hk0. }
                  eapply global_env_rel_set; [exact Hglob_e2 |].
                  intros k_g _ Hlk_g decl_g body_g Hdecl_g Hbody_g src_vg f_g t_g Heval_g.
                  assert (Heval_g' : exists fg tg,
                    src_eval [] body_g (fuel_sem.Val (ClosFix_v rho' mfix0 idx0)) fg tg).
                  { eapply anf_cvt_cmap_eval;
                      [exact Heval1 | exact Hcvt_e1 | exact Hdis | exact Hdis_cmap
                      | exact Hcons | exact Hcmap | exact Hlk_g | exact Hdecl_g | exact Hbody_g]. }
                  destruct Heval_g' as [fg [tg Heval_g']].
                  assert (src_vg = ClosFix_v rho' mfix0 idx0)
                    by (eapply eval_val_det; [exact Heval_g | exact Heval_g']).
                  subst src_vg. exact Hrel_fix_saved.
                - exact Hcvt_e2.
                - exact Hdis_eletapp.
                - eapply IH2_val; eauto. }
            (* Stage 3: Eletapp + body + env bridge *)
            (* Get body from fix bundle *)
            unfold fix_body in Hbody.
            destruct (nth_error mfix0 idx0) as [d0|] eqn:Hnth_d; [| discriminate].
            injection Hbody as Hbody_eq.
            assert (Hfix_ex : exists d na e_body x_pc C_bc r_bc S_body1 S_body2,
              nth_error mfix0 idx0 = Some d /\
              EAst.dbody d = EAst.tLambda na e_body /\
              find_def f0 Bs = Some (func_tag, [x_pc], C_bc |[ Ehalt r_bc ]|) /\
              anf_cvt_rel' S_body1 e_body (x_pc :: List.rev fnames ++ names) S_body2 C_bc r_bc /\
              Disjoint _ (x_pc |: (FromList fnames :|: FromList names)) S_body1 /\
              ~ x_pc \in (FromList fnames :|: FromList names) /\
              x_pc \in S1 /\ S_body1 \subset S1).
            { eapply anf_fix_rel_exists; eassumption. }
            destruct Hfix_ex
              as (d0' & na0' & e_body & x_pc & C_bc & r_bc & S_body1 & S_body2 &
                  Hnth_d' & Hbody_d' & Hfind_fc & Hcvt_bc &
                  Hdis_xpc & Hfresh_xpc & Hxpc_in_S1 & Hsbody_sub).
            (* d0' = d0, body0 = e_body *)
            assert (d0' = d0) by congruence. subst d0'.
            rewrite Hbody_eq in Hbody_d'. injection Hbody_d' as -> ->.
            set (rho_bc := M.set x_pc v2' (def_funs Bs Bs rho1 rho1)).
            (* Apply IH3 *)
            assert (IH3_full :
              (forall v0 v'0, fuel_sem.Val v = fuel_sem.Val v0 ->
               anf_val_rel' v0 v'0 ->
               preord_exp cenv (anf_bound f3 t3) eq_fuel (i + 1)%nat
                          (Ehalt r_bc, M.set r_bc v'0 rho_bc)
                          (C_bc |[ Ehalt r_bc ]|, rho_bc)) /\
              (fuel_sem.Val v = fuel_sem.OOT ->
               exists c, bstep_fuel cenv rho_bc (C_bc |[ Ehalt r_bc ]|) c eval.OOT tt)).
            { eapply (IH3 rho_bc (x_pc :: List.rev fnames ++ names) C_bc r_bc
                          S_body1 S_body2 (i + 1)).
              - (* well_formed_env *)
                constructor; [exact Hwf_v2 |].
                eapply well_formed_env_make_rec_env;
                  [inv Hwf_fix; assumption | inv Hwf_fix; assumption].
              - (* wellformed body0 *)
                admit.
              - (* env_consistent *) admit.
              - (* cmap_consistent *) admit.
              - (* Disjoint FromList *) admit.
              - (* Disjoint cmap *) admit.
              - (* anf_env_rel' *)
                unfold rho_bc. constructor.
                + exists v2'. split; [rewrite M.gss; reflexivity | exact Hrel_v2].
                + eapply anf_env_rel_weaken.
                  * eapply anf_env_rel_extend_fundefs; eassumption.
                  * (* x_pc ∉ FromList (rev fnames ++ names) *)
                    admit.
              - (* global_env_rel' *)
                unfold rho_bc.
                eapply global_env_rel_set_fresh.
                + eapply global_env_rel_def_funs.
                  * eapply global_env_rel_mono; [exact H10 |].
                    intros kn Hkn. unfold kn_deps_mfix.
                    apply Exists_exists. exists d0. split.
                    -- eapply nth_error_In; exact Hnth_d.
                    -- rewrite Hbody_eq. simpl. exact Hkn.
                  * rewrite (Same_set_all_fun_name Bs).
                    erewrite anf_fix_rel_names by exact H9. exact H5.
                + intro Hcm. destruct H4 as [Hdc]. apply (Hdc x_pc).
                  constructor; [exact Hcm | exact Hxpc_in_S1].
              - exact Hcvt_bc.
              - (* Disjoint Ehalt *)
                admit. }
            destruct IH3_full as [IH3_val _].
            specialize (IH3_val v v' eq_refl Hrel').
            (* Ehalt bstep witness *)
            assert (Hehalt : bstep_fuel cenv (M.set r_bc v' rho_bc)
                               (Ehalt r_bc) (<0> <+> <1> (Ehalt r_bc)) (eval.Res v') (<0> <+> <1> (Ehalt r_bc))).
            { apply BStepf_run. apply BStept_halt. rewrite M.gss. reflexivity. }
            intros v_ek cin_ek cout_ek Hle_ek Hbstep_ek.
            assert (H1_le_Si : to_nat (<0> <+> <1> (Ehalt r_bc)) <= i + 1).
            { unfold_all. simpl. lia. }
            destruct (IH3_val (eval.Res v') (<0> <+> <1> (Ehalt r_bc)) (<0> <+> <1> (Ehalt r_bc))
                        H1_le_Si Hehalt)
              as [v_bc [cin_bc [cout_bc [Hbstep_bc [Hpost_bc Hres_bc]]]]].
            destruct v_bc as [| v_bc_val].
            { exfalso. exact Hres_bc. }
            (* Case split x1 = x2, then env bridge + BStept_letapp *)
            destruct (Pos.eq_dec x1 x2) as [Heq_x1x2 | Hneq_x1x2].
            { (* x1 = x2 *) admit. }
            { (* x1 ≠ x2 *)
              assert (Hrefl : preord_exp cenv eq_fuel eq_fuel i
                        (e_k, M.set x v' rho)
                        (e_k, M.set x v_bc_val (M.set x2 v2' (M.set x1 (Vfun rho1 Bs f0) rho)))).
              { admit. }
              edestruct Hrefl as (v_cont & cin_cont & cout_cont &
                Hbstep_cont & Heq_cont & Hres_cont).
              { exact Hle_ek. }
              { exact Hbstep_ek. }
              do 3 eexists. split.
              { econstructor 2. eapply BStept_letapp.
                - rewrite M.gso by auto. rewrite M.gss. reflexivity.
                - simpl. rewrite M.gss. reflexivity.
                - exact Hfind_fc.
                - reflexivity.
                - exact Hbstep_bc.
                - exact Hbstep_cont. }
              split.
              { unfold anf_bound in Hpost_bc |- *.
                unfold eq_fuel in Heq_cont. simpl in Heq_cont, Hpost_bc.
                destruct Hpost_bc as [Hlb_bc Hub_bc].
                simpl. unfold one, one_i in *; simpl; unfold_all. lia. }
              { exact Hres_cont. } } }
        (* inclusion *)
        { unfold inclusion, comp, eq_fuel, anf_bound.
          intros [[[? ?] ?] ?] [[[? ?] ?] ?].
          intros [[[[? ?] ?] ?] [[[[[? ?] ?] ?] [[? ?] [? ?]]] [? ?]]].
          unfold_all. simpl in *. split; lia. }
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
                    (* v1 also evaluates body b1 in [], by anf_cvt_cmap_eval *)
                    destruct (anf_cvt_cmap_eval _ _ _ _ _ Heval1
                                _ _ _ _ _ kn d1 b1
                                Hcvt_b Hdis Hdis_cmap Hcons Hcmap Hl Hd1 Hd2)
                      as [f1' [t1' Heval_body_v1]].
                    (* eval_val_det: src_v = v1 *)
                    assert (Heq_sv : src_v = v1) by (eapply eval_val_det; eassumption).
                    subst src_v. exact Hrel1.
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
                   - (* x1 ∈ cmap_vars: case split on x1 ∈ FromList vnames *)
                     destruct (In_dec Pos.eq_dec x1 vnames) as [Hin1_vn | Hni1_vn].
                     + (* x1 also in FromList: use anf_env_rel *)
                       apply In_nth_error in Hin1_vn. destruct Hin1_vn as [k1' Hk1'].
                       assert (Heval_b_k : nth_error rho0 k1' = Some v1).
                       { eapply anf_cvt_rel_var_lookup;
                           [exact Heval1 | exact Hcvt_b | exact Hdis | exact Hdis_cmap
                           | exact Hcons | exact Hcmap | exact Hk1']. }
                       destruct (Forall2_nth_error_r _ _ _ _ _ Henv Hk1')
                         as [v_src1' [Hk1_src' [w1' [Hget_w1' Hrel_w1']]]].
                       assert (v_src1' = v1) by congruence. subst v_src1'.
                       exists w1'. split; [exact Hget_w1' | exact Hrel_w1'].
                     + (* x1 not in FromList: use global_env_rel' *)
                       destruct Hin_cm as [kn_x Hlk_x].
                       unfold global_env_rel' in Hglob.
                       assert (Hknx_deps : kn_deps (EAst.tLetIn na0 b0 t0) kn_x).
                       { unfold kn_deps. simpl. apply KernameSet.union_spec.
                         left. eapply anf_cvt_cmap_result_in_deps;
                           [exact Hcvt_b | exact Hlk_x | exact Hdis | exact Hdis_cmap
                           | exact Hni1_vn]. }
                       destruct (Hglob kn_x x1 Hknx_deps Hlk_x)
                         as [dx [bx [avx [Hdx [Hbx [Hgx Hrx]]]]]].
                       exists avx. split; [exact Hgx |].
                       (* anf_val_rel v1 avx: from Hrx + eval_val_det *)
                       assert (Heval_cmap : exists f_c t_c,
                         src_eval [] bx (fuel_sem.Val v1) f_c t_c).
                       { eapply anf_cvt_cmap_eval;
                           [exact Heval1 | exact Hcvt_b | exact Hdis | exact Hdis_cmap
                           | exact Hcons | exact Hcmap | exact Hlk_x | exact Hdx | exact Hbx]. }
                       destruct Heval_cmap as [f_c [t_c Heval_c]].
                       exact (Hrx v1 f_c t_c Heval_c).
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
      (* After inv: anf_Construct gives
         H  : c_tag = dcon_to_tag ...
         H0 : x \in S
         H1 : anf_cvt_rel_args (S \\ [set x]) args vnames S' C0 xs *)
      split.
      + intros v v' Heq Hrel'. injection Heq as <-.
        (* Hrel' : anf_val_rel (Con_v (dcon_of_con ind c) vs0) v' — invert *)
        pose proof Hrel' as Hrel'_saved.
        rename vs0 into vs_src.
        remember (fuel_sem.Con_v (dcon_of_con ind c) vs_src) as cv.
        destruct Hrel'; try discriminate.
        injection Heqcv as Heq_dc Heq_vs. subst.
        match goal with
        | [ HF : Forall2 _ vs_src ?vs_tgt |- _ ] => rename HF into HF2_vs;
            rename vs_tgt into vs'0
        end.
        (* Length equalities *)
        assert (Hlen_xs_args : Datatypes.length xs = Datatypes.length args)
          by (eapply anf_cvt_rel_args_length; eassumption).
        assert (Hlen_vs_src_args : Datatypes.length vs_src = Datatypes.length args)
          by (eapply eval_fuel_many_length; exact Heval_args).
        assert (Hlen_xs_vs'0 : Datatypes.length xs = Datatypes.length vs'0).
        { pose proof (Forall2_length HF2_vs). lia. }
        (* get_list for Econstr_red *)
        destruct (get_list_set_many_exists xs vs'0 rho Hlen_xs_vs'0)
          as [vs_new Hvs_new].
        (* Rewrite context: comp_ctx_f C0 (Econstr_c ...) |[e_k]| = C0 |[Econstr x c_tag xs e_k]| *)
        rewrite <- app_ctx_f_fuse.
        (* Chain: IH_args → Econstr_red → env bridge *)
        eapply preord_exp_post_monotonic.
        2:{ eapply preord_exp_trans; [tci | exact eq_fuel_idemp | | ].
            (* IH_args: args evaluation *)
            2:{ intros m.
                unfold anf_cvt_correct_exps in IH_args.
                eapply IH_args.
                - exact Hwf.
                - eapply wellformed_tConstruct. exact Hwfe.
                - exact Hcons.
                - exact Hcmap.
                - eapply Disjoint_Included_r.
                  eapply Setminus_Included. exact Hdis.
                - eapply Disjoint_Included_r.
                  eapply Setminus_Included. exact Hdis_cmap.
                - exact Henv.
                - eapply global_env_rel_mono; [exact Hglob |].
                  intros k0 Hk0. eapply kn_deps_list_subset_construct. exact Hk0.
                - eassumption.
                - exact HF2_vs.
                - (* Disjoint (occurs_free (Econstr x c_tag xs e_k)) ... *)
                  simpl. rewrite occurs_free_Econstr.
                  eapply Union_Disjoint_l.
                  + eapply Disjoint_Setminus_r. eapply Included_refl.
                  + eapply Setminus_Disjoint_preserv_l.
                    eapply Setminus_Disjoint_preserv_r.
                    eapply Disjoint_Included_r.
                    2: exact Hdis_ek.
                    intros y [[Hy_S Hy_nx] Hy_nS'].
                    split; [split; [exact Hy_S | exact Hy_nS'] | exact Hy_nx]. }
            (* Econstr_red + env bridge *)
            eapply preord_exp_trans; [tci | exact eq_fuel_idemp | | ].
            (* Right step: Econstr reduction *)
            2:{ intros m0. eapply preord_exp_Econstr_red. exact Hvs_new. }
            (* Left step: env bridge
               M.set x (Vconstr c_tag vs'0) rho ≈
               M.set x (Vconstr c_tag vs_new) (set_many xs vs'0 rho) *)
            eapply preord_exp_refl. now eapply eq_fuel_compat.
            intros y Hy v1 Hget.
            destruct (Pos.eq_dec y x) as [Heq|Hneq].
            * (* y = x: constructor value *)
              subst. rewrite M.gss in Hget. inv Hget.
              eexists. split. rewrite M.gss. reflexivity.
              rewrite preord_val_eq. simpl. split; eauto.
              { (* Forall2 (preord_val cenv eq_fuel i) vs'0 vs_new *)
                assert (Hcons_xs : list_consistent (preord_val cenv eq_fuel i) xs vs'0).
                { eapply anf_cvt_args_consistent; try eassumption.
                  - eapply Disjoint_Included_r.
                    eapply Setminus_Included. exact Hdis.
                  - eapply Disjoint_Included_r.
                    eapply Setminus_Included. exact Hdis_cmap.
                  - eapply global_env_rel_mono; [exact Hglob |].
                    intros k0 Hk0. eapply kn_deps_list_subset_construct. exact Hk0. }
                destruct (get_list_set_many_consistent
                            (preord_val cenv eq_fuel i) xs vs'0 rho)
                  as [vs_new' [Hvs_new' HF2_new]].
                - intros x0. eapply preord_val_refl. tci.
                - exact Hlen_xs_vs'0.
                - exact Hcons_xs.
                - rewrite Hvs_new in Hvs_new'. inv Hvs_new'. exact HF2_new. }
            * (* y ≠ x *)
              rewrite M.gso in Hget; auto.
              destruct (in_dec Pos.eq_dec y xs) as [Hyin | Hynin].
              -- (* y ∈ xs: three sub-cases *)
                rewrite M.gso; [ | assumption ].
                edestruct set_many_get_in as [v_y Hget_y]; eauto.
                rewrite Hget_y. eexists. split; [ reflexivity | ].
                destruct (anf_cvt_rel_args_In_range _ _ _ _ _ _ H9 y Hyin)
                  as [Hy_vn | [Hy_S | Hy_cm]].
                ++ (* y ∈ FromList vnames: position tracking + alpha-equiv *)
                   destruct (In_nth_error _ _ Hy_vn) as [n Hn].
                   destruct (In_nth_error _ _ Hyin) as [k Hk].
                   destruct (first_occurrence_exists xs k y Hk) as [k0 [Hle [Hk0 Hfirst]]].
                   destruct (set_many_get_first xs vs'0 rho y k0 Hlen_xs_vs'0 Hk0 Hfirst)
                     as [v0 [Hv0k Hget_v0]].
                   assert (Hvy_eq : v_y = v0) by congruence. subst v0.
                   (* Common source value via var_lookup *)
                   destruct (anf_cvt_rel_args_var_lookup _ _ _ _ _ Heval_args
                               _ _ _ _ _ H9 ltac:(eapply Disjoint_Included_r; [eapply Setminus_Included | exact Hdis])
                               ltac:(eapply Disjoint_Included_r; [eapply Setminus_Included | exact Hdis_cmap])
                               Hcons Hcmap _ _ _ Hk0 Hn)
                     as [v_src [Hvsrc_k0 Hvsrc_n]].
                   unfold anf_env_rel' in Henv.
                   destruct (Forall2_nth_error_r _ _ _ n _ Henv Hn)
                     as [v_env [Hv_env [v_tgt [Hget_tgt Hrel_tgt]]]].
                   rewrite Hvsrc_n in Hv_env. inv Hv_env.
                   rewrite Hget in Hget_tgt. inv Hget_tgt.
                   destruct (Forall2_nth_error_l _ _ _ _ _ HF2_vs Hvsrc_k0)
                     as [v_y' [Hvy' Hrel_vy]].
                   rewrite Hv0k in Hvy'. inv Hvy'.
                   eapply (@anf_cvt_val_alpha_equiv
                     _ _ _ _ eq_fuel eq_fuel tgm cmap cenv
                     eq_fuel_compat (fun _ _ H0 => H0)
                     nat LambdaBox_resource_fuel LambdaBox_resource_trace
                     Σ box_dc Hglob_term func_tag default_tag); eassumption.
                ++ (* y ∈ S \ {x} (fresh): contradiction with Hdis_ek *)
                   exfalso.
                   assert (Hy_not_S' : ~ y \in S').
                   { eapply anf_cvt_rel_args_results_not_in_output; try eassumption.
                     eapply Disjoint_Included_r; [eapply Setminus_Included | exact Hdis].
                     eapply Disjoint_Included_r; [eapply Setminus_Included | exact Hdis_cmap]. }
                   destruct Hdis_ek as [Hdis_ek'].
                   apply (Hdis_ek' y). constructor; [ exact Hy | ].
                   constructor.
                   { inv Hy_S. constructor; assumption. }
                   { intro Heq_yx. apply Hneq. symmetry. inv Heq_yx. reflexivity. }
                ++ (* y ∈ cmap_vars: if also y ∈ FromList vnames, use sub-case A.
                      Otherwise use anf_cvt_cmap_eval via Hglob. *)
                   destruct (@Dec _ _ (Decidable_FromList vnames) y) as [Hy_vn2 | Hni_y].
                   ** (* y ∈ FromList vnames: reuse sub-case A logic *)
                      destruct (In_nth_error _ _ Hy_vn2) as [n Hn].
                      destruct (In_nth_error _ _ Hyin) as [k Hk].
                      destruct (first_occurrence_exists xs k y Hk) as [k0 [Hle [Hk0 Hfirst]]].
                      destruct (set_many_get_first xs vs'0 rho y k0 Hlen_xs_vs'0 Hk0 Hfirst)
                        as [v0 [Hv0k Hget_v0]].
                      assert (Hvy_eq : v_y = v0) by congruence. subst v0.
                      destruct (anf_cvt_rel_args_var_lookup _ _ _ _ _ Heval_args
                                  _ _ _ _ _ H9 ltac:(eapply Disjoint_Included_r; [eapply Setminus_Included | exact Hdis])
                                  ltac:(eapply Disjoint_Included_r; [eapply Setminus_Included | exact Hdis_cmap])
                                  Hcons Hcmap _ _ _ Hk0 Hn)
                        as [v_src [Hvsrc_k0 Hvsrc_n]].
                      unfold anf_env_rel' in Henv.
                      destruct (Forall2_nth_error_r _ _ _ n _ Henv Hn)
                        as [v_env [Hv_env [v_tgt [Hget_tgt Hrel_tgt]]]].
                      rewrite Hvsrc_n in Hv_env. inv Hv_env.
                      rewrite Hget in Hget_tgt. inv Hget_tgt.
                      destruct (Forall2_nth_error_l _ _ _ _ _ HF2_vs Hvsrc_k0)
                        as [v_y' [Hvy' Hrel_vy]].
                      rewrite Hv0k in Hvy'. inv Hvy'.
                      eapply (@anf_cvt_val_alpha_equiv
                        _ _ _ _ eq_fuel eq_fuel tgm cmap cenv
                        eq_fuel_compat (fun _ _ H0 => H0)
                        nat LambdaBox_resource_fuel LambdaBox_resource_trace
                        Σ box_dc Hglob_term func_tag default_tag); eassumption.
                   ** (* y ∉ FromList vnames: cmap approach *)
                      destruct Hy_cm as [kn Hlk_kn].
                      destruct (In_nth_error _ _ Hyin) as [k Hk].
                      destruct (first_occurrence_exists xs k y Hk) as [k0 [Hle [Hk0 Hfirst]]].
                      destruct (set_many_get_first xs vs'0 rho y k0 Hlen_xs_vs'0 Hk0 Hfirst)
                        as [v0 [Hv0k Hget_v0]].
                      assert (Hvy_eq : v_y = v0) by congruence. subst v0.
                      (* Extract individual conversion *)
                      assert (Hk0_range : (k0 < Datatypes.length args)%nat).
                      { rewrite <- Hlen_xs_args. apply nth_error_Some.
                        intro Habs. rewrite Habs in Hk0. discriminate. }
                      destruct (nth_error args k0) as [e_k0|] eqn:Hes_k0;
                        [| exfalso; apply nth_error_None in Hes_k0; lia].
                      destruct (anf_cvt_rel_args_nth_cvt _ _ _ _ _ _ H9 _ _ _ Hes_k0 Hk0)
                        as [Sk0 [Sk0' [Ck0 [Hcvt_k0 Hsub_k0]]]].
                      (* kn ∈ kn_deps_list args *)
                      assert (Hkn_in : kn_deps_list args kn).
                      { unfold kn_deps_list. apply Exists_exists. exists e_k0. split.
                        - eapply nth_error_In. exact Hes_k0.
                        - eapply anf_cvt_cmap_result_in_deps;
                            [ exact Hcvt_k0 | exact Hlk_kn
                            | eapply Disjoint_Included_r; [exact Hsub_k0 |];
                              eapply Disjoint_Included_r; [eapply Setminus_Included | exact Hdis]
                            | eapply Disjoint_Included_r; [exact Hsub_k0 |];
                              eapply Disjoint_Included_r; [eapply Setminus_Included | exact Hdis_cmap]
                            | exact Hni_y ]. }
                      (* Hglob gives declared_constant for kn *)
                      assert (Hkn_construct : KernameSet.In kn (term_global_deps (EAst.tConstruct ind c args))).
                      { eapply kn_deps_list_subset_construct. exact Hkn_in. }
                      destruct (Hglob kn y Hkn_construct Hlk_kn)
                        as [decl [body [anf_v [Hdecl [Hbody [Hget_glob Hrel_glob]]]]]].
                      (* v1 = anf_v from Hglob *)
                      rewrite Hget in Hget_glob. inv Hget_glob.
                      (* Get source value at k0 for v_y *)
                      assert (Hlen_vs_es := eval_fuel_many_length _ _ _ _ _ Heval_args).
                      destruct (nth_error vs_src k0) as [v_src_k0|] eqn:Hvs_k0;
                        [| exfalso; apply nth_error_None in Hvs_k0; lia].
                      destruct (eval_fuel_many_nth _ _ _ _ _ _ _ _ Heval_args Hes_k0 Hvs_k0)
                        as [fk0 [tk0 Heval_k0]].
                      (* anf_cvt_cmap_eval: v_src_k0 evaluates body in [] *)
                      destruct (anf_cvt_cmap_eval _ _ _ _ _ Heval_k0 _ _ _ _ _ kn decl body
                                  Hcvt_k0
                                  ltac:(eapply Disjoint_Included_r; [exact Hsub_k0 |];
                                        eapply Disjoint_Included_r; [eapply Setminus_Included | exact Hdis])
                                  ltac:(eapply Disjoint_Included_r; [exact Hsub_k0 |];
                                        eapply Disjoint_Included_r; [eapply Setminus_Included | exact Hdis_cmap])
                                  Hcons Hcmap Hlk_kn Hdecl Hbody)
                        as [fk0' [tk0' Heval_body_k0]].
                      (* v_y = vs'0[k0] is anf_val_rel to v_src_k0 *)
                      destruct (Forall2_nth_error_l _ _ _ _ _ HF2_vs Hvs_k0)
                        as [v_y' [Hvy' Hrel_vy]].
                      rewrite Hv0k in Hvy'. inv Hvy'.
                      (* v1 = anf_v is related to body eval via Hrel_glob *)
                      (* alpha-equiv: both related to v_src_k0 = body eval *)
                      eapply (@anf_cvt_val_alpha_equiv
                        _ _ _ _ eq_fuel eq_fuel tgm cmap cenv
                        eq_fuel_compat (fun _ _ H0 => H0)
                        nat LambdaBox_resource_fuel LambdaBox_resource_trace
                        Σ box_dc Hglob_term func_tag default_tag).
                      { eapply Hrel_glob. exact Heval_body_k0. }
                      { exact Hrel_vy. }
              -- (* y ∉ xs: set_many doesn't affect y *)
                 eexists. split. rewrite M.gso; auto.
                 rewrite set_many_get_notin; auto. eassumption.
                 eapply preord_val_refl. tci. }
        (* Post inclusion: comp (comp eq_fuel eq_fuel) (anf_bound fs ts) ⊆
           anf_bound (fs + one_i ...) (ts + one_i ...) *)
        unfold inclusion, comp, eq_fuel, anf_bound.
        intros [[[? ?] ?] ?] [[[? ?] ?] ?].
        intros [[[[? ?] ?] ?] [[[[? ?] ?] ?] [? ?]]].
        unfold_all. destruct p. destructAll. simpl in *. lia.
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
