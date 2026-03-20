(* Correctness of the ANF transformation from EAst.term to LambdaANF *)

(** Stdlib *)
From Stdlib Require Import ZArith.ZArith Lists.List micromega.Lia Arith
     Ensembles Relations.Relation_Definitions.

(** MetaRocq *)
From MetaRocq.Erasure Require Import EAst EGlobalEnv EWellformed.
From MetaRocq.Common Require Import BasicAst Kernames.

(** CompCert *)
From compcert Require Import lib.Maps lib.Coqlib.

(** CertiRocq *)
From CertiRocq.Common Require Import AstCommon.
From CertiRocq.LambdaANF Require Import
  cps cps_util eval ctx logical_relations
  List_util algebra functions Ensembles_util
  tactics identifiers bounds stemctx set_util.

From CertiRocq.LambdaBox_to_LambdaANF Require Import
  common ANF fuel_sem anf_util wf.

Import ListNotations.
Open Scope list_scope.


(** * ANF Correctness *)

Section Correct.

  Context (func_tag kon_tag default_tag default_itag : positive)
          (cnstrs : conId_map)
          (cmap : const_map)
          (cenv : ctor_env).

  Context (Σ : EAst.global_context).

  (** Term/environment flags for our pipeline:
      no CoFix, Lazy/Force, Var, Evar. *)
  Definition certirocq_prim_flags :=
    {| has_primint := true;
       has_primfloat := true;
       has_primstring := true;
       has_primarray := false |}.

  Definition certirocq_term_flags : ETermFlags :=
    {| has_tBox := true
     ; has_tRel := true
     ; has_tVar := false
     ; has_tEvar := false
     ; has_tLambda := true
     ; has_tLetIn := true
     ; has_tApp := true
     ; has_tConst := true
     ; has_tConstruct := true
     ; has_tCase := true
     ; has_tProj := true
     ; has_tFix := true
     ; has_tCoFix := false
     ; has_tPrim := certirocq_prim_flags
     ; has_tLazy_Force := false
    |}.

  Definition certirocq_env_flags : EEnvFlags :=
    {| has_axioms := false
     ; has_cstr_params := false
     ; term_switches := certirocq_term_flags
     ; cstr_as_blocks := true
    |}.

  Local Existing Instance certirocq_env_flags.

  Context (dcon_to_tag_inj :
    forall tgm dc dc',
      dcon_to_tag default_tag dc tgm = dcon_to_tag default_tag dc' tgm -> dc = dc').


  (** ** Source fuel and trace *)

  Definition fuel_exp (e : EAst.term) : nat :=
    match e with
    | EAst.tLetIn _ _ _ => 0
    | _ => 1
    end.

  Fixpoint max_m_branches (brs : list (list name * EAst.term)) : nat :=
    match brs with
    | [] => 0
    | (names, _) :: brs' => max (List.length names) (max_m_branches brs')
    end.

  Definition anf_trace_exp (e : EAst.term) : nat :=
    match e with
    | EAst.tRel _ => 1
    | EAst.tLambda _ _ => 2
    | EAst.tApp _ _ => 2
    | EAst.tLetIn _ _ _ => 0
    | EAst.tFix _ _ => 2
    | EAst.tConstruct _ _ _ => 2
    | EAst.tCase _ _ brs => 4 + max_m_branches brs
    | EAst.tBox => 2
    | EAst.tConst _ => 1
    | EAst.tProj _ _ => 2
    | EAst.tPrim _ => 2
    | _ => 0
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

  Instance LambdaBox_resource_fuel : @LambdaBox_resource nat :=
    {| HRes := fuel_resource_LambdaBox |}.

  Instance LambdaBox_resource_trace : @LambdaBox_resource nat :=
    {| HRes := trace_resource_LambdaBox |}.


  (** ** LambdaANF fuel and trace *)

  Global Program Instance trace_res_pre : @resource fin unit :=
    { zero := tt;
      one_i fin := tt;
      plus x y := tt; }.
  Next Obligation. destruct x. reflexivity. Qed.
  Next Obligation. destruct x; destruct y. reflexivity. Qed.

  Global Program Instance trace_res_exp : @exp_resource unit :=
    { HRes := trace_res_pre }.

  Global Instance trace_res : @trace_resource unit.
  Proof. econstructor. eapply trace_res_exp. Defined.

  Definition eq_fuel : @PostT nat unit :=
    fun '(e1, r1, f1, t1) '(e2, r2, f2, t2) => f1 = f2.

  Definition anf_bound (f_src t_src : nat) : @PostT nat unit :=
    fun '(e1, r1, f1, t1) '(e2, r2, f2, t2) =>
      (f1 + f_src <= f2)%nat /\
      (f2 <= f1 + t_src)%nat.

  Ltac unfold_all :=
    try unfold zero in *;
    try unfold one_ctx in *;
    try unfold algebra.one in *;
    try unfold one_i in *;
    try unfold algebra.HRes in *;
    try unfold HRexp_f in *; try unfold fuel_res in *; try unfold fuel_res_exp in *; try unfold fuel_res_pre in *;
    try unfold HRexp_t in *; try unfold trace_res in *; try unfold trace_res_exp in *; try unfold trace_res_pre in *.

  Global Instance eq_fuel_compat :
    @Post_properties cenv nat _ unit _ eq_fuel eq_fuel eq_fuel.
  Proof.
    unfold eq_fuel. constructor; try now (intro; intros; intro; intros; unfold_all; simpl; lia).
    - intro; intros. unfold post_base'. unfold_all; simpl. lia.
    - firstorder.
  Qed.

  Lemma eq_fuel_idemp :
    inclusion _ (comp eq_fuel eq_fuel) eq_fuel.
  Proof.
    unfold comp, eq_fuel. intro; intros.
    destruct x as [[[? ?] ?] ?].
    destruct y as [[[? ?] ?] ?]. destructAll.
    destruct x as [[[? ?] ?] ?]. congruence.
  Qed.


  (** ** Shorthands *)

  Definition anf_cvt_rel' := ANF.anf_cvt_rel func_tag default_tag cnstrs cmap.
  Definition anf_cvt_rel_args' := ANF.anf_cvt_rel_args func_tag default_tag cnstrs cmap.
  Definition anf_cvt_rel_mfix' := ANF.anf_cvt_rel_mfix func_tag default_tag cnstrs cmap.
  Definition anf_cvt_rel_branches' := ANF.anf_cvt_rel_branches func_tag default_tag cnstrs cmap.

  Definition anf_val_rel' := anf_util.anf_val_rel func_tag default_tag cnstrs cmap.
  Definition anf_env_rel' := anf_util.anf_env_rel func_tag default_tag cnstrs cmap.
  Definition anf_fix_rel' := anf_util.anf_fix_rel func_tag default_tag cnstrs cmap.


  (** ** Global environment invariant *)

  (** Connects the MetaRocq global context [Σ], the [const_map] produced
      by conversion, and the LambdaANF environment [rho].
      For each constant in [cmap]:
      - it is declared in [Σ] with some body
      - its variable is bound in [rho] to an ANF value
      - that ANF value is related to any source value the body evaluates to *)
  Definition global_env_inv (rho : M.t val) : Prop :=
    forall k v,
      lookup_const cmap k = Some v ->
      exists decl body anf_v,
        declared_constant Σ k decl /\
        decl.(EAst.cst_body) = Some body /\
        M.get v rho = Some anf_v /\
        (forall src_v f t,
           @eval_env_fuel _ LambdaBox_resource_fuel LambdaBox_resource_trace
                          Σ [] body (fuel_sem.Val src_v) f t ->
           anf_val_rel' src_v anf_v).

  (** Variables from [cmap] that appear in [rho] *)
  Definition cmap_vars : Ensemble var :=
    fun v => exists k, lookup_const cmap k = Some v.


  (** ** Helper: set_many *)
  Fixpoint set_many (xs : list var) (vs : list val) (rho : M.t val) : M.t val :=
    match xs, vs with
    | x :: xs', v :: vs' => M.set x v (set_many xs' vs' rho)
    | _, _ => rho
    end.


  (** ** Main correctness statement *)

  (** For an expression that evaluates via [eval_env_fuel]:
      - if it terminates with value [v] and [v] is related to [v'] by [anf_val_rel],
        then the ANF code [C |[ e_k ]|] is related to [e_k{x := v'}] by [preord_exp]
      - if it diverges, the ANF code diverges too *)
  Definition anf_cvt_correct_exp
             (vs : fuel_sem.env) (e : EAst.term) (r : fuel_sem.result) (f t : nat) :=
    forall rho vnames C x S S' i,
      wf.well_formed_env Σ vs ->
      wellformed Σ (List.length vnames) e = true ->

      anf_util.env_consistent vnames vs ->

      Disjoint _ (FromList vnames) S ->
      Disjoint _ cmap_vars S ->

      anf_env_rel' vnames vs rho ->
      global_env_inv rho ->

      anf_cvt_rel' S e vnames S' C x ->

      forall e_k,
        Disjoint _ (occurs_free e_k) ((S \\ S') \\ [set x]) ->

        (* Source terminates *)
        (forall v v', r = fuel_sem.Val v -> anf_val_rel' v v' ->
         preord_exp cenv (anf_bound f t) eq_fuel i
                    (e_k, M.set x v' rho)
                    (C |[ e_k ]|, rho)) /\
        (* Source diverges *)
        (r = fuel_sem.OOT ->
         exists c, bstep_fuel cenv rho (C |[ e_k ]|) c eval.OOT tt).


  Definition anf_cvt_correct_exp_step
             (vs : fuel_sem.env) (e : EAst.term) (r : fuel_sem.result) (f t : nat) :=
    forall rho vnames C x S S' i,
      wf.well_formed_env Σ vs ->
      wellformed Σ (List.length vnames) e = true ->

      anf_util.env_consistent vnames vs ->

      Disjoint _ (FromList vnames) S ->
      Disjoint _ cmap_vars S ->

      anf_env_rel' vnames vs rho ->
      global_env_inv rho ->

      anf_cvt_rel' S e vnames S' C x ->

      forall e_k,
        Disjoint _ (occurs_free e_k) ((S \\ S') \\ [set x]) ->

        (* Source terminates *)
        (forall v v', r = fuel_sem.Val v -> anf_val_rel' v v' ->
                      preord_exp cenv
                                 (anf_bound (f <+> @one_i _ _ fuel_resource_LambdaBox e)
                                            (t <+> @one_i _ _ trace_resource_LambdaBox e))
                                 eq_fuel i
                                 (e_k, M.set x v' rho)
                                 (C |[ e_k ]|, rho)) /\
        (* Source diverges *)
        (r = fuel_sem.OOT ->
         exists c, bstep_fuel cenv rho (C |[ e_k ]|) c eval.OOT tt).


  Definition anf_cvt_correct_args
             (vs : fuel_sem.env) (args : list EAst.term)
             (vals : list value) (f t : nat) :=
    forall rho vnames C xs S S' i,
      wf.well_formed_env Σ vs ->
      Forall (fun t => wellformed Σ (List.length vnames) t = true) args ->

      anf_util.env_consistent vnames vs ->

      Disjoint _ (FromList vnames) S ->
      Disjoint _ cmap_vars S ->

      anf_env_rel' vnames vs rho ->
      global_env_inv rho ->

      anf_cvt_rel_args' S args vnames S' C xs ->

      NoDup xs ->

      forall e_k,
        Disjoint _ (occurs_free e_k) ((S \\ S') \\ FromList xs) ->

        (forall vs',
           Forall2 anf_val_rel' vals vs' ->
           preord_exp cenv (anf_bound f t) eq_fuel i
                      (e_k, set_many xs vs' rho)
                      (C |[ e_k ]|, rho)) /\
        True. (* OOT case omitted for now *)


  (** ** Main correctness theorem *)

  Lemma anf_cvt_correct :
    forall vs e r f t,
      @eval_env_fuel _ LambdaBox_resource_fuel LambdaBox_resource_trace Σ vs e r f t ->
      anf_cvt_correct_exp vs e r f t.
  Proof.
    intros vs e r f t Heval.
    eapply (eval_env_fuel_ind' (Hf := LambdaBox_resource_fuel) (Ht := LambdaBox_resource_trace)) with
      (P := anf_cvt_correct_exp_step)
      (P0 := anf_cvt_correct_args)
      (P1 := anf_cvt_correct_exp);
      try eassumption.

    (* Each case of the mutual induction follows. *)

    (** ** eval_env_step cases (P = anf_cvt_correct_exp_step) *)

    - (* eval_App_step: closure application *)
      admit.

    - (* eval_App_step_OOT1: e1 diverges *)
      intros e1' e2' rho0 f0 t0 Hoot IH_oot.
      unfold anf_cvt_correct_exp_step.
      intros rho vnames C x S S' i Hwf Hwfe Hcons Hdis Hdis_cm Henv Hginv Hcvt e_k Hdis_ek.
      split; [intros; congruence | intros _; eexists 0%nat; constructor 1; unfold algebra.one; simpl; lia].

    - (* eval_App_step_OOT2: e2 diverges *)
      intros e1' e2' v0 rho0 f1' f2' t1' t2' Heval1 IH1 Hoot2 IH2.
      unfold anf_cvt_correct_exp_step.
      intros rho vnames C x S S' i Hwf Hwfe Hcons Hdis Hdis_cm Henv Hginv Hcvt e_k Hdis_ek.
      split; [intros; congruence | intros _; eexists 0%nat; constructor 1; unfold algebra.one; simpl; lia].

    - (* eval_FixApp_step: fix application *)
      admit.

    - (* eval_LetIn_step *)
      admit.

    - (* eval_LetIn_step_OOT: binding diverges *)
      intros na0 b0 t0 rho0 f0 t0' Hoot IH_oot.
      unfold anf_cvt_correct_exp_step.
      intros rho vnames C x S S' i Hwf Hwfe Hcons Hdis Hdis_cm Henv Hginv Hcvt e_k Hdis_ek.
      split; [intros; congruence | intros _; eexists 0%nat; constructor 1; unfold algebra.one; simpl; lia].

    - (* eval_Construct_step *)
      admit.

    - (* eval_Construct_step_OOT: some constructor arg diverges *)
      intros ind0 c0 args0 args_done args_rest e0 vs0 rho0 fs0 f0 t0 ts0
             Hargs Hmany IH_many Hoot IH_oot.
      unfold anf_cvt_correct_exp_step.
      intros rho vnames C x S S' i Hwf Hwfe Hcons Hdis Hdis_cm Henv Hginv Hcvt e_k Hdis_ek.
      split; [intros; congruence | intros _; eexists 0%nat; constructor 1; unfold algebra.one; simpl; lia].

    - (* eval_Case_step *)
      admit.

    - (* eval_Case_step_OOT: scrutinee diverges *)
      intros ind0 npars0 mch0 brs0 rho0 f0 t0 Hoot IH_oot.
      unfold anf_cvt_correct_exp_step.
      intros rho vnames C x S S' i Hwf Hwfe Hcons Hdis Hdis_cm Henv Hginv Hcvt e_k Hdis_ek.
      split; [intros; congruence | intros _; eexists 0%nat; constructor 1; unfold algebra.one; simpl; lia].

    - (* eval_Proj_step — NEW *)
      admit.

    - (* eval_Proj_step_OOT: scrutinee diverges — NEW *)
      intros p0 c0 rho0 f0 t0 Hoot IH_oot.
      unfold anf_cvt_correct_exp_step.
      intros rho vnames C x S S' i Hwf Hwfe Hcons Hdis Hdis_cm Henv Hginv Hcvt e_k Hdis_ek.
      split; [intros; congruence | intros _; eexists 0%nat; constructor 1; unfold algebra.one; simpl; lia].

    - (* eval_Const_step — NEW:
         Source: declared_constant Σ k decl, body = Some body, eval [] body r f t
         ANF: anf_Const says lookup_const cmap k = Some v, C = Hole_c, S' = S
         IH: anf_cvt_correct_exp [] body r f t
         NOTE: This case has a fundamental cost-model mismatch for OOT —
         the source pays fuel for delta reduction but the ANF has the value
         precomputed in rho. Needs design decision. *)
      admit.

    (** ** eval_fuel_many cases (P0 = anf_cvt_correct_args) *)

    - (* eval_many_nil *)
      admit.

    - (* eval_many_cons *)
      admit.

    (** ** eval_env_fuel cases (P1 = anf_cvt_correct_exp) *)

    - (* eval_Rel_fuel: tRel n — variable lookup *)
      intros n vs1 v Hnth.
      unfold anf_cvt_correct_exp.
      intros rho vnames C x S S' i Hwf Hwfe Hcons Hdis Hdis_cm Henv Hginv Hcvt e_k Hdis_ek.
      inv Hcvt.
      simpl.
      split.
      + (* Termination: C = Hole_c, x = v0, S' = S *)
        intros v0 v' Heq Hrel. inv Heq.
        change (preord_exp cenv (anf_bound 0 0) eq_fuel i (e_k, M.set x v' rho) (e_k, rho)).
        eapply preord_exp_post_monotonic with (P1 := eq_fuel).
        { unfold inclusion, eq_fuel, anf_bound.
          intros [[[? ?] ?] ?] [[[? ?] ?] ?]. intros. subst.
          unfold_all. simpl in *. lia. }
        eapply preord_exp_refl. now eapply eq_fuel_compat.
        intros y Hy.
        destruct (Pos.eq_dec y x) as [Heq | Hneq].
        * subst. intros v1 Hget. rewrite M.gss in Hget. inv Hget.
          admit. (* needs anf_env_rel_nth_error + anf_cvt_val_alpha_equiv *)
        * intros v1 Hget. rewrite M.gso in Hget; auto.
          eexists. split. eassumption.
          eapply preord_val_refl. tci.
      + intros Habs. congruence.

    - (* eval_Lam_fuel: tLambda na body → Clos_v vs na body
         ANF: Efun (Fcons f func_tag [x1] (C1|[Ehalt r1]|) Fnil) e_k
         After Efun_red, f ↦ Vfun rho (Fcons f ...) f in rho.
         Need preord_val v' (Vfun ...) via anf_rel_Clos + alpha-equiv. *)
      intros body0 vs1 na0.
      unfold anf_cvt_correct_exp.
      intros rho vnames C x S S' i Hwf Hwfe Hcons Hdis Hdis_cm Henv Hginv Hcvt e_k Hdis_ek.
      inv Hcvt. simpl.
      split.
      + intros v0 v' Heq Hrel. inv Heq.
        admit. (* needs preord_exp chain: post_monotonic + trans via Efun step
                  + env bridging between M.set x v' rho and def_funs B B rho rho
                  + alpha-equiv for the x ↦ v' vs x ↦ Vfun rho B x case *)
      + intros Habs. congruence.

    - (* eval_Fix_fuel: tFix mfix idx → ClosFix_v vs mfix idx
         ANF: Efun fdefs e_k
         After Efun_red, f ↦ Vfun rho fdefs f in rho.
         Need preord_val v' (Vfun ...) via anf_rel_ClosFix + alpha-equiv. *)
      admit.

    - (* eval_Box_fuel: tBox → Con_v box_dc []
         ANF: Econstr x default_tag [] e_k
         After Econstr_red, x ↦ Vconstr default_tag [] in rho.
         Need preord_val v' (Vconstr default_tag []) via anf_rel_Con + alpha-equiv. *)
      admit.

    - (* eval_OOT *)
      intros vs1 e1 f1 t1 Hlt.
      unfold anf_cvt_correct_exp.
      intros rho vnames C x S S' i Hwf Hwfe Hcons Hdis Hdis_cm Henv Hginv Hcvt e_k Hdis_ek.
      split.
      + intros v v' Heq _. congruence.
      + intros _.
        eexists 0%nat. constructor 1. unfold algebra.one. simpl. lia.

    - (* eval_step: forwards to IH from eval_env_step.
         P1 is applied to (vs, e, r, f+one_i e, t+one_i e).
         IH : anf_cvt_correct_exp_step vs e r f t, which internally uses
         anf_bound (f + one_i e) (t + one_i e). So IH is exactly the goal. *)
      intros vs1 e1 r1 f1 t1 Hstep IH.
      intros.
      cbv beta iota delta [HRes LambdaBox_resource_fuel LambdaBox_resource_trace
                            one_i plus fuel_resource_LambdaBox trace_resource_LambdaBox] in *.
      assumption.

  Admitted.

End Correct.
