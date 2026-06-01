(* Top-level correctness theorems for ANF transformation *)
(* ANF analog of LambdaBoxLocal_to_LambdaANF_toplevel.v (CPS version) *)

From Stdlib Require Import ZArith.ZArith Lists.List micromega.Lia Arith
     Ensembles Relations.Relation_Definitions.
From CertiRocq Require Import Common.AstCommon Common.compM Pipeline_utils.
Require Import MetaRocq.Utils.bytestring.
Require compcert.lib.Maps compcert.lib.Coqlib.

Import ListNotations.

Require Import LambdaBoxLocal.expression LambdaBoxLocal.fuel_sem.

Require Import cps cps_show eval ctx logical_relations LambdaANF.tactics
        List_util algebra alpha_conv functions Ensembles_util
        LambdaBoxLocal_to_LambdaANF LambdaBoxLocal_to_LambdaANF_util
        LambdaBoxLocal_to_LambdaANF_anf_util
        LambdaBoxLocal_to_LambdaANF_anf_corresp LambdaBoxLocal_to_LambdaANF_anf_correct
        identifiers bounds cps_util rename.

Require Import ExtLib.Data.Monads.OptionMonad ExtLib.Structures.Monads.

Import Monad.MonadNotation.

Open Scope monad_scope.


Section Refinement.

  Context (cnstrs : conId_map)
          (dtag : positive) (* default tag *)
          (cenv : ctor_env).

  (* value_ref' : intensional refinement between source and target values.
     For constructors, checks tag correspondence and recursive refinement.
     For closures (both Clos and ClosFix), refinement is trivially True. *)
  Fixpoint value_ref' (v1 : value) (v2 : val) : Prop :=
    let fix Forall2_aux vs1 vs2 :=
        match vs1, vs2 with
        | [], [] => True
        | v1 :: vs1, v2 :: vs2 =>
          value_ref' v1 v2 /\ Forall2_aux vs1 vs2
        | _, _ => False
        end
    in
    match v1, v2 with
    | Con_v c1 vs1, Vconstr c2 vs2 =>
      dcon_to_tag dtag c1 cnstrs = c2 /\ Forall2_aux vs1 vs2
    | Clos_v _ _ _, Vfun _ _ _ => True
    | ClosFix_v _ _ _, Vfun _ _ _ => True
    | _, _ => False
    end.


  Definition value_ref (v1 : value) (v2 : val) : Prop :=
    match v1, v2 with
    | Con_v c1 vs1, Vconstr c2 vs2 =>
      dcon_to_tag dtag c1 cnstrs = c2 /\ Forall2 value_ref' vs1 vs2
    | Clos_v _ _ _, Vfun _ _ _ => True
    | ClosFix_v _ _ _, Vfun _ _ _ => True
    | _, _ => False
    end.

  Lemma value_ref_eq v1 v2 :
    value_ref' v1 v2 <-> value_ref v1 v2.
  Proof.
    induction v1; try easy.

    destruct v2; simpl; try easy.

    revert l0. induction l; intros l'.

    - split; intros [H1 H2]. split; eauto; destruct l'; eauto.
      inv H2. split; eauto.

    - split; intros [H1 H2].

      + split; eauto; destruct l'; inv H2.
        constructor; eauto. eapply IHl. split; eauto.

      + split; eauto. destruct l'; inv H2.
        constructor; eauto. eapply IHl. split; eauto.
  Qed.

  (* Fix resource instance resolution: eval_env_fuel from fuel_sem.v is
     polymorphic in resource instances. We need to pin the fuel to
     LambdaBoxLocal_resource_fuel and trace to LambdaBoxLocal_resource_trace. *)
  Local Definition eval_env_fuel :=
    @fuel_sem.eval_env_fuel nat LambdaBoxLocal_resource_fuel LambdaBoxLocal_resource_trace.

  Definition diverge (v : list value) (e : expression.exp) :=
    forall (c : nat), exists t, eval_env_fuel v e fuel_sem.OOT c t.

  (* ANF refines: if source terminates, target terminates with bounded cost
     and related value. If source diverges, target diverges.
     The constant M accounts for the Ehalt step at the end. *)
  Program Definition refines M (e1 : expression.exp) (e2 : cps.exp) :=
    (* Termination *)
    (forall (v1 : value) (c1 t1 : nat),
        eval_env_fuel [] e1 (Val v1) c1 t1 ->
        exists (v2 : val) (c2 : nat),
          bstep_fuel cenv (M.empty val) e2 c2 (Res v2) tt /\
          (c2 <= t1 + M)%nat /\
          value_ref v1 v2) /\
    (* Divergence *)
    (diverge [] e1 -> eval.diverge cenv (M.empty val) e2).

  Context (prim_map : M.t primitive).
  Context (func_tag kon_tag default_itag : positive)
          (next_id : positive).
  Context (dcon_to_tag_inj :
             forall (tgm : conId_map) (dc dc' : dcon),
               dcon_to_tag dtag dc tgm = dcon_to_tag dtag dc' tgm -> dc = dc').

  (* The relational ANF conversion at the top level.
     Unlike CPS, there is no continuation variable k.
     The result is a context C and result variable r. *)
  Definition anf_rel_top (e : expression.exp) (xs : list var)
             (C : exp_ctx) (r : var) :=
    let S := fun x => (max_list xs 1 + 1 <= x)%positive in
    exists S', LambdaBoxLocal_to_LambdaANF.anf_cvt_rel func_tag dtag S e xs cnstrs S' C r.

  (* Composing anf_val_rel with preord_val gives value_ref.
     For constructors: tag is preserved and recursive values are related.
     For closures: value_ref is trivially True. *)
  Lemma anf_val_comp k v1 v2 v3 :
    LambdaBoxLocal_to_LambdaANF_anf_util.anf_val_rel func_tag dtag cnstrs v1 v2 ->
    preord_val cenv eq_fuel k v2 v3 ->
    value_ref v1 v3.
  Proof.
    revert v2 v3.
    induction v1 using value_ind'; intros v2 v3 Hval Hll; inv Hval.
    - rewrite preord_val_eq in Hll.
      destruct v3; try contradiction. inv Hll.
      simpl. split. reflexivity.

      revert l vs' H2 H1.
      induction H.

      + intros. inv H2. inv H1. constructor.

      + intros. inv H2. inv H1. constructor; eauto.
        eapply value_ref_eq. eauto.

    - rewrite preord_val_eq in Hll.
      destruct v3; try contradiction.
      simpl. eauto.

    - rewrite preord_val_eq in Hll.
      destruct v3; try contradiction.
      simpl. eauto.
  Qed.


  Theorem anf_correct_top e :
    exp_wf 0%N e ->
    exists C r,
      anf_rel_top e [] C r /\
      refines 1 e (C |[ Ehalt r ]|).
  Proof.
    intros Hwf.
    edestruct (LambdaBoxLocal_to_LambdaANF_anf_corresp.anf_rel_exists
                 prim_map func_tag dtag)
      with (xs := @nil var) (m := (max_list (@nil var) 1 + 1)%positive).
    eassumption.

    destructAll.
    eexists. eexists. split.
    eexists. eassumption.

    split.

    (* Termination *)
    - intro; intros.
      pose proof (LambdaBoxLocal_to_LambdaANF_anf_correct.anf_cvt_correct
                   prim_map func_tag kon_tag dtag default_itag cnstrs cenv dcon_to_tag_inj
                   _ _ _ _ _ H0) as Hcorr.
      unfold LambdaBoxLocal_to_LambdaANF_anf_correct.anf_cvt_correct_exp in Hcorr.

      (* Forward-apply Hcorr to all arguments including e_k := Ehalt x0 *)
      specialize (Hcorr (M.empty val) (@nil var) x x0
                        (fun z => (max_list (@nil var) 1 + 1 <= z)%positive) x1 1%nat).

      assert (Hwfe : well_formed_env []) by constructor.
      assert (Hewf : exp_wf (N.of_nat (Datatypes.length (@nil var))) e) by (simpl; exact Hwf).
      assert (Hec : env_consistent [] []) by (intros i j y Hi; destruct i; discriminate).
      assert (Hdis1 : Disjoint var (FromList (@nil var))
                                (fun z => (max_list (@nil var) 1 + 1 <= z)%positive)).
      { constructor. intros ? [? H1 _]. exact H1. }
      assert (Henv : anf_env_rel func_tag dtag cnstrs (@nil var) [] (M.empty val)) by constructor.

      specialize (Hcorr Hwfe Hewf Hec Hdis1 Henv H (Ehalt x0)).

      (* Disjointness: occurs_free (Ehalt x0) = [set x0],
         and x0 is excluded from (S \\ S') \\ [set x0] *)
      assert (Hdis2 : Disjoint var (occurs_free (Ehalt x0))
                                ((fun z => (max_list (@nil var) 1 + 1 <= z)%positive) \\ x1 \\ [set x0])).
      { constructor. intros y Hy.
        destruct Hy as [? Hof Hsm].
        inv Hof.
        destruct Hsm as [_ Habs]. apply Habs. constructor. }

      specialize (Hcorr Hdis2).
      destruct Hcorr as [Hterm Hoot].
      clear Hoot.

      edestruct (LambdaBoxLocal_to_LambdaANF_anf_corresp.anf_val_rel_exists
                   prim_map func_tag dtag) as [v2 Hval].
      eapply (@eval_env_step_preserves_wf nat LambdaBoxLocal_resource_fuel LambdaBoxLocal_resource_trace).
      eassumption. reflexivity. constructor. eassumption.

      specialize (Hterm v1 v2 eq_refl Hval).

      (* Instantiate preord_exp: LHS is (Ehalt x0, M.set x0 v2 (M.empty val))
         which steps in 1 fuel to (Res v2).
         Solve bstep_fuel first to determine cin, then prove to_nat cin <= 1. *)
      edestruct Hterm as [v3 [cin' [cout' [Hstep [Hbound Hres]]]]].
      2: { econstructor 2. econstructor. rewrite M.gss. reflexivity. }
      simpl. unfold algebra.one, one_i. simpl. lia.

      destruct v3; try contradiction.
      destruct cout'.

      do 2 eexists. split; [ | split ].

      + eassumption.
      + (* c2 <= t1 + 1 *)
        unfold LambdaBoxLocal_to_LambdaANF_anf_correct.eq_fuel in *.
        unfold LambdaBoxLocal_to_LambdaANF_anf_correct.anf_bound in Hbound.
        destruct Hbound as [Hlb Hub]. simpl in *. lia.
      + eapply anf_val_comp. eassumption. eassumption.

    (* Divergence *)
    (* BLOCKED: The OOT clause of anf_cvt_correct_exp provides
         exists c, bstep_fuel cenv rho (C|[e_k]|) c OOT tt
       but with NO lower bound on c (all OOT proofs use c = 0).
       The CPS version has (f <= c)%nat, enabling the proof via
       bstep_fuel_OOT_monotonic. Adding this bound to the ANF version
       requires reworking ~15 OOT cases in anf_correct.v to use the
       induction hypothesis instead of trivial eexists 0.

       The fundamental difficulty: in CPS, each source step produces a
       target step (continuation call), so target fuel >= source fuel.
       In ANF, the context C may not add target steps for each source
       step (e.g., when e1 in App_e OOTs, the Eletapp is never reached).
       This means the CPS-style bound f <= c is not directly provable
       for ANF without structural changes to the correctness proof. *)
    - admit.
  Admitted.


  Section Linking.

    Definition link_src (e_lib e_cli : expression.exp) :=
      Let_e nAnon e_lib e_cli.

    (* ANF target linking: just compose the two contexts.
       Unlike CPS, no continuation wrapper (Efun) is needed. *)
    Definition link_trg (C_lib C_cli : exp_ctx) :=
      comp_ctx_f C_lib C_cli.

    (* Separate compilation: library and client are compiled independently,
       then their ANF contexts are composed. The result refines the source
       Let-linking.

       This is a corollary of anf_correct_top applied to Let_e,
       with inversion on the anf_Let constructor to expose the
       decomposition into C_lib and C_cli. *)
    Theorem anf_correct_sep_comp e_lib e_cli :
      exp_wf 0%N e_lib ->
      exp_wf 1%N e_cli ->
      exists C_lib x_lib C_cli r,
        anf_rel_top e_lib [] C_lib x_lib /\
        (exists S_mid S',
           LambdaBoxLocal_to_LambdaANF.anf_cvt_rel func_tag dtag S_mid
             e_cli [x_lib] cnstrs S' C_cli r) /\
        refines 1 (link_src e_lib e_cli)
                  (link_trg C_lib C_cli |[ Ehalt r ]|).
    Proof.
      intros Hwf_lib Hwf_cli.
      assert (Hwf_link : exp_wf 0%N (link_src e_lib e_cli)).
      { unfold link_src. apply let_e_wf.
        - exact Hwf_lib.
        - replace (1 + 0)%N with 1%N by lia. exact Hwf_cli. }

      edestruct (anf_correct_top (link_src e_lib e_cli) Hwf_link)
        as [C [r [Hrel Href]]].
      unfold anf_rel_top in Hrel. destruct Hrel as [S' Hcvt].
      inv Hcvt. fold anf_cvt_rel in *.

      (* anf_Let inversion gives: C = comp_ctx_f C1 C2, r = x2,
         with anf_cvt_rel for e_lib (context C1, result x1)
         and  anf_cvt_rel for e_cli (context C2, result x2). *)
      do 4 eexists. split; [ | split ].
      - (* anf_rel_top e_lib [] C1 x1 *)
        unfold anf_rel_top. eexists. eassumption.
      - (* anf_cvt_rel for e_cli *)
        do 2 eexists. eassumption.
      - (* refines *)
        unfold link_trg. exact Href.
    Qed.

  End Linking.

End Refinement.


Section RefinmentTermination.

  Context (cnstrs : conId_map)
          (dtag : positive) (* default tag *)
          (cenv : ctor_env).

  Program Definition refines_term M (e1 : expression.exp) (e2 : cps.exp) :=
    (* Termination *)
    (forall (v1 : value) (c1 t1 : nat),
        eval_env_fuel [] e1 (Val v1) c1 t1 ->
        exists (v2 : val) (c2 : nat),
          bstep_fuel cenv (M.empty val) e2 c2 (Res v2) tt /\
          (c2 <= t1 + M)%nat /\
          value_ref cnstrs dtag v1 v2).

  Context (prim_map : M.t primitive).
  Context (func_tag kon_tag default_itag : positive)
          (next_id : positive).
  Context (dcon_to_tag_inj :
             forall (tgm : conId_map) (dc dc' : dcon),
               dcon_to_tag dtag dc tgm = dcon_to_tag dtag dc' tgm -> dc = dc').

  Theorem anf_correct_top_termination e :
    exp_wf 0%N e ->
    exists C r,
      anf_rel_top cnstrs dtag func_tag e [] C r /\
      refines_term 1 e (C |[ Ehalt r ]|).
  Proof.
    intros Hwf.
    edestruct (LambdaBoxLocal_to_LambdaANF_anf_corresp.anf_rel_exists
                 prim_map func_tag dtag)
      with (xs := @nil var) (m := (max_list (@nil var) 1 + 1)%positive).
    eassumption.

    destructAll.
    eexists. eexists. split.
    eexists. eassumption.

    (* Termination *)
    { intro; intros.
      pose proof (LambdaBoxLocal_to_LambdaANF_anf_correct.anf_cvt_correct
                   prim_map func_tag kon_tag dtag default_itag cnstrs cenv dcon_to_tag_inj
                   _ _ _ _ _ H0) as Hcorr.
      unfold LambdaBoxLocal_to_LambdaANF_anf_correct.anf_cvt_correct_exp in Hcorr.

      (* Forward-apply Hcorr to all arguments including e_k := Ehalt x0 *)
      specialize (Hcorr (M.empty val) (@nil var) x x0
                        (fun z => (max_list (@nil var) 1 + 1 <= z)%positive) x1 1%nat).

      assert (Hwfe : well_formed_env []) by constructor.
      assert (Hewf : exp_wf (N.of_nat (Datatypes.length (@nil var))) e) by (simpl; exact Hwf).
      assert (Hec : env_consistent [] []) by (intros i j y Hi; destruct i; discriminate).
      assert (Hdis1 : Disjoint var (FromList (@nil var))
                                (fun z => (max_list (@nil var) 1 + 1 <= z)%positive)).
      { constructor. intros ? [? H1 _]. exact H1. }
      assert (Henv : anf_env_rel func_tag dtag cnstrs (@nil var) [] (M.empty val)) by constructor.

      specialize (Hcorr Hwfe Hewf Hec Hdis1 Henv H (Ehalt x0)).

      (* Disjointness: occurs_free (Ehalt x0) = [set x0],
         and x0 is excluded from (S \\ S') \\ [set x0] *)
      assert (Hdis2 : Disjoint var (occurs_free (Ehalt x0))
                                ((fun z => (max_list (@nil var) 1 + 1 <= z)%positive) \\ x1 \\ [set x0])).
      { constructor. intros y Hy.
        destruct Hy as [? Hof Hsm].
        inv Hof.
        destruct Hsm as [_ Habs]. apply Habs. constructor. }

      specialize (Hcorr Hdis2).
      destruct Hcorr as [Hterm Hoot].
      clear Hoot.

      edestruct (LambdaBoxLocal_to_LambdaANF_anf_corresp.anf_val_rel_exists
                   prim_map func_tag dtag) as [v2 Hval].
      eapply (@eval_env_step_preserves_wf nat LambdaBoxLocal_resource_fuel LambdaBoxLocal_resource_trace).
      eassumption. reflexivity. constructor. eassumption.

      specialize (Hterm v1 v2 eq_refl Hval).

      (* Instantiate preord_exp: LHS is (Ehalt x0, M.set x0 v2 (M.empty val))
         which steps in 1 fuel to (Res v2).
         Solve bstep_fuel first to determine cin, then prove to_nat cin <= 1. *)
      edestruct Hterm as [v3 [cin' [cout' [Hstep [Hbound Hres]]]]].
      2: { econstructor 2. econstructor. rewrite M.gss. reflexivity. }
      simpl. unfold algebra.one, one_i. simpl. lia.

      destruct v3; try contradiction.
      destruct cout'.

      do 2 eexists. split; [ | split ].

      + eassumption.
      + (* c2 <= t1 + 1 *)
        unfold LambdaBoxLocal_to_LambdaANF_anf_correct.eq_fuel in *.
        unfold LambdaBoxLocal_to_LambdaANF_anf_correct.anf_bound in Hbound.
        destruct Hbound as [Hlb Hub]. simpl in *. lia.
      + eapply anf_val_comp. eassumption. eassumption. }
  Qed.

  Print Assumptions anf_correct_top_termination.

  Section Linking.

    Theorem anf_correct_sep_comp_term e_lib e_cli :
      exp_wf 0%N e_lib ->
      exp_wf 1%N e_cli ->
      exists C_lib x_lib C_cli r,
        anf_rel_top cnstrs dtag func_tag e_lib [] C_lib x_lib /\
        (exists S_mid S',
           LambdaBoxLocal_to_LambdaANF.anf_cvt_rel func_tag dtag S_mid
             e_cli [x_lib] cnstrs S' C_cli r) /\
        refines_term 1 (link_src e_lib e_cli)
                  (link_trg C_lib C_cli |[ Ehalt r ]|).
    Proof.
      intros Hwf_lib Hwf_cli.
      assert (Hwf_link : exp_wf 0%N (link_src e_lib e_cli)).
      { unfold link_src. apply let_e_wf.
        - exact Hwf_lib.
        - replace (1 + 0)%N with 1%N by lia. exact Hwf_cli. }

      edestruct (anf_correct_top_termination (link_src e_lib e_cli) Hwf_link)
        as [C [r [Hrel Href]]].
      unfold anf_rel_top in Hrel. destruct Hrel as [S' Hcvt].
      inv Hcvt. fold anf_cvt_rel in *.

      (* anf_Let inversion gives: C = comp_ctx_f C1 C2, r = x2,
         with anf_cvt_rel for e_lib (context C1, result x1)
         and  anf_cvt_rel for e_cli (context C2, result x2). *)
      do 4 eexists. split; [ | split ].
      - (* anf_rel_top e_lib [] C1 x1 *)
        unfold anf_rel_top. eexists. eassumption.
      - (* anf_cvt_rel for e_cli *)
        do 2 eexists. eassumption.
      - (* refines *)
        unfold link_trg. exact Href.
    Qed.

    Print Assumptions anf_correct_sep_comp_term.

  End Linking.
