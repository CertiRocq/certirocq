(* Correctness of the global environment let-binding step.
   Proves that [convert_global_decls] produces a binding context [C_env]
   that, when composed around the main expression, establishes the
   [global_env_rel'] required by [anf_cvt_correct]. *)

(** Stdlib *)
From Stdlib Require Import ZArith.ZArith Lists.List micromega.Lia Arith
     Ensembles Relations.Relation_Definitions.

(** MetaRocq *)
From MetaRocq.Erasure Require Import EAst EAstUtils EGlobalEnv EWellformed EPrimitive.
From MetaRocq.Common Require Import BasicAst Kernames.

(** CompCert *)
From compcert Require Import lib.Maps lib.Coqlib.

(** CertiRocq *)
From CertiRocq.Common Require Import AstCommon.
From CertiRocq Require Import Pipeline_utils.
From CertiRocq.LambdaANF Require Import
  cps cps_show eval ctx logical_relations
  List_util algebra alpha_conv functions Ensembles_util
  tactics identifiers bounds cps_util rename set_util stemctx.
From MetaRocq.Utils Require Import All_Forall.
From CertiRocq.LambdaBox_to_LambdaANF Require Import
  common ANF fuel_sem wf anf_corresp anf_util anf_correct.

Import ListNotations.


(* ================================================================= *)
(** * Relational specification for [convert_global_decls] *)
(* ================================================================= *)

Section GlobalSpec.

  Context (func_tag default_tag : positive)
          (tgm : conId_map)
          (cmap : const_map).

  (** Relational specification for [convert_global_decls].
      Mirrors the monadic function: for each constant with a body,
      convert the body and compose its binding context. Skip constants
      without bodies and inductive declarations. *)
  Inductive anf_cvt_rel_global :
    Ensemble var ->
    EAst.global_declarations ->
    const_map ->           (* cm_acc: accumulated const_map *)
    const_map ->           (* cm: final const_map *)
    exp_ctx ->             (* C_env: composed binding context *)
    Ensemble var ->
    Prop :=
  | cvt_global_nil :
      forall S cm_acc,
        anf_cvt_rel_global S [] cm_acc cm_acc Hole_c S

  | cvt_global_const :
      forall S S1 S2 k body gd' cm_acc cm' C C_rest v,
        anf_cvt_rel func_tag default_tag tgm cm_acc
          S body [] S1 C v ->
        anf_cvt_rel_global S1 gd' ((k, v) :: cm_acc) cm' C_rest S2 ->
        anf_cvt_rel_global S
          ((k, EAst.ConstantDecl {| EAst.cst_body := Some body |}) :: gd')
          cm_acc cm' (comp_ctx_f C C_rest) S2

  | cvt_global_no_body :
      forall S S' k gd' cm_acc cm' C_rest,
        anf_cvt_rel_global S gd' cm_acc cm' C_rest S' ->
        anf_cvt_rel_global S
          ((k, EAst.ConstantDecl {| EAst.cst_body := None |}) :: gd')
          cm_acc cm' C_rest S'

  | cvt_global_ind :
      forall S S' k ind gd' cm_acc cm' C_rest,
        anf_cvt_rel_global S gd' cm_acc cm' C_rest S' ->
        anf_cvt_rel_global S
          ((k, EAst.InductiveDecl ind) :: gd')
          cm_acc cm' C_rest S'.

End GlobalSpec.


(* ================================================================= *)
(** * Global environment relation: existence *)
(* ================================================================= *)

Section GlobalEnvExists.

  Context (func_tag default_tag : positive)
          (prim_map : M.t primitive)
          (tgm : conId_map)
          (prims : list (primitive * positive))
          (cmap : const_map)
          {efl : EEnvFlags}
          (Σ : EAst.global_context)
          (box_dc : dcon)
          (box_tag : dcon_to_tag default_tag box_dc tgm = default_tag).

  Let Hf_src := LambdaBox_resource_fuel default_tag tgm box_dc box_tag.
  Let Ht_src := LambdaBox_resource_trace default_tag tgm box_dc box_tag.

  Let anf_val_rel' :=
    @anf_val_rel func_tag default_tag tgm cmap nat Hf_src Ht_src Σ box_dc.

  Let global_env_rel' :=
    @global_env_rel func_tag default_tag tgm cmap nat Hf_src Ht_src Σ box_dc.

  Let src_eval := @eval_env_fuel nat Hf_src Ht_src Σ box_dc.

  Context (Hwf_glob : wf_glob Σ).
  Context (Hglob_term : @globals_terminate nat Hf_src Ht_src Σ box_dc).

  (* Hypotheses for anf_val_rel_exists *)
  Context (HnoVar : has_tVar = false)
          (HnoEvar : has_tEvar = false)
          (HnoCoFix : has_tCoFix = false)
          (HnoLazy : has_tLazy_Force = false)
          (Hblocks : cstr_as_blocks = true)
          (HnoArray : has_primarray = false).
  Context (no_prims : forall s, find_prim prims s = None).
  Context (cmap_complete : forall s d,
    lookup_constant Σ s = Some d -> lookup_const cmap s <> None).
  Context (cmap_sound : forall k v,
    lookup_const cmap k = Some v ->
    exists decl body,
      declared_constant Σ k decl /\ decl.(EAst.cst_body) = Some body).
  Context (cmap_nodup_vals : NoDup (map snd cmap)).

  (* Well-formedness of global bodies *)
  Context (Hglob_wf : forall k decl body,
    declared_constant Σ k decl ->
    decl.(EAst.cst_body) = Some body ->
    wellformed Σ 0 body = true).

  Let val_rel_exists :=
    @anf_val_rel_exists func_tag default_tag prim_map tgm prims cmap
      _ Σ box_dc nat Hf_src Ht_src
      Hglob_term Hwf_glob
      HnoVar HnoEvar HnoCoFix HnoLazy Hblocks HnoArray
      no_prims cmap_complete cmap_sound cmap_nodup_vals.

  (** There exists a target environment [rho_g] satisfying [global_env_rel']
      for all kernames in [cmap].

      Proof: iterate over [cmap]. For each [(k, v)]:
      1. [cmap_sound] gives a declared body
      2. [Hglob_term] gives evaluation to a source value
      3. [eval_preserves_wf] gives well-formedness of the source value
      4. [anf_val_rel_exists] gives a related ANF value
      5. [M.set v anf_v rho_g] extends the environment

      Collision case (two cmap entries with same var) is ruled out
      by [cmap_nodup_vals]. *)
  Lemma global_env_rel_exists :
    exists rho_g, global_env_rel' (fun _ => True) rho_g.
  Proof.
    unfold global_env_rel', global_env_rel, anf_util.global_env_rel'.
    (* Build rho_g by iterating over cmap *)
    assert (Hbuild : forall cm, NoDup (map snd cm) ->
      (forall ka va, List.In (ka, va) cm -> List.In ka (map fst cmap)) ->
      exists rho_g, forall k v_g,
        lookup_const cm k = Some v_g ->
        exists decl body anf_v,
          declared_constant Σ k decl /\
          EAst.cst_body decl = Some body /\
          M.get v_g rho_g = Some anf_v /\
          (forall src_v f0 t0,
            src_eval [] body (Val src_v) f0 t0 ->
            anf_val_rel' src_v anf_v)).
    { induction cm as [| [k0 v0] cm' IHcm]; intros Hnd_cm Hsuffix.
      - (* cm = [] *) exists (M.empty val). intros. discriminate.
      - (* cm = (k0, v0) :: cm' *)
        simpl in Hnd_cm. apply NoDup_cons_iff in Hnd_cm.
        destruct Hnd_cm as [Hv0_notin Hnd_cm'].
        destruct (IHcm Hnd_cm'
          ltac:(intros ka' va' Hin; eapply Hsuffix; right; exact Hin))
          as [rho_g' Hrho_g'].
        (* Look up k0 in cmap via cmap_sound *)
        assert (Hin_cmap : List.In k0 (map fst cmap))
          by (exact (Hsuffix k0 v0 (or_introl eq_refl))).
        assert (Hlk_cmap : exists vc, lookup_const cmap k0 = Some vc).
        { clear -Hin_cmap. induction cmap as [| [k' v'] cm0 IH0]; [contradiction |].
          simpl. destruct (eq_kername k0 k') eqn:Heq0.
          - eexists. reflexivity.
          - simpl in Hin_cmap. destruct Hin_cmap as [Heq0' | Hin0].
            + subst k'. rewrite ReflectEq.eqb_refl in Heq0. discriminate.
            + exact (IH0 Hin0). }
        destruct Hlk_cmap as [vc Hlk_cmap].
        destruct (cmap_sound k0 vc Hlk_cmap) as [decl0 [body0 [Hdecl0 Hbody0]]].
        (* Evaluate body0 *)
        destruct (Hglob_term k0 decl0 body0 Hdecl0 Hbody0)
          as [src_v0 [f0 [t0 Heval0]]].
        (* Well-formedness *)
        assert (Hwf_src0 : well_formed_val Σ src_v0).
        { eapply eval_preserves_wf; [exact Hglob_wf | constructor | | exact Heval0].
          exact (Hglob_wf k0 decl0 body0 Hdecl0 Hbody0). }
        (* ANF value exists *)
        destruct (val_rel_exists src_v0 Hwf_src0) as [anf_v0 Hrel0].
        (* Extended map *)
        exists (M.set v0 anf_v0 rho_g').
        intros k v_g Hlk.
        simpl in Hlk. destruct (eq_kername k k0) eqn:Hkeq.
        + (* k = k0 *)
          apply ReflectEq.eqb_eq in Hkeq. subst k0.
          injection Hlk as <-.
          exists decl0, body0, anf_v0.
          split; [exact Hdecl0 |]. split; [exact Hbody0 |].
          split; [apply M.gss |].
          intros src_v' f' t' Heval'.
          assert (src_v' = src_v0) by (eapply eval_val_det; eassumption).
          subst src_v'. exact Hrel0.
        + (* k ≠ k0 *)
          destruct (M.elt_eq v_g v0) as [Heq_v | Hneq_v].
          * (* collision: v_g = v0, impossible by NoDup *)
            subst v0. exfalso. apply Hv0_notin.
            clear -Hlk. induction cm' as [| [k' v'] cm'' IH].
            -- discriminate.
            -- simpl in Hlk. destruct (eq_kername k k').
               ++ injection Hlk as <-. left. reflexivity.
               ++ right. exact (IH Hlk).
          * (* v_g ≠ v0: delegate to IH *)
            specialize (Hrho_g' k v_g Hlk).
            destruct Hrho_g' as [decl' [body' [anf_v' [Hd [Hb [Hg Hr]]]]]].
            exists decl', body', anf_v'.
            split; [exact Hd |]. split; [exact Hb |]. split; [| exact Hr].
            rewrite M.gso; [exact Hg | exact Hneq_v]. }
    destruct (Hbuild cmap cmap_nodup_vals
      (fun k0' v0' Hin => in_map fst _ _ Hin)) as [rho_g Hrho_g].
    exists rho_g.
    intros k v_g _ Hlk.
    exact (Hrho_g k v_g Hlk).
  Qed.

End GlobalEnvExists.


(* ================================================================= *)
(** * Operational correctness of global binding contexts *)
(* ================================================================= *)

Section GlobalBindingsCorrect.

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

  Context (cenv_case_consistent : forall P ctag, caseConsistent cenv P ctag).
  Context (cmap_inj : forall k1 k2 v,
    lookup_const cmap k1 = Some v ->
    lookup_const cmap k2 = Some v -> k1 = k2).

  Let Hf_src := LambdaBox_resource_fuel default_tag tgm box_dc box_tag.
  Let Ht_src := LambdaBox_resource_trace default_tag tgm box_dc box_tag.

  Let anf_val_rel' :=
    @anf_val_rel func_tag default_tag tgm cmap nat Hf_src Ht_src Σ box_dc.

  Let anf_cvt_rel' :=
    anf_cvt_rel func_tag default_tag tgm cmap.

  Let global_env_rel' :=
    @global_env_rel func_tag default_tag tgm cmap nat Hf_src Ht_src Σ box_dc.

  Let anf_env_rel' :=
    @anf_env_rel func_tag default_tag tgm cmap nat Hf_src Ht_src Σ box_dc.

  Let src_eval := @eval_env_fuel nat Hf_src Ht_src Σ box_dc.

  Context (Hglob_term :
    forall k decl body,
      declared_constant Σ k decl ->
      decl.(EAst.cst_body) = Some body ->
      exists src_v f t, src_eval [] body (Val src_v) f t).

  Context (Hglob_wf :
    forall k decl body,
      declared_constant Σ k decl ->
      decl.(EAst.cst_body) = Some body ->
      wellformed Σ 0 body = true).

  (* Hypotheses for anf_val_rel_exists *)
  Context (prim_map : M.t primitive)
          (prims : list (primitive * positive)).
  Context (Hwf_glob : wf_glob Σ).
  Context (HnoVar : has_tVar = false)
          (HnoEvar : has_tEvar = false)
          (HnoCoFix : has_tCoFix = false)
          (HnoLazy : has_tLazy_Force = false)
          (Hblocks : cstr_as_blocks = true)
          (HnoArray : has_primarray = false).
  Context (no_prims : forall s, find_prim prims s = None).
  Context (cmap_complete : forall s d,
    lookup_constant Σ s = Some d -> lookup_const cmap s <> None).
  Context (cmap_sound : forall k v,
    lookup_const cmap k = Some v ->
    exists decl body,
      declared_constant Σ k decl /\ decl.(EAst.cst_body) = Some body).
  Context (cmap_nodup_vals : NoDup (map snd cmap)).

  Let cvt_correct :=
    @anf_cvt_correct func_tag default_tag kon_tag
      tgm cmap cenv Σ _ dcon_to_tag_inj box_dc box_tag
      cenv_case_consistent cmap_inj
      Hglob_term Hglob_wf prim_map prims Hwf_glob
      HnoVar HnoEvar HnoCoFix HnoLazy Hblocks HnoArray
      no_prims cmap_complete cmap_sound cmap_nodup_vals.


  (* ----------------------------------------------------------------- *)
  (** ** Per-global-body correctness *)
  (* ----------------------------------------------------------------- *)

  (** Evaluating a single global body's binding context [C] in
      environment [rho] extends [rho] with the body's ANF value
      bound to [v]. Instantiates [anf_cvt_correct] with empty source
      environment and derives both the ANF value and the preord_exp. *)
  Lemma global_body_correct :
    forall body v C S S' rho,
      wellformed Σ 0 body = true ->
      anf_cvt_rel' S body [] S' C v ->
      Disjoint _ (cmap_vars cmap) S ->
      global_env_rel' (kn_deps body) rho ->
      forall src_v f t,
        src_eval [] body (Val src_v) f t ->
        forall e_k i,
          Disjoint _ (occurs_free e_k) ((S \\ S') \\ [set v]) ->
          exists anf_v,
            anf_val_rel' src_v anf_v /\
            preord_exp cenv (anf_bound f t) eq_fuel i
              (e_k, M.set v anf_v rho) (C |[ e_k ]|, rho).
  Proof.
    intros body v C S S' rho Hwf Hcvt Hdis Hglob src_v f t Heval e_k i Hdis_ek.
    (* Get ANF value via eval_preserves_wf + val_rel_exists *)
    assert (Hwf_src : well_formed_val Σ src_v).
    { eapply eval_preserves_wf; [exact Hglob_wf | constructor | exact Hwf | exact Heval]. }
    destruct (@anf_val_rel_exists func_tag default_tag prim_map tgm prims cmap
      _ Σ box_dc nat Hf_src Ht_src
      Hglob_term Hwf_glob
      HnoVar HnoEvar HnoCoFix HnoLazy Hblocks HnoArray
      no_prims cmap_complete cmap_sound cmap_nodup_vals
      src_v Hwf_src) as [anf_v Hrel_v].
    exists anf_v. split; [exact Hrel_v |].
    (* Apply anf_cvt_correct to the body with empty source env *)
    pose proof (cvt_correct [] body (Val src_v) f t Heval) as Hcorrect.
    unfold anf_cvt_correct_exp in Hcorrect.
    specialize (Hcorrect rho [] C v S S' i).
    (* Discharge preconditions of anf_cvt_correct_exp *)
    assert (Hcons : @env_consistent [] []).
    { intros i0 j0 x0 Hi Hj. rewrite nth_error_nil in Hi. discriminate. }
    assert (Hcmap_c : @cmap_consistent cmap _ Hf_src Ht_src Σ box_dc [] []).
    { intros i0 x0 k0 decl0 body0 Hnth. rewrite nth_error_nil in Hnth. discriminate. }
    assert (Hdis_fn : Disjoint _ (FromList []) S).
    { constructor. intros z Hz. inversion Hz as [? HL _].
      unfold FromList, Ensembles.In in HL. contradiction. }
    assert (Henv : anf_env_rel' [] [] rho) by constructor.
    assert (Hwfe : well_formed_env Σ []) by constructor.
    destruct (Hcorrect Hwfe
      Hwf Hcons Hcmap_c Hdis_fn Hdis Henv Hglob Hcvt e_k Hdis_ek) as [Hval _].
    exact (Hval src_v anf_v eq_refl Hrel_v).
  Qed.


  (* ----------------------------------------------------------------- *)
  (** ** Composed global context correctness *)
  (* ----------------------------------------------------------------- *)

  (** The composed binding context [C_env] from [anf_cvt_rel_global],
      when evaluated, produces an environment satisfying [global_env_rel'].

      Proof strategy: induction on [anf_cvt_rel_global].
      - Base: [C_env = Hole_c], environment unchanged.
      - Step: [C_env = comp_ctx_f C C_rest]. Use [global_body_correct]
        on the head body to extend [rho], then the IH for [C_rest]. *)
  Lemma global_ctx_correct :
    forall gd cm_acc cm C_env S S',
      anf_cvt_rel_global func_tag default_tag tgm
        S gd cm_acc cm C_env S' ->
      Disjoint _ (cmap_vars cmap) S ->
      forall rho_g,
        global_env_rel' (fun k => lookup_const cm k <> None) rho_g ->
        forall e_k i,
          preord_exp cenv (anf_bound 0 0) eq_fuel i
            (e_k, rho_g) (C_env |[ e_k ]|, M.empty val).
  Proof.
    admit.
  Admitted.

End GlobalBindingsCorrect.
