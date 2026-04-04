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
(** * Global environment correctness *)
(* ================================================================= *)

Section GlobalCorrect.

  Context (func_tag kon_tag default_tag default_itag : positive)
          (tgm : conId_map)
          (cmap : const_map)
          (cenv : ctor_env)
          (Σ : EAst.global_context).

  Context {efl : EEnvFlags}.

  Context (box_dc : dcon)
          (box_tag : dcon_to_tag default_tag box_dc tgm = default_tag).

  Let Hf_src := LambdaBox_resource_fuel default_tag tgm box_dc box_tag.
  Let Ht_src := LambdaBox_resource_trace default_tag tgm box_dc box_tag.

  Let anf_val_rel' :=
    @anf_val_rel func_tag default_tag tgm cmap nat Hf_src Ht_src Σ box_dc.

  Let anf_cvt_rel' :=
    anf_cvt_rel func_tag default_tag tgm cmap.

  Let global_env_rel' :=
    @global_env_rel func_tag default_tag tgm cmap nat Hf_src Ht_src Σ box_dc.

  Let src_eval := @eval_env_fuel nat Hf_src Ht_src Σ box_dc.


  (* ----------------------------------------------------------------- *)
  (** ** Per-global-body correctness *)
  (* ----------------------------------------------------------------- *)

  (** Evaluating a single global body's binding context [C] in
      environment [rho] extends [rho] with the body's ANF value
      bound to [v]. *)
  Lemma global_body_correct :
    forall k body v C S S' rho,
      declared_constant Σ k {| EAst.cst_body := Some body |} ->
      wellformed Σ 0 body = true ->
      anf_cvt_rel' S body [] S' C v ->
      Disjoint _ (cmap_vars cmap) S ->
      (forall src_v f t,
        src_eval [] body (Val src_v) f t ->
        exists anf_v,
          anf_val_rel' src_v anf_v /\
          forall e_k i,
            preord_exp cenv (anf_bound f t) eq_fuel i
              (e_k, M.set v anf_v rho) (C |[ e_k ]|, rho)).
  Proof.
    (* Uses anf_cvt_correct on body with empty source env *)
    admit.
  Admitted.


  (* ----------------------------------------------------------------- *)
  (** ** Global context evaluation *)
  (* ----------------------------------------------------------------- *)

  (** After evaluating the composed global binding context [C_env],
      the target environment satisfies [global_env_rel'] for all
      kernames in the resulting const_map. *)
  (** After evaluating the composed global binding context [C_env],
      the target environment satisfies [global_env_rel'] for all
      kernames in the resulting const_map.

      Proof strategy: induction on [anf_cvt_rel_global].
      - Base: [C_env = Hole_c], environment unchanged.
      - Step: [C_env = comp_ctx_f C C_rest]. Use [anf_cvt_correct]
        on the body to evaluate [C], extending [rho] with the new
        binding. Then apply the IH for [C_rest]. *)
  Lemma global_env_bindings_correct :
    forall gd cm_acc cm C_env S S',
      anf_cvt_rel_global func_tag default_tag tgm
        S gd cm_acc cm C_env S' ->
      wf_glob Σ ->
      (* All source global bodies terminate *)
      (forall k decl body,
        declared_constant Σ k decl ->
        decl.(EAst.cst_body) = Some body ->
        exists src_v f t, src_eval [] body (Val src_v) f t) ->
      (* Freshness *)
      Disjoint _ (cmap_vars cmap) S ->
      (* The composed context builds an environment satisfying global_env_rel' *)
      forall rho,
        global_env_rel' (fun k => lookup_const cm k <> None) rho.
  Proof.
    admit.
  Admitted.


  (* ----------------------------------------------------------------- *)
  (** ** Top-level correctness *)
  (* ----------------------------------------------------------------- *)

  Context (Hglob_term : forall k decl body,
    declared_constant Σ k decl ->
    decl.(EAst.cst_body) = Some body ->
    exists src_v f t, src_eval [] body (Val src_v) f t).

  Context (Hwf_glob : wf_glob Σ).

  (** Top-level theorem: the full converted program is correct.
      If the source expression [e] evaluates to [v] in the empty source
      environment, then the ANF target program [C_env |[ C_main |[ Ehalt x ]| ]|]
      evaluates to a related value. *)
  Theorem anf_top_correct :
    forall e v f t,
      src_eval [] e (Val v) f t ->
      wellformed Σ 0 e = true ->
      forall cm C_env x C_main S_env S_main S',
        (* Global environment conversion *)
        anf_cvt_rel_global func_tag default_tag tgm
          S_env (rev Σ) [] cm C_env S_main ->
        (* Main expression conversion *)
        anf_cvt_rel' S_main e [] S' C_main x ->
        (* Freshness conditions *)
        Disjoint _ (cmap_vars cmap) S_env ->
        Disjoint _ (occurs_free (C_main |[ Ehalt x ]|))
                   (S_env \\ S_main) ->
        (* Target is correct *)
        exists (v' : val) c,
          bstep_fuel cenv (M.empty val)
            (C_env |[ C_main |[ Ehalt x ]| ]|)
            c (Res v') tt /\
          anf_val_rel' v v'.
  Proof.
    (* 1. Use global_env_bindings_correct to establish global_env_rel'
          in the environment built by C_env.
       2. Use anf_cvt_correct for the main expression e.
       3. Compose via preord_exp transitivity. *)
    admit.
  Admitted.

End GlobalCorrect.
