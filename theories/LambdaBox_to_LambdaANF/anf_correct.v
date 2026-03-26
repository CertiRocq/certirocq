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
                       Σ [] body (fuel_sem.Val src_v) f t.


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
  Let anf_val_rel' := anf_val_rel func_tag default_tag tgm cmap Σ.
  Let anf_env_rel' := anf_env_rel func_tag default_tag tgm cmap Σ.
  Let global_env_rel' := global_env_rel func_tag default_tag tgm cmap Σ.

  (* Shorthand for the source evaluation relation.
     Must be explicit about both resource instances since both are
     [@LambdaBox_resource nat] and Coq's instance resolution can't
     distinguish them by type. *)
  Let src_eval := @eval_env_fuel nat LambdaBox_resource_fuel
                                     LambdaBox_resource_trace Σ.


  (** ** Helper: set_many *)

  Fixpoint set_many (xs : list var) (vs : list val) (rho : M.t val) : M.t val :=
    match xs, vs with
    | x :: xs', v :: vs' => M.set x v (set_many xs' vs' rho)
    | _, _ => rho
    end.


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
              nat LambdaBox_resource_fuel LambdaBox_resource_trace Σ
              (fun vs e r f t => anf_cvt_correct_exp_step vs e r f t)
              (fun vs es vs1 f t => anf_cvt_correct_exps vs es vs1 f t)).

    (* ================================================================ *)
    (* P cases: eval_env_step (13 cases)                                *)
    (* ================================================================ *)

    (* eval_App_step *) 1: admit.
    (* eval_App_step_OOT1 *) 1: admit.
    (* eval_App_step_OOT2 *) 1: admit.
    (* eval_FixApp_step *) 1: admit.
    (* eval_LetIn_step *) 1: admit.
    (* eval_LetIn_step_OOT *) 1: admit.
    (* eval_Construct_step *) 1: admit.
    (* eval_Construct_step_OOT *) 1: admit.
    (* eval_Case_step *) 1: admit.
    (* eval_Case_step_OOT *) 1: admit.
    (* eval_Proj_step *) 1: admit.
    (* eval_Proj_step_OOT *) 1: admit.
    (* eval_Const_step *) 1: admit.

    (* ================================================================ *)
    (* P0 cases: eval_fuel_many (2 cases)                               *)
    (* ================================================================ *)

    (* eval_many_nil *) 1: admit.
    (* eval_many_cons *) 1: admit.

    (* ================================================================ *)
    (* P1 cases: eval_env_fuel (6 cases)                                *)
    (* ================================================================ *)

    (* eval_Rel_fuel *) 1: admit.
    (* eval_Lam_fuel *) 1: admit.
    (* eval_Fix_fuel *) 1: admit.
    (* eval_Box_fuel *) 1: admit.
    (* eval_OOT *) 1: admit.
    (* eval_step *)
    - intros rho0 e0 r0 f0 t0 Hstep IH_step.
      unfold anf_cvt_correct_exp, anf_cvt_correct_exp_step in *.
      intros. eapply IH_step; eassumption.

    - exact Heval.
  Admitted.

End Correct.
