(* Environment-based big-step resource semantics for MetaRocq's EAst.term *)

(** Stdlib *)
From Stdlib Require Import Arith.Arith Lists.List.

(** MetaRocq *)
From MetaRocq.Erasure Require Import EAst EGlobalEnv EPrimitive.
From MetaRocq.Common Require Import Primitive BasicAst Kernames.

(** CertiRocq *)
From CertiRocq.Common Require Import AstCommon.
From CertiRocq.LambdaANF Require Import algebra.
From CertiRocq.LambdaBox_to_LambdaANF Require Import common.

Import ListNotations.

Open Scope alg_scope.


(** * Source values *)

Inductive value :=
| Con_v : dcon -> list value -> value
| Clos_v : list value -> name -> EAst.term -> value
| ClosFix_v : list value -> list (EAst.def EAst.term) -> nat -> value.

Definition env := list value.

Lemma value_ind' (P : value -> Prop) :
  (forall dc vs, Forall P vs -> P (Con_v dc vs)) ->
  (forall vs na e, Forall P vs -> P (Clos_v vs na e)) ->
  (forall vs mfix n, Forall P vs -> P (ClosFix_v vs mfix n)) ->
  (forall v, P v).
Proof.
  intros H1 H2 H3.
  fix IHv 1; intros v. destruct v.
  - eapply H1. induction l.
    constructor.
    constructor. eapply IHv. eassumption.
  - eapply H2. induction l.
    constructor.
    constructor. eapply IHv. eassumption.
  - eapply H3. induction l.
    constructor.
    constructor. eapply IHv. eassumption.
Qed.


(** * Result type *)

Inductive result :=
| Val : value -> result
| OOT : result.


(** * Resource class for EAst.term *)

Class LambdaBox_resource {A} :=
  { HRes :: @resource EAst.term A }.


(** * Utilities *)

Section Util.

  (** Build the recursive environment for a fixpoint.
      Each mutual function gets a ClosFix_v pointing back to the whole mfix. *)
  Definition make_rec_env (mfix : list (EAst.def EAst.term)) (rho : env) : env :=
    let fix make_env_aux (n : nat) :=
        match n with
        | O => rho
        | S n' =>
          let env' := make_env_aux n' in
          (ClosFix_v rho mfix n') :: env'
        end
    in
    make_env_aux (List.length mfix).

  (** Find the branch matching constructor index [c] with [nargs] arguments *)
  Fixpoint find_branch (ind : inductive) (c : nat) (nargs : nat)
           (brs : list (list name * EAst.term)) : option EAst.term :=
    match brs with
    | [] => None
    | (names, body) :: brs' =>
      if Nat.eqb c 0 then
        if Nat.eqb (List.length names) nargs then Some body
        else None (* arity mismatch *)
      else find_branch ind (c - 1) nargs brs'
    end.

  (** Look up the idx-th function body in a fixpoint *)
  Definition fix_body (mfix : list (EAst.def EAst.term)) (idx : nat)
    : option EAst.term :=
    match nth_error mfix idx with
    | Some d => Some d.(dbody)
    | None => None
    end.

End Util.


Section FUEL_SEM.

  Context {trace : Type}
          {Hf : @LambdaBox_resource nat}
          {Ht : @LambdaBox_resource trace}.

  Context (Σ : EAst.global_context).
  Context (box_dc : dcon).


  (** * Big-step resource semantics for EAst.term *)

  Inductive eval_env_step : env -> EAst.term -> result -> nat -> trace -> Prop :=

  (** ** Application: function is a closure *)
  | eval_App_step :
      forall (e1 e2 body : EAst.term) v2 r (na : name) (rho rho' : env)
             f1 f2 f3 t1 t2 t3,
        eval_env_fuel rho e1 (Val (Clos_v rho' na body)) f1 t1 ->
        eval_env_fuel rho e2 (Val v2) f2 t2 ->
        eval_env_fuel (v2 :: rho') body r f3 t3 ->
        eval_env_step rho (EAst.tApp e1 e2) r (f1 <+> f2 <+> f3) (t1 <+> t2 <+> t3)
  | eval_App_step_OOT1 :
      forall (e1 e2 : EAst.term) (rho : env) f1 t1,
        eval_env_fuel rho e1 OOT f1 t1 ->
        eval_env_step rho (EAst.tApp e1 e2) OOT f1 t1
  | eval_App_step_OOT2 :
      forall (e1 e2 : EAst.term) (v : value) (rho : env) f1 f2 t1 t2,
        eval_env_fuel rho e1 (Val v) f1 t1 ->
        eval_env_fuel rho e2 OOT f2 t2 ->
        eval_env_step rho (EAst.tApp e1 e2) OOT (f1 <+> f2) (t1 <+> t2)

  (** ** Application: function is a fix closure *)
  | eval_FixApp_step :
      forall (e1 e2 body : EAst.term) (rho rho' rho'' : env) (idx : nat) (na : name)
             (mfix : list (EAst.def EAst.term)) (v2 : value) r f1 f2 f3 t1 t2 t3,
        eval_env_fuel rho e1 (Val (ClosFix_v rho' mfix idx)) f1 t1 ->
        fix_body mfix idx = Some (EAst.tLambda na body) ->
        make_rec_env mfix rho' = rho'' ->
        eval_env_fuel rho e2 (Val v2) f2 t2 ->
        eval_env_fuel (v2 :: rho'') body r f3 t3 ->
        eval_env_step rho (EAst.tApp e1 e2) r (f1 <+> f2 <+> f3) (t1 <+> t2 <+> t3)

  (** ** Let binding *)
  | eval_LetIn_step :
      forall (na : name) (b t : EAst.term) (v1 : value) (r : result) (rho : env)
             f1 f2 t1 t2,
        eval_env_fuel rho b (Val v1) f1 t1 ->
        eval_env_fuel (v1 :: rho) t r f2 t2 ->
        eval_env_step rho (EAst.tLetIn na b t) r (f1 <+> f2) (t1 <+> t2)
  | eval_LetIn_step_OOT :
      forall (na : name) (b t : EAst.term) (rho : env) f1 t1,
        eval_env_fuel rho b OOT f1 t1 ->
        eval_env_step rho (EAst.tLetIn na b t) OOT f1 t1

  (** ** Constructor *)
  | eval_Construct_step :
      forall (ind : inductive) (c : nat) (args : list EAst.term)
             (vs : list value) (rho : env) (dc : dcon) fs ts,
        dc = dcon_of_con ind c ->
        eval_fuel_many rho args vs fs ts ->
        eval_env_step rho (EAst.tConstruct ind c args) (Val (Con_v dc vs)) fs ts
  | eval_Construct_step_OOT :
      forall (ind : inductive) (c : nat) (args args_done args_rest : list EAst.term)
             (e : EAst.term) (vs : list value) (rho : env) fs f t ts,
        args = args_done ++ e :: args_rest ->
        eval_fuel_many rho args_done vs fs ts ->
        eval_env_fuel rho e OOT f t ->
        eval_env_step rho (EAst.tConstruct ind c args) OOT (fs <+> f) (ts <+> t)

  (** ** Case analysis *)
  | eval_Case_step :
      forall (ind : inductive) (npars : nat) (mch : EAst.term) (brs : list (list name * EAst.term))
             (rho : env) (dc : dcon) (vs : list value) (body : EAst.term)
             (c : nat) (r : result) f1 f2 t1 t2,
        eval_env_fuel rho mch (Val (Con_v dc vs)) f1 t1 ->
        dc = dcon_of_con ind c ->
        find_branch ind c (List.length vs) brs = Some body ->
        eval_env_fuel ((List.rev vs) ++ rho) body r f2 t2 ->
        eval_env_step rho (EAst.tCase (ind, npars) mch brs) r (f1 <+> f2) (t1 <+> t2)
  | eval_Case_step_OOT :
      forall (ind : inductive) (npars : nat) (mch : EAst.term) (brs : list (list name * EAst.term))
             (rho : env) f1 t1,
        eval_env_fuel rho mch OOT f1 t1 ->
        eval_env_step rho (EAst.tCase (ind, npars) mch brs) OOT f1 t1

  (** ** Projection *)
  (* Projections apply to records (single constructor, index 0).
     In the erased language, parameters are stripped (has_cstr_params = false),
     so we index by proj_arg alone (proj_npars = 0). *)
  | eval_Proj_step :
      forall (p : projection) (c : EAst.term) (rho : env)
             (vs : list value) (v : value) f1 t1,
        eval_env_fuel rho c (Val (Con_v (dcon_of_con p.(proj_ind) 0) vs)) f1 t1 ->
        nth_error vs p.(proj_arg) = Some v ->
        eval_env_step rho (EAst.tProj p c) (Val v) f1 t1
  | eval_Proj_step_OOT :
      forall (p : projection) (c : EAst.term) (rho : env) f1 t1,
        eval_env_fuel rho c OOT f1 t1 ->
        eval_env_step rho (EAst.tProj p c) OOT f1 t1

  (** ** Constant (delta reduction) — globals are assumed to be values,
      so the body evaluates with zero fuel. *)
  | eval_Const_step :
      forall (k : kername) (body : EAst.term) (v : value)
             (decl : EAst.constant_body) (rho : env) t,
        declared_constant Σ k decl ->
        decl.(EAst.cst_body) = Some body ->
        eval_env_fuel [] body (Val v) <0> t ->
        eval_env_step rho (EAst.tConst k) (Val v) <0> t

  (** ** Mutual evaluation of argument lists *)
  with eval_fuel_many : env -> list EAst.term -> list value -> nat -> trace -> Prop :=
  | eval_many_nil :
      forall rho,
        eval_fuel_many rho [] [] <0> <0>
  | eval_many_cons :
      forall rho e es v vs f fs t ts,
        eval_env_fuel rho e (Val v) f t ->
        eval_fuel_many rho es vs fs ts ->
        eval_fuel_many rho (e :: es) (v :: vs) (f <+> fs) (t <+> ts)

  (** ** Top-level fuel-indexed evaluation *)
  with eval_env_fuel : env -> EAst.term -> result -> nat -> trace -> Prop :=
  (* Values *)
  | eval_Rel_fuel :
      forall (n : nat) (rho : env) (v : value),
        nth_error rho n = Some v ->
        eval_env_fuel rho (EAst.tRel n) (Val v) <0> <0>
  | eval_Lam_fuel :
      forall (body : EAst.term) (rho : env) (na : name),
        eval_env_fuel rho (EAst.tLambda na body)
                      (Val (Clos_v rho na body)) <0> (one_i (EAst.tLambda na body))
  | eval_Fix_fuel :
      forall (mfix : list (EAst.def EAst.term)) (idx : nat) (rho : env),
        eval_env_fuel rho (EAst.tFix mfix idx)
                      (Val (ClosFix_v rho mfix idx)) <0> (one_i (EAst.tFix mfix idx))
  | eval_Box_fuel :
      forall (rho : env),
        eval_env_fuel rho EAst.tBox
                      (Val (Con_v box_dc []))
                      <0> (one_i EAst.tBox)
  (* OOT *)
  | eval_OOT :
      forall rho (e : EAst.term) f t,
        (f < one_i e)%nat ->
        eval_env_fuel rho e OOT f t
  (* STEP *)
  | eval_step :
      forall rho (e : EAst.term) r (f : nat) t,
        eval_env_step rho e r f t ->
        eval_env_fuel rho e r (f <+> (one_i e)) (t <+> (one_i e)).

  Scheme eval_env_step_ind' := Minimality for eval_env_step Sort Prop
    with eval_fuel_many_ind' := Minimality for eval_fuel_many Sort Prop
    with eval_env_fuel_ind' := Minimality for eval_env_fuel Sort Prop.


  (** * Value determinism *)

  Lemma eval_val_det rho e v1 v2 f1 t1 f2 t2 :
    eval_env_fuel rho e (Val v1) f1 t1 ->
    eval_env_fuel rho e (Val v2) f2 t2 ->
    v1 = v2.
  Proof.
    intros Heval1. revert v2 f2 t2.
    set (Pdet := fun (rho : env) (e : EAst.term) (r : result) (f : nat) (t : trace) =>
      match r with
      | Val v1 => forall v2 f2 t2,
          eval_env_fuel rho e (Val v2) f2 t2 -> v1 = v2
      | OOT => True
      end).
    set (Pmany := fun (rho : env) (es : list EAst.term) (vs : list value)
                      (fs : nat) (ts : trace) =>
      forall vs2 fs2 ts2,
        eval_fuel_many rho es vs2 fs2 ts2 -> vs = vs2).
    enough (Haux : Pdet rho e (Val v1) f1 t1) by exact Haux.
    apply (eval_env_fuel_ind' Pdet Pmany Pdet); try exact Heval1;
    unfold Pdet, Pmany; try solve [intros; exact I].
    (* eval_App_step: e1 → Clos_v *)
    - intros e1 e2 body v2' r na rho0 rho' f0 f2 f3 t0 t2 t3
             _ IH1 _ IH2 _ IH3.
      destruct r as [v_r |]; [| exact I].
      intros v_target f_t t_t Heval2.
      remember (EAst.tApp e1 e2) as ea in Heval2.
      remember (Val v_target) as rv in Heval2.
      destruct Heval2; try discriminate. subst.
      remember (EAst.tApp e1 e2) as ea in H.
      remember (Val v_target) as rv in H.
      destruct H; try discriminate;
        injection Heqea as <- <-; subst.
      + specialize (IH1 _ _ _ H). injection IH1 as <- <- <-.
        specialize (IH2 _ _ _ H0). subst. exact (IH3 _ _ _ H1).
      + specialize (IH1 _ _ _ H). discriminate.
    (* eval_FixApp_step: e1 → ClosFix_v *)
    - intros e1 e2 body rho0 rho' rho'' idx na mfix v2' r
             f0 f2 f3 t0 t2 t3
             _ IH1 Hfb Hmre _ IH2 _ IH3.
      destruct r as [v_r |]; [| exact I].
      intros v_target f_t t_t Heval2.
      remember (EAst.tApp e1 e2) as ea in Heval2.
      remember (Val v_target) as rv in Heval2.
      destruct Heval2; try discriminate. subst.
      remember (EAst.tApp e1 e2) as ea in H.
      remember (Val v_target) as rv in H.
      destruct H; try discriminate.
      + (* App_step from 2nd *)
        injection Heqea as <- <-. subst.
        specialize (IH1 _ _ _ H). discriminate.
      + (* FixApp_step from 2nd *)
        rename H into He1_2. rename H0 into Hfb2.
        rename H2 into He2_2. rename H3 into Hbody2.
        injection Heqea as <- <-. subst.
        specialize (IH1 _ _ _ He1_2). injection IH1 as <- <- <-.
        rewrite Hfb in Hfb2. injection Hfb2 as <- <-.
        specialize (IH2 _ _ _ He2_2). subst. exact (IH3 _ _ _ Hbody2).
    (* eval_LetIn_step *)
    - intros na b t0 v1' r rho0 f0 f2 t2 t3 _ IH1 _ IH2.
      destruct r as [v_r |]; [| exact I].
      intros v_target f_t t_t Heval2.
      remember (EAst.tLetIn na b t0) as ea in Heval2.
      remember (Val v_target) as rv in Heval2.
      destruct Heval2; try discriminate. subst.
      remember (EAst.tLetIn na b t0) as ea in H.
      remember (Val v_target) as rv in H.
      destruct H; try discriminate.
      injection Heqea as <- <- <-. subst.
      specialize (IH1 _ _ _ H). subst. exact (IH2 _ _ _ H0).
    (* eval_Construct_step *)
    - intros ind c args vs dc rho0 fs ts Hdc _ IHmany.
      intros v_target f_t t_t Heval2.
      remember (EAst.tConstruct ind c args) as ea in Heval2.
      remember (Val v_target) as rv in Heval2.
      destruct Heval2; try discriminate. subst.
      remember (EAst.tConstruct ind c args) as ea in H.
      remember (Val v_target) as rv in H.
      destruct H; try discriminate.
      injection Heqea as <- <- <-. injection Heqrv as <-.
      specialize (IHmany _ _ _ H0). congruence.
    (* eval_Case_step *)
    - intros ind npars mch brs rho0 dc vs body c r f0 f2 t0 t2
             _ IH1 Hdc Hfind _ IH2.
      destruct r as [v_r |]; [| exact I].
      intros v_target f_t t_t Heval2.
      remember (EAst.tCase (ind, npars) mch brs) as ea in Heval2.
      remember (Val v_target) as rv in Heval2.
      destruct Heval2; try discriminate. subst.
      remember (EAst.tCase (ind, npars) mch brs) as ea in H.
      remember (Val v_target) as rv in H.
      destruct H; try discriminate.
      assert (ind0 = ind) by congruence.
      assert (mch0 = mch) by congruence.
      assert (brs0 = brs) by congruence.
      subst. clear Heqea.
      specialize (IH1 _ _ _ H).
      assert (vs0 = vs) by congruence. subst vs0.
      assert (c0 = c).
      { assert (Hde : dcon_of_con ind c = dcon_of_con ind c0) by congruence.
        unfold dcon_of_con in Hde. injection Hde as HN.
        now apply Nnat.Nat2N.inj. }
      subst c0. rewrite Hfind in H1. injection H1 as <-.
      exact (IH2 _ _ _ H2).
    (* eval_Proj_step *)
    - intros p c rho0 vs v f0 t0 _ IH Hnth.
      intros v_target f_t t_t Heval2.
      remember (EAst.tProj p c) as ea in Heval2.
      remember (Val v_target) as rv in Heval2.
      destruct Heval2; try discriminate. subst.
      remember (EAst.tProj p c) as ea in H.
      remember (Val v_target) as rv in H.
      destruct H; try discriminate.
      injection Heqea as <- <-. injection Heqrv as <-. subst.
      specialize (IH _ _ _ H). injection IH as <-.
      rewrite Hnth in H0. congruence.
    (* eval_Const_step *)
    - intros k body v decl rho0 t0 Hdecl Hbody _ IH.
      intros v_target f_t t_t Heval2.
      remember (EAst.tConst k) as ea in Heval2.
      remember (Val v_target) as rv in Heval2.
      destruct Heval2; try discriminate. subst.
      remember (EAst.tConst k) as ea in H.
      remember (Val v_target) as rv in H.
      destruct H; try discriminate.
      injection Heqea as <-. injection Heqrv as <-. subst.
      assert (decl = decl0) by (unfold declared_constant in *; congruence).
      subst decl0. rewrite Hbody in H0. injection H0 as <-.
      exact (IH _ _ _ H1).
    (* eval_many_nil *)
    - intros rho0 vs2 fs2 ts2 Hmany2.
      remember (@nil EAst.term) as es in Hmany2.
      destruct Hmany2; [reflexivity | discriminate].
    (* eval_many_cons *)
    - intros rho0 e0 es v vs f0 fs t0 ts _ IH_e _ IH_es.
      intros vs2 fs2 ts2 Hmany2.
      remember (e0 :: es) as ees in Hmany2.
      destruct Hmany2; [discriminate |].
      injection Heqees as <- <-. f_equal.
      + exact (IH_e _ _ _ H).
      + exact (IH_es _ _ _ Hmany2).
    (* eval_Rel_fuel *)
    - intros n rho0 v Hnth v2 f2 t2 Heval2.
      remember (EAst.tRel n) as ea in Heval2.
      remember (Val v2) as rv in Heval2.
      destruct Heval2; try discriminate.
      + injection Heqea as <-. injection Heqrv as <-. congruence.
      + subst. exfalso. remember (EAst.tRel n) as ea in H.
        destruct H; discriminate.
    (* eval_Lam_fuel *)
    - intros body rho0 na v2 f2 t2 Heval2.
      remember (EAst.tLambda na body) as ea in Heval2.
      remember (Val v2) as rv in Heval2.
      destruct Heval2; try discriminate.
      + injection Heqea as <- <-. injection Heqrv as <-. reflexivity.
      + subst. exfalso. remember (EAst.tLambda na body) as ea in H.
        destruct H; discriminate.
    (* eval_Fix_fuel *)
    - intros mfix idx rho0 v2 f2 t2 Heval2.
      remember (EAst.tFix mfix idx) as ea in Heval2.
      remember (Val v2) as rv in Heval2.
      destruct Heval2; try discriminate.
      + injection Heqea as <- <-. injection Heqrv as <-. reflexivity.
      + subst. exfalso. remember (EAst.tFix mfix idx) as ea in H.
        destruct H; discriminate.
    (* eval_Box_fuel *)
    - intros rho0 v2 f2 t2 Heval2.
      remember EAst.tBox as ea in Heval2.
      remember (Val v2) as rv in Heval2.
      destruct Heval2; try discriminate.
      + injection Heqrv as <-. reflexivity.
      + subst. exfalso. remember EAst.tBox as ea in H.
        destruct H; discriminate.
    (* eval_step *)
    - intros rho0 e0 r f0 t0 _ IH. destruct r; [exact IH | exact I].
  Qed.

  Lemma eval_many_det rho es vs1 vs2 fs1 ts1 fs2 ts2 :
    eval_fuel_many rho es vs1 fs1 ts1 ->
    eval_fuel_many rho es vs2 fs2 ts2 ->
    vs1 = vs2.
  Proof.
    intros H1 H2. revert vs2 fs2 ts2 H2. induction H1; intros.
    - remember (@nil EAst.term) as es in H2.
      destruct H2; [reflexivity | discriminate].
    - remember (e :: es) as ees in H2. destruct H2; [discriminate |].
      injection Heqees as <- <-. f_equal.
      + eapply eval_val_det; eassumption.
      + exact (IHeval_fuel_many _ _ _ H2).
  Qed.

End FUEL_SEM.
