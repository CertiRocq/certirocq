(* Environment-based big-step resource semantics for MetaRocq's EAst.term *)

(** Stdlib *)
From Stdlib Require Import Arith.Arith Lists.List.

(** MetaRocq *)
From MetaRocq.Erasure Require Import EAst EPrimitive.
From MetaRocq.Common Require Import Primitive BasicAst Kernames.

(** CertiRocq *)
From CertiRocq.Common Require Import AstCommon.
From CertiRocq.LambdaANF Require Import algebra.
From CertiRocq.LambdaBox_to_LambdaANF Require Import common anf_util.

Import ListNotations.

Open Scope alg_scope.


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


(** * Global environment *)

(** The global environment maps constant names to values.
    We assume all definitions in the global env have been evaluated to values. *)
Definition global_env := list (kername * value).

Fixpoint lookup_global (ge : global_env) (k : kername) : option value :=
  match ge with
  | [] => None
  | (k', v) :: ge' =>
    if eq_kername k k' then Some v else lookup_global ge' k
  end.


Section FUEL_SEM.

  Context {trace : Type}
          {Hf : @LambdaBox_resource nat}
          {Ht : @LambdaBox_resource trace}.

  Context (ge : global_env).


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
  | eval_Proj_step :
      forall (p : projection) (c : EAst.term) (rho : env)
             (dc : dcon) (vs : list value) (v : value) f1 t1,
        eval_env_fuel rho c (Val (Con_v dc vs)) f1 t1 ->
        nth_error vs (p.(proj_npars) + p.(proj_arg)) = Some v ->
        eval_env_step rho (EAst.tProj p c) (Val v) f1 t1
  | eval_Proj_step_OOT :
      forall (p : projection) (c : EAst.term) (rho : env) f1 t1,
        eval_env_fuel rho c OOT f1 t1 ->
        eval_env_step rho (EAst.tProj p c) OOT f1 t1

  (** ** Constant lookup (delta reduction) *)
  | eval_Const_step :
      forall (k : kername) (v : value) (rho : env),
        lookup_global ge k = Some v ->
        eval_env_step rho (EAst.tConst k) (Val v) <0> <0>

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
      forall (rho : env) (box_dc : dcon),
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

End FUEL_SEM.
