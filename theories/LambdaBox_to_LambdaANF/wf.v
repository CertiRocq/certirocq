(* Well-formedness predicates for source values and environments *)

(** Stdlib *)
From Stdlib Require Import Lists.List Arith.

(** MetaRocq *)
From MetaRocq.Erasure Require Import EAst EGlobalEnv EWellformed.
From MetaRocq.Common Require Import BasicAst Kernames.

(** CertiRocq *)
From CertiRocq.LambdaBox_to_LambdaANF Require Import fuel_sem.

Import ListNotations.


Section WF.

  Context {efl : EEnvFlags}.
  Context (Σ : global_context).

  (** A term is well-formed in an environment of size [n] *)
  Definition well_formed_in_env (t : EAst.term) (rho : env) :=
    wellformed Σ (List.length rho) t = true.

  (** Well-formedness of source values.
      Closure bodies must be well-formed w.r.t. their captured environment.
      Fix bodies must be lambdas, well-formed in an environment extended
      by all mutual functions. *)
  Inductive well_formed_val : value -> Prop :=
  | Wf_Con :
      forall dc vs,
        Forall well_formed_val vs ->
        well_formed_val (Con_v dc vs)
  | Wf_Clos :
      forall vs na body,
        Forall well_formed_val vs ->
        wellformed Σ (S (List.length vs)) body = true ->
        well_formed_val (Clos_v vs na body)
  | Wf_ClosFix :
      forall vs mfix idx,
        Forall well_formed_val vs ->
        (idx < List.length mfix)%nat ->
        Forall (fun d =>
                  EAst.isLambda d.(EAst.dbody) = true /\
                  wellformed Σ (List.length mfix + List.length vs) d.(EAst.dbody) = true)
               mfix ->
        well_formed_val (ClosFix_v vs mfix idx).

  Definition well_formed_env (rho : env) : Prop :=
    Forall well_formed_val rho.

End WF.
