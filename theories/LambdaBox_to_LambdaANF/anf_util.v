(* Utility definitions and lemmas for ANF correctness proof.
   Defines source value type, value relations between EAst evaluation
   results and LambdaANF values. *)

(** Stdlib *)
From Stdlib Require Import ZArith.ZArith Lists.List Arith Ensembles.

(** MetaRocq *)
From MetaRocq.Erasure Require Import EAst.
From MetaRocq.Common Require Import BasicAst.

(** CompCert *)
From compcert Require lib.Maps.

(** CertiRocq *)
From CertiRocq.LambdaANF Require Import cps ctx Ensembles_util.
From CertiRocq.LambdaBox_to_LambdaANF Require Import common ANF.

Import ListNotations.


(** * Source value type for EAst.term evaluation *)

(** Values produced by environment-based big-step evaluation of EAst.term. *)

Inductive value :=
| Con_v : dcon -> list value -> value
| Clos_v : list value -> name -> EAst.term -> value
| ClosFix_v : list value -> list (EAst.def EAst.term) -> nat -> value.

(** Source environment *)
Definition env := list value.

(** Induction principle for value *)
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


(** * ANF Value Relation *)

Section ANF_Val.

  Context (func_tag default_tag : positive)
          (cnstrs : conId_map)
          (cmap : const_map).

  (** Shorthand for the relational spec, partially applied with tags *)
  Definition anf_cvt_rel' (tgm : conId_map) (cmap : const_map) :=
    ANF.anf_cvt_rel func_tag default_tag tgm cmap.
  Definition anf_cvt_rel_args' (tgm : conId_map) (cmap : const_map) :=
    ANF.anf_cvt_rel_args func_tag default_tag tgm cmap.
  Definition anf_cvt_rel_mfix' (tgm : conId_map) (cmap : const_map) :=
    ANF.anf_cvt_rel_mfix func_tag default_tag tgm cmap.
  Definition anf_cvt_rel_branches' (tgm : conId_map) (cmap : const_map) :=
    ANF.anf_cvt_rel_branches func_tag default_tag tgm cmap.


  (** ** Environment and consistency relations *)

  Definition anf_env_rel' (P : value -> val -> Prop) (vn : list var)
             (vs : list value) (rho : M.t val) :=
    Forall2 (fun v x => exists v', M.get x rho = Some v' /\ P v v') vs vn.

  Definition env_consistent (vn : list var) (rho : list value) : Prop :=
    forall i j x,
      nth_error vn i = Some x ->
      nth_error vn j = Some x ->
      nth_error rho i = nth_error rho j.


  (** ** Fix relation *)

  Inductive anf_fix_rel (fnames : list var) (names : list var)
    : Ensemble var -> list var -> list (EAst.def EAst.term) -> fundefs -> Ensemble var -> Prop :=
  | anf_fix_fnil :
      forall S, anf_fix_rel fnames names S [] [] Fnil S
  | anf_fix_fcons :
      forall S1 S1' S2 S2' S3 fnames' d mfix' C1 r1 na e1 f x Bs,
        d.(EAst.dbody) = EAst.tLambda na e1 ->
        Disjoint _ S1 (FromList fnames :|: FromList names) ->
        x \in S1 ->
        S1' \subset S1 \\ [set x] ->
        S2' \subset S2 ->

        anf_cvt_rel' cnstrs cmap S1' e1 (x :: List.rev fnames ++ names) S2 C1 r1 ->

        anf_fix_rel fnames names S2' fnames' mfix' Bs S3 ->
        anf_fix_rel fnames names S1 (f :: fnames') (d :: mfix')
                    (Fcons f func_tag [x] (C1 |[ Ehalt r1 ]|) Bs) S3.


  (** ** Value relation *)

  Inductive anf_val_rel : value -> val -> Prop :=
  | anf_rel_Con :
      forall vs vs' dc c_tag,
        Forall2 (fun v v' => anf_val_rel v v') vs vs' ->
        dcon_to_tag default_tag dc cnstrs = c_tag ->
        anf_val_rel (Con_v dc vs) (Vconstr c_tag vs')
  | anf_rel_Clos :
      forall vs rho names na x f e C1 r1 S1 S2,
        anf_env_rel' anf_val_rel names vs rho ->

        env_consistent names vs ->

        Disjoint var (x |: (f |: FromList names)) S1 ->

        ~ x \in f |: FromList names ->
        ~ f \in FromList names ->

        anf_cvt_rel' cnstrs cmap S1 e (x :: names) S2 C1 r1 ->
        anf_val_rel (Clos_v vs na e)
                    (Vfun rho (Fcons f func_tag [x] (C1 |[ Ehalt r1 ]|) Fnil) f)
  | anf_rel_ClosFix :
      forall S1 S2 names fnames vs rho mfix Bs n f,
        anf_env_rel' anf_val_rel names vs rho ->

        env_consistent names vs ->
        NoDup fnames ->

        Disjoint _ (FromList names :|: FromList fnames) S1 ->
        Disjoint _ (FromList names) (FromList fnames) ->

        nth_error fnames n = Some f ->

        anf_fix_rel fnames names S1 fnames mfix Bs S2 ->

        anf_val_rel (ClosFix_v vs mfix n) (Vfun rho Bs f).


  Definition anf_env_rel : list var -> list value -> M.t val -> Prop :=
    anf_env_rel' anf_val_rel.

End ANF_Val.
