(* Abstract resource algebra to be used by the ANF semantics.
 * Author: Anonymized, 2016
 *)

From Stdlib Require Import Classes.Morphisms Arith NArith.BinNat Relations
     Lia NArith.BinNat.

From CertiRocq Require Import LambdaANF.term LambdaANF.ctx LambdaANF.tactics.


Class resource {I : Type} {A : Type} :=
  { zero : A ;            (* a zero element *)
    one_i  : I -> A ;     (* a bunch of "elementary" non-zero elements *)
    plus : A -> A -> A;   (* addition operator *)

    (* commutativity *)
    plus_comm  : forall x y, plus x y = plus y x;
    (* associativity *)
    plus_assoc : forall x y z, plus (plus x y) z = plus x (plus y z);
    (* identity elem *)
    plus_zero : forall x, plus zero x = x;
    (* name? *)
    plus_inv : forall x y z, plus x z = plus y z -> x = y; }.


Class ordered {I : Type} {A : Type} {Hr : @resource I A} :=
  { lt  : A -> A -> Prop;

    lt_trans   : Transitive lt;
    lt_antisym : Irreflexive lt;

    (* no element below zero *)
    lt_zero     : forall x, ~ lt x zero;
    (* 0 < 1 *)
    zero_one_lt : forall i, lt zero (one_i i);
    (* no element between zero and one *)
    lt_one : forall i x, lt x (one_i i) -> x = zero;

    plus_stable : forall x y z, lt x y <-> lt (plus x z) (plus y z);
    lt_all_dec  : forall x y, lt x y \/ (exists z, x = plus z y);
  }.


Lemma plus_lt I A `{ordered I A} : forall x y z, lt (plus x y) z -> lt x z.
Proof.
  intros.
  destruct (lt_all_dec x z); eauto.
  destructAll.
  rewrite plus_assoc in H0. rewrite (plus_comm z) in H0. rewrite <- plus_assoc in H0.
  rewrite <- (plus_zero z) in H0 at 2. eapply plus_stable in H0.
  eapply lt_zero in H0. contradiction.
Qed.

Lemma not_lt_add I A `{ordered I A} x y :
  ~ lt (plus y x) x.
Proof.
  intro. rewrite algebra.plus_comm in H0. eapply plus_lt in H0.
  eapply lt_antisym. eassumption.
Qed.

Class nat_hom I A `{resource I A} :=
  { to_nat : A -> nat;
    to_nat_add : forall x y, to_nat (plus x y) = to_nat x + to_nat y;
    to_nat_one : forall i, to_nat (one_i i) = 1; }.

(* A resource with all ones being the same *)
Class resource_ones {I : Type} {A : Type} {Hr : @resource I A} :=
  { one_eq : forall i j, one_i i = one_i j  }.


(* Mapping of expressions to a finite type that is used as an index set *)
Inductive fin : Type :=
| One
| Two
| Three
| Four
| Five
| Six
| Seven
| Eight.

Definition exp_to_fin (e: exp) : fin :=
  match e with
  | Econstr _ _ _ _  => One
  | Ecase _ _  => Two
  | Eproj _ _ _ _ _ => Three
  | Eletapp _ _ _ _ _ => Four
  | Efun _ _ => Five
  | Eapp _ _ _ => Four
  | Eprim_val _ _ _ => Six
  | Eprim _ _ _ _ => Seven
  | Ehalt _ => Eight
  end.

Definition exp_ctx_to_fin (C: exp_ctx) : fin :=
  match C with
  | Econstr_c _ _ _ _  => One
  | Ecase_c _ _ _ _ _  => Two
  | Eproj_c _ _ _ _ _ => Three
  | Eletapp_c _ _ _ _ _ => Four
  | Efun1_c _ _ => Five
  | Efun2_c _ _ => Five
  | Eprim_val_c _ _ _ => Six
  | Eprim_c _ _ _ _ => Seven
  | Hole_c => One (* we should never use this function on empty contexts *)
  end.


(* Resource indexed by exprssions *)

Class exp_resource {A} :=
  { HRes :: @resource fin A;
    one := (fun e => @one_i _ _ HRes (exp_to_fin e));
    one_ctx := (fun C => @one_i _ _ HRes (exp_ctx_to_fin C)) }.


(* Fuel resource *)

Class fuel_resource {A} :=
  { HRexp_f :: @exp_resource A;
    HOrd    :: @ordered fin A HRes;
    HOne    :: @resource_ones fin A HRes;
    HNat    :: @nat_hom fin A HRes
  }.

(* Trace resource *)
Class trace_resource {A} :=
  { HRexp_t :: @exp_resource A }.


Declare Scope alg_scope.

(* Notations *)
Notation "a <+> b" := (algebra.plus a b) (at level 72, left associativity) : alg_scope.
Notation "<0>" := algebra.zero : alg_scope.
Notation "<1> x " := (algebra.one (x : exp)) (at level 111, left associativity) : alg_scope.
Notation "a << b" := (algebra.lt a b) (at level 73, left associativity) : alg_scope.
