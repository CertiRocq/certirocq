(* Require Import CertiCoq. *)
From MetaCoq Require Import Template.Ast.
Require Import Arith List.

Import ListNotations.

(** * VST specs for compiled Coq programs

    The idea is that we want to derive a proof in Verifiable C (VST's separation
    logic) for compiled Coq programs. These specifications will relate the
    original Coq function (rather than L1g abstract syntax) with the compiled C
    code.

    Let [f : A -> B] be a Coq function and [f_in_C : compcert.exp] its
    translation. Then we want:

    forall (a: A) (v : compcert.val),
      {{ rep_A a v }} f_in_C(v)  {{ret. rep_B (f a) ret }}


    The separation logic predicate rep_A describes how Coq values of type A are
    laid out as a C data structure.

    For instance, if for simplicity we assume that Coq values of type [list A]
    will be represented as a null terminated linked lists, then rep_list will,
    very roughly, be

    Fixpoint rep_list (l: list A) (p: compcert.val) : mpred :=
      match l with
      |  h :: l' => rep_A h p ∗ rep_list l' (offset p 4)
         (* i.e. p is a struct pointer and p.head points to a C value in memory
          * that represents h and p.tail is a struct pointer that represents the
          * rest of the list *)
      |  nil => !! (p = null) && emp
    end.

    Then a C program may call f_in_C, and also we may use the above spec when we
    prove it correct in VST!


    To obtain this triple for a compiled program we'll make use of the
    semantic definition of the triple that (again very roughly) says

    {{ pre }} e {{ post }} iff forall h, pre h -> exists v h', eval (e, h) (v, h') /\ post v h'


    That is, to obtain the top-level theorem we need

    forall (a: A) (v : compcert.val) (h : heap),
       rep_A a v h -> exists v' h', eval (app e v, h) (v', h') /\ rep_B (f a) v'


   It should be possible to obtain a similar theorem for L1 -> C light just from
   our compiler correctness theorem.

   The following explains how can we obtain such a theorem for Coq -> L1 to
   eventually compose the two and derive the desired theorem.

  This idea seems to be similar with the one presented in
  https://pdfs.semanticscholar.org/58bb/00b882700d67779871a6208f288f68a0b71c.pdf
  where they verify an HOL -> ML extractor.

 *)


(* Assume we have this *)
Axiom (eval : Ast.term -> Ast.term).

Class Rep (A : Type) :=
  {
    (* An Ast.term represents a Coq value *)
    rep : A -> Ast.term -> Prop
  }.


(* Example 1 : nat *)

Fixpoint nat_rep (n : nat) (v : Ast.term) : Prop :=
  match n with
    | O =>
      match v with
        | Ast.tConstruct (Ast.mkInd "Coq.Init.Datatypes.nat" 0) 0 => True
        | _ => False
      end
    | S n =>
      match v with
        | Ast.tApp (Ast.tConstruct (Ast.mkInd "Coq.Init.Datatypes.nat" 0) 1) [x] =>
          nat_rep n x
        | _ => False
      end
  end.

Instance NatRep : Rep nat := { rep n v := nat_rep n (eval v) }.


(* Example 2 : list *)

Fixpoint list_rep {A : Type} `{Rep A} (l : list A) (v : Ast.term) : Prop :=
  match l with
    | [] =>
      match v with
        | Ast.tConstruct (Ast.mkInd "Coq.Init.Datatypes.list" 0) 0 => True
        | _ => False
      end
    | hd :: tl =>
      match v with
        | Ast.tApp (Ast.tConstruct (Ast.mkInd "Coq.Init.Datatypes.list" 0) 1) [typ; vhd; vtl] =>
          rep hd vhd /\ list_rep tl vtl
        | _ => False
      end
  end.

Instance ListRep {A : Type} `{Rep A} : Rep (list A) := { rep l v := list_rep l (eval v) }.


(* And so on. For inductive types we should be able to generate these instances automatically *)

(* Function types are more interesting *)

Instance ArrowRep {A B : Type} `{Rep A} `{Rep B} : Rep (A -> B) :=
  { rep f t :=
      forall (a : A) (v : Ast.term), rep a v -> rep (f a) (eval (Ast.tApp t [v]))
  }.


Instance ProdRep (B : Type -> Type) `{forall (A : Type) (H : Rep A), Rep (B A)}
: Rep (forall (A : Type), B A) :=
  { rep f t :=
      forall (A : Type) `{Rep A}, rep (f A) (eval (Ast.tApp t [qUnit]))
  }.




(* For every term f we reify we want to generate a proof that [rep f f_reified].
   If we can generate such a thing (can we?) then we could obtain the
   top-level theorem we want. *)

(* What about quantification over computationally irrelevant things? *)

Quote Definition qUnit := tt.

Instance ProdRep (B : Type -> Type) `{forall (A : Type) (H : Rep A), Rep (B A)}
: Rep (forall (A : Type), B A) :=
  { rep f t :=
      forall (A : Type) `{Rep A}, rep (f A) (eval (Ast.tApp t [qUnit]))
  }.

(* This resembles a lot the approach we follow in QuickChick to automatically
   generate correctness proofs for automatically generated generators. We do the
   proof term generation in OCaml, but I think it would be nice to do it in Coq
   and then reflect the terms. *)

Instance ProdRep (B : Type -> Type) `{forall (A : Type) (H : Rep A), Rep (B A)}
: Rep (forall (A : Type), B A) :=
  { rep f t :=
      forall (A : Type) `{Rep A}, rep (f A) (eval (Ast.tApp t [qUnit]))
  }.
