From Stdlib Require Import ZArith.ZArith.
From Stdlib Require Import ZArith.Znumtheory.
From Stdlib Require Import Lists.List.
From Stdlib Require Import Bool.Bool.
Require Maps.
From Stdlib Require funind.Recdef.
Import Nnat.
From Stdlib Require Structures.Orders.
Import RelationClasses.

Require Import term.

Definition class := positive.
Definition noclass : class := 1%positive.

Definition formal := positive.  (* formal-parameter location *)
Inductive taginfo : Type :=
| Tag_record: N -> taginfo (* tag N in header, before record *)
| Tag_const: N -> taginfo (* int N carrying no record fields *)
| Tag_lobit: taginfo (* tag-boxing of a 31- or 63-bit integer *)
| Tag_floats: taginfo (* record of all floats *)
| Tag_string: taginfo (* string value *)
(* | Tag_stackrecord: taginfo  (* stack-allocated record, holds free vars of closure *) *)
| Tag_fun: forall (returncont: bool) (* true if this is a "return" continuation *)
                         (formals: list formal),   (* list of formal-parameter locations/regs *)
                         taginfo.

Module TagInfo <: Orders.UsualOrderedType.
 Definition t := (class * taginfo)%type.
 Definition eq := @eq t.
 Definition eq_equiv : Equivalence eq := eq_equivalence.

 Definition lexi {A}{B} (f: A -> A -> comparison) a a' (g: B -> B -> comparison) b b' : comparison :=
    match f a a' with Lt => Lt | Eq => g b b' | Gt => Gt end.

 Fixpoint compare_list {A} (f: A -> A -> comparison) (al bl: list A) : comparison :=
   match al, bl with
     | a::al', b::bl' => lexi f a b (compare_list f) al' bl'
     | nil, _::_ => Lt
     | _::_, nil => Gt
     | nil, nil => Eq
   end.

 Fixpoint compare_pair {A}{B} (f: A -> A -> comparison) (g: B -> B -> comparison)
                     (x: A*B) (y: A*B) : comparison :=
  lexi f (fst x) (fst y) g (snd x) (snd y).

Definition compare_bool (x y: bool) : comparison :=
 match x, y with
 | false, false => Eq
 | false, true => Lt
 | true, false => Gt
 | true, true => Eq
 end.

 Fixpoint compare (x y : t) : comparison :=
 match x, y with
 | (n,x1), (n', y1) =>
 match Pos.compare n n' with
 | Lt => Lt | Gt => Gt
 | Eq => match x1,y1 with
    | Tag_record n, Tag_record n' => N.compare n n'
    | Tag_record _, _ => Lt
    | _, Tag_record _ => Gt
    | Tag_const n, Tag_const n' => N.compare n n'
    | Tag_const _,  _ => Lt
    | _, Tag_const _ => Gt
    | Tag_lobit, Tag_lobit => Eq
    | Tag_lobit, _ => Lt
    | _ , Tag_lobit => Gt
    | Tag_floats, Tag_floats => Eq
    | Tag_floats, _ => Lt
    | _ , Tag_floats => Gt
    | Tag_string, Tag_string => Eq
    | Tag_string, _ => Lt
    | _ , Tag_string => Gt
    | Tag_fun ret fmls, Tag_fun ret' fmls' =>
         lexi compare_bool ret ret' (compare_list (Pos.compare)) fmls fmls'
   end
 end
end.

 Definition lt (x y: t) : Prop := compare x y = Lt.
 Lemma lt_strorder: StrictOrder lt.
 Proof.
 Abort.

 Lemma lt_compat:  Morphisms.Proper
       (Morphisms.respectful Logic.eq (Morphisms.respectful Logic.eq iff)) lt.
 Proof.
  hnf; intros. subst. split; subst; auto.
 Qed.

 Lemma compare_spec :
     forall x y : t, CompareSpec (x = y) (lt x y) (lt y x) (compare x y).
 Proof.
 Abort.

   Lemma eq_dec : forall x y : t, {x = y} + {x <> y}.
   Proof.
   Abort.

End TagInfo.

Module TagDict := HashMap.MakeHashMap TagInfo.
Definition tagdict := TagDict.t.
