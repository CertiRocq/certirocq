(* General purpose tactics *)

From Stdlib Require Import ssrbool Arith.Arith.

Ltac inv H := inversion H; clear H; subst.

Ltac subst_exp :=
  match goal with
    | [H1 : ?e = ?e1, H2 : ?e = ?e2 |- _ ] =>
      rewrite H1 in H2; inv H2
    | [H1 : ?e1 = ?e, H2 : ?e2 = ?e |- _ ] =>
      rewrite <- H1 in H2; inv H2
    | [H1 : ?e = ?e1, H2 : ?e2 = ?e |- _ ] =>
      rewrite H1 in H2; inv H2
    | [H1 : ?e1 = ?e, H2 : ?e = ?e2 |- _ ] =>
      rewrite <- H1 in H2; inv H2
  end.

Ltac tci := eauto with typeclass_instances.

Global Remove Hints ssrbool.not_false_is_true : core.

Ltac sets := eauto with Ensembles_DB functions_BD.

Ltac xsets := eauto 20 with Ensembles_DB functions_BD.

Ltac destructAll :=
  match goal with
    | [ H : _ /\ _ |- _] => destruct H; destructAll
    | [ H : exists E, _ |- _ ] => destruct H; destructAll
    | _ => subst
  end.

Ltac pi0 :=
  repeat match goal with
         | [ H: _ + _ = 0 |- _ ] =>
           apply Nat.eq_add_0 in H; destruct H; subst
         | [ H: 0 = _ + _ |- _ ] =>
           symmetry in H; pi0
         (* | [ H: (if term_util.var_dec ?X ?Y then _ else _) = 0 |- _] => *)
         (*   destruct (term_util.var_dec X Y); try inversion H; pi0 *)
         | [ H: ?X <> ?X |- _] =>
           exfalso; apply H; auto
         end.
