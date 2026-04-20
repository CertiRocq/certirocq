(* Contextual approximation for LambdaANF. Part of the CertiRocq project.
 * Author: Anonymized, 2016
 *)

From Stdlib Require Import Arith.Arith NArith.BinNat Lists.List micromega.Lia
        Relations.Relations Classes.RelationClasses.
From CertiRocq.LambdaANF Require Import term ctx eval logical_relations identifiers tactics.

Import ListNotations.


Definition empty_env := M.empty val.

Section ctx_approx.

  Variable pr : prims.
  Variable cenv : ctor_env.

  Open Scope ctx_scope.

  (** Contextual approximation *)
  Definition ctx_approx : relation exp :=
    fun e1 e2 =>
      forall C i v1, bstep_e pr cenv empty_env (C |[ e1 ]|) v1 i ->
                exists v2 j, bstep_e pr cenv empty_env (C |[ e2 ]|) v2 j.

  (** Contextual equivalence *)
  Definition ctx_equiv : relation exp :=
    fun e1 e2 => ctx_approx e1 e2 /\ ctx_approx e2 e1.

  Lemma ctx_approx_trans :
    Transitive ctx_approx.
  Proof.
    intros x y z H1 H2 C i v1 Hstep.
    edestruct H1 as [v2 [j2 Hstep2]]; eauto.
  Qed.

  Lemma ctx_approx_refl :
    Reflexive ctx_approx.
  Proof.
    intros x C i v1 Hstep.
    repeat split; eauto.
  Qed.

  Lemma ctx_equiv_equiv :
    Equivalence ctx_equiv.
  Proof.
    constructor.
    - split; apply ctx_approx_refl; eauto.
    - split; eapply H.
    - intros x y z [H1 H2] [H3 H4]; split; eapply ctx_approx_trans; eauto.
  Qed.

  Context (P : Post) (PG : PostG).

  Lemma preord_exp_sound e1 e2 :
    (forall k rho1 rho2, preord_env_P pr cenv (occurs_free e1) k PG rho1 rho2 ->
                    preord_exp pr cenv k P PG (e1, rho1) (e2, rho2)) ->
    ctx_approx e1 e2.
  Proof.
    intros Hyp C i v1 Hstep.
    assert (Hyp' := Hyp).
    eapply (preord_exp_compat pr cenv i PG empty_env empty_env C) in Hyp;
      [| now eapply preord_env_P_refl ].
    edestruct Hyp as [v2 [c2 [Hstep2 Hpre2]]]; eauto.
  Qed.

  Definition x : var := 1%positive.
  Definition y : var := 2%positive.
  Definition c : ctor_tag := 1%positive.
  Definition f : fun_tag := 1%positive.

  Definition stuck : exp :=
    Econstr x  c [] (
              Econstr y c [] (
                        Eapp x f [y])).

  Lemma stuck_gets_stuck rho :
    ~ (exists v c, bstep_e pr cenv rho stuck v c).
  Proof.
    intros [v [c H]]. inv H. inv H7.
    inv H9. inv H6. inv H8.
    rewrite M.gso, M.gss in H2. inv H2.
    intros Hc. inv Hc.
  Qed.

End ctx_approx.
