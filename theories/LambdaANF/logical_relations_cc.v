(* Step-indexed logical relations for LambdaANF closure conversion.  Part of the CertiRocq project.
 * Author: Anonymized, 2016
 *)

From Stdlib Require Import NArith.BinNat Relations.Relations MSets.MSets MSets.MSetRBT
        Lists.List micromega.Lia Sets.Ensembles.
Require Import LambdaANF.term LambdaANF.eval LambdaANF.term_util LambdaANF.identifiers LambdaANF.ctx LambdaANF.set_util
        LambdaANF.Ensembles_util LambdaANF.List_util LambdaANF.size_cps LambdaANF.tactics LambdaANF.algebra.
Require Export LambdaANF.logical_relations.
Require Import compcert.lib.Coqlib.

Import ListNotations.

Close Scope Z_scope.

Section LogRelCC.

  Variable (pr : prims).
  Variable (cenv : ctor_env).

  (* Tag for closure records *)
  Variable (clo_tag : ctor_tag).

  Context {fuel : Type} {Hf : @fuel_resource fuel} {trace : Type} {Ht : @trace_resource trace}.

  Section Exp_rel.

    Variable (cc_approx_val : nat -> @PostGT fuel trace -> val -> val -> Prop).

    Definition cc_approx_res (k : nat) (P2 : PostGT) (r1 r2 : res) :=
    match r1, r2 with
    | OOT, OOT => True
    | Res v1, Res v2 => cc_approx_val k P2 v1 v2
    | _, _ => False
    end.

    Definition cc_approx_exp' (k : nat) (P1 : @PostGT fuel trace) (P2 : @PostGT fuel trace) (p1 p2 : exp * env) : Prop :=
      let '(e1, rho1) := p1 in
      let '(e2, rho2) := p2 in
      forall v1 cin1 cout1,
        to_nat cin1 <= k -> bstep_fuel cenv rho1 e1 cin1 v1 cout1 ->
        (* @not_stuck cenv fuel _ trace _ rho1 e1 -> *)
        exists v2 cin2 cout2,
          bstep_fuel cenv rho2 e2 cin2 v2 cout2 /\
          (* extra invariants for cost *)
          P1 (e1, rho1, cin1, cout1) (e2, rho2, cin2, cout2) /\
          cc_approx_res (k - to_nat cin1) P2 v1 v2.

  End Exp_rel.

  (** step-indexed relation on LambdaANF terms. Relates terms with open function with closure-converted terms *)

  Fixpoint cc_approx_val (k : nat) (PG : PostGT) (v1 v2 : val) {struct k} : Prop :=
    let fix cc_approx_val_aux (v1 v2 : val) {struct v1} : Prop :=
        let fix Forall2_aux vs1 vs2 :=
            match vs1, vs2 with
              | [], [] => True
              | v1 :: vs1, v2 :: vs2 =>
                cc_approx_val_aux v1 v2 /\ Forall2_aux vs1 vs2
              | _, _ => False
            end
        in
        match v1, v2 with
          | Vfun rho1 defs1 f1,
            Vconstr tag ((Vfun rho2 defs2 f2) ::  (Vconstr tag' fvs) :: [])  =>
            tag = clo_tag /\
            forall (vs1 vs2 : list val) (j : nat) (t : fun_tag)
              (xs1 : list var) (e1 : exp) (rho1' : env),
              List.length vs1 = List.length vs2 ->
              find_def f1 defs1 = Some (t, xs1, e1) ->
              Some rho1' = set_lists xs1 vs1 (def_funs defs1 defs1 rho1 rho1) ->
              exists (Γ : var) (xs2 : list var) (e2 : exp) (rho2' : env),
                find_def f2 defs2 = Some (t, Γ :: xs2, e2) /\
                Some rho2' = set_lists (Γ :: xs2) ((Vconstr tag' fvs) :: vs2)
                                     (def_funs defs2 defs2 rho2 rho2) /\
                match k with
                  | 0 => True
                  | S k =>
                    let R := cc_approx_val (k - (k-j)) PG in
                    j < S k ->
                    Forall2 R vs1 vs2 ->
                    cc_approx_exp' cc_approx_val (k - (k - j)) PG PG
                      (e1, rho1') (e2, rho2')
                end
          | Vconstr t1 vs1, Vconstr t2 vs2 =>
            t1 = t2 /\ Forall2_aux vs1 vs2
          | Vint n1, Vint n2 => n1 = n2
          | Vprim p1, Vprim p2 => p1 = p2
          | _, _ => False
        end
    in cc_approx_val_aux v1 v2.


  (** More compact definition of the value relation *)
  Definition cc_approx_val' (k : nat) (P : PostGT) (v1 v2 : val) : Prop :=
    match v1, v2 with
      | Vfun rho1 defs1 f1,
        Vconstr tag ((Vfun rho2 defs2 f2) ::  (Vconstr tag' fvs) :: []) =>
        tag = clo_tag /\
        forall (vs1 vs2 : list val) (j : nat) (t : fun_tag)
          (xs1 : list var) (e1 : exp) (rho1' : env),
          List.length vs1 = List.length vs2 ->
          find_def f1 defs1 = Some (t, xs1, e1) ->
          Some rho1' = set_lists xs1 vs1 (def_funs defs1 defs1 rho1 rho1) ->
          exists (Γ : var) (xs2 : list var) (e2 : exp) (rho2' : env),
            find_def f2 defs2 = Some (t, Γ :: xs2, e2) /\
            Some rho2' = set_lists (Γ :: xs2) ((Vconstr tag' fvs) :: vs2)
                                 (def_funs defs2 defs2 rho2 rho2) /\
            (j < k -> Forall2 (cc_approx_val j P) vs1 vs2 ->
             cc_approx_exp' cc_approx_val j P P (e1, rho1') (e2, rho2'))
      | Vconstr t1 vs1, Vconstr t2 vs2 =>
        t1 = t2 /\ Forall2 (cc_approx_val k P) vs1 vs2
      | Vint n1, Vint n2 => n1 = n2
      | Vprim p1, Vprim p2 => p1 = p2
      | _, _ => False
    end.

  (** Correspondence of the two definitions *)
  Lemma cc_approx_val_eq (k : nat) P (v1 v2 : val) :
    cc_approx_val k P v1 v2 <-> cc_approx_val' k P v1 v2.
  Proof.
    destruct k as [ | k ]; destruct v1; destruct v2;
    eauto; try (split; intros H; (now simpl in H; inv H)).
    - split.
      * revert l0; induction l as [| x xs IHxs];
        intros l2; destruct l2 as [| y ys ];
        try (now intros [H1 H2]; split; eauto; inv H2).
        intros H; split; destruct H as [H1 [H2 H3]]; eauto.
        constructor; [ now eauto | now eapply IHxs ].
      * revert l0; induction l as [| x xs IHxs];
        intros l2; destruct l2 as [| y ys ];
        try (now intros [H1 H2]; split; eauto; inv H2).
        intros H; split; inv H; eauto. inv H1.
        split; [ now eauto | now eapply IHxs ].
    - split; intros Hpre; simpl; destruct l; try contradiction;
      destruct v0; try contradiction; destruct l; try contradiction;
      destruct l; try contradiction; destruct v1; try contradiction;
      destruct Hpre as [Heq Hpre]; subst; split; eauto;
      intros; edestruct (Hpre vs1 vs2 0) as [Γ [xs2 [e2 [rho' [H1' [H2' H3']]]]]];
      eauto; subst; do 4 eexists; repeat split; eauto; intros Hc; exfalso; lia.
    - split.
      * revert l0; induction l as [| x xs IHxs];
        intros l2; destruct l2 as [| y ys ];
        try (now intros [H1 H2]; split; eauto; inv H2).
        intros H; split; destruct H as [H1 [H2 H3]]; eauto. constructor. eauto.
        eapply IHxs. simpl. eauto.
      * revert l0; induction l as [| x xs IHxs];
        intros l2; destruct l2 as [| y ys ];
        try (now intros [H1 H2]; split; eauto; inv H2).
        intros H; split; inv H; eauto. inv H1.
        split; [now eauto | now apply IHxs].
    - split; intros Hpre; simpl; destruct l; try contradiction;
      destruct v0; try contradiction; destruct l; try contradiction;
      destruct l; try contradiction; destruct v1; try contradiction;
      destruct Hpre as [Heq Hpre]; subst;
      split; eauto; intros;
      edestruct (Hpre vs1 vs2 j) as [Γ [xs2 [e2 [rho' [H1' [H2' H3']]]]]];
      eauto; do 4 eexists; repeat split; eauto; intros Hleq Hf' v1 c1 Hleq' Hstep;
      (assert (Heq' : k - (k - j) = j) by lia);
      rewrite Heq' in *;  eapply H3'; eauto.
  Qed.

  Global Opaque cc_approx_val.

  Notation cc_approx_exp := (cc_approx_exp' cc_approx_val).

  (** Environment relation for a single point (i.e. variable) :
   * ρ1 ~_k^x ρ2 iff ρ1(x) = Some v -> ρ2(x) = Some v' /\ v ~_k v' *)
  Definition cc_approx_var_env (k : nat) P (rho1 rho2 : env) (x y : var) : Prop :=
    forall v1,
      M.get x rho1 = Some v1 ->
      exists v2, M.get y rho2 = Some v2 /\ cc_approx_val k P v1 v2.

  (** Environment relation for a set of points (i.e. predicate over variables) :
   * ρ1 ~_k^S ρ2 iff
   *   forall x, S x -> ρ1(x) = Some v -> ρ2(x) = Some v' /\ v ~_k v' *)
  Definition cc_approx_env_P (S : Ensemble var) k P rho1 rho2 :=
    forall (x : var), S x -> cc_approx_var_env k P rho1 rho2 x x.

  (** Environment relation for the whole domain of definition :
   * ρ1 ~_k ρ2 iff forall x, ρ1(x) = v => ρ2(x) = v' /\ v ~_k v' *)
  Definition cc_approx_env (k : nat) P (rho1 rho2 : env) : Prop :=
    cc_approx_env_P (fun _ => True) k P rho1 rho2.

  (** Lemmas about extending the environment *)
  Lemma cc_approx_var_env_extend_eq :
    forall (rho1 rho2 : env) (k : nat) P (x : var) (v1 v2 : val),
      cc_approx_val k P v1 v2 ->
      cc_approx_var_env k P (M.set x v1 rho1) (M.set x v2 rho2) x x.
  Proof.
    intros rho1 rho2 k P x v1 v2 Hval x' Hget.
    rewrite M.gss in Hget. inv Hget. eexists. rewrite M.gss. split; eauto.
  Qed.

  Lemma cc_approx_var_env_extend_neq :
    forall (rho1 rho2 : env) (k : nat) P (x y : var) (v1 v2 : val),
      cc_approx_var_env k P rho1 rho2 y y ->
      y <> x ->
      cc_approx_var_env k P (M.set x v1 rho1) (M.set x v2 rho2) y y.
  Proof.
    intros rho1 rho2 k P x y v1 v2 Hval Hneq x' Hget.
    rewrite M.gso in *; eauto.
  Qed.

  Lemma cc_approx_var_env_extend :
    forall (rho1 rho2 : env) (k : nat) P (x y : var) (v1 v2 : val),
      cc_approx_var_env k P rho1 rho2 y y ->
      cc_approx_val k P v1 v2 ->
      cc_approx_var_env k P (M.set x v1 rho1) (M.set x v2 rho2) y y.
  Proof.
    intros rho1 rho2 k P x y v1 v2 Henv Hval.
    destruct (peq y x); subst.
    - apply cc_approx_var_env_extend_eq; eauto.
    - apply cc_approx_var_env_extend_neq; eauto.
  Qed.

  (** The environment relation is antimonotonic in the set
   * of free variables *)
  Lemma cc_approx_env_P_antimon (S1 S2 : var -> Prop) P k rho1 rho2 :
    cc_approx_env_P S2 k P rho1 rho2 ->
    S1 \subset S2 ->
    cc_approx_env_P S1 k P rho1 rho2.
  Proof.
    intros Hpre Hin x HP2. eapply Hpre; eapply Hin; eauto.
  Qed.

  Lemma cc_approx_exp_rel_mon (P1 P1' : PostT) P2 k e1 rho1 e2 rho2 :
    cc_approx_exp k P1 P2 (e1, rho1) (e2, rho2) ->
    inclusion _ P1 P1' ->
    cc_approx_exp k P1' P2 (e1, rho1) (e2, rho2).
  Proof.
    intros Hcc Hin v1 c1 cout1 Hleq Hstep.
    edestruct Hcc as [v2 [c2 [cout2 [Hstep2 [HP Hval]]]]]; eauto.
    repeat eexists; eauto.
  Qed.

  Lemma cc_approx_exp_same_rel_IH (P1 : PostT) P2 P2' k e1 rho1 e2 rho2 :
    (forall m v1 v2,
       m <= k ->
       cc_approx_val m P2 v1 v2 ->
       cc_approx_val m P2' v1 v2) ->
    cc_approx_exp k P1 P2 (e1, rho1) (e2, rho2) ->
    same_relation _ P2 P2' ->
    cc_approx_exp k P1 P2' (e1, rho1) (e2, rho2).
  Proof.
    intros IH Hcc Hin v1 c1 cout1 Hleq Hstep.
    edestruct Hcc as [v2 [c2 [cout2 [Hstep2 [HP Hval]]]]]; eauto.
    repeat eexists; eauto.
    destruct v1; destruct v2; try contradiction; eauto.
    eapply IH; eauto. lia.
  Qed.

  Lemma cc_approx_val_same_rel (k : nat) P1 P2 v1 v2 :
    cc_approx_val k P1 v1 v2 ->
    same_relation _ P1 P2 ->
    cc_approx_val k P2 v1 v2.
  Proof.
    revert v1 v2 P1 P2.
    induction k using lt_wf_rec1.
    intros x; induction x using val_ind'; simpl; eauto;
    intros v2 P1 P2 Hval Hin; rewrite cc_approx_val_eq in *;
    destruct v2; try contradiction.
    - destruct Hval as [Heq Hall]; subst; simpl; eauto.
      inv Hall. split; eauto.
    - destruct Hval as [Heq Hall]; subst; simpl; eauto.
      inv Hall. split; eauto. constructor; eauto.
      assert
        (Hsuf :
           cc_approx_val' k P2 (Vconstr c l) (Vconstr c l')).
      { rewrite <- cc_approx_val_eq. eapply IHx0; eauto.
        rewrite cc_approx_val_eq. split; eauto. }
      now inv Hsuf.
    - destruct l; try contradiction.
      destruct v0; try contradiction.
      destruct l; try contradiction.
      destruct v1; try contradiction.
      destruct l; try contradiction.
      destruct Hval as [Heq Hval]; subst; split; eauto.
      intros vs1 vs2 i t1 xs1 e1 rho1' Hlen Hdef Hset.
      edestruct Hval as [Gamma [xs2 [e2 [rho2' [Hdef' [Hset' Hi]]]]]]; eauto.
      do 4 eexists; repeat split; eauto. intros Hlt Hall.
      eapply cc_approx_exp_same_rel_IH; [| | eassumption ].
      intros; eapply H; eauto; lia.
      eapply cc_approx_exp_rel_mon.
      eapply Hi; eauto. eapply Forall2_monotonic; [| eassumption ].
      intros. eapply H; eauto. now firstorder. now firstorder.
    - eauto.
    - eauto.
  Qed.

  Lemma cc_approx_exp_same_rel (P : PostT) P1 P2 k e1 rho1 e2 rho2 :
    cc_approx_exp k P P1 (e1, rho1) (e2, rho2) ->
    same_relation _ P1 P2 ->
    cc_approx_exp k P P2 (e1, rho1) (e2, rho2).
  Proof.
    intros Hcc Hin v1 c1 c2 Hleq Hstep.
    edestruct Hcc as [v2 [c2' [cout2 [Hstep2 [HP Hval]]]]]; eauto.
    repeat eexists; eauto.
    destruct v1; destruct v2; try contradiction; eauto. simpl in *.
    eapply cc_approx_val_same_rel; eauto.
  Qed.

  Global Instance cc_approx_env_proper_set :
    Proper (Same_set var ==> Logic.eq ==> Logic.eq ==> Logic.eq ==> Logic.eq ==> iff)
           cc_approx_env_P.
  Proof.
    intros s1 s2 [H1 H2]; split; intros Hpre;
    eapply cc_approx_env_P_antimon; subst; eauto.
  Qed.

  (** Lemmas about the sets that index the environment relation *)
  Lemma cc_approx_env_Empty_set k P (rho1 rho2 : env) :
    cc_approx_env_P (Empty_set var) k P rho1 rho2.
  Proof.
    intros x H. inv H.
  Qed.

  Lemma cc_approx_env_P_union (P1 P2 : Ensemble var) k P rho1 rho2 :
    cc_approx_env_P P1 k P rho1 rho2 ->
    cc_approx_env_P P2 k P rho1 rho2 ->
    cc_approx_env_P (Union var P1 P2) k P rho1 rho2.
  Proof.
    intros Hpre1 Hpre2 x HP2. inv HP2; eauto.
  Qed.

  Lemma cc_approx_env_P_inter_l (P1 P2 : Ensemble var) k P rho1 rho2 :
    cc_approx_env_P P1 k P rho1 rho2 ->
    cc_approx_env_P (Intersection var P1 P2) k P rho1 rho2.
  Proof.
    intros Hpre x HP2. inv HP2; eauto.
  Qed.

  Lemma cc_approx_env_P_inter_r (P1 P2 : Ensemble var) k P rho1 rho2 :
    cc_approx_env_P P2 k P rho1 rho2 ->
    cc_approx_env_P (Intersection var P1 P2) k P rho1 rho2.
  Proof.
    intros Hpre x HP2. inv HP2; eauto.
  Qed.

  (** Extend the related environments with a single point *)
  Lemma cc_approx_env_P_extend :
    forall S (rho1 rho2 : env) (k : nat) P (x : var) (v1 v2 : val),
      cc_approx_env_P (Setminus var S (Singleton var x)) k P rho1 rho2 ->
      cc_approx_val k P v1 v2 ->
      cc_approx_env_P S k P (M.set x v1 rho1) (M.set x v2 rho2).
  Proof.
    intros S rho1 rho2 k P x v1 v2 Henv Hval x' HP v1' Hget.
    rewrite M.gsspec in Hget. destruct (peq x' x); subst.
    - inv Hget. eexists. rewrite M.gss. split; eauto.
    - apply Henv in Hget; eauto. destruct Hget as [v2' [Heq Hpre]].
      eexists; split; eauto. rewrite M.gso; eauto. constructor; eauto.
      intros Hin. inv Hin. congruence.
  Qed.

  (** Extend the related environments with a list *)
  Lemma cc_approx_env_P_set_lists_l:
    forall (P1 P2 : Ensemble var) (rho1 rho2 rho1' rho2' : env)
      (k : nat) P (xs : list var) (vs1 vs2 : list val),
      cc_approx_env_P P1 k P rho1 rho2 ->
      (forall x, ~ List.In x xs -> P2 x -> P1 x) ->
      Forall2 (cc_approx_val k P) vs1 vs2 ->
      set_lists xs vs1 rho1 = Some rho1' ->
      set_lists xs vs2 rho2 = Some rho2' ->
      cc_approx_env_P P2 k P rho1' rho2'.
  Proof.
    intros P1 P2 rho1' rho2' rho1 rho2 k P xs vs1 vs2 Hpre Hyp Hall Hset1 Hset2
           x HP v Hget.
    destruct (in_dec var_dec x xs).
    - edestruct (@set_lists_Forall2_get val) as [v1 [v2 [Hget1 [Hget2 HP']]]]; eauto.
      rewrite Hget in Hget1. inv Hget1. repeat eexists; eauto.
    - erewrite <- set_lists_not_In in Hget; eauto.
      edestruct Hpre as [v2 [Hget' Hpre']]; eauto.
      repeat eexists; eauto. erewrite <- set_lists_not_In; eauto.
  Qed.

  Lemma cc_approx_var_env_get_list (rho1 rho2 : env) (k : nat) P
        (xs ys : list var) (vs1 : list val) :
    Forall2 (cc_approx_var_env k P rho1 rho2) xs ys ->
    get_list xs rho1 = Some vs1 ->
    exists vs2,
      get_list ys rho2 = Some vs2 /\ Forall2 (cc_approx_val k P) vs1 vs2.
  Proof.
    revert ys vs1. induction xs as [| x xs IHxs]; intros ys vs2 Hall Hget.
    - destruct ys; inv Hall. inv Hget. eexists. split; simpl; eauto.
    - simpl in Hget.
      destruct (M.get x rho1) eqn:Heq1; try discriminate.
      destruct (get_list xs rho1) eqn:Heq2; try discriminate. inv Hget.
      destruct ys as [| y ys]; inv Hall.
      destruct (IHxs ys l H4 eq_refl) as [vs2 [Hget HAll]].
      destruct (H2 _ Heq1) as [v2 [Heq Hpre]].
      eexists. split; simpl; eauto. rewrite Hget, Heq. eauto.
  Qed.

  Lemma cc_approx_env_P_get_list_l (P : var -> Prop) (rho1 rho2 : env) (k : nat) S
        (xs : list var) (vs1 : list val) :
    cc_approx_env_P P k S rho1 rho2 ->
    Included _ (FromList xs) P ->
    get_list xs rho1 = Some vs1 ->
    exists vs2,
      get_list xs rho2 = Some vs2 /\ Forall2 (cc_approx_val k S) vs1 vs2.
  Proof.
    intros Henv. revert vs1.
    induction xs as [| x xs IHxs]; intros vs1 Hp Hget.
    - inv Hget. eexists. split; simpl; eauto.
    - simpl in Hget. destruct (M.get x rho1) eqn:Heq1; try discriminate.
      destruct (get_list xs rho1) eqn:Heq2; try discriminate. inv Hget.
      edestruct (IHxs l) as  [vs2 [Hget HAll]]; eauto.
      + intros x' Hin. eapply Hp. constructor 2; eauto.
      + eapply Henv in Heq1. destruct Heq1 as [v2 [H1 H2]].
        eexists. split; simpl; eauto. rewrite H1. rewrite Hget.
        constructor. apply Hp. now constructor.
  Qed.

  Corollary cc_approx_env_get_list_l (rho1 rho2 : env) (k : nat) S
            (xs : list var) (vs1 : list val) :
    cc_approx_env k S rho1 rho2 ->
    get_list xs rho1 = Some vs1 ->
    exists vs2,
      get_list xs rho2 = Some vs2 /\ Forall2 (cc_approx_val k S) vs1 vs2.
  Proof.
    intros. eapply cc_approx_env_P_get_list_l; eauto.
    intros x H'; simpl; eauto.
  Qed.

  Corollary cc_approx_env_extend (rho1 rho2 : env) (k : nat) S
            (x : var) (v1 v2 : val) :
    cc_approx_env k S rho1 rho2 ->
    cc_approx_val k S v1 v2 ->
    cc_approx_env k S (M.set x v1 rho1) (M.set x v2 rho2).
  Proof.
    intros H1 Hval. apply cc_approx_env_P_extend; eauto.
    eapply cc_approx_env_P_antimon; eauto. intros x' H; simpl; eauto.
  Qed.

  Corollary cc_approx_env_set_lists_l (rho1 rho2 rho1' rho2' : env) (k : nat)
            S (xs : list var) (vs1 vs2 : list val) :
    cc_approx_env k S rho1 rho2 ->
    Forall2 (cc_approx_val k S) vs1 vs2 ->
    set_lists xs vs1 rho1 = Some rho1' ->
    set_lists xs vs2 rho2 = Some rho2' ->
    cc_approx_env k S rho1' rho2'.
  Proof.
    intros. eapply cc_approx_env_P_set_lists_l; eauto.
  Qed.

  Lemma cc_approx_env_P_set_not_in_P_r P k S rho rho' x v :
    cc_approx_env_P P k S rho rho' ->
    ~ x \in P ->
    cc_approx_env_P P k S rho (M.set x v rho').
  Proof.
    intros Hcc Hnin y Py v' Hget.
    edestruct Hcc as [v'' [Hget' Happrox]]; eauto.
    exists v''. rewrite M.gsspec.
    destruct (peq y x); subst.
    - contradiction.
    - eauto.
  Qed.

  Lemma cc_approx_env_P_def_funs_not_In_P_l k S rho1 rho2 P B B' :
    Disjoint _ S (name_in_fundefs B') ->
    cc_approx_env_P S k P rho1 rho2 ->
    cc_approx_env_P S k P (def_funs B B' rho1 rho1) rho2.
  Proof.
    intros Hd Hcc x HS v Hget. eapply Hcc; eauto.
    erewrite <- def_funs_neq. eassumption.
    intros Hc. eapply Hd; constructor; eauto.
  Qed.

  Lemma cc_approx_env_P_def_funs_not_In_P_r k P rho1 rho2 S B B' :
    Disjoint _ S (name_in_fundefs B') ->
    cc_approx_env_P S k P rho1 rho2 ->
    cc_approx_env_P S k P rho1 (def_funs B B' rho2 rho2).
  Proof.
    intros Hd Hcc x HS v Hget.
    edestruct Hcc as [v' [Hget' Hcc']]; eauto.
    eexists; split; eauto.
    rewrite def_funs_neq. eassumption.
    intros Hc. eapply Hd; constructor; eauto.
  Qed.

  (** * Index Monotonicity Properties *)

  (** The value relation is monotonic in the step index *)
  Lemma cc_approx_val_monotonic (k : nat) P :
    (forall v1 v2 j,
       cc_approx_val k P v1 v2 -> j <= k -> cc_approx_val j P v1 v2).
  Proof.
    intros v1 v2 h Hpre Hleq. try rewrite cc_approx_val_eq in *.
    revert v2 Hpre; induction v1 using val_ind'; intros v2 Hpre;
    destruct v2; try (simpl; contradiction); eauto.
    - destruct l; try now inv Hpre.
    - inv Hpre. inv H0.
      split; auto. constructor; rewrite cc_approx_val_eq in *.
      now eapply IHv1; eauto.
      destruct (IHv0 ((Vconstr c l'))) as [Heq Hpre']; eauto.
      now split; eauto.
    - destruct l; try contradiction. destruct v0; try contradiction.
      destruct l; try contradiction. destruct v1; try contradiction.
      destruct l; try contradiction.
      destruct Hpre as [Heq1 Hpre]; subst; split; eauto.
      intros vs1 vs2 j t1' xs e1 rho1' Hlen Hf' Heq.
      edestruct Hpre as [Γ [xs2 [e2 [rho2' [H1 [H2 H3]]]]]]; eauto.
      subst. do 4 eexists; repeat split; eauto. intros Hleq' Hall.
      eapply H3; eauto. lia.
  Qed.

  Lemma cc_approx_res_monotonic (k : nat) P :
  (forall v1 v2 j,
     cc_approx_res cc_approx_val k P v1 v2 -> j <= k -> cc_approx_res cc_approx_val j P v1 v2).
  Proof.
    intros [|] [|] j H; try contradiction; eauto.
    eapply cc_approx_val_monotonic; eauto.
  Qed.

  (** The expression relation is monotonic in the step index *)
  Lemma cc_approx_exp_monotonic (k j : nat) P1 P2 rho1 e1 rho2 e2 :
    cc_approx_exp k P1 P2 (rho1, e1) (rho2, e2) ->
    j <= k ->
    cc_approx_exp j P1 P2 (rho1, e1) (rho2, e2).
  Proof.
    intros Hpre Hleq v1 c1 cout1 Hlt Hstep.
    edestruct (Hpre v1 c1) as [v2 [c2 [cout2 [H1 [H2 H3]]]]]; eauto. lia.
    do 3 eexists; repeat split; eauto.
    eapply cc_approx_res_monotonic; eauto. lia.
  Qed.

  (** The environment relations are monotonic in the step index *)
  Lemma cc_approx_env_P_monotonic :
    forall P (k j : nat) S (rho1 rho2 : env),
      j <= k -> cc_approx_env_P P k S rho1 rho2 -> cc_approx_env_P P j S rho1 rho2.
  Proof.
    intros P k j S rho1 rho2 Hleq Hpre x HP v Hget.
    edestruct Hpre as [v2 [Heq Hpre2]]; eauto.
    eexists; split; eauto. eapply cc_approx_val_monotonic; eauto.
  Qed.

  Lemma cc_approx_env_monotonic k j S rho1 rho2 :
    j <= k -> cc_approx_env k S rho1 rho2 -> cc_approx_env j S rho1 rho2.
  Proof.
    intros Hleq H. eapply cc_approx_env_P_monotonic; eauto.
  Qed.

  (* Closure projection before application application *)
  Definition AppClo f f' Γ :=
    Eproj_c f' clo_tag 0%N f
          (Eproj_c Γ clo_tag 1%N f Hole_c).

  Open Scope alg_scope.

  Definition post_app_compat_cc' x t ys rho1 (P : @PostT fuel trace) (PG : @PostGT fuel trace):=
    forall e1 xs f2 Γ x' t' ys' e2 rho2 rhoc1 rhoc2 fl f vs rhoc1' cin1 cin2 cout1 cout2,

      map_util.M.get x rho1 = Some (Vfun rhoc1 fl f) ->
      get_list ys rho1 = Some vs ->
      find_def f fl = Some (t, xs, e1) ->
      set_lists xs vs (def_funs fl fl rhoc1 rhoc1) = Some rhoc1' ->

      (* for simplicity don't model the semantics of the target since it doesn't matter *)
      PG (e1, rhoc1', cin1, cout1)  (e2, rhoc2, cin2, cout2) ->
      P (Eapp x t ys, rho1, cin1 <+> one (Eapp x t ys), cout1 <+> one (Eapp x t ys))
        (AppClo f2 x' Γ |[ Eapp x' t' (Γ :: ys') ]|, rho2,
                         cin2 <+> one (Eapp x' t' (Γ :: ys)) <+>
                              one (Eproj Γ clo_tag 1%N f2 (Eapp x' t' (Γ :: ys))) <+>
                              one (AppClo f2 x' Γ |[ Eapp x' t' (Γ :: ys') ]|),
                         cout2 <+> one (Eapp x' t' (Γ :: ys)) <+>
                              one (Eproj Γ clo_tag 1%N f2 (Eapp x' t' (Γ :: ys))) <+>
                              one (AppClo f2 x' Γ |[ Eapp x' t' (Γ :: ys') ]|)).


  Definition post_letapp_compat_cc' x f t ys e1 rho1 (P1 P2 : @PostT fuel trace) (PG : @PostGT fuel trace) :=
    forall xs e_b1 v1 f2 Γ x' f' t' ys' e2 e_b2
         rho2 rho2' rhoc1 rhoc2 fl h vs rhoc1' cin1 cin1' cin2 cin2' cout1 cout2 cout1' cout2',

      map_util.M.get f rho1 = Some (Vfun rhoc1 fl h) ->
      get_list ys rho1 = Some vs ->
      find_def h fl = Some (t, xs, e_b1) ->
      set_lists xs vs (def_funs fl fl rhoc1 rhoc1) = Some rhoc1' ->
      bstep_fuel cenv rhoc1' e_b1 cin1 (Res v1) cout1 ->
      (* Will need to prove that the size of the returned val is *)

      (* for simplicity don't model the semantics of the target since it doesn't matter *)
      PG (e_b1, rhoc1', cin1, cout1)  (e_b2, rhoc2, cin2, cout2) ->
      P1 (e1, M.set x v1 rho1, cin1', cout1') (e2, rho2', cin2', cout2') ->
      P2 (Eletapp x f t ys e1, rho1, cin1 <+> cin1' <+> one (Eletapp x f t ys e1), cout1 <+> cout1' <+> one (Eletapp x f t ys e1))
         (AppClo f2 f' Γ |[ Eletapp x' f' t' (Γ :: ys') e2 ]|, rho2,
                          cin2 <+> cin2' <+> one (Eletapp x' f' t' (Γ :: ys') e2) <+>
                               one (Eproj Γ clo_tag 1%N f2 (Eletapp x' f' t' (Γ :: ys') e2)) <+>
                               one (AppClo f2 f' Γ |[ Eletapp x' f' t' (Γ :: ys') e2 ]|),
                          cout2 <+> cout2' <+> one (Eletapp x' f' t' (Γ :: ys') e2) <+>
                                one (Eproj Γ clo_tag 1%N f2 (Eletapp x' f' t' (Γ :: ys') e2)) <+>
                                one (AppClo f2 f' Γ |[ Eletapp x' f' t' (Γ :: ys') e2 ]|) ).

  Definition post_letapp_compat_cc_OOT' x f t ys e1 rho1 (P2 : @PostT fuel trace) (PG :  @PostGT fuel trace):=
    forall xs e_b1 f2 Γ x' f' t' ys' e2 e_b2
           rho2 rhoc1 rhoc2 fl h vs rhoc1' cin1 cout1 cin2 cout2,

      map_util.M.get f rho1 = Some (Vfun rhoc1 fl h) ->
      get_list ys rho1 = Some vs ->
      find_def h fl = Some (t, xs, e_b1) ->
      set_lists xs vs (def_funs fl fl rhoc1 rhoc1) = Some rhoc1' ->

      (* for simplicity don't model the semantics of the target since it doesn't matter *)
      PG (e_b1, rhoc1', cin1, cout1)  (e_b2, rhoc2, cin2, cout2) ->
      P2 (Eletapp x f t ys e1, rho1, cin1 <+> one (Eletapp x f t ys e1), cout1 <+> one (Eletapp x f t ys e1))
         (AppClo f2 f' Γ |[ Eletapp x' f' t' (Γ :: ys') e2 ]|, rho2,
                          cin2 <+> one (Eletapp x' f' t' (Γ :: ys') e2) <+>
                             one (Eproj Γ clo_tag 1%N f2 (Eletapp x' f' t' (Γ :: ys') e2)) <+>
                             one (AppClo f2 f' Γ |[ Eletapp x' f' t' (Γ :: ys') e2 ]|),
                          cout2 <+> one (Eletapp x' f' t' (Γ :: ys') e2) <+>
                             one (Eproj Γ clo_tag 1%N f2 (Eletapp x' f' t' (Γ :: ys') e2)) <+>
                             one (AppClo f2 f' Γ |[ Eletapp x' f' t' (Γ :: ys') e2 ]|)).

  Definition post_app_compat_cc P PG := forall x t xs rho1, post_app_compat_cc' x t xs rho1 P PG.

  Definition post_letapp_compat_cc P1 P2 PG := forall x f t xs e1 rho1, post_letapp_compat_cc' x f t xs e1 rho1 P1 P2 PG.

  Definition post_letapp_compat_cc_OOT P2 PG := forall x f t xs e1 rho1, post_letapp_compat_cc_OOT' x f t xs e1 rho1 P2 PG.



  Section Compat.

   Context (P1 P2 : @PostT fuel trace) (* Local *)
           (PG : @PostGT fuel trace). (* Global *)


   Lemma cc_approx_exp_constr_compat k
         rho1 rho2 x t ys1 ys2 e1 e2 :
     post_constr_compat' x t ys1 e1 rho1  x t ys2 e2 rho2 P1 P2 ->
     post_OOT' (Econstr x t ys1 e1) rho1 (Econstr x t ys2 e2) rho2 P2 ->
     (* For application *)
     Forall2 (cc_approx_var_env k PG rho1 rho2) ys1 ys2 ->
     (forall vs1 vs2 : list val,
         (* needed by cost proof *)
         get_list ys1 rho1 = Some vs1 ->
         Forall2 (cc_approx_val k PG) vs1 vs2 ->
         cc_approx_exp k P1 PG (e1, M.set x (Vconstr t vs1) rho1)
                       (e2, M.set x (Vconstr t vs2) rho2)) ->
     cc_approx_exp k P2 PG (Econstr x t ys1 e1, rho1) (Econstr x t ys2 e2, rho2).
   Proof.
     intros Hpost Hoot Hall Hpre v1 c1 cout Hleq1 Hstep1. inv Hstep1.
     - (* OOT *)
       exists OOT, c1, <0>. split. constructor; eauto.
       split; [| now eauto ]. eapply Hoot; eassumption.
     - inv H.
       edestruct (cc_approx_var_env_get_list rho1 rho2) as [vs2' [Hget' Hpre']];
         [| eauto |]; eauto.
       rewrite to_nat_add in *.
       assert (Hg := to_nat_one (exp_to_fin (Econstr x t ys1 e1))). unfold one in *.

       edestruct Hpre as [v2 [c2 [cout' [Hstep [HS Hval]]]]]; [| | | eassumption | ]; eauto.
       lia.

       eexists. exists (c2 <+> one (Econstr x t ys2 e2)); repeat eexists.
       econstructor 2; eauto. econstructor; eauto.
       eapply Hpost; eauto.
       eapply cc_approx_res_monotonic. eassumption.
       simpl in *. lia.
   Qed.

  Lemma cc_approx_exp_proj_compat k rho1 rho2 x tau n y1 y2 e1 e2 :
    post_proj_compat' x tau n y1 e1 rho1  x tau n y2 e2 rho2 P1 P2 ->
    post_OOT' (Eproj x tau n y1 e1) rho1 (Eproj x tau n y2 e2) rho2 P2 ->
    cc_approx_var_env k PG rho1 rho2 y1 y2 ->
    (forall v1 v2 c vs,
       (* needed for cost proof *)
       M.get y1 rho1 = Some (Vconstr c vs) ->
       List.In v1 vs ->
       cc_approx_val k PG v1 v2 ->
       cc_approx_exp k P1 PG (e1, M.set x v1 rho1)
                     (e2, M.set x v2 rho2)) ->
    cc_approx_exp k P2 PG (Eproj x tau n y1 e1, rho1) (Eproj x tau n y2 e2, rho2).
  Proof.
    intros Hpost Hoot Henv Hexp v1 cin cout Hleq1 Hstep1. inv Hstep1.
    - (* ΟΟΤ *)
      exists OOT, cin, <0>. split. constructor; eassumption.
      split; [| now eauto ]. eapply Hoot; eassumption.
    - inv H. edestruct Henv as [v' [Hget Hpre]]; eauto.
      destruct v'; rewrite cc_approx_val_eq in Hpre; simpl in Hpre; try contradiction.
      inv Hpre.

      rewrite to_nat_add in *. assert (Hg := to_nat_one (exp_to_fin (Eproj x c n y1 e1))). unfold one in *.

      edestruct (Forall2_nthN (cc_approx_val k PG) vs l) as [v2 [Hnth Hval]]; eauto.
      edestruct Hexp as [v2' [cin' [cout' [Hstep [HS Hval']]]]];
        [| | | | eassumption | ]; eauto.
      now eapply nthN_In; eauto. lia.

      do 3 eexists. split; [| split ].
      econstructor 2; eauto. econstructor; eauto.

      eapply Hpost; try eassumption.
      eapply cc_approx_res_monotonic. eassumption.
      simpl in *. lia.
  Qed.

  (** Let Application compatibility *)
  Lemma cc_approx_exp_letapp_compat (k : nat)
        (rho1 rho2 : env) (x f1 : var) (xs1 : list var)
        (f2 f' Γ : var) (xs2 : list var) (t : fun_tag) (e1 e2 : exp) :
    post_letapp_compat_cc' x f1 t xs1 e1 rho1 P1 P2 PG ->
    post_letapp_compat_cc_OOT' x f1 t xs1 e1 rho1 P2 PG ->
    post_OOT' (Eletapp x f1 t xs1 e1) rho1 (AppClo f2 f' Γ |[ Eletapp x f' t (Γ :: xs2) e2 ]|) rho2 P2 ->
    ~ Γ \in (f2 |: [set f'] :|: FromList xs2) ->
    ~ f' \in (f2 |: FromList xs2) ->
    cc_approx_var_env k PG rho1 rho2 f1 f2 ->
    Forall2 (cc_approx_var_env k PG rho1 rho2) xs1 xs2 ->
    (forall m v1 v2 rho2',
        m <= k ->
        cc_approx_val m PG v1 v2 ->
        ctx_to_rho (AppClo f2 f' Γ) rho2 rho2' ->
        cc_approx_exp m P1 PG (e1, M.set x v1 rho1) (e2, M.set x v2 rho2')) ->

    cc_approx_exp k P2 PG (Eletapp x f1 t xs1 e1, rho1)
                  (AppClo f2 f' Γ |[ Eletapp x f' t (Γ :: xs2) e2 ]|, rho2).
  Proof.
    intros Hpost Hpostoot Hoot Hnin1 Hnin2 Henv Hall Hexp v1 cin cout Hleq1 Hstep1. inv Hstep1.
    - (* ΟΟΤ *)
      exists OOT, cin, <0>. split; [| split ].
      + econstructor. unfold one. erewrite one_eq. eassumption.
      + eapply Hoot; eauto.
      + simpl; eauto.
    - inv H.
      + (* App terminates *)
        edestruct Henv as [v' [Hget Hpre]]; eauto.
        destruct v'; rewrite cc_approx_val_eq in Hpre; simpl in Hpre; try contradiction.
        destruct l as [| ? [|] ]; try contradiction;
        destruct v0; try contradiction;
          destruct v2; try contradiction.
        destruct l; try contradiction;

        destruct Hpre as [Heq Hpre]; subst.
        edestruct cc_approx_var_env_get_list as [vs' [Hgetl2 Hvall]]; eauto.

        rewrite !to_nat_add in *. assert (Hg := to_nat_one (exp_to_fin (Eletapp x f1 t xs1 e1))). unfold one in *.

        edestruct Hpre with (j := k - 1) as [G [xs2' [e2' [rho2'' [Hfdef [Hseteq Hcc]]]]]].
        eapply Forall2_length. eassumption. eassumption. now eauto.
        subst. assert (Hevalb := H13).
        eapply Hcc in H13;
          [| | eapply Forall2_monotonic; [| eassumption ] | ]; try (unfold one in *; simpl in *; lia).
        * destruct H13 as (v2' & c2 & c2' & Hstep2 & Hge & Hccv).
          destruct v2' as [ | v2' ]; try contradiction.
          edestruct (Hexp (k - to_nat (cin1 <+> (one_i (exp_to_fin (Eletapp x f1 t xs1 e1)))))) as [v3' [cin2' [cout2' [Hstep [HS Hval']]]]];
            [| | | | eassumption | ]; eauto. simpl in *; lia.

          eapply cc_approx_val_monotonic. eapply Hccv. rewrite to_nat_add. unfold one in *; simpl in *. lia.

           econstructor. eassumption. reflexivity. econstructor. rewrite M.gso. eassumption.
           intros Hc; eapply Hnin2; subst; eauto. reflexivity. now econstructor.

           rewrite !to_nat_add. unfold one in *; simpl in *. lia.

           destruct (set_lists xs2' vs' (def_funs f f t0 t0)) eqn:Hgetl; try congruence.
           repeat subst_exp. inv Hseteq.
           do 3 eexists. split; [| split].
           -- constructor 2. econstructor; eauto. simpl. reflexivity.
              constructor 2. econstructor; eauto.
              rewrite M.gso. eassumption. intros Hc; subst. eapply Hnin2; eauto.
              simpl. reflexivity.
              constructor 2. econstructor.
              rewrite M.gso. rewrite M.gss. reflexivity.
              intros Hc. subst; now eapply Hnin1; eauto.
              simpl. rewrite M.gss. rewrite get_list_set_neq. rewrite get_list_set_neq, Hgetl2.
              reflexivity. intros Hc1. now eapply Hnin2; eauto.
              intros Hc2. now eapply Hnin1; eauto. eassumption.
              simpl. rewrite Hgetl. reflexivity. eassumption. eassumption.
           -- eapply Hpost; eassumption.
          -- eapply cc_approx_res_monotonic; eauto. simpl. rewrite to_nat_add. unfold one in *; simpl in *; lia.
        * intros. eapply cc_approx_val_monotonic; eauto. lia.
      + edestruct Henv as [v' [Hget Hpre]]; eauto.
        destruct v'; rewrite cc_approx_val_eq in Hpre; simpl in Hpre; try contradiction.
        destruct l as [| [] [|] ]; try contradiction.
        destruct v0; try contradiction. destruct l; try contradiction. destruct Hpre as [HEq Hpre].
        edestruct cc_approx_var_env_get_list as [vs' [Hgetl2 Hvall]]; eauto.
        edestruct Hpre with (j := k - 1) as [G [xs2' [e2' [rho2' [Hfdef [Hseteq Hcc]]]]]].
        eapply Forall2_length. eassumption. eassumption. now eauto.
        subst.
        rewrite !to_nat_add in *. assert (Hg := to_nat_one (exp_to_fin (Eletapp x f1 t xs1 e1))). unfold one in *.

        eapply Hcc in H13;
          [| | eapply Forall2_monotonic; [| eassumption ] | ]; try (simpl in *; lia).
        2:{ intros; eapply cc_approx_val_monotonic; eauto. lia. }
        destruct (set_lists xs2' vs' (def_funs f f t0 t0)) as [rho2'' | ] eqn:Hsets; inv Hseteq.
        repeat subst_exp.
        destruct H13 as (v2' & c2 & c2'  & Hstep2 & Hge & Hccv).
        destruct v2' as [ | v2' ]; try contradiction. simpl in *.
        do 3 eexists; split; [| split; eauto ].
        * constructor 2. econstructor; eauto. simpl; reflexivity.
          constructor 2. econstructor; eauto. rewrite M.gso. eassumption.
          intros Hc; subst; eapply Hnin2; eauto.
          reflexivity.
          constructor 2. eapply BStept_letapp_oot; eauto.
          rewrite M.gso. rewrite M.gss. reflexivity.
          intros Hc1; subst. now eapply Hnin1; eauto.
          simpl. rewrite M.gss.
          rewrite get_list_set_neq. rewrite get_list_set_neq, Hgetl2.
          reflexivity. intros Hc1. now eapply Hnin2; eauto.
          intros Hc2. now eapply Hnin1; eauto.
          simpl. rewrite Hsets. reflexivity.
        * eapply Hpostoot; eassumption.
        * eauto.
  Qed.

  (** Application compatibility *)

  Lemma cc_approx_exp_app_compat (k : nat)
        (rho1 rho2 : env) (f1 : var) (xs1 : list var)
        (f2 f' Γ : var) (xs2 : list var) (t : fun_tag) :
    post_app_compat_cc' f1 t xs1 rho1 P2 PG ->
    post_OOT' (Eapp f1 t xs1) rho1 (AppClo f2 f' Γ |[ Eapp f' t (Γ :: xs2) ]|) rho2 P2 ->
    ~ Γ \in (f2 |: [set f'] :|: FromList xs2) ->
    ~ f' \in (f2 |: FromList xs2) ->

    cc_approx_var_env k PG rho1 rho2 f1 f2 ->
    Forall2 (cc_approx_var_env k PG rho1 rho2) xs1 xs2 ->
    cc_approx_exp k P2 PG (Eapp f1 t xs1, rho1)
                  (AppClo f2 f' Γ |[ Eapp f' t (Γ :: xs2) ]|, rho2).
  Proof.
    intros Hpost Hoot Hnin1 Hnin2 Hvar Hall v1 cin cout Hleq1 Hstep1. inv Hstep1.
    - (* ΟΟΤ *)
      exists OOT, cin, <0>. split; [| split ].
      + econstructor. unfold one. erewrite one_eq. eassumption.
      + eapply Hoot; eauto.
      + simpl; eauto.
    - inv H. edestruct Hvar as [v2' [Hget Hpre]]; eauto.
      destruct v2'; rewrite cc_approx_val_eq in Hpre; simpl in Hpre; try contradiction.
      destruct l as [| ? [|] ]; try contradiction;
        destruct v; try contradiction.
        destruct v0; try contradiction.
      edestruct cc_approx_var_env_get_list as [vs' [Hgetl2 Hvall]]; eauto.
      destruct l; try contradiction.
      destruct Hpre as [Heq Hpre]; subst.
      edestruct Hpre with (j := k - 1) as [G [xs2' [e2' [rho2'' [Hfdef [Hseteq Hcc]]]]]]; try eassumption.
      eapply Forall2_length. eassumption. now eauto.
      rewrite !to_nat_add in *. assert (Hg := to_nat_one (exp_to_fin (Eapp f1 t xs1))). unfold one in *.

      subst.
      destruct (set_lists xs2' vs' (def_funs f f t0 t0)) eqn:Hgetl; try congruence. inv Hseteq.
      repeat subst_exp. assert (Heval := H11).
      eapply Hcc in H11;
        [| | eapply Forall2_monotonic; [| eassumption ] | ]; try (simpl in *; lia).
      + destruct H11 as (v2' & c2 & cout2' & Hstep2 & Hge & Hccv).
        edestruct Hcc as [v4 [c4 [c5 [Hstep4 [Hpg4 Hrel4]]]]]; [ | | | eassumption | ].
        simpl in *; lia.
        eapply Forall2_monotonic; [| eassumption ].
        intros. eapply cc_approx_val_monotonic. eassumption. lia. simpl in *; lia.

        do 3 eexists. split; [| split].
        * simpl. econstructor 2. econstructor; eauto. reflexivity.
          econstructor 2. econstructor; eauto.
          rewrite M.gso. eassumption.
          intros Hc. subst; now eapply Hnin2; eauto. reflexivity.
          econstructor 2. econstructor; eauto.
          rewrite M.gso. rewrite M.gss. reflexivity.
          intros Hc. subst. now eapply Hnin1; eauto.
          simpl. rewrite M.gss.
          rewrite get_list_set_neq. rewrite get_list_set_neq. rewrite Hgetl2. reflexivity.
          intros Hc. now eapply Hnin2; eauto.
          intros Hc. now eapply Hnin1; eauto.
          simpl. rewrite Hgetl. reflexivity.
        * eapply Hpost; eauto.
        * eapply cc_approx_res_monotonic; eauto. simpl in *; lia.
      + intros. eapply cc_approx_val_monotonic; eauto. lia.
  Qed.

  Lemma cc_approx_exp_fun_compat k rho1 rho2 B B' e1 e2 :
    post_fun_compat' B e1 rho1 B' e2 rho2 P1 P2 ->
    post_OOT' (Efun B e1) rho1 (Efun B' e2) rho2 P2 ->
    cc_approx_exp (k - 1) P1 PG (e1, def_funs B B rho1 rho1)
               (e2, def_funs B' B' rho2 rho2) ->
    cc_approx_exp k P2 PG (Efun B e1, rho1) (Efun B' e2, rho2).
  Proof.
    intros Hyp Hpost Hexp v1 c1 c2 Hleq1 Hstep1. inv Hstep1.
    - (* OOT *)
      exists OOT, c1, <0>. split. constructor; eassumption.
      split. eapply Hpost. eassumption.
      simpl; eauto.
    - inv H.
      rewrite !to_nat_add in *. assert (Hg := to_nat_one (exp_to_fin (Efun B e1))). unfold one in *.

      edestruct Hexp as [v2' [c3 [c4 [Hstepv2' [Hprev2' Hpost']]]]]; [ | eassumption | ]; eauto.

      simpl in *; lia.

      eexists v2', (c3 <+> one (Efun B' e2)). repeat eexists.
      econstructor 2; eauto. econstructor; eauto.
      eapply Hyp. eassumption.
      eapply cc_approx_res_monotonic. eassumption. simpl in *; lia.
  Qed.

  Lemma cc_approx_exp_case_nil_compat k rho1 rho2 x1 x2 :
    post_OOT' (Ecase x1 []) rho1 (Ecase x2 []) rho2 P2 ->
    cc_approx_exp k P2 PG (Ecase x1 [], rho1) (Ecase x2 [], rho2).
  Proof.
    intros Hoot v1 c1 c2 Hleq1 Hstep1. inv Hstep1.
    - (* ΟΟΤ *)
      exists OOT, c1, <0>. split. constructor; eauto. simpl in *.
      split; [| now eauto ]. eapply Hoot; eauto.
    - inv H. inv H5.
  Qed.

  Lemma cc_approx_exp_case_cons_compat k rho1 rho2 x1 x2 t e1 e2 B1 B2 :
    post_OOT' (Ecase x1 ((t, e1) :: B1)) rho1 (Ecase x2 ((t, e2) :: B2)) rho2 P2 ->
    post_case_compat_hd' x1 t e1 B1 rho1 x2 t e2 B2 rho2 P1 P2 ->
    post_case_compat_tl' x1 t e1 B1 rho1 x2 t e2 B2 rho2 P2 P2 ->

    Forall2 (fun p1 p2 => fst p1 = fst p2) B1 B2 ->
    cc_approx_var_env k PG rho1 rho2 x1 x2 ->
    (forall m, m < k -> cc_approx_exp k P1 PG (e1, rho1) (e2, rho2)) ->
    cc_approx_exp k P2 PG (Ecase x1 B1, rho1) (Ecase x2 B2, rho2) ->
    cc_approx_exp k P2 PG (Ecase x1 ((t, e1) :: B1), rho1) (Ecase x2 ((t, e2) :: B2), rho2).
  Proof.
    intros Hoot Hposthd Hposttl Hall Henv Hexp_hd Hexp_tl v1 c1 c2 Hleq1 Hstep1. inv Hstep1.
    - (* ΟΟΤ *)
      exists OOT, c1, <0>. split. constructor; eauto. simpl in *.
      split; [| now eauto ]. eapply Hoot; eauto.
    - inv H.
      rewrite !to_nat_add in *. assert (Hg := to_nat_one (exp_to_fin (Ecase x1 ((t, e1) :: B1)))). unfold one in *.
      inv H3. destruct (var_dec t t0).
    + inv H5; [| contradiction ]; subst.
      edestruct (Hexp_hd (k - 1)) as [v2 [c2 [c2' [Hstep2 [Hpost Hpre2]]]]];
        [ | | eassumption | ]; eauto. simpl in *; lia. simpl in *; lia.

     edestruct Henv as [v2' [Hget Hpre]]; eauto.
     rewrite cc_approx_val_eq in Hpre.
     destruct v2'; try (now simpl in Hpre; contradiction). inv Hpre.

     repeat eexists.
     * econstructor 2; eauto. econstructor; eauto. econstructor; eauto.
       eapply caseConsistent_same_ctor_tags. eassumption. eassumption.
       now constructor.
     * eapply Hposthd; eauto.
     * eapply cc_approx_res_monotonic. eassumption.
       simpl in *; lia.
    + inv H5. contradiction.
      edestruct Hexp_tl with (cin1 := cin <+> one (Ecase x1 B1)) as [v2 [c2 [c3 [Hstep2 [Hpost2 Hpre2]]]]].
      * rewrite to_nat_add. unfold one in *; simpl in *; lia.
      * econstructor 2; eauto. econstructor; eauto.
      * eapply Henv in H2. destruct H2 as [v2' [Hgetx2 Hval]].
        assert (Hval' := Hval). rewrite cc_approx_val_eq in Hval'.
        destruct v2'; try contradiction. simpl in Hval'. inv Hval'.
        inv Hstep2.
        -- destruct v1; try contradiction.
           exists OOT, c2, <0>. split; [| split ]. constructor 1.
           simpl in *; eassumption. eapply Hposttl; eassumption. eauto.
        -- inv H.  repeat subst_exp.
           do 3 eexists. split; [| split ].
           econstructor 2. econstructor; eauto. econstructor; eauto.
           now econstructor; eauto.
           eapply Hposttl. eassumption.
           simpl. rewrite to_nat_add in Hpre2. unfold one in *. eassumption.
  Qed.

  Lemma cc_approx_exp_halt_compat k rho1 rho2 x1 x2 :
    post_OOT' (Ehalt x1) rho1 (Ehalt x2) rho2 P2 ->
    post_base' x1 rho1 x2 rho2 P2 ->
    cc_approx_var_env k PG rho1 rho2 x1 x2 ->
    cc_approx_exp k P2 PG (Ehalt x1, rho1) (Ehalt x2, rho2).
  Proof.
    intros Hoot Hbase Hvar v1 c1 c2 Hleq1 Hstep1. inv Hstep1.
    - (* ΟΟΤ *)
      exists OOT, c1, <0>. split. constructor; eauto.
      split; [| now eauto ]. eapply Hoot; eauto.
    - inv H. edestruct Hvar as [v2' [Hget Hpre]]; eauto.
      repeat eexists. econstructor 2; eauto. econstructor. eassumption.
      rewrite !plus_zero.
      now eapply Hbase; eauto.
      eapply cc_approx_val_monotonic. eassumption. lia.
  Qed.

  Lemma cc_approx_exp_prim_val_compat k rho1 rho2 x1 x2 p e1 e2 :
    post_OOT' (Eprim_val x1 p e1) rho1 (Eprim_val x2 p e2) rho2 P2 ->
    cc_approx_exp k P2 PG (Eprim_val x1 p e1, rho1) (Eprim_val x2 p e2, rho2).
  Proof.
    intros Hoot v1 cin cout Hleq1 Hstep1. inv Hstep1.
    - (* OOT *)
      exists OOT, cin, <0>. split. constructor; eassumption.
      split; [| now eauto ]. eapply Hoot; eauto.
   - inv H.
(*   edestruct cc_approx_var_env_get_list as [vs2 [Hget' Hpre']]; [| eassumption | ]; eauto.
     edestruct Prim_axiom_cc as [v2 [Heq Hprev2]]; eauto.
     edestruct (Hpre (k - 1)) as [v2' [c2 [Hstepv2' [Hpost2 Hprev2']]]]; [ | | | | | | eassumption | ]; eauto.
     simpl in *; lia. simpl in *; lia.
     eexists. exists (c2 + cost (Eprim x2 f ys2 e2)). split; [| split ].
     econstructor 2; eauto. lia.
     econstructor; eauto.
     replace (c2 + cost (Eprim x2 f ys2 e2) - cost (Eprim x2 f ys2 e2)) with c2 by lia.
     eassumption.
     replace cin with (cin - cost (Eprim x1 f ys1 e1) + cost (Eprim x2 f ys2 e2)).
     2:{ simpl in *. eapply Forall2_length in Hall. rewrite Hall. lia. }
     eapply HPost. eassumption.
     eapply cc_approx_res_monotonic. eassumption.
    simpl in *. lia. *)
  Qed.


  Axiom Prim_axiom_cc :
    forall f f' v1,
      M.get f pr = Some f' ->
      forall k S vs1 vs2,
        Forall2 (cc_approx_val k S) vs1 vs2 ->
        f' vs1 = Some v1 ->
        exists v2,
          f' vs2 = Some v2 /\
          cc_approx_val k S v1 v2.

  Lemma cc_approx_exp_prim_compat k rho1 rho2 x1 x2 f ys1 ys2 e1 e2 :
    post_OOT' (Eprim x1 f ys1 e1) rho1 (Eprim x2 f ys2 e2) rho2 P2 ->
    Forall2 (cc_approx_var_env k PG rho1 rho2) ys1 ys2 ->
    (* (forall m v1 v2 vs f',
       m < k ->
       (* needed by the cost proof *)
       get_list ys1 rho1 = Some vs ->
       M.get f pr = Some f' ->
       f' vs = Some v1 ->
       cc_approx_val k PG v1 v2 ->
       cc_approx_exp k P1 PG (e1, M.set x1 v1 rho1)
                     (e2, M.set x2 v2 rho2)) -> *)
    cc_approx_exp k P2 PG (Eprim x1 f ys1 e1, rho1) (Eprim x2 f ys2 e2, rho2).
  Proof.
    intros Hoot Hall v1 cin cout Hleq1 Hstep1. inv Hstep1.
    - (* OOT *)
      exists OOT, cin, <0>. split. constructor; eassumption.
      split; [| now eauto ]. eapply Hoot; eauto.
   - inv H.
(*   edestruct cc_approx_var_env_get_list as [vs2 [Hget' Hpre']]; [| eassumption | ]; eauto.
     edestruct Prim_axiom_cc as [v2 [Heq Hprev2]]; eauto.
     edestruct (Hpre (k - 1)) as [v2' [c2 [Hstepv2' [Hpost2 Hprev2']]]]; [ | | | | | | eassumption | ]; eauto.
     simpl in *; lia. simpl in *; lia.
     eexists. exists (c2 + cost (Eprim x2 f ys2 e2)). split; [| split ].
     econstructor 2; eauto. lia.
     econstructor; eauto.
     replace (c2 + cost (Eprim x2 f ys2 e2) - cost (Eprim x2 f ys2 e2)) with c2 by lia.
     eassumption.
     replace cin with (cin - cost (Eprim x1 f ys1 e1) + cost (Eprim x2 f ys2 e2)).
     2:{ simpl in *. eapply Forall2_length in Hall. rewrite Hall. lia. }
     eapply HPost. eassumption.
     eapply cc_approx_res_monotonic. eassumption.
    simpl in *. lia. *)
  Qed.

  End Compat.

  (** Lift a value predicate to a subset of an environment *)
  Definition lift_P_env (S : Ensemble var) (P : Ensemble val) (rho : env) :=
    forall x v, S x -> M.get x rho = Some v -> P v.

  Lemma lift_P_env_antimon S S' P rho :
    Included _ S S' ->
    lift_P_env S' P rho ->
    lift_P_env S P rho.
  Proof.
    intros H Henv x v HS Hget.
    eapply Henv; eauto. eapply H; eauto.
  Qed.

  Global Instance lift_P_env_proper : Proper (Same_set var ==> eq ==> eq ==> iff) lift_P_env.
  Proof.
    intros S1 S2 Heq B1 B2 Heq' rho1 rho2 Heq''; subst.
    split; intros H x v Hi Hget; (eapply H; [ | now eauto ]);
    now eapply Heq.
  Qed.

  Lemma lift_P_env_Union_l S1 S2 P rho :
    lift_P_env (Union _ S1 S2) P rho ->
    lift_P_env S1 P rho.
  Proof.
    intros H. eapply lift_P_env_antimon; [| now eauto ].
    now apply Included_Union_l.
  Qed.

  Lemma lift_P_env_Union_r S1 S2 P rho :
    lift_P_env (Union _ S1 S2) P rho ->
    lift_P_env S2 P rho.
  Proof.
    intros H. eapply lift_P_env_antimon; [| now eauto ].
    now apply Included_Union_r.
  Qed.

  Lemma lift_P_env_Emtpy_set P rho :
    lift_P_env (Empty_set _) P rho.
  Proof.
    intros x v H. inv H.
  Qed.

  Lemma lift_P_env_extend S P rho x v :
    lift_P_env (Setminus _ S (Singleton _ x)) P rho ->
    P v ->
    lift_P_env S P (M.set x v rho).
  Proof.
    intros H Hp x' v' HS Hget.
    rewrite M.gsspec in Hget.
    destruct (peq x' x); subst.
    - now inv Hget.
    - eapply H; [| eassumption ].
      constructor; eauto. intros Hc. inv Hc. congruence.
  Qed.

  Lemma lift_P_env_set_lists S P rho rho' xs vs :
    lift_P_env (Setminus _ S (FromList xs)) P rho ->
    Forall P vs ->
    set_lists xs vs rho = Some rho' ->
    lift_P_env S P rho'.
  Proof.
    revert S xs rho rho'. induction vs; intros S xs rho rho' Henv Hall Hset.
    - destruct xs; inv Hset.
      rewrite FromList_nil, Setminus_Empty_set_neut_r in Henv.
      eapply Henv; now eauto.
    - destruct xs; try discriminate. inv Hall.
      simpl in Hset. destruct (set_lists xs vs rho) eqn:Heq ; try discriminate.
      inv Hset. eapply lift_P_env_extend; eauto.
      eapply IHvs; eauto.
      now rewrite FromList_cons, <- Setminus_Union in Henv.
  Qed.

  Lemma lift_P_env_def_funs S P B B' rho  :
    lift_P_env (Setminus _ S (name_in_fundefs B)) P rho ->
    (forall f, P (Vfun rho B' f)) ->
    lift_P_env S P (def_funs B' B rho rho).
  Proof.
    revert S rho. induction B; intros S rho Henv Hfun.
    - simpl. eapply lift_P_env_extend; [| now eauto ].
      eapply IHB; [| eassumption ].
      eapply lift_P_env_antimon; [| eassumption ].
      rewrite Setminus_Union. now eapply Included_refl.
    - now rewrite Setminus_Empty_set_neut_r in Henv.
  Qed.

  Lemma lift_P_env_get S P rho x v :
    lift_P_env S P rho ->
    Included _ (Singleton _ x) S ->
    M.get x rho = Some v ->
    P v.
  Proof.
    intros Henv HS Hget. eapply Henv; eauto.
    now eapply HS; eauto.
  Qed.

  Lemma lift_P_env_get_list S P rho xs vs :
    lift_P_env S P rho ->
    Included _ (FromList xs) S ->
    get_list xs rho = Some vs ->
    Forall P vs.
  Proof.
    revert S xs rho. induction vs; intros S xs rho Henv Hincl Hget.
    - eauto.
    - destruct xs; try discriminate. simpl in Hget.
      destruct (M.get v rho) eqn:Heq; try discriminate.
      destruct (get_list xs rho) eqn:Heq'; try discriminate.
      inv Hget. rewrite FromList_cons in Hincl.
      constructor.
      + eapply lift_P_env_get; eauto.
        eapply Included_trans; [| now eauto ].
        eapply Included_Union_l.
      + eapply IHvs; eauto.
        eapply Included_trans; [| now eauto ].
        eapply Included_Union_r.
  Qed.

  Lemma Forall_nthN {A} (R : A -> Prop) l n v :
    Forall R l ->
    nthN l n = Some v ->
    R v.
  Proof.
    revert n. induction l; intros n Hall Hnth; [ discriminate |].
    inv Hall. simpl in Hnth.
    destruct n.
    - inv Hnth; eauto.
    - eapply IHl; eauto.
  Qed.

  Section Compose.

    Context (P1 P2 : @PostT fuel trace) (* Local *)
            (PG  : @PostGT fuel trace) (* Global *)
            (Hprops : Post_properties cenv PG PG PG)
            (HGPost : inclusion _ (comp P1 P2) PG)
            (Hp1 : inclusion _ PG P1)
            (Hp2 : inclusion _ PG P2).


    Lemma cc_approx_res_respects_preord_exp_r_pre (k : nat) r1 r2 r3 :
      (forall j v1 v2 v3,
          j <= k ->
          cc_approx_val j PG v1 v2 ->
          (forall k, preord_val cenv PG k v2 v3) ->
          cc_approx_val j PG v1 v3) ->
      cc_approx_res cc_approx_val k PG r1 r2 ->
      (forall k', preord_res (preord_val cenv) PG k' r2 r3) ->
      cc_approx_res cc_approx_val k PG r1 r3.
    Proof.
      intros Hyp H1 H2;
      assert (H2' := H2 0); destruct r1; destruct r2; destruct r3; try contradiction; eauto.
      simpl. eapply Hyp; eauto.
    Qed.

    Lemma cc_approx_exp_respects_preord_exp_r_pre (k : nat)
          (rho1 rho2 rho3 : env) (e1 e2 e3 : exp) :
      (forall j v1 v2 v3,
          j <= k ->
          cc_approx_val j PG v1 v2 ->
          (forall k, preord_val cenv PG k v2 v3) ->
          cc_approx_val j PG v1 v3) ->
      cc_approx_exp k P1 PG (e1, rho1) (e2, rho2) ->
      (forall k', preord_exp cenv P2 PG k' (e2, rho2) (e3, rho3)) ->
      cc_approx_exp k (comp P1 P2) PG (e1, rho1) (e3, rho3).
    Proof.
      intros IH Hexp1 Hexp2 v1 c Hleq1 Hstep1 Hns.
      edestruct Hexp1 as [v2 [c2 [c2' [Hstep2 [HS Hpre2]]]]]; eauto.
      edestruct (Hexp2 (to_nat c2)) as [v3 [c3 [c3' [Hstep3 [HS' Hpre3]]]]]; [| eassumption | ].
      lia. do 3 eexists; repeat split; eauto. eexists; split; eauto.
      eapply cc_approx_res_respects_preord_exp_r_pre.
      intros. eapply IH; eauto. lia. eassumption.
      intros m.
      edestruct (Hexp2 (m + to_nat c2)) with (cin := c2)
        as [v3' [c4 [c4' [Hstep3' [Hpost3 Hpre3']]]]]; [| eauto |]. lia.
      destruct v1; destruct v2; destruct v3; destruct v3'; try contradiction; eauto.
      eapply bstep_fuel_deterministic in Hstep3; [| eapply Hstep3' ]. inv Hstep3.
      eapply preord_val_monotonic. eauto. lia.
    Qed.

  (* TODO move *)
  Lemma occurs_free_closed_fundefs f tau xs e B :
    fun_in_fundefs B (f, tau, xs, e) ->
    closed_fundefs B ->
    Included _ (occurs_free e) (Union _ (FromList xs) (name_in_fundefs B)).
  Proof.
    intros H Hcl.
    eapply Included_trans. now eapply occurs_free_in_fun; eauto.
    unfold closed_fundefs in Hcl. rewrite Hcl, Union_Empty_set_neut_r.
    eapply Included_refl.
  Qed.

  Lemma cc_approx_val_respects_preord_val_r (k : nat) (v1 v2 v3 : val) :
    cc_approx_val k PG v1 v2 ->
    (forall k, preord_val cenv PG k v2 v3) ->
    cc_approx_val k PG v1 v3.
  Proof.
    revert v1 v2 v3. induction k using lt_wf_rec.
    induction v1 using val_ind'; intros v2 v3 Happrox Hpre;
    assert (Hpre' := Hpre k);
    rewrite cc_approx_val_eq, preord_val_eq in *.
    - destruct v2; try contradiction.
      destruct v3; try contradiction.
      inv Happrox; inv Hpre'. inv H1; inv H2. split; eauto.
    - destruct v2; try contradiction.
      destruct v3; try contradiction.
      destruct l0; [now inv Happrox; inv H1 |].
      destruct l1; [now inv Hpre'; inv H1 |].
      inv Hpre'; inv Happrox. inv H1; inv H2; split; eauto.
      constructor; eauto.
      + eapply IHv1; [ now eauto |].
        intros k'. specialize (Hpre k').
        rewrite preord_val_eq in Hpre. inv Hpre. now inv H1.
      + assert (Hsuf : cc_approx_val' k PG (Vconstr c0 l) (Vconstr c0 l1)).
        { rewrite <- cc_approx_val_eq.
          eapply IHv0 with (v2 := Vconstr c0 l0).
          - rewrite cc_approx_val_eq. now split; eauto.
          - intros k'. specialize (Hpre k'). rewrite preord_val_eq in Hpre.
            inv Hpre. inv H1. rewrite preord_val_eq. now split; eauto. }
        now inv Hsuf.
    - destruct v2, v3; try contradiction.
      destruct l; try contradiction.
      destruct v0, l; try contradiction.
      destruct v1; try contradiction.
      inversion Hpre' as [Hleq Hall]. clear Hpre'. inv Hall.
      rewrite preord_val_eq in H2. inv H4.
      rewrite preord_val_eq in H3.
      destruct y, y0; try contradiction. simpl.
      destruct l; try contradiction.
      destruct Happrox as [Heq1 Happrox]; subst. inv H6. split; eauto.
      intros vs1 vs2 j t1' xs1 e1 rho1 Heq1 Hfind1 Hset1.
      edestruct (Happrox vs1 vs2) as [Γ [xs2 [e2 [rho2' [Hfind2 [Hset2 Heval2]]]]]]; eauto.
      subst.
      edestruct (H2 (Vconstr c1 l1 :: vs2) (Vconstr c l0 :: vs2)) with (j := 0) as
          [xs3' [e3 [rho3 [Hfind3 [Hset3 _]]]]]; eauto.
      edestruct xs3' as [| Γ' xs3]; try discriminate.
      do 4 eexists. repeat split; eauto.
      intros Hlt Hall.
      eapply cc_approx_exp_rel_mon.
      eapply cc_approx_exp_respects_preord_exp_r_pre
        with (e2 := e2) (rho2 := rho2').
      + intros. eapply H; [ lia | eassumption | eassumption ].
      + eapply cc_approx_exp_rel_mon.
        eapply Heval2. lia. assumption.
        intros ? ? ?. eauto.
      + intros k'. specialize (Hpre (k'+1)). rewrite preord_val_eq in Hpre.
        inversion Hpre as [_ Hall']. clear Hpre. inv Hall'.
        rewrite preord_val_eq in H5.
        edestruct (H5 (Vconstr c1 l1 :: vs2) (Vconstr c l0 :: vs2)) as
            [xs3'' [e3' [rho4 [Hfind3' [Hset3' Heval3']]]]]; eauto.
        rewrite Hfind3' in Hfind3. inv Hfind3.
        rewrite <- Hset3 in Hset3'. inv Hset3'.
        eapply preord_exp_post_monotonic; [| eapply Heval3' ].
        intros ? ? ?. eauto.
        lia. inv H7. constructor.
        eapply preord_val_monotonic. eassumption. lia.
        eapply List_util.Forall2_refl. eapply preord_val_refl; eauto.
      + eauto.
    - destruct v2; try contradiction.
      destruct v3; try contradiction. inv Happrox.
      inv Hpre'. reflexivity.
    - destruct v2; try contradiction.
      destruct v3; try contradiction. inv Happrox.
      inv Hpre'. reflexivity.
  Qed.

  Corollary cc_approx_exp_respects_preord_exp_r (k : nat)
        (rho1 rho2 rho3 : env) (e1 e2 e3 : exp) :
    cc_approx_exp k P1 PG (e1, rho1) (e2, rho2) ->
    (forall k', preord_exp cenv P2 PG k' (e2, rho2) (e3, rho3)) ->
    cc_approx_exp k (comp P1 P2) PG (e1, rho1) (e3, rho3).
  Proof.
    eapply cc_approx_exp_respects_preord_exp_r_pre.
    now intros; eapply cc_approx_val_respects_preord_val_r; eauto.
  Qed.


  (* Sadly, composing with the preord relation on the left doesn't seem provable *)

  Lemma cc_approx_exp_respects_preord_exp_l (rho1 rho2 rho3 : env) (e1 e2 e3 : exp) k:
    (forall k, preord_exp cenv P1 PG k (e1, rho1) (e2, rho2)) ->
    cc_approx_exp k P2 PG (e2, rho2) (e3, rho3) ->
    cc_approx_exp k (comp P1 P2) PG (e1, rho1) (e3, rho3).
  Proof.
    intros Hyp1 Hyp2 v c1 c2 Hleq Hstep1.
    edestruct (Hyp1 k) as (v2 & c3 & c4 & Hstep2 & Hpost & Hv2). eassumption. eassumption.
  Abort.

  Lemma cc_approx_val_respects_preord_val_l (v1 v2 v3 : val) :
    (forall k, preord_val cenv PG k v1 v2) ->
    (forall k, cc_approx_val k PG v2 v3) ->
    (forall k, cc_approx_val k PG v1 v3).
  Proof.
    intros H1 H2 k.
    revert v1 v2 v3 H1 H2. induction k as [k IHK] using lt_wf_rec.
    induction v1 using val_ind'; intros v2 v3 Hpre Happrox;
      assert (Hpre' := Hpre k);
      assert (Happrox' := Happrox k);
      rewrite cc_approx_val_eq, preord_val_eq in *.
    - admit.
    - admit.
    - destruct v2; try contradiction.
      destruct v3; try contradiction.
      destruct l. now inv Happrox'.
      simpl in Happrox'.
      destruct v1; try contradiction.
      destruct l. now inv Happrox'.
      destruct v2; try contradiction.
(*
      intros vs1 vs2 i t2 xs1 e1 rho1 Hleneq Hfdef Hset.
      simpl in Hpre'.
      edestruct (Hpre' vs1 vs1) as [xs2' [e2 [rho2 [Hfind2 [Hset2 _]]]]]; eauto.
      edestruct (Happrox' vs1 vs2) with (j := i)
        as [Γ [xs3' [e3 [rho3 [Heq [Hfind3 [Hset3 Heval3]]]]]]]; eauto.
      subst.
      do 4 eexists. split; [| split; [| split ] ]; eauto.
      intros Hlt Hall.
*)

  Abort.


  End Compose.

  Section Divergence.


    Lemma cc_approx_exp_preserves_divergence
          (P : @PostT fuel trace)
          (PG : @PostGT fuel trace) e1 rho1 e2 rho2
          (Hrel : post_upper_bound P) :
      (forall k, cc_approx_exp k P PG (e1, rho1) (e2, rho2)) ->
      @diverge cenv fuel _ trace _ rho1 e1 ->
      @diverge cenv fuel _ trace _ rho2 e2.
    Proof.
      intros Hexp Hdiv. assert (Hdiv' := Hdiv).
      specialize (Hrel e1 rho1 e2 rho2). inv Hrel.
      intros c2.
      specialize (Hdiv (x c2)). destructAll.
      edestruct Hexp as [v2 [c2' [cout2 [Hs2 [Hp Hval]]]]].
      reflexivity. eassumption.
      destruct v2; try contradiction.
      eapply H in Hp. inv Hp.
      eapply bstep_fuel_OOT_monotonic in Hs2. destructAll. eexists. eassumption.
    Qed.

    Lemma cc_approx_exp_preserves_not_stuck
          (P : @PostT fuel trace)
          (PG : @PostGT fuel trace) e1 rho1 e2 rho2
          (Hrel : post_upper_bound P) :
      (forall k, cc_approx_exp k P PG (e1, rho1) (e2, rho2)) ->
      @not_stuck cenv fuel _ trace _ rho1 e1 ->
      @not_stuck cenv fuel _ trace _ rho2 e2.
    Proof.
      intros Hexp Hns. assert (Hns' := Hns). inv Hns.
      - destructAll.
        edestruct Hexp as [v2 [c2' [cout' [Hs2 [Hp Hval]]]]].
        reflexivity. eassumption.

        destruct v2; try contradiction.
        left. now eauto.
      - right. eapply cc_approx_exp_preserves_divergence; eassumption.
    Qed.

  End Divergence.


  (* More environment lemmas *)

  Lemma cc_approx_val_cc_appox_var_env k P rho1 rho2 x y v1 v2 :
    M.get x rho1 = Some v1 -> M.get y rho2 = Some v2 ->
    cc_approx_val k P v1 v2 ->
    cc_approx_var_env k P rho1 rho2 x y.
  Proof.
    intros Hget1 Hget2 Hcc.
    intros v1' Hget1'. rewrite Hget1 in Hget1'. inv Hget1'.
    firstorder.
  Qed.

  Lemma Forall2_cc_approx_var_env k P rho1 rho2 l1 l2 vs1 vs2 :
    get_list l1 rho1 = Some vs1 ->
    get_list l2 rho2 = Some vs2 ->
    Forall2 (cc_approx_val k P) vs1 vs2 ->
    Forall2 (cc_approx_var_env k P rho1 rho2) l1 l2.
  Proof.
    revert vs1 l2 vs2; induction l1; intros vs1 l2 vs2  Hget1 Hget2 Hall.
    - destruct vs1; try discriminate.
      inv Hall. destruct l2; try discriminate.
      now constructor.
      simpl in Hget2. destruct (M.get e rho2); try discriminate.
      destruct (get_list l2 rho2); try discriminate.
    - simpl in Hget1.
      destruct (M.get a rho1) eqn:Hgeta; try discriminate.
      destruct (get_list l1 rho1) eqn:Hgetl; try discriminate.
      inv Hget1.
      inv Hall.
      destruct l2; try discriminate. simpl in Hget2.
      destruct (M.get e rho2) eqn:Hgeta'; try discriminate.
      destruct (get_list l2 rho2) eqn:Hgetl'; try discriminate.
      inv Hget2. constructor; eauto.
      eapply cc_approx_val_cc_appox_var_env; eauto.
  Qed.

  (** Lemmas about evaluation contexts *)

  (** [(e1, ρ1) < (C [ e2 ], ρ2)] if [(e1, ρ1) < (e2, ρ2')], where [ρ2'] is the
      interpretation of [C] in [ρ2] *)
  Lemma ctx_to_rho_cc_approx_exp k (P : nat -> PostT) boundG rho1 rho2 rho2' C e e' m :
    (forall n e1 rho1 cin1 cout1 e2 rho2 rho2' cin2 cout2 C,
        ctx_to_rho C rho2 rho2' ->
        P (n + to_nat (one_ctx C)) (e1, rho1, cin1, cout1) (e2, rho2', cin2, cout2) ->
        P n (e1, rho1, cin1, cout1) (C|[ e2 ]|, rho2, cin2 <+> one_ctx C, cout2 <+> one_ctx C)) ->

    ctx_to_rho C rho2 rho2' ->
    cc_approx_exp k (P (m + exp_ctx_len C)) boundG (e, rho1) (e', rho2') ->
    cc_approx_exp k (P m) boundG (e, rho1) (C |[ e' ]|, rho2).
  Proof.
    intros H1 Hctx Hcc. revert m Hcc; induction Hctx; intros m Hcc.
    - intros v1' c1 Hleq1 Hstep1 Hns.
      edestruct Hcc as [v2' [c2 [Hstep2 [Hub Hcc2]]]]; try eassumption.
      simpl in *. rewrite Nat_as_OT.add_0_r in *. firstorder.
    - intros v1 c1 Hleq1 Hstep1 Hns.
      edestruct IHHctx as [v2 [c2 [c3 [Hstep2 [HP Hcc2]]]]]; try eassumption.
      simpl exp_ctx_len in Hcc.
      replace (m + S (exp_ctx_len C)) with ((m + 1) + (exp_ctx_len C)) in Hcc by lia.
      eassumption.
      eexists. eexists (c2 <+> one (Eproj_c y t N Γ C |[ e' ]|)). eexists. split; [| split ].
      constructor 2; eauto. econstructor; eauto.
      simpl. eapply H1 with (C := Eproj_c y t N Γ Hole_c); eauto.
      econstructor; eauto. now econstructor.
      simpl. unfold one_ctx. simpl. rewrite to_nat_one. eassumption.
      eassumption.
    - intros v1' c1 Hleq1 Hstep1 Hns.
      edestruct IHHctx as [v2' [c2 [c3 [Hstep2 [Hub Hcc2]]]]]; try eassumption.

      simpl exp_ctx_len in Hcc.
      replace (m + S (exp_ctx_len C)) with ((m + 1 + exp_ctx_len C)) in Hcc by lia.
      eassumption.
      eexists. eexists (c2 <+> one (Econstr_c x t ys C |[ e' ]|)). eexists. split; [| split ].
      constructor 2; eauto. econstructor; eauto.
      simpl. eapply H1 with (C := Econstr_c x t ys Hole_c); eauto.
      econstructor; eauto. now econstructor.
      unfold one_ctx. rewrite to_nat_one. simpl. eassumption. eassumption.
    - intros v1' c1 Hleq1 Hstep1 Hns.
      edestruct IHHctx as [v2' [c2 [c3 [Hstep2 [Hub Hcc2]]]]]; try eassumption.

      simpl exp_ctx_len in Hcc.
      replace (m + S (exp_ctx_len C)) with (m + 1 + exp_ctx_len C) in Hcc by lia.
      eassumption.

      eexists. eexists (c2 <+> one (Efun1_c B C |[ e' ]|)). eexists. split; [| split ].
      constructor 2; eauto. econstructor; eauto.
      simpl. eapply H1 with (C := Efun1_c B Hole_c); eauto.
      econstructor; eauto. now econstructor.
      unfold one_ctx. rewrite to_nat_one. simpl. eassumption. eassumption.
  Qed.

  Lemma cc_approx_exp_ctx_to_rho k (P : nat -> @PostT fuel trace) boundG rho1 rho2 rho2' C e e' m :
    (forall n e1 rho1 e2 rho2 rho2' (cin1 cin2 : fuel) (cout1 cout2 : trace) C,
        ctx_to_rho C rho2 rho2' ->
        P n (e1, rho1, cin1, cout1) (C|[ e2 ]|, rho2, cin2 <+> one_ctx C, cout2 <+> one_ctx C) ->
        P (n + to_nat (one_ctx C)) (e1, rho1, cin1, cout1) (e2, rho2', cin2, cout2)) ->
    (forall m e2 rho2 rho2' (cin1 cin2 : fuel) (cout1 cout2 : trace) C,
        ctx_to_rho C rho2 rho2' ->
        P m (e, rho1, cin1, cout1) (C |[ e2 ]|, rho2, cin2, cout2) ->
        P (m + to_nat (one_ctx C)) (e, rho1, cin1, cout1) (e2, rho2', cin2, cout2)) ->
    ctx_to_rho C rho2 rho2' ->
    cc_approx_exp k (P m) boundG (e, rho1) (C |[ e' ]|, rho2) ->
    cc_approx_exp k (P (m + exp_ctx_len C)) boundG (e, rho1) (e', rho2').
  Proof.
    intros H1 H2 Hctx Hcc. revert m Hcc; induction Hctx; intros m Hcc.
    - intros v1' c1 c1' Hleq1 Hstep1.
      edestruct Hcc as [v2' [c2 [Hstep2 [Hub Hcc2]]]]; try eassumption.
      simpl in *. rewrite Nat_as_OT.add_0_r in *. firstorder.
    - simpl exp_ctx_len.
      replace (m + S (exp_ctx_len C)) with ((m + 1) + (exp_ctx_len C)) by lia.
      eapply IHHctx; eauto.
      + intros v1 c1 c1' Hleq1 Hstep1.
        edestruct Hcc as [v2 [c2 [c2' [Hstep2 [Hub Hcc2]]]]]; try eassumption.
        inv Hstep2; repeat subst_exp.
        * destruct v1; try contradiction.
          (* eapply lt_zero_one in H3. subst. *)
          eexists OOT, c2, <0>. split. econstructor; eauto.
          unfold one; erewrite one_eq. eassumption.
          split.
          -- erewrite <- (@to_nat_one _ fuel _). eapply H2 with (C := Eproj_c y t N Γ Hole_c); try eassumption.
             econstructor; eauto. now econstructor.
          -- simpl. eassumption.
        * inv H3. do 3 eexists. repeat subst_exp.
          split. eassumption. split.
          erewrite <- (@to_nat_one _ fuel _).
          eapply H1 with (C := Eproj_c y t N Γ Hole_c); try eassumption.
          econstructor; eauto. now econstructor. eassumption.
    - simpl .
      replace (m + S (exp_ctx_len C)) with ((m + 1) + (exp_ctx_len C)) by lia.
      eapply IHHctx; eauto.
      intros v1' c1' Hleq1 Hstep1 Hns.
      edestruct Hcc as [v2' [c2' [c3' [Hstep2 [Hub Hcc2]]]]]; try eassumption.
      inv Hstep2; simpl in *; repeat subst_exp.
      + destruct v1'; try contradiction.
        eexists OOT, c2', <0>. split. econstructor; eauto. unfold one. erewrite one_eq. eassumption.
        split.
        erewrite <- (@to_nat_one _ fuel _). eapply H2 with (C := Econstr_c x t ys Hole_c).
        econstructor; eauto. now econstructor.
        simpl. eassumption. eassumption.
      + inv H0. repeat subst_exp. do 3 eexists. split. eassumption.
        split.
        erewrite <- (@to_nat_one _ fuel). eapply H1 with (C := Econstr_c x t ys Hole_c); try eassumption.
        econstructor; eauto. now econstructor. simpl.
        eassumption.
    - simpl exp_ctx_len.
      replace (m + S (exp_ctx_len C)) with (m + 1 + exp_ctx_len C) by lia.
      eapply IHHctx; eauto.
      intros v1' c1' c2' Hleq1 Hstep1.
      edestruct Hcc as [v2' [c3 [c3' [Hstep2 [Hub Hcc2]]]]]; try eassumption.
      inv Hstep2; simpl in *; repeat subst_exp.
      + destruct v1'; try contradiction.
        eexists OOT, c3, <0>. split. econstructor; eauto. unfold one. erewrite one_eq. eassumption.

        split.
        erewrite <- to_nat_one. eapply H2 with (C := Efun1_c B Hole_c).
        econstructor; eauto. now econstructor.
        simpl. eassumption.
        simpl; eauto.
      + inv H. repeat subst_exp. do 3 eexists. split. eassumption.
        split.
        erewrite <- to_nat_one. eapply H1 with (C := Efun1_c B Hole_c); try eassumption.
        econstructor; eauto. now econstructor. simpl.
        eassumption.

  Qed.

  Lemma leq_sum_exists A B C:
    A <= B + C ->
    exists B' C', A = B' + C' /\ B' <= B /\ C' <= C.
  Proof.
    revert B C. induction A; intros B C Hleq.
    - eexists 0, 0. split; eauto. split; lia.
    - destruct B; destruct C.
      + lia.
      + assert (Hleq' : A <= 0 + C) by lia.
        edestruct IHA as [B' [C' [Heq1 [Hl1 Hl2]]]]. eassumption.
        subst. eexists 0. eexists (S C'). split; lia.
      + assert (Hleq' : A <= B + 0) by lia.
        edestruct IHA as [B' [C' [Heq1 [Hl1 Hl2]]]]. eassumption.
        subst. eexists (S B'). eexists 0. destruct C'; try lia.
      + assert (Hleq' : A <= S B + C) by lia.
        edestruct IHA as [B' [C' [Heq1 [Hl1 Hl2]]]]. eassumption.
        subst. eexists B'. eexists (S C').
        split; try lia.
  Qed.

  (*
  Lemma ctx_to_rho_cc_approx_exp_left_weak k P1 P2 boundG rho1 rho1' rho2 C e e' :
    (* This is very specific to what holds currently for CC *)
    (* forall c1 c2 m a b, b <= 7 * a -> P m c1 c2 -> P (m + b) (c1 + a) c2) -> *)
    ctx_to_rho C rho1 rho1' ->
    cc_approx_exp k P1 boundG (e, rho1') (e', rho2) ->
    cc_approx_exp k P2 boundG (C|[ e ]|, rho1) (e', rho2).
  Proof.
    intros Hctx. induction Hctx.
    - intros H1. eapply cc_approx_exp_rel_mon. eassumption.
      admit.
    - intros v1 c1 Hleq1 Hstep1.
      edestruct Hcc as [v2' [c2 [Hstep2 [Hub Hcc2]]]]; try eassumption.
      simpl in *. do 2 eexists; split; eauto. split; eauto.
      rewrite (plus_n_O c1). eapply H1; eauto.
    - intros v1 c1 Hleq1 Hstep1. simpl in Hstep1. inv Hstep1; repeat subst_exp.
      + assert (Hc1 : c1 = 0) by (simpl in *; lia); subst.
        eexists OOT, 0. split. constructor; eauto. eapply cost_gt_0.
        split. eapply
        assert (Heq' : exists B D, A = B + D /\ B <= 7 * exp_ctx_len C /\ D <= 7).
        { revert Hleq. clear. intros Hleq.
          destruct A. eexists 0, 0. split; eauto. split; lia.
        assert (Heq : A <= 7 * (exp_ctx_len C) + 6) by (simpl in *; lia).
        destruct (Nat_as_DT.le_decidable A (7 * (exp_ctx_len C))).
        + eexists A, 1. split; eauto. lia. split; eauto.
          lia.
        + eexists (7 * exp_ctx_len C).
          eexists (S A - 7 * exp_ctx_len C).
          split. lia. split. lia. lia. }
      edestruct Heq' as [B [D [Heq [HeqB HleqD]]]]. subst.
      edestruct IHHctx with (A := B) as [v2 [c2 [Hstep2 [HP Hcc2]]]];
        [ | | | | eassumption | ].
      intros. now eapply H1; eauto.
      simpl in *. lia.
      eassumption.
      lia.
      repeat eexists. eassumption.
      replace (m + (B + D)) with (m + B + D) by lia. eapply H1; eauto.
      eapply cc_approx_val_monotonic. eassumption. lia.
    - intros v1' c1 Hleq1 Hstep1. inv Hstep1. repeat subst_exp.
      assert (Heq'' : exists B D, A = B + D /\ B <= 7 * exp_ctx_len C /\ D <= 7 + 7 * @List.length var ys).
      { eapply leq_sum_exists. simpl in *; lia. }
      destruct Heq'' as [B [D [Heq [Hleqb Hleqd]]]]. subst.

      edestruct IHHctx with (A := B)
        as [v2' [c2 [Hstep2 [Hub Hcc2]]]]; [ eassumption | | eassumption | | eassumption | ].
      eassumption. lia.
      repeat eexists. eassumption.
      rewrite (plus_assoc m). rewrite <- (plus_assoc c).
      eapply H1. eauto. lia. eassumption.
      eapply cc_approx_val_monotonic. eassumption. lia.
    - intros v1' c1 Hleq1 Hstep1. inv Hstep1. repeat subst_exp.
      simpl in Hleq.
      pose (cost := 1 + PS.cardinal (fundefs_fv B)).
      assert (Heq'' : exists B D, A = B + D /\ B <= 7 * exp_ctx_len C /\ D <= 7*cost).
      { eapply leq_sum_exists. simpl in *; lia. }
      destruct Heq'' as [B' [D [Heq [Hleqb Hleqd]]]]. subst.

      edestruct IHHctx with (A := B')
        as [v2' [c2 [Hstep2 [Hub Hcc2]]]]; [ eassumption | | eassumption | | eassumption | ].
      eassumption. lia.
      repeat eexists. eassumption.
      rewrite (plus_assoc m).
      eapply H1; eauto.
       eapply cc_approx_val_monotonic. eassumption. lia.
  Qed.

  Lemma ctx_to_rho_cc_approx_exp_left k (P : nat -> relation nat) boundG rho1 rho1' rho2 C e e' m A :
    (* This is very specific to what holds currently for CC *)
    (forall c1 c2 m a b, a <= b <= 7 * a -> P m c1 c2 -> P (m + b) (c1 + a) c2) ->
    ctx_to_rho C rho1 rho1' ->
    exp_ctx_len C <= A <= 7 * exp_ctx_len C ->
    cc_approx_exp k (P m) boundG (e, rho1') (e', rho2) ->
    cc_approx_exp k (P (m + A)) boundG (C|[ e ]|, rho1) (e', rho2).
  Proof.
    intros H1 Hctx Hcc; revert m A rho2 H1 Hcc; induction Hctx;
      intros m A rho2 H1 Hleq Hcc.
    - intros v1 c1 Hleq1 Hstep1.
      edestruct Hcc as [v2' [c2 [Hstep2 [Hub Hcc2]]]]; try eassumption.
      simpl in *. do 2 eexists; split; eauto. split; eauto.
      rewrite (plus_n_O c1). eapply H1; eauto.
    - intros v1 c1 Hleq1 Hstep1. simpl in Hstep1. inv Hstep1. repeat subst_exp.
      assert (Heq' : exists B D, A = B + D /\ exp_ctx_len C <= B <= 7 * exp_ctx_len C /\ 1 <= D <= 7).
      { revert Hleq. clear. intros Hleq.
        destruct A; try (simpl in *; lia). simpl in Hleq.
        assert (Heq : exp_ctx_len C <= A <= 7 * (exp_ctx_len C) + 6) by lia.
        clear Hleq.
        destruct (Nat_as_DT.le_decidable A (7 * (exp_ctx_len C))).
        + eexists A, 1. split; eauto. lia. split; eauto.
          lia. lia.
        + eexists (7 * exp_ctx_len C).
          eexists (S A - 7 * exp_ctx_len C).
          split. lia. split. lia. lia. }
      edestruct Heq' as [B [D [Heq [HeqB HleqD]]]]. subst.
      edestruct IHHctx with (A := B) as [v2 [c2 [Hstep2 [HP Hcc2]]]];
        [ | | | | eassumption | ].
      intros. now eapply H1; eauto.
      simpl in *. lia.
      eassumption.
      lia.
      repeat eexists. eassumption.
      replace (m + (B + D)) with (m + B + D) by lia. eapply H1; eauto.
      eapply cc_approx_val_monotonic. eassumption. lia.
    - intros v1' c1 Hleq1 Hstep1. inv Hstep1. repeat subst_exp.
      assert (Heq' : exists B, A = B + (1 + @List.length var ys)).
      { simpl in *. eexists (A - S (Datatypes.length ys)).
        rewrite NPeano.Nat.sub_add. lia. simpl in *. lia. }
      destruct Heq' as [B' Hbeq].
      assert (Heq'' : exists B D, A = B + D /\ exp_ctx_len C <= B <= 7 * exp_ctx_len C /\
                             1 + @List.length var ys <= D <= 7 + 7 * @List.length var ys).
      { revert Hbeq Hleq. clear. intros Hbeq Hleq. subst.
        assert (Heq : exp_ctx_len C <= B' <= 7 * (exp_ctx_len C) + (6 + 6 * @List.length var ys))
          by (simpl in *; lia).
        clear Hleq.
        destruct (Nat_as_DT.le_decidable B' (7 * (exp_ctx_len C))).
        + eexists B'. eexists. split; eauto. split. lia. lia.
        + eexists (7 * exp_ctx_len C).
          eexists (1 + @List.length var ys + B' - 7 * exp_ctx_len C).
          split. lia. split. lia. lia. }
      clear Hbeq.
      destruct Heq'' as [B [D [Heq [Hleqb Hleqd]]]]. subst.

      edestruct IHHctx with (A := B)
        as [v2' [c2 [Hstep2 [Hub Hcc2]]]]; [ eassumption | | eassumption | | eassumption | ].
      eassumption. lia.
      repeat eexists. eassumption.
      rewrite (plus_assoc m). rewrite <- (plus_assoc c).
      eapply H1. eauto. lia. eassumption.
      eapply cc_approx_val_monotonic. eassumption. lia.
    - intros v1' c1 Hleq1 Hstep1. inv Hstep1. repeat subst_exp.
      simpl in Hleq.
      pose (cost := 1 + PS.cardinal (fundefs_fv B)).
       assert (Heq' : exists B, A = B + cost).
       { simpl in *. eexists (A - cost).
         rewrite NPeano.Nat.sub_add. lia. lia. }
      assert (Heq'' : exists B D, A = B + D /\ exp_ctx_len C <= B <= 7 * exp_ctx_len C /\
                             cost <= D <= 7*cost).
       { destruct Heq' as [B' Hbeq].
         revert Hbeq Hleq. clear. intros Hbeq Hleq. subst.
         assert (Heq : exp_ctx_len C <= B' <= 7 * (exp_ctx_len C) + 6*cost)
           by (simpl in *; lia).
        clear Hleq.
        destruct (Nat_as_DT.le_decidable B' (7 * (exp_ctx_len C))).
        + eexists B'. eexists. split; eauto. split. lia. lia.
        + eexists (7 * exp_ctx_len C).
          eexists (cost + B' - 7 * exp_ctx_len C).
          split. lia. split. lia. lia. }
       clear Heq'.
       destruct Heq'' as [B' [D [Heq [Hleqb Hleqd]]]]. subst.

       edestruct IHHctx with (A := B')
         as [v2' [c2 [Hstep2 [Hub Hcc2]]]]; [ eassumption | | eassumption | | eassumption | ].
       eassumption. lia.
       repeat eexists. eassumption.
       rewrite (plus_assoc m).
       eapply H1; eauto.
       eapply cc_approx_val_monotonic. eassumption. lia.
  Qed.
*)

  (*
  Lemma cc_approx_exp_rel_conj k P1 P2 P rho1 rho2 e1 e2 :
    cc_approx_exp k P1 P (e1, rho1) (e2, rho2) ->
    cc_approx_exp k P2 P (e1, rho1) (e2, rho2) ->
    cc_approx_exp k (fun c1 c2 => P1 c1 c2 /\ P2 c1 c2) P (e1, rho1) (e2, rho2).
  Proof.
    intros Hcc1 Hcc2 v c Hlt Hstep.
    edestruct Hcc1 as [v1 [c1 [Hstep1 [HP1 Hv1]]]]; eauto.
    edestruct Hcc2 as [v2 [c2 [Hstep2 [HP2 Hv2]]]]; eauto.
    destruct v; destruct v2; try contradiction.
    - destruct v1; try contradiction. do 2 eexists. split. eassumption. split; eauto.
      split; eauto.

    eapply bstep_fuel_deterministic in Hstep1. ; eauto. inv Hstep1.
    firstorder.
  Qed.  *)

  (* The following are obsolete *)
  (* TODO: move to identifiers.v *)
  Inductive closed_fundefs_in_val : val -> Prop :=
  | Vconstr_closed :
      forall t vs,
        Forall closed_fundefs_in_val vs ->
        closed_fundefs_in_val (Vconstr t vs)
  | Vfun_closed :
      forall rho B f,
        closed_fundefs B ->
        closed_fundefs_in_fundefs B ->
        (* fun_in_fundefs B (f, tau, xs, e) -> *)
        (* Included _ (occurs_free e) (Union _ (FromList xs) (name_in_fundefs B)) -> *)
        closed_fundefs_in_val (Vfun rho B f)
  | Vint_closed :
      forall z, closed_fundefs_in_val (Vint z)
  | Vprim_closed : forall p, closed_fundefs_in_val (Vprim p).

  Definition closed_fundefs_in_env (S : Ensemble var) rho : Prop :=
    lift_P_env S closed_fundefs_in_val rho.

  Lemma fun_in_fundefs_funs_in_fundef B B' f t xs e :
    fun_in_fundefs B (f, t, xs, e) ->
    funs_in_exp B' e ->
    funs_in_fundef B' B.
  Proof.
    induction B; intros Hin Hfuns.
    - inv Hin.
      + inv H. now eauto.
      + constructor 2. eapply IHB; eauto.
    - inv Hin.
  Qed.

  Axiom prims_closed_fundefs :
    forall (f : prim) (f' : list val -> option val) vs v,
      M.get f pr = Some f' ->
      Forall closed_fundefs_in_val vs ->
      f' vs = Some v ->
      closed_fundefs_in_val v.

  Lemma bstep_e_preserves_closed_fundefs rho e v c :
    bstep_e pr cenv rho e v c ->
    closed_fundefs_in_env (occurs_free e) rho ->
    closed_fundefs_in_exp e ->
    closed_fundefs_in_val v.
  Proof.
    intros Hstep Hcl1 Hcl2. induction Hstep.
    - eapply IHHstep.
      + subst. eapply lift_P_env_extend.
        * eapply lift_P_env_antimon; [| now eauto ].
          rewrite occurs_free_Econstr.
          eapply Included_Union_r.
        * constructor. eapply lift_P_env_get_list; eauto.
          rewrite occurs_free_Econstr. eapply Included_Union_l.
      + intros B Hin. eauto.
    - eapply IHHstep.
      + subst. eapply lift_P_env_extend.
        * eapply lift_P_env_antimon; [| now eauto ].
          rewrite occurs_free_Eproj.
          eapply Included_Union_r.
        * eapply Forall_nthN; [| eassumption ].
          eapply lift_P_env_get in H; [| eassumption |].
          now inv H.
          rewrite occurs_free_Eproj. eapply Included_Union_l.
      + intros B Hin. eauto.
    - eapply IHHstep.
      + eapply lift_P_env_antimon; [| now eauto ].
        eapply occurs_free_Ecase_Included.
        eapply findtag_In_patterns. eassumption.
      + intros B Hin. eapply Hcl2.
        econstructor; eauto. apply findtag_In_patterns. eassumption.
    - eapply IHHstep.
      + eapply Hcl1 in H; [| now eauto ]. inv H.
        apply find_def_correct in H1.
        eapply lift_P_env_antimon. eapply occurs_free_in_fun.
        eassumption.
        unfold closed_fundefs in H5. rewrite H5, Union_Empty_set_neut_r.
        eapply lift_P_env_set_lists; [| | now eauto ].
        * rewrite Setminus_Union_distr, Setminus_Same_set_Empty_set, Union_Empty_set_neut_l.
          eapply  lift_P_env_def_funs.
          rewrite Setminus_Included_Empty_set. now apply lift_P_env_Emtpy_set.
          eauto with Ensembles_DB.
          intros f''. now constructor.
        * eapply lift_P_env_get_list; [ eassumption | | eassumption ].
          rewrite occurs_free_Eapp. eapply Included_Union_l.
      + intros B Hin.
        eapply Hcl1 in H; [| now eauto ].
        eapply find_def_correct in H1.
        inv H. eapply H7. eapply fun_in_fundefs_funs_in_fundef; eassumption.
    - admit. (* TODO fill in letapp case *)
    - eapply IHHstep.
      + eapply lift_P_env_def_funs.
        * eapply lift_P_env_antimon; [| eassumption ].
          rewrite occurs_free_Efun. eapply Included_Union_r.
        * intros f. constructor. now eapply Hcl2.
          intros B H. eapply Hcl2. now eauto.
      + intros B Hin. eauto.
    - eapply IHHstep.
      + subst. eapply lift_P_env_extend.
        * eapply lift_P_env_antimon; [| now eauto ].
          rewrite occurs_free_Eprim_val. reflexivity.
        * constructor.
      + intros B Hin. eauto.
    - eapply IHHstep.
      + subst. eapply lift_P_env_extend.
        * eapply lift_P_env_antimon; [| now eauto ].
          rewrite occurs_free_Eprim. eapply Included_Union_r.
        * eapply prims_closed_fundefs; [ eassumption | | eassumption ].
          eapply lift_P_env_get_list; [ eassumption | | eassumption ].
          rewrite occurs_free_Eprim. eapply Included_Union_l.
      + intros B Hin. eauto.
    - eapply Hcl1. now constructor. eassumption.
  Abort.

End LogRelCC.

Notation cc_approx_exp := (fun cenv ct => (cc_approx_exp' cenv (cc_approx_val cenv ct))).
