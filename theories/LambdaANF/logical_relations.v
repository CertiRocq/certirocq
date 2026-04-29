(* Step-indexed logical relations for LambdaANF.  Part of the CertiRocq project.
 * Author: Anonymized, 2016
 *)

Require Import compcert.lib.Coqlib.
From Stdlib Require Import NArith.BinNat Relations.Relations MSets.MSets MSets.MSetRBT
        Lists.List micromega.Lia Sets.Ensembles.
From Stdlib Require Import Logic.Classical_Prop Logic.Classical_Pred_Type.

Require Import LambdaANF.term LambdaANF.eval LambdaANF.term_util LambdaANF.identifiers LambdaANF.ctx LambdaANF.map_util
        LambdaANF.Ensembles_util LambdaANF.List_util LambdaANF.tactics LambdaANF.set_util LambdaANF.algebra.

Import ListNotations.

Close Scope Z_scope.


  (** step-indexed preorder on LambdaANF terms *)
  (* Expression relation :
   * ---------------------
   *  (e1, ρ1) ~_k (e2, ρ2) iff
   *    forall c1 <= k,
   *      ρ1 |- e1 ->^c1 v1 ->
   *      exists v2, p2 |- e2 -> v2 /\ v1 ~_(k-c1) v2
   * Value relation :
   * ----------------
   * Integers: (n1 ~_k n2) iff n1 = n2
   * Constructors: [v_1, .., v_n] ~_k [v'_1, .., v'_m] iff
                     n <= m /\ v_1 ~_k v'_1 /\ ... /\ v_n ~_k v'_n'
   * Closures: (\f1 x1. e1, ρ1) ~_k (\f2 x2. e2, ρ2) iff
   *              \forall v1 v2 i < k, v1 ~_j v2 =>
   *                (e1, ρ1[x1 -> v1, f1 -> (\f1 x1. e1, ρ1)]) ~_j
   *                (e2, ρ2[x2 -> v2, f2 -> (\f2 x2. e2, ρ2)])
   *)

Section Log_rel.

  Variable (pr : prims).
  Variable (cenv : ctor_env).

  Context {fuel : Type} {Hf : @fuel_resource fuel} {trace : Type} {Ht : @trace_resource trace}.

  Definition PostT  : Type := relation (exp * env * fuel * trace).
  Definition PostGT : Type := relation (exp * env * fuel * trace).


  Section Exp_rel.

    Variable (val_rel : PostGT -> nat -> val -> val -> Prop).

    Variable (Post : PostT).
    Variable (PostG : PostGT).

    Definition preord_res (k : nat) (r1 r2 : res) :=
    match r1, r2 with
    | OOT, OOT => True
    | Res v1, Res v2 => val_rel PostG k v1 v2
    | _, _ => False
    end.

    Definition preord_exp' (k : nat) (p1 p2 : exp * env) : Prop :=
      let '(e1, rho1) := p1 in
      let '(e2, rho2) := p2 in
      forall v1 (cin : fuel) (cout : trace),
        to_nat cin <= k -> bstep_fuel cenv rho1 e1 cin v1 cout ->
        exists v2 cin' cout',
          bstep_fuel cenv rho2 e2 cin' v2 cout' /\
          Post (e1, rho1, cin, cout) (e2, rho2, cin', cout') /\
          preord_res (k - to_nat cin) v1 v2.

  End Exp_rel.

  Section Val_rel.

    (* Tag for closure records *)
    Variable (clo_tag : ctor_tag).

    Fixpoint preord_val (PostG : PostGT) (k : nat) (v1 v2 : val) {struct k} : Prop :=
      let fix preord_val_aux (v1 v2 : val) {struct v1} : Prop :=
          let fix Forall2_aux vs1 vs2 :=
              match vs1, vs2 with
                | [], [] => True
                | v1 :: vs1, v2 :: vs2 =>
                  preord_val_aux v1 v2 /\ Forall2_aux vs1 vs2
                | _, _ => False
              end
        in
        match v1, v2 with
        | Vfun rho1 defs1 f1, Vfun rho2 defs2 f2 =>
          forall (vs1 vs2 : list val) (j : nat) (t : fun_tag)
            (xs1 : list var) (e1 : exp) (rho1' : env),
            List.length vs1 = List.length vs2 ->
            find_def f1 defs1 = Some (t, xs1, e1) ->
            Some rho1' = set_lists xs1 vs1 (def_funs defs1 defs1 rho1 rho1) ->
            exists (xs2 : list var) (e2 : exp) (rho2' : env),
             find_def f2 defs2 = Some (t, xs2, e2) /\
             Some rho2' = set_lists xs2 vs2 (def_funs defs2 defs2 rho2 rho2) /\
             match k with
             | 0 => True
             | S k =>
              let R := preord_val PostG (k - (k-j)) in
              j < S k ->
              Forall2 R vs1 vs2 ->
              preord_exp' preord_val PostG PostG (k - (k - j))  (e1, rho1') (e2, rho2')
             end
       | Vconstr t1 vs1, Vconstr t2 vs2 =>
         t1 = t2 /\ Forall2_aux vs1 vs2
       | Vint n1, Vint n2 => n1 = n2
       | Vprim p, Vprim p' => p = p'
       | _, _ => False
       end
    in preord_val_aux v1 v2.

   (** a more compact definition of the value preorder *)
    Definition preord_val' (PostG : PostGT) (k : nat) (v1 v2 : val) : Prop :=
      match v1, v2 with
      | Vfun rho1 defs1 f1, Vfun rho2 defs2 f2 =>
          forall (vs1 vs2 : list val) j (t : fun_tag) (xs1 : list var)
            (e1 : exp) (rho1' : env),
            List.length vs1 = List.length vs2 ->
            find_def f1 defs1 = Some (t, xs1, e1) ->
            Some rho1' = set_lists xs1 vs1 (def_funs defs1 defs1 rho1 rho1) ->
            exists (xs2 : list var) (e2 : exp) (rho2' : env),
              find_def f2 defs2 = Some (t, xs2, e2) /\
              Some rho2' = set_lists xs2 vs2 (def_funs defs2 defs2 rho2 rho2) /\
              (j < k -> Forall2 (preord_val PostG j) vs1 vs2 ->
               preord_exp' preord_val PostG PostG j (e1, rho1') (e2, rho2'))
      | Vconstr t1 vs1, Vconstr t2 vs2 =>
        t1 = t2 /\ Forall2 (preord_val PostG k) vs1 vs2
      | Vint n1, Vint n2 => n1 = n2
      | Vprim p, Vprim p' => p = p'
      | _, _ => False
    end.

    (** correspondence of the two definitions *)
    Lemma preord_val_eq (k : nat) PostG (v1 v2 : val) :
      preord_val PostG k v1 v2 <-> preord_val' PostG k v1 v2.
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
      - split; intros Hpre; simpl; intros;
        edestruct (Hpre vs1 vs2 0) as [xs2 [e2 [rho' [H1' [H2' H3']]]]];
        eauto; do 4 eexists; repeat split; eauto; intros Hc; exfalso; lia.
      - revert l0; induction l as [| x xs IHxs];
        intros l2; destruct l2 as [| y ys ];
        split; intros H; try (now simpl in H; inv H); try now (simpl; eauto).
        + destruct H as [Heq [H1 H2]]; subst.
          constructor; eauto. constructor; eauto. eapply IHxs.
          constructor; eauto.
        + inv H. inv H1. split. reflexivity.
          split. now eauto. eapply IHxs. split; eauto.
      - split; intros Hpre; simpl; intros;
          try now (edestruct Hpre as [xs2 [e2 [rho' [H1' [H2' H3']]]]]; eauto;
                   do 3 eexists; do 2 (split; eauto); intros Hleq Hf' v1 cin cout Hleq' Hstep;
           (assert (Heq : k - (k - j) = j) by lia); rewrite Heq in *;
           eapply H3'; eauto).
    Qed.

    Global Opaque preord_val.

  End Val_rel.

  Notation preord_exp := (preord_exp' preord_val).

  (** Environment relation for a single point (i.e. variable) :
    * ρ1 ~_k^(x, y) ρ2 iff ρ1(x) = Some v -> ρ2(x) = Some v' /\ v ~_k v' *)
  Definition preord_var_env PostG (k : nat) (rho1 rho2 : env) (x y : var) : Prop :=
    forall v1,
      M.get x rho1 = Some v1 ->
      exists v2, M.get y rho2 = Some v2 /\ preord_val PostG k v1 v2.

  (** Environment relation for a set of points (i.e. predicate over variables) :
    * ρ1 ~_k^S ρ2 iff
    *   forall x, S x -> ρ1(x) = Some v -> ρ2(x) = Some v' /\ v ~_k v' *)
  Definition preord_env_P PostG (S : Ensemble var) k rho1 rho2 :=
    forall (x : var), S x -> preord_var_env PostG k rho1 rho2 x x.

  (** Environment relation for the whole domain of definition :
    * ρ1 ~_k ρ2 iff forall x, ρ1(x) = v => ρ2(x) = v' /\ v ~_k v' *)
  Definition preord_env PostG (k : nat) (rho1 rho2 : env) : Prop :=
    preord_env_P PostG (fun _ => True) k rho1 rho2.

  Open Scope ctx_scope.

  (** Context relation. *)
  Definition preord_ctx Post PostG (k : nat) (rho1 rho2 : env)
             (p1 p2 : exp_ctx * env) :=
    let '(c1, rho1') := p1 in
    let '(c2, rho2') := p2 in
    forall e1 e2,
      preord_exp Post PostG k (e1, rho1) (e2, rho2) ->
      preord_exp Post PostG k (c1 |[ e1 ]|, rho1') (c2 |[ e2 ]|, rho2').

  Section PostCond.

    (* Postcondition parameter *)
    Context (Post : PostT) (* Local *)
            (PostG : PostGT). (* Global *)

  (** Lemmas about extending the environment *)
  Lemma preord_var_env_extend_eq :
    forall (rho1 rho2 : env) (k : nat) (x1 x2 : var) (v1 v2 : term.val),
      preord_val PostG k v1 v2 ->
      preord_var_env PostG k (M.set x1 v1 rho1) (M.set x2 v2 rho2) x1 x2.
  Proof.
    intros rho1 rho2 k x1 x2 v1 v2 Hval x' Hget.
    rewrite M.gss in Hget. inv Hget. eexists. rewrite M.gss. split; eauto.
  Qed.


  Lemma preord_var_env_extend_neq :
    forall (rho1 rho2 : env) (k : nat) (x1 x2 y1 y2 : var) (v1 v2 : term.val),
      preord_var_env PostG k rho1 rho2 y1 y2 ->
      y1 <> x1 ->
      y2 <> x2 ->
      preord_var_env PostG k (M.set x1 v1 rho1) (M.set x2 v2 rho2) y1 y2.
  Proof.
    intros rho1 rho2 k x1 x2 y1 y2 v1 v2 Hval Hneq Hneq' x' Hget.
    rewrite M.gso in *; eauto.
  Qed.


  Lemma preord_var_env_extend :
    forall (rho1 rho2 : env) (k : nat) (x y : var) (v1 v2 : val),
      preord_var_env PostG k rho1 rho2 y y ->
      preord_val PostG k v1 v2 ->
      preord_var_env PostG k (M.set x v1 rho1) (M.set x v2 rho2) y y.
  Proof.
    intros rho1 rho2 k x y v1 v2 Henv Hval.
    destruct (peq y x); subst.
    - apply preord_var_env_extend_eq; eauto.
    - apply preord_var_env_extend_neq; eauto.
  Qed.


  Lemma preord_var_env_def_funs_not_In_l k B1 rho1 rho2 k1 k2 :
    ~ k1 \in name_in_fundefs B1 ->
             preord_var_env PostG k rho1 rho2 k1 k2 ->
             preord_var_env PostG k (def_funs B1 B1 rho1 rho1) rho2 k1 k2.
  Proof.
    intros Hnin Henv x Hget.
    rewrite def_funs_neq in Hget; eauto.
  Qed.

  Lemma preord_var_env_def_funs_not_In_r k B2 rho1 rho2 k1 k2 :
    ~ k2 \in name_in_fundefs B2 ->
             preord_var_env PostG k rho1 rho2 k1 k2 ->
             preord_var_env PostG k rho1 (def_funs B2 B2 rho2 rho2) k1 k2.
  Proof.
    intros Hnin Henv x Hget.
    rewrite def_funs_neq; eauto.
  Qed.

  (** The environment relation is antimonotonic in the set
    * of free variables *)
  Lemma preord_env_P_antimon (P1 P2 : var -> Prop) k rho1 rho2 :
    preord_env_P PostG P2 k rho1 rho2 ->
    (Included var P1 P2) ->
    preord_env_P PostG P1 k rho1 rho2.
  Proof.
    intros Hpre Hin x HP2. eapply Hpre; eapply Hin; eauto.
  Qed.

  (** Lemmas about the sets that index the environment relation *)
  Lemma preord_env_Empty_set k (rho1 rho2 : env) :
    preord_env_P PostG (Empty_set var) k rho1 rho2.
  Proof.
    intros x H. inv H.
  Qed.

  Lemma preord_env_P_union P1 P2 k rho1 rho2 :
    preord_env_P PostG P1 k rho1 rho2 ->
    preord_env_P PostG P2 k rho1 rho2 ->
    preord_env_P PostG (Union var P1 P2) k rho1 rho2.
  Proof.
    intros Hpre1 Hpre2 x HP2. inv HP2; eauto.
  Qed.

  Lemma preord_env_P_inter_l (P1 P2 : var -> Prop) k rho1 rho2 :
    preord_env_P PostG P1 k rho1 rho2 ->
    preord_env_P PostG (Intersection var P1 P2) k rho1 rho2.
  Proof.
    intros Hpre x HP2. inv HP2; eauto.
  Qed.

  Lemma preord_env_P_inter_r (P1 P2 : var -> Prop) k rho1 rho2 :
    preord_env_P PostG P2 k rho1 rho2 ->
    preord_env_P PostG (Intersection var P1 P2) k rho1 rho2.
  Proof.
    intros Hpre x HP2. inv HP2; eauto.
  Qed.

  (** Extend the related environments with a single point *)
  Lemma preord_env_P_extend :
    forall P (rho1 rho2 : env) (k : nat) (x : var) (v1 v2 : val),
      preord_env_P PostG (Setminus var P (Singleton var x)) k rho1 rho2 ->
      preord_val PostG k v1 v2 ->
      preord_env_P PostG P k (M.set x v1 rho1) (M.set x v2 rho2).
  Proof.
    intros S rho1 rho2 k x v1 v2 Henv Hval x' HP v1' Hget.
    rewrite M.gsspec in Hget. destruct (peq x' x); subst.
    - inv Hget. eexists. rewrite M.gss. split; eauto.
    - apply Henv in Hget; eauto. destruct Hget as [v2' [Heq Hpre]].
      eexists; split; eauto. rewrite M.gso; eauto. constructor; eauto.
      intros Hin. inv Hin. congruence.
  Qed.

  (** Extend the related environments with a list *)
  Lemma preord_env_P_set_lists_l:
    forall (P1 P2 : var -> Prop) (rho1 rho2 rho1' rho2' : env)
      (k : nat) (xs : list var) (vs1 vs2 : list val),
      preord_env_P PostG P1 k rho1 rho2 ->
      (forall x, ~ List.In x xs -> P2 x -> P1 x) ->
      Forall2 (preord_val PostG k) vs1 vs2 ->
      set_lists xs vs1 rho1 = Some rho1' ->
      set_lists xs vs2 rho2 = Some rho2' ->
      preord_env_P PostG P2 k rho1' rho2'.
  Proof.
    intros P1 P2 rho1' rho2' rho1 rho2 k xs vs1 vs2 Hpre Hyp Hall Hset1 Hset2
           x HP v Hget.
    destruct (in_dec var_dec x xs).
    - edestruct (@set_lists_Forall2_get val) as [v1 [v2 [Hget1 [Hget2 HP']]]]; eauto.
      rewrite Hget in Hget1. inv Hget1. repeat eexists; eauto.
    - erewrite <- set_lists_not_In in Hget; eauto.
      edestruct Hpre as [v2 [Hget' Hpre']]; eauto.
      repeat eexists; eauto. erewrite <- set_lists_not_In; eauto.
  Qed.

  Lemma preord_var_env_get_list (rho1 rho2 : env) (k : nat)
        (xs ys : list var) (vs1 : list val) :
    Forall2 (preord_var_env PostG k rho1 rho2) xs ys ->
    get_list xs rho1 = Some vs1 ->
    exists vs2,
      get_list ys rho2 = Some vs2 /\ Forall2 (preord_val PostG k) vs1 vs2.
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

  Lemma preord_env_P_get_list_l (S : var -> Prop) (rho1 rho2 : env) (k : nat)
        (xs : list var) (vs1 : list val) :
    preord_env_P PostG S k rho1 rho2 ->
    Included _ (FromList xs) S ->
    get_list xs rho1 = Some vs1 ->
    exists vs2,
      get_list xs rho2 = Some vs2 /\ Forall2 (preord_val PostG k) vs1 vs2.
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

  Corollary preord_env_get_list_l (rho1 rho2 : env) (k : nat)
        (xs : list var) (vs1 : list val) :
    preord_env PostG k rho1 rho2 ->
    get_list xs rho1 = Some vs1 ->
    exists vs2,
      get_list xs rho2 = Some vs2 /\ Forall2 (preord_val PostG k) vs1 vs2.
  Proof.
    intros. eapply preord_env_P_get_list_l; eauto.
    intros x H'; simpl; eauto.
  Qed.

  Corollary preord_env_extend (rho1 rho2 : env) (k : nat)
        (x : var) (v1 v2 : val) :
    preord_env PostG k rho1 rho2 ->
    preord_val PostG k v1 v2 ->
    preord_env PostG k (M.set x v1 rho1) (M.set x v2 rho2).
  Proof.
    intros H1 Hval. apply preord_env_P_extend; eauto.
    eapply preord_env_P_antimon; eauto. intros x' H; simpl; eauto.
  Qed.


  Lemma preord_env_P_set_not_in_P_l' (x : var) (v : val) (P : Ensemble var) (k : nat) (rho1 rho2 : env) :
      preord_env_P PostG P k (M.set x v rho1) rho2 ->
      Disjoint var P (Singleton var x) ->
      preord_env_P PostG P k rho1 rho2.
  Proof.
    intros Henv Hdis y Hin v1 Hget.
    apply Henv. auto.
    rewrite M.gso; auto.
    intros; subst. intros Hc; subst. eapply Hdis; constructor; eauto.
  Qed.

  Lemma preord_env_P_set_not_in_P_r' (x : var) (v : val)
      (P : Ensemble var) (k : nat) (rho1 rho2 : env) :
    preord_env_P PostG P k rho1 (M.set x v rho2) ->
    Disjoint var P (Singleton var x) ->
    preord_env_P PostG P k rho1 rho2.
  Proof.
    intros Henv Hdis y Hin v1 Hget. eapply Henv in Hget; eauto.
    rewrite M.gso in Hget; auto.
    intros; subst. intros Hc; subst. eapply Hdis; constructor; eauto.
  Qed.

  Lemma preord_env_P_def_funs_not_in_P_l' (B B' : fundefs)
      (P : Ensemble var) (k : nat) (rho : M.t val) (rho1 rho2 : env) :
      preord_env_P PostG P k (def_funs B' B rho rho1) rho2 ->
      Disjoint var P (name_in_fundefs B) ->
      preord_env_P PostG P k rho1 rho2.
  Proof.
    intros Henv Hdis y Hin v1 Hget. eapply Henv; eauto.
    rewrite def_funs_neq; auto. intros Hc. eapply Hdis.
    constructor; eauto.
  Qed.

  Lemma preord_env_refl k :
    Reflexive (preord_val PostG k) ->
    Reflexive (preord_env PostG k).
  Proof.
    intros H r. intros; eexists; eauto.
  Qed.

  Corollary preord_env_set_lists_l (rho1 rho2 rho1' rho2' : env) (k : nat)
        (xs : list var) (vs1 vs2 : list val) :
    preord_env PostG k rho1 rho2 ->
    Forall2 (preord_val PostG k) vs1 vs2 ->
    set_lists xs vs1 rho1 = Some rho1' ->
    set_lists xs vs2 rho2 = Some rho2' ->
    preord_env PostG k rho1' rho2'.
  Proof.
    intros. eapply preord_env_P_set_lists_l; eauto.
  Qed.

  Lemma preord_val_constr k t vl x :
    preord_val PostG k (term.Vconstr t vl) x  ->
    exists vl', x = term.Vconstr t vl' /\ Forall2 (preord_val PostG k) vl vl'.
  Proof.
    intros H. eapply preord_val_eq in H.
    destruct x; try contradiction. destruct H as [Heq Hall]; eauto. subst.
    eexists; split; eauto.
  Qed.

  Lemma preord_val_fun k f1 f2 rho1 rho2 B1 B2 ft xs1 xs2 e1 e2 :
    find_def f1 B1 = Some (ft, xs1, e1) ->
    find_def f2 B2 = Some (ft, xs2, e2) ->

    (forall rho1' j vs1 vs2,
        Datatypes.length vs1 = Datatypes.length vs2 ->
        Some rho1' = set_lists xs1 vs1 (def_funs B1 B1 rho1 rho1) ->
        exists (rho2' : env),
          Some rho2' = set_lists xs2 vs2 (def_funs B2 B2 rho2 rho2) /\
          ((j < k)%nat ->
           Forall2 (preord_val PostG j) vs1 vs2 ->
           preord_exp' preord_val PostG PostG j (e1, rho1') (e2, rho2'))) ->


    preord_val PostG k (Vfun rho1 B1 f1) (Vfun rho2 B2 f2).
  Proof.
    intros Hf1 Hf2 Hexp. rewrite preord_val_eq.
    intro; intros. repeat subst_exp.
    edestruct Hexp. eassumption. eassumption. destructAll.
    do 3 eexists. split; [ | split ]. eassumption.
    eassumption. eauto.
  Qed.


  (** * Index Anti-Monotonicity Properties *)

  (** The value relation is anti-monotonic in the step index *)
  Lemma preord_val_monotonic (k : nat) :
    (forall v1 v2 j,
       preord_val PostG k v1 v2 -> j <= k -> preord_val PostG j v1 v2).
  Proof.
    intros v1 v2 h Hpre Hleq. try rewrite preord_val_eq in *.
    revert v2 Hpre; induction v1 using val_ind'; intros v2 Hpre;
    destruct v2; try (simpl; contradiction); eauto.
    - destruct l; try now inv Hpre.
    - inv Hpre. inv H0.
      split; auto. constructor; eauto; rewrite preord_val_eq in *.
      eapply IHv1; eauto.
      destruct (IHv0 ((Vconstr c l'))) as [Heq Hpre']; eauto.
      simpl. split; eauto.
    - intros vs1 vs2 j t1 xs e1 rho1' Hlen Hf' Heq.
      edestruct Hpre as [xs2 [e2 [rho2' [H1 [H2 H3]]]]]; eauto.
      do 3 eexists; split; eauto. split; eauto. intros Hleq' Hall.
      eapply H3; eauto. lia.
  Qed.

  Lemma preord_var_env_monotonic k rho1 rho2 j z x:
    preord_var_env PostG k rho1 rho2 x z ->
    j <= k ->
    preord_var_env PostG j rho1 rho2 x z.
  Proof.
    intros Henv Hleq y HIn. apply Henv in HIn. destructAll.
    eexists; split; eauto.
    eapply preord_val_monotonic; eauto.
  Qed.

  Lemma preord_res_monotonic (k j: nat)  r1 r2 :
    preord_res preord_val PostG k r1 r2 ->
    j <= k ->
    preord_res preord_val PostG j r1 r2.
  Proof.
   intros Hres Hlt.
   destruct r1; destruct r2; try contradiction; eauto.
   simpl in Hres. eapply preord_val_monotonic; eassumption.
  Qed.


  (** The environment relations are monotonic in the step index *)
  Lemma preord_env_P_monotonic :
    forall S (k j : nat) (rho1 rho2 : env),
      j <= k -> preord_env_P PostG S k rho1 rho2 -> preord_env_P PostG S j rho1 rho2.
  Proof.
    intros S k j rho1 rho2 Hleq Hpre x HP v Hget.
    edestruct Hpre as [v2 [Heq Hpre2]]; eauto.
    eexists; split; eauto. eapply preord_val_monotonic; eauto.
  Qed.

  Lemma preord_env_monotonic k j rho1 rho2 :
    j <= k -> preord_env PostG k rho1 rho2 -> preord_env PostG j rho1 rho2.
  Proof.
    intros Hleq H. eapply preord_env_P_monotonic; eauto.
  Qed.

  (** The expression relation is anti-monotonic in the step index *)
  Lemma preord_exp_monotonic (k : nat) :
    forall rho1 e1 rho2 e2 j,
      preord_exp Post PostG k (rho1, e1) (rho2, e2) ->
      j <= k -> preord_exp Post PostG j (rho1, e1) (rho2, e2).
  Proof.
    intros rho1 e1 rho2 e2 j Hpre Hleq v1 cin Hlt Hstep Hns.
    edestruct (Hpre v1 cin) as [v2 [cin' [H1 [H2 [H3 H4]]]]]; eauto. lia.
    do 3 eexists; split; eauto. split; eauto.
    eapply preord_res_monotonic. eassumption. lia.
  Qed.

  Lemma preord_exp_post_monotonic_strong k (P1 P2 : PostT) PG e1 rho1 e2 rho2 :
    (forall c1 c2 c3 c4, P1 (e1, rho1, c1, c3) (e2, rho2, c2, c4) ->
                         P2 (e1, rho1, c1, c3) (e2, rho2, c2, c4)) ->
    preord_exp P1 PG k (e1, rho1) (e2, rho2) ->
    preord_exp P2 PG k (e1, rho1) (e2, rho2).
  Proof.
     intros Hyp Hexp v1 c2 Hleq Hstep Hns.
     edestruct Hexp as [v2 [c2' [Hstep2 [Hp [Hv Hr]]]]]; try eassumption.
     do 3 eexists; repeat split; eauto.
  Qed.


  End PostCond.

  (** * Compatibility Properties of Post-conditions *)

  (** Versions of the properties where the e1 rho1 are extenralized, whhich is needed in some cases for them to be provable *)

  Open Scope alg_scope.

  Definition post_constr_compat' x t ys e1 rho1 x' t' ys' e2 rho2 (P1 P2 : PostT) :=
    forall vs vs' c1 c2 cout1 cout2,
      get_list ys rho1 = Some vs ->
      get_list ys' rho2 = Some vs' ->
      P1 (e1, M.set x (Vconstr t vs) rho1, c1, cout1)  (e2, M.set x' (Vconstr t' vs') rho2, c2, cout2) ->
      P2 (Econstr x t ys e1, rho1, c1 <+> one (Econstr x t ys e1), cout1 <+> one (Econstr x t ys e1))
         (Econstr x' t' ys' e2, rho2, c2 <+> one (Econstr x' t' ys' e2), cout2 <+> one (Econstr x t ys e1)).

  Definition post_proj_compat' x t N y e1 rho1 x' t' N' y' e2 rho2 (P1 P2 : PostT) :=
    forall vs v1 v2 c1 c2 cout1 cout2,
      M.get y rho1 = Some (Vconstr t vs) ->
      nthN vs N = Some v1 ->
      P1 (e1, M.set x v1 rho1, c1, cout1)  (e2, M.set x' v2 rho2, c2, cout2) ->
      P2 (Eproj x t N y e1, rho1, c1 <+> one (Eproj x t N y e1), cout1 <+> one (Eproj x t N y e1))
         (Eproj x' t' N' y' e2, rho2, c2 <+> one (Eproj x' t' N' y' e2), cout2 <+> one (Eproj x t N y e1)).

  Definition post_case_compat_hd' x t e1 B1 rho1 x' t' e2 B2 rho2 (P1 P2 : PostT) :=
    forall c1 c2 cout1 cout2,
      P1 (e1, rho1, c1, cout1)  (e2, rho2, c2, cout2)  ->
      P2 (Ecase x ((t, e1) :: B1), rho1, c1 <+> one (Ecase x ((t, e1) :: B1)), cout1 <+> one (Ecase x ((t, e1) :: B1)))
         (Ecase x' ((t', e2) :: B2), rho2, c2 <+> one (Ecase x' ((t', e2) :: B2)), cout2 <+> one (Ecase x' ((t', e2) :: B2))).

  Definition post_case_compat_tl' x t e1 B1 rho1 x' t' e2 B2 rho2  (P1 P2 : PostT) :=
    forall c1 c2 cout1 cout2,
      P1 (Ecase x B1, rho1, c1, cout1)  (Ecase x' B2, rho2, c2, cout2) ->
      P2 (Ecase x ((t, e1) :: B1), rho1, c1, cout1) (Ecase x' ((t', e2) :: B2), rho2, c2, cout2).

  Definition post_fun_compat' B1 e1 rho1 B2 e2 rho2 (P1 P2 : PostT) :=
    forall c1 c2 cout1 cout2,
      P1 (e1, def_funs B1 B1 rho1 rho1, c1, cout1)  (e2, def_funs B2 B2 rho2 rho2, c2, cout2) ->
      P2 (Efun B1 e1, rho1, c1 <+> one (Efun B1 e1), cout1 <+> one (Efun B1 e1))
         (Efun B2 e2, rho2, c2 <+> one (Efun B2 e2), cout2 <+> one (Efun B1 e1)).

  Definition post_OOT' e1 rho1 e2 rho2 (P1 : PostT) :=
    forall c,
      c << one e1 -> P1 (e1, rho1, c, <0>) (e2, rho2, c, <0>).

  (* Definition post_zero e1 rho1 e2 rho2 (P1 : PostT) := *)
  (*   forall c,  *)
  (*     c <<_{ e1 } one e1 -> *)
  (*     P1 (e1, rho1, c) (e2, rho2, <0>). *)

  Definition post_base' x rho1 y rho2 (P1 : PostT) :=
    P1 (Ehalt x, rho1, one (Ehalt x), one (Ehalt x)) (Ehalt y, rho2, one (Ehalt y), one (Ehalt y)).

  Definition post_app_compat' x t ys rho1 x' t' ys' rho2 (P : PostT) (PG : PostGT):=
    forall xs e1 e2 rhoc1 rhoc2 fl f vs rhoc1' c1 c2 cout1 cout2,

      map_util.M.get x rho1 = Some (Vfun rhoc1 fl f) ->
      get_list ys rho1 = Some vs ->
      find_def f fl = Some (t, xs, e1) ->
      set_lists xs vs (def_funs fl fl rhoc1 rhoc1) = Some rhoc1' ->

      (* for simplicity don't model the semantics of the target since it doesn't matter *)
      PG (e1, rhoc1', c1, cout1)  (e2, rhoc2, c2, cout2) ->
      P (Eapp x t ys, rho1, c1 <+> one (Eapp x t ys), cout1 <+> one (Eapp x t ys))
        (Eapp x' t' ys', rho2, c2 <+> one (Eapp x' t' ys'), cout2 <+> one (Eapp x' t' ys')).

  Definition post_letapp_compat' x f t ys e1 rho1 x' f' t' ys' e2 rho2 (P1 P2 : PostT) (PG : PostGT):=
    forall xs e_b1 v1  e_b2 v2
           rhoc1 rhoc2 fl h vs rhoc1' c1 c1' c2 c2' cout1 cout2 cout1' cout2',

      map_util.M.get f rho1 = Some (Vfun rhoc1 fl h) ->
      get_list ys rho1 = Some vs ->
      find_def h fl = Some (t, xs, e_b1) ->
      set_lists xs vs (def_funs fl fl rhoc1 rhoc1) = Some rhoc1' ->
      bstep_fuel cenv rhoc1' e_b1 c1 (Res v1) cout1 ->

      (* for simplicity don't model the semantics of the target since it doesn't matter *)
      PG (e_b1, rhoc1', c1, cout1)  (e_b2, rhoc2, c2, cout2) ->
      P1 (e1, M.set x v1 rho1, c1', cout1') (e2, M.set x' v2 rho2, c2', cout2') ->
      P2 (Eletapp x f t ys e1, rho1, c1 <+> c1' <+> one (Eletapp x f t ys e1), cout1 <+> cout1' <+> one (Eletapp x f t ys e1))
         (Eletapp x' f' t' ys' e2, rho2, c2 <+> c2' <+> one (Eletapp x' f' t' ys' e2), cout2 <+> cout2' <+> one (Eletapp x' f' t' ys' e2)).

  Definition post_letapp_compat_OOT' x f t ys e1 rho1
             x' f' t' ys' e2 rho2 (P2 : PostT) (PG : PostGT):=
    forall xs e_b1  e_b2 rhoc1 rhoc2 fl h vs rhoc1' c1 c2 cout1 cout2,

      map_util.M.get f rho1 = Some (Vfun rhoc1 fl h) ->
      get_list ys rho1 = Some vs ->
      find_def h fl = Some (t, xs, e_b1) ->
      set_lists xs vs (def_funs fl fl rhoc1 rhoc1) = Some rhoc1' ->

      (* for simplicity don't model the semantics of the target since it doesn't matter *)
      PG (e_b1, rhoc1', c1, cout1)  (e_b2, rhoc2, c2, cout2) ->
      P2 (Eletapp x f t ys e1, rho1, c1 <+> one (Eletapp x f t ys e1), cout1 <+> one (Eletapp x f t ys e1))
         (Eletapp x' f' t' ys' e2, rho2, c2 <+> one (Eletapp x' f' t' ys' e2), cout2 <+> one (Eletapp x' f' t' ys' e2)).

  Definition post_constr_compat (P1 P2 : PostT) :=
    forall x t ys e1 rho1 x' t' ys' e2 rho2, post_constr_compat' x t ys e1 rho1 x' t' ys' e2 rho2 P1 P2.

  Definition post_proj_compat (P1 P2 : PostT) :=
    forall x t N y e1 rho1 x' t' N' y' e2 rho2, post_proj_compat' x t N y e1 rho1 x' t' N' y' e2 rho2 P1 P2.

  Definition post_case_compat_hd (P1 P2 : PostT) :=
    forall x t e1 B1 rho1 x' t' e2 B2 rho2, post_case_compat_hd' x t e1 B1 rho1 x' t' e2 B2 rho2 P1 P2.

  Definition post_case_compat_tl (P1 P2 : PostT) :=
    forall x t e1 B1 rho1 x' t' e2 B2 rho2, post_case_compat_tl' x t e1 B1 rho1 x' t' e2 B2 rho2 P1 P2.

  Definition post_fun_compat (P1 P2 : PostT) :=
    forall B1 e1 rho1 B2 e2 rho2, post_fun_compat' B1 e1 rho1 B2 e2 rho2 P1 P2.

  Definition post_OOT (P1 : PostT) :=
    forall e1 rho1 e2 rho2, post_OOT' e1 rho1 e2 rho2 P1.

  Definition post_base (P1 : PostT) :=
    forall e1 rho1 e2 rho2, post_base' e1 rho1 e2 rho2 P1.

  Definition post_app_compat (P : PostT) (PG : PostGT) :=
    forall x t xs rho1 x' t' xs' rho2, post_app_compat' x t xs rho1 x' t' xs' rho2 P PG.

  Definition post_letapp_compat (P1 P2 : PostT) (PG : PostGT) :=
    forall x f t xs e1 rho1 x' f' t' ys' e2 rho2, post_letapp_compat' x f t xs e1 rho1 x' f' t' ys' e2 rho2 P1 P2 PG.

  Definition post_letapp_compat_OOT (P2 : PostT) (PG : PostGT) :=
    forall x f t xs e1 rho1 x' f' t' ys' e2 rho2, post_letapp_compat_OOT' x f t xs e1 rho1 x' f' t' ys' e2 rho2 P2 PG.

  Class Post_properties (P1 P2 : PostT) (PG : PostGT) : Prop :=
    { HPost_con : post_constr_compat P1 P2;
      HPost_proj : post_proj_compat P1 P2;
      HPost_fun : post_fun_compat P1 P2;
      HPost_case_hd : post_case_compat_hd P1 P2;
      HPost_case_tl : post_case_compat_tl P2 P2;
      HPost_app : post_app_compat P1 PG;
      HPost_letapp : post_letapp_compat P1 P2 PG;
      HPost_letapp_OOT : post_letapp_compat_OOT P1 PG;
      HPost_OOT : post_OOT P2;
      Hpost_base : post_base P2;
      HGPost : inclusion _ P1 PG }.


  (* Assymetric properties *)
  Definition post_Efun_l (P1 P2 : PostT) :=
    forall B e1 e2 rho1 rho2 c1 c2 cout1 cout2,
      P1 (e1, def_funs B B rho1 rho1, c1, cout1) (e2, rho2, c2, cout2) ->
      P2 (Efun B e1, rho1, c1 <+> one (Efun B e1), cout1 <+> one (Efun B e1)) (e2, rho2, c2, cout2).

  Definition post_Efun_r (P1 P2 : PostT) :=
    forall B e1 e2 rho1 rho2 c1 c2 cout1 cout2,
      P1 (e1, rho1, c1, cout1) (e2, def_funs B B rho2 rho2, c2, cout2) ->
      P2 (e1, rho1, c1, cout1)
         (Efun B e2, rho2, c2 <+> one (Efun B e2), cout2 <+> one (Efun B e2)).

  Definition post_Eapp_r (P1 P2 : PostT) e1 rho1 f ft ys rho2 :=
    forall e2 rho2' c1 c2 cout1 cout2,
      P1 (e1, rho1, c1, cout1) (e2, rho2', c2, cout2) ->
      P2 (e1, rho1, c1, cout1) ((Eapp f ft ys), rho2, c2 <+> one (Eapp f ft ys), cout2 <+> one (Eapp f ft ys)).

  Definition post_Eapp_l (P1 P2 : PostT) f ft ys rho1 e2 rho2 :=
    forall (rhoc rho' : env) (f' : var) (xs : list var) e1 B vs c1 c2 cout1 cout2,
      M.get f rho1 = Some (Vfun rhoc B f') ->
      get_list ys rho1 = Some vs ->
      find_def f' B = Some (ft, xs, e1) ->
      set_lists xs vs (def_funs B B rhoc rhoc) = Some rho' ->
      P1 (e1, rho', c1, cout1) (e2, rho2, c2, cout2) ->
      P2 (Eapp f ft ys, rho1, c1 <+> one (Eapp f ft ys), cout1 <+> one (Eapp f ft ys)) (e2, rho2, c2, cout2).

  Section Compat.
    Context (P1 P2 : PostT) (* Local *)
            (PG : PostGT). (* Global *)


    Lemma nat_minus_minus (n m k : nat) :
      n >= k ->
      m >= n ->
      m - (n - k) = m - n + k.
    Proof.
      intros. lia.
    Qed.

   (** * Compatibility Properties *)

    Lemma preord_exp_constr_compat k rho1 rho2 x x' t ys1 ys2 e1 e2
          (Hcompat : post_constr_compat' x t ys1 e1 rho1 x' t ys2 e2 rho2 P1 P2)
          (HOOT : post_OOT' (Econstr x t ys1 e1) rho1 (Econstr x' t ys2 e2) rho2 P2):
      Forall2 (preord_var_env PG k rho1 rho2) ys1 ys2 ->
      (forall m (vs1 vs2 : list val),
          m < k ->
          Forall2 (preord_val PG m) vs1 vs2 ->
          preord_exp P1 PG m (e1, M.set x (Vconstr t vs1) rho1)
                     (e2, M.set x' (Vconstr t vs2) rho2)) ->
      preord_exp P2 PG k (Econstr x t ys1 e1, rho1) (Econstr x' t ys2 e2, rho2).
    Proof.
      intros Hall Hpre v1 cin cout Hleq1 Hstep1. inv Hstep1.
      - (* OOT *)
        exists OOT, cin, <0>. split. constructor; eassumption.
        split; [| now eauto ]. eapply HOOT. eassumption.
      - inv H.
        rewrite to_nat_add in Hleq1.
        assert (Hg := to_nat_one (exp_to_fin (Econstr x t ys1 e1))). unfold one in *.
        edestruct (preord_var_env_get_list PG rho1 rho2) as [vs2' [Hget' Hpre']];
          [| eauto |]; eauto.

        edestruct (Hpre (k - to_nat (one (Econstr x t ys1 e1)))) as [v2 [cin' [cout' [Hstep [Hpost Hval]]]]];
          [| | | eassumption | ]; eauto.
        unfold one. simpl in *. lia.

        eapply Forall2_monotonic; [| eassumption ]. intros. eapply preord_val_monotonic. eassumption.
        lia. unfold one; simpl in *; lia.

        do 3 eexists. split; [| split ].
        econstructor 2; eauto. now econstructor; eauto.
        eapply Hcompat; try eassumption.
        eapply preord_res_monotonic. eassumption.
        simpl in *. rewrite to_nat_add. unfold one. simpl in *. lia.
    Qed.

    (* TODO check if can be avoided *)
    Lemma preord_exp_constr_compat_alt k rho1 rho2 x x' t ys1 ys2 e1 e2
          (Hcompat : post_constr_compat' x t ys1 e1 rho1 x' t ys2 e2 rho2 P1 P2)
          (HOOT : post_OOT' (Econstr x t ys1 e1) rho1 (Econstr x' t ys2 e2) rho2 P2):
      Forall2 (preord_var_env PG k rho1 rho2) ys1 ys2 ->
      (forall m (vs1 vs2 : list val),
          m < k ->
          get_list ys1 rho1 = Some vs1 ->
          get_list ys2 rho2 = Some vs2 ->
          preord_exp P1 PG m (e1, M.set x (Vconstr t vs1) rho1)
                     (e2, M.set x' (Vconstr t vs2) rho2)) ->
      preord_exp P2 PG k (Econstr x t ys1 e1, rho1) (Econstr x' t ys2 e2, rho2).
    Proof.
      intros Hall Hpre v1 cin cout Hleq1 Hstep1. inv Hstep1.
      - (* OOT *)
        exists OOT, cin, <0>. split. constructor; eassumption.
        split; [| now eauto ]. eapply HOOT. eassumption.
      - inv H. edestruct (preord_var_env_get_list PG rho1 rho2) as [vs2' [Hget' Hpre']];
                 [| eauto |]; eauto.

        rewrite to_nat_add in Hleq1.
        assert (Hg := to_nat_one (exp_to_fin (Econstr x t ys1 e1))).

        edestruct (Hpre (k - to_nat (one (Econstr x t ys1 e1)))) as [v2 [cin' [cout' [Hstep [Hpost Hval]]]]];
          [| | | | eassumption | ]; eauto.
        unfold one in *; simpl in *. lia. lia.

        do 3 eexists. split; [| split ].
        econstructor 2; eauto. now econstructor; eauto.
        eapply Hcompat; eassumption.
        eapply preord_res_monotonic. eassumption.
        rewrite to_nat_add. unfold one in *; simpl in *. lia.
    Qed.


    Lemma preord_exp_proj_compat k rho1 rho2 x x' tau n y1 y2 e1 e2
          (Hcompat : post_proj_compat' x tau n y1 e1 rho1 x' tau n y2 e2 rho2 P1 P2)
          (HOOT : post_OOT' (Eproj x tau n y1 e1) rho1 (Eproj x' tau n y2 e2) rho2 P2):
      preord_var_env PG k rho1 rho2 y1 y2 ->
      (forall m v1 v2,
          m < k ->
          preord_val PG m v1 v2 ->
          preord_exp P1 PG m (e1, M.set x v1 rho1)
                     (e2, M.set x' v2 rho2)) ->
      preord_exp P2 PG k (Eproj x tau n y1 e1, rho1) (Eproj x' tau n y2 e2, rho2).
    Proof.
      intros Henv Hexp v1 cin cout Hleq1 Hstep1. inv Hstep1.
      - (* ΟΟΤ *)
        exists OOT, cin, <0>. split. constructor; eassumption.
        split; [| now eauto ]. eapply HOOT. eassumption.
      - inv H. edestruct Henv as [v' [Hget Hpre]]; eauto.
        destruct v'; rewrite preord_val_eq in Hpre; simpl in Hpre; try contradiction.
        inv Hpre.
        rewrite to_nat_add in Hleq1.
        assert (Hg := to_nat_one (exp_to_fin (Eproj x c n y1 e1))).

        edestruct (Forall2_nthN (preord_val PG k) vs l) as [v2 [Hnth Hval]];
          try eassumption.
        edestruct (Hexp  (k - 1)) as [v2' [cin' [cout' [Hstep [Hpost Hval']]]]];
          [ | | | eassumption | ]; eauto.
        unfold one in *; simpl in *; lia.
        eapply preord_val_monotonic. eassumption. lia.
        unfold one in *; simpl in *. lia.

        do 3 eexists. split; [| split ].
        econstructor 2; eauto. now econstructor 2; eauto.
        eapply Hcompat; try eassumption.
        eapply preord_res_monotonic. eassumption.
        rewrite to_nat_add. unfold one; simpl in *; lia.
    Qed.

    (* TODO move *)
    Lemma Forall2_Forall2_asym_included {A} R (l1 l2 : list A) :
      Forall2 R l1 l2 ->
      Forall2_asym R l1 l2.
    Proof.
      intros H. induction H; eauto.
    Qed.

    Lemma preord_exp_app_compat k rho1 rho2 x1 x2 ft ys1 ys2
          (Hcompat : post_app_compat' x1 ft ys1 rho1 x2 ft ys2 rho2 P2 PG)
          (HOOT : post_OOT' (Eapp x1 ft ys1) rho1 (Eapp x2 ft ys2) rho2 P2):
      preord_var_env PG k rho1 rho2 x1 x2 ->
      Forall2 (preord_var_env PG k rho1 rho2) ys1 ys2 ->
      preord_exp P2 PG k (Eapp x1 ft ys1, rho1) (Eapp x2 ft ys2, rho2).
    Proof.
      intros Hvar Hall v1 cin cout Hleq1 Hstep1. inv Hstep1.
      - (* ΟΟΤ *)
        exists OOT, cin, <0>.  split. constructor; eassumption.
        split; [| now eauto ]. eapply HOOT. eassumption.
      - inv H. edestruct Hvar as [v2' [Hget Hpre]]; eauto.
        rewrite preord_val_eq in Hpre.
        destruct v2'; try (now simpl in Hpre; contradiction).
        edestruct preord_var_env_get_list as [vs2 [Hget' Hpre']]; eauto.
        edestruct (Hpre vs vs2 (k - to_nat (one (Eapp x1 ft ys1)))) as [xs2 [e2 [rho2' [Hf' [Hset H']]]]]; eauto.
        now eapply Forall2_length; eauto.
        rewrite to_nat_add in Hleq1.
        assert (Hg := to_nat_one (exp_to_fin (Eapp x1 ft ys1))).

        edestruct H' as [v2 [cin' [cout' [Hstep' [Hpost' Hpre'']]]]];
          eauto; try (unfold one in *; simpl in *; lia).
        + eapply Forall2_monotonic; [| now eauto ].
          intros. eapply (preord_val_monotonic PG k); [ now eauto | lia ].
        + do 3 eexists. split; [| split ].
          econstructor 2; eauto. now econstructor; eauto.
          eapply Hcompat; eassumption.
          eapply preord_res_monotonic. eassumption.
          rewrite to_nat_add. simpl in *; lia.
    Qed.


    Lemma preord_exp_letapp_compat k rho1 rho2 x x' f1 f2 ft ys1 ys2 e1 e2
          (Hcompat : post_letapp_compat' x f1 ft ys1 e1 rho1 x' f2 ft ys2 e2 rho2 P1 P2 PG)
          (HcompatOOT : post_letapp_compat_OOT' x f1 ft ys1 e1 rho1 x' f2 ft ys2 e2 rho2 P2 PG)
          (HOOT : post_OOT' (Eletapp x f1 ft ys1 e1) rho1 (Eletapp x' f2 ft ys2 e2) rho2 P2) :
      preord_var_env PG k rho1 rho2 f1 f2 ->
      Forall2 (preord_var_env PG k rho1 rho2) ys1 ys2 ->
      (forall m v1 v2,
          m < k ->
          preord_val PG m v1 v2 ->
          preord_exp P1 PG m (e1, M.set x v1 rho1)
                     (e2, M.set x' v2 rho2)) ->
      preord_exp P2 PG k (Eletapp x f1 ft ys1 e1, rho1) (Eletapp x' f2 ft ys2 e2, rho2).
    Proof.
      intros Henv Hall Hexp v1 cin cout Hleq1 Hstep1. inv Hstep1.
      - (* ΟΟΤ *)
        exists OOT, cin, <0>. split. constructor; eassumption.
        split; [| now eauto ]. eapply HOOT. eassumption.
      - inv H.
        + (* App terminates *)
          edestruct Henv as [v' [Hget Hpre]]; eauto.
          rewrite preord_val_eq in Hpre.
          destruct v'; try (now simpl in Hpre; contradiction).
          rewrite !to_nat_add in Hleq1.
          assert (Hg := to_nat_one (exp_to_fin (Eletapp x f1 ft ys1 e1))).

          edestruct preord_var_env_get_list as [vs2 [Hget' Hpre']]; eauto.
          edestruct (Hpre vs vs2 (k - to_nat (one (Eletapp x f1 ft ys1 e1)))) as [xs2 [e2' [rho2' [Hf' [Hset H']]]]]; eauto.
          now eapply Forall2_length; eauto.

          edestruct H' with (cin := cin1) as [v2 [cin' [cout' [Hstep' [Hpost' Hpre'']]]]].
          unfold one in *; simpl in *; lia.

          eapply Forall2_monotonic; [| eassumption ]. intros. eapply preord_val_monotonic.
          eassumption. lia. simpl in *; lia. eassumption.


          destruct v2; try contradiction. simpl in Hpre''.
          edestruct Hexp as [v2' [cin'' [cout'' [Hstep  [Hpost Hval']]]]]; [ | eassumption | | eassumption | ]; eauto.
          repeat eexists. unfold one in *; simpl in *; lia.
          simpl in *; lia.

          repeat eexists.
          * econstructor 2. econstructor; eauto.
          * eapply Hcompat; eassumption.
          * eapply preord_res_monotonic. eassumption.
            rewrite !to_nat_add; lia.
        + edestruct Henv as [v' [Hget Hpre]]; eauto.
          rewrite preord_val_eq in Hpre.
          destruct v'; try (now simpl in Hpre; contradiction).
          edestruct preord_var_env_get_list as [vs2 [Hget' Hpre']]; eauto.
          edestruct (Hpre vs vs2 (k - to_nat (one (Eletapp x f1 ft ys1 e1)))) as [xs2 [e2' [rho2' [Hf' [Hset H']]]]]; eauto.
          now eapply Forall2_length; eauto.
          rewrite !to_nat_add in Hleq1.
          assert (Hg := to_nat_one (exp_to_fin (Eletapp x f1 ft ys1 e1))).

          edestruct H'; try eassumption. unfold one in *; simpl in *; lia.
          eapply Forall2_monotonic; [| eassumption ]. intros. eapply preord_val_monotonic.
          eassumption. simpl in *; lia. simpl in *; lia.

          destructAll. repeat eexists.

          destruct x0; try contradiction. econstructor 2; eauto. now eapply BStept_letapp_oot; eauto.
          eapply HcompatOOT; eassumption.
          eauto.
    Qed.

    Lemma preord_exp_halt_compat k rho1 rho2 x1 x2
          (HOOT : post_OOT' (Ehalt x1) rho1 (Ehalt x2) rho2 P2)
          (Hbase : post_base' x1 rho1 x2 rho2 P2):
      preord_var_env PG k rho1 rho2 x1 x2 ->
      preord_exp P2 PG k (Ehalt x1, rho1) (Ehalt x2, rho2).
    Proof.
      intros Hvar v1 c1 cout Hleq1 Hstep1. inv Hstep1.
      - (* ΟΟΤ *)
        exists OOT, c1, <0>. split. constructor; eauto; eassumption.
        split; [| now eauto ]. eapply HOOT. eassumption.
      - inv H. edestruct Hvar as [v2' [Hget Hpre]]; eauto.
        rewrite !to_nat_add in Hleq1.
        assert (Hg := to_nat_one (exp_to_fin (Ehalt x1))).

        repeat eexists. econstructor 2; eauto. econstructor; eauto.

        rewrite !plus_zero.
        eapply Hbase.
        eapply preord_val_monotonic. eassumption. lia.
    Qed.

    Lemma preord_exp_case_nil_compat k rho1 rho2 x1 x2
          (HOOT : post_OOT' (Ecase x1 []) rho1 (Ecase x2 []) rho2 P2):
      preord_exp P2 PG k (Ecase x1 [], rho1) (Ecase x2 [], rho2).
    Proof.
      intros v1 c1 cout Hleq1 Hstep1. inv Hstep1.
      - (* ΟΟΤ *)
        exists OOT, c1, <0>. split. constructor; eauto; eassumption.
        split; [| now eauto ]. eapply HOOT; eassumption.
      - inv H. inv H5.
    Qed.

    Lemma preord_exp_case_cons_compat k rho1 rho2 x1 x2 c e1 e2 D1 D2
          (Hcompat_hd : post_case_compat_hd' x1 c e1 D1 rho1  x2 c e2 D2 rho2 P1 P2)
          (Hcompat_tl : post_case_compat_tl' x1 c e1 D1 rho1  x2 c e2 D2 rho2 P2 P2)
          (HOOT : post_OOT' (Ecase x1 ((c, e1) :: D1)) rho1 (Ecase x2 ((c, e2) :: D2)) rho2 P2) :
      Forall2 (fun p p' => fst p = fst p') D1 D2 ->
      preord_var_env PG k rho1 rho2 x1 x2 ->
      (forall m, m < k -> preord_exp P1 PG m (e1, rho1) (e2, rho2)) ->
      preord_exp P2 PG k (Ecase x1 D1, rho1)
                 (Ecase x2 D2, rho2) ->
      preord_exp P2 PG k (Ecase x1 ((c, e1) :: D1), rho1)
                 (Ecase x2 ((c, e2) :: D2), rho2).
    Proof.
      intros Hall Henv Hexp_hd Hexp_tl v1 c1 cout Hleq1 Hstep1. inv Hstep1.
      - (* ΟΟΤ *)
        exists OOT, c1, <0>. split. constructor; eauto; eassumption.
        split; [| now eauto ]. eapply HOOT; eassumption.
      - inv H. inv H3.
        rewrite !to_nat_add in Hleq1.
        assert (Hg := to_nat_one (exp_to_fin (Ecase x1 ((c, e1) :: D1)))).
        destruct (var_dec c t).
        + inv H5; [| contradiction ]; subst.
          edestruct (Hexp_hd (k - 1)) as [v2 [c2 [cout' [Hstep2 [Hpost Hpre2]]]]];
            [ | | eassumption | ]; eauto.

          unfold one in *; simpl in *; lia. unfold one in *; simpl in *; lia.

          edestruct Henv as [v2' [Hget Hpre]]; eauto.
          rewrite preord_val_eq in Hpre.
          destruct v2'; try (now simpl in Hpre; contradiction). inv Hpre.
          repeat subst_exp.
          repeat eexists. econstructor 2. econstructor; eauto.

          econstructor 2; eauto. eapply caseConsistent_same_ctor_tags. eassumption. eassumption.
          now constructor.

          eapply Hcompat_hd. eassumption.
          eapply preord_res_monotonic. eassumption.
          rewrite to_nat_add. unfold one in *; simpl in *; lia.
        + inv H5. contradiction.
          edestruct Hexp_tl as [v2 [c2 [cout' [Hstep2 [Hpost2 Hpre2]]]]].
          2:{ econstructor 2; eauto. econstructor; eauto. }
          * rewrite to_nat_add. unfold one in *. simpl in *; lia.
          * eapply Henv in H2. destruct H2 as [v2' [Hgetx2 Hval]].
            assert (Hval' := Hval). rewrite preord_val_eq in Hval'.
            destruct v2'; try contradiction. simpl in Hval'. inv Hval'.
            inv Hstep2.
            -- destruct v1; try contradiction.
               exists OOT, c2, <0>. split; [| split ]. econstructor 1.
               simpl in *; eassumption. eapply Hcompat_tl. eassumption.
               eauto.
            -- inv H.  repeat subst_exp.
               do 3 eexists. split; [| split ].
               ++ constructor 2. econstructor; eauto. econstructor; eauto.
                  econstructor; eauto.
               ++ eapply Hcompat_tl. eassumption.
               ++ eassumption.
    Qed.

    (* Slightly stronger version *)
    Lemma preord_exp_case_cons_compat_alt k rho1 rho2 x1 x2 c e1 e2 D1 D2
          (Hcompat_hd : post_case_compat_hd' x1 c e1 D1 rho1  x2 c e2 D2 rho2 P1 P2)
          (Hcompat_tl : post_case_compat_tl' x1 c e1 D1 rho1  x2 c e2 D2 rho2 P2 P2)
          (HOOT : post_OOT' (Ecase x1 ((c, e1) :: D1)) rho1 (Ecase x2 ((c, e2) :: D2)) rho2 P2) :
      Forall2 (fun p p' => fst p = fst p') D1 D2 ->
      ((exists c vs, rho1 ! x1 = Some (Vconstr c vs)) -> preord_var_env PG k rho1 rho2 x1 x2) ->
      (forall m, m < k -> preord_exp P1 PG m (e1, rho1) (e2, rho2)) ->
      preord_exp P2 PG k (Ecase x1 D1, rho1)
                 (Ecase x2 D2, rho2) ->
      preord_exp P2 PG k (Ecase x1 ((c, e1) :: D1), rho1)
                 (Ecase x2 ((c, e2) :: D2), rho2).
    Proof.
      intros Hall Henv Hexp_hd Hexp_tl v1 c1 cout Hleq1 Hstep1. inv Hstep1.
      - (* ΟΟΤ *)
        exists OOT, c1, <0>. split. constructor; eauto; eassumption.
        split; [| now eauto ]. eapply HOOT; eassumption.
      - inv H. inv H3.
        specialize (Henv ltac:(do 2 eexists; eassumption)).
        eapply preord_exp_case_cons_compat; eauto.
        econstructor 2. econstructor; eauto. econstructor; eauto.
    Qed.




    Axiom Prim_axiom :
      forall f f' v1,
        M.get f pr = Some f' ->
        forall k vs1 vs2,
          Forall2 (preord_val PG k) vs1 vs2 ->
          f' vs1 = Some v1 ->
          exists v2,
            f' vs2 = Some v2 /\
            preord_val PG k v1 v2.
 (*
    Lemma preord_exp_prim_compat k rho1 rho2 x1 x2 f ys1 ys2 e1 e2 :
      Forall2 (preord_var_env PG k rho1 rho2) ys1 ys2 ->
      (forall m v1 v2,
          m < k ->
          preord_val PG m v1 v2 ->
          preord_exp P1 PG m (e1, M.set x1 v1 rho1)
                     (e2, M.set x2 v2 rho2)) ->
      preord_exp P2 PG k (Eprim x1 f ys1 e1, rho1) (Eprim x2 f ys2 e2, rho2).
    Proof.
      intros Hall Hpre v1 cin Hleq1 Hstep1.
      destruct (lt_dec cin (cost (Eprim x1 f ys1 e1))); inv Hstep1; try lia.
      - (* OOT *)
        exists OOT, cin. split. constructor.
        simpl in *. erewrite <- Forall2_length; [| eassumption ].
        eassumption. split; [| now eauto ]. eapply HPostRefl2.
      - inv H0.
        edestruct preord_var_env_get_list as [vs2 [Hget' Hpre']]; eauto.
        edestruct Prim_axiom as [v2 [Heq Hprev2]]; eauto.
        edestruct (Hpre (k - 1)) as [v2' [c2 [Hstepv2' [Hpost2 Hprev2']]]]; [ | | | eassumption | ]; eauto.
        simpl in *; lia.
        eapply preord_val_monotonic. eassumption.
        lia. simpl in *; lia.
        eexists. exists (c2 + cost (Eprim x2 f ys2 e2)). split; [| split ].
        econstructor 2; eauto. lia.
        econstructor; eauto.
        replace (c2 + cost (Eprim x2 f ys2 e2) - cost (Eprim x2 f ys2 e2)) with c2 by lia.
        eassumption.
        replace cin with (cin - cost (Eprim x1 f ys1 e1) + cost (Eprim x2 f ys2 e2)).
          2:{ simpl in *. eapply Forall2_length in Hall. rewrite Hall. lia. }
        eapply HPost. eassumption.
        eapply preord_res_monotonic. eassumption.
        simpl in *. lia.
    Qed.
*)

    Lemma preord_exp_prim_val_compat k rho1 rho2 x1 x2 p e1 e2
      (HOOT : post_OOT' (Eprim_val x1 p e1) rho1 (Eprim_val x2 p e2) rho2 P2) :
      preord_exp P2 PG k (Eprim_val x1 p e1, rho1) (Eprim_val x2 p e2, rho2).
    Proof.
      intros v1 cin cout Hleq1 Hstep1. inv Hstep1.
      - (* OOT *)
        exists OOT, cin, <0>. split. econstructor. eassumption.
        split; [| now eauto ]. eapply HOOT; eassumption.
      - inv H.
    Qed.

    Lemma preord_exp_prim_compat k rho1 rho2 x1 x2 f ys1 ys2 e1 e2
      (HOOT : post_OOT' (Eprim x1 f ys1 e1) rho1 (Eprim x2 f ys2 e2) rho2 P2) :

      Forall2 (preord_var_env PG k rho1 rho2) ys1 ys2 ->
      preord_exp P2 PG k (Eprim x1 f ys1 e1, rho1) (Eprim x2 f ys2 e2, rho2).
    Proof.
      intros Hall v1 cin cout Hleq1 Hstep1. inv Hstep1.
      - (* OOT *)
        exists OOT, cin, <0>. split. econstructor. eassumption.
        split; [| now eauto ]. eapply HOOT; eassumption.
      - inv H.
    Qed.


    Lemma preord_exp_fun_compat k rho1 rho2 B B' e1 e2
          (HOOT : post_OOT' (Efun B e1) rho1 (Efun B' e2) rho2 P2)
          (Hcompat : post_fun_compat' B e1 rho1 B' e2 rho2 P1 P2) :

      preord_exp P1 PG (k - 1) (e1, def_funs B B rho1 rho1)
                 (e2, def_funs B' B' rho2 rho2) ->
      preord_exp P2 PG k (Efun B e1, rho1) (Efun B' e2, rho2).
    Proof.
      intros Hexp v1 c1 cout2 Hleq1 Hstep1. inv Hstep1.
      - (* OOT *)
        exists OOT, c1, <0>. split. constructor; eassumption.
        split.
        eapply HOOT. eassumption.
        simpl; eauto.
      - inv H.
        rewrite !to_nat_add in Hleq1.
        assert (Hg := to_nat_one (exp_to_fin (Efun B e1))).

        edestruct Hexp as [v2' [c2 [cout' [Hstepv2' [Hprev2' Hpost]]]]];
          [ | eassumption | ]; eauto.

        unfold one in *; simpl in *; lia.

        repeat eexists.

        econstructor 2; eauto. now econstructor; eauto.
        eapply Hcompat. eassumption.
        eapply preord_res_monotonic. eassumption. rewrite to_nat_add. unfold one in *; simpl in *; lia.
    Qed.

    Lemma preord_exp_Efun_l k boundG rho1 rho2 B e e' (HOOT : post_OOT P2) :
      post_Efun_l P1 P2 ->
      preord_exp P1 boundG (k - 1) (e, def_funs B B rho1 rho1) (e', rho2) ->
      preord_exp P2 boundG k (Efun B e, rho1) (e', rho2).
    Proof.
      intros Hyp Hexp. intros v1' c1 cout Hleq1 Hstep1. inv Hstep1; repeat subst_exp.
      - exists OOT, c1, <0>. split. econstructor; eauto.
        unfold one. erewrite one_eq. eassumption. split. eapply HOOT. eassumption.
        simpl; eauto.
      - inv H.
        rewrite !to_nat_add in Hleq1.
        assert (Hg := to_nat_one (exp_to_fin (Efun B e))).

        edestruct Hexp as [v2' [c2 [cout' [Hstep2 [Hub Hcc2]]]]]; [| eassumption | ]; try (unfold one in *; simpl in *; lia).

        repeat eexists; eauto.
        eapply preord_res_monotonic. eassumption. rewrite to_nat_add. unfold one in *; simpl in *; lia.
    Qed.

    Lemma preord_exp_Efun_r k boundG rho1 rho2 B e e' (HOOT : post_OOT P2) :
      post_Efun_r P1 P2 ->
      preord_exp P1 boundG k (e, rho1) (e', def_funs B B rho2 rho2) ->
      preord_exp P2 boundG k (e, rho1) (Efun B e', rho2).
    Proof.
      intros Hyp Hexp. intros v1' c1 cout Hleq1 Hstep1. inv Hstep1; repeat subst_exp.
      - exists OOT, c1, <0>. split. econstructor; eauto.
        unfold one. erewrite one_eq. eassumption. split.
        eapply HOOT. eassumption.
        simpl; eauto.
      - edestruct Hexp as [v2' [c2 [cout' [Hstep2 [Hub Hcc2]]]]]; [| constructor 2; eassumption | ].
        unfold one in *; simpl in *; lia.

        repeat eexists; eauto. econstructor 2. econstructor. eassumption.
    Qed.

    Lemma preord_exp_app_r
      (k : nat) (rho1 rho2 rhoc rho' : env) (f f' : var) (ft : fun_tag)
      (ys xs : list var) e1 e2 B vs :
      post_Eapp_r P1 P2 e1 rho1 f ft ys rho2 ->
      M.get f rho2 = Some (Vfun rhoc B f') ->
      get_list ys rho2 = Some vs ->
      find_def f' B = Some (ft, xs, e2) ->
      set_lists xs vs (def_funs B B rhoc rhoc) = Some rho' ->
      preord_exp P1 PG k (e1, rho1) (e2, rho') ->
      preord_exp P2 PG k (e1, rho1) (Eapp f ft ys, rho2).
    Proof.
      intros Hypc Hget Hgetl Hf' Hset Hexp v c1 Hleq Hstep Hns.
      edestruct Hexp as (v2 & c2 & cout & Hstep' & Hpost & Hval); eauto.
      do 3 eexists. split.
      econstructor 2; eauto. econstructor; eauto. split.
      eapply Hypc. now eauto.
      eassumption.
    Qed.

    Lemma preord_exp_app_l
          (k : nat) (rho1 rho2 : env) (f : var) (ft : fun_tag)
          (ys : list var) e2
      (Hls : post_Eapp_l P1 P2 f ft ys rho1 e2 rho2)
      (HOOT : post_OOT  P2) :
      (forall rhoc rho' e1 vs f' xs B,
          get_list ys rho1 = Some vs ->
          M.get f rho1 = Some (Vfun rhoc B f') ->
          find_def f' B = Some (ft, xs, e1) ->
          set_lists xs vs (def_funs B B rhoc rhoc) = Some rho' ->
          preord_exp P1 PG k (e1, rho') (e2, rho2)) ->
      preord_exp P2 PG k (Eapp f ft ys, rho1) (e2, rho2).
    Proof.
      intros Hyp v c1 cout Hleq Hstep. inv Hstep.
      - eexists OOT, c1, <0>. split; [| split ].
        econstructor; eauto.
        unfold one. erewrite one_eq. eassumption. eapply HOOT. eassumption.
        simpl; eauto.
      - inv H. repeat subst_exp. rewrite to_nat_add in Hleq.
        edestruct Hyp as (v2 & c2 & cout' & Hstep' & Hpost & Hval); [ | | | | | eassumption | ]; eauto.
        lia.

        eexists. exists c2, cout'. split; [ eassumption | split ].
        eapply Hls; eauto.
        eapply preord_res_monotonic. eassumption. rewrite to_nat_add. lia.
    Qed.

    Fixpoint exp_ctx_len (c : exp_ctx) : nat :=
      match c with
      | Hole_c => 0
      | Econstr_c _ _ ys c => 1 + exp_ctx_len c
      | Eproj_c _ _ _ _ c => 1 + exp_ctx_len c
      | Eprim_val_c _ _ c => 1 + exp_ctx_len c
      | Eprim_c _ _ ys c => 1 + exp_ctx_len c
      | Eletapp_c _ f _ ys c => 1 + exp_ctx_len c
      | Ecase_c _ l1 _ c l2  => 1 + exp_ctx_len c
      | Efun1_c B c => 1 + exp_ctx_len c
      | Efun2_c B e => 1 + fundefs_ctx_len B
      end
    with fundefs_ctx_len (B : fundefs_ctx) : nat :=
           match B with
           | Fcons1_c _ _ xs c B =>
             1 + exp_ctx_len c
           | Fcons2_c _ _ xs e B =>
             1 + fundefs_ctx_len B
           end.

    (** Context application lemma *)
    (** [(e1, ρ1) < (C [ e2 ], ρ2)] if [(e1, ρ1) < (e2, ρ2')], where [ρ2'] is the
      interpretation of [C] in [ρ2] *)
    Lemma ctx_to_rho_preord_exp k (P : nat -> PostT) boundG rho1 rho2 rho2' C e e' m :
      (forall n e2 rho2 rho2' C c1 c2 cout1 cout2,
          ctx_to_rho C rho2 rho2' ->
          P n (e, rho1, c1, cout1) (e2, rho2', c2, cout2) ->
          P (n + to_nat (one_ctx C)) (e, rho1, c1, cout1) (C |[ e2 ]|, rho2, c2 <+> one_ctx C, cout2 <+> one_ctx C)) ->
      ctx_to_rho C rho2 rho2' ->
      preord_exp (P m) boundG k (e, rho1) (e', rho2') ->
      preord_exp (P (m + exp_ctx_len C)) boundG k (e, rho1) (C |[ e' ]|, rho2).
    Proof.
      intros H1 Hctx Hcc. revert m Hcc; induction Hctx; intros m Hcc.
      - intros v1' c1 Hleq1 Hstep1 Hns.
        edestruct Hcc as [v2' [c2 [cout2 [Hstep2 [Hub Hcc2]]]]]; try eassumption.
        simpl in *. rewrite Nat_as_OT.add_0_r in *. firstorder.
      - intros v1 c1 cout1 Hleq1 Hstep1.
        edestruct IHHctx as [v2 [c2 [cout2 [Hstep2 [HP Hcc2]]]]]; try eassumption.
        simpl exp_ctx_len.
        replace (m + S (exp_ctx_len C)) with ((m + exp_ctx_len C) + 1) by lia.
        exists v2, (c2 <+> one ((Eproj_c y t N Γ C |[ e' ]|))). repeat eexists.
        econstructor 2; eauto. econstructor; eauto.

        erewrite <- !to_nat_one. unfold one. eapply H1 with (C := Eproj_c y t N Γ Hole_c); eauto.
        econstructor; eauto. now econstructor.
        eassumption.
      - intros v1' c1 Hleq1 Hstep1 Hns.
        edestruct IHHctx as [v2' [c2 [cout2 [Hstep2 [Hub Hcc2]]]]]; try eassumption.
        simpl exp_ctx_len.
        replace (m + S (@Datatypes.length var ys + exp_ctx_len C))
          with ((m + exp_ctx_len C) + (1 + @Datatypes.length var ys)) by lia.
        exists v2', (c2 <+> one (Econstr_c x t ys C |[ e' ]|)). repeat eexists.
        econstructor 2; eauto. econstructor; eauto.
        simpl. replace (m + S (exp_ctx_len C)) with ((m + exp_ctx_len C) + 1).

        erewrite <- !(@to_nat_one _ fuel). unfold one. eapply H1 with (C := Econstr_c x t ys Hole_c); eauto.
        econstructor; eauto. econstructor; eauto.
        replace (m + S (@Datatypes.length var ys)) with (m + 1 + @Datatypes.length var ys) by lia. simpl; lia.
        eassumption.
      - intros v1' c1 cout2 Hleq1 Hstep1.
        simpl exp_ctx_len.
        replace (m + S (exp_ctx_len C)) with (m + exp_ctx_len C + 1) by lia.
        edestruct IHHctx as [v2' [c2 [cout2' [Hstep2 [Hub Hcc2]]]]];
          [ | | eassumption | ].
        + eassumption.
        + eassumption.
        + exists v2', (c2 <+> one (Efun1_c B C |[ e' ]|)). repeat eexists.
          econstructor 2; eauto. econstructor; eauto.
          simpl.
          erewrite <- to_nat_one. unfold one. eapply H1 with (C := Efun1_c B Hole_c); eauto.
          econstructor; eauto. econstructor; eauto.
          eassumption.
    Qed.


    Fixpoint len_exp_ctx (c : exp_ctx) :=
      match c with
      | Econstr_c _ _ _ c
      | Eproj_c _ _ _ _ c
      | Eprim_val_c _ _ c
      | Eprim_c _ _ _ c
      | Efun1_c _ c => 1 + len_exp_ctx c
      | Efun2_c _ _
      | Eletapp_c _ _ _ _ _
      | Ecase_c _ _ _ _ _ => 2
      | Hole_c => 0
      end.

  (** Context application lemma, left *)
  (** [(C |[ e1 ]|, ρ1) < (e2, ρ2)] if [(e1, ρ1) < (e2, ρ2')], where [ρ2'] is the
      interpretation of [C] in [ρ2] *)
  Lemma ctx_to_rho_preord_exp_l k boundG rho1 rho2 C e e' :
    (forall rho1' e2 rho2 c1 c2 cout1 cout2,
       ctx_to_rho C rho1 rho1' ->
       P1 (e, rho1', c1, cout1) (e2, rho2, c2, cout2) ->
       P2 (C |[ e ]|, rho1, c1 <+> (one (C |[ e ]|)), cout1 <+> (one (C |[ e ]|))) (e2, rho2, c2, cout2)) ->
    post_OOT P2 ->
    len_exp_ctx C = 1 ->
    (forall rho1', ctx_to_rho C rho1 rho1' -> preord_exp P1 boundG k (e, rho1') (e', rho2)) ->
    preord_exp P2 boundG k (C |[ e ]|, rho1) (e', rho2).
  Proof.
    intros H1 Hzero Hlen Hcc.
    destruct C; try (simpl in Hlen; lia); try (destruct C; simpl in Hlen; try lia).
    - intros v1 c1 cout1 Hleq1 Hstep1. inv Hstep1.
      + simpl in *. eexists OOT, c1, <0>. split.
        econstructor 1. unfold one. erewrite one_eq. eassumption.
        split; eauto. eapply Hzero. eassumption.
      + inv H. repeat subst_exp. rewrite to_nat_add in *.
        edestruct Hcc as [v2' [c2 [cout2 [Hstep2 [Hub Hcc2]]]]]; [| | eassumption| ]; try lia.
        econstructor; eauto. now econstructor.

        repeat eexists; eauto.


        eapply H1; eauto. econstructor; eauto. now econstructor.
        eapply preord_res_monotonic. eassumption. lia.
    - intros v1 c1 cout1 Hleq1 Hstep1. inv Hstep1.
      + simpl in *. exists OOT, c1, <0>. split.
        econstructor 1. unfold one. erewrite one_eq. eassumption.
        split; eauto. eapply Hzero. eassumption.
      + inv H. rewrite to_nat_add in *.
        edestruct Hcc as [v2' [c2 [cout2 [Hstep2 [Hub Hcc2]]]]]; [| | eassumption | ]; try lia.
        econstructor; eauto. now econstructor.

        repeat eexists; eauto. simpl in *.
        eapply H1; eauto. econstructor; eauto. now econstructor.
        eapply preord_res_monotonic. eassumption. lia.

    - intros v' c1 cout1 Hleq1 Hstep1. inv Hstep1.
      + simpl in *. exists OOT, c1, <0>. split.
        econstructor 1. unfold one. erewrite one_eq. eassumption.
        split; eauto. eapply Hzero. eassumption.
      + inv H.
    - intros v' c1 cout1 Hleq1 Hstep1. inv Hstep1.
      + simpl in *. exists OOT, c1, <0>. split.
        econstructor 1. unfold one. erewrite one_eq. eassumption.
        split; eauto. eapply Hzero. eassumption.
      + inv H.
    - intros v' c1 cout1 Hleq1 Hstep1. inv Hstep1.
      + simpl in *. exists OOT, c1, <0>. split.
        econstructor 1. unfold one. erewrite one_eq. eassumption.
        split; eauto. eapply Hzero. eassumption.
      + inv H. repeat subst_exp. rewrite to_nat_add in *.
        edestruct Hcc as [v2' [c2 [cout2 [Hstep2 [Hub Hcc2]]]]]; [| | eassumption | ]; try lia.

        econstructor; eauto. now econstructor.

        repeat eexists; eauto. simpl in *.
        eapply H1; eauto. econstructor; eauto. now econstructor.
        eapply preord_res_monotonic. eassumption. lia.
  Qed.

    (** Context application lemma, left *)
    (** [(C |[ e1 ]|, ρ1) < (e2, ρ2)] if [(e1, ρ1) < (e2, ρ2')], where [ρ2'] is the
       interpretation of [C] in [ρ2] *)
    Lemma ctx_to_rho_preord_exp_l_old k (L : nat -> PostT) boundG rho1 rho1' rho2 C e e' m :
      ctx_to_rho C rho1 rho1' ->
      preord_exp (L m) boundG k (e, rho1') (e', rho2) ->
      preord_exp (L (m + exp_ctx_len C)) boundG k (C |[ e ]|, rho1) (e', rho2).
    Proof.
    Abort.
(*      intros H1 Hctx Hcc. revert m Hcc; induction Hctx; intros m Hcc.
      - intros v1' c1 Hleq1 Hstep1.
        edestruct Hcc as [v2' [c2 [Hstep2 [Hub Hcc2]]]]; try eassumption.
        simpl in *. repeat eexists; eauto.
        rewrite <- plus_n_O. eassumption.
      - intros v1 c1 Hleq1 Hstep1. inv Hstep1.
        + simpl in *. exists OOT.
        repeat subst_exp.

        edestruct I HHctx as [v2 [c2 [Hstep2 [HP Hcc2]]]]; [| eassumption | | | ]; try lia.
          + intros. eapply H1; eauto. simpl; lia.
          + eassumption.
          +
             repeat eexists; eauto.
          simpl.
          replace (m + S (size_cps.exp_ctx_len C)) with (m + size_cps.exp_ctx_len C + 1) by lia.
          eapply H1; eauto. simpl; lia.
          eapply preord_val_monotonic. eassumption. lia.
        - intros v1' c1 Hleq1 Hstep1. inv Hstep1. repeat subst_exp.
          edestruct IHHctx as [v2' [c2 [Hstep2 [Hub Hcc2]]]]; [| eassumption | | eassumption | ]; try lia.
          intros. eapply H1; eauto. simpl; lia.
          repeat eexists; eauto.
          simpl.
          rewrite <- (plus_assoc c 1 _).
          replace (m + S (@Datatypes.length var ys + size_cps.exp_ctx_len C))
            with ((m + (size_cps.exp_ctx_len C)) + (1 + @Datatypes.length var ys)) by lia.
          eapply H1; eauto. simpl; lia.
          eapply preord_val_monotonic. eassumption. lia.
        - intros v1' c1 Hleq1 Hstep1. inv Hstep1. repeat subst_exp.
          edestruct IHHctx as [v2' [c2 [Hstep2 [Hub Hcc2]]]]; [| eassumption | | eassumption | ]; try lia.
          intros. eapply H1; eauto. simpl; lia.
          repeat eexists; eauto.
          simpl.
          replace (m + S (set_util.PS.cardinal (fundefs_fv B) + size_cps.exp_ctx_len C))
            with ((m + (size_cps.exp_ctx_len C)) + (1 + set_util.PS.cardinal (fundefs_fv B))) by lia.
          eapply H1; eauto. simpl; lia.
          eapply preord_val_monotonic. eassumption. lia.
      Qed. *)



  End Compat.

  Global Instance preord_env_proper  :
    Proper (Logic.eq ==> Same_set var ==> Logic.eq ==> Logic.eq ==> Logic.eq ==> iff)
           preord_env_P.
  Proof.
    intros ? ? ? s1 s2 [H1 H2]; split; intros Hpre; subst;
      eapply preord_env_P_antimon; subst; eauto.
  Qed.

  Lemma preord_exp_post_monotonic k (P1 P2 : PostT) PG e1 rho1 e2 rho2 :
    inclusion _ P1 P2 ->
    preord_exp P1 PG k (e1, rho1) (e2, rho2) ->
    preord_exp P2 PG k (e1, rho1) (e2, rho2).
  Proof.
    intros Hyp Hexp v1 c2 cout2 Hleq Hstep.
    edestruct Hexp as [v2 [c2' [cout2' [Hstep2 [Hp Hv]]]]]; try eassumption.
    do 2 eexists; repeat split; eauto.
  Qed.

  Lemma preord_env_P_eq_r PG S S' k rho1 rho2 rho3 :
      preord_env_P PG S k rho1 rho2 ->
      eq_env_P S' rho2 rho3 ->
      preord_env_P PG (S :&: S') k rho1 rho3.
  Proof.
    intros Henv Heqx x Hin v Hget. inv Hin.
    rewrite <- Heqx; eauto. eapply Henv; eauto.
  Qed.

  Lemma preord_env_P_eq_l PG S S' k rho1 rho2 rho3 :
    preord_env_P PG S k rho1 rho2 ->
    eq_env_P S' rho1 rho3 ->
    preord_env_P PG (S :&: S') k rho3 rho2.
  Proof.
    intros Henv Heqx x Hin v Hget. inv Hin.
    eapply Henv; eauto.
    rewrite Heqx; eauto.
  Qed.

  Lemma preord_env_eq_env PostG k S rho1 rho2 rho1' rho2' :
    preord_env_P PostG S k rho1 rho2 ->
    eq_env_P S rho1 rho1' ->
    eq_env_P S rho2 rho2' ->
    preord_env_P PostG S k rho1' rho2'.
  Proof.
    intros Henv Heq1 Heq2.
    rewrite <- (Intersection_idempotent S).
    eapply preord_env_P_eq_r; eauto.
    rewrite <- (Intersection_idempotent S).
    eapply preord_env_P_eq_l; eauto.
  Qed.


  Section Refl.

    (* PostCondition parameter for the reflexivity proof *)
    Context (P1 : PostT) (* Local *)
            (PG : PostGT) (* Global *)
            (Hprops : Post_properties P1 P1 PG).

   (** * Reflexivity Properties *)

    (** Un-nesting the function case of the reflexivity proof *)
    Lemma preord_env_P_def_funs_pre k B rho rho' B' e (Hinl : inclusion _ P1 PG):
      (* The inductive hypothesis on expressions *)
      (forall m e (rho rho' : env),
          m <  k ->
          preord_env_P PG (occurs_free e) m rho rho' ->
          preord_exp P1 PG m (e, rho) (e, rho')) ->
      (* Environments are related at FV(Efun B' e) *)
      preord_env_P PG (occurs_free (Efun B' e)) k rho rho' ->
      preord_env_P PG (Union _ (occurs_free (Efun B' e)) (name_in_fundefs B))
                   k (def_funs B' B rho rho) (def_funs B' B rho' rho').
    Proof with eauto 6 with Ensembles_DB.
      revert B rho rho' e B'.
      induction k as [ k IH' ] using lt_wf_rec1. intros B rho rho' e B'.
      induction B; intros Hyp Hpre.
      - simpl. apply preord_env_P_extend.
        + eapply preord_env_P_antimon; [ now eapply IHB; eauto | ]...
        + rewrite preord_val_eq.
          intros vs1 vs2 j t1 xs1 e1 rho1' Hlen Hf' Hs.
          edestruct (@set_lists_length val) as [rho2' Hs']; eauto.
          exists xs1. exists e1. exists rho2'. split; eauto.
          split; [ now eauto |]. intros Hleq Hpre'.
          eapply preord_exp_post_monotonic. eassumption.
          eapply Hyp. lia.
          eapply preord_env_P_set_lists_l; [| | eauto | eauto | eauto].
          * apply IH'; eauto. intros. apply Hyp. lia. eauto.
            eapply (preord_env_P_monotonic PG _ k); eauto. lia.
          * intros x Hin Hfr. simpl.
            apply find_def_correct in Hf'; eauto.
            specialize (occurs_free_in_fun _ _ _ _ _ Hf' x Hfr); intros H1.
            inv H1; eauto; try contradiction. inv H.
            now right; eauto. now left; eauto.
      - simpl. intros x HP. inv HP. inv H. apply Hpre; eauto.
        apply Hpre; eauto. inv H.
    Qed.

    (* Reflexivity of any post condition, given that it satisfies the compatibility properties *)
    Lemma preord_exp_refl k e rho rho' :
      preord_env_P PG (occurs_free e) k rho rho' ->
      preord_exp P1 PG k (e, rho) (e, rho').
    Proof with eauto with Ensembles_DB.
      revert e rho rho'.
      (* Well founded induction on the step-index *)
      induction k as [ k IH ] using lt_wf_rec1.
      (* Induction on e *)
      intros e. revert k IH.
      induction e using exp_ind'; intros k IH rho rho' Henv; inv Hprops.
      (* Each case follows from the corresponding compat lemma *)
      - eapply preord_exp_constr_compat; eauto; intros.
        * eapply Forall2_same. intros x HIn. apply Henv. now constructor.
        * eapply IHe. intros. eapply IH; eauto. lia.
          eapply preord_env_P_extend.
          eapply preord_env_P_antimon. eapply preord_env_P_monotonic; [| eassumption ].
          lia.
          now (normalize_occurs_free; eauto with Ensembles_DB).
          rewrite preord_val_eq. constructor; eauto.
      - eapply preord_exp_case_nil_compat. now eauto.
      - eapply preord_exp_case_cons_compat; eauto.
        now apply Forall2_refl.
        intros m Hlt. apply IHe; try eassumption.
        intros. eapply IH; eauto. lia.
        eapply preord_env_P_antimon.
        eapply preord_env_P_monotonic; [| eassumption ]. lia.
        normalize_occurs_free. sets.
        eapply IHe0; eauto.
        eapply preord_env_P_antimon.
        eapply preord_env_P_monotonic; [| eassumption ]. lia.
        normalize_occurs_free. sets.
      - eapply preord_exp_proj_compat; eauto.
        intros m v1 v2 Hlt Hval. apply IHe; try eassumption.
        intros. eapply IH; eauto. lia.
        eapply preord_env_P_extend; eauto.
        eapply preord_env_P_antimon.
        eapply preord_env_P_monotonic; [| eassumption ]. lia.
        now (normalize_occurs_free; eauto with Ensembles_DB).
      - eapply preord_exp_letapp_compat; eauto.
        eapply Henv. constructor. now left.
        eapply Forall2_same. intros. apply Henv. constructor. now right.
        intros m v1 v2 Hlt Hval.
        eapply IHe; try eassumption.
        intros. eapply IH; eauto. lia.
        eapply preord_env_P_extend; eauto.
        eapply preord_env_P_antimon.
        eapply preord_env_P_monotonic; [| eassumption ]. lia.
        now (normalize_occurs_free; eauto with Ensembles_DB).
      - eapply preord_exp_fun_compat; eauto.
        eapply IHe; try eassumption.
        intros. eapply IH; eauto. lia.
        eapply preord_env_P_antimon.
        eapply preord_env_P_def_funs_pre; eauto.
        intros. eapply IH; eauto. lia.
        eapply preord_env_P_monotonic; [| eassumption ]. lia.
        now eapply occurs_free_Efun_Included.
      - eapply preord_exp_app_compat. now eauto. now eauto.
        intros x HP. apply Henv; eauto.
        apply Forall2_same. intros. apply Henv. now constructor.
      - eapply preord_exp_prim_val_compat; eauto; intros.
      - eapply preord_exp_prim_compat; eauto; intros.
        eapply Forall2_same. intros. apply Henv. now constructor.
      - eapply preord_exp_halt_compat; try eassumption. now eauto. now eauto.
        intros x HP. apply Henv; eauto.
    Qed.


  End Refl.

  Section Rel.

    (* PostCondition parameter for the reflexivity proof *)
    Context (P1 : PostT) (* Local *)
            (PG : PostGT) (* Global *)
            (Hprops : Post_properties P1 P1 PG)
            (HpropsG : Post_properties PG PG PG).

  Lemma preord_env_P_def_funs k B rho rho' B' S1 :
    preord_env_P PG (fun x => (~ name_in_fundefs B' x /\ S1 x) \/
                        occurs_free_fundefs B' x) k rho rho' ->
    preord_env_P PG (fun x => (~ name_in_fundefs B' x /\ S1 x) \/
                           occurs_free_fundefs B' x \/ name_in_fundefs B x)
                 k (def_funs B' B rho rho) (def_funs B' B rho' rho').
  Proof.
    intros Hpre.
    revert B rho rho' B' Hpre.
    induction k as [ k IH' ] using lt_wf_rec1. intros B rho rho' B' Hpre.
    induction B.
    - simpl. apply preord_env_P_extend.
      + intros x H. inv H. eapply IHB; eauto.
        inv H0; eauto. inv H; eauto. inv H0; try contradiction; eauto.
      + rewrite preord_val_eq.
        intros vs1 vs2 j t1 xs1 e1 rho1' Hlen Hf' Hs.
        edestruct (@set_lists_length val) as [rho2' Hs']; eauto.
        exists xs1. exists e1. exists rho2'. split; eauto.
        split. eauto. intros Hleq Hpre'.
        eapply preord_exp_refl; eauto.
        eapply preord_env_P_set_lists_l; [| | eauto | eauto | eauto].
        apply IH'; eauto.
        eapply (preord_env_P_monotonic PG _ k); eauto. lia.
        intros x Hin Hfr.
        apply find_def_correct in Hf'.
        edestruct (occurs_free_in_fun _ _ _ _ _ Hf' x Hfr);
          eauto; try contradiction.
        inv H; eauto.
    - simpl. intros x HP. inv HP. apply Hpre; eauto. inv H.
      apply Hpre; eauto. inv H0.
  Qed.

  Corollary preord_env_P_def_funs_cor k B rho rho' S1 :
    preord_env_P PG (Union var (Setminus var S1 (name_in_fundefs B))
                        (occurs_free_fundefs B)) k rho rho' ->
    preord_env_P PG S1 k (def_funs B B rho rho) (def_funs B B rho' rho').
  Proof.
    intros Hpre. eapply preord_env_P_antimon.
    - eapply preord_env_P_def_funs; eauto.
      eapply preord_env_P_antimon; eauto.
      intros x HS. inv HS. inv H. left. constructor; eauto.
      right; eauto.
    - intros x HS.
      destruct (@Dec _ _ (Decidable_name_in_fundefs B) x); eauto.
  Qed.

  Lemma preord_exp_refl_weak (k : nat) e rho rho' :
      preord_env PG k rho rho' ->
      preord_exp PG PG k (e, rho) (e, rho').
  Proof.
    intros Henv. eapply preord_exp_refl; try eauto.
    eapply preord_env_P_antimon; eauto.
    intros x H; simpl; eauto.
  Qed.

  Lemma preord_val_refl (k : nat) :
    Reflexive (preord_val PG k).
  Proof.
    induction k using lt_wf_rec1.
    destruct k as [| k]; unfold Reflexive; intros x; rewrite preord_val_eq;
    induction x using val_ind'; simpl; eauto;
    try (now (try split; eauto); econstructor; eauto; rewrite preord_val_eq; eauto).
    - split; eauto. constructor; eauto. rewrite preord_val_eq; eauto.
      destruct IHx0. eauto.
    - intros.
      edestruct (set_lists_length (def_funs f0 f0 t t) (def_funs f0 f0 t t))
        as [rho2' Hset']; eauto.
      do 3 eexists; split; eauto. split; eauto. intros Hc.
      exfalso. lia.
    - split; eauto. constructor; eauto. rewrite preord_val_eq; eauto.
        destruct IHx0. eauto.
    - intros.
      edestruct (set_lists_length (def_funs f0 f0 t t) (def_funs f0 f0 t t))
        as [rho2' Hset']; eauto.
      do 3 eexists; eauto. split; eauto.
      split; eauto.
      intros Hleq Hall v1 c Hleq' Hstep.
      eapply preord_exp_refl_weak; eauto.
      eapply preord_env_set_lists_l; eauto.
      eapply preord_env_refl; eauto.
  Qed.

  Lemma preord_env_P_refl S k rho :
    preord_env_P PG S k rho rho.
  Proof.
    intros x Px v Hget.
    eexists; split; eauto. eapply preord_val_refl; eauto.
  Qed.

  Lemma preord_res_refl k r :
    preord_res preord_val PG k r r.
  Proof.
    destruct r; simpl; eauto.
   eapply preord_val_refl.
  Qed.

  Lemma eq_env_P_preord_env_P  S r1 r2 :
    eq_env_P S r1 r2 ->
    (forall q, preord_env_P PG S q r1 r2).
  Proof.
    intros Heq q x Hin v Hget. rewrite <- Heq; eauto.
    eexists; split; eauto.
    apply preord_val_refl; eauto.
  Qed.


  Lemma preord_env_def_funs k f rho1 rho2 :
    preord_env PG k rho1 rho2 ->
    preord_env PG k (def_funs f f rho1 rho1) (def_funs f f rho2 rho2).
  Proof.
    intros Henv. eapply preord_env_P_def_funs_cor.
    eapply preord_env_P_antimon; eauto. intros x H; simpl; eauto.
  Qed.

  Lemma preord_exp_case_compat k rho1 rho2 x c e1 e2 D1' D1 :
    preord_env_P PG (occurs_free (Ecase x (D1' ++ ((c, e1) :: D1)))) k rho1 rho2 ->
    (forall m, m < k -> preord_exp P1 PG m (e1, rho1) (e2, rho2)) ->
    preord_exp P1 PG k (Ecase x (D1' ++ ((c, e1) :: D1)), rho1)
               (Ecase x (D1' ++ ((c, e2) :: D1)), rho2).
  Proof.
    (* TODO : this lemma could be used to refactor hoisting correctness proof *)
    assert (Hpr := Hprops). inv Hprops.
    induction D1' as [| [c' e'] P1' IHP1']; intros Henv Hexp.
    - simpl (Ecase _ _). eapply preord_exp_case_cons_compat; eauto.
      eapply Forall2_refl. clear; now firstorder.
      eapply preord_exp_refl; eauto.
      simpl in Henv. eapply preord_env_P_antimon. eassumption.
      normalize_occurs_free. now sets.
    - simpl (Ecase _ _).  eapply preord_exp_case_cons_compat; eauto.
      + eapply Forall2_app.
        eapply Forall2_refl. clear; now firstorder.
        constructor. reflexivity.
        eapply Forall2_refl. clear; now firstorder.
      + intros m Hlt. eapply preord_exp_refl; eauto.
        eapply preord_env_P_antimon. eapply preord_env_P_monotonic; [| eassumption ].
        lia. repeat normalize_occurs_free. now sets.
      + eapply IHP1'; [| eassumption ].
        eapply preord_env_P_antimon. eassumption.
        repeat normalize_occurs_free. now sets.
  Qed.

  (** * Compatibility with context application *)

  Lemma preord_env_P_def_funs_compat_pre k B rho1 rho2 B' e1 e2 S1 :
    (forall m c (rho1 rho2 : env),
       m <  k ->
       preord_env_P PG (occurs_free (c |[ e1 ]|)) m rho1 rho2 ->
       preord_exp P1 PG m (c |[ e1 ]|, rho1) (c |[ e2 ]|, rho2)) ->
    preord_env_P PG (Union _ (occurs_free_fundefs (B' <[ e1 ]>))
                        (Setminus _ S1 (name_in_fundefs (B' <[ e1 ]>))))
                 k rho1 rho2 ->
    preord_env_P PG (Union _ (Setminus _ S1 (name_in_fundefs (B' <[ e1 ]>)))
                        (Union _ (occurs_free_fundefs (B' <[ e1 ]>))
                               (name_in_fundefs (B <[ e1 ]>))))
                 k (def_funs (B' <[ e1 ]>) (B <[ e1 ]>) rho1 rho1)
                 (def_funs (B' <[ e2 ]>) (B <[ e2 ]>) rho2 rho2).
  Proof.
    revert B rho1 rho2 B' e1 e2 S1.
    induction k as [ k IH' ] using lt_wf_rec1.
    intros B rho1 rho2 B' e1 e2 S1 Hpre Henv.
    assert (Hval : forall f, preord_val PG k (Vfun rho1 (B' <[ e1 ]>) f)
                                   (Vfun rho2 (B' <[ e2 ]>) f)).
    { intros f. rewrite preord_val_eq.
      intros vs1 vs2 j t1 xs1 e' rho1' Hlen Hf' Hs.
      edestruct find_def_def_funs_ctx as [H1 | [c [H1 H2]]]; eauto.
      + edestruct (@set_lists_length val) as [rho2' Hs']; eauto.
        do 4 eexists; eauto. split; eauto.
        intros Hleq Hall.
        eapply preord_exp_refl; try now eauto.
        eapply preord_env_P_set_lists_l; [| | now eauto | now eauto | now eauto ].
        eapply IH'; eauto.
        intros. eapply Hpre; eauto. lia.
        eapply preord_env_P_monotonic; [| eassumption ]. lia.
        intros x H Hfv.
        eapply find_def_correct in Hf'; eauto.
        eapply occurs_free_in_fun in Hfv; eauto.
        inv Hfv. exfalso. eauto. right. eapply Union_commut. eauto.
      + subst. edestruct (@set_lists_length val) as [rho2' Hs']; eauto.
        do 4 eexists; eauto. split; eauto.
        intros Hleq Hall.
        eapply preord_exp_post_monotonic; [| eapply Hpre ].
        inv Hprops. eassumption.
        lia.
        eapply preord_env_P_set_lists_l; [| | eauto | eauto | eauto ].
        eapply IH'; eauto.
        intros. eapply Hpre; eauto. lia.
        eapply preord_env_P_monotonic; [| eassumption ]. lia.
        intros x H Hfv.
        eapply find_def_correct in Hf'; eauto.
        eapply occurs_free_in_fun in Hfv; eauto.
        inv Hfv. exfalso. eauto. right. eapply Union_commut. eauto. }
    induction B.
    - simpl. apply preord_env_P_extend.
      + induction f.
        { simpl. apply preord_env_P_extend.
          - eapply preord_env_P_antimon; [ eassumption |].
            rewrite !Setminus_Union_distr. eapply Union_Included.
            now eauto with Ensembles_DB.
            eapply Union_Included.
            now eauto with Ensembles_DB.
            eapply Union_Included.
            now eauto with Ensembles_DB.
            rewrite Setminus_Union. rewrite (Union_commut [set v] [set v0]).
            rewrite <- Setminus_Union.
            rewrite Setminus_Same_set_Empty_set.
            now eauto with Ensembles_DB.
          - eapply Hval. }
        { simpl. eapply preord_env_P_antimon ; [ eassumption |].
          eauto with Ensembles_DB. }
      + eapply Hval.
    - simpl. apply preord_env_P_extend.
      + eapply preord_env_P_antimon; [now eauto |].
        eauto 10 with Ensembles_DB.
      + apply Hval.
  Qed.

  Lemma preord_exp_compat k rho1 rho2 c e1 e2 :
    (* Annoying, but we need that for the cost of fundefs *)
    (* PS.cardinal (exp_fv (c |[ e1 ]|)) = PS.cardinal (exp_fv (c |[ e2 ]|)) -> *)
    (forall m rho1 rho2,
        m <= k ->
        preord_env_P PG (occurs_free e1) m rho1 rho2 ->
        preord_exp P1 PG m (e1, rho1) (e2, rho2)) ->
    preord_env_P PG (occurs_free (c |[ e1 ]|)) k rho1 rho2 ->
    preord_exp P1 PG k (c |[ e1 ]|, rho1) (c |[ e2 ]|, rho2).
  Proof.
    unfold exp_fv. assert (Hp := Hprops). inv Hp.
    revert c rho1 rho2 e1 e2. induction k as [ k IH' ] using lt_wf_rec1.
    intros c. revert k IH'.
    induction c; intros k IH' rho1 rho2 e1 e2 Hyp Hpre; eauto.
    - simpl. eapply preord_exp_constr_compat; eauto.
      + eapply Forall2_same. intros x Hin. eapply Hpre. constructor; eauto.
      + intros m vs1 vs2 Hlt Hall. eapply IHc; eauto.

        * intros. eapply IH'; eauto. lia.
        * intros. eapply Hyp; eauto. lia.
        * eapply preord_env_P_extend.

          eapply preord_env_P_antimon; eauto. eapply preord_env_P_monotonic; [| eassumption ]. lia.
          simpl. normalize_occurs_free.  sets.

          rewrite preord_val_eq. simpl; split; eauto.

    - simpl. eapply preord_exp_proj_compat; eauto.
      + eapply Hpre. constructor; eauto.
      + intros m v1 v2 Hlt Hval. eapply IHc; eauto.
        * intros. eapply IH'; eauto. lia.
        * intros. eapply Hyp; eauto. lia.
        * eapply preord_env_P_extend; [| assumption ].
          eapply preord_env_P_antimon; eauto.
          eapply preord_env_P_monotonic; [| eassumption ]. lia.
          simpl. normalize_occurs_free. sets.
    - simpl. eapply preord_exp_prim_val_compat; eauto.
    - simpl. eapply preord_exp_prim_compat; eauto.
      + eapply Forall2_same. intros x Hin. eapply Hpre. constructor; eauto.
    - simpl. eapply preord_exp_letapp_compat; eauto.
      + eapply Hpre. constructor. now left.
      + eapply Forall2_same. intros x Hin. eapply Hpre. constructor; eauto.
        now right.
      + intros m vs1 vs2 Hlt Hall.
        eapply IHc; eauto. intros.
        * eapply IH'. lia. eassumption. eassumption.
        * intros; eapply Hyp; eauto; lia.
        * eapply preord_env_P_extend; [| assumption ].
          eapply preord_env_P_antimon.
          eapply preord_env_P_monotonic; [| eassumption ]. lia.
          simpl. normalize_occurs_free. now eauto with Ensembles_DB.
    - simpl. eapply preord_exp_case_compat; eauto. intros i Hlt.
      eapply IHc; auto. intros. eapply IH'; eauto. lia.
      intros. eapply Hyp; eauto. lia.
      eapply preord_env_P_antimon; eauto.
      eapply preord_env_P_monotonic; [| eassumption ]. lia.
      eapply occurs_free_Ecase_Included; eauto.
      eapply in_or_app. right. left; eauto.
    - simpl. eapply preord_exp_fun_compat; eauto.
      eapply IHc; auto. intros. eapply IH'; eauto. lia.
      intros. eapply Hyp; eauto. lia.
      eapply preord_env_P_def_funs_cor.
      eapply preord_env_P_antimon.
      eapply preord_env_P_monotonic; [| eassumption ]. lia.
      intros x' H'. inv H'.
      + inv H. simpl. constructor; eauto.
      + simpl. eapply Free_Efun2; eauto.
    - simpl app_ctx_f.
      eapply preord_exp_fun_compat; [| now eauto |]. now eauto.
       eapply preord_exp_refl; eauto.
       eapply preord_env_P_antimon.
       eapply preord_env_P_def_funs_compat_pre.
      * intros. eapply IH'. lia.
        intros. eapply Hyp; eauto. lia.
        eassumption.
      * eapply preord_env_P_antimon.
        eapply preord_env_P_monotonic; [| eassumption ]. lia.
        simpl. rewrite occurs_free_Efun. reflexivity.
      * rewrite <- Union_Included_Union_Setminus. now sets. tci. sets.
  Qed.

  End Rel.

  Definition comp (P1 P2 : PostT) : PostT := fun c1 c2 => exists c3, P1 c1 c3 /\ P2 c3 c2.
  Definition compG (P1 P2 : PostGT) : PostGT := fun c1 c2 => exists c3, P1 c1 c3 /\ P2 c3 c2.

  Section Divergence.

    Definition post_upper_bound (P : PostT) :=
      forall e1 rho1 e2 rho2,
      exists (f : fuel -> fuel),
      forall cin1 cin2 cout1 cout2,
        P (e1, rho1, f cin1, cout1) (e2, rho2, cin2, cout2) ->
        exists (c : fuel), cin2 = (c <+> cin1).


    Lemma preord_exp_preserves_divergence P PG e1 rho1 e2 rho2
          (Hrel : post_upper_bound P) :
      (forall k, preord_exp P PG k (e1, rho1) (e2, rho2)) ->
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

    Lemma preord_exp_preserves_not_stuck P PG e1 rho1 e2 rho2
          (Hrel : post_upper_bound P) :
      (forall k, preord_exp P PG k (e1, rho1) (e2, rho2)) ->
      @not_stuck cenv fuel _ trace _ rho1 e1 ->
      @not_stuck cenv fuel _ trace _ rho2 e2.
    Proof.
      intros Hexp Hns. assert (Hns' := Hns). inv Hns.
      - destructAll.
        edestruct Hexp as [v2 [c2' [cout' [Hs2 [Hp Hval]]]]].
        reflexivity. eassumption.

        destruct v2; try contradiction.
        left. now eauto.
      - right. eapply preord_exp_preserves_divergence; eassumption.
    Qed.

  End Divergence.



  Section Trans.

    Context (PG  : PostGT) (* Global *)
            (HpropG: Post_properties PG PG PG)
            (HGPost : inclusion _ (comp PG PG) PG).

  (** * Transitivity Properties *)

  (** Expression relation is transitive *)
    Lemma preord_res_trans_pre (k : nat) :
      (forall k' v1 v2 v3,
          k' <= k ->
          preord_val PG k' v1 v2 ->
          (forall m, preord_val PG m v2 v3) ->
          preord_val PG k' v1 v3) ->
      forall r1 r2 r3,
        preord_res preord_val PG k r1 r2 ->
        (forall m, preord_res preord_val PG m r2 r3) ->
        preord_res preord_val PG k r1 r3.
    Proof.
      intros Hyp r1 r2 r3 H1 H2.
      destruct r1; destruct r2; destruct r3; try contradiction; eauto.
      specialize (H2 0); contradiction.
      eapply Hyp; eauto.
    Qed.

    (** Expression relation is transitive *)
    Lemma preord_exp_trans_pre P1 P2 (k : nat) :
      (* The induction hypothesis for transitivity of
       the value relation. *)
      (forall k' v1 v2 v3,
          k' <= k ->
          preord_val PG k' v1 v2 ->
          (forall m, preord_val PG m v2 v3) ->
          preord_val PG k' v1 v3) ->
      forall rho1 rho2 rho3 e1 e2 e3,
        preord_exp P1 PG k (e1, rho1) (e2, rho2) ->
        (forall m, preord_exp P2 PG m (e2, rho2) (e3, rho3)) ->
        preord_exp (comp P1 P2) PG k (e1, rho1) (e3, rho3).
    Proof.
      intros Htrans rho1 rho2 rho3 e1 e2 e3 H1 H2 v1 c1 cout1 Hleq1 Hstep1.
      edestruct H1 as [v2 [c2 [cout2 [Hstep2 [Hpost2 Hpre2]]]]]; eauto.
      edestruct (H2 (to_nat c2)) as [v3 [c3 [cout3 [Hstep3 [Hpost3 Hpre3]]]]]; [| eauto |]. lia.
      exists v3, c3, cout3. split; eauto.
      split.

      eexists. split. eassumption. eassumption.
      eapply preord_res_trans_pre; eauto.
      {intros. eapply Htrans; eauto. lia. }
      intros m.
      edestruct (H2 (m + to_nat c2)) as [v3' [c3' [cout3' [Hstep3' [Hpost3' Hpre3']]]]]; [| eauto |]. lia.
      destruct v1; destruct v2; destruct v3; destruct v3'; try contradiction; eauto.
      eapply bstep_fuel_deterministic in Hstep3; [| eapply Hstep3' ]. inv Hstep3.
      eapply preord_val_monotonic; eauto. lia.
    Qed.

    Lemma preord_val_trans (k : nat) v1 v2 v3 :
      preord_val PG k v1 v2 ->
      (forall m, preord_val PG m v2 v3) ->
      preord_val PG k v1 v3.
    Proof.
      revert v1 v2 v3.
      induction k using lt_wf_rec1.
      intros x; induction x using val_ind'; simpl; eauto.
      - intros v1 v2 H1 H2; specialize (H2 k); rewrite !preord_val_eq in *.
        destruct v1; destruct v2;
          try (now simpl in *; contradiction); inv H1; inv H2; simpl; eauto.
        inv H3; inv H1. eauto.
      - intros v1 v2 H1 H2. assert (H2' := H2 k); rewrite !preord_val_eq in *.
        destruct v1; destruct v2; try (now simpl in *; contradiction).
        destruct H1 as [H1 H1']. destruct H2' as [H3 H3']. subst.
        destruct l0; try inv H1'; try inv H3'. split; eauto.
        econstructor; eauto.
        + eapply IHx. eassumption.
          intros m. specialize (H2 m). rewrite !preord_val_eq in H2.
          inv H2. now inv H1.
        + assert
            (Hsuf :
               preord_val PG k (Vconstr c0 l) (Vconstr c0 l')).
          { eapply IHx0 with (v2 := Vconstr c0 l0); [| intros m];
              rewrite !preord_val_eq in *. simpl. split; eauto.
            specialize (H2 m). rewrite !preord_val_eq in H2.
            split; eauto. inv H2. now inv H1. }
          rewrite !preord_val_eq in Hsuf. now inv Hsuf.
      - intros v1 v2 H1 H2. assert (H2' := H2 k); rewrite !preord_val_eq in *.
        destruct v1; destruct v2; try (now simpl in *; contradiction).
        intros vs1 vs3 j t1' xs1 e1 rho1' Hlen Hf' Hs.
        edestruct (H1 vs1 vs3) as [xs2 [e2 [rho2 [Hf2 [Hs2 Hpre2]]]]]; eauto.
        edestruct (H2' vs3 vs3) with (j := 0) as [xs3 [e3 [rho3 [Hf3 [Hs3 Hpre3]]]]]; eauto.
        do 3 eexists; split; eauto. split; eauto. intros Hlt Hall.
        eapply preord_exp_post_monotonic; [| eapply preord_exp_trans_pre ].
        eassumption.

        intros. eapply H; eauto. lia.

        eapply Hpre2; eauto.

        intros m.
        specialize (H2 (m + 1)). rewrite !preord_val_eq in H2.
        edestruct (H2 vs3 vs3) with (j := m)
          as [xs3' [e3' [rho3' [Hf3' [Hs3' Hpre3']]]]]; eauto.
        rewrite Hf3 in Hf3'. inv Hf3'. rewrite <- Hs3 in Hs3'. inv Hs3'.
        eapply Hpre3'. lia.
        eapply Forall2_refl. eapply preord_val_refl; eauto.
      - intros v1 v2 H1 H2; specialize (H2 k); rewrite !preord_val_eq in *.
        destruct v1; destruct v2;
          try (now simpl in *; contradiction); inv H1; inv H2; simpl; eauto.
      - intros v1 v2 H1 H2; specialize (H2 k); rewrite !preord_val_eq in *.
        destruct v1; destruct v2;
          try (now simpl in *; contradiction); inv H1; inv H2; simpl; eauto.
    Qed.



  Lemma preord_env_P_trans (k : nat) P rho1 rho2 rho3 :
    preord_env_P PG P k rho1 rho2 ->
    (forall m,  preord_env_P PG P m rho2 rho3) ->
    preord_env_P PG P k rho1 rho3.
  Proof.
    intros H1 H2 x Px v Hget. assert (H2' := (H2 k)).
    edestruct H1 as [v' [Hget' Hpre']]; eauto.
    edestruct H2' as [v'' [Hget'' Hpre'']]; eauto.
    eexists; split; eauto. eapply preord_val_trans; eauto.
    intros m.
    edestruct (H2 m) as [v''' [Hget''' Hpre''']]; eauto.
    rewrite Hget'' in Hget'''. now inv Hget'''.
  Qed.


  Corollary preord_exp_trans (k : nat) :
    forall P1 P2 rho1 rho2 rho3 e1 e2 e3,
      preord_exp P1 PG k (e1, rho1) (e2, rho2) ->
      (forall m, preord_exp P2 PG m (e2, rho2) (e3, rho3)) ->
      preord_exp (comp P1 P2) PG k (e1, rho1) (e3, rho3).
  Proof.
    intros. eapply preord_exp_trans_pre; eauto.
    intros. eapply preord_val_trans; eauto.
  Qed.

  Context (P1 : PostT) (Hprops : Post_properties P1 P1 PG).

  Lemma preord_env_P_def_funs_pre' k (S1 : var -> Prop) B B' rho1 rho2 :
    preord_env_P PG (S1 \\ name_in_fundefs B) k rho1 rho2 ->

    name_in_fundefs B \subset name_in_fundefs B' ->
    occurs_free_fundefs B' \subset S1 ->
    Disjoint _ (occurs_free_fundefs B') (name_in_fundefs B) ->

    (forall m (* S1  *)(rho rho' : env) (e : exp),
        m <  k ->
        preord_env_P PG (occurs_free e) m rho rho' ->
        preord_exp P1 PG m (e, rho) (e, rho')) ->

    preord_env_P PG S1 k (def_funs B' B rho1 rho1) (def_funs B' B rho2 rho2).
  Proof.
    revert B B' S1 rho1 rho2.
    induction k as [ k IH' ] using lt_wf_rec1. intros B.
    induction B; intros B' S1 rho rho2 Henv Hname Hfv Hdis Hyp1.
    - simpl. eapply preord_env_P_extend.
      + eapply IHB; eauto. eapply preord_env_P_antimon. eassumption. simpl. sets.
        eapply Included_trans; [| eassumption ]. now sets.
        eapply Included_Setminus; now sets. now sets.
      + rewrite preord_val_eq.
        intros vs1 vs2 j t1 xs1 e1 rho1' Hlen Hf' Hs.
        edestruct (@set_lists_length val) as [rho2' Hs']; eauto.
        exists xs1. exists e1. exists rho2'. split; eauto.
        split. eauto. intros Hleq Hpre.

        eapply preord_exp_post_monotonic; [| eapply Hyp1 ].
        inv Hprops. eassumption.
        eassumption.
        eapply preord_env_P_set_lists_l with (P1 := occurs_free e1 \\ FromList xs1); try eassumption; try now eauto.
        eapply preord_env_P_antimon with (P2 := occurs_free_fundefs B' :|: name_in_fundefs B').
        eapply IH'. eassumption. rewrite Setminus_Union_distr. rewrite Setminus_Same_set_Empty_set, Union_Empty_set_neut_r.
        eapply preord_env_P_antimon. eapply preord_env_P_monotonic; [| eassumption ]. lia. simpl.

        eapply Included_Setminus. now sets. eapply Included_trans; [| eassumption ]. sets. reflexivity.
        now sets. eapply Disjoint_sym. eapply occurs_free_fundefs_name_in_fundefs_Disjoint.

        intros. eapply Hyp1. lia. eassumption.

        eapply Setminus_Included_Included_Union. eapply Included_trans. eapply occurs_free_in_fun.
        eapply find_def_correct. eassumption. now sets.
    - simpl. eapply preord_env_P_antimon. eassumption. sets.
  Qed.

  Lemma preord_env_P_def_funs_alt k (S1 : var -> Prop) B rho1 rho2 :
    preord_env_P PG (S1 \\ name_in_fundefs B) k rho1 rho2 ->
    occurs_free_fundefs B \subset S1 ->
    Disjoint _ (occurs_free_fundefs B) (name_in_fundefs B) ->
    preord_env_P PG S1 k (def_funs B B rho1 rho1) (def_funs B B rho2 rho2).
  Proof.
    intros H HS HD. eapply preord_env_P_def_funs_pre'. eassumption. reflexivity. eassumption. eassumption.
    intros. eapply preord_exp_refl; eauto.
  Qed.

  (** Commutativity property *)
  Lemma preord_exp_preord_env_com rho1 rho2 rho1' rho2' e1 e2 :
    (forall k, preord_exp P1 PG k (e1, rho1) (e2, rho2)) ->
    (forall k, preord_env_P PG (occurs_free e1) k rho1' rho1) ->
    (forall k, preord_env_P PG (occurs_free e2) k rho2 rho2') ->
    (forall k, preord_exp P1 PG k (e1, rho1') (e2, rho2')).
  Proof.
    intros Hexp1 Henv1 Henv2 k.
  Abort.
  (* Should be provable but we need to find the right preconditions for the post *)

  (*   eapply preord_exp_trans. *)
  (*   - now eapply preord_exp_refl. *)
  (*   - intros m. eapply preord_exp_trans; [ now eauto | ]. *)
  (*     intros m'. now eapply preord_exp_refl. *)
  (* Qed. *)

  Lemma preord_env_permut k x y v1 v2 rho1 rho2 P :
    x <> y ->
    preord_env_P PG P k (M.set x v1 (M.set y v2 rho1)) (M.set x v1 (M.set y v2 rho2)) ->
    preord_env_P PG P k (M.set x v1 (M.set y v2 rho1)) (M.set y v2 (M.set x v1 rho2)).
  Proof.
    intros Hneq Hpre x' HP v1' Hget.
    rewrite M.gsspec in Hget.
    destruct (peq x' x). inv Hget.
    - edestruct (Hpre x) as [v1'' [Hget'' Hpre'']]; eauto. rewrite M.gss; eauto.
      rewrite M.gss in Hget''; inv Hget''.
      eexists. rewrite M.gso; eauto. rewrite M.gss; eauto.
    - edestruct (Hpre x') as [v1'' [Hget'' Hpre'']]; eauto.
      rewrite M.gso; eauto. rewrite M.gsspec in Hget.
      destruct (peq x' y). inv Hget.
      + eexists. rewrite M.gss; eauto. split; eauto.
        eapply preord_val_refl; try eauto.
      + do 2 (rewrite M.gso in Hget''; eauto).
        eexists. split; eauto.
        do 2 (rewrite M.gso; eauto).
  Qed.

  (** Left weakening *)
  Lemma preord_env_P_set_not_in_P_l x v P k rho1 rho2 :
    preord_env_P PG P k rho1 rho2 ->
    Disjoint var P (Singleton var x) ->
    preord_env_P PG P k (M.set x v rho1) rho2.
  Proof.
    intros Hpre HP x' HP' v' Hget.
    rewrite M.gsspec in Hget. destruct (peq x' x).
    - inv Hget. exfalso. inv HP. eapply H; eauto.
    - edestruct Hpre; eauto.
  Qed.

  (** Right weakening *)
  Lemma preord_env_P_set_not_in_P_r x v P k rho1 rho2 :
    preord_env_P PG P k rho1 rho2 ->
    Disjoint var P (Singleton var x) ->
    preord_env_P PG P k rho1 (M.set x v rho2).
  Proof.
    intros Hpre HP x' HP' v' Hget.
    rewrite M.gsspec. destruct (peq x' x); subst.
    - exfalso; eauto. inv HP. eapply H; eauto.
    - edestruct Hpre; eauto.
  Qed.

  (** Left weakening for function definitions *)
  Lemma preord_env_P_def_funs_not_in_P_l B B' P k rho rho1 rho2 :
    preord_env_P PG P k rho1 rho2 ->
    Disjoint var P (name_in_fundefs B) ->
    preord_env_P PG P k (def_funs B' B rho rho1) rho2.
  Proof.
    intros Hpre HP x' HP' v' Hget.
    eapply def_funs_spec in Hget.
    destruct Hget as [[Hname Heq] | [Hname Heq ]]; subst.
    - exfalso. eapply HP; eauto.
    - edestruct Hpre; eauto.
  Qed.

  (** Right weakening for function definitions *)
  Lemma preord_env_P_def_funs_not_in_P_r B B' P k rho rho1 rho2 :
    preord_env_P PG P k rho1 rho2 ->
    Disjoint var P (name_in_fundefs B) ->
    preord_env_P PG P k rho1 (def_funs B' B rho rho2).
  Proof.
    intros Hpre HP x' HP' v' Hget.
    edestruct (@Dec _ _ (Decidable_name_in_fundefs B) x').
    - exfalso. eapply HP; eauto.
    - edestruct Hpre as [v'' [Hget' Hpre']]; eauto.
      eexists. rewrite def_funs_neq; eauto.
  Qed.

  (** Left weakening for set_lists *)
  Lemma preord_env_P_set_lists_not_in_P_r xs vs P k rho1 rho2 rho2' :
    preord_env_P PG P k rho1 rho2 ->
    Some rho2' = set_lists xs vs rho2 ->
    Disjoint var P (FromList xs) ->
    preord_env_P PG P k rho1 rho2'.
  Proof.
    revert vs rho2'. induction xs; intros vs rho2' Hpre Hset HD.
    - destruct vs; try discriminate. inv Hset; eauto.
    - destruct vs; try discriminate. simpl in Hset.
      destruct (set_lists xs vs rho2) eqn:Heq ; try discriminate. inv Hset.
      rewrite FromList_cons in HD.
      apply preord_env_P_set_not_in_P_r; [| now eauto with Ensembles_DB ].
      eapply IHxs; eauto with Ensembles_DB.
  Qed.

  (** Right weakening for set_lists *)
  Lemma preord_env_P_set_lists_not_in_P_l xs vs P k rho1 rho2 rho1' :
    preord_env_P PG P k rho1 rho2 ->
    Some rho1' = set_lists xs vs rho1 ->
    Disjoint var P (FromList xs) ->
    preord_env_P PG P k rho1' rho2.
  Proof.
    revert vs rho1'. induction xs; intros vs rho1' Hpre Hset HD.
    - destruct vs; try discriminate. inv Hset; eauto.
    - destruct vs; try discriminate. simpl in Hset.
      destruct (set_lists xs vs rho1) eqn:Heq ; try discriminate. inv Hset.
      rewrite FromList_cons in HD.
      apply preord_env_P_set_not_in_P_l; [| now eauto with Ensembles_DB ].
      eapply IHxs; eauto with Ensembles_DB.
  Qed.

  Lemma preord_env_P_singleton_extend (rho1 rho2 : env) (k : nat) (x : var)
        (v1 v2 : val) :
    preord_val PG k v1 v2 ->
    preord_env_P PG (Singleton var x) k (M.set x v1 rho1) (M.set x v2 rho2).
  Proof.
    intros Hpre. eapply preord_env_P_extend; eauto.
    eapply preord_env_P_antimon. apply preord_env_Empty_set.
    eauto with Ensembles_DB.
  Qed.

  (** * Technical lemmas about mutually recursive function definitions *)

  Lemma preord_env_set_def_funs_permut k x S1 B v1 v2 rho1 rho2 :
    ~ bound_var_fundefs B x ->
    closed_fundefs B ->
    preord_val PG k v1 v2 ->
    preord_env_P PG S1 k rho1 rho2 ->
    preord_env_P PG (Union var S1 (Union var (Singleton var x) (name_in_fundefs B))) k
                 (def_funs B B (M.set x v1 rho1) (M.set x v1 rho1))
                 (M.set x v2 (def_funs B B rho2 rho2)).
  Proof.
    intros Hb Hclo Hval Hpre. rewrite (@Union_Setminus _ _ _ _).
    apply preord_env_P_union.
    - apply preord_env_P_def_funs_not_in_P_l; [| now eauto with Ensembles_DB ].
      apply preord_env_P_set_not_in_P_l; [| now eauto with Ensembles_DB ].
      apply preord_env_P_set_not_in_P_r; [| now eauto with Ensembles_DB ].
      apply preord_env_P_def_funs_not_in_P_r; [| now eauto with Ensembles_DB ].
      eapply preord_env_P_antimon; now eauto with Ensembles_DB.
    - apply preord_env_P_union.
      + apply preord_env_P_def_funs_not_in_P_l.
        eapply preord_env_P_singleton_extend; eauto.
        apply Disjoint_Singleton_l. intros Hc; apply Hb.
        now apply name_in_fundefs_bound_var_fundefs.
      + apply preord_env_P_set_not_in_P_r.
        eapply preord_env_P_def_funs_cor; eauto.
        eapply preord_env_P_antimon. apply preord_env_Empty_set.
        eauto with Ensembles_DB.
        unfold closed_fundefs in Hclo. rewrite <- Hclo; eauto with Ensembles_DB.
        apply Disjoint_Singleton_r. intros Hc; apply Hb.
        now apply name_in_fundefs_bound_var_fundefs.
  Qed.

  Lemma preord_env_def_funs_permut (k : nat) S1 (B1 B2 : fundefs) (rho1 rho2 : env) :
    closed_fundefs B1 -> closed_fundefs B2 ->
    Disjoint var (name_in_fundefs B1) (name_in_fundefs B2) ->
    preord_env_P PG S1 k rho1 rho2 ->
    preord_env_P PG (Union var S1 (Union var (name_in_fundefs B1) (name_in_fundefs B2)))
                 k (def_funs B1 B1 (def_funs B2 B2 rho1 rho1) (def_funs B2 B2 rho1 rho1))
                 (def_funs B2 B2 (def_funs B1 B1 rho2 rho2) (def_funs B1 B1 rho2 rho2)).
  Proof.
    intros Hclo1 Hclo2 HD Hpre. rewrite (@Union_Setminus _ _ _ _).
    apply preord_env_P_union.
    - eapply preord_env_P_def_funs_not_in_P_r; [| now eauto with Ensembles_DB ].
      eapply preord_env_P_def_funs_not_in_P_l; [| now eauto with Ensembles_DB ].
      eapply preord_env_P_def_funs_not_in_P_r; [| now eauto with Ensembles_DB ].
      eapply preord_env_P_def_funs_not_in_P_l; [| now eauto with Ensembles_DB ].
      eapply preord_env_P_antimon; now eauto with Ensembles_DB.
    - apply preord_env_P_union.
      + apply preord_env_P_def_funs_not_in_P_r; eauto.
        eapply preord_env_P_def_funs_cor; eauto.
        eapply preord_env_P_antimon. apply preord_env_Empty_set.
        unfold closed_fundefs in Hclo1. rewrite <- Hclo1; eauto with Ensembles_DB.
      + apply preord_env_P_def_funs_not_in_P_l; eauto using Disjoint_sym.
        eapply preord_env_P_def_funs_cor; eauto.
        eapply preord_env_P_antimon. apply preord_env_Empty_set.
        unfold closed_fundefs in Hclo2. rewrite <- Hclo2; eauto with Ensembles_DB.
  Qed.

  Lemma preord_env_P_def_funs_strengthen_l (k : nat) rho rho' B1 B1' B2 :
    Disjoint var (occurs_free_fundefs B1') (name_in_fundefs B2) ->
    Disjoint var (name_in_fundefs B1') (name_in_fundefs B2) ->
    closed_fundefs B1' ->
    preord_env_P PG (name_in_fundefs B1) k
                 (def_funs B1' B1 rho rho')
                 (def_funs (fundefs_append B2 B1') B1 rho rho').
  Proof.
    revert rho rho' B1 B1' B2.
    induction k as [ k IH' ] using lt_wf_rec1. intros rho rho' B1 B1' B2 HD1 HD2 Hclo.
    induction B1.
    - simpl. apply preord_env_P_extend.
      + eapply preord_env_P_antimon. eapply IHB1; eauto.
        eauto with Ensembles_DB typeclass_instances.
      + rewrite preord_val_eq.
        intros vs1 vs2 j t1 xs1 e1 rho1' Hlen Hf' Hs.
        edestruct (@set_lists_length val) as [rho2' Hs']; eauto.
        exists xs1. exists e1. exists rho2'. split; eauto.
        specialize (find_def_name_in_fundefs _ _ _ Hf'); intros Hname.
        destruct (@Dec _ _  (Decidable_name_in_fundefs B2) v) as [Hin | Hnin ].
        exfalso. inv HD2. eapply H; eauto.
        eapply name_not_in_fundefs_find_def_None in Hnin.
        erewrite find_def_fundefs_append_r; eauto.
        split. eauto. intros Hleq Hpre'.
        eapply preord_exp_refl; eauto.
        eapply preord_env_P_set_lists_l; [| | now eauto | now eauto | now eauto].
        rewrite def_funs_append.
        apply preord_env_P_def_funs_not_in_P_r; eauto.
        intros x Hin Hfr.
        apply find_def_correct in Hf'.
        edestruct (occurs_free_in_fun _ _ _ _ _ Hf' x Hfr); try contradiction.
        inv H; eauto. unfold closed_fundefs in Hclo. rewrite Hclo in H0. inv H0.
    - simpl. intros x HP. inv HP.
  Qed.



  (*
  Lemma preord_val_def_funs_append_pre (k : nat) f tau xs e (B1 B2 : fundefs)
        (rho1 rho2  : env) :
    closed_fundefs (Fcons f tau xs (Efun B2 e) B1) ->
    closed_fundefs B2 ->
    unique_bindings_fundefs (Fcons f tau xs (Efun B2 e) B1) ->
    Disjoint var (name_in_fundefs (Fcons f tau xs e B1)) (name_in_fundefs B2) ->
    (forall j S1 rho1 rho2 rho1' rho2',
       j < k ->
       preord_env_P S1 j PG rho1 rho2 ->
       preord_env_P (Union var S1 (name_in_fundefs B1))
                    j PG
                    (def_funs (Fcons f tau xs (Efun B2 e) B1) B1 rho1' rho1)
                    (def_funs (fundefs_append (Fcons f tau xs e B1) B2) B1 rho2' rho2)) ->
    preord_val k PG (Vfun rho1 (Fcons f tau xs (Efun B2 e) B1) f)
               (Vfun rho2 (fundefs_append (Fcons f tau xs e B1) B2) f).
  Proof.
    revert f tau xs e B1 B2 rho1 rho2. induction k using lt_wf_rec1.
    intros f tau xs e B1 B2 rho1 rho2 Hcl1 Hcl2 Hun HD Hyp. rewrite preord_val_eq.
    intros vs1 vs2 j t1 xs1 e1 rho1' Hlen Hf Hs. inv Hf. destruct (M.elt_eq f f); try congruence. subst; inv H1.
    clear e0.

    edestruct (@set_lists_length val) as [rho2' Hs']; eauto.
    do 3 eexists. split. simpl.

    destruct (M.elt_eq f f); try congruence. eauto. split; eauto.

    intros Hleq Hpre'. simpl in Hs, Hs'. rewrite def_funs_append in Hs'.

    intros v1 c1 Hleq1 Hstep1. inv Hstep1.
    edestruct preord_exp_refl
      with (k := j + c) (rho := def_funs B2 B2 rho1' rho1') as [v2 [c2 [Hst2 [Hp2 Hv2]]]]; (try now eapply H5); eauto.
    - intros. eapply HGPost. now eapply H0.
    - admit.
    - lia.
    - do 2 eexists. split; eauto. split; eauto. simpl in Hp2. admit. eapply Hp2.
    - apply preord_env_P_antimon with
          (P2 := Union var (FromList xs1)
                       (Union var (name_in_fundefs B2)
                              (Union var (Singleton var f) (name_in_fundefs B1)))).
      { - repeat apply preord_env_P_union.
          + apply preord_env_P_def_funs_not_in_P_l.
            * eapply preord_env_P_set_lists_l with (P1 := Empty_set var) (xs := xs1);
                [ | | | now eauto | clear Hs'; now eauto ].
              eapply preord_env_Empty_set. intros x Hc1 Hc2. exfalso. eapply Hc1; eauto.
              eapply Forall2_refl. now eapply preord_val_refl.
            * inv Hun. eapply Disjoint_Included_r.
              eapply name_in_fundefs_bound_var_Efun. eauto using Disjoint_sym.
          + apply preord_env_P_def_funs_not_in_P_l. eapply preord_env_P_refl; eauto.
            eassumption.
          * eapply preord_env_P_set_lists_l with (P1 := Empty_set var) (xs := xs1);
              [ | | | now eauto | clear Hs'; now eauto ].
            eapply preord_env_Empty_set. intros x Hc1 Hc2. exfalso. eapply Hc1; eauto.
            eapply Forall2_refl. now eapply preord_val_refl.
          * inv Hun. eapply Disjoint_Included_r.
            eapply name_in_fundefs_bound_var_Efun. eauto using Disjoint_sym.

        + eapply preord_env_P_set_lists_not_in_P_r.
          * eapply preord_env_P_set_not_in_P_r; eauto with Ensembles_DB.
            eapply preord_env_P_def_funs_not_in_P_r; eauto with Ensembles_DB.
            eapply preord_env_P_trans;
              [| intros m; eapply preord_env_P_def_funs_strengthen_l
                             with (B2 := Fcons f t1 xs1 e B1) ]; eauto with Ensembles_DB.
            eapply preord_env_P_def_funs_cor; eauto.
            eapply preord_env_P_antimon. eapply preord_env_Empty_set.
          unfold closed_fundefs in Hcl2. rewrite Hcl2. eauto with Ensembles_DB.
          unfold closed_fundefs in Hcl2. rewrite Hcl2. eauto with Ensembles_DB.
        * inv Hun. eapply Disjoint_Included_l ; [| apply H8 ].
          eapply name_in_fundefs_bound_var_Efun.
      + inv Hun. eapply preord_env_P_set_lists_not_in_P_r; eauto with Ensembles_DB.
        eapply preord_env_P_def_funs_not_in_P_l; eauto with Ensembles_DB.
        eapply preord_env_P_set_lists_not_in_P_l; eauto with Ensembles_DB.
        eapply preord_env_P_extend. rewrite Setminus_Same_set_Empty_set.
        eapply preord_env_Empty_set.
        eapply H; eauto. now constructor; eauto. intros. eapply Hyp; eauto. lia.
      + inv Hun. eapply preord_env_P_set_lists_not_in_P_r; eauto.
        * eapply preord_env_P_set_not_in_P_r; eauto.
          eapply preord_env_P_def_funs_not_in_P_l; eauto with Ensembles_DB.
          eapply preord_env_P_set_lists_not_in_P_l; eauto with Ensembles_DB.
          eapply preord_env_P_set_not_in_P_l; eauto with Ensembles_DB.
          eapply preord_env_P_antimon. eapply Hyp. lia.
          eapply preord_env_Empty_set. eauto with Ensembles_DB.
          eapply Disjoint_Singleton_r. intros Hc. apply H7.
          apply name_in_fundefs_bound_var_fundefs; eauto.
          eapply Disjoint_Included_l; [| apply H9 ].
          apply name_in_fundefs_bound_var_fundefs; eauto.
          eapply Disjoint_Singleton_r. intros Hc. apply H7.
          apply name_in_fundefs_bound_var_fundefs; eauto.
        * eapply Disjoint_Included_l; [| apply H9 ]. intros x Hx.
          eapply name_in_fundefs_bound_var_fundefs; eauto.
    - eapply Included_trans. eapply occurs_free_Efun_Included with (B := B2).
      unfold closed_fundefs in Hcl1.
      intros x Hfr. inv Hfr; eauto.
      assert (Hin : fun_in_fundefs (Fcons f t1 xs1 (Efun B2 e) B1)
                                   (f, t1, xs1, (Efun B2 e)))
        by (constructor; eauto).
      edestruct (occurs_free_in_fun _ _ _ _ _ Hin x H0); eauto.  inv H1; eauto.
      unfold closed_fundefs in Hcl1. rewrite Hcl1 in H2. inv H2.
    -
    - edestruct H0 as [c2 [Hs'' [Hp Hr]]].


      Grab Existential Variables. eauto. eauto. eauto. eauto.
  Qed.

  Lemma preord_env_P_def_funs_append (k : nat) S1 f tau xs e (B1 B1' B2 : fundefs)
        (rho1 rho2 rho1' rho2' : env) :
    closed_fundefs (Fcons f tau xs (Efun B2 e) B1) ->
    closed_fundefs B2 ->
    unique_bindings_fundefs (Fcons f tau xs (Efun B2 e) B1) ->
    Disjoint var (name_in_fundefs (Fcons f tau xs e B1)) (name_in_fundefs B2) ->
    preord_env_P S1 k PG rho1 rho2 ->
    preord_env_P (Union var S1 (name_in_fundefs B1'))
                 k PG (def_funs (Fcons f tau xs (Efun B2 e) B1) B1' rho1' rho1)
                 (def_funs (fundefs_append (Fcons f tau xs e B1) B2) B1' rho2' rho2).
  Proof.
    revert S1 f tau xs e B1 B1' B2 rho1 rho2 rho1' rho2'. induction k using lt_wf_rec1.
    intros S1 f tau xs e B1 B1' B2 rho1 rho2 rho1' rho2' Hcl1 Hcl2 Hun HD Hpre1. simpl.
    induction B1'.
    - simpl. apply preord_env_P_extend.
      + eapply preord_env_P_antimon. now eauto. now eauto 7 with Ensembles_DB.
      + destruct (M.elt_eq v f); subst.
        * eapply preord_val_def_funs_append_pre; eauto.
        * rewrite preord_val_eq. intros vs1 vs2 j t1 xs1 e1 rho1'' Hlen Hf Hs.
          edestruct (@set_lists_length val) as [rho2'' Hs']; [eauto | | ]. eauto.
          exists xs1, e1, rho2''. repeat split; eauto.
          simpl in *. destruct (M.elt_eq v f); try congruence.
          specialize (find_def_name_in_fundefs _ _ _ Hf); intros Hname.
          erewrite <- find_def_fundefs_append_l in Hf; eauto.
          intros Hleq Hpre'. eapply preord_exp_refl; eauto.
          eapply preord_env_P_set_lists_l with
          (P1 := Union var (name_in_fundefs B1) (Singleton var f)); [| | eauto | eauto | eauto].
          simpl. eapply preord_env_P_extend. eapply preord_env_P_antimon.
          rewrite def_funs_append. eapply H; eauto. eapply preord_env_Empty_set.
          now eauto with Ensembles_DB.
          eapply preord_val_def_funs_append_pre; eauto. intros; eauto.
          eapply H; eauto. lia.
          destruct (M.elt_eq v f); try congruence.
          apply find_def_correct in Hf.
          intros x Hin Hfr. specialize (occurs_free_in_fun _ _ _ _ _ Hf x Hfr).
          intros H1. inv H1; try contradiction.
          inv H0; eauto. simpl in H1. inv H1; eauto. right; eauto. left; eauto.
          destruct (var_dec f x); subst. right; eauto.
          exfalso. eapply not_In_Empty_set. eapply Hcl1; eauto.
    - simpl. now rewrite Union_Empty_set_neut_r.
  Qed.


  Lemma preord_env_P_def_funs_hoist (k : nat) S1 f tau xs e (B1 B2 : fundefs)
        (rho1 rho2 : env) :
    closed_fundefs (Fcons f tau xs (Efun B2 e) B1) ->
    closed_fundefs B2 ->
    unique_bindings_fundefs (Fcons f tau xs (Efun B2 e) B1) ->
    Disjoint var S1 (name_in_fundefs B2) ->
    Disjoint var (name_in_fundefs (Fcons f tau xs e B1)) (name_in_fundefs B2) ->
    preord_env_P S1 k PG rho1 rho2 ->
    preord_env_P (Union var S1 (Union var (name_in_fundefs B1) (Singleton var f)))
                 k PG (def_funs (Fcons f tau xs (Efun B2 e) B1)
                                (Fcons f tau xs (Efun B2 e) B1)
                                rho1 rho1)
                 (def_funs (fundefs_append (Fcons f tau xs e B1) B2)
                           (fundefs_append (Fcons f tau xs e B1) B2)
                           rho2 rho2).
  Proof.
    intros Hcl1 Hcl2 Hun HD1 HD2 Hpre. simpl.
    eapply preord_env_P_extend.
    - eapply preord_env_P_antimon.
      rewrite def_funs_append. eapply preord_env_P_def_funs_append with (S1 := S1); eauto.
      eapply preord_env_P_def_funs_not_in_P_r; eauto.
      eauto with Ensembles_DB.
    - eapply preord_val_def_funs_append_pre; eauto.
      intros. eapply preord_env_P_def_funs_append; eauto.
  Qed.
   *)

  (* TODO : figure out fundefs above... *)

  Lemma proerd_env_P_def_funs_weakening k S1 B B1 B2 f tau xs e rho rho':
    ~ In var S1 f ->
    preord_env_P PG S1 k (def_funs B (fundefs_append B1 B2) rho rho')
                 (def_funs B (fundefs_append B1 (Fcons f tau xs e B2)) rho rho').
  Proof.
    revert S1 rho'. induction B1; intros S1 rho' Hin; simpl.
    - destruct (var_dec f v); subst.
      + apply preord_env_P_set_not_in_P_l; eauto using Disjoint_Singleton_r.
        apply preord_env_P_set_not_in_P_r; eauto using Disjoint_Singleton_r.
      + apply preord_env_P_extend.
        * eapply IHB1. intros Hc. inv Hc. eauto.
        * eapply preord_val_refl; eauto.
    - apply preord_env_P_set_not_in_P_r; eauto using Disjoint_Singleton_r.
      apply preord_env_P_refl; eauto.
  Qed.

  (* (* TODO : make this a corollary of a following proof *) *)
  (* Lemma preord_env_P_split_fds k S1 B1 B1' B2 B2' B11 B12 B11' B12' rho1 rho1' : *)
  (*   split_fds B11 B12 B1 -> *)
  (*   split_fds B11' B12' B1' -> *)
  (*   split_fds B11 B12 B2 -> *)
  (*   split_fds B11' B12' B2' -> *)
  (*   unique_bindings_fundefs B1' -> *)
  (*   unique_bindings_fundefs B1 ->   *)
  (*   preord_env_P PG S1 k (def_funs B1' B1 rho1 rho1') (def_funs B2' B2 rho1 rho1'). *)
  (* Proof. *)
  (*   intros Hspl. *)
  (*   revert B1 B11 B12 Hspl S1 B1' B2 B2' B11' B12' rho1 rho1'. induction k using lt_wf_rec1. *)
  (*   induction B1; intros B11 B12 Hspl1 S1 B1' B2 B2' B11' B12' rho1 rho1' *)
  (*                        Hspl1' Hspl2 Hspl2' Hun1 Hun2. *)
  (*   - edestruct split_fds_unique_bindings_fundefs_l as [H1 [H2 H3]]; [| |]; eauto. *)
  (*     specialize (split_fds_unique_bindings_fundefs_r _ _ _ H1 H2 H3 Hspl2); intros H4. *)
  (*     inv Hspl1. *)
  (*     + edestruct split_fds_cons_l_append_fundefs as [B3 [B4 [Heq Hspl3]]]; eauto. *)
  (*       eapply preord_env_P_antimon; *)
  (*         [| apply (@Included_Union_Setminus _ _ (name_in_fundefs B2) _)]. *)
  (*       eapply preord_env_P_union. *)
  (*       * eapply preord_env_P_def_funs_not_in_P_r; eauto with Ensembles_DB. *)
  (*         eapply preord_env_P_def_funs_not_in_P_l. eapply preord_env_P_refl; eauto. *)
  (*         rewrite split_fds_name_in_fundefs; eauto. simpl. *)
  (*         rewrite split_fds_name_in_fundefs with (B3 := B1); eauto. *)
  (*         eauto with Ensembles_DB. *)
  (*       * rewrite split_fds_name_in_fundefs; eauto. simpl (Union _ _ _). *)
  (*         rewrite <- Union_assoc. *)
  (*         eapply preord_env_P_union. *)
  (*         rewrite Heq. rewrite def_funs_append; eauto. *)
  (*         eapply preord_env_P_def_funs_not_in_P_r. *)
  (*         simpl. apply preord_env_P_extend. *)
  (*         rewrite Setminus_Same_set_Empty_set. apply preord_env_Empty_set. *)
  (*         { rewrite preord_val_eq. intros vs1 vs2 j t1 xs1 e1 rho1'' Hlen Hf Hs. *)
  (*           edestruct (@set_lists_length val) as [rho2'' Hs']; [eauto | | ]. eauto. *)
  (*           exists xs1, e1, rho2''. repeat split; eauto. *)
  (*           erewrite <- find_def_split_fds; eauto. *)
  (*           intros Hleq Hpre'. eapply preord_exp_refl; eauto. *)
  (*           eapply preord_env_P_set_lists_l; [| | | eauto | eauto ]; eauto. } *)
  (*         symmetry in Heq. eapply fundefs_append_split_fds in Heq. *)
  (*         edestruct split_fds_unique_bindings_fundefs_l as [H5 [H6 H8]]. apply H4.  eauto. *)
  (*         rewrite bound_var_fundefs_Fcons in H8. *)
  (*         eapply Disjoint_Included_r. eapply name_in_fundefs_bound_var_fundefs. *)
  (*         now eauto with Ensembles_DB. *)
  (*         simpl. eapply preord_env_P_set_not_in_P_l. *)
  (*         rewrite Heq. eapply preord_env_P_trans; *)
  (*           [| intros m; apply proerd_env_P_def_funs_weakening ]. *)
  (*         eapply IHB1; eauto. inv Hun2; eauto. *)
  (*         edestruct split_fds_unique_bindings_fundefs_l as [H5 [H6 H8]]; [apply H4| |]; eauto. *)
  (*         intros Hc. inv H5. inv Hc; eauto. apply H14. *)
  (*         apply name_in_fundefs_bound_var_fundefs; eauto. *)
  (*         eapply H8. constructor; eauto. now apply name_in_fundefs_bound_var_fundefs; eauto. *)
  (*         inv H1. apply Disjoint_Singleton_r. intros Hc. inv Hc. *)
  (*         eapply H11. now apply name_in_fundefs_bound_var_fundefs; eauto. *)
  (*         eapply H3. constructor; eauto. *)
  (*         now apply name_in_fundefs_bound_var_fundefs; eauto. *)
  (*     + edestruct split_fds_cons_r_append_fundefs as [B3 [B4 [Heq Hspl3]]]; eauto. *)
  (*       eapply preord_env_P_antimon; *)
  (*         [| apply (@Included_Union_Setminus _ _ (name_in_fundefs B2) _)]. *)
  (*       eapply preord_env_P_union. *)
  (*       * eapply preord_env_P_def_funs_not_in_P_r; *)
  (*         eauto with Ensembles_DB. *)
  (*         eapply preord_env_P_def_funs_not_in_P_l. eapply preord_env_P_refl; eauto. *)
  (*         rewrite split_fds_name_in_fundefs; eauto. simpl. *)
  (*         rewrite split_fds_name_in_fundefs with (B3 := B1); eauto. *)
  (*         eauto with Ensembles_DB. *)
  (*       * rewrite split_fds_name_in_fundefs; eauto. simpl (Union _ _ _). *)
  (*         rewrite Union_assoc, (Union_commut _ (Singleton var v)), <- Union_assoc. *)
  (*         eapply preord_env_P_union. *)
  (*         rewrite Heq. rewrite def_funs_append; eauto. *)
  (*         eapply preord_env_P_def_funs_not_in_P_r. *)
  (*         simpl. apply preord_env_P_extend. *)
  (*         rewrite Setminus_Same_set_Empty_set. apply preord_env_Empty_set. *)
  (*         { rewrite preord_val_eq. intros vs1 vs2 j t1 xs1 e1 rho1'' Hlen Hf Hs. *)
  (*           edestruct (@set_lists_length val) as [rho2'' Hs']; [eauto | | ]. eauto. *)
  (*           exists xs1, e1, rho2''. repeat split; eauto. *)
  (*           erewrite <- find_def_split_fds; eauto. *)
  (*           intros Hleq Hpre'. eapply preord_exp_refl; eauto. *)
  (*           eapply preord_env_P_set_lists_l; [| | | eauto | eauto ]; eauto. } *)
  (*         symmetry in Heq. eapply fundefs_append_split_fds in Heq. *)
  (*         edestruct split_fds_unique_bindings_fundefs_l as [H5 [H6 H8]]. *)
  (*         apply H4. eauto. rewrite bound_var_fundefs_Fcons in H8. *)
  (*         eapply Disjoint_Included_r. *)
  (*         eapply name_in_fundefs_bound_var_fundefs. eauto with Ensembles_DB. *)
  (*         simpl. eapply preord_env_P_set_not_in_P_l. *)
  (*         rewrite Heq. eapply preord_env_P_trans; *)
  (*           [| intros m; apply proerd_env_P_def_funs_weakening ]. *)
  (*         eapply IHB1; eauto. inv Hun2; eauto. *)
  (*         edestruct split_fds_unique_bindings_fundefs_l as [H5 [H6 H8]]; [apply H4| |]; eauto. *)
  (*         intros Hc. inv H6. inv Hc; eauto. eapply H8. constructor; eauto. *)
  (*         now apply name_in_fundefs_bound_var_fundefs; eauto. *)
  (*         eapply H14. now apply name_in_fundefs_bound_var_fundefs; eauto. *)
  (*         inv H2. apply Disjoint_Singleton_r. intros Hc. inv Hc. *)
  (*         eapply H3. constructor. now apply name_in_fundefs_bound_var_fundefs; eauto. *)
  (*         rewrite bound_var_fundefs_Fcons. left; eauto. *)
  (*         eapply H11. now apply name_in_fundefs_bound_var_fundefs; eauto. *)
  (*   - inv Hspl1. simpl. inv Hspl2. eapply preord_env_P_refl; eauto. *)
  (* Qed. *)


(* Need minor updates:

  Lemma preord_env_P_Included_fun_in_fundefs k B1 B1' B2 B2' rho1 rho1' :
    Included _ (fun_in_fundefs B1) (fun_in_fundefs B2) ->
    Included _ (fun_in_fundefs B1') (fun_in_fundefs B2') ->
    closed_fundefs B1' ->
    unique_functions B1'->
    unique_functions B1 ->
    unique_functions B2'->
    unique_functions B2 ->
    preord_env_P PG (name_in_fundefs B1) k (def_funs B1' B1 rho1 rho1')
                 (def_funs B2' B2 rho1 rho1').
  Proof.
    revert B1 B1' B2 B2' rho1 rho1'. induction k using lt_wf_rec1.
    induction B1; intros B1' B2 B2' rho1 rho1' HS1 HS2 Hcl Hun1' Hun1 Hun2' Hun2.
    - edestruct fun_in_fundefs_unique_functions_split
      with (B := B2) as [B [B' [Heq [Hn [HS Hun']]]]]; eauto.
      eapply HS1. left. eauto.
      edestruct fundefs_append_unique_functions_l as [H1 [H2 H3]]; eauto.
      rewrite Heq.
      eapply preord_env_P_antimon;
        [| apply (@Included_Union_Setminus _ _ (Singleton var v) _)].
      eapply preord_env_P_union.
      + simpl. eapply preord_env_P_set_not_in_P_l; eauto with Ensembles_DB.
        eapply preord_env_P_trans;
          [| intros m; apply proerd_env_P_def_funs_weakening; intros Hc; inv Hc; eauto ].
        rewrite Setminus_Union_distr, Setminus_Same_set_Empty_set, Union_Empty_set_neut_l.
        eapply preord_env_P_antimon; [ eapply IHB1; eauto |].
        rewrite (fundefs_append_fun_in_fundefs B B' (fundefs_append B B')); eauto.
        rewrite HS. simpl in HS1.
        rewrite <- (Setminus_Disjoint (fun_in_fundefs B1) (Singleton _ (v, f, l, e))).
        eapply Included_Setminus_compat; eauto using Included_refl.
        eapply Included_trans; [| eassumption ]. eauto with Ensembles_DB.
        eapply Disjoint_Singleton_r. inv Hun1; eauto. intros Hc. apply H9.
        apply name_in_fundefs_bound_var_fundefs.
        now eapply fun_in_fundefs_name_in_fundefs; eauto.
        now inv Hun1; eauto. eauto with Ensembles_DB.
      + rewrite def_funs_append;
        eapply preord_env_P_def_funs_not_in_P_r.
        * simpl. eapply preord_env_P_extend.
          rewrite Setminus_Same_set_Empty_set. apply preord_env_Empty_set.
          rewrite preord_val_eq. intros vs1 vs2 j t1 xs1 e1 rho1'' Hlen Hf Hs.
          edestruct (@set_lists_length val) as [rho2'' Hs']; [eauto | | ]. eauto.
          exists xs1, e1, rho2''. repeat split; eauto.
          erewrite <- find_def_Included_fun_in_fundefs; eauto.
          eapply fun_in_fundefs_name_in_fundefs. now eapply find_def_correct; eauto.
          intros Hleq Hpre'. eapply preord_exp_refl; eauto.
          clear; now firstorder.
          eapply preord_env_P_set_lists_l; [| | | eauto | eauto ]; eauto.
          intros c Hnin Hf'. apply find_def_correct in Hf.
          eapply occurs_free_in_fun in Hf'; eauto. inv Hf'.
          exfalso; eauto. inv H0; eauto.
          exfalso. eapply not_In_Empty_set. eapply Hcl; eauto.
        * apply Disjoint_Singleton_l. eauto.
    - simpl. eapply preord_env_Empty_set.
  Qed.

  Lemma preord_env_P_def_funs_merge k S1 B B' B'' rho rho' :
    unique_bindings_fundefs B ->
    split_fds B' B'' B ->
    closed_fundefs B' ->
    closed_fundefs B'' ->
    preord_env_P PG S1 k rho rho' ->
    preord_env_P PG (Union var S1 (name_in_fundefs B)) k
                 (def_funs B' B' (def_funs B'' B'' rho rho)
                           (def_funs B'' B'' rho rho))
                 (def_funs B B rho' rho').
  Proof.
    intros Hun HS Hcl Hcl' Hpre.
    assert (Hcl'' := split_fds_closed_fundefs B' B'' B HS Hcl Hcl').
    rewrite (@Union_Setminus _ _ _ _ ).
    eapply preord_env_P_union.
    - eapply preord_env_P_def_funs_not_in_P_l; eauto with Ensembles_DB.
      eapply preord_env_P_def_funs_not_in_P_l; eauto with Ensembles_DB.
      eapply preord_env_P_def_funs_not_in_P_r; eauto with Ensembles_DB.
      eapply preord_env_P_antimon; eauto with Ensembles_DB.
      rewrite split_fds_name_in_fundefs; eauto with Ensembles_DB.
      rewrite (split_fds_name_in_fundefs B' B'' B); eauto with Ensembles_DB.
    - edestruct split_fds_unique_bindings_fundefs_l as [H1 [H2 H3]]; eauto.
      rewrite split_fds_name_in_fundefs; eauto. eapply preord_env_P_union.
      + eapply preord_env_P_trans.
        eapply preord_env_P_Included_fun_in_fundefs with (B2 := B) (B2' := B);
          eauto using Included_refl;
          try (now rewrite (split_fds_fun_in_fundefs B' B'' B); eauto;
               apply Included_Union_l).
        intros m. eapply preord_env_P_def_funs_cor; eauto.
        rewrite (split_fds_name_in_fundefs B' B'' B); eauto.
        unfold closed_fundefs in *. rewrite Hcl'', Union_Empty_set_neut_r.
        rewrite Setminus_Included_Empty_set. eapply preord_env_Empty_set.
        eauto with Ensembles_DB.
      + eapply preord_env_P_def_funs_not_in_P_l.
        eapply preord_env_P_trans.
        eapply preord_env_P_Included_fun_in_fundefs with (B2 := B) (B2' := B);
          eauto using Included_refl;
          try (now rewrite (split_fds_fun_in_fundefs B' B'' B); eauto;
               apply Included_Union_r).
        intros m. eapply preord_env_P_def_funs_cor; eauto.
        rewrite (split_fds_name_in_fundefs B' B'' B); eauto.
        unfold closed_fundefs in *. rewrite Hcl'', Union_Empty_set_neut_r.
        rewrite Setminus_Included_Empty_set. eapply preord_env_Empty_set.
        now eauto with Ensembles_DB.
        eapply Disjoint_Included_r. eapply name_in_fundefs_bound_var_fundefs.
        eapply Disjoint_Included_l. eapply name_in_fundefs_bound_var_fundefs.
        now apply Disjoint_sym.
  Qed.


  Lemma preord_env_P_Same_set_fun_in_fundefs k S1 B1 B1' B2 B2' rho1 rho1' :
    Same_set _ (fun_in_fundefs B1) (fun_in_fundefs B2) ->
    Same_set _ (fun_in_fundefs B1') (fun_in_fundefs B2') ->
    unique_bindings_fundefs B1'->
    unique_bindings_fundefs B1 ->
    unique_bindings_fundefs B2'->
    unique_bindings_fundefs B2 ->
    preord_env_P PG S1 k (def_funs B1' B1 rho1 rho1') (def_funs B2' B2 rho1 rho1').
  Proof.
    revert B1 S1 B1' B2 B2' rho1 rho1'. induction k using lt_wf_rec1.
    induction B1; intros S1 B1' B2 B2' rho1 rho1' HS1 HS2 Hun1' Hun1 Hun2' Hun2.
    - edestruct fun_in_fundefs_unique_bindings_split
      with (B := B2) as [B [B' [Heq [Hn [HS Hun']]]]]; eauto.
      eapply HS1. left. eauto.
      edestruct fundefs_append_unique_bindings_l as [H1 [H2 H3]]; eauto.
      rewrite Heq.
      eapply preord_env_P_antimon;
        [| apply (@Included_Union_Setminus _ _ (Singleton var v) _)].
      eapply preord_env_P_union.
      + simpl. eapply preord_env_P_set_not_in_P_l;
          eauto using Disjoint_Setminus_l, Included_refl.
        eapply preord_env_P_trans;
          [| intros m; apply proerd_env_P_def_funs_weakening; intros Hc; inv Hc; eauto ].
        eapply IHB1; eauto ; try (now inv Hun1; eauto).
        rewrite (fundefs_append_fun_in_fundefs B B' (fundefs_append B B')); eauto.
        rewrite HS, <- HS1. eauto with Ensembles_DB. simpl.
        rewrite Setminus_Union_distr, Setminus_Same_set_Empty_set, Union_Empty_set_neut_l.
        inv Hun1. rewrite Setminus_Disjoint; eauto with Ensembles_DB.
        eapply Disjoint_Singleton_r.
        intros Hc. apply H9. apply name_in_fundefs_bound_var_fundefs.
        eapply fun_in_fundefs_name_in_fundefs; eauto.
      + rewrite def_funs_append;
        eapply preord_env_P_def_funs_not_in_P_r.
        * simpl. eapply preord_env_P_extend.
          rewrite Setminus_Same_set_Empty_set. apply preord_env_Empty_set.
          rewrite preord_val_eq. intros vs1 vs2 j t1 xs1 e1 rho1'' Hlen Hf Hs.
          edestruct (@set_lists_length val) as [rho2'' Hs']; [eauto | | ]. eauto.
          exists xs1, e1, rho2''. repeat split; eauto.
          erewrite <- find_def_Same_set_fun_in_fundefs; eauto.
          intros Hleq Hpre'. eapply preord_exp_refl; eauto. clear; now firstorder.
          eapply preord_env_P_set_lists_l; [| | | eauto | eauto ]; eauto.
        * eauto with Ensembles_DB.
    - simpl. destruct B2; eauto using preord_env_P_refl.
      destruct HS1 as [_ H1]. exfalso. eapply not_In_Empty_set. eapply H1.
      simpl. eauto.
  Qed.
*)
  End Trans.

End Log_rel.

Notation preord_exp := (fun cenv => (preord_exp' cenv (preord_val cenv))).
