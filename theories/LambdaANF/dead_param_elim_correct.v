Require Import LambdaANF.term LambdaANF.identifiers LambdaANF.ctx LambdaANF.set_util LambdaANF.state LambdaANF.alpha_conv
        LambdaANF.dead_param_elim LambdaANF.Ensembles_util LambdaANF.tactics LambdaANF.map_util LambdaANF.term_util
        LambdaANF.hoisting LambdaANF.dead_param_elim_util LambdaANF.eval LambdaANF.algebra LambdaANF.logical_relations.
Require Import compcert.lib.Coqlib Common.compM Common.Pipeline_utils.
From Stdlib Require Import Lists.List MSets.MSets MSets.MSetRBT Numbers.BinNums
        NArith.BinNat PArith.BinPos Sets.Ensembles micromega.Lia.
Require Import maps_util.
Require Import ExtLib.Structures.Monads ExtLib.Data.Monads.StateMonad.
Import ListNotations Nnat.

Require Import LambdaANF.alpha_conv LambdaANF.term LambdaANF.term_util LambdaANF.ctx LambdaANF.state LambdaANF.set_util LambdaANF.identifiers LambdaANF.List_util
        LambdaANF.functions LambdaANF.Ensembles_util LambdaANF.uncurry LambdaANF.tactics.
From Stdlib Require Import ZArith.Znumtheory Strings.String.
From Stdlib Require Import Lists.List MSets.MSets MSets.MSetRBT Numbers.BinNums
        NArith.BinNat PArith.BinPos Sets.Ensembles.
Require Import ExtLib.Structures.Monads ExtLib.Data.Monads.StateMonad ExtLib.Data.Monads.OptionMonad.
Require Import compcert.lib.Coqlib.

Import ListNotations Nnat MonadNotation PS.



Import MonadNotation.
Open Scope monad_scope.

Open Scope ctx_scope.
Open Scope fun_scope.
Open Scope alg_scope.
Close Scope Z_scope.


(* DPE as a relation *)

(* S is the set of formal parameters that have been eliminated from the *current* function.
   That is, whatever is in S, is undefined in the environment when we execute the code. *)
Inductive Elim_expr (L : live_fun) (find_tag : var -> option fun_tag) :  exp -> exp -> Prop :=
| Elim_Constr :
    forall (x : var) (ys : list var) (ct : ctor_tag) (e : exp) (e' : exp),
      Elim_expr L find_tag e e' ->
      Elim_expr L find_tag (Econstr x ct ys e) (Econstr x ct ys e')
| Elim_Prim_val :
    forall (x : var) p (e : exp) (e' : exp),
      Elim_expr L find_tag e e' ->
      Elim_expr L find_tag (Eprim_val x p e) (Eprim_val x p e')
| Elim_Prim :
    forall (x : var) (g : prim) (ys : list var) (e : exp) (e' : exp),
      Elim_expr L find_tag e e' ->
      Elim_expr L find_tag (Eprim x g ys e) (Eprim x g ys e')
| Elim_Proj :
    forall (x : var) (ct : ctor_tag) (n : N) (y : var) (e : exp) (e' : exp),
      Elim_expr L find_tag e e' ->
      Elim_expr L find_tag (Eproj x ct n y e) (Eproj x ct n y e')
| Elim_Case:
    forall (x : var) (ce : list (ctor_tag * exp)) (ce' : list (ctor_tag * exp)),
      Forall2 (fun p1 p2 => fst p1 = fst p2 /\ Elim_expr L find_tag (snd p1) (snd p2)) ce ce' ->
      Elim_expr L find_tag (Ecase x ce) (Ecase x ce')
| Elim_Halt :
    forall (x : var),
      Elim_expr L find_tag (Ehalt x) (Ehalt x)
| Elim_App_Unknown :
    forall (f : var) (ys : list var) (ft : fun_tag),
      L ! f = None ->
      Elim_expr L find_tag (Eapp f ft ys) (Eapp f ft ys)
| Elim_App_Known :
    forall (f : var) (ys : list var) (ft ft' : fun_tag) (bs : list bool),
      L ! f = Some bs ->
      find_tag f = Some ft' ->
      Elim_expr L find_tag (Eapp f ft ys) (Eapp f ft' (live_args ys bs))
| Elim_Letapp_Unknown :
    forall (x f : var) (ys : list var) (ys' : list var) (ft : fun_tag) (e e' : exp),
      L ! f = None ->
      Elim_expr L find_tag e e' ->
      Elim_expr L find_tag (Eletapp x f ft ys e) (Eletapp x f ft ys e')
| Elim_Letapp_Known :
    forall (x f : var) (ys : list var) (ys' : list var) (ft ft' : fun_tag) (e e' : exp) (bs : list bool),
      L ! f = Some bs ->
      find_tag f = Some ft' ->
      Elim_expr L find_tag e e' ->
      Elim_expr L find_tag (Eletapp x f ft ys e) (Eletapp x f ft' (live_args ys bs) e').

Inductive Elim_fundefs (L : live_fun) (find_tag : var -> option fun_tag) : fundefs -> fundefs -> Prop :=
| Elim_nil :
  Elim_fundefs L find_tag Fnil Fnil
| Elim_cons_in_map :
    forall (F : fundefs) (F' : fundefs) (e : exp) (e' : exp) (xs : list var) (bs : list bool)
           (g : var) (ft ft' : fun_tag),
      L ! g = Some bs ->
      find_tag g = Some ft' ->
      Elim_expr L find_tag e e' ->
      Elim_fundefs L find_tag F F' ->
      Elim_fundefs L find_tag (Fcons g ft xs e F) (Fcons g ft' (live_args xs bs) e' F')
| Elim_cons_not_in_map :
    forall (F : fundefs) (F' : fundefs) (e : exp) (e' : exp) (xs : list var)
           (g : var) (ft : fun_tag),
      L ! g = None ->
      Elim_expr L find_tag e e' ->
      Elim_fundefs L find_tag F F' ->
      Elim_fundefs L find_tag (Fcons g ft xs e F) (Fcons g ft xs e' F').



Lemma Elim_fundefs_exists_Some L find_tag B B' bs f ft xs e :
  Elim_fundefs L find_tag B B' ->
  L ! f = Some bs ->
  fun_in_fundefs B (f, ft, xs, e) ->
  exists ft' e',
    find_tag f = Some ft' /\
    fun_in_fundefs B' (f, ft', live_args xs bs, e') /\
    Elim_expr L find_tag e e'.
Proof.
  intros. induction H.
  - inv H1.
  - inv H1.
    + inv H5. repeat subst_exp. do 2 eexists. split; eauto. split; eauto. now left.
    + edestruct IHElim_fundefs. eassumption. destructAll.
      do 2 eexists. split; eauto. split; eauto. now right; eauto.
  - inv H1.
    + inv H4. congruence.
    + edestruct IHElim_fundefs. eassumption. destructAll.
      do 2 eexists. split; eauto. split; eauto. now right; eauto.
Qed.

Lemma Elim_fundefs_exists_None L find_tag B B' f ft xs e :
  Elim_fundefs L find_tag B B' ->
  L ! f = None ->
  fun_in_fundefs B (f, ft, xs, e) ->
  exists e',
    fun_in_fundefs B' (f, ft, xs, e') /\
    Elim_expr L find_tag e e'.
Proof.
  intros. induction H.
  - inv H1.
  - inv H1.
    + inv H5. congruence.
    + edestruct IHElim_fundefs. eassumption. destructAll.
      eexists. split; eauto. now right; eauto.
  - inv H1.
    + inv H4. repeat subst_exp. eexists. split; eauto. now left.
    + edestruct IHElim_fundefs. eassumption. destructAll.
      eexists. split; eauto. now right; eauto.
Qed.

Lemma Elim_fundefs_name_in_fundefs L find_tag B B' :
  Elim_fundefs L find_tag B B' ->
  name_in_fundefs B <--> name_in_fundefs B'.
Proof.
  intros H. induction H; simpl; sets.
Qed.

Lemma live_args_NoDup {A} (xs : list A) bs :
  NoDup xs ->
  NoDup (live_args xs bs).
Proof.
  revert bs. induction xs; intros.
  - destruct bs; eauto.
  - destruct bs; eauto.
    inv H. simpl. destruct b; eauto.
    econstructor; eauto.

    intros Hc. eapply live_args_subset in Hc. eauto.
Qed.

(** Well-scopedness lemmas **)

Lemma Elim_exp_bound_var L find_tag e e' :
  Elim_expr L find_tag e e' ->
  bound_var e' \subset bound_var e.
Proof.
  revert e'.
  induction e using exp_ind'; intros e' Helim; inv Helim;
    try repeat normalize_bound_var; sets.

  inv H2.
  + rewrite !bound_var_Ecase_nil at 1. sets.
  + inv H2. inv H1. destruct y.
    repeat normalize_bound_var.
    simpl in *. subst.
    eapply Included_Union_compat; eauto.
    eapply IHe0. econstructor; eauto.
Qed.

Lemma Elim_fundefs_bound_var L find_tag B B' :
  Elim_fundefs L find_tag B B' ->
  bound_var_fundefs B' \subset bound_var_fundefs B.
Proof.
  intros Helim; induction Helim; sets; repeat normalize_bound_var.
  - eapply Included_Union_compat; sets.
    eapply Included_Union_compat; sets.
    eapply live_args_subset.
    eapply Elim_exp_bound_var in H1. sets.
  - eapply Included_Union_compat; sets.
    eapply Included_Union_compat; sets.
    eapply Elim_exp_bound_var in H0. sets.
Qed.

Lemma Elim_exp_unique_bindings L find_tag e e' :
  Elim_expr L find_tag e e' ->
  unique_bindings e ->
  unique_bindings e'.
Proof.
  revert e'.
  induction e using exp_ind'; intros e' Helim Hun; inv Helim;
    inv Hun; try (now econstructor; eauto);
      try (now econstructor; eauto; intros Hc; eapply H1; eapply Elim_exp_bound_var; eauto).
  - inv H2. econstructor; eauto.
  - inv H2. destruct y. inv H1. econstructor; eauto.

    eapply IHe0. now econstructor; eauto. eassumption.

    eapply Disjoint_Included_l.
    eapply Elim_exp_bound_var. eassumption.
    eapply Disjoint_Included_r.
    eapply Elim_exp_bound_var. econstructor. eassumption.
    sets.
Qed.


Lemma Elim_fundefs_unique_bindings L find_tag B B' :
  Elim_fundefs L find_tag B B' ->
  unique_bindings_fundefs B ->
  unique_bindings_fundefs B'.
Proof.
  intros Helim Hun; induction Helim; inv Hun; eauto.
  - econstructor.
  - econstructor; eauto.
    + intros Hc; eapply H7; eapply Elim_exp_bound_var; eauto.
    + intros Hc; eapply H8; eapply Elim_fundefs_bound_var; eauto.
    + eapply Disjoint_Included.
      eapply live_args_subset.
      eapply Elim_exp_bound_var; eauto.
      sets.
    + eapply Disjoint_Included.
      eapply live_args_subset.
      eapply Elim_fundefs_bound_var; eauto.
      sets.
    + eapply Disjoint_Included.
      eapply Elim_fundefs_bound_var; eauto.
      eapply Elim_exp_bound_var; eauto.
      sets.
    + intros Hc. eapply live_args_subset in Hc. eauto.
    + eapply live_args_NoDup. eassumption.
    + eapply Elim_exp_unique_bindings; eauto.
  - econstructor; eauto.
    + intros Hc; eapply H6; eapply Elim_exp_bound_var; eauto.
    + intros Hc; eapply H7; eapply Elim_fundefs_bound_var; eauto.
    + eapply Disjoint_Included_l.
      eapply Elim_exp_bound_var; eauto.
      sets.
    + eapply Disjoint_Included_l.
      eapply Elim_fundefs_bound_var; eauto.
      sets.
    + eapply Disjoint_Included.
      eapply Elim_fundefs_bound_var; eauto.
      eapply Elim_exp_bound_var; eauto.
      sets.
    + eapply Elim_exp_unique_bindings; eauto.
Qed.


Lemma Dead_Disjoint S L find_tag e e' :
  Dead S L e ->
  Elim_expr L find_tag e e' ->
  Disjoint _ S (occurs_free e').
Proof.
  revert e'.
  induction e using exp_ind'; intros e' Hdead Helim; inv Helim; inv Hdead;
    try congruence; repeat normalize_occurs_free; sets;
      try (now eapply Union_Disjoint_r; sets).
  - inv H2. normalize_occurs_free. sets.
  - inv H2. inv H3. destruct y. normalize_occurs_free. simpl in *. inv H4.
    eapply Union_Disjoint_r. now sets.
    eapply Union_Disjoint_r. now sets.
    eapply IHe0; econstructor; eassumption.
  - repeat subst_exp.
    eapply Union_Disjoint_r. now sets.
    eapply Disjoint_Included_r. eapply Setminus_Included. sets.
Qed.


Lemma dead_arg_live_arg xs bs :
  FromList xs <--> FromList (dead_args xs bs) :|: FromList (live_args xs bs).
Proof.
  revert bs. induction xs; intros [|]; simpl.
  - rewrite !FromList_nil at 1. sets.
  - rewrite !FromList_nil at 1. sets.
  - repeat normalize_sets. sets.
  - destruct b; repeat normalize_sets; sets.
    rewrite (IHxs l). now sets.
    rewrite (IHxs l). now sets.
Qed.

Lemma Elim_exp_occurs_free L find_tag e e' :
  Elim_expr L find_tag e e' ->
  occurs_free e' \subset occurs_free e.
Proof.
  revert e'.
  induction e using exp_ind'; intros e' Helim; inv Helim;
    try repeat normalize_occurs_free; sets.
  - inv H2. normalize_occurs_free. sets.
  - inv H2. destruct y. normalize_occurs_free. simpl in *. inv H1.
    rewrite !Union_assoc. eapply Included_Union_compat; sets.
    eapply IHe0. econstructor; eauto.
  - assert (Hsub := live_args_subset ys bs). sets.
  - assert (Hsub := live_args_subset l bs). sets.
Qed.

Lemma Elim_fundefs_occurs_free L find_tag B B' :
  Elim_fundefs L find_tag B B' ->
  live_map_sound B L ->
  occurs_free_fundefs B' \subset occurs_free_fundefs B.
Proof.
  intros Helim Hl; induction Helim; sets.
  - repeat normalize_occurs_free.
    eapply Included_Union_compat.
    + eapply Hl in H. 2:{ now left. }
      rewrite (dead_arg_live_arg xs bs).
      rewrite Elim_fundefs_name_in_fundefs with (B := F); eauto.
      eapply Dead_Disjoint in H; [| eassumption ].
      rewrite <- (Setminus_Disjoint (occurs_free e')) at 1; [| eapply Disjoint_sym; eassumption ].
      rewrite Setminus_Union.
      eapply Included_trans.

      eapply Included_Setminus_compat; [ eapply Elim_exp_occurs_free; eassumption | reflexivity ].
      sets.
    + eapply Included_Setminus_compat; sets.
      eapply IHHelim.
      intro; intros. eapply Hl; eauto. now right; eauto.
  - repeat normalize_occurs_free.
    eapply Included_Union_compat.
    + rewrite Elim_fundefs_name_in_fundefs with (B := F); eauto.
      eapply Included_Setminus_compat; sets.
      eapply Elim_exp_occurs_free. eassumption.
    + eapply Included_Setminus_compat; sets.
      eapply IHHelim.
      intro; intros. eapply Hl; eauto. now right; eauto.
Qed.


Require Import lambda_lifting_corresp.

Section Corresp.


  Opaque bind ret.

  (** * The DPE is sound w.r.t. its relational specification *)

  Lemma eliminate_expr_sound (fmap : ftagMap) (L : live_fun) (Hdom : Dom_map L \subset Dom_map fmap) :
    forall (e : exp) (Hnf : no_fun e),
       {{ fun r s => True }}
         eliminate_expr fmap L e
       {{ fun r s e' s' =>
            s = s' /\
            Elim_expr L (fun x => fmap ! x) e e' }}.
  Proof.
    induction e using exp_ind'; intros; inv Hnf; simpl;
      try
        (now eapply bind_triple;
         [ eapply IHe |
           intros; eapply return_triple; intros; destructAll; split; [ eauto | econstructor; eauto ] ] ).

    - (* Ecase nil *)
      eapply return_triple; intros; split; eauto. constructor; eauto.

    - (* Ecase cons *)
      setoid_rewrite assoc. eapply bind_triple.
      + eapply IHe; eauto.
      + intros e' s1. simpl.
        setoid_rewrite st_eq_Ecase. eapply pre_curry_r. intros He.
        eapply bind_triple.
        * eapply pre_strenghtening with (P := fun _ s => s1 = s /\ True).
          clear; now firstorder.
          eapply frame_rule.
          eapply IHe0; eauto.
        * simpl. intros. eapply pre_curry_l. intros Heq; subst.
          eapply pre_curry_r. intros Hel. assert (Hel' := Hel). inv Hel'.
          eapply return_triple. intros. split; eauto.
          econstructor; eauto.

    - (* Eletapp *)
      unfold get_fun_vars.
      destruct (L ! f) eqn:Hget.

      + (* Some *)

        assert (He : exists ft, fmap ! f = Some ft).
        { eapply Hdom. eexists; eauto. }
        destructAll.

        unfold dead_param_elim.get_fun_tag. rewrite H.

        eapply bind_triple.
        * eapply IHe; eauto.
        * intros e' s1. simpl.
          eapply return_triple; intros; destructAll; split; [ eauto | econstructor; eauto ].

      + (* None *)

        eapply bind_triple.
        * eapply IHe; eauto.
        * intros e' s1. simpl.
          eapply return_triple; intros; destructAll; split; [ eauto | econstructor; eauto ].

    - (* Eapp *)

      unfold get_fun_vars.
      destruct (L ! v) eqn:Hget.

      + (* Some *)

        assert (He : exists ft, fmap ! v = Some ft).
        { eapply Hdom. eexists; eauto. }
        destructAll.

        unfold dead_param_elim.get_fun_tag. rewrite H.

        eapply return_triple; intros; destructAll; split; [ eauto | econstructor; eauto ].

      + (* None *)
        eapply return_triple; intros; destructAll; split; [ eauto | econstructor; eauto ].

    - eapply return_triple; intros; destructAll; split; [ eauto | econstructor; eauto ].
  Qed.


  Lemma eliminate_fundefs_sound (fmap : ftagMap) (L : live_fun) (Hdom : Dom_map L \subset Dom_map fmap) :
    forall (B : fundefs) (Hnf : no_fun_defs B),
      {{ fun r s => True }}
        eliminate_fundefs fmap L B
      {{ fun r s B' s' =>
           s = s' /\
           Elim_fundefs L (fun x => fmap ! x) B B' }}.
  Proof.
    induction B; intros; inv Hnf; simpl.
    - (* Fcons *)
      unfold get_fun_vars.
      destruct (L ! v) eqn:Hget.

      + (* Some *)

        assert (He : exists ft, fmap ! v = Some ft).
        { eapply Hdom. eexists; eauto. }
        destructAll.

        unfold dead_param_elim.get_fun_tag. rewrite H.

        eapply bind_triple.
        * eapply eliminate_expr_sound; eauto.
        * intros e' s1. simpl.
          eapply pre_curry_r. intros He.

          eapply bind_triple.

          -- eapply pre_strenghtening with (P := fun _ s => s1 = s /\ True).
             clear; now firstorder.
             eapply frame_rule.
             eapply IHB; eauto.

          -- simpl; intros. eapply return_triple. intros. destructAll.
             split; eauto. econstructor; eauto.

      + (* None *)

        eapply bind_triple.
        * eapply eliminate_expr_sound; eauto.
        * intros e' s1. simpl.
          eapply pre_curry_r. intros He.

          eapply bind_triple.

          -- eapply pre_strenghtening with (P := fun _ s => s1 = s /\ True).
             clear; now firstorder.
             eapply frame_rule.
             eapply IHB; eauto.

          -- simpl; intros. eapply return_triple. intros. destructAll.
             split; eauto. econstructor; eauto.


    - (* Fnil *)

      eapply return_triple. intros. split; eauto. econstructor.
  Qed.

End Corresp.



Section Correct.

  Context {fuel : Type} {Hfuel : @fuel_resource fuel} {trace : Type} {Htrace : @trace_resource trace}.

  Variable cenv : ctor_env.

  Context (PL : @PostT fuel trace) (* Local *)
          (PG : @PostGT fuel trace).  (* Global *)

  Context (HPost : Post_properties cenv PL PL PG).


  Definition fun_inv (L : live_fun) (find_tag  : var -> option fun_tag) k (rho rho' : env) : Prop :=
    (forall f, f \in Dom_map L -> exists rho1 B1 f1, M.get f rho = Some (Vfun rho1 B1 f1)) /\
    forall f bs vs1 vs2 j ft1 ft2 rho1 rho1' B1 f1 xs1 e1,
      L ! f = Some bs ->
      find_tag f = Some ft2 ->
      M.get f rho = Some (Vfun rho1 B1 f1) ->
      find_def f1 B1 = Some (ft1, xs1, e1) ->
      Some rho1' = set_lists xs1 vs1 (def_funs B1 B1 rho1 rho1) ->
      length (live_args xs1 bs) = length vs2 ->

      exists rho2 rho2' B2 f2 xs2 e2,
        M.get f rho' = Some (Vfun rho2 B2 f2) /\
        find_def f2 B2 = Some (ft2, xs2, e2) /\
        Some rho2' = set_lists xs2 vs2 (def_funs B2 B2 rho2 rho2) /\

        (j < k -> Forall2 (preord_val cenv PG j) (live_args vs1 bs) vs2 ->
         preord_exp cenv PL PG j (e1, rho1') (e2, rho2')).



  (* Lemmas about fun_inv *)

  Lemma fun_inv_set_Disjoint_l L find_tag k x v1 rho1 rho2 :
    fun_inv L find_tag k rho1 rho2 ->
    Disjoint _ [set x] (Dom_map L) ->
    fun_inv L find_tag k (M.set x v1 rho1) rho2.
  Proof.
    intros Hinv Hd. split.
    { intro; intros.
      destruct (peq x f).
      - subst. exfalso. eapply Hd. constructor; eauto.
      - rewrite !M.gso in *; eauto. eapply Hinv. eauto. }

    { intro; intros. destruct (peq x f).
      - subst. exfalso. eapply Hd. constructor; eauto. eexists; eassumption.
      - rewrite !M.gso in *; eauto. eapply Hinv; eauto. }
  Qed.

  Lemma fun_inv_set_Disjoint_r L find_tag k x v1 rho1 rho2 :
    fun_inv L find_tag k rho1 rho2 ->
    Disjoint _ [set x] (Dom_map L) ->
    fun_inv L find_tag k rho1 (M.set x v1 rho2).
  Proof.
    intros Hinv Hd. split.
    { intro; intros.
      destruct (peq x f).
      - subst. exfalso. eapply Hd. constructor; eauto.
      - eapply Hinv. eauto. }

    { intro; intros. destruct (peq x f).
      - subst. exfalso. eapply Hd. constructor; eauto. eexists; eassumption.
      - rewrite !M.gso in *; eauto. eapply Hinv; eauto. }
  Qed.

  Lemma fun_inv_set_Disjoint L find_tag k x v1 v2 rho1 rho2 :
    fun_inv L find_tag k rho1 rho2 ->
    Disjoint _ [set x] (Dom_map L) ->
    fun_inv L find_tag k (M.set x v1 rho1) (M.set x v2 rho2).
  Proof.
    intros Hinv Hd.
    eapply fun_inv_set_Disjoint_l; eauto.
    eapply fun_inv_set_Disjoint_r; eauto.
  Qed.


  Lemma fun_inv_set_lists_Disjoint_l L find_tag k xs vs rho1 rho2 rho1' :
    fun_inv L find_tag k rho1 rho2 ->
    Disjoint _ (FromList xs) (Dom_map L) ->
    set_lists xs vs rho1 = Some rho1' ->
    fun_inv L find_tag k rho1' rho2.
  Proof.
    revert vs rho1 rho2 rho1'; induction xs; simpl; intros vs rho1 rho2 rho1' Hf Hdis Hset.
    - destruct vs; congruence.
    - destruct vs; try congruence.
      destruct (set_lists xs vs rho1) eqn:Heq. repeat normalize_sets.
      inv Hset.
      eapply fun_inv_set_Disjoint_l; sets.
      congruence.
  Qed.


  Lemma fun_inv_set_lists_Disjoint_r L find_tag k xs vs rho1 rho2 rho2' :
    fun_inv L find_tag k rho1 rho2 ->
    Disjoint _ (FromList xs) (Dom_map L) ->
    set_lists xs vs rho2 = Some rho2' ->
    fun_inv L find_tag k rho1 rho2'.
  Proof.
    revert vs rho1 rho2 rho2'; induction xs; simpl; intros vs rho1 rho2 rho1' Hf Hdis Hset.
    - destruct vs; congruence.
    - destruct vs; try congruence.
      destruct (set_lists xs vs rho2) eqn:Heq. repeat normalize_sets.
      inv Hset.
      eapply fun_inv_set_Disjoint_r; sets.
      congruence.
  Qed.



  Lemma fun_inv_monotonic L find_tag k m rho1 rho2 :
    fun_inv L find_tag k rho1 rho2 ->
    m <= k ->
    fun_inv L find_tag m rho1 rho2.
  Proof.
    intros [Hyp Hinv] Hd. split; eauto. intro; intros. edestruct Hinv; eauto. destructAll.
    do 6 eexists. repeat split. eassumption. eassumption. eassumption. intros.
    eapply preord_exp_monotonic. eapply H8; eauto. lia. lia.
  Qed.

  Lemma live_args_nil {A} xs :
    @live_args A xs [] = xs.
  Proof. destruct xs; eauto. Qed.


  Lemma preord_env_P_get_list_live_args xs (S : var -> Prop) bs k rho1 rho2 vs1 :
    preord_env_P cenv PG S k rho1 rho2 ->
    Included var (FromList (live_args xs bs)) S ->
    get_list xs rho1 = Some vs1 ->
    exists vs2 : list val,
      get_list (live_args xs bs) rho2 = Some vs2 /\ Forall2 (preord_val cenv PG k) (live_args vs1 bs) vs2.
  Proof with now eauto with Ensembles_DB.
    revert vs1 bs. induction xs; intros vs1 bs Henv Hinc Hget.
    - inv Hget. destruct bs; eexists; simpl; split; eauto; econstructor.
    - simpl in *.
      destruct (M.get a rho1) eqn:Hgeta; try discriminate.
      destruct (get_list xs rho1) eqn:Hgetl; try discriminate.
      inv Hget.
      destruct bs; simpl in *.
      + simpl in *. repeat normalize_sets. edestruct Henv. eapply Hinc. now left. eassumption.
        inv H.
        edestruct IHxs with (bs := @nil bool); eauto.
        { destruct xs; simpl; repeat normalize_sets; sets.
          eapply Included_trans; [| eassumption ]; simpl. sets. }
        rewrite live_args_nil in H. destructAll.
        rewrite live_args_nil in H2.

        eexists. rewrite H, H0. split. reflexivity. econstructor; eauto.
      + destruct b.
        * simpl in *. repeat normalize_sets. edestruct Henv. eapply Hinc. now left. eassumption.
          inv H.
          edestruct IHxs; eauto.
          { eapply Included_trans; [| eassumption ]; simpl. sets. }
          destructAll.
          eexists. rewrite H, H0. split. reflexivity. econstructor; eauto.

        * simpl in *. repeat normalize_sets.
          edestruct IHxs; eauto.
  Qed.


  Lemma live_args_length {A B} xs ys bs :
    length xs = length ys ->
    length (@live_args A xs bs) = length (@live_args B ys bs).
  Proof.
    revert ys bs. induction xs; intros; eauto.
    - destruct ys; try (simpl in * ; congruence).
      destruct bs; reflexivity.
    - simpl.
      destruct ys; try (simpl in * ; congruence). inv H.
      destruct bs. simpl. congruence.
      destruct b0; simpl; eauto.
  Qed.


  Lemma fun_inv_Eletapp L find_tag S k bs x f ft ys e ft' e' rho rho'
        (Henv : preord_env_P cenv PG (occurs_free (Eletapp x f ft ys e) \\ S \\ Dom_map L) k rho rho')
        (Hdis1 : Disjoint _ (Dom_map L) (FromList ys))
        (Hdis2 : Disjoint _ S (FromList (live_args ys bs)))
        (Hget : L ! f = Some bs)
        (Htag : find_tag f = Some ft')
        (Hinv : fun_inv L find_tag k rho rho')
        (Hexp : (forall (m : nat) (v1 v2 : val),
                    m < k ->
                    preord_val cenv PG m v1 v2 -> preord_exp cenv PL PG m (e, M.set x v1 rho) (e', M.set x v2 rho'))) :

    preord_exp cenv PL PG k (Eletapp x f ft ys e, rho) (Eletapp x f ft' (live_args ys bs) e', rho').
  Proof.
    intros v1 c1 t1 Hleq Hstep. inv Hstep.
    - eexists OOT, c1, zero. split; [| split; eauto ].
      + econstructor. eassumption.
      + eapply lt_one in H.
        subst. eapply HPost. eapply zero_one_lt.
      + simpl; eauto.
    - inv H.
      + edestruct (preord_env_P_get_list_live_args ys) with (bs := bs) as [vs' [Hgetl' Hprevs]]; eauto.
        eapply Included_Setminus; [| eapply Included_Setminus ]; sets.
        eapply Disjoint_Included_l. eapply live_args_subset. now sets.
        eapply Included_trans. eapply live_args_subset. normalize_occurs_free. sets.

        rewrite !to_nat_add in Hleq. unfold one in Hleq. rewrite to_nat_one in Hleq.
        destruct Hinv as [_ Hinv].

        edestruct Hinv with (j := k - 1) as (rhoc & rhoc' & B2 & f2 & xs2 & e2 & Hget2 & Hf2 & Hset & Hval).
        eassumption. eassumption. eassumption. eassumption. now eauto.

        erewrite <- List_util.Forall2_length with (l2 := vs'); [| eassumption ]. eapply live_args_length.
        eapply set_lists_length_eq. eassumption.

        edestruct Hval.
        lia.
        eapply List_util.Forall2_monotonic; [| eassumption ]. intros.
        eapply preord_val_monotonic. eassumption. lia.
        2:{ eassumption. } lia.
        destructAll.

        destruct x0; try contradiction.

        edestruct Hexp with (m := k - 1 - to_nat cin1) as (v2' & c2' & t2' & Hstep2' & Hpost' & Hval');
          [  | | | eassumption | ]. simpl in *.
        lia. simpl in H1. eassumption. lia.

        exists v2', (x1 <+> c2' <+> (one (Eletapp x f ft' (live_args ys bs) e'))). eexists.
        split; [| split ]; eauto.
        * econstructor 2.
          econstructor; try eassumption. now eauto.
        * simpl. eapply HPost. eassumption. eassumption. eassumption. eassumption. eassumption.
          eapply HGPost. eassumption. eassumption.
          eassumption.
        * eapply preord_res_monotonic. eassumption.
          rewrite !to_nat_add. unfold one. rewrite to_nat_one. lia.
      + edestruct (preord_env_P_get_list_live_args ys) with (bs := bs) as [vs' [Hgetl' Hprevs]]; eauto.
        eapply Included_Setminus; [| eapply Included_Setminus ]; sets.
        eapply Disjoint_Included_l. eapply live_args_subset. now sets.
        eapply Included_trans. eapply live_args_subset. normalize_occurs_free. sets.

        rewrite !to_nat_add in Hleq. unfold one in Hleq. rewrite to_nat_one in Hleq.
        destruct Hinv as [_ Hinv].
        edestruct Hinv with (j := k - 1) as (rhoc & rhoc' & B2 & f2 & xs2 & e2 & Hget2 & Hf2 & Hset & Hval).
        eassumption. eassumption. eassumption. now eauto. now eauto.
        erewrite <- List_util.Forall2_length with (l2 := vs'); [| eassumption ]. eapply live_args_length.
        eapply set_lists_length_eq. eassumption.

        edestruct Hval.
        lia.
        eapply List_util.Forall2_monotonic; [| eassumption ]. intros.
        eapply preord_val_monotonic. eassumption. lia.
        2:{ eassumption. } lia.
        destructAll.

        destruct x0; try contradiction.

        exists OOT, (x1 <+> (one (Eletapp x f ft' (live_args ys bs) e'))). eexists.
        split; [| split ]; eauto.
        * econstructor 2.
          econstructor; try eassumption. now eauto.
        * simpl. eapply HPost. eassumption. eassumption. eassumption. eassumption.
          eapply HGPost. eassumption. eassumption.
  Qed.


  Lemma fun_inv_Eapp L find_tag S k bs f ft ys ft' rho rho'
        (Henv : preord_env_P cenv PG (occurs_free (Eapp f ft ys) \\ S \\ Dom_map L) k rho rho')
        (Hdis1 : Disjoint _ (Dom_map L) (FromList ys))
        (Hdis2 : Disjoint _ S (FromList (live_args ys bs)))
        (Hget : L ! f = Some bs)
        (Htag : find_tag f = Some ft')
        (Hinv : fun_inv L find_tag k rho rho') :

    preord_exp cenv PL PG k (Eapp f ft ys, rho) (Eapp f ft' (live_args ys bs), rho').
  Proof.
    intros v1 c1 t1 Hleq Hstep. inv Hstep.
    - eexists OOT, c1, zero. split; [| split; eauto ].
      + econstructor. eassumption.
      + eapply lt_one in H.
        subst. eapply HPost. eapply zero_one_lt.
      + simpl; eauto.
    - inv H. edestruct (preord_env_P_get_list_live_args ys) with (bs := bs) as [vs' [Hgetl' Hprevs]]; eauto.
      eapply Included_Setminus; [| eapply Included_Setminus ]; sets.
      eapply Disjoint_Included_l. eapply live_args_subset. now sets.
      eapply Included_trans. eapply live_args_subset. normalize_occurs_free. sets.

      rewrite !to_nat_add in Hleq. unfold one in Hleq. rewrite to_nat_one in Hleq.

      destruct Hinv as [_ Hinv].
      edestruct Hinv with (j := k - 1) as (rhoc & rhoc' & B2 & f2 & xs2 & e2 & Hget2 & Hf2 & Hset & Hval).
      eassumption. eassumption. eassumption. now eauto. now eauto.
      erewrite <- List_util.Forall2_length with (l2 := vs'); [| eassumption ]. eapply live_args_length.
      eapply set_lists_length_eq. eassumption.

      edestruct Hval.
      lia.
      eapply List_util.Forall2_monotonic; [| eassumption ]. intros.
      eapply preord_val_monotonic. eassumption. lia.
      2:{ eassumption. } lia.
      destructAll.

      do 3 eexists.
      split; [| split ]; eauto.
      * econstructor 2.
        econstructor; try eassumption. now eauto.
      * simpl. eapply HPost; eauto. eapply HGPost. eassumption. eassumption.
      * eapply preord_res_monotonic. eassumption.
        rewrite !to_nat_add. unfold one. rewrite to_nat_one. lia.
  Qed.


  Lemma Elim_expr_correct :
    forall k e e' L find_tag S rho1 rho2
           (Hdis1 : Disjoint _ (Dom_map L) (bound_var e))

           (Hd : Dead S L e)
           (Hk : Known_exp (Dom_map L) e)

           (Hfinv : fun_inv L find_tag k rho1 rho2)

           (Henv : preord_env_P cenv PG (occurs_free e \\ S \\ Dom_map L) k rho1 rho2)

           (Helim : Elim_expr L find_tag e e'),

      preord_exp cenv PL PG k (e, rho1) (e', rho2).
  Proof.
    induction k as [k IHk] using lt_wf_rec1. intros e.
    revert k IHk; induction e using exp_ind'; intros; inv Helim; inv Hd; inv Hk; try congruence.
    (* Constr *)
    - eapply preord_exp_constr_compat.
      + now eapply HPost.
      + now eapply HPost.
      + rewrite <- (map_id l) at 2. eapply Forall2_preord_var_env_map. now eauto.
        normalize_occurs_free. sets.
      + intros. eapply IHk; eauto.

        * repeat normalize_bound_var_in_ctx. sets.
        * eapply fun_inv_set_Disjoint. eapply fun_inv_monotonic. eassumption. lia.
          repeat normalize_occurs_free_in_ctx. sets.
        * eapply preord_env_P_extend.
          eapply preord_env_P_antimon.
          eapply preord_env_P_monotonic; [| eassumption ]. lia.
          normalize_occurs_free. sets. rewrite !Setminus_Union_distr, !Setminus_Union. now sets.
          rewrite preord_val_eq. simpl. split; eauto.

    - (* Ecase nil *)
      inv H2.
      eapply preord_exp_case_nil_compat. now eapply HPost.

    - (* Ecase cons *)
      inv H2. inv H0. inv H3. destructAll. destruct y. simpl in H; subst.
      eapply preord_exp_case_cons_compat_alt.
      + now eapply HPost.
      + now eapply HPost.
      + now eapply HPost.
      + eapply List_util.Forall2_monotonic; [| eassumption ].
        intros [? ?] [? ?]. simpl; intros [? ?]; eauto.
      + intros Heq. destructAll. eapply Henv.
        constructor. constructor. normalize_occurs_free. now sets.
        eassumption.
        intros Hc. eapply Hfinv in Hc. destructAll. congruence.
      + intros. eapply IHe; eauto.
        * intros; eauto. eapply IHk; eauto. lia.
        * repeat normalize_bound_var_in_ctx. sets.
        * eapply fun_inv_monotonic; eauto. lia.
        * eapply preord_env_P_antimon.
          eapply preord_env_P_monotonic; [| eassumption ]. lia.
          normalize_occurs_free. sets.

      + eapply IHe0; eauto.
        * repeat normalize_bound_var_in_ctx. sets.
        * constructor; eauto.
        * constructor; eauto.
        * eapply preord_env_P_antimon.
          eapply preord_env_P_monotonic; [| eassumption ]. lia.
          normalize_occurs_free. sets.
        * econstructor. eauto.

    (* Proj *)
    - eapply preord_exp_proj_compat.
      + now eapply HPost.
      + now eapply HPost.
      + eapply Henv.
        eapply Included_Setminus with (s1 := [set v0]). now sets.
        eapply Included_Setminus with (s1 := [set v0]). now sets.
        normalize_occurs_free. now sets.
        reflexivity.
      + intros. eapply IHk; eauto.

        * repeat normalize_bound_var_in_ctx. sets.
        * eapply fun_inv_set_Disjoint. eapply fun_inv_monotonic; eauto. lia.
          repeat normalize_occurs_free_in_ctx. sets.
        * eapply preord_env_P_extend.
          eapply preord_env_P_antimon.
          eapply preord_env_P_monotonic; [| eassumption ]. lia.
          normalize_occurs_free. sets. rewrite !Setminus_Union_distr, !Setminus_Union. now sets.
          eassumption.

    - (* Eletapp None *)
      eapply preord_exp_letapp_compat.
      + now eapply HPost.
      + now eapply HPost.
      + now eapply HPost.
      + eapply Henv.
        econstructor.
        2:{ intros Hin. inv Hin. congruence. }
        eapply Included_Setminus with (s1 := [set f]). now sets.
        normalize_occurs_free. now sets.
        reflexivity.
      + rewrite <- (map_id ys) at 2. eapply Forall2_preord_var_env_map. now eauto.
        normalize_occurs_free. sets.
      + intros. eapply IHk; eauto.

        * repeat normalize_bound_var_in_ctx. sets.
        * eapply fun_inv_set_Disjoint.
          eapply fun_inv_monotonic; eauto. lia.
          repeat normalize_occurs_free_in_ctx. sets.
        * eapply preord_env_P_extend.
          eapply preord_env_P_antimon.
          eapply preord_env_P_monotonic; [| eassumption ]. lia.
          normalize_occurs_free. sets. rewrite !Setminus_Union_distr, !Setminus_Union. now sets.
          eassumption.

    - (* Eletapp Some *)
      repeat subst_exp.
      eapply fun_inv_Eletapp.

      + eassumption.
      + sets.
      + sets.
      + eassumption.
      + eassumption.
      + eassumption.
      + intros. eapply IHk; eauto.

        * repeat normalize_bound_var_in_ctx. sets.
        * eapply fun_inv_set_Disjoint.
          eapply fun_inv_monotonic; eauto. lia.
          repeat normalize_occurs_free_in_ctx. sets.
        * eapply preord_env_P_extend.
          eapply preord_env_P_antimon.
          eapply preord_env_P_monotonic; [| eassumption ]. lia.
          normalize_occurs_free. sets. rewrite !Setminus_Union_distr, !Setminus_Union. now sets.
          eassumption.


    - (* Eapp None *)
      eapply preord_exp_app_compat.
      + now eapply HPost.
      + now eapply HPost.
      + eapply Henv.
        econstructor.
        2:{ intros Hin. inv Hin. congruence. }
        eapply Included_Setminus with (s1 := [set v]). now sets.
        normalize_occurs_free. now sets.
        reflexivity.
      + rewrite <- (map_id l) at 2. eapply Forall2_preord_var_env_map. now eauto.
        normalize_occurs_free. sets.

    - (* Eapp Some *)
      repeat subst_exp.
      eapply fun_inv_Eapp.

      + eassumption.
      + sets.
      + sets.
      + eassumption.
      + eassumption.
      + eassumption.

    - (* Eprim_val *)
      eapply preord_exp_prim_val_compat.
      + eapply HPost.

    - (* Eprim *)
      eapply preord_exp_prim_compat.
      + eapply HPost.
      + rewrite <- (map_id l) at 2. eapply Forall2_preord_var_env_map. now eauto.
        normalize_occurs_free. sets.

    - (* Ehalt *)
      eapply preord_exp_halt_compat.
      + eapply HPost.
      + eapply HPost.
      + eapply Henv.
        eapply Included_Setminus with (s1 := [set v]). now sets.
        eapply Included_Setminus with (s1 := [set v]). now sets.
        normalize_occurs_free. now sets.
        reflexivity.
  Qed.


  Lemma Known_fundefs_fun_in_fundefs S B f ft xs e:
    Known_fundefs S B ->
    fun_in_fundefs B (f, ft, xs, e) ->
    Known_exp S e.
  Proof.
    intros Hd Hf. induction Hd; inv Hf; eauto.
    inv H0; eauto.
  Qed.

  Lemma no_fun_in_fundefs B f ft xs e:
    no_fun_defs B ->
    fun_in_fundefs B (f, ft, xs, e) ->
    no_fun e.
  Proof.
    intros Hd Hf. induction Hd; inv Hf; eauto.
    inv H0; eauto.
  Qed.

  Lemma dead_args_nil xs :
    dead_args xs [] = [].
  Proof.
    induction xs; eauto.
  Qed.

  Lemma Dead_empty L e :
    no_fun e ->
    Dead (Empty_set var) L e.
  Proof.
    induction e using exp_ind'; intros Hnf; inv Hnf; try (now econstructor; sets; eauto).
    - econstructor; sets.
      specialize (IHe0 H1). inv IHe0. econstructor; eauto.
    - destruct (L ! f) eqn:Heq.
      + eapply Live_LetApp_Known; eauto; sets.
      + eapply Live_LetApp_Unknown; eauto; sets.
    - destruct (L ! v) eqn:Heq.
      + eapply Live_App_Known; eauto; sets.
      + eapply Live_App_Unknown; eauto; sets.
  Qed.

  Lemma preord_env_P_set_lists_live:
    forall (xs1 : list var) (P : Ensemble var) (rho1 rho2 rho1' rho2' : env)
           (k : nat) (vs1 vs2 : list val) bs,
      preord_env_P cenv PG (P \\ FromList xs1) k rho1 rho2 ->
      Forall2 (preord_val cenv PG k) (live_args vs1 bs) vs2 ->
      set_lists xs1 vs1 rho1 = Some rho1' ->
      set_lists (live_args xs1 bs) vs2 rho2 = Some rho2' ->
      preord_env_P cenv PG (P \\ FromList (dead_args xs1 bs)) k rho1' rho2'.
  Proof.
    induction xs1; intros P rho1 rho2 rho1' rho2' k vs1 vs2 bs Henv Hall Hs1 Hs2.
    + destruct vs1; destruct vs2; destruct bs; simpl in *; try congruence.
      inv Hs1. inv Hs2. eassumption.
      inv Hs1. inv Hs2. eassumption.
    + destruct bs.
      { rewrite dead_args_nil in *. rewrite live_args_nil in Hall.
        rewrite live_args_nil in Hs2.
        normalize_sets.
        eapply preord_env_P_set_lists_l; eauto.
        intros. constructor; eauto. inv H0; eauto. }

      simpl in *. destruct vs1; try congruence.
      destruct (set_lists xs1 vs1 rho1) eqn:Hs1'; try congruence.
      inv Hs1.
      destruct b.

      * simpl in *. destruct vs2; try congruence.
        destruct (set_lists (live_args xs1 bs) vs2 rho2) eqn:Hs2'; try congruence.
        inv Hs2.

        inv Hall. eapply preord_env_P_extend; eauto.

        rewrite Setminus_Union. rewrite Union_commut, <- Setminus_Union.
        eapply IHxs1; eauto.
        rewrite Setminus_Union. repeat normalize_sets. eassumption.

      * eapply preord_env_P_set_not_in_P_l.

        normalize_sets. rewrite <- Setminus_Union.
        eapply IHxs1; eauto.
        rewrite Setminus_Union. repeat normalize_sets. eassumption.

        normalize_sets. sets.
  Qed.


  Lemma Elim_fundefs_correct :
    forall k B B' S L find_tag rho1 rho2
           (Hun : unique_bindings_fundefs B)
           (Hnf : no_fun_defs B)

           (Hdis1 : Disjoint _ (Dom_map L) (bound_var_fundefs B \\ name_in_fundefs B))
           (Hdom : Dom_map L \subset name_in_fundefs B)

           (Hd : live_map_sound B L)
           (Hk : Known_fundefs (Dom_map L) B)

           (Henv : preord_env_P cenv PG (occurs_free_fundefs B :|: S \\ Dom_map L) k rho1 rho2)

           (Helim : Elim_fundefs L find_tag B B'),

      fun_inv L find_tag k (def_funs B B rho1 rho1) (def_funs B' B' rho2 rho2) /\
      preord_env_P cenv PG ((name_in_fundefs B :|: occurs_free_fundefs B :|: S) \\ Dom_map L) k
                   (def_funs B B rho1 rho1) (def_funs B' B' rho2 rho2).
  Proof with now eauto with Ensembles_DB.
    induction k as [k IHk] using lt_wf_rec1; intros. split.

    - split.
      + intro; intros. eapply Hdom in H. do 3 eexists. rewrite def_funs_eq. reflexivity. eassumption.
      + intro; intros.
        rewrite def_funs_eq in H1. 2:{ eapply Hdom. eexists; eauto. }

        inv H1.
        edestruct Elim_fundefs_exists_Some; try eassumption. eapply find_def_correct. eassumption.
        destructAll.

        rewrite def_funs_eq; eauto.
        2:{ eapply Elim_fundefs_name_in_fundefs with (B := B1) (B' := B'). eassumption. eapply Hdom. eexists; eauto. }
        repeat subst_exp.

        edestruct (@set_lists_length3 val) with (xs := live_args xs1 bs) (vs := vs2) (rho := def_funs B' B' rho2 rho2).
        rewrite <- H4. reflexivity.

        assert (Hand : forall m, m < k ->
                                 fun_inv L find_tag m (def_funs B1 B1 rho0 rho0) (def_funs B' B' rho2 rho2) /\
                                 preord_env_P cenv PG
                                              (name_in_fundefs B1 :|: occurs_free_fundefs B1 :|: S \\ Dom_map L) m
                                              (def_funs B1 B1 rho0 rho0) (def_funs B' B' rho2 rho2)).
        { intros. eapply IHk; try eassumption.
          eapply preord_env_P_monotonic; [| eassumption ]. lia. }

        do 6 eexists. repeat split.
        * eapply find_def_complete.
          eapply unique_bindings_fundefs_unique_functions.
          eapply Elim_fundefs_unique_bindings. eassumption. eassumption.
          eassumption.
        * now eauto.
        * intros.
          edestruct (Hand j) as [Hinv' Henv']. lia.

          eapply Elim_expr_correct; try eassumption.
          -- repeat normalize_bound_var_in_ctx. sets.
             eapply Disjoint_Included_r; [| eassumption ].
             eapply Included_Setminus.
             eapply unique_bindings_fun_in_fundefs. eapply find_def_correct. eassumption. eassumption.
             eapply Included_trans;
               [| eapply fun_in_fundefs_bound_var_fundefs; eapply find_def_correct; eassumption ].
             now sets.
          -- eapply Hd. eapply find_def_correct. eassumption. eassumption.
          -- eapply Known_fundefs_fun_in_fundefs. eassumption. eapply find_def_correct. eassumption.
          -- assert (Hdis :  Disjoint map_util.M.elt (FromList xs1) (Dom_map L)).
             { eapply Disjoint_sym.
               eapply Disjoint_Included_r; [| eassumption ].
               eapply Included_Setminus.
               eapply unique_bindings_fun_in_fundefs. eapply find_def_correct. eassumption. eassumption.
               eapply Included_trans;
                 [| eapply fun_in_fundefs_bound_var_fundefs; eapply find_def_correct; eassumption ].
             now sets. }
             eapply fun_inv_set_lists_Disjoint_l; eauto; sets.
             eapply fun_inv_set_lists_Disjoint_r; [| | now eauto ].
             eassumption.
             eapply Disjoint_Included_l. eapply live_args_subset. sets.
          -- rewrite Setminus_Union. rewrite Union_commut, <- Setminus_Union.
             eapply preord_env_P_set_lists_live; eauto.
             eapply preord_env_P_antimon. eassumption.
             rewrite Setminus_Union. rewrite Union_commut, <- Setminus_Union.
             eapply Included_Setminus_compat. eapply Setminus_Included_Included_Union.
             eapply Included_trans. eapply occurs_free_in_fun.
             eapply find_def_correct. eassumption. sets. reflexivity.

    - intros x Hinx v Hgetx. destruct (Decidable_name_in_fundefs B).
      destruct (Dec x).
      + rewrite def_funs_eq in Hgetx; eauto. inv Hgetx.
        edestruct name_in_fundefs_find_def_is_Some. eassumption. destructAll.
        inv Hinx.

        assert (Heq: L ! x = None).
        { destruct (L ! x) eqn:Het; eauto. exfalso. eapply H1. eexists. eassumption. }

        edestruct Elim_fundefs_exists_None; try eassumption. eapply find_def_correct. eassumption.
        destructAll.

        eexists. split.
        * rewrite def_funs_eq. reflexivity.
          eapply Elim_fundefs_name_in_fundefs with (B := B); eassumption.

        * rewrite preord_val_eq. intro; intros. repeat subst_exp.

          edestruct (@set_lists_length3 val) with (xs := xs1) (vs := vs2) (rho := def_funs B' B' rho2 rho2).
          rewrite <- H4. eapply set_lists_length_eq. now eauto.

          assert (Hand : forall m, m < k ->
                                   fun_inv L find_tag m (def_funs B B rho1 rho1) (def_funs B' B' rho2 rho2) /\
                                   preord_env_P cenv PG
                                                (name_in_fundefs B :|: occurs_free_fundefs B :|: S \\ Dom_map L) m
                                                (def_funs B B rho1 rho1) (def_funs B' B' rho2 rho2)).
          { intros. eapply IHk; try eassumption.
            eapply preord_env_P_monotonic; [| eassumption ]. lia. }


          do 3 eexists. repeat split.
          -- eapply find_def_complete.
             eapply unique_bindings_fundefs_unique_functions.
             eapply Elim_fundefs_unique_bindings. eassumption. eassumption.
             eassumption.
          -- now eauto.
          -- intros.
             edestruct (Hand j) as [Hinv' Henv']. lia.

             { eapply preord_exp_post_monotonic. eapply HGPost. eassumption.
               eapply Elim_expr_correct with (S := Empty_set _); try eassumption.
               - repeat normalize_bound_var_in_ctx. sets.
                 eapply Disjoint_Included_r; [| eassumption ].
                 eapply Included_Setminus.
                 eapply unique_bindings_fun_in_fundefs. eapply find_def_correct. eassumption. eassumption.
                 eapply Included_trans;
                   [| eapply fun_in_fundefs_bound_var_fundefs; eapply find_def_correct; eassumption ].
                 now sets.
               - eapply Dead_empty. eapply no_fun_in_fundefs. eassumption.
                 eapply find_def_correct. eassumption.
               - eapply Known_fundefs_fun_in_fundefs. eassumption. eapply find_def_correct. eassumption.
               - assert (Hdis :  Disjoint map_util.M.elt (FromList xs1) (Dom_map L)).
                 { eapply Disjoint_sym.
                   eapply Disjoint_Included_r; [| eassumption ].
                   eapply Included_Setminus.
                   eapply unique_bindings_fun_in_fundefs. eapply find_def_correct. eassumption. eassumption.
                   eapply Included_trans;
                     [| eapply fun_in_fundefs_bound_var_fundefs; eapply find_def_correct; eassumption ].
                   now sets. }
                 eapply fun_inv_set_lists_Disjoint_l; eauto; sets.
                 eapply fun_inv_set_lists_Disjoint_r; [| | now eauto ]; sets.
               - normalize_sets.
                 eapply preord_env_P_set_lists_l; eauto.

                 intros. inv H10. eapply occurs_free_in_fun in H11; [| eapply find_def_correct; eassumption ].
                 constructor; eauto. inv H11; eauto. exfalso; eauto. }

      + rewrite def_funs_neq in Hgetx; eauto. rewrite def_funs_neq.
        2:{ intros Hc. eapply n. eapply Elim_fundefs_name_in_fundefs in Hc; eauto. }
        eapply Henv; eauto. inv Hinx. inv H; eauto. inv H1; eauto.
        now exfalso; eauto. constructor; eauto.
        constructor; eauto.
  Qed.


  Lemma create_fun_tag_dom_subset L am B (c c' : comp_data) (fm fm' : ftagMap) :
    create_fun_tag L am B c fm = (fm', c') ->
    Dom_map fm \subset Dom_map fm'.
  Proof.
    revert c c' fm fm'.
    induction B; intros c c' fm fm' Hcr; simpl in *; sets.

    - unfold get_fun_vars in *.

      destruct (L ! v) eqn:Hget.

      + destruct (am ! (Positive_as_DT.of_succ_nat (Datatypes.length (live_args l l0)))).
        eapply Included_trans; [| eapply IHB; eauto ].
        rewrite Dom_map_set. sets.

        destruct (dead_param_elim.make_ftag (Datatypes.length (live_args l l0)) c).
        eapply Included_trans; [| eapply IHB; eauto ].
        rewrite Dom_map_set. sets.

      + eauto.

    - inv Hcr. sets.
  Qed.



  Lemma create_fun_tag_dom L am B (c c' : comp_data) (fm fm' : ftagMap) :
    create_fun_tag L am B c fm = (fm', c') ->
    Dom_map L :&: name_in_fundefs B \subset Dom_map fm'.
  Proof.
    revert c c' fm fm'.
    induction B; intros c c' fm fm' Hcr; simpl in *; sets.

    - unfold get_fun_vars in *.

      destruct (L ! v) eqn:Hget.

      + destruct (am ! (Positive_as_DT.of_succ_nat (Datatypes.length (live_args l l0)))).
        * rewrite Intersection_commut, Intersection_Union_distr.
          eapply Union_Included; eauto.
          2:{ rewrite Intersection_commut. eauto. }

          eapply create_fun_tag_dom_subset in Hcr.
          eapply Included_trans. eapply Included_Intersection_l.
          eapply Included_trans; [| eassumption ].
          rewrite Dom_map_set. sets.

        * destruct (dead_param_elim.make_ftag (Datatypes.length (live_args l l0)) c).
          rewrite Intersection_commut, Intersection_Union_distr.
          eapply Union_Included; eauto.
          2:{ rewrite Intersection_commut. eauto. }

          eapply create_fun_tag_dom_subset in Hcr.
          eapply Included_trans. eapply Included_Intersection_l.
          eapply Included_trans; [| eassumption ].
          rewrite Dom_map_set. sets.

      + rewrite Intersection_commut. rewrite Union_commut.
        rewrite closure_conversion_util.Intersection_Union_Disjoint.
        rewrite Intersection_commut. eapply IHB. eassumption.
        eapply Disjoint_Singleton_l. intros Hc. inv Hc. congruence.

    - rewrite Intersection_Empty_set_abs_r. sets.
  Qed.

  Lemma create_fun_tag_next_var L am B (c c' : comp_data) (fm fm' : ftagMap) :
    create_fun_tag L am B c fm = (fm', c') ->
    next_var c = next_var c'.
  Proof.
    revert c c' fm fm'.
    induction B; intros c c' fm fm' Hcr; simpl in *; eauto.

    - unfold get_fun_vars in *.

      destruct (L ! v) eqn:Hget.

      + destruct (am ! (Positive_as_DT.of_succ_nat (Datatypes.length (live_args l l0)))).
        * eapply IHB. eassumption.
        * destruct (dead_param_elim.make_ftag (Datatypes.length (live_args l l0)) c) eqn:Ht.

          unfold dead_param_elim.make_ftag in *. destruct c. inv Ht. simpl.
          eapply IHB in Hcr. simpl in *. eassumption.

      + eapply IHB. eassumption.

    - inv Hcr. reflexivity.
  Qed.


  (* TODO move *)

  Lemma max_var_le e e' :
    bound_var e :|: occurs_free e \subset bound_var e' :|: occurs_free e' ->
    (max_var e 1 <= max_var e' 1)%positive.
  Proof.
    intros Hin.
    assert (Hin' := max_var_subset e).
    eapply Hin in Hin'.
    inv Hin'.
    eapply bound_var_leq_max_var. eassumption.
    eapply occurs_free_leq_max_var. eassumption.
  Qed.


  Lemma DPE_correct_top  (e : exp) (c : comp_data) :
    unique_bindings e ->
    (max_var e 1%positive < next_var c)%positive ->
    Disjoint _ (bound_var e) (occurs_free e) ->
    exists e' c',
      DPE e c = (Ret e', c') /\
      unique_bindings e' /\
      occurs_free e' \subset occurs_free e /\
      Disjoint _ (bound_var e') (occurs_free e') /\
      (max_var e' 1%positive < next_var c')%positive /\
      (forall k rho1 rho2,
          preord_env_P cenv PG (occurs_free e) k rho1 rho2 ->
          binding_in_map (occurs_free e) rho1 ->
          preord_exp cenv PL PG k (e, rho1) (e', rho2)).
  Proof.
    intros Hun Hleq Hdis. unfold DPE.

    (* identity case *)
    assert (Hid :
              forall s, exists (e' : exp) (c' : comp_data),
                  (Ret e, add_log s c) = (Ret e', c') /\
                  unique_bindings e' /\
                  occurs_free e' \subset occurs_free e /\
                  Disjoint var (bound_var e') (occurs_free e') /\
                  (max_var e' 1 < next_var c')%positive /\
                  (forall (k : nat) (rho1 rho2 : env),
                      preord_env_P cenv PG (occurs_free e) k rho1 rho2 ->
                      binding_in_map (occurs_free e) rho1 -> preord_exp' cenv (preord_val cenv) PL PG k (e, rho1) (e', rho2))).
    { do 2 eexists. split; [| split; [| split; [| split; [| split ] ]]]; eauto; sets.
      now destruct c; eauto.
      intros. eapply preord_exp_refl; eauto. }

    assert (Hid' :
              exists (e' : exp) (c' : comp_data),
                  (Ret e, c) = (Ret e', c') /\
                  unique_bindings e' /\
                  occurs_free e' \subset occurs_free e /\
                  Disjoint var (bound_var e') (occurs_free e') /\
                  (max_var e' 1 < next_var c')%positive /\
                  (forall (k : nat) (rho1 rho2 : env),
                      preord_env_P cenv PG (occurs_free e) k rho1 rho2 ->
                      binding_in_map (occurs_free e) rho1 -> preord_exp' cenv (preord_val cenv) PL PG k (e, rho1) (e', rho2))).
    { do 2 eexists. split; [| split; [| split; [| split; [| split ] ]]]; eauto; sets.
      intros. eapply preord_exp_refl; eauto. }

    destruct (is_hoisted e) eqn:Hhoist; [ | now eauto ].

    destruct e;  try now eauto.
    destruct (find_live (Efun f e)) as [ L |  ] eqn:Hlive; [ now eauto | ].
    destruct (create_fun_tag l (make_arityMap (Efun f e) (M.empty fun_tag)) f c (M.empty fun_tag)) eqn:Hfmap.

    (* something actually happens *)
    edestruct is_hoisted_correct. eassumption. destructAll.

    edestruct find_live_sound_top. eassumption.
    eapply unique_bindings_fundefs_unique_functions. inv Hun. eassumption. eassumption.

    destructAll.

    assert (Hceq := create_fun_tag_next_var _ _ _ _ _ _ _ Hfmap). rewrite Hceq in *.

    eapply create_fun_tag_dom in Hfmap.
    rewrite Intersection_Same_set in Hfmap; [| eassumption ].


    unfold run_compM.

    assert (Hsb := eliminate_fundefs_sound f0 l Hfmap f H tt (c0, tt) I).
    destruct (compM.runState (eliminate_fundefs f0 l f) tt (c0, tt)) as [[ B' | ] c1].
    contradiction.  destructAll.

    assert (Hse := eliminate_expr_sound f0 l Hfmap e H0 tt (c0, tt) I).
    destruct (compM.runState (eliminate_expr f0 l e) tt (c0, tt)) as [[ e' | ] c2].
    contradiction. destructAll.

    (* bound_var *)
    assert (Hbe := Elim_exp_bound_var _ _ _ _ H12).
    assert (Hbf := Elim_fundefs_bound_var _ _ _ _ H11).
    (* unique bindings *)
    inv Hun.
    assert (Hue := Elim_exp_unique_bindings _ _ _ _ H12 H14).
    assert (Huf := Elim_fundefs_unique_bindings _ _ _ _ H11 H15).
    (* free vars *)
    assert (Hfve := Elim_exp_occurs_free _ _ _ _ H12).
    assert (Hfvf := Elim_fundefs_occurs_free _ _ _ _ H11 H7).


    do 2 eexists.  split; [| split; [| split; [| split; [| split ] ]]].
    - reflexivity.
    - econstructor; eauto.
      eapply Disjoint_Included. eassumption. eassumption. sets.
    - repeat normalize_occurs_free.
      rewrite Elim_fundefs_name_in_fundefs with (B := f); eauto. sets.
    - eapply Disjoint_Included; [| | eapply Hdis ].
      + repeat normalize_occurs_free.
        rewrite Elim_fundefs_name_in_fundefs with (B := f); eauto.
        sets.
      + repeat normalize_bound_var. sets.
    - eapply Pos.le_lt_trans; [| eassumption ]. eapply max_var_le.
      repeat normalize_occurs_free. repeat normalize_bound_var.
      rewrite Elim_fundefs_name_in_fundefs with (B := f); eauto. sets.

    - (* Semantic correctness *)
      intros k rho1 rho2 Henv Hbin.
      inv H9.

      eapply Elim_fundefs_correct in H11; try eauto.
      2:{ sets. }
      2:{ eapply preord_env_P_antimon. eassumption. normalize_occurs_free. sets. }
      destructAll.

      eapply preord_exp_fun_compat.
      + eapply HPost.
      + eapply HPost.
      + eapply Elim_expr_correct; try eassumption.
        * eapply Disjoint_Included_l.
          eapply Included_trans. eassumption.
          eapply name_in_fundefs_bound_var_fundefs. sets.
        * eapply Dead_empty. eassumption.
        * eapply fun_inv_monotonic. eassumption. lia.
        * eapply preord_env_P_antimon.
          eapply preord_env_P_monotonic; [| eassumption ]. lia.
          repeat normalize_sets. eapply Included_Setminus_compat; sets.
          rewrite Union_Setminus_Included; sets. tci.
  Qed.

End Correct.
