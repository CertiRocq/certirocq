Require Import LambdaANF.term LambdaANF.identifiers LambdaANF.ctx LambdaANF.set_util LambdaANF.state
        LambdaANF.dead_param_elim LambdaANF.Ensembles_util LambdaANF.tactics LambdaANF.map_util
        LambdaANF.hoisting.
Require Import compcert.lib.Coqlib Common.compM Common.Pipeline_utils.
From Stdlib Require Import Lists.List MSets.MSets MSets.MSetRBT Numbers.BinNums
        NArith.BinNat PArith.BinPos Sets.Ensembles micromega.Lia.
Require Import maps_util.
Require Import ExtLib.Structures.Monads ExtLib.Data.Monads.StateMonad.
Import ListNotations Nnat.


Import MonadNotation.
Open Scope monad_scope.

Open Scope ctx_scope.
Open Scope fun_scope.
Close Scope Z_scope.


Inductive Dead_in_args (S : Ensemble var) : list var -> list bool -> Prop :=
| Live_nil : Dead_in_args S [] []
| ALive_cons_Dead :
    forall (x : var) (xs : list var) (bs: list bool),
      Dead_in_args S xs bs ->
      Dead_in_args S (x :: xs) (false :: bs)
| ALive_cons_Live :
    forall (x : var) (xs : list var) (bs: list bool),
      Dead_in_args S xs bs ->
      ~ x \in S ->
      Dead_in_args S (x :: xs) (true :: bs).


Fixpoint dead_args (ys : list var) (bs : list bool) : list var :=
  match ys, bs with
  | [], [] => ys
  | y :: ys', b :: bs' =>
    if b then (dead_args ys' bs')
    else y :: dead_args ys' bs'
| _, _ => []
end.

Inductive Dead (S : Ensemble var) (L : live_fun) : exp -> Prop :=
| Live_Constr :
    forall (x : var) (ys : list var) (ct : ctor_tag) (e : exp),
      Disjoint _ (FromList ys) S ->
      Dead S L e ->
      Dead S L (Econstr x ct ys e)
| Live_Prim_val :
  forall (x : var) p (e : exp),
    Dead S L e ->
    Dead S L (Eprim_val x p e)
| Live_Prim :
  forall (x : var) (g : prim) (ys : list var) (e : exp),
    Disjoint _ (FromList ys) S ->
    Dead S L e ->
    Dead S L (Eprim x g ys e)
| Live_Proj :
    forall (x : var) (ct : ctor_tag) (n : N) (y : var) (e : exp),
      ~ y \in S ->
     Dead S L e ->
     Dead S L (Eproj x ct n y e)
| Live_Case:
    forall (x : var) (ce : list (ctor_tag * exp)),
      ~ x \in S ->
      Forall (fun p => Dead S L (snd p)) ce ->
      Dead S L (Ecase x ce)
| Live_Halt :
    forall (x : var),
      ~ x \in S ->
      Dead S L (Ehalt x)
| Live_App_Unknown :
    forall (f : var) (ys : list var) (ft : fun_tag),
      ~ f \in S ->
      Disjoint _ (FromList ys) S ->
      L ! f = None ->
      Dead S L (Eapp f ft ys)
| Live_App_Known :
    forall (f : var) (ys : list var) (ft : fun_tag) (bs : list bool),
      L ! f = Some bs ->
      ~ f \in S ->
      Disjoint _ S (FromList (live_args ys bs)) ->
      Dead S L (Eapp f ft ys)
| Live_LetApp_Unknown :
    forall (x f : var) (ys : list var) (ft : fun_tag) (e : exp),
      ~ f \in S ->
      Disjoint _ (FromList ys) S ->
      L ! f = None ->
      Dead S L e ->
      Dead S L (Eletapp x f ft ys e)
| Live_LetApp_Known :
    forall (x f : var) (ys : list var) (ft : fun_tag) (e : exp) (bs : list bool),
      L ! f = Some bs ->
      ~ f \in S ->
      Disjoint _ S (FromList (live_args ys bs)) ->
      Dead S L e ->
      Dead S L (Eletapp x f ft ys e).


Definition live_map_sound (B : fundefs) (L : live_fun) :=
  forall f ft xs e bs,
    fun_in_fundefs B (f, ft, xs, e) ->
    L ! f = Some bs ->
    Dead (FromList (dead_args xs bs)) L e.

Definition live_fun_args (L : live_fun) (f : var) (xs : list var) :=
  exists bs, L ! f = Some bs /\ length xs = length bs.

Definition live_fun_consistent (L : live_fun) (B : fundefs) :=
  forall f ft xs e,
    fun_in_fundefs B (f, ft, xs, e) ->
    live_fun_args L f xs.

(* Lemmas about [live] *)

Lemma live_diff B L L' d :
  live B L d = (L', false) ->
  d = false.
Proof.
  revert L L' d. induction B; simpl; intros L L' d Hl; eauto.
  - destruct (update_live_fun L v l (live_expr L e PS.empty)) as [L'' d''].
    eapply IHB in Hl. destruct d; eauto. destruct d''; eauto.
  - inv Hl; eauto.
Qed.

Lemma update_live_fun_false L L' f xs S :
  update_live_fun L f xs S = (L', false) ->
  L = L' /\
  (forall bs,
      get_fun_vars L f = Some bs ->
      Disjoint _ (FromSet S) (FromList (dead_args xs bs))).
Proof.
  intros Hl.
  unfold update_live_fun in Hl.
  destruct (get_fun_vars L f) eqn:Hf.
  - unfold get_fun_vars in *.
    destruct (update_bs S xs l) as [bs diff] eqn:Hupd.
    inv Hl.
    destruct diff. congruence. inv H0.
    split. reflexivity.
    intros bs' Hget. inv Hget.

    assert (Hsuff : Disjoint  positive (FromSet S) (FromList (dead_args xs bs'))).
    { clear Hf. revert bs bs' Hupd.
      induction xs; intros bs bs' Hupd.
      - inv Hupd.
        destruct bs; eauto; simpl; normalize_sets; sets.
      - destruct bs'.
        { simpl. normalize_sets; sets. }
        simpl in *.

        destruct (update_bs S xs bs') eqn:Hup.
        destruct b. inv Hupd.
        * eapply IHxs. eassumption.
        * inv Hupd.
          eapply orb_false_iff in H1. inv H1.
          destruct (PS.mem a S) eqn:Hmem. now inv H. clear H.
          specialize (IHxs l bs' Hup).
          normalize_sets. eapply Union_Disjoint_r; [| eassumption ].
          eapply Disjoint_Singleton_r.
          intros Hc. eapply FromSet_sound in Hc; [| reflexivity ].
          eapply PS.mem_spec in Hc. congruence. }
    eassumption.

  - inv Hl. split; eauto. congruence.
Qed.


Lemma add_fun_vars_subset L v l Q :
  FromSet Q \subset FromSet (add_fun_vars L v l Q).
Proof.
  unfold add_fun_vars.
  destruct (get_fun_vars L v); rewrite FromSet_union_list; sets.
Qed.


Lemma live_expr_subset L e Q :
  FromSet Q \subset FromSet (live_expr L e Q).
Proof.
  revert Q; induction e using exp_ind'; intros Q; simpl;
    try now (eapply Included_trans; [| eapply IHe ]; rewrite FromSet_union_list; sets).
  - rewrite FromSet_add; sets.
  - simpl in *. rewrite !FromSet_add. setoid_rewrite FromSet_add in IHe0.
    eapply Included_trans; [| eapply IHe0 ].
    eapply IHe.
  - eapply Included_trans; [| eapply IHe ].
    rewrite FromSet_add; sets.
  - eapply Included_trans; [| eapply IHe ].
    eapply Included_trans; [| eapply add_fun_vars_subset ].
    rewrite !FromSet_add; sets.
  - sets.
  - eapply Included_trans; [| eapply add_fun_vars_subset ].
    rewrite FromSet_add; sets.
  - auto.
  - rewrite FromSet_add; sets.
Qed.

Lemma fold_left_live_expr_subset L S (P : list (ctor_tag * exp)) :
  FromSet S \subset FromSet (fold_left (fun (S : PS.t) '(_, e') => live_expr L e' S) P S).
Proof.
  revert S. induction P; simpl; intros; sets.
  destruct a. eapply Included_trans; [| eapply IHP ].
  eapply live_expr_subset.
Qed.

Lemma live_args_subset {A} (ys : list A) bs:
  FromList (live_args ys bs) \subset FromList ys.
Proof.
  revert bs; induction ys; intros [ | [|] bs ]; simpl; sets.
  - repeat normalize_sets. sets.
  - repeat normalize_sets. sets.
Qed.


Lemma live_expr_sound Q L e S :
  no_fun e ->
  Disjoint _ (FromSet (live_expr L e Q)) S ->
  Dead S L e.
Proof.
  revert Q; induction e using exp_ind'; intros Q; simpl; intros Hnf Hdis; inv Hnf.
  - econstructor.
    + repeat normalize_bound_var_in_ctx. repeat normalize_occurs_free_in_ctx.
      eapply Disjoint_Included_l; [| eassumption ].
      eapply Included_trans; [| eapply live_expr_subset ].
      rewrite FromSet_union_list. sets.
    + eapply IHe; eauto.
  - rewrite FromSet_add in *.
    econstructor; eauto. intros Hc.
    eapply Hdis. econstructor; eauto.
  - rewrite FromSet_add in *. econstructor.
    + intros Hc. eapply Hdis. econstructor; eauto.
    + econstructor. eapply IHe; eauto.
      * eapply Disjoint_Included_l; [| eassumption ].
        eapply Included_Union_preserv_r.
        eapply fold_left_live_expr_subset.
      * assert (Hsuff : Dead S L (Ecase v l)).
        { eapply IHe0; eauto.
          eapply Disjoint_Included_l; [| eassumption ].
          simpl. rewrite FromSet_add. sets. }
        inv Hsuff. eassumption.
  - econstructor.
    + repeat normalize_bound_var_in_ctx. repeat normalize_occurs_free_in_ctx.
      intros Hc.
      eapply Hdis; eauto. econstructor; eauto. eapply live_expr_subset.
      rewrite FromSet_add. sets.
    + eapply IHe; eauto.
  - destruct (L ! f) eqn:Heq.
    + eapply Live_LetApp_Known. eassumption.
      * intros Hc. eapply Hdis. constructor; eauto.
        eapply live_expr_subset.
        eapply add_fun_vars_subset. rewrite FromSet_add. sets.
      * repeat normalize_bound_var_in_ctx. repeat normalize_occurs_free_in_ctx.
        eapply Disjoint_sym. eapply Disjoint_Included_l; [| eassumption ].
        eapply Included_trans; [| eapply live_expr_subset ].
        unfold add_fun_vars, get_fun_vars. rewrite Heq.
        rewrite FromSet_union_list.  sets.
      * eapply IHe; eauto.
    + eapply Live_LetApp_Unknown; eauto.
      * intros Hc. eapply Hdis. constructor; eauto.
        eapply live_expr_subset.
        eapply add_fun_vars_subset. rewrite FromSet_add. sets.
      * repeat normalize_bound_var_in_ctx. repeat normalize_occurs_free_in_ctx.
        eapply Disjoint_Included_l; [| eassumption ].
        eapply Included_trans; [| eapply live_expr_subset ].
        unfold add_fun_vars. unfold get_fun_vars. rewrite Heq.
        rewrite FromSet_union_list. sets.
  - destruct (L ! v) eqn:Heq.
    + eapply Live_App_Known. eassumption.
      * intros Hc. eapply Hdis. constructor; eauto.
        eapply add_fun_vars_subset. rewrite FromSet_add. sets.
      * repeat normalize_bound_var_in_ctx. repeat normalize_occurs_free_in_ctx.
        eapply Disjoint_sym. eapply Disjoint_Included_l; [| eassumption ].
        unfold add_fun_vars, get_fun_vars. rewrite Heq.
        rewrite FromSet_union_list.  sets.
    + eapply Live_App_Unknown; eauto.
      * intros Hc. eapply Hdis. constructor; eauto.
        eapply add_fun_vars_subset. rewrite FromSet_add. sets.
      * repeat normalize_bound_var_in_ctx. repeat normalize_occurs_free_in_ctx.
        eapply Disjoint_Included_l; [| eassumption ].
        unfold add_fun_vars. unfold get_fun_vars. rewrite Heq.
        rewrite FromSet_union_list. sets.
  - econstructor; eauto.
  - econstructor.
    + repeat normalize_bound_var_in_ctx. repeat normalize_occurs_free_in_ctx.
      eapply Disjoint_Included_l; [| eassumption ].
      eapply Included_trans; [| eapply live_expr_subset ].
      rewrite FromSet_union_list. sets.
    + eapply IHe; eauto.
  - econstructor.
    + repeat normalize_bound_var_in_ctx. repeat normalize_occurs_free_in_ctx.
      intros Hc. eapply Hdis. constructor; eauto.
      rewrite FromSet_add. now sets.
Qed.

Lemma live_correct L L' B :
  no_fun_defs B -> (* no nested functions in B *)
  live B L false = (L', false) ->
  L = L' /\ live_map_sound B L.
Proof.
  revert L L'; induction B; simpl; intros L L' Hnf Hl.
  - destruct (update_live_fun L v l (live_expr L e PS.empty)) as [L'' b] eqn:Heq.

    assert (Hd := live_diff _ _ _ _ Hl). destruct b; inv Hd.
    simpl in *.

    edestruct update_live_fun_false; try eassumption.

    destructAll.

    eapply IHB in Hl. inv Hl.

    split. reflexivity.

    { intro; intros. inv H.
      - inv H3. eapply live_expr_sound. inv Hnf. eassumption.
        unfold get_fun_vars in *. eapply H0. eassumption.
      - eapply H1. eassumption. eassumption. }

    inv Hnf. eassumption.

  - inv Hl. split; eauto.
    intro; intros. inv H.
Qed.


(* Proof that a fixpoint is reached in n steps *)

Fixpoint bitsize (bs : list bool) :=
  match bs with
  | [] => 0
  | b :: bs => if b then 1 + bitsize bs else bitsize bs
  end.

Definition map_size (L : live_fun) :=
  fold_left (fun s '(_, bs) => s + bitsize bs) (M.elements L) 0.

Definition max_map_size (L : live_fun) :=
  fold_left (fun s '(_, bs) => s + length bs) (M.elements L) 0.


Lemma update_bs_bitsize_leq S xs bs bs' diff :
  update_bs S xs bs = (bs', diff) ->
  bitsize bs <= bitsize bs'.
Proof.
  revert S bs bs' diff. induction xs; simpl; intros S bs bs' diff Hupd.
  - inv Hupd. reflexivity.
  - destruct bs.
    + inv Hupd. reflexivity.
    + destruct (update_bs S xs bs) as [bs'' d] eqn:Hupd'.
      destruct b.
      * inv Hupd. simpl. eapply IHxs in Hupd'. lia.
      * inv Hupd. eapply IHxs in Hupd'. simpl.
        destruct (PS.mem a S); lia.
Qed.

Lemma update_bs_bitsize S xs bs bs' :
  update_bs S xs bs = (bs', true) ->
  bitsize bs < bitsize bs'.
Proof.
  revert S bs bs'. induction xs; simpl; intros S bs bs' Hupd.
  - inv Hupd.
  - destruct bs.
    + inv Hupd.
    + destruct (update_bs S xs bs) as [bs'' d] eqn:Hupd'.
      destruct b.
      * inv Hupd. simpl. eapply IHxs in Hupd'. lia.
      * inv Hupd. simpl.
        destruct (PS.mem a S).
        -- eapply update_bs_bitsize_leq in Hupd'. lia.
        -- simpl in H1. subst. eapply IHxs. eassumption.
Qed.

Lemma update_bs_length S xs bs bs' diff :
  update_bs S xs bs = (bs', diff) ->
  length bs = length bs'.
Proof.
  revert S bs bs' diff. induction xs; simpl; intros S bs bs' diff Hupd.
  - inv Hupd. reflexivity.
  - destruct bs.
    + inv Hupd. reflexivity.
    + destruct (update_bs S xs bs) as [bs'' d] eqn:Hupd'.
      destruct b.
      * inv Hupd. simpl. eapply IHxs in Hupd'. lia.
      * inv Hupd. simpl.
        eapply IHxs in Hupd'. congruence.
Qed.


Lemma set_fun_vars_map_size L f l bs :
  L ! f = Some l ->
  length l = length bs ->
  map_size L + bitsize bs =  map_size (set_fun_vars L f bs) + bitsize l.
Proof.
  intros Heq Hlen. unfold set_fun_vars.

  unfold map_size.
  edestruct elements_set_some. eassumption.
  destructAll.
  rewrite H, H0.
  rewrite !fold_left_app. simpl.
  rewrite <- (plus_O_n (fold_left _ _ _ + bitsize l)).
  rewrite <- (plus_O_n (fold_left _ x 0 + bitsize bs)).
  erewrite !List_util.fold_left_acc_plus. simpl. lia.

  intros ? ? [? ? ]. lia.
  intros ? ? [? ? ]. lia.
Qed.


Lemma update_live_fun_size_leq L L' b f xs S :
  update_live_fun L f xs S = (L', b) ->
  map_size L <= map_size L'.
Proof.
  intros Hl.
  unfold update_live_fun in Hl.
  destruct (get_fun_vars L f) eqn:Hf.
  unfold get_fun_vars in *.
  destruct (update_bs S xs l) as [bs diff] eqn:Hupd.
  destruct diff.

  - inv Hl. assert (Hupd' := Hupd). eapply update_bs_bitsize in Hupd.
    eapply set_fun_vars_map_size with (bs := bs) in Hf. lia.
    eapply update_bs_length. eassumption.
  - inv Hl. reflexivity.
  - inv Hl. reflexivity.
Qed.

Lemma update_live_fun_size L L' f xs S :
  update_live_fun L f xs S = (L', true) ->
  map_size L < map_size L'.
Proof.
  intros Hl.
  unfold update_live_fun in Hl.
  destruct (get_fun_vars L f) eqn:Hf; try congruence.
  unfold get_fun_vars in *.
  destruct (update_bs S xs l) as [bs diff] eqn:Hupd.
  destruct diff.

  - inv Hl. assert (Hupd' := Hupd). eapply update_bs_bitsize in Hupd.
    eapply set_fun_vars_map_size with (bs := bs) in Hf. lia.
    eapply update_bs_length. eassumption.
  - inv Hl.
Qed.


Lemma live_size_leq L L' d d' B :
  live B L d = (L', d') ->
  map_size L <= map_size L'.
Proof.
  revert L L' d d'; induction B; simpl; intros L L' d d' Hl; subst.
  - destruct (update_live_fun L v l (live_expr L e PS.empty)) as [L'' b] eqn:Heq.
    destruct b; simpl in *.
    + eapply Nat.le_trans.
      eapply update_live_fun_size_leq.
      eassumption.
      eapply IHB. eassumption.
    + edestruct update_live_fun_false.
      eassumption. destructAll.
      eapply IHB. eassumption.
  - inv Hl. reflexivity.
Qed.


Lemma live_size L L' B :
  live B L false = (L', true) ->
  map_size L < map_size L'.
Proof.
  assert (Heq : false = false) by reflexivity. revert Heq. generalize false at 1 3.
  revert L L'; induction B; simpl; intros L L' d Heq Hl; subst.
  - destruct (update_live_fun L v l (live_expr L e PS.empty)) as [L'' b] eqn:Heq.

    destruct b; simpl in *.
    + eapply Nat.lt_le_trans.
      eapply update_live_fun_size. eassumption.
      eapply live_size_leq.
      eassumption.
    + edestruct update_live_fun_false.
      eassumption. destructAll.
      eapply IHB. reflexivity. eassumption.
  - inv Hl.
Qed.


Lemma find_live_helper_size B L n L' :
  no_fun_defs B ->
  find_live_helper B L n = Ret L' ->
  (* either a fixpoint is reached *)
  live_map_sound B L' \/
  (* or the distance between L and L' is at least n *)
  map_size L + n <= map_size L'.
Proof.
  revert B L L'. induction n; intros.
  - inv H0. right. lia.
  - simpl in H0.
    destruct (live B L false) as [L1 diff]  eqn:Hlive.

    destruct diff.

    + eapply IHn in H0; eauto. inv H0. now left.
      right.

      eapply live_size in Hlive. lia.

    + inv H0. eapply live_correct in Hlive; eauto.
      destructAll. now left.
Qed.


(* Lemmas about max_size *)

Lemma bitsize_leq bs :
  bitsize bs <= Datatypes.length bs.
Proof.
  induction bs; simpl; eauto. destruct a; lia.
Qed.

Lemma max_map_size_leq L :
  map_size L <= max_map_size L.
Proof.
  unfold map_size, max_map_size.
  eapply List_util.fold_left_monotonic; eauto.
  intros. destruct x2. simpl.
  assert (Hleq := bitsize_leq l).
  lia.
Qed.



Lemma max_map_size_empty :
  max_map_size (M.empty (list bool)) = 0.
Proof. reflexivity. Qed.

(* Proofs that max_max_size is preserved during liveness analysis *)

Lemma set_fun_vars_max_size L f l bs :
  L ! f = Some l ->
  length l = length bs ->
  max_map_size (set_fun_vars L f bs) = max_map_size L.
Proof.
  intros Heq Hlen. unfold set_fun_vars.

  unfold map_size, max_map_size.
  edestruct elements_set_some. eassumption.
  destructAll.
  rewrite H, H0.
  rewrite !fold_left_app. simpl.

  rewrite <- (plus_O_n (fold_left _ _ _ + length bs)).
  rewrite <- (plus_O_n (fold_left _ _ _  + length l)).
  erewrite !List_util.fold_left_acc_plus. simpl. congruence.

  intros ? ? [? ? ]. lia.
  intros ? ? [? ? ]. lia.
Qed.


Lemma update_live_fun_max_size L L' b f xs S :
  update_live_fun L f xs S = (L', b) ->
  max_map_size L' = max_map_size L.
Proof.
  intros Hl.
  unfold update_live_fun in Hl.
  destruct (get_fun_vars L f) eqn:Hf; try congruence.
  unfold get_fun_vars in *.
  destruct (update_bs S xs l) as [bs diff] eqn:Hupd.
  destruct diff.

  - inv Hl.  eapply update_bs_length in Hupd.
    assert (Hupd' := Hupd).
    eapply set_fun_vars_max_size. eassumption. eassumption.

  - inv Hl. reflexivity.
Qed.


Lemma live_max_size L L' d d' B :
  live B L d = (L', d') ->
  max_map_size L' = max_map_size L.
Proof.
  revert L L' d d'; induction B; simpl; intros L L' d d' Hl; subst.
  - destruct (update_live_fun L v l (live_expr L e PS.empty)) as [L'' b] eqn:Heq.

    eapply IHB in Hl. eapply update_live_fun_max_size in Heq. congruence.
  - inv Hl. reflexivity.
Qed.


Lemma find_live_helper_max_size B L n L' :
  no_fun_defs B ->
  find_live_helper B L n = Ret L' ->
  max_map_size L' = max_map_size L.
Proof.
  revert B L L'. induction n; intros.
  - inv H0. reflexivity.
  - simpl in H0.
    destruct (live B L false) as [L1 diff]  eqn:Hlive.

    destruct diff.

    + eapply IHn in H0; eauto. eapply live_max_size in Hlive.
      congruence.

    + inv H0.
      eapply live_max_size in Hlive. lia.
Qed.

Lemma set_fun_vars_max_size_None L f bs :
  L ! f = None ->
  max_map_size (set_fun_vars L f bs) = max_map_size L + length bs.
Proof.
  intros Heq. unfold set_fun_vars.

  unfold map_size, max_map_size.
  edestruct elements_set_none. eassumption.
  destructAll.
  rewrite H, H0.
  rewrite !fold_left_app. simpl.

  rewrite <- (plus_O_n (fold_left _ _ _ + length bs)).
  rewrite <- (plus_O_n (fold_left _ x 0)).
  erewrite !List_util.fold_left_acc_plus. simpl. lia.
  intros ? ? [? ? ]. lia.
  intros ? ? [? ? ]. lia.
Qed.

Lemma get_bool_false_length {A} (l : list A) :
  length (get_bool_false l) = length l.
Proof.
  induction l; simpl; eauto.
Qed.

Lemma get_bool_true_length {A} (l : list A) :
  length (get_bool_true l) = length l.
Proof.
  induction l; simpl; eauto.
Qed.

Lemma num_vars_acc B m n :
  num_vars B (n + m) = num_vars B n + m.
Proof.
  revert m n. induction B; intros; simpl; eauto.

  rewrite <- Nat.add_assoc. rewrite (Nat.add_comm m). rewrite Nat.add_assoc.
  rewrite IHB. lia.
Qed.


Lemma init_live_fun_aux_max_size L B L' m :
  Disjoint _ (Dom_map L) (name_in_fundefs B) ->
  unique_functions B ->
  init_live_fun_aux L B = L' ->
  max_map_size L' + m = max_map_size L + num_vars B m.
Proof.
  revert L L' m; induction B; simpl; intros L L' m Hdis Hun Hinit.
  - eapply IHB in Hinit.
    + rewrite Hinit. rewrite set_fun_vars_max_size_None.
      rewrite get_bool_false_length, num_vars_acc. lia.

      destruct (L ! v) eqn:Heq; eauto. exfalso. eapply Hdis.
      constructor; eauto. eexists; eauto.

    + unfold set_fun_vars.
      rewrite Dom_map_set. inv Hun. sets.

    + inv Hun. sets.

  - congruence.
Qed.


Lemma init_live_fun_max_size L B :
  unique_functions B ->
  init_live_fun B = L ->
  max_map_size L = num_vars B 0.
Proof.
  intros.
  eapply init_live_fun_aux_max_size in H0; eauto.
  rewrite max_map_size_empty in H0. simpl in H0. rewrite <- H0. lia.

  rewrite Dom_map_empty. sets.
Qed.

Lemma remove_escaping_max_size L x :
  max_map_size (remove_escaping L x) <= max_map_size L.
Proof.
  unfold remove_escaping. destruct (get_fun_vars L x) eqn:Hget; subst; eauto.

  unfold max_map_size.
  edestruct term.M.elements_remove. eassumption.
  destructAll. rewrite H, H0.
  rewrite !fold_left_app. simpl.

  rewrite <- (plus_O_n (fold_left _ x0 0)).
  erewrite !List_util.fold_left_acc_plus. simpl. lia.
  intros ? ? [? ? ]. lia.
  intros ? ? [? ? ]. lia.
  intros ? ? [? ? ]. lia.
Qed.


Lemma remove_escapings_max_size L x :
  max_map_size (remove_escapings L x) <= max_map_size L.
Proof.
  revert L; induction x; simpl; intros L; subst; eauto.
  specialize (IHx (remove_escaping L a)).
  assert (Hleq := remove_escaping_max_size L a). lia.
Qed.


Lemma escaping_fun_fundefs_max_size_mut :
  (forall e L,
      max_map_size (escaping_fun_exp e L) <= max_map_size L) /\
  (forall B L,
      max_map_size (escaping_fun_fundefs B L) <= max_map_size L).
Proof.
  exp_defs_induction IHe IHl IHB; simpl; intros; subst; eauto;
    try (now eapply Nat.le_trans; [ eapply IHe | eapply remove_escapings_max_size ]);
    try (now eapply Nat.le_trans; [ eapply IHe | eapply remove_escaping_max_size ]).
  - simpl in IHl.
    eapply Nat.le_trans. eapply IHl. eapply IHe.
  - simpl in *.
    eapply Nat.le_trans. eapply IHe. eapply IHB.
  - eapply remove_escapings_max_size.
  - eapply remove_escaping_max_size.
  - simpl in *.
    eapply Nat.le_trans. eapply IHB. eapply IHe.
Qed.

Lemma escaping_fun_exp_max_size :
  (forall e L,
      max_map_size (escaping_fun_exp e L) <= max_map_size L).
Proof. eapply escaping_fun_fundefs_max_size_mut. Qed.

Lemma escaping_fun_fundefs_max_size :
  (forall B L,
      max_map_size (escaping_fun_fundefs B L) <= max_map_size L).
Proof. eapply escaping_fun_fundefs_max_size_mut. Qed.


Lemma find_live_sound (B : fundefs) (e : exp) L :
  no_fun_defs B -> (* no nested fundefs *)
  unique_functions B -> (* unique bindings *)
  find_live (Efun B e) = Ret L ->
  live_map_sound B L.
Proof.
  intros Hnf Hun Hl. unfold find_live in *.
  assert (Hl' := Hl).

  eapply find_live_helper_size in Hl; eauto.
  inv Hl; eauto.
  eapply find_live_helper_max_size in Hl'; eauto.

  assert (Hleq1 := escaping_fun_fundefs_max_size B (init_live_fun B)).
  assert (Hleq2 := escaping_fun_exp_max_size e (escaping_fun_fundefs B (init_live_fun B))).

  erewrite init_live_fun_max_size  with (L := init_live_fun _) in *; eauto.

  assert (Hleq := max_map_size_leq L). lia.
Qed.


(* Domain of live_fun is preserved *)


Lemma update_live_fun_dom L L' f xs S d :
  update_live_fun L f xs S = (L', d) ->
  Dom_map L <--> Dom_map L'.
Proof.
  intros Hl.
  unfold update_live_fun in Hl.
  destruct (get_fun_vars L f) eqn:Hf; try congruence.
  unfold get_fun_vars in *.
  destruct (update_bs S xs l) as [bs diff] eqn:Hupd.
  destruct diff.

  - inv Hl. unfold set_fun_vars.
    rewrite Dom_map_set. rewrite (Union_Same_set [set f] (Dom_map L)). reflexivity.
    eapply Singleton_Included. eexists; eauto.

  - inv Hl. reflexivity.
  - inv Hl. reflexivity.
Qed.


Lemma live_dom L L' d d' B :
  live B L d = (L', d') ->
  Dom_map L <--> Dom_map L'.
Proof.
  revert L L' d d'; induction B; simpl; intros L L' d d' Hl; subst.
  - destruct (update_live_fun L v l (live_expr L e PS.empty)) as [L'' b] eqn:Heq.
    destruct b; simpl in *.
    + eapply IHB in Hl. rewrite <- Hl.
      eapply update_live_fun_dom. eassumption.
    + edestruct update_live_fun_false.
      eassumption. destructAll.
      eapply IHB. eassumption.
  - inv Hl. reflexivity.
Qed.

Lemma find_live_helper_dom B L n L' :
  find_live_helper B L n = Ret L' ->
  Dom_map L <--> Dom_map L'.
Proof.
  revert B L L'. induction n; intros.
  - inv H. reflexivity.
  - simpl in H.
    destruct (live B L false) as [L1 diff] eqn:Hlive.

    destruct diff.

    + eapply live_dom in Hlive.
      rewrite Hlive. eauto.

    + inv H.
      eapply live_dom. eassumption.
Qed.


Lemma init_live_fun_aux_dom L B L' :
  init_live_fun_aux L B = L' ->
  Dom_map L' \subset name_in_fundefs B :|: Dom_map L.
Proof.
  revert L L'; induction B; simpl; intros L L' Hinit.
  - rewrite IHB; eauto.
    unfold set_fun_vars.
    rewrite Dom_map_set. sets.
  - subst. sets.
Qed.


Inductive Known_exp (S : Ensemble var) : exp -> Prop :=
| Known_Constr :
    forall (x : var) (ys : list var) (ct : ctor_tag) (e : exp),
      Disjoint _ (FromList ys) S ->
      Known_exp S e ->
      Known_exp S (Econstr x ct ys e)
| Known_Prim_val :
  forall (x : var) p (e : exp),
    Known_exp S e ->
    Known_exp S (Eprim_val x p e)
| Known_Prim :
  forall (x : var) (g : prim) (ys : list var) (e : exp),
    Disjoint _ (FromList ys) S ->
    Known_exp S e ->
    Known_exp S (Eprim x g ys e)
| Known_Proj :
    forall (x : var) (ct : ctor_tag) (n : N) (y : var) (e : exp),
      ~ y \in S ->
     Known_exp S e ->
     Known_exp S (Eproj x ct n y e)
| Known_Case:
    forall (x : var) (ce : list (ctor_tag * exp)),
      Forall (fun p => Known_exp S (snd p)) ce ->
      Known_exp S (Ecase x ce)
| Known_Fun:
    forall B e,
      Known_fundefs S B ->
      Known_exp S e ->
      Known_exp S (Efun B e)
| Known_Halt :
    forall (x : var),
      ~ x \in S ->
      Known_exp S (Ehalt x)
| Known_App :
    forall (f : var) (ys : list var) (ft : fun_tag),
      Disjoint _ (FromList ys) S ->
      Known_exp S (Eapp f ft ys)
| Known_LetApp :
    forall (x f : var) (ys : list var) (ft : fun_tag) (e : exp),
      Disjoint _ (FromList ys) S ->
      Known_exp S e ->
      Known_exp S (Eletapp x f ft ys e)
with Known_fundefs (S : Ensemble var) : fundefs -> Prop :=
| Known_Fcons :
    forall f ft xs e B,
      Known_exp S e ->
      Known_fundefs S B ->
      Known_fundefs S (Fcons f ft xs e B)
| Known_Fnil :
    Known_fundefs S Fnil.


(* Dom subset *)

Lemma remove_escaping_subset L x :
  Dom_map (remove_escaping L x) \subset Dom_map L.
Proof.
  unfold remove_escaping. destruct (get_fun_vars L x) eqn:Hget; subst; sets.
  rewrite Dom_map_remove. sets.
Qed.

Lemma remove_escapings_subset L x :
  Dom_map (remove_escapings L x) \subset Dom_map L.
Proof.
  revert L; induction x; simpl; intros L; subst; sets.
  eapply Included_trans. eapply IHx. eapply remove_escaping_subset.
Qed.


Lemma escaping_fun_subset_mut :
  (forall e L,
      (Dom_map  (escaping_fun_exp e L)) \subset Dom_map L) /\
  (forall B L,
      (Dom_map (escaping_fun_fundefs B L)) \subset Dom_map L).
Proof.
  exp_defs_induction IHe IHl IHB; simpl; intros; subst; eauto; sets;
  try now (eapply Included_trans; [ eapply IHe | ];
           eauto using remove_escaping_subset, remove_escapings_subset).
  - simpl in *. eapply Included_trans. eapply IHl. eapply IHe.
  - eapply remove_escapings_subset.
  - eapply remove_escaping_subset.
  - eapply Included_trans. eapply IHB. eapply IHe.
Qed.

Lemma escaping_fun_exp_subset :
  (forall e L,
      (Dom_map  (escaping_fun_exp e L)) \subset Dom_map L).
Proof. eapply escaping_fun_subset_mut. Qed.


Lemma escaping_fun_fundefs_subset :
  (forall e L,
      (Dom_map (escaping_fun_fundefs e L)) \subset Dom_map L).
Proof. eapply escaping_fun_subset_mut. Qed.



Lemma remove_escaping_preserves_disjoint S L x :
  Disjoint _ S (Dom_map L) ->
  Disjoint _ S (Dom_map (remove_escaping L x)).
Proof.
  intros Hc. eapply Disjoint_Included_r. eapply remove_escaping_subset. sets.
Qed.

Lemma remove_escapings_preserves_disjoint S L x :
  Disjoint _ S (Dom_map L) ->
  Disjoint _ S (Dom_map (remove_escapings L x)).
Proof.
  intros Hc. eapply Disjoint_Included_r. eapply remove_escapings_subset. sets.
Qed.

Lemma escaping_fun_exp_preserves_disjoint :
  forall e S L,
    Disjoint _ S (Dom_map L) ->
    Disjoint _ S (Dom_map  (escaping_fun_exp e L)).
Proof.
  intros. eapply Disjoint_Included_r. eapply escaping_fun_exp_subset. sets.
Qed.

Lemma escaping_fun_fundefs_preserves_disjoint :
  forall B S L,
    Disjoint _ S (Dom_map L) ->
    Disjoint _ S (Dom_map  (escaping_fun_fundefs B L)).
Proof.
  intros. eapply Disjoint_Included_r. eapply escaping_fun_fundefs_subset. sets.
Qed.


Lemma Known_exp_monotonic_mut :
  (forall e S1 S2,
      Known_exp S1 e ->
      S2 \subset S1 ->
      Known_exp S2 e) /\
  (forall B S1 S2,
      Known_fundefs S1 B ->
      S2 \subset S1 ->
      Known_fundefs S2 B).
Proof.
  exp_defs_induction IHe IHl IHB; simpl; intros; subst; inv H; eauto; try (now econstructor; eauto; sets).
  - inv H2. econstructor. econstructor.
    now eauto.
    assert (Hk : Known_exp S1 (Ecase v l)) by (econstructor; eassumption).
    eapply IHl in Hk; eauto. inv Hk. eassumption.
Qed.


Corollary Known_exp_monotonic :
  forall e S1 S2,
    Known_exp S1 e ->
    S2 \subset S1 ->
    Known_exp S2 e.
Proof. eapply Known_exp_monotonic_mut. Qed.

Corollary Known_fundefs_monotonic :
  forall B S1 S2,
    Known_fundefs S1 B ->
    S2 \subset S1 ->
    Known_fundefs S2 B.
Proof. eapply Known_exp_monotonic_mut. Qed.


Lemma remove_escaping_disjoint L x :
  ~ x \in (Dom_map (remove_escaping L x)).
Proof.
  unfold remove_escaping. destruct (get_fun_vars L x) eqn:Hget; subst; eauto.
  rewrite Dom_map_remove. intros Hc. inv Hc. now eauto.
  intros Hc. inv Hc. unfold get_fun_vars in *. congruence.
Qed.

Lemma remove_escapings_disjoint L x :
  Disjoint _ (FromList x) (Dom_map (remove_escapings L x)).
Proof.
  revert L; induction x; simpl; intros L; subst; eauto.
  - normalize_sets. now sets.
  - normalize_sets. assert (H := remove_escaping_disjoint L a).
    specialize (IHx (remove_escaping L a)).
    eapply Union_Disjoint_l; eauto.
    eapply remove_escapings_preserves_disjoint. eapply Disjoint_Singleton_l. eassumption.
 Qed.

Lemma escaping_fun_fundefs_sound :
  (forall e L,
      Known_exp (Dom_map (escaping_fun_exp e L)) e) /\
  (forall B L,
      Known_fundefs (Dom_map (escaping_fun_fundefs B L)) B).
Proof.
  exp_defs_induction IHe IHl IHB; simpl; intros; subst; eauto;
    try (now econstructor; eauto; eapply escaping_fun_exp_preserves_disjoint; eapply remove_escapings_disjoint).
  - econstructor. econstructor.
    + simpl.
      eapply Known_exp_monotonic. eapply IHe.
      assert (Hsub := escaping_fun_exp_subset (Ecase v l) (escaping_fun_exp e L)). eassumption.
    + simpl in *.
      specialize (IHl (escaping_fun_exp e L)). inv IHl. eassumption.
  - econstructor; eauto.
    assert (Hdis : Disjoint _ [set v0] (Dom_map (escaping_fun_exp e (remove_escaping L v0)))).
    { eapply escaping_fun_exp_preserves_disjoint. eapply Disjoint_Singleton_l.
      eapply remove_escaping_disjoint. }
    intros Hc. eapply Hdis; eauto.
  - econstructor; eauto.
    eapply Known_fundefs_monotonic. eapply IHB.
    eapply escaping_fun_exp_subset.
  - econstructor. eapply remove_escapings_disjoint.
  - econstructor. eapply remove_escaping_disjoint.
  - econstructor; eauto.
    eapply Known_exp_monotonic. eapply IHe.
    eapply escaping_fun_fundefs_subset.
Qed.

Lemma find_live_fun_map_dom B e L :
  find_live (Efun B e) = Ret L ->
  Dom_map L \subset name_in_fundefs B /\
  Known_exp (Dom_map L) (Efun B e).
Proof.
  intros Hf. unfold find_live in *.
  eapply find_live_helper_dom in Hf.
  rewrite <- !Hf at 1. split.

  - eapply Included_trans. eapply escaping_fun_exp_subset.
    eapply Included_trans. eapply escaping_fun_fundefs_subset.
    eapply Included_trans. eapply init_live_fun_aux_dom. reflexivity.
    rewrite Dom_map_empty. sets.

  - eapply Known_exp_monotonic; [| eapply Hf ].
    destruct escaping_fun_fundefs_sound.

    econstructor.

    + eapply Known_fundefs_monotonic. eapply H0.
      eapply Included_trans. eapply escaping_fun_exp_subset. reflexivity.

    + eapply H.
Qed.

(* Top-level theorem for liveness analysis *)
Corollary find_live_sound_top (B : fundefs) (e : exp) L :
  no_fun_defs B -> (* no nested fundefs *)
  unique_functions B -> (* unique bindings *)
  find_live (Efun B e) = Ret L ->
  live_map_sound B L /\
  Dom_map L \subset name_in_fundefs B /\
  Known_exp (Dom_map L) (Efun B e).
Proof.
  intros Hnf Hun Hl.
  edestruct find_live_fun_map_dom. eassumption.
  split; eauto. eapply find_live_sound; eassumption.
Qed.


(* is_hoisted is correct *)

Lemma is_hoisted_exp_correct e :
  is_hoisted_exp e = true ->
  no_fun e.
Proof.
  induction e using exp_ind'; simpl; intros; eauto.
  - simpl in *. congruence.
Qed.


Lemma is_hoisted_fundefs_correct B :
  is_hoisted_fundefs B = true ->
  no_fun_defs B.
Proof.
  induction B; simpl; intros; eauto.

  eapply andb_prop in H. destructAll.
  econstructor; eauto.
  eapply is_hoisted_exp_correct; eauto.
Qed.


Lemma is_hoisted_correct B e :
  is_hoisted (Efun B e) = true ->
  no_fun_defs B /\ no_fun e.
Proof.
  intros H. simpl in *.  eapply andb_prop in H.
  destructAll.
  split; eauto using is_hoisted_exp_correct, is_hoisted_fundefs_correct.
Qed.
