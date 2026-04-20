
From Stdlib Require Import NArith.BinNat Relations.Relations MSets.MSets MSets.MSetRBT
        Lists.List micromega.Lia Sets.Ensembles.
Require Import LambdaANF.term LambdaANF.eval LambdaANF.term_util LambdaANF.identifiers LambdaANF.ctx LambdaANF.set_util
        LambdaANF.Ensembles_util LambdaANF.List_util LambdaANF.tactics LambdaANF.relations LambdaANF.algebra.
Require Export LambdaANF.logical_relations LambdaANF.logical_relations_cc LambdaANF.alpha_conv LambdaANF.inline_letapp.
Require Import compcert.lib.Coqlib.

Import ListNotations.

Close Scope Z_scope.

Section Types.

Context {fuel trace : Type}.
Context {Hf : @fuel_resource fuel} {Ht : @trace_resource trace}.

Definition PostT := @PostT fuel trace.
Definition PostGT := @PostGT fuel trace.

Section Compose.

  Context {A : Type}.

  (* Properties that the intermediate post conditions have *)
  Definition post_property := PostT -> PostGT -> Prop.

  Context (wf_pres : A -> A -> Prop)   (* well-formedness conditions that are preserved by the relation *)
          (post_prop : post_property). (* predicates over postconditons. Usefull to show *)


  Definition rel := PostT -> PostGT -> A -> A -> Prop.

  Inductive R_n (R : PostT -> PostGT -> A -> A -> Prop) : nat -> A -> A -> Prop :=
  | One :
      forall (P1 P2 : PostT) (c1 : A) (c2: A),
        R P1 P2 c1 c2 ->
        wf_pres c1 c2 ->
        post_prop P1 P2 ->
        R_n R 1%nat c1 c2
  | More :
      forall (n m : nat) (c1 : A) (c2: A) c',
        R_n R n c1 c' ->
        R_n R m c' c2 ->
        R_n R (n + m) c1 c2.

  Definition compose_rel (R1 R2 : A -> A -> Prop) (c1 : A) (c2: A) : Prop :=
    exists c', R1 c1 c' /\ R2 c' c2.

End Compose.

Definition pr_trivial : post_property := fun _ _  => True.

Definition wf_trivial {A} : A -> A -> Prop := fun _ _ => True.

Definition preserves_fv (e1 e2 : exp) := occurs_free e2 \subset occurs_free e1.


Section RelComp.

  Context (cenv : ctor_env) (ctag : ctor_tag).

  Context (wf_pres : exp -> exp -> Prop) (post_prop : post_property).



  Definition preord_exp_n n := R_n wf_pres post_prop
                                   (fun P PG e1 e2 =>
                                      forall k rho1 rho2,
                                        preord_env_P cenv PG (occurs_free e1) k rho1 rho2 ->
                                        (* For certain proofs rho1 needs to be a closing substitution,
                                           to ensure that programs "get stuck in the same way" *)
                                        binding_in_map (occurs_free e1) rho1 ->
                                        preord_exp cenv P PG k (e1, rho1) (e2, rho2)) n.

  Definition preord_env_n n S := R_n wf_trivial pr_trivial (fun P PG c1 c2 => forall k, preord_env_P cenv PG S k c1 c2) n.

  Definition preord_val_n n := R_n wf_trivial pr_trivial (fun P PG c1 c2 => forall k, preord_val cenv PG k c1 c2) n.

  Definition preord_res_n n := R_n wf_trivial pr_trivial (fun P PG c1 c2 => forall k, preord_res (preord_val cenv) PG k c1 c2) n.

  Lemma R_n_not_zero A (R : A -> A -> Prop) P Pr k a b :
    R_n R P Pr k a b -> 0 < k.
  Proof.
    intros Hrel. induction Hrel; eauto.
    lia.
  Qed.

  Lemma preord_res_n_OOT_r n v :
    ~ preord_res_n n (Res v) OOT.
  Proof.
    revert v. induction n using lt_wf_rec1; destruct n; intros m Hyp.
    - eapply R_n_not_zero in Hyp. lia.
    - inv Hyp.
      + now specialize (H1 0); eauto.
      + assert (Hlt : 0 < n0). { eapply R_n_not_zero. eassumption. }
        assert (Hlt' : 0 < m0). { eapply R_n_not_zero. eassumption. }
        destruct c'.
        * eapply H. 2:{ eapply H1. } lia.
        * eapply H. 2:{ eapply H2. } lia.
  Qed.

  Lemma preord_res_n_OOT_l n v :
    ~ preord_res_n n OOT (Res v).
  Proof.
    revert v. induction n using lt_wf_rec1; destruct n; intros m Hyp.
    - eapply R_n_not_zero in Hyp. lia.
    - inv Hyp.
      + now specialize (H1 0); eauto.
      + assert (Hlt : 0 < n0). { eapply R_n_not_zero. eassumption. }
        assert (Hlt' : 0 < m0). { eapply R_n_not_zero. eassumption. }
        destruct c'.
        * eapply H. 2:{ eapply H2. } lia.
        * eapply H. 2:{ eapply H1. } lia.
  Qed.

  Context (Hwf : forall e1 e2, wf_pres e1 e2 -> preserves_fv e1 e2).

  Context (Hwf_trans : Transitive wf_pres).

  Lemma closed_preserved e1 e2 :
    closed_exp e1 ->
    wf_pres e1 e2 ->
    closed_exp e2.
  Proof.
    intros Hc1 Hwf1. split; [| now sets ]. eapply Included_trans.
    eapply Hwf. eassumption. eapply Hc1.
  Qed.

  Context (Hwf_c : forall e1 e2, wf_pres e1 e2 -> closed_exp e1 -> closed_exp e2).

  Definition Pr_implies_post_upper_bound (Pr : PostT -> PostGT -> Prop) :=
    forall P PG, Pr P PG -> @post_upper_bound fuel _ trace P.

  Lemma preord_exp_n_wf_pres n e1 e2 :
    preord_exp_n n e1 e2 ->
    wf_pres e1 e2.
  Proof.
    intros Hn. induction Hn; eauto.
  Qed.

  Lemma preord_exp_n_trans n m e1 e2 e3 :
    preord_exp_n n e1 e2 ->
    preord_exp_n m e2 e3 ->
    preord_exp_n (n + m) e1 e3.
  Proof.
    intros H1. revert m e3. induction H1; intros k e3 H2.
    - econstructor. econstructor. eassumption. eassumption. eassumption.
      eassumption.
    - rewrite <- Nat.add_assoc. simpl.
      eapply IHR_n1.
      eapply IHR_n2. eassumption.
  Qed.

  (* Adequacy, termination *)

  Lemma preord_exp_n_impl (n : nat) (e1 : exp) (e2: exp) :
    closed_exp e1 ->
    preord_exp_n n e1 e2 ->

    (forall rho1 rho2,
      forall (v1 : res) cin cout,
        bstep_fuel cenv rho1 e1 cin v1 cout ->
        exists (v2 : res) cin' cout',
          bstep_fuel cenv rho2 e2 cin' v2 cout' /\
          preord_res_n n v1 v2).
  Proof.
    intros Hwfe Hrel. induction Hrel.
    + (* base case *)
      intros.
      edestruct (H (to_nat cin)); eauto.
      eapply preord_env_P_antimon; [| eapply Hwfe ]. now intros z Hin; inv Hin.
      intros x Hc1. eapply Hwfe in Hc1. now inv Hc1.
      destructAll.
      do 3 eexists. split; eauto. eapply One. intros k.
      edestruct (H (k + to_nat cin) rho1 rho2); [| | | eassumption | ].
      eapply preord_env_P_antimon; [| eapply Hwfe ].
      now intros z Hin; inv Hin.
      intros z Hc1. eapply Hwfe in Hc1. now inv Hc1.
      lia. destructAll.
      destruct v1.
      * destruct x; eauto.
      * destruct x; eauto. destruct x2. contradiction.
        eapply bstep_fuel_deterministic in H3; [| clear H3; eassumption ].
        inv H3. eapply preord_res_monotonic. eassumption. lia.
      * clear. firstorder.
      * clear; now firstorder.
    + intros.
      edestruct IHHrel1. eassumption. eassumption. destructAll.
      edestruct IHHrel2. eapply closed_preserved. eassumption. eapply preord_exp_n_wf_pres. eassumption.
      eassumption. destructAll.
      do 3 eexists. split; eauto. eapply More. eassumption. eassumption.

      Unshelve. eauto. eauto.
  Qed.


  (* Adequacy, divergence *)

  Lemma preord_exp_n_preserves_divergence n e1 e2 rho1 rho2 :
    Pr_implies_post_upper_bound post_prop ->
    closed_exp e1 ->

    preord_exp_n n e1 e2 ->
    diverge cenv rho1 e1 ->
    diverge cenv rho2 e2.
  Proof.
    intros Hrel Hef Hexp Hdiv. revert rho1 rho2 Hdiv. induction Hexp; intros rho1 rho2 Hdiv.
    - eapply logical_relations.preord_exp_preserves_divergence. eapply Hrel. eassumption.
      intros k. eapply H.
      unfold closed_exp in Hef. rewrite Hef. now intros z Hin; inv Hin.
      intros x Hc1. eapply Hef in Hc1. now inv Hc1.
      eassumption.
    - eapply IHHexp2. eapply Hwf_c. eapply preord_exp_n_wf_pres. eassumption.
      eassumption.
      eapply IHHexp1. eassumption. eassumption.
      Unshelve. eauto.
  Qed.


  Lemma preord_exp_n_preserves_not_stuck n e1 e2 rho1 rho2  :
    Pr_implies_post_upper_bound post_prop ->
    closed_exp e1 ->

    preord_exp_n n e1 e2 ->
    not_stuck cenv rho1 e1 ->
    not_stuck cenv rho2 e2.
  Proof.
    intros Piml Hwfe Hexp Hns. inv Hns.
    - destructAll. eapply preord_exp_n_impl in Hexp; [| eassumption | eassumption ].
      destructAll. destruct x2; eauto.
      eapply preord_res_n_OOT_r in H1. contradiction.
      left. eauto.
    - right. eapply preord_exp_n_preserves_divergence; eassumption.
  Qed.


  (* Top-level relation for LambdaANF pipeline *)
  Definition R_n_exp P PG n m : relation exp :=
    compose_rel (preord_exp_n n)
                (compose_rel (fun e1 e2 =>
                                wf_pres e1 e2 /\
                                forall k rho1 rho2 ,
                                  cc_approx_env_P cenv ctag (occurs_free e1) k PG rho1 rho2 ->
                                  binding_in_map (occurs_free e1) rho1 ->
                                  cc_approx_exp cenv ctag k P PG (e1, rho1) (e2, rho2))
                             (preord_exp_n m)).


  Definition R_n_res PG n m : relation res :=
    compose_rel (preord_res_n n)
                (compose_rel (fun c1 c2 => forall k, cc_approx_res (cc_approx_val cenv ctag) k PG c1 c2)
                             (preord_res_n m)).

  Definition R_n_val PG n m : relation val :=
    compose_rel (preord_val_n n)
                (compose_rel (fun (c1 : val) (c2 : val) => forall k, cc_approx_val cenv ctag k PG c1 c2)
                             (preord_val_n m)).




  Context {Htr : Transitive wf_pres}.

  (* Adequacy, termination *)

  Lemma R_n_exp_impl P PG (n m : nat) e1 rho1 e2 rho2 :
    closed_exp e1 ->
    R_n_exp P PG n m e1 e2 ->

    forall (v1 : res) cin cout,
      bstep_fuel cenv rho1 e1 cin v1 cout ->
      exists (v2 : res) cin' cout',
        bstep_fuel cenv rho2 e2 cin' v2 cout' /\
        R_n_res PG n m v1 v2.
  Proof.
    intros Hwfe Hrel. inv Hrel. destructAll. inv H0. destructAll.
    assert (Hexp1 := H). assert (Hexp2 := H2). intros.
    eapply preord_exp_n_impl in H; [| eassumption | eassumption ]. destructAll.
    edestruct (H2 (to_nat x2) rho1 rho2); [ | | | eassumption | ].
    intros z Hin. eapply Hwf_c in Hin. now inv Hin. eapply preord_exp_n_wf_pres. eassumption. eassumption.
    intros z Hin. eapply Hwf_c in Hin. now inv Hin. eapply preord_exp_n_wf_pres. eassumption. eassumption.
    lia.

    destructAll.

    assert (H5' := H5).
    eapply preord_exp_n_impl in H5; [| | eassumption ]. destructAll.

    do 3 eexists. split. eassumption.

    eexists. split. eassumption. eexists.
    split. 2:{ eassumption. }

    intros k.
    destruct v1.
    - destruct x1.
      * destruct x4; eauto.
      * eapply preord_res_n_OOT_l in H4. contradiction.
    - destruct x1.
      + eapply preord_res_n_OOT_r in H4. contradiction.
      + destruct x4; eauto.
        destruct x7. eapply preord_res_n_OOT_r in H8.
        contradiction.

        edestruct (H2 (k + to_nat x2)); [| | | eassumption | ].

        eapply cc_approx_env_P_antimon; [| eapply Hwf_c; eauto ].

        intros z Hin. now inv Hin.
        eapply preord_exp_n_wf_pres. eassumption.

        intros z Hin. eapply Hwf_c in Hin. now inv Hin. eapply preord_exp_n_wf_pres; eauto. eassumption.

        lia.
        destructAll.

        destruct x1. contradiction.

        eapply bstep_fuel_deterministic in H9; [| clear H9; eassumption ]. destructAll.
        eapply cc_approx_res_monotonic. eassumption. lia.

    - eapply Hwf_c; eauto. eapply Hwf_c; eauto. eapply preord_exp_n_wf_pres; eauto.

  Qed.


  (* R_n_exp preserves divergence *)
  Lemma R_n_exp_preserves_divergence P PG n m e1 rho1 e2 rho2 (Htrans : Transitive wf_pres ):
    Pr_implies_post_upper_bound post_prop ->
    post_upper_bound P ->
    closed_exp e1 ->
    R_n_exp P PG n m e1 e2 ->
    diverge cenv rho1 e1 ->
    diverge cenv rho2 e2.
  Proof.
    intros Hpr Hp Hc Hrel Hdiv. inv Hrel. destructAll. inv H0. destructAll.
    eapply preord_exp_n_preserves_divergence; [| | eassumption | ]; eauto.
    eapply Hwf_c. eapply Htrans; [| eassumption ]. eapply preord_exp_n_wf_pres. eassumption.
    eassumption.

    eapply cc_approx_exp_preserves_divergence.
    2:{ intros. eapply H2.
        eapply cc_approx_env_P_antimon; [| eapply Hwf_c; eauto ]. intros z Hin. now inv Hin.
        eapply preord_exp_n_wf_pres. eassumption.

        intros z Hin. eapply Hwf_c in Hin. now inv Hin. eapply preord_exp_n_wf_pres; eassumption. eassumption. }
    eassumption.

    eapply preord_exp_n_preserves_divergence. eapply Hpr. eassumption. eassumption. eassumption.

    Unshelve. eauto. eauto.
  Qed.

End RelComp.

Section Linking.

  Context (lft: fun_tag).
  Context (cenv : ctor_env) (ctag : ctor_tag).


  Definition link (x : var) (e1 e2 : exp) : exp :=
    let f := (max_var e1 (max_var e2 x) + 1)%positive in
    Efun (Fcons f lft [] e1 Fnil)
    (Eletapp x f lft [] e2).


  Lemma link_closed x e1 e2 :
    closed_exp e1 ->
    occurs_free e2 \subset [set x] ->
    closed_exp (link x e1 e2).
  Proof.
    intros Hc Hs. unfold closed_exp, link. repeat normalize_occurs_free.
    rewrite !Setminus_Union_distr. repeat rewrite FromList_nil at 1.
    repeat normalize_sets. simpl. repeat rewrite Union_Empty_set_neut_r at 1.
    unfold closed_exp in Hc. rewrite !Hc. repeat normalize_sets.
    rewrite Setminus_Same_set_Empty_set. repeat normalize_sets.
    sets.
  Qed.


  Context (P : PostT) (PG : PostGT) (Hpr : Post_properties cenv P P PG).

  Lemma preord_exp_preserves_linking x e1 e2 e1' e2' :

    (forall k rho1 rho2,
        preord_exp cenv P PG k (e1, rho1) (e2, rho2)) ->

    (forall k rho1 rho2,
        preord_env_P cenv PG [set x] k rho1 rho2 ->
        binding_in_map [set x] rho1 ->
        preord_exp cenv P PG k (e1', rho1) (e2', rho2)) ->

    forall k rho1 rho2, preord_exp cenv P PG k (link x e1 e1', rho1) (link x e2 e2', rho2).
  Proof.
    intros Hexp1 Hexp2. inv Hpr.
    unfold link in *.
    intros k rho1 rho2.


    eapply preord_exp_fun_compat.
    - now eauto.
    - now eauto.
    - eapply preord_exp_letapp_compat.
      + now eauto.
      + now eauto.
      + now eauto.
      + simpl. intros w Hget. rewrite M.gss in Hget. inv Hget.
        eexists. rewrite M.gss. split. reflexivity.
        rewrite preord_val_eq. intros vs1 vs2 j t xs1 eb rho1' Hlen Hdef Hset1.
        simpl in *. rewrite peq_true in Hdef. inv Hdef. simpl in Hset1. destruct vs1. 2:{ congruence. }
        inv Hset1.
        destruct vs2; [| simpl in *; congruence ].
        rewrite peq_true. do 3 eexists. split. reflexivity. split. reflexivity.
        intros. eapply (Hexp1 j) in H2; [| lia ]. destructAll. do 3 eexists. split. eassumption.
        split. eapply HGPost. eassumption. eassumption.
      + now constructor.
      + intros. eapply Hexp2.
        simpl. intros w1 Hget. inv Hget. intros v3 Hget1. rewrite M.gss in *. inv Hget1.
        eauto.

        rewrite <- (Union_Empty_set_neut_l _ [set x]). eapply binding_in_map_set.
        intros z Hin. inv Hin.
  Qed.



  Lemma cc_approx_exp_preserves_linking x e1 e2 e1' e2' :

    (forall k rho1 rho2,
        cc_approx_exp cenv ctag k P PG (e1, rho1) (e2, rho2)) ->

    (forall k rho1 rho2,
        cc_approx_env_P cenv ctag [set x] k PG rho1 rho2 ->
        binding_in_map [set x] rho1 ->
        cc_approx_exp cenv ctag k P PG (e1', rho1) (e2', rho2)) ->

    forall k rho1 rho2, cc_approx_exp cenv ctag k P PG (link x e1 e1', rho1) (link x e2 e2', rho2).
  Proof.
    intros Hexp1 Hexp2. inv Hpr.
    unfold link in *.
    intros k rho1 rho2.


    eapply cc_approx_exp_fun_compat.
    - now eauto.
    - now eauto.
    - intros v1 cin1 cout1 Hlt Hbstep. inv Hbstep.
      + (* OOT *)
        eexists OOT, cin1, <0>. split; [| split ].
        econstructor. eassumption. eapply HPost_OOT. eassumption.
        simpl; eauto.
      + inv H.
        * simpl in *. inv H7.
          destruct xs; [| simpl in H12; congruence ]. simpl in *. inv H12.
          rewrite M.gss in *. inv H5. simpl in *. rewrite peq_true in *. inv H11.

          edestruct (Hexp1 (k + to_nat cin1 + to_nat cin2)); try eassumption. lia.
          destructAll. destruct x0. contradiction.

          edestruct (Hexp2 (k + to_nat cin2)); try eassumption.

          2:{ rewrite <- (Union_Empty_set_neut_l _ [set x]). eapply binding_in_map_set.
              intros z Hin. inv Hin. }

          2:{ lia. }


          2:{ destructAll.
              do 3 eexists. split. econstructor 2. econstructor.
              simpl. rewrite M.gss. reflexivity. simpl. reflexivity. simpl. rewrite peq_true.
              reflexivity. simpl. reflexivity. eassumption. eapply H2.
              split.
              eapply HPost_letapp; eauto. rewrite M.gss. reflexivity.  reflexivity.
              simpl. rewrite peq_true. reflexivity. reflexivity.
              eapply cc_approx_res_monotonic. eassumption. rewrite !to_nat_add. lia. }

          simpl. intros w1 Hget. inv Hget. intros v3 Hget1. rewrite M.gss in *. simpl in *. inv Hget1.
          eexists. split; eauto.
          eapply cc_approx_val_monotonic. eassumption. lia.
        * simpl in *. inv H10.
          destruct xs; [| simpl in H12; congruence ]. simpl in *. inv H12.
          rewrite M.gss in *. inv H6. simpl in *. rewrite peq_true in *. inv H11.

          edestruct (Hexp1 (k + to_nat cin)); try eassumption. lia.
          destructAll. destruct x0. 2:{ contradiction. }

          do 3 eexists. split. econstructor 2. eapply BStept_letapp_oot.
          simpl. rewrite M.gss. reflexivity. simpl. reflexivity. simpl. rewrite peq_true.
          reflexivity. simpl. reflexivity. eapply H.
          split.
          eapply HPost_letapp_OOT; eauto. rewrite M.gss. reflexivity.  reflexivity.
          simpl. rewrite peq_true. reflexivity. reflexivity.

          eauto.
  Qed.



  Context (wf_pres : exp -> exp -> Prop) (post_prop : post_property).



  Lemma preord_exp_n_1 Pr e1 e2 :
    preord_exp_n cenv wf_pres Pr 1 e1 e2 ->
    exists P PG,
      Pr P PG /\
      wf_pres e1 e2 /\
      (forall k rho1 rho2,
          preord_env_P cenv PG (occurs_free e1) k rho1 rho2 ->
          binding_in_map (occurs_free e1) rho1 ->
          preord_exp cenv P PG k (e1, rho1) (e2, rho2)).
  Proof.
    intros H. inv H. do 2 eexists. now split; eauto.
    eapply Nat.eq_add_1 in H0. inv H0. inv H.
    - eapply R_n_not_zero in H2. lia.
    - inv H. eapply R_n_not_zero in H1. lia.
  Qed.

End Linking.

Section LinkingComp.

  Context (Pr : post_property)
          (wf_pres : exp -> exp -> Prop)
          (cenv : ctor_env) (lf : var).

  Context (Hpr : forall P PG, Pr P PG -> Post_properties cenv P P PG).


  Lemma inclusion_refl {A} (Q : relation A) : inclusion _ Q Q.
  Proof. clear. now firstorder. Qed.

  Definition preserves_closed (e1 e2 : exp) := closed_exp e1 -> closed_exp e2.

  Lemma preord_exp_n_preserves_linking_src_l x n e1 e2 e1' :
    preord_exp_n cenv preserves_fv Pr n e1 e2 ->

    closed_exp e1 ->
    occurs_free e1' \subset [set x] ->

    preord_exp_n cenv preserves_fv Pr n (link lf x e1 e1') (link lf x e2 e1').
  Proof.
    intros Hrel. revert e1'. induction Hrel; intros e1' Hw1 Hfv.
    - assert (Hexp2 :
                forall k rho1 rho2,
                  preord_env_P cenv P2 [set x] k rho1 rho2 ->
                  binding_in_map [set x] rho1 ->
                  preord_exp cenv P1 P2 k (e1', rho1) (e1', rho2)).
      { intros. eapply preord_exp_refl. eapply Hpr. eassumption.
        intros z Hin. eapply Hfv in Hin . eauto. }
      assert (Hexp1 :
                forall (k : nat) (rho1 rho2 : env),
                  preord_exp' cenv (preord_val cenv) P1 P2 k (c1, rho1) (c2, rho2)).
      { intros. eapply H. intros z Hin. eapply Hw1 in Hin; eauto. inv Hin.
        intros z Hin. eapply Hw1 in Hin. inv Hin. }


      specialize (preord_exp_preserves_linking
                    lf cenv P1 P2 (Hpr _ _ H1) _ _ _ _ _ Hexp1 Hexp2).
      intros Hc.
      econstructor.
      * intros. eapply Hc.
      * intros x1 Hfv1. eapply link_closed in Hfv1; eauto.
        inv Hfv1.
        eapply closed_preserved; eauto.
      * eassumption.
    - econstructor. eapply IHHrel1. eassumption. eassumption.
      eapply IHHrel2.
      eapply preord_exp_n_wf_pres in Hrel1.
      eapply closed_preserved; eauto.
      clear. now firstorder. eassumption.
  Qed.

  Lemma preord_exp_n_preserves_linking_src_r x n e1 e1' e2' :
    preord_exp_n cenv preserves_fv Pr n e1' e2' ->

    closed_exp e1 ->
    occurs_free e1' \subset [set x] ->

    preord_exp_n cenv preserves_fv Pr n (link lf x e1 e1') (link lf x e1 e2').
  Proof.
    intros Hrel. revert e1. induction Hrel; intros e1 Hw1 Hfv.
    - assert (Hexp2 :
                forall k rho1 rho2,
                  preord_env_P cenv P2 [set x] k rho1 rho2 ->
                  binding_in_map [set x] rho1 ->
                  preord_exp cenv P1 P2 k (c1, rho1) (c2, rho2)).
      { intros. eapply H. intros z Hin. eapply Hfv in Hin; eauto.
        eapply binding_in_map_antimon. eassumption. eassumption. }

      assert (Hexp1 :
                forall (k : nat) (rho1 rho2 : env),
                  preord_exp' cenv (preord_val cenv) P1 P2 k (e1, rho1) (e1, rho2)).
      { intros. eapply preord_exp_refl. eapply Hpr. eassumption.
        intros z Hin. eapply Hw1 in Hin. inv Hin. }

      specialize (preord_exp_preserves_linking
                    lf cenv P1 P2 (Hpr _ _ H1) _ _ _ _ _ Hexp1 Hexp2).
      intros Hc.
      econstructor.
      * intros. eapply Hc.
      * intros x1 Hfv1. eapply link_closed in Hfv1; eauto.
        inv Hfv1.
        eapply Included_trans. eapply H0. eassumption.
      * eassumption.
    - econstructor. eapply IHHrel1. eassumption. eassumption.
      eapply IHHrel2.
      eassumption.
      eapply preord_exp_n_wf_pres in Hrel1.
      eapply Included_trans. eapply Hrel1. eassumption.
      clear. now firstorder.
  Qed.

  Lemma preord_exp_n_preserves_linking x n m e1 e2 e1' e2' :
    preord_exp_n cenv preserves_fv Pr n e1 e2 ->
    preord_exp_n cenv preserves_fv Pr m e1' e2' ->

    closed_exp e1 ->
    occurs_free e1' \subset [set x] ->

    preord_exp_n cenv preserves_fv Pr (n + m) (link lf x e1 e1') (link lf x e2 e2').
  Proof.
    intros (* Hp1 Hp2 *) Hrel1 Hrel2 Hc1 Hfv.
    specialize (preord_exp_n_preserves_linking_src_l x n _ _ _ Hrel1 Hc1 Hfv). intros Hr1.
    eapply preord_exp_n_trans. eassumption.

    assert (Hc2 : closed_exp e2). {
      eapply preord_exp_n_wf_pres in Hrel1. eapply closed_preserved; eauto.
      clear. firstorder. }

    eapply preord_exp_n_preserves_linking_src_r. eassumption. eassumption. eassumption.
  Qed.

End LinkingComp.

Section LinkingCompTop.

  Context (Pr : post_property)
          (wf_pres : exp -> exp -> Prop)
          (wf1 wf2 : exp -> Prop)
          (cenv : ctor_env) (ctag : ctor_tag) (lf : var) (P : PostT) (PG : PostGT).


  Context (* (Hwf : forall e e', wf_pres e e' -> preserves_fv e e') *)
          (Hpr : forall P PG, Pr P PG -> Post_properties cenv P P PG)
          (Hp : Post_properties cenv P P PG).


  Lemma preord_exp_n_prop_mon (Pt1 Pt2 : post_property) n e1 e2 :
    preord_exp_n cenv wf_pres Pt1 n e1 e2 ->
    (forall P PG, Pt1 P PG -> Pt2 P PG) ->
    preord_exp_n cenv wf_pres Pt2 n e1 e2.
  Proof.
    intros Hrel Hi. induction Hrel.
    - econstructor; eauto.
    - econstructor; eauto.
  Qed.

  Lemma Rel_exp_n_preserves_linking x n1 n2 m1 m2 e1 e2 e1' e2' :
    R_n_exp cenv ctag preserves_fv Pr P PG n1 n2 e1 e2 ->
    R_n_exp cenv ctag preserves_fv Pr P PG m1 m2 e1' e2' ->

    (* e1: source library, e2: compiled library *)
    (* e1': source client, e2': compiled client *)

    closed_exp e1 ->
    occurs_free e1' \subset [set x] ->

    R_n_exp cenv ctag preserves_fv Pr P PG (n1 + m1) (n2 + m2) (link lf x e1 e1') (link lf x e2 e2').
  Proof.

    intros Hrel1 Hrel2 Hc1 Hfv. inv Hrel1. inv Hrel2. destructAll. inv H1. inv H2. destructAll.

    assert (Hc2 : closed_exp x0). {
      eapply preord_exp_n_wf_pres in H.
      eapply closed_preserved; eauto. clear. now firstorder. }
    assert (Hfv2 : occurs_free x1 \subset [set x]).
    { eapply preord_exp_n_wf_pres in H0. eapply Included_trans. eapply H0; eauto. eassumption.
      clear. now firstorder. }
    assert (Hc3 : closed_exp x3).
    { eapply closed_preserved; eauto. }
    assert (Hfv3 : occurs_free x3 \subset [set x]).
    { eapply Included_trans. eapply Hc3. sets. }
    assert (Hfv3' : occurs_free x2 \subset [set x]).
    { eapply Included_trans. eapply H3. eassumption. }


    eexists. split.

    eapply preord_exp_n_preserves_linking; eassumption.

    eexists. split. split.
    2:{ intros. eapply cc_approx_exp_preserves_linking.
        2:{ intros. eapply H4. intros z Hin. eapply preord_exp_n_wf_pres in H. eapply H in Hin.
            eapply Hc1 in Hin. now inv Hc1.
            clear; now firstorder.
            intros z Hin. eapply Hc2 in Hin. inv Hin. }

        eassumption.

        intros. eapply H6. intros z Hin. eapply H9. eapply Hfv2. eassumption.
        eapply binding_in_map_antimon. eassumption. eassumption. }


    intros z1 Hfv1. eapply link_closed in Hfv1; eauto.
    inv Hfv1.


    eapply preord_exp_n_preserves_linking; eassumption.
  Qed.

End LinkingCompTop.

Section LinkingFast.

  Context (lft: fun_tag).
  Context (cenv : ctor_env) (ctag : ctor_tag).

  Definition link' (x : var) (* the external reference that will be bound to e1 *)
             (e1 e2 : exp) : option exp :=
    match inline_letapp e1 x with
    | Some (C, x') =>
      let f := (max_var e1 (max_var e2 x') + 1)%positive in
      (* pick fresh name for function *)
      Some (C |[ Efun (Fcons f lft [x] e1 Fnil) (Eapp f lft [x'])]|)
    | None => None
    end.

  Lemma link_straight_code_r x (e1 e2 e : exp) :
    link' x e1 e2 = Some e ->
    straight_code e1 = true.
  Proof.
    unfold link' in *. intros H.
    match goal with
    | [ Hin : context[inline_letapp ?E ?X] |- _ ] =>
      destruct (inline_letapp E X) as [[C' w] | ] eqn:Hin'; inv Hin
    end. eapply inline_straight_code_r. eassumption.
  Qed.

  Lemma link_straight_code_l (e1 e2 : exp) x :
    straight_code e1 = true ->
    exists e, link' x e1 e2 = Some e.
  Proof.
    intros. eapply inline_straight_code_l in H. destructAll.
    eexists. unfold link'. rewrite H. reflexivity.
  Qed.


  Lemma link_src_closed x e1 e2 e :
    closed_exp e1 ->
    occurs_free e2 \subset [set x] ->
    link' x e1 e2 = Some e ->
    closed_exp e.
  Proof.
    intros Hc1 Hc2 Hin. unfold link' in *.
    destruct (inline_letapp e1 x) as [[C z] | ] eqn:Hinl1; try congruence. inv Hin.
    split; [| now sets ].
    eapply Included_trans. eapply occurs_fee_inline_letapp; eauto.
    eapply Union_Included. now eapply Hc1.
    unfold closed_exp in Hc1. repeat normalize_occurs_free.
    simpl in *. repeat normalize_sets.
    rewrite !Setminus_Union_distr in *. rewrite !Setminus_Same_set_Empty_set in *. repeat normalize_sets.
    eapply Union_Included.
    - rewrite Hc1. sets.
    - rewrite Setminus_Union. rewrite Union_commut. rewrite <- Setminus_Union.
      eapply Included_trans. eapply Setminus_Included.
      eapply inline_letapp_var_eq_alt in Hinl1. inv Hinl1.
      + inv H. intros z H. inv H. inv H0. contradiction.
      + inv H.
        * intros y H. inv H. inv H1. contradiction.
        * eapply Hc1 in H0. inv H0.
  Qed.


  Context (P : PostT) (PG : PostGT) (Hpr : Post_properties cenv P P PG)
          (Hinl : post_inline cenv P P P)
          (HinlOOT : post_inline_OOT P P)
          (HinclG : inclusion _ P PG) .


  Lemma preord_exp_preserves_linking_fast x e1 e2 e1' e2' :

    (forall k rho1 rho2,
        preord_exp cenv P PG k (e1, rho1) (e2, rho2)) ->

    (forall k rho1 rho2,
        preord_env_P cenv PG [set x] k rho1 rho2 ->
        binding_in_map [set x] rho1 ->
        preord_exp cenv P PG k (e1', rho1) (e2', rho2)) ->

    closed_exp e1 ->

    match link' x e1 e1', link' x e2 e2' with
    | Some e, Some e' =>
      forall k rho1 rho2, preord_exp cenv P PG k (e, rho1) (e', rho2)
    | _ , _ => True
    end.
  Proof.
    intros Hexp1 Hexp2 (* Hc1 *) Hc1. inv Hpr.
    unfold link' in *.

    destruct (inline_letapp e1 x) as [[C z] | ] eqn:Hinl1; eauto.
    destruct (inline_letapp e2 x) as [[C' z'] | ] eqn:Hinl2; eauto.

    intros k rho1 rho2.
    eapply inline_letapp_compat with (sig := id); [ | | | eapply Hc1 | eassumption | eassumption  | ].
    - eassumption.
    - eassumption.
    - intros. eapply Hexp1.
    - intros. eapply preord_exp_fun_compat.
      + eauto.
      + eauto.
      + eapply preord_exp_app_compat.
        * now eauto.
        * now eauto.
        * simpl. intros w Hget. rewrite M.gss in Hget. inv Hget.
          eexists. rewrite M.gss. split. reflexivity.
          rewrite preord_val_eq. intros vs1 vs2 j t xs1 eb rho1' Hlen Hdef Hset1.
          simpl in *. rewrite peq_true in Hdef. inv Hdef. simpl in Hset1. destruct vs1. congruence.
          destruct vs1; [| congruence ]. inv Hset1. destruct vs2. simpl in *. congruence.
          destruct vs2; [| simpl in *; congruence ].
          rewrite peq_true. do 3 eexists. split. reflexivity. split. reflexivity.
          intros. eapply (Hexp1 j) in H4; [| lia ]. destructAll. do 3 eexists. split. eassumption.
          split. eapply HinclG. eassumption. eassumption.
        * assert (Hleq : (z' <= max_var e2 (max_var e2' z'))%positive).
          { eapply Pos.le_trans. eapply acc_leq_max_var. eapply acc_leq_max_var. }
          assert (Hleq' : (z <= max_var e1 (max_var e1' z))%positive).
          { eapply Pos.le_trans. eapply acc_leq_max_var. eapply acc_leq_max_var. }

          constructor; [| now constructor ].
          simpl. intros w1 Hget.
          rewrite M.gso in Hget; auto.
          rewrite M.gso; auto.
          eapply H0 in Hget; [| reflexivity ]. destructAll.
          rewrite functions.extend_gss in H1.
          eexists. split; eauto. eapply preord_val_monotonic. eassumption. lia.

          intros Hc. rewrite Hc in Hleq at 1. zify; lia.
          intros Hc. rewrite Hc in Hleq' at 1. zify; lia.
  Qed.

  Lemma cc_approx_exp_preserves_linking_fast x e1 e2 e1' e2' (Hincl : inclusion _ P PG):

    (forall k rho1 rho2,
        cc_approx_exp cenv ctag k P PG (e1, rho1) (e2, rho2)) ->

    (forall k rho1 rho2,
        cc_approx_env_P cenv ctag [set x] k PG rho1 rho2 ->
        binding_in_map [set x] rho1 ->
        cc_approx_exp cenv ctag k P PG (e1', rho1) (e2', rho2)) ->

    closed_exp e1 ->

    match link' x e1 e1', link' x e2 e2' with
    | Some e, Some e' =>
      forall k rho1 rho2, cc_approx_exp cenv ctag k P PG (e, rho1) (e', rho2)
    | _ , _ => True
    end.
  Proof.
    intros Hexp1 Hexp2 (* Hc1 *) Hc1. inv Hpr.
    unfold link' in *.

    destruct (inline_letapp e1 x) as [[C z] | ] eqn:Hinl1; eauto.
    destruct (inline_letapp e2 x) as [[C' z'] | ] eqn:Hinl2; eauto.

    intros k rho1 rho2.
    eapply inline_letapp_compat_cc with (sig := id); [ | | | eapply Hc1 | eassumption | eassumption  | ].
    - eassumption.
    - eassumption.
    - intros. eapply Hexp1.
    - intros. eapply cc_approx_exp_fun_compat.
      + eauto.
      + eauto.
      + simpl def_funs. intros v1 c1 c2 Hleq Hstep. inv Hstep.
        * eexists OOT, c1. eexists. split; [| split ].
          -- econstructor. simpl in *. eassumption.
          -- simpl. eapply HPost_OOT. eassumption.
          -- simpl. eauto.
        * inv H1. simpl in *. rewrite M.gss in *. inv H5. simpl in H8.
          rewrite peq_true in H8. inv H8. simpl in H12. destruct vs. congruence.
          destruct vs; [| congruence ]. inv H12.
          assert (Hleqz : (z <= max_var e (max_var e1' z))%positive).
          { eapply Pos.le_trans. eapply acc_leq_max_var. eapply acc_leq_max_var. }
          rewrite M.gso in H6.
          2:{ intros Hc. zify. lia. }
          destruct (rho' ! z) eqn:Hgetz; inv H6.
          edestruct H0. reflexivity. eassumption. destructAll. rewrite functions.extend_gss in H1.

          eapply (Hexp1 (m + 2  + to_nat cin)) in H13; try lia.


          destructAll.
          assert (Hleqz' : (z' <= max_var e2 (max_var e2' z'))%positive).
          { eapply Pos.le_trans. eapply acc_leq_max_var. eapply acc_leq_max_var. }
          do 3 eexists.
          split; [| split ].
          -- constructor 2. econstructor. rewrite M.gss. reflexivity.
             simpl. rewrite M.gso. rewrite H1. reflexivity.

             intros Heq.
             zify. lia.
             simpl. rewrite peq_true. reflexivity. simpl. reflexivity. eassumption.
          -- simpl. eapply HGPost in H4.  eapply HPost_app in H4.
             unfold one in *. simpl in *. eassumption.
             rewrite M.gss. reflexivity. simpl. rewrite M.gso. rewrite Hgetz. reflexivity.
             intros Hc. zify; lia.
             simpl. rewrite peq_true. reflexivity. simpl. reflexivity.
          -- eapply cc_approx_res_monotonic. eassumption. lia.
  Qed.

End LinkingFast.


(* Formalization of the top-level behavioral refinement *)
Section Refinement.

  Context (cenv : ctor_env) (ctag : ctor_tag).

  Fixpoint value_ref' (v1 v2 : val) : Prop:=
    let fix Forall2_aux vs1 vs2 :=
        match vs1, vs2 with
        | [], [] => True
        | v1 :: vs1, v2 :: vs2 =>
          value_ref' v1 v2 /\ Forall2_aux vs1 vs2
        | _, _ => False
        end
    in
    match v1, v2 with
    | Vconstr c1 vs1, Vconstr c2 vs2 =>
      c1 = c2 /\ Forall2_aux vs1 vs2
    | Vfun _ _ _, Vfun _ _ _ => True
    | Vint i1, Vint i2 => i1 = i2
    | Vprim p1, Vprim p2 => p1 = p2
    | _, _ => False
    end.


  Definition value_ref (v1 v2 : val) : Prop:=
    match v1, v2 with
    | Vconstr c1 vs1, Vconstr c2 vs2 =>
      c1 = c2 /\ Forall2 value_ref' vs1 vs2
    | Vfun _ _ _, Vfun _ _ _ => True
    | Vint i1, Vint i2 => i1 = i2
    | Vprim p1, Vprim p2 => p1 = p2
    | _, _ => False
    end.


  Fixpoint value_ref_cc' (v1 v2 : val) : Prop:=
    let fix Forall2_aux vs1 vs2 :=
        match vs1, vs2 with
        | [], [] => True
        | v1 :: vs1, v2 :: vs2 =>
          value_ref_cc' v1 v2 /\ Forall2_aux vs1 vs2
        | _, _ => False
        end
    in
    match v1, v2 with
    | Vconstr c1 vs1, Vconstr c2 vs2 =>
      c1 = c2 /\ Forall2_aux vs1 vs2
    | Vfun _ _ _, Vconstr c [Vfun _ _ _; env] => True
    | Vint i1, Vint i2 => i1 = i2
    | Vprim p1, Vprim p2 => p1 = p2
    | _, _ => False
    end.


  Definition value_ref_cc (v1 v2 : val) : Prop:=
    match v1, v2 with
    | Vconstr c1 vs1, Vconstr c2 vs2 =>
      c1 = c2 /\ Forall2 value_ref_cc' vs1 vs2
    | Vfun _ _ _, Vconstr c [Vfun _ _ _; env] => True
    | Vint i1, Vint i2 => i1 = i2
    | Vprim p1, Vprim p2 => p1 = p2
    | _, _ => False
    end.


  Lemma value_ref_eq v1 v2 :
    value_ref' v1 v2 <-> value_ref v1 v2.
  Proof.
    destruct v1; destruct v2; simpl; try easy.
    split; intros [H1 H2]; split; eauto.
    + revert l0 H2. induction l; intros l0 H2; destruct l0; intros; eauto.
      inv H2. constructor. easy. eauto.
    + induction H2; eauto.
  Qed.

  Lemma value_ref_cc_eq v1 v2 :
    value_ref_cc' v1 v2 <-> value_ref_cc v1 v2.
  Proof.
    destruct v1; destruct v2; simpl; try easy.
    split; intros [H1 H2]; split; eauto.
    + revert l0 H2. induction l; intros l0 H2; destruct l0; intros; eauto.
      inv H2. constructor. easy. eauto.
    + induction H2; eauto.
  Qed.

  (* e2 refines the behavior of e1 *)

  Definition emp := M.empty val.

  Definition refines (vref : val -> val -> Prop) (e1 e2 : exp) :=
    (* Termination *)
    (forall (v1 : val) (c1 : fuel) (t1 : trace),
        bstep_fuel cenv emp e1 c1 (Res v1) t1 ->
        exists (v2 : val) (c2 : fuel) (t2 : trace),
          bstep_fuel cenv emp e2 c2 (Res v2) t2 /\
          vref v1 v2) /\
    (* Divergence *)
    (diverge cenv emp e1 -> diverge cenv emp e2).

  (* Properties of the value refinement *)

  Instance value_ref_transitive : Transitive value_ref.
  Proof.
    intro x; induction x using val_ind';
      intros y1 z1; destruct y1; destruct z1; intros; simpl in *; eauto; try contradiction.
    - simpl in *. destructAll. inv H2. inv H1. eauto.
    - destructAll. split; eauto.
      destruct l0. now inv H2.
      destruct l1. now inv H1. inv H2; inv H1. constructor; eauto.
      rewrite value_ref_eq in *. now eapply IHx; eauto.

      specialize (IHx0 (Vconstr c0 l0) (Vconstr c0 l1)). simpl in IHx0.
      eapply IHx0; eauto.
    - congruence.
    - congruence.
  Qed.

  Lemma preord_val_in_value_ref PG k v1 v2 :
    preord_val cenv PG k v1 v2 -> value_ref v1 v2.
  Proof.
    rewrite preord_val_eq.
    revert v2. induction v1 using val_ind'; intros v2.
    - intros H. simpl in H. destruct v2; try contradiction. inv H.
      inv H1. simpl. split; eauto.
    - intros H. simpl in H. destruct v2; try contradiction. inv H.
      inv H1. simpl. split; eauto. constructor.
      rewrite value_ref_eq. eapply IHv1. rewrite <- preord_val_eq. easy.
      specialize (IHv0 (Vconstr c l')). eapply IHv0.
      split; eauto.
    - intros H. destruct v2; eauto.
      easy.
    - intros H. destruct v2; eauto.
    - intros H; destruct v2; eauto.
  Qed.


  Lemma cc_approx_val_in_value_ref PG k v1 v2 :
    cc_approx_val cenv ctag  PG k v1 v2 -> value_ref_cc v1 v2.
  Proof.
    rewrite cc_approx_val_eq.
    revert v2. induction v1 using val_ind'; intros v2.
    - intros H. simpl in H. destruct v2; try contradiction. inv H.
      inv H1. simpl. split; eauto.
    - intros H. simpl in H. destruct v2; try contradiction. inv H.
      inv H1. simpl. split; eauto. constructor.
      rewrite value_ref_cc_eq. eapply IHv1. rewrite <- cc_approx_val_eq. easy.
      specialize (IHv0 (Vconstr c l')). eapply IHv0.
      split; eauto.
    - intros H. destruct v2; try contradiction.
      simpl in H. destruct l; try contradiction. destruct v0; try contradiction.
      destruct l; try contradiction. destruct v1; simpl; try contradiction.
      destruct l; eauto.
    - intros H. destruct v2; eauto.
    - intros H; destruct v2; eauto.
  Qed.

  Lemma value_ref_compose_l :
    forall v1 v2 v3,
      value_ref v1 v2 -> value_ref_cc v2 v3 -> value_ref_cc v1 v3.
  Proof.
    intros v1.
    induction v1 using val_ind';
      intros v2 v3; destruct v2; destruct v3; intros; simpl in *; eauto; try contradiction.
    - simpl in *. destructAll. inv H2. inv H1. eauto.
    - destructAll. inv H2. inv H1. split; eauto.
      constructor. rewrite value_ref_cc_eq in *. rewrite value_ref_eq in *. eapply IHv1.
      eassumption. eassumption.

      specialize (IHv0 (Vconstr c0 l') (Vconstr c0 l'0)). simpl in IHv0.
      eapply IHv0; eauto.
    - congruence.
    - congruence.
  Qed.

  Lemma value_ref_compose_r :
    forall v1 v2 v3,
      value_ref_cc v1 v2 -> value_ref v2 v3 -> value_ref_cc v1 v3.
  Proof.
    intros v1.
    induction v1 using val_ind';
      intros v2 v3; destruct v2; destruct v3; intros; simpl in *; eauto; try contradiction.
    - simpl in *. destructAll. inv H2. inv H1. eauto.
    - destructAll. inv H2. inv H1. split; eauto.
      constructor. rewrite value_ref_cc_eq in *. rewrite value_ref_eq in *. eapply IHv1.
      eassumption. eassumption.

      specialize (IHv0 (Vconstr c0 l') (Vconstr c0 l'0)). simpl in IHv0.
      eapply IHv0; eauto.
    - destruct l. contradiction.
      destruct v0. contradiction.
      destruct l. contradiction.
      destruct l. inv H0. inv H2. inv H5. inv H6.
      simpl in H3. destruct y. contradiction. easy.
      contradiction. contradiction. contradiction. contradiction. contradiction.
    - congruence.
    - congruence.
  Qed.

  Lemma preord_res_n_in_value_ref n v1 v2 :
    preord_res_n cenv n (Res v1) (Res v2) ->
    value_ref v1 v2.
  Proof.
    assert (Heq1 : Res v1 = Res v1) by reflexivity.
    assert (Heq2 : Res v2 = Res v2) by reflexivity.
    revert Heq1 Heq2. generalize (Res v1) at 1 3 as r1. generalize (Res v2) at 1 3 as r2.
    intros. revert v1 v2 Heq1 Heq2. induction H.
    - intros; subst. eapply preord_val_in_value_ref with (k := 0). eapply H.
    - intros. subst. destruct c'.

      + exfalso. eapply preord_res_n_OOT_r. eassumption.

      + eapply value_ref_transitive. now eapply IHR_n1; eauto. now eapply IHR_n2; eauto.
  Qed.


  Lemma R_n_res_in_value_ref PG n m v1 v2 :
    R_n_res cenv ctag PG n m (Res v1) (Res v2) ->
    value_ref_cc v1 v2.
  Proof.
    assert (Heq1 : Res v1 = Res v1) by reflexivity.
    assert (Heq2 : Res v2 = Res v2) by reflexivity.
    revert Heq1 Heq2. generalize (Res v1) at 1 3 as r1. generalize (Res v2) at 1 3 as r2.
    intros. revert v1 v2 Heq1 Heq2. induction H.
    - intros; subst. destructAll. inv H0. destructAll.
      destruct x.
      + exfalso. eapply preord_res_n_OOT_r. eassumption.
      + destruct x0.
        * exfalso. eapply preord_res_n_OOT_l. eassumption.
        * eapply value_ref_compose_l. eapply preord_res_n_in_value_ref. eassumption.
          eapply value_ref_compose_r.
          eapply cc_approx_val_in_value_ref. eapply (H0 0).
          eapply preord_res_n_in_value_ref. eassumption.
  Qed.


  (* Composition for value refinement *)

  Lemma refines_compose (r1 r2 r3 : val -> val -> Prop) e1 e2 e3 :
    (forall v1 v2 v3, r1 v1 v2 -> r2 v2 v3 -> r3 v1 v3) ->
    refines r1 e1 e2 ->
    refines r2 e2 e3 ->
    refines r3 e1 e3.
  Proof.
    intros Hv [Hterm Hdiv] [Hterm' Hdiv'].
    split; [| now eauto ].
    intros v1 c1 t1 Hstep.
    edestruct Hterm. eassumption. destructAll.
    edestruct Hterm'. eassumption. destructAll.
    do 3 eexists. split. eassumption. eauto.
  Qed.

  Instance refines_transitive (rel : val -> val -> Prop) { _ : Transitive rel } : Transitive (refines rel).
  Proof.
    intros x y z H1 H2. eapply refines_compose; eauto.
  Qed.


  Lemma refines_compose_l e1 e2 e3 :
    refines value_ref e1 e2 ->
    refines value_ref_cc e2 e3 ->
    refines value_ref_cc e1 e3.
  Proof.
    intros. eapply refines_compose; eauto.
    eapply value_ref_compose_l.
  Qed.

  Lemma refines_compose_r e1 e2 e3 :
    refines value_ref_cc e1 e2 ->
    refines value_ref e2 e3 ->
    refines value_ref_cc e1 e3.
  Proof.
    intros. eapply refines_compose; eauto.
    eapply value_ref_compose_r.
  Qed.



  Lemma R_n_res_OOT_r PG n m v :
    ~ R_n_res cenv ctag PG n m (Res v) OOT.
  Proof.
    intros Hc. inv Hc. destructAll. inv H0. destructAll.
    destruct x. eapply preord_res_n_OOT_r in H; eauto.
    specialize (H0 0). destruct x0; try contradiction.
    eapply preord_res_n_OOT_r; eauto.
  Qed.


  Lemma R_n_res_OOT_l PG n m v :
    ~ R_n_res cenv ctag PG n m OOT (Res v).
  Proof.
    intros Hc. inv Hc. destructAll. inv H0. destructAll.
    destruct x0. now eapply preord_res_n_OOT_l; eauto.
    specialize (H0 0). destruct x; try contradiction.
    eapply preord_res_n_OOT_l; eauto.
  Qed.


  (* Transitive logical relations imply behavioral refinement *)

  Context (wf_pres : exp -> exp -> Prop)
          (PostProp : post_property)

          (Hwf : forall e1 e2, wf_pres e1 e2 -> preserves_fv e1 e2)
          (Hwf_trans : Transitive wf_pres)
          (Hub : Pr_implies_post_upper_bound PostProp).

  Lemma cc_approx_exp_in_refines P PG (HP : post_upper_bound P) e1 e2 :
    (forall k, cc_approx_exp cenv ctag k P PG (e1, M.empty _) (e2, M.empty _)) ->
    refines value_ref_cc e1 e2.
  Proof.
    intros Hc1. split.
    - intros. edestruct Hc1; eauto. destructAll.
      destruct x. contradiction.
      do 3 eexists. split. eassumption. eapply cc_approx_val_in_value_ref.
      eassumption.
    - intros.
      eapply cc_approx_exp_preserves_divergence; eauto.
  Qed.


  Lemma R_n_exp_in_refines P PG (HP : post_upper_bound P) n m e1 e2 :
    closed_exp e1 ->
    R_n_exp cenv ctag wf_pres PostProp P PG n m e1 e2 ->
    refines value_ref_cc e1 e2.
  Proof.
    intros Hc1 Hexp. split.
    - intros. edestruct R_n_exp_impl; try eassumption.
      intros. now eapply closed_preserved; eauto.

      destructAll. destruct x. exfalso. eapply R_n_res_OOT_r. eassumption.
      do 3 eexists. split. eassumption. eapply R_n_res_in_value_ref. eassumption.

    - intros.
      eapply R_n_exp_preserves_divergence; try eassumption.
      intros. now eapply closed_preserved; eauto.
  Qed.

End Refinement.

End Types.
