(* Correctness proof for lambda lifting. Part of the CertiRocq project.
 * Author: Anonymized, 2016
 *)

Require Import LambdaANF.term LambdaANF.term_util LambdaANF.set_util LambdaANF.identifiers LambdaANF.ctx LambdaANF.tactics
        LambdaANF.Ensembles_util LambdaANF.List_util LambdaANF.functions LambdaANF.lambda_lifting LambdaANF.lambda_lifting_util LambdaANF.eval
        LambdaANF.logical_relations LambdaANF.alpha_conv LambdaANF.algebra LambdaANF.state LambdaANF.lambda_lifting_corresp .
Require Import compcert.lib.Coqlib.
From Stdlib Require Import Lists.List MSets.MSets MSets.MSetRBT Numbers.BinNums
        NArith.BinNat PArith.BinPos Sets.Ensembles micromega.Lia Lia.
Require Import ExtLib.Structures.Monads ExtLib.Data.Monads.StateMonad.
Import ListNotations Nnat MonadNotation.
Require Import Common.compM.

Open Scope ctx_scope.
Open Scope fun_scope.
Close Scope Z_scope.

Open Scope alg_scope.

Section Lambda_lifting_correct.

  Context {fuel : Type} {Hfuel : @fuel_resource fuel} {trace : Type} {Htrace : @trace_resource trace}.


  Variable pr : prims.
  Variable cenv : ctor_env.

  Context (P1 : nat -> PostT) (* Local *) (* the nat parameter is the extra steps the target is allowed to take (e.g. c2 <= A*c1 + n) *)
          (PG : PostGT) (* Global *)
          (Hcompat : forall n, Post_properties cenv (P1 n) (P1 n) PG) (* can be specialized to 0 *)

          (HPost_fun' : post_fun_compat (P1 1) (P1 0))
          (Hinc : inclusion _ (P1 0) PG)

          (PG_P_local_steps :
             forall {A} e1 rho1 c1 t1 e2 rho2 c2 t2 fvs f B1 rhoc x t xs1 l,
               (* Datatypes.length fvs <= PS.cardinal (fundefs_fv B1) -> *)
               M.get f rho1 = Some (Vfun rhoc B1 x) ->
               find_def x B1 = Some (t, xs1, e1) ->
               P1 l (e1, rho1, c1, t1) (e2, rho2, c2, t2) ->
               l <= 1 + length xs1 + @length A fvs + 1 ->
               PG (e1, rho1, c1, t1) (e2, rho2, c2, t2))
          (P1_mon : forall l l', l <= l' -> inclusion _ (P1 l) (P1 l'))
          (P1_local_app :
             forall (e1 : exp) (rho1 : env) (f : var) (ft : fun_tag) (ys : list var) (rho2 : env),
               post_Eapp_r (P1 0) (P1 (1 + Datatypes.length ys)) e1 rho1 f ft ys rho2)
          (P1_local_app' :
             forall (e1 : exp) (rho1 : env) (f : var) (ft : fun_tag) (ys : list var) (rho2 : env),
               post_Eapp_r (P1 1) (P1 (1 + Datatypes.length ys + 1)) e1 rho1 f ft ys rho2)
          (PG_P_local_steps_let_app :
             forall e1 rho1 c1 t1 c1' t1' e2 rho2 e2' rho2' e2'' rho2'' c2  t2 c2' t2'
                    f B1 e1' rhoc rhoc' x ft ys ys' xs1 vs1 v fvs ft' f',
               M.get f rho1 = Some (Vfun rhoc B1 f') ->
               find_def f' B1 = Some (ft, xs1, e1') ->
               set_lists xs1 vs1 (def_funs B1 B1 rhoc rhoc) = Some rhoc' ->
               (* maybe bstep is needed but ignore for now *)
               P1 1 (e1', rhoc', c1, t1) (e2', rho2', c2, t2) ->
               P1 0 (e1, M.set x v rho1, c1', t1') (e2'', rho2'', c2', t2') ->
               P1 0 (Eletapp x f ft ys e1, rho1, c1 <+> c1' <+> one (Eletapp x f ft ys e1), t1 <+> t1' <+> one (Eletapp x f ft ys e1))
                  (e2, rho2, c2 <+> c2' <+> one (Eletapp x f' ft' (ys' ++ fvs) e2''),
                   t2 <+> t2' <+> one (Eletapp x f' ft' (ys' ++ fvs) e2'')))
          (PG_P_local_steps_let_app_OOT :
             forall e1 rho1 c1 t1  e2 rho2 e2' rho2' e2'' c2  t2
                    f B1 e1' rhoc rhoc' x ft ys ys' xs1 vs1 fvs ft' f' f'',
               M.get f rho1 = Some (Vfun rhoc B1 f'') ->
               find_def f'' B1 = Some (ft, xs1, e1') ->
               set_lists xs1 vs1 (def_funs B1 B1 rhoc rhoc) = Some rhoc' ->
               (* maybe bstep is needed but ignore for now *)
               P1 1 (e1', rhoc', c1, t1) (e2', rho2', c2, t2) ->
               P1 0 (Eletapp x f ft ys e1, rho1, c1 <+> one (Eletapp x f ft ys e1), t1 <+> one (Eletapp x f ft ys e1))
                  (e2, rho2, c2 <+> one (Eletapp x f' ft' (ys' ++ fvs) e2''),
                   t2 <+> one (Eletapp x f' ft' (ys' ++ fvs) e2'')))
          (PG_P_local_steps_app :
             forall rho1 c1 t1 e2 rho2 e2' rho2' c2 t2
                    f B1 e1' rhoc rhoc' f' ft ys xs1 vs1 f'' ft' ys' fvs,
               M.get f rho1 = Some (Vfun rhoc B1 f') ->
               find_def f' B1 = Some (ft, xs1, e1') ->
               set_lists xs1 vs1 (def_funs B1 B1 rhoc rhoc) = Some rhoc' ->
               (* maybe bstep is needed but ignore for now *)
               P1 1 (e1', rhoc', c1, t1) (e2', rho2', c2, t2) ->
               P1 0 (Eapp f ft ys, rho1, c1 <+> one (Eapp f ft ys), t1 <+> one (Eapp f ft ys))
                  (e2, rho2, c2 <+> one (Eapp f'' ft' (ys' ++ fvs)), t2 <+> one (Eapp f' ft' (ys' ++ fvs))))
          (P1_ctx_r :
         forall (n : nat) (e1 e2 : exp) (C : exp_ctx) (rho1 rho2 rho2' : env)
                (C0 : exp_ctx) (c1 c2 : fuel) (cout1 cout2 : trace),
           ctx_to_rho C rho2 rho2' ->
           P1 n (e1, rho1, c1, cout1) (e2, rho2', c2, cout2) ->
           P1 (n + to_nat (one_ctx C0)) (e1, rho1, c1, cout1)
              (C |[ e2 ]|, rho2, plus c2 (one_ctx C), plus cout2 (one_ctx C))).




  (** The invariant that relates the original function definitions with the lifted ones *)
  Definition Funs_inv k (rho rho' : env) (sig : var -> var)
             (zeta : var -> option (var * fun_tag * list var)) : Prop :=
    forall f f' ft' fvs vs1 vs2 j ft1  rho1 rho1' B1 f1 xs1 e1,
      zeta f = Some (f', ft', fvs) ->
      M.get f rho = Some (Vfun rho1 B1 f1) ->
      length vs1 = length vs2 ->
      find_def f1 B1 = Some (ft1, xs1, e1) ->
      Some rho1' = set_lists xs1 vs1 (def_funs B1 B1 rho1 rho1) ->
      exists rho2 rho2' B2 f2 xs2 e2 vs2',
        M.get (sig f') rho' = Some (Vfun rho2 B2 f2) /\
        find_def f2 B2 = Some (ft', xs2, e2) /\
        get_list (map sig fvs) rho' = Some vs2' /\
        (* length vs2' <= PS.cardinal (fundefs_fv B1) /\ (* For the cost bound *) *)
        Some rho2' = set_lists xs2 (vs2 ++ vs2') (def_funs B2 B2 rho2 rho2) /\
        (j < k -> Forall2 (preord_val cenv PG j) vs1 vs2 ->
         preord_exp cenv (P1 1) PG j (e1, rho1') (e2, rho2')).

  (** * Lemmas about [Funs_inv] *)

  Lemma Funs_inv_set k rho rho' sig zeta v1 v2 x y :
    ~ In _ (Funs zeta) x ->
    ~ In _ (LiftedFuns zeta) x ->
    ~ In _ (FunsFVs zeta) x ->
    ~ In _ (image sig (Union _ (FunsFVs zeta) (LiftedFuns zeta))) y ->
    Funs_inv k rho rho' sig zeta ->
    Funs_inv k (M.set x v1 rho) (M.set y v2 rho') (sig {x ~> y}) zeta.
  Proof.
    intros Hnin1 Hnin2 Hnin4 Hnin5 Hinv f f' ft' fvs vs1 vs2 j ft1  rho1 rho1' B1 f1
           xs1 e1 Hget1 Hget2 Hlen Hdef Hset.
    assert (Heq : lifted_name zeta f = Some f')
      by (unfold lifted_name; rewrite Hget1; simpl; eauto).
    assert (Hneq : f <> x)
      by (intros Hc; subst; eapply Hnin1; eexists; eauto).
    assert (Hneq' : f' <> x)
      by (intros Hc; subst; eapply Hnin2; repeat eexists; eauto).
    rewrite M.gso in Hget2; eauto.
    edestruct Hinv as
        [rho2 [rho2' [B2 [f2 [xs2 [e2 [vs2' [Hget' [Hdef' [Hgetl [Hset' Hpre]]]]]]]]]]]; eauto.
    do 8 eexists; repeat split; eauto.
    - rewrite extend_gso; eauto. rewrite M.gso; eauto.
      intros Hc; subst.
      eapply Hnin5. eexists; split; eauto. right. repeat eexists; eauto.
    - rewrite map_extend_not_In. rewrite get_list_set_neq. eassumption.
      intros Hc. eapply in_map_iff in Hc. destruct Hc as [x' [Heq' HIn]].
      eapply Hnin5. eexists; split; eauto. left. now repeat eexists; eauto.
      intros Hc. eapply Hnin4. repeat eexists. eassumption. eassumption.
  Qed.

  Lemma Funs_inv_set_lists k rho rho' rho1 rho1' sig zeta vs1 vs2 xs ys :
    set_lists xs vs1 rho = Some rho1 ->
    set_lists ys vs2 rho' = Some rho1' ->
    Funs_inv k rho rho' sig zeta ->
    Disjoint _ (Funs zeta) (FromList xs) ->
    Disjoint _ (LiftedFuns zeta) (FromList xs) ->
    Disjoint _ (FunsFVs zeta) (FromList xs) ->
    Disjoint _ (image sig (Setminus _ (Union _ (FunsFVs zeta) (LiftedFuns zeta)) (FromList xs))) (FromList ys) ->
    Funs_inv k rho1 rho1' (sig <{xs ~> ys}>) zeta.
  Proof.
    intros Hset1 Hset2 Hinv HD1 HD2 HD3 HD4 f f' ft' fvs vs1' vs2' j ft1  rho2 rho2' B1 f1
           xs1 e1 Hget1 Hget2 Hlen Hdef Hset.
    assert (Heq := lifted_name_eq _ _ _ _ _ Hget1).
    assert (Hneq : ~ In _ (FromList xs) f)
      by (intros Hc; subst; eapply HD1; constructor; eauto; eexists; eauto).
    erewrite <- set_lists_not_In in Hget2; eauto.
    edestruct Hinv as
        [rho3 [rho3' [B2 [f2 [xs2 [e2 [vs2'' [Hget' [Hdef' [Hgetl [Hset' Hpre]]]]]]]]]]]; eauto.
    do 8 eexists; repeat split; eauto.
    - rewrite extend_lst_gso. erewrite <- set_lists_not_In; eauto.
      intros Hc; subst. eapply HD4. constructor; eauto.
      eexists. split; eauto. constructor. right. now repeat eexists; eauto.
      intros Hc'; subst. eapply HD2. constructor; eauto.
      now repeat eexists; eauto.
      intros Hc'; subst. eapply HD2. constructor; eauto.
      now repeat eexists; eauto.
    - erewrite get_list_set_lists_Disjoint; eauto.
      rewrite map_extend_lst_Disjoint. eassumption.
      eapply Disjoint_Included_l; [| eassumption ].
      repeat eexists; eassumption.
      eapply Disjoint_Included_r_sym; [| eassumption ].
      rewrite map_extend_lst_Disjoint.
      intros x Hin. unfold In, FromList in Hin. eapply list_in_map_inv in Hin.
      edestruct Hin as [x' [Heq' Hin']]. eexists; split; eauto.
      constructor.
      left. repeat eexists; eassumption.
      intros Hc. eapply HD3. constructor; eauto.
      now repeat eexists; eauto.
      eapply Disjoint_Included_l; [| eassumption ].
      repeat eexists; eassumption.
  Qed.

  (* TODO move *)
  Lemma get_reset_lst sig xs ys (vs : list val) rho rho' z  :
    set_lists ys vs rho = Some rho' ->
    get_list (map sig xs) rho = Some vs ->
    ~ In _ (FromList ys) (sig z) ->
    length xs = length ys ->
    NoDup xs -> NoDup ys ->
    M.get (sig z) rho = M.get (sig <{ xs ~> ys }> z) rho'.
  Proof with now eauto with Ensembles_DB.
    revert sig ys vs rho' rho. induction xs as [| x xs IHxs ];
      intros sig ys vs rho' rho Hset Hget HD Hlen Hnd1 Hnd2.
    - destruct ys; try discriminate.
      inv Hget. inv Hset. reflexivity.
    - destruct ys; try discriminate. simpl in *.
      inv Hlen. destruct vs; try discriminate.
      destruct (set_lists ys vs rho) eqn:Hset'; try discriminate.
      destruct (M.get (sig x) rho) eqn:Hget'; try discriminate.
      destruct (get_list (map sig xs) rho) eqn:Hgetl; try discriminate.
      inv Hget. inv Hset. inv Hnd1. inv Hnd2. rewrite !FromList_cons in HD.
      assert (H : M.get ((sig <{ xs ~> ys }> {x ~> e}) z) (M.set e v t) =
                  M.get (sig <{ xs ~> ys }> z) t).
      { destruct (peq x z); subst.
        - rewrite extend_gss, M.gss.
          rewrite extend_lst_gso; eauto.
          erewrite <- set_lists_not_In. symmetry. eassumption.
          eassumption.
          intros Hc. eapply HD. right; eauto.
        - rewrite extend_gso; eauto. rewrite M.gso. reflexivity.
          destruct (in_dec peq z xs).
          + edestruct (extend_lst_gss sig) as [y' [Hin' Heq']]; eauto.
            intros Hc. congruence.
          + rewrite extend_lst_gso; eauto.
            intros Hc. subst. eapply HD. constructor; eauto. }
      rewrite H.
      erewrite <- IHxs; eauto.
  Qed.


  Lemma Funs_inv_set_lists_get_list_r k rho rho' rho'' sig zeta vs xs ys :
    set_lists ys vs rho' = Some rho'' ->
    get_list (map sig xs) rho' = Some vs ->
    Funs_inv k rho rho' sig zeta ->
    NoDup ys -> NoDup xs ->
    length xs = length ys ->
    Disjoint _ (image sig (Union _ (FunsFVs zeta) (LiftedFuns zeta))) (FromList ys) ->
    Funs_inv k rho rho'' (sig <{xs ~> ys}>) zeta.
  Proof.
    intros Hset1 Hgetl Hinv Hnd1 Hnd2 Hlen HD1  f f' ft' fvs vs1'
           vs2' j ft1  rho2 rho2' B1 f1 xs1 e1 Hget1 Hget2 Hlen' Hdef Hset.
    assert (Heq : lifted_name zeta f = Some f')
      by (unfold lifted_name; rewrite Hget1; simpl; eauto).
    edestruct Hinv as
        [rho3 [rho3' [B2 [f2 [xs2 [e2 [vs2'' [Hget' [Hdef' [Hgetl' [Hset' Hpre]]]]]]]]]]]; eauto.
    do 8 eexists; repeat split; eauto.
    - erewrite <- get_reset_lst; eauto.
      intros Hc; subst. eapply HD1. constructor; eauto.
      eexists; split; eauto. right. repeat eexists; eauto.
    - erewrite <- get_list_reset_lst; try eassumption.
      eapply Disjoint_Included_l; [| eassumption ].
      eapply image_monotonic.
      intros x Hin. left. repeat eexists; eauto.
  Qed.

  Lemma Funs_inv_monotonic k i rho rho' sig zeta :
    Funs_inv k rho rho' sig zeta ->
    i <= k ->
    Funs_inv i rho rho' sig zeta.
  Proof.
    intros Hinv Hleq f f' ft' fvs vs1' vs2' j ft1  rho2 rho2' B1 f1
           xs1 e1 Hget1 Hget2 Hlen Hdef Hset.
    edestruct Hinv as
        [rho3 [rho3' [B2 [f2 [xs2 [e2 [vs2'' [Hget' [Hdef' [Hgetl [Hset' Hpre]]]]]]]]]]]; eauto.
    do 7 eexists; repeat split; try eassumption.
    intros Hlt. eapply Hpre. lia.
  Qed.

  Instance Funs_inv_Proper : Proper (eq ==> eq ==> eq ==> f_eq ==> eq ==> iff) Funs_inv.
  Proof.
    constructor; intros Hinv f f' ft' fvs vs1' vs2' j ft1  rho2 rho2' B1 f1
                        xs1 e1 Hget1 Hget2 Hlen Hdef Hset; subst;
    edestruct Hinv as
        [rho3 [rho3' [B2 [f2 [xs2 [e2 [vs2'' [Hget' [Hdef' [Hgetl [Hset' Hpre]]]]]]]]]]]; eauto;
    do 7 eexists; repeat split; eauto.
    rewrite <- H2. eassumption.
    rewrite <- H2. eassumption.
    rewrite H2. eassumption.
    rewrite H2. eassumption.
  Qed.

  Lemma Make_wrappers_correct k S f1 f2 z B S1 fds S2 rho1 rho2 :
    Make_wrappers z f1 B S1 fds S2 f2 ->

    preord_env_P_inj cenv PG (S \\ name_in_fundefs B) k f1 rho1 rho2 ->
    Funs_inv k rho1 rho2 f1 z ->

    Disjoint _ (image f1 (S \\ name_in_fundefs B :|: FunsFVs z)) S1 ->
    Disjoint _ (LiftedFuns z :|: FunsFVs z) (S1 :|: name_in_fundefs B) ->

    unique_bindings_fundefs B ->

    (forall f, f \in name_in_fundefs B -> exists rho1c, M.get f rho1 = Some (Vfun rho1c B f)) ->
    f_eq_subdomain (image' (lifted_name z) (name_in_fundefs B)) f1 id ->

    preord_env_P_inj cenv PG S k f2 rho1 (def_funs fds fds rho2 rho2).
  Proof.
    intros Hwr Henv Hfuns Hdis Hdis' Hun Hbin Hfeq x Hin.
    destruct (Decidable_name_in_fundefs B) as [Hdec]. destruct (Hdec x).
    - (* M.get lemma for Make_wrappers *)
      intros v1 Hgetv1. edestruct name_in_fundefs_find_def_is_Some as (ft & xs & e & Hfdef). eassumption.
      edestruct Make_wrappers_find_def as (f' & ft' & fvs & g & xs' & Hzeq & Hlsub & Hgin & Hleq & Hnd & Hfeq' & Hfdef');
        [ eassumption | eassumption | | eassumption | ].
      + eapply Disjoint_Included; [| | eapply Hdis' ]; sets.
      + edestruct (Hbin x) as [rhoc Hgetx]. eassumption. repeat subst_exp.
        eexists. split. rewrite def_funs_eq. reflexivity. eapply find_def_name_in_fundefs. eassumption.

        rewrite preord_val_eq. intros vs1 vs2 j t xs1' e1 rho1c Hlen Hf Hset. repeat subst_exp.
        edestruct Hfuns as (rhoc1 & rhoc1' & B2 & f3 & xs2 & e2 & vs2' & Hgetf' & Hfdef'' & Hgetl  & Hset' & Hyp); try eassumption.

        assert (Hlin : In var (LiftedFuns z) f').
        { eexists. split. eexists. eapply lifted_name_eq. eassumption. eapply lifted_name_eq. eassumption. }
        assert (Hfvin : FromList fvs \subset FunsFVs z).
        { intros y Hiny. do 4 eexists. now split; eauto. }


        edestruct (set_lists_length3 (def_funs fds fds rho2 rho2) xs' vs2) as [rho2c' Hset3].
        rewrite <- Hlen. erewrite <- set_lists_length_eq with (vs := vs1); [| now eauto ]. now eauto.
        do 3 eexists. split. eassumption. split. now eauto. intros Hlt Hall.
        specialize (Hyp Hlt Hall). repeat subst_exp.
        eapply preord_exp_post_monotonic_strong. intros.
        eapply PG_P_local_steps with (l := 1 + (length xs1' + length fvs) + 1); eauto.
        erewrite <- set_lists_not_In; [| now eauto |]. now rewrite def_funs_eq.
        assert (Hdis1 : Disjoint _ (FromList xs1') (name_in_fundefs B)).
        { eapply unique_bindings_fun_in_fundefs; eauto. eapply find_def_correct; eauto. }
        intros Hc. eapply Hdis1; now constructor; eauto.

        erewrite <- (get_list_length_eq (map f1 fvs) vs2'); eauto.
        rewrite list_length_map. lia.

        eapply preord_exp_app_r with (P1 := P1 1); [|  | | eassumption | | ].
        * rewrite <- (length_map f1 fvs). rewrite Hleq.
          rewrite <- length_app.  eapply P1_local_app'.
        * assert (Hfeq'' : f2 f' = f'). {
            erewrite <- Make_wrappers_f_eq_subdomain with (Q := [set f']); [| eassumption | | reflexivity ].
            2:{ eapply Disjoint_Included; [| | eapply Hdis' ]; sets. }
            rewrite Hfeq.
            - reflexivity.
            - eexists. split. eassumption. unfold lifted_name. rewrite Hzeq. reflexivity. }

          { erewrite <- set_lists_not_In; [| now eauto |].
            rewrite def_funs_neq. rewrite <- Hfeq''.
            erewrite <- Make_wrappers_f_eq_subdomain with (Q := [set f']); [ eassumption | eassumption | | reflexivity ].

            eapply Disjoint_Included; [| | eapply Hdis' ]. now sets. now sets.

            intros Hc. eapply Make_wrappers_name_in_fundefs in Hc; [| eassumption ].
            inv Hc. eapply Hdis'. constructor. 2:{ left. eassumption. }
            now left.
            intros Hc. eapply Hdis'. split. left; eassumption. left. now eauto. }

        * eapply get_list_app. eapply get_list_set_lists; [ eassumption | eassumption ].
          erewrite get_list_set_lists_Disjoint; [| | now eauto ].
          rewrite get_list_def_funs_Disjoint. eassumption.

          eapply Disjoint_Included; [| | eapply Hdis ].
          eapply Included_trans. eapply Make_wrappers_name_in_fundefs. eassumption. now sets.
          rewrite FromList_map_image_FromList.
          eapply image_monotonic. eapply Included_Union_preserv_r. intros y Hiny.
          do 4 eexists. now split; eauto.

          eapply Disjoint_sym. eapply Disjoint_Included; [| | eapply Hdis ]. eassumption.
          rewrite FromList_map_image_FromList. eapply image_monotonic. eapply Included_Union_preserv_r. intros y Hiny.
          do 4 eexists. now split; eauto.
        * now eauto.
        * eassumption.
    - erewrite <- Make_wrappers_f_eq_subdomain with (Q := [set x]);
        [| eassumption | now eapply Disjoint_Singleton_l | reflexivity ].
      assert (Hin' : x \in (S \\ name_in_fundefs B)) by (constructor; eauto). assert (Hin'' := Hin').
      intros v1 Hget. eapply Henv in Hin'. edestruct Hin' as [v2 [Hgetv2 Henv']]. eassumption.

      eexists. split; [| eassumption ].
      rewrite def_funs_neq. eassumption. intros Hc. eapply Hdis.
      eapply Make_wrappers_name_in_fundefs in Hc; [| eassumption ]. inv Hc.
      constructor; [| eassumption ]. eapply In_image. left. now constructor; eauto.
  Qed.

  Lemma Make_wrappers_Funs_inv k f1 f2 z B S1 fds S2 rho1 rho2 :
    Make_wrappers z f1 B S1 fds S2 f2 ->
    Funs_inv k rho1 rho2 f1 z ->

    Disjoint _ (LiftedFuns z :|: FunsFVs z) (name_in_fundefs B) ->
    Disjoint _ (image f1 (LiftedFuns z :|: FunsFVs z)) (S1 \\ S2) ->

    Funs_inv k rho1 (def_funs fds fds rho2 rho2) f2 z.
  Proof.
    intros Hw Hfv Hd1 Hd2 f f' ft fvs vs1 vs2 j ft' rhoc rhoc' B1 h xs1 e1 Hzeq Hget Hlen Hf Hset.
    edestruct Hfv as (rhoc1 & rhoc1' & B2 & f3 & xs2 & e2 & vs2' & Hgetf' & Hfdef'' & Hgetl  & Hset' & Hyp); try eassumption.
    do 7 eexists. split; [| split; [| split; [| split ]]].
    - erewrite <- Make_wrappers_f_eq_subdomain with (Q := [set f']); [| eassumption | | reflexivity ].
      rewrite def_funs_neq. eassumption.
      + intros Hc. eapply Make_wrappers_name_in_fundefs in Hc; [| eassumption ].
        eapply Hd2. constructor; [| eassumption ].
        eapply In_image.
        left. eexists. split. eexists. eapply lifted_name_eq. eassumption.
        eapply lifted_name_eq. eassumption.
      + eapply Disjoint_Included_l; [| eassumption ].
        eapply Singleton_Included. left. eexists. split. eexists.
        eapply lifted_name_eq. eassumption.
        eapply lifted_name_eq. eassumption.
    - eassumption.
    - erewrite map_f_eq_subdomain.
      rewrite get_list_def_funs_Disjoint. eassumption.
      rewrite FromList_map_image_FromList. eapply Disjoint_Included_r.
      eapply Make_wrappers_name_in_fundefs. eassumption.
      eapply Disjoint_Included_l; [| eassumption ].
      eapply image_monotonic.
      eapply Included_Union_preserv_r.
      intros y Hiny. do 4 eexists. split; eassumption.

      symmetry. eapply Make_wrappers_f_eq_subdomain. eassumption.
      eapply Disjoint_Included_l; [| eassumption ].
      eapply Included_Union_preserv_r.
      intros y Hiny. do 4 eexists. split; eassumption.
    - eassumption.
    - now eauto.
  Qed.

  Lemma Fundefs_lambda_lift_correct2 k rho rho' B1 B2 sig zeta sig1 zeta1 S S1' S1'' S1''' fvs :
    (* The IH for expressions *)
    (forall m : nat,
        m < k ->
        forall (e : exp) (rho rho' : env)
          (zeta : var -> option (var * fun_tag * list var))
          (sig : var -> var) (S : Ensemble var) (e' : exp)
          (S' : Ensemble var),
          unique_bindings e ->
          Disjoint var (image sig (Union _ (Union _ (occurs_free e) (FunsFVs zeta)) (LiftedFuns zeta)))
                   (Union var S (bound_var e)) ->
          Disjoint var S (Union var (bound_var e) (occurs_free e)) ->
          Disjoint var (LiftedFuns zeta) (Union _ S (bound_var e)) ->
          Disjoint var (Funs zeta) (Union _ S (bound_var e)) ->
          Disjoint var (FunsFVs zeta) (Union _ S (bound_var e)) ->
          Disjoint _ (bound_var e) (occurs_free e) ->
          binding_in_map (image sig (Union _ (Union _ (occurs_free e) (FunsFVs zeta)) (LiftedFuns zeta))) rho' ->
          preord_env_P_inj cenv PG (occurs_free e) m sig rho rho' ->
          Funs_inv m rho rho' sig zeta ->
          Exp_lambda_lift zeta sig e S e' S' ->
          preord_exp cenv (P1 0) PG m (e, rho) (e', rho')) ->

    (* Unique bindings *)
    unique_bindings_fundefs B1 ->

    (* The image of sig is neither in the free set nor in the set of bound variables *)
    Disjoint var (image sig (occurs_free_fundefs B1 :|: (FunsFVs zeta :|: LiftedFuns zeta))) (S :|: bound_var_fundefs B1) ->

    (* The free set is disjoint from the set of bound and free variables *)
    Disjoint var S (bound_var_fundefs B1 :|: occurs_free_fundefs B1) ->

    (* The names of lifted functions is neither in the free set nor in the set of bound variables*)
    Disjoint var (LiftedFuns zeta) (S :|: bound_var_fundefs B1) ->

    (* The domain of zeta is disjoint with the bound variables *)
    Disjoint var (Funs zeta) (S :|: bound_var_fundefs B1) ->

    (* The free variables of the funs in zeta are disjoint from the bound variables *)
    Disjoint var (FunsFVs zeta) (S :|: bound_var_fundefs B1) ->

    (* The bound variables and the free variables are disjoint *)
    Disjoint _ (bound_var_fundefs B1) (occurs_free_fundefs B1) ->

    (* The free variables are in the environment *)
    binding_in_map (image sig (occurs_free_fundefs B1 :|: (FunsFVs zeta :|: LiftedFuns zeta))) rho' ->

    (** The invariant hold for the initial environments **)
    preord_env_P_inj cenv PG (occurs_free_fundefs B1) k sig rho rho' ->
    Funs_inv k rho rho' sig zeta ->

    NoDup fvs ->
    FromList fvs \subset occurs_free_fundefs B1 :|: (FunsFVs zeta :|: LiftedFuns zeta) ->

    Add_functions B1 fvs sig zeta S sig1 zeta1 S1' ->
    Included _ S1'' S1' ->
    Fundefs_lambda_lift2 zeta1 sig1 B1 B1 S1'' B2 S1''' ->

    (** The invariants hold for the final environments **)
    Funs_inv k (def_funs B1 B1 rho rho) (def_funs B2 B2 rho' rho') sig1 zeta1.
  Proof with now eauto with Ensembles_DB.
    revert rho rho' B1 B2 sig zeta sig1 zeta1 S S1' S1'' S1''' fvs.
    induction k as [k IHk] using lt_wf_rec1;
      intros rho rho' B1 B2 sig zeta sig1 zeta1 S
             S1 S2 S3 fvs IHe Hun Hd1 Hd2 Hd3 Hd4 Hd5 Hd6 Hbin Henv Hfinv Hnd  Hin1 Hadd Hin2 Hllfuns.
    assert
      (HB1 : forall j, j < k -> Funs_inv j (def_funs B1 B1 rho rho) (def_funs B2 B2 rho' rho') sig1 zeta1).
    { intros j leq. eapply IHk; last (now apply Hllfuns); eauto.
      - intros. eapply IHe; eauto. lia.
      - eapply preord_env_P_inj_monotonic; [| eassumption]. lia.
      - eapply Funs_inv_monotonic. eassumption. lia. }
    (* ASSERTIONS *)
    assert (Hname : name_in_fundefs B1 \subset bound_var_fundefs B1).
    { eapply name_in_fundefs_bound_var_fundefs. }
    assert (HsubS: S1 \subset S).
    { eapply Add_functions_free_set_Included. eassumption. }
    assert (HDlfuns : Disjoint _ (LiftedFuns zeta1) (S1 :|: bound_var_fundefs B1)).
    { eapply Disjoint_Included_l.
      eapply Add_functions_LiftedFuns_Included_r. eassumption. xsets. }
    assert (HDfuns : Disjoint _ (Funs zeta1) (S :|: (bound_var_fundefs B1 \\ name_in_fundefs B1))).
    { eapply Disjoint_Included_l.
      eapply Add_functions_Funs_Included. eassumption. xsets. }
    assert (HDfunsfvs : Disjoint _ (FunsFVs zeta1) (S :|: bound_var_fundefs B1)).
    { eapply Disjoint_Included_l.
      eapply Add_functions_FunsFVs_Included_r. eassumption.
      eapply Union_Disjoint_l. eassumption.
      eapply Disjoint_Included_l. eassumption. xsets. }
    assert (Himin : image sig1 (occurs_free_fundefs B1 :|: (LiftedFuns zeta1 :|: FunsFVs zeta1)) \subset
                    image sig (occurs_free_fundefs B1 :|: (FunsFVs zeta :|: LiftedFuns zeta)) :|: (S \\ S1)).
    { eapply Included_trans.
      eapply image_monotonic. eapply Included_Union_compat. reflexivity.
      eapply Included_Union_compat.  eapply Add_functions_LiftedFuns_Included_r. eassumption.
      eapply Add_functions_FunsFVs_Included_r. eassumption. rewrite !Union_assoc.
      assert (Hseq :  (occurs_free_fundefs B1 :|: LiftedFuns zeta :|: (S \\ S1) :|: FunsFVs zeta :|: FromList fvs) <-->
                      (occurs_free_fundefs B1 :|: LiftedFuns zeta :|: FunsFVs zeta) :|: (S \\ S1)).
      { rewrite (Union_commut _ (FromList fvs)). rewrite (Union_Same_set (FromList fvs)).
        rewrite <- !Union_assoc. repeat (eapply Same_set_Union_compat; [ reflexivity | ]). sets.
        eapply Included_trans. eassumption. xsets. }
      rewrite Hseq.
      rewrite image_Union. rewrite Add_functions_image_LiftedFuns_Same_set; [| | eassumption | eassumption ].
      rewrite Add_functions_image_Disjoint_Same_set; [| | eassumption ]. now xsets.
      now xsets. sets. }

    assert (Himdis : Disjoint _ (image sig1 (occurs_free_fundefs B1 :|: (LiftedFuns zeta1 :|: FunsFVs zeta1))) (S1 :|: bound_var_fundefs B1)).
    { eapply Disjoint_Included_l. eassumption. eapply Union_Disjoint_l. now sets. sets. }

    intros f1 f2 ft fvs' vs1 vs2 j ft1 rho1 rho1' B1' f1' xs1 e1 Hzeq Hgetf1 Hleq Hfeq Hset.
    destruct (Decidable_name_in_fundefs B1) as [Hdec]. destruct (Hdec f1); clear Hdec.
    + (* f1 is in B1 *)
      rewrite def_funs_eq in Hgetf1; eauto. symmetry in Hgetf1. inv Hgetf1.
      edestruct Fundefs_lambda_lift_find_def2 as
          (ys & e2 & Q1 & Q2 & Q3 & sig' & C & Hf1 & Hnd1 & Hleq1 & Hsub1 & Hsub2 & Hd1' & Hw & Hllexp);
        [ eassumption | eassumption | | | eassumption | ].
      * (* Disjoint var (bound_var_fundefs B1) (LiftedFuns zeta1) *)
        eapply Disjoint_Included_r. eapply Add_functions_LiftedFuns_Included_r. eassumption.
        eapply Union_Disjoint_r...
      * eapply Add_functions_injective_subdomain_LiftedFuns. eassumption.
      * assert (Hinxs : FromList xs1 \subset bound_var_fundefs B1 \\ name_in_fundefs B1).
        { eapply Included_Setminus.
          eapply unique_bindings_fun_in_fundefs. eapply find_def_correct; eassumption. eassumption.
          eapply Included_trans; [| eapply fun_in_fundefs_bound_var_fundefs; eapply find_def_correct; eassumption ]. sets. }
        assert (Hinxs' : FromList xs1 \subset bound_var_fundefs B1).
        { eapply Included_trans. eassumption. sets. }
        assert (Hine : bound_var e1 \subset bound_var_fundefs B1 \\ name_in_fundefs B1).
        { eapply Included_Setminus.
          eapply unique_bindings_fun_in_fundefs. eapply find_def_correct; eassumption. eassumption.
          eapply Included_trans; [| eapply fun_in_fundefs_bound_var_fundefs; eapply find_def_correct; eassumption ]. sets. }
        assert (Hine' : bound_var e1 \subset bound_var_fundefs B1).
        { eapply Included_trans. eassumption. sets. }
        assert (Hssub : Q2 \subset S2).
        { eapply Included_trans. eapply Make_wrappers_free_set_Included. eassumption.
          eapply Included_trans. eassumption. sets. }
        assert (Hssub' : Q2 \subset S).
        { eapply Included_trans. eassumption. eapply Included_trans; eassumption. }
        assert (Hfree : occurs_free e1 \subset (FromList xs1 :|: (name_in_fundefs B1 :|: occurs_free_fundefs B1))).
        { eapply occurs_free_in_fun. apply find_def_correct. eassumption. }
        assert (Him : image sig1 (occurs_free e1 :|: FunsFVs zeta1 :|: LiftedFuns zeta1 \\ FromList (xs1)) \subset
                      image sig (occurs_free_fundefs B1 :|: (FunsFVs zeta :|: LiftedFuns zeta)) :|: (name_in_fundefs B1 :|: (S \\ S1))).
          { eapply Included_trans. eapply image_monotonic. eapply Included_Setminus_compat; [| reflexivity ].
            eapply Included_Union_compat; [| reflexivity ]. eapply Included_Union_compat; [| reflexivity ].
            eassumption. rewrite !Setminus_Union_distr, Setminus_Same_set_Empty_set, Union_Empty_set_neut_l.
            rewrite <- !Setminus_Union_distr. eapply Included_trans. eapply image_monotonic. eapply Setminus_Included.
            rewrite <- !Union_assoc. rewrite image_Union.
            rewrite Add_functions_image_name_in_fundefs; [| | eassumption | eassumption ].
            eapply Union_Included. sets. eapply Included_trans. eapply Included_trans; [| eapply Himin ]. now sets. now sets. now sets. }
          assert (Hesub : occurs_free e1 \\ name_in_fundefs B1 \\ FromList xs1 \subset occurs_free_fundefs B1).
          { do 2 eapply Setminus_Included_Included_Union. eapply Included_trans. eassumption. now sets. }


          assert (Himdis' : Disjoint _ (image sig1 (occurs_free e1 \\ name_in_fundefs B1 \\ FromList (xs1))) (S :|: bound_var_fundefs B1)).
          { rewrite Add_functions_image_Disjoint_Same_set; [| | eassumption ].
            eapply Disjoint_Included; [| | eapply Hd1 ]. now sets. now sets. now xsets. }

          erewrite Add_functions_same_name; [ | | eassumption ].
          2:{ right. eapply Add_functions_image_LiftedFuns_Included. eassumption.
              eapply lifted_name_eq. eassumption. eassumption. }
        edestruct Add_functions_is_Some as (f1'' & ft'' & Hzeq' & Hin). eassumption. eassumption.
        rewrite Hzeq in Hzeq'. inv Hzeq'.
        assert (Ha : exists vsfv, get_list (map sig1 fvs) (def_funs B2 B2 rho' rho') = Some vsfv).
        { eapply binding_in_map_get_list. eapply binding_in_map_def_funs. eassumption. rewrite FromList_map_image_FromList.
          rewrite Add_functions_image_Disjoint_Same_set with (sig := sig) (sig' := sig1); try eassumption.
          eapply Included_Union_preserv_r. eapply image_monotonic.
          eapply Included_trans. eassumption. now sets. eapply Disjoint_Included_l. eassumption. xsets. }
        destruct Ha as [vfvs Hgetfvs].

        assert (Hfset : exists rho2', set_lists (xs1 ++ ys) (vs2 ++ vfvs) (def_funs B2 B2 rho' rho') = Some rho2').
        { eapply set_lists_length3. rewrite !length_app, Hleq1.
          eapply get_list_length_eq in Hgetfvs. rewrite list_length_map in Hgetfvs.
          symmetry in Hset. eapply set_lists_length_eq in Hset. rewrite Hgetfvs, <- Hleq. f_equal. eassumption. }
        destruct Hfset as [rho2' Hsetapp].
        do 7 eexists. split; [| split; [| split; [| split ]]]; [| eassumption | eassumption | | ].
        -- rewrite def_funs_eq. reflexivity. eapply fun_in_fundefs_name_in_fundefs. eapply find_def_correct. eassumption.
        -- now eauto.
        -- intros Hlt Hall. replace 1 with (0 + 1).
           eapply ctx_to_rho_preord_exp with (C := Efun1_c C Hole_c). eassumption. eassumption. eassumption. (* TODO remove extra args ? *)
           ++ intros. eapply P1_ctx_r. eassumption. eassumption.
           ++ constructor. constructor.
           ++ { assert (Hsetapp' := Hsetapp). eapply set_lists_app in Hsetapp. edestruct Hsetapp as (rho2i & Hsetl1 & Hsetl2).
                2:{ rewrite <- Hleq. eapply set_lists_length_eq. now eauto. }

                assert (Hfuns : Funs_inv j rho1' rho2' ((sig1 <{ fvs ~> ys }>) <{ xs1 ~> xs1 }>) zeta1 ).
                 { eapply Funs_inv_set_lists; try now eauto.
                   + eapply Funs_inv_set_lists_get_list_r.
                     -- eassumption.
                     -- eassumption.
                     -- eapply HB1. eassumption.
                     -- eassumption.
                     -- eassumption.
                     -- now eauto.
                     -- eapply Disjoint_Included; [| | eapply Himdis ].
                        eapply Included_trans. eassumption. now sets. sets.
                   + sets.
                   + sets.
                   + sets.
                   + eapply Disjoint_Included_l. eapply image_extend_lst_Included. now eauto. eapply Union_Disjoint_l.
                     -- eapply Disjoint_Included_l. eapply image_monotonic. eapply Setminus_Included.
                        eapply Disjoint_Included_l. eapply Included_trans; [| eapply Him ]. now sets.
                        eapply Union_Disjoint_l. now sets.
                        eapply Union_Disjoint_l; [| now sets ]. eapply Disjoint_sym. eapply unique_bindings_fun_in_fundefs.
                        eapply find_def_correct. eassumption. eassumption.
                     -- eapply Disjoint_Included. eassumption. eassumption.
                        eapply Disjoint_Included; [| | eapply Hd2 ]. sets. eapply Included_trans; eauto. }
                 eapply IHe; [ eassumption | | | | | | | | | | | eassumption ].
               - eapply unique_bindings_fun_in_fundefs.
                 eapply find_def_correct. eassumption. eassumption.
               - eapply Disjoint_Included_l.
                 eapply Make_wrappers_image_Included. eassumption.
                 eapply Union_Disjoint_l.
                 + eapply Disjoint_Included_l. eapply image_extend_lst_Included.
                   rewrite !length_app. rewrite Hleq1. reflexivity.
                   rewrite !FromList_app. eapply Union_Disjoint_l.
                   * rewrite <- Setminus_Union. eapply Disjoint_Included; [| | eapply Himdis ].
                     eapply Included_Union_compat; [| now sets ]. eapply Included_trans. eapply Hssub. eassumption.
                     rewrite !Setminus_Union_distr. eapply image_monotonic. xsets.
                   * eapply Union_Disjoint_r; eapply Union_Disjoint_l.
                     -- eapply Disjoint_Included_r. eassumption. sets.
                     -- eapply Disjoint_Included_r. eapply Make_wrappers_free_set_Included. eassumption.
                        sets.
                     -- eapply Disjoint_sym. eapply unique_bindings_fun_in_fundefs.
                        eapply find_def_correct. eassumption. eassumption.
                     -- eapply Disjoint_Included. eassumption. eapply Included_trans. eassumption.
                        eapply Included_trans. eassumption. eassumption.
                        xsets.
                 + eapply Union_Disjoint_r. now sets.
                   eapply Disjoint_Included; [| | eapply Hd2 ]. now sets.
                   eapply Included_trans. eapply Setminus_Included.
                   eapply Included_trans. eassumption. eapply Included_trans. eapply Setminus_Included. sets.
                   eapply Included_trans; eassumption.
               - eapply Disjoint_Included_r. eapply Included_Union_compat. eassumption. eassumption.
                 eapply Disjoint_Included; [| | eapply Hd2 ]. now xsets. now sets.
               - eapply Disjoint_Included_r; [| eassumption ]. sets.
                 eapply Included_Union_compat; sets. eapply Included_trans. eapply Hssub. eassumption.
               - sets.
               - sets.
               - eapply fun_in_fundefs_Disjoint_bound_Var_occurs_free. eapply find_def_correct. eassumption.
                 eassumption. eassumption.
               - eapply binding_in_map_antimon.
                 eapply Included_Union_Setminus with (s2 := name_in_fundefs C). now tci.
                 rewrite Union_commut. eapply binding_in_map_def_funs.
                 eapply binding_in_map_antimon.
                 rewrite Make_wrappers_name_in_fundefs_image; [| eassumption | eassumption ].
                 eapply functions.image_Setminus. now tci.
                 rewrite <- Make_wrapper_image; [| eassumption | now sets ].

                 eapply binding_in_map_antimon.
                 eapply image_extend_lst_Included. rewrite !length_app. rewrite <- Hleq1. reflexivity.
                 rewrite Union_commut. eapply binding_in_map_set_lists; [| eassumption ].
                 rewrite FromList_app. rewrite <- Setminus_Union.

                 eapply binding_in_map_antimon. eapply Included_trans; [| now eapply Himin ].
                 eapply image_monotonic. repeat apply Setminus_Included_Included_Union.
                 rewrite <- Union_assoc. eapply Union_Included. eapply Included_trans. eassumption. now xsets.
                 now xsets.

                 rewrite <- Add_functions_name_in_fundefs; [| eassumption | eassumption ].
                 rewrite <- Fundefs_lambda_lift_name_in_fundefs2; [| eassumption ].
                 rewrite (Union_commut _ (name_in_fundefs B2)).
                 eapply binding_in_map_def_funs. eassumption.

               - assert (Hnd1': NoDup xs1).
                 { eapply unique_bindings_fun_in_fundefs. eapply find_def_correct; eassumption. eassumption. }

                 { eapply Make_wrappers_correct.
                   - eassumption.
                   - eapply preord_env_P_inj_f_proper; [ reflexivity | reflexivity | | reflexivity | reflexivity | ].
                     eapply extend_lst_app. reflexivity.
                     eapply preord_env_P_inj_set_lists_alt with (f := sig1 <{ fvs ~> ys }>);
                       [| eassumption | eassumption | eassumption | now eauto | | now eauto | eassumption ].
                     + eapply preord_env_P_inj_reset_lists; [ | | eassumption | | | ]; try eassumption.
                       -- eapply Disjoint_Included_r; [| eassumption ]. eapply Included_trans. eassumption.
                          eapply Included_trans. eassumption. sets.
                       -- symmetry. eassumption.
                       -- eapply preord_env_P_inj_def_funs_neq_l. eapply preord_env_P_inj_def_funs_neq_r.
                          eapply preord_env_P_inj_antimon. eapply preord_env_P_inj_f_eq_subdomain.
                          eapply preord_env_P_inj_monotonic; [| eassumption ]. lia.
                          ++ eapply Add_functions_sig_eq_alt. eassumption. now sets.
                          ++ eassumption.
                          ++ rewrite Fundefs_lambda_lift_name_in_fundefs2 with (B' := B2); [| eassumption ].
                             rewrite Add_functions_name_in_fundefs; [| eassumption | eassumption ]. xsets.
                          ++ xsets.
                     + eapply Disjoint_Included_l. eapply image_extend_lst_Included. now eauto. eapply Union_Disjoint_l.
                       * eapply Disjoint_Included; [| | eapply Himdis' ]. now sets. now sets.
                       * eapply Disjoint_Included_l. eassumption. eapply Disjoint_Included_r. eassumption.
                         eapply Disjoint_Included; [| | eapply Hd2 ]; sets. eapply Included_trans; eassumption.
                   - rewrite extend_lst_app.  eassumption. reflexivity.
                   - eapply Disjoint_Included_l. eapply image_extend_lst_Included. rewrite !length_app. congruence.
                     rewrite !FromList_app. eapply Union_Disjoint_l.
                     + eapply Disjoint_Included; [| | eapply Himdis ].
                       eapply Included_trans. eassumption. eapply Included_trans. eapply Included_trans. eapply Setminus_Included.
                       eassumption. now sets. rewrite <- Setminus_Union, !Setminus_Union_distr. eapply image_monotonic. xsets.
                     + eapply Union_Disjoint_l. eapply Disjoint_Included_l. eassumption. eapply Disjoint_sym.
                       eapply Disjoint_Included; [| | eapply Hd2 ]. now xsets. eapply Included_trans. eassumption.
                       eapply Included_trans. eapply Setminus_Included. eapply Included_trans; eassumption. now xsets.
                   - eapply Union_Disjoint_r; [| now xsets ]. sets.
                     eapply Disjoint_Included_r. eapply Included_trans. eassumption. eapply Setminus_Included.
                     xsets. eapply Disjoint_Included_r. eassumption. sets.
                   - sets.
                   - intros g Hgin. eexists. erewrite <- set_lists_not_In; [| now eauto |].
                     rewrite def_funs_eq. reflexivity. eassumption. intros Hc. eapply Hinxs; eassumption.
                   - rewrite Add_functions_name_in_fundefs; [| eassumption | eassumption ].
                     eapply f_eq_subdomain_trans. eapply f_eq_subdomain_extend_lst_Disjoint.
                     rewrite FromList_app. eapply Union_Disjoint_l. now sets.
                     eapply Disjoint_Included_l. eassumption. now xsets.
                     intros y Hiny. unfold id. eapply Add_functions_same_name. right. eassumption. eassumption. }
               - eapply Make_wrappers_Funs_inv. eassumption. rewrite extend_lst_app. eassumption. reflexivity.
                 now xsets.
                 eapply Disjoint_Included_r. eapply Included_trans. eapply Setminus_Included. eassumption.
                 eapply Disjoint_Included_l. eapply image_extend_lst_Included. rewrite !length_app. congruence.
                 rewrite !FromList_app. eapply Union_Disjoint_l.
                 + eapply Disjoint_Included; [| | eapply Himdis ].
                   eapply Setminus_Included_Included_Union. eapply Included_trans. eassumption. now sets.
                   now sets.
                 + eapply Union_Disjoint_l. eapply Disjoint_Included_l. eassumption. eapply Disjoint_sym.
                   eapply Disjoint_Included; [| | eapply Hd2 ]. now xsets. eapply Included_trans.
                   eapply Included_trans. eapply Setminus_Included. eassumption. now xsets.
                   now sets. }
          ++ lia.
    + rewrite def_funs_neq in Hgetf1; [| eassumption ].
      erewrite Add_functions_eq in Hzeq; [| eassumption | eassumption ].
      edestruct Hfinv as (rho2 & rho2' & B2' & f2' & xs2 & e2 & cs2 & Hgetf2 & Hf2 & Hgetl & Hset2  & Hyp).
      * eassumption.
      * eassumption.
      * eapply Hleq.
      * eassumption.
      * eassumption.
      * do 7 eexists. split; [| split; [| split; [| split ]]].
        --  assert (Hnin : ~ f2 \in name_in_fundefs B1 :|: (S \\ S1)).
            { intros Hc. eapply Hd3. constructor; eauto.
              eexists f1. split. eexists.
              eapply lifted_name_eq. eassumption.
              eapply lifted_name_eq. eassumption.
              simpl.
              eapply Included_trans; [| reflexivity | eassumption ]. xsets. }
            erewrite <- Add_functions_sig_eq; [ | eassumption | ].
            rewrite def_funs_neq. eassumption.
            ++ intros Hc.
               eapply Fundefs_lambda_lift_name_in_fundefs2 in Hc; [| eassumption ].
               eapply Add_functions_name_in_fundefs in Hc; [| eassumption | eassumption ].
               eapply Hd1. constructor. eexists f2. split; [| reflexivity ]. do 2 right.
               eexists. split. eexists.
               eapply lifted_name_eq. eassumption.
               eapply lifted_name_eq. eassumption.
               inv Hc; eauto.
            ++ eassumption.
        -- eassumption.
        -- erewrite <- Add_functions_map_eq; [| eassumption |]. eapply get_list_fundefs. eassumption.
           ++ intros y Hin Hin'. eapply FromList_map_image_FromList in Hin.
              eapply Fundefs_lambda_lift_name_in_fundefs2 in Hin'; [| eassumption ].
              rewrite Add_functions_name_in_fundefs in Hin'; [| eassumption | eassumption ].
              eapply Hd1. constructor. eapply image_monotonic; [| eassumption ].
              eapply Included_Union_preserv_r. eapply Included_Union_preserv_l.
              intros x Hinx. do 4 eexists. split; eassumption. left. now inv Hin'.
           ++ eapply Disjoint_Included; [| | eapply Hd5 ]; sets.
              intros z Hin. do 4 eexists. eauto.
        -- eassumption.
        -- eassumption.
  Qed.



  Lemma bound_var_occurs_free_Eletapp_Included x f t ys e :
    (bound_var e :|: occurs_free e) \subset
                                    (bound_var (Eletapp x f t ys e) :|: occurs_free (Eletapp x f t ys e)).
  Proof with eauto with Ensembles_DB.
    repeat normalize_bound_var. repeat normalize_occurs_free.
    rewrite <- Union_assoc.
    apply Included_Union_compat...
    eapply Included_trans. now apply occurs_free_Eletapp_Included with (ft := t).
    normalize_occurs_free...
  Qed.


  Lemma Funs_inv_def_funs k rho rho' sig zeta B B1 B2 f1 f2 S S' :
    Fundefs_lambda_lift3 zeta sig B B1 S B2 S' ->
    Disjoint _ (name_in_fundefs B1) (Funs zeta :|: LiftedFuns zeta :|: FunsFVs zeta) ->
    Disjoint _ (name_in_fundefs B1) (image sig (FunsFVs zeta :|: LiftedFuns zeta)) ->
    Funs_inv k rho rho' sig zeta ->
    Funs_inv k (def_funs f1 B1 rho rho) (def_funs f2 B2 rho' rho') (extend_fundefs sig B1 B1) zeta.
  Proof.
    intros Hll. revert f1 f2. induction Hll; intros f1 f2 Hd Hd' Hfuns; simpl in *.
    eapply Funs_inv_set; [ | | | | eapply IHHll; try eassumption ].
    - eapply Disjoint_In_l with (s1 := [set f]); [| reflexivity ].
      eapply Disjoint_Included; [| | eapply Hd ]. sets. sets.
    - eapply Disjoint_In_l with (s1 := [set f]); [| reflexivity ].
      eapply Disjoint_Included; [| | eapply Hd ]. sets. sets.
    - eapply Disjoint_In_l with (s1 := [set f]); [| reflexivity ].
      eapply Disjoint_Included; [| | eapply Hd ]. sets. sets.
    - rewrite extend_fundefs_image; [| eapply Disjoint_sym ].
      eapply Disjoint_In_l with (s1 := [set f]); [| reflexivity ]. now sets.
      eapply Disjoint_Included; [| | eapply Hd ]; sets.
    - sets.
    - sets.
    - eassumption.
  Qed.

  Lemma Funs_inv_f_eq_subdomain (k : nat) (rho rho' : env) (sig sig' : var -> var)
        (zeta : var -> option (var * fun_tag * list var)) :
    f_eq_subdomain (FunsFVs zeta :|: LiftedFuns zeta) sig sig' ->
    Funs_inv k rho rho' sig zeta ->
    Funs_inv k rho rho' sig' zeta.
  Proof.
    intros Heq Hin. unfold Funs_inv in *. intros.
    rewrite <- Heq. erewrite <- map_f_eq_subdomain.
    now eauto.
    eapply f_eq_subdomain_antimon; eauto.
    eapply Included_Union_preserv_l.

    intros z Hinz. do 4 eexists. split; eauto.

    right. eexists. split. unfold Funs. eexists. eapply lifted_name_eq. eassumption.
    eapply lifted_name_eq. eassumption.
  Qed.


  Lemma Funs_inv_def_funs_alt k rho rho' sig zeta B B1 B2 f1 f2 S S' :
    Fundefs_lambda_lift3 zeta sig B B1 S B2 S' ->
    Disjoint _ (name_in_fundefs B1) (Funs zeta :|: LiftedFuns zeta :|: FunsFVs zeta) ->
    Disjoint _ (name_in_fundefs B1) (image sig (FunsFVs zeta :|: LiftedFuns zeta)) ->
    Funs_inv k rho rho' sig zeta ->
    Funs_inv k (def_funs f1 B1 rho rho) (def_funs f2 B2 rho' rho') sig zeta.
  Proof.
    intros.
    eapply Funs_inv_f_eq_subdomain.
    2:{ eapply Funs_inv_def_funs; eauto. }
    intros x Hinx.
    rewrite extend_fundefs_neq. reflexivity.
    intros Hc. eapply H0. constructor. eassumption.
    inv Hinx; eauto.
  Qed.

  Lemma Fundefs_lambda_lift3_name_in_fundefs zeta sig B B1 S B2 S' :
    Fundefs_lambda_lift3 zeta sig B B1 S B2 S' ->
    name_in_fundefs B1 <--> name_in_fundefs B2.
  Proof.
    intros Hf. induction Hf; try reflexivity.
    simpl. eapply Same_set_Union_compat. reflexivity. eassumption.
  Qed.

  Lemma Fundefs_lambda_lift_correct3 k rho rho' B1 B2 sig zeta S S' e:
    (* The IH for expressions *)
    (forall m : nat,
        m < k ->
        forall (e : exp) (rho rho' : env)
               (zeta : var -> option (var * fun_tag * list var))
               (sig : var -> var) (S : Ensemble var) (e' : exp)
               (S' : Ensemble var),
          unique_bindings e ->
          Disjoint var (image sig (Union _ (Union _ (occurs_free e) (FunsFVs zeta)) (LiftedFuns zeta)))
                   (Union var S (bound_var e)) ->
          Disjoint var S (Union var (bound_var e) (occurs_free e)) ->
          Disjoint var (LiftedFuns zeta) (Union _ S (bound_var e)) ->
          Disjoint var (Funs zeta) (Union _ S (bound_var e)) ->
          Disjoint var (FunsFVs zeta) (Union _ S (bound_var e)) ->
          Disjoint _ (bound_var e) (occurs_free e) ->
          binding_in_map (image sig (Union _ (Union _ (occurs_free e) (FunsFVs zeta)) (LiftedFuns zeta))) rho' ->
          preord_env_P_inj cenv PG (occurs_free e) m sig rho rho' ->
          Funs_inv m rho rho' sig zeta ->
          Exp_lambda_lift zeta sig e S e' S' ->
          preord_exp cenv (P1 0) PG m (e, rho) (e', rho')) ->

    (* Unique bindings *)
    unique_bindings_fundefs B1 ->

    (* The image of sig is neither in the free set nor in the set of bound variables *)
    Disjoint var (image sig (Union _ (occurs_free (Efun B1 e)) (Union _ (FunsFVs zeta) (LiftedFuns zeta))))
             (Union var S (bound_var_fundefs B1)) ->

    (* The free set is disjoint from the set of bound and free variables *)
    Disjoint var S (Union var (bound_var_fundefs B1) (occurs_free (Efun B1 e))) ->

    (* The names of lifted functions is neither in the free set nor in the set of bound variables*)
    Disjoint var (LiftedFuns zeta) (Union _ S (bound_var_fundefs B1)) ->

    (* The domain of zeta is disjoint with the bound variables *)
    Disjoint var (Funs zeta) (Union _ S (bound_var_fundefs B1)) ->

    (* The free variables of the funs in zeta are disjoint from the bound variables *)
    Disjoint var (FunsFVs zeta) (Union _ S (bound_var_fundefs B1)) ->

    (* The bound variables and the free variables are disjoint *)
    Disjoint _ (bound_var_fundefs B1) (occurs_free_fundefs B1) ->

    (* The free variables are in the environment *)
    binding_in_map (image sig (Union _ (occurs_free (Efun B1 e)) (Union _ (FunsFVs zeta) (LiftedFuns zeta))))
                   rho' ->

    (** The invariant holds for the initial environments **)
    preord_env_P_inj cenv PG (occurs_free (Efun B1 e)) k sig rho rho' ->
    Funs_inv k rho rho' sig zeta ->

    (forall x, x \in name_in_fundefs B1 -> sig x = x) ->

    Fundefs_lambda_lift3 zeta sig B1 B1 S B2 S' ->


    (** The invariants hold for the final environments **)
    preord_env_P_inj cenv PG (occurs_free (Efun B1 e) :|: name_in_fundefs B1)
                     k sig (def_funs B1 B1 rho rho) (def_funs B2 B2 rho' rho'). (* /\ *)
    (* Funs_inv k (def_funs B1 B1 rho rho) (def_funs B2 B2 rho' rho') (extend_fundefs sig B1 B1) zeta. *)
  Proof with now eauto with Ensembles_DB.
    revert rho rho' B1 B2 sig zeta  S S' e.
    induction k as [k IHk] using lt_wf_rec1;
      intros rho rho' B1 B2 sig zeta  S1 S2 e IHe Hun Hd1 Hd2 Hd3 Hd4 Hd5 Hd6 Hbin Henv Hfinv Hfeq Hllfuns.
    assert
      (HB1 : forall j, j < k ->
                       preord_env_P_inj cenv PG (occurs_free (Efun B1 e) :|: name_in_fundefs B1)
                                        j sig (def_funs B1 B1 rho rho) (def_funs B2 B2 rho' rho')). (*  /\ *)
                       (* Funs_inv j (def_funs B1 B1 rho rho) (def_funs B2 B2 rho' rho') (extend_fundefs sig B1 B1) zeta) *)
    { intros j leq. eapply IHk; last (now apply Hllfuns); eauto.
      - intros. eapply IHe; eauto. lia.
      - eapply preord_env_P_inj_monotonic; [| eassumption]. lia.
      - eapply Funs_inv_monotonic. eassumption. lia. }

    intros x Hxin v Hget. destruct (Decidable_name_in_fundefs B1) as [Hdec]. destruct (Hdec x); clear Hdec.
    - (* x is in B1 *)
      edestruct name_in_fundefs_find_def_is_Some as (ft & xs1 & e1 & Hfdef1); [ eassumption | ].
      edestruct Fundefs_lambda_lift_find_def3 as
          (e2 & Q1 & Q2 & Hfdef2 & Hsub & Hllexp); [ eassumption | eassumption | ].
      (* rewrite extend_fundefs_eq; [| eassumption ].  *)
      eexists. split. rewrite def_funs_eq. reflexivity. eapply fun_in_fundefs_name_in_fundefs.
      eapply find_def_correct. rewrite Hfeq. eassumption. eassumption.
      rewrite def_funs_eq in Hget; [| eassumption ]. inv Hget.
      rewrite preord_val_eq. intros vs1 vs2 j t xs1' e1' rhoc1 Hleq' Hfd Hset.
      repeat subst_exp. edestruct (set_lists_length3 (def_funs B2 B2 rho' rho') xs1' vs2) as [rho2 Hset2].
      rewrite <- Hleq'. eapply set_lists_length_eq. now eauto.
      do 3 eexists. split. rewrite Hfeq; eassumption.
      split. now eauto. intros Hlt Hall.

      assert (Hinxs : FromList xs1' \subset bound_var_fundefs B1 \\ name_in_fundefs B1).
      { eapply Included_Setminus.
        eapply unique_bindings_fun_in_fundefs. eapply find_def_correct; eassumption. eassumption.
        eapply Included_trans; [| eapply fun_in_fundefs_bound_var_fundefs; eapply find_def_correct; eassumption ]. sets. }
      assert (Hinxs' : FromList xs1' \subset bound_var_fundefs B1).
      { eapply Included_trans. eassumption. sets. }
      assert (Hine : bound_var e1' \subset bound_var_fundefs B1 \\ name_in_fundefs B1).
      { eapply Included_Setminus.
        eapply unique_bindings_fun_in_fundefs. eapply find_def_correct; eassumption. eassumption.
        eapply Included_trans; [| eapply fun_in_fundefs_bound_var_fundefs; eapply find_def_correct; eassumption ]. sets. }
      assert (Hine' : bound_var e1' \subset bound_var_fundefs B1).
      { eapply Included_trans. eassumption. sets. }
      assert (Hssub : S2 \subset S1).
      { eapply Fundefs_Lambda_lift_free_set_Included3. eassumption. }
      assert (Hssub' : Q2 \subset Q1).
      { eapply Exp_Lambda_lift_free_set_Included. eassumption. }
      assert (Hfree : occurs_free e1' \\ FromList xs1' \\ name_in_fundefs B1 \subset occurs_free_fundefs B1).
      { do 2 eapply Setminus_Included_Included_Union. eapply Included_trans. eapply occurs_free_in_fun.
        apply find_def_correct. eassumption. sets. }
      assert (Hname : name_in_fundefs B1 \subset bound_var_fundefs B1).
      { eapply name_in_fundefs_bound_var_fundefs. }

      eapply preord_exp_post_monotonic. eapply Hinc.
      eapply IHe; last eassumption.
      + eassumption.
      + eapply unique_bindings_fun_in_fundefs.
        eapply find_def_correct. eassumption. eassumption.
      + eapply Disjoint_Included_l.
        eapply Included_trans. eapply image_extend_lst_Included. reflexivity.
        eapply Included_Union_compat. eapply image_extend_fundefs. reflexivity.
        rewrite !Setminus_Union_distr. eapply Union_Disjoint_l. eapply Union_Disjoint_l.
        * eapply Disjoint_Included; [| | eapply Hd1 ]. now xsets. normalize_occurs_free. xsets.
        * eapply Union_Disjoint_r. eapply Disjoint_sym. eapply Disjoint_Included; [| | eapply Hd2 ].
          now sets. eassumption. eapply Disjoint_Included_r. eapply Hine. now sets.
        * eapply Union_Disjoint_r. eapply Disjoint_sym. eapply Disjoint_Included; [| | eapply Hd2 ]. now sets.
          eassumption. eapply Disjoint_sym. eapply unique_bindings_fun_in_fundefs. eapply find_def_correct. eassumption.
          eassumption.
      + eapply Disjoint_Included_r. eapply bound_var_occurs_free_in_fun_Included. eapply find_def_correct. eassumption.
        eapply Disjoint_Included; [| | eapply Hd2 ]. normalize_occurs_free. now sets.
        eassumption.
      + xsets.
      + xsets.
      + xsets.
      + eapply fun_in_fundefs_Disjoint_bound_Var_occurs_free. eapply find_def_correct. eassumption.
        eassumption. eassumption.
      + eapply binding_in_map_antimon.
        eapply Included_trans. eapply image_extend_lst_Included. reflexivity.
        eapply Included_Union_compat; [| reflexivity ]. eapply image_extend_fundefs.
        rewrite Union_commut. eapply binding_in_map_set_lists; [| eassumption ].
        rewrite Union_commut. rewrite Fundefs_lambda_lift3_name_in_fundefs at 1; [| eassumption ].
        eapply binding_in_map_def_funs.
        eapply binding_in_map_antimon; [| eassumption ]. normalize_occurs_free.
        eapply image_monotonic. rewrite !Setminus_Union_distr. now xsets.
      + assert (Hnd1': NoDup xs1').
        { eapply unique_bindings_fun_in_fundefs. eapply find_def_correct. eapply Hfdef1. eassumption. }

        eapply preord_env_P_inj_set_lists_alt;
          [| eassumption | eassumption | eassumption | now eauto | | now eauto | now eauto ].
        * eapply preord_env_P_inj_antimon.
          eapply preord_env_P_inj_f_eq_subdomain.
          2:{ intros z Hin. destruct (Decidable_name_in_fundefs B1). destruct (Dec z).
              rewrite Hfeq. rewrite extend_fundefs_eq. reflexivity.
              eassumption. eassumption.
              simpl. rewrite extend_fundefs_neq. reflexivity. eassumption. }

          eapply IHk; [ eassumption | | eassumption | | | | | | | | | | | eassumption ]; try eassumption.
          -- intros. eapply IHe; eauto. lia.
          -- eapply preord_env_P_inj_monotonic; [| eassumption ]. lia.
          -- eapply Funs_inv_monotonic. eassumption. lia.
          -- normalize_occurs_free. eapply Setminus_Included_Included_Union. eapply Included_trans.
             eapply occurs_free_in_fun. eapply find_def_correct. eassumption. sets.
        * eapply Disjoint_Included_l. eapply image_extend_fundefs. eapply Union_Disjoint_l.
          eapply Disjoint_Included; [| | eapply Hd1 ]. now sets. normalize_occurs_free...
          eapply Disjoint_Included_r. eapply Hinxs. xsets.
      + eapply Funs_inv_set_lists; try now eauto; try xsets.
        eapply Funs_inv_def_funs; [ eassumption | | | ].
        * now xsets.
        * eapply Disjoint_sym. eapply Disjoint_Included; [| | eapply Hd1 ]...
        * eapply Funs_inv_monotonic. eassumption. lia.
        * xsets.
          eapply Disjoint_Included_l.
          eapply image_extend_fundefs. eapply Union_Disjoint_l.
          -- eapply Disjoint_Included; [| | eapply Hd1 ]. now xsets. now xsets.
          -- eapply Disjoint_Included_r. eapply Hinxs. now sets.
    - (* x is not in B1 *)
      inv Hxin; [| contradiction ].
      rewrite def_funs_neq; eauto. eapply Henv. eassumption.
      rewrite def_funs_neq in Hget; eauto.
      intros Hc. eapply Fundefs_lambda_lift3_name_in_fundefs in Hc; [| eassumption ].
      eapply Hd1. constructor. eapply In_image. left. eassumption. right.
      eapply name_in_fundefs_bound_var_fundefs. eassumption.
  Qed.


  Lemma Funs_inv_Eletapp k x f ft ys e f' ft' fvs e' sig zeta rho rho' :
    (forall (m : nat) (v1 v2 : val),
        m < k ->
        preord_val cenv PG m v1 v2 -> preord_exp cenv (P1 0) PG m (e, M.set x v1 rho) (e', M.set x v2 rho')) ->
    Funs_inv k rho rho' sig zeta ->
    preord_env_P_inj cenv PG (occurs_free (Eletapp x f ft ys e)) k sig rho rho' ->

    zeta f = Some (f', ft', fvs) ->
    preord_exp cenv (P1 0) PG k (Eletapp x f ft ys e, rho) (Eletapp x (sig f') ft' (map sig (ys ++ fvs)) e', rho').
  Proof.
    intros Hyp Hfuns Henv Hzeq v1 c1 t1 Hleq Hstep. inv Hstep.
    - eexists OOT, c1, zero. split; [| split; eauto ].
      + econstructor. eassumption.
      + eapply lt_one in H.
        eapply HPost_OOT; eauto. subst. eapply zero_one_lt.
      + simpl; eauto.
    - inv H.
      + edestruct preord_env_P_inj_get_list_l as [vs' [Hgetl' Hprevs]]; try eassumption.
        normalize_occurs_free. now sets.
        assert (Hlen := Forall2_length Hprevs).

        edestruct Hfuns with (j := k - 1) as (rhoc & rhoc' & B2 & f2 & xs2 & e2 & vs2' & Hget2 & Hf2 & Hgl2  & Hset2 & Hyp2);
          [ eassumption | eassumption | eassumption | eassumption | now eauto | ].

        rewrite !to_nat_add in Hleq. unfold one in Hleq. erewrite to_nat_one in Hleq.

        edestruct Hyp2 as (v2' & c2' & t2' & Hstep2' & Hpost' & Hval'); [  | | | eassumption | ]. simpl in *.
        lia.

        eapply Forall2_monotonic; [| eassumption ]. intros. eapply preord_val_monotonic. eassumption. lia.

        lia.
        destruct v2'; try (simpl in *; contradiction).

        edestruct Hyp as (v2 & c2 & t2 & Hstep2 & Hpost & Hval); [ | eassumption | | eassumption | ].
        simpl in *; lia. lia.
        exists v2, (c2' <+> c2 <+> (one (Eletapp x (sig f') ft' (map sig (ys ++ fvs)) e'))),
        (t2' <+> t2 <+> (one (Eletapp x (sig f') ft' (map sig (ys ++ fvs)) e'))).
        split; [| split ]; eauto.
        * econstructor 2.
          econstructor; try eassumption. rewrite map_app. eapply get_list_app; eauto.
          now eauto.
        * eapply preord_res_monotonic. eassumption.
          rewrite !to_nat_add. unfold one. rewrite to_nat_one. lia.
      + edestruct preord_env_P_inj_get_list_l as [vs' [Hgetl' Hprevs]]; try eassumption.
        normalize_occurs_free. now sets.
        assert (Hlen := Forall2_length Hprevs).

        edestruct Hfuns with (j := k - 1) as (rhoc & rhoc' & B2 & f2 & xs2 & e2 & vs2' & Hget2 & Hf2 & Hgl2 & Hset2 & Hyp2);
          [ eassumption | eassumption | eassumption | eassumption | now eauto | ].

        rewrite !to_nat_add in Hleq. unfold one in Hleq. erewrite to_nat_one in Hleq.
        edestruct Hyp2 as (v2' & c2' & t2' & Hstep2' & Hpost' & Hval'); [  | | | eassumption | ]. simpl in *.

        lia.
        eapply Forall2_monotonic; [| eassumption ]. intros. eapply preord_val_monotonic. eassumption. lia.
        simpl in *; lia.
        destruct v2'; try (simpl in *; contradiction).
        exists OOT. do 2 eexists.
        split; [| split ].
        * eapply BStepf_run. eapply BStept_letapp_oot.
          eassumption. rewrite map_app. eapply get_list_app; eauto. eassumption.
          now eauto. eassumption.
        * repeat subst_exp. simpl. rewrite !map_app. eapply PG_P_local_steps_let_app_OOT. eassumption.
          eassumption. eassumption. eassumption.
        * eassumption.

          Unshelve. exact []. exact []. eauto.
    Qed.


  Lemma Funs_inv_Eapp k f ft ys f' ft' fvs sig zeta rho rho' :
    Funs_inv k rho rho' sig zeta ->
    preord_env_P_inj cenv PG (occurs_free (Eapp f ft ys)) k sig rho rho' ->

    zeta f = Some (f', ft', fvs) ->
    preord_exp cenv (P1 0) PG k (Eapp f ft ys, rho) (Eapp (sig f') ft' (map sig (ys ++ fvs)), rho').
  Proof.
    intros Hfuns Henv Hzeq v1 c1 t1 Hleq Hstep. inv Hstep.
    - eexists OOT, c1, <0>. split; [| split; eauto ].
      + econstructor. eassumption.
      + eapply lt_one in H.
        eapply HPost_OOT; eauto. subst. eapply zero_one_lt.
      + simpl; eauto.
    - inv H. edestruct preord_env_P_inj_get_list_l as [vs' [Hgetl' Hprevs]]; try eassumption.
      normalize_occurs_free. now sets.
      assert (Hlen := Forall2_length Hprevs).

      edestruct Hfuns with (j := k - 1) as (rhoc & rhoc' & B2 & f2 & xs2 & e2 & vs2' & Hget2 & Hf2 & Hgl2 & Hset2 & Hyp2);
        [ eassumption | eassumption | eassumption | eassumption | now eauto | ].

      rewrite !to_nat_add in Hleq. unfold one in Hleq. erewrite to_nat_one in Hleq.

     edestruct Hyp2 as (v2' & c2' & t2' & Hstep2' & Hpost' & Hval'); [ simpl in *; lia | | | eassumption | ].
     eapply Forall2_monotonic; [| eassumption ]. intros. eapply preord_val_monotonic. eassumption. lia. simpl in *; lia.
     repeat subst_exp.

     exists v2'. do 2 eexists.
     split; [| split ].
     + econstructor 2. econstructor; eauto.
       rewrite list_append_map. eapply get_list_app. eassumption. eassumption.
     + eapply PG_P_local_steps_app. eassumption. eassumption. eassumption. eassumption.
     + eapply preord_res_monotonic. eassumption. rewrite to_nat_add. unfold one. rewrite to_nat_one.
       simpl in *; lia.

      Unshelve. eassumption. eassumption. eassumption. eassumption.
  Qed.


  Lemma Exp_lambda_lift_correct k rho rho' zeta sig e S e' S' :
    (* The expression has unique bindings *)
    unique_bindings e ->
    (* The new free variable names are fresh *)
    Disjoint var (image sig (Union _ (Union _ (occurs_free e) (FunsFVs zeta)) (LiftedFuns zeta)))
             (Union var S (bound_var e)) ->
    (* The fresh set is fresh *)
    Disjoint _ S (Union _ (bound_var e) (occurs_free e)) ->
    (* The new function names for lifted functions are fresh *)
    Disjoint _ (LiftedFuns zeta) (Union _ S (bound_var e)) ->
    (* The names of the (already defined) functions are disjoint from the bound variables of the expression *)
    Disjoint var (Funs zeta) (Union _ S (bound_var e)) ->
    (* The free variables of a function are disjoint from the bound variables of the expression *)
    Disjoint var (FunsFVs zeta) (Union _ S (bound_var e)) ->
    (* The bound variables of the expression are disjoint from the free variables *)
    Disjoint _ (bound_var e) (occurs_free e) ->
    (* All the free variables are in the environment *)
    binding_in_map (image sig (Union _ (Union _ (occurs_free e) (FunsFVs zeta)) (LiftedFuns zeta))) rho' ->
    (* The environments are related *)
    preord_env_P_inj cenv PG (occurs_free e) k sig rho rho' ->
    (* The invariant about lifted functions hold*)
    Funs_inv k rho rho' sig zeta ->
    (* e' is the translation of e*)
    Exp_lambda_lift zeta sig e S e' S' ->
    (* e and e' are related *)
    preord_exp cenv (P1 0) PG k (e, rho) (e', rho').
   Proof with now eauto with Ensembles_DB.
    revert e rho rho' zeta sig S e' S'; induction k as [k IHk] using lt_wf_rec1; edestruct (Hcompat 0).
    induction e using exp_ind';
      intros rho rho' zeta sig S e' S' Hun Him Hf Hlf Hfun Hfvs HD Hin Henv Hinv Hll;
      inv Hll.
    - inv Hun. eapply preord_exp_constr_compat.
      + eapply HPost_con.
      + eauto. (* post *)
      + eapply Forall2_preord_var_env_map. eassumption.
        normalize_occurs_free...
      + intros m vs1 vs2 Hall Hlt. eapply IHk; [ eassumption | eassumption | | | | | | | | | | eassumption ].
        * eapply Disjoint_Included_l. now eapply image_extend_Included'.
          eapply Union_Disjoint_l.
          rewrite occurs_free_Econstr in Him.
          eapply Disjoint_Included; [ | | now apply Him ].
          normalize_bound_var...
          apply image_monotonic.
          rewrite !Setminus_Union_distr...
          eapply Union_Disjoint_r.
          eapply Disjoint_Included_l_sym; [| eassumption ]...
          eapply Disjoint_Singleton_l. intros Hc. now eauto.
        * eapply Disjoint_Included_r; [| eassumption ].
          now apply bound_var_occurs_free_Econstr_Included.
        * repeat normalize_bound_var_in_ctx...
        * repeat normalize_bound_var_in_ctx...
        * repeat normalize_bound_var_in_ctx...
        * eapply Disjoint_Included_r. now apply occurs_free_Econstr_Included.
          eapply Union_Disjoint_r.
          eapply Disjoint_Included_l ; [| now apply HD].
          normalize_bound_var... now apply Disjoint_Singleton_r.
        * eapply binding_in_map_antimon; [| eapply binding_in_map_set; eassumption ].
          eapply Included_trans. eapply image_extend_Included'.
          eapply Included_Union_compat; [| reflexivity ].
          eapply image_monotonic. rewrite !Setminus_Union_distr.
          normalize_occurs_free...
        * eapply preord_env_P_inj_set_alt.
          eapply preord_env_P_inj_antimon.
          eapply preord_env_P_inj_monotonic; [| eassumption]. lia.
          normalize_occurs_free...
          rewrite preord_val_eq. constructor. reflexivity.
          eassumption.
          intros Hc. eapply Him. constructor; eauto.
          eapply image_monotonic; [| eassumption ].
          normalize_occurs_free...
        * eapply Funs_inv_set.
          intros Hc. eapply Hfun. now constructor; eauto.
          intros Hc. eapply Hlf. now constructor; eauto.
          intros Hc. eapply Hfvs. now constructor; eauto.
          intros Hc. eapply Him. constructor; eauto.
          eapply image_monotonic; [| eassumption ]...
          eapply Funs_inv_monotonic. eassumption. lia.
    - eapply preord_exp_case_nil_compat. eauto.
    - inv Hun. edestruct Exp_lambda_lift_Ecase as [P'' [Heq Hall]]; eauto. inv Heq.
      eapply preord_exp_case_cons_compat; eauto.
      + intros m Hlt. eapply IHk; eauto.
        * eapply Disjoint_Included; [| | now apply Him ].
          normalize_bound_var...
          apply image_monotonic. normalize_occurs_free...
        * eapply Disjoint_Included_r; [ | now eapply Hf ].
          normalize_occurs_free. normalize_bound_var...
        * eapply Disjoint_Included_r; [ | now eapply Hlf ].
          normalize_bound_var...
        * eapply Disjoint_Included_r; [ | now eapply Hfun ].
          normalize_bound_var...
        * eapply Disjoint_Included_r; [ | now eapply Hfvs ].
          normalize_bound_var...
        * eapply Disjoint_Included; [ | | now eapply HD ].
          normalize_occurs_free... normalize_bound_var...
        * eapply binding_in_map_antimon; [| eassumption ].
          normalize_occurs_free...
        * eapply preord_env_P_inj_antimon. eapply preord_env_P_inj_monotonic; [| eassumption ]. lia.
          normalize_occurs_free...
        * eapply Funs_inv_monotonic. eassumption. lia.
      + assert (Hinc' : Included _ S'0 S).
        { eapply Exp_Lambda_lift_free_set_Included; eauto. }
        eapply IHe0; eauto.
        * eapply Disjoint_Included; [| | now apply Him ].
          normalize_bound_var...
          apply image_monotonic. normalize_occurs_free...
        * eapply Disjoint_Included; [ | eassumption | now eapply Hf ].
          normalize_occurs_free. normalize_bound_var...
        * eapply Disjoint_Included_r; [ | now eapply Hlf ].
          normalize_bound_var...
        * eapply Disjoint_Included_r; [ | now eapply Hfun ].
          normalize_bound_var...
        * eapply Disjoint_Included_r; [ | now eapply Hfvs ].
          normalize_bound_var...
        * eapply Disjoint_Included; [ | | now eapply HD ].
          normalize_occurs_free... normalize_bound_var...
        * eapply binding_in_map_antimon; [| eassumption ].
          normalize_occurs_free...
        * eapply preord_env_P_inj_antimon. eassumption.
          normalize_occurs_free...
    - inv Hun. eapply preord_exp_proj_compat.
      + eapply HPost_proj.
      + eauto. (* post *)
      + eapply Henv. eauto.
      + intros m vs1 vs2 Hlt Hall. eapply IHk; [ eassumption | eassumption | | | | | | | | | | eassumption ].
        * eapply Disjoint_Included_l. now eapply image_extend_Included'.
          eapply Union_Disjoint_l.
          rewrite occurs_free_Eproj in Him.
          eapply Disjoint_Included; [ | | now apply Him ].
          normalize_bound_var...
          apply image_monotonic. rewrite !Setminus_Union_distr...
          eapply Union_Disjoint_r.
          eapply Disjoint_Included_l_sym; [| eassumption ]...
          now eapply Disjoint_Singleton_l.
        * eapply Disjoint_Included_r; [| eassumption ].
          now apply bound_var_occurs_free_Eproj_Included.
        * repeat normalize_bound_var_in_ctx...
        * repeat normalize_bound_var_in_ctx...
        * repeat normalize_bound_var_in_ctx...
        * eapply Disjoint_Included_r. now apply occurs_free_Eproj_Included.
          eapply Union_Disjoint_r.
          eapply Disjoint_Included_l ; [| now apply HD].
          normalize_bound_var... now apply Disjoint_Singleton_r.
        * eapply binding_in_map_antimon; [| eapply binding_in_map_set; eassumption ].
          eapply Included_trans. eapply image_extend_Included'.
          eapply Included_Union_compat; [| reflexivity ].
          eapply image_monotonic. rewrite !Setminus_Union_distr.
          normalize_occurs_free...
        * eapply preord_env_P_inj_set_alt.
          eapply preord_env_P_inj_antimon. eapply preord_env_P_inj_monotonic; [| eassumption ]. lia.
          normalize_occurs_free... eassumption.
          intros Hc. eapply Him. constructor; eauto.
          eapply image_monotonic; [| eassumption ].
          normalize_occurs_free...
        * eapply Funs_inv_set.
          intros Hc. eapply Hfun. now constructor; eauto.
          intros Hc. eapply Hlf. now constructor; eauto.
          intros Hc. eapply Hfvs. now constructor; eauto.
          intros Hc. eapply Him. constructor; eauto.
          eapply image_monotonic; [| eassumption ]...
          eapply Funs_inv_monotonic. eassumption. lia.
    - (* Eletapp known *)
      eapply Funs_inv_Eletapp; [| eassumption | eassumption | eassumption ].
      intros m v1 v2 Hlt Hval. inv Hun.
      eapply IHk; [ eassumption | eassumption | | | | | | | | | | eassumption ].
      * eapply Disjoint_Included_l. now eapply image_extend_Included'.
        eapply Union_Disjoint_l. rewrite occurs_free_Eletapp in Him.
        eapply Disjoint_Included; [ | | now apply Him ].
        normalize_bound_var...
        apply image_monotonic. rewrite !Setminus_Union_distr...
        eapply Union_Disjoint_r. eapply Disjoint_Included_l_sym; [| eassumption ]...
        now eapply Disjoint_Singleton_l.
      * eapply Disjoint_Included_r; [| eassumption ].
        now apply bound_var_occurs_free_Eletapp_Included.
      * repeat normalize_bound_var_in_ctx...
      * repeat normalize_bound_var_in_ctx...
      * repeat normalize_bound_var_in_ctx...
      * eapply Disjoint_Included_r. now apply occurs_free_Eletapp_Included.
        eapply Union_Disjoint_r.
        eapply Disjoint_Included_l ; [| now apply HD].
        normalize_bound_var... now apply Disjoint_Singleton_r.
      * eapply binding_in_map_antimon; [| eapply binding_in_map_set; eassumption ].
        eapply Included_trans. eapply image_extend_Included'.
        eapply Included_Union_compat; [| reflexivity ].
        eapply image_monotonic. rewrite !Setminus_Union_distr.
        normalize_occurs_free...
      * eapply preord_env_P_inj_set_alt.
        eapply preord_env_P_inj_antimon. eapply preord_env_P_inj_monotonic; [| eassumption ]. lia.
        normalize_occurs_free... eassumption.
        intros Hc. eapply Him. constructor; eauto.
        eapply image_monotonic; [| eassumption ].
        normalize_occurs_free...
      * eapply Funs_inv_set.
        intros Hc. eapply Hfun. now constructor; eauto.
        intros Hc. eapply Hlf. now constructor; eauto.
        intros Hc. eapply Hfvs. now constructor; eauto.
        intros Hc. eapply Him. constructor; eauto.
        eapply image_monotonic; [| eassumption ]...
        eapply Funs_inv_monotonic. eassumption. lia.
    - (* Eletapp unknown *)
      inv Hun. eapply preord_exp_letapp_compat.
      + eapply HPost_letapp. (* post *)
      + eapply HPost_letapp_OOT. (* post *)
      + eauto. (* post *)
      + eapply Henv. eapply occurs_free_Eletapp. auto.
      + eapply Forall2_preord_var_env_map. eassumption.
        normalize_occurs_free...
      + intros m vs1 vs2 Hall Hlt. eapply IHk; [ eassumption | eassumption | | | | | | | | | | eassumption ].
        * eapply Disjoint_Included_l. now eapply image_extend_Included'.
          eapply Union_Disjoint_l. rewrite occurs_free_Eletapp in Him.
          eapply Disjoint_Included; [ | | now apply Him ].
          normalize_bound_var...
          apply image_monotonic. rewrite !Setminus_Union_distr...
          eapply Union_Disjoint_r.
          eapply Disjoint_Included_l_sym; [| eassumption ]...
          eapply Disjoint_Singleton_l. intros Hc. now eauto.
        * eapply Disjoint_Included_r; [| eassumption ].
          now apply bound_var_occurs_free_Eletapp_Included.
        * repeat normalize_bound_var_in_ctx...
        * repeat normalize_bound_var_in_ctx...
        * repeat normalize_bound_var_in_ctx...
        * eapply Disjoint_Included_r. now apply occurs_free_Eletapp_Included.
          eapply Union_Disjoint_r.
          eapply Disjoint_Included_l ; [| now apply HD].
          normalize_bound_var... now apply Disjoint_Singleton_r.
        * eapply binding_in_map_antimon; [| eapply binding_in_map_set; eassumption ].
          eapply Included_trans. eapply image_extend_Included'.
          eapply Included_Union_compat; [| reflexivity ].
          eapply image_monotonic. rewrite !Setminus_Union_distr.
          normalize_occurs_free...
        * eapply preord_env_P_inj_set_alt.
          eapply preord_env_P_inj_antimon.
          eapply preord_env_P_inj_monotonic; [| eassumption]. lia.
          normalize_occurs_free... eassumption.
          intros Hc. eapply Him. constructor; eauto.
          eapply image_monotonic; [| eassumption ].
          normalize_occurs_free...
        * eapply Funs_inv_set.
          intros Hc. eapply Hfun. now constructor; eauto.
          intros Hc. eapply Hlf. now constructor; eauto.
          intros Hc. eapply Hfvs. now constructor; eauto.
          intros Hc. eapply Him. constructor; eauto.
          eapply image_monotonic; [| eassumption ]...
          eapply Funs_inv_monotonic. eassumption. lia.
    - (* Efun 2 *)
      assert (Hinc' : Included _ S'' S).
      { eapply Included_trans.
        now eapply Fundefs_Lambda_lift_free_set_Included2; eauto.
        now eapply Add_functions_free_set_Included; eauto. }
      assert (Hinc'' : Included _ S''' S).
      { eapply Included_trans. eapply Make_wrappers_free_set_Included; eassumption. eassumption. }
      assert (Hinc''' : Included _ S''' S'0).
      { eapply Included_trans. eapply Make_wrappers_free_set_Included; eassumption.
        eapply Fundefs_Lambda_lift_free_set_Included2. eassumption. }

      repeat normalize_bound_var_in_ctx.
      inv Hun. eapply preord_exp_fun_compat; [  now eauto | now eapply HPost_fun' | ].
      replace 1 with (0 + 1) by lia.
      eapply ctx_to_rho_preord_exp with (C := Efun1_c fds Hole_c).
      eassumption. eassumption. eassumption.
      intros. eapply P1_ctx_r; eauto.
      (* ctx_to_rho *) econstructor. now econstructor.

      rewrite occurs_free_Efun in Hf, Him, HD.
      assert (Hs : S'0 \subset S).
      { eapply Add_functions_free_set_Included. eassumption. }

      assert (Hfuns : Funs_inv k (def_funs f2 f2 rho rho) (def_funs B' B' rho' rho') σ' ζ').
      { eapply Fundefs_lambda_lift_correct2; last eassumption;
          [ eassumption | eassumption | | | | | | | | | eassumption | eassumption | | eassumption | reflexivity ].
        ++ eapply Disjoint_Included; [| | eapply Him ]. sets. xsets.
        ++ sets.
        ++ sets.
        ++ sets.
        ++ sets.
        ++ eapply Disjoint_Included; [| | eapply HD ]. sets. sets.
        ++ eapply binding_in_map_antimon; [| eassumption ]. normalize_occurs_free.
           xsets.
        ++ eapply preord_env_P_inj_antimon. eassumption. normalize_occurs_free...
        ++ eapply Included_trans. eassumption. sets. }

      eapply preord_exp_monotonic.
      eapply IHe; [ eassumption | | | | | | | | | | eassumption ].
      * eapply Disjoint_Included_l.
        eapply image_monotonic. eapply Included_Union_compat.
        eapply Included_Union_compat. reflexivity.
        eapply Add_functions_FunsFVs_Included_r. eassumption.
        eapply Add_functions_LiftedFuns_Included_r. eassumption.
        eapply Disjoint_Included_l. eapply Make_wrappers_image_Included. eassumption.
        eapply Union_Disjoint_l; [| eapply Union_Disjoint_r; xsets ].
        2:{ eapply Disjoint_Included; [ | | eapply Hf ]. sets. sets. }

        eapply Disjoint_Included_l. eapply Add_functions_image_Included. eassumption.

        eapply Union_Disjoint_l.
        -- eapply Disjoint_Included; [| | eapply Him ]. now sets. eapply image_monotonic.
           rewrite !Setminus_Union_distr. eapply Union_Included.
           eapply Union_Included. now sets.
           eapply Union_Included. now sets. eapply Included_trans.
           rewrite !Setminus_Union. eapply Setminus_Included. eapply Included_trans. eassumption. now sets.
           eapply Union_Included. now sets.
           rewrite Setminus_Union. rewrite Setminus_Included_Empty_set. now sets. now sets.
        -- eapply Union_Disjoint_l. eapply Disjoint_Included_l. eapply name_in_fundefs_bound_var_fundefs.
           eapply Disjoint_sym. eapply Union_Disjoint_l; [| now sets ].
           eapply Disjoint_Included_l. eapply Hinc''. now sets.
           xsets.
      * eapply Disjoint_Included; [| | now apply Hf ].
        rewrite <- bound_var_Efun, <- occurs_free_Efun. now apply bound_var_occurs_free_Efun_Included.
        eassumption.
      * eapply Disjoint_Included_l.
        eapply Add_functions_LiftedFuns_Included_r. eassumption.
        apply Union_Disjoint_l. repeat normalize_bound_var_in_ctx. now sets.
        apply Union_Disjoint_r. now sets. now xsets.
      * eapply Disjoint_Included_l.
        eapply Add_functions_Funs_Included. eassumption.
        apply Union_Disjoint_l. now eauto with Ensembles_DB.
        eapply Disjoint_Included_l_sym.
        now apply name_in_fundefs_bound_var_fundefs.
        eapply Union_Disjoint_l; eauto.
        eapply Disjoint_Included; [| | now apply Hf ]...
      * eapply Disjoint_Included_l.
        eapply Add_functions_FunsFVs_Included_r. eassumption.
        apply Union_Disjoint_l. now eauto with Ensembles_DB.
        eapply Disjoint_Included_l. eassumption.
        eapply Union_Disjoint_l; [| now xsets ].
        eapply Union_Disjoint_r.
        eapply Disjoint_sym. eapply Disjoint_Included; [ | | now apply Hf ]. now xsets. eassumption.
        eapply Disjoint_sym.
        eapply Disjoint_Included; [ | | now apply HD ]. now eauto with Ensembles_DB. now sets.
      * eapply Disjoint_Included_r.
        eapply occurs_free_Efun_Included with (B := f2). normalize_occurs_free.
        eapply Union_Disjoint_r. sets.
        eapply Disjoint_Included_r. now apply name_in_fundefs_bound_var_fundefs. eassumption.
      * eapply binding_in_map_antimon.
        eapply Included_Union_Setminus with (s2 := name_in_fundefs fds). now tci.
        rewrite Union_commut. eapply binding_in_map_def_funs.
        eapply binding_in_map_antimon.
        rewrite Make_wrappers_name_in_fundefs_image; [| eassumption | eassumption ].
        eapply functions.image_Setminus. now tci.
        rewrite <- Make_wrapper_image; [| eassumption | now sets ].

        eapply binding_in_map_antimon.
        eapply Included_Union_Setminus with (s2 := name_in_fundefs B'). now tci.
        rewrite Union_commut. eapply binding_in_map_def_funs.
        rewrite Fundefs_lambda_lift_name_in_fundefs2 with (B' := B'); [| eassumption ].
        rewrite Add_functions_name_in_fundefs; [| eassumption | eassumption ].

        eapply binding_in_map_antimon; [| eassumption ].
        eapply Setminus_Included_Included_Union. eapply Included_trans.
        eapply image_monotonic. eapply Included_Setminus_compat; [| reflexivity ].
        eapply Included_Union_compat. eapply Included_Union_compat. reflexivity.

        now eapply Add_functions_FunsFVs_Included_r; eauto.
        now eapply Add_functions_LiftedFuns_Included_r; eauto. rewrite !Union_assoc.
        rewrite Setminus_Union_distr.
        eapply Included_trans. eapply image_monotonic. eapply Included_Union_compat. reflexivity.
        eapply Setminus_Included. rewrite image_Union.
        rewrite Add_functions_image_LiftedFuns_Same_set with (S := S) (S' := S'0); [| | eassumption | eassumption ].
        eapply Union_Included; [ | now sets ].
        rewrite Add_functions_image_Disjoint_Same_set with (sig' := σ'); [| | eassumption ].
        normalize_occurs_free. eapply Included_Union_preserv_l. eapply image_monotonic. rewrite !Setminus_Union_distr.
        rewrite <- !Union_assoc. repeat (eapply Union_Included; [ now sets | ]).
        eapply Union_Included; [| now sets]. eapply Setminus_Included_Included_Union.
        eapply Included_trans. eassumption. now sets.
        eapply Union_Disjoint_r; [| now sets ].
        rewrite !Setminus_Union_distr.
        eapply Union_Disjoint_l; [| now sets ]. eapply Union_Disjoint_l.
        now xsets.
        eapply Disjoint_Included_l. eapply Setminus_Included_Included_Union. eapply Included_Union_preserv_l. eassumption.
        now xsets. eapply Disjoint_Included_r. eapply name_in_fundefs_bound_var_fundefs. now sets.
      * eapply Make_wrappers_correct; [ eassumption | | | | | eassumption | | ].
        -- eapply preord_env_P_inj_def_funs_neq_l; [| now sets ].
           eapply preord_env_P_inj_def_funs_neq_r. eapply preord_env_P_inj_f_eq_subdomain.
           eapply preord_env_P_inj_antimon. eassumption. normalize_occurs_free...
           eapply Add_functions_sig_eq_alt. eassumption. now xsets.
           rewrite Add_functions_image_Disjoint_Same_set; [| | eassumption ].

           rewrite Fundefs_lambda_lift_name_in_fundefs2 with (B' := B'); [| eassumption ].
           rewrite Add_functions_name_in_fundefs; [| eassumption | eassumption ].
           eapply Disjoint_Included; [ | | eapply Him ]. now sets. now sets.
           xsets.
        -- eassumption.
        -- eapply Disjoint_Included_l. eapply image_monotonic.
           eapply Included_Union_compat. reflexivity. now eapply Add_functions_FunsFVs_Included_r; eauto.
           eapply Disjoint_Included_l. eapply Add_functions_image_Included. eassumption.
           eapply Disjoint_Included_r. eapply Fundefs_Lambda_lift_free_set_Included2. eassumption.
           eapply Union_Disjoint_l.
           eapply Disjoint_Included_r. eapply Add_functions_free_set_Included. eassumption.
           eapply Disjoint_Included; [ | | eapply Him ]. now sets.
           eapply image_monotonic. eapply Setminus_Included_Included_Union. eapply Union_Included. now sets.
           eapply Union_Included. now sets. eapply Included_trans. eassumption. now xsets.
           eapply Union_Disjoint_l; [| now sets ].
           eapply Disjoint_sym. eapply Disjoint_Included; [| | eapply Hf ].
           eapply Included_trans. eapply name_in_fundefs_bound_var_fundefs. now sets.
           eapply Add_functions_free_set_Included. eassumption.
        -- eapply Disjoint_Included_l. eapply Included_Union_compat.
           now eapply Add_functions_LiftedFuns_Included_r; eauto.
           now eapply Add_functions_FunsFVs_Included_r; eauto.
           eapply Disjoint_Included_r. eapply Included_Union_compat. eapply Fundefs_Lambda_lift_free_set_Included2. eassumption.
           eapply name_in_fundefs_bound_var_fundefs.
           eapply Union_Disjoint_l; eapply Union_Disjoint_l. now sets. now xsets. now sets.
           eapply Disjoint_Included_l. eassumption.

           eapply Union_Disjoint_r. xsets.
           eapply Union_Disjoint_l.
           eapply Disjoint_sym. eapply Disjoint_Included; [| | eapply Hf ]. now xsets. eassumption.
           now xsets.
           eapply Union_Disjoint_l.
           eapply Disjoint_sym. eapply Disjoint_Included; [| | eapply HD ]; sets.
           now xsets.
        -- intros f Hfin. eexists. rewrite def_funs_eq. reflexivity. eassumption.
        -- rewrite Add_functions_name_in_fundefs; [| eassumption | eassumption ].
           intros y Hyin. unfold id. eapply Add_functions_same_name. now right; eauto. eassumption.
      * eapply Make_wrappers_Funs_inv; [ eassumption | eassumption | |].
        -- eapply Disjoint_Included_r. eapply name_in_fundefs_bound_var_fundefs.
           eapply Disjoint_Included_l. eapply Included_Union_compat.
           now eapply Add_functions_LiftedFuns_Included_r; eauto. now eapply Add_functions_FunsFVs_Included_r; eauto.
           eapply Union_Disjoint_l; eapply Union_Disjoint_l. now sets. now sets. now sets.
           eapply Disjoint_Included_l. eassumption.
           eapply Union_Disjoint_l; [| now xsets ].
           eapply Disjoint_sym. eapply Disjoint_Included; [| | eapply HD ]...
        -- eapply Disjoint_Included_l.
           eapply image_monotonic. eapply Included_Union_compat.
           now eapply Add_functions_LiftedFuns_Included_r; eauto.
           now eapply Add_functions_FunsFVs_Included_r; eauto.
           eapply Disjoint_Included_l. eapply Add_functions_image_Included. eassumption.
           eapply Disjoint_Included_r. eapply Included_trans. eapply Setminus_Included.
           eapply Fundefs_Lambda_lift_free_set_Included2. eassumption.
           eapply Union_Disjoint_l.
           eapply Disjoint_Included_r. eapply Add_functions_free_set_Included. eassumption.
           eapply Disjoint_Included; [ | | eapply Him ]. now sets.
           eapply image_monotonic. eapply Setminus_Included_Included_Union. eapply Union_Included. now sets.
           eapply Union_Included. now sets. eapply Included_trans. eassumption. now xsets.
           eapply Union_Disjoint_l; [| now sets ].
           eapply Disjoint_sym. eapply Disjoint_Included; [| | eapply Hf ].
           eapply Included_trans. eapply name_in_fundefs_bound_var_fundefs. now sets.
           eapply Add_functions_free_set_Included. eassumption.
      * lia.
    - (* Efun 3 *)
      repeat normalize_bound_var_in_ctx.

      assert (Hdis : Disjoint _ (occurs_free (Efun f2 e) :|: (FunsFVs zeta :|: LiftedFuns zeta)) (name_in_fundefs f2)).
        { normalize_occurs_free. eapply Union_Disjoint_l. eapply Union_Disjoint_l; sets.
          eapply Disjoint_sym. eapply occurs_free_fundefs_name_in_fundefs_Disjoint.
          eapply Disjoint_Included_r. eapply name_in_fundefs_bound_var_fundefs.
          eapply Union_Disjoint_l; now sets. }

      assert (Hsub : S'0 \subset S). { eapply Fundefs_Lambda_lift_free_set_Included3. eassumption. }
      inv Hun. eapply preord_exp_fun_compat. now eauto. now eapply HPost_fun. (* post *)
      eapply preord_exp_monotonic.
      eapply IHe; eauto.
      * eapply Disjoint_Included_l. eapply image_extend_fundefs.
        eapply Union_Disjoint_l.
        -- eapply Disjoint_Included; [| | eapply Him ]. now sets. normalize_occurs_free.
           rewrite !Setminus_Union_distr. sets.
        -- eapply Disjoint_Included_l. eapply name_in_fundefs_bound_var_fundefs.
           eapply Union_Disjoint_r; sets. eapply Disjoint_Included_r. eassumption. sets.
      * eapply Disjoint_Included_l. eassumption.
        eapply Disjoint_Included_r; [| eapply Hf ]. normalize_occurs_free.
        rewrite !Union_assoc. rewrite Union_Setminus_Included. now sets. now tci.
        eapply Included_trans. eapply name_in_fundefs_bound_var_fundefs. sets.
      * sets.
      * sets.
      * sets.
      * eapply Disjoint_Included_r. eapply Included_Union_Setminus with (s2 := name_in_fundefs f2).
        now tci. eapply Union_Disjoint_r. eapply Disjoint_Included; [| | eapply HD ].
        normalize_occurs_free... now sets.
        eapply Disjoint_Included_r. eapply name_in_fundefs_bound_var_fundefs. sets.
      * eapply binding_in_map_antimon. eapply image_extend_fundefs.
        rewrite Union_commut. rewrite Fundefs_lambda_lift3_name_in_fundefs at 1; [| eassumption ].
        eapply binding_in_map_def_funs.
        eapply binding_in_map_antimon; [| eassumption ].
        normalize_occurs_free. rewrite !Setminus_Union_distr. eapply image_monotonic.
        eapply Union_Included. now sets. now sets.
      * eapply preord_env_P_inj_antimon.
        eapply Fundefs_lambda_lift_correct3;
          [ eassumption | eassumption | | | | | | | | | | | eassumption ]; sets.
        -- rewrite extend_fundefs_image; sets.
           eapply Disjoint_Included; [ | | eapply Him ]. now sets. sets.
        -- eapply Disjoint_Included; [ | | eapply HD ]. normalize_occurs_free. now sets.
           now sets.
        -- eapply binding_in_map_antimon; [| eassumption ].
           rewrite extend_fundefs_image; sets.
        -- eapply preord_env_P_inj_f_eq_subdomain. eassumption.
           { intros z Hinz. rewrite extend_fundefs_neq. reflexivity.
             intros Hc. eapply Hdis. constructor; eauto. }
        -- eapply Funs_inv_f_eq_subdomain; eauto.
           { intros z Hinz. rewrite extend_fundefs_neq. reflexivity.
             intros Hc. eapply Hdis. constructor; eauto. }
        -- intros. rewrite extend_fundefs_eq. reflexivity. eassumption.
        -- normalize_occurs_free. rewrite <- Union_assoc, <- Union_Setminus; tci. sets.
      * eapply Funs_inv_def_funs_alt.
        -- eassumption.
        -- eapply Disjoint_Included_l. eapply name_in_fundefs_bound_var_fundefs. xsets.
        -- eapply Disjoint_Included_l. eapply name_in_fundefs_bound_var_fundefs.
           eapply Disjoint_sym. eapply Disjoint_Included; [| | eapply Him ]; sets.
           rewrite extend_fundefs_image; eauto. sets. xsets.
        -- eapply Funs_inv_f_eq_subdomain. 2: eassumption.
            intros z Hinz. rewrite extend_fundefs_neq. reflexivity.
            intros Hc. eapply Hdis. constructor; eauto.
      * lia.
    - (* App known *)
      eapply Funs_inv_Eapp; [ eassumption | eassumption | eassumption ].
    - (* App unknown *)
      eapply preord_exp_app_compat; eauto.
      eapply Forall2_preord_var_env_map. eassumption.
      normalize_occurs_free...
    - inv Hun. eapply preord_exp_prim_val_compat; eauto.
    - inv Hun. eapply preord_exp_prim_compat; eauto.
      + eapply Forall2_preord_var_env_map. eassumption.
        normalize_occurs_free...
    (* Back when prims were not trivial:
      + intros m vs1 vs2 Hlt Hall. eapply IHk; [ eassumption | eassumption | | | | | | | | | | eassumption ].
        * eapply Disjoint_Included_l. now eapply image_extend_Included'.
          eapply Union_Disjoint_l.
          rewrite occurs_free_Eprim in Him.
          eapply Disjoint_Included; [ | | now apply Him ].
          normalize_bound_var...
          apply image_monotonic. rewrite !Setminus_Union_distr...
          eapply Union_Disjoint_r.
          eapply Disjoint_Included_l_sym; [| eassumption ]...
          now eapply Disjoint_Singleton_l.
        * eapply Disjoint_Included_r; [| eassumption ].
          now apply bound_var_occurs_free_Eprim_Included.
        * repeat normalize_bound_var_in_ctx...
        * repeat normalize_bound_var_in_ctx...
        * repeat normalize_bound_var_in_ctx...
        * eapply Disjoint_Included_r. now apply occurs_free_Eprim_Included.
          eapply Union_Disjoint_r.
          eapply Disjoint_Included_l ; [| now apply HD].
          normalize_bound_var... now apply Disjoint_Singleton_r.
        * eapply binding_in_map_antimon; [| eapply binding_in_map_set; eassumption ].
          eapply Included_trans. eapply image_extend_Included'.
          eapply Included_Union_compat; [| reflexivity ].
          eapply image_monotonic. rewrite !Setminus_Union_distr.
          normalize_occurs_free...
        * eapply preord_env_P_inj_set_alt.
          eapply preord_env_P_inj_antimon. eapply preord_env_P_inj_monotonic; [| eassumption ]. lia.
          normalize_occurs_free...
          eassumption.
          intros Hc. eapply Him. constructor; eauto.
          eapply image_monotonic; [| eassumption ].
          normalize_occurs_free...
        * eapply Funs_inv_set.
          intros Hc. eapply Hfun. now constructor; eauto.
          intros Hc. eapply Hlf. now constructor; eauto.
          intros Hc. eapply Hfvs. now constructor; eauto.
          intros Hc. eapply Him. constructor; eauto.
          eapply image_monotonic; [| eassumption ]...
          eapply Funs_inv_monotonic. eassumption. lia. *)
    - eapply preord_exp_halt_compat; eauto.
   Qed.



   Opaque preord_exp'.


   Lemma lambda_lift_correct_top  (e : exp) (c : comp_data) k l b :
     unique_bindings e ->
     (max_var e 1%positive < next_var c)%positive ->
     Disjoint _ (bound_var e) (occurs_free e) ->
     exists e' c',
       lambda_lift k l b e c = (Ret e', c') /\
       unique_bindings e' /\
       occurs_free e' \subset occurs_free e /\
       Disjoint _ (bound_var e') (occurs_free e') /\
       (max_var e' 1%positive < next_var c')%positive /\
       (forall k rho1 rho2,
           preord_env_P cenv PG (occurs_free e) k rho1 rho2 ->
           binding_in_map (occurs_free e) rho1 ->
           preord_exp cenv (P1 0) PG k (e, rho1) (e', rho2)).
   Proof.
     intros Hun Hleq Hdis.
     set (lift_dec := if b then lift_all else lift_conservative).
     assert (Hs := lambda_lifting_sound). destruct (Hs k l lift_dec) as [Hsound _]. clear Hs.
     specialize (Hsound e (M.empty _) (M.empty _) (M.empty _) PS.empty PS.empty (fun x => (max_var e 1%positive < x))%positive).

     rewrite !Dom_map_empty in Hsound.

     assert (Heq : LiftedFuns (fun_map (M.empty FunInfo)) <--> Empty_set _).
     { clear. split; sets. intros x Hin. inv Hin. destructAll.
       inv H. inv H0. }

     assert (Heq' : FunsFVs (fun_map (M.empty FunInfo)) <--> Empty_set _).
     { clear. split; sets. intros x Hin. inv Hin. destructAll.
       unfold fun_map, lifted_name in *. rewrite M.gempty in H. congruence. }

     assert (Heq'' : Funs (fun_map (M.empty FunInfo)) <--> Empty_set _).
     { clear. split; sets. intros x Hin. inv Hin. inv H. }

     rewrite !Heq, !Heq' in *.

     assert (Hfresh : Disjoint var (fun x : var => (max_var e 1 < x)%positive) (bound_var e :|: occurs_free e)).
     { constructor. intros x Hnin. inv Hnin. inv H0.
       - eapply bound_var_leq_max_var with (y := 1%positive) in H1. unfold Ensembles.In in *. zify. lia.
       - eapply occurs_free_leq_max_var with (y := 1%positive) in H1. unfold Ensembles.In in *. zify. lia. }

     specialize (Hsound ltac:(sets) ltac:(sets) ltac:(eassumption) ltac:(eassumption) ltac:(sets) ltac:(sets) ltac:(eassumption)).

     unfold lambda_lift, triple in *.
     unfold run_compM, compM.runState in *. simpl in *.

     destruct (exp_lambda_lift k l (if b then lift_all else lift_conservative) e PS.empty PS.empty
                               (PTree.empty VarInfo) (PTree.empty FunInfo) (M.empty GFunInfo)) eqn:Heqe.
     unfold lift_dec in *. rewrite Heqe in Hsound.
     destruct (runState tt (c, tt)) as [e' [c' u]] eqn:Hstate. simpl in *.

     assert (Hf : fresh (fun x : var => (max_var e 1 < x)%positive) (next_var (fst (c, tt)))).
     { unfold fresh. intros. unfold Ensembles.In in *. simpl in *. zify; lia. }

     assert (Hren_empty : f_eq (rename (M.empty _)) id).
     { intros x. unfold rename. rewrite M.gempty. reflexivity. }

     specialize (Hsound tt _ Hf). rewrite Hstate in Hsound.
     destruct e'. contradiction. destructAll.

     do 2 eexists. split. reflexivity.

     assert (Hsub : occurs_free e0 \subset occurs_free e).
     { eapply Included_trans.
       eapply Exp_lambda_lift_occurs_free; try eassumption.
       + rewrite Heq, Heq'. rewrite Hren_empty. rewrite image_id. repeat normalize_sets.
         now sets.
       + rewrite Heq, Heq'. sets.
       + rewrite Heq, Heq'. sets.
       + rewrite !Heq, !Heq' at 1. rewrite Hren_empty. rewrite image_id. repeat normalize_sets. sets. }
     assert (Hsub' : bound_var e0 \subset bound_var e :|: ((fun x0 : var => (max_var e 1 < x0)%positive) \\ x)).
     { eapply Included_trans. eapply Exp_lambda_lift_bound_var. eassumption. sets. }


     split; [| split; [| split; [| split ] ] ]; try eassumption.
     - eapply Exp_lambda_lift_unique_bindings; try eassumption.
       sets.
       rewrite Heq. sets.
     - eapply Disjoint_Included. eassumption. eassumption. sets.
     - assert (Hin := max_var_subset e0). assert (Hin' := max_var_subset e).
       inv Hin.
       + eapply Hsub' in H1. inv H1.
         * simpl in *. find_subsets. eapply bound_var_leq_max_var in H2.
           assert (Hin : x (next_var c')). eapply H0. zify; lia.
           eapply H in Hin. unfold In in *.
           eapply Pos.le_lt_trans. eassumption. eassumption.
         * inv H2. simpl in *.
           eapply Pos.lt_nle. intros Hc. eapply H3. eapply H0. eassumption.
       + eapply Hsub in H1. simpl in *. find_subsets.
         eapply occurs_free_leq_max_var in H1.
         eapply Pos.le_lt_trans. eassumption.
         assert (Hin : x (next_var c')). eapply H0. simpl; zify; lia.
         eapply H in Hin. unfold In in *. eassumption.
     - intros. eapply Exp_lambda_lift_correct; try eassumption.
       + rewrite !Heq, !Heq', Hren_empty. rewrite image_id.
         normalize_sets. sets.
       + rewrite !Heq. sets.
       + rewrite !Heq''. sets.
       + rewrite !Heq'. sets.
       + rewrite !Heq, !Heq', Hren_empty. rewrite image_id.
         repeat normalize_sets.
         rewrite exp_fv_correct in *. intros z Hin.
         edestruct H2. eassumption.
         edestruct H1. eassumption. eassumption. destructAll. eauto.
       + rewrite Hren_empty. eassumption.
       + intro. intros. unfold fun_map in *. rewrite M.gempty in H3. congruence.
  Qed.


End Lambda_lifting_correct.
