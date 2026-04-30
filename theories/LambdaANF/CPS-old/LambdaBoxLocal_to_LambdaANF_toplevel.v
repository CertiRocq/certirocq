From Stdlib Require Import ZArith.ZArith Lists.List Strings.String micromega.Lia Arith
     Ensembles Relations.Relation_Definitions.
Require Import Common.AstCommon.
Require compcert.lib.Maps compcert.lib.Coqlib.

Import ListNotations.

Require Import LambdaBoxLocal.expression LambdaBoxLocal.fuel_sem.

Require Import term cps_show eval ctx logical_relations
        List_util algebra alpha_conv functions Ensembles_util
        tactics LambdaBoxLocal_to_LambdaANF LambdaBoxLocal_to_LambdaANF_util LambdaBoxLocal_to_LambdaANF_corresp LambdaBoxLocal_to_LambdaANF_correct
        LambdaANF.tactics identifiers bounds term_util rename.

Require Import ExtLib.Data.Monads.OptionMonad ExtLib.Structures.Monads.

Import Monad.MonadNotation.

Open Scope monad_scope.


Section Refinement.

  Context (cnstrs : conId_map)
          (dtag : positive) (* default tag *)
          (cenv : ctor_env).

  Fixpoint value_ref' (v1 : value) (v2 : val) : Prop:=
    let fix Forall2_aux vs1 vs2 :=
        match vs1, vs2 with
        | [], [] => True
        | v1 :: vs1, v2 :: vs2 =>
          value_ref' v1 v2 /\ Forall2_aux vs1 vs2
        | _, _ => False
        end
    in
    match v1, v2 with
    | Con_v c1 vs1, Vconstr c2 vs2 =>
      dcon_to_tag dtag c1 cnstrs = c2 /\ Forall2_aux vs1 vs2
    | Clos_v _ _ _, Vfun _ _ _ => True
    | ClosFix_v _ _ _, Vfun _ _ _ => True
    | _, _ => False
    end.


  Definition value_ref (v1 : value) (v2 : val) : Prop:=
    match v1, v2 with
    | Con_v c1 vs1, Vconstr c2 vs2 =>
      dcon_to_tag dtag c1 cnstrs = c2 /\ Forall2 value_ref' vs1 vs2
    | Clos_v _ _ _, Vfun _ _ _ => True
    | ClosFix_v _ _ _, Vfun _ _ _ => True
    | _, _ => False
    end.

  Lemma value_ref_eq v1 v2 :
    value_ref' v1 v2 <-> value_ref v1 v2.
  Proof.
    induction v1; try easy.

    destruct v2; simpl; try easy.


    revert l0. induction l; intros l'.

    - split; intros [H1 H2]. split; eauto; destruct l'; eauto.
      inv H2. split; eauto.

    - split; intros [H1 H2].

      + split; eauto; destruct l'; inv H2.
        constructor; eauto. eapply IHl. split; eauto.

      + split; eauto. destruct l'; inv H2.
        constructor; eauto. eapply IHl. split; eauto.
  Qed.

  Definition diverge (v : list value) (e : expression.exp) :=
    forall (c : nat), exists t, eval_env_fuel v e fuel_sem.OOT c t.


  Program Definition refines M (e1 : expression.exp) (e2 : term.exp) :=
    (* Termination *)
    (forall (v1 : value) (c1 t1 : nat),
        eval_env_fuel [] e1 (Val v1) c1 t1 ->
        exists (v2 : val) (c2 : nat),
          bstep_fuel cenv (M.empty _) e2 c2 (Res v2) tt /\
          (c2 <= t1 + M)%nat /\
          value_ref v1 v2) /\
    (* Divergence *)
    (diverge [] e1 -> eval.diverge cenv (M.empty _) e2).

  Context (prim_map : M.t (kername * string (* C definition *) * nat (* arity *))).
  Context (func_tag kon_tag default_itag : positive)
          (next_id : positive).
  Context (dcon_to_tag_inj :
             forall (tgm : conId_map) (dc dc' : dcon),
               dcon_to_tag dtag dc tgm = dcon_to_tag dtag dc' tgm -> dc = dc').

  Definition cps_rel_top (e : expression.exp) (xs : list var)
             (k : var) (e' : term.exp) :=
    let S := fun x => (max_list xs k + 1 <= x)%positive in
    exists S', cps_cvt_rel func_tag kon_tag dtag S e xs k cnstrs S' e'.


  Lemma cps_val_comp k v1 v2 v3 :
    cps_val_rel func_tag kon_tag dtag cnstrs v1 v2 ->
    preord_val cenv eq_fuel k v2 v3 ->
    value_ref v1 v3.
  Proof.
    revert v2 v3.
    induction v1 using value_ind'; intros v2 v3 Hval Hll; inv Hval.
    - rewrite preord_val_eq in Hll.
      destruct v3; try contradiction. inv Hll.
      simpl. split. reflexivity.

      revert l vs' H2 H1.
      induction H.

      + intros. inv H2. inv H1. constructor.

      + intros. inv H2. inv H1. constructor; eauto.
        eapply value_ref_eq. eauto.

    - rewrite preord_val_eq in Hll.
      destruct v3; try contradiction.
      simpl. eauto.

    - rewrite preord_val_eq in Hll.
      destruct v3; try contradiction.
      simpl. eauto.
  Qed.


  Theorem cps_corrrect_top e k x (Hneq : x <> k):
    exp_wf 0%N e ->
    exists e',
      cps_rel_top e [] k e' /\
      refines 3 e (Efun (Fcons k kon_tag [x] (Ehalt x) Fnil) e').
  Proof.
    intros Hwf.
    edestruct cps_rel_exists with (xs := @nil var).
    eassumption.
    eassumption.

    destructAll.
    eexists. split.
    eexists. eassumption.


    split.

    - intro; intros.
      edestruct cps_cvt_correct
        with (rho := M.set k
                           (Vfun (M.empty _) (Fcons k kon_tag [x] (Ehalt x) Fnil) k)
                           (M.empty _)) (x := x); try eassumption.
      + now constructor.
      + simpl. eassumption.
      + repeat normalize_sets.
        eapply Disjoint_Singleton_l. simpl.
        intros Hin. unfold In in *. lia.
      + repeat normalize_sets. intros Hc. inv Hc.
        eauto.
      + intros Hc. inv Hc.
      + constructor.
      + rewrite M.gss. reflexivity.
      + clear H2.

        edestruct cps_val_rel_exists as [v2 Hval]. eassumption.
        eapply (@eval_env_step_preserves_wf nat LambdaBoxLocal_resource_fuel LambdaBoxLocal_resource_trace).
        eassumption. reflexivity. constructor. eassumption.

        specialize (H1 v1 v2 eq_refl Hval).

        edestruct H1. reflexivity.

        econstructor 2. econstructor.
        rewrite M.gso. rewrite M.gss. reflexivity.
        now eauto.
        simpl. rewrite M.gss. reflexivity.
        simpl. rewrite Coqlib.peq_true. reflexivity.
        simpl. reflexivity.

        econstructor 2. econstructor. rewrite M.gss. reflexivity.

        destructAll. destruct x2. contradiction.

        destruct x4.

        do 2 eexists. split; [ | split ].

        replace tt with (tt <+> tt) by reflexivity.
        econstructor 2.
        econstructor. simpl. eassumption.

        simpl in *.  unfold one, one_i; simpl. lia.
        simpl in *. eapply cps_val_comp. eassumption. eassumption.

    - intros Hdiv.

      intros c. specialize (Hdiv c). destructAll.
      edestruct cps_cvt_correct
        with (rho := M.set k
                           (Vfun (M.empty _) (Fcons k kon_tag [x] (Ehalt x) Fnil) k)
                           (M.empty _)) (x := x); try eassumption.
      + now constructor.
      + simpl. eassumption.
      + repeat normalize_sets.
        eapply Disjoint_Singleton_l. simpl.
        intros Hin. unfold In in *. lia.
      + repeat normalize_sets. intros Hc. inv Hc.
        eauto.
      + intros Hc. inv Hc.
      + constructor.
      + rewrite M.gss. reflexivity.
      + clear H1.
        specialize (H2 eq_refl). destructAll.

        destruct c.

        * eexists. constructor. simpl.
          unfold one, one_i. simpl. lia.

        * eexists. replace (S c) with (c + 1)%nat by lia.
          econstructor 2. econstructor.
          simpl.
          edestruct Nat.le_exists_sub with (n := c) (m := x3). lia. destructAll.
          eapply bstep_fuel_OOT_monotonic in H2.
          destructAll. destruct x3. eassumption.

          Grab Existential Variables. exact 0%nat.
  Qed.


  Section Linking.

    Definition link_src (e_lib e_cli : expression.exp) :=
      Let_e nAnon e_lib e_cli.


    Definition link_trg (k1 x1 : var) (e_lib e_cli : term.exp) :=
      (* Efun (Fcons k2 kon_tag [x2] (Ehalt x1) Fnil) *)
      (Efun (Fcons k1 kon_tag [x1] e_cli Fnil) e_lib).


    Lemma linking_correct e_lib e_cli k1 x1 r f t :
      forall rho k x vk e_lib' e_cli' i,
        exp_wf 0%N e_lib ->
        exp_wf 1%N e_cli ->

        eval_env_fuel [] (link_src e_lib e_cli) r f t ->

        cps_rel_top e_cli [x1] k e_cli' ->
        cps_rel_top e_lib [] k1 e_lib' ->

        x1 <> k ->
        k1 <> k ->
        x <> k ->

        M.get k rho = Some vk ->

        (* Source terminates *)
        (forall v v',
            r = (Val v) ->
            cps_val_rel func_tag kon_tag dtag cnstrs v v' ->
            preord_exp cenv (cps_bound f t) eq_fuel i
                  ((Eapp k kon_tag (x::nil)), (M.set x v' (M.set k vk (M.empty term.val))))
                  (link_trg k1 x1 e_lib' e_cli', rho)) /\
        (* SOurce diverges *)
        (r = fuel_sem.OOT ->
         exists c, (f <= c)%nat /\ bstep_fuel cenv rho (link_trg k1 x1 e_lib' e_cli') c eval.OOT tt).
    Proof.
      intros rho k x vk e_lib' e_cli' i Hwf1 Hwf2 Heval Hcps1 Hcps2 Hneq1 Hneq2 Hneq3 Hget.
      inv Heval.

      - split. congruence.
        intros _. simpl in *. unfold fuel_exp in *.
        eexists 0%nat. split.

        simpl in *. lia.
        constructor 1. unfold one, one_i. simpl. lia.

      - inv H.

        + assert (Heval1 := H7). eapply cps_cvt_correct in H7; eauto.
          assert (Heval2 := H8). eapply cps_cvt_correct in H8; eauto.

          unfold link_trg.

          assert (Hwfv2 : well_formed_val v1).
          { eapply (@eval_env_step_preserves_wf nat LambdaBoxLocal_resource_fuel LambdaBoxLocal_resource_trace);
              [ | reflexivity | | ]. eassumption.
            now constructor. eassumption. }

          assert (Hex' : exists v', cps_val_rel func_tag kon_tag dtag cnstrs v1 v').
          { eapply cps_val_rel_exists. eassumption. (* TODO remove arg *) eassumption. } destructAll.

          inv Hcps1. inv Hcps2.

          assert (Heq : forall m, preord_exp' cenv (preord_val cenv)
                                              (cps_bound (f1 <+> @one_i _ _ fuel_resource_LambdaBoxLocal (link_src e_lib e_cli))
                                                         (t1 <+> @one_i _ _ trace_resource_LambdaBoxLocal (link_src e_lib e_cli)))

                                              eq_fuel m
                                              (e_cli', map_util.M.set x1 x0 (M.set k1 (Vfun rho (Fcons k1 kon_tag [x1] e_cli' Fnil) k1) rho))
                                              (Efun (Fcons k1 kon_tag [x1] e_cli' Fnil) e_lib', rho)).
        { intros j. eapply preord_exp_post_monotonic.
          2:{ eapply preord_exp_trans. tci. eapply eq_fuel_idemp.

              2:{ intros m. eapply preord_exp_Efun_red. }
              assert (Hex' : exists z, ~ In var (k1 |: FromList []) z).
              { eapply ToMSet_non_member. tci. } destructAll.

              eapply preord_exp_trans. tci. eapply eq_fuel_idemp.


              2:{ intros m. simpl. eapply H7; [ | | | | | | | eassumption | reflexivity | ].
                  - now constructor.
                  - eassumption.
                  - repeat normalize_sets. eapply Disjoint_Singleton_l.
                    unfold In. simpl. lia.
                  - eassumption.
                  - intros Hc. inv Hc.
                  - econstructor.
                  - rewrite M.gss. reflexivity.
                  - eassumption. }

              eapply preord_exp_Eapp_red.
              - rewrite M.gso; eauto. rewrite M.gss. reflexivity. intros Hc; subst; eauto.
              - simpl. rewrite Coqlib.peq_true. reflexivity.
              - simpl. rewrite M.gss. reflexivity.
              - simpl. reflexivity. }

          (* Invariant composition *)
          { unfold inclusion, comp, eq_fuel, one_step, cps_bound, one_i.
            intros [[[? ?] ?] ?] [[[? ?] ?] ?] ?.
            destructAll. destruct x4, x5. repeat destruct p, p0. subst. simpl. unfold fuel_exp. simpl. lia. } }

        assert (Hex : exists x, ~ In var (k |: FromList [x1]) x).
        { eapply ToMSet_non_member. tci. } destructAll.

        split.
        (* Termination *)
        { intros v v' Heq1 Hvrel. subst.

          eapply preord_exp_post_monotonic.

          2:{ eapply preord_exp_trans; [ | | | eassumption ]. tci. eapply eq_fuel_idemp.

              eapply preord_exp_trans. tci. eapply eq_fuel_idemp.

              2:{ intros m. eapply H8; [ | | | | | | | eassumption | reflexivity | eassumption ].
                  - constructor; eauto.
                  - simpl Datatypes.length. rewrite Nnat.Nat2N.inj_succ, <- OrdersEx.N_as_OT.add_1_l. eassumption.
                  - repeat normalize_sets. eapply Union_Disjoint_l; sets.
                    eapply Disjoint_Singleton_l. unfold In. simpl. lia.
                    eapply Disjoint_Singleton_l. unfold In. simpl. lia.
                  - eassumption.
                  - repeat normalize_sets. intros Hc; inv Hc; eauto.
                  - eapply cps_env_rel_extend_weaken; eauto.
                    eapply cps_env_rel_weaken; eauto. constructor.
                  - rewrite !M.gso. eassumption.
                    now eauto. now eauto. }

              eapply preord_exp_app_compat with (P2 := eq_fuel).
              now eapply eq_fuel_compat.
              now eapply eq_fuel_compat.

              eapply preord_var_env_extend_neq.
              eapply preord_var_env_extend_eq.
              eapply preord_val_refl. now tci.
              now eauto.

              now intros Hc; subst; eauto.
              constructor.
              eapply preord_var_env_extend_eq.
              eapply preord_val_refl. now tci. now constructor. }

          (* Invariant composition *)
          { unfold inclusion, comp, eq_fuel, one_step, cps_bound, one_i.
            intros [[[? ?] ?] ?] [[[? ?] ?] ?] ?.
            destructAll. destruct x5, x6. repeat destruct p, p0. subst.
            simpl in *. lia. } }

        (* OOT *)
        { intros ?; subst.

          edestruct H8 with (rho := M.set x1 x0 (M.set k1 (Vfun rho (Fcons k1 kon_tag [x1] e_cli' Fnil) k1) rho));
            [ | | | | | | | eassumption | ].
          - constructor; eauto.
          - eassumption.
          - repeat normalize_sets.
            eapply Union_Disjoint_l.
            eapply Disjoint_Singleton_l. unfold In. simpl. lia.
            eapply Disjoint_Singleton_l. unfold In. simpl. lia.
          - eassumption.
          - repeat normalize_sets. intros Hc; inv Hc; eauto.
          - eapply cps_env_rel_extend_weaken; eauto.
            eapply cps_env_rel_weaken; eauto. constructor.
          - rewrite !M.gso. eassumption.
            now eauto. now eauto.
          - destruct (H4 ltac:(reflexivity)). destructAll. eapply Heq in H6; [ | reflexivity ]. destructAll.
            destruct x6; try contradiction. destruct x8. eexists. split; [ | eassumption ].

            unfold one_i in *. simpl in *. lia. }

      + (* Let_e, OOT *)
        split. congruence.
        intros _.
        set (rho' := M.set k1 (Vfun rho (Fcons k1 kon_tag [x1] e_cli' Fnil) k1) rho).

        assert (Hex : exists x, ~ In var (k1 |: FromList []) x).
        { eapply ToMSet_non_member. tci. } destructAll.

        assert (Heval1 := H7). eapply cps_cvt_correct in H7; eauto.

        inv Hcps1. inv Hcps2.

        edestruct (H7 rho'); [ | | | | | | | eassumption | ].
        * constructor.
        * eassumption.
        * repeat normalize_sets.
          eapply Disjoint_Singleton_l. unfold In. simpl. lia.
        * eassumption.
        * intros Hc. inv Hc.
        * econstructor.
        * unfold rho'. rewrite M.gss. reflexivity.
        * edestruct H3. reflexivity. destructAll.
          exists (x4 + 1)%nat.
          split. unfold one_i. simpl. unfold fuel_exp. lia.
          replace tt with (tt <+> tt) by reflexivity. eapply BStepf_run. econstructor; eauto.


          Grab Existential Variables. exact 0%nat. exact 0%nat.

    Qed.


    Theorem cps_corrrect_top_sep_comp e_lib e_cli k1 k2 x1 x2 :
      exp_wf 0%N e_lib ->
      exp_wf 1%N e_cli ->

      x1 <> k2 ->
      k1 <> k2 ->
      x2 <> k2 ->

      exists e_cli' e_lib',
        cps_rel_top e_cli [x1] k2 e_cli' /\
        cps_rel_top e_lib [] k1 e_lib' /\
        refines 3 (link_src e_lib e_cli)
                (Efun (Fcons k2 kon_tag [x2] (Ehalt x2) Fnil) (link_trg k1 x1 e_lib' e_cli')).

    Proof.
      intros Hwf1 Hwf2 Hneq1 Hneq2 Hneq3.

      edestruct cps_rel_exists with (xs := @nil var).
      eassumption.
      eassumption.


      destructAll.

      edestruct cps_rel_exists with (xs := [x1]).
      eassumption.
      eassumption.

      destructAll.


      do 2 eexists. split; [ | split ].
      eexists. eassumption.
      eexists. eassumption.


      split.

      - intro; intros.
        edestruct linking_correct
          with (rho := M.set k2
                             (Vfun (M.empty _) (Fcons k2 kon_tag [x2] (Ehalt x2) Fnil) k2)
                             (M.empty _)) (x := x2).
        + eapply Hwf1.
        + eapply Hwf2.
        + eassumption.
        + eexists. eassumption.
        + eexists. eassumption.
        + now eauto.
        + now eauto.
        + now eauto.
        + rewrite M.gss. reflexivity.
        + clear H3.

          edestruct cps_val_rel_exists as [v2 Hval]. eassumption.
          eapply (@eval_env_step_preserves_wf nat LambdaBoxLocal_resource_fuel LambdaBoxLocal_resource_trace). eassumption. reflexivity. constructor.
          constructor.
          eassumption. eassumption.
          specialize (H2 v1 v2 eq_refl Hval).

          edestruct H2. reflexivity.

          econstructor 2. econstructor.
          rewrite M.gso. rewrite M.gss. reflexivity.
          now eauto.
          simpl. rewrite M.gss. reflexivity.
          simpl. rewrite Coqlib.peq_true. reflexivity.
          simpl. reflexivity.

          econstructor 2. econstructor. rewrite M.gss. reflexivity.

          destructAll. destruct x5. contradiction.

          destruct x7.

          do 2 eexists. split; [ | split ].

          replace tt with (tt <+> tt) by reflexivity.
          econstructor 2.
          econstructor. simpl. eassumption.

          simpl in *. unfold one, one_i. simpl. lia.
          simpl in *. eapply cps_val_comp. eassumption. eassumption.

      - intros Hdiv.

        intros c. specialize (Hdiv c). destructAll.
        edestruct linking_correct
          with (rho := M.set k2
                             (Vfun (M.empty _) (Fcons k2 kon_tag [x2] (Ehalt x2) Fnil) k2)
                             (M.empty _)) (x := x2).
        + eapply Hwf1.
        + eapply Hwf2.
        + eassumption.
        + eexists. eassumption.
        + eexists. eassumption.
        + now eauto.
        + now eauto.
        + now eauto.
        + rewrite M.gss. reflexivity.
        + clear H2.
          specialize (H3 eq_refl). destructAll.

          destruct c.

          * eexists. constructor. simpl.
            unfold one, one_i. simpl. lia.

          * eexists. replace (S c) with (c + 1)%nat by lia.
            econstructor 2. econstructor.
            simpl.
            edestruct Nat.le_exists_sub with (n := c) (m := x6). lia. destructAll.
            eapply bstep_fuel_OOT_monotonic in H3.
            destructAll. destruct x6. eassumption.

            Grab Existential Variables. exact 0%nat.
    Qed.


  End Linking.


End Refinement.
