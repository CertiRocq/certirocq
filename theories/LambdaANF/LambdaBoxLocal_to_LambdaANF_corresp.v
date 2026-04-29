Require Import Common.AstCommon Common.compM.
From Stdlib Require Import ZArith.ZArith Lists.List micromega.Lia Arith
     Ensembles Relations.Relation_Definitions.
Require compcert.lib.Maps compcert.lib.Coqlib.
Import ListNotations.

Require Import LambdaBoxLocal.expression LambdaBoxLocal.fuel_sem.

Require Import term cps_show eval ctx logical_relations
        List_util algebra alpha_conv functions Ensembles_util
        LambdaBoxLocal_to_LambdaANF LambdaBoxLocal_to_LambdaANF_util LambdaANF.tactics identifiers
        term_util rename state.
Require Import closure_conversion_corresp.

Require Import ExtLib.Data.Monads.OptionMonad ExtLib.Structures.Monads.

Require Import MetaRocq.Utils.bytestring.

Import Monad.MonadNotation.

Open Scope monad_scope.

Section Corresp.

  Context (prim_map : M.t Pipeline_utils.primitive)
          (func_tag kon_tag default_tag : positive).


  Definition cps_cvt_exp_corresp :=
    forall e S vn k ctrs (Hwf : exp_wf (N.of_nat (List.length vn)) e),
           (* (Hdis : Disjoint _ S [set k]), *)
      {{ fun _ s => fresh S (next_var (fst s)) }}
        cps_cvt prim_map func_tag kon_tag default_tag e vn k ctrs
      {{ fun _ s e' s' =>
           exists S',
             cps_cvt_rel func_tag kon_tag default_tag S e vn k ctrs S' e' /\
             fresh S' (next_var (fst s'))
             (* Needed to compose with λANF proofs -- ignore for now *)
             (* (next_var (fst s') >= next_var (fst s))%positive /\ *)
             (* bound_var e' \subset Range (next_var (fst s)) (next_var (fst s')) /\ *)
             (* unique_bindings e' /\ *)
             (* Disjoint _ (occurs_free e') (bound_var e') *)
      }} .

  Definition cps_cvt_exps_corresp :=
    forall es S vn xs ks k ctrs (Hwf : exps_wf (N.of_nat (List.length vn)) es)
           (Hlen : List.length xs = N.to_nat (exps_length es))
           (Hlen' : List.length ks = N.to_nat (exps_length es)),
           (* (Hdis : Disjoint _ S [set k]), *)
      {{ fun _ s => fresh S (next_var (fst s)) }}
        cps_cvt_exps prim_map func_tag kon_tag default_tag es vn k xs ks ctrs
      {{ fun _ s e' s' =>
           exists S',
             cps_cvt_rel_exps func_tag kon_tag default_tag S es vn k xs ks ctrs S' e' /\
             fresh S' (next_var (fst s'))
             (* (next_var (fst s') >= next_var (fst s))%positive /\ *)
             (* bound_var e' \subset Range (next_var (fst s)) (next_var (fst s')) /\ *)
             (* unique_bindings e' /\ *)
             (* Disjoint _ (occurs_free e') (bound_var e') *)
      }}.

  Definition cps_cvt_efnlst_corresp :=
    forall efns S vn xs ctrs (Hwf : efnlst_wf (N.of_nat (List.length vn)) efns)
           (Hlen : List.length xs = efnlength efns),
      {{ fun _ s => fresh S (next_var (fst s)) }}
        cps_cvt_efnlst prim_map func_tag kon_tag default_tag efns vn xs ctrs
      {{ fun _ s B' s' =>
           exists S',
             cps_cvt_rel_efnlst func_tag kon_tag default_tag S efns vn xs ctrs S' B' /\
             fresh S' (next_var (fst s'))
             (* (next_var (fst s') >= next_var (fst s))%positive /\ *)
             (* bound_var_fundefs B' \subset Range (next_var (fst s)) (next_var (fst s')) /\ *)
             (* unique_bindings_fundefs B' /\ *)
             (* Disjoint _ (occurs_free_fundefs B') (bound_var_fundefs B') *)
      }} .

  Definition cps_cvt_branches_corresp :=
    forall bs S vn k r ctrs (Hwf : branches_wf (N.of_nat (List.length vn)) bs),
           (* (Hdis : Disjoint _ S [set k]), *)
      {{ fun _ s => fresh S (next_var (fst s)) }}
        cps_cvt_branches prim_map func_tag kon_tag default_tag bs vn k r ctrs
      {{ fun _ s P s' =>
           exists S',
             cps_cvt_rel_branches func_tag kon_tag default_tag S bs vn k r ctrs S' P /\
             fresh S' (next_var (fst s'))
             (* (next_var (fst s') >= next_var (fst s))%positive /\ *)
             (* bound_var (Ecase r P) \subset Range (next_var (fst s)) (next_var (fst s')) /\ *)
             (* unique_bindings (Ecase r P) /\            *)
             (* Disjoint _ (occurs_free (Ecase r P)) (bound_var (Ecase r P)) *)
      }} .

  (* TODO move to state *)
  Lemma get_named_spec :
    forall (A : Type) (S : Ensemble var) (n : name),
      {{fun (_ : unit) (s : comp_data * A) => fresh S (next_var (fst s))}} get_named n
      {{fun (_ : unit) (s : comp_data * A) (x : var) (s' : comp_data * A) =>
          In var S x /\
          In var (Range (next_var (fst s)) (next_var (fst s'))) x /\
          (next_var (fst s) < next_var (fst s'))%positive /\ fresh (S \\ [set x]) (next_var (fst s'))}}.
  Proof.
    intros.
    eapply pre_post_mp_l.
    eapply bind_triple. now eapply get_triple.
    intros [[] w1] [[] w2].
    eapply pre_post_mp_l.
    eapply bind_triple. now eapply put_triple.
    intros x [r3 w3].
    eapply return_triple.
    intros ? [r4 w4] H2. inv H2. intros [H1 H2]. inv H1; inv H2. intros.
    split. eapply H. reflexivity. split. unfold Range, Ensembles.In. simpl. zify. lia.
    simpl. split. zify; lia.
    intros z Hin. constructor. eapply H; eauto. simpl. zify. lia.
    intros Hc. inv Hc. zify; lia.
  Qed.

  Lemma get_named_str_lst_spec S strs :
    {{ fun _ (s : comp_data * unit) => identifiers.fresh S (next_var (fst s)) }}
      get_named_str_lst strs
      {{ fun (r: unit) s xs s' =>
           NoDup xs /\ List.length xs = List.length strs /\
           FromList xs \subset S /\
           FromList xs \subset Range (next_var (fst s)) (next_var (fst s')) /\
           (next_var (fst s) <= next_var (fst s'))%positive /\
           identifiers.fresh (S \\ FromList xs) (next_var (fst s')) }}.
  Proof.
    unfold get_named_str_lst. revert S; induction strs; intros S.
    - simpl. eapply return_triple.
      intros. repeat normalize_sets. split; eauto.
      sets. now constructor. split; eauto.
      split. now sets. split. sets. split. reflexivity. eassumption.
    - simpl. eapply bind_triple. eapply get_named_str_fresh.
      intros x w.
      eapply bind_triple. eapply frame_rule. eapply frame_rule. eapply frame_rule. eapply IHstrs.
      intros xs w'. eapply return_triple. intros. destructAll.
      repeat normalize_sets. split; [ | split; [ | split; [ | split; [ | split ]]]].
      + constructor; eauto. intros Hc. eapply H4 in Hc. inv Hc. now eauto.
      + simpl. congruence.
      + eapply Union_Included. sets. eapply Included_trans. eapply H4. sets.
      + eapply Union_Included. eapply Singleton_Included.
        eapply Range_Subset; [ | | eassumption ]. reflexivity. zify. lia.
        eapply Included_trans. eassumption. eapply Range_Subset. zify; lia. reflexivity.
      + zify; lia.
      + rewrite <- Setminus_Union. eassumption.
  Qed.


  Lemma get_named_lst_spec S strs :
    {{ fun _ (s : comp_data * unit) => identifiers.fresh S (next_var (fst s)) }}
      get_named_lst strs
      {{ fun (r: unit) s xs s' =>
           NoDup xs /\ List.length xs = List.length strs /\
           FromList xs \subset S /\
           FromList xs \subset Range (next_var (fst s)) (next_var (fst s')) /\
           (next_var (fst s) <= next_var (fst s'))%positive /\
           identifiers.fresh (S \\ FromList xs) (next_var (fst s')) }}.
  Proof.
    unfold get_named_str_lst. revert S; induction strs; intros S.
    - simpl. eapply return_triple.
      intros. repeat normalize_sets. split; eauto.
      sets. now constructor. split; eauto.
      split. now sets. split. sets. split. reflexivity. eassumption.
    - simpl. eapply bind_triple. eapply get_named_spec.
      intros x w.
      eapply bind_triple. eapply frame_rule. eapply frame_rule. eapply frame_rule. eapply IHstrs.
      intros xs w'. eapply return_triple. intros. destructAll.
      repeat normalize_sets. split; [ | split; [ | split; [ | split; [ | split ]]]].
      + constructor; eauto. intros Hc. eapply H4 in Hc. inv Hc. now eauto.
      + simpl. congruence.
      + eapply Union_Included. sets. eapply Included_trans. eapply H4. sets.
      + eapply Union_Included. eapply Singleton_Included.
        eapply Range_Subset; [ | | eassumption ]. reflexivity. zify. lia.
        eapply Included_trans. eassumption. eapply Range_Subset. zify; lia. reflexivity.
      + zify; lia.
      + rewrite <- Setminus_Union. eassumption.
  Qed.


  Ltac inv_setminus :=
    match goal with
    | [ H : In _ (?S \\ ?Q) _ |- _ ] => inv H; try inv_setminus
    end.


  Lemma cps_cvt_sound :
    cps_cvt_exp_corresp /\
    cps_cvt_exps_corresp /\
    cps_cvt_efnlst_corresp /\
    cps_cvt_branches_corresp.
  Proof.
    eapply exp_ind_alt_2; intros; try inv Hwf.
    - (* Var_e *)
      unfold cps_cvt.
      destruct (nth_error vn (N.to_nat n)) eqn:Hnth.
      + eapply return_triple. intros _ w Hf.
        eexists. split.
        * econstructor. eassumption.
        * eassumption.
        (* * lia. *)
        (* * normalize_bound_var. sets. *)
        (* * constructor. *)
        (* * normalize_bound_var. sets. *)
      + eapply nth_error_Some in Hnth. now exfalso; eauto. lia.
    - (* Lam_e *)
      eapply bind_triple. eapply pre_post_copy. unfold cps_cvt; simpl.
      eapply get_named_str_fresh.
      intros x w. simpl.
      eapply pre_curry_l; intros Hfresh.
      eapply pre_curry_l; intros Hx.

      eapply bind_triple.

      eapply frame_rule. eapply frame_rule.
      eapply get_named_spec.

      intros f w2. simpl.
      eapply pre_curry_l; intros Hr'.
      eapply pre_curry_l; intros Hlt'.
      eapply pre_curry_l; intros Hf.

      eapply bind_triple.

      eapply frame_rule. eapply frame_rule.
      eapply get_named_str_fresh.

      intros k1 w1. simpl.
      eapply pre_curry_l; intros Hr.
      eapply pre_curry_l; intros Hlt.
      eapply pre_curry_l; intros Hk1.


      eapply bind_triple.

      eapply frame_rule. eapply frame_rule.
      eapply H.

      simpl List.length.
      replace (N.of_nat (Datatypes.S (Datatypes.length vn))) with (1 + N.of_nat (Datatypes.length vn)) by lia.
      eassumption.

      intros e' w3. simpl. eapply return_triple.
      intros. destructAll.

      eexists. split.
      + inv_setminus. econstructor; eauto.
        now constructor; eauto.
        constructor; eauto. intros Hc; inv Hc; eauto; inv H14; now eauto.
      + eassumption.

    - (* App_e *)
      unfold cps_cvt.

      eapply bind_triple. eapply pre_post_copy. unfold cps_cvt; simpl.
      eapply get_named_str_fresh.
      intros x w. simpl.
      eapply pre_curry_l; intros Hfresh.
      eapply pre_curry_l; intros Hx.

      eapply bind_triple.

      eapply frame_rule. eapply frame_rule.
      eapply get_named_spec.

      intros k1 w2. simpl.
      eapply pre_curry_l; intros Hr1.
      eapply pre_curry_l; intros Hlt1.
      eapply pre_curry_l; intros Hk1.

      eapply bind_triple.

      eapply frame_rule. eapply frame_rule.
      eapply get_named_spec.

      intros k2 w4. simpl.
      eapply pre_curry_l; intros Hr3.
      eapply pre_curry_l; intros Hlt3.
      eapply pre_curry_l; intros Hk2.

      eapply bind_triple.

      eapply frame_rule. eapply frame_rule.
      eapply get_named_spec.

      intros x2 w5. simpl.
      eapply pre_curry_l; intros Hr4.
      eapply pre_curry_l; intros Hlt4.
      eapply pre_curry_l; intros Hk4.

      eapply bind_triple.


      eapply frame_rule. eapply frame_rule. eapply H. eassumption.

      intros e1 w3. simpl.
      eapply pre_curry_l; intros Hr2.
      eapply pre_curry_l; intros Hlt2.
      eapply pre_existential. intros S1.
      eapply pre_curry_l; intros Hrel1.

      eapply bind_triple.

      eapply H0 with (S := S1). eassumption.

      intros e2 w6. simpl. eapply return_triple.
      intros. destructAll.

      eexists. split.
      + econstructor; eauto.
      + eassumption.
    - (* Con_e *)
      eapply bind_triple. eapply pre_post_copy. unfold cps_cvt; simpl.
      eapply get_named_str_fresh.
      intros x w. simpl.
      eapply pre_curry_l; intros Hfresh.
      eapply pre_curry_l; intros Hx.

      eapply bind_triple.

      eapply frame_rule. eapply frame_rule.
      eapply get_named_str_lst_spec.

      intros xs w2. simpl.
      eapply pre_curry_l; intros Hink.
      eapply pre_curry_l; intros Hlt'.
      eapply pre_curry_l; intros Hnd.
      eapply pre_curry_l; intros Hlen.
      eapply pre_curry_l; intros Hsub.


      eapply bind_triple.
      eapply frame_rule. eapply frame_rule.

      eapply get_named_str_lst_spec.

      intros xs' w3. simpl.
      eapply pre_curry_l; intros Hsub'.
      eapply pre_curry_l; intros Hlt''.
      eapply pre_curry_l; intros Hnd'.
      eapply pre_curry_l; intros Hlen'.
      eapply pre_curry_l; intros Hsub''.

      assert (Hlenes : Datatypes.length (exps_as_list e) = N.to_nat (exps_length e)).
      { clear. induction e; simpl. congruence.
        rewrite IHe.
        destruct (exps_length e0). lia.
        destruct p; lia. }

      eapply pre_strenghtening.
      2:{ eapply post_weakening.
          2:{ eapply H. eassumption.
              rewrite Hlen. rewrite length_map. eassumption.
              rewrite Hlen'. rewrite length_map. eassumption. }
          simpl. intros. destructAll.
          eexists. split. econstructor; try eassumption. reflexivity.
          eassumption. }

      simpl. intros. destructAll. eassumption.

    - (* Match_e *)
      eapply bind_triple. eapply pre_post_copy. unfold cps_cvt; simpl.
      eapply get_named_str_fresh.
      intros x w. simpl.
      eapply pre_curry_l; intros Hfresh.
      eapply pre_curry_l; intros Hx.

      eapply bind_triple.

      eapply frame_rule. eapply frame_rule.
      eapply get_named_spec.

      intros k1 w1. simpl.
      eapply pre_curry_l; intros Hinx.
      eapply pre_curry_l; intros Hr.
      eapply pre_curry_l; intros Hk.

      eapply bind_triple.

      eapply frame_rule. eapply frame_rule.
      eapply H. eassumption.

      intros e' w2. simpl.

      eapply pre_curry_l; intros Hink.
      eapply pre_curry_l; intros Hlt'.

      eapply pre_existential. intros S1.
      eapply pre_curry_l; intros Hrel.

      eapply bind_triple.

      eapply H0. eassumption.

      intros Ps w3. simpl.

      eapply return_triple. intros. destructAll.

      eexists. split; eauto. econstructor; eauto.

    - (* Let_e *)
      unfold cps_cvt.

      eapply bind_triple. eapply pre_post_copy. unfold cps_cvt; simpl.
      eapply get_named_str_fresh.
      intros x w. simpl.
      eapply pre_curry_l; intros Hfresh.
      eapply pre_curry_l; intros Hx.

      eapply bind_triple.

      eapply frame_rule. eapply frame_rule.
      eapply get_named_spec.

      intros k1 w2. simpl.
      eapply pre_curry_l; intros Hr1.
      eapply pre_curry_l; intros Hlt1.
      eapply pre_curry_l; intros Hk1.

      eapply bind_triple.

      eapply frame_rule. eapply frame_rule.
      eapply H0.

      replace (N.of_nat (Datatypes.length (x :: vn))) with (1 + N.of_nat (Datatypes.length vn)).
      2:{ simpl Datatypes.length. lia. }
      eassumption.

      intros e1 w3. simpl.
      eapply pre_curry_l; intros Hr2.
      eapply pre_curry_l; intros Hlt2.
      eapply pre_existential. intros S1.
      eapply pre_curry_l; intros Hrel1.

      eapply bind_triple.

      eapply H with (S := S1). eassumption.
      intros e2 w6. simpl. eapply return_triple.
      intros. destructAll.

      eexists. split.
      + econstructor; eauto.
      + eassumption.

    - (* Fix_e *)
      eapply bind_triple. eapply pre_post_copy. unfold cps_cvt; simpl.
      eapply get_named_lst_spec.
      intros x w. simpl.
      eapply pre_curry_l; intros Hfresh.
      eapply pre_curry_l; intros Hnd.
      eapply pre_curry_l; intros Hlen.
      eapply pre_curry_l; intros Hsub.

      assert (Hlen' : N.of_nat (Datatypes.length (efnlst_as_list e)) = efnlst_length e).
      { clear. induction e. simpl. lia.
        simpl Datatypes.length; simpl efnlst_length.
        simpl. destruct (efnlst_length e0); simpl; try lia. destruct p; lia. }

      eapply bind_triple.

      eapply frame_rule. eapply frame_rule.

      eapply H. rewrite length_app, length_rev. unfold fnames in Hlen.
      rewrite length_map in Hlen. rewrite Hlen.

      rewrite Nnat.Nat2N.inj_add. rewrite Hlen'. eassumption.
      rewrite Hlen. unfold fnames. rewrite length_map.
      rewrite <- Nnat.Nat2N.id with (n := Datatypes.length (efnlst_as_list e)).
      rewrite <- Nnat.Nat2N.id with (n := efnlength e).
      rewrite Hlen', efnlength_efnlst_length. reflexivity.

      intros B w1. simpl.

      destruct (nth_error x (N.to_nat n)) eqn:Hnth.
      + eapply return_triple. intros _ w3 Hf. destructAll.
        eexists. split.
        * econstructor; eauto. rewrite Hlen. unfold fnames. rewrite length_map.
          rewrite <- Nnat.Nat2N.id with (n := Datatypes.length (efnlst_as_list e)).
          rewrite <- Nnat.Nat2N.id with (n := efnlength e).
          rewrite Hlen'. rewrite efnlength_efnlst_length. reflexivity.

        * eassumption.

      + eapply nth_error_Some in Hnth. now exfalso; eauto.
        rewrite Hlen. unfold fnames. rewrite length_map.
        rewrite <- Nnat.Nat2N.id with (n := Datatypes.length (efnlst_as_list e)).
        rewrite Hlen'. lia.

    - (* Prf_e *)
      unfold cps_cvt.

      eapply bind_triple. eapply pre_post_copy. unfold cps_cvt; simpl.
      eapply get_named_str_fresh.
      intros x w. simpl.
      eapply pre_curry_l; intros Hfresh.
      eapply pre_curry_l; intros Hx.

      eapply return_triple.
      intros. destructAll.

      eexists. split.
      + econstructor; eauto.
      + eassumption.

    - unfold cps_cvt.
      eapply bind_triple. eapply pre_post_copy. eapply get_named_str_fresh.
      intros x w. simpl.
      eapply pre_curry_l. intros Hfresh.
      eapply pre_curry_l. intros Hx.
      eapply return_triple.
      intros; destructAll.
      eexists; split.
      + econstructor; eauto.
      + eassumption.

    - (* enil *)

      eapply return_triple. intros. eexists. split; [ | eassumption ].
      destruct xs; simpl in *; try congruence.
      destruct ks; simpl in *; try congruence. constructor.

    - (* econs *)
      destruct xs.
      { inv Hlen. destruct (exps_length e0). lia. destruct p; lia. }
      destruct ks.
      { inv Hlen'. destruct (exps_length e0). lia. destruct p; lia. }

      eapply bind_triple. eapply pre_post_copy. unfold cps_cvt; simpl.
      eapply H. eassumption.

      intros e1 w3. simpl.
      eapply pre_curry_l; intros Hf.
      eapply pre_existential. intros S1.
      eapply pre_curry_l; intros Hrel1.

      eapply bind_triple.
      eapply H0. eassumption.

      simpl in Hlen. destruct (exps_length e0). lia. destruct p; lia.
      simpl in Hlen'. destruct (exps_length e0). lia. destruct p; lia.

      intros e2 w4. eapply return_triple. intros. destructAll.

      eexists. split.
      + econstructor; eauto.
      + eassumption.

    - (* efnil *)
      eapply return_triple. intros. destruct xs; [ | simpl in *; congruence ].
      eexists. split. now constructor. eassumption.

    - (* efcons *) split; intros.
      2:{ inv Hwf. exfalso; eauto. }
      inv Hwf.

      eapply bind_triple. eapply pre_post_copy. unfold cps_cvt; simpl.
      eapply get_named_str_fresh.
      intros x w. simpl.
      eapply pre_curry_l; intros Hfresh.
      eapply pre_curry_l; intros Hx.

      eapply bind_triple.

      eapply frame_rule. eapply frame_rule.
      eapply get_named_spec.

      intros k1 w2. simpl.
      eapply pre_curry_l; intros Hr1.
      eapply pre_curry_l; intros Hlt1.
      eapply pre_curry_l; intros Hk1.

      eapply bind_triple.

      eapply frame_rule. eapply frame_rule.
      eapply H0.
      inv H6.

      replace (N.of_nat (Datatypes.length (x :: vn))) with (1 + N.of_nat (Datatypes.length vn)).
      2:{ simpl Datatypes.length. lia. }
      eassumption.

      intros e1 w3. simpl.
      eapply pre_curry_l; intros Hr2.
      eapply pre_curry_l; intros Hlt2.
      eapply pre_existential. intros S1.
      eapply pre_curry_l; intros Hrel1.

      destruct xs. simpl in Hlen. congruence.
      eapply bind_triple.
      eapply H1. eassumption.

      simpl in *. congruence.

      intros B w4. eapply return_triple. intros. destructAll.

      eexists. split.
      + econstructor; eauto.
      + eassumption.

    - (* brnil_e *)

      eapply return_triple. intros. eexists. split.
      now constructor. eassumption.

    - (* brcons_e *)
      destruct p. eapply bind_triple. eapply pre_post_copy.

      eapply H0. eassumption.

      intros e1 w1. simpl.
      eapply pre_curry_l; intros Hr2.
      eapply pre_existential. intros S1.
      eapply pre_curry_l; intros Hrel1.

      eapply bind_triple.

      eapply get_named_lst_spec.
      intros xs w2. simpl.
      eapply pre_curry_l; intros Hfresh.
      eapply pre_curry_l; intros Hnd.
      eapply pre_curry_l; intros Hlen.

      eapply bind_triple.

      eapply frame_rule. eapply frame_rule.

      eapply H. simpl in *.
      rewrite length_app. rewrite Hnd, names_lst_length.
      rewrite Nnat.Nat2N.inj_add. rewrite Nnat.N2Nat.id. eassumption.

      intros e2 w3. eapply return_triple. intros. destructAll.

      eexists. split.
      + econstructor; [ | | | | | eassumption | eassumption ]; eauto.
        rewrite Hnd. rewrite names_lst_length. reflexivity.
        rewrite Hnd. rewrite names_lst_length. reflexivity.
      + eassumption.
  Qed.

  Lemma set_lists_Forall2 {A} xs (vs : list A) rho rho' :
    set_lists xs vs rho = Some rho' ->
    NoDup xs ->
    Forall2 (fun x v => M.get x rho' = Some v) xs vs.
  Proof.
    revert vs rho rho'; induction xs; intros ys rho rho' Hset Hnd;
      destruct ys; simpl in *; try congruence.
    - constructor.
    - destruct (set_lists xs ys rho) eqn:Hset'; try congruence.
      inv Hset.
      constructor.
      rewrite M.gss. reflexivity.
      eapply Forall2_monotonic_strong.
      2:{ eapply IHxs; eauto. inv Hnd. eassumption. }

      intros. rewrite M.gso. eassumption.
      intros Heq; subst.
      inv Hnd; eauto.
  Qed.


  Fixpoint pos_seq (start : var) (n : nat) : list positive :=
    match n with
    | 0%nat => []
    | S n =>
      start :: (pos_seq (start + 1)%positive n)
    end.

  Lemma pos_seq_len start n :
    List.length (pos_seq start n) = n.
  Proof.
    revert start. induction n; intros start.
    - reflexivity.
    - simpl. rewrite IHn. reflexivity.
  Qed.

  Lemma pos_seq_In start n x :
    List.In x (pos_seq start n) ->
    (start <= x <= Pos.of_nat (Pos.to_nat start + n)%nat)%positive.
  Proof.
    revert start. induction n; intros start Hin.
    - inv Hin.
    - inv Hin.
      + lia.
      + eapply IHn in H.
        split. lia. lia.
  Qed.

  Lemma pos_seq_NoDup start n :
    NoDup (pos_seq start n).
  Proof.
    revert start; induction n; intros start.
    - now constructor.
    - simpl. constructor; eauto.
      intros Hc. eapply pos_seq_In in Hc. lia.
  Qed.

  Lemma cps_rel_exists e xs k m ctrs :
    exp_wf (N.of_nat (List.length xs)) e ->
    exists e' S',
      cps_cvt_rel func_tag kon_tag default_tag (fun x => (m <= x)%positive) e xs k ctrs S' e'.
  Proof.
    intros Hwf.
    destruct cps_cvt_sound as (Hexp & _).

    set (comp_d := pack_data m
                             1%positive 1%positive 1%positive
                             (M.empty _) (M.empty _) (M.empty _) (M.empty _) []).

    set (S := fun x => (m <= x)%positive).

    edestruct (runState (cps_cvt prim_map func_tag kon_tag default_tag e
                                 xs k ctrs) tt (comp_d, tt)) eqn:Hcvt.

    assert (Hf : fresh S m).
    { unfold S, fresh, In. lia. }

    specialize (Hexp e S xs k ctrs Hwf tt (comp_d, tt) Hf).

    rewrite Hcvt in Hexp. destruct e0. contradiction.

    destructAll.
    do 2 eexists. eassumption.
  Qed.


  Lemma cps_fix_rel_exists m efns ctrs fnames names fnames' :
    efnlst_wf (N.of_nat (List.length (fnames ++ names))) efns ->
    Disjoint _ (fun x => (m <= x)%positive) (FromList fnames :|: FromList names) ->
    List.length fnames' = N.to_nat (efnlst_length efns) ->
    exists B S3,
      cps_fix_rel ctrs func_tag kon_tag default_tag fnames names (fun x => (m <= x)%positive) fnames' efns B S3.
  Proof.
    revert m ctrs fnames names fnames'.
    induction efns; intros m ctrs fnames names fnames'; intros Hwf Hdis Hlen.

    - do 2 eexists.
      destruct fnames'; simpl in *; try congruence.
      econstructor.

    - destruct fnames'. simpl in Hlen. destruct (efnlst_length efns); lia.

      assert (Heq : N.to_nat (efnlst_length (eflcons n e efns)) = (1 + N.to_nat (efnlst_length efns))%nat).
      { simpl. destruct (efnlst_length efns). lia. destruct p; lia. }

      rewrite Heq in *. clear Heq. simpl in *. inv Hlen.
      inv Hwf.

      set (k := (1 + m)%positive).
      set (y := (1 + k)%positive).
      set (next_id := (1 + y)%positive).


      set (comp_d := pack_data next_id
                               1%positive 1%positive 1%positive
                               (M.empty _) (M.empty _) (M.empty _) (M.empty _) []).

      set (S := fun x => (next_id <= x)%positive).

      assert (Hf : fresh S next_id).
      { unfold S, next_id, fresh, In. lia. }

      destruct e; inv H5.

      destruct cps_cvt_sound as (Hexp & _).

      edestruct (runState (cps_cvt prim_map func_tag kon_tag default_tag e (y :: (rev fnames ++ names)) k ctrs) tt (comp_d, tt)) eqn:Hcvt.

      inv H4.
      assert (Hwf : exp_wf (N.of_nat (Datatypes.length (y :: (rev fnames ++ names)))) e).
      { simpl. rewrite length_app in *. rewrite length_rev.
        replace (N.pos (Pos.of_succ_nat (Datatypes.length fnames + Datatypes.length names)))
          with (1 + N.of_nat (Datatypes.length fnames + Datatypes.length names)) by lia.
        eassumption. }

      unfold cps_cvt_efnlst_corresp, triple in Hexp.
      specialize (Hexp e S (y :: (rev fnames ++ names)) k ctrs Hwf tt (comp_d, tt) Hf).
      rewrite Hcvt in Hexp.
      destruct e0; try contradiction. destructAll.

      edestruct IHefns with (m := (next_var (fst p))). eassumption.
      eapply Disjoint_Included_l; [ | eassumption ].
      intros z. unfold In.
      intros Hc. eapply H1 in Hc. unfold In in *.
      eapply cps_cvt_exp_subset in Hc; [ | eassumption ].
      unfold S, In, next_id in *. lia.
      eassumption. destructAll.


      do 2 eexists. econstructor; [ | | | | | eassumption | eassumption  ].
      + eassumption.
      + unfold In, y. lia.
      + constructor.
        unfold In, x2. lia.
        intros Hc. inv Hc. lia.
      + unfold S. intros z. unfold In. intros Hleq.
        constructor. constructor.
        unfold In. lia.
        intros Hc. inv Hc. lia.
        intros Hc. inv Hc. lia.
      + intros z Hc. eapply H1 in Hc. eassumption.
  Qed.



  Lemma cps_val_rel_exists v ctrs :
    well_formed_val v ->
    exists v', cps_val_rel ctrs func_tag kon_tag default_tag v v'.
  Proof.
    induction v using value_ind'; intros Hwf; inv Hwf.

    - (* Con_v *)
      induction vs.
      + eexists. constructor. constructor. reflexivity.
      + inv H. inv H1.
        edestruct IHvs; eauto. edestruct H3; eauto.
        inv H.
        eexists. constructor. econstructor. eassumption. eassumption. reflexivity.

    - (* Clos_v *)

      set (k := 1%positive).
      set (f := 2%positive).
      set (x := 3%positive).
      set (names := pos_seq 4%positive (List.length vs)).

      assert (Hvs : exists vs', Forall2 (cps_val_rel ctrs func_tag kon_tag default_tag) vs vs').
      { revert H H2. clear. intros. induction vs.
        + eexists. constructor.
        + inv H2. inv H.
          edestruct IHvs; eauto. edestruct H2; eauto. }

      destruct Hvs as [vs' Hvs].

      edestruct (@set_lists_length3 val) with (rho := M.empty val) (vs := vs') (xs := names) as [ rho ].
      eapply Forall2_length in Hvs. rewrite <- Hvs. eapply pos_seq_len.

      assert (Henv: cps_env_rel' (cps_val_rel ctrs func_tag kon_tag default_tag) names vs rho).
      { eapply set_lists_Forall2 in H0; eauto. 2:{ eapply pos_seq_NoDup. }
        unfold names in *. revert Hvs H0. clear. generalize (pos_seq 4%positive (Datatypes.length vs)) as ns.
        revert vs' rho.
        induction vs; intros vs' rho ns Hvs Hset; destruct vs'; inv Hvs; destruct ns; inv Hset.
        now constructor.
        constructor.
        now eauto.
        eapply IHvs; eauto. }

      destruct cps_cvt_sound as (Hexp & _).

      specialize (H4 (Clos_v [] nAnon e)).

      assert (Hwf : exp_wf (N.of_nat (Datatypes.length (x :: names))) e).
      { unfold well_formed_in_env in *. simpl in *.
        unfold names. rewrite pos_seq_len. eassumption. }

      set (next_id := (Pos.of_nat (Pos.to_nat 4%positive + (List.length vs))%nat + 1)%positive).

      set (comp_d := pack_data next_id
                               1%positive 1%positive 1%positive
                               (M.empty _) (M.empty _) (M.empty _) (M.empty _) []).

      set (S := fun x => (next_id <= x)%positive).

      assert (Hf : fresh S next_id).
      { unfold S, next_id, fresh, In. lia. }

      edestruct (runState (cps_cvt prim_map func_tag kon_tag default_tag e (x :: names) k ctrs) tt (comp_d, tt)) eqn:Hcvt.

      unfold cps_cvt_exp_corresp, triple in Hexp.
      specialize (Hexp e S (x :: names) k ctrs Hwf tt (comp_d, tt) Hf).
      rewrite Hcvt in Hexp.
      destruct e0; try contradiction. destructAll.

      eexists. eapply rel_Clos with (f := f); [ eassumption | | | | | | eassumption ].
      + eapply pos_seq_NoDup.
      + unfold S, next_id. constructor. intros z Hc.
        inv Hc. unfold In in *.
        inv H5. inv H7. lia.
        inv H7. inv H5. lia.
        eapply pos_seq_In in H5. lia.
      + intros Hx.
        inv Hx. inv H5. inv H6. inv H6.
        eapply pos_seq_In in H5. lia.
      + intros Hx.
        inv Hx. inv H5.
        eapply pos_seq_In in H5. lia.
      + intros Hx.
        eapply pos_seq_In in Hx. lia.

    - (* ClosFix_v *)

      set (names := pos_seq 1%positive (List.length vs)).
      set (fnames := pos_seq (Pos.of_nat (List.length vs + 2)) (N.to_nat (efnlst_length fnl))).
      set (next_id := (Pos.of_nat (N.to_nat (efnlst_length fnl) + (List.length vs) + 3)%nat)%positive).

      assert (Hvs : exists vs', Forall2 (cps_val_rel ctrs func_tag kon_tag default_tag) vs vs').
      { revert H H3. clear. intros. induction vs.
        + eexists. constructor.
        + inv H3. inv H.
          edestruct IHvs; eauto. edestruct H3; eauto. }

      destruct Hvs as [vs' Hvs].

      edestruct (@set_lists_length3 val) with (rho := M.empty val) (vs := vs') (xs := names) as [ rho ].
      eapply Forall2_length in Hvs. rewrite <- Hvs. eapply pos_seq_len.

      assert (Henv: cps_env_rel' (cps_val_rel ctrs func_tag kon_tag default_tag) names vs rho).
      { eapply set_lists_Forall2 in H0; eauto. 2:{ eapply pos_seq_NoDup. }
        unfold names in *. revert Hvs H0. clear. generalize (pos_seq 1%positive (Datatypes.length vs)) as ns.
        revert vs' rho.
        induction vs; intros vs' rho ns Hvs Hset; destruct vs'; inv Hvs; destruct ns; inv Hset.
        now constructor.
        constructor.
        now eauto.
        eapply IHvs; eauto. }


      assert (Hlen : efnlst_length fnl = N.of_nat (List.length fnames)).
      { unfold fnames. rewrite pos_seq_len. lia. }

      assert (Hwf : efnlst_wf (N.of_nat (Datatypes.length (fnames ++ names))) fnl).
      { revert H5. rewrite length_app, Nnat.Nat2N.inj_add, Hlen.
        unfold names. rewrite pos_seq_len. generalize (N.of_nat (Datatypes.length fnames) + N.of_nat (Datatypes.length vs)).
        clear. induction fnl; intros m Hall.
        - constructor.
        - inv Hall. destructAll. constructor; eauto. }


      edestruct cps_fix_rel_exists with (fnames' := fnames) (m := next_id).

      eassumption.

      { eapply Union_Disjoint_r.
        constructor. intros z Hc. inv Hc. eapply pos_seq_In in H2.
        unfold In, next_id in *. inv H2. lia.
        constructor. intros z Hc. inv Hc. eapply pos_seq_In in H2.
        unfold In, next_id in *. lia. }

      unfold fnames. rewrite pos_seq_len. reflexivity.

      destructAll.


      edestruct (nth_error fnames (N.to_nat n)) eqn:Hnth.
      2:{ eapply nth_error_Some in Hnth. contradiction.
          unfold fnames. rewrite pos_seq_len. lia. }

      eexists. econstructor; [ eassumption  | | | | | | eassumption ].

      + eapply pos_seq_NoDup.

      + eapply pos_seq_NoDup.

      + unfold next_id. constructor. intros z Hc.
        inv Hc. unfold In in *. inv H2.
        eapply pos_seq_In in H7. lia.
        eapply pos_seq_In in H7. lia.

      + constructor. intros z Hc.
        inv Hc.  eapply pos_seq_In in H2.
        eapply pos_seq_In in H6. lia.

      + eassumption.

  Qed.


End Corresp.
