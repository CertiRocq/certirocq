(* Correctness of the ANF transformation from LambdaBoxLocal to LambdaANF *)
(* Follows the same proof technique as LambdaBoxLocal_to_LambdaANF_correct.v (CPS) *)

From Stdlib Require Import ZArith.ZArith Lists.List micromega.Lia Arith
     Ensembles Relations.Relation_Definitions.
Require Import MetaRocq.Utils.bytestring.
Require Import Common.AstCommon.
Require compcert.lib.Maps compcert.lib.Coqlib.
Require Import set_util.

Import ListNotations.
Open Scope list_scope.

Require Import LambdaBoxLocal.expression LambdaBoxLocal.fuel_sem.

Require Import cps cps_show eval ctx logical_relations
        List_util algebra alpha_conv functions Ensembles_util
        LambdaBoxLocal_to_LambdaANF LambdaBoxLocal_to_LambdaANF_util
        LambdaANF.tactics identifiers bounds cps_util rename stemctx
        LambdaBoxLocal_to_LambdaANF_anf_util
        LambdaBoxLocal_to_LambdaANF_anf_corresp.

Require Import ExtLib.Data.Monads.OptionMonad ExtLib.Structures.Monads.

Import Monad.MonadNotation.

Open Scope monad_scope.


(** * ANF Correctness *)

Section Correct.

  Context (prim_map : M.t Pipeline_utils.primitive).
  Context (func_tag kon_tag default_tag default_itag : positive)
          (cnstrs : conId_map)
          (cenv : ctor_env).

  Context (dcon_to_tag_inj :
    forall tgm dc dc',
      dcon_to_tag default_tag dc tgm = dcon_to_tag default_tag dc' tgm -> dc = dc').


  (** ** LambdaBoxLocal fuel and trace *)

  Definition fuel_exp (e: expression.exp) : nat :=
    match e with
    | Let_e _ _ _ => 0
    | _ => 1
    end.

  Fixpoint max_m_branches (br : branches_e) : nat :=
    match br with
    | brnil_e => 0
    | brcons_e _ (m, _) e br => max (N.to_nat m) (max_m_branches br)
    end.

  Definition anf_trace_exp (e: expression.exp) : nat :=
    match e with
    | Var_e _ => 1
    | Lam_e _ _ => 2
    | App_e _ _ => 2
    | Let_e _ _ _ => 0
    | Fix_e _ _ => 2
    | Con_e _ es => 2
    | Match_e _ _ brs => 4 + max_m_branches brs
    | Prf_e => 2
    | Prim_e x => 0
    | Prim_val_e x => 2
    end.

  Program Instance fuel_resource_LambdaBoxLocal : @resource expression.exp nat :=
    { zero := 0;
      one_i := fuel_exp;
      plus := Nat.add
    }.
  Next Obligation. lia. Qed.
  Next Obligation. lia. Qed.
  Next Obligation. lia. Qed.

  Program Instance trace_resource_LambdaBoxLocal : @resource expression.exp nat :=
    { zero := 0;
      one_i := anf_trace_exp;
      plus := Nat.add
    }.
  Next Obligation. lia. Qed.
  Next Obligation. lia. Qed.
  Next Obligation. lia. Qed.

  Global Instance LambdaBoxLocal_resource_fuel : @LambdaBoxLocal_resource nat.
  Proof. constructor. eapply fuel_resource_LambdaBoxLocal. Defined.

  Global Instance LambdaBoxLocal_resource_trace : @LambdaBoxLocal_resource nat.
  Proof. constructor. eapply trace_resource_LambdaBoxLocal. Defined.


  (** ** LambdaANF fuel and trace *)

  Global Program Instance trace_res_pre : @resource fin unit :=
    { zero := tt;
      one_i fin := tt;
      plus x y := tt; }.
  Next Obligation. destruct x. reflexivity. Qed.
  Next Obligation. destruct x; destruct y. reflexivity. Qed.

  Global Program Instance trace_res_exp : @exp_resource unit :=
    { HRes := trace_res_pre }.

  Global Instance trace_res : @trace_resource unit.
  Proof. econstructor. eapply trace_res_exp. Defined.

  Definition eq_fuel : @PostT nat unit :=
    fun '(e1, r1, f1, t1) '(e2, r2, f2, t2) => f1 = f2.

  Definition anf_bound (f_src t_src : nat) : @PostT nat unit :=
    fun '(e1, r1, f1, t1) '(e2, r2, f2, t2) =>
      (f1 + f_src <= f2)%nat /\
      (f2 <= f1 + t_src)%nat.

  Ltac unfold_all :=
    try unfold zero in *;
    try unfold one_ctx in *;
    try unfold algebra.one in *;
    try unfold one_i in *;
    try unfold algebra.HRes in *;
    try unfold HRexp_f in *; try unfold fuel_res in *; try unfold fuel_res_exp in *; try unfold fuel_res_pre in *;
    try unfold HRexp_t in *; try unfold trace_res in *; try unfold trace_res_exp in *; try unfold trace_res_pre in *.

  Global Instance eq_fuel_compat :
    @Post_properties cenv nat _ unit _ eq_fuel eq_fuel eq_fuel.
  Proof.
    unfold eq_fuel. constructor; try now (intro; intros; intro; intros; unfold_all; simpl; lia).
    - intro; intros. unfold post_base'. unfold_all; simpl. lia.
    - firstorder.
  Qed.

  Lemma eq_fuel_idemp :
    inclusion _ (comp eq_fuel eq_fuel) eq_fuel.
  Proof.
    unfold comp, eq_fuel. intro; intros.
    destruct x as [[[? ?] ?] ?].
    destruct y as [[[? ?] ?] ?]. destructAll.
    destruct x as [[[? ?] ?] ?]. congruence.
  Qed.



  Definition anf_cvt_rel := LambdaBoxLocal_to_LambdaANF.anf_cvt_rel func_tag default_tag.
  Definition anf_cvt_rel_exps := LambdaBoxLocal_to_LambdaANF.anf_cvt_rel_exps func_tag default_tag.
  Definition anf_cvt_rel_efnlst := LambdaBoxLocal_to_LambdaANF.anf_cvt_rel_efnlst func_tag default_tag.
  Definition anf_cvt_rel_branches := LambdaBoxLocal_to_LambdaANF.anf_cvt_rel_branches func_tag default_tag.


  (** ** ANF value relation (from LambdaBoxLocal_to_LambdaANF_anf_util) *)

  Definition anf_val_rel := LambdaBoxLocal_to_LambdaANF_anf_util.anf_val_rel func_tag default_tag cnstrs.
  Definition anf_env_rel := LambdaBoxLocal_to_LambdaANF_anf_util.anf_env_rel func_tag default_tag cnstrs.
  Definition anf_fix_rel := LambdaBoxLocal_to_LambdaANF_anf_util.anf_fix_rel func_tag default_tag cnstrs.


  (** ** Helper lemmas for environment relations *)

  Lemma anf_env_rel_weaken vnames vs x v rho :
    anf_env_rel vnames vs rho ->
    ~ x \in FromList vnames ->
    anf_env_rel vnames vs (M.set x v rho).
  Proof.
    intros Henv Hnin. unfold anf_env_rel, LambdaBoxLocal_to_LambdaANF_anf_util.anf_env_rel, anf_env_rel' in *.
    eapply Forall2_monotonic_strong; [ | eassumption ].
    simpl. intros x1 x2 Hin1 Hin2 Hr. rewrite M.gso; eauto.
    intros Hc; subst; auto.
  Qed.

  Lemma anf_env_rel_extend vnames vs x v v' rho :
    anf_env_rel vnames vs rho ->
    M.get x rho = Some v' ->
    anf_val_rel v v' ->
    anf_env_rel (x :: vnames) (v :: vs) rho.
  Proof.
    intros Henv Hget Hval. unfold anf_env_rel, LambdaBoxLocal_to_LambdaANF_anf_util.anf_env_rel, anf_env_rel' in *.
    econstructor; eauto.
  Qed.

  Lemma anf_env_rel_extend_weaken vnames vs x v v' rho :
    anf_env_rel vnames vs rho ->
    anf_val_rel v v' ->
    ~ x \in FromList vnames ->
    anf_env_rel (x :: vnames) (v :: vs) (M.set x v' rho).
  Proof.
    intros Henv Hval Hnin. unfold anf_env_rel, LambdaBoxLocal_to_LambdaANF_anf_util.anf_env_rel, anf_env_rel' in *.
    econstructor; eauto.
    - rewrite M.gss. eexists. split; eauto.
    - eapply anf_env_rel_weaken; eauto.
  Qed.


  (** Setting a variable preserves env_rel when the value is related
      at every position where the variable appears in vnames.
      This generalizes anf_env_rel_weaken (which requires x ∉ vnames). *)
  Lemma anf_env_rel_set vnames vs x v' rho :
    anf_env_rel vnames vs rho ->
    (forall k, nth_error vnames k = Some x ->
      exists v, nth_error vs k = Some v /\ anf_val_rel v v') ->
    anf_env_rel vnames vs (M.set x v' rho).
  Proof.
    unfold anf_env_rel, LambdaBoxLocal_to_LambdaANF_anf_util.anf_env_rel, anf_env_rel'.
    intros Henv Hdup.
    revert vs Henv Hdup.
    induction vnames as [ | y vnames' IH]; intros vs Henv Hdup.
    - inv Henv. constructor.
    - destruct vs as [ | v_s vs']; [inv Henv | ].
      inv Henv. constructor.
      + destruct (Pos.eq_dec y x) as [-> | Hneq].
        * rewrite M.gss.
          destruct (Hdup 0%nat eq_refl) as [v_src [Hnth Hrel]].
          simpl in Hnth. inv Hnth.
          eexists; eauto.
        * rewrite M.gso; [ | auto]. assumption.
      + eapply IH; [assumption | ].
        intros k Hnth. exact (Hdup (S k) Hnth).
  Qed.


  Lemma anf_env_rel_nth_error vnames vs rho n y v :
    anf_env_rel vnames vs rho ->
    nth_error vnames n = Some y ->
    nth_error vs n = Some v ->
    exists v', M.get y rho = Some v' /\ anf_val_rel v v'.
  Proof.
    intros Hrel. revert n y v; induction Hrel; intros n z v Hnth1 Hnth2.
    - destruct n; simpl in *; congruence.
    - destruct n; simpl in *.
      + inv Hnth1. inv Hnth2. destructAll. eauto.
      + eauto.
  Qed.


  Lemma anf_env_rel_length vnames vs rho :
    anf_env_rel vnames vs rho ->
    Datatypes.length vnames = Datatypes.length vs.
  Proof.
    unfold anf_env_rel, LambdaBoxLocal_to_LambdaANF_anf_util.anf_env_rel, anf_env_rel'. intros H.
    induction H; simpl; auto.
  Qed.

  Lemma well_formed_val_from_eval vs e v f t :
    eval_env_fuel vs e (Val v) f t ->
    well_formed_env vs ->
    exp_wf (N.of_nat (Datatypes.length vs)) e ->
    well_formed_val v.
  Proof.
    intros Heval Hwf_env Hwf_e.
    eapply eval_env_step_preserves_wf; eauto.
  Qed.


  Definition anf_fix_rel_fnames_length :=
    LambdaBoxLocal_to_LambdaANF_anf_util.anf_fix_rel_fnames_length func_tag default_tag cnstrs.
  Definition anf_fix_rel_names :=
    LambdaBoxLocal_to_LambdaANF_anf_util.anf_fix_rel_names func_tag default_tag cnstrs.
  Definition anf_fix_rel_find_def :=
    LambdaBoxLocal_to_LambdaANF_anf_util.anf_fix_rel_find_def func_tag default_tag cnstrs.
  Definition anf_fix_rel_find_def_ext :=
    LambdaBoxLocal_to_LambdaANF_anf_util.anf_fix_rel_find_def_ext func_tag default_tag cnstrs.

  Local Lemma nth_error_Forall2 (A B : Type) (P : A -> B -> Prop)
        (l : list A) (l' : list B) :
    (forall n t, nth_error l n = Some t ->
                 exists t', nth_error l' n = Some t' /\ P t t') ->
    Datatypes.length l = Datatypes.length l' ->
    Forall2 P l l'.
  Proof.
    revert l'; induction l; intros l' Hyp Hlen.
    - destruct l'; simpl in *; [ constructor | congruence ].
    - destruct l'; simpl in *; [ congruence | ]. constructor.
      + destruct (Hyp 0%nat a eq_refl) as [? [Hnth ?]]. inv Hnth. assumption.
      + eapply IHl; [ | congruence ].
        intros n t Hn. exact (Hyp (S n) t Hn).
  Qed.

  (* Environment relation extends to include fixpoint function definitions.
     Analogous to cps_env_rel_extend_fundefs in LambdaBoxLocal_to_LambdaANF_correct.v. *)
  Lemma anf_env_rel_extend_fundefs fnames names S1 fns Bs S2 rho vs :
    anf_env_rel names vs rho ->
    anf_fix_rel fnames names S1 fnames fns Bs S2 ->
    NoDup fnames ->
    env_consistent names vs ->
    Disjoint var (FromList names :|: FromList fnames) S1 ->
    Disjoint var (FromList names) (FromList fnames) ->
    anf_env_rel (rev fnames ++ names) (make_rec_env_rev_order fns vs) (def_funs Bs Bs rho rho).
  Proof.
    intros Hrel Hfix Hnd Hcons Hdis1 Hdis2.
    unfold anf_env_rel, LambdaBoxLocal_to_LambdaANF_anf_util.anf_env_rel, anf_env_rel' in *.
    destruct (make_rec_env_rev_order_app fns vs) as [vs' [Hrec [Hlen_vs' Hnth_vs']]].
    rewrite Hrec.
    assert (Hfnames_len : Datatypes.length fnames = efnlength fns).
    { erewrite <- anf_fix_rel_fnames_length; eauto. }
    assert (Hlen : Datatypes.length vs' = Datatypes.length (rev fnames)).
    { rewrite length_rev. lia. }
    eapply Forall2_app.
    - (* Part 1: fixpoint closures correspond to rev fnames *)
      eapply nth_error_Forall2; [ | exact Hlen ].
      intros n t Hnth.
      assert (Hn_bound : (n < efnlength fns)%nat).
      { eapply MRList.nth_error_Some_length in Hnth. lia. }
      assert (Hnth_vs := Hnth_vs' n Hn_bound).
      rewrite Hnth_vs in Hnth. inv Hnth.
      assert (Hn_rev : (n < Datatypes.length (rev fnames))%nat).
      { rewrite length_rev. lia. }
      assert (exists f, nth_error (rev fnames) n = Some f) as [f Hf].
      { apply nth_error_Some in Hn_rev.
        destruct (nth_error (rev fnames) n); eauto. congruence. }
      eexists. split. exact Hf.
      eexists. split.
      + rewrite def_funs_eq. reflexivity.
        eapply Same_set_all_fun_name.
        rewrite (anf_fix_rel_names _ _ _ _ _ _ _ Hfix).
        rewrite <- FromList_rev. eapply nth_error_In. exact Hf.
      + econstructor; try eassumption.
        rewrite Nnat.Nat2N.id.
        assert (Hf' := Hf).
        rewrite MRList.nth_error_rev_inv in Hf';
          [ | rewrite length_rev in Hn_rev; exact Hn_rev ].
        rewrite Hfnames_len in Hf'.
        replace (efnlength fns - S n)%nat with (efnlength fns - n - 1)%nat in Hf' by lia.
        exact Hf'.
    - (* Part 2: original env variables preserved by def_funs *)
      eapply Forall2_monotonic_strong; [ | eassumption ].
      intros v x Hv_in Hx_in [v' [Hget Hval]].
      eexists. split; [ | exact Hval ].
      rewrite def_funs_neq; [ exact Hget | ].
      intros Hc. eapply Hdis2. constructor.
      + exact Hx_in.
      + apply Same_set_all_fun_name in Hc.
        rewrite (anf_fix_rel_names _ _ _ _ _ _ _ Hfix) in Hc. exact Hc.
  Qed.

  Lemma anf_env_rel_weaken_setlists vnames vs ys ws rho rho' :
    anf_env_rel vnames vs rho ->
    set_lists ys ws rho = Some rho' ->
    Disjoint _ (FromList ys) (FromList vnames) ->
    anf_env_rel vnames vs rho'.
  Proof.
    revert ws rho rho'; induction ys; intros ws rho1 rho2 Hrel Hset Hdis.
    - destruct ws; inv Hset. exact Hrel.
    - destruct ws; [ discriminate | ].
      simpl in Hset.
      destruct (set_lists ys ws rho1) eqn:Hset'; [ | discriminate ]. inv Hset.
      apply anf_env_rel_weaken.
      + eapply IHys; [ exact Hrel | exact Hset' | ].
        eapply Disjoint_Included_l; [ | exact Hdis ].
        intros z Hz. right. exact Hz.
      + intros Hc. eapply Hdis. constructor.
        * left. reflexivity.
        * exact Hc.
  Qed.

  Lemma anf_env_rel_extend_get_list vnames vs xs ws us rho :
    anf_env_rel vnames vs rho ->
    get_list xs rho = Some ws ->
    Forall2 anf_val_rel us ws ->
    anf_env_rel (xs ++ vnames) (us ++ vs) rho.
  Proof.
    revert ws us; induction xs; intros ws us Hrel Hget Hall.
    - simpl in Hget. inv Hget. inv Hall. simpl. exact Hrel.
    - simpl in Hget.
      destruct (M.get a rho) as [va | ] eqn:Ha; [ | discriminate ].
      destruct (get_list xs rho) as [ws' | ] eqn:Hrest; [ | discriminate ].
      injection Hget as Heq. subst ws.
      destruct us as [ | u us']; [ inv Hall | ].
      inversion Hall as [ | ? ? ? ? Hvr Hall']. subst. simpl.
      eapply anf_env_rel_extend.
      + eapply IHxs; [ exact Hrel | reflexivity | exact Hall' ].
      + exact Ha.
      + exact Hvr.
  Qed.

  Lemma Forall2_nth_error_l {A B} (R : A -> B -> Prop) l1 l2 k a :
    Forall2 R l1 l2 ->
    nth_error l1 k = Some a ->
    exists b, nth_error l2 k = Some b /\ R a b.
  Proof.
    intros HF2 Hk. revert k Hk.
    induction HF2 as [ | a' b' l1' l2' Hab HF2' IH]; intros k Hk.
    - destruct k; simpl in Hk; discriminate.
    - destruct k as [ | k']; simpl in Hk.
      + inv Hk. exists b'. split; [ reflexivity | exact Hab ].
      + exact (IH k' Hk).
  Qed.

  Lemma Forall2_nth_error_r {A B} (R : A -> B -> Prop) l1 l2 k b :
    Forall2 R l1 l2 ->
    nth_error l2 k = Some b ->
    exists a, nth_error l1 k = Some a /\ R a b.
  Proof.
    intros HF2 Hk. revert k Hk.
    induction HF2 as [ | a' b' l1' l2' Hab HF2' IH]; intros k Hk.
    - destruct k; simpl in Hk; discriminate.
    - destruct k as [ | k']; simpl in Hk.
      + inv Hk. exists a'. split; [ reflexivity | exact Hab ].
      + exact (IH k' Hk).
  Qed.

  (* Helper: relate get_list output to individual M.get lookups via nth_error *)
  Lemma get_list_nth_error (xs : list var) (vs : list val) (rho : M.t val)
        (k : nat) (x : var) :
    get_list xs rho = Some vs ->
    nth_error xs k = Some x ->
    nth_error vs k = M.get x rho.
  Proof.
    revert vs k. induction xs as [ | a xs' IH]; intros vs k Hgl Hnth.
    - destruct k; simpl in Hnth; discriminate.
    - simpl in Hgl.
      destruct (M.get a rho) eqn:Ha; [ | discriminate ].
      destruct (get_list xs' rho) eqn:Hrest; [ | discriminate ].
      inv Hgl.
      destruct k as [ | k'].
      + simpl in Hnth. inv Hnth. simpl. symmetry. exact Ha.
      + simpl in Hnth. simpl. exact (IH l k' eq_refl Hnth).
  Qed.

  (* Environment relation extends through set_lists with reversed variable list.
     Used for Match_e case where constructor fields are bound via set_lists (rev vars). *)
  Lemma anf_env_rel_extend_weaken_setlists_rev vnames vs xs vs1 vs2 rho rho' :
    anf_env_rel vnames vs rho ->
    set_lists (rev xs) vs2 rho = Some rho' ->
    Forall2 anf_val_rel vs1 vs2 ->
    Disjoint _ (FromList xs) (FromList vnames) ->
    NoDup xs ->
    anf_env_rel (xs ++ vnames) (rev vs1 ++ vs) rho'.
  Proof.
    intros Hrel Hset Hval Hdis Hnd.
    assert (Hlen_eq : Datatypes.length xs = Datatypes.length vs1).
    { assert (Hlen1 : Datatypes.length vs1 = Datatypes.length vs2).
      { eapply Forall2_length; exact Hval. }
      assert (Hlen2 := set_lists_length_eq _ _ _ _ Hset).
      rewrite length_rev in Hlen2. lia. }
    unfold anf_env_rel, LambdaBoxLocal_to_LambdaANF_anf_util.anf_env_rel, anf_env_rel' in *.
    assert (Hgl : get_list (rev xs) rho' = Some vs2).
    { eapply get_list_set_lists; [ | exact Hset ].
      apply NoDup_rev. exact Hnd. }
    assert (Hlen_rev : Datatypes.length (rev vs1) = Datatypes.length xs).
    { rewrite length_rev. lia. }
    eapply Forall2_app.
    - eapply nth_error_Forall2; [ | exact Hlen_rev ].
      intros n v1r Hnth_v1r.
      assert (Hn_bound : (n < Datatypes.length xs)%nat).
      { rewrite <- Hlen_rev. eapply MRList.nth_error_Some_length. exact Hnth_v1r. }
      (* v1r = (rev vs1)[n] = vs1[length vs1 - 1 - n] *)
      assert (Hnth_v1r' := Hnth_v1r).
      rewrite MRList.nth_error_rev_inv in Hnth_v1r'; [ | rewrite length_rev in *; lia ].
      (* xs[n] is some variable x *)
      destruct (nth_error xs n) as [x | ] eqn:Hx; [ | exfalso; apply nth_error_None in Hx; lia ].
      eexists. split. reflexivity.
      (* M.get x rho' = vs2[length xs - 1 - n] *)
      assert (Hnth_rev_xs : nth_error (rev xs) (Datatypes.length xs - 1 - n) = Some x).
      { rewrite MRList.nth_error_rev_inv; [ | lia ].
        replace (Datatypes.length xs - S (Datatypes.length xs - 1 - n))%nat with n by lia.
        exact Hx. }
      assert (Hget_x : nth_error vs2 (Datatypes.length xs - 1 - n) = M.get x rho').
      { eapply get_list_nth_error; [ exact Hgl | exact Hnth_rev_xs ]. }
      destruct (nth_error vs2 (Datatypes.length xs - 1 - n)) as [v2 | ] eqn:Hv2;
        [ | exfalso; apply nth_error_None in Hv2;
            assert (tmp : Datatypes.length vs1 = Datatypes.length vs2)
              by (eapply Forall2_length; exact Hval); lia ].
      eexists. split.
      + symmetry. exact Hget_x.
      + (* anf_val_rel v1r v2 *)
        (* v1r = vs1[length vs1 - 1 - n], v2 = vs2[length xs - 1 - n] *)
        (* Forall2 anf_val_rel vs1 vs2 at index (length vs1 - 1 - n) *)
        replace (Datatypes.length vs1 - S n)%nat
          with (Datatypes.length xs - 1 - n)%nat in Hnth_v1r' by lia.
        destruct (Forall2_nth_error_r _ _ _ _ _ Hval Hv2) as [v1' [Hv1' Hvrel]].
        rewrite Hv1' in Hnth_v1r'. inv Hnth_v1r'. exact Hvrel.
    - eapply anf_env_rel_weaken_setlists; [ exact Hrel | exact Hset | ].
      rewrite FromList_rev. exact Hdis.
  Qed.


  (** ** Reduction lemmas *)

  Definition one_step : @PostT nat unit :=
    fun '(e1, r1, f1, t1) '(e2, r2, f2, t2) => (f1 + 1)%nat = f2.


  Lemma preord_exp_Efun_red k e B rho :
    preord_exp cenv one_step eq_fuel k (e, def_funs B B rho rho) (Efun B e, rho).
  Proof.
    intros r cin cout Hleq Hbstep.
    do 3 eexists. split. econstructor 2. econstructor. eassumption.
    split. simpl. unfold_all. lia.
    eapply preord_res_refl; tci.
  Qed.

  Lemma preord_exp_Econstr_red k x ctag ys e rho vs :
    get_list ys rho = Some vs ->
    preord_exp cenv one_step eq_fuel k (e, M.set x (Vconstr ctag vs) rho) (Econstr x ctag ys e, rho).
  Proof.
    intros Hgvs r cin cout Hleq Hbstep.
    do 3 eexists. split. econstructor 2. econstructor; eauto.
    split. simpl. unfold_all. lia.
    eapply preord_res_refl; tci.
  Qed.

  Lemma preord_exp_Eproj_red k x ctag n y e rho v vs :
    M.get y rho = Some (Vconstr ctag vs) ->
    nthN vs n = Some v ->
    preord_exp cenv one_step eq_fuel k (e, M.set x v rho) (Eproj x ctag n y e, rho).
  Proof.
    intros Hget Hnth r cin cout Hleq Hbstep.
    do 3 eexists. split. econstructor 2. econstructor; eauto.
    split. simpl. unfold_all. lia.
    eapply preord_res_refl; tci.
  Qed.

  (* Note: no preord_exp_Eprim_val_red because bstep has no constructor for Eprim_val.
     Eprim_val expressions always OOT in bstep_fuel (BStepf_OOT only).
     See preord_exp_prim_val_compat in logical_relations.v for the vacuous compatibility lemma. *)



  Definition eq_fuel_n (n : nat) : @PostT nat unit :=
    fun '(e1, r1, f1, t1) '(e2, r2, f2, t2) => (f1 + n)%nat = f2.

  Lemma preord_exp_Ecase_red k rho ctag vs P e n y :
    M.get y rho = Some (Vconstr ctag vs) ->
    find_tag_nth P ctag e n ->
    preord_exp cenv one_step eq_fuel k (e, rho) (Ecase y P, rho).
  Proof.
    intros Hget Hnth r cin cout Hleq Hbstep.
    do 3 eexists. split. econstructor 2. econstructor; eauto.
    admit. (* caseConsistent — same admit as CPS version *)
    split. simpl. unfold_all. lia.
    eapply preord_res_refl; tci.
  Admitted.

  Lemma ctx_bind_proj_preord_exp :
    forall vars C k r n e rho rho' vs vs' ctag,
      n = (List.length vars) ->
      ~ r \in FromList vars ->
      ctx_bind_proj ctag r vars n = C ->
      M.get r rho = Some (Vconstr ctag (vs ++ vs')) ->
      set_lists (rev vars) vs rho = Some rho' ->
      preord_exp cenv (eq_fuel_n n) eq_fuel k (e, rho') (C |[ e ]|, rho).
  Proof.
    induction vars; intros C k r n e rho rho' vs vs' ctag Heq Hnin Hctx Hget Hset.
    - destruct vs. 2:{ simpl in Hset. destruct (rev vs); inv Hset. }
      simpl in Hset. inv Hset.
      simpl.
      intros r0 cin cout Hleq Hbstep.
      do 3 eexists. split. exact Hbstep.
      split. unfold eq_fuel_n. lia.
      eapply preord_res_refl; tci.
    - destruct n; inv Heq.
      simpl ctx_bind_proj.
      change (rev (a :: vars)) with (rev vars ++ [a]) in *.
      revert vs Hget Hset.
      intros vs. eapply MRList.rev_ind with (l := vs).
      + intros Hget Hset. eapply set_lists_length_eq in Hset.
        rewrite length_app in Hset. simpl in Hset. lia.
      + intros x l IH Hget Hset.
        assert (Hlen : Datatypes.length vars = Datatypes.length l).
        { assert (Htmp := set_lists_length_eq _ _ _ _ Hset).
          rewrite !length_app in Htmp. simpl in Htmp.
          rewrite length_rev in Htmp. lia. }
        assert (Hlen_rev : Datatypes.length (rev vars) = Datatypes.length l).
        { rewrite length_rev. exact Hlen. }
        set (setl := @set_lists_app val).
        edestruct setl as [rho_mid [Hset_tail Hset_head]].
        eassumption. eassumption.
        simpl in Hset_tail. inv Hset_tail.
        eapply preord_exp_post_monotonic.
        2:{ eapply preord_exp_trans. tci. eapply eq_fuel_idemp.
            2:{ intros m. eapply preord_exp_Eproj_red. eassumption.
                eapply nthN_is_Some_app.
                rewrite Hlen. rewrite nthN_app_geq. simpl.
                replace (N.of_nat (Datatypes.length l - 0) - N.of_nat (Datatypes.length l))%N with 0%N by lia.
                reflexivity.
                lia. }
            repeat normalize_sets.
            eapply IHvars with (vs := l). reflexivity. eauto.
            rewrite Nat.sub_0_r. reflexivity.
            rewrite M.gso; eauto.
            rewrite app_assoc. eassumption.
            now intros Hc; subst; eauto. eassumption. }
        { unfold comp, eq_fuel_n, eq_fuel. intro; intros. destructAll.
          repeat match goal with [ X : _ * _ |- _ ] => destruct X end.
          unfold one_step in *. lia. }
  Qed.

  (** ** Subset lemma for ANF relation *)

  Lemma Setminus_Included_preserv_alt :
    forall {A: Type} (S1 S2 S3: Ensemble A),
      S1 \subset S2 \\ S3 -> S1 \subset S2.
  Proof.
    intros A S1 S2 S3 H x Hin. apply H in Hin. destruct Hin. assumption.
  Qed.

  (* Helper tactic: apply an IH to the matching relation hypothesis *)
  Local Ltac apply_cvt_IH IH e :=
    match goal with
    | [ H : anf_cvt_rel _ e _ _ _ _ _ |- _ ] => eapply IH in H
    | [ H : anf_cvt_rel_exps _ e _ _ _ _ _ |- _ ] => eapply IH in H
    | [ H : anf_cvt_rel_efnlst _ e _ _ _ _ _ |- _ ] => eapply IH in H
    | [ H : anf_cvt_rel_branches _ e _ _ _ _ _ |- _ ] => eapply IH in H
    end.

  Lemma anf_cvt_rel_subset :
    (forall S e vn tgm S' C x,
        anf_cvt_rel S e vn tgm S' C x -> S' \subset S) /\
    (forall S es vn tgm S' C xs,
        anf_cvt_rel_exps S es vn tgm S' C xs -> S' \subset S) /\
    (forall S efns vn fnames tgm S' fdefs,
        anf_cvt_rel_efnlst S efns vn fnames tgm S' fdefs -> S' \subset S) /\
    (forall S bs vn r tgm S' pats,
        anf_cvt_rel_branches S bs vn r tgm S' pats -> S' \subset S).
  Proof.
    enough (H :
      (forall e S vn tgm S' C x, anf_cvt_rel S e vn tgm S' C x -> S' \subset S) /\
      (forall es S vn tgm S' C xs, anf_cvt_rel_exps S es vn tgm S' C xs -> S' \subset S) /\
      (forall efns S vn fnames tgm S' fdefs, anf_cvt_rel_efnlst S efns vn fnames tgm S' fdefs -> S' \subset S) /\
      (forall bs S vn r tgm S' pats, anf_cvt_rel_branches S bs vn r tgm S' pats -> S' \subset S)).
    { destruct H as [H1 [H2 [H3 H4]]]. repeat split; intros; eauto. }
    eapply exp_ind_alt_2.
    - (* Var_e *)
      intros n S vn tgm S' C x Hrel. inv Hrel. eapply Included_refl.
    - (* Lam_e *)
      intros na e IH S vn tgm S' C x Hrel. inv Hrel. fold anf_cvt_rel in *.
      apply_cvt_IH IH e.
      eapply Included_trans. eassumption.
      eapply Included_trans. eapply Setminus_Included. eapply Setminus_Included.
    - (* App_e *)
      intros e1 IHe1 e2 IHe2 S vn tgm S' C x Hrel.
      inv Hrel. fold anf_cvt_rel in *.
      apply_cvt_IH IHe1 e1. apply_cvt_IH IHe2 e2.
      eapply Included_trans. eapply Setminus_Included.
      eapply Included_trans; eassumption.
    - (* Con_e *)
      intros dc es IH S vn tgm S' C x Hrel.
      inv Hrel. fold anf_cvt_rel_exps in *.
      apply_cvt_IH IH es.
      eapply Included_trans. eassumption. eapply Setminus_Included.
    - (* Match_e *)
      intros e IHe pars bs IHbs S vn tgm S' C x Hrel.
      inv Hrel. fold anf_cvt_rel in *. fold anf_cvt_rel_branches in *.
      apply_cvt_IH IHe e. apply_cvt_IH IHbs bs.
      eapply Included_trans. eapply Setminus_Included.
      eapply Included_trans. eassumption.
      eapply Included_trans. eassumption.
      eapply Included_trans. eapply Setminus_Included. eapply Setminus_Included.
    - (* Let_e *)
      intros na e1 IHe1 e2 IHe2 S vn tgm S' C x Hrel.
      inv Hrel. fold anf_cvt_rel in *.
      apply_cvt_IH IHe1 e1. apply_cvt_IH IHe2 e2.
      eapply Included_trans; eassumption.
    - (* Fix_e *)
      intros efns IHefns n S vn tgm S' C x Hrel.
      inv Hrel. fold anf_cvt_rel_efnlst in *.
      apply_cvt_IH IHefns efns.
      eapply Included_trans. eassumption. eapply Setminus_Included.
    - (* Prf_e *)
      intros S vn tgm S' C x Hrel. inv Hrel.
      eapply Setminus_Included.
    - (* Prim_val_e *)
      intros p S vn tgm S' C x Hrel. inv Hrel.
      eapply Setminus_Included.
    - (* Prim_e *)
      intros p S vn tgm S' C x Hrel. inv Hrel.
    - (* enil *)
      intros S vn tgm S' C xs Hrel. inv Hrel. eapply Included_refl.
    - (* econs *)
      intros e IHe es IHes S vn tgm S' C xs Hrel.
      inv Hrel. fold anf_cvt_rel in *. fold anf_cvt_rel_exps in *.
      apply_cvt_IH IHe e. apply_cvt_IH IHes es.
      eapply Included_trans; eassumption.
    - (* eflnil *)
      intros S vn fnames tgm S' fdefs Hrel. inv Hrel. eapply Included_refl.
    - (* eflcons *)
      split.
      + intros na' e' Hlam IHe' efns IHefns S vn fnames tgm S' fdefs Hrel.
        inv Hrel. fold anf_cvt_rel in *. fold anf_cvt_rel_efnlst in *.
        (* inv any remaining Lam_e equalities *)
        repeat match goal with
        | [ H : Lam_e _ _ = Lam_e _ _ |- _ ] => inv H
        end.
        apply_cvt_IH IHe' e'. apply_cvt_IH IHefns efns.
        eapply Included_trans. eassumption.
        eapply Included_trans. eassumption. eapply Setminus_Included.
      + intros Hnot IHe efns IHefns S vn fnames tgm S' fdefs Hrel.
        inv Hrel. unfold isLambda in Hnot. contradiction.
    - (* brnil *)
      intros S vn r tgm S' pats Hrel. inv Hrel. eapply Included_refl.
    - (* brcons *)
      intros dc p e IHe bs IHbs S vn r tgm S' pats Hrel.
      inv Hrel. fold anf_cvt_rel in *. fold anf_cvt_rel_branches in *.
      apply_cvt_IH IHe e. apply_cvt_IH IHbs bs.
      match goal with
      | [ H : _ \subset _ \\ _ |- _ ] => eapply Setminus_Included_preserv_alt in H
      end.
      eapply Included_trans; eassumption.
  Qed.


  Lemma anf_cvt_exp_subset S e vn tgm S' C x :
    anf_cvt_rel S e vn tgm S' C x -> S' \subset S.
  Proof. eapply (proj1 anf_cvt_rel_subset). Qed.



  Lemma anf_cvt_rel_efnlst_all_fun_name S efns vn fnames tgm S' fdefs :
    anf_cvt_rel_efnlst S efns vn fnames tgm S' fdefs ->
    all_fun_name fdefs = fnames.
  Proof.
    intros H. induction H.
    - reflexivity.
    - simpl. congruence.
  Qed.


  (** ** Result variable is consumed by ANF conversion *)

  (* The result variable of an ANF conversion is NOT in the output set S'.
     This is because:
     - For Var_e: result ∈ FromList vn, and Disjoint gives result ∉ S = S'.
     - For all other constructors: result is consumed from S during conversion. *)
  Lemma anf_cvt_result_not_in_output :
    forall e S vn tgm S' C x,
      anf_cvt_rel S e vn tgm S' C x ->
      Disjoint _ (FromList vn) S -> ~ x \in S'.
  Proof.
    enough (H :
      (forall (e : expression.exp) S vn tgm S' C x,
          anf_cvt_rel S e vn tgm S' C x ->
          Disjoint _ (FromList vn) S -> ~ x \in S') /\
      (forall (es : exps), True) /\
      (forall (efns : efnlst), True) /\
      (forall (bs : branches_e), True)).
    { exact (proj1 H). }
    eapply exp_ind_alt_2.
    - (* Var_e *)
      intros n S vn tgm S' C x Hcvt Hdis.
      inv Hcvt.
      intros Hin. eapply Hdis. constructor; eauto.
      eapply nth_error_In. eassumption.
    - (* Lam_e *)
      intros na e IH S vn tgm S' C x Hcvt Hdis.
      inv Hcvt. fold anf_cvt_rel in *.
      intros Hin.
      assert (S' \subset S \\ [set x1] \\ [set x])
        by (eapply anf_cvt_exp_subset; eassumption).
      apply H in Hin. inv Hin. inv H0. eauto.
    - (* App_e *)
      intros e1 IH1 e2 IH2 S vn tgm S' C x Hcvt Hdis.
      inv Hcvt. fold anf_cvt_rel in *.
      intros Hin. inv Hin. eauto.
    - (* Con_e *)
      intros dc es IH S vn tgm S' C x Hcvt Hdis.
      inv Hcvt. fold anf_cvt_rel_exps in *.
      intros Hin.
      assert (S' \subset S \\ [set x])
        by (eapply (proj1 (proj2 anf_cvt_rel_subset)); eassumption).
      apply H in Hin. inv Hin. eauto.
    - (* Match_e *)
      intros e1 IH1 n bs IH2 S vn tgm S' C x Hcvt Hdis.
      inv Hcvt. fold anf_cvt_rel in *. fold anf_cvt_rel_branches in *.
      intros Hin. inv Hin. eauto.
    - (* Let_e *)
      intros na e1 IH1 e2 IH2 S vn tgm S' C x Hcvt Hdis.
      inv Hcvt. fold anf_cvt_rel in *.
      eapply IH2; [ eassumption | ].
      rewrite FromList_cons.
      eapply Union_Disjoint_l.
      + eapply Disjoint_Singleton_l.
        eapply IH1; eassumption.
      + eapply Disjoint_Included_r.
        eapply anf_cvt_exp_subset. eassumption.
        eassumption.
    - (* Fix_e *)
      intros efns IH n S vn tgm S' C x Hcvt Hdis.
      inv Hcvt. fold anf_cvt_rel_efnlst in *.
      intros Hin.
      assert (Hsub : S' \subset S \\ FromList fnames)
        by (eapply (proj1 (proj2 (proj2 anf_cvt_rel_subset))); eassumption).
      apply Hsub in Hin. inv Hin. apply H0.
      eapply nth_error_In. eassumption.
    - (* Prf_e *)
      intros S vn tgm S' C x Hcvt Hdis.
      inv Hcvt. intros Hin. inv Hin. eauto.
    - (* Prim_val_e *)
      intros p S vn tgm S' C x Hcvt Hdis.
      inv Hcvt. intros Hin. inv Hin. eauto.
    - (* Prim_e *) intros. inv H. (* no ANF conversion for Prim_e *)
    - (* enil *) exact I.
    - (* econs *) intros; exact I.
    - (* eflnil *) exact I.
    - (* eflcons *)
      split; intros; exact I.
    - (* brnil *) exact I.
    - (* brcons *) intros; exact I.
  Qed.


  (** ** Environment consistency and variable lookup *)

  Lemma NoDup_env_consistent (vn : list var) (rho : list value) :
    NoDup vn -> env_consistent vn rho.
  Proof.
    intros Hnd i j x Hi Hj.
    assert (Heq : i = j).
    { clear rho. revert j vn Hnd Hi Hj. induction i; intros j vn Hnd Hi Hj.
      - destruct vn; simpl in *; [ discriminate | ]. inv Hi.
        destruct j; [ reflexivity | ].
        simpl in Hj. inv Hnd. exfalso. apply H1. eapply nth_error_In. eassumption.
      - destruct vn; simpl in *; [ discriminate | ].
        destruct j; simpl in *.
        + inv Hnd. inv Hj. exfalso. apply H1. eapply nth_error_In. eassumption.
        + inv Hnd. f_equal. eapply IHi; eassumption. }
    subst. reflexivity.
  Qed.

  Lemma env_consistent_extend vn rho x1 v1 :
    env_consistent vn rho ->
    (forall k, nth_error vn k = Some x1 -> nth_error rho k = Some v1) ->
    env_consistent (x1 :: vn) (v1 :: rho).
  Proof.
    intros Hcons Hx1 i j y Hi Hj.
    destruct i as [ | i'], j as [ | j']; simpl in *.
    - reflexivity.
    - inv Hi. specialize (Hx1 j' Hj). rewrite Hx1. reflexivity.
    - inv Hj. specialize (Hx1 i' Hi). rewrite Hx1. reflexivity.
    - eapply Hcons; eassumption.
  Qed.

  Lemma env_consistent_app vn1 vn2 vs1 vs2 :
    env_consistent vn1 vs1 ->
    env_consistent vn2 vs2 ->
    Disjoint _ (FromList vn1) (FromList vn2) ->
    Datatypes.length vn1 = Datatypes.length vs1 ->
    env_consistent (vn1 ++ vn2) (vs1 ++ vs2).
  Proof.
    intros Hc1 Hc2 Hdis Hlen. intros i j x Hi Hj.
    destruct (Nat.lt_ge_cases i (Datatypes.length vn1)) as [Hilt | Hige];
    destruct (Nat.lt_ge_cases j (Datatypes.length vn1)) as [Hjlt | Hjge].
    - (* both in vn1 *)
      assert (Hi' := nth_error_app1 vn1 vn2 Hilt).
      assert (Hj' := nth_error_app1 vn1 vn2 Hjlt).
      rewrite Hi' in Hi. rewrite Hj' in Hj.
      assert (Hilt' : (i < Datatypes.length vs1)%nat) by lia.
      assert (Hjlt' : (j < Datatypes.length vs1)%nat) by lia.
      rewrite (nth_error_app1 vs1 vs2 Hilt').
      rewrite (nth_error_app1 vs1 vs2 Hjlt').
      exact (Hc1 _ _ _ Hi Hj).
    - (* i in vn1, j in vn2 — contradiction *)
      assert (Hi' := nth_error_app1 vn1 vn2 Hilt).
      assert (Hj' := nth_error_app2 vn1 vn2 Hjge).
      rewrite Hi' in Hi. rewrite Hj' in Hj.
      exfalso. eapply Hdis. constructor.
      + eapply nth_error_In. exact Hi.
      + eapply nth_error_In. exact Hj.
    - (* i in vn2, j in vn1 — contradiction *)
      assert (Hi' := nth_error_app2 vn1 vn2 Hige).
      assert (Hj' := nth_error_app1 vn1 vn2 Hjlt).
      rewrite Hi' in Hi. rewrite Hj' in Hj.
      exfalso. eapply Hdis. constructor.
      + eapply nth_error_In. exact Hj.
      + eapply nth_error_In. exact Hi.
    - (* both in vn2 *)
      assert (Hi' := nth_error_app2 vn1 vn2 Hige).
      assert (Hj' := nth_error_app2 vn1 vn2 Hjge).
      rewrite Hi' in Hi. rewrite Hj' in Hj.
      assert (Hige' : (Datatypes.length vs1 <= i)%nat) by lia.
      assert (Hjge' : (Datatypes.length vs1 <= j)%nat) by lia.
      rewrite (nth_error_app2 vs1 vs2 Hige').
      rewrite (nth_error_app2 vs1 vs2 Hjge').
      rewrite <- Hlen.
      exact (Hc2 _ _ _ Hi Hj).
  Qed.

  (* TODO move to more general file *)
  Lemma occurs_free_ctx_comp (C1 C2 : exp_ctx) :
    occurs_free_ctx (comp_ctx_f C1 C2) \subset
    occurs_free_ctx C1 :|: (occurs_free_ctx C2 \\ bound_stem_ctx C1).
  Proof.
    revert C2.
    eapply ctx_exp_mut with (P := fun C1 =>
                                    forall C2,
                                      occurs_free_ctx (comp_ctx_f C1 C2) \subset
                                                      occurs_free_ctx C1 :|: (occurs_free_ctx C2 \\ bound_stem_ctx C1))
                            (P0 := fun F =>
                                     forall C,
                                       occurs_free_fundefs_ctx (comp_f_ctx_f F C) \subset
                                                               occurs_free_fundefs_ctx F :|: (occurs_free_ctx C \\ (names_in_fundefs_ctx F :|: bound_stem_fundefs_ctx F))); intros.
    - simpl. normalize_occurs_free_ctx. normalize_bound_stem_ctx. sets.
    - simpl. repeat normalize_occurs_free_ctx.
      repeat normalize_bound_stem_ctx.
      eapply Union_Included. now sets.
      eapply Included_trans. eapply Included_Setminus_compat. eapply H. reflexivity.
      rewrite Setminus_Union_distr. now sets.
    - simpl. repeat normalize_occurs_free_ctx.
      repeat normalize_bound_stem_ctx. repeat normalize_bound_var.
      eapply Union_Included. now sets.
      eapply Included_trans. eapply Included_Setminus_compat. eapply H. reflexivity.
      rewrite Setminus_Union_distr. now sets.
    - simpl. repeat normalize_occurs_free_ctx.
      repeat normalize_bound_stem_ctx. repeat normalize_bound_var.
      eapply Included_trans. eapply Included_Setminus_compat. eapply H. reflexivity.
      rewrite Setminus_Union_distr.
      eapply Union_Included; now sets.
    - simpl. repeat normalize_occurs_free_ctx.
      repeat normalize_bound_stem_ctx. repeat normalize_bound_var.
      eapply Union_Included. now sets.
      eapply Included_trans. eapply Included_Setminus_compat. eapply H. reflexivity.
      rewrite Setminus_Union_distr.
      eapply Union_Included; now sets.
    - simpl. repeat normalize_occurs_free_ctx.
      repeat normalize_bound_stem_ctx. repeat normalize_bound_var.
      eapply Union_Included. now sets.
      eapply Included_trans. eapply Included_Setminus_compat. eapply H. reflexivity.
      rewrite Setminus_Union_distr.
      eapply Union_Included; now sets.
    - simpl. repeat normalize_occurs_free_ctx.
      repeat normalize_bound_stem_ctx. repeat normalize_bound_var.
      eapply Union_Included. now sets.
      eapply Union_Included.
      eapply Included_trans. eapply H. now sets.
      now sets.
    - simpl. repeat repeat normalize_occurs_free_ctx.
      repeat normalize_bound_stem_ctx. repeat normalize_bound_var.
      eapply Union_Included. now sets.
      eapply Included_trans. eapply Included_Setminus_compat. eapply H. reflexivity.
      rewrite Setminus_Union_distr.
      eapply Union_Included; now sets.
    - simpl. repeat normalize_occurs_free_ctx.
      repeat normalize_bound_stem_ctx. repeat normalize_bound_var.
      eapply Union_Included.
      eapply Included_trans. eapply H. now sets.
      rewrite name_in_fundefs_ctx_comp. now sets.
    - simpl. repeat normalize_occurs_free_ctx.
      eapply Union_Included; [ | now sets ].
      eapply Setminus_Included_Included_Union.
      eapply Included_trans. eapply H.
      eapply Union_Included.
      rewrite <- !Union_assoc.
      rewrite <- Union_Included_Union_Setminus with (s3 := (v |: (FromList l :|: name_in_fundefs f))).
      now sets. now tci. now sets.
      normalize_bound_stem_ctx.
      rewrite (Union_commut (bound_stem_ctx e) (FromList l)).
      rewrite !Union_assoc.
      rewrite (Union_commut _ (bound_stem_ctx e)).
      rewrite <- Setminus_Union with (s2 := bound_stem_ctx e).
      rewrite <- ! Union_assoc.
      rewrite <- Union_Included_Union_Setminus with (s3 := (v |: (name_in_fundefs f :|: FromList l))).
      now sets. now tci. now sets.
    - simpl. repeat normalize_occurs_free_ctx. repeat normalize_bound_stem_ctx.
      eapply Union_Included.
      + rewrite name_in_fundefs_ctx_comp. now sets.
      + eapply Included_trans. eapply Included_Setminus_compat. eapply H. reflexivity.
        rewrite !Setminus_Union_distr.
        eapply Union_Included. now sets. now xsets.
  Qed.

  Lemma occurs_free_ctx_app (C : exp_ctx)  (e : exp) :
    occurs_free (C |[ e ]|) \subset
    occurs_free_ctx C :|: (occurs_free e \\ bound_stem_ctx C).
  Proof.
    revert e.
    eapply ctx_exp_mut with (P := fun C =>
                                    forall e,
                                      occurs_free (C |[ e ]|) \subset
                                      occurs_free_ctx C :|: (occurs_free e \\ bound_stem_ctx C))
                            (P0 := fun F =>
                                     forall e,
                                       occurs_free_fundefs (F <[ e ]>) \subset
                                        occurs_free_fundefs_ctx F :|: (occurs_free e \\ (names_in_fundefs_ctx F :|: bound_stem_fundefs_ctx F))); intros.
    - simpl. normalize_occurs_free_ctx. normalize_bound_stem_ctx. sets.
    - simpl. repeat normalize_occurs_free. repeat normalize_occurs_free_ctx.
      repeat normalize_bound_stem_ctx. repeat normalize_bound_var.
      eapply Union_Included. now sets.
      eapply Included_trans. eapply Included_Setminus_compat. eapply H. reflexivity.
      rewrite Setminus_Union_distr.
      eapply Union_Included; now sets.
    - simpl. repeat normalize_occurs_free. repeat normalize_occurs_free_ctx.
      repeat normalize_bound_stem_ctx. repeat normalize_bound_var.
      eapply Union_Included. now sets.
      eapply Included_trans. eapply Included_Setminus_compat. eapply H. reflexivity.
      rewrite Setminus_Union_distr.
      eapply Union_Included; now sets.
    - simpl. repeat normalize_occurs_free. repeat normalize_occurs_free_ctx.
      repeat normalize_bound_stem_ctx. repeat normalize_bound_var.
      eapply Included_trans. eapply Included_Setminus_compat. eapply H. reflexivity.
      rewrite Setminus_Union_distr.
      eapply Union_Included; now sets.
    - simpl. repeat normalize_occurs_free. repeat normalize_occurs_free_ctx.
      repeat normalize_bound_stem_ctx. repeat normalize_bound_var.
      eapply Union_Included. now sets.
      eapply Included_trans. eapply Included_Setminus_compat. eapply H. reflexivity.
      rewrite Setminus_Union_distr.
      eapply Union_Included; now sets.
    - simpl. repeat normalize_occurs_free. repeat normalize_occurs_free_ctx.
      repeat normalize_bound_stem_ctx. repeat normalize_bound_var.
      eapply Union_Included. now sets.
      eapply Included_trans. eapply Included_Setminus_compat. eapply H. reflexivity.
      rewrite Setminus_Union_distr.
      eapply Union_Included; now sets.
    - simpl. repeat normalize_occurs_free. repeat normalize_occurs_free_ctx.
      repeat normalize_bound_stem_ctx. repeat normalize_bound_var.
      eapply Union_Included. now sets.
      eapply Union_Included. now sets.
      eapply Union_Included.
      + eapply Included_trans. eapply H.
        eapply Union_Included; now sets.
      + now sets.
    - simpl. repeat normalize_occurs_free. repeat normalize_occurs_free_ctx.
      repeat normalize_bound_stem_ctx. repeat normalize_bound_var.
      eapply Union_Included. now sets.
      eapply Included_trans. eapply Included_Setminus_compat. eapply H. reflexivity.
      rewrite Setminus_Union_distr.
      eapply Union_Included; now sets.
    - simpl. repeat normalize_occurs_free. repeat normalize_occurs_free_ctx.
      repeat normalize_bound_stem_ctx. repeat normalize_bound_var.
      eapply Union_Included.
      + eapply Included_trans. eapply H. now sets.
      + rewrite <- name_in_fundefs_ctx_ctx at 1. now sets.
    - simpl. repeat normalize_occurs_free. repeat normalize_occurs_free_ctx.
      repeat normalize_bound_stem_ctx.
      eapply Union_Included; [ | now sets ].

      eapply Setminus_Included_Included_Union.
      eapply Included_trans. eapply H.
      eapply Union_Included.
      + rewrite <- !Union_assoc.
        rewrite <- Union_Included_Union_Setminus with (s3 := (v |: (FromList l :|: name_in_fundefs f))).
        now sets. now tci. now sets.
      + rewrite (Union_commut (bound_stem_ctx e) (FromList l)).
        rewrite !Union_assoc.
        rewrite (Union_commut _ (bound_stem_ctx e)).
        rewrite <- Setminus_Union with (s2 := bound_stem_ctx e).
        rewrite <- ! Union_assoc.
        rewrite <- Union_Included_Union_Setminus with (s3 := (v |: (name_in_fundefs f :|: FromList l))).
        now sets. now tci. now sets.
    - simpl. repeat normalize_occurs_free_ctx. repeat normalize_bound_stem_ctx.
      repeat normalize_occurs_free.
      eapply Union_Included.
      + rewrite <- name_in_fundefs_ctx_ctx. now sets.
      + eapply Included_trans. eapply Included_Setminus_compat. eapply H. reflexivity.
        rewrite !Setminus_Union_distr.
        eapply Union_Included. now sets. now xsets.
  Qed.

  Lemma ctx_bind_proj_occurs_free_ctx tg r vars n :
    occurs_free_ctx (ctx_bind_proj tg r vars n) \subset [set r].
  Proof.
    revert n; induction vars as [ | v vars' IH]; intros n; simpl.
    - rewrite occurs_free_Hole_c. now sets.
    - rewrite occurs_free_Eproj_c.
      eapply Union_Included; [ now sets | ].
      eapply Included_trans; [ eapply Setminus_Included | exact (IH _) ].
  Qed.

  Lemma ctx_bind_proj_bound_stem_ctx tg r vars n :
    FromList vars \subset bound_stem_ctx (ctx_bind_proj tg r vars n).
  Proof.
    revert n; induction vars as [ | v vars' IH]; intros n.
    - simpl. rewrite FromList_nil. now sets.
    - intros z Hz. unfold FromList, In in Hz. destruct Hz as [Heq | Hin].
      + subst. simpl. constructor.
      + simpl. eapply SBound_Proj2_c. eapply IH. exact Hin.
  Qed.


  (* If x1 is a fresh variable (from S, disjoint from vnames), then
     x1 is in the consumed set (S \ S') and not the result variable x2. *)
  Lemma anf_cvt_result_in_consumed S1 S2 e vn tgm C x :
    anf_cvt_rel S1 e vn tgm S2 C x ->
    (x \in FromList vn \/ x \in S1).
  Proof.
    enough (H :
      (forall (e : expression.exp) S1 vn tgm S2 C x,
          anf_cvt_rel S1 e vn tgm S2 C x ->
          (x \in FromList vn \/ x \in S1)) /\
      (forall (es : exps), True) /\
      (forall (efns : efnlst), True) /\
      (forall (bs : branches_e), True)).
    { exact (proj1 H e S1 vn tgm S2 C x). }
    eapply exp_ind_alt_2.
    - (* Var_e *)
      intros n S1' vn' tgm' S2' C' x' Hcvt.
      inv Hcvt. left. eapply nth_error_In. eassumption.
    - (* Lam_e *)
      intros na e1 IH S1' vn' tgm' S2' C' x' Hcvt.
      inv Hcvt. fold anf_cvt_rel in *.
      right. destruct H3. assumption.
    - (* App_e *)
      intros e1 IH1 e2 IH2 S1' vn' tgm' S2' C' x' Hcvt.
      inv Hcvt. fold anf_cvt_rel in *.
      right.
      repeat match goal with
      | [ H : anf_cvt_rel _ _ _ _ _ _ _ |- _ ] =>
        apply anf_cvt_exp_subset in H
      end.
      eauto.
    - (* Con_e *)
      intros dc es IH S1' vn' tgm' S2' C' x' Hcvt.
      inv Hcvt. fold anf_cvt_rel_exps in *.
      right. assumption.
    - (* Match_e *)
      intros e1 IH1 n bs IH2 S1' vn' tgm' S2' C' x' Hcvt.
      inv Hcvt. fold anf_cvt_rel in *. fold anf_cvt_rel_branches in *.
      right.
      repeat match goal with
      | [ H : anf_cvt_rel _ _ _ _ _ _ _ |- _ ] =>
        apply anf_cvt_exp_subset in H
      | [ H : anf_cvt_rel_branches _ _ _ _ _ _ _ |- _ ] =>
        apply (proj2 (proj2 (proj2 anf_cvt_rel_subset))) in H
      end.
      match goal with
      | [ Hin : x' \in ?S3m, Hsub1 : ?S3m \subset ?S2m,
          Hsub2 : ?S2m \subset _ |- _ ] =>
        apply Hsub1 in Hin; apply Hsub2 in Hin;
        destruct Hin as [ [Hin _] _]; exact Hin
      end.
    - (* Let_e *)
      intros na e1 IH1 e2 IH2 S1' vn' tgm' S2' C' x' Hcvt.
      inv Hcvt. fold anf_cvt_rel in *.
      match goal with
      | [ Hcvt2 : anf_cvt_rel _ e2 (_ :: vn') _ _ _ x' |- _ ] =>
        destruct (IH2 _ _ _ _ _ _ Hcvt2) as [Hvn2 | HS2]
      end.
      + rewrite FromList_cons in Hvn2. inv Hvn2.
        * match goal with [ Heq : In _ [set _] _ |- _ ] => inv Heq end.
          match goal with
          | [ Hcvt1 : anf_cvt_rel S1' e1 vn' _ _ _ _ |- _ ] =>
            destruct (IH1 _ _ _ _ _ _ Hcvt1) as [Hvn1 | HS1]
          end.
          -- left. exact Hvn1.
          -- right. exact HS1.
        * left. assumption.
      + right.
        match goal with
        | [ Hcvt1 : anf_cvt_rel S1' e1 vn' _ _ _ _ |- _ ] =>
          eapply anf_cvt_exp_subset in Hcvt1; apply Hcvt1; exact HS2
        end.
    - (* Fix_e *)
      intros efns IH n S1' vn' tgm' S2' C' x' Hcvt.
      inv Hcvt. fold anf_cvt_rel_efnlst in *.
      right.
      match goal with
      | [ Hsub : FromList _ \subset S1',
          Hnth : nth_error _ _ = Some x' |- _ ] =>
        eapply Hsub; eapply nth_error_In; eassumption
      end.
    - (* Prf_e *)
      intros S1' vn' tgm' S2' C' x' Hcvt.
      inv Hcvt. right. assumption.
    - (* Prim_val_e *)
      intros p S1' vn' tgm' S2' C' x' Hcvt.
      inv Hcvt. right. assumption.
    - (* Prim_e *) intros. inv H. (* no ANF conversion for Prim_e *)
    - (* enil *) exact I.
    - (* econs *) intros; exact I.
    - (* eflnil *) exact I.
    - (* eflcons *) split; intros; exact I.
    - (* brnil *) exact I.
    - (* brcons *) intros; exact I.
  Qed.

  (* All result variables of an exps conversion are in FromList vn or in the starting state S. *)
  Lemma anf_cvt_rel_exps_results_in_consumed S es vn tgm S' C xs :
    anf_cvt_rel_exps S es vn tgm S' C xs ->
    forall x, List.In x xs -> (x \in FromList vn \/ x \in S).
  Proof.
    intros H. induction H.
    - intros x Hin. destruct Hin.
    - intros y Hin. destruct Hin as [Heq | Hin].
      + subst. eapply anf_cvt_result_in_consumed. eassumption.
      + destruct (IHanf_cvt_rel_exps _ Hin) as [Hl | Hr].
        * left. exact Hl.
        * right. eapply (anf_cvt_exp_subset _ _ _ _ _ _ _ H). exact Hr.
  Qed.

  (* If x is in target and all branch bodies' free vars are in target,
     then occurs_free (Ecase x pats) is in target. *)
  Lemma occurs_free_Ecase_all_branches x pats (target : Ensemble var) :
    x \in target ->
    (forall c e, List.In (c, e) pats -> occurs_free e \subset target) ->
    occurs_free (Ecase x pats) \subset target.
  Proof.
    intros Hx Hall z Hz.
    induction pats as [ | [c e] pats' IHpats].
    - rewrite occurs_free_Ecase_nil in Hz. inv Hz. exact Hx.
    - rewrite occurs_free_Ecase_cons in Hz. inv Hz.
      + inv H. exact Hx.
      + inv H.
        * eapply Hall. now left. exact H0.
        * eapply IHpats.
          -- intros c' e' Hin'. eapply Hall. now right.
          -- exact H0.
  Qed.

  (* Free variables of an ANF conversion context come from variable names
     or consumed state variables. Proved by mutual induction on anf_cvt_rel,
     using occurs_free_ctx_app and occurs_free_ctx_comp. *)
  Lemma anf_cvt_occurs_free_mutual :
    (forall e S vn tgm S' C x,
        anf_cvt_rel S e vn tgm S' C x ->
        Disjoint _ (FromList vn) S ->
        occurs_free_ctx C \subset FromList vn :|: (S \\ S')) /\
    (forall es S vn tgm S' C xs,
        anf_cvt_rel_exps S es vn tgm S' C xs ->
        Disjoint _ (FromList vn) S ->
        occurs_free_ctx C \subset FromList vn :|: (S \\ S') /\
        FromList xs \subset FromList vn :|: (S \\ S')) /\
    (forall efns S vn fnames tgm S' fdefs,
        anf_cvt_rel_efnlst S efns vn fnames tgm S' fdefs ->
        Disjoint _ (FromList vn) S ->
        occurs_free_fundefs fdefs \subset FromList vn :|: (S \\ S')) /\
    (forall bs S vn r tgm S' pats,
        anf_cvt_rel_branches S bs vn r tgm S' pats ->
        Disjoint _ (FromList vn) S ->
        forall c e, List.In (c, e) pats ->
          occurs_free e \subset [set r] :|: FromList vn :|: (S \\ S')).
  Proof.
    (* Helper: if x ∈ S and S' ⊆ S \ {x}, then x ∈ S \ S' *)
    assert (Hfresh_consumed : forall (x : var) (S S' : Ensemble var),
      x \in S -> S' \subset S \\ [set x] -> x \in S \\ S').
    { intros x0 S0 S0' Hin Hsub. constructor; [ exact Hin | ].
      intros Hc. apply Hsub in Hc. inv Hc. eauto. }
    (* Helper: extend disjointness to x::vn when x is consumed *)
    assert (Hdis_ext : forall (x : var) (vn0 : list var) (S S' : Ensemble var),
      Disjoint _ (FromList vn0) S ->
      S' \subset S ->
      ~ x \in S' ->
      Disjoint _ (FromList (x :: vn0)) S').
    { intros x0 vn0' S0 S0' Hdis0 Hsub0 Hni.
      rewrite FromList_cons. eapply Union_Disjoint_l.
      - eapply Disjoint_Singleton_l. exact Hni.
      - eapply Disjoint_Included_r; [ exact Hsub0 | exact Hdis0 ]. }
    (* Helper: IH target monotonicity *)
    assert (Hmono_sub : forall (vn0 : list var) (S1 S2 S1' S2' : Ensemble var),
      S1 \subset S2 -> S2' \subset S1' ->
      FromList vn0 :|: (S1 \\ S1') \subset FromList vn0 :|: (S2 \\ S2')).
    { intros vn0' S10 S20 S10' S20' Hsub1 Hsub2.
      eapply Union_Included; [ now sets | ].
      intros z Hz. inv Hz. right. constructor.
      - eapply Hsub1. exact H.
      - intros Hc. apply H0. eapply Hsub2. exact Hc. }
    eapply exp_ind_alt_2.
    - (* Var_e *)
      intros n S vn tgm S' C x Hcvt Hdis.
      inv Hcvt. rewrite occurs_free_Hole_c. now sets.
    - (* Lam_e *)
      intros na e1 IH S vn tgm S' C x Hcvt Hdis.
      inv Hcvt. fold anf_cvt_rel in *.
      (* Capture hypotheses introduced by inv *)
      match goal with
      | [ Hx1S : x1 \in S,
          HxS : x \in S \\ [set x1],
          Hbody : anf_cvt_rel _ e1 _ _ _ _ _ |- _ ] =>
        assert (Hx1_in_S := Hx1S);
        assert (Hsub_body : S' \subset S \\ [set x1] \\ [set x])
          by (eapply anf_cvt_exp_subset; exact Hbody);
        assert (Hdis' : Disjoint _ (FromList (x1 :: vn)) (S \\ [set x1] \\ [set x]))
          by (eapply Hdis_ext; [ exact Hdis |
              eapply Included_trans; eapply Setminus_Included |
              intros Hc; inv Hc; inv H; eauto ]);
        assert (Hih : occurs_free_ctx C1 \subset
                      FromList (x1 :: vn) :|: ((S \\ [set x1] \\ [set x]) \\ S'))
          by (eapply IH; eassumption)
      end.
      rewrite occurs_free_Efun1_c, occurs_free_Hole_c.
      eapply Union_Included; [ | now sets ].
      rewrite occurs_free_fundefs_Fcons, occurs_free_fundefs_Fnil.
      eapply Union_Included; [ | now sets ].
      eapply Included_trans; [ eapply Setminus_Included | ].
      eapply Included_trans; [ eapply occurs_free_ctx_app | ].
      assert (Htarget : FromList (x1 :: vn) :|: ((S \\ [set x1] \\ [set x]) \\ S')
                        \subset FromList vn :|: (S \\ S')).
      { rewrite FromList_cons. eapply Union_Included.
        - eapply Union_Included; [ | now sets ].
          intros z Hz. inv Hz. right. eapply Hfresh_consumed.
          + exact Hx1_in_S.
          + eapply Included_trans; [ exact Hsub_body | now sets ].
        - intros z Hz. inv Hz. right. constructor.
          + repeat match goal with
            | [ Hyp : _ \in _ \\ _ |- _ ] => inv Hyp
            end. assumption.
          + assumption. }
      eapply Union_Included.
      + eapply Included_trans; [ exact Hih | exact Htarget ].
      + eapply Included_trans; [ eapply Setminus_Included | ].
        rewrite occurs_free_Ehalt. intros z Hz. inv Hz.
        match goal with
        | [ Hbody : anf_cvt_rel _ e1 _ _ _ _ _ |- _ ] =>
          destruct (anf_cvt_result_in_consumed _ _ _ _ _ _ _ Hbody) as [Hv | Hs]
        end.
        * eapply Htarget. left. exact Hv.
        * eapply Htarget. right. constructor; [ exact Hs | ].
          eapply anf_cvt_result_not_in_output; eassumption.
    - (* App_e *)
      intros e1 IH1 e2 IH2 S vn tgm S' C x Hcvt Hdis.
      inv Hcvt. fold anf_cvt_rel in *.
      match goal with
      | [ He1 : anf_cvt_rel S e1 _ _ ?S2 ?C1 ?x1,
          He2 : anf_cvt_rel ?S2 e2 _ _ ?S3 ?C2 ?x2 |- _ ] =>
        assert (Hcvt_e1 := He1); assert (Hcvt_e2 := He2);
        assert (Hsub1 : S2 \subset S) by (eapply anf_cvt_exp_subset; exact He1);
        assert (Hsub2 : S3 \subset S2) by (eapply anf_cvt_exp_subset; exact He2);
        assert (Hdis2 : Disjoint _ (FromList vn) S2)
          by (eapply Disjoint_Included_r; [ exact Hsub1 | exact Hdis ]);
        assert (Hih1 : occurs_free_ctx C1 \subset FromList vn :|: (S \\ S2))
          by (eapply IH1; eassumption);
        assert (Hih2 : occurs_free_ctx C2 \subset FromList vn :|: (S2 \\ S3))
          by (eapply IH2; eassumption)
      end.
      eapply Included_trans; [ eapply occurs_free_ctx_comp | ].
      eapply Union_Included.
      + eapply Included_trans; [ exact Hih1 | ].
        eapply Hmono_sub; [ now sets | ].
        intros z Hz. inv Hz. eapply Hsub2 in H. now sets.
      + eapply Included_trans; [ eapply Setminus_Included | ].
        eapply Included_trans; [ eapply occurs_free_ctx_comp | ].
        eapply Union_Included.
        * eapply Included_trans; [ exact Hih2 | ].
          eapply Hmono_sub; [ exact Hsub1 | ].
          intros z Hz. inv Hz. eauto.
        * eapply Included_trans; [ eapply Setminus_Included | ].
          rewrite occurs_free_Eletapp_c, occurs_free_Hole_c.
          eapply Union_Included; [ | now sets ].
          eapply Union_Included.
          -- (* x1: result of e1 *)
             intros z Hz; inv Hz.
             destruct (anf_cvt_result_in_consumed _ _ _ _ _ _ _ Hcvt_e1) as [Hv | Hs];
             [ now left | right; constructor;
               [ exact Hs | intros Hc; inv Hc;
                 eapply (anf_cvt_result_not_in_output _ _ _ _ _ _ _ Hcvt_e1 Hdis);
                 eapply Hsub2; match goal with [ H : _ \in _ |- _ ] => exact H end ] ].
          -- (* x2: result of e2 *)
             rewrite FromList_cons, FromList_nil.
             intros z Hz. inv Hz.
             ++ inv H.
                destruct (anf_cvt_result_in_consumed _ _ _ _ _ _ _ Hcvt_e2) as [Hv | Hs];
                [ now left | right; constructor;
                  [ eapply Hsub1; exact Hs | intros Hc; inv Hc;
                    eapply (anf_cvt_result_not_in_output _ _ _ _ _ _ _ Hcvt_e2 Hdis2);
                    match goal with [ Hyp : _ \in _ |- _ ] => exact Hyp end ] ].
             ++ inv H.
    - (* Con_e *)
      intros dc es IH S vn tgm S' C x Hcvt Hdis.
      inv Hcvt. fold anf_cvt_rel_exps in *.
      match goal with
      | [ Hexps : anf_cvt_rel_exps _ es _ _ _ _ _ |- _ ] =>
        assert (Hdis' : Disjoint _ (FromList vn) (S \\ [set x]))
          by (eapply Disjoint_Included_r; [ eapply Setminus_Included | exact Hdis ]);
        destruct (IH _ _ _ _ _ _ Hexps Hdis') as [Hih_ctx Hih_xs]
      end.
      eapply Included_trans; [ eapply occurs_free_ctx_comp | ].
      eapply Union_Included.
      + eapply Included_trans; [ exact Hih_ctx | ].
        eapply Hmono_sub; [ eapply Setminus_Included | now sets ].
      + eapply Included_trans; [ eapply Setminus_Included | ].
        rewrite occurs_free_Econstr_c, occurs_free_Hole_c.
        eapply Union_Included; [ | now sets ].
        eapply Included_trans; [ exact Hih_xs | ].
        eapply Hmono_sub; [ eapply Setminus_Included | now sets ].
    - (* Match_e *)
      intros e1 IH1 pars bs IH2 S vn tgm S' C x Hcvt Hdis.
      inv Hcvt. fold anf_cvt_rel in *. fold anf_cvt_rel_branches in *.
      match goal with
      | [ Hf : f \in S,
          Hy : y \in S \\ [set f],
          He1 : anf_cvt_rel (S \\ [set f] \\ [set y]) e1 _ _ ?S2 _ _,
          Hbs : anf_cvt_rel_branches ?S2 bs _ _ _ ?S3 _ |- _ ] =>
        assert (Hcvt_e1 := He1); assert (Hcvt_bs := Hbs);
        assert (Hf_in_S := Hf); assert (Hy_in_S := Hy);
        assert (Hsub_e : S2 \subset S \\ [set f] \\ [set y])
          by (eapply anf_cvt_exp_subset; exact He1);
        assert (Hsub_bs : S3 \subset S2)
          by (eapply (proj2 (proj2 (proj2 anf_cvt_rel_subset))); exact Hbs);
        assert (Hdis_e : Disjoint _ (FromList vn) (S \\ [set f] \\ [set y]))
          by (eapply Disjoint_Included_r; [ eapply Included_trans; eapply Setminus_Included | exact Hdis ]);
        assert (Hdis_bs : Disjoint _ (FromList vn) S2)
          by (eapply Disjoint_Included_r; [ exact Hsub_e |
              eapply Disjoint_Included_r; [ eapply Included_trans; eapply Setminus_Included | exact Hdis ] ]);
        assert (Hih1 : occurs_free_ctx _ \subset
                  FromList vn :|: ((S \\ [set f] \\ [set y]) \\ S2))
          by (eapply IH1; eassumption)
      end.
      (* Helper: z \in S' → z \in S \\ [set f] \\ [set y] → contradiction for z ∈ {y,f} *)
      assert (Hy_in_S_raw : y \in S) by (destruct Hy_in_S; assumption).
      assert (Hfy_contra : forall z, z \in S \\ [set f] \\ [set y] -> z = y \/ z = f -> False).
      { intros z0 Hz0 [Heq | Heq]; subst; destruct Hz0 as [[_ Hn1] Hn2];
        [ apply Hn2; constructor | apply Hn1; constructor ]. }
      assert (Hfy_contra' : forall z, z \in (S3 \\ [set x]) -> z = y \/ z = f -> False).
      { intros z0 Hz0 Hor. eapply Hfy_contra; [ | exact Hor ].
        destruct Hz0 as [Hz0 _]. eapply Hsub_e. eapply Hsub_bs. exact Hz0. }
      rewrite occurs_free_Efun1_c.
      eapply Union_Included.
      + (* fundefs part: Fcons f func_tag [y] (Ecase y pats) Fnil *)
        rewrite occurs_free_fundefs_Fcons, occurs_free_fundefs_Fnil.
        eapply Union_Included; [ | now sets ].
        eapply Included_trans; [ eapply Setminus_Included | ].
        (* Need: occurs_free (Ecase y pats) ⊆ target *)
        assert (Hy_in_target : y \in FromList vn :|: (S \\ (S3 \\ [set x]))).
        { right. constructor.
          - exact Hy_in_S_raw.
          - intros Hc. destruct Hc as [Hc _].
            apply Hsub_bs in Hc. apply Hsub_e in Hc.
            destruct Hc as [_ Hc]. apply Hc. constructor. }
        eapply occurs_free_Ecase_all_branches.
        * exact Hy_in_target.
        * intros c0 e0 Hin.
          eapply Included_trans;
            [ eapply (IH2 _ _ _ _ _ _ Hcvt_bs Hdis_bs c0 e0 Hin) | ].
          eapply Union_Included.
          -- eapply Union_Included.
             ++ intros z Hz. inv Hz. exact Hy_in_target.
             ++ now sets.
          -- intros z Hz. destruct Hz as [Hz_pos Hz_neg].
             right. constructor.
             ++ eapply Hsub_e in Hz_pos.
                destruct Hz_pos as [Hz_pos _]. destruct Hz_pos as [Hz_pos _]. exact Hz_pos.
             ++ intros Hc. apply Hz_neg. destruct Hc as [Hc _]. exact Hc.
      + (* comp_ctx_f C1 (Eletapp_c x f func_tag [x1] Hole_c) part, minus {f} *)
        eapply Included_trans; [ eapply Setminus_Included | ].
        eapply Included_trans; [ eapply occurs_free_ctx_comp | ].
        eapply Union_Included.
        * eapply Included_trans; [ exact Hih1 | ].
          eapply Hmono_sub.
          -- eapply Included_trans; eapply Setminus_Included.
          -- intros z0 Hz0. destruct Hz0 as [Hz0 _]. eapply Hsub_bs. exact Hz0.
        * eapply Included_trans; [ eapply Setminus_Included | ].
          rewrite occurs_free_Eletapp_c, occurs_free_Hole_c.
          eapply Union_Included; [ | now sets ].
          eapply Union_Included.
          -- (* {f}: the function name *)
             intros z Hz. inv Hz. right. constructor.
             ++ exact Hf_in_S.
             ++ intros Hc. eapply Hfy_contra'; eauto.
          -- (* {x1}: result of e1 conversion *)
             rewrite FromList_cons, FromList_nil.
             intros z Hz. inv Hz.
             ++ inv H.
                destruct (anf_cvt_result_in_consumed _ _ _ _ _ _ _ Hcvt_e1) as [Hv | Hs].
                ** now left.
                ** right. constructor.
                   --- destruct Hs as [Hs _]. destruct Hs as [Hs _]. exact Hs.
                   --- intros Hc. destruct Hc as [Hc _].
                       eapply (anf_cvt_result_not_in_output _ _ _ _ _ _ _ Hcvt_e1 Hdis_e).
                       eapply Hsub_bs. exact Hc.
             ++ inv H.
    - (* Let_e *)
      intros na e1 IH1 e2 IH2 S vn tgm S' C x Hcvt Hdis.
      inv Hcvt. fold anf_cvt_rel in *.
      match goal with
      | [ H1 : anf_cvt_rel S e1 _ _ ?S2 ?C1 ?x1,
          H2 : anf_cvt_rel ?S2 e2 _ _ _ ?C2 _ |- _ ] =>
        assert (Hcvt_e1 := H1);
        assert (Hsub1 : S2 \subset S) by (eapply anf_cvt_exp_subset; exact H1);
        assert (Hnih : ~ x1 \in S2)
          by (eapply anf_cvt_result_not_in_output; eassumption);
        assert (Hdis2 : Disjoint _ (FromList (x1 :: vn)) S2)
          by (eapply Hdis_ext; [ exact Hdis | exact Hsub1 | exact Hnih ]);
        assert (Hih1 : occurs_free_ctx C1 \subset FromList vn :|: (S \\ S2))
          by (eapply IH1; eassumption);
        assert (Hih2 : occurs_free_ctx C2 \subset FromList (x1 :: vn) :|: (S2 \\ S'))
          by (eapply IH2; eassumption)
      end.
      eapply Included_trans; [ eapply occurs_free_ctx_comp | ].
      eapply Union_Included.
      + eapply Included_trans; [ exact Hih1 | ].
        eapply Hmono_sub; [ now sets | ].
        eapply anf_cvt_exp_subset. eassumption.
      + eapply Included_trans; [ eapply Setminus_Included | ].
        eapply Included_trans; [ exact Hih2 | ].
        rewrite FromList_cons.
        eapply Union_Included.
        * eapply Union_Included; [ | now sets ].
          intros z Hz. inv Hz.
          destruct (anf_cvt_result_in_consumed _ _ _ _ _ _ _ Hcvt_e1) as [Hv | Hs].
          -- now left.
          -- right. constructor.
             ++ exact Hs.
             ++ intros Hc. eapply Hnih.
                assert (Htmp : S' \subset S2) by (eapply anf_cvt_exp_subset; eassumption).
                apply Htmp. exact Hc.
        * intros z Hz. inv Hz. right. constructor.
          -- eapply Hsub1. exact H.
          -- exact H0.
    - (* Fix_e *)
      intros efns IHefns n S vn tgm S' C x Hcvt Hdis.
      inv Hcvt. fold anf_cvt_rel_efnlst in *.
      rewrite occurs_free_Efun1_c, occurs_free_Hole_c.
      eapply Union_Included; [ | now sets ].
      match goal with
      | [ Hefn : anf_cvt_rel_efnlst _ efns _ ?fn _ _ ?fd |- _ ] =>
        assert (Hcvt_efn := Hefn);
        assert (Hfnames_sub : FromList fn \subset S) by eassumption;
        assert (Hsub_efn : S' \subset S \\ FromList fn)
          by (eapply (proj1 (proj2 (proj2 anf_cvt_rel_subset))); exact Hefn);
        assert (Hdis_efn : Disjoint _ (FromList (List.rev fn ++ vn)) (S \\ FromList fn))
          by (rewrite FromList_app, FromList_rev;
              eapply Union_Disjoint_l;
              [ now sets
              | eapply Disjoint_Included_r; [ eapply Setminus_Included | exact Hdis ] ]);
        assert (Hih : occurs_free_fundefs fd \subset
                      FromList (List.rev fn ++ vn) :|: ((S \\ FromList fn) \\ S'))
          by (eapply IHefns; eassumption)
      end.
      eapply Included_trans; [ exact Hih | ].
      rewrite FromList_app, FromList_rev.
      eapply Union_Included.
      + eapply Union_Included; [ | now sets ].
        intros z Hz. right. constructor.
        * eapply Hfnames_sub. exact Hz.
        * intros Hc. apply Hsub_efn in Hc. destruct Hc as [_ Hc]. apply Hc. exact Hz.
      + intros z Hz. destruct Hz as [Hz_pos Hz_neg]. right. constructor.
        * destruct Hz_pos as [Hz_pos _]. exact Hz_pos.
        * exact Hz_neg.
    - (* Prf_e *)
      intros S vn tgm S' C x Hcvt Hdis.
      inv Hcvt. rewrite occurs_free_Econstr_c, occurs_free_Hole_c, FromList_nil. now sets.
    - (* Prim_val_e *)
      intros p S vn tgm S' C x Hcvt Hdis.
      inv Hcvt. rewrite occurs_free_Eprim_val_c, occurs_free_Hole_c. now sets.
    - (* Prim_e *) intros p S vn tgm S' C x Hcvt. inv Hcvt.
    - (* enil *)
      intros S vn tgm S' C xs Hcvt Hdis.
      inv Hcvt. split; rewrite ?occurs_free_Hole_c, ?FromList_nil; now sets.
    - (* econs *)
      intros e IHe es IHes S vn tgm S' C xs Hcvt Hdis.
      inv Hcvt. fold anf_cvt_rel in *. fold anf_cvt_rel_exps in *.
      match goal with
      | [ H1 : anf_cvt_rel S e _ _ ?S2 ?C1 ?x1,
          H2 : anf_cvt_rel_exps ?S2 es _ _ _ ?C2 ?xs' |- _ ] =>
        assert (Hsub1 : S2 \subset S) by (eapply anf_cvt_exp_subset; exact H1);
        assert (Hdis2 : Disjoint _ (FromList vn) S2)
          by (eapply Disjoint_Included_r; [ exact Hsub1 | exact Hdis ]);
        assert (Hih1 : occurs_free_ctx C1 \subset FromList vn :|: (S \\ S2))
          by (eapply IHe; eassumption);
        destruct (IHes _ _ _ _ _ _ H2 Hdis2) as [Hih2_ctx Hih2_xs]
      end.
      split.
      + (* occurs_free_ctx (comp_ctx_f C1 C2) ⊆ target *)
        eapply Included_trans; [ eapply occurs_free_ctx_comp | ].
        eapply Union_Included.
        * eapply Included_trans; [ exact Hih1 | ].
          eapply Hmono_sub; [ now sets | eapply (proj1 (proj2 anf_cvt_rel_subset)); eassumption ].
        * eapply Included_trans; [ eapply Setminus_Included | ].
          eapply Included_trans; [ exact Hih2_ctx | ].
          eapply Hmono_sub; [ exact Hsub1 | now sets ].
      + (* FromList (x1 :: xs') ⊆ target *)
        rewrite FromList_cons. eapply Union_Included.
        * match goal with
          | [ H1 : anf_cvt_rel S e _ _ ?S2 _ ?x1 |- _ ] =>
            intros z Hz; inv Hz;
            destruct (anf_cvt_result_in_consumed _ _ _ _ _ _ _ H1) as [Hv | Hs];
            [ now left |
              right; constructor; [ exact Hs |
                intros Hc;
                eapply (anf_cvt_result_not_in_output _ _ _ _ _ _ _ H1 Hdis);
                eapply (proj1 (proj2 anf_cvt_rel_subset)); eassumption ] ]
          end.
        * eapply Included_trans; [ exact Hih2_xs | ].
          eapply Hmono_sub; [ exact Hsub1 | now sets ].
    - (* eflnil *)
      intros S vn fnames tgm S' fdefs Hcvt Hdis.
      inv Hcvt. rewrite occurs_free_fundefs_Fnil. now sets.
    - (* eflcons *)
      split.
      + (* isLambda case *)
        intros na' e' Hlam IHe' efns IHefns S vn fnames tgm S' fdefs Hcvt Hdis.
        inv Hcvt. fold anf_cvt_rel in *. fold anf_cvt_rel_efnlst in *.
        repeat match goal with
        | [ H : Lam_e _ _ = Lam_e _ _ |- _ ] => inv H
        end.
        match goal with
        | [ Hx1_raw : ?x1_v \in S,
            Hbody : anf_cvt_rel (S \\ [set ?x1_v]) e' _ _ ?S2 ?C1 ?r1,
            Hrest : anf_cvt_rel_efnlst ?S2 efns _ _ _ ?S3 ?fdefs' |- _ ] =>
          assert (Hcvt_body := Hbody);
          assert (Hx1_in_S := Hx1_raw);
          assert (Hsub_body : S2 \subset S \\ [set x1_v])
            by (eapply anf_cvt_exp_subset; exact Hbody);
          assert (Hsub_rest : S3 \subset S2)
            by (eapply (proj1 (proj2 (proj2 anf_cvt_rel_subset))); exact Hrest);
          assert (Hdis_body : Disjoint _ (FromList (x1_v :: vn)) (S \\ [set x1_v]))
            by (eapply Hdis_ext; [ exact Hdis | eapply Setminus_Included |
                intros Hc; inv Hc; eauto ]);
          assert (Hdis_rest : Disjoint _ (FromList vn) S2)
            by (eapply Disjoint_Included_r; [ eapply Included_trans; [ exact Hsub_body | eapply Setminus_Included ] | exact Hdis ]);
          assert (Hih_body : occurs_free_ctx C1 \subset
                    FromList (x1_v :: vn) :|: ((S \\ [set x1_v]) \\ S2))
            by (eapply IHe'; eassumption);
          assert (Hih_rest : occurs_free_fundefs fdefs' \subset
                    FromList vn :|: (S2 \\ S3))
            by (eapply IHefns; eassumption)
        end.
        rewrite occurs_free_fundefs_Fcons.
        eapply Union_Included.
        * (* occurs_free body \ (f_name ∪ {x1} ∪ name_in_fundefs fdefs') *)
          eapply Included_trans; [ eapply Setminus_Included | ].
          eapply Included_trans; [ eapply occurs_free_ctx_app | ].
          eapply Union_Included.
          -- eapply Included_trans; [ exact Hih_body | ].
             rewrite FromList_cons.
             eapply Union_Included.
             ++ eapply Union_Included; [ | now sets ].
                intros z Hz. inv Hz. right. constructor.
                ** exact Hx1_in_S.
                ** intros Hc. apply Hsub_rest in Hc. apply Hsub_body in Hc. inv Hc. eauto.
             ++ intros z Hz. destruct Hz as [[Hz_in_S _] Hz_not_S2].
                right. constructor.
                ** exact Hz_in_S.
                ** intros Hc. apply Hz_not_S2. apply Hsub_rest. exact Hc.
          -- eapply Included_trans; [ eapply Setminus_Included | ].
             rewrite occurs_free_Ehalt. intros z Hz. inv Hz.
             destruct (anf_cvt_result_in_consumed _ _ _ _ _ _ _ Hcvt_body) as [Hv | Hs].
             ++ rewrite FromList_cons in Hv. inv Hv.
                ** inv H. right. constructor.
                   --- exact Hx1_in_S.
                   --- intros Hc. apply Hsub_rest in Hc. apply Hsub_body in Hc. inv Hc. eauto.
                ** now left.
             ++ right. constructor.
                ** destruct Hs as [Hs_in_S _]. exact Hs_in_S.
                ** intros Hc. apply Hsub_rest in Hc.
                   eapply (anf_cvt_result_not_in_output _ _ _ _ _ _ _ Hcvt_body Hdis_body).
                   exact Hc.
        * (* occurs_free_fundefs fdefs' \ {f_name} *)
          eapply Included_trans; [ eapply Setminus_Included | ].
          eapply Included_trans; [ exact Hih_rest | ].
          eapply Hmono_sub.
          -- eapply Included_trans; [ exact Hsub_body | eapply Setminus_Included ].
          -- now sets.
      + (* not isLambda *)
        intros Hnot IHe efns IHefns S vn fnames tgm S' fdefs Hcvt Hdis.
        inv Hcvt. unfold isLambda in Hnot. contradiction.
    - (* brnil *)
      intros S vn r tgm S' pats Hcvt Hdis.
      inv Hcvt. intros c e Hin. inv Hin.
    - (* brcons *)
      intros dc p e IHe bs IHbs S vn r tgm S' pats Hcvt Hdis.
      inv Hcvt. fold anf_cvt_rel in *. fold anf_cvt_rel_branches in *.
      intros c0 e0 Hin. destruct Hin as [Heq | Hin_tail].
      + (* current branch: (tg, app_ctx_f ctx_p (C1|[Ehalt r1]|)) *)
        inv Heq.
        match goal with
        | [ Hbs_rest : anf_cvt_rel_branches S bs _ _ _ ?S2 _,
            Hvars_sub : FromList ?vars \subset ?S2,
            Hbody : anf_cvt_rel (?S2 \\ FromList ?vars) e _ _ _ ?C1 ?r1 |- _ ] =>
          assert (Hsub_bs : S2 \subset S)
            by (eapply (proj2 (proj2 (proj2 anf_cvt_rel_subset))); exact Hbs_rest);
          assert (Hvars_sub_saved := Hvars_sub);
          assert (Hcvt_body_saved := Hbody);
          assert (Hdis_body : Disjoint _ (FromList (vars ++ vn)) (S2 \\ FromList vars))
            by (rewrite FromList_app; eapply Union_Disjoint_l;
                [ now sets
                | eapply Disjoint_Included_r; [ eapply Included_trans;
                    [ eapply Setminus_Included | exact Hsub_bs ] | exact Hdis ] ]);
          assert (Hih : occurs_free_ctx C1 \subset
                    FromList (vars ++ vn) :|: ((S2 \\ FromList vars) \\ S'))
            by (eapply IHe; eassumption)
        end.
        eapply Included_trans; [ eapply occurs_free_ctx_app | ].
        eapply Union_Included.
        * eapply Included_trans.
          -- eapply ctx_bind_proj_occurs_free_ctx.
          -- now sets.
        * eapply Included_trans; [ eapply Setminus_Included | ].
          eapply Included_trans; [ eapply occurs_free_ctx_app | ].
          eapply Union_Included.
          -- eapply Included_trans; [ exact Hih | ].
             rewrite FromList_app.
             eapply Union_Included.
             ++ (* FromList vars :|: FromList vn ⊆ target *)
                eapply Union_Included.
                ** (* FromList vars ⊆ target — vars are in S2, consumed by body *)
                   intros z Hz. right. constructor.
                   --- eapply Hsub_bs; eapply Hvars_sub_saved; exact Hz.
                   --- intros Hc.
                       assert (Htmp := anf_cvt_exp_subset _ _ _ _ _ _ _ Hcvt_body_saved).
                       apply Htmp in Hc. destruct Hc as [_ Hc_not]. apply Hc_not. exact Hz.
                ** (* FromList vn ⊆ target *)
                   now left; right.
             ++ (* (S2 \\ FromList vars) \\ S' ⊆ target *)
                intros z Hz. destruct Hz as [[Hz_in_S2 _] Hz_not_S'].
                right. constructor.
                ** eapply Hsub_bs; exact Hz_in_S2.
                ** exact Hz_not_S'.
          -- eapply Included_trans; [ eapply Setminus_Included | ].
             rewrite occurs_free_Ehalt. intros z Hz. inv Hz.
             destruct (anf_cvt_result_in_consumed _ _ _ _ _ _ _ Hcvt_body_saved) as [Hv | Hs].
             ++ rewrite FromList_app in Hv. inv Hv.
                ** (* r1 ∈ FromList vars *)
                   match goal with [ Hrc : _ \in FromList vars |- _ ] =>
                     right; constructor;
                     [ eapply Hsub_bs; eapply Hvars_sub_saved; exact Hrc
                     | intros Hc;
                       assert (Htmp := anf_cvt_exp_subset _ _ _ _ _ _ _ Hcvt_body_saved);
                       apply Htmp in Hc; destruct Hc as [_ Hc_not]; apply Hc_not; exact Hrc ]
                   end.
                ** (* r1 ∈ FromList vn *)
                   match goal with [ Hrc : _ \in FromList vn |- _ ] =>
                     left; right; exact Hrc end.
             ++ right. constructor.
                ** destruct Hs as [Hs_in_S2 _]. eapply Hsub_bs; exact Hs_in_S2.
                ** intros Hc.
                   eapply (anf_cvt_result_not_in_output _ _ _ _ _ _ _ Hcvt_body_saved Hdis_body).
                   exact Hc.
      + (* tail: in cbs' *)
        match goal with
        | [ Hbs_rest : anf_cvt_rel_branches S bs _ _ _ ?S2 _,
            Hbody_cvt : anf_cvt_rel _ _ _ _ S' _ _ |- _ ] =>
          assert (Hdis_bs : Disjoint _ (FromList vn) S)
            by exact Hdis;
          assert (Hih_tail := IHbs _ _ _ _ _ _ Hbs_rest Hdis_bs c0 e0 Hin_tail);
          assert (Hsub_body_tail : S' \subset S2)
            by (eapply Included_trans;
                [ eapply anf_cvt_exp_subset; exact Hbody_cvt
                | eapply Setminus_Included ])
        end.
        eapply Included_trans; [ exact Hih_tail | ].
        eapply Union_Included; [ now sets | ].
        intros z Hz. right. destruct Hz as [Hz_in Hz_not].
        constructor.
        * exact Hz_in.
        * intros Hc. apply Hz_not. eapply Hsub_body_tail. exact Hc.
  Qed.

  Lemma anf_cvt_occurs_free_ctx_subset S e vn tgm S' C x :
    anf_cvt_rel S e vn tgm S' C x ->
    Disjoint _ (FromList vn) S ->
    occurs_free_ctx C \subset FromList vn :|: (S \\ S').
  Proof. eapply (proj1 anf_cvt_occurs_free_mutual). Qed.

  Lemma anf_cvt_occurs_free_ctx_subset_exps S es vn tgm S' C xs :
    anf_cvt_rel_exps S es vn tgm S' C xs ->
    Disjoint _ (FromList vn) S ->
    occurs_free_ctx C \subset FromList vn :|: (S \\ S').
  Proof.
    intros Hrel Hdis.
    exact (proj1 (proj1 (proj2 anf_cvt_occurs_free_mutual) es _ _ _ _ _ _ Hrel Hdis)).
  Qed.

  Local Lemma Union_destr {A} (B C : Ensemble A) (x : A) :
    Union A B C x -> B x \/ C x.
  Proof. inversion 1; subst; [left | right]; assumption. Qed.

  (* In the Let_e case, the free variables of C2|[e_k]| are disjoint
     from (S \ S2) \ {x1}. This follows from:
     - occurs_free(C2|[e_k]|) ⊆ occurs_free_ctx C2 ∪ occurs_free e_k
     - occurs_free_ctx C2 ⊆ FromList(x1::vnames), disjoint from S by Hdis
     - occurs_free e_k is disjoint from (S\S')\{x2} by Hdis_ek,
       and (S\S2)\{x1} ⊆ (S\S')\{x2} *)
  Lemma anf_cvt_disjoint_occurs_free_ctx S e1 vn tgm S2 C1 x1
        e2 S' C2 x2 e_k :
    anf_cvt_rel S e1 vn tgm S2 C1 x1 ->
    anf_cvt_rel S2 e2 (x1 :: vn) tgm S' C2 x2 ->
    Disjoint _ (FromList vn) S ->
    Disjoint _ (occurs_free e_k) ((S \\ S') \\ [set x2]) ->
    Disjoint _ (occurs_free (C2 |[ e_k ]|)) ((S \\ S2) \\ [set x1]).
  Proof.
    intros Hcvt1 Hcvt2 Hdis_vn Hdis_ek.
    pose proof (anf_cvt_exp_subset _ _ _ _ _ _ _ Hcvt1) as HS2_S.
    pose proof (anf_cvt_exp_subset _ _ _ _ _ _ _ Hcvt2) as HS'_S2.
    pose proof (anf_cvt_result_not_in_output _ _ _ _ _ _ _ Hcvt1 Hdis_vn) as Hx1_not_S2.
    pose proof (anf_cvt_result_in_consumed _ _ _ _ _ _ _ Hcvt2) as Hx2_consumed.
    assert (Hdis_x1vn_S2 : Disjoint _ (FromList (x1 :: vn)) S2).
    { constructor. intros z Hz.
      assert (Hz_l : FromList (x1 :: vn) z) by (inversion Hz; assumption).
      assert (Hz_r : S2 z) by (inversion Hz; assumption).
      simpl in Hz_l. destruct Hz_l as [Heq | Hin].
      - subst. exact (Hx1_not_S2 Hz_r).
      - eapply Hdis_vn; constructor; [exact Hin | eapply HS2_S; exact Hz_r]. }
    pose proof (anf_cvt_occurs_free_ctx_subset _ _ _ _ _ _ _ Hcvt2 Hdis_x1vn_S2) as Hctx.
    constructor. intros z Hz.
    assert (Hz_of : occurs_free (C2 |[ e_k ]|) z) by (inversion Hz; assumption).
    assert (Hz_sm : ((S \\ S2) \\ [set x1]) z) by (inversion Hz; assumption).
    clear Hz.
    destruct Hz_sm as [[Hz_S Hz_not_S2] Hz_not_x1].
    apply (occurs_free_ctx_app C2 e_k) in Hz_of.
    apply Union_destr in Hz_of.
    destruct Hz_of as [Hz_ctx | Hz_ek_bs].
    - (* z ∈ occurs_free_ctx C2 *)
      apply Hctx in Hz_ctx.
      apply Union_destr in Hz_ctx.
      destruct Hz_ctx as [Hz_x1vn | Hz_S2S'].
      + simpl in Hz_x1vn. destruct Hz_x1vn as [Heq | Hin].
        * subst. exact (Hz_not_x1 (In_singleton _ _)).
        * eapply Hdis_vn; constructor; [exact Hin | exact Hz_S].
      + destruct Hz_S2S' as [Hz_S2 _]. exact (Hz_not_S2 Hz_S2).
    - (* z ∈ occurs_free e_k \ bound_stem_ctx C2 *)
      destruct Hz_ek_bs as [Hz_ek Hz_not_bsc].
      assert (Hz_not_x2 : z <> x2).
      { intro Heq. subst. destruct Hx2_consumed as [Hx2_vn | Hx2_S2].
        - simpl in Hx2_vn. destruct Hx2_vn as [Heq | Hin].
          + subst. exact (Hz_not_x1 (In_singleton _ _)).
          + eapply Hdis_vn; constructor; [exact Hin | exact Hz_S].
        - exact (Hz_not_S2 Hx2_S2). }
      eapply Hdis_ek; constructor.
      + exact Hz_ek.
      + constructor.
        * constructor; [exact Hz_S | intro; apply Hz_not_S2; eapply HS'_S2; assumption].
        * intro Hz_x2. destruct Hz_x2. exact (Hz_not_x2 eq_refl).
  Qed.

  (* In the Match_e case, occurs_free of Eletapp is disjoint from ((S\{f}\{y})\S2)\{x1} for IH1. *)
  Lemma anf_cvt_disjoint_eletapp_match S f y e1 vn tgm S2 C1 x1
        brs S3 pats x e_k :
    f \in S ->
    y \in S \\ [set f] ->
    anf_cvt_rel (S \\ [set f] \\ [set y]) e1 vn tgm S2 C1 x1 ->
    anf_cvt_rel_branches S2 brs vn y tgm S3 pats ->
    x \in S3 ->
    Disjoint _ (occurs_free e_k) ((S \\ (S3 \\ [set x])) \\ [set x]) ->
    Disjoint _ (occurs_free (Eletapp x f func_tag [x1] e_k))
               (((S \\ [set f] \\ [set y]) \\ S2) \\ [set x1]).
  Proof.
    intros Hf Hy Hcvt1 Hcvt_brs Hx Hdis_ek.
    pose proof (anf_cvt_exp_subset _ _ _ _ _ _ _ Hcvt1) as HS2_Sfy.
    pose proof (proj2 (proj2 (proj2 anf_cvt_rel_subset)) _ _ _ _ _ _ _ Hcvt_brs) as HS3_S2.
    constructor. intros z Hz.
    assert (Hz_of : occurs_free (Eletapp x f func_tag [x1] e_k) z) by (inversion Hz; assumption).
    assert (Hz_sm : (((S \\ [set f] \\ [set y]) \\ S2) \\ [set x1]) z) by (inversion Hz; assumption).
    clear Hz.
    destruct Hz_sm as [[[[Hz_S Hz_not_f] Hz_not_y] Hz_not_S2] Hz_not_x1].
    apply (proj1 (occurs_free_Eletapp _ _ _ _ _)) in Hz_of.
    apply Union_destr in Hz_of.
    destruct Hz_of as [Hz_left | Hz_right].
    - (* z ∈ f |: FromList [x1] *)
      apply Union_destr in Hz_left.
      destruct Hz_left as [Hz_f | Hz_x1].
      + (* z = f *) inv Hz_f. exact (Hz_not_f (In_singleton _ _)).
      + (* z ∈ FromList [x1] = {x1} *)
        simpl in Hz_x1. destruct Hz_x1 as [Heq | []]. subst.
        exact (Hz_not_x1 (In_singleton _ _)).
    - (* z ∈ occurs_free e_k \\ {x} *)
      destruct Hz_right as [Hz_ek Hz_not_x].
      eapply Hdis_ek; constructor.
      + exact Hz_ek.
      + constructor.
        * constructor; [exact Hz_S | ].
          intro Hz_S3x. destruct Hz_S3x as [Hz_S3 _].
          exact (Hz_not_S2 (HS3_S2 _ Hz_S3)).
        * exact Hz_not_x.
  Qed.

  (* In the eval_many_econs case, occurs_free e_k is disjoint from (S2\S')\FromList xs for IH_es. *)
  Lemma anf_cvt_disjoint_exps_continuation S e1 vn tgm S2 C1 x1
        es S' C2 xs e_k :
    anf_cvt_rel S e1 vn tgm S2 C1 x1 ->
    anf_cvt_rel_exps S2 es vn tgm S' C2 xs ->
    Disjoint _ (FromList vn) S ->
    Disjoint _ (occurs_free e_k) ((S \\ S') \\ FromList (x1 :: xs)) ->
    Disjoint _ (occurs_free e_k) ((S2 \\ S') \\ FromList xs).
  Proof.
    intros Hcvt1 Hcvt_exps Hdis_vn Hdis_ek.
    pose proof (anf_cvt_exp_subset _ _ _ _ _ _ _ Hcvt1) as HS2_S.
    pose proof (anf_cvt_result_not_in_output _ _ _ _ _ _ _ Hcvt1 Hdis_vn) as Hx1_not_S2.
    eapply Disjoint_Included_r; [ | exact Hdis_ek ].
    intros z [Hz_S2S' Hz_not_xs].
    destruct Hz_S2S' as [Hz_S2 Hz_not_S'].
    constructor.
    - constructor; [eapply HS2_S; exact Hz_S2 | exact Hz_not_S'].
    - intro Hz_x1xs. simpl in Hz_x1xs. destruct Hz_x1xs as [Heq | Hin].
      + subst. exact (Hx1_not_S2 Hz_S2).
      + exact (Hz_not_xs Hin).
  Qed.

  (* In the eval_many_econs case, occurs_free of C2|[e_k]| is disjoint from (S\S2)\{x1} for IH_e. *)
  Lemma anf_cvt_disjoint_occurs_free_ctx_exps S e1 vn tgm S2 C1 x1
        es S' C2 xs e_k :
    anf_cvt_rel S e1 vn tgm S2 C1 x1 ->
    anf_cvt_rel_exps S2 es vn tgm S' C2 xs ->
    Disjoint _ (FromList vn) S ->
    Disjoint _ (occurs_free e_k) ((S \\ S') \\ FromList (x1 :: xs)) ->
    Disjoint _ (occurs_free (C2 |[ e_k ]|)) ((S \\ S2) \\ [set x1]).
  Proof.
    intros Hcvt1 Hcvt_exps Hdis_vn Hdis_ek.
    pose proof (anf_cvt_exp_subset _ _ _ _ _ _ _ Hcvt1) as HS2_S.
    pose proof (proj1 (proj2 anf_cvt_rel_subset) _ _ _ _ _ _ _ Hcvt_exps) as HS'_S2.
    pose proof (anf_cvt_result_not_in_output _ _ _ _ _ _ _ Hcvt1 Hdis_vn) as Hx1_not_S2.
    assert (Hdis_vn_S2 : Disjoint _ (FromList vn) S2).
    { eapply Disjoint_Included_r; [ exact HS2_S | exact Hdis_vn ]. }
    pose proof (anf_cvt_occurs_free_ctx_subset_exps _ _ _ _ _ _ _ Hcvt_exps Hdis_vn_S2) as Hctx.
    constructor. intros z Hz.
    assert (Hz_of : occurs_free (C2 |[ e_k ]|) z) by (inversion Hz; assumption).
    assert (Hz_sm : ((S \\ S2) \\ [set x1]) z) by (inversion Hz; assumption).
    clear Hz.
    destruct Hz_sm as [[Hz_S Hz_not_S2] Hz_not_x1].
    apply (occurs_free_ctx_app C2 e_k) in Hz_of.
    apply Union_destr in Hz_of.
    destruct Hz_of as [Hz_ctx | Hz_ek_bs].
    - (* z ∈ occurs_free_ctx C2 *)
      apply Hctx in Hz_ctx.
      apply Union_destr in Hz_ctx.
      destruct Hz_ctx as [Hz_vn | Hz_S2S'].
      + eapply Hdis_vn; constructor; [exact Hz_vn | exact Hz_S].
      + destruct Hz_S2S' as [Hz_S2 _]. exact (Hz_not_S2 Hz_S2).
    - (* z ∈ occurs_free e_k \ bound_stem_ctx C2 *)
      destruct Hz_ek_bs as [Hz_ek Hz_not_bsc].
      assert (Hz_not_S' : ~ z \in S') by (intro; apply Hz_not_S2; eapply HS'_S2; assumption).
      assert (Hz_not_x1xs : ~ FromList (x1 :: xs) z).
      { intro Hz_bad. simpl in Hz_bad. destruct Hz_bad as [Heq | Hin].
        - subst. apply Hz_not_x1. constructor.
        - destruct (anf_cvt_rel_exps_results_in_consumed _ _ _ _ _ _ _ Hcvt_exps _ Hin) as [Hxvn | HxS2].
          + eapply Hdis_vn; constructor; [exact Hxvn | exact Hz_S].
          + exact (Hz_not_S2 HxS2). }
      exfalso. eapply Hdis_ek; constructor;
        [ exact Hz_ek
        | constructor; [constructor; [exact Hz_S | exact Hz_not_S'] | exact Hz_not_x1xs] ].
  Qed.

  (* In the App_e case, occurs_free of C2|[Eletapp ...]| is disjoint from (S\S2)\{x1} for IH1. *)
  Lemma anf_cvt_disjoint_occurs_free_ctx_app S e1 vn tgm S2 C1 x1
        e2 S3 C2 x2 r e_k :
    anf_cvt_rel S e1 vn tgm S2 C1 x1 ->
    anf_cvt_rel S2 e2 vn tgm S3 C2 x2 ->
    r \in S3 ->
    Disjoint _ (FromList vn) S ->
    Disjoint _ (occurs_free e_k) ((S \\ (S3 \\ [set r])) \\ [set r]) ->
    Disjoint _ (occurs_free (C2 |[ Eletapp r x1 func_tag [x2] e_k ]|))
               ((S \\ S2) \\ [set x1]).
  Proof.
    intros Hcvt1 Hcvt2 Hr_in Hdis_vn Hdis_ek.
    pose proof (anf_cvt_exp_subset _ _ _ _ _ _ _ Hcvt1) as HS2_S.
    pose proof (anf_cvt_exp_subset _ _ _ _ _ _ _ Hcvt2) as HS3_S2.
    pose proof (anf_cvt_result_not_in_output _ _ _ _ _ _ _ Hcvt1 Hdis_vn) as Hx1_not_S2.
    pose proof (anf_cvt_result_in_consumed _ _ _ _ _ _ _ Hcvt2) as Hx2_consumed.
    assert (Hdis_vn_S2 : Disjoint _ (FromList vn) S2).
    { eapply Disjoint_Included_r; [ exact HS2_S | exact Hdis_vn ]. }
    pose proof (anf_cvt_occurs_free_ctx_subset _ _ _ _ _ _ _ Hcvt2 Hdis_vn_S2) as Hctx.
    constructor. intros z Hz.
    assert (Hz_of : occurs_free (C2 |[ Eletapp r x1 func_tag [x2] e_k ]|) z)
      by (inversion Hz; assumption).
    assert (Hz_sm : ((S \\ S2) \\ [set x1]) z) by (inversion Hz; assumption).
    clear Hz.
    destruct Hz_sm as [[Hz_S Hz_not_S2] Hz_not_x1].
    apply (occurs_free_ctx_app C2 (Eletapp r x1 func_tag [x2] e_k)) in Hz_of.
    apply Union_destr in Hz_of.
    destruct Hz_of as [Hz_ctx | Hz_elet_bs].
    - (* z ∈ occurs_free_ctx C2 *)
      apply Hctx in Hz_ctx.
      apply Union_destr in Hz_ctx.
      destruct Hz_ctx as [Hz_vn | Hz_S2S3].
      + eapply Hdis_vn; constructor; [exact Hz_vn | exact Hz_S].
      + destruct Hz_S2S3 as [Hz_S2 _]. exact (Hz_not_S2 Hz_S2).
    - (* z ∈ occurs_free (Eletapp ...) \ bound_stem_ctx C2 *)
      destruct Hz_elet_bs as [Hz_elet Hz_not_bsc].
      apply (proj1 (occurs_free_Eletapp _ _ _ _ _)) in Hz_elet.
      apply Union_destr in Hz_elet.
      destruct Hz_elet as [Hz_left | Hz_right].
      + apply Union_destr in Hz_left.
        destruct Hz_left as [Hz_x1 | Hz_x2].
        * inv Hz_x1. exact (Hz_not_x1 (In_singleton _ _)).
        * simpl in Hz_x2. destruct Hz_x2 as [Heq | []]. subst.
          destruct Hx2_consumed as [Hx2_vn | Hx2_S2].
          -- eapply Hdis_vn; constructor; [exact Hx2_vn | exact Hz_S].
          -- exact (Hz_not_S2 Hx2_S2).
      + destruct Hz_right as [Hz_ek Hz_not_r].
        eapply Hdis_ek; constructor.
        * exact Hz_ek.
        * constructor.
          -- constructor; [exact Hz_S | ].
             intro Hz_S3r. destruct Hz_S3r as [Hz_S3 _].
             exact (Hz_not_S2 (HS3_S2 _ Hz_S3)).
          -- exact Hz_not_r.
  Qed.

  (* In the App_e case, occurs_free of the Eletapp continuation is disjoint from (S2\S3)\{x2}. *)
  Lemma anf_cvt_disjoint_eletapp S e1 vn tgm S2 C1 x1
        e2 S3 C2 x2 r e_k :
    anf_cvt_rel S e1 vn tgm S2 C1 x1 ->
    anf_cvt_rel S2 e2 vn tgm S3 C2 x2 ->
    r \in S3 ->
    Disjoint _ (FromList vn) S ->
    Disjoint _ (occurs_free e_k) ((S \\ (S3 \\ [set r])) \\ [set r]) ->
    Disjoint _ (occurs_free (Eletapp r x1 func_tag [x2] e_k))
               ((S2 \\ S3) \\ [set x2]).
  Proof.
    intros Hcvt1 Hcvt2 Hr_in Hdis_vn Hdis_ek.
    pose proof (anf_cvt_exp_subset _ _ _ _ _ _ _ Hcvt1) as HS2_S.
    pose proof (anf_cvt_exp_subset _ _ _ _ _ _ _ Hcvt2) as HS3_S2.
    pose proof (anf_cvt_result_in_consumed _ _ _ _ _ _ _ Hcvt1) as Hx1_consumed.
    pose proof (anf_cvt_result_not_in_output _ _ _ _ _ _ _ Hcvt1 Hdis_vn) as Hx1_not_S2.
    constructor. intros z Hz.
    assert (Hz_of : occurs_free (Eletapp r x1 func_tag [x2] e_k) z)
      by (inversion Hz; assumption).
    assert (Hz_sm : ((S2 \\ S3) \\ [set x2]) z) by (inversion Hz; assumption).
    clear Hz.
    destruct Hz_sm as [[Hz_S2 Hz_not_S3] Hz_not_x2].
    apply (proj1 (occurs_free_Eletapp _ _ _ _ _)) in Hz_of.
    apply Union_destr in Hz_of.
    destruct Hz_of as [Hz_left | Hz_right].
    - apply Union_destr in Hz_left.
      destruct Hz_left as [Hz_x1 | Hz_x2].
      + inv Hz_x1. exact (Hx1_not_S2 Hz_S2).
      + simpl in Hz_x2. destruct Hz_x2 as [Heq | []]. subst.
        exact (Hz_not_x2 (In_singleton _ _)).
    - destruct Hz_right as [Hz_ek Hz_not_r].
      eapply Hdis_ek; constructor.
      + exact Hz_ek.
      + constructor.
        * constructor; [eapply HS2_S; exact Hz_S2 | ].
          intro Hz_S3r. destruct Hz_S3r as [Hz_S3 _].
          exact (Hz_not_S3 Hz_S3).
        * exact Hz_not_r.
  Qed.

  (* Convert anf_cvt_rel_efnlst to anf_fix_rel.
     The key difference: anf_fix_rel carries explicit disjointness and subset witnesses
     at each step. These follow from the efnlst subset property. *)
  Lemma anf_cvt_rel_efnlst_to_fix_rel fnames_all names0 :
    forall efns S fnames S' fdefs,
      anf_cvt_rel_efnlst S efns (List.rev fnames_all ++ names0) fnames cnstrs S' fdefs ->
      Disjoint _ S (FromList fnames_all :|: FromList names0) ->
      anf_fix_rel fnames_all names0 S fnames efns fdefs S'.
  Proof.
    intros efns. induction efns; intros S fnames S' fdefs Hcvt Hdis.
    - inv Hcvt. constructor.
    - inv Hcvt. fold anf_cvt_rel in *. fold anf_cvt_rel_efnlst in *.
      econstructor.
      + exact Hdis.
      + eassumption. (* x1 ∈ S *)
      + apply Included_refl.
      + apply Included_refl.
      + eassumption. (* anf_cvt_rel *)
      + eapply IHefns; [ eassumption | ].
        eapply Disjoint_Included_l; [ | exact Hdis ].
        eapply Included_trans.
        * eapply anf_cvt_exp_subset. eassumption.
        * eapply Setminus_Included.
  Qed.

  (* Generalized consistency: two positions with the same key have R-related values. *)
  Definition list_consistent {A : Type} (R : A -> A -> Prop)
             (keys : list var) (vals : list A) : Prop :=
    forall i j x vi vj,
      nth_error keys i = Some x ->
      nth_error keys j = Some x ->
      nth_error vals i = Some vi ->
      nth_error vals j = Some vj ->
      R vi vj.

  (* Helper: result of non-Var ANF conversion is in S, hence not in FromList vn. *)
  Local Ltac anf_result_in_S :=
    match goal with
    | [ Hin : _ \in FromList ?vn,
        Hdis : Disjoint _ (FromList ?vn) ?S,
        Hmem : _ \in ?S |- _ ] =>
      exfalso; eapply Hdis; constructor; [ exact Hin | exact Hmem ]
    | [ Hin : _ \in FromList ?vn,
        Hdis : Disjoint _ (FromList ?vn) ?S,
        Hmem : _ \in ?S2,
        Hsub : ?S2 \subset ?S |- _ ] =>
      exfalso; eapply Hdis; constructor; [ exact Hin | eapply Hsub; exact Hmem ]
    | [ Hin : _ \in FromList ?vn,
        Hdis : Disjoint _ (FromList ?vn) ?S,
        Hmem : _ \in ?S3,
        Hsub2 : ?S3 \subset ?S2,
        Hsub1 : ?S2 \subset ?S |- _ ] =>
      exfalso; eapply Hdis; constructor;
      [ exact Hin | eapply Hsub1; eapply Hsub2; exact Hmem ]
    end.

  (** If the result variable of an ANF conversion equals vn[i],
      then the evaluation result equals rho[i].
      Proof by mutual induction on the evaluation derivation. *)
  Lemma anf_cvt_rel_var_lookup :
    forall rho e r f t,
      @eval_env_fuel _ LambdaBoxLocal_resource_fuel LambdaBoxLocal_resource_trace
                     rho e r f t ->
      forall v, r = Val v ->
      forall S vn tgm S' C x i,
        anf_cvt_rel S e vn tgm S' C x ->
        Disjoint _ (FromList vn) S ->
        env_consistent vn rho ->
        nth_error vn i = Some x ->
        nth_error rho i = Some v.
  Proof.
    pose (Plookup := fun (rho : fuel_sem.env) (e : expression.exp)
                          (r : result) (f : nat) (t : nat) =>
      forall v, r = Val v ->
      forall S vn tgm S' C x i,
        anf_cvt_rel S e vn tgm S' C x ->
        Disjoint _ (FromList vn) S ->
        env_consistent vn rho ->
        nth_error vn i = Some x ->
        nth_error rho i = Some v).
    intros rho e r f t Heval.
    eapply @eval_env_fuel_ind' with
      (Hf := LambdaBoxLocal_resource_fuel)
      (Ht := LambdaBoxLocal_resource_trace)
      (P := Plookup)
      (P0 := fun _ _ _ _ _ => True)
      (P1 := Plookup);
    unfold Plookup; clear Plookup.

    (** eval_env_step cases (P) *)

    - (* 1. eval_Con_step *)
      intros es vs0 rho0 dc fs ts Hmany _ v Hv S vn tgm S' C x i Hcvt Hdis Hcons Hnth.
      inv Hcvt. fold anf_cvt_rel_exps in *.
      assert (Hin : x \in FromList vn) by (eapply nth_error_In; eassumption).
      anf_result_in_S.

    - (* 2. eval_Con_step_OOT *)
      intros. congruence.

    - (* 3. eval_App_step *)
      intros e1 e2 e1' v2 r0 na rho0 rho' f1 f2 f3 t1 t2 t3
             Heval1 IH1 Heval2 IH2 Heval3 IH3
             v Hv S vn tgm S' C x i Hcvt Hdis Hcons Hnth.
      inv Hcvt. fold anf_cvt_rel in *.
      assert (Hin : x \in FromList vn) by (eapply nth_error_In; eassumption).
      assert (Hsub2 : S3 \subset S2)
        by (eapply anf_cvt_exp_subset; eassumption).
      assert (Hsub1 : S2 \subset S)
        by (eapply anf_cvt_exp_subset; eassumption).
      anf_result_in_S.

    - (* 4. eval_App_step_OOT1 *) intros. congruence.
    - (* 5. eval_App_step_OOT2 *) intros. congruence.

    - (* 6. eval_Let_step — the key case *)
      intros e1 e2 v1 r0 rho0 na f1 f2 t1 t2
             Heval1 IH1 Heval2 IH2
             v Hv S vn tgm S' C x i Hcvt Hdis Hcons Hnth.
      subst. inv Hcvt. fold anf_cvt_rel in *.
      (* We have:
         H8 : anf_cvt_rel S e1 vn tgm S2 C1 x1
         H9 : anf_cvt_rel S2 e2 (x1::vn) tgm S' C2 x
         Heval1 : eval_env_fuel rho0 e1 (Val v1) f1 t1
         Heval2 : eval_env_fuel (v1::rho0) e2 (Val v) f2 t2
         Hnth : nth_error vn i = Some x *)
      eapply IH2 with (i := Datatypes.S i).
      + reflexivity.
      + eassumption.
      + (* Disjoint (FromList (x1::vn)) S2 *)
        rewrite FromList_cons.
        eapply Union_Disjoint_l.
        * eapply Disjoint_Singleton_l.
          eapply anf_cvt_result_not_in_output; eassumption.
        * eapply Disjoint_Included_r.
          eapply anf_cvt_exp_subset. eassumption.
          eassumption.
      + (* env_consistent (x1::vn) (v1::rho0) *)
        eapply env_consistent_extend; [ exact Hcons | ].
        intros k Hk. eapply IH1; [ reflexivity | eassumption .. ].
      + (* nth_error (x1::vn) (S i) = Some x *)
        simpl. exact Hnth.

    - (* 7. eval_Let_step_OOT *) intros. congruence.

    - (* 8. eval_FixApp_step *)
      intros e1 e2 e' rho0 rho' rho'' n na fnlst v2 r0
             f1 f2 f3 t1 t2 t3
             Heval1 IH1 _ _ Heval2 IH2 Heval3 IH3
             v Hv S vn tgm S' C x i Hcvt Hdis Hcons Hnth.
      inv Hcvt. fold anf_cvt_rel in *.
      assert (Hin : x \in FromList vn) by (eapply nth_error_In; eassumption).
      assert (Hsub2 : S3 \subset S2)
        by (eapply anf_cvt_exp_subset; eassumption).
      assert (Hsub1 : S2 \subset S)
        by (eapply anf_cvt_exp_subset; eassumption).
      anf_result_in_S.

    - (* 9. eval_Match_step *)
      intros e1 e' rho0 dc vs0 n brnchs r0 f1 f2 t1 t2
             Heval1 IH1 _ Heval2 IH2
             v Hv S vn tgm S' C x i Hcvt Hdis Hcons Hnth.
      inv Hcvt. fold anf_cvt_rel in *. fold anf_cvt_rel_branches in *.
      assert (Hin : x \in FromList vn) by (eapply nth_error_In; eassumption).
      exfalso. eapply Hdis. constructor; [ exact Hin | ].
      (* x = r ∈ S3. Chain: S3 ⊆ S2 ⊆ S_body ⊆ S *)
      match goal with
      | [ Hbr : anf_cvt_rel_branches _ _ _ _ _ ?S3 _,
          He1 : anf_cvt_rel _ _ _ _ ?S2 _ _,
          Hr : _ \in ?S3 |- _ \in ?S ] =>
        eapply Setminus_Included; eapply Setminus_Included;
        eapply (anf_cvt_exp_subset _ _ _ _ _ _ _ He1);
        eapply (proj2 (proj2 (proj2 anf_cvt_rel_subset)) _ _ _ _ _ _ _ Hbr);
        exact Hr
      end.

    - (* 10. eval_Match_step_OOT *) intros. congruence.

    (** eval_fuel_many cases (P0 = True) *)
    - (* 11. eval_many_enil *) intros. exact I.
    - (* 12. eval_many_econs *) intros. exact I.

    (** eval_env_fuel cases (P1) *)

    - (* 13. eval_Var_fuel *)
      intros n rho0 v0 Hnth_rho v Hv S0 vn tgm S' C x i Hcvt Hdis Hcons Hnth_vn.
      inv Hv. inv Hcvt.
      unfold env_consistent in Hcons.
      match goal with
      | [ Hnth_src : nth_error ?vn (N.to_nat ?n) = Some ?x |- _ ] =>
        rewrite (Hcons i (N.to_nat n) x Hnth_vn Hnth_src)
      end.
      exact Hnth_rho.

    - (* 14. eval_Lam_fuel *)
      intros e0 rho0 na v Hv S0 vn tgm S' C x i Hcvt Hdis Hcons Hnth.
      inv Hv. inv Hcvt. fold anf_cvt_rel in *.
      assert (Hin : x \in FromList vn) by (eapply nth_error_In; eassumption).
      exfalso. eapply Hdis. constructor; [ exact Hin | ].
      eapply Setminus_Included.
      match goal with
      | [ H : _ \in _ |- _ \in _ ] => exact H
      end.

    - (* 15. eval_Fix_fuel *)
      intros n rho0 fnlst v Hv S0 vn tgm S' C x i Hcvt Hdis Hcons Hnth.
      inv Hv. inv Hcvt. fold anf_cvt_rel_efnlst in *.
      assert (Hin : x \in FromList vn) by (eapply nth_error_In; eassumption).
      exfalso. eapply Hdis. constructor; [ exact Hin | ].
      match goal with
      | [ H : FromList _ \subset _ |- _ \in _ ] =>
        eapply H; eapply nth_error_In; eassumption
      end.

    - (* 16. eval_OOT *) intros. congruence.
    - (* 17. eval_step *)
      intros rho0 e0 r0 f0 t0 Hstep IH. exact IH.
    - (* derivation *) exact Heval.
  Unshelve. all: exact 0%nat.
  Qed.

  Lemma env_consistent_extend_from_cvt vn vs S e tgm S' C x v f t :
    env_consistent vn vs ->
    anf_cvt_rel S e vn tgm S' C x ->
    Disjoint _ (FromList vn) S ->
    @eval_env_fuel nat LambdaBoxLocal_resource_fuel
                   LambdaBoxLocal_resource_trace vs e (Val v) f t ->
    env_consistent (x :: vn) (v :: vs).
  Proof.
    intros Hc Hcvt Hdis Heval.
    apply env_consistent_extend; [ exact Hc | ].
    intros k Hk.
    eapply anf_cvt_rel_var_lookup;
      [ exact Heval | reflexivity | exact Hcvt | exact Hdis | exact Hc | exact Hk ].
  Qed.

  (** Exps version: if xs[j] = vn[i], then vs[j] = rho[i]. *)
  Lemma anf_cvt_rel_exps_var_lookup rho es vs f t :
    @eval_fuel_many _ LambdaBoxLocal_resource_fuel LambdaBoxLocal_resource_trace
                    rho es vs f t ->
    forall S vn tgm S' C xs,
      anf_cvt_rel_exps S es vn tgm S' C xs ->
      Disjoint _ (FromList vn) S ->
      env_consistent vn rho ->
      forall j i x,
        nth_error xs j = Some x ->
        nth_error vn i = Some x ->
        exists v, nth_error vs j = Some v /\ nth_error rho i = Some v.
  Proof.
    intros Hmany. induction Hmany as [ | rho0 e0 es0 v0 vs0 f0 fs0 t0 ts0 Heval Hmany IH].
    - (* eval_many_enil *)
      intros S vn tgm S' C xs Hcvt Hdis Hcons j i x Hj Hi.
      inv Hcvt. destruct j; simpl in Hj; discriminate.
    - (* eval_many_econs *)
      intros S vn tgm S' C xs Hcvt Hdis Hcons j i x Hj Hi.
      inv Hcvt. fold anf_cvt_rel in *. fold anf_cvt_rel_exps in *.
      destruct j as [ | j']; simpl in Hj.
      + (* j = 0: xs[0] = x1 *)
        inv Hj. exists v0. split; [ reflexivity | ].
        eapply anf_cvt_rel_var_lookup; [ eassumption | reflexivity | eassumption .. ].
      + (* j > 0: use IH on the tail *)
        eapply IH; [ eassumption | | exact Hcons | exact Hj | exact Hi ].
        eapply Disjoint_Included_r.
        eapply anf_cvt_exp_subset. eassumption.
        exact Hdis.
  Qed.


  (** ** Alpha-equivalence for ANF values *)

  (* Two target values related to the same source value are preord_val-related.
     Analogous to cps_cvt_val_alpha_equiv in LambdaBoxLocal_to_LambdaANF_util.v. *)
  Lemma anf_cvt_val_alpha_equiv :
    forall k v v1 v2,
      anf_val_rel v v1 -> anf_val_rel v v2 ->
      preord_val cenv eq_fuel k v1 v2.
  Proof.
    intros k.
    eapply (LambdaBoxLocal_to_LambdaANF_anf_util.anf_cvt_val_alpha_equiv
              func_tag default_tag cnstrs
              eq_fuel eq_fuel cenv
              eq_fuel_compat (fun x y H => H) k).
  Qed.



  (* Every well-formed source value has a related target value. *)
  Lemma anf_val_rel_exists :
    forall v, well_formed_val v -> exists v', anf_val_rel v v'.
  Proof.
    intros v Hwf.
    eapply LambdaBoxLocal_to_LambdaANF_anf_corresp.anf_val_rel_exists.
    exact prim_map. exact Hwf.
  Qed.

  (** ** Consistency lemmas for duplicate ANF variables *)

  (* Every element of xs is either in FromList vn or in the input set S. *)
  Lemma anf_cvt_rel_exps_In_range :
    forall xs S es vn tgm S' C,
      anf_cvt_rel_exps S es vn tgm S' C xs ->
      forall x, List.In x xs -> x \in FromList vn \/ x \in S.
  Proof.
    induction xs as [ | x1 xs' IH]; intros S es vn tgm S' C Hcvt x Hin.
    - inv Hin.
    - inv Hcvt. fold anf_cvt_rel in *. fold anf_cvt_rel_exps in *.
      destruct Hin as [Heq | Hin].
      + subst. eapply anf_cvt_result_in_consumed. eassumption.
      + match goal with
        | [ Hcvt1 : anf_cvt_rel S _ _ _ ?S2 _ _,
            Hcvt_rest : anf_cvt_rel_exps ?S2 _ _ _ _ _ xs' |- _ ] =>
          destruct (IH _ _ _ _ _ _ Hcvt_rest x Hin) as [Hvn | HS2];
          [ left; exact Hvn
          | right; eapply (anf_cvt_exp_subset _ _ _ _ _ _ _ Hcvt1); exact HS2 ]
        end.
  Qed.

  (* Result variables of anf_cvt_rel_exps are not in the final output set. *)
  Lemma anf_cvt_rel_exps_results_not_in_output :
    forall xs S es vn tgm S' C,
      anf_cvt_rel_exps S es vn tgm S' C xs ->
      Disjoint _ (FromList vn) S ->
      forall x, List.In x xs -> ~ x \in S'.
  Proof.
    induction xs as [ | x1 xs' IH]; intros S es vn tgm S' C Hcvt Hdis x Hin.
    - inv Hin.
    - inv Hcvt. fold anf_cvt_rel in *. fold anf_cvt_rel_exps in *.
      destruct Hin as [Heq | Hin].
      + subst. intro Hin_S'.
        eapply anf_cvt_result_not_in_output; [ eassumption | exact Hdis | ].
        eapply (proj1 (proj2 anf_cvt_rel_subset)); eassumption.
      + eapply IH; try eassumption.
        eapply Disjoint_Included_r; [ | exact Hdis ].
        eapply anf_cvt_exp_subset. eassumption.
  Qed.

  (* Fresh variables (not in vn) appear at most once in xs. *)
  Lemma anf_cvt_rel_exps_unique_fresh :
    forall xs S es vn tgm S' C,
      anf_cvt_rel_exps S es vn tgm S' C xs ->
      Disjoint _ (FromList vn) S ->
      forall i j x,
        nth_error xs i = Some x -> nth_error xs j = Some x ->
        ~ x \in FromList vn ->
        i = j.
  Proof.
    induction xs as [ | x1 xs' IH]; intros S es vn tgm S' C Hcvt Hdis i j x Hxi Hxj Hx_not_vn.
    - destruct i; simpl in Hxi; discriminate.
    - inv Hcvt. fold anf_cvt_rel in *. fold anf_cvt_rel_exps in *.
      destruct i as [ | i'], j as [ | j']; simpl in Hxi, Hxj.
      + reflexivity.
      + exfalso. inv Hxi.
        match goal with
        | [ Hcvt1 : anf_cvt_rel S _ _ _ ?S2 _ x,
            Hcvt_rest : anf_cvt_rel_exps ?S2 _ _ _ _ _ xs' |- _ ] =>
          assert (Hx_not_S2 : ~ x \in S2)
            by (eapply anf_cvt_result_not_in_output; eassumption);
          destruct (anf_cvt_rel_exps_In_range _ _ _ _ _ _ _ Hcvt_rest x (nth_error_In _ _ Hxj))
            as [Hvn | HS2];
          [ exact (Hx_not_vn Hvn) | exact (Hx_not_S2 HS2) ]
        end.
      + exfalso. inv Hxj.
        match goal with
        | [ Hcvt1 : anf_cvt_rel S _ _ _ ?S2 _ x,
            Hcvt_rest : anf_cvt_rel_exps ?S2 _ _ _ _ _ xs' |- _ ] =>
          assert (Hx_not_S2 : ~ x \in S2)
            by (eapply anf_cvt_result_not_in_output; eassumption);
          destruct (anf_cvt_rel_exps_In_range _ _ _ _ _ _ _ Hcvt_rest x (nth_error_In _ _ Hxi))
            as [Hvn | HS2];
          [ exact (Hx_not_vn Hvn) | exact (Hx_not_S2 HS2) ]
        end.
      + f_equal.
        match goal with
        | [ Hcvt1 : anf_cvt_rel S _ _ _ ?S2 _ _,
            Hcvt_rest : anf_cvt_rel_exps ?S2 _ _ _ _ _ xs' |- _ ] =>
          eapply (IH _ _ _ _ _ _ Hcvt_rest); try eassumption;
          eapply Disjoint_Included_r;
          [ eapply anf_cvt_exp_subset; eassumption | exact Hdis ]
        end.
  Qed.

  (* Lemma 1: ANF-converted expression list variables are consistent w.r.t. preord_val.
     Duplicate xs positions map to the same source variable (by anf_cvt_rel_exps_var_lookup),
     so their target values are both anf_val_rel to the same source value,
     hence preord_val by alpha-equiv. *)
  Lemma anf_cvt_exps_consistent k rho_src es vs_src f t
        S vn tgm S' C xs vs_tgt :
    @eval_fuel_many _ LambdaBoxLocal_resource_fuel LambdaBoxLocal_resource_trace
                    rho_src es vs_src f t ->
    anf_cvt_rel_exps S es vn tgm S' C xs ->
    Disjoint _ (FromList vn) S ->
    env_consistent vn rho_src ->
    Forall2 anf_val_rel vs_src vs_tgt ->
    list_consistent (preord_val cenv eq_fuel k) xs vs_tgt.
  Proof.
    intros Hmany Hcvt Hdis Hcons HF2 i j x vi vj Hxi Hxj Hvi Hvj.
    destruct (Nat.eq_dec i j) as [Heq | Hneq].
    - (* i = j: reflexivity *)
      subst j. rewrite Hxi in Hxj. inv Hxj.
      rewrite Hvi in Hvj. inv Hvj.
      eapply preord_val_refl. tci.
    - (* i ≠ j *)
      set (d := @Dec _ _ (Decidable_FromList vn) x). 
      destruct d as [Hin_vn | Hnin_vn].
       (* x ∈ vn: use var_lookup to find same source value *)
      + destruct (In_nth_error _ _ Hin_vn) as [i_vn Hi_vn].
        destruct (anf_cvt_rel_exps_var_lookup _ _ _ _ _ Hmany _ _ _ _ _ _ Hcvt Hdis Hcons _ _ _ Hxi Hi_vn)
          as [v_src_i [Hvsi Hrhoi]].
        destruct (anf_cvt_rel_exps_var_lookup _ _ _ _ _ Hmany _ _ _ _ _ _ Hcvt Hdis Hcons _ _ _ Hxj Hi_vn)
          as [v_src_j [Hvsj Hrhoj]].
        rewrite Hrhoi in Hrhoj. inv Hrhoj.
        (* Both target values related to the same source value *)
        destruct (Forall2_nth_error_l _ _ _ _ _ HF2 Hvsi) as [vt_i [Hvti Hrel_i]].
        destruct (Forall2_nth_error_l _ _ _ _ _ HF2 Hvsj) as [vt_j [Hvtj Hrel_j]].
        rewrite Hvi in Hvti. inv Hvti.
        rewrite Hvj in Hvtj. inv Hvtj.
        eapply anf_cvt_val_alpha_equiv; eassumption.
      + (* x ∉ vn: fresh variables are unique, contradicts i ≠ j *)
        exfalso. apply Hneq.
        eapply anf_cvt_rel_exps_unique_fresh; eassumption.
  Qed.


  (* If the result variable x of a conversion is in vnames (Var_e case),
     then the ANF value at x in the environment is related to the
     evaluation result via anf_val_rel. *)
  Lemma anf_cvt_result_in_vnames_eval S e vn tgm S' C x vs rho v f t v' :
    anf_env_rel vn vs rho ->
    env_consistent vn vs ->
    Disjoint _ (FromList vn) S ->
    anf_cvt_rel S e vn tgm S' C x ->
    x \in FromList vn ->
    @eval_env_fuel nat LambdaBoxLocal_resource_fuel
                   LambdaBoxLocal_resource_trace vs e (Val v) f t ->
    M.get x rho = Some v' ->
    anf_val_rel v v'.
  Proof.
    intros Hrel Hcons Hdis Hcvt Hin Heval Hget.
    destruct (In_nth_error _ _ Hin) as [k Hk].
    assert (Hvk := anf_cvt_rel_var_lookup _ _ _ _ _ Heval v eq_refl _ _ _ _ _ _ k Hcvt Hdis Hcons Hk).
    destruct (Forall2_nth_error_r _ _ _ k _ Hrel Hk) as [v_src [Hvsrc [v'' [Hget' Hvrel]]]].
    rewrite Hvk in Hvsrc. inv Hvsrc.
    rewrite Hget in Hget'. inv Hget'.
    exact Hvrel.
  Qed.


  (** ** Branch extraction and Ecase helpers *)

  (* Extract branch data from the branches relation:
     given find_branch finds a source branch, extract the ANF conversion data
     (projection vars, body context, find_tag_nth position). *)
  Lemma anf_cvt_rel_branches_find_branch S1 brs vn r S2 pats dc e tg n_arity :
    anf_cvt_rel_branches S1 brs vn r cnstrs S2 pats ->
    find_branch dc n_arity brs = Some e ->
    tg = dcon_to_tag default_tag dc cnstrs ->
    exists vars S_mid S_out C_br r_br ctx_p m,
      FromList vars \subset S_mid /\
      List.length vars = N.to_nat n_arity /\
      NoDup vars /\
      ctx_bind_proj tg r vars (List.length vars) = ctx_p /\
      find_tag_nth pats tg (app_ctx_f ctx_p (C_br |[ Ehalt r_br ]|)) m /\
      anf_cvt_rel (S_mid \\ FromList vars) e (vars ++ vn) cnstrs S_out C_br r_br /\
      S_mid \subset S1.
  Proof.
    intros Hcvt Hfind Htg. subst tg.
    revert S1 S2 pats Hcvt.
    induction brs as [ | dc0 [n0 lnames0] e0 brs0 IH];
      intros S1 S2 pats Hcvt.
    - simpl in Hfind. discriminate.
    - inv Hcvt. fold anf_cvt_rel in *. fold anf_cvt_rel_branches in *.
      unfold find_branch in Hfind. fold find_branch in Hfind.
      destruct (classes.eq_dec dc dc0) as [Heq_dc | Hneq_dc].
      + subst dc0. simpl in Hfind.
        destruct (N.eq_dec n0 n_arity) as [Hn | Hn]; [ | discriminate ].
        subst n0. inv Hfind.
        do 7 eexists.
        split; [ | split; [ | split; [ | split; [ | split; [ | split ] ] ] ] ].
        * eassumption.
        * eassumption.
        * eassumption.
        * match goal with
          | [ H : Datatypes.length _ = N.to_nat n_arity |- _ ] =>
            rewrite H; reflexivity
          end.
        * apply find_tag_hd.
        * eassumption.
        * eapply (proj2 (proj2 (proj2 anf_cvt_rel_subset))). eassumption.
      + edestruct (IH Hfind) as (vars' & S_mid & S_out & C_br & r_br & ctx_p_f & m_f &
                          Hvars_sub & Hvars_len & Hvars_nd & Hctx_p & Hfind_tag &
                          Hcvt_br & HS_sub).
        { eassumption. }
        do 7 eexists.
        split; [ | split; [ | split; [ | split; [ | split; [ | split ] ] ] ] ].
        * exact Hvars_sub.
        * exact Hvars_len.
        * exact Hvars_nd.
        * exact Hctx_p.
        * apply find_tag_lt. exact Hfind_tag.
          intros Hc. apply Hneq_dc. symmetry. eapply dcon_to_tag_inj. exact Hc.
        * exact Hcvt_br.
        * exact HS_sub.
  Qed.

  Lemma find_branch_max_m_branches dc n brs e :
    find_branch dc n brs = Some e ->
    (N.to_nat n <= max_m_branches brs)%nat.
  Proof.
    intros Hfind. induction brs as [ | d' p e' brs' IH]. 
    - discriminate. 
    - destruct p as [m lnames]. simpl in Hfind. simpl.
      match type of Hfind with
      | context [if ?c then _ else _] => destruct c
      end.
      + destruct (N.eq_dec m n).
        * subst. apply Nat.le_max_l.
        * unfold nargs in Hfind. simpl in Hfind. destruct (N.eq_dec m n); [congruence | discriminate].
      + etransitivity; [exact (IH Hfind) | apply Nat.le_max_r].
  Qed.

  (** ** Correctness statements *)

  (* The key insight: correctness is stated for an arbitrary continuation e_k,
     not just Ehalt x. This is necessary because when composing contexts
     (e.g. Let_e produces comp_ctx_f C1 C2), the IH for C1 needs to work
     with C2 |[ e_k ]| as the continuation, not Ehalt x1.

     The disjointness condition ensures e_k doesn't reference intermediate
     variables bound by C (except the result variable x).
     All bound variables of C come from the fresh set S, so requiring
     disjointness with (S \\ S') \\ [set x] captures exactly the right condition. *)

  Definition anf_cvt_correct_exp (vs : fuel_sem.env) (e : expression.exp) (r : fuel_sem.result) (f t : nat) :=
    forall rho vnames C x S S' i,
      well_formed_env vs ->
      exp_wf (N.of_nat (Datatypes.length vnames)) e ->

      env_consistent vnames vs ->

      Disjoint _ (FromList vnames) S ->

      anf_env_rel vnames vs rho ->

      anf_cvt_rel S e vnames cnstrs S' C x ->

      forall e_k,
        (* e_k may reference x (the result) but not intermediate vars consumed from S *)
        Disjoint _ (occurs_free e_k) ((S \\ S') \\ [set x]) ->

        (* Source terminates *)
        (forall v v', r = (Val v) -> anf_val_rel v v' ->
         preord_exp cenv (anf_bound f t) eq_fuel i
                    (e_k, M.set x v' rho)
                    (C |[ e_k ]|, rho)) /\
        (* Source diverges *)
        (r = fuel_sem.OOT ->
         exists c, bstep_fuel cenv rho (C |[ e_k ]|) c eval.OOT tt).


  Definition anf_cvt_correct_exp_step (vs : fuel_sem.env) (e : expression.exp) (r : fuel_sem.result) (f t : nat) :=
    forall rho vnames C x S S' i,
      well_formed_env vs ->
      exp_wf (N.of_nat (Datatypes.length vnames)) e ->

      env_consistent vnames vs ->

      Disjoint _ (FromList vnames) S ->

      anf_env_rel vnames vs rho ->

      anf_cvt_rel S e vnames cnstrs S' C x ->

      forall e_k,
        Disjoint _ (occurs_free e_k) ((S \\ S') \\ [set x]) ->

        (* Source terminates *)
        (forall v v', r = (Val v) -> anf_val_rel v v' ->
                      preord_exp cenv
                                 (anf_bound (f <+> @one_i _ _ fuel_resource_LambdaBoxLocal e)
                                            (t <+> @one_i _ _ trace_resource_LambdaBoxLocal e))
                                 eq_fuel i
                                 (e_k, M.set x v' rho)
                                 (C |[ e_k ]|, rho)) /\
        (* Source diverges *)
        (r = fuel_sem.OOT ->
         exists c, bstep_fuel cenv rho (C |[ e_k ]|) c eval.OOT tt).


  (** ** Helper: set_many *)
  Fixpoint set_many (xs : list var) (vs : list val) (rho : M.t val) : M.t val :=
    match xs, vs with
    | x :: xs', v :: vs' => M.set x v (set_many xs' vs' rho)
    | _, _ => rho
    end.

  Lemma get_list_set_many xs vs rho :
    NoDup xs ->
    Datatypes.length xs = Datatypes.length vs ->
    get_list xs (set_many xs vs rho) = Some vs.
  Proof.
    revert vs. induction xs; intros vs Hnd Hlen; destruct vs; simpl in *; try lia.
    - reflexivity.
    - inv Hnd. rewrite M.gss.
      rewrite get_list_set_neq.
      + rewrite IHxs; auto.
      + intros Hc. apply H1. assumption.
  Qed.

  Lemma set_many_get_neq xs vs rho y :
    ~ List.In y xs ->
    M.get y (set_many xs vs rho) = M.get y rho.
  Proof.
    revert vs. induction xs; intros vs Hnin; destruct vs; simpl in *; auto.
    rewrite M.gso. apply IHxs. tauto. intros Heq; subst. apply Hnin. left; auto.
  Qed.

  Lemma set_many_set_comm x v xs vs rho :
    ~ List.In x xs ->
    forall y, M.get y (M.set x v (set_many xs vs rho)) =
              M.get y (set_many xs vs (M.set x v rho)).
  Proof.
    revert vs. induction xs; intros vs Hnin y; destruct vs; simpl in *; auto.
    assert (Ha : a <> x) by tauto.
    assert (Hx : ~ List.In x xs) by tauto.
    destruct (Pos.eq_dec y a).
    - subst.
      destruct (Pos.eq_dec a x).
      + exfalso; tauto.
      + rewrite M.gso. 2: auto. rewrite !M.gss. reflexivity.
    - destruct (Pos.eq_dec y x).
      + subst. rewrite M.gss.
        rewrite M.gso. 2: intro Hc; subst; tauto.
        rewrite set_many_get_neq. 2: auto.
        rewrite M.gss. reflexivity.
      + rewrite M.gso; auto. rewrite M.gso; auto. rewrite M.gso; auto.
        rewrite <- (IHxs vs Hx y). rewrite M.gso; auto.
  Qed.


  (** Looking up the first occurrence of x in set_many returns the
      corresponding value from vs. *)
  Lemma set_many_get_first xs vs rho x k :
    Datatypes.length xs = Datatypes.length vs ->
    nth_error xs k = Some x ->
    (forall (j : nat), (j < k)%nat -> nth_error xs j <> Some x) ->
    exists v, nth_error vs k = Some v /\
      M.get x (set_many xs vs rho) = Some v.
  Proof.
    revert vs k. induction xs as [ | a xs' IH]; intros vs k Hlen Hnth Hfirst.
    - destruct k; simpl in Hnth; discriminate.
    - destruct vs as [ | v0 vs'].
      { simpl in Hlen; lia. }
      simpl in Hlen.
      destruct k as [ | k'].
      + simpl in Hnth. inv Hnth. simpl.
        rewrite M.gss. eexists; eauto.
      + simpl in Hnth. simpl.
        assert (Ha_neq : a <> x).
        { intros ->. eapply (Hfirst 0%nat). lia. simpl. reflexivity. }
        rewrite M.gso. 2: now apply not_eq_sym.
        apply IH.
        * lia.
        * exact Hnth.
        * intros j Hj. apply (Hfirst (S j)). lia.
  Qed.

  (** Changing the base env for a key different from z doesn't affect
      M.get z through set_many. *)
  Lemma set_many_set_neq_base z x v xs vs rho :
    z <> x ->
    M.get z (set_many xs vs (M.set x v rho)) = M.get z (set_many xs vs rho).
  Proof.
    revert vs. induction xs as [ | a xs' IH]; intros vs Hneq.
    - simpl. rewrite M.gso; auto.
    - destruct vs as [ | va vs'].
      + simpl. rewrite M.gso; auto.
      + simpl. destruct (Pos.eq_dec z a) as [-> | Hza].
        * rewrite !M.gss. reflexivity.
        * rewrite !M.gso by auto. apply IH. exact Hneq.
  Qed.


  (** Every variable in xs is bound in set_many xs vs rho. *)
  Lemma set_many_get_in x xs vs rho :
    List.In x xs ->
    Datatypes.length xs = Datatypes.length vs ->
    exists v, M.get x (set_many xs vs rho) = Some v.
  Proof.
    revert vs. induction xs as [ | a xs' IH]; intros vs Hin Hlen.
    - destruct Hin.
    - destruct vs as [ | v vs']. { simpl in Hlen; lia. }
      simpl. destruct Hin as [-> | Hin'].
      + exists v. apply M.gss.
      + destruct (Pos.eq_dec x a) as [-> | Hneq].
        * exists v. apply M.gss.
        * rewrite M.gso by auto. apply IH. assumption. simpl in Hlen; lia.
  Qed.

  (** Variables not in xs are unaffected by set_many. *)
  Lemma set_many_get_notin y xs vs (rho : M.t val) :
    ~ List.In y xs ->
    M.get y (set_many xs vs rho) = M.get y rho.
  Proof.
    revert vs. induction xs as [ | a xs' IH]; intros vs Hnin.
    - reflexivity.
    - destruct vs as [ | v vs']. { reflexivity. }
      simpl. rewrite M.gso by (intro; apply Hnin; left; auto).
      apply IH. intro; apply Hnin; right; auto.
  Qed.

  (** If every variable in xs is bound in rho, get_list succeeds. *)
  Lemma get_list_exists xs (rho : M.t val) :
    (forall x, List.In x xs -> exists v, M.get x rho = Some v) ->
    exists vs, get_list xs rho = Some vs.
  Proof.
    induction xs as [ | a xs' IH]; intros Hbound.
    - exists []. reflexivity.
    - destruct (Hbound a (or_introl eq_refl)) as [v Hv].
      destruct (IH (fun x Hin => Hbound x (or_intror Hin))) as [vs_rest Hvs].
      exists (v :: vs_rest). simpl. rewrite Hv, Hvs. reflexivity.
  Qed.

  (** Adding M.set a v on top of rho preserves get_list when:
      - positions where xs has a already have value v in vs. *)
  Lemma get_list_set_shadow xs a v (rho : M.t val) vs :
    get_list xs rho = Some vs ->
    (forall (k : nat), nth_error xs k = Some a -> nth_error vs k = Some v) ->
    get_list xs (M.set a v rho) = Some vs.
  Proof.
    revert vs. induction xs as [ | b xs' IH]; intros vs Hgl Hshadow.
    - exact Hgl.
    - simpl in Hgl.
      destruct (M.get b rho) eqn:Hb; [ | discriminate].
      destruct (get_list xs' rho) eqn:Hrest; [ | discriminate].
      inv Hgl. simpl.
      destruct (Pos.eq_dec b a) as [-> | Hneq].
      + rewrite M.gss.
        assert (Hv := Hshadow 0%nat eq_refl). simpl in Hv. inv Hv.
        assert (Hgl' : get_list xs' (M.set a v rho) = Some l).
        { eapply IH. reflexivity. intros k Hk. exact (Hshadow (S k) Hk). }
        rewrite Hgl'. reflexivity.
      + rewrite M.gso by auto. rewrite Hb.
        assert (Hgl' : get_list xs' (M.set a v rho) = Some l).
        { eapply IH. reflexivity. intros k Hk. exact (Hshadow (S k) Hk). }
        rewrite Hgl'. reflexivity.
  Qed.

  (** get_list xs (set_many xs vs rho) = Some vs, provided duplicate
      positions in xs carry the same value in vs. *)
  Lemma get_list_set_many_dup xs vs rho :
    Datatypes.length xs = Datatypes.length vs ->
    (forall (i j : nat), (i < j)%nat ->
       nth_error xs i = nth_error xs j ->
       nth_error xs i <> None ->
       nth_error vs i = nth_error vs j) ->
    get_list xs (set_many xs vs rho) = Some vs.
  Proof.
    revert vs. induction xs as [ | a xs' IH]; intros vs Hlen Hdup.
    - destruct vs; [ reflexivity | simpl in Hlen; lia].
    - destruct vs as [ | v vs']. { simpl in Hlen; lia. }
      simpl. rewrite M.gss.
      assert (Hgl : get_list xs' (M.set a v (set_many xs' vs' rho)) = Some vs').
      { eapply get_list_set_shadow.
        - eapply IH.
          + simpl in Hlen; lia.
          + intros i j Hij Hnth Hnn.
            apply (Hdup (S i) (S j)). lia. exact Hnth. exact Hnn.
        - intros k Hk.
          assert (H0Sk := Hdup 0%nat (S k) ltac:(lia) ltac:(simpl; symmetry; exact Hk) ltac:(discriminate)).
          simpl in H0Sk. congruence. }
      rewrite Hgl. reflexivity.
  Qed.

  (** If every xs[i] is in the domain of set_many xs vs rho, get_list succeeds. *)
  Lemma get_list_set_many_exists xs vs rho :
    Datatypes.length xs = Datatypes.length vs ->
    exists vs', get_list xs (set_many xs vs rho) = Some vs'.
  Proof.
    intros Hlen.
    eapply get_list_exists.
    intros y Hy. eapply set_many_get_in; eauto.
  Qed.

  (* If xs and vs are list_consistent w.r.t. R, then
     get_list xs (set_many xs vs rho) produces R-related values.
     set_many stores left-to-right (first occurrence of each key wins);
     consistency ensures all duplicate values are R-related. *)
  (* Helper: find the first occurrence of x in a list, or return k if none before k. *)
  Lemma first_occurrence_exists (xs : list var) (k : nat) (x : var) :
    nth_error xs k = Some x ->
    exists k0, (k0 <= k)%nat /\ nth_error xs k0 = Some x /\
               forall j, (j < k0)%nat -> nth_error xs j <> Some x.
  Proof.
    revert k. induction xs as [ | a xs' IH]; intros k Hk.
    - destruct k; simpl in Hk; discriminate.
    - destruct k as [ | k'].
      + exists 0%nat. simpl in *. split; [ lia | split; [ exact Hk | ] ].
        intros j Hj. lia.
      + simpl in Hk.
        destruct (Pos.eq_dec a x) as [Heq | Hneq].
        * subst. exists 0%nat. simpl. split; [ lia | split; [ reflexivity | ] ].
          intros j Hj. lia.
        * destruct (IH k' Hk) as [k0 [Hle [Hk0 Hfirst]]].
          exists (S k0). simpl. split; [ lia | split; [ exact Hk0 | ] ].
          intros j Hj. destruct j as [ | j']; simpl.
          -- intros Heq'. inv Heq'. contradiction.
          -- apply Hfirst. lia.
  Qed.

  (* Helper: build Forall2 from pointwise nth_error relation *)
  Lemma Forall2_from_nth_error {A B : Type} (R : A -> B -> Prop)
        (l1 : list A) (l2 : list B) :
    Datatypes.length l1 = Datatypes.length l2 ->
    (forall k a b, nth_error l1 k = Some a -> nth_error l2 k = Some b -> R a b) ->
    Forall2 R l1 l2.
  Proof.
    revert l2. induction l1 as [ | a l1' IH]; intros l2 Hlen Hpw.
    - destruct l2; [ constructor | simpl in Hlen; lia ].
    - destruct l2 as [ | b l2']; [ simpl in Hlen; lia | ].
      constructor.
      + exact (Hpw 0%nat a b eq_refl eq_refl).
      + apply IH.
        * simpl in Hlen; lia.
        * intros k a' b' Ha' Hb'. exact (Hpw (S k) a' b' Ha' Hb').
  Qed.

  Lemma get_list_set_many_consistent (R : val -> val -> Prop) xs vs (rho : M.t val) :
    (forall x, R x x) ->
    Datatypes.length xs = Datatypes.length vs ->
    list_consistent R xs vs ->
    exists vs', get_list xs (set_many xs vs rho) = Some vs' /\
                Forall2 R vs vs'.
  Proof.
    intros Hrefl Hlen Hcons.
    destruct (get_list_set_many_exists xs vs rho Hlen) as [vs' Hvs'].
    exists vs'. split; [ exact Hvs' | ].
    assert (Hlen' : Datatypes.length vs = Datatypes.length vs').
    { assert (H : Datatypes.length xs = Datatypes.length vs') by
        (eapply get_list_length_eq; exact Hvs').
      rewrite Hlen in H. exact H. }
    eapply Forall2_from_nth_error; [ exact Hlen' | ].
    intros k vk v'k Hvk Hv'k.
    (* Find what key xs[k] is *)
    destruct (nth_error xs k) as [x | ] eqn:Hx.
    2: { (* nth_error xs k = None contradicts nth_error vs' k = Some v'k *)
         exfalso.
         (* k >= length xs but k < length vs' = length xs, contradiction *)
         assert (Hlen_xs_vs' : Datatypes.length xs = Datatypes.length vs') by lia.
         clear -Hx Hv'k Hlen_xs_vs'.
         revert vs' k Hv'k Hx Hlen_xs_vs'.
         induction xs; intros vs' k Hv'k Hx Hlen_xs_vs'.
         - simpl in Hlen_xs_vs'. destruct vs'; [ | simpl in Hlen_xs_vs'; lia].
           destruct k; simpl in Hv'k; discriminate.
         - destruct k; simpl in Hx; [ discriminate | ].
           destruct vs' as [ | v' vs'']; [ destruct k; simpl in Hv'k; discriminate | ].
           simpl in Hv'k. simpl in Hlen_xs_vs'.
           eapply IHxs; [ exact Hv'k | exact Hx | lia ]. }
    (* Find first occurrence of x in xs *)
    destruct (first_occurrence_exists xs k x Hx) as [k0 [Hle [Hk0 Hfirst]]].
    (* set_many_get_first: M.get x (set_many xs vs rho) = vs[k0] *)
    destruct (set_many_get_first xs vs rho x k0 Hlen Hk0 Hfirst) as [v0 [Hvk0 Hget]].
    (* get_list_nth_error: vs'[k] = M.get xs[k] (set_many xs vs rho) *)
    assert (Hv'eq : nth_error vs' k = Some v0).
    { erewrite get_list_nth_error; [ | exact Hvs' | exact Hx ]. exact Hget. }
    (* v'k = v0 *)
    assert (Heq : v'k = v0) by congruence. subst v'k.
    (* By list_consistent: R vk v0 *)
    exact (Hcons k k0 x vk v0 Hx Hk0 Hvk Hvk0).
  Qed.

  Lemma eval_fuel_many_length vs es vs1 f1 t1 :
    @eval_fuel_many _ LambdaBoxLocal_resource_fuel LambdaBoxLocal_resource_trace
                    vs es vs1 f1 t1 ->
    Datatypes.length vs1 = N.to_nat (exps_length es).
  Proof.
    intros Hrel. induction Hrel.
    - reflexivity.
    - simpl. rewrite IHHrel.
      destruct (exps_length es); try lia. destruct p; lia.
  Qed.

  Lemma anf_cvt_rel_exps_length S es vn S' C xs :
    anf_cvt_rel_exps S es vn cnstrs S' C xs ->
    Datatypes.length xs = N.to_nat (exps_length es).
  Proof.
    unfold anf_cvt_rel_exps.
    intros H. induction H as [ | ? ? ? ? ? ? ? ? ? ? ? ? ? IH].
    - reflexivity.
    - simpl. rewrite IH.
      destruct (exps_length es); try lia. destruct p; lia.
  Qed.

  (* P0: correctness for expression lists.
     Note: xs may have duplicates (from anf_Var) and may overlap with vnames.
     This is sound because:
     - Duplicates in xs always come from the same Var_e reference,
       so they have the same value in vs'.
     - Fresh variables in xs (from non-Var expressions) are unique
       and disjoint from vnames (since S ∩ vnames = ∅). *)
  Definition anf_cvt_correct_exps (vs_env : fuel_sem.env) (es : expression.exps)
             (vs1 : list value) (f t : nat) :=
    forall rho vnames C xs S S' i,
      well_formed_env vs_env ->
      exps_wf (N.of_nat (Datatypes.length vnames)) es ->
      env_consistent vnames vs_env ->
      Disjoint _ (FromList vnames) S ->
      anf_env_rel vnames vs_env rho ->
      anf_cvt_rel_exps S es vnames cnstrs S' C xs ->
      forall e_k vs',
        Forall2 anf_val_rel vs1 vs' ->
        Disjoint _ (occurs_free e_k) ((S \\ S') \\ FromList xs) ->
        preord_exp cenv (anf_bound f t) eq_fuel i
                   (e_k, set_many xs vs' rho)
                   (C |[ e_k ]|, rho).


  (** ** Main Correctness Theorem *)

  (* The proof proceeds by mutual induction using eval_env_fuel_ind'.
     The scheme requires goals in order:
       P  (eval_env_step):   10 cases
       P0 (eval_fuel_many):  2 cases
       P1 (eval_env_fuel):   5 cases
     Total: 17 cases *)

  Lemma anf_cvt_correct :
    forall vs e r f t,
      @eval_env_fuel _ LambdaBoxLocal_resource_fuel LambdaBoxLocal_resource_trace vs e r f t ->
      anf_cvt_correct_exp vs e r f t.
  Proof.
    eapply eval_env_fuel_ind' with (P1 := anf_cvt_correct_exp)
                                   (P0 := anf_cvt_correct_exps)
                                   (P := anf_cvt_correct_exp_step).

    (** ** eval_env_step cases (P = anf_cvt_correct_exp_step) *)

    - (* 1. eval_Con_step: Con_e terminates *)
      intros es vs0 vs' dc fs ts Hmany IH_many.
      unfold anf_cvt_correct_exp_step.
      intros rho vnames C x S S' i Hwf Hwfe Hnd Hdis Henv Hcvt e_k Hdis_ek.
      inv Hcvt. fold anf_cvt_rel_exps in *.
      match goal with
      | [ Hes : anf_cvt_rel_exps _ es _ _ _ _ _ |- _ ] => rename Hes into Hcvt_es
      end.
      assert (Hwfe_es : exps_wf (N.of_nat (Datatypes.length vnames)) es) by (inversion Hwfe; assumption).
      rewrite <- app_ctx_f_fuse.
      split.
      + intros v v' Heq Hrel. inv Heq. inv Hrel.
        eapply preord_exp_post_monotonic.
        2:{ eapply preord_exp_trans. tci. eapply eq_fuel_idemp.
            2:{ intros m. eapply IH_many.
                - eassumption.
                - exact Hwfe_es.
                - eassumption.
                - eapply Disjoint_Included_r. eapply Setminus_Included. eassumption.
                - eassumption.
                - exact Hcvt_es.
                - eassumption. (* Forall2 anf_val_rel *)
                - (* Disjoint (occurs_free (Econstr ...)) ... *)
                  simpl. rewrite occurs_free_Econstr.
                  eapply Union_Disjoint_l.
                  + eapply Disjoint_Setminus_r. eapply Included_refl.
                  + eapply Setminus_Disjoint_preserv_l.
                    eapply Setminus_Disjoint_preserv_r.
                    eapply Disjoint_Included_r.
                    2: exact Hdis_ek.
                    intros y [[Hy_S Hy_nx] Hy_nS'].
                    split; [split; [exact Hy_S | exact Hy_nS'] | exact Hy_nx]. }
            (* Prove length xs = length vs'0 *)
            assert (Hlen_xs_vs0 : Datatypes.length xs = Datatypes.length vs0).
            { pose proof (anf_cvt_rel_exps_length _ _ _ _ _ _ Hcvt_es).
              assert (Datatypes.length vs0 = N.to_nat (exps_length es))
                by (clear -Hmany; induction Hmany;
                    [ reflexivity
                    | simpl; rewrite IHHmany;
                      destruct (exps_length es); try lia; destruct p; lia ]).
              lia. }
            assert (Hlen_xs_vs'0 : Datatypes.length xs = Datatypes.length vs'0)
              by (pose proof (Forall2_length _ _ _ H1); lia).
            (* Establish get_list existence for Econstr_red *)
            destruct (get_list_set_many_exists xs vs'0 rho Hlen_xs_vs'0)
              as [vs_new Hvs_new].
            eapply preord_exp_trans. tci. eapply eq_fuel_idemp.
            2:{ intros m. eapply preord_exp_Econstr_red. exact Hvs_new. }
            eapply preord_exp_refl. now eapply eq_fuel_compat.
            intros y Hy v1 Hget.
            destruct (Pos.eq_dec y x) as [Heq|Hneq].
            * subst. rewrite M.gss in Hget. inv Hget.
              eexists. split. rewrite M.gss. reflexivity.
              rewrite preord_val_eq. simpl. split; eauto. 
              (* Forall2 (preord_val cenv eq_fuel i) vs'0 vs_new *)
              { assert (Hcons_xs : list_consistent (preord_val cenv eq_fuel i) xs vs'0).
                { eapply anf_cvt_exps_consistent; try eassumption.
                  eapply Disjoint_Included_r. eapply Setminus_Included. eassumption. }
                destruct (get_list_set_many_consistent
                            (preord_val cenv eq_fuel i) xs vs'0 rho)
                  as [vs_new' [Hvs_new' HF2_new]].
                - intros x0. eapply preord_val_refl. tci.
                - exact Hlen_xs_vs'0.
                - exact Hcons_xs.
                - rewrite Hvs_new in Hvs_new'. inv Hvs_new'. exact HF2_new. }
            * rewrite M.gso in Hget; auto.
              destruct (in_dec Pos.eq_dec y xs) as [Hyin | Hynin].
              -- (* y in xs: both rho and set_many bindings are
                    anf_val_rel to the same source value, needs alpha-equiv *)
                rewrite M.gso; [ | assumption ]. 
                edestruct set_many_get_in as [v_y Hget_y]; eauto.
                rewrite Hget_y. eexists. split; [ reflexivity | ]. 
                - (* y ∈ vnames (eliminate y ∈ S \ {x} by contradiction) *)
                  assert (Hy_vn : y \in FromList vnames).
                  { destruct (anf_cvt_rel_exps_In_range _ _ _ _ _ _ _ Hcvt_es y Hyin)
                      as [Hvn | HS_x].
                    - exact Hvn.
                    - exfalso.
                      assert (Hy_not_S' : ~ y \in S').
                      { eapply anf_cvt_rel_exps_results_not_in_output; [ eassumption | | eassumption ].
                        eapply Disjoint_Included_r; [ eapply Setminus_Included | exact Hdis ]. }
                      destruct HS_x as [Hy_S Hy_nx].
                      destruct Hdis_ek as [Hdis_ek'].
                      apply (Hdis_ek' y). constructor.
                      + exact Hy.
                      + constructor.
                        * constructor; assumption.
                        * exact Hy_nx. }
                  (* Find positions in vnames and xs *)
                  destruct (In_nth_error _ _ Hy_vn) as [n Hn].
                  destruct (In_nth_error _ _ Hyin) as [k Hk].
                  destruct (first_occurrence_exists xs k y Hk) as [k0 [Hle [Hk0 Hfirst]]].
                  (* Connect v_y to vs'0[k0] via set_many_get_first *)
                  destruct (set_many_get_first xs vs'0 rho y k0 Hlen_xs_vs'0 Hk0 Hfirst)
                    as [v0 [Hv0k Hget_v0]].
                  assert (Hvy_eq : v_y = v0) by congruence. subst v0.
                  (* Common source value via var_lookup *)
                  assert (Hdis_exps : Disjoint _ (FromList vnames) (S \\ [set x])).
                  { eapply Disjoint_Included_r. eapply Setminus_Included. exact Hdis. }
                  destruct (anf_cvt_rel_exps_var_lookup _ _ _ _ _ Hmany
                              _ _ _ _ _ _ Hcvt_es Hdis_exps
                              Hnd _ _ _ Hk0 Hn)
                    as [v_src [Hvsrc_k0 Hvsrc_n]].
                  (* anf_val_rel v_src v1 from anf_env_rel *)
                  destruct (anf_env_rel_nth_error _ _ _ _ _ _ Henv Hn Hvsrc_n)
                    as [v_tgt [Hget_tgt Hrel_tgt]].
                  rewrite Hget in Hget_tgt. inv Hget_tgt.
                  (* anf_val_rel v_src v_y from Forall2 *)
                  destruct (Forall2_nth_error_l _ _ _ _ _ H1 Hvsrc_k0)
                    as [v_y' [Hvy' Hrel_vy]].
                  rewrite Hv0k in Hvy'. inv Hvy'.
                  (* alpha-equivalence *)
                  eapply anf_cvt_val_alpha_equiv; eassumption.
              -- (* y not in xs: set_many does not affect y *)
                 eexists. split. rewrite M.gso; auto.
                 rewrite set_many_get_notin; auto. eassumption.
                 eapply preord_val_refl. tci. }
        unfold inclusion, comp, eq_fuel, anf_bound.
        intros [[[? ?] ?] ?] [[[? ?] ?] ?].
        intros [[[[? ?] ?] ?] [[[[? ?] ?] ?] [? ?]]].
        unfold_all. destruct p. destructAll. simpl in *. lia.
      + intros Habs. congruence.

    - (* 2. eval_Con_step_OOT: Con_e diverges *)
      intros es es1 es2 e0 vs0 rho0 dc0 fs0 f0 t0 ts0 Hexps Hmany IH_many Hoot IH_oot.
      unfold anf_cvt_correct_exp_step.
      intros rho vnames C x S S' i Hwf Hwfe Hnd Hdis Henv Hcvt e_k Hdis_ek.
      split; [intros; congruence | intros _; eexists 0%nat; constructor 1; unfold algebra.one; simpl; lia].

    - (* 3. eval_App_step: App_e with Clos_v *)
      intros e1' e2' e_body v2 r0 na0 rho0 rho_clos f1' f2' f3' t1' t2' t3'
             Heval1 IH1 Heval2 IH2 Heval3 IH3.
      unfold anf_cvt_correct_exp_step.
      intros rho vnames C x S S' i Hwf Hwfe Hnd Hdis Henv Hcvt e_k Hdis_ek.
      inv Hcvt. fold anf_cvt_rel in *.
      (* After inv (anf_App):
         C = comp_ctx_f C1 (comp_ctx_f C2 (Eletapp_c r0 x1 func_tag [x2] Hole_c))
         x = r0  (the result variable)
         Hcvt_e1 : anf_cvt_rel S e1' vnames cnstrs S2 C1 x1
         Hcvt_e2 : anf_cvt_rel S2 e2' vnames cnstrs S3 C2 x2
         H_r_in : r0 \in S3 *)
      match goal with
      | [ He1 : anf_cvt_rel _ e1' vnames _ _ _ _,
          He2 : anf_cvt_rel _ e2' vnames _ _ _ _,
          Hr : x \in _ |- _ ] =>
        rename He1 into Hcvt_e1; rename He2 into Hcvt_e2; rename Hr into Hr_in
      end.
      rewrite <- !app_ctx_f_fuse.
      split.
      + (* Termination case *)
        intros v v' Heq Hrel. subst r0.
        (* Get target values for Clos_v and v2 *)
        assert (Hwf_clos : well_formed_val (Clos_v rho_clos na0 e_body)).
        { eapply (eval_env_step_preserves_wf (Hf := LambdaBoxLocal_resource_fuel)).
          exact Heval1. reflexivity. exact Hwf.
          unfold well_formed_in_env.
          replace (Datatypes.length rho0) with (Datatypes.length vnames)
            by (eapply anf_env_rel_length; eassumption).
          inversion Hwfe; subst; eassumption. }
        destruct (anf_val_rel_exists _ Hwf_clos) as [clos_v' Hrel_clos].
        assert (Hwf_v2 : well_formed_val v2).
        { eapply (eval_env_step_preserves_wf (Hf := LambdaBoxLocal_resource_fuel)).
          exact Heval2. reflexivity. exact Hwf.
          unfold well_formed_in_env.
          replace (Datatypes.length rho0) with (Datatypes.length vnames)
            by (eapply anf_env_rel_length; eassumption).
          inversion Hwfe; subst; eassumption. }
        destruct (anf_val_rel_exists _ Hwf_v2) as [v2' Hrel_v2].
        (* Chain: IH1 + env bridge + IH2 + env bridge + Eletapp reduction *)
        eapply preord_exp_post_monotonic.
        2:{ eapply preord_exp_trans. tci. eapply eq_fuel_idemp.
            (* IH1: C1 layer *)
            2:{ intros m.
                assert (Hdis_C2ek : Disjoint _ (occurs_free (C2 |[ Eletapp x x1 func_tag [x2] e_k ]|))
                                               ((S \\ S2) \\ [set x1])).
                { eapply anf_cvt_disjoint_occurs_free_ctx_app;
                    [ exact Hcvt_e1 | exact Hcvt_e2 | exact Hr_in | exact Hdis | exact Hdis_ek ]. }
                edestruct IH1 as [IH1_val _].
                - eassumption.
                - inversion Hwfe; subst; eassumption. (* exp_wf *)
                - eassumption.
                - eassumption.
                - eassumption.
                - exact Hcvt_e1.
                - exact Hdis_C2ek.
                - eapply IH1_val; eauto. }
            eapply preord_exp_trans with (P1 := anf_bound (f3' + 2) (t3' + 2)).
            tci. eapply eq_fuel_idemp.
            (* IH2: C2 layer, in env with x1 bound *)
            2:{ intros m.
                assert (Hnd_x1 : env_consistent (x1 :: vnames) (Clos_v rho_clos na0 e_body :: rho0)).
                { eapply env_consistent_extend_from_cvt;
                    [ exact Hnd | exact Hcvt_e1 | exact Hdis | exact Heval1 ]. }
                assert (Henv_x1 : anf_env_rel vnames rho0 (M.set x1 clos_v' rho)).
                { eapply anf_env_rel_set; [ exact Henv | ].
                  intros k Hk.
                  destruct (anf_cvt_result_in_consumed _ _ _ _ _ _ _ Hcvt_e1) as [Hin_vn | Hin_S].
                  - exists (Clos_v rho_clos na0 e_body). split.
                    + assert (Hnd_inst := Hnd_x1 0%nat (Datatypes.S k) x1 eq_refl Hk).
                      simpl in Hnd_inst. symmetry. exact Hnd_inst.
                    + exact Hrel_clos.
                  - exfalso. destruct Hdis as [Hdis''].
                    apply (Hdis'' x1). constructor.
                    + eapply nth_error_In. exact Hk.
                    + exact Hin_S. }
                assert (Hdis_letapp : Disjoint _ (occurs_free (Eletapp x x1 func_tag [x2] e_k))
                                                 ((S2 \\ S3) \\ [set x2])).
                { eapply anf_cvt_disjoint_eletapp;
                    [ exact Hcvt_e1 | exact Hcvt_e2 | exact Hr_in | exact Hdis | exact Hdis_ek ]. }
                edestruct IH2 as [IH2_val _].
                - eassumption.
                - inversion Hwfe; subst; eassumption. (* exp_wf *)
                - eassumption.
                - eapply Disjoint_Included_r; [eapply (proj1 anf_cvt_rel_subset); exact Hcvt_e1 | exact Hdis].
                - exact Henv_x1.
                - exact Hcvt_e2.
                - exact Hdis_letapp.
                - eapply IH2_val; eauto. }
            (* Eletapp step + body evaluation + env bridging *)
            (* Extract closure structure from Hrel_clos *)
            assert (Hclos_inv :
              exists rho_fc names_fc x_pc f_cc C_bc r_bc S1_bc S2_bc,
                clos_v' = Vfun rho_fc (Fcons f_cc func_tag [x_pc]
                            (C_bc |[ Ehalt r_bc ]|) Fnil) f_cc /\
                anf_env_rel' anf_val_rel names_fc rho_clos rho_fc /\
                env_consistent names_fc rho_clos /\
                Disjoint var (x_pc |: (f_cc |: FromList names_fc)) S1_bc /\
                ~ x_pc \in f_cc |: FromList names_fc /\
                ~ f_cc \in FromList names_fc /\
                anf_cvt_rel S1_bc e_body (x_pc :: names_fc) cnstrs S2_bc C_bc r_bc).
            { inversion Hrel_clos; try discriminate; subst.
              do 8 eexists.
              split; [ reflexivity | ].
              repeat (split; [ eassumption | ]).
              eassumption. }
            destruct Hclos_inv as (rho_fc & names_fc & x_pc & f_cc & C_bc & r_bc &
              S1_bc & S2_bc & Hclos_eq & Henv_fc & Hnd_fc &
              Hdis_fc & Hxpc_nin & Hfcc_nin & Hcvt_bc).
            subst clos_v'.
            set (defs_cc := Fcons f_cc func_tag [x_pc] (C_bc |[ Ehalt r_bc ]|) Fnil) in *.
            set (rho_bc := M.set x_pc v2' (def_funs defs_cc defs_cc rho_fc rho_fc)).
            (* Get body evaluation from IH3 *)
            assert (Henv_bc : anf_env_rel (x_pc :: names_fc) (v2 :: rho_clos) rho_bc).
            { constructor.
              - exists v2'. split. unfold rho_bc. rewrite M.gss. reflexivity. exact Hrel_v2.
              - unfold rho_bc. apply anf_env_rel_weaken.
                + apply anf_env_rel_weaken.
                  * exact Henv_fc.
                  * exact Hfcc_nin.
                + intro Hc. apply Hxpc_nin. now right. }
            (* Apply IH3 to get body correctness *)
            assert (IH3_full :
              (forall v0 v'0, Val v = Val v0 -> anf_val_rel v0 v'0 ->
               preord_exp cenv (anf_bound f3' t3') eq_fuel (i + 1)%nat
                          (Ehalt r_bc, M.set r_bc v'0 rho_bc)
                          (C_bc |[ Ehalt r_bc ]|, rho_bc)) /\
              (Val v = fuel_sem.OOT ->
               exists c, bstep_fuel cenv rho_bc (C_bc |[ Ehalt r_bc ]|) c eval.OOT tt)).
            { eapply IH3 with (vnames := x_pc :: names_fc).
              - (* well_formed_env (v2 :: rho_clos) *)
                constructor; [exact Hwf_v2 | inversion Hwf_clos; assumption].
              - (* exp_wf (N.of_nat (length (x_pc :: names_fc))) e_body *)
                inv Hwf_clos. unfold well_formed_in_env in *. 
                specialize (H3 v2). eapply Forall2_length in Henv_fc.
                simpl in *. unfold var, M.elt. rewrite <- Henv_fc. eauto.   
              - (* env_consistent (x_pc :: names_fc) (v2 :: rho_clos) *)
                apply env_consistent_extend.
                + exact Hnd_fc.
                + intros k Hk. exfalso. apply Hxpc_nin. right.
                  eapply nth_error_In. exact Hk.
              - (* Disjoint (FromList (x_pc :: names_fc)) S1_bc *)
                eapply Disjoint_Included_l. 2: exact Hdis_fc.
                intros z Hz. inv Hz. now left. right. now right.
              - exact Henv_bc.
              - exact Hcvt_bc.
              - (* Disjoint (occurs_free (Ehalt r_bc)) ((S1_bc \\ S2_bc) \\ [set r_bc]) *)
                constructor. intros z Hz. inv Hz.
                (* H : occurs_free (Ehalt r_bc) z → z = r_bc *)
                inversion H; subst.
                (* H0 : In ((S1_bc \\ S2_bc) \\ [set r_bc]) r_bc — impossible *)
                destruct H0 as [_ Habs]. apply Habs. constructor. }
            destruct IH3_full as [IH3_val _].
            specialize (IH3_val v v' eq_refl Hrel).
            (* IH3_val : preord_exp (anf_bound f3' t3') eq_fuel (i+1)
                 (Ehalt r_bc, M.set r_bc v' rho_bc) (C_bc |[ Ehalt r_bc ]|, rho_bc) *)
            (* Extract body evaluation from IH3_val *)
            (* First build the Ehalt bstep_fuel with existential fuel/trace *)
            (* Directly specialize IH3_val: Ehalt r_bc evaluates in 1 step *)
            assert (Hle_h : (to_nat 1%nat <= i + 1)%nat) by (simpl; lia).
            assert (Hehalt : @bstep_fuel cenv nat fuel_res unit trace_res
                                         (M.set r_bc v' rho_bc) (Ehalt r_bc) 1%nat (Res v') tt).
            { pose proof (BStepf_run cenv (M.set r_bc v' rho_bc) (Ehalt r_bc) (Res v') 0%nat tt
                (BStept_halt cenv r_bc v' (M.set r_bc v' rho_bc) (M.gss r_bc v' rho_bc))) as Hbsf.
              simpl in Hbsf. exact Hbsf. }
            destruct (IH3_val (Res v') 1%nat tt Hle_h Hehalt)
              as (v_body_res & cin_bc & cout_bc & Hbstep_bc & Hpost_bc & Hres_bc).
            (* Body result must be Res (not OOT) *)
            destruct v_body_res as [ | v_bc ].
            { simpl in Hres_bc. contradiction. }
            simpl in Hres_bc.
            (* Hres_bc : preord_val cenv eq_fuel i v' v_bc *)
            (* Case split on whether x1 = x2 *)
            destruct (Pos.eq_dec x1 x2) as [Heq_x12 | Hneq_x12].
            { (* Case x1 = x2: both results map to the same variable in vnames *)
              subst x2.
              (* x1 ∈ FromList vnames *)
              assert (Hx1_in_vn : x1 \in FromList vnames).
              { destruct (anf_cvt_result_in_consumed _ _ _ _ _ _ _ Hcvt_e2) as [Hin | Hin].
                - exact Hin.
                - exfalso. eapply anf_cvt_result_not_in_output.
                  exact Hcvt_e1. exact Hdis. exact Hin. }
              (* Get v_rho from original anf_env_rel *)
              assert (Hx1_list : List.In x1 vnames) by exact Hx1_in_vn.
              apply In_nth_error in Hx1_list. destruct Hx1_list as [k0 Hk0].
              destruct (Forall2_nth_error_r _ _ _ _ _ Henv Hk0)
                as [v_src_k [Hk0_vs [v_rho [Hget_rho Hrel_rho]]]].
              (* preord_val (Vfun rho_fc defs_cc f_cc) v2' via alpha-equiv + transitivity *)
              assert (Hpv_cv : forall j, preord_val cenv eq_fuel j
                        (Vfun rho_fc defs_cc f_cc) v2').
              { intro j. eapply preord_val_trans. tci. eapply eq_fuel_idemp.
                - eapply anf_cvt_val_alpha_equiv. exact Hrel_clos.
                  eapply anf_cvt_result_in_vnames_eval;
                    [ exact Henv | exact Hnd | exact Hdis
                    | exact Hcvt_e1 | exact Hx1_in_vn | exact Heval1 | exact Hget_rho ].
                - intros m0. eapply anf_cvt_val_alpha_equiv.
                  eapply anf_cvt_result_in_vnames_eval;
                    [ exact Henv | exact Hnd
                    | eapply Disjoint_Included_r;
                        [eapply anf_cvt_exp_subset; exact Hcvt_e1 | exact Hdis]
                    | exact Hcvt_e2 | exact Hx1_in_vn | exact Heval2 | exact Hget_rho ].
                  exact Hrel_v2. }
              (* Extract Vfun structure of v2' from preord_val *)
              assert (Hpv_inst := Hpv_cv (cin_bc + i + 1)%nat).
              rewrite preord_val_eq in Hpv_inst.
              destruct v2' as [ | rho2_fc B2 f2 | | ];
                try (simpl in Hpv_inst; contradiction).
              (* v2' = Vfun rho2_fc B2 f2 *)
              (* Get body correspondence from preord_val *)
              assert (Hfind_cc : find_def f_cc defs_cc =
                Some (func_tag, [x_pc], C_bc |[ Ehalt r_bc ]|)).
              { unfold defs_cc. simpl.
                destruct (M.elt_eq f_cc f_cc); [ reflexivity | congruence ]. }
              assert (Hset_cc : Some rho_bc = set_lists [x_pc]
                [Vfun rho2_fc B2 f2] (def_funs defs_cc defs_cc rho_fc rho_fc)).
              { unfold rho_bc. reflexivity. }
              edestruct Hpv_inst as (xs2_pc & e2_body & rho2_body &
                Hfind_v2 & Hset_v2 & Hbody_preord).
              { reflexivity. }
              { exact Hfind_cc. }
              { exact Hset_cc. }
              (* Transfer body evaluation via preord_exp' *)
              assert (Hbody_pe : preord_exp' cenv (preord_val cenv) eq_fuel eq_fuel
                        (cin_bc + i)%nat
                        (C_bc |[ Ehalt r_bc ]|, rho_bc) (e2_body, rho2_body)).
              { apply Hbody_preord. lia.
                constructor; [ | constructor ].
                eapply preord_val_refl. tci. }
              destruct (Hbody_pe (Res v_bc) cin_bc cout_bc) as
                (v2_body_res & cin2_bc & cout2_bc & Hbstep2_bc & Hpost2_bc & Hres2_bc).
              { simpl. lia. }
              { exact Hbstep_bc. }
              destruct v2_body_res as [ | v2_bc ].
              { simpl in Hres2_bc. contradiction. }
              simpl in Hres2_bc.
              (* Establish forall m', preord_val m' v_bc v2_bc
                 using Hpv_cv at varying indices + bstep determinism *)
              assert (Hpv_all : forall m', preord_val cenv eq_fuel m' v_bc v2_bc).
              { intro m'.
                pose proof (Hpv_cv (cin_bc + m' + 1)%nat) as Hpv_m.
                rewrite preord_val_eq in Hpv_m.
                edestruct Hpv_m as (xs2_m & e2_m & rho2_m &
                  Hfind_m & Hset_m & Hbp_m).
                { reflexivity. }
                { exact Hfind_cc. }
                { exact Hset_cc. }
                replace e2_m with e2_body in * by congruence.
                replace xs2_m with xs2_pc in * by congruence.
                replace rho2_m with rho2_body in *.
                2:{ congruence. }
                assert (Hba_m : preord_exp' cenv (preord_val cenv) eq_fuel eq_fuel
                          (cin_bc + m')%nat
                          (C_bc |[ Ehalt r_bc ]|, rho_bc) (e2_body, rho2_body)).
                { apply Hbp_m. lia.
                  constructor; [ | constructor ].
                  eapply preord_val_refl. tci. }
                destruct (Hba_m (Res v_bc) cin_bc cout_bc) as
                  (v2_m & cin2_m & cout2_m & Hbs2_m & _ & Hres2_m).
                { simpl. lia. }
                { exact Hbstep_bc. }
                destruct v2_m as [ | v2_m_val ].
                { simpl in Hres2_m. contradiction. }
                simpl in Hres2_m.
                eapply bstep_fuel_deterministic in Hbs2_m.
                2:{ exact Hbstep2_bc. }
                destruct Hbs2_m as [Hv_eq [_ _]]. subst v2_m_val.
                replace (cin_bc + m' - cin_bc)%nat with m' in Hres2_m
                  by lia.
                exact Hres2_m. }
              (* preord_val i v' v2_bc via transitivity *)
              assert (Hpv_direct : preord_val cenv eq_fuel i v' v2_bc).
              { eapply preord_val_trans. tci. eapply eq_fuel_idemp.
                - eapply preord_val_monotonic. exact Hres_bc. lia.
                - exact Hpv_all. }
              (* Unfold preord_exp and construct BStept_letapp with v2' *)
              intros v1 cin cout Hle_cin Hbstep_ek.
              (* Continuation env bridge *)
              assert (Hx_neq_x1 : x <> x1).
              { intro Heq. subst x.
                destruct Hdis as [Hdis']. apply (Hdis' x1).
                constructor.
                - exact Hx1_in_vn.
                - eapply anf_cvt_exp_subset. exact Hcvt_e1.
                  eapply anf_cvt_exp_subset. exact Hcvt_e2.
                  exact Hr_in. }
              assert (Hrefl : preord_exp cenv eq_fuel eq_fuel i
                        (e_k, M.set x v' rho)
                        (e_k, M.set x v2_bc
                          (M.set x1 (Vfun rho2_fc B2 f2)
                            (M.set x1 (Vfun rho_fc defs_cc f_cc) rho)))).
              { eapply preord_exp_refl. now eapply eq_fuel_compat.
                intros y Hy.
                destruct (Pos.eq_dec y x) as [-> | Hneq_x].
                - (* y = x *)
                  unfold preord_var_env. intros v0 Hget0.
                  rewrite M.gss in Hget0. inv Hget0.
                  eexists. split. rewrite M.gss. reflexivity.
                  exact Hpv_direct.
                - (* y ≠ x *)
                  unfold preord_var_env. intros v0 Hget0.
                  rewrite M.gso in Hget0 by auto.
                  destruct (Pos.eq_dec y x1) as [-> | Hneq_x1].
                  + (* y = x1 *)
                    eexists. split.
                    { rewrite M.gso by auto. rewrite M.gss. reflexivity. }
                    eapply anf_cvt_val_alpha_equiv.
                    * eapply anf_cvt_result_in_vnames_eval;
                        [ exact Henv | exact Hnd
                        | eapply Disjoint_Included_r;
                            [eapply anf_cvt_exp_subset; exact Hcvt_e1 | exact Hdis]
                        | exact Hcvt_e2 | exact Hx1_in_vn | exact Heval2 | exact Hget0 ].
                    * exact Hrel_v2.
                  + (* y ≠ x, y ≠ x1 *)
                    eexists. split.
                    { rewrite M.gso by auto. rewrite M.gso by auto.
                      rewrite M.gso by auto. exact Hget0. }
                    eapply preord_val_refl. tci. }
              edestruct Hrefl as (v_cont & cin_cont & cout_cont &
                Hbstep_cont & Heq_cont & Hres_cont).
              { exact Hle_cin. }
              { exact Hbstep_ek. }
              do 3 eexists. split.
              { econstructor 2. eapply BStept_letapp.
                - rewrite M.gss. reflexivity.
                - simpl. rewrite M.gss. reflexivity.
                - exact Hfind_v2.
                - symmetry. exact Hset_v2.
                - exact Hbstep2_bc.
                - exact Hbstep_cont. }
              split.
              { unfold anf_bound in Hpost_bc, Hpost2_bc |- *.
                unfold eq_fuel in Heq_cont, Hpost2_bc. simpl in Heq_cont, Hpost_bc, Hpost2_bc.
                destruct Hpost_bc as [Hlb_bc Hub_bc].
                destruct Hpost2_bc as [Hlb2_bc Hub2_bc].
                simpl. unfold one, one_i in *; simpl; unfold_all. lia. }
              { exact Hres_cont. } }
            { (* Case x1 ≠ x2: existing proof *)
              intros v1 cin cout Hle_cin Hbstep_ek.
              assert (Hrefl : preord_exp cenv eq_fuel eq_fuel i
                        (e_k, M.set x v' rho)
                        (e_k, M.set x v_bc (M.set x2 v2' (M.set x1 (Vfun rho_fc defs_cc f_cc) rho)))).
              { eapply preord_exp_refl. now eapply eq_fuel_compat.
                intros y Hy.
                destruct (Pos.eq_dec y x) as [-> | Hneq_x].
                - unfold preord_var_env. intros v0 Hget0.
                  rewrite M.gss in Hget0. inv Hget0.
                  eexists. split. rewrite M.gss. reflexivity.
                  eapply preord_val_monotonic. exact Hres_bc. lia.
                - unfold preord_var_env. intros v0 Hget0.
                  rewrite M.gso in Hget0 by auto.
                  destruct (Pos.eq_dec y x2) as [-> | Hneq_x2].
                  + destruct (anf_cvt_result_in_consumed _ _ _ _ _ _ _ Hcvt_e2) as [Hin_vn | Hin_S].
                    * eexists. split.
                      { rewrite M.gso by auto. rewrite M.gss. reflexivity. }
                      eapply anf_cvt_val_alpha_equiv.
                      -- eapply anf_cvt_result_in_vnames_eval;
                           [ exact Henv | exact Hnd
                           | eapply Disjoint_Included_r;
                               [eapply anf_cvt_exp_subset; exact Hcvt_e1 | exact Hdis]
                           | exact Hcvt_e2 | exact Hin_vn | exact Heval2 | exact Hget0 ].
                      -- eassumption.
                    * exfalso.
                      destruct Hdis_ek as [Hdis_ek'].
                      apply (Hdis_ek' x2). constructor.
                      { exact Hy. }
                      { constructor.
                        - constructor.
                          ++ eapply anf_cvt_exp_subset. exact Hcvt_e1. exact Hin_S.
                          ++ intros Hin_inner. inv Hin_inner.
                             eapply anf_cvt_result_not_in_output;
                               [ exact Hcvt_e2 | | assumption ].
                             eapply Disjoint_Included_r;
                               [eapply anf_cvt_exp_subset; exact Hcvt_e1 | exact Hdis].
                        - intros Hin_x. inv Hin_x. congruence. }
                  + destruct (Pos.eq_dec y x1) as [-> | Hneq_x1].
                    * destruct (anf_cvt_result_in_consumed _ _ _ _ _ _ _ Hcvt_e1) as [Hin_vn | Hin_S].
                      -- eexists. split.
                         { rewrite M.gso by auto. rewrite M.gso by auto.
                           rewrite M.gss. reflexivity. }
                         eapply anf_cvt_val_alpha_equiv.
                         ++ eapply anf_cvt_result_in_vnames_eval;
                              [ exact Henv | exact Hnd | exact Hdis
                              | exact Hcvt_e1 | exact Hin_vn | exact Heval1 | exact Hget0 ].
                         ++ eassumption.
                      -- exfalso.
                         assert (Hx1_not_S2 : ~ x1 \in S2).
                         { eapply anf_cvt_result_not_in_output; eassumption. }
                         destruct Hdis_ek as [Hdis_ek'].
                         apply (Hdis_ek' x1). constructor.
                         { exact Hy. }
                         { constructor.
                           - constructor.
                             ++ exact Hin_S.
                             ++ intros Hin_inner. inv Hin_inner.
                                apply Hx1_not_S2.
                                eapply anf_cvt_exp_subset. exact Hcvt_e2. assumption.
                           - intros Hin_x. inv Hin_x. congruence. }
                    * eexists. split.
                      -- rewrite M.gso by auto. rewrite M.gso by auto.
                         rewrite M.gso by auto. exact Hget0.
                      -- eapply preord_val_refl. tci. }
              edestruct Hrefl as (v_cont & cin_cont & cout_cont &
                Hbstep_cont & Heq_cont & Hres_cont).
              { exact Hle_cin. }
              { exact Hbstep_ek. }
              do 3 eexists. split.
              { econstructor 2. eapply BStept_letapp.
                - rewrite M.gso by auto. rewrite M.gss. reflexivity.
                - simpl. rewrite M.gss. reflexivity.
                - simpl. destruct (M.elt_eq f_cc f_cc); [reflexivity | congruence].
                - reflexivity.
                - exact Hbstep_bc.
                - exact Hbstep_cont. }
              split.
              { unfold anf_bound in Hpost_bc |- *.
                unfold eq_fuel in Heq_cont. simpl in Heq_cont, Hpost_bc.
                destruct Hpost_bc as [Hlb_bc Hub_bc].
                simpl. unfold one, one_i in *; simpl; unfold_all. lia. }
              { exact Hres_cont. } } }
        (* inclusion: comp (comp (anf_bound (f3'+2) (t3'+2)) (anf_bound f2' t2')) (anf_bound f1' t1')
                     ⊆ anf_bound (f1'+f2'+f3'+1) (t1'+t2'+t3'+2) *)
        { unfold inclusion, comp, eq_fuel, anf_bound.
          intros [[[? ?] ?] ?] [[[? ?] ?] ?].
          intros [[[[? ?] ?] ?] [[[[[? ?] ?] ?] [[? ?] [? ?]]] [? ?]]].
          unfold_all. simpl in *. split; lia. }
      + (* Divergence case *)
        intros _. eexists 0%nat. constructor 1. unfold algebra.one. simpl. lia.

    - (* 4. eval_App_step_OOT1: App_e, e1 diverges *)
      intros e1' e2' rho0 f0 t0 Hoot IH_oot.
      unfold anf_cvt_correct_exp_step.
      intros rho vnames C x S S' i Hwf Hwfe Hnd Hdis Henv Hcvt e_k Hdis_ek.
      split; [intros; congruence | intros _; eexists 0%nat; constructor 1; unfold algebra.one; simpl; lia].

    - (* 5. eval_App_step_OOT2: App_e, e2 diverges *)
      intros e1' e2' v0 rho0 f1' f2' t1' t2' Heval1 IH1 Hoot2 IH2.
      unfold anf_cvt_correct_exp_step.
      intros rho vnames C x S S' i Hwf Hwfe Hnd Hdis Henv Hcvt e_k Hdis_ek.
      split; [intros; congruence | intros _; eexists 0%nat; constructor 1; unfold algebra.one; simpl; lia].

    - (* 6. eval_Let_step: Let_e terminates *)
      intros e1' e2' v1 r0 rho0 na0 f1' f2' t1' t2' Heval1 IH1 Heval2 IH2.
      unfold anf_cvt_correct_exp_step.
      intros rho vnames C x S S' i Hwf Hwfe Hnd Hdis Henv Hcvt e_k Hdis_ek.
      inv Hcvt. fold anf_cvt_rel in *.
      (* After inv (anf_Let):
         C = comp_ctx_f C1 C2, x = x2
         Hcvt_e1 : anf_cvt_rel S e1' vnames cnstrs S2 C1 x1
         Hcvt_e2 : anf_cvt_rel S2 e2' (x1::vnames) cnstrs S' C2 x2 *)
      (* Name the hypotheses from inv *)
      match goal with
      | [ He1 : anf_cvt_rel _ e1' vnames _ _ _ _,
          He2 : anf_cvt_rel _ e2' (_ :: vnames) _ _ _ _ |- _ ] =>
        rename He1 into Hcvt_e1; rename He2 into Hcvt_e2
      end.
      rewrite <- app_ctx_f_fuse.
      split.
      + intros v v' Heq Hrel. subst r0.
        (* Get v1' with anf_val_rel v1 v1' *)
        assert (Hwfv1 : well_formed_val v1).
        { eapply (eval_env_step_preserves_wf (Hf := LambdaBoxLocal_resource_fuel)).
          exact Heval1. reflexivity. exact Hwf.
          unfold well_formed_in_env.
          replace (Datatypes.length rho0) with (Datatypes.length vnames)
            by (eapply anf_env_rel_length; eassumption).
          inversion Hwfe; subst; eassumption. }
        destruct (anf_val_rel_exists v1 Hwfv1) as [v1' Hrel1].
        (* Chain: env bridging + IH2 + IH1 via preord_exp_trans *)
        eapply preord_exp_post_monotonic.
        2:{ eapply preord_exp_trans. tci. eapply eq_fuel_idemp.
            (* IH1 for e1, with e_k' = C2|[e_k]| *)
            2:{ intros m.
                assert (Hdis_C2ek : Disjoint _ (occurs_free (C2 |[ e_k ]|)) ((S \\ S2) \\ [set x1])).
                { eapply anf_cvt_disjoint_occurs_free_ctx;
                    [ exact Hcvt_e1 | exact Hcvt_e2 | exact Hdis | exact Hdis_ek ]. }
                edestruct IH1 as [IH1_val _].
                - eassumption. (* well_formed_env *)
                - inversion Hwfe; subst; eassumption. (* exp_wf e1' *)
                - eassumption. (* NoDup *)
                - eassumption. (* Disjoint vnames S *)
                - eassumption. (* anf_env_rel *)
                - exact Hcvt_e1.
                - exact Hdis_C2ek.
                - eapply IH1_val; eauto. }
            (* env bridging + IH2 *)
            eapply preord_exp_trans. tci. eapply eq_fuel_idemp.
            (* IH2 for e2, in extended env *)
            2:{ intros m.
                assert (Hnd' : env_consistent (x1 :: vnames) (v1 :: rho0)).
                { eapply env_consistent_extend_from_cvt; [ exact Hnd | exact Hcvt_e1 | exact Hdis | exact Heval1 ]. }
                assert (Hdis' : Disjoint _ (FromList (x1 :: vnames)) S2).
                { constructor. intros z Hz. inv Hz.
                  (* H : z ∈ FromList (x1 :: vnames), H0 : z ∈ S2 *)
                  inv H.
                  - (* z = x1 (subst): x1 ∉ S2 by result_not_in_output *)
                    eapply anf_cvt_result_not_in_output; [ exact Hcvt_e1 | exact Hdis | exact H0 ].
                  - (* z ∈ FromList vnames: vnames ∩ S2 = ∅ since S2 ⊆ S and vnames ∩ S = ∅ *)
                    destruct Hdis as [Hdis''].
                    apply (Hdis'' z). constructor; [ exact H1 | ].
                    eapply (proj1 anf_cvt_rel_subset). exact Hcvt_e1. exact H0. }
                assert (Henv' : anf_env_rel (x1 :: vnames) (v1 :: rho0) (M.set x1 v1' rho)).
                { constructor.
                  - exists v1'. split. rewrite M.gss. reflexivity. exact Hrel1.
                  - eapply anf_env_rel_set; [ exact Henv | ].
                    intros k Hk.
                    destruct (anf_cvt_result_in_consumed _ _ _ _ _ _ _ Hcvt_e1) as [Hin_vn | Hin_S].
                    + (* x1 ∈ FromList vnames: same source value v1 at position k *)
                      exists v1. split.
                      * (* Use Hnd' : env_consistent (x1 :: vnames) (v1 :: rho0)
                           with positions 0 and (S k) — both have key x1 *)
                        assert (Hnd'_inst := Hnd' 0%nat (Datatypes.S k) x1 eq_refl Hk).
                        simpl in Hnd'_inst. symmetry. exact Hnd'_inst.
                      * exact Hrel1.
                    + (* x1 ∈ S: contradiction — vnames[k] = x1 but x1 ∈ S and vnames ∩ S = ∅ *)
                      exfalso. destruct Hdis as [Hdis''].
                      apply (Hdis'' x1). constructor.
                      * eapply nth_error_In. exact Hk.
                      * exact Hin_S. }
                assert (Hwfe' : exp_wf (N.of_nat (Datatypes.length (x1 :: vnames))) e2').
                { assert (Hwf_let := Hwfe). clear -Hwf_let.
                  simpl Datatypes.length.
                  replace (N.of_nat (S (Datatypes.length vnames)))
                    with (1 + N.of_nat (Datatypes.length vnames))%N by lia.
                  inversion Hwf_let; subst; assumption. }
                assert (Hdis_ek' : Disjoint _ (occurs_free e_k) ((S2 \\ S') \\ [set x])).
                { eapply Disjoint_Included_r.
                  2: eassumption.
                  intros z Hz. destruct Hz as [Hz1 Hz2].
                  constructor.
                  - constructor.
                    + eapply (anf_cvt_exp_subset _ _ _ _ _ _ _ Hcvt_e1).
                      destruct Hz1. eassumption.
                    + destruct Hz1. eassumption.
                  - eassumption. }
                edestruct IH2 as [IH2_val _].
                - constructor; assumption. (* well_formed_env (v1::rho0) *)
                - exact Hwfe'.
                - exact Hnd'.
                - exact Hdis'.
                - exact Henv'.
                - exact Hcvt_e2.
                - exact Hdis_ek'.
                - eapply IH2_val; eauto. }
            (* env bridging: M.set x2 v' rho ≤ M.set x2 v' (M.set x1 v1' rho) *)
            eapply preord_exp_refl. now eapply eq_fuel_compat.
            intros y Hy.
            destruct (Pos.eq_dec y x) as [Heq2 | Hneq2].
            * subst. intros v1x Hget.
              rewrite M.gss in Hget. inv Hget.
              eexists. split. rewrite M.gss. reflexivity.
              eapply preord_val_refl. tci.
            * intros v1x Hget. rewrite M.gso in Hget; auto.
              destruct (Pos.eq_dec y x1) as [Heq1 | Hneq1].
              -- (* y = x1: either x1 ∈ vnames (Var_e case) or x1 ∈ S (contradiction) *)
                 subst.
                 destruct (anf_cvt_result_in_consumed _ _ _ _ _ _ _ Hcvt_e1) as [Hin_vn | Hin_S].
                 ++ (* x1 ∈ vnames: use alpha-equiv *)
                    eexists. split.
                    { rewrite M.gso; auto. rewrite M.gss. reflexivity. }
                    assert (Hrel_v1x : anf_val_rel v1 v1x).
                    { eapply (anf_cvt_result_in_vnames_eval
                                S e1' vnames cnstrs S2 C1 x1 rho0 rho v1 f1' t1' v1x).
                      - exact Henv.
                      - exact Hnd.
                      - exact Hdis.
                      - exact Hcvt_e1.
                      - exact Hin_vn.
                      - exact Heval1.
                      - exact Hget. }
                    eapply anf_cvt_val_alpha_equiv; eauto.
                 ++ (* x1 ∈ S: x1 is fresh, contradiction with Hy via Hdis_ek *)
                    exfalso.
                    assert (Hx1_not_S' : ~ x1 \in S2).
                    { eapply anf_cvt_result_not_in_output; eassumption. }
                    assert (Hx1_not_S'2 : ~ x1 \in S').
                    { intro Hin. apply Hx1_not_S'.
                      eapply anf_cvt_exp_subset. exact Hcvt_e2. exact Hin. }
                    destruct Hdis_ek as [Hdis_ek'].
                    apply (Hdis_ek' x1). constructor.
                    { exact Hy. }
                    { constructor.
                      - constructor; assumption.
                      - intros Hin_x. inv Hin_x. congruence. }
              -- eexists. split.
                 { rewrite M.gso; auto. rewrite M.gso; eauto. }
                 eapply preord_val_refl. tci. }
        (* inclusion: comp eq_fuel (comp (anf_bound f2' t2') (anf_bound f1' t1'))
           ⊆ anf_bound (f1'+f2') (t1'+t2') *)
        unfold inclusion, comp, eq_fuel, anf_bound.
        intros [[[? ?] ?] ?] [[[? ?] ?] ?].
        intros [[[[? ?] ?] ?] [[[[? ?] ?] ?] [? ?]]].
        unfold_all. destruct p. destructAll. simpl in *. lia.
      + intros _. eexists 0%nat. constructor 1. unfold algebra.one. simpl. lia.

    - (* 7. eval_Let_step_OOT: Let_e, e1 diverges *)
      intros e1' e2' rho0 na0 f0 t0 Hoot IH_oot.
      unfold anf_cvt_correct_exp_step.
      intros rho vnames C x S S' i Hwf Hwfe Hnd Hdis Henv Hcvt e_k Hdis_ek.
      split; [intros; congruence | intros _; eexists 0%nat; constructor 1; unfold algebra.one; simpl; lia].

    - (* 8. eval_FixApp_step: App_e with ClosFix_v *)
      intros e1' e2' e_body rho0 rho_fix rho_rec n0 na0 fnlst0 v2 r0 f1' f2' f3' t1' t2' t3'
             Heval1 IH1 Hnth Hrec Heval2 IH2 Heval3 IH3.
      unfold anf_cvt_correct_exp_step.
      intros rho vnames C x S S' i Hwf Hwfe Hnd Hdis Henv Hcvt e_k Hdis_ek.
      inv Hcvt. fold anf_cvt_rel in *.
      match goal with
      | [ He1 : anf_cvt_rel _ e1' vnames _ _ _ _,
          He2 : anf_cvt_rel _ e2' vnames _ _ _ _,
          Hr : x \in _ |- _ ] =>
        rename He1 into Hcvt_e1; rename He2 into Hcvt_e2; rename Hr into Hr_in
      end.
      rewrite <- !app_ctx_f_fuse.
      split.
      + (* Termination case *)
        intros v v' Heq Hrel. subst r0.
        assert (Hwf_fix : well_formed_val (ClosFix_v rho_fix fnlst0 n0)).
        { eapply (eval_env_step_preserves_wf (Hf := LambdaBoxLocal_resource_fuel)).
          exact Heval1. reflexivity. exact Hwf.
          unfold well_formed_in_env.
          replace (Datatypes.length rho0) with (Datatypes.length vnames)
            by (eapply anf_env_rel_length; eassumption).
          inversion Hwfe; subst; eassumption. }
        destruct (anf_val_rel_exists _ Hwf_fix) as [fix_v' Hrel_fix].
        assert (Hwf_v2 : well_formed_val v2).
        { eapply (eval_env_step_preserves_wf (Hf := LambdaBoxLocal_resource_fuel)).
          exact Heval2. reflexivity. exact Hwf.
          unfold well_formed_in_env.
          replace (Datatypes.length rho0) with (Datatypes.length vnames)
            by (eapply anf_env_rel_length; eassumption).
          inversion Hwfe; subst; eassumption. }
        destruct (anf_val_rel_exists _ Hwf_v2) as [v2' Hrel_v2].
        (* Chain: IH1 + IH2 + Eletapp reduction + IH3 *)
        eapply preord_exp_post_monotonic.
        2:{ eapply preord_exp_trans. tci. eapply eq_fuel_idemp.
            (* IH1: C1 layer *)
            2:{ intros m.
                assert (Hdis_C2ek : Disjoint _ (occurs_free (C2 |[ Eletapp x x1 func_tag [x2] e_k ]|))
                                               ((S \\ S2) \\ [set x1])).
                { eapply anf_cvt_disjoint_occurs_free_ctx_app;
                    [ exact Hcvt_e1 | exact Hcvt_e2 | exact Hr_in | exact Hdis | exact Hdis_ek ]. }
                edestruct IH1 as [IH1_val _].
                - eassumption.
                - inversion Hwfe; subst; eassumption.
                - eassumption.
                - eassumption.
                - eassumption.
                - exact Hcvt_e1.
                - exact Hdis_C2ek.
                - eapply IH1_val; eauto. }
            eapply preord_exp_trans with (P1 := anf_bound (f3' + 2) (t3' + 2)).
            tci. eapply eq_fuel_idemp.
            (* IH2: C2 layer *)
            2:{ intros m.
                assert (Hnd_x1 : env_consistent (x1 :: vnames) (ClosFix_v rho_fix fnlst0 n0 :: rho0)).
                { eapply env_consistent_extend_from_cvt;
                    [ exact Hnd | exact Hcvt_e1 | exact Hdis | exact Heval1 ]. }
                assert (Henv_x1 : anf_env_rel vnames rho0 (M.set x1 fix_v' rho)).
                { eapply anf_env_rel_set; [ exact Henv | ].
                  intros k Hk.
                  destruct (anf_cvt_result_in_consumed _ _ _ _ _ _ _ Hcvt_e1) as [Hin_vn | Hin_S].
                  - exists (ClosFix_v rho_fix fnlst0 n0). split.
                    + assert (Hnd_inst := Hnd_x1 0%nat (Datatypes.S k) x1 eq_refl Hk).
                      simpl in Hnd_inst. symmetry. exact Hnd_inst.
                    + exact Hrel_fix.
                  - exfalso. destruct Hdis as [Hdis''].
                    apply (Hdis'' x1). constructor.
                    + eapply nth_error_In. exact Hk.
                    + exact Hin_S. }
                assert (Hdis_letapp : Disjoint _ (occurs_free (Eletapp x x1 func_tag [x2] e_k))
                                                 ((S2 \\ S3) \\ [set x2])).
                { eapply anf_cvt_disjoint_eletapp;
                    [ exact Hcvt_e1 | exact Hcvt_e2 | exact Hr_in | exact Hdis | exact Hdis_ek ]. }
                edestruct IH2 as [IH2_val _].
                - eassumption.
                - inversion Hwfe; subst; eassumption.
                - eassumption.
                - eapply Disjoint_Included_r; [eapply (proj1 anf_cvt_rel_subset); exact Hcvt_e1 | exact Hdis].
                - exact Henv_x1.
                - exact Hcvt_e2.
                - exact Hdis_letapp.
                - eapply IH2_val; eauto. }
            (* Eletapp reduction + IH3 for body *)
            (* Step 1: Extract fix closure structure from Hrel_fix *)
            assert (Hfix_inv :
              exists rho_fc names_fc fnames_fc Bs_fix f_fc S1_fc S2_fc,
                fix_v' = Vfun rho_fc Bs_fix f_fc /\
                anf_env_rel' anf_val_rel names_fc rho_fix rho_fc /\
                env_consistent names_fc rho_fix /\
                NoDup fnames_fc /\
                Disjoint _ (FromList names_fc :|: FromList fnames_fc) S1_fc /\
                Disjoint _ (FromList names_fc) (FromList fnames_fc) /\
                nth_error fnames_fc (N.to_nat n0) = Some f_fc /\
                anf_fix_rel fnames_fc names_fc S1_fc fnames_fc fnlst0 Bs_fix S2_fc).
            { inversion Hrel_fix; try discriminate; subst.
              do 7 eexists.
              split; [reflexivity | ].
              repeat (split; [eassumption | ]).
              eassumption. }
            destruct Hfix_inv as (rho_fc & names_fc & fnames_fc & Bs_fix & f_fc &
              S1_fc & S2_fc & Hfix_eq & Henv_fc & Hnd_names & Hnd_fnames &
              Hdis_fix & Hdis_nf & Hnth_fix & Hfix_rel).
            subst fix_v'.
            (* Get specific function from the fix bundle *)
            edestruct (anf_fix_rel_find_def_ext _ _ _ _ _ _ _ _ _ _ _ Hfix_rel Hnth_fix Hnth Hnd_fnames)
              as (x_pc & C_bc & r_bc & S_body1 & S_body2 & Hfind_fc & Hcvt_bc & Hdis_body & Hxpc_fresh).
            set (rho_bc := M.set x_pc v2' (def_funs Bs_fix Bs_fix rho_fc rho_fc)).
            (* Step 2: Body environment relation *)
            assert (Henv_bc : anf_env_rel (x_pc :: List.rev fnames_fc ++ names_fc)
                                          (v2 :: make_rec_env_rev_order fnlst0 rho_fix) rho_bc).
            { unfold rho_bc. apply anf_env_rel_extend_weaken.
              - eapply anf_env_rel_extend_fundefs; eassumption.
              - exact Hrel_v2.
              - intro Hc. apply Hxpc_fresh.
                rewrite FromList_app, FromList_rev in Hc. exact Hc. }
            (* Step 3: Apply IH3 to get body correctness *)
            assert (IH3_full :
              (forall v0 v'0, Val v = Val v0 -> anf_val_rel v0 v'0 ->
               preord_exp cenv (anf_bound f3' t3') eq_fuel (i + 1)%nat
                          (Ehalt r_bc, M.set r_bc v'0 rho_bc)
                          (C_bc |[ Ehalt r_bc ]|, rho_bc)) /\
              (Val v = fuel_sem.OOT ->
               exists c, bstep_fuel cenv rho_bc (C_bc |[ Ehalt r_bc ]|) c eval.OOT tt)).
            { eapply IH3 with (vnames := x_pc :: List.rev fnames_fc ++ names_fc).
              - (* well_formed_env (v2 :: make_rec_env_rev_order fnlst0 rho_fix) *)
                constructor.
                + exact Hwf_v2.
                + inversion Hwf_fix.
                  eapply well_formed_envmake_rec_env_rev_order;
                    [reflexivity | assumption | assumption].
              - (* exp_wf (N.of_nat (length (x_pc :: rev fnames_fc ++ names_fc))) e_body *)
                assert (Hwf_body_lam :
                  exp_wf (efnlst_length fnlst0 + N.of_nat (Datatypes.length rho_fix))
                         (Lam_e na0 e_body)).
                { eapply (enthopt_inlist_Forall
                    (fun e => isLambda e /\
                       exp_wf (efnlst_length fnlst0 + N.of_nat (Datatypes.length rho_fix)) e)
                    fnlst0 n0).
                  - inv Hwf_fix. assumption.
                  - exact Hnth. }
                assert (Hlen_eq :
                  N.of_nat (Datatypes.length (x_pc :: rev fnames_fc ++ names_fc)) =
                  efnlst_length fnlst0 + N.of_nat (Datatypes.length rho_fix) + 1).
                { simpl Datatypes.length.
                  rewrite length_app, length_rev.
                  erewrite anf_fix_rel_fnames_length; [ | exact Hfix_rel].
                  erewrite <- Forall2_length; [ | exact Henv_fc].
                  rewrite Nnat.Nat2N.inj_succ, <- OrdersEx.N_as_OT.add_1_l,
                          Nnat.Nat2N.inj_add, efnlength_efnlst_length. lia. }
                rewrite Hlen_eq. inversion Hwf_body_lam. subst.
                replace (efnlst_length fnlst0 + N.of_nat (length rho_fix) + 1) with
                (1 + (efnlst_length fnlst0 + N.of_nat (length rho_fix))) by lia. assumption.
              - (* env_consistent (x_pc :: rev fnames_fc ++ names_fc)
                                  (v2 :: make_rec_env_rev_order fnlst0 rho_fix) *)
                apply env_consistent_extend.
                + destruct (make_rec_env_rev_order_app fnlst0 rho_fix)
                    as [closfix_vals [Hdecomp [Hlen_cf _]]].
                  rewrite Hdecomp.
                  eapply env_consistent_app.
                  * apply NoDup_env_consistent. apply NoDup_rev. exact Hnd_fnames.
                  * exact Hnd_names.
                  * rewrite FromList_rev. apply Disjoint_sym. exact Hdis_nf.
                  * rewrite length_rev.
                    erewrite anf_fix_rel_fnames_length; [ | exact Hfix_rel].
                    symmetry. exact Hlen_cf.
                + intros k Hk. exfalso. apply Hxpc_fresh.
                  apply nth_error_In in Hk. apply in_app_or in Hk.
                  destruct Hk as [Hk | Hk].
                  * constructor. apply in_rev in Hk. exact Hk.
                  * constructor 2. exact Hk.
              - (* Disjoint (FromList (x_pc :: rev fnames_fc ++ names_fc)) S_body1 *)
                repeat normalize_sets. rewrite FromList_rev. exact Hdis_body.
              - exact Henv_bc.
              - exact Hcvt_bc.
              - (* Disjoint (occurs_free (Ehalt r_bc)) ((S_body1 \\ S_body2) \\ [set r_bc]) *)
                constructor. intros z Hz. inv Hz.
                inversion H; subst.
                destruct H0 as [_ Habs]. apply Habs. constructor. }
            destruct IH3_full as [IH3_val _].
            specialize (IH3_val v v' eq_refl Hrel).
            (* Step 4: Build Ehalt bstep_fuel *)
            assert (Hle_h : (to_nat 1%nat <= i + 1)%nat) by (simpl; lia).
            assert (Hehalt : @bstep_fuel cenv nat fuel_res unit trace_res
                                         (M.set r_bc v' rho_bc) (Ehalt r_bc) 1%nat (Res v') tt).
            { pose proof (BStepf_run cenv (M.set r_bc v' rho_bc) (Ehalt r_bc) (Res v') 0%nat tt
                (BStept_halt cenv r_bc v' (M.set r_bc v' rho_bc) (M.gss r_bc v' rho_bc))) as Hbsf.
              simpl in Hbsf. exact Hbsf. }
            destruct (IH3_val (Res v') 1%nat tt Hle_h Hehalt)
              as (v_body_res & cin_bc & cout_bc & Hbstep_bc & Hpost_bc & Hres_bc).
            (* Body result must be Res (not OOT) *)
            destruct v_body_res as [ | v_bc ].
            { simpl in Hres_bc. contradiction. }
            simpl in Hres_bc.
            (* Case split on whether x1 = x2 *)
            destruct (Pos.eq_dec x1 x2) as [Heq_x12 | Hneq_x12].
            { (* Case x1 = x2 *)
              subst x2.
              assert (Hx1_in_vn : x1 \in FromList vnames).
              { destruct (anf_cvt_result_in_consumed _ _ _ _ _ _ _ Hcvt_e2) as [Hin | Hin].
                - exact Hin.
                - exfalso. eapply anf_cvt_result_not_in_output.
                  exact Hcvt_e1. exact Hdis. exact Hin. }
              assert (Hx1_list : List.In x1 vnames) by exact Hx1_in_vn.
              apply In_nth_error in Hx1_list. destruct Hx1_list as [k0 Hk0].
              destruct (Forall2_nth_error_r _ _ _ _ _ Henv Hk0)
                as [v_src_k [Hk0_vs [v_rho [Hget_rho Hrel_rho]]]].
              assert (Hpv_cv : forall j, preord_val cenv eq_fuel j
                        (Vfun rho_fc Bs_fix f_fc) v2').
              { intro j. eapply preord_val_trans. tci. eapply eq_fuel_idemp.
                - eapply anf_cvt_val_alpha_equiv. exact Hrel_fix.
                  eapply anf_cvt_result_in_vnames_eval;
                    [ exact Henv | exact Hnd | exact Hdis
                    | exact Hcvt_e1 | exact Hx1_in_vn | exact Heval1 | exact Hget_rho ].
                - intros m0. eapply anf_cvt_val_alpha_equiv.
                  eapply anf_cvt_result_in_vnames_eval;
                    [ exact Henv | exact Hnd
                    | eapply Disjoint_Included_r;
                        [eapply anf_cvt_exp_subset; exact Hcvt_e1 | exact Hdis]
                    | exact Hcvt_e2 | exact Hx1_in_vn | exact Heval2 | exact Hget_rho ].
                  exact Hrel_v2. }
              assert (Hpv_inst := Hpv_cv (cin_bc + i + 1)%nat).
              rewrite preord_val_eq in Hpv_inst.
              destruct v2' as [ | rho2_fc B2 f2 | | ];
                try (simpl in Hpv_inst; contradiction).
              assert (Hset_fc : Some rho_bc = set_lists [x_pc]
                [Vfun rho2_fc B2 f2] (def_funs Bs_fix Bs_fix rho_fc rho_fc)).
              { unfold rho_bc. reflexivity. }
              edestruct Hpv_inst as (xs2_pc & e2_body & rho2_body &
                Hfind_v2 & Hset_v2 & Hbody_preord).
              { reflexivity. }
              { exact Hfind_fc. }
              { exact Hset_fc. }
              assert (Hbody_pe : preord_exp' cenv (preord_val cenv) eq_fuel eq_fuel
                        (cin_bc + i)%nat
                        (C_bc |[ Ehalt r_bc ]|, rho_bc) (e2_body, rho2_body)).
              { apply Hbody_preord. lia.
                constructor; [ | constructor ].
                eapply preord_val_refl. tci. }
              destruct (Hbody_pe (Res v_bc) cin_bc cout_bc) as
                (v2_body_res & cin2_bc & cout2_bc & Hbstep2_bc & Hpost2_bc & Hres2_bc).
              { simpl. lia. }
              { exact Hbstep_bc. }
              destruct v2_body_res as [ | v2_bc ].
              { simpl in Hres2_bc. contradiction. }
              simpl in Hres2_bc.
              (* Establish forall m', preord_val m' v_bc v2_bc
                 using Hpv_cv at varying indices + bstep determinism *)
              assert (Hpv_all : forall m', preord_val cenv eq_fuel m' v_bc v2_bc).
              { intro m'.
                pose proof (Hpv_cv (cin_bc + m' + 1)%nat) as Hpv_m.
                rewrite preord_val_eq in Hpv_m.
                edestruct Hpv_m as (xs2_m & e2_m & rho2_m &
                  Hfind_m & Hset_m & Hbp_m).
                { reflexivity. }
                { exact Hfind_fc. }
                { exact Hset_fc. }
                replace e2_m with e2_body in * by congruence.
                replace xs2_m with xs2_pc in * by congruence.
                replace rho2_m with rho2_body in *.
                2:{ congruence. }
                assert (Hba_m : preord_exp' cenv (preord_val cenv) eq_fuel eq_fuel
                          (cin_bc + m')%nat
                          (C_bc |[ Ehalt r_bc ]|, rho_bc) (e2_body, rho2_body)).
                { apply Hbp_m. lia.
                  constructor; [ | constructor ].
                  eapply preord_val_refl. tci. }
                destruct (Hba_m (Res v_bc) cin_bc cout_bc) as
                  (v2_m & cin2_m & cout2_m & Hbs2_m & _ & Hres2_m).
                { simpl. lia. }
                { exact Hbstep_bc. }
                destruct v2_m as [ | v2_m_val ].
                { simpl in Hres2_m. contradiction. }
                simpl in Hres2_m.
                eapply bstep_fuel_deterministic in Hbs2_m.
                2:{ exact Hbstep2_bc. }
                destruct Hbs2_m as [Hv_eq [_ _]]. subst v2_m_val.
                replace (cin_bc + m' - cin_bc)%nat with m' in Hres2_m
                  by lia.
                exact Hres2_m. }
              (* preord_val i v' v2_bc via transitivity *)
              assert (Hpv_direct : preord_val cenv eq_fuel i v' v2_bc).
              { eapply preord_val_trans. tci. eapply eq_fuel_idemp.
                - eapply preord_val_monotonic. exact Hres_bc. lia.
                - exact Hpv_all. }
              intros v1 cin cout Hle_cin Hbstep_ek.
              assert (Hx_neq_x1 : x <> x1).
              { intro Heq. subst x.
                destruct Hdis as [Hdis']. apply (Hdis' x1).
                constructor.
                - exact Hx1_in_vn.
                - eapply anf_cvt_exp_subset. exact Hcvt_e1.
                  eapply anf_cvt_exp_subset. exact Hcvt_e2.
                  exact Hr_in. }
              assert (Hrefl : preord_exp cenv eq_fuel eq_fuel i
                        (e_k, M.set x v' rho)
                        (e_k, M.set x v2_bc
                          (M.set x1 (Vfun rho2_fc B2 f2)
                            (M.set x1 (Vfun rho_fc Bs_fix f_fc) rho)))).
              { eapply preord_exp_refl. now eapply eq_fuel_compat.
                intros y Hy.
                destruct (Pos.eq_dec y x) as [-> | Hneq_x].
                - unfold preord_var_env. intros v0 Hget0.
                  rewrite M.gss in Hget0. inv Hget0.
                  eexists. split. rewrite M.gss. reflexivity.
                  exact Hpv_direct.
                - unfold preord_var_env. intros v0 Hget0.
                  rewrite M.gso in Hget0 by auto.
                  destruct (Pos.eq_dec y x1) as [-> | Hneq_x1].
                  + eexists. split.
                    { rewrite M.gso by auto. rewrite M.gss. reflexivity. }
                    eapply anf_cvt_val_alpha_equiv.
                    * eapply anf_cvt_result_in_vnames_eval;
                        [ exact Henv | exact Hnd
                        | eapply Disjoint_Included_r;
                            [eapply anf_cvt_exp_subset; exact Hcvt_e1 | exact Hdis]
                        | exact Hcvt_e2 | exact Hx1_in_vn | exact Heval2 | exact Hget0 ].
                    * exact Hrel_v2.
                  + eexists. split.
                    { rewrite M.gso by auto. rewrite M.gso by auto.
                      rewrite M.gso by auto. exact Hget0. }
                    eapply preord_val_refl. tci. }
              edestruct Hrefl as (v_cont & cin_cont & cout_cont &
                Hbstep_cont & Heq_cont & Hres_cont).
              { exact Hle_cin. }
              { exact Hbstep_ek. }
              do 3 eexists. split.
              { econstructor 2. eapply BStept_letapp.
                - rewrite M.gss. reflexivity.
                - simpl. rewrite M.gss. reflexivity.
                - exact Hfind_v2.
                - symmetry. exact Hset_v2.
                - exact Hbstep2_bc.
                - exact Hbstep_cont. }
              split.
              { unfold anf_bound in Hpost_bc, Hpost2_bc |- *.
                unfold eq_fuel in Heq_cont, Hpost2_bc. simpl in Heq_cont, Hpost_bc, Hpost2_bc.
                destruct Hpost_bc as [Hlb_bc Hub_bc].
                destruct Hpost2_bc as [Hlb2_bc Hub2_bc].
                simpl. unfold one, one_i in *; simpl; unfold_all. lia. }
              { exact Hres_cont. } }
            { (* Case x1 ≠ x2 *)
              intros v1 cin cout Hle_cin Hbstep_ek.
              assert (Hrefl : preord_exp cenv eq_fuel eq_fuel i
                        (e_k, M.set x v' rho)
                        (e_k, M.set x v_bc (M.set x2 v2' (M.set x1 (Vfun rho_fc Bs_fix f_fc) rho)))).
              { eapply preord_exp_refl. now eapply eq_fuel_compat.
                intros y Hy.
                destruct (Pos.eq_dec y x) as [-> | Hneq_x].
                - unfold preord_var_env. intros v0 Hget0.
                  rewrite M.gss in Hget0. inv Hget0.
                  eexists. split. rewrite M.gss. reflexivity.
                  eapply preord_val_monotonic. exact Hres_bc. lia.
                - unfold preord_var_env. intros v0 Hget0.
                  rewrite M.gso in Hget0 by auto.
                  destruct (Pos.eq_dec y x2) as [-> | Hneq_x2].
                  + destruct (anf_cvt_result_in_consumed _ _ _ _ _ _ _ Hcvt_e2) as [Hin_vn | Hin_S].
                    * eexists. split.
                      { rewrite M.gso by auto. rewrite M.gss. reflexivity. }
                      eapply anf_cvt_val_alpha_equiv.
                      -- eapply anf_cvt_result_in_vnames_eval;
                           [ exact Henv | exact Hnd
                           | eapply Disjoint_Included_r;
                               [eapply anf_cvt_exp_subset; exact Hcvt_e1 | exact Hdis]
                           | exact Hcvt_e2 | exact Hin_vn | exact Heval2 | exact Hget0 ].
                      -- eassumption.
                    * exfalso.
                      destruct Hdis_ek as [Hdis_ek'].
                      apply (Hdis_ek' x2). constructor.
                      { exact Hy. }
                      { constructor.
                        - constructor.
                          ++ eapply anf_cvt_exp_subset. exact Hcvt_e1. exact Hin_S.
                          ++ intros Hin_inner. inv Hin_inner.
                             eapply anf_cvt_result_not_in_output;
                               [ exact Hcvt_e2 | | assumption ].
                             eapply Disjoint_Included_r;
                               [eapply anf_cvt_exp_subset; exact Hcvt_e1 | exact Hdis].
                        - intros Hin_x. inv Hin_x. congruence. }
                  + destruct (Pos.eq_dec y x1) as [-> | Hneq_x1].
                    * destruct (anf_cvt_result_in_consumed _ _ _ _ _ _ _ Hcvt_e1) as [Hin_vn | Hin_S].
                      -- eexists. split.
                         { rewrite M.gso by auto. rewrite M.gso by auto.
                           rewrite M.gss. reflexivity. }
                         eapply anf_cvt_val_alpha_equiv.
                         ++ eapply anf_cvt_result_in_vnames_eval;
                              [ exact Henv | exact Hnd | exact Hdis
                              | exact Hcvt_e1 | exact Hin_vn | exact Heval1 | exact Hget0 ].
                         ++ eassumption.
                      -- exfalso.
                         assert (Hx1_not_S2 : ~ x1 \in S2).
                         { eapply anf_cvt_result_not_in_output; eassumption. }
                         destruct Hdis_ek as [Hdis_ek'].
                         apply (Hdis_ek' x1). constructor.
                         { exact Hy. }
                         { constructor.
                           - constructor.
                             ++ exact Hin_S.
                             ++ intros Hin_inner. inv Hin_inner.
                                apply Hx1_not_S2.
                                eapply anf_cvt_exp_subset. exact Hcvt_e2. assumption.
                           - intros Hin_x. inv Hin_x. congruence. }
                    * eexists. split.
                      -- rewrite M.gso by auto. rewrite M.gso by auto.
                         rewrite M.gso by auto. exact Hget0.
                      -- eapply preord_val_refl. tci. }
              edestruct Hrefl as (v_cont & cin_cont & cout_cont &
                Hbstep_cont & Heq_cont & Hres_cont).
              { exact Hle_cin. }
              { exact Hbstep_ek. }
              do 3 eexists. split.
              { econstructor 2. eapply BStept_letapp.
                - rewrite M.gso by auto. rewrite M.gss. reflexivity.
                - simpl. rewrite M.gss. reflexivity.
                - exact Hfind_fc.
                - reflexivity.
                - exact Hbstep_bc.
                - exact Hbstep_cont. }
              split.
              { unfold anf_bound in Hpost_bc |- *.
                unfold eq_fuel in Heq_cont. simpl in Heq_cont, Hpost_bc.
                destruct Hpost_bc as [Hlb_bc Hub_bc].
                simpl. unfold one, one_i in *; simpl; unfold_all. lia. }
              { exact Hres_cont. } } }
        (* inclusion: comp (comp (anf_bound (f3'+2) (t3'+2)) (anf_bound f2' t2')) (anf_bound f1' t1')
                     ⊆ anf_bound (f1'+f2'+f3'+1) (t1'+t2'+t3'+2) *)
        { unfold inclusion, comp, eq_fuel, anf_bound.
          intros [[[? ?] ?] ?] [[[? ?] ?] ?].
          intros [[[[? ?] ?] ?] [[[[[? ?] ?] ?] [[? ?] [? ?]]] [? ?]]].
          unfold_all. simpl in *. split; lia. }
      + intros _. eexists 0%nat. constructor 1. unfold algebra.one. simpl. lia.

    - (* 9. eval_Match_step: Match_e terminates *)
      intros e1' e_br rho0 dc0 vs_con n0 brnchs0 r0 f1' f2' t1' t2' Heval1 IH1 Hfind Heval2 IH2.
      unfold anf_cvt_correct_exp_step.
      intros rho vnames C x S S' i Hwf Hwfe Hnd Hdis Henv Hcvt e_k Hdis_ek.
      inv Hcvt. fold anf_cvt_rel in *. fold anf_cvt_rel_branches in *.
      (* After inversion of anf_Match:
         f \in S, y \in S \ {f}
         Hcvt_e1 : anf_cvt_rel (S \ {f} \ {y}) e1' vnames cnstrs S2 C1 x1
         Hcvt_brs : anf_cvt_rel_branches S2 brnchs0 vnames y cnstrs S3 pats
         x \in S3, S' = S3 \ {x}
         Target: Efun (Fcons f func_tag [y] (Ecase y pats) Fnil)
                      (C1 |[ Eletapp x f func_tag [x1] e_k ]|) *)
      match goal with
      | [ He1 : anf_cvt_rel _ e1' vnames _ _ _ _,
          Hbrs : anf_cvt_rel_branches _ brnchs0 vnames _ _ _ _ |- _ ] =>
        rename He1 into Hcvt_e1; rename Hbrs into Hcvt_brs
      end.
      split.
      + (* Termination case *)
        intros v v' Heq Hrel. subst r0.
        (* Well-formedness of constructor value *)
        assert (Hwf_con : well_formed_val (Con_v dc0 vs_con)).
        { eapply (eval_env_step_preserves_wf (Hf := LambdaBoxLocal_resource_fuel)).
          exact Heval1. reflexivity. exact Hwf.
          unfold well_formed_in_env.
          replace (Datatypes.length rho0) with (Datatypes.length vnames)
            by (eapply anf_env_rel_length; eassumption).
          inversion Hwfe; subst; eassumption. }
        destruct (anf_val_rel_exists _ Hwf_con) as [con_v' Hrel_con].
        (* Subset from scrutinee conversion *)
        assert (HS2 : S2 \subset S \\ [set f] \\ [set y]).
        { eapply anf_cvt_exp_subset. eassumption. }
        (* Extract constructor shape early — needed for Hbody *)
        assert (Hcon_shape : exists c_tag vs_anf,
          con_v' = Vconstr c_tag vs_anf /\
          dcon_to_tag default_tag dc0 cnstrs = c_tag /\
          Forall2 anf_val_rel vs_con vs_anf).
        { inv Hrel_con. eexists _, _. eauto. }
        destruct Hcon_shape as (c_tag & vs_anf & Hcon_eq & Htag_eq & Hvs_rel).
        subst con_v'.
        (* Extract branch data from the branches conversion *)
        edestruct (anf_cvt_rel_branches_find_branch
                     S2 brnchs0 vnames y S3 pats dc0 e_br
                     (dcon_to_tag default_tag dc0 cnstrs)
                     (N.of_nat (Datatypes.length vs_con)))
          as (vars & S_mid & S_out & C_br & r_br & ctx_p_br & m_br &
              Hvars_sub & Hvars_len & Hvars_nd & Hctx_p & Hfind_tag & Hcvt_br & HS_mid_sub).
        { exact Hcvt_brs. }
        { exact Hfind. }
        { reflexivity. }
        set (n_vars := List.length vars).
        assert (Hn_le : (n_vars <= max_m_branches brnchs0)%nat).
        { unfold n_vars. rewrite Hvars_len.
          eapply find_branch_max_m_branches. exact Hfind. }
        (* The target expression unfolds as:
             Efun (Fcons f func_tag [y] (Ecase y pats) Fnil)
                  (C1 |[ Eletapp x f func_tag [x1] e_k ]|) *)
        simpl app_ctx_f. rewrite <- app_ctx_f_fuse.
        set (defs := Fcons f func_tag [y] (Ecase y pats) Fnil).
        set (rho_efun := def_funs defs defs rho rho).
        set (rho_match := M.set y (Vconstr c_tag vs_anf) rho_efun).
        (* Assert projection bindings succeed *)
        assert (Hset_proj : exists rho_proj,
          set_lists (rev vars) vs_anf rho_match = Some rho_proj).
        { eapply set_lists_length3. rewrite length_rev.
          rewrite Hvars_len. rewrite Nnat.Nat2N.id.
          eapply Forall2_length. exact Hvs_rel. }
        destruct Hset_proj as [rho_proj Hset_proj].
        (* Main proof: compose three reduction steps *)
        eapply preord_exp_post_monotonic with
          (P1 := comp (comp (anf_bound (f2' + n_vars + 3) (t2' + n_vars + 3))
                            (anf_bound f1' t1'))
                      one_step).
        2:{ eapply preord_exp_trans. tci. eapply eq_fuel_idemp.
            (* Step 1: Efun_red — defines match function f *)
            2:{ intros m. eapply preord_exp_Efun_red. }
            eapply preord_exp_trans. tci. eapply eq_fuel_idemp.
            (* Step 2: IH1 — evaluates scrutinee through C1, binds x1 *)
            2:{ intros m.
                assert (Hdis_ek_IH : Disjoint _
                  (occurs_free (Eletapp x f func_tag [x1] e_k))
                  (((S \\ [set f] \\ [set y]) \\ S2) \\ [set x1])).
                { eapply anf_cvt_disjoint_eletapp_match; eassumption. }
                assert (Henv_efun : anf_env_rel vnames rho0 rho_efun).
                { unfold rho_efun. simpl def_funs.
                  apply anf_env_rel_weaken; [ exact Henv | ].
                  intro Hc. destruct Hdis as [Hdis''].
                  eapply (Hdis'' f). constructor; eauto. }
                assert (Hdis_efun : Disjoint _ (FromList vnames) (S \\ [set f] \\ [set y])).
                { eapply Disjoint_Included_r.
                  eapply Included_trans; eapply Setminus_Included.
                  exact Hdis. }
                edestruct IH1 as [IH1_val _].
                - exact Hwf.
                - inversion Hwfe; subst; eassumption.
                - exact Hnd.
                - exact Hdis_efun.
                - exact Henv_efun.
                - exact Hcvt_e1.
                - exact Hdis_ek_IH.
                - eapply IH1_val; eauto. }

            (* Step 3: Eletapp — compositional Ecase body proof *)
            intros v1 cin cout Hle_cin Hbstep_ek.

            (* == Compositionally build Ecase body preord_exp == *)
            (* Use index i+1 so that after Ehalt (1 step), preord_val is at i *)
            (* Compose: IH2 → ctx_bind_proj → Ecase_red *)
            assert (Hpre_ecase : preord_exp cenv
              (comp (comp (anf_bound f2' t2') (eq_fuel_n n_vars)) one_step)
              eq_fuel (i + 1)%nat
              (Ehalt r_br, M.set r_br v' rho_proj)
              (Ecase y pats, rho_match)).
            { eapply preord_exp_trans. tci. eapply eq_fuel_idemp.
              (* Ecase_red: case dispatch *)
              2:{ intros m'. eapply preord_exp_Ecase_red.
                  - unfold rho_match. rewrite M.gss. reflexivity.
                  - rewrite <- Htag_eq. exact Hfind_tag. }
              eapply preord_exp_trans. tci. eapply eq_fuel_idemp.
              (* ctx_bind_proj: bind constructor fields via projections *)
              2:{ intros m'. eapply ctx_bind_proj_preord_exp with (vs' := []).
                  - reflexivity.
                  - intro Hy_in_vars.
                    apply Hvars_sub in Hy_in_vars. apply HS_mid_sub in Hy_in_vars.
                    apply HS2 in Hy_in_vars.
                    destruct Hy_in_vars as [_ Habs]. apply Habs. constructor.
                  - subst ctx_p_br. unfold n_vars. reflexivity.
                  - unfold rho_match. rewrite M.gss. rewrite <- Htag_eq. rewrite app_nil_r. reflexivity.
                  - exact Hset_proj. }
              (* IH2: branch body evaluation *)
              intros m'.
              edestruct IH2 as [IH2_val _]; [ | | | | | exact Hcvt_br | | eapply IH2_val; eauto ].
              - (* well_formed_env (List.rev vs_con ++ rho0) *)
                eapply Forall_app. split.
                + eapply Forall_rev. inv Hwf_con. assumption.
                + exact Hwf.
              - (* exp_wf (N.of_nat (length (vars ++ vnames))) e_br *)
                rewrite length_app, Nnat.Nat2N.inj_add, Hvars_len, Nnat.Nat2N.id.
                eapply find_branch_preserves_wf; [ | exact Hfind ].
                inversion Hwfe; eassumption.
              - (* env_consistent (vars ++ vnames) (List.rev vs_con ++ rho0) *)
                eapply env_consistent_app.
                + eapply NoDup_env_consistent. exact Hvars_nd.
                + exact Hnd.
                + apply Disjoint_sym.
                  eapply Disjoint_Included_r; [ | exact Hdis ].
                  intros z Hz. apply Hvars_sub in Hz. apply HS_mid_sub in Hz.
                  apply HS2 in Hz. inv Hz. inv H. exact H1.
                + rewrite length_rev. rewrite Hvars_len. rewrite Nnat.Nat2N.id. reflexivity.
              - (* Disjoint (FromList (vars ++ vnames)) (S_mid \\ FromList vars) *)
                rewrite FromList_app. apply Union_Disjoint_l.
                + apply Disjoint_Setminus_r. apply Included_refl.
                + eapply Disjoint_Included_r; [ | exact Hdis ].
                  eapply Included_trans; [ eapply Setminus_Included | ].
                  eapply Included_trans. exact HS_mid_sub.
                  eapply Included_trans. exact HS2.
                  eapply Included_trans; eapply Setminus_Included.
              - (* anf_env_rel (vars ++ vnames) (List.rev vs_con ++ rho0) rho_proj *)
                eapply anf_env_rel_extend_weaken_setlists_rev.
                + (* anf_env_rel vnames rho0 rho_match *)
                  unfold rho_match. apply anf_env_rel_weaken.
                  * unfold rho_efun. simpl def_funs.
                    apply anf_env_rel_weaken; [ exact Henv | ].
                    intro Hc. destruct Hdis as [Hdis'].
                    apply (Hdis' f). constructor; eauto.
                  * intro Hc. destruct Hdis as [Hdis'].
                    apply (Hdis' y). constructor; [ exact Hc | ].
                    match goal with
                    | [ H : y \in S \\ _ |- _ ] =>
                      destruct H as [Hy _]; exact Hy
                    end.
                + exact Hset_proj.
                + exact Hvs_rel.
                + (* Disjoint (FromList vars) (FromList vnames) *)
                  apply Disjoint_sym.
                  eapply Disjoint_Included_r; [ | exact Hdis ].
                  intros z Hz. apply Hvars_sub in Hz. apply HS_mid_sub in Hz.
                  apply HS2 in Hz. destruct Hz as [[Hz _] _]. exact Hz.
                + exact Hvars_nd.
              - constructor. intros z0 Hz0. inv Hz0. inv H.
                destruct H0 as [_ Habs]. apply Habs. constructor. }
            (* Extract bstep from Ecase preord_exp using Ehalt source evaluation *)
            assert (Hehalt : @bstep_fuel cenv nat fuel_res unit trace_res
                     (M.set r_br v' rho_proj) (Ehalt r_br) 1%nat (Res v') tt).
            { pose proof (BStepf_run cenv (M.set r_br v' rho_proj) (Ehalt r_br) (Res v') 0%nat tt
                (BStept_halt cenv r_br v' (M.set r_br v' rho_proj) (M.gss r_br v' rho_proj))) as Hbsf.
              simpl in Hbsf. exact Hbsf. }
            assert (Hle_h : (to_nat 1%nat <= i + 1)%nat) by (simpl; lia).
            edestruct Hpre_ecase as
              (v_body & cin_ecase & cout_ecase & Hbstep_ecase & Hpost_ecase & Hres_ecase).
            { exact Hle_h. }
            { exact Hehalt. }

            (* Extract fuel bounds from the composed post *)
            unfold comp, anf_bound, eq_fuel_n, one_step in Hpost_ecase.
            destruct Hpost_ecase as
              [[[[e_z1 rho_z1] f_z1] t_z1]
               [[[[[e_z2 rho_z2] f_z2] t_z2] [[Hlb_f2 Hub_f2] Heq_fn]] Hone_f]].
            simpl in Hlb_f2, Hub_f2, Heq_fn, Hone_f.
            (* Derived: f2' + n_vars + 2 <= cin_ecase <= t2' + n_vars + 2 *)

            (* v_body is a res; extract the actual val *)
            destruct v_body as [ | v_bc].
            { (* OOT case: contradiction *)
              simpl in Hres_ecase. contradiction. }
            (* Extract preord_val from preord_res *)
            simpl in Hres_ecase.
            rename Hres_ecase into Hrel_body.
            (* Hrel_body : preord_val cenv eq_fuel ((i+1) - to_nat 1) v' v_bc = preord_val ... i v' v_bc *)

            (* Build env bridge for continuation *)
            assert (Hrefl : preord_exp cenv eq_fuel eq_fuel i
              (e_k, M.set x v' rho)
              (e_k, M.set x v_bc (M.set x1 (Vconstr c_tag vs_anf) rho_efun))).
            { eapply preord_exp_refl. now eapply eq_fuel_compat.
              intros z Hz.
              destruct (Pos.eq_dec z x) as [-> | Hneq_x].
              - (* z = x: v' vs v_bc *)
                intros vz Hgetz. rewrite M.gss in Hgetz. inv Hgetz.
                eexists. split. rewrite M.gss. reflexivity.
                eapply preord_val_monotonic. exact Hrel_body. lia.
              - (* z ≠ x: freshness *)
                intros vz Hgetz. rewrite M.gso in Hgetz by auto.
                destruct (Pos.eq_dec z x1) as [-> | Hneq_x1].
                + (* z = x1: alpha-equiv or contradiction *)
                  destruct (anf_cvt_result_in_consumed _ _ _ _ _ _ _ Hcvt_e1) as [Hin_vn | Hin_S].
                  * (* x1 ∈ FromList vnames: alpha-equiv *)
                    eexists. split.
                    { rewrite M.gso by auto. rewrite M.gss. reflexivity. }
                    eapply anf_cvt_val_alpha_equiv.
                    -- eapply anf_cvt_result_in_vnames_eval;
                         [ exact Henv | exact Hnd
                         | eapply Disjoint_Included_r;
                             [eapply Included_trans;
                               [eapply Setminus_Included | eapply Setminus_Included]
                             | exact Hdis]
                         | exact Hcvt_e1 | exact Hin_vn | exact Heval1 | exact Hgetz ].
                    -- exact Hrel_con.
                  * (* x1 ∈ S \\ [set f] \\ [set y]: contradiction *)
                    exfalso.
                    assert (Hx1_not_S2 : ~ x1 \in S2).
                    { eapply anf_cvt_result_not_in_output.
                      - exact Hcvt_e1.
                      - eapply Disjoint_Included_r;
                          [eapply Included_trans;
                            [eapply Setminus_Included | eapply Setminus_Included]
                          | exact Hdis]. }
                    destruct Hdis_ek as [Hdis_ek'].
                    apply (Hdis_ek' x1). constructor.
                    { exact Hz. }
                    { constructor.
                      - constructor.
                        ++ eapply Setminus_Included. eapply Setminus_Included. exact Hin_S.
                        ++ intros [Habs_S3 _].
                           apply Hx1_not_S2.
                           eapply (proj2 (proj2 (proj2 anf_cvt_rel_subset))).
                           exact Hcvt_brs. exact Habs_S3.
                      - intros Habs. inv Habs. congruence. }
                + (* z ≠ x1 *)
                  destruct (Pos.eq_dec z f) as [-> | Hneq_f].
                  * (* z = f: contradiction with Hdis_ek *)
                    exfalso.
                    assert (HS3_S2 : S3 \subset S2).
                    { eapply (proj2 (proj2 (proj2 anf_cvt_rel_subset))). exact Hcvt_brs. }
                    destruct Hdis_ek as [Hdis_ek'].
                    apply (Hdis_ek' f). constructor.
                    { exact Hz. }
                    { constructor.
                      - constructor.
                        ++ assumption.
                        ++ intros [Habs_S3 _].
                           apply HS3_S2 in Habs_S3. apply HS2 in Habs_S3.
                           destruct Habs_S3 as [[_ Hc] _]. apply Hc. constructor.
                      - intros Habs. inv Habs. congruence. }
                  * (* z ≠ x1, z ≠ f *)
                    eexists. split.
                    -- rewrite M.gso by auto. rewrite M.gso by auto.
                       unfold rho_efun, defs. simpl. rewrite M.gso by auto.
                       exact Hgetz.
                    -- eapply preord_val_refl. tci. }

            edestruct Hrefl as (v_cont & cin_cont & cout_cont & Hbstep_cont & Heq_cont & Hres_cont).
            { exact Hle_cin. }
            { exact Hbstep_ek. }

            (* Construct the full Eletapp bstep *)
            do 3 eexists. split.
            { econstructor 2. eapply BStept_letapp.
              - (* M.get f (M.set x1 ... rho_efun) = Vfun rho defs f *)
                assert (Hneq_x1f : x1 <> f).
                { destruct (anf_cvt_result_in_consumed _ _ _ _ _ _ _ Hcvt_e1) as [Hin_vn | Hin_S].
                  - intro Heq. subst. destruct Hdis as [Hdis''].
                    eapply (Hdis'' f). constructor; eauto.
                  - intro Heq. subst.
                    destruct Hin_S as [Hin_inner _].
                    destruct Hin_inner as [_ Habs].
                    apply Habs. constructor. }
                rewrite M.gso by (intro Heq'; apply Hneq_x1f; auto).
                unfold rho_efun, defs. simpl. rewrite M.gss. reflexivity.
              - (* get_list [x1] (M.set x1 ... rho_efun) = [Vconstr c_tag vs_anf] *)
                simpl. rewrite M.gss. reflexivity.
              - (* find_def f defs = (func_tag, [y], Ecase y pats) *)
                subst defs. simpl. destruct (M.elt_eq f f); [reflexivity | congruence].
              - (* set_lists [y] [Vconstr c_tag vs_anf] (def_funs ...) = Some rho_match *)
                reflexivity.
              - (* body evaluates: Ecase y pats *)
                exact Hbstep_ecase.
              - (* continuation evaluates *)
                exact Hbstep_cont. }
            split.
            { (* PostT: anf_bound (f2' + n_vars + 3) (t2' + n_vars + 3) *)
              unfold anf_bound. unfold eq_fuel in Heq_cont.
              simpl in Heq_cont. subst.
              simpl. 
              unfold one, one_i in *; simpl; unfold_all. lia. }
            { exact Hres_cont. } }
        (* Step 4: Inclusion — compose bounds *)
        { unfold inclusion, comp, eq_fuel, anf_bound, one_step.
          intros [[[? ?] ?] ?] [[[? ?] ?] ?].
          intros [[[[? ?] ?] ?] [[[[[? ?] ?] ?] [[? ?] [? ?]]] ?]].
          unfold_all. simpl in *. split; lia. }
      + intros _. eexists 0%nat. constructor 1. unfold algebra.one. simpl. lia.

    - (* 10. eval_Match_step_OOT: Match_e, e1 diverges *)
      intros e1' rho0 n0 br0 f0 t0 Hoot IH_oot.
      unfold anf_cvt_correct_exp_step.
      intros rho vnames C x S S' i Hwf Hwfe Hnd Hdis Henv Hcvt e_k Hdis_ek.
      split; [intros; congruence | intros _; eexists 0%nat; constructor 1; unfold algebra.one; simpl; lia].

    (** ** eval_fuel_many cases (P0 = anf_cvt_correct_exps) *)

    - (* 11. eval_many_enil *)
      intros vs0.
      unfold anf_cvt_correct_exps.
      intros rho vnames C xs S S' i Hwf _Hwfe Hnd Hdis Henv Hcvt e_k vs' Hrel_vs Hdis_ek.
      inv Hcvt. inv Hrel_vs. simpl.
      intros v1 cin cout Hleq Hstep.
      exists v1, cin, cout. split. exact Hstep. split.
      { unfold anf_bound. unfold_all. simpl. lia. }
      { destruct v1; simpl; auto. eapply preord_val_refl. tci. }

    - (* 12. eval_many_econs *)
      intros vs_env e0 es0 v0 vs0 f0 fs0 t0 ts0 Heval_e IH_e Heval_es IH_es.
      unfold anf_cvt_correct_exps in IH_es |- *.
      unfold anf_cvt_correct_exp in IH_e.
      intros rho vnames C xs S S' i Hwf Hwfe Hnd Hdis Henv Hcvt e_k vs' Hrel_vs Hdis_ek.
      inv Hcvt. fold anf_cvt_rel in *. fold anf_cvt_rel_exps in *.
      inv Hrel_vs.
      (* After inv: C = comp_ctx_f C1 C2, xs = x1 :: xs_rest,
         vs' = v1' :: vs_tl', with:
         Hcvt_e  : anf_cvt_rel S e0 vnames cnstrs S2 C1 x1
         Hcvt_es : anf_cvt_rel_exps S2 es0 vnames cnstrs S' C2 xs_rest
         Hrel_v  : anf_val_rel v0 v1'
         Hrel_rest : Forall2 anf_val_rel vs0 vs_tl' *)
      assert (Hwfe_e0 : exp_wf (N.of_nat (Datatypes.length vnames)) e0) by (inversion Hwfe; assumption).
      assert (Hwfe_es0 : exps_wf (N.of_nat (Datatypes.length vnames)) es0) by (inversion Hwfe; assumption).
      simpl set_many. rewrite <- app_ctx_f_fuse.
      (* Chain: env_bridge(eq_fuel) + IH_es(anf_bound fs0 ts0) + IH_e(anf_bound f0 t0) *)
      eapply preord_exp_post_monotonic.
      2:{ eapply preord_exp_trans. tci. eapply eq_fuel_idemp.
          (* Right step: IH_e with continuation C2|[e_k]| *)
          2:{ intros m.
              edestruct IH_e as [IH_val _]; [ exact Hwf | exact Hwfe_e0 | exact Hnd | exact Hdis | exact Henv | eassumption | eapply anf_cvt_disjoint_occurs_free_ctx_exps; eassumption | ].
              eapply IH_val; eauto. }
          eapply preord_exp_trans. tci. eapply eq_fuel_idemp.
          (* Right step: IH_es with env M.set x1 v1' rho *)
          2:{ intros m.
              match goal with
              | [ Hcvt_e0 : anf_cvt_rel S e0 vnames _ _ _ ?x1_v,
                  Hrel_v0 : anf_val_rel v0 ?v1'_v |- _ ] =>
                assert (Hnd_ext : env_consistent (x1_v :: vnames) (v0 :: vs_env))
                  by (eapply env_consistent_extend_from_cvt;
                      [ exact Hnd | exact Hcvt_e0 | exact Hdis | exact Heval_e ]);
                eapply IH_es; [ exact Hwf | exact Hwfe_es0 | exact Hnd | | | eassumption | eassumption | eapply anf_cvt_disjoint_exps_continuation; eassumption ];
                [ eapply Disjoint_Included_r;
                    [eapply (proj1 anf_cvt_rel_subset); exact Hcvt_e0 | exact Hdis]
                | eapply anf_env_rel_set; [ exact Henv | ];
                  intros k Hnth_k;
                  destruct (anf_cvt_result_in_consumed _ _ _ _ _ _ _ Hcvt_e0) as [Hin_vn | Hin_S];
                  [ exists v0; split;
                    [ assert (Hnd_inst := Hnd_ext 0%nat (Datatypes.S k) x1_v eq_refl Hnth_k);
                      simpl in Hnd_inst; symmetry; exact Hnd_inst
                    | exact Hrel_v0 ]
                  | exfalso; destruct Hdis as [Hdis''];
                    apply (Hdis'' x1_v); constructor;
                    [ eapply nth_error_In; exact Hnth_k | exact Hin_S ] ] ]
              end. }
          (* Leftmost: env bridge —
             M.set x1 v1' (set_many xs_rest vs_tl' rho) ≈
             set_many xs_rest vs_tl' (M.set x1 v1' rho)
             This holds for preord_var_env because:
             - At y ≠ x1: both sides agree (set_many dominates for y ∈ xs_rest,
               otherwise M.get y rho since y ≠ x1)
             - At y = x1: LHS gives v1' (M.gss), RHS gives v1' if x1 ∉ xs_rest,
               or the set_many value if x1 ∈ xs_rest. In the latter case,
               both values translate the same source value (preord_val_refl). *)
          eapply preord_exp_refl. now eapply eq_fuel_compat.
          intros z Hz v1 Hget.
          (* env bridge: M.set x1 v1' (set_many xs vs rho) ≈ set_many xs vs (M.set x1 v1' rho) *)
          destruct (Pos.eq_dec z x1) as [Heq_z | Hneq_z].
          + subst z. rewrite M.gss in Hget.
            inv Hget.
            destruct (in_dec Pos.eq_dec x1 xs0) as [Hin_xs | Hnin_xs].
            * (* x1 ∈ xs0: both v1 and set_many value translate
                 the same source value via alpha-equiv *)
              (* x1 ∈ xs0: both values translate the same source value *)
              (* Step 1: x1 ∈ FromList vnames *)
              assert (Hx1_vn : x1 \in FromList vnames).
              { edestruct anf_cvt_rel_exps_In_range as [? | ?];
                  [ eassumption | exact Hin_xs | assumption | ].
                exfalso; eapply anf_cvt_result_not_in_output; eassumption. }
              (* Step 2: Find positions *)
              destruct (In_nth_error _ _ Hx1_vn) as [n_pos Hn_pos].
              destruct (In_nth_error _ _ Hin_xs) as [k_pos Hk_pos].
              destruct (first_occurrence_exists xs0 k_pos x1 Hk_pos)
                as [k0 [Hle [Hk0 Hfirst]]].
              (* Step 3: Get set_many value — match on goal to find the values list *)
              match goal with
              | [ |- context [ set_many xs0 ?l_v ?base ] ] =>
                assert (Hlen_xs0 : Datatypes.length xs0 = Datatypes.length l_v)
                  by (etransitivity;
                      [ eapply anf_cvt_rel_exps_length; eassumption
                      | etransitivity;
                        [ symmetry; eapply eval_fuel_many_length; eassumption
                        | eapply Forall2_length; eassumption ] ]);
                destruct (set_many_get_first xs0 l_v base x1 k0 Hlen_xs0 Hk0 Hfirst)
                  as [v_sm [Hv_sm_k Hget_sm]]
              end.
              eexists; split; [ exact Hget_sm | ].
              (* Step 4: Common source value *)
              assert (Hdis_S2 : Disjoint _ (FromList vnames) _)
                by (eapply Disjoint_Included_r;
                    [ eapply anf_cvt_exp_subset; eassumption | exact Hdis ]).
              edestruct anf_cvt_rel_exps_var_lookup
                as [v_src [Hvsrc_k0 Hvsrc_n]];
                [ exact Heval_es | eassumption | exact Hdis_S2 | exact Hnd
                | exact Hk0 | exact Hn_pos | ].
              edestruct anf_env_rel_nth_error
                as [v'_rho [Hget_rho Hrel_src_rho]];
                [ exact Henv | exact Hn_pos | exact Hvsrc_n | ].
              (* Step 5: anf_val_rel v0 v'_rho *)
              assert (Hrel_v0_rho : anf_val_rel v0 v'_rho)
                by (eapply anf_cvt_result_in_vnames_eval;
                    [ exact Henv | exact Hnd | exact Hdis
                    | eassumption | exact Hx1_vn | exact Heval_e | exact Hget_rho ]).
              (* Step 6: anf_val_rel v_src v_sm from Forall2 *)
              assert (Hrel_src_sm : anf_val_rel v_src v_sm).
              { destruct (Forall2_nth_error_l _ _ _ _ _ H4 Hvsrc_k0)
                  as [v_sm' [Hvsm' Hrel']].
                rewrite Hv_sm_k in Hvsm'. inv Hvsm'. exact Hrel'. }
              (* Step 7: Transitivity via v'_rho *)
              eapply preord_val_trans. tci. eapply eq_fuel_idemp.
              { eapply anf_cvt_val_alpha_equiv; eassumption. }
              { intro m. eapply anf_cvt_val_alpha_equiv;
                  [ exact Hrel_src_rho | exact Hrel_src_sm ]. }
            * eexists; split.
              -- rewrite set_many_get_neq; auto. rewrite M.gss. reflexivity.
              -- eapply preord_val_refl. tci.
          + rewrite M.gso in Hget; auto.
            eexists; split.
            * rewrite set_many_set_neq_base; auto. exact Hget.
            * eapply preord_val_refl. tci. }
      (* inclusion: comp (comp eq_fuel (anf_bound fs0 ts0)) (anf_bound f0 t0) ⊆ anf_bound (f0+fs0) (t0+ts0) *)
      unfold inclusion, comp, eq_fuel, anf_bound.
      intros [[[? ?] ?] ?] [[[? ?] ?] ?].
      intros [[[[? ?] ?] ?] [[[[? ?] ?] ?] [? ?]]].
      unfold_all. destruct p. destructAll. simpl in *. lia.

    (** ** eval_env_fuel cases (P1 = anf_cvt_correct_exp) *)

    - (* 13. eval_Var_fuel *)
      intros vs1 n v Hnth.
      unfold anf_cvt_correct_exp.
      intros rho vnames C x S S' i Hwf Hwfe Hnd Hdis Henv Hcvt e_k Hdis_ek.
      inv Hcvt. (* anf_Var: C = Hole_c, x = v0, S' = S *)
      split.
      + intros v0 v' Heq Hrel. inv Heq.
        (* C = Hole_c, so C |[ e_k ]| = e_k. S' = S so (S\S')\{x} = empty.
           Need: preord_exp (anf_bound 0 0) eq_fuel i (e_k, M.set x v' rho) (e_k, rho).
           By anf_env_rel, x already maps to some v'_old in rho with anf_val_rel v v'_old.
           By alpha-equiv, preord_val eq_fuel i v' v'_old. Then use preord_exp_refl. *)
        eapply preord_exp_post_monotonic.
        2:{ (* preord_exp eq_fuel eq_fuel i ... *)
          eapply preord_exp_refl. now eapply eq_fuel_compat.
          (* preord_env_P eq_fuel (occurs_free e_k) i (M.set x v' rho) rho *)
          intros y Hy.
          destruct (Pos.eq_dec y x) as [Heq | Hneq].
          - subst. intros v1 Hget. rewrite M.gss in Hget. inv Hget.
            edestruct anf_env_rel_nth_error as [v'_old [Hget_old Hrel_old]]; eauto.
            eexists. split. eassumption.
            eapply anf_cvt_val_alpha_equiv; eassumption.
          - intros v1 Hget. rewrite M.gso in Hget; auto.
            eexists. split. eassumption.
            eapply preord_val_refl. tci. }
        (* inclusion eq_fuel (anf_bound <0> <0>) *)
        unfold inclusion, eq_fuel, anf_bound.
        intros [[[? ?] ?] ?] [[[? ?] ?] ?]. intros. subst.
        unfold_all. simpl in *. lia.
      + intros Habs. congruence. (* Var_e never OOTs with 0 fuel *)

    - (* 14. eval_Lam_fuel *)
      intros vs1 e1 na1.
      unfold anf_cvt_correct_exp.
      intros rho vnames C x S S' i Hwf Hwfe Hnd Hdis Henv Hcvt e_k Hdis_ek.
      inv Hcvt.
      (* After inv: x is the function name, C = Efun1_c (Fcons x func_tag [x1] (C1 |[ Ehalt r1 ]|) Fnil) Hole_c
         Hypotheses from anf_Lam:
           H1 : x1 \in S
           H3 : x \in S \\ [set x1]
           H9 : anf_cvt_rel (S \\ [set x1] \\ [set x]) vs1 (x1 :: vnames) cnstrs S' C1 r1 *)
      split.
      + intros v0 v' Heq Hrel. inv Heq.
        eapply preord_exp_post_monotonic.
        2:{ eapply preord_exp_trans. tci. eapply eq_fuel_idemp.
            2:{ intros m. eapply preord_exp_Efun_red. }
            eapply preord_exp_refl. now eapply eq_fuel_compat.
            intros y Hy.
            destruct (Pos.eq_dec y x) as [Heq | Hneq].
            - subst. intros v1 Hget. rewrite M.gss in Hget. inv Hget.
              eexists. split.
              { cbn [def_funs]. rewrite M.gss. reflexivity. }
              eapply anf_cvt_val_alpha_equiv. eassumption.
              eapply anf_rel_Clos with (names := vnames); eauto.
              * (* Disjoint var (x1 |: (x |: FromList vnames)) (S \\ [set x1] \\ [set x]) *)
                eapply Union_Disjoint_l.
                { eapply Disjoint_Singleton_l. intros [[_ Habs] _]. apply Habs. constructor. }
                eapply Union_Disjoint_l.
                { eapply Disjoint_Singleton_l. intros [_ Habs]. apply Habs. constructor. }
                eapply Disjoint_Included_r.
                { eapply Included_trans. eapply Setminus_Included. eapply Setminus_Included. }
                eassumption.
              * (* ~ x1 \in x |: FromList vnames *)
                intros Hc. inv Hc.
                -- (* x1 = x *) inv H. destruct H3 as [_ Habs]. apply Habs. constructor.
                -- (* x1 \in FromList vnames *) eapply Hdis. constructor; eauto.
              * (* ~ x \in FromList vnames *)
                intros Hc. eapply Hdis. constructor; eauto.
                destruct H3. assumption.
            - intros v1 Hget. rewrite M.gso in Hget; eauto.
              eexists. split.
              { cbn [def_funs]. rewrite M.gso; eauto. }
              eapply preord_val_refl. tci. }
        unfold inclusion, comp, eq_fuel, one_step, anf_bound.
        intros [[[? ?] ?] ?] [[[? ?] ?] ?] [[[[? ?] ?] ?] [? ?]].
        unfold_all. simpl in *. lia.
      + intros Habs. congruence.

    - (* 15. eval_Fix_fuel *)
      intros vs1 n1 fnlst1.
      unfold anf_cvt_correct_exp.
      intros rho vnames C x S S' i Hwf Hwfe Hnd Hdis Henv Hcvt e_k Hdis_ek.
      inv Hcvt. fold anf_cvt_rel in *. fold anf_cvt_rel_efnlst in *.
      (* After inv (anf_Fix):
         C = Efun1_c fdefs Hole_c, x = f
         H_fnames_sub : FromList fnames ⊆ S
         H_nodup : NoDup fnames
         H_len : length fnames = efnlength fnlst1
         H_efnlst : anf_cvt_rel_efnlst ... fnlst1 (rev fnames ++ vnames) fnames cnstrs S' fdefs
         H_nth : nth_error fnames (N.to_nat n1) = Some f *)
      match goal with
      | [ Hsub : FromList ?fn \subset S,
          Hnodup : NoDup ?fn,
          Hefn : anf_cvt_rel_efnlst _ _ _ ?fn _ _ _,
          Hnth : nth_error ?fn _ = Some ?f |- _ ] =>
        rename Hsub into Hfnames_sub; rename Hnodup into Hnodup_fnames;
        rename Hefn into Hcvt_efn; rename Hnth into Hnth_f
      end.
      split.
      + intros v0 v' Heq Hrel. inv Heq.
        (* Chain: one_step via Efun_red + eq_fuel via env bridging *)
        eapply preord_exp_post_monotonic.
        2:{ eapply preord_exp_trans. tci. eapply eq_fuel_idemp.
            2:{ intros m. eapply preord_exp_Efun_red. }
            (* env bridging: (e_k, M.set f v' rho) ≤eq_fuel (e_k, def_funs fdefs fdefs rho rho) *)
            eapply preord_exp_refl. now eapply eq_fuel_compat.
            intros y Hy.
            destruct (Pos.eq_dec y x) as [Heq | Hneq].
            - (* y = f (the selected function name) *)
              subst. intros v1 Hget. rewrite M.gss in Hget. inv Hget.
              eexists. split.
              { eapply def_funs_eq. eapply name_fds_same.
                rewrite (anf_cvt_rel_efnlst_all_fun_name _ _ _ _ _ _ _ Hcvt_efn).
                eapply nth_error_In. eassumption. }
              eapply anf_cvt_val_alpha_equiv. eassumption.
              eapply anf_rel_ClosFix with (names := vnames) (S1 := S \\ FromList fnames); eauto.
              * (* Disjoint _ (FromList vnames :|: FromList fnames) (S \\ FromList fnames) *)
                apply Union_Disjoint_l.
                -- eapply Disjoint_Included_r; [ eapply Setminus_Included | exact Hdis ].
                -- apply Disjoint_Setminus_r. apply Included_refl.
              * (* Disjoint _ (FromList vnames) (FromList fnames) *)
                eapply Disjoint_Included_r. eapply Hfnames_sub. eassumption.
              * (* anf_fix_rel *)
                eapply anf_cvt_rel_efnlst_to_fix_rel.
                -- exact Hcvt_efn.
                -- apply Disjoint_sym. apply Union_Disjoint_l.
                   ++ apply Disjoint_Setminus_r. apply Included_refl.
                   ++ eapply Disjoint_Included_r; [ eapply Setminus_Included | exact Hdis ].
            - (* y ≠ f: y cannot be in FromList fnames because of disjointness *)
              intros v1 Hget. rewrite M.gso in Hget; auto.
              assert (Hnotfn : ~ name_in_fundefs fdefs y).
              { intros Hc. apply name_fds_same in Hc.
                rewrite (anf_cvt_rel_efnlst_all_fun_name _ _ _ _ _ _ _ Hcvt_efn) in Hc.
                eapply Hdis_ek. constructor; eauto.
                constructor.
                - constructor.
                  + eapply Hfnames_sub. exact Hc.
                  + intros Hin.
                    assert (Hsub_efn := proj1 (proj2 (proj2 anf_cvt_rel_subset)) _ _ _ _ _ _ _ Hcvt_efn).
                    apply Hsub_efn in Hin. inv Hin. contradiction.
                - intros Habs. inv Habs. congruence. }
              eexists. split.
              { rewrite def_funs_neq; eauto. }
              eapply preord_val_refl. tci. }
        unfold inclusion, comp, eq_fuel, one_step, anf_bound.
        intros [[[? ?] ?] ?] [[[? ?] ?] ?] [[[[? ?] ?] ?] [? ?]].
        unfold_all. simpl in *. lia.
      + intros Habs. congruence.
      

    - (* 16. eval_OOT *)
      intros vs1 e1 f1 t1 Hlt.
      unfold anf_cvt_correct_exp.
      intros rho vnames C x S S' i Hwf Hwfe Hnd Hdis Henv Hcvt e_k Hdis_ek.
      split.
      + intros v v' Heq _. congruence.
      + intros _.
        eexists 0%nat. constructor 1. unfold algebra.one. simpl. lia.

    - (* 17. eval_step: wraps eval_env_step into eval_env_fuel *)
      now eauto.

  Qed.

End Correct.
