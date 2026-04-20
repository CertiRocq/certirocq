Require Import MetaRocq.Utils.bytestring.
From Stdlib Require Import ZArith.ZArith Lists.List micromega.Lia Arith
     Ensembles Relations.Relation_Definitions.
Require Import Common.AstCommon.
Require compcert.lib.Maps compcert.lib.Coqlib.
Require Import set_util.

Import ListNotations.
Open Scope list_scope.

Require Import LambdaBoxLocal.expression LambdaBoxLocal.fuel_sem.

(* From Stdlib Require Import Relations.Relation_Definitions. *)
(* From Stdlib Require Import Classes.Morphisms. *)
(* From Stdlib Require Import Classes.RelationClasses. *)

Require Import term cps_show eval ctx logical_relations
        List_util algebra alpha_conv functions Ensembles_util
        LambdaBoxLocal_to_LambdaANF LambdaBoxLocal_to_LambdaANF_util LambdaBoxLocal_to_LambdaANF_corresp
        LambdaANF.tactics identifiers bounds term_util rename.

Require Import ExtLib.Data.Monads.OptionMonad ExtLib.Structures.Monads.

Import Monad.MonadNotation.

Open Scope monad_scope.

Section Bounds.

  (** LambdaBoxLocal fuel and trace *)

  Definition fuel_exp (e: expression.exp) : nat := 1.

  Fixpoint max_m_branches (br : branches_e) : nat :=
    match br with
    | brnil_e => 0
    | brcons_e _ (m, _) e br => max (N.to_nat m) (max_m_branches br)
    end.


  (* This is the cost of the CPS-ed program *)
  Definition trace_exp (e: expression.exp) : nat :=
    match e with
    | Var_e _ => 1
    | Lam_e _ _ => 1
    | App_e _ _ => 5
    | Let_e _ _ _ => 2
    | Fix_e _ _ => 1

    | Con_e _ es => 1 + 2 * List.length (exps_as_list es)
    | Match_e _ _ brs => 3 + max_m_branches brs

    (* Unused *)
    | Prf_e => 0
    | Prim_e x => 0
    | Prim_val_e x => 0
    end.


  Program Instance fuel_resource_LambdaBoxLocal : @resource expression.exp nat :=
    { zero := 0;
      one_i := fuel_exp;
      plus := Nat.add
    }.
  Next Obligation.
    lia.
  Qed.
  Next Obligation.
    lia.
  Qed.
  Next Obligation.
    lia.
  Qed.

  Program Instance trace_resource_LambdaBoxLocal : @resource expression.exp nat :=
    { zero := 0;
      one_i := trace_exp;
      plus := Nat.add
    }.
  Next Obligation.
    lia.
  Qed.
  Next Obligation.
    lia.
  Qed.
  Next Obligation.
    lia.
  Qed.

  Global Instance LambdaBoxLocal_resource_fuel : @LambdaBoxLocal_resource nat.
  Proof.
    constructor. eapply fuel_resource_LambdaBoxLocal.
  Defined.

  Global Instance LambdaBoxLocal_resource_trace : @LambdaBoxLocal_resource nat.
  Proof.
    constructor. eapply trace_resource_LambdaBoxLocal.
  Defined.



  (** LambdaANF fuel and trace *)

  Global Program Instance trace_res_pre : @resource fin unit :=
    { zero := tt;
      one_i fin := tt;
      plus x y := tt; }.
  Next Obligation. destruct x. reflexivity. Qed.
  Next Obligation. destruct x; destruct y. reflexivity. Qed.


  Global Program Instance trace_res_exp : @exp_resource unit :=
    { HRes := trace_res_pre }.

  Global Instance trace_res : @trace_resource unit.
  Proof.
    econstructor. eapply trace_res_exp.
  Defined.

  Definition eq_fuel : @PostT nat unit :=
    fun '(e1, r1, f1, t1) '(e2, r2, f2, t2) => f1 = f2.

  Definition cps_bound (f_src t_src : nat) : @PostT nat unit :=
    fun '(e1, r1, f1, t1) '(e2, r2, f2, t2) =>
      (f1 + f_src <= f2)%nat /\ (* lower bound *)
      (f2 <= f1 + t_src)%nat (* upper bound *).


  Ltac unfold_all :=
    try unfold zero in *;
    try unfold one_ctx in *;
    try unfold algebra.one in *;
    try unfold one_i in *;
    try unfold HRes in *;
    try unfold HRexp_f in *; try unfold fuel_res in *; try unfold fuel_res_exp in *; try unfold fuel_res_pre in *;
    try unfold HRexp_t in *; try unfold trace_res in *; try unfold trace_res_exp in *; try unfold trace_res_pre in *.



  Global Instance eq_fuel_compat cenv :
    @Post_properties cenv nat _ unit _ eq_fuel eq_fuel eq_fuel.
  Proof.
    unfold eq_fuel. constructor; try now (intro; intros; intro; intros; unfold_all; simpl; lia).
    - intro; intros. unfold post_base'. unfold_all; simpl. lia.
    - firstorder.
  Qed.

End Bounds.


Ltac inv_setminus :=
  match goal with
  | [ H : In _ (?S \\ ?Q) _ |- _ ] => inv H; try inv_setminus
  end.


Section FV.

  Context (func_tag kon_tag default_tag default_itag : positive)
          (cnstrs : conId_map).

  Definition cps_cvt_exp_fv_stmt :=
    forall e e' k1 vars1 S1 S2,
      cps_cvt_rel func_tag kon_tag default_tag S1 e vars1 k1 cnstrs S2 e' ->
      occurs_free e' \subset k1 |: FromList vars1 :|: S1.

  Definition cps_cvt_exps_fv_stmt :=
    forall es e' e_app vars1 ks xs S1 S2,
      (* Disjoint _ (FromList ks) (FromList vars1 :|: S1) -> *)
      cps_cvt_rel_exps func_tag kon_tag default_tag S1 es vars1 e_app xs ks cnstrs S2 e' ->
      occurs_free e' \subset (FromList vars1 :|: S1 :|: (occurs_free e_app \\ FromList ks)).

  Definition cps_cvt_efnlst_fv_stmt :=
    forall efns S1 vars1 nlst1 S2 fdefs1,
      cps_cvt_rel_efnlst func_tag kon_tag default_tag S1 efns vars1 nlst1 cnstrs S2 fdefs1 ->
      occurs_free_fundefs fdefs1 \subset FromList vars1 :|: S1.

  Definition cps_cvt_branches_fv_stmt :=
    forall bs S1 vars1 k1 x1 S2 bs1,
      cps_cvt_rel_branches func_tag kon_tag default_tag S1 bs vars1 k1 x1 cnstrs S2 bs1 ->
      occurs_free (Ecase x1 bs1) \\ [set x1] \subset k1 |: FromList vars1 :|: S1.


  Definition cps_cvt_rel_fv_stmt :=
    cps_cvt_exp_fv_stmt /\
    cps_cvt_exps_fv_stmt /\
    cps_cvt_efnlst_fv_stmt /\
    cps_cvt_branches_fv_stmt.

  Lemma ctx_bind_proj_occurs_free t x1 vars n e :
    occurs_free (ctx_bind_proj t x1 vars n |[ e ]|) \subset x1 |: occurs_free e.
  Proof.
    revert n; induction vars; intros n; simpl.
    - now sets.
    - repeat normalize_occurs_free. eapply Union_Included; sets.
  Qed.

  Lemma cps_cvt_rel_fv : cps_cvt_rel_fv_stmt.
  Proof.
    eapply exp_ind_alt_2; intros.
    - (* Var_e *)
      inv H. normalize_occurs_free. repeat normalize_sets.
      eapply nth_error_In in H2.
      eapply Union_Included; sets.

    - (* Lem_e *)
      inv H0. repeat normalize_occurs_free. repeat normalize_sets.
      inv_setminus.
      eapply Union_Included; sets.

      + eapply Setminus_Included_Included_Union.
        eapply Included_trans. eapply H. eassumption.
        simpl. repeat normalize_sets.
        xsets.

      + simpl. repeat normalize_sets. rewrite Setminus_Union_distr.
        eapply Union_Included; sets.

    - (* App_e *)
      inv H1. do 5 normalize_occurs_free. simpl. repeat rewrite occurs_free_fundefs_Fnil at 1.

      eapply Union_Included.

      + normalize_sets.
        eapply Union_Included; sets.
        rewrite !Setminus_Union_distr. eapply Union_Included; sets.
        eapply Union_Included; sets.
        eapply Union_Included; sets.
        eapply Union_Included; sets.

        do 2 eapply Setminus_Included_Included_Union.
        eapply Included_trans. eapply H0. eassumption.
        eapply cps_cvt_exp_subset in H9.
        eapply Union_Included; sets.
        now xsets.
        eapply Included_trans. eassumption. now xsets.

      + apply Setminus_Included_Included_Union.
        eapply Included_trans. eapply H. eassumption. xsets.

    - (* Con_e *)
      inv H0.
      repeat normalize_occurs_free. simpl. repeat normalize_sets.
      eapply Included_trans. eapply H. eassumption.

      (* rewrite !Setminus_Union_distr. eapply Union_Included. *)
      eapply Union_Included. eapply Union_Included.
      now sets. now xsets.
      repeat normalize_occurs_free.
      rewrite !Setminus_Union_distr. eapply Union_Included; sets.
      eapply Setminus_Included_Included_Union. eapply Included_trans.
      eassumption. now xsets.
      repeat normalize_sets. xsets.

    - (* Match_e *)
      inv H1.
      repeat normalize_occurs_free. simpl.
      eapply Union_Included.
      eapply Union_Included; sets.

      + repeat normalize_sets.
        rewrite (Union_commut [set k0]).
        rewrite <- Setminus_Union. apply Setminus_Included_Included_Union.
        eapply Included_trans. eapply H0. eassumption.
        eapply cps_cvt_exp_subset in H13.
        eapply Union_Included; sets.
        eapply Included_trans. eassumption. sets.

      +  repeat normalize_sets. apply Setminus_Included_Included_Union.
         eapply Included_trans. eapply H. eassumption. now xsets.

    - (* Let_e *)
      inv H1.
      repeat normalize_occurs_free. simpl. repeat normalize_sets.
      eapply Union_Included.

      + eapply Setminus_Included_Included_Union.
        eapply Included_trans. eapply H0. eassumption.
        repeat normalize_sets. now xsets.

      + eapply Setminus_Included_Included_Union.
        eapply Included_trans. eapply H. eassumption.
        repeat normalize_sets.
        eapply Union_Included; sets.
        eapply Included_trans. eapply cps_cvt_exp_subset. eassumption. now sets.


    - (* Fix_e *)
      inv H0.
      repeat normalize_occurs_free. simpl. repeat normalize_sets.
      eapply nth_error_In in H13.
      eapply Union_Included; [ | now xsets ].
      eapply Included_trans. eapply H. eassumption.
      repeat normalize_sets. rewrite FromList_rev. xsets.

    - (* Prf_e *)
      inv H. repeat normalize_occurs_free. repeat normalize_sets.
      xsets.

    - (* Prim_val_e *)
      inv H. repeat normalize_occurs_free. repeat normalize_sets. xsets.

    - (* Prim_e *)
      inv H.

    - (* enil *)
      inv H. normalize_sets. sets.

    - (* econs *)
      inv H1.
      repeat normalize_occurs_free. simpl. repeat normalize_sets.
      eapply Union_Included.

      + apply Setminus_Included_Included_Union.
        eapply cps_cvt_exp_subset in H5.
        eapply Included_trans. eapply H0. eassumption.
        (* now eapply Disjoint_Included; [ | | eassumption ]; sets. *)

        rewrite (Union_commut _ (FromList ks0)), <- Setminus_Union.
        rewrite <- !Union_assoc. rewrite <- Union_Included_Union_Setminus with (s3 := [set k1]) (s2 := k1 |: _); tci; sets.

      + apply Setminus_Included_Included_Union.
        eapply Included_trans. eapply H. eassumption.

        eapply Union_Included; sets.

    - (* efnil *)
      inv H. normalize_occurs_free. sets.

    - (* efcons *)
      split; intros.  2:{ inv H2. exfalso. now eapply H. }

      inv H2. inv H4. repeat normalize_occurs_free. simpl. repeat normalize_sets.

      eapply Union_Included.

      + eapply Setminus_Included_Included_Union.
        eapply Included_trans. eapply H0. eassumption.
        repeat normalize_sets.
        eapply Union_Included; sets.
        eapply Union_Included; sets.

      + eapply Setminus_Included_Included_Union.
        eapply Included_trans. eapply H1. eassumption.
        eapply Union_Included; sets.
        eapply Included_trans. eapply cps_cvt_exp_subset. eassumption. now sets.

    - inv H. repeat normalize_occurs_free. sets.

    - inv H1. repeat normalize_occurs_free. repeat normalize_sets.
      rewrite !Setminus_Union_distr. eapply Union_Included. now sets.

      eapply Union_Included.

      eapply Setminus_Included_Included_Union.
      eapply Included_trans. eapply ctx_bind_proj_occurs_free.

      eapply Union_Included; sets. eapply Included_trans.
      eapply H. eassumption.
      eapply cps_cvt_branches_subset in H18.
      rewrite FromList_app.
      eapply Union_Included; sets.
      eapply Union_Included; sets.
      eapply Union_Included; sets.
      eapply Included_trans. eassumption. now sets.

      eapply H0. eassumption.

  Qed.


  Corollary cps_cvt_exp_fv : cps_cvt_exp_fv_stmt.
  Proof. eapply (proj1 cps_cvt_rel_fv). Qed.

  Corollary cps_cvt_exps_fv : cps_cvt_exps_fv_stmt.
  Proof. eapply (proj1 (proj2 cps_cvt_rel_fv)). Qed.

  Corollary cps_cvt_efnlst_fv : cps_cvt_efnlst_fv_stmt.
  Proof. eapply (proj1 (proj2 (proj2 cps_cvt_rel_fv))). Qed.

  Corollary cps_cvt_branches_fv : cps_cvt_branches_fv_stmt.
  Proof. eapply (proj2 (proj2 (proj2 cps_cvt_rel_fv))). Qed.


End FV.

Section Correct.

  Context (prim_map : M.t Pipeline_utils.primitive).
  Context (func_tag kon_tag default_tag default_itag : positive)
          (cnstrs : conId_map)
          (cenv : ctor_env).

  Ltac unfold_all :=
    try unfold zero in *;
    try unfold one_ctx in *;
    try unfold algebra.one in *;
    try unfold one_i in *;
    try unfold algebra.HRes in *;
    try unfold HRexp_f in *; try unfold fuel_res in *; try unfold fuel_res_exp in *; try unfold fuel_res_pre in *;
    try unfold HRexp_t in *; try unfold trace_res in *; try unfold trace_res_exp in *; try unfold trace_res_pre in *.


  Definition cps_cvt_rel := LambdaBoxLocal_to_LambdaANF.cps_cvt_rel func_tag kon_tag default_tag.
  Definition cps_cvt_rel_exps := LambdaBoxLocal_to_LambdaANF.cps_cvt_rel_exps func_tag kon_tag default_tag.
  Definition cps_cvt_rel_efnlst := LambdaBoxLocal_to_LambdaANF.cps_cvt_rel_efnlst func_tag kon_tag default_tag.
  Definition cps_cvt_rel_branches := LambdaBoxLocal_to_LambdaANF.cps_cvt_rel_branches func_tag kon_tag default_tag.
  Definition cps_env_rel := cps_env_rel cnstrs func_tag kon_tag default_tag.
  Definition cps_val_rel := cps_val_rel cnstrs func_tag kon_tag default_tag.

  (* Alpha-equiv corollaries *)

  Corollary cps_cvt_exp_alpha_equiv k :
    cps_cvt_exp_alpha_equiv eq_fuel eq_fuel cnstrs cenv func_tag kon_tag default_tag k.
  Proof. eapply cps_cvt_alpha_equiv; tci. firstorder. Qed.

  Corollary cps_cvt_exps_alpha_equiv k :
    cps_cvt_exps_alpha_equiv eq_fuel eq_fuel cnstrs cenv func_tag kon_tag default_tag k.
  Proof. eapply cps_cvt_alpha_equiv; tci. firstorder. Qed.

  Corollary cps_cvt_efnlst_alpha_equiv k :
    cps_cvt_efnlst_alpha_equiv eq_fuel cnstrs cenv func_tag kon_tag default_tag k.
  Proof. eapply cps_cvt_alpha_equiv; tci. firstorder. Qed.

  Corollary cps_cvt_branches_alpha_equiv k :
    cps_cvt_branches_alpha_equiv eq_fuel eq_fuel cnstrs cenv func_tag kon_tag default_tag k.
  Proof. eapply cps_cvt_alpha_equiv; tci. firstorder. Qed.


  Lemma exps_to_list_inj es1 es2 :
    exps_as_list es1 = exps_as_list es2 ->
    es1 = es2.
  Proof.
    revert es2.
    induction es1; intros es2 Heq; destruct es2; inv Heq.

    reflexivity.

    f_equal. eauto.

  Qed.

  Lemma cps_cvt_rel_exps_app S es es1 es2 vnames e_app xs ks S' e' :
    exps_as_list es = exps_as_list es1 ++ exps_as_list es2 ->
    cps_cvt_rel_exps S es vnames e_app xs ks cnstrs S' e' ->
    exists S'' e'' xs1 xs2 ks1 ks2,
      xs = xs1 ++ xs2 /\
      ks = ks1 ++ ks2 /\
      S'' \subset S /\
      cps_cvt_rel_exps S'' es2 vnames e_app xs2 ks2 cnstrs S' e'' /\
      cps_cvt_rel_exps S es1 vnames e'' xs1 ks1 cnstrs S'' e'.
  Proof.
    revert S es es2 vnames e_app xs ks S' e'.
    induction es1; intros S es es2 vnames e_app xs ks S' e' Heq Hrel.

    - simpl in Heq. eapply exps_to_list_inj in Heq. subst.
      do 2 eexists. exists []. exists xs. exists []. exists ks.
      split. reflexivity. split. reflexivity. split. reflexivity.
      split. eassumption. now econstructor.

    - destruct es. simpl in Heq. now inv Heq. inv Hrel.

      simpl in *. inv Heq.

      edestruct IHes1. eassumption. eassumption.
      destructAll.

      do 2 eexists. exists (x1 :: x2), x3. exists (k1 :: x4), x5.  split; [ | split; [ | split; [ | split ]]].

      reflexivity.  reflexivity.

      2:{ eassumption. }

      eapply Included_trans. eassumption.
      eapply Included_trans. eapply cps_cvt_exp_subset. eassumption. now sets.

      econstructor; eauto.

  Qed.


  Lemma cps_cvt_rel_exps_occurs_free S es vnames e_app xs ks S' e' :
    cps_cvt_rel_exps S es vnames e_app xs ks cnstrs S' e' ->
    Disjoint _ (FromList vnames :|: S) (FromList ks) ->
    NoDup ks ->
    Disjoint _ (occurs_free e') (FromList ks).
  Proof.
    intros Hrel Hdis Hnd.
    induction Hrel.
    - normalize_sets. sets.
    - repeat normalize_occurs_free.
      repeat normalize_sets. simpl.
      repeat rewrite FromList_cons in Hdis at 1.
      inv Hnd.

      specialize (IHHrel
                    ltac:(eapply cps_cvt_exp_subset in H; eapply Disjoint_Included; [ | | eapply Hdis ]; sets)
                    H3
                 ).
      eapply Union_Disjoint_r; sets.
      eapply Union_Disjoint_l; sets.

      normalize_sets.
      eapply cps_cvt_exp_fv in H.
      eapply Disjoint_Included_l.
      eapply Included_trans. eapply Setminus_Included. eassumption.
      eapply Union_Disjoint_l; sets.

      eapply Union_Disjoint_l. now sets.
      eapply Disjoint_Included; [ | | eapply Hdis ]; sets.
      eapply Disjoint_Included; [ | | eapply Hdis ]; sets.
  Qed.




  Lemma get_list_rev A xs (vs  : list A) rho :
    get_list xs rho = Some vs ->
    get_list (rev xs) rho = Some (rev vs).
  Proof.
    revert vs. induction xs; intros vs Hget; destruct vs; simpl in *; try congruence.
    - destruct (rho ! a); [ | congruence ].
      destruct (get_list xs rho); [ | congruence ]. inv Hget.
    - destruct (rho ! a) eqn:Hget'; [ | congruence ].
      destruct (get_list xs rho); [ | congruence ]. inv Hget.
      erewrite get_list_app. reflexivity. now eauto.
      simpl. rewrite Hget'. reflexivity.
  Qed.


    Lemma cps_env_rel_nth_error vnames vs rho n y v :
      cps_env_rel vnames vs rho ->
      nth_error vnames n = Some y ->
      nth_error vs n = Some v ->
      exists v', M.get y rho = Some v' /\ cps_val_rel v v'.
    Proof.
      intros Hrel. revert n y v; induction Hrel; intros n z v Hnth1 Hnth2.
      - destruct n; simpl in *; congruence.
      - destruct n; simpl in *.
        + inv Hnth1. inv Hnth2. destructAll. eauto.
        + eauto.
    Qed.

    Lemma preord_var_env_extend_neq_l PostG (rho1 rho2 : eval.env) (k : nat) (x1 y1 y2 : var)
          (v1 : term.val) :
        preord_var_env cenv PostG k rho1 rho2 y1 y2 ->
        y1 <> x1 ->
        preord_var_env cenv PostG k (M.set x1 v1 rho1) rho2 y1 y2.
    Proof.
      intros Hval Hneq x' Hget.
      rewrite M.gso in *; eauto.
    Qed.

    Lemma preord_var_env_extend_neq_r PostG (rho1 rho2 : eval.env) (k : nat) (x1 y1 y2 : var)
          (v1 : term.val) :
      preord_var_env cenv PostG k rho1 rho2 y1 y2 ->
      y2 <> x1 ->
      preord_var_env cenv PostG k rho1 (M.set x1 v1 rho2) y1 y2.
    Proof.
      intros Hval Hneq x' Hget.
      rewrite M.gso in *; eauto.
    Qed.

    Lemma preord_var_env_get :
      forall PostG (rho1 rho2 : eval.env) (k : nat) (x1 x2 : var) (v1 v2 : term.val),
        preord_val cenv PostG k v1 v2 ->
        M.get x1 rho1 = Some v1 ->
        M.get x2 rho2 = Some v2 ->
        preord_var_env cenv PostG k rho1 rho2 x1 x2.
    Proof.
      intros rho1 rho2 k x1 x2 v1 v2 Hval Hget1 Hget2 x' v' Hget.
      repeat subst_exp. eauto.
    Qed.

    Lemma preord_var_env_get_list :
      forall PostG (rho1 rho2 : eval.env) (k : nat) (xs1 xs2 : list var) (vs1 vs2 : list term.val),
        Forall2 (preord_val cenv PostG k) vs1 vs2 ->
        get_list xs1 rho1 = Some vs1 ->
        get_list xs2 rho2 = Some vs2 ->
        Forall2 (preord_var_env cenv PostG k rho1 rho2) xs1 xs2.
    Proof.
      intros PG rho1 rho2 k xs1.
      revert rho1 rho2. induction xs1; intros rho1 rho2 xs2 vs1 vs2 Hall Hget1 Hget2.
      - simpl in Hget1. inv Hget1. inv Hall.
        destruct xs2. now constructor.
        simpl in *. destruct (rho2 ! v); try congruence.
        destruct (get_list xs2 rho2); congruence.
      - simpl in Hget1.
         destruct (rho1 ! a) eqn:Hget; try congruence.
         destruct (get_list xs1 rho1) eqn:Hgetl; try congruence.
         inv Hget1.
         inv Hall.
         destruct xs2. now inv Hget2. simpl in *.
         destruct (rho2 ! v0) eqn:Hget'; try congruence.
         destruct (get_list xs2 rho2) eqn:Hgetl'; try congruence.
         inv Hget2.
         constructor; eauto.

         eapply preord_var_env_get; eauto.
    Qed.



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

    Lemma preord_exp_Eapp_red k B rho f rho1 g xs ft ys e' vs rho2 :
      M.get f rho = Some (Vfun rho1 B g) ->
      find_def g B = Some (ft, ys, e') ->
      get_list xs rho = Some vs ->
      set_lists ys vs (def_funs B B rho1 rho1) = Some rho2 ->
      preord_exp cenv one_step eq_fuel k (e', rho2) (Eapp f ft xs , rho).
    Proof.
      intros r cin cout Hleq Hbstep Hget Hf Hgetl Hsetl.
      do 3 eexists. split. econstructor 2. econstructor; eauto.
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


    Lemma eq_fuel_idemp :
      inclusion _ (comp eq_fuel eq_fuel) eq_fuel.
    Proof.
      clear. unfold comp, eq_fuel. intro; intros.
      destruct x as [[[? ?] ?] ?].
      destruct y as [[[? ?] ?] ?]. destructAll.
      destruct x as [[[? ?] ?] ?]. congruence.
    Qed.

    (* TODO move *)
    Ltac destruct_tuples :=
      try match goal with
          | [ X : ?A * ?B |- _ ] => destruct X; destruct_tuples
          end.

    Lemma MSet_non_member (s : PS.t) :
      exists x, ~ PS.In x s.
    Proof.
      destruct (PS.max_elt s) as [m | ] eqn:Hmax.
      - eexists (m + 1)%positive.
        destruct (PS.mem (m + 1)%positive s) eqn:Hmem.
        + eapply PS.mem_spec in Hmem. eapply PS.max_elt_spec2 in Hmax; [ | eassumption ].
          exfalso. eapply Hmax. eapply Pos.compare_lt_iff. zify. lia.
        + intros Hc. eapply PS.mem_spec in Hc. congruence.
      - eapply PS.max_elt_spec3 in Hmax. eexists 1%positive.
        intros Hc. eapply Hmax. eassumption.
    Qed.

    Lemma ToMSet_non_member (S : Ensemble positive) {Hm: ToMSet S} :
      exists x, ~ x \in S.
    Proof.
      edestruct MSet_non_member. exists x. intros Hc.
      eapply H. eapply FromSet_sound. eapply Hm. eassumption.
    Qed.

    Lemma cps_env_rel_weaken vnames vs x v rho :
      cps_env_rel vnames vs rho ->
      ~ x \in FromList vnames ->
      cps_env_rel vnames vs (M.set x v rho).
    Proof.
      intros Henv Hnin. unfold cps_env_rel, LambdaBoxLocal_to_LambdaANF_util.cps_env_rel, cps_env_rel' in *.
      eapply Forall2_monotonic_strong; [ | eassumption ].
      simpl. intros x1 x2 Hin1 Hin2 Hr. rewrite M.gso; eauto.
      intros Hc; subst; auto.
    Qed.


    Lemma cps_env_rel_weaken_setlists vnames vs xs vs' rho rho' :
      cps_env_rel vnames vs rho ->
      set_lists xs vs' rho = Some rho' ->
      Disjoint _ (FromList xs) (FromList vnames) ->
      cps_env_rel vnames vs rho'.
    Proof.
      revert vs' rho rho'; induction xs; intros vs1 rho1 rho2 Hrel Hset Hdis.
      - destruct vs1; inv Hset.  eassumption.
      - destruct vs1; inv Hset.
        destruct (set_lists xs vs1 rho1) eqn:Hset; inv H0.
        repeat normalize_sets.
        eapply cps_env_rel_weaken.
        eapply IHxs. eassumption. eassumption.
        sets.
        intros Hc. eapply Hdis; eauto.
    Qed.


    Lemma cps_env_rel_extend vnames vs x v v' rho :
      cps_env_rel vnames vs rho ->
      M.get x rho = Some v' ->
      cps_val_rel v v' ->
      cps_env_rel (x :: vnames) (v :: vs) rho.
    Proof.
      intros Henv Hget Hval. unfold cps_env_rel, LambdaBoxLocal_to_LambdaANF_util.cps_env_rel, cps_env_rel' in *.
      econstructor; eauto.
    Qed.


    Lemma cps_env_rel_extend_setlists vnames vs xs vs1 vs2 rho :
      cps_env_rel vnames vs rho ->
      get_list xs  rho = Some vs2 ->
      Forall2 (cps_val_rel) vs1 vs2 ->
      cps_env_rel (xs ++ vnames) (vs1 ++ vs) rho.
    Proof.
      revert vs1 vs2 rho; induction xs; intros vs1 vs2 rho1 Hrel Hset Hall.
      - simpl. inv Hset. inv Hall. eassumption.
      - simpl in Hset.
        destruct (rho1 ! a) eqn:Hget; try congruence.
        destruct (get_list xs rho1) eqn:Hgetl; try congruence.
        inv Hset. inv Hall. simpl.
        eapply cps_env_rel_extend; eauto.
    Qed.


    Lemma cps_env_rel_extend_weaken vnames vs x v v' rho :
      cps_env_rel vnames vs rho ->
      cps_val_rel v v' ->
      ~ x \in FromList vnames ->
      cps_env_rel (x :: vnames) (v :: vs) (M.set x v' rho).
    Proof.
      intros Henv Hval Hnin. unfold cps_env_rel, LambdaBoxLocal_to_LambdaANF_util.cps_env_rel, cps_env_rel' in *.
      econstructor; eauto.
      - rewrite M.gss. eexists. split; eauto.
      - eapply cps_env_rel_weaken; eauto.
    Qed.


    Lemma cps_env_rel_extend_weaken_setlists vnames vs xs vs1 vs2 rho rho' :
      cps_env_rel vnames vs rho ->
      set_lists xs vs2 rho = Some rho' ->
      Forall2 (cps_val_rel) vs1 vs2 ->
      Disjoint _ (FromList xs) (FromList vnames) ->
      NoDup xs ->
      cps_env_rel (xs ++ vnames) (vs1 ++ vs) rho'.
    Proof.
      intros.
      eapply cps_env_rel_extend_setlists; eauto.
      eapply cps_env_rel_weaken_setlists; eauto.
      eapply get_list_set_lists; eauto.
    Qed.


    Lemma nth_error_Forall2 (A B : Type) (P : A -> B -> Prop) (l : list A) (l' : list B) :
      (forall n t,
          nth_error l n = Some t ->
          exists t', nth_error l' n = Some t' /\ P t t') ->
      List.length l = List.length l' ->
      Forall2 P l l'.
    Proof.
      revert l'; induction l; intros l' Hyp Hlen.
      - destruct l'; simpl in *; try congruence. constructor.
      - destruct l'; simpl in *; try congruence. constructor.
        destruct (Hyp 0%nat a). reflexivity. destructAll. inv H. eassumption.

        eapply IHl; [ | congruence ].

        intros.

        destruct (Hyp (S n) t). eassumption. destructAll.
        eauto.
    Qed.

    Lemma cps_cvt_rel_efnlst_all_fun_name S efns vs fnames S' fdefs :
      cps_cvt_rel_efnlst S efns vs fnames cnstrs S' fdefs ->
      all_fun_name fdefs = fnames.
    Proof.
      intros Hefn. induction Hefn.
      - reflexivity.
      - simpl. congruence.
    Qed.

    Lemma cps_env_rel_extend_fundefs fnames names S1 fns Bs S2 rho vs :
      cps_env_rel names vs rho ->
      cps_fix_rel cnstrs func_tag kon_tag default_tag fnames names S1 fnames fns Bs S2 ->
      NoDup fnames ->
      NoDup names ->
      Disjoint var (FromList names :|: FromList fnames) S1 ->
      Disjoint var (FromList names) (FromList fnames) ->
      cps_env_rel (rev (all_fun_name Bs) ++ names) (make_rec_env_rev_order fns vs) (def_funs Bs Bs rho rho).
    Proof.
      intros Hrel Hfix Hnd1 Hnd2 Hdis1 Hdis2.
      unfold cps_env_rel, LambdaBoxLocal_to_LambdaANF_util.cps_env_rel, cps_env_rel'.
      destruct (make_rec_env_rev_order_app fns vs). destructAll. rewrite H.
      eapply Forall2_app.

      assert (Hlen : Datatypes.length x = Datatypes.length (all_fun_name Bs)).
      { erewrite cps_fix_rel_names; [ | eassumption ].
        rewrite H0. erewrite <- cps_fix_rel_length. reflexivity. eassumption. }

      - eapply nth_error_Forall2; [ | rewrite length_rev; eassumption ].
        intros.
        assert (exists f, nth_error (rev (all_fun_name Bs)) n = Some f).
        { eapply MRList.nth_error_Some_length in H2.
          rewrite Hlen, <- length_rev in H2. eapply nth_error_Some in H2.
          destruct (nth_error (rev (all_fun_name Bs)) n); eauto. congruence. }
        destructAll.
        eexists. split. eauto.
        eexists. split. rewrite def_funs_eq. reflexivity.
        eapply Same_set_all_fun_name. rewrite <- FromList_rev. eapply nth_error_In. eassumption.
        assert (Heq := H2).
        rewrite H1 in Heq. 2:{ rewrite <- H0. eapply MRList.nth_error_Some_length. eassumption. }
        inv Heq. econstructor; last eassumption; try eassumption.
        eapply cps_fix_rel_names in Hfix. rewrite <- Hfix.
        rewrite MRList.nth_error_rev.

        rewrite Nnat.Nat2N.id.
        replace (Datatypes.length (all_fun_name Bs) - S (efnlength fns - n - 1))%nat with n.
        2:{ rewrite <- H0, <- Hlen. eapply MRList.nth_error_Some_length in H2. lia. }
        eassumption.

        rewrite Nnat.Nat2N.id. rewrite <- H0, Hlen.
        destruct (all_fun_name Bs). now destruct n; inv H3.
        simpl. destruct n; lia.

      - eapply Forall2_monotonic_strong; [ | eassumption ].
        intros. rewrite def_funs_neq. eassumption.
        intros Hc. eapply Hdis2. constructor. eassumption.
        eapply cps_fix_rel_names in Hfix. rewrite <- Hfix.
        eapply Same_set_all_fun_name. eassumption.
    Qed.


    Lemma cps_val_rel_exists_list vs1 :
      Forall (well_formed_val) vs1 ->
      exists vs2, Forall2 (cps_val_rel) vs1 vs2.
    Proof.
      intros Hall; induction Hall.
      - eexists. constructor.
      - destructAll.
        edestruct cps_val_rel_exists.
        exact (M.empty _). (* TODO remove arg *)
        eassumption.
        eexists. constructor. eauto. eassumption.
    Qed.


    Lemma exps_wf_app es es1 es2 n :
      exps_as_list es = exps_as_list es1 ++ exps_as_list es2 ->
      exps_wf n es ->
      exps_wf n es1 /\ exps_wf n es2.
    Proof.
      revert es1 es2; induction es; intros es1 es2 Heq Hwf.
      + destruct es1; destruct es2; simpl in *; try congruence.
        split; constructor.
      + destruct es1; simpl in *; try congruence; inv Heq; inv Hwf.
        * destruct es2; inv H0.

          edestruct IHes with (es1 := enil). split. eassumption.
          split.
          constructor. constructor; eauto.
          eapply exps_to_list_inj in H2. subst; eauto.

        * edestruct IHes with (es1 := es1) (es2 := es2). eassumption.
          eassumption. split.
          constructor. eassumption. eassumption. eassumption.
    Qed.


    Context
      (dcon_to_tag_inj :
         forall tgm dc dc',
           dcon_to_tag default_tag dc tgm = dcon_to_tag default_tag dc' tgm -> dc = dc').

    Lemma cps_cvt_rel_branches_find_branch S1 brs vs k r S2 P dc e tg n :
      cps_cvt_rel_branches S1 brs vs k r cnstrs S2 P ->
      find_branch dc n brs = Some e ->
      tg = dcon_to_tag default_tag dc cnstrs ->
       exists vars S1' S2' ce ctx_p m,
         FromList vars \subset S1 /\
         List.length vars = N.to_nat n /\
         S1' \subset S1 \\ FromList vars /\
         NoDup vars /\
         ctx_bind_proj tg r vars (List.length vars) = ctx_p /\
         find_tag_nth P tg (ctx_p |[ ce ]|) m /\
         LambdaBoxLocal_to_LambdaANF.cps_cvt_rel func_tag kon_tag default_tag S1' e
                              (vars ++ vs) k cnstrs S2' ce.
    Proof.
      intros Hrel Hf Htg.
      induction Hrel.
      - inv Hf.
      - unfold find_branch in Hf. destruct (classes.eq_dec dc dc0); subst.
        + simpl in *.
          destruct (N.eq_dec n0 n); try congruence.
          inv Hf.
          do 6 eexists.
          split; [ | split ; [ | split ; [ | split; [ | split ; [ | split ] ] ] ] ]; try eassumption.
          * eapply Included_trans. eassumption.
            eapply cps_cvt_branches_subset. eassumption.
          * eapply Included_Setminus_compat; sets.
            eapply cps_cvt_branches_subset. eassumption.
          * now sets.
          * simpl. rewrite <- H2.  eapply find_tag_hd.
        + edestruct IHHrel. eassumption. reflexivity. destructAll.
          do 6 eexists.
          split; [ | split ; [ | split ; [ | split; [ | split ; [ | split ] ] ] ] ]; last eassumption; try eassumption.
          * reflexivity.
          * constructor. eassumption.
            intros Hc.
            eapply dcon_to_tag_inj in Hc. subst; eauto.
    Qed.

    Lemma cps_cvt_rel_branches_find_branch_wf S1 brs vs k r S2 P dc e n j :
      branches_wf j brs ->
      cps_cvt_rel_branches S1 brs vs k r cnstrs S2 P ->
      find_branch dc n brs = Some e ->
      exp_wf (n + j) e.
    Proof.
      intros Hwf Hrel Hf.
      induction Hrel.
      - inv Hf.
      - inv Hwf. unfold find_branch in Hf. destruct (classes.eq_dec dc dc0); subst.
        + simpl in *.
          destruct (N.eq_dec n0 n); try congruence.
        + eauto.
    Qed.


    Definition eval_fuel_many := @eval_fuel_many nat LambdaBoxLocal_resource_fuel LambdaBoxLocal_resource_trace.
    Definition eval_env_fuel := @eval_env_fuel nat LambdaBoxLocal_resource_fuel LambdaBoxLocal_resource_trace.
    Definition eval_env_step := @eval_env_step nat LambdaBoxLocal_resource_fuel LambdaBoxLocal_resource_trace.

    Lemma eval_fuel_many_length vs es vs1 f1 t1 :
      eval_fuel_many vs es vs1 f1 t1 ->
      List.length vs1 = N.to_nat (exps_length es).
    Proof.
      intros Hrel.
      induction Hrel.
      reflexivity.
      simpl. rewrite IHHrel.
      destruct (exps_length es); try lia.
      destruct p; lia.
    Qed.

    Lemma preord_exp_Eproj_red k x ctag y N e vs v rho :
      M.get y rho = Some (Vconstr ctag vs) ->
      nthN vs N = Some v ->
      preord_exp cenv one_step eq_fuel k (e, M.set x v rho) (Eproj x ctag N y e, rho).
    Proof.
      intros Hget Hnth r c1 c2 Hleq Hstep.
      do 3 eexists. split. econstructor 2. econstructor; eauto.
      split. simpl. unfold_all. lia.
      eapply preord_res_refl; tci.
    Qed.


    Lemma preord_exp_Ecase_red k rho ctag vs P e n y :
      M.get y rho = Some (Vconstr ctag vs) ->
      find_tag_nth P ctag e n ->
      preord_exp cenv one_step eq_fuel k (e, rho) (Ecase y P, rho).
    Proof.
      intros Hget Hnth r c1 c2 Hleq Hstep.
      do 3 eexists. split. econstructor 2. econstructor; eauto.
      admit. (* case consistent??? *)
      split. simpl. unfold_all. lia.
      eapply preord_res_refl; tci.
    Admitted.


    Definition eq_fuel_n (n : nat) : @PostT nat unit :=
      fun '(e1, r1, f1, t1) '(e2, r2, f2, t2) => (f1 + n)%nat = f2.


    Opaque preord_exp'.

    Lemma ctx_bind_proj_preord_exp :
      forall vars C k r n e rho rho' vs vs'  ctag,
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
        eapply preord_exp_post_monotonic.
        2:{ eapply preord_exp_refl. tci. eapply preord_env_P_refl. tci. }

        unfold eq_fuel, eq_fuel_n. intro; intros. destruct_tuples. lia.

      - destruct n; inv Heq.
        simpl in *.
        revert vs Hget Hset.
        intros vs. eapply MRList.rev_ind with (l := vs); intros.

        + eapply set_lists_length_eq in Hset.
          rewrite length_app in Hset. inv Hset. lia.

        + simpl in Hset.

          assert (Hlen : Datatypes.length (rev vars) = Datatypes.length l).
          { eapply set_lists_length_eq in Hset. rewrite !length_app in Hset. simpl in *.
            replace (@Datatypes.length map_util.M.elt) with (@Datatypes.length positive) in * by reflexivity.
            lia. }

          edestruct (@set_lists_app val). eassumption. eassumption.

          destructAll. inv H0.

          eapply preord_exp_post_monotonic.
          2:{ eapply preord_exp_trans. tci. eapply eq_fuel_idemp.

              2:{ intros m. eapply preord_exp_Eproj_red. eassumption.
                  eapply nthN_is_Some_app.
                  eapply set_lists_length_eq in Hset.
                  rewrite length_rev in *.
                  replace (@Datatypes.length map_util.M.elt) with (@Datatypes.length positive) in * by reflexivity.
                  rewrite Hlen. rewrite nthN_app_geq. simpl.

                  replace (N.of_nat (Datatypes.length l - 0) - N.of_nat (Datatypes.length l)) with 0 by lia.
                  reflexivity.
                  lia. }

              repeat normalize_sets.

              eapply IHvars with (vs := l). reflexivity. eauto.

              rewrite Nat.sub_0_r. reflexivity.

              rewrite M.gso; eauto.

              rewrite app_assoc. eassumption.

              now intros Hc; subst; eauto. eassumption. }

          { unfold comp, eq_fuel_n, eq_fuel. intro; intros. destructAll. destruct_tuples.
            unfold one_step in *. lia. }

    Qed.



    Lemma eval_fuel_many_wf vs es vs' f t :
      well_formed_env vs ->
      exps_wf (N.of_nat (List.length vs)) es ->
      eval_fuel_many vs es vs' f t ->
      Forall well_formed_val vs'.
    Proof.
      intros Hwf Hwf' Heval.
      induction Heval.
      - now constructor.
      - inv Hwf'.
        constructor; eauto.
        eapply (@eval_env_step_preserves_wf nat LambdaBoxLocal_resource_fuel LambdaBoxLocal_resource_trace).
        eassumption. reflexivity.
        eassumption. eassumption.
    Qed.


    Lemma exps_as_list_len e :
      Datatypes.length (exps_as_list e) = N.to_nat (exps_length e).
    Proof.
      induction e; simpl. congruence.
      rewrite IHe.
      destruct (exps_length e0). lia.
      destruct p; lia.
    Qed.


    Lemma find_branch_max_m_branches dc m brs e:
      find_branch dc m brs = Some e ->
      (N.to_nat m <= max_m_branches brs)%nat.
    Proof.
      revert dc m e.
      induction brs; simpl; intros dc m e' Hf. congruence.
      destruct p; simpl in *. destruct dc, d.
      destruct (inductive_dec i i0); subst.
      destruct (N.eq_dec n0 n1); subst.
      destruct (N.eq_dec n m); subst; [ | congruence ].
      lia.

      eapply IHbrs in Hf. lia.
      eapply IHbrs in Hf. lia.

    Qed.


  (** ** Correctness statements *)

  Definition cps_cvt_correct_exp (vs : fuel_sem.env) (e : expression.exp) (r : fuel_sem.result) (f t : nat) :=
    forall rho vnames k x vk e' S S' i,
      well_formed_env vs ->
      exp_wf (N.of_nat (Datatypes.length vnames)) e ->

      Disjoint _ (k |: FromList vnames) S ->
      ~ x \in k |: FromList vnames ->
      ~ k \in FromList vnames ->

      cps_env_rel vnames vs rho ->
      M.get k rho = Some vk ->

      cps_cvt_rel S e vnames k cnstrs S' e' ->

      (* Source terminates *)
      (forall v v', r = (Val v) -> cps_val_rel v v' ->
       preord_exp cenv (cps_bound f t) eq_fuel i
                  ((Eapp k kon_tag (x::nil)), (M.set x v' (M.set k vk (M.empty term.val))))
                  (e', rho)) /\
      (* SOurce diverges *)
      (r = fuel_sem.OOT ->
       exists c, (f <= c)%nat /\ bstep_fuel cenv rho e' c eval.OOT tt).




  Definition cps_cvt_correct_exp_step (vs : fuel_sem.env) (e : expression.exp) (r : fuel_sem.result) (f t : nat)  :=
    forall rho vnames k x vk e' S S' i,
      well_formed_env vs ->
      exp_wf (N.of_nat (Datatypes.length vnames)) e ->

      Disjoint _ (k |: FromList vnames) S ->
      ~ x \in k |: FromList vnames ->
      ~ k \in FromList vnames ->

      cps_env_rel vnames vs rho ->
      M.get k rho = Some vk ->

      cps_cvt_rel S e vnames k cnstrs S' e' ->

      (* Source terminates *)
      (forall v v', r = (Val v) -> cps_val_rel v v' ->
                    preord_exp cenv
                               (cps_bound (f <+> @one_i _ _ fuel_resource_LambdaBoxLocal e)
                                          (t <+> @one_i _ _ trace_resource_LambdaBoxLocal e))
                               eq_fuel i
                               ((Eapp k kon_tag (x::nil)), (M.set x v' (M.set k vk (M.empty term.val))))
                               (e', rho)) /\
      (* Source diverges *)
      (r = fuel_sem.OOT ->
       exists c, ((f <+> @one_i _ _ fuel_resource_LambdaBoxLocal e) <= c)%nat /\ bstep_fuel cenv rho e' c eval.OOT tt).




  Definition cps_cvt_correct_exps (vs : fuel_sem.env) (es : expression.exps) (vs1 : list value) (f t : nat)  :=
    forall rho vnames e' e_app S S' vs2 xs ys ks vs',
      well_formed_env vs ->
      exps_wf (N.of_nat (Datatypes.length vnames)) es ->

      Disjoint _ (FromList vnames :|: FromList xs :|: FromList ys :|: FromList ks) S ->

      Disjoint _ (FromList vnames) (FromList xs :|: FromList ys :|: FromList ks) ->
      Disjoint _ (FromList ks) (FromList xs :|: FromList ys) ->
      Disjoint _ (FromList xs) (FromList ys) ->
      NoDup xs ->

      cps_env_rel vnames vs rho ->

      Disjoint _ (occurs_free e_app) (FromList ks) ->
      (* M.get k rho = Some vk -> *)

      cps_cvt_rel_exps S es vnames e_app xs ks cnstrs S' e' ->

      Forall2 (cps_val_rel) vs1 vs2 ->
      get_list ys rho = Some vs' ->

      exists rho1,
        set_lists (ys ++ xs) (vs' ++ vs2) rho = Some rho1 /\
        forall i,
          preord_exp cenv (cps_bound f (t <+> (2 * Datatypes.length (exps_as_list es))%nat))
                     eq_fuel i (e_app, rho1) (e', rho).



    Lemma cps_cvt_correct :
      forall vs e r f t, eval_env_fuel vs e r f t -> cps_cvt_correct_exp vs e r f t.
    Proof.
      eapply eval_env_fuel_ind' with (P1 := cps_cvt_correct_exp)
                                     (P0 := cps_cvt_correct_exps)
                                     (P := cps_cvt_correct_exp_step).
      - (* Con_e terminates *)
        intros es vs1 vs dc f1 t1 Heval IH.
        intros rho vnames k x vk e' S S' i Hwfenv Hwf Hdis Hnin1 Hnin2 Hcenv Hget Hcps.
        inv Hwf. inv Hcps. split; [ | congruence ].

        intros v1 v2 Heq Hrel. inv Heq. inv Hrel.

        eapply preord_exp_post_monotonic.

        2:{ edestruct IH with (ys := @nil var) (vs' := @nil val) (rho := rho);
            [ | | | | | | | | | eassumption | eassumption | | ].
            - eassumption.
            - eassumption.
            - repeat normalize_sets. eapply Union_Disjoint_l; xsets.
            - repeat normalize_sets.
              eapply Disjoint_Included; [ | | eapply Hdis ]; sets.
              eapply Union_Included; eapply Included_trans; eauto; sets.
            - repeat normalize_sets.
              eapply Disjoint_Included_l; eauto; sets.
            - repeat normalize_sets; sets.
            - eassumption.
            - eassumption.
            - repeat normalize_occurs_free. repeat normalize_sets.
              eapply Union_Disjoint_l.
              now eapply Disjoint_Included_r; eauto; sets.
              rewrite Setminus_Union_distr. rewrite Setminus_Same_set_Empty_set. normalize_sets.
              now eapply Disjoint_Included_r; eauto; sets.
            - reflexivity.
            - destructAll.

              eapply preord_exp_trans. tci. eapply eq_fuel_idemp.

              2:{ intros m. simpl. eapply H0. }

              eapply preord_exp_trans. tci. eapply eq_fuel_idemp.

              2:{ intros m. eapply preord_exp_Econstr_red.
                  eapply get_list_set_lists. eassumption.
                  eassumption. }

              eapply preord_exp_app_compat with (P2 := eq_fuel).
              now eapply eq_fuel_compat.
              now eapply eq_fuel_compat.

              eapply preord_var_env_extend_neq.
              eapply preord_var_env_get.
              2:{ eapply M.gss. }
              2:{ erewrite <- set_lists_not_In; [ | eassumption | ].
                  eassumption.
                  simpl. intros Hc; subst. eapply H4 in Hc. inv Hc. now eapply Hdis; eauto. }

              eapply preord_val_refl. now tci.
              now intros Hc; subst; eauto.
              intros Hc; subst; eapply Hdis; now eauto.
              constructor.
              eapply preord_var_env_extend_eq.
              eapply preord_val_refl. now tci. now constructor. }

          (* Invariant composition *)
          { unfold inclusion, comp, eq_fuel, one_step, cps_bound, one_i.
            intros [[[? ?] ?] ?] [[[? ?] ?] ?] ?.
            destructAll. destruct_tuples. subst. simpl in *.
            unfold fuel_exp, trace_exp. lia. }

      - (* Con_e OOT *)
        intros es es1 es2 e vs1 vs dc fs f1 t1 ts (* TODO fix order *) Heq Heval IH Hoot IHoot.
        intros rho vnames k x vk e' S S' i Hwfenv Hwf Hdis Hnin1 Hnin2 Hcenv Hget Hcps.
        inv Hwf. inv Hcps. split. congruence.

        intros _.

        assert (Hwf := H1). eapply exps_wf_app with (es2 := econs e es2) in H1; [ | eassumption ].
        destruct H1 as [ H1 Hwf' ].

        edestruct cps_cvt_rel_exps_app with (es2 := econs e es2). eassumption. eassumption.
        destructAll.

        assert (Hex :  exists vs2, Forall2 (cps_val_rel) vs1 vs2).
        { eapply cps_val_rel_exists_list. eapply eval_fuel_many_wf in Heval.
          eassumption. eassumption.
          eapply Forall2_length in Hcenv. rewrite Hcenv. eassumption. }
        destructAll.

        unfold cps_cvt_correct_exps in *.
        assert (Hexps := H9).

        eapply IH with (rho := rho) (ys := []) (vs' := []) in H9; clear IH; [ | | | | | | | | | | eassumption | reflexivity ]; eauto.
        + destructAll.

          inv H7.

          assert (Hex' : exists z, ~ In var (k1 |: FromList vnames) z).
          { eapply ToMSet_non_member. tci. } destructAll.

          set (rho'' := (M.set k1 (Vfun x8 (Fcons k1 kon_tag [x9] es' Fnil) k1) x8)).

          eapply IHoot with (rho := rho'') in H13.

          * destructAll.
            assert (Hoot' : bstep_fuel cenv x8 (Efun (Fcons k1 kon_tag [x9] es' Fnil) e'0) (x4 + 1)%nat OOT tt).
            { replace tt with (tt <+> tt) by reflexivity. econstructor 2. econstructor. simpl. eassumption. }

            edestruct H9. reflexivity. eassumption. destructAll.
            eexists. split.
            2:{ replace tt with (tt <+> tt).
                destruct x6; [ | contradiction ]. destruct x11. eassumption.
                reflexivity. }

            simpl. unfold cps_bound, one, one_i in *; simpl; unfold_all.
            unfold fuel_exp. simpl. lia.

          * eassumption.
          * eassumption.
          * inv Hwf'. eassumption.
          * eapply Disjoint_Included_r. eassumption.
            eapply Union_Disjoint_l.
            repeat rewrite FromList_app, FromList_cons at 1. now sets.
            xsets.
          * eassumption.
          * intros Hc. eapply Hdis. constructor. now right.
            eapply H5.
            repeat rewrite FromList_app, FromList_cons at 1. now sets.
          * unfold rho''. eapply cps_env_rel_weaken.
            simpl in *.
            eapply cps_env_rel_weaken_setlists; [ | eauto | ].
            repeat eapply cps_env_rel_weaken. eassumption.
            eapply Disjoint_sym. eapply Disjoint_Included; [ | | eapply Hdis ]; sets.
            eapply Included_trans.
            eapply Included_trans; [ | eapply H4 ].
            repeat rewrite FromList_app, FromList_cons at 1. now sets. now sets.
            intros Hc.
            eapply Hdis. constructor. now right.
            eapply H5.
            repeat rewrite FromList_app, FromList_cons at 1. now sets.
          * unfold rho''. rewrite M.gss. reflexivity.
          * reflexivity.

        + repeat rewrite FromList_app; rewrite FromList_nil.
          eapply Union_Disjoint_l; sets.
          eapply Union_Disjoint_l; sets.
          eapply Union_Disjoint_l; sets.

        + eapply Disjoint_Included; [ | | eapply Hdis ]; sets. do 2 normalize_sets.
          eapply Union_Included.

          eapply Included_trans.
          eapply Included_trans; [ | eapply H4 ].
          repeat rewrite FromList_app.  now sets. now sets.


          eapply Included_trans.
          eapply Included_trans; [ | eapply H5 ].
          repeat rewrite FromList_app.  now sets. now sets.

        + eapply Disjoint_Union_l.
          rewrite <- FromList_app. eapply Disjoint_Included_l. eassumption.
          rewrite FromList_app, FromList_nil. sets.

        + normalize_sets. sets.
        + eapply NoDup_cons_l. eassumption.

        + eapply Disjoint_Included_l.
          eapply cps_cvt_exps_fv. eassumption.
          repeat normalize_occurs_free. normalize_sets.
          eapply Disjoint_sym. eapply Disjoint_Union_l. rewrite <- FromList_app with (l2 := x6).
          rewrite Union_commut. eapply Union_Disjoint_r.
          * eapply Disjoint_Included_l. eassumption. normalize_sets.
            eapply Setminus_Disjoint_preserv_r.
            eapply Union_Disjoint_r. now sets.
            rewrite !Setminus_Union_distr. rewrite Setminus_Same_set_Empty_set.
            rewrite Setminus_Empty_set_abs_r. rewrite !Union_Empty_set_neut_l.
            eapply Disjoint_sym.
            eapply Disjoint_Included; [ | | eapply Hdis ]; sets.

          * eapply Union_Disjoint_r.

            eapply Disjoint_Included_l. eassumption. now xsets.

            eapply Disjoint_Included_r. eassumption. now xsets.

      - (* App_e Clos_v *)
        intros e1 e2 e1' v2 r' na vs vs' f1 f2 f3 t1 t2 t3 Heval1 IH1 Heval2 IH2 Heval3 IH3.
        intros rho vnames k x vk e' S S' f Hwfenv Hwf Hdis Hnin1 Hnin2 Hcenv Hget Hcps.
        inv Hwf. inv Hcps.

        assert (Hlen : Datatypes.length vs = Datatypes.length vnames).
        { unfold well_formed_in_env. eapply Forall2_length. eassumption. }

        assert (Hwfv2 : well_formed_val v2).
        { eapply (@eval_env_step_preserves_wf nat LambdaBoxLocal_resource_fuel LambdaBoxLocal_resource_trace);
            [ | reflexivity | | ]. eassumption.
          eassumption. unfold well_formed_in_env. rewrite Hlen. eassumption. }

        assert (Hwfcl : well_formed_val (Clos_v vs' na e1')).
        { eapply (@eval_env_step_preserves_wf nat LambdaBoxLocal_resource_fuel LambdaBoxLocal_resource_trace);
            [ | reflexivity | | ]. eassumption.
          eassumption. unfold well_formed_in_env. rewrite Hlen. eassumption. }

        assert (Hex : exists v', cps_val_rel (Clos_v vs' na e1') v').
        { eapply cps_val_rel_exists. eassumption. eassumption. }

        assert (Hex' : exists v', cps_val_rel v2 v').
        { eapply cps_val_rel_exists. eassumption. (* TODO remove arg *) eassumption. }

        destructAll. inv H0.

        (* Prove that whole CPS-term is related to the body of the app -- useful for both cases *)
        assert (Heq : forall m, preord_exp' cenv (preord_val cenv)
                                            (cps_bound (f1 <+> f2 <+> @one_i _ _ fuel_resource_LambdaBoxLocal (e1 $ e2))
                                                       (t1 <+> t2 <+> @one_i _ _ trace_resource_LambdaBoxLocal (e1 $ e2)))
                                            eq_fuel m
                                            (e', M.set k0 vk (M.set x4 x0 (M.set f0 (Vfun rho0 (Fcons f0 func_tag [k0; x4] e' Fnil) f0) rho0)))
                                            (Efun (Fcons k1 kon_tag [x1] (Efun (Fcons k2 kon_tag [x2] (Eapp x1 func_tag [k; x2]) Fnil) e2') Fnil)
                                                  e1'0, rho)).
        { intros j. eapply preord_exp_post_monotonic.
          2:{ eapply preord_exp_trans. tci. eapply eq_fuel_idemp.

              2:{ intros m. eapply preord_exp_Efun_red. }
              assert (Hex' : exists z, ~ In var (k1 |: FromList vnames) z).
              { eapply ToMSet_non_member. tci. } destructAll.

              eapply preord_exp_trans. tci. eapply eq_fuel_idemp.

              2:{ intros m. simpl. eapply IH1; [ | | | | | | |  eassumption | reflexivity | ].
                  - eassumption.
                  - eassumption.
                  - eapply Union_Disjoint_l; sets.
                    eapply Disjoint_Included; [ | | eapply Hdis ]; sets.
                  - eassumption.
                  - intros Hc. inv_setminus. eapply Hdis; eauto.
                  - eapply cps_env_rel_weaken. eassumption.
                    inv_setminus. intros Hc. eapply Hdis; eauto.
                  - rewrite M.gss. reflexivity.
                  - econstructor; eauto. }

              eapply preord_exp_trans. tci. eapply eq_fuel_idemp.

              2:{ intros m. eapply preord_exp_Eapp_red.
                  - rewrite M.gso; eauto. rewrite M.gss. reflexivity. intros Hc; subst; eauto.
                  - simpl. rewrite Coqlib.peq_true. reflexivity.
                  - simpl. rewrite M.gss. reflexivity.
                  - simpl. reflexivity. }

              eapply preord_exp_trans. tci. eapply eq_fuel_idemp.

              2:{ intros m. eapply preord_exp_Efun_red. } simpl.

              assert (Hex' : exists z, ~ In var (k2 |: FromList vnames) z).
              { eapply ToMSet_non_member. tci. } destructAll.

              assert (HS2 := H8). eapply cps_cvt_rel_subset in HS2.

              eapply preord_exp_trans. tci. eapply eq_fuel_idemp.


              2:{ intros m. simpl. eapply IH2 ; [ | | | | | | | eassumption | reflexivity | eassumption ].
                  - eassumption.
                  - eassumption.
                  - eapply Disjoint_Included_r. eassumption.
                    eapply Union_Disjoint_l; sets.
                    eapply Setminus_Disjoint_preserv_r.
                    eapply Disjoint_Included ; [ | | eapply Hdis ]; sets.
                  - eassumption.
                  - inv_setminus. intros Hin. eapply Hdis. eauto.
                  - repeat eapply cps_env_rel_weaken. eassumption.
                    inv_setminus. intros Hc. now eapply Hdis; eauto.
                    intros Hc. now eapply Hdis; eauto.
                    inv_setminus. intros Hin. eapply Hdis. eauto.
                  - rewrite M.gss. reflexivity. }

              eapply preord_exp_trans. tci. eapply eq_fuel_idemp.

              2:{ intros m. eapply preord_exp_Eapp_red.
                  - rewrite M.gso; eauto. rewrite M.gss. reflexivity. intros Hc; subst; eauto.
                  - simpl. rewrite Coqlib.peq_true. reflexivity.
                  - simpl. rewrite M.gss. reflexivity.
                  - simpl. reflexivity. }

              eapply preord_exp_Eapp_red.
              - rewrite M.gso; eauto. rewrite M.gso; eauto.
                rewrite M.gss. reflexivity.
                intros Hc; subst. now inv_setminus; eauto.
                intros Hc; subst. now inv_setminus; eauto.
              - simpl. rewrite Coqlib.peq_true. reflexivity.
              - simpl. rewrite M.gso.
                simpl. rewrite M.gso.
                simpl. rewrite M.gso.
                simpl. rewrite M.gso. rewrite M.gss.
                rewrite Hget. reflexivity.
                intros Hc; subst. inv_setminus. now eapply Hdis; eauto.
                intros Hc; subst. now eapply Hdis; eauto.
                intros Hc; subst. inv_setminus. now eapply Hdis; eauto.
                intros Hc; subst. inv_setminus. now eapply Hdis; eauto.
              - simpl. reflexivity. }

          (* Invariant composition *)
          { unfold inclusion, comp, eq_fuel, one_step, cps_bound, one_i.
            intros [[[? ?] ?] ?] [[[? ?] ?] ?] ?.
            destructAll. destruct_tuples. subst. simpl. unfold fuel_exp, trace_exp.
            lia. } }

        split.

        (* Termination *)
        { intros v v' Heq1 Hvrel. subst.

          assert (Hex : exists x, ~ In var (k0 |: FromList (x4 :: names)) x).
          { eapply ToMSet_non_member. tci. } destructAll.

          eapply preord_exp_post_monotonic.

          2:{ eapply preord_exp_trans; [ | | | eassumption ]. tci. eapply eq_fuel_idemp.

              eapply preord_exp_trans. tci. eapply eq_fuel_idemp.

              2:{ intros m. eapply IH3 with (x := x3); [ | | | | | | | eassumption | reflexivity  | eapply Hvrel ].
                  - inv Hwfcl. constructor; eauto.
                  - inv Hwfcl. specialize (H20 v). simpl Datatypes.length in *.
                    erewrite <- Forall2_length. eassumption. eassumption.
                  - repeat normalize_sets. sets.
                  - eassumption.
                  - repeat normalize_sets. inv_setminus. intros Hc. inv Hc; eauto. inv H4; eauto.
                  - eapply cps_env_rel_weaken; eauto.
                    eapply cps_env_rel_extend_weaken; eauto.
                    eapply cps_env_rel_weaken; eauto.
                    repeat normalize_sets. intros Hc. inv Hc; eauto. inv H7; eauto.
                  - rewrite M.gss. reflexivity. }

              eapply preord_exp_app_compat with (P2 := eq_fuel).
              now eapply eq_fuel_compat.
              now eapply eq_fuel_compat.

              eapply preord_var_env_extend_neq.
              eapply preord_var_env_extend_eq.
              eapply preord_val_refl. now tci.
              now intros Hc; subst; eauto.
              now intros Hc; subst; eauto.
              constructor.
              eapply preord_var_env_extend_eq.
              eapply preord_val_refl. now tci. now constructor. }

          (* Invariant composition *)
          { unfold inclusion, comp, eq_fuel, one_step, cps_bound, one_i.
            intros [[[? ?] ?] ?] [[[? ?] ?] ?] ?.
            destructAll. destruct_tuples. subst. simpl in *. lia. } }

        (* OOT *)
        { intros ?; subst.
          assert (Hex : exists x, ~ In var (k0 |: FromList (x4 :: names)) x).
          { eapply ToMSet_non_member. tci. } destructAll.

          edestruct IH3 with (x := x3) (rho :=  M.set k0 vk (M.set x4 x0 (M.set f0 (Vfun rho0 (Fcons f0 func_tag [k0; x4] e' Fnil) f0) rho0)));
            [ | | | | | | | eassumption | ].
          - inv Hwfcl. constructor; eauto.
          - inv Hwfcl. specialize (H20 v2). simpl Datatypes.length in *.
            erewrite <- Forall2_length. eassumption. eassumption.
          - repeat normalize_sets. sets.
          - eassumption.
          - repeat normalize_sets. sets.
            intros Hc; inv Hc; eauto. inv H7; eauto.
          - eapply cps_env_rel_weaken; eauto.
            eapply cps_env_rel_extend_weaken; eauto.
            eapply cps_env_rel_weaken; eauto.
            repeat normalize_sets. intros Hc; inv Hc. inv H7; eauto. eapply H16; eauto.
          - rewrite M.gss. reflexivity.
          - destruct (H9 ltac:(reflexivity)). destructAll. eapply Heq in H17; [ | reflexivity ]. destructAll.
            destruct x6; try contradiction. destruct x8. eexists. split; [ | eassumption ].

            unfold one_i in *. simpl in *. lia. }

      - (* App_e Clos_v, OOT 1 *)
        intros e1 e2 vs f1 t1 Hoot IH.
        intros rho vnames k x vk e' S S' f Hwfenv Hwf Hdis Hnin1 Hnin2 Hcenv Hget Hcps. split.
        congruence.
        intros _. inv Hcps. inv Hwf.
        set (rho' := M.set k1 (Vfun rho
                                    (Fcons k1 kon_tag [x1]
                                           (Efun
                                              (Fcons k2 kon_tag [x2] (Eapp x1 func_tag [k; x2]) Fnil)
                                              e2') Fnil) k1) rho).
        assert (Hex : exists x, ~ In var (k1 |: FromList vnames) x).
        { eapply ToMSet_non_member. tci. } destructAll.

        edestruct IH with (rho := rho'); [ | | | | | | | eassumption | ].
        + eassumption.
        + eassumption.
        + eapply Union_Disjoint_l; sets.
          eapply Disjoint_Included; [ | | eapply Hdis ]; sets.
        + eassumption.
        + intros Hc; inv H2; eapply Hdis; eauto.
        + unfold rho'.
          eapply cps_env_rel_weaken; try eassumption.
          intros Hc. inv H2. eapply Hdis; eauto.
        + unfold rho'. rewrite M.gss. reflexivity.
        + destruct H5. reflexivity. destructAll. eexists (x3 + 1)%nat. split.
          unfold one_i. simpl. unfold fuel_exp. lia.
          replace tt with (tt <+> tt) by reflexivity. eapply BStepf_run. econstructor.
          simpl. eassumption.

      - (* App_e Clos_v, OOT 2 *)
        intros e1 e2 v1 vs2 f1 f2 t1 t2 He1 IH1 Hoot IH2.
        intros rho vnames k x vk e' S S' f Hwfenv Hwf Hdis Hnin1 Hnin2 Hcenv Hget Hcps. split.
        congruence.
        intros _. inv Hcps. inv Hwf.

        assert (Hlen : Datatypes.length vs2 = Datatypes.length vnames).
        { unfold well_formed_in_env. eapply Forall2_length. eassumption. }

        assert (Hwfv2 : well_formed_val v1).
        { eapply (@eval_env_step_preserves_wf nat LambdaBoxLocal_resource_fuel LambdaBoxLocal_resource_trace);
            [ | reflexivity | | ]. eassumption.
          eassumption. unfold well_formed_in_env. rewrite Hlen. eassumption. }

        assert (Hex' : exists v', cps_val_rel v1 v').
        { eapply cps_val_rel_exists. eassumption. (* TODO remove arg *) eassumption. } destructAll.

        set (rho' := M.set k2 (Vfun (M.set x1 x0 (M.set k1 (Vfun rho (Fcons k1 kon_tag [x1] (Efun (Fcons k2 kon_tag [x2] (Eapp x1 func_tag [k; x2]) Fnil) e2') Fnil) k1) rho)) (Fcons k2 kon_tag [x2] (Eapp x1 func_tag [k; x2]) Fnil) k2)
                           (M.set x1 x0
                                  (M.set k1 (Vfun rho (Fcons k1 kon_tag [x1]
                                                             (Efun (Fcons k2 kon_tag [x2] (Eapp x1 func_tag [k; x2])
                                                                          Fnil) e2') Fnil) k1) rho))).

        assert (Heq : forall m, preord_exp' cenv (preord_val cenv)
                                            (cps_bound (f1 <+> @one_i _ _ fuel_resource_LambdaBoxLocal (e1 $ e2))
                                                       (t1 <+> @one_i _ _ trace_resource_LambdaBoxLocal (e1 $ e2)))
                                            eq_fuel m
                                            (e2', rho')
                                            (Efun (Fcons k1 kon_tag [x1] (Efun (Fcons k2 kon_tag [x2] (Eapp x1 func_tag [k; x2]) Fnil) e2') Fnil)
                                                  e1', rho)).
        { intros j. eapply preord_exp_post_monotonic.
          2:{ eapply preord_exp_trans. tci. eapply eq_fuel_idemp.

              2:{ intros m. eapply preord_exp_Efun_red. }
              assert (Hex' : exists z, ~ In var (k1 |: FromList vnames) z).
              { eapply ToMSet_non_member. tci. } destructAll.

              eapply preord_exp_trans. tci. eapply eq_fuel_idemp.

              2:{ intros m. simpl. eapply IH1; [ | | | | | | | eassumption | reflexivity | ].
                  - eassumption.
                  - eassumption.
                  - eapply Union_Disjoint_l; sets.
                    eapply Disjoint_Included; [ | | eapply Hdis ]; sets.
                  - eassumption.
                  - intros Hc. inv H2. eapply Hdis; eauto.
                  - eapply cps_env_rel_weaken. eassumption.
                    inv H2. intros Hc. eapply Hdis; eauto.
                  - rewrite M.gss. reflexivity.
                  - eassumption. }

              eapply preord_exp_trans. tci. eapply eq_fuel_idemp.

              2:{ intros m. eapply preord_exp_Eapp_red.
                  - rewrite M.gso; eauto. rewrite M.gss. reflexivity. intros Hc; subst; eauto.
                  - simpl. rewrite Coqlib.peq_true. reflexivity.
                  - simpl. rewrite M.gss. reflexivity.
                  - simpl. reflexivity. }

              eapply preord_exp_trans. tci. eapply eq_fuel_idemp.

              2:{ intros m. eapply preord_exp_Efun_red. } simpl.

              eapply preord_exp_refl. tci.
              eapply preord_env_P_refl. tci. }

          (* Invariant composition *)
          { unfold inclusion, comp, eq_fuel, one_step, cps_bound, one_i.
            intros [[[? ?] ?] ?] [[[? ?] ?] ?] ?.
            destructAll. destruct_tuples. subst. simpl. unfold fuel_exp, trace_exp. lia. } }


        assert (Hex : exists x, ~ In var (k2 |: FromList (vnames)) x).
        { eapply ToMSet_non_member. tci. } destructAll.

        assert (HS2 := H6). eapply cps_cvt_rel_subset in HS2.

        edestruct IH2 with (rho := rho'); [ | | | | | | | eassumption | ].
        + eassumption.
        + eassumption.
        + repeat normalize_sets.
          eapply Disjoint_Included_r. eassumption.
          eapply Union_Disjoint_l; sets.
          repeat eapply Setminus_Disjoint_preserv_r. sets.
        + eassumption.
        + inv_setminus. intros Hc; eauto. eapply Hdis; eauto.
        + inv_setminus.
          repeat eapply cps_env_rel_weaken; eauto; now intros Hc; eapply Hdis; eauto.
        + unfold rho'. rewrite M.gss. reflexivity.
        + destruct (H9 ltac:(reflexivity)). destructAll. eapply Heq in H11; [ | reflexivity ]. destructAll.
          destruct x5; try contradiction. destruct x7. eexists. split; [ | eassumption ].
          unfold one_i in *. simpl in *. lia.

      - (* Let_e *)
        intros e1 e2 v1 r vs na f1 f2 t1 t2 He1 IH1 He2 IH2.
        intros rho vnames k x vk e' S S' f Henvwf Hwf Hdis Hnin1 Hnin2 Hcenv Hstep Hcps. inv Hcps. inv Hwf.


        assert (Hlen : Datatypes.length vs = Datatypes.length vnames).
        { unfold well_formed_in_env. eapply Forall2_length. eassumption. }

        assert (Hwfv2 : well_formed_val v1).
        { eapply (@eval_env_step_preserves_wf nat LambdaBoxLocal_resource_fuel LambdaBoxLocal_resource_trace);
            [ | reflexivity | | ]. eassumption.
          eassumption. unfold well_formed_in_env. rewrite Hlen. eassumption. }

        assert (Hex' : exists v', cps_val_rel v1 v').
        { eapply cps_val_rel_exists. eassumption. (* TODO remove arg *) eassumption. } destructAll.

        (* Prove that whole CPS-term is related to the body of the app -- useful for both cases *)
        assert (Heq : forall m, preord_exp' cenv (preord_val cenv)
                                            (cps_bound (f1 <+> @one_i _ _ fuel_resource_LambdaBoxLocal (Let_e na e1 e2))
                                                       (t1 <+> @one_i _ _ trace_resource_LambdaBoxLocal (Let_e na e1 e2)))
                                            eq_fuel m
                                            (e2', map_util.M.set x1 x0 (M.set k1 (Vfun rho (Fcons k1 kon_tag [x1] e2' Fnil) k1) rho))
                                            (Efun (Fcons k1 kon_tag [x1] e2' Fnil) e1', rho)).
        { intros j. eapply preord_exp_post_monotonic.
          2:{ eapply preord_exp_trans. tci. eapply eq_fuel_idemp.

              2:{ intros m. eapply preord_exp_Efun_red. }
              assert (Hex' : exists z, ~ In var (k1 |: FromList vnames) z).
              { eapply ToMSet_non_member. tci. } destructAll.

              eapply preord_exp_trans. tci. eapply eq_fuel_idemp.

              2:{ intros m. simpl. eapply IH1; [ | | | | | | | eassumption | reflexivity | ].
                  - eassumption.
                  - eassumption.
                  - eapply Disjoint_Included_r. eapply cps_cvt_exp_subset. eassumption.
                    eapply Union_Disjoint_l; sets.
                  - eassumption.
                  - intros Hc. inv H4. eapply Hdis; eauto.
                  - eapply cps_env_rel_weaken; try eassumption.
                    intros Hc. inv H4. eapply Hdis; eauto.
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
            destructAll. destruct_tuples. subst. simpl. unfold fuel_exp, trace_exp.
            lia. } }

        assert (Hex : exists x, ~ In var (k |: FromList (x1 :: vnames)) x).
        { eapply ToMSet_non_member. tci. } destructAll.

        split.
        (* Termination *)
        { intros v v' Heq1 Hvrel. subst.

          eapply preord_exp_post_monotonic.

          2:{ eapply preord_exp_trans; [ | | | eassumption ]. tci. eapply eq_fuel_idemp.

              eapply preord_exp_trans. tci. eapply eq_fuel_idemp.

              2:{ intros m. eapply IH2; [ | | | | | | | eassumption | reflexivity | eassumption ].
                  - constructor; eauto.
                  - simpl Datatypes.length. rewrite Nnat.Nat2N.inj_succ, <- OrdersEx.N_as_OT.add_1_l. eassumption.
                  - repeat normalize_sets. eapply Union_Disjoint_l; sets.
                    eapply Union_Disjoint_l; sets.
                  - eassumption.
                  - repeat normalize_sets. intros Hc; inv Hc; eauto. inv H1.
                    eapply Hdis. eauto.
                  - eapply cps_env_rel_extend_weaken; eauto.
                    eapply cps_env_rel_weaken; eauto.
                    intros Hc. inv H4. eapply Hdis; eauto.
                    intros Hc. eapply Hdis; eauto.
                  - rewrite !M.gso. eassumption.
                    intros Hc; subst; inv H4; eapply Hdis; eauto.
                    intros Hc; subst; inv H4; eapply Hdis; eauto. }

              eapply preord_exp_app_compat with (P2 := eq_fuel).
              now eapply eq_fuel_compat.
              now eapply eq_fuel_compat.

              eapply preord_var_env_extend_neq.
              eapply preord_var_env_extend_eq.
              eapply preord_val_refl. now tci.
              now intros Hc; subst; eauto.
              now intros Hc; subst; eauto.
              constructor.
              eapply preord_var_env_extend_eq.
              eapply preord_val_refl. now tci. now constructor. }

          (* Invariant composition *)
          { unfold inclusion, comp, eq_fuel, one_step, cps_bound, one_i.
            intros [[[? ?] ?] ?] [[[? ?] ?] ?] ?.
            destructAll. destruct_tuples. subst. simpl in *. unfold fuel_exp, trace_exp in *. lia. } }

        (* OOT *)
        { intros ?; subst.

          edestruct IH2 with (x := x2) (rho := M.set x1 x0 (M.set k1 (Vfun rho (Fcons k1 kon_tag [x1] e2' Fnil) k1) rho));
            [ | | | | | | | eassumption | ].
          - constructor; eauto.
          - simpl Datatypes.length. rewrite Nnat.Nat2N.inj_succ, <- OrdersEx.N_as_OT.add_1_l. eassumption.
          - repeat normalize_sets.
            eapply Union_Disjoint_l; sets.
            eapply Union_Disjoint_l; sets.
          - eassumption.
          - repeat normalize_sets. sets.
            intros Hc; inv Hc; eauto. inv H1. eapply Hdis; eauto.
          - eapply cps_env_rel_extend_weaken; eauto.
            eapply cps_env_rel_weaken; eauto.
            intros Hc. inv H4; eapply Hdis; eauto.
            intros Hc. inv H4; eapply Hdis; eauto.
          - rewrite !M.gso. eassumption.
            (* TODO tactic to do these + hint constructor *)
            intros Hc; subst; inv H4; eapply Hdis; eauto.
            intros Hc; subst; inv H4; eapply Hdis; eauto.
          - destruct (H5 ltac:(reflexivity)). destructAll. eapply Heq in H8; [ | reflexivity ]. destructAll.
            destruct x4; try contradiction. destruct x6. eexists. split; [ | eassumption ].

            unfold one_i in *. simpl in *. lia. }

      - (* Let_e, OOT *)
        intros e1 e2 vs na f1 t1 Hoot IH.
        intros rho vnames k x vk e' S S' f Hwfenv Hwf Hdis Hnin1 Hnin2 Hcenv Hget Hcps. split.
        congruence.
        intros _. inv Hcps. inv Hwf.
        set (rho' := M.set k1 (Vfun rho (Fcons k1 kon_tag [x1] e2' Fnil) k1) rho).

        assert (HS2 := H10). eapply cps_cvt_rel_subset in HS2.

        assert (Hex : exists x, ~ In var (k1 |: FromList vnames) x).
        { eapply ToMSet_non_member. tci. } destructAll.

        edestruct IH with (rho := rho'); [ | | | | | | | eassumption | ].
        + eassumption.
        + eassumption.
        + inv H4. eapply Disjoint_Included_r. eassumption. sets.
          eapply Union_Disjoint_l; sets.
        + eassumption.
        + intros Hc; inv H4; eapply Hdis; eauto.
        + unfold rho'.
          eapply cps_env_rel_weaken; try eassumption.
          intros Hc. inv H4. eapply Hdis; eauto.
        + unfold rho'. rewrite M.gss. reflexivity.
        + destruct H1. reflexivity. destructAll. eexists (x2 + 1)%nat. split.
          unfold one_i. simpl. unfold fuel_exp, trace_exp. lia.
          replace tt with (tt <+> tt) by reflexivity. eapply BStepf_run. econstructor; eauto.

      - (* App_e, ClosFix_v *)
        intros e1 e2 e1' vs1 vs2 vs3 n na fns v2 r f1 f2 f3 t1 t2 t3  Heval1 IH1 Hnth Hrec Heval2 IH2 Heval3 IH3.
        intros rho vnames k x vk e' S S' f Hwfenv Hwf Hdis Hnin1 Hnin2 Hcenv Hget Hcps.
        inv Hcps.  inv Hwf.

        assert (Hlen : Datatypes.length vs1 = Datatypes.length vnames).
        { unfold well_formed_in_env. eapply Forall2_length. eassumption. }

        assert (Hwfv2 : well_formed_val v2).
        { eapply (@eval_env_step_preserves_wf nat LambdaBoxLocal_resource_fuel LambdaBoxLocal_resource_trace);
            [ | reflexivity | | ]. eassumption.
          eassumption. unfold well_formed_in_env. rewrite Hlen. eassumption. }

        assert (Hwfcl : well_formed_val (ClosFix_v vs2 fns n)).
        { eapply (@eval_env_step_preserves_wf nat LambdaBoxLocal_resource_fuel LambdaBoxLocal_resource_trace);
            [ | reflexivity | | ]. eassumption.
          eassumption. unfold well_formed_in_env. rewrite Hlen. eassumption. }

        assert (Hex : exists v', cps_val_rel (ClosFix_v vs2 fns n) v').
        { eapply cps_val_rel_exists. eassumption. eassumption. }

        assert (Hex' : exists v', cps_val_rel v2 v').
        { eapply cps_val_rel_exists. eassumption. (* TODO remove arg *) eassumption. }

        destructAll. inv H0.

        edestruct LambdaBoxLocal_to_LambdaANF_util.cps_fix_rel_exists. eassumption. eassumption. eassumption.
        destruct H0 as (y1 & na' & e3 & e3' & Hu). destructAll.
        repeat subst_exp.
        (* Prove that whole CPS-term is related to the body of the app -- useful for both cases *)
        assert (Heq : forall m, preord_exp' cenv (preord_val cenv)
                                            (cps_bound (f1 <+> f2 <+> @one_i _ _ fuel_resource_LambdaBoxLocal (e1 $ e2))
                                                       (t1 <+> t2 <+> @one_i _ _ trace_resource_LambdaBoxLocal (e1 $ e2)))
                                            eq_fuel m
                                            (e3', (map_util.M.set x3 vk (map_util.M.set y1 x0 (def_funs Bs Bs rho0 rho0))))
                                            (Efun (Fcons k1 kon_tag [x1] (Efun (Fcons k2 kon_tag [x2] (Eapp x1 func_tag [k; x2]) Fnil) e2') Fnil) e1'0,
                                             rho)).
        { intros j. eapply preord_exp_post_monotonic.
          2:{ eapply preord_exp_trans. tci. eapply eq_fuel_idemp.

              2:{ intros m. eapply preord_exp_Efun_red. }
              assert (Hex' : exists z, ~ In var (k1 |: FromList vnames) z).
              { eapply ToMSet_non_member. tci. } destructAll.

              eapply preord_exp_trans. tci. eapply eq_fuel_idemp.

              2:{ intros m. simpl. eapply IH1; [ | | | | | | | eassumption | reflexivity | ].
                  - eassumption.
                  - eassumption.
                  - eapply Union_Disjoint_l; sets.
                    eapply Disjoint_Included; [ | | eapply Hdis ]; now sets.
                  - eassumption.
                  - intros Hc. inv H2. eapply Hdis; eauto.
                  - eapply cps_env_rel_weaken; try eassumption.
                    intros Hc. inv H2; eapply Hdis; eauto.
                  - rewrite M.gss. reflexivity.
                  - econstructor; eauto. }

              eapply preord_exp_trans. tci. eapply eq_fuel_idemp.

              2:{ intros m. eapply preord_exp_Eapp_red.
                  - rewrite M.gso; eauto. rewrite M.gss. reflexivity. intros Hc; subst; eauto.
                  - simpl. rewrite Coqlib.peq_true. reflexivity.
                  - simpl. rewrite M.gss. reflexivity.
                  - simpl. reflexivity. }

              eapply preord_exp_trans. tci. eapply eq_fuel_idemp.

              2:{ intros m. eapply preord_exp_Efun_red. } simpl.

              assert (Hex' : exists z, ~ In var (k2 |: FromList vnames) z).
              { eapply ToMSet_non_member. tci. } destructAll.

              assert (HS2 := H6). eapply cps_cvt_rel_subset in HS2.

              eapply preord_exp_trans. tci. eapply eq_fuel_idemp.


              2:{ intros m. simpl. eapply IH2 ; [ | | | | | | | eassumption | reflexivity | eassumption ].
                  - eassumption.
                  - eassumption.
                  - eapply Disjoint_Included_r. eassumption.
                    eapply Union_Disjoint_l; sets.
                    eapply Disjoint_Included; [ | | eapply Hdis ]; sets.
                  - eassumption.
                  - inv_setminus. intros Hin. eapply Hdis. eauto.
                  - repeat eapply cps_env_rel_weaken. eassumption.
                    intros Hc. inv H2. now eapply Hdis; eauto.
                    intros Hc. now eapply Hdis; eauto.
                    inv_setminus. intros Hin. eapply Hdis. eauto.
                  - rewrite M.gss. reflexivity. }

              eapply preord_exp_trans. tci. eapply eq_fuel_idemp.

              2:{ intros m. eapply preord_exp_Eapp_red.
                  - rewrite M.gso; eauto. rewrite M.gss. reflexivity. intros Hc; subst; eauto.
                  - simpl. rewrite Coqlib.peq_true. reflexivity.
                  - simpl. rewrite M.gss. reflexivity.
                  - simpl. reflexivity. }

              (* inv H0. simpl. *)
              eapply preord_exp_Eapp_red.
              - rewrite M.gso; eauto. rewrite M.gso; eauto.
                rewrite M.gss. reflexivity.
                inv_setminus. intros Hin. subst; eauto.
                inv_setminus. intros Hin. subst; eauto.
              - eassumption.
              - simpl. rewrite M.gso.
                simpl. rewrite M.gso.
                simpl. rewrite M.gso.
                simpl. rewrite M.gso. rewrite M.gss.
                rewrite Hget. reflexivity.
                intros Hc; subst. inv H2. now eapply Hdis; eauto.
                intros Hc; subst. now eapply Hdis; eauto.
                intros Hc; subst. inv_setminus. now eapply Hdis; eauto.
                intros Hc; subst. inv_setminus. now eapply Hdis; eauto.
              - simpl. reflexivity. }

          (* Invariant composition *)
          { unfold inclusion, comp, eq_fuel, one_step, cps_bound, one_i.
            intros [[[? ?] ?] ?] [[[? ?] ?] ?] ?.
            destructAll. destruct_tuples. subst. simpl. unfold fuel_exp, trace_exp. lia. } }

        split.

        (* Termination *)
        { intros v v' Heq1 Hvrel. subst.

          assert (Hex : exists x, ~ In var (x3 |: FromList (y1 :: fnames ++ names)) x).
          { eapply ToMSet_non_member. tci. } destructAll.

          eapply preord_exp_post_monotonic.

          2:{ eapply preord_exp_trans; [ | | | eassumption ]. tci. eapply eq_fuel_idemp.

              repeat subst_exp.
              eapply preord_exp_trans. tci. eapply eq_fuel_idemp.

              2:{ intros m. eapply IH3; [ | | | | | | | eassumption | reflexivity  | eapply Hvrel ].
                  - inv Hwfcl. constructor; eauto.
                    eapply well_formed_envmake_rec_env_rev_order. reflexivity. eassumption. eassumption.
                  - inv Hwfcl.
                    eapply enthopt_inlist_Forall in H26; [ | eassumption ].
                    inv H26. inv H22. simpl Datatypes.length.
                    rewrite length_app, length_rev. erewrite cps_fix_rel_length; [ | eassumption ].
                    erewrite <- Forall2_length; [ | eassumption ].
                    rewrite Nnat.Nat2N.inj_succ, <- OrdersEx.N_as_OT.add_1_l, Nnat.Nat2N.inj_add, efnlength_efnlst_length.
                    eassumption.
                  - repeat normalize_sets.
                    eapply Union_Disjoint_l; sets.
                    eapply Union_Disjoint_l; sets.
                    eapply Disjoint_Singleton_l. now eauto.
                    eapply Disjoint_Included_r. eassumption. rewrite FromList_rev. sets.
                  - repeat normalize_sets. rewrite FromList_rev. eassumption.
                  - repeat normalize_sets. rewrite FromList_rev. intros Hc; inv Hc; eauto. inv H21; eauto.
                  - eapply cps_env_rel_weaken; eauto.
                    eapply cps_env_rel_extend_weaken; eauto.
                    erewrite <- cps_fix_rel_names with (fnames' := fnames); [ | eassumption ].
                    eapply cps_env_rel_extend_fundefs; try eassumption.
                    repeat normalize_sets. rewrite FromList_rev. now eauto.
                    repeat normalize_sets. rewrite FromList_rev. intros Hc; inv Hc; eauto.
                    inv H21; eauto.
                  - rewrite M.gss. reflexivity. }

              eapply preord_exp_app_compat with (P2 := eq_fuel).
              now eapply eq_fuel_compat.
              now eapply eq_fuel_compat.

              eapply preord_var_env_extend_neq.
              eapply preord_var_env_extend_eq.
              eapply preord_val_refl. now tci.
              now intros Hc; subst; eauto.
              now intros Hc; subst; eauto.
              constructor.
              eapply preord_var_env_extend_eq.
              eapply preord_val_refl. now tci. now constructor. }

          (* Invariant composition *)
          { unfold inclusion, comp, eq_fuel, one_step, cps_bound, one_i.
            intros [[[? ?] ?] ?] [[[? ?] ?] ?] ?.
            destructAll. destruct_tuples. subst. simpl in *. lia. } }

        (* OOT *)
        { intros ?; subst.
          assert (Hex : exists x, ~ In var (x3 |: FromList (y1 :: fnames ++ names)) x).
          { eapply ToMSet_non_member. tci. } destructAll.

          edestruct IH3 with (rho := M.set x3 vk (map_util.M.set y1 x0 (def_funs Bs Bs rho0 rho0)));
            [ | | | | | | | eassumption | ].
          - inv Hwfcl. constructor; eauto.
            eapply well_formed_envmake_rec_env_rev_order. reflexivity. eassumption. eassumption.
          - inv Hwfcl.
            eapply enthopt_inlist_Forall in H26; [ | eassumption ].
            inv H26. inv H22. simpl Datatypes.length.
            rewrite length_app, length_rev. erewrite cps_fix_rel_length; [ | eassumption ].
            erewrite <- Forall2_length; [ | eassumption ].
            rewrite Nnat.Nat2N.inj_succ, <- OrdersEx.N_as_OT.add_1_l, Nnat.Nat2N.inj_add, efnlength_efnlst_length.
            eassumption.
          - repeat normalize_sets.
            eapply Union_Disjoint_l; sets.
            eapply Union_Disjoint_l; sets.
            eapply Disjoint_Singleton_l. now eauto.
            eapply Disjoint_Included_r. eassumption. rewrite FromList_rev. sets.
          - repeat normalize_sets. rewrite FromList_rev. eassumption.
          - repeat normalize_sets. rewrite FromList_rev. sets.
            intros Hc; inv Hc; eauto. inv H21; eauto.
          - eapply cps_env_rel_weaken; eauto.
            eapply cps_env_rel_extend_weaken; eauto.
            erewrite <- cps_fix_rel_names with (fnames' := fnames); [ | eassumption ].
            eapply cps_env_rel_extend_fundefs; try eassumption.
            repeat normalize_sets. rewrite FromList_rev. now eauto.
            repeat normalize_sets. rewrite FromList_rev. intros Hc; inv Hc; eauto.
            inv H21; eauto.
          - rewrite M.gss. reflexivity.
          - destruct (H22 ltac:(reflexivity)). destructAll. eapply Heq in H24; [ | reflexivity ]. destructAll.
            destruct x8; try contradiction. destruct x10. eexists. split; [ | eassumption ].

            unfold one_i in *. simpl in *. lia. }

      - (* Match_e *)
        intros e1 e' vs dc vs' n brs r f1 f2 t1 t2 Heval1 IH1  Hfind Heval2 IH2.
        intros rho vnames k x vk e2 S S' f Henvwf Hwf Hdis Hnin1 Hnin2 Hcenv Hstep Hcps.
        inv Hwf. inv Hcps.

        assert (Hvwf : well_formed_val (Con_v dc vs')).
        { eapply (@eval_env_step_preserves_wf nat LambdaBoxLocal_resource_fuel LambdaBoxLocal_resource_trace) in Heval1.
          eassumption. reflexivity.
          eassumption. unfold well_formed_in_env.
          eapply Forall2_length in Hcenv. rewrite Hcenv. eassumption. }

        assert (Hex : exists v2, cps_val_rel (Con_v dc vs') v2).
        { eapply cps_val_rel_exists; eassumption. }

        assert (Hex' : exists z, ~ In var (k1 |: FromList vnames) z).
        { eapply ToMSet_non_member. tci. } destructAll.

        assert (Hwf := H0). inv Hwf.

        assert (HS2 := H12). eapply cps_cvt_exp_subset in HS2.

        edestruct cps_cvt_rel_branches_find_branch. eassumption. eassumption. reflexivity.
        destructAll.

        set (rho' := map_util.M.set x1 (Vconstr (dcon_to_tag default_tag dc cnstrs) vs'0)
                                    (M.set k1 (Vfun rho (Fcons k1 kon_tag [x1] (Ecase x1 bs') Fnil) k1) rho)).

        edestruct (set_lists_length3 rho' (rev x2) vs'0).
        { rewrite length_rev. rewrite H5, Nnat.Nat2N.id. eapply Forall2_length. eassumption. }
        destructAll.


        assert (Hexp : forall j, preord_exp' cenv (preord_val cenv)
                                             (cps_bound (f1 <+> @one_i _ _ fuel_resource_LambdaBoxLocal (Match_e e1 n brs))
                                                        (t1 <+> @one_i _ _ trace_resource_LambdaBoxLocal (Match_e e1 n brs)))
                                             eq_fuel j
                                             (x5, x6) (Efun (Fcons k1 kon_tag [x1] (Ecase x1 bs') Fnil) e1', rho)).
        { intros j. eapply preord_exp_post_monotonic.
          2:{ eapply preord_exp_trans. tci. eapply eq_fuel_idemp.

              2:{ intros m. eapply preord_exp_Efun_red. }

              assert (Hex' : exists z, ~ In var (k1 |: FromList vnames) z).
              { eapply ToMSet_non_member. tci. } destructAll.

              eapply preord_exp_trans. tci. eapply eq_fuel_idemp.

              2:{ intros m. simpl. eapply IH1; [ | | | | | | |  eassumption | reflexivity | ].
                  - eassumption.
                  - eassumption.
                  - eapply Union_Disjoint_l; sets.
                  - eassumption.
                  - intros Hc. inv_setminus. eapply Hdis; eauto.
                  - eapply cps_env_rel_weaken. eassumption.
                    inv_setminus. intros Hc. eapply Hdis; eauto.
                  - rewrite M.gss. reflexivity.
                  - eassumption. }

              eapply preord_exp_trans. tci. eapply eq_fuel_idemp.

              2:{ intros m. eapply preord_exp_Eapp_red.
                  - rewrite M.gso; eauto. rewrite M.gss. reflexivity. intros Hc; subst; eauto.
                  - simpl. rewrite Coqlib.peq_true. reflexivity.
                  - simpl. rewrite M.gss. reflexivity.
                  - simpl. reflexivity. }


              eapply preord_exp_trans. tci. eapply eq_fuel_idemp.

              2:{ intros m. eapply preord_exp_Ecase_red.
                  - rewrite M.gss. reflexivity.
                  - eassumption. }

              eapply ctx_bind_proj_preord_exp with (vs' := []); try reflexivity.
              - intros Hc. eapply H1 in Hc. eapply HS2 in Hc. inv_setminus. now eauto.
              - unfold rho'. rewrite M.gss. rewrite app_nil_r. reflexivity.
              - eassumption. }


          { unfold inclusion, comp, eq_fuel, one_step, cps_bound, one_i.
            intros [[[? ?] ?] ?] [[[? ?] ?] ?] ?.
            destructAll. destruct_tuples. subst. simpl in *. unfold fuel_exp, trace_exp.
            split. lia.
            eapply find_branch_max_m_branches in Hfind. rewrite <- H5 in Hfind. subst.
            replace (@Datatypes.length var x2) with (@Datatypes.length positive x2) in * by reflexivity. lia. } }

        assert (Hex' : exists z, ~ In var (k |: FromList (x2 ++ vnames)) z).
        { eapply ToMSet_non_member. tci. } destructAll.

        rewrite Nnat.Nat2N.id in *.

        split.

        (* Termination *)
        { intros v v' Heq Hval. subst.

          eapply preord_exp_post_monotonic.

          2:{ eapply preord_exp_trans. tci. eapply eq_fuel_idemp.

              2:{ eassumption. }

              eapply preord_exp_trans. tci. eapply eq_fuel_idemp.

              2:{ intros i. eapply IH2 ; [ | | | | | | | eassumption | reflexivity | eassumption ].
                  - eapply Forall_app. split; eauto.
                    eapply Forall_rev. inv Hvwf. eassumption.
                  - rewrite length_app, Nnat.Nat2N.inj_add.
                    eapply cps_cvt_rel_branches_find_branch_wf. eassumption.
                    eassumption. rewrite H5. eassumption.
                  - normalize_sets.
                    eapply Disjoint_Included_r. eassumption.
                    rewrite Union_commut, <- Union_assoc.
                    eapply Union_Disjoint_l; sets.

                    eapply Disjoint_Included_r.
                    eapply Included_trans. eapply Setminus_Included. eassumption.
                    sets.
                  - eassumption.
                  - normalize_sets.
                    intros Hc; inv Hc; eauto.
                    eapply H1 in H16. eapply HS2 in H16. inv_setminus. eapply Hdis; eauto.
                  - eapply Forall2_app.
                    rewrite <- rev_involutive with (l := x2). eapply All_Forall.Forall2_rev.
                    rewrite <- app_nil_r with (l := vs').
                    rewrite <- app_nil_r with (l := rev x2).
                    eapply cps_env_rel_extend_setlists. now constructor.
                    eapply get_list_set_lists.
                    now eapply NoDup_rev; eauto.
                    eassumption.
                    eassumption.

                    eapply cps_env_rel_weaken_setlists with (rho := rho').
                    repeat eapply cps_env_rel_weaken. eassumption.
                    intros Hc. inv_setminus. now eapply Hdis; eauto.
                    intros Hc. inv_setminus. now eapply Hdis; eauto.
                    eassumption.
                    rewrite FromList_rev.

                    eapply Disjoint_Included_l.
                    eapply Included_trans. eassumption. eassumption. sets.

                  - erewrite <- set_lists_not_In; [ | now eauto | ].
                    unfold rho'. rewrite !M.gso.
                    eassumption.
                    intros hc. inv_setminus. now eapply Hdis; eauto.
                    intros hc. inv_setminus. now eapply Hdis; eauto.
                    intros Hc.
                    eapply in_rev in Hc.
                    eapply H1 in Hc. eapply HS2 in Hc. inv_setminus. eapply Hdis; eauto. }

          eapply preord_exp_app_compat with (P2 := eq_fuel).
          now eapply eq_fuel_compat.
          now eapply eq_fuel_compat.

          eapply preord_var_env_extend_neq.
          eapply preord_var_env_get.
          2:{ eapply M.gss. }
          2:{ rewrite M.gss. reflexivity. }

          eapply preord_val_refl. now tci.
          now intros Hc; subst; eauto.
          now intros Hc; subst; eauto.
          constructor.
          eapply preord_var_env_extend_eq.
          eapply preord_val_refl. now tci. now constructor. }

        (* Invariant composition *)
        { unfold inclusion, comp, eq_fuel, one_step, cps_bound, one_i.
          intros [[[? ?] ?] ?] [[[? ?] ?] ?] ?.
          destructAll. destruct_tuples. subst. simpl in *. lia. } }


        { intros ?; subst.
          edestruct IH2 ; [ | | | | | | | eassumption | ].
          - eapply Forall_app. split; eauto.
            eapply Forall_rev. inv Hvwf. eassumption.
          - rewrite length_app, Nnat.Nat2N.inj_add.
            eapply cps_cvt_rel_branches_find_branch_wf. eassumption.
            eassumption. rewrite H5. eassumption.
          - normalize_sets.
            eapply Disjoint_Included_r. eassumption.
            rewrite Union_commut, <- Union_assoc.
            eapply Union_Disjoint_l; sets.

            eapply Disjoint_Included_r.
            eapply Included_trans. eapply Setminus_Included. eassumption.
            sets.
          - eassumption.
          - normalize_sets.
            intros Hc; inv Hc; eauto.
            eapply H1 in H16. eapply HS2 in H16. inv_setminus. eapply Hdis; eauto.
          - eapply Forall2_app.
            rewrite <- rev_involutive with (l := x2). eapply All_Forall.Forall2_rev.
            rewrite <- app_nil_r with (l := vs').
            rewrite <- app_nil_r with (l := rev x2).
            eapply cps_env_rel_extend_setlists. now constructor.
            eapply get_list_set_lists.
            now eapply NoDup_rev; eauto.
            eassumption.
            eassumption.

            eapply cps_env_rel_weaken_setlists with (rho := rho').
            repeat eapply cps_env_rel_weaken. eassumption.
            intros Hc. inv_setminus. now eapply Hdis; eauto.
            intros Hc. inv_setminus. now eapply Hdis; eauto.
            eassumption.
            rewrite FromList_rev.

            eapply Disjoint_Included_l.
            eapply Included_trans. eassumption. eassumption. sets.

          - erewrite <- set_lists_not_In; [ | now eauto | ].
            unfold rho'. rewrite !M.gso.
            eassumption.
            intros hc. inv_setminus. now eapply Hdis; eauto.
            intros hc. inv_setminus. now eapply Hdis; eauto.
            intros Hc.
            eapply in_rev in Hc.
            eapply H1 in Hc. eapply HS2 in Hc. inv_setminus. eapply Hdis; eauto.

          - destruct (H17 ltac:(reflexivity)). destructAll. eapply Hexp in H19; [ | reflexivity ]. destructAll.
            destruct x10; try contradiction. destruct x12. eexists. split; [ | eassumption ].

            unfold one_i in *. simpl in *. lia. }


      - (* Match_e OOT *)
        intros e1 vs n br f1 t1 Hoot IH.
        intros rho vnames k x vk e' S S' f Henvwf Hwf Hdis Hnin1 Hnin2 Hcenv Hstep Hcps. split.
        congruence.
        intros _. inv Hcps. inv Hwf.
        set (rho' := M.set k1 (Vfun rho (Fcons k1 kon_tag [x1] (Ecase x1 bs') Fnil) k1) rho).
        assert (Hex : exists x, ~ In var (k1 |: FromList vnames) x).
        { eapply ToMSet_non_member. tci. } destructAll.

        edestruct IH with (rho := rho'); [ | | | | | | | eassumption | ].
        + eassumption.
        + eassumption.
        + eapply Union_Disjoint_l; sets.
        + eassumption.
        + intros Hc; inv H4; eapply Hdis; eauto.
        + unfold rho'.
          eapply cps_env_rel_weaken; try eassumption.
          intros hc. inv H4. eapply Hdis; eauto.
        + unfold rho'. rewrite M.gss. reflexivity.
        + destruct H1. reflexivity. destructAll. eexists (x2 + 1)%nat. split.
          unfold one_i. simpl. unfold fuel_exp. lia.
          replace tt with (tt <+> tt) by reflexivity. eapply BStepf_run. econstructor.
          simpl. eassumption.

      - (* enil *)
        intros vs'.

        intros rho vnames e' e_app S S' vs2 xs ys ks vs'' Hwfenv Hwf
               Hdis Hdis' Hdis'' Hdis''' Hnd Hcenv Hfv Hcps Hall Hgetl.
        inv Hall. inv Hcps.

        edestruct (set_lists_length3 rho (ys ++ []) (vs'' ++ [])).
        { rewrite !app_nil_r. eapply get_list_length_eq. eassumption. }

        eexists. split. eassumption.
        intros i.
        eapply preord_exp_post_monotonic.

        2:{ eapply preord_exp_refl. tci.


            assert (Henv : preord_env_P_inj cenv eq_fuel (occurs_free e') i id x rho).
            { eapply preord_env_P_inj_f_eq_subdomain.
              eapply preord_env_P_inj_set_lists_l; eauto.
              eapply preord_env_P_refl. tci.
              rewrite !app_nil_r. eapply Forall2_refl. intro. eapply preord_val_refl. tci.
              rewrite !app_nil_r. rewrite apply_r_set_list_f_eq.

              clear. induction ys. simpl.
              intros z Hin. rewrite apply_r_empty. reflexivity.
              simpl. intros z Hin.
              destruct (Coqlib.peq z a). subst. rewrite extend_gss; eauto.
              rewrite extend_gso; eauto. }

            unfold preord_env_P_inj, id in *.  eassumption. }

        (* Invariant composition *)
        { unfold inclusion, comp, eq_fuel, one_step, cps_bound, one_i.
          intros [[[? ?] ?] ?] [[[? ?] ?] ?] ?.
          destructAll. destruct_tuples. subst. simpl in *. lia. }

      - (* econs *)
        intros vs' we es v vs f1 fs t1 ts Heval1 IH1 Heval2 IH2.
        intros rho vnames e' e_app S S' vs2 xs ys ks vs'' Hwfenv Hwf Hdis Hdis' Hdis'' Hdis''' Hnd
               Hcenv Hfv Hcps Hall Hgetl.
        inv Hall. inv Hcps. inv Hwf.

        set (rho' := M.set x1 y (M.set k1 (Vfun rho (Fcons k1 kon_tag [x1] es' Fnil) k1) rho)).

        replace (ys ++ x1 :: xs0) with ((ys ++ [x1]) ++ xs0) in *.
        2:{ rewrite app_cons with (a := x1) (l2 := xs0). reflexivity.  }

        edestruct IH2 with (ys := ys ++ [x1]) (vs' := vs'' ++ [y]) (rho := rho');
          [ | | | | | | | | | eassumption | eassumption | | ].
        + eassumption.
        + eassumption.
        + repeat normalize_sets.
          eapply Disjoint_Included_r.
          eapply cps_cvt_exp_subset. eassumption.
          xsets.
        + repeat normalize_sets.
          eapply Disjoint_Included; [ | | eapply Hdis' ]; sets.
        + repeat normalize_sets.
          eapply Union_Disjoint_r; sets.
          eapply Disjoint_Included; [ | | eapply Hdis'' ]; sets.
          eapply Disjoint_Included; [ | | eapply Hdis'' ]; sets.
        + repeat normalize_sets.
          inv Hnd. eapply Union_Disjoint_r; sets.
        + inv Hnd. eassumption.
        + repeat normalize_sets. unfold rho'. repeat eapply cps_env_rel_weaken.
          eassumption.
          intros Hc. eapply Hdis'; eauto.
          intros Hc. eapply Hdis'; eauto.
        + repeat normalize_sets. sets.
        + unfold rho'. eapply get_list_app.
          repeat normalize_sets. rewrite !get_list_set_neq. eassumption.
          intros Hc. now eapply Hdis''; eauto.
          intros Hc. now eapply Hdis'''; eauto.
          simpl. rewrite M.gss. reflexivity.
        + destructAll.

          edestruct (set_lists_length3 rho ((ys ++ [x1]) ++ xs0) ((vs'' ++ [y]) ++ l')).
          eapply set_lists_length_eq. eassumption.

          eexists. split.

          rewrite app_cons with (a := y). eassumption.

          intros i.

          eapply preord_exp_post_monotonic.

          2:{ eapply preord_exp_trans. tci. eapply eq_fuel_idemp.

              2:{ intros m. eapply preord_exp_Efun_red. }

              assert (Hex' : exists z, ~ In var (k1 |: FromList vnames) z).
              { eapply ToMSet_non_member. tci. } destructAll.

              eapply preord_exp_trans. tci. eapply eq_fuel_idemp.

              2:{ intros m. eapply IH1; [ | | | | | | | eassumption | reflexivity | ].
                  - eassumption.
                  - eassumption.
                  - eapply Union_Disjoint_l; sets.
                    repeat normalize_sets. sets.
                  - eassumption.
                  - repeat normalize_sets.
                    intros Hc. eapply Hdis'; eauto.
                  - simpl.
                    eapply cps_env_rel_weaken. eassumption.
                    repeat normalize_sets. intros Hc. eapply Hdis'; eauto.
                  - simpl. eapply M.gss.
                  - eassumption. }

              eapply preord_exp_trans. tci. eapply eq_fuel_idemp.

              2:{ intros m. eapply preord_exp_Eapp_red.
                  - rewrite M.gso; eauto.
                    rewrite M.gss. reflexivity.
                    intros Hc; subst. now eauto.
                  - simpl. rewrite Coqlib.peq_true. reflexivity.
                  - simpl. rewrite M.gss. reflexivity.
                  - simpl. reflexivity. }

              simpl in H0.

              eapply preord_exp_trans. tci. eapply eq_fuel_idemp.

              2:{ eassumption. }

              eapply preord_exp_refl. tci.

              eapply uncurry_correct.preord_env_P_set_lists_extend; eauto.

              2:{ eapply Forall2_refl. intro. eapply preord_val_refl. tci. }

              unfold rho'.

              eapply preord_env_P_set_not_in_P_r.
              eapply preord_env_P_set_not_in_P_r.

              eapply preord_env_P_refl. now tci.

              repeat normalize_sets.
              now sets.
              repeat normalize_sets. now sets. }

          (* Invariant composition *)
          { simpl. unfold inclusion, comp, eq_fuel, one_step, cps_bound, one_i.
            intros [[[? ?] ?] ?] [[[? ?] ?] ?] ?.
            destructAll. destruct_tuples. subst. simpl in *. lia. }


      - (* Var_e *)
        intros z vs v Hnth.
        intros rho vnames k x vk e' S S' f  Henvwf Hwf Hdis Hnin1 Hnin2 Hcenv Hstep Hcps. split; [ | congruence ].
        intros v1 v2 Heq Hval. inv Heq. inv Hcps.

        eapply preord_exp_app_compat.

        + intro; intros. unfold eq_fuel, cps_bound in *. simpl in *. subst.
          unfold_all. lia.

        + intro; intros. unfold eq_fuel, cps_bound in *. simpl in *. subst.
          unfold_all. lia.

        + eapply preord_var_env_extend_neq_l.
          eapply preord_var_env_get. eapply preord_val_refl; tci.
          rewrite M.gss. reflexivity. eassumption. intros Hc; subst; eauto.

        + constructor; eauto.
          edestruct cps_env_rel_nth_error; eauto. destructAll.
          eapply preord_var_env_get.
          2:{ rewrite M.gss. reflexivity. }
          2:{ eassumption. }
          eapply cps_cvt_val_alpha_equiv.
          eapply eq_fuel_compat. eapply eq_fuel_compat.
          clear; now firstorder. (* TODO find inclusion refl *)
          eassumption. eassumption.

      - (* Lam_e *)
        intros e vs na.
        intros rho vnames k x vk e' S S' f Hwfenv Hwf Hdis Hnin1 Hnin2 Hcenv Hstep Hcps. split; [ | congruence ].
        intros v1 v2 Heq Hval. inv Heq. inv Hcps.

        eapply preord_exp_post_monotonic.
        2:{ eapply preord_exp_trans. tci. eapply eq_fuel_idemp.

            2:{ intros m. eapply preord_exp_Efun_red. }

            simpl. eapply preord_exp_app_compat with (P2 := eq_fuel).
            now eapply eq_fuel_compat.
            now eapply eq_fuel_compat.

            eapply preord_var_env_extend_neq.
            eapply preord_var_env_get.
            eapply preord_val_refl. now tci. now rewrite M.gss; reflexivity. eassumption.

            - intros Hc; subst; eauto.
            - intros Hc; subst. inv H2. eapply Hdis; eauto.
            - constructor; eauto.
              eapply preord_var_env_extend_eq. inv Hval.
              (* Seems similar to other cases in alpha equiv, maybe lemma? *)
              eapply preord_val_fun.
              + simpl. rewrite Coqlib.peq_true. reflexivity.
              + simpl. rewrite Coqlib.peq_true. reflexivity.
              + assert (Hlen : Datatypes.length names = Datatypes.length vnames).
                { simpl. eapply Forall2_length in Hcenv.
                  eapply Forall2_length in H5.
                  replace (@Datatypes.length positive) with (@Datatypes.length var) in * by reflexivity.
                  congruence. }

                intros rho1' j vs1 vs2 Heq Hset.
                destruct vs1 as [ | ? [ | ? [ | ] ]]; simpl in *; try congruence.  inv Hset.
                destruct vs2 as [ | ? [ | ? [ | ] ]]; simpl in *; try congruence.
                eexists. split. reflexivity. intros.
                eapply cps_cvt_exp_alpha_equiv; try eassumption.
                * reflexivity.
                * constructor; eauto.
                * normalize_sets. intros Hc. inv Hc. inv H3; eauto. eapply H9; eauto.
                * simpl. congruence.
                * normalize_sets. sets.
                * normalize_sets.
                  eapply Union_Disjoint_l. sets.
                  eapply Union_Disjoint_l; sets.
                * assert (Hseq : k0 |: (x0 |: FromList names) \\ [set k0] \\ [set x0] \\ FromList names <--> Empty_set _) by xsets.
                  inv H0. inv H17. clear H18. normalize_sets. simpl.
                  rewrite extend_extend_lst_commut. rewrite extend_commut.
                  eapply preord_env_P_inj_set_alt; eauto.
                  eapply preord_env_P_inj_set_alt; eauto.
                  eapply preord_env_P_inj_set_not_In_P_l; eauto.
                  eapply preord_env_P_inj_set_not_In_P_r; eauto.
                  eapply preord_env_P_inj_antimon. eapply cps_cvt_env_alpha_equiv.
                  now eapply eq_fuel_compat. now tci. now firstorder. eassumption. eassumption.
                  now xsets.
                  -- intros Hc. eapply image_extend_lst_Included in Hc; eauto.
                     rewrite image_id in Hc.
                     rewrite Hseq in Hc.
                     inv Hc; eauto. now inv H0.
                     inv H2; eapply Hdis; eauto.
                  -- intros Hc. inv Hc. inv H0. inv H11; eauto. inv H0; eauto.
                  -- intros Hc. eapply image_extend_lst_Included in Hc; eauto.
                     rewrite image_id in Hc.
                     rewrite Hseq in Hc.
                     inv Hc; eauto. inv H0.
                     inv H2. eapply Hdis. constructor. now right. eassumption.
                  -- intros Hc. eapply image_extend_Included' in Hc.
                     inv Hc; eauto. eapply image_extend_lst_Included in H0; eauto.
                     rewrite Hseq, image_id in H0. inv H0; eauto. inv H3.
                     inv H4. now eapply Hdis; eauto.
                     inv H0; eauto. inv H4; eauto.
                  -- intros Hc; subst; eauto.
                  -- intros Hc; subst; eauto. inv H4; eauto.
                  -- intros Hc; subst; eauto.
                  -- intros Hc; eauto. inv H4. eapply Hdis; eauto.
                  -- eassumption. }

        (* Invariant composition *)
        { unfold inclusion, comp, eq_fuel, one_step, cps_bound.
          intros [[[? ?] ?] ?] [[[? ?] ?] ?] H.
          destructAll. destruct_tuples. subst. simpl. lia. }

      - (* Fix_e *)
        intros n vs efns.
        intros rho vnames k x vk e' S S' f Hwfenv Hwf Hdis Hnin1 Hnin2 Hcenv Hstep Hcps. split; [ | congruence ].
        intros v1 v2 Heq Hval. inv Heq. inv Hcps. inv Hval.

        assert (Hfeq : all_fun_name fdefs = fnames).
        { eapply cps_cvt_rel_efnlst_all_fun_name; eauto. }

        eapply preord_exp_post_monotonic.
        2:{ eapply preord_exp_trans. tci. eapply eq_fuel_idemp.

            2:{ intros m. eapply preord_exp_Efun_red. }

            simpl. eapply preord_exp_app_compat with (P2 := eq_fuel).
            now eapply eq_fuel_compat.
            now eapply eq_fuel_compat.


            eapply preord_var_env_def_funs_not_In_r.
            rewrite Same_set_all_fun_name.
            erewrite Hfeq. intros Hc. now eapply Hdis; eauto.

            eapply preord_var_env_extend_neq_l.
            eapply preord_var_env_get.
            eapply preord_val_refl. now tci. rewrite M.gss. reflexivity. eassumption.
            now intros Hc; subst.

            constructor; eauto.

            eapply preord_var_env_get.
            2:{ rewrite M.gss. reflexivity. }
            2:{ rewrite def_funs_eq. reflexivity. eapply Same_set_all_fun_name.
                rewrite Hfeq. eapply nth_error_In. eassumption. }

            revert f1 f0 H13 H11. generalize (N.to_nat n). induction f as [f IHf] using lt_wf_rec1. intros.

            edestruct cps_cvt_rel_efnlst_exists. eassumption. rewrite Hfeq. eassumption.
            rewrite Hfeq. eassumption. destructAll.

            edestruct LambdaBoxLocal_to_LambdaANF_util.cps_fix_rel_exists. eassumption. eassumption. eassumption. destructAll.

            eapply preord_val_fun.
            + eassumption.
            + eassumption.
            +
              assert (Hlen : Datatypes.length names = Datatypes.length vnames).
              { simpl. eapply Forall2_length in Hcenv.
                  eapply Forall2_length in H6.
                  replace (@Datatypes.length positive) with (@Datatypes.length var) in * by reflexivity.
                  congruence. }

              intros rho1' j vs1 vs2 Heq Hset.
              destruct vs1 as [ | ? [ | ? [ | ] ]]; simpl in *; try congruence.  inv Hset.
              destruct vs2 as [ | ? [ | ? [ | ] ]]; simpl in *; try congruence.
              eexists. split. reflexivity. intros. repeat subst_exp.

              eapply cps_cvt_exp_alpha_equiv; try eassumption.
              * reflexivity.
              * constructor.
                -- intros Hc. eapply in_app_or in Hc. inv Hc; eauto.
                   eapply in_rev in H17; eauto.
                -- eapply List_util.NoDup_app; eauto.
                   eapply NoDup_rev. eassumption.
                   rewrite FromList_rev. sets.
              * repeat normalize_sets. rewrite FromList_rev.
                intros Hc. inv Hc. inv H17; eauto. inv H17; eauto.
              * simpl. rewrite !length_app, !length_rev.
                rewrite H3. erewrite <- cps_fix_rel_length; [ | eassumption ]. congruence.
              * repeat normalize_sets. rewrite FromList_rev.
                eapply Union_Disjoint_l. now sets.
                eapply Union_Disjoint_l.
                eapply Disjoint_Singleton_l. now eauto.
                eapply Disjoint_Included_r. eassumption. sets.
              * repeat normalize_sets. rewrite FromList_rev.
                eapply Union_Disjoint_l; sets.
                eapply Union_Disjoint_l; sets.
                eapply Union_Disjoint_l; sets.
                eapply Disjoint_Included_r. eapply Included_trans. eapply Setminus_Included.
                eapply Included_trans. eapply Setminus_Included. eassumption.
                now sets.
                eapply Disjoint_Included; [ | | eapply Hdis ]; sets.
                eapply Included_trans. eapply Setminus_Included.
                eapply Included_trans. eapply Setminus_Included.
                eapply Included_trans. eassumption. sets.

              * inv H24. inv H29. clear H30. simpl. repeat normalize_sets.

                assert (Hseq : (x7 |: (x8 |: (name_in_fundefs Bs :|: FromList names)) \\ [set x7] \\ [set x8] \\
                                   name_in_fundefs Bs \\ FromList names) <--> Empty_set _) by xsets.

                rewrite extend_extend_lst_commut. rewrite extend_commut.
                eapply preord_env_P_inj_set_alt; eauto.
                eapply preord_env_P_inj_set_alt; eauto.

                rewrite extend_lst_app. rewrite extend_lst_rev; eauto.

                erewrite <- cps_fix_rel_names with (fnames' := fnames0); [ | eassumption ].


                eapply preord_env_P_inj_def_funs_Vfun.

                -- eapply preord_env_P_inj_antimon. eapply cps_cvt_env_alpha_equiv.
                   now eapply eq_fuel_compat. now tci. now firstorder. eassumption. eassumption.
                   rewrite FromList_rev. rewrite Same_set_all_fun_name. now xsets.

                -- rewrite H3. erewrite cps_fix_rel_names; [ | eassumption ].
                   eapply cps_fix_rel_length; eauto.

                -- erewrite cps_fix_rel_names with (fnames' := fnames0); [ | eassumption ]. eassumption.

                -- eapply Disjoint_Included_l.
                   eapply image_extend_lst_Included. eassumption.
                   rewrite FromList_rev, image_id, <- Same_set_all_fun_name, Hseq.
                   rewrite Same_set_all_fun_name.
                   eapply Disjoint_Included_r. eassumption. sets.

                -- intros. eapply IHf. lia.
                   now erewrite <- !cps_fix_rel_names with (Bs := Bs) (fnames' := fnames0); eauto.
                   eassumption.

                -- replace (@Datatypes.length positive) with (@Datatypes.length var) in * by reflexivity.
                   rewrite H3. eapply cps_fix_rel_length; eauto.

                -- rewrite !length_rev.
                   rewrite H3. eapply cps_fix_rel_length; eauto.

                -- intros Hc. eapply image_extend_lst_Included in Hc; eauto. rewrite image_id in Hc.
                   repeat normalize_sets. rewrite !FromList_rev in Hc. rewrite <- Same_set_all_fun_name in Hc.

                   erewrite <- !cps_fix_rel_names with (Bs := Bs) (fnames' := fnames0),
                             <- !Same_set_all_fun_name, <- Setminus_Union in Hc; eauto.
                   rewrite Hseq in Hc. repeat normalize_sets. inv Hc; eauto.
                   now eapply Same_set_all_fun_name in H17; inv H4; eauto.
                   now inv H4; eapply Hdis; eauto.
                   rewrite !length_app, !length_rev.
                   erewrite H3, <- cps_fix_rel_length; [ | eassumption ]. congruence.

                -- intros Hc. eapply image_extend_Included' in Hc. inv Hc; eauto.
                   eapply image_extend_lst_Included in H17; eauto. rewrite image_id in H17.
                   repeat normalize_sets. rewrite !FromList_rev in H17. rewrite <- Same_set_all_fun_name in H17.

                   erewrite <- !cps_fix_rel_names with (Bs := Bs) (fnames' := fnames0),
                             <- !Same_set_all_fun_name, <- Setminus_Union in H17; eauto.
                   rewrite Hseq in H17. repeat normalize_sets. inv H17; eauto.
                   now eapply Same_set_all_fun_name in H24; inv H12; inv H17; eauto.
                   now inv H12; inv H17; eapply Hdis; eauto.
                   rewrite !length_app, !length_rev.
                   erewrite H3, <- cps_fix_rel_length; [ | eassumption ]. congruence.
                   inv H17; inv H12; eauto.

                -- intros Hc; subst; eauto.

                -- intros Hc; subst; inv H12; eauto.

                -- repeat normalize_sets.
                   intros Hc. eapply in_app_or in Hc. inv Hc; eauto.
                   eapply in_rev in H17; eauto.

                -- repeat normalize_sets. inv H12. inv H17.
                   intros Hc. eapply in_app_or in Hc. inv Hc.
                   eapply in_rev in H17; eauto. eapply Hdis; eauto.

                -- rewrite !length_app, !length_rev.
                   erewrite H3, <- cps_fix_rel_length; [ | eassumption ]. congruence. }


        (* Invariant composition *)
        { unfold inclusion, comp, eq_fuel, one_step, cps_bound. intros [[[? ?] ?] ?] [[[? ?] ?] ?] H.
          destructAll. destruct_tuples. subst. simpl. lia.  }

      - (* OOT *)
        intros vs e c Hlt.
        intros rho vnames k x vk e' S S' f Hwfenv Hwf Hdis Hnin1 Hnin2 Hcenv Hcps. split.
        congruence.
        intros _.
        unfold one_i, lt in *. simpl in *.
        unfold fuel_exp in *. eexists 0%nat. split. lia.
        constructor 1. unfold algebra.one. simpl. lia.

      - (* STEP *)
        now eauto. (* Immediate from IH for eval_step *)

        Unshelve. all:exact 0%nat.
        (* Where do these come from??? *)
    Qed.

End Correct.
