From compcert.lib Require Import Coqlib.
Require Import LambdaANF.tactics.
From CertiRocq.LambdaANF Require Import term ctx Ensembles_util List_util functions map_util identifiers term_util stemctx
     rename logical_relations alpha_conv eval functions.
From Stdlib Require Import Arith.Arith NArith.BinNat Strings.String Lists.List
     micromega.Lia Sets.Ensembles Relations.Relation_Operators Classes.Morphisms.
From MetaRocq.Common Require Import BasicAst. (* For identifier names *)
Require Import ExtLib.Structures.Monad ExtLib.Structures.MonadState ExtLib.Data.Monads.StateMonad.

Import MonadNotation.
Open Scope monad_scope.
Open Scope ctx_scope.


Fixpoint inline_letapp
         (e : exp) (* expression to be inlined *)
         (z : var) (* the binding used for the app *)
  : option (exp_ctx * var) := (* Returns an evaluation context that computes the result of the function and puts it in the variable that's returned *)
  match e with
  | Econstr x ct xs e =>
    res <- inline_letapp e z ;;
    let (C, v) := (res : exp_ctx * var) in
    ret (Econstr_c x ct xs C, v)
  | Ecase x P =>
    (* Some (Efun1_c (Fcons f ft nil (Ecase x P) Fnil) (Eletapp_c z f ft nil Hole_c), z) *)
    (* currently we don't support inlining of let-bound applications of functions that
       are not straight line code *)
    None
  | Eproj x n ct y e =>
    res <- inline_letapp e z ;;
    let (C, v) := (res : exp_ctx * var) in
    ret (Eproj_c x n ct y C, v)
  | Eletapp x f ft ys e =>
    res <- inline_letapp e z ;;
    let (C, v) := (res : exp_ctx * var) in
    ret (Eletapp_c x f ft ys C, v)
  | Efun B e =>
    res <- inline_letapp e z ;;
    let (C, v) := (res : exp_ctx * var) in
    ret (Efun1_c B C, v)
  | Eapp f ft ys =>
    ret (Eletapp_c z f ft ys Hole_c, z)
  | Eprim_val x p e  =>
    res <- inline_letapp e z ;;
    let (C, v) := (res : exp_ctx * var) in
    ret (Eprim_val_c x p C, v)
  | Eprim x p ys e  =>
    res <- inline_letapp e z ;;
    let (C, v) := (res : exp_ctx * var) in
    ret (Eprim_c x p ys C, v)
  | Ehalt x => ret (Hole_c, x)
  end.


Lemma bound_var_inline_letapp x e C x' :
  inline_letapp e x = Some (C, x') ->
  bound_var_ctx C \subset x |: bound_var e.
Proof.
  revert C.
  induction e using exp_ind'; simpl; intros C Hin;
    (try match goal with
         | [ _ : context[inline_letapp ?E ?X] |- _ ] =>
           destruct (inline_letapp E X) as [[C' z] | ] eqn:Hin'; inv Hin
         end);
    (try now (normalize_bound_var; normalize_bound_var_ctx;
              eapply Union_Included; sets; eapply Included_trans;
              [ eapply IHe; reflexivity | ]; sets)).
  congruence.
  inv Hin. normalize_bound_var. repeat normalize_bound_var_ctx. sets.
  inv Hin. normalize_bound_var. repeat normalize_bound_var_ctx. sets.
Qed.

Lemma inline_letapp_var_eq x e C x' :
  inline_letapp e x = Some (C, x') ->
  x' = x \/ x' \in bound_var e :|: occurs_free e.
Proof.
  revert C. induction e using exp_ind'; simpl; intros C Hin;
              (try match goal with
                   | [ _ : context[inline_letapp ?E ?X] |- _ ] =>
                     destruct (inline_letapp E X) as [[C' z] | ] eqn:Hin'; inv Hin
                   end).
  - destruct (IHe C' eq_refl); eauto. right.
    eapply bound_var_occurs_free_Econstr_Included; eauto.
  - congruence.
  - destruct (IHe C' eq_refl); eauto. right.
    eapply bound_var_occurs_free_Eproj_Included; eauto.
  - destruct (IHe C' eq_refl); eauto. right.
    eapply bound_var_occurs_free_Eletapp_Included; eauto.
  - destruct (IHe C' eq_refl); eauto. right.
    eapply bound_var_occurs_free_Efun_Included; eauto.
  - inv Hin. eauto.
  - destruct (IHe C' eq_refl); eauto. right.
    eapply bound_var_occurs_free_Eprim_val_Included; eauto.
  - destruct (IHe C' eq_refl); eauto. right.
    eapply bound_var_occurs_free_Eprim_Included; eauto.
  - inv Hin. normalize_occurs_free. sets.
Qed.

Lemma occurs_fee_inline_letapp C e x x' e' :
  inline_letapp e x = Some (C, x') ->
  occurs_free (C |[ e' ]|)  \subset occurs_free e :|: (occurs_free e' \\ bound_stem_ctx C).
Proof.
  revert C x x' e'; induction e; intros C x x' e' Hin; simpl in Hin;
    (try match goal with
         | [ _ : context [inline_letapp ?E ?X ] |- _] => destruct (inline_letapp E X) as [[C' x''] | ] eqn:Hin'; inv Hin
         end); try congruence.
  - simpl. repeat normalize_occurs_free.
    eapply Union_Included; sets.
    eapply Setminus_Included_Included_Union. eapply Included_trans.
    eapply IHe; eauto. normalize_bound_stem_ctx. rewrite <- Setminus_Union.
    rewrite <- !Union_assoc. rewrite <- Union_Setminus; tci.
    rewrite <- Union_Included_Union_Setminus with (s3 := [set v]); tci; sets.
  - simpl. repeat normalize_occurs_free.
    eapply Union_Included; sets.
    eapply Setminus_Included_Included_Union. eapply Included_trans.
    eapply IHe; eauto. normalize_bound_stem_ctx. rewrite <- Setminus_Union.
    rewrite <- !Union_assoc. rewrite <- Union_Setminus; tci.
    rewrite <- Union_Included_Union_Setminus with (s3 := [set v]); tci; sets.
  - simpl. repeat normalize_occurs_free.
    eapply Union_Included; sets.
    eapply Setminus_Included_Included_Union. eapply Included_trans.
    eapply IHe; eauto. normalize_bound_stem_ctx. rewrite <- Setminus_Union.
    rewrite <- !Union_assoc. rewrite <- Union_Setminus; tci.
    rewrite <- Union_Included_Union_Setminus with (s3 := [set v]); tci; sets.
  - simpl. repeat normalize_occurs_free.
    eapply Union_Included; sets.
    eapply Setminus_Included_Included_Union. eapply Included_trans.
    eapply IHe; eauto. normalize_bound_stem_ctx. rewrite (Union_commut (name_in_fundefs f)).
    rewrite <- Setminus_Union.
    rewrite <- !Union_assoc. rewrite <- Union_Setminus; tci.
    rewrite <- Union_Included_Union_Setminus with (s3 := name_in_fundefs f); tci; sets.
  - inv Hin. simpl. repeat normalize_occurs_free. repeat normalize_bound_stem_ctx.
    xsets.
  - simpl. repeat normalize_occurs_free.
    eapply Setminus_Included_Included_Union. eapply Included_trans.
    eapply IHe; eauto. normalize_bound_stem_ctx. rewrite <- Setminus_Union.
    rewrite <- !Union_assoc. rewrite <- Union_Setminus; tci.
    rewrite <- Union_Included_Union_Setminus with (s3 := [set v]); tci; sets.
  - simpl. repeat normalize_occurs_free.
    eapply Union_Included; sets.
    eapply Setminus_Included_Included_Union. eapply Included_trans.
    eapply IHe; eauto. normalize_bound_stem_ctx. rewrite <- Setminus_Union.
    rewrite <- !Union_assoc. rewrite <- Union_Setminus; tci.
    rewrite <- Union_Included_Union_Setminus with (s3 := [set v]); tci; sets.
  - inv Hin. repeat normalize_occurs_free. repeat normalize_bound_stem_ctx.
    simpl. sets.
Qed.


Lemma unique_bindings_inline_letapp C e x x' :
  inline_letapp e x = Some (C, x') ->
  ~ x \in bound_var e ->
  unique_bindings e ->
  unique_bindings_c C.
Proof.
  revert C x x'; induction e; intros C x x' Hin Hbv Hub; simpl in Hin;
    (try match goal with
         | [ _ : context [inline_letapp ?E ?X ] |- _] => destruct (inline_letapp E X) as [[C' x''] | ] eqn:Hin'; inv Hin
         end); try congruence.
  - inv Hub. constructor; eauto. intros Hc; eapply H1.
    eapply bound_var_inline_letapp in Hc; eauto. inv Hc; eauto. inv H.
    exfalso. eapply Hbv; eauto.
    eapply IHe; eauto.
  - inv Hub. constructor; eauto. intros Hc; eapply H1.
    eapply bound_var_inline_letapp in Hc; eauto. inv Hc; eauto. inv H.
    exfalso. eapply Hbv; eauto.
    eapply IHe; eauto.
  - inv Hub. constructor; eauto. intros Hc; eapply H1.
    eapply bound_var_inline_letapp in Hc; eauto. inv Hc; eauto. inv H.
    exfalso. eapply Hbv; eauto.
    eapply IHe; eauto.
  - inv Hub. constructor; eauto.
    eapply IHe; eauto.
    eapply Disjoint_Included_l.
    eapply bound_var_inline_letapp. eassumption.
    eapply Union_Disjoint_l; sets. eapply Disjoint_Singleton_l.
    intros Hc. eapply Hbv; eauto.
  - inv Hin. constructor; eauto.
    intros Hc; inv Hc.
    constructor.
  - inv Hub. constructor; eauto. intros Hc; eapply H1.
    eapply bound_var_inline_letapp in Hc; eauto. inv Hc; eauto. inv H.
    exfalso. eapply Hbv; eauto.
    eapply IHe; eauto.
  - inv Hub.
    constructor; eauto. intros Hc; eapply H1.
    eapply bound_var_inline_letapp in Hc; eauto. inv Hc; eauto. inv H.
    exfalso. eapply Hbv; eauto.
    eapply IHe; eauto.
  - inv Hin. constructor.
Qed.

Lemma bound_stem_inline_letapp x e C x' :
  inline_letapp e x = Some (C, x') ->
  bound_stem_ctx C \subset x |: bound_var e.
Proof.
  revert C. induction e using exp_ind'; simpl; intros C Hin;
              (try match goal with
                   | [ _ : context[inline_letapp ?E ?X] |- _ ] =>
                     destruct (inline_letapp E X) as [[C' z] | ] eqn:Hin'; inv Hin
                   end);
              (try now (normalize_bound_var; normalize_bound_stem_ctx;
                        eapply Union_Included; sets; eapply Included_trans;
                        [ eapply IHe; reflexivity | ]; sets)).
  congruence.

  normalize_bound_var; normalize_bound_stem_ctx. eapply Union_Included.
  eapply Included_trans. eapply name_in_fundefs_bound_var_fundefs. now sets.
  eapply Included_trans. eapply IHe. reflexivity. sets.

  inv Hin. normalize_bound_var. repeat normalize_bound_stem_ctx. sets.
  inv Hin. normalize_bound_var. repeat normalize_bound_stem_ctx. sets.
Qed.


Lemma inline_letapp_var_eq_alt x e C x' :
  inline_letapp e x = Some (C, x') ->
  (x' = x /\ x \in bound_stem_ctx C) \/ x' \in bound_stem_ctx C :|: occurs_free e.
Proof.
  revert C. induction e using exp_ind'; simpl; intros C Hin;
              (try match goal with
                   | [ _ : context[inline_letapp ?E ?X] |- _ ] =>
                     destruct (inline_letapp E X) as [[C' z] | ] eqn:Hin'; inv Hin
                   end).
  - destruct (IHe C' eq_refl); eauto. right.
    inv H. now left; eauto.
    normalize_occurs_free. normalize_bound_stem_ctx.
    rewrite !Union_assoc, Union_Setminus_Included; tci; sets. inv H; eauto.
  - congruence.
  - destruct (IHe C' eq_refl); eauto. right.
    inv H. now left; eauto.
    normalize_occurs_free. normalize_bound_stem_ctx. inv H; eauto.
    rewrite !Union_assoc. rewrite Union_Setminus_Included with (s3 := [set v]); tci. sets.
  - destruct (IHe C' eq_refl); eauto. right.
    inv H. now left; eauto.
    normalize_occurs_free. normalize_bound_stem_ctx.
    rewrite !Union_assoc, Union_Setminus_Included; tci; sets. inv H; eauto 20.
  - destruct (IHe C' eq_refl); eauto. right.
    inv H. now left; eauto.
    normalize_occurs_free. normalize_bound_stem_ctx.
    rewrite !Union_assoc, Union_Setminus_Included; tci; sets. inv H; eauto.
  - inv Hin. eauto.
  - destruct (IHe C' eq_refl); eauto. right.
    inv H. now left; eauto.
    normalize_occurs_free. normalize_bound_stem_ctx.
    rewrite Union_Setminus_Included; tci; sets. inv H; eauto.
  - destruct (IHe C' eq_refl); eauto. right.
    inv H. now left; eauto.
    normalize_occurs_free. normalize_bound_stem_ctx.
    rewrite !Union_assoc, Union_Setminus_Included; tci; sets. inv H; eauto.
  - inv Hin. normalize_occurs_free; sets.
Qed.


Ltac dec_vars :=
  repeat match goal with
         | [ H: (if var_dec ?X ?Y then _ else _) = 0 |- _] =>
           destruct (var_dec X Y); try inversion H; pi0
         end.


Lemma num_occur_inline_letapp e f C x x' :
  num_occur e f 0 ->
  inline_letapp e  x = Some (C, x') ->
  x <> f ->
  num_occur_ec C f 0 /\ x' <> f.
Proof.
  revert f C x x'.
  induction e using exp_ind'; intros g C y x' Hnum  Hin Hneq; simpl in Hin;
    (try match goal with
         | [ _ : context [inline_letapp ?E ?X ] |- _] => destruct (inline_letapp E X) as [[C' x''] | ] eqn:Hin'; inv Hin
         end); try congruence.
  - inv Hnum. pi0. eapply IHe in H4; eauto. destructAll. split; eauto.
    rewrite Nat.add_comm. constructor. eassumption.
  - inv Hnum. pi0. eapply IHe in H5; [| eassumption |]; eauto. destructAll. split; eauto.
    constructor. eassumption.
  - inv Hnum. pi0. eapply IHe in H5; [| eassumption |]; eauto. destructAll. split; eauto.
    constructor. eassumption.
  - inv Hnum. pi0. eapply IHe in Hin'; try eassumption; eauto. destructAll. split; eauto.
    constructor; eassumption.
  - Opaque num_occur_list. inv Hin. inv Hnum. split; eauto.
    replace (num_occur_list (v :: l) g) with (num_occur_list (v :: l) g + 0) by lia.
    econstructor. eauto. econstructor.
  - inv Hnum. eapply IHe in H4. 2:eauto. destructAll.
    split; eauto. now constructor. auto.
  - inv Hnum. pi0. eapply IHe in H4; eauto. destructAll. split; eauto.
    rewrite Nat.add_comm. constructor. eassumption.
  - inv Hin. inv Hnum.
    Transparent num_occur_list.
    simpl in *.
    destruct (term_util.var_dec g x'); subst; try congruence. split; eauto. econstructor.
Qed.

Lemma num_occur_inline_letapp_leq e f C x x' m :
  num_occur e f m ->
  inline_letapp e  x = Some (C, x') ->
  exists n, num_occur_ec C f n /\ n <= m.
Proof.
  revert m f C x x'. induction e using exp_ind'; intros m g C y x' Hnum  Hin; simpl in Hin;
                       (try match goal with
                            | [ _ : context [inline_letapp ?E ?X ] |- _] => destruct (inline_letapp E X) as [[C' x''] | ] eqn:Hin'; inv Hin
                            end); try congruence.
  - inv Hnum. eapply IHe in Hin'; eauto. destructAll.
    eexists; split. econstructor. eassumption. lia.
  - inv Hnum. eapply IHe in Hin'; eauto. destructAll.
    eexists; split. econstructor. eassumption. lia.
  - inv Hnum. eapply IHe in Hin'; eauto. destructAll.
    eexists; split. econstructor. eassumption. lia.
  - inv Hnum. eapply IHe in Hin'; eauto. destructAll.
    eexists; split. econstructor. eassumption. eassumption. lia.
  - inv Hnum. inv Hin. eexists; split. econstructor. now constructor. lia.
  - inv Hnum. eapply IHe in Hin'; eauto. destructAll.
    eexists; split. econstructor. eassumption. lia.
  - inv Hnum. eapply IHe in Hin'; eauto. destructAll.
    eexists; split. econstructor. eassumption. lia.
  - inv Hin. eexists. split. constructor. lia.
Qed.

Lemma inline_letapp_var_num_occur x e C x' :
  inline_letapp e x = Some (C, x') ->
  x' = x \/ (exists m, m > 0 /\ num_occur e x' m).
Proof.
  revert C. induction e using exp_ind'; simpl; intros C Hin;
              (try match goal with
                   | [ _ : context[inline_letapp ?E ?X] |- _ ] =>
                     destruct (inline_letapp E X) as [[C' z] | ] eqn:Hin'; inv Hin
                   end);
              try now (destruct (IHe C' eq_refl); eauto; destructAll; right;
                       eauto; eexists; split; [| econstructor; eassumption ]; lia).
  - congruence.
  - destruct (IHe C' eq_refl); eauto. right. destructAll.
    edestruct (proj2 (e_num_occur_mut x')).
    eexists. constructor. 2:{ econstructor; eauto. }
    lia.
  - inv Hin. now left.
  - inv Hin. right. eauto. eexists. split. 2:{ econstructor. }
    simpl. rewrite peq_true. lia.
Qed.

Lemma inline_letapp_None e x sig :
  inline_letapp e x = None ->
  inline_letapp (rename_all_ns sig e) x = None.
Proof.
  revert x sig; induction e; intros x sig Hinl; simpl in *;
    try match goal with
        | [H : context[inline_letapp ?E ?X] |- _ ] => destruct (inline_letapp E X) as [[C' y] | ] eqn:Hinl'; inv Hinl
        end;
    try now (erewrite IHe; [| eassumption ]).
  - reflexivity.
  - inv Hinl.
  - inv Hinl.
Qed.

Lemma inline_letapp_var_eq_alt' x e C x' :
  inline_letapp e x = Some (C, x') ->
  (x' = x /\ x \in bound_stem_ctx C) \/ x' \in bound_var e :|: occurs_free e.
Proof.
  revert C. induction e using exp_ind'; simpl; intros C Hin;
              (try match goal with
                   | [ _ : context[inline_letapp ?E ?X] |- _ ] =>
                     destruct (inline_letapp E X) as [[C' z] | ] eqn:Hin'; inv Hin
                   end).
  - destruct (IHe C' eq_refl); eauto. now inv H; eauto.
    normalize_occurs_free. normalize_bound_var.
    rewrite !Union_assoc, Union_Setminus_Included; tci; sets. inv H; eauto.
  - congruence.
  - destruct (IHe C' eq_refl); eauto.
    inv H. now left; eauto.
    normalize_occurs_free. normalize_bound_var. inv H; eauto.
    rewrite !Union_assoc. rewrite Union_Setminus_Included with (s3 := [set v]); tci. sets.
  - destruct (IHe C' eq_refl); eauto.
    inv H. now left; eauto.
    normalize_occurs_free. normalize_bound_var.
    rewrite !Union_assoc, Union_Setminus_Included; tci; sets. inv H; eauto 20.
  - destruct (IHe C' eq_refl); eauto.
    inv H. now left; eauto.
    normalize_occurs_free. normalize_bound_var.
    rewrite !Union_assoc, Union_Setminus_Included; tci; sets. inv H; eauto.
    eapply Included_trans. eapply name_in_fundefs_bound_var_fundefs. sets.
  - inv Hin. eauto.
  - destruct (IHe C' eq_refl); eauto.
    inv H. now left; eauto.
    normalize_occurs_free. normalize_bound_var.
    rewrite Union_Setminus_Included; tci; sets. inv H; eauto.
  - destruct (IHe C' eq_refl); eauto.
    inv H. now left; eauto.
    normalize_occurs_free. normalize_bound_var.
    rewrite !Union_assoc, Union_Setminus_Included; tci; sets. inv H; eauto.
  - inv Hin. normalize_occurs_free; sets.
Qed.

(* TODO move *)
Lemma num_occur_ec_eq C x m n :
  num_occur_ec C x m ->
  n = m ->
  num_occur_ec C x n.
Proof. intros; subst; eauto. Qed.

Lemma num_occur_eq C x m n :
  num_occur C x m ->
  n = m ->
  num_occur C x n.
Proof. intros; subst; eauto. Qed.

Lemma inline_letapp_gt_zero e v C x :
  inline_letapp e v = Some (C, x) ->
  v <> x ->
  exists m, m > 0 /\ num_occur e x m.
Proof.
  revert C.
  induction e using exp_ind'; intros C Hin Hneq; simpl in Hin;
    (try match goal with
         | [ _ : context [inline_letapp ?E ?X ] |- _] => destruct (inline_letapp E X) as [[C' x''] | ] eqn:Hin'; inv Hin
         end); try congruence; try (edestruct IHe; eauto; destructAll);
      (try now eexists; split; [| eapply num_occur_eq; econstructor; eauto ]; lia).
  - edestruct e_num_occur_fds. eexists. split. 2:{ eapply num_occur_eq. constructor; eassumption. reflexivity. }
    lia.
  - eexists. split. 2:{ constructor. }
    inv Hin. simpl. rewrite peq_true. lia.
Qed.

Lemma inline_letapp_num_occur e v C x z n :
  inline_letapp e v = Some (C, x) ->
  v <> z ->
  num_occur e z n ->
  if (var_dec z x) then num_occur_ec C z (n - 1) else num_occur_ec C z n.
Proof.
  revert C n.
  induction e using exp_ind'; intros C (* m Hleq *) m Hin Hneq Hnum; simpl in Hin;
    (try match goal with
         | [ _ : context [inline_letapp ?E ?X ] |- _] => destruct (inline_letapp E X) as [[C' x''] | ] eqn:Hin'; inv Hin
         end); try congruence; inv Hnum; destruct (var_dec z x); subst;
      (try now eapply num_occur_ec_eq; [ constructor; eapply IHe; eauto | lia ]);
      (try now edestruct inline_letapp_gt_zero; [ eassumption | eassumption | ]; destructAll;
       match goal with
       | [H1 : num_occur _ _ _, H2 : num_occur _ _ _ |- _ ] => eapply num_occur_det in H1; [| eapply H2 ]; subst
       end;
       eapply num_occur_ec_eq; [ constructor; eapply IHe; eauto | lia ]).
  - edestruct inline_letapp_gt_zero; [ eassumption | eassumption | ]; destructAll.
    match goal with
    | [H1 : num_occur _ _ _, H2 : num_occur _ _ _ |- _ ] => eapply num_occur_det in H1; [| eapply H2 ]; subst
    end.
    eapply num_occur_ec_eq. constructor. eapply IHe; eauto. eassumption. lia .
  - eapply num_occur_ec_eq. constructor. eapply IHe; eauto. eassumption. lia .
  - inv Hin. contradiction.
  - inv Hin. eapply num_occur_ec_eq. econstructor. now constructor. lia.
  - inv Hin. eapply num_occur_ec_eq. econstructor. simpl. rewrite peq_true. lia.
  - inv Hin. eapply num_occur_ec_eq. econstructor. simpl. rewrite peq_false; eauto.
Qed.


Require Import LambdaANF.algebra.
Require Import LambdaANF.logical_relations_cc.
From Stdlib Require Import Logic.Classical_Prop Logic.Classical_Pred_Type.

Open Scope alg_scope.

Section Post.

  Context {fuel : Type} {Hf : @fuel_resource fuel} {trace : Type} {Ht : @trace_resource trace}.


  Definition remove_steps_letapp cenv (P1 P2 P3 : @PostT fuel trace) :=
    forall (x f z : positive) (t : fun_tag) (ys : list map_util.M.elt) (e1 : exp)
           (rho1 : map_util.M.t val)
           (xs : list var) (e_b1 : exp) (v1 : val) (e2 e2' e_b2: exp) (rho2 rho2' rhoc2  rhoc1 : M.t val)
           (fl : fundefs) (h : var) (vs : list val) (rhoc1' : map_util.M.t val)
           (cin1 cin1' cin2 cin2' : fuel) (cout1 cout1' cout2 cout2' : trace),
      rho1 ! f = Some (Vfun rhoc1 fl h) ->
      get_list ys rho1 = Some vs ->
      find_def h fl = Some (t, xs, e_b1) ->
      set_lists xs vs (def_funs fl fl rhoc1 rhoc1) = Some rhoc1' ->
      bstep_fuel cenv rhoc1' e_b1 cin1 (Res v1) cout1 ->

      P1 (e_b1, rhoc1', cin1, cout1) (e_b2, rhoc2, cin2, cout2) (* when inlined body makes a tail call *) \/
      P1 (e_b1, rhoc1', cin1, cout1) (e_b2, rhoc2, cin2 <+> one (Ehalt z), cout2 <+> one (Ehalt z)) (* when inlined body returns *) ->
      P2 (e1, M.set x v1 rho1, cin1', cout1') (e2', rho2', cin2', cout2') ->
      P3 (Eletapp x f t ys e1, rho1, cin1 <+> cin1' <+> one (Eletapp x f t ys e1), cout1 <+> cout1' <+> one (Eletapp x f t ys e1))
         (e2, rho2, cin2 <+> cin2', cout2 <+> cout2').


  Definition remove_steps_letapp_OOT cenv (P1 P2 : @PostT fuel trace) :=
    forall (x f z: positive) (t : fun_tag) (ys : list map_util.M.elt) (e1 : exp) (rho1 : map_util.M.t val)
           (xs : list var) (e_b1 : exp) (r : res) (e2 e_b2 : exp) (rho2 rhoc1 : M.t val) (rhoc2 : env)
           (fl : fundefs) (h : var) (vs : list val) (rhoc1' : map_util.M.t val)
           (cin1 cin2  : fuel) (cout1 cout2 : trace),

      rho1 ! f = Some (Vfun rhoc1 fl h) ->
      get_list ys rho1 = Some vs ->
      find_def h fl = Some (t, xs, e_b1) ->
      set_lists xs vs (def_funs fl fl rhoc1 rhoc1) = Some rhoc1' ->
      bstep_fuel cenv rhoc1' e_b1 cin1 r cout1 ->

      P1 (e_b1, rhoc1', cin1, cout1) (e_b2, rhoc2, cin2, cout2) (* when inlined body makes a tail call *) \/
      P1 (e_b1, rhoc1', cin1, cout1) (e_b2, rhoc2, cin2 <+> one (Ehalt z), cout2 <+> one (Ehalt z)) (* when inlined body returns *) ->
      P2 (Eletapp x f t ys e1, rho1, cin1 <+> one (Eletapp x f t ys e1), cout1 <+> one (Eletapp x f t ys e1)) (e2, rho2, cin2, cout2).

End Post.

Section Inline_correct.

  Context {fuel : Type} {Hf : @fuel_resource fuel} {trace : Type} {Ht : @trace_resource trace}.

  Definition PostT  : Type := @PostT fuel trace.
  Definition PostGT : Type := @PostGT fuel trace.

  Context (cenv : ctor_env) (ctag : ctor_tag) (P1 P2 P3 : PostT) (PG : PostGT).

  Context (Hless_steps_letapp : remove_steps_letapp cenv P1 P2 P3)
          (Hless_steps_letapp_OOT : remove_steps_letapp_OOT cenv P1 P3)
          (HOOT: post_OOT P3).


  Lemma inline_letapp_correct k x sig f t ys e1 e2 e' C C' x' rho1 rho2 :
    (forall m rhoc rhoc' B f' xs vs e,
        m < k ->
        M.get f rho1 = Some (Vfun rhoc B f') ->
        find_def f' B = Some (t, xs, e) ->
        get_list ys rho1 = Some vs ->
        set_lists xs vs (def_funs B B rhoc rhoc) = Some rhoc' ->
        preord_exp cenv P1 PG m (e, rhoc') (C' |[ e' ]|, rho2)) ->

    (forall m rho1' rho2' rhoc B f' t xs e,
        m < k ->
        M.get f rho1 = Some (Vfun rhoc B f') ->
        find_def f' B = Some (t, xs, e) -> length xs = length ys ->
        preord_env_P_inj cenv PG (occurs_free e1) m (sig {x ~> x'}) rho1' rho2' ->
        preord_exp cenv P2 PG m (e1, rho1') (e2, rho2')) ->

    preord_env_P_inj cenv PG (occurs_free (Eletapp x f t ys e1)) k sig rho1 rho2 ->

    Disjoint _ (bound_var_ctx C' :|: bound_var_ctx C) (image sig (occurs_free e1 \\ [set x])) ->
    ~ x \in (image sig (occurs_free e1 \\ [set x])) ->
    interprable C' = true ->
    inline_letapp e' x = Some (C, x') ->

    preord_exp cenv P3 PG k (Eletapp x f t ys e1, rho1) (C' |[ C |[ e2 ]| ]|, rho2).
  Proof.
    revert C' k x sig f t ys e1 e2 C x' rho1 rho2; induction e';
      intros C' k x sig f' t ys e1 e2 C x' rho1 rho2 Hyp1 Hyp2 Hpre Hdis Him Hint Hin; simpl in Hin;
        try match goal with
        | [ _ : context [inline_letapp ?E ?X] |- _ ] =>
          (destruct (inline_letapp E X) as [ [C'' u] | ] eqn:Hin'; simpl in Hin; inv Hin)
        end.
    - intros r1 cin2 cout2 Hleq Hs1. inv Hs1.
      + exists OOT, cin2, <0>. split; [| split ]; eauto. constructor.
        unfold one. erewrite one_eq. eassumption.
        eapply HOOT; eauto. now simpl; eauto.
      + edestruct (IHe' (comp_ctx_f C' (Econstr_c v c l Hole_c)) k) with (C := C'')
          as [r2 [cout2 [cout2' [Hs2 [Hp2 Hv2]]]]].
        9:{ econstructor 2; eauto. }
        * rewrite <- app_ctx_f_fuse. simpl ( _ |[ _ ]|). eapply Hyp1.
        * eapply Hyp2.
        * eassumption.
        * destruct  bound_var_ctx_comp_ctx as [Heq1 _ ]. rewrite Heq1.
          rewrite bound_var_Econstr_c, bound_var_Hole_c in *. simpl.
          eauto 10 with Ensembles_DB nocore.
        * eassumption.
        * eapply interprable_comp_f_l; eauto.
        * eassumption.
        * eassumption.
        * rewrite <- app_ctx_f_fuse in *. simpl in *. do 3 eexists.
          split; [| split ]. eassumption. eassumption. eassumption.
    - inv Hin.
    - intros r1 cin2 cout2 Hleq Hs1. inv Hs1.
      + exists OOT, cin2, <0>. split; [| split ]; eauto. constructor.
        unfold one. erewrite one_eq. eassumption.
        eapply HOOT; eauto. now simpl; eauto.
      + edestruct (IHe' (comp_ctx_f C' (Eproj_c v c n v0 Hole_c)) k) with (C := C'') as [r2 [cin2' [cout2' [Hs2 [Hp2 Hv2]]]]].
        9:{ econstructor 2; eauto. }
        * rewrite <- app_ctx_f_fuse. simpl ( _ |[ _ ]|). eapply Hyp1.
        * eapply Hyp2.
        * eassumption.
        * destruct  bound_var_ctx_comp_ctx as [Heq1 _ ]. rewrite Heq1.
          rewrite bound_var_Eproj_c, bound_var_Hole_c in *.
          eauto 10 with Ensembles_DB nocore.
        * eassumption.
        * eapply interprable_comp_f_l; eauto.
        * eassumption.
        * eassumption.
        * rewrite <- app_ctx_f_fuse in *. simpl in *. do 3 eexists.
          split; [| split ]. eassumption. eassumption. eassumption.
    - intros r1 cin2 cout2 Hleq Hs1. inv Hs1.
      + exists OOT, cin2, <0>. split; [| split ]; eauto. constructor.
        unfold one. erewrite one_eq. eassumption.
        eapply HOOT; eauto. now simpl; eauto.
      + edestruct (IHe' (comp_ctx_f C' (Eletapp_c v v0 f l Hole_c)) k) with (C := C'') as [r2 [cin2' [cout2' [Hs2 [Hp2 Hv2]]]]].
        9:{ econstructor 2; eauto. }
        * rewrite <- app_ctx_f_fuse. simpl ( _ |[ _ ]|). eapply Hyp1.
        * eapply Hyp2.
        * eassumption.
        * destruct  bound_var_ctx_comp_ctx as [Heq1 _ ]. rewrite Heq1.
          rewrite bound_var_Eletapp_c, bound_var_Hole_c in *. xsets.
        * eassumption.
        * eapply interprable_comp_f_l; eauto.
        * eassumption.
        * eassumption.
        * rewrite <- app_ctx_f_fuse in *. simpl in *. do 3 eexists.
          split; [| split ]. eassumption. eassumption. eassumption.
    - intros r1 cin2 cout2  Hleq Hs1. inv Hs1.
      + exists OOT, cin2, <0>. split; [| split ]; eauto. constructor.
        unfold one. erewrite one_eq. eassumption.
        eapply HOOT; eauto. now simpl; eauto.
      + edestruct (IHe' (comp_ctx_f C' (Efun1_c f  Hole_c)) k) with (C := C'') as [r2 [cin2' [cout2' [Hs2 [Hp2 Hv2]]]]].
        9:{ econstructor 2; eauto. }
        * rewrite <- app_ctx_f_fuse. simpl ( _ |[ _ ]|). eapply Hyp1.
        * eapply Hyp2.
        * eassumption.
        * destruct  bound_var_ctx_comp_ctx as [Heq1 _ ]. rewrite Heq1.
          rewrite bound_var_Fun1_c, bound_var_Hole_c in *. xsets.
        * eassumption.
        * eapply interprable_comp_f_l; eauto.
        * eassumption.
        * eassumption.
        * rewrite <- app_ctx_f_fuse in *. simpl in *. do 3 eexists.
          split; [| split ]. eassumption. eassumption. eassumption.
    - inv Hin. simpl (_ |[ _ ]|).
      intros r1 cin2 cout2 Hleq Hs1. inv Hs1.
      + exists OOT, cin2, <0>. split; [| split ]; eauto. constructor.
        unfold one. erewrite one_eq. eassumption.
        eapply HOOT; eauto. now simpl; eauto.
      + rewrite !to_nat_add in Hleq. assert (Hone := to_nat_one (exp_to_fin (Eletapp x' f' t ys e1))).

        inv H.

        * edestruct (Hyp1 (k -1)) as [r2 [cin2' [cout2' [Hs2 [Hp2 Hv2]]]]]; [ | | | | | | now eapply H13 | ]; eauto; rewrite !to_nat_add in Hleq.

          unfold one in *; simpl in *; lia.
          unfold one in *; simpl in *; lia.

          destruct r2; [ simpl in Hv2; contradiction | ].
          eapply interpret_ctx_bstep_l in Hs2; [| eassumption ]. destructAll.
          inv H2.

          edestruct (Hyp2 (k - 1 - to_nat cin1)) as [r3 [cin3 [cout3 [Hs3 [Hp3 Hv3]]]]];
            [ | |  | | | | now eapply H14 | ]; eauto.
          unfold one in *; simpl in *; lia.

          rewrite (get_list_length_eq _ _ _ H7). eapply set_lists_length_eq. now eauto.

          { eapply preord_env_P_inj_set_alt; [| eassumption | eassumption ].
            eapply preord_env_P_inj_eq_env_P; [| eapply eq_env_P_refl | ].
            2:{ eapply interpret_ctx_eq_env_P with (fuel := fuel). eassumption. sets. }
            eapply preord_env_P_inj_antimon.
            eapply preord_env_P_inj_monotonic; [| eassumption ]. lia. normalize_occurs_free. sets.  }

          unfold one in *; simpl in *; lia.
          inv H.

          do 3 eexists. split; [| split ].

          -- eapply interpret_ctx_bstep_r. eassumption.
             constructor 2. econstructor; eauto.

          -- rewrite !plus_assoc. rewrite (plus_comm cin3). rewrite (plus_comm cout3).
             rewrite  <- (algebra.plus_assoc cin). rewrite  <- (algebra.plus_assoc _ _ cin3).
             rewrite  <- (algebra.plus_assoc cout). rewrite  <- (algebra.plus_assoc _ _ cout3).
             do 2 rewrite <- algebra.plus_assoc.

             eapply Hless_steps_letapp; try eassumption. left. eassumption.

          -- eapply preord_res_monotonic. eassumption. rewrite !to_nat_add. unfold one in *. simpl in *; lia.
        * edestruct (Hyp1 (k -1)) as [r2 [cin2' [cout2' [Hs2 [Hp2 Hv2]]]]]; [ | | | | | | now eapply H13 | ]; eauto.

          unfold one in *; simpl in *; lia. unfold one in *; simpl in *; lia.

          destruct r2; [ | simpl in Hv2; contradiction ].

          eexists OOT, cin2', cout2'. split; [| split ].
          now eapply eval_ctx_app_OOT_Eapp; eauto.
          now eapply Hless_steps_letapp_OOT; eauto.
          simpl; eauto.
    - intros r1 cin2 cout2 Hleq Hs1. inv Hs1.
      + exists OOT, cin2, <0>. split; [| split ]; eauto. constructor.
        unfold one. erewrite one_eq. eassumption.
        eapply HOOT; eauto. now simpl; eauto.
      + rewrite !to_nat_add in Hleq. assert (Hone := to_nat_one (exp_to_fin (Eletapp x f' t ys e1))). inv H.

        * edestruct (Hyp1 (k -1)) as [r2 [cin2' [cout2' [Hs2 [Hp2 Hv2]]]]]; [ | | | | | | now eapply H13 | ]; eauto; rewrite to_nat_add in Hleq.
          unfold one in *. simpl in *; lia. unfold one in *; simpl in *; lia.


          destruct r2; [ simpl in Hv2; contradiction | ].
          eapply interpret_ctx_bstep_l in Hs2; [| eassumption ]. destructAll.
          inv H2. inv H.

        * edestruct (Hyp1 (k -1)) as [r2 [cin2' [cout2' [Hs2 [Hp2 Hv2]]]]]; [ | | | | | | now eapply H13 | ]; eauto.
          unfold one in *; simpl in *; lia. unfold one in *; simpl in *; lia.

          destruct r2; [ | simpl in Hv2; contradiction ].

          eexists OOT, cin2', cout2'. split; [| split ].

          now eapply eval_ctx_app_OOT_Eprim_val; eassumption.

          eapply Hless_steps_letapp_OOT; try eassumption. left. eassumption.
          simpl; eauto.
    - intros r1 cin2 cout2 Hleq Hs1. inv Hs1.
      + exists OOT, cin2, <0>. split; [| split ]; eauto. constructor.
        unfold one. erewrite one_eq. eassumption.
        eapply HOOT; eauto. now simpl; eauto.
      + rewrite !to_nat_add in Hleq. assert (Hone := to_nat_one (exp_to_fin (Eletapp x f' t ys e1))). inv H.

        * edestruct (Hyp1 (k -1)) as [r2 [cin2' [cout2' [Hs2 [Hp2 Hv2]]]]]; [ | | | | | | now eapply H13 | ]; eauto; rewrite to_nat_add in Hleq.
          unfold one in *. simpl in *; lia. unfold one in *; simpl in *; lia.


          destruct r2; [ simpl in Hv2; contradiction | ].
          eapply interpret_ctx_bstep_l in Hs2; [| eassumption ]. destructAll.
          inv H2. inv H.

        * edestruct (Hyp1 (k -1)) as [r2 [cin2' [cout2' [Hs2 [Hp2 Hv2]]]]]; [ | | | | | | now eapply H13 | ]; eauto.
          unfold one in *; simpl in *; lia. unfold one in *; simpl in *; lia.

          destruct r2; [ | simpl in Hv2; contradiction ].

          eexists OOT, cin2', cout2'. split; [| split ].

          now eapply eval_ctx_app_OOT_Eprim; eassumption.

          eapply Hless_steps_letapp_OOT; try eassumption. left. eassumption.
          simpl; eauto.

    - inv Hin. simpl (_ |[ _ ]|).
      intros r1 cin2 cout2 Hleq Hs1. inv Hs1.
      + exists OOT, cin2, <0>. split; [| split ]; eauto. constructor.
        unfold one. erewrite one_eq. eassumption.
        eapply HOOT; eauto. now simpl; eauto.
      + rewrite !to_nat_add in Hleq. assert (Hone := to_nat_one (exp_to_fin (Eletapp x f' t ys e1))). inv H.

        * edestruct (Hyp1 (k -1)) as [r2 [cin2' [cout2' [Hs2 [Hp2 Hv2]]]]]; [ | | | | | | now eapply H13 | ]; eauto; rewrite to_nat_add in Hleq.
          unfold one in *; simpl in *; lia.
          unfold one in *; simpl in *; lia.

          destruct r2; [ simpl in Hv2; contradiction | ].
          eapply interpret_ctx_bstep_l in Hs2; [| eassumption ]. destructAll.
          inv H2. inv H.

          edestruct (Hyp2 (k - 1 - to_nat cin1)) as [r3 [cin3 [cout3 [Hs3 [Hp3 Hv3]]]]];
            [ | | | | | | now eapply H14 | ]; eauto.
          unfold one in *; simpl in *; lia.

          rewrite (get_list_length_eq _ _ _ H7). eapply set_lists_length_eq. now eauto.

          { eapply preord_env_P_inj_set_l; [| eassumption | eassumption ].
            eapply preord_env_P_inj_eq_env_P; [| eapply eq_env_P_refl | ].
            2:{ eapply interpret_ctx_eq_env_P with (fuel := fuel). eassumption. sets. }
            eapply preord_env_P_inj_antimon.
            eapply preord_env_P_inj_monotonic; [| eassumption ]. lia. normalize_occurs_free. sets. }

          unfold one in *; simpl in *; lia.

          do 3 eexists. split. eapply interpret_ctx_bstep_r. eassumption. eassumption.

          split.
          eapply Hless_steps_letapp; try eassumption. rewrite !plus_zero in Hp2.

          now right; eauto.

          eapply preord_res_monotonic. eassumption. rewrite !to_nat_add. unfold one in *; simpl in *; lia.

        * edestruct (Hyp1 (k -1)) as [r2 [cin2' [cout2' [Hs2 [Hp2 Hv2]]]]]; [ | | | | | | now eapply H13 | ]; eauto.

          unfold one in *. simpl in *; lia. unfold one in *; simpl in *; lia.

          destruct r2; [ | simpl in Hv2; contradiction ].

          exists OOT. eexists cin2', cout2'. split; [| split ]; [| now eapply Hless_steps_letapp_OOT; eauto | now eauto ].

          eapply eval_ctx_app_Ehalt_div. eassumption. eassumption.

          Unshelve. exact 1%positive. exact 1%positive. exact 1%positive. exact 1%positive. exact 1%positive.
  Qed.


  Lemma eq_env_P_def_funs_not_in_P_r' (B B' : fundefs) (P : Ensemble M.elt)
        (rho : term.M.t val) (rho1 rho2 : M.t val) :
    eq_env_P P rho1 (def_funs B' B rho rho2) ->
    Disjoint M.elt P (name_in_fundefs B) ->
    eq_env_P P rho1 rho2.
  Proof.
    intros H1 Hdis x Hin. assert (Hin' := Hin). eapply H1 in Hin.
    destruct (Decidable_name_in_fundefs B). destruct (Dec x).
    - exfalso. eapply Hdis. constructor; eassumption.
    - rewrite def_funs_neq in Hin ; eauto.
  Qed.

  (* TOPO move to eval.v *)
  Lemma interpret_ctx_fuel_env_eq_P S C rho rho' (cin : fuel) (cout : trace) :
    interpret_ctx_fuel cenv C rho cin (Res rho') cout ->
    Disjoint _ (bound_stem_ctx C) S ->
    eq_env_P S rho rho'.
  Proof.
    revert rho rho' cin cout. induction C; intros rho rho' cin cout Hi Hd.
    - inv Hi. eapply eq_env_P_refl. inv H0.
    - inv Hi. inv H0.
      normalize_bound_stem_ctx_in_ctx. eapply IHC in H10; [| now sets ].
      eapply eq_env_P_set_not_in_P_l'. eassumption. sets.
    - inv Hi. inv H0.
      normalize_bound_stem_ctx_in_ctx. eapply IHC in H12; [| now sets ].
      eapply eq_env_P_set_not_in_P_l'. eassumption. sets.
    - inv Hi. inv H0.
    - inv Hi. inv H0.
    - inv Hi. inv H0.
      normalize_bound_stem_ctx_in_ctx. eapply IHC in H15; [| now sets ].
      eapply eq_env_P_set_not_in_P_l'. eassumption. sets.
    - inv Hi. inv H0.
    - inv Hi. inv H0.
      normalize_bound_stem_ctx_in_ctx. eapply IHC in H7; [| now sets ].
      eapply eq_env_P_sym in H7. eapply eq_env_P_def_funs_not_in_P_r' in H7.
      eapply eq_env_P_sym. eassumption.
      sets.
    - inv Hi. inv H0.
  Qed.


  Lemma inline_letapp_correct_alt k x z sig f t ys e1 e2 e' C C' x' rho1 rho2 :
    (forall m rhoc rhoc' B f' xs vs e,
        m < k ->
        M.get f rho1 = Some (Vfun rhoc B f') ->
        find_def f' B = Some (t, xs, e) ->
        get_list ys rho1 = Some vs ->
        set_lists xs vs (def_funs B B rhoc rhoc) = Some rhoc' ->
        preord_exp cenv P1 PG m (e, rhoc') (C' |[ e' ]|, rho2)) ->

    (forall m rho1' rho2' rhoc B f' t xs e,
        m < k ->
        M.get f rho1 = Some (Vfun rhoc B f') ->
        find_def f' B = Some (t, xs, e) -> length xs = length ys ->
        eq_env_P (Complement _ [set x]) rho1 rho1' ->
        eq_env_P (Complement _ (bound_var_ctx C :|: bound_var_ctx C')) rho2 rho2' ->
        Dom_map rho1' <--> x |: Dom_map rho1 ->
        preord_env_P_inj cenv PG (occurs_free e1) m (sig {x ~> x'}) rho1' rho2' ->
        preord_exp cenv P2 PG m (e1, rho1') (e2, rho2')) ->

    preord_env_P_inj cenv PG (occurs_free (Eletapp x f t ys e1)) k sig rho1 rho2 ->

    Disjoint _ (bound_var_ctx C' :|: bound_var_ctx C) (image sig (occurs_free e1 \\ [set x])) ->

    interprable C' = true ->
    inline_letapp e' z = Some (C, x') ->

    preord_exp cenv P3 PG k (Eletapp x f t ys e1, rho1) (C' |[ C |[ e2 ]| ]|, rho2).
  Proof.
   revert C' k x sig f t ys e1 e2 C x' rho1 rho2; induction e';
      intros C' k x sig f' t ys e1 e2 C x' rho1 rho2 Hyp1 Hyp2 Hpre Hdis Hint Hin; simpl in Hin;
        try match goal with
        | [ _ : context [inline_letapp ?E ?X] |- _ ] =>
          (destruct (inline_letapp E X) as [ [C'' u] | ] eqn:Hin'; simpl in Hin; inv Hin)
        end.
    - intros r1 cin2 cout2 Hleq Hs1. inv Hs1.
      + exists OOT, cin2, <0>. split; [| split ]; eauto. constructor.
        unfold one. erewrite one_eq. eassumption.
        eapply HOOT; eauto. now simpl; eauto.
      + edestruct (IHe' (comp_ctx_f C' (Econstr_c v c l Hole_c)) k) with (C := C'')
          as [r2 [cout2 [cout2' [Hs2 [Hp2 Hv2]]]]].
        8:{ econstructor 2; eauto. }
        * rewrite <- app_ctx_f_fuse. simpl ( _ |[ _ ]|). eapply Hyp1.
        * intros. eapply Hyp2; eauto. eapply eq_env_P_antimon. eassumption.
          eapply Complement_antimon. repeat normalize_bound_var_ctx; sets.
        * eassumption.
        * destruct  bound_var_ctx_comp_ctx as [Heq1 _ ]. rewrite Heq1.
          rewrite bound_var_Econstr_c, bound_var_Hole_c in *. xsets.
        * eapply interprable_comp_f_l; eauto.
        * reflexivity.
        * eassumption.
        * rewrite <- app_ctx_f_fuse in *. simpl in *. do 3 eexists.
          split; [| split ]. eassumption. eassumption. eassumption.
    - inv Hin.
    - intros r1 cin2 cout2 Hleq Hs1. inv Hs1.
      + exists OOT, cin2, <0>. split; [| split ]; eauto. constructor.
        unfold one. erewrite one_eq. eassumption.
        eapply HOOT; eauto. now simpl; eauto.
      + edestruct (IHe' (comp_ctx_f C' (Eproj_c v c n v0 Hole_c)) k) with (C := C'') as [r2 [cin2' [cout2' [Hs2 [Hp2 Hv2]]]]].
        8:{ econstructor 2; eauto. }
        * rewrite <- app_ctx_f_fuse. simpl ( _ |[ _ ]|). eapply Hyp1.
        * intros. eapply Hyp2; eauto. eapply eq_env_P_antimon. eassumption.
          eapply Complement_antimon. repeat normalize_bound_var_ctx; sets.
        * eassumption.
        * destruct  bound_var_ctx_comp_ctx as [Heq1 _ ]. rewrite Heq1.
          rewrite bound_var_Eproj_c, bound_var_Hole_c in *. xsets.
        * eapply interprable_comp_f_l; eauto.
        * reflexivity.
        * eassumption.
        * rewrite <- app_ctx_f_fuse in *. simpl in *. do 3 eexists.
          split; [| split ]. eassumption. eassumption. eassumption.
    - intros r1 cin2 cout2 Hleq Hs1. inv Hs1.
      + exists OOT, cin2, <0>. split; [| split ]; eauto. constructor.
        unfold one. erewrite one_eq. eassumption.
        eapply HOOT; eauto. now simpl; eauto.
      + edestruct (IHe' (comp_ctx_f C' (Eletapp_c v v0 f l Hole_c)) k) with (C := C'') as [r2 [cin2' [cout2' [Hs2 [Hp2 Hv2]]]]].
        8:{ econstructor 2; eauto. }
        * rewrite <- app_ctx_f_fuse. simpl ( _ |[ _ ]|). eapply Hyp1.
        * intros. eapply Hyp2; eauto. eapply eq_env_P_antimon. eassumption.
          eapply Complement_antimon. repeat normalize_bound_var_ctx; sets.
        * eassumption.
        * destruct  bound_var_ctx_comp_ctx as [Heq1 _ ]. rewrite Heq1.
          rewrite bound_var_Eletapp_c, bound_var_Hole_c in *. xsets.
        * eapply interprable_comp_f_l; eauto.
        * reflexivity.
        * eassumption.
        * rewrite <- app_ctx_f_fuse in *. simpl in *. do 3 eexists.
          split; [| split ]. eassumption. eassumption. eassumption.
    - intros r1 cin2 cout2  Hleq Hs1. inv Hs1.
      + exists OOT, cin2, <0>. split; [| split ]; eauto. constructor.
        unfold one. erewrite one_eq. eassumption.
        eapply HOOT; eauto. now simpl; eauto.
      + edestruct (IHe' (comp_ctx_f C' (Efun1_c f  Hole_c)) k) with (C := C'') as [r2 [cin2' [cout2' [Hs2 [Hp2 Hv2]]]]].
        8:{ econstructor 2; eauto. }
        * rewrite <- app_ctx_f_fuse. simpl ( _ |[ _ ]|). eapply Hyp1.
        * intros. eapply Hyp2; eauto. eapply eq_env_P_antimon. eassumption.
          eapply Complement_antimon. repeat normalize_bound_var_ctx; sets.
        * eassumption.
        * destruct  bound_var_ctx_comp_ctx as [Heq1 _ ]. rewrite Heq1.
          rewrite bound_var_Fun1_c, bound_var_Hole_c in *. xsets.
        * eapply interprable_comp_f_l; eauto.
        * reflexivity.
        * eassumption.
        * rewrite <- app_ctx_f_fuse in *. simpl in *. do 3 eexists.
          split; [| split ]. eassumption. eassumption. eassumption.
    - inv Hin. simpl (_ |[ _ ]|).
      intros r1 cin2 cout2 Hleq Hs1. inv Hs1.
      + exists OOT, cin2, <0>. split; [| split ]; eauto. constructor.
        unfold one. erewrite one_eq. eassumption.
        eapply HOOT; eauto. now simpl; eauto.
      + rewrite !to_nat_add in Hleq. assert (Hone := to_nat_one (exp_to_fin (Eletapp x' f' t ys e1))).

        inv H.

        * edestruct (Hyp1 (k -1)) as [r2 [cin2' [cout2' [Hs2 [Hp2 Hv2]]]]]; [ | | | | | | now eapply H13 | ]; eauto; rewrite !to_nat_add in Hleq.

          unfold one in *; simpl in *; lia.
          unfold one in *; simpl in *; lia.

          destruct r2; [ simpl in Hv2; contradiction | ].
          eapply interpret_ctx_bstep_l in Hs2; [| eassumption ]. destructAll.
          inv H2. inv H.

          edestruct (Hyp2 (k - 1 - to_nat cin1)) as [r3 [cin3 [cout3 [Hs3 [Hp3 Hv3]]]]];
            [ | | | | | | | | |now eapply H14 | ]; eauto.

          unfold one in *; simpl in *; lia.

          rewrite (get_list_length_eq _ _ _ H7). eapply set_lists_length_eq. now eauto.

          eapply eq_env_P_sym. eapply eq_env_P_set_not_in_P_l. eapply eq_env_P_refl. now eauto.
          eapply eq_env_P_sym. eapply eq_env_P_set_not_in_P_l. eapply eq_env_P_sym.
          eapply interpret_ctx_fuel_env_eq_P (* with (fuel := fuel) *). eassumption.
          eapply Disjoint_sym. eapply Complement_Disjoint.
          eapply Included_trans. eapply bound_stem_var. now sets.
          intros Hc. eapply Hc. now eauto.

          rewrite Dom_map_set. reflexivity.

          { eapply preord_env_P_inj_set_alt; [| eassumption |  ].
            eapply preord_env_P_inj_eq_env_P; [| eapply eq_env_P_refl | ].
            2:{ eapply interpret_ctx_eq_env_P with (fuel := fuel). eassumption. sets. }
            eapply preord_env_P_inj_antimon.
            eapply preord_env_P_inj_monotonic; [| eassumption ]. lia. normalize_occurs_free. sets.
            intros Hc. eapply Hdis. constructor; [| eassumption ]. normalize_bound_var_ctx. eauto. }

          unfold one in *; simpl in *; lia.

          do 3 eexists. split; [| split ].

          -- eapply interpret_ctx_bstep_r. eassumption.
             constructor 2. econstructor; eauto.

          -- rewrite !plus_assoc. rewrite (plus_comm cin3). rewrite (plus_comm cout3).
             rewrite  <- (algebra.plus_assoc cin). rewrite  <- (algebra.plus_assoc _ _ cin3).
             rewrite  <- (algebra.plus_assoc cout). rewrite  <- (algebra.plus_assoc _ _ cout3).
             do 2 rewrite <- algebra.plus_assoc. eapply Hless_steps_letapp; eauto.

          -- eapply preord_res_monotonic. eassumption. rewrite !to_nat_add. unfold one in *. simpl in *; lia.
        * edestruct (Hyp1 (k -1)) as [r2 [cin2' [cout2' [Hs2 [Hp2 Hv2]]]]]; [ | | | | | | now eapply H13 | ]; eauto.

          unfold one in *; simpl in *; lia. unfold one in *; simpl in *; lia.

          destruct r2; [ | simpl in Hv2; contradiction ].

          eexists OOT, cin2', cout2'. split; [| split ].
          now eapply eval_ctx_app_OOT_Eapp; eauto.
          now eapply Hless_steps_letapp_OOT; eauto.
          simpl; eauto.
    - intros r1 cin2 cout2 Hleq Hs1. inv Hs1.
      + exists OOT, cin2, <0>. split; [| split ]; eauto. constructor.
        unfold one. erewrite one_eq. eassumption.
        eapply HOOT; eauto. now simpl; eauto.
      + rewrite !to_nat_add in Hleq. assert (Hone := to_nat_one (exp_to_fin (Eletapp x f' t ys e1))). inv H.

        * edestruct (Hyp1 (k -1)) as [r2 [cin2' [cout2' [Hs2 [Hp2 Hv2]]]]]; [ | | | | | | now eapply H13 | ]; eauto; rewrite to_nat_add in Hleq.
          unfold one in *. simpl in *; lia. unfold one in *; simpl in *; lia.


          destruct r2; [ simpl in Hv2; contradiction | ].
          eapply interpret_ctx_bstep_l in Hs2; [| eassumption ]. destructAll.
          inv H2. inv H.

        * edestruct (Hyp1 (k -1)) as [r2 [cin2' [cout2' [Hs2 [Hp2 Hv2]]]]]; [ | | | | | | now eapply H13 | ]; eauto.
          unfold one in *; simpl in *; lia. unfold one in *; simpl in *; lia.

          destruct r2; [ | simpl in Hv2; contradiction ].

          eexists OOT, cin2', cout2'. split; [| split ].

          now eapply eval_ctx_app_OOT_Eprim_val; eassumption.

          now eapply Hless_steps_letapp_OOT; eauto.
          simpl; eauto.
    - intros r1 cin2 cout2 Hleq Hs1. inv Hs1.
      + exists OOT, cin2, <0>. split; [| split ]; eauto. constructor.
        unfold one. erewrite one_eq. eassumption.
        eapply HOOT; eauto. now simpl; eauto.
      + rewrite !to_nat_add in Hleq. assert (Hone := to_nat_one (exp_to_fin (Eletapp x f' t ys e1))). inv H.

        * edestruct (Hyp1 (k -1)) as [r2 [cin2' [cout2' [Hs2 [Hp2 Hv2]]]]]; [ | | | | | | now eapply H13 | ]; eauto; rewrite to_nat_add in Hleq.
          unfold one in *. simpl in *; lia. unfold one in *; simpl in *; lia.


          destruct r2; [ simpl in Hv2; contradiction | ].
          eapply interpret_ctx_bstep_l in Hs2; [| eassumption ]. destructAll.
          inv H2. inv H.

        * edestruct (Hyp1 (k -1)) as [r2 [cin2' [cout2' [Hs2 [Hp2 Hv2]]]]]; [ | | | | | | now eapply H13 | ]; eauto.
          unfold one in *; simpl in *; lia. unfold one in *; simpl in *; lia.

          destruct r2; [ | simpl in Hv2; contradiction ].

          eexists OOT, cin2', cout2'. split; [| split ].

          now eapply eval_ctx_app_OOT_Eprim; eassumption.

          now eapply Hless_steps_letapp_OOT; eauto.
          simpl; eauto.
    - inv Hin. simpl (_ |[ _ ]|).
      intros r1 cin2 cout2 Hleq Hs1. inv Hs1.
      + exists OOT, cin2, <0>. split; [| split ]; eauto. constructor.
        unfold one. erewrite one_eq. eassumption.
        eapply HOOT; eauto. now simpl; eauto.
      + rewrite !to_nat_add in Hleq. assert (Hone := to_nat_one (exp_to_fin (Eletapp x f' t ys e1))). inv H.

        * edestruct (Hyp1 (k -1)) as [r2 [cin2' [cout2' [Hs2 [Hp2 Hv2]]]]]; [ | | | | | | now eapply H13 | ]; eauto; rewrite to_nat_add in Hleq.
          unfold one in *; simpl in *; lia.
          unfold one in *; simpl in *; lia.

          destruct r2; [ simpl in Hv2; contradiction | ].
          eapply interpret_ctx_bstep_l in Hs2; [| eassumption ]. destructAll.
          inv H2. inv H.

          edestruct (Hyp2 (k - 1 - to_nat cin1)) as [r3 [cin3 [cout3 [Hs3 [Hp3 Hv3]]]]];
            [ | | | | | | | | | now eapply H14 | ]; eauto.
          unfold one in *; simpl in *; lia.

          rewrite (get_list_length_eq _ _ _ H7). eapply set_lists_length_eq. now eauto.

          eapply eq_env_P_sym. eapply eq_env_P_set_not_in_P_l. eapply eq_env_P_refl. now eauto.

          eapply interpret_ctx_fuel_env_eq_P. eassumption. normalize_bound_var_ctx.
          normalize_sets. eapply Disjoint_sym. eapply Complement_Disjoint.
          eapply Included_trans. eapply bound_stem_var. now sets.

          rewrite Dom_map_set. reflexivity.


          { eapply preord_env_P_inj_set_l; [| eassumption | eassumption ].
            eapply preord_env_P_inj_eq_env_P; [| eapply eq_env_P_refl | ].
            2:{ eapply interpret_ctx_eq_env_P with (fuel := fuel). eassumption. sets. }
            eapply preord_env_P_inj_antimon.
            eapply preord_env_P_inj_monotonic; [| eassumption ]. lia. normalize_occurs_free. sets. }

          unfold one in *; simpl in *; lia.
          do 3 eexists. split. eapply interpret_ctx_bstep_r. eassumption. eassumption.

          split.
          eapply Hless_steps_letapp; eauto. rewrite !plus_zero in Hp2. now eauto.

          eapply preord_res_monotonic. eassumption. rewrite !to_nat_add. unfold one in *; simpl in *; lia.

        * edestruct (Hyp1 (k -1)) as [r2 [cin2' [cout2' [Hs2 [Hp2 Hv2]]]]]; [ | | | | | | now eapply H13 | ]; eauto.

          unfold one in *. simpl in *; lia. unfold one in *; simpl in *; lia.

          destruct r2; [ | simpl in Hv2; contradiction ].

          exists OOT. eexists cin2', cout2'. split; [| split ]; [| now eapply Hless_steps_letapp_OOT; eauto | now eauto ].

          eapply eval_ctx_app_Ehalt_div. eassumption. eassumption.

          Unshelve. exact 1%positive. exact 1%positive. exact 1%positive. exact 1%positive. exact 1%positive.
  Qed.

  Lemma inline_letapp_eval_l C e x x' v rho rho' (cin : fuel) (cout : trace):
    inline_letapp e x = Some (C, x') ->
    interpret_ctx_fuel cenv C rho cin (Res rho') cout ->
    M.get x' rho' = Some v ->
    exists cin' cout', bstep_fuel cenv rho e cin' (Res v) cout' /\
                       ((cin' = cin /\ cout' = cout ) \/
                        (cin' = plus cin (one (Ehalt 1%positive)) /\ cout' = plus cout (one (Ehalt 1%positive)))).
  Proof.
    revert C x x' v rho rho' cin cout.
    induction e using exp_ind'; simpl; intros C z z' v1 rho rho' cin cout Hin Hinp Hget;
      try (match goal with
           | [ _ : context[inline_letapp ?E ?X] |- _ ] =>
             destruct (inline_letapp E X) as [[C' w] | ] eqn:Hin'; inv Hin
           end); (try now inv Hin); try (now inv Hinp; inv H0; eapply IHe; eauto);
        try (now inv Hinp; inv H0;
             match goal with
             | [ H : interpret_ctx_fuel _ _ _ _ _ _ |- _ ] => eapply IHe in H; eauto; destructAll
             end;
             do 2 eexists; split;
             [ econstructor; econstructor; eauto |
               inv H1;
               [ destructAll; left; now split; eauto | destructAll; right; rewrite !plus_assoc; split; rewrite (plus_comm (one _ )); eauto ]]).
    - inv Hin. inv Hinp. inv H0. inv H15; [| congruence ].
      rewrite M.gss in *. inv Hget. do 2 eexists. split.
      + econstructor. econstructor; eauto.
      + left. rewrite !plus_assoc. rewrite !plus_zero. simpl. split; eauto.
    - inv Hin. inv Hinp.
      do 2 eexists. split.
      econstructor. econstructor. eassumption.
      right. split; reflexivity.
      congruence.
  Qed.


  Lemma inline_letapp_eval_r e x C x' v (cin : fuel) (cout : trace) rho :
    bstep_fuel cenv rho e cin (Res v) cout ->
    inline_letapp e x = Some (C, x') ->
    exists rho' cin' cout',
      interpret_ctx_fuel cenv C rho cin' (Res rho') cout' /\
      M.get x' rho' = Some v  /\
      ((cin = cin' /\ cout = cout') \/ (cin = plus cin' (one (Ehalt 1%positive)) /\ cout = plus cout' (one (Ehalt 1%positive)))).
  Proof.
    revert x C x' v cin cout rho.
    induction e using exp_ind'; simpl; intros z C z' v1 cin cout rho Hstep Hin;
      try (match goal with
           | [ _ : context[inline_letapp ?E ?X] |- _ ] =>
             destruct (inline_letapp E X) as [[C' w] | ] eqn:Hin'; inv Hin
           end); (try now inv Hin);
        (try now inv Hstep; inv H;
         match goal with
         | [ H : bstep_fuel _ _ _ _ _ _ |- _ ] => eapply IHe in H; eauto; destructAll
         end;
         do 3 eexists; split; [| split ];
         [ econstructor; [ congruence | econstructor; eauto ] | congruence
           | inv H1;
             [ destructAll; left; now split; eauto | destructAll; right; rewrite !plus_assoc; split; rewrite (plus_comm (one _ )); eauto ]]).
    - inv Hin. inv Hstep. inv H.
      do 3 eexists.
      split; [| split ].
      + econstructor. congruence.
        econstructor; eauto. econstructor.
      + rewrite M.gss. reflexivity.
      + left. rewrite !plus_assoc. rewrite !plus_zero. simpl. split; reflexivity.
    - inv Hstep. inv H.
    - inv Hstep. inv H.
    - inv Hstep. inv H. inv Hin. do 3 eexists. split. econstructor.
      split. eassumption. right. split; reflexivity.
  Qed.


  Lemma inline_letapp_preord_env_P_inj k S e1 e2 x y x' y' C1 C2 sig rho1 rho2 rho1' rho2' (cin1 cin2 : fuel) (cout1 cout2 : trace) :
    (forall k, preord_exp cenv P1 PG k (e1, rho1) (e2, rho2)) ->

    inline_letapp e1 x = Some (C1, x') ->
    inline_letapp e2 y = Some (C2, y') ->

    interpret_ctx_fuel cenv C1 rho1 cin1 (Res rho1') cout1 ->
    interpret_ctx_fuel cenv C2 rho2 cin2 (Res rho2') cout2 ->

    preord_env_P_inj cenv PG S k sig rho1 rho2 ->

    Disjoint _ (image sig S) (bound_stem_ctx C2) ->

    preord_env_P_inj cenv PG (x' |: (S \\ bound_stem_ctx C1)) k (sig {x' ~> y'}) rho1' rho2'.
  Proof.
    intros Hexp Hinl1 Hinl2 Hi1 Hi2 Henv Hdis z Hin v Hget. destruct (peq z x'); subst.
    - rewrite extend_gss.
      edestruct inline_letapp_eval_l with (C := C1); eauto. destructAll.
      eapply (Hexp (k + to_nat x0)) in H; [| lia ]. destructAll.
      destruct x2; eauto. now inv H0.
      edestruct inline_letapp_eval_r with (C := C2); eauto. destructAll.
      eapply interpret_ctx_fuel_deterministic in H3; [| clear H3; eauto ]. destructAll.
      eexists. split. eassumption. simpl in H2. eapply preord_val_monotonic. eassumption. lia.
    - inv Hin. inv H. contradiction. inv H.
      erewrite <- interpret_ctx_fuel_env_eq_P in Hget; [| eassumption | | ].
      2:{ eapply Disjoint_Singleton_r. eassumption. }
      2:{ reflexivity. }
      rewrite extend_gso; eauto. eapply Henv in Hget; eauto. destructAll.
      erewrite interpret_ctx_fuel_env_eq_P in H; [| eassumption | | ].
      2:{ eapply Disjoint_sym. eassumption. }
      2:{ eapply In_image. eassumption. }
      eexists. split; eauto.
  Qed.

  Lemma interpret_ctx_bound C rho (cin : fuel) (cout : trace) rho' x :
    interpret_ctx_fuel cenv C rho cin (Res rho') cout ->
    x \in bound_stem_ctx C ->
    exists v, M.get x rho' = Some v.
  Proof.
    revert rho cin cout rho' x. induction C; intros rho cin cout rho' x Hint Hin; inv Hint; try inv H0.
    - inv Hin.
    - destruct (bound_stem_ctx_dec C) as [Dec]; destruct (Dec x).
      + eapply IHC; eassumption.
      + inv Hin; [| contradiction ]. erewrite <- interpret_ctx_fuel_env_eq_P; eauto.
        eexists. rewrite M.gss. reflexivity.
        eapply Disjoint_Singleton_r. eassumption. reflexivity.
    - destruct (bound_stem_ctx_dec C) as [Dec]; destruct (Dec x).
      + eapply IHC; eassumption.
      + inv Hin; [| contradiction ]. erewrite <- interpret_ctx_fuel_env_eq_P; eauto.
        eexists. rewrite M.gss. reflexivity.
        eapply Disjoint_Singleton_r. eassumption. reflexivity.
    - destruct (bound_stem_ctx_dec C) as [Dec]; destruct (Dec x).
      + eapply IHC; eassumption.
      + inv Hin; [| contradiction ]. erewrite <- interpret_ctx_fuel_env_eq_P; eauto.
        eexists. rewrite M.gss. reflexivity.
        eapply Disjoint_Singleton_r. eassumption. reflexivity.
    - destruct (bound_stem_ctx_dec C) as [Dec]; destruct (Dec x).
      + eapply IHC; eassumption.
      + inv Hin; [| contradiction ]. erewrite <- interpret_ctx_fuel_env_eq_P; [| eassumption | | ].
        eexists. rewrite def_funs_eq. reflexivity. eassumption.
        eapply Disjoint_Singleton_r. eassumption. reflexivity.
  Qed.

  Lemma inline_letapp_get C e x x' rho rho' (cin : fuel) (cout : trace) :
    closed_exp e ->
    inline_letapp e x = Some (C, x') ->
    interpret_ctx_fuel cenv C rho cin (Res rho') cout ->
    exists v, M.get x' rho' = Some v.
  Proof.
    intros Hc Hinl Hin. edestruct inline_letapp_var_eq_alt. eassumption.
    - inv H. eapply interpret_ctx_bound; eassumption.
    - inv H. eapply interpret_ctx_bound; eassumption.
      eapply Hc in H0; inv H0.
  Qed.


  Lemma inline_letapp_eval_OOT_l C e x x' rho (cin : fuel) (cout : trace) :
    inline_letapp e x = Some (C, x') ->
    interpret_ctx_fuel cenv C rho cin OOT cout ->
    bstep_fuel cenv rho e cin OOT cout.
  Proof.
    revert C x x' rho cin cout.
    induction e using exp_ind'; simpl; intros C z z' rho cin cout Hin Hinp;
      try (match goal with
           | [ _ : context[inline_letapp ?E ?X] |- _ ] =>
             destruct (inline_letapp E X) as [[C' w] | ] eqn:Hin'; inv Hin
           end); (try now inv Hin).
    - inv Hinp. constructor 1. eassumption.
      inv H0. eapply IHe in H10; eauto. destructAll.
      econstructor 2. econstructor; eauto.
    - inv Hinp. constructor 1; eassumption.
      inv H0. eapply IHe in H12; eauto. destructAll.
      econstructor 2. simpl. econstructor; eauto.
    - inv Hinp. constructor 1; eassumption.
      inv H0.
      + econstructor 2. econstructor; eauto.
      + econstructor 2. eapply BStept_letapp_oot; eauto.
    - inv Hinp. constructor 1. eassumption.
      inv H0. eapply IHe in H7; eauto. destructAll.
      econstructor 2. econstructor; eauto.
    - inv Hin. inv Hinp. constructor 1. eassumption.
      inv H0.
      + econstructor 2. inv H15. congruence. inv H1.
      + econstructor 2. econstructor; eauto.
    - inv Hinp. econstructor 1. eassumption.
      inv H0.
    - inv Hinp. econstructor 1. eassumption. inv H0.
    - inv Hin. inv Hinp. congruence. inv H0.
  Qed.

  Lemma lt_exists n m1 m2 :
    n < m1 + m2 ->
    m1 <= n ->
    exists m2', n = m1 + m2' /\ m2' < m2.
  Proof.
    revert m1 m2. induction n; intros.
    - assert (m1 = 0) by lia. subst. destruct m2. lia.
      eexists. split; eauto.
    - destruct m1.
      + destruct m2. lia.
        eexists. split. reflexivity. lia.
      + edestruct IHn with (m1 := m1) (m2 := m2). lia. lia.
        destructAll. eexists x. split. lia. eassumption.
  Qed.

  Lemma inline_letapp_Ehole e z z' :
    inline_letapp e z = Some (Hole_c, z') ->
    e = Ehalt z'.
  Proof.
    intros Hin.
    destruct e; simpl in Hin;
      try (match goal with
           | [ _ : context[inline_letapp ?E ?X] |- _ ] =>
             destruct (inline_letapp E X) as [[C' w] | ] eqn:Hin'; inv Hin
           end); (try now inv Hin).
  Qed.

  Lemma inline_letapp_eval_OOT_r e x C x' (cin : fuel) (cout : trace) rho :
    bstep_fuel cenv rho e cin OOT cout ->
    inline_letapp e x = Some (C, x') ->
    (exists cin' cout' r, interpret_ctx_fuel cenv C rho cin' r cout' /\
                          ((cin' = cin /\ cout' = cout) \/ cin' = plus cin (one (Ehalt 1%positive)) /\ cout' = plus cout (one (Ehalt 1%positive)))).
  Proof.
    revert x C x' cin cout rho.
    induction e using exp_ind'; simpl; intros z C z' cin cout rho Hstep Hin;
      try (match goal with
           | [ _ : context[inline_letapp ?E ?X] |- _ ] =>
             destruct (inline_letapp E X) as [[C' u] | ] eqn:Hin'; inv Hin
           end); (try now inv Hin);
        (try now inv Hstep;
         [ do 3 eexists; split; [ econstructor; [ eassumption | congruence ] | now eauto ] | ];
         inv H;
         match goal with
         | [ H : bstep_fuel _ _ _ _ _ _ |- _ ] => eapply IHe in H; eauto; destructAll
         end;
         do 3 eexists; split; [ econstructor 3; [ congruence |  econstructor; eauto ] | ];
         inv H0; destructAll; [ now eauto | right; split; do 2 rewrite plus_assoc; rewrite (plus_comm (one _ )); reflexivity ]).
    - inv Hstep.
      + do 3 eexists; split. econstructor. eassumption. congruence. eauto.
      + inv H.
        * eapply IHe in H14; [| eassumption ]. destructAll.
          do 3 eexists. split. econstructor 3. congruence. econstructor; eauto.
          inv H0; eauto.
          destructAll. left. eauto.
          destructAll.
          right. split; rewrite !plus_assoc; rewrite (plus_comm (one _)); reflexivity.
        * do 3 eexists. split. econstructor 3. congruence. eapply Eletapp_c_i_OOT; eauto.
          now eauto.
    - inv Hin. inv Hstep.
      + do 3 eexists; split. econstructor. eassumption.
        congruence. eauto.
      + inv H.
        do 3 eexists. split. econstructor 3. congruence. eapply Eletapp_c_i_OOT; eauto.
        eauto.
    - inv Hstep.
      + do 3 eexists; split. econstructor. eassumption. congruence. eauto.
      + inv H.
    - inv Hstep.
      + do 3 eexists; split. econstructor. eassumption. congruence. eauto.
      + inv H.
    - inv Hin. inv Hstep.
      + do 3 eexists; split. eapply ctx_hole. eauto. eapply lt_one in H. subst. eauto.
      + inv H.
  Qed.

  Definition post_inline :=
    forall e1 e2 e e' C1 C2 x x' y y' z z' rho1 rho2 rho1' rho2'
           (cin1 cin2 cin3 cin4 cin1' cin3' : fuel)
           (cout1 cout2 cout3 cout4 cout1' cout3' : trace),
      inline_letapp e1 x = Some (C1, x') ->
      inline_letapp e2 y = Some (C2, y') ->

      interpret_ctx_fuel cenv C1 rho1 cin1' (Res rho1') cout1' ->
      interpret_ctx_fuel cenv C2 rho2 cin3' (Res rho2') cout3' ->
      cin1 = cin1' /\ cout1 = cout1' \/ cin1 = plus cin1' (one (Ehalt z)) /\ cout1 = plus cout1' (one (Ehalt z)) ->
      cin3 = cin3' /\ cout3 = cout3' \/ cin3 = plus cin3' (one (Ehalt z')) /\ cout3 = plus cout3' (one (Ehalt z')) ->

      P1 (e1, rho1, cin1, cout1) (e2, rho2, cin3, cout3) ->
      P2 (e, rho1', cin2, cout2) (e', rho2', cin4, cout4) ->
      P3 (C1 |[ e ]|, rho1, cin1' <+> cin2, cout1' <+> cout2) (C2 |[ e' ]|, rho2, cin3' <+> cin4, cout3' <+> cout4).

  Definition post_inline_OOT :=
    forall e1 e2  C1 C2 x x' y y' z (cin1 cin3 cin3' : fuel) (cout1 cout3 cout3' : trace) e e' rho1 rho2,
      inline_letapp e1 x = Some (C1, x') ->
      inline_letapp e2 y = Some (C2, y') ->

      cin3' = cin3 /\  cout3' = cout3  \/ cin3' = plus cin3 (one (Ehalt z)) /\ cout3' = plus cout3 (one (Ehalt z)) ->

      P1 (e1, rho1, cin1, cout1) (e2, rho2, cin3, cout3) ->

      P3 (C1 |[ e ]|, rho1, cin1, cout1) (C2 |[ e' ]|, rho2, cin3', cout3').

  Context (Hposti : post_inline) (Hposti_OOT : post_inline_OOT).


  Lemma inline_letapp_compat k e1 e2 x y x' y' C1 C2 e e' sig rho1 rho2 :
    (forall k rho1 rho2,
        preord_exp cenv P1 PG k (e1, rho1) (e2, rho2)) ->
    closed_exp e1 ->
    (* closed_exp e2 -> *)

    inline_letapp e1 x = Some (C1, x') ->
    inline_letapp e2 y = Some (C2, y') ->

    (forall m rho1 rho2,
        m <= k ->
        preord_env_P_inj cenv PG [set x'] m (sig {x' ~> y'}) rho1 rho2 ->
        preord_exp cenv P2 PG m (e, rho1) (e', rho2)) ->

    preord_exp cenv P3 PG k (C1 |[ e ]|, rho1) (C2 |[ e' ]|, rho2).
  Proof.
    intros Hexp Hc1  (* Hc2 *) Hinl1 Hinl2 Hrel v cin cout Hleq Hstep.
    destruct v.
    - edestruct bstep_fuel_ctx_OOT. eassumption. eapply interprable_inline_letapp. eassumption.
      + eassert (H' := H). eapply inline_letapp_eval_OOT_l in H'; [| eassumption ].
        edestruct (Hexp (k + to_nat cin)); [| eassumption | ]. lia. destructAll.
        destruct x0; [| contradiction ].
        eapply inline_letapp_eval_OOT_r in H0; [| eassumption ]. destructAll.
        destruct x4.
        * do 3 eexists. split; [| split ].
          eapply interpret_ctx_OOT_bstep; eassumption. eapply Hposti_OOT; eassumption.
          eauto.
        * do 3 eexists. split; [| split ].
          -- eapply interpret_ctx_bstep_r. eassumption. econstructor 1. eapply zero_one_lt.
          -- rewrite !(plus_comm _ <0>). rewrite !plus_zero. eapply Hposti_OOT; eauto.
          -- eauto.
      + assert (Hstep' := Hstep). destructAll.
        edestruct inline_letapp_get with (C := C1) (e := e1). eassumption. eassumption. eassumption.
        edestruct inline_letapp_eval_l with (C := C1). eassumption. eassumption. eassumption.
        destructAll. rewrite to_nat_add in *.
        edestruct (Hexp (k + to_nat x6)); [| eassumption | ].
        lia. destructAll.
        destruct x8. contradiction.
        edestruct inline_letapp_eval_r with (C := C2). eassumption. eassumption.
        destructAll.

        edestruct Hrel with (m := k); [ lia | | | eassumption | ]; [| lia |].

        intros z Hin v1 Hget. inv Hin. eexists. rewrite extend_gss. split. eassumption.
        repeat subst_exp.
        simpl in H7. eapply preord_val_monotonic. eassumption. lia. destructAll.
        do 3 eexists. split; [| split ].
        * eapply interpret_ctx_bstep_r. eassumption. eassumption.
        * eapply Hposti; eassumption.
        * eapply preord_res_monotonic. eassumption. lia.
    - assert (Hstep' := Hstep). eapply interpret_ctx_bstep_l in Hstep'. destructAll.
      2:{ eapply interprable_inline_letapp. eassumption. }
      edestruct inline_letapp_get with (C := C1) (e := e1). eassumption. eassumption. eassumption.
      edestruct inline_letapp_eval_l with (C := C1); try eassumption.
      destructAll.
      edestruct (Hexp (k + to_nat x6)); [| eassumption | ]. lia. destructAll.
      destruct x8. contradiction.
      edestruct inline_letapp_eval_r with (C := C2). eassumption. eassumption.
      destructAll.

      rewrite to_nat_add in Hleq.
      edestruct Hrel with (m := k); [ lia | | | eassumption | ].

      intros z Hin v1 Hget. inv Hin. eexists. rewrite extend_gss. split. eassumption.
      repeat subst_exp.
      simpl in H7. eapply preord_val_monotonic. eassumption. lia. lia.
      destructAll.

      do 3 eexists. split; [| split ].
      + eapply interpret_ctx_bstep_r. eassumption. eassumption.
      + eapply Hposti; eassumption.
      + eapply preord_res_monotonic. eassumption. rewrite to_nat_add. lia.
  Qed.


  Definition cc_approx_env_P_inj (S : Ensemble var) k P f rho1 rho2 :=
    forall x : var, S x -> cc_approx_var_env (fuel := fuel) (trace := trace) cenv ctag k P rho1 rho2 x (f x).

  Lemma inline_letapp_compat_cc k e1 e2 x y x' y' C1 C2 e e' sig rho1 rho2 :
    (forall k rho1 rho2,
        cc_approx_exp cenv ctag k P1 PG (e1, rho1) (e2, rho2)) ->
    closed_exp e1 ->

    inline_letapp e1 x = Some (C1, x') ->
    inline_letapp e2 y = Some (C2, y') ->

    (forall m rho1 rho2,
        m <= k ->
        cc_approx_env_P_inj [set x'] m PG (sig {x' ~> y'}) rho1 rho2 ->
        cc_approx_exp cenv ctag m P2 PG (e, rho1) (e', rho2)) ->

     cc_approx_exp cenv ctag k P3 PG (C1 |[ e ]|, rho1) (C2 |[ e' ]|, rho2).
  Proof.
    intros Hexp Hc1 Hinl1 Hinl2 Hrel v cin cout Hleq Hstep.
    destruct v.
    - edestruct bstep_fuel_ctx_OOT. eassumption. eapply interprable_inline_letapp. eassumption.
      + eassert (H' := H). eapply inline_letapp_eval_OOT_l in H'; [| eassumption ].
        edestruct (Hexp (k + to_nat cin)); [| eassumption | ]. lia.
        destructAll. destruct x0; [| contradiction ].
        eapply inline_letapp_eval_OOT_r in H0; [| eassumption ]. destructAll.
        destruct x4.
        -- do 3 eexists. split; [| split ].
           eapply interpret_ctx_OOT_bstep. eassumption. eapply Hposti_OOT; eauto.
           eauto.
        -- do 3 eexists. split; [| split ].
           --- eapply interpret_ctx_bstep_r. eassumption. econstructor 1. eapply zero_one_lt.
           --- rewrite !(plus_comm _ <0>). rewrite !plus_zero. eapply Hposti_OOT; eassumption.
           --- eauto.
      + assert (Hstep' := Hstep). destructAll.
        edestruct inline_letapp_get with (C := C1) (e := e1). eassumption. eassumption. eassumption.
        edestruct inline_letapp_eval_l with (C := C1). eassumption. eassumption. eassumption.
        destructAll.
        edestruct (Hexp (k + to_nat x6)); [ | eassumption | ]. lia.

        destructAll.
        destruct x8. contradiction.
        edestruct inline_letapp_eval_r with (C := C2). eassumption. eassumption.
        destructAll.
        rewrite to_nat_add in *.

        edestruct Hrel with (m := k); [ lia | | | eassumption | ]; [| lia | ].
        intros z Hin v1 Hget. inv Hin. eexists. rewrite extend_gss. split. eassumption.
        repeat subst_exp.
        simpl in H8. eapply cc_approx_val_monotonic. eassumption. lia.
        destructAll.
        do 3 eexists. split; [| split ].
        * eapply interpret_ctx_bstep_r. eassumption. eassumption.
        * eapply Hposti; eassumption.
        * eapply cc_approx_res_monotonic. eassumption. lia.
    - assert (Hstep' := Hstep). eapply interpret_ctx_bstep_l in Hstep'. destructAll.
      2:{ eapply interprable_inline_letapp. eassumption. }
      edestruct inline_letapp_get with (C := C1) (e := e1). eassumption. eassumption. eassumption.
      edestruct inline_letapp_eval_l with (C := C1); try eassumption.
      destructAll.
      edestruct (Hexp (k + to_nat x6)); [| eassumption | ]. lia.

      destructAll.
      destruct x8. contradiction.
      edestruct inline_letapp_eval_r with (C := C2). eassumption. eassumption.
      destructAll.

      edestruct Hrel with (m := k); [ lia | | | eassumption | ].

      intros z Hin v1 Hget. inv Hin. eexists. rewrite extend_gss. split. eassumption.
      repeat subst_exp.
      simpl in H7. eapply cc_approx_val_monotonic. eassumption. lia. rewrite to_nat_add in Hleq. lia.
      destructAll.
      do 3 eexists. split; [| split ].
      + eapply interpret_ctx_bstep_r. eassumption. eassumption.
      + eapply Hposti; eassumption.
      + eapply cc_approx_res_monotonic. eassumption.
        rewrite to_nat_add. lia.
  Qed.

End Inline_correct.
