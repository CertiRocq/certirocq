(* Computational definition and declarative spec for function hoisting. Part of the CertiRocq project.
 * Author: Anonymized, 2016
 *)

Require Import Common.AstCommon Common.compM.
Require Import LambdaANF.term LambdaANF.term_util LambdaANF.identifiers LambdaANF.eval LambdaANF.env LambdaANF.ctx LambdaANF.size_cps
        LambdaANF.logical_relations LambdaANF.Ensembles_util LambdaANF.List_util LambdaANF.map_util LambdaANF.tactics
        LambdaANF.algebra LambdaANF.closure_conversion LambdaANF.closure_conversion_util LambdaANF.state.
Require Import compcert.lib.Coqlib.
From Stdlib Require Import Lists.List NArith.BinNat Relations.Relations
        micromega.Lia Sets.Ensembles Classes.Morphisms.

Import ListNotations.

Close Scope Z_scope.

(** Given an expression [e], [exp_hoist e B f] will return an expression [e']
  * and a block of function definitions [B']. [e'] is the function definition
  * erasure of [e] and [B] is exactly the function definitions of [e]. It's
  * written in a CPS fashion and [f] is the continuation. [B] is an accumulator
  * of function definitions.
  *)
Fixpoint erase_fundefs (e : exp) (defs : fundefs)
         (f : exp * fundefs * nat -> exp * fundefs * nat) {struct e} : exp * fundefs * nat :=
  match e with
    | Econstr x  tag ys e' =>
      erase_fundefs e' defs (fun p => let '(e, defs, n) := p in
                                      f (Econstr x tag ys e, defs, n))
    | Ecase x tes =>
      fold_left
        (fun (f : exp * fundefs * nat -> exp * fundefs * nat) (te : ctor_tag * exp) =>
           fun p =>
             let (c, e) := te in
             let '(e1, defs1, n1) := p in
             erase_fundefs e defs1
                       (fun p2 =>
                          let '(e2, defs2, n2) := p2 in
                          match e1 with
                          | Ecase x' tes' =>
                            f (Ecase x' ((c, e2) :: tes'), defs2, max n1 n2)
                          | _ => (* This should never match *)
                            f (Ecase x [(c, e2)], defs2, max n1 n2)
                          end)) tes f (Ecase x [], defs, 0)
    | Eproj x tag n y e' =>
      erase_fundefs e' defs (fun p =>
                               let '(e, defs, m) := p in
                               f (Eproj x tag n y e, defs, m))
    | Eletapp x g ft ys e' =>
      erase_fundefs e' defs (fun p =>
                               let '(e, defs, n) := p in
                               f (Eletapp x g ft ys e, defs, n))

    | Efun fdefs e' =>
      erase_fundefs e' defs (fun p =>
                               let '(e'', defs'', n) := p in
                               erase_nested_fundefs fdefs e'' defs'' (fun p => let '(e, defs, m) := p in f (e, defs, 1 + max n m)))
    | Eapp g ft xs =>
      f (Eapp g ft xs, defs, 0)
    | Eprim_val x pv e' =>
      erase_fundefs e' defs (fun p =>
                               let '(e', defs', n) := p in
                               f (Eprim_val x pv e', defs', n))
    | Eprim x prim ys e' =>
      erase_fundefs e' defs (fun p =>
                               let '(e', defs', n) := p in
                               f (Eprim x prim ys e', defs', n))
    | Ehalt x => f (Ehalt x, defs, 0)
  end
with erase_nested_fundefs (defs : fundefs) (e : exp) (hdefs : fundefs)
                          (f : exp * fundefs * nat -> exp * fundefs * nat) {struct defs}
     : exp * fundefs * nat :=
       match defs with
         | Fcons g t xs e' defs =>
           erase_nested_fundefs defs e hdefs
                                (fun p1 =>
                                   let '(e1, defs1, n1) := p1 in
                                   erase_fundefs e' defs1
                                                 (fun p2 =>
                                                    let '(e2, defs2, n2) := p2 in
                                                    f (e1, Fcons g t xs e2 defs2, max n1 n2)))
         | Fnil => f (e, hdefs, 0)
  end.

(** [exp_hoist e] moves all function definitions of [e] at the outermost level *)
Definition exp_hoist (e : exp) :=
  let '(e, defs, n) := erase_fundefs e Fnil id in
  match defs with
  | Fnil => (e, n)
    | _ => (Efun defs e, n)
  end.


Section CC.
  Context (clo_tag : ctor_tag). (* Tag for closure records *)
  Context (clo_itag : ind_tag). (* Inductive tag for closure records *)

  Definition closure_conversion_hoist (e : exp) (c: comp_data) : error exp * comp_data :=
    let '(e'_err, c') := closure_conversion_top clo_tag clo_itag e c in
    match e'_err with
    | Ret e' => (Ret (fst (exp_hoist e')), c')
    | Err str => (Err str, c')
    end.

End CC.

(** [erase_fundefs e e' B] iff [e'] is [e] after erasing all the function
  *  definition blocks and [B] is exactly the function definitions of [e]
  *)
Inductive Erase_fundefs : exp -> exp -> fundefs -> nat (* number of hoisting steps *) -> Prop :=
| Efun_erase :
    forall e e' defs Be Bdefs Be_defs n m,
      Erase_fundefs e e' Be n ->
      Erase_nested_fundefs defs Bdefs m ->
      split_fds Be Bdefs Be_defs ->
      Erase_fundefs (Efun defs e) e' Be_defs (1 + max n m)
| Econstr_erase :
    forall x t ys e e' B n,
      Erase_fundefs e e' B n ->
      Erase_fundefs (Econstr x t ys e)
                  (Econstr x  t ys e') B n
| Ecase_nil_erase :
    forall x,
      Erase_fundefs (Ecase x nil) (Ecase x nil) Fnil 0
| Ecase_cons_erase :
    forall x c e e' tes tes' B B' B'' n m,
      Erase_fundefs (Ecase x tes) (Ecase x tes') B n ->
      Erase_fundefs e e' B' m ->
      split_fds B B' B'' ->
      Erase_fundefs (Ecase x ((c, e) :: tes)) (Ecase x ((c, e') :: tes')) B'' (max n m)
| Eproj_erase :
    forall x tau N y e e' B n,
      Erase_fundefs e e' B n ->
      Erase_fundefs (Eproj x tau N y e)
                    (Eproj x tau N y e') B n
| Eletapp_erase :
    forall x f tau ys e e' B n,
      Erase_fundefs e e' B n ->
      Erase_fundefs (Eletapp x f tau ys e)
                    (Eletapp x f tau ys e') B n
| Eapp_erase :
    forall f ft xs,
      Erase_fundefs (Eapp f ft xs) (Eapp f ft xs) Fnil 0
| Eprim_val_erase n :
    forall x p e e' B,
      Erase_fundefs e e' B n ->
      Erase_fundefs (Eprim_val x p e)
                    (Eprim_val x p e') B n
| Eprim_erase n :
    forall x f ys e e' B,
      Erase_fundefs e e' B n ->
      Erase_fundefs (Eprim x f ys e)
                    (Eprim x f ys e') B n
| Ehalt_erase :
    forall x, Erase_fundefs (Ehalt x) (Ehalt x) Fnil 0
with Erase_nested_fundefs : fundefs -> fundefs -> nat -> Prop :=
| Fcons_erase :
    forall f tau xs e e' defs B B' B'' n m,
      Erase_fundefs e e' B n ->
      Erase_nested_fundefs defs B' m ->
      split_fds B (Fcons f tau xs e' B') B'' ->
      Erase_nested_fundefs (Fcons f tau xs e defs) B'' (max n m)
| Fnil_erase :
    Erase_nested_fundefs Fnil Fnil 0.

(** Correspondence between the inductive and the computational definitions of function definition erasure *)
Lemma erase_fundefs_in_Erase_fundefs :
  (forall e B f,
   exists e' B' B'' m,
     erase_fundefs e B f = f (e', B', m) /\
     split_fds B B'' B' /\
     Erase_fundefs e e' B'' m) /\
  (forall defs e B f,
    exists B' B'' m,
      erase_nested_fundefs defs e B f = f (e, B', m) /\
      split_fds B B'' B' /\
      Erase_nested_fundefs defs B'' m).
Proof.
  exp_defs_induction IHe IHl IHf; intros; simpl in *;
  try (now edestruct IHe as [e' [B' [B'' [m [Heq [Hsplit Her]]]]]];
       repeat eexists; eauto; try rewrite Heq; try constructor; eauto).
  - repeat eexists; eauto using split_fds_nil_l; repeat econstructor.
  - edestruct IHl as [e1' [B1' [B1'' [m [Heq1 [Hspl1 Her1]]]]]].
    edestruct IHe as [e2' [B2' [B2'' [n [Heq2 [Hspl2 Her2]]]]]].
    rewrite Heq1, Heq2. clear Heq1 Heq2.
    edestruct split_fds_trans as [B3 [H1 H2]]; [apply Hspl1 | |]; eauto.
    inv Her1; repeat eexists; eauto; econstructor; eauto; econstructor; eauto.
  - edestruct IHe as [e2 [B2 [B2' [m [Heq2 [Hspl2 Her2]]]]]].
    edestruct IHf as [B1 [B1' [n [Heq1 [Hspl1 Her1]]]]]; subst.
    edestruct split_fds_trans as [B3 [H1 H2]] ; [ | apply Hspl1 |]; eauto.
    repeat eexists. rewrite Heq2, Heq1; eauto. eauto.
    econstructor; eauto.
  - repeat eexists; eauto using split_fds_nil_l; repeat econstructor.
  - repeat eexists; eauto using split_fds_nil_l; repeat econstructor.
  - edestruct IHf as [B1 [B1' [m [Heq1 [Hspl1 Her1]]]]]; subst.
    edestruct IHe as [e2 [B2 [B2' [n [Heq2 [Hspl2 Her2]]]]]].
    edestruct split_fds_trans as [B3 [H1 H2]] ; [ apply Hspl1 | |]; eauto.
    repeat eexists. rewrite Heq1, Heq2; eauto.
    constructor. eassumption.
    rewrite Nat.max_comm. econstructor; eauto. econstructor; eauto.
    apply split_fds_sym; eauto.
  - repeat eexists; eauto using split_fds_nil_l; repeat econstructor.
Qed.


(** Expressions without function definitions *)
Inductive no_fun : exp -> Prop  :=
| Econstr_no_fun :
    forall x t xs e,
      no_fun e ->
      no_fun (Econstr x t xs e)
| Ecase_nil_no_fun :
    forall x, no_fun (Ecase x [])
| Ecase_no_fun :
    forall x c e tes,
      no_fun (Ecase x tes) ->
      no_fun e ->
      no_fun (Ecase x ((c, e) :: tes))
| Eproj_no_fun :
    forall x tau n y e,
      no_fun e ->
      no_fun (Eproj x tau n y e)
| Eletapp_no_fun :
    forall x f tau ys e,
      no_fun e ->
      no_fun (Eletapp x f tau ys e)
| Eapp_no_fun :
    forall x ft ys, no_fun (Eapp x ft ys)
| Eprim_val_no_fun :
    forall x p e,
      no_fun e ->
      no_fun (Eprim_val x p e)
| Eprim_no_fun :
    forall x p xs e,
      no_fun e ->
      no_fun (Eprim x p xs e)
| Ehalt_no_fun :
    forall x, no_fun (Ehalt x).

(** Function definitions without nested function definitions *)
Inductive no_fun_defs : fundefs -> Prop  :=
| Fcons_no_fun :
    forall f tau xs e B,
      no_fun e ->
      no_fun_defs B ->
      no_fun_defs (Fcons f tau xs e B)
| Fnil_no_fun :
    no_fun_defs Fnil.

#[global] Hint Constructors no_fun no_fun_defs : core.

Lemma no_fun_split_fds B B' B'' :
  no_fun_defs B -> no_fun_defs B' ->
  split_fds B B' B'' ->
  no_fun_defs B''.
Proof.
  intros Hnf Hnf' Hsp. induction Hsp; eauto.
  - inv Hnf; constructor; eauto.
  - inv Hnf'; constructor; eauto.
Qed.


(** If [Erase_fundefs e e' B] then there are no function definitions
    in [e'] and [B] *)
Lemma erase_fundefs_no_fun :
  (forall e e' B m,
     Erase_fundefs e e' B m ->
     no_fun e' /\ no_fun_defs B) /\
  (forall B B' m,
     Erase_nested_fundefs B B' m ->
     no_fun_defs B').
Proof.
  exp_defs_induction IHe IHl IHf; intros; simpl;
  try (now inv H; edestruct IHe; eauto);
  try (now inv H; split; eauto).
  - inv H. edestruct IHe; eauto.
    edestruct IHl; eauto.
    econstructor. eauto. eapply no_fun_split_fds; [ | | eauto]; eauto.
  - inv H. edestruct IHe; eauto. split. eauto.
    eapply no_fun_split_fds; [ | | eauto]; eauto.
  - inv H. edestruct IHe; eauto.
    eapply no_fun_split_fds; [ | | eauto]; eauto.
  - inv H; eauto.
Qed.

Definition funs_inv_env B rho :=
  exists rho0,
  forall f,
    f \in name_in_fundefs B ->
    M.get f rho = Some (Vfun rho0 B f).


Lemma funs_inv_env_set B rho x v :
  funs_inv_env B rho ->
  ~ x \in name_in_fundefs B ->
          funs_inv_env B (M.set x v rho).
Proof.
  intros [rhoi Hin] Hnin. eexists. intros f Hfun.
  rewrite M.gso; eauto.
  intros Hc; subst; eauto.
Qed.


Lemma Erase_fundefs_bound_var_mut :
  (forall e e' B m (Herase : Erase_fundefs e e' B m),
      bound_var e <--> bound_var e' :|: bound_var_fundefs B) /\
  (forall B B' m (Herase : Erase_nested_fundefs B B' m),
      bound_var_fundefs B <--> bound_var_fundefs B').
Proof.
  exp_defs_induction IHe IHc IHB;
    try (intros e' B m Hr); try (intros B' m Hr); inv Hr;
      try (now repeat normalize_bound_var; rewrite IHe; [| eassumption ];
           split; xsets).
  - repeat normalize_bound_var. sets.
  - repeat normalize_bound_var.
    rewrite IHe; [| eassumption ].
    rewrite IHc; [| eassumption ].
    erewrite (split_fds_bound_vars B0 B' B); eauto.
    split; xsets.
  - normalize_bound_var.
    rewrite IHe; [| eassumption ].
    rewrite IHB; [| eassumption ].
    erewrite (split_fds_bound_vars Be Bdefs B); eauto.
    sets.
  - repeat normalize_bound_var. sets.
  - repeat normalize_bound_var. sets.
  - erewrite (split_fds_bound_vars B (Fcons v t l e' B'0) B'); eauto.
    repeat normalize_bound_var.
    rewrite IHe; [| eassumption ].
    rewrite IHB; [| eassumption ]. xsets.
  - normalize_bound_var. xsets.
Qed.


Lemma Erase_fundefs_bound_var :
  forall e e' B m (Herase : Erase_fundefs e e' B m),
    bound_var e <--> bound_var e' :|: bound_var_fundefs B.
Proof.
  eapply Erase_fundefs_bound_var_mut.
Qed.

Lemma Erase_nested_fundefs_bound_var :
  forall B B' m (Herase : Erase_nested_fundefs B B' m),
    bound_var_fundefs B <--> bound_var_fundefs B'.
Proof.
  eapply Erase_fundefs_bound_var_mut.
Qed.

Ltac bound_var_heq Hname :=
  match goal with
  | [ H : Erase_fundefs _ _ _ _ |- _ ] =>
    assert (Hname := Erase_fundefs_bound_var _ _ _ _ H)
  end.

Ltac bound_var_fundefs_heq Hname :=
  match goal with
  | [ H : Erase_nested_fundefs _ _ _ |- _ ] =>
    assert (Hname := Erase_nested_fundefs_bound_var _ _ _ H)
  end.


Lemma Erase_fundefs_unique_bindings_mut :
  (forall e e' B m (Herase : Erase_fundefs e e' B m),
      unique_bindings e ->
      unique_bindings e' /\
      unique_bindings_fundefs B /\
      Disjoint _ (bound_var_fundefs B) (bound_var e')) /\
  (forall B B' m (Herase : Erase_nested_fundefs B B' m),
      unique_bindings_fundefs B ->
      unique_bindings_fundefs B').
Proof.
  exp_defs_induction IHe IHc IHB;
    try (intros e' B m Hr Hun); try (intros B' m Hr Hun); inv Hr;
      try (bound_var_heq Hbin); try (bound_var_fundefs_heq Hbin').
  - inv Hun.
    edestruct (IHe _ _ _ H6) as [Hun [Hunf Hdis]]; eauto.
    split; [| split ].
    + constructor; eauto.
      intros Hc. eapply H1. eapply Erase_fundefs_bound_var_mut.
      eassumption. now left.
    + eassumption.
    + normalize_bound_var.
      eapply Union_Disjoint_r.
      eassumption. eapply Disjoint_Singleton_r.
      intros Hc. eapply H1. eapply Hbin. now right.
  - repeat normalize_bound_var.
    split; [| split ].
    + sets.
    + constructor.
    + sets.
  - normalize_bound_var.
    inv Hun.
    edestruct (IHe _ _ _ H7) as [Hun' [Hunf' Hd']]; eauto.
    edestruct (IHc _ _ _ H6) as [Hun [Hunf Hd]]; eauto.
    clear H7. bound_var_heq Hbin'.
    split; [| split ].
    + constructor; eauto.
      eapply Disjoint_Included; [| | eapply H5 ].
      rewrite Hbin'. sets.
      rewrite Hbin. sets.
    + rewrite Hbin', Hbin in *.
      eapply split_fds_unique_bindings_fundefs_r;
        [| | | eassumption ]; eauto.
      eapply Disjoint_sym.
      eapply Disjoint_Included; [| | eapply H5 ]; sets.
    + rewrite (split_fds_bound_vars B0 B' B); eauto.
      rewrite Hbin, Hbin' in *.
      eapply Union_Disjoint_l; eapply Union_Disjoint_r.
      * eapply Disjoint_sym.
        eapply Disjoint_Included; [| | eapply H5 ]; sets.
      * eassumption.
      * eassumption.
      * eapply Disjoint_Included; [| | eapply H5 ]; sets.
  - inv Hun.
    edestruct (IHe _ _ _ H7) as [Hun [Hunf Hdis]]; eauto.
    split; [| split ].
    + constructor; eauto.
      intros Hc. eapply H1. eapply Erase_fundefs_bound_var_mut.
      eassumption. now left.
    + eassumption.
    + normalize_bound_var.
      eapply Union_Disjoint_r.
      eassumption. eapply Disjoint_Singleton_r.
      intros Hc. eapply H1. eapply Hbin. now right.
  - inv Hun.
    edestruct (IHe _ _ _ H7) as [Hun [Hunf Hdis]]; eauto.
    split; [| split ].
    + constructor; eauto.
      intros Hc. eapply H1. eapply Erase_fundefs_bound_var_mut.
      eassumption. now left.
    + eassumption.
    + normalize_bound_var.
      eapply Union_Disjoint_r.
      eassumption. eapply Disjoint_Singleton_r.
      intros Hc. eapply H1. eapply Hbin. now right.
  - inv Hun.
    edestruct (IHe _ _ _ H1) as [Hun [Hunf Hdis]]; eauto.
    assert (Hunf' := IHB _ _ H2 H4).
    split; [| split ]; eauto.
    + eapply split_fds_unique_bindings_fundefs_r;
        [ | | | eassumption ]; eauto.
      eapply Disjoint_Included; [| | eapply H5 ]; sets.
      rewrite Hbin'. sets.
      rewrite Hbin. sets.
    + erewrite (split_fds_bound_vars _ _ B); eauto.
      eapply Union_Disjoint_l.
      * eassumption.
      * rewrite <- Hbin'.
        eapply Disjoint_sym.
        eapply Disjoint_Included; [| | eapply H5 ]; sets.
        rewrite Hbin; sets.
  - inv Hun.
    split; [| split ]; eauto.
    + constructor; eauto.
    + constructor.
    + normalize_bound_var. sets.
  - inv Hun.
    edestruct (IHe _ _ _ H5) as [Hun [Hunf Hdis]]; eauto.
    split; [| split ].
    + constructor; eauto.
      intros Hc. eapply H1. eapply Erase_fundefs_bound_var_mut.
      eassumption. now left.
    + eassumption.
    + normalize_bound_var.
      eapply Union_Disjoint_r.
      eassumption. eapply Disjoint_Singleton_r.
      intros Hc. eapply H1. eapply Hbin. now right.
  - inv Hun.
    edestruct (IHe _ _ _ H6) as [Hun [Hunf Hdis]]; eauto.
    split; [| split ].
    + constructor; eauto.
      intros Hc. eapply H1. eapply Erase_fundefs_bound_var_mut.
      eassumption. now left.
    + eassumption.
    + normalize_bound_var.
      eapply Union_Disjoint_r.
      eassumption. eapply Disjoint_Singleton_r.
      intros Hc. eapply H1. eapply Hbin. now right.
  - inv Hun.
    split; [| split ].
    + constructor; eauto.
    + constructor.
    + normalize_bound_var; sets.
  - inv Hun.
    eapply split_fds_unique_bindings_fundefs_r;
      [ | | | eassumption ]; eauto.
    * eapply IHe. eassumption. eassumption.
    * constructor; eauto.
      intros Hc; eapply H4.
      eapply Hbin. now left.
      intros Hc. eapply H5.
      eapply Hbin'. eassumption.
      eapply Disjoint_Included_l; [| eapply H9 ]; sets.
      rewrite Hbin. sets.
      eapply Disjoint_Included_l; [| eapply H10 ]; sets.
      rewrite Hbin'. sets.
      eapply Disjoint_Included; [| | eapply H11 ]; sets.
      rewrite Hbin'. sets.
      rewrite Hbin. sets.
      eapply IHe. eassumption. eassumption.
    * normalize_bound_var.
      repeat eapply Union_Disjoint_r.
      -- eapply Disjoint_Singleton_r.
         intros Hc; eapply H4.
         eapply Hbin. now right.
      -- eapply Disjoint_Included_l; [| eapply H9 ]; sets.
         rewrite Hbin. sets.
      -- eapply IHe. eassumption. eassumption.
      -- rewrite <- Hbin'.
         eapply Disjoint_Included; [| | eapply H11 ]; sets.
         rewrite Hbin. sets.
  - constructor.
Qed.

Lemma Erase_nested_fundefs_name_in_fundefs :
  (forall B B' m (Herase : Erase_nested_fundefs B B' m),
      name_in_fundefs B \subset name_in_fundefs B').
Proof.
  intros B B' m Hr. induction Hr; sets.
  rewrite (split_fds_name_in_fundefs _ _ _ H0).
  simpl. sets.
Qed.


Lemma Erase_fundefs_funnames_in_exp :
      (forall e e' B m (Herase : Erase_fundefs e e' B m),
          funnames_in_exp e \subset name_in_fundefs B) /\
      (forall B B' m (Herase : Erase_nested_fundefs B B' m),
          funnames_in_fundefs B \subset name_in_fundefs B').
Proof.
  exp_defs_induction IHe IHc IHB; intros; simpl; inv Herase;
    try now (intros z Hin; inv Hin; destructAll; inv H; eapply IHe; eauto;
             econstructor; split; eauto).
  - intros x Hin; inv Hin; destructAll. inv H. inv H5.
  - eapply IHc in H6. intros z Hin; inv Hin; destructAll. inv H. inv H5.
    + inv H. eapply IHe in H7. erewrite split_fds_name_in_fundefs; [| eassumption ].
      right; eauto. eapply H7. econstructor. split; eauto.
    + erewrite split_fds_name_in_fundefs; [| eassumption ]. left.
      eapply H6. econstructor. split; [| eassumption ].
      econstructor. eassumption. eassumption.
  - intros z Hin; inv Hin; destructAll. erewrite split_fds_name_in_fundefs; [| eassumption ]. inv H.
    + right. eapply Erase_nested_fundefs_name_in_fundefs. eassumption. eassumption.
    + left. eapply IHe. eassumption. econstructor. split; eauto.
    + right. eapply IHB. eassumption. econstructor. split; eauto.
  - intros z Hin; inv Hin; destructAll. erewrite split_fds_name_in_fundefs; [| eassumption ]. inv H.
    + left. eapply IHe. eassumption. econstructor. split; eauto.
    + right. simpl. right. eapply IHB. eassumption. econstructor. split; eauto.
Qed.


Lemma Erase_fundefs_fun_fv_in e e' B m
      (Herase : Erase_fundefs e e' B m)
      (Hsub : fun_fv_in e (funnames_in_exp e)) :
      fun_fv_in e (name_in_fundefs B).
Proof.
  intros B' Hin. eapply Hsub in Hin. eapply Included_trans.
  eassumption. eapply Erase_fundefs_funnames_in_exp. eassumption.
Qed.


Lemma Erase_fundefs_occurs_free :
  (forall e e' Ball B Bprev m
          (Herase : Erase_fundefs e e' B m)
          (Hsplit: split_fds Bprev B Ball)
          (Hfv : fun_fv_in e (name_in_fundefs Ball)),
      occurs_free e' \subset (name_in_fundefs Ball) :|: occurs_free e).
Proof.
  induction e using exp_ind'; intros; inv Herase;
  try (now repeat normalize_occurs_free;
       eapply Union_Included; [ now sets | ];
       eapply Included_trans;
       [ eapply Included_Setminus_compat; [ eapply IHe; eauto; intros B1 Hin1; eapply Hfv; eauto | reflexivity ]
       | rewrite Setminus_Union_distr; sets ]).
  - rewrite !occurs_free_Ecase_nil at 1. sets.
  - rewrite !occurs_free_Ecase_cons at 1.

    eapply Union_Included. now sets.
    eapply Union_Included.
    + edestruct split_fds_trans. eapply split_fds_sym.
      eapply H8. eapply split_fds_sym. eassumption. destructAll.
      eapply IHe in H7. 3:{ intros B1 Hin1. eapply Hfv; eauto. econstructor. eassumption. now left. }
      eapply Included_trans. eassumption. now sets.
      eapply split_fds_sym. eassumption.
    + edestruct split_fds_trans. eapply H8. eapply split_fds_sym. eassumption. destructAll.
      eapply IHe0 in H6.
      eapply Included_trans. eassumption. now sets.
      eapply split_fds_sym. eassumption.
      intros B1 Hin1. eapply Hfv; eauto. inv Hin1. econstructor. eassumption. right. eauto.
  - edestruct split_fds_trans. eapply H6. eapply split_fds_sym. eassumption. destructAll.
    eapply IHe in H1. 2:{ eapply split_fds_sym. eassumption. }
    2:{ intros B1 Hin1. eapply Hfv; eauto. }

    repeat normalize_occurs_free. rewrite Union_assoc.
    rewrite Union_Setminus_Included.
    eapply Included_trans. eassumption. now sets. tci.
    eapply Included_trans. eapply Erase_nested_fundefs_name_in_fundefs. eassumption.

    rewrite split_fds_name_in_fundefs with (B3 := Ball); eauto.
    rewrite split_fds_name_in_fundefs with (B3 := x); eauto. now sets.
  - sets.
  - repeat normalize_occurs_free.
    eapply Included_trans;
    [ eapply Included_Setminus_compat; [ eapply IHe; eauto; intros B1 Hin1; eapply Hfv; eauto | reflexivity ]
      | rewrite Setminus_Union_distr; sets ].
  - sets.
Qed.

Lemma Erase_fundefs_occurs_free_fundefs :
  (forall e e' Ball B Bprev m
          (Herase : Erase_fundefs e e' B m)
          (Hsplit: split_fds Bprev B Ball)
          (Hfv : fun_fv_in e (name_in_fundefs Ball)),
      occurs_free_fundefs B \subset name_in_fundefs Ball) /\
  (forall B B' Ball Bprev m
          (Herase : Erase_nested_fundefs B B' m)
          (Hsplit: split_fds Bprev B' Ball)
          (Hfv : fun_fv_in_fundefs B (name_in_fundefs Ball)),
      occurs_free_fundefs B' \subset name_in_fundefs Ball).
Proof.
  exp_defs_induction IHe IHl IHB; intros; inv Herase;
  try (now repeat normalize_occurs_free;
       eapply IHe; [ eassumption | eassumption | intros B1 Hin1; eapply Hfv; eauto ]).
  - repeat normalize_occurs_free. sets.
  - rewrite split_fds_occurs_free_fundefs; [| eassumption ].
    eapply Union_Included; eapply Setminus_Included_Included_Union.
    + edestruct split_fds_trans. eapply H8. eapply split_fds_sym. eassumption. destructAll.
      eapply Included_trans. eapply IHl. eassumption. eapply split_fds_sym. eassumption.
      intros B1 Hin1. eapply Hfv; eauto. inv Hin1. econstructor. eassumption. right. now eauto.
      now sets.
    + edestruct split_fds_trans. eapply split_fds_sym. eapply H8. eapply split_fds_sym. eassumption. destructAll.
      eapply Included_trans. eapply IHe. eassumption. eapply split_fds_sym. eassumption.
      intros B1 Hin1. eapply Hfv; eauto. econstructor. eassumption. now left.
      now sets.
  - rewrite split_fds_occurs_free_fundefs; [| eassumption ].
    eapply Union_Included; eapply Setminus_Included_Included_Union.
    + edestruct split_fds_trans. eapply H6. eapply split_fds_sym. eassumption. destructAll.
      eapply IHe in H1. 2:{ eapply split_fds_sym. eassumption. }
      2:{ intros B1 Hin1. eapply Hfv; eauto. }
      eapply Included_trans. eassumption. sets.
    + edestruct split_fds_trans. eapply split_fds_sym. eapply H6. eapply split_fds_sym. eassumption. destructAll.
      eapply Included_trans. eapply IHB. eassumption. eapply split_fds_sym. eassumption.
      { intros B1 Hin1. inv Hin1. eapply Hfv; eauto. eapply Hfv; eauto. }
      now sets.
  - normalize_occurs_free. sets.
  - normalize_occurs_free. sets.
  - rewrite split_fds_occurs_free_fundefs; [| eassumption ].
    eapply Union_Included; eapply Setminus_Included_Included_Union.
    + edestruct split_fds_trans. eapply H8. eapply split_fds_sym. eassumption. destructAll.
      eapply Included_trans. eapply IHe. eassumption. eapply split_fds_sym. eassumption.
      intros B1 Hin1. eapply Hfv; eauto. now sets.
    +  normalize_occurs_free. eapply Union_Included; eapply Setminus_Included_Included_Union.
      * edestruct split_fds_trans. eapply H8. eapply split_fds_sym. eassumption. destructAll.
        eapply Included_trans. eapply Erase_fundefs_occurs_free. eassumption.
        eapply split_fds_sym. eassumption. intros B1 Hin1. eapply Hfv; eauto.
        eapply Union_Included. now sets.
        eapply Included_trans. eapply occurs_free_in_fun with (B := Fcons v t l e f5).
        now left. simpl. rewrite !Union_assoc. eapply Union_Included.
        eapply Union_Included. now sets. eapply Included_trans.
        eapply Erase_nested_fundefs_name_in_fundefs. eassumption. now sets.
        eapply Included_trans. eapply Hfv. now left. now sets.
      * assert (Hs : split_fds B'0 (Fcons v t l e' Fnil) (Fcons v t l e' B'0)).
        constructor. eapply split_fds_nil_l.
        edestruct split_fds_trans with (B1 := B'0) (B3 := B').
        eassumption. eapply split_fds_sym. eassumption. destructAll.

        edestruct split_fds_trans with (B1 := B'0) (B3 := Ball).
        2:{ eapply split_fds_sym. eassumption. } eassumption. destructAll.
        eapply IHB in H7. 2:{ eapply split_fds_sym. eassumption. }
        eapply Included_trans. eassumption. now sets.

        intros B1 Hin1. inv Hin1. 2:{ eapply Hfv; eauto. }

        eapply Included_trans. eapply Included_Union_Setminus with (s2 := [set v]). now tci.
        eapply Union_Included.
        -- eapply Included_trans; [| eapply Hfv ]; [| now left ]. normalize_occurs_free. sets.
        -- rewrite split_fds_name_in_fundefs; [| eapply Hsplit ].
           rewrite split_fds_name_in_fundefs with (B3 := B'); [| eapply H8 ].
           now sets.
  - normalize_occurs_free. sets.
Qed.



Lemma Erase_fundefs_occurs_free_fundefs_Empty_set :
  forall e e' B m
         (Herase : Erase_fundefs e e' B m)
         (Hfv : fun_fv_in e (name_in_fundefs B)),
    occurs_free_fundefs B <--> Empty_set _.
Proof.
  intros. split; sets.
  rewrite <- Setminus_Disjoint with (s2 := name_in_fundefs B).
  2:{ eapply Disjoint_sym. eapply occurs_free_fundefs_name_in_fundefs_Disjoint. }
  eapply Included_trans. eapply Included_Setminus_compat; [| reflexivity ].
  eapply (proj1 Erase_fundefs_occurs_free_fundefs). eassumption.
  eapply split_fds_nil_r. eassumption.
  sets.
Qed.

Lemma Erase_fundefs_unique_bindings :
  forall e e' B m (Herase : Erase_fundefs e e' B m),
    unique_bindings e ->
    unique_bindings e' /\
    unique_bindings_fundefs B /\
    Disjoint _ (bound_var_fundefs B) (bound_var e').
Proof. eapply Erase_fundefs_unique_bindings_mut. Qed.

Lemma Erase_nested_fundefs_unique_bindings :
  forall B B' m (Herase : Erase_nested_fundefs B B' m),
    unique_bindings_fundefs B ->
    unique_bindings_fundefs B'.
Proof. eapply Erase_fundefs_unique_bindings_mut. Qed.


Lemma Erase_nested_fundefs_in_name B B_hoist f tau xs e m :
  unique_bindings_fundefs B ->
  f \in name_in_fundefs B ->
  Erase_nested_fundefs B B_hoist m ->
  find_def f B = Some (tau, xs, e) ->
  exists e' Be Bfuns n,
    find_def f B_hoist = Some (tau, xs, e') /\
    Erase_fundefs e e' Be n /\
    split_fds Be Bfuns B_hoist /\ n <= m.
Proof.
  intros Hun Hin Hhoist Hfind.
  induction Hhoist.
  - assert (Hunn'' : unique_bindings_fundefs B'').
    { eapply Erase_nested_fundefs_unique_bindings; [| now eapply Hun ].
      eapply Fcons_erase; eassumption. }
    inv Hun.
    destruct (peq f f0).
    * subst. simpl in Hfind. rewrite peq_true in Hfind. inv Hfind.
      do 4 eexists. split; [| split; [| split ]].
      erewrite split_fds_find_def; [ | | eassumption | ].
      simpl. rewrite peq_true. reflexivity.
      eapply unique_bindings_fundefs_unique_functions.
      eassumption. now left. eassumption.
      eassumption. eapply Nat.le_max_l.
    * subst. simpl in Hfind. rewrite peq_false in Hfind; eauto.
      inv Hin. inv H1; congruence.
      edestruct IHHhoist as [e'' [Be' [Bfuns' [n1 [Hfind' [Hr [Hsplit Hleq]]]]]]];
        eauto.
      assert (Hfind'' : find_def f B'' = Some (tau, xs, e'')).
      { erewrite split_fds_find_def; [ | | eassumption | ].
        simpl. now  rewrite peq_false; eauto.
        eapply unique_bindings_fundefs_unique_functions. eassumption.
        right. eapply Erase_nested_fundefs_name_in_fundefs. eassumption. eassumption. }
      edestruct split_fds_trans as [Bf [Heq1 Heq2]];
        [| eapply split_fds_sym; eapply H0 | ].
      eapply Right_f; eassumption.
      do 4 eexists. split; [| split; [| split ]].
      -- eassumption.
      -- eassumption.
      -- eassumption.
      -- eapply Nat.le_trans. eassumption. eapply Nat.le_max_r.
  - inv Hfind.
Qed.

Lemma funs_in_fundef_fun_in_fundefs B Be xs t e :
  funs_in_exp Be e ->
  fun_in_fundefs B (xs, t, e) ->
  funs_in_fundef Be B.
Proof.
  intros Hf1 Hf2. induction B.
  - inv Hf2.
    + inv H. constructor. eassumption.
    + constructor 2. eapply IHB. eassumption.
  - inv Hf2.
Qed.

Lemma Erase_fundefs_Ecase x l1 l2 B n :
  Erase_fundefs (Ecase x l1) (Ecase x l2) B n ->
  Forall2 (fun p1 p2 => fst p1 = fst p2) l1 l2.
Proof.
  revert x l2 B n; induction l1; intros x l2 B n Herase; inv Herase; eauto.
Qed.


Section Hoisting_correct.

  Variable (pr : prims) (cenv : ctor_env) (G : nat).

  Context {fuel : Type} {Hfuel : @fuel_resource fuel} {trace : Type} {Htrace : @trace_resource trace}.

  Context (P1 : nat -> PostT) (* Local *)
          (PG : PostGT) (* Global *)
          (HP : forall n, n <= G -> Post_properties cenv (P1 n) (P1 n) PG)
          (HPmon : forall n m, n <= m -> inclusion _ (P1 n) (P1 m))
          (Hpost_Efun_l : forall n, post_Efun_l (P1 n) (P1 (S n))).


  (** * Correctness of Erase_nested_fundefs *)
  Lemma Erase_nested_fundefs_correct S k B rho rho' B_hoist Bprev Ball n (Hleq : n <= G)
        (* IH for expresssions *)
        (IHe :
           forall m : nat,
             m < k ->
             forall (e e' : exp) (Bprev B Ball : fundefs) n (Hleq : n <= G) (rho rho' : env) (U L : nat),
               unique_bindings_fundefs Ball ->
               unique_bindings e ->
               preord_env_P cenv PG (occurs_free e) m rho rho' ->
               funs_inv_env Ball rho' ->
               split_fds Bprev B Ball ->
               Disjoint var (name_in_fundefs Ball) (bound_var e') ->
               fun_fv_in e (name_in_fundefs Ball) ->
               Erase_fundefs e e' B n -> preord_exp cenv (P1 n) PG m (e, rho) (e', rho')) :
    unique_bindings_fundefs Ball ->
    unique_bindings_fundefs B ->
    occurs_free_fundefs B \subset S ->
    (* initial environments are related *)
    preord_env_P cenv PG (S \\ name_in_fundefs B) k rho rho' ->
    (* assumptions about global funs *)
    funs_inv_env Ball rho' ->
    split_fds Bprev B_hoist Ball ->
    Disjoint var (name_in_fundefs Ball) (bound_var_fundefs B_hoist \\ name_in_fundefs B_hoist) ->
    fun_fv_in_fundefs B (name_in_fundefs Ball) ->
    (* Erase fundefs *)
    Erase_nested_fundefs B B_hoist n ->
    (* Environments after defining the function bundles *)
    preord_env_P cenv PG (name_in_fundefs B :|: S) k (def_funs B B rho rho) rho'.
  Proof.
    revert S B n Hleq rho rho' B_hoist Bprev Ball IHe.
    induction k as [k IHk] using lt_wf_rec1.
    intros S B n Hleq rho rho' B_hoist Bprev Ball IHe Hun1 Hun2
           Hsub Henv Hfuns Hsplit Hdis Hfvs Hhoist. assert (Hd' := HP). edestruct (Hd' n). eassumption.
    rewrite <- (Union_Setminus_Included (name_in_fundefs B) S (name_in_fundefs B)) at 1;
      [| tci | reflexivity ].
    eapply preord_env_P_union.
    - (* show it for the set of the added functions *)

      intros x Hin v Hget. rewrite def_funs_eq in Hget; eauto.
      inv Hget.

      destruct Hfuns as [rhoi Hfuns].

      eexists. split.
      eapply Hfuns. rewrite split_fds_name_in_fundefs; [| eassumption ]. right.
      eapply Erase_nested_fundefs_name_in_fundefs. eassumption. eassumption.

      rewrite preord_val_eq.
      intros vs1 vs2 j t xs1 e1 rho1' Heq1 Hf1 Hset1.
      edestruct Erase_nested_fundefs_in_name as [e2' [B2 [B2f [n1 [Hf2 [Hr2 [Hs2 Hleq']]]]]]];
        [| | | eapply Hf1 | ]; eauto.
      edestruct (@set_lists_length3 val (def_funs Ball Ball rhoi rhoi) xs1 vs2)
        as [rho2' Hset2].
      rewrite <- Heq1. eapply set_lists_length_eq. now eauto.
      do 3 eexists. split; [| split ].
      + erewrite split_fds_find_def; try eassumption.
        eapply unique_bindings_fundefs_unique_functions. eassumption.
        eapply Erase_nested_fundefs_name_in_fundefs; eassumption.
      + eauto.
      + intros Hlt Hall.
        eapply preord_exp_post_monotonic with (P1 := P1 n1). eapply Hd'. lia.

        assert (Hsplit' := Hsplit).
        eapply split_fds_sym in Hsplit.
        edestruct (split_fds_trans _ _ _ _ _ Hs2 Hsplit) as [Bprev' [Hs3 Hs4]].
        eapply IHe with (Ball := Ball) (Bprev := Bprev');
          last eassumption; try eassumption.
        * lia.
        * eapply unique_bindings_fun_in_fundefs.
          eapply find_def_correct. eassumption.
          eassumption.
        * eapply preord_env_P_antimon;
            [| eapply occurs_free_in_fun; eapply find_def_correct; eauto ].
          eapply preord_env_P_set_lists_l with (P1 := name_in_fundefs B :|: occurs_free_fundefs B);
            try solve [eauto].
          2:{ intros z Hnin Hinz. inv Hinz; eauto. contradiction. }
          clear Hs3 Hs4.
          (* eapply IHk to show that inner def_funs are related *)
          { eapply IHk with (Ball := Ball); last eassumption; try eassumption.
            - intros. eapply IHe; eauto. lia.
            - reflexivity.
            - intros z Hinz v Hgetz.
              inv Hinz.
              setoid_rewrite def_funs_eq; eauto.
              eexists; split; eauto.


              edestruct Henv as [v2 [Hget2 Hv2]]; eauto. constructor; eauto.
              rewrite Hfuns in Hget2. inv Hget2; eauto.
              eapply preord_val_monotonic. eassumption. lia.
              eapply Hfvs; eauto.
              eapply Hfvs; eauto.
            - eexists. intros f1 Hf. rewrite def_funs_eq. reflexivity.
              eassumption. }
        * eexists. intros f H1. erewrite <- set_lists_not_In; [| now eauto | ].
          rewrite def_funs_eq. reflexivity. eassumption.
          assert (Hun : Disjoint var (FromList xs1) (name_in_fundefs Ball)).
          { eapply unique_bindings_fun_in_fundefs; [| eassumption ].
            erewrite split_fds_fun_in_fundefs; [| eapply Hsplit ].
            left. eapply find_def_correct. eassumption. }
          intros Hc. eapply Hun. constructor. eassumption. eassumption.
        * eapply split_fds_sym. eassumption.
        * eapply Disjoint_Included_r; [| eassumption ].
          eapply Included_Setminus.

          eapply unique_bindings_fun_in_fundefs. eapply find_def_correct. eassumption.
          eapply Erase_fundefs_unique_bindings_mut. eassumption. eassumption.

          eapply Included_trans; [| eapply fun_in_fundefs_bound_var_fundefs; eauto;
                                    eapply find_def_correct; eauto ].
          sets.
        * intros Be HBe. eapply Included_trans; [| eapply Hfvs ]. reflexivity.
          right. eapply funs_in_fundef_fun_in_fundefs. eassumption.
          eapply find_def_correct. eassumption.
    - (* show if for S *)
      eapply preord_env_P_def_funs_not_in_P_l; [| sets ].
      eapply preord_env_P_antimon. eassumption. sets.
  Qed.

  (** * Correctness of Erase_fundefs *)

  Lemma hoisting_correct k e e' Bprev B Ball rho rho' n (Hleq : n <= G) :
    unique_bindings_fundefs Ball ->
    unique_bindings e ->
    (* environments are related *)
    preord_env_P cenv PG (occurs_free e) k rho rho' ->
    (* Hoisted functions are already defined *)
    funs_inv_env Ball rho' ->
    split_fds Bprev B Ball ->
    (* And will not be shadowed by other vars *)
    Disjoint _ (name_in_fundefs Ball) (bound_var e') ->
    (* the FVs of the original functions are in the global fundefs *)
    fun_fv_in e (name_in_fundefs Ball) ->
    (* Hoisting *)
    Erase_fundefs e e' B n ->
    preord_exp cenv (P1 n) PG k (e, rho) (e', rho').
  Proof.
    revert e e' Bprev B Ball n Hleq rho rho'.
    induction k as [k IHk] using lt_wf_rec1.
    intros e; revert k IHk; induction e using exp_ind';
      intros k IHk e' Bprev B Ball m Hleq' rho rho' Hun1 Hun2 Henv Hfuns Hsplit Hdis Hfvs Hhoist;
      inv Hhoist; inv Hun2; try (assert (Hd' := HP m); destruct Hd'; try lia).
    - (* Econstr *)
      eapply preord_exp_constr_compat.
      + now eauto.
      + now eauto.
      + eapply Forall2_same. intros x Hin. eapply Henv.
        now constructor.
      + intros m1 vs1 vs2 Hlt Hall.
        eapply IHk; [ eassumption | eassumption | eassumption | | | | eassumption | | | ].
        * eassumption.
        * eapply preord_env_P_extend.
          -- eapply preord_env_P_antimon.
             eapply preord_env_P_monotonic; [| eassumption ]. lia.
             normalize_occurs_free. sets.
          -- rewrite preord_val_eq. constructor; eauto.
        * eapply funs_inv_env_set. eassumption.
          eapply Disjoint_In_l. eapply Disjoint_sym. eassumption.
          normalize_bound_var; sets.
        * eapply Disjoint_Included_r; [| eassumption ].
          normalize_bound_var; sets.
        * intros B' Hbin. eapply Hfvs. constructor; eauto.
        * eassumption.
    - (* Ecase nil *)
      eapply preord_exp_case_nil_compat. eapply HP. lia.
    - (* Ecase cons *)
      eapply split_fds_sym in H8.
      edestruct split_fds_trans as [Bnew [Hs1 Hs2]].
      now eapply H8. eapply split_fds_sym. eassumption.
      eapply split_fds_sym in H8.
      edestruct split_fds_trans as [Bnew' [Hs1' Hs2']].
      now eapply H8. eapply split_fds_sym. eassumption.
      eapply preord_exp_case_cons_compat; eauto.
      + eapply HP. lia.
      + eapply HP. lia.
      + eapply HP. lia.
      + eapply Erase_fundefs_Ecase. eassumption.
      + intros m Hlt.
        eapply preord_exp_post_monotonic. eapply HPmon with (n := m0). lia.
        eapply IHk; last eassumption; eauto.
        * lia.
        * eapply preord_env_P_antimon.
          eapply preord_env_P_monotonic; [| eassumption ]. lia.
          normalize_occurs_free; sets.
        * apply split_fds_sym. eassumption.
        * eapply Disjoint_Included_r; [| eassumption ].
          normalize_bound_var; sets.
        * intros x Hin; eapply Hfvs. econstructor; eauto.
          now left.
      + eapply preord_exp_post_monotonic. eapply HPmon with (n := n). lia.
        eapply IHe0; last eassumption; eauto.
        * lia.
        * eapply preord_env_P_antimon. eassumption.
          normalize_occurs_free; sets.
        * apply split_fds_sym. eassumption.
        * eapply Disjoint_Included_r; [| eassumption ].
          normalize_bound_var; sets.
        * intros x Hin; eapply Hfvs.
          inv Hin. econstructor. eassumption.
          right. eassumption.
    - (* Eproj *)
      eapply preord_exp_proj_compat.
      + now eauto.
      + now eauto.
      + eapply Henv. eauto.
      + intros m1 vs1 vs2 Hlt Hall.
        eapply IHk; [ eassumption | eassumption | eassumption | | | | eassumption | | | ].
        * eassumption.
        * eapply preord_env_P_extend.
          -- eapply preord_env_P_antimon.
             eapply preord_env_P_monotonic; [| eassumption ]. lia.
             normalize_occurs_free. sets.
          -- eassumption.
        * eapply funs_inv_env_set. eassumption.
          eapply Disjoint_In_l. eapply Disjoint_sym. eassumption.
          normalize_bound_var; sets.
        * eapply Disjoint_Included_r; [| eassumption ].
          normalize_bound_var; sets.
        * intros B' Hbin. eapply Hfvs. constructor; eauto.
        * eassumption.
    - (* Eletapp *)
      eapply preord_exp_letapp_compat.
      + now eauto.
      + now eauto.
      + now eauto.
      + eapply Henv. constructor. now left.
      + eapply Forall2_same. intros z Hin. eapply Henv.
        constructor. now right.
      + intros m1 v1 v2 hlew Hrel.
        eapply IHk; [ eassumption | eassumption | eassumption | | | | eassumption | | | ].
        * eassumption.
        * eapply preord_env_P_extend.
          -- eapply preord_env_P_antimon.
             eapply preord_env_P_monotonic; [| eassumption ]. lia.
             normalize_occurs_free. sets.
          -- eassumption.
        * eapply funs_inv_env_set. eassumption.
          eapply Disjoint_In_l. eapply Disjoint_sym. eassumption.
          normalize_bound_var; sets.
        * eapply Disjoint_Included_r; [| eassumption ].
          normalize_bound_var; sets.
        * intros B' Hbin. eapply Hfvs. constructor; eauto.
        * eassumption.
    - (* Efun -- the only non trivial case *)
      eapply preord_exp_Efun_l.
      + eapply HP. lia.
      + now eauto.
      + eapply split_fds_sym in Hsplit.
        eapply split_fds_sym in H6.
        edestruct split_fds_trans as [Bnew [Hs1 Hs2]]. now eapply H6. eassumption.
        eapply split_fds_sym in H6.
        edestruct split_fds_trans as [Bnew' [Hs1' Hs2']]. now eapply H6. eassumption.
        eapply preord_exp_post_monotonic. eapply HPmon with (n := n). lia.

        eapply IHe with (Ball := Ball); [ | | eassumption | eassumption | | | | | | eassumption ].
        * intros. eapply IHk; eauto. lia.
        * lia.
        * eapply preord_env_P_antimon.
          -- { eapply Erase_nested_fundefs_correct with (S := occurs_free_fundefs f2 :|: occurs_free e);
               [ | | | | | | | | | | eassumption ].
               - lia.
               - intros. eapply IHk; eauto. lia.
               - eapply Hun1.
               - eassumption.
               - sets.
               - eapply preord_env_P_antimon. eapply preord_env_P_monotonic; [| eassumption ].
                 lia. normalize_occurs_free; sets.
                 rewrite Setminus_Union_distr. sets.
               - eassumption.
               - eapply split_fds_sym.  eassumption.
               - edestruct Erase_fundefs_unique_bindings.

                 eapply Efun_erase. eassumption. eassumption. eassumption. constructor; eassumption.
                 destructAll.

                 rewrite (split_fds_name_in_fundefs _ _ _ Hs2). eapply Union_Disjoint_l.
                 now sets.
                 eapply split_fds_unique_bindings_fundefs_l in Hs2. destructAll.
                 eapply Disjoint_Included_l. eapply name_in_fundefs_bound_var_fundefs. sets.
                 eassumption.
               - intros x Hfv. inv Hfv; eauto. }
          -- sets.
        * eassumption.
        * eapply split_fds_sym. eassumption.
        * eapply Disjoint_Included_r; [| eassumption ]. reflexivity.
        * intros x Hin. eapply Hfvs. constructor; eauto.
    - (* Eapp *)
      eapply preord_exp_app_compat.
      + eapply HP. lia.
      + eapply HP. lia.
      + eapply Henv. constructor.
      + eapply Forall2_same. intros z Hin. eapply Henv.
        now constructor.
    - (* Eprim *)
      eapply preord_exp_prim_val_compat.
      + now eauto.
    - (* Eprim *)
      eapply preord_exp_prim_compat.
      + now eauto.
      + eapply Forall2_same. intros x Hin. eapply Henv.
        now constructor.
    - (* Ehalt *)
      eapply preord_exp_halt_compat; eauto.
      + eapply HP. lia.
      + eapply HP. lia.
  Qed.


  (* TODO move *)
  Open Scope alg_scope.


  Context (P2: @PostT fuel trace).

  Context (Hp2 : forall n, n <= G -> post_Efun_r (P1 n) P2) (Hoot2 : post_OOT P2).

  Lemma Erase_fundefs_correct_top e e' B n (Hleq : n <= G) :
    unique_bindings e ->
    Disjoint _ (occurs_free e) (bound_var e) ->
    fun_fv_in e (funnames_in_exp e) ->
    (* Hoisting *)
    Erase_fundefs e e' B n ->

    (forall k rho rho',
        preord_env_P cenv PG (occurs_free e) k rho rho' ->
        preord_exp cenv P2 PG k (e, rho) (Efun B e', rho')) /\
    unique_bindings (Efun B e') /\
    Disjoint _ (occurs_free (Efun B e')) (bound_var (Efun B e')) /\
    occurs_free (Efun B e') \subset occurs_free e /\
    bound_var (Efun B e') \subset bound_var e.
  Proof.
    intros Hub Hdis Hin Her. split; [| split; [| split; [| split ] ] ].
    { intros k rho rho' Henv.
      eapply preord_exp_Efun_r.
      - eassumption.
      - eauto.
      - edestruct Erase_fundefs_unique_bindings. eassumption. eassumption. destructAll.
        eapply hoisting_correct with (Bprev := Fnil) (B := B) (Ball := B).
        + lia.
        + eassumption.
        + eassumption.
        + eapply preord_env_P_def_funs_not_in_P_r. eassumption.
          eapply Disjoint_Included_r; [| eassumption ].
          rewrite Erase_fundefs_bound_var; [| eassumption ].
          eapply Included_trans. eapply name_in_fundefs_bound_var_fundefs. sets.
        + eexists rho'. intros f Hfin. rewrite def_funs_eq. reflexivity. eassumption.
        + eapply split_fds_nil_r.
        + eapply Disjoint_Included_l. eapply name_in_fundefs_bound_var_fundefs. eassumption.
        + eapply Erase_fundefs_fun_fv_in. eassumption. eassumption.
        + eassumption. }
    { edestruct Erase_fundefs_unique_bindings. eassumption. eassumption. destructAll.
      constructor; eauto. sets. }
    { normalize_occurs_free.
      eapply Disjoint_Included_r.
      eapply Included_Union_Setminus with (s2 := name_in_fundefs B). tci.

      eapply Union_Disjoint_l.
      - rewrite Erase_fundefs_occurs_free_fundefs_Empty_set. sets. eassumption.
        eapply Erase_fundefs_fun_fv_in. eassumption. eassumption.
      - eapply Union_Disjoint_r; [| sets ].
        eapply Disjoint_Included_l. eapply Included_Setminus_compat.
        eapply Erase_fundefs_occurs_free. eassumption.
        eapply split_fds_nil_r. eapply Erase_fundefs_fun_fv_in. eassumption. eassumption.
        reflexivity. rewrite Setminus_Union_distr. rewrite Setminus_Same_set_Empty_set.
        repeat normalize_sets.
        normalize_bound_var. rewrite Union_commut. rewrite <- Erase_fundefs_bound_var; [| eassumption ].
        sets. }
    { repeat normalize_occurs_free.
      rewrite Erase_fundefs_occurs_free_fundefs_Empty_set; try eassumption.
      2:{ eapply Erase_fundefs_fun_fv_in. eassumption. eassumption. }
      normalize_sets.

      eapply Included_trans. eapply Included_Setminus_compat; [| reflexivity ].
      eapply Erase_fundefs_occurs_free. eassumption.
      eapply split_fds_nil_r. eapply Erase_fundefs_fun_fv_in. eassumption. eassumption.
      sets. }
    { normalize_bound_var. rewrite Union_commut. rewrite <- Erase_fundefs_bound_var.
      reflexivity. eassumption. }
  Qed.

  Context (Hinc : forall n, n <= G -> inclusion (exp * env * fuel * trace) (P1 n) P2).

  Lemma Erase_fundefs_correct_top_Fnil e e' n (Hleq : n <= G) :
    unique_bindings e ->
    Disjoint _ (occurs_free e) (bound_var e) ->
    fun_fv_in e (funnames_in_exp e) ->
    (* Hoisting *)
    Erase_fundefs e e' Fnil n ->

    (forall k rho rho',
        preord_env_P cenv PG (occurs_free e) k rho rho' ->
        preord_exp cenv P2 PG k (e, rho) (e', rho')) /\
    unique_bindings e' /\
    Disjoint _ (occurs_free e') (bound_var e') /\
    occurs_free e' \subset occurs_free e /\
    bound_var e' \subset bound_var e.
  Proof.
    intros Hub Hdis Hin Her.
    edestruct Erase_fundefs_correct_top; try eassumption. destructAll. clear H.
    inv H0.
    rewrite occurs_free_Efun, occurs_free_fundefs_Fnil in H1.
    rewrite bound_var_Efun, bound_var_fundefs_Fnil in H1.
    simpl in H1. repeat normalize_sets.

    split; [| split; [| split; [| split ]]]; try eassumption.
    intros k rho rho' Henv.

    edestruct Erase_fundefs_unique_bindings. eassumption. eassumption. destructAll.
    eapply preord_exp_post_monotonic. eapply Hinc. eassumption.
    eapply hoisting_correct with (Bprev := Fnil) (B := Fnil) (Ball := Fnil).
    + eassumption.
    + eassumption.
    + eassumption.
    + eassumption.
    + eexists rho'. intros f Hfin. inv Hfin.
    + eapply split_fds_nil_r.
    + now sets.
    + eapply Erase_fundefs_fun_fv_in. eassumption. eassumption.
    + eassumption.
    + eapply Included_trans.
      eapply Erase_fundefs_occurs_free. eassumption.
      eapply split_fds_nil_r. eapply Erase_fundefs_fun_fv_in. eassumption. eassumption.
      sets.
    + eapply Erase_fundefs_bound_var in Her. repeat normalize_bound_var_in_ctx.
      rewrite Her. sets.
  Qed.

  Lemma exp_hoist_correct_top e e' n (Hleq : n <= G) :
    unique_bindings e ->
    Disjoint _ (occurs_free e) (bound_var e) ->
    fun_fv_in e (funnames_in_exp e) ->

    exp_hoist e = (e', n) ->

    (forall k rho rho',
        preord_env_P cenv PG (occurs_free e) k rho rho' ->
        preord_exp cenv P2 PG k (e, rho) (e', rho')) /\
    unique_bindings e' /\
    Disjoint _ (occurs_free e') (bound_var e') /\
    occurs_free e' \subset occurs_free e /\
    bound_var e' \subset bound_var e.
  Proof.
    intros Hun Hdis Hfv Hh.
    unfold exp_hoist in Hh.

    edestruct (proj1 erase_fundefs_in_Erase_fundefs) as [e1 [B1 [B2 [m [H1 [Hs H2]]]]]].
    rewrite H1 in Hh. unfold id in *. clear H1.
    eapply split_fds_Fnil_eq_l in Hs. rewrite Hs in *. clear Hs.
    destruct B1.
    - inv Hh. eapply Erase_fundefs_correct_top; eauto.
    - inv Hh. eapply Erase_fundefs_correct_top_Fnil; eauto.
  Qed.

End Hoisting_correct.
