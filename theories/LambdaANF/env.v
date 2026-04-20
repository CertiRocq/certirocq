(* Well-scopedness definition for LambdaANF. Part of the CertiRocq project.
 * Author: Anonymized, 2016
 *)

Require Import LambdaANF.set_util LambdaANF.term LambdaANF.eval LambdaANF.term_util LambdaANF.ctx LambdaANF.identifiers.
From Stdlib Require Import MSets.MSetRBT Lists.List.
Require Import compcert.lib.Coqlib.


Import PS.

Definition env_subset (rho1 rho2 : env) :=
  forall x v, M.get x rho1 = Some v -> M.get x rho2 = Some v.

(** An expression is well scoped in an environment: [Γ |- e] *)
Inductive well_scoped_exp : env -> exp -> Prop :=
| WS_constr :
    forall x t ys vs e Γ,
      get_list ys Γ = Some vs ->
      (forall v, well_scoped_exp (M.set x v Γ) e) ->
      well_scoped_exp Γ (Econstr x t ys e)
| WS_case :
    forall x v te Γ,
      M.get x Γ = Some v ->
      Forall (fun p => well_scoped_exp Γ (snd p)) te ->
      well_scoped_exp Γ (Ecase x te)
| WSproj :
    forall x tau N y v e Γ,
      M.get y Γ = Some v ->
      (forall v, well_scoped_exp (M.set x v Γ) e) ->
      well_scoped_exp Γ (Eproj x tau N y e)
| WSletapp :
    forall x tau f ys v e Γ,
      get_list ys Γ = Some v ->
      (forall v, well_scoped_exp (M.set x v Γ) e) ->
      well_scoped_exp Γ (Eletapp x f tau ys e)
| WS_app :
    forall x v ys vs ft Γ,
      get_list ys Γ = Some vs ->
      M.get x Γ = Some v ->
      well_scoped_exp Γ (Eapp x ft ys)
| WS_prim :
    forall x f ys vs e Γ,
      get_list ys Γ = Some vs ->
      (forall v, well_scoped_exp (M.set x v Γ) e) ->
      well_scoped_exp Γ (Eprim x f ys e)
| WS_halt :
    forall x v Γ,
      M.get x Γ = Some v ->
      well_scoped_exp Γ (Ehalt x)
| WS_fun :
    forall defs e Γ,
      well_scoped_fundefs Γ defs ->
      (forall vs Γ',
         set_lists (elements (fundefs_names defs)) vs Γ = Some Γ' ->
         well_scoped_exp Γ' e) ->
      well_scoped_exp Γ (Efun defs e)
with well_scoped_fundefs : env -> fundefs -> Prop :=
| WS_fcons :
    forall f tau xs e defs Γ,
      (forall vs vs' Γ' Γ'',
         set_lists (elements (fundefs_names defs)) vs' Γ = Some Γ' ->
         set_lists xs vs Γ' = Some Γ'' ->
         well_scoped_exp Γ'' e) ->
      (forall v, well_scoped_fundefs (M.set f v Γ) defs) ->
      well_scoped_fundefs Γ (Fcons f tau xs e defs)
| WS_fnil :
    forall Γ,
      well_scoped_fundefs Γ Fnil.

Fixpoint fundefs_ctx_names (cdefs : fundefs_ctx) : FVSet :=
  match cdefs with
    | Fcons1_c f _ _ _ defs => add f (fundefs_names defs)
    | Fcons2_c f _ _ _ cdefs' => add f (fundefs_ctx_names cdefs')
  end.

(** [Γ {[Γ']} |- c  ]: A context is well scoped in an environment Γ, given that
    the expression we put in the hole is well scoped in the environment Γ' *)
Inductive well_scoped_exp_ctx : env -> exp_ctx -> env -> Prop :=
| WSCtx_hole :
    forall Γ Γ',
      env_subset Γ' Γ ->
      well_scoped_exp_ctx Γ Hole_c Γ'
| WSCtx_constr :
    forall x t ys vs c Γ Γ',
      get_list ys Γ = Some vs ->
      (forall v, well_scoped_exp_ctx (M.set x v Γ) c Γ') ->
      well_scoped_exp_ctx Γ (Econstr_c x t ys c) Γ'
| WSCtx_proj :
    forall x tau N y v c Γ Γ',
      M.get y Γ = Some v ->
      (forall v, well_scoped_exp_ctx (M.set x v Γ) c Γ') ->
      well_scoped_exp_ctx Γ (Eproj_c x tau N y c) Γ'
| WSCtx_letapp :
    forall x tau f ys vs c Γ Γ',
      get_list ys Γ = Some vs->
      (forall v, well_scoped_exp_ctx (M.set x v Γ) c Γ') ->
      well_scoped_exp_ctx Γ (Eletapp_c x f tau ys c) Γ'
| WSCtx_prim :
    forall x f ys vs c Γ Γ',
      get_list ys Γ = Some vs ->
      (forall v, well_scoped_exp_ctx (M.set x v Γ) c Γ') ->
      well_scoped_exp_ctx Γ (Eprim_c x f ys c) Γ'
| WSCtx_fun1 :
    forall defs c Γ Γ',
      well_scoped_fundefs Γ defs ->
      (forall vs Γ'',
         set_lists (elements (fundefs_names defs)) vs Γ = Some Γ'' ->
         well_scoped_exp_ctx Γ'' c Γ') ->
      well_scoped_exp_ctx Γ (Efun1_c defs c) Γ'
| WSCtx_fun2 :
    forall cdefs e Γ Γ',
      well_scoped_fundefs_ctx Γ cdefs Γ' ->
      (forall vs Γ'',
         set_lists (elements (fundefs_ctx_names cdefs)) vs Γ = Some Γ'' ->
         well_scoped_exp Γ'' e) ->
      well_scoped_exp_ctx Γ (Efun2_c cdefs e) Γ'
with well_scoped_fundefs_ctx : env -> fundefs_ctx -> env -> Prop :=
| WS_fcons1 :
    forall f tau xs c defs Γ Γ',
      (forall vs vs' Γ'' Γ''',
         set_lists (elements (fundefs_names defs)) vs' Γ = Some Γ''->
         set_lists xs vs Γ'' = Some Γ''' ->
         well_scoped_exp_ctx Γ''' c Γ') ->
      (forall v, well_scoped_fundefs (M.set f v Γ) defs) ->
      well_scoped_fundefs_ctx Γ (Fcons1_c f tau xs c defs) Γ'
| WS_fcons2 :
    forall f tau xs e cdefs Γ Γ',
      (forall vs vs' Γ'' Γ''',
         set_lists (elements (fundefs_ctx_names cdefs)) vs' Γ = Some Γ''->
         set_lists xs vs Γ'' = Some Γ''' ->
         well_scoped_exp Γ''' e) ->
      (forall v, well_scoped_fundefs_ctx (M.set f v Γ) cdefs Γ') ->
      well_scoped_fundefs_ctx Γ (Fcons2_c f tau xs e cdefs) Γ'.

Declare Scope env_scope.

Notation "Γ '⊢' e" := (well_scoped_exp Γ e) (at level 30, no associativity)
                      : env_scope.
Notation "Γ '{[' Γ' ']}' '⊢' e " := (well_scoped_exp_ctx Γ e Γ')
                                      (at level 30, no associativity)
                                    : env_scope.
Notation "Γ '⊢*' f" := (well_scoped_fundefs Γ f) (at level 30, no associativity)
                       : env_scope.
Notation "Γ '{[' Γ' ']}' '⊢*' f " := (well_scoped_fundefs_ctx Γ f Γ')
                                       (at level 30, no associativity)
                                     : env_scope.


Open Scope env_scope.
Open Scope ctx_scope.



Lemma env_subset_set Γ Γ' x v :
  env_subset Γ Γ' ->
  env_subset (M.set x v Γ) (M.set x v Γ')
.
Proof.
  intros Hsub x' v' Hget. rewrite M.gsspec in *.
  destruct (peq x' x); eauto.
Qed.

Lemma env_subset_set_lists Γ1 Γ2 Γ1' xs vs :
  env_subset Γ2 Γ1 ->
  Some Γ1' = set_lists xs vs Γ1 ->
  exists Γ2', Some Γ2' = set_lists xs vs Γ2 /\ env_subset Γ2' Γ1'.
Proof.
  revert vs Γ1'.
  induction xs; simpl; intros vs Γ1' Hsub Hset1;
  destruct vs; try discriminate.
  - inv Hset1; eexists; eauto.
  - destruct (set_lists xs vs Γ1) as [Γ1'' | ] eqn:Heq; try discriminate.
    edestruct (IHxs vs Γ1'' Hsub) as [Γ2' [Heq' Ηsub]]; eauto. inv Hset1.
    exists (M.set a v Γ2'). split. rewrite <- Heq'. eauto.
    eapply env_subset_set. eauto.
Qed.

Lemma env_subset_get_list Γ1 Γ2 xs vs :
  env_subset Γ1 Γ2 ->
  get_list xs Γ1 = Some vs ->
  get_list xs Γ2 = Some vs.
Proof.
  revert vs.
  induction xs; simpl; intros vs Hsub Hget; eauto.
  destruct (M.get a Γ1) eqn:Heq; try discriminate.
  destruct (get_list xs Γ1) eqn:Heq'; try discriminate.
  eapply Hsub in Heq. rewrite Heq. inv Hget.
  erewrite IHxs; eauto.
Qed.

Lemma env_subset_get Γ1 Γ2 x v :
  env_subset Γ1 Γ2 ->
  M.get x Γ1 = Some v ->
  M.get x Γ2 = Some v.
Proof.
  intros Henv Hget. eauto.
Qed.


Lemma well_scoped_exp_fundefs_weakening :
  (forall e Γ Γ',
     Γ ⊢ e -> env_subset Γ Γ' -> Γ' ⊢ e) /\
  (forall defs Γ Γ',
     Γ ⊢* defs -> env_subset Γ Γ' -> Γ' ⊢* defs).
Proof.
  exp_defs_induction IHc IHl IHfc; intros Γ Γ' Hws Hsub;
  try (now inv Hws; econstructor; eauto using env_subset_get_list, env_subset_get;
       intros; eapply IHc; eauto using env_subset_set).
  - inv Hws; econstructor; eauto.
    inv H3. constructor; eauto.
    assert (Hsuf : Γ' ⊢ Ecase v l)
      by (eapply IHl; eauto; econstructor; eauto).
    inv Hsuf; eauto.
  - inv Hws. constructor; eauto.
    intros. edestruct env_subset_set_lists as [Γ2 [Hset2 Hsub2]]; eauto.
  - inv Hws. constructor; eauto.
    intros. edestruct env_subset_set_lists as [Γ2 [Hset2 Hsub2]]; eauto.
    edestruct env_subset_set_lists as [Γ3 [Hset3 Hsub3]]; eauto.
    intros. eapply IHfc; eauto using env_subset_set.
Qed.

Lemma fundefs_names_eq fc e :
  eq (fundefs_ctx_names fc) (fundefs_names (fc <[ e ]>)).
Proof.
  induction fc; simpl; intros x; split; intros HIn; eauto;
  eapply add_spec in HIn; inv HIn; eapply add_spec; eauto;
  right; eapply IHfc; eauto.
Qed.

Lemma fundefs_names_elem fc e :
  eq (fundefs_ctx_names fc) (fundefs_names (fc <[ e ]>)).
Proof.
  induction fc; simpl; eauto;
  intros x; split; intros HIn; eauto;
  eapply add_spec in HIn; inv HIn; eapply add_spec; eauto;
  right; eapply IHfc; eauto.
Qed.

Lemma well_scoped_ctx_app :
  (forall c e Γ Γ',
     Γ {[ Γ' ]} ⊢ c  -> Γ' ⊢ e -> Γ  ⊢ c |[ e ]| ) /\
  (forall fc e Γ Γ',
     Γ {[ Γ' ]} ⊢* fc  -> Γ' ⊢ e -> Γ  ⊢* fc <[ e ]>).
Proof.
  exp_fundefs_ctx_induction IHc IHfc;
  try (now intros e' Γ Γ' Hws1 Hws2; inv Hws1;
       simpl; econstructor; eauto).
  - intros e' Γ Γ' Hws1 Hws2. inv Hws1. simpl.
    eapply well_scoped_exp_fundefs_weakening; eauto.
  - intros te e' Γ Γ' Hws1 Hws2. inv Hws1.
  - intros e' Γ Γ' Hws1 Hws2. inv Hws1.
    simpl. econstructor; eauto. intros.
    eapply H4. erewrite elements_eq; eauto.
    apply fundefs_names_eq.
  - intros e' Γ Γ' Hws1 Hws2. inv Hws1.
    simpl. econstructor; eauto. intros.
    eapply H6. erewrite elements_eq; eauto.
    apply fundefs_names_eq. eauto.
Qed.
