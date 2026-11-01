(** * Scoping of ANF conversion

    The program produced by ANF conversion ([convert_top_anf]) is closed and has unique
    bindings. Both facts are proven on the relational specification ([anf_cvt_rel] and
    [anf_cvt_rel_global]), by mutual induction:
    - every variable bound by a conversion context is a fresh variable it consumed, and it is
      bound only once ([anf_cvt_bound_vars]);
    - the free variables of a conversion context are source variables or constant variables,
      and its result variable is a source variable, a constant variable or a variable bound
      on its stem ([anf_cvt_occurs_free]). *)

From Stdlib Require Import ZArith.ZArith Lists.List micromega.Lia Arith Ensembles.
From MetaRocq.Erasure Require Import EAst.
From MetaRocq.Common Require Import BasicAst Kernames.
From compcert Require Import lib.Maps lib.Coqlib.
From CertiRocq.LambdaANF Require Import
  term ctx Ensembles_util identifiers stemctx shrink_cps_corresp.
From CertiRocq.LambdaBox_to_LambdaANF Require Import common anf anf_util anf_global.
From Stdlib Require Import ssreflect.

Import ListNotations.

(** ** Pointwise reasoning on sets *)

Lemma Disjoint_iff {A} (X Y : Ensemble A) :
  Disjoint A X Y <-> (forall x, x \in X -> x \in Y -> False).
Proof.
  split.
  - intros [h] x hx hy. apply (h x). now constructor.
  - intros h. constructor. intros x [x' hx hy]. eauto.
Qed.

(** Membership in unions, singletons and the empty set. [Setminus], [Ensembles.In] and
    [FromList] are definitions, which we unfold instead. *)
Lemma Union_app_iff {A} (X Y : Ensemble A) x : Union A X Y x <-> X x \/ Y x.
Proof. split; [intros []; auto|intros [];[left|right]; auto]. Qed.

Lemma Singleton_app_iff {A} (y x : A) : Singleton A y x <-> y = x.
Proof. split; [intros []; auto|intros ->; constructor]. Qed.

Lemma Empty_set_app_iff {A} (x : A) : Empty_set A x <-> False.
Proof. split; intros []. Qed.

Ltac sets_rw_in H :=
  rewrite_strat (repeat (topdown (choice Union_app_iff Singleton_app_iff Empty_set_app_iff
                                         in_app_iff (<- in_rev)))) in H.

Ltac sets_rw :=
  rewrite_strat (repeat (topdown (choice Union_app_iff Singleton_app_iff Empty_set_app_iff
                                         in_app_iff (<- in_rev)))).

(** Turn set inclusions, equalities and disjointness into statements about their elements *)
Ltac sets_prep :=
  unfold Same_set, Included in *;
  repeat match goal with
         | H : Disjoint _ _ _ |- _ => rewrite Disjoint_iff in H
         | |- Disjoint _ _ _ => rewrite Disjoint_iff
         end;
  unfold Setminus, Ensembles.In, FromList in *; cbv beta in *;
  repeat match goal with H : _ |- _ => progress (try sets_rw_in H) end;
  try sets_rw;
  cbn [List.In] in *.

Definition seen {A B : Type} (a : A) (b : B) : Prop := True.

(** Instantiate the pointwise hypotheses with the variables of the goal *)
Ltac sets_inst_goal :=
  repeat match goal with
         | H : forall v : var, _, y : var |- context [?y'] =>
           constr_eq y y';
           lazymatch goal with
           | _ : seen H y |- _ => fail
           | _ => pose proof (H y); assert (seen H y) by exact I
           end
         end.

(** Instantiate the pointwise hypotheses with all the variables in scope *)
Ltac sets_inst_all :=
  repeat match goal with
         | H : forall v : var, _, y : var |- _ =>
           lazymatch goal with
           | _ : seen H y |- _ => fail
           | _ => pose proof (H y); assert (seen H y) by exact I
           end
         end.

(** Reason propositionally on instances of the pointwise hypotheses, first with the
    variables of the goal only, then with all the variables *)
Ltac sets :=
  sets_prep;
  repeat match goal with
         | |- _ /\ _ => split
         | |- forall _, _ => intro
         | |- ~ _ => intro
         | H : _ /\ _ |- _ => destruct H
         end;
  first [ solve [sets_inst_goal; intuition (subst; tauto)]
        | sets_inst_all; intuition (subst; tauto) ].

Combined Scheme anf_cvt_rel_mut from anf_cvt_rel_ind', anf_cvt_rel_args_ind',
  anf_cvt_rel_mfix_ind', anf_cvt_rel_branches_ind'.

(** ** Bound variables *)

Lemma ctx_bind_proj_bound_var tg r vars n :
  bound_var_ctx (ctx_bind_proj tg r vars n) <--> FromList vars.
Proof.
  elim: vars n => [|v vars IH] n /=.
  - rewrite bound_var_Hole_c FromList_nil. reflexivity.
  - rewrite bound_var_Eproj_c IH FromList_cons. sets.
Qed.

Lemma ctx_bind_proj_unique_bindings tg r vars n :
  NoDup vars -> unique_bindings_c (ctx_bind_proj tg r vars n).
Proof.
  elim: vars n => [|v vars IH] n hnd /=.
  - constructor.
  - inversion hnd; subst. constructor; [|now apply IH].
    intros hb. apply ctx_bind_proj_bound_var in hb. exact (H1 hb).
Qed.

Lemma ub_comp c1 c2 :
  unique_bindings_c c1 -> unique_bindings_c c2 ->
  Disjoint _ (bound_var_ctx c1) (bound_var_ctx c2) -> unique_bindings_c (comp_ctx_f c1 c2).
Proof. intros. apply (proj1 (ub_comp_ctx_f c2)). auto. Qed.

Lemma ub_app c e :
  unique_bindings_c c -> unique_bindings e ->
  Disjoint _ (bound_var_ctx c) (bound_var e) -> unique_bindings (c |[ e ]|).
Proof. intros. apply (proj1 (ub_app_ctx_f e)). auto. Qed.

Lemma bound_var_comp_ctx C1 C2 :
  bound_var_ctx (comp_ctx_f C1 C2) <--> bound_var_ctx C1 :|: bound_var_ctx C2.
Proof. exact (proj1 bound_var_ctx_comp_ctx C1 C2). Qed.

(** Compute the bound variables of the contexts and terms built by ANF conversion. The
    [outermost] strategy, unlike [topdown], does not need [Proper] instances for the
    functions returning sets (such as [name_in_fundefs]) whose arguments are traversed. *)
Ltac bv_rw :=
  rewrite_strat (outermost (choice
      bound_var_comp_ctx bound_var_Econstr_c bound_var_Eproj_c bound_var_Eletapp_c
      bound_var_Eprim_val_c bound_var_Hole_c bound_var_Fun1_c ctx_bind_proj_bound_var
      bound_var_fundefs_Fcons bound_var_fundefs_Fnil bound_var_app_ctx bound_var_Ehalt
      bound_var_Ecase_cons bound_var_Ecase_nil)).

Ltac bv_simpl := repeat bv_rw.

Ltac ub_side :=
  try match goal with |- ~ ?X ?x => change (~ x \in X) end;
  bv_simpl; sets.

(** Decompose a unique bindings goal on the contexts built by ANF conversion *)
Ltac ub :=
  repeat first
    [ assumption | apply ub_comp | apply ub_app
    | apply ctx_bind_proj_unique_bindings; assumption
    | match goal with
      | |- unique_bindings_c _ => constructor
      | |- unique_bindings _ => constructor
      | |- unique_bindings_fundefs _ => constructor
      | |- NoDup _ => constructor
      end ];
  try ub_side.

(** ** Free variables *)

Lemma ctx_bind_proj_bound_stem tg r vars n :
  bound_stem_ctx (ctx_bind_proj tg r vars n) <--> FromList vars.
Proof.
  elim: vars n => [|v vars IH] n /=.
  - rewrite bound_stem_Hole_c FromList_nil. reflexivity.
  - rewrite bound_stem_Eproj_c IH FromList_cons. sets.
Qed.

Lemma ctx_bind_proj_occurs_free tg r vars n :
  occurs_free_ctx (ctx_bind_proj tg r vars n) \subset [set r].
Proof.
  elim: vars n => [|v vars IH] n /=.
  - rewrite occurs_free_Hole_c. sets.
  - rewrite occurs_free_Eproj_c. specialize (IH (n - 1)). sets.
Qed.

Ltac add_fact t :=
  let T := type of t in
  lazymatch goal with
  | _ : T |- _ => fail
  | _ => pose proof t
  end.

(** The free variables of compositions and applications of contexts are only bounded from
    above: add these bounds for the compositions and applications in the goal *)
Ltac of_facts :=
  repeat match goal with
  | |- context [comp_ctx_f ?A ?B] => add_fact (occurs_free_ctx_comp A B)
  | _ : context [comp_ctx_f ?A ?B] |- _ => add_fact (occurs_free_ctx_comp A B)
  | |- context [app_ctx_f ?A ?e] => add_fact (occurs_free_ctx_app A e)
  | _ : context [app_ctx_f ?A ?e] |- _ => add_fact (occurs_free_ctx_app A e)
  | |- context [ctx_bind_proj ?tg ?r ?vars ?n] =>
    add_fact (ctx_bind_proj_occurs_free tg r vars n)
  | _ : context [ctx_bind_proj ?tg ?r ?vars ?n] |- _ =>
    add_fact (ctx_bind_proj_occurs_free tg r vars n)
  end.

Lemma bound_stem_comp_ctx C1 C2 :
  bound_stem_ctx (comp_ctx_f C1 C2) <--> bound_stem_ctx C1 :|: bound_stem_ctx C2.
Proof. symmetry. exact (proj1 (bound_stem_comp_ctx_mut C2) C1). Qed.

(** Compute the stems and free variables of the other contexts and terms *)
Ltac of_rw :=
  rewrite_strat (outermost (choice
      bound_stem_comp_ctx bound_stem_Econstr_c bound_stem_Eproj_c bound_stem_Eletapp_c
      bound_stem_Eprim_val_c bound_stem_Hole_c bound_stem_Fun1_c ctx_bind_proj_bound_stem
      occurs_free_Econstr_c occurs_free_Eproj_c occurs_free_Eletapp_c occurs_free_Eprim_val_c
      occurs_free_Hole_c occurs_free_Efun1_c occurs_free_fundefs_Fcons occurs_free_fundefs_Fnil
      occurs_free_Ecase_cons occurs_free_Ecase_nil occurs_free_Ehalt)).

Ltac of_rw_in H :=
  rewrite_strat (outermost (choice
      bound_stem_comp_ctx bound_stem_Econstr_c bound_stem_Eproj_c bound_stem_Eletapp_c
      bound_stem_Eprim_val_c bound_stem_Hole_c bound_stem_Fun1_c ctx_bind_proj_bound_stem
      occurs_free_Econstr_c occurs_free_Eproj_c occurs_free_Eletapp_c occurs_free_Eprim_val_c
      occurs_free_Hole_c occurs_free_Efun1_c occurs_free_fundefs_Fcons occurs_free_fundefs_Fnil
      occurs_free_Ecase_cons occurs_free_Ecase_nil occurs_free_Ehalt)) in H.

Ltac of_simpl :=
  of_facts;
  repeat of_rw;
  repeat match goal with H : _ \subset _ |- _ => progress (repeat of_rw_in H) end;
  cbn [name_in_fundefs] in *.

Section Scoping.

  Context (func_tag default_tag : positive) (tgm : conId_map) (cmap : const_map).

  Local Notation anf_cvt_rel := (anf_cvt_rel func_tag default_tag tgm cmap).
  Local Notation anf_cvt_rel_args := (anf_cvt_rel_args func_tag default_tag tgm cmap).
  Local Notation anf_cvt_rel_mfix := (anf_cvt_rel_mfix func_tag default_tag tgm cmap).
  Local Notation anf_cvt_rel_branches := (anf_cvt_rel_branches func_tag default_tag tgm cmap).

  (** The variables bound by a conversion are the fresh variables it consumed (and the names
      of the functions of a fixpoint block), each bound once *)
  Lemma anf_cvt_bound_vars :
    (forall S e vn S' C r, anf_cvt_rel S e vn S' C r ->
       S' \subset S /\ bound_var_ctx C \subset S \\ S' /\ unique_bindings_c C) /\
    (forall S es vn S' C xs, anf_cvt_rel_args S es vn S' C xs ->
       S' \subset S /\ bound_var_ctx C \subset S \\ S' /\ unique_bindings_c C) /\
    (forall S mfix vn fnames S' fdefs, anf_cvt_rel_mfix S mfix vn fnames S' fdefs ->
       S' \subset S /\ bound_var_fundefs fdefs \subset (S \\ S') :|: FromList fnames /\
       (NoDup fnames -> Disjoint _ (FromList fnames) S -> unique_bindings_fundefs fdefs)) /\
    (forall S ind brs n vn r S' pats, anf_cvt_rel_branches S ind brs n vn r S' pats ->
       S' \subset S /\ bound_var (Ecase r pats) \subset S \\ S' /\
       unique_bindings (Ecase r pats)).
  Proof.
    apply anf_cvt_rel_mut; intros; subst.
    all: repeat match goal with H : _ /\ _ |- _ => destruct H end.
    all: repeat match goal with
         | H : anf_cvt_rel _ _ _ _ _ _ |- _ => clear H
         | H : anf_cvt_rel_args _ _ _ _ _ _ |- _ => clear H
         | H : anf_cvt_rel_mfix _ _ _ _ _ _ |- _ => clear H
         | H : anf_cvt_rel_branches _ _ _ _ _ _ _ _ |- _ => clear H
         end.
    all: split; [sets|split; [bv_simpl; sets|]].
    all: try (intros; ub; fail).
    - (* Fix *)
      constructor; [constructor|apply H6; [assumption|sets] | bv_simpl; sets].
    - (* Mfix_cons *)
      intros hnd hdis. inversion hnd; subst.
      have huf : unique_bindings_fundefs fdefs by apply H6; [assumption|sets].
      constructor; try ub_side; ub.
  Qed.


  (** The free variables of a conversion are source variables or constant variables, and its
      result is a source variable, a constant variable or a variable bound on its stem *)
  Lemma anf_cvt_occurs_free :
    (forall S e vn S' C r, anf_cvt_rel S e vn S' C r ->
       occurs_free_ctx C \subset FromList vn :|: cmap_vars cmap /\
       r \in FromList vn :|: bound_stem_ctx C :|: cmap_vars cmap) /\
    (forall S es vn S' C xs, anf_cvt_rel_args S es vn S' C xs ->
       occurs_free_ctx C \subset FromList vn :|: cmap_vars cmap /\
       FromList xs \subset FromList vn :|: bound_stem_ctx C :|: cmap_vars cmap) /\
    (forall S mfix vn fnames S' fdefs, anf_cvt_rel_mfix S mfix vn fnames S' fdefs ->
       name_in_fundefs fdefs <--> FromList fnames /\
       occurs_free_fundefs fdefs \subset (FromList vn :|: cmap_vars cmap) \\ FromList fnames) /\
    (forall S ind brs n vn r S' pats, anf_cvt_rel_branches S ind brs n vn r S' pats ->
       occurs_free (Ecase r pats) \subset r |: (FromList vn :|: cmap_vars cmap)).
  Proof.
    apply anf_cvt_rel_mut; intros; subst.
    all: repeat match goal with H : _ /\ _ |- _ => destruct H end.
    all: repeat match goal with
         | H : nth_error _ _ = Some _ |- _ => apply nth_error_In in H
         | H : lookup_const _ _ = Some ?v |- _ =>
           assert (v \in cmap_vars cmap) by (eexists; eassumption); clear H
         | H : anf_cvt_rel _ _ _ _ _ _ |- _ => clear H
         | H : anf_cvt_rel_args _ _ _ _ _ _ |- _ => clear H
         | H : anf_cvt_rel_mfix _ _ _ _ _ _ |- _ => clear H
         | H : anf_cvt_rel_branches _ _ _ _ _ _ _ _ |- _ => clear H
         end.
    all: of_simpl; sets.
  Qed.

End Scoping.

(** ** Global declarations and whole programs *)

Lemma cmap_vars_nil : cmap_vars [] <--> Empty_set var.
Proof. split; [intros x [s hs]; discriminate|intros x []]. Qed.

Lemma cmap_vars_cons k v cm : cmap_vars ((k, v) :: cm) \subset v |: cmap_vars cm.
Proof.
  intros x [s hs]. cbn in hs. destruct eq_kername.
  - injection hs as ->. now left.
  - right. now exists s.
Qed.

Section Global.

  Context (func_tag default_tag : positive) (tgm : conId_map).

  (** The constants are bound once, on the stem of the global context, to fresh variables *)
  Lemma anf_cvt_global_scoping S gd cm_acc cm C_env S' :
    anf_cvt_rel_global func_tag default_tag tgm S gd cm_acc cm C_env S' ->
    S' \subset S /\ bound_var_ctx C_env \subset S \\ S' /\ unique_bindings_c C_env /\
    occurs_free_ctx C_env \subset cmap_vars cm_acc /\
    cmap_vars cm \subset cmap_vars cm_acc :|: bound_stem_ctx C_env.
  Proof.
    induction 1 as [S0 cm0|S0 S1 S2 k body gd' cm0 cm1 C C_rest v hbody hrest IH| |];
      try assumption.
    - bv_simpl; of_simpl. split; [sets|split; [sets|split; [constructor|sets]]].
    - destruct (proj1 (anf_cvt_bound_vars func_tag default_tag tgm cm0) _ _ _ _ _ _ hbody)
        as (hS & hbv & hub).
      destruct (proj1 (anf_cvt_occurs_free func_tag default_tag tgm cm0) _ _ _ _ _ _ hbody)
        as (hof & hr).
      destruct IH as (hS' & hbv' & hub' & hof' & hcm).
      have hcons := cmap_vars_cons k v cm0.
      clear hbody hrest.
      split; [sets|split; [bv_simpl; sets|split; [ub|]]].
      of_simpl. split; sets.
  Qed.

  (** The program built from the conversions of the global declarations and of the main
      expression is closed and has unique bindings *)
  Theorem anf_cvt_program_scoping S gd cm C_env Sg e S' C r :
    anf_cvt_rel_global func_tag default_tag tgm S gd [] cm C_env Sg ->
    anf_cvt_rel func_tag default_tag tgm cm Sg e [] S' C r ->
    closed_exp (C_env |[ C |[ Ehalt r ]| ]|) /\ unique_bindings (C_env |[ C |[ Ehalt r ]| ]|).
  Proof.
    intros hg he.
    destruct (anf_cvt_global_scoping _ _ _ _ _ _ hg) as (hSg & hbvg & hubg & hofg & hcm).
    destruct (proj1 (anf_cvt_bound_vars func_tag default_tag tgm cm) _ _ _ _ _ _ he)
      as (hS & hbv & hub).
    destruct (proj1 (anf_cvt_occurs_free func_tag default_tag tgm cm) _ _ _ _ _ _ he)
      as (hof & hr).
    clear hg he.
    rewrite cmap_vars_nil in hofg hcm.
    split.
    - rewrite /closed_exp. of_simpl. sets.
    - ub.
  Qed.

End Global.
