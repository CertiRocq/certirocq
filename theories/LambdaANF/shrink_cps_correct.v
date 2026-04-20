From Stdlib Require Import Relations.Relations.
From Stdlib Require Import Setoids.Setoid.
From Stdlib Require Import Classes.Morphisms.
Import RelationClasses.


Require compcert.lib.Maps.
Require Import ExtLib.Data.Bool.
From Stdlib Require funind.Recdef.
Require Import compcert.lib.Coqlib.
Import Nnat.
From Stdlib Require Import Arith.Arith NArith.BinNat.
Require Import ExtLib.Data.String ExtLib.Data.List.
From Stdlib Require Import micromega.Lia Program.Program micromega.Lia Sets.Ensembles Logic.Decidable Lists.ListDec.
Require Import Libraries.CpdtTactics.
From Stdlib Require Import Sorting.Permutation.
Require Import Libraries.HashMap.
Require Import Libraries.maps_util.
Require Import LambdaANF.Ensembles_util.

Require Import LambdaANF.term LambdaANF.ctx LambdaANF.logical_relations LambdaANF.tactics LambdaANF.term_util LambdaANF.List_util
        LambdaANF.shrink_cps LambdaANF.eval LambdaANF.set_util LambdaANF.identifiers LambdaANF.stemctx LambdaANF.alpha_conv
        LambdaANF.functions LambdaANF.relations LambdaANF.rename LambdaANF.inline_letapp LambdaANF.algebra.

Open Scope ctx_scope.
Import ListNotations.

(** general rewrite rules that preserves semantics
    - Fun_inline replaces one occurence on f by its definition
    - Fun_dead removes the definition of a set of functions if none of them occur free in the rest of the program
    - Fun_rm removes a function if it doesn't occur anywhere in its mutual bundle or in the rest of the term
    -  Constr_dead removes the binding of a datatype when it doesn't occur free in the rest of the program
    -  Constr_proj replaces a binding by the nth projection of a datatype when the datatype is known (in ctx)
    -  Constr_case reduces a pattern match into an application of the right continuation on the datatype when the
        datatype is known
 *)

Inductive rw : relation exp :=
(* Rules about dead var elimination *)
| Constr_dead:
    forall x t ys e,
      ~ occurs_free e x ->
      rw (Econstr x t ys e) e
| Prim_val_dead:
    forall x p e,
      ~ occurs_free e x ->
      rw (Eprim_val x p e) e
| Prim_dead:
    forall x p ys e,
      ~ occurs_free e x ->
      rw (Eprim x p ys e) e
| Proj_dead:
    forall x t n y e,
      ~ occurs_free e x ->
      rw (Eproj x t n y e) e
| Fun_dead:
    forall e fds,
      Forall (fun v => ~ occurs_free e v) (all_fun_name fds) ->
      rw (Efun fds e) e
| Fun_rem:
    forall f t xs fb B1 B2 e,
      unique_functions (fundefs_append B1 (Fcons f t xs fb B2)) ->
      (* Zoe : This will not delete unused rec. functions. *)
      num_occur (Efun (fundefs_append B1 (Fcons f t xs fb B2)) e) f 0 ->
      rw (Efun (fundefs_append B1 (Fcons f t xs fb B2)) e) (Efun (fundefs_append B1 B2) e)
(* Rules about inlining/constant-folding *)
| Constr_case:
    forall x c cl co n e ys,
      find_tag_nth cl co e n ->
      (* x isn't shadowed on the way to the case statement *)
      ~ bound_stem_ctx c x ->
      rw (Econstr x co ys (c |[ Ecase x cl ]|)) (Econstr x co ys (c |[e]|))

| Constr_proj:
    forall v t t' n x e k ys c,
      (* nothing shadows constructor x or var k in c *)
      ~ bound_stem_ctx c x ->
      ~ bound_stem_ctx c k ->
      (* nothing rebinds k in e *)
      ~ bound_var e k ->
      x <> k ->
      v <> k ->
      nthN ys n = Some k ->
      rw (Econstr x t ys (c |[Eproj v t' n x e]|)) (Econstr x t ys (c |[ rename k v e]|))
| Fun_inline:
    forall c vs f t xs fb  fds,
      length xs = length vs ->
      find_def f fds = Some (t, xs, fb) ->
      (* nothing rebinds vs in \xs.fb *)
      Disjoint _ (bound_var fb) (FromList vs) ->
      unique_functions fds ->
      (* nothing shadows the names and FV of fds in cμ   *)
      Disjoint var (bound_stem_ctx c) (occurs_free_fundefs fds)  ->
      Disjoint var (bound_stem_ctx c) (name_in_fundefs fds)  ->

      rw (Efun fds (c |[ Eapp f t vs ]|)) (Efun fds (c |[ (rename_all (set_list (combine xs vs) (M.empty var)) fb)]|))
| Fun_inline_letapp:
    forall c vs x f t xs e1 fb fds x' C',
      length xs = length vs ->
      find_def f fds = Some (t, xs, fb) ->
      (* nothing rebinds vs in \xs.fb *)
      Disjoint _ ( bound_var fb) (FromList vs) ->
      unique_functions fds ->
      (* nothing shadows the names and FV of fds in cμ   *)
      Disjoint var (bound_stem_ctx c) (occurs_free_fundefs fds)  ->
      Disjoint var (bound_stem_ctx c) (name_in_fundefs fds)  ->

      (* Required for letapp inlining *)
      Disjoint _ (bound_var e1) (FromList vs :|: bound_var_fundefs fds :|: occurs_free_fundefs fds) ->
      Disjoint _ (occurs_free e1 \\ [set x]) (bound_var fb) ->
      ~ x \in bound_var e1 -> (* could be avoided, but holds from unique bindings assumptions *)

      inline_letapp (rename_all (set_list (combine xs vs) (M.empty var)) fb) x = Some (C', x') ->

      rw (Efun fds (c |[ Eletapp x f t vs e1]|)) (Efun fds (c |[ C' |[ rename x' x e1 ]| ]|)).

(* Congruence closure *)
Inductive gen_rw : relation exp :=
| Ctx_rw :
    forall c e e', rw e e' -> gen_rw (c |[ e ]|) (c |[ e' ]|).

Definition gr_clos n := refl_trans_closure_n gen_rw n.

Section Shrink_correct.

  Variable pr : prims.
  Variable cenv : ctor_env.

  Context {fuel : Type} {Hfuel : @fuel_resource fuel} {trace : Type} {Htrace : @trace_resource trace}.

  Variable (P1 : nat ->  @PostT fuel trace) (PG : @PostGT fuel trace)
           (HPost : forall n, n <= 1 -> Post_properties cenv (P1 n) (P1 n) PG)
           (HPost' : Post_properties cenv PG PG PG)

           (Hless_steps_app : forall f ft ys rho1 e2 rho2, post_Eapp_l (P1 0) (P1 1) f ft ys rho1 e2 rho2)
           (Hless_steps_letapp : remove_steps_letapp cenv (P1 0) (P1 0) (P1 1))
           (Hless_steps_letapp_OOT : remove_steps_letapp_OOT cenv (P1 0) (P1 1)).

  Context (Hless_steps_ctx :
             forall C e1 rho1 (rho1' : env) (e2 : exp) (rho2 : env) (cin1 cin2 : fuel)
                    (cout1 cout2 : trace),
               ctx_to_rho C rho1 rho1' ->
               len_exp_ctx C = 1 ->
               P1 0 (e1, rho1', cin1, cout1) (e2, rho2, cin2, cout2) ->
               P1 1 (C |[ e1 ]|, rho1, cin1 <+> one (C |[ e1 ]|), cout1 <+> one (C |[ e1 ]|)) (e2, rho2, cin2, cout2)).

  Context (Hless_steps_case :
             forall x cl t e n rho1 rho2 cin1 cout1 cin2 cout2,
               find_tag_nth cl t e n ->
               P1 0 (e, rho1, cin1, cout1) (e, rho2, cin2, cout2) ->
               P1 1 (Ecase x cl, rho1, cin1 <+> one (Ecase x cl), cout1 <+> one (Ecase x cl)) (e, rho2, cin2, cout2)).

  Lemma HPost_OOT : post_OOT (P1 1).
  Proof. eapply HPost; eauto. Qed.

  (* Removing unused bindings *)

  Lemma rm_constr k rho rho' e' v t l :
    ~ occurs_free e' v ->
    preord_env_P cenv PG (occurs_free e' \\ [set v]) k rho rho' ->
    preord_exp cenv (P1 1) PG k (Econstr v t l e', rho) (e', rho').
  Proof.
    intros Hnin Henv.
    eapply ctx_to_rho_preord_exp_l with (C := Econstr_c v t l Hole_c) (P1 := P1 0).
    - intros; eapply Hless_steps_ctx; eauto.
    - simpl. eapply HPost_OOT.
    - reflexivity.
    - intros. inv H. inv H7.
      eapply preord_exp_refl; eauto.
      eapply preord_env_P_set_not_in_P_l in Henv; eauto with Ensembles_DB.
      rewrite Setminus_Disjoint in Henv. eauto. eauto with Ensembles_DB.
  Qed.

  Lemma rm_prim k rho rho' e x p l :
    ~occurs_free e x ->
    preord_env_P cenv PG (occurs_free e \\ [set x]) k rho rho' ->
    preord_exp cenv (P1 1) PG k (Eprim x p l e, rho) (e, rho').
  Proof.
    intros Hnin Henv.
    eapply ctx_to_rho_preord_exp_l with (C := Eprim_c x p l Hole_c) (P1 := P1 0).
    - intros; eapply Hless_steps_ctx; eauto.
    - simpl. eapply HPost_OOT.
    - reflexivity.
    - intros. inv H.
  Qed.

  Lemma rm_prim_val k rho rho' e x p :
    ~occurs_free e x ->
    preord_env_P cenv PG (occurs_free e \\ [set x]) k rho rho' ->
    preord_exp cenv (P1 1) PG k (Eprim_val x p e, rho) (e, rho').
  Proof.
    intros Hnin Henv.
    eapply ctx_to_rho_preord_exp_l with (C := Eprim_val_c x p Hole_c) (P1 := P1 0).
    - intros; eapply Hless_steps_ctx; eauto.
    - simpl. eapply HPost_OOT.
    - reflexivity.
    - intros. inv H.
  Qed.

  Lemma rm_proj k rho rho' e x t n y :
    ~occurs_free e x ->
    preord_env_P cenv PG (occurs_free e \\ [set x]) k rho rho' ->
    preord_exp cenv (P1 1) PG k (Eproj x t n y e, rho) (e, rho').
  Proof.
    intros Hnin Henv.
    eapply ctx_to_rho_preord_exp_l with (C := Eproj_c x t n y Hole_c) (P1 := P1 0).
    - intros; eapply Hless_steps_ctx; eauto.
    - simpl. eapply HPost_OOT.
    - reflexivity.
    - intros. inv H. inv H9.
      eapply preord_exp_refl; eauto.
      eapply preord_env_P_set_not_in_P_l in Henv; sets.
      rewrite Setminus_Disjoint in Henv. eassumption. sets.
  Qed.


  Lemma split_fds_unique_name_l: forall fds,
      unique_functions fds ->
      forall fds' fds'',
        split_fds fds' fds'' fds ->
        unique_functions fds' /\ unique_functions fds'' /\
        Disjoint var (name_in_fundefs fds') (name_in_fundefs fds'').
  Proof.
    induction fds; intros H fds' fds'' Hsplit.
    - inversion H; subst.
      specialize (IHfds H6).
      inversion Hsplit; subst.
      + specialize (IHfds _ _ H4).
        destruct IHfds.
        split. constructor; [| eassumption ].
        intro; apply H2.
        now eapply split_fds_name_in_fundefs; eauto.
        destruct H1; split; auto.
        simpl. apply split_fds_name_in_fundefs in H4.
        apply Union_Disjoint_l; eauto.
        eapply Disjoint_Singleton_l. rewrite H4 in H2. eauto.
      + specialize (IHfds _ _ H4). destruct IHfds.
        destruct H1. split; [| split ]; eauto.
        simpl; constructor; eauto.
        intros Hc. apply H2.
        now eapply split_fds_name_in_fundefs; eauto.
        simpl; apply Union_Disjoint_r; eauto.
        apply split_fds_name_in_fundefs in H4.
        eapply Disjoint_Singleton_r. rewrite H4 in H2; eauto.
    - apply split_fds_to_nil in Hsplit. inv Hsplit; eauto.
      split; constructor; eauto. sets.
  Qed.

  (* TODO move *)
  Lemma split_fds_unique_functions_r B1 B2 B3 :
    unique_functions B1 -> unique_functions B2 ->
    Disjoint var (name_in_fundefs B1) (name_in_fundefs B2) ->
    split_fds B1 B2 B3 ->
    unique_functions B3.
  Proof with eauto with Ensembles_DB.
    intros Hun1 Hun2 HD Hspl. induction Hspl; simpl; repeat normalize_bound_var_in_ctx.
    - inv Hun1. constructor; eauto.
      + intros Hc.
        eapply split_fds_name_in_fundefs in Hc; [| eauto].
        inv Hc; auto.
        inv HD. specialize (H0 v). apply H0; split; auto.
        constructor. auto.
      + eapply IHHspl...
    - inv Hun2. constructor; eauto.
      + intros Hc.
        eapply split_fds_name_in_fundefs in Hc; [| eauto].
        inv Hc; auto.
        inv HD. specialize (H0 v). apply H0; split; auto.
        constructor. auto.
      + eapply IHHspl...
    - constructor.
  Qed.

  Lemma fundefs_append_unique_name_l B1 B2 B3 :
    unique_functions B3 ->
    fundefs_append B1 B2 = B3 ->
    unique_functions B1 /\
    unique_functions B2 /\
    Disjoint var (name_in_fundefs B1) (name_in_fundefs B2).
  Proof.
    intros. edestruct split_fds_unique_name_l; eauto.
    apply fundefs_append_split_fds; eauto.
  Qed.


  Lemma fundefs_append_unique_name_r B1 B2 B3 :
    fundefs_append B1 B2 = B3 ->
    unique_functions B1 ->
    unique_functions B2  ->
    Disjoint var (name_in_fundefs B1) (name_in_fundefs B2) ->
    unique_functions B3.
  Proof.
    intros.
    eapply split_fds_unique_functions_r;
      [ apply H0 | | | ]; eauto.
    apply fundefs_append_split_fds; eauto.
  Qed.

  Lemma find_def_fundefs_append_none:
    forall (f : var) (B1 B2 : fundefs) (v : fun_tag * list var * exp),
      find_def f B1 = None -> find_def f (fundefs_append B1 B2) = find_def f B2.
  Proof.
    induction B1; intros.
    simpl in *.
    destruct (M.elt_eq f v); eauto. inv H.
    simpl. auto.
  Qed.


  Lemma rm_fundefs_of k rho rho' e fds :
      Forall (fun v => ~ occurs_free e v) (all_fun_name fds) ->
      preord_env_P cenv PG (occurs_free e \\ name_in_fundefs fds)  k rho rho' ->
      preord_exp cenv (P1 1) PG k (Efun fds e, rho) (e, rho').
  Proof.
    intros Hall Hpre. eapply ctx_to_rho_preord_exp_l with (C := Efun1_c fds Hole_c) (P1 := P1 0).
    - intros; eapply Hless_steps_ctx; eauto.
    - intros; eapply HPost_OOT.
    - reflexivity.
    - intros rho1 Henv. inv Henv. inv H3.
      eapply preord_exp_refl; eauto.
      eapply Disjoint_occurs_free_name_in_fundefs_cor in Hall.
      eapply preord_env_P_def_funs_not_in_P_l; eauto.
      rewrite Setminus_Disjoint in Hpre; eauto.
  Qed.



  Lemma rm_fundefs: forall k rho rho' e fds,
      Forall (fun v => num_occur e v 0) (all_fun_name fds) ->
      preord_env_P cenv PG (occurs_free e \\ name_in_fundefs fds)  k rho rho' ->
      preord_exp cenv (P1 1) PG k (Efun fds e, rho) (e, rho').
  Proof.
    intros. eapply rm_fundefs_of; eauto.
    eapply Forall_impl; [| eassumption ]. intros.
    apply not_occurs_not_free; auto.
  Qed.


  Lemma find_def_append_not_cons:
    forall B2 f t xs fb x B1,
      x <> f ->
      find_def x (fundefs_append B1 (Fcons f t xs fb B2)) = find_def x (fundefs_append B1 B2).
  Proof.
    induction B1; intros.
    - simpl. destruct (M.elt_eq x v); auto.
    - simpl. destruct (M.elt_eq x f).
      exfalso; auto.
      auto.
  Qed.

  Lemma split_fds_unique_bindings_lr:
    forall B1 B11 B12 B2 ,
      unique_bindings_fundefs B1 ->
      split_fds B11 B12 B1 ->
      split_fds B11 B12 B2 ->
      unique_bindings_fundefs B2.
  Proof.
    intros.
    assert (HB1112 := split_fds_unique_bindings_fundefs_l _ _ _ H H0).
    destructAll.
    eapply split_fds_unique_bindings_fundefs_r.
    apply H2. apply H3. apply H4. auto.
  Qed.

  Lemma fundefs_append_num_occur:
    forall B1 B2 B,
      fundefs_append B1 B2 = B ->
      forall x n m,
        num_occur_fds B1 x n ->
        num_occur_fds B2 x m ->
        num_occur_fds B x (n+m).
  Proof.
    induction B1; intros.
    - simpl in H. destruct B. inversion H.
      specialize (IHB1 _ _ H7).
      subst.
      inv H0.
      specialize (IHB1 _ _ _ H10 H1).
      replace (n0 + m0 + m) with (n0 + (m0 + m)) by lia.
      constructor; auto.
      inv H.
    - simpl in H. inv H0. auto.
  Qed.

  Lemma fundefs_append_num_occur':
    forall B1 B2 nm x,
      num_occur_fds (fundefs_append B1 B2) x nm ->
      exists n m,
        num_occur_fds B1 x n /\ num_occur_fds B2 x m /\ n + m = nm.
  Proof.
    induction B1; intros.
    - simpl in H. inv H.
      apply IHB1 in H8. destructAll. exists (n + x0), x1. split.
      constructor; auto. split; auto. lia.
    - simpl in H. exists 0, nm. split; auto. constructor.
  Qed.

  Lemma rm_any_fundefs: forall k rho1 rho2 fb e B1 B2 xs t f ,
      unique_functions (fundefs_append B1 (Fcons f t xs fb B2)) ->
      num_occur (Efun (fundefs_append B1 B2) e) f 0 ->
      preord_env_P cenv PG (occurs_free (Efun (fundefs_append B1 B2) e)) k rho1 rho2 ->
      preord_exp cenv (P1 1) PG k (Efun (fundefs_append B1 (Fcons f t xs fb B2)) e, rho1)
                 ((Efun (fundefs_append B1 B2) e), rho2).
  Proof.
    intros k rho1 rho2 fb e B1 B2 xs t f Hnin Hub H H0. destruct (HPost 1). lia.

    eapply preord_exp_fun_compat; eauto.
    simpl. eapply preord_exp_refl; eauto.
    assert (Hin : ~ f \in (occurs_free (Efun (fundefs_append B1 B2) e))).
    { intros Hin. eapply not_occurs_not_free in Hin; eauto. } repeat normalize_occurs_free_in_ctx.
    revert Hin H. generalize (occurs_free e) as S.

    revert rho1 rho2 fb e B1 B2 xs t f Hnin Hub.
    induction k as [k' IHk'] using lt_wf_rec1; intros rho1 rho2 fb e B1 B2 xs t f Hnin Hub S H Henv.
    intros x Hin v Hget. simpl.
    destruct (peq x f); subst.
    - exfalso. eapply H. right. constructor; eauto.
      intros Hc. eapply fundefs_append_unique_name_l in Hnin; eauto.
      destruct Hnin as [Hun1 [Hun2 Hdis]]. inv Hun2. simpl in Hdis.
      rewrite fundefs_append_name_in_fundefs in Hc; [| reflexivity ]. inv Hc; eauto.
      eapply Hdis. constructor; eauto.
    -  destruct (Decidable_name_in_fundefs (fundefs_append B1 B2)) as [Hdec].
       destruct (Hdec x).
       + rewrite def_funs_eq in Hget. inv Hget.
         eexists. rewrite def_funs_eq; eauto. split; eauto.
         * rewrite preord_val_eq. intros vs1 vs2 i t' xs1 e1 rho1'' Hlen Hf1 Hset1.
           edestruct (set_lists_length3 (def_funs (fundefs_append B1 B2) (fundefs_append B1 B2) rho2 rho2) xs1 vs2).
           rewrite <- Hlen. eapply set_lists_length_eq. now eauto.
           do 3 eexists. split; [| split ]; eauto.
           erewrite <- find_def_fundefs_append_Fcons_neq; eassumption.
           intros Hlt Hall.
           eapply preord_exp_refl; eauto.
           eapply preord_env_P_set_lists_l with (P1 := occurs_free e1 \\ FromList xs1); eauto.
           replace i with (i + 1 - 1) by lia.
           erewrite find_def_fundefs_append_Fcons_neq in Hf1; try eassumption.
           eapply IHk'. lia. eassumption. eassumption.
           intros Hc. inv Hc.
           -- eapply not_occurs_not_free in H2; eauto. inv Hub. pi0. eassumption.
           -- inv Hub. pi0. eapply not_occurs_not_free in H8; eauto.
              eapply find_def_correct in Hf1.
              eapply occurs_free_in_fun in Hf1. inv H2. inv H3. eapply Hf1 in H2.
              inv H2; eauto. inv H3; eauto.
           -- eapply preord_env_P_monotonic; [| eapply preord_env_P_antimon; try eassumption ].
              lia. eapply Union_Included. now sets.
              do 2 eapply Setminus_Included_Included_Union. eapply Included_trans.
              eapply occurs_free_in_fun. eapply find_def_correct. eassumption. now sets.
           -- intros y Hnin' Hfv. constructor; eauto.
         * eapply fundefs_append_name_in_fundefs in n0; [| reflexivity ].
           eapply fundefs_append_name_in_fundefs. reflexivity. inv n0; eauto.
           right; right; eauto.
       + rewrite def_funs_neq in *; eauto. eapply preord_env_P_monotonic in Henv.
         eapply Henv. right; constructor; eauto. eassumption. lia.
         intros Hc. eapply n0. eapply fundefs_append_name_in_fundefs in Hc; [| reflexivity ].
         eapply fundefs_append_name_in_fundefs. reflexivity. inv Hc; eauto. inv H1; eauto.
         inv H2; eauto. contradiction.
  Qed.


  (* XXX unused *)
  Lemma caseConsistent_app: forall cenv t0 l0 l,
      caseConsistent cenv (l ++ l0) t0 ->
      caseConsistent cenv l t0 /\ caseConsistent cenv l0 t0.
  Proof.
    induction l; intros.
    split. apply CCnil.
    simpl in H. auto.
    inversion H; subst.
    apply IHl in H6.
    destruct H6.
    split; auto.
    eapply CCcons; eauto.
  Qed.

  (* XXX unused *)
  Lemma findtag_app_in: forall l0 t (e:exp) l,
      List.In (t, e) l ->
      findtag (l++l0) t = Some e ->
      findtag l t = Some e.
  Proof.
    induction l; intros.
    inversion H.
    simpl in H0. destruct a. simpl. destruct (M.elt_eq c t).
    auto. apply IHl; auto. inversion H.
    inversion H1; exfalso; auto.
    auto.
  Qed.

  Lemma bv_in_find_def: forall x f t1 xs1 c B,
      find_def f B = Some (t1, xs1, c) ->
      bound_var c x -> bound_var_fundefs B x.
  Proof.
    induction B; intros.
    - simpl in H. destruct (M.elt_eq f v).
      + inversion H; subst. constructor 3. auto.
      + apply IHB in H; eauto.
    - inversion H.
  Qed.

  Lemma bv_in_find_def_ctx: forall x f t1 e xs1 c B,
      find_def f B = Some (t1, xs1, c |[ e ]|) ->
      bound_var_ctx c x -> bound_var_fundefs B x.
  Proof.
    induction B; intros.
    - simpl in H. destruct (M.elt_eq f v).
      + inversion H; subst. constructor 3.  apply bound_var_app_ctx. left. assumption.
      + apply IHB in H; eauto.
    - inversion H.
  Qed.


  Fixpoint ctx_size (c:exp_ctx): nat :=
    match c with
    | Hole_c => 0
    | Econstr_c v t vs c' => 1 + ctx_size c'
    | Eproj_c v t i r c' => 1 + ctx_size c'
    | Eletapp_c _ _ _ _  c' => 1 + ctx_size c'
    | Eprim_val_c v p c' => 1 + ctx_size c'
    | Eprim_c v p vs c' => 1 + ctx_size c'
    | Ecase_c v l t c' l0 => 1 + fold_right
                                  (fun (p : ctor_tag * exp) (n : nat) => let (_, e1) := p in n + term_size e1)
                                  0 (l ++ l0) + ctx_size c'

    | Efun1_c fds c' => 1 + ctx_size c' + funs_size fds
    | Efun2_c cfds e => 1 + fundefs_ctx_size cfds + term_size e
    end
  with fundefs_ctx_size (cfds:fundefs_ctx): nat :=
         match cfds with
         | Fcons1_c v t ys c fds => 1 + ctx_size c + funs_size fds
         | Fcons2_c v t ys e cfds => 1 + term_size e + fundefs_ctx_size cfds
         end.


  Lemma app_ctx_size: (forall c e,
                          term_size (c |[e]|) = ctx_size c + term_size e) /\
                      (forall cfds e,
                          funs_size (cfds <[ e ]>) = fundefs_ctx_size cfds + term_size e).
  Proof.
    exp_fundefs_ctx_induction IHe IHf; intros; auto; try (simpl; rewrite IHe; reflexivity).
    - simpl.
      apply eq_S.
      induction l. simpl. rewrite IHe. lia.
      simpl. destruct a.
      rewrite IHl. lia.
    - simpl. rewrite IHe. lia.
    - simpl. rewrite IHf. lia.
    - simpl. rewrite IHe. lia.
    - simpl. rewrite IHf. lia.
  Qed.

  Lemma ctx_circular:
    forall c e,
      c |[e]| = e  -> c = Hole_c.
  Proof.
    intros.
    assert (term_size(c |[e]|) = ctx_size c + term_size e) by apply app_ctx_size.
    rewrite H in H0.
    destruct c; auto; exfalso; simpl in H0; lia.
  Qed.




  Lemma name_boundvar_ctx: forall  x B' e1,
      name_in_fundefs (B' <[ e1 ]>) x -> bound_var_fundefs_ctx B' x.
  Proof.
    intros.
    induction B'; intros.
    - inversion H; subst. inversion H0; subst.
      constructor.
      constructor 4.
      apply name_in_fundefs_bound_var_fundefs; auto.
    - inversion H; subst. inversion H0; subst. constructor.
      apply Bound_Fcons24_c.
      apply IHB'; auto.
  Qed.

  Lemma name_boundvar_arg: forall x xs1 f c t1 f0,
      List.In x xs1 ->
      find_def f f0 = Some (t1, xs1, c) -> bound_var_fundefs f0 x.
  Proof.
    induction f0; intros.
    - simpl in H0.
      destruct (M.elt_eq f v).
      inversion H0; subst.
      constructor. right. apply H.
      constructor 2. apply IHf0; auto.
    - inversion H0.
  Qed.

  Lemma name_boundvar_arg_ctx: forall x xs1 t1 c e2 f B',
      List.In x xs1 ->
      find_def f (B' <[ e2 ]>) = Some (t1, xs1, c) -> bound_var_fundefs_ctx B' x.
  Proof.
    induction B'; intros.
    - simpl in H0. destruct (M.elt_eq f v).
      + subst. inversion H0; subst.
        constructor 2. auto.
      + constructor 4. eapply name_boundvar_arg; eauto.
    - simpl in H0. destruct (M.elt_eq f v).
      + subst. inversion H0; subst.
        constructor. auto.
      + constructor 8. apply IHB'; auto.
  Qed.

  Lemma included_bound_var_arg_ctx: forall  xs1 t1 c e2 f B',
      find_def f (B' <[ e2 ]>) = Some (t1, xs1, c) ->
      Included var (FromList xs1) (bound_var_fundefs_ctx B').
  Proof.
    intros. intro. intros.
    eapply name_boundvar_arg_ctx; eauto.
  Qed.

  Lemma included_name_fundefs_ctx: forall B e,
      Included var (name_in_fundefs (B <[ e ]>)) (bound_var_fundefs_ctx B).
  Proof.
    intros. intro. eapply name_boundvar_ctx.
  Qed.

  Lemma fundefs_append_fnil_r: forall B, fundefs_append B Fnil = B.
  Proof.
    induction B.
    simpl. rewrite IHB. auto.
    auto.
  Qed.


  Lemma eq_env_P_def_funs:
    forall fl rho,
      eq_env_P (name_in_fundefs fl) (def_funs fl fl rho rho) rho ->
      eq_env_P (fun v => True) (def_funs fl fl rho rho) rho.
  Proof.
    intros.
    assert (Hv := Decidable_name_in_fundefs fl).
    destruct Hv.
    intro; intro.
    clear H0.
    specialize (Dec x).
    destruct Dec as [Hin | Hnin].
    + apply H in Hin. auto.
    + apply def_funs_neq.
      auto.
  Qed.


  Lemma eq_env_P_def_funs_not_in_P_l':
    forall (B B' : fundefs)
      (P : Ensemble var) (rho : M.t val) (rho1 rho2 : env),
      eq_env_P P (def_funs B' B rho rho1) rho2 ->
      Disjoint var P (name_in_fundefs B) ->
      eq_env_P P rho1 rho2.
  Proof.
    intros. intro; intros.
    specialize (H x H1).
    rewrite def_funs_neq in H; auto.
    inv H0.
    specialize (H2 x).
    intro. apply H2; auto.
  Qed.

  Lemma eq_env_P_set_lists_not_in_P_r :
    forall (xs : list M.elt)
      (vs : list val) (P : Ensemble var) (rho1 rho2 : env)
      (rho2' : M.t val),
      eq_env_P P rho1 rho2 ->
      Some rho2' = set_lists xs vs rho2 ->
      Disjoint var P (FromList xs) -> eq_env_P P rho1 rho2'.
  Proof.
    intros. intro. intros.
    specialize (H x H2).
    erewrite <- set_lists_not_In with (rho' := rho2'); eauto.
    intro.
    inv H1. specialize (H4 x).
    apply H4; auto.
  Qed.

  Lemma eq_env_P_get_list: forall {A} S (rho:M.t A) rho',
      eq_env_P S rho rho' ->
      forall xs,
        Included _ (FromList xs) S ->
        get_list xs rho = get_list xs rho'.
  Proof.
    induction xs; intros. auto.
    simpl. destruct (M.get a rho) eqn:gar.
    + assert (S a).
      apply H0.
      constructor. reflexivity.
      apply H in H1.
      rewrite <- H1. rewrite gar.
      rewrite IHxs. reflexivity.
      intro. intros.
      apply H0.
      constructor 2. auto.
    + assert (S a).
      apply H0.
      constructor; reflexivity.
      apply H in H1.
      rewrite <- H1.
      rewrite gar.
      auto.
  Qed.


  (* More precise statement of find_def_def_funs_ctx *)
  Lemma find_def_def_funs_ctx' B f e1 tau xs e' :
    find_def f (B <[ e1 ]>) = Some (tau, xs, e') ->
    (forall e2, (find_def f (B <[ e2 ]>) = Some (tau, xs, e'))) \/
    (exists c, e' = c |[ e1 ]| /\
                          (forall e2, find_def f (B <[ e2 ]>) = Some (tau, xs, c |[ e2 ]|)) /\ (exists fd fd', B = (app_fundefs_ctx fd (Fcons1_c f tau xs c fd')))).
  Proof.
    revert tau xs e'. induction B; simpl; intros tau xs e' Heq.
    - destruct (M.elt_eq f v).
      + inv Heq. right. eexists e.
        split; eauto.
        split; eauto. exists Fnil, f0; auto.
      + left; eauto.
    - destruct (M.elt_eq f v).
      + inv Heq. left; eauto.
      + apply IHB in Heq. inv Heq. left; auto.
        inv H. destruct H0.
        inv H0. right.  exists x. split; auto. split; auto. destruct H2. destruct H.
        exists (Fcons v c l e x0), (x1).
        simpl. rewrite H. auto.
  Qed.


  Lemma preord_env_P_def_funs_compat_pre_vals_stem_set S k B  rho1 rho2 B' e1 e2 S1 :
    (forall m c (rho1' rho2' : env),
        m <  k ->
        Disjoint var (bound_stem_ctx c) S ->
        eq_env_P S rho1 rho1' ->
        eq_env_P S rho2 rho2' ->
        preord_env_P cenv PG (occurs_free (c |[ e1 ]|) :|: S1) m rho1' rho2' ->
        preord_exp cenv (P1 1) PG m (c |[ e1 ]|, rho1') (c |[ e2 ]|, rho2')) ->
    preord_env_P cenv PG (occurs_free_fundefs (B' <[ e1 ]>) :|: S1) k rho1 rho2 ->
    Disjoint var (Union var (names_in_fundefs_ctx B) (bound_stem_fundefs_ctx B)) S ->
    Disjoint var (Union var (names_in_fundefs_ctx B') (bound_stem_fundefs_ctx B')) S ->
    preord_env_P cenv PG (S1 :|: (occurs_free_fundefs (B' <[ e1 ]>)) :|: (name_in_fundefs (B <[ e1 ]>)))
                 k (def_funs (B' <[ e1 ]>) (B <[ e1 ]>) rho1 rho1)
                 (def_funs (B' <[ e2 ]>) (B <[ e2 ]>) rho2 rho2).
  Proof.
    revert B rho1 rho2 B' e1 e2 S1.
    induction k as [ k IH' ] using lt_wf_rec1.
    intros B rho1 rho2 B' e1 e2 S1 Hpre Henv Hbv Hbv'.
    assert (Hval : forall f, preord_val cenv PG k (Vfun rho1 (B' <[ e1 ]>) f)
                                   (Vfun rho2 (B' <[ e2 ]>) f)).
    { intros f. rewrite preord_val_eq.
      intros vs1 vs2 j t1 xs1 e' rho1' Hlen Hf Hs.
      edestruct find_def_def_funs_ctx' as [H1 | [c [H1 H2]]]; eauto.

      + edestruct (@set_lists_length term.val) as [rho2' Hs']; eauto.
        do 4 eexists; eauto. split; eauto.
        intros Hleq Hall.
        eapply preord_exp_refl; eauto.
        eapply preord_env_P_set_lists_l; [| | now eauto | now eauto | now eauto ].
        eapply IH'; eauto.
        intros. eapply Hpre; eauto. lia.
        eapply preord_env_P_monotonic; [| eassumption ]. lia.
        intros x0 H Hfv.
        eapply find_def_correct in Hf; eauto.
        eapply occurs_free_in_fun in Hfv; eauto.
        inv Hfv. exfalso. eauto. eapply Union_assoc. right. eapply Ensembles_util.Union_commut. eauto.
      + destruct H2. inv H0. inv H2.
        edestruct (@set_lists_length term.val) as [rho2' Hs']; eauto.
        do 4 eexists; eauto.
        split; eauto.
        intros Hleq Hall.
        eapply preord_exp_post_monotonic. now eapply HPost.
        eapply Hpre; eauto.
        {
          split; intro; intro. rewrite bound_stem_app_fundefs_ctx in Hbv'.
          inv Hbv'. specialize (H1 x1). apply H1. inv H0; auto.
        }
        eapply eq_env_P_set_lists_not_in_P_r; eauto.


        apply eq_env_P_def_funs_not_in_P_r. apply eq_env_P_refl.

        rewrite <- name_in_fundefs_ctx_ctx.
        eauto with Ensembles_DB.
        rewrite bound_stem_app_fundefs_ctx in Hbv'.
        eauto with Ensembles_DB.

        symmetry in Hs'.
        intro; eapply eq_env_P_set_lists_not_in_P_r; eauto.
        apply eq_env_P_def_funs_not_in_P_r.
        apply eq_env_P_refl.
        rewrite <- name_in_fundefs_ctx_ctx.
        eauto with Ensembles_DB.
        rewrite bound_stem_app_fundefs_ctx in Hbv'.
        eauto with Ensembles_DB.

        eapply preord_env_P_set_lists_l; [| | eauto | eauto | eauto ].
        eapply IH'; eauto.
        intros. eapply Hpre; eauto. lia.
        repeat normalize_sets.
        eapply preord_env_P_antimon. eapply preord_env_P_monotonic; [| eassumption ]. lia. sets.
        intros x1 Hv Hfv.
        eapply find_def_correct in Hf; eauto. inv Hfv; eauto.
        eapply occurs_free_in_fun in H0; eauto. inv H0. now exfalso; eauto.
        eapply Union_assoc.
        right. eapply Ensembles_util.Union_commut. eauto. left; eauto. }
    induction B.
    - simpl. apply preord_env_P_extend.
      + clear Hbv. induction f.
        { simpl. apply preord_env_P_extend.
          - eapply preord_env_P_antimon; [ eassumption |].
            rewrite !Setminus_Union_distr. eapply Union_Included.
            now eauto with Ensembles_DB.
            eapply Union_Included.
            now eauto with Ensembles_DB.
            eapply Union_Included.
            now eauto with Ensembles_DB.
            rewrite Setminus_Union. rewrite (Union_commut [set v] [set v0]).
            rewrite <- Setminus_Union.
            rewrite Setminus_Same_set_Empty_set.
            now eauto with Ensembles_DB.
          - eapply Hval. }
        { simpl. eapply preord_env_P_antimon ; [ eassumption |].
          eauto with Ensembles_DB. }
      + eapply Hval.
    - simpl. apply preord_env_P_extend.
      + eapply preord_env_P_antimon. apply IHB.
        eapply Disjoint_Included_l.
        2: apply Hbv.
        apply Included_Union_compat.
        simpl. right; auto.
        rewrite bound_stem_Fcons2_c. reflexivity.
        eauto 10 with Ensembles_DB.
      + apply Hval.
  Qed.

  (* This means that only bound variables on the applicative context c will modify the evaluation context rho *)
  Lemma preord_exp_compat_vals_stem_set S1 S k rho1 rho2 c e1 e2 :
    (forall k' rho1' rho2', k' <= k ->
                       preord_env_P cenv PG (occurs_free e1 :|: S1) k' rho1' rho2' ->

                       eq_env_P S rho1 rho1' ->
                       eq_env_P S rho2 rho2' ->
                       preord_exp cenv (P1 1) PG k' (e1, rho1') (e2, rho2')) ->
    Disjoint var (bound_stem_ctx c) S ->
    preord_env_P cenv PG (occurs_free (c |[ e1 ]|) :|: S1) k rho1 rho2 ->
    preord_exp cenv (P1 1) PG k (c |[ e1 ]|, rho1) (c |[ e2 ]|, rho2).
  Proof.
    revert c S1 S rho1 rho2 e1 e2. induction k as [ k IH' ] using lt_wf_rec1.
    induction c; intros S1 S rho1 rho2 e1 e2 Hyp Hbv Hpre; eauto; (destruct (HPost 1); [ lia | ]).
    - simpl. apply Hyp. auto.
      simpl in Hpre. apply Hpre.
      apply eq_env_P_refl.
      apply eq_env_P_refl.
    - rewrite bound_stem_Econstr_c in Hbv. simpl.
      eapply preord_exp_constr_compat; eauto; intros.
      * eapply Forall2_same. intros x0 HIn. apply Hpre. left. constructor. auto.
      * assert (Disjoint _ S (Singleton _ v)).
         { eauto 10 with Ensembles_DB. }
         eapply preord_exp_monotonic. eapply IH'; eauto.
         {
           intros.
           apply Hyp; eauto. lia.
           eapply eq_env_P_set_not_in_P_l'; eauto.
           eapply eq_env_P_set_not_in_P_l'; eauto.
         }
         eapply Disjoint_Included_l; eauto.
         left; auto.
         apply preord_env_P_extend.
         eapply preord_env_P_antimon; eauto. eapply preord_env_P_monotonic; [| eassumption ]. lia.
         simpl.
         rewrite occurs_free_Econstr.
         rewrite Setminus_Union_distr. now sets.
         rewrite preord_val_eq. constructor. reflexivity. eassumption. lia.
    - simpl app_ctx_f.
      rewrite bound_stem_Eproj_c in Hbv.
      eapply preord_exp_proj_compat; eauto.
      + eapply Hpre. left. constructor; eauto.
      + intros m vs1 vs2 Hall Hpre'.
        assert (Disjoint _ S (Singleton _ v)).
        {
          eauto 10 with Ensembles_DB.
        }
        eapply IH'; eauto.
        {
          intros.
          apply Hyp; eauto. lia.
          eapply eq_env_P_set_not_in_P_l'; eauto.
          eapply eq_env_P_set_not_in_P_l'; eauto.
        }
        eauto with Ensembles_DB.
        eapply preord_env_P_extend; [| assumption ].
        eapply preord_env_P_antimon; eauto. eapply preord_env_P_monotonic; [| eassumption ]; lia.
        simpl. rewrite Setminus_Union_distr. rewrite occurs_free_Eproj. sets.
    - rewrite bound_stem_Eprim_val_c in Hbv.
      eapply preord_exp_prim_val_compat; eauto.
    - simpl.
      rewrite bound_stem_Eprim_c in Hbv.
      eapply preord_exp_prim_compat; eauto.
      + eapply Forall2_same. intros x0 Hin. eapply Hpre. left. constructor; eauto.
    (*    + intros vs1 vs2 Hall.
        assert (Disjoint _ S (Singleton _ v)).
        {
          eauto 10 with Ensembles_DB.
        }
        eapply IHc; eauto.
        {
          intros.
          apply Hyp; eauto.
          eapply eq_env_P_set_not_in_P_l'; eauto.
          eapply eq_env_P_set_not_in_P_l'; eauto.
        }
        eauto with Ensembles_DB.
        eapply preord_env_P_extend; [| assumption ].
        eapply preord_env_P_antimon; eauto.
        simpl. rewrite occurs_free_Eprim.
        eauto with Ensembles_DB. *)
    - rewrite bound_stem_Eletapp_c in Hbv. simpl.
      eapply preord_exp_letapp_compat; eauto; intros.
      * eapply Hpre. simpl. left. eapply occurs_free_Eletapp. sets.
      * eapply Forall2_same. intros x0 HIn. apply Hpre. left.
        constructor. auto. now right.
      * assert (Disjoint _ S (Singleton _ v)).
        { eauto 10 with Ensembles_DB. }
        eapply preord_exp_monotonic. eapply IH'; eauto.
        {
          intros.
          apply Hyp; eauto. lia.
          eapply eq_env_P_set_not_in_P_l'; eauto.
          eapply eq_env_P_set_not_in_P_l'; eauto.
        }
        eapply Disjoint_Included_l; eauto.
        left; auto.
        apply preord_env_P_extend.
        eapply preord_env_P_antimon; eauto. eapply preord_env_P_monotonic; [| eassumption ]. lia.
        simpl.
        rewrite occurs_free_Eletapp. rewrite Setminus_Union_distr.
        eauto 10 with Ensembles_DB. eassumption. lia.
    - simpl; eapply preord_exp_case_compat; eauto.
      eapply preord_env_P_antimon. eassumption. simpl. now sets.
      intros m Hlt.
      eapply IH'; auto.
      {
        intros.
        apply Hyp; eauto. lia.
      }
      rewrite bound_stem_Case_c in Hbv.
      eapply Disjoint_Included_l; eauto.
      reflexivity.
      eapply preord_env_P_antimon; eauto. eapply preord_env_P_monotonic; [| eassumption ]. lia.
      simpl. intros x0 H.
      inv H; eauto. left. eapply occurs_free_Ecase_Included; eauto.
      eapply in_or_app. right. left; eauto.
    - simpl.
      rewrite bound_stem_Fun1_c in Hbv.
      eapply preord_exp_fun_compat; eauto.
      assert (Disjoint _ S (name_in_fundefs f)).
      {
        eapply Disjoint_Included_l in Hbv.
        apply Disjoint_sym. apply Hbv.
        left.
        auto.
      }
      eapply preord_exp_monotonic.
      eapply IHc; eauto.
      {
        intros.
        apply Hyp; eauto.
        eapply eq_env_P_def_funs_not_in_P_l'; eauto.
        eapply eq_env_P_def_funs_not_in_P_l'; eauto.
      }
      eauto with Ensembles_DB.
      eapply preord_env_P_def_funs_cor; eauto.
      eapply preord_env_P_antimon; [ eassumption |].
      simpl. rewrite occurs_free_Efun.
      rewrite Setminus_Union_distr. eauto with Ensembles_DB. lia.
    - simpl. eapply preord_exp_fun_compat; eauto.
      eapply preord_exp_refl; eauto.
      eapply preord_env_P_antimon.
      simpl in Hpre.
      erewrite occurs_free_Efun in Hpre.
      eapply preord_env_P_def_funs_compat_pre_vals_stem_set with (S1 := S1 :|: (occurs_free e \\ name_in_fundefs (f <[ e1 ]>))); eauto.
      { intros. eapply IH' with (S1 := S1 :|: (occurs_free e \\ name_in_fundefs (f <[ e1 ]>))); eauto.
        lia.
        intros.
        eapply Hyp; eauto. lia. eapply preord_env_P_antimon. eassumption.
        now sets.
        eapply eq_env_P_trans.
        apply H1. auto.
        eapply eq_env_P_trans; eauto. }
      + eapply preord_env_P_antimon. eapply preord_env_P_monotonic; [| eassumption ]. lia.
        sets.
      + rewrite bound_stem_Fun2_c in Hbv. eassumption.
      + rewrite bound_stem_Fun2_c in Hbv. eassumption.
      + rewrite <- !Union_assoc.
        rewrite <- Union_Included_Union_Setminus; sets. tci.
  Qed.


  Corollary preord_exp_compat_stem_vals_le S1 xs vs vs' k rho1 rho2 c e1 e2 :
    (forall k' rho1 rho2, preord_env_P cenv PG (occurs_free e1 :|: S1) k' rho1 rho2 ->
                     k' <= k ->
                     get_list xs rho1 = Some vs ->
                     get_list xs rho2 = Some vs' ->
                     preord_exp cenv (P1 1) PG k' (e1, rho1) (e2, rho2)) ->
    Disjoint var (bound_stem_ctx c) (FromList xs) ->
    get_list xs rho1 = Some vs ->
    get_list xs rho2 = Some vs' ->
    preord_env_P cenv PG (occurs_free (c |[ e1 ]|) :|: S1) k rho1 rho2 ->
    preord_exp cenv (P1 1) PG k (c |[ e1 ]|, rho1) (c |[ e2 ]|, rho2).
  Proof.
    intros.
    eapply @preord_exp_compat_vals_stem_set with (S := FromList xs); eauto.
    intros. apply H; eauto.
    erewrite <- eq_env_P_get_list.
    eauto.
    eauto. intro; auto.
    erewrite <- eq_env_P_get_list.
    eauto.
    eauto. intro; auto.
  Qed.

  Corollary preord_exp_compat_vals_le S1 xs vs vs' k rho1 rho2 c e1 e2 :
    (forall k' rho1 rho2, preord_env_P cenv PG (occurs_free e1 :|: S1) k' rho1 rho2 ->
                     k' <= k ->
                     get_list xs rho1 = Some vs ->
                     get_list xs rho2 = Some vs' ->
                     preord_exp cenv (P1 1) PG k' (e1, rho1) (e2, rho2)) ->
    Disjoint var (bound_var_ctx c) (FromList xs) ->
    get_list xs rho1 = Some vs ->
    get_list xs rho2 = Some vs' ->
    preord_env_P cenv PG (occurs_free (c |[ e1 ]|) :|: S1) k rho1 rho2 ->
    preord_exp cenv (P1 1) PG k (c |[ e1 ]|, rho1) (c |[ e2 ]|, rho2).
  Proof.
    intros.
    eapply preord_exp_compat_stem_vals_le; eauto.
    eapply Disjoint_Included_l; eauto.
    apply bound_stem_var.
  Qed.

  Corollary preord_exp_compat_stem_val S1 x k val rho1 rho2 c e1 e2 :
    (forall k rho1 rho2, preord_env_P cenv PG (occurs_free e1 :|: S1) k rho1 rho2 ->
                         M.get x rho1 = Some val ->
                         preord_exp cenv (P1 1) PG k (e1, rho1) (e2, rho2)) ->
    ~ bound_stem_ctx c x ->
    M.get x rho1 = Some val ->
    preord_env_P cenv PG (occurs_free (c |[ e1 ]|) :|: S1) k rho1 rho2 ->
    preord_exp cenv (P1 1) PG k (c |[ e1 ]|, rho1) (c |[ e2 ]|, rho2).
  Proof.
    intros.
    eapply @preord_exp_compat_vals_stem_set with (S := Singleton _ x); auto.
    intros.
    apply H. eauto. specialize (H5 x). rewrite <- H1.
    symmetry. apply H5.
    constructor.
    split. intro. intro. apply H0.
    inv H3. inv H5. eauto. eassumption.
  Qed.

  Corollary preord_exp_compat_val S1 x k val rho1 rho2 c e1 e2 :
    (forall k rho1 rho2, preord_env_P cenv PG (occurs_free e1 :|: S1) k rho1 rho2 ->
                         M.get x rho1 = Some val ->
                         preord_exp cenv (P1 1) PG k (e1, rho1) (e2, rho2)) ->
    ~ bound_var_ctx c x ->
    M.get x rho1 = Some val ->
    preord_env_P cenv PG (occurs_free (c |[ e1 ]|) :|: S1) k rho1 rho2 ->
    preord_exp cenv (P1 1) PG k (c |[ e1 ]|, rho1) (c |[ e2 ]|, rho2).
  Proof.
    intros. eapply preord_exp_compat_stem_val; eauto.
    intro; apply H0.
    apply bound_stem_var. auto.
  Qed.



  Lemma rw_case_local (k0 : nat) c0 vs e cl x n (rho0 rho3 : env) :
      preord_env_P cenv PG (occurs_free (Ecase x cl)) k0 rho0 rho3 ->
      find_tag_nth cl c0 e n ->
      M.get x rho0 = Some (Vconstr c0 vs) ->
      preord_exp cenv (P1 1) PG k0 (Ecase x cl, rho0) (e, rho3).
  Proof.
    intros Hcc Hf Hget v1 c1 c2 Hleq Hs. inv Hs.
    + do 3 eexists. split; [| split ]. eapply bstep_fuel_zero_OOT. eapply lt_one in H. subst.
      eapply HPost_OOT. eapply zero_one_lt.
      now simpl; eauto.
    + inv H; repeat subst_exp.
      eapply find_tag_nth_deterministic in H5; [| clear H5; eassumption ]. inv H5.
      edestruct (preord_exp_refl cenv (P1 0) PG). now eauto.
      eapply preord_env_P_antimon. apply Hcc. 3:{ eassumption. }
      eapply occurs_free_Ecase_Included. eapply find_tag_nth_In_patterns; eassumption.
      rewrite to_nat_add in Hleq. simpl; lia.
      destructAll.
      do 3 eexists. split; [| split ]. eassumption.
      now eapply Hless_steps_case; eauto.
      eapply preord_res_monotonic. eassumption. rewrite to_nat_add. lia.
  Qed.



  Lemma rw_case_equiv  cl c0 e n x c ys rho1 rho2 k :
    find_tag_nth cl c0 e n ->
    ~bound_stem_ctx c x ->
    preord_env_P cenv PG (occurs_free (Econstr x c0 ys (c |[ Ecase x cl ]|))) k rho1 rho2 ->
    preord_exp cenv (P1 1) PG k (Econstr x c0 ys (c |[ Ecase x cl ]|), rho1) (Econstr x c0 ys (c |[ e ]|), rho2).
  Proof.
    intros Hf Hb Henv. assert (HP := HPost). destruct (HP 1). lia.
    eapply preord_exp_constr_compat; eauto.
    eapply Forall2_same. intros y Hin. eapply Henv. now constructor; eauto.
    intros m vs1 vs2 Hlt Hall.
    eapply preord_exp_compat_stem_val with (S1 := Empty_set _); eauto.
    2:{ rewrite M.gss; reflexivity. }
    - intros k' rho1' rho2' Hpre Hget1.
      rewrite Union_Empty_set_neut_r in Hpre. eapply rw_case_local; eassumption.
    - eapply preord_env_P_extend.
      eapply preord_env_P_antimon. eapply preord_env_P_monotonic; [| eassumption ]. lia.
      normalize_occurs_free; now sets.
      rewrite preord_val_eq. simpl. split; auto.
  Qed.


  Lemma preord_env_P_inj_remove (S : Ensemble var) (rho1 rho2 : env)
        (k : nat) m (x  : var) (v1 v2 : val) :
    ~ x \in (image' (fun x => M.get x m) (S \\ [set x])) ->
    preord_env_P_inj cenv PG (S \\ [set x]) k (apply_r m) rho1 rho2 ->
    preord_val cenv PG k v1 v2 ->
    preord_env_P_inj cenv PG S k (apply_r (M.remove x m)) (M.set x v1 rho1) (M.set x v2 rho2).
  Proof.
    intros Hnin Henv Hv z HP. unfold extend.
    destruct (peq z x) as [| Hneq].
    - subst. intros z Hget.
      rewrite M.gss in Hget. inv Hget. eexists.
      split; eauto. unfold apply_r. rewrite M.grs. rewrite M.gss; eauto.
    - intros z' Hget. rewrite M.gso in Hget; eauto.
      unfold apply_r. rewrite M.gro; eauto. rewrite M.gso; eauto.
      eapply Henv. constructor; eauto. intros Hc; inv Hc; eauto. eassumption.
      destruct (M.get z m) eqn:Hget'; eauto.
      intros Hc; subst. eapply Hnin. eexists. split; eauto. constructor; eauto.
      intros Hc; inv Hc; eauto.
  Qed.

  Lemma preord_env_P_inj_set_lists_remove_all (S : var -> Prop) (rho1 rho2 rho1' rho2' : env)
        (k : nat) (xs1 : list var) (vs1 vs2 : list val) m :
    Disjoint _ (image' (fun x => M.get x m) (S \\ FromList xs1)) (FromList xs1) ->
    preord_env_P_inj cenv PG (S \\ (FromList xs1)) k (apply_r m) rho1 rho2 ->
    Forall2 (preord_val cenv PG k) vs1 vs2 ->
    set_lists xs1 vs1 rho1 = Some rho1' ->
    set_lists xs1 vs2 rho2 = Some rho2' ->
    preord_env_P_inj cenv PG S k (apply_r (remove_all m xs1))  rho1' rho2'.
  Proof with now eauto with Ensembles_DB.
    revert S rho1 rho2 rho1' rho2' vs1 vs2 m.
    induction xs1; intros S rho1 rho2 rho1' rho2' vs1 vs2 m Hd Hpre Hall Hs1 Hs2.
    - simpl in *. destruct vs1; destruct vs2; try congruence. inv Hs1; inv Hs2.
      eapply preord_env_P_inj_antimon. eassumption. do 2 normalize_sets. now sets.
    - simpl in *. destruct vs1; destruct vs2; try congruence.
      destruct (set_lists xs1 vs1 rho1) eqn:Hs1'; try congruence.
      destruct (set_lists xs1 vs2 rho2) eqn:Hs2'; try congruence.
      inv Hs1; inv Hs2.
      eapply preord_env_P_inj_remove.
      + intros Hc. eapply Hd. constructor; [| now left ].
        eapply image'_get_remove_all in Hc. normalize_sets. rewrite <- Setminus_Union.
        eassumption.
      + inv Hall. eapply IHxs1; [ | | | eassumption | eassumption ]; eauto.
        eapply Disjoint_Included; [| | eassumption ].
        now normalize_sets; sets.
        normalize_sets. rewrite Setminus_Union. sets.

        eapply preord_env_P_inj_antimon. eassumption.
        normalize_sets. sets.
      + inv Hall ; eauto.
  Qed.

  Lemma rename_all_correct k (m : M.t var) e1 rho1 rho2 n (Hleq : n <= 1):
    Disjoint _ (image' (fun x => M.get x m) (occurs_free e1)) (bound_var e1) ->
    preord_env_P_inj cenv PG (occurs_free e1) k (apply_r m) rho1 rho2 ->
    preord_exp cenv (P1 n) PG k (e1, rho1) (rename_all m e1, rho2).
  Proof.
    revert e1 m rho1 rho2. induction k as [k IHk] using lt_wf_rec1.
    intros e1.
    revert k IHk; induction e1 using exp_ind'; intros k IHk m rho1 rho2 Hdis Hpre;
      (assert (HP := HPost n); destruct HP; [ lia | ]).
    - (* Econstr *)
      simpl; eapply preord_exp_constr_compat; eauto; intros.
      + eapply Forall2_preord_var_env_map. eassumption.
        normalize_occurs_free. sets.
      + eapply IHk; [ eassumption | | ].
        * eapply Disjoint_Included; [| | eassumption ].
          normalize_bound_var. now sets.
          normalize_occurs_free. rewrite image'_Union.
          eapply Included_trans. eapply image'_get_not_In. now sets.
        * eapply preord_env_P_inj_remove.
          -- intros Hc. eapply Hdis. normalize_occurs_free.
             constructor; eauto. rewrite image'_Union. right; eauto.
          -- eapply preord_env_P_inj_antimon.
             eapply preord_env_P_inj_monotonic; [| eassumption ].
             lia. normalize_occurs_free; sets.
          -- rewrite preord_val_eq. simpl; split; eauto.
    - (* Ecase nil *)
      simpl; eapply preord_exp_case_nil_compat; eauto; intros.
    - (* Ecase cons *)
      simpl; eapply preord_exp_case_cons_compat; eauto; intros.
      + clear. induction l. now constructor.
        constructor; eauto. destruct a; reflexivity.
      + eapply IHk; [ eassumption | | ].
        * eapply Disjoint_Included; [| | eassumption ].
          normalize_bound_var. now sets.
          normalize_occurs_free. rewrite !image'_Union. now sets.
        * eapply preord_env_P_inj_antimon.
          eapply preord_env_P_inj_monotonic; [| eassumption ].
          lia. normalize_occurs_free; sets.
      + eapply IHe0.
        * eauto.
        * eapply Disjoint_Included; [| | eassumption ].
          normalize_bound_var. now sets.
          normalize_occurs_free. rewrite !image'_Union. now sets.
        * eapply preord_env_P_inj_antimon.
          eapply preord_env_P_inj_monotonic; [| eassumption ].
          lia. normalize_occurs_free; sets.
    - (* Eproj *)
      simpl; eapply preord_exp_proj_compat; eauto; intros.
      eapply IHk; [ eassumption | | ].
      * eapply Disjoint_Included; [| | eassumption ].
        normalize_bound_var. now sets.
        normalize_occurs_free. rewrite image'_Union.
        eapply Included_trans. eapply image'_get_not_In. now sets.
      * eapply preord_env_P_inj_remove.
        -- intros Hc. eapply Hdis. normalize_occurs_free.
           constructor; eauto. rewrite image'_Union. right; eauto.
        -- eapply preord_env_P_inj_antimon.
           eapply preord_env_P_inj_monotonic; [| eassumption ].
           lia. normalize_occurs_free; sets.
        -- eassumption.
    - (* Eletapp *)
      simpl; eapply preord_exp_letapp_compat; eauto; intros.
      + eapply Hpre. constructor. now left.
      + eapply Forall2_preord_var_env_map. eassumption.
        normalize_occurs_free. sets.
      + eapply IHk; [ eassumption | | ].
        * eapply Disjoint_Included; [| | eassumption ].
          normalize_bound_var. now sets.
          normalize_occurs_free. rewrite image'_Union.
          eapply Included_trans. eapply image'_get_not_In. now sets.
        * eapply preord_env_P_inj_remove.
          -- intros Hc. eapply Hdis. normalize_occurs_free.
             constructor; eauto. rewrite image'_Union. right; eauto.
          -- eapply preord_env_P_inj_antimon.
             eapply preord_env_P_inj_monotonic; [| eassumption ].
             lia. normalize_occurs_free; sets.
          -- eassumption.
    - (* Efun *)
      simpl; eapply preord_exp_fun_compat; eauto.
      eapply preord_exp_monotonic.
      eapply IHe1.
      + eauto.
      + eapply Disjoint_Included; [| | eassumption ].
        normalize_bound_var. now sets.
        normalize_occurs_free. rewrite image'_Union.
        eapply Included_trans. eapply image'_get_remove_all.
        rewrite Same_set_all_fun_name. now sets.
      + eapply preord_env_P_inj_antimon with (S2 := (occurs_free (Efun f2 e1)) :|: name_in_fundefs f2).
        2:{ normalize_occurs_free; sets. rewrite <- Union_assoc, <- Union_Setminus. sets. tci. }
        induction k as [h IHk'] using lt_wf_rec1.
        intros z Hget v1 Hgetz1.
        destruct (Decidable_name_in_fundefs f2) as [Hdec]. destruct (Hdec z).
        * rewrite def_funs_eq in Hgetz1. inv Hgetz1.
          eexists. split.
          -- rewrite def_funs_eq. reflexivity.
             eapply rename_all_fun_name. unfold apply_r. rewrite in_remove_all.
             eassumption. eapply Same_set_all_fun_name. eassumption.
          -- rewrite preord_val_eq. intros vs1 vs2 j t xs1 e rho Hlen Hf Hset.
             edestruct (set_lists_length3 (def_funs (rename_all_fun (remove_all m (all_fun_name f2)) f2)
                                                    (rename_all_fun (remove_all m (all_fun_name f2)) f2) rho2 rho2)
                                          xs1 vs2).
             rewrite <- Hlen; eapply set_lists_length_eq. now eauto.
             do 3 eexists; split; [| split ].
             ++ eapply find_def_rename. unfold apply_r.
                rewrite in_remove_all. eassumption. eapply Same_set_all_fun_name. eassumption.
             ++ now eauto.
             ++ eapply find_def_correct in Hf.
                intros Hlt Hall.
                eapply preord_exp_post_monotonic. eassumption. eapply IHk.
                ** eassumption.
                ** eapply Disjoint_Included_l. eapply Included_trans.
                   eapply image'_get_remove_all. eapply image'_get_remove_all.
                   eapply Disjoint_Included; [ | | eassumption ].
                   normalize_bound_var. eapply Included_Union_preserv_l.
                   eapply Included_trans; [| now eapply fun_in_fundefs_bound_var_fundefs; eauto ].

                   now sets.
                   normalize_occurs_free. eapply image'_monotonic. do 2 eapply Setminus_Included_Included_Union.
                   eapply Included_trans. eapply occurs_free_in_fun; eauto. rewrite <- Same_set_all_fun_name.
                   sets.
                ** eapply preord_env_P_inj_set_lists_remove_all; [ | | | now eauto | now eauto ].
                   --- eapply Disjoint_Included; [| | eassumption ].
                       normalize_bound_var. eapply Included_Union_preserv_l.
                       eapply Included_trans; [| now eapply fun_in_fundefs_bound_var_fundefs; eauto ].
                       now sets.
                       eapply Included_trans. eapply image'_get_remove_all.
                       eapply image'_monotonic. do 2 eapply Setminus_Included_Included_Union.
                       eapply Included_trans. eapply occurs_free_in_fun; eauto. rewrite <- Same_set_all_fun_name.
                       normalize_occurs_free. sets.
                   --- eapply preord_env_P_inj_antimon. eapply IHk'; [ eassumption | | ].
                       +++ intros. eapply IHk; eauto. lia.
                       +++ eapply preord_env_P_inj_monotonic; [| eassumption ]. lia.
                       +++ eapply Setminus_Included_Included_Union. eapply Included_trans.
                           eapply occurs_free_in_fun. eassumption. normalize_occurs_free. sets.
                   --- eassumption.
          -- eassumption.
        * inv Hget; try contradiction.
          rewrite def_funs_neq in *; eauto. unfold apply_r. rewrite <- not_in_remove_all.
          eapply Hpre. eassumption. eassumption.
          intros Hc. eapply n0. eapply Same_set_all_fun_name. eassumption.
          intros Hc. edestruct rename_all_fun_name as [Hl Hr]. eapply Hl in Hc. clear Hr Hl.
          unfold apply_r in Hc. rewrite <- not_in_remove_all in Hc.
          destruct (M.get z m) eqn:Heq; eauto. eapply Hdis. constructor.
          now eexists; split; eauto.
          constructor; eauto. eapply name_in_fundefs_bound_var_fundefs. eassumption.
          intros Hc'. eapply n0. eapply Same_set_all_fun_name. eassumption.
      + lia.
    - (* Eapp *)
      simpl; eapply preord_exp_app_compat; eauto; intros.
      + eapply Forall2_preord_var_env_map. eassumption.
        normalize_occurs_free. sets.
    - (* Eprimval *)
      simpl; eapply preord_exp_prim_val_compat; eauto; intros.
    - (* Eprim *)
      simpl; eapply preord_exp_prim_compat; eauto; intros.
      eapply Forall2_preord_var_env_map. eassumption.
      normalize_occurs_free. sets.
    - (* Ehalt *)
      simpl; eapply preord_exp_halt_compat; eauto.
  Qed.

  Lemma num_occur_arl:
    forall x y l,
      x <> y ->
      num_occur_list (apply_r_list (M.set x y (M.empty var)) l) x = 0.
  Proof.
    induction l; intros.
    auto.
    simpl. rewrite IHl; auto.
    destruct (var_dec x a).
    + subst. erewrite apply_r_some by apply M.gss.
      destruct (term_util.var_dec a y). exfalso; auto. auto.
    + rewrite apply_r_none.
      destruct (term_util.var_dec x a). exfalso; auto. auto.
      rewrite M.gso by auto. apply M.gempty.
  Qed.


  Lemma Disjoint_Singletons:
    forall v x,
      Disjoint var (Singleton var x) (Singleton var v) ->
      x <> v.
  Proof.
    intros. intro; subst. inv H.
    specialize (H0 v).
    apply H0. split; auto.
  Qed.


  Lemma preord_env_P_inj_id S k rho1 rho2 :
    preord_env_P cenv PG S k rho1 rho2 ->
    preord_env_P_inj cenv PG S k id rho1 rho2.
  Proof.
    intros Henv z Hin v1 Hgetz. eapply Henv; eauto.
  Qed.

  Lemma preord_env_P_inj_map_id S k rho1 rho2 :
    preord_env_P cenv PG S k rho1 rho2 ->
    preord_env_P_inj cenv PG S k (apply_r (M.empty _)) rho1 rho2.
  Proof.
    intros Henv z Hin v1 Hgetz. unfold apply_r. rewrite M.gempty.
    eapply Henv; eauto.
  Qed.


  (* TODO move *)
  Lemma image'_get_Singleton {A} S x (y : A) :
    image' (fun z : positive => M.get z (M.set x y (M.empty _))) S \subset [set y].
  Proof.
    intros m [z [Hin Heq]]. destruct (peq z x); subst.
    - rewrite M.gss in Heq. inv Heq. reflexivity.
    - rewrite M.gso, M.gempty in Heq; eauto. inv Heq.
  Qed.

  (* rw rule for proj *)
  Lemma rw_proj_equiv x x' t t' ys  y e c n k rho1 rho2 :
      ~ bound_stem_ctx c x ->
      ~ bound_stem_ctx c y ->
      ~ bound_var e y  ->
      x <> y ->
      x' <> y ->
      nthN ys n = Some y ->
      preord_env_P cenv PG (occurs_free (Econstr x t ys (c |[ Eproj x' t' n x e ]|))) k rho1 rho2 ->
      preord_exp cenv (P1 1) PG k (Econstr x t ys (c |[ Eproj x' t' n x e ]|) , rho1 )
                 (Econstr x t ys (c |[ rename y x' e ]|), rho2).
  Proof.
    intros Hn1 Hn2 Hn3 Hleq Hneq Hnth Henv. assert (HP := HPost 1). destruct HP. lia.
    eapply preord_exp_constr_compat_alt; eauto.
    + eapply Forall2_same. intros. eapply Henv. now constructor.
    + intros m vs1 vs2 Hlt Hg1 Hg2.
      edestruct (@get_list_nth_get val ys vs2) as [v2 [Hnth2 Hget2]]; eauto.
      edestruct (@get_list_nth_get val ys vs1) as [v1 [Hnth1 Hget1]]; eauto.

      assert (Hval : preord_val cenv PG k v1 v2).
      { edestruct preord_env_P_get_list_l as [vs2' [Hg2' Hvs]]; [| | eapply Hg1 |].
        eassumption. normalize_occurs_free; sets. subst_exp. eapply Forall2_nthN'; eassumption. }

      eapply preord_exp_compat_stem_vals_le with (xs := [x ; y]) (S1 := Empty_set _);
        [ | | simpl; rewrite M.gss, M.gso, Hget1; eauto | simpl; rewrite M.gss, M.gso, Hget2; eauto | ].
      * intros k1 rho1' rho2' Hpre Hleq1 Hgetl1 Hgetl2.
        eapply ctx_to_rho_preord_exp_l with (C := Eproj_c x' t' n x Hole_c) (P1 := P1 0).

        -- intros; eapply Hless_steps_ctx; eauto.
        -- eassumption.
        -- reflexivity.
        -- intros rho1'' Hrho1'; inv Hrho1'. inv H8.
           eapply rename_all_correct.
           ++ lia.
           ++ eapply Disjoint_Included_l.
              eapply image'_get_Singleton. eapply Disjoint_Singleton_l. eassumption.
           ++ simpl in Hgetl1, Hgetl2.
              destruct (M.get x rho1') eqn:Hgetx1; try congruence.
              destruct (M.get y rho1') eqn:Hgety1; try congruence.
              destruct (M.get x rho2') eqn:Hgetx2; try congruence.
              destruct (M.get y rho2') eqn:Hgety2; try congruence.
              inv Hgetl2. inv Hgetl1. inv H6.
              eapply preord_env_P_inj_set_l_apply_r; eauto. eapply preord_env_P_inj_map_id.
              eapply preord_env_P_antimon. eassumption. normalize_occurs_free; sets.
              subst_exp. eapply preord_val_monotonic; eauto. lia.
      * repeat normalize_sets.
        eapply Union_Disjoint_r; eapply Disjoint_Singleton_r; eauto.
      * eapply preord_env_P_extend.
        eapply preord_env_P_antimon. eapply preord_env_P_monotonic; [| eassumption ]. lia.
        normalize_occurs_free. now sets.
        rewrite preord_val_eq.  split; eauto.
        edestruct preord_env_P_get_list_l as [vs2' [Hg2' Hvs]]; [| | eapply Hg1 |]. eassumption.
        normalize_occurs_free; sets.
        subst_exp. eapply Forall2_monotonic; [ | eassumption ].
        intros. eapply preord_val_monotonic. eassumption. lia.
  Qed.


  (* TODO move *)
  Lemma Disjoint_FromList_r A S l x :
      Disjoint A S (FromList l) ->
      List.In x l -> ~ x \in S.
  Proof.
    intros HD Hin Hin'.
    eapply HD; eauto.
  Qed.

  Lemma Disjoint_FromList_cons A S a xs :
      Disjoint A S (FromList (a :: xs)) ->
      Disjoint A S (FromList xs).
  Proof.
    normalize_sets. intros HD. sets.
  Qed.


  Lemma find_def_free_included:
    forall f t xs fb fds,
      find_def f fds = Some (t, xs, fb) ->
      Included  _
                (Setminus var (Setminus var (occurs_free fb) (FromList xs))
                          (name_in_fundefs fds))
                (occurs_free_fundefs fds).
  Proof.
    induction fds.
    - intros.
      simpl in H.
      rewrite occurs_free_fundefs_Fcons.
      destruct (M.elt_eq f v).
      + subst. inv H.
        simpl.
        eauto 20 with Ensembles_DB.
      + apply IHfds in H.
        simpl.
        intro. intros.
        right.

        assert (In var (occurs_free_fundefs fds) x).
        apply H. inv H0.
        constructor. auto. intro. apply H2. right; auto.
        constructor. auto.
        inv H0. intro.
        apply H3. left. auto.
    -   intros. inv H.
  Qed.

  Lemma image'_get_set_list S xs1 vs1 :
    image' (fun x : positive => M.get x (set_list (combine xs1 vs1) (M.empty var))) S \subset (FromList vs1).
  Proof.
    revert vs1; induction xs1; intros vs1. simpl.
    - intros m [z [Hin Heq]]. rewrite M.gempty in Heq. inv Heq.
    - destruct vs1; simpl.
      + intros m [z [Hin Heq]]. rewrite M.gempty in Heq. inv Heq.
      + intros m [z [Hin Heq]].
        destruct (peq z a); subst. rewrite M.gss in Heq. inv Heq.
        now left.
        right. eapply IHxs1. eexists; split; eauto.
        rewrite M.gso in Heq. eassumption. eassumption.
  Qed.


  (* Main lemma for function inlining *)
  Lemma rw_fun_corr f fds t xs fb vs c rho1 rho2 k :
    find_def f fds = Some (t, xs, fb) ->

    Disjoint _ (bound_var fb) (FromList vs) ->
    unique_functions fds ->
    Disjoint var (bound_stem_ctx c) (occurs_free_fundefs fds)  ->
    Disjoint var (bound_stem_ctx c) (name_in_fundefs fds)  ->

    preord_env_P cenv PG (occurs_free (Efun fds (c |[ Eapp f t vs ]|))) k rho1 rho2 ->
    preord_exp cenv (P1 1) PG k
               (Efun fds (c |[ Eapp f t vs ]|), rho1)
               (Efun fds (c |[ (rename_all (set_list (combine xs vs) (M.empty var)) fb)]|), rho2).
  Proof.
    intros Hf1 Hd1 Hun1 Hd2 Hd3 Hpre. assert (HP := HPost 1). destruct HP. lia.
    eapply preord_exp_fun_compat; eauto.
    assert (Hget1 : M.get f (def_funs fds fds rho1 rho1) = Some (Vfun rho1 fds f)).
    { rewrite def_funs_eq. reflexivity. eapply fun_in_fundefs_name_in_fundefs. eapply find_def_correct.
      eassumption. }
    assert (Hget2 : M.get f (def_funs fds fds rho2 rho2) = Some (Vfun rho2 fds f)).
    { rewrite def_funs_eq. reflexivity. eapply fun_in_fundefs_name_in_fundefs. eapply find_def_correct.
      eassumption. }

    eapply @preord_exp_compat_vals_stem_set with
        (S1 := name_in_fundefs fds :|: occurs_free_fundefs fds) (S :=  name_in_fundefs fds :|: occurs_free_fundefs fds).

    * intros k1 rho1' rho2' Hleq1 Hpre' Heq1 Heq2.

      assert (Hf1' := Hf1).
      eapply find_def_correct in Hf1; eapply fun_in_fundefs_name_in_fundefs in Hf1.
      eapply preord_exp_app_l. now eauto. now eauto. intros rhoc rho' e1 vs1 f' xs1 B Hgetl Hget Hf Hset.
      rewrite def_funs_eq in Hget1, Hget2; eauto.
      inv Hget1; inv Hget2.

      rewrite <- Heq1 in Hget. rewrite def_funs_eq in Hget; eauto. inv Hget. repeat subst_exp.

      eapply rename_all_correct.
      ++ lia.
      ++ eapply Disjoint_Included_l. eapply image'_get_set_list.
         eapply Disjoint_sym. eapply Disjoint_Included_l; [| eassumption ].
         now sets.

      ++ edestruct preord_env_P_get_list_l as [vs2 [Hget' Hvall]]; [ | | eassumption | ]. eassumption.
         normalize_occurs_free. sets.
         (* erewrite <- get_list_def_funs_Disjoint in Hget'.         *)
         eapply preord_env_P_inj_set_lists_l; [ | | | ]; eauto.

         eapply preord_env_eq_env.
         ** eapply preord_env_P_antimon.
            eapply preord_env_P_def_funs_pre. eassumption.
            { intros. eapply preord_exp_refl; eauto. }
            eapply preord_env_P_monotonic; [| eassumption ]. lia.
            eapply Setminus_Included_Included_Union.
            eapply Included_trans. eapply occurs_free_in_fun. eapply find_def_correct; eauto.
            normalize_occurs_free. sets.
         ** eapply eq_env_P_refl.
         ** intros x Hin. eapply Heq2. inv Hin. eapply occurs_free_in_fun in H; [| eapply find_def_correct; eassumption ].
            inv H; eauto. contradiction.
      ++ now left.
    * sets.
    * eapply preord_env_P_antimon.
      eapply preord_env_P_def_funs_pre with (e := c |[ Eapp f t vs ]|); eauto.
      { intros. eapply preord_exp_refl; eauto. }
      eapply preord_env_P_antimon. eapply preord_env_P_monotonic; [| eassumption ]. lia. reflexivity.
      normalize_occurs_free. rewrite <- Union_assoc, <- Union_Setminus; tci. sets.
  Qed.

  (* TODO move *)
  Ltac normalize_bound_var_ctx :=
  match goal with
    | [|- context[bound_var_ctx (Econstr_c _ _ _ _)]] =>
      rewrite bound_var_Econstr_c
    | [|- context[bound_var_ctx (Eproj_c _ _ _ _ _)]] =>
      rewrite bound_var_Eproj_c
    | [|- context[bound_var_ctx (Ecase_c _ _ _ _ _)]] =>
      rewrite bound_var_Case_c
    | [|- context[bound_var_ctx (Eletapp_c _ _ _ _ _)]] =>
      rewrite bound_var_Eletapp_c
    | [|- context[bound_var_ctx (Efun1_c _ _)]] =>
      rewrite bound_var_Fun1_c
    | [|- context[bound_var_ctx (Efun2_c _ _)]] =>
      rewrite bound_var_Fun2_c
    | [|- context[bound_var_ctx (Eprim_c _ _ _ _)]] =>
      rewrite bound_var_Eprim_c
    | [|- context[bound_var_ctx Hole_c]] =>
      rewrite bound_var_Hole_c
    | [|- context[bound_var_fundefs_ctx (Fcons1_c _ _ _ _ _)]] =>
      rewrite bound_var_Fcons1_c
    | [|- context[bound_var_fundefs_ctx (Fcons2_c _ _ _ _ _)]] =>
       rewrite bound_var_Fcons2_c
  end.

  (* Letapp inlining *)
  Lemma rw_fun_letapp_corr x f fds t xs fb vs c rho1 rho2 k x' C' e1 :
    find_def f fds = Some (t, xs, fb) ->

    Disjoint _ (bound_var fb) (FromList vs) ->
    unique_functions fds ->
    Disjoint var (bound_stem_ctx c) (occurs_free_fundefs fds)  ->
    Disjoint var (bound_stem_ctx c) (name_in_fundefs fds)  ->

    (* Required for letapp inlining *)
    Disjoint _ (bound_var e1) (FromList vs :|: bound_var_fundefs fds :|: occurs_free_fundefs fds) ->
    Disjoint _ (occurs_free e1 \\ [set x]) (bound_var fb) ->
    ~ x \in bound_var e1 -> (* could be avoided, but holds from unique bindings assumptions *)


    inline_letapp
      (rename_all
         (set_list (combine xs vs) (M.empty var)) fb) x = Some (C', x') ->

    preord_env_P cenv PG (occurs_free (Efun fds (c |[ Eletapp x f t vs e1 ]|))) k rho1 rho2 ->
    preord_exp cenv (P1 1) PG k
               (Efun fds (c |[ Eletapp x f t vs e1 ]|), rho1)
               (Efun fds (c |[ C' |[ rename x' x e1 ]| ]|), rho2).
  Proof.
    intros Hf1 Hd1 Hun1 Hd2 Hd3  Hd4 Hd5 Hnin Hnd Hpre. assert (HP := HPost 1). destruct HP. lia.
    eapply preord_exp_fun_compat; eauto.
    assert (Hget1 : M.get f (def_funs fds fds rho1 rho1) = Some (Vfun rho1 fds f)).
    { rewrite def_funs_eq. reflexivity. eapply fun_in_fundefs_name_in_fundefs. eapply find_def_correct.
      eassumption. }
    assert (Hget2 : M.get f (def_funs fds fds rho2 rho2) = Some (Vfun rho2 fds f)).
    { rewrite def_funs_eq. reflexivity. eapply fun_in_fundefs_name_in_fundefs. eapply find_def_correct.
      eassumption. }

    eapply @preord_exp_compat_vals_stem_set with (S1 := name_in_fundefs fds :|: occurs_free_fundefs fds)
                                                (S :=  name_in_fundefs fds :|: occurs_free_fundefs fds).
    - intros k1 rho1' rho2' Hleq1 Hpre' Heq1 Heq2.

      assert (Hf1' := Hf1).
      eapply find_def_correct in Hf1; eapply fun_in_fundefs_name_in_fundefs in Hf1.

      eapply @inline_letapp_correct with (C' := Hole_c) (sig := id); [ | | | | | | | | | eassumption ].
      + eassumption.
      + eassumption.
      + eassumption.
      + intros m rhoc rhoc' B f' xs1 vs1 e Hlt Hget' Hf' Hgetl Hsetl.
        rewrite <- Heq1, def_funs_eq in Hget'; eauto. inv Hget'. repeat subst_exp.
        2:{ left; eauto. } simpl (_ |[ _ ]|).

        eapply rename_all_correct.
        * lia.
        * eapply Disjoint_Included_l. eapply image'_get_set_list. sets.
        * edestruct preord_env_P_get_list_l as [vs2 [Hget' Hvall]]; [ | | eassumption | ]. eassumption.
          normalize_occurs_free. now sets.
          eapply preord_env_P_inj_set_lists_l; [ | eassumption | | ]; eauto.
          -- eapply preord_env_eq_env.
             ** eapply preord_env_P_antimon.
                eapply preord_env_P_def_funs_pre. eassumption.
                { intros. eapply preord_exp_refl; eauto. }
                eapply preord_env_P_monotonic; [| eassumption ]. lia.
                eapply Setminus_Included_Included_Union.
                eapply Included_trans. eapply occurs_free_in_fun. eapply find_def_correct; eauto.
                normalize_occurs_free. sets.
             ** eapply eq_env_P_refl.
             ** intros z Hin. eapply Heq2. inv Hin.
                eapply occurs_free_in_fun in H; [| eapply find_def_correct; eassumption ].
                inv H; eauto. contradiction.
          -- eapply Forall2_monotonic; [| eassumption ]. intros z1 z2 Hv.
             eapply preord_val_monotonic; eauto. lia.
      + intros m rho3 rho4 rhoc B' f' t' xs1' e' Hlt Hgetf Hfind Hlen Henv.
        rewrite <- Heq1 in Hgetf; [| now left; eauto ]. rewrite def_funs_eq in Hgetf. inv Hgetf. repeat subst_exp.
        eapply rename_all_correct.
        * lia.
        * eapply Disjoint_Included_l.
          eapply image'_get_Singleton.
          destruct (inline_letapp_var_eq _ _ _ _ Hnd).
          -- subst. sets. (* prehaps could be avoided by strengthening rename_all_correct *)
          -- rewrite rename_all_bound_var in H.
             inv H.

             ++ eapply Disjoint_Included_l. eapply Singleton_Included. eassumption.
                eapply Disjoint_sym. eapply Disjoint_Included; [| | eapply Hd4 ]; sets.
                eapply Included_trans. eapply Included_trans; [| eapply bound_var_fun_in_fundefs; eapply find_def_correct; eauto ].
                now sets. now sets.
             ++ eapply rename_all_occurs_free in H0.
                eapply image_apply_r_set_list in H0.
                2:{ eassumption. }
                rewrite image_apply_r_empty in H0.
                eapply Disjoint_sym. eapply Disjoint_Included; [| | eapply Hd4 ].
                inv H0. eapply Singleton_Included. left; now left.
                eapply find_def_correct in Hf1'. eapply occurs_free_in_fun in Hf1'.
                inv H. eapply Hf1' in H0. eapply Singleton_Included.
                inv H0. contradiction. inv H.
                left. right. eapply name_in_fundefs_bound_var_fundefs. eassumption.
                right. eassumption.
                reflexivity.
        * eapply preord_env_P_inj_f_eq_subdomain. eassumption.
          unfold apply_r. intros z Hin. destruct (peq z x); subst. rewrite extend_gss, M.gss.
          reflexivity.
          rewrite extend_gso, M.gso, M.gempty; eauto.
        * eassumption.
      + eapply preord_env_P_antimon. eassumption. sets.
      + rewrite image_id, bound_var_Hole_c, Union_Empty_set_neut_l.
        eapply Disjoint_Included_l. eapply bound_var_inline_letapp.  eassumption.
        eapply Union_Disjoint_l. now sets.
        rewrite rename_all_bound_var.
        eapply Disjoint_sym. sets.
      + rewrite image_id. destruct (inline_letapp_var_eq _ _ _ _ Hnd); subst.
        * intros Hc; inv Hc. eapply H0; reflexivity.
        * intros Hc. inv Hc. eapply H1; eauto.
      + reflexivity.
    - sets.
    - eapply preord_env_P_antimon.
      eapply preord_env_P_def_funs_pre with (e := c |[ Eletapp x f t vs e1 ]|); eauto.
      { intros. eapply preord_exp_refl; eauto. }
      eapply preord_env_P_antimon. eapply preord_env_P_monotonic; [| eassumption ]. lia. reflexivity.
      normalize_occurs_free. rewrite <- Union_assoc, <- Union_Setminus; tci. sets.
  Qed.


  (* can be restricted to bound_var on the path to hole in c *)
  Lemma occurs_free_app_bound_var x e:
    occurs_free e x ->
    ( forall c,
        ~ occurs_free (c |[e]|) x -> bound_var_ctx c x) /\
    ( forall fds,
        ~ occurs_free_fundefs (fds <[e]>) x -> bound_var_fundefs_ctx fds x).
  Proof.
    intro H.
    apply exp_fundefs_ctx_mutual_ind; intros.
    + exfalso. apply H0. apply H.
    + simpl in H1.
      destruct (var_dec v x).
      subst. constructor.
      constructor 2. apply H0. intro. apply H1.
      apply occurs_free_Econstr.
      right.
      split; auto.
    + simpl in H1.
      destruct (var_dec v x).
      subst. constructor.
      constructor. apply H0. intro. apply H1.
      apply occurs_free_Eproj.
      right.
      split; auto.
    + simpl in H1.
      destruct (var_dec v x).
      subst. constructor. eapply Bound_Letapp2_c.
      apply H0. intro. apply H1.
      apply occurs_free_Eletapp.
      right.
      split; auto.
    + simpl in H1.
      destruct (var_dec v x).
      subst. constructor.
      constructor. apply H0. intro. apply H1.
      apply occurs_free_Eprim_val.
      split; auto.
    + simpl in H1.
      destruct (var_dec v x).
      subst. constructor.
      constructor. apply H0. intro. apply H1.
      apply occurs_free_Eprim.
      right.
      split; auto.
    + constructor. apply H0.
      intro.
      apply H1.
      simpl.
      eapply occurs_free_Ecase_Included.
      2: apply H2.
      apply in_app. right. constructor; auto.
    + simpl in H1.
      assert (Hv := Decidable_name_in_fundefs f4).
      destruct Hv. specialize (Dec x). destruct Dec.
      constructor.
      apply name_in_fundefs_bound_var_fundefs.
      auto.
      apply Bound_Fun12_c. apply H0. intro.
      apply H1.
      apply Free_Efun1; auto.
    + simpl in H1.
      constructor.
      apply H0. intro.
      apply H1.
      apply Free_Efun2.
      auto.
    + simpl in H1.
      assert (Hv := Decidable_name_in_fundefs (Fcons v t l (e0 |[ e ]|) f6)).
      destruct Hv. destruct (Dec x) as [Hin | Hnin].
      inv Hin. inv H2.
      constructor.
      constructor 4.
      apply name_in_fundefs_bound_var_fundefs. auto.
      assert (Hl := Decidable_FromList l).
      destruct Hl. destruct (Dec0 x) as [Hin | Hnin'].
      constructor 2; auto.
      constructor 3. apply H0. intro. apply H1. constructor; auto.
      intro. subst. apply Hnin. constructor. auto.
      intro. apply Hnin. constructor 2. auto.
    + simpl in H1.
      assert (Hv := Decidable_name_in_fundefs (Fcons v t l e0 (f7 <[ e ]>))).
      destruct Hv. destruct (Dec x) as [Hin | Hnin].
      inv Hin. now inv H2; eauto.
      apply Bound_Fcons24_c.
      eapply name_boundvar_ctx. eassumption.
      apply Bound_Fcons24_c.
      apply H0. intro. apply H1.
      constructor 2. apply H2.
      intro; apply Hnin. subst.
      constructor. auto.
  Qed.

  Lemma ub_find_def_nodup: forall t xs fb f fds,
      unique_bindings_fundefs fds ->
      find_def f fds = Some (t,xs,fb) ->
      NoDup xs.
  Proof.
    induction fds; intros.
    - simpl in H0.
      inv H.
      destruct (M.elt_eq f v).
      inv H0; auto.
      apply IHfds; auto.
    -           inv H0.
  Qed.

  Lemma Disjoint_bindings_fundefs: forall t f xs fb fds,
      unique_bindings_fundefs fds ->
      find_def f fds = Some (t, xs, fb) ->
      Disjoint _ (name_in_fundefs fds) (Union _ (FromList xs) (bound_var fb)).
  Proof.
    induction fds; intros.
    - simpl in H0.
      destruct (M.elt_eq f v).
      + subst.
        inv H0.
        simpl.
        inv H.
        split. intro. intro. inv H.
        inv H0.
        inv H.
        inv H1.
        apply H10; auto.
        apply H5; auto.
        inv H1.
        inv H8. specialize (H1 x). apply H1. split; auto.
        apply name_in_fundefs_bound_var_fundefs. auto.
        inv H9. specialize (H1 x). apply H1. split; auto.
        apply name_in_fundefs_bound_var_fundefs. auto.
      + inv H. simpl. specialize (IHfds H14 H0).
        apply Union_Disjoint_l; auto.
        split. intro. intro. destruct H. inv H.
        inv H1.
        apply H7.
        eapply name_boundvar_arg.
        apply H. apply H0.
        apply H7.
        eapply bv_in_find_def.
        apply H0. apply H.
    - inv H0.
  Qed.


  Lemma rw_correct e e' :
    rw e e' ->
    forall rho rho' k,
      preord_env_P cenv PG (occurs_free e) k rho rho'->
      preord_exp cenv (P1 1) PG k (e, rho) (e', rho').
  Proof.
    intros Hrw. inv Hrw.
    - intros; apply rm_constr; auto.
      eapply preord_env_P_antimon. eassumption.
      normalize_occurs_free. sets.
    - intros; apply rm_prim_val; auto.
      eapply preord_env_P_antimon. eassumption.
      normalize_occurs_free. sets.
    - intros; apply rm_prim; auto.
      eapply preord_env_P_antimon. eassumption.
      normalize_occurs_free. sets.
    - intros; apply rm_proj; auto.
      eapply preord_env_P_antimon. eassumption.
      normalize_occurs_free. sets.
    - intros; apply rm_fundefs_of; auto.
      eapply preord_env_P_antimon. eassumption.
      normalize_occurs_free. sets.
    - intros rho1 rho2 k Henv.
      inv H0. eapply fundefs_append_num_occur' in H6.
      destruct H6 as [n1 [n2 [Hn1 [Hn2 Heq_z]]]]. pi0. inv Hn2. pi0.
      apply rm_any_fundefs; auto.
      + replace 0 with (0 + (0 + 0)) by lia.
        econstructor. eassumption. eapply fundefs_append_num_occur. reflexivity.
        eassumption. eassumption.
      + eapply preord_env_P_antimon. eassumption.
        repeat normalize_occurs_free.
        rewrite fundefs_append_name_in_fundefs; [| reflexivity ].
        rewrite (fundefs_append_name_in_fundefs B1 (Fcons f t xs fb B2) (fundefs_append B1 (Fcons f t xs fb B2))); [| reflexivity ].

        simpl.
        eapply Included_Union_compat.
        * rewrite (split_fds_occurs_free_fundefs B1 B2 (fundefs_append B1 B2));
            [| now eapply fundefs_append_split_fds; eauto ].
          rewrite (split_fds_occurs_free_fundefs B1 (Fcons f t xs fb B2) (fundefs_append B1 (Fcons f t xs fb B2)));
            [| now eapply fundefs_append_split_fds; eauto ].
          repeat normalize_occurs_free. simpl.
          rewrite <- !Setminus_Union.
          rewrite !Setminus_Disjoint with (s2 := [set f]).
          now sets.

          eapply Disjoint_Singleton_r. eapply not_occurs_not_free. eassumption.
          eapply Disjoint_Singleton_r. eapply not_occurs_not_free. eassumption.
          eapply Disjoint_Singleton_r. eapply not_occurs_not_free. eassumption.
        * rewrite <- !Setminus_Union.
          rewrite !Setminus_Disjoint with (s2 := [set f]).
          now sets.

          eapply Disjoint_Singleton_r. intros Hc. inv Hc.
          eapply not_occurs_not_free in H0; eauto.
    - intros.
      eapply rw_case_equiv; eauto.
    - intros.
      eapply rw_proj_equiv; eauto.
    - intros.
      eapply rw_fun_corr; auto.
    - intros.
      eapply rw_fun_letapp_corr; eauto.
  Qed.

  Lemma gen_rw_correct e e' :
    gen_rw e e' ->
    forall rho rho' k,
      preord_env_P cenv PG (occurs_free e) k rho rho'->
      preord_exp cenv (P1 1) PG k (e, rho) (e', rho').
  Proof.
    intros H; inv H. intros.
    apply preord_exp_compat; auto.
    intros; eapply rw_correct; eauto.
  Qed.

  Context (HcompP1 : inclusion _ (comp (P1 1) (P1 1)) (P1 1))
          (HGPost' : inclusion (exp * env * fuel * trace) (comp PG PG) PG).

  (* NOTE : works only for trivial postcondition. For meaningful ones we need to compose differently *)
  Lemma gr_clos_correct n e e' :
    gr_clos n e e' ->
    forall rho rho' k,
      preord_env_P cenv PG (occurs_free e) k rho rho'->
      preord_exp cenv (P1 1) PG k (e, rho) (e', rho').
  Proof with now eauto.
    intros H.
    induction H; intros.
    - eapply preord_exp_post_monotonic.
      eapply HcompP1.
      eapply preord_exp_trans; eauto.
      eapply gen_rw_correct; try eassumption.
      intros m. eapply IHrefl_trans_closure_n.
      eapply preord_env_P_refl; eauto.
    - eapply preord_exp_refl; eauto.
  Qed.

End Shrink_correct.



Section inv_app_ctx.

  Lemma inv_app_Hole:
    forall e, e = Hole_c |[ e ]|.
  Proof. auto.
  Qed.

  Lemma inv_app_Econstr:
    forall x t  ys e,
      Econstr x t ys e = Econstr_c x t ys Hole_c  |[ e ]|.
  Proof. auto.
  Qed.

  Lemma inv_app_Eproj:
    forall x t n y e,
      Eproj x t n y e = Eproj_c x t n y Hole_c |[ e ]|.
  Proof.
    auto.
  Qed.

  Lemma inv_app_Eprim:
    forall x f ys e,
      Eprim x f ys e = Eprim_c x f ys Hole_c |[ e ]|.
  Proof.
    auto.
  Qed.

  Lemma inv_app_Ecase:
    forall x te t te' e,
      Ecase x (te ++ (t, e) :: te') = Ecase_c x te t Hole_c te' |[e]|.
  Proof.
    auto.
  Qed.


  Lemma inv_app_Fcons1:
    forall f t ys e fds,
      Fcons f t ys e fds = Fcons1_c f t ys Hole_c fds <[ e ]>.
  Proof. auto.
  Qed.


  Lemma inv_app_Fcons2:  forall z t ys e0 f e,
      (Fcons z t ys e0 (f <[ e ]>)) = (Fcons2_c z t ys e0 f) <[ e]>.
  Proof. auto.
  Qed.

  Lemma inv_app_Efun1:
    forall e fds,
      Efun fds e = Efun1_c fds Hole_c |[e]|.
  Proof. auto. Qed.

  Lemma inv_app_Efun2:  forall f e e',
      (Efun (f <[ e ]>) e') = Efun2_c f e' |[ e]|.
  Proof. auto. Qed.


End inv_app_ctx.


Lemma ub_fun_inlining: forall B1 xs fb B2 c f t vs c',
    unique_bindings (c' |[ Efun (fundefs_append B1 (Fcons f t xs fb B2)) (c |[ Eapp f t vs ]|) ]|)  ->
    unique_bindings (c' |[ Efun (fundefs_append B1 B2) (c |[ (rename_all_ns (set_list (combine xs vs) (M.empty var)) fb) ]|) ]|).
Proof.
  intros.
  apply ub_app_ctx_f.
  apply ub_app_ctx_f in H.
  destructAll.
  split; auto.
  rewrite inv_app_Efun1 in H0. rewrite app_ctx_f_fuse in H0.
  apply ub_app_ctx_f in H0.
  destructAll.
  split.

  rewrite inv_app_Efun1. rewrite app_ctx_f_fuse.
  apply ub_app_ctx_f.
  split.

  {
    simpl.
    simpl in H0. inv H0.
    constructor; eauto.
    eapply fundefs_append_unique_bindings_l in H7.
    2: reflexivity.
    destructAll.
    eapply fundefs_append_unique_bindings_r; eauto. inv H4. auto.
    eapply Disjoint_Included_r. 2: apply H5.
    rewrite bound_var_fundefs_Fcons. right; right; right;  auto.
    eapply Disjoint_Included_r. 2: apply H8.
    rewrite fundefs_append_bound_vars.
    2: reflexivity.
    intro. intros.
    rewrite fundefs_append_bound_vars.  2: reflexivity.
    inv H0. left; auto.
    right.
    rewrite bound_var_fundefs_Fcons.
    right; right; right; auto.
  }
  split.

  apply unique_bindings_rename_all_ns.
  simpl in H0. inv H0.
  eapply fundefs_append_unique_bindings_l in H7. 2: reflexivity. destructAll.
  inv H4. auto.

  simpl. rewrite bound_var_Fun1_c.
  rewrite <- bound_var_rename_all_ns.
  simpl in H0. inv H0.
  apply Union_Disjoint_l.

  rewrite fundefs_append_bound_vars.
  2: reflexivity.
  apply Union_Disjoint_l.

  eapply fundefs_append_unique_bindings_l in H7.
  2: apply reflexivity.
  destructAll.
  eapply Disjoint_Included_r. 2: apply H5. rewrite bound_var_fundefs_Fcons. right; right; left; auto.
  eapply fundefs_append_unique_bindings_l in H7.
  2: apply reflexivity.
  destructAll.
  inv H4. apply Disjoint_sym.
  auto.

  eapply Disjoint_Included_r.
  2: apply H8.
  rewrite fundefs_append_bound_vars.
  2: reflexivity.
  right. constructor 3. auto.

  eapply Disjoint_Included_r.
  2: apply H1.
  do 2 (rewrite bound_var_Efun).
  do 2 (rewrite bound_var_app_ctx).
  erewrite fundefs_append_bound_vars. 2: reflexivity.
  intro. intros.
  erewrite fundefs_append_bound_vars. 2: reflexivity.
  rewrite bound_var_fundefs_Fcons.
  inv H4. inv H5. eauto with Ensembles_DB.
  left; right; right; right; right. auto.
  inv H5.
  right. left; auto.
  left; right; right; right; left. rewrite <- bound_var_rename_all_ns in H4.  auto.
Qed.




Lemma ub_case_inl: forall c x cl e,
    (exists co, findtag cl co = Some e) ->
    unique_bindings (c |[ Ecase x cl ]|) ->
    unique_bindings (c |[ e]|).
Proof.
  intros.
  apply ub_app_ctx_f.
  apply ub_app_ctx_f in H0.
  destructAll.
  apply findtag_In in H.
  apply in_split in H.
  destructAll.
  rewrite bound_var_Ecase_app in H2.
  rewrite bound_var_Ecase_cons in H2.
  apply unique_bindings_Ecase_l in H1.
  destructAll.
  split; auto.
  split; auto.
  eapply Disjoint_Included_r.
  2: apply H2.
  right; left; auto.
Qed.


Section occurs_free_rw.

  (* for each rw e e', OF e' \subset OF e *)

  (* restricted form of occurs_free_ctx_mut to inclusion *)
  (* TODO move *)

  Lemma occurs_free_ctx_mut_included:
    (forall c e e',
        Included _ (occurs_free e) (occurs_free e') ->
        Included _ (occurs_free (c|[ e]|)) (occurs_free (c|[ e']|))) /\
    (forall fds e e',
        Included _ (occurs_free e) (occurs_free e') ->
        Included _ (occurs_free_fundefs (fds <[ e]>)) (occurs_free_fundefs (fds<[ e']>))).
  Proof with eauto with Ensembles_DB.
    exp_fundefs_ctx_induction IHc IHf; eauto; simpl;
      intros; repeat normalize_occurs_free;
        try (rewrite IHc; [| eassumption ]); try (rewrite IHB; [| eassumption ]);
          eauto with Ensembles_DB.
    rewrite name_in_fundefs_ctx...
    rewrite name_in_fundefs_ctx...
  Qed.

  Lemma occurs_free_exp_ctx_included:
    forall c e e',
      Included _ (occurs_free e) (occurs_free e') ->
      Included _ (occurs_free (c|[ e]|)) (occurs_free (c|[ e']|)).
  Proof.
    apply (proj1 occurs_free_ctx_mut_included).
  Qed.

  Lemma occurs_free_fundefs_ctx_included:
    forall fds e e',
      Included _ (occurs_free e) (occurs_free e') ->
      Included _ (occurs_free_fundefs (fds <[ e]>)) (occurs_free_fundefs (fds<[ e']>)).
  Proof.
    apply (proj2 occurs_free_ctx_mut_included).
  Qed.


  Lemma of_constr_dead: forall c x t ys e,
      num_occur e x 0 ->
      Included _ (occurs_free (c |[ e ]|)) (occurs_free (c |[ Econstr x t ys e ]|)).
  Proof.
    intros.
    apply occurs_free_exp_ctx_included.
    rewrite occurs_free_Econstr.
    apply not_occurs_not_free in H.
    eauto with Ensembles_DB.
  Qed.

  Lemma of_prim_dead: forall c x t ys e,
      num_occur e x 0 ->
      Included _ (occurs_free (c |[ e ]|)) (occurs_free (c |[ Eprim x t ys e ]|)).
  Proof.
    intros.
    apply occurs_free_exp_ctx_included.
    rewrite occurs_free_Eprim.
    apply not_occurs_not_free in H.
    eauto with Ensembles_DB.
  Qed.


  Lemma of_proj_dead: forall c x t n y e,
      num_occur e x 0 ->
      Included _ (occurs_free (c |[ e ]|)) (occurs_free (c |[ Eproj x t n y e ]|)).
  Proof.
    intros.
    apply occurs_free_exp_ctx_included.
    rewrite occurs_free_Eproj.
    apply not_occurs_not_free in H.
    eauto with Ensembles_DB.
  Qed.

  Lemma of_fun_dead: forall c fds e,
      Forall (fun v => num_occur e v 0) (all_fun_name fds) ->
      Included _ (occurs_free (c |[ e ]|)) (occurs_free (c |[ Efun fds e]|)).
  Proof.
    intros.
    apply occurs_free_exp_ctx_included.
    rewrite occurs_free_Efun.
    apply Disjoint_occurs_free_name_in_fundefs in H.
    eauto with Ensembles_DB.
  Qed.

  Lemma included_of_fundefs_append_r: forall B2 B2' B1,
      Included _ (occurs_free_fundefs B2) (occurs_free_fundefs B2') ->
      Included _ (name_in_fundefs B2') (name_in_fundefs B2) ->
      Included _ (occurs_free_fundefs (fundefs_append B1 B2)) (occurs_free_fundefs (fundefs_append B1 B2')).
  Proof.
    induction B1; intros.
    - simpl.
      repeat normalize_occurs_free.
      specialize (IHB1 H H0).
      apply Included_Union_compat.
      + apply Included_Setminus_compat.
        reflexivity.
        apply Included_Union_compat. reflexivity.
        apply Included_Union_compat. reflexivity.
        intro.
        intros.
        eapply fundefs_append_name_in_fundefs in H1.
        2: reflexivity.
        eapply fundefs_append_name_in_fundefs.
        reflexivity.
        inv H1. left; auto.
        right.
        apply H0. auto.
      + eauto with Ensembles_DB.
    - simpl. auto.
  Qed.


  (* local version *)
  Lemma of_fun_rm': forall f t xs fb B1 B2 e,
      unique_functions (fundefs_append B1 (Fcons f t xs fb B2)) ->
      num_occur (Efun (fundefs_append B1 (Fcons f t xs fb B2)) e) f 0 ->
      (occurs_free (Efun (fundefs_append B1 B2) e )) \subset
      (occurs_free (Efun (fundefs_append B1 (Fcons f t xs fb B2)) e)).
  Proof.
    intros.
    repeat normalize_occurs_free.
    rewrite fundefs_append_name_in_fundefs.
    2: reflexivity.
    rewrite fundefs_append_name_in_fundefs with (B3 := (fundefs_append B1 (Fcons f t xs fb B2))).
    2: reflexivity.
    simpl.

    inv H0. apply Nat.eq_add_0 in H3. destruct H3. subst.
    apply fundefs_append_num_occur' in H6.
    destructAll.
    apply Nat.eq_add_0 in H2. destructAll.


    inv H1. apply Nat.eq_add_0 in H10.
    destructAll.
    apply not_occurs_not_free in H5.
    apply not_occurs_not_free in H11.
    apply not_occurs_not_free in H9.

    apply Included_Union_compat.

    {
      clear H.
      induction B1.
      + inv H0; pi0.
        specialize (IHB1 H10).
        simpl.
        repeat normalize_occurs_free.
        apply Included_Union_compat.
        rewrite fundefs_append_name_in_fundefs.
        2: reflexivity.
        rewrite fundefs_append_name_in_fundefs with (B3 := (fundefs_append B1 (Fcons f t xs fb B2))).
        2: reflexivity.
        simpl.
        apply not_occurs_not_free in H7.
        repeat (rewrite <- Setminus_Union).
        apply Included_Setminus_compat.
        apply Included_Setminus.
        apply Setminus_Disjoint_preserv_l.
        apply Setminus_Disjoint_preserv_l.
        apply Setminus_Disjoint_preserv_l.
        eauto with Ensembles_DB.
        reflexivity.
        reflexivity.
        eauto with Ensembles_DB.
      + simpl.
        normalize_occurs_free.
        eauto with Ensembles_DB.
    }

    apply not_occurs_not_free in H0.
    eauto 25 with Ensembles_DB.
  Qed.

  Lemma of_fun_rm:  forall c f t xs fb B1 B2 e,
      unique_bindings_fundefs (fundefs_append B1 (Fcons f t xs fb B2)) ->
      num_occur (Efun (fundefs_append B1 (Fcons f t xs fb B2)) e) f 0 ->
      Included _ (occurs_free (c |[ Efun (fundefs_append B1 B2) e  ]| )) (occurs_free (c |[ (Efun (fundefs_append B1 (Fcons f t xs fb B2)) e) ]|)).
  Proof.
    intros.
    apply occurs_free_exp_ctx_included.
    apply of_fun_rm'; auto.
    eapply unique_bindings_fundefs_unique_functions; eauto.
  Qed.


  Lemma of_case_fold': forall x cl co e,
      findtag cl co = Some e ->
      Included _ (occurs_free e) (occurs_free (Ecase x cl)).
  Proof.
    intros.
    eapply occurs_free_Ecase_Included.
    apply findtag_In_patterns.
    eauto.
  Qed.


  Lemma name_in_fundefs_rename_all_ns:
    forall sig f,
      name_in_fundefs f <--> name_in_fundefs (rename_all_fun_ns sig f).
  Proof.
    induction f; simpl; eauto with Ensembles_DB.
  Qed.

  Lemma remove_all_some:
    forall x y l sigma,
      M.get x (remove_all sigma l) = Some y ->
      ~ (FromList l x).
  Proof.
    induction l.
    - intros. intro. inv H0.
    - simpl. intros s Hget Hc. destruct (peq a x); subst; inv Hc; try contradiction.
      rewrite M.grs in Hget. congruence.
      rewrite M.grs in Hget. congruence.
      rewrite M.gro in Hget. eapply IHl; eauto.
      eauto.
  Qed.

  Lemma Dom_map_remove_all: forall l sigma ,
      Same_set _ (Dom_map (remove_all sigma l))
               (Setminus _ (Dom_map sigma) (FromList l)).
  Proof.
    split; intro; intro.
    inv H.
    assert (~ (FromList l x)) by apply (remove_all_some _ _ _ _ H0).
    split; auto.
    rewrite <- not_in_remove_all in H0; auto.
    exists x0; auto.
    inv H.
    inv H0.
    exists x0.
    rewrite <- not_in_remove_all; auto.
  Qed.

  Lemma Range_map_remove_all : forall l sigma ,
      Included _ (Range_map (remove_all sigma l))
               (Range_map sigma).
  Proof.
    induction l; intros.
    simpl. reflexivity.
    simpl. eapply Included_trans.
    apply Range_map_remove.
    apply IHl.
  Qed.



  Lemma of_rename_all_ns_mut:
    (forall e sigma, (occurs_free (rename_all_ns sigma e)) \subset
                     ((occurs_free e) \\ (Dom_map sigma)) :|: (Range_map sigma)) /\
    (forall fds sigma, (occurs_free_fundefs (rename_all_fun_ns sigma fds)) \subset
                       ((occurs_free_fundefs fds) \\ (Dom_map sigma)) :|: (Range_map sigma)).
  Proof.
    apply exp_def_mutual_ind; intros.
    - simpl.
      repeat normalize_occurs_free.
      apply Union_Included.
      + eapply Included_trans.
        apply FromList_apply_r_list.
        eauto with Ensembles_DB.
      + apply Setminus_Included_Included_Union.
        eapply Included_trans.
        apply H.
        intro.
        intros. inv H0.
        destruct (var_dec x v).
        * subst. right. constructor.
        * inv H1.
          left. left. split.
          right. split; auto.
          intro. apply n; inv H1.
          auto.
          auto.
        * auto.
    - simpl.
      repeat normalize_occurs_free.
      intro. intros.
      inv H.
      apply apply_r_sigma_in.
    - simpl.
      repeat normalize_occurs_free.
      specialize (H sigma).
      specialize (H0 sigma).
      repeat (apply Union_Included).
      + eapply Included_trans.
        intro; intro.
        inv H1.
        apply apply_r_sigma_in.
        eauto with Ensembles_DB.
      + eapply Included_trans.
        apply H.
        eauto with Ensembles_DB.
      + eapply Included_trans.
        apply H0.
        eauto with Ensembles_DB.
    - simpl.
      repeat normalize_occurs_free.
      apply Union_Included.
      + eapply Included_trans.
        intro. intro. inv H0.
        apply apply_r_sigma_in.
        eauto with Ensembles_DB.
      + apply Setminus_Included_Included_Union.
        eapply Included_trans.
        apply H.
        intro.
        intros. inv H0.
        destruct (var_dec x v).
        * subst. right. constructor.
        * inv H1.
          left. left. split.
          right. split; auto.
          intro. apply n0; inv H1.
          auto.
          auto.
        * eauto.
    - simpl.
      repeat normalize_occurs_free.
      apply Union_Included.
      + eapply Included_trans.
        eapply Included_Union_compat.
        eapply Singleton_Included. apply apply_r_sigma_in.
        apply FromList_apply_r_list.
        rewrite !Setminus_Union_distr.
        eapply Union_Included. now sets.
        now sets.
      + apply Setminus_Included_Included_Union.
        eapply Included_trans. apply H.
        rewrite Setminus_Union_distr, Setminus_Union.
        rewrite (Union_commut [set x]), <- Setminus_Union.
        rewrite <- !Union_assoc.
        rewrite <- (Union_Included_Union_Setminus) with (s3 := [set x]); tci; sets.
    - simpl.
      repeat normalize_occurs_free.
      apply Union_Included.
      + eapply Included_trans.
        apply H.
        eauto with Ensembles_DB.
      + apply Setminus_Included_Included_Union.
        eapply Included_trans.
        apply H0.
        apply Union_Included.
        * intro. intro.
          inv H1.
          assert (Hh := Decidable_name_in_fundefs f2).
          inv Hh. specialize (Dec x).
          destruct Dec.
          right.
          apply name_in_fundefs_rename_all_ns. auto.
          left.  left. split. right. split; auto.
          intro; apply H3.
          auto.
        * left; right.
          auto.
    - simpl.
      repeat normalize_occurs_free.
      apply Union_Included.
      eapply Included_trans.
      apply FromList_apply_r_list.
      eauto with Ensembles_DB.
      eapply Included_trans.
      intro. intro. inv H.
      apply apply_r_sigma_in.
      eauto with Ensembles_DB.
    -  simpl.
      repeat normalize_occurs_free.
      apply Setminus_Included_Included_Union.
      eapply Included_trans.
      apply H.
      intro.
      intros. inv H0.
      destruct (var_dec x v).
      * subst. right. constructor.
      * inv H1.
        left. left. split.
        split; auto.
        intro. apply n; inv H1.
        auto.
        intro.
        apply H2.
        auto.
      * eauto.
    -  simpl.
       repeat normalize_occurs_free.
       apply Union_Included.
       + eapply Included_trans.
         apply FromList_apply_r_list.
         eauto with Ensembles_DB.
       + apply Setminus_Included_Included_Union.
         eapply Included_trans.
         apply H.
         intro.
         intros. inv H0.
         destruct (var_dec x v).
         * subst. right. constructor.
         * inv H1.
           left. left. split.
           right. split; auto.
           intro. apply n; inv H1.
           auto.
           intro.
           apply H2.
           auto.
         * eauto.
    - simpl.
      rewrite occurs_free_Ehalt.
      rewrite occurs_free_Ehalt.
      intro. intro. inv H. apply apply_r_sigma_in.
    - simpl.
      repeat normalize_occurs_free.

      apply Union_Included.
      + intro. intro. inv H1. apply H in H2.
        inv H2.
        left. inv H1.
        split.
        left. split; auto.
        intro.
        inv H1. apply H3; auto.
        rewrite <- name_in_fundefs_rename_all_ns in H3.
        apply H3; auto.
        auto.
        right.
        auto.
      + intro. intro. inv H1.
        apply H0 in H2.
        inv H2.
        inv H1. left.
        split; auto.
        right. split; auto.
        auto.
    - simpl.
      intro. intro. inv H.
  Qed.

  Lemma Dom_map_set_lists_ss: forall xs vs,
      List.length xs = List.length vs ->
      Same_set _  (Dom_map (set_list (combine xs vs) (M.empty var)))
               (FromList xs).
  Proof.
    induction xs.
    - intros. split.
      simpl.
      intro. intro. inv H.
      inv H0.
      rewrite M.gempty in H. inv H.
      intro. intro. inv H0.
    - intros. simpl. simpl in H. destruct vs.
      inv H.
      simpl in H.
      inv H. apply IHxs in H1.
      split.
      intro. intro. inv H.
      rewrite FromList_cons.
      simpl in H0.
      destruct (var_dec a x).
      subst. left; auto.
      right.
      apply H1.
      rewrite M.gso in H0 by auto.
      exists x0.
      apply H0.
      intro. intros.
      destruct (var_dec a x).
      subst.
      simpl. exists v. apply M.gss.
      inv H.
      exfalso; auto.
      apply H1 in H0. simpl.
      inv H0.
      exists x0. rewrite M.gso; auto.
  Qed.


  Lemma of_fun_inline':
    forall f fds t xs fb vs,
      find_def f fds = Some (t, xs, fb) ->
      List.length xs = List.length vs ->
      (Setminus var
                (occurs_free
                   (rename_all_ns (set_list (combine xs vs) (M.empty var)) fb))
                (name_in_fundefs fds)) \subset
                                       Union var (occurs_free_fundefs fds)
                                       (Setminus var (occurs_free ( Eapp f t vs)) (name_in_fundefs fds)).
  Proof.
    intros.
    eapply Included_trans.
    eapply Included_Setminus_compat.
    apply of_rename_all_ns_mut.
    reflexivity.
    eapply Included_trans.
    apply Setminus_Union_distr.
    apply find_def_free_included in H.
    apply Union_Included.
    - eapply Included_trans.
      rewrite Dom_map_set_lists_ss; auto.
      apply H.
      left; auto.
    - apply Setminus_Included_Included_Union.
      eapply Included_trans.
      apply Range_map_set_list.
      rewrite occurs_free_Eapp.
      intro. intro.
      assert (Hh := Decidable_name_in_fundefs fds).
      destruct Hh.
      destruct (Dec x) as [Hin | Hnin].
      right; auto.
      left. right.
      split.
      left; auto.
      apply Hnin.
  Qed.


  Lemma of_fun_inline'':
    forall f fds t xs fb vs,
      find_def f fds = Some (t, xs, fb) ->
      List.length xs = List.length vs ->
      Union var
            (occurs_free
               (rename_all_ns (set_list (combine xs vs) (M.empty var)) fb))
            (Union var
                   (name_in_fundefs fds)
                   (occurs_free_fundefs fds))
            \subset
            Union var (occurs_free ( Eapp f t vs))
            (Union var (name_in_fundefs fds)
                   (occurs_free_fundefs fds))
  .
  Proof.
    intros.
    assert (Hofi := of_fun_inline' f fds t xs fb vs H H0).
    rewrite Union_assoc.
    rewrite Union_assoc.
    apply Union_Included.
    - rewrite Union_Setminus.
      apply Union_Included.
      eapply Included_trans. apply Hofi.
      eauto with Ensembles_DB.
      eauto with Ensembles_DB.
      apply Decidable_name_in_fundefs.
    - right; auto.
  Qed.


  Lemma occurs_free_ctx_mut_included_u:
    forall S,
      Decidable S ->
      (forall c e e',
          Included _ (Union _ (occurs_free e) S) (Union _ (occurs_free e') S) ->
          Included _ (Union _ (occurs_free (c|[ e]|)) S)  (Union _ (occurs_free (c|[ e']|)) S)) /\
      (forall fds e e',
          Included _ (Union _ (occurs_free e) S) (Union _ (occurs_free e') S) ->
          Included _ (Union _ (occurs_free_fundefs (fds <[ e]>)) S)  (Union _ (occurs_free_fundefs (fds<[ e']>)) S)).
  Proof with eauto with Ensembles_DB.
    intros S Hds.
    exp_fundefs_ctx_induction IHc IHf; eauto; simpl;
      intros; repeat normalize_occurs_free;
        try (rewrite IHc; [| eassumption ]); try (rewrite IHB; [| eassumption ]);
          try (
              apply IHc in H;
              rewrite <- Union_assoc;
              rewrite <- Union_assoc;
              rewrite Union_Setminus_Setminus_Union; [|auto];
              rewrite Union_Setminus_Setminus_Union; [|auto];
              eauto with Ensembles_DB).
    { apply IHc in H.
      repeat (rewrite <- Union_assoc).
      repeat (rewrite Union_Setminus_Setminus_Union; [|auto]).
      apply Included_Union_compat; [reflexivity|].
      apply Included_Union_compat; [reflexivity|].
      eapply Included_Setminus_compat; [| reflexivity ]. eassumption.
    }
    { apply IHc in H.
      rewrite Union_Setminus_Setminus_Union; [|auto].
      rewrite Union_Setminus_Setminus_Union; [|auto].
      now eapply Included_Setminus_compat; [|reflexivity]. }
    { apply IHc in H.
      repeat (rewrite <- Union_assoc).
      apply Included_Union_compat; [reflexivity|].
      apply Included_Union_compat; [reflexivity|].
      intro. intro. inv H0.
      eapply Included_Union_l in H1. apply H in H1.
      inv H1. auto. auto.
      inv H1.
      auto.
      eapply Included_Union_r in H0. apply H in H0.
      inv H0; auto.
    }
    {
      apply IHf in H.
      rewrite name_in_fundefs_ctx with (e2 := e').
      do 2 (rewrite Union_commut with (s2 := S)).
      do 2 (rewrite  Union_assoc).
      do 2 (rewrite Union_commut with (s1 := S)).
      eauto with Ensembles_DB.
    }
    {
      apply IHc in H.
      do 2 (rewrite Union_commut with (s2 := S)).
      rewrite Union_assoc.
      rewrite Union_assoc with (s1 := S).

      rewrite Union_commut with (s1 := S).
      rewrite Union_commut with (s1 := S).
      rewrite Union_Setminus_Setminus_Union.
      rewrite Union_Setminus_Setminus_Union with (s3 := S).
      eauto with Ensembles_DB.
      auto.
      auto.
    }
    {
      apply IHf in H.
      rewrite name_in_fundefs_ctx with (e2 := e').


      do 2 (rewrite Union_commut with (s2 := S)).
      do 2 (rewrite Union_commut with (s1 := (Setminus var (occurs_free e)
                                                       (Union var [set v]
                                                              (Union var (FromList l) (name_in_fundefs (f7 <[ e' ]>))))))).
      rewrite Union_assoc.
      rewrite Union_assoc with (s1 := S).
      rewrite Union_commut with (s1 := S).
      rewrite Union_commut with (s1 := S).
      rewrite Union_Setminus_Setminus_Union.
      rewrite Union_Setminus_Setminus_Union with (s3 := S).
      eauto with Ensembles_DB.
      auto.
      auto.
    }
  Qed.

  (* todo: move *)
  Lemma nthN_FromList {A} k ys n :
      nthN ys n = Some k ->
      @FromList A ys k.
  Proof.
    intros Hnth. eapply nthN_In. eassumption.
  Qed.

  Lemma occurs_free_exp_ctx_included_u:
    forall c e e' S,
      Decidable S ->
      Included _ (Union _ (occurs_free e) S) (Union _ (occurs_free e') S) ->
      Included _ (Union _ (occurs_free (c|[ e]|)) S) (Union _ (occurs_free (c|[ e']|)) S).
  Proof.
    intros.
    apply occurs_free_ctx_mut_included_u; auto.
  Qed.

  Lemma of_case_fold: forall c' c x cl  e ys co,
      findtag cl co = Some e ->
      Included _ (occurs_free (c' |[ Econstr x co ys (c |[ e ]|) ]|)) (occurs_free (c' |[Econstr x co ys (c |[Ecase x cl]|) ]|)) .
  Proof.
    intros.
    apply occurs_free_exp_ctx_included.
    do 2 (rewrite inv_app_Econstr).
    do 2 (rewrite app_ctx_f_fuse).
    apply occurs_free_exp_ctx_included.
    eapply occurs_free_Ecase_Included.
    apply findtag_In_patterns. apply H.
  Qed.






  Lemma of_fun_inline''':
    forall xs vs fb t c f fds,
      find_def f fds = Some (t, xs, fb) ->
      List.length xs = List.length vs ->
      Included _ (occurs_free (Efun fds (c |[ (rename_all_ns (set_list (combine xs vs) (M.empty var)) fb)]|)))
               (occurs_free (Efun fds (c |[ Eapp f t vs ]|))).
  Proof.
    intros.
    repeat normalize_occurs_free.
    apply Union_Included.
    - left; auto.
    - assert (Hofi := of_fun_inline'' f fds t xs fb vs H H0).
      eapply occurs_free_exp_ctx_included_u with (c  := c) in Hofi.
      intro. intro.
      inv H1.
      assert (In var (Union var
                            (occurs_free
                               (c |[ rename_all_ns (set_list (combine xs vs) (M.empty var)) fb ]|))
                            (Union var (name_in_fundefs fds) (occurs_free_fundefs fds))) x).
      left. auto.
      apply Hofi in H1.
      inv H1. right. split; auto.
      inv H4.
      exfalso; auto.
      left; auto.
      apply Decidable_Union.
      apply Decidable_name_in_fundefs.
      apply occurs_free_dec_fundefs.
  Qed.



  Lemma of_constr_proj':
    forall x t ys c k v e n t',
      nthN ys n = Some k  ->
      Included _
               (occurs_free (Econstr x t ys (c |[rename_all_ns (M.set v k (M.empty var)) e]|)))
               (occurs_free (Econstr x t ys (c |[Eproj v t' n x e]|))).
  Proof.
    intros.
    repeat normalize_occurs_free.
    assert (Included _ (Union _ (occurs_free (c |[ rename_all_ns (M.set v k (M.empty var)) e ]|)) [set k])
                     (Union _ (occurs_free (c |[ Eproj v t' n x e ]|)) [set k])).
    eapply occurs_free_exp_ctx_included_u with (c  := c).
    split. intro. destruct (var_dec k x0); subst.
    left; constructor. right.
    intro; apply n0; auto. inv H0; auto.
    normalize_occurs_free.
    unfold rename.
    apply Union_Included.
    eapply Included_trans.

    apply of_rename_all_ns_mut.
    intro.
    intro. inv H0.
    inv H1.
    left.
    right.
    split.
    auto.
    intro.
    apply H2.
    inv H1.
    exists k.
    rewrite M.gss.
    auto.
    inv H1.
    destruct (var_dec x1 v).
    subst.
    rewrite M.gss in H0. inv H0.
    right. auto.
    rewrite M.gso in H0.
    rewrite M.gempty in H0.
    inv H0.
    auto.
    right; auto.
    intro.
    intro. inv H1.
    left; auto.
    destruct (var_dec x0 k).
    - subst. left. eapply nthN_FromList. eauto.
    - inv H2.
      right.
      split; auto.
      eapply Included_Union_l in H1.
      apply H0 in H1.
      inv H1. auto.
      exfalso.
      apply n0. inv H2. auto.
  Qed.



End occurs_free_rw.

Section Shrink_Rewrites.

  (* shrink rewrites, with rewrite step count -- useful for cost counting *)
  Inductive sr_rw : nat -> relation exp :=
  (* Rules about dead var elimination *)
  | Constr_dead_s: forall x t ys e,
      num_occur e x 0 ->
      sr_rw 1 (Econstr x t ys e) e
  | Prim_dead_s: forall x p ys e,
      num_occur e x 0 ->
      sr_rw 1 (Eprim x p ys e) e
  | Proj_dead_s: forall x t n y e,
      num_occur e x 0 ->
      sr_rw 1 (Eproj x t n y e) e
  | Fun_dead_s: forall e fds,
      Forall (fun v => num_occur e v 0) (all_fun_name fds) ->
      sr_rw 1 (Efun fds e) e
  | Fun_rem_s: forall f t xs fb B1 B2 e,
      num_occur (Efun (fundefs_append B1 (Fcons f t xs fb B2)) e) f 0 ->
      sr_rw 0 (Efun (fundefs_append B1 (Fcons f t xs fb B2)) e) (Efun (fundefs_append B1 B2) e)
  (* Rules about inlining/constant-folding *)
  | Constr_case_s: forall x c cl co e ys n,
      find_tag_nth cl co e n ->
      sr_rw 1 (Econstr x co ys (c |[ Ecase x cl ]|)) (Econstr x co ys (c |[e]|))
  | Constr_proj_s: forall v  t t' n x e k ys c,
      nthN ys n = Some k ->
      sr_rw 1 (Econstr x t ys (c |[Eproj v t' n x e]|)) (Econstr x t ys (c |[ rename_all_ns (M.set v k (M.empty var)) e]|))
  | Fun_inline_s: forall c  vs f  t xs fb  B1 B2,
      List.length xs = List.length vs ->
      num_occur (Efun (fundefs_append B1 (Fcons f t xs fb B2)) (c |[ Eapp f t vs ]|)) f 1 ->
      sr_rw 1 (Efun (fundefs_append B1 (Fcons f t xs fb B2)) (c |[ Eapp f t vs ]|))
            (Efun (fundefs_append B1 B2) (c |[ (rename_all_ns (set_list (combine xs vs) (M.empty var)) fb)]|))
  | Fun_inline_letapp_s: forall c  vs x f  t xs e1 fb B1 B2 C' x',
      List.length xs = List.length vs ->
      num_occur (Efun (fundefs_append B1 (Fcons f t xs fb B2)) (c |[ Eletapp x f t vs e1 ]|)) f 1 ->
      inline_letapp (rename_all_ns (set_list (combine xs vs) (M.empty var)) fb) x = Some (C', x') ->
      sr_rw 1 (Efun (fundefs_append B1 (Fcons f t xs fb B2)) (c |[ Eletapp x f t vs e1 ]|))
            (Efun (fundefs_append B1 B2) (c |[ C' |[ rename_all_ns (M.set x x' (M.empty _)) e1 ]|  ]|)).

  Inductive gen_sr_rw (n : nat) : relation exp :=
  | Ctx_sr_rw : forall c e e',
      sr_rw n e e' ->
      gen_sr_rw n (c |[ e ]|) (c |[ e' ]|).


  Inductive gsr_clos : nat -> relation exp :=
  | Trans_srw :
      forall n m e1 e2 e3,
        gen_sr_rw n e1 e2 ->
        gsr_clos m e2 e3 ->
        gsr_clos (n + m) e1 e3
  | Refl_srw :
      forall e,
        gsr_clos 0 e e.

  Local Hint Constructors rw : core.

  Lemma Disjoint_dom_map :
    forall (sig:M.t M.elt) S,
      Disjoint _ (Dom_map sig) S ->
      forall (x:M.elt), In _ S x ->
                   M.get x sig  = None.
  Proof.
    intros. inv H. destruct (M.get x sig) eqn:gxs.
    exfalso. specialize (H1 x). apply H1. split; eauto.
    exists e. auto.
    auto.
  Qed.

  Notation "A =mg= B" := (map_get_r _ A B) (at level 81).

  Lemma Not_In_dom_remove A x (sig : M.t A) :
      ~ x \in (Dom_map sig) ->
      M.remove x sig =mg= sig.
  Proof.
    intros Hnin z. destruct (peq z x); subst.
    - rewrite M.grs. unfold Dom_map, In in *.
      destruct (sig ! x); eauto. exfalso. eauto.
    - rewrite M.gro; eauto.
  Qed.

  Lemma Disjoint_dom_remove_all:
    forall l sig,
      Disjoint _ (Dom_map sig) (FromList l) ->
      remove_all sig l =mg= sig.
  Proof.
    induction l; simpl; intros.
    - apply smg_refl.
    - eapply smg_trans; [| apply IHl ]; [| now normalize_sets; sets ].
      eapply Not_In_dom_remove.
      intros Hc. eapply H; eauto. normalize_sets. constructor; eauto.
      destruct Hc. rewrite IHl in H0. eexists. eassumption.
      normalize_sets. sets.
  Qed.

  (** If the substitution is not shadowed in e, we can replace rename_all by
     rename_all_ns which does not consider variable captures *)
  Lemma Disjoint_dom_rename_all_eq:
    forall sig,
      (forall e,
          Disjoint _ (Dom_map sig) (bound_var e) ->
          rename_all sig e = rename_all_ns sig e) /\
      (forall fds,
          Disjoint _ (Dom_map sig) (bound_var_fundefs fds) ->
          rename_all_fun sig fds = rename_all_fun_ns sig fds).
  Proof with (eauto with Ensembles_DB).
    intro sig.
    apply exp_def_mutual_ind; intros; repeat normalize_bound_var_in_ctx; simpl.
    - rewrite <- H.
      erewrite (proj1 prop_rename_all).
      reflexivity.
      apply remove_none.
      eapply Disjoint_dom_map. apply H0. auto.
      eapply Disjoint_Included_r...
    - reflexivity.
    - rewrite H.
      assert ( Disjoint M.elt (Dom_map sig) (bound_var (Ecase v l)))...
      apply H0 in H2. simpl in H2.
      inv H2. reflexivity.
      eapply Disjoint_Included_r...
    - rewrite <- H.
      erewrite (proj1 prop_rename_all).
      reflexivity.
      apply remove_none.
      eapply Disjoint_dom_map...
      eapply Disjoint_Included_r...
    - rewrite <- H.
      erewrite (proj1 prop_rename_all).
      reflexivity.
      apply remove_none.
      eapply Disjoint_dom_map. apply H0. auto.
      eapply Disjoint_Included_r...
    - rewrite <- H0...
      rewrite <- H...
      erewrite (proj1 prop_rename_all).
      erewrite (proj2 prop_rename_all).
      reflexivity.
      apply Disjoint_dom_remove_all. rewrite <- Same_set_all_fun_name. eapply Disjoint_Included_r.
      apply name_in_fundefs_bound_var_fundefs. auto...
      apply Disjoint_dom_remove_all. rewrite <- Same_set_all_fun_name. eapply Disjoint_Included_r.
      apply name_in_fundefs_bound_var_fundefs. auto...
    - reflexivity.
    - rewrite <- H...
      erewrite (proj1 prop_rename_all).
      reflexivity.
      apply remove_none.
      eapply Disjoint_dom_map...
    - rewrite <- H...
      erewrite (proj1 prop_rename_all).
      reflexivity.
      apply remove_none.
      eapply Disjoint_dom_map...
    - reflexivity.
    - rewrite <- H...
      rewrite <- H0...
      erewrite (proj1 prop_rename_all).
      reflexivity.
      apply Disjoint_dom_remove_all...
    - reflexivity.
  Qed.


  Lemma occurs_free_ctx_not_bound:
    forall (x : var) (e : exp),
      occurs_free e x ->
      (forall c : exp_ctx, ~ bound_var_ctx c x ->  occurs_free (c |[ e ]|) x).
  Proof.
    intros.
    destruct (occurs_free_dec_exp (c |[ e ]|)).
    specialize (Dec x).
    inv Dec; auto.
    exfalso.
    apply H0.
    eapply occurs_free_app_bound_var; eauto.
  Qed.

  Lemma occurs_free_fundefs_ctx_not_bound:
    forall (x : var) (e : exp),
      occurs_free e x ->
      (forall fds : fundefs_ctx,
          ~ bound_var_fundefs_ctx fds x -> occurs_free_fundefs (fds <[ e ]>) x).
  Proof.
    intros.
    destruct (occurs_free_dec_fundefs (fds <[ e ]>)).
    specialize (Dec x).
    inv Dec; auto.
    exfalso.
    apply H0.
    eapply occurs_free_app_bound_var; eauto.
  Qed.

  Lemma Disjoint_bv_of_ctx:
    forall c e,
      unique_bindings (c |[ e]|) ->
      Disjoint _ (bound_var (c |[ e]|)) (occurs_free (c |[ e]|)) ->
      Disjoint _ (bound_var e) (occurs_free e).
  Proof.
    intros.
    split. intro. intro.
    destruct H1.
    destruct (bound_var_ctx_dec c).
    destruct (Dec x) as [Hin | Hnin].
    apply ub_app_ctx_f in H; destructAll.
    inv H4. specialize (H5 x). auto.
    inv H0. specialize (H3 x).
    apply H3.
    split. apply bound_var_app_ctx; auto.
    apply occurs_free_ctx_not_bound; auto.
  Qed.


  Lemma num_occur_list_not_dom: forall f sigma,
      ~ (Dom_map sigma f) ->
      forall l,
        num_occur_list l f <= num_occur_list (apply_r_list sigma l) f.
  Proof.
    induction l; auto.
    simpl.
    destruct (term_util.var_dec f a).
    unfold apply_r.
    subst.
    destruct (M.get a sigma) eqn:gas.
    exfalso.
    apply H. exists v; auto.
    destruct (term_util.var_dec a a). lia.
    exfalso; apply n. auto.
    destruct (term_util.var_dec f (apply_r sigma a)); lia.
  Qed.

  Lemma num_occur_list_not_range: forall f sigma,
      ~ (Range_map sigma f) ->
      forall l,
        num_occur_list (apply_r_list sigma l) f  <= num_occur_list l f.
  Proof.
    induction l.
    - simpl. reflexivity.
    - simpl.
      destruct (term_util.var_dec f a).
      + subst.
        destruct (term_util.var_dec a (apply_r sigma a)); lia.
      + destruct (term_util.var_dec f (apply_r sigma a)).
        * exfalso. apply H.
          exists a.
          unfold apply_r in e.
          destruct  (Maps.PTree.get a sigma).
          subst; auto.
          exfalso; apply n; auto.
        * lia.
  Qed.

  Local Hint Constructors num_occur num_occur_fds num_occur_case num_occur_ec num_occur_fdc : core.

  (** If a variable is not in the range of a substitution, applying the
substitution to a term cannot increase the occurence count for that variable. *)
  Lemma num_occur_rename_all_not_range_mut:
    forall f,
      ( forall e m n sigma,
          num_occur e f m ->
          num_occur (rename_all sigma e) f n  ->
          ~ Range_map sigma f ->
          n <= m) /\
      ( forall fds m n sigma,
          num_occur_fds fds f m ->
          num_occur_fds (rename_all_fun sigma fds) f n  ->
          ~ Range_map sigma f ->
          n <= m).
  Proof.
    intro f.
    apply exp_def_mutual_ind; intros.
    - simpl in H1. inv H1.
      inv H0.
      specialize (H _ _ _  H8 H9).
      apply Nat.add_le_mono.
      apply H. intro. apply H2.
      apply Range_map_remove in H0. auto.
      apply num_occur_list_not_range. auto.
    - simpl in H0. inv H0.
      inv H6. inv H.
      inv H5.
      apply Nat.add_le_mono.
      assert (Hll := num_occur_list_not_range _ _ H1 ([v])).
      simpl in Hll.    auto.
      auto.
    - simpl in H2. inv H1. inv H2. inv H8. inv H7.
      replace (num_occur_list [v] f + (n + m)) with
          (n + (num_occur_list [v] f + m)) by lia.
      replace ((num_occur_list (@cons var (apply_r sigma v) (@nil var)) f) + (n0 + m0)) with
          (n0 + (num_occur_list (@cons var (apply_r sigma v) (@nil var)) f + m0)) by lia.
      apply Nat.add_le_mono.
      eapply H; eauto.
      eapply H0; eauto.
      simpl. constructor.
      auto.

    - simpl in H1. inv H1.
      inv H0.
      specialize (H _ _ _ H9 H10).
      apply Nat.add_le_mono.
      assert (Hll := num_occur_list_not_range _ _ H2 ([v0])).
      simpl in Hll.    auto.
      apply H. intro; apply H2.
      apply Range_map_remove in H0.
      auto.
    - inv H1. inv H0.
      assert (Hll := num_occur_list_not_range _ _ H2 (f0::ys)).
      apply Nat.add_le_mono. eassumption.
      eapply H. eassumption. eassumption. intros Hc.
      apply Range_map_remove in Hc. auto.
    - inv H1.
      simpl in H2. inv H2.
      apply Nat.add_le_mono.
      eapply H0; eauto.
      intro; apply H3.
      apply Range_map_remove_all in H1.
      auto.
      eapply H; eauto.
      intro.
      apply H3.
      apply Range_map_remove_all in H1.
      auto.
    - inv H. inv H0.
      assert (Hll := num_occur_list_not_range _ _ H1 (v::l)).
      auto.
    - inv H0. inv H1.
      assert (Hll := num_occur_list_not_range _ _ H2 ([v])).
      eapply H; eauto.
      intro; apply H2.
      apply (@Range_map_remove var) in H0. auto.
    - inv H0; inv H1.
      apply Nat.add_le_mono.
      eapply H; eauto.
      intro; apply H2.
      apply (@Range_map_remove var) in H0. auto.
      apply num_occur_list_not_range; auto.
    - inv H; inv H0.
      assert (Hll := num_occur_list_not_range _ _ H1 ([v])).
      auto.
    - inv H1; inv H2.
      apply Nat.add_le_mono.
      eapply H; eauto.
      intro; apply H3.
      apply Range_map_remove_all in H1. auto.
      eapply H0; eauto.
    - inv H; inv H0. auto.
  Qed.

  Lemma num_occur_rename_all_not_range:
    forall f,
      ( forall e m n sigma,
          num_occur e f m ->
          num_occur (rename_all sigma e) f n  ->
          ~ Range_map sigma f ->
          n <= m).
  Proof.
    apply num_occur_rename_all_not_range_mut.
  Qed.


  Lemma num_occur_rename_all_ns_not_range_mut:
    forall f sigma,
      ~ Range_map sigma f ->
      ( forall e m n,
          num_occur e f m ->
          num_occur (rename_all_ns sigma e) f n  ->
          n <= m) /\
      ( forall fds m n,
          num_occur_fds fds f m ->
          num_occur_fds (rename_all_fun_ns sigma fds) f n  ->
          n <= m).
  Proof.
    intros f sig Hs.
    apply exp_def_mutual_ind; simpl; intros.
    - inv H0; inv H1.
      specialize (H _ _ H8 H7).
      assert (Hnn := num_occur_list_not_range _ _ Hs l).
      lia.
    - inv H; inv H0.
      inv H5; inv H4.
      rewrite Nat.add_0_r.
      rewrite Nat.add_0_r.
      apply (num_occur_list_not_range _ _ Hs [v]).
    - inv H1. inv H2.
      inv H7. inv H6.
      specialize (H _ _ H8 H7).
      assert (  num_occur_list [apply_r sig v] f + m0 <=
                num_occur_list [v] f + m).
      eapply H0. constructor; auto. constructor; auto.
      simpl in *. lia.
    - inv H0; inv H1.
      specialize (H _ _ H9 H8).
      assert (Hnn := num_occur_list_not_range _ _ Hs [v0]).
      simpl in *. lia.
    - inv H0; inv H1.
      specialize (H _ _ H9 H8).
      assert (Hnn := num_occur_list_not_range _ _ Hs (f0 :: ys)).
      simpl in *; lia.
    - inv H1; inv H2.
      specialize (H _ _ H8 H9).
      specialize (H0 _ _ H5 H4).
      lia.
    - inv H; inv H0.
      apply (num_occur_list_not_range _ _ Hs (v::l)).
    - inv H0; inv H1.
      specialize (H _ _ H7 H6).
      assert (Hnn := num_occur_list_not_range _ _ Hs [v]).
      lia.
    - inv H0; inv H1.
      specialize (H _ _ H8 H7).
      assert (Hnn := num_occur_list_not_range _ _ Hs l).
      lia.
    - inv H; inv H0.
      apply (num_occur_list_not_range _ _ Hs [v]).
    - inv H1; inv H2.
      specialize (H _ _ H10 H9).
      specialize (H0 _ _ H11 H12).
      lia.
    - inv H; inv H0; auto.
  Qed.

  Lemma num_occur_rename_all_ns_not_range:
    forall f sigma,
      ( forall e m n,
          num_occur e f m ->
          num_occur (rename_all_ns sigma e) f n  ->
          ~ Range_map sigma f ->
          n <= m).
  Proof.
    intros. eapply (proj1 (num_occur_rename_all_ns_not_range_mut _ _ H1)); eauto.
  Qed.

  Lemma num_occur_rename_all_fun_ns_not_range:
    forall f sigma fds m n,
      num_occur_fds fds f m ->
      num_occur_fds (rename_all_fun_ns sigma fds) f n  ->
      ~ Range_map sigma f ->
      n <= m.
  Proof.
    intros. eapply (proj2 (num_occur_rename_all_ns_not_range_mut _ _ H1)); eauto.
  Qed.


  Lemma num_occur_rename_all_not_dom_mut:
    forall f,
      ( forall e m n sigma,
          num_occur e f m ->
          num_occur (rename_all_ns sigma e) f n  ->
          ~ Dom_map sigma f ->
          m <= n) /\
      ( forall fds m n sigma,
          num_occur_fds fds f m ->
          num_occur_fds (rename_all_fun_ns sigma fds) f n  ->
          ~ Dom_map sigma f ->
          m <= n).
  Proof.
    intro f.
    apply exp_def_mutual_ind; intros.
    - simpl in H1. inv H1.
      inv H0.
      specialize (H _ _ _  H8 H9).
      apply Nat.add_le_mono.
      apply H. intro. apply H2.
      auto.
      apply num_occur_list_not_dom. auto.
    - simpl in H0. inv H0.
      inv H6. inv H.
      inv H5.
      apply Nat.add_le_mono.
      apply (num_occur_list_not_dom _ _ H1 ([v])).
      auto.
    - simpl in H2. inv H1. inv H2. inv H8. inv H7.
      replace (num_occur_list [v] f + (n + m)) with
          (n + (num_occur_list [v] f + m)) by lia.
      replace (Init.Nat.add (num_occur_list (@cons var (apply_r sigma v) (@nil var)) f) (Init.Nat.add n0 m0)) with
          (n0 + (num_occur_list (@cons var (apply_r sigma v) (@nil var)) f + m0)) by lia.
      apply Nat.add_le_mono.
      eapply H; eauto.
      eapply H0; eauto.
      simpl. constructor.
      auto.
    - simpl in H1. inv H1.
      inv H0.
      specialize (H _ _ _ H9 H10).
      apply Nat.add_le_mono.
      assert (Hll := num_occur_list_not_dom _ _ H2 ([v0])).
      simpl in Hll.    auto.
      apply H. intro; apply H2.
      auto.
    - simpl in H1. inv H1.
      inv H0.
      specialize (H _ _ _  H9 H10).
      apply Nat.add_le_mono.
      assert (Hll := num_occur_list_not_dom _ _ H2 (f0::ys)). eassumption.
      eauto.
    - inv H1.
      simpl in H2. inv H2.
      apply Nat.add_le_mono.
      eapply H0; eauto.
      eapply H; eauto.
    - inv H. inv H0.
      assert (Hll := num_occur_list_not_dom _ _ H1 (v::l)).
      simpl in Hll.
      auto.
    - inv H0; inv H1.
      eapply H; eauto.
    - inv H0; inv H1.
      apply Nat.add_le_mono.
      eapply H; eauto.
      apply num_occur_list_not_dom.
      auto.
    - inv H; inv H0.
      assert (Hll := num_occur_list_not_dom _ _ H1 ([v])).
      auto.
    - inv H1; inv H2.
      apply Nat.add_le_mono.
      eapply H; eauto.

      eapply H0; eauto.
    - inv H; inv H0. auto.
  Qed.


  Lemma num_occur_list_set:
    forall f y x sigma,
      f <> y ->
      forall l,
        num_occur_list (apply_r_list (M.set x y sigma) l) f  <=
        num_occur_list (apply_r_list sigma l) f.
  Proof.
    induction l; intros; simpl; auto.
    destruct (var_dec x a).
    - subst.
      rewrite apply_r_set1.
      destruct (term_util.var_dec f y).
      exfalso; auto.
      destruct (term_util.var_dec f (apply_r sigma a)); lia.
    - rewrite apply_r_set2  by auto.
      destruct (term_util.var_dec f (apply_r sigma a)); lia.
  Qed.


  Lemma num_occur_list_set_not_x:
    forall f y x sigma,
      ~ Dom_map sigma x ->
      f <> x ->
      forall l,
        num_occur_list (apply_r_list sigma l) f  <=
        num_occur_list (apply_r_list (M.set x y sigma) l) f.
  Proof.
    induction l; intros; simpl; auto.
    destruct (var_dec x a).
    - subst.
      rewrite apply_r_set1.
      destruct (term_util.var_dec f y). subst.
      destruct (term_util.var_dec y (apply_r sigma a)); lia.
      destruct (term_util.var_dec f (apply_r sigma a)).
      exfalso. unfold apply_r  in e.
      destruct (Maps.PTree.get a sigma) eqn:gas.
      apply H. exists v; auto.
      auto.
      auto.
    - rewrite apply_r_set2; auto.
      destruct (term_util.var_dec f (apply_r sigma a)); lia.
  Qed.

  Lemma num_occur_sig_unaffected:
    forall x sig n m e,
      ~ Dom_map sig x ->
      ~ Range_map sig x ->
      num_occur e x n ->
      num_occur (rename_all_ns sig e) x m ->
      n = m.
  Proof.
    intros.
    assert (n <= m).
    eapply (proj1 (num_occur_rename_all_not_dom_mut _)); eauto.
    assert (m <= n).
    eapply (proj1 (num_occur_rename_all_ns_not_range_mut _ _ H0)); eauto.
    lia.
  Qed.

  Lemma num_occur_rename_all_ns_set_not_x:
    forall f x y sigma,
      ~ Dom_map sigma x ->
      f <> x ->
      ( forall e m n,
          num_occur (rename_all_ns sigma e) f m ->
          num_occur (rename_all_ns (M.set x y sigma) e) f n  ->
          m <= n) /\
      ( forall fds m n,
          num_occur_fds (rename_all_fun_ns sigma fds) f m ->
          num_occur_fds (rename_all_fun_ns (M.set x y sigma) fds) f n  ->
          m <= n).
  Proof.
    intros f x y sigma Hdom Hfy; apply exp_def_mutual_ind; intros; simpl in *; try (inv H0; inv H1).
    - assert (Hl := num_occur_list_set_not_x f y x _ Hdom Hfy l).
      specialize (H _ _ H8 H7).
      apply Nat.add_le_mono; eauto.
    - inv H; inv H0.
      inv H5; inv H4.
      assert (Hl := num_occur_list_set_not_x).
      specialize (Hl f y x _ Hdom Hfy [v]).
      simpl in Hl.
      simpl.
      do 2 (rewrite Nat.add_0_r).
      auto.
    - inv H1; inv H2.
      inv H7; inv H6.
      rewrite OrdersEx.Nat_as_OT.add_shuffle3.
      rewrite  OrdersEx.Nat_as_OT.add_shuffle3 with (p := m0).
      apply Nat.add_le_mono; eauto.
    - assert (Hl := num_occur_list_set_not_x).
      specialize (Hl f y x _ Hdom Hfy [v0]).
      specialize (H _ _ H9 H8).
      simpl; simpl in Hl.
      apply Nat.add_le_mono; eauto.
    - assert (Hl := num_occur_list_set_not_x f y x _ Hdom Hfy (f0 :: ys)).
      apply Nat.add_le_mono; eauto.
    - inv H1; inv H2.
      apply Nat.add_le_mono; eauto.
    - inv H; inv H0.
      assert (Hl := num_occur_list_set_not_x).
      specialize (Hl f y x _ Hdom Hfy (v::l)).
      auto.
    - assert (Hl := num_occur_list_set_not_x f y x _ Hdom Hfy [v]).
      eauto.
    - assert (Hl := num_occur_list_set_not_x f y x _ Hdom Hfy l).
       apply Nat.add_le_mono; eauto.
    - inv H; inv H0.
      assert (Hl := num_occur_list_set_not_x f y x _ Hdom Hfy [v]).
      auto.
    - inv H1; inv H2.
      apply Nat.add_le_mono; eauto.
    - inv H; inv H0; auto.
  Qed.

  Lemma num_occur_rename_all_ns_set:
    forall f x y,
      f <> y ->
      ( forall e m n sigma,
          num_occur (rename_all_ns sigma e) f m ->
          num_occur (rename_all_ns (M.set x y sigma) e) f n  ->
          n <= m) /\
      ( forall fds m n sigma,
          num_occur_fds (rename_all_fun_ns sigma fds) f m ->
          num_occur_fds (rename_all_fun_ns (M.set x y sigma) fds) f n  ->
          n <= m).
  Proof.
    intros f x y Hfy; apply exp_def_mutual_ind; intros; simpl in *; try (inv H0; inv H1).
    - assert (Hl := num_occur_list_set _ _ x sigma Hfy l).
      specialize (H _ _ _ H8 H7).
      apply Nat.add_le_mono; eauto.
    - inv H; inv H0.
      inv H5; inv H4.
      assert (Hl := num_occur_list_set).
      specialize (Hl _ _ x sigma Hfy [v]).
      simpl in Hl.
      simpl.
      do 2 (rewrite Nat.add_0_r).
      auto.
    - inv H1; inv H2.
      inv H7; inv H6.
      rewrite OrdersEx.Nat_as_OT.add_shuffle3.
      rewrite  OrdersEx.Nat_as_OT.add_shuffle3 with (p := m).
      apply Nat.add_le_mono; eauto.
    - assert (Hl := num_occur_list_set).
      specialize (Hl _ _ x sigma Hfy [v0]).
      specialize (H _ _ _ H9 H8).
      simpl; simpl in Hl.
      apply Nat.add_le_mono; eauto.
    - assert (Hl := num_occur_list_set).
      specialize (Hl _ _ x sigma Hfy (f0::ys)).
      apply Nat.add_le_mono; eauto.
    - inv H1; inv H2.
      apply Nat.add_le_mono; eauto.
    - inv H; inv H0.
      assert (Hl := num_occur_list_set).
      specialize (Hl _ _ x sigma Hfy (v::l)).
      auto.
    - assert (Hl := num_occur_list_set _ _ x sigma Hfy [v]).
      eauto.
    - assert (Hl := num_occur_list_set _ _ x sigma Hfy l).
      apply Nat.add_le_mono; eauto.
    - inv H; inv H0.
      assert (Hl := num_occur_list_set _ _ x sigma Hfy [v]).
      auto.
    - inv H1; inv H2.
      apply Nat.add_le_mono; eauto.
    - inv H; inv H0; auto.
  Qed.


  Lemma num_occur_rename_all_ns_set_unchanged:
    forall f x y sigma e m n,
      ~ Dom_map sigma x ->
      f <> x ->
      f <> y ->
      num_occur (rename_all_ns sigma e) f m ->
      num_occur (rename_all_ns (M.set x y sigma) e) f n  ->
      m = n.
  Proof.
    intros.
    assert (n <= m). eapply (proj1 (num_occur_rename_all_ns_set _ _ _ H1)); eauto.
    assert (m <= n). eapply (proj1 (num_occur_rename_all_ns_set_not_x _ _ _ _ H H0)); eauto.
    lia.
  Qed.

  Lemma not_occur_rename_not_dom:
    forall sig v e,
      ~ Dom_map sig v ->
      num_occur (rename_all_ns sig e) v 0 ->
      num_occur e v 0.
  Proof.
    intros.
    assert (exists n, num_occur e v n) by apply e_num_occur.
    inv H1.
    assert (Hn0 := proj1 (num_occur_rename_all_not_dom_mut v) _ _ _ _ H2 H0 H).
    apply Nat.le_0_r in Hn0. subst; auto.
  Qed.

  Definition rename_all_case sigma cl := (List.map (fun (p:var*exp) => let (k, e) := p in
                                                                    (k, rename_all_ns sigma e)) cl).


  Lemma num_occur_case_rename_all_ns_not_dom:
    forall f,
    forall cl sig n m,
      num_occur_case cl f n ->
      num_occur_case (rename_all_case sig cl) f m ->
      ~ Dom_map sig f ->
      n <= m.
  Proof.
    induction cl; intros.
    - inv H; inv H0; auto.
    - inv H; inv H0.
      apply Nat.add_le_mono.
      eapply (proj1 (num_occur_rename_all_not_dom_mut _)); eauto.
      eauto.
  Qed.


  Lemma num_occur_set_arl:
    forall x y,
      x <> y ->
      forall l,
        num_occur_list (apply_r_list (M.set x y (M.empty var)) l) y =
        num_occur_list l y + num_occur_list l x.
  Proof.
    intros x y Hxy. induction l.
    auto.
    simpl. destruct (term_util.var_dec x a).
    - subst. rewrite apply_r_set1.
      destruct (term_util.var_dec y a).
      exfalso; auto.
      destruct (term_util.var_dec y y). 2: exfalso; auto.
      lia.
    - rewrite apply_r_set2 by auto.
      rewrite apply_r_empty.
      destruct (term_util.var_dec y a); lia.
  Qed.

  Lemma num_occur_arl_kill:
    forall x sig,
      ~ Range_map sig x ->
      Dom_map sig x ->
      forall l,
        num_occur_list (apply_r_list sig l) x = 0.
  Proof.
    induction l.
    auto.
    simpl. destruct (term_util.var_dec x (apply_r sig a)).
    - exfalso. unfold apply_r in e.
      destruct (@M.get var a sig) eqn:gas.
      subst.
      apply H. exists a; auto.
      subst.
      inv H0. unfold var, M.elt in *. rewrite H1 in gas. inv gas.
    - auto.
  Qed.

  Lemma num_occur_rename_all_ns_kill:
    forall x sig,
      ~ Range_map sig x ->
      Dom_map sig x ->
      (forall e,
          num_occur (rename_all_ns sig e) x 0 )/\
      (forall fds,
          num_occur_fds (rename_all_fun_ns sig fds) x 0).
  Proof.
    intros x sig Hrx Hdx.
    apply exp_def_mutual_ind; intros; simpl in *.
    - eapply num_occur_n. constructor. eauto.
      rewrite num_occur_arl_kill; auto.
    - eapply num_occur_n. constructor. constructor.
      assert (Hn := num_occur_arl_kill _ _ Hrx Hdx [v]).
      simpl in Hn. simpl. lia.
    - eapply num_occur_n. constructor. constructor. eauto.
      inv H0; pi0; eauto. simpl.
      inv H0; pi0. destruct (term_util.var_dec x (apply_r sig v)); subst; pi0; auto.
    - eapply num_occur_n. constructor; eauto.
      assert (Hn := num_occur_arl_kill _ _ Hrx Hdx [v0]).
      simpl in *; lia.
    - eapply num_occur_n. constructor; eauto.
      assert (Hn := num_occur_arl_kill _ _ Hrx Hdx (f::ys)).
      simpl in *. lia.
    - eapply num_occur_n. constructor; eauto.
      auto.
    - eapply num_occur_n. constructor; eauto.
      assert (Hn := num_occur_arl_kill _ _ Hrx Hdx (v::l)).
      simpl in *. lia.
    - eapply num_occur_n. constructor; eauto. reflexivity.
    - eapply num_occur_n. constructor; eauto.
      rewrite num_occur_arl_kill; auto.
    - eapply num_occur_n. constructor; auto.
      assert (Hn := num_occur_arl_kill _ _ Hrx Hdx [v]).
      simpl in *; lia.
    - eapply num_occur_fds_n.  constructor; eauto.
      auto.
    - constructor.
  Qed.

  Lemma num_occur_rename_mut:
    forall x y,
      x <> y ->
      (forall e n m,
          num_occur e x n ->
          num_occur e y m ->
          num_occur (rename_all_ns (M.set x y (M.empty var)) e) x 0 /\
          num_occur (rename_all_ns (M.set x y (M.empty var)) e) y (n+m)) /\
      (forall fds n m,
          num_occur_fds fds x n ->
          num_occur_fds fds y m ->
          num_occur_fds (rename_all_fun_ns (M.set x y (M.empty var)) fds) x 0 /\
          num_occur_fds (rename_all_fun_ns (M.set x y (M.empty var)) fds) y (n+m)).
  Proof.
    intros x y Hxy.
    apply exp_def_mutual_ind; intros; simpl in *; try (inv H0; inv H1).
    - specialize (H _ _ H8 H7).
      destruct H. split.
      eapply num_occur_n.
      constructor. eauto.
      rewrite num_occur_arl; auto.
      eapply num_occur_n.
      constructor; eauto.
      rewrite num_occur_set_arl; auto. lia.
    - inv H; inv H0.
      inv H5; inv H4.
      split.
      eapply num_occur_n. constructor; eauto.
      assert (Hn := num_occur_arl _ _ [v] Hxy).
      simpl in Hn. simpl.  rewrite Nat.add_0_r. auto.
      eapply num_occur_n. constructor. auto.
      assert (Hnn := num_occur_set_arl _ _ Hxy [v]).
      simpl. simpl in Hnn. do 3 (rewrite Nat.add_0_r). rewrite Nat.add_comm. auto.
    - inv H1; inv H2. inv H7; inv H6.
      specialize (H _ _ H8 H7).
      assert (num_occur (Ecase v l) x ( num_occur_list [v] x + m)).
      constructor; auto.
      assert (num_occur (Ecase v l) y ( num_occur_list [v] y + m0)).
      constructor; auto.
      specialize (H0 _ _ H1 H2).
      destruct H. destruct H0.
      inv H0; inv H4.
      split.
      + eapply num_occur_n.
        constructor. constructor; eauto.
        simpl. auto.
      + eapply num_occur_n.
        constructor. constructor; eauto.
        simpl. lia.
    - specialize (H _ _ H9 H8).
      destruct H.
      split.
      eapply num_occur_n. constructor; eauto.
      assert (Hn := num_occur_arl _ _ [v0] Hxy).
      simpl in Hn. simpl. rewrite Nat.add_0_r. auto.
      eapply num_occur_n. constructor; eauto.
      assert (Hnn := num_occur_set_arl _ _ Hxy [v0]).
      simpl. simpl in Hnn. unfold var in *. unfold M.elt in *. rewrite Hnn. lia.
    - specialize (H _ _ H9 H8).
      inv H. split; eapply num_occur_n; eauto.
      assert (Hn := num_occur_arl _ _ (f::ys) Hxy).
      simpl in Hn. simpl.
      unfold var in *. unfold M.elt in *. lia.
      assert (Hnn := num_occur_set_arl _ _ Hxy (f::ys)).
      simpl. simpl in Hnn. unfold var in *. unfold M.elt in *. lia.
    - inv H1; inv H2.
      specialize (H _ _ H8 H9).
      specialize (H0 _ _ H5 H4).
      destructAll. split; eapply num_occur_n; eauto.
      lia.
    - inv H; inv H0. split; eapply num_occur_n; eauto.
      assert (Hn := num_occur_arl _ _ (v::l) Hxy).
      simpl in Hn. simpl.
      unfold var in *. unfold M.elt in *. lia.
      assert (Hnn := num_occur_set_arl _ _ Hxy (v::l)).
      simpl. simpl in Hnn. unfold var in *. unfold M.elt in *. lia.
    - specialize (H _ _ H7 H6) as [].
      split; eapply num_occur_n; eauto.
    - specialize (H _ _ H8 H7).
      destruct H.
      split; eapply num_occur_n; eauto.
      rewrite num_occur_arl; auto.
      rewrite num_occur_set_arl; auto. lia.
    - inv H; inv H0.
      split; eapply num_occur_n; eauto.
      assert (Hn := num_occur_arl _ _ [v] Hxy).
      simpl in Hn. simpl. unfold var in *.
      unfold M.elt in *.
      lia.
      assert (Hnn := num_occur_set_arl _ _ Hxy [v]).
      simpl. simpl in Hnn. unfold var in *.  unfold M.elt in *. lia.
    - inv H1; inv H2. specialize (H _ _ H10 H9).
      specialize (H0 _ _ H11 H12).
      destruct H; destruct H0.
      split.
      eapply num_occur_fds_n. constructor; eauto.  auto.
      eapply num_occur_fds_n. constructor; eauto.  lia.
    - inv H; inv H0. split; auto.
  Qed.

  Lemma num_occur_rename_all_ctx_not_dom_mut:
    forall f,
      ( forall c m n sigma,
          num_occur_ec c f m ->
          num_occur_ec (rename_all_ctx_ns sigma c) f n  ->
          ~ Dom_map sigma f ->
          m <= n) /\
      ( forall fds m n sigma,
          num_occur_fdc fds f m ->
          num_occur_fdc (rename_all_fun_ctx_ns sigma fds) f n  ->
          ~ Dom_map sigma f ->
          m <= n).
  Proof.
    intro f.
    exp_fundefs_ctx_induction IHc IHfc; intros.
    - inv H0. inv H; auto.
    - simpl in H0. inv H0.
      inv H.
      specialize (IHc _ _ _  H7 H8).
      apply Nat.add_le_mono.
      apply num_occur_list_not_dom. auto.
      apply IHc. auto.
    - simpl in H0. inv H0.
      inv H.
      apply Nat.add_le_mono.
      apply (num_occur_list_not_dom _ _ H1 ([v0])).
      eauto.
    - simpl in H0. inv H0.
      inv H.
      specialize (IHc _ _ _  H8 H9).
      apply Nat.add_le_mono.
      assert (Hll := num_occur_list_not_dom _ _ H1 (f0::ys)). eassumption.
      eauto.
    - simpl in H0. inv H0; inv H. eauto.
    - simpl in H0. inv H0. inv H.
      apply Nat.add_le_mono.
      apply num_occur_list_not_dom; auto.
      eauto.
    - simpl in H0. inv H0.
      inv H.
      repeat apply Nat.add_le_mono.
      apply (num_occur_list_not_dom _ _ H1 ([v])).
      2: eauto.
      eapply num_occur_case_rename_all_ns_not_dom; eauto.
      eapply num_occur_case_rename_all_ns_not_dom; eauto.
    - inv H.
      simpl in H0. inv H0.
      apply Nat.add_le_mono; eauto.
      eapply (proj2 (num_occur_rename_all_not_dom_mut _)); eauto.
    - inv H. inv H0.
      apply Nat.add_le_mono; eauto.
      eapply (proj1 (num_occur_rename_all_not_dom_mut _)); eauto.
    - inv H.
      simpl in H0. inv H0.
      apply Nat.add_le_mono; eauto.
      eapply (proj2 (num_occur_rename_all_not_dom_mut _)); eauto.
    - inv H. inv H0.
      apply Nat.add_le_mono; eauto.
      eapply (proj1 (num_occur_rename_all_not_dom_mut _)); eauto.
  Qed.

  (* move to term_util *)
  Lemma e_num_occur_ec:
    forall c v, exists n, num_occur_ec c v n.
  Proof.
    intros.
    assert (exists n, num_occur (c |[ Ehalt v ]|) v n) by apply e_num_occur.
    destruct H.
    apply num_occur_app_ctx in H. destructAll.
    eauto.
  Qed.


  Lemma not_occur_rename_ctx_not_dom:
    forall sig v c,
      ~ Dom_map sig v ->
      num_occur_ec (rename_all_ctx_ns sig c) v 0 ->
      num_occur_ec c v 0.
  Proof.
    intros.
    assert (exists n, num_occur_ec c v n) by apply e_num_occur_ec.
    inv H1.
    assert (Hn0 := proj1 (num_occur_rename_all_ctx_not_dom_mut v) _ _ _ _ H2 H0 H).
    apply Nat.le_0_r in Hn0. subst; auto.
  Qed.


  Lemma not_occur_list: forall v l,
      num_occur_list l v = 0 <->
      ~ FromList l v.
  Proof.
    induction l; split; intro.
    - intro.
      inv H0.
    - constructor.
    - intro.
      simpl in H.
      inv H0.
      destruct (term_util.var_dec v v). inv H. apply n; auto.
      destruct (term_util.var_dec v a). inv H. apply IHl in H.
      auto.
    - simpl.
      destruct (term_util.var_dec v a).
      exfalso; apply H.
      constructor. auto.
      apply IHl.
      intro; apply H.
      constructor 2. auto.
  Qed.

  Lemma of_fun_inline:
    forall xs vs fb t c f B1 B2 c',
      unique_bindings (c' |[ Efun (fundefs_append B1 (Fcons f t xs fb B2)) (c |[ Eapp f t vs ]|) ]|) ->
      num_occur
        (Efun (fundefs_append B1 (Fcons f t xs fb B2))
              (c |[ Eapp f t vs ]|)) f 1 ->
      List.length xs = List.length vs ->
      Included _ (occurs_free (c' |[Efun (fundefs_append B1 B2) (c |[ (rename_all_ns (set_list (combine xs vs) (M.empty var)) fb)]|) ]|))
               (occurs_free (c' |[ Efun (fundefs_append B1 (Fcons f t xs fb B2)) (c |[ Eapp f t vs ]|) ]|)).
  Proof.
    intros xs vs fb t c f B1 B2 c' H Hnoc H0.
    eapply Included_trans.
    2:{ apply occurs_free_exp_ctx_included.
        apply of_fun_inline''' with (f := f) (fds := (fundefs_append B1 (Fcons f t xs fb B2))).
        2: apply H0.
        erewrite find_def_fundefs_append_r.
        simpl. destruct (M.elt_eq f f).
        reflexivity.
        exfalso. apply n. auto.
        simpl. destruct (M.elt_eq f f).
        reflexivity.
        exfalso. apply n. auto.
        apply ub_app_ctx_f in H.
        destructAll.
        inv H1.
        apply name_not_in_fundefs_find_def_None.
        eapply fundefs_append_unique_bindings_l in H6.
        2: reflexivity.
        destructAll.
        rewrite bound_var_fundefs_Fcons in H4.
        intro.
        apply name_in_fundefs_bound_var_fundefs in H6.
        inv H4.
        specialize (H8 f).
        apply H8.
        split; eauto. }
    apply of_fun_rm.
    apply ub_app_ctx_f in H.
    destructAll.
    inv H1. auto.
    {
      inv Hnoc.
      apply num_occur_app_ctx in H5.
      destructAll.
      inv H2. simpl in H3.
      destruct (term_util.var_dec f f).
      2: (exfalso; apply n; auto).
      assert (x = 0 /\ num_occur_list vs f = 0 /\ m = 0).
      lia.
      clear H3.
      apply fundefs_append_num_occur' in H6.
      destructAll.
      pi0.
      inv H6; pi0.
      constructor.
      apply num_occur_app_ctx.
      exists 0, 0.
      split; auto.
      split; auto.
      assert (exists n, num_occur (rename_all_ns (set_list (combine xs vs) (M.empty var)) fb) f n) by apply e_num_occur.
      destruct H2.
      assert (x <= 0).
      eapply num_occur_rename_all_ns_not_range; eauto.
      intro.
      apply Range_map_set_list in H4.
      apply not_occur_list in H3. auto.
      apply Nat.le_0_r in H4.
      subst. auto.
      rewrite <- Nat.add_0_l.
      eapply fundefs_append_num_occur.
      reflexivity.
      auto.
      rewrite <- Nat.add_0_l.
      constructor; auto.
    }
  Qed.

  Opaque num_occur_list.


  Lemma sr_rw_in_rw n e e' :
      unique_bindings e ->
      Disjoint _ (bound_var e) (occurs_free e) ->
      sr_rw n e e' ->
      (exists m, m >= n /\ gr_clos m e e').
  Proof.
    intros Hun Hdis Hsr; inv Hun; inv Hsr;
      try now (exists 1; split; eauto; econstructor; [| now eapply Refl ]; eapply Ctx_rw with (c := Hole_c);
               constructor; apply not_occurs_not_free).
    - (* Case folding *)
      exists 1; split; eauto. econstructor; [| now eapply Refl ]; eapply Ctx_rw with (c := Hole_c).
      econstructor. eassumption.
      intros Hc. eapply H. eapply bound_var_app_ctx.
      left. eapply bound_stem_var. auto.
    - (* Constructor folding *)
      eexists 1; split; eauto.
      econstructor; [| now eapply Refl ]; eapply Ctx_rw with (c := Hole_c).
      eapply ub_app_ctx_f in H0. destructAll.
      rewrite <- (proj1 (Disjoint_dom_rename_all_eq _)).
      2:{ rewrite Dom_map_set. rewrite Dom_map_empty. normalize_sets.
          inv H1. sets. }
      repeat normalize_bound_var_in_ctx. repeat normalize_occurs_free_in_ctx.
      constructor; eauto.
      + intros Hc. eapply H. eapply bound_var_app_ctx.
        left. eapply bound_stem_var. auto.
      + eapply Disjoint_In_l. eapply Disjoint_sym.
        eapply Disjoint_Included_l; [| eapply Hdis ].
        eapply Included_trans. eapply bound_stem_var. rewrite bound_var_app_ctx. now sets.
        left. eapply nthN_FromList. eassumption.
      + eapply Disjoint_In_l. eapply Disjoint_sym.
        eapply Disjoint_Included_l; [| eapply Hdis ].
        rewrite bound_var_app_ctx. normalize_bound_var. now sets.
        left. eapply nthN_FromList. eassumption.
      + intros Hc; subst. eapply Hdis. constructor.
        right. reflexivity. left. eapply nthN_FromList. eassumption.
      + intros Hc; subst. eapply Hdis. constructor.
        left. rewrite bound_var_app_ctx. normalize_bound_var. do 2 right. reflexivity.
        left. eapply nthN_FromList. eassumption.
    - (* Dead Funs *)
      exists 1; split; eauto.
      econstructor; [| now eapply Refl ]; eapply Ctx_rw with (c := Hole_c).
      econstructor. eapply Forall_impl; [| eassumption ].
      intros. eapply not_occurs_not_free. auto.
    - (* Dead Fun *)
      exists 1; split; eauto.
      econstructor; [| now eapply Refl ]; eapply Ctx_rw with (c := Hole_c).
      econstructor; eauto.
      eapply unique_bindings_fundefs_unique_functions. eassumption.
    - (* App inlining *)
      exists 2; split; eauto.
      replace 2 with (1 + 1) by lia.

      assert (Hub := H0).
        eapply split_fds_unique_bindings_fundefs_l in H0; [| eapply fundefs_append_split_fds; reflexivity ].
        destructAll. inv H2.
      assert (Hfind : find_def f (fundefs_append B1 (Fcons f t xs fb B2)) =  Some (t, xs, fb)).
        { erewrite find_def_fundefs_append_r. simpl. rewrite peq_true. reflexivity.
          simpl. rewrite peq_true. reflexivity. eapply name_not_in_fundefs_find_def_None.
          intros Hc. eapply H3. constructor. eapply name_in_fundefs_bound_var_fundefs. eassumption. constructor. now left. }

      econstructor; [ eapply Ctx_rw with (c := Hole_c) |
                      econstructor; [| now eapply Refl ]; eapply Ctx_rw with (c := Hole_c)].
      { eapply Fun_inline.
        - eassumption.
        - eassumption.
        - repeat normalize_bound_var_in_ctx. repeat normalize_occurs_free_in_ctx.
          rewrite bound_var_app_ctx in Hdis.
          repeat normalize_bound_var_in_ctx. repeat normalize_occurs_free_in_ctx. repeat normalize_sets.
          constructor. intros v Hin. inv Hin.

          destruct (Decidable_name_in_fundefs (fundefs_append B1 (Fcons f t xs fb B2))) as [Hdf].
          destruct (Hdf v) as [Hn | Hn].
          * eapply fundefs_append_name_in_fundefs in Hn; [| reflexivity ].
            simpl in Hn; inv Hn. eapply H3; eauto. constructor.
            eapply name_in_fundefs_bound_var_fundefs. eassumption. now eauto.
            inv H6. inv H8. contradiction.
            eapply H15; eauto. constructor; eauto. eapply name_in_fundefs_bound_var_fundefs. eassumption.

          * destruct (bound_var_ctx_dec c) as [Hdc]. destruct (Hdc v).
            -- eapply H1. rewrite bound_var_app_ctx. constructor; eauto.
               rewrite fundefs_append_bound_vars; [| reflexivity ]. normalize_bound_var.
               do 3 right. now left.
            -- eapply Hdis. constructor.
               left.
               eapply fun_in_fundefs_bound_var_fundefs. now eapply find_def_correct; eauto. now eauto.
               right. constructor; eauto.
               eapply occurs_free_ctx_not_bound; eauto.
        - eapply unique_bindings_fundefs_unique_functions. eassumption.
        - eapply Disjoint_Included; [| | eapply Hdis ].
          normalize_occurs_free; sets.
          normalize_bound_var. rewrite bound_var_app_ctx.
          eapply Included_trans. eapply bound_stem_var. sets.
        - eapply Disjoint_Included; [| | eapply H1 ].
          now eapply name_in_fundefs_bound_var_fundefs.
          rewrite bound_var_app_ctx.
          eapply Included_trans. eapply bound_stem_var. sets. }

      { erewrite <- (proj1 (Disjoint_dom_rename_all_eq _)).

        2:{ rewrite Dom_map_set_lists_ss; [| eassumption ]. eapply Disjoint_sym. sets. }

        eapply Fun_rem. eapply unique_bindings_fundefs_unique_functions. eassumption.
        Transparent num_occur_list.
        - inv H7. eapply num_occur_app_ctx_mut in H9.
          destructAll. inv H4. simpl in H6. rewrite peq_true in H6.
          assert (Heq0 : num_occur_list vs f = 0) by lia.
          assert (Heqx : x = 0) by lia.
          assert (Heqm : m = 0) by lia. subst.
          replace 0 with (0 + 0) by lia. constructor; [| eassumption ].

          eapply num_occur_app_ctx_mut. exists 0, 0. split; [| split ]; eauto.

          erewrite (proj1 (Disjoint_dom_rename_all_eq _)).

          2:{ rewrite Dom_map_set_lists_ss; [| eassumption ]. eapply Disjoint_sym. sets. }

          edestruct (e_num_occur f (rename_all_ns (set_list (combine xs vs) (M.empty var)) fb))
            as [m Ho].

          eapply fundefs_append_num_occur' in H10. destructAll. pi0. inv H7. pi0.
          eapply num_occur_rename_all_ns_not_range in H23; [| eassumption | ].
          assert (Heq : m = 0) by lia. subst. eassumption.

          intros Hc. eapply Range_map_set_list in Hc. eapply not_occur_list; eauto. }

    - (* Let app inlining *)
      eexists 2; split; eauto.
      assert (Hdefs:= H). assert (Hub := H0).
      replace 2 with (1 + 1) by lia.

      eapply split_fds_unique_bindings_fundefs_l in H0; [| eapply fundefs_append_split_fds; reflexivity ].
      destructAll. inv H2.

      assert (Hfind : find_def f (fundefs_append B1 (Fcons f t xs fb B2)) =  Some (t, xs, fb)).
      { erewrite find_def_fundefs_append_r. simpl. rewrite peq_true. reflexivity.
        simpl. rewrite peq_true. reflexivity. eapply name_not_in_fundefs_find_def_None.
        intros Hc. eapply H3. constructor. eapply name_in_fundefs_bound_var_fundefs. eassumption. constructor. now left. }


      assert (HdisFV : Disjoint var (bound_var fb :|: bound_var (Eletapp x f t vs e1))
                                (occurs_free (Eletapp x f t vs e1))).
      { constructor. intros v Hin. inv Hin.
        destruct (Decidable_name_in_fundefs (fundefs_append B1 (Fcons f t xs fb B2))) as [Hdf]. destruct (Hdf v) as [Hn | Hn ].
        * eapply fundefs_append_name_in_fundefs in Hn; [| reflexivity ].
          simpl in Hn; inv Hn.
          -- inv H2. eapply H3; eauto. constructor.
             eapply name_in_fundefs_bound_var_fundefs. eassumption. normalize_bound_var. now eauto.
             eapply H1. constructor. rewrite bound_var_app_ctx. now right; eauto.
             rewrite fundefs_append_bound_vars; [| reflexivity ]. left.
             eapply name_in_fundefs_bound_var_fundefs. eassumption.
          -- inv H7.
             ++ inv H9. inv H2; eauto.
                eapply H1. constructor. rewrite bound_var_app_ctx. now eauto.
                rewrite fundefs_append_bound_vars; [| reflexivity ]. right. eauto.
             ++ inv H2. eapply H16. constructor; eauto.
                eapply name_in_fundefs_bound_var_fundefs. eassumption.
                eapply H1. constructor. rewrite bound_var_app_ctx. now eauto.
                rewrite fundefs_append_bound_vars; [| reflexivity ]. right. normalize_bound_var.
                do 3 right. eapply name_in_fundefs_bound_var_fundefs. eassumption.
        * destruct (bound_var_ctx_dec c) as [Hdc]. destruct (Hdc v).
          -- inv H2.
             ++ eapply H1. constructor. rewrite bound_var_app_ctx. now left; eauto.
                rewrite fundefs_append_bound_vars; [| reflexivity ]. right. normalize_bound_var.
                now eauto.
             ++ eapply ub_app_ctx_f with (c := c) in Hdefs. destructAll.
                eapply H10. constructor; eauto.
          -- eapply Hdis. constructor.
             ++ inv H2. constructor.
                eapply fundefs_append_bound_vars. reflexivity. right.
                normalize_bound_var. do 2 right. left; eauto.

                normalize_bound_var. right. rewrite bound_var_app_ctx. right. eauto.
             ++ constructor; eauto. eapply occurs_free_ctx_not_bound; eauto. }


      econstructor; [ eapply Ctx_rw with (c := Hole_c) |
                      econstructor; [| now eapply Refl ]; eapply Ctx_rw with (c := Hole_c)].

      { eapply Fun_inline_letapp.
        - eassumption.
        - eassumption.
        - eapply Disjoint_Included; [| | eapply HdisFV ]. normalize_occurs_free; sets.
          sets.
        - eapply unique_bindings_fundefs_unique_functions. eassumption.
        - eapply Disjoint_Included; [| | eapply Hdis ]. normalize_occurs_free. sets.
          normalize_bound_var. rewrite bound_var_app_ctx. eapply Included_trans. eapply bound_stem_var. sets.
        - eapply Disjoint_Included; [| | eapply H1 ].
          now eapply name_in_fundefs_bound_var_fundefs.
          eapply Included_trans. eapply bound_stem_var. rewrite bound_var_app_ctx. sets.
        - eapply Union_Disjoint_r.
          eapply Union_Disjoint_r.
          * eapply Disjoint_Included; [| | eapply HdisFV ].  normalize_occurs_free; sets. normalize_bound_var; sets.
          * eapply Disjoint_Included; [| | eapply H1 ]; sets.
            rewrite bound_var_app_ctx. normalize_bound_var. sets.
          * eapply Disjoint_Included; [| | eapply Hdis ]; sets. normalize_occurs_free; sets.
            normalize_bound_var. rewrite bound_var_app_ctx. normalize_bound_var. sets.
        - eapply Disjoint_sym. eapply Disjoint_Included; [| | eapply HdisFV ]; sets.
          normalize_occurs_free. sets.
        - eapply ub_app_ctx_f in H.
          destructAll. inv H2. eassumption.
        - rewrite (proj1 (Disjoint_dom_rename_all_eq _)). eassumption.
          rewrite Dom_map_set_lists_ss; [| eassumption ].
          eapply Disjoint_sym. eapply unique_bindings_fun_in_fundefs. eapply find_def_correct. eassumption.
          eassumption.
      }

      { eapply ub_app_ctx_f in H.  destructAll. inv H2.

        rewrite <- (proj1 (Disjoint_dom_rename_all_eq _)).
        2:{ rewrite Dom_map_set. rewrite Dom_map_empty. normalize_sets.
            eapply Disjoint_Singleton_l.  eassumption. }

        eapply Fun_rem. eapply unique_bindings_fundefs_unique_functions. eassumption.

        - inv H6. eapply num_occur_app_ctx_mut in H21.
          destructAll. inv H6. simpl in H9. rewrite peq_true in H9.
          assert (Heq0 : num_occur_list vs f = 0) by lia.
          assert (Heqx : x0 = 0) by lia.
          assert (Heqm : m = 0) by lia.
          assert (Heqn : n = 0) by lia. subst.

          replace 0 with (0 + 0) by lia. constructor; [| eassumption ].

          eapply num_occur_app_ctx_mut. exists 0, 0. split; [| split ]; eauto.

          erewrite (proj1 (Disjoint_dom_rename_all_eq _)).

          2:{ rewrite Dom_map_set. rewrite Dom_map_empty. normalize_sets.
              eapply Disjoint_Singleton_l. eassumption. }

          eapply fundefs_append_num_occur' in H22. destructAll. pi0.
          eapply num_occur_app_ctx_mut. exists 0, 0.
          inv H7. pi0.
          split; [| split ]; eauto.

          { eapply num_occur_inline_letapp; [| eassumption | ].
            edestruct (e_num_occur f (rename_all_ns (set_list (combine xs vs) (M.empty var)) fb))
              as [m Ho].

            eapply num_occur_rename_all_ns_not_range in H27; [| eassumption | ].
            assert (Heq : m = 0) by lia. subst. eassumption.
            intros Hc. eapply Range_map_set_list in Hc. eapply not_occur_list; eauto.
            intros Hc; subst.
            eapply HdisFV. constructor. right. normalize_bound_var. now right.
            normalize_occurs_free. eauto. }
          { edestruct (e_num_occur f (rename_all_ns (M.set x x' (M.empty var)) e1))
              as [m Ho].
            eapply num_occur_rename_all_ns_not_range in H28; [| eassumption | ].
            assert (Heq : m = 0) by lia. subst. eassumption.
            intros Hc.
            eapply @Range_map_set_list with (xs := [x]) (vs := [x']) in Hc.
            repeat normalize_sets. inv Hc. eapply inline_letapp_var_eq in H8. inv H8; subst.

            eapply HdisFV. constructor. right. normalize_bound_var. now right.
            normalize_occurs_free. eauto.

            rewrite <- bound_var_rename_all_ns in H7. inv H7.
            eapply HdisFV. constructor. left; eauto. constructor; eauto. now left.

            eapply of_rename_all_ns_mut in H8. rewrite Dom_map_set_lists_ss in H8.
            inv H8. inv H7. now eapply not_occurs_not_free in H8; eauto.

            eapply Range_map_set_list in H7. eapply not_occur_list; eassumption.

            eassumption. } }
  Qed.

  (* TODO move *)
  Lemma find_tag_nth_findtag P c e1 :
    (exists n, find_tag_nth P c e1 n) <-> findtag P c = Some e1.
  Proof.
    induction P; simpl.
    - split; intros; try congruence.
      destructAll. inv H.
    - destruct a as [c' e2].
      destruct (M.elt_eq c' c); subst.
      + split; intros H.
        * destructAll. inv H. reflexivity.
          contradiction.
        * inv H. eexists. constructor.
      + rewrite <- IHP.
        split; intros H; destructAll.
        * inv H.
          contradiction. eauto.
        * eexists. constructor; eauto.
  Qed.

  Lemma ub_proj_dead: forall c x t n y e,
      unique_bindings (c |[ Eproj x t n y e]|)  ->
      unique_bindings (c |[e]|).
  Proof.
    intros.
    apply ub_app_ctx_f in H.
    apply ub_app_ctx_f.
    destructAll.
    split; auto.
    inv H0.
    split; auto.
    eapply Disjoint_Included_r.
    2: apply H1.
    rewrite bound_var_Eproj.
    left; auto.
  Qed.





  Lemma image_apply_r_set_list_alt xs vs (m : M.t var) S :
    image (apply_r (set_list (combine xs vs) m)) S \subset FromList vs :|: (image (apply_r m) S).
  Proof.
    revert vs m S; induction xs; intros vs m S.
    - simpl. sets.
    - destruct vs.
      + simpl; sets.
      + simpl. eapply Included_trans.
        eapply image_apply_r_set. normalize_sets.
        eapply Union_Included. now sets.
        eapply Included_trans. eapply (IHxs vs). xsets.
  Qed.


  Lemma of_fun_inline_letapp x e1 xs vs fb t c f fds C' x' :
      length xs = length vs ->
      find_def f fds = Some (t, xs, fb) ->
      inline_letapp (rename_all (set_list (combine xs vs) (M.empty var)) fb) x = Some (C', x') ->
      (occurs_free (Efun fds (c |[ C' |[ rename x' x e1 ]| ]|))) \subset
      (occurs_free (Efun fds (c |[ Eletapp x f t vs e1 ]|))).
  Proof.
    intros Hlen Hf Hin.
    repeat normalize_occurs_free.
    rewrite <- (Union_Same_set (occurs_free_fundefs fds \\ name_in_fundefs fds) (occurs_free_fundefs fds)) at 1; sets.
    rewrite (Union_commut (occurs_free_fundefs fds \\ name_in_fundefs fds)). rewrite <- Union_assoc.
    apply Union_Included; sets.
    rewrite Union_commut. rewrite <- Setminus_Union_distr.
    rewrite <- Setminus_Union_Included; [| reflexivity ].
    eapply Setminus_Included_Included_Union.
    rewrite <- Union_assoc. eapply Included_trans.
    eapply occurs_free_exp_ctx_included_u. tci.
    2:{ rewrite <- !Union_assoc. rewrite <- Union_Setminus; tci. sets. }
    eapply Union_Included; sets.
    eapply Included_trans. eapply occurs_fee_inline_letapp. eassumption.
    eapply Union_Included.
    - eapply Included_trans.
      eapply rename_all_occurs_free. eapply Included_trans. eapply image_apply_r_set_list. eassumption.
      rewrite image_apply_r_empty. eapply Union_Included.
      normalize_occurs_free. now sets.
      eapply Setminus_Included_Included_Union.
      eapply Included_trans. eapply occurs_free_in_fun. eapply find_def_correct. eassumption.
      now sets.
    - eapply Setminus_Included_Included_Union. eapply Included_trans.
      eapply rename_all_occurs_free. eapply Included_trans. eapply image_apply_r_set.
      eapply Union_Included.
      eapply inline_letapp_var_eq_alt in Hin. inv Hin.
      inv H. now sets.
      inv H; sets. eapply rename_all_occurs_free in H0. eapply image_apply_r_set_list in H0; [| eassumption ].
      rewrite image_apply_r_empty in H0.
      eapply Singleton_Included. normalize_occurs_free. inv H0. now eauto.
      inv H. eapply occurs_free_in_fun in H0; [| eapply find_def_correct; eauto ].
      inv H0; eauto. contradiction. now inv H; eauto.
      rewrite image_apply_r_empty. normalize_occurs_free. sets.
  Qed.


  Lemma of_fun_inline_app xs vs fb t c f fds:
      length xs = length vs ->
      find_def f fds = Some (t, xs, fb) ->
      (occurs_free (Efun fds (c |[ rename_all (set_list (combine xs vs) (M.empty var)) fb ]|))) \subset
      (occurs_free (Efun fds (c |[ Eapp f t vs ]|))).
  Proof.
    intros Hlen Hf Hin.
    repeat normalize_occurs_free.
    rewrite <- (Union_Same_set (occurs_free_fundefs fds \\ name_in_fundefs fds) (occurs_free_fundefs fds)) at 1; sets.
    rewrite (Union_commut (occurs_free_fundefs fds \\ name_in_fundefs fds)). rewrite <- Union_assoc.
    apply Union_Included; sets.
    rewrite Union_commut. rewrite <- Setminus_Union_distr.
    rewrite <- Setminus_Union_Included; [| reflexivity ].
    eapply Setminus_Included_Included_Union.
    rewrite <- Union_assoc. eapply Included_trans.
    eapply occurs_free_exp_ctx_included_u. tci.
    2:{ rewrite <- !Union_assoc. rewrite <- Union_Setminus; tci. sets. }
    eapply Union_Included; sets.
    eapply Included_trans.
    now eapply rename_all_occurs_free.
    eapply Included_trans. eapply image_apply_r_set_list. eassumption.
    rewrite image_apply_r_empty. eapply Union_Included. normalize_occurs_free. sets.
    eapply Setminus_Included_Included_Union.
    eapply Included_trans. eapply occurs_free_in_fun. eapply find_def_correct. eassumption.
    now sets.
  Qed.


  Lemma rw_preserves: forall n e e',
      unique_bindings e ->
      Disjoint _ (bound_var e) (occurs_free e) ->
      sr_rw n e e' ->
      unique_bindings e' /\
      Disjoint _ (bound_var e') (occurs_free e').
  Proof.
    intros n e e' Hub Hdj H; inv H; destructAll.
    - assert (Hub' := Hub). inv Hub'. split; eauto.
      eapply Disjoint_bv_of_ctx with (c := Econstr_c x t ys Hole_c).
      eassumption. eassumption.
    - assert (Hub' := Hub). inv Hub'. split; eauto.
      eapply Disjoint_bv_of_ctx with (c := Eprim_c x p ys Hole_c).
      eassumption. eassumption.
    - assert (Hub' := Hub). inv Hub'. split; eauto.
      eapply Disjoint_bv_of_ctx with (c := Eproj_c x t n0 y Hole_c).
      eassumption. eassumption.
    - assert (Hub' := Hub). inv Hub'. split; eauto.
      eapply Disjoint_bv_of_ctx with (c := Efun1_c fds Hole_c).
      eassumption. eassumption.
    - assert (Hub' := Hub). inv Hub. split.
      + simpl in *. repeat normalize_bound_var_in_ctx.
        rewrite !fundefs_append_bound_vars in *; try reflexivity.
        eapply fundefs_append_unique_bindings_l in H3;
          [| reflexivity ]. destructAll.
        repeat normalize_bound_var_in_ctx.
        constructor; eauto.
        inv H1. eapply fundefs_append_unique_bindings_r; eauto.
        now sets.
        rewrite !fundefs_append_bound_vars; try reflexivity.
        sets.
      + simpl in *. repeat normalize_bound_var_in_ctx.
        rewrite !fundefs_append_bound_vars in *; try reflexivity.
        eapply fundefs_append_unique_bindings_l in H3;
          [| reflexivity ]. destructAll.
        repeat normalize_bound_var_in_ctx.
        eapply Disjoint_Included; [ eapply of_fun_rm' | | eassumption ].
        * repeat normalize_bound_var.
          inv Hub'. eapply unique_bindings_fundefs_unique_functions. eassumption.
        * eassumption.
        * normalize_bound_var.
          rewrite fundefs_append_bound_vars; [| reflexivity ]. sets.
    - split.
      + eapply ub_case_inl with (c := Econstr_c x co ys c).
        eexists. eapply find_tag_nth_findtag. now eauto.
        eassumption.
      + eapply Disjoint_Included_r.
        eapply of_case_fold with (c' := Hole_c).
        eapply find_tag_nth_findtag. now eauto.
        simpl. eapply Disjoint_Included_l; [| eassumption ].
        repeat normalize_bound_var.
        repeat rewrite !bound_var_app_ctx in *.
        eapply Union_Included; sets.
        eapply Union_Included; sets.
        intros z Hin. left. right. econstructor. eassumption.
        eapply find_tag_nth_In_patterns. eassumption.
    - assert (Hub' := Hub).
      eapply ub_app_ctx_f with (c := Econstr_c x t ys c) in Hub. destructAll.
      inv H1.
      split.
      + apply ub_app_ctx_f with (c := Econstr_c x t ys c). split; [| split ]; eauto.
        eapply unique_bindings_rename_all_ns; eassumption.
        rewrite <- bound_var_rename_all_ns.
        eapply Disjoint_Included; [ | | eapply H2 ].
        normalize_bound_var; sets. reflexivity.
      + eapply Disjoint_Included; [| | eapply Hdj ].
        * eapply of_constr_proj'. eassumption.
        * simpl. repeat normalize_bound_var.
          rewrite !bound_var_app_ctx.
          rewrite <- bound_var_rename_all_ns. normalize_bound_var. sets.
    - assert (Hub' := Hub). inv Hub.
      eapply ub_app_ctx_f in H3. destructAll.
      assert (Hubd := H4). eapply fundefs_append_unique_bindings_l in H4; [| reflexivity ]. destructAll.
      inv H6.
      assert (Hfind : find_def f (fundefs_append B1 (Fcons f t xs fb B2)) =  Some (t, xs, fb)).
      { erewrite find_def_fundefs_append_r. simpl. rewrite peq_true. reflexivity.
        simpl. rewrite peq_true. reflexivity. eapply name_not_in_fundefs_find_def_None.
        intros Hc. eapply H7. constructor.
        eapply name_in_fundefs_bound_var_fundefs. eassumption. constructor. now left. }

      repeat normalize_bound_var_in_ctx.
      split.
      + constructor; eauto.
        eapply ub_app_ctx_f with (c := c).
        split; [| split ]; eauto.
        * eapply unique_bindings_rename_all_ns.
          eapply unique_bindings_fun_in_fundefs. eapply find_def_correct. eassumption. eassumption.
        * rewrite <- bound_var_rename_all_ns.
          eapply Disjoint_Included; [| | eapply H5 ].
          eapply Included_trans; [| eapply fun_in_fundefs_bound_var_fundefs; eapply find_def_correct; eauto ]. now sets.
          rewrite bound_var_app_ctx. now sets.
        * eapply fundefs_append_unique_bindings_r. reflexivity. eassumption. eassumption.
          sets.
        * rewrite fundefs_append_bound_vars; [| reflexivity ].
          rewrite bound_var_app_ctx in *. rewrite <- bound_var_rename_all_ns.
          rewrite fundefs_append_bound_vars in H5; [| reflexivity ].
          repeat  normalize_bound_var_in_ctx.
          eapply Union_Disjoint_l.
          eapply Disjoint_Included; [| | eapply H5 ]; now sets.
          sets.
      + eapply Disjoint_Included_r.
        apply of_fun_inline with (c' := Hole_c); eauto. simpl.
        eapply Disjoint_Included_l.
        2: apply Hdj.
        repeat normalize_bound_var. rewrite !bound_var_app_ctx.
        rewrite <- bound_var_rename_all_ns.
        rewrite fundefs_append_bound_vars; [| reflexivity ].
        rewrite fundefs_append_bound_vars with (B3 := (fundefs_append B1 (Fcons f t xs fb B2))); [| reflexivity ].
        repeat normalize_bound_var. xsets.
    - assert (Hub' := Hub). inv Hub.
      eapply ub_app_ctx_f in H4. destructAll.
      assert (Hubd := H5). eapply fundefs_append_unique_bindings_l in H5; [| reflexivity ]. destructAll.
      inv H7.
      assert (Hfind : find_def f (fundefs_append B1 (Fcons f t xs fb B2)) =  Some (t, xs, fb)).
      { erewrite find_def_fundefs_append_r. simpl. rewrite peq_true. reflexivity.
        simpl. rewrite peq_true. reflexivity. eapply name_not_in_fundefs_find_def_None.
        intros Hc. eapply H8. constructor.
        eapply name_in_fundefs_bound_var_fundefs. eassumption. constructor. now left. }

      repeat normalize_bound_var_in_ctx.
      rewrite !bound_var_app_ctx in *. rewrite fundefs_append_bound_vars in H6; [| reflexivity ].
      repeat normalize_bound_var_in_ctx.

      split.
      + inv H3. constructor; eauto.
        eapply ub_app_ctx_f with (c := c).
        split; [| split ]; eauto.
        * eapply ub_app_ctx_f with (c := C').  split; [| split ].
          -- eapply unique_bindings_inline_letapp; eauto.
             rewrite <- bound_var_rename_all_ns; eauto.
             intros Hc. eapply H6.
             constructor. now eauto. eauto.
             eapply unique_bindings_rename_all_ns. eassumption.
          -- eapply unique_bindings_rename_all_ns. eassumption.
          -- eapply Disjoint_Included_l. eapply bound_var_inline_letapp. eassumption.
             rewrite <- !bound_var_rename_all_ns; eauto.
             eapply Union_Disjoint_l. sets.
             eapply Disjoint_sym. eapply Disjoint_Included; [| | eapply H6]; sets.
        * rewrite bound_var_app_ctx. rewrite <- !bound_var_rename_all_ns; eauto.
          eapply Union_Disjoint_r; [| now sets ].
          eapply Disjoint_Included_r. eapply bound_var_inline_letapp. eassumption.
          rewrite <- !bound_var_rename_all_ns; eauto.
          eapply Union_Disjoint_r. sets. eapply Disjoint_Included; [| | eapply H6]; sets.

        * eapply fundefs_append_unique_bindings_r. reflexivity. eassumption. eassumption.
          sets.
        * rewrite fundefs_append_bound_vars; [| reflexivity ].
          rewrite !bound_var_app_ctx in *. rewrite <- bound_var_rename_all_ns.
          eapply Union_Disjoint_l; sets.
          now eapply Disjoint_Included; [| | eapply H6]; sets.
          eapply Union_Disjoint_l; sets.
          eapply Disjoint_Included_l. eapply bound_var_inline_letapp. eassumption.
          rewrite <- !bound_var_rename_all_ns; eauto.
          eapply Union_Disjoint_l.
          now eapply Disjoint_Included; [| | eapply H6]; sets.
          now eapply Union_Disjoint_r; sets.
          now eapply Disjoint_Included; [| | eapply H6]; sets.
      + rewrite <- (proj1 (Disjoint_dom_rename_all_eq _)) at 2.
        2:{ rewrite Dom_map_set. rewrite Dom_map_empty. normalize_sets.
            eapply Disjoint_Singleton_l. inv H3. eassumption. }

        assert (Hneq : x <> f).
        { intros Hc; subst. inv Hub'. eapply H12. constructor.
          rewrite bound_var_app_ctx. right. eauto.
          rewrite fundefs_append_bound_vars; [| reflexivity ]. normalize_bound_var. eauto. }

        eapply Disjoint_Included; [| | eapply Hdj ].
        * eapply Included_trans.
          2:{ eapply of_fun_inline_letapp. eassumption. eassumption.
              rewrite (proj1 (Disjoint_dom_rename_all_eq _)). eassumption.
              rewrite Dom_map_set_lists_ss; eauto. eapply Disjoint_sym. eassumption. }

          eapply of_fun_rm with (c := Hole_c). eassumption.
          inv H1. eapply num_occur_app_ctx in H12. destructAll. inv H7.
          simpl in H10. rewrite peq_true in H10. assert (Heqx : x0 = 0) by lia.
          assert (Heqn : n = 0) by lia. assert (Heqm : m = 0) by lia. subst.
          replace 0 with ((0 + 0) + 0) by lia.
          econstructor; eauto.

          eapply fundefs_append_num_occur' in H13. destructAll. pi0.
          eapply num_occur_app_ctx. exists 0, 0. split; eauto. split; eauto.
          eapply num_occur_app_ctx. exists 0, 0. split; eauto.
          eapply num_occur_inline_letapp; [| eassumption | ].
          edestruct (e_num_occur f (rename_all_ns (set_list (combine xs vs) (M.empty var)) fb))
            as [m Ho].
          inv H9. pi0.
          eapply num_occur_rename_all_ns_not_range in H26; [| eassumption | ].
          assert (Heq : m = 0) by lia. subst. eassumption.
          intros Hc. eapply Range_map_set_list in Hc. eapply not_occur_list; eauto. lia.
          eassumption.

          split; eauto.
          unfold rename. rewrite (proj1 (Disjoint_dom_rename_all_eq _)).
          2:{ rewrite Dom_map_set. rewrite Dom_map_empty. normalize_sets.
              eapply Disjoint_Singleton_l. inv H3. eassumption. }
          edestruct (e_num_occur f (rename_all_ns (M.set x x' (M.empty var)) e1)) as [m Ho].

          eapply num_occur_rename_all_ns_not_range with (e := e1) in H27; [| eassumption | ].
          assert (Heq : m = 0) by lia. subst. eassumption.
          intros Hc.
          eapply @Range_map_set_list with (xs := [x]) (vs := [x']) in Hc.
          repeat normalize_sets. inv Hc. eapply inline_letapp_var_eq in H2. inv H2; subst.

          contradiction.
          rewrite <- bound_var_rename_all_ns in H11. inv H11.
          contradiction.
          eapply of_rename_all_ns_mut in H2. rewrite Dom_map_set_lists_ss in H2.
          inv H2. inv H11.

          inv H9. pi0. now eapply not_occurs_not_free in H28; eauto.
          eapply Range_map_set_list in H11. eapply not_occur_list; [| eassumption ]. lia.
          eassumption.
        * repeat normalize_bound_var. rewrite fundefs_append_bound_vars; [| reflexivity ].
          rewrite fundefs_append_bound_vars with (B3 := fundefs_append B1 (Fcons f t xs fb B2)); [| reflexivity ].
          repeat rewrite bound_var_app_ctx. rewrite <- bound_var_rename_all_ns.
          normalize_bound_var. eapply Union_Included; sets.
          eapply Union_Included; sets. eapply Union_Included; sets.
          eapply Included_trans. eapply bound_var_inline_letapp. eassumption.
          rewrite <- bound_var_rename_all_ns. xsets.
  Qed.


  Lemma rw_preserves_fv e e' :
    rw e e' ->
    occurs_free e' \subset occurs_free e.
  Proof.
    intros Hrw.
    inv Hrw;
      (try now (normalize_occurs_free; rewrite Setminus_Disjoint; sets)).
    - normalize_occurs_free; rewrite Setminus_Disjoint; sets.
      eapply Disjoint_occurs_free_name_in_fundefs_cor. eassumption.
    - eapply of_fun_rm'; eauto.
    - eapply of_case_fold with (c' := Hole_c).
      eapply find_tag_nth_findtag; eauto.
    - repeat normalize_occurs_free.
      rewrite <- (Union_Same_set (FromList ys  \\ [set x]) (FromList ys)) at 1; sets.
      rewrite (Union_commut (FromList ys  \\ [set x])). rewrite <- Union_assoc.
      apply Union_Included; sets.
      rewrite Union_commut. rewrite <- Setminus_Union_distr.
      rewrite <- Setminus_Union_Included; [| reflexivity ].
      eapply Setminus_Included_Included_Union.
      rewrite <- Union_assoc. eapply Included_trans.
      eapply occurs_free_exp_ctx_included_u. tci.
      2:{ rewrite <- !Union_assoc. rewrite <- Union_Setminus; tci. sets. }
      eapply Union_Included; sets.
      eapply Included_trans.
      now eapply rename_all_occurs_free.
      eapply Included_trans. eapply image_apply_r_set.
      rewrite image_apply_r_empty. normalize_occurs_free.
      eapply Union_Included; sets.
      eapply Singleton_Included. right. left. eapply nthN_FromList. eassumption.
    - eapply of_fun_inline_app; eauto.
    - eapply of_fun_inline_letapp; eauto.
  Qed.

  Lemma rw_preserves_bv e e' :
    rw e e' ->
    bound_var e' \subset bound_var e.
  Proof.
    intros Hrw.
    inv Hrw;
      (try now (repeat normalize_bound_var; sets)).
    - repeat normalize_bound_var.
      rewrite fundefs_append_bound_vars; [| reflexivity ].
      rewrite fundefs_append_bound_vars with (B3 := (fundefs_append B1 (Fcons f t xs fb B2))); [| reflexivity ].
      normalize_bound_var. sets.
    - repeat normalize_bound_var.
      rewrite !bound_var_app_ctx.
      eapply Union_Included; sets.
      eapply Union_Included; sets.
      intros z Hin. left; right.
      eapply Bound_Ecase. eassumption.
      eapply find_tag_nth_In_patterns. eassumption.
    - repeat normalize_bound_var.
      rewrite !bound_var_app_ctx. repeat normalize_bound_var.
      unfold rename. rewrite rename_all_bound_var. sets.
    - repeat normalize_bound_var.
      rewrite !bound_var_app_ctx.
      rewrite rename_all_bound_var.
      eapply Union_Included; sets.
      eapply Union_Included; sets.
      eapply Included_Union_preserv_l.
      eapply Included_trans; [| eapply fun_in_fundefs_bound_var_fundefs; eapply find_def_correct; eauto ].
      sets.
    - repeat normalize_bound_var.
      rewrite !bound_var_app_ctx.
      unfold rename. rewrite rename_all_bound_var.
      eapply Union_Included; sets.
      eapply Union_Included; sets. normalize_bound_var.
      eapply Union_Included; sets.
      eapply Included_trans. eapply bound_var_inline_letapp. eassumption.
      rewrite rename_all_bound_var.
      eapply Union_Included; sets.
      eapply Included_Union_preserv_l.
      eapply Included_trans; [| eapply fun_in_fundefs_bound_var_fundefs; eapply find_def_correct; eauto ].
      sets.
  Qed.

  Lemma grw_preserves_fv e e' :
    gen_rw e e' ->
    occurs_free e' \subset occurs_free e.
  Proof.
    intros Hc. inv Hc.
    rewrite <- (Union_Empty_set_neut_r (occurs_free (c |[ e'0 ]|))).
    rewrite <- (Union_Empty_set_neut_r (occurs_free (c |[ e0 ]|))).
    eapply occurs_free_exp_ctx_included_u. tci.
    repeat normalize_sets.
    eapply rw_preserves_fv. eassumption.
  Qed.


  Lemma grw_preserves_bv e e' :
    gen_rw e e' ->
    bound_var e' \subset bound_var e.
  Proof.
    intros Hc. inv Hc.
    rewrite !bound_var_app_ctx.
    eapply Included_Union_compat. reflexivity.
    eapply rw_preserves_bv. eassumption.
  Qed.


  Lemma gr_clos_preserves_fv n e e' :
    gr_clos n e e' ->
    occurs_free e' \subset occurs_free e.
  Proof.
    intros Hc. induction Hc.
    - eapply Included_trans; eauto.
      eapply grw_preserves_fv. eassumption.
    - reflexivity.
  Qed.

  Lemma gr_clos_preserves_bv n e e' :
    gr_clos n e e' ->
    bound_var e' \subset bound_var e.
  Proof.
    intros Hc. induction Hc.
    - eapply Included_trans; eauto.
      eapply grw_preserves_bv. eassumption.
    - reflexivity.
  Qed.


  Lemma refl_trans_closure_n_ctx_compat (R : relation exp) :
    (forall e e' C, R e e' -> R (C |[ e ]|) (C |[ e' ]|)) ->
    (forall e e' C n, refl_trans_closure_n R n e e' -> refl_trans_closure_n R n (C |[ e ]|) (C |[ e' ]|)).
  Proof.
    intros Hyp e e' C n Hr. induction Hr.
    - econstructor.
      eapply Hyp. eassumption. eassumption.
    - eapply Refl.
  Qed.

  Lemma gen_sr_in_rw (n : nat) (e e' : exp) :
    unique_bindings e ->
    Disjoint var (bound_var e) (occurs_free e) ->
    gen_sr_rw n e e' ->
    exists m, m >= n /\ gr_clos m e e'.
  Proof.
    intros Hun Hdis Hsw. inv Hsw.
    edestruct sr_rw_in_rw; [| | eassumption | ].
    - eapply ub_app_ctx_f in Hun. destructAll. eassumption.
    - eapply Disjoint_bv_of_ctx; eauto.
    - destructAll. eexists. split; eauto.
      eapply refl_trans_closure_n_ctx_compat; [| eassumption ].
      intros e1 e2 C Hrw. inv Hrw.
      rewrite !app_ctx_f_fuse. constructor; eauto.
  Qed.

  Lemma gen_sr_rw_preserves n e e':
    unique_bindings e ->
    Disjoint _ (bound_var e) (occurs_free e) ->
    gen_sr_rw n e e' ->
    unique_bindings e' /\
    Disjoint _ (bound_var e') (occurs_free e').
  Proof.
    intros Hun Hdis Hrw.
    assert (Hrw' := Hrw). eapply gen_sr_in_rw in Hrw'; eauto. destructAll.
    split.
    + inv Hrw.
      assert (Hun' := Hun). eapply ub_app_ctx_f in Hun. destructAll.
      assert (H' := H1). eapply sr_rw_in_rw in H1; [| | eapply Disjoint_bv_of_ctx; eauto ]; eauto. destructAll.
      eapply ub_app_ctx_f with (c := c). split; [| split ]; eauto.
      * destructAll.
        eapply rw_preserves; [| | eassumption ]; eauto.
        eapply Disjoint_bv_of_ctx; eauto.
      * eapply Disjoint_Included_r; [| eassumption ].
        eapply gr_clos_preserves_bv. eassumption.
    + eapply Disjoint_Included; [| | eassumption ].
      eapply gr_clos_preserves_fv; eauto.
      eapply gr_clos_preserves_bv; eauto.
  Qed.


  Lemma gsr_clos_in_rw (n : nat) (e e' : exp) :
    unique_bindings e ->
    Disjoint var (bound_var e) (occurs_free e) ->
    gsr_clos n e e' ->
    (exists m, m >= n /\ gr_clos m e e').
  Proof.
    intros Hun Hdis Hsw. induction Hsw.
    - edestruct IHHsw as [m1 [Hgeq Hgr]].
      eapply gen_sr_rw_preserves; eauto.
      eapply gen_sr_rw_preserves; eauto.
      eapply gen_sr_in_rw in H; eauto. destructAll.
      eexists (x + m1).
      split. lia.
      eapply refl_trans_closure_n_trans; eauto.
    - eexists; split; [| eapply Refl ]. lia.
  Qed.


  Lemma gsr_clos_preserves n e e':
    unique_bindings e ->
    Disjoint _ (bound_var e) (occurs_free e) ->
    gsr_clos n e e' ->
    unique_bindings e' /\
    Disjoint _ (bound_var e') (occurs_free e').
  Proof.
    intros Hun Hdis H. induction H; eauto.
    eapply IHgsr_clos.
    eapply gen_sr_rw_preserves; eauto.
    eapply gen_sr_rw_preserves; eauto.
  Qed.


  Lemma gsr_clos_preserves_clos n e e' :
    unique_bindings e ->
    closed_exp e ->
    gsr_clos n e e' ->
    unique_bindings e' /\ closed_exp e'.
  Proof.
    intros Hun Hc Hrw.
    split.
    - eapply gsr_clos_preserves; eauto.
      unfold closed_exp in *. rewrite Hc. sets.
    - eapply gsr_clos_in_rw in Hrw; eauto. destructAll.
      + eapply gr_clos_preserves_fv in H0.
        unfold closed_exp in *. rewrite Hc in H0.
        eapply Included_Empty_set_r; eauto.
      + unfold closed_exp in *. rewrite Hc. sets.
  Qed.

  (* Corollary sr_correct n e e' : *)
  (*   unique_bindings e -> *)
  (*   Disjoint _ (bound_var e) (occurs_free e) -> *)
  (*   gsr_clos n e e' -> *)
  (*   forall pr cenv rho rho' k, *)
  (*     preord_env_P cenv P1 PG (occurs_free e) k rho rho'-> *)
  (*     preord_exp cenv P1 PG k (e, rho) (e', rho'). *)
  (* Proof. *)
  (*   intros. *)
  (*   apply rw_correct. *)
  (*   apply grs_in_gr; auto. *)
  (*   auto. *)
  (* Qed. *)

End Shrink_Rewrites.
