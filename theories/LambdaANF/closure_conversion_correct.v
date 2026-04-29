(* Correctness proof for closure conversion. Part of the CertiRocq project.
 * Author: Anonymized, 2016
 *)

Require Import LambdaANF.tactics LambdaANF.closure_conversion_invariants LambdaANF.closure_conversion LambdaANF.closure_conversion_util
        LambdaANF.algebra.
Require Import LambdaANF.closure_conversion_corresp LambdaANF.state compM.
From CertiRocq.LambdaANF Require Import term size_cps term_util set_util hoisting identifiers ctx
                       Ensembles_util List_util functions eval logical_relations_cc.
Require Import compcert.lib.Coqlib.
From Stdlib Require Import ZArith.Znumtheory Relations.Relations Arith.Wf_nat
                        Lists.List MSets.MSets MSets.MSetRBT Numbers.BinNums
                        NArith.BinNat PArith.BinPos Sets.Ensembles micromega.Lia
                        Sorting.Permutation ArithRing.
Import ListNotations.

Open Scope ctx_scope.
Open Scope fun_scope.
Close Scope Z_scope.


Section Closure_conversion_correct.

  Open Scope alg_scope.

  Context {fuel : Type} {Hfuel : @fuel_resource fuel} {trace : Type} {Htrace : @trace_resource trace}.

  Variable pr : prims.
  Variable cenv : ctor_env.
  Variable clo_tag : ctor_tag.
  Variable clo_itag : ind_tag.

  Context (boundL : nat -> @PostT fuel trace) (* Local *)
          (* the nat parameter is usefull when we want to give an upper bound to the steps, but for now its a dummy paramater *)
          (boundG : @PostGT fuel trace).  (* Global *)

  Context (HPost : forall k, Post_properties cenv (boundL 0) (boundL k) boundG).
  Context (Hpost_locals_r :
             forall (n : nat) (rho1 rho2  rho2' : env)(e1 : exp) (e2 : exp)
                    (cin1 : fuel) (cout1 : trace)
                    (cin2 : fuel) (cout2 : trace) (C : exp_ctx),
               ctx_to_rho C rho2 rho2' ->
               boundL (n + to_nat (one_ctx C)) (e1, rho1, cin1, cout1)
                      (e2, rho2', cin2, cout2) ->
               boundL n (e1, rho1, cin1, cout1)
                      (C |[ e2 ]|, rho2, cin2 <+> (one_ctx C), cout2 <+> (one_ctx C))).
  Context (Hpost_locals_l :
             forall (n : nat) (rho1 rho2  rho2' : env)(e1 : exp) (e2 : exp)
                    (cin1 : fuel) (cout1 : trace)
                    (cin2 : fuel) (cout2 : trace) (C : exp_ctx),
               ctx_to_rho C rho2 rho2' ->
               boundL n (e1, rho1, cin1, cout1)
                      (C |[ e2 ]|, rho2, cin2 <+> (one_ctx C), cout2 <+> (one_ctx C)) ->
               boundL (n + to_nat (one_ctx C)) (e1, rho1, cin1, cout1)
                      (e2, rho2', cin2, cout2)).
  Context (Hpost_locals_l0 :
             forall (n : nat) (rho1 rho2  rho2' : env)(e1 : exp) (e2 : exp)
                    (cin1 : fuel) (cout1 : trace)
                    (cin2 : fuel) (cout2 : trace) (C : exp_ctx),
               ctx_to_rho C rho2 rho2' ->
               boundL n (e1, rho1, cin1, cout1)
                      (C |[ e2 ]|, rho2, cin2, cout2) ->
               boundL (n + to_nat (one_ctx C)) (e1, rho1, cin1, cout1)
                      (e2, rho2', cin2, cout2)).

  (** ** Semantics preservation proof *)


  (* Short-hands so that we don't have to apply the parameters every time *)
  Definition FV_inv := FV_inv cenv clo_tag boundG.
  Definition FV_inv_strong := FV_inv_strong cenv clo_tag boundG.
  Definition Fun_inv := Fun_inv cenv clo_tag boundG.
  Definition GFun_inv := GFun_inv cenv clo_tag boundG.
  Definition closure_env := closure_env cenv clo_tag boundG.

  (** * Lemmas about the existance of the interpretation of an evaluation context *)

  Lemma project_var_ctx_to_rho Scope Funs GFuns c genv Γ FVs x x' C S S' v1 k rho1 rho2 :
    Disjoint _ S (GFuns \\ Scope) ->
    project_var clo_tag Scope Funs GFuns c genv Γ FVs S x x' C S' ->
    FV_inv k rho1 rho2 Scope Funs GFuns c Γ FVs ->
    Fun_inv k rho1 rho2 Scope Funs genv ->
    GFun_inv k rho1 rho2 GFuns ->
    M.get x rho1 = Some v1 ->
    exists rho2', ctx_to_rho C rho2 rho2'.
  Proof.
    intros Hg Hproj HFV HFun HGfun Hget. inv Hproj.
    - eexists; econstructor; eauto.
    - edestruct HFun as
          [vs' [rho3 [B3 [f3 [rho4 [B4 [f4 [Hget1 [Heq2 [Ηnin2 [Hget2 Happrox]]]]]]]]]]]; eauto.
      eexists; econstructor; eauto.
      simpl. rewrite Hget2. rewrite Hget1. reflexivity.
      constructor.
    - edestruct HGfun with (c := c) as
          [rho3 [B3 [f3 [rho4 [B4 [f4 [Heq2 [Hget2 Happrox]]]]]]]]; eauto.
      eexists; econstructor; eauto. reflexivity.
      subst. econstructor.
      simpl. rewrite M.gso, Hget2.
      rewrite M.gss. reflexivity.
      intros Hc; subst. eapply Hg. constructor.
      now eapply H3. now constructor; eauto.
      constructor.
    - edestruct HFV as [c' [g [Hgetg [Hleq Hin]]]].
      intros Heq. subst. simpl in H2. inv H2.
      eapply Forall2_nthN in Hin; eauto.
      destruct Hin as [v2 [Hnth' Hyp]]. destruct FVs; try now inv H2.
      rewrite Hleq in *; try congruence.
      eexists. econstructor; eauto. constructor.
  Qed.

  Lemma project_vars_ctx_to_rho Scope Funs GFuns c genv Γ FVs xs xs' C S S' vs1 k rho1 rho2 :
    Disjoint _ S (Scope :|: (Funs \\ Scope) :|: GFuns:|: image genv (Funs \\ Scope) :|: FromList FVs :|: [set Γ]) ->
    project_vars clo_tag Scope Funs GFuns c genv Γ FVs S xs xs' C S' ->
    Fun_inv k rho1 rho2 Scope Funs genv ->
    GFun_inv k rho1 rho2 GFuns ->
    FV_inv k rho1 rho2 Scope Funs GFuns c Γ FVs ->
    get_list xs rho1 = Some vs1 ->
    exists rho2', ctx_to_rho C rho2 rho2'.
  Proof.
    revert Scope Funs genv Γ FVs xs' C S S' vs1 k
           rho1 rho2.
    induction xs;
      intros Scope Funs genv Γ FVs xs' C S S' vs1 k
             rho1 rho2 HD Hvars HFun HGfun HFV Hget_list.
    - inv Hvars. eexists; econstructor; eauto.
    - inv Hvars. simpl in Hget_list.
      destruct (M.get a rho1) eqn:Hgeta1; try discriminate.
      destruct (get_list xs rho1) eqn:Hget_list1; try discriminate.
      edestruct project_var_ctx_to_rho with (rho1 := rho1) as [rho2' Hctx1]; eauto.
      eapply Disjoint_Included_r; [| eassumption ].
      now eauto 10 with Ensembles_DB functions_BD.
      edestruct IHxs with (rho2 := rho2') as [rho2'' Hctx2].
      + eapply Disjoint_Included_l; [| eassumption ].
        eapply project_var_free_set_Included. eassumption.
      + eassumption.
      + inv Hget_list. intros f v' Hnin Hin Hget.
        edestruct HFun as
            [vs' [rho3 [B3 [f3 [rho4 [B4 [f4 [Hget1 [Heq2 [Ηnin2 [Hget2 Happrox]]]]]]]]]]]; eauto.
        repeat eexists; eauto.
        erewrite <- project_var_get; eauto.  intros Hc. eapply HD. constructor. eassumption.
        do 2 left. right. eapply In_image. constructor; eauto.

        erewrite <- project_var_get; eauto.
        intros Hin'. eapply HD. constructor. now eauto.
        do 4 left. right. constructor; eauto.
      + intros x v1 c' Hin Hget. inv Hget_list.
        edestruct HGfun as [rho0 [B1 [f1 [rho3 [B2 [f2 [Heq1 [Hget' Hcc]]]]]]]]; eauto.
        subst.
        repeat eexists; eauto.
        erewrite <- project_var_get; eauto.
        intros Hin'. eapply HD. constructor; eauto.
      + intros Hneq. edestruct HFV as [c' [g [Hgetg [Hleq Hinv]]]]. eassumption.
        exists c'.  eexists; split; eauto.
        erewrite <- project_var_get; eauto.
        intros Hin. eapply HD. now eauto.
      + eassumption.
      + exists rho2''. eapply ctx_to_rho_comp_ctx_f_r; eassumption.
  Qed.

  (** * Correctness lemmas *)

  (** Correctness of [closure_conversion_fundefs]. Basically un-nesting the nested
      induction that is required by the correctness of [Closure_conversion] *)
  Lemma Closure_conversion_fundefs_correct k rho rho' B1 B2 Scope c genv Γ FVs GFuns GFuns' :
    (* The IH *)
    (forall m : nat,
       m < k ->
       forall (e : exp) (rho rho' : env) (e' : exp)
         (Scope Funs GFuns : Ensemble var) c genv (Γ : var) (FVs : list var)
         (C : exp_ctx),
         cc_approx_env_P cenv clo_tag Scope m boundG rho rho' ->
         ~ In var (bound_var e) Γ ->

         binding_in_map (occurs_free e) rho ->
         unique_bindings e ->

         Disjoint var (Funs \\ Scope :|: GFuns) (bound_var e) ->
         Disjoint _ (image genv (Funs \\ Scope)) (bound_var e) ->

         Fun_inv m rho rho' Scope Funs genv ->
         GFun_inv m rho rho' GFuns ->
         FV_inv m rho rho' Scope Funs GFuns c Γ FVs ->

         Closure_conversion clo_tag Scope Funs GFuns c genv Γ FVs e e' C ->

         cc_approx_exp cenv clo_tag m (boundL 0) boundG (e, rho) (C |[ e' ]|, rho')) ->
    (* FVs *)
    (occurs_free_fundefs B1 \\ GFuns) <--> (FromList FVs) ->
    (* unique functions *)
    unique_bindings_fundefs B1 ->
    binding_in_map (occurs_free_fundefs B1) rho ->

    GFun_inv k rho rho' GFuns ->
    FV_inv_strong k rho rho' (Empty_set _) (Empty_set _) GFuns c Γ FVs ->

    add_global_funs GFuns (name_in_fundefs B1) (FromList FVs) GFuns' ->
    (* Closure Conversion *)
    Closure_conversion_fundefs clo_tag B1 GFuns' c FVs B1 B2 ->

    Disjoint _ GFuns (bound_var_fundefs B1) ->

    (name_in_fundefs B1) <--> (name_in_fundefs B2) ->

    (* ~ In _ (image σ GFuns :|: name_in_fundefs B1) Γ -> *)
    ~ In _ (name_in_fundefs B2) Γ ->

    Fun_inv k (def_funs B1 B1 rho rho) (def_funs B2 B2 rho' rho') Scope (name_in_fundefs B1) (extend_fundefs' genv B1 Γ) /\
    GFun_inv k (def_funs B1 B1 rho rho) (def_funs B2 B2 rho' rho') GFuns'.
  Proof.
    revert k rho rho' B1 B2 Scope c genv Γ FVs GFuns GFuns'.
    induction k as [k IHk] using lt_wf_rec1;
      intros rho rho' B1 B2 Scope c genv Γ FVs GFuns GFuns' IHe Heqfv Hun Hbin Hgfun Hfvs Haddf Hcc
             Hdis (* Hscope_d *) Hseq (* Hnin *) Hnin'.
    split.
    - intros f1 v1 Hin1 Hnin2 Hget. repeat subst_exp.
      edestruct (name_in_fundefs_find_def_is_Some _ _ Hnin2) as [ft [xs [e_body Hfind1]]].
      edestruct closure_conversion_fundefs_find_def as [G' [C [e2 [Hnin1 [Hfind2 Hcce]]]]]; eauto.
      rewrite def_funs_eq in Hget; [| eassumption ]. inv Hget. assert (Hfvs' := Hfvs).
      destruct Hfvs' as [c1 [vs [Hget1 [Hceq Hall]]]].
      do 7 eexists; repeat split.
      + rewrite extend_fundefs'_get_s; eauto.
        rewrite def_funs_neq; eassumption.
      + eassumption.
      + rewrite def_funs_eq. reflexivity.
        eapply Hseq. eassumption.
      + simpl. rewrite cc_approx_val_eq. split; auto.
        intros vs1 vs2 j t1 xs1 e1 rho1' Hlen Hfind Hset.
        edestruct (@set_lists_length val)
          with (rho' := def_funs B2 B2 rho' rho') as [rho2' Hset'].
        eassumption. now eauto. repeat subst_exp.
        do 4 eexists; repeat split.
        * eassumption.
        * simpl. rewrite Hset'. reflexivity.
        * intros Hlt Hall1.
          eapply cc_approx_exp_rel_mon with (P1 := boundL 0).
          2:{ eapply HPost. exact 0. }
          assert (HK : Fun_inv j (def_funs B1 B1 rho rho) (def_funs B2 B2 rho' rho') (FromList xs1) (name_in_fundefs B1) (extend_fundefs' id B1 Γ) /\
                       GFun_inv j (def_funs B1 B1 rho rho) (def_funs B2 B2 rho' rho') GFuns').
          { eapply IHk with (B1 := B1); try eassumption.
            - intros. eapply IHe; eauto. lia.
            - eapply GFun_inv_monotonic; eauto. lia.
            - eapply FV_inv_strong_monotonic. eassumption. lia. }
          edestruct HK as [Hf Hg].
          (* Apply IHe *)
          eapply IHe with (Scope := FromList xs1) (GFuns := GFuns');
            [ eassumption | | | | | | | | | | eassumption ].
          -- eapply cc_approx_env_P_set_not_in_P_r.
             eapply cc_approx_env_P_set_lists_l with (P1 := Empty_set _); eauto.
             eapply cc_approx_env_Empty_set. now intros Hc; eauto.
             intros Hc. eapply Hnin1. right; left. eassumption.
          -- intros Hc. apply Hnin1. eauto.
          -- eapply binding_in_map_antimon.
             eapply occurs_free_in_fun. eapply find_def_correct. eassumption.
             eapply binding_in_map_set_lists; [| now eauto ].
             eapply binding_in_map_def_funs. eassumption.
          -- eapply unique_bindings_fun_in_fundefs. eapply find_def_correct. eassumption. eassumption.
          -- eapply Disjoint_Included_l. eapply Included_Union_compat. reflexivity.
             eapply add_global_funs_included_r. eassumption.
             rewrite Union_Same_set; [| now sets ]. eapply Union_Disjoint_l.
             eapply Disjoint_Included;[ | | eapply Hdis ]; sets.
             eapply Included_trans;
               [| eapply fun_in_fundefs_bound_var_fundefs; now eapply find_def_correct; eauto ]. now sets.
             eapply Disjoint_sym. eapply unique_bindings_fun_in_fundefs. eapply find_def_correct. eassumption. eassumption.
          -- eapply Disjoint_Included_l.
             eapply Included_trans. eapply image_monotonic. eapply Setminus_Included.
             eapply extend_fundefs'_image. eapply Disjoint_Singleton_l. intros Hc; eapply Hnin1.
             sets.
          -- (* Fun_inv *)
             eapply Fun_inv_rename with (Γ := Γ). intros Hin.
             eapply Hnin'. rewrite <- Hseq. inv Hin. now sets.

             intros Hin. eapply Hnin1. left. inv Hin. now eauto. now sets.

             eapply Fun_inv_set_lists_In_Scope_l; [ now apply Included_refl | | now eauto ].
             eapply Fun_inv_set_lists_In_Scope_r; [ now apply Included_refl | | reflexivity | | eassumption ].
             now sets.

             eapply Fun_inv_reset. eauto. reflexivity. eassumption. eassumption.
          -- assert (Hdis1 : Disjoint map_util.M.elt GFuns' (FromList xs1)).
             { eapply Disjoint_Included_l. eapply add_global_funs_included_r. eassumption.
               eapply Union_Disjoint_l.
               eapply Disjoint_Included;[ | | eapply Hdis ]; sets.
               eapply Included_trans;
                 [| eapply fun_in_fundefs_bound_var_fundefs; now eapply find_def_correct; eauto ]. now sets.
               eapply Disjoint_sym. eapply unique_bindings_fun_in_fundefs. eapply find_def_correct. eassumption. eassumption. }

             eapply GFun_inv_set_not_In_GFuns_r.
             intros Hc. eapply Hnin1. left. now eauto.
             eapply GFun_inv_setlist_not_In_GFuns_l; [| now eauto | ]. eassumption.
             eapply GFun_inv_setlist_not_In_GFuns_r; [| now eauto | ]. eassumption.

             eapply GFun_inv_antimon. eassumption. sets.
          -- do 2 eexists. split. rewrite M.gss. reflexivity. split. now eauto.
             eapply Forall2_monotonic; [| eassumption ].
             intros x v1 Hyp v2 Hnin3 Hnin4 Hnin5 Hget'.
             erewrite <- set_lists_not_In in Hget'; [| now eauto | eassumption ].
             erewrite def_funs_neq in Hget'.
             eapply cc_approx_val_monotonic. eapply Hyp; eauto.
             now eapply not_In_Empty_set. now eapply not_In_Empty_set.
             intros Hc. eapply add_global_funs_included in Hc; [| | eassumption ]; tci. inv Hc; eauto.
             lia. eassumption.
    - edestruct Hfvs as [c' [vs [Hgetg [Hleq Hallg]]]].
      assert (Hpre : GFun_inv k (def_funs B1 B1 rho rho) (def_funs B2 B2 rho' rho') (GFuns \\ name_in_fundefs B1)).
      { intros f1 v1 c1 Hnin2 Hget. inv Hnin2.
        rewrite def_funs_neq in Hget; eauto.
        edestruct Hgfun as [rho3 [B3 [f3 [rho4 [B4 [f4 [Hveq [Hgetsf Hvalcc]]]]]]]].
        eassumption.
        eassumption. repeat eexists. eassumption.
        rewrite def_funs_neq. eassumption.
        rewrite Hseq in H0. eassumption. eassumption. }

      inv Haddf; [| eassumption ].
      intros f1 v1 c1 Hnin2 Hget.
      eapply add_global_funs_included_r in Hnin2; eauto.
      2:{ constructor. eassumption. }
      destruct (Decidable_name_in_fundefs B1). destruct (Dec f1); [| inv Hnin2; try contradiction ].
      + rewrite def_funs_eq in Hget; eauto. inv Hget.
        do 7 eexists; repeat split.
        * rewrite def_funs_eq. reflexivity.
          eapply Hseq. eassumption.
        * simpl. rewrite cc_approx_val_eq. split; eauto.
          intros vs1 vs2 j t1 xs1 e1 rho1' Hlen Hfind Hset.
          edestruct (@set_lists_length val)
            with (rho' := def_funs B2 B2 rho' rho') as [rho2' Hset']; [| now eauto | ]. eassumption.
          edestruct closure_conversion_fundefs_find_def
            as [Γ'' [C2 [e2 [Hnin'' [Hfind' Hcc']]]]]. eassumption. eassumption.

          exists Γ'', xs1. do 2 eexists. split. eassumption. split.
          simpl. rewrite Hset'. reflexivity.
          intros Hlt Hall.
          assert (HK : Fun_inv j (def_funs B1 B1 rho rho) (def_funs B2 B2 rho' rho') (FromList xs1) (name_in_fundefs B1) (extend_fundefs' id B1 Γ) /\
                       GFun_inv j (def_funs B1 B1 rho rho) (def_funs B2 B2 rho' rho') (name_in_fundefs B1 :|: GFuns)).
          { eapply IHk with (B1 := B1); try eassumption.
            - intros. eapply IHe; eauto. lia.
            - eapply GFun_inv_monotonic; eauto. lia.
            - eapply FV_inv_strong_monotonic. eassumption. lia.
            - constructor; eauto. }
          destruct HK as [Hkf Hkg].
          assert (Hdis1 : Disjoint map_util.M.elt (name_in_fundefs B1 :|: GFuns) (FromList xs1)).
          { eapply Union_Disjoint_l.
             eapply Disjoint_sym. eapply unique_bindings_fun_in_fundefs. eapply find_def_correct. eassumption. eassumption.
             eapply Disjoint_Included;[ | | eapply Hdis ]; sets.
             eapply Included_trans;
               [| eapply fun_in_fundefs_bound_var_fundefs; now eapply find_def_correct; eauto ]. now sets. }

          assert (Hgfun' : GFun_inv j rho1' (M.set Γ'' (Vconstr c1 []) rho2') (name_in_fundefs B1 :|: GFuns)).
          {
            eapply GFun_inv_set_not_In_GFuns_r.
            intros Hc. eapply Hnin''.
            left. inv Hc. now eauto. now eauto.

            eapply GFun_inv_setlist_not_In_GFuns_l; [| now eauto | ]. now sets.
            eapply GFun_inv_setlist_not_In_GFuns_r; [| now eauto | ]. now sets.
            eapply GFun_inv_antimon. eassumption. sets. }

          eapply cc_approx_exp_rel_mon with (P1 := boundL 0).
          2:{ eapply HPost. exact 0. }
          (* Apply IHe *)
          eapply IHe with (Scope := FromList xs1) (GFuns := name_in_fundefs B1 :|: GFuns)
                          (genv := extend_fundefs' id B1 Γ''); [ | | | | | | | | | | eassumption ].
          -- eassumption.
          -- eapply cc_approx_env_P_set_not_in_P_r.
             eapply cc_approx_env_P_set_lists_l with (P1 := Empty_set _); eauto.
             eapply cc_approx_env_Empty_set. now intros Hc; eauto.
             intros Hc. eapply Hnin''. right; left. eassumption.
          -- intros Hc. apply Hnin''. eauto.
          -- eapply binding_in_map_antimon.
             eapply occurs_free_in_fun. eapply find_def_correct. eassumption.
             eapply binding_in_map_set_lists; [| now eauto ].
             eapply binding_in_map_def_funs. eassumption.
          -- eapply unique_bindings_fun_in_fundefs. eapply find_def_correct. eassumption. eassumption.
          -- rewrite Union_Same_set; [| now sets ]. eapply Union_Disjoint_l.
             eapply Disjoint_sym. eapply unique_bindings_fun_in_fundefs. eapply find_def_correct. eassumption. eassumption.
             eapply Disjoint_Included;[ | | eapply Hdis ]; sets.
             eapply Included_trans;
               [| eapply fun_in_fundefs_bound_var_fundefs; now eapply find_def_correct; eauto ]. now sets.
          -- eapply Disjoint_Included_l.
             eapply Included_trans. eapply image_monotonic. eapply Setminus_Included.
             eapply extend_fundefs'_image. eapply Disjoint_Singleton_l. intros Hc; eapply Hnin''.
             sets.
          -- (* Fun_inv *)
             eapply Fun_inv_from_GFun_inv; [ | | eassumption | rewrite M.gss; reflexivity ]. sets. reflexivity.
          -- eassumption.
          -- destruct FVs. 2:{ assert (Hc: Empty_set _ v). eapply H. now left. inv Hc. }
             intros Hc. exfalso; eauto.
      + eapply Hpre; eauto. constructor; eauto.
  Qed.

  (** Correctness of [project_var] *)
  Lemma project_var_correct k rho1 rho2 rho2' Scope GFuns Funs c genv Γ FVs x x' C S S'  :
    project_var clo_tag Scope Funs GFuns c genv Γ FVs S x x' C S' ->
    cc_approx_env_P cenv clo_tag Scope k boundG rho1 rho2 ->
    Fun_inv k rho1 rho2 Scope Funs genv ->
    GFun_inv k rho1 rho2 GFuns ->
    FV_inv k rho1 rho2 Scope Funs GFuns c Γ FVs ->

    ctx_to_rho C rho2 rho2' ->

    Disjoint _ S (Scope :|: (Funs \\ Scope) :|: GFuns :|: image genv (Funs \\ Scope) :|: FromList FVs :|: [set Γ])  ->

    ~ In _ S' x' /\
    cc_approx_env_P cenv clo_tag Scope k boundG rho1 rho2' /\
    Fun_inv k rho1 rho2' Scope Funs genv /\
    GFun_inv k rho1 rho2' GFuns /\
    FV_inv k rho1 rho2' Scope Funs GFuns c Γ FVs /\
    cc_approx_var_env cenv clo_tag k boundG rho1 rho2' x x'.
  Proof.
    intros Hproj Hcc Hfun Hgfun Henv Hctx Hd.
    inv Hproj.
    - inv Hctx. repeat split; eauto. intros Hc. eapply Hd. constructor; eauto. do 5 left. eassumption.
    - inv Hctx. inv H9.
      repeat split; eauto.
      + intros Hc. inv Hc. eauto.
      + eapply cc_approx_env_P_set_not_in_P_r. eassumption.
        intros Hc. eapply Hd. constructor; eauto. do 5 left; eauto.
      + (* TODO : make lemma *)
        intros f v Hnin Hin Hget.
        edestruct Hfun as
            [vs' [rho3 [B3 [f3 [rho4 [B4 [f4 [Hget1 [Heq2 [Ηnin2 [Hget2 Happrox]]]]]]]]]]]; eauto.
        subst. repeat eexists; eauto.
        rewrite M.gso; [ eassumption | ].
        intros Heq; subst; eapply Hd; eauto.
        constructor; eauto. do 2 left. right. eapply In_image. now constructor; eauto.
        rewrite M.gso. eassumption.
        intros Hc. subst; eapply Hd; constructor; eauto. do 4 left.
        right. constructor; eauto.
      + eapply GFun_inv_set_not_In_GFuns_r; [| eassumption ].
        intros Hc. eapply Hd; constructor; eauto.
      + eapply FV_inv_set_r. now intros Heq; subst; eapply Hd; eauto.
        eassumption.
      + intros v Hget. eexists. rewrite M.gss. split; eauto.
        edestruct Hfun as
            [vs' [rho3 [B3 [f3 [rho4 [B4 [f4 [Hget1 [Heq2 [Ηnin2 [Hget2 Happrox]]]]]]]]]]]; eauto.
        simpl in H8. rewrite Hget2 in H8; inv H8.
        rewrite Hget1 in H3; inv H3. eassumption.
    - inv Hctx. inv H11. inv H10. inv H13. repeat split.
      + intros Hc. inv Hc. eapply H4; eauto.
      + eapply cc_approx_env_P_set_not_in_P_r.
        eapply cc_approx_env_P_set_not_in_P_r. eassumption.
        intros Hc. eapply Hd. constructor. eapply H3. constructor; eauto.
        intros Hc. eapply Hd. constructor. eapply H2. do 5 left; eauto.
      + eapply Fun_inv_set_not_In_Funs_r_not_Γ.
        intros Hc. eapply Hd. constructor; eauto. do 4 left. now eauto.
        intros Hc. subst. eapply Hd; eauto.
        eapply Fun_inv_set_not_In_Funs_r_not_Γ; [| | eassumption ].
        intros Hc. subst. eapply Hd; eauto. constructor.
        now eapply H3. do 4 left. now eauto.
        intros Hc1. subst. eapply Hd; eauto. constructor. eapply H3. sets.
      + intros f v c1 Hin Hget.
        edestruct Hgfun as
            [vs' [rho3 [B3 [f3 [rho4 [B4 [Hget1 [Hget2 Happrox]]]]]]]]; eauto.
        simpl in H12.
        subst. repeat eexists; eauto.
        rewrite M.gso. 2:{ intros Heq; subst. eapply Hd. constructor; eauto. }
        rewrite M.gso. eassumption.
        intros Hc. subst; eapply Hd; constructor. eapply H3. do 3 left. now eauto.
      + eapply FV_inv_set_r. now intros Heq; subst; eapply Hd; eauto.
        eapply FV_inv_set_r. intros Heq; subst; eapply Hd; eauto. constructor.
        eapply H3. now sets. eassumption.
      + intros v' Hget. eexists. rewrite M.gss. split; eauto.
        edestruct Hgfun as
            [vs' [rho3 [B3 [f3 [rho4 [B4 [Hget1 [Hget2 Happrox]]]]]]]]; eauto.
        subst. simpl in H12.
        rewrite !M.gss, !M.gso in H12. rewrite Hget2 in H12. inv H12.
        eassumption. intros Hc. subst. eapply Hd. constructor.
        eapply H3; eauto. do 3 left. eauto.
    - inv Hctx. inv H13.
      repeat split; eauto.
      + intros Hc. inv Hc. eauto.
      + eapply cc_approx_env_P_set_not_in_P_r. eassumption.
        intros Hc. eapply Hd. constructor; eauto . do 5 left. eassumption.
      + intros f' v' Hnin Hin Hget.
        edestruct Hfun as
            [vs' [rho3 [B3 [f3 [rho4 [B4 [f4 [Hget1 [Heq2 [Ηnin2 [Hget2 Happrox]]]]]]]]]]]; eauto.
        subst. repeat eexists; eauto.
        rewrite M.gso; [ eassumption | ].
        intros Heq; subst; eapply Hd; eauto. constructor; eauto. do 2 left. right.
        eapply In_image. now constructor; eauto.
        rewrite M.gso. eassumption.
        intros Hc. subst; eapply Hd; constructor; eauto. do 4 left. right. constructor; eauto.
      + eapply GFun_inv_set_not_In_GFuns_r; [| eassumption ].
        intros Hc. eapply Hd; constructor; eauto.
      + eapply FV_inv_set_r. now intros Heq; subst; eapply Hd; eauto.
        eassumption.
      + intros v' Hget. eexists. rewrite M.gss. split; eauto.
        edestruct Henv as [g [ce [Hgetg [Hc Hinv]]]].
        intros Hc. subst. now inv H2.
        repeat subst_exp. eapply Forall2_nthN' in Hinv; eauto.
  Qed.

  (** Correctness of [project_vars] *)
  Lemma project_vars_correct k rho1 rho2 rho2'
        Scope Funs GFuns c genv Γ FVs xs xs' C S S' :
    project_vars clo_tag Scope Funs GFuns c genv Γ FVs S xs xs' C S' ->
    cc_approx_env_P cenv clo_tag Scope k boundG rho1 rho2 ->
    Fun_inv k rho1 rho2 Scope Funs genv ->
    GFun_inv k rho1 rho2 GFuns ->
    FV_inv k rho1 rho2 Scope Funs GFuns c Γ FVs ->
    ctx_to_rho C rho2 rho2' ->
    Disjoint _ S (Scope :|: (Funs \\ Scope) :|: GFuns :|: image genv (Funs \\ Scope) :|: FromList FVs :|: [set Γ]) ->
    cc_approx_env_P cenv clo_tag Scope k boundG rho1 rho2' /\
    Fun_inv k rho1 rho2' Scope Funs genv /\
    GFun_inv k rho1 rho2' GFuns /\
    FV_inv k rho1 rho2' Scope Funs GFuns c Γ FVs /\
    (forall vs,
       get_list xs rho1 = Some vs ->
       exists vs', get_list xs' rho2' = Some vs' /\
              Forall2 (cc_approx_val cenv clo_tag k boundG) vs vs').
  Proof.
    revert k rho1 rho2 rho2' Scope Funs genv Γ FVs xs' C S.
    induction xs;
      intros k rho1 rho2 rho2' Scope Funs genv Γ FVs xs' C S Hproj Hcc Hfun Hgfuns Henv Hctx Hd.
    - inv Hproj. inv Hctx. repeat split; eauto.
      eexists. split. reflexivity.
      inv H. now constructor.
    - inv Hproj.
      edestruct ctx_to_rho_comp_ctx_l as [rho'' [Hctx1 Hctx2]]; eauto.
      rewrite <- comp_ctx_f_correct. reflexivity.
      eapply project_var_correct in Hctx1; eauto.
      destruct Hctx1 as [Hnin [Hcc1 [Hfun1 [Hgfun1 [Henv1 Hcc_var]]]]].
      edestruct IHxs as [Hcc2 [Hfun2 [Hgfun2 [Henv2 Hyp]]]]; eauto.
      eapply Disjoint_Included_l; [| eassumption ].
      eapply project_var_free_set_Included; eassumption.
      repeat split; eauto. intros vs Hget.
      simpl in Hget. destruct (M.get a rho1) eqn:Hget'; try discriminate.
      destruct (get_list xs rho1) eqn:Hget_list; try discriminate.
      inv Hget. edestruct Hyp as [vs' [Hget_list' Hall]]; [ reflexivity |].
      edestruct Hcc_var as [v' [Hget''' Hcc''']]; eauto.
      eexists. split; eauto. simpl. rewrite Hget_list'.
      erewrite <- project_vars_get; eauto. rewrite Hget'''. reflexivity.
  Qed.



  Lemma Fun_inv_Union (k : nat) (rho1 : env) (rho2 : M.t val)
        (Scope1 Scope2 Funs : Ensemble var) B
        (genv : var -> var) G :
    Scope2 \subset Scope1 \\ (name_in_fundefs B) ->
    Fun_inv k rho1 rho2 Scope1 (Funs \\ name_in_fundefs B) genv ->
    Fun_inv k rho1 rho2 Scope2 (name_in_fundefs B) (extend_fundefs' genv B G) ->
    Fun_inv k rho1 rho2 (Scope1 \\ (name_in_fundefs B)) ((name_in_fundefs B) :|: Funs) (extend_fundefs' genv B G).
  Proof.
    intros Hsub1 Hfun1 Hfun2.
    intros f'' v Hnin Hin Hget.
    destruct (Decidable_name_in_fundefs B). destruct (Dec f'').
    - edestruct Hfun2 as
          [vs' [rho3 [B3 [f3 [rho4 [B4 [f4 [Hget1 [Heq2 [Ηnin2 [Hget2 Happrox]]]]]]]]]]];
        [| | eassumption |].
      eauto. eassumption.
      repeat eexists; eauto.
    - inv Hin; try contradiction.
      edestruct Hfun1 as
          [vs' [rho3 [B3 [f3 [rho4 [B4 [f4 [Hget1 [Heq2 [Ηnin2 [Hget2 Happrox]]]]]]]]]]];
        [| | eassumption |]. eauto. intros Hc. eapply Hnin. constructor; eauto.
      constructor; eauto.
      repeat eexists; eauto.
      rewrite extend_fundefs'_get_o. eassumption.
      eassumption.
  Qed.

  (* TODO move *)

  Lemma mult_le_n n m :
    1 <= m ->
    n <= n * m.
  Proof.
    rewrite Nat.mul_comm.
    edestruct Arith_base.mult_O_le_stt; eauto. lia.
  Qed.

  Lemma plus_le_mult  (a1 a2 b1 b2 b3 : nat) :
    b3 <= a1 ->
    1 <= b2 ->
    a2 <= b1 * b3 ->
    a1 + a2 <= (1 + b1) * a1 * b2.
  Proof.
    intros.
    rewrite <- Nat.mul_assoc, Nat.mul_add_distr_r.
    eapply Nat.add_le_mono.
    - simpl. rewrite <- plus_n_O.
      now eapply mult_le_n.
    - eapply Nat.le_trans. eapply Nat.le_trans. eassumption.
      eapply Nat.mul_le_mono. eauto. eassumption.
      rewrite Nat.mul_assoc. eapply mult_le_n. eassumption.
  Qed.


  Context (HOOT : forall j, post_OOT (boundL j)).

  Lemma Ecase_correct k rho1 rho2 rho2' C x x' c e e' l l' :
    ctx_to_rho C rho2 rho2' ->
    (* exp_ctx_len C <= 4 -> *)
    Forall2 (fun p1 p2 : ctor_tag * exp => fst p1 = fst p2) l l' ->
    cc_approx_var_env cenv clo_tag k boundG rho1 rho2' x x' ->
    cc_approx_exp cenv clo_tag k (boundL 0)
                  boundG (e, rho1) (e', rho2') ->
    cc_approx_exp cenv clo_tag k (boundL 0)
                  boundG (Ecase x l, rho1) (C |[ Ecase x' l' ]|, rho2) ->
    cc_approx_exp cenv clo_tag k (boundL 0) boundG (Ecase x ((c, e) :: l), rho1)
                  (C |[ Ecase x' ((c, e') :: l') ]|, rho2).
  Proof.
    intros Hctx Hall Henv Hcc1 Hcc2.
    eapply ctx_to_rho_cc_approx_exp.
    - intros. eapply Hpost_locals_r; eassumption.
    - eassumption.
    - eapply cc_approx_exp_case_cons_compat; try eassumption;
        [ | | | | eapply cc_approx_exp_ctx_to_rho; try eassumption ].
      + eapply HOOT.
      + eapply HPost.
      + eapply HPost.
      + intros. eapply Hcc1.
      + intros. eapply Hpost_locals_l; eauto.
      + intros. eapply Hpost_locals_l0; eauto.
  Qed.


  (* Axiom about prims. Currently assuming that they do not return functions *)
  Parameter primAxiom :
    forall f f' vs v k,
      M.get f pr = Some f' ->
      f' vs = Some v ->
      sizeOf_val k v = 0.


  Context (HPost_letapp : forall f x t xs e1 rho1 n k,
              k <= 4 + 4 * length xs  ->
              post_letapp_compat_cc' cenv clo_tag f x t xs e1 rho1 (boundL n) (boundL (n + k)) boundG)

          (HPost_letapp_OOT : forall f x t xs e1 rho1 n k,
              k <= 4 + 4 * length xs ->
              post_letapp_compat_cc_OOT' clo_tag f x t xs e1 rho1 (boundL (n + k)) boundG).


  Context (HPost_app :
             forall k v t l rho1,  k <= 4 + 4 * length l -> post_app_compat_cc' clo_tag v t l rho1 (boundL k) boundG).

  Context (Hbase : forall j, post_base (boundL j)).

  Lemma exp_ctx_len_leq_aux :
    (forall C, exp_ctx_len C <= sizeOf_exp_ctx C) /\
    (forall C, fundefs_ctx_len C <= sizeOf_fundefs_ctx C).
  Proof.
    exp_fundefs_ctx_induction IHC IHB; intros; simpl; try lia.
  Qed.


  (** Correctness of [Closure_conversion] *)
  Lemma Closure_conversion_correct k rho rho' e e' Scope Funs GFuns c genv Γ FVs C :
    (* [Scope] invariant *)
    cc_approx_env_P cenv clo_tag Scope k boundG rho rho' ->
    (* [Γ] (the current environment parameter) is not bound in e *)
    ~ In _ (bound_var e) Γ ->

    (* The free variables of e are defined in the environment *)
    binding_in_map (occurs_free e) rho ->

    (* The blocks of functions have unique function names *)
    unique_bindings e ->
    (* function renaming is injective in the [Funs] subdomain *)
    (* injective_subdomain (Funs \\ Scope :|: GFuns) σ -> *)

    Disjoint _ (Funs \\ Scope :|: GFuns) (bound_var e) ->
    Disjoint _ (image genv (Funs \\ Scope)) (bound_var e) ->

    (* [Fun] invariant *)
    Fun_inv k rho rho' Scope Funs genv ->
    (* Free variables invariant *)
    FV_inv k rho rho' Scope Funs GFuns c Γ FVs ->
    (* Global functions invariant *)
    GFun_inv k rho rho' GFuns ->
    (* [e'] is the closure conversion of [e] *)
    Closure_conversion clo_tag Scope Funs GFuns c genv Γ FVs e e' C ->
    cc_approx_exp cenv clo_tag k (boundL 0) boundG (e, rho) (C |[ e' ]|, rho').
  Proof with now eauto with Ensembles_DB.
    revert k e rho rho' e' Scope Funs GFuns c genv Γ FVs C.
    induction k as [k IHk] using lt_wf_rec1. intros e.
    revert k IHk; induction e using exp_ind';
      intros k IHk rho1 rho2 e' Scope Funs GFuns c' genv Γ FVs C Happrox Hnin HFVs Hun Hd Hd' Hfun Hgfun Henv Hcc.
    - (* Case Econstr *)
      inv Hcc.
      assert(Hadm : sizeOf_exp_ctx C <= 4*length l) by (eapply project_vars_sizeOf_ctx_exp; eauto).


      edestruct (@binding_in_map_get_list val) with (xs := l) as [vs Hgetvs]; eauto. normalize_occurs_free...

      edestruct project_vars_ctx_to_rho as [rho2' Hto_rho]; eauto. now sets.
      edestruct project_vars_correct as [Happ [Hfun' [Hgfun' [Henv' Hvar]]]]; eauto. now sets.
      edestruct Hvar as [v' [Hget' Happ']]; eauto.
      eapply ctx_to_rho_cc_approx_exp; eauto.
      + eapply cc_approx_exp_constr_compat with (P1 := boundL 0).
        * eapply HPost.
        * simpl. eapply HOOT.
        * eapply Forall2_cc_approx_var_env; eauto.
        * intros vs1 vs2 Hget Hall.
          { eapply IHe; [ | | | | | | | | | | eassumption ].
            * eauto.
            * eapply cc_approx_env_P_extend with (v2 := Vconstr t vs2).
              eapply cc_approx_env_P_antimon; [ eassumption |]...
              rewrite cc_approx_val_eq. constructor; eauto.
            * now eauto.
            * eapply binding_in_map_antimon; [| eapply binding_in_map_set; eassumption ].
              eapply occurs_free_Econstr_Included.
            * inv Hun. eassumption.
            * eapply Disjoint_Included; [| | eapply Hd ].
              normalize_bound_var... now sets.
            * eapply Disjoint_Included_r;
              [| eapply Disjoint_Included_l; [ apply image_monotonic | now apply Hd' ]].
              normalize_bound_var... now eauto with Ensembles_DB.
            * eapply Fun_inv_set_In_Scope_l. now eauto.
              eapply Fun_inv_set_In_Scope_r_not_Γ. now eauto.
              eapply Disjoint_In_l. eapply Disjoint_sym. eapply Disjoint_Included_l; [| eapply Hd' ]; sets.
              now constructor.
              eapply Fun_inv_mon. eassumption.
            * eapply FV_inv_set_In_Scope_l. now constructor.
              eapply FV_inv_set_r. intros Hc. eapply Hnin.
              subst. now eauto. now eapply FV_inv_extend_Scope_GFuns.
            * eapply GFun_inv_set_not_In_GFuns_l.
              intros Hc. eapply Hd. constructor; eauto.
              eapply GFun_inv_set_not_In_GFuns_r.
              intros Hc. eapply Hd. constructor; eauto. eassumption. }
    - (* Case [Ecase x []] *)
      inv Hcc. inv H12.
      edestruct HFVs with (x := v) as [v' Hgetv]. normalize_occurs_free...
      edestruct project_var_ctx_to_rho as [rho2' Hto_rho]; eauto. now sets.
      eapply ctx_to_rho_cc_approx_exp; eauto.
      eapply cc_approx_exp_case_nil_compat; eauto.
      assert(Hadm : sizeOf_exp_ctx C <= 4) by (eapply project_var_sizeOf_ctx_exp; eauto).
      eapply HOOT.
    - (* Case [Ecase x ((c, p) :: pats] *)
      inv Hcc.
      inversion H12 as [ | [c1 p1] [c2 p2] l1 l2 [Heq [C' [e' [Heq' Hcc]]]] Hall ];
        simpl in Heq, Heq'; subst.
      repeat normalize_bound_var_in_ctx.
      assert(Hadm : sizeOf_exp_ctx C <= 4) by (eapply project_var_sizeOf_ctx_exp; eauto).
      edestruct HFVs with (x := v) as [v' Hgetv]. normalize_occurs_free...
      edestruct project_var_ctx_to_rho as [rho2' Hto_rho]; eauto. now sets.
      edestruct project_var_correct as [Happ [Hfun' [Hgfun' [Henv' Hvar]]]]; eauto. now sets.
      edestruct Hvar as [Hget' Happ']; eauto.
      eapply Ecase_correct; try eassumption.
      + inv H12. eapply Forall2_monotonic; try eassumption.
        firstorder.
      + eapply IHe; try eassumption.
        * now intros Hc; eapply Hnin; eauto.
        * eapply binding_in_map_antimon; [|  eassumption ].
          eapply occurs_free_Ecase_Included. now constructor.
        * inv Hun. eassumption.
        * eauto with Ensembles_DB.
        * sets.
      + eapply IHe0; try eassumption.
        * now eauto.
        * eapply binding_in_map_antimon; [| eassumption ].
          intros x Hin. inv Hin; eauto.
        * inv Hun. eassumption.
        * eauto with Ensembles_DB.
        * sets.
        * econstructor; eauto.
    - (* Case Eproj *)
      inv Hcc.
      assert (Hadm : sizeOf_exp_ctx C <= 4) by (eapply project_var_sizeOf_ctx_exp; eauto).
      edestruct HFVs with (x := v0) as [v' Hgetv]. normalize_occurs_free...

      edestruct project_var_ctx_to_rho as [rho2' Hto_rho]; eauto. now xsets.
      edestruct project_var_correct as [Happ [Hfun' [Hgfun' [Henv' Hvar]]]]; eauto. now sets.
      edestruct Hvar as [Hget' Happ']; eauto.
      eapply ctx_to_rho_cc_approx_exp; eauto.
      + eapply cc_approx_exp_proj_compat with (P1 := boundL 0).
        * eapply HPost_proj; eauto.
        * eapply HOOT; simpl; lia.
        * eassumption.
        * intros v1' v2' c1 vs1 Hget Hin Hv.
          { eapply IHe; [ now eauto | | | | | | | | | | eassumption ].
            * eapply cc_approx_env_P_extend.
              eapply cc_approx_env_P_antimon; [ eassumption |]...
              eassumption.
            * now eauto.
            * eapply binding_in_map_antimon; [| eapply binding_in_map_set; eassumption ].
              eapply occurs_free_Eproj_Included.
            * inv Hun. eassumption.
            * eapply Disjoint_Included; [ | | eapply Hd ].
              normalize_bound_var... now eauto with Ensembles_DB.
            * eapply Disjoint_Included_r;
              [| eapply Disjoint_Included_l; [ apply image_monotonic | now apply Hd' ]].
              normalize_bound_var... now eauto with Ensembles_DB.
            * eapply Fun_inv_set_In_Scope_l. now eauto.
              eapply Fun_inv_set_In_Scope_r_not_Γ. now eauto.
              eapply Disjoint_In_l. eapply Disjoint_sym.
              eapply Disjoint_Included_l; [| eapply Hd' ]; sets.
              now constructor.
              eapply Fun_inv_mon. eassumption.
            * eapply FV_inv_set_In_Scope_l. now constructor.
              eapply FV_inv_set_r. intros Hc. eapply Hnin.
              subst. now eauto. now eapply FV_inv_extend_Scope_GFuns.
            * eapply GFun_inv_set_not_In_GFuns_l.
              intros Hc. eapply Hd. constructor; eauto.
              eapply GFun_inv_set_not_In_GFuns_r.
              intros Hc. eapply Hd. constructor; eauto.
              eassumption. }
    - (* Case letapp *)
      inv Hcc.
      assert (Hadm : sizeOf_exp_ctx C <= 4 + 4 * length ys).
      { eapply Nat.le_trans. eapply project_vars_sizeOf_ctx_exp; eauto. simpl; lia. }
      edestruct (HFVs f) as [v' Hgetv]. normalize_occurs_free...
      edestruct (@binding_in_map_get_list val) with (xs := ys) as [vs Hgetvs]; eauto. normalize_occurs_free...

      edestruct project_vars_ctx_to_rho as [rho2' Hto_rho]; eauto. now sets. simpl. rewrite Hgetv, Hgetvs. reflexivity.
      edestruct project_vars_correct as [Happ [Hfun' [Hgfun' [Henv' Hvar]]]]; eauto.  now sets.
      edestruct Hvar as [v'' [Hget' Happ']]; eauto.
      simpl. rewrite Hgetv, Hgetvs. reflexivity.
      simpl in Hget'.
      destruct (M.get f' rho2') eqn:Hgetf';
        destruct (get_list ys' rho2') eqn:Hgetvs'; try congruence. inv Hget'.
      inv Happ'.
      assert (Hv := H2). rewrite cc_approx_val_eq in H2.

(*    destruct v' as [ | | ]; try contradiction.
      simpl in H2. destruct l0 as [ | ? [|]] ; try contradiction; destruct v0;  try contradiction.
      destruct v2; try contradiction.
      edestruct H2 with (j := 0) as [Gamma [xs2 [e2' [rho2'' [Heqc [Hfdef [Hset Hlt]]]]]]]; [ | now eauto | now eauto | ].
      eapply Forall2_length. eassumption. subst. *)

      assert (Hnin' :  ~ In var (f' |: FromList ys') f'').
      { eapply Disjoint_In_l; [| eassumption ].
        rewrite <- FromList_cons. eapply project_vars_not_In_free_set. eassumption.
        xsets. }

      eapply ctx_to_rho_cc_approx_exp; eauto.
      eapply cc_approx_exp_letapp_compat with (P1 := boundL 0) (rho1 := rho1) (f1 := f).
      + eapply HPost_letapp. eapply Nat.le_trans. eapply exp_ctx_len_leq_aux. eassumption.
      + eapply HPost_letapp_OOT. eapply Nat.le_trans. eapply exp_ctx_len_leq_aux. eassumption.
      + eapply HOOT.
      + rewrite (Union_commut [set f']), <- Union_assoc. intros Hc. inv Hc; eauto. inv H. contradiction.
        revert H. eapply Disjoint_In_l; [| eassumption ].
        rewrite <- FromList_cons. eapply project_vars_not_In_free_set. eassumption.
        xsets.
      + eassumption.
      + intros v3 v4. repeat subst_exp. eexists; split; eauto.
      + eapply Forall2_cc_approx_var_env; eauto.
      + intros m v4 v5 rho2'' Hleq' Hvs Hctx. inv Hctx. inv H11. inv H19. repeat subst_exp.
        eapply cc_approx_exp_monotonic.
        eapply IHe with (k := m); [ | | | | | | | | | | eassumption ].
        * intros. eapply IHk; eauto. lia.
        * eapply cc_approx_env_P_extend; [| eassumption ].
          eapply cc_approx_env_P_set_not_in_P_r.
          eapply cc_approx_env_P_set_not_in_P_r.
          eapply cc_approx_env_P_antimon.
          eapply cc_approx_env_P_monotonic; [| eassumption ]. lia. now sets.
          rewrite Setminus_Union_distr. rewrite Setminus_Same_set_Empty_set, Union_Empty_set_neut_l.
          eapply Disjoint_In_l; [| eassumption ].
          eapply Disjoint_Included; [ | | eapply H4 ]; sets.
          eapply project_vars_free_set_Included. eassumption.

          rewrite Setminus_Union_distr. rewrite Setminus_Same_set_Empty_set, Union_Empty_set_neut_l.
          eapply Disjoint_In_l; [| eassumption ].
          eapply Disjoint_Included; [ | | eapply H4 ]; sets.
          eapply project_vars_free_set_Included. eassumption.
        * now eauto.
        * eapply binding_in_map_antimon; [| eapply binding_in_map_set; eassumption ].
          eapply occurs_free_Eletapp_Included.
        * inv Hun. eassumption.
        * eapply Disjoint_Included; [| | eapply Hd ].
          normalize_bound_var... now sets.
        * eapply Disjoint_Included_r;
            [| eapply Disjoint_Included_l; [ apply image_monotonic | now apply Hd' ]].
          normalize_bound_var... now eauto with Ensembles_DB.
        * eapply Fun_inv_set_In_Scope_r_not_Γ. now eauto.
          eapply Disjoint_In_l. eapply Disjoint_sym.
          eapply Disjoint_Included_l; [| eapply Hd' ]; sets.
          now constructor.

          eapply Fun_inv_set_not_In_Funs_r_not_Γ.
          eapply Disjoint_In_l; [| eassumption ].
          eapply Disjoint_Included; [| | eapply H4 ].
          eauto 10 with Ensembles_DB functions_BD.
          eapply project_vars_free_set_Included. eassumption.
          eapply Disjoint_In_l; [| eassumption ].
          eapply Disjoint_Included; [| | eapply H4 ]. xsets.
          eapply project_vars_free_set_Included. eassumption.

          eapply Fun_inv_set_not_In_Funs_r_not_Γ.
          eapply Disjoint_In_l; [| eapply H15 ].
          eapply Disjoint_Included; [| | eapply H4 ].
          now eauto 10 with Ensembles_DB functions_BD.
          eapply project_vars_free_set_Included. now xsets.

          eapply Disjoint_In_l; [| eapply H15 ].
          eapply Disjoint_Included; [| | eapply H4 ].
          now eauto 10 with Ensembles_DB functions_BD.
          eapply project_vars_free_set_Included. eassumption.

          apply Fun_inv_set_In_Scope_l. now eauto.
          eapply Fun_inv_monotonic. shelve. eapply Fun_inv_mon. eassumption. lia.
        * eapply FV_inv_set_In_Scope_l. now constructor.
          eapply FV_inv_set_r. intros Hc. eapply Hnin.
          subst. now eauto.
          eapply FV_inv_set_r; [| eapply  FV_inv_set_r; eauto ].
          intros Hc; subst. eapply H4. constructor.
          eapply project_vars_free_set_Included. eassumption. eassumption. now sets.
          intros Hc; subst. eapply H4. constructor.
          eapply project_vars_free_set_Included. eassumption. eapply H15. now sets.
          eapply FV_inv_extend_Scope_GFuns. eapply FV_inv_monotonic. eassumption. lia.
        * eapply GFun_inv_set_not_In_GFuns_l.
          intros Hc. eapply Hd. now constructor; eauto.
          eapply GFun_inv_set_not_In_GFuns_r.
          intros Hc. eapply Hd. now constructor; eauto.
          eapply GFun_inv_set_not_In_GFuns_r.
          eapply Disjoint_In_l; [| eassumption ].
          eapply Disjoint_Included; [| | eapply H4 ]. now sets.
          eapply project_vars_free_set_Included. eassumption.
          eapply GFun_inv_set_not_In_GFuns_r.
          eapply Disjoint_In_l; [| eassumption ].
          eapply Disjoint_Included; [| | eapply H4 ].
          eauto 10 with Ensembles_DB functions_BD.
          eapply project_vars_free_set_Included. eassumption.
          eapply GFun_inv_antimon. eapply GFun_inv_monotonic; eauto. sets.
        * lia.
    - (* Case Efun -- the hardest one! *)
      inv Hcc.
      assert (Hsub : FromList FVs' \subset occurs_free_fundefs f2).
      { rewrite <- H1... }
      specialize (occurs_free_fundefs_cardinality _ _ Hsub H2); intros Hlen.
      assert (Ha : exists vs, get_list FVs' rho1 = Some vs).
      { eapply In_get_list. intros x Hin. eapply HFVs.
        rewrite occurs_free_Efun. left. eauto. }
      destruct Ha as [vs Hget_list].
      (* sizes of evaluation contexts *)
      assert (HC1 : sizeOf_exp_ctx C' <= 4 * (length FVs')) by
          (eapply Nat.le_trans; [ now eapply project_vars_sizeOf_ctx_exp; eauto | lia ]).

      edestruct project_vars_ctx_to_rho as [rho2' Hto_rho]; [ | eassumption | | | | | ]; eauto. now sets.
      edestruct project_vars_correct as [Happ [Hfun' [Henv' [Hgfun' Hvar]]]]; eauto. now sets.
      edestruct Hvar as [v' [Hget' Happ']]; eauto. rewrite <- app_ctx_f_fuse. simpl.
      eapply ctx_to_rho_cc_approx_exp;  try (now intros; eauto).

      assert (Hfuns : Fun_inv k (def_funs f2 f2 rho1 rho1) (def_funs B' B' (M.set Γ' (Vconstr c'0 v') rho2') (M.set Γ' (Vconstr c'0 v') rho2'))
                                (Empty_set var) (name_in_fundefs f2) (extend_fundefs' genv f2 Γ') /\
                      GFun_inv k (def_funs f2 f2 rho1 rho1) (def_funs B' B' (M.set Γ' (Vconstr c'0 v') rho2') (M.set Γ' (Vconstr c'0 v') rho2'))
                               GFuns'
               ).
        { eapply Closure_conversion_fundefs_correct with (c := c'0) ; eauto.
          * inv Hun. eassumption.
          * eapply binding_in_map_antimon; [| eassumption ].
            intros x H. eapply Free_Efun2. eassumption.
          * eapply GFun_inv_set_not_In_GFuns_r.
            intros Hc. eapply H5. now constructor; eauto.
            eassumption.
          * edestruct Hvar as [vs' [Hget_list' Hall]]; eauto.
            eapply FV_inv_strong_Forall2. eassumption. rewrite M.gss. reflexivity.
            eassumption.
          * eapply Disjoint_Included; [ | | eapply Hd ]. normalize_bound_var... sets.
          * eapply closure_conversion_fundefs_Same_set_image. eassumption.
          * intros Hc. eapply H5. constructor; eauto. normalize_bound_var.
            do 2 left. eapply name_in_fundefs_bound_var_fundefs.
            eapply closure_conversion_fundefs_Same_set_image; eassumption. }
        destruct Hfuns as [Hf Hg].

        eapply ctx_to_rho_cc_approx_exp with (C := Econstr_c Γ' c'0 FVs'' Hole_c);
          try (now intros; eauto).
        econstructor. eassumption. now constructor.

        eapply cc_approx_exp_fun_compat with (P1 := boundL 0).
      + eapply HPost_fun. eauto.
      + eapply HOOT.
        + { eapply IHe with (GFuns := GFuns') (Funs := name_in_fundefs f2 :|: Funs)
                            (Scope := Scope \\ name_in_fundefs f2)
                            (genv := extend_fundefs' genv f2 Γ'); (try now eapply H17); eauto.
            * intros. eapply IHk; eauto. lia.
            * eapply cc_approx_env_P_def_funs_not_In_P_l.
              now eauto with Ensembles_DB.
              eapply cc_approx_env_P_def_funs_not_In_P_r. sets.
              erewrite <- closure_conversion_fundefs_Same_set_image with (B2 := B'); [| eassumption ].
              now sets.

              eapply cc_approx_env_P_set_not_in_P_r.
              eapply cc_approx_env_P_antimon; [ eapply cc_approx_env_P_monotonic; [| eassumption ] |].
              lia. now sets.
              intros Hin. inv Hin. eapply H5. constructor; eauto. right. left. now eauto.
            * eapply binding_in_map_antimon.
              eapply Included_trans. now eapply occurs_free_Efun_Included.
              rewrite Union_commut. now apply Included_refl.
              apply binding_in_map_def_funs. eassumption.
            * inv Hun. eassumption.
            * rewrite Setminus_Setminus_Same_set; sets; tci.
              rewrite Setminus_Union_distr. rewrite <- !Union_assoc, Union_Same_set; [| now sets ].
              eapply Disjoint_Included_l.
              eapply Included_Union_compat. reflexivity. eapply Included_Union_compat. reflexivity.
              eapply add_global_funs_included_r. eassumption.
              rewrite (Union_Same_set (name_in_fundefs _)); [| now sets ].
              rewrite !Union_assoc. eapply Union_Disjoint_l.
              -- repeat normalize_bound_var_in_ctx. sets.
              -- inv Hun. eapply Disjoint_Included_l. eapply name_in_fundefs_bound_var_fundefs. now sets.
            * eapply Disjoint_Included_l.
              eapply extend_fundefs'_image_Included'.
              eapply Union_Disjoint_l.
              eapply Disjoint_Included; [| | eapply H5 ]; sets. normalize_bound_var...
              eapply Disjoint_Included_l with (s3 := image genv (Funs \\ Scope)).
              eapply image_monotonic. rewrite !Setminus_Union_distr.
              eapply Union_Included; sets.
              eapply Included_trans. eapply Included_Setminus_compat; [| reflexivity ].
              eapply Setminus_Setminus_Included. tci. sets.
              eapply Disjoint_Included; [| | eapply Hd' ]; sets. normalize_bound_var...
            * eapply Fun_inv_Union; [| | eapply Fun_inv_monotonic; eauto ]. sets. 2:{ lia. }
              eapply Fun_inv_def_funs.
              ** erewrite <- closure_conversion_fundefs_Same_set_image; [| eassumption ].
                 eapply Disjoint_Included_l. eapply name_in_fundefs_bound_var_fundefs.
                 repeat normalize_bound_var_in_ctx. sets.
              ** erewrite <- closure_conversion_fundefs_Same_set_image; [| eassumption ].
                 eapply Disjoint_Included_r. eapply name_in_fundefs_bound_var_fundefs.
                 repeat normalize_bound_var_in_ctx.
                 eapply Disjoint_Included; [ | | eapply Hd ]; sets.
              ** eapply Fun_inv_set_not_In_Funs_r_not_Γ; [| | ].
                 intros Hc. eapply H5. constructor; eauto.
                 right. left. now eauto.
                 intros Hc. subst. eapply H5. constructor. now eauto.
                 now eauto. eapply Fun_inv_monotonic; eauto. lia.
            * eapply FV_inv_antimonotonic_add_global_funs; [ | | eassumption | ]; tci.
              eapply FV_inv_def_funs.
              ** intros Hc. eapply Hnin. constructor.
                  now eapply name_in_fundefs_bound_var_fundefs.
              ** intros Hc.
                 erewrite <- closure_conversion_fundefs_Same_set_image in Hc; [| eassumption ].
                 eapply Hnin. constructor.
                  now eapply name_in_fundefs_bound_var_fundefs.
              ** eapply FV_inv_set_r.
                 intros Hc. subst. eapply H5. constructor; eauto.
                 eapply FV_inv_monotonic. eassumption. lia.
              ** sets.
            * eapply GFun_inv_fuse with (names := name_in_fundefs f2); tci; sets.
              ** eapply GFun_inv_def_funs_not_In_GFuns_r.
                 erewrite <- closure_conversion_fundefs_Same_set_image with (B2 := B'); eauto.
                 now sets.
                 eapply GFun_inv_def_funs_not_In_GFuns_l. sets.
                 eapply GFun_inv_set_not_In_GFuns_r.
                 intros Hc. eapply H5. constructor; eauto. inv Hc. now sets.
                 eapply GFun_inv_antimon. eapply GFun_inv_monotonic. eassumption.
                 lia. sets.
              ** eapply GFun_inv_monotonic. eassumption. lia. }
    - (* Case Eapp *)
      inv Hcc.
      assert(Hadm : sizeOf_exp_ctx C <= 4 * length l + 4)
        by (eapply Nat.le_trans; [ now eapply project_vars_sizeOf_ctx_exp; eauto | simpl; lia ]).
      edestruct HFVs with (x := v) as [v' Hgetv]. normalize_occurs_free...
      edestruct (@binding_in_map_get_list val) with (xs := l) as [vs Hgetvs]; eauto. normalize_occurs_free...

      edestruct project_vars_ctx_to_rho as [rho2' Hto_rho]; eauto. now sets.
      simpl. rewrite Hgetv, Hgetvs. reflexivity.

      edestruct project_vars_correct as [Happ [Hfun' [Hgfun' [Henv' Hvar]]]]; eauto. now sets.
      edestruct Hvar as [v'' [Hget' Happ']]; eauto.
      simpl. rewrite Hgetv, Hgetvs. reflexivity.
      eapply ctx_to_rho_cc_approx_exp; [ | eassumption | ].
      { intros; eapply Hpost_locals_r. eassumption. eassumption. }

      simpl in Hget'. destruct (M.get f' rho2') eqn:Hgetf'; try congruence.
      destruct (get_list ys' rho2') eqn:Hgetys'; try congruence. inv Hget'. inv Happ'.
      assert (Hnin' :  ~ In var (f' |: FromList ys') f'').
      { eapply Disjoint_In_l; [| eassumption ].
        rewrite <- FromList_cons. eapply project_vars_not_In_free_set. eassumption.
        eapply Disjoint_Included_r; [| eassumption ].
        repeat (eapply Union_Included; [| now sets ]). now sets. }

      eapply cc_approx_exp_app_compat.
      + eapply HPost_app.
        simpl (0 + _). eapply Nat.le_trans. eapply exp_ctx_len_leq_aux. rewrite Nat.add_comm. eassumption.
      + eapply HOOT.
      + rewrite (Union_commut [set f']), <- Union_assoc. intros Hc. inv Hc; eauto. inv H. contradiction.
        revert H. eapply Disjoint_In_l; [| eassumption ].
        rewrite <- FromList_cons. eapply project_vars_not_In_free_set. eassumption.
        eapply Disjoint_Included_r; [| eassumption ].
        repeat (eapply Union_Included; [| now sets ]). now sets.
      + eassumption.
      + intros x Hget. repeat subst_exp. eexists; split; eauto.
      + eapply Forall2_cc_approx_var_env; eauto.

    - (* Case Eprim_val *)
     inv Hcc.
     cbn [app_ctx_f].
     eapply cc_approx_exp_prim_val_compat.
     eapply HOOT.

    (* Case Eprim *)
    - inv Hcc.
      assert(Hadm : sizeOf_exp_ctx C <= 4 * length l) by (eapply project_vars_sizeOf_ctx_exp; eauto).
      edestruct (@binding_in_map_get_list val) with (xs := l) as [vs Hgetvs]; eauto.
      normalize_occurs_free...

      edestruct project_vars_ctx_to_rho as [rho2' Hto_rho]; eauto. now sets.
      edestruct project_vars_correct as [Happ [Hfun' [Hgfun' [Henv' Hvar]]]]; eauto. now sets.
      edestruct Hvar as [v' [Hget' Happ']]; eauto.
      eapply ctx_to_rho_cc_approx_exp; eauto.
      + eapply cc_approx_exp_prim_compat.
        * eapply HOOT; eauto.
        * eapply Forall2_cc_approx_var_env; eauto.
(*      * intros vs1 vs2 l1 f Hgetl Hgetf Happf Hall.
        { eapply IHe with (c := c'); [ now eauto | | | | | | | | | | | eassumption ].
          * eapply cc_approx_env_P_extend with (v2 := vs2).
            eapply cc_approx_env_P_antimon; [ eassumption |]...
            eassumption.
          * now eauto.
          * eapply binding_in_map_antimon; [| eapply binding_in_map_set; eassumption ].
            eapply occurs_free_Eprim_Included.
          * intros f1 Hfin. eauto.
          * eapply injective_subdomain_antimon. eassumption. sets.
          * eapply Disjoint_Included_r;
              [| eapply Disjoint_Included_l; [ apply image_monotonic | now apply Hd ]].
            normalize_bound_var... now eauto with Ensembles_DB.
          * eapply Disjoint_Included_r;
              [| eapply Disjoint_Included_l; [ apply image_monotonic | now apply Hd' ]].
            normalize_bound_var... now eauto with Ensembles_DB.
          * eapply Fun_inv_set_In_Scope_l. now eauto.
            eapply Fun_inv_set_In_Scope_r_not_Γ. now eauto.
            eapply Disjoint_In_l. eapply Disjoint_sym.
            eapply Disjoint_Included_l; [| eapply Hd' ]; sets. now constructor.
            eapply Fun_inv_mon; [ | now eauto ].
            eapply Disjoint_Included; [| | eapply Hd ]; sets.
          * eapply FV_inv_set_In_Scope_l. now constructor.
            eapply FV_inv_set_r. intros Hc. eapply Hnin.
            subst. now eauto. now eapply FV_inv_extend_Scope_GFuns.
          * eapply GFun_inv_set_not_In_GFuns_l. intros Hc. inv Hc. eapply H0. reflexivity.
            eapply GFun_inv_set_not_In_GFuns_r.
            intros Hc. eapply Hd. constructor. rewrite image_Union.
            right. eapply image_monotonic; [| eassumption ]; sets. sets.
            eapply GFun_inv_Scope_extend; sets.
            eapply Disjoint_Included; [| | now eapply Hd ].
            normalize_bound_var... sets.
            eapply GFun_inv_antimon; sets. } *)
    (* Case Ehalt *)
    - inv Hcc.
      assert(Hadm : sizeOf_exp_ctx C <= 4) by (eapply project_var_sizeOf_ctx_exp; eauto).
      edestruct HFVs with (x := v) as [v' Hgetv]. normalize_occurs_free...
      edestruct project_var_ctx_to_rho as [rho2' Hto_rho]; eauto.
      eapply Disjoint_Included_r; [| eassumption ]. now sets.
      edestruct project_var_correct as [Hnin' [Happ [Hfun' [Hgfun' [Henv' Hvar]]]]]; eauto. now sets.
      edestruct Hvar as [v'' [Hget' Happ']]; eauto.
      eapply ctx_to_rho_cc_approx_exp; eauto.
      eapply cc_approx_exp_halt_compat. eapply HOOT.

      eapply Hbase.
      eassumption.
      Unshelve. assumption.
  Qed.


  Corollary Closure_conversion_correct_top k rho rho' e e' Scope c genv Γ C :
    cc_approx_env_P cenv clo_tag Scope k boundG rho rho' ->
    ~ In _ (bound_var e) Γ ->
    binding_in_map (occurs_free e) rho ->
    unique_bindings e ->
    Closure_conversion clo_tag Scope (Empty_set _) (Empty_set _) c genv Γ [] e e' C ->

    cc_approx_exp cenv clo_tag k (boundL 0) boundG (e, rho) (C |[ e' ]|, rho').
  Proof with now eauto with Ensembles_DB.
    intros.
    eapply Closure_conversion_correct; try eassumption.
    - now sets.
    - normalize_sets. rewrite image_Empty_set. sets.
    - intro; intros. inv H5.
    - intro. exfalso; eauto.
    - intro; intros. inv H4.
  Qed.


  (* Correctness of the CC program *)

  Lemma populate_map_FVmap_inv s map Scope Funs GFuns FVs:
    FVmap_inv map Scope Funs GFuns FVs ->
    FVmap_inv (populate_map s map) (Union _ (FromSet s) Scope) Funs GFuns FVs.
  Proof.
    unfold populate_map. rewrite PS.fold_spec.
    unfold FromSet. generalize (PS.elements s). intros l.
    revert Scope map. induction l as [| x l IHl ]; intros Scope map Hinv.
    - simpl. rewrite FromList_nil, Union_Empty_set_neut_l. eassumption.
    - simpl in *. rewrite FromList_cons, (Union_commut (Singleton _ _) _), <- Union_assoc.
      eapply IHl. apply FVmap_inv_set_bound. eassumption.
  Qed.

  Corollary populate_map_FVmap_inv_init e :
    FVmap_inv (populate_map (exp_fv e) (Maps.PTree.empty VarInfo))
              (occurs_free e) (Empty_set positive) (Empty_set positive) [].
  Proof.
    rewrite <- (Union_Empty_set_neut_r (occurs_free e)). rewrite exp_fv_correct.
    eapply populate_map_FVmap_inv.
    split; [| split; [| split; [| split ]]].
    + split; sets.
      intros x Hin. unfold In in Hin. rewrite M.gempty in Hin. inv Hin.
    + split; sets.
      intros x Hin. unfold In in Hin. rewrite M.gempty in Hin. inv Hin. inv H.
    + intros. destructAll. inv H.
    + rewrite M.gempty in H. inv H.
    + rewrite M.gempty in H. inv H.
  Qed.

  Lemma populate_map_binding_in_not_in_map S s m:
    Disjoint _ (FromSet s) S ->
    binding_not_in_map S m ->
    binding_not_in_map S (populate_map s m).
  Proof.
     unfold populate_map. rewrite PS.fold_spec.
     unfold FromSet. generalize (PS.elements s). intros l.
     revert S m. induction l; intros S m.
     - simpl. eauto.
     - repeat normalize_sets.
       intros Hd Hnin x Hin. simpl. eapply IHl with (S := S); [| | eassumption ].
       now sets.
       eapply binding_not_in_map_set_not_In_S. eassumption.
       intros Hc. eapply Hd. constructor; eauto.
  Qed.

  Corollary populate_map_binding_in_not_in_map_init S s:
    Disjoint _ (FromSet s) S ->
    binding_not_in_map S (populate_map s (M.empty _)).
  Proof.
    intros. eapply populate_map_binding_in_not_in_map. eassumption.
    intros x Hin. rewrite M.gempty. reflexivity.
  Qed.

  Opaque preord_exp'.

  Lemma unique_bindings_fundef_names_unique_mut :
    (forall e, unique_bindings e -> fundefs_names_unique e) /\
    (forall B, unique_bindings_fundefs B -> fundefs_names_unique_fundefs B).
  Proof.
    exp_defs_induction IHe IHl IHB; intros Hun; inv Hun;
    try now (intros B Hin; inv Hin; eapply IHe; eauto).
    - intros B Hin. inv Hin. inv H3.
    - intros B Hin. inv Hin. inv H6.
      + inv H. eapply IHe; eauto.
      + eapply IHl. eassumption.
        econstructor. eassumption. eassumption.
    - intros B Hin. inv Hin.
      + eapply unique_bindings_fundefs_unique_functions. eassumption.
      + eapply IHe. eassumption. eassumption.
      + eapply IHB. eassumption. left. eassumption.
    - intros B Hin. inv Hin. inv H.
      + eapply IHe. eassumption. eassumption.
      + eapply IHB. eassumption. left. eassumption.
      + constructor. intros Hc. eapply H5. eapply name_in_fundefs_bound_var_fundefs.
        eassumption.
        eapply IHB. eassumption. eauto.
    - intros B HIn. inv HIn. inv H. constructor.
  Qed.

  Lemma exp_closure_conv_correct e c :
    unique_bindings e ->
    Disjoint _ (bound_var e) (occurs_free e) ->
    (max_var e 1%positive < next_var c)%positive ->
    exists e' c',
      closure_conversion_top clo_tag clo_itag e c = (Ret e', c') /\
      unique_bindings e' /\
      occurs_free e' \subset occurs_free e /\
      Disjoint _ (bound_var e') (occurs_free e') /\
      (max_var e' 1%positive < next_var c')%positive /\
      fun_fv_in e' (funnames_in_exp e') /\
      (forall k rho1 rho2,
          cc_approx_env_P cenv clo_tag (occurs_free e) k boundG rho1 rho2 ->
          binding_in_map (occurs_free e) rho1 ->
          cc_approx_exp cenv clo_tag k (boundL 0) boundG (e, rho1) (e', rho2)).
  Proof.
    intros Hun Hdis Hlt. unfold closure_conversion_top.
    set (fvmap := populate_map (exp_fv e) (Maps.PTree.empty VarInfo)).
    destruct (closure_conversion.get_name c) as [G c1] eqn:Hg.
    assert (Hlt' : (max_var e 1 < next_var c1)%positive).
    { unfold closure_conversion.get_name in *. destruct c. simpl in *. inv Hg. simpl. zify; lia. }

    assert (Hlt'' : (max_var e 1 < G)%positive).
    { unfold closure_conversion.get_name in *. destruct c. simpl in *. inv Hg. simpl. zify; lia. }

    assert (Hlt''' : (G < next_var c1)%positive).
    { unfold closure_conversion.get_name in *. destruct c. simpl in *. inv Hg. simpl. zify; lia. }


    set (S := (fun x : var => G < x)%positive).

    assert (Hsound := (proj1 (exp_closure_conv_Closure_conv_sound clo_tag)
                             e (occurs_free e) (Empty_set _) (Empty_set _)
                             (Maps.PTree.empty GFunInfo) 1%positive G [] fvmap S)).

    assert (Hfvmap : FVmap_inv fvmap (occurs_free e) (Empty_set positive) (Empty_set positive) []).
    { eapply populate_map_FVmap_inv_init. }

    assert (Hsub : occurs_free e \subset occurs_free e :|: Empty_set positive :|: Empty_set positive :|: FromList []).
    { sets. }

    assert (Hbnin: binding_not_in_map (S :|: [set G]) fvmap).
    { eapply populate_map_binding_in_not_in_map_init. rewrite <- exp_fv_correct.
      unfold S. eapply Union_Disjoint_r.
      - constructor. intros x Hnin. inv Hnin.
        eapply occurs_free_leq_max_var with (y := 1%positive) in H. unfold Ensembles.In in *.
        zify. lia.
      - constructor. intros x Hnin. inv Hnin. inv H0.
        eapply occurs_free_leq_max_var with (y := 1%positive) in H. unfold Ensembles.In in *.
        zify. lia. }

    assert (Hgmap: gfuns_inv (PTree.empty GFunInfo) (Empty_set positive)).
    { unfold gfuns_inv.
      split; sets.
      intros x Hin. unfold In in Hin. rewrite M.gempty in Hin. inv Hin. }

    assert (Hdis1 : Disjoint positive (Empty_set positive) (occurs_free e)).
    { sets. }

    assert (Hdis2 : Disjoint positive (Empty_set positive :|: Empty_set positive) (bound_var e)).
    { sets. }

    assert (Hdis3 : Disjoint M.elt S
                             (Empty_set positive \\ occurs_free e :|: Empty_set positive :|: used_vars e :|: [set G]
                                        :|: image (to_env fvmap) (Empty_set positive \\ occurs_free e))).
    { rewrite !Setminus_Empty_set_abs_r at 1. rewrite image_Empty_set.
      rewrite !Union_Empty_set_neut_r. rewrite Union_Empty_set_neut_l.

      unfold S. eapply Union_Disjoint_r.
      - constructor. intros x Hnin. inv Hnin. inv H0.
        + eapply bound_var_leq_max_var with (y := 1%positive) in H1. unfold Ensembles.In in *. zify. lia.
        + eapply occurs_free_leq_max_var with (y := 1%positive) in H1. unfold Ensembles.In in *. zify. lia.
      - constructor. intros x Hnin. inv Hnin. inv H0.
        unfold Ensembles.In in *. zify. lia. }

    assert (Hnin : ~ In var (used_vars e) G).
    { intros Hc. inv Hc.
      - eapply bound_var_leq_max_var with (y := 1%positive) in H. unfold Ensembles.In in *. zify. lia.
      - eapply occurs_free_leq_max_var with (y := 1%positive) in H. unfold Ensembles.In in *. zify. lia. }

    unfold triple in *.
    assert (Hf' : fresh S (next_var (fst (c1, tt)))).
    { unfold S, fresh. intros. unfold Ensembles.In in *. simpl in *. zify; lia. }

    specialize (Hsound Hfvmap Hsub Hbnin Hgmap Hun Hdis1 Hdis2 Hdis3 Hnin tt (c1, tt) Hf').

    unfold run_compM.
    destruct (runState (exp_closure_conv clo_tag e fvmap (PTree.empty GFunInfo) 1%positive G) tt (c1, tt))
      as [ p [c2 w2]] eqn:Hcc.
    destruct p as [ | [e' f]]. contradiction. simpl in *. destructAll.

    assert (Hs : occurs_free (x |[ e' ]|) \subset occurs_free e).
    { eapply Closure_conversion_occurs_free_toplevel; try eassumption.
      tci. eapply unique_bindings_fundef_names_unique_mut. eassumption. }

    do 2 eexists. split; [| split; [| split; [| split; [| split; [| split ]]]]].
    - reflexivity.
    - rewrite H0. eassumption.
    - rewrite (H0 e'). eassumption.
    - rewrite H0.
      eapply Disjoint_Included.
      + eassumption.
      + eapply Included_trans. eapply bound_var_app_ctx.
        eapply Included_Union_compat. eassumption. eassumption.
      + rewrite Union_Same_set; [| now sets ].
        eapply Union_Disjoint_l. now sets.
        constructor. intros z Hninz. inv Hninz.
        eapply occurs_free_leq_max_var with (y := 1%positive) in H7.
        unfold Ensembles.In, Range in *. simpl in *. zify; lia.
    - rewrite (H0 e').
      assert (Hin := max_var_subset (x |[ e' ]|)).
      inv Hin.
      + eapply bound_var_app_ctx in H6. inv H6.
        * eapply H2 in H7.
          destruct c2. simpl in *.
          unfold Ensembles.In, Range in *. simpl in *. zify; lia.
        * eapply H4 in H7. inv H7.
          ++ eapply bound_var_leq_max_var with (y := 1%positive) in H6.
             destruct c2. simpl in *.
             unfold Ensembles.In in *. zify. lia.
          ++ destruct c2. simpl in *.
             unfold Ensembles.In, Range in *. simpl in *. zify; lia.
      + destruct c2. simpl in *.
        eapply Hs in H6. eapply occurs_free_leq_max_var with (y := 1%positive) in H6. unfold Ensembles.In in *. zify. lia.
    - rewrite (H0 e'). intros z Hin.
      rewrite <- (Union_Empty_set_neut_l _ (funnames_in_exp (x |[ e' ]|))).
      eapply Closure_conversion_closed_fundefs. eassumption.
      eapply unique_bindings_fundef_names_unique_mut. eassumption. eassumption.
    - intros.
      rewrite (H0 e').
      eapply Closure_conversion_correct_top; try eassumption.
      intros Hn.
      eapply bound_var_leq_max_var with (y := 1%positive) in Hn. unfold Ensembles.In in *. zify. lia.
  Qed.

End Closure_conversion_correct.
