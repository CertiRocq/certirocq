(* Correctness proof for closure conversion. Part of the CertiRocq project.
 * Author: Anonymized, 2016
 *)

Require Import LambdaANF.tactics LambdaANF.closure_conversion LambdaANF.closure_conversion_util LambdaANF.algebra.
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

(** ** Environment Invariants for Closure Conversion Proof *)

(** For closure conversion, the free variables of an expression are divided in
    three categories :

    1. Variables in the current scope, i.e. arguments of the current function
    and bindings in the body of the current function definition.

    2. Names of the functions that are defined in the current block of mutually
    recursive functions.

    3. Free variables, i.e. variables that are not declared outside of the
    body of the current function but in outer definitions

    In the proof maintains different invariants for each kind of variable *)


(** * Invariants *)

(** Naming conventions in the following :

    [Scope] : The set of variables in the current scope.

    [Funs] : The set of variables in the current block of mutually recursive
    functions.

    [FVs] : The list of free variables (needs to be ordered).

    [Γ] : The formal parameter of the environment after closure conversion. *)


Section Closure_conversion_invariants.

  Variable pr : prims.
  Variable cenv : ctor_env.
  Variable clo_tag : ctor_tag.

  Context {fuel : Type} {Hfuel : @fuel_resource fuel} {trace : Type} {Htrace : @trace_resource trace}.

  (* Parameterize over the postconditions *)
  Context (boundL : nat -> @PostT fuel trace)
          (boundG : @PostGT fuel trace).

  (** ** Semantics preservation proof *)

  (** We show observational approximation of the final results as well as an
    * upper bound on the concrete execution cost of the translated program *)

  (** Invariant about the values of free variables. *)
  Definition closure_env k rho Scope Funs GFuns vs FVs : Prop :=
      Forall2 (fun x v' =>
                 forall v, ~ In _ Scope x ->
                      ~ In _ Funs x ->
                      ~ In _ GFuns x ->
                      M.get x rho = Some v ->
                      cc_approx_val cenv clo_tag k boundG v v') FVs vs.

  (** Invariant about the free variables *)
  Definition FV_inv k rho rho' Scope Funs GFuns c Γ FVs : Prop :=
    FVs <> [] ->
    exists c' (vs : list val),
      M.get Γ rho' = Some (Vconstr c' vs) /\
      c' = c /\
      Forall2 (fun x v' =>
                 forall v, ~ In _ Scope x ->
                      ~ In _ Funs x ->
                      ~ In _ GFuns x ->
                      M.get x rho = Some v ->
                      cc_approx_val cenv clo_tag k boundG v v') FVs vs.

  (** Invariant about the free variables *)
  Definition FV_inv_strong k rho rho' Scope Funs GFuns c Γ FVs : Prop :=
    exists c' (vs : list val),
      M.get Γ rho' = Some (Vconstr c' vs) /\
      (FVs <> [] -> c' = c) /\ (* Because if FVs = [] we don't care about c' *)
      Forall2 (fun x v' =>
                 forall v, ~ In _ Scope x ->
                      ~ In _ Funs x ->
                      ~ In _ GFuns x ->
                      M.get x rho = Some v ->
                      cc_approx_val cenv clo_tag k boundG v v') FVs vs.


  (** Invariant about the functions in the current function definition *)
  Definition Fun_inv k (rho rho' : env) Scope Funs genv : Prop :=
    forall f v,
      ~ In _ Scope f ->
      In var Funs f ->
      M.get f rho = Some v  ->
      exists env rho1 B1 f1 rho2 B2 f2,
        M.get (genv f) rho' = Some env /\
        v = (Vfun rho1 B1 f1) /\
        ~ In _ Scope f /\
        M.get f rho' = Some (Vfun rho2 B2 f2) /\
        cc_approx_val cenv clo_tag k boundG
                      (Vfun rho1 B1 f1)
                      (Vconstr clo_tag [(Vfun rho2 B2 f2) ; env]).

  (** Invariant about the functions in the current function definition *)
  Definition GFun_inv k (rho rho' : env) GFuns : Prop :=
    forall f v c,
      (* ~ In _ Scope f -> *)
      In var GFuns f ->
      M.get f rho = Some v  ->
      exists rho1 B1 f1 rho2 B2 f2,
        v = (Vfun rho1 B1 f1) /\
        M.get f rho' = Some (Vfun rho2 B2 f2) /\
        cc_approx_val cenv clo_tag k boundG
                      (Vfun rho1 B1 f1)
                      (Vconstr clo_tag [(Vfun rho2 B2 f2) ; (Vconstr c [])]).


  (** * Lemmas about Fun_inv *)

  (** Extend the first environment with a variable in not in [Funs] *)
  Lemma Fun_inv_monotonic k m rho1 rho2 Scope Funs Γ :
    Fun_inv k rho1 rho2 Scope Funs Γ ->
    m <= k ->
    Fun_inv m rho1 rho2 Scope Funs Γ.
  Proof.
    intros Hinv Hin f v' Hninf Hinf Hget.
    edestruct Hinv with (f := f) as
        [vs' [rho3 [B3 [f3 [rho4 [B4 [f4 [Hget1 [Heq2 [Ηnin2 [Hget2 Happrox]]]]]]]]]]]; eauto.
    repeat eexists; eauto.
    eapply cc_approx_val_monotonic. eassumption. lia.
  Qed.

  (** Extend the two environments with a variable that is not the current environment
    argument (i.e. [Γ]) *)
  Lemma Fun_inv_set k rho rho' Scope Funs genv f rho1 B1 f1 rho2 B2 f2 env:
    Fun_inv k rho rho' Scope Funs genv ->

    ~ In _ (image genv (Funs \\ Scope)) f ->
    f <> genv f ->


    M.get (genv f) rho' = Some env ->
    (cc_approx_val cenv clo_tag k boundG (Vfun rho1 B1 f1)
                   (Vconstr clo_tag [(Vfun rho2 B2 f2) ; env])) ->
    Fun_inv k (M.set f (Vfun rho1 B1 f1) rho)
            (M.set f (Vfun rho2 B2 f2) rho')
            Scope (Union _ (Singleton _ f) Funs) genv.
  Proof.
    intros Hinv Hneq Hnin Hget Hv f'' v Hnin''' Hin Hget'.
    destruct (peq f'' f); subst.
    - repeat eexists; eauto. rewrite M.gso; eauto.
      now rewrite M.gss in Hget'; inv Hget'; eauto.
      now rewrite M.gss.
    - inv Hin. inv H; congruence. rewrite M.gso in Hget'; eauto.
      edestruct Hinv with (f := f'') as
          [vs' [rho3 [B3 [f3 [rho4 [B4 [f4 [Hget1 [Heq2 [Ηnin2 [Hget2 Happrox]]]]]]]]]]];
        subst; eauto.
      repeat eexists; eauto. rewrite M.gso. eassumption.
      intros Hc. eapply Hneq. rewrite <- Hc. eapply In_image. constructor; eauto.
      rewrite M.gso. now eauto.
      intros Hc. subst. contradiction.
  Qed.

  (** Rename the environment parameter *)
  Lemma Fun_inv_rename k rho1 rho2 Scope Funs Γ Γ' v genv B1 :
    ~ In _ (Funs \\ Scope) Γ ->
    ~ In _ (Funs \\ Scope) Γ' ->
    Funs \subset name_in_fundefs B1 ->
    Fun_inv k rho1 (M.set Γ v rho2) Scope Funs (extend_fundefs' genv B1 Γ) ->
    Fun_inv k rho1 (M.set Γ' v rho2) Scope Funs (extend_fundefs' genv B1 Γ').
  Proof.
    intros Hnin Hnin' Hsub Hinv f v1 Hninf Hinf Hget.
    edestruct Hinv with (f := f) as
        [vs' [rho3 [B3 [f3 [rho4 [B4 [f4 [Hget1 [Heq2 [Ηnin2 [Hget2 Happrox]]]]]]]]]]]; eauto.
    rewrite extend_fundefs'_get_s in *.
    rewrite M.gss in Hget1. inv Hget1.
    repeat eexists; eauto. now rewrite M.gss; eauto.
    rewrite M.gso in Hget2. rewrite M.gso; eauto.
    intros Hc. eapply Hnin'. subst. econstructor; eauto.
    intros Hc. eapply Hnin. subst. econstructor; eauto.
    eauto. eauto.
  Qed.



  (** Extend [Scope] with a set that does not shadow the new function names *)
  Lemma Fun_inv_mon k rho1 rho2 Scope Scope' Funs genv :
    Fun_inv k rho1 rho2 Scope Funs genv ->
    Fun_inv k rho1 rho2 (Union _ Scope' Scope) Funs genv.
  Proof.
    intros (* Hd *) Hinv f v Hninf Hinf Hget.
    edestruct Hinv with (f := f) as
        [vs' [rho3 [B3 [f3 [rho4 [B4 [f4 [Hget1 [Heq2 [Ηnin2 [Hget2 Happrox]]]]]]]]]]]; eauto.
    repeat eexists; eauto.
  Qed.

  (** Extend the first environment with a variable in [Scope] *)
  Lemma Fun_inv_set_In_Scope_l k rho1 rho2 Scope Funs Γ x v :
    In _ Scope x ->
    Fun_inv k rho1 rho2 Scope Funs Γ ->
    Fun_inv k (M.set x v rho1) rho2 Scope Funs Γ.
  Proof.
    intros Hin Hinv f v' Hninf Hinf Hget.
    eapply Hinv; eauto. rewrite M.gso in Hget.
    now eauto. intros Hc; subst. now eauto.
  Qed.

    (** Extend the first environment with a variable in not in [Funs] *)
  Lemma Fun_inv_set_not_In_Funs_l k rho1 rho2 Scope Funs Γ x v :
    ~ In _ Funs x  ->
    Fun_inv k rho1 rho2 Scope Funs Γ ->
    Fun_inv k (M.set x v rho1) rho2 Scope Funs Γ.
  Proof.
    intros Hin Hinv f v' Hninf Hinf Hget.
    eapply Hinv; eauto. rewrite M.gso in Hget.
    now eauto. intros Hc; subst. now eauto.
  Qed.

  (** Extend the first environment with a variable in not in [Funs] *)
  Lemma Fun_inv_funs_monotonic k rho1 rho2 Scope Funs Funs' Γ :
    Fun_inv k rho1 rho2 Scope Funs Γ ->
    Funs' \subset Funs ->
    Fun_inv k rho1 rho2 Scope Funs' Γ.
  Proof.
    intros Hin Hinv f v' Hninf Hinf Hget.
    eapply Hin; eauto.
  Qed.

  (** Extend the second environment with a variable in [Scope] that is different
    from [Γ] *)
  Lemma Fun_inv_set_In_Scope_r_not_Γ k rho1 rho2 Scope Funs Γ x v :
    In _ Scope x ->
    ~ In _ (image Γ (Funs \\ Scope)) x ->
    Fun_inv k rho1 rho2 Scope Funs Γ ->
    Fun_inv k rho1 (M.set x v rho2) Scope Funs Γ.
  Proof.
    intros Hin Hnin Hinv f v1 Hninf Hinf Hget.
    edestruct Hinv with (f := f) as
        [vs' [rho3 [B3 [f3 [rho4 [B4 [f4 [Hget1 [Heq2 [Ηnin2 [Hget2 Happrox]]]]]]]]]]]; eauto.
    repeat eexists; eauto.
    rewrite M.gso. eassumption. intros Hc. eapply Hnin. subst. eapply In_image.
    constructor; eauto.
    rewrite M.gso. now eauto.
    intros Hc. subst. contradiction.
  Qed.

  (** Extend the second environment with a variable not in [Funs] that is different
    from Γ *)
  Lemma Fun_inv_set_not_In_Funs_r_not_Γ k rho1 rho2 Scope Funs Γ x v :
    ~ In _ (Funs \\ Scope) x ->
    ~ In _ (image Γ (Funs \\ Scope)) x ->
    Fun_inv k rho1 rho2 Scope Funs Γ ->
    Fun_inv k rho1 (M.set x v rho2) Scope Funs Γ.
  Proof.
    intros Hnin Hneq Hinv f v1 Hninf Hinf Hget.
    edestruct Hinv with (f := f) as
        [vs' [rho3 [B3 [f3 [rho4 [B4 [f4 [Hget1 [Heq2 [Ηnin2 [Hget2 Happrox]]]]]]]]]]]; eauto.
    repeat eexists; eauto.
    rewrite M.gso. now eauto.
    intros Hc. subst. eapply Hneq. eapply In_image. constructor; eauto.

    rewrite M.gso. now eauto.
    intros Hc. subst. eapply Hnin. constructor; eauto.
  Qed.

  (** Extend the first environment with a list of variables in [Scope] *)
  Lemma Fun_inv_set_lists_In_Scope_l k rho1 rho1' rho2 Scope Funs Γ xs vs :
    Included _ (FromList xs) Scope ->
    Fun_inv k rho1 rho2 Scope Funs Γ ->
    set_lists xs vs rho1 = Some rho1' ->
    Fun_inv k rho1' rho2 Scope Funs Γ.
  Proof.
    revert rho1 rho1' vs. induction xs; intros rho1 rho1' vs.
    - intros Hinc Hfun Hset. inv Hset.
      destruct vs; [ | discriminate ]. now inv H0.
    - intros Hinc Hfun Hset.
      simpl in Hset.
      destruct vs; [ discriminate | ].
      destruct (set_lists xs vs rho1) eqn:Heq; [ | discriminate ]. inv Hset.
      eapply Fun_inv_set_In_Scope_l.
      + rewrite FromList_cons in Hinc.
        eapply Hinc. eauto.
      + eapply IHxs; eauto.
        rewrite FromList_cons in Hinc.
        eapply Included_trans; [| eassumption ].
        eapply Included_Union_r.
  Qed.


  (** Extend the second environment with a variable in [Scope] *)
  Lemma Fun_inv_set_In_Scope_r k rho1 rho2 Scope Funs Γ x v v' B :
    In _ Scope x ->
    ~ In _ (Funs \\ Scope) x ->
    Funs \subset name_in_fundefs B ->
    Fun_inv k rho1 (M.set Γ v rho2) Scope Funs (extend_fundefs' id B Γ) ->
    Fun_inv k rho1 (M.set Γ v (M.set x v' rho2)) Scope Funs (extend_fundefs' id B Γ).
  Proof.
    intros Hin Hnin Hsub Hinv f v1 Hninf Hinf Hget.
    edestruct Hinv with (f := f) as
        [vs' [rho3 [B3 [f3 [rho4 [B4 [f4 [Hget1 [Heq2 [Ηnin2 [Hget2 Happrox]]]]]]]]]]]; eauto.
    subst. rewrite extend_fundefs'_get_s in Hget1.
    rewrite M.gss in Hget1; inv Hget1.
    repeat eexists; eauto.
    rewrite extend_fundefs'_get_s, M.gss. reflexivity. now eauto.
    destruct_with_eqn (peq f Γ).
    - subst. now rewrite M.gss in *.
    - rewrite M.gso; eauto. rewrite M.gso in Hget2; eauto.
      rewrite M.gso; eauto.
      intros Hc; subst. eapply Hnin. eexists; eauto.
    - eauto.
  Qed.


  (** Extend the second environment with a list of variables in [Scope] *)
  Lemma Fun_inv_set_lists_In_Scope_r k rho1 rho2 rho2' Scope Funs Γ xs vs v B :
    Included _ (FromList xs) Scope ->
    Disjoint _ (Funs \\ Scope) (FromList xs) ->
    Funs \subset name_in_fundefs B ->
    Fun_inv k rho1 (M.set Γ v rho2) Scope Funs (extend_fundefs' id B Γ) ->
    set_lists xs vs rho2 = Some rho2' ->
    Fun_inv k rho1 (M.set Γ v rho2') Scope Funs (extend_fundefs' id B Γ).
  Proof.
    revert rho2 rho2' vs. induction xs; intros rho2 rho2' vs.
    - intros Hinc Hd Hsub Hfun Hset. inv Hset.
      destruct vs; [ | discriminate ]. now inv H0.
    - intros Hinc Hd Hsub Hfun Hset.
      simpl in Hset.
      destruct vs; [ discriminate | ].
      destruct (set_lists xs vs rho2) eqn:Heq; [| now eauto ]. inv Hset.
      eapply Fun_inv_set_In_Scope_r.
      + rewrite FromList_cons in Hinc.
        eapply Hinc. eauto.
      + intros Hin. eapply Hd. constructor; eauto.
        rewrite FromList_cons. eauto.
      + eauto.
      + rewrite FromList_cons in Hinc, Hd. eapply IHxs; eauto.
        eapply Included_trans; [| eassumption ].
        eapply Included_Union_r.
        eapply Disjoint_Included_r; [| eassumption ].
        eapply Included_Union_r.
  Qed.

  (** Redefine the environment argument in the second environment *)
  Lemma Fun_inv_reset k rho rho' B B' v Scope Funs Γ :
    ~ In _ (name_in_fundefs B) Γ ->
    Funs \subset name_in_fundefs B' ->
    M.get Γ rho' = Some v ->
    Fun_inv k rho (def_funs B B rho' rho') Scope Funs (extend_fundefs' id B' Γ) ->
    Fun_inv k rho (M.set Γ v (def_funs B B rho' rho')) Scope Funs (extend_fundefs' id B' Γ).
  Proof.
    intros Hnin Hsub Hget Hinv f v1 Hninf Hinf Hget'.
    edestruct Hinv with (f := f) as
        [vs' [rho3 [B3 [f3 [rho4 [B4 [f4 [Hget1 [Heq2 [Ηnin2 [Hget2 Happrox]]]]]]]]]]]; eauto.
    rewrite extend_fundefs'_get_s in *.
    rewrite def_funs_neq in Hget1; eauto. subst.
    repeat subst_exp.
    repeat eexists.
    - now rewrite M.gss.
    - eauto.
    - destruct (peq f Γ); subst.
      rewrite def_funs_neq in Hget2; eauto.  subst_exp.
      rewrite M.gss. reflexivity.

      rewrite M.gso. eassumption.
      now intros Hc; subst; eauto.
    - eassumption.
    - eauto.
    - eauto.
  Qed.

  Global Instance Fun_inv_proper :
    Proper (Logic.eq ==> Logic.eq ==> Logic.eq ==> Same_set var ==>
                     Logic.eq ==> Logic.eq ==> iff)
           (Fun_inv).
  Proof.
    constructor; intros Hinv; subst;
    intros f v1 Hninf Hinf Hget;
    edestruct Hinv with (f := f) as
        [vs' [rho3 [B3 [f3 [rho4 [B4 [f4 [Hget1 [Heq2 [Ηnin2 [Hget2 Happrox]]]]]]]]]]]; eauto;
    repeat eexists; try (now rewrite <- H2; eauto); try rewrite H2; eauto.
  Qed.

  (** Define a block of functions in the first environment and put them in the
    current scope *)
  Lemma Fun_inv_def_funs_l k rho rho' B1 B1' Scope Funs Γ:
    Fun_inv k rho rho' Scope Funs Γ ->
    Fun_inv k (def_funs B1 B1' rho rho) rho' (Union _ (name_in_fundefs B1')  Scope) Funs Γ.
  Proof.
    intros Hinv f v1 Hninf Hinf Hget. rewrite def_funs_neq in Hget; eauto.
    edestruct Hinv with (f := f) as
        [vs' [rho3 [B3 [f3 [rho4 [B4 [f4 [Hget1 [Heq2 [Ηnin2 [Hget2 Happrox]]]]]]]]]]]; eauto.
    subst. repeat eexists; eauto.
  Qed.


  (* TODO move *)
  Lemma Disjoint_In_l {A} (s1 s2 : Ensemble A) x :
    Disjoint _ s1 s2 ->
    x \in s1 ->
   ~ x \in s2.
  Proof.
    intros Hd Hin Hc. eapply Hd. constructor; eauto.
  Qed.

  (** Define a block of functions in the second environment and put the in the
    current scope *)
  Lemma Fun_inv_def_funs_r k rho rho' B1 B1' Scope Funs genv :
    Disjoint _ (name_in_fundefs B1') (image genv (Funs \\ Scope)) ->
    Fun_inv k rho rho' Scope Funs genv ->
    Fun_inv k rho (def_funs B1 B1' rho' rho') ((name_in_fundefs B1') :|: Scope) Funs genv.
  Proof.
    intros Hnin Hinv f v1 Hninf Hinf Hget.
    edestruct Hinv with (f := f) as
        [vs' [rho3 [B3 [f3 [rho4 [B4 [f4 [Hget1 [Heq2 [Ηnin2 [Hget2 Happrox]]]]]]]]]]]; eauto.
    subst. repeat eexists; eauto.
    rewrite def_funs_neq; eauto. simpl. eapply Disjoint_In_l. eapply Disjoint_sym. eassumption.
    eapply In_image. constructor; eauto.
    rewrite def_funs_neq; eauto.
  Qed.

  (** Define a block of functions in both environments and put the in the
    current scope *)
  Lemma Fun_inv_def_funs k rho rho' B1 B1' B2 B2' Scope Funs genv:
    Disjoint _ (name_in_fundefs B2') (image genv (Funs \\ Scope)) ->
    Disjoint _ (Funs \\ Scope) (name_in_fundefs B2') ->
    Fun_inv k rho rho' Scope Funs genv ->
    Fun_inv k  (def_funs B1 B1' rho rho) (def_funs B2 B2' rho' rho')
            Scope (Funs \\ (name_in_fundefs B1')) genv.
  Proof.
    intros Hnin2 HD1 (*  HD2 *) Hinv f v1 Hninf Hinf Hget. inv Hinf.
    rewrite def_funs_neq in Hget; eauto.
    edestruct Hinv with (f := f) as
        [vs' [rho3 [B3 [f3 [rho4 [B4 [f4 [Hget1 [Heq2 [Ηnin2 [Hget2 Happrox]]]]]]]]]]]; eauto.
    subst.
    repeat eexists; eauto.
    rewrite def_funs_neq; eauto. eapply Disjoint_In_l. eapply Disjoint_sym. eassumption.
    eapply In_image. constructor; eauto.
    rewrite def_funs_neq; eauto.
    intros Hc. eapply HD1. econstructor; eauto. econstructor; eauto.
  Qed.

  (** * Lemmas about FV_inv *)

  (** Extend the first environment with a variable in [Scope] *)
  Lemma FV_inv_set_In_Scope_l k rho rho' x v Scope Funs GFuns FVs c Γ :
    In var Scope x ->
    FV_inv k rho rho' Scope Funs GFuns c Γ FVs ->
    FV_inv k (M.set x v rho) rho' Scope Funs GFuns c Γ FVs.
  Proof.
    intros Hin Hfv Hneq. edestruct Hfv as [g [c' [Hget [Hleq HInv]]]].
    eassumption.
    destruct FVs.
    - congruence.
    - do 2 eexists; repeat split; eauto.
      rewrite <- Hleq; eauto.
      eapply Forall2_monotonic_strong; [| eassumption ].
      intros z w Hin1 Hin2 He v1 Hnin1 Hnin2 Hnin3 Hget'.
      eapply He; eauto. rewrite M.gso in Hget'; eauto.
      intros Hc; subst; contradiction.
  Qed.

  (** Extend the first environment with a variable not in [FVs] *)
  Lemma FV_inv_set_not_In_FVs_l k rho rho' x v Scope Funs GFuns c Γ FVs :
    ~ List.In x FVs ->
    FV_inv k rho rho' Scope Funs GFuns c Γ FVs ->
    FV_inv k (M.set x v rho) rho' Scope Funs GFuns c Γ FVs.
  Proof.
    intros Hnin Hfv Hne1. edestruct Hfv as [g [c' [Hget [Hleq HInv]]]].
    eassumption.
    destruct FVs.
    - congruence.
    - do 2 eexists; repeat split; eauto.
      rewrite <- Hleq; eauto.
      eapply Forall2_monotonic_strong; [| eassumption ].
      intros z w Hin1 Hin2 He v1 Hnin1 Hnin2 Hnin3 Hget'.
      eapply He; eauto. rewrite M.gso in Hget'; eauto.
      intros Hc; subst; contradiction.
  Qed.

  (** Extend the second environment with a variable that is not [Γ] *)
  Lemma FV_inv_set_r k rho rho' x v Scope Funs GFuns c Γ FVs :
    x <> Γ ->
    FV_inv k rho rho' Scope Funs GFuns c Γ FVs ->
    FV_inv k rho (M.set x v rho') Scope Funs GFuns c Γ FVs.
  Proof.
    intros Hnin Hfv Hneq. edestruct Hfv as [c' [g [Hget HInv]]].
    eassumption.
    do 2 eexists; split; eauto.
    rewrite M.gso; eauto.
  Qed.


  (** Extend the [Scope] and remove from [GFuns] **)
  Lemma FV_inv_extend_Scope_GFuns k rho rho' Scope GFuns Funs c Γ FVs x :
    FV_inv k rho rho' Scope Funs GFuns c Γ FVs ->
    FV_inv k rho rho' (x |: Scope) Funs GFuns c Γ FVs.
  Proof.
    intros Hfv Hneq. edestruct Hfv as [c' [g [Hget [Hc HInv]]]]. eassumption.
    do 2 eexists; split; eauto.
    split; eauto.
    eapply Forall2_monotonic_strong; [| eassumption ]; eauto.
  Qed.

  Lemma FV_inv_monotonic k j rho rho' Scope GFuns Funs c Γ FVs :
    FV_inv j rho rho' Scope Funs GFuns c Γ FVs ->
    j >= k ->
    FV_inv k rho rho' Scope Funs GFuns c Γ FVs.
  Proof.
    intros Hfvs Hleq Hneq. edestruct Hfvs as [c' [g [Hget [Hc HInv]]]].
    eassumption. do 2 eexists; split; eauto.
    split; eauto.
    eapply Forall2_monotonic_strong; [| eassumption ]; eauto.
    intros; eauto. eapply cc_approx_val_monotonic. eauto. eassumption.
  Qed.

  Lemma FV_inv_strong_monotonic k j rho rho' Scope GFuns Funs c Γ FVs :
    FV_inv_strong j rho rho' Scope Funs GFuns c Γ FVs ->
    j >= k ->
    FV_inv_strong k rho rho' Scope Funs GFuns c Γ FVs.
  Proof.
    intros [c' [g [Hget [Hc HInv]]]]. do 2 eexists; split; eauto.
    split; eauto.
    eapply Forall2_monotonic_strong; [| eassumption ]; eauto.
    intros; eauto. eapply cc_approx_val_monotonic. eauto. eassumption.
  Qed.


  Lemma FV_inv_antimonotonic_GFuns k rho rho' Scope GFuns1 GFuns2 Funs c Γ FVs :
    FV_inv k rho rho' Scope Funs GFuns1 c Γ FVs ->
    GFuns1 \subset GFuns2 ->
    FV_inv k rho rho' Scope Funs GFuns2 c Γ FVs.
  Proof.
    intros Hfv Hsub Hneq. edestruct Hfv as [c' [g [Hget [Hc HInv]]]].
    eassumption. do 2 eexists; split; eauto.
    split; eauto.
    eapply Forall2_monotonic_strong; [| eassumption ]; eauto.
  Qed.

  Lemma FV_inv_antimonotonic_add_global_funs k rho rho' Scope GFuns GFuns' names {Hd : Decidable names} Funs c Γ FVs FVs' :
    FV_inv k rho rho' Scope Funs GFuns c Γ FVs ->
    add_global_funs GFuns names (FromList FVs') GFuns' ->
    names \subset Funs ->
    FV_inv k rho rho' Scope Funs GFuns' c Γ FVs.
  Proof.
    intros Hfv Hadd Hsub Hneq. edestruct Hfv as [c' [g [Hget [Hc HInv]]]].
    eassumption. inv Hadd; eauto.
    - do 2 eexists; split; eauto.
      split; eauto.
      eapply Forall2_monotonic_strong; [| eassumption ]; eauto.
    - do 2 eexists; split; eauto.
      split; eauto.
      eapply Forall2_monotonic_strong; [| eassumption ]; eauto.
      intros. eapply H2; eauto.
      destruct Hd. destruct (Dec x1); eauto. intros Hc1.
      eapply H5. constructor; eauto.
  Qed.

  Lemma FV_inv_strong_Forall2 k rho rho' Scope GFuns Funs c Γ FVs vs1 vs2 :
    get_list FVs rho = Some vs1 ->
    M.get Γ rho' = Some (Vconstr c vs2) ->
    Forall2 (cc_approx_val cenv clo_tag k boundG) vs1 vs2 ->
    FV_inv_strong k rho rho' Scope Funs GFuns c Γ FVs.
  Proof.
    intros Hget1 Hget2 Hall. do 2 eexists; split; eauto.
    split; eauto. clear Hget2.
    revert vs1 vs2 Hget1 Hall; induction FVs; intros vs1 vs2 Hget1 Hall;
      destruct vs2; try (now inv Hget1).
    + inv Hall; eauto.
      eapply get_list_length_eq in Hget1. simpl in Hget1. congruence.
    + inv Hall.
      constructor; eauto.
      * intros. simpl in Hget1.
        rewrite H4 in Hget1.
        destruct (get_list FVs rho) eqn:Hfv; try congruence.
      * simpl in Hget1.
        destruct (get_list FVs rho) eqn:Hfv; try congruence; destruct (M.get a rho); try congruence.
        inv Hget1. eapply IHFVs; eauto.
  Qed.

  (** Extend the [Scope]. TODO : replace with monotonicity property? *)
  Lemma FV_inv_extend_Scope k rho rho' Scope GFuns Funs c Γ FVs x :
    FV_inv k rho rho' Scope Funs GFuns c Γ FVs ->
    FV_inv k rho rho' (Union _ (Singleton _ x) Scope) Funs GFuns c Γ FVs.
  Proof.
    intros Hfvs Hneq.
    edestruct Hfvs as [c' [g [Hget [Hc HInv]]]]. eassumption.
    do 2 eexists; split; eauto.
    split; eauto.
    eapply Forall2_monotonic_strong; [| eassumption ]; eauto.
  Qed.

  (** Define a block of functions in both environments and put the in the
    current scope *)
  Lemma FV_inv_def_funs k rho rho' B1 B1' B2 B2' Scope Funs GFuns c Γ FVs:
    ~ In _ (name_in_fundefs B1') Γ ->
    ~ In _ (name_in_fundefs B2') Γ ->
    FV_inv k rho rho' Scope Funs GFuns c Γ FVs ->
    FV_inv k  (def_funs B1 B1' rho rho) (def_funs B2 B2' rho' rho')
           (Scope \\ (name_in_fundefs B1')) (name_in_fundefs B1' :|: Funs) GFuns c Γ FVs.
  Proof.
    intros Hnin1 Hnin2 Hfvs Hneq.
    edestruct Hfvs as [c' [g [Hget [Hc HInv]]]]. eassumption.
    do 2 eexists; split; eauto.
    now rewrite def_funs_neq; eauto.
    split; eauto.
    eapply Forall2_monotonic_strong; [| eassumption ]; eauto.
    intros z w Hin1 Hin2 He v1 Hnin3 Hnin4 Hnin5 Hget'.
    eapply He; eauto.
    intros Hc1. eapply Hnin3; constructor; eauto.
    now rewrite def_funs_neq in Hget'; eauto.
  Qed.

  (** * Lemmas about [GFun_inv]  *)

  (** Extend the two environments with a variable that is not the current environment
    argument (i.e. [Γ]) *)
  Lemma GFun_inv_set k rho rho' GFuns f rho1 B1 f1 rho2 B2 f2:
    GFun_inv k rho rho' GFuns ->
    (forall c, f \in GFuns ->
          cc_approx_val cenv clo_tag k boundG (Vfun rho1 B1 f1) (Vconstr clo_tag [(Vfun rho2 B2 f2) ; Vconstr c []])) ->
    GFun_inv k (M.set f (Vfun rho1 B1 f1) rho) (M.set f (Vfun rho2 B2 f2) rho') GFuns.
  Proof.
    intros Hinv Hv f'' v Hnin'' Hin Hget'.
    destruct (peq f'' f); subst; eauto.
    - rewrite M.gss in Hget'. inv Hget'. repeat eexists; eauto.
      now rewrite M.gss.
    - rewrite M.gso in Hget'; eauto.
      edestruct Hinv with (f := f'') as
          [rho3 [B3 [f3 [rho4 [B4 [f4 [Heq [Hget2 Happrox]]]]]]]]; subst; eauto.
      repeat eexists; eauto.
      rewrite M.gso. now eauto. eassumption.
  Qed.

  (** Extend the first environment with a variable not in [GFuns] *)
  Lemma GFun_inv_set_not_In_GFuns_l k rho1 rho2 GFuns x v :
    ~ x \in GFuns ->
    GFun_inv k rho1 rho2 GFuns ->
    GFun_inv k (M.set x v rho1) rho2 GFuns.
  Proof.
    intros Hnin Hinv f v' c Hin Hget.
    eapply Hinv; eauto. rewrite M.gso in Hget.
    now eauto. intros Hc; subst. now eauto.
  Qed.

  (** Extend the second environment with a variable in [GFuns] *)
  Lemma GFun_inv_set_not_In_GFuns_r k rho1 rho2 GFuns x v :
    ~ x \in GFuns ->
    GFun_inv k rho1 rho2 GFuns ->
    GFun_inv k rho1 (M.set x v rho2) GFuns.
  Proof.
    intros Hnin Hinv f v' c Hin Hget.
    edestruct Hinv as
        [rho3 [B3 [f3 [rho4 [B4 [f4 [Heq2 [Hget2 Happrox]]]]]]]]; eauto.
    repeat eexists; eauto.
    rewrite M.gso. eassumption.
    intros Hc. eapply Hnin. subst. eassumption.
  Qed.

(** Extend the first environment with a variable not in [GFuns] *)
  Lemma GFun_inv_setlist_not_In_GFuns_l k rho1 rho1' rho2 GFuns xs vs :
    Disjoint _ GFuns (FromList xs) ->
    set_lists xs vs rho1 = Some rho1' ->
    GFun_inv k rho1 rho2 GFuns ->
    GFun_inv k rho1' rho2 GFuns.
  Proof.
    revert rho1 rho1' vs. induction xs; intros rho1 rho1' vs.
    - intros Hinc Hset Hfun. inv Hset.
      destruct vs; [ | discriminate ]. now inv H0.
    - intros Hinc Hset Hfun.
      simpl in Hset.
      destruct vs; [ discriminate | ].
      destruct (set_lists xs vs rho1) eqn:Heq; [ | discriminate ]. inv Hset.
      eapply GFun_inv_set_not_In_GFuns_l.
      + intros Hc. eapply Hinc. constructor; eauto. now left.
      + eapply IHxs; eauto. normalize_sets.
        repeat normalize_sets. sets.
  Qed.

  (** Extend the second environment with a list not in [GFuns] *)
  Lemma GFun_inv_setlist_not_In_GFuns_r k rho1 rho2' rho2 GFuns xs vs :
    Disjoint _ GFuns (FromList xs) ->
    set_lists xs vs rho2 = Some rho2' ->
    GFun_inv k rho1 rho2 GFuns ->
    GFun_inv k rho1 rho2' GFuns.
  Proof.
    revert rho2 rho2' vs. induction xs; intros rho2 rho2' vs.
    - intros Hinc Hset Hfun. inv Hset.
      destruct vs; [ | discriminate ]. now inv H0.
    - intros Hinc Hset Hfun.
      simpl in Hset.
      destruct vs; [ discriminate | ].
      destruct (set_lists xs vs rho2) eqn:Heq; [ | discriminate ]. inv Hset.
      eapply GFun_inv_set_not_In_GFuns_r.
      + intros Hc. eapply Hinc. constructor; eauto. now left.
      + eapply IHxs; eauto. normalize_sets.
        repeat normalize_sets. sets.
  Qed.

  (** Extend the first environment with funs not in [GFuns] *)
  Lemma GFun_inv_def_funs_not_In_GFuns_l k rho1 rho2 GFuns B1 B1' :
    Disjoint _ (name_in_fundefs B1') GFuns ->
    GFun_inv k rho1 rho2 GFuns ->
    GFun_inv k (def_funs B1 B1' rho1 rho1) rho2 GFuns.
  Proof.
    intros HD Hinv f v1 c Hinf Hget. rewrite def_funs_neq in Hget; eauto.
    intros Hc. eapply HD. constructor; eauto.
  Qed.

  Lemma GFun_inv_def_funs_not_In_GFuns_r k rho rho' B1 B1' GFuns :
    Disjoint _ GFuns (name_in_fundefs B1') ->
    GFun_inv k rho rho' GFuns ->
    GFun_inv k rho (def_funs B1 B1' rho' rho') GFuns.
  Proof.
    intros HD Hinv f v1 c Hinf Hget. setoid_rewrite def_funs_neq; eauto.
    intros Hc. eapply HD. constructor; sets.
  Qed.

  Lemma GFun_inv_antimon k rho rho' GFuns GFuns' :
     GFun_inv k rho rho' GFuns ->
     GFuns' \subset GFuns ->
     GFun_inv k rho rho' GFuns'.
  Proof.
    intros Hg Hsub f v1 Hinf Hget; eauto.
  Qed.

  Lemma GFun_inv_monotonic k j rho rho' GFuns :
    GFun_inv k rho rho' GFuns ->
    j <= k ->
    GFun_inv j rho rho' GFuns.
  Proof.
    intros Hg Hleq c f v1 Hinf Hget; eauto.
    edestruct Hg as (rho1 & B1 & f1 & rho2 & B2 & f2 & Heq1 & Hget1 & Hcc); eauto.
    repeat eexists; eauto.
    eapply cc_approx_val_monotonic; eauto.
  Qed.

  (* Lemma GFun_inv_Scope_extend k rho rho' Scope Scope' GFuns : *)
  (*   GFun_inv k rho rho' Scope GFuns -> *)
  (*   GFun_inv k rho rho' (Scope' :|: Scope) GFuns. *)
  (* Proof. *)
  (*   intros Hdis Hg f v1 c1 Hinf Hget; eauto. *)
  (* Qed. *)

  Lemma GFun_inv_fuse k rho rho' GFuns1 GFuns2 names FVs { Hd : Decidable names} :
    add_global_funs GFuns1 names FVs GFuns2 ->
    GFun_inv k rho rho' (GFuns1 \\ names) ->
    GFun_inv k rho rho' GFuns2 ->
    (* Disjoint _ Scope1 names -> *)
    GFun_inv k rho rho' GFuns2.
  Proof.
    intros Ha Hg1 Hg2 x v c Hin1 Hget. inv Ha.
    - eapply Hg2. now eauto. eassumption.
    - eapply Hg1. now eauto. eassumption.
  Qed.


  Lemma Fun_inv_from_GFun_inv k rho1 rho2 Scope GFuns Funs Γ c B :
    Funs \subset GFuns ->
    Funs \subset name_in_fundefs B ->
    GFun_inv k rho1 rho2 GFuns ->
    M.get Γ rho2 = Some (Vconstr c []) ->
    Fun_inv k rho1 rho2 Scope Funs (extend_fundefs' id B Γ).
  Proof.
    intros Hsub Hsub' Hinv Hget f v' Hnin Hin Hget'.
    edestruct Hinv as
        [rho3 [B3 [f3 [rho4 [B4 [f4 [Heq2 [Hget2 Happrox]]]]]]]]; eauto.
    repeat eexists; eauto.
    rewrite extend_fundefs'_get_s. eassumption. eauto.
  Qed.


End Closure_conversion_invariants.
