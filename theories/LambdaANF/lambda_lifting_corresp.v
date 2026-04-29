(* Correspondence of the computational definition and the declarative
  spec for lambda lifting. Part of the CertiRocq project.
 * Author: Anonymized, 2016 *)

Require Import LambdaANF.term LambdaANF.term_util LambdaANF.set_util LambdaANF.identifiers LambdaANF.ctx LambdaANF.Ensembles_util
        LambdaANF.List_util LambdaANF.lambda_lifting LambdaANF.functions LambdaANF.state LambdaANF.tactics
        LambdaANF.logical_relations LambdaANF.eval LambdaANF.lambda_lifting_util LambdaANF.uncurry_correct.
From CertiRocq.Common Require Import compM.
Require Import ExtLib.Structures.Monads ExtLib.Data.Monads.StateMonad ExtLib.Data.Monads.OptionMonad.
Require Import compcert.lib.Coqlib.
From Stdlib Require Import ZArith.Znumtheory Relations.Relations Arith.Wf_nat.
From Stdlib Require Import Lists.List MSets.MSets MSets.MSetRBT Numbers.BinNums
     NArith.BinNat PArith.BinPos Sets.Ensembles micromega.Lia.
Require Import ExtLib.Structures.Monads ExtLib.Data.Monads.StateMonad.

Import ListNotations MonadNotation.

Open Scope ctx_scope.
Open Scope fun_scope.
Open Scope monad_scope.

(** * Correspondence of the relational and the computational definitions of  lambda lifting *)

Section Lambda_lifting_corresp.

  (** Construct a function map from [FunInfoMap] similar to the one that is used in the relational spec   *)
  Definition fun_map (m : FunInfoMap) : var -> option (var * fun_tag * list var) :=
    fun f =>
      match M.get f m with
        | Some inf =>
          match inf with
          | Fun f' ft _ _ fvs => Some (f', ft, fvs)
          | NoLiftFun _ _ => None
          end
        | None => None
      end.

  (** Useful equality to use the IH for [Ecase]  *)
  Lemma st_eq_Ecase (m1 :  lambdaM (list (ctor_tag * exp))) (x : var) y :
    st_eq
      (bind (bind m1 (fun ys => ret (y :: ys))) (fun ys' => ret (Ecase x ys')))
      (e <- (ys <- m1 ;;
             ret (Ecase x ys)) ;;
       match e with
         | Ecase x ys =>
           ret (Ecase x (y :: ys))
         | _ => ret e
       end).
  Proof.
    unfold bind, ret. simpl.
    intros s [w u]. simpl. destruct (compM.runState m1 s (w, u)).
    simpl. destruct e; reflexivity.
  Qed.

  Global Opaque bind ret.

  (** * Lemmas about [rename] *)

  Lemma rename_set_FreeVar_f_eq m x y :
    f_eq (rename (M.set x (FreeVar y) m))
         ((rename m) {x ~> y}).
  Proof.
    intros z. unfold rename.
    destruct (peq z x); subst; simpl.
    - now rewrite M.gss, extend_gss.
    - now rewrite M.gso, extend_gso.
  Qed.

  Lemma rename_set_WraperFun_f_eq m x y :
    f_eq (rename (M.set x (WrapperFun y) m))
         ((rename m) {x ~> y}).
  Proof.
    intros z. unfold rename.
    destruct (peq z x); subst; simpl.
    - now rewrite M.gss, extend_gss.
    - now rewrite M.gso, extend_gso.
  Qed.

  Lemma rename_not_in_domain_f_eq m x :
    ~ x \in Dom_map m ->
    f_eq (rename m) ((rename m) {x ~> x}).
  Proof with now eauto with Ensembles_DB.
    intros H y. unfold rename.
    destruct (peq y x); subst; simpl.
    - rewrite extend_gss. destruct (M.get x m) eqn:Heq; eauto.
      exfalso. eapply H; eexists; eauto.
    - rewrite extend_gso; eauto.
  Qed.

  Lemma rename_not_in_domain_lst_f_eq m xs :
    Disjoint _ (FromList xs) (Dom_map m) ->
    f_eq (rename m) ((rename m) <{xs ~> xs}>).
  Proof with now eauto with Ensembles_DB.
    induction xs; intros Hnin; simpl; eauto.
    - reflexivity.
    - rewrite <- IHxs. rewrite <- rename_not_in_domain_f_eq. reflexivity.
      normalize_sets. intros Hc. eapply Hnin. constructor; eauto.
      normalize_sets. sets.
  Qed.

  Lemma rename_not_in_domain_add_extend_fundefs_f_eq m B :
    Disjoint _ (name_in_fundefs B) (Dom_map m) ->
    f_eq (rename m) (alpha_conv.extend_fundefs (rename m) B B).
  Proof with now eauto with Ensembles_DB.
    induction B; intros Hnin; simpl; eauto.
    - rewrite <- IHB. rewrite <- rename_not_in_domain_f_eq. reflexivity.
      simpl in *. intros Hc. eapply Hnin. constructor; eauto.
      sets.
    - reflexivity.
  Qed.

  (** * Lemmas about [fun_map] *)


  Lemma fun_map_set_Fun_f_eq m f f' ft vs s fvs :
    f_eq (fun_map (M.set f (Fun f' ft vs s fvs) m))
         ((fun_map m) {f ~> Some (f', ft, fvs)}).
  Proof.
    intros z. unfold fun_map.
    destruct (peq z f); subst; simpl.
    - now rewrite M.gss, extend_gss.
    - now rewrite M.gso, extend_gso.
  Qed.

  Lemma fun_map_set_NoListFun_f_eq m f f' fvs :
    ~ f \in (Dom_map m) ->
    f_eq (fun_map (M.set f (NoLiftFun f' fvs) m))
         (fun_map m).
  Proof.
    intros Hnin z. unfold fun_map.
    destruct (peq z f); subst; simpl.
    - rewrite M.gss.
      destruct (m ! f) eqn:Hget; eauto.
      exfalso. eapply Hnin. eexists; eauto.
    - rewrite M.gso; eauto.
  Qed.

  (** Spec for [get_tag] *)
  Lemma get_tag_spec A P N :
    {{ fun r (s : comp_data * A) => P (next_var (fst s))}}
      get_ftag N
    {{ fun r s x s' => P (next_var (fst s')) }}.
  Proof.
    eapply pre_post_mp_l.
    eapply bind_triple. now eapply get_triple.
    intros [x1 t1] [x2 t2].
    eapply pre_curry_l. intros H; inv H. destruct x2. simpl.
    eapply bind_triple. eapply pre_strenghtening. 2:{ now eapply put_triple. }
    now clear; firstorder.
    intros x [x3 t3]. apply return_triple.
    intros. inv H. eassumption.
  Qed.


  (** [add_functions] is sound w.r.t. its relational spec *)
  Lemma add_functions_true_sound B fvs sfvs args fm gfuns fvm S :
    Disjoint _ (S :|: bound_var_fundefs B) (Dom_map fvm) ->
    (Datatypes.length fvs =? Datatypes.length args)%nat = true ->
    {{ fun r s => fresh S (next_var (fst s)) }}
      add_functions B fvs sfvs args fm gfuns
    {{ fun r s m s' =>
         let '(fm', gfuns') := m in
         exists σ ζ S',
           Add_functions B args (rename fvm) (fun_map fm) S σ ζ S' /\
           name_in_fundefs B \subset (domain (fun_map fm')) /\
           Dom_map fm' <--> Dom_map fm :|: name_in_fundefs B /\
           f_eq σ (rename fvm) /\
           f_eq ζ (fun_map fm') /\
           fresh S' (next_var (fst s')) }}.
  Proof with now eauto with Ensembles_DB.
    revert fm S. induction B; intros m S Hnin Hbeq.
    - eapply bind_triple.
      + eapply IHB.
        normalize_bound_var_in_ctx... eassumption.
      + intros [fm' gfuns'] s1. simpl. eapply pre_existential; intros g1.
        eapply pre_existential; intros g2.
        eapply pre_existential; intros S'.
        eapply pre_curry_l. intros Hadd.
        eapply pre_curry_l. intros Hin.
        eapply pre_curry_l. intros Hdom.
        eapply pre_curry_l. intros Hfeq1.
        eapply pre_curry_l. intros Hfeq2.
        rewrite Hbeq.
        simpl.
        eapply bind_triple. now apply get_name_spec.
        intros x s2. eapply pre_curry_l. intros Hf'.
        eapply bind_triple.
        apply get_tag_spec with (P := fun s => x \in (Range (next_var (fst s2)) s) /\
                                                     (next_var (fst s2) < s)%positive /\
                                                     fresh (S' \\ [set x]) s).
        intros ft s3. apply return_triple. intros _ s4 Hf. destructAll.
        do 3 eexists. split ; [| split; [| split; [| split; [| split ]]]].

        -- econstructor. eassumption. eassumption.
        -- rewrite fun_map_set_Fun_f_eq. rewrite <- domain_extend_Some. sets.
        -- rewrite Dom_map_set. rewrite Hdom. sets.
        -- symmetry. rewrite Hfeq1, <- !rename_not_in_domain_f_eq. reflexivity.
           intros Hc. eapply Hnin. constructor; [| eassumption ]. left.
           eapply Add_functions_free_set_Included; eauto.
           intros Hc. eapply Hnin. constructor; [| eassumption ]. right.
           now constructor.
        -- symmetry. rewrite Hfeq2. apply fun_map_set_Fun_f_eq.
        -- eassumption.
    - apply return_triple. intros _ s Hf.
      do 3 eexists; eauto. split. constructor; reflexivity.
      split. sets. split. simpl. sets. split. reflexivity. split. reflexivity. eassumption.
  Qed.

  Lemma add_functions_false_sound B fvs sfvs args fm gfuns S :
    Disjoint _ (bound_var_fundefs B) (Dom_map fm) ->
    unique_bindings_fundefs B ->
    (Datatypes.length fvs =? Datatypes.length args)%nat = false ->
    {{ fun r s => fresh S (next_var (fst s)) }}
      add_functions B fvs sfvs args fm gfuns
    {{ fun r s m s' =>
         let '(fm', gfuns') := m in
         Dom_map fm' <--> Dom_map fm :|: name_in_fundefs B /\
         Disjoint _ (name_in_fundefs B) (domain (fun_map fm')) /\
         f_eq (fun_map fm) (fun_map fm') /\
         fresh S (next_var (fst s')) }}.
  Proof with now eauto with Ensembles_DB.
    revert fm S. induction B; intros fm S Hdis Hun Hbeq.
    - eapply bind_triple.
      + eapply IHB.
        normalize_bound_var_in_ctx. now sets. inv Hun. eassumption.
        eassumption.
      + intros [fm' gfuns'] s1. simpl.
        eapply pre_curry_l. intros Heq.
        (* eapply pre_curry_l. intros Hfeq1. *)
        rewrite Hbeq.
        simpl. apply return_triple. intros _ s4 Hf. destructAll.
        split; [| split; [| split ]].
        * rewrite Dom_map_set, Heq. now sets.
        * eapply Union_Disjoint_l.
          2:{ rewrite fun_map_set_NoListFun_f_eq. eassumption.
              inv Hun.
              intros Hc. eapply Heq in Hc. inv Hc; eauto.
              eapply Hdis. constructor. now eauto. eassumption.
              eapply H8. eapply name_in_fundefs_bound_var_fundefs. eassumption. }
          eapply Disjoint_Singleton_l. intros Hc.
          unfold domain, fun_map, In in *. destruct Hc. rewrite M.gss in H2. congruence.
        * symmetry. rewrite H0; eauto. eapply fun_map_set_NoListFun_f_eq.
          intros Hnin. eapply Heq in Hnin. inv Hnin.
          -- eapply Hdis. constructor; eauto.
          -- inv Hun; eauto. eapply H9. eapply name_in_fundefs_bound_var_fundefs.
             eassumption.
        * eassumption.
    - apply return_triple. intros s Hf Hs.
      split. simpl; now sets. split. now sets.
      split. reflexivity.
      eassumption.
  Qed.

  (** [make_wrappers] is sound *)

  Lemma make_wrappers_sound_subset S B fv fm :
    name_in_fundefs B \subset (domain (fun_map fm)) ->
    {{ fun r s => fresh S (next_var (fst s)) }}
      make_wrappers B fv fm
    {{ fun r s r s' =>
         let (o, fv') := r in
         exists B' σ S',
           o = Some B' /\
           Make_wrappers (fun_map fm) (rename fv) B S B' S' σ /\
           f_eq (rename fv') σ /\
           Dom_map fv' <--> name_in_fundefs B :|: Dom_map fv /\
           fresh S' (next_var (fst s'))
    }}.
  Proof.
    revert S; induction B; intros S Hsub.
    - unfold make_wrappers.
      destruct (fm ! v) eqn:Hget.
      + destruct f0.
        eapply bind_triple. eapply get_name_spec.
        simpl. intros z [c u].
        eapply pre_curry_l. intros Hf.
        eapply bind_triple.
        eapply frame_rule. eapply frame_rule.
        now eapply get_names_lst_spec.
        intros xs [c' u'].
        eapply pre_curry_l. intros Hf'.
        eapply pre_curry_l. intros Hlt.
        eapply pre_curry_l. intros Hnd.
        eapply pre_curry_l. intros Hlen.
        eapply pre_curry_l. intros Hsub'.
        eapply bind_triple.
        * eapply frame_rule. eapply frame_rule.
          eapply pre_strenghtening.
          intros. rewrite Setminus_Union, Union_commut, <- Setminus_Union in H.
          eapply H. eapply IHB.
          eapply Included_trans; [| eassumption ]; sets.
        * intros [C fv'] [c'' u'']. destruct C.
          { eapply return_triple.
            simpl; intros. destructAll.
            do 3 eexists. split; [| split; [| split ]].
            -- reflexivity.
            -- inv H1. econstructor; eauto.
               unfold fun_map. rewrite Hget. reflexivity.
               eapply Included_trans. eapply Hsub'. now sets.
               constructor; eauto. intros Hc. eapply Hsub'; eauto.
            -- simpl. rewrite rename_set_WraperFun_f_eq. rewrite H3. reflexivity.
            -- rewrite Dom_map_set, H4. sets. }
          { eapply return_triple. simpl; intros. destructAll. congruence. }
        * exfalso.
          assert (Hin : domain (fun_map fm) v). eapply Hsub. now left.
          destruct Hin. unfold fun_map in *. rewrite Hget in H. congruence.
      + exfalso.
        assert (Hin : domain (fun_map fm) v). eapply Hsub. now left.
        destruct Hin. unfold fun_map in *. rewrite Hget in H. congruence.
    - eapply return_triple. intros. do 3 eexists. split.
      reflexivity. split. constructor. split. reflexivity. split. simpl. sets. eassumption.
  Qed.

  Lemma make_wrappers_sound_Disjoint S B fv fm :
    B <> Fnil ->
    name_in_fundefs B \subset Dom_map fm ->
    Disjoint _ (name_in_fundefs B) (domain (fun_map fm)) ->
    {{ fun r s => fresh S (next_var (fst s)) }}
      make_wrappers B fv fm
    {{ fun r s r s' =>
         let (o, fv') := r in
         o = None /\
         fv = fv' /\
         fresh S (next_var (fst s'))
    }}.
  Proof.
    intros Hneq Hin Hdis. destruct B.
    - unfold make_wrappers.
      destruct (fm ! v) eqn:Hget.
      + destruct f0.
        exfalso.
        eapply Hdis. constructor. now left. eexists. unfold fun_map. rewrite Hget. reflexivity.
        eapply return_triple. intros. split; eauto.
      + exfalso.
        assert (Hin' : Dom_map fm v). eapply Hin. now left.
        destruct Hin'. congruence.
    - congruence.
  Qed.

  (** [add_free_var] spec *)
  Lemma add_free_vars_f_eq xs fvm S P :
    Disjoint _ P (Dom_map fvm) ->
    {{ fun r s => fresh S (next_var (fst s)) }}
      add_free_vars xs fvm
    {{ fun r s p s' =>
         let (ys, fvm') := p in
         f_eq ((rename fvm) <{xs ~> ys}>) (rename fvm') /\
         Disjoint _ (Setminus _ P (FromList xs)) (Dom_map fvm') /\
         NoDup ys /\
         FromList ys \subset S /\
         length xs = length ys /\
         fresh (Setminus var S (FromList ys)) (next_var (fst s')) }}.
  Proof with now eauto with Ensembles_DB.
    revert fvm S. induction xs as [| x xs IHxs ]; intros fvm S Hnin.
    - apply return_triple. simpl.
      intros r [w s] Hf. split. reflexivity. split.
      normalize_sets. rewrite Setminus_Empty_set_neut_r. eassumption.
      split. now constructor.
      split. now sets.
      split. reflexivity.
      normalize_sets. rewrite Setminus_Empty_set_neut_r. eassumption.
    - eapply bind_triple.
      + eapply IHxs; eauto.
      + intros [ys m'] _.
        apply pre_curry_l. intros Hfeq1.
        apply pre_curry_l. intros Hnin'.
        apply pre_curry_l. intros Hnd.
        apply pre_curry_l. intros Hall.
        apply pre_curry_l. intros Hlen.
        eapply bind_triple. now apply get_name_spec.
        intros y [w1 s1]. apply return_triple.
        intros s2 [w2 s3] H. destructAll. split; [| split; [| split; [| split; [| split ]]]].
        * simpl. rewrite rename_set_FreeVar_f_eq, Hfeq1.
          reflexivity.
        * normalize_sets. rewrite Dom_map_set. sets.
        * constructor; eauto. intros Hc. simpl in *.
          eapply H. eassumption.
        * normalize_sets. eapply Union_Included; eauto.
          inv H. eapply Singleton_Included. eassumption.
        * simpl; congruence.
        * rewrite FromList_cons, Union_commut, <- Setminus_Union. eassumption.
  Qed.

  (** [Add_functions] up to functional extensionality *)
  Lemma Add_functions_f_eq B fvs σ1 ζ1 σ2 ζ2 S1 S2 σ1' ζ1' S1'  :
    Add_functions B fvs σ1 ζ1 S1 σ2 ζ2 S2 ->
    f_eq σ1 σ1' -> f_eq ζ1 ζ1' -> Same_set _ S1 S1' ->
    exists σ2' ζ2' S2',
      Add_functions B fvs σ1' ζ1' S1' σ2' ζ2' S2' /\
      f_eq σ2 σ2' /\ f_eq ζ2 ζ2' /\ Same_set _ S2 S2'.
  Proof.
    intros Hadd.
    induction Hadd; intros Heq1 Heq2 Heq3.
    - edestruct IHHadd as [σ2' [ζ2' [S2' [Hadd' [Heq1' [Heq2' Heq3']]]]]]; eauto.
      do 3 eexists. split; [| split; [| split ]].
      constructor. eassumption. rewrite <- Heq3'. eassumption.
      rewrite Heq1'. reflexivity. rewrite Heq2'. reflexivity.
      rewrite Heq3'. reflexivity.
    - do 3 eexists. split; [| split; [| split ]]; try eassumption.
      constructor.
  Qed.


  Lemma Add_functions_f_eq' B fvs σ1 ζ1 σ2 ζ2 S1 S2 σ1' ζ1' :
    Add_functions B fvs σ1 ζ1 S1 σ2 ζ2 S2 ->
    f_eq σ1 σ1' -> f_eq ζ1 ζ1' ->
    exists σ2' ζ2',
      Add_functions B fvs σ1' ζ1' S1 σ2' ζ2' S2 /\
      f_eq σ2 σ2' /\ f_eq ζ2 ζ2'.
  Proof.
    intros Hadd.
    induction Hadd; intros Heq1 Heq2.
    - edestruct IHHadd as [σ2' [ζ2' [Hadd' [Heq1' Heq2']]]]; eauto.
      do 2 eexists. split; [| split ].
      constructor. eassumption. eassumption.
      rewrite Heq1'. reflexivity. rewrite Heq2'. reflexivity.
    - do 2 eexists. split; [| split ]; try eassumption.
      constructor.
  Qed.


  Lemma Make_wrappers_f_eq B B' S1 S2 σ1 ζ1 σ2 σ1' ζ1' :
    Make_wrappers ζ1 σ1 B S1 B' S2 σ2 ->
    f_eq σ1 σ1' ->
    f_eq ζ1 ζ1' ->
    exists σ2',
      Make_wrappers ζ1' σ1' B S1 B' S2 σ2' /\
      f_eq σ2 σ2'.
  Proof.
    intros Hadd. revert σ1' ζ1'.
    induction Hadd; intros σ1' ζ1' Heq1 Heq2.
    - eexists. split.
      econstructor. eassumption.
    - edestruct IHHadd as [σ2' [Hadd' Heq']]; eauto.
      eexists. split.
      rewrite Heq1. econstructor; eauto. rewrite <- Heq2. eassumption.
      rewrite Heq'. reflexivity.
  Qed.

  (** * Some Proper instances *)

  Instance FunsFVs_Proper : Proper (f_eq ==> Same_set _) FunsFVs.
  Proof.
    constructor; intros z [f [f' [ft [fvs [Heq Hin]]]]].
    rewrite H in Heq. now repeat eexists; eauto.
    rewrite <- H in Heq. now repeat eexists; eauto.
  Qed.

  Instance lifted_name_Proper : Proper (f_eq ==> f_eq) lifted_name.
  Proof.
    intros f1 f2 Heq x. unfold lifted_name. rewrite Heq; reflexivity.
  Qed.

  Instance Funs_Proper : Proper (f_eq ==> Same_set _) Funs.
  Proof.
    constructor; intros z [f H']; eexists; unfold lifted_name in *.
    rewrite <- H; eassumption.
    rewrite H; eassumption.
  Qed.

  Instance LiftedFuns_Proper : Proper (f_eq ==> Same_set _) LiftedFuns.
  Proof.
    intros f1 f2 Heq. unfold LiftedFuns.
    rewrite !Heq. reflexivity.
  Qed.

  Lemma Exp_lambda_lift_proper_mut :
    (forall e ζ σ ζ' σ' S1 e' S2
       (Hll : Exp_lambda_lift ζ σ e S1 e' S2)
       (Heq1 : f_eq σ σ') (Heq2 : f_eq ζ ζ'),
       Exp_lambda_lift ζ' σ' e S1 e' S2) /\
    (forall B B0 ζ σ ζ' σ' S1 B' S2,
        (forall (Hll : Fundefs_lambda_lift2 ζ σ B0 B S1 B' S2) (Heq1 : f_eq σ σ') (Heq2 : f_eq ζ ζ'),
            Fundefs_lambda_lift2 ζ' σ' B0 B S1 B' S2) /\
        (forall (Hll : Fundefs_lambda_lift3 ζ σ B0 B S1 B' S2) (Heq1 : f_eq σ σ') (Heq2 : f_eq ζ ζ'),
          Fundefs_lambda_lift3 ζ' σ' B0 B S1 B' S2)).
  Proof.
    eapply exp_def_mutual_ind; simpl; intros; try inv Hll.
    - rewrite Heq1. econstructor; eauto. eapply H; eauto.
      rewrite Heq1; reflexivity.
    - rewrite Heq1. econstructor; eauto.
    - rewrite Heq1. econstructor; eauto.
    - rewrite Heq1. econstructor; eauto.
      eapply H; eauto. rewrite Heq1; reflexivity.
    - rewrite !Heq1. eapply LL_Eletapp_known.
      rewrite <- Heq2. eassumption.
      eapply H; eauto.
      rewrite Heq1; reflexivity.
    - rewrite !Heq1. eapply LL_Eletapp_unknown.
      eapply H; eauto.
      rewrite Heq1; reflexivity.
    - edestruct Add_functions_f_eq' as [σ''' [ζ'' [Hadd1 [Heq1' Heq2']]]]; eauto.
      edestruct Make_wrappers_f_eq as [σ2 [S2' Hwr]]. eassumption.
      eassumption. eassumption.
      eapply LL_Efun2.
      eapply Included_trans. eassumption.
      eapply Included_Union_compat. reflexivity.
      eapply Included_Union_compat.
      eapply FunsFVs_Proper. symmetry. eassumption.
      eapply LiftedFuns_Proper. symmetry. eassumption.
      eassumption. eassumption.
      eapply H; eassumption. eassumption.
      eapply H0; eassumption.
    - eapply LL_Efun3.
      eapply H. eassumption. rewrite Heq1. reflexivity. eassumption.
      eapply H0; eauto. rewrite Heq1. reflexivity.
    - rewrite !Heq1. econstructor; eauto. rewrite <- Heq2. eauto.
    - rewrite !Heq1. econstructor; eauto.
    - econstructor. eauto. eapply H; eauto. now rewrite Heq1.
    - rewrite Heq1. econstructor; eauto. eapply H; eauto.
      rewrite Heq1. reflexivity.
    - rewrite Heq1. econstructor; eauto.
    - split; intros.
      + inv Hll.
        edestruct Make_wrappers_f_eq as [σ2 [S2' Hwr]]. eassumption. rewrite Heq1. reflexivity.
        eassumption.
        econstructor; eauto. rewrite <- Heq2; eauto.
        eapply H0. eassumption. eassumption. eassumption.
      + inv Hll. econstructor; eauto.
        eapply H; eauto. rewrite Heq1. reflexivity.
        eapply H0; eauto.
    - split; intros; inv Hll; constructor.
  Qed.

  Instance Exp_lambda_lift_Proper_ζ :
    Proper (f_eq ==> eq ==> eq ==> eq ==> eq ==> eq ==> iff) Exp_lambda_lift.
  Proof.
    constructor; intros; subst;
    eapply Exp_lambda_lift_proper_mut; try eassumption; try reflexivity.
    symmetry. eassumption.
  Qed.

  Instance Exp_lambda_lift_Proper_σ :
    Proper (eq ==> f_eq ==> eq ==> eq ==> eq ==> eq ==> iff) Exp_lambda_lift.
  Proof.
    constructor; intros; subst;
    eapply Exp_lambda_lift_proper_mut; try eassumption; try reflexivity.
    symmetry. eassumption.
  Qed.

  Instance Fundefs_lambda2_lift_Proper_ζ :
    Proper (f_eq ==> eq ==> eq ==> eq ==> eq ==> eq ==> eq ==> iff) Fundefs_lambda_lift2.
  Proof.
    constructor; intros; subst;
    eapply Exp_lambda_lift_proper_mut; try eassumption; try reflexivity.
    symmetry. eassumption.
  Qed.

  Instance Fundefs_lambda2_lift_Proper_σ :
    Proper (eq ==> f_eq ==> eq ==> eq ==> eq ==> eq ==> eq ==> iff) Fundefs_lambda_lift2.
  Proof.
    constructor; intros; subst;
    eapply Exp_lambda_lift_proper_mut; try eassumption; try reflexivity.
    symmetry. eassumption.
  Qed.

  Instance Fundefs_lambda3_lift_Proper_ζ :
      Proper (f_eq ==> eq ==> eq ==> eq ==> eq ==> eq ==> eq ==> iff) Fundefs_lambda_lift3.
  Proof.
    constructor; intros; subst;
    eapply Exp_lambda_lift_proper_mut; try eassumption; try reflexivity.
    symmetry. eassumption.
  Qed.

  Instance Fundefs_lambda3_lift_Proper_σ :
    Proper (eq ==> f_eq ==> eq ==> eq ==> eq ==> eq ==> eq ==> iff) Fundefs_lambda_lift3.
  Proof.
    constructor; intros; subst;
    eapply Exp_lambda_lift_proper_mut; try eassumption; try reflexivity.
    symmetry. eassumption.
  Qed.



  (** Alternative definition for [Funs] *)
  Lemma Funs_Same_set ζ :
    Same_set _ (Funs ζ) (domain ζ).
  Proof.
    split; intros x [y H]. unfold lifted_name in H.
    edestruct (ζ x) eqn:Heq; simpl in H; eauto.
    repeat eexists; eauto.
    inv H.
    destruct y as [[? ?] ?]. eapply lifted_name_eq in H.
    repeat eexists; eauto.
  Qed.

  Lemma Add_functions_name_in_fundefs_Included (B : fundefs) (fvs : list var) (σ : var -> var)
        (ζ : var -> option (var * fun_tag * list var)) (S : Ensemble var)
        (σ' : var -> var) (ζ' : var -> option (var * fun_tag * list var))
        (S' : Ensemble var) :
    Add_functions B fvs σ ζ S σ' ζ' S' ->
    Included var (name_in_fundefs B) (domain ζ').
  Proof with now eauto with Ensembles_DB.
    intros Hadd; induction Hadd.
    - simpl. rewrite <- domain_extend_Some...
    - now eauto with Ensembles_DB.
  Qed.

  (** Soundness of [exp_true_fv] *)
  Section TrueFV_correct.

    Variable (funmap : FunInfoMap).

    Lemma exp_true_fv_fundefs_true_fv_correct lift_dec :
      (forall e Scope FVset x,
         PS.In x (exp_true_fv_aux lift_dec funmap e Scope FVset) ->
         ((In _ (occurs_free e) x /\ ~ PS.In x Scope) \/
          (In _ (Union _ (FunsFVs (fun_map funmap)) (LiftedFuns (fun_map funmap))) x) \/
          PS.In x FVset)) /\
      (forall B Scope FVset,
         let '(Scope', FVset') := fundefs_true_fv_aux lift_dec funmap B Scope FVset in
         (forall x, PS.In x Scope' <-> (PS.In x Scope \/ In _ (name_in_fundefs B) x)) /\
         (forall x, PS.In x FVset' ->
               ((In _ (occurs_free_fundefs B) x /\ ~ PS.In x Scope) \/
                (In _ (Union _ (FunsFVs (fun_map funmap)) (LiftedFuns (fun_map funmap))) x) \/
                PS.In x FVset))).
    Proof.
      exp_defs_induction IHe IHl IHdefs; simpl; intros.
      - eapply IHe in H. inv H.
        + inv H0. left. split. constructor 2; eauto.
          intros Hc. subst. apply H1. now apply_set_specs; eauto.
          intros Hc. apply H1. now apply_set_specs; eauto.
        + inv H0; eauto.
          eapply add_list_spec in H. inv H; eauto.
          inv H0; left; eauto.
      - destruct (PS.mem v Scope) eqn:Heq; eauto.
        repeat apply_set_specs_ctx; eauto. left; split; eauto.
        intros Hc. eapply PS.mem_spec in Hc. congruence.
      - eapply IHl in H. inv H.
        + inv H0. left; eauto.
        + inv H0; eauto. eapply IHe in H. inv H; eauto. inv H0; eauto.
      - eapply IHe in H. inv H.
        + inv H0. left. split. constructor; eauto.
          intros Hc. subst. apply H1. now apply_set_specs; eauto.
          intros Hc. apply H1. now apply_set_specs; eauto.
        + destruct (PS.mem v0 Scope) eqn:Heq; eauto. inv H0; eauto.
          apply_set_specs_ctx; eauto. left; split; eauto.
          intros Hc.  apply PS.mem_spec in Hc. congruence.
      - eapply IHe in H. inv H.
        + inv H0. left. split. eapply Free_Eletapp2; eauto.
          intros Hc. subst. apply H1. now apply_set_specs; eauto.
          intros Hc. apply H1. now apply_set_specs; eauto.
        + inv H0; eauto. eapply add_list_spec in H. inv H.
          * destruct (funmap ! f) eqn:Hget.
            -- destruct f0; eauto. destruct (lift_dec l0 FVset).
                ++ eapply union_list_spec in H0. inv H0.
                   ** repeat apply_set_specs_ctx; eauto.
                      right. left. right. eexists.
                      split. eexists. erewrite lifted_name_eq; eauto.
                      unfold fun_map. simpl.
                      rewrite Hget. reflexivity.
                      unfold lifted_name, fun_map. simpl.
                      rewrite Hget. reflexivity.
                   ** right. left. left. do 4 eexists.
                      unfold fun_map. rewrite Hget. eauto.
                ++ destruct (PS.mem f Scope) eqn:Heq; eauto.
                   repeat apply_set_specs_ctx; eauto.
                   left. constructor. constructor; eauto. now left.
                   intros Hc. eapply PS.mem_spec in Hc. congruence.
                ++ destruct (PS.mem f Scope) eqn:Heq; eauto.
                   repeat apply_set_specs_ctx; eauto.
                   left. constructor. constructor; eauto. now left.
                   intros Hc. eapply PS.mem_spec in Hc. congruence.
            -- destruct (PS.mem f Scope) eqn:Heq; eauto.
               repeat apply_set_specs_ctx; eauto.
               left. constructor. constructor; eauto. now left.
               intros Hc. eapply PS.mem_spec in Hc. congruence.
          * destructAll.
            left. constructor. constructor; eauto. now right. eassumption.
      - destruct (fundefs_true_fv_aux lift_dec funmap f2 Scope FVset) as [Scope' FVset'] eqn:Heq.
        specialize (IHdefs Scope FVset). rewrite Heq in IHdefs.
        destruct IHdefs as [H1 H2].
        eapply IHe in H. inv H.
        + inv H0. left; split. constructor; eauto.
          intros Hc. eapply H3. eapply H1; eauto.
          intros Hc. eapply H3. eapply H1; eauto.
        + inv H0; eauto. eapply H2 in H. inv H; eauto. inv H0; eauto.
      - eapply add_list_spec in H. inv H; eauto.
        + destruct (Maps.PTree.get v funmap) eqn:Heqf.
          destruct f. destruct (lift_dec l1 FVset); eauto.
          * repeat apply_set_specs_ctx; eauto.
            right; left; right. repeat eexists. erewrite lifted_name_eq; eauto.
            unfold fun_map. rewrite Heqf; reflexivity.
            erewrite lifted_name_eq; eauto.
            unfold fun_map. rewrite Heqf; reflexivity.
            right; left; left. repeat eexists.
            unfold fun_map. rewrite Heqf; reflexivity.
            eassumption.
          * destruct (PS.mem v Scope) eqn:Heq; eauto.
            repeat apply_set_specs_ctx; eauto.
            left; split; eauto. intros Hc.
            eapply PS.mem_spec in Hc. congruence.
          * destruct (PS.mem v Scope) eqn:Heq; eauto.
            repeat apply_set_specs_ctx; eauto.
            left. split; eauto. intros Hc.
            eapply PS.mem_spec in Hc. congruence.
          * destruct (PS.mem v Scope) eqn:Heq; eauto.
            repeat apply_set_specs_ctx; eauto.
            left. split; eauto. intros Hc.
            eapply PS.mem_spec in Hc. congruence.
        + destructAll.
          repeat apply_set_specs_ctx; eauto.
      - eapply IHe in H. inv H.
        + inv H0. left. split. eapply Free_Eprim_val ; eauto.
          intros Hc. subst. apply H1. now apply_set_specs; eauto.
          intros Hc. apply H1. now apply_set_specs; eauto.
        + inv H0; eauto.
      - eapply IHe in H. inv H.
        + inv H0. left. split. eapply Free_Eprim2 ; eauto.
          intros Hc. subst. apply H1. now apply_set_specs; eauto.
          intros Hc. apply H1. now apply_set_specs; eauto.
        + inv H0; eauto. eapply add_list_spec in H. inv H; eauto.
          inv H0; left; eauto.
      - destruct (PS.mem v Scope) eqn:Heq; eauto.
        repeat apply_set_specs_ctx; eauto. left; split; eauto.
        intros Hc. eapply PS.mem_spec in Hc. congruence.
      - destruct (fundefs_true_fv_aux lift_dec funmap f5 (PS.add v Scope) FVset) as [Scope' FVset'] eqn:Heq.
        specialize (IHdefs (PS.add v Scope) FVset). rewrite Heq in IHdefs.
        destruct IHdefs as [H1 H2]. split.
        + split; intros H.
          eapply H1 in H; inv H; eauto. repeat apply_set_specs_ctx; eauto.
          eapply H1. inv H; eauto. left. now apply_set_specs; eauto.
          inv H0; eauto. inv H. left. now apply_set_specs; eauto.
        + intros x H. eapply IHe in H. inv H. inv H0. left. split; eauto.
          eapply Free_Fcons1; eauto.
          intros Hc; subst. eapply H3. eapply union_list_spec.
          left. eapply H1; left. now repeat apply_set_specs; eauto.
          intros Hc. eapply H3. eapply union_list_spec. now right; eauto.
          intros Hc. eapply H3. eapply union_list_spec.
          left. now eapply H1; right; eauto.
          intros Hc; subst. eapply H3. eapply union_list_spec.
          left. eapply H1; left. now repeat apply_set_specs; eauto.
          inv H0; eauto.
          eapply H2 in H. inv H; eauto. inv H0; eauto. left; split; eauto.
          constructor 2; eauto.
          intros Hc; subst. eapply H3. now repeat apply_set_specs; eauto.
          intros Hc; subst. eapply H3. now repeat apply_set_specs; eauto.
      - split. intros x. split; eauto. intros [H1 | H1]; eauto. inv H1.
        intros x. intros H; eauto.
    Qed.

    Corollary fundefs_true_fv_correct B lift_dec :
      Included var (FromList (PS.elements (fundefs_true_fv lift_dec funmap B)))
               (Union _ (occurs_free_fundefs B)
                      (Union _ (FunsFVs (fun_map funmap)) (LiftedFuns (fun_map funmap)))).
    Proof.
      destruct (exp_true_fv_fundefs_true_fv_correct lift_dec) as [_ H2].
      unfold fundefs_true_fv. specialize (H2 B PS.empty PS.empty).
      destruct (fundefs_true_fv_aux lift_dec funmap B PS.empty PS.empty) as [scope fvs].
      intros x H. inv H2.
      assert (Hin : PS.In x fvs).
      { eapply PS.elements_spec1. eapply InA_alt.
        eexists; split; eauto. }
      eapply H1 in Hin. inv Hin.
      inv H2; eauto.
      inv H2; eauto. inv H3.
    Qed.

  End TrueFV_correct.

  (** * The lambda lifting algorithm is sound w.r.t. its relational specification *)
  Lemma lambda_lifting_sound max_args max_push lift_dec :
    (forall (e : exp) (FVmap : VarInfoMap) (FNmap : FunInfoMap) (GFuns: GFunMap)
            (Scope AFuns : PS.t) (S : Ensemble var)
       (Hlf : Disjoint _ (LiftedFuns (fun_map FNmap)) (Union _ S (bound_var e)))
       (Hfvs : Disjoint _ (FunsFVs (fun_map FNmap)) (Union _ S (bound_var e)))
       (Hf : Disjoint _ S (Union _ (bound_var e) (occurs_free e)))
       (HD : Disjoint _ (bound_var e) (occurs_free e))
       (Hnin : Disjoint _  (Union _ S (bound_var e)) (Dom_map FVmap))
       (Hnin' : Disjoint _  (bound_var e) (Dom_map FNmap))

       (Hun : unique_bindings e),
       {{ fun r s => fresh S (next_var (fst s)) }}
         exp_lambda_lift max_args max_push lift_dec e Scope AFuns FVmap FNmap GFuns
       {{ fun r s e' s' =>
           exists S', Exp_lambda_lift (fun_map FNmap) (rename FVmap) e S e' S' /\
                      fresh S' (next_var (fst s'))
        }}) /\
    (forall (B B0 : fundefs) (FVmap : VarInfoMap) (FNmap : FunInfoMap) (GFuns: GFunMap)
            (names AFuns : PS.t) (S : Ensemble var) (no : nat)
       (Hlf : Disjoint _ (LiftedFuns (fun_map FNmap)) (Union _ S (bound_var_fundefs B)))
       (Hfvs : Disjoint _ (FunsFVs (fun_map FNmap)) (Union _ S (bound_var_fundefs B)))
       (Hf : Disjoint _ S ((bound_var_fundefs B :|: occurs_free_fundefs B) :|: bound_var_fundefs B0))
       (Hdis : Disjoint _ (bound_var_fundefs B \\ name_in_fundefs B) (name_in_fundefs B0))
       (HD : Disjoint _ (bound_var_fundefs B) (occurs_free_fundefs B))
       (Hnin : Disjoint _  (Union _ S (bound_var_fundefs B :|: bound_var_fundefs B0)) (Dom_map FVmap))
       (Hnin' : Disjoint _  (bound_var_fundefs B \\ name_in_fundefs B) (Dom_map FNmap))
       (Hun : unique_bindings_fundefs B)
       (Hor : (name_in_fundefs B \subset domain (fun_map FNmap) /\ name_in_fundefs B0 \subset domain (fun_map FNmap)) \/
              (Disjoint _ (name_in_fundefs B) (domain (fun_map FNmap)) /\ Disjoint _ (name_in_fundefs B0) (domain (fun_map FNmap))  ))
       (Hdom : name_in_fundefs B \subset Dom_map FNmap),
       {{ fun r s => fresh S (next_var (fst s)) }}
         fundefs_lambda_lift max_args max_push lift_dec B B0 names AFuns FVmap FNmap GFuns no
         {{ fun r s B' s' =>
              exists S',
                (name_in_fundefs B \subset domain (fun_map FNmap) ->
                 Fundefs_lambda_lift2 (fun_map FNmap) (rename FVmap) B0 B S B' S') /\
                (Disjoint _ (name_in_fundefs B) (domain (fun_map FNmap)) ->
                 Fundefs_lambda_lift3 (fun_map FNmap) (rename FVmap) B0 B S B' S') /\
                fresh S' (next_var (fst s'))
        }}).
  Proof with now eauto with Ensembles_DB functions_BD.
    exp_defs_induction IHe IHl IHB; simpl; intros.
    Opaque exp_lambda_lift fundefs_lambda_lift.
    - eapply bind_triple.
      + inv Hun. repeat normalize_bound_var_in_ctx. eapply IHe; try eauto with Ensembles_DB.
        * eapply Disjoint_Included_r; [| eassumption ].
          rewrite <- bound_var_Econstr.
          now apply bound_var_occurs_free_Econstr_Included.
        * eapply Disjoint_Included_r. now apply occurs_free_Econstr_Included.
          eapply Union_Disjoint_r. now eauto with Ensembles_DB.
          eapply Disjoint_Singleton_r; eassumption.
      + intros x s1. apply return_triple.
        intros _ [c2 _u] [S' [Hexp Hfr]]. eexists; split; eauto.
        constructor; eauto. rewrite <- rename_not_in_domain_f_eq.
        eassumption.
        repeat normalize_bound_var_in_ctx. eapply Disjoint_In_l. eassumption. sets.
    - eapply return_triple. intros s Hfr.
      eexists. split; eauto. constructor.
    - setoid_rewrite assoc. eapply bind_triple.
      + inv Hun. repeat normalize_bound_var_in_ctx.
        eapply IHe; try eauto with Ensembles_DB.
        * eapply Disjoint_Included_r; [| eassumption ].
          normalize_occurs_free...
        * eapply Disjoint_Included; [| | now apply HD ].
          normalize_occurs_free...
          now eauto with Ensembles_DB.
      + intros e' s1. simpl.
        setoid_rewrite st_eq_Ecase. eapply pre_existential.
        intros S1. eapply pre_curry_l; intros Hll.
        eapply bind_triple.
        * { repeat normalize_bound_var_in_ctx.
            eapply IHl with (FVmap := FVmap) (FNmap := FNmap) (S := S1).
            - eapply Disjoint_Included_r; [| eassumption ].
              eapply Included_Union_compat;
              [ now eapply Exp_Lambda_lift_free_set_Included; eauto |]...
            - eapply Disjoint_Included_r; [| eassumption ].
              eapply Included_Union_compat;
              [ now eapply Exp_Lambda_lift_free_set_Included; eauto |]...
            - eapply Disjoint_Included_l.
              now eapply Exp_Lambda_lift_free_set_Included; eauto.
              eapply Disjoint_Included_r; [| eassumption ].
              normalize_occurs_free...
            - eapply Disjoint_Included; [| | now apply HD ].
              normalize_occurs_free...
              now eauto with Ensembles_DB.
            - eapply Exp_Lambda_lift_free_set_Included in Hll.
              sets.
            - sets.
            - inv Hun; eauto. }
        * intros e1 s2. eapply pre_existential.
          intros S2. eapply pre_curry_l; intros Hll'.
          edestruct Exp_lambda_lift_Ecase as [P' [Heq Hall]]. eassumption.
          subst. eapply return_triple.
          intros s3 Hfr. eexists. split; eauto.
          econstructor; eauto.
    - eapply bind_triple.
      + inv Hun. repeat normalize_bound_var_in_ctx. eapply IHe; try eauto with Ensembles_DB.
        * eapply Disjoint_Included_r; [| eassumption ].
          rewrite <- bound_var_Eproj.
          now apply bound_var_occurs_free_Eproj_Included.
        * eapply Disjoint_Included_r. now apply occurs_free_Eproj_Included.
          eapply Union_Disjoint_r. now eauto with Ensembles_DB.
          eapply Disjoint_Singleton_r; eassumption.
      + intros x s1. apply return_triple.
        intros _ [c2 _u] [S' [Hexp Hfr]]. eexists; split; eauto.
        constructor; eauto. rewrite <- rename_not_in_domain_f_eq.
        eassumption.
        repeat normalize_bound_var_in_ctx. eapply Disjoint_In_l. eassumption. sets.
    - eapply bind_triple.
      + inv Hun. repeat normalize_bound_var_in_ctx. eapply IHe; try eauto with Ensembles_DB.
        * eapply Disjoint_Included_r; [| eassumption ].
          rewrite <- bound_var_Eletapp.
          now apply bound_var_occurs_free_Eletapp_Included.
        * eapply Disjoint_Included_r. now apply occurs_free_Eletapp_Included.
          eapply Union_Disjoint_r. now eauto with Ensembles_DB.
          eapply Disjoint_Singleton_r; eassumption.
      + intros z s1. simpl. destruct (FNmap ! f) eqn:Hget.
        destruct f0. destruct (lift_dec l0 Scope).
        * apply return_triple.
          intros _ [c2 _u] [S' [Hexp Hfr]]. eexists; split; eauto.
          constructor; eauto. unfold fun_map. rewrite Hget. reflexivity. rewrite <- rename_not_in_domain_f_eq.
          eassumption.
          repeat normalize_bound_var_in_ctx. eapply Disjoint_In_l. eassumption. sets.
        * apply return_triple.
          intros _ [c2 _u] [S' [Hexp Hfr]]. eexists; split; eauto.
          eapply LL_Eletapp_unknown.
          rewrite <- rename_not_in_domain_f_eq.
          eassumption.
          repeat normalize_bound_var_in_ctx. eapply Disjoint_In_l. eassumption. sets.
        * apply return_triple.
          intros _ [c2 _u] [S' [Hexp Hfr]]. eexists; split; eauto.
          eapply LL_Eletapp_unknown.
          rewrite <- rename_not_in_domain_f_eq.
          eassumption.
          repeat normalize_bound_var_in_ctx. eapply Disjoint_In_l. eassumption. sets.
        * apply return_triple.
          intros _ [c2 _u] [S' [Hexp Hfr]]. eexists; split; eauto.
          eapply LL_Eletapp_unknown.
          rewrite <- rename_not_in_domain_f_eq.
          eassumption.
          repeat normalize_bound_var_in_ctx. eapply Disjoint_In_l. eassumption. sets.
    - assert (HFV : Included var (FromList (PS.elements (fundefs_true_fv lift_dec FNmap f2)))
                             (Union var (occurs_free_fundefs f2)
                                    (Union var (FunsFVs (fun_map FNmap)) (LiftedFuns (fun_map FNmap)))))
        by eapply fundefs_true_fv_correct.
      set (fvs := (PS.filter
                      (fun x : PS.elt =>
                         match GFuns ! x with
                         | Some _ => false
                         | None => true
                         end) (fundefs_true_fv lift_dec FNmap f2))).

      set (args := (if
                       (max_args - fundefs_max_params f2 <?
                        Datatypes.length
                          (if
                              existsb (fun x : var => max_push <? stack_push_fundefs x f2)
                                      (PS.elements fvs)
                            then []
                            else PS.elements fvs))%nat
                     then []
                     else
                       if
                         existsb (fun x : var => (max_push <? stack_push_fundefs x f2)%nat)
                                 (PS.elements fvs)
                       then []
                       else PS.elements fvs)).

      assert (Hsub : FromList args \subset FromList (PS.elements (fundefs_true_fv lift_dec FNmap f2))).
      { unfold args.
        destruct (_ <? _)%nat. normalize_sets. now sets.
        destruct (existsb _). normalize_sets. now sets.
        unfold fvs. rewrite <- !FromSet_elements.
        intros s Hin. eapply FromSet_sound in Hin; [| reflexivity ].
        eapply PS.filter_spec in Hin. destructAll. eapply FromSet_complete. reflexivity. eassumption.
        clear. intro; intros. subst. reflexivity. }
      assert (Hndargs : NoDup args).
      { unfold args.
        destruct (_ <? _)%nat. now constructor.
        destruct (existsb _). now constructor.
        unfold fvs.
        eapply NoDupA_NoDup. eapply PS.elements_spec2w. }

      destruct (Datatypes.length (PS.elements fvs) =? Datatypes.length args)%nat eqn:Heqb.
      { eapply bind_triple.
        + eapply add_functions_true_sound; eauto.
          repeat normalize_bound_var_in_ctx.
          eapply Disjoint_Included_l; [| eassumption ]. sets.
        + intros [m gm] [s1 _u]. eapply pre_existential. intros σ'.
          eapply pre_existential. intros ζ'. eapply pre_existential. intros S1.
          eapply pre_curry_l. intros Hadd. eapply pre_curry_l. intros Hsub'.
          eapply pre_curry_l. intros Hdom.
          eapply pre_curry_l. intros Heq1. eapply pre_curry_l. intros Heq2.
          eapply bind_triple.
          * { inv Hun. eapply IHB; eauto.
              - rewrite <- Heq2. eapply Disjoint_Included_l.
                eapply Add_functions_LiftedFuns_Included_r. eassumption.
                eapply Union_Disjoint_l.
                eapply Disjoint_Included_r; [| eassumption ].
                eapply Included_Union_compat.
                now eapply Add_functions_free_set_Included; eauto.
                normalize_bound_var...
                eapply Union_Disjoint_r. now eauto with Ensembles_DB.
                eapply Disjoint_Included; [| | now apply Hf ].
                normalize_bound_var... now eauto with Ensembles_DB.
              - rewrite <- Heq2. eapply Disjoint_Included_l.
                eapply Add_functions_FunsFVs_Included_r. eassumption.
                eapply Union_Disjoint_l.
                eapply Disjoint_Included_r; [| eassumption ].
                eapply Included_Union_compat.
                now eapply Add_functions_free_set_Included; eauto.
                normalize_bound_var...
                repeat sets.
                eapply Disjoint_Included_l; [ eassumption |].
                eapply Disjoint_Included_l; [ eassumption |].
                eapply Union_Disjoint_l.
                eapply Disjoint_sym. eapply Union_Disjoint_l.
                eapply Disjoint_Included; [| | now apply Hf ].
                normalize_occurs_free...
                now eapply Add_functions_free_set_Included; eauto.
                eapply Disjoint_Included; [| | now apply HD ].
                normalize_occurs_free... normalize_bound_var...
                eapply Union_Disjoint_l.
                eapply Disjoint_Included_r; [| eassumption ].
                eapply Included_Union_compat.
                now eapply Add_functions_free_set_Included; eauto.
                normalize_bound_var...
                eapply Disjoint_Included_r; [| eassumption ].
                eapply Included_Union_compat.
                now eapply Add_functions_free_set_Included; eauto.
                normalize_bound_var...
              - eapply Disjoint_Included; [| | now apply Hf].
                normalize_bound_var. normalize_occurs_free...
                now eapply Add_functions_free_set_Included; eauto.
              - now sets.
              - eapply Disjoint_Included; [| | now apply HD].
                normalize_occurs_free...
                normalize_bound_var...
              - eapply Disjoint_Included_l; [| eassumption ].
                normalize_bound_var. eapply Add_functions_free_set_Included in Hadd.
                sets.
              - rewrite Hdom. repeat normalize_bound_var_in_ctx.
                eapply Union_Disjoint_r. now sets.
                sets.
              - rewrite Hdom. sets. }
          * intros B' s2. eapply pre_existential. intros S2.
            eapply pre_curry_l. intros Hll.
            eapply pre_curry_l. intros HDis.
            eapply bind_triple.
            { eapply make_wrappers_sound_subset. eassumption. }
            { intros [Bw m'] [c u]. inv Hun. repeat normalize_bound_var_in_ctx.
              eapply pre_existential. intros Bw'.
              eapply pre_existential. intros sig.
              eapply pre_existential. intros S'.
              eapply pre_curry_l. intros Hbw. subst.
              eapply pre_curry_l. intros Hw.
              eapply pre_curry_l. intros Hfeq.
              eapply pre_curry_l. intros Hdom'.
              eapply bind_triple.
              assert (Hfs : S' \subset S).
              { eapply Included_trans.
                now eapply Make_wrappers_free_set_Included; eauto. eapply Included_trans.
                now eapply Fundefs_Lambda_lift_free_set_Included2; eauto.
                now eapply Add_functions_free_set_Included; eauto. }

              eapply IHe; eauto.
              - rewrite <- Heq2. eapply Disjoint_Included_l.
                eapply Add_functions_LiftedFuns_Included_r. eassumption.
                eapply Union_Disjoint_l.
                eapply Disjoint_Included_r; [| eassumption ].
                eapply Included_Union_compat. eassumption.
                now sets.
                eapply Union_Disjoint_r.
                eapply Disjoint_Included_r.
                now eapply Make_wrappers_free_set_Included; eauto.
                eapply Disjoint_Included_r.
                now eapply Fundefs_Lambda_lift_free_set_Included2; eauto.
                now sets. sets.
              - rewrite <- Heq2. eapply Disjoint_Included_l.
                eapply Add_functions_FunsFVs_Included_r. eassumption.
                eapply Union_Disjoint_l.
                eapply Disjoint_Included_r; [| eassumption ].
                eapply Included_Union_compat. eassumption.
                now eauto with Ensembles_DB.
                eapply Disjoint_Included_l; [ eassumption |].
                eapply Disjoint_Included_l; [ eassumption |].
                repeat normalize_occurs_free_in_ctx.
                eapply Union_Disjoint_l; sets.
                + eapply Union_Disjoint_r; sets.
                  eapply Disjoint_sym. eapply Disjoint_Included; [| | eapply Hf ]. now sets.
                  eassumption.
                  eapply Disjoint_sym. eapply Disjoint_Included; [| | eapply HD]; sets.
                + eapply Union_Disjoint_l; sets.
              - eapply Disjoint_Included; [| | now apply Hf].
                eapply Union_Included. now eauto with Ensembles_DB.
                eapply Included_trans. now eapply occurs_free_Efun_Included.
                eapply Union_Included. now eauto with Ensembles_DB.
                eapply Included_trans. now apply name_in_fundefs_bound_var_fundefs.
                now eauto with Ensembles_DB. eassumption.
              - eapply Disjoint_Included_r.
                now apply occurs_free_Efun_Included.
                eapply Union_Disjoint_r. now eauto with Ensembles_DB.
                eapply Disjoint_Included_r. now apply name_in_fundefs_bound_var_fundefs.
                assumption.
              - rewrite Hdom'. eapply Union_Disjoint_r; sets.
                eapply Disjoint_Included_r. eapply name_in_fundefs_bound_var_fundefs.
                eapply Union_Disjoint_l; eauto.
                eapply Disjoint_Included; [| | eapply Hf ]; sets.
              - rewrite Hdom. eapply Union_Disjoint_r; sets.
                eapply Disjoint_Included_r. now apply name_in_fundefs_bound_var_fundefs.
                eassumption.
              - intros e' s3. eapply return_triple. intros _ s4 [S3 [Hll' Hfr]].
                eexists; split.
                edestruct Make_wrappers_f_eq. eassumption. symmetry. eassumption. symmetry. eassumption.
                destructAll.

                eapply LL_Efun2; [ | | | | eapply H | ]. 5:{ rewrite <- H0, <- Hfeq, Heq2. eassumption. }
                4:{ rewrite Heq2, Heq1. eapply Hll. eassumption. }
                3:{ eassumption. }
                eapply Included_trans. eassumption.
                eapply Included_trans. eassumption.

                edestruct Add_functions_f_eq. eassumption. symmetry. eassumption. reflexivity.
                reflexivity.  reflexivity. eassumption. eassumption. } }
      { inv Hun. eapply bind_triple.
        + eapply add_functions_false_sound; eauto.
          repeat normalize_bound_var_in_ctx.
          eapply Disjoint_Included_l; [| eassumption ]. sets.
        + intros [m gm] [s1 _u].
          eapply pre_curry_l. intros Hdom.
          eapply pre_curry_l. intros Heq1. eapply pre_curry_l. intros Heq2.
          eapply bind_triple.
          * { repeat normalize_bound_var_in_ctx. repeat normalize_occurs_free_in_ctx.
              eapply IHB; eauto.
              - rewrite <- Heq2. eapply Disjoint_Included_l. reflexivity.
                 now sets.
              - rewrite <- Heq2. now sets.
              - now sets.
              - now sets.
              - eapply Disjoint_Included; [| | now apply HD]; sets.
              - now sets.
              - rewrite Hdom. now sets.
              - rewrite Hdom. now sets. }
          * intros B' s2. eapply pre_existential. intros S2.
            eapply pre_curry_l. intros Hll.
            eapply pre_curry_l. intros HDis.
            eapply bind_triple.
            { eapply make_wrappers_sound_Disjoint.
              - intro. subst. simpl in *. repeat normalize_sets. congruence.
              - rewrite Hdom. sets.
              - eassumption. }
            { intros [Bw m'] [c u].
              eapply pre_curry_l. intro; subst.
              eapply pre_curry_l. intro; subst.
              eapply bind_triple.
              repeat normalize_bound_var_in_ctx.
              repeat normalize_occurs_free_in_ctx.
              eapply IHe; eauto.
              - rewrite <- Heq2.
                eapply Union_Disjoint_r.
                eapply Disjoint_Included_r.
                eapply Fundefs_Lambda_lift_free_set_Included3; eauto.
                now sets. now sets.
              - rewrite <- Heq2.
                eapply Union_Disjoint_r.
                eapply Disjoint_Included_r.
                eapply Fundefs_Lambda_lift_free_set_Included3; eauto.
                now sets. now sets.
              - eapply Disjoint_Included; [| | now apply Hf].
                rewrite !Union_assoc. rewrite Union_Setminus_Included.
                now sets. tci. eapply Included_trans. eapply name_in_fundefs_bound_var_fundefs. now sets.
                eapply Fundefs_Lambda_lift_free_set_Included3; eauto.
              - eapply Disjoint_Included_r. eapply Included_Union_Setminus with (s2 := name_in_fundefs f2).
                tci.
                eapply Union_Disjoint_r.
                eapply Disjoint_Included; [| | eapply HD ]; now sets.
                eapply Disjoint_Included_r; [| eassumption ].
                eapply name_in_fundefs_bound_var_fundefs.
              - eapply Union_Disjoint_l.
                eapply Disjoint_Included_l.
                eapply Fundefs_Lambda_lift_free_set_Included3; eauto.
                now sets. now sets.
              - rewrite Hdom. eapply Union_Disjoint_r; sets.
                eapply Disjoint_Included_r. eapply name_in_fundefs_bound_var_fundefs.
                eassumption.
              - intros e' s3. eapply return_triple. intros _ s4 [S3 [Hll' Hfr]].
                eexists; split.  eapply LL_Efun3.
                rewrite <- rename_not_in_domain_add_extend_fundefs_f_eq. rewrite Heq2.
                now eauto.
                eapply Disjoint_Included_l. eapply name_in_fundefs_bound_var_fundefs.
                repeat normalize_bound_var_in_ctx. now sets.
                rewrite <- rename_not_in_domain_add_extend_fundefs_f_eq. rewrite Heq2. eassumption.
                eapply Disjoint_Included_l. eapply name_in_fundefs_bound_var_fundefs.
                repeat normalize_bound_var_in_ctx. now sets.
                eassumption. } }
    - edestruct (M.get v FNmap) as [ [ | ] | ] eqn:Heq.
      destruct (lift_dec l1 Scope).
      + eapply return_triple; intros u s1 Hfr.
        eexists. split; eauto.
        econstructor. unfold fun_map. rewrite Heq. reflexivity.
      + eapply return_triple; intros u s1 Hfr.
        eexists. split; eauto.
        econstructor.
      + eapply return_triple; intros u s1 Hfr.
        eexists. split; eauto.
        econstructor.
      + eapply return_triple; intros u s1 Hfr.
        eexists. split; eauto.
        econstructor.
    - simpl. eapply bind_triple.
      + inv Hun. repeat normalize_bound_var_in_ctx. eapply IHe; try eauto with Ensembles_DB.
        * eapply Disjoint_Included_r; [| eassumption ].
          rewrite <- bound_var_Eprim_val.
          now apply bound_var_occurs_free_Eprim_val_Included.
        * eapply Disjoint_Included_r. now apply occurs_free_Eprim_val_Included.
          eapply Union_Disjoint_r. now eauto with Ensembles_DB.
          eapply Disjoint_Singleton_r; eassumption.
      + intros x s1. apply return_triple.
        intros _ [c2 _u] [S' [Hexp Hfr]]. eexists; split; eauto.
        constructor; eauto. rewrite <- rename_not_in_domain_f_eq.
        eassumption.
        repeat normalize_bound_var_in_ctx. eapply Disjoint_In_l. eassumption. sets.
    - simpl. eapply bind_triple.
      + inv Hun. repeat normalize_bound_var_in_ctx. eapply IHe; try eauto with Ensembles_DB.
        * eapply Disjoint_Included_r; [| eassumption ].
          rewrite <- bound_var_Eprim.
          now apply bound_var_occurs_free_Eprim_Included.
        * eapply Disjoint_Included_r. now apply occurs_free_Eprim_Included.
          eapply Union_Disjoint_r. now eauto with Ensembles_DB.
          eapply Disjoint_Singleton_r; eassumption.
      + intros x s1. apply return_triple.
        intros _ [c2 _u] [S' [Hexp Hfr]]. eexists; split; eauto.
        constructor; eauto. rewrite <- rename_not_in_domain_f_eq.
        eassumption.
        repeat normalize_bound_var_in_ctx. eapply Disjoint_In_l. eassumption. sets.
    - eapply return_triple. intros s1 Hfr. eexists. split; eauto.
      econstructor.
    - inv Hun.
      repeat normalize_bound_var_in_ctx. repeat normalize_occurs_free_in_ctx. inv Hor.
      { (* Case Lifted Funs *)
        edestruct (M.get v FNmap) eqn:Heq'; try discriminate.
        destruct f.
        + eapply bind_triple.
          * eapply add_free_vars_f_eq. eassumption.
          * destructAll. intros [ys map'] _. apply pre_curry_l. intros Heq1.
            apply pre_curry_l. intros Hnin1. apply pre_curry_l. intros Hnd.
            apply pre_curry_l. intros Hall. apply pre_curry_l. intros Hlen.
            eapply bind_triple.
            eapply make_wrappers_sound_subset. eassumption.
            intros xs' s1. simpl. destruct xs'. apply pre_existential. intros B'.
            apply pre_existential. intros sig. eapply pre_existential. intros S'.
            eapply pre_curry_l. intro; subst. eapply pre_curry_l. intros Hwr. apply pre_curry_l. intros Hfew.
            apply pre_curry_l. intros Hfeq'. eapply bind_triple.
            { eapply IHe; eauto.
              - eapply Disjoint_Included_r; [| eassumption ]. eapply Make_wrappers_free_set_Included in Hwr.
                eapply Union_Included; sets. eapply Included_trans. eassumption. sets.
              - eapply Disjoint_Included_r; [| eassumption ]. eapply Make_wrappers_free_set_Included in Hwr.
                eapply Union_Included; sets. eapply Included_trans. eassumption. sets.
              - eapply Disjoint_Included; [| | eapply Hf ].
                eapply Union_Included. now sets.
                eapply Included_trans. eapply (occurs_free_in_fun v t l e (Fcons v t l e f5)).
                now left; eauto.
                eapply Union_Included. now sets.
                eapply Union_Included. eapply Included_Union_preserv_l.
                eapply Included_trans. apply name_in_fundefs_bound_var_fundefs. normalize_bound_var...
                normalize_occurs_free... eapply Included_trans.
                eapply Make_wrappers_free_set_Included in Hwr.
                eassumption. now eauto with Ensembles_DB.
              - eapply Disjoint_Included_r. eapply (occurs_free_in_fun v t l e (Fcons v t l e f5)).
                now constructor. eapply Union_Disjoint_r.
                eassumption. simpl. eapply Union_Disjoint_r. eapply Union_Disjoint_r.
                eapply Disjoint_Singleton_r. eassumption.
                eapply Disjoint_Included_r. now apply name_in_fundefs_bound_var_fundefs.
                eassumption. normalize_occurs_free. sets.
              - eapply Union_Disjoint_l. eapply Disjoint_Included_l.
                eapply Make_wrappers_free_set_Included. eassumption. rewrite Hfeq'.
                eapply Union_Disjoint_r. eapply Disjoint_Included; [| | eapply Hf ].
                eapply Included_trans. eapply name_in_fundefs_bound_var_fundefs. now sets.
                now sets.
                eapply Disjoint_Included_l; [ | eassumption ].
                rewrite Setminus_Union_distr. rewrite (Setminus_Disjoint S (FromList l1)). now sets.
                eapply Disjoint_sym. eapply Disjoint_Included; [ | | eapply Hfvs ]. now sets.
                intros z Hin. do 4 eexists. split. unfold fun_map. rewrite Heq'. reflexivity. eassumption.
                rewrite Hfeq'. sets. eapply Union_Disjoint_r; sets.
                eapply Disjoint_Included_l; [| eapply Hdis ].
                rewrite !Setminus_Union_distr. do 2 eapply Included_Union_preserv_r. eapply Included_Union_preserv_l.
                rewrite Setminus_Disjoint. now sets. eapply Union_Disjoint_r; sets.
                eapply Disjoint_Included_r. eapply name_in_fundefs_bound_var_fundefs. eassumption.
                eapply Disjoint_Included_l; [| eassumption ].
                rewrite Setminus_Union_distr. rewrite !Setminus_Union_distr.
                rewrite @Setminus_Disjoint with (s1 := bound_var e).
                now sets. eapply Disjoint_sym. eapply Disjoint_Included; [| | eapply Hfvs ]. now sets.
                intros el Hel. do 4 eexists. split. unfold Funs, fun_map. rewrite Heq'. now eauto. eassumption.
              - eapply Disjoint_Included_l; [| eassumption ].
                rewrite !Setminus_Union_distr. do 2 eapply Included_Union_preserv_r. eapply Included_Union_preserv_l.
                rewrite Setminus_Disjoint. now sets. eapply Union_Disjoint_r; sets.
                eapply Disjoint_Included_r. eapply name_in_fundefs_bound_var_fundefs. eassumption. }
            { intros e' s2. eapply pre_existential. intros S1.
              eapply pre_curry_l. intros Hll.
              assert (Hsub : S1 \subset S).
              { eapply Included_trans. eapply Exp_Lambda_lift_free_set_Included. eassumption.
                eapply Included_trans. eapply Make_wrappers_free_set_Included; eauto. now sets. }
              eapply bind_triple.
              - eapply IHB; eauto.
                + eapply Disjoint_Included_r; [| eassumption ]. xsets.
                + eapply Disjoint_Included_r; [| eassumption ]. xsets.
                + eapply Disjoint_Included; [| | now apply Hf].
                  eapply Union_Included. eapply Union_Included. now sets.
                  rewrite !Union_assoc. rewrite @Union_Setminus_Included with (s3 := [set v]); tci.
                  now sets. now sets. now sets. eassumption.
                + eapply Disjoint_Included_l; [| eassumption ].
                  rewrite !Setminus_Union_distr. do 3 eapply Included_Union_preserv_r.
                  rewrite <- Setminus_Union. rewrite @Setminus_Disjoint with (s2 := [set v]).
                  now sets. now sets.
                + eapply Disjoint_Included_r. now apply occurs_free_fundefs_Fcons_Included.
                  eapply Union_Disjoint_r. eapply Disjoint_Included; [| | eapply HD ].
                  normalize_occurs_free. now sets. now sets. now sets.
                + xsets.
                + eapply Disjoint_Included_l; [| eapply Hnin' ].
                  rewrite !Setminus_Union_distr. do 3 eapply Included_Union_preserv_r.
                  rewrite <- Setminus_Union. rewrite @Setminus_Disjoint with (s2 := [set v]).
                  now sets. now sets.
                + left. split; eauto. eapply Included_trans; [| eapply H ]...
                + eapply Included_trans; [| eassumption ]...
              - intros B'' s3. eapply return_triple.
                intros _ s4 [S2 [Hll' Hfr]]. eexists; split; eauto. intros Hsub'.
                assert (Hfeq : f_eq ((rename FVmap) <{ l ++ l1 ~> l ++ ys }>) (rename map')).
                { rewrite extend_lst_app; eauto. rewrite Heq1.
                  rewrite <- rename_not_in_domain_lst_f_eq. reflexivity.
                  eapply Disjoint_Included_l; [| eassumption ].
                  rewrite !Setminus_Union_distr.
                  rewrite @Setminus_Disjoint with (s1 := FromList l). now sets.
                  eapply Disjoint_sym. eapply Disjoint_Included; [| | eapply Hfvs ]. now sets.
                  intros el Hel. do 4 eexists. split. unfold Funs, fun_map. rewrite Heq'. now eauto. eassumption. }
                edestruct Make_wrappers_f_eq. eassumption. symmetry. eassumption. reflexivity.
                inv H1.
                econstructor; try eassumption.
                + unfold fun_map. rewrite Heq'. reflexivity.
                + now eauto.
                + rewrite <- H3, <- Hfew. eassumption.
                + eapply Hll'. eapply Included_trans; [| eassumption ]...
                + split. intros Hdis1. exfalso. eapply Hdis1. constructor. now left.
                  eapply H. now left. eapply Hfr. }
        + exfalso. destructAll.
          assert (Hind:  domain (fun_map FNmap) v).
          { eapply H. now left. }
          destruct Hind. unfold fun_map in *. rewrite Heq' in *. congruence.
        + exfalso. destructAll.
          assert (Hind:  domain (fun_map FNmap) v).
          { eapply H. now left. }
          destruct Hind. unfold fun_map in *. rewrite Heq' in *. congruence. }
      { (* Case No Lifted Funs *)
        edestruct (M.get v FNmap) eqn:Heq'; try discriminate.
        destruct f.
        + exfalso. destructAll. eapply H. constructor; eauto. unfold In, domain.
          eexists. unfold fun_map. rewrite Heq'. reflexivity.
        + eapply bind_triple.
          { eapply IHe; eauto.
            - sets.
            - sets.
            - sets. eapply Disjoint_Included_r; [| eassumption ].
              eapply Included_trans. eapply bound_var_occurs_free_Fcons_Included.
              normalize_bound_var. normalize_occurs_free. sets.
            - eapply fun_in_fundefs_Disjoint_bound_Var_occurs_free with (B := (Fcons v t l e f5)).
              now left. constructor; eauto.
              repeat normalize_occurs_free. repeat normalize_bound_var. eassumption.
            - xsets.
            - eapply Disjoint_Included_l ; [| eassumption ].
              rewrite !Setminus_Union_distr. do 2 eapply Included_Union_preserv_r. eapply Included_Union_preserv_l.
              rewrite Setminus_Disjoint. now sets. eapply Union_Disjoint_r; sets.
                eapply Disjoint_Included_r. eapply name_in_fundefs_bound_var_fundefs. eassumption. }
            { intros e' s2. eapply pre_existential. intros S1.
              eapply pre_curry_l. intros Hll.
              assert (Hsub : S1 \subset S).
              { eapply Exp_Lambda_lift_free_set_Included. eassumption. }

              eapply bind_triple.
              - eapply IHB; eauto.
                + sets.
                + sets.
                + eapply Disjoint_Included; [| | now apply Hf].
                  eapply Union_Included. eapply Union_Included. now sets.
                  rewrite !Union_assoc. rewrite @Union_Setminus_Included with (s3 := [set v]); tci.
                  now sets. now sets. now sets. eassumption.
                + eapply Disjoint_Included_l; [| eassumption ].
                  rewrite !Setminus_Union_distr. do 3 eapply Included_Union_preserv_r.
                  rewrite <- Setminus_Union. rewrite @Setminus_Disjoint with (s2 := [set v]).
                  now sets. now sets.
                + eapply Disjoint_Included_r. now apply occurs_free_fundefs_Fcons_Included.
                  eapply Union_Disjoint_r. eapply Disjoint_Included; [| | eapply HD ].
                  normalize_occurs_free. now sets. now sets. now sets.
                + now xsets.
                + eapply Disjoint_Included_l; [| eapply Hnin' ].
                  rewrite !Setminus_Union_distr. do 3 eapply Included_Union_preserv_r.
                  rewrite <- Setminus_Union. rewrite @Setminus_Disjoint with (s2 := [set v]).
                  now sets. now sets.
                + right. inv H. split; eauto. clear H1. now sets.
                + eapply Included_trans; [| eassumption ]...
              - intros B'' s3. eapply return_triple.
                intros _ s4 [S2 [Hll' Hfr]]. eexists; split; eauto.
                + intros Hsub'. exfalso. inv H. eapply H0. constructor; eauto.
                + inv Hfr. split; eauto. intros Hdis2. econstructor.
                  rewrite <- rename_not_in_domain_add_extend_fundefs_f_eq.
                  2:{ eapply Disjoint_Included_l. eapply name_in_fundefs_bound_var_fundefs. sets. }
                  rewrite <- rename_not_in_domain_lst_f_eq. eassumption.
                  now sets. eapply H0. sets. }
        + exfalso. destructAll.
          assert (Hind: Dom_map FNmap v).
          { eapply Hdom. now left. }
          destruct Hind. congruence. }
    - apply return_triple. intros s1 Hfr. eexists; split; eauto.
      intros. constructor.
      split; intros. constructor. eassumption.

      Unshelve.
      eassumption. eassumption. eassumption.
  Qed.


End Lambda_lifting_corresp.
