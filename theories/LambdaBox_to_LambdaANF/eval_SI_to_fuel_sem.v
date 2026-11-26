From Stdlib Require Import Utf8 List ssreflect ssrbool.
From Stdlib Require Import Lia.
Import ListNotations.
Import EqNotations.
From MetaRocq.Erasure Require Import StepIndex.EvalStepIndex.
From MetaRocq.Erasure Require Import EWellformed.
From MetaRocq.Erasure Require Import StepIndex.EvalSIToEval.
From MetaRocq.Erasure Require Import StepIndex.Values.
From CertiRocq.LambdaBox_to_LambdaANF Require Import fuel_sem.


Lemma extract_andb_left {b1 b2 : bool} : (andb b1 b2) = true -> b1 = true.
Proof.
  now destruct b1.
Qed.

Lemma extract_andb_right {b1 b2 : bool} : (andb b1 b2) = true -> b2 = true.
Proof.
  now destruct b1, b2.
Qed.


Lemma nth_error_find_branch brs c v nargs ind :
  nth_error brs c = Some v ->
  length (fst v) = nargs ->
  find_branch ind c nargs brs = Some (snd v).
Proof.
  induction brs as [|[? ?] ? IH] in c |- *; destruct c; simpl; try easy.
  - intros [=[]].
    simpl; intros <-.
    now rewrite PeanoNat.Nat.eqb_refl.
  - now rewrite PeanoNat.Nat.sub_0_r.
Qed.


#[local] Hint Resolve eval_step : core.
#[local] Hint Resolve extract_andb_left : core.
#[local] Hint Resolve extract_andb_right : core.
#[local] Hint Resolve MRPrelude.uip_bool : core.
#[local] Hint Resolve f_equal : core.
#[local] Ltac ok := try solve[simpl in *; easy || eauto].
#[local] Ltac tea := try eassumption.


Section ConvertVals.
  Context {efl : EEnvFlags}.
  Context {hBox : has_tBox = false}.
  Context {hCofix : has_tCoFix = false}.
  Context {hLazy : has_tLazy_Force = false}.
  Context {hPrimArray : has_primarray = false}.
  Context (Σ : EAst.global_declarations).
  Context (wf_Σ : wf_glob Σ).


  (** Primitive integers, floats and strings are translated as is; arrays
      are excluded by [hPrimArray]. *)
  Definition convert_prim {X} (p : EPrimitive.prim_val X) :
    MetaRocq.Erasure.StepIndex.Utils.has_prim p = true -> AstCommon.primitive_value :=
    match p with
    | existT t m =>
      match m as m0 in EPrimitive.prim_model t0
        return MetaRocq.Erasure.StepIndex.Utils.has_prim (existT (@EPrimitive.prim_model X) t0 m0) = true -> AstCommon.primitive_value with
      | EPrimitive.primIntModel i => λ _, existT _ AstCommon.primInt i
      | EPrimitive.primFloatModel f => λ _, existT _ AstCommon.primFloat f
      | EPrimitive.primStringModel s => λ _, existT _ AstCommon.primString s
      | EPrimitive.primArrayModel _ => λ h,
          False_rect _ (Bool.diff_false_true (eq_trans (eq_sym hPrimArray) h))
      end
    end.


  Fixpoint convert_list' (cv : ∀ v, wellformed_val Σ v = true -> value) (vs : list Values.value) : forallb (wellformed_val Σ) vs = true -> list value :=
      match vs with
      | [] => λ _, []
      | v :: vs => λ wf, 
        cv v (extract_andb_left wf) :: 
          (convert_list' cv vs (extract_andb_right wf))
      end.

  #[refine]
  Fixpoint convert_vals (v : Values.value) : wellformed_val Σ v = true -> value :=
    match v return wellformed_val Σ v = true -> value with
    | vConstruct ind c vs => 
        λ wf_v, 
        let vs_wf := extract_andb_right (extract_andb_left wf_v) in
        let new_vs := convert_list' convert_vals vs vs_wf in
        Con_v (ind, BinNat.N.of_nat c) new_vs
    | vClos na t Γ => 
        λ wf_v, 
        let Γ_wf := extract_andb_right (extract_andb_left wf_v) in
        let new_Γ := convert_list' convert_vals Γ Γ_wf in
        Clos_v new_Γ na t
    | vRecClos mfix t Γ =>
        λ wf_v,
        let Γ_wf := 
          extract_andb_right 
            (extract_andb_left (extract_andb_left wf_v))
        in
        let new_Γ := convert_list' convert_vals Γ Γ_wf in
        ClosFix_v new_Γ mfix t
    | vBox => λ wf_v, False_rect _ _
    | vCoFixClos a b c d =>  λ wf_v, False_rect _ _
    | vPrim p => λ wf_v, Prim_v (convert_prim p (extract_andb_left wf_v))
    | vLazy t Γ => λ wf_v, False_rect _ _
    end
  .
  Proof.
    - simpl in *. now rewrite hBox in wf_v.
    - simpl in *. now rewrite hCofix in wf_v. 
    - simpl in *. now rewrite hLazy in wf_v. 
  Defined.

  Definition convert_list := convert_list' convert_vals.

  Lemma length_convert_list l e :
    length (convert_list l e) = length l.
  Proof.
    induction l; ok.
  Qed.


  Lemma convert_list_app l1 l2 h1 h2 h3 :
    convert_list l1 h1 ++ convert_list l2 h2 = 
      convert_list (l1 ++ l2) h3.
  Proof.
    induction l1; cbn; repeat f_equal; ok.
  Qed.

  Lemma convert_list_rev l h h_rev :
    convert_list (rev l) h = rev (convert_list l h_rev).
  Proof.
    induction l; cbn; repeat f_equal.
    unshelve erewrite <-convert_list_app, IHl; ok.
    - simpl in h. now rewrite forallb_app in h.
    - unfold convert_list; simpl. do 3 f_equal; ok.
  Qed.


  Lemma convert_list_cong l1 l2 h1 h2 :
    l1 = l2 ->
    convert_list l1 h1 = convert_list l2 h2.
  Proof.
    now intros ->.
  Qed.

  Lemma nth_error_convert_list l h n v h' :
    nth_error l n = Some v ->
    nth_error (convert_list l h) n = Some (convert_vals v h').
  Proof.
    induction l in n, h |- *; destruct n; cbn; try easy.
    intros [=<-].
    repeat f_equal. ok.
  Qed.

  Lemma make_rec_env_map mfix Γ :
    make_rec_env mfix Γ = map (ClosFix_v Γ mfix) (rev (seq 0 (length mfix))) ++ Γ.
  Proof.
    unfold make_rec_env.
    generalize (length mfix) as n.
    induction n as [|? IHn]; ok.
    now rewrite IHn seq_S rev_unit.
  Qed.

  Lemma fix_env_make_rec_env mfix Γ h1 h2 :
    convert_list (fix_env mfix Γ ++ Γ) h1 = make_rec_env mfix (convert_list Γ h2).
  Proof.
      assert (forallb (wellformed_val Σ) (fix_env mfix Γ) = true) as wf_fix_env.
      { rewrite forallb_app in h1. ok. }
      unshelve erewrite <-convert_list_app; tea.
      rewrite make_rec_env_map.
      do 2 f_equal; ok.
      pose proof eq_sym (fix_env_map mfix Γ) as h.
      destruct h. clear.
      induction (length mfix); first reflexivity.
      rewrite {2}seq_S.
      rewrite rev_app_distr. simpl.
      assert (forallb (wellformed_val Σ) (map (λ n0 : nat, vRecClos mfix n0 Γ) (rev (seq 0 n))) = true) as h.
      { rewrite seq_S rev_app_distr in wf_fix_env. ok. }
      unshelve erewrite <-IHn; ok.
      assert (wellformed_val Σ (vRecClos mfix n Γ) = true) as h'.
      { rewrite seq_S rev_app_distr in wf_fix_env; ok. }
      match goal with 
      | |- _ = ?a :: _ => 
          replace a with (convert_vals (vRecClos mfix n Γ) h'); last first
      end.
      { simpl in *. repeat f_equal. ok. }
      change (convert_vals (vRecClos mfix n Γ) h' :: convert_list (map (λ n0 : nat, vRecClos mfix n0 Γ) (rev (seq 0 n))) h)
      with ([convert_vals (vRecClos mfix n Γ) h'] ++ convert_list (map (λ n0 : nat, vRecClos mfix n0 Γ) (rev (seq 0 n))) h).
      assert (forallb (wellformed_val Σ) (map (λ n, vRecClos mfix n Γ) [n]) = true) as h'' by ok.
      replace [convert_vals (vRecClos mfix n Γ) h'] 
      with (convert_list (map (λ n, vRecClos mfix n Γ) [n]) h''); last first.
      { cbn. do 3 f_equal. ok. }
      unshelve erewrite convert_list_app.
      { now rewrite forallb_app h h''. }
      apply convert_list_cong.
      rewrite <-map_app.
      now rewrite <-(rev_app_distr _ [n]), <-(rev_app_distr [0]), <-seq_S.
  Qed.

End ConvertVals.

Section exist_fuel.
  Context {efl : EEnvFlags}.
  Context {hBox : has_tBox = false}.
  Context {hCofix : has_tCoFix = false}.
  Context {hLazy : has_tLazy_Force = false}.
  Context {hPrimArray : has_primarray = false}.
  Context {hBlocks : cstr_as_blocks = true}.
  Context {hApp : has_tApp = true}.
  Context {hRel : has_tRel = true}.
  Context (Σ : EAst.global_declarations).
  Context (wf_Σ : wf_glob Σ).

  Notation cvt_list := (@convert_list efl hBox hCofix hLazy hPrimArray Σ).
  Notation cvt_vals := (@convert_vals efl hBox hCofix hLazy hPrimArray Σ).

  Ltac assumption_upto_prf := 
    match goal with
    | h: eval_env_step ?Σ ?e1 ?b (Val (cvt_vals ?res _)) _ _ |-
      eval_env_step ?Σ ?e2 ?b (Val (cvt_vals ?res _)) _ _ => replace e2 with e1; first eassumption
    end; cbn.

  Lemma evalSI_to_fuel_sem (trace : Type) (Hf Ht : LambdaBox_resource) Γ e v n wf_Γ wf_v :
    has_cstr_params = false ->
    wellformed Σ (length Γ) e = true ->
    EvalStepIndex.eval Σ Γ e v n ->
    ∃ n' tr, @eval_env_step trace Hf Ht Σ (cvt_list Γ wf_Γ) e (Val (cvt_vals v wf_v)) n' tr.
  Proof.
    intros h_cstr wf_e h_eval.
    assert (is_true (negb has_cstr_params)) as h_cstr' by now rewrite h_cstr.
    revert wf_Γ wf_v wf_e.
    induction h_eval using eval_rect with (Pf := fun _ _ _ _ _ _ => True);
      [intros wf_Γ wf_v wf_e..| exact I | exact I].
    - ok.
    - ok.
    - do 2 eexists.
      constructor.
      induction Γ in n, wf_Γ, e |- *; destruct n; simpl; ok.
      injection e as ?; subst; ok.
    - assert (wellformed Σ (length Γ) a = true) as wf_a by ok.
      assert (wellformed Σ (length Γ) f1 = true) as wf_f1 by ok.
      assert (wellformed_val Σ (vClos na b Γ') = true) as wf_clos.
      { eapply eval_SI_wellformed_val in h_eval1; tea. }
      assert (wellformed_val Σ a' = true) as wf_a'.
      { apply eval_SI_wellformed_val in h_eval2; tea. }
      assert (forallb (wellformed_val Σ) Γ' = true) as wf_Γ' by ok.
      assert (wellformed Σ (S (length Γ')) b = true) as wf_b by ok.
      assert (forallb (wellformed_val Σ) (a' :: Γ') = true) as wf_a'Γ' by ok.
      unshelve epose proof IHh_eval1 wf_Γ _ _ as (n'1 & tr1 & h_eval'1); tea.
      unshelve epose proof IHh_eval2 wf_Γ _ _ as (n'2 & tr2 & h_eval'2); tea.
      unshelve epose proof IHh_eval3 _ _ _ as (n'3 & tr3 & h_eval'3); tea.
      do 2 eexists. simpl.
      econstructor; [ok..|].
      fold cvt_list.
      apply eval_step.
      assumption_upto_prf.
      now repeat f_equal.
    - do 2 eexists.
      erewrite (MRPrelude.uip_bool _ _ wf_Γ).
      constructor.
    - assert (wellformed Σ (length Γ) b0 = true) as wf_b0 by ok.
      assert (wellformed_val Σ b0' = true) as wf_b0'.
      { eapply eval_SI_wellformed_val in h_eval1; tea. }
      assert (forallb (wellformed_val Σ) (b0' :: Γ) = true) as wf_b0'Γ by ok.
      assert (wellformed Σ (length (b0' :: Γ)) b1 = true) as wf_b1 by ok.
      unshelve epose proof IHh_eval1 wf_Γ _ _ as (n'1 & tr1 & h_eval'1); tea.
      unshelve epose proof IHh_eval2 _ _ _ as (n'2 & tr2 & h_eval'2); tea.
      do 2 eexists.
      econstructor; ok.
      constructor.
      assumption_upto_prf.
      now repeat f_equal.
    - assert (wellformed Σ (length Γ) discr = true) as wf_discr by ok.
      assert (wellformed_val Σ (vConstruct ind c args) = true) as wf_vConstr.
      { now apply eval_SI_wellformed_val in h_eval1. }
      assert (forallb (wellformed_val Σ) args = true) as wf_args by ok.
      assert (forallb (wellformed_val Σ) (rev args ++ Γ) = true) as wf_revargsΓ.
      { now rewrite forallb_app MRList.forallb_rev. }
      assert (wellformed Σ (length (rev args ++ Γ)) (snd br) = true) as wf_snd_br.
      { simpl in wf_e. rewrite length_app length_rev e3.
        repeat apply extract_andb_right in wf_e.
        apply (All_Forall.nth_error_forallb e1 wf_e). }
      unshelve epose proof IHh_eval1 wf_Γ _ _ as (n'1 & tr1 & h_eval'1); tea.
      unshelve epose proof IHh_eval2 _ _ _ as (n'2 & tr2 & h_eval'2); tea.
      do 2 eexists.
      econstructor; [ok..| |]; fold cvt_list.
      + rewrite length_convert_list.
        now apply nth_error_find_branch.
      + unshelve erewrite <-convert_list_rev, convert_list_app; [|ok..].
        clear h_eval'2; now rewrite forallb_app in wf_revargsΓ.
    - assert (wellformed_val Σ (vConstruct (Kernames.proj_ind p) 0 args) = true).
      { apply eval_SI_wellformed_val in h_eval; ok. }
      assert (wellformed Σ (length Γ) discr = true) as wf_discr by ok.
      unshelve epose proof IHh_eval _ _ _ as (n' & tr & h_eval'); tea.
      do 2 eexists.
      econstructor; ok.
      pose proof (MetaRocq.Erasure.StepIndex.Utils.constructor_isprop_pars_decl_params h_cstr wf_Σ e2) as hnpars.
      rewrite hnpars in e4. now apply nth_error_convert_list.
    - assert (wellformed_val Σ (vRecClos mfix idx Γ') = true) as wf_recclos. 
      { apply eval_SI_wellformed_val in h_eval1; ok. }
      assert (forallb (wellformed_val Σ) Γ' = true) as wf_Γ' by ok.
      assert (wellformed_val Σ av = true) as wf_av.
      { apply eval_SI_wellformed_val in h_eval2; ok. }
      assert (forallb (wellformed_val Σ) (fix_env mfix Γ') = true).
      { rewrite fix_env_map All_Forall.forallb_map MRList.forallb_rev.
        rewrite forallb_forall.
        intros x ?%in_seq.
        enough ((wf_fix Σ (length Γ') mfix x)%bool = true) by ok.
        unfold wf_fix in *.
        enough (PeanoNat.Nat.ltb x (length mfix) = true) as -> by ok. 
        now apply PeanoNat.Nat.ltb_lt. }
      assert (forallb (wellformed_val Σ) (av :: fix_env mfix Γ' ++ Γ') = true).
      { simpl. now rewrite forallb_app wf_av wf_Γ' Bool.andb_true_r Bool.andb_true_l. }
      assert (wellformed Σ (length Γ) f = true) as wf_f by ok.
      assert (wellformed Σ (length Γ) a = true) as wf_a by ok.
      assert (wellformed Σ (length (av :: fix_env mfix Γ' ++ Γ')) fn = true) as wf_fn.
      { simpl in wf_recclos.
        unfold wf_fix, EAst.test_def in wf_recclos.
        assert (forallb (λ d, wellformed Σ (length mfix + length Γ') (EAst.dbody d)) mfix = true) as h_wf by ok.
        unfold Utils.cunfold_fix in e0.
        destruct (nth_error mfix idx) as [?|] eqn:heq; try easy.
        eapply All_Forall.nth_error_forallb in h_wf; last eassumption.
        destruct d as [? [] ?]; try easy.
        injection e0 as ?; subst.
        simpl in *. unfold is_true in h_wf.
        now rewrite length_app size_fix_env. }
      unshelve epose proof IHh_eval1 _ _ _ as (n'1 & tr1 & h_eval'1); tea.
      unshelve epose proof IHh_eval2 _ _ _ as (n'2 & tr2 & h_eval'2); tea.
      unshelve epose proof IHh_eval3 _ _ _ as (n'3 & tr3 & h_eval'3); tea.
      unfold Utils.cunfold_fix in e0.
      destruct (nth_error mfix idx) as [[? [] ?]|] eqn:heq; try easy.
      injection e0 as ?; subst.
      do 2 eexists.
      simpl in *.
      econstructor; first (now apply eval_step); ok.
      { unfold fix_body. now rewrite heq. }
      cbn in h_eval'3.
      simpl.
      apply eval_step.
      assumption_upto_prf.
      f_equal; ok.
      apply fix_env_make_rec_env.
    - do 2 eexists. simpl.
      rewrite (MRPrelude.uip_bool _ _ (extract_andb_right _) wf_Γ).
      constructor.
    - simpl in *. exfalso.
      now rewrite hCofix in wf_v.
    - simpl in *. exfalso.
      now rewrite hCofix in wf_v.
    - simpl in *. exfalso.
      apply eval_SI_wellformed_val in h_eval1; simpl in *; try easy.
      now rewrite hCofix in h_eval1.
    - apply eval_SI_wellformed_val in h_eval; simpl in *; try easy.
      now rewrite hCofix in h_eval.
    - assert (wellformed Σ 0 body = true) as wf_body.
      { eapply EInlining.lookup_env_wf; first easy.
        etransitivity; [exact isdecl|]. destruct decl; simpl in *; now subst. }  
      unshelve epose proof IHh_eval eq_refl _ _ as (n' & tr & h_eval'); tea.
      do 2 eexists.
      econstructor; ok.
    - assert (
        ∃ n' tr, 
        eval_fuel_many Σ (cvt_list Γ wf_Γ) args (cvt_list args' (extract_andb_right (extract_andb_left wf_v))) n' tr
      ) as (n' & tr & h); last first.
      { do 2 eexists.
        simpl. now constructor. }
      assert (forallb (wellformed Σ (length Γ)) args = true) as wf_args.
      { simpl in wf_e. now rewrite hBlocks in wf_e. }
      assert (forallb (wellformed_val Σ) args' = true) as wf_args' by ok.
      fold cvt_list.
      rewrite -> (MRPrelude.uip_bool _ _ _ wf_args').
      clear wf_e wf_v.
      clear l.
      induction a; simpl.
      { repeat econstructor. }
      inversion IHa.
      assert (wellformed_val Σ y = true) by ok.
      assert (forallb (wellformed_val Σ) l' = true) by ok.
      assert (wellformed Σ (length Γ) x = true) by ok.
      assert (forallb (wellformed Σ (length Γ)) l = true) by ok.
      unshelve epose proof H _ _ _ as (n' & tr & ?); tea.
      unshelve epose proof IHa0 X _ _ as (n'2 & tr2 & ?); tea.
      do 2 eexists.
      cbn. constructor.
      + apply eval_step. now rewrite -> (MRPrelude.uip_bool _ _ _ H0).
      + now rewrite -> (MRPrelude.uip_bool _ _ _ H1).
    - clear evih. destruct ev; [do 2 eexists; now constructor..|].
      exfalso. cbn in wf_e.
      now rewrite hPrimArray in wf_e.
    - simpl in *; exfalso.
      now rewrite hLazy in wf_v.
    - simpl in *; exfalso.
      now rewrite hLazy in wf_e.
    - simpl in *; exfalso.
      now rewrite hLazy in wf_e.
  Qed.
End exist_fuel.


Section nat_fuel.
  Context {efl : EEnvFlags}.
  Context {hBox : has_tBox = false}.
  Context {hCofix : has_tCoFix = false}.
  Context {hLazy : has_tLazy_Force = false}.
  Context {hPrimArray : has_primarray = false}.
  Context {hBlocks : cstr_as_blocks = true}.
  Context {hApp : has_tApp = true}.
  Context {hRel : has_tRel = true}.
  Context (Σ : EAst.global_declarations).
  Context (wf_Σ : wf_glob Σ).

  Notation cvt_list := (@convert_list efl hBox hCofix hLazy hPrimArray Σ).
  Notation cvt_vals := (@convert_vals efl hBox hCofix hLazy hPrimArray Σ).

  Ltac assumption_upto_prf :=
    match goal with
    | h: eval_env_fuel ?Σ ?e1 ?b (Val (cvt_vals ?res _)) _ _ |-
      eval_env_fuel ?Σ ?e2 ?b (Val (cvt_vals ?res _)) _ _ => replace e2 with e1; first eassumption
    end; cbn.

  (** The fuel counting evaluated applications, as in CertiRocq's [fuel_exp]
      resource: this is the cost model of MetaRocq's step-indexed evaluation. *)
  Definition app_fuel (t : EAst.term) : nat :=
    match t with
    | EAst.tApp _ _ => 1
    | _ => 0
    end.

  Context (trace : Type)
          (Hf : @LambdaBox_resource nat)
          (Ht : @LambdaBox_resource trace)
          (Heq0 : @algebra.zero _ _ (@HRes nat Hf) = 0)
          (Heq1 : ∀ t, @algebra.one_i _ _ (@HRes nat Hf) t = app_fuel t)
          (Heqadd : @algebra.plus _ _ (@HRes nat Hf) = Nat.add).

  Lemma step_to_fuel rho e r f t n :
    @eval_env_step trace Hf Ht Σ rho e r f t ->
    n = f + app_fuel e ->
    ∃ tr, @eval_env_fuel trace Hf Ht Σ rho e r n tr.
  Proof.
    intros h ->.
    eexists. pose proof (eval_step _ _ _ _ _ _ h) as h'.
    rewrite -> Heqadd, Heq1 in h'. exact h'.
  Qed.

  Ltac cost := cbn; rewrite -> ?Heq0, ?Heqadd; cbn; lia.

  Lemma evalSI_to_fuel_sem' Γ e v n wf_Γ wf_v :
    has_cstr_params = false ->
    wellformed Σ (length Γ) e = true ->
    EvalStepIndex.eval Σ Γ e v n ->
    ∃ tr, @eval_env_fuel trace Hf Ht Σ (cvt_list Γ wf_Γ) e (Val (cvt_vals v wf_v)) n tr.
  Proof.
    intros h_cstr wf_e h_eval.
    assert (is_true (negb has_cstr_params)) as h_cstr' by now rewrite h_cstr.
    revert wf_Γ wf_v wf_e.
    induction h_eval using eval_rect with (Pf := fun _ _ _ _ _ _ => True);
      [intros wf_Γ wf_v wf_e..| exact I | exact I].
    - ok.
    - ok.
    - eapply step_to_fuel; [|shelve].
      constructor.
      now erewrite nth_error_convert_list.
    - assert (wellformed Σ (length Γ) a = true) as wf_a by ok.
      assert (wellformed Σ (length Γ) f1 = true) as wf_f1 by ok.
      assert (wellformed_val Σ (vClos na b Γ') = true) as wf_clos.
      { eapply eval_SI_wellformed_val in h_eval1; tea. }
      assert (wellformed_val Σ a' = true) as wf_a'.
      { apply eval_SI_wellformed_val in h_eval2; tea. }
      assert (forallb (wellformed_val Σ) Γ' = true) as wf_Γ' by ok.
      assert (wellformed Σ (S (length Γ')) b = true) as wf_b by ok.
      assert (forallb (wellformed_val Σ) (a' :: Γ') = true) as wf_a'Γ' by ok.
      unshelve epose proof IHh_eval1 wf_Γ _ _ as (tr1 & h_eval'1); tea.
      unshelve epose proof IHh_eval2 wf_Γ _ _ as (tr2 & h_eval'2); tea.
      unshelve epose proof IHh_eval3 _ _ _ as (tr3 & h_eval'3); tea.
      eapply step_to_fuel; [|shelve].
      simpl. econstructor; [ok..|].
      fold cvt_list.
      assumption_upto_prf.
      now repeat f_equal.
    - eapply step_to_fuel; [|shelve].
      erewrite (MRPrelude.uip_bool _ _ wf_Γ).
      constructor.
    - assert (wellformed Σ (length Γ) b0 = true) as wf_b0 by ok.
      assert (wellformed_val Σ b0' = true) as wf_b0'.
      { eapply eval_SI_wellformed_val in h_eval1; tea. }
      assert (forallb (wellformed_val Σ) (b0' :: Γ) = true) as wf_b0'Γ by ok.
      assert (wellformed Σ (length (b0' :: Γ)) b1 = true) as wf_b1 by ok.
      unshelve epose proof IHh_eval1 wf_Γ _ _ as (tr1 & h_eval'1); tea.
      unshelve epose proof IHh_eval2 _ _ _ as (tr2 & h_eval'2); tea.
      eapply step_to_fuel; [|shelve].
      econstructor; ok.
      assumption_upto_prf.
      now repeat f_equal.
    - assert (wellformed Σ (length Γ) discr = true) as wf_discr by ok.
      assert (wellformed_val Σ (vConstruct ind c args) = true) as wf_vConstr.
      { now apply eval_SI_wellformed_val in h_eval1. }
      assert (forallb (wellformed_val Σ) args = true) as wf_args by ok.
      assert (forallb (wellformed_val Σ) (rev args ++ Γ) = true) as wf_revargsΓ.
      { now rewrite forallb_app MRList.forallb_rev. }
      assert (wellformed Σ (length (rev args ++ Γ)) (snd br) = true) as wf_snd_br.
      { simpl in wf_e. rewrite length_app length_rev e3.
        repeat apply extract_andb_right in wf_e.
        apply (All_Forall.nth_error_forallb e1 wf_e). }
      unshelve epose proof IHh_eval1 wf_Γ _ _ as (tr1 & h_eval'1); tea.
      unshelve epose proof IHh_eval2 _ _ _ as (tr2 & h_eval'2); tea.
      eapply step_to_fuel; [|shelve].
      econstructor; [ok..| |]; fold cvt_list.
      + rewrite length_convert_list.
        now apply nth_error_find_branch.
      + unshelve erewrite <-convert_list_rev, convert_list_app; [|ok..].
        clear h_eval'2; now rewrite forallb_app in wf_revargsΓ.
    - assert (wellformed_val Σ (vConstruct (Kernames.proj_ind p) 0 args) = true).
      { apply eval_SI_wellformed_val in h_eval; ok. }
      assert (wellformed Σ (length Γ) discr = true) as wf_discr by ok.
      unshelve epose proof IHh_eval _ _ _ as (tr & h_eval'); tea.
      eapply step_to_fuel; [|shelve].
      econstructor; ok.
      pose proof (MetaRocq.Erasure.StepIndex.Utils.constructor_isprop_pars_decl_params h_cstr wf_Σ e2) as hnpars.
      rewrite hnpars in e4. now apply nth_error_convert_list.
    - assert (wellformed_val Σ (vRecClos mfix idx Γ') = true) as wf_recclos.
      { apply eval_SI_wellformed_val in h_eval1; ok. }
      assert (forallb (wellformed_val Σ) Γ' = true) as wf_Γ' by ok.
      assert (wellformed_val Σ av = true) as wf_av.
      { apply eval_SI_wellformed_val in h_eval2; ok. }
      assert (forallb (wellformed_val Σ) (fix_env mfix Γ') = true).
      { rewrite fix_env_map All_Forall.forallb_map MRList.forallb_rev.
        rewrite forallb_forall.
        intros x ?%in_seq.
        enough ((wf_fix Σ (length Γ') mfix x)%bool = true) by ok.
        unfold wf_fix in *.
        enough (PeanoNat.Nat.ltb x (length mfix) = true) as -> by ok.
        now apply PeanoNat.Nat.ltb_lt. }
      assert (forallb (wellformed_val Σ) (av :: fix_env mfix Γ' ++ Γ') = true).
      { simpl. now rewrite forallb_app wf_av wf_Γ' Bool.andb_true_r Bool.andb_true_l. }
      assert (wellformed Σ (length Γ) f = true) as wf_f by ok.
      assert (wellformed Σ (length Γ) a = true) as wf_a by ok.
      assert (wellformed Σ (length (av :: fix_env mfix Γ' ++ Γ')) fn = true) as wf_fn.
      { simpl in wf_recclos.
        unfold wf_fix, EAst.test_def in wf_recclos.
        assert (forallb (λ d, wellformed Σ (length mfix + length Γ') (EAst.dbody d)) mfix = true) as h_wf by ok.
        unfold Utils.cunfold_fix in e0.
        destruct (nth_error mfix idx) as [?|] eqn:heq; try easy.
        eapply All_Forall.nth_error_forallb in h_wf; last eassumption.
        destruct d as [? [] ?]; try easy.
        injection e0 as ?; subst.
        simpl in *. unfold is_true in h_wf.
        now rewrite length_app size_fix_env. }
      unshelve epose proof IHh_eval1 _ _ _ as (tr1 & h_eval'1); tea.
      unshelve epose proof IHh_eval2 _ _ _ as (tr2 & h_eval'2); tea.
      unshelve epose proof IHh_eval3 _ _ _ as (tr3 & h_eval'3); tea.
      unfold Utils.cunfold_fix in e0.
      destruct (nth_error mfix idx) as [[? [] ?]|] eqn:heq; try easy.
      injection e0 as ?; subst.
      eapply step_to_fuel; [|shelve].
      simpl in *.
      econstructor; first eassumption; ok.
      { unfold fix_body. now rewrite heq. }
      cbn in h_eval'3.
      simpl.
      assumption_upto_prf.
      f_equal; ok.
      apply fix_env_make_rec_env.
    - eapply step_to_fuel; [|shelve].
      simpl.
      rewrite -> (MRPrelude.uip_bool _ _ (extract_andb_right _) wf_Γ).
      constructor.
    - simpl in *. exfalso.
      now rewrite hCofix in wf_v.
    - simpl in *. exfalso.
      now rewrite hCofix in wf_v.
    - simpl in *. exfalso.
      apply eval_SI_wellformed_val in h_eval1; simpl in *; try easy.
      now rewrite hCofix in h_eval1.
    - apply eval_SI_wellformed_val in h_eval; simpl in *; try easy.
      now rewrite hCofix in h_eval.
    - assert (wellformed Σ 0 body = true) as wf_body.
      { eapply EInlining.lookup_env_wf; first easy.
        etransitivity; [exact isdecl|]. destruct decl; simpl in *; now subst. }
      unshelve epose proof IHh_eval eq_refl _ _ as (tr & h_eval'); tea.
      eapply step_to_fuel; [|shelve].
      econstructor; ok.
    - enough (
        ∃ tr,
        eval_fuel_many Σ (cvt_list Γ wf_Γ) args (cvt_list args' (extract_andb_right (extract_andb_left wf_v))) (list_sum cs) tr
      ) as (tr & h).
      { eapply step_to_fuel; [|shelve].
        simpl. now constructor. }
      assert (forallb (wellformed Σ (length Γ)) args = true) as wf_args.
      { simpl in wf_e. now rewrite hBlocks in wf_e. }
      assert (forallb (wellformed_val Σ) args' = true) as wf_args' by ok.
      fold cvt_list.
      rewrite -> (MRPrelude.uip_bool _ _ _ wf_args').
      clear wf_e wf_v.
      clear l.
      induction a; simpl.
      { eexists. rewrite <- Heq0. constructor. }
      inversion IHa.
      assert (wellformed_val Σ y = true) by ok.
      assert (forallb (wellformed_val Σ) l' = true) by ok.
      assert (wellformed Σ (length Γ) x = true) by ok.
      assert (forallb (wellformed Σ (length Γ)) l = true) by ok.
      unshelve epose proof H _ _ _ as (tr & ?); tea.
      unshelve epose proof IHa0 X _ _ as (tr2 & ?); tea.
      eexists.
      cbn. replace (z + list_sum l'') with (algebra.plus z (list_sum l'')) by now rewrite -> Heqadd.
      constructor.
      + now rewrite -> (MRPrelude.uip_bool _ _ _ H0).
      + now rewrite -> (MRPrelude.uip_bool _ _ _ H1).
    - clear evih. destruct ev; [eapply step_to_fuel; [now constructor|]..|].
      1-3: cost.
      exfalso. cbn in wf_e.
      now rewrite hPrimArray in wf_e.
    - simpl in *; exfalso.
      now rewrite hLazy in wf_v.
    - simpl in *; exfalso.
      now rewrite hLazy in wf_e.
    - simpl in *; exfalso.
      now rewrite hLazy in wf_e.
    Unshelve. all: cost.
  Qed.
End nat_fuel.