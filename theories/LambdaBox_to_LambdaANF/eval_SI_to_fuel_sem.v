From Stdlib Require Import Utf8.
From Stdlib Require Import List.
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

Section Convert.
  Context {efl : EEnvFlags}.
  Context {hBox : has_tBox = false}.
  Context {hCofix : has_tCoFix = false}.
  Context {hLazy : has_tLazy_Force = false}.
  Context {hPrim : has_tPrim = {| 
      has_primint := false;
      has_primfloat := false;
      has_primstring := false;
      has_primarray := false;
    |}
  }.
  Context {hBlocks : cstr_as_blocks = true}.
  Context {hApp : has_tApp = true}.
  Context (Σ : EAst.global_declarations).
  Context (wf_Σ : wf_glob Σ).
  Context (f : Kernames.inductive -> nat -> common.dcon).


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
  | vPrim p => λ wf_v, False_rect _ _
  | vLazy t Γ => λ wf_v, False_rect _ _
  end
.
Proof.
  - simpl in *; congruence.
  - simpl in *. now destruct has_tCoFix. 
  - simpl in *. apply extract_andb_left in wf_v.
    unfold Utils.has_prim in wf_v.
    destruct has_tPrim; injection hPrim as ? ? ? ?.
    destruct p as [[] ?]; simpl in wf_v.
    + now destruct has_primint.
    + now destruct has_primfloat.
    + now destruct has_primstring.
    + now destruct has_primarray.
  - simpl in *. now destruct has_tLazy_Force. 
Defined.

Definition convert_list := convert_list' convert_vals.

Lemma length_convert_list l e :
  length (convert_list l e) = length l.
Proof.
  now induction l; simpl.
Qed.

Print find_branch.
Print nth_error.
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

Search andb eq true.

Lemma convert_list_app l1 l2 h1 h2 h3 :
  convert_list l1 h1 ++ convert_list l2 h2 = 
    convert_list (l1 ++ l2) h3.
Proof.
  induction l1; cbn; repeat f_equal.
  - apply MRUtils.uip_bool.
  - apply MRUtils.uip_bool.
  - now erewrite IHl1.
Qed.

Lemma convert_list_rev l h h_rev :
  convert_list (rev l) h = rev (convert_list l h_rev).
Proof.
  induction l; cbn; repeat f_equal.
  unshelve erewrite <-convert_list_app, IHl.
  - simpl in h. now rewrite forallb_app in h.
  - simpl in h. now rewrite forallb_app in h.
  - simpl in h. now rewrite forallb_app, MRList.forallb_rev in h.
  - do 3 f_equal.
    + apply MRUtils.uip_bool.
    + cbn. do 2 f_equal. apply MRUtils.uip_bool.
Qed.


Lemma nth_error_convert_list l h n v h' :
  nth_error l n = Some v ->
  nth_error (convert_list l h) n = Some (convert_vals v h').
Proof.
  induction l in n, h |- *; destruct n; cbn; try easy.
  intros [=<-].
  repeat f_equal.
  apply MRUtils.uip_bool.
Qed.

Lemma no_prim p : has_prim p = false.
Proof.
  destruct has_tPrim; injection hPrim as ? ? ? ?; subst.
  now destruct p as [[] ?]; cbn.
Qed.
Print make_rec_env.
Lemma make_rec_env_map mfix Γ :
  make_rec_env mfix Γ = map (ClosFix_v Γ mfix) (rev (seq 0 (length mfix))) ++ Γ.
Proof.
  unfold make_rec_env.
  generalize (length mfix) as n.
  induction n.
  - reflexivity.
  - now rewrite IHn, seq_S, rev_unit.
Qed.


Lemma convert_list_cong l1 l2 h1 h2 :
  l1 = l2 ->
  convert_list l1 h1 = convert_list l2 h2.
Proof.
  intros ->.
  f_equal.
  apply MRUtils.uip_bool.
Qed.


Lemma evalSI_to_fuel_sem (trace : Type) (Hf Ht : LambdaBox_resource) dcon Γ e v n wf_Γ wf_v :
  has_cstr_params = false ->
  wellformed Σ (length Γ) e = true ->
  EvalStepIndex.eval Σ Γ e v n ->
  ∃ n' tr, @eval_env_step trace Hf Ht Σ dcon (convert_list Γ wf_Γ) e (Val (convert_vals v wf_v)) n' tr.
Proof.
  intros h_cstr wf_e h_eval.
  assert (is_true (negb has_cstr_params)) as h_cstr' by now rewrite h_cstr.
  induction h_eval.
  - simpl in *; congruence.
  - simpl in *; congruence.
  - do 2 eexists.
    constructor.
    induction Γ in n, wf_Γ, e |- *; destruct n; simpl.
    + discriminate.
    + discriminate.
    + injection e as ?; subst.
      do 2 f_equal. simpl in *.
      apply MRUtils.uip_bool.
    + simpl. now apply IHΓ.
  - assert (wellformed_val Σ a' = true) as wf_a'.
    { now apply eval_SI_wellformed_val in h_eval2; simpl in *. }
    assert (forallb (wellformed_val Σ) Γ' = true) as wf_Γ'.
    { apply eval_SI_wellformed_val in h_eval1; simpl in *; 
        try easy.
      now apply extract_andb_left, extract_andb_right in h_eval1. }
    assert (wellformed Σ (S (length Γ')) b = true) as wf_b.
    { apply eval_SI_wellformed_val in h_eval1; simpl in *; try easy.
      now apply extract_andb_right in h_eval1. }
    unshelve epose proof IHh_eval1 wf_Γ _ _ as (n'1 & tr1 & h_eval'1).
    { eapply eval_SI_wellformed_val; try assumption.
      - apply wf_Γ.
      - simpl in wf_e.
        now eapply extract_andb_right, extract_andb_left.
      - eassumption. }
    { simpl in wf_e.
      now eapply extract_andb_right, extract_andb_left. }
    unshelve epose proof IHh_eval2 wf_Γ _ _ as (n'2 & tr2 & h_eval'2).
    { eapply eval_SI_wellformed_val; try assumption.
      - apply wf_Γ.
      - simpl in wf_e.
        now eapply extract_andb_right.
      - eassumption. }
    { simpl in wf_e. now eapply extract_andb_right. }
    unshelve epose proof IHh_eval3 _ _ _ as (n'3 & tr3 & h_eval'3).
    { simpl. now rewrite wf_a', wf_Γ'. }
    { now apply eval_SI_wellformed_val in h_eval3; simpl in *. }
    { now simpl. }
    do 2 eexists.
    simpl.
    econstructor.
    + apply eval_step. eassumption. 
    + apply eval_step. eassumption. 
    + fold convert_vals convert_list.
      apply eval_step.
      match goal with
      | h: eval_env_step Σ dcon ?e1 b (Val (convert_vals res _)) _ _ |-
        eval_env_step Σ dcon ?e2 b (Val (convert_vals res _)) _ _ => replace e2 with e1; first eassumption
      end.
      cbn.
      repeat f_equal.
      * apply MRUtils.uip_bool.
      * apply MRUtils.uip_bool.
  - do 2 eexists. 
    erewrite (MRUtils.uip_bool _ _ _).
    constructor.
  - assert (wellformed_val Σ b0' = true) as wf_b0'.
    { eapply eval_SI_wellformed_val in h_eval1; try assumption.
      now simpl in wf_e. }
    unshelve epose proof IHh_eval1 wf_Γ _ _ as (n'1 & tr1 & h_eval'1).
    { assumption. }
    { now simpl in wf_e. }
    unshelve epose proof IHh_eval2 _ _ _ as (n'2 & tr2 & h_eval'2); try now simpl in *.
    do 2 eexists.
    econstructor.
    + now apply eval_step.
    + cbn in h_eval'2. 
      rewrite (MRUtils.uip_bool _ _ _ wf_b0'), (MRUtils.uip_bool _ _ _ wf_Γ) in h_eval'2.
      now apply eval_step.
  - assert (wellformed Σ (length Γ) discr = true) as wf_discr.
    { now simpl in *. }
    assert (forallb (wellformed_val Σ) args = true) as wf_args.
    { apply eval_SI_wellformed_val in h_eval1; simpl in *; try easy.
      now apply extract_andb_left in h_eval1. }
    assert (forallb (wellformed_val Σ) (rev args ++ Γ) = true) as ?.
    { now rewrite forallb_app, MRList.forallb_rev. }
    unshelve epose proof IHh_eval1 wf_Γ _ _ as (n'1 & tr1 & h_eval'1).
    { now apply eval_SI_wellformed_val in h_eval1. }
    { assumption. }
    unshelve epose proof IHh_eval2 _ _ _ as (n'2 & tr2 & h_eval'2).
    { assumption. }
    { assumption. }
    { simpl in wf_e. rewrite length_app, length_rev, e3.
      repeat apply extract_andb_right in wf_e.
      apply (All_Forall.nth_error_forallb e1 wf_e). }
    do 2 eexists.
    econstructor.
    + now apply eval_step.
    + reflexivity.
    + fold convert_vals.
      rewrite length_convert_list.
      now apply nth_error_find_branch.
    + fold convert_vals convert_list.
      unshelve erewrite <-convert_list_rev, convert_list_app.
      { clear h_eval'2; now rewrite forallb_app in H. }
      { assumption. }
      now apply eval_step.
  - assert (wellformed_val Σ (vConstruct (Kernames.proj_ind p) 0 args) = true).
    { now apply eval_SI_wellformed_val in h_eval; simpl in *. }  
    unshelve epose proof IHh_eval _ _ _ as (n' & tr & h_eval').
    { assumption. }  
    { assumption. }  
    { now simpl in *. }  
    do 2 eexists.
    econstructor.
    + now apply eval_step.
    + fold convert_vals convert_list.
      now apply nth_error_convert_list.
  - assert (wellformed_val Σ (vRecClos mfix idx Γ') = true) as wf_recclos. 
    { now apply eval_SI_wellformed_val in h_eval1; simpl in *. }
    assert (forallb (wellformed_val Σ) Γ' = true) as wf_Γ' .
    { now simpl in wf_recclos. }
    assert (wellformed_val Σ av = true) as wf_av.
    { now apply eval_SI_wellformed_val in h_eval2; simpl in *. }
    assert (forallb (wellformed_val Σ) (fix_env mfix Γ') = true).
    { rewrite fix_env_map, All_Forall.forallb_map, MRList.forallb_rev.
      rewrite forallb_forall.
      intros x ?%in_seq.
      simpl in *. 
      assert ((wf_fix Σ (length Γ') mfix x)%bool = true) as ->.
      { unfold wf_fix in *.
        now assert (PeanoNat.Nat.ltb x (length mfix) = true) as -> 
            by now apply PeanoNat.Nat.ltb_lt. }
      easy.  }
    assert (forallb (wellformed_val Σ) (av :: fix_env mfix Γ' ++ Γ') = true).
    { simpl. now rewrite forallb_app, wf_av, wf_Γ', Bool.andb_true_r, Bool.andb_true_l. }
    unshelve epose proof IHh_eval1 _ _ _ as (n'1 & tr1 & h_eval'1).
    { assumption. }
    { assumption. }
    { now simpl in *. }
    unshelve epose proof IHh_eval2 _ _ _ as (n'2 & tr2 & h_eval'2).
    { assumption. }
    { assumption. }
    { now simpl in *. }
    unshelve epose proof IHh_eval3 _ _ _ as (n'3 & tr3 & h_eval'3).
    { assumption. }
    { assumption. }
    { simpl in wf_recclos.
      unfold wf_fix, EAst.test_def in wf_recclos.
      assert (forallb (λ d, wellformed Σ (length mfix + length Γ') (EAst.dbody d)) mfix = true) as h_wf.
      { clear h_eval'1. now apply extract_andb_right in wf_recclos. }
      unfold Utils.cunfold_fix in e0.
      destruct (nth_error mfix idx) as [?|] eqn:heq; try easy.
      eapply All_Forall.nth_error_forallb in h_wf; last eassumption.
      destruct d as [? [] ?]; try easy.
      injection e0 as ?; subst.
      simpl in *. unfold is_true in h_wf.
      now rewrite length_app, size_fix_env. }
    unfold Utils.cunfold_fix in e0.
    destruct (nth_error mfix idx) as [[? [] ?]|] eqn:heq; try easy.
    injection e0 as ?; subst.
    do 2 eexists.
    simpl in *.
    econstructor; first now apply eval_step.
    + unfold fix_body. now rewrite heq.
    + reflexivity.
    + now apply eval_step.
    + cbn in h_eval'3.
      simpl.
      apply eval_step.
      match goal with
      | h: eval_env_step Σ dcon ?e1 fn (Val (convert_vals res _)) _ _ |-
        eval_env_step Σ dcon ?e2 fn (Val (convert_vals res _)) _ _ => replace e2 with e1; first eassumption
      end.
      f_equal.
      { f_equal. apply MRUtils.uip_bool. }
      unshelve erewrite <-convert_list_app.
      { assumption. }
      { assumption. }
      rewrite make_rec_env_map.
      fold convert_list.
      do 2 f_equal; last apply MRUtils.uip_bool.
      pose proof eq_sym (fix_env_map mfix Γ') as h.
      destruct h.
      clear.
      induction (length mfix); first reflexivity.
      rewrite seq_S at 2.
      rewrite rev_app_distr.
      simpl.
      assert (forallb (wellformed_val Σ) (map (λ n0 : nat, vRecClos mfix n0 Γ') (rev (seq 0 n))) = true) as h.
      { rewrite seq_S, rev_app_distr in H. now simpl in H. }
      unshelve erewrite <-IHn; first assumption.
      assert (wellformed_val Σ (vRecClos mfix n Γ') = true) as h'.
      { now rewrite seq_S, rev_app_distr in H; simpl in *. }
      match goal with 
      | |- _ = ?a :: _ => 
          replace a with (convert_vals (vRecClos mfix n Γ') h'); last first
      end.
      { simpl in *. fold convert_list. repeat f_equal. apply MRUtils.uip_bool. }
      change (convert_vals (vRecClos mfix n Γ') h' :: convert_list (map (λ n0 : nat, vRecClos mfix n0 Γ') (rev (seq 0 n))) h)
      with ([convert_vals (vRecClos mfix n Γ') h'] ++ convert_list (map (λ n0 : nat, vRecClos mfix n0 Γ') (rev (seq 0 n))) h).
      assert (forallb (wellformed_val Σ) (map (λ n, vRecClos mfix n Γ') [n]) = true) as h''.
      { now simpl in *. }
      replace [convert_vals (vRecClos mfix n Γ') h'] 
      with (convert_list (map (λ n, vRecClos mfix n Γ') [n]) h''); last first.
      { cbn. do 3 f_equal. apply MRUtils.uip_bool. }
      unshelve erewrite convert_list_app.
      { now rewrite forallb_app, h, h''. }
      apply convert_list_cong.
      rewrite <-map_app.
      now rewrite <-(rev_app_distr _ [n]), <-(rev_app_distr [0]), <-seq_S.
  - do 2 eexists. simpl.
    rewrite (MRUtils.uip_bool _ _ (extract_andb_right _) wf_Γ).
    constructor.
  - simpl in *. exfalso.
    now rewrite hCofix in wf_v.
  - simpl in *. exfalso.
    now rewrite hCofix in wf_v.
  - simpl in *. exfalso.
    apply eval_SI_wellformed_val in h_eval1; simpl in *; try easy.
    now rewrite hCofix in h_eval1.
  - apply eval_SI_wellformed_val in h_eval1; simpl in *; try easy.
    now rewrite hCofix in h_eval1.
  - unshelve epose proof IHh_eval _ _ _ as (n' & tr & h_eval').
    { reflexivity. }
    { assumption. }
    { eapply EInlining.lookup_env_wf; first easy.
      rewrite isdecl. destruct decl; simpl in *; now subst. }  
    do 2 eexists.
    econstructor; try easy.
    now apply eval_step.
  - assert (
      ∃ n' tr, 
      eval_fuel_many Σ dcon (convert_list Γ wf_Γ) args (convert_list' convert_vals args' (extract_andb_right (extract_andb_left wf_v))) n' tr
    ) as (n' & tr & h); last first.
    { do 2 eexists.
      simpl. now constructor. }
    assert (forallb (wellformed Σ (length Γ)) args = true) as wf_args.
    { simpl in wf_e. now rewrite hBlocks in wf_e. }
    assert (forallb (wellformed_val Σ) args' = true) as wf_args'.
    { now simpl in wf_v. }
    fold convert_list.
    rewrite (MRUtils.uip_bool _ _ _ wf_args').
    clear wf_e wf_v.
    clear l.
    induction a; simpl.
    { repeat econstructor. }
    inversion IHa.
    assert (wellformed_val Σ y = true).
    { now simpl in wf_args'. }
    assert (forallb (wellformed_val Σ) l' = true).
    { now simpl in wf_args'. }
    assert (wellformed Σ (length Γ) x = true).
    { now simpl in wf_args. }
    assert (forallb (wellformed Σ (length Γ)) l = true).
    { now simpl in wf_args. }
    unshelve epose proof H _ _ _ as (n' & tr & ?).
    { assumption. }
    { assumption. }
    { assumption. }
    unshelve epose proof IHa0 X _ _ as (n'2 & tr2 & ?).
    { assumption. }
    { assumption. }
    do 2 eexists.
    cbn. constructor.
    + apply eval_step. now rewrite (MRUtils.uip_bool _ _ _ H0).
    + now rewrite (MRUtils.uip_bool _ _ _ H1).
  - simpl in wf_e. exfalso.
    now rewrite no_prim in wf_e.
  - simpl in *; exfalso.
    now rewrite hLazy in wf_v.
  - simpl in *; exfalso.
    now rewrite hLazy in wf_e.
Qed.
End Convert.
