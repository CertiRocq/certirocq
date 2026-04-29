(* Correspondence between the monadic ANF transformation (convert_anf)
   and the relational specification (anf_cvt_rel).
   ANF analog of LambdaBoxLocal_to_LambdaANF_corresp.v (CPS version). *)

Require Import Common.AstCommon Common.compM.
From Stdlib Require Import ZArith.ZArith Lists.List micromega.Lia Arith
     Ensembles Relations.Relation_Definitions.
Require compcert.lib.Maps compcert.lib.Coqlib.
Import ListNotations.

Require Import LambdaBoxLocal.expression LambdaBoxLocal.fuel_sem.

Require Import term cps_show eval ctx logical_relations
        List_util algebra alpha_conv functions Ensembles_util
        LambdaBoxLocal_to_LambdaANF LambdaBoxLocal_to_LambdaANF_util
        LambdaBoxLocal_to_LambdaANF_anf_util
        LambdaANF.tactics identifiers
        term_util rename state.
Require Import closure_conversion_corresp.

Require Import ExtLib.Data.Monads.OptionMonad ExtLib.Structures.Monads.

Require Import MetaRocq.Utils.bytestring.

Import Monad.MonadNotation.

Open Scope monad_scope.

Section Corresp.

  Context (prim_map : M.t Pipeline_utils.primitive)
          (func_tag default_tag : positive).


  (** * var_map correctness *)

  Definition var_map_correct (vm : var_map) (vn : list var) : Prop :=
    forall i, get_var_name vm (N.of_nat i) = nth_error vn i.

  Lemma Npos_succ_pos p : Npos (N.succ_pos p) = N.succ p.
  Proof. destruct p; reflexivity. Qed.

  Lemma var_map_correct_nil :
    var_map_correct new_var_map [].
  Proof.
    unfold var_map_correct, new_var_map, get_var_name. intros i.
    simpl. destruct i; reflexivity.
  Qed.

  Lemma var_map_correct_cons vm vn x :
    var_map_correct vm vn ->
    var_map_correct (add_var_name vm x) (x :: vn).
  Proof.
    unfold var_map_correct, add_var_name, get_var_name.
    intros Hvm i. destruct i as [ | i'].
    - (* i = 0 *)
      destruct vm as [m p]. simpl.
      destruct p; simpl; rewrite Maps.PTree.gss; reflexivity.
    - (* i = S i' *)
      specialize (Hvm i').
      destruct vm as [m p].
      change (nth_error (x :: vn) (S i')) with (nth_error vn i').
      rewrite Npos_succ_pos, Nnat.Nat2N.inj_succ.
      replace (N.succ p - N.succ (N.of_nat i'))%N with (p - N.of_nat i')%N by lia.
      destruct (p - N.of_nat i')%N eqn:Hdiff.
      + exact Hvm.
      + rewrite Maps.PTree.gso; [ exact Hvm | ].
        intros Heq. subst p0.
        assert (Hle : (Npos (N.succ_pos p) <= p)%N) by lia.
        rewrite Npos_succ_pos in Hle. lia.
  Qed.

  Lemma var_map_correct_fold_right vm vn vars :
    var_map_correct vm vn ->
    var_map_correct (List.fold_right (fun v vm' => add_var_name vm' v) vm vars) (vars ++ vn).
  Proof.
    induction vars; intros Hvm; simpl.
    - exact Hvm.
    - apply var_map_correct_cons. apply IHvars. exact Hvm.
  Qed.


  (** * Fresh name specs (reused from CPS corresp) *)

  Lemma get_named_spec :
    forall (A : Type) (S : Ensemble var) (n : name),
      {{fun (_ : unit) (s : comp_data * A) => fresh S (next_var (fst s))}} get_named n
      {{fun (_ : unit) (s : comp_data * A) (x : var) (s' : comp_data * A) =>
          In var S x /\
          In var (Range (next_var (fst s)) (next_var (fst s'))) x /\
          (next_var (fst s) < next_var (fst s'))%positive /\ fresh (S \\ [set x]) (next_var (fst s'))}}.
  Proof.
    intros.
    eapply pre_post_mp_l.
    eapply bind_triple. now eapply get_triple.
    intros [[] w1] [[] w2].
    eapply pre_post_mp_l.
    eapply bind_triple. now eapply put_triple.
    intros x [r3 w3].
    eapply return_triple.
    intros ? [r4 w4] H2. inv H2. intros [H1 H2]. inv H1; inv H2. intros.
    split. eapply H. reflexivity. split. unfold Range, Ensembles.In. simpl. zify. lia.
    simpl. split. zify; lia.
    intros z Hin. constructor. eapply H; eauto. simpl. zify. lia.
    intros Hc. inv Hc. zify; lia.
  Qed.

  Lemma get_named_str_lst_spec S strs :
    {{ fun _ (s : comp_data * unit) => identifiers.fresh S (next_var (fst s)) }}
      get_named_str_lst strs
      {{ fun (r: unit) s xs s' =>
           NoDup xs /\ List.length xs = List.length strs /\
           FromList xs \subset S /\
           FromList xs \subset Range (next_var (fst s)) (next_var (fst s')) /\
           (next_var (fst s) <= next_var (fst s'))%positive /\
           identifiers.fresh (S \\ FromList xs) (next_var (fst s')) }}.
  Proof.
    unfold get_named_str_lst. revert S; induction strs; intros S.
    - simpl. eapply return_triple.
      intros. repeat normalize_sets. split; eauto.
      sets. now constructor. split; eauto.
      split. now sets. split. sets. split. reflexivity. eassumption.
    - simpl. eapply bind_triple. eapply get_named_str_fresh.
      intros x w.
      eapply bind_triple. eapply frame_rule. eapply frame_rule. eapply frame_rule. eapply IHstrs.
      intros xs w'. eapply return_triple. intros. destructAll.
      repeat normalize_sets. split; [ | split; [ | split; [ | split; [ | split ]]]].
      + constructor; eauto. intros Hc. eapply H4 in Hc. inv Hc. now eauto.
      + simpl. congruence.
      + eapply Union_Included. sets. eapply Included_trans. eapply H4. sets.
      + eapply Union_Included. eapply Singleton_Included.
        eapply Range_Subset; [ | | eassumption ]. reflexivity. zify. lia.
        eapply Included_trans. eassumption. eapply Range_Subset. zify; lia. reflexivity.
      + zify; lia.
      + rewrite <- Setminus_Union. eassumption.
  Qed.

  Lemma get_named_lst_spec S strs :
    {{ fun _ (s : comp_data * unit) => identifiers.fresh S (next_var (fst s)) }}
      get_named_lst strs
      {{ fun (r: unit) s xs s' =>
           NoDup xs /\ List.length xs = List.length strs /\
           FromList xs \subset S /\
           FromList xs \subset Range (next_var (fst s)) (next_var (fst s')) /\
           (next_var (fst s) <= next_var (fst s'))%positive /\
           identifiers.fresh (S \\ FromList xs) (next_var (fst s')) }}.
  Proof.
    unfold get_named_str_lst. revert S; induction strs; intros S.
    - simpl. eapply return_triple.
      intros. repeat normalize_sets. split; eauto.
      sets. now constructor. split; eauto.
      split. now sets. split. sets. split. reflexivity. eassumption.
    - simpl. eapply bind_triple. eapply get_named_spec.
      intros x w.
      eapply bind_triple. eapply frame_rule. eapply frame_rule. eapply frame_rule. eapply IHstrs.
      intros xs w'. eapply return_triple. intros. destructAll.
      repeat normalize_sets. split; [ | split; [ | split; [ | split; [ | split ]]]].
      + constructor; eauto. intros Hc. eapply H4 in Hc. inv Hc. now eauto.
      + simpl. congruence.
      + eapply Union_Included. sets. eapply Included_trans. eapply H4. sets.
      + eapply Union_Included. eapply Singleton_Included.
        eapply Range_Subset; [ | | eassumption ]. reflexivity. zify. lia.
        eapply Included_trans. eassumption. eapply Range_Subset. zify; lia. reflexivity.
      + zify; lia.
      + rewrite <- Setminus_Union. eassumption.
  Qed.


  Ltac inv_setminus :=
    match goal with
    | [ H : In _ (?S \\ ?Q) _ |- _ ] => inv H; try inv_setminus
    end.


  (** * Correspondence definitions *)

  Definition anf_cvt_exp_corresp :=
    forall e S vn tgm vm
      (Hwf : exp_wf (N.of_nat (List.length vn)) e)
      (Hvm : var_map_correct vm vn),
    {{ fun _ s => fresh S (next_var (fst s)) }}
      convert_anf prim_map func_tag default_tag tgm e vm
    {{ fun _ s (p : var * exp_ctx) s' =>
         let (r, C) := p in
         exists S',
           anf_cvt_rel func_tag default_tag S e vn tgm S' C r /\
           fresh S' (next_var (fst s')) }}.

  Definition anf_cvt_exps_corresp :=
    forall es S vn tgm vm
      (Hwf : exps_wf (N.of_nat (List.length vn)) es)
      (Hvm : var_map_correct vm vn),
    {{ fun _ s => fresh S (next_var (fst s)) }}
      convert_anf_exps prim_map func_tag default_tag tgm es vm
    {{ fun _ s (p : list var * exp_ctx) s' =>
         let (xs, C) := p in
         exists S',
           anf_cvt_rel_exps func_tag default_tag S es vn tgm S' C xs /\
           fresh S' (next_var (fst s')) }}.

  Definition anf_cvt_efnlst_corresp :=
    forall efns S vn fnames i tgm vm
      (Hwf : efnlst_wf (N.of_nat (List.length vn)) efns)
      (Hlen : List.length fnames = efnlength efns)
      (Hvm : var_map_correct vm vn),
    {{ fun _ s => fresh S (next_var (fst s)) }}
      convert_anf_efnlst prim_map func_tag default_tag tgm efns fnames i vm
    {{ fun _ s (p : var * fundefs) s' =>
         let (fi, B) := p in
         exists S',
           anf_cvt_rel_efnlst func_tag default_tag S efns vn fnames tgm S' B /\
           (forall f, nth_error fnames (N.to_nat i) = Some f -> fi = f) /\
           fresh S' (next_var (fst s')) }}.

  Definition anf_cvt_branches_corresp :=
    forall bs S vn y tgm vm
      (Hwf : branches_wf (N.of_nat (List.length vn)) bs)
      (Hvm : var_map_correct vm vn),
    {{ fun _ s => fresh S (next_var (fst s)) }}
      convert_anf_branches prim_map func_tag default_tag tgm bs y vm
    {{ fun _ s (pats : list (ctor_tag * exp)) s' =>
         exists S',
           anf_cvt_rel_branches func_tag default_tag S bs vn y tgm S' pats /\
           fresh S' (next_var (fst s')) }}.


  (** * add_fix_names spec *)

  Lemma add_fix_names_spec :
    forall fnlst S vm vn
      (Hvm : var_map_correct vm vn),
    {{ fun _ (s : comp_data * unit) => fresh S (next_var (fst s)) }}
      add_fix_names fnlst vm
    {{ fun _ s (p : list var * var_map) s' =>
         let (names, vm') := p in
         NoDup names /\
         List.length names = efnlength fnlst /\
         FromList names \subset S /\
         var_map_correct vm' (List.rev names ++ vn) /\
         fresh (S \\ FromList names) (next_var (fst s')) }}.
  Proof.
    induction fnlst; intros S vm vn Hvm.
    - (* eflnil *)
      simpl. eapply return_triple.
      intros _ w Hf. repeat normalize_sets.
      split. constructor.
      split. reflexivity.
      split. sets.
      split. simpl. exact Hvm.
      eassumption.
    - (* eflcons *)
      simpl.
      eapply bind_triple. eapply pre_post_copy.
      eapply get_named_spec.
      intros f w. simpl.
      eapply pre_curry_l; intros Hfresh.
      eapply pre_curry_l; intros Hf.

      eapply bind_triple.
      eapply frame_rule. eapply frame_rule.
      eapply IHfnlst. eapply var_map_correct_cons. exact Hvm.

      intros [names vm'] w'. simpl.
      eapply pre_curry_l; intros Hlt.
      eapply pre_curry_l; intros Hfr.

      eapply return_triple. intros _ w'' Hpost. destructAll.
      repeat normalize_sets.
      split; [ | split; [ | split; [ | split ]]].
      + constructor; eauto. intros Hc. eapply H1 in Hc. inv Hc. now eauto.
      + simpl. congruence.
      + eapply Union_Included. sets. eapply Included_trans. eapply H1. sets.
      + simpl rev. rewrite <- app_assoc. simpl.
        exact H2.
      + rewrite <- Setminus_Union. eassumption.
  Qed.


  (** * proj_ctx spec *)

  Lemma proj_ctx_spec names n scrut vm ct S vn
    (Hvm : var_map_correct vm vn) :
    {{ fun _ (s : comp_data * unit) => fresh S (next_var (fst s)) }}
      proj_ctx names n scrut vm ct
    {{ fun _ s (p : exp_ctx * var_map) s' =>
         let (ctx_p, vm') := p in
         exists vars,
           NoDup vars /\
           List.length vars = n /\
           FromList vars \subset S /\
           ctx_p = ctx_bind_proj ct scrut vars (List.length vars) /\
           var_map_correct vm' (vars ++ vn) /\
           fresh (S \\ FromList vars) (next_var (fst s')) }}.
  Proof.
    unfold proj_ctx.
    eapply bind_triple. eapply get_named_lst_spec.
    intros vars w'. eapply return_triple.
    intros _ w Hvars. destructAll.
    exists vars.
    split; [ eassumption | ].
    split; [ rewrite H0; apply names_lst_length | ].
    split; [ eassumption | ].
    split; [ reflexivity | ].
    split; [ apply var_map_correct_fold_right; exact Hvm | ].
    eassumption.
  Qed.


  (** * Main correspondence proof *)

  Lemma anf_cvt_sound :
    anf_cvt_exp_corresp /\
    anf_cvt_exps_corresp /\
    anf_cvt_efnlst_corresp /\
    anf_cvt_branches_corresp.
  Proof.
    eapply exp_ind_alt_2; intros; try inv Hwf.

    - (* Var_e *)
      assert (Hget : get_var_name vm n = nth_error vn (N.to_nat n)).
      { specialize (Hvm (N.to_nat n)). rewrite Nnat.N2Nat.id in Hvm. exact Hvm. }
      cbn -[get_var_name]. rewrite Hget.
      destruct (nth_error vn (N.to_nat n)) eqn:Hnth.
      + eapply return_triple. intros _ w Hf.
        eexists. split.
        * econstructor. eassumption.
        * eassumption.
      + exfalso. apply nth_error_None in Hnth. lia.

    - (* Lam_e *)
      simpl.
      eapply bind_triple.
      eapply get_named_spec.
      intros x w. simpl.
      eapply pre_curry_l; intros Hx.

      eapply bind_triple.
      eapply pre_strenghtening. 2: eapply get_named_spec.
      intros ? ? [? [? ?]]. eassumption.
      intros f w2. simpl.
      eapply pre_curry_l; intros Hf.

      eapply bind_triple.
      eapply pre_strenghtening.
      2: { eapply H.
           2: { eapply var_map_correct_cons. eassumption. }
           simpl List.length.
           replace (N.of_nat (Datatypes.S (Datatypes.length vn)))
             with (1 + N.of_nat (Datatypes.length vn))%N by lia.
           eassumption. }
      intros ? ? [? [? ?]]. eassumption.

      intros [r C] w3. simpl. eapply return_triple.
      intros ? ? Hpost. destructAll.

      eexists. split; [ | eassumption ].
      econstructor; eauto.

    - (* App_e *)
      simpl.
      eapply bind_triple. eapply pre_post_copy.
      eapply H. eassumption. eassumption.
      intros [x1 C1] w1. simpl.
      eapply pre_curry_l; intros Hfresh.
      eapply pre_existential. intros S1.
      eapply pre_curry_l; intros Hrel1.

      eapply bind_triple. eapply pre_post_copy.
      eapply H0. eassumption. eassumption.
      intros [x2 C2] w2. simpl.
      eapply pre_curry_l; intros Hfresh2.
      eapply pre_existential. intros S2.
      eapply pre_curry_l; intros Hrel2.

      eapply bind_triple.
      eapply get_named_spec.
      intros r w3. simpl.
      eapply pre_curry_l; intros Hr.

      eapply return_triple.
      intros _ w Hpost. destructAll.

      eexists. split; [ | eassumption ].
      econstructor; eauto.

    - (* Con_e *)
      simpl.
      eapply bind_triple. eapply pre_post_copy.
      eapply get_named_spec.
      intros x w. simpl.
      eapply pre_curry_l; intros Hfresh.
      eapply pre_curry_l; intros Hx.

      eapply bind_triple.
      eapply pre_strenghtening.
      2: { eapply H; eassumption. }
      intros ? ? [? [? ?]]. eassumption.

      intros [ys C] w2. simpl.
      eapply pre_existential. intros S2.
      eapply pre_curry_l; intros Hrel.

      eapply return_triple.
      intros _ w3 Hfr.

      eexists. split; [ | eassumption ].
      econstructor; eauto.

    - (* Match_e *)
      simpl.
      eapply bind_triple.
      eapply get_named_str_fresh.
      intros f w. simpl.
      eapply pre_curry_l; intros Hf.

      eapply bind_triple.
      eapply pre_strenghtening. 2: eapply get_named_str_fresh.
      intros ? ? [? [? ?]]. eassumption.
      intros y w1. simpl.
      eapply pre_curry_l; intros Hy.

      eapply bind_triple.
      eapply pre_strenghtening. 2: { eapply H; eassumption. }
      intros ? ? [? [? ?]]. eassumption.
      intros [x1 C1] w2. simpl.
      eapply pre_existential. intros S2.
      eapply pre_curry_l; intros Hrel1.

      eapply bind_triple. eapply pre_post_copy.
      eapply H0. eassumption. eassumption.
      intros pats w3. simpl.
      eapply pre_curry_l; intros Hfr3.
      eapply pre_existential. intros S3.
      eapply pre_curry_l; intros Hrel2.

      eapply bind_triple.
      eapply get_named_spec.
      intros r w4. simpl.
      eapply pre_curry_l; intros Hr_in.

      eapply return_triple.
      intros ? ? Hpost. destructAll.

      eexists. split; [ | eassumption ].
      econstructor; eauto.

    - (* Let_e *)
      simpl.
      eapply bind_triple. eapply pre_post_copy.
      eapply H. eassumption. eassumption.
      intros [x C1] w1. simpl.
      eapply pre_curry_l; intros Hfresh.
      eapply pre_existential. intros S1.
      eapply pre_curry_l; intros Hrel1.

      eapply bind_triple.
      eapply H0.
      2: { eapply var_map_correct_cons. eassumption. }
      simpl List.length.
      replace (N.of_nat (Datatypes.S (Datatypes.length vn)))
        with (1 + N.of_nat (Datatypes.length vn))%N by lia.
      eassumption.

      intros [r C2] w2. simpl. eapply return_triple.
      intros. destructAll.

      eexists. split.
      + econstructor; eauto.
      + eassumption.

    - (* Fix_e *)
      simpl.
      eapply bind_triple. eapply pre_post_copy.
      eapply add_fix_names_spec. eassumption.
      intros [names vm'] w1. simpl.
      eapply pre_curry_l; intros Hfresh.
      eapply pre_curry_l; intros Hnd.
      eapply pre_curry_l; intros Hlen'.
      eapply pre_curry_l; intros Hsub.
      eapply pre_curry_l; intros Hvm'.

      eapply bind_triple.
      eapply H.
      3: eassumption.
      2: eassumption.
      rewrite length_app, length_rev.
      rewrite Nnat.Nat2N.inj_add.
      rewrite Hlen', efnlength_efnlst_length. eassumption.

      intros [fi defs] w2. simpl.
      eapply return_triple.
      intros. destructAll.

      destruct (nth_error names (N.to_nat n)) eqn:Hnth.
      2:{ exfalso. apply nth_error_None in Hnth.
          rewrite Hlen' in Hnth.
          match goal with
          | H : (_ < efnlst_length ?es)%N |- _ =>
            pose proof (efnlength_efnlst_length es)
          end. lia. }

      eexists. split; [ | eassumption ].
      assert (fi = v) as -> by eauto.
      econstructor; eassumption.

    - (* Prf_e *)
      simpl.
      eapply bind_triple. eapply pre_post_copy.
      eapply get_named_str_fresh.
      intros x w. simpl.
      eapply pre_curry_l; intros Hfresh.
      eapply pre_curry_l; intros Hx.

      eapply return_triple.
      intros. destructAll.

      eexists. split.
      + econstructor; eauto.
      + eassumption.

    - (* Prim_val_e *)
      simpl.
      eapply bind_triple. eapply pre_post_copy.
      eapply get_named_str_fresh.
      intros x w. simpl.
      eapply pre_curry_l; intros Hfresh.
      eapply pre_curry_l; intros Hx.

      eapply return_triple.
      intros. destructAll.

      eexists. split.
      + econstructor; eauto.
      + eassumption.

    - (* enil — Prim_e auto-closed by inv Hwf *)
      simpl.
      eapply return_triple. intros _ w Hf.
      eexists. split.
      + constructor.
      + eassumption.

    - (* econs *)
      simpl.
      eapply bind_triple. eapply pre_post_copy.
      eapply H. eassumption. eassumption.
      intros [y C1] w1. simpl.
      eapply pre_curry_l; intros Hfresh.
      eapply pre_existential. intros S1.
      eapply pre_curry_l; intros Hrel1.

      eapply bind_triple.
      eapply H0. eassumption. eassumption.

      intros [ys C2] w2. simpl.
      eapply return_triple.
      intros. destructAll.

      eexists. split.
      + econstructor; eauto.
      + eassumption.

    - (* eflnil *)
      destruct fnames; [ | simpl in Hlen; congruence ].
      simpl. eapply return_triple. intros _ w Hf.
      eexists. split.
      + constructor.
      + split.
        * intros f Hf'. destruct (N.to_nat i); discriminate.
        * exact Hf.

    - (* eflcons — Lambda case *)
      split.
      2:{ intros. inv Hwf. exfalso; eauto. }
      intros ? ? ? H ? H0.
      intros S vn fnames i tgm vm Hwf Hlen Hvm.

      (* Lambda case: e = Lam_e n' e' *)
      subst. inv Hwf.
      match goal with H : exp_wf _ (Lam_e _ _) |- _ => inv H end.
      destruct fnames as [ | f_name rest]. simpl in Hlen; congruence.
      simpl in Hlen.

      simpl.
      eapply bind_triple. eapply pre_post_copy.
      eapply get_named_spec.
      intros x w. simpl.
      eapply pre_curry_l; intros Hfresh.
      eapply pre_curry_l; intros Hx.

      eapply bind_triple.
      eapply pre_strenghtening.
      2: { eapply H.
           2: { eapply var_map_correct_cons. eassumption. }
           simpl List.length.
           replace (N.of_nat (Datatypes.S (Datatypes.length vn)))
             with (1 + N.of_nat (Datatypes.length vn))%N by lia.
           eassumption. }
      intros ? ? [? [? ?]]. eassumption.

      intros [r C] w2. simpl.
      eapply pre_existential. intros S2.
      eapply pre_curry_l; intros Hrel1.

      eapply bind_triple.
      eapply H0.
      3: eassumption.
      2: lia.
      eassumption.

      intros [fi defs'] w3. simpl.
      eapply return_triple.
      intros ? ? Hpost. destructAll.

      eexists. split.
      + econstructor; eauto.
      + split.
        * intros f' Hf'.
          destruct i.
          -- simpl in Hf'. inv Hf'. reflexivity.
          -- match goal with
             | Htail : forall f, nth_error _ (N.to_nat _) = Some f -> _ = f |- _ =>
               eapply Htail
             end.
             change (N.to_nat (N.pos p)) with (Pos.to_nat p) in Hf'.
             destruct (Pos2Nat.is_succ p) as [n0 Hpn].
             rewrite Hpn in Hf'. simpl in Hf'.
             replace (N.to_nat (N.pos p - 1)) with n0; [ exact Hf' | lia ].
        * eassumption.

    - (* brnil_e *)
      simpl.
      eapply return_triple. intros _ w Hf.
      eexists. split.
      + constructor.
      + eassumption.

    - (* brcons_e *)
      destruct p as [n_br lnames].
      simpl.
      eapply bind_triple. eapply pre_post_copy.
      eapply H0. eassumption. eassumption.
      intros pats' w1. simpl.
      eapply pre_curry_l; intros Hfresh.
      eapply pre_existential. intros S2.
      eapply pre_curry_l; intros Hrel1.

      eapply bind_triple.
      eapply proj_ctx_spec. eassumption.
      intros [Cproj vm'] w2. simpl.
      eapply pre_existential. intros vars.
      eapply pre_curry_l; intros Hnd.
      eapply pre_curry_l; intros Hlen_vars.
      eapply pre_curry_l; intros Hsub_vars.
      eapply pre_curry_l; intros Hcproj.
      eapply pre_curry_l; intros Hvm'.

      eapply bind_triple.
      eapply H.
      2: eassumption.
      simpl in *. rewrite length_app. rewrite Hlen_vars.
      rewrite Nnat.Nat2N.inj_add. rewrite Nnat.N2Nat.id. eassumption.

      intros [r C] w3. simpl.
      eapply return_triple.
      intros. destructAll.

      eexists. split.
      + subst. econstructor; [ | | | | | | eassumption ]; eauto.
      + eassumption.
  Qed.


  (** * Utility lemmas for existence proofs *)

  Lemma set_lists_Forall2 {A} xs (vs : list A) rho rho' :
    set_lists xs vs rho = Some rho' ->
    NoDup xs ->
    Forall2 (fun x v => M.get x rho' = Some v) xs vs.
  Proof.
    revert vs rho rho'; induction xs; intros ys rho rho' Hset Hnd;
      destruct ys; simpl in *; try congruence.
    - constructor.
    - destruct (set_lists xs ys rho) eqn:Hset'; try congruence.
      inv Hset.
      constructor.
      rewrite M.gss. reflexivity.
      eapply Forall2_monotonic_strong.
      2:{ eapply IHxs; eauto. inv Hnd. eassumption. }
      intros. rewrite M.gso. eassumption.
      intros Heq; subst. inv Hnd; eauto.
  Qed.

  Fixpoint pos_seq (start : var) (n : nat) : list positive :=
    match n with
    | 0%nat => []
    | S n => start :: (pos_seq (start + 1)%positive n)
    end.

  Lemma pos_seq_len start n :
    List.length (pos_seq start n) = n.
  Proof.
    revert start. induction n; intros start.
    - reflexivity.
    - simpl. rewrite IHn. reflexivity.
  Qed.

  Lemma pos_seq_In start n x :
    List.In x (pos_seq start n) ->
    (start <= x <= Pos.of_nat (Pos.to_nat start + n)%nat)%positive.
  Proof.
    revert start. induction n; intros start Hin.
    - inv Hin.
    - inv Hin.
      + lia.
      + eapply IHn in H. split. lia. lia.
  Qed.

  Lemma pos_seq_NoDup start n :
    NoDup (pos_seq start n).
  Proof.
    revert start; induction n; intros start.
    - now constructor.
    - simpl. constructor; eauto.
      intros Hc. eapply pos_seq_In in Hc. lia.
  Qed.


  (** * Existence of ANF conversion *)

  Lemma anf_rel_exists e xs tgm m :
    exp_wf (N.of_nat (List.length xs)) e ->
    exists C r S',
      anf_cvt_rel func_tag default_tag (fun x => (m <= x)%positive) e xs tgm S' C r.
  Proof.
    intros Hwf.
    destruct anf_cvt_sound as (Hexp & _).

    set (comp_d := pack_data m
                             1%positive 1%positive 1%positive
                             (M.empty _) (M.empty _) (M.empty _) (M.empty _) []).

    set (S := fun x => (m <= x)%positive).

    (* We need var_map_correct for some vm and xs.
       We don't have a specific vm; we need to construct one.
       But anf_rel_exists is used at the top level with xs being a specific list.
       We can build a var_map from xs using fold_right add_var_name. *)
    set (vm := List.fold_right (fun v vm' => add_var_name vm' v) new_var_map xs).

    assert (Hvm : var_map_correct vm xs).
    { unfold vm. rewrite <- (app_nil_r xs) at 2.
      apply var_map_correct_fold_right. apply var_map_correct_nil. }

    edestruct (runState (convert_anf prim_map func_tag default_tag tgm e vm) tt (comp_d, tt)) eqn:Hcvt.

    assert (Hf : fresh S m).
    { unfold S, fresh, In. lia. }

    specialize (Hexp e S xs tgm vm Hwf Hvm tt (comp_d, tt) Hf).

    rewrite Hcvt in Hexp. destruct e0 as [ | [r0 C0]]. contradiction.
    simpl in Hexp. destructAll.
    do 3 eexists. eassumption.
  Qed.


  Lemma anf_fix_rel_exists m efns tgm fnames names fnames' :
    efnlst_wf (N.of_nat (List.length (List.rev fnames ++ names))) efns ->
    Disjoint _ (fun x => (m <= x)%positive) (FromList fnames :|: FromList names) ->
    List.length fnames' = efnlength efns ->
    exists B S3,
      anf_fix_rel func_tag default_tag tgm fnames names (fun x => (m <= x)%positive) fnames' efns B S3.
  Proof.
    revert m tgm fnames names fnames'.
    induction efns; intros m tgm fnames names fnames'; intros Hwf Hdis Hlen.

    - do 2 eexists.
      destruct fnames'; simpl in *; try congruence.
      econstructor.

    - destruct fnames'. simpl in Hlen. congruence.

      simpl in Hlen. injection Hlen as Hlen.

      (* Save efnlst_wf for tail before inv destroys Hwf *)
      assert (Hwf_efns : efnlst_wf (N.of_nat (Datatypes.length (List.rev fnames ++ names))) efns)
        by (inv Hwf; assumption).
      inv Hwf.

      set (x := (1 + m)%positive).
      set (next_id := (1 + x)%positive).

      set (comp_d := pack_data next_id
                               1%positive 1%positive 1%positive
                               (M.empty _) (M.empty _) (M.empty _) (M.empty _) []).

      set (S := fun z => (next_id <= z)%positive).

      assert (Hf : fresh S next_id).
      { unfold S, next_id, fresh, In. lia. }

      (* e must be a lambda *)
      destruct e; match goal with H : isLambda _ |- _ => simpl in H; try contradiction end.

      destruct anf_cvt_sound as (Hexp & _).

      set (vn := (List.rev fnames ++ names)%list).

      set (vm := List.fold_right (fun v vm' => add_var_name vm' v) new_var_map vn).

      assert (Hvm : var_map_correct vm vn).
      { unfold vm. rewrite <- (app_nil_r vn) at 2.
        apply var_map_correct_fold_right. apply var_map_correct_nil. }

      match goal with H : exp_wf _ (Lam_e _ _) |- _ => inv H end.
      assert (Hwf' : exp_wf (N.of_nat (Datatypes.length (x :: vn))) e).
      { match goal with
        | H : exp_wf ?n e |- exp_wf ?m e =>
          replace m with n; [exact H | ]
        end.
        unfold vn. cbn [length]. rewrite Nnat.Nat2N.inj_succ. lia. }

      destruct (runState (convert_anf prim_map func_tag default_tag tgm e (add_var_name vm x)) tt (comp_d, tt)) as [cvt_res cvt_st] eqn:Hcvt.

      unfold anf_cvt_exp_corresp, triple in Hexp.
      specialize (Hexp e S (x :: vn) tgm
                       (add_var_name vm x) Hwf'
                       (var_map_correct_cons vm vn x Hvm)
                       tt (comp_d, tt) Hf).
      rewrite Hcvt in Hexp.
      destruct cvt_res as [? | [r_cvt C_cvt]]; try contradiction.
      destruct cvt_st as [c_st u_st]. simpl in Hexp. destructAll.

      edestruct IHefns with (m := (next_var c_st)) (fnames' := fnames') (fnames := fnames) (names := names) (tgm := tgm).
      exact Hwf_efns.
      { eapply Disjoint_Included_l; [ | eassumption ].
        intros z Hz. unfold In in *.
        enough (m <= next_var c_st)%positive by lia.
        assert (Hsub : Included _ x0 S) by (eapply anf_cvt_exp_subset; eassumption).
        assert (Htmp : x0 (next_var c_st)) by (apply H0; lia).
        specialize (Hsub _ Htmp). unfold S, In, next_id, x in Hsub. lia. }
      eassumption. destructAll.

      do 2 eexists. econstructor; [ | | | | eassumption | eassumption ].
      + eassumption.
      + unfold In, x. lia.
      + unfold S. intros z Hz. constructor.
        unfold In, next_id, x in *. lia.
        intros Hc. inv Hc. unfold In, next_id, x in *. lia.
      + unfold S. intros z Hz. eapply H0 in Hz. eassumption.
  Qed.


  Lemma NoDup_env_consistent (vn : list var) (rho : list value) :
    NoDup vn -> env_consistent vn rho.
  Proof.
    intros Hnd i j x Hi Hj.
    assert (Heq : i = j).
    { clear rho. revert j vn Hnd Hi Hj. induction i; intros j vn Hnd Hi Hj.
      - destruct vn; simpl in *; [ discriminate | ]. inv Hi.
        destruct j; [ reflexivity | ].
        simpl in Hj. inv Hnd. exfalso. apply H1. eapply nth_error_In. eassumption.
      - destruct vn; simpl in *; [ discriminate | ].
        destruct j; simpl in *.
        + inv Hnd. inv Hj. exfalso. apply H1. eapply nth_error_In. eassumption.
        + inv Hnd. f_equal. eapply IHi; eassumption. }
    subst. reflexivity.
  Qed.

  Lemma anf_val_rel_exists v tgm :
    well_formed_val v ->
    exists v', anf_val_rel func_tag default_tag tgm v v'.
  Proof.
    induction v using value_ind'; intros Hwf; inv Hwf.

    - (* Con_v *)
      induction vs.
      + eexists. constructor. constructor. reflexivity.
      + inv H. inv H1.
        edestruct IHvs; eauto. edestruct H3; eauto.
        inv H.
        eexists. constructor. econstructor. eassumption. eassumption. reflexivity.

    - (* Clos_v *)

      set (x := 1%positive).
      set (f := 2%positive).
      set (names := pos_seq 3%positive (List.length vs)).

      assert (Hvs : exists vs', Forall2 (anf_val_rel func_tag default_tag tgm) vs vs').
      { revert H H2. clear. intros. induction vs.
        + eexists. constructor.
        + inv H2. inv H.
          edestruct IHvs; eauto. edestruct H2; eauto. }

      destruct Hvs as [vs' Hvs].

      set (s := @set_lists_length3 val).
      edestruct s with (rho := M.empty val) (vs := vs') (xs := names) as [ rho ].
      eapply Forall2_length in Hvs. rewrite <- Hvs. eapply pos_seq_len.

      assert (Henv: anf_env_rel' (anf_val_rel func_tag default_tag tgm) names vs rho).
      { eapply set_lists_Forall2 in H0; eauto. 2:{ eapply pos_seq_NoDup. }
        unfold names in *. revert Hvs H0. clear. generalize (pos_seq 3%positive (Datatypes.length vs)) as ns.
        revert vs' rho.
        induction vs; intros vs' rho ns Hvs Hset; destruct vs'; inv Hvs; destruct ns; inv Hset.
        now constructor.
        constructor.
        now eauto.
        eapply IHvs; eauto. }

      specialize (H4 (Clos_v [] nAnon e)).

      assert (Hwfe : exp_wf (N.of_nat (Datatypes.length (x :: names))) e).
      { unfold well_formed_in_env in *. simpl in *.
        unfold names. rewrite pos_seq_len. eassumption. }

      set (next_id := (Pos.of_nat (Pos.to_nat 3%positive + (List.length vs))%nat + 1)%positive).

      edestruct (anf_rel_exists e (x :: names) tgm next_id) as [C1 [r1 [S2 Hrel]]].
      eassumption.

      eexists. eapply anf_rel_Clos with (f := f); [ eassumption | | | | | eassumption ].
      + eapply NoDup_env_consistent. eapply pos_seq_NoDup.
      + constructor. intros z Hz.
        inversion Hz as [z' HL HR]; subst; clear Hz.
        unfold In, next_id in HR. unfold In in HL.
        destruct HL as [HL | HL].
        * inv H1; zify; lia.
        * unfold In in H1. destruct H1 as [H1 | H1].
          -- inv H3; zify; lia.
          -- unfold FromList, In, names in H3. eapply pos_seq_In in H3. zify; lia.
      + intros Hc. unfold x, f, names, In in Hc.
        inv Hc.
        -- inv H1.
        -- unfold In, FromList in H1. cbn beta in H1. eapply pos_seq_In in H1. lia.
      + intros Hc. unfold f, names, FromList, In in Hc.
        eapply pos_seq_In in Hc. lia.

    - (* ClosFix_v *)

      set (names := pos_seq 1%positive (List.length vs)).
      set (fnames := pos_seq (Pos.of_nat (List.length vs + 2)) (N.to_nat (efnlst_length fnl))).
      set (next_id := (Pos.of_nat (N.to_nat (efnlst_length fnl) + (List.length vs) + 3)%nat)%positive).

      assert (Hvs : exists vs', Forall2 (anf_val_rel func_tag default_tag tgm) vs vs').
      { revert H H3. clear. intros. induction vs.
        + eexists. constructor.
        + inv H3. inv H.
          edestruct IHvs; eauto. edestruct H3; eauto. }

      destruct Hvs as [vs' Hvs].

      set (s := @set_lists_length3 val).
      edestruct s with (rho := M.empty val) (vs := vs') (xs := names) as [ rho ].
      eapply Forall2_length in Hvs. rewrite <- Hvs. eapply pos_seq_len.

      assert (Henv: anf_env_rel' (anf_val_rel func_tag default_tag tgm) names vs rho).
      { eapply set_lists_Forall2 in H0; eauto. 2:{ eapply pos_seq_NoDup. }
        unfold names in *. revert Hvs H0. clear. generalize (pos_seq 1%positive (Datatypes.length vs)) as ns.
        revert vs' rho.
        induction vs; intros vs' rho ns Hvs Hset; destruct vs'; inv Hvs; destruct ns; inv Hset.
        now constructor.
        constructor.
        now eauto.
        eapply IHvs; eauto. }


      assert (Hlen : efnlst_length fnl = N.of_nat (List.length fnames)).
      { unfold fnames. rewrite pos_seq_len. lia. }

      assert (Hwf : efnlst_wf (N.of_nat (Datatypes.length (List.rev fnames ++ names))) fnl).
      { revert H5. rewrite length_app, Nnat.Nat2N.inj_add.
        rewrite length_rev, Hlen.
        unfold names. rewrite pos_seq_len.
        generalize (N.of_nat (Datatypes.length fnames) + N.of_nat (Datatypes.length vs)).
        clear. induction fnl; intros m Hall.
        - constructor.
        - inv Hall. destructAll. constructor; eauto. }

      edestruct anf_fix_rel_exists with (fnames := fnames) (m := next_id) (tgm := tgm) (fnames' := fnames).

      eassumption.

      { eapply Union_Disjoint_r.
        constructor. intros z Hc. inv Hc. eapply pos_seq_In in H2.
        unfold In, next_id in *. inv H2. lia.
        constructor. intros z Hc. inv Hc. eapply pos_seq_In in H2.
        unfold In, next_id in *. lia. }

      
      unfold fnames. rewrite pos_seq_len. rewrite <- efnlength_efnlst_length. lia.
      
      destructAll.


      edestruct (nth_error fnames (N.to_nat n)) eqn:Hnth.
      2:{ eapply nth_error_Some in Hnth. contradiction.
          unfold fnames. rewrite pos_seq_len. lia. }
      
      eexists. econstructor; [ eassumption  | | | | | | eassumption ].
      + eapply NoDup_env_consistent. eapply pos_seq_NoDup. 

      + eapply pos_seq_NoDup.

      + unfold next_id. constructor. intros z Hc.
        inv Hc. unfold In in *. inv H2.
        eapply pos_seq_In in H7. lia.
        eapply pos_seq_In in H7. lia.

      + constructor. intros z Hc.
        inv Hc.  eapply pos_seq_In in H2.
        eapply pos_seq_In in H6. lia.

      + eassumption.
  Qed.

End Corresp.
