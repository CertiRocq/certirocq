(* Correspondence between the monadic ANF transformation (convert_anf)
   and the relational specification (anf_convert_rel).
   Proves that convert_anf satisfies the anf_convert_rel spec. *)

(** Stdlib *)
From Stdlib Require Import ZArith.ZArith NArith.NArith Lists.List micromega.Lia Arith
     Ensembles Relations.Relation_Definitions.

(** MetaRocq *)
From MetaRocq.Erasure Require Import EAst EGlobalEnv EWellformed.
From MetaRocq.Common Require Import BasicAst Kernames.
From MetaRocq.Utils Require Import bytestring.

(** CompCert *)
From compcert Require Import lib.Maps lib.Coqlib.

(** ExtLib *)
From ExtLib Require Import Structures.Monads Data.Monads.OptionMonad.

(** CertiRocq *)
From CertiRocq.Common Require Import AstCommon compM.
From CertiRocq Require Import Pipeline_utils.
From CertiRocq.LambdaANF Require Import
  cps cps_util ctx List_util Ensembles_util
  identifiers state set_util tactics.

From CertiRocq.LambdaBox_to_LambdaANF Require Import common ANF.

Import ListNotations.
Import Monad.MonadNotation.

Open Scope monad_scope.
Open Scope bs_scope.


Section Corresp.

  Context
    (* LambdaANF tags *)
    (func_tag default_tag : positive)
    (* primitive map *)
    (prim_map : M.t primitive)
    (* constructor tag map *)
    (tgm : conId_map)
    (* primitive list *)
    (prims : list (primitive * positive))
    (* global constant map *)
    (cmap : const_map).


  (** * var_map correctness *)

  Definition var_map_correct (vm : var_map) (vn : list var) : Prop :=
    forall i, get_var_name vm (N.of_nat i) = nth_error vn i.

  Lemma var_map_correct_nil :
    var_map_correct new_var_map [].
  Proof.
    unfold var_map_correct, new_var_map, get_var_name. intros i.
    simpl. destruct i; reflexivity.
  Qed.

  Lemma get_var_name_add_0 vm x :
    get_var_name (add_var_name vm x) 0%N = Some x.
  Proof.
    unfold add_var_name, get_var_name. destruct vm as [m p].
    rewrite N.sub_0_r. rewrite M.gss. reflexivity.
  Qed.

  Lemma get_var_name_add_succ vm x n :
    get_var_name (add_var_name vm x) (N.succ n) = get_var_name vm n.
  Proof.
    unfold add_var_name, get_var_name. destruct vm as [m p].
    replace (Npos (N.succ_pos p) - N.succ n)%N with (p - n)%N.
    2:{ change (Npos (N.succ_pos p)) with (N.pos (N.succ_pos p)).
        rewrite N.succ_pos_spec. lia. }
    destruct (p - n)%N eqn:Hsub.
    - reflexivity.
    - rewrite M.gso; [ reflexivity | ].
      intros Heq. subst.
      exfalso.
      assert (N.pos (N.succ_pos p) = N.succ p) by apply N.succ_pos_spec.
      lia.
  Qed.

  Lemma var_map_correct_cons vm vn x :
    var_map_correct vm vn ->
    var_map_correct (add_var_name vm x) (x :: vn).
  Proof.
    unfold var_map_correct.
    intros Hvm i. destruct i as [ | i'].
    - simpl. exact (get_var_name_add_0 vm x).
    - simpl. rewrite <- (Hvm i').
      assert (Heq : N.pos (Pos.of_succ_nat i') = N.succ (N.of_nat i')).
      { rewrite <- Nat2N.inj_succ. reflexivity. }
      rewrite Heq.
      exact (get_var_name_add_succ vm x (N.of_nat i')).
  Qed.


  (** * Correspondence specifications *)

  Let convert_anf := convert_anf func_tag default_tag prim_map tgm prims cmap.

  Definition anf_convert_exp_corresp :=
    forall e vn vm S,
      var_map_correct vm vn ->
      {{ fun _ s => identifiers.fresh S (next_var (fst s)) }}
        convert_anf e vm
      {{ fun _ s p s' =>
           let '(r, C) := p in
           exists S',
             ANF.anf_convert_rel func_tag default_tag tgm cmap S e vn S' C r /\
             identifiers.fresh S' (next_var (fst s')) }}.

  (* When e = tLambda na e1, gives the triple for e1 directly.
     Needed because convert_anf_mfix destructures the lambda body. *)
  Definition mfix_body_corresp (e : EAst.term) :=
    forall na e1, e = EAst.tLambda na e1 ->
    forall vn vm S,
      var_map_correct vm vn ->
      {{ fun _ s => identifiers.fresh S (next_var (fst s)) }}
        convert_anf e1 vm
      {{ fun _ s p s' =>
           let '(r, C) := p in
           exists S',
             ANF.anf_convert_rel func_tag default_tag tgm cmap S e1 vn S' C r /\
             identifiers.fresh S' (next_var (fst s')) }}.

  Definition anf_convert_args_corresp :=
    forall args vn vm S,
      var_map_correct vm vn ->
      {{ fun _ s => identifiers.fresh S (next_var (fst s)) }}
        convert_anf_args convert_anf args vm
      {{ fun _ s p s' =>
           let '(xs, C) := p in
           exists S',
             ANF.anf_convert_rel_args func_tag default_tag tgm cmap S args vn S' C xs /\
             identifiers.fresh S' (next_var (fst s')) }}.

  Definition anf_convert_mfix_corresp :=
    forall mfix fnames idx vn vm S,
      var_map_correct vm vn ->
      List.length fnames = List.length mfix ->
      {{ fun _ s => identifiers.fresh S (next_var (fst s)) }}
        convert_anf_mfix func_tag convert_anf mfix fnames idx vm
      {{ fun _ s p s' =>
           let '(fi, B) := p in
           exists S',
             ANF.anf_convert_rel_mfix func_tag default_tag tgm cmap S mfix vn fnames S' B /\
             (forall f, nth_error fnames idx = Some f -> fi = f) /\
             identifiers.fresh S' (next_var (fst s')) }}.

  Definition anf_convert_branches_corresp :=
    forall ind brs n scrut vn vm S,
      var_map_correct vm vn ->
      {{ fun _ s => identifiers.fresh S (next_var (fst s)) }}
        convert_anf_branches default_tag tgm convert_anf ind brs n scrut vm
      {{ fun _ s pats s' =>
           exists S',
             ANF.anf_convert_rel_branches func_tag default_tag tgm cmap S ind brs n vn scrut S' pats /\
             identifiers.fresh S' (next_var (fst s')) }}.


  (** * Main correspondence theorem *)

  (** Spec for get_named / get_named_str *)
  (** Spec for add_fix_names *)
  Lemma add_fix_names_spec :
    forall mfix S vm vn
      (Hvm : var_map_correct vm vn),
    {{ fun _ (s : comp_data * unit) => identifiers.fresh S (next_var (fst s)) }}
      add_fix_names mfix vm
    {{ fun _ s (p : list var * var_map) s' =>
         let (names, vm') := p in
         NoDup names /\
         List.length names = List.length mfix /\
         FromList names \subset S /\
         var_map_correct vm' (List.rev names ++ vn) /\
         identifiers.fresh (S \\ FromList names) (next_var (fst s')) }}.
  Proof.
    induction mfix; intros S vm vn Hvm.
    - simpl. eapply return_triple.
      intros _ w Hf. repeat normalize_sets.
      split; [ constructor | split; [ reflexivity | split; [ sets | split; [ exact Hvm | eassumption ]]]].
    - simpl.
      eapply bind_triple.
      eapply pre_post_copy. eapply get_named_spec'.
      intros f w. simpl.
      eapply pre_curry_l; intros Hfresh.
      eapply pre_curry_l; intros Hf.
      eapply bind_triple.
      eapply frame_rule. eapply frame_rule.
      eapply IHmfix. eapply var_map_correct_cons. exact Hvm.
      intros [names vm'] w'. simpl.
      eapply pre_curry_l; intros Hlt.
      eapply pre_curry_l; intros Hfr.
      eapply return_triple. intros _ w'' Hpost. destructAll.
      repeat normalize_sets.
      split; [ | split; [ | split; [ | split ]]].
      + constructor; eauto. intros Hc. eapply H1 in Hc. inv Hc. now eauto.
      + simpl. congruence.
      + eapply Union_Included. sets. eapply Included_trans. eapply H1. sets.
      + simpl rev. rewrite <- app_assoc. simpl. exact H2.
      + rewrite <- Setminus_Union. eassumption.
  Qed.

  Lemma get_named_spec' S0 na :
    {{ fun (_ : unit) (s : comp_data * unit) => identifiers.fresh S0 (next_var (fst s)) }}
      @get_named unit na
    {{ fun (_ : unit) (s : comp_data * unit) (x : var) (s' : comp_data * unit) =>
         x \in S0 /\
         (next_var (fst s) < next_var (fst s'))%positive /\
         identifiers.fresh (S0 \\ [set x]) (next_var (fst s')) }}.
  Proof.
    unfold get_named.
    eapply pre_post_mp_l.
    eapply bind_triple. now eapply get_triple.
    intros [[] w1] [[] w2].
    eapply pre_post_mp_l. simpl.
    eapply bind_triple. now eapply put_triple.
    intros x [r3 w3].
    eapply return_triple.
    intros ? [r4 w4] H2. inv H2. intros [H1 H2]. inv H1; inv H2. intros Hfresh.
    simpl in *.
    split. eapply Hfresh. reflexivity.
    split. zify; lia.
    intros z Hin. constructor. eapply Hfresh; eauto. zify. lia.
    intros Hc. inversion Hc. subst. zify; lia.
  Qed.

  Lemma get_named_str_spec' S0 str :
    {{ fun (_ : unit) (s : comp_data * unit) => identifiers.fresh S0 (next_var (fst s)) }}
      @get_named_str unit str
    {{ fun (_ : unit) (s : comp_data * unit) (x : var) (s' : comp_data * unit) =>
         x \in S0 /\
         (next_var (fst s) < next_var (fst s'))%positive /\
         identifiers.fresh (S0 \\ [set x]) (next_var (fst s')) }}.
  Proof.
    unfold get_named_str.
    eapply pre_post_mp_l.
    eapply bind_triple. now eapply get_triple.
    intros [[] w1] [[] w2].
    eapply pre_post_mp_l. simpl.
    eapply bind_triple. now eapply put_triple.
    intros x [r3 w3].
    eapply return_triple.
    intros ? [r4 w4] H2. inv H2. intros [H1 H2]. inv H1; inv H2. intros Hfresh.
    simpl in *.
    split. eapply Hfresh. reflexivity.
    split. zify; lia.
    intros z Hin. constructor. eapply Hfresh; eauto. zify. lia.
    intros Hc. inversion Hc. subst. zify; lia.
  Qed.

  Lemma var_map_correct_fold_right vm vn vars :
    var_map_correct vm vn ->
    var_map_correct (List.fold_right (fun v vm' => add_var_name vm' v) vm vars) (vars ++ vn).
  Proof.
    induction vars; intros Hvm; simpl.
    - exact Hvm.
    - apply var_map_correct_cons. apply IHvars. exact Hvm.
  Qed.

  Lemma names_lst_length ns m :
    List.length (names_lst_len ns m) = m.
  Proof.
    revert m; induction ns; intros m; destruct m; simpl; try reflexivity.
    - rewrite repeat_length. reflexivity.
    - rewrite IHns. reflexivity.
  Qed.

  Lemma get_named_lst_spec S strs :
    {{ fun _ (s : comp_data * unit) => identifiers.fresh S (next_var (fst s)) }}
      get_named_lst strs
    {{ fun (r: unit) s xs s' =>
         NoDup xs /\ List.length xs = List.length strs /\
         FromList xs \subset S /\
         identifiers.fresh (S \\ FromList xs) (next_var (fst s')) }}.
  Proof.
    induction strs; simpl.
    - unfold get_named_lst. simpl. eapply return_triple.
      intros _ w Hf. repeat normalize_sets.
      split; [ constructor | split; [ reflexivity | split; [ sets | eassumption ]]].
    - unfold get_named_lst. simpl. unfold mapM. simpl.
      eapply bind_triple. eapply get_named_spec'.
      intros x w. eapply pre_curry_l. intros Hx.
      eapply pre_strenghtening. { intros ? ? [_ Hf]. exact Hf. }
      eapply bind_triple.
      change (mapM get_named strs) with (get_named_lst strs).
      eapply IHstrs.
      intros xs w'. eapply return_triple.
      intros _ s [Hnd [Hlen [Hsub Hfresh]]].
      repeat normalize_sets.
      split; [ | split; [ | split ]].
      + constructor; eauto. intros Hc. eapply Hsub in Hc. inv Hc. now eauto.
      + simpl. congruence.
      + eapply Union_Included. sets. eapply Included_trans. eapply Hsub. sets.
      + rewrite <- Setminus_Union. eassumption.
  Qed.

  Lemma proj_ctx_spec names n scrut vm ct S vn
    (Hvm : var_map_correct vm vn) :
    {{ fun _ (s : comp_data * unit) => identifiers.fresh S (next_var (fst s)) }}
      proj_ctx names n scrut vm ct
    {{ fun _ s (p : exp_ctx * var_map) s' =>
         let (ctx_p, vm') := p in
         exists vars,
           NoDup vars /\
           List.length vars = n /\
           FromList vars \subset S /\
           ctx_p = ctx_bind_proj ct scrut vars (List.length vars) /\
           var_map_correct vm' (vars ++ vn) /\
           identifiers.fresh (S \\ FromList vars) (next_var (fst s')) }}.
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

  Lemma anf_convert_exp_sound : anf_convert_exp_corresp.
  Proof.
    unfold anf_convert_exp_corresp.
    intros e. induction e using EInduction.term_forall_list_ind;
    intros vn vm S Hvm.

    - (* tRel n *)
      simpl. unfold convert_anf. simpl.
      rewrite (Hvm n).
      destruct (nth_error vn n) eqn:Hnth.
      + eapply return_triple. intros _ s Hfresh.
        eexists. split; [ econstructor; exact Hnth | exact Hfresh ].
      + (* error — term not well-scoped, triple holds vacuously *)
        unfold triple. intros r w _. simpl.
        destruct (runState _ r w). destruct e. auto. auto.

    - (* tVar — impossible in our pipeline *)
      simpl. unfold triple. intros r w _. destruct (runState _ r w). destruct e; auto.
    - (* tEvar — impossible *)
      simpl. unfold triple. intros r w _. destruct (runState _ r w). destruct e; auto.
    - (* tLambda *)
      simpl.
      eapply bind_triple. eapply get_named_spec'.
      intros x w.
      eapply pre_curry_l. intros Hx_in.
      eapply pre_strenghtening.
      { intros ? ? [_ Hfresh]. exact Hfresh. }
      eapply bind_triple. eapply get_named_str_spec'.
      intros f w'.
      eapply pre_curry_l. intros Hf_in.
      eapply pre_strenghtening.
      { intros ? ? [_ Hfresh]. exact Hfresh. }
      eapply bind_triple.
      { eapply IHe. eapply var_map_correct_cons. exact Hvm. }
      intros [r C_body] w''.
      eapply pre_existential. intros S'.
      eapply pre_curry_l. intros Hconvert_body.
      eapply return_triple.
      intros _ s Hfresh.
      eexists S'. split; [ | exact Hfresh ].
      econstructor; eassumption.
    - (* tLetIn *)
      simpl.
      eapply bind_triple.
      { eapply IHe1. exact Hvm. }
      intros [x1 C1] w.
      eapply pre_existential. intros S2.
      eapply pre_curry_l. intros Hconvert1.
      eapply bind_triple.
      { eapply IHe2. eapply var_map_correct_cons. exact Hvm. }
      intros [r C2] w'.
      eapply pre_existential. intros S3.
      eapply pre_curry_l. intros Hconvert2.
      eapply return_triple.
      intros _ s Hfresh.
      eexists S3. split; [ | exact Hfresh ].
      econstructor; eassumption.
    - (* tApp *)
      simpl.
      eapply bind_triple.
      { eapply IHe1. exact Hvm. }
      intros [x1 C1] w.
      eapply pre_existential. intros S2.
      eapply pre_curry_l. intros Hconvert1.
      eapply bind_triple.
      { eapply IHe2. exact Hvm. }
      intros [x2 C2] w'.
      eapply pre_existential. intros S3.
      eapply pre_curry_l. intros Hconvert2.
      eapply bind_triple. eapply get_named_str_spec'.
      intros r w''. eapply return_triple.
      intros _ s [Hr_in [_ Hfresh']].
      eexists (S3 \\ [set r]). split; [ | exact Hfresh' ].
      econstructor; eassumption.
    - (* tConst *)
      simpl.
      destruct (find_prim prims k) eqn:Hprim.
      + (* primitive — TODO *)
        admit.
      + destruct (lookup_const cmap k) eqn:Hlookup.
        * eapply return_triple. intros _ s Hfresh.
          eexists. split; [ econstructor; exact Hlookup | exact Hfresh ].
        * unfold triple. intros r w _. destruct (runState _ r w). destruct e; auto.
    - (* tConstruct *)
      simpl.
      eapply bind_triple. eapply get_named_str_spec'.
      intros x w.
      eapply pre_curry_l. intros Hx_in.
      eapply pre_strenghtening.
      { intros ? ? [_ Hfresh]. exact Hfresh. }
      eapply bind_triple.
      { (* prove args inline using All IH *)
        clear -H Hvm.
        induction H as [| t args' IH_t IH_rest IH_args].
        - simpl. eapply return_triple. intros _ s Hfresh.
          eexists. split; [ econstructor | exact Hfresh ].
        - simpl.
          eapply bind_triple.
          { eapply IH_t. exact Hvm. }
          intros [y C1] w.
          eapply pre_existential. intros S2.
          eapply pre_curry_l. intros Hconvert1.
          eapply bind_triple.
          { eapply IH_args. exact Hvm. }
          intros [ys C2] w'.
          eapply pre_existential. intros S3.
          eapply pre_curry_l. intros Hconvert2.
          eapply return_triple.
          intros _ s Hfresh.
          eexists S3. split; [ | exact Hfresh ].
          econstructor; eassumption. }
      intros [ys C_args] w'.
      eapply pre_existential. intros S2.
      eapply pre_curry_l. intros Hconvert_args.
      eapply return_triple.
      intros _ s Hfresh.
      eexists S2. split; [ | exact Hfresh ].
      econstructor; [ reflexivity | exact Hx_in | exact Hconvert_args ].
    - (* tCase *)
      simpl. destruct p as [ind npars].
      eapply bind_triple. eapply get_named_str_spec'.
      intros f w. eapply pre_curry_l. intros Hf_in.
      eapply pre_strenghtening. { intros ? ? [_ Hfr]. exact Hfr. }
      eapply bind_triple. eapply get_named_str_spec'.
      intros y w'. eapply pre_curry_l. intros Hy_in.
      eapply pre_strenghtening. { intros ? ? [_ Hfr]. exact Hfr. }
      eapply bind_triple. { eapply IHe. exact Hvm. }
      intros [x1 C1] w''.
      eapply pre_existential. intros S2.
      eapply pre_curry_l. intros Hconvert_scr.
      eapply bind_triple.
      { (* branches — inline using Forall IH *)
        clear -H0 Hvm.
        revert S. generalize 0%N as n.
        induction H0 as [| [lnames e_br] brs' [IH_body _] IH_rest IH_brs];
          intros n S.
        (* nil *)
        - simpl. eapply return_triple. intros _ s Hfresh.
          eexists. split; [ econstructor | exact Hfresh ].
        (* cons *)
        - simpl.
          eapply bind_triple. { eapply IH_brs. }
          intros pats' w1.
          eapply pre_existential. intros S2.
          eapply pre_curry_l. intros Hconvert_rest.
          eapply bind_triple.
          { eapply proj_ctx_spec. exact Hvm. }
          intros [Cproj vm'] w2.
          eapply pre_existential. intros vars.
          eapply pre_curry_l. intros Hnd.
          eapply pre_curry_l. intros Hlen_vars.
          eapply pre_curry_l. intros Hsub_vars.
          eapply pre_curry_l. intros Hcproj.
          eapply pre_curry_l. intros Hvm'.
          eapply bind_triple.
          { eapply IH_body. exact Hvm'. }
          intros [r1 C1] w3.
          eapply pre_existential. intros S3.
          eapply pre_curry_l. intros Hconvert_body.
          eapply return_triple. intros _ s Hfresh.
          eexists S3. split; [ | exact Hfresh ].
          econstructor; [ reflexivity | exact Hconvert_rest
                        | exact Hsub_vars | exact Hnd | exact Hlen_vars
                        | subst; reflexivity | exact Hconvert_body ]. }
      intros pats w'''.
      eapply pre_existential. intros S3.
      eapply pre_curry_l. intros Hconvert_brs.
      eapply bind_triple. eapply get_named_str_spec'.
      intros r w4. eapply return_triple.
      intros _ s [Hr_in [_ Hfresh']].
      eexists (S3 \\ [set r]). split; [ | exact Hfresh' ].
      econstructor; eassumption.
    - (* tProj *)
      simpl.
      eapply bind_triple.
      { eapply IHe. exact Hvm. }
      intros [x C_sub] w.
      eapply pre_existential. intros S2.
      eapply pre_curry_l. intros Hconvert_sub.
      eapply bind_triple. eapply get_named_str_spec'.
      intros y w'. eapply return_triple.
      intros _ s [Hy_in [_ Hfresh']].
      eexists (S2 \\ [set y]). split; [ | exact Hfresh' ].
      econstructor; [ reflexivity | exact Hconvert_sub | exact Hy_in ].
    - (* tFix *)
      simpl.
      eapply bind_triple.
      { eapply add_fix_names_spec. exact Hvm. }
      intros [names vm'] w.
      eapply pre_curry_l. intros Hnd.
      eapply pre_curry_l. intros Hlen.
      eapply pre_curry_l. intros Hsub.
      eapply pre_curry_l. intros Hvm'.
      eapply bind_triple.
      { (* mfix conversion inline using All IH *)
        clear -H Hvm' Hlen.
        revert names n vm' Hvm' Hlen.
        induction H as [| d mfix' IH_d IH_rest IH_mfix];
          intros names idx vm' Hvm' Hlen.
        (* nil *)
        - destruct names; [ | simpl in Hlen; congruence ].
          simpl. eapply return_triple. intros _ s Hfresh.
          eexists. split; [ econstructor | ].
          split; [ intros f Hf; destruct idx; discriminate | exact Hfresh ].
        (* cons *)
        - destruct names as [| f_name rest]; [ simpl in Hlen; congruence | ].
          simpl in Hlen.
          simpl.
          destruct (EAst.dbody d) eqn:Hbody.
          all: try (unfold triple; intros r w0 _; destruct (runState _ r w0); destruct e; auto).
          (* body must be tLambda *)
          eapply bind_triple. eapply get_named_spec'.
          intros x w1.
          eapply pre_curry_l. intros Hx_in.
          eapply pre_strenghtening. { intros ? ? [_ Hf]. exact Hf. }
          eapply bind_triple.
          { eapply IH_d. eapply var_map_correct_cons. exact Hvm'. }
          intros [r1 C1] w2.
          eapply pre_existential. intros S2.
          eapply pre_curry_l. intros Hconvert_body.
          eapply bind_triple.
          { eapply IH_mfix; [ exact Hvm' | lia ]. }
          intros [fi defs'] w3.
          eapply pre_existential. intros S3.
          eapply pre_curry_l. intros Hconvert_rest.
          eapply pre_curry_l. intros Hfi_eq.
          eapply return_triple. intros _ s Hfresh.
          eexists S3. split; [ | split ].
          + econstructor; [ exact Hbody | exact Hx_in | exact Hconvert_body | ].
            exact (proj1 Hconvert_rest).
          + intros f Hf.
            destruct idx.
            * simpl in Hf. congruence.
            * eapply Hfi_eq. exact Hf.
          + exact Hfresh. }
      intros [fi defs] w'.
      eapply pre_existential. intros S2.
      eapply pre_curry_l. intros Hconvert_mfix.
      eapply pre_curry_l. intros Hfi_eq.
      eapply return_triple. intros _ s Hfresh.
      (* Need nth_error names n = Some fi *)
      destruct (nth_error names n) eqn:Hnth.
      2:{ exfalso. apply nth_error_None in Hnth.
          rewrite Hlen in Hnth. apply Forall_length in H. lia. }
      assert (fi = v) as -> by (eapply Hfi_eq; exact Hnth).
      eexists S2. split; [ | exact Hfresh ].
      econstructor; eassumption.
    - (* tCoFix — impossible *)
      simpl. unfold triple. intros r w _. destruct (runState _ r w). destruct e; auto.
    - (* tPrim *)
      simpl.
      destruct (trans_prim_val p) eqn:Hprim.
      + eapply bind_triple. eapply get_named_str_spec'.
        intros x w. eapply return_triple.
        intros _ s [Hx_in [_ Hfresh']].
        eexists (S \\ [set x]). split; [ | exact Hfresh' ].
        econstructor; [ exact Hprim | exact Hx_in ].
      + unfold triple. intros r w _. destruct (runState _ r w). destruct e; auto.
    - (* tLazy — impossible *)
      simpl. unfold triple. intros r w _. destruct (runState _ r w). destruct e; auto.
    - (* tForce — impossible *)
      simpl. unfold triple. intros r w _. destruct (runState _ r w). destruct e; auto.
    - (* tBox *)
      simpl.
      eapply bind_triple. eapply get_named_str_spec'.
      intros x w. eapply return_triple.
      intros _ s [Hx_in [_ Hfresh']].
      eexists (S \\ [set x]). split; [ | exact Hfresh' ].
      econstructor. exact Hx_in.
  Admitted.

  Lemma anf_convert_sound :
    anf_convert_exp_corresp /\
    anf_convert_args_corresp /\
    anf_convert_mfix_corresp /\
    anf_convert_branches_corresp.
  Proof.
    split; [ exact anf_convert_exp_sound | ].
    split.
    { (* anf_convert_args_corresp *)
      unfold anf_convert_args_corresp.
      intros args. induction args as [| t args' IHargs];
      intros vn vm S Hvm.
      - (* nil *)
        simpl. eapply return_triple. intros _ s Hfresh.
        eexists. split; [ econstructor | exact Hfresh ].
      - (* cons *)
        simpl.
        eapply bind_triple.
        { eapply anf_convert_exp_sound. exact Hvm. }
        intros [y C1] w.
        eapply pre_existential. intros S2.
        eapply pre_curry_l. intros Hconvert1.
        eapply bind_triple.
        { eapply IHargs. exact Hvm. }
        intros [ys C2] w'.
        eapply pre_existential. intros S3.
        eapply pre_curry_l. intros Hconvert2.
        eapply return_triple.
        intros _ s Hfresh.
        eexists S3. split; [ | exact Hfresh ].
        econstructor; eassumption. }
    split; [ admit | ]. (* mfix *)
    admit. (* branches *)
  Admitted.

End Corresp.
