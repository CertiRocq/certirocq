(* Correspondence between monadic convert_anf and relational anf_cvt_rel *)

From Stdlib Require Import ZArith.ZArith NArith.NArith Lists.List micromega.Lia Arith
     Ensembles Relations.Relation_Definitions.
From MetaRocq.Erasure Require Import EAst EGlobalEnv EWellformed EInduction.
From MetaRocq.Utils Require Import All_Forall.
From MetaRocq.Common Require Import BasicAst Kernames.
From MetaRocq.Utils Require Import bytestring.
From compcert Require Import lib.Maps lib.Coqlib.
From ExtLib Require Import Structures.Monads Data.Monads.OptionMonad.
From CertiRocq.Common Require Import AstCommon compM.
From CertiRocq Require Import Pipeline_utils.
From CertiRocq.LambdaANF Require Import
  cps cps_util ctx List_util Ensembles_util
  identifiers state set_util tactics
  closure_conversion_corresp.
From CertiRocq.LambdaBox_to_LambdaANF Require Import common ANF.

Import ListNotations.
Import Monad.MonadNotation.
Open Scope monad_scope.
Open Scope bs_scope.


Section Corresp.

  Context (func_tag default_tag : positive)
          (prim_map : M.t primitive)
          (tgm : conId_map)
          (prims : list (primitive * positive))
          (cmap : const_map).


  (** * var_map correctness *)

  Definition var_map_correct (vm : var_map) (vn : list var) : Prop :=
    forall i, get_var_name vm (N.of_nat i) = nth_error vn i.

  Lemma var_map_correct_nil :
    var_map_correct new_var_map [].
  Proof.
    unfold var_map_correct, new_var_map, get_var_name.
    intros []; reflexivity.
  Qed.

  (* Helper: looking up index 0 in an extended var_map yields the new variable *)
  Lemma get_var_name_add_0 vm x :
    get_var_name (add_var_name vm x) 0%N = Some x.
  Proof.
    unfold add_var_name, get_var_name.
    destruct vm as [m p]. simpl.
    destruct p; simpl; rewrite M.gss; reflexivity.
  Qed.

  (* Helper: looking up a successor index in an extended var_map
     gives the same result as the original map at the predecessor index.
     Key idea: add_var_name increments the internal counter by 1,
     so shifting the lookup index by 1 cancels out. *)
  Lemma get_var_name_add_succ vm x n :
    get_var_name (add_var_name vm x) (N.succ n) = get_var_name vm n.
  Proof.
    unfold add_var_name, get_var_name.
    destruct vm as [m p].
    (* LHS: match (Npos (N.succ_pos p) - N.succ n) with ... end
       RHS: match (p - n) with ... end
       Key fact: Npos (N.succ_pos p) - N.succ n = p - n *)
    replace (Npos (N.succ_pos p) - N.succ n)%N with (p - n)%N.
    2:{ rewrite N.succ_pos_spec. lia. }
    destruct (p - n)%N as [| q] eqn:Hdiff; [reflexivity |].
    rewrite M.gso; [reflexivity |].
    (* q <> N.succ_pos p: if q = N.succ_pos p then (p-n) = N.succ p,
       but (p-n) <= p < N.succ p, contradiction. *)
    intros Heq. subst q. rewrite N.succ_pos_spec in Hdiff. lia.
  Qed.

  Lemma var_map_correct_cons vm vn x :
    var_map_correct vm vn ->
    var_map_correct (add_var_name vm x) (x :: vn).
  Proof.
    intros Hvm i. destruct i as [| i'].
    - (* i = 0 *)
      simpl. exact (get_var_name_add_0 vm x).
    - (* i = S i' *)
      change (nth_error (x :: vn) (S i')) with (nth_error vn i').
      rewrite <- (Hvm i').
      rewrite Nat2N.inj_succ.
      exact (get_var_name_add_succ vm x (N.of_nat i')).
  Qed.

  Lemma var_map_correct_fold_right vm vn vars :
    var_map_correct vm vn ->
    var_map_correct
      (List.fold_right (fun v vm' => add_var_name vm' v) vm vars)
      (vars ++ vn).
  Proof.
    induction vars; simpl; intros Hvm.
    - exact Hvm.
    - apply var_map_correct_cons, IHvars, Hvm.
  Qed.

  (** * Fresh name specs *)

  (* get_named_str_fresh is imported from closure_conversion_corresp.
     We prove the analogous spec for get_named. Both functions have
     the same monadic structure: get state, increment next_var, put, ret old next_var. *)

  Lemma get_named_fresh :
    forall (A : Type) (S0 : Ensemble var) (na : name),
      {{ fun (_ : unit) (s : comp_data * A) => fresh S0 (next_var (fst s)) }}
        get_named na
      {{ fun (_ : unit) (s : comp_data * A) (x : var) (s' : comp_data * A) =>
           x \in S0 /\
           (next_var (fst s) < next_var (fst s'))%positive /\
           fresh (S0 \\ [set x]) (next_var (fst s')) }}.
  Proof.
    intros.
    eapply pre_post_mp_l.
    eapply bind_triple. now eapply get_triple.
    intros [[] w1] [[] w2].
    eapply pre_post_mp_l.
    eapply bind_triple. now eapply put_triple.
    intros x [r3 w3].
    eapply return_triple.
    intros ? [r4 w4] H2. inv H2. intros [H1 H2]. inv H1; inv H2. intros Hfresh.
    split. eapply Hfresh. reflexivity.
    simpl. split. zify; lia.
    intros z Hin. constructor. eapply Hfresh; eauto. simpl. zify. lia.
    intros Hc. inv Hc. zify; lia.
  Qed.

  Lemma names_lst_length ns m :
    List.length (names_lst_len ns m) = m.
  Proof.
    revert m; induction ns; intros []; simpl; try reflexivity.
    - rewrite repeat_length. reflexivity.
    - f_equal. apply IHns.
  Qed.

  (* Spec for get_named_lst: produces a NoDup list of fresh names from S0. *)
  Lemma get_named_lst_spec :
    forall (S0 : Ensemble var) (strs : list name),
      {{ fun _ (s : comp_data * unit) => fresh S0 (next_var (fst s)) }}
        get_named_lst strs
      {{ fun _ s xs s' =>
           NoDup xs /\
           List.length xs = List.length strs /\
           FromList xs \subset S0 /\
           fresh (S0 \\ FromList xs) (next_var (fst s')) }}.
  Proof.
    intros S0 strs. revert S0.
    induction strs as [| a strs' IH]; intros S0; simpl.
    - unfold get_named_lst. simpl.
      eapply return_triple. intros _ w Hf.
      repeat normalize_sets.
      split; [constructor | split; [reflexivity | split; [sets | assumption]]].
    - unfold get_named_lst. simpl. unfold mapM. simpl.
      eapply bind_triple. eapply get_named_fresh.
      intros x w.
      eapply pre_curry_l. intros Hx.
      eapply pre_strenghtening. { intros ? ? [_ Hf]. exact Hf. }
      eapply bind_triple.
      change (mapM get_named strs') with (get_named_lst strs').
      eapply IH.
      intros xs w'. eapply return_triple.
      intros _ s [Hnd [Hlen [Hsub Hfresh]]].
      repeat normalize_sets.
      split; [| split; [| split]].
      + constructor; eauto. intros Hc.
        eapply Hsub in Hc. inv Hc. now eauto.
      + simpl. congruence.
      + eapply Union_Included. now sets.
        eapply Included_trans; [eapply Hsub | sets].
      + rewrite <- Setminus_Union. assumption.
  Qed.

  (** * Spec for proj_ctx *)

  Lemma proj_ctx_spec names n scrut vm ct S0 vn
    (Hvm : var_map_correct vm vn) :
    {{ fun _ (s : comp_data * unit) => fresh S0 (next_var (fst s)) }}
      proj_ctx names n scrut vm ct
    {{ fun _ s (p : exp_ctx * var_map) s' =>
         let (ctx_p, vm') := p in
         exists vars,
           NoDup vars /\
           List.length vars = n /\
           FromList vars \subset S0 /\
           ctx_p = ctx_bind_proj ct scrut vars (List.length vars) /\
           var_map_correct vm' (vars ++ vn) /\
           fresh (S0 \\ FromList vars) (next_var (fst s')) }}.
  Proof.
    unfold proj_ctx.
    eapply bind_triple. eapply get_named_lst_spec.
    intros vars w'. eapply return_triple.
    intros _ w [Hnd [Hlen [Hsub Hfr]]].
    exists vars.
    split; [exact Hnd |].
    split; [rewrite Hlen; apply names_lst_length |].
    split; [exact Hsub |].
    split; [reflexivity |].
    split; [apply var_map_correct_fold_right, Hvm |].
    exact Hfr.
  Qed.


  (** * Spec for add_fix_names *)

  Lemma add_fix_names_spec :
    forall mfix S0 vm vn
      (Hvm : var_map_correct vm vn),
    {{ fun _ (s : comp_data * unit) => fresh S0 (next_var (fst s)) }}
      add_fix_names mfix vm
    {{ fun _ s (p : list var * var_map) s' =>
         let (names, vm') := p in
         NoDup names /\
         List.length names = List.length mfix /\
         FromList names \subset S0 /\
         var_map_correct vm' (List.rev names ++ vn) /\
         fresh (S0 \\ FromList names) (next_var (fst s')) }}.
  Proof.
    induction mfix; intros S0 vm vn Hvm.
    - (* nil *)
      simpl. eapply return_triple.
      intros _ w Hf. repeat normalize_sets.
      split; [constructor |].
      split; [reflexivity |].
      split; [sets |].
      split; [exact Hvm | assumption].
    - (* cons *)
      simpl.
      (* Step 1: get_named allocates f *)
      eapply bind_triple. eapply get_named_fresh.
      intros f w.
      eapply pre_curry_l; intros Hf_in.
      eapply pre_strenghtening. { intros ? ? [_ Hfr]. exact Hfr. }
      (* Step 2: recursive call with updated vm *)
      eapply bind_triple.
      eapply IHmfix. eapply var_map_correct_cons. exact Hvm.
      (* Step 3: destructure result and return *)
      intros [names vm'] w'.
      eapply pre_curry_l; intros Hnd.
      eapply pre_curry_l; intros Hlen.
      eapply pre_curry_l; intros Hsub.
      eapply pre_curry_l; intros Hvm'.
      eapply return_triple. intros _ w'' Hfr.
      repeat normalize_sets.
      split; [| split; [| split; [| split]]].
      + (* NoDup (f :: names) *)
        constructor; [| exact Hnd].
        intros Hc. eapply Hsub in Hc. inv Hc. now eauto.
      + (* length *)
        simpl. congruence.
      + (* FromList (f :: names) ⊆ S0 *)
        eapply Union_Included. now sets.
        eapply Included_trans; [exact Hsub | sets].
      + (* var_map_correct *)
        simpl rev. rewrite <- app_assoc. simpl. exact Hvm'.
      + (* fresh *)
        rewrite <- Setminus_Union. exact Hfr.
  Qed.

  (** * Correspondence statements *)

  Context {efl : EEnvFlags}.
  Context (Σ : global_context).

  (* Flags: our pipeline excludes tVar, tEvar, tCoFix, tLazy, tForce
     and uses block constructors *)
  Context (HnoVar : has_tVar = false)
          (HnoEvar : has_tEvar = false)
          (HnoCoFix : has_tCoFix = false)
          (HnoLazy : has_tLazy_Force = false)
          (Hblocks : cstr_as_blocks = true).

  Let convert_anf' := convert_anf func_tag default_tag prim_map tgm prims cmap.

  (* For tConst: assume no primitive constants (find_prim always fails).
     Also assume every constant in Σ is in cmap. *)
  Context (no_prims : forall s, find_prim prims s = None).
  Context (cmap_complete : forall s d,
    lookup_constant Σ s = Some d -> lookup_const cmap s <> None).

  (* Helper: args correspondence from per-term IH.
     Given All (per-term correspondence) args, prove the args triple. *)
  Lemma anf_cvt_args_corresp :
    forall args vn vm
      (Hall : All (fun t => forall vn vm S0
        (Hwf : wellformed Σ (List.length vn) t = true)
        (Hvm : var_map_correct vm vn),
        {{ fun _ s => fresh S0 (next_var (fst s)) }}
          convert_anf' t vm
        {{ fun _ s p s' => let '(r, C) := p in
           exists S', anf_cvt_rel func_tag default_tag tgm cmap S0 t vn S' C r /\
           fresh S' (next_var (fst s')) }}) args)
      (Hwf : forallb (wellformed Σ (List.length vn)) args = true)
      (Hvm : var_map_correct vm vn)
      S0,
    {{ fun _ s => fresh S0 (next_var (fst s)) }}
      convert_anf_args convert_anf' args vm
    {{ fun _ s p s' => let '(xs, C) := p in
       exists S', anf_cvt_rel_args func_tag default_tag tgm cmap S0 args vn S' C xs /\
       fresh S' (next_var (fst s')) }}.
  Proof.
    induction args as [| t args' IHargs]; intros vn vm Hall Hwf Hvm S0.
    - simpl. eapply return_triple. intros _ s Hfr.
      eexists. split; [econstructor | exact Hfr].
    - simpl in Hwf. apply Bool.andb_true_iff in Hwf as [Hwf_hd Hwf_tl].
      inversion Hall as [| ? ? IH_hd IH_tl]; subst.
      simpl.
      eapply bind_triple. { eapply IH_hd; eassumption. }
      intros [y C1] w. eapply pre_existential; intros S2.
      eapply pre_curry_l; intros Hcvt1.
      eapply bind_triple. { eapply IHargs; eassumption. }
      intros [ys C2] w'. eapply pre_existential; intros S3.
      eapply pre_curry_l; intros Hcvt2.
      eapply return_triple. intros _ s Hfr.
      eexists. split; [econstructor; eassumption | exact Hfr].
  Qed.

  (* Helper: branches correspondence from per-branch IH *)
  Lemma anf_cvt_branches_corresp :
    forall ind brs n scrut vn vm
      (Hall : All (fun br : list name * EAst.term => forall vn vm S0
        (Hwf : wellformed Σ (List.length vn) (snd br) = true)
        (Hvm : var_map_correct vm vn),
        {{ fun _ s => fresh S0 (next_var (fst s)) }}
          convert_anf' (snd br) vm
        {{ fun _ s p s' => let '(r, C) := p in
           exists S', anf_cvt_rel func_tag default_tag tgm cmap S0 (snd br) vn S' C r /\
           fresh S' (next_var (fst s')) }}) brs)
      (Hwf : forallb (fun br : list name * EAst.term =>
               wellformed Σ (List.length (fst br) + List.length vn) (snd br)) brs = true)
      (Hvm : var_map_correct vm vn)
      S0,
    {{ fun _ s => fresh S0 (next_var (fst s)) }}
      convert_anf_branches default_tag tgm convert_anf' ind brs n scrut vm
    {{ fun _ s pats s' =>
       exists S', anf_cvt_rel_branches func_tag default_tag tgm cmap S0 ind brs n vn scrut S' pats /\
       fresh S' (next_var (fst s')) }}.
  Proof.
    induction brs as [| [lnames e_br] brs' IHbrs];
    intros n scrut vn vm Hall Hwf_brs Hvm S0.
    - (* nil *)
      simpl. eapply return_triple. intros _ s Hfr.
      eexists. split; [econstructor | exact Hfr].
    - (* cons *)
      simpl in Hwf_brs. apply Bool.andb_true_iff in Hwf_brs as [Hwf_hd Hwf_tl].
      inversion Hall as [| ? ? IH_hd IH_tl]; subst.
      simpl.
      (* Step 1: recurse on remaining branches *)
      eapply bind_triple. { eapply IHbrs; eassumption. }
      intros pats' w1. eapply pre_existential; intros S2.
      eapply pre_curry_l; intros Hcvt_rest.
      (* Step 2: proj_ctx for this branch *)
      eapply bind_triple. { eapply proj_ctx_spec. exact Hvm. }
      intros [Cproj vm'] w2.
      eapply pre_existential; intros vars.
      eapply pre_curry_l; intros Hnd.
      eapply pre_curry_l; intros Hlen.
      eapply pre_curry_l; intros Hsub.
      eapply pre_curry_l; intros Hctx.
      eapply pre_curry_l; intros Hvm'.
      (* Step 3: convert branch body with extended vm *)
      eapply bind_triple.
      { eapply (IH_hd (List.app vars vn)); [| exact Hvm'].
        rewrite app_length, Hlen. exact Hwf_hd. }
      intros [r1 C1] w3. eapply pre_existential; intros S3.
      eapply pre_curry_l; intros Hcvt_body.
      eapply return_triple. intros _ s Hfr.
      eexists. split; [| exact Hfr].
      eapply anf_Branches_cons;
        [reflexivity | exact Hcvt_rest | exact Hsub | exact Hnd
         | exact Hlen | subst; reflexivity | exact Hcvt_body].
  Qed.

  (* Helper: mfix correspondence from per-body IH *)
  Lemma anf_cvt_mfix_corresp :
    forall mfix fnames idx vn vm
      (Hall : All (fun d : EAst.def EAst.term => forall vn vm S0
        (Hwf : wellformed Σ (List.length vn) (EAst.dbody d) = true)
        (Hvm : var_map_correct vm vn),
        {{ fun _ s => fresh S0 (next_var (fst s)) }}
          convert_anf' (EAst.dbody d) vm
        {{ fun _ s p s' => let '(r, C) := p in
           exists S', anf_cvt_rel func_tag default_tag tgm cmap S0 (EAst.dbody d) vn S' C r /\
           fresh S' (next_var (fst s')) }}) mfix)
      (Hlen : List.length fnames = List.length mfix)
      (Hwf_mfix : forallb (fun d => isLambda (EAst.dbody d)) mfix = true)
      (Hwf_bodies : forallb (test_def (wellformed Σ (List.length mfix + List.length vn))) mfix = true)
      (Hvm : var_map_correct vm vn)
      S0,
    {{ fun _ s => fresh S0 (next_var (fst s)) }}
      convert_anf_mfix func_tag convert_anf' mfix fnames idx vm
    {{ fun _ s (p : var * fundefs) s' =>
         let '(fi, B) := p in
         exists S',
           anf_cvt_rel_mfix func_tag default_tag tgm cmap S0 mfix vn fnames S' B /\
           (forall f, nth_error fnames idx = Some f -> fi = f) /\
           fresh S' (next_var (fst s')) }}.
  Proof.
    admit.
  Admitted.

  (* Main correspondence *)
  Lemma anf_cvt_exp_corresp :
    forall e vn vm S0
      (Hwf : wellformed Σ (List.length vn) e = true)
      (Hvm : var_map_correct vm vn),
    {{ fun _ s => fresh S0 (next_var (fst s)) }}
      convert_anf' e vm
    {{ fun _ s (p : var * exp_ctx) s' =>
         let '(r, C) := p in
         exists S',
           anf_cvt_rel func_tag default_tag tgm cmap S0 e vn S' C r /\
           fresh S' (next_var (fst s')) }}.
  Proof.
    intros e. induction e using EInduction.term_forall_list_ind;
    intros vn vm S0 Hwf Hvm; simpl in Hwf.

    - (* tBox *)
      simpl.
      eapply bind_triple. eapply get_named_str_fresh.
      intros x w. eapply return_triple.
      intros _ s [Hx_in [_ [_ Hfr]]].
      eexists. split; [econstructor; exact Hx_in | exact Hfr].

    - (* tRel n *)
      simpl. rewrite (Hvm n).
      assert (Hn : (n < List.length vn)%nat).
      { apply Bool.andb_true_iff in Hwf as [_ Hlt].
        apply Nat.ltb_lt in Hlt. exact Hlt. }
      destruct (nth_error vn n) eqn:Hnth.
      2:{ apply nth_error_None in Hnth. lia. }
      eapply return_triple. intros _ s Hfr.
      eexists. split; [econstructor; exact Hnth | exact Hfr].

    - (* tVar *) rewrite HnoVar in Hwf. discriminate.
    - (* tEvar *) rewrite HnoEvar in Hwf. discriminate.

    - (* tLambda na body *)
      simpl. apply Bool.andb_true_iff in Hwf as [_ Hwf_body].
      eapply bind_triple. eapply get_named_fresh.
      intros x w. eapply pre_curry_l; intros Hx.
      eapply pre_strenghtening. { intros ? ? [_ Hfr]. exact Hfr. }
      eapply bind_triple. eapply get_named_fresh.
      intros f w'. eapply pre_curry_l; intros Hf.
      eapply pre_strenghtening. { intros ? ? [_ Hfr]. exact Hfr. }
      eapply bind_triple.
      { eapply (IHe (x :: vn)); [exact Hwf_body | eapply var_map_correct_cons; exact Hvm]. }
      intros [r C] w''.
      eapply pre_existential; intros S'.
      eapply pre_curry_l; intros Hcvt.
      eapply return_triple. intros _ s Hfr.
      eexists. split; [econstructor; eassumption | exact Hfr].

    - (* tLetIn na b t *)
      apply Bool.andb_true_iff in Hwf as [Hwf_rest Hwf_t].
      apply Bool.andb_true_iff in Hwf_rest as [_ Hwf_b].
      simpl.
      eapply bind_triple. { eapply IHe1; eassumption. }
      intros [x1 C1] w. eapply pre_existential; intros S2.
      eapply pre_curry_l; intros Hcvt1.
      eapply bind_triple.
      { eapply (IHe2 (x1 :: vn));
        [exact Hwf_t | eapply var_map_correct_cons; exact Hvm]. }
      intros [r C2] w'. eapply pre_existential; intros S3.
      eapply pre_curry_l; intros Hcvt2.
      eapply return_triple. intros _ s Hfr.
      eexists. split; [econstructor; eassumption | exact Hfr].

    - (* tApp u v *)
      apply Bool.andb_true_iff in Hwf as [Hwf_rest Hwf_v].
      apply Bool.andb_true_iff in Hwf_rest as [_ Hwf_u].
      simpl.
      eapply bind_triple. { eapply IHe1; eassumption. }
      intros [x1 C1] w. eapply pre_existential; intros S2.
      eapply pre_curry_l; intros Hcvt1.
      eapply bind_triple. { eapply IHe2; eassumption. }
      intros [x2 C2] w'. eapply pre_existential; intros S3.
      eapply pre_curry_l; intros Hcvt2.
      eapply bind_triple. eapply get_named_fresh.
      intros r w''. eapply return_triple.
      intros _ s [Hr [_ Hfr]].
      eexists. split; [econstructor; eassumption | exact Hfr].

    - (* tConst s *)
      simpl. rewrite no_prims.
      apply Bool.andb_true_iff in Hwf as [_ Hwf_const].
      destruct (lookup_constant Σ s) as [d |] eqn:Hd; [| discriminate].
      specialize (cmap_complete s d Hd).
      destruct (lookup_const cmap s) eqn:Hlookup; [| contradiction].
      eapply return_triple. intros _ s0 Hfr.
      eexists. split; [econstructor; exact Hlookup | exact Hfr].

    - (* tConstruct ind c args *)
      simpl.
      eapply bind_triple. eapply get_named_fresh.
      intros x w. eapply pre_curry_l; intros Hx.
      eapply pre_strenghtening. { intros ? ? [_ Hfr]. exact Hfr. }
      eapply bind_triple.
      { eapply anf_cvt_args_corresp; [exact X | | exact Hvm].
        (* Extract forallb (wellformed ...) args from Hwf *)
        rewrite Hblocks in Hwf.
        apply Bool.andb_true_iff in Hwf as [_ Hwf_args].
        apply Bool.andb_true_iff in Hwf_args as [_ Hwf_args].
        exact Hwf_args. }
      intros [ys C] w'.
      eapply pre_existential; intros S2.
      eapply pre_curry_l; intros Hcvt_args.
      eapply return_triple. intros _ s Hfr.
      eexists. split; [econstructor; [reflexivity | exact Hx | exact Hcvt_args] | exact Hfr].

    - (* tCase (ind, npars) mch brs *)
      destruct p as [ind npars]. simpl.
      (* Decompose wellformed:
         has_tCase && ((wf_brs && wellformed mch) && forallb brs) = true *)
      apply Bool.andb_true_iff in Hwf as [_ Hwf].
      apply Bool.andb_true_iff in Hwf as [Hwf_lhs Hwf_brs].
      apply Bool.andb_true_iff in Hwf_lhs as [_ Hwf_mch].
      simpl.
      (* Step 1-2: allocate f and y *)
      eapply bind_triple. eapply get_named_fresh.
      intros f w. eapply pre_curry_l; intros Hf.
      eapply pre_strenghtening. { intros ? ? [_ Hfr]. exact Hfr. }
      eapply bind_triple. eapply get_named_fresh.
      intros yv w'. eapply pre_curry_l; intros Hyv.
      eapply pre_strenghtening. { intros ? ? [_ Hfr]. exact Hfr. }
      (* Step 3: convert scrutinee *)
      eapply bind_triple. { eapply IHe. apply Hwf_mch. apply Hvm. }
      intros [x1 C1] w''. eapply pre_existential; intros S2.
      eapply pre_curry_l; intros Hcvt_mch.
      (* Step 4: convert branches *)
      eapply bind_triple.
      { eapply anf_cvt_branches_corresp; [exact X | exact Hwf_brs | exact Hvm]. }
      intros pats w'''. eapply pre_existential; intros S3.
      eapply pre_curry_l; intros Hcvt_brs.
      (* Step 5: allocate result variable *)
      eapply bind_triple. eapply get_named_fresh.
      intros r w4. eapply return_triple.
      intros _ s [Hr [_ Hfr]].
      eexists. split; [| exact Hfr].
      eapply anf_Case.
      + exact Hf.
      + exact Hyv.
      + exact Hcvt_mch.
      + exact Hcvt_brs.
      + exact Hr.

    - (* tProj p c *)
      apply Bool.andb_true_iff in Hwf as [Hwf_rest Hwf_c].
      apply Bool.andb_true_iff in Hwf_rest as [_ _].
      simpl.
      eapply bind_triple. { eapply IHe; eassumption. }
      intros [x C] w. eapply pre_existential; intros S2.
      eapply pre_curry_l; intros Hcvt.
      eapply bind_triple. eapply get_named_fresh.
      intros y w'. eapply return_triple.
      intros _ s0 [Hy [_ Hfr]].
      eexists. split; [econstructor; [reflexivity | exact Hcvt | exact Hy] | exact Hfr].

    - (* tFix mfix idx — requires careful set/context threading *)
      admit.

    - (* tCoFix *) rewrite HnoCoFix in Hwf. discriminate.

    - (* tPrim p *)
      simpl.
      destruct (trans_prim_val p) as [pv |] eqn:Hpv.
      + eapply bind_triple. eapply get_named_str_fresh.
        intros x w. eapply return_triple.
        intros _ s0 [Hx [_ [_ Hfr]]].
        eexists. split; [econstructor; [exact Hpv | exact Hx] | exact Hfr].
      + (* Arrays — need contradiction from wellformed *)
        admit.

    - (* tLazy *) rewrite HnoLazy in Hwf. discriminate.
    - (* tForce *) rewrite HnoLazy in Hwf. discriminate.
  Admitted.

End Corresp.
