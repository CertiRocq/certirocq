(* Correspondence between monadic convert_anf and relational anf_cvt_rel *)

From Stdlib Require Import ZArith.ZArith NArith.NArith Lists.List micromega.Lia Arith
     Ensembles Relations.Relation_Definitions.
From MetaRocq.Erasure Require Import EAst EGlobalEnv EWellformed EInduction EPrimitive
     ErasureFunction.
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
From CertiRocq.LambdaBox_to_LambdaANF Require Import common ANF fuel_sem wf anf_util.

Import ListNotations.
Import Monad.MonadNotation.
Open Scope monad_scope.
Open Scope bs_scope.


(* [term_ind_fix_body] is now in common.v *)

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
          (Hblocks : cstr_as_blocks = true)
          (HnoArray : has_primarray = false).

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

  (* Helper: mfix correspondence from per-body IH.
     Hall gives P on the lambda BODY (not the whole lambda),
     matching term_ind_fix_body's tFix case. *)
  Lemma anf_cvt_mfix_corresp :
    forall mfix fnames idx vn vm
      (Hall : All (fun d : EAst.def EAst.term =>
        match EAst.dbody d with
        | EAst.tLambda _ e1 =>
          forall vn vm S0
            (Hwf : wellformed Σ (List.length vn) e1 = true)
            (Hvm : var_map_correct vm vn),
          {{ fun _ s => fresh S0 (next_var (fst s)) }}
            convert_anf' e1 vm
          {{ fun _ s p s' => let '(r, C) := p in
             exists S', anf_cvt_rel func_tag default_tag tgm cmap S0 e1 vn S' C r /\
             fresh S' (next_var (fst s')) }}
        | _ => True
        end) mfix)
      (Hlen : List.length fnames = List.length mfix)
      (Hwf_mfix : forallb (fun d => isLambda (EAst.dbody d)) mfix = true)
      (Hwf_bodies : forallb (test_def (wellformed Σ (List.length vn))) mfix = true)
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
    induction mfix as [| d mfix' IHmfix];
    intros fnames idx vn vm Hall Hlen Hwf_mfix Hwf_bodies Hvm S0.
    - (* nil *)
      destruct fnames; [| simpl in Hlen; congruence].
      simpl. eapply return_triple. intros _ s Hfr.
      eexists. split; [econstructor |].
      split; [intros f Hf; destruct idx; discriminate | exact Hfr].
    - (* cons *)
      destruct fnames as [| f_name rest]; [simpl in Hlen; congruence |].
      simpl in Hlen.
      simpl in Hwf_mfix. apply Bool.andb_true_iff in Hwf_mfix as [Hislam Hwf_mfix'].
      simpl in Hwf_bodies.
      apply Bool.andb_true_iff in Hwf_bodies as [Hwf_d Hwf_bodies'].
      (* d.(dbody) must be a tLambda *)
      destruct (EAst.dbody d) eqn:Hbody; simpl in Hislam; try discriminate.
      (* Extract wellformed for body t *)
      unfold test_def in Hwf_d. rewrite Hbody in Hwf_d. simpl in Hwf_d.
      apply Bool.andb_true_iff in Hwf_d as [_ Hwf_t].
      (* Extract IH for body from All *)
      inversion Hall as [| ? ? IH_hd IH_tl]; subst.
      rewrite Hbody in IH_hd.
      simpl. rewrite Hbody.
      (* Step 1: allocate argument variable x *)
      eapply bind_triple. eapply get_named_fresh.
      intros x w. eapply pre_curry_l; intros Hx.
      eapply pre_strenghtening. { intros ? ? [_ Hfr]. exact Hfr. }
      (* Step 2: convert body t with extended vm *)
      eapply bind_triple.
      { eapply (IH_hd (x :: vn)).
        - exact Hwf_t.
        - eapply var_map_correct_cons. exact Hvm. }
      intros [r1 C1] w'. eapply pre_existential; intros S2.
      eapply pre_curry_l; intros Hcvt_body.
      (* Step 3: recurse on remaining mfix *)
      eapply bind_triple.
      { eapply (IHmfix rest); try eassumption. lia. }
      intros [fi defs'] w''.
      eapply pre_existential; intros S3.
      eapply pre_curry_l; intros Hcvt_rest.
      eapply pre_curry_l; intros Hfi_eq.
      eapply return_triple. intros _ s Hfr.
      eexists. split; [| split].
      + eapply anf_Mfix_cons; [exact Hbody | exact Hx | exact Hcvt_body |].
        exact Hcvt_rest.
      + intros f Hf. destruct idx.
        * simpl in Hf. congruence.
        * eapply Hfi_eq. exact Hf.
      + exact Hfr.
  Qed.

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
    intros e. induction e using term_ind_fix_body;
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

    - (* tFix mfix idx *)
      simpl.
      (* Decompose wellformed: has_tFix && forallb isLambda && wf_fix_gen *)
      apply Bool.andb_true_iff in Hwf as [Hwf_lhs Hwf_fix].
      apply Bool.andb_true_iff in Hwf_lhs as [_ Hwf_lam].
      (* wf_fix_gen gives: idx < length mfix && forallb test_def mfix *)
      (* We need to extract these from Hwf_fix *)
      (* Step 1: add_fix_names *)
      eapply bind_triple. { eapply add_fix_names_spec. exact Hvm. }
      intros [names vm'] w.
      eapply pre_curry_l; intros Hnd.
      eapply pre_curry_l; intros Hlen.
      eapply pre_curry_l; intros Hsub.
      eapply pre_curry_l; intros Hvm'.
      (* Step 2: convert_anf_mfix *)
      eapply bind_triple.
      { eapply (anf_cvt_mfix_corresp _ _ _ (List.app (List.rev names) vn));
          [exact X | exact Hlen | exact Hwf_lam | |exact Hvm'].
        (* wellformed bodies: need forallb (test_def (wellformed Σ (length (rev names ++ vn)))) mfix *)
        (* Extract forallb test_def from Hwf_fix *)
        unfold wf_fix, wf_fix_gen in Hwf_fix.
        apply Bool.andb_true_iff in Hwf_fix as [_ Hwf_bodies].
        rewrite app_length, rev_length, Hlen. exact Hwf_bodies. }
      intros [fi defs] w'.
      eapply pre_existential; intros S2.
      eapply pre_curry_l; intros Hcvt_mfix.
      eapply pre_curry_l; intros Hfi_eq.
      eapply return_triple. intros _ s Hfr.
      (* Determine fi from Hfi_eq *)
      destruct (nth_error names idx) as [f_res |] eqn:Hnth.
      2:{ exfalso. apply nth_error_None in Hnth.
          (* idx < length names follows from wf_fix *)
          unfold wf_fix, wf_fix_gen in Hwf_fix.
          apply Bool.andb_true_iff in Hwf_fix as [Hidx _].
          apply Nat.ltb_lt in Hidx. lia. }
      assert (fi = f_res) as -> by (apply Hfi_eq; reflexivity).
      eexists. split; [| exact Hfr].
      eapply anf_Fix; [exact Hsub | exact Hnd | exact Hlen | exact Hcvt_mfix |].
      exact Hnth.

    - (* tCoFix *) rewrite HnoCoFix in Hwf. discriminate.

    - (* tPrim p *)
      simpl.
      destruct (trans_prim_val p) as [pv |] eqn:Hpv.
      + eapply bind_triple. eapply get_named_str_fresh.
        intros x w. eapply return_triple.
        intros _ s0 [Hx [_ [_ Hfr]]].
        eexists. split; [econstructor; [exact Hpv | exact Hx] | exact Hfr].
      + (* Arrays: trans_prim_val = None only for primArrayModel.
           wellformed requires has_prim p = true, but has_primarray = false. *)
        exfalso.
        (* p is a prim_val with primArrayModel *)
        destruct p as [tag model].
        destruct model; simpl in Hpv; try discriminate.
        (* model = primArrayModel, so has_prim = has_primarray = false *)
        unfold has_prim in Hwf. simpl in Hwf. rewrite HnoArray in Hwf. discriminate.

    - (* tLazy *) rewrite HnoLazy in Hwf. discriminate.
    - (* tForce *) rewrite HnoLazy in Hwf. discriminate.
  Qed.

  (** * Auxiliary definitions *)

  Fixpoint pos_seq (start : var) (n : nat) : list positive :=
    match n with
    | 0%nat => []
    | S n => start :: (pos_seq (start + 1)%positive n)
    end.

  Lemma pos_seq_len start n :
    List.length (pos_seq start n) = n.
  Proof.
    revert start. induction n; intros start; simpl; [reflexivity | rewrite IHn; reflexivity].
  Qed.

  Lemma pos_seq_In start n x :
    List.In x (pos_seq start n) ->
    (start <= x <= Pos.of_nat (Pos.to_nat start + n)%nat)%positive.
  Proof.
    revert start. induction n; intros start Hin.
    - inv Hin.
    - inv Hin; [lia |]. eapply IHn in H. lia.
  Qed.

  Lemma pos_seq_NoDup start n :
    NoDup (pos_seq start n).
  Proof.
    revert start; induction n; intros start; simpl.
    - constructor.
    - constructor; [| eauto].
      intros Hc. eapply pos_seq_In in Hc. lia.
  Qed.

  Lemma set_lists_Forall2 {A} xs (vs : list A) rho rho' :
    set_lists xs vs rho = Some rho' ->
    NoDup xs ->
    Forall2 (fun x v => M.get x rho' = Some v) xs vs.
  Proof.
    revert vs rho rho'; induction xs; intros ys rho rho' Hset Hnd;
      destruct ys; simpl in *; try congruence.
    - constructor.
    - destruct (set_lists xs ys rho) eqn:Hset'; try congruence.
      inv Hset. constructor.
      + rewrite M.gss. reflexivity.
      + eapply Forall2_monotonic_strong.
        2:{ eapply IHxs; eauto. inv Hnd. eassumption. }
        intros. rewrite M.gso. eassumption.
        intros Heq; subst. inv Hnd; eauto.
  Qed.

  (** * Existence of relational derivation *)

  (* Given a well-formed term, there exists a relational derivation.
     Proved by running convert_anf and applying correspondence. *)
  Lemma anf_rel_exists e xs m :
    wellformed Σ (List.length xs) e = true ->
    exists C r S',
      anf_cvt_rel func_tag default_tag tgm cmap
        (fun x => (m <= x)%positive) e xs S' C r.
  Proof.
    intros Hwf.
    set (S0 := fun x => (m <= x)%positive).
    set (vm := List.fold_right (fun v vm' => add_var_name vm' v) new_var_map xs).

    assert (Hvm : var_map_correct vm xs).
    { unfold vm. rewrite <- (List.app_nil_r xs) at 2.
      apply var_map_correct_fold_right. apply var_map_correct_nil. }

    set (comp_d := pack_data m 1%positive 1%positive 1%positive
                             (M.empty _) (M.empty _) (M.empty _) (M.empty _) []).

    destruct (runState (convert_anf' e vm) tt (comp_d, tt)) as [cvt_res cvt_st] eqn:Hrun.

    assert (Hf : fresh S0 m).
    { unfold S0, fresh, Ensembles.In. lia. }

    pose proof (anf_cvt_exp_corresp e xs vm S0 Hwf Hvm) as Hcorresp.
    unfold triple in Hcorresp.
    specialize (Hcorresp tt (comp_d, tt) Hf).
    rewrite Hrun in Hcorresp.
    destruct cvt_res as [msg | [r0 C0]].
    - contradiction.
    - simpl in Hcorresp. destruct Hcorresp as [S' [Hrel Hfr]].
      exists C0, r0, S'. exact Hrel.
  Qed.

  (** Existence of [anf_cvt_rel_mfix] for well-formed fixpoint bodies.
      Proved by running the monadic [convert_anf_mfix] and applying
      [anf_cvt_mfix_corresp]. *)
  Lemma anf_cvt_rel_mfix_exists mfix fnames vn m :
    List.length fnames = List.length mfix ->
    forallb (fun d => EAst.isLambda (EAst.dbody d)) mfix = true ->
    forallb (test_def (wellformed Σ (List.length vn))) mfix = true ->
    exists fdefs S',
      anf_cvt_rel_mfix func_tag default_tag tgm cmap
        (fun z => (m <= z)%positive) mfix vn fnames S' fdefs.
  Proof.
    intros Hlen Hlam Hwf_bodies.
    set (S0 := fun z => (m <= z)%positive).
    set (vm := List.fold_right (fun v vm' => add_var_name vm' v) new_var_map vn).
    assert (Hvm : var_map_correct vm vn).
    { unfold vm. rewrite <- (List.app_nil_r vn) at 2.
      apply var_map_correct_fold_right. apply var_map_correct_nil. }
    (* Build All hypothesis from anf_cvt_exp_corresp *)
    assert (Hall : All (fun d : EAst.def EAst.term =>
      match EAst.dbody d with
      | EAst.tLambda _ e1 =>
        forall vn0 vm0 S1
          (Hwf : wellformed Σ (List.length vn0) e1 = true)
          (Hvm0 : var_map_correct vm0 vn0),
        {{ fun _ s => fresh S1 (next_var (fst s)) }}
          convert_anf' e1 vm0
        {{ fun _ s p s' => let '(r, C) := p in
           exists S', anf_cvt_rel func_tag default_tag tgm cmap S1 e1 vn0 S' C r /\
                      fresh S' (next_var (fst s')) }}
      | _ => True
      end) mfix).
    { clear Hlen Hvm Hwf_bodies vm S0.
      induction mfix as [| d mfix' IHm]; [constructor |].
      simpl in Hlam. apply Bool.andb_true_iff in Hlam as [Hlam_d Hlam_rest].
      constructor.
      - destruct (EAst.dbody d) eqn:Hbd; try exact I.
        intros vn0 vm0 S1 Hwf0 Hvm0.
        exact (anf_cvt_exp_corresp t vn0 vm0 S1 Hwf0 Hvm0).
      - exact (IHm Hlam_rest). }
    (* Run the monadic computation *)
    set (comp_d := pack_data m 1%positive 1%positive 1%positive
                             (M.empty _) (M.empty _) (M.empty _) (M.empty _) []).
    destruct (runState (convert_anf_mfix func_tag convert_anf' mfix fnames 0 vm)
                tt (comp_d, tt)) as [cvt_res cvt_st] eqn:Hrun.
    assert (Hf : fresh S0 m).
    { unfold S0, fresh, Ensembles.In. lia. }
    pose proof (anf_cvt_mfix_corresp mfix fnames 0 vn vm Hall Hlen Hlam Hwf_bodies Hvm S0)
      as Hspec.
    unfold triple in Hspec.
    specialize (Hspec tt (comp_d, tt) Hf).
    rewrite Hrun in Hspec.
    destruct cvt_res as [msg | [fi fdefs]].
    - contradiction.
    - simpl in Hspec. destruct Hspec as [S' [Hrel [_ Hfr]]].
      exists fdefs, S'. exact Hrel.
  Qed.

End Corresp.


(* ================================================================= *)
(** * Helpers for ValRelExists                                        *)
(* ================================================================= *)

(** Upper bound on cmap variable values (for freshness arguments). *)
Fixpoint max_cmap_var (cm : const_map) : positive :=
  match cm with
  | [] => 1%positive
  | (_, v) :: cm' => Pos.max v (max_cmap_var cm')
  end.

Lemma pos_seq_lt start n x :
  List.In x (pos_seq start n) ->
  (x < start + Pos.of_succ_nat n)%positive.
Proof.
  revert start. induction n; intros start Hin.
  - inv Hin.
  - simpl in Hin. destruct Hin as [<- | Hin].
    + lia.
    + specialize (IHn (start + 1)%positive Hin). lia.
Qed.

Lemma max_cmap_var_bound cm v :
  cmap_vars cm v -> (v <= max_cmap_var cm)%positive.
Proof.
  intros [s Hlk]. induction cm as [| [k' v'] cm' IH].
  - simpl in Hlk. discriminate.
  - simpl in Hlk. destruct (eq_kername s k').
    + injection Hlk as <-. simpl. lia.
    + simpl. specialize (IH Hlk). lia.
Qed.


Section ValRelExists.

  Context (func_tag default_tag : positive)
          (prim_map : M.t primitive)
          (tgm : conId_map)
          (prims : list (primitive * positive))
          (cmap : const_map)
          {efl : EWellformed.EEnvFlags}
          (Σ : EAst.global_context)
          (box_dc : dcon)
          {src_trace : Type}
          {Hf_src : @LambdaBox_resource nat}
          {Ht_src : @LambdaBox_resource src_trace}.

  Context (Hglob_term : globals_terminate Σ box_dc).
  Context (Hwf_glob : EWellformed.wf_glob Σ).

  (* Pipeline flags needed for anf_rel_exists *)
  Context (HnoVar : has_tVar = false)
          (HnoEvar : has_tEvar = false)
          (HnoCoFix : has_tCoFix = false)
          (HnoLazy : has_tLazy_Force = false)
          (Hblocks : cstr_as_blocks = true)
          (HnoArray : has_primarray = false).

  Context (no_prims : forall s, find_prim prims s = None).
  Context (cmap_complete : forall s d,
    lookup_constant Σ s = Some d -> lookup_const cmap s <> None).
  Context (cmap_sound : forall k v,
    lookup_const cmap k = Some v ->
    exists decl body,
      declared_constant Σ k decl /\ decl.(EAst.cst_body) = Some body).
  Context (cmap_nodup_vals : NoDup (map snd cmap)).

  Let anf_val_rel' := anf_val_rel func_tag default_tag tgm cmap Σ box_dc.

  (* Convert anf_cvt_rel_mfix to anf_fix_rel.
     Proved here since anf_correct.v (which has this lemma) imports anf_corresp.v. *)
  Lemma anf_cvt_rel_mfix_to_fix_rel fnames_all names0 :
    forall mfix S fnames S' fdefs,
      anf_cvt_rel_mfix func_tag default_tag tgm cmap
        S mfix (List.rev fnames_all ++ names0) fnames S' fdefs ->
      Disjoint _ S (FromList fnames_all :|: FromList names0) ->
      anf_fix_rel func_tag default_tag tgm cmap
        fnames_all names0 S fnames mfix fdefs S'.
  Proof.
    intros mfix. induction mfix; intros S fnames S' fdefs Hcvt Hdis.
    - inv Hcvt. constructor.
    - inv Hcvt.
      eapply anf_fix_fcons.
      1: eassumption.
      1: exact Hdis.
      1: eassumption.
      1: apply Included_refl.
      1: apply Included_refl.
      1: eassumption.
      eapply IHmfix; [eassumption |].
      eapply Disjoint_Included_l; [| exact Hdis].
      eapply Included_trans.
      + eapply (anf_cvt_exp_subset func_tag default_tag tgm cmap). eassumption.
      + eapply Setminus_Included.
  Qed.

  (* well_formed_val is monotone w.r.t. extending Σ *)
  Lemma well_formed_val_extends Σ_small Σ_big v :
    EWellformed.wf_glob Σ_big ->
    EGlobalEnv.extends Σ_small Σ_big ->
    well_formed_val Σ_small v ->
    well_formed_val Σ_big v.
  Proof.
    intros Hwf_big Hext Hwf_v. revert Hwf_v.
    induction v using value_ind'; intros Hwf_v; inv Hwf_v.
    - (* Con_v *)
      constructor. clear -H H1.
      induction H; inv H1; constructor; auto.
    - (* Clos_v *)
      constructor.
      + clear -H H2.
        induction H; inv H2; constructor; auto.
      + eapply EWellformed.extends_wellformed; eassumption.
    - (* ClosFix_v *)
      econstructor.
      + clear -H H3.
        induction H; inv H3; constructor; auto.
      + assumption.
      + eapply Forall_impl; [| eassumption]. intros d0 [Hlam Hwf_b]. split;
          [exact Hlam | eapply EWellformed.extends_wellformed; eassumption].
  Qed.

  (* If e is wellformed w.r.t. Σ0 and k ∈ kn_deps e, then k is declared in Σ0.
     Follows from wellformed checking lookup_constant for tConst,
     lookup_constructor for tConstruct, etc. Proof by induction on e. *)
  Lemma kn_deps_declared Σ0 n e k :
    wellformed Σ0 n e = true ->
    kn_deps e k ->
    List.In k (map fst Σ0).
  Proof.
    intros Hwf Hkd. exact (@term_global_deps_fresh _ Σ0 n e Hwf k Hkd).
  Qed.

  (* Generalized: all global bodies are wellformed w.r.t. their context *)
  Lemma wf_glob_globals_wellformed_gen Σ0 :
    EWellformed.wf_glob Σ0 ->
    forall k decl body,
      declared_constant Σ0 k decl ->
      decl.(EAst.cst_body) = Some body ->
      wellformed Σ0 0 body = true.
  Proof.
    induction 1 as [| kn0 d0 Σ0' Hwf0 IH Hwd Hfr].
    - intros ? ? ? Hdecl. unfold declared_constant in Hdecl. discriminate.
    - intros k0 decl0 body0 Hdecl Hbody.
      unfold declared_constant in Hdecl. simpl in Hdecl.
      assert (Hwf_full : EWellformed.wf_glob ((kn0, d0) :: Σ0')).
      { exact (EWellformed.wf_glob_cons _ _ _ Hwf0 Hwd Hfr). }
      eapply (EWellformed.extends_wellformed Hwf_full
                (EWellformed.extends_fresh _ _ _ Hfr)).
      destruct (ReflectEq.eqb k0 kn0) eqn:Hek.
      + injection Hdecl as Heq. subst d0. simpl in Hwd. rewrite Hbody in Hwd. exact Hwd.
      + exact (IH _ _ _ Hdecl Hbody).
  Qed.

  Lemma wf_glob_globals_wellformed :
    forall k decl body,
      declared_constant Σ k decl ->
      decl.(EAst.cst_body) = Some body ->
      wellformed Σ 0 body = true.
  Proof. exact (wf_glob_globals_wellformed_gen Σ Hwf_glob). Qed.

  (** Every well-formed source value has a related ANF target value.
      Proved by well-founded induction on wf_glob (outer) combined with
      structural induction on values (inner). The wf_glob induction resolves
      the circular dependency in global_env_rel'. *)
  Lemma anf_val_rel_exists v :
    well_formed_val Σ v ->
    exists v', anf_val_rel' v v'.
  Proof.
    (* Strengthen: induct on wf_glob varying the well-formedness context.
       anf_val_rel always uses the full Σ; only well_formed_val varies. *)
    cut (forall Σ0, EWellformed.wf_glob Σ0 -> EGlobalEnv.extends Σ0 Σ ->
      forall v0, well_formed_val Σ0 v0 ->
      exists v', anf_val_rel' v0 v').
    { intro Hgen. apply (Hgen Σ Hwf_glob). intros ? ? Hlk. exact Hlk. }
    intros Σ0 Hwf0.
    induction Hwf0 as [| kn d Σ' Hwf' IH Hwfd Hfresh].

    (* ---- Base: Σ0 = [] ---- *)
    - intros Hext v0 Hwf_v0.
      induction v0 using value_ind'; intros; inv Hwf_v0.
      + (* Con_v *)
        assert (Hvs' : exists vs', Forall2 anf_val_rel' vs vs').
        { clear -H H1. induction vs.
          + exists []. constructor.
          + inv H. inv H1. destruct (H3 H2) as [v' Hv'].
            destruct (IHvs H4 H5) as [vs' Hvs'].
            exists (v' :: vs'). constructor; assumption. }
        destruct Hvs' as [vs' Hvs'].
        eexists. eapply anf_rel_Con; [exact Hvs' | reflexivity].
      + (* Clos_v — same structure as step case, global_env_rel' vacuous *)
        admit.
      + (* ClosFix_v — similar to Clos_v base *)
        admit.

    (* ---- Step: Σ0 = (kn, d) :: Σ' ---- *)
    - intros Hext v0 Hwf_v0.
      (* Establish IH for Σ' *)
      assert (Hext' : EGlobalEnv.extends Σ' Σ).
      { intros k' d' Hlk. apply Hext. simpl.
        destruct (ReflectEq.eqb k' kn) eqn:Heq; [| exact Hlk].
        apply ReflectEq.eqb_eq in Heq. subst k'.
        exfalso. exact (EGlobalEnv.lookup_env_Some_fresh Hlk Hfresh). }
      specialize (IH Hext').

      induction v0 using value_ind'; intros; inv Hwf_v0.
      + (* Con_v *)
        assert (Hvs' : exists vs', Forall2 anf_val_rel' vs vs').
        { clear -H H1. induction vs.
          + exists []. constructor.
          + inv H. inv H1. destruct (H3 H2) as [v' Hv'].
            destruct (IHvs H4 H5) as [vs' Hvs'].
            exists (v' :: vs'). constructor; assumption. }
        destruct Hvs' as [vs' Hvs'].
        eexists. eapply anf_rel_Con; [exact Hvs' | reflexivity].

      + (* Clos_v *)
        (* Step 1: ANF values for captured environment *)
        assert (Hvs' : exists vs', Forall2 anf_val_rel' vs vs').
        { clear -H H2. induction vs.
          + exists []. constructor.
          + inv H. inv H2. destruct (H3 H1) as [v' Hv'].
            destruct (IHvs H4 H5) as [vs' Hvs'].
            exists (v' :: vs'). constructor; assumption. }
        destruct Hvs' as [vs' Hvs'].

        (* Step 2: Fresh names *)
        set (base := (max_cmap_var cmap + 1)%positive).
        set (x := base).
        set (f := (base + 1)%positive).
        set (names := pos_seq (base + 2)%positive (List.length vs)).
        set (next_id := (base + Pos.of_succ_nat (List.length vs + 2))%positive).

        (* Step 3: Build global target env using wf_glob IH.
           For each k ∈ kn_deps e: evaluate in Σ, get src_v_k,
           eval_preserves_wf_restricted gives well_formed_val Σ' src_v_k,
           then IH gives anf_val_rel' src_v_k v'. *)
        assert (Hglob : exists rho_g,
          global_env_rel func_tag default_tag tgm cmap Σ box_dc
            (kn_deps e) rho_g).
        { (* Build rho_g by iterating over cmap.
             For each (k0, v0) in cmap: if k0 is declared in Σ0 with body,
             get eval result, eval_wf_restricted gives wf Σ', IH gives anf_val. *)
          unfold global_env_rel, global_env_rel'.
          assert (Hbuild : forall cm, NoDup (map snd cm) ->
            exists rho_g, forall k v_g,
            kn_deps e k -> lookup_const cm k = Some v_g ->
            exists decl body anf_v,
              declared_constant Σ k decl /\
              EAst.cst_body decl = Some body /\
              M.get v_g rho_g = Some anf_v /\
              (forall src_v f0 t0,
                eval_env_fuel Σ box_dc [] body (Val src_v) f0 t0 ->
                anf_val_rel' src_v anf_v)).
          { induction cm as [| [k0 v0] cm' IHcm]; intros Hnd_cm.
            - (* cm = [] *) exists (M.empty val). intros. discriminate.
            - (* cm = (k0, v0) :: cm' *)
              simpl in Hnd_cm. inversion Hnd_cm as [| ? ? Hv0_notin Hnd_cm']. subst.
              destruct (IHcm Hnd_cm') as [rho_g' Hrho_g'].
              (* Check if k0 is declared in Σ0 = (kn,d)::Σ' with a body.
                 Using Σ0 (not Σ) so we can derive wellformed Σ' 0 body0. *)
              destruct (EGlobalEnv.lookup_env ((kn, d) :: Σ') k0) as [[cb | ?] |] eqn:Hlk0;
                [destruct (EAst.cst_body cb) as [body0 |] eqn:Hbody0 | |].
              + (* k0 is a constant in Σ0 with body body0 *)
                (* declared_constant Σ k0 cb — via extends *)
                assert (Hdecl0 : declared_constant Σ k0 cb) by (apply Hext; exact Hlk0).
                (* Get eval result from globals_terminate *)
                destruct (Hglob_term k0 cb body0 Hdecl0 Hbody0)
                  as [src_v0 [f0 [t0 Heval0]]].
                (* wellformed Σ' 0 body0 — from wf_glob Σ0 *)
                assert (Hwf_body0 : wellformed Σ' 0 body0 = true).
                { simpl in Hlk0. destruct (ReflectEq.eqb k0 kn) eqn:Hkeq0.
                  - (* k0 = kn: body0 comes from d *)
                    injection Hlk0 as Heq_d. rewrite Heq_d in Hwfd.
                    simpl in Hwfd. rewrite Hbody0 in Hwfd. exact Hwfd.
                  - (* k0 ∈ Σ': use wf_glob_globals_wellformed_gen *)
                    exact (wf_glob_globals_wellformed_gen Σ' Hwf' k0 cb body0 Hlk0 Hbody0). }
                (* eval_preserves_wf_restricted: well_formed_val Σ' src_v0 *)
                assert (Hwf_src0 : well_formed_val Σ' src_v0).
                { eapply eval_preserves_wf_restricted;
                    [exact wf_glob_globals_wellformed
                    | exact Hwf' | exact Hext' | constructor | exact Hwf_body0
                    | exact Heval0]. }
                (* Get ANF value from wf_glob IH *)
                destruct (IH src_v0 Hwf_src0) as [anf_v0 Hrel0].
                (* Build extended map *)
                exists (M.set v0 anf_v0 rho_g').
                intros k v_g Hkdep Hlk.
                simpl in Hlk. destruct (eq_kername k k0) eqn:Hkeq.
                * (* k = k0 *)
                  apply ReflectEq.eqb_eq in Hkeq. subst k0.
                  injection Hlk as <-.
                  exists cb, body0, anf_v0.
                  split; [exact Hdecl0 |]. split; [exact Hbody0 |].
                  split; [apply M.gss |].
                  intros src_v' f' t' Heval'.
                  assert (src_v' = src_v0)
                    by (eapply eval_val_det; eassumption).
                  subst src_v'. exact Hrel0.
                * (* k ≠ k0: delegate to IH for cm' *)
                  destruct (M.elt_eq v_g v0) as [Heq_v | Hneq_v].
                  -- (* v_g = v0: collision — impossible by NoDup (map snd cm).
                        lookup_const cm' k = Some v0 implies In v0 (map snd cm'),
                        but NoDup gives ~ In v0 (map snd cm'). *)
                     subst v0. exfalso. apply Hv0_notin.
                     clear -Hlk. induction cm' as [| [k' v'] cm'' IH].
                     ++ discriminate.
                     ++ simpl in Hlk. destruct (eq_kername k k').
                        ** injection Hlk as <-. left. reflexivity.
                        ** right. exact (IH Hlk).
                  -- (* v_g ≠ v0: standard case *)
                     specialize (Hrho_g' k v_g Hkdep Hlk).
                     destruct Hrho_g' as [decl' [body' [anf_v' [Hd [Hb [Hg Hr]]]]]].
                     exists decl', body', anf_v'.
                     split; [exact Hd |]. split; [exact Hb |].
                     split; [| exact Hr].
                     rewrite M.gso; [exact Hg | exact Hneq_v].
              + (* k0 constant but no body in Σ0: skip *)
                exists rho_g'. intros k v_g Hkdep Hlk. simpl in Hlk.
                destruct (eq_kername k k0) eqn:Hkeq;
                  [| exact (Hrho_g' k v_g Hkdep Hlk)].
                (* k = k0 but no body — contradiction via cmap_sound on full cmap *)
                exfalso. admit.
              + (* k0 is InductiveDecl in Σ0: skip *)
                exists rho_g'. intros k v_g Hkdep Hlk. simpl in Hlk.
                destruct (eq_kername k k0) eqn:Hkeq;
                  [| exact (Hrho_g' k v_g Hkdep Hlk)].
                (* k = k0 but InductiveDecl — contradiction via cmap_sound *)
                exfalso. admit.
              + (* k0 not in Σ0: skip *)
                exists rho_g'. intros k v_g Hkdep Hlk. simpl in Hlk.
                destruct (eq_kername k k0) eqn:Hkeq;
                  [| exact (Hrho_g' k v_g Hkdep Hlk)].
                apply ReflectEq.eqb_eq in Hkeq. subst k0. injection Hlk as <-.
                (* k not in Σ0, but kn_deps e k and wellformed Σ0 ... e
                   requires In k (map fst Σ0). Contradiction with lookup_env = None. *)
                exfalso.
                assert (Hin := kn_deps_declared _ _ e k H4 Hkdep).
                (* In k (map fst Σ0) but lookup_env Σ0 k = None *)
                clear -Hin Hlk0.
                induction ((kn, d) :: Σ') as [| [k' d'] Σ0' IH]; [exact Hin |].
                simpl in Hlk0. destruct (ReflectEq.eqb k k') eqn:Heq.
                * discriminate.
                * simpl in Hin. destruct Hin as [Heq_k | Hin].
                  -- subst. rewrite ReflectEq.eqb_refl in Heq. discriminate.
                  -- exact (IH Hlk0 Hin).
          }
          exact (Hbuild cmap cmap_nodup_vals). }
        destruct Hglob as [rho_g Hglob_rel].

        (* Step 4: Build target environment *)
        edestruct (@set_lists_length3 val) with
          (rho := rho_g) (vs := vs') (xs := names) as [rho Hset].
        { rewrite <- (Forall2_length _ _ _ Hvs'). unfold names. eapply pos_seq_len. }

        (* Step 5: Get ANF conversion of body *)
        assert (Hwf_e_full : wellformed Σ (S (Datatypes.length vs)) e = true).
        { eapply EWellformed.extends_wellformed; [exact Hwf_glob | exact Hext |exact H4]. }
        edestruct (anf_rel_exists func_tag default_tag prim_map tgm prims cmap Σ
          HnoVar HnoEvar HnoCoFix HnoLazy Hblocks HnoArray no_prims cmap_complete
          e (x :: names) next_id) as [C1 [r1 [S2 Hcvt]]].
        { simpl. subst names. rewrite pos_seq_len. exact Hwf_e_full. }

        (* Step 6: Construct the ANF closure value *)
        eexists.
        eapply anf_rel_Clos with
          (x := x) (f := f) (rho := rho) (names := names)
          (S1 := fun z => (next_id <= z)%positive)
          (S2 := S2) (C1 := C1) (r1 := r1).

        * (* anf_env_rel' *)
          unfold anf_env_rel'.
          assert (Hget : Forall2 (fun n v' => M.get n rho = Some v') names vs')
            by (eapply set_lists_Forall2; [exact Hset | eapply pos_seq_NoDup]).
          { assert (Hcombine : forall vs0 vs0' ns0,
              Forall2 anf_val_rel' vs0 vs0' ->
              Forall2 (fun n v' => M.get n rho = Some v') ns0 vs0' ->
              Forall2 (fun v n => exists v', M.get n rho = Some v' /\
                        anf_val_rel' v v') vs0 ns0).
            { intros vs0 vs0' ns0 Hvs0. revert ns0.
              induction Hvs0 as [| sv sv' svs svs' Hrel Hvs_tl IHc]; intros ns0 Hget0.
              - inv Hget0. constructor.
              - destruct ns0 as [| n ns']; [inv Hget0 |]. inv Hget0.
                constructor.
                + eexists. split; eassumption.
                + eapply IHc. eassumption. }
            exact (Hcombine vs vs' names Hvs' Hget). }
        * eapply NoDup_env_consistent. eapply pos_seq_NoDup.
        * (* cmap_consistent — vacuous: names are above max_cmap_var *)
          intros i y k0' decl body Hnth Hlk' _ _.
          exfalso.
          assert (Hy_in : List.In y names) by (eapply nth_error_In; exact Hnth).
          unfold names in Hy_in. eapply pos_seq_In in Hy_in.
          destruct Hy_in as [Hy_lo _].
          assert (Hbd : (y <= max_cmap_var cmap)%positive)
            by (eapply max_cmap_var_bound; exists k0'; exact Hlk').
          unfold base in Hy_lo. lia.
        * admit. (* Disjoint (x |: ...) S1 *)
        * admit. (* Disjoint (cmap_vars cmap) S1 *)
        * admit. (* ~ cmap_vars cmap x *)
        * admit. (* ~ cmap_vars cmap f *)
        * admit. (* ~ x ∈ f |: FromList names *)
        * admit. (* ~ f ∈ FromList names *)
        * exact Hcvt.
        * admit. (* global_env_rel' *)

      + (* ClosFix_v *)
        admit.
  Admitted.

End ValRelExists.
