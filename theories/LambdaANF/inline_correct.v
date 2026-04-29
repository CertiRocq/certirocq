From Stdlib Require Import ZArith.ZArith Lists.List Strings.String Sets.Ensembles Classes.Morphisms micromega.Lia micromega.Zify.
Require Import compcert.lib.Maps compcert.lib.Coqlib.
Require Import LambdaANF.term LambdaANF.state LambdaANF.freshen LambdaANF.term_util LambdaANF.cps_show LambdaANF.ctx LambdaANF.inline LambdaANF.rename LambdaANF.identifiers
        LambdaANF.Ensembles_util LambdaANF.alpha_conv LambdaANF.functions LambdaANF.logical_relations LambdaANF.tactics LambdaANF.eval LambdaANF.map_util LambdaANF.inline_letapp
        LambdaANF.List_util LambdaANF.algebra.
Require Import Common.compM Common.Pipeline_utils Libraries.CpdtTactics Libraries.maps_util.
Require Import ExtLib.Structures.Monad.
Require Import ExtLib.Structures.MonadState.
Require Import ExtLib.Data.Monads.StateMonad.
From Stdlib Require Import Structures.OrdersEx.

Import MonadNotation.
Import ListNotations.
Open Scope monad_scope.
Open Scope ctx_scope.
Open Scope fun_scope.

Section Inline_Eq.

  Context (St : Type) (IH : InlineHeuristic St).

    Definition inline_fundefs (d j : nat) (sig sig' : subst) (fm : fun_map) :=
    (fix inline_fds (fds:fundefs) (s:St) : inlineM fundefs :=
       match fds with
       | Fcons f t xs e fds' =>
         let s' := update_inFun _ IH f t xs e sig s in
         let f' := apply_r sig' f in
         xs' <- get_fresh_names xs ;;
         e' <- inline_exp St IH d j e (set_list (combine xs xs') sig') (M.remove f fm) s' ;;
         fds'' <- inline_fds fds' s ;;
         ret (Fcons f' t xs' e' fds'')
       | Fnil => ret Fnil
       end).


    Definition inline_exp' (d j : nat) (e : exp) (sig : r_map) (fm:fun_map) (s:St) : inlineM exp :=
      match e with
      | Econstr x t ys e =>
        let ys' := apply_r_list sig ys in
        x' <- get_fresh_name x ;;
        e' <- inline_exp _ IH d j e (M.set x x' sig) fm s ;;
        ret (Econstr x' t ys' e')
      | Ecase v cl =>
        let v' := apply_r sig v in
        cl' <- (fix beta_list (br: list (ctor_tag*exp)) : inlineM (list (ctor_tag*exp)) :=
                  match br with
                  | nil => ret ( nil)
                  | (t, e)::br' =>
                    e' <- inline_exp _ IH d j e sig fm s ;;
                    br'' <- beta_list br';;
                    ret ((t, e')::br'')
                  end) cl;;
        ret (Ecase v' cl')
      | Eproj x t n y e =>
        let y' := apply_r sig y in
        x' <- get_fresh_name x ;;
        e' <- inline_exp _ IH d j e (M.set x x' sig) fm s ;;
        ret (Eproj x' t n y' e')
      | Eletapp x f t ys ec =>
        let f' := apply_r sig f in
        let ys' := apply_r_list sig ys in
        let '(s', s'' , inl_dec) := update_letApp _ IH f t ys' s in
        (* fstr <- get_pp_name f' ;; *)
        (* log_msg ("Application of " ++ fstr ++ " is " ++ (if inl_dec then else "not ") ++ "inlined") ;; *)
        (match (inl_dec, M.get f fm, d, j) with
         | (true, Some  (ft, xs, e), S d', S j') =>
           if (Nat.eqb (List.length xs) (List.length ys)) then
             let sig' := set_list (combine xs ys') sig  in
             x' <- get_fresh_name x ;;
             let '(j1, j2) := split_fuel j' in
             e' <- inline_exp _ IH d' j1 e sig' (M.remove f fm) s' ;;
             match inline_letapp e' x' with
             | Some (C, x') =>
               click ;;
               ec' <- inline_exp _ IH d' j2 ec (M.set x x' sig) fm s'' ;;
               ret (C |[ ec' ]|)
             | _ =>
               x' <- get_fresh_name x ;;
               ec' <- inline_exp _ IH d j ec (M.set x x' sig) fm s' ;;
               ret (Eletapp x' f' t ys' ec')
             end
           else
             x' <- get_fresh_name x ;;
             ec' <- inline_exp _ IH d j ec (M.set x x' sig) fm s' ;;
             ret (Eletapp x' f' t ys' ec')
         | _ =>
           x' <- get_fresh_name x ;;
           ec' <- inline_exp _ IH d j ec (M.set x x' sig) fm s' ;;
           ret (Eletapp x' f' t ys' ec')
         end)
      | Efun fds e =>
        let fm' := add_fundefs fds fm in
        let (s1, s2) := update_funDef _ IH fds sig s in
        let names := all_fun_name fds in
        names' <- get_fresh_names names ;;
        let sig' := set_list (combine names names') sig in
        fds' <- (fix inline_exp_fds (fds:fundefs) (s:St) : inlineM fundefs :=
                   match fds with
                   | Fcons f t xs e fds' =>
                     let s' := update_inFun _ IH f t xs e sig s in
                     let f' := apply_r sig' f in
                     xs' <- get_fresh_names xs ;;
                     e' <- inline_exp _ IH d j e (set_list (combine xs xs') sig') (M.remove f fm') s' ;;
                     fds'' <- inline_exp_fds fds' s ;;
                     ret (Fcons f' t xs' e' fds'')
                   | Fnil => ret Fnil
                   end) fds s1 ;;
        e' <- inline_exp _ IH d j e sig' fm' s2 ;;
        ret (Efun fds' e')
      | Eapp f t ys =>
        let f' := apply_r sig f in
        let ys' := apply_r_list sig ys in
        let (s', inl) := update_App _ IH f t ys' s in
        (match (inl, M.get f fm, d, j) with
         | (true, Some (ft, xs, e), S d', S j') =>
           if (Nat.eqb (List.length xs) (List.length ys))%bool then
             let sig' := set_list (combine xs ys') sig  in
             click ;;
             inline_exp _ IH d' j' e sig' (M.remove f fm) s'
           else
             ret (Eapp f' t ys')
         | _ =>
           ret (Eapp f' t ys')
         end)
      | Eprim x t ys e =>
        let ys' := apply_r_list sig ys in
        x' <- get_fresh_name x ;;
        e' <- inline_exp _ IH d j e (M.set x x' sig) fm s ;;
        ret (Eprim x' t ys' e')
      | Eprim_val x t e =>
        x' <- get_fresh_name x ;;
        e' <- inline_exp _ IH d j e (M.set x x' sig) fm s ;;
        ret (Eprim_val x' t e')
      | Ehalt x =>
        let x' := apply_r sig x in
        ret (Ehalt x')
      end.


    Lemma inline_exp_eq (d j : nat) (e : exp) (sig : r_map) (fm:fun_map) (s:St) :
      inline_exp _ IH d j e sig fm s = inline_exp' d j e sig fm s.
    Proof.
      destruct d; destruct e; try reflexivity.
    Qed.

End Inline_Eq.

(* get_fresh_name[s] specs *)


(** Spec for [get_fresh_name] *)
Lemma get_fresh_name_spec S y :
  {{ fun _ s => identifiers.fresh S (next_var (fst s)) }}
    get_fresh_name y
  {{ fun (r: unit) s x s' =>
       x \in S /\
       x \in Range (next_var (fst s)) (next_var (fst s')) /\
       (next_var (fst s) < next_var (fst s'))%positive /\
       identifiers.fresh (S \\ [set x]) (next_var (fst s'))
  }}.
Proof.
  unfold get_fresh_name.
  eapply bind_triple with (Q' := fun r w x w' => w = w' /\ fresh S (next_var (fst w'))).
  - eapply pre_post_mp_l.
    eapply post_weakening.  2:{ eapply get_state_spec. }
    intros. simpl in *. destructAll. split; eauto.
  - intros [b nenv] [c1 s1]. simpl.
    eapply post_weakening.
    2:{ eapply pre_strenghtening.
        2:{ eapply get_name'_spec. }
        intros; eauto. destructAll. eassumption. }

    intros; eauto. destructAll. eassumption.
Qed.

Lemma get_fresh_names_spec S ys :
  {{ fun _ s => identifiers.fresh S (next_var (fst s)) }}
    get_fresh_names ys
  {{ fun (r: unit) s xs s' =>
       NoDup xs /\ List.length xs = List.length ys /\
       FromList xs \subset S /\
       FromList xs \subset Range (next_var (fst s)) (next_var (fst s')) /\
       (next_var (fst s) <= next_var (fst s'))%positive /\
       identifiers.fresh (S \\ FromList xs) (next_var (fst s')) }}.
Proof.
  unfold get_fresh_names.
  eapply bind_triple with (Q' := fun r w x w' => w = w' /\ fresh S (next_var (fst w'))).
  - eapply pre_post_mp_l.
    eapply post_weakening.  2:{ eapply get_state_spec. }
    intros. simpl in *. destructAll. split; eauto.
  - intros [b nenv] [c1 s1]. simpl.
    eapply post_weakening.
    2:{ eapply pre_strenghtening.
        2:{ eapply get_names_lst'_spec. }
        intros; eauto. destructAll. eassumption. }

    intros; eauto. destructAll. eassumption.
Qed.


Lemma click_spec P :
  {{ fun _ s => P (fst s) }}
    click
  {{ fun r s res s' => P (fst s') }}.
Proof.
  unfold click.
  eapply bind_triple.
  - eapply @pre_strenghtening with (P := fun _ s => P (fst s) /\ True).
    + firstorder.
    + eapply frame_rule. eapply get_state_spec.
  - intros [c w] [c' w']. simpl.
    eapply pre_curry_l. intros. eapply pre_curry_l. intros. subst.
    eapply @pre_strenghtening with (P := fun _ s => (c', (c, w)) = s /\ True).
    now firstorder.
    eapply post_weakening.
    2:{ eapply frame_rule. eapply put_state_spec. }
    intros. destructAll. destructAll. simpl in *. subst.
    destruct w', p. inv H3. eassumption.
Qed.


Lemma click_spec2 P :
  {{ fun _ s => P (fst s) }}
    click
  {{ fun r s res s' => P (fst s') /\ fst s = fst s' }}.
Proof.
  unfold click.
  eapply bind_triple.
  - eapply @pre_strenghtening with (P := fun _ s => P (fst s) /\ True).
    + firstorder.
    + eapply frame_rule. eapply get_state_spec.
  - intros [c w] [c' w']. simpl.
    eapply pre_curry_l. intros. eapply pre_curry_l. intros. subst.
    eapply @pre_strenghtening with (P := fun _ s => (c', (c, w)) = s /\ True).
    now firstorder.
    eapply post_weakening.
    2:{ eapply frame_rule. eapply put_state_spec. }
    intros. destructAll. destructAll. simpl in *. subst.
    destruct w', p. inv H3.  split; eauto.
Qed.


Opaque bind ret.

Section Inline_correct.

  Context {fuel : Type} {Hf : @fuel_resource fuel} {trace : Type} {Ht : @trace_resource trace}.


  Context (St : Type) (IH : InlineHeuristic St) (cenv : ctor_env)
          (P1 : nat -> @PostT fuel trace) (PG : @PostGT fuel trace)
          (G : nat).

  Variable (HProp : forall L, (L <= G)%nat -> Post_properties cenv (P1 L) (P1 L) PG)
           (HEapp_l : forall L v t l rho1 x rho2, post_Eapp_l (P1 L) (P1 (S L)) v t l rho1 x rho2)
           (HEletapp : forall L1 L2, remove_steps_letapp cenv (P1 L1) (P1 L2) (P1 (S (L1 + L2))))
           (Eletapp_OOT : forall L1 L2, remove_steps_letapp_OOT cenv (P1 L1) (P1 (S (L1 + L2)))).


  (* [add_fundefs] *)

  Lemma add_fundefs_in fm f B ft xs e:
    find_def f B = Some (ft, xs, e) ->
    (add_fundefs B fm) ! f = Some (ft, xs, e).
  Proof.
    induction B.
    - simpl. intros Hdef. destruct (M.elt_eq f v); subst.
      + inv Hdef. simpl. rewrite M.gss. reflexivity.
      + simpl. rewrite M.gso; eauto.
    - intros H. inv H.
  Qed.

  Lemma add_fundefs_not_in fm f B :
    ~ f \in name_in_fundefs B ->
            (add_fundefs B fm) ! f = fm ! f.
  Proof.
    intros Hnin. induction B.
    - simpl. rewrite M.gso. eapply IHB.
      intros Hc. eapply Hnin. simpl. now right; eauto.
      intros Hc. eapply Hnin. simpl. subst; eauto.
    - reflexivity.
  Qed.

  Lemma Dom_map_add_fundefs fm B :
    Dom_map (add_fundefs B fm) <--> name_in_fundefs B :|: Dom_map fm.
  Proof.
    induction B; simpl; [| now sets ].
    rewrite Dom_map_set. rewrite IHB. sets.
  Qed.

  Fixpoint funnames_in_exp (e : exp) : Ensemble var :=
    match e with
    | Econstr _ _ _ e
    | Eproj _ _ _ _ e
    | Eletapp _ _ _ _ e
    | Eprim_val _ _ e
    | Eprim _ _ _ e  => funnames_in_exp e
    | Ecase _ P =>
      (fix aux P  :=
         match P with
         | [] => Empty_set _
         | (c, e) :: P => (funnames_in_exp e) :|: aux P
         end) P
    | Efun B e => name_in_fundefs B :|: funnames_in_fundefs B :|: funnames_in_exp e
    | Eapp _ _ _  => Empty_set _
    | Ehalt _ => Empty_set _
    end
  with funnames_in_fundefs (B : fundefs) : Ensemble var :=
         match B with
         | Fcons _ _ _ e B => funnames_in_exp e :|: funnames_in_fundefs B
         | Fnil => Empty_set _
         end.


  (* Lemmas about [funnames_in_exp] *)

  Lemma funnames_in_exp_subset_mut :
    (forall e, funnames_in_exp e \subset bound_var e) /\
    (forall B, funnames_in_fundefs B \subset bound_var_fundefs B).
  Proof.
    exp_defs_induction IHe IHl IHB; intros; normalize_bound_var; simpl; sets.

    eapply Union_Included. eapply Union_Included.
    eapply Included_trans. eapply name_in_fundefs_bound_var_fundefs. sets.
    now sets. now sets.
  Qed.

  Lemma funname_in_exp_subset :
    forall e, funnames_in_exp e \subset bound_var e.
  Proof. eapply funnames_in_exp_subset_mut. Qed.

  Lemma funname_in_fundefs_subset :
    forall e, funnames_in_fundefs e \subset bound_var_fundefs e.
  Proof. eapply funnames_in_exp_subset_mut. Qed.


  Lemma fun_in_fundefs_bound_var_Setminus' e f ft xs B :
    fun_in_fundefs B (f, ft, xs, e) ->
    unique_bindings_fundefs B ->
    bound_var e \\ funnames_in_exp e \subset bound_var_fundefs B \\ funnames_in_fundefs B \\ name_in_fundefs B.
  Proof.
    intros Hin Hun. induction B; [| now inv Hin ].
    inv Hun. simpl in Hin. inv Hin.
    - inv H. simpl. normalize_bound_var. rewrite !Setminus_Union_distr. do 2 eapply Included_Union_preserv_r.
      eapply Included_Union_preserv_l. eapply Included_Setminus.
      + eapply Union_Disjoint_r. eapply Disjoint_Singleton_r. now intros Hc; inv Hc; eauto.
        eapply Disjoint_Included_r. eapply name_in_fundefs_bound_var_fundefs. sets.
      + rewrite <- Setminus_Union. eapply Included_Setminus; [| now sets ].
        eapply Disjoint_Included_r. eapply funname_in_fundefs_subset. sets.
    - eapply Included_trans. eapply IHB; eauto.
      simpl. normalize_bound_var. rewrite !Setminus_Union_distr. do 3 eapply Included_Union_preserv_r.
      rewrite !Setminus_Union. rewrite <- !Union_assoc. rewrite (Union_commut (funnames_in_exp _)).
      rewrite (Union_commut [set v]).
      rewrite <- !Union_assoc. rewrite Union_assoc. do 2 rewrite <- Setminus_Union.
      eapply Included_Setminus; [| now sets ]. eapply Union_Disjoint_r.
      eapply Disjoint_Singleton_r. now intros Hc; inv Hc; inv H0; eauto.
      eapply Disjoint_Included_r. eapply funname_in_exp_subset. sets.
  Qed.

  Lemma fun_in_fundefs_bound_var_Setminus e f ft xs B :
    fun_in_fundefs B (f, ft, xs, e) ->
    unique_bindings_fundefs B ->
    bound_var e \\ funnames_in_exp e \subset bound_var_fundefs B \\ funnames_in_fundefs B.
  Proof.
    intros Hin Hun. eapply Included_trans. eapply fun_in_fundefs_bound_var_Setminus'. eassumption.
    eassumption. sets.
  Qed.


  Lemma fun_in_fundefs_FromList_subset e f ft xs B :
    fun_in_fundefs B (f, ft, xs, e) ->
    unique_bindings_fundefs B ->
    FromList xs \subset bound_var_fundefs B \\ funnames_in_fundefs B \\ name_in_fundefs B.
  Proof.
    intros Hin Hun. induction B; [| now inv Hin ]. inv Hun. inv Hin.
    - inv H. simpl. normalize_bound_var. rewrite !Setminus_Union_distr. eapply Included_Union_preserv_r.
      eapply Included_Union_preserv_l. rewrite !Setminus_Union. eapply Included_Setminus; [| now sets ].
      eapply Union_Disjoint_r; eapply Union_Disjoint_r.
      + eapply Disjoint_Included_r. eapply funname_in_exp_subset. sets.
      + eapply Disjoint_Included_r. eapply funname_in_fundefs_subset. sets.
      + sets.
      + eapply Disjoint_Included_r. eapply name_in_fundefs_bound_var_fundefs. sets.
    - eapply Included_trans. eapply IHB; eauto.
      simpl. normalize_bound_var. rewrite !Setminus_Union_distr. do 3 eapply Included_Union_preserv_r.
      rewrite !Setminus_Union. rewrite <- !Union_assoc. rewrite (Union_commut (funnames_in_exp _)). rewrite (Union_commut [set v]).
      rewrite <- !Union_assoc. rewrite Union_assoc. do 2 rewrite <- Setminus_Union.
      eapply Included_Setminus; [| now sets ]. eapply Union_Disjoint_r.
      eapply Disjoint_Singleton_r. now intros Hc; inv Hc; inv H0; eauto.
      eapply Disjoint_Included_r. eapply funname_in_exp_subset. sets.
  Qed.


  (*
  Lemma fun_in_fundefs_funnames_in_exp f ft xs e B :
    (f, ft, xs, e) \infun_in_fundefs B ->
    funnames_in_exp e \subset funnames_in_fundefs B.
  Proof.
    induction B; intros Hin; inv Hin.
    + inv H. sets.
    + simpl. eapply Included_Union_preserv_r. eauto.
  Qed.
  *)

  (* [occurs_free_fun_map] and [bound_var_fun_map] *)

  Definition occurs_free_fun_map (fm : fun_map) : Ensemble var :=
    fun x => exists f ft xs e, fm ! f = Some (ft, xs, e) /\ x \in occurs_free e \\ FromList xs.

  Definition bound_var_fun_map (fm : fun_map) : Ensemble var :=
    fun x => exists f ft xs e, fm ! f = Some (ft, xs, e) /\ x \in bound_var e :|: FromList xs.


  Lemma occurs_free_fun_map_get f ft xs e (fm : fun_map) :
    M.get f fm = Some (ft, xs, e) ->
    occurs_free e \\ (FromList xs) \subset occurs_free_fun_map fm.
  Proof.
    intros Hget z Hin. do 4 eexists. split; eauto.
  Qed.

  Lemma occurs_free_fun_map_add_fundefs B fm :
    occurs_free_fun_map (add_fundefs B fm) \subset occurs_free_fundefs B :|: name_in_fundefs B :|: occurs_free_fun_map fm.
  Proof.
    intros x [z Hin]. destructAll. destruct (Decidable_name_in_fundefs B). destruct (Dec z).
    - edestruct name_in_fundefs_find_def_is_Some. eassumption. destructAll.
      erewrite add_fundefs_in in H; eauto. inv H. left.
      eapply find_def_correct in H1. eapply occurs_free_in_fun in H1.
      inv H0. eapply H1 in H. inv H. contradiction. inv H0; eauto.
    - right. rewrite add_fundefs_not_in in H. do 4 eexists; split; eauto.
      eassumption.
  Qed.


  Lemma bound_var_fun_map_get f ft xs e (fm : fun_map) :
    M.get f fm = Some (ft, xs, e) ->
    bound_var e :|: (FromList xs) \subset bound_var_fun_map fm.
  Proof.
    intros Hget z Hin. do 4 eexists. split; eauto.
  Qed.

  Lemma bound_var_fun_map_add_fundefs_un B fm :
    unique_bindings_fundefs B ->
    bound_var_fun_map (add_fundefs B fm) \subset (bound_var_fundefs B \\ name_in_fundefs B) :|: bound_var_fun_map fm.
  Proof.
    intros Hun x [z Hin]. destructAll. destruct (Decidable_name_in_fundefs B). destruct (Dec z).
    - edestruct name_in_fundefs_find_def_is_Some. eassumption. destructAll. erewrite add_fundefs_in in H; [| eassumption ]. inv H.
      edestruct unique_bindings_fun_in_fundefs. eapply find_def_correct. eassumption. eassumption. destructAll.
      left.
      inv H0.
      + constructor. eapply fun_in_fundefs_bound_var_fundefs. eapply find_def_correct. eassumption. now sets.
        intros hc. eapply H4; constructor; eauto.
      + constructor.
        eapply fun_in_fundefs_bound_var_fundefs. eapply find_def_correct. eassumption. now sets.
        intros hc. eapply H5; constructor; eauto.
    - right. rewrite add_fundefs_not_in in H. do 4 eexists; split; eauto.
      eassumption.
  Qed.


  Lemma occurs_free_fun_map_remove_add_fundefs B f fm :
    occurs_free_fun_map (M.remove f (add_fundefs B fm)) \subset occurs_free_fundefs B :|: name_in_fundefs B :|: occurs_free_fun_map (M.remove f fm).
  Proof.
    intros x [z Hin]. destructAll. destruct (peq f z); subst.
    - rewrite M.grs in H. inv H.
    - destruct (Decidable_name_in_fundefs B). destruct (Dec z).
      + edestruct name_in_fundefs_find_def_is_Some. eassumption. destructAll.
        rewrite M.gro in H; eauto. erewrite add_fundefs_in in H; eauto. inv H. left.
        eapply find_def_correct in H1. eapply occurs_free_in_fun in H1.
        inv H0. eapply H1 in H. inv H. contradiction. inv H0; eauto.
      + rewrite M.gro in H; eauto.
        right. rewrite add_fundefs_not_in in H. do 4 eexists; split; eauto. rewrite M.gro. eassumption.
        now eauto. eassumption.
  Qed.

  Lemma occurs_free_fun_map_remove f fm :
    occurs_free_fun_map (M.remove f fm) \subset occurs_free_fun_map fm.
  Proof.
    intros x [z Hin]. destructAll. destruct (peq f z); subst.
    - rewrite M.grs in H. inv H.
    - rewrite M.gro in H; eauto. do 4 eexists; split; eauto.
  Qed.

  Lemma bound_var_fun_map_remove_add_fundefs_un' (B : fundefs) (fm : fun_map) f :
    unique_bindings_fundefs B ->
    bound_var_fun_map (M.remove f (add_fundefs B fm)) \subset
    bound_var_fundefs B \\ name_in_fundefs B :|: bound_var_fun_map (M.remove f fm).
  Proof.
    intros Hun x [z Hin]. destructAll. destruct (peq f z); subst.
    - rewrite M.grs in H. inv H.
    - rewrite M.gro in H; eauto.
      destruct (Decidable_name_in_fundefs B). destruct (Dec z).
      + edestruct name_in_fundefs_find_def_is_Some. eassumption. destructAll. erewrite add_fundefs_in in H; [| eassumption ]. inv H.
        edestruct unique_bindings_fun_in_fundefs. eapply find_def_correct. eassumption. eassumption. destructAll.
        left.
        inv H0.
        * constructor. eapply fun_in_fundefs_bound_var_fundefs. eapply find_def_correct. eassumption. now sets.
          intros hc. eapply H4; constructor; eauto.
        * constructor.
          eapply fun_in_fundefs_bound_var_fundefs. eapply find_def_correct. eassumption. now sets.
          intros hc. eapply H5; constructor; eauto.
      + right. rewrite add_fundefs_not_in in H. do 4 eexists; split; eauto.
        rewrite M.gro; now eauto. eassumption.
  Qed.

  Lemma bound_var_fun_map_remove_add_fundefs_un (B : fundefs) (fm : fun_map) f ft xs e:
    unique_bindings_fundefs B ->
    find_def f B = Some (ft, xs, e) ->
    bound_var_fun_map (M.remove f (add_fundefs B fm)) \subset
    bound_var_fundefs B \\ name_in_fundefs B \\ bound_var e \\ FromList xs :|: bound_var_fun_map (M.remove f fm).
  Proof.
    induction B.
    - intros Hun Hfind. inv Hun. destruct (peq f v); subst.
      + simpl in *. rewrite peq_true in Hfind. inv Hfind.
        intros x [z Hin]. destructAll. rewrite remove_set_1 in H.
        destruct (peq v z); subst.
        * rewrite M.grs in H. inv H.
        * rewrite M.gro in H; eauto. destruct (Decidable_name_in_fundefs B). destruct (Dec z).
          -- edestruct name_in_fundefs_find_def_is_Some. eassumption. destructAll.
             erewrite add_fundefs_in in H; [| eassumption ]. inv H. normalize_bound_var. simpl.
             edestruct unique_bindings_fun_in_fundefs. eapply find_def_correct. eassumption. eassumption. destructAll.

             left. constructor. constructor. constructor. do 3 right.
              eapply fun_in_fundefs_bound_var_fundefs. eapply find_def_correct. eassumption. inv H0; now eauto.
             ++ intros Hc; inv Hc; eauto. inv H17. eapply H5.
                eapply fun_in_fundefs_bound_var_fundefs. eapply find_def_correct. eassumption. inv H0; now eauto.
                inv H0; eauto. eapply H13; constructor. eassumption. eassumption.
                eapply H14; constructor. eassumption. eassumption.
             ++ intros hc. eapply H8. constructor. eassumption. eapply fun_in_fundefs_bound_var_fundefs. eapply find_def_correct. eassumption.
                inv H0; eauto.
             ++ intros hc. eapply H7. constructor. eapply fun_in_fundefs_bound_var_fundefs. eapply find_def_correct. eassumption.
                inv H0; eauto. eassumption.
          -- rewrite add_fundefs_not_in in H; eauto. right. do 4 eexists. split. rewrite M.gro. eassumption. now eauto.
             eassumption.
      + simpl in Hfind. rewrite peq_false in Hfind; eauto. assert (Hf' := Hfind). eapply IHB in Hfind; eauto.
        simpl. intros x Hin. destruct Hin. destructAll. normalize_bound_var. simpl.
        destruct (peq f x0); subst.
        * rewrite M.grs in H. inv H.
        * rewrite M.gro in H; eauto. destruct (peq v x0). subst.
          -- rewrite M.gss in H. inv H. left. constructor. constructor. constructor.
             inv H0; now eauto.
             ++ intros Hc. inv Hc. inv H. now inv H0; eauto.
                inv H0. eapply H8. constructor. eassumption. eapply name_in_fundefs_bound_var_fundefs. eassumption.
                eapply H7. constructor. eapply name_in_fundefs_bound_var_fundefs. eassumption. eassumption.
             ++ intros Hc1. inv H0. eapply H8. constructor. eassumption.
                eapply fun_in_fundefs_bound_var_fundefs. eapply find_def_correct. eassumption. now eauto.
                eapply H7. constructor.
                eapply fun_in_fundefs_bound_var_fundefs. eapply find_def_correct. eassumption. now eauto.
                eassumption.
             ++ intros Hc1. inv H0. eapply H8. constructor. eassumption.
                eapply fun_in_fundefs_bound_var_fundefs. eapply find_def_correct. eassumption. now eauto.
                eapply H7. constructor.
                eapply fun_in_fundefs_bound_var_fundefs. eapply find_def_correct. eassumption. now eauto.
                eassumption.
          -- rewrite M.gso in H.
             assert (Hin' : x \in bound_var_fun_map (M.remove f (add_fundefs B fm))).
             { do 4 eexists. split. rewrite M.gro. eassumption. now eauto. eassumption. }
             eapply Hfind in Hin'. inv Hin'; [| now eauto ]. left. inv H1. inv H2. inv H1.
             constructor. constructor. constructor. eauto.
             ++ intros Hc; inv Hc; eauto. inv H1. contradiction.
             ++ eassumption.
             ++ eassumption.
             ++ eauto.
    - intros. inv H0.
  Qed.

  Lemma  bound_var_fun_map_remove f fm :
    bound_var_fun_map (M.remove f fm) \subset bound_var_fun_map fm.
  Proof.
    intros x [z Hin]. destructAll. destruct (peq f z); subst.
    - rewrite M.grs in H. inv H.
    - rewrite M.gro in H; eauto. do 4 eexists; split; eauto.
  Qed.


  Lemma occurs_free_fun_map_remove' f f' fm :
    occurs_free_fun_map (M.remove f (M.remove f' fm)) \subset occurs_free_fun_map (M.remove f fm).
  Proof.
    intros x [z Hin]. destructAll. destruct (peq f z); subst.
    - rewrite M.grs in H. inv H.
    - rewrite M.gro in H; eauto.
      destruct (peq f' z); subst. rewrite M.grs in H. inv H.
      rewrite M.gro in H; eauto.
      do 4 eexists; split; eauto. rewrite M.gro. eassumption. eauto.
  Qed.


  Lemma bound_var_fun_map_remove' f f' fm :
    bound_var_fun_map (M.remove f (M.remove f' fm)) \subset bound_var_fun_map (M.remove f fm).
  Proof.
    intros x [z Hin]. destructAll. destruct (peq f z); subst.
    - rewrite M.grs in H. inv H.
    - rewrite M.gro in H; eauto.
      destruct (peq f' z); subst. rewrite M.grs in H. inv H.
      rewrite M.gro in H; eauto.
      do 4 eexists; split; eauto. rewrite M.gro. eassumption. eauto.
  Qed.

  (* Various lemmas *)

  Lemma sub_map_def_funs rho B :
    Disjoint _ (name_in_fundefs B) (Dom_map rho) ->
    sub_map rho (def_funs B B rho rho).
  Proof.
    intros Hdis x v Hget.
    rewrite def_funs_neq; eauto.
    intros Hc. eapply Hdis. constructor. eassumption. eexists. eassumption.
  Qed.

  Lemma Dom_map_def_funs B rho B' rho' :
    Dom_map (def_funs B' B rho' rho) <--> name_in_fundefs B :|: Dom_map rho.
  Proof.
    induction B; simpl; sets.
    rewrite Dom_map_set. rewrite IHB. sets.
  Qed.

  (* TODO move *)
  Lemma preord_env_P_inj_set_lists_not_In_P_r' S k f rho1 rho2 rho2' xs vs :
    preord_env_P_inj cenv PG S k f rho1 rho2 ->
    set_lists xs vs rho2 = Some rho2' ->
    Disjoint _(FromList xs) (image f S) ->
    preord_env_P_inj cenv PG S k f rho1 rho2'.
  Proof.
    intros Henv Hnin Hnin' z Hy v' Hget.
    edestruct Henv as [v'' [Hget' Hv]]; eauto.
    eexists; split; eauto. erewrite <- set_lists_not_In. eassumption.
    eassumption. intros Hc. eapply Hnin'. constructor. eassumption.
    eapply In_image. eassumption.
  Qed.

  Lemma NoDup_all_fun_name B :
    unique_bindings_fundefs B ->
    NoDup (all_fun_name B).
  Proof.
    induction B; intros Hc; inv Hc.
    - simpl. constructor; eauto.
      intros Hc. eapply Same_set_all_fun_name in Hc. eapply H5.
      eapply name_in_fundefs_bound_var_fundefs. eassumption.
    - constructor.
  Qed.

  (* [Fun_map_inv] *)

  Fixpoint fun_map_inv' (k : nat) (S : Ensemble var) (fm : fun_map) (rho1 rho2 : env) (i : nat) (sig : subst) : Prop :=
    forall f ft xs e rhoc B f',
      f \in S ->
      fm ! f = Some (ft, xs, e) ->
      rho1 ! f = Some (Vfun rhoc B f') ->
      find_def f B = Some (ft, xs, e) /\ f = f' /\
      preord_env_P_inj cenv PG (occurs_free e \\ FromList xs) i (apply_r sig) (def_funs B B rhoc rhoc) rho2 /\
      match k with
      | 0%nat => True
      | S k => fun_map_inv' k (occurs_free e \\ FromList xs) fm (def_funs B B rhoc rhoc) rho2 i sig
      end.

  Definition fun_map_inv (k : nat) (S : Ensemble var) (fm : fun_map) (rho1 rho2 : env) (i : nat) (sig : subst) : Prop :=
    forall f ft xs e rhoc B f',
      f \in S ->
      fm ! f = Some (ft, xs, e) ->
      rho1 ! f = Some (Vfun rhoc B f') ->
      find_def f B = Some (ft, xs, e) /\ f = f' /\
      preord_env_P_inj cenv PG (occurs_free e \\ FromList xs) i (apply_r sig) (def_funs B B rhoc rhoc) rho2 /\
      match k with
      | 0%nat => True
      | S k => fun_map_inv' k (occurs_free e \\ FromList xs) fm (def_funs B B rhoc rhoc) rho2 i sig
      end.

  Lemma fun_map_inv_eq k S fm rho1 rho2 i sig :
    fun_map_inv k S fm rho1 rho2 i sig = fun_map_inv' k S fm rho1 rho2 i sig.
  Proof.
    destruct k; reflexivity.
  Qed.

  Lemma fun_map_inv_mon k k' S fm rho1 rho2 i sig :
    fun_map_inv k S fm rho1 rho2 i sig ->
    (k' <= k)%nat ->
    fun_map_inv k' S fm rho1 rho2 i sig.
  Proof.
    revert S k fm rho1. induction k' as [k' IHk] using lt_wf_rec1; intros.
    destruct k'.
    - unfold fun_map_inv in *. intros. edestruct H; eauto. destructAll.
      repeat (split; eauto).
    - destruct k; [ lia | ].
      intro; intros. edestruct H; eauto. destructAll.
      split; eauto. split; eauto. split; eauto.
      rewrite <- fun_map_inv_eq. eapply IHk.
      lia. rewrite fun_map_inv_eq. eassumption. lia.
  Qed.

  Lemma fun_map_inv_antimon k S S' fm rho1 rho2 i sig :
    fun_map_inv k S fm rho1 rho2 i sig ->
    S' \subset S ->
    fun_map_inv k S' fm rho1 rho2 i sig.
  Proof.
    intros H1 H2. intro; intros; eauto.
  Qed.


  Lemma fun_map_inv_set_not_In_r k S fm rho1 rho2 i sig x x' v' :
    fun_map_inv k S fm rho1 rho2 i sig ->
    ~ x \in occurs_free_fun_map fm ->
    ~ x' \in image (apply_r sig) (occurs_free_fun_map fm) ->
    fun_map_inv k S fm rho1 (M.set x' v' rho2) i (M.set x x' sig).
  Proof.
    revert S fm rho1 rho2 i sig x x' v'. induction k using lt_wf_rec1; intros. intro; intros.
    edestruct H0; eauto.
    destructAll. split; [| split; [| split ]]; eauto.
    - rewrite apply_r_set_f_eq. eapply preord_env_P_inj_set_extend_not_In_P_r. eassumption.
      + intros Hc. eapply H1. eapply occurs_free_fun_map_get. eassumption. eassumption.
      + intros Hc. eapply H2. eapply image_monotonic; [| eassumption ].
        eapply occurs_free_fun_map_get. eassumption.
    - destruct k; eauto. rewrite <- fun_map_inv_eq in *.
      eapply H. lia. eassumption.
      intros hc. eapply H1. eassumption.
      intros hc. eapply H2. eapply image_monotonic; [| eassumption ]. reflexivity.
  Qed.

  Lemma fun_map_inv_set k S fm rho1 rho2 i sig x v x' v' :
    fun_map_inv k S fm rho1 rho2 i sig ->
    ~ x \in occurs_free_fun_map fm :|: Dom_map fm ->
    ~ x' \in image (apply_r sig) (occurs_free_fun_map fm) ->
    fun_map_inv k (x |: S) fm (M.set x v rho1) (M.set x' v' rho2) i (M.set x x' sig).
  Proof.
    intros Hinv Hnin Hnin'. intro; intros.
    rewrite M.gso in *.
    2:{ intros Heq; subst. eapply Hnin. right. eexists; eauto. }
    inv H.
    - inv H2. exfalso. eapply Hnin. right. eexists; eauto.
    - edestruct Hinv; eauto.
      destructAll. split; [| split; [| split ]]; eauto.
      + rewrite apply_r_set_f_eq. eapply preord_env_P_inj_set_extend_not_In_P_r. eassumption.
        intros Hc. eapply Hnin. left. eapply occurs_free_fun_map_get; eauto.
        intros Hc. eapply Hnin'. eapply image_monotonic; [| eassumption ].
        eapply occurs_free_fun_map_get. eassumption.
      + destruct k; eauto. rewrite <- fun_map_inv_eq in *.
        eapply fun_map_inv_set_not_In_r. eapply fun_map_inv_antimon. eassumption.
        * reflexivity.
        * sets.
        * sets.
  Qed.

  Lemma fun_map_inv_sig_extend_Disjoint k S fm rho1 rho2 i sig xs xs' :
    fun_map_inv k S fm rho1 rho2 i sig ->

    Disjoint _ (FromList xs) (occurs_free_fun_map fm) ->

    fun_map_inv k S fm rho1 rho2 i (set_list (combine xs xs') sig).
  Proof.
    revert S fm rho1 rho2 i sig xs xs'.
    induction k using lt_wf_rec1; intros S fm rho1 rho2 i sig xs xs' Hfm Hdis1.
    intro; intros. edestruct Hfm; eauto. destructAll.
    split; eauto. split; eauto. split.
    - rewrite apply_r_set_list_f_eq.
      eapply preord_env_P_inj_extend_lst_not_In_P_r. eassumption.
      eapply Disjoint_Included_r; [| eapply Hdis1 ].
      eapply occurs_free_fun_map_get. eassumption.
    - destruct k; eauto. rewrite <- fun_map_inv_eq in *. eapply H. lia.
      eassumption.
      sets.
  Qed.


  Lemma fun_map_inv_sig_extend_one_Disjoint k S fm rho1 rho1' rho2 i sig x x' :
    fun_map_inv k S fm rho1 rho2 i sig ->

    eq_env_P (Complement _ [set x]) rho1 rho1' ->
    ~ x \in (Dom_map fm) ->
    ~ x \in (occurs_free_fun_map fm) ->
    ~ x \in S ->

    fun_map_inv k (x |: S) fm rho1' rho2 i (M.set x x' sig).
  Proof.
    intros Hfm HeqP Hdis1 Hdis2 Hdis3.
    intro; intros. inv H. exfalso. inv H2. eapply Hdis1. eexists; eauto.
    rewrite <- HeqP in H1. 2:{ intros Hc; inv Hc; subst; eauto. }
    edestruct Hfm; eauto. destructAll.
    split; eauto. split; eauto. split.
    - rewrite apply_r_set_f_eq.
      eapply preord_env_P_inj_extend_not_In_P_r. eassumption.
      intros Hc. eapply Hdis2. eapply occurs_free_fun_map_get. eassumption.
      eassumption.
    - destruct k; eauto. rewrite <- fun_map_inv_eq in *.
      eapply fun_map_inv_sig_extend_Disjoint with (xs := [x]) (xs' := [x']). eassumption.
      repeat normalize_sets. eapply Disjoint_Singleton_l.
      sets.
  Qed.

  Lemma fun_map_inv_env_eq_P S k fm rho1 rho2 i sig rho1' rho2' :
    fun_map_inv k S fm rho1 rho2 i sig ->
    eq_env_P S rho1 rho1' ->
    eq_env_P (image (apply_r sig) (occurs_free_fun_map fm)) rho2 rho2' ->
    fun_map_inv k S fm rho1' rho2' i sig.
  Proof.
    revert S fm rho1 rho2 i sig rho1' rho2'.
    induction k using lt_wf_rec1; intros S fm rho1 rho2 i sig rho1' rho2' Hfm Heq1 Hsub Heq2.
    intro; intros. rewrite <- Heq1 in H2; eauto. edestruct Hfm; eauto. destructAll.
    split; eauto. split; eauto. split.
    - eapply preord_env_P_inj_eq_env_P.
      eassumption.
      now eapply eq_env_P_refl.
      eapply eq_env_P_antimon. eassumption.
      eapply image_monotonic. eapply occurs_free_fun_map_get; eauto.
    - destruct k; eauto. rewrite <- fun_map_inv_eq in *. eapply H. lia.
      eassumption. eapply eq_env_P_refl. eassumption.
  Qed.


  Lemma fun_map_inv_set_lists k S fm rho1 rho1' rho2 i sig xs vs :
    fun_map_inv k S fm rho1 rho2 i sig ->

    NoDup xs ->
    Disjoint _ (FromList xs) (occurs_free_fun_map fm :|: Dom_map fm) ->
    set_lists xs vs rho1 = Some rho1' ->

    fun_map_inv k (FromList xs :|: S) fm rho1' rho2 i sig.
  Proof.
    revert S fm rho1 rho1' rho2 i sig xs vs.
    induction k using lt_wf_rec1;
      intros S fm rho1 rho1' rho2 i sig xs vs Hfm Hnd Hdis1 Hset.
    intro f; intros.
    destruct (Decidable_FromList xs). destruct (Dec f).
    - exfalso. eapply Hdis1. constructor. eassumption. right. eexists; eauto.
    - inv H0; try contradiction. erewrite <- set_lists_not_In in H2; [| eassumption | eassumption ].
      edestruct Hfm; eauto.
  Qed.

  Lemma fun_map_inv_set_lists_r k S fm rho1 rho2' rho2 i sig xs vs :
    fun_map_inv k S fm rho1 rho2 i sig ->
    Disjoint _ (FromList xs) (image (apply_r sig) (occurs_free_fun_map fm)) ->

    set_lists xs vs rho2 = Some rho2' ->

    fun_map_inv k S fm rho1 rho2' i sig.
  Proof.
    revert S fm rho1 rho2' rho2 i sig xs vs.
    induction k using lt_wf_rec1;
      intros S fm rho1 rho1' rho2 i sig xs vs Hfm Hdis1 Hset.
    intro f; intros.
    edestruct Hfm; eauto. destructAll. split; eauto. split; eauto. split.
    + eapply preord_env_P_inj_set_lists_not_In_P_r'. eassumption. eassumption.
      eapply Disjoint_Included_r; [| eassumption ]. eapply image_monotonic. eapply occurs_free_fun_map_get.
      eassumption.
    + destruct k; eauto. rewrite <- fun_map_inv_eq in *.
      eapply H. lia. eassumption.
      eapply Disjoint_Included_r; [| eapply Hdis1 ]. reflexivity. eassumption.
  Qed.

  Lemma fun_map_inv_def_funs_Disjoint k S fm rho1 rho2 i sig B1 B2 :
    fun_map_inv k S fm rho1 rho2 i sig ->

    Disjoint _ (name_in_fundefs B1) (S :|: occurs_free_fun_map fm) ->
    Disjoint _ (name_in_fundefs B2) (image (apply_r sig) (occurs_free_fun_map fm)) ->

    fun_map_inv k S fm rho1 (def_funs B2 B2 rho2 rho2) i
                (set_list (combine (all_fun_name B1) (all_fun_name B2)) sig).
  Proof.
    revert S fm rho1 rho2 i sig B1 B2; induction k using lt_wf_rec1; intros.
    intro; intros.
    edestruct H0; eauto. destructAll.
    repeat (split; [ now eauto |]). split.
    - eapply preord_env_P_inj_def_funs_neq_r.
      rewrite apply_r_set_list_f_eq. eapply preord_env_P_inj_extend_lst_not_In_P_r.
      eassumption. rewrite <- Same_set_all_fun_name.
      eapply Disjoint_Included_r; [| eapply H1 ]. eapply Included_Union_preserv_r.
      eapply occurs_free_fun_map_get. eassumption.

      rewrite apply_r_set_list_f_eq. eapply Disjoint_Included_l.
      intros x Hc. destruct Hc. destructAll.
      rewrite extend_lst_gso. eapply In_image. eassumption.
      rewrite <- Same_set_all_fun_name. intros Hc. eapply H1. constructor. eassumption. right.
      eapply occurs_free_fun_map_get. eassumption. eassumption.
      eapply Disjoint_sym. eapply Disjoint_Included_r; [| eassumption ]. eapply image_monotonic.
      eapply occurs_free_fun_map_get. eassumption.
    - destruct k; eauto. rewrite <- fun_map_inv_eq in *. eapply H.
      + lia.
      + eassumption.
      + eapply Union_Disjoint_r; [| sets ].
        eapply Disjoint_Included_r; [| eassumption ]. eapply Included_Union_preserv_r.
      eapply occurs_free_fun_map_get. eassumption.
      + sets.
  Qed.

  Lemma fun_map_inv_add_fundefs k S fm rho1 rho2 i sig B1 (* B2 *) :
    fun_map_inv k S fm rho1 rho2 i sig ->

    Disjoint _ (name_in_fundefs B1) (S :|: occurs_free_fun_map fm) ->

    fun_map_inv k S (add_fundefs B1 fm) rho1 rho2 i sig.
  Proof.
    revert S fm rho1 rho2 i sig B1 (* B2 *); induction k using lt_wf_rec1; intros.
    intro; intros. rewrite add_fundefs_not_in in H3.
    2:{ intros Hc. eapply H1. constructor. eassumption. left. eassumption. }
    edestruct H0; eauto. destructAll.
    repeat (split; [ now eauto |]).
    destruct k; eauto. rewrite <- fun_map_inv_eq in *. eapply H.
    + lia.
    + eassumption.
    + eapply Union_Disjoint_r; [| sets ].
      eapply Disjoint_Included_r; [| eassumption ]. eapply Included_Union_preserv_r.
      eapply occurs_free_fun_map_get. eassumption.
  Qed.

  Lemma fun_map_inv_def_funs_add_fundefs k S fm rho1 rho2 i sig B1 B2 :
    fun_map_inv k S fm rho1 rho2 i sig ->

    preord_env_P_inj cenv PG (name_in_fundefs B1 :|: occurs_free_fundefs B1) i
                     (apply_r (set_list (combine (all_fun_name B1) (all_fun_name B2)) sig))
                     (def_funs B1 B1 rho1 rho1) (def_funs B2 B2 rho2 rho2) ->

    unique_bindings_fundefs B1 ->
    occurs_free_fundefs B1 \subset S ->

    Disjoint _ (name_in_fundefs B1) (S :|: occurs_free_fun_map fm) ->
    Disjoint _ (name_in_fundefs B2) (image (apply_r sig) (occurs_free_fun_map fm)) ->

    fun_map_inv k (name_in_fundefs B1 :|: S) (add_fundefs B1 fm) (def_funs B1 B1 rho1 rho1) (def_funs B2 B2 rho2 rho2) i
                (set_list (combine (all_fun_name B1) (all_fun_name B2)) sig).
  Proof.
    revert S fm rho1 rho2 i sig B1 B2. induction k as [k IHk] using lt_wf_rec1.
    intros S fm rho1 rho2 i sig B1 B2 Hf' Hrel Hun Hsub Hdis Hdis'.
    intros f ft xs e rhoc B' f' HSin Heq1 Heq2.
    destruct (Decidable_name_in_fundefs B1) as [Dec]. destruct (Dec f).
    - rewrite def_funs_eq in Heq2; eauto. inv Heq2.
      edestruct name_in_fundefs_find_def_is_Some. eassumption. destructAll.
      erewrite add_fundefs_in in Heq1; [| eassumption ]. inv Heq1. split; eauto.
      split; eauto. split.
      + eapply preord_env_P_inj_antimon. eassumption. eapply Setminus_Included_Included_Union.
        eapply Included_trans. eapply occurs_free_in_fun. eapply find_def_correct. eassumption. sets.
      + destruct k; eauto. rewrite <- fun_map_inv_eq. eapply fun_map_inv_antimon. eapply IHk.
        lia. eapply fun_map_inv_mon. eassumption. lia. eassumption. eassumption.
        eassumption. now sets. now sets. eapply Setminus_Included_Included_Union.
        eapply Included_trans. eapply occurs_free_in_fun. eapply find_def_correct. eassumption.
        sets.
    - rewrite def_funs_neq in Heq2; eauto.
      rewrite add_fundefs_not_in in Heq1; [| eassumption ]. inv HSin. contradiction.
      edestruct Hf'. eassumption. eassumption. eassumption. destructAll. split; eauto. split; eauto. split.
      + eapply preord_env_P_inj_def_funs_neq_r.
        rewrite apply_r_set_list_f_eq. eapply preord_env_P_inj_extend_lst_not_In_P_r.
        eassumption.
        * rewrite <- Same_set_all_fun_name.
          eapply Disjoint_Included; [| | eapply Hdis ]. eapply Included_Union_preserv_r.
          eapply occurs_free_fun_map_get. eassumption. reflexivity.
        * rewrite apply_r_set_list_f_eq. eapply Disjoint_Included_l.
          intros x Hc. destruct Hc. destructAll.
          rewrite extend_lst_gso. eapply In_image. eassumption.
          rewrite <- Same_set_all_fun_name. intros Hc. eapply Hdis. constructor.
          eassumption. right.
          eapply occurs_free_fun_map_get. eassumption. eassumption.
          eapply Disjoint_sym. eapply Disjoint_Included_r; [| eassumption ]. apply image_monotonic.
          eapply occurs_free_fun_map_get. eassumption.
      + destruct k; eauto. rewrite <- fun_map_inv_eq in *.
        eapply fun_map_inv_add_fundefs. eapply fun_map_inv_def_funs_Disjoint; try eassumption.
        * eapply Union_Disjoint_r; [| sets ].
          eapply Disjoint_Included_r; [| eassumption ]. eapply Included_Union_preserv_r.
          eapply occurs_free_fun_map_get. eassumption.
        * eapply Union_Disjoint_r; [| sets ].
          eapply Disjoint_Included_r; [| eassumption ]. eapply Included_Union_preserv_r.
          eapply occurs_free_fun_map_get. eassumption.
  Qed.

  Lemma fun_map_inv_i_mon k S fm rho1 rho2 i i' sig :
    fun_map_inv k S fm rho1 rho2 i sig ->
    (i' <= i)%nat ->
    fun_map_inv k S fm rho1 rho2 i' sig.
  Proof.
    revert k S fm rho1 rho2 i i' sig. induction k as [k' IHk] using lt_wf_rec1; intros.
    intros. intro; intros. edestruct H; eauto. destructAll. split; eauto. split; eauto. split; eauto.
    eapply preord_env_P_inj_monotonic; eassumption.
    destruct k'; eauto. rewrite <- fun_map_inv_eq in *. eapply IHk; eauto.
  Qed.

  Lemma fun_map_inv_remove k S fm rho1 rho2 i sig f:
    fun_map_inv k S fm rho1 rho2 i sig ->
    fun_map_inv k S (M.remove f fm) rho1 rho2 i sig.
  Proof.
    revert k S fm rho1 rho2 i sig f. induction k as [k' IHk] using lt_wf_rec1; intros.
    intros. intro; intros.
    destruct (peq f f0). subst. rewrite M.grs in H1. inv H1. rewrite M.gro in H1; eauto.
    edestruct H; eauto. destructAll. split; eauto. split; eauto. split; eauto.
    destruct k'; eauto. rewrite <- fun_map_inv_eq in *. eapply IHk; eauto.
  Qed.

  Definition fun_map_vars (fm : fun_map) (F : Ensemble var) (sig : subst) :=
    forall f ft xs e,
      fm ! f = Some (ft, xs, e) ->
      unique_bindings e /\
      NoDup xs /\
      Disjoint _ (bound_var e) (FromList xs :|: occurs_free e) /\
      Disjoint _ (bound_var e) (Dom_map fm) /\
      Disjoint _ (bound_var e :|: FromList xs) (occurs_free_fun_map (M.remove f fm)) /\
      Disjoint _ (bound_var e :|: occurs_free e) (bound_var_fun_map (M.remove f fm)) /\
      Disjoint _ (FromList xs) (Dom_map fm) /\
      Disjoint _ F ((* bound_var e :|: *) image (apply_r sig) (occurs_free e \\ FromList xs)).

  Lemma fun_map_vars_antimon fm F F' sig :
    fun_map_vars fm F sig ->
    F' \subset F ->
    fun_map_vars fm F' sig.
  Proof.
    intros Hfm Hsub; intro; intros. eapply Hfm in H. destructAll.
    do 6 (split; eauto). sets.
  Qed.

  Instance fm_map_vars_Proper fm : Proper (Same_set _ ==> eq ==> iff) (fun_map_vars fm).
  Proof.
    repeat (intro; intros). subst. split; intros.
    intro; intros. eapply H0 in H1. rewrite H in H1. eauto.
    intro; intros. eapply H0 in H1. rewrite <- H in H1. eauto.
  Qed.


  Lemma fun_map_vars_set fm F sig x v :
    fun_map_vars fm F sig ->
    fun_map_vars fm (F \\ [set v]) (M.set x v sig).
  Proof.
    intros Hfm; intro; intros. eapply Hfm in H. destructAll.
    do 8 (split; eauto).
    (* eapply Union_Disjoint_r. now sets. *)
    eapply Disjoint_Included_r. eapply image_apply_r_set.
    eapply Union_Disjoint_r. now sets. now xsets.
  Qed.

  Lemma fun_map_vars_set_list fm F sig xs vs :
    fun_map_vars fm F sig ->
    fun_map_vars fm (F \\ FromList vs) (set_list (combine xs vs) sig).
  Proof.
    revert F vs sig. induction xs; intros F vs sig.
    - simpl. intros Hin. eapply fun_map_vars_antimon. eassumption.
      now sets.
    - destruct vs; simpl.
      + intros Hf'. eapply fun_map_vars_antimon. eassumption. sets.
      + intros Hfm. simpl. repeat normalize_sets. rewrite Union_commut.
        rewrite <- Setminus_Union. eapply fun_map_vars_set.
        simpl. eapply IHxs; eauto.
  Qed.


  Lemma fun_map_vars_def_funs fm S sig B xs :
    fun_map_vars fm S sig ->
    unique_bindings_fundefs B ->

    Disjoint _ (bound_var_fundefs B) (occurs_free_fundefs B :|: occurs_free_fun_map fm) ->
    Disjoint _ (occurs_free_fundefs B :|: bound_var_fundefs B) (bound_var_fun_map fm) ->

    Disjoint _ (bound_var_fundefs B) (Dom_map fm) ->
    Disjoint _ (S \\ FromList xs) ((* bound_var_fundefs B :|: *) image (apply_r sig) (occurs_free_fundefs B)) ->

    Datatypes.length (all_fun_name B) = Datatypes.length xs ->

    fun_map_vars (add_fundefs B fm) (S \\ FromList xs) (set_list (combine (all_fun_name B) xs) sig).
  Proof.
    intros Hfm Hun Hdis1 Hdis' Hdis2 Hdis3 (* Hdis4 Hdis5 *) Hlen x ft ys e Hget. destruct (Decidable_name_in_fundefs B). destruct (Dec x).
    - edestruct name_in_fundefs_find_def_is_Some; eauto. destructAll. erewrite add_fundefs_in in Hget; eauto.
      inv Hget. edestruct unique_bindings_fun_in_fundefs. eapply find_def_correct. eassumption. eassumption. destructAll.
      assert (Hin1 : bound_var e \subset bound_var_fundefs B).
      { eapply Included_trans; [| eapply fun_in_fundefs_bound_var_fundefs; eapply find_def_correct; eauto ]. now sets. }
      assert (Hin2 : FromList ys \subset bound_var_fundefs B).
      { eapply Included_trans; [| eapply fun_in_fundefs_bound_var_fundefs; eapply find_def_correct; eauto ]. now sets. }

      split. now eauto. split. now eauto. split; [| split; [| split; [| split; [| split; [| split ]]]]].
      + eapply Union_Disjoint_r. now sets.
        eapply fun_in_fundefs_Disjoint_bound_Var_occurs_free. eapply find_def_correct. eassumption.
        eassumption. clear Hdis2. sets.
      + rewrite Dom_map_add_fundefs. eapply Union_Disjoint_r. now sets.
        eapply Disjoint_Included; [| | eapply Hdis2 ]. now sets.
        eapply Included_trans; [| eapply fun_in_fundefs_bound_var_fundefs; eapply find_def_correct; eauto ]. now sets.
      + eapply Disjoint_Included_r. eapply occurs_free_fun_map_remove_add_fundefs. eapply Union_Disjoint_r; [ eapply Union_Disjoint_r | ].
        * eapply Disjoint_Included_l. eapply Union_Included. eassumption.
          eapply Included_trans; [| eapply fun_in_fundefs_bound_var_fundefs; eapply find_def_correct; eauto ]. now sets.
          clear Hdis2. sets.
        * sets.
        * eapply Disjoint_Included_r. eapply occurs_free_fun_map_remove.
          eapply Disjoint_Included_l. eapply Union_Included; eassumption. clear Hdis2. sets.
      + eapply Disjoint_Included_l.
        * eapply Included_Union_compat. reflexivity. eapply occurs_free_in_fun. eapply find_def_correct. eassumption.
        * rewrite Union_assoc. eapply Union_Disjoint_l.
          -- eapply Disjoint_Included_r.
             eapply bound_var_fun_map_remove_add_fundefs_un. eassumption. eassumption. eapply Union_Disjoint_r.
             ++ sets.
             ++ eapply Disjoint_Included. eapply bound_var_fun_map_remove.
                eapply Union_Included; eassumption. sets.
          -- eapply Disjoint_Included_r. eapply bound_var_fun_map_remove_add_fundefs_un'. eassumption.
             eapply Union_Disjoint_r.
             ++ eapply Union_Disjoint_l. now sets. clear Hdis2. sets.
             ++ eapply Disjoint_Included_r. eapply bound_var_fun_map_remove.
                eapply Union_Disjoint_l; [| now sets ]. eapply Disjoint_Included_l.
                eapply name_in_fundefs_bound_var_fundefs. sets.
      + rewrite Dom_map_add_fundefs. eapply Union_Disjoint_r. eassumption.
        eapply Disjoint_Included_l.
        eapply Included_Setminus. eassumption. eassumption. sets.
      + (* eapply Union_Disjoint_r. now sets. *)
        eapply Disjoint_Included_r.
        eapply image_apply_r_set_list. now eauto. eapply Union_Disjoint_r. now sets.
        rewrite <- Same_set_all_fun_name.
        eapply Disjoint_Included; [| | eapply Hdis3 ]; [| now sets ].
        eapply image_monotonic. do 2 eapply Setminus_Included_Included_Union.
        eapply Included_trans. eapply occurs_free_in_fun. eapply find_def_correct. eassumption. now sets.
    - rewrite add_fundefs_not_in in Hget; eauto. edestruct Hfm. eassumption. destructAll.
      split; eauto. split; eauto. split; [| split; [| split; [| split; [| split; [| split ]]]]].
      + now sets.
      + rewrite Dom_map_add_fundefs. eapply Union_Disjoint_r.
        * eapply Disjoint_sym. eapply Disjoint_Included; [| | eapply Hdis' ].
          eapply Included_trans; [| eapply bound_var_fun_map_get; eauto ]. now sets.
          eapply Included_trans. eapply name_in_fundefs_bound_var_fundefs. sets.
        * sets.
      + eapply Disjoint_Included_r. eapply occurs_free_fun_map_remove_add_fundefs.
        eapply Union_Disjoint_r; [| now sets ].
        eapply Disjoint_Included_l.
        now eapply bound_var_fun_map_get; eauto.
        eapply Disjoint_sym. eapply Disjoint_Included_l; [| eassumption ]. eapply Included_Union_compat.
        reflexivity. eapply name_in_fundefs_bound_var_fundefs.
      + eapply Disjoint_Included_r. eapply bound_var_fun_map_remove_add_fundefs_un'.
        eassumption. eapply Union_Disjoint_r; [| now sets ]. eapply Union_Disjoint_l.
        * eapply Disjoint_sym. eapply Disjoint_Included; [| | eapply Hdis' ].
          eapply Included_trans; [| eapply bound_var_fun_map_get; eauto ]. sets. sets.
        * eapply Disjoint_Included_l. eapply Included_Union_Setminus with (s2 := FromList ys). tci.
          eapply Union_Disjoint_l.
          -- eapply Disjoint_sym. eapply Disjoint_Included; [| | eapply Hdis1 ].
             eapply Included_Union_preserv_r. eapply Included_trans; [| eapply occurs_free_fun_map_get; eauto ]. sets.
             sets.
          -- eapply Disjoint_sym. eapply Disjoint_Included; [| | eapply Hdis' ].
             eapply Included_trans; [| eapply bound_var_fun_map_get; eauto ]. sets. sets.
      + rewrite Dom_map_add_fundefs. eapply Union_Disjoint_r.
        eapply Disjoint_sym. eapply Disjoint_Included; [| | eapply Hdis' ].
        eapply Included_trans; [| eapply bound_var_fun_map_get; eauto ]. sets.
        eapply Included_trans. eapply name_in_fundefs_bound_var_fundefs. sets.
        sets.
      + (* eapply Union_Disjoint_r. now sets.  *)
        eapply Disjoint_Included_r. eapply image_apply_r_set_list. eassumption.
        eapply Union_Disjoint_r. now sets. xsets.
  Qed.

  Lemma fun_map_vars_inv_remove S fm sig f :
    fun_map_vars fm S sig ->
    fun_map_vars (M.remove f fm) S sig.
  Proof.
    intros Hfm. intro; intros.
    destruct (peq f f0). subst. rewrite M.grs in H. inv H. rewrite M.gro in H; eauto.
    edestruct Hfm. eassumption. destructAll. repeat (split; [ now eauto |]).
    split; [| split; [| split; [| split ]]]; eauto.
    - rewrite Dom_map_remove. sets.
    - sets. eapply Disjoint_Included_r. eapply occurs_free_fun_map_remove'. sets.
    - sets. eapply Disjoint_Included_r. eapply bound_var_fun_map_remove'. sets.
    - rewrite Dom_map_remove. sets.
  Qed.


  (* This invariant is used just for fundefs, instead of
     [Disjoint _ (bound_var_fun_map fm) (bound_var_fundefs B :|: occurs_free_fundefs B)]
     which does not hold after add_fundefs *)

  Definition just_for_fun_inv (B : fundefs) (fm : fun_map) :=
    forall f ft xs e,
      fun_in_fundefs B (f, ft, xs, e) ->
      Disjoint _ (bound_var_fun_map (M.remove f fm)) (bound_var e :|: occurs_free e).

  Lemma bound_var_fun_map_remove_set_same f v fm :
    bound_var_fun_map (M.remove f (M.set f v fm)) \subset bound_var_fun_map fm.
  Proof.
    intros z Hin. inv Hin. destructAll. destruct (peq f x).
    + subst. rewrite M.grs in H. congruence.
    + rewrite M.gro, M.gso in H; eauto. repeat eexists; eauto.
  Qed.

  Lemma bound_var_fun_map_set f xs ft e fm :
    bound_var_fun_map (M.set f (ft, xs, e) fm) \subset bound_var e :|: FromList xs :|: bound_var_fun_map fm.
  Proof.
    intros z Hin. inv Hin. destructAll. destruct (peq f x).
    + subst. rewrite M.gss in H. inv H. eauto.
    + rewrite M.gso in H; eauto. right. repeat eexists; eauto.
  Qed.

  Lemma bound_var_fun_map_remove_set_swap f g v fm :
    f <> g ->
    bound_var_fun_map (M.remove f (M.set g v fm)) <--> bound_var_fun_map (M.set g v (M.remove f fm)).
  Proof.
    intros Hneq. split.
    - intros z Hin. inv Hin. destructAll. destruct (peq f x).
      + subst. rewrite M.grs in H. congruence.
      + rewrite remove_set_2 in H; eauto. repeat eexists; eauto.
    - intros z Hin. inv Hin. destructAll. destruct (peq g x).
      + subst. rewrite M.gss in H. inv H. repeat eexists; eauto.
        rewrite M.gro. rewrite M.gss. reflexivity. eauto.
      + rewrite M.gso in H; eauto.
        destruct (peq f x).
        * subst. rewrite M.grs in H. congruence.
        * rewrite M.gro in H; eauto. repeat eexists; eauto.
          rewrite M.gro, M.gso; eauto.
  Qed.


  Lemma just_for_fun_inv_add_fundefs B fm :
    unique_bindings_fundefs B ->
    Disjoint _ (bound_var_fun_map fm) (bound_var_fundefs B :|: occurs_free_fundefs B) ->
    Disjoint _ (bound_var_fundefs B) (occurs_free_fundefs B) ->
    just_for_fun_inv B (add_fundefs B fm).
  Proof.
    revert fm; induction B; intros fm Hun Hdis Hdis'.
    - simpl. intro; intros. inv H.
      + inv H0. inv Hun.
        eapply Disjoint_Included_l.
        eapply Included_trans.
        now eapply bound_var_fun_map_remove_set_same.
        now eapply bound_var_fun_map_add_fundefs_un; eauto.
        eapply Union_Disjoint_l.
        * eapply Union_Disjoint_r.
          -- sets.
          -- eapply Disjoint_Included_r. eapply occurs_free_in_fun with (B := Fcons f0 ft xs e0 B).
             now left.  simpl.
             repeat (eapply Union_Disjoint_r; [ now sets | ]).
             rewrite bound_var_fundefs_Fcons in Hdis'. sets.
        * eapply Disjoint_Included_r. eapply bound_var_occurs_free_Fcons_Included.
          eassumption.
      + inv Hun. assert (Hin := H0).
        destruct (peq v f0); subst.
        { exfalso. eapply fun_in_fundefs_bound_var_fundefs in Hin. eapply H6. eapply Hin. sets. }

        eapply IHB in H0.
        * rewrite bound_var_fun_map_remove_set_swap; eauto.
          eapply Disjoint_Included_l.
          eapply bound_var_fun_map_set. eapply Union_Disjoint_l; [| now sets ].
          eapply Union_Disjoint_r.
          -- eapply Disjoint_Included_r. eapply Included_trans; [| eapply fun_in_fundefs_bound_var_fundefs; eauto ]. now sets.
             now sets.
          -- eapply Disjoint_Included_r. eapply occurs_free_in_fun. eassumption. eapply Union_Disjoint_r; [| eapply Union_Disjoint_r ].
             ++ eapply Disjoint_Included_r. eapply Included_trans; [| eapply fun_in_fundefs_bound_var_fundefs; eauto ]. now sets.
                now sets.
             ++ eapply Disjoint_Included_r. eapply name_in_fundefs_bound_var_fundefs. sets.
             ++ rewrite bound_var_fundefs_Fcons, occurs_free_fundefs_Fcons in Hdis'.
                eapply Disjoint_Included_r. eapply Included_Union_Setminus with (s2 := [set v]). now tci.
                eapply Union_Disjoint_r. eapply Disjoint_Included; [| | eapply Hdis' ]; now xsets. now sets.
        * eassumption.
        * eapply Disjoint_Included_r; [| eassumption ].
          normalize_bound_var. normalize_occurs_free. (* XXX make lemma pls *)
          rewrite !Union_assoc.
          rewrite Union_Setminus_Included with (s3 := [set v]); tci; sets.
        * rewrite bound_var_fundefs_Fcons in Hdis'.
          rewrite occurs_free_fundefs_Fcons in Hdis'.
          eapply Disjoint_Included_r.
          eapply Included_Union_Setminus_Included_Union with (s3 := [set v]); tci. reflexivity.
          eapply Included_Union_preserv_l. reflexivity.
          eapply Union_Disjoint_r.
          eapply Disjoint_Included; [| | eapply Hdis' ]; sets.
          sets.
    - intro; intros. inv H.
  Qed.

  Opaque preord_exp'.


  (** This identity is very useful to make the computation of the IH to appear
      as a subcomputation in the goal *)
  Lemma st_eq_Ecase (m1 : inlineM (list (ctor_tag * exp))) (x : var) y :
    st_eq
      (bind (ys <- m1 ;; ret (y :: ys)) (fun ys' => ret (Ecase x ys')))
      (e <- (ys <- m1 ;; ret (Ecase x ys)) ;;
       match e with
         | Ecase x ys =>
           ret (Ecase x (y :: ys))
         | _ => ret e
       end).
  Proof.
    repeat rewrite pbind_bind.
    eapply st_eq_transitive. eapply (assoc m1). simpl.
    rewrite (assoc m1).
    apply bind_Proper_r; auto; intros x0.
    now do 2 rewrite left_id.
  Qed.

  Definition Ecase_shape sig (e e' : exp) : Prop :=
    match e with
    | Ecase x l => exists cl, e' = Ecase (apply_r sig x) cl /\ Forall2 (fun p p' : ctor_tag * exp => fst p = fst p') l cl
    | _ => True
    end.


  Lemma inline_correct_mut d j (Hleq : (j <= G)%nat) :
    (forall e sig fm st S
            (Hun : unique_bindings e)
            (Hdis1 : Disjoint _ (bound_var e) (occurs_free e :|: occurs_free_fun_map fm))
            (Hdis3 : Disjoint _ S (image (apply_r sig) (occurs_free e :|: occurs_free_fun_map fm)))
            (Hdis4 : Disjoint _ (bound_var e) (Dom_map fm))
            (Hdis5 : Disjoint _ (bound_var_fun_map fm) (bound_var e :|: occurs_free e))

            (Hfm : fun_map_vars fm S sig),
        {{ fun _ s => fresh S (next_var (fst s)) }}
          inline_exp St IH d j e sig fm st
        {{ fun _ s e' s' =>
             fresh S (next_var (fst s')) /\ next_var (fst s) <= next_var (fst s') /\
             unique_bindings e' /\
             occurs_free e' \subset image (apply_r sig) (occurs_free e :|: occurs_free_fun_map fm) /\
             bound_var e' \subset (Range (next_var (fst s)) (next_var (fst s')))  /\ Ecase_shape sig e e' /\
             (forall k rho1 rho2,
                 preord_env_P_inj cenv PG (occurs_free e) k (apply_r sig) rho1 rho2 ->
                 fun_map_inv d (occurs_free e) fm rho1 rho2 k sig ->
                 preord_exp cenv (P1 j) PG k (e, rho1) (e', rho2)) }} ) /\

    (forall B sig sig0 fm st S
            (Hun : unique_bindings_fundefs B)
            (Hdis1 : Disjoint _ (bound_var_fundefs B) (occurs_free_fundefs B :|: (occurs_free_fun_map fm \\ name_in_fundefs B)))
            (Hdis3 : Disjoint _ S (image (apply_r sig) (occurs_free_fundefs B :|: occurs_free_fun_map fm)))
            (Hdis4 : Disjoint _ (bound_var_fundefs B \\ name_in_fundefs B) (Dom_map fm))
            (Hdis5 : just_for_fun_inv B fm)

            (Hfm : fun_map_vars fm S sig)
            (Hnames1 : NoDup (apply_r_list sig (all_fun_name B)))
            (Hnames2 : Disjoint _ S (FromList (apply_r_list sig (all_fun_name B)))),
        {{ fun _ s => fresh S (next_var (fst s)) }}
          inline_fundefs _ IH d j sig0 sig fm B st
        {{ fun _ s B' s' =>
             fresh S (next_var (fst s')) /\ next_var (fst s) <= next_var (fst s') /\
             unique_bindings_fundefs B' /\
             occurs_free_fundefs B' \subset image (apply_r sig) (occurs_free_fundefs B :|: occurs_free_fun_map fm) /\
             bound_var_fundefs B' \\ name_in_fundefs B' \subset (Range (next_var (fst s)) (next_var (fst s'))) /\
             all_fun_name B' = apply_r_list sig (all_fun_name B) /\
             (forall f xs ft e1,
                 find_def f B = Some (ft, xs, e1) ->
                 exists xs' e2,
                   find_def (apply_r sig f) B' = Some (ft, xs', e2) /\
                   length xs = length xs' /\ NoDup xs' /\ FromList xs' \subset S /\
                   (forall rho1 rho2 k,
                       preord_env_P_inj cenv PG (occurs_free_fundefs B :|: name_in_fundefs B :|: FromList xs )
                                        k (apply_r sig <{ xs ~> xs' }>) rho1 rho2 ->
                       fun_map_inv d (occurs_free_fundefs B :|: name_in_fundefs B :|: FromList xs) fm rho1 rho2 k (set_list (combine xs xs') sig) ->
                       preord_exp cenv (P1 j) PG k (e1, rho1) (e2, rho2))) }}).

  Proof.
    revert j Hleq. induction d as [d IHd] using lt_wf_rec1; intros j Hleq.
    exp_defs_induction IHe IHl IHB; intros; inv Hun; try rewrite inline_exp_eq;
      (destruct (HProp j); [ eassumption | ]).
    - (* constr *)
      eapply bind_triple. eapply pre_transfer_r. now eapply get_fresh_name_spec.
      intros x w1. simpl. eapply pre_curry_l. intros Hf'. eapply pre_curry_l. intros HinS.
      eapply bind_triple. eapply frame_rule. eapply frame_rule. eapply IHe with (S := S \\ [set x]).
      + eassumption.
      + repeat normalize_bound_var_in_ctx. repeat normalize_occurs_free_in_ctx.
        eapply Disjoint_Included_r. eapply @Included_Union_Setminus with (s2 := [set v]). tci.
        eapply Union_Disjoint_r. eapply Disjoint_Included; [| | eapply Hdis1 ]; sets.
        rewrite Setminus_Union_distr. now sets.
        eapply Disjoint_Singleton_r. eassumption.
      + eapply Disjoint_Included_r.
        eapply image_apply_r_set.
        repeat normalize_bound_var_in_ctx. repeat normalize_occurs_free_in_ctx.
        eapply Union_Disjoint_r. now sets.
        eapply Disjoint_Included; [| | eapply Hdis3 ].
        rewrite Setminus_Union_distr. rewrite !image_Union. now xsets. now sets.
      + eapply Disjoint_Included_l; [| eassumption ]. normalize_bound_var. sets.
      + eapply Disjoint_Included_r. eapply bound_var_occurs_free_Econstr_Included. eassumption.
      + eapply fun_map_vars_set. eassumption.
      + intros e' w2. eapply return_triple.
        intros _ st'. intros [Hf1 [Hf2 [Hf3 [Hf4 [Hun [Hsub [Hsub' [Hsh  Hsem]]]]]]]].
        split; [| split; [| split; [| split; [| split; [| split ]]]]].
        * eapply fresh_monotonic;[| eassumption ]. sets.
        * zify; lia.
        * constructor; [| eassumption ].
          intros Hc. eapply Hsub' in Hc. eapply Disjoint_Range; [| constructor; [ eapply Hf1 | eapply Hc ]].
          reflexivity.
        * repeat normalize_occurs_free. rewrite !image_Union.
          rewrite <- FromList_apply_list. rewrite <- !Union_assoc. eapply Included_Union_compat. reflexivity.
          eapply Included_trans. eapply Included_Setminus_compat.
          eapply Included_trans. eassumption. now eapply image_apply_r_set. reflexivity.
          rewrite !Setminus_Union_distr. rewrite Setminus_Same_set_Empty_set. normalize_sets.
          rewrite image_Union. sets.
        * normalize_bound_var. eapply Union_Included. eapply Included_trans. eassumption.
          eapply Range_Subset. zify; lia. reflexivity.
          eapply Included_trans. eapply Singleton_Included. eassumption. eapply Range_Subset. reflexivity.
          zify; lia.
        * eauto.
        * intros r1 r2 k Henv Hfm'. eapply preord_exp_constr_compat.
          now eauto. now eauto.
          eapply Forall2_preord_var_env_map. eassumption. normalize_occurs_free. now sets.
          intros. eapply Hsem.
          rewrite apply_r_set_f_eq. eapply preord_env_P_inj_set_alt.
          -- eapply preord_env_P_inj_antimon. eapply preord_env_P_inj_monotonic; [| eassumption ].
             lia. normalize_occurs_free. sets.
          -- rewrite preord_val_eq. split. reflexivity.
             eassumption.
          -- intros Hc. eapply Hdis3. constructor. eapply Hf'. eapply Hf1.
             normalize_occurs_free. eapply image_monotonic; [| eassumption ]. sets.
          -- eapply fun_map_inv_antimon. eapply fun_map_inv_set. eapply fun_map_inv_i_mon. eassumption. lia.
             intros Hc. inv Hc.
             ++ eapply Hdis1. normalize_bound_var. normalize_occurs_free. constructor. now right. eauto.
             ++ eapply Hdis4. constructor. normalize_bound_var. now right. eassumption.
             ++ intros Hc. eapply Hdis3. constructor; try eassumption. rewrite image_Union. right. eassumption.
             ++ normalize_occurs_free. rewrite !Union_assoc. rewrite Union_Setminus_Included; sets; tci.
    - (* Ecase [] *)
      simpl. eapply bind_triple.
      eapply return_triple
        with (Q := fun r w l w' => fresh S (next_var (fst w)) /\ fresh S (next_var (fst w')) /\ l = [] /\ next_var (fst w) <= next_var (fst w')).
      now intros; eauto.
      intros xs w'. simpl. eapply return_triple. simpl; intros.  destructAll.
      split; [| split; [| split; [| split; [| split; [| split ]]]]]; eauto.
      + constructor.
      + simpl. normalize_occurs_free. sets.
      + normalize_bound_var. sets.
      + intros. eapply preord_exp_case_nil_compat. now eauto.
    - (* Ecase (_ :: _) *)
      unfold inline_exp. simpl. setoid_rewrite assoc at 1. eapply bind_triple.
      + eapply pre_transfer_r. eapply IHe.
        * eassumption.
        * repeat normalize_bound_var_in_ctx. repeat normalize_occurs_free_in_ctx.
          eapply Disjoint_Included; [| | eapply Hdis1 ]; sets.
        * repeat normalize_bound_var_in_ctx. repeat normalize_occurs_free_in_ctx.
          xsets.
        * repeat normalize_bound_var_in_ctx. repeat normalize_occurs_free_in_ctx. now sets.
        * eapply Disjoint_Included_r. eapply bound_var_occurs_free_Ecase_Included. 2:{ eassumption. }
          now left.
        * eassumption.
      + intros e' w. simpl.
        eapply pre_curry_l. intros Hf'. eapply pre_strenghtening.
        { intros. destructAll.
          eapply (conj H8 (conj H7 (conj H3 (conj H1 (conj H6 (conj H0 H)))))). }

        eapply pre_curry_l. intros Hrel. eapply pre_curry_l. intros Hcase.
        eapply pre_curry_l. intros Hfv. eapply pre_curry_l. intros Hun.
        setoid_rewrite st_eq_Ecase. eapply bind_triple.
        * setoid_rewrite inline_exp_eq in IHl. unfold inline_exp' in IHl.
          do 2 eapply frame_rule. eapply pre_transfer_r.
          eapply IHl.
          -- eassumption.
          -- repeat normalize_bound_var_in_ctx. repeat normalize_occurs_free_in_ctx.
             eapply Disjoint_Included; [| | eapply Hdis1 ]; sets.
          -- repeat normalize_bound_var_in_ctx. repeat normalize_occurs_free_in_ctx.
             xsets.
          -- repeat normalize_bound_var_in_ctx. repeat normalize_occurs_free_in_ctx. now sets.
          -- eapply Disjoint_Included_r. eapply bound_var_occurs_free_Ecase_cons_Included. eassumption.
          -- eassumption.
        * intros ce w'. simpl. eapply pre_curry_l. intros Hbv. eapply pre_curry_l. intros Hleq1.
          eapply pre_curry_l. intros Hf''.
          eapply pre_strenghtening.
          { intros. destruct H as (H1 & H2' & H3 & H4' & H5' & H6 & H7).
            eapply (conj H6 (conj H1 (conj H2' (conj H3 (conj H4' (conj H5' H7)))))). }
          eapply pre_curry_l. intros Hex. destructAll.
          eapply return_triple. intros. destructAll.
          split; [| split; [| split; [| split; [| split; [| split ]]]]]; eauto.
          ++ zify; lia.
          ++ constructor. eassumption. eassumption.
             eapply Disjoint_Included. eassumption. eassumption. eapply Disjoint_Range. reflexivity.
          ++ repeat normalize_occurs_free. eapply Union_Included; [| eapply Union_Included ].
             ** rewrite !image_Union, image_Singleton. sets.
             ** eapply Included_trans. eassumption. sets.
             ** eapply Included_trans. eassumption. sets.
          ++ normalize_bound_var. eapply Union_Included.
             ** eapply Included_trans. eassumption. eapply Range_Subset. reflexivity. eassumption.
             ** eapply Included_trans. eassumption. eapply Range_Subset. eassumption. reflexivity.
          ++ intros. eapply preord_exp_case_cons_compat.
             ** now eauto.
             ** now eauto.
             ** now eauto.
             ** now eauto.
             ** eapply H9. now constructor.
             ** intros. eapply Hrel.
                --- eapply preord_env_P_inj_monotonic; [| eapply preord_env_P_inj_antimon; [ eassumption | ]].
                    lia. normalize_occurs_free. sets.
                --- eapply fun_map_inv_antimon. eapply fun_map_inv_i_mon. eassumption. lia.
                    normalize_occurs_free. sets.
             ** eapply H8.
                --- eapply preord_env_P_inj_monotonic; [| eapply preord_env_P_inj_antimon; [ eassumption | ]].
                    lia. normalize_occurs_free. sets.
                --- eapply fun_map_inv_antimon. eassumption.
                    normalize_occurs_free. sets.
    - (* Eproj *)
      eapply bind_triple. eapply pre_transfer_r. now eapply get_fresh_name_spec.
      intros x w1. simpl. eapply pre_curry_l. intros Hf'.  eapply pre_curry_l. intros Hsin.
      eapply bind_triple. eapply frame_rule. eapply frame_rule. eapply IHe with (S := S \\ [set x]).
      + eassumption.
      + repeat normalize_bound_var_in_ctx. repeat normalize_occurs_free_in_ctx.
        eapply Disjoint_Included_r. eapply @Included_Union_Setminus with (s2 := [set v]). tci.
        eapply Union_Disjoint_r. eapply Disjoint_Included; [| | eapply Hdis1 ]; sets. rewrite Setminus_Union_distr. sets.
        eapply Disjoint_Singleton_r. eassumption.
      + eapply Disjoint_Included_r.
        eapply image_apply_r_set.
        repeat normalize_bound_var_in_ctx. repeat normalize_occurs_free_in_ctx.
        eapply Union_Disjoint_r. now sets.
        eapply Disjoint_Included; [| | eapply Hdis3 ].
        rewrite Setminus_Union_distr. rewrite !image_Union. now xsets. now sets.
      + eapply Disjoint_Included_l; [| eassumption ]. normalize_bound_var. sets.
      + eapply Disjoint_Included_r. eapply bound_var_occurs_free_Eproj_Included. eassumption.
      + eapply fun_map_vars_set. eassumption.
      + intros e' w2. eapply return_triple.
        intros _ st'. intros [Hf1 [Hf2 [Hf3 [Hf4 [Hun [Hsub [Hsub' [Hsh Hsem]]]]]]]].
        split; [| split; [| split; [| split; [| split; [| split ]]]]].
        * eapply fresh_monotonic;[| eassumption ]. sets.
        * zify; lia.
        * constructor; [| eassumption ].
          intros Hc. eapply Hsub' in Hc. eapply Disjoint_Range; [| constructor; [ eapply Hf1 | eapply Hc ]].
          reflexivity.
        * repeat normalize_occurs_free. rewrite !image_Union, image_Singleton. eapply Union_Included. now sets.
          eapply Included_trans. eapply Included_Setminus_compat.
          eapply Included_trans. eassumption. now eapply image_apply_r_set. reflexivity.
          rewrite !Setminus_Union_distr. rewrite Setminus_Same_set_Empty_set. normalize_sets.
          rewrite image_Union. sets.
        * normalize_bound_var. eapply Union_Included. eapply Included_trans. eassumption.
          eapply Range_Subset. zify; lia. reflexivity.
          eapply Included_trans. eapply Singleton_Included. eassumption. eapply Range_Subset. reflexivity.
          zify; lia.
        * eauto.
        * intros r1 r2 k Henv Hfm'. eapply preord_exp_proj_compat.
          now eauto. now eauto. eapply Henv. now constructor.
          intros. eapply Hsem.
          rewrite apply_r_set_f_eq. eapply preord_env_P_inj_set_alt.
          -- eapply preord_env_P_inj_antimon. eapply preord_env_P_inj_monotonic; [| eassumption ].
             lia. normalize_occurs_free. sets.
          -- eassumption.
          -- intros Hc. eapply Hdis3. constructor. eapply Hf'. eapply Hf1.
             normalize_occurs_free. eapply image_monotonic; [| eassumption ]. sets.
          -- eapply fun_map_inv_antimon. eapply fun_map_inv_set. eapply fun_map_inv_i_mon. eassumption. lia.
             intros Hc. inv Hc.
             ++ eapply Hdis1. normalize_bound_var. constructor. now right. now right; eauto.
             ++ eapply Hdis4. constructor. normalize_bound_var. now right. eassumption.
             ++ intros Hc. eapply Hdis3. constructor; try eassumption. rewrite image_Union. right. eassumption.
             ++ normalize_occurs_free. rewrite !Union_assoc. rewrite Union_Setminus_Included; sets; tci.
    - (* Eletapp *)
      simpl. Opaque inline_exp.  destruct (update_letApp St IH f ft (apply_r_list sig ys) st) as [[s1 s2] b].
      match goal with
      | [ _ : _ |- {{ ?P }} (if _ then _ else ?E) {{ ?Q }} ] => set (Lemm := {{ P }} E {{ Q }})
      end.
      assert (Hsame : Lemm).
      { unfold Lemm. eapply bind_triple. eapply pre_transfer_r. eapply get_fresh_name_spec. intros x' w1.
        simpl. eapply pre_curry_l. intros Hf'. eapply pre_curry_l. intros HSin.
        eapply bind_triple. eapply frame_rule. eapply frame_rule. eapply IHe with (S := S \\ [set x']).
        - eassumption.
        - repeat normalize_bound_var_in_ctx. repeat normalize_occurs_free_in_ctx.
          eapply Disjoint_Included_r. eapply @Included_Union_Setminus with (s2 := [set x]). tci.
          eapply Union_Disjoint_r. eapply Disjoint_Included; [| | eapply Hdis1 ]; sets.
          rewrite Setminus_Union_distr. now sets. eapply Disjoint_Singleton_r. eassumption.
        - repeat normalize_bound_var_in_ctx. repeat normalize_occurs_free_in_ctx.
          eapply Disjoint_Included_r.
          eapply image_apply_r_set.
          eapply Union_Disjoint_r. now sets.
          eapply Disjoint_Included; [| | eapply Hdis3 ]; [| now sets ].
          eapply image_monotonic. rewrite Setminus_Union_distr. sets.
        - eapply Disjoint_Included_l; [| eassumption ]. normalize_bound_var. sets.
        - eapply Disjoint_Included_r. eapply bound_var_occurs_free_Eletapp_Included. eassumption.
        - eapply fun_map_vars_set. eassumption.
        - intros e' w2. eapply return_triple.
          intros _ st'. intros [Hf1 [Hf2 [Hf3 [Hf4 [Hun [Hsub [Hsub' [Hsh Hsem]]]]]]]].
          split; [| split; [| split; [| split; [| split; [| split ]]]]].
          * eapply fresh_monotonic;[| eassumption ]. sets.
          * zify; lia.
          * constructor; [| eassumption ].
            intros Hc. eapply Hsub' in Hc. eapply Disjoint_Range; [| constructor; [ eapply Hf1 | eapply Hc ]].
            reflexivity.
          * repeat normalize_occurs_free. rewrite !image_Union.
            rewrite <- FromList_apply_list. rewrite <- !Union_assoc. eapply Included_Union_compat.
            rewrite image_Singleton. now sets. eapply Union_Included. now sets.
            eapply Included_trans. eapply Included_Setminus_compat.
            eapply Included_trans. eassumption. now eapply image_apply_r_set. reflexivity.
            rewrite !Setminus_Union_distr. rewrite Setminus_Same_set_Empty_set. normalize_sets.
            rewrite image_Union. rewrite !Setminus_Union_distr. eapply  Union_Included; xsets.
          * normalize_bound_var. eapply Union_Included. eapply Included_trans. eassumption.
            eapply Range_Subset. zify; lia. reflexivity.
            eapply Included_trans. eapply Singleton_Included. eassumption. eapply Range_Subset. reflexivity.
            zify; lia.
          * simpl; eauto.
          * intros r1 r2 k Henv Hfm'. eapply preord_exp_letapp_compat.
            now eauto. now eauto. now eauto.
            eapply Henv. econstructor. now left.
            eapply Forall2_preord_var_env_map. eassumption. normalize_occurs_free. now sets.
            intros. eapply Hsem.
            rewrite apply_r_set_f_eq. eapply preord_env_P_inj_set_alt.
            -- eapply preord_env_P_inj_antimon. eapply preord_env_P_inj_monotonic; [| eassumption ].
               lia. normalize_occurs_free. sets.
            -- eassumption.
            -- intros Hc. eapply Hdis3. constructor. eapply Hf'. eapply Hf1.
               normalize_occurs_free. rewrite !image_Union. left. right. eassumption.
            -- eapply fun_map_inv_antimon. eapply fun_map_inv_set. eapply fun_map_inv_i_mon. eassumption. lia.
               intros Hc. inv Hc.
               ++ eapply Hdis1. constructor. normalize_bound_var. now right. right; eassumption.
               ++ eapply Hdis4. constructor. normalize_bound_var. now right. eassumption.
               ++ intros Hc. eapply Hdis3. constructor. eassumption. rewrite image_Union.
                  right. eassumption.
               ++ normalize_occurs_free. rewrite !Union_assoc. rewrite Union_Setminus_Included; sets; tci. }

      destruct b.
      + destruct (fm ! f) as [ [[? ?] ?] | ] eqn:Hf'.
        * destruct d. eassumption.
          destruct j. eassumption.
          destruct (Datatypes.length l =? Datatypes.length ys)%nat eqn:Hlen; [| eassumption ].
          eapply Nat.eqb_eq in Hlen.
          eapply bind_triple. eapply pre_transfer_r. now eapply get_fresh_name_spec.
          intros z w. simpl. eapply pre_curry_l. intros Hfx. eapply pre_curry_l. intros HSin.
          { edestruct Hfm. eassumption. destructAll. eapply bind_triple.
            - do 2 eapply frame_rule. eapply pre_transfer_r. eapply IHd.
              + lia.
              + eapply Nat.le_trans. reflexivity.
                eapply Nat.div2_decr. lia.
              + eassumption.
              + eapply Union_Disjoint_r. clear H3. now sets. now sets.
              + repeat normalize_bound_var_in_ctx. repeat normalize_occurs_free_in_ctx.
                eapply Disjoint_Included_r.
                eapply image_apply_r_set_list. unfold apply_r_list. rewrite length_map. eassumption.
                eapply Union_Disjoint_r.
                rewrite FromList_apply_list.
                eapply Disjoint_Included; [| | eapply Hdis3 ]; [| now sets ]. rewrite !image_Union. now sets.

                rewrite !Setminus_Union_distr. rewrite image_Union. eapply Union_Disjoint_r.
                eapply Disjoint_Included; [| | eapply H8 ]; now sets.
                eapply Disjoint_Included; [| | eapply Hdis3 ].
                eapply Included_trans. eapply image_monotonic. eapply Included_Setminus_compat.
                eapply occurs_free_fun_map_remove. reflexivity. now sets. now sets.
              + rewrite Dom_map_remove. sets.
              + sets.
              + eapply fun_map_vars_inv_remove.
                intros ? ? ? ? ?.
                edestruct Hfm; eauto. destructAll.
                repeat (split; [ now eauto |]).
                eapply Disjoint_Included_r. eapply image_apply_r_set_list.
                unfold apply_r_list. rewrite list_length_map. eassumption.
                eapply Union_Disjoint_r.
                eapply Disjoint_Included; [| | eapply Hdis3 ]. normalize_occurs_free.
                rewrite !image_Union. rewrite FromList_apply_list. now sets. now sets. now xsets.
            - intros ei w'. simpl. eapply pre_curry_l; intros Hfr. eapply pre_curry_l; intros Hleq1.
              eapply pre_curry_l; intros Hfz.
              destruct (inline_letapp ei z) as [ [C r] | ] eqn:Hinl.
              eapply pre_strenghtening.
              { intros. destructAll.
                assert (Hfr' : fresh (S \\ [set z] \\ bound_var ei) (next_var (fst s))).
                { intros u Hleq'. constructor. eapply H9; eauto.
                  intros Hnin. eapply H13 in Hnin. unfold Ensembles.In, Range in Hnin. zify. lia. }
                assert (Hbv : bound_var ei \subset S \\ [set z]).
                { eapply Included_trans. eassumption. intros y Hin. unfold Ensembles.In, Range in *. inv Hin.
                  eapply Hfz. eassumption. }

                eapply (conj Hbv (conj H15 (conj H14 (conj H12 (conj H11 (conj H9 (conj H10 (conj H13 Hfr')))))))). }

              eapply pre_curry_l. intros Hbv. eapply pre_curry_l. intros Hrel.
              eapply pre_curry_l. intros Hcase. eapply pre_curry_l. intros Hfv. eapply pre_curry_l. intros Hun.


              assert (Hdisr : Disjoint var (S \\ [set z] \\ bound_var ei) [set r]).
              { edestruct inline_letapp_var_eq. eassumption.
                - subst. now sets.
                - repeat normalize_bound_var_in_ctx. repeat normalize_occurs_free_in_ctx.
                  inv H9.
                  + eapply Disjoint_Included_r. eapply Singleton_Included. eassumption. sets.
                  + eapply Disjoint_Included_r. eapply Included_trans. eapply Singleton_Included. eassumption.
                    eassumption.
                    eapply Disjoint_Included_r. eapply image_apply_r_set_list. unfold apply_r_list. rewrite length_map. now eauto.
                    rewrite !Setminus_Union_distr, image_Union.
                    eapply Union_Disjoint_r; [| eapply Union_Disjoint_r ].
                    rewrite FromList_apply_list. eapply Disjoint_Included; [| | eapply Hdis3 ]; now sets.
                    now sets.
                    eapply Disjoint_Included_r. eapply image_monotonic. eapply Included_Setminus_compat.
                    eapply occurs_free_fun_map_remove. reflexivity.
                    eapply Disjoint_Included; [| | eapply Hdis3 ]; now sets. }

              eapply bind_triple.
              eapply click_spec with (P := fun s => fresh (S \\ [set z]) (next_var s) /\
                                                    next_var (fst w') <= next_var s /\
                                                    bound_var ei \subset Range (next_var (fst w')) (next_var s) /\
                                                    fresh (S \\ [set z] \\ bound_var ei) (next_var s)).
              intros _u w''. simpl.
              eapply bind_triple.
              + do 3 eapply frame_rule.
                { eapply IHd.
                  + lia.
                  + eapply Nat.le_trans; [| eassumption ].
                    assert (Heq := split_fuel_add j). rewrite Heq at 3. unfold split_fuel. simpl. lia.
                  + eassumption.
                  + repeat normalize_bound_var_in_ctx. repeat normalize_occurs_free_in_ctx.
                    eapply Disjoint_Included_r. eapply @Included_Union_Setminus with (s2 := [set x]). tci.
                    eapply Union_Disjoint_r. rewrite Setminus_Union_distr. now eapply Disjoint_Included; [| | eapply Hdis1 ]; sets.
                    eapply Disjoint_Singleton_r. eassumption.
                  + repeat normalize_bound_var_in_ctx. repeat normalize_occurs_free_in_ctx.
                    eapply Disjoint_Included_r.
                    eapply image_apply_r_set. eapply Union_Disjoint_r. now sets.
                    eapply Disjoint_Included; [| | eapply Hdis3 ]. rewrite Setminus_Union_distr. now sets. now sets.
                  + repeat normalize_bound_var_in_ctx. repeat normalize_occurs_free_in_ctx.
                    eapply Disjoint_Included_l; [| eapply Hdis4 ]. simpl. sets.
                  + eapply Disjoint_Included_r. eapply bound_var_occurs_free_Eletapp_Included. eassumption.
                  + (* Make lemma if needed about fun_map_vars fm S (set_list (combine xs (apply_r_list sig l)) sig) *)
                    intros ? ? ? ? ?. edestruct Hfm; eauto. destructAll.
                    repeat (split; [ now eauto |]).
                    eapply Disjoint_Included_r. eapply image_apply_r_set.
                    eapply Union_Disjoint_r. now sets. now xsets. }
              + intros e' w'''. eapply return_triple. intros _ w'''' Hyp. destructAll.
                split; [| split; [| split; [| split; [| split; [| split ]]]]].
                * eapply fresh_monotonic; [| eassumption ]. sets.
                * zify; lia.
                * eapply (proj1 (ub_app_ctx_f e')). split; [| split ]; [| eassumption |].
                  eapply unique_bindings_inline_letapp; [ eassumption | | eassumption ].
                  intros Hc. eapply H11 in Hc.
                  unfold Ensembles.In, Range in Hc, Hfr. zify; lia.
                  eapply Disjoint_Included_l. eapply bound_var_inline_letapp. eassumption.
                  eapply Union_Disjoint_l.
                  -- eapply Disjoint_Included_r. eassumption. eapply Disjoint_Singleton_l.
                     intros Hc. unfold Ensembles.In, Range in Hc, Hfr. zify; lia.
                  -- eapply Disjoint_Included. eassumption. eassumption.
                     eapply Disjoint_Range. reflexivity.
                * eapply Included_trans. eapply occurs_fee_inline_letapp. eassumption.
                  assert (Hsub : occurs_free ei :|: (occurs_free e' \\ stemctx.bound_stem_ctx C) \subset
                                             occurs_free ei :|: (occurs_free e' \\ [set r])).
                  { edestruct inline_letapp_var_eq_alt. eassumption. inv H19; subst. now sets.
                    inv H19. now sets. rewrite @Union_Setminus_Included with (s3 := [set r]); tci. sets.
                    sets. }
                  eapply Included_trans. eassumption. eapply Union_Included.
                  -- eapply Included_trans. eassumption. eapply Included_trans.
                     eapply image_apply_r_set_list. unfold apply_r_list. rewrite length_map. eassumption.
                     normalize_occurs_free. rewrite Setminus_Union_distr, !image_Union. eapply Union_Included.
                     rewrite FromList_apply_list. now sets.
                     eapply Union_Included. eapply Included_trans.
                     eapply image_monotonic. eapply occurs_free_fun_map_get. eassumption. sets.
                     eapply Included_trans. eapply image_monotonic. eapply Included_Setminus_compat.
                     eapply occurs_free_fun_map_remove. reflexivity. sets.
                  -- eapply Included_trans. eapply Included_Setminus_compat.
                     eapply Included_trans. eassumption. eapply image_apply_r_set. reflexivity.
                     rewrite Setminus_Union_distr. eapply Union_Included. now sets.
                     normalize_occurs_free. rewrite !Setminus_Union_distr. now sets.
                * rewrite bound_var_app_ctx. eapply Union_Included.
                  -- eapply Included_trans. eapply bound_var_inline_letapp. eassumption.
                     eapply Union_Included.
                     eapply Singleton_Included. unfold Ensembles.In, Range in *. zify; lia.
                     eapply Included_trans. eassumption. eapply Range_Subset. zify; lia. zify; lia.
                  -- eapply Included_trans. eassumption. eapply Range_Subset. zify; lia. zify; lia.
                * eauto.
                * intros. assert (Hadd := split_fuel_add j).
                  unfold split_fuel in *. simpl in Hadd. rewrite Hadd.
                  eapply inline_letapp_correct_alt with (C' := Hole_c);
                            [ | | | | | | |  now eauto | eassumption ].
                  -- eapply HEletapp.
                  -- eapply Eletapp_OOT.
                  -- eapply HProp.
                     eapply Nat.le_trans; [| eassumption ]. rewrite Hadd at 4. simpl. lia.
                  -- simpl. intros. edestruct (H20 f). constructor. now left. eassumption. eassumption.
                     destructAll. do 2 subst_exp. eapply Hrel.
                     ++ edestruct preord_env_P_inj_get_list_l. now eapply H19. normalize_occurs_free. now sets.
                        eassumption. destructAll.
                        eapply preord_env_P_inj_set_lists_l'; try eassumption.
                        eapply preord_env_P_inj_monotonic; [| eassumption ]. lia.
                        eapply List_util.Forall2_monotonic; [| eassumption ].
                        intros. eapply preord_val_monotonic. eassumption. lia.
                     ++ eapply fun_map_inv_antimon. eapply fun_map_inv_set_lists; [ | | | eassumption ].
                        ** eapply fun_map_inv_sig_extend_Disjoint. rewrite <- fun_map_inv_eq in *.
                           eapply fun_map_inv_i_mon. eapply fun_map_inv_remove.
                           eapply fun_map_inv_mon. eassumption. lia. lia. sets.
                        ** eassumption.
                        ** eapply Union_Disjoint_r. now sets. rewrite Dom_map_remove. sets.
                        ** rewrite Union_Setminus_Included. sets. tci. sets.
                  -- intros. edestruct (H20 f). constructor. now left. eassumption. eassumption.
                     destructAll. subst_exp. eapply H18.
                     ++ rewrite apply_r_set_f_eq. eassumption.
                     ++ eapply fun_map_inv_antimon.
                        2:{ eapply Included_trans. eapply @Included_Union_Setminus with (s2 := [set x]); tci.
                            rewrite Union_commut. reflexivity. }
                        eapply fun_map_inv_sig_extend_one_Disjoint.
                        ** eapply fun_map_inv_env_eq_P.
                           eapply fun_map_inv_antimon. eapply fun_map_inv_mon.
                           eapply fun_map_inv_i_mon. eassumption. lia. lia. normalize_occurs_free. now sets.

                           eapply eq_env_P_refl.
                           eapply eq_env_P_antimon. eassumption.
                           normalize_bound_var_ctx. normalize_sets. intros y Hin Hin'.
                           eapply bound_var_inline_letapp in Hin'; [| eassumption ]. eapply Hdis3.
                           constructor. 2:{ rewrite image_Union. right. eassumption. }
                           inv Hin'. inv H29.
                           eapply Hfx. unfold Ensembles.In, Range in *. zify; lia.
                           eapply H11 in H29. eapply Hfx. unfold Ensembles.In, Range in *. zify; lia.
                        ** eassumption.
                        ** intros Hc. eapply Hdis4. constructor. 2:{ eassumption. } now eauto.
                        ** intros Hc. eapply Hdis1. constructor. now constructor. now eauto.
                        ** intros Hc. inv Hc; eauto.
                  -- eassumption.
                  -- normalize_bound_var_ctx. normalize_sets.
                     eapply Disjoint_Included_l. eapply bound_var_inline_letapp. eassumption.
                     eapply Disjoint_Included; [| | eapply Hdis3 ]. normalize_occurs_free. rewrite image_Union. now sets.
                     eapply Union_Included. intros u Hc. inv Hc. eapply Hfx. unfold Ensembles.In, Range in *. zify; lia.
                     intros u Hc. eapply H11 in Hc. unfold Ensembles.In, Range in *. eapply Hfx. zify; lia.
             + eapply post_weakening.
                2:{ eapply pre_transfer_r. eapply pre_strenghtening. 2:{
                      eapply post_weakening; [| eassumption ]. simpl. intros.
                      eapply (conj H9 H10). }
                    simpl. intros.  destructAll. eapply fresh_monotonic; [| eassumption ]. sets. }
                simpl. intros. destructAll.
                split; [| split; [| split; [| split; [| split ]]]]; eauto.
                * zify; lia.
                * eapply Included_trans. eassumption. eapply Range_Subset; eauto.
                  zify; lia. zify; lia. }
        * eassumption.
      + eassumption.
    - (* Efun *)
      simpl. destruct (update_funDef St IH f2 sig st).
      eapply bind_triple. eapply pre_transfer_r. now eapply get_fresh_names_spec. intros xs w. simpl.
      eapply pre_curry_l. intros Hf'. eapply pre_curry_l. intros Hnd.  eapply pre_curry_l. intros Hlen.

      assert (Hfm' : fun_map_vars (add_fundefs f2 fm) (S \\ FromList xs) (set_list (combine (all_fun_name f2) xs) sig)).
      { eapply fun_map_vars_def_funs; (try now eauto).
        + repeat normalize_bound_var_in_ctx. repeat normalize_occurs_free_in_ctx.
          eapply Disjoint_Included; [| | eapply Hdis1 ]; sets.
        + repeat normalize_bound_var_in_ctx. repeat normalize_occurs_free_in_ctx. sets.
        + repeat normalize_bound_var_in_ctx. repeat normalize_occurs_free_in_ctx. sets.
        + repeat normalize_bound_var_in_ctx. repeat normalize_occurs_free_in_ctx. xsets. }

      assert (Hnd' := NoDup_all_fun_name _ H2).
      assert (Hseq :  apply_r_list (set_list (combine (all_fun_name f2) xs) sig) (all_fun_name f2) = xs).
      { rewrite apply_r_list_eq. reflexivity. now eauto. now eauto. }
      eapply pre_curry_l. intros Hin.
      eapply bind_triple.
      { do 2 eapply frame_rule. eapply IHB with (S := S \\ FromList xs).
        - eassumption.
        - repeat normalize_occurs_free_in_ctx. repeat normalize_bound_var_in_ctx. eapply Union_Disjoint_r.
          eapply Disjoint_Included; [| | eapply Hdis1 ]; now sets.
          eapply Disjoint_Included_r.
          eapply Included_Setminus_compat. now eapply occurs_free_fun_map_add_fundefs. reflexivity.
          rewrite !Setminus_Union_distr. rewrite Setminus_Same_set_Empty_set. normalize_sets.
          eapply Disjoint_Included; [| | eapply Hdis1 ]; now sets.
        - repeat normalize_occurs_free_in_ctx. repeat normalize_bound_var_in_ctx.
          eapply Disjoint_Included_r. eapply image_apply_r_set_list. now eauto.
          rewrite <- Same_set_all_fun_name. rewrite !Setminus_Union_distr. rewrite !image_Union.
          repeat (eapply Union_Disjoint_r; sets).
          now xsets.
          eapply Disjoint_Included_r. eapply image_monotonic.
          eapply Included_Setminus_compat. eapply occurs_free_fun_map_add_fundefs. reflexivity. xsets.
        - repeat normalize_occurs_free_in_ctx. repeat normalize_bound_var_in_ctx.
          eapply Disjoint_Included_r. eapply Dom_map_add_fundefs. sets.
        - repeat normalize_occurs_free_in_ctx. repeat normalize_bound_var_in_ctx.
          eapply just_for_fun_inv_add_fundefs. eassumption. sets.
          eapply Disjoint_Included; [| | eapply Hdis1 ]; sets.
        - eassumption.
        - rewrite Hseq. eassumption.
        - rewrite Hseq. now sets. }

      intros fds' w'. simpl.
      eapply pre_curry_l. intros Hsub. eapply pre_curry_l. intros Hr.
      eapply bind_triple.
      { eapply pre_strenghtening.
        2:{ eapply frame_rule. eapply IHe with (S := S \\ FromList xs).
            + eassumption.
            + repeat normalize_bound_var_in_ctx. repeat normalize_occurs_free_in_ctx.
              * eapply Disjoint_Included_r. eapply Included_Union_Setminus with (s2 := name_in_fundefs f2). now tci.
                eapply Union_Disjoint_r. eapply Disjoint_Included; [| | eapply Hdis1 ]; try now sets.
                rewrite Setminus_Union_distr. eapply Union_Included. now sets.  eapply Included_trans.
                eapply Included_Setminus_compat. eapply occurs_free_fun_map_add_fundefs. reflexivity.
                rewrite !Setminus_Union_distr. rewrite !Setminus_Same_set_Empty_set. repeat normalize_sets. now sets.
                eapply Disjoint_Included_r. eapply name_in_fundefs_bound_var_fundefs. now sets.
            + repeat normalize_bound_var_in_ctx. repeat normalize_occurs_free_in_ctx.
              eapply Disjoint_Included_r.
              eapply image_apply_r_set_list. now eauto. eapply Union_Disjoint_r.
              * now sets.
              * rewrite <- Same_set_all_fun_name. rewrite Setminus_Union_distr.
                rewrite image_Union. eapply Union_Disjoint_r.
                eapply Disjoint_Included; [| | eapply Hdis3 ]. now sets. now sets.
                eapply Disjoint_Included_r. eapply image_monotonic. eapply Included_Setminus_compat.
                eapply occurs_free_fun_map_add_fundefs. reflexivity.
                rewrite !Setminus_Union_distr. rewrite !Setminus_Same_set_Empty_set. repeat normalize_sets.
                eapply Disjoint_Included; [| | eapply Hdis3 ]. now sets. now sets.
            + repeat normalize_bound_var_in_ctx. repeat normalize_occurs_free_in_ctx.
              rewrite Dom_map_add_fundefs. eapply Union_Disjoint_r.
              * eapply Disjoint_Included_r. eapply name_in_fundefs_bound_var_fundefs. now sets.
              * sets.
            + repeat normalize_bound_var_in_ctx. repeat normalize_occurs_free_in_ctx.
              eapply Disjoint_Included_l.
              * eapply bound_var_fun_map_add_fundefs_un. eassumption.
              * eapply Union_Disjoint_l.
                -- eapply Union_Disjoint_r. now sets.
                   eapply Disjoint_Included_r.
                   eapply Included_Union_Setminus with (s2 := name_in_fundefs f2). tci.
                   eapply Union_Disjoint_r; [| now sets ].
                   eapply Disjoint_Included; [| | eapply Hdis1 ]; now sets.
                -- eapply Union_Disjoint_r. now sets.
                   eapply Disjoint_Included; [| | eapply Hdis5 ]; [| now sets ].
                   rewrite !Union_assoc. rewrite Union_commut. rewrite <- Union_Included_Union_Setminus.
                   now sets. now tci.  eapply Included_trans. eapply name_in_fundefs_bound_var_fundefs. now sets.
            + eassumption. }

        simpl. intros u w1 [Hyp Hyp']. split. eapply Hyp'. eassumption. }


      intros e' w''. eapply return_triple. intros _ w''' Hyp. destructAll.
      split; [| split; [| split; [| split; [| split; [| split ]]]]].
      * eapply fresh_monotonic; [| eassumption ]. sets.
      * zify; lia.
      * constructor. eassumption. eassumption.
        eapply Disjoint_Included_r. eapply Included_Union_Setminus with (s2 := name_in_fundefs fds'). now tci.
        eapply Union_Disjoint_r.
        -- eapply Disjoint_Included. eassumption. eassumption.
           eapply Disjoint_sym. eapply Disjoint_Range. reflexivity.
        -- rewrite Same_set_all_fun_name. rewrite H13. rewrite Hseq.
           eapply Disjoint_Included. eassumption. eassumption.
           eapply Disjoint_sym. eapply Disjoint_Range. zify; lia.
      * repeat normalize_occurs_free. eapply Union_Included.
        -- eapply Included_trans. eapply Included_Setminus. eapply Disjoint_sym.
           eapply occurs_free_fundefs_name_in_fundefs_Disjoint. reflexivity.
           eapply Setminus_Included_Included_Union. eapply Included_trans. eassumption.
           eapply Included_trans. eapply image_apply_r_set_list. now eauto.
           rewrite (Same_set_all_fun_name fds'). rewrite H13.
           rewrite apply_r_list_eq; eauto. eapply Union_Included. now sets.
           eapply Included_Union_preserv_l. rewrite <- Same_set_all_fun_name.
           rewrite Setminus_Union_distr. rewrite !image_Union. eapply Union_Included. now sets.
           eapply Included_trans. eapply image_monotonic. eapply Included_Setminus_compat.
           eapply occurs_free_fun_map_add_fundefs. reflexivity. rewrite !Setminus_Union_distr, Setminus_Same_set_Empty_set.
           normalize_sets. rewrite !image_Union. xsets.
        -- eapply Included_trans. eapply Included_Setminus_compat. eassumption. reflexivity.
           eapply Setminus_Included_Included_Union.
           eapply Included_trans. eapply image_apply_r_set_list. now eauto.
           rewrite (Same_set_all_fun_name fds'). rewrite H13.
           rewrite apply_r_list_eq; eauto. eapply Union_Included. now sets.
           eapply Included_Union_preserv_l. rewrite <- Same_set_all_fun_name.
           rewrite Setminus_Union_distr. rewrite !image_Union. eapply Union_Included. now sets.
           eapply Included_trans. eapply image_monotonic. eapply Included_Setminus_compat.
           eapply occurs_free_fun_map_add_fundefs. reflexivity.
           rewrite !Setminus_Union_distr, Setminus_Same_set_Empty_set. repeat normalize_sets.
           rewrite image_Union. now xsets.
      * normalize_bound_var. eapply Union_Included.
        -- eapply Included_trans.
           eapply Included_Union_Setminus with (s2 := name_in_fundefs fds'). now tci. eapply Union_Included.
           ++ eapply Included_trans. eassumption. eapply Range_Subset; zify; lia.
           ++ rewrite Same_set_all_fun_name. rewrite H13. rewrite Hseq.
              eapply Included_trans. eassumption. eapply Range_Subset; zify; lia.
        -- eapply Included_trans. eassumption. eapply Range_Subset. zify; lia. reflexivity.
      * eauto.
      * intros k rho1 rho2 Henv Hfm''. eapply preord_exp_fun_compat.
        now eauto. now eauto.
        assert (Hrel : preord_env_P_inj cenv PG
                                        (name_in_fundefs f2 :|: occurs_free (Efun f2 e))
                                        (k - 1) (apply_r (set_list (combine (all_fun_name f2) xs) sig))
                                        (def_funs f2 f2 rho1 rho1) (def_funs fds' fds' rho2 rho2)).
        { assert (Hi : (k - 1 <= k)%nat) by lia.
          revert Hi. generalize (k - 1)%nat as i. intros i Hi. induction i as [i IHi] using lt_wf_rec1.
          intros x HIn v Hgetx. destruct (Decidable_name_in_fundefs f2). destruct (Dec x).
          - rewrite def_funs_eq in Hgetx; [| now eauto ]. inv Hgetx. eexists. split.
            + rewrite def_funs_eq. reflexivity. eapply Same_set_all_fun_name.
              rewrite H13. rewrite FromList_apply_list. eapply In_image.
              rewrite <- Same_set_all_fun_name. eassumption.
            + rewrite preord_val_eq. intros vs1 vs2 j' t1 ys1 e2 rho1' Hlen' Hfind Hset.
              edestruct H14. eassumption. destructAll.
              edestruct set_lists_length2 with (xs2 := x0) (vs2 := vs2) (rho' := def_funs fds' fds' rho2 rho2).
              now eauto. eassumption. now eauto. do 3 eexists. split. eassumption. split. now eauto.
              intros Hlt Hvs. eapply preord_exp_post_monotonic. eassumption. eapply H19.
              * eapply preord_env_P_inj_set_lists_alt; [| eassumption | | | | | now eauto | now eauto ].
                -- eapply preord_env_P_inj_antimon. eapply IHi. eassumption. lia.
                   normalize_occurs_free. sets.
                -- eapply unique_bindings_fun_in_fundefs. eapply find_def_correct. eassumption.
                   eassumption.
                -- eassumption.
                -- eassumption.
                -- eapply Disjoint_Included_r. eassumption.
                   eapply Disjoint_Included_l. eapply image_apply_r_set_list. now eauto.
                   eapply Union_Disjoint_l. now sets. rewrite <- Same_set_all_fun_name.
                   eapply Disjoint_sym. eapply Disjoint_Included; [| | eapply Hdis3 ].
                   normalize_occurs_free. now xsets. now sets.
              * assert (Hdisys : Disjoint positive (FromList ys1)
                                          (occurs_free_fundefs f2 :|: name_in_fundefs f2
                                                               :|: occurs_free_fun_map fm)).
                { rewrite Union_commut. rewrite Union_assoc. eapply Union_Disjoint_r.
                  - eapply Disjoint_Included_l.
                    eapply Included_trans; [| eapply fun_in_fundefs_bound_var_fundefs; eapply find_def_correct; eapply Hfind ]. now sets.
                    eapply Disjoint_Included; [| | eapply Hdis1 ]. normalize_occurs_free. now sets. normalize_bound_var. now sets.
                  - eapply unique_bindings_fun_in_fundefs. eapply find_def_correct. eassumption. eassumption. }
                eapply fun_map_inv_antimon. eapply fun_map_inv_set_lists; [ | | | now eauto ].
                eapply fun_map_inv_set_lists_r; [| | now eauto ].
                -- rewrite <- Hseq. rewrite <- H13. eapply fun_map_inv_sig_extend_Disjoint.
                   eapply fun_map_inv_def_funs_add_fundefs. eapply fun_map_inv_i_mon. eassumption. lia.
                   ++ eapply preord_env_P_inj_antimon. rewrite apply_r_list_eq in H13.
                      rewrite H13. eapply IHi. lia. lia. eassumption. now eauto. normalize_occurs_free. sets.
                   ++ eassumption.
                   ++ normalize_occurs_free. sets.
                   ++ eapply Disjoint_Included; [| | eapply Hdis1 ]. now sets. normalize_bound_var.
                      eapply Included_trans. eapply name_in_fundefs_bound_var_fundefs. now sets.
                   ++ rewrite Same_set_all_fun_name, H13, Hseq. eapply Disjoint_Included ; [| | eapply Hdis3 ]. now sets. eassumption.
                   ++ eapply Disjoint_Included_r. eapply occurs_free_fun_map_add_fundefs. sets.
                -- rewrite image_f_eq_subdomain.
                   2:{ rewrite apply_r_set_list_f_eq. eapply f_eq_subdomain_extend_lst_Disjoint.
                       eapply Disjoint_Included_r. eapply occurs_free_fun_map_add_fundefs. sets. }
                   eapply Disjoint_Included_r.
                   eapply image_apply_r_set_list. now eauto. eapply Union_Disjoint_r.
                   eapply Disjoint_Included_l. eassumption. now sets.
                   rewrite <- Same_set_all_fun_name.
                   eapply Disjoint_Included_l. eassumption.
                   eapply Disjoint_Included; [| | eapply Hdis3 ]. normalize_occurs_free.
                   eapply Included_trans. eapply image_monotonic. eapply Included_Setminus_compat. eapply occurs_free_fun_map_add_fundefs. reflexivity.
                   rewrite !Setminus_Union_distr. rewrite Setminus_Same_set_Empty_set. normalize_sets.
                   now sets. now sets.
                -- eapply unique_bindings_fun_in_fundefs. eapply find_def_correct. eassumption. eassumption.
                -- eapply Union_Disjoint_r.
                   ++ eapply Disjoint_Included_r. eapply occurs_free_fun_map_add_fundefs. now sets.
                   ++ rewrite Dom_map_add_fundefs. eapply Union_Disjoint_r. now sets.
                      eapply Disjoint_Included; [| | eapply Hdis4 ]. now sets. repeat normalize_bound_var.
                      eapply Included_Union_preserv_l.
                      eapply Included_trans; [| eapply fun_in_fundefs_bound_var_fundefs; eapply find_def_correct; eauto ]. now sets.
                -- normalize_occurs_free. sets.
          - inv HIn. contradiction. rewrite def_funs_neq in Hgetx; [| eassumption ]. eapply Henv in Hgetx; [| eassumption ]. destructAll.
            eexists. rewrite apply_r_set_list_f_eq. rewrite extend_lst_gso. rewrite def_funs_neq.
            split; eauto. eapply preord_val_monotonic. eassumption. lia.
            + intros Hc. eapply Same_set_all_fun_name in Hc. rewrite H13 in Hc.
              rewrite apply_r_list_eq in Hc; [| | now eauto ]. eapply Hdis3. constructor.
              2:{ eapply In_image. eauto. }
              eapply fresh_Range. 2:{ eapply Hsub. eassumption. } eassumption. eassumption.
            + rewrite <- Same_set_all_fun_name. intros Hc. eapply Hdis1. constructor. normalize_bound_var. left.
              now eapply name_in_fundefs_bound_var_fundefs. now eauto. }
        eapply H9.
        -- eapply preord_env_P_inj_antimon. eassumption. normalize_occurs_free.
           rewrite !Union_assoc. rewrite Union_Setminus_Included; sets. tci.
        -- eapply fun_map_inv_antimon. rewrite <- Hseq. rewrite <- H13. eapply fun_map_inv_def_funs_add_fundefs.
           eapply fun_map_inv_i_mon. eassumption. lia. rewrite H13, Hseq. eapply preord_env_P_inj_antimon.
           eassumption. normalize_occurs_free. now sets. eassumption. normalize_occurs_free. sets.
           eapply Disjoint_Included_l. eapply name_in_fundefs_bound_var_fundefs.
           eapply Disjoint_Included; [| | eapply Hdis1 ]. now sets. normalize_bound_var. now sets.

           rewrite Same_set_all_fun_name, H13, Hseq. eapply Disjoint_Included; [| | eapply Hdis3 ]. now sets. eassumption.
           normalize_occurs_free. rewrite !Union_assoc. rewrite Union_Setminus_Included. now sets. tci. now sets.
    - (* Eapp *)
      simpl. destruct (update_App St IH v t (apply_r_list sig l) st) as [s b] eqn:Hup.
      + destruct b.
        * destruct (fm ! v) as [[[ft xs] e] |] eqn:Heqf.
          destruct d.
          -- eapply return_triple.
             intros. split; [| split; [| split; [| split; [| split; [| split ]]]]]; try eassumption.
             ++ reflexivity.
             ++ constructor.
             ++ repeat normalize_occurs_free. rewrite !image_Union, image_Singleton.
                rewrite FromList_apply_list. sets.
             ++ normalize_bound_var. sets.
             ++ eauto.
             ++ intros. eapply preord_exp_app_compat.
                now eauto. now eauto.
                eapply H0. now constructor.
                eapply Forall2_preord_var_env_map. eassumption.
                now constructor.
          -- destruct j.
             ++ eapply return_triple.
                intros. split; [| split; [| split; [| split; [| split; [| split ]]]]]; try eassumption.
                +++ reflexivity.
                +++ constructor.
                +++ repeat normalize_occurs_free. rewrite !image_Union, image_Singleton.
                    rewrite FromList_apply_list. sets.
                +++ normalize_bound_var. sets.
                +++ eauto.
                +++ intros. eapply preord_exp_app_compat.
                    now eauto. now eauto.
                    eapply H0. now constructor.
                    eapply Forall2_preord_var_env_map. eassumption.
                    now constructor.
             ++ destruct ((Datatypes.length xs =?  Datatypes.length l)%nat) eqn:Hbeq.
                { apply Nat.eqb_eq in Hbeq.
                  edestruct Hfm. eassumption. destructAll.

                  eapply bind_triple. eapply click_spec2 with (P := fun s => fresh S (next_var s)).
                  intros _u w.

                  edestruct Hfm. eassumption. destructAll.

               eapply pre_strenghtening with
                   (P := fun _ w' => fst w = fst w' /\ fresh S (next_var (fst w'))).
               now clear; firstorder.

               eapply post_weakening; [|  eapply frame_rule; eapply IHd; try lia ].

               ++ simpl. intros. destructAll.
                  split; [| split; [| split; [| split; [| split; [| split ]]]]]; try eassumption.
                  ** congruence.
                  ** eapply Included_trans. eassumption.
                     eapply Included_trans. eapply image_apply_r_set_list.
                     unfold apply_r_list. rewrite list_length_map. eassumption.
                     normalize_occurs_free. rewrite !image_Union. rewrite FromList_apply_list.
                     eapply Union_Included. now sets.
                     rewrite !Setminus_Union_distr. rewrite !image_Union.
                     eapply Included_Union_preserv_r. eapply Union_Included.
                     eapply image_monotonic. eapply occurs_free_fun_map_get. eassumption.
                     eapply image_monotonic. eapply Included_trans. eapply Setminus_Included.
                     eapply occurs_free_fun_map_remove.
                  ** rewrite H15. eassumption.
                  ** exact I.
                  ** intros. eapply preord_exp_app_l.
                     --- eauto.
                     --- eauto.
                     --- intros. assert (Hf' := H26). assert (Heqf' := Heqf).
                         edestruct H26; eauto. destructAll.
                         do 2 subst_exp. eapply H23.
                         +++ edestruct preord_env_P_inj_get_list_l. now eapply H25. normalize_occurs_free. now sets.
                             eassumption. destructAll.
                             eapply preord_env_P_inj_set_lists_l'; try eassumption.
                         +++ eapply fun_map_inv_antimon. eapply fun_map_inv_set_lists; [ | | | eassumption ].
                             *** eapply fun_map_inv_sig_extend_Disjoint. rewrite <- fun_map_inv_eq in *.
                                 eapply fun_map_inv_remove. eassumption.
                                 now sets.
                             *** eassumption.
                             *** eapply Union_Disjoint_r. now sets.
                                 rewrite Dom_map_remove. sets.
                             *** rewrite Union_Setminus_Included. sets. tci. sets.
               ++ eassumption.
               ++ eapply Union_Disjoint_r. eapply Disjoint_Included; [| | eapply H1 ]; now sets.
                  sets.
               ++ clear H6. eapply Disjoint_Included_r. eapply image_apply_r_set_list.
                  unfold apply_r_list. rewrite list_length_map. eassumption.
                  eapply Disjoint_Included_r; [ | eapply Hdis3 ]. normalize_occurs_free.
                  rewrite FromList_apply_list.
                  eapply Union_Included; [ now sets  | ].
                  rewrite Setminus_Union_distr. eapply image_monotonic.
                  eapply Included_Union_preserv_r.
                  eapply Union_Included; [| ].
                  eapply occurs_free_fun_map_get. eassumption.
                  eapply Included_trans. eapply Setminus_Included. eapply occurs_free_fun_map_remove.
               ++ rewrite Dom_map_remove. sets.
               ++ sets.
               ++ eapply fun_map_vars_inv_remove.
                 (* Make lemma if needed about fun_map_vars fm S (set_list (combine xs (apply_r_list sig l)) sig) *)
                  intros ? ? ? ? ?. edestruct Hfm; eauto. destructAll.
                  repeat (split; [ now eauto |]).
                  eapply Disjoint_Included_r. eapply image_apply_r_set_list.
                  unfold apply_r_list. rewrite list_length_map. eassumption.
                  eapply Union_Disjoint_r.
                  eapply Disjoint_Included_r; [| eapply Hdis3 ]. normalize_occurs_free.
                  rewrite image_Union. rewrite FromList_apply_list. now sets. now sets. }
             { eapply return_triple.
               intros. split; [| split; [| split; [| split; [| split; [| split ]]]]]; try eassumption.
               ++ reflexivity.
               ++ constructor.
               ++ simpl. repeat normalize_occurs_free. rewrite !image_Union, image_Singleton.
                  rewrite FromList_apply_list. sets.
               ++ normalize_bound_var. sets.
               ++ eauto.
               ++ intros. eapply preord_exp_app_compat.
                  now eauto. now eauto.
                  eapply H0. now constructor.
                  eapply Forall2_preord_var_env_map. eassumption.
                  now constructor. }
          -- eapply return_triple.
             intros. split; [| split; [| split; [| split; [| split; [| split ]]]]]; try eassumption.
             ++ reflexivity.
             ++ constructor.
             ++ simpl. repeat normalize_occurs_free. rewrite !image_Union, image_Singleton.
                rewrite FromList_apply_list. sets.
             ++ normalize_bound_var. sets.
             ++ eauto.
             ++ intros. eapply preord_exp_app_compat.
                now eauto. now eauto.
                eapply H0. now constructor.
                eapply Forall2_preord_var_env_map. eassumption.
                now constructor.
        *  eapply return_triple.
           intros. split; [| split; [| split; [| split; [| split; [| split ]]]]]; try eassumption.
           ++ reflexivity.
           ++ constructor.
           ++ simpl. repeat normalize_occurs_free. rewrite !image_Union, image_Singleton.
              rewrite FromList_apply_list. sets.
           ++ normalize_bound_var. sets.
           ++ eauto.
           ++ intros. eapply preord_exp_app_compat.
              now eauto. now eauto.
              eapply H0. now constructor.
              eapply Forall2_preord_var_env_map. eassumption.
              now constructor.
    - (* Eprim_val *)
      eapply bind_triple. eapply pre_transfer_r. now eapply get_fresh_name_spec.
      intros x w1. simpl. eapply pre_curry_l. intros HSin. eapply pre_curry_l. intros Hf'.
      eapply bind_triple. eapply frame_rule. eapply frame_rule. eapply IHe with (S := S \\ [set x]).
      + eassumption.
      + repeat normalize_bound_var_in_ctx. repeat normalize_occurs_free_in_ctx.
        eapply Disjoint_Included_r. eapply Included_Union_Setminus with (s2 := [set v]). tci.
        eapply Union_Disjoint_r. rewrite Setminus_Union_distr. eapply Disjoint_Included; [| | eapply Hdis1 ]; sets.
        eapply Disjoint_Singleton_r. eassumption.
      + eapply Disjoint_Included_r.
        eapply image_apply_r_set.
        repeat normalize_bound_var_in_ctx. repeat normalize_occurs_free_in_ctx.
        eapply Union_Disjoint_r. now sets.
        eapply Disjoint_Included; [| | eapply Hdis3 ].
        rewrite Setminus_Union_distr. rewrite !image_Union. now xsets. now sets.
      + eapply Disjoint_Included_l; [| eassumption ]. normalize_bound_var. sets.
      + eapply Disjoint_Included_r. eapply bound_var_occurs_free_Eprim_val_Included. eassumption.
      + eapply fun_map_vars_set. eassumption.
      + intros e' w2. eapply return_triple.
        intros _ st'. intros [Hf1 [Hf2 [Hf3 [Hf4 [Hun [Hsub [Hsub' [Hsh Hsem]]]]]]]].
        split; [| split; [| split; [| split; [| split; [| split ]]]]].
        * eapply fresh_monotonic;[| eassumption ]. sets.
        * zify; lia.
        * constructor; [| eassumption ].
          intros Hc. eapply Hsub' in Hc. eapply Disjoint_Range; [| constructor; [ eapply Hf1 | eapply Hc ]].
          reflexivity.
        * repeat normalize_occurs_free. rewrite !image_Union.
          eapply Included_trans. eapply Included_Setminus_compat.
          eapply Included_trans. eassumption. now eapply image_apply_r_set. reflexivity.
          rewrite !Setminus_Union_distr. rewrite Setminus_Same_set_Empty_set. normalize_sets.
          rewrite image_Union. sets.
        * normalize_bound_var. eapply Union_Included. eapply Included_trans. eassumption.
          eapply Range_Subset. zify; lia. reflexivity.
          eapply Included_trans. eapply Singleton_Included. eassumption. eapply Range_Subset. reflexivity.
          zify; lia.
        * eauto.
        * intros r1 r2 k Henv Hfm'. eapply preord_exp_prim_val_compat.
          now eauto.
    - (* Eprim *)
      eapply bind_triple. eapply pre_transfer_r. now eapply get_fresh_name_spec.
      intros x w1. simpl. eapply pre_curry_l. intros HSin. eapply pre_curry_l. intros Hf'.
      eapply bind_triple. eapply frame_rule. eapply frame_rule. eapply IHe with (S := S \\ [set x]).
      + eassumption.
      + repeat normalize_bound_var_in_ctx. repeat normalize_occurs_free_in_ctx.
        eapply Disjoint_Included_r. eapply Included_Union_Setminus with (s2 := [set v]). tci.
        eapply Union_Disjoint_r. rewrite Setminus_Union_distr. eapply Disjoint_Included; [| | eapply Hdis1 ]; sets.
        eapply Disjoint_Singleton_r. eassumption.
      + eapply Disjoint_Included_r.
        eapply image_apply_r_set.
        repeat normalize_bound_var_in_ctx. repeat normalize_occurs_free_in_ctx.
        eapply Union_Disjoint_r. now sets.
        eapply Disjoint_Included; [| | eapply Hdis3 ].
        rewrite Setminus_Union_distr. rewrite !image_Union. now xsets. now sets.
      + eapply Disjoint_Included_l; [| eassumption ]. normalize_bound_var. sets.
      + eapply Disjoint_Included_r. eapply bound_var_occurs_free_Eprim_Included. eassumption.
      + eapply fun_map_vars_set. eassumption.
      + intros e' w2. eapply return_triple.
        intros _ st'. intros [Hf1 [Hf2 [Hf3 [Hf4 [Hun [Hsub [Hsub' [Hsh Hsem]]]]]]]].
        split; [| split; [| split; [| split; [| split; [| split ]]]]].
        * eapply fresh_monotonic;[| eassumption ]. sets.
        * zify; lia.
        * constructor; [| eassumption ].
          intros Hc. eapply Hsub' in Hc. eapply Disjoint_Range; [| constructor; [ eapply Hf1 | eapply Hc ]].
          reflexivity.
        * repeat normalize_occurs_free. rewrite !image_Union.
          rewrite <- FromList_apply_list. rewrite <- !Union_assoc. eapply Included_Union_compat. reflexivity.
          eapply Included_trans. eapply Included_Setminus_compat.
          eapply Included_trans. eassumption. now eapply image_apply_r_set. reflexivity.
          rewrite !Setminus_Union_distr. rewrite Setminus_Same_set_Empty_set. normalize_sets.
          rewrite image_Union. sets.
        * normalize_bound_var. eapply Union_Included. eapply Included_trans. eassumption.
          eapply Range_Subset. zify; lia. reflexivity.
          eapply Included_trans. eapply Singleton_Included. eassumption. eapply Range_Subset. reflexivity.
          zify; lia.
        * eauto.
        * intros r1 r2 k Henv Hfm'. eapply preord_exp_prim_compat.
          now eauto.
          eapply Forall2_preord_var_env_map. eassumption. normalize_occurs_free. now sets.
    - (* Ehalt *)
      eapply return_triple.
      intros. split; [| split; [| split; [| split; [| split; [| split ]]]]]; eauto.
      + reflexivity.
      + constructor.
      + repeat normalize_occurs_free. rewrite image_Union, image_Singleton. sets.
      + normalize_bound_var. sets.
      + simpl; eauto.
      + intros. eapply preord_exp_halt_compat. now eauto. now eauto.
        eapply H0. now constructor.
    - (* Fcons *)
      simpl.
      eapply bind_triple. eapply pre_transfer_r. now eapply get_fresh_names_spec. intros xs w. simpl.
      eapply pre_curry_l. intros HSin. eapply pre_curry_l. intros Hf'. eapply pre_curry_l. intros Hnd. eapply pre_curry_l. intros Hlen.
      eapply bind_triple.
      { do 2 eapply frame_rule. eapply IHe with (S := S \\ FromList xs).
        - eassumption.
        - eapply Union_Disjoint_r.
          + eapply fun_in_fundefs_Disjoint_bound_Var_occurs_free with (B := (Fcons v t l e f5)).
            now left. constructor; eauto. eapply Disjoint_Included; [| | eapply Hdis1 ]. now sets. now sets.
          + eapply Disjoint_Included_r. eapply Included_Union_Setminus with (s2 := name_in_fundefs (Fcons v t l e f5)). now tci.
            eapply Union_Disjoint_r.
            eapply Disjoint_Included; [| | eapply Hdis1 ]. eapply Included_Union_preserv_r. eapply Included_Setminus_compat.
            eapply occurs_free_fun_map_remove. reflexivity. normalize_bound_var. now sets.
            eapply unique_bindings_fun_in_fundefs. now left. constructor; eauto.
        - eapply Disjoint_Included_r. eapply image_apply_r_set_list. now eauto.
          eapply Union_Disjoint_r. now sets.
          eapply Disjoint_Included_r. eapply Included_Union_Setminus with (s2 := image (apply_r sig) (name_in_fundefs (Fcons v t l e f5))).
          now tci. eapply Union_Disjoint_r. eapply Disjoint_Included_r. eapply image_Setminus. now tci. rewrite Setminus_Union_distr.
          eapply Disjoint_Included; [| | eapply Hdis3 ]. rewrite !Setminus_Union_distr. normalize_occurs_free.
          rewrite !Setminus_Union. eapply image_monotonic. eapply Union_Included. simpl.
          now sets.
          eapply Included_trans. eapply Setminus_Included. eapply Included_trans. eapply occurs_free_fun_map_remove. now sets. now sets.

          eapply Disjoint_Included; [| | eapply Hnames2 ]. rewrite FromList_apply_list. rewrite Same_set_all_fun_name.
          reflexivity. now sets.
        - repeat normalize_bound_var_in_ctx. rewrite Dom_map_remove.
          eapply Disjoint_Included; [| | eapply Hdis4 ]; sets.
          rewrite !Setminus_Union_distr. do 2 eapply Included_Union_preserv_r. eapply Included_Union_preserv_l.
          rewrite Setminus_Disjoint. reflexivity. simpl. eapply Union_Disjoint_r. now sets.
          eapply Disjoint_Included_r; [| eapply H8 ]. eapply name_in_fundefs_bound_var_fundefs.
        - eapply Hdis5. now left.
        - repeat normalize_occurs_free_in_ctx. repeat normalize_bound_var_in_ctx.
          eapply fun_map_vars_set_list. eapply fun_map_vars_inv_remove. eassumption. }

      intros e' w'. simpl. eapply pre_curry_l. intros Hxs. eapply pre_curry_l; intros Hleq1.
      eapply bind_triple.

      { eapply pre_strenghtening.
        2:{ eapply frame_rule. eapply IHB with (S := S \\ FromList xs (* \\ bound_var e' *)).
            + eassumption.
            + repeat normalize_bound_var_in_ctx. repeat normalize_occurs_free_in_ctx.
              eapply Disjoint_Included_r. eapply Included_Union_Setminus with (s2 := [set v]). now tci.
              rewrite Setminus_Union_distr. eapply Union_Disjoint_r. eapply Disjoint_Included; [| | eapply Hdis1 ].
              simpl. rewrite Setminus_Union. now sets. now sets. now sets.
            + repeat normalize_bound_var_in_ctx. repeat normalize_occurs_free_in_ctx.
              eapply Disjoint_Included_r. eapply Included_Union_Setminus with (s2 := image (apply_r sig) [set v]). now tci.
              eapply Union_Disjoint_r.
              eapply Disjoint_Included_r. eapply image_Setminus. now tci.
              eapply Disjoint_Included; [| | eapply Hdis3 ].
              eapply image_monotonic. rewrite !Setminus_Union_distr. now sets. now sets.
              eapply Disjoint_Included; [| | eapply Hnames2 ]. rewrite FromList_apply_list, <- Same_set_all_fun_name. simpl. now sets. now sets.
            + repeat normalize_bound_var_in_ctx. repeat normalize_occurs_free_in_ctx. xsets.
            + intro; intros. eapply Hdis5. right. eassumption.
            + eapply fun_map_vars_antimon; eauto. sets.
            + simpl in Hnames1. inv Hnames1. eassumption.
            + eapply Disjoint_Included; [ | | eapply Hnames2 ]; simpl; sets. normalize_sets. sets. }

        simpl. intros u w1 [Hyp Hyp']. split. eapply Hyp'. eassumption. }


      intros B' w''. eapply return_triple. intros. destructAll. split; [| split ; [| split; [| split; [| split; [| split ]]]]].
      + eapply fresh_monotonic; [|  eassumption ]. sets.
      + zify; lia.
      + constructor; eauto.
        * intros Hc. eapply Hnames2. constructor. 2:{ left. reflexivity. }
          eapply H18 in Hc. unfold Ensembles.In, Range in Hc. eapply HSin. zify; lia.
        * intros Hc. eapply Included_Union_Setminus with (s2 := name_in_fundefs B') in Hc; [| tci ].
          inv Hc.
          -- eapply Hnames2. constructor. 2:{ left. reflexivity. }
             eapply HSin. eapply H13 in H21. unfold Ensembles.In, Range in H21. zify; lia.
          -- rewrite Same_set_all_fun_name in H21. rewrite H14 in H21. rewrite FromList_apply_list in H21.
             inv Hnames1. eapply H24; eauto. eapply FromList_apply_list. eassumption.

        * eapply Disjoint_Included. eassumption. eassumption. eapply Disjoint_sym. eapply Disjoint_Range. reflexivity.
        * eapply Disjoint_Included_l. eapply Included_Union_Setminus with (s2 := name_in_fundefs B'); tci. eapply Union_Disjoint_l.
          -- eapply Disjoint_Included. eassumption. eassumption. eapply Disjoint_sym. eapply Disjoint_Range. zify. lia.
          -- apply Disjoint_sym. eapply Disjoint_Included; [| | eapply Hnames2 ].
             simpl. normalize_sets. rewrite Same_set_all_fun_name. rewrite H14. now sets.
             eapply Included_trans. eassumption. intros z Hc. eapply HSin. unfold Ensembles.In, Range in Hc. zify; lia.
        * eapply Disjoint_Included_r. eapply Included_Union_Setminus with (s2 := name_in_fundefs B'); tci. eapply Union_Disjoint_r.
          -- eapply Disjoint_Included. eassumption. eassumption. eapply Disjoint_Range. zify. lia.
          -- rewrite Same_set_all_fun_name.  rewrite H14. eapply Disjoint_Included; [ | | eapply Hnames2 ].
             simpl. normalize_sets. now sets.
             intros z Hin. eapply H18 in Hin. eapply HSin. unfold Ensembles.In, Range in Hin. zify; lia.
        * intros Hc. eapply Hnames2. constructor. 2:{ left. reflexivity. }
          eapply HSin. eapply Hxs in Hc. unfold Ensembles.In, Range in Hc. zify; lia.
      + normalize_occurs_free. eapply Included_trans. eapply Included_Union_compat.
        * eapply Included_Setminus_compat. eassumption. reflexivity.
        * eapply Included_Setminus_compat. eassumption. reflexivity.
        * eapply Union_Included.
          -- eapply Included_trans. eapply Included_Setminus_compat. eapply image_apply_r_set_list. now eauto. reflexivity.
             rewrite !Setminus_Union_distr. eapply Union_Included. now sets.
             rewrite Same_set_all_fun_name. rewrite H14. rewrite FromList_apply_list. rewrite <- Same_set_all_fun_name.
             rewrite (Union_commut (FromList xs)). rewrite Union_assoc. rewrite <- Setminus_Union.
             eapply Included_trans. eapply Setminus_Included. eapply Included_trans.
             rewrite <- image_Singleton, <- image_Union. eapply image_Setminus. now tci.
             rewrite !Setminus_Union_distr, !Setminus_Union. normalize_occurs_free.
             rewrite !image_Union. eapply Union_Included; sets. now xsets.
             eapply Included_trans. eapply image_monotonic. eapply Included_trans. eapply Setminus_Included.
             eapply occurs_free_fun_map_remove. now sets.
          -- rewrite <- image_Singleton. eapply Included_trans. eapply image_Setminus. now tci.
             rewrite Setminus_Union_distr. normalize_occurs_free. sets.
      + normalize_bound_var. simpl. rewrite Setminus_Union_distr. eapply Union_Included. now sets.
        rewrite !Setminus_Union_distr. eapply Union_Included; [| eapply Union_Included ].
        * eapply Included_trans. eapply Setminus_Included.
          eapply Included_trans. eassumption. eapply Range_Subset; zify; lia.
        * eapply Included_trans. eapply Setminus_Included.
          eapply Included_trans. eassumption. eapply Range_Subset; zify; lia.
        * rewrite Union_commut. rewrite <- Setminus_Union.
          eapply Included_trans. eapply Setminus_Included.
          eapply Included_trans. eassumption. eapply Range_Subset; zify; lia.
      + simpl. rewrite H14. reflexivity.
      + intros. destruct (term.M.elt_eq f v); subst.
        * inv H21. do 2 eexists. split; [| split; [| split; [| split ]]].
          -- simpl. rewrite peq_true. reflexivity.
          -- now eauto.
          -- eassumption.
          -- intros z HIn. eapply HSin. eapply Hxs in HIn. unfold Ensembles.In, Range in HIn. zify; lia.
          -- intros. eapply H20.
             ++ rewrite apply_r_set_list_f_eq.
                eapply preord_env_P_inj_antimon. eassumption. eapply Included_trans.
                eapply occurs_free_in_fun with (B := (Fcons v ft xs0 e1 f5)). now left.
                sets.
             ++ eapply fun_map_inv_remove. eapply fun_map_inv_antimon. eassumption.
                eapply Included_trans. eapply occurs_free_in_fun with (B := (Fcons v ft xs0 e1 f5)). now left.
                sets.
        * edestruct H15. eassumption. destructAll.
          do 2 eexists. split; [| split; [| split; [| split ] ]].
          -- simpl. rewrite peq_false. eassumption. intros Hc. inv Hnames1. eapply H29. rewrite <- Hc.
             rewrite <- H14. eapply Same_set_all_fun_name. eapply find_def_name_in_fundefs. eassumption.
          -- now eauto.
          -- eassumption.
          -- eapply Included_trans. eassumption. sets.
          -- intros. eapply H26; eauto.
             ++ eapply preord_env_P_inj_antimon. eassumption. normalize_occurs_free.
                rewrite <- !Union_assoc.
                rewrite <- Union_Included_Union_Setminus with (s1 := occurs_free_fundefs _) (s3 := [set v]).
                now sets. tci. now sets.
             ++ eapply fun_map_inv_antimon. eassumption. normalize_occurs_free.
                rewrite <- !Union_assoc.
                rewrite <- Union_Included_Union_Setminus with (s1 := occurs_free_fundefs _) (s3 := [set v]).
                now sets. tci. now sets.
    - (* Fnil *)
      eapply return_triple.
      intros. split; [| split; [| split; [| split; [| split; [| split ]]]]]; eauto.
      + reflexivity.
      + constructor.
      + intros z Hin; inv Hin.
      + normalize_bound_var. sets.
      + intros. inv H0.
  Qed.


  Lemma apply_r_empty_f_eq :
    f_eq (apply_r (M.empty var)) id.
  Proof.
    intros x. rewrite apply_r_empty. reflexivity.
  Qed.

  Lemma occurs_free_fun_map_empty :
    occurs_free_fun_map (M.empty _) <--> Empty_set _.
  Proof.
    split; sets.
    intros x Hin. inv Hin. destructAll. rewrite M.gempty in H. inv H.
  Qed.

  Lemma bound_var_fun_map_empty :
    bound_var_fun_map (M.empty _) <--> Empty_set _.
  Proof.
    split; sets.
    intros x Hin. inv Hin. destructAll. rewrite M.gempty in H. inv H.
  Qed.


  Lemma inline_correct_top d (Hleq : (d <= G)%nat) P (e : exp) (st : St) (c:comp_data) (Hi : inclusion (P1 d) P) z :
    unique_bindings e ->
    Disjoint _ (bound_var e) (occurs_free e) ->
    exists e' c' click,
      inline_top' St IH z d st e c  = (Ret e', c', click) /\
      unique_bindings e' /\
      occurs_free e' \subset occurs_free e /\
      Disjoint _ (bound_var e') (occurs_free e') /\
      (max_var e' 1%positive) < (next_var c') /\
      (forall k rho1 rho2,
          preord_env_P cenv PG (occurs_free e) k rho1 rho2 ->
          preord_exp cenv P PG k (e, rho1) (e', rho2)).
  Proof.
    intros Hun Hdis. edestruct (inline_correct_mut d) as [He _]. eassumption.
    unfold inline_top', triple in *.

    destruct (restart_names z e c) as [c_data nenv] eqn:Hnames.
    unfold restart_names in Hnames. destruct c.

    pose (nv := match set_util.PS.max_elt (exp_fv e)
                      with
                      | Some v => Pos.max v z + 1
                      | None => z + 1
                      end).

    simpl in Hnames.

    specialize (He e (M.empty _) (M.empty _) st (fun x => nv <= x) Hun).
    rewrite occurs_free_fun_map_empty, bound_var_fun_map_empty in *.
    repeat normalize_sets.
    specialize (He Hdis).

    assert (Hdis_fv : Disjoint var (fun x : var => nv <= x) (occurs_free e)).
    { constructor. intros x Hnin. inv Hnin.
      eapply exp_fv_correct in H0.
      destruct (set_util.PS.max_elt (exp_fv e)) eqn:Hmax.
      - inv Hnames. simpl in *. unfold nv in *. simpl in *.
        eapply set_util.PS.max_elt_spec2 with (y := x) in Hmax. eapply Pos.compare_ge_iff in Hmax.
        unfold Ensembles.In in *. zify. lia.
        eapply set_util.FromSet_sound. reflexivity. eassumption.
      - eapply set_util.FromSet_sound in H0; [| reflexivity ].
        eapply set_util.PS.max_elt_spec3 in H0. eassumption. eassumption. }

    assert (Hdis1 : Disjoint var (fun x : var => nv <= x) (image (apply_r (M.empty var)) (occurs_free e))).
    { rewrite apply_r_empty_f_eq. rewrite image_id. eassumption. }

    assert (Hdis2 : Disjoint var (bound_var e) (Dom_map (M.empty (fun_tag * list var * exp)))).
    { rewrite Dom_map_empty. sets. }

    assert (Hdis3 :  Disjoint var (Empty_set var) (bound_var e :|: occurs_free e) ).
    { sets. }

    assert (Hfinv : fun_map_vars (M.empty (fun_tag * list var * exp))
                                 (fun x : var => nv <= x)
                                 (M.empty var)).
    { unfold fun_map_vars. intros. rewrite M.gempty in H. inv H. }


    assert (Hf' : fresh (fun x : var => nv <= x) (state.next_var (fst (c_data, (nenv, false))))).
    { unfold fresh. intros. unfold Ensembles.In in *. simpl in *.
      unfold restart_names in Hnames. destruct c. inv Hnames. simpl in *. unfold nv. eassumption. }


    specialize (He Hdis1 Hdis2 Hdis3 Hfinv tt (c_data, (false, nenv)) Hf').

    unfold run_compM, compM.runState in *. simpl in *.

    destruct (inline_exp St IH d d e (M.empty var) (M.empty (fun_tag * list var * exp)) st) eqn:Heq.
    destruct (runState tt (c_data, (false, nenv))) eqn:Hstate.
    destruct e0. contradiction. destructAll.

    destruct p. destruct i. do 3 eexists.
    split; [| split; [| split; [| split; [| split ]]]].
    - reflexivity.
    - eassumption.
    - eapply Included_trans. eassumption. rewrite apply_r_empty_f_eq. rewrite image_id, occurs_free_fun_map_empty.
      sets.
    - eapply Disjoint_Included. eassumption. eassumption.
      rewrite apply_r_empty_f_eq. rewrite image_id, occurs_free_fun_map_empty. normalize_sets.
      eapply Disjoint_Included_l. eapply fresh_Range. eassumption. eassumption.
    - assert (Hin := max_var_subset e0). assert (Hin' := max_var_subset e).
      inv Hin.
      + eapply H3 in H6. unfold Ensembles.In, Range in H6. simpl. inv H6. eassumption.
      + rewrite occurs_free_fun_map_empty, image_apply_r_empty in H2. repeat normalize_sets.
        eapply H2 in H6.
        simpl in *. inv Hnames. simpl in *.
        eapply exp_fv_correct in H6.
        destruct (set_util.PS.max_elt (exp_fv e)) eqn:Hmax.
        * simpl in *. unfold nv in *. simpl in *.
          eapply set_util.PS.max_elt_spec2 with (y := (max_var e0 1)) in Hmax. eapply Pos.compare_ge_iff in Hmax.
          unfold Ensembles.In in *. zify. lia.
          eapply set_util.FromSet_sound. reflexivity. eassumption.
        * eapply set_util.PS.max_elt_spec3 in Hmax.
          eapply set_util.FromSet_sound in H6; [| reflexivity ]. exfalso. eapply Hmax. eassumption.
    - intros.
      eapply preord_exp_post_monotonic. eassumption.
      eapply H5; eauto.
      intros x Hin. unfold id. now eauto.
  Qed.

End Inline_correct.
