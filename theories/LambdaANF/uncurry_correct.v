Require Import
  LambdaANF.size_cps LambdaANF.eval LambdaANF.term LambdaANF.term_util
  LambdaANF.logical_relations LambdaANF.identifiers
  LambdaANF.ctx LambdaANF.Ensembles_util LambdaANF.List_util
  LambdaANF.uncurry LambdaANF.algebra LambdaANF.state.
From Stdlib Require Import Lia.
From Stdlib Require Import ZArith.Znumtheory Relations.Relations Arith.Wf_nat.
From Stdlib Require Import
  Lists.List MSets.MSets MSets.MSetRBT Numbers.BinNums
  NArith.BinNat PArith.BinPos Sets.Ensembles micromega.Lia.
Require Import ExtLib.Structures.Monads ExtLib.Data.Monads.StateMonad.
Require Import Common.compM.

Import ListNotations MonadNotation.

Section list_lemmas.

  Lemma set_lists_length : forall {A} (l : list M.elt) (l1 : list A) (rho rho1 : M.t A),
    Some rho1 = set_lists l l1 rho -> length l = length l1.
  Proof.
    induction l; intros.
    - (* [] *) destruct l1; [ easy | now simpl in H ].
    - (* :: *) destruct l1; [ now simpl in H | ].
      simpl. apply f_equal.
      remember (set_lists l l1 rho).
      destruct o.
      + eapply IHl. simpl in H. eapply Heqo.
      + simpl in H. now rewrite <- Heqo in H.
  Qed.

  Lemma exists_set_lists_iff_length :
    forall {A} (l : list M.elt) (l1 : list A) (rho : M.t A),
      (exists rho1, Some rho1 = set_lists l l1 rho) <-> length l = length l1.
  Proof.
    induction l; split; intros.
    - (* [] -> *) destruct H. destruct l1; [easy|now simpl in H].
    - (* [] <- *) destruct l1; [now exists rho|easy].
    - (* :: -> *) destruct H. destruct l1; [now simpl in H|].
      simpl. apply f_equal.
      simpl in H. remember (set_lists l l1 rho).
      destruct o; [|congruence].
      rewrite <- IHl with (rho := rho). now exists t.
    - (* :: <- *) destruct l1; [easy|]. simpl in H.
      apply Nat_as_OT.succ_inj in H.
      rewrite <- IHl with (rho := rho) in H. destruct H.
      simpl. rewrite <- H. now exists (M.set a a0 x).
  Qed.

  Corollary exists_set_lists_length :
    forall {A} (l : list M.elt) (l1 : list A) (rho : M.t A),
      (exists rho1, Some rho1 = set_lists l l1 rho) -> length l = length l1.
  Proof.
    intros. now rewrite <- exists_set_lists_iff_length.
  Qed.

  Corollary length_exists_set_lists : forall {A} (l : list M.elt) (l1 : list A) (rho : M.t A),
     length l = length l1 -> (exists rho1, Some rho1 = set_lists l l1 rho).
  Proof. intros; now rewrite exists_set_lists_iff_length. Qed.

  (* expose an M.set from a successful set_lists *)
  Lemma set_set_lists : forall {A} h h1 (t : list M.elt) (t1 : list A) (rho rho2 : M.t A),
      Some rho2 = set_lists (h :: t) (h1 :: t1) rho -> exists rho1,
        rho2 = M.set h h1 rho1 /\ Some rho1 = set_lists t t1 rho.
  Proof.
    simpl. intros. remember (set_lists t t1 rho). destruct o; [|congruence].
    inversion H. inversion H. subst. eauto.
  Qed.

End list_lemmas.

Section Uncurry_correct.

  (* all variables in a list are distinct and disjoint from some set of used vars *)
  Definition fresh_copies (s : Ensemble var) (l : list var) : Prop
    := Disjoint _ s (FromList l) /\ NoDup l.

  Inductive uncurry_step :
    exp ->          (* original expression *)
    Ensemble var -> (* used variables *)
    localMap ->     (* already uncurried functions *)
    exp ->          (* expression w/ 1 function uncurried *)
    Ensemble var -> (* new used variables *)
    localMap ->     (* new uncurried functions *)
    Prop :=
  | uncurry_letapp : forall x f ft ys e e1 s s1 m m1,
      uncurry_step e s m e1 s1 m1 ->
      uncurry_step (Eletapp x f ft ys e) s m (Eletapp x f ft ys e1) s1 m1
  | uncurry_constr : forall x c args e e1 s s1 m m1,
      uncurry_step e s m e1 s1 m1 ->
      uncurry_step (Econstr x c args e) s m (Econstr x c args e1) s1 m1
  | uncurry_case_expr : forall x arms c e e1 s s1 m m1,
      uncurry_step e s m e1 s1 m1 ->
      uncurry_step (Ecase x ((c, e) :: arms)) s m (Ecase x ((c, e1) :: arms)) s1 m1
  | uncurry_case_arms : forall x arms arms1 arm s s1 m m1,
      uncurry_step (Ecase x arms) s m (Ecase x arms1) s1 m1 ->
      uncurry_step (Ecase x (arm :: arms)) s m (Ecase x (arm :: arms1)) s1 m1
  | uncurry_proj : forall x c n y e e1 s s1 m m1,
      uncurry_step e s m e1 s1 m1 ->
      uncurry_step (Eproj x c n y e) s m (Eproj x c n y e1) s1 m1
  | uncurry_prim : forall x p args e e1 s s1 m m1,
      uncurry_step e s m e1 s1 m1 ->
      uncurry_step (Eprim x p args e) s m (Eprim x p args e1) s1 m1
  | uncurry_prim_val : forall v p e e1 s s1 m m1,
      uncurry_step e s m e1 s1 m1 ->
      uncurry_step (Eprim_val v p e) s m (Eprim_val v p e1) s1 m1
  | uncurry_fun_expr : forall fds e e1 s s1 m m1,
      uncurry_step e s m e1 s1 m1 ->
      uncurry_step (Efun fds e) s m (Efun fds e1) s1 m1
  | uncurry_fun_fds : forall fds fds1 e s s1 m m1,
      uncurry_fundefs_step fds s m fds1 s1 m1 ->
      uncurry_step (Efun fds e) s m (Efun fds1 e) s1 m1
  with uncurry_fundefs_step :
    fundefs ->
    Ensemble var ->
    localMap ->
    fundefs ->
    Ensemble var ->
    localMap ->
    Prop :=
  | uncurry_fundefs_fds : forall f t args e fds fds1 s s1 m m1,
      uncurry_fundefs_step fds s m fds1 s1 m1 ->
      uncurry_fundefs_step (Fcons f t args e fds) s m (Fcons f t args e fds1) s1 m1
  | uncurry_fundefs_e : forall f t args e e1 fds s s1 m m1,
      uncurry_step e s m e1 s1 m1 ->
      uncurry_fundefs_step (Fcons f t args e fds) s m (Fcons f t args e1 fds) s1 m1
  | uncurry_fundefs_curried :
      forall f f1 ft ft1 k kt fv fv1
             g gt gv gv1 ge fds s m s',
      match M.get g m with Some true => true | _ => false end = false ->
      occurs_in_exp g ge = false ->
      occurs_in_exp k ge = false ->
      fresh_copies s gv1 ->
      length gv1 = length gv ->
      fresh_copies (s :|: FromList gv1) fv1 ->
      length fv1 = length fv ->
      ~(In _ (s :|: FromList gv1 :|: FromList fv1) f1) ->
      s' <--> s :|: FromList gv1 :|: FromList fv1 :|: [set f1] ->
      uncurry_fundefs_step
        (Fcons f ft (k :: fv) (Efun (Fcons g gt gv ge Fnil) (Eapp k kt [g])) fds) s m
        (Fcons f ft (k :: fv1)
           (Efun (Fcons g gt gv1 (Eapp f1 ft1 (gv1 ++ fv1)) Fnil) (Eapp k kt [g]))
           (Fcons f1 ft1 (gv ++ fv) ge fds))
        s'
        (M.set g true m)
  | uncurry_fundefs_curried_anf :
      forall f f1 ft ft1 fv fv1
             g gt gv gv1 ge fds s m s',
        match M.get g m with
        | Some true => true
        | _ => false end = false
        ->
      occurs_in_exp g ge = false ->
      fresh_copies s gv1 ->
      length gv1 = length gv ->
      fresh_copies (s :|: FromList gv1) fv1 ->
      length fv1 = length fv ->
      ~(In _ (s :|: FromList gv1 :|: FromList fv1) f1) ->
      s' <--> s :|: FromList gv1 :|: FromList fv1 :|: [set f1] ->
      uncurry_fundefs_step
        (Fcons f ft fv (Efun (Fcons g gt gv ge Fnil) (Ehalt g)) fds) s m
        (Fcons f ft fv1
           (Efun (Fcons g gt gv1 (Eapp f1 ft1 (gv1 ++ fv1)) Fnil) (Ehalt g))
           (Fcons f1 ft1 (gv ++ fv) ge fds))
        s'
        (M.set g true m).

  Hint Constructors uncurry_step : core.
  Hint Constructors uncurry_fundefs_step : core.

  Scheme uncurry_step_mut := Minimality for uncurry_step Sort Prop
  with uncurry_step_fundefs_mut := Minimality for uncurry_fundefs_step Sort Prop.

  Ltac uncurry_step_induction P Q IHuncurry IH :=
    apply uncurry_step_mut with (P := P) (P0 := Q);
    [ intros ? ? ? ? ? ? ? ? ? ? IHuncurry IH
    | intros ? ? ? ? ? ? ? ? ? IHuncurry IH
    | intros ? ? ? ? ? ? ? ? ? IHuncurry IH
    | intros ? ? ? ? ? ? ? ? IHuncurry IH
    | intros ? ? ? ? ? ? ? ? ? ? IHuncurry IH
    | intros ? ? ? ? ? ? ? ? ? IHuncurry IH
    | intros ? ? ? ? ? ? ? ? IHuncurry IH
    | intros ? ? ? ? ? ? ? IHuncurry IH
    | intros ? ? ? ? ? ? ? IHuncurry IH
    | intros ? ? ? ? ? ? ? ? ? ? IHuncurry IH
    | intros ? ? ? ? ? ? ? ? ? ? IHuncurry IH
    | intros
    | intros
    ].

  Lemma uncurry_step_mutual_ind :
    forall (P : exp -> Ensemble var -> localMap -> exp -> Ensemble var -> localMap -> Prop)
           (P0 : fundefs -> Ensemble var -> localMap -> fundefs -> Ensemble var -> localMap -> Prop),
      (forall (x f : var) (ft : fun_tag) (ys : list var) (e e1 : exp) (s s1 : Ensemble var) (m m1 : localMap),
          uncurry_step e s m e1 s1 m1 -> P e s m e1 s1 m1 -> P (Eletapp x f ft ys e) s m (Eletapp x f ft ys e1) s1 m1) ->
      (forall (x : var) (c : ctor_tag) (args : list var) (e e1 : exp) (s s1 : Ensemble var) (m m1 : localMap),
          uncurry_step e s m e1 s1 m1 ->
          P e s m e1 s1 m1 -> P (Econstr x c args e) s m (Econstr x c args e1) s1 m1) ->
      (forall (x : var) (arms : list (ctor_tag * exp)) (c : ctor_tag) (e e1 : exp) (s s1 : Ensemble var)
              (m m1 : localMap),
          uncurry_step e s m e1 s1 m1 ->
          P e s m e1 s1 m1 -> P (Ecase x ((c, e) :: arms)) s m (Ecase x ((c, e1) :: arms)) s1 m1) ->
      (forall (x : var) (arms arms1 : list (ctor_tag * exp)) (arm : ctor_tag * exp) (s s1 : Ensemble var)
              (m m1 : localMap),
          uncurry_step (Ecase x arms) s m (Ecase x arms1) s1 m1 ->
          P (Ecase x arms) s m (Ecase x arms1) s1 m1 ->
          P (Ecase x (arm :: arms)) s m (Ecase x (arm :: arms1)) s1 m1) ->
      (forall (x : var) (c : ctor_tag) (n : N) (y : var) (e e1 : exp) (s s1 : Ensemble var) (m m1 : localMap),
          uncurry_step e s m e1 s1 m1 -> P e s m e1 s1 m1 -> P (Eproj x c n y e) s m (Eproj x c n y e1) s1 m1) ->
      (forall (x : var) (p : prim) (args : list var) (e e1 : exp) (s s1 : Ensemble var) (m m1 : localMap),
          uncurry_step e s m e1 s1 m1 ->
          P e s m e1 s1 m1 -> P (Eprim x p args e) s m (Eprim x p args e1) s1 m1) ->
      (forall (v : var) p (e e1 : exp) (s s1 : Ensemble var) (m m1 : localMap),
          uncurry_step e s m e1 s1 m1 ->
          P e s m e1 s1 m1 -> P (Eprim_val v p e) s m (Eprim_val v p e1) s1 m1) ->
      (forall (fds : fundefs) (e e1 : exp) (s s1 : Ensemble var) (m m1 : localMap),
          uncurry_step e s m e1 s1 m1 -> P e s m e1 s1 m1 -> P (Efun fds e) s m (Efun fds e1) s1 m1) ->
      (forall (fds fds1 : fundefs) (e : exp) (s s1 : Ensemble var) (m m1 : localMap),
          uncurry_fundefs_step fds s m fds1 s1 m1 ->
          P0 fds s m fds1 s1 m1 -> P (Efun fds e) s m (Efun fds1 e) s1 m1) ->
      (forall (f6 : var) (t : fun_tag) (args : list var) (e : exp) (fds fds1 : fundefs)
              (s s1 : Ensemble var) (m m1 : localMap),
          uncurry_fundefs_step fds s m fds1 s1 m1 ->
          P0 fds s m fds1 s1 m1 -> P0 (Fcons f6 t args e fds) s m (Fcons f6 t args e fds1) s1 m1) ->
      (forall (f7 : var) (t : fun_tag) (args : list var) (e e1 : exp) (fds : fundefs)
              (s s1 : Ensemble var) (m m1 : localMap),
          uncurry_step e s m e1 s1 m1 ->
          P e s m e1 s1 m1 -> P0 (Fcons f7 t args e fds) s m (Fcons f7 t args e1 fds) s1 m1) ->
      (forall (f9 f10 : var) (ft ft1 : fun_tag) (k : var) (kt : fun_tag) (fv fv1 : list var)
              (g : positive) (gt : fun_tag) (gv gv1 : list var) (ge : exp) (fds : fundefs)
              (s : Ensemble var) (m : M.t bool) (s' : Ensemble var),
          match M.get g m with
          | Some true => true
          | Some false => false
          | None => false
          end = false ->
          occurs_in_exp g ge = false ->
          occurs_in_exp k ge = false ->
          fresh_copies s gv1 ->
          length gv1 = length gv ->
          fresh_copies (s :|: FromList gv1) fv1 ->
          length fv1 = length fv ->
          ~ In var (s :|: FromList gv1 :|: FromList fv1) f10 ->
          s' <--> s :|: FromList gv1 :|: FromList fv1 :|: [set f10] ->
          P0 (Fcons f9 ft (k :: fv) (Efun (Fcons g gt gv ge Fnil) (Eapp k kt [g])) fds) s m
            (Fcons f9 ft (k :: fv1) (Efun (Fcons g gt gv1 (Eapp f10 ft1 (gv1 ++ fv1)) Fnil) (Eapp k kt [g]))
               (Fcons f10 ft1 (gv ++ fv) ge fds)) s'
            (M.set g true m)) ->
      (forall (f10 f11 : var) (ft ft1 : fun_tag) (fv fv1 : list var) (g : positive) (gt : fun_tag)
              (gv gv1 : list var) (ge : exp) (fds : fundefs) (s : Ensemble var) (m : M.t bool)
              (s' : Ensemble var),
          match m ! g with
          | Some true => true
          | _ => false
          end = false ->
          occurs_in_exp g ge = false ->
          fresh_copies s gv1 ->
          Datatypes.length gv1 = Datatypes.length gv ->
          fresh_copies (s :|: FromList gv1) fv1 ->
          Datatypes.length fv1 = Datatypes.length fv ->
          ~ In var (s :|: FromList gv1 :|: FromList fv1) f11 ->
          s' <--> s :|: FromList gv1 :|: FromList fv1 :|: [set f11] ->
          P0 (Fcons f10 ft fv (Efun (Fcons g gt gv ge Fnil) (Ehalt g)) fds) s m
            (Fcons f10 ft fv1 (Efun (Fcons g gt gv1 (Eapp f11 ft1 (gv1 ++ fv1)) Fnil) (Ehalt g))
               (Fcons f11 ft1 (gv ++ fv) ge fds)) s' (M.set g true m)) ->
      (forall (e : exp) (e0 : Ensemble var) (l : localMap) (e1 : exp) (e2 : Ensemble var)
              (l0 : localMap), uncurry_step e e0 l e1 e2 l0 -> P e e0 l e1 e2 l0) /\
        (forall (f10 : fundefs) (e : Ensemble var) (l : localMap) (f11 : fundefs)
                (e0 : Ensemble var) (l0 : localMap),
            uncurry_fundefs_step f10 e l f11 e0 l0 ->
            P0 f10 e l f11 e0 l0).
  Proof.
    intros. split.
    apply (uncurry_step_mut P P0); assumption.
    apply (uncurry_step_fundefs_mut P P0); assumption.
  Qed.

  (* to do proofs simultaneously *)
  Ltac uncurry_induction_mut P Q IHuncurry IH :=
    apply uncurry_step_mutual_ind with (P := P) (P0 := Q);
    [ intros ? ? ? ? ? ? ? ? ? ? IHuncurry IH
    | intros ? ? ? ? ? ? ? ? ? IHuncurry IH
    | intros ? ? ? ? ? ? ? ? ? IHuncurry IH
    | intros ? ? ? ? ? ? ? ? IHuncurry IH
    | intros ? ? ? ? ? ? ? ? ? ? IHuncurry IH
    | intros ? ? ? ? ? ? ? ? ? IHuncurry IH
    | intros ? ? ? ? ? ? ? ? IHuncurry IH (* prim_val *)
    | intros ? ? ? ? ? ? ? IHuncurry IH
    | intros ? ? ? ? ? ? ? IHuncurry IH
    | intros ? ? ? ? ? ? ? ? ? ? IHuncurry IH
    | intros ? ? ? ? ? ? ? ? ? ? IHuncurry IH
    | intros
    | intros
    ].

  Context {fuel : Type} {Hfuel : @fuel_resource fuel} {trace : Type} {Htrace : @trace_resource trace}.
  Variable (pr : prims).
  Variable (cenv : ctor_env).
  Variable (Post : @PostT fuel trace).
  Variable (PostG : @PostGT fuel trace).

  Ltac easy_post :=
    assumption ||
    match goal with
    | |- inclusion _ ?R ?R => now unfold inclusion
    end.

  Context (Hpost_prop : Post_properties cenv Post Post PostG)
          (Hpost_propG : Post_properties cenv PostG PostG PostG).

  Context (Hpost_curry :
             forall e rho rho' rho'' c1 c2 cout1 cout2 f1 ft1 fv1 gv1,
               Post (e, rho, c1, cout1) (e, rho'', c2, cout2) ->
               PostG (e, rho, c1, cout1)
                     (Eapp f1 ft1 (gv1 ++ fv1), rho', plus c2 (one (Eapp f1 ft1 (gv1 ++ fv1))), plus cout2 (one (Eapp f1 ft1 (gv1 ++ fv1))))).

  Lemma find_def_fundefs_append_neq_l: forall (f : var) (B B1 : fundefs),
      unique_bindings_fundefs (fundefs_append B B1) ->
      ~ name_in_fundefs B1 f ->
      find_def f (fundefs_append B B1) = find_def f B.
  Proof.
    induction B.
    intros B1 Huniq Hname.
    simpl.
    destruct (M.elt_eq f v); auto.
    inv Huniq.
    apply IHB; auto.
    intros.
    rewrite name_not_in_fundefs_find_def_None; auto.
  Qed.

  Lemma preord_val_fundefs Post' k rho rho1 fds f
    (Hpost_refl_constr : post_constr_compat Post' Post')
    (Hpost_refl_proj : post_proj_compat Post' Post')
    (Hpost_refl_fun : post_fun_compat Post' Post')
    (Hpost_refl_case_hd : post_case_compat_hd Post' Post')
    (Hpost_refl_case_tl : post_case_compat_tl Post' Post')
    (Hpost_refl_app : post_app_compat Post' Post')
    (Hpost_refl_letapp : post_letapp_compat cenv Post' Post' Post')
    (Hpost_refl_letapp_OOT : post_letapp_compat_OOT Post' Post')
    (Hpost_refl_primval : post_primval_compat Post' Post')
    (Hpost_refl_OOT : post_OOT Post')
    (Hpost_refl_base : post_base Post') :
    preord_env_P cenv Post' (occurs_free_fundefs fds) k rho rho1 ->
    preord_val cenv Post' k (Vfun rho fds f) (Vfun rho1 fds f).
  Proof.
    rewrite preord_val_eq. simpl; intros.
    pose (Hlen := H2). apply set_lists_length in Hlen. rewrite <- Hlen in H0.
    rename rho1' into rho'.
    eapply length_exists_set_lists in H0. destruct H0 as [rho1' Hrho1'].
    do 3 eexists. split; [eassumption|split]; [eassumption|].

    intros Hj Hvs. apply preord_exp_refl. now constructor; easy_post.

    assert (preord_env_P cenv Post' (occurs_free_fundefs fds :|: name_in_fundefs fds) j
                         (def_funs fds fds rho rho)
                         (def_funs fds fds rho1 rho1)). {
      apply preord_env_P_monotonic with (k := k). lia.
      apply preord_env_P_def_funs_cor. now constructor; try easy_post.
      eapply preord_env_P_antimon; [eassumption|].
      auto with Ensembles_DB.
    }
    clear H.
    eapply preord_env_P_set_lists_l; [eassumption| |eassumption|eauto|eauto].

    apply find_def_correct in H1.
    assert (occurs_free e1 \\ FromList xs1 \subset occurs_free_fundefs fds :|: name_in_fundefs fds). {
      apply occurs_free_in_fun in H1.
      apply Setminus_Included_Included_Union.
      rewrite Union_commut.
      now rewrite Union_commut with (s1 := occurs_free_fundefs fds).
    }

    intros. assert ((occurs_free e1 \\ FromList xs1) x) by (now split).
    now apply H.
  Qed.

  Lemma Union_Included_subst : forall {A} (a : Ensemble A) b b' c,
    a \subset b :|: c -> b \subset b' -> a \subset b' :|: c.
  Proof with eauto with Ensembles_DB.
    intros A a b b' c Hb Hb' x Hx.
    destruct Hb with (x := x)...
  Qed.

  Lemma name_in_fundefs_bound_var_fundefs : forall fds,
    name_in_fundefs fds \subset bound_var_fundefs fds.
  Proof with auto.
    induction fds; [|simpl;auto with Ensembles_DB].
    inversion 1; subst.
    - inversion H0; subst...
    - apply IHfds in H0...
  Qed.

  Lemma preord_env_P_union_converse : forall A B k rho rho1,
    preord_env_P cenv Post (A :|: B) k rho rho1 ->
    preord_env_P cenv Post A k rho rho1 /\
    preord_env_P cenv Post B k rho rho1.
  Proof.
    split; intros a Hin; apply H; [now left|now right].
  Qed.

  Lemma preord_env_P_set_lists_extend :
    forall cenv Post k vs vs1 vs2 P rho1 rho2 rho1' rho2',
      preord_env_P cenv Post (P \\ FromList vs) k rho1 rho2 ->
      Some rho1' = set_lists vs vs1 rho1 ->
      Some rho2' = set_lists vs vs2 rho2 ->
      Forall2 (preord_val cenv Post k) vs1 vs2 ->
      preord_env_P cenv Post P k rho1' rho2'.
  Proof.
    induction vs; intros vs1 vs2 P rho1 rho2 rho1' rho2' Hrho Hrho1' Hrho2' Hvs1_vs2.
    - destruct vs1; [|apply set_lists_length in Hrho1'; discriminate].
      destruct vs2; [|apply set_lists_length in Hrho2'; discriminate].
      inv Hrho1'; inv Hrho2'.
      eapply preord_env_P_antimon; [apply Hrho|].
      intros a Ha; split; [apply Ha|inversion 1].
    - destruct vs1; [apply set_lists_length in Hrho1'; discriminate|].
      destruct vs2; [apply set_lists_length in Hrho2'; discriminate|].
      simpl in Hrho1', Hrho2'.
      destruct (set_lists vs vs1 rho1) as [rho3|] eqn:Hrho3; [|congruence].
      destruct (set_lists vs vs2 rho2) as [rho4|] eqn:Hrho4; [|congruence].
      inv Hrho1'; inv Hrho2'.
      apply preord_env_P_extend; [|now inv Hvs1_vs2].
      eapply IHvs; [|eauto|eauto|now inv Hvs1_vs2].
      eapply preord_env_P_antimon; [apply Hrho|].
      intros a' Ha'; split; [inv Ha'; now inv H|];
        intros contra; inv contra;
        [inv Ha'; inv H; contradiction H2; easy|inv Ha'; inv H0; contradiction].
  Qed.

  Lemma preord_env_P_set_lists_extend' :
    forall cenv Post k vs vs1 vs2 P rho1 rho2 rho1' rho2',
      preord_env_P cenv Post P k rho1 rho2 ->
      Some rho1' = set_lists vs vs1 rho1 ->
      Some rho2' = set_lists vs vs2 rho2 ->
      Forall2 (preord_val cenv Post k) vs1 vs2 ->
      preord_env_P cenv Post P k rho1' rho2'.
  Proof with eauto with Ensembles_DB.
    induction vs; intros vs1 vs2 P rho1 rho2 rho1' rho2' Hrho Hrho1' Hrho2' Hvs1_vs2.
    - destruct vs1; [|apply set_lists_length in Hrho1'; discriminate].
      destruct vs2; [|apply set_lists_length in Hrho2'; discriminate].
      inv Hrho1'; inv Hrho2'.
      eapply preord_env_P_antimon...
    - destruct vs1; [apply set_lists_length in Hrho1'; discriminate|].
      destruct vs2; [apply set_lists_length in Hrho2'; discriminate|].
      simpl in Hrho1', Hrho2'.
      destruct (set_lists vs vs1 rho1) as [rho3|] eqn:Hrho3; [|congruence].
      destruct (set_lists vs vs2 rho2) as [rho4|] eqn:Hrho4; [|congruence].
      inv Hrho1'; inv Hrho2'.
      apply preord_env_P_extend; [|now inv Hvs1_vs2].
      eapply IHvs; [|eauto|eauto|now inv Hvs1_vs2].
      eapply preord_env_P_antimon...
  Qed.

  Lemma preord_env_P_subst : forall cenv Post P k rho rho1 rho' rho1',
    preord_env_P cenv Post P k rho rho1 ->
    (forall a, P a -> M.get a rho = M.get a rho') ->
    (forall a, P a -> M.get a rho1 = M.get a rho1') ->
    preord_env_P cenv Post P k rho' rho1'.
  Proof.
    intros cenv' Post' P k rho rho1 rho' rho1' Heq Hrho Hrho1 a Ha v1 Hv1.
    rewrite <- Hrho in Hv1; [|apply Ha].
    rewrite <- Hrho1; [|apply Ha].
    now apply Heq.
  Qed.

  Lemma set_lists_set_permut : forall {A} x (y : A) xs ys rho rho',
      ~ List.In x xs ->
      Some rho' = set_lists xs ys (M.set x y rho) -> exists rho1,
          Some rho1 = set_lists xs ys rho /\ forall a,
            M.get a rho' = M.get a (M.set x y rho1).
  Proof.
    intros A x y xs ys rho rho' Hx Hrho.
    assert (Hrho1 : length xs = length ys)
      by now apply set_lists_length in Hrho.
    eapply length_exists_set_lists in Hrho1.
    destruct Hrho1 as [rho1 Hrho1].
    exists rho1; split; [apply Hrho1 |].
    intros a.
    split_var_in_list a xs.
    - assert (forall A (l : list A), Forall2 eq l l)
        by (induction l; auto).
      specialize H with (l := ys).
      symmetry in Hrho, Hrho1.
      destruct
        (set_lists_Forall2_get _ _ _ _ _ _ _ _ _ H Hrho Hrho1 i)
        as [v1 [v2 [Hv1 [Hv2 Hv1_v2]]]]; subst.
      rewrite M.gso.
      + transitivity (Some v2); auto.
      + intros Ha; contradiction Hx; now subst.
    - erewrite <- set_lists_not_In;
        [|symmetry in Hrho; apply Hrho |assumption].
      split_var_eq a x; [subst; now do 2 rewrite M.gss |].
      do 2 (rewrite M.gso; [|assumption]).
      erewrite <- set_lists_not_In with (rho' := rho1); eauto.
  Qed.

  Lemma Forall2_preord_val_monotonic : forall cenv Post k k1 l1 l2,
    k1 <= k ->
    Forall2 (preord_val cenv Post k) l1 l2 ->
    Forall2 (preord_val cenv Post k1) l1 l2.
  Proof.
    induction l1; [now inversion 2|intros].
    destruct l2; inv H0.
    constructor; [|now apply IHl1].
    eapply preord_val_monotonic; eassumption.
  Qed.

  Lemma preord_var_env_extend_neq_r : forall cenv Post k rho rho1 a b v,
    preord_var_env cenv Post k rho rho1 a a ->
    a <> b ->
    preord_var_env cenv Post k rho (M.set b v rho1) a a.
  Proof.
    unfold preord_var_env; intros.
    rewrite M.gso; auto.
  Qed.
  Lemma def_funs_get_neq : forall B' B B1 rho a,
    ~ In _ (name_in_fundefs B') a ->
    M.get a (def_funs B1 (fundefs_append B' B) rho rho) =
    M.get a (def_funs B1 B rho rho).
  Proof.
    induction B'.
    - intros; simpl.
      rewrite M.gso.
      apply IHB'; intros contra; contradiction H; now right.
      intros contra; subst; contradiction H; now left.
    - auto.
  Qed.

  Lemma preord_var_env_def_funs_neq : forall cenv Post k B' B B1 B2 B3 rho rho1 a,
    preord_var_env cenv Post k
                   (def_funs B2 B rho rho)
                   (def_funs B3 B1 rho1 rho1) a a ->
    ~ In _ (name_in_fundefs B') a ->
    preord_var_env cenv Post k
                   (def_funs B2 (fundefs_append B' B) rho rho)
                   (def_funs B3 (fundefs_append B' B1) rho1 rho1) a a.
  Proof.
    intros.
    unfold preord_var_env.
    do 2 (rewrite def_funs_get_neq; auto).
  Qed.

  Lemma Ensemble_In : forall {U : Type} S a,
    In U S a -> S a.
  Proof. auto. Qed.

  Lemma preord_var_env_extend' : forall cenv Post rho1 rho2 k x y v1 v2,
    (y <> x -> preord_var_env cenv Post k rho1 rho2 y y) ->
    preord_val cenv Post k v1 v2 ->
    preord_var_env cenv Post k (M.set x v1 rho1) (M.set x v2 rho2) y y.
  Proof.
    intros.
    unfold preord_var_env.
    split_var_eq y x; subst.
    do 2 rewrite M.gss; intros v0 Hv0; inv Hv0; eexists; split; eauto.
    do 2 (rewrite M.gso; auto).
    now apply H.
  Qed.

  Lemma find_def_fundefs_append_eq : forall f B B1,
    name_in_fundefs B f ->
    find_def f (fundefs_append B B1) = find_def f B.
  Proof.
    induction B.
    - intros; simpl.
      destruct (M.elt_eq f v); subst; auto.
      rewrite IHB; auto.
      inv H; auto.
      now inv H0.
    - inversion 1.
  Qed.

  Lemma find_def_fundefs_append_neq : forall f B B1,
    ~ name_in_fundefs B f ->
    find_def f (fundefs_append B B1) = find_def f B1.
  Proof.
    induction B.
    - intros; simpl.
      destruct (M.elt_eq f v); subst.
      contradiction H; now left.
      apply IHB; intros contra.
      contradiction H; now right.
    - auto.
  Qed.

  Lemma occurs_free_fundefs_append : forall fds1 fds a,
    ~ In _ (name_in_fundefs fds1) a ->
    occurs_free_fundefs fds a ->
    occurs_free_fundefs (fundefs_append fds1 fds) a.
  Proof.
    induction fds1.
    intros fds a Ha Hfds.
    simpl; apply Free_Fcons2.
    apply IHfds1; auto.
    intros contra; contradiction Ha.
    now right.
    intros contra; subst; contradiction Ha; now left.
    auto.
  Qed.

  Lemma occurs_free_fundefs_append_l : forall fds1 fds a,
    ~ In _ (name_in_fundefs fds) a ->
    occurs_free_fundefs fds1 a ->
    occurs_free_fundefs (fundefs_append fds1 fds) a.
  Proof.
    induction fds1.
    intros fds a Ha Hfds.
    inv Hfds.
    constructor; auto.
    intros contra.
    assert (In _ (name_in_fundefs (fundefs_append fds1 fds)) a) by auto.
    rewrite fundefs_append_name_in_fundefs in H; [|reflexivity].
    inv H; contradiction.
    apply Free_Fcons2; auto.
    inversion 2.
  Qed.

  Lemma fundefs_append_unique : forall (f : var) (B B1 : fundefs),
    unique_bindings_fundefs (fundefs_append B B1) ->
    name_in_fundefs B1 f ->
    ~ name_in_fundefs B f.
  Proof.
    induction B.
    intros B1 Huniq Hname.
    intros contra.
    inv contra.
    inv H.
    inv Huniq.
    contradiction H5.
    apply Ensemble_In; erewrite fundefs_append_bound_vars; [|reflexivity]; right.
    now apply name_in_fundefs_bound_var_fundefs.
    inv Huniq.
    unfold not in IHB; eapply IHB; eauto.
    inversion 3.
  Qed.

  Lemma fundefs_append_unique_l : forall (f : var) (B1 B : fundefs),
    unique_bindings_fundefs (fundefs_append B1 B) ->
    name_in_fundefs B1 f ->
    ~ name_in_fundefs B f.
  Proof.
    induction B1.
    intros B Huniq Hname.
    intros contra.
    inv Hname.
    inv H.
    inv Huniq.
    contradiction H5.
    apply Ensemble_In; erewrite fundefs_append_bound_vars; [|reflexivity]; right.
    now apply name_in_fundefs_bound_var_fundefs.
    inv Huniq.
    unfold not in IHB1; eapply IHB1; eauto.
    inversion 2.
  Qed.

  Lemma fundefs_append_unique_and : forall B B1,
    unique_bindings_fundefs (fundefs_append B B1) ->
    unique_bindings_fundefs B /\ unique_bindings_fundefs B1.
  Proof.
    induction B.
    intros B1 Huniq; split.
    inv Huniq.
    constructor; auto.
    intros contra.
    contradiction H5; apply Ensemble_In; rewrite fundefs_append_bound_vars; [|reflexivity].
    now left.
    eapply Disjoint_Included_l; eauto.
    intros a Ha; rewrite fundefs_append_bound_vars; [|reflexivity]; now left.
    eapply Disjoint_Included_r; eauto.
    intros a Ha; rewrite fundefs_append_bound_vars; [|reflexivity]; now left.
    edestruct IHB; eauto.
    inv Huniq.
    edestruct IHB; eauto.
    split; auto.
    constructor.
  Qed.

  Lemma fundefs_append_used_vars : forall B B1,
    used_vars_fundefs (fundefs_append B B1) <--> used_vars_fundefs B :|: used_vars_fundefs B1.
  Proof with eauto 10 with Ensembles_DB.
    induction B.
    intros B1; split.
    - intros a Ha.
      simpl in Ha; rewrite used_vars_Fcons in Ha.
      inv Ha. inv H. inv H0. inv H.
      left; left; constructor; now left.
      left; left; constructor; now right.
      left; rewrite used_vars_Fcons...
      rewrite IHB in H.
      inv H.
      left; rewrite used_vars_Fcons...
      now right.
    - intros a Ha.
      rewrite used_vars_Fcons in Ha.
      inv Ha. inv H. inv H0. inv H. inv H0.
      all: simpl; rewrite used_vars_Fcons...
      right; rewrite IHB...
      right; rewrite IHB...
    - intros B1; simpl; rewrite used_vars_Fnil...
  Qed.

  Lemma fundefs_append_ctx_exists : forall f' c',
    exists c, forall e, c <[ e ]> = fundefs_append f' (c' <[ e ]>).
  Proof.
    induction f'.
    intros c'; simpl.
    edestruct IHf' as [c Hc].
    exists (Fcons2_c v f l e c); intros e0; simpl.
    now rewrite Hc.
    intros c'.
    eexists; simpl; eauto.
  Qed.

  (* unnesting fundefs_curried case of uncurry_step_correct *)
  Lemma uncurry_step_correct_fundefs_curried :
    forall k e f ft k0 kt fv g gt gv ge pre_fds fds f1 ft1 fv1 gv1 s rho rho1 already_uncurried,
    let curried := fundefs_append pre_fds
        (Fcons f ft (k0 :: fv) (Efun (Fcons g gt gv ge Fnil) (Eapp k0 kt [g])) fds) in
    let uncurried := fundefs_append pre_fds
        (Fcons f ft (k0 :: fv1)
                (Efun (Fcons g gt gv1 (Eapp f1 ft1 (gv1 ++ fv1)) Fnil) (Eapp k0 kt [g]))
                (Fcons f1 ft1 (gv ++ fv) ge fds)) in
    (used_vars e :|: used_vars_fundefs curried \subset s) ->
    (used_vars e :|: used_vars_fundefs uncurried \subset
       s :|: FromList gv1 :|: FromList fv1 :|: [set f1]) ->
    (match M.get g already_uncurried with
         | Some true => true | Some false => false | None => false end
     = false) ->
    (occurs_in_exp g ge = false) ->
    (occurs_in_exp k0 ge = false) ->
    (unique_bindings_fundefs curried) ->
    (used_vars_fundefs curried \subset s) ->
    (unique_bindings_fundefs uncurried) ->
    (fresh_copies s gv1) ->
    (length gv1 = length gv) ->
    (fresh_copies (s :|: FromList gv1) fv1) ->
    (length fv1 = length fv) ->
    (~ In var (s :|: FromList gv1 :|: FromList fv1) f1) ->
    (preord_env_P cenv PostG (occurs_free (Efun curried e)) k rho rho1) ->
    preord_exp cenv Post PostG k (Efun curried e, rho) (Efun uncurried e, rho1).
  Proof with unfold used_vars in *; eauto 15 with Ensembles_DB.
    intros k e f ft k0 kt fv g gt gv ge pre_fds fds f1 ft1 fv1 gv1 s rho rho1
           already_uncurried curried uncurried
           Hcurried_used Huncurried_used Halready_uncurried
           Hg_nonrec Hk0_nonrec Hcurried_unique_fundefs Hcurried_used_fundefs
           Huncurried_unique_fundefs Hgv1_fresh Hgv_gv1 Hfv1_fresh Hfv_fv1 Hf1_fresh Henv.
    eapply preord_exp_fun_compat. now eapply Hpost_prop. now eapply Hpost_prop.
    apply preord_exp_refl. eassumption.
    intros h Hh; unfold preord_var_env.

    (* useful facts for later *)
    assert (Hf1_gv1 : ~ List.In f1 gv1). {
      rewrite Union_demorgan in Hf1_fresh; destruct Hf1_fresh as [Hf1_fresh2 Hf1_fresh3].
      rewrite Union_demorgan in Hf1_fresh2; destruct Hf1_fresh2 as [Hf1_fresh1 Hf1_fresh2].
      assumption.
    }
    assert (Hf1_k0fv1 : ~ List.In f1 (k0 :: fv1)). {
      rewrite Union_demorgan in Hf1_fresh; destruct Hf1_fresh as [Hf1_fresh2 Hf1_fresh3].
      rewrite Union_demorgan in Hf1_fresh2; destruct Hf1_fresh2 as [Hf1_fresh1 Hf1_fresh2].
      intros contra; inv contra; [|contradiction].
      apply fundefs_append_unique_and in Huncurried_unique_fundefs.
      destruct Huncurried_unique_fundefs as [HL HR].
      inv HR. inv H7. contradiction (H f1).
      split.
      constructor; now left.
      now left.
    }
    assert (Hg_f1 : g <> f1). {
      intros contra; subst.
      apply fundefs_append_unique_and in Huncurried_unique_fundefs.
      destruct Huncurried_unique_fundefs as [HL HR].
      inv HR. inv H8.
      contradiction (H f1).
      split.
      constructor; constructor; now left.
      constructor; now left.
    }
    assert (f_f1 : f <> f1). {
      intros contra; subst.
      apply fundefs_append_unique_and in Huncurried_unique_fundefs.
      destruct Huncurried_unique_fundefs as [HL HR].
      inv HR. contradiction H5; constructor; now left.
    }
    assert (Hk0_fv1 : ~ List.In k0 fv1). {
      intros contra.
      apply fundefs_append_unique_and in Huncurried_unique_fundefs.
      destruct Huncurried_unique_fundefs as [HL HR].
      inv HR. now inv H10.
    }
    assert (Hg_fv1 : ~ List.In g fv1). {
      intros contra.
      apply fundefs_append_unique_and in Huncurried_unique_fundefs.
      destruct Huncurried_unique_fundefs as [HL HR].
      inv HR.
      inv H6.
      contradiction (H g).
      split.
      constructor; constructor; now left.
      now right.
    }
    assert (Hk0_g : k0 <> g). {
      intros contra; subst.
      apply fundefs_append_unique_and in Hcurried_unique_fundefs.
      destruct Hcurried_unique_fundefs as [HL HR].
      inv HR.
      inv H6. contradiction (H g).
      split.
      constructor; constructor; now left.
      now left.
    }
    assert (Hf1_pre_fds : ~ name_in_fundefs pre_fds f1). {
      intros contra.
      apply fundefs_append_unique_l with (f := f1) in Huncurried_unique_fundefs; auto.
      contradiction Huncurried_unique_fundefs.
      right; now left.
    }
    assert (Hf_pre_fds : ~ name_in_fundefs pre_fds f). {
      intros contra.
      apply fundefs_append_unique_l with (f := f) in Hcurried_unique_fundefs; auto.
      contradiction Hcurried_unique_fundefs.
      now left.
    }
    assert (Hcurried_uncurried : name_in_fundefs curried \subset name_in_fundefs uncurried). {
      intros a Ha.
      rewrite fundefs_append_name_in_fundefs; [|reflexivity].
      split_var_in_fundefs a pre_fds Ha_pre_fds.
      now left.
      split_var_eq a f; subst.
      right; now left.
      split_var_in_fundefs a fds Ha_fds.
      right; right; now right.
      rewrite fundefs_append_name_in_fundefs in Ha; [|reflexivity].
      inv Ha; try contradiction.
      inv H; try contradiction.
      inv H0; contradiction.
    }
    assert (Hgv_g : ~ List.In g gv). {
      intros contra.
      apply fundefs_append_unique_and in Hcurried_unique_fundefs.
      destruct Hcurried_unique_fundefs as [HL HR].
      inv HR.
      inv H11.
      now inv H2.
    }
    assert (Hpre_fds_curried : name_in_fundefs pre_fds \subset name_in_fundefs curried). {
      subst curried; intros a Ha.
      rewrite fundefs_append_name_in_fundefs; [|reflexivity]; now left.
    }
    assert (Hpre_fds_uncurried : name_in_fundefs pre_fds \subset name_in_fundefs uncurried). {
      subst uncurried; intros a Ha.
      rewrite fundefs_append_name_in_fundefs; [|reflexivity]; now left.
    }
    assert (Hf1_ge : ~ In _ (occurs_free ge) f1). {
      intros contra1.
      rewrite Union_demorgan in Hf1_fresh; destruct Hf1_fresh as [Hf1_fresh2 Hf1_fresh3];
      rewrite Union_demorgan in Hf1_fresh2; destruct Hf1_fresh2 as [Hf1_fresh1 Hf1_fresh2].
      contradiction Hf1_fresh1.
      apply Hcurried_used; right; right.
      subst curried; apply occurs_free_fundefs_append; auto.
      constructor; auto.
      inversion 1; subst.
      - apply fundefs_append_unique_and in Huncurried_unique_fundefs.
        destruct Huncurried_unique_fundefs as [HL HR].
        inv HR.
        inv H8; contradiction (H0 f1).
        split; [constructor; now left|now left].
      - apply fundefs_append_unique_and in Huncurried_unique_fundefs.
        destruct Huncurried_unique_fundefs as [HL HR].
        inv HR.
        inv H14.
        contradiction H20.
        apply Ensemble_In; rewrite FromList_app.
        now right.
      - apply fundefs_append_unique_and in Huncurried_unique_fundefs.
        destruct Huncurried_unique_fundefs as [HL HR].
        inv HR.
        inv H12.
        intros contra; contradiction H14; now apply name_in_fundefs_bound_var_fundefs.
      - apply Free_Efun2.
        constructor; auto; [|inversion 1].
        intros contra.
        apply fundefs_append_unique_and in Huncurried_unique_fundefs.
        destruct Huncurried_unique_fundefs as [HL HR].
        inv HR.
        inv H12.
        contradiction H18; apply Ensemble_In; rewrite FromList_app; now left.
    }
    assert (Hf1_curried : ~ In _ (name_in_fundefs curried) f1). {
      intros contra.
      rewrite Union_demorgan in Hf1_fresh; destruct Hf1_fresh as [Hf1_fresh2 Hf1_fresh3];
      rewrite Union_demorgan in Hf1_fresh2; destruct Hf1_fresh2 as [Hf1_fresh1 Hf1_fresh2].
      contradiction Hf1_fresh1.
      apply Hcurried_used; right; left.
      now apply name_in_fundefs_bound_var_fundefs.
    }
    assert (Hf_curried : In _ (name_in_fundefs curried) f). {
      rewrite fundefs_append_name_in_fundefs; [|reflexivity].
      right; now left.
    }
    assert (Hf_uncurried : In _ (name_in_fundefs uncurried) f) by now apply Hcurried_uncurried.

    split_var_in_fundefs
      h
      curried
      Hfds; clear Hfds; rename n into Hfds; simpl in Hfds.
    - (* h\in pre_fds ++ f |: fundefs(fds) *)
      rewrite def_funs_eq; auto.
      rewrite def_funs_eq; [|now apply Hcurried_uncurried].
      intros v1 Hv1; inv Hv1.
      eexists; split; [reflexivity|].
      generalize dependent h. generalize dependent e.
      induction k as [k IHk] using lt_wf_rec1.
      (* Opaque preord_exp. *)
      intros e Hcurried_used Huncurried_used Henv h Hh Hfds.
      split_var_eq h f; subst; rewrite preord_val_eq; simpl.
      + (* h = f *)
        rename curried into curried'; pose (curried := curried').
        rename uncurried into uncurried'; pose (uncurried := uncurried').
        subst curried'; subst uncurried'.
        do 2 (rewrite find_def_fundefs_append_neq; auto; simpl).
        destruct (M.elt_eq f f) as [Heq|]; [clear Heq|contradiction].
        intros vs1 vs2 k1 t xs1 e1 rho' Hlen_vs1_vs2 Hsome Hrho'; inv Hsome.
        assert (Hrho1' : length (k0 :: fv1) = length vs2). {
          apply set_lists_length in Hrho'.
          rewrite <- Hlen_vs1_vs2.
          rewrite <- Hrho'.
          simpl; rewrite Hfv_fv1.
          reflexivity.
        }
        eapply length_exists_set_lists in Hrho1'.
        destruct Hrho1' as [rho1' Hrho1'].
        do 3 eexists; split; [reflexivity|split]; [eassumption|intros Hk1 Hvs1_vs2].
        eapply preord_exp_fun_compat.
        now eapply Hpost_propG.
        now eapply Hpost_propG.

        apply preord_exp_refl. eassumption.

        (* wrt k0 and g, the environments
             rho'' = g + [k0 :: fv -> vs1] + curried f + fds + rho
             rho1'' = uncurried g + [k0 :: fv1 -> vs2] + uncurried f + f1 + fds + rho1
           agree. *)
        destruct vs1 as [|hvs1 tvs1]; [apply set_lists_length in Hrho'; inv Hrho'|].
        destruct vs2 as [|hvs2 tvs2]; [apply set_lists_length in Hrho1'; inv Hrho1'|].
        intros a Ha.
        inv Ha; [rename a into k0|inv H3]; [|rename a into g|inv H].
        * (* k0: hvs1 == hvs2 *)
          unfold preord_var_env; simpl.
          do 2 (rewrite M.gso; [|assumption]).
          apply set_set_lists in Hrho'; destruct Hrho' as [rho'k0 [Hrho' Hrho'k0]].
          apply set_set_lists in Hrho1'; destruct Hrho1' as [rho1'k0 [Hrho1' Hrho1'k0]].
          subst rho'; subst rho1'; do 2 rewrite M.gss.
          intros v1 Hv1; inv Hv1; eexists; split; [reflexivity|inv Hvs1_vs2].
          eapply preord_val_monotonic; eauto; lia.
        * (* g *)
          unfold preord_var_env; simpl.
          do 2 rewrite M.gss.
          intros v1 Hv1; inv Hv1; eexists; split; [reflexivity|].
          rewrite preord_val_eq; simpl.
          destruct (M.elt_eq g g) as [Heq|]; [clear Heq|contradiction].
          intros vs3 vs4 k2 t0 xs1 e1 rho'' Hlen_vs3_vs4 Hsome Hrho''.
          inversion Hsome; subst t0; subst xs1; subst e1; clear Hsome.
          assert (Hrho1'' : length gv1 = length vs4). {
            apply set_lists_length in Hrho''.
            rewrite <- Hlen_vs3_vs4.
            rewrite <- Hrho''.
            assumption.
          }
          eapply length_exists_set_lists in Hrho1''; destruct Hrho1'' as [rho1'' Hrho1''].
          do 3 eexists; split; [reflexivity|split]; [eassumption|intros Hk2 Hvs3_vs4].
          assert (Hrho''' : length (gv ++ fv) = length (vs4 ++ tvs2)). {
            do 2 rewrite length_app.
            apply set_lists_length in Hrho1''.
            rewrite <- Hrho1''.
            rewrite <- Hgv_gv1.
            apply set_lists_length in Hrho1'.
            inv Hrho1'.
            rewrite <- Hfv_fv1.
            reflexivity.
          }
          (* Transparent preord_exp. *)
          intros v1 c1 cout Hc1 Hv1.
          apply @length_exists_set_lists with
            (rho := (def_funs uncurried uncurried rho1 rho1)) in Hrho'''.
          destruct Hrho''' as [rho''' Hrho'''].
          assert (Hgoal : preord_exp cenv Post PostG k2 (ge, rho'') (ge, rho''')). {
            apply preord_exp_refl. eassumption.

            (* wrt free variables of ge, the environments
                 rho'' = [gv -> vs3] + g + [k0 :: fv -> vs1] + curried f + fds + rho
                 rho''' = [gv ++ fv -> vs4 ++ tvs2] + uncurried f + f1 + fds + rho1
               agree.
             *)

            (* rho''g := rho'' \ g *)
            eapply set_lists_set_permut in Hgv_g; [|apply Hrho''].
            destruct Hgv_g as [rho''g [Hrho''g Hrho''_rho''g]].
            eapply preord_env_P_subst; [|intros a Ha;symmetry; apply Hrho''_rho''g|reflexivity].
            apply preord_env_P_set_not_in_P_l;
              [|apply Disjoint_Union_r with (s1 := bound_var ge);
                replace (bound_var ge :|: occurs_free ge) with (used_vars ge) by reflexivity;
                now rewrite <- occurs_in_exp_correct].

            (* split [gv ++ fv -> vs4 ++ tvs2] into [gv -> vs4] + [fv -> tvs2] *)
            symmetry in Hrho'''; eapply set_lists_app in Hrho''';
              [|apply set_lists_length in Hrho1''; now rewrite <- Hrho1''].
            destruct Hrho''' as [rho'''fv [Hrho'''fv Hrho''']].

            (* [[gv]](rho''g) ==_k2 [[gv]](rho''') *)
            eapply preord_env_P_set_lists_extend; eauto.

            (* rho'k0 := rho' \ k0 *)
            eapply set_set_lists in Hrho'; destruct Hrho' as [rho'k0 [Hrho' Hrho'k0]]; subst rho'.
            apply preord_env_P_set_not_in_P_l;
              [|eapply Disjoint_Included_l;
                  [|rewrite <- occurs_in_exp_correct];
                  [|apply Hk0_nonrec];
                apply Setminus_Included_preserv;
                eapply Included_Union_r].

            (* [[fv]](rho'k0) ==_k2 [[gv]](rho''') *)
            inv Hvs1_vs2.
            eapply preord_env_P_set_lists_extend; eauto;
              [|eapply Forall2_preord_val_monotonic];
              [| |eassumption];
              [|lia].

            intros a Ha.
            (* remove pre_fds from (pre_fds + curried f + fds + rho),
                                   (pre_fds + f + f1 + fds + rho1) *)
            split_var_in_fundefs a pre_fds Hpre_fds. {
              unfold preord_var_env.
              rewrite def_funs_eq; [|now apply Hpre_fds_curried].
              rewrite def_funs_eq; [|now apply Hpre_fds_uncurried].
              intros v0 Hv0; inv Hv0; eexists; split; [reflexivity|].
              eapply preord_val_monotonic; [apply IHk with (m := k1) (e := Ehalt a)|];
                [lia| | | |constructor| |lia].
              * rewrite Union_Same_set; [assumption|].
                unfold used_vars.
                rewrite bound_var_Ehalt.
                rewrite Union_Empty_set_neut_l.
                intros a' Ha'; inv Ha'; left.
                rewrite fundefs_append_bound_vars; [|reflexivity]; left.
                now apply name_in_fundefs_bound_var_fundefs.
              * unfold used_vars.
                rewrite bound_var_Ehalt.
                rewrite Union_Empty_set_neut_l.
                rewrite Union_Same_set; [eapply Union_Included_r; eassumption|].
                intros a' Ha'; inv Ha'; left.
                rewrite fundefs_append_bound_vars; [|reflexivity]; left.
                now apply name_in_fundefs_bound_var_fundefs.
              * eapply preord_env_P_antimon.
                eapply preord_env_P_monotonic; [|eassumption]; lia.
                intros a' Ha'; inv Ha'.
                inv H5; contradiction H1.
                apply Ensemble_In.
                rewrite fundefs_append_name_in_fundefs; [|reflexivity]; now left.
                now apply Free_Efun2.
              * apply Ensemble_In.
                rewrite fundefs_append_name_in_fundefs; [|reflexivity]; now left.
            }
            rename uncurried into uncurried'; pose (uncurried := uncurried'); subst uncurried'.
            apply preord_var_env_def_funs_neq; auto.

            (* remove curried f, uncurried f *)
            simpl; apply preord_var_env_extend'. intros Ha_f.

            (* remove f1 *)
            apply preord_var_env_extend_neq_r.

            (* remove fds *) {
            rename Hfds into Hname_fds.
            split_var_in_fundefs a fds Hfds.
            - unfold preord_var_env.
              do 2 (rewrite def_funs_eq; [|assumption]).
              intros v0 Hv0; inv Hv0; eexists; split; [reflexivity|].
              eapply preord_val_monotonic; [apply IHk with (m := k1) (e := Ehalt a)|];
                [lia| | | |constructor| |lia].
              * rewrite Union_Same_set; [assumption|].
                unfold used_vars.
                rewrite bound_var_Ehalt.
                rewrite Union_Empty_set_neut_l.
                intros a' Ha'; inv Ha'; left.
                rewrite fundefs_append_bound_vars; [|reflexivity].
                right; apply Bound_Fcons2.
                now apply name_in_fundefs_bound_var_fundefs.
              * unfold used_vars.
                rewrite bound_var_Ehalt.
                rewrite Union_Empty_set_neut_l.
                rewrite Union_Same_set; [eapply Union_Included_r; eassumption|].
                intros a' Ha'; inv Ha'; left.
                rewrite fundefs_append_bound_vars; [|reflexivity].
                right; do 2 apply Bound_Fcons2.
                now apply name_in_fundefs_bound_var_fundefs.
              * eapply preord_env_P_antimon.
                eapply preord_env_P_monotonic; [|eassumption]; lia.
                intros a' Ha'; inv Ha'.
                inv H5; contradiction H1.
                apply Ensemble_In; rewrite fundefs_append_name_in_fundefs; [|reflexivity].
                right; now right.
                now apply Free_Efun2.
              * apply Ensemble_In; rewrite fundefs_append_name_in_fundefs; [|reflexivity].
                right; now right.
            - unfold preord_var_env.
              do 2 (rewrite def_funs_neq; auto).
              assert ((occurs_free ge
                                   \\ FromList gv
                                   \\ FromList fv
                                   \\ [set f]
                                   \\ name_in_fundefs pre_fds
                                   \\ name_in_fundefs fds) a). {
                do 3 (split; auto).
                intros contra; now inv contra.
              }
              clear Ha; clear n; clear Ha_f; clear n0; generalize dependent a.
              eapply preord_env_P_antimon.
              eapply preord_env_P_monotonic; [|apply Henv]; lia.
              intros a Ha; inv Ha; inv H; inv H1; inv H.
              apply Free_Efun2.
              apply occurs_free_fundefs_append; auto.
              apply Free_Fcons1;
                [intros contra; subst; now contradiction H5| |assumption|].
              * intros contra; inv contra; [|contradiction].
                rewrite occurs_in_exp_correct in Hk0_nonrec.
                rewrite Disjoint_Singleton_In in Hk0_nonrec; auto with Decidable_DB.
                contradiction Hk0_nonrec; inv H1; now right.
              * inv H1.
                apply Free_Efun2; apply Free_Fcons1; [|assumption|inversion 1|assumption].
                intros contra; subst.
                rewrite occurs_in_exp_correct in Hg_nonrec.
                rewrite Disjoint_Singleton_In in Hg_nonrec; auto with Decidable_DB.
                contradiction Hg_nonrec; now right.
            }

            (* f1 not in (occurs_free ge) *) {
              intros contra; subst; inv Ha; inv H.
              contradiction.
            }

            (* [[curried f]](f + fds + rho) ==_k2 [[uncurried f]](f + f1 + fds + rho1) *) {
              eapply preord_val_monotonic; [eapply IHk with (m := k1); eauto|]; try lia.
              eapply preord_env_P_monotonic; [|eassumption]; lia.
            }
          }
          unfold preord_exp' in Hgoal.
          specialize Hgoal with (v1 := v1) (cin := c1) (cout := cout); destruct Hgoal; [apply Hc1|apply Hv1|].
          rename x into v2; destruct H as [c2 [cout' [Hv2 [Hvpost Hv1_v2]]]].
          eexists; exists (plus c2 (one (Eapp f1 ft1 (gv1 ++ fv1) : exp))),
                   (plus cout' (one (Eapp f1 ft1 (gv1 ++ fv1) : exp))); split; [|split; [|eassumption]].
          2: { eapply Hpost_curry. eassumption. }

          apply BStepf_run.
          eapply BStept_app; eauto.
          { erewrite <- set_lists_not_In; [|symmetry; eassumption|assumption].
            rewrite M.gso; [|auto].
            erewrite <- set_lists_not_In; [|symmetry; eassumption|assumption].
            rewrite def_funs_get_neq; auto.
            simpl; rewrite M.gso; auto.
            now rewrite M.gss. }
          { apply get_list_app.
            eapply get_list_set_lists; [now inv Hgv1_fresh|symmetry; eassumption].
            erewrite get_list_set_lists_Disjoint;
              [|inv Hfv1_fresh; apply Disjoint_Union_r in H; apply H|symmetry; eassumption].
            rewrite get_list_set_neq; [|assumption].
            apply set_set_lists in Hrho1'.
            destruct Hrho1' as [rho1'k0 [Hrho1'k0 Hrho1']]; subst rho1'.
            rewrite get_list_set_neq; [|assumption].
            eapply get_list_set_lists; [now inv Hfv1_fresh|symmetry; eassumption]. }
          { rename uncurried into uncurried'; pose (uncurried := uncurried'); subst uncurried'.
            rewrite find_def_fundefs_append_neq; auto.
            simpl; destruct (M.elt_eq f1 f) as [|Heq]; [now subst|clear Heq].
            destruct (M.elt_eq f1 f1) as [Heq|]; [clear Heq|contradiction].
            reflexivity. }
      + (* h \in pre_fds ++ fds *)
        assert (Hf' : h <> f). {
          intros contra; subst; inv Hcurried_unique_fundefs.
          now apply name_in_fundefs_bound_var_fundefs in Hfds.
          contradiction. }
        assert (Hf1: h <> f1). {
          (* f1 is not in curried (freshly generated by uncurrier) *)
          intros contra; subst; contradiction. }
        destruct (M.elt_eq h f) as [|Heq]; [contradiction|clear Heq].
        destruct (M.elt_eq h f1) as [|Heq]; [contradiction|clear Heq].
        intros vs1 vs2 k1 t xs1 e1 rho' Hlen_vs1_vs2 Hfind_def Hrho'.
        assert (Hrho1' : length xs1 = length vs2). {
          apply set_lists_length in Hrho'.
          now rewrite <- Hlen_vs1_vs2. }
        eapply length_exists_set_lists in Hrho1'; destruct Hrho1' as [rho1' Hrho1'].
        exists xs1, e1; eexists; split; [|split]; [|eassumption|intros Hk1 Hvs1_vs2].
        (* only f is uncurried, so h in uncurried = h in curried (Hfind_def) *)
        assert (HLR : In _ (name_in_fundefs curried) h) by auto.
        rewrite fundefs_append_name_in_fundefs in HLR; [|reflexivity].
        split_var_in_fundefs h pre_fds Hh_pre_fds.
        subst curried; subst uncurried.
        rewrite find_def_fundefs_append_eq; auto.
        rewrite find_def_fundefs_append_eq in Hfind_def; auto.
        inv HLR; [contradiction|]; inv H; [inv H0; contradiction|].
        subst curried; subst uncurried.
        rewrite find_def_fundefs_append_neq; auto.
        rewrite find_def_fundefs_append_neq in Hfind_def; auto.
        simpl; simpl in Hfind_def.
        destruct (M.elt_eq h f); try contradiction.
        destruct (M.elt_eq h f1); try contradiction; auto.
        apply preord_exp_refl. eassumption.

        (* wrt free variables of e1, the environments
             rho' = [xs1 -> vs1] + f + fds + rho
             rho1' = [xs1 -> vs2] + f + f1 + fds + rho1
           agree.
         *)

        (* [[xs1]](rho') ==_k1 [[xs1]](rho1') *)
        eapply preord_env_P_set_lists_extend; eauto.

        (* remove pre_fds *)
        intros a Ha.
        split_var_in_fundefs a pre_fds Hpre_fds. {
          unfold preord_var_env.
          rewrite def_funs_eq; [|now apply Hpre_fds_curried].
          rewrite def_funs_eq; [|now apply Hpre_fds_uncurried].
          intros v0 Hv0; inv Hv0; eexists; split; [reflexivity|].
          eapply preord_val_monotonic;
          [apply IHk with (m := k - 1) (e := Ehalt a)|]; [lia| | | |constructor| |lia].
          * rewrite Union_Same_set; [assumption|].
            unfold used_vars.
            rewrite bound_var_Ehalt.
            rewrite Union_Empty_set_neut_l.
            intros a' Ha'; inv Ha'; left.
            rewrite fundefs_append_bound_vars; [|reflexivity]; left.
            now apply name_in_fundefs_bound_var_fundefs.
          * unfold used_vars.
            rewrite bound_var_Ehalt.
            rewrite Union_Empty_set_neut_l.
            rewrite Union_Same_set; [eapply Union_Included_r; eassumption|].
            intros a' Ha'; inv Ha'; left.
            rewrite fundefs_append_bound_vars; [|reflexivity]; left.
            now apply name_in_fundefs_bound_var_fundefs.
          * eapply preord_env_P_antimon.
            eapply preord_env_P_monotonic; [|eassumption]; lia.
            intros a' Ha'; inv Ha'.
            inv H3; contradiction H1.
            apply Ensemble_In.
            rewrite fundefs_append_name_in_fundefs; [|reflexivity]; now left.
            now apply Free_Efun2.
          * apply Ensemble_In.
            rewrite fundefs_append_name_in_fundefs; [|reflexivity]; now left.
        }
        rename uncurried into uncurried'; pose (uncurried := uncurried'); subst uncurried'.
        apply preord_var_env_def_funs_neq; auto.

        (* remove f and f1 *)
        simpl; apply preord_var_env_extend'. intros Ha_f.
        apply preord_var_env_extend_neq_r.

        (* remove fds *) {
          split_var_in_fundefs a fds Hfds'; unfold preord_var_env; simpl.
          - do 2 (rewrite def_funs_eq; [|assumption]).
            intros v1 Hv1; inv Hv1; eexists; split; [reflexivity|].
            (* todo: basically a duplicate with the previous application of IH *)
            eapply preord_val_monotonic;
            [apply IHk with (m := k - 1) (e := Ehalt a)|]; [lia| | | |constructor| |lia].
            + rewrite Union_Same_set; [assumption|].
              unfold used_vars.
              rewrite bound_var_Ehalt.
              rewrite Union_Empty_set_neut_l.
              intros a' Ha'; inv Ha'; left.
              rewrite fundefs_append_bound_vars; [|reflexivity].
              right; apply Bound_Fcons2.
              now apply name_in_fundefs_bound_var_fundefs.
            + unfold used_vars.
              rewrite bound_var_Ehalt.
              rewrite Union_Empty_set_neut_l.
              rewrite Union_Same_set; [eapply Union_Included_r; eassumption|].
              intros a' Ha'; inv Ha'; left.
              rewrite fundefs_append_bound_vars; [|reflexivity].
              right; do 2 apply Bound_Fcons2.
              now apply name_in_fundefs_bound_var_fundefs.
            + eapply preord_env_P_antimon.
              eapply preord_env_P_monotonic; [|eassumption]; lia.
              intros a' Ha'; inv Ha'.
              inv H3; contradiction H1.
              apply Ensemble_In; rewrite fundefs_append_name_in_fundefs; [|reflexivity].
              right; now right.
              now apply Free_Efun2.
            + apply Ensemble_In; rewrite fundefs_append_name_in_fundefs; [|reflexivity].
              right; now right.
          - unfold preord_var_env.
            do 2 (rewrite def_funs_neq; auto).
            assert ((occurs_free e1
                                 \\ FromList xs1
                                 \\ [set f]
                                 \\ name_in_fundefs pre_fds
                                 \\ name_in_fundefs fds) a). {
              do 3 (split; auto).
              intros contra; now inv contra.
            }
            clear Ha; clear n1; clear Ha_f; clear n0; generalize dependent a.
            eapply preord_env_P_antimon.
            eapply preord_env_P_monotonic; [|eassumption]; lia.
            intros a Ha; inv Ha; inv H; inv H1; inv H.
            apply Free_Efun2.
            subst curried.
            split_var_in_fundefs h pre_fds Hh_pre_fds.
            + apply occurs_free_fundefs_append_l.
              intros contra; inv contra; auto.
              eapply find_def_is_Some_occurs_free_fundefs; eauto.
              rewrite <- find_def_fundefs_append_neq_l
                with (B1 := Fcons f ft (k0 :: fv)
                                 (Efun (Fcons g gt gv ge Fnil) (Eapp k0 kt [g])) fds); auto.
              apply Hfind_def.
              intros contra; inv contra.
              apply fundefs_append_unique with (f := h) in Huncurried_unique_fundefs.
              contradiction.
              now inv H.
              apply fundefs_append_unique with (f := h) in Huncurried_unique_fundefs.
              contradiction.
              right; now right.
            + apply occurs_free_fundefs_append; auto.
              apply Free_Fcons2; [|intros contra; subst; now contradiction H3].
              eapply find_def_is_Some_occurs_free_fundefs; eauto.
              rewrite <- find_def_fundefs_append_neq
                with (B := Fcons f ft (k0 :: fv)
                                 (Efun (Fcons g gt gv ge Fnil) (Eapp k0 kt [g])) Fnil); auto.
              rewrite <- find_def_fundefs_append_neq with (B := pre_fds); auto.
              apply Hfind_def.
              auto.
              intros contra; inv contra; now inv H.
        }

        (* f1 never occurs in the definition of h *)
        {
          intros contra; subst.
          rewrite Union_demorgan in Hf1_fresh; destruct Hf1_fresh as [Hf1_fresh2 Hf1_fresh3].
          rewrite Union_demorgan in Hf1_fresh2; destruct Hf1_fresh2 as [Hf1_fresh1 Hf1_fresh2].
          contradiction Hf1_fresh1.
          apply Hcurried_used_fundefs.
          right.
          eapply find_def_is_Some_occurs_free_fundefs; eauto; now inv Ha.
        }

        (* [[curried f]](rho') ==_k1 [[uncurried f]](rho1') *)
        eapply preord_val_monotonic;
        [apply IHk with (m := k - 1) (e := Ehalt f)|lia]; [lia| | | |constructor|assumption].
        (* todo: basically a duplicate with the previous application of IH,
           but with left instaed of right soemtimes *)
        * rewrite Union_Same_set; [assumption|].
          unfold used_vars.
          rewrite bound_var_Ehalt.
          rewrite Union_Empty_set_neut_l.
          intros b Hb; inv Hb.
          left; now apply name_in_fundefs_bound_var_fundefs.
        * unfold used_vars.
          rewrite bound_var_Ehalt.
          rewrite Union_Empty_set_neut_l.
          rewrite Union_Same_set; [eapply Union_Included_r; eassumption|].
          rewrite occurs_free_Ehalt.
          intros b Hb; inv Hb.
          left; now apply name_in_fundefs_bound_var_fundefs.
        * eapply preord_env_P_antimon.
          eapply preord_env_P_monotonic; [|eassumption]; lia.
          repeat normalize_occurs_free.
          intros b Hb; inv Hb.
          now left.
          inv H.
          contradiction H1.
          now inv H0.
    - (* h\not\in pre_fds ++ f |: fundefs(fds) *)
      assert (h <> f). {
        intros contra; subst.
        contradiction Hfds.
      }
      assert (h <> f1). {
        intros contra; subst.
        rewrite Union_demorgan in Hf1_fresh; destruct Hf1_fresh as [Hf1_fresh2 Hf1_fresh3].
        rewrite Union_demorgan in Hf1_fresh2; destruct Hf1_fresh2 as [Hf1_fresh1 Hf1_fresh2].
        contradiction Hf1_fresh1.
        apply Hcurried_used.
        now left; right.
      }
      simpl.
      rename curried into curried'; pose (curried := curried'); subst curried'.
      rename uncurried into uncurried'; pose (uncurried := uncurried'); subst uncurried'.
      assert (~ name_in_fundefs fds h). {
        intros contra; contradiction Hfds.
        apply Ensemble_In; rewrite fundefs_append_name_in_fundefs; [|reflexivity].
        right; now right.
      }
      assert (~ name_in_fundefs pre_fds h). {
        intros contra; contradiction Hfds.
        apply Ensemble_In; rewrite fundefs_append_name_in_fundefs; [|reflexivity].
        now left.
      }
      do 2 (rewrite def_funs_get_neq; auto).
      simpl; do 3 (rewrite M.gso; auto).
      do 2 (rewrite def_funs_neq; [|assumption]).
      unfold preord_env_P, preord_var_env in Henv.
      intros v1 Hv1.
      edestruct Henv as [v2 [Hv2 Hv12]]; try eassumption.
      + constructor; [simpl|assumption]; auto.
      + eexists; split; eapply preord_val_monotonic in Hv12; eauto; lia.
  Qed.

  (* the same thing, but for anf uncurrying *)
  Lemma uncurry_step_correct_fundefs_curried_anf :
    forall k e f ft fv g gt gv ge pre_fds fds f1 ft1 fv1 gv1 s rho rho1 already_uncurried,
    let curried := fundefs_append pre_fds
        (Fcons f ft fv (Efun (Fcons g gt gv ge Fnil) (Ehalt g)) fds) in
    let uncurried := fundefs_append pre_fds
        (Fcons f ft fv1
                (Efun (Fcons g gt gv1 (Eapp f1 ft1 (gv1 ++ fv1)) Fnil) (Ehalt g))
                (Fcons f1 ft1 (gv ++ fv) ge fds)) in
    (used_vars e :|: used_vars_fundefs curried \subset s) ->
    (used_vars e :|: used_vars_fundefs uncurried \subset
       s :|: FromList gv1 :|: FromList fv1 :|: [set f1]) ->
    (match M.get g already_uncurried with
         | Some true => true | Some false => false | None => false end
     = false) ->
    (occurs_in_exp g ge = false) ->
    (unique_bindings_fundefs curried) ->
    (used_vars_fundefs curried \subset s) ->
    (unique_bindings_fundefs uncurried) ->
    (fresh_copies s gv1) ->
    (length gv1 = length gv) ->
    (fresh_copies (s :|: FromList gv1) fv1) ->
    (length fv1 = length fv) ->
    (~ In var (s :|: FromList gv1 :|: FromList fv1) f1) ->
    (preord_env_P cenv PostG (occurs_free (Efun curried e)) k rho rho1) ->
    preord_exp cenv Post PostG k (Efun curried e, rho) (Efun uncurried e, rho1).
  Proof with unfold used_vars in *; eauto 15 with Ensembles_DB.
    intros k e f ft fv g gt gv ge pre_fds fds f1 ft1 fv1 gv1 s rho rho1
           already_uncurried curried uncurried
           Hcurried_used Huncurried_used Halready_uncurried
           Hg_nonrec Hcurried_unique_fundefs Hcurried_used_fundefs
           Huncurried_unique_fundefs Hgv1_fresh Hgv_gv1 Hfv1_fresh Hfv_fv1 Hf1_fresh Henv.
    eapply preord_exp_fun_compat. now eapply Hpost_prop. now eapply Hpost_prop.
    apply preord_exp_refl. eassumption.
    intros h Hh; unfold preord_var_env.

    (* useful facts for later *)
    assert (Hf1_gv1 : ~ List.In f1 gv1). {
      rewrite Union_demorgan in Hf1_fresh; destruct Hf1_fresh as [Hf1_fresh2 Hf1_fresh3].
      rewrite Union_demorgan in Hf1_fresh2; destruct Hf1_fresh2 as [Hf1_fresh1 Hf1_fresh2].
      assumption.
    }
    assert (Hf1_k0fv1 : ~ List.In f1 fv1). {
      rewrite Union_demorgan in Hf1_fresh; destruct Hf1_fresh as [Hf1_fresh2 Hf1_fresh3].
      rewrite Union_demorgan in Hf1_fresh2; destruct Hf1_fresh2 as [Hf1_fresh1 Hf1_fresh2].
      apply fundefs_append_unique_and in Huncurried_unique_fundefs.
      destruct Huncurried_unique_fundefs as [HL HR].
      intros contra.
      inv HR. inv H7. contradiction (H f1).
      split.
      constructor; now left.
      apply contra.
    }
    assert (Hg_f1 : g <> f1). {
      intros contra; subst.
      apply fundefs_append_unique_and in Huncurried_unique_fundefs.
      destruct Huncurried_unique_fundefs as [HL HR].
      inv HR. inv H8.
      contradiction (H f1).
      split.
      constructor; constructor; now left.
      constructor; now left.
    }
    assert (f_f1 : f <> f1). {
      intros contra; subst.
      apply fundefs_append_unique_and in Huncurried_unique_fundefs.
      destruct Huncurried_unique_fundefs as [HL HR].
      inv HR. contradiction H5; constructor; now left.
    }
    assert (Hg_fv1 : ~ List.In g fv1). {
      intros contra.
      apply fundefs_append_unique_and in Huncurried_unique_fundefs.
      destruct Huncurried_unique_fundefs as [HL HR].
      inv HR.
      inv H6.
      contradiction (H g).
      split.
      constructor; constructor; now left.
      apply contra.
    }
    assert (Hf1_pre_fds : ~ name_in_fundefs pre_fds f1). {
      intros contra.
      apply fundefs_append_unique_l with (f := f1) in Huncurried_unique_fundefs; auto.
      contradiction Huncurried_unique_fundefs.
      right; now left.
    }
    assert (Hf_pre_fds : ~ name_in_fundefs pre_fds f). {
      intros contra.
      apply fundefs_append_unique_l with (f := f) in Hcurried_unique_fundefs; auto.
      contradiction Hcurried_unique_fundefs.
      now left.
    }
    assert (Hcurried_uncurried : name_in_fundefs curried \subset name_in_fundefs uncurried). {
      intros a Ha.
      rewrite fundefs_append_name_in_fundefs; [|reflexivity].
      split_var_in_fundefs a pre_fds Ha_pre_fds.
      now left.
      split_var_eq a f; subst.
      right; now left.
      split_var_in_fundefs a fds Ha_fds.
      right; right; now right.
      rewrite fundefs_append_name_in_fundefs in Ha; [|reflexivity].
      inv Ha; try contradiction.
      inv H; try contradiction.
      inv H0; contradiction.
    }
    assert (Hgv_g : ~ List.In g gv). {
      intros contra.
      apply fundefs_append_unique_and in Hcurried_unique_fundefs.
      destruct Hcurried_unique_fundefs as [HL HR].
      inv HR.
      inv H11.
      now inv H2.
    }
    assert (Hpre_fds_curried : name_in_fundefs pre_fds \subset name_in_fundefs curried). {
      subst curried; intros a Ha.
      rewrite fundefs_append_name_in_fundefs; [|reflexivity]; now left.
    }
    assert (Hpre_fds_uncurried : name_in_fundefs pre_fds \subset name_in_fundefs uncurried). {
      subst uncurried; intros a Ha.
      rewrite fundefs_append_name_in_fundefs; [|reflexivity]; now left.
    }
    assert (Hf1_ge : ~ In _ (occurs_free ge) f1). {
      intros contra1.
      rewrite Union_demorgan in Hf1_fresh; destruct Hf1_fresh as [Hf1_fresh2 Hf1_fresh3];
      rewrite Union_demorgan in Hf1_fresh2; destruct Hf1_fresh2 as [Hf1_fresh1 Hf1_fresh2].
      contradiction Hf1_fresh1.
      apply Hcurried_used; right; right.
      subst curried; apply occurs_free_fundefs_append; auto.
      constructor; auto.
      - apply fundefs_append_unique_and in Huncurried_unique_fundefs.
        destruct Huncurried_unique_fundefs as [HL HR].
        inv HR.
        inv H12.
        intros Hin.
        contradiction H18.
        apply Ensemble_In; rewrite FromList_app.
        now right.
      - apply fundefs_append_unique_and in Huncurried_unique_fundefs.
        destruct Huncurried_unique_fundefs as [HL HR].
        inv HR.
        inv H12.
        intros contra; contradiction H14; now apply name_in_fundefs_bound_var_fundefs.
      - apply Free_Efun2.
        constructor; auto; [|inversion 1].
        intros contra.
        apply fundefs_append_unique_and in Huncurried_unique_fundefs.
        destruct Huncurried_unique_fundefs as [HL HR].
        inv HR.
        inv H12.
        contradiction H18; apply Ensemble_In; rewrite FromList_app; now left.
    }
    assert (Hf1_curried : ~ In _ (name_in_fundefs curried) f1). {
      intros contra.
      rewrite Union_demorgan in Hf1_fresh; destruct Hf1_fresh as [Hf1_fresh2 Hf1_fresh3];
      rewrite Union_demorgan in Hf1_fresh2; destruct Hf1_fresh2 as [Hf1_fresh1 Hf1_fresh2].
      contradiction Hf1_fresh1.
      apply Hcurried_used; right; left.
      now apply name_in_fundefs_bound_var_fundefs.
    }
    assert (Hf_curried : In _ (name_in_fundefs curried) f). {
      rewrite fundefs_append_name_in_fundefs; [|reflexivity].
      right; now left.
    }
    assert (Hf_uncurried : In _ (name_in_fundefs uncurried) f) by now apply Hcurried_uncurried.

    split_var_in_fundefs
      h
      curried
      Hfds; clear Hfds; rename n into Hfds; simpl in Hfds.
    - (* h\in pre_fds ++ f |: fundefs(fds) *)
      rewrite def_funs_eq; auto.
      rewrite def_funs_eq; [|now apply Hcurried_uncurried].
      intros v1 Hv1; inv Hv1.
      eexists; split; [reflexivity|].
      generalize dependent h. generalize dependent e.
      induction k as [k IHk] using lt_wf_rec1.
      (* Opaque preord_exp. *)
      intros e Hcurried_used Huncurried_used Henv h Hh Hfds.
      split_var_eq h f; subst; rewrite preord_val_eq; simpl.
      + (* h = f *)
        rename curried into curried'; pose (curried := curried').
        rename uncurried into uncurried'; pose (uncurried := uncurried').
        subst curried'; subst uncurried'.
        do 2 (rewrite find_def_fundefs_append_neq; auto; simpl).
        destruct (M.elt_eq f f) as [Heq|]; [clear Heq|contradiction].
        intros vs1 vs2 k1 t xs1 e1 rho' Hlen_vs1_vs2 Hsome Hrho'; inv Hsome.
        assert (Hrho1' : length fv1 = length vs2). {
          apply set_lists_length in Hrho'.
          rewrite <- Hlen_vs1_vs2.
          rewrite <- Hrho'.
          simpl; rewrite Hfv_fv1.
          reflexivity.
        }
        eapply length_exists_set_lists in Hrho1'.
        destruct Hrho1' as [rho1' Hrho1'].
        do 3 eexists; split; [reflexivity|split]; [eassumption|intros Hk1 Hvs1_vs2].
        eapply preord_exp_fun_compat. now eapply Hpost_propG.
        now eapply Hpost_propG.
        apply preord_exp_refl. eassumption.
        (* wrt g, the environments
             rho'' = g + [fv -> vs1] + curried f + fds + rho
             rho1'' = uncurried g + [fv1 -> vs2] + uncurried f + f1 + fds + rho1
           agree. *)
        (* destruct vs1 as [|hvs1 tvs1]; [apply set_lists_length in Hrho'; inv Hrho'|]. *)
        (* destruct vs2 as [|hvs2 tvs2]; [apply set_lists_length in Hrho1'; inv Hrho1'|]. *)
        rename vs1 into tvs1, vs2 into tvs2.
        intros a Ha.
        inv Ha; rename a into g.
        unfold preord_var_env; simpl.
        do 2 rewrite M.gss.
        intros v1 Hv1; inv Hv1; eexists; split; [reflexivity|].
        rewrite preord_val_eq; simpl.
        destruct (M.elt_eq g g) as [Heq|]; [clear Heq|contradiction].
        intros vs3 vs4 k2 t0 xs0 e1 rho'' Hlen_vs3_vs4 Hsome Hrho''.
        inversion Hsome; subst t0; subst xs0; subst e1; clear Hsome.
        assert (Hrho1'' : length gv1 = length vs4). {
          apply set_lists_length in Hrho''.
          rewrite <- Hlen_vs3_vs4.
          rewrite <- Hrho''.
          assumption.
        }
        eapply length_exists_set_lists in Hrho1''; destruct Hrho1'' as [rho1'' Hrho1''].
        do 3 eexists; split; [reflexivity|split]; [eassumption|intros Hk2 Hvs3_vs4].
        rename xs1 into fv.
        assert (Hrho''' : length (gv ++ fv) = length (vs4 ++ tvs2)). {
          do 2 rewrite length_app.
          apply set_lists_length in Hrho1''.
          rewrite <- Hrho1''.
          rewrite <- Hgv_gv1.
          apply set_lists_length in Hrho1'.
          inv Hrho1'.
          rewrite <- Hfv_fv1.
          reflexivity.
        }
        (* Transparent preord_exp. *) intros v1 c1 cout Hc1 Hv1.
        apply @length_exists_set_lists with
          (rho := (def_funs uncurried uncurried rho1 rho1)) in Hrho'''.
        destruct Hrho''' as [rho''' Hrho'''].
        assert (Hgoal : preord_exp cenv Post PostG k2 (ge, rho'') (ge, rho''')). {
          apply preord_exp_refl. eassumption.
          (* wrt free variables of ge, the environments
               rho'' = [gv -> vs3] + g + [k0 :: fv -> vs1] + curried f + fds + rho
               rho''' = [gv ++ fv -> vs4 ++ tvs2] + uncurried f + f1 + fds + rho1
             agree.
           *)

          (* rho''g := rho'' \ g *)
          eapply set_lists_set_permut in Hgv_g; [|apply Hrho''].
          destruct Hgv_g as [rho''g [Hrho''g Hrho''_rho''g]].
          eapply preord_env_P_subst; [|intros a Ha;symmetry; apply Hrho''_rho''g|reflexivity].
          apply preord_env_P_set_not_in_P_l;
            [|apply Disjoint_Union_r with (s1 := bound_var ge);
              replace (bound_var ge :|: occurs_free ge) with (used_vars ge) by reflexivity;
              now rewrite <- occurs_in_exp_correct].

          (* split [gv ++ fv -> vs4 ++ tvs2] into [gv -> vs4] + [fv -> tvs2] *)
          symmetry in Hrho'''; eapply set_lists_app in Hrho''';
            [|apply set_lists_length in Hrho1''; now rewrite <- Hrho1''].
          destruct Hrho''' as [rho'''fv [Hrho'''fv Hrho''']].

          (* [[gv]](rho''g) ==_k2 [[gv]](rho''') *)
          eapply preord_env_P_set_lists_extend; eauto.

          (* rho'k0 := rho' *)
          (* eapply set_set_lists in Hrho'; destruct Hrho' as [rho'k0 [Hrho' Hrho'k0]]; subst rho'. *)
          rename rho' into rho'k0, Hrho' into Hrho'k0.

          (*
          apply preord_env_P_set_not_in_P_l;
            [|eapply Disjoint_Included_l;
                [|rewrite <- occurs_in_exp_correct];
                [|apply Hk0_nonrec];
              apply Setminus_Included_preserv;
              eapply Included_Union_r].*)

          (* [[fv]](rho'k0) ==_k2 [[gv]](rho''') *)
          (* inv Hvs1_vs2. *)
          eapply preord_env_P_set_lists_extend; eauto;
            [|eapply Forall2_preord_val_monotonic];
            [| |eassumption];
            [|lia].

          intros a Ha.
          (* remove pre_fds from (pre_fds + curried f + fds + rho),
                                 (pre_fds + f + f1 + fds + rho1) *)
          split_var_in_fundefs a pre_fds Hpre_fds. {
            unfold preord_var_env.
            rewrite def_funs_eq; [|now apply Hpre_fds_curried].
            rewrite def_funs_eq; [|now apply Hpre_fds_uncurried].
            intros v0 Hv0; inv Hv0; eexists; split; [reflexivity|].
            eapply preord_val_monotonic; [apply IHk with (m := k1) (e := Ehalt a)|];
              [lia| | | |constructor| |lia].
            * rewrite Union_Same_set; [assumption|].
              unfold used_vars.
              rewrite bound_var_Ehalt.
              rewrite Union_Empty_set_neut_l.
              intros a' Ha'; inv Ha'; left.
              rewrite fundefs_append_bound_vars; [|reflexivity]; left.
              now apply name_in_fundefs_bound_var_fundefs.
            * unfold used_vars.
              rewrite bound_var_Ehalt.
              rewrite Union_Empty_set_neut_l.
              rewrite Union_Same_set; [eapply Union_Included_r; eassumption|].
              intros a' Ha'; inv Ha'; left.
              rewrite fundefs_append_bound_vars; [|reflexivity]; left.
              now apply name_in_fundefs_bound_var_fundefs.
            * eapply preord_env_P_antimon.
              eapply preord_env_P_monotonic; [|eassumption]; lia.
              intros a' Ha'; inv Ha'.
              inv H3; contradiction H1.
              apply Ensemble_In.
              rewrite fundefs_append_name_in_fundefs; [|reflexivity]; now left.
              now apply Free_Efun2.
            * apply Ensemble_In.
              rewrite fundefs_append_name_in_fundefs; [|reflexivity]; now left.
          }
          rename uncurried into uncurried'; pose (uncurried := uncurried'); subst uncurried'.
          apply preord_var_env_def_funs_neq; auto.

          (* remove curried f, uncurried f *)
          simpl; apply preord_var_env_extend'. intros Ha_f.

          (* remove f1 *)
          apply preord_var_env_extend_neq_r.

          (* remove fds *) {
          rename Hfds into Hname_fds.
          split_var_in_fundefs a fds Hfds.
          - unfold preord_var_env.
            do 2 (rewrite def_funs_eq; [|assumption]).
            intros v0 Hv0; inv Hv0; eexists; split; [reflexivity|].
            eapply preord_val_monotonic; [apply IHk with (m := k1) (e := Ehalt a)|];
              [lia| | | |constructor| |lia].
            * rewrite Union_Same_set; [assumption|].
              unfold used_vars.
              rewrite bound_var_Ehalt.
              rewrite Union_Empty_set_neut_l.
              intros a' Ha'; inv Ha'; left.
              rewrite fundefs_append_bound_vars; [|reflexivity].
              right; apply Bound_Fcons2.
              now apply name_in_fundefs_bound_var_fundefs.
            * unfold used_vars.
              rewrite bound_var_Ehalt.
              rewrite Union_Empty_set_neut_l.
              rewrite Union_Same_set; [eapply Union_Included_r; eassumption|].
              intros a' Ha'; inv Ha'; left.
              rewrite fundefs_append_bound_vars; [|reflexivity].
              right; do 2 apply Bound_Fcons2.
              now apply name_in_fundefs_bound_var_fundefs.
            * eapply preord_env_P_antimon.
              eapply preord_env_P_monotonic; [|eassumption]; lia.
              intros a' Ha'; inv Ha'.
              inv H3; contradiction H1.
              apply Ensemble_In; rewrite fundefs_append_name_in_fundefs; [|reflexivity].
              right; now right.
              now apply Free_Efun2.
            * apply Ensemble_In; rewrite fundefs_append_name_in_fundefs; [|reflexivity].
              right; now right.
          - unfold preord_var_env.
            do 2 (rewrite def_funs_neq; auto).
            assert ((occurs_free ge
                                 \\ FromList gv
                                 \\ FromList fv
                                 \\ [set f]
                                 \\ name_in_fundefs pre_fds
                                 \\ name_in_fundefs fds) a). {
              do 3 (split; auto).
              intros contra; now inv contra.
            }
            clear Ha; clear n; clear Ha_f; clear n0; generalize dependent a.
            eapply preord_env_P_antimon.
            eapply preord_env_P_monotonic; [|apply Henv]; lia.
            intros a Ha; inv Ha; inv H; inv H1; inv H.
            apply Free_Efun2.
            apply occurs_free_fundefs_append; auto.
            apply Free_Fcons1;
              [intros contra; subst; now contradiction H3| |assumption|].
            * assumption.
            * inv H1.
              apply Free_Efun2; apply Free_Fcons1; [|assumption|inversion 1|assumption].
              intros contra; subst.
              rewrite occurs_in_exp_correct in Hg_nonrec.
              rewrite Disjoint_Singleton_In in Hg_nonrec; auto with Decidable_DB.
              contradiction Hg_nonrec; now right.
          }

          (* f1 not in (occurs_free ge) *) {
            intros contra; subst; inv Ha; inv H.
            contradiction.
          }

          (* [[curried f]](f + fds + rho) ==_k2 [[uncurried f]](f + f1 + fds + rho1) *) {
            eapply preord_val_monotonic; [eapply IHk with (m := k1); eauto|]; try lia.
            eapply preord_env_P_monotonic; [|eassumption]; lia.
          }
        }
        unfold preord_exp' in Hgoal.
        specialize Hgoal with (v1 := v1) (cin := c1) (cout := cout); destruct Hgoal; [apply Hc1|apply Hv1|].
        rename x into v2; destruct H as [c2 [cout' [Hv2 [Hvpost Hv1_v2]]]].
        eexists; exists (plus c2 (one (Eapp f1 ft1 (gv1 ++ fv1) : exp))),
                 (plus cout' (one (Eapp f1 ft1 (gv1 ++ fv1) : exp))); split; [|split; [|eassumption]].
        2: { eapply Hpost_curry. eassumption. }
        apply BStepf_run.
        eapply BStept_app; eauto.
        { erewrite <- set_lists_not_In; [|symmetry; eassumption|assumption].
          rewrite M.gso; [|auto].
          erewrite <- set_lists_not_In; [|symmetry; eassumption|assumption].
          rewrite def_funs_get_neq; auto.
          simpl; rewrite M.gso; auto.
          now rewrite M.gss. }
        { apply get_list_app.
          eapply get_list_set_lists; [now inv Hgv1_fresh|symmetry; eassumption].
          erewrite get_list_set_lists_Disjoint;
            [|inv Hfv1_fresh; apply Disjoint_Union_r in H; apply H|symmetry; eassumption].
          rewrite get_list_set_neq; [|assumption].
          rename rho1' into rho1'k0, Hrho1' into Hrho1'k0.
          eapply get_list_set_lists; [now inv Hfv1_fresh|symmetry; eassumption]. }
        { rename uncurried into uncurried'; pose (uncurried := uncurried'); subst uncurried'.
          rewrite find_def_fundefs_append_neq; auto.
          simpl; destruct (M.elt_eq f1 f) as [|Heq]; [now subst|clear Heq].
          destruct (M.elt_eq f1 f1) as [Heq|]; [clear Heq|contradiction].
          reflexivity. }
      + (* h \in pre_fds ++ fds *)
        assert (Hf' : h <> f). {
          intros contra; subst; inv Hcurried_unique_fundefs.
          now apply name_in_fundefs_bound_var_fundefs in Hfds.
          contradiction. }
        assert (Hf1: h <> f1). {
          (* f1 is not in curried (freshly generated by uncurrier) *)
          intros contra; subst; contradiction. }
        destruct (M.elt_eq h f) as [|Heq]; [contradiction|clear Heq].
        destruct (M.elt_eq h f1) as [|Heq]; [contradiction|clear Heq].
        intros vs1 vs2 k1 t xs1 e1 rho' Hlen_vs1_vs2 Hfind_def Hrho'.
        assert (Hrho1' : length xs1 = length vs2). {
          apply set_lists_length in Hrho'.
          now rewrite <- Hlen_vs1_vs2. }
        eapply length_exists_set_lists in Hrho1'; destruct Hrho1' as [rho1' Hrho1'].
        exists xs1, e1; eexists; split; [|split]; [|eassumption|intros Hk1 Hvs1_vs2].
        (* only f is uncurried, so h in uncurried = h in curried (Hfind_def) *)
        assert (HLR : In _ (name_in_fundefs curried) h) by auto.
        rewrite fundefs_append_name_in_fundefs in HLR; [|reflexivity].
        split_var_in_fundefs h pre_fds Hh_pre_fds.
        subst curried; subst uncurried.
        rewrite find_def_fundefs_append_eq; auto.
        rewrite find_def_fundefs_append_eq in Hfind_def; auto.
        inv HLR; [contradiction|]; inv H; [inv H0; contradiction|].
        subst curried; subst uncurried.
        rewrite find_def_fundefs_append_neq; auto.
        rewrite find_def_fundefs_append_neq in Hfind_def; auto.
        simpl; simpl in Hfind_def.
        destruct (M.elt_eq h f); try contradiction.
        destruct (M.elt_eq h f1); try contradiction; auto.
        apply preord_exp_refl. eassumption.

        (* wrt free variables of e1, the environments
             rho' = [xs1 -> vs1] + f + fds + rho
             rho1' = [xs1 -> vs2] + f + f1 + fds + rho1
           agree.
         *)

        (* [[xs1]](rho') ==_k1 [[xs1]](rho1') *)
        eapply preord_env_P_set_lists_extend; eauto.

        (* remove pre_fds *)
        intros a Ha.
        split_var_in_fundefs a pre_fds Hpre_fds. {
          unfold preord_var_env.
          rewrite def_funs_eq; [|now apply Hpre_fds_curried].
          rewrite def_funs_eq; [|now apply Hpre_fds_uncurried].
          intros v0 Hv0; inv Hv0; eexists; split; [reflexivity|].
          eapply preord_val_monotonic;
          [apply IHk with (m := k - 1) (e := Ehalt a)|]; [lia| | | |constructor| |lia].
          * rewrite Union_Same_set; [assumption|].
            unfold used_vars.
            rewrite bound_var_Ehalt.
            rewrite Union_Empty_set_neut_l.
            intros a' Ha'; inv Ha'; left.
            rewrite fundefs_append_bound_vars; [|reflexivity]; left.
            now apply name_in_fundefs_bound_var_fundefs.
          * unfold used_vars.
            rewrite bound_var_Ehalt.
            rewrite Union_Empty_set_neut_l.
            rewrite Union_Same_set; [eapply Union_Included_r; eassumption|].
            intros a' Ha'; inv Ha'; left.
            rewrite fundefs_append_bound_vars; [|reflexivity]; left.
            now apply name_in_fundefs_bound_var_fundefs.
          * eapply preord_env_P_antimon.
            eapply preord_env_P_monotonic; [|eassumption]; lia.
            intros a' Ha'; inv Ha'.
            inv H3; contradiction H1.
            apply Ensemble_In.
            rewrite fundefs_append_name_in_fundefs; [|reflexivity]; now left.
            now apply Free_Efun2.
          * apply Ensemble_In.
            rewrite fundefs_append_name_in_fundefs; [|reflexivity]; now left.
        }
        rename uncurried into uncurried'; pose (uncurried := uncurried'); subst uncurried'.
        apply preord_var_env_def_funs_neq; auto.

        (* remove f and f1 *)
        simpl; apply preord_var_env_extend'. intros Ha_f.
        apply preord_var_env_extend_neq_r.

        (* remove fds *) {
          split_var_in_fundefs a fds Hfds'; unfold preord_var_env; simpl.
          - do 2 (rewrite def_funs_eq; [|assumption]).
            intros v1 Hv1; inv Hv1; eexists; split; [reflexivity|].
            (* todo: basically a duplicate with the previous application of IH *)
            eapply preord_val_monotonic;
            [apply IHk with (m := k - 1) (e := Ehalt a)|]; [lia| | | |constructor| |lia].
            + rewrite Union_Same_set; [assumption|].
              unfold used_vars.
              rewrite bound_var_Ehalt.
              rewrite Union_Empty_set_neut_l.
              intros a' Ha'; inv Ha'; left.
              rewrite fundefs_append_bound_vars; [|reflexivity].
              right; apply Bound_Fcons2.
              now apply name_in_fundefs_bound_var_fundefs.
            + unfold used_vars.
              rewrite bound_var_Ehalt.
              rewrite Union_Empty_set_neut_l.
              rewrite Union_Same_set; [eapply Union_Included_r; eassumption|].
              intros a' Ha'; inv Ha'; left.
              rewrite fundefs_append_bound_vars; [|reflexivity].
              right; do 2 apply Bound_Fcons2.
              now apply name_in_fundefs_bound_var_fundefs.
            + eapply preord_env_P_antimon.
              eapply preord_env_P_monotonic; [|eassumption]; lia.
              intros a' Ha'; inv Ha'.
              inv H3; contradiction H1.
              apply Ensemble_In; rewrite fundefs_append_name_in_fundefs; [|reflexivity].
              right; now right.
              now apply Free_Efun2.
            + apply Ensemble_In; rewrite fundefs_append_name_in_fundefs; [|reflexivity].
              right; now right.
          - unfold preord_var_env.
            do 2 (rewrite def_funs_neq; auto).
            assert ((occurs_free e1
                                 \\ FromList xs1
                                 \\ [set f]
                                 \\ name_in_fundefs pre_fds
                                 \\ name_in_fundefs fds) a). {
              do 3 (split; auto).
              intros contra; now inv contra.
            }
            clear Ha; clear n1; clear Ha_f; clear n0; generalize dependent a.
            eapply preord_env_P_antimon.
            eapply preord_env_P_monotonic; [|eassumption]; lia.
            intros a Ha; inv Ha; inv H; inv H1; inv H.
            apply Free_Efun2.
            subst curried.
            split_var_in_fundefs h pre_fds Hh_pre_fds.
            + apply occurs_free_fundefs_append_l.
              intros contra; inv contra; auto.
              eapply find_def_is_Some_occurs_free_fundefs; eauto.
              rewrite <- find_def_fundefs_append_neq_l
                with (B1 := Fcons f ft fv
                                 (Efun (Fcons g gt gv ge Fnil) (Ehalt g)) fds); auto.
              apply Hfind_def.
              intros contra; inv contra.
              apply fundefs_append_unique with (f := h) in Huncurried_unique_fundefs.
              contradiction.
              now inv H.
              apply fundefs_append_unique with (f := h) in Huncurried_unique_fundefs.
              contradiction.
              right; now right.
            + apply occurs_free_fundefs_append; auto.
              apply Free_Fcons2; [|intros contra; subst; now contradiction H3].
              eapply find_def_is_Some_occurs_free_fundefs; eauto.
              rewrite <- find_def_fundefs_append_neq
                with (B := Fcons f ft fv
                                 (Efun (Fcons g gt gv ge Fnil) (Ehalt g)) Fnil); auto.
              rewrite <- find_def_fundefs_append_neq with (B := pre_fds); auto.
              apply Hfind_def.
              auto.
              intros contra; inv contra; now inv H.
        }

        (* f1 never occurs in the definition of h *)
        {
          intros contra; subst.
          rewrite Union_demorgan in Hf1_fresh; destruct Hf1_fresh as [Hf1_fresh2 Hf1_fresh3].
          rewrite Union_demorgan in Hf1_fresh2; destruct Hf1_fresh2 as [Hf1_fresh1 Hf1_fresh2].
          contradiction Hf1_fresh1.
          apply Hcurried_used_fundefs.
          right.
          eapply find_def_is_Some_occurs_free_fundefs; eauto; now inv Ha.
        }

        (* [[curried f]](rho') ==_k1 [[uncurried f]](rho1') *)
        eapply preord_val_monotonic;
        [apply IHk with (m := k - 1) (e := Ehalt f)|lia]; [lia| | | |constructor|assumption].
        (* todo: basically a duplicate with the previous application of IH,
           but with left instaed of right soemtimes *)
        * rewrite Union_Same_set; [assumption|].
          unfold used_vars.
          rewrite bound_var_Ehalt.
          rewrite Union_Empty_set_neut_l.
          intros b Hb; inv Hb.
          left; now apply name_in_fundefs_bound_var_fundefs.
        * unfold used_vars.
          rewrite bound_var_Ehalt.
          rewrite Union_Empty_set_neut_l.
          rewrite Union_Same_set; [eapply Union_Included_r; eassumption|].
          rewrite occurs_free_Ehalt.
          intros b Hb; inv Hb.
          left; now apply name_in_fundefs_bound_var_fundefs.
        * eapply preord_env_P_antimon.
          eapply preord_env_P_monotonic; [|eassumption]; lia.
          repeat normalize_occurs_free.
          intros b Hb; inv Hb.
          now left.
          inv H.
          contradiction H1.
          now inv H0.
    - (* h\not\in pre_fds ++ f |: fundefs(fds) *)
      assert (h <> f). {
        intros contra; subst.
        contradiction Hfds.
      }
      assert (h <> f1). {
        intros contra; subst.
        rewrite Union_demorgan in Hf1_fresh; destruct Hf1_fresh as [Hf1_fresh2 Hf1_fresh3].
        rewrite Union_demorgan in Hf1_fresh2; destruct Hf1_fresh2 as [Hf1_fresh1 Hf1_fresh2].
        contradiction Hf1_fresh1.
        apply Hcurried_used.
        now left; right.
      }
      simpl.
      rename curried into curried'; pose (curried := curried'); subst curried'.
      rename uncurried into uncurried'; pose (uncurried := uncurried'); subst uncurried'.
      assert (~ name_in_fundefs fds h). {
        intros contra; contradiction Hfds.
        apply Ensemble_In; rewrite fundefs_append_name_in_fundefs; [|reflexivity].
        right; now right.
      }
      assert (~ name_in_fundefs pre_fds h). {
        intros contra; contradiction Hfds.
        apply Ensemble_In; rewrite fundefs_append_name_in_fundefs; [|reflexivity].
        now left.
      }
      do 2 (rewrite def_funs_get_neq; auto).
      simpl; do 3 (rewrite M.gso; auto).
      do 2 (rewrite def_funs_neq; [|assumption]).
      unfold preord_env_P, preord_var_env in Henv.
      intros v1 Hv1.
      edestruct Henv as [v2 [Hv2 Hv12]]; try eassumption.
      + constructor; [simpl|assumption]; auto.
      + eexists; split; eapply preord_val_monotonic in Hv12; eauto; lia.
  Qed.

  Lemma uncurry_step_preserves_ctag : forall x s m s1 m1 arms arms1,
    uncurry_step (Ecase x arms) s m (Ecase x arms1) s1 m1 ->
    Forall2 (fun p p' : ctor_tag * exp => fst p = fst p') arms arms1.
  Proof.
    induction arms; intros.
    - destruct arms1; inv H.
    - destruct arms1; inv H; (constructor; [easy|]); auto.
      now apply List_util.Forall2_refl.
  Qed.

  Lemma uncurry_step_s_nondecreasing_mut :
    let P := (fun e s m e1 s1 m1 => s \subset s1) in
    let Q := (fun f s m f1 s1 m1 => s \subset s1) in
    (forall e s m e1 s1 m1, uncurry_step e s m e1 s1 m1 -> P e s m e1 s1 m1) /\
    (forall f s m f1 s1 m1, uncurry_fundefs_step f s m f1 s1 m1 -> Q f s m f1 s1 m1).
  Proof with auto with Ensembles_DB.
    intros P Q.
    uncurry_induction_mut P Q IHstep IH;
      subst P; subst Q; simpl in *...
    rewrite H7...
    rewrite H6...
  Qed.

  Corollary uncurry_step_s_nondecreasing : forall e s m e1 s1 m1,
    uncurry_step e s m e1 s1 m1 -> s \subset s1.
  Proof. apply uncurry_step_s_nondecreasing_mut. Qed.

  Corollary uncurry_fundefs_step_s_nondecreasing : forall e s m e1 s1 m1,
    uncurry_fundefs_step e s m e1 s1 m1 -> s \subset s1.
  Proof. apply uncurry_step_s_nondecreasing_mut. Qed.

  Lemma Union_Included_lr : forall {A} (S1 S2 S3 : _ A),
    S1 :|: S2 \subset S3 -> S1 \subset S3 /\ S2 \subset S3.
  Proof. intros; split; [eapply Union_Included_l|eapply Union_Included_r]; eauto. Qed.

  Local Ltac destruct_Union_Included :=
    repeat match goal with
      [ H : _ :|: _ \subset _ |- _ ] => apply Union_Included_lr in H; destruct H
    end.

  Local Ltac inv_all :=
    repeat match goal with
    | [ H : Ensembles.In var _ _ |- _ ] => inv H
    | [ H : List.In _ _ |- _ ] => inv H
    | [ H : (_, _) = (_, _) |- _ ] => inv H
    end;
    eauto with Ensembles_DB.

  Lemma uncurry_step_preserves_used_vars_mut :
    let P := (fun e s m e1 s1 m1 => used_vars e \subset s -> used_vars e1 \subset s1) in
    let Q := (fun f s m f1 s1 m1 =>
                used_vars_fundefs f \subset s ->
                used_vars_fundefs f1 \subset s1) in
    (forall e s m e1 s1 m1, uncurry_step e s m e1 s1 m1 -> P e s m e1 s1 m1) /\
    (forall f s m f1 s1 m1, uncurry_fundefs_step f s m f1 s1 m1 -> Q f s m f1 s1 m1).
  Proof with eauto with Ensembles_DB.
    intros P Q.
    uncurry_induction_mut P Q IHstep IH; subst P; subst Q; simpl in *; intros He;
    try destruct arm;
    try solve [
      (apply uncurry_step_s_nondecreasing in IHstep
         || apply uncurry_fundefs_step_s_nondecreasing in IHstep);
      repeat normalize_used_vars;
      destruct_Union_Included;
      try solve [eapply Included_trans; [|eauto]; eauto with Ensembles_DB];
      apply Union_Included; eauto with Ensembles_DB;
      eapply Included_trans; [|eauto]; eauto with Ensembles_DB].
    - (* Eletapp *)
      apply uncurry_step_s_nondecreasing in IHstep.
      rewrite used_vars_Eletapp in *.
      destruct_Union_Included.
      apply Union_Included...
      apply Union_Included...
      apply Union_Included...
      eapply Included_trans...
    - (* Eproj *)
      apply uncurry_step_s_nondecreasing in IHstep.
      rewrite used_vars_Eproj in *.
      destruct_Union_Included.
      apply Union_Included; [|apply Union_Included]...
    - (* Eprim_val *)
      apply uncurry_step_s_nondecreasing in IHstep.
      rewrite used_vars_Eprim_val in *.
      destruct_Union_Included.
      apply Union_Included...
    - (* Fcons e *)
      apply uncurry_step_s_nondecreasing in IHstep.
      rewrite used_vars_Fcons in *.
      destruct_Union_Included.
      apply Union_Included; [apply Union_Included|]...
      all: eapply Included_trans; [|eassumption]...
    - (* Fcons curried *)
      rewrite H7.
      repeat (rewrite used_vars_Fcons in * + rewrite used_vars_Efun in *).
      destruct_Union_Included.
      repeat rewrite Union_assoc.
      repeat rewrite used_vars_Eapp.
      apply Union_Included. apply Union_Included. apply Union_Included. apply Union_Included.
      apply Union_Included. apply Union_Included. apply Union_Included. apply Union_Included.
      apply Union_Included. apply Union_Included.
      all: eauto with Ensembles_DB.
      + intros a Ha; inv Ha. (* admit: this sort of stuff should be automated away *)
        do 3 left; apply H15; now left.
        left; now right.
      + intros a Ha; inv_all.
        rewrite FromList_app in H16; inv H16; eauto.
      + intros a Ha; inv_all.
        do 3 left; apply H11; rewrite used_vars_Eapp; auto.
        contradiction.
      + rewrite FromList_app.
        rewrite FromList_cons in H15.
        intros a Ha; inv Ha; do 3 left; eauto.
    - (* anf *)
      repeat normalize_used_vars; repeat normalize_sets.
      rewrite H6.
      repeat match goal with |- _ :|: _ \subset _ => apply Union_Included end...
      all: repeat apply Included_Union_preserv_l; eapply Included_trans; [|eassumption]...
  Qed.

  Lemma uncurry_step_preserves_disjoint_mut :
    let P := (fun e s m e1 s1 m1 => used_vars e \subset s -> used_vars e1 \subset s1) in
    let Q := (fun f s m f1 s1 m1 =>
                used_vars_fundefs f \subset s ->
                used_vars_fundefs f1 \subset s1) in
    (forall e s m e1 s1 m1, uncurry_step e s m e1 s1 m1 -> P e s m e1 s1 m1) /\
    (forall f s m f1 s1 m1, uncurry_fundefs_step f s m f1 s1 m1 -> Q f s m f1 s1 m1).
  Proof with eauto with Ensembles_DB.
    intros P Q.
    uncurry_induction_mut P Q IHstep IH; subst P; subst Q; simpl in *; intros He;
    try destruct arm;
    try solve [
      (apply uncurry_step_s_nondecreasing in IHstep
         || apply uncurry_fundefs_step_s_nondecreasing in IHstep);
      repeat normalize_used_vars;
      destruct_Union_Included;
      try solve [eapply Included_trans; [|eauto]; eauto with Ensembles_DB];
      apply Union_Included; eauto with Ensembles_DB;
      eapply Included_trans; [|eauto]; eauto with Ensembles_DB].
    - (* Eletapp *)
      apply uncurry_step_s_nondecreasing in IHstep.
      rewrite used_vars_Eletapp in *.
      destruct_Union_Included.
      apply Union_Included...
      apply Union_Included...
      apply Union_Included...
      eapply Included_trans...
    - (* Eproj *)
      apply uncurry_step_s_nondecreasing in IHstep.
      rewrite used_vars_Eproj in *.
      destruct_Union_Included.
      apply Union_Included; [|apply Union_Included]...
    - (* Eprim_val *)
      apply uncurry_step_s_nondecreasing in IHstep.
      rewrite used_vars_Eprim_val in *.
      destruct_Union_Included.
      apply Union_Included...
    - (* Fcons e *)
      apply uncurry_step_s_nondecreasing in IHstep.
      rewrite used_vars_Fcons in *.
      destruct_Union_Included.
      apply Union_Included; [apply Union_Included|]...
      all: eapply Included_trans; [|eassumption]...
    - (* Fcons curried *)
      rewrite H7.
      repeat (rewrite used_vars_Fcons in * + rewrite used_vars_Efun in *).
      destruct_Union_Included.
      repeat rewrite Union_assoc.
      repeat rewrite used_vars_Eapp.
      apply Union_Included. apply Union_Included. apply Union_Included. apply Union_Included.
      apply Union_Included. apply Union_Included. apply Union_Included. apply Union_Included.
      apply Union_Included. apply Union_Included.
      all: eauto with Ensembles_DB.
      + intros a Ha; inv Ha. (* admit: this sort of stuff should be automated away *)
        do 3 left; apply H15; now left.
        left; now right.
      + intros a Ha; inv_all.
        rewrite FromList_app in H16; inv H16; eauto.
      + intros a Ha; inv_all.
        do 3 left; apply H11; rewrite used_vars_Eapp; auto.
        contradiction.
      + rewrite FromList_app.
        rewrite FromList_cons in H15.
        intros a Ha; inv Ha; do 3 left; eauto.
    - (* anf *)
      repeat normalize_used_vars; repeat normalize_sets.
      rewrite H6.
      repeat match goal with |- _ :|: _ \subset _ => apply Union_Included end...
      all: repeat apply Included_Union_preserv_l; eapply Included_trans; [|eassumption]...
  Qed.

  Corollary uncurry_step_preserves_used_vars : forall e s m e1 s1 m1,
      uncurry_step e s m e1 s1 m1 ->
      used_vars e \subset s ->
      used_vars e1 \subset s1.
  Proof. apply uncurry_step_preserves_used_vars_mut. Qed.

  Corollary uncurry_fundefs_step_preserves_used_vars : forall e s m e1 s1 m1,
    uncurry_fundefs_step e s m e1 s1 m1 ->
    used_vars_fundefs e \subset s ->
    used_vars_fundefs e1 \subset s1.
  Proof. apply uncurry_step_preserves_used_vars_mut. Qed.

  Ltac destruct_Union_Intersection :=
    repeat match goal with
      [ H : In _ (_ :&: _) _ |- _ ] => destruct H
    | [ H : In _ (_ :|: _) _ |- _ ] => destruct H
    end.

  Lemma Intersection_Union_distr : forall {A} (S1 S2 S3 : _ A),
    (S1 :|: S2) :&: S3 <--> (S1 :&: S3) :|: (S2 :&: S3).
  Proof.
    split; intros a Ha; destruct_Union_Intersection; auto with Ensembles_DB.
  Qed.

  Lemma uncurry_step_maintains_bindings_mut :
    let P := (fun e s m e1 s1 m1 =>
                used_vars e \subset s -> bound_var e1 :&: s <--> bound_var e) in
    let Q := (fun f s m f1 s1 m1 =>
                used_vars_fundefs f \subset s ->
                bound_var_fundefs f1 :&: s <--> bound_var_fundefs f) in
    (forall e s m e1 s1 m1, uncurry_step e s m e1 s1 m1 -> P e s m e1 s1 m1) /\
    (forall f s m f1 s1 m1, uncurry_fundefs_step f s m f1 s1 m1 -> Q f s m f1 s1 m1).
  Proof with eauto with Ensembles_DB.
    intros P Q.
    uncurry_induction_mut P Q IHstep IH; subst P; subst Q; simpl in *; intros;
    try destruct arm;
    try (
      repeat normalize_bound_var; repeat normalize_used_vars;
      rewrite Intersection_Union_distr;
      rewrite IH; [rewrite Intersection_Same_set; [reflexivity| ] |];
      eapply Included_trans; [|eauto| |eauto]; eauto with Ensembles_DB).
    - (* Eletapp *)
      rewrite used_vars_Eletapp in *.
      eauto with Ensembles_DB.
    - (* Fcons fds *)
      repeat rewrite bound_var_fundefs_Fcons.
      repeat rewrite Intersection_Union_distr.
      rewrite IH.
      repeat rewrite Intersection_Same_set.
      reflexivity.
      all: rewrite used_vars_Fcons in H.
      eapply Included_trans; [|eassumption]...
      eapply Union_Included_r.
      do 2 eapply Union_Included_l...
      do 3 eapply Union_Included_l...
      eapply Included_trans; [|eassumption]...
    - (* Fcons e *)
      repeat rewrite bound_var_fundefs_Fcons.
      repeat rewrite Intersection_Union_distr.
      rewrite IH.
      repeat rewrite Intersection_Same_set.
      reflexivity.
      all: rewrite used_vars_Fcons in H.
      eapply Included_trans; [|eassumption]...
      eapply Union_Included_r.
      do 2 eapply Union_Included_l...
      do 3 eapply Union_Included_l...
      eapply Included_trans; [|eassumption]...
    - (* Fcons curried *)
      assert (Hsubst :
              bound_var_fundefs
                (Fcons f9 ft (k :: fv1)
                       (Efun (Fcons g gt gv1
                                    (Eapp f10 ft1 (gv1 ++ fv1))
                                    Fnil)
                             (Eapp k kt [g]))
                       (Fcons f10 ft1 (gv ++ fv) ge fds)) <-->
             bound_var_fundefs
                (Fcons f9 ft (k :: fv) (Efun (Fcons g gt gv ge Fnil) (Eapp k kt [g])) fds)
                :|: FromList (f10 :: fv1 ++ gv1)). {
        repeat (rewrite bound_var_fundefs_Fcons + rewrite bound_var_Efun).
        repeat rewrite bound_var_Eapp.
        repeat rewrite FromList_cons.
        repeat rewrite FromList_app.
        split; intros a Ha; destruct_Union_Intersection; auto 10 with Ensembles_DB.
      }
      assert (Hsubst1 : FromList (f10 :: fv1 ++ gv1) :&: s <--> Empty_set _). {
        rewrite FromList_cons.
        rewrite FromList_app.
        split; intros a Ha; [|inv Ha].
        repeat rewrite Union_demorgan in H6.
        unfold fresh_copies in *.
        repeat match goal with
          [ H : _ /\ _ |- _ ] => destruct H
        | [ H : _ \/ _ |- _ ] => destruct H
        end.
        destruct_Union_Intersection; inv_all.
        contradiction.
        inv H4. contradiction (H15 x); auto.
        inv H2. contradiction (H15 x); auto.
      }
      rewrite Hsubst.
      rewrite Intersection_Union_distr.
      rewrite Hsubst1.
      rewrite Intersection_Same_set.
      now rewrite Union_Empty_set_neut_r.
      eapply Union_Included_l; eauto.
    - (* anf *)
      repeat normalize_used_vars.
      repeat normalize_bound_var.
      repeat rewrite Intersection_Union_distr.
      normalize_sets.
      rewrite Ensemble_iff_In_iff; intros arbitrary.
      assert (Hgv1 : FromList gv1 :&: s <--> Empty_set _). {
        split; [intros x' [x Hx]; clear x' |inversion 1].
        destruct H1 as [[Hfresh] Hdup].
        contradiction (Hfresh x); now split. }
      assert (Hfv1 : FromList fv1 :&: s <--> Empty_set _). {
        split; [intros x' [x Hx]; clear x' |inversion 1].
        destruct H3 as [[Hfresh] Hdup].
        contradiction (Hfresh x); split; [now left|auto]. }
      assert (Hf11 : f11 &: s <--> Empty_set _). {
        split; [intros x' [x Hx]; clear x'; inv Hx |inversion 1].
        contradiction H5; now (left; left). }
      rewrite Hgv1, Hfv1, Hf11.
      repeat rewrite In_or_Iff_Union.
      repeat rewrite Intersection_Empty_set_abs_l.
      repeat rewrite In_Empty_set.
      assert (False_neut_r : forall A, A \/ False <-> A) by tauto.
      assert (False_neut_l : forall A, False \/ A <-> A) by tauto.
      repeat (rewrite False_neut_l || rewrite False_neut_r).
      assert (Intersection_and_iff : forall S1 S2 x, In var (S1 :&: S2) x <-> In _ S1 x /\ In _ S2 x). {
        intros x; split; destruct 1; split; auto. }
      repeat rewrite Intersection_and_iff; rewrite In_or_Iff_Union.
      rename H7 into Hused.
      clear - Hused.
      specialize (Hused arbitrary).
      unfold used_vars, used_vars_fundefs in Hused.
      repeat rewrite In_or_Iff_Union in Hused.
      tauto.
  Qed.

  Corollary uncurry_step_maintains_bindings: forall e s m e1 s1 m1,
    uncurry_step e s m e1 s1 m1 ->
    used_vars e \subset s ->
    bound_var e1 :&: s <--> bound_var e.
  Proof. apply uncurry_step_maintains_bindings_mut. Qed.

  Corollary uncurry_fundefs_step_maintains_bindings: forall f s m f1 s1 m1,
    uncurry_fundefs_step f s m f1 s1 m1 ->
    used_vars_fundefs f \subset s ->
    bound_var_fundefs f1 :&: s <--> bound_var_fundefs f.
  Proof. apply uncurry_step_maintains_bindings_mut. Qed.

  Corollary uncurry_step_maintains_bindings_fn: forall e s m e1 s1 m1,
    uncurry_step e s m e1 s1 m1 ->
    used_vars e \subset s -> forall a,
    In _ (bound_var e1) a ->
    In _ s a ->
    In _ (bound_var e) a.
  Proof. intros; rewrite <- uncurry_step_maintains_bindings; eauto. Qed.

  Corollary uncurry_fundefs_step_maintains_bindings_fn: forall f s m f1 s1 m1,
    uncurry_fundefs_step f s m f1 s1 m1 ->
    used_vars_fundefs f \subset s -> forall a,
    In _ (bound_var_fundefs f1) a ->
    In _ s a ->
    In _ (bound_var_fundefs f) a.
  Proof. intros; rewrite <- uncurry_fundefs_step_maintains_bindings; eauto. Qed.

  Lemma uncurry_step_preserves_unique_bindings_mut :
    let P := (fun e s m e1 s1 m1 =>
                used_vars e \subset s ->
                unique_bindings e ->
                unique_bindings e1) in
    let Q := (fun f s m f1 s1 m1 =>
                used_vars_fundefs f \subset s ->
                unique_bindings_fundefs f ->
                unique_bindings_fundefs f1) in
    (forall e s m e1 s1 m1, uncurry_step e s m e1 s1 m1 -> P e s m e1 s1 m1) /\
    (forall f s m f1 s1 m1, uncurry_fundefs_step f s m f1 s1 m1 -> Q f s m f1 s1 m1).
  Proof with eauto with Ensembles_DB.
    intros P Q.
    uncurry_induction_mut P Q IHstep IH; subst P; subst Q; simpl in *; intros.
    - (* Eletapp *)
      rewrite used_vars_Eletapp in H; inv H0.
      assert (used_vars e \subset s).
      eapply Included_trans; [|eassumption]...
      assert (unique_bindings e)...
      constructor; auto.
      intros contra.
      contradiction H3.
      eapply uncurry_step_maintains_bindings_fn; eauto.
    - (* Econstr *)
      rewrite used_vars_Econstr in H; inv H0.
      assert (used_vars e \subset s).
      eapply Union_Included_r...
      assert (unique_bindings e)...
      constructor; auto.
      intros contra.
      contradiction H3.
      eapply uncurry_step_maintains_bindings_fn; eauto.
    - (* Ecase arm *)
      rewrite used_vars_Ecase_cons in H; inv H0.
      assert (used_vars e \subset s).
      eapply Union_Included_l...
      constructor; auto.
      constructor; intros a contra; destruct contra.
      inv H7. contradiction (H3 x0).
      split; auto.
      eapply uncurry_step_maintains_bindings_fn; eauto.
      apply H; right; now left.
    - (* Ecase arms *)
      destruct arm; rewrite used_vars_Ecase_cons in H; inv H0.
      assert (used_vars (Ecase x arms) \subset s).
      eapply Union_Included_r...
      constructor; auto.
      constructor; intros a contra; destruct contra.
      inv H7. contradiction (H3 x0).
      split; auto.
      eapply uncurry_step_maintains_bindings_fn; eauto.
      apply H; left; now left.
    - (* Eproj *)
      rewrite used_vars_Eproj in H; inv H0.
      assert (used_vars e \subset s).
      do 2 eapply Union_Included_r...
      constructor; auto.
      intros contra.
      contradiction H3.
      eapply uncurry_step_maintains_bindings_fn; eauto.
    - (* Eprim *)
      rewrite used_vars_Eprim in H; inv H0.
      assert (used_vars e \subset s).
      eapply Union_Included_r...
      constructor; auto.
      intros contra; contradiction H3; eapply uncurry_step_maintains_bindings_fn; eauto.
    - (* Eprim_val *)
      rewrite used_vars_Eprim_val in H; inv H0.
      assert (used_vars e \subset s).
      eapply Union_Included_r...
      constructor; auto.
      intros contra; contradiction H3; eapply uncurry_step_maintains_bindings_fn; eauto.
    - (* Efun e *)
      rewrite used_vars_Efun in H; inv H0.
      assert (used_vars e \subset s).
      eapply Union_Included_r...
      constructor; auto.
      constructor; intros a contra; destruct contra.
      inv H5. contradiction (H6 x).
      split; auto.
      eapply uncurry_step_maintains_bindings_fn; eauto.
      apply H; left; now left.
    - (* Efun fds *)
      rewrite used_vars_Efun in H; inv H0.
      assert (used_vars_fundefs fds \subset s).
      eapply Union_Included_l...
      constructor; auto.
      constructor; intros a contra; destruct contra.
      inv H5. contradiction (H6 x).
      split; auto.
      eapply uncurry_fundefs_step_maintains_bindings_fn; eauto.
      apply H; right; now left.
    - (* Fcons fds *)
      rewrite used_vars_Fcons in H; inv H0.
      assert (used_vars_fundefs fds \subset s).
      eapply Union_Included_r...
      constructor; auto.
      intros contra.
      contradiction H7; eapply uncurry_fundefs_step_maintains_bindings_fn; eauto.
      constructor; intros a contra; destruct contra.
      inv H9. contradiction (H3 x).
      split; auto.
      eapply uncurry_fundefs_step_maintains_bindings_fn; eauto.
      constructor; intros a contra; destruct contra.
      inv H10. contradiction (H3 x).
      split; auto.
      eapply uncurry_fundefs_step_maintains_bindings_fn; eauto.
      apply H; left; right; now left.
    - (* Fcons e *)
      rewrite used_vars_Fcons in H; inv H0.
      assert (used_vars e \subset s).
      eapply Union_Included_r. eapply Union_Included_l...
      constructor; auto.
      intros contra.
      contradiction H6; eapply uncurry_step_maintains_bindings_fn; eauto.
      constructor; intros a contra; destruct contra.
      inv H8. contradiction (H3 x). split; auto.
      eapply uncurry_step_maintains_bindings_fn; eauto.
      constructor; intros a contra; destruct contra.
      inv H10; contradiction (H3 x); split; auto.
      eapply uncurry_step_maintains_bindings_fn; eauto.
      apply H; right; now left.
    - (* Fcons curried *)
      repeat (rewrite used_vars_Fcons in H8 + rewrite used_vars_Efun in H8).
      repeat rewrite Union_assoc in H8.
      rewrite not_occurs_in_exp_iff_used_vars in H0.
      rewrite not_occurs_in_exp_iff_used_vars in H1.
      unfold fresh_copies in *; destruct H2; destruct H4.
      repeat rewrite Union_demorgan in H6.
      do 2 destruct H6.
      constructor.
      Local Ltac clear_false_bound_var_hyps :=
        try match goal with
          [ H : bound_var_fundefs Fnil _ |- _ ] => inv H
        | [ H : bound_var (Eapp _ _ _) _ |- _ ] => inv H
        | [ _ : _ |- ~ bound_var_fundefs Fnil _ ] => inversion 1
        | [ _ : _ |- ~ bound_var (Eapp _ _ _) _ ] => inversion 1
        end.
      + intros contra; inv contra; clear_false_bound_var_hyps.
        inv H17; inv_all; clear_false_bound_var_hyps.
        * inv H9.
          contradiction H19. constructor. constructor. now left.
        * inv H2. contradiction (H15 f9).
          split; auto. apply H8; now do 7 left.
      + intros contra; inv contra.
        inv_all.
        * contradiction H6; apply H8; now do 7 left.
        * rewrite FromList_app in H14; inv H14.
          inv H9.
          contradiction H20.
          constructor.
          constructor.
          now right.
          inv H9.
          contradiction H25; now right.
        * now inv H9.
        * inv H9. contradiction H19.
          constructor.
          now apply Bound_Fcons3.
      + constructor; intros a contra; destruct contra.
        inv_all; clear_false_bound_var_hyps.
        inv H18; inv_all; clear_false_bound_var_hyps.
        inv H9; inv_all; clear_false_bound_var_hyps.
        inv H21. contradiction (H9 x).
        split; [|now left].
        constructor; constructor; now constructor.
        inv H2. contradiction (H15 x).
        split; auto.
        apply H8; do 6 left; right; now left.
        inv H19; inv_all; clear_false_bound_var_hyps.
        inv H4. contradiction (H14 x).
        split; auto; left; apply H8; do 5 left; now right.
        inv H4; contradiction (H15 x); split; auto; right.
      + constructor; intros a contra; destruct contra.
        inv_all; clear_false_bound_var_hyps.
        * contradiction H6; apply H8; do 6 left; right; now left.
        * rewrite FromList_app in H14; inv H14.
          inv H9. inv H22. contradiction (H9 x).
          split; auto; now left.
          inv H9; inv H26. contradiction.
        * inv H9. inv H23. contradiction (H9 x); split; auto; now left.
        * contradiction H1; now left.
        * rewrite FromList_app in H14; inv H14.
          inv H4. contradiction (H14 x).
          split; auto; left; apply H8; do 4 left; now right.
          inv H4. contradiction (H14 x).
          split; auto; left; apply H8; do 6 left; right; now right.
        * inv H4. contradiction (H14 x).
          split; auto; left; apply H8; right; now left.
        * inv H4. contradiction (H14 x).
          split; auto; left; apply H8; do 3 left; right; now left.
      + constructor; intros a contra; destruct contra.
        inv_all; clear_false_bound_var_hyps.
        * inv H18; inv_all; clear_false_bound_var_hyps.
          contradiction H6; apply H8; do 5 left; now right.
        * rewrite FromList_app in H15; inv H15.
          inv H19; inv_all; clear_false_bound_var_hyps.
          inv H9. inv H27. inv H17. contradiction.
          inv H2. contradiction (H16 x); split; auto.
          apply H8; do 4 left; now right.
          inv H19; inv_all; clear_false_bound_var_hyps.
          inv H9. inv H27. inv H22. contradiction (H9 x).
          split; auto; now right.
          inv H2. contradiction (H16 x); split; auto.
          apply H8; do 6 left; right; now right.
        * inv H18; inv_all; clear_false_bound_var_hyps.
          inv H9. inv H24. contradiction (H9 x); split; auto.
          inv H2. contradiction (H15 x); split; auto.
          apply H8; right; now left.
        * inv H18; inv_all; clear_false_bound_var_hyps.
          inv H9. inv H27. inv H16. contradiction.
          inv H2. contradiction (H15 x). split; auto.
          apply H8; do 3 left; right; now left.
      + inversion 1; subst.
        inv H9. contradiction H25; now left.
        inv H4. contradiction (H16 f9); split; auto.
        left; apply H8; now do 7 left.
      + constructor; auto; intros contra.
        inv H4. contradiction (H14 k); split; auto.
        left; apply H8; do 6 left; right; now left.
      + constructor; [constructor ..|]; clear_false_bound_var_hyps; auto.
        rewrite bound_var_Eapp...
        rewrite bound_var_fundefs_Fnil...
        rewrite bound_var_Eapp...
        intros contra.
        inv H2. contradiction (H14 g); split; auto; apply H8.
        do 5 left; now right.
        constructor.
        constructor.
        rewrite bound_var_Eapp...
      + constructor.
        intros contra.  contradiction H6. apply H8. do 3 left. right. now left.
        intros contra; contradiction H6; apply H8; right; now left.
        constructor. intros a contra. inv contra.
        rewrite FromList_app in H15. destruct H15.
        inv H9. inv H28. inv H18. inv H33. contradiction (H9 x); split; auto.
        inv H9. inv H23. contradiction (H9 x); split; auto; now right.
        constructor; intros a contra; inv contra.
        rewrite FromList_app in H15; destruct H15.
        inv H9. inv H25. contradiction (H9 x); split; auto.
        inv H9. inv H24. contradiction (H9 x); split; auto; now right.
        constructor; intros a contra; inv contra.
        inv H9. inv H25. contradiction (H9 a); split; auto.
        change (~ In _ (FromList (gv ++ fv)) f10).
        intros contra; rewrite FromList_app in contra; destruct contra.
        contradiction H6; apply H8; do 4 left; now right.
        contradiction H6; apply H8; do 6 left; right; now right.
        apply NoDup_app.
        inv H9. inv H26. now inv H16.
        inv H9. now inv H25.
        inv H9. inv H21.
        intros a Hin Hin'.
        contradiction (H9 a). split. auto. now right.
        inv H9. inv H26. now inv H16.
        now inv H9.
    - (* anf *)
      repeat normalize_used_vars; unfold used_vars, used_vars_fundefs in *.
      repeat match goal with
      | H : fresh_copies _ _ |- _ => destruct H
      | H : ?S1 :|: ?S2 \subset ?S3 |- _ => apply Union_Included_lr in H; destruct H
      | H : unique_bindings (_ _) |- _ => inv H
      | H : unique_bindings_fundefs (_ _) |- _ => inv H
      end.
      change (~ bound_var ?e ?x) with (~ In _ (bound_var e) x) in *;
      change (~ bound_var_fundefs ?fds ?x) with (~ In _ (bound_var_fundefs fds) x) in *;
      repeat normalize_bound_var_in_ctx.
      repeat match goal with
      | H : ~ In _ (_ :|: _) _ |- _ => rewrite Union_demorgan in H; destruct H
      | H : Disjoint ?A (?S1 :|: ?S2) ?S3 |- _ =>
        assert (Disjoint A S1 S3) by (apply Disjoint_Union_l in H; apply H);
        apply Disjoint_Union_r in H
      | H : Disjoint ?A ?S1 (?S2 :|: ?S3) |- _ => apply Disjoint_sym in H
      end.
      repeat progress multimatch goal with
      | Hdis : Disjoint var s ?S2, Hsub : ?S1 \subset s |- _ =>
        match goal with
        | Hconc : Disjoint var S1 S2 |- _ => idtac
        | _ => assert (Disjoint var S1 S2) by (eapply Disjoint_Included_l; [apply Hsub|apply Hdis])
        end
      end.
      assert (Disjoint_In_falso : forall S x, In var S x -> Disjoint var S [set x] -> False). {
        intros S x Hin [Hdis]; contradiction (Hdis x); now constructor. }
      repeat match goal with
      | |- unique_bindings (_ _) => constructor
      | |- unique_bindings_fundefs (_ _) => constructor
      end;
      change (~ bound_var ?e ?x) with (~ In _ (bound_var e) x) in *;
      change (~ bound_var_fundefs ?fds ?x) with (~ In _ (bound_var_fundefs fds) x) in *;
      change (~ FromList ?xs ?x) with (~ In _ (FromList xs) x) in *;
      repeat normalize_bound_var; repeat normalize_sets;
      repeat match goal with
      | |- Disjoint _ (_ :|: _) _ => apply Union_Disjoint_l
      | |- Disjoint _ _ (_ :|: _) => apply Union_Disjoint_r
      | |- ~ In _ (_ :|: _) _ => rewrite Union_demorgan; split
      | |- NoDup (_ ++ _) => apply NoDup_app
      end...
      + intros Hin. apply (Disjoint_In_falso _ _ Hin)...
      + now apply Disjoint_sym.
      + intros a Hin.
        apply (Disjoint_In_l (FromList gv) (FromList fv) a) in H49.
        apply H49. apply Hin.
  Qed.

  Corollary uncurry_step_preserves_unique_bindings : forall e s m e1 s1 m1,
    uncurry_step e s m e1 s1 m1 ->
    used_vars e \subset s ->
    unique_bindings e ->
    unique_bindings e1.
  Proof. apply uncurry_step_preserves_unique_bindings_mut. Qed.

  Corollary uncurry_fundefs_step_preserves_unique_bindings : forall f s m f1 s1 m1,
    uncurry_fundefs_step f s m f1 s1 m1 ->
    used_vars_fundefs f \subset s ->
    unique_bindings_fundefs f ->
    unique_bindings_fundefs f1.
  Proof. apply uncurry_step_preserves_unique_bindings_mut. Qed.

  Hint Constructors unique_bindings : core.

  Lemma uncurry_fundefs_step_unique_names : forall a f s m f1 s1 m1,
    used_vars_fundefs f \subset s ->
    uncurry_fundefs_step f s m f1 s1 m1 ->
    name_in_fundefs f1 a ->
    ~ name_in_fundefs f a ->
    ~ In var s a.
  Proof with eauto with Ensembles_DB.
    intros a f s m f1 s1 m1 Hused Hstep Hf1 Hf2.
    induction Hstep; try solve [inv Hf1; [inv H0|]; contradiction Hf; [now left|now right]].
    - apply IHHstep.
      eapply Included_trans; [|eauto]; repeat normalize_used_vars...
      inv Hf1; auto.
      inv H; contradiction Hf2; now left.
      intros contra; contradiction Hf2; now right.
    - simpl in *.
      inv Hf1; contradiction Hf2. now left. now right.
    - simpl in *.
      inv Hf1.
      + contradiction Hf2. now left.
      + destruct H8.
        * inv H8.
          intros Hin; contradiction H6; now do 2 left.
        * contradiction Hf2. now right.
    - simpl in *.
      inv Hf1.
      + contradiction Hf2. now left.
      + destruct H7.
        * inv H7.
          intros Hin; contradiction H5; now do 2 left.
        * contradiction Hf2. now right.
  Qed.

  Lemma uncurry_fundefs_step_preserves_names : forall a f s m f1 s1 m1,
    name_in_fundefs f a ->
    uncurry_fundefs_step f s m f1 s1 m1 ->
    name_in_fundefs f1 a.
  Proof.
    intros a f s m f1 s1 m1 Hf' Hstep.
    induction Hstep; try solve [inv Hf'; [inv H0; now left|now right]].
    - inv Hf'.
      inv H; now left.
      right; now apply IHHstep.
    - inv Hf'.
      inv H7; now left.
      right; now right.
    - inv Hf'.
      inv H7; now left.
      right; now right.
  Qed.

  Lemma uncurry_fundefs_step_preserves_tags : forall a f s m f1 s1 m1 t v e t1 v1 e1,
    used_vars_fundefs f \subset s ->
    uncurry_fundefs_step f s m f1 s1 m1 ->
    find_def a f = Some (t, v, e) ->
    find_def a f1 = Some (t1, v1, e1) ->
    t = t1.
  Proof with eauto 10 with Ensembles_DB.
    intros a f s m f1 s1 m1 t v e t1 v1 e1 Hused Hstep Hf1 Hf2.
    induction Hstep; simpl in Hf1, Hf2; destruct (M.elt_eq a f); subst;
      inv Hf1; inv Hf2; auto;
      try solve [rewrite H1 in H2; now inv H2].
    - apply IHHstep; auto.
      rewrite used_vars_Fcons in Hused.
      eapply Included_trans...
    - destruct (M.elt_eq a f1); subst.
      + contradiction H6.
        left; left.
        apply Hused; left.
        apply Bound_Fcons2.
        apply name_in_fundefs_bound_var_fundefs.
        eapply find_def_name_in_fundefs; eauto.
      + rewrite H9 in H10; now inv H10.
    - destruct (M.elt_eq a f1); subst.
      + contradiction H5.
        left; left.
        apply Hused; left.
        apply Bound_Fcons2.
        apply name_in_fundefs_bound_var_fundefs.
        eapply find_def_name_in_fundefs; eauto.
      + rewrite H8 in H9; now inv H9.
  Qed.

  Lemma uncurry_fundefs_step_preserves_length : forall a f s m f1 s1 m1 t v e t1 v1 e1,
    used_vars_fundefs f \subset s ->
    uncurry_fundefs_step f s m f1 s1 m1 ->
    find_def a f = Some (t, v, e) ->
    find_def a f1 = Some (t1, v1, e1) ->
    length v = length v1.
  Proof with eauto 10 with Ensembles_DB.
    intros a f s m f1 s1 m1 t v e t1 v1 e1 Hused Hstep Hf1 Hf2.
    induction Hstep; simpl in Hf1, Hf2; destruct (M.elt_eq a f); subst;
      inv Hf1; inv Hf2; auto;
      try solve [rewrite H1 in H2; now inv H2].
    - apply IHHstep; auto.
      rewrite used_vars_Fcons in Hused.
      eapply Included_trans...
    - simpl; now apply f_equal.
    - destruct (M.elt_eq a f1); subst.
      + contradiction H6.
        left; left.
        apply Hused; left.
        apply Bound_Fcons2.
        apply name_in_fundefs_bound_var_fundefs.
        eapply find_def_name_in_fundefs; eauto.
      + rewrite H9 in H10; now inv H10.
    - destruct (M.elt_eq a f1); subst.
      + contradiction H5.
        left; left.
        apply Hused; left.
        apply Bound_Fcons2.
        apply name_in_fundefs_bound_var_fundefs.
        eapply find_def_name_in_fundefs; eauto.
      + rewrite H8 in H9; now inv H9.
  Qed.

  Lemma find_def_body_occurs_free_Included : forall fds a t xs e,
    find_def a fds = Some (t, xs, e) ->
    occurs_free e \subset name_in_fundefs fds :|: occurs_free_fundefs fds :|: FromList xs.
  Proof.
    induction fds; intros a t xs e0 Hfind; [|inv Hfind].
    simpl in Hfind.
    destruct (M.elt_eq a v).
    - inv Hfind.
      intros a Ha.
      split_var_in_fundefs a (Fcons v t xs e0 fds) Hfds; [now do 2 left|].
      split_var_in_list a xs; [now right|].
      left; right; constructor; auto.
      intro contra; subst; contradiction n; now left.
      intros contra; contradiction n; now right.
    - eapply Included_trans.
      eapply IHfds; eauto.
      intros b Hb; inv Hb; [inv H|]; [left; left; now right| |now right].
      split_var_in_fundefs b (Fcons v f l e fds) Hfds; [left; now left|].
      left; right.
      apply Free_Fcons2; eauto.
      intros contra; subst; contradiction n0; now left.
  Qed.

  Lemma fundefs_append_assoc : forall A B C,
    fundefs_append A (fundefs_append B C) = fundefs_append (fundefs_append A B) C.
  Proof.
    induction A.
    - intros B C; simpl. now rewrite IHA.
    - auto.
  Qed.

  Lemma preord_exp_eq_compat :
    forall (cenv : ctor_env) (P1 : PostT) (PG : PostGT)
           (Hprop1 : Post_properties cenv P1 P1 PG)
           (Hprop2 : Post_properties cenv PG PG PG)
           (k : nat) (rho1 rho2 : env) (c : exp_ctx) (e1 e2 e1' e2' : exp),
      (forall (m : nat) (rho3 rho4 : env),
          m <= k ->
          preord_env_P cenv PG (occurs_free e1) m rho3 rho4 ->
          preord_exp' cenv (preord_val cenv) P1 PG m (e1, rho3) (e2, rho4)) ->
      c |[ e1 ]| = e1' -> c |[ e2 ]| = e2' ->
      preord_env_P cenv PG (occurs_free e1') k rho1 rho2 ->
      preord_exp' cenv (preord_val cenv) P1 PG k (e1', rho1) (e2', rho2).
  Proof.
    intros.
    rewrite <- H0, <- H1; apply preord_exp_compat; auto.
    now rewrite H0.
  Qed.

  Definition ctx_preord_exp (k : nat) (e e1 : exp) := forall rho rho1,
    preord_env_P cenv PostG (occurs_free e) k rho rho1 ->
    preord_exp cenv Post PostG k (e, rho) (e1, rho1).

  (* Obligations generated by cps and anf proofs *)
  Variables
    (Hpost_refl_constr : post_constr_compat Post Post)
    (Hpost_refl_proj : post_proj_compat Post Post)
    (Hpost_refl_fun : post_fun_compat Post Post)
    (Hpost_refl_case_hd : post_case_compat_hd Post Post)
    (Hpost_refl_case_tl : post_case_compat_tl Post Post)
    (Hpost_refl_app : post_app_compat Post Post)
    (Hpost_refl_letapp : post_letapp_compat cenv Post Post Post)
    (Hpost_refl_letapp_OOT : post_letapp_compat_OOT Post Post)
    (Hpost_refl_primval : post_primval_compat Post Post)
    (Hpost_refl_OOT : post_OOT Post)
    (Hpost_refl_base : post_base Post).

  Variables
    (Hpost_app : post_app_compat Post PostG)
    (Hpost_letapp : post_letapp_compat cenv Post Post PostG)
    (Hpost_letapp_OOT : post_letapp_compat_OOT Post PostG)
    (Hpost_inclusion : inclusion (exp * env * fuel * trace) Post PostG).

  Variable
    (HpostG_refl_constr : post_constr_compat PostG PostG)
    (HpostG_refl_proj : post_proj_compat PostG PostG)
    (HpostG_refl_fun : post_fun_compat PostG PostG)
    (HpostG_refl_case_hd : post_case_compat_hd PostG PostG)
    (HpostG_refl_case_tl : post_case_compat_tl PostG PostG)
    (HpostG_refl_app : post_app_compat PostG PostG)
    (HpostG_refl_letapp : post_letapp_compat cenv PostG PostG PostG)
    (HpostG_refl_letapp_OOT : post_letapp_compat_OOT PostG PostG)
    (HpostG_refl_primval : post_primval_compat PostG PostG)
    (HpostG_refl_OOT : post_OOT PostG)
    (HpostG_refl_base : post_base PostG).

  Lemma uncurry_step_correct' :
    let P := (fun e s _ e1 s1 _ => forall k,
                  unique_bindings e ->
                  unique_bindings e1 -> (* TODO: remove this assumption *)
                  used_vars e \subset s ->
                  used_vars e1 \subset s1 -> (* TODO: remove this assumption *)
                  ctx_preord_exp k e e1) in
    let Q := (fun f s (m : localMap) f1 s1 (m1 : localMap) => forall f' k e,
                  unique_bindings (Efun (fundefs_append f' f) e) ->
                  unique_bindings (Efun (fundefs_append f' f1) e) -> (* TODO: remove this assumption *)
                  used_vars (Efun (fundefs_append f' f) e) \subset s ->
                  used_vars (Efun (fundefs_append f' f1) e) \subset s1 -> (* TODO: remove this assumption *)
                  ctx_preord_exp k (Efun (fundefs_append f' f) e) (Efun (fundefs_append f' f1) e)) in
    forall e s m e1 s1 m1,
    uncurry_step e s m e1 s1 m1 -> P e s m e1 s1 m1.
  Proof with eauto 10 with Ensembles_DB.
    intros P Q.
    uncurry_step_induction P Q IHuncurry IH;
      subst P; subst Q; simpl in *;
      [ intros k .. | intros f' k' e' | intros f' k' e' | intros f' k' e' | intros f' k' e' ];
      intros Hunique Hunique1 Hused Hused1 rho rho1 Henv.
    - (* uncurry_letapp *)
      eapply preord_exp_letapp_compat; try eassumption; try easy_post.
      + eapply Hpost_prop.
      + eapply Hpost_prop.
      + eapply Hpost_prop.
      + unfold preord_env_P in Henv.
        intros a Hin.
        apply Henv; [|easy].
        constructor; now left.
      + unfold preord_env_P in Henv.
        apply Forall2_same.
        intros a Hin.
        apply Henv.
        apply Free_Eletapp1; now right.
      + intros k' args1 args2 Hargs Hk'.
        apply IH; inv Hunique; inv Hunique1; auto.
        rewrite used_vars_Eletapp in Hused.
        eapply Included_trans; [|eassumption]...
        rewrite used_vars_Eletapp in Hused1.
        eapply Included_trans; [|eassumption]...
        apply preord_env_P_extend.
        * intros x1 Hx1.
          apply preord_var_env_monotonic with (k := k); [|lia].
          apply Henv.
          inversion Hx1. apply Free_Eletapp2; [|assumption].
          intros contra. subst. intuition.
        * assumption.
    - (* uncurry_constr *)
      eapply preord_exp_constr_compat; try eassumption; try easy_post.
      + eapply Hpost_prop.
      + eapply Hpost_prop.
      + unfold preord_env_P in Henv.
        apply Forall2_same.
        intros a Hin.
        apply Henv.
        now apply Free_Econstr1.
      + intros k' args1 args2 Hargs Hk'.
        apply IH; inv Hunique; inv Hunique1; auto.
        rewrite used_vars_Econstr in Hused.
        eapply Included_trans; [|eassumption]...
        rewrite used_vars_Econstr in Hused1.
        eapply Included_trans; [|eassumption]...
        apply preord_env_P_extend.
        * intros x1 Hx1.
          apply preord_var_env_monotonic with (k := k); [|lia].
          apply Henv.
          inversion Hx1. apply Free_Econstr2; [|assumption].
          intros contra. subst. intuition.
        * rewrite preord_val_eq. split; [trivial|]. eassumption.
    - (* uncurry_case_expr *)
      eapply preord_exp_case_cons_compat; try eassumption; try easy_post.
      + eapply Hpost_prop.
      + eapply Hpost_prop.
      + eapply Hpost_prop.
      + now apply List_util.Forall2_refl.
      + now apply Henv.
      + intros k' Hk'; apply IH; inv Hunique; inv Hunique1; auto.
        rewrite used_vars_Ecase_cons in Hused.
        eapply Included_trans; [|eassumption]...
        rewrite used_vars_Ecase_cons in Hused1.
        eapply Included_trans; [|eassumption]...
        apply preord_env_P_monotonic with (k := k); [lia|].
        eapply preord_env_P_antimon; [eassumption|].
        eapply occurs_free_Ecase_Included; simpl; eauto.
      + apply preord_exp_refl. eassumption.
        eapply preord_env_P_antimon; [eassumption|].
        rewrite occurs_free_Ecase_cons...
    - (* uncurry_case_arms *)
      destruct arm.
      eapply preord_exp_case_cons_compat; try eassumption; try easy_post.
      + eapply Hpost_prop.
      + eapply Hpost_prop.
      + eapply Hpost_prop.
      + eapply uncurry_step_preserves_ctag; eauto.
      + now apply Henv.
      + intros k' Hk'; apply preord_exp_refl. eassumption.
        apply preord_env_P_monotonic with (k := k); [lia|].
        eapply preord_env_P_antimon; [eassumption|].
        rewrite occurs_free_Ecase_cons...
      + apply IH; inv Hunique; inv Hunique1; auto.
        rewrite used_vars_Ecase_cons in Hused.
        eapply Included_trans; [|eassumption]...
        rewrite used_vars_Ecase_cons in Hused1.
        eapply Included_trans; [|eassumption]...
        apply preord_env_P_monotonic with (k := k); [lia|].
        eapply preord_env_P_antimon; [eassumption|].
        rewrite occurs_free_Ecase_cons...
    - (* uncurry_proj *)
      eapply preord_exp_proj_compat; try eassumption; try easy_post.
      now eapply Hpost_prop.
      now eapply Hpost_prop.
      now apply Henv.
      intros k' v1 v2 Hk' Hv1_v2.
      apply IH; inv Hunique; inv Hunique1; auto.
      rewrite used_vars_Eproj in Hused.
      eapply Included_trans; [|eassumption]...
      rewrite used_vars_Eproj in Hused1.
      eapply Included_trans; [|eassumption]...
      intros a Ha; split_var_eq a x; subst; unfold preord_var_env.
      + do 2 rewrite M.gss.
        intros v0 Hv0; inv Hv0; eauto.
      + do 2 (rewrite M.gso; [|assumption]).
        apply preord_env_P_monotonic with (j := k') in Henv; [|lia].
        apply Henv; auto.
    - (* uncurry_prim *)
      apply preord_exp_prim_compat.
      now eapply Hpost_prop.
      + induction args; constructor.
        apply Henv; constructor; now left.
        inv Hunique; inv Hunique1.
        apply IHargs; try constructor; auto.
        rewrite used_vars_Eprim in *.
        rewrite FromList_cons in Hused.
        eapply Included_trans; [|eassumption]...
        rewrite used_vars_Eprim in *.
        rewrite FromList_cons in Hused1.
        eapply Included_trans; [|eassumption]...
        eapply preord_env_P_antimon; [eassumption|].
        intros a' Ha'; inv Ha'.
        constructor; now right.
        apply Free_Eprim2; assumption.
    - (* uncurry_prim_val *) 
      eapply preord_exp_prim_val_compat.
      now eapply Hpost_prop.
      now apply Hpost_prop.
      intros k' v1 v2 Hk' Hv1_v2.
      apply IH; inv Hunique; inv Hunique1; auto.
      rewrite used_vars_Eprim_val in Hused.
      eapply Included_trans; [|eassumption]...
      rewrite used_vars_Eprim_val in Hused1.
      eapply Included_trans; [|eassumption]...
      intros a Ha; split_var_eq a v; subst; unfold preord_var_env.
      + do 2 rewrite M.gss.
        intros v0 Hv0; inv Hv0; eauto.
        exists (Vprim p). split; eauto.
        now eapply preord_val_eq.
      + do 2 (rewrite M.gso; [|assumption]).
        apply preord_env_P_monotonic with (j := k') in Henv; [|lia].
        apply Henv; auto. (* uncurry_prim_val *)
    - (* uncurry_fun_expr *)
      eapply preord_exp_fun_compat; try eassumption.
      now eapply Hpost_prop. now eapply Hpost_prop.
      apply IH; inv Hunique; inv Hunique1; auto.
      rewrite used_vars_Efun in Hused.
      eapply Included_trans; [|eassumption]...
      rewrite used_vars_Efun in Hused1.
      eapply Included_trans; [|eassumption]...
      intros a Ha; split_var_in_fundefs a fds Hfds; unfold preord_var_env.
      + do 2 (rewrite def_funs_eq; [|assumption]).
        intros v1 Hv1; inv Hv1; eexists; split; [reflexivity|].
        apply preord_val_fundefs; try easy_post.
        apply preord_env_P_monotonic with (k := k); [lia|].
        eapply preord_env_P_antimon; [eassumption|].
        rewrite occurs_free_Efun...
      + do 2 (rewrite def_funs_neq; [|assumption]).
        apply preord_env_P_monotonic with (j := k - 1) in Henv; [|lia].
        apply Henv; auto.
    - (* uncurry_fun_fds *)
      apply IH with (f' := Fnil); eauto.
    - (* uncurry_fundefs_fds *)
      replace (fundefs_append f' (Fcons f t args e fds))
        with (fundefs_append (fundefs_append f' (Fcons f t args e Fnil)) fds)
        by now rewrite <- fundefs_append_assoc.
      replace (fundefs_append f' (Fcons f t args e fds1))
        with (fundefs_append (fundefs_append f' (Fcons f t args e Fnil)) fds1)
        by now rewrite <- fundefs_append_assoc.
      apply IH with (f' := fundefs_append f' (Fcons f t args e Fnil));
        rewrite <- fundefs_append_assoc; auto.
    - (* uncurry_fundefs_e *)
      edestruct fundefs_append_ctx_exists
        with (f' := f') (c' := Fcons1_c f t args Hole_c fds) as [c Hc].
      eapply preord_exp_eq_compat with (c := Efun2_c c e') (e1 := e) (e2 := e1); eauto.
      unfold ctx_preord_exp in IH.
      inv Hunique; inv Hunique1.
      apply fundefs_append_unique_and in H2; destruct H2.
      apply fundefs_append_unique_and in H5; destruct H5.
      inv H0; inv H5.
      intros k rho0 rho2 Hk; eapply IH; auto.
      eapply Included_trans; eauto.
      rewrite used_vars_Efun.
      rewrite fundefs_append_used_vars.
      rewrite used_vars_Fcons...
      eapply Included_trans; eauto.
      rewrite used_vars_Efun.
      rewrite fundefs_append_used_vars.
      rewrite used_vars_Fcons...
      all: simpl; now rewrite Hc.
    - (* uncurry_fundefs_curried *)
      eapply uncurry_step_correct_fundefs_curried; eauto...
      eapply Included_trans; [|apply Hused].
      rewrite used_vars_Efun...
      rewrite H7 in Hused1.
      eapply Included_trans; [|apply Hused1].
      rewrite used_vars_Efun...
      now inv Hunique.
      eapply Union_Included_l.
      eapply Included_trans; [|apply Hused].
      rewrite used_vars_Efun...
      now inv Hunique1.
    - (* anf uncurrying *)
      eapply uncurry_step_correct_fundefs_curried_anf; eauto...
      eapply Included_trans; [|apply Hused].
      rewrite used_vars_Efun...
      rewrite H6 in Hused1.
      eapply Included_trans; [|apply Hused1].
      rewrite used_vars_Efun...
      now inv Hunique.
      eapply Union_Included_l.
      eapply Included_trans; [|apply Hused].
      rewrite used_vars_Efun...
      now inv Hunique1.
  Qed.

  Lemma uncurry_step_correct : forall k e s m e1 s1 m1,
    unique_bindings e ->
    unique_bindings e1 -> (* TODO: remove this assumption *)
    used_vars e \subset s ->
    used_vars e1 \subset s1 -> (* TODO: remove this assumption *)
    uncurry_step e s m e1 s1 m1 -> ctx_preord_exp k e e1.
  Proof. intros. intros rho rho1 Henv. eapply uncurry_step_correct'; eauto. Qed.

  Lemma uncurry_step_increases_size_mut :
    let P := (fun e s m e1 s1 m1 => sizeOf_exp e < sizeOf_exp e1) in
    let Q := (fun f s m f1 s1 m1 => sizeOf_fundefs f < sizeOf_fundefs f1) in
    (forall e s m e1 s1 m1, uncurry_step e s m e1 s1 m1 -> P e s m e1 s1 m1) /\
    (forall f s m f1 s1 m1, uncurry_fundefs_step f s m f1 s1 m1 -> Q f s m f1 s1 m1).
  Proof with eauto with Ensembles_DB.
    intros P Q.
    uncurry_induction_mut P Q IHstep IH; subst P; subst Q;
    try (try destruct arm; simpl in *; lia).
  Qed.

  Corollary uncurry_step_increases_size : forall e s m e1 s1 m1,
    uncurry_step e s m e1 s1 m1 -> sizeOf_exp e < sizeOf_exp e1.
  Proof. apply uncurry_step_increases_size_mut. Qed.

  Corollary uncurry_fundefs_step_increases_size : forall f s m f1 s1 m1,
    uncurry_fundefs_step f s m f1 s1 m1 -> sizeOf_fundefs f < sizeOf_fundefs f1.
  Proof. apply uncurry_step_increases_size_mut. Qed.

  Lemma uncurry_step_acyclic : forall e s m e1 s1 m1 s2 m2,
    uncurry_step e s m e1 s1 m1 -> ~ uncurry_step e1 s1 m1 e s2 m2.
  Proof.
    intros; intros H1.
    apply uncurry_step_increases_size in H.
    apply uncurry_step_increases_size in H1.
    lia.
  Qed.

  Lemma uncurry_fundefs_step_acyclic : forall e s m e1 s1 m1 s2 m2,
    uncurry_fundefs_step e s m e1 s1 m1 -> ~ uncurry_fundefs_step e1 s1 m1 e s2 m2.
  Proof.
    intros; intros H1.
    apply uncurry_fundefs_step_increases_size in H.
    apply uncurry_fundefs_step_increases_size in H1.
    lia.
  Qed.

  Lemma uncurry_step_preserves_occurs_free_mut :
    let P := (fun e s m e1 s1 m1 =>
                used_vars e \subset s ->
                unique_bindings e ->
                occurs_free e <--> occurs_free e1) in
    let Q := (fun f s m f1 s1 m1 =>
                used_vars_fundefs f \subset s ->
                unique_bindings_fundefs f ->
                occurs_free_fundefs f <--> occurs_free_fundefs f1) in
    (forall e s m e1 s1 m1, uncurry_step e s m e1 s1 m1 -> P e s m e1 s1 m1) /\
    (forall f s m f1 s1 m1, uncurry_fundefs_step f s m f1 s1 m1 -> Q f s m f1 s1 m1).
  Proof with eauto with Ensembles_DB.
    Local Ltac ensemble_compat_simpl := match goal with
      [ _ : _ |- ?a :|: ?b \subset ?a :|: ?c ] => apply Included_Union_compat; eauto with Ensembles_DB
    | [ _ : _ |- ?a \\ ?b \subset ?a \\ ?c ] => apply Included_Setminus_compat; eauto with Ensembles_DB
    | [ _ : _ |- ?a :|: ?c \subset ?b :|: ?c ] => apply Included_Union_compat; eauto with Ensembles_DB
    | [ _ : _ |- ?a \\ ?c \subset ?b \\ ?c ] => apply Included_Setminus_compat; eauto with Ensembles_DB
    | [ _ : _ |- ?a :|: ?b <--> ?a :|: ?c ] => apply Same_set_Union_compat; eauto with Ensembles_DB
    | [ _ : _ |- ?a \\ ?b <--> ?a \\ ?c ] => apply Same_set_Setminus_compat; eauto with Ensembles_DB
    | [ _ : _ |- ?a :|: ?c <--> ?b :|: ?c ] => apply Same_set_Union_compat; eauto with Ensembles_DB
    | [ _ : _ |- ?a \\ ?c <--> ?b \\ ?c ] => apply Same_set_Setminus_compat; eauto with Ensembles_DB
    end.
    intros P Q.
    uncurry_induction_mut P Q IHstep IH; subst P; subst Q; simpl in *;
    try destruct arm;
    try (
      repeat normalize_occurs_free;
      repeat normalize_used_vars; intros Hused Huniq; inv Huniq;
      destruct IH as [HL HR]; eauto; [eapply Included_trans; [|eauto]; eauto with Ensembles_DB|];
      rewrite (conj HL HR : _ <--> _));
    try reflexivity.
    - (* Efun *)
      ensemble_compat_simpl; split.
      + intros a Ha; inv Ha; split; auto; intros contra.
        assert (~ In var s a). {
          eapply uncurry_fundefs_step_unique_names; eauto.
          eapply Included_trans; [|eauto]...
        }
        contradiction H4; apply Hused; right; now right.
      + ensemble_compat_simpl.
        intros a Ha; eapply uncurry_fundefs_step_preserves_names; eauto.
    - (* Fcons e *)
      split.
      + ensemble_compat_simpl.
        intros a Ha; inv Ha.
        repeat rewrite Union_demorgan in H0; destruct H0 as [Hf6 [Hargs Hfds]].
        split; auto; intros contra; inv contra; inv H0; auto.
        assert (~ In var s a). {
          eapply uncurry_fundefs_step_unique_names; eauto.
          eapply Included_trans; [|eauto]...
        }
        contradiction H0; apply Hused; left; right; now right.
      + repeat ensemble_compat_simpl; intros a Ha; eapply uncurry_fundefs_step_preserves_names; eauto.
    - (* Fcons cps uncurry *)
      intros Hused Huniq.
      do 2 rewrite occurs_free_fundefs_Fcons.
      do 2 rewrite occurs_free_Efun; simpl; repeat rewrite Union_Empty_set_neut_r.
      rewrite occurs_free_Eapp.
      assert (Hrw : FromList [g] :|: [set k] \\ [set g] <--> [set k]). {
        split; intros a Ha; inv Ha.
        - inv H8. inv H10. now contradiction H9. inv H8. auto.
        - constructor; [now right|].
          intros contra; inv contra.
          inv Huniq.
          inv H15; contradiction (H8 a).
          split; [|now left].
          constructor; constructor; now left.
      }
      rewrite Hrw.
      repeat normalize_occurs_free.
      repeat (rewrite Union_Empty_set_neut_r + rewrite Setminus_Empty_set_abs_r).
      assert (Hrw1 :
        occurs_free ge \\ (g |: FromList gv) :|: [set k] \\
          (f9 |: (FromList (k :: fv) :|: name_in_fundefs fds)) <-->
        occurs_free ge \\ (f9 |: FromList gv :|: FromList fv :|: name_in_fundefs fds)). {
        rewrite Setminus_Union_Included; [|rewrite FromList_cons; eauto with Ensembles_DB].
        repeat rewrite <- Setminus_Union.
        rewrite <- Included_Setminus_Disjoint with (s2 := [set g]).
        repeat rewrite Setminus_Union.
        rewrite Union_assoc, FromList_cons.
        rewrite Union_commut.
        repeat rewrite <- Setminus_Union.
        rewrite <- Included_Setminus_Disjoint with (s2 := [set k]).
        repeat rewrite Setminus_Union.
        repeat rewrite Union_assoc.
        rewrite Union_commut.
        rewrite Union_commut with (s2 := FromList gv).
        repeat rewrite Union_assoc...
        apply Disjoint_Singleton_r; intros contra.
        rewrite not_occurs_in_exp_iff_used_vars in H1; contradiction H1; now right.
        apply Disjoint_Singleton_r; intros contra.
        rewrite not_occurs_in_exp_iff_used_vars in H0; contradiction H0; now right.
      }
      rewrite Hrw1.
      assert (Hrw2 : occurs_free_fundefs fds \\ [set f10] <--> occurs_free_fundefs fds). {
        split...
        intros a Ha; constructor...
        intros contra; inv contra.
        contradiction H6; do 2 left; apply Hused.
        normalize_used_vars; right; now right.
      }
      rewrite Hrw2.
      assert (Hrw3 :
        occurs_free ge \\ (f10 |: (FromList (gv ++ fv) :|: name_in_fundefs fds)) <-->
        occurs_free ge \\ (FromList gv :|: FromList fv :|: name_in_fundefs fds)). {
        rewrite Union_commut.
        rewrite <- Setminus_Union.
        symmetry.
        rewrite FromList_app.
        apply Included_Setminus_Disjoint.
        constructor; intros a contra; inv contra; inv H9.
        contradiction H6; do 2 left; apply Hused.
        inv H8.
        normalize_used_vars; left; right.
        normalize_used_vars; left; normalize_used_vars.
        left; right; now right.
      }
      rewrite Hrw3.
      assert (Hrw4 : FromList (gv1 ++ fv1) :|: [set f10] \\ (g |: FromList gv1) <-->
                              f10 |: FromList fv1). {
        rewrite Setminus_Union_distr.
        assert (Hrw5 : [set f10] \\ (g |: FromList gv1) <--> [set f10]). {
          symmetry.
          apply Included_Setminus_Disjoint.
          constructor; intros a contra; inv contra; inv H8.
          inv H9; [inv H8|]; contradiction H6.
          do 2 left; apply Hused; normalize_used_vars; left; right.
          normalize_used_vars; left; normalize_used_vars; now do 3 left.
          left; now right.
        }
        rewrite Hrw5.
        rewrite Union_commut; apply Same_set_Union_compat...
        rewrite FromList_app, Setminus_Union_distr.
        assert (Hrw6 : FromList gv1 \\ (g |: FromList gv1) <--> Empty_set _).
        apply Setminus_Included_Empty_set...
        rewrite Hrw6; rewrite Union_Empty_set_neut_l.
        symmetry.
        apply Included_Setminus_Disjoint.
        constructor; intros a contra; inv contra.
        destruct H4 as [HL HR].
        inv H9; [inv H4|].
        inv HL; contradiction (H4 a).
        split; auto.
        left; apply Hused; normalize_used_vars; left; right.
        normalize_used_vars; left; normalize_used_vars; now do 3 left.
        inv HL; contradiction (H9 a); split; auto.
      }
      rewrite Hrw4.
      assert (Hrw5 :
        (f10 |: FromList fv1 :|: [set k]) \\
          (f9 |: (FromList (k :: fv1) :|: (f10 |: name_in_fundefs fds))) <-->
          Empty_set _). {
        apply Setminus_Included_Empty_set.
        intros a Ha; inv Ha; inv H8; [inv H9| |].
        do 2 right; now left.
        right; left; now right.
        right; left; now left.
      }
      rewrite Hrw5; rewrite Union_Empty_set_neut_l.
      rewrite Setminus_Union_distr.
      rewrite Setminus_Union.
      rewrite Union_commut with (s2 := [set f9]).
      now repeat rewrite Union_assoc.
    - (* anf uncurry *)
      repeat normalize_used_vars.
      apply not_occurs_in_exp_iff_used_vars in H0.
      unfold used_vars, used_vars_fundefs in *.
      repeat (normalize_occurs_free || normalize_bound_var || normalize_sets).
      intros Hused Huniq.
      repeat match goal with
      | H : fresh_copies _ _ |- _ => destruct H
      | H : ?S1 :|: ?S2 \subset ?S3 |- _ => apply Union_Included_lr in H; destruct H
      | H : unique_bindings (_ _) |- _ => inv H
      | H : unique_bindings_fundefs (_ _) |- _ => inv H
      | H : ~ In _ (_ :|: _) _ |- _ => rewrite Union_demorgan in H; destruct H
      end.
      change (~ bound_var ?e ?x) with (~ In _ (bound_var e) x) in *;
      change (~ bound_var_fundefs ?fds ?x) with (~ In _ (bound_var_fundefs fds) x) in *;
      repeat normalize_bound_var_in_ctx.
      repeat match goal with
      | H : ~ In _ (_ :|: _) _ |- _ => rewrite Union_demorgan in H; destruct H
      | H : Disjoint ?A (?S1 :|: ?S2) ?S3 |- _ =>
        assert (Disjoint A S1 S3) by (apply Disjoint_Union_l in H; apply H);
        apply Disjoint_Union_r in H
      | H : Disjoint ?A ?S1 (?S2 :|: ?S3) |- _ => apply Disjoint_sym in H
      end.
      repeat progress multimatch goal with
      | Hdis : Disjoint var s ?S2, Hsub : ?S1 \subset s |- _ =>
        match goal with
        | Hconc : Disjoint var S1 S2 |- _ => idtac
        | _ => assert (Disjoint var S1 S2) by (eapply Disjoint_Included_l; [apply Hsub|apply Hdis])
        end
      | Hdis : ~ In var s ?x, Hsub : ?S \subset s |- _ =>
        match goal with
        | Hconc : ~ In var S x |- _ => idtac
        | _ => assert (~ In var S x) by
              (let contra := fresh "contra" in intros contra;
               contradiction Hdis; apply Hsub, contra)
        end
      end.
      rewrite Ensemble_iff_In_iff; intros arbitrary.
      repeat progress (cbn; (rewrite Union_demorgan || rewrite In_or_Iff_Union || rewrite not_In_Setminus)).
      assert (True_neut_r : forall A, A /\ True <-> A) by tauto.
      assert (True_neut_l : forall A, True /\ A <-> A) by tauto.
      repeat rewrite identifiers.not_In_Empty_set.
      repeat (rewrite True_neut_l || rewrite True_neut_r).
      assert (Disjoint_Singleton : forall S x, Disjoint var [set x] S -> ~ In var S x). {
        intros S x [Hdis] Hin; contradiction (Hdis x); now constructor. }
      repeat multimatch goal with
      | H : Disjoint ?A [set ?x] ?S |- _ =>
        match goal with
        | Hdup : ~ In A S x |- _ => idtac
        | _ => assert (~ In A S x) by (apply Disjoint_Singleton in H; apply H)
        end
      end.
      split; intros Hin; decompose [and or] Hin; clear Hin; try tauto.
      + right; split; [|tauto].
        left; split; [tauto|].
        split; [|tauto].
        inversion 1; now subst.
      + right; split; [|tauto]; right; split; [tauto|].
        inversion 1; now subst.
      + left; split; [|tauto]; left; split; [tauto|].
        split; [|tauto].
        inversion 1; now subst.
  Qed.

  Lemma uncurry_step_preserves_occurs_free : forall e s m e1 s1 m1,
    used_vars e \subset s ->
    unique_bindings e ->
    uncurry_step e s m e1 s1 m1 -> occurs_free e <--> occurs_free e1.
  Proof with eauto with Ensembles_DB.
    destruct uncurry_step_preserves_occurs_free_mut. now eauto.
  Qed.

  Lemma Disjoint_Intersection {A} s1 s2 s3 :
    Included A s1 s2 ->
    Disjoint A (s3 :&: s2) s1 ->
    Disjoint A s3 s1.
  Proof.
    intros Hinc Hdis. inv Hdis.
    constructor.
    intros.
    specialize (H x).
    specialize (Intersection_Same_set s1 s2 Hinc) as H'.
    erewrite Intersection_commut in H'.
    erewrite <- Intersection_assoc in H.
    rewrite H' in H.
    auto.
  Qed.

  Lemma uncurry_step_preserves_disjoint : forall e s m e1 s1 m1,
    used_vars e \subset s ->
    unique_bindings e ->
    uncurry_step e s m e1 s1 m1 ->
    Disjoint _ (bound_var e) (occurs_free e) ->
    Disjoint _ (bound_var e1) (occurs_free e1).
  Proof with eauto with Ensembles_DB.
    intros.

    apply Union_Included_r in H as Hof_e.
    specialize (uncurry_step_maintains_bindings e s m e1 s1 m1 H1 H) as Hbind.

    rewrite <- Hbind in H2.

    apply (Disjoint_Intersection (occurs_free e) s (bound_var e1) Hof_e) in H2.
    specialize (uncurry_step_preserves_occurs_free e s m e1 s1 m1 H H0 H1) as Hof.
    rewrite -> Hof in H2.
    auto.
  Qed.

  Lemma app_ctx_uncurry_step_mut :
    (forall c, (fun c => forall e s m e1 s1 m1,
      used_vars (c |[ e ]|) \subset s ->
      uncurry_step e s m e1 s1 m1 ->
      uncurry_step (c |[ e ]|) s m (c |[ e1 ]|) s1 m1) c) /\
    (forall f, (fun f => forall e s m e1 s1 m1,
      used_vars_fundefs (f <[ e ]>) \subset s ->
      uncurry_step e s m e1 s1 m1 ->
      uncurry_fundefs_step (f <[ e ]>) s m (f <[ e1 ]>) s1 m1) f).
  Proof with eauto with Ensembles_DB.
    exp_fundefs_ctx_induction IHe IHf; simpl;
      try rename e into c;
      try intros arms e s m e1 s1 m1 Hused Hstep (* Huniq*);
      try intros e s m e1 s1 m1 Hused Hstep (* Huniq*);
      try assumption;
      try (
        constructor;
        repeat normalize_used_vars;
        ((apply IHe; auto) || (apply IHf; auto));
        eapply Included_trans; [|eauto]; eauto with Ensembles_DB).
    - rewrite used_vars_Eletapp...
    - induction l; simpl in *.
      + constructor; rewrite used_vars_Ecase_cons in Hused.
        apply IHe; auto.
        rewrite Union_commut in Hused.
        eapply Included_trans...
      + destruct a; constructor.
        rewrite used_vars_Ecase_cons in Hused.
        apply IHl; auto.
        eapply Included_trans...
  Qed.

  Corollary app_ctx_uncurry_step : forall c e s m e1 s1 m1,
      used_vars (c |[ e ]|) \subset s ->
      uncurry_step e s m e1 s1 m1 ->
      uncurry_step (c |[ e ]|) s m (c |[ e1 ]|) s1 m1.
  Proof. apply app_ctx_uncurry_step_mut. Qed.

  Corollary app_ctx_uncurry_step' : forall c e s m e1 s1 m1,
      used_vars (c |[ e ]|) \subset s ->
      uncurry_step e s m e1 s1 m1 ->
      uncurry_step (c |[ e ]|) s m (c |[ e1 ]|) s1 m1.
  Proof. apply app_ctx_uncurry_step_mut. Qed.

  Corollary app_ctx_uncurry_fundefs_step : forall f e s m e1 s1 m1,
      used_vars_fundefs (f <[ e ]>) \subset s ->
      uncurry_step e s m e1 s1 m1 ->
      uncurry_fundefs_step (f <[ e ]>) s m (f <[ e1 ]>) s1 m1.
  Proof. apply app_ctx_uncurry_step_mut. Qed.

  (* reflexive transitive closure *)
  Inductive uncurry_rel :
    nat ->
    exp -> Ensemble var -> localMap ->
    exp -> Ensemble var -> localMap ->
    Prop :=
  | uncurry_rel_refl : forall e s m, uncurry_rel 0 e s m e s m
  | uncurry_rel_trans : forall n e s m e1 s1 m1 e2 s2 m2,
        uncurry_step e s m e1 s1 m1 ->
        uncurry_rel n e1 s1 m1 e2 s2 m2 ->
        uncurry_rel (S n) e s m e2 s2 m2.

  Inductive uncurry_rel_fundefs :
    nat ->
    fundefs -> Ensemble var -> localMap ->
    fundefs -> Ensemble var -> localMap ->
    Prop :=
  | uncurry_rel_fundefs_refl : forall f s m, uncurry_rel_fundefs 0 f s m f s m
  | uncurry_rel_fundefs_trans : forall n f s m f1 s1 m1 f2 s2 m2,
        uncurry_fundefs_step f s m f1 s1 m1 ->
        uncurry_rel_fundefs n f1 s1 m1 f2 s2 m2 ->
        uncurry_rel_fundefs (S n) f s m f2 s2 m2.

  Hint Constructors uncurry_rel : core.
  Hint Constructors uncurry_rel_fundefs : core.

  Lemma uncurry_rel_Sn : forall n e s m e1 s1 m1,
    uncurry_rel (S n) e s m e1 s1 m1 -> exists e2 s2 m2,
    uncurry_rel n e s m e2 s2 m2 /\ uncurry_step e2 s2 m2 e1 s1 m1.
  Proof.
    induction n.
    - do 3 eexists; split; auto.
      inv H; now inv H2.
    - intros.
      inv H.
      apply IHn in H2.
      destruct H2 as [e3 [s3 [m3 [Hrel Hstep]]]].
      do 3 eexists; split; eauto.
  Qed.

  Lemma Sn_uncurry_rel : forall n e s m e1 s1 m1 e2 s2 m2,
    uncurry_rel n e s m e2 s2 m2 ->
    uncurry_step e2 s2 m2 e1 s1 m1 ->
    uncurry_rel (S n) e s m e1 s1 m1.
  Proof.
    induction 1; intros.
    - econstructor; eauto.
    - apply IHuncurry_rel in H1.
      econstructor; eauto.
  Qed.

  Lemma uncurry_rel_fundefs_Sn : forall n e s m e1 s1 m1,
    uncurry_rel_fundefs (S n) e s m e1 s1 m1 -> exists e2 s2 m2,
    uncurry_rel_fundefs n e s m e2 s2 m2 /\ uncurry_fundefs_step e2 s2 m2 e1 s1 m1.
  Proof.
    induction n.
    - do 3 eexists; split; auto.
      inv H; now inv H2.
    - intros.
      inv H.
      apply IHn in H2.
      destruct H2 as [e3 [s3 [m3 [Hrel Hstep]]]].
      do 3 eexists; split; eauto.
  Qed.

  Lemma Sn_uncurry_rel_fundefs : forall n e s m e1 s1 m1 e2 s2 m2,
    uncurry_rel_fundefs n e s m e2 s2 m2 ->
    uncurry_fundefs_step e2 s2 m2 e1 s1 m1 ->
    uncurry_rel_fundefs (S n) e s m e1 s1 m1.
  Proof.
    induction 1; intros.
    - econstructor; eauto.
    - apply IHuncurry_rel_fundefs in H1.
      econstructor; eauto.
  Qed.

  Lemma uncurry_rel_preserves_unique_bindings : forall n e s m e1 s1 m1,
    used_vars e \subset s ->
    unique_bindings e ->
    uncurry_rel n e s m e1 s1 m1 ->
    unique_bindings e1.
  Proof.
    induction n; [ inversion 3; subst; auto |].
    intros.
    inv H1.
    eapply IHn; [| | eassumption ].
    eapply uncurry_step_preserves_used_vars; eauto.
    eapply uncurry_step_preserves_unique_bindings; eauto.
  Qed.

  Lemma uncurry_rel_preserves_unique_bindings' : forall n e s m e1 s1 m1,
    used_vars e \subset s ->
    unique_bindings e ->
    uncurry_rel n e s m e1 s1 m1 ->
    unique_bindings e1.
  Proof.
    induction n; [ inversion 3; subst; auto |].
    intros.
    inv H1.
    eapply IHn; [| | eassumption ].
    eapply uncurry_step_preserves_used_vars; eauto.
    eapply uncurry_step_preserves_unique_bindings; eauto.
  Qed.

  Lemma uncurry_fundefs_rel_s_nondecreasing : forall n f s m f1 s1 m1,
    uncurry_rel_fundefs n f s m f1 s1 m1 -> s \subset s1.
  Proof.
    induction n; inversion 1; [ eauto with Ensembles_DB | subst].
    eapply Included_trans.
    eapply uncurry_fundefs_step_s_nondecreasing; eauto.
    eapply IHn; eauto.
  Qed.

  Lemma uncurry_rel_preserves_used_vars : forall n e s m e1 s1 m1,
    used_vars e \subset s ->
    uncurry_rel n e s m e1 s1 m1 ->
    used_vars e1 \subset s1.
  Proof.
    induction n; [ inversion 2; subst; auto |].
    intros.
    inv H0.
    eapply IHn; [| eassumption ].
    eapply uncurry_step_preserves_used_vars; eauto.
  Qed.

  Lemma uncurry_fundefs_rel_preserves_used_vars : forall n f s m f1 s1 m1,
    uncurry_rel_fundefs n f s m f1 s1 m1 ->
    used_vars_fundefs f \subset s ->
    used_vars_fundefs f1 \subset s1.
  Proof.
    induction n; inversion 1; [ eauto with Ensembles_DB | subst ]; intros.
    apply uncurry_fundefs_step_preserves_used_vars in H1; auto.
    eapply IHn; eauto.
  Qed.

  Lemma uncurry_rel_preserves_disjoint : forall n e s m e1 s1 m1,
      used_vars e \subset s ->
      unique_bindings e ->
      Disjoint _ (bound_var e) (occurs_free e) ->
      uncurry_rel n e s m e1 s1 m1 ->
      Disjoint _ (bound_var e1) (occurs_free e1).
  Proof.
    intros n e s m e1 s1 m1 Hused Huniq Hdis Hrel.
    revert Hused Huniq Hdis.
    induction Hrel; intros Hused Huniq Hdis; [ assumption |].
    apply IHHrel.
    - eapply uncurry_step_preserves_used_vars; eauto.
    - eapply uncurry_step_preserves_unique_bindings; eauto.
    - eapply uncurry_step_preserves_disjoint; eauto.
  Qed.

  Lemma uncurry_rel_preserves_occurs_free : forall n e s m e1 s1 m1,
      used_vars e \subset s ->
      unique_bindings e ->
      uncurry_rel n e s m e1 s1 m1 ->
      occurs_free e <--> occurs_free e1.
  Proof.
    intros n e s m e1 s1 m1 Hused Huniq Hrel.
    revert Hused Huniq.
    induction Hrel; intros Hused Huniq; [ reflexivity |].

    assert (Hof_step : occurs_free e <--> occurs_free e1)
      by (eapply uncurry_step_preserves_occurs_free; eauto).

    rewrite Hof_step.
    apply IHHrel.
    - eapply uncurry_step_preserves_used_vars; eauto.
    - eapply uncurry_step_preserves_unique_bindings; eauto.
  Qed.

  Lemma uncurry_rel_s_nondecreasing : forall n e s m e1 s1 m1,
    uncurry_rel n e s m e1 s1 m1 -> s \subset s1.
  Proof.
    induction n; inversion 1; [eauto with Ensembles_DB|subst].
    eapply Included_trans.
    eapply uncurry_step_s_nondecreasing; eauto.
    eapply IHn; eauto.
  Qed.

  Lemma uncurry_rel_compose : forall n1 n e s m e1 s1 m1 e2 s2 m2,
    uncurry_rel n e s m e1 s1 m1 ->
    uncurry_rel n1 e1 s1 m1 e2 s2 m2 ->
    uncurry_rel (n1 + n) e s m e2 s2 m2.
  Proof.
    induction n1; intros; [inv H0; auto|].
    apply uncurry_rel_Sn in H0.
    destruct H0 as [e3 [s3 [m3 [Hrel Hstep]]]].
    eapply Sn_uncurry_rel; eauto.
  Qed.

  Lemma uncurry_rel_fundefs_compose : forall n1 n e s m e1 s1 m1 e2 s2 m2,
    uncurry_rel_fundefs n e s m e1 s1 m1 ->
    uncurry_rel_fundefs n1 e1 s1 m1 e2 s2 m2 ->
    uncurry_rel_fundefs (n1 + n) e s m e2 s2 m2.
  Proof.
    induction n1; intros; [inv H0; auto|].
    apply uncurry_rel_fundefs_Sn in H0.
    destruct H0 as [e3 [s3 [m3 [Hrel Hstep]]]].
    eapply Sn_uncurry_rel_fundefs; eauto.
  Qed.

  Lemma uncurry_rel_Ecase_l : forall n v arms s m arms1 s1 m1 c e,
    uncurry_rel n (Ecase v arms) s m (Ecase v arms1) s1 m1 ->
    uncurry_rel n (Ecase v ((c, e) :: arms)) s m (Ecase v ((c, e) :: arms1)) s1 m1.
  Proof.
    induction n; intros.
    - now inv H.
    - inv H.
      inv H1.
      + econstructor.
        apply uncurry_case_arms.
        apply uncurry_case_expr; eauto.
        now apply IHn.
      + econstructor.
        do 2 apply uncurry_case_arms; eauto.
        apply IHn; eauto.
  Qed.

  Lemma uncurry_rel_fundefs_Efun : forall n f s m f1 s1 m1 e,
    uncurry_rel_fundefs n f s m f1 s1 m1 ->
    uncurry_rel n (Efun f e) s m (Efun f1 e) s1 m1.
  Proof.
    induction n; intros; inv H; auto.
    eapply IHn in H2.
    econstructor; eauto.
  Qed.

  Lemma uncurry_rel_fundefs_Fcons : forall n f' t v f s m f1 s1 m1 e,
    uncurry_rel_fundefs n f s m f1 s1 m1 ->
    uncurry_rel_fundefs n (Fcons f' t v e f) s m (Fcons f' t v e f1) s1 m1.
  Proof.
    induction n; intros; inv H; auto.
    eapply IHn in H2.
    econstructor; eauto.
  Qed.

  Lemma app_ctx_uncurry_rel : forall n c e s m e1 s1 m1,
    used_vars (c |[ e ]|) \subset s ->
    uncurry_rel n e s m e1 s1 m1 ->
    uncurry_rel n (c |[ e ]|) s m (c |[ e1 ]|) s1 m1.
  Proof.
    induction n; [inversion 2; subst; constructor|].
    intros c e s m e1 s1 m1 Hused Hrel.
    inv Hrel.
    econstructor.
    apply app_ctx_uncurry_step; eauto.
    apply IHn; auto.
    eapply uncurry_step_preserves_used_vars.
    apply app_ctx_uncurry_step. all: eauto.
  Qed.

  Lemma app_ctx_uncurry_rel_fundefs : forall n f e s m e1 s1 m1,
    used_vars_fundefs (f <[ e ]>) \subset s ->
    uncurry_rel n e s m e1 s1 m1 ->
    uncurry_rel_fundefs n (f <[ e ]>) s m (f <[ e1 ]>) s1 m1.
  Proof.
    induction n; [inversion 2; subst; constructor|].
    intros f e s m e1 s1 m1 Hused Hrel.
    inv Hrel.
    econstructor.
    apply app_ctx_uncurry_fundefs_step; eauto.
    apply IHn; auto.
    eapply uncurry_fundefs_step_preserves_used_vars.
    apply app_ctx_uncurry_fundefs_step. all: eauto.
  Qed.

  Variable (Hpost_idemp : inclusion _ (comp Post Post) Post).
  Variable (Hpost_idemp' : inclusion _ (comp PostG PostG) PostG).

  Lemma uncurry_rel_correct : forall n k e s m e1 s1 m1,
    unique_bindings e ->
    used_vars e \subset s ->
    uncurry_rel n e s m e1 s1 m1 ->
    ctx_preord_exp k e e1.
  Proof.
    intros n k e s m e1 s1 m1 Hub_e Huv_e Hrel.
    assert (Hub_e1 : unique_bindings e1)
      by (eapply uncurry_rel_preserves_unique_bindings; eauto).
    assert (Huv_e1 : used_vars e1 \subset s1)
      by (eapply uncurry_rel_preserves_used_vars; eauto).
    revert Hub_e Hub_e1 Huv_e Huv_e1 Hrel.
    revert n k e s m e1 s1 m1.
    induction n; intros; intros rho rho1 Henv; inv Hrel.
    now apply preord_exp_refl.
    assert (Hub_e2 : unique_bindings e2)
      by (eapply uncurry_step_preserves_unique_bindings; eauto).
    assert (Huv_e2 : used_vars e2 \subset s2)
      by (eapply uncurry_step_preserves_used_vars; eauto ).
    eapply preord_exp_post_monotonic. apply Hpost_idemp.
    eapply preord_exp_trans.
    - now constructor; try easy_post.
    - now apply Hpost_idemp'.
    - eapply uncurry_step_correct; try eauto.
    - intros; eapply IHn; try eauto.
      now apply preord_env_P_refl.
  Qed.

  Definition total {R W A} (m : compM R W A) := forall P, {{ P }} m {{ fun _ _ _ _ => True }}.

  Lemma ret_total {R W A} x : @total R W A (ret x).
  Proof. intros P. now apply return_triple. Qed.

  Lemma bind_total {R W A B} (m : compM R W A) (f : A -> compM R W B) :
    total m ->
    (forall x, total (f x)) ->
    total (bind m f).
  Proof. intros Hm Hf P; eapply bind_triple; [apply Hm|intros; apply Hf]. Qed.

  Hint Resolve ret_total : TotalDB.
  Hint Extern 1 (total (_ <- _ ;; _)) => (apply bind_total; [|let x := fresh "arbitrary" in intros x]) : TotalDB.

  Lemma get_triple' {R W} P :
    {{ P }} compM.get {{ fun (r : R) (w : W) (x : W) (w' : W) => x = w /\ w = w' }}.
  Proof. unfold triple; intros. simpl. eauto. Qed.

  Lemma put_triple' {R W} P x :
    {{ P }} compM.put x {{ fun (r : R) (w : W) (_ : unit) (w' : W) => x = w' }}.
  Proof. unfold triple; intros. simpl. eauto. Qed.

  Lemma get_total {R W} : total (get : compM R W W).
  Proof.
    unfold total; intros; eapply post_weakening; [|apply get_triple']; auto.
  Qed.

  Lemma put_total {R W} x : total (put x : compM R W unit).
  Proof.
    unfold total; intros; eapply post_weakening; [|apply put_triple']; auto.
  Qed.

  Hint Resolve get_total put_total : TotalDB.

  Lemma get_state_total {S} : total (state.get_state tt : state.compM' S).
  Proof. unfold state.get_state; auto with TotalDB. Qed.

  Lemma put_state_total {S} (s : S) : total (state.put_state s).
  Proof. unfold state.put_state; auto with TotalDB. Qed.

  Hint Resolve get_state_total put_state_total : TotalDB.

  Lemma already_uncurried_total x : total (uncurry.already_uncurried x).
  Proof.
    unfold uncurry.already_uncurried.
    apply bind_total; [auto with TotalDB|intros x'].
    destruct x' as [[[b aenv] lm] s].
    destruct (lm ! x) as [[] |]; apply ret_total.
  Qed.

  Lemma get_name_total {S} x s : total (@state.get_name S x s).
  Proof.
    unfold state.get_name.
    apply bind_total; [apply get_total|].
    destruct x0 as [[] st].
    apply bind_total; [apply put_total|apply ret_total].
  Qed.

  Lemma get_names_lst_total {S} xs s : total (@state.get_names_lst S xs s).
  Proof.
    induction xs; unfold state.get_names_lst, mapM; [apply ret_total|].
    apply bind_total; [apply get_name_total|intros x].
    apply bind_total; [apply IHxs|intros x0; apply ret_total].
  Qed.

  Lemma mark_as_uncurried_total x : total (mark_as_uncurried x).
  Proof.
    unfold mark_as_uncurried.
    apply bind_total; [apply get_state_total|intros [[[b aenv] lm] s]].
    apply put_state_total.
  Qed.

  Lemma click_total : total click.
  Proof.
    unfold click; apply bind_total; [apply get_state_total|intros [[[b aenv] lm] s]].
    apply put_state_total.
  Qed.

  Lemma markToInline_total xs v1 v2 : total (markToInline xs v1 v2).
  Proof.
    unfold markToInline.
    apply bind_total; [apply get_state_total|].
    intros [[[b aenv] lm] s]; apply put_state_total.
  Qed.

  Lemma get_ftag_total {S} n : total (@state.get_ftag S n).
  Proof.
    unfold state.get_ftag.
    apply bind_total; [apply get_total|].
    intros [[] s]; apply bind_total; [apply put_total|intros []; apply ret_total].
  Qed.

  Lemma get_fun_tag_total n : total (get_fun_tag n).
  Proof.
    unfold get_fun_tag; apply bind_total; [apply get_state_total|].
    intros [[[b aenv] lm] s].
    destruct (aenv ! (N.succ_pos n)); [apply ret_total|].
    apply bind_total; [apply get_ftag_total|intros x].
    apply bind_total; [apply put_state_total|intros x'].
    apply ret_total.
  Qed.

  Hint Resolve already_uncurried_total : TotalDB.
  Hint Resolve get_names_lst_total : TotalDB.
  Hint Resolve get_name_total : TotalDB.
  Hint Resolve mark_as_uncurried_total : TotalDB.
  Hint Resolve click_total : TotalDB.
  Hint Resolve markToInline_total : TotalDB.
  Hint Resolve get_ftag_total : TotalDB.
  Hint Resolve get_fun_tag_total : TotalDB.

  Fixpoint sizeof_exp e : nat :=
    match e with
    | Econstr _ _ ys e => 1 + length ys + sizeof_exp e
    | Ecase _ l =>
      1 + (fix sizeof_l l :=
              match l with
                [] => 0
              | (t, e) :: l => 1 + sizeof_exp e + sizeof_l l
              end) l
    | Eproj x _ _ y e => 1 + sizeof_exp e
    | Eletapp _ _ _ xs e => 1 + length xs + sizeof_exp e
    | Efun fds e => 1 + sizeof_fundefs fds + sizeof_exp e
    | Eapp _ _ ys => 1 + length ys
    | Eprim_val _ _ e => 1 + sizeof_exp e
    | Eprim _ _ ys e => 1 + length ys + sizeof_exp e
    | Ehalt _ => 1
    end
  with sizeof_fundefs f : nat :=
    match f with
    | Fcons f t v e fds => 1 + sizeof_exp e + sizeof_fundefs fds
    | Fnil => 0
    end.

  Definition sizeof (a : exp + fundefs) : nat :=
    match a with inl e => sizeof_exp e | inr f => sizeof_fundefs f end.

  Definition uncurry_stmt (P : exp -> Prop) (Q : fundefs -> Prop) a :=
    match a with
    | inl e => P e
    | inr fds => Q fds
    end.

  Lemma uncurry_total cps a :
    uncurry_stmt (fun e => total (uncurry_exp cps e)) (fun fds => total (uncurry_fundefs cps fds)) a.
  Proof.
    remember (sizeof a) as n; generalize dependent a.
    induction n as [n IHn] using lt_wf_ind; intros a Hsize; subst n.
    destruct a as [e|fds]; cbn.
    Local Ltac solve_total IHn :=
      match goal with
      | |- total (ret ?x) => apply (ret_total x)
      | |- total (uncurry_exp _ ?e) =>
        exact (IHn (sizeof (inl e)) ltac:(cbn; lia) (inl e) eq_refl)
      | |- total (uncurry_fundefs ?b ?e) =>
        exact (IHn (sizeof (inr e)) ltac:(cbn; lia) (inr e) eq_refl)
      | |- total (_ <- _ ;; _) => apply bind_total; try solve_total IHn
      | |- forall _, _ => let x := fresh "arbitrary" in intros x; try solve_total IHn
      | |- total (match ?e with _ => _ end) => destruct e; try solve_total IHn
      | |- total (if ?e then _ else _) => destruct e; try solve_total IHn
      | |- _ => try solve [auto with TotalDB]
      end.
    - destruct e; unfold uncurry_exp; fold uncurry_exp; fold uncurry_fundefs; solve_total IHn.
      induction l as [| [c e] ces IHces]; solve_total IHn.
      apply IHces; intros.
      apply (IHn m); cbn in *; lia.
    - destruct fds; unfold uncurry_fundefs; fold uncurry_fundefs; fold uncurry_exp; solve_total IHn.
  Qed.

  Definition uncurry_exp_total cps e : total (uncurry_exp cps e) := uncurry_total cps (inl e).
  Definition uncurry_fundefs_total cps fds : total (uncurry_fundefs cps fds) := uncurry_total cps (inr fds).

  Definition stateType' : Type := state.comp_data * stateType.
  Definition next_free (s : stateType') : var :=
    match s with (cdata, _) => cdata.(state.next_var) end.
  Definition from_maxvar v := fun a => (a < v)%positive.
  Definition from_fresh st := from_maxvar (next_free st).
  Definition already_uncurried (st : stateType') : localMap :=
    match st with (_, (_, _, lm, _)) => lm end.

  (* This identity is useful for the Ecase case -- see below *)
  Lemma st_eq_Ecase (m1 : uncurryM (list (ctor_tag * exp))) (x : var) y :
    st_eq
      (bind (ys <- m1 ;; ret (y :: ys)) (fun ys' => ret (Ecase x ys')))
      (e <- (ys <- m1 ;;
             ret (Ecase x ys)) ;;
       match e with
         | Ecase x ys =>
           ret (Ecase x (y :: ys))
         | _ => ret e
       end).
  Proof.
    repeat rewrite pbind_bind.
    do 2 rewrite (assoc m1).
    apply bind_Proper_r; auto; intros x0.
    now do 2 rewrite left_id.
  Qed.

  Lemma already_uncurried_triple : forall s f,
    {{fun _ s' => s = s'}} uncurry.already_uncurried f
    {{fun _ s a s1 => s = s1 /\
        a = match M.get f (already_uncurried s) with
              Some true => true
            | _ => false
            end }}.
  Proof.
    intros; unfold uncurry.already_uncurried, state.get_state.
    repeat rewrite pbind_bind.
    setoid_rewrite (assoc compM.get).
    eapply bind_triple; [apply get_triple'|intros [cdata st] st'].
    setoid_rewrite left_id; cbn; destruct st as [[[b aenv] lm] s'].
    destruct (lm ! f) as [[|] |] eqn:Hget; apply return_triple; intros.
    - destruct H; subst st' w; cbn; now rewrite Hget.
    - destruct H; subst st' w; cbn; now rewrite Hget.
    - destruct H; subst st' w; cbn; now rewrite Hget.
  Qed.

  Opaque bind ret.

  Lemma next_free_not_In_from_fresh : forall s, ~ In _ (from_fresh s) (next_free s).
  Proof.
    intros s.
    destruct s as [cdata [[[b aenv] lm] s]]; cbn.
    unfold from_fresh, In; cbn.
    apply Pos.lt_irrefl.
  Qed.

  Lemma get_name_triple : forall s f str,
    {{fun _ s' => s = s'}} state.get_name f str
    {{fun _ s a s1 =>
        from_fresh s1 <--> a |: from_fresh s /\
        already_uncurried s1 = already_uncurried s /\
        a = next_free s}}.
  Proof.
    intros; eapply bind_triple; [apply get_triple'|intros s0 s0'; cbn].
    apply pre_eq_state_l; intros [] s0'' [Hs0' Hs0'']; subst s0' s0''.
    destruct s0 as [[] st0]; cbn.
    eapply bind_triple; [apply put_triple'|intros [] s1].
    apply pre_eq_state_l; intros [] w Hw; subst w.
    apply return_triple; intros [] w [_ Hw]; subst w; unfold from_fresh; cbn.
    destruct st0 as [[[b aenv] lm] s'].
    split; [|easy].
    split; unfold Included, In; intros.
    - unfold from_maxvar in H.
      assert (Hle : (x < next_var \/ x = next_var)%positive) by lia.
      destruct Hle; [right; now unfold In, from_maxvar|left; unfold In; now subst].
    - inv H; [inv H0|].
      all: unfold from_maxvar; rewrite <- Pplus_one_succ_r; rewrite Pos.lt_succ_r; rewrite Pos.le_lteq; auto.
  Qed.

  Lemma get_names_lst_triple : forall l s str,
    {{fun _ s' => s = s'}} state.get_names_lst l str
    {{fun _ s l1 s1 =>
        from_fresh s1 <--> from_fresh s :|: FromList l1 /\
        already_uncurried s1 = already_uncurried s /\
        fresh_copies (from_fresh s) l1 /\
        List.length l = List.length l1}}.
  Proof with eauto with Ensembles_DB.
    unfold state.get_names_lst.
    induction l.
    - intros s str; unfold mapM.
      apply return_triple.
      intros _ s' Hs'; split; [|split]; auto; [|split]; auto.
      + now repeat normalize_sets.
      + unfold fresh_copies; split; [|constructor].
        rewrite FromList_nil.
        apply Disjoint_Empty_set_r.
    - intros s str; cbn.
      eapply bind_triple; [apply get_name_triple|intros x' s0].
      apply pre_eq_state_l. intros [] s0' [Hs0' [Hunc_s0' Hx']].
      eapply pre_strenghtening.
      2: eapply bind_triple.
      2: eapply pre_post_copy.
      2: apply IHl.
      1: cbn; intros ? ? [? ?]; eassumption.
      cbn; intros xs' s1.
      apply pre_eq_state_l.
      intros [] s1' [Hs0'' [Hs1' [Hunc_s1' [Hfresh Hlen]]]].
      apply return_triple; intros [] s1'' [_ Hs1'']; subst s1'' s0'.
      split; [|split; [|split; [unfold fresh_copies; split|]]].
      + rewrite FromList_cons.
        rewrite Hs1', Hs0'...
      + congruence.
      + constructor.
        intros x contra; inv contra.
        inv H0.
        * unfold from_fresh, next_free, In in H.
          destruct s0 as [[] ?]; cbn in H.
          unfold from_maxvar in H; lia.
        * destruct Hfresh as [Hfresh Hdup].
          destruct Hfresh as [Hfresh].
          contradiction (Hfresh x); split.
          -- assert (Hsub : from_fresh s0 \subset from_fresh s1).
             { eapply Union_Included_l.
               rewrite Union_commut.
               now rewrite <- Hs0'. }
             now apply Hsub.
          -- assumption.
      + destruct Hfresh as [Hfresh Hdup].
        constructor; auto.
        intros Hin.
        destruct Hfresh as [Hfresh].
        contradiction (Hfresh x'); split.
        * rewrite Hs0'; now left.
        * assumption.
      + cbn; congruence.
  Qed.

  Lemma mark_as_uncurried_triple : forall v,
    {{fun _ s' => True}}
      uncurry.mark_as_uncurried v
    {{fun _ s _ s1 =>
        from_fresh s1 = from_fresh s /\
        already_uncurried s1 = M.set v true (already_uncurried s) }}.
  Proof.
    intros; unfold uncurry.mark_as_uncurried, state.get_state.
    repeat rewrite pbind_bind.
    setoid_rewrite (assoc compM.get).
    eapply bind_triple; [apply get_triple'|].
    intros s s'.
    apply pre_eq_state_l. intros [] s'' [Hs' Hs'']; subst s' s''.
    destruct s as [cdata [[[b aenv] lm] s]]; cbn.
    rewrite left_id; unfold state.put_state.
    eapply bind_triple; [apply pre_post_copy, get_triple'|]; cbn.
    intros s' s''; apply pre_eq_state_l.
    intros [] s''' [[_ Htup] [Hs'' Hs''']]; subst s' s'' s'''.
    eapply post_weakening; [|apply put_triple']; cbn.
    intros [] w [] w' [? Hw] Hw'; subst w w'; unfold from_fresh; now cbn.
  Qed.

  Lemma click_triple : forall s,
    {{fun _ s' => s = s'}}
      uncurry.click
    {{fun _ s _ s1 =>
        from_fresh s1 = from_fresh s /\
        already_uncurried s1 = already_uncurried s }}.
  Proof.
    intros; unfold uncurry.click, state.get_state.
    repeat rewrite pbind_bind; setoid_rewrite assoc.
    apply pre_eq_state_l; intros [] w Hw; subst w.
    eapply bind_triple; [apply pre_post_copy; apply get_triple'|cbn].
    intros [cdata [[[b aenv] lm] s']] w.
    apply pre_eq_state_l; intros [] w' [[_ Hs] [Hw Hw']]; subst s w w'.
    rewrite left_id; cbn; unfold state.put_state.
    eapply bind_triple; [apply pre_post_copy; apply get_triple'|cbn].
    intros x w; apply pre_eq_state_l.
    intros [] w0 [[_ Hw] [Hx Hw0]]; subst x w w0.
    eapply post_weakening; [|apply put_triple']; cbn.
    intros [] w _ w' [_ Hw] Hw'; subst w w'; now cbn.
  Qed.

  Lemma markToInline_triple : forall s n f k,
    {{fun _ s' => s = s'}}
      uncurry.markToInline n f k
    {{fun _ s _ s1 =>
        from_fresh s1 = from_fresh s /\
        already_uncurried s1 = already_uncurried s }}.
  Proof.
    intros; unfold markToInline, state.get_state.
    repeat rewrite pbind_bind; setoid_rewrite assoc.
    apply pre_eq_state_l; intros [] w Hw; subst w.
    eapply bind_triple; [apply pre_post_copy; apply get_triple'|cbn].
    intros [cdata [[[b aenv] lm] s']] w.
    apply pre_eq_state_l; intros [] w' [[_ Hs] [Hw Hw']]; subst s w w'; cbn.
    rewrite left_id; unfold state.put_state.
    eapply bind_triple; [apply pre_post_copy; apply get_triple'|cbn].
    intros x w; apply pre_eq_state_l.
    intros [] w0 [[_ Hw] [Hx Hw0]]; subst x w w0.
    eapply post_weakening; [|apply put_triple']; cbn.
    intros [] w _ w' [_ Hw] Hw'; subst w w'; now cbn.
  Qed.

  Lemma get_fun_tag_triple : forall s n,
    {{fun _ s' => s = s'}}
      uncurry.get_fun_tag n
    {{fun _ s _ s1 =>
        from_fresh s1 = from_fresh s /\
        already_uncurried s1 = already_uncurried s }}.
  Proof.
    intros; unfold uncurry.get_fun_tag, state.get_state.
    repeat rewrite pbind_bind; setoid_rewrite assoc.
    apply pre_eq_state_l; intros [] w Hw; subst w.
    eapply bind_triple; [apply pre_post_copy; apply get_triple'|cbn].
    intros [cdata [[[b aenv] lm] s']] w.
    apply pre_eq_state_l; intros [] w' [[_ Hs] [Hw Hw']]; subst s w w'; cbn.
    rewrite left_id; unfold state.put_state.
    destruct (aenv ! (N.succ_pos n)).
    - apply return_triple.
      intros _ w [_ Hw]; subst w; split; auto.
    - unfold state.get_ftag; repeat rewrite pbind_bind; setoid_rewrite assoc.
      eapply bind_triple; [apply pre_post_copy; apply get_triple'|cbn].
      intros x w; apply pre_eq_state_l; intros [] w0 [[_ Hw] [Hx Hw0]]; subst x w w0.
      destruct cdata; cbn.
      repeat rewrite pbind_bind; setoid_rewrite assoc.
      eapply bind_triple; [apply put_triple'|cbn].
      intros _ _; apply pre_eq_state_l; intros [] w Hw; subst w.
      rewrite left_id; repeat rewrite pbind_bind; setoid_rewrite assoc.
      eapply bind_triple; [apply pre_post_copy; apply get_triple'|cbn].
      intros x w; apply pre_eq_state_l; intros [] w' [[_ Hw] [Hx Hw']]; subst x w w'.
      eapply bind_triple; [apply put_triple'|cbn]; intros _ _; apply pre_eq_state_l.
      intros [] w Hw; subst w.
      apply return_triple; intros [] w [_ Hw]; now subst w.
  Qed.

  Lemma uncurry_step_subst_mut :
    let P := (fun e s m e1 s1 m1 => forall e' s' m' e1' s1' m1',
      e = e' -> s <--> s' -> m = m' -> e1 = e1' -> s1 <--> s1' -> m1 = m1' ->
      uncurry_step e' s' m' e1' s1' m1') in
    let Q := (fun f s m f1 s1 m1 => forall f' s' m' f1' s1' m1',
      f = f' -> s <--> s' -> m = m' -> f1 = f1' -> s1 <--> s1' -> m1 = m1' ->
      uncurry_fundefs_step f' s' m' f1' s1' m1') in
    (forall e s m e1 s1 m1, uncurry_step e s m e1 s1 m1 -> P e s m e1 s1 m1) /\
    (forall f s m f1 s1 m1, uncurry_fundefs_step f s m f1 s1 m1 -> Q f s m f1 s1 m1).
  Proof with eauto with Ensembles_DB.
    intros P Q.
    uncurry_induction_mut P Q IHstep IH; subst P; subst Q; simpl in *; intros; try solve
    [destruct e'; destruct e1'; try congruence; inv H; inv H2; constructor; apply IH; auto
    |destruct f'; destruct f1'; try congruence; inv H; inv H2; constructor; apply IH; auto].
    - destruct f'; destruct f1'; try congruence.
      inv H8; inv H11.
      constructor; unfold fresh_copies in *; destruct H2, H4; try split; auto;
        try rewrite <- H9; try rewrite H12; try rewrite H7...
      rewrite <- H12.
      rewrite H7...
      rewrite <- H7; rewrite H12...
    - destruct f'; destruct f1'; try congruence.
      inv H7; inv H10.
      constructor; auto; unfold fresh_copies in *.
      + now rewrite <- H8.
      + now rewrite <- H8.
      + now rewrite <- H8.
      + now rewrite <- H8, <- H11.
  Qed.

  Corollary uncurry_fundefs_step_subst : forall f s m f1 s1 m1 f' s' m' f1' s1' m1',
    uncurry_fundefs_step f s m f1 s1 m1 ->
    f = f' -> s <--> s' -> m = m' -> f1 = f1' -> s1 <--> s1' -> m1 = m1' ->
    uncurry_fundefs_step f' s' m' f1' s1' m1'.
  Proof. intros; eapply uncurry_step_subst_mut; eauto. Qed.

  Corollary uncurry_step_subst : forall e s m e1 s1 m1 e' s' m' e1' s1' m1',
    uncurry_step e s m e1 s1 m1 ->
    e = e' -> s <--> s' -> m = m' -> e1 = e1' -> s1 <--> s1' -> m1 = m1' ->
    uncurry_step e' s' m' e1' s1' m1'.
  Proof. intros; eapply uncurry_step_subst_mut; eauto. Qed.

  Lemma uncurry_rel_case : forall n v l s m e s1 m1,
      uncurry_rel n (Ecase v l) s m e s1 m1 -> exists l', e = Ecase v l'.
  Proof.
    induction n; intros.
    - inv H; eauto.
    - inv H; inv H1; now apply IHn in H2.
  Qed.

  Lemma from_fresh_fst_eq s s' :
    fst s = fst s' ->
    from_fresh s <--> from_fresh s'.
  Proof. destruct s, s'; cbn; now inversion 1. Qed.

  Lemma uncurry_corresp_mut a :
    let P e := forall b,
      {{ fun _ st => unique_bindings e /\ used_vars e \subset from_fresh st }}
        (uncurry_exp b e)
      {{ fun _ st e1 st1 => exists n,
           uncurry_rel n
                       e (from_fresh st) (already_uncurried st)
                       e1 (from_fresh st1) (already_uncurried st1)
      }} in
    let Q f := forall b,
      {{ fun _ st => unique_bindings_fundefs f /\ used_vars_fundefs f \subset from_fresh st }}
        (uncurry_fundefs b f)
      {{ fun _ st f1 st1 => exists n,
           uncurry_rel_fundefs n
                               f (from_fresh st) (already_uncurried st)
                               f1 (from_fresh st1) (already_uncurried st1)
      }} in
    uncurry_stmt P Q a.
  Proof with eauto with Ensembles_DB.
    intros P Q.
    remember (sizeof a) as n; generalize dependent a.
    induction n as [n IHn] using lt_wf_ind; intros [e|f] Hsize; subst n; cbn.
    - destruct e; unfold P; intros b.
      + eapply pre_eq_state_lr; intros [] st [Huniq Hused].
        unfold uncurry_exp; fold uncurry_exp.
        eapply bind_triple.
        Ltac use_IH IHn :=
          match goal with
          | |- {{ _ }} uncurry_exp ?b ?e {{ _ }} =>
            apply (IHn (sizeof (inl e)) ltac:(cbn; lia) (inl e) eq_refl b)
          | |- {{ _ }} uncurry_fundefs ?b ?fds {{ _ }} =>
            apply (IHn (sizeof (inr fds)) ltac:(cbn; lia) (inr fds) eq_refl b)
          end.
        eapply pre_strenghtening; [|use_IH IHn].
        { intros [] st' [_ Hst']; subst st'.
          split; [now inv Huniq|].
          eapply Included_trans; [|apply Hused].
          rewrite used_vars_Econstr... }
        intros e1 st1; apply return_triple.
        intros [] st2 [n Hrel] [_ Hst]; subst st1; rename st2 into st1.
        assert (from_fresh st \subset from_fresh st1) by (eapply uncurry_rel_s_nondecreasing; eauto).
        destruct n; inv Hrel.
        exists 0; constructor.
        exists (S n); econstructor.
        constructor; eauto.
        apply app_ctx_uncurry_rel with (c := Econstr_c v c l Hole_c).
        eapply uncurry_step_preserves_used_vars; eauto.
        apply app_ctx_uncurry_step with (c := Econstr_c v c l Hole_c). all: eauto.
      + induction l as [| [c e] ces IHces].
        * (* Ecase [] *)
          eapply pre_eq_state_lr; intros [] st [Huniq Hused].
          unfold uncurry_exp; fold uncurry_exp.
          repeat rewrite pbind_bind; setoid_rewrite left_id.
          apply return_triple; auto.
          intros [] w [_ Hw] _; subst w.
          exists 0; constructor.
        * (* Ecase :: *)
          eapply pre_eq_state_lr; intros [] st [Huniq Hused].
          unfold uncurry_exp; fold uncurry_exp.
          Transparent bind. setoid_rewrite assoc. Opaque bind.
          eapply bind_triple'.
          rewrite pre_post_copy.
          eapply pre_strenghtening; [|use_IH IHn].
          intros [] st' [_ Hst']; subst st'; split; [now inv Huniq|].
          eapply Included_trans; eauto; rewrite used_vars_Ecase_cons...
          intros e' st'.
          setoid_rewrite st_eq_Ecase.
          change (ys <- _ ces;; ret (Ecase v ys)) with (uncurry_exp b (Ecase v ces)).
          eapply bind_triple'.
          rewrite pre_post_copy.
          eapply pre_strenghtening; [|use_IH IHn].
          intros [] st0' [[_ Hst'] [n Hrel]]; subst st'; split; [now inv Huniq|].
          apply Included_trans with (s2 := from_fresh st).
          eapply Included_trans; eauto; rewrite used_vars_Ecase_cons...
          eapply uncurry_rel_s_nondecreasing; eauto.
          intros c' st0'; apply pre_eq_state_lr.
          intros [] st1 [[[_ Hst0] [n_c Hc]] [n_ces Hces]]; subst.
          pose (Hces' := Hces).
          apply uncurry_rel_case in Hces'; destruct Hces' as [l' Hces']; subst.
          eapply return_triple.
          intros [] st1' [_ Hst1] _ _; subst st1'.
          exists (n_ces + n_c).
          eapply uncurry_rel_compose.
          eapply app_ctx_uncurry_rel with (c := Ecase_c v [] c Hole_c ces); eauto.
          now apply uncurry_rel_Ecase_l.
      + (* Eproj *)
        unfold uncurry_exp; fold uncurry_exp.
        eapply pre_eq_state_lr; intros [] st [Huniq Hused].
        eapply bind_triple.
        eapply pre_strenghtening; [|use_IH IHn].
        simpl; intros [] s [_ Hs]; subst s.
        split; [now inv Huniq|].
        eapply Included_trans; [|apply Hused].
        rewrite used_vars_Eproj...
        intros e1 st'; apply return_triple.
        intros [] st1 [n1 Hrel] [_ Hst]; subst st'.
        assert (from_fresh st \subset from_fresh st1) by (eapply uncurry_rel_s_nondecreasing; eauto).
        destruct n1; inv Hrel.
        exists 0; constructor.
        exists (S n1); econstructor.
        constructor; eauto.
        apply app_ctx_uncurry_rel with (c := Eproj_c v c n v0 Hole_c).
        eapply uncurry_step_preserves_used_vars; eauto.
        apply app_ctx_uncurry_step with (c := Eproj_c v c n v0 Hole_c). all: eauto.
      + (* Eletapp *)
        unfold uncurry_exp; fold uncurry_exp.
        eapply pre_eq_state_lr; intros [] st [Huniq Hused].
        eapply bind_triple. eapply pre_strenghtening; [|use_IH IHn].
        cbn; intros [] s [_ Hs]; subst s.
        { split; [now inv Huniq|].
          eapply Included_trans; [|apply Hused]; rewrite used_vars_Eletapp... }
        cbn; intros e' st0; apply return_triple.
        intros [] st1 [n1 Hrel] [_ Hst]; subst st0.
        assert (from_fresh st \subset from_fresh st1) by (eapply uncurry_rel_s_nondecreasing; eauto).
        destruct n1; inv Hrel.
        exists 0; constructor.
        exists (S n1); econstructor.
        constructor; eauto.
        apply app_ctx_uncurry_rel with (c := Eletapp_c v v0 f l Hole_c).
        eapply uncurry_step_preserves_used_vars; eauto.
        apply app_ctx_uncurry_step with (c := Eletapp_c v v0 f l Hole_c). all: eauto.
      + (* Efun *)
        eapply pre_eq_state_lr; intros [] st [Huniq Hused].
        unfold uncurry_exp; fold uncurry_exp; fold uncurry_fundefs.
        eapply bind_triple'.
        rewrite pre_post_copy.
        eapply pre_strenghtening; [|use_IH IHn].
        intros [] i [_ Hi]; subst i.
        split; [now inv Huniq|].
        eapply Included_trans; eauto.
        rewrite used_vars_Efun...
        intros f2' st0.
        eapply pre_eq_state_lr.
        intros [] s [[_ Hst0] [n_f2 Hf2]]; subst.
        eapply bind_triple'.
        rewrite pre_post_copy.
        eapply pre_strenghtening; [|use_IH IHn].
        intros [] i [_ Hi]; subst i.
        split; [now inv Huniq|].
        eapply Included_trans with (s2 := from_fresh st0).
        eapply Included_trans; eauto.
        rewrite used_vars_Efun...
        eapply uncurry_fundefs_rel_s_nondecreasing; eauto.
        intros e' st1.
        apply pre_eq_state_lr.
        intros [] s0 [[_ Hst1] [n_e He]]; subst.
        eapply return_triple.
        intros [] s0' [_ Hs0] _ _; subst s0'.
        exists (n_e + n_f2).
        eapply uncurry_rel_compose.
        eapply uncurry_rel_fundefs_Efun; eauto.
        eapply app_ctx_uncurry_rel with (c := Efun1_c f2' Hole_c); simpl; eauto.
        rewrite used_vars_Efun.
        apply Union_Included.
        eapply uncurry_fundefs_rel_preserves_used_vars; eauto.
        eapply Included_trans; eauto.
        rewrite used_vars_Efun...
        eapply Included_trans with (s2 := from_fresh st0).
        eapply Included_trans; eauto.
        rewrite used_vars_Efun...
        eapply uncurry_fundefs_rel_s_nondecreasing; eauto.
      + (* Eapp *)
        apply return_triple; intros.
        exists 0; constructor.
      + (* EPrim_val *)
        simpl.
        eapply pre_eq_state_lr; intros [] st [Huniq Hused].
        unfold uncurry_exp; fold uncurry_exp.
        eapply bind_triple.
        eapply pre_strenghtening; [|use_IH IHn].
        simpl; intros [] s [_ Hs]; subst.
        split; [now inv Huniq|].
        eapply Included_trans; [|apply Hused].
        rewrite used_vars_Eprim_val...
        intros e1 st1; apply return_triple.
        intros [] st2 [n Hrel] [_ Hst]; subst st1; rename st2 into st1.
        assert (from_fresh st \subset from_fresh st1) by (eapply uncurry_rel_s_nondecreasing; eauto).
        destruct n; inv Hrel.
        exists 0; constructor.
        exists (S n); econstructor.
        constructor; eauto.
        apply app_ctx_uncurry_rel with (c := Eprim_val_c v p Hole_c).
        eapply uncurry_step_preserves_used_vars; eauto.
        apply app_ctx_uncurry_step with (c := Eprim_val_c v p Hole_c). all: eauto.
      + (* Eprim *)
        eapply pre_eq_state_lr; intros [] st [Huniq Hused].
        unfold uncurry_exp; fold uncurry_exp.
        eapply bind_triple.
        eapply pre_strenghtening; [|use_IH IHn].
        simpl; intros [] s [_ Hs]; subst.
        split; [now inv Huniq|].
        eapply Included_trans; [|apply Hused].
        rewrite used_vars_Eprim...
        intros e1 st1; apply return_triple.
        intros [] st2 [n Hrel] [_ Hst]; subst st1; rename st2 into st1.
        assert (from_fresh st \subset from_fresh st1) by (eapply uncurry_rel_s_nondecreasing; eauto).
        destruct n; inv Hrel.
        exists 0; constructor.
        exists (S n); econstructor.
        constructor; eauto.
        apply app_ctx_uncurry_rel with (c := Eprim_c v p l Hole_c).
        eapply uncurry_step_preserves_used_vars; eauto.
        apply app_ctx_uncurry_step with (c := Eprim_c v p l Hole_c). all: eauto.
      + apply return_triple; intros.
        exists 0; constructor.
    - (* fundefs *)
      destruct f; unfold Q; intros b.
      + (* Fcons *)
        eapply pre_eq_state_l; intros [] st [Huniq Hused].
        unfold uncurry_fundefs; fold uncurry_fundefs; fold uncurry_exp.
        destruct b.
        * (* cps uncurrying *)
          eapply bind_triple; [apply pre_post_copy; eapply pre_strenghtening; [|use_IH IHn] |].
          intros [] st0 [_ Hst0]; subst st0; split; [now inv Huniq|].
          eapply Included_trans; eauto.
          rewrite used_vars_Fcons...
          intros fds' st'.
          eapply pre_eq_state_l.
          intros [] st0 [[_ Hst] [n_fds Hfds]]; subst st'.
          destruct l.
          -- eapply bind_triple; [eapply pre_post_copy; eapply pre_strenghtening; [|use_IH IHn] |].
             intros [] st0' [_ Hst0']; subst; cbn; split; [now inv Huniq|].
             eapply Included_trans; eauto.
             2: eapply uncurry_fundefs_rel_s_nondecreasing; eauto.
             eapply Included_trans; eauto.
             normalize_used_vars...
             cbn; intros e0' st0'; apply pre_eq_state_l.
             intros [] st1 [[_ Hst1] [n_e0 He0]]; subst.
             apply return_triple. intros [] w [_ Hw]; subst w.
             exists (n_e0 + n_fds); eapply uncurry_rel_fundefs_compose.
             apply uncurry_rel_fundefs_Fcons; eauto.
             apply app_ctx_uncurry_rel_fundefs with (f := Fcons1_c v f [] Hole_c fds'); auto.
             simpl; rewrite used_vars_Fcons.
             intros a Ha; inv Ha.
             revert H; apply Included_trans with (s2 := from_fresh st).
             eapply Included_trans; eauto; rewrite used_vars_Fcons...
             eapply uncurry_fundefs_rel_s_nondecreasing; eauto.
             eapply uncurry_fundefs_rel_preserves_used_vars; eauto.
             eapply Included_trans; eauto; rewrite used_vars_Fcons...
           Ltac solve_wildcard IHn Huniq n_fds fds' st H v f v0 l := solve[
             eapply bind_triple; [eapply pre_post_copy; eapply pre_strenghtening; [|use_IH IHn] |];
              [intros [] st0' [_ Hst0']; subst; cbn; split; [now inv Huniq|];
               eapply Included_trans; eauto; [|eapply uncurry_fundefs_rel_s_nondecreasing; eauto];
               eapply Included_trans; eauto; rewrite used_vars_Fcons; eauto with Ensembles_DB
              |cbn; intros e' st'; apply pre_eq_state_l;
               intros [] st1 [[_ Hst'] [n_e He]]; subst st';
               apply return_triple; intros [] w [_ Hw]; subst w;
               exists (n_e + n_fds); eapply uncurry_rel_fundefs_compose;
                [apply uncurry_rel_fundefs_Fcons; eauto|];
               apply app_ctx_uncurry_rel_fundefs
                 with (f := Fcons1_c v f (v0 :: l) Hole_c fds'); auto;
               cbn; rewrite used_vars_Fcons;
               intros a Ha; inv Ha;
               [revert H; apply Included_trans with (s2 := from_fresh st);
                [eapply Included_trans; eauto; rewrite used_vars_Fcons; eauto with Ensembles_DB
                |eapply uncurry_fundefs_rel_s_nondecreasing; eauto]
               |eapply uncurry_fundefs_rel_preserves_used_vars; eauto;
                eapply Included_trans; eauto; rewrite used_vars_Fcons; eauto with Ensembles_DB]]].
          -- destruct e; try solve_wildcard IHn Huniq n_fds fds' st H v f v0 l.
             destruct f1; try solve_wildcard IHn Huniq n_fds fds' st H v f v0 l.
             destruct f2; try solve_wildcard IHn Huniq n_fds fds' st H v f v0 l.
             destruct e; try solve_wildcard IHn Huniq n_fds fds' st H v f v0 l.
             destruct l1; try solve_wildcard IHn Huniq n_fds fds' st H v f v0 l.
             destruct l1; try solve_wildcard IHn Huniq n_fds fds' st H v f v0 l.
             eapply bind_triple; [apply pre_post_copy; eapply pre_strenghtening;
                                  [|apply already_uncurried_triple] |].
             { cbn; intros [] s [_ Hs]; now subst. }
             intros getb st1'; apply pre_eq_state_l.
             intros [] st1'' [[_ Hst1] [Hst1' Hget]]; subst st1' st1''.
             destruct (eq_var v0 v2 &&
                       eq_var v1 v3 &&
                       negb (occurs_in_exp v1 e0) &&
                       negb (occurs_in_exp v0 e0) &&
                       negb getb) eqn:Hpred.
             ++ eapply bind_triple.
                rewrite pre_post_copy; eapply pre_strenghtening; [|apply get_names_lst_triple].
                { cbn; intros [] s [_ Hs]; now subst. }
                intros l0' st1'. apply pre_eq_state_l.
                intros [] st2 [[_ Hst1] [Hst2 [Hst2_m [Hl0' Hlen_l0']]]]; subst st1'.
                eapply bind_triple.
                apply pre_post_copy; eapply pre_strenghtening; [|apply get_names_lst_triple].
                { cbn; intros [] s [_ Hs]; now subst. }
                intros l' st2'. apply pre_eq_state_l.
                intros [] st3 [[_ Hst2'] [Hst3 [Hst3_m [Hl' Hlen_l']]]]; subst st2'.
                eapply bind_triple.
                rewrite pre_post_copy; eapply pre_strenghtening; [|apply get_name_triple].
                { cbn; intros [] s [_ Hs]; now subst. }
                intros v' st3'. apply pre_eq_state_l.
                intros [] st4 [[_ Hst3'] [Hst4 [Hst4_m Hv]]]; subst st3'.
                eapply bind_triple'. rewrite pre_post_copy.
                eapply pre_strenghtening; [|apply mark_as_uncurried_triple].
                { cbn; intros [] s [_ Hs]; now subst. }
                intros [] st4'. apply pre_eq_state_l.
                intros [] st5' [[_ Hst4'] [Hst5 Hst5_m]]. subst.
                eapply bind_triple. apply pre_post_copy; eapply pre_strenghtening; [|apply click_triple].
                { cbn; intros [] s [_ Hs]; now subst. }
                intros [] st5''. apply pre_eq_state_lr.
                intros [] st6' [[_ Hst5'] [Hst6 Hst6_m]]; subst st5''.
                eapply bind_triple. apply pre_post_copy.
                eapply pre_strenghtening; [|apply markToInline_triple].
                { cbn; intros [] s [_ Hs]; now subst. }
                intros [] st6''. apply pre_eq_state_lr.
                intros [] st7' [[_ Hst6'] [Hst7 Hst7_m]]; subst st6''.
                eapply bind_triple'. rewrite pre_post_copy.
                eapply pre_strenghtening; [|apply get_fun_tag_triple].
                { cbn; intros [] s [_ Hs]; now subst. }
                intros ft' st7''. apply pre_eq_state_lr.
                intros [] st8 [[_ Hst7'] [Hst8 Hst8_m]]; subst st7''.
                apply return_triple.
                intros [] st8' [_ Hst8'] _ _ _; subst st8'.
                assert (Hfds_ctx :
                  uncurry_rel_fundefs n_fds
                    (Fcons v f (v0 :: l)
                           (Efun (Fcons v1 f1 l0 e0 Fnil) (Eapp v2 f2 [v3]))
                           f0)
                    (from_fresh st)
                    (already_uncurried st)
                    (Fcons v f (v0 :: l)
                           (Efun (Fcons v1 f1 l0 e0 Fnil) (Eapp v2 f2 [v3]))
                           fds')
                    (from_fresh st0)
                    (already_uncurried st0)) by now apply uncurry_rel_fundefs_Fcons.
                exists (1 + n_fds).
                eapply uncurry_rel_fundefs_compose; eauto.
                econstructor; [|constructor].
                repeat match goal with
                  [ H : ?a && ?b = true |- _ ] => apply andb_prop in H; destruct H
                | [ H : negb ?a = true |- _ ] => rewrite negb_true_iff in H
                | [ H : eq_var ?a ?b = true |- _ ] => rewrite Pos.eqb_eq in H; subst a
                | [ H : occurs_in_exp ?a ?e = false |- _ ] =>
                  rewrite not_occurs_in_exp_iff_used_vars in H
                end.
                eapply uncurry_fundefs_step_subst.
                apply uncurry_fundefs_curried with (s' := from_fresh st8).
                13: reflexivity.
                all:
                  unfold fresh_copies in *;
                  try rewrite <- Hst2 in *;
                  try rewrite <- Hst3 in *;
                  try setoid_rewrite <- Hst3;
                  eauto with Ensembles_DB;
                  try match goal with
                    [ _ : _ |- occurs_in_exp ?a ?e = false ] =>
                      apply not_occurs_in_exp_iff_used_vars; intros contra
                  | [ _ : ?a = next_free ?s |- ~ In _ (from_fresh ?s) ?a ] =>
                      subst a; apply next_free_not_In_from_fresh
                end.
                ** contradiction H2.
                ** contradiction H1.
                ** eapply next_free_not_In_from_fresh.
                ** rewrite Union_commut. rewrite <- Hst4.
                   rewrite Hst8, Hst7, Hst6, Hst5.
                   eapply from_fresh_fst_eq. congruence.
                ** now rewrite <- Hst2_m, <- Hst3_m, <- Hst4_m, Hst8_m, Hst7_m, Hst6_m, Hst5_m.
             ++ eapply bind_triple; [eapply pre_post_copy; eapply pre_strenghtening; [|use_IH IHn] |].
                 { intros [] st0' [_ Hst0']; subst; cbn; split; [now inv Huniq|];
                  eapply Included_trans; eauto; [|eapply uncurry_fundefs_rel_s_nondecreasing; eauto];
                    eapply Included_trans; eauto; rewrite used_vars_Fcons; eauto with Ensembles_DB. }
                 cbn; intros e' st'; apply pre_eq_state_l;
                  intros [] st1 [[_ Hst'] [n_e He]]; subst st';
                  apply return_triple; intros [] w [_ Hw]; subst w;
                  exists (n_e + n_fds); eapply uncurry_rel_fundefs_compose;
                   [apply uncurry_rel_fundefs_Fcons; eauto|];
                  apply app_ctx_uncurry_rel_fundefs
                    with (f := Fcons1_c v f (v0 :: l) Hole_c fds'); auto;
                    cbn; rewrite used_vars_Fcons.
                 apply Union_Included.
                 ** eapply Included_trans; [|eapply uncurry_fundefs_rel_s_nondecreasing; eassumption].
                    eapply Included_trans; [|eassumption].
                    rewrite used_vars_Fcons...
                 ** eapply uncurry_fundefs_rel_preserves_used_vars; eauto.
                    eapply Included_trans; eauto; rewrite used_vars_Fcons...
        * (* anf uncurrying *)
          eapply bind_triple; [apply pre_post_copy; eapply pre_strenghtening; [|use_IH IHn] |].
          intros [] st0 [_ Hst0]; subst st0; split; [now inv Huniq|].
          eapply Included_trans; eauto.
          rewrite used_vars_Fcons...
          intros fds' st'.
          eapply pre_eq_state_l.
          intros [] st0 [[_ Hst] [n_fds Hfds]]; subst st'.
          Ltac solve_wildcard' IHn Huniq n_fds fds' st H v f l := solve[
            eapply bind_triple; [eapply pre_post_copy; eapply pre_strenghtening; [|use_IH IHn] |];
             [intros [] st0' [_ Hst0']; subst; cbn; split; [now inv Huniq|];
              eapply Included_trans; eauto; [|eapply uncurry_fundefs_rel_s_nondecreasing; eauto];
              eapply Included_trans; eauto; rewrite used_vars_Fcons; eauto with Ensembles_DB
             |cbn; intros e' st'; apply pre_eq_state_l;
              intros [] st1 [[_ Hst'] [n_e He]]; subst st';
              apply return_triple; intros [] w [_ Hw]; subst w;
              exists (n_e + n_fds); eapply uncurry_rel_fundefs_compose;
               [apply uncurry_rel_fundefs_Fcons; eauto|];
              apply app_ctx_uncurry_rel_fundefs
                with (f := Fcons1_c v f l Hole_c fds'); auto;
              cbn; rewrite used_vars_Fcons;
              intros a Ha; inv Ha;
              [revert H; apply Included_trans with (s2 := from_fresh st);
               [eapply Included_trans; eauto; rewrite used_vars_Fcons; eauto with Ensembles_DB
               |eapply uncurry_fundefs_rel_s_nondecreasing; eauto]
              |eapply uncurry_fundefs_rel_preserves_used_vars; eauto;
               eapply Included_trans; eauto; rewrite used_vars_Fcons; eauto with Ensembles_DB]]].
          destruct e; try solve_wildcard' IHn Huniq n_fds fds' st H v f l.
          destruct f1; try solve_wildcard' IHn Huniq n_fds fds' st H v f l.
          destruct f2; try solve_wildcard' IHn Huniq n_fds fds' st H v f l.
          destruct e; try solve_wildcard' IHn Huniq n_fds fds' st H v f l.
          eapply bind_triple; [apply pre_post_copy; eapply pre_strenghtening;
                               [|apply already_uncurried_triple] |].
          { cbn; intros [] s [_ Hs]; now subst. }
          intros getb st1'; apply pre_eq_state_l.
          intros [] st1'' [[_ Hst1] [Hst1' Hget]]; subst st1' st1''.
          destruct (eq_var v0 v1 && negb getb && negb (occurs_in_exp v0 e0)) eqn:Hpred.
          -- eapply bind_triple.
             rewrite pre_post_copy; eapply pre_strenghtening; [|apply get_names_lst_triple].
             { cbn; intros [] s [_ Hs]; now subst. }
             intros l0' st1'. apply pre_eq_state_l.
             intros [] st2 [[_ Hst1] [Hst2 [Hst2_m [Hl0' Hlen_l0']]]]; subst st1'.
             eapply bind_triple.
             apply pre_post_copy; eapply pre_strenghtening; [|apply get_names_lst_triple].
             { cbn; intros [] s [_ Hs]; now subst. }
             intros l' st2'. apply pre_eq_state_l.
             intros [] st3 [[_ Hst2'] [Hst3 [Hst3_m [Hl' Hlen_l']]]]; subst st2'.
             eapply bind_triple.
             rewrite pre_post_copy; eapply pre_strenghtening; [|apply get_name_triple].
             { cbn; intros [] s [_ Hs]; now subst. }
             intros v' st3'. apply pre_eq_state_l.
             intros [] st4 [[_ Hst3'] [Hst4 [Hst4_m Hv]]]; subst st3'.
             eapply bind_triple'. rewrite pre_post_copy.
             eapply pre_strenghtening; [|apply mark_as_uncurried_triple].
             { cbn; intros [] s [_ Hs]; now subst. }
             intros [] st4'. apply pre_eq_state_l.
             intros [] st5' [[_ Hst4'] [Hst5 Hst5_m]]. subst.
             eapply bind_triple. apply pre_post_copy; eapply pre_strenghtening; [|apply markToInline_triple].
             { cbn; intros [] s [_ Hs]; now subst. }
             intros [] st5''. apply pre_eq_state_lr.
             intros [] st6' [[_ Hst5'] [Hst6 Hst6_m]]; subst st5''.
             eapply bind_triple. apply pre_post_copy.
             eapply pre_strenghtening; [|apply click_triple].
             { cbn; intros [] s [_ Hs]; now subst. }
             intros [] st6''. apply pre_eq_state_lr.
             intros [] st7' [[_ Hst6'] [Hst7 Hst7_m]]; subst st6''.
             eapply bind_triple'. rewrite pre_post_copy.
             eapply pre_strenghtening; [|apply get_fun_tag_triple].
             { cbn; intros [] s [_ Hs]; now subst. }
             intros ft' st7''. apply pre_eq_state_lr.
             intros [] st8 [[_ Hst7'] [Hst8 Hst8_m]]; subst st7''.
             apply return_triple.
             intros [] st8' [_ Hst8'] _ _ _; subst st8'.
             assert (Hfds_ctx :
               uncurry_rel_fundefs n_fds
                 (Fcons v f l
                        (Efun (Fcons v0 f1 l0 e0 Fnil) (Ehalt v1))
                        f0)
                 (from_fresh st)
                 (already_uncurried st)
                 (Fcons v f l
                        (Efun (Fcons v0 f1 l0 e0 Fnil) (Ehalt v1))
                        fds')
                 (from_fresh st0)
                 (already_uncurried st0)) by now apply uncurry_rel_fundefs_Fcons.
             exists (1 + n_fds).
             eapply uncurry_rel_fundefs_compose; eauto.
             econstructor; [|constructor].
             repeat match goal with
               [ H : ?a && ?b = true |- _ ] => apply andb_prop in H; destruct H
             | [ H : negb ?a = true |- _ ] => rewrite negb_true_iff in H
             | [ H : eq_var ?a ?b = true |- _ ] => rewrite Pos.eqb_eq in H; subst a
             | [ H : occurs_in_exp ?a ?e = false |- _ ] =>
               rewrite not_occurs_in_exp_iff_used_vars in H
             end.
             eapply uncurry_fundefs_step_subst.
             apply uncurry_fundefs_curried_anf with (s' := from_fresh st8).
             12: reflexivity.
             all:
               unfold fresh_copies in *;
               try rewrite <- Hst2 in *;
               try rewrite <- Hst3 in *;
               try setoid_rewrite <- Hst3;
               eauto with Ensembles_DB;
               try match goal with
                 [ _ : _ |- occurs_in_exp ?a ?e = false ] =>
                   apply not_occurs_in_exp_iff_used_vars; intros contra
               | [ _ : ?a = next_free ?s |- ~ In _ (from_fresh ?s) ?a ] =>
                   subst a; apply next_free_not_In_from_fresh
             end.
             ++ contradiction.
             ++ eapply next_free_not_In_from_fresh.
             ++ rewrite Union_commut. rewrite <- Hst4.
                rewrite Hst8, Hst7, Hst6, Hst5.
                eapply from_fresh_fst_eq. congruence.
             ++ now rewrite <- Hst2_m, <- Hst3_m, <- Hst4_m, Hst8_m, Hst7_m, Hst6_m, Hst5_m.
          -- eapply bind_triple; [eapply pre_post_copy; eapply pre_strenghtening; [|use_IH IHn] |].
              { intros [] st0' [_ Hst0']; subst; cbn; split; [now inv Huniq|];
               eapply Included_trans; eauto; [|eapply uncurry_fundefs_rel_s_nondecreasing; eauto];
                 eapply Included_trans; eauto; rewrite used_vars_Fcons; eauto with Ensembles_DB. }
              cbn; intros e' st'; apply pre_eq_state_l;
               intros [] st1 [[_ Hst'] [n_e He]]; subst st';
               apply return_triple; intros [] w [_ Hw]; subst w;
               exists (n_e + n_fds); eapply uncurry_rel_fundefs_compose;
                [apply uncurry_rel_fundefs_Fcons; eauto|];
               apply app_ctx_uncurry_rel_fundefs
                 with (f := Fcons1_c v f l Hole_c fds'); auto;
                 cbn; rewrite used_vars_Fcons.
              apply Union_Included.
              ++ eapply Included_trans; [|eapply uncurry_fundefs_rel_s_nondecreasing; eassumption].
                 eapply Included_trans; [|eassumption].
                 rewrite used_vars_Fcons...
              ++ eapply uncurry_fundefs_rel_preserves_used_vars; eauto.
                 eapply Included_trans; eauto; rewrite used_vars_Fcons...
      + (* Fnil *)
        apply return_triple; intros.
        exists 0; constructor.
  Qed.

  Corollary uncurry_exp_corresp : forall cps e,
    {{ fun _ st => unique_bindings e /\ used_vars e \subset from_fresh st }}
      uncurry_exp cps e
    {{ fun _ st e1 st1 => exists n,
         uncurry_rel n
                     e (from_fresh st) (already_uncurried st)
                     e1 (from_fresh st1) (already_uncurried st1)
    }}.
  Proof. intros; eapply (uncurry_corresp_mut (inl e)); eauto. Qed.

  Corollary uncurry_fundefs_corresp : forall cps f,
    {{ fun _ st => unique_bindings_fundefs f /\ used_vars_fundefs f \subset from_fresh st }}
      uncurry_fundefs cps f
    {{ fun _ st f1 st1 => exists n,
         uncurry_rel_fundefs n
                             f (from_fresh st) (already_uncurried st)
                             f1 (from_fresh st1) (already_uncurried st1)
    }}.
  Proof. intros; eapply (uncurry_corresp_mut (inr f)); eauto. Qed.

  Definition uncurry_triple cps e P Q :=
    {{ fun _ st => unique_bindings e /\ used_vars e \subset from_fresh st /\ P st }}
      uncurry_exp cps e
    {{ fun _ => Q e }}.

  Lemma uncurry_rel_to_triple : forall cps e P Q,
    (forall n e1 st st1,
        uncurry_rel n e  (from_fresh st)  (already_uncurried st)
                      e1 (from_fresh st1) (already_uncurried st1) ->
        unique_bindings e ->
        used_vars e \subset from_fresh st ->
        P st ->
        Q e st e1 st1
    ) -> uncurry_triple cps e P Q.
  Proof.
    intros.
    apply pre_eq_state_lr; intros [] s [Huniq [Hused He]].
    eapply triple_consequence.
    apply uncurry_exp_corresp.
    - intros _ w [_ Hw]; subst; auto.
    - cbn. intros _ w x w' H' [n Hrel] [_ Hw]; subst.
      eapply H; eauto.
  Qed.

  Lemma uncurry_exp_correct : forall cps e,
    uncurry_triple cps e (fun _ => True) (fun e _ e1 _ => forall k, ctx_preord_exp k e e1).
  Proof.
    intros; apply uncurry_rel_to_triple.
    intros; eapply uncurry_rel_correct; eauto.
  Qed.

  Lemma uncurry_fuel'_correct cps :
    forall (n : nat) (e : exp) (st : stateType'),
      unique_bindings e ->
      Disjoint _ (bound_var e) (occurs_free e) ->
      used_vars e \subset from_fresh st ->
      exists e' st',
        compM.runState
          (uncurry_fuel' uncurry_exp cps n e) tt st = (Ret e', st') /\
        unique_bindings e' /\
        Disjoint _ (bound_var e') (occurs_free e') /\
        used_vars e' \subset from_fresh st' /\
        occurs_free e' \subset occurs_free e /\
        forall k, ctx_preord_exp k e e'.
  Proof.
    Transparent bind ret.
    intros n.
    induction n as [| n IH ];
      intros e0 st Huniq Hdis Hused.

    - do 2 eexists.
      repeat split; try reflexivity; try assumption.
      + apply Hdis.
      + intros k rho1 rho2 Henv.
        now apply preord_exp_refl.

    - specialize (uncurry_exp_corresp cps e0) as Hpass.
      specialize (Hpass tt st (conj Huniq Hused)).

      destruct (compM.runState (uncurry_exp cps e0) tt st)
        as [res st1] eqn:Hrun.

      unfold stateType' in Hpass.
      rewrite Hrun in Hpass.
      destruct res as [| e1 ]; [ contradiction |].
      destruct Hpass.

      assert (Huniq1 : unique_bindings e1)
        by (eapply uncurry_rel_preserves_unique_bindings; eauto).

      assert (Hdis1 : Disjoint _ (bound_var e1) (occurs_free e1))
        by (eapply uncurry_rel_preserves_disjoint; eauto).

      assert (Hused1 : used_vars e1 \subset from_fresh st1)
        by (eapply uncurry_rel_preserves_used_vars; eauto).

      destruct st1 as [c1 [[[clicked aenv] lm] stats]].
      destruct clicked.

      + destruct (IH e1 (c1, (false, aenv, lm, stats))
                    Huniq1 Hdis1 Hused1)
          as [e2 [st2 [Hrun2 [Huniq2 [Hdis2 [Hused2 [Hfree2 Hsem2]]]]]]].

        do 2 eexists.
        repeat split; try eassumption.
        * simpl in Hrun |- *; rewrite Hrun; apply Hrun2.
        * apply Hdis2.
        * apply Included_refl.
          eapply Included_trans; eauto.
          eapply uncurry_rel_preserves_occurs_free; eauto.
        * intros k rho1 rho2 Henv.
          eapply preord_exp_post_monotonic.
          apply Hpost_idemp.
          eapply preord_exp_trans.
          -- now constructor; try easy_post.
          -- now apply Hpost_idemp'.
          -- eapply uncurry_rel_correct; eauto.
          -- intros.
             eapply Hsem2.
             apply preord_env_P_refl; eauto.

      + do 2 eexists. repeat split.
        * simpl in Hrun |- *; rewrite Hrun; reflexivity.
        * assumption.
        * apply Hdis.
        * eapply Included_trans; [ eassumption |].
          eapply uncurry_rel_s_nondecreasing; eauto.
        * apply Included_refl.
        * intros k rho1 rho2 Henv.
          now apply preord_exp_refl.
  Qed.

  Lemma uncurry_fuel_correct cps n (e : exp) (c : comp_data) :
    unique_bindings e ->
    Disjoint _ (bound_var e) (occurs_free e) ->
    (max_var e 1 < state.next_var c)%positive ->
    exists e' c', uncurry_fuel cps n e c = (Ret e', c') /\
                    unique_bindings e' /\
                    Disjoint _ (bound_var e') (occurs_free e') /\
                    (max_var e' 1 < state.next_var c')%positive /\
                    occurs_free e' \subset occurs_free e /\
                    forall k, ctx_preord_exp k e e'.
  Proof.
    Transparent bind ret.

    intros Huniq Hdis Hmax.
    set (st0 := (c, (false, M.empty fun_tag, M.empty bool, (0, M.empty nat)))).

    assert (Hused : used_vars e \subset from_fresh st0).
    {
      intros x Hx.
      destruct Hx; eapply Pos.le_lt_trans; try eassumption.
      - eapply bound_var_leq_max_var; eassumption.
      - eapply occurs_free_leq_max_var; eassumption.
    }

    destruct (uncurry_fuel'_correct cps n e st0 Huniq Hdis Hused)
      as [e' [st' [Hrun [Huniq' [Hdis' [Hused' [Hfree' Hsem']]]]]]].

    destruct st' as [c' [[[clicked aenv] lm] [arity imap]]].

    exists e', (put_inline_map imap c').
    repeat split; try eassumption.
    * unfold uncurry_fuel, uncurry_fuel'', run_compM.
      unfold st0, stateType', stateType, arityMap, localMap, St
        in Hrun |- *.
      now rewrite Hrun.
    * apply Hdis'.
    * destruct c'; apply Hused'; apply max_var_subset.
  Qed.

  Corollary uncurry_top_correct cps (e : exp) (c : comp_data) :
    unique_bindings e ->
    Disjoint _ (bound_var e) (occurs_free e) ->
    (max_var e 1 < state.next_var c)%positive ->
    exists e' c', uncurry_top cps e c = (Ret e', c') /\
                    unique_bindings e' /\
                    Disjoint _ (bound_var e') (occurs_free e') /\
                    (max_var e' 1 < state.next_var c')%positive /\
                    occurs_free e' \subset occurs_free e /\
                    forall k, ctx_preord_exp k e e'.
  Proof.
    unfold uncurry_top.
    apply uncurry_fuel_correct.
  Qed.

End Uncurry_correct.
