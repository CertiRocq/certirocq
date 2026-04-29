From Stdlib Require Import Relations.Relations.
From Stdlib Require Import Relations.Relations.
From Stdlib Require Import Setoids.Setoid.
From Stdlib Require Import Classes.Morphisms.
Import RelationClasses.

Require Import ExtLib.Data.Bool.
Require compcert.lib.Maps.
Require Import compcert.lib.Coqlib.
From Stdlib Require funind.Recdef.
Import Nnat.
From Stdlib Require Import Arith.Arith NArith.BinNat.
Require Import ExtLib.Data.String ExtLib.Data.List.
From Stdlib Require Import micromega.Lia Program.Program micromega.Lia Sets.Ensembles Logic.Decidable Lists.ListDec.
Require Import Libraries.CpdtTactics.
From Stdlib Require Import Sorting.Permutation.
Require Import Libraries.HashMap.
Require Import Libraries.maps_util.
Require Import LambdaANF.Ensembles_util LambdaANF.term LambdaANF.rename LambdaANF.ctx LambdaANF.logical_relations LambdaANF.tactics LambdaANF.term_util
        LambdaANF.List_util LambdaANF.shrink_cps LambdaANF.eval LambdaANF.set_util LambdaANF.identifiers LambdaANF.stemctx LambdaANF.shrink_cps_correct LambdaANF.inline_letapp.

Import ListNotations.


Ltac dec_vars :=
  repeat match goal with
         | [ H: (if var_dec ?X ?Y then _ else _) = 0 |- _] =>
           destruct (var_dec X Y); try inversion H; pi0
         end.


Notation "A =mgd0= B" := (map_getd_r _ 0 A B) (at level 80).
Notation "A =mg= B" := (map_get_r _ A B) (at level 81).

Notation c_plus := (fun v c => get_c v c + 1)%nat.
Notation c_minus := (fun v c => get_c v c - 1)%nat.

Section CENSUS.

  Definition c_count: exp -> c_map -> Prop :=
    fun e count => forall v, num_occur e v (get_c v count).

  Definition c_count_f: fundefs -> c_map -> Prop :=
    fun f count => forall v, num_occur_fds f v (get_c v count).

  Definition c_count_c: exp_ctx -> c_map -> Prop :=
    fun c count => forall v, num_occur_ec c v (get_c v count).

  Definition c_count_fdc: fundefs_ctx -> c_map -> Prop :=
    fun fdc count => forall v, num_occur_fdc fdc v (get_c v count).

  Definition init_census_f (f:fundefs) :=
    update_census_f (M.empty var) f (fun v c => get_c v c + 1)%nat (M.empty nat).

  Definition f_opt_d {A} (d:A) f on om: option A :=
    match on with
    | Some n => (match om with
                 | Some m => Some (f n m)
                 | None => Some (f n d)
                 end)
    | None => match om with
              | Some m => Some (f d m)
              | None => None
              end
    end.


  Lemma gccombine:
    forall (x : M.elt) (x1 x0 : c_map) (n m: nat),
      get_c x x1 = n ->
      get_c x x0 = m ->
      get_c x (M.combine (f_opt_d 0 Init.Nat.add) x1 x0) = (n + m).
  Proof.
    unfold getd; intros. rewrite M.gcombine.
    destruct (M.get x x1); destruct (M.get x x0);
      simpl; subst; auto. reflexivity.
  Qed.


  Lemma gccombine':
    forall (x : M.elt) (x1 x0 : c_map),
      get_c x (M.combine (f_opt_d 0 Init.Nat.add) x1 x0) = (get_c x x1 + get_c x x0).
  Proof.
    unfold getd; intros. rewrite M.gcombine.
    destruct (M.get x x1); destruct (M.get x x0); simpl; subst; auto. reflexivity.
  Qed.

  Lemma gccombine_sub:
    forall (x : M.elt) (x1 x0 : c_map),
      get_c x (M.combine (f_opt_d 0 Init.Nat.sub) x1 x0) = (get_c x x1 - get_c x x0 ).
  Proof.
    unfold getd; intros. rewrite M.gcombine.
    destruct (M.get x x1); destruct (M.get x x0); simpl; subst; auto. reflexivity.
  Qed.


  Lemma proper_set_fun f x y z :
    map_getd_r nat 0 x y ->
    (forall c c' : Maps.PTree.t nat,
        map_getd_r nat 0 c c' -> forall n0 : var, f n0 c = f n0 c') ->
    map_getd_r nat 0 (M.set z (f z x) x) (M.set z (f z y) y).
  Proof.
    intro; intro; intros; intro.
    destruct (var_dec v z).
    subst.
    do 2 (rewrite gdss).  apply H0; auto.
    rewrite gdso. rewrite gdso. apply H. auto. auto.
  Qed.

  Theorem proper_update_census_d_list:
    forall {l} {f} {sig},
      (forall c c', map_getd_r _ 0 c c' -> forall n, f n c = f n c') ->
      Proper (map_getd_r _ 0 ==> map_getd_r _ 0) (update_census_list sig l f).
  Proof.
    induction l; intros.
    simpl. intro. intros. auto.
    intro. intros. simpl. apply IHl.
    intro; intros. apply H; auto.
    intro. destruct (M.elt_eq v (apply_r sig a)).
    subst. rewrite gdss. rewrite gdss. apply H; auto.
    rewrite gdso by auto. rewrite gdso by auto. apply H0.
  Qed.


  Theorem proper_update_census_d f :
    (forall c c', map_getd_r _ 0 c c' -> forall n, f n c = f n c') ->
    (forall e sig, Proper (map_getd_r _ 0 ==> map_getd_r _ 0) (update_census sig e f)) /\
    (forall fds sig, Proper (map_getd_r _ 0 ==> map_getd_r _ 0) (update_census_f sig fds f)).
  Proof.
    intros fhs;
    eapply exp_def_mutual_ind; intros; simpl.
    - intro. intros.
      apply H.
      apply proper_update_census_d_list; auto.
    - intro; intros.
      apply proper_set_fun; auto.
    - intro; intros.
      eapply H.
      simpl in H0. apply H0. auto.
    - intro; intros.
      apply H.
      revert fhs.
      revert H0.
      apply proper_set_fun.
    - intro. intros.
      apply H.
      apply proper_update_census_d_list; auto.
      apply proper_set_fun; eauto.
    - intro. intros.
      apply H0.
      apply H. auto.
    - intro; intros.
      apply proper_update_census_d_list.
      auto.
      apply proper_set_fun; auto.
    - apply H.
    - intro. intros.
      apply H. apply proper_update_census_d_list; auto.
    - intro; intros.
      apply proper_set_fun; auto.
    - intro; intros.
      apply H0.
      apply H.
      auto.
    - intro; intros. auto.
  Qed.


  Theorem proper_plus_census_d e sig:
    Proper (map_getd_r _ 0 ==> map_getd_r _ 0) (update_census sig e c_plus).
  Proof.
    apply proper_update_census_d.
    intros.  rewrite H. reflexivity.
  Qed.

  Theorem proper_minus_census_d e sig:
    Proper (map_getd_r _ 0 ==> map_getd_r _ 0) (update_census sig e c_minus).
  Proof.
    apply proper_update_census_d.
    intros. rewrite H; auto.
  Qed.


  Theorem init_census_f_ar_l f l sig c :
    map_getd_r _ 0 (update_census_list (M.empty var) (apply_r_list sig l) f c) (update_census_list sig l f c).
  Proof.
    revert f sig c; induction l; intros f sig c.
    - intro. simpl. reflexivity.
    - simpl. rewrite !apply_r_empty.
      apply IHl.
  Qed.

  (** update_census sig on m produces the same count as update_census (empty) on (sig m)  *)
  (* TODO: change name*)
  Theorem init_census_f_ar f :
    (forall c c', map_getd_r _ 0 c c' -> forall n, f n c = f n c') ->
    (forall m sig c,
        map_getd_r _ 0 (update_census (M.empty var) (rename_all_ns sig m) f c) (update_census sig m f c)) /\
    (forall m sig c,
        map_getd_r _ 0 (update_census_f (M.empty var) (rename_all_fun_ns sig m) f c) (update_census_f sig m f c)).
  Proof.
    intros Hf;
    eapply exp_def_mutual_ind; intros.
    - simpl.
      intro. rewrite <- H.
      apply proper_update_census_d.
      auto.
      apply init_census_f_ar_l.
    - simpl.
      rewrite apply_r_empty.
      apply smgd_refl.
    - simpl.
      intro. rewrite <- H.
      apply proper_update_census_d. auto.
      simpl in H0.
      apply H0.
    - simpl.
      intro. rewrite <- H.
      apply proper_update_census_d.
      auto.
      rewrite apply_r_empty.
      apply smgd_refl.
    - simpl.
      intro. rewrite <- H.
      apply proper_update_census_d.
      auto.
      rewrite !apply_r_empty.
      apply init_census_f_ar_l.
    - simpl.
      intro.
      rewrite <- H0.
      apply proper_update_census_d. auto.
      apply H.
    - simpl. rewrite apply_r_empty.
      apply init_census_f_ar_l.
    - simpl. intro. now rewrite H.
    - simpl.
      intro. rewrite <- H.
      apply proper_update_census_d.
      auto.
      apply init_census_f_ar_l.
    - simpl.
      rewrite apply_r_empty.
      apply smgd_refl.
    - simpl.
      intro.
      rewrite H0.
      apply proper_update_census_d. auto.
      intro. rewrite <- H.
      auto.
    - simpl. apply smgd_refl.
  Qed.


  Theorem init_census_plus_ar m sig c :
       map_getd_r _ 0 (update_census (M.empty var) (rename_all_ns sig m) c_plus c) (update_census sig m c_plus c).
  Proof.
    apply init_census_f_ar.
    intros.
    rewrite H. reflexivity.
  Qed.


  Theorem init_census_plus_ar_f m sig c :
    map_getd_r _ 0 (update_census_f (M.empty var) (rename_all_fun_ns sig m) c_plus c) (update_census_f sig m c_plus c).
  Proof.
    apply init_census_f_ar.
    intros.
    rewrite H.
    reflexivity.
  Qed.


  Theorem combine_plus_census_list l count sig :
    map_getd_r _ 0 (M.combine (f_opt_d 0 plus) count
                              (update_census_list (M.empty var) (apply_r_list sig l) c_plus (M.empty nat)))
               (update_census_list sig l c_plus count).
  Proof.
    revert count sig; induction l; intros count sig.
    - simpl. intro. rewrite gccombine'. rewrite gdempty. auto.
    - simpl. intro. rewrite !gccombine'. rewrite apply_r_empty. simpl.
      rewrite <- IHl.
      simpl. rewrite gccombine'.
      rewrite init_census_f_ar_l.
      rewrite <- IHl.
      rewrite gccombine'.
      destruct (var_dec v (apply_r sig a)).
      + subst. rewrite gdss. rewrite gdss.
        lia.
      + rewrite gdso by auto.
        rewrite gdso by auto.
        rewrite gdempty. simpl. reflexivity.
  Qed.

  Theorem get_c_up v v0 count :
    get_c v0 (M.set v (get_c v count + 1) count) = get_c v0 count + get_c v0 (M.set v 1 (M.empty nat)).
  Proof.
    intros. destruct (var_dec v v0).
    - subst.
      rewrite gdss. rewrite gdss. reflexivity.
    - rewrite gdso by auto.
      rewrite gdso by auto.
      rewrite gdempty.
      rewrite <- plus_n_O.
      auto.
  Qed.

  (** update_census sig on m with c_plus adds the occurences of variables in (sig m) to their respective tally in count  *)
  Theorem combine_plus_census_correct :
    (forall m count sig,
              map_getd_r _ 0 (M.combine (f_opt_d 0 plus) count (init_census (rename_all_ns sig m))) (update_census sig m c_plus count)) /\
    (forall f count sig,
        map_getd_r _ 0 (M.combine (f_opt_d 0 plus) count (update_census_f (M.empty var) (rename_all_fun_ns sig f) c_plus (M.empty nat))) (update_census_f sig f c_plus count)).
  Proof.
    eapply exp_def_mutual_ind; intros; simpl.
    - intro. rewrite gccombine'.
      rewrite <- H.
      rewrite gccombine'.
      unfold init_census.
      simpl.
      rewrite <- combine_plus_census_list.
      rewrite gccombine'.
      assert (Hfr := init_census_f_ar).
      destruct (Hfr c_plus). intros.  simpl. rewrite H0. auto.
      rewrite H0.
      rewrite <- H.
      rewrite gccombine'.
      simpl.
      unfold init_census.
      lia.
    - intro.
      rewrite gccombine'.
      unfold init_census.
      simpl.
      rewrite plus_n_O.
      rewrite apply_r_empty.
      simpl.
      rewrite get_c_up.
      lia.
    - intro.
      rewrite gccombine'.
      unfold init_census.
      simpl.
      unfold init_census in H0. simpl in H0.
      rewrite init_census_plus_ar.
      symmetry.
      erewrite proper_plus_census_d.
      2:{ apply smgd_sym. apply H0. }
      rewrite <- H. rewrite <- H.
      do 3 (rewrite gccombine').
      lia.
    - unfold init_census.
      simpl. intro. rewrite gccombine'.
      rewrite <- H.
      rewrite gccombine'.
      rewrite init_census_plus_ar.
      rewrite <- H.
      rewrite gccombine'.
      rewrite apply_r_empty.
      rewrite get_c_up. simpl.
      lia.
    - intro. rewrite gccombine'. rewrite <- H.
      rewrite gccombine'.
      unfold init_census. simpl.  rewrite <- !combine_plus_census_list.
      rewrite gccombine'.
      assert (Hfr := init_census_f_ar). destruct (Hfr c_plus). intros. simpl. rewrite H0. now auto.
      rewrite H0. rewrite <- H. rewrite gccombine'.
      unfold init_census.

      rewrite <- combine_plus_census_list.
      rewrite !gccombine'.
      rewrite !apply_r_empty.
      rewrite !get_c_up, apply_r_list_empty. lia.
    - intro.
      rewrite gccombine'.
      unfold init_census. simpl.
      rewrite init_census_plus_ar.
      rewrite <- H0.
      rewrite gccombine'.
      symmetry.
      rewrite <- H0.
      rewrite gccombine'.
      rewrite <- H.
      rewrite gccombine'.
      lia.
    - intro.
      rewrite gccombine'.
      rewrite <- combine_plus_census_list.
      rewrite gccombine'.
      unfold init_census. simpl.
      rewrite <- combine_plus_census_list.
      rewrite gccombine'.
      rewrite apply_r_empty.
      rewrite apply_r_list_empty.
      rewrite get_c_up. lia.
    - intro.
      rewrite gccombine'.
      unfold init_census. simpl.
      rewrite <- H.
      rewrite gccombine'.
      rewrite init_census_plus_ar.
      rewrite <- H.
      rewrite gccombine'.
      symmetry. reflexivity.
    - intro.
      rewrite gccombine'.
      unfold init_census. simpl.
      rewrite <- H.
      rewrite gccombine'.
      rewrite init_census_plus_ar.
      rewrite <- H.
      rewrite gccombine'.
      symmetry.
      rewrite <- combine_plus_census_list.
      rewrite gccombine'.
      lia.
    - intro.
      rewrite gccombine'.
      rewrite get_c_up. unfold init_census. simpl. rewrite apply_r_empty. lia.
    - intro; rewrite gccombine'.
      rewrite <- H0.
      rewrite gccombine'.
      rewrite init_census_plus_ar_f.
      rewrite <- H0.
      rewrite gccombine'.
      symmetry. rewrite <- H. rewrite gccombine'. unfold init_census.
      lia.
    - intro.
      rewrite gccombine'.
      rewrite gdempty.
      rewrite plus_n_O. reflexivity.
  Qed.

  Theorem num_occur_constr:
  forall {e} {v} {n n'},
    num_occur e v n ->
    n = n' ->
    num_occur e v n'.
  Proof.
    intros; subst; auto.
  Qed.

  Theorem num_occur_fds_constr:
  forall {e} {v} {n n'},
    num_occur_fds e v n ->
    n = n' ->
    num_occur_fds e v n'.
  Proof.
    intros; subst; auto.
  Qed.


  Theorem update_census_list_correct v sig l count :
    getd 0 v (update_census_list sig l c_plus count) =
    getd 0 v count + num_occur_list (apply_r_list sig l) v.
  Proof.
    revert v sig count; induction l; intros v sig count.
    - simpl; lia.
    - simpl. rewrite IHl. destruct (term_util.var_dec v (apply_r sig a)).
      + subst. rewrite gdss. lia.
      + rewrite gdso by auto. unfold get_c. unfold maps_util.getd.
        reflexivity.
  Qed.


  Theorem get_c_minus v v0 count :
    get_c v0 (M.set v (get_c v count - 1) count) = get_c v0 count - get_c v0 (M.set v 1 (M.empty nat)).
  Proof.
    intros. destruct (var_dec v v0).
    - subst.
      rewrite gdss. rewrite gdss. reflexivity.
    - rewrite gdso by auto.
      rewrite gdso by auto.
      rewrite gdempty.
      rewrite Nat.sub_0_r.
      auto.
  Qed.


  Theorem combine_minus_census_list l count sig :
    map_getd_r _ 0 (M.combine (f_opt_d 0 minus)
                              count
                              (update_census_list (M.empty var) (apply_r_list sig l) c_plus (M.empty nat)))
               (update_census_list sig l c_minus count).
  Proof.
    revert count sig; induction l; intros count sig.
    - simpl. intro. rewrite gccombine_sub. rewrite gdempty. rewrite Nat.sub_0_r. auto.
    - simpl. intro. rewrite gccombine_sub. rewrite <- IHl.
      simpl. rewrite gccombine_sub. rewrite apply_r_empty.
      rewrite init_census_f_ar_l.
      rewrite <- combine_plus_census_list.
      rewrite gccombine'.
      rewrite get_c_minus. lia.
  Qed.

End CENSUS.


Fixpoint inlined_fundefs_f (fds:fundefs) (i:b_map): fundefs :=
  match fds with
    | Fnil => Fnil
    | Fcons f t ys e fds' =>
      match get_b f i with
        | true => inlined_fundefs_f fds' i
        | false => Fcons f t ys e (inlined_fundefs_f fds' i)
      end
  end.

Theorem inlined_fundefs_append B2 im B1:
  inlined_fundefs_f (fundefs_append B1 B2) im =
  fundefs_append (inlined_fundefs_f B1 im) (inlined_fundefs_f B2 im).
Proof.
  induction B1; intros; simpl; auto.
  destruct (get_b v im); auto.
  rewrite IHB1.
  simpl. reflexivity.
Qed.


(** Only functions which are on the stem are considered *)
Fixpoint inlined_ctx_f (c:exp_ctx) (i:b_map): exp_ctx :=
  match c with
    | Hole_c => Hole_c
    | Econstr_c x t ys c => Econstr_c x t ys (inlined_ctx_f c i)
    | Eproj_c x t n y c => Eproj_c x t n y (inlined_ctx_f c i)
    | Eletapp_c x f t ys c => Eletapp_c x f t ys (inlined_ctx_f c i)
    | Ecase_c x te t c te' =>
      Ecase_c x te t (inlined_ctx_f c i) te'
    | Eprim_c x f ys c => Eprim_c x f ys (inlined_ctx_f c i)
    | Eprim_val_c x p c => Eprim_val_c x p (inlined_ctx_f c i)
    | Efun1_c fds c => Efun1_c (inlined_fundefs_f fds i) (inlined_ctx_f c i)
    | Efun2_c cfds e' => Efun2_c (inlined_fundefs_ctx_f cfds i) e'
  end
with inlined_fundefs_ctx_f (cfds: fundefs_ctx) (im:b_map): fundefs_ctx :=
       match cfds with
         | Fcons1_c f t ys c fds =>
           Fcons1_c f t ys (inlined_ctx_f c im) fds
         | Fcons2_c f t ys e' cfds =>
           Fcons2_c f t ys e' (inlined_fundefs_ctx_f cfds im)
       end.


Definition eq_b_map_P:  Ensemble var -> b_map -> b_map -> Prop :=
  fun S rho1 rho2 =>
    forall x, S x -> get_b x rho1 = get_b x rho2.


Theorem eq_b_map_P_mon:
  forall S S' b1 b2,
    eq_b_map_P S' b1 b2 ->
    Included _ S S' ->
    eq_b_map_P S b1 b2.
Proof.
  intros.
  intro; intros.
  apply H0 in H1. apply H in H1. auto.
Qed.

Theorem  eq_b_inlined_fundefs b1 b2 fds :
  eq_b_map_P (name_in_fundefs fds) b1 b2 ->
  inlined_fundefs_f fds b1 = inlined_fundefs_f fds b2.
Proof.
  induction fds; intros.
  - simpl in *.
    assert ( eq_b_map_P (name_in_fundefs fds) b1 b2 ).
    eapply eq_b_map_P_mon; eauto with Ensembles_DB.
    specialize (IHfds H0).
    destruct (get_b v b1) eqn:gbv1.
    rewrite H in gbv1.
    rewrite gbv1.
    apply IHfds.
    left; auto.
    rewrite H in gbv1.
    rewrite gbv1.
    rewrite IHfds.
    auto.
    left; auto.
  - auto.
Qed.



Definition Dom_map_b im: Ensemble var := fun x => get_b x im = true.

(** inlined_ctx_f distributes over context composition *)
Theorem inlined_comp_ctx:
  (forall c1 c2 im, inlined_ctx_f (comp_ctx_f c1 c2) im = comp_ctx_f (inlined_ctx_f c1 im) (inlined_ctx_f c2 im)) /\
  (forall f c2 im, (inlined_fundefs_ctx_f (comp_f_ctx_f f c2) im) = (comp_f_ctx_f (inlined_fundefs_ctx_f f im) (inlined_ctx_f c2 im))).
Proof.
  exp_fundefs_ctx_induction IHc1 IHf; intros; simpl; auto; try (rewrite IHc1; reflexivity).
  rewrite IHf. reflexivity.
  rewrite IHf. reflexivity.
Qed.


Theorem Disjoint_inlined_fds fds im :
    Disjoint _ (name_in_fundefs fds) (Dom_map_b im) ->
    inlined_fundefs_f fds im = fds.
Proof.
  induction fds; intros.
  - simpl in H.
    simpl.
    destruct (get_b v im) eqn:bvm.
    + exfalso.
      inv H. specialize (H0 v).
      apply H0; split; auto.
    + rewrite IHfds.
      reflexivity.
      eapply Disjoint_Included_l.
      2: apply H.
      eauto with Ensembles_DB.
  - reflexivity.
Qed.


Theorem Disjoint_inlined_ctx_mut im:
  (forall c (HD : Disjoint _ (bound_var_ctx c) (Dom_map_b im)),
      inlined_ctx_f c im = c) /\
  (forall fc (HD : Disjoint _ (bound_var_fundefs_ctx fc) (Dom_map_b im)),
     inlined_fundefs_ctx_f fc im = fc).
Proof.
  exp_fundefs_ctx_induction IHc IHf; simpl; intros; try (rewrite IHc); try (rewrite IHf); auto;
    try now (eapply Disjoint_Included_l; [| eapply HD ];  normalize_bound_var_ctx; sets).

  rewrite Disjoint_inlined_fds. reflexivity.
  eapply Disjoint_Included_l; [| eapply HD ]; normalize_bound_var_ctx; sets.
  eapply Included_trans. eapply name_in_fundefs_bound_var_fundefs. sets.
Qed.


Theorem Disjoint_inlined_ctx:
  (forall c im,
     Disjoint _ (bound_var_ctx c) (Dom_map_b im) ->
     inlined_ctx_f c im = c).
Proof.
  intros.
  apply Disjoint_inlined_ctx_mut.
  auto.
Qed.

Section CONTRACT.

  (** The domain of inl represents inlined functions in the context.
      The function and its arguments should no longer be bound in the term *)
  Definition inl_inv (im:b_map) (sub:ctx_map) (e:exp):Prop :=
    forall f, get_b f im = true ->
              ~ (bound_var e f) /\
              (forall t xs m, M.get f sub = Some (SVfun t xs m) ->
                              Disjoint _ (bound_var e) (FromList xs)).

  (** cmap is a correct approximation of the context w.r.t. constructors and functions on the stem *)
  Definition cmap_view_ctx sub c: Prop :=
    (forall x t xs,
       M.get x sub = Some (SVconstr t xs) <->
       exists c' c'',
         c = comp_ctx_f c' (Econstr_c x t xs c'')) /\
    (forall f t ys e,
       M.get f sub = Some (SVfun t ys e) <->
       exists c' c'' B1 B2,
         c = comp_ctx_f c' (Efun1_c
                              (fundefs_append B1 (Fcons f t ys e B2)) c'')).

  Theorem empty_view_hole:
    cmap_view_ctx (M.empty _) (Hole_c).
  Proof.
    split; split; intros.
    - rewrite M.gempty in H. inv H.
    - destructAll.
      exfalso.
      destruct x0; inv H.
    - rewrite M.gempty in H. inv H.
    - destructAll.
      exfalso.
      destruct x; inv H.
  Qed.


  Theorem num_occur_case_le :
    forall x v e m cl,
      List.In (v, e) cl ->
      forall n,
        num_occur_case cl x n ->
        num_occur e x m ->
        m <= n.
  Proof.
    induction cl; intros.
    inv H.
    inv H.
    + inv H0. assert (m = n0).
      eapply (proj1 (num_occur_det _)); eauto.
      lia.
    + inv H0.
      specialize (IHcl H2 _ H7 H1).
      lia.
  Qed.

  (* equivalent to c_nozombie in aj  *)
  Definition no_zombie e1 e2: Prop :=
    Included _ (dead_var e1) (dead_var e2).

  (* Delete after compile *)
  Ltac pi0 :=
  repeat match goal with
         | [ H: _ + _ = 0 |- _ ] =>
           apply Nat.eq_add_0 in H; destruct H; subst
         | [ H: 0 = _ + _ |- _ ] =>
           symmetry in H; pi0
         (* | [ H: (if term_util.var_dec ?X ?Y then _ else _) = 0 |- _] => *)
         (*   destruct (term_util.var_dec X Y); try inversion H; pi0 *)
         | [ H: ?X <> ?X |- _] =>
           exfalso; apply H; auto
         end.


  Lemma rename_all_ns_same_mut m (Hyp : forall x, apply_r m x = x) :
    (forall e, rename_all_ns m e = e) /\
    (forall B, rename_all_fun_ns m B = B).
  Proof.
    exp_defs_induction IHe IHl IHB; simpl; try reflexivity;
    (try rewrite IHe); (try rewrite IHB);
      (try rewrite apply_r_list_refl; eauto); (try rewrite Hyp; eauto).
    - simpl in IHl. inv IHl. rewrite !H1. reflexivity.
  Qed.

  Lemma rename_all_ns_same_set e x :
    rename_all_ns (M.set x x (M.empty var)) e = e.
  Proof.
    eapply rename_all_ns_same_mut.
    intros x1. destruct (peq x x1); subst.
    unfold apply_r. rewrite M.gss. reflexivity.
    unfold apply_r. rewrite M.gso, M.gempty; eauto.
  Qed.

  Lemma num_occur_rename_all_ns :
    forall e x x' (Hlneq : x <> x'),
      num_occur (rename_all_ns (M.set x x' (M.empty var)) e) x 0.
  Proof.
    intros. eapply num_occur_rename_all_ns_kill.
    intros Hc. eapply Range_map_set_list with (xs := [x]) (vs := [x']) in Hc.
    now inv Hc; eauto.
    eapply Dom_map_set. now left.
  Qed.



  Theorem gsr_no_zombie n e1 e2 :
    gen_sr_rw n e1 e2 ->
    no_zombie e1 e2.
  Proof.
    intros. inv H. inv H0; intro;
                     intros;
                     apply num_occur_app_ctx in H0; destructAll; pi0; dec_vars; inv H1; pi0.
    pi0.
    -  apply num_occur_app_ctx. eexists; eauto.
    -  apply num_occur_app_ctx. eexists; eauto.
    -  apply num_occur_app_ctx. eexists; eauto.
    -  apply num_occur_app_ctx. eexists; eauto.
    -  apply fundefs_append_num_occur' in H7. destructAll; pi0.
       inv H2; pi0.
       apply num_occur_app_ctx. eexists 0, 0; eauto.
       split; auto. split; auto.
       rewrite <- Nat.add_0_l.
       constructor; auto.
       rewrite <- Nat.add_0_l.
       eapply fundefs_append_num_occur; eauto.
    - apply num_occur_app_ctx in H7; destructAll; pi0.
      apply num_occur_app_ctx. eexists 0, 0; eauto.
      split; auto. split.
      eapply num_occur_n. constructor.
      apply num_occur_app_ctx. eexists 0, 0; eauto.
      split; auto. split; auto.
      inv H3. rewrite H8.
      apply find_tag_nth_In_patterns in H.
      pi0.
      assert (exists n, num_occur e0 x0 n) by apply e_num_occur.
      destruct H4.
      assert (x1 <= 0).
      eapply num_occur_case_le; eauto.
      apply Nat.le_0_r in H5. subst; auto.
      lia. auto.
    - apply num_occur_app_ctx in H7; destructAll; pi0.
      inv H3; pi0.
      apply num_occur_app_ctx. exists 0, 0; eauto. split; auto.
      split; auto.
      eapply num_occur_n. constructor. apply num_occur_app_ctx.
      exists 0, 0; split; auto. split.
      assert (exists n,  num_occur  (rename_all_ns (M.set v k (M.empty var)) e0) x0 n) by apply e_num_occur.
      destruct H4.
      assert (x1 <= 0).
      eapply num_occur_rename_all_ns_not_range. apply H10.
      apply H4.
      intro. inv H5.
      destruct (var_dec x2 v).
      subst. rewrite M.gss in H6. inv H6.
      apply nthN_In in H.
      apply not_occur_list_not_in in H2.
      auto.
      rewrite M.gso in H6; auto. rewrite M.gempty in H6.
      inv H6.
      apply Nat.le_0_r in H5; subst; auto.

      reflexivity. auto.
    - inv H2; pi0.
      apply num_occur_app_ctx in H9. destructAll; pi0.
      inv H2; pi0.
      eapply fundefs_append_num_occur' in H10.
      destructAll; pi0. dec_vars.
      inv H3; pi0.
      eapply num_occur_app_ctx. exists 0, 0; split; auto.
      split; auto.
      eapply num_occur_n. constructor.
      apply num_occur_app_ctx. exists 0, 0; split; auto.
      split.
      assert (exists n,  num_occur (rename_all_ns (set_list (combine xs vs) (M.empty var)) fb) x n) by apply e_num_occur.
      destruct H3.
      assert (x0 <= 0).
      eapply num_occur_rename_all_ns_not_range. eassumption. eassumption.
      intro Hr. apply Range_map_set_list in Hr.
      apply not_occur_list in Hr; eauto.
      apply Nat.le_0_r in H4. subst; auto.
      reflexivity.
      eapply fundefs_append_num_occur; eauto.
      auto.
    - inv H3; pi0.
      apply num_occur_app_ctx in H8. destructAll; pi0. inv H3; pi0.
      apply num_occur_app_ctx in H10. destructAll; pi0.
      simpl in H6. rewrite peq_true in H6.
      assert (Hx1 : x1 = 0) by lia.
      assert (Hn : n = 0) by lia. assert (Hm : m = 0) by lia. subst.
      eapply fundefs_append_num_occur' in H9. destructAll; pi0.
      eapply fundefs_append_num_occur' in H11. destructAll; pi0. inv H7; destructAll; pi0.
      inv H4. inv H9. destructAll; pi0. dec_vars.
      unfold dead_var, In. replace 0 with (0 + 0) by lia.
      assert (exists n,  num_occur (rename_all_ns (set_list (combine xs vs) (M.empty var)) fb) x0 n) by apply e_num_occur.
      destructAll.
      assert (x1 <= 0).
      { eapply num_occur_rename_all_ns_not_range; [| eassumption |]. eassumption.
        intro Hr. apply Range_map_set_list in Hr.
        apply not_occur_list in Hr; eauto.  } assert (Heq : x1 = 0) by lia. subst.

      assert (exists n,  num_occur (rename_all_ns (M.set x x' (M.empty var)) e1) x0 n) by apply e_num_occur.
      destructAll.

      apply num_occur_app_ctx. do 2 eexists. split; eauto.
      econstructor. econstructor.
      apply num_occur_app_ctx. do 2 eexists. split. eassumption. assert (Hinl := H2).
      eapply num_occur_inline_letapp_leq in H2; [| eassumption ]. destructAll.
      assert (Heq : x2 = 0) by lia. subst.
      split.
      apply num_occur_app_ctx. do 2 eexists. split. eassumption.
      split.
      { destruct (peq x x'); subst.
        + rewrite rename_all_ns_same_set. eassumption.
        + destruct (peq x x0); subst.
          now eapply num_occur_rename_all_ns; eauto.
          destruct (peq x' x0); subst.
          * eapply inline_letapp_var_num_occur in Hinl. inv Hinl; eauto. contradiction.
            destructAll. eapply num_occur_det in H7; [| eapply H18 ]. subst. lia.
          * eapply num_occur_sig_unaffected in H16; eauto.  subst. eassumption.
            intros Hc. eapply Dom_map_set in Hc. rewrite Dom_map_empty in Hc. normalize_sets.
            now inv Hc; eauto. intros Hc.
            eapply (Range_map_set_list [x] [x']) in Hc. inv Hc; eauto. }
      reflexivity. reflexivity.
      eapply fundefs_append_num_occur. reflexivity. eassumption. eassumption. lia.
  Qed.

  (** If a variable is dead in a term, it will be dead in any shrink rewrites of the term *)
  Corollary shrink_no_zombie:
    forall n e1 e2,
      gsr_clos n e1 e2 ->
      no_zombie e1 e2.
  Proof.
    intros n e1 e2 H. unfold no_zombie. induction H.
    - eapply Included_trans. apply gsr_no_zombie in H; auto. eassumption. eassumption.
    - reflexivity.
  Qed.


  (* This is implied by sig_inv_dom in the case where e is also closed. *)
  Definition sig_inv sig e: Prop :=
    forall x y, M.get x sig = Some y ->
                (* dom *) ~ (bound_var e x) /\
                          (* codom *)
                          (num_occur e y  0 \/ bound_var e y).


  (* Strengthening of sig_inv. Need the bound_stem_ctx due to function inlining  *)
  Definition sig_inv_full sig c e: Prop :=
    forall x y, M.get x sig = Some y ->
                (* dom *) ~ (bound_var (c |[e]|) x) /\
                          (* codom *)
                          (num_occur (c |[e ]|) y  0 \/ bound_stem_ctx c y).


  Definition sig_inv_codom sig c e: Prop :=
    forall x y, M.get x sig = Some y ->
                (num_occur (c |[e ]|) y  0 \/ bound_stem_ctx c y).


  Theorem sig_inv_full_push:
    forall sig c c' e,
      sig_inv_full sig c (c' |[ e ]|) ->
      sig_inv_full sig (comp_ctx_f c c') e.
  Proof.
    intros. intro. intros. apply H in H0.
    destruct H0.
    rewrite app_ctx_f_fuse in H0.
    rewrite app_ctx_f_fuse in H1.
    split; auto.
    inv H1. auto.
    right.
    apply bound_stem_comp_ctx_mut.
    auto.
  Qed.

  Theorem sig_inv_full_dead_l:
    forall c c' e sig,
      sig_inv_full sig c (c' |[ e ]|) ->
      sig_inv_full sig c e.
  Proof.
    intros. intro. intros. apply H in H0. destruct H0. split.
    - intro. apply H0. apply bound_var_app_ctx in H2.
      apply bound_var_app_ctx.
      inv H2. auto.
      right;           apply bound_var_app_ctx; auto.
    - inv H1.
      apply num_occur_app_ctx in H2; destructAll; pi0.
      apply num_occur_app_ctx in H2; destructAll; pi0.
      left. apply num_occur_app_ctx. exists 0, 0; auto.
      auto.
  Qed.


  Theorem not_occur_rename_fun_not_dom :
    forall (sig : M.t var) (v : M.elt) (e : fundefs),
      ~ Dom_map sig v -> num_occur_fds (rename_all_fun_ns sig e) v 0 -> num_occur_fds e v 0.
  Proof.
    intros.
    assert (exists n, num_occur_fds e v n) by apply e_num_occur_fds.
    destruct H1.
    assert (x <= 0).
    eapply num_occur_rename_all_not_dom_mut.
    apply H1. apply H0. auto.
    apply Nat.le_0_r in H2. subst; auto.
  Qed.


  (* meaning either get_c y count 0 OR y is bound on the way to the hole [or, weaker, bound somewhere in the term, which is enough to show that Disjoint Dom Codom *)
  Theorem not_free_bound_or_not_occur :
    forall v : var,
      (forall e : exp,  ~ occurs_free e v -> num_occur e v 0  \/ bound_var e v) /\
      (forall f : fundefs, ~ occurs_free_fundefs f v ->  num_occur_fds f v 0 \/ bound_var_fundefs f v).
  Proof.
    intro v.
    apply exp_def_mutual_ind; intros.
    - destruct (var_dec v0 v).
      + right. subst.
        constructor.
      + assert (~ List.In v l).
        intro; apply H0.
        constructor; auto.
        assert (~ (occurs_free e) v).
        intro; apply H0.
        constructor 2; auto.
        apply H in H2. inv H2.
        left.
        apply not_occur_list_not_in in H1.
        eapply num_occur_n. constructor.
        apply H3.
        rewrite H1. auto.
        right.
        apply bound_var_Econstr.
        left; auto.
    - left.
      eapply num_occur_n.
      constructor.
      constructor.
      simpl.
      destruct (term_util.var_dec v v0).
      exfalso; apply H.
      subst. constructor.
      auto.
    - assert (~occurs_free e v).
      intro; apply H1.
      constructor. auto.
      assert (~ occurs_free (Ecase v0 l) v).
      intro; apply H1.
      apply Free_Ecase3. auto.
      apply H in H2.
      apply H0 in H3.
      inv H2.
      inv H3.
      left.
      inv H2. rewrite H8.
      eapply num_occur_n.
      constructor. constructor.
      apply H4. apply H7.
      simpl. destruct (term_util.var_dec v v0).
      inv H8.
      auto.
      right.
      apply bound_var_Ecase_cons. right; auto.
      right. apply bound_var_Ecase_cons. auto.
    - destruct (var_dec v0 v).
      right; subst; constructor.
      assert (~ occurs_free e v).
      intro; apply H0.
      constructor. auto. auto.
      apply H in H1.
      destruct H1. left.
      eapply num_occur_n.
      constructor; eauto.
      simpl.
      destruct (term_util.var_dec v v1).
      exfalso; apply H0; subst; constructor.
      auto.
      right; auto.
    - destruct (var_dec x v).
      + right. subst. constructor.
      + assert (~ List.In v (f :: ys)).
        { intros Hc. eapply H0; eauto. }
        assert (~ (occurs_free e) v).
        { intro; apply H0. eapply Free_Eletapp2; eauto. }
        eapply H in H2. inv H2.
        left.
        apply not_occur_list_not_in in H1.
        eapply num_occur_n. constructor; eauto. lia.
        right. econstructor. eassumption.
    - assert ( ~ occurs_free_fundefs f2 v).
      intro.
      apply H1.
      apply Free_Efun2. auto.
      assert (Hf2 := Decidable_name_in_fundefs f2).
      destruct Hf2.
      specialize (Dec v).
      destruct Dec as [Hin | Hnin].
      + right. constructor. apply name_in_fundefs_bound_var_fundefs. auto.
      + assert (~ occurs_free e v).
        intro.
        apply H1.
        constructor; auto.
        apply H0 in H3.
        apply H in H2.
        inv H3.
        inv H2.
        left.
        eapply num_occur_n. constructor; eauto. auto.
        right; auto.
        right; auto.
    - left.
      eapply num_occur_n. constructor.
      simpl.
      destruct (term_util.var_dec v v0).
      exfalso; apply H; subst; auto.
      apply not_occur_list_not_in.
      intro; apply H.
      constructor.
      auto.
    - destruct (var_dec v0 v).
      + right. subst.
        constructor.
      + assert (~ (occurs_free e) v).
        intro; apply H0.
        apply Free_Eprim_val; auto.
        apply H in H1 as []. left. now constructor.
        right. now constructor.
    - destruct (var_dec v0 v).
      + right. subst.
        constructor.
      + assert (~ List.In v l).
        intro; apply H0.
        constructor; auto.
        assert (~ (occurs_free e) v).
        intro; apply H0.
        apply Free_Eprim2; auto.
        apply H in H2.  inv H2.
        left.
        apply not_occur_list_not_in in H1.
        eapply num_occur_n. constructor.
        apply H3.
        rewrite H1. auto.
        right.
        apply bound_var_Eprim.
        left; auto.
    - left.
      eapply num_occur_n.
      constructor.
      simpl.
      destruct (term_util.var_dec v v0).
      exfalso; apply H; subst; auto.
      auto.
    - destruct (var_dec v0 v).
      right; subst; auto.
      assert (Hl := Decidable_FromList l).
      inv Hl. specialize (Dec v). inv Dec.
      right.
      constructor. right; auto.
      assert (Hf5 := Decidable_name_in_fundefs f5).
      destruct Hf5; specialize (Dec v); inv Dec.
      right. constructor 2. apply name_in_fundefs_bound_var_fundefs. auto.
      assert (~ occurs_free e v).
      intro; apply H1.
      constructor; auto.
      apply H in H4.
      assert (~ occurs_free_fundefs f5 v).
      intro; apply H1.
      constructor 2; auto.
      apply H0 in H5.
      destruct H4.
      destruct H5.
      left.
      eapply num_occur_fds_n.
      constructor; eauto. auto.
      right.
      constructor 2. auto.
      right. auto.
    - left; constructor.
  Qed.

  Theorem Disjoint_Setminus_swap:
    forall {A} s1 s2 s3,
      Disjoint A (Setminus _ s1 s2) s3 <-> Disjoint A s1 (Setminus _ s3 s2).
  Proof.
    intros. split; intro.
    - split; intro; intro.
      inv H. specialize (H1 x).
      apply H1.
      inv H0.
      inv H2.
      split;
        eauto with Ensembles_DB.
      split; auto.
    - split; intro; intro.
      inv H.
      inv H0.
      specialize (H1 x).
      inv H.
      apply H1. split.
      auto.
      split; auto.
  Qed.


  Theorem Disjoint_Dom_map_funs f2 sig s :
    Disjoint _ (Dom_map sig) (Setminus _ s (name_in_fundefs f2)) ->
    Disjoint M.elt (Dom_map (remove_all sig (all_fun_name f2))) s.
  Proof.
    intros.
    rewrite Dom_map_remove_all.
    apply Disjoint_Setminus_swap.
    rewrite Same_set_all_fun_name in H.
    auto.
  Qed.


  Theorem Disjoint_dom_rename_all:
    (forall  e sig,
       Disjoint _ (Dom_map sig) (occurs_free e) ->
       rename_all sig e = e) /\
    (forall f sig,
       Disjoint _ (Dom_map sig) (occurs_free_fundefs f :|: name_in_fundefs f) ->
       rename_all_fun sig f = f).
  Proof.
    apply exp_def_mutual_ind; intros; repeat normalize_occurs_free_in_ctx; simpl.
    - rewrite H.
      rewrite Disjoint_apply_r_FromList.
      reflexivity.
      eapply Disjoint_Included_r.
      2: apply H0. auto with Ensembles_DB.
      rewrite Dom_map_remove.
      split.
      intros. intro.
      inv H1.
      destruct (var_dec v x). subst.
      inv H2. apply H4. auto.
      inv H0. specialize (H1 x).
      apply H1. split.
      apply H2.
      right.
      split; auto.
      intro; apply n.
      inv H0. auto.
    - rewrite Disjoint_apply_r; auto.
    - assert ( Disjoint M.elt (Dom_map sig) (occurs_free (Ecase v l)) ).
      eauto with Ensembles_DB.
      apply H0 in H2.
      simpl in H2.
      inversion H2.
      rewrite  H4.
      rewrite H4.
      rewrite H5.
      rewrite H5.
      rewrite H; auto with Ensembles_DB.
    - rewrite Disjoint_apply_r.
      rewrite H; auto.
      rewrite Dom_map_remove.
      rewrite Disjoint_Setminus_swap.
      eapply Disjoint_Included_r.
      2: apply H0.
      right; auto.
      eapply Disjoint_Included_r.
      2: apply H0.
      left; auto.
    - rewrite H.
      rewrite Disjoint_apply_r_FromList.
      rewrite Disjoint_apply_r. reflexivity. sets. sets.
      rewrite Dom_map_remove. sets.
      eapply Disjoint_sym. eapply Disjoint_Setminus_swap. sets.
    - rewrite H. rewrite H0. reflexivity.
      apply Disjoint_Dom_map_funs. sets.
      apply Disjoint_Dom_map_funs. sets.
    - rewrite Disjoint_apply_r.
      rewrite Disjoint_apply_r_FromList.
      auto.
      eauto with Ensembles_DB.
      eauto with Ensembles_DB.
    - rewrite H; auto.
      rewrite Dom_map_remove.
      now rewrite Disjoint_Setminus_swap.
    - rewrite Disjoint_apply_r_FromList.
      rewrite H.
      auto.
      rewrite Dom_map_remove.
      rewrite Disjoint_Setminus_swap.
      auto with Ensembles_DB.
      auto with Ensembles_DB.
    - rewrite Disjoint_apply_r. reflexivity. sets.
    - rewrite H. rewrite H0.
       auto.
       { simpl in H1.
         split; intro; intro.
         inv H2.
         inv H1.
         specialize (H2 x).
         apply H2.
         destruct (var_dec x v).
         subst; auto.
         inv H4.
         split. auto.
         left.
         right. split; auto. intro; apply n.
         inv H4; auto.
         split; auto.
       }
       simpl in H1.
       rewrite Dom_map_remove_all.
       rewrite Disjoint_Setminus_swap.
       eapply Disjoint_Included_r.
       2: apply H1.
       intro.
       intro.
       assert (Hd := Decidable_name_in_fundefs f5).
       inv Hd.
       specialize (Dec x).
       inv Dec;
         auto with Ensembles_DB.
       destruct (var_dec x v).
       right. subst; left; auto.
       left.
       inv H2.
       left.
       split; auto.
       intro.
       inv H2; auto.
       inv H6; auto.
       inv H6; auto.
    - reflexivity.
  Qed.


  (* split sig_inv into the comps *)
  Definition sig_inv_dom (sig:r_map) e: Prop :=
    forall x y, M.get x sig = Some y -> ~ (bound_var e x).



  Theorem sig_inv_combine:
    forall sig c e,
      sig_inv_dom sig (c |[e ]|) /\
      sig_inv_codom sig c e <->
      sig_inv_full sig c e.
  Proof.
    intros.
    split; intro; intros.
    - intro. intros.
      inv H.
      assert (H0' := H0).
      apply H1 in H0.
      apply H2 in H0'.
      auto.
    - split; intro; intros.
      + apply H in H0. inv H0; auto.
      + apply H in H0. inv H0; auto.
  Qed.

  Definition sig_inv_dom_fundefs (sig:r_map) fds: Prop :=
    forall x y, M.get x sig = Some y ->
                ~ (bound_var_fundefs fds x).


  Definition sig_inv_dead (sig:r_map) e :Prop :=
    forall x y, M.get x sig = Some y ->
                num_occur e x 0.

  Theorem inl_inv_mon:
    forall e' e im sub ,
      Included _ (bound_var e') (bound_var e) ->
      inl_inv im sub e ->
      inl_inv im sub e'.
  Proof.
    intros; intro; intros.
    apply H0 in H1; destructAll.
    split; intro; intros.
    - apply H1. apply H; auto.
    - apply H2 in H3.
      eapply Disjoint_Included_l.
      2: apply H3. auto.
  Qed.


  Theorem sig_inv_dom_mon:
    forall e' e sig,
      Included _ (bound_var e') (bound_var e) ->
      sig_inv_dom sig e ->
      sig_inv_dom sig e'.
  Proof.
    intros. intro; intros.
    apply H0 in H1.
    intro.
    apply H1.
    apply H. auto.
  Qed.

    Theorem rename_all_no_shadow:
    forall sig,
      (forall e,
          sig_inv_dom sig e ->
          rename_all sig e = rename_all_ns sig e) /\
      (forall fds,
          sig_inv_dom_fundefs sig fds ->
          rename_all_fun sig fds = rename_all_fun_ns sig fds).
  Proof.
    intros. split; intros; eapply Disjoint_dom_rename_all_eq; split; intro; intro; inv H0; inv H1; apply H in H0; auto.
  Qed.

  Lemma rename_all_ns_empty:
    (forall e, e = rename_all_ns (M.empty var) e) /\
    (forall fds, fds = rename_all_fun_ns (M.empty var) fds).
  Proof.
    split; intros.
    rewrite <- (proj1 (rename_all_no_shadow _)).
    apply rename_all_empty.
    intro. intros. rewrite M.gempty in H. inv H.
    rewrite <- (proj2 (rename_all_no_shadow _)).
    apply rename_all_empty.
    intro. intros. rewrite M.gempty in H. inv H.
  Qed.

  Theorem dsubterm_num_occur:
    (forall {e' e} {x} {n m},
       dsubterm_e e e' ->
       num_occur e' x n ->
       num_occur e x m ->
       m <= n) /\
    (forall {f} {e} {x} {n m},
       dsubterm_fds_e e f ->
       num_occur_fds f x n ->
       num_occur e x m ->
       m <= n).
  Proof.
    eapply exp_def_mutual_ind; intros.
    - inv H0; inv H1.
      assert (m = n0).
      eapply (proj1 (num_occur_det _)); eauto.
      lia.
    - inv H.
      inv H4.
    - inv H2.
      inv H8.
      inv H1.
      inv H5.
      + inv H1.
        assert (m = n).
        eapply (proj1 (num_occur_det _)); eauto.
        lia.
      + assert (m <=  num_occur_list [v] x + m0).
        eapply H0.
        eapply dsubterm_case.
        apply H1.
        constructor; auto.
        auto.
        lia.
    - inv H0; inv H1.
      assert (m = n1).
      eapply (proj1 (num_occur_det _)); eauto.
      lia.
    - inv H0; inv H1.
      assert (m = n0).
      eapply (proj1 (num_occur_det _)); eauto.
      lia.
    - inv H2.
      inv H1.
      specialize (H _ _ _ _ H5 H9 H3).
      lia.
      assert (n0 = m).
      eapply (proj1 (num_occur_det _)); eauto.
      lia.
    - inv H.
    - inv H1. inv H0.
      assert (n = m).
      eapply (proj1 (num_occur_det _)); eauto. lia.
    - inv H0; inv H1.
      assert (m = n0).
      eapply (proj1 (num_occur_det _)); eauto.
      lia.
    - inv H.
    - inv H2.
      inv H1.
      + assert (m = n0).
        eapply (proj1 (num_occur_det _)); eauto.
        lia.
      + specialize (H0 _ _ _ _ H5 H12 H3).
        lia.
    - inv H.
  Qed.

  Theorem rename_sig_dead:
    forall {sig} {e},
      sig_inv_dead sig e ->
      rename_all sig e = e.
  Proof.
    intros.
    apply Disjoint_dom_rename_all.
    split. intro. intro.
    inv H0.
    inv H1. apply H in H0.
    revert H2.
    apply not_occurs_not_free. auto.
  Qed.


  Theorem init_census_correct:
    (forall e, c_count e (init_census e)) /\
    forall f, c_count_f f (init_census_f f).
  Proof.
    eapply exp_def_mutual_ind; intros; intro vv;
    assert (Hcpc := combine_plus_census_correct).
    - specialize (H vv).
      unfold init_census. simpl.
      eapply num_occur_constr.
      constructor. eauto.
      destructAll.
      rewrite <- H0.
      rewrite gccombine'.
      rewrite update_census_list_correct.
      rewrite gdempty. rewrite apply_r_list_empty.
      rewrite <- (proj1 rename_all_ns_empty).
      lia.
    - unfold init_census.
      simpl.
      rewrite apply_r_empty.
      eapply num_occur_constr.
      constructor. constructor.
      simpl. destruct (term_util.var_dec vv v).
      subst.
      rewrite gdss. auto.
      rewrite gdso by auto.
      rewrite gdempty.
      auto.
    - unfold init_census; simpl.
      specialize (H0 vv).
      inversion H0; subst.
      eapply num_occur_constr.
      constructor. constructor; eauto.
      unfold init_census in H5.
      simpl.
      simpl in H5.
      rewrite apply_r_empty in *.
      destruct Hcpc.
      rewrite <- H1.
      rewrite gccombine'.
      rewrite <- H5.
      rewrite <- (proj1 rename_all_ns_empty).
      lia.
    - unfold init_census; simpl.
      eapply num_occur_constr.
      constructor. apply H.
      destruct Hcpc. rewrite <- H0.
      rewrite gccombine'.
      rewrite apply_r_empty.
      rewrite <- (proj1 rename_all_ns_empty).
      simpl. destruct (term_util.var_dec vv v0). subst; rewrite gdss. auto.
      rewrite gdso by auto.
      rewrite gdempty. auto.
    - specialize (H vv).
      unfold init_census. simpl.
      eapply num_occur_constr.
      constructor. eassumption.
      destructAll.
      rewrite <- H0.
      rewrite gccombine'.
      rewrite update_census_list_correct.
      rewrite apply_r_list_empty.
      rewrite <- (proj1 rename_all_ns_empty). rewrite !apply_r_empty.
      simpl. destruct (term_util.var_dec vv f).
      + subst. unfold get_c at 2. rewrite M.gss. lia.
      + subst. unfold get_c at 2. rewrite M.gso, M.gempty; eauto.
    - unfold init_census; simpl.
      eapply num_occur_constr.
      constructor; auto.
      destruct Hcpc.
      rewrite <- H1. rewrite gccombine'.
      rewrite <- (proj1 rename_all_ns_empty).
      unfold init_census_f. apply Nat.add_comm.
    - eapply num_occur_constr.
      constructor.
      unfold init_census. simpl.
      rewrite apply_r_empty.
      rewrite update_census_list_correct.
      rewrite apply_r_list_empty.
      destruct (term_util.var_dec vv v).
      subst; rewrite gdss. rewrite ?gdempty. auto.
      rewrite gdso by auto. rewrite gdempty. auto.
    - unfold init_census; simpl.
      eapply num_occur_constr. constructor; auto.
      destruct Hcpc.
      rewrite <- H0.
      rewrite gccombine'.
      rewrite <- (proj1 rename_all_ns_empty).
      rewrite gdempty.
      now simpl.
    - unfold init_census; simpl. eapply num_occur_constr.
      constructor; auto.
      destruct Hcpc.
      rewrite <- H0.
      rewrite gccombine'.
      rewrite update_census_list_correct.
      rewrite <- (proj1 rename_all_ns_empty).
      rewrite apply_r_list_empty.
      rewrite gdempty.
      simpl.
      apply Nat.add_comm.
    - unfold init_census.
      eapply num_occur_constr.
      constructor.
      simpl.
      rewrite ?gdempty.
      rewrite apply_r_empty.
      simpl.
      destruct (term_util.var_dec vv v).
      subst; rewrite gdss. auto.
      rewrite gdso by auto.
      rewrite gdempty.
      auto.
    - unfold init_census_f; simpl.
      eapply num_occur_fds_constr.
      constructor; auto.
      destruct Hcpc.
      rewrite <- H2.
      rewrite gccombine'.
      rewrite <- (proj2 rename_all_ns_empty).
      auto.
    - unfold init_census_f. simpl. rewrite gdempty. constructor.
  Qed.


  (** dec_census removes the occurences of variables in (sig m) from their tally in count *)
  Theorem combine_minus_census_correct:
    (forall  m count sig,
        map_getd_r _ 0 (M.combine (f_opt_d 0 minus) count (init_census (rename_all_ns sig m))) (update_census sig m c_minus count)) /\
    (forall f count sig,   map_getd_r _ 0 (M.combine (f_opt_d 0 minus) count (update_census_f (M.empty var) (rename_all_fun_ns sig f) c_plus (M.empty nat))) (update_census_f sig f c_minus count)).
  Proof.
    eapply exp_def_mutual_ind; intros; simpl.
    - intro. rewrite gccombine_sub.
      rewrite <- H.
      rewrite gccombine_sub.
      unfold init_census.
      simpl.
      rewrite <- combine_minus_census_list.
      rewrite gccombine_sub.
      assert (Hfr := init_census_f_ar).
      destruct (Hfr c_plus). intros.  simpl. rewrite H0. auto.
      rewrite H0.
      assert (Hcc := combine_plus_census_correct).
      destruct Hcc.
      rewrite <- H2.
      rewrite gccombine'.
      unfold init_census.
      lia.
    - intro.
      rewrite gccombine_sub.
      unfold init_census.
      simpl.
      rewrite ?gdempty.
      simpl.
      rewrite apply_r_empty.
      rewrite get_c_minus.
      reflexivity.
    - intro.
      rewrite gccombine_sub.
      unfold init_census.
      simpl.
      simpl in H0. unfold init_census in H0. simpl in H0.
      rewrite init_census_plus_ar.
      erewrite proper_minus_census_d.
      2:{ apply smgd_sym. apply H0. }
      rewrite <- H.
      rewrite gccombine_sub.
      rewrite gccombine_sub.
      assert (Hcc := combine_plus_census_correct).
      destruct Hcc.
      rewrite <- H1.
      rewrite gccombine'.
      lia.
    - unfold init_census.
      simpl. intro. rewrite gccombine_sub.
      rewrite <- H.
      rewrite gccombine_sub.
      rewrite init_census_plus_ar.
      assert (H' := combine_plus_census_correct).
      destruct H'.
      rewrite <- H0.
      rewrite gccombine'.
      rewrite apply_r_empty.
      rewrite get_c_minus. lia.
    - intro. rewrite gccombine_sub.
      rewrite <- H.
      rewrite gccombine_sub.
      rewrite <- combine_minus_census_list.
      rewrite gccombine_sub.
      unfold init_census. simpl.
      assert (Hcc := combine_plus_census_correct).
      destruct Hcc.
      rewrite <- H0. rewrite gccombine'.

      rewrite <- combine_plus_census_list.
      rewrite gccombine'.
      rewrite apply_r_empty.
      rewrite apply_r_list_empty.

      rewrite get_c_minus.
      assert (Hfr := init_census_f_ar).

      destruct (Hfr c_plus). 1:{ intros. simpl. rewrite H2. auto. }
      rewrite <- (proj1 (rename_all_ns_empty)).
      unfold init_census.
      simpl. lia.
    - intro.
      rewrite gccombine_sub.
      unfold init_census. simpl.
      rewrite init_census_plus_ar.
      rewrite <- H0.
      rewrite gccombine_sub.
      symmetry.
      assert (H' := combine_plus_census_correct).
      destruct H'.
      rewrite <- H1.
      rewrite gccombine'.
      rewrite <- H2.
      rewrite gccombine'.
      rewrite <- (proj2 rename_all_ns_empty).
      rewrite <- H.
      rewrite gccombine_sub.
      unfold init_census.
      rewrite gdempty.
      lia.
    - intro.
      rewrite gccombine_sub.
      rewrite <- combine_minus_census_list.
      rewrite gccombine_sub.
      unfold init_census. simpl.
      rewrite <- combine_plus_census_list.
      rewrite gccombine'.
      rewrite apply_r_empty.
      rewrite apply_r_list_empty.
      rewrite get_c_minus.
      lia.
    - intro.
      rewrite gccombine_sub.
      unfold init_census. simpl.
      rewrite <- H.
      rewrite gccombine_sub.
      assert (H' := combine_plus_census_correct).
      destruct H'.
      rewrite <- H0.
      rewrite gccombine'.
      symmetry.
      rewrite <- (proj1 rename_all_ns_empty).
      simpl. lia.
    - intro.
      rewrite gccombine_sub.
      unfold init_census. simpl.
      rewrite <- H.
      rewrite gccombine_sub.
      assert (H' := combine_plus_census_correct).
      destruct H'.
      rewrite <- H0.
      rewrite gccombine'.
      symmetry.
      rewrite <- combine_minus_census_list.
      rewrite gccombine_sub.
      rewrite <- (proj1 rename_all_ns_empty).
      lia.
    - intro.
      rewrite gccombine_sub.
      rewrite get_c_minus. unfold init_census. simpl. rewrite apply_r_empty. lia.
    - intro; rewrite gccombine_sub.
      rewrite <- H0.
      rewrite gccombine_sub.
      rewrite init_census_plus_ar_f.
      assert (H' := combine_plus_census_correct).
      destruct H'.
      rewrite <- H2.
      rewrite gccombine'.
      symmetry. rewrite <- H. rewrite gccombine_sub. unfold init_census.
      lia.
    - intro.
      rewrite gccombine_sub.
      rewrite gdempty.
      rewrite Nat.sub_0_r. reflexivity.
  Qed.


  Theorem rename_all_ns_app_ctx:
    forall e sig,
      (forall c,
         rename_all_ns sig (c |[ e]|) =
         (rename_all_ctx_ns sig c) |[rename_all_ns sig e ]|) /\
      (forall fc,
         rename_all_fun_ns sig (fc <[ e]>) =
         (rename_all_fun_ctx_ns sig fc) <[rename_all_ns sig e ]>).
  Proof.
    intros.
    exp_fundefs_ctx_induction IHc IHfc; simpl; auto; try (rewrite IHc; auto); try (rewrite IHfc; auto).
    intro.
    rewrite list_append_map.
    simpl.
    rewrite IHc; auto.
  Qed.


  Theorem rename_all_ctx_ns_comp_ctx:
    forall c' sig,
      (forall c,
         rename_all_ctx_ns sig (comp_ctx_f c c') =
         comp_ctx_f (rename_all_ctx_ns sig c) (rename_all_ctx_ns sig c')) /\
      (forall fc,
         rename_all_fun_ctx_ns sig (comp_f_ctx_f fc c') =
         comp_f_ctx_f (rename_all_fun_ctx_ns sig fc) (rename_all_ctx_ns sig c')).
  Proof.
    intros.
    exp_fundefs_ctx_induction IHc IHfc; simpl; auto; try (rewrite IHc; auto); try (rewrite IHfc; auto).
  Qed.



  Theorem rename_all_ns_fundefs_append:
    forall sig B2 B1,
      rename_all_fun_ns sig (fundefs_append B1 B2) =
      fundefs_append (rename_all_fun_ns sig B1) (rename_all_fun_ns sig B2).
  Proof.
    induction B1; simpl; auto.
    rewrite IHB1. auto.
  Qed.


  Theorem all_fun_name_append:
    forall B2 B1,
      all_fun_name (fundefs_append B1 B2) = all_fun_name B1 ++ all_fun_name B2.
  Proof.
    induction B1; auto.
    simpl.
    rewrite IHB1. auto.
  Qed.


  (* push rename_all_ns and inlined_ctx down *)
  Ltac normalize_ctx :=
    match goal with
      (* rename_all *)
      | [H: context[rename_all_ns _ (_ |[ _ ]|)] |- _] =>
        rewrite (proj1 (rename_all_ns_app_ctx _ _)) in H
      | [H: context[rename_all_fun_ns _ (_ <[ _ ]>)] |- _] =>
        rewrite (proj2 (rename_all_ns_app_ctx _ _)) in H
      | [|- context[rename_all_ns _ (_ |[ _ ]|)]] =>
        rewrite (proj1 (rename_all_ns_app_ctx _ _))
      | [|- context[rename_all_fun_ns _ (_ <[ _ ]>)]] =>
        rewrite (proj2 (rename_all_ns_app_ctx _ _))
      | [H: context[rename_all_fun_ns _ (fundefs_append _ _)] |- _] =>
        rewrite rename_all_ns_fundefs_append in H
      | [|- context[rename_all_fun_ns _ (fundefs_append _ _)]] =>
        rewrite rename_all_ns_fundefs_append
      | [H: context[rename_all_ctx_ns _ (comp_ctx_f _ _)] |- _] =>
        rewrite (proj1 (rename_all_ctx_ns_comp_ctx _ _)) in H
      | [|- context[rename_all_ctx_ns _ (comp_ctx_f _ _)]] =>
        rewrite (proj1 (rename_all_ctx_ns_comp_ctx _ _))
      | [H: context[rename_all_fun_ctx_ns _ (comp_f_ctx_f _ _)] |- _] =>
        rewrite (proj2 (rename_all_ctx_ns_comp_ctx _ _)) in H
      | [|- context[rename_all_fun_ctx_ns _ (comp_f_ctx_f _ _)]] =>
        rewrite (proj2 (rename_all_ctx_ns_comp_ctx _ _))

      (* inlined *)
      | [H: context[ inlined_ctx_f (comp_ctx_f _ _ ) _ ] |- _] =>
        rewrite (proj1 (inlined_comp_ctx)) in H
      | [|-context[ inlined_ctx_f (comp_ctx_f _ _) _]] =>
        rewrite (proj1 (inlined_comp_ctx))
      | [H: context[ inlined_fundefs_ctx_f (comp_f_ctx_f _ _) _] |- _] =>
        rewrite (proj2 (inlined_comp_ctx)) in H
      | [|-context[ inlined_fundefs_ctx_f (comp_f_ctx_f _ _) _]] =>
        rewrite (proj2 (inlined_comp_ctx))
      | [H: context[ inlined_fundefs_f (fundefs_append _ _) _] |- _] =>
        rewrite inlined_fundefs_append in H
      | [|-context[ inlined_fundefs_f (fundefs_append _ _) _]] =>
        rewrite inlined_fundefs_append
    end.

  (* TODO move *)
  Definition closed_fundefs :=
    fun f => Empty_set var <--> occurs_free_fundefs f.

  Corollary closed_app_ctx:
    forall e c,
      closed_exp (c |[ e ]|) ->
      closed_ctx c.
  Proof.
    intros.
    assert (Hc := occurs_free_included_ctx e c).
    apply Included_Empty_set_l.
    unfold closed_exp in H. rewrite H in Hc; eauto.
  Qed.

  Theorem not_free_dead_or_bound e:
      (Complement _ (occurs_free e)) \subset ((dead_var e) :|: (bound_var e)).
  Proof.
    intros.
    intro. intro.
    apply not_free_bound_or_not_occur in H.
    destruct H; auto.
  Qed.

  Theorem not_bound_dead_or_free e :
    (Complement _ (bound_var e)) \subset ((dead_var e) :|: (occurs_free e)).
  Proof.
    intros.
    intro; intro.
    assert (He := Decidable_occurs_free e).
    inv He. specialize (Dec x).
    inv Dec; auto.
    apply not_free_dead_or_bound in H0.
    inv H0; auto.
    exfalso. auto.
  Qed.


  Theorem name_in_bound_var_fundefs_ctx cf :
    names_in_fundefs_ctx cf \subset bound_var_fundefs_ctx cf.
  Proof.
    induction cf; simpl; normalize_bound_var_ctx; auto with Ensembles_DB.
    intro. intro. inv H. auto.
    apply name_in_fundefs_bound_var_fundefs in H0.
    auto.
  Qed.

  Theorem not_free_bound_or_not_occur_ctx v:
      (forall c : exp_ctx, ~ occurs_free_ctx c v -> num_occur_ec c v 0 \/ bound_var_ctx c v) /\
      (forall cf : fundefs_ctx, ~ occurs_free_fundefs_ctx cf v -> num_occur_fdc cf v 0 \/ bound_var_fundefs_ctx cf v).
  Proof.
    exp_fundefs_ctx_induction IHc IHf; intros; eauto with Ensembles_DB.
    - left. constructor.
    - destruct (var_dec v0 v).
      + right; subst; auto.
      + assert (~occurs_free_ctx e v).
        intro; apply H.
        constructor 2; auto.
        apply IHc in H0.
        inv H0.
        * left.
          eapply num_occur_ec_n.
          constructor. apply H1.
          assert (~ FromList l v).
          intro; apply H.
          auto.
          apply not_occur_list_not_in in H0. rewrite H0; auto.
        * right; auto.
    -  destruct (var_dec v0 v).
       + right; subst; auto.
       +  assert (~occurs_free_ctx e v).
          intro; apply H.
          auto.
          apply IHc in H0.
          inv H0.
          * left.
            eapply num_occur_ec_n.
            constructor. apply H1.
            simpl. destruct (term_util.var_dec v v1).
            subst;
              exfalso; apply H; auto.
            auto.
          * right; auto.
    - destruct (var_dec v0 v).
      + right; subst; auto.
      + assert (~occurs_free_ctx e v).
        intro; apply H. eapply Free_ctx_Eletapp2; eauto.
        apply IHc in H0.
        inv H0.
        * left.
          eapply num_occur_ec_n.
          constructor. apply H1.
          assert (~ FromList (f :: ys) v).
          intro; apply H.
          auto.
          apply not_occur_list_not_in in H0. rewrite H0; auto.
        * right; auto.
    - destruct (var_dec v0 v).
       + right; subst; auto.
       +  assert (~occurs_free_ctx e v).
          intro; apply H.
          auto.
          apply IHc in H0.
          inv H0.
          * left.
            now constructor.
          * right; auto.
   - destruct (var_dec v0 v).
      + right; subst; auto.
      +  assert (~occurs_free_ctx e v).
          intro; apply H.
          auto.
          apply IHc in H0.
          inv H0.
          * left.
            eapply num_occur_ec_n.
            constructor. apply H1.
            simpl.
            assert (~ FromList l v).
            intro; apply H.
            auto.
            apply not_occur_list_not_in in H0. rewrite H0; auto.
          * right; auto.
    - assert (~ Union var [set v0]
                (Union var (occurs_free_ctx e)
                       (Union var (occurs_free (Ecase v0 l))
                              (occurs_free (Ecase v0 l0)))) v).
      intro. apply H.
      apply occurs_free_Ecase_c.
      auto.
      assert (v <> v0).
      intro; apply H0; subst;
      left; auto.
      assert (~ occurs_free (Ecase v0 l) v).
      intro; apply H0.
      right; right; left; auto.
      assert (~ occurs_free (Ecase v0 l0) v).
      intro; apply H0.
      right; right; right; auto.
      assert (~(occurs_free_ctx e) v).
      intro; apply H0.
      right; left; auto.
      clear H0.
      apply IHc in H4.
      apply not_free_bound_or_not_occur in H2.
      apply not_free_bound_or_not_occur in H3.
      destruct H2.
      destruct H3.
      destruct H4.
      left.
      inv H0; pi0.
      inv H2; pi0.
      eapply num_occur_ec_n.
      constructor; eauto.
      simpl. destruct (term_util.var_dec v v0). subst; exfalso; auto.
      auto.
      right; auto.
      right; auto.
      inv H2.
      eapply Bound_Case3_c; eauto.
      right.
      inv H0;
        eapply Bound_Case2_c; eauto.
    - assert (Hf4 := Decidable_name_in_fundefs f4).
      destruct Hf4.
      specialize (Dec v).
      inv Dec.
      right.
      constructor.
      apply name_in_fundefs_bound_var_fundefs.
      auto.
      assert (~ occurs_free_ctx e v).
      intro; apply H; auto.
      assert (~ occurs_free_fundefs f4 v).
      intro; apply H. auto.
      apply IHc in H1.
      apply not_free_bound_or_not_occur in H2.
      destruct H1.
      destruct H2.
      left.
      eapply num_occur_ec_n.
      constructor; eauto.
      auto.
      right; auto.
      right; auto.
    - assert (Hf5 := Decidable_name_in_fundefs_ctx f5).
      destruct Hf5.
      specialize (Dec v).
      inv Dec.
      right.
      constructor.
      apply name_in_bound_var_fundefs_ctx. auto.
      assert (~ occurs_free_fundefs_ctx f5 v).
      intro; apply H; auto.
      assert (~ occurs_free e v).
      intro; apply H; auto.
      apply IHf in H1.
      apply not_free_bound_or_not_occur in H2.
      inv H1. inv H2.
      left.
      eapply num_occur_ec_n.
      constructor; eauto. auto.
      right; auto.
      right; auto.
    - destruct (var_dec v0 v).
      right; subst.
      constructor.
      assert (Hl := Decidable_FromList l).
      inv Hl.
      specialize (Dec v).
      inv Dec.
      right; auto.
      assert (Hf6 := Decidable_name_in_fundefs f6).
      destruct Hf6.
      specialize (Dec v).
      inv Dec.
      right. apply name_in_fundefs_bound_var_fundefs in H1. auto.
      assert (~ occurs_free_ctx e v).
      intro; apply H.
      constructor; auto.
      apply IHc in H2.
      assert (~ occurs_free_fundefs f6 v).
      intro; apply H. constructor 2; auto.
      apply not_free_bound_or_not_occur in H3.
      inv H2.
      inv H3.
      left. eapply num_occur_fdc_n.
      constructor; eauto. auto.
      right. auto.
      right. auto.
    - destruct (var_dec v0 v).
      right; subst.
      constructor.
      assert (Hl := Decidable_FromList l).
      inv Hl.
      specialize (Dec v).
      inv Dec.
      right; auto.
      assert (Hf7 := Decidable_name_in_fundefs_ctx f7).
      destruct Hf7.
      specialize (Dec v).
      inv Dec.
      right. apply name_in_bound_var_fundefs_ctx in H1. auto.
      assert (~ occurs_free e v).
      intro; apply H.
      constructor; auto.
      apply not_free_bound_or_not_occur in H2.
      assert (~ occurs_free_fundefs_ctx f7 v).
      intro; apply H. apply Free_ctx_Fcons22; auto.
      apply IHf in H3.
      inv H2.
      inv H3.
      left. eapply num_occur_fdc_n.
      constructor; eauto. auto.
      right. auto.
      right. auto.
  Qed.


  Corollary not_occurs_free_ctx_not_bound c e x :
      ~ occurs_free (c |[ e ]|) x ->
      ~ bound_var_ctx c x ->
      ~ occurs_free e x.
  Proof.
    intros. intro. apply H.
    apply occurs_free_ctx_not_bound; auto.
  Qed.

  Corollary not_occur_free_Efun f e :
    Same_set _
             (Complement _ (occurs_free (Efun f e)))
             (Intersection _ (Complement _ (occurs_free_fundefs f))
                           (Complement _ (Setminus _  (occurs_free e) (name_in_fundefs f)))).
  Proof.
    intros; split; intro; intro.
    -  split.
       intro. apply H.
       apply occurs_free_Efun. auto.
       intro. apply H.
       apply occurs_free_Efun. auto.
    - intro.
      apply occurs_free_Efun in H0.
      inv H.
      inv H0; auto.
  Qed.



  Theorem occurs_free_fundefs_append f1 f2 :
    Same_set _
             (occurs_free_fundefs (fundefs_append f1 f2))
             (Setminus _ (Union _ (occurs_free_fundefs f1) (occurs_free_fundefs f2))  (name_in_fundefs (fundefs_append f1 f2))).
  Proof.
    induction f1; intros.
    -  simpl.
       rewrite occurs_free_fundefs_Fcons.
       rewrite IHf1.
       rewrite occurs_free_fundefs_Fcons.
       assert (Hf := fundefs_append_name_in_fundefs).
       specialize (Hf f1 f2 (fundefs_append f1 f2)).
       specialize (Hf eq_refl).
       split; intro; intro.
       + inv H.
         * inv H0. split.
           left. left. constructor.
           auto. intro. apply H1. rewrite Hf. inv H0; auto. inv H2; auto.
           intro. apply H1. inv H0; auto.
         * inv H0. inv H. inv H0.
           split; auto.
           left. right. split; auto.
           intro. inv H0; auto.
           split. right; auto.
           intro. inv H0; auto.
       + inv H. inv H0.
         inv H.
         inv H0.
         left. split; auto.
         intro.
         inv H0. apply H1. auto.
         inv H3. apply H2. auto.
         apply H1. auto.
         inv H0. right. split. split.
         left; auto.
         intro. apply H1; auto. auto.
         right. split. split.
         right; auto.
         intro; apply H1; auto.
         intro; apply H1; auto.
    - simpl. rewrite occurs_free_fundefs_Fnil.
      assert (Hnn := occurs_free_fundefs_name_in_fundefs_Disjoint f2).
      rewrite Union_Empty_set_neut_l.
      symmetry.
      apply Setminus_Disjoint. sets.
  Qed.

  Theorem not_occurs_free_fundefs_append f1 f2 :
    Same_set _
             (Complement _ (occurs_free_fundefs (fundefs_append f1 f2)))
             (Intersection _ (Complement _ (Setminus _ (occurs_free_fundefs f1) (name_in_fundefs (fundefs_append f1 f2)))) (Complement _ (Setminus _ (occurs_free_fundefs f2) (name_in_fundefs (fundefs_append f1 f2))))).
  Proof.
    intros. split; intro; intro.
    - split. intro. apply H.
      apply occurs_free_fundefs_append.
      inv H0. split; auto.
      intro. apply H.
      apply occurs_free_fundefs_append. inv H0.
      split; auto.
    - intro.
      apply occurs_free_fundefs_append in H0. inv H0.
      inv H.
      inv H1. apply H0; split; auto.
      apply H3; split; auto.
  Qed.


  Theorem not_free_dead_or_bound_ctx c:
    Included _ (Complement _ (occurs_free_ctx c)) (Union _ (dead_var_ctx c) (bound_var_ctx c)).
  Proof.
    intros. intro. intro.
    apply not_free_bound_or_not_occur_ctx in H.
    destruct H; auto.
  Qed.


  Theorem not_bound_dead_or_free_ctx e:
      Included _ (Complement _ (bound_var_ctx e)) (Union _ (dead_var_ctx e) (occurs_free_ctx e)).
  Proof.
    intros.
    intro; intro.
    assert (He := Decidable_occurs_free_ctx e).
    inv He. destruct (Dec x); eauto.
    apply not_free_dead_or_bound_ctx in n.
    inv n; auto.
    exfalso. auto.
  Qed.

  Theorem closed_not_occurs_in_context c v :
      closed_ctx c ->
      ~ bound_var_ctx c v ->
      num_occur_ec c v 0.
  Proof.
    intros.
    assert (~ occurs_free_ctx c v).
    intro.
    apply H in H1.
    inv H1.
    apply not_free_bound_or_not_occur_ctx in H1.
    inv H1; auto.
    exfalso; auto.
  Qed.



  Theorem closed_implies_Disjoint e :
    closed_exp e ->
    Disjoint _ (bound_var e) (occurs_free e).
  Proof.
    intros. split; intro. intro.
    inv H0.
    apply H in H2. inv H2.
  Qed.

  Theorem gsr_preserves_sig_dom n sig ce ce':
      unique_bindings ce ->
      Disjoint var (bound_var ce) (occurs_free ce) ->
      gsr_clos n ce ce' ->
      sig_inv_dom sig ce ->
      sig_inv_dom sig ce'.
  Proof.
    intros Hun Hc Hrw Hsig.
    unfold sig_inv_dom in *. intros x y Hget Hb.
    apply Hsig in Hget. eapply Hget.
    eapply gsr_clos_in_rw in Hrw; eauto. destructAll.
    eapply gr_clos_preserves_bv in Hb. eassumption. eassumption.
  Qed.

  Lemma eq_env_P_antimon {A} S1 S2 rho1 rho2 :
    @eq_env_P A S1 rho1 rho2 ->
    S2 \subset S1 ->
    eq_env_P S2 rho1 rho2.
  Proof.
    firstorder.
  Qed.


  (** rename_all_ns only affects variables which occurs in the term *)
  Theorem eq_P_rename_all_ns :
    (forall e : exp,
     forall sub sub' : maps_util.M.t var,
       eq_env_P (Complement _ (dead_var e)) sub sub' ->
       rename_all_ns sub e = rename_all_ns sub' e) /\
    (forall fds : fundefs,
     forall sub sub' : maps_util.M.t var,
       eq_env_P (Complement _ (dead_var_fundefs fds)) sub sub' ->
       rename_all_fun_ns sub fds = rename_all_fun_ns sub' fds).
  Proof.
    apply exp_def_mutual_ind; intros; simpl.
    - erewrite H.
      2:{ intro. intro. apply H0.
          intro. apply H1. inv H2; pi0; auto. }
      erewrite eq_P_apply_r_list.
      reflexivity.
      intro; intro; apply H0.
      intro. inv H2.
      pi0.
      apply not_occur_list in H3.
      auto.
    - erewrite eq_P_apply_r.
      auto.
      intro; intro; apply H.
      inv H0.
      intro. inv H0.
      destruct (term_util.var_dec x x).
      inv H5.
      apply n0; auto.
    - erewrite H.
      assert  (eq_env_P (Complement var (dead_var (Ecase v l))) sub sub').
      { intro; intro; apply H1; intro.
        inv H3; pi0; auto. inv H7; pi0; auto.
        apply H2. eapply num_occur_n.
        constructor; eauto.
        simpl. destruct (term_util.var_dec x v); auto. }
      apply H0 in H2. simpl in H2. inv H2.
      now eauto.
      intro; intro; apply H1; intro.
      inv H3. inv H7; pi0.
      auto.
    - erewrite eq_P_apply_r.
      erewrite H. reflexivity.
      eapply eq_env_P_antimon. eassumption.
      intros x Hin Hd. inv Hd.
      pi0. dec_vars. eapply Hin. eassumption.
      eapply eq_env_P_antimon. eassumption.
      intros x Hin Hd. inv Hin. inv Hd.
      pi0. dec_vars.
    - erewrite eq_P_apply_r. erewrite eq_P_apply_r_list.
      erewrite H. reflexivity.
      eapply eq_env_P_antimon. eassumption.
      intros z Hin Hd. inv Hd.
      pi0. dec_vars. eapply Hin. eassumption.
      eapply eq_env_P_antimon. eassumption.
      intros z Hin Hd. inv Hd.
      pi0. dec_vars. now eapply not_occur_list; eauto.
      eapply eq_env_P_antimon. eassumption.
      intros z Hin Hd. inv Hd.
      pi0. dec_vars. inv Hin; eauto.
    - erewrite H. erewrite H0.
      auto.
      intro; intro; apply H1.
      intro. inv H3; pi0; auto.
      intro; intro; apply H1.
      intro. inv H3; pi0; auto.
    - erewrite eq_P_apply_r.
      erewrite eq_P_apply_r_list.
      reflexivity.
      intro; intro. apply H. intro. inv H1; pi0; dec_vars.
      apply not_occur_list in H2.
      auto.
      intro; intro. apply H. intro.
      inv H0; inv H1; auto.
      dec_vars; pi0.
    - erewrite H.
      2:{ intro. intro. apply H0.
          intro. apply H1. inv H2; pi0; auto. }
      reflexivity.
    - erewrite H.
      2:{ intro. intro. apply H0.
          intro. apply H1. inv H2; pi0; auto. }
      erewrite eq_P_apply_r_list.
      reflexivity.
      intro; intro; apply H0.
      intro. inv H2.
      pi0.
      apply not_occur_list in H3.
      auto.
    - erewrite eq_P_apply_r.
      auto.
      intro; intro; apply H; intro.
      inv H0. inv H1; pi0; dec_vars.
    - erewrite H.
      erewrite H0; auto.
      intro; intro; apply H1; intro.
      inv H3; pi0; auto.
      intro; intro; apply H1; intro.
      inv H3; pi0; auto.
    - auto.
  Qed.

  Theorem eq_P_rename_all_ctx_ns :
    (forall e : exp_ctx,
     forall sub sub' : maps_util.M.t var,
       eq_env_P (Complement _ (dead_var_ctx e)) sub sub' ->
       rename_all_ctx_ns sub e = rename_all_ctx_ns sub' e) /\
    (forall fds : fundefs_ctx,
     forall sub sub' : maps_util.M.t var,
       eq_env_P (Complement _ (dead_var_fundefs_ctx fds)) sub sub' ->
       rename_all_fun_ctx_ns sub fds = rename_all_fun_ctx_ns sub' fds).
  Proof.
    exp_fundefs_ctx_induction IHc IHfdc; intros; simpl; auto.
    - erewrite IHc.
      erewrite eq_P_apply_r_list.
      auto.
      intro; intro; apply H; intro.
      inv H1; pi0.
      apply not_occur_list in H1. auto.
      intro; intro; apply H; intro.
      inv H1; pi0. auto.
    - erewrite IHc.
      erewrite eq_P_apply_r.
      auto.
      intro; intro; apply H; intro; inv H1; pi0; dec_vars. inv H0; auto.
      intro; intro; apply H; intro; inv H1; pi0; auto.
    - erewrite IHc, eq_P_apply_r_list, eq_P_apply_r. reflexivity.
      eapply eq_env_P_antimon. eassumption.
      intros x Hin Hd. inv Hd.
      pi0. dec_vars. inv Hin; eauto.
      eapply eq_env_P_antimon. eassumption.
      intros x Hin Hd. inv Hd.
      pi0. dec_vars. eapply not_occur_list; eauto.
      eapply eq_env_P_antimon. eassumption.
      intros x Hin Hd. inv Hd.
      pi0. dec_vars. eapply Hin. eassumption.
    - erewrite IHc. auto.
      intro. intros. apply H. intro. inv H1; pi0.
      apply H0. apply H7.
    - erewrite IHc.
      erewrite eq_P_apply_r_list.
      auto.
      intro; intro; apply H; intro.
      inv H1; pi0.
      apply not_occur_list in H1. auto.
      intro; intro; apply H; intro.
      inv H1; pi0. apply H0. apply H7.
    - assert (rename_all_ns sub (Ecase v l) = rename_all_ns sub' (Ecase v l)).
      erewrite (proj1 eq_P_rename_all_ns).
      reflexivity.
      intro; intro; apply H; intro. inv H1; pi0; dec_vars. apply H0.
      eapply num_occur_n.
      constructor; eauto.
      simpl. destruct (term_util.var_dec x v); eauto. now exfalso; auto.
      assert (rename_all_ns sub (Ecase v l0) = rename_all_ns sub' (Ecase v l0)).
      erewrite (proj1 eq_P_rename_all_ns).
      reflexivity.
      intro; intro; apply H; intro. inv H2; pi0; dec_vars. apply H1.
      eapply num_occur_n.
      constructor; eauto.
      simpl. destruct (term_util.var_dec x v); eauto. now exfalso; auto.
      simpl in *. inv H0; inv H1.
      erewrite IHc. reflexivity.
      intro; intro; apply H; intro.
      inv H1; pi0; auto.
    - erewrite IHc.
      erewrite (proj2 eq_P_rename_all_ns).
      auto.
      intro; intro; apply H; intro; inv H1; pi0; auto.
      intro; intro; apply H; intro; inv H1; pi0; auto.
    - erewrite IHfdc.
      erewrite (proj1 eq_P_rename_all_ns).
      auto.
      intro; intro; apply H; intro; inv H1; pi0; auto.
      intro; intro; apply H; intro; inv H1; pi0; auto.
    - erewrite IHc.
      erewrite (proj2 eq_P_rename_all_ns).
      auto.
      intro; intro; apply H; intro; inv H1; pi0; auto.
      intro; intro; apply H; intro; inv H1; pi0; auto.
    - erewrite IHfdc.
      erewrite (proj1 eq_P_rename_all_ns).
      auto.
      intro; intro; apply H; intro; inv H1; pi0; auto.
      intro; intro; apply H; intro; inv H1; pi0; auto.
  Qed.

  Theorem eq_P_set_list_not_in:
    forall {A} (rho:M.t A) l l',
      eq_env_P (Complement _ (FromList l)) (set_list (combine l l') rho) rho.
  Proof.
    induction l.
    - intros; intro; intros. simpl. reflexivity.
    - intros l' x Hl.
      simpl. destruct l'.
      simpl; auto.
      simpl.
      rewrite M.gso. apply IHl. intro; apply Hl. constructor 2. auto.
      intro; apply Hl; subst.
      constructor. auto.
  Qed.

  Theorem cmap_view_case:
    forall sub c x cl1 c0 cl2,
      cmap_view_ctx sub c ->
      cmap_view_ctx sub (comp_ctx_f c (Ecase_c x cl1 c0 Hole_c cl2)).
  Proof.
    intros.
    split; intros; split; intros.
    - apply H in H0.
      destructAll.
      eexists; eexists; eauto.
      rewrite comp_ctx_f_assoc.
      simpl.
      reflexivity.
    - destructAll.
      destruct H.
      apply H.
      exists x1.
      apply comp_ctx_split in H0.
      destruct H0.
      + destructAll.
        destruct x3; inv H0.
        eexists; eauto.
      + destructAll.
        destruct x4; inv H3.
        destruct x4; inv H6.
    - apply H in H0.
      destructAll.
      eexists; eexists; eexists; eexists.
      rewrite comp_ctx_f_assoc.
      simpl.
      reflexivity.
    - destructAll.
      destruct H.
      apply H1.
      exists x0.
      apply comp_ctx_split in H0.
      destruct H0.
      + destructAll.
        destruct x4; inv H0.
        exists x4, x2, x3; auto.
      + destructAll.
        destruct x5; inv H3.
        destruct x5; inv H6.
  Qed.


  Fixpoint fundefs_ctx_append B1 B2:=
    match B1 with
      | Fcons f t xs xe B => Fcons2_c f t xs xe (fundefs_ctx_append B B2)
      | Fnil => B2
    end.


  Lemma bound_stem_fundefs_append:
    forall fc f,
      Same_set _ (bound_stem_fundefs_ctx (fundefs_ctx_append f fc))
               (bound_stem_fundefs_ctx fc).
  Proof.
    induction f. simpl.
    rewrite bound_stem_Fcons2_c. auto.
    simpl. reflexivity.
  Qed.

  Theorem fundex_ctx_comp_f_ctx:
    forall fds1 f1 c v f l fds2,
      fundefs_ctx_append fds1 (Fcons1_c v f l Hole_c fds2) =
      comp_f_ctx_f f1 c ->
      c = Hole_c.
  Proof.
    induction fds1; intros.
    -  simpl in H.
       destruct f1; inv H.
       apply IHfds1 in H5. auto.
    - simpl in H.
      destruct f1; inv H.
      destruct e; inv H4. simpl; auto.
  Qed.

  Theorem cmap_view_efun2:
    forall sub c fds1 fds2 v f l e,
      cmap_view_ctx sub c ->
      cmap_view_ctx sub
                    (comp_ctx_f c
                                (Efun2_c (fundefs_ctx_append fds1
                                                             (Fcons1_c v f l Hole_c fds2)) e)).
  Proof.
    intros. split; intros; split; intros.
    - apply H in H0.
      destructAll.
      exists x0.
      exists (comp_ctx_f x1 (Efun2_c (fundefs_ctx_append fds1 (Fcons1_c v f l Hole_c fds2)) e)).
      rewrite comp_ctx_f_assoc.
      simpl. auto.
    - apply H.
      destructAll.
      apply comp_ctx_split in H0.
      destruct H0.
      + destructAll.
        destruct x2; inv H0.
        eauto.
      + destructAll.
        destruct x3; inv H2.
        apply fundex_ctx_comp_f_ctx in H1.
        inv H1.
    - apply H in H0.
      destructAll.
      exists x.
      exists (comp_ctx_f x0 (Efun2_c (fundefs_ctx_append fds1 (Fcons1_c v f l Hole_c fds2)) e)).
      exists x1, x2.
      rewrite comp_ctx_f_assoc.
      auto.
    - apply H.
      destructAll.
      apply comp_ctx_split in H0.
      destruct H0.
      + destructAll.
        destruct x3; inv H0.
        eauto.
      + destructAll.
        destruct x4; inv H2.
        apply fundex_ctx_comp_f_ctx in H1.
        inv H1.
  Qed.


  Theorem cmap_view_constr:
  forall {sub c} x t xs,
    cmap_view_ctx sub c ->
    M.get x sub = None ->
    cmap_view_ctx (M.set x (SVconstr t xs) sub) (comp_ctx_f c (Econstr_c x t xs Hole_c)).
  Proof.
    intros; split; intros; split; intros.
    - destruct (var_dec x0 x).
      + exists c, Hole_c.
        subst.
        rewrite M.gss in H1. inv H1. auto.
      + rewrite M.gso in H1 by auto.
        apply H in H1.
        destructAll.
        exists x1, (comp_ctx_f x2 (Econstr_c x t xs Hole_c)).
        rewrite comp_ctx_f_assoc.
        simpl. auto.
    - destructAll.
      apply comp_ctx_split in H1.
      destruct H1.
      + destructAll.
        destruct x3; inv H1.
        * rewrite M.gss. auto.
        * rewrite M.gso.
          2:{ intro. subst.
            destruct H. specialize (H x c l).
            assert ((exists c' c'' : exp_ctx,
                     comp_ctx_f x1 (Econstr_c x c l x3) =
                     comp_ctx_f c' (Econstr_c x c l c''))) by eauto.
            apply H in H2. rewrite H0 in H2. inv H2. }
          apply H. eauto.
      + destructAll.
        destruct x4; inv H3.
        * rewrite M.gss; auto.
        * destruct x4; inv H6.
    - rewrite M.gso in H1.
      apply H in H1. destructAll.
      exists x0.
      exists (comp_ctx_f x1 (Econstr_c x t xs Hole_c)).
      rewrite comp_ctx_f_assoc. simpl. eauto.
      intro.
      subst.
      rewrite M.gss in H1. inv H1.
    - destructAll.
      rewrite M.gso.
      apply H.
      apply comp_ctx_split in H1.
      destruct H1.
      + destructAll; subst.
        destruct x4; inv H1.
        eauto.
      + destructAll. destruct x5; inv H3.
        destruct x5; inv H6.
      + intro; subst.
        apply comp_ctx_split in H1.
        destruct H1.
        * destructAll; subst.
          destruct x4; inv H1.
          destruct H.
          specialize (H1 x t0 ys e).
          assert
            (exists (c' c'' : exp_ctx) (B1 B2 : fundefs),
               comp_ctx_f x0 (Efun1_c (fundefs_append x2 (Fcons x t0 ys e x3)) x4) =
               comp_ctx_f c' (Efun1_c (fundefs_append B1 (Fcons x t0 ys e B2)) c'')) by eauto.
          apply H1 in H2. rewrite H0 in H2. inv H2.
        * destructAll.
          destruct x5; inv H3.
          destruct x5; inv H6.
  Qed.

  Theorem cmap_view_prim:
    forall sub c v p l,
      cmap_view_ctx sub c ->
      cmap_view_ctx sub (comp_ctx_f c (Eprim_c v p l Hole_c)).
  Proof.
    intros; split; intros; split; intros.
    - apply H in H0.
      destructAll.
      eexists; eexists.
      rewrite  comp_ctx_f_assoc.
      simpl. reflexivity.
    - apply H. destructAll.
      apply comp_ctx_split in H0.
      destruct H0; destructAll.
      + destruct x2; inv H0.
        eauto.
      + destruct x3; inv H2.
        destruct x3; inv H5.
    - apply H in H0.
      destructAll.
      eexists; eexists; eexists; eexists.
      rewrite  comp_ctx_f_assoc.
      simpl. reflexivity.
    - apply H.
      destructAll.
      apply comp_ctx_split in H0.
      destruct H0; destructAll.
      + destruct x3; inv H0.
        eauto.
      + destruct x4; inv H2.
        destruct x4; inv H5.
  Qed.

  Theorem cmap_view_prim_val:
    forall sub c v p,
      cmap_view_ctx sub c ->
      cmap_view_ctx sub (comp_ctx_f c (Eprim_val_c v p Hole_c)).
  Proof.
    intros; split; intros; split; intros.
    - apply H in H0.
      destructAll.
      eexists; eexists.
      rewrite  comp_ctx_f_assoc.
      simpl. reflexivity.
    - apply H. destructAll.
      apply comp_ctx_split in H0.
      destruct H0; destructAll.
      + destruct x2; inv H0.
        eauto.
      + destruct x3; inv H2.
        destruct x3; inv H4.
    - apply H in H0.
      destructAll.
      eexists; eexists; eexists; eexists.
      rewrite  comp_ctx_f_assoc.
      simpl. reflexivity.
    - apply H.
      destructAll.
      apply comp_ctx_split in H0.
      destruct H0; destructAll.
      + destruct x3; inv H0.
        eauto.
      + destruct x4; inv H2.
        destruct x4; inv H4.
  Qed.


  Theorem cmap_view_proj:
    forall sub c v t n v',
      cmap_view_ctx sub c ->
      cmap_view_ctx sub (comp_ctx_f c (Eproj_c v t n v' Hole_c)).
  Proof.
    intros; split; intros; split; intros.
    - apply H in H0.
      destructAll.
      eexists; eexists.
      rewrite  comp_ctx_f_assoc.
      simpl. reflexivity.
    - apply H. destructAll.
      apply comp_ctx_split in H0.
      destruct H0; destructAll.
      + destruct x2; inv H0.
        eauto.
      + destruct x3; inv H2.
        destruct x3; inv H6.
    - apply H in H0.
      destructAll.
      eexists; eexists; eexists; eexists.
      rewrite  comp_ctx_f_assoc.
      simpl. reflexivity.
    - apply H.
      destructAll.
      apply comp_ctx_split in H0.
      destruct H0; destructAll.
      + destruct x3; inv H0.
        eauto.
      + destruct x4; inv H2.
        destruct x4; inv H6.
  Qed.


  Theorem cmap_view_efun1_cons:
    forall c0 c f0 v f l e,
      cmap_view_ctx c0 (comp_ctx_f c (Efun1_c f0 Hole_c)) ->
      M.get v c0 = None ->
      cmap_view_ctx (M.set v (SVfun f l e) c0)
                    (comp_ctx_f c (Efun1_c (Fcons v f l e f0) Hole_c)).
  Proof.
    intros; split; intros; split; intros.
    - rewrite M.gso in H1. apply H in H1.
      destructAll.
      apply comp_ctx_split in H1. destruct H1.
      + destructAll. destruct x2; inv H1.
        exists x0, (comp_ctx_f x2 (Efun1_c (Fcons v f l e f0) Hole_c)).
        rewrite comp_ctx_f_assoc. auto.
      + destructAll.
        destruct x3; inv H3.
        destruct x3; inv H4.
      + intro. subst.
        rewrite M.gss in H1.
        inv H1.
    - destructAll.
      rewrite M.gso.
      apply H.
      apply comp_ctx_split in H1.
      destruct H1.
      + destructAll.
        destruct x2; inv H1.
        exists x0, (comp_ctx_f x2 (Efun1_c f0 Hole_c)).
        rewrite comp_ctx_f_assoc. auto.
      + destructAll.
        destruct x3; inv H3.
        destruct x3; inv H4.
      + intro; subst.
        apply comp_ctx_split in H1.
        destruct H1.
        * destructAll.
          destruct x; inv H1.
          assert (exists e e', (comp_ctx_f (comp_ctx_f x0 (Econstr_c v0 c l0 x)) (Efun1_c f0 Hole_c)) = (comp_ctx_f e (Econstr_c v0 c l0 e'))).
          exists x0, (comp_ctx_f x (Efun1_c f0 Hole_c)).
          rewrite comp_ctx_f_assoc.
          auto.
          apply H in H1.
          rewrite H0 in H1. inv H1.
        * destructAll. destruct x2; inv H3.
          destruct x2; inv H4.
    - destruct (var_dec f1 v).
      + subst. rewrite M.gss in H1.
        inv H1.
        exists  c, Hole_c, Fnil, f0.
        simpl. auto.
      + rewrite M.gso in H1 by auto.
        apply H in H1. destructAll.
        apply comp_ctx_split in H1.
        destruct H1.
        * destructAll.
          destruct x3; inv H1.
          exists  (comp_ctx_f x Hole_c), Hole_c, (Fcons v f l e x1), x2.
          auto.
          exists x, (comp_ctx_f x3 (Efun1_c (Fcons v f l e f0) Hole_c)), x1, x2.
          rewrite comp_ctx_f_assoc. auto.
        * destructAll.
          destruct x4; inv H3.
          exists x3, Hole_c, (Fcons v f l e x1), x2. auto.
          destruct x4; inv H4.
    - destructAll.
      apply comp_ctx_split in H1.
      destruct H1.
      + destructAll.
        destruct x3; inv H1.
        * destruct x1; inv H3.
          rewrite M.gso.
          apply H. exists (comp_ctx_f x Hole_c), Hole_c, x1, x2.
          auto.
          intro; subst.
          assert (exists g1 g2 B1 B2, (comp_ctx_f (comp_ctx_f x Hole_c)
                                                  (Efun1_c (fundefs_append x1 (Fcons v t ys e0 x2)) Hole_c)) =
                                      comp_ctx_f g1 (Efun1_c (fundefs_append B1 (Fcons v t ys e0 B2)) g2)).
          eauto.
          apply H in H1. rewrite H0 in H1. inv H1.
          rewrite M.gss. auto.
        * assert (M.get f1 c0 = Some (SVfun t ys e0)).
          apply H.
          exists x, (comp_ctx_f x3 (Efun1_c f0 Hole_c)), x1, x2.
          rewrite comp_ctx_f_assoc.
          auto.
          destruct (var_dec f1 v).
          subst.
          rewrite H1 in H0.
          inv H0.
          rewrite M.gso; auto.
      + destructAll.
        destruct x4; inv H3.
        * destruct x1; inv H2.
          assert (M.get f1 c0 = Some (SVfun t ys e0)).
          apply H.
          exists x3, Hole_c, x1, x2.
          auto.
          destruct (var_dec f1 v0).
          subst. rewrite H1 in H0. inv H0.
          rewrite M.gso; auto.
          rewrite M.gss. auto.
        * destruct x4; inv H4.
  Qed.

  Theorem cmap_view_efun1_nil:
    forall sub c,
      cmap_view_ctx sub c ->
      cmap_view_ctx sub (comp_ctx_f c (Efun1_c Fnil Hole_c)).
  Proof.
    intros. split; intros; split; intros.
    - apply H in H0.
      destructAll.
      eexists x0, (comp_ctx_f x1 (Efun1_c Fnil Hole_c)).
      rewrite comp_ctx_f_assoc. auto.
    - apply H. destructAll.
      apply comp_ctx_split in H0.
      destruct H0.
      + destructAll. destruct x2; inv H0.
        eauto.
      + destructAll. destruct x3; inv H2. destruct x3; inv H3.
    - apply H in H0.
      destructAll.
      exists x, (comp_ctx_f x0 (Efun1_c Fnil Hole_c)), x1, x2.
      rewrite comp_ctx_f_assoc; auto.
    - apply H. destructAll.
      apply comp_ctx_split in H0.
      destruct H0.
      + destructAll.
        destruct x3; inv H0.
        * destruct x1; inv H2.
        * eauto.
      + destructAll.
        destruct x4; inv H2.
        destruct x1; inv H1.
        destruct x4; inv H3.
  Qed.


  Theorem bound_var_ctx_rename_all_ns:
    forall sigma,
      (forall (c : exp_ctx),
         bound_var_ctx c <--> bound_var_ctx (rename_all_ctx_ns sigma c)) /\
      (forall (fdc : fundefs_ctx),
         bound_var_fundefs_ctx fdc <--> bound_var_fundefs_ctx (rename_all_fun_ctx_ns sigma fdc)).
  Proof.
    intro sig.
    assert (Hcc := bound_var_rename_all_ns_mut).
    specialize (Hcc sig).
    destruct Hcc.
    exp_fundefs_ctx_induction IHc IHfdc; intros; simpl; repeat (first [normalize_bound_var_ctx|normalize_bound_var]); split; try (rewrite IHc); try (rewrite IHfdc); try (rewrite <- H); try (rewrite <- H0); auto with Ensembles_DB.
    rewrite H.
    simpl.
    rewrite H with (e := (Ecase v l0)).
    simpl.
    eauto with Ensembles_DB.
    rewrite H with (e:= (Ecase v l)).
    simpl.
    rewrite H with (e := (Ecase v l0)).
    simpl.
    eauto with Ensembles_DB.
  Qed.


  Theorem name_in_fundefs_ctx_rename_all_ns:
    forall sig f,
      names_in_fundefs_ctx f <--> names_in_fundefs_ctx (rename_all_fun_ctx_ns sig f).
  Proof.
    induction f; simpl; eauto with Ensembles_DB.
    rewrite name_in_fundefs_rename_all_ns. reflexivity.
  Qed.


  Theorem bound_stem_ctx_rename_all_ns:
    forall sigma,
      (forall (c : exp_ctx),
         bound_stem_ctx c <--> bound_stem_ctx (rename_all_ctx_ns sigma c)) /\
      (forall (fdc : fundefs_ctx),
         bound_stem_fundefs_ctx fdc <--> bound_stem_fundefs_ctx (rename_all_fun_ctx_ns sigma fdc)).
  Proof.
    intro sig.
    exp_fundefs_ctx_induction IHc IHfdc; intros; simpl; repeat (first [normalize_bound_stem_ctx|normalize_bound_stem_ctx_in_ctx]); split; try (rewrite IHc); try (rewrite IHfdc); try (rewrite <- H); try (rewrite <- H0); try (rewrite <- name_in_fundefs_rename_all_ns); try (rewrite <- name_in_fundefs_ctx_rename_all_ns); auto with Ensembles_DB.
  Qed.

  Theorem cmap_view_bound_in_ctx:
    forall sub c v s,
      cmap_view_ctx sub c ->
      M.get v sub = Some s ->
      bound_var_ctx c v.
  Proof.
    intros. destruct s; apply H in H0; destructAll.
    - apply bound_var_ctx_comp_ctx.
      right; auto.
    - apply bound_var_ctx_comp_ctx.
      right.
      constructor.
      eapply fundefs_append_bound_vars.
      reflexivity.
      right; auto.
  Qed.

  (* Variables are bound by (1) binding on the stem (2) mutually rec. functions *)
  Theorem occurs_free_app_bound_stem x e:
    occurs_free e x ->
    ( forall c,
        ~ occurs_free (c |[e]|) x ->
        bound_stem_ctx c x) /\
    ( forall fds,
        ~ occurs_free_fundefs (fds <[e]>) x ->
        bound_stem_fundefs_ctx fds x \/ names_in_fundefs_ctx fds x).
  Proof.
    intro H.
    apply exp_fundefs_ctx_mutual_ind; intros.
    + exfalso. apply H0. apply H.
    + simpl in H1.
      destruct (var_dec v x).
      subst. constructor.
      constructor 2. apply H0. intro. apply H1.
      apply occurs_free_Econstr.
      right.
      split; auto.
    + simpl in H1.
      destruct (var_dec v x).
      subst. constructor.
      constructor. apply H0. intro. apply H1.
      apply occurs_free_Eproj.
      right.
      split; auto.
    + simpl in H1.
      destruct (var_dec v x).
      subst. constructor.
      constructor. apply H0. intro. apply H1.
      apply occurs_free_Eletapp.
      right.
      split; auto.
    + simpl in H1.
      destruct (var_dec v x).
      subst. constructor.
      constructor. apply H0. intro. apply H1.
      apply occurs_free_Eprim_val.
      split; auto.
    + simpl in H1.
      destruct (var_dec v x).
      subst. constructor.
      constructor. apply H0. intro. apply H1.
      apply occurs_free_Eprim.
      right.
      split; auto.
    + constructor. apply H0.
      intro.
      apply H1.
      simpl.
      eapply occurs_free_Ecase_Included.
      2: apply H2.
      apply in_app. right. constructor; auto.
    + simpl in H1.
      assert (Hv := Decidable_name_in_fundefs f4).
      destruct Hv. specialize (Dec x). destruct Dec.
      constructor.
      auto.
      apply SBound_Fun12_c. apply H0. intro.
      apply H1.
      apply Free_Efun1; auto.
    + simpl in H1.
      assert (Hv := Decidable_name_in_fundefs_ctx f5).
      inv Hv. specialize (Dec x). inv Dec.
      constructor; auto.
      apply SBound_Fun2_c.
      assert (~ occurs_free_fundefs (f5 <[ e ]>) x).
      intro.
      apply H1.
      apply Free_Efun2.
      auto. apply H0 in H3. inv H3. auto.
      exfalso. auto.
    + simpl in H1.
      assert (Hv := Decidable_name_in_fundefs (Fcons v t l (e0 |[ e ]|) f6)).
      destruct Hv. specialize (Dec x). destruct Dec.
      right.
      eapply name_in_fundefs_ctx_ctx with (e := e). eauto.
      left.
      assert (Hl := Decidable_FromList l).
      inv Hl. specialize (Dec x). inv Dec.
      constructor. auto.
      apply SBound_Fcons12_c. apply H0. intro. apply H1.
      constructor; auto. intro. subst. apply n. now constructor.
      intro; apply n. constructor 2. auto.
    + simpl in H1.
      assert (Hv := Decidable_name_in_fundefs (Fcons v t l e0 (f7 <[ e ]>))).
      destruct Hv. specialize (Dec x). destruct Dec.
      right.
      eapply name_in_fundefs_ctx_ctx. eauto.
      left.
      constructor.
      assert ( ~ occurs_free_fundefs (f7 <[ e ]>) x).
      intro; apply H1.
      constructor 2. auto.
      intro. subst. apply n. subst; constructor; auto.
      apply H0 in H2. inv H2; auto.
      exfalso. apply n.
      simpl. right.
      eapply name_in_fundefs_ctx_ctx. eauto.
  Qed.

  (* TODO: move to identifier *)
  Theorem ub_comp_ctx_f :
    forall c' : exp_ctx,
      (forall c : exp_ctx,
         unique_bindings_c (comp_ctx_f c c') <->
         unique_bindings_c c /\
         unique_bindings_c c' /\ Disjoint var (bound_var_ctx c) (bound_var_ctx c')) /\
      (forall fds : fundefs_ctx,
         unique_bindings_fundefs_c (comp_f_ctx_f fds c') <->
         unique_bindings_fundefs_c fds /\
         unique_bindings_c c' /\ Disjoint var (bound_var_fundefs_ctx fds) (bound_var_ctx c')).
  Proof.
    intros c'.
    exp_fundefs_ctx_induction IHc IHfdc; intros; simpl; repeat normalize_bound_var_ctx.
    (* Hole *)
    - split; intros.
      split. constructor. split; auto. eauto with Ensembles_DB.
      destructAll; auto.
    (* Constr *)
    - split; intros.
      + inv H. apply IHc in H5. destructAll.
        split; auto. constructor. intro. apply H2.
        apply bound_var_ctx_comp_ctx.  auto.
        auto.
        split; auto.
        apply Union_Disjoint_l. auto.
        split. intro. intro. inv H3. inv H4.
        apply H2.
        apply bound_var_ctx_comp_ctx.  auto.
      + destructAll.
        constructor.  intro. apply bound_var_ctx_comp_ctx in H2. inv H2.
        inv H. apply H5. auto.
        inv H1. specialize (H2 v).
        apply H2. split; auto.
        apply IHc. inv H. split; auto. split; auto.
        eapply Disjoint_Included_l. 2: apply H1. auto with Ensembles_DB.
    (* Proj *)
    - split; intros.
      + inv H. apply IHc in H6. destructAll.
        split; auto. constructor. intro. apply H2.
        apply bound_var_ctx_comp_ctx.  auto.
        auto.
        split; auto.
        apply Union_Disjoint_l. auto.
        split. intro. intro. inv H3. inv H4.
        apply H2.
        apply bound_var_ctx_comp_ctx.  auto.
      + destructAll.
        constructor.  intro. apply bound_var_ctx_comp_ctx in H2. inv H2.
        inv H. apply H5. auto.
        inv H1. specialize (H2 v).
        apply H2. split; auto.
        apply IHc. inv H. split; auto. split; auto.
        eapply Disjoint_Included_l. 2: apply H1. auto with Ensembles_DB.
    (* Letapp *)
    - split; intros.
      + inv H. apply IHc in H6. destructAll.
        split; auto. constructor. intro. apply H2.
        apply bound_var_ctx_comp_ctx.  auto.
        auto.
        split; auto.
        apply Union_Disjoint_l. auto.
        split. intro. intro. inv H3. inv H4.
        apply H2.
        apply bound_var_ctx_comp_ctx.  auto.
      + destructAll.
        constructor.  intro. apply bound_var_ctx_comp_ctx in H2. inv H2.
        inv H. apply H5. auto.
        inv H1. specialize (H2 v).
        apply H2. split; auto.
        apply IHc. inv H. split; auto. split; auto.
        eapply Disjoint_Included_l. 2: apply H1. auto with Ensembles_DB.
    - split; intros.
      + inv H. apply IHc in H4. destructAll.
        split; auto. constructor. intro. apply H2.
        apply bound_var_ctx_comp_ctx.  auto.
        auto.
        split; auto.
        apply Union_Disjoint_l. auto.
        split. intro. intro. inv H3. inv H4.
        apply H2.
        apply bound_var_ctx_comp_ctx.  auto.
      + destructAll.
        constructor.  intro. apply bound_var_ctx_comp_ctx in H2. inv H2.
        inv H. apply H5. auto.
        inv H1. specialize (H2 v).
        apply H2. split; auto.
        apply IHc. inv H. split; auto. split; auto.
        eapply Disjoint_Included_l. 2: apply H1. auto with Ensembles_DB.
    - split; intros.
      + inv H. apply IHc in H5. destructAll.
        split; auto. constructor. intro. apply H2.
        apply bound_var_ctx_comp_ctx.  auto.
        auto.
        split; auto.
        apply Union_Disjoint_l. auto.
        split. intro. intro. inv H3. inv H4.
        apply H2.
        apply bound_var_ctx_comp_ctx.  auto.
      + destructAll.
        constructor.  intro. apply bound_var_ctx_comp_ctx in H2. inv H2.
        inv H. apply H5. auto.
        inv H1. specialize (H2 v).
        apply H2. split; auto.
        apply IHc. inv H. split; auto. split; auto.
        eapply Disjoint_Included_l. 2: apply H1. auto with Ensembles_DB.
    (* case *)
    -  split; intros.
       + inv H. apply IHc in H6. destructAll.
         split. constructor; auto. eapply Disjoint_Included_l.
         2: apply H7. intro; intro. apply bound_var_ctx_comp_ctx. auto.
         split; auto.
         apply Union_Disjoint_l.
         split; intro; intro. inv H2. inv H7. specialize (H2 x).
         apply H2. split. apply bound_var_ctx_comp_ctx; auto.
         apply bound_var_Ecase_app. auto.
         apply Union_Disjoint_l.
         auto.
         split; intro; intro. inv H2. inv H7. specialize (H2 x).
         apply H2. split. apply bound_var_ctx_comp_ctx; auto.
         apply bound_var_Ecase_app. auto.
       + destructAll.
         inv H.
         constructor; auto.
         apply IHc. split; auto. split; auto.
         eapply Disjoint_Included_l. 2: apply H1.
         eauto with Ensembles_DB.
         split.
         intros. intro. inv H. apply bound_var_ctx_comp_ctx in H2.
         inv H2. inv H9. specialize (H2 x). apply H2.
         split; auto.
         inv H1. specialize (H2 x). apply H2. split; auto.
         apply bound_var_Ecase_app in H3. inv H3; auto.
    (* Efun1_c *)
    - split; intros.
      + inv H. apply IHc in H2. destructAll.
        split. constructor; auto.
        eapply Disjoint_Included_l. 2: apply H4.
        intro; intros; apply bound_var_ctx_comp_ctx; auto.
        split; auto.
        apply Disjoint_sym.  apply Union_Disjoint_r.
        eapply Disjoint_Included_l. 2: apply H4.
        intro; intros; apply bound_var_ctx_comp_ctx; auto.
        apply Disjoint_sym; auto.
      + destructAll. inv H. constructor. apply IHc.
        split; auto. split; auto.
        eapply Disjoint_Included_l. 2: apply H1.
        auto with Ensembles_DB.
        auto.
        split. intro. intro. inv H.
        apply bound_var_ctx_comp_ctx in H2. inv H2.
        inv H6. specialize (H2 x). apply H2; auto.
        inv H1. specialize (H2 x). apply H2; auto.
    (* Efun2_c *)
    - split; intros.
      + inv H. apply IHfdc in H3. destructAll. split.
        constructor; auto. eapply Disjoint_Included_r.
        2: apply H4.
        intro. intros. apply bound_var_ctx_comp_ctx. auto.
        split; auto.
        apply Union_Disjoint_l. auto.
        eapply Disjoint_Included_r.
        2: apply H4.
        intro. intros. apply bound_var_ctx_comp_ctx. auto.
      + destructAll. inv H.
        constructor; auto.
        apply IHfdc. split; auto. split; auto.
        eapply Disjoint_Included_l. 2: apply H1.
        auto with Ensembles_DB.
        split. intro; intro.
        inv H. apply bound_var_ctx_comp_ctx in H3. inv H3.
        inv H6. specialize (H3 x). apply H3. auto.
        inv H1. specialize (H3 x). apply H3. split; auto.
    (* Fcons1 *)
    - split; intros.
      + inv H.
        apply IHc in H12.
        destructAll. split.
        constructor; auto.
        intro; apply H5.
        apply bound_var_ctx_comp_ctx; auto.
        eapply Disjoint_Included_l. 2: apply H7.
        intro; intros. apply bound_var_ctx_comp_ctx. auto.
        eapply Disjoint_Included_l. 2: apply H9.
        intro; intros. apply bound_var_ctx_comp_ctx; auto.
        split; auto. repeat eapply Union_Disjoint_l; eauto.
        split. intro. intro. apply H5. inv H2.
        inv H3.
        apply bound_var_ctx_comp_ctx; auto.
        apply Disjoint_sym.
        eapply Disjoint_Included_l. 2: apply H7.
        intro; intros. apply bound_var_ctx_comp_ctx; auto.
        apply Disjoint_sym.
        eapply Disjoint_Included_l. 2: apply H9.
        intro; intros. apply bound_var_ctx_comp_ctx; auto.
      + destructAll.
        inv H. constructor; eauto.
        intro.
        apply bound_var_ctx_comp_ctx in H.
        inv H. apply H7; auto.
        inv H1. specialize (H v). apply H. split; auto.
        split. intro. intro. inv H. apply bound_var_ctx_comp_ctx in H2.
        inv H2.
        inv H9. specialize (H2 x). apply H2. split; auto.
        inv H1. specialize (H2 x). apply H2.
        split. right; auto. auto.
        split; intro; intro. inv H.
        apply bound_var_ctx_comp_ctx in H2. inv H2. inv H11. specialize (H2 x); auto.
        inv H1. specialize (H2 x); apply H2. split; auto.
        apply IHc.
        split; auto. split; auto. eapply Disjoint_Included_l.
        2: apply H1.
        eauto with Ensembles_DB.
    (* Fcons2 *)
    - split; intro.
      + inv H. apply IHfdc in H13. destructAll.
        split. constructor; auto.
        intro; apply H6. apply bound_var_ctx_comp_ctx.
        auto.
        eapply Disjoint_Included_l. 2: apply H8.
        intro; intro. apply bound_var_ctx_comp_ctx; auto.
        eapply Disjoint_Included_r. 2: apply H9.
        intro; intro. apply bound_var_ctx_comp_ctx; auto.
        split; auto. split. intro. intro. inv H2. inv H3.
        apply H6. inv H2. apply bound_var_ctx_comp_ctx; auto.
        inv H2.
        inv H8. specialize (H2 x). apply H2. split; auto.
        apply bound_var_ctx_comp_ctx; auto.
        inv H3.
        inv H9. specialize (H3 x). apply H3. split; auto.
        apply bound_var_ctx_comp_ctx; auto.
        inv H1. specialize (H3 x). apply H3; split; auto.
      + destructAll. inv H.
        constructor; auto. intro.
        apply bound_var_ctx_comp_ctx in H.
        inv H. auto.
        inv H1. specialize (H v). apply H. split; auto.
        split. intro; intro. inv H.
        apply bound_var_ctx_comp_ctx in H2. inv H2.
        inv H10. specialize (H2 x). apply H2; auto.
        inv H1. specialize (H2 x). apply H2; auto.
        split; intro; intro. inv H.
        apply bound_var_ctx_comp_ctx in H3. inv H3.
        inv H11. specialize (H3 x). apply H3; auto.
        inv H1. specialize (H3 x). apply H3. split. auto. auto.
        apply IHfdc.
        split; auto. split; auto. eapply Disjoint_Included_l.
        2: apply H1. auto with Ensembles_DB.
  Qed.

  Theorem inlined_fundefs_f_staged:
    forall x im f4,
      (inlined_fundefs_f f4 (M.set x true im)) =
      (inlined_fundefs_f (inlined_fundefs_f f4 im) (M.set x true (M.empty bool))).
  Proof.
    induction f4; simpl; try rewrite IHf4; auto.
    destruct (var_dec v x).
    - subst.
      unfold get_b.
      rewrite M.gss.
      destruct (M.get x im). destruct b.
      auto.
      simpl. unfold get_b.
      rewrite M.gss. auto.
      simpl. unfold get_b. rewrite M.gss.
      auto.
    - unfold get_b. rewrite M.gso.
      destruct (M.get v im).  destruct b. auto.
      simpl. unfold get_b. rewrite M.gso. rewrite M.gempty.
      auto. auto.
      simpl. unfold get_b. rewrite M.gso; auto. auto.
  Qed.

  Theorem inlined_ctx_f_staged_mut:
    forall x  im,
      (forall c,
         inlined_ctx_f c (M.set x true im) =
         inlined_ctx_f (inlined_ctx_f c im) (M.set x true (M.empty bool))) /\
      ( forall fc,
          inlined_fundefs_ctx_f fc (M.set x true im) =
          inlined_fundefs_ctx_f (inlined_fundefs_ctx_f fc im) (M.set x true (M.empty bool))).
  Proof.
    intros x im.
    apply exp_fundefs_ctx_mutual_ind; simpl; intros; try rewrite H; auto .
    rewrite <- inlined_fundefs_f_staged. auto.
  Qed.

  Theorem inlined_ctx_f_staged:
    forall x  im,
      (forall c,
         inlined_ctx_f c (M.set x true im) =
         inlined_ctx_f (inlined_ctx_f c im) (M.set x true (M.empty bool))).
  Proof.
    intros.
    apply inlined_ctx_f_staged_mut.
  Qed.

  Lemma gsr_clos_trans n m e1 e2 e3 :
    gsr_clos n e1 e2 ->
    gsr_clos m e2 e3 ->
    gsr_clos (n + m) e1 e3.
  Proof.
    intros H1 H2. induction H1.
    + rewrite <- Nat.add_assoc. econstructor; eauto.
    + eassumption.
  Qed.

  (** precontractfun returns a subset of the current fundefs related to the original term by Fun_rem_s *)
  Theorem precontractfun_corresp:
    forall fds_c fds e c im sub count sig,
      let ce := (app_ctx_f (rename_all_ctx_ns sig (inlined_ctx_f c im)) (rename_all_ns sig (Efun (fundefs_append fds fds_c) e))) in
      unique_bindings ce ->
      closed_exp ce ->
      c_count ce count ->
      cmap_view_ctx sub c ->
      inl_inv im sub ce ->
      sig_inv_full sig (rename_all_ctx_ns sig (inlined_ctx_f c im)) (rename_all_ns sig (Efun (fundefs_append fds fds_c) e)) ->
      forall fds_c' count' sub',
        precontractfun sig count sub fds_c = (fds_c', count', sub') ->
        let ce' := (app_ctx_f (rename_all_ctx_ns sig (inlined_ctx_f c im)) (rename_all_ns sig (Efun (fundefs_append fds fds_c') e))) in
        gsr_clos 0 ce ce' /\ c_count ce' count' /\ inl_inv im sub' ce' /\
        cmap_view_ctx sub' (comp_ctx_f c (Efun1_c fds_c' Hole_c)) /\
        sig_inv_full sig (rename_all_ctx_ns sig (inlined_ctx_f c im)) (rename_all_ns sig (Efun (fundefs_append fds fds_c') e)).
  Proof.
    induction fds_c; intros.
    - simpl in H5.
      destruct (get_c v count) eqn:gvc.
      +  assert (H1v := H1 v).
         rewrite gvc in H1v.
         assert (gsr_clos 0 ce
                          (rename_all_ctx_ns sig (inlined_ctx_f c im)
                          |[ rename_all_ns sig
                                           (Efun (fundefs_append fds fds_c) e0) ]|)).
         { replace 0 with (0 + 0) by lia. econstructor.
           constructor.
           simpl.
           rewrite rename_all_ns_fundefs_append.
           simpl.
           (* rewrite rename_all_ns_fundefs_append. *)
           (* simpl. *)
           apply Fun_rem_s.
           specialize (H1 v).
           rewrite gvc in H1.
           unfold ce in H1.
           apply num_occur_app_ctx in H1. destructAll; pi0.
           simpl in H6.
           rewrite rename_all_ns_fundefs_append in H6.
           simpl in H6. now auto.

           simpl. rewrite rename_all_ns_fundefs_append.
           now econstructor.
         }
         assert (Hub' := gsr_clos_preserves_clos _ _ _ H H0 H6).
         destruct Hub'.
         assert (H4' := H4).
         apply sig_inv_combine in H4.
         destruct H4 as (H4dom, H4co).
         assert (Hse := gsr_preserves_sig_dom _ _ _ _ H (closed_implies_Disjoint _ H0) H6 H4dom).
         eapply IHfds_c with (fds := fds) (e := e0) (c := c) (im := im) in H5; eauto.
         destructAll.
         unfold ce'.
         split.
         replace 0 with (0 + 0) by lia. eapply gsr_clos_trans.
         * apply H6.
         * auto.
         * split; auto.
         * intro.
           specialize (H1 v0).
           unfold ce in H1.
           apply num_occur_app_ctx in H1.
           destructAll.
           simpl in H4. inv H4.
           rewrite rename_all_ns_fundefs_append in H15.
           apply fundefs_append_num_occur' in H15.
           destructAll.
           simpl in H10.
           inv H10.
           eapply num_occur_n.
           apply num_occur_app_ctx.
           exists x, (n+(x0 + m)).
           split; auto.
           split.
           simpl.
           constructor; auto.
           rewrite rename_all_ns_fundefs_append.
           eapply fundefs_append_num_occur.
           reflexivity.
           auto. auto.
           reflexivity.
           symmetry.
           unfold dec_census.
           assert  (Hcc := combine_minus_census_correct).
           destruct Hcc.
           specialize (H10 e count sig). rewrite <- H10.
           rewrite gccombine_sub.
           rewrite H9.
           assert (c_count (rename_all_ns sig e) (init_census (rename_all_ns sig e))) by apply init_census_correct.
           assert (n0 =  get_c v0 (init_census (rename_all_ns sig e))).
           eapply (proj1 (num_occur_det v0)); eauto.
           lia.
         * { intro.
             intros.
             apply H3 in H4.
             destruct H4.
             split; [| split].
             - intro.
               apply H4.
               unfold ce.
               apply bound_var_app_ctx in H10.
               apply bound_var_app_ctx.
               inv H10; auto.
               right.
               apply bound_var_rename_all_ns.
               apply bound_var_rename_all_ns in H11.
               normalize_bound_var.
               rewrite bound_var_Efun in H11.
               inv H11; auto.
               left.
               rewrite fundefs_append_bound_vars.
               2: reflexivity.
               rewrite fundefs_append_bound_vars in H10.
               2: reflexivity.
               rewrite bound_var_fundefs_Fcons.
               inv H10; auto.
             - apply H9 in H10.
               unfold ce in H10.
               intro. intro.
               inv H10.
               specialize (H12 x).
               apply H12.
               inv H11. split; auto.
               rewrite bound_var_app_ctx in H10.
               rewrite bound_var_app_ctx.
               inv H10; auto.
               right.
               apply bound_var_rename_all_ns.
               apply bound_var_rename_all_ns in H11.
               normalize_bound_var.
               rewrite bound_var_Efun in H11.
               inv H11; auto.
               left.
               rewrite fundefs_append_bound_vars.
               2: reflexivity.
               rewrite fundefs_append_bound_vars in H10.
               2: reflexivity.
               rewrite bound_var_fundefs_Fcons.
               inv H10; auto. }
         * apply sig_inv_combine.
           split; auto.
           intro.
           intros.
           apply H4' in H4.
           inv H4. inv H10; auto.
           left.
           apply num_occur_app_ctx in H4.
           destructAll; pi0.
           simpl in H10.
           rewrite rename_all_ns_fundefs_append in H10.
           inv H10.
           apply fundefs_append_num_occur' in H16; destructAll.
           inv H11; pi0.
           simpl.
           apply num_occur_app_ctx.
           exists 0, 0.
           split; auto.
           split; auto.
           eapply num_occur_n.
           constructor; eauto.
           rewrite rename_all_ns_fundefs_append.
           eapply fundefs_append_num_occur.
           reflexivity.
           eauto. eauto.
           auto.
      +  assert (rename_all_ctx_ns sig (inlined_ctx_f c im)
                |[ rename_all_ns sig
                                 (Efun (fundefs_append fds (Fcons v f l e fds_c)) e0) ]| =
                                                                                         rename_all_ctx_ns sig (inlined_ctx_f c im)
                |[ rename_all_ns sig
                                 (Efun (fundefs_append (fundefs_append fds (Fcons v f l e Fnil)) fds_c) e0) ]|) by
            (rewrite <- fundefs_append_assoc; reflexivity).
         unfold ce in IHfds_c.
         fold ce in H6. rewrite H6 in *.
         destruct  (precontractfun sig count sub fds_c ) eqn:prefun.
         destruct p.
         assert (Hff : (fundefs_append fds (Fcons v f l e fds_c)) =
                       (fundefs_append (fundefs_append fds (Fcons v f l e Fnil))
                                       fds_c)).
         rewrite <- fundefs_append_assoc. simpl. auto.
         rewrite Hff in H4.
         specialize (IHfds_c  _ _ _ _ _ _ _ H H0 H1 H2 H3 H4 _ _ _ prefun).
         inv H5.
         assert (rename_all_ctx_ns sig (inlined_ctx_f c im)
                |[ rename_all_ns sig (Efun (fundefs_append fds (Fcons v f l e f0)) e0)
                 ]| =
                    rename_all_ctx_ns sig (inlined_ctx_f c im)
                |[ rename_all_ns sig (Efun (fundefs_append (fundefs_append fds (Fcons v f l e Fnil))  f0) e0)
                 ]|).
         rewrite <-fundefs_append_assoc; reflexivity.
         unfold ce'.
         rewrite H5.
         destructAll.
         split; auto.
         split; auto.
         split; auto.
         clear H10.
         intro. intro. apply H9 in H10.
         destruct H10.
         split; auto.

         intros.
         destruct (var_dec f1 v).
         * subst.
           exfalso.
           apply H10.
           apply bound_var_app_ctx.
           right.
           rewrite <- bound_var_rename_all_ns.
           rewrite bound_var_Efun.
           left.
           rewrite fundefs_append_bound_vars.
           2: reflexivity.
           left.
           rewrite fundefs_append_bound_vars.
           2: reflexivity.
           right.
           rewrite bound_var_fundefs_Fcons.
           left; auto.
         * rewrite M.gso in H13.
           apply H12 in H13.
           auto. auto.
         * split. apply cmap_view_efun1_cons. apply H10.

           (* due to unique binding *)

           apply (gsr_clos_preserves_clos _ _ _ H H0) in H7.
           destruct H7.
           destruct (M.get v c0) eqn:gvc0.
           2: auto.

           assert (bound_var_ctx (comp_ctx_f c (Efun1_c f0 Hole_c)) v).
           eapply cmap_view_bound_in_ctx; eauto.

           apply bound_var_ctx_comp_ctx in H13.
           apply ub_app_ctx_f in H7.
           destructAll.
           exfalso.
           inv H13.
           {
             inv H15.
             specialize (H13 v).
             apply H13.
             split.
             apply bound_var_ctx_rename_all_ns.
             {
               destruct s.
               - apply H10 in gvc0. destructAll.
                 apply comp_ctx_split in H15.
                 destruct H15.
                 + destructAll.
                   destruct x1; inv H15.
                   rewrite (proj1 inlined_comp_ctx).
                   simpl.
                   apply bound_var_ctx_comp_ctx.
                   right; auto.
                 + destructAll. destruct x2; inv H18. destruct x2; inv H19.
               - assert (gvc0' := gvc0).
                 apply H10 in gvc0. destructAll.
                 apply comp_ctx_split in H15.
                 destruct H15.
                 + destructAll.
                   destruct x3; inv H15.
                   * simpl in H14.
                     inv H14.
                     repeat rewrite rename_all_ns_fundefs_append in H19.
                     eapply fundefs_append_unique_bindings_l in H19.
                     2: reflexivity.
                     destructAll.
                     inv H17.
                     exfalso. specialize (H19 v).
                     apply H19.
                     split.
                     eapply fundefs_append_bound_vars.
                     reflexivity. right.
                     simpl. auto.
                     eapply fundefs_append_bound_vars.
                     reflexivity. right.
                     simpl. auto.
                   * rewrite (proj1 inlined_comp_ctx).
                     apply bound_var_ctx_comp_ctx. right. simpl.
                     rewrite inlined_fundefs_append.
                     simpl. destruct (get_b v im) eqn:gbvim.
                     apply H3 in gbvim. destructAll.
                     exfalso.
                     apply H15.
                     apply bound_var_app_ctx.
                     right.
                     apply bound_var_rename_all_ns.
                     constructor.
                     eapply fundefs_append_bound_vars.
                     reflexivity.
                     left.
                     eapply fundefs_append_bound_vars.
                     reflexivity.
                     right.
                     auto.
                     constructor.
                     eapply fundefs_append_bound_vars.
                     reflexivity.
                     right.
                     auto.
                 + destructAll.
                   destruct x4; inv H18.
                   * exfalso.
                     simpl in H14.
                     inv H14.
                     repeat rewrite rename_all_ns_fundefs_append in H19.
                     eapply fundefs_append_unique_bindings_l in H19.
                     2: reflexivity.
                     destructAll.
                     inv H17.
                     exfalso. specialize (H19 v).
                     apply H19.
                     split.
                     eapply fundefs_append_bound_vars.
                     reflexivity. right.
                     simpl. auto.
                     eapply fundefs_append_bound_vars.
                     reflexivity. right.
                     simpl. auto.
                   * destruct x4; inv H19.
             }
             apply bound_var_rename_all_ns.
             constructor.
             eapply fundefs_append_bound_vars.
             reflexivity.
             left.
             eapply fundefs_append_bound_vars.
             reflexivity.
             right.
             auto.
           }
           {
             simpl in H14. inv H14.
             rewrite rename_all_ns_fundefs_append in H19.
             rewrite rename_all_ns_fundefs_append in H19.
             eapply fundefs_append_unique_bindings_l in H19.
             2: reflexivity.
             destructAll.
             inv H17. specialize (H19 v).
             apply H19.
             split.
             eapply fundefs_append_bound_vars.
             reflexivity.
             right. simpl. auto.
             apply bound_var_rename_all_ns_fundefs.
             inv H16.
             auto.
             inv H23.
           }
           rewrite <- fundefs_append_assoc in H11.
           simpl in H11. simpl. auto.
    - simpl in H5. inv H5. split. eapply Refl_srw.
      split; auto.
      split; auto.
      split.
      apply cmap_view_efun1_nil. auto.
      auto.
  Qed.

  Theorem bound_var_fundefs_inlined:
    forall im1 im2,
      b_map_le im1 im2 ->
      forall fds,
        Included _ (bound_var_fundefs (inlined_fundefs_f fds im2)) (bound_var_fundefs (inlined_fundefs_f fds im1)).
  Proof.
    intros im1 im2 Him; induction fds; simpl; repeat normalize_bound_var; auto.
    - destruct (get_b v im1) eqn:gbvi.
      + apply Him in gbvi. rewrite gbvi. auto.
      + destruct (get_b v im2); repeat normalize_bound_var; eauto with Ensembles_DB.
    - intro. intro. inv H.
  Qed.

  Lemma bound_var_ctx_inlined_antimon_mut:
    forall im1 im2,
      b_map_le im1 im2 ->
      (forall c,
         Included _ (bound_var_ctx (inlined_ctx_f c im2)) (bound_var_ctx (inlined_ctx_f c im1))) /\
      (forall fdc,
         Included _ (bound_var_fundefs_ctx (inlined_fundefs_ctx_f fdc im2)) (bound_var_fundefs_ctx (inlined_fundefs_ctx_f fdc im1))).
  Proof.
    intros im1 im2 Him.
    exp_fundefs_ctx_induction IHc1 IHfc1; simpl; repeat normalize_bound_var_ctx; eauto with Ensembles_DB.
    - intro.
      repeat normalize_bound_var_ctx.
      eauto with Ensembles_DB.
    - apply Included_Union_compat; auto.
      apply bound_var_fundefs_inlined; auto.
  Qed.

  Theorem bound_var_ctx_inlined_antimon:
    forall im1 im2 c,
      b_map_le im1 im2 ->
      Included _ (bound_var_ctx (inlined_ctx_f c im2)) (bound_var_ctx (inlined_ctx_f c im1)).
  Proof.
    intros.
    apply bound_var_ctx_inlined_antimon_mut; auto.
  Qed.


  Theorem num_occur_rename_all_ns_dead_set:
    forall f x y sigma e,
      f <> y ->
      num_occur (rename_all_ns sigma e) f 0 ->
      num_occur (rename_all_ns (M.set x y sigma) e) f 0.
  Proof.
    intros.
    assert (exists n,  num_occur (rename_all_ns (M.set x y sigma) e) f n) by apply e_num_occur.
    destruct H1.
    assert (x0 <= 0).
    eapply (proj1 (num_occur_rename_all_ns_set f x y H)); eauto.
    apply Nat.le_0_r in H2.
    subst; auto.
  Qed.


  (* used for function and constructor case *)
  Theorem sub_none_from_pre:
    forall c im e v sub sig,
      unique_bindings (rename_all_ctx_ns sig (inlined_ctx_f c im) |[ e ]|) ->
      cmap_view_ctx sub c ->
      inl_inv im sub (rename_all_ctx_ns sig (inlined_ctx_f c im) |[ e ]|) ->
      bound_var e v ->
      M.get v sub = None.
  Proof.
    intros.
    destruct (M.get v sub) eqn:gvs; auto.
    exfalso.
    destruct s; apply H0 in gvs; destructAll.
    - apply ub_app_ctx_f in H.
      destructAll.
      inv H4.
      specialize (H5 v).
      apply H5.
      split.
      apply bound_var_ctx_rename_all_ns.
      rewrite (proj1 inlined_comp_ctx).
      apply bound_var_ctx_comp_ctx.
      right.
      simpl. auto.
      auto.
    - apply ub_app_ctx_f in H.
      destructAll.
      inv H4.
      specialize (H5 v).
      apply H5.
      split.
      apply bound_var_ctx_rename_all_ns.
      rewrite (proj1 inlined_comp_ctx).
      apply bound_var_ctx_comp_ctx.
      right.
      simpl.
      constructor.
      rewrite inlined_fundefs_append.
      simpl. destruct (get_b v im) eqn:gbvi.
      + apply H1 in gbvi.
        exfalso.
        destruct gbvi. apply H4.
        apply bound_var_app_ctx.
        right. auto.
      + eapply fundefs_append_bound_vars.
        reflexivity.
        right. simpl; auto.
      + auto.
  Qed.

  Ltac ctx_inl_push :=
    rewrite (proj1 inlined_comp_ctx);
    simpl;
    rewrite (proj1 (rename_all_ctx_ns_comp_ctx _ _));
    symmetry;
    rewrite <- app_ctx_f_fuse;
    simpl; auto.


  Theorem get_set_list2:
    forall (x : M.elt) (sig : M.t Maps.PTree.elt) (l : list M.elt)
           (l' : list Maps.PTree.elt),
      ~ FromList l x -> M.get x (set_list (combine l l') sig) = M.get x sig.
  Proof.
    induction l; intros.
    simpl. auto.
    destruct l'.
    simpl; auto.
    simpl. rewrite M.gso.
    apply IHl. intro; apply H. simpl; auto.
    intro; apply H. subst. simpl; auto.
  Qed.

  Theorem apply_r_set_list2:
    forall x sig l l',
      ~ FromList l x ->
      apply_r (set_list (combine l l') sig) x =
      apply_r sig x.
  Proof.
    intros. unfold apply_r.
    rewrite get_set_list2; auto.
  Qed.

  (* can stage set_list *)
  Theorem set_list_rename_all_ar l0 l sig v :
    (forall x, FromList l0 x -> (x <> (apply_r sig v) \/
                                 ~ Range_map sig x)) ->
    Disjoint _ (FromList l0) (Dom_map sig) ->
    (apply_r (set_list (combine l0 (apply_r_list sig l)) (M.empty var))
             (apply_r sig v)) =
    (apply_r (set_list (combine l0 (apply_r_list sig l)) sig) v).
  Proof.
    intros.
    assert (Hl0 := Decidable_FromList l0).
    inv Hl0. specialize (Dec v). inv Dec.
    - assert (H' := H v H1).
      unfold apply_r in H'.
      destruct (Maps.PTree.get v sig) eqn:gvs.
      + exfalso. inv H0.
        specialize (H2 v). apply H2. split; auto.
        exists v0. auto.
      + inv H'.
        exfalso. auto.
        rewrite apply_r_none with (v := v); auto.
        clear H. clear H2. clear H0. revert l.  induction l0.
        * simpl. unfold apply_r.
          rewrite M.gempty. rewrite gvs. auto.
        * intro. simpl.
          destruct (apply_r_list sig l) eqn:asl.
          simpl.
          unfold apply_r.
          rewrite M.gempty. rewrite gvs. auto.
          simpl in H1.
          destruct (var_dec a v).
          subst.
          simpl.
          rewrite apply_r_some with (y := v0).
          rewrite apply_r_some with (y := v0).
          auto. apply M.gss. apply M.gss.
          inv H1. exfalso; auto.
          simpl. rewrite apply_r_set2; auto.
          rewrite apply_r_set2; auto.
          destruct l. simpl in asl. inv asl.
          simpl in asl. inv asl.
          apply IHl0.
          auto.
    - symmetry.
      rewrite apply_r_set_list2; auto.
      assert (Hl0 := Decidable_FromList l0).
      inv Hl0. specialize (Dec (apply_r sig v)). inv Dec.
      + unfold apply_r in H2. destruct (Maps.PTree.get v sig) eqn:gvs.
        * unfold apply_r in H. rewrite gvs in H.
          apply H in H2. inv H2. exfalso; auto.
          exfalso. apply H3. exists v. auto.
        * exfalso; auto.
      + rewrite apply_r_set_list2; auto.
  Qed.

  Theorem set_list_rename_all_arl :
    forall l0 l  sig l1,
      Included _ (FromList l0) (Union _ (Complement _  (Range_map sig)) (Complement _ (FromList (apply_r_list sig l1)))) ->
      Disjoint _ (FromList l0) (Dom_map sig) ->

      (apply_r_list (set_list (combine l0 (apply_r_list sig l)) (M.empty var))
                    (apply_r_list sig l1)) =
      (apply_r_list (set_list (combine l0 (apply_r_list sig l)) sig) l1).
  Proof.
    induction l1; intros.
    - auto.
    - simpl.
      rewrite IHl1.
      rewrite set_list_rename_all_ar.
      reflexivity. intros.
      apply H in H1. inv H1. auto.
      left. simpl in H2. intro. apply H2. subst.
      constructor. auto.
      auto.
      intro. intros. apply H in H1. inv H1.
      auto.
      right. intro. apply H2. simpl.
      right. auto.
      auto.
  Qed.


  Theorem set_list_rename_all_ns:
    forall l0 l,
      (forall e sig,
         Included _ (FromList l0) (Union _ (Complement _ (Range_map sig)) (dead_var (rename_all_ns sig e))) ->
         Disjoint _ (FromList l0) (Dom_map sig) ->
         rename_all_ns (set_list (combine l0 (apply_r_list sig l)) (M.empty var))
                       (rename_all_ns sig e)  =
         rename_all_ns (set_list (combine l0 (apply_r_list sig l)) sig) e) /\
      (forall f sig,
         Included _ (FromList l0) (Union _ (Complement _ (Range_map sig)) (dead_var_fundefs (rename_all_fun_ns sig f))) ->
         Disjoint _ (FromList l0) (Dom_map sig) ->
         rename_all_fun_ns (set_list (combine l0 (apply_r_list sig l)) (M.empty var))
                           (rename_all_fun_ns sig f)  =
         rename_all_fun_ns (set_list (combine l0 (apply_r_list sig l)) sig) f)
  .
  Proof.
    intros l0 l.
    assert (Hpr := prop_rename_all).
    destruct Hpr as (Hpr1, Hpr2).
    eapply exp_def_mutual_ind; intros; simpl.
    - rewrite set_list_rename_all_arl; auto.
      2:{ intro. intro. apply H0 in H2. inv H2; auto.
          right. intro. simpl in H3. inv H3; pi0.
          apply not_occur_list_not_in in H4. auto. }
      rewrite H; auto.
      intro. intro. apply H0 in H2.
      inv H2. auto.
      right.
      inv H3; pi0. auto.
    - rewrite set_list_rename_all_ar; auto.
      intros. apply H in H1.
      inv H1. auto. left.
      inv H2. intro.
      destruct (term_util.var_dec x (apply_r sig v)).
      lia.
      auto.
    - rewrite H; auto.
      specialize (H0 sig).
      assert (FromList l0 \subset
                       Union var (Complement var (Range_map sig))
                       (dead_var (rename_all_ns sig (Ecase v l1)))).
      intro; intro. apply H1 in H3. inv H3; auto.
      inv H4; pi0. inv H7; pi0. right.
      eapply num_occur_n.
      constructor; eauto. simpl.
      destruct (term_util.var_dec x (apply_r sig v)). now  exfalso; auto.
      lia.
      specialize (H0 H3 H2).
      simpl in H0. inv H0. auto.
      intro; intro. apply H1 in H3. inv H3; auto.
      inv H4; pi0.
      inv H7; pi0. auto.
    - rewrite set_list_rename_all_ar; auto.
      rewrite H; auto.
      intro; intro. apply H0 in H2. inv H2.
      auto.
      right. inv H3; pi0. auto.
      intros. apply H0 in H2. inv H2; auto.
      inv H3; pi0; dec_vars. auto.
    - rewrite set_list_rename_all_ar; auto.
      rewrite set_list_rename_all_arl; auto.
      2:{ intro. intro. apply H0 in H2. inv H2; auto.
          right. intro. simpl in H3. inv H3; pi0. dec_vars.
          apply not_occur_list_not_in in H3. auto. }
      rewrite H; auto.
      intro. intro. apply H0 in H2.
      inv H2. auto.
      right.
      inv H3; pi0. auto.
      intros z Hin. apply H0 in Hin. inv Hin; auto.
      inv H2; pi0; dec_vars; pi0; auto.
    - rewrite H; auto.
      rewrite H0; auto.
      intro; intro. apply H1 in H3; inv H3; auto.
      inv H4; pi0; auto.
      intro; intro. apply H1 in H3; inv H3; auto.
      inv H4; pi0; auto.
    - rewrite set_list_rename_all_ar; auto.
      rewrite set_list_rename_all_arl; auto.
      intro; intro. apply H in H1.
      inv H1; auto.
      right. inv H2; pi0; dec_vars.
      apply  not_occur_list_not_in. auto.
      intros. apply H in H1. inv H1; auto.
      inv H2; pi0; dec_vars; auto.
    - rewrite H; auto.
      intro; intro.
      apply H0 in H2. inv H2; auto. inv H3; pi0.
      auto.
    - rewrite set_list_rename_all_arl; auto.
      rewrite H; auto.
      intro; intro.
      apply H0 in H2. inv H2; auto. inv H3; pi0.
      auto.
      intro; intro.
      apply H0 in H2. inv H2; auto. inv H3; pi0.
      right. apply not_occur_list_not_in; auto.
    - rewrite set_list_rename_all_ar; auto.
      intro; intro.
      apply H in H1. inv H1; auto.
      inv H2; pi0; dec_vars; auto.
    - rewrite H; auto.
      rewrite H0; auto.
      intro; intros. apply H1 in H3. inv H3; auto.
      inv H4; pi0. auto.
      intro; intros. apply H1 in H3. inv H3; auto.
      inv H4; pi0. auto.
    - auto.
  Qed.

  Theorem FromList_set_list:
    forall {A} x y sig l (l':list A),
      M.get x (set_list (combine l l') sig) = Some y ->
      List.length l = List.length l' ->
      FromList l x ->
      FromList l' y.
  Proof.
    induction l; intros.
    inv H1.
    destruct l'. simpl in H0. inv H0.
    simpl in H0.
    simpl in H.
    inv H1.
    rewrite M.gss in H. inv H. constructor. auto.
    destruct (var_dec a x). subst. rewrite M.gss in H.
    inv H; constructor; auto.
    rewrite M.gso in H.
    right.
    eapply IHl; auto. auto.
  Qed.


  Theorem num_occur_rename_all_ns_set_list:
    (forall (e : exp) (m : nat) f l x n (sigma : r_map),
       ~ FromList l f ->
       num_occur (rename_all_ns sigma e) f m ->
       num_occur (rename_all_ns (set_list (combine x l) sigma) e) f n -> n <= m).
  Proof.
    induction l; intros.
    destruct x; simpl in H1.
    assert (n = m).
    eapply (proj1 (num_occur_det _ )); eauto.
    subst. constructor.
    assert (n = m).
    eapply (proj1 (num_occur_det _ )); eauto.
    subst. constructor.
    destruct x. simpl in H1.
    assert (n = m).
    eapply (proj1 (num_occur_det _ )); eauto.
    subst. constructor.
    simpl in H1.
    assert (exists n,  num_occur (rename_all_ns (set_list (combine x l) sigma) e) f n) by apply e_num_occur.
    destruct H2.
    etransitivity; revgoals.
    eapply IHl. intro; apply H. constructor 2; auto.
    apply H0. apply H2.
    assert (f <> a). intro. apply H. constructor. auto.
    eapply (proj1 (num_occur_rename_all_ns_set _ _ _ H3)).
    apply H2. apply H1.
  Qed.

  Theorem dead_occur_rename_all_ns_set_list:
    (forall (e : exp) f l x (sigma : r_map),
       ~ FromList l f ->
       num_occur (rename_all_ns sigma e) f 0 ->
       num_occur (rename_all_ns (set_list (combine x l) sigma) e) f 0).
  Proof.
    intros.
    assert (exists n, num_occur (rename_all_ns (set_list (combine x l) sigma) e) f n) by apply e_num_occur.
    destruct H1.
    assert (x0 <= 0).
    eapply num_occur_rename_all_ns_set_list; eauto.
    apply Nat.le_0_r in H2. subst; auto.
  Qed.

  Theorem length_apply_r_list:
    forall sig l,
      List.length (apply_r_list sig l) = List.length l.
  Proof.
    induction l; simpl; auto.
  Qed.

  Theorem nthN_map:
    forall A B  f l n v,
      nthN l n = Some v ->
      nthN (@map A B f l) n = Some (f v).
  Proof.
    induction l; intros.
    - inv H.
    - simpl in H. destruct n.
      simpl. inv H; auto.
      apply IHl.
      simpl. destruct p. apply H.
      apply H.
      apply H.
  Qed.

  Theorem num_occur_fds_le_antimon:
    forall im im',
      b_map_le im im' ->
      forall f,
      forall f4 n m,
        num_occur_fds (inlined_fundefs_f f4 im) f n ->
        num_occur_fds (inlined_fundefs_f f4 im') f m ->
        m <= n.
  Proof.
    induction f4; simpl; intros.
    - destruct (get_b v im) eqn:gbvim.
      apply H in gbvim.
      rewrite gbvim in H1. eauto.
      inv H0.
      destruct (get_b v im').
      specialize (IHf4 _ _ H10 H1). lia.
      inv H1.
      apply Nat.add_le_mono; eauto.
      apply Nat.eq_le_incl.
      eapply (proj1 (num_occur_det _)); eauto.
    - inv H0; inv H1; auto.
  Qed.

  Theorem num_occur_case_det:
    forall f cl n m ,
      num_occur_case cl f n ->
      num_occur_case cl f m ->
      n = m.
  Proof.
    induction cl; intros; inv H; inv H0; eauto.
    erewrite IHcl with (n := m0); eauto.
    erewrite (proj1 (num_occur_det _) _ n0); eauto.
  Qed.


  Theorem num_occur_ec_le_antimon:
    forall im im',
      b_map_le im im' ->
      forall f,
        (forall c n m,
           num_occur_ec (inlined_ctx_f c im) f n ->
           num_occur_ec (inlined_ctx_f c im') f m ->
           m <= n) /\
        (forall cfds n m,
           num_occur_fdc (inlined_fundefs_ctx_f cfds im) f n ->
           num_occur_fdc (inlined_fundefs_ctx_f cfds im') f m ->
           m <= n).
  Proof.
    intros im im' Him f.
    exp_fundefs_ctx_induction IHc IHf; intros nn mm Hn Hm; simpl in *;
    try (inversion Hn; inversion Hm; subst); auto; try (apply Nat.add_le_mono; eauto).
    - intro. simpl in *. inv H. simpl.
      repeat apply Nat.add_le_mono; eauto.
      apply Nat.eq_le_incl.
      eapply num_occur_case_det; eauto.
      apply Nat.eq_le_incl.
      eapply num_occur_case_det; eauto.
    - intro. inversion H0; subst.
      repeat apply Nat.add_le_mono; eauto.
      apply Nat.eq_le_incl.
      eapply num_occur_case_det; eauto.
      apply Nat.eq_le_incl.
      eapply num_occur_case_det; eauto.
    - clear Hm; clear Hn.
      eapply num_occur_fds_le_antimon; eauto.
    - clear Hm; clear Hn.
      apply Nat.eq_le_incl.
      eapply (proj1 (num_occur_det _)); eauto.
    - apply Nat.eq_le_incl.
      eapply (proj2 (num_occur_det _)); eauto.
    - apply Nat.eq_le_incl.
      eapply (proj1 (num_occur_det _)); eauto.
  Qed.

  Theorem dead_occur_ec_le_antimon:
    forall im im' c f,
      b_map_le im im' ->
      num_occur_ec (inlined_ctx_f c im) f 0 ->
      num_occur_ec (inlined_ctx_f c im') f 0.
  Proof.
    intros.
    assert (exists n, num_occur_ec (inlined_ctx_f c im') f n) by apply e_num_occur_ec.
    destruct H1.
    assert (x <= 0).
    eapply (proj1 (num_occur_ec_le_antimon _ _ H _)); eauto.
    apply Nat.le_0_r in H2.
    subst; auto.
  Qed.

  Lemma apply_r_list_push:
    forall v v1 sig l,
      List.In v1 l ->
      List.In (apply_r sig v1) (apply_r_list (M.set v (apply_r sig v1) sig) l).
  Proof.
    induction l; intros.
    - inv H.
    - inv H.
      + simpl.
        left.
        destruct (var_dec v v1).
        * subst.
          unfold apply_r.
          rewrite M.gss. auto.
        * apply apply_r_set2. auto.
      + simpl. right.
        eauto.
  Qed.




  (* TODO: move to identifiers *)




  Theorem dead_not_free:
    (forall e, Disjoint _ (dead_var e) (occurs_free e)) /\
    (forall fds, Disjoint _ (dead_var_fundefs fds) (occurs_free_fundefs fds)).
  Proof.
    split.
    - intros x. constructor. intros z Hnin. inv Hnin.
      eapply not_occurs_not_free in H. contradiction.
    - intros x. constructor. intros z Hnin. inv Hnin.
      eapply not_occurs_not_free in H. contradiction.
  Qed.

  Theorem precontractfun_sig_nbv:
    forall fds_c sig count sub fds_c' count' sub',
      precontractfun sig count sub fds_c = (fds_c', count', sub') ->
      eq_env_P (Complement _ (name_in_fundefs fds_c)) sub sub'.
  Proof.
    induction fds_c; intros.
    - simpl in H. destruct (get_c v count).
      eapply IHfds_c in H. intro. intro. apply H.
      intro; apply H0. simpl. auto.
      remember (precontractfun sig count sub fds_c).
      destruct p. destruct p. symmetry in Heqp.
      apply IHfds_c in Heqp.
      inv H. intro. intro. simpl in H.
      apply Union_DeMorgan in H. inv H.
      rewrite M.gso. apply Heqp. auto.
      intro; apply H0. subst; auto.
    - simpl in H. inv H. intro. intro. auto.
  Qed.

  Hint Constructors bound_not_stem_ctx : core.
  Hint Constructors bound_not_stem_fundefs_ctx : core.

  Theorem Proper_Intersection:
    forall A : Type, Proper (Same_set A ==> Same_set A ==> Same_set A) (Intersection A).
  Proof.
    intros. intro. intros. intro. intros. split; intro; intros.
    inv H1. apply H in H2. apply H0 in H3. auto.
    inv H1. apply H in H2.
    apply H0 in H3. auto.
  Qed.

  Theorem findtag_map: forall f (c0:ctor_tag) e l,
                         findtag l c0 = Some e ->
                         @findtag exp
                                  (map (fun p : var * exp => let (k, e0) := p in (k, f e0))
                                       l) c0 = Some (f e).
  Proof.
    induction l; intro. inv H.
    simpl in H. simpl. destruct a.
    destruct (M.elt_eq c c0). inv H; auto.
    apply IHl in H. auto.
  Qed.


  Theorem contractcases_corresp:
    forall cl2 cl1 sig c im x count sub,
      (* recursive call to shrink_corresp *)
      (forall e sub' im' sig c count,
         (term_sub_inl_size (e, sub', im') < term_sub_inl_size (Ecase x cl2, sub, im)) ->
         let ce := (app_ctx_f (rename_all_ctx_ns sig (inlined_ctx_f c im')) (rename_all_ns sig e)) in
         unique_bindings ce ->
         closed_exp ce ->
         c_count ce count ->
         cmap_view_ctx sub' c ->
         inl_inv im' sub' ce ->
         sig_inv_full sig (rename_all_ctx_ns sig (inlined_ctx_f c im')) (rename_all_ns sig e) ->
         forall e' count' steps im'' BP,
           contract sig count e sub' im' = existT _ (e', steps, count', im'') BP ->
           let ce' := (app_ctx_f (rename_all_ctx_ns sig (inlined_ctx_f c im'')) e') in
           gsr_clos steps ce ce' /\ c_count ce' count' /\ inl_inv im'' sub' ce' /\
           sig_inv_codom sig (rename_all_ctx_ns sig (inlined_ctx_f c im'')) e') ->
      (* actual statement of contract_case *)
      let ce := (app_ctx_f (rename_all_ctx_ns sig (inlined_ctx_f c im)) (Ecase x (cl1 ++ (rename_all_case sig cl2)))) in
      unique_bindings ce ->
      closed_exp ce ->
      c_count ce count ->
      cmap_view_ctx sub c ->
      inl_inv im sub ce ->
      sig_inv_full sig (rename_all_ctx_ns sig (inlined_ctx_f c im)) (Ecase x (cl1 ++ (rename_all_case sig cl2)))  ->
      forall cl2' steps count' im' oes pfe pfsub bp,
        contractcases oes (fun rm cm es H => contract rm cm (fst (fst es)) (snd (fst es)) (snd es)) sig count im sub cl2 pfe pfsub = existT _ (cl2', steps, count', im') bp ->
        let ce' := (app_ctx_f (rename_all_ctx_ns sig (inlined_ctx_f c im')) (Ecase x (cl1 ++ cl2'))) in
        gsr_clos steps ce ce' /\ c_count ce' count' /\ inl_inv im' sub ce' /\
        sig_inv_codom sig (rename_all_ctx_ns sig (inlined_ctx_f c im')) (Ecase x (cl1 ++ cl2')).
  Proof.
    induction cl2; intros cl1 sig c im x count sub;
    intro Hcontract_corresp;
    intros; simpl in H5.
    - inv H5; unfold ce in *; unfold ce' in *; split; auto.
      apply Refl_srw.
      split; auto. split; auto.
      apply sig_inv_combine in H4. inv H4. simpl in H6. auto.
    - destruct a.
      remember (contract sig count e sub im) as con_e.
      destruct con_e.
      destruct x0.
      destruct p. destruct p.
      simpl in ce.
      assert (Hcl1: (rename_all_ns sig (Ecase x cl1)) = Ecase x cl1 ). {
        rewrite <- (proj1 (rename_all_no_shadow _)).
        apply Disjoint_dom_rename_all.

        (* by sig inv dead using H4 *)
        split. intro. intro.
        inv H6.
        inv H7.
        apply H4 in H6.
        destruct H6 as (H6, H6c).
        apply not_bound_dead_or_free in H6.
        inv H6.
        2:               apply H0 in H7; inv H7.
        unfold ce in H7.
        apply num_occur_app_ctx in H7. destructAll; pi0.
        inv H7.
        apply num_occur_app_case in H12.
        destructAll.
        pi0. dec_vars.
        assert (~(occurs_free (Ecase x cl1)) x0).
        apply not_occurs_not_free.
        eapply num_occur_n.
        constructor; eauto.
        simpl. destruct (term_util.var_dec x0 x). exfalso; auto. auto.
        auto.
        (* using H4 *)
        eapply sig_inv_dom_mon.
        2:{ apply sig_inv_combine in H4. destruct H4.
            eauto. }
        rewrite bound_var_app_ctx.
        rewrite bound_var_Ecase_app. sets. }

      rename c0 into v.
      assert (rename_all_ctx_ns sig (inlined_ctx_f c im)
             |[ Ecase x  (cl1 ++ (v, rename_all_ns sig e) :: rename_all_case sig cl2) ]| = rename_all_ctx_ns sig (inlined_ctx_f (comp_ctx_f c (Ecase_c x cl1 v Hole_c cl2)) im)
             |[ rename_all_ns sig e]|).
      {
        assert (
            Ecase x (cl1 ++ (v, rename_all_ns sig e) :: rename_all_case sig cl2) =
            rename_all_ns sig (Ecase x (cl1 ++ (v, e) :: cl2))).
        {
          simpl. rewrite list_append_map.
          simpl in Hcl1. inversion Hcl1.
          repeat rewrite H8.
          repeat rewrite H7.
          reflexivity.
        }
        rewrite H6.
        clear H6.
        do 2 (rewrite <- (proj1 (rename_all_ns_app_ctx _ _))).
        rewrite (proj1 inlined_comp_ctx).
        simpl.
        rewrite <- app_ctx_f_fuse.
        simpl. reflexivity.
      }
      symmetry in Heqcon_e.

      eapply Hcontract_corresp with
      (c :=  (comp_ctx_f c (Ecase_c x cl1 v Hole_c cl2)))
        in Heqcon_e; try (rewrite <- H6; auto).
      2:{ unfold term_sub_inl_size. simpl. lia. }

      (*
        eapply shrink_corresp with
        (c :=  (comp_ctx_f c (Ecase_c x cl1 v Hole_c cl2)))
          in Heqcon_e; try (rewrite <- H6; auto). *)
      2:{ apply cmap_view_case. auto. }

      (* push Disjoint, Unique and Sub_inv through e0 *)
      destruct Heqcon_e as (H7, H8).
      destruct H8 as (H8, H9).
      destruct H9 as (H9, H_sig_r).
      rewrite <- H6 in H7.
      assert (Hub' := gsr_clos_preserves_clos _ _ _ H H0 H7).
      destructAll.
      apply sig_inv_combine in H4.
      destruct H4 as (H4, H4c).
      assert (Hse := gsr_preserves_sig_dom _ _ _ _ H (closed_implies_Disjoint _ H0) H7 H4).
      assert (He0 : rename_all_ns sig e0 = e0). {
        rewrite <- (proj1 (rename_all_no_shadow _)).
        apply Disjoint_dom_rename_all.

        split; intros; intro. inv H12.
        inv H13. apply Hse in H12.
        apply not_bound_dead_or_free in H12.
        inv H12.
        2: apply H11 in H13; inv H13.

        apply num_occur_app_ctx in H13; destructAll; pi0; auto.
        apply not_occurs_not_free in H13. auto.
        eapply sig_inv_dom_mon.
        2: apply Hse.
        rewrite bound_var_app_ctx.
        right; auto.
      }

      assert (
        (rename_all_ctx_ns sig
                           (inlined_ctx_f (comp_ctx_f c (Ecase_c x cl1 v Hole_c cl2)) b0)
        |[ rename_all_ns sig e0 ]|) =
        (rename_all_ctx_ns sig
                           (inlined_ctx_f c b0)
        |[  (Ecase x ((cl1++[(v,e0)])++(rename_all_case sig cl2)))]|)).
      {
        assert (Ecase x ((cl1 ++ [(v, e0)]) ++ rename_all_case sig cl2)  =
                rename_all_ns sig (Ecase x ((cl1 ++ [(v, e0)]) ++ cl2))).
        {
          simpl.
          inversion Hcl1.
          rewrite list_append_map.
          rewrite list_append_map.
          simpl.
          repeat rewrite H14.
          repeat rewrite H13.
          rewrite He0. reflexivity.
        }
        rewrite H12. clear H12.

        do 2 (rewrite <- (proj1 (rename_all_ns_app_ctx _ _))).
        rewrite (proj1 inlined_comp_ctx).
        simpl.
        rewrite <- app_ctx_f_fuse.
        simpl.
        rewrite <- app_assoc. simpl. reflexivity.
      }

      (* I.H. *)
      remember (contractcases oes
                              (fun (rm : r_map) (cm : c_map)
                                   (es : prod (prod exp ctx_map) b_map)
                                   (_ : lt (term_sub_inl_size es) (term_sub_inl_size oes)) =>
                                 contract rm cm
                                          (@fst exp ctx_map (@fst (prod exp ctx_map) b_map es))
                                          (@snd exp ctx_map (@fst (prod exp ctx_map) b_map es))
                                          (@snd (prod exp ctx_map) b_map es)) sig c1 b0 sub cl2
                              (@subcl_e_cons_l v e cl2
                                               (@fst exp ctx_map (@fst (prod exp ctx_map) b_map oes))
                                               (@eq_ind_r (list (prod var exp))
                                                          (@cons (prod ctor_tag exp) (@pair ctor_tag exp v e) cl2)
                                                          (fun x : list (prod var exp) =>
                                                             subcl_e x
                                                                     (@fst exp ctx_map (@fst (prod exp ctx_map) b_map oes)))
                                                          pfe (@cons (prod var exp) (@pair var exp v e) cl2)
                                                          (@eq_refl (list (prod var exp))
                                                                    (@cons (prod ctor_tag exp) (@pair ctor_tag exp v e) cl2))))
                              (@sub_inl_size_compat sub im b0
                                                    (@snd exp ctx_map (@fst (prod exp ctx_map) b_map oes))
                                                    (@snd (prod exp ctx_map) b_map oes) pfsub b)) as cc_ind.
      destruct cc_ind. destruct x0.
      destruct p. destruct p.
      symmetry in Heqcc_ind.
      rewrite He0 in H12.
      rewrite H12 in *.


      eapply IHcl2 in Heqcc_ind; eauto.
      destruct Heqcc_ind.
      destruct H14.
      destruct H15 as (H15, Hsig_r).
      clear He0.
      inv H5. unfold ce'.
      split.
      eapply gsr_clos_trans.
      now apply H7.
      do 2 (rewrite <- app_assoc in H13).
      simpl in H13.
      rewrite <- app_assoc.
      simpl.
      auto.
      rewrite <- app_assoc in H14.
      rewrite <- app_assoc in H15.
      split; auto.
      split; auto.
      rewrite <- app_assoc in Hsig_r.
      simpl in Hsig_r. auto.
      {
        intros.
        eapply Hcontract_corresp; eauto.
        etransitivity. apply H13.
        assert (sub_inl_size sub b0 <= sub_inl_size sub im).
        apply sub_size_le. apply b_map_le_c. auto.
        simpl. unfold term_sub_inl_size. simpl.
        assert ( 1 <= term_size e) by apply min_term_size.
        lia.
      }
      {
        apply sig_inv_combine.
        split.
        - (* dom *)
          auto.
        - (* codom *)
          intro. intros. apply H_sig_r in H13.
          rewrite H12 in H13.
          destruct H13; auto.
          right.
          repeat normalize_ctx.
          apply bound_stem_comp_ctx_mut in H13. inversion H13; auto.
          simpl in H14. inversion H14. inversion H22.
      }
      intro. intros.
      apply H4 in H7. destruct H7.
      split.
      +  intro. apply H7.
         apply bound_var_app_ctx.
         apply bound_var_app_ctx in H9.
         repeat normalize_ctx.
         inv H9.
         apply bound_var_ctx_comp_ctx in H10.
         inv H10.
         left; auto.
         right.
         normalize_bound_var.

         apply bound_var_ctx_rename_all_ns in H9.
         simpl in H9.
         normalize_bound_var_ctx_in_ctx.
         inv H9.
         auto.
         inv H10. inv H9.
         right.
         apply bound_var_rename_all_ns with (sigma := sig) in H9.
         simpl in H9. inv H9.
         eapply Bound_Ecase.
         apply H12. right; eauto.
         right.
         normalize_bound_var.
         right.
         eapply Bound_Ecase.
         2:{ left. eauto. } auto.
      + inv H8.
        * left.
          apply num_occur_app_ctx in H9. destructAll; pi0.
          inv H9; pi0.
          apply num_occur_app_case in H13.
          destructAll; pi0.
          inv H11; pi0.
          simpl.
          apply num_occur_app_ctx. exists 0, 0; split; auto.
          rewrite (proj1 inlined_comp_ctx).
          rewrite (proj1 (rename_all_ctx_ns_comp_ctx _ _)).
          apply num_occur_ec_comp_ctx.
          exists 0, 0. repeat split; auto.
          simpl.
          eapply num_occur_ec_n.
          constructor. simpl in Hcl1. inversion Hcl1.
          rewrite H13. rewrite H13.
          eauto.
          constructor.
          eauto.
          simpl.
          unfold apply_r.
          destruct ( @Maps.PTree.get Maps.PTree.elt x sig) eqn:gxs.
          exfalso.
          apply H4 in gxs.
          destruct gxs.
          apply not_bound_dead_or_free in H11. inv H11.
          apply num_occur_app_ctx in H13.
          destructAll; pi0.
          inv H13.
          destruct (term_util.var_dec x x). now inv H20. now eauto.
          apply H0 in H13. inv H13. unfold var, M.elt in *. rewrite gxs.
          destruct (term_util.var_dec y x).
          now exfalso; auto.
          auto.
        * right.
          repeat normalize_ctx.
          apply bound_stem_comp_ctx_mut.
          left; auto.
  Qed.


  (* move to shrink_cps_correct *)
  Theorem gsr_included_bv :
    forall n e e',
      gsr_clos n e e' ->
      Included _ (bound_var e') (bound_var e).
  Proof.
    intros n e e' Hrw.
    induction Hrw.
    - inv H; inv H0; rewrite !bound_var_app_ctx in *;
        repeat normalize_bound_var; eapply Included_trans; eauto with Ensembles_DB.
      + apply Included_Union_compat. sets. repeat normalize_bound_var.
        rewrite !fundefs_append_bound_vars; [| reflexivity ].
        rewrite !fundefs_append_bound_vars with (B3 := fundefs_append B1 (Fcons f t xs fb B2)); [| reflexivity ].
        repeat normalize_bound_var. sets.
      + normalize_bound_var. rewrite !bound_var_app_ctx in *.
        rewrite !Union_assoc. apply Included_Union_compat; sets.
        apply Included_Union_compat; sets. intros x1 Hin. econstructor. eassumption.
        eapply find_tag_nth_In_patterns. eassumption.
      + rewrite !bound_var_app_ctx. repeat normalize_bound_var. rewrite !bound_var_app_ctx.
        rewrite <- bound_var_rename_all_ns. sets.
      + rewrite !bound_var_app_ctx. repeat normalize_bound_var. rewrite !bound_var_app_ctx.
        rewrite <- bound_var_rename_all_ns.
        rewrite !fundefs_append_bound_vars; [| reflexivity ].
        rewrite !fundefs_append_bound_vars with (B3 := fundefs_append B1 (Fcons f t xs fb B2)); [| reflexivity ].
        normalize_bound_var. xsets.
      + rewrite !bound_var_app_ctx. repeat normalize_bound_var. rewrite !bound_var_app_ctx.
        rewrite <- bound_var_rename_all_ns.
        rewrite !fundefs_append_bound_vars; [| reflexivity ].
        rewrite !fundefs_append_bound_vars with (B3 := fundefs_append B1 (Fcons f t xs fb B2)); [| reflexivity ].
        normalize_bound_var. eapply bound_var_inline_letapp in H2.
        rewrite !Union_assoc. eapply Union_Included; sets. eapply Union_Included. now xsets.
        eapply Included_trans. eassumption.
        rewrite <- bound_var_rename_all_ns. xsets.
    - sets.
  Qed.


  Theorem inlined_fundefs_ctx_append1:
    forall v f l fds_c im fds,
      (inlined_fundefs_ctx_f
         (fundefs_ctx_append (inlined_fundefs_f fds im)
                             (Fcons1_c v f l Hole_c (inlined_fundefs_f fds_c im))) im) =
      (fundefs_ctx_append (inlined_fundefs_f fds im)
                          (Fcons1_c v f l Hole_c (inlined_fundefs_f fds_c im))).
  Proof.
    induction fds; intros; simpl; auto.
    destruct (get_b v0 im); auto.
    simpl.
    rewrite IHfds.
    reflexivity.
  Qed.


  Theorem inlined_fundefs_ctx_append_shallow:
    forall v f l fds_c b0 fds,
      (inlined_fundefs_ctx_f
         (fundefs_ctx_append fds
                             (Fcons1_c v f l Hole_c fds_c)) b0) =
      (fundefs_ctx_append fds
                          (Fcons1_c v f l Hole_c fds_c)).
  Proof.
    intros.
    induction fds.
    - simpl.

      rewrite IHfds. auto.
    - simpl. reflexivity.
  Qed.



  Theorem rename_all_fundefs_ctx_append:
    forall sig fdc fds,
      rename_all_fun_ctx_ns sig (fundefs_ctx_append fds fdc) =
      fundefs_ctx_append (rename_all_fun_ns sig fds)
                         (rename_all_fun_ctx_ns sig fdc).
  Proof.
    induction fds; auto.
    simpl.
    rewrite IHfds. auto.
  Qed.

  Theorem app_f_ctx_fundefs_ctx_append:
    forall fdc e fds,
      fundefs_ctx_append fds fdc <[ e ]> =
      fundefs_append fds (fdc <[e]>).
  Proof.
    induction fds; auto.
    simpl; rewrite IHfds. auto.
  Qed.




  Theorem bound_var_fundefs_ctx_append_f:
    forall im fdc,
      Included _ (names_in_fundefs_ctx fdc)
               (bound_var_fundefs_ctx (inlined_fundefs_ctx_f fdc im)).
  Proof.
    induction fdc.
    - simpl.
      normalize_bound_var_ctx.
      intro. intro. inv H; auto.
      apply name_in_fundefs_bound_var_fundefs in H0.
      auto.
    - simpl.
      normalize_bound_var_ctx.
      intro; intro.
      inv H; auto.
  Qed.

  Theorem name_in_fundefs_ctx_append:
    forall fdc fds,
      Same_set _ (names_in_fundefs_ctx (fundefs_ctx_append fds fdc)) (Union _ (name_in_fundefs fds) (names_in_fundefs_ctx fdc)).
  Proof.
    induction fds.
    - simpl. rewrite IHfds; auto with Ensembles_DB.
    - simpl. auto with Ensembles_DB.
  Qed.

  Theorem bound_var_fundefs_ctx_append:
    forall fdc fds,
      Same_set _ (bound_var_fundefs_ctx
                    (fundefs_ctx_append fds fdc))
               (Union _ (bound_var_fundefs fds) (bound_var_fundefs_ctx fdc)).
  Proof.
    induction fds; simpl; normalize_bound_var; try normalize_bound_var_ctx; eauto with Ensembles_DB.
    rewrite IHfds.
    eauto with Ensembles_DB.
  Qed.



  Theorem name_in_fundefs_not_inlined:
    forall f im fds,
      get_b f im = false ->
      (name_in_fundefs fds f <-> name_in_fundefs (inlined_fundefs_f fds im) f).
  Proof.
    induction fds; simpl; intros.
    2: split; intro; auto.
    destruct (var_dec v f).
    - subst. rewrite H. simpl.
      split; intro. left; auto.  left; auto.
    - split. intro. inv H0.
      exfalso. apply n. inv H1. auto.
      apply IHfds in H1; auto.
      destruct (get_b v im); auto. constructor 2. auto.
      intro. right.
      apply IHfds; auto.
      destruct (get_b v im). auto. inv H0.
      exfalso; apply n; inv H1; auto.
      auto.
  Qed.

  Theorem Included_name_in_fundefs_inlined:
    forall im fds,
      Included _ (name_in_fundefs (inlined_fundefs_f fds im)) (name_in_fundefs fds).
  Proof.
    induction fds; eauto with Ensembles_DB.
    simpl. destruct (get_b v im); simpl; auto with Ensembles_DB.
  Qed.


  Theorem name_in_fundefs_not_inlined':
    forall f fds im,
      name_in_fundefs fds f ->
      get_b f im = false ->
      bound_var_fundefs (inlined_fundefs_f fds im) f.
  Proof.
    induction fds; simpl; intros.
    - inv H.
      inv H1.
      rewrite H0.
      apply bound_var_fundefs_Fcons.
      auto.
      specialize (IHfds _ H1 H0).
      destruct (get_b v im); eauto with Ensembles_DB.
    - inv H.
  Qed.


  Theorem fundefs_ctx_append_num_occur:
    forall B1 B2,
    forall (x : var) (n m : nat),
      num_occur_fds B1 x n -> num_occur_fdc B2 x m -> num_occur_fdc (fundefs_ctx_append B1 B2) x (n + m).
  Proof.
    induction B1; intros.
    - simpl in H.
      inv H.
      simpl.
      eapply num_occur_fdc_n.
      constructor. eauto.
      apply IHB1; eauto.
      lia.
    - inv H. auto.
  Qed.

  Theorem fundefs_ctx_append_num_occur':
    forall (B1: fundefs) B2 (nm : nat) (x : var),
      num_occur_fdc (fundefs_ctx_append B1 B2) x nm ->
      exists n m : nat,
        num_occur_fds B1 x n /\ num_occur_fdc B2 x m /\ n + m = nm.
  Proof.
    induction B1; intros.
    - simpl in H. inv H.
      apply IHB1 in H8. destructAll.
      exists (n + x0), x1. split.
      constructor; auto.
      split; auto. lia.
    - simpl in H. exists 0, nm.
      split; auto. constructor.
  Qed.

  Theorem rename_all_fun_ns_inlined_fundefs:
    forall sig im fds,
      (rename_all_fun_ns sig (inlined_fundefs_f fds im)) = (inlined_fundefs_f (rename_all_fun_ns sig fds) im).
  Proof.
    induction fds; simpl.
    - destruct (get_b v im).
      + auto.
      + simpl. rewrite IHfds. auto.
    - auto.
  Qed.

  Theorem update_count_inlined_unaffected:
    forall v0 lx ly count,
      ~FromList lx v0 ->
      ~FromList ly v0 ->
      get_c v0 (update_count_inlined ly lx count) = get_c v0 count.
  Proof.
    induction lx; intros.
    destruct ly; simpl; auto.
    destruct ly. simpl. auto.
    simpl. erewrite IHlx.
    rewrite gdso. rewrite gdso. auto.
    intro; apply H. constructor; auto.
    intro; apply H0. constructor; auto.
    intro; apply H. constructor 2; auto.
    intro; apply H0. constructor 2; auto.
  Qed.

  Theorem  update_count_inlined_dom:
    forall v0 lx ly count,
      List.length lx = List.length ly ->
      FromList lx v0 ->
      Disjoint _ (FromList ly) (FromList lx) ->
      get_c v0
            (update_count_inlined ly lx count) = 0.
  Proof.
    induction lx; intros.
    inv H0.
    destruct ly;  inv H.
    simpl.
    assert (Hlx := Decidable_FromList lx).
    inv Hlx. specialize (Dec v0). inv Dec.
    eapply IHlx. auto. auto. split; intro. intro.
    inv H1. specialize (H4 x). apply H4. inv H2. split; constructor 2; auto.
    inv H0.
    rewrite update_count_inlined_unaffected. rewrite gdso.  rewrite gdss. auto.
    inv H1. specialize (H0 v0). intro; subst. apply H0. split; constructor; auto.
    auto.
    inv H1. specialize (H0 v0). intro; apply H0. split. constructor 2; auto.
    constructor. auto.
    exfalso; auto.
  Qed.


  Theorem dead_occur_fds_le_antimon:
    forall im im' : b_map,
      b_map_le im im' ->
      forall (f : var) (f4 : fundefs),
        num_occur_fds (inlined_fundefs_f f4 im) f 0 ->
        num_occur_fds (inlined_fundefs_f f4 im') f 0.
  Proof.
    intros.
    assert (exists n, num_occur_fds (inlined_fundefs_f f4 im') f n) by apply e_num_occur_fds.
    destruct H1. assert (x <= 0).
    eapply num_occur_fds_le_antimon; eauto.
    apply Nat.le_0_r in H2. subst; auto.
  Qed.

  Inductive sum_range_n: list var -> list var -> exp -> var -> nat -> Prop :=
  | SRN_cons1: forall lx ly e v0 n m x,
                 sum_range_n lx ly e v0 n -> num_occur e x m -> sum_range_n (x::lx) (v0::ly) e v0 (m+n)
  | SRN_cons2: forall lx ly e v n y x,
                 sum_range_n lx ly e v n -> y <> v -> sum_range_n (x::lx) (y::ly) e v n
  | SRN_nil: forall e v,
               sum_range_n nil nil e v 0.



  Theorem e_sum_range_n:
    forall e v lx ly,
      List.length lx  = List.length ly ->
      exists n, sum_range_n lx ly e v n.
  Proof.
    induction lx; intros; destruct ly; inv H. exists 0; constructor.
    apply IHlx in H1. inv H1. destruct (var_dec v0 v).
    subst.
    assert (exists n, num_occur e a n) by apply e_num_occur.
    destruct H0. exists (x0+x). constructor; auto.
    exists x. constructor; auto.
  Qed.


  (* *)
  Theorem update_count_sum_range:
    forall v0 e sig l l0 count n,
      num_occur_list (apply_r_list sig l) v0 <= get_c v0 count ->
      ~ FromList l0 v0 ->
      Disjoint _ (FromList (apply_r_list sig l)) (FromList l0) ->
      (forall x n, FromList l0 x ->
                   num_occur (rename_all_ns sig e) x n ->
                   get_c x count = n) ->
      sum_range_n l0 (apply_r_list sig l) (rename_all_ns sig e) v0 n ->
      NoDup l0 ->
      (get_c v0
             (update_count_inlined (apply_r_list sig l) l0 count ) =
       get_c v0 count  + n - num_occur_list (apply_r_list sig l) v0).
  Proof.
    induction l; intros.
    - inv H3. simpl. lia.
    - inv H3.
      + simpl in H.
        simpl.
        destruct  (term_util.var_dec (apply_r sig a) (apply_r sig a)).
        2: exfalso; auto.
        rewrite IHl with (n := n0); eauto.
        rewrite gdss.
        apply H2 in H12.
        rewrite H12. lia.
        constructor; auto.
        rewrite gdss. lia.
        intro; apply H0. constructor 2; auto.
        eapply Disjoint_Included.
        3: apply H1.
        intro; intro; constructor 2; auto.
        intro; intro; constructor 2; auto.
        intros. rewrite gdso. rewrite gdso.
        apply H2; eauto. constructor 2; auto. intro. inv H4; auto.
        intro. inv H1. specialize (H7 (apply_r sig a)). apply H7. split.
        constructor; auto. constructor 2; auto.
        inv H4; auto.
      + simpl.
        simpl in H.
        destruct ( term_util.var_dec v0 (apply_r sig a)).
        exfalso; auto.
        rewrite IHl with (n := n).
        rewrite gdso by auto. rewrite gdso. reflexivity.
        intro; apply H0. constructor; auto.
        rewrite gdso by auto. rewrite gdso. simpl in H. auto. intro; apply H0. constructor; auto.
        intro; apply H0. constructor 2; auto.
        eapply Disjoint_Included. 3: apply H1.
        intro; intro; constructor 2; auto.
        intro; intro; constructor 2; auto.
        intros. rewrite gdso. rewrite gdso. apply H2.
        constructor 2; auto. auto. inv H4. intro; subst; auto.
        intro. inv H1. specialize (H7 (apply_r sig a)). apply H7. split.
        constructor. auto. constructor 2. auto.
        auto. inv H4; auto.
  Qed.


  Definition set_list_r {A:Type}  (l : list (M.elt * A)) (map: M.t A) : M.t A :=
    fold_left (fun cmap xv => M.set (fst xv) (snd xv) cmap ) l map.

  Theorem num_occur_set_arl_s:
    forall x y sig,
      x <> y ->
      ~ Dom_map sig x ->
      forall l,
        num_occur_list (apply_r_list (M.set x y sig) l) y =
        num_occur_list (apply_r_list sig l) y + num_occur_list l x.
  Proof.
    induction l. auto.
    simpl. destruct (term_util.var_dec x a).
    - subst.
      rewrite apply_r_set1.
      destruct (term_util.var_dec y y).
      2:{ exfalso. apply n; auto. }
      rewrite Disjoint_apply_r.
      destruct (term_util.var_dec y a). exfalso; auto.
      lia.
      split. intro. intro. inv H1. inv H2. apply H0. exists x0. inv H3; auto.
    - rewrite apply_r_set2 by auto.
      destruct (term_util.var_dec y (apply_r sig a)); lia.
  Qed.

  Theorem num_occur_rename_all_set_x:
    forall x y sig,
      x <> y ->
      ~ Dom_map sig x ->
      (forall e n m,
         num_occur e x n ->
         num_occur (rename_all_ns sig e) y m ->
         num_occur (rename_all_ns (M.set x y sig) e) y (n+m)) /\
      (forall fds n m,
         num_occur_fds fds x n ->
         num_occur_fds (rename_all_fun_ns sig fds) y m ->
         num_occur_fds (rename_all_fun_ns (M.set x y sig) fds) y (n+m)).
  Proof.
    intros x y sig Hxy Hdom.
    apply exp_def_mutual_ind; intros; simpl in *; try (inv H0; inv H1).
    - specialize (H _ _ H8 H7).
      eapply num_occur_n.
      constructor. eauto.
      rewrite num_occur_set_arl_s; auto.
      lia.
    - inv H; inv H0.
      inv H5; inv H4.
      eapply num_occur_n. constructor; eauto. constructor.
      assert (Hn := num_occur_set_arl_s _ _ _ Hxy Hdom [v]).
      simpl in Hn. simpl. unfold var in *.
      lia.
    - inv H1; inv H2. inv H7; inv H6.
      specialize (H _ _ H8 H7).
      assert (num_occur (Ecase v l) x ( num_occur_list [v] x + m)).
      constructor; auto.
      assert (num_occur (Ecase (apply_r sig v) (rename_all_case sig l)) y ( num_occur_list [apply_r sig v] y + m0)).
      constructor; auto.
      specialize (H0 _ _ H1 H2).
      inv H0.
      eapply num_occur_n.
      constructor. constructor; eauto.
      simpl. lia.
    - specialize (H _ _ H9 H8).
      eapply num_occur_n. constructor; eauto.
      assert (Hn := num_occur_set_arl_s _ _ _ Hxy Hdom [v0]).
      simpl in Hn. simpl. unfold var in *.
      lia.
    - specialize (H _ _ H9 H8).
      eapply num_occur_n. constructor; eauto.
      assert (Hn := num_occur_set_arl_s _ _ _ Hxy Hdom (f :: ys)).
      simpl in Hn. simpl. unfold var in *.
      lia.
    - inv H1; inv H2.
      specialize (H _ _ H8 H9).
      specialize (H0 _ _ H5 H4).
      eapply num_occur_n. constructor; eauto.
      lia.
    - inv H; inv H0.
      eapply num_occur_n. constructor; eauto.
      assert (Hn := num_occur_set_arl_s _ _ _ Hxy Hdom (v::l)).
      simpl in Hn. simpl.
      unfold var in *. lia.
    - specialize (H _ _ H7 H6).
      eapply num_occur_n. constructor. eauto. lia.
    - specialize (H _ _ H8 H7).
      eapply num_occur_n. constructor. eauto.
      rewrite num_occur_set_arl_s; auto. lia.
    - inv H; inv H0.
      eapply num_occur_n. constructor.
      assert (Hn := num_occur_set_arl_s _ _ _ Hxy Hdom [v]).
      simpl in Hn. simpl. unfold var in *.
      lia.
    - inv H1; inv H2. specialize (H _ _ H10 H9).
      specialize (H0 _ _ H11 H12).
      eapply num_occur_fds_n. constructor; eauto. lia.
    - inv H; inv H0. constructor.
  Qed.

  Theorem sum_range_length:
    forall v0 e lx ly n,
      sum_range_n lx ly e v0 n ->
      List.length lx = List.length ly.
  Proof.
    induction lx; intros. inv H; auto.
    inv H. apply IHlx in H2. simpl; auto.
    apply IHlx in H2. simpl; auto.
  Qed.


  Theorem num_occur_set_list_r:
    forall  m v0 sig e lx ly n,
      Disjoint _ (Dom_map sig) (FromList lx) ->
      Disjoint _ (FromList lx) (FromList ly) ->
      NoDup lx ->
      Included _ (FromList lx) (Union _ (Complement _ (Range_map sig)) (dead_var (rename_all_ns sig e))) ->
      sum_range_n lx ly (rename_all_ns sig e) v0 n ->
      num_occur (rename_all_ns sig e) v0 m ->
      ~ FromList lx v0 ->
      num_occur (rename_all_ns (set_list (combine lx ly) sig) e) v0 (n + m).
  Proof.
    induction lx.
    - intros. inv H3. simpl.  auto.
    - intros.
      rename H5 into Hv0.
      inv H3.
      + simpl.
        assert (H7' := H7).
        eapply IHlx in H7; eauto.
        assert (FromList (a::lx) a) by (constructor; auto).
        apply H2 in H3. inv H3.
        * assert (num_occur e a m0).
          assert (exists n, num_occur e a n) by apply e_num_occur.
          destruct H3. assert (x = m0).
          eapply num_occur_sig_unaffected; eauto.
          inv H. specialize (H6 a). intro. apply H6. split; auto. constructor; auto.
          subst; auto.
          replace (m0 + n0 + m) with (m0 + (n0 + m)) by lia.
          eapply num_occur_rename_all_set_x; eauto.
          inv H0. intro. specialize (H6 a). apply H6; subst.
          split; constructor; auto.
          intro.
          apply Dom_map_set_list in H6.
          inv H6.  inv H1; auto. inv H. specialize (H6 a). apply H6; split; auto.
          constructor; auto.
          eapply sum_range_length; eauto.
        * assert (m0 = 0). eapply (proj1 (num_occur_det _)); eauto.
          subst.
          apply not_occur_rename_not_dom in H5.
          replace (0 + n0 + m) with (0 + (n0 + m)) by lia.
          eapply num_occur_rename_all_set_x; eauto.
          inv H0. intro. specialize (H3 a). subst. apply H3. split; constructor; auto.
          intro. apply Dom_map_set_list in H3. inv H3. inv H1; auto.
          inv H. specialize (H3 a). apply H3. split; auto. constructor; auto.
          eapply sum_range_length; eauto.
          intro. inv H. specialize (H6 a). apply H6. split; auto.
          constructor; auto.
        * eapply Disjoint_Included_r. 2: apply H.
          intro; intro. constructor 2; auto.
        * eapply Disjoint_Included. 3: apply H0.
          intro; intro. constructor 2; auto.
          intro; intro. constructor 2; auto.
        *  inv H1; auto.
        *    intro. intro; apply H2; constructor 2; auto.
        * intro; apply Hv0. constructor 2; auto.
      + simpl.
        inv H1.
        assert (H7' := H7).
        apply IHlx in H7; auto.
        assert (exists n,  num_occur (rename_all_ns (M.set a y (set_list (combine lx ly0) sig)) e) v0 n) by apply e_num_occur. destruct H1.
        assert ((n + m) = x).
        eapply num_occur_rename_all_ns_set_unchanged.  4: apply H7.
        4: apply H1. intro.
        apply  Dom_map_set_list in H3. inv H3; auto.
        inv H. specialize (H3 a). apply H3. split; auto.
        constructor; auto.
        apply sum_range_length in H7'. auto.
        intro; apply Hv0. constructor; auto.
        auto.
        rewrite H3. auto.
        eapply Disjoint_Included_r. 2: apply H. intro; intro. constructor 2; auto.
        eapply Disjoint_Included.
        3: apply H0.
        intro; intro; constructor 2; auto.
        intro; intro; constructor 2; auto.
        intro; intro; apply H2. constructor 2; auto.
        intro; apply Hv0. constructor 2; auto.
  Qed.

  (** update_count_inlined correctly updates the count after inlining a function *)
  Theorem count_inlining:
    forall sig x x1 v f l0 e x2 x0 l count inl,
      let ce := (rename_all_ctx_ns sig
                                   (inlined_ctx_f
                                      (comp_ctx_f x
                                                  (Efun1_c
                                                     (fundefs_append x1 (Fcons (apply_r sig v) f l0 e x2)) x0))
                                      inl) |[ Eapp (apply_r sig v) f (apply_r_list sig l) ]| ) in
      c_count ce  count ->
      closed_exp ce ->
      unique_bindings ce ->
      get_b (apply_r sig v) inl = false ->
      sig_inv_full sig (rename_all_ctx_ns sig
                                          (inlined_ctx_f
                                             (comp_ctx_f x
                                                         (Efun1_c
                                                            (fundefs_append x1 (Fcons (apply_r sig v) f l0 e x2)) x0)) inl))  (rename_all_ns sig (Eapp v f l)) ->
      num_occur ce (apply_r sig v) 1 ->
      List.length l0 = List.length l ->
      c_count
        (rename_all_ctx_ns sig
                           (inlined_ctx_f (comp_ctx_f x (Efun1_c (fundefs_append x1 x2) x0)) inl)
        |[ rename_all_ns (set_list (combine l0 (apply_r_list sig l)) sig) e ]|)
        (update_count_inlined (apply_r_list sig l) l0
                              (M.set (apply_r sig v) 0 count)).
  Proof.
    intros.
    rename H4 into Hsv1.
    rename H5 into Hl0l.
    intro.
    assert (Hc_v0 := H v0).
    apply num_occur_app_ctx in Hc_v0. destructAll.


    assert (Disjoint _ [set apply_r sig v] (FromList l0)).
    { (* by unique bindings *)
      split; intros; intro. inv H7.
      inv H8.
      apply ub_app_ctx_f in H1; destructAll.
      repeat normalize_ctx.
      apply ub_comp_ctx_f in H1; destructAll.
      inv H10.
      repeat normalize_ctx.
      eapply fundefs_append_unique_bindings_l in H15.
      2: reflexivity.  destructAll.
      simpl in H12.  rewrite H2 in H12.
      inv H12. auto.
    }

    assert (Disjoint _ (FromList  (apply_r_list sig l)) (FromList l0)).
    { (* due to unique_binding and closed *)
      split. intro. intro.
      inv H8.

      assert (occurs_free (rename_all_ns sig (Eapp v f l)) x5) by (constructor; auto).
      assert (~ occurs_free ce x5). intro. apply H0 in H11. inv H11.

      apply (proj1 (occurs_free_app_bound_stem _ _ H8)) in H11.

      unfold ce in H11.
      apply ub_app_ctx_f in H1; destructAll.

      repeat normalize_ctx.
      apply ub_comp_ctx_f in H1; destructAll.
      apply bound_stem_comp_ctx_mut in H11. inv H11.

      inv H15. specialize (H11 x5).
      apply H11. split.
      apply bound_stem_var. auto.

      constructor. repeat normalize_ctx.
      eapply fundefs_append_bound_vars. reflexivity.
      right. simpl. rewrite H2. constructor. auto.

      simpl in H16. inv H16.
      inv H14. repeat normalize_ctx.
      eapply fundefs_append_unique_bindings_l in H18.
      2: reflexivity. destructAll.

      eapply fundefs_append_name_in_fundefs in H19. 2: reflexivity.
      inv H19.

      inv H16.
      specialize (H19 x5). apply H19. split.
      apply name_in_fundefs_bound_var_fundefs. auto.
      simpl. rewrite H2. simpl. constructor. auto.

      simpl in H18. rewrite H2 in H18.
      simpl in H14. rewrite H2 in H14. inv H14.
      simpl in H18. inv H18.
      inv H14; auto.
      inv H28. specialize (H18 x5).
      apply H18.
      split; auto.
      apply name_in_fundefs_bound_var_fundefs. auto.
      simpl in H14. inv H14. inv H20.
      specialize (H11 x5). apply H11. split; auto.
      apply bound_stem_var; auto.
      apply bound_var_rename_all_ns_fundefs.
      repeat normalize_ctx.
      eapply fundefs_append_bound_vars.
      reflexivity. right.
      simpl. rewrite H2. constructor. auto.
    }
    assert (Disjoint _ (bound_var_ctx (rename_all_ctx_ns sig
                                                         (inlined_ctx_f (comp_ctx_f x (Efun1_c (fundefs_append x1 x2) x0)) inl))) (FromList l0)).
    {
      split; intro.
      intro.  inv H9.
      unfold ce in H1.
      repeat normalize_ctx.
      apply ub_app_ctx_f in H1; destructAll.
      apply ub_comp_ctx_f in H1. destructAll.
      apply bound_var_ctx_comp_ctx in H10. inv H10.
      inv H14. specialize (H10 x5). apply H10. split; auto.
      simpl. constructor. repeat normalize_ctx.
      eapply fundefs_append_bound_vars. reflexivity.
      right. simpl. rewrite H2. constructor. auto.
      simpl in H15. inv H15.
      repeat normalize_ctx.
      eapply fundefs_append_bound_vars in H18. 2: reflexivity.
      simpl in H13. inv H13.
      repeat normalize_ctx.
      eapply fundefs_append_unique_bindings_l in H17. 2: reflexivity.
      destructAll.
      inv H18.
      inv H15. specialize (H18 x5).
      apply H18. split; auto. simpl. rewrite H2.
      constructor; auto.
      simpl in H13. rewrite H2 in H13. inv H13.
      inv H27. specialize (H13 x5). apply H13. split; auto.
      simpl in H13. inv H13. inv H19. specialize (H10 x5).
      apply H10. split; auto.
      repeat normalize_ctx.
      eapply fundefs_append_bound_vars. reflexivity. right. simpl. rewrite H2.
      constructor; auto.
    }
    assert (Included _ (FromList l0)
                     ( dead_var (rename_all_ctx_ns sig
                                                   (inlined_ctx_f
                                                      (comp_ctx_f x
                                                                  (Efun1_c
                                                                     (fundefs_append x1 x2) x0))
                                                      inl) |[ Eapp (apply_r sig v) f (apply_r_list sig l) ]| ))).
    { intro. intro. apply num_occur_app_ctx.
      unfold ce in *. repeat normalize_ctx.
      assert (Hx5_c: ~ bound_var_ctx (rename_all_ctx_ns sig (inlined_ctx_f x inl)) x5).
      intro. inv H9.
      specialize (H12 x5). apply H12.
      split; auto. apply bound_var_ctx_comp_ctx. auto.

      exists 0, 0. split; auto.
      - apply num_occur_ec_comp_ctx.
        exists 0, 0. split; auto.
        + apply not_bound_dead_or_free_ctx in Hx5_c. inv Hx5_c. auto.
          rewrite <- app_ctx_f_fuse in H0.
          apply closed_app_ctx in H0.
          apply H0 in H11. inv H11.
        + split; auto.
          assert (~ occurs_free (rename_all_ctx_ns sig
                                                   (inlined_ctx_f
                                                      (Efun1_c
                                                         (fundefs_append x1 (Fcons (apply_r sig v) f l0 e x2)) x0)
                                                      inl) |[ Eapp (apply_r sig v) f (apply_r_list sig l) ]|) x5).
          eapply not_occurs_free_ctx_not_bound.
          intro.
          rewrite <- app_ctx_f_fuse in H0. apply H0 in H11. inv H11.
          auto.

          apply not_occur_free_Efun in H11. inv H11.
          rewrite inlined_fundefs_append in H12.
          rewrite rename_all_ns_fundefs_append in H12.
          apply not_occurs_free_fundefs_append in H12.
          inv H12.
          rewrite inlined_fundefs_append in *.
          rewrite rename_all_ns_fundefs_append in *.
          assert (Hname_x5:
                    ~
                      In var
                      (name_in_fundefs
                         (fundefs_append (rename_all_fun_ns sig (inlined_fundefs_f x1 inl))
                                         (rename_all_fun_ns sig
                                                            (inlined_fundefs_f (Fcons (apply_r sig v) f l0 e x2) inl)))) x5).
          {
            intro.
            eapply fundefs_append_name_in_fundefs in H12. 2: reflexivity.
            inv H9. specialize (H15 x5).
            apply H15. split. apply bound_var_ctx_comp_ctx.
            right. constructor.
            repeat normalize_ctx.
            eapply fundefs_append_bound_vars. reflexivity.
            inv H12. left.
            apply name_in_fundefs_bound_var_fundefs. auto.
            simpl in H9. rewrite H2 in H9. simpl in H9. inv H9.
            exfalso. inv H7. specialize (H9 x5). apply H9. split; auto.
            right. apply name_in_fundefs_bound_var_fundefs; auto.
            auto.
          }
          assert (H11' :
                    In var
                       (Complement var (occurs_free_fundefs
                                          (rename_all_fun_ns sig (inlined_fundefs_f x1 inl)))) x5).
          intro. apply H11. split; auto.
          clear H11.

          assert (H13' :
                    In var
                       (Complement var
                                   (occurs_free
                                      (rename_all_ctx_ns sig (inlined_ctx_f x0 inl)
                                      |[ Eapp (apply_r sig v) f (apply_r_list sig l) ]|))) x5).
          intro. apply H13. split; auto.  clear H13.
          assert (H14' :
                    In var
                       (Complement var
                                   (occurs_free_fundefs
                                      (rename_all_fun_ns sig
                                                         (inlined_fundefs_f (Fcons (apply_r sig v) f l0 e x2)
                                                                            inl)))) x5).
          intro. apply H14. split; auto.  clear H14.

          eapply Complement_Proper in H14'.
          2:{ simpl. rewrite H2.
              simpl. symmetry. apply occurs_free_fundefs_Fcons. }
          assert (H14'' : In var (Complement var
                                             (occurs_free_fundefs
                                                (rename_all_fun_ns sig (inlined_fundefs_f x2 inl)))) x5).
          intro. apply H14'. right. split; auto.
          intro. inv H7. specialize (H13 x5). apply H13; auto.
          clear H14'.
          apply not_free_dead_or_bound in H13'. inv H13'.
          2:{ exfalso. inv H9. specialize (H12 x5). apply H12. split; auto.
            apply bound_var_ctx_comp_ctx. right. simpl. apply identifiers.Bound_Fun12_c.
            apply bound_var_app_ctx in H11. inv H11; auto. inv H9. }

          apply not_free_bound_or_not_occur in H11'. inv H11'.
          2:{ exfalso. inv H9. specialize (H13 x5). apply H13. split; auto.
            apply bound_var_ctx_comp_ctx.
            right. constructor. rewrite inlined_fundefs_append.
            normalize_ctx.
            eapply fundefs_append_bound_vars.
            reflexivity. left; auto. }

          apply not_free_bound_or_not_occur in H14''. inv H14''.
          2:{ exfalso. inv H9.  specialize (H14 x5). apply H14. split; auto. apply bound_var_ctx_comp_ctx.
              right. constructor. rewrite inlined_fundefs_append.
              normalize_ctx.
              eapply fundefs_append_bound_vars.
              reflexivity. auto. }
          simpl.
          eapply num_occur_ec_n. constructor.
          apply num_occur_app_ctx in H11; destructAll; pi0. eauto.
          repeat normalize_ctx.
          eapply fundefs_append_num_occur.
          reflexivity. eauto. eauto.
          auto.
      - split. eapply num_occur_n.
        constructor.
        assert (num_occur_list (apply_r_list sig l) x5 = 0).
        apply not_occur_list_not_in. intro. inv H8.
        specialize (H12 x5). apply H12; auto.
        assert (num_occur_list [apply_r sig v] x5 = 0).
        apply not_occur_list_not_in. intro. inv H7.
        specialize (H13 x5). apply H13. split; auto.
        inv H12. constructor. inv H7.
        simpl in *. rewrite H11. lia.
        auto.
    }
    assert (forall vx n m, FromList l0 vx ->
                           num_occur ce vx n ->
                           num_occur (rename_all_ns sig e) vx m ->
                           n = m).
    {
      intros.
      apply num_occur_app_ctx in H12. destructAll.
      apply H10 in H11. apply num_occur_app_ctx in H11. destructAll; pi0.
      assert (x6 = 0). eapply (proj1 (num_occur_det _)); eauto. subst.

      repeat normalize_ctx.
      apply num_occur_ec_comp_ctx in H11; destructAll; pi0.
      apply num_occur_ec_comp_ctx in H12. destructAll.
      assert (x6 = 0). eapply num_occur_ec_det; eauto.
      subst.
      simpl in *. inv H16; pi0.
      inv H17. assert (n = 0). eapply num_occur_ec_det; eauto.
      subst.
      repeat normalize_ctx.
      apply fundefs_append_num_occur' in H24. destructAll.
      apply fundefs_append_num_occur' in H23; destructAll; pi0.
      assert (x5 = 0). eapply (proj2 (num_occur_det _)); eauto. subst.
      simpl in H17. rewrite H2 in H17. inv H17.
      assert (m0 = 0). eapply (proj2 (num_occur_det _)); eauto. subst.
      simpl. do 2 (rewrite Nat.add_0_r).
      eapply (proj1 (num_occur_det _)); eauto.
    }
    assert (Hl0 := Decidable_FromList l0). destruct Hl0.
    specialize (Dec v0) as [H12 | H12].

    (* x5 is in l0 *)
    apply num_occur_app_ctx. exists 0, 0. split.
    apply H10 in H12. apply num_occur_app_ctx in H12; destructAll; pi0.
    auto.
    split.
    { assert  (Hl0 := Decidable_Range_map sig).
      inv Hl0. destruct (Dec v0) as [H13 | H13].
      - inv H13. apply H3 in H14. destructAll.
        inv H14.
        + apply dead_occur_rename_all_ns_set_list.
          inv H8. intro. specialize (H14 v0).
          apply H14; auto.
          apply num_occur_app_ctx in H15. destructAll; pi0.
          repeat normalize_ctx.
          apply num_occur_ec_comp_ctx in H14.
          destructAll; pi0.
          inv H16; pi0.
          repeat normalize_ctx.
          apply fundefs_append_num_occur' in H22.
          destructAll; pi0.
          simpl in H17. rewrite H2 in H17. inv H17; pi0. auto.
        + exfalso. inv H9. specialize (H14 v0). apply H14. repeat normalize_ctx. split; auto.
          apply bound_var_ctx_comp_ctx.
          apply bound_stem_comp_ctx_mut in H15. destruct H15. left.
          apply bound_stem_var; auto.
          simpl in H9. right. inv H9.
          constructor.
          repeat normalize_ctx.
          eapply fundefs_append_bound_vars. reflexivity.
          eapply fundefs_append_name_in_fundefs in H18. 2: reflexivity.
          inv H18. left. apply name_in_fundefs_bound_var_fundefs. auto.
          simpl in H9. rewrite H2 in H9. inv H9. exfalso. inv H7. specialize (H9 x6).
          apply H9; auto.
          right. apply name_in_fundefs_bound_var_fundefs. auto.
          apply bound_var_Fun1_c. right. apply bound_stem_var. auto.
      - apply num_occur_rename_all_ns_kill.
        intro. apply range_map_set_list in H14. inv H14. auto.
        inv H8. specialize (H14 v0). apply H14; auto.
        apply Dom_map_set_list.
        rewrite length_apply_r_list. auto.  auto.
    }
    rewrite update_count_inlined_dom. auto.
    rewrite length_apply_r_list. auto.
    auto. auto.

    assert (exists n, sum_range_n l0 (apply_r_list sig l) (rename_all_ns sig e) v0 n).
    apply e_sum_range_n. rewrite length_apply_r_list. auto.
    destruct H13.
    assert (Hn_v0 := H v0).
    apply num_occur_app_ctx in Hn_v0; destructAll. repeat normalize_ctx.
    apply num_occur_ec_comp_ctx in H14. destructAll. repeat normalize_ctx.
    simpl in H17. inv H17. repeat normalize_ctx.
    apply fundefs_append_num_occur' in H23. destructAll. simpl in H18. rewrite H2 in H18. inv H18.
    inv H15. simpl in H16.

    assert (Hnd_l0 : NoDup l0). apply ub_app_ctx_f in H1; destructAll; repeat normalize_ctx.
    apply ub_comp_ctx_f in H1; destructAll; repeat normalize_ctx. inv H19.
    repeat normalize_ctx. eapply fundefs_append_unique_bindings_l in H25. 2: reflexivity.
    destructAll. simpl in H22; rewrite H2 in H22. inv H22. auto.


    apply num_occur_app_ctx.  eexists. eexists.
    split. apply num_occur_ec_comp_ctx. eexists. eexists. split; eauto.
    split. simpl. constructor. eauto. repeat normalize_ctx.
    eapply fundefs_append_num_occur. reflexivity. eauto. eauto. reflexivity.
    split.
    apply num_occur_set_list_r.
    split; intro. intro. destruct H15.
    inv H15. apply H3 in H19.  destructAll. apply H15.
    apply bound_var_app_ctx. left. apply bound_var_ctx_comp_ctx. right. constructor.
    repeat normalize_ctx.  eapply fundefs_append_bound_vars. reflexivity. right. simpl. rewrite H2.
    constructor. auto.
    auto with Ensembles_DB. auto.
    {
      intro. intro. assert (Hsr := Decidable_Range_map sig). inv Hsr. specialize (Dec x7).
      destruct Dec as [H18 | H18]; auto.
      right. inv H18. apply H3 in H19. destructAll. inv H19.
      apply num_occur_app_ctx in H21; destructAll; pi0.
      apply num_occur_ec_comp_ctx in H19; destructAll; pi0.
      simpl in H22. inv H22; pi0. repeat normalize_ctx.
      eapply fundefs_append_num_occur' in H30.  destructAll; pi0.
      simpl in H23. rewrite H2 in H23. inv H23; pi0. auto.
      exfalso.
      inv H9. specialize (H19 x7). apply H19.
      split; auto. apply bound_stem_comp_ctx_mut in H21.
      apply bound_var_ctx_comp_ctx.
      inv H21. left. apply bound_stem_var; auto.
      right. simpl in *.  inv H9.
      constructor.
      repeat normalize_ctx. eapply fundefs_append_name_in_fundefs in H24. 2: reflexivity.
      apply name_in_fundefs_bound_var_fundefs. eapply fundefs_append_name_in_fundefs. reflexivity.
      inv H24; auto. simpl in H9. rewrite H2 in H9. simpl in H9. inv H9.
      exfalso. inv H7. specialize (H9 x7). apply H9; auto.
      auto.
      apply bound_stem_var in H24. auto.
    }
    apply H13. apply H27. auto.
    erewrite update_count_sum_range; eauto.

    destruct (term_util.var_dec v0 (apply_r sig v)).
    (* apply_r sig v *) subst. rewrite gdss.
    specialize (H (apply_r sig v)). assert ( (get_c (apply_r sig v) count) = 1).
    eapply (proj1 (num_occur_det _)); eauto. rewrite H16 in H15. clear H16.
    assert (x8 + (n + (x6 + (n0 + m)))  = 0) by lia. pi0.
    assert (num_occur_list (apply_r_list sig l) (apply_r sig v) = 0) by lia. rewrite H16. lia.

    rewrite gdso by auto. unfold maps_util.getd.  unfold get_c in H16. rewrite H16.
    lia.

    destruct (term_util.var_dec v0 (apply_r sig v)).
    subst. rewrite gdss.
    specialize (H (apply_r sig v)). assert ( (get_c (apply_r sig v) count) = 1).
    eapply (proj1 (num_occur_det _)); eauto.
    rewrite H15 in H. apply num_occur_app_ctx in H; destructAll. inv H18.
    simpl in H19. destruct  (term_util.var_dec (apply_r sig v) (apply_r sig v)). lia.
    exfalso; auto.
    rewrite gdso by auto. unfold get_c in H16; unfold maps_util.getd. lia.

    intros. rewrite gdso. specialize (H x7). specialize (H11 _ _ _ H15 H H18). auto.
    intro. inv H7. specialize (H21 (apply_r sig v)). apply H21. split; auto.
  Qed.


  (** postcontractfun reduces or preserves the names of functions *)
  Theorem postcontractfun_name_in_fundefs:
    forall {fds_c steps im sub count sig},
    forall {oes fds_c' steps' count' im' pfe pfsub bp},
      postcontractfun oes (fun rm cm es H => contract rm cm (fst (fst es)) (snd (fst es)) (snd es)) sig count im sub fds_c pfe steps pfsub =
      existT _ (fds_c', steps', count', im')  bp ->
      name_in_fundefs fds_c' \subset name_in_fundefs fds_c.
  Proof.
    induction fds_c; intros.
    - simpl in H.
      destruct (get_b v im).
      + apply IHfds_c in H.
        simpl. auto with Ensembles_DB.
      + destruct (get_c v count).
        apply IHfds_c in H.
        simpl. now sets.
        destruct (contract sig count e sub im).
        destruct x. destruct p. destruct p.
        remember  (postcontractfun oes
                                   (fun (rm : r_map) (cm : c_map)
                                        (es : prod (prod exp ctx_map) b_map)
                                        (_ : lt (term_sub_inl_size es) (term_sub_inl_size oes)) =>
                                      contract rm cm
                                               (@fst exp ctx_map (@fst (prod exp ctx_map) b_map es))
                                               (@snd exp ctx_map (@fst (prod exp ctx_map) b_map es))
                                               (@snd (prod exp ctx_map) b_map es)) sig c b0 sub fds_c
                                   (@subfds_Fcons v f l e fds_c
                                                  (@fst exp ctx_map (@fst (prod exp ctx_map) b_map oes))
                                                  (@eq_ind_r fundefs (Fcons v f l e fds_c)
                                                             (fun x : fundefs =>
                                                                subfds_e x
                                                                         (@fst exp ctx_map (@fst (prod exp ctx_map) b_map oes)))
                                                             pfe (Fcons v f l e fds_c)
                                                             (@eq_refl fundefs (Fcons v f l e fds_c)))) steps
                                   (@tsis_sub_pcf' sub im
                                                   (@snd exp ctx_map (@fst (prod exp ctx_map) b_map oes))
                                                   (@snd (prod exp ctx_map) b_map oes) b0 pfsub b)).
        destruct s. destruct x. destruct p. destruct p. symmetry  in Heqs.
        apply IHfds_c in Heqs.
        inv H. simpl. auto with Ensembles_DB.
    - simpl in H. inv H. auto with Ensembles_DB.
  Qed.

  Theorem postcontractfun_steps_ge fds_c steps im sub count sig oes fds_c' steps' count' im' pfe pfsub bp :
    postcontractfun oes (fun rm cm es H => contract rm cm (fst (fst es)) (snd (fst es)) (snd es)) sig count im sub fds_c pfe steps pfsub =
    existT _ (fds_c', steps', count', im')  bp ->
    steps' >= steps.
  Proof.
    revert steps im sub count sig oes fds_c' steps' count' im' pfe pfsub bp.
    induction fds_c; intros steps im sub count sig oes fds_c' steps' count' im' pfe pfsub bp Hc.
    - simpl in Hc.
      destruct (get_b v im).
      + apply IHfds_c in Hc. eassumption.
      + destruct (get_c v count).
        * apply IHfds_c in Hc. eassumption.
        * destruct (contract sig count e sub im) as [[[[? ?] ?] ?] ?].
          remember (postcontractfun oes
                                    (fun (rm : r_map) (cm : c_map) (es : exp * ctx_map * b_map)
                                         (_ : term_sub_inl_size es < term_sub_inl_size oes) =>
                                       contract rm cm
                                                (@fst exp ctx_map (@fst (exp * ctx_map) b_map es))
                                                (@snd exp ctx_map (@fst (exp * ctx_map) b_map es))
                                                (@snd (exp * ctx_map) b_map es)) sig c b sub fds_c
                                    (@subfds_Fcons v f l e fds_c
                                                   (@fst exp ctx_map (@fst (exp * ctx_map) b_map oes))
                                                   (@eq_ind_r fundefs (Fcons v f l e fds_c)
                                                              (fun x : fundefs =>
                                                                 subfds_e x
                                                                          (@fst exp ctx_map (@fst (exp * ctx_map) b_map oes)))
                                                              pfe (Fcons v f l e fds_c)
                                                              (@eq_refl fundefs (Fcons v f l e fds_c)))) steps
                                    (@tsis_sub_pcf' sub im
                                                    (@snd exp ctx_map (@fst (exp * ctx_map) b_map oes))
                                                    (@snd (exp * ctx_map) b_map oes) b pfsub b0)) as s.
          destruct s as [[[[? ?] ?] ?] ?]. simpl in *. inv Hc. symmetry in Heqs. eapply IHfds_c in Heqs. lia.
    - simpl in Hc. inv Hc. lia.
  Qed.


(** postcontractfun removes dead functions and processed the terms according to the shrink rewrite system. Also, none of the functions in fds and fds_c are ever eligible to be inlined *)
  Theorem postcontractfun_corresp:
    forall fds_c steps fds e c im sub count sig,
      (* recursive call to shrink_corresp *)
      (forall eb sub' im' sig c count,
         (term_sub_inl_size (eb, sub', im') < funs_size fds_c + sub_inl_size sub im) ->
         let ce := (app_ctx_f (rename_all_ctx_ns sig (inlined_ctx_f c im')) (rename_all_ns sig eb)) in
         unique_bindings ce ->
         closed_exp ce ->
         c_count ce count ->
         cmap_view_ctx sub' c ->
         inl_inv im' sub' ce ->
         sig_inv_full sig (rename_all_ctx_ns sig (inlined_ctx_f c im')) (rename_all_ns sig eb) ->
         forall e' steps count' im'' BP,
           contract sig count eb sub' im' = existT _ (e', steps, count', im'') BP ->
           let ce' := (app_ctx_f (rename_all_ctx_ns sig (inlined_ctx_f c im'')) e') in
           gsr_clos steps ce ce' /\ c_count ce' count' /\ inl_inv im'' sub' ce' /\
           sig_inv_codom sig (rename_all_ctx_ns sig (inlined_ctx_f c im'')) e') ->
      (* actual statement for postcontractfun *)
      let ce := (app_ctx_f (rename_all_ctx_ns sig (inlined_ctx_f (comp_ctx_f c (Efun1_c (fundefs_append fds fds_c) Hole_c)) im)) (rename_all_ns sig e)) in
      (Disjoint _ (name_in_fundefs fds) (Dom_map_b im)) ->
      unique_bindings ce ->
      closed_exp ce ->
      c_count ce count ->
      cmap_view_ctx sub c ->
      inl_inv im sub ce ->
      sig_inv_full sig (rename_all_ctx_ns sig (inlined_ctx_f (comp_ctx_f c (Efun1_c (fundefs_append fds fds_c) Hole_c)) im)) (rename_all_ns sig e) ->
      forall oes fds_c' steps' count' im' pfe pfsub bp,
        postcontractfun oes (fun rm cm es H => contract rm cm (fst (fst es)) (snd (fst es)) (snd es)) sig count im sub fds_c pfe steps pfsub =
        existT _ (fds_c', steps', count', im')  bp ->
        let ce' := (app_ctx_f (rename_all_ctx_ns sig (inlined_ctx_f (comp_ctx_f c (Efun1_c (fundefs_append fds fds_c') Hole_c)) im')) (rename_all_ns sig e)) in
        gsr_clos (steps' - steps) ce ce' /\ c_count ce' count' /\ inl_inv im' sub ce' /\
        sig_inv_codom sig (rename_all_ctx_ns sig (inlined_ctx_f (comp_ctx_f c (Efun1_c (fundefs_append fds fds_c') Hole_c)) im')) (rename_all_ns sig e) /\ (rename_all_fun_ns sig (inlined_fundefs_f fds_c' im') = fds_c') /\ (Disjoint _ (name_in_fundefs fds) (Dom_map_b im')).
  Proof.
    induction fds_c;
      intros steps fds e0 c im sub count sig Hcontract_corresp ce Hdjfds; intros.
    (* Fnil *)
    2:{ simpl in H5. inv H5. unfold ce in *; unfold ce'.
        split; auto. rewrite Nat.sub_diag. eapply Refl_srw.
        split; auto. split; auto.
        apply sig_inv_combine in H4. destruct H4. auto. }
    { (* Fcons *)
      simpl in H5.
      destruct (get_b v im) eqn:gbvim.
      - (* get_b v im = true *)
        assert (
            (inlined_ctx_f (comp_ctx_f c (Efun1_c (fundefs_append fds (Fcons v f l e fds_c)) Hole_c)) im) =
            (inlined_ctx_f (comp_ctx_f c (Efun1_c (fundefs_append fds fds_c) Hole_c)) im)).
        { do 2 (rewrite (proj1 inlined_comp_ctx)). simpl.
          do 2 (rewrite inlined_fundefs_append). simpl.
          rewrite gbvim. reflexivity. }
        unfold ce in *. rewrite H6 in *.
        eapply IHfds_c in H5; eauto. intros. eapply Hcontract_corresp; eauto.
        etransitivity. apply H7. simpl. lia.
    - (* get_b v im = false *)
      destruct (get_c v count) eqn:gvc.
      + (* get_c v count = 0 i.e. dead fun *)
        assert (Hgsr_dead: gsr_clos 0 ce (rename_all_ctx_ns sig (inlined_ctx_f (comp_ctx_f c (Efun1_c (fundefs_append fds fds_c) Hole_c)) im) |[ rename_all_ns sig e0 ]|)).
        { (* by Fun_rem_s *)
          unfold ce. do 2 (rewrite (proj1 inlined_comp_ctx)). simpl.
          do 2 (rewrite inlined_fundefs_append). simpl. rewrite gbvim.
          do 2 (rewrite (proj1 (rename_all_ctx_ns_comp_ctx _ _))). do 2 (rewrite <- app_ctx_f_fuse).
          replace 0 with (0 + 0) by lia. eapply Trans_srw; [| now constructor ].
          constructor. simpl. do 2 (rewrite rename_all_ns_fundefs_append). simpl.
          apply Fun_rem_s. specialize (H1 v). rewrite gvc in H1.
          unfold ce in H1.
          rewrite (proj1 inlined_comp_ctx) in H1.
          simpl in H1.
          rewrite (inlined_fundefs_append) in H1.
          rewrite (proj1 (rename_all_ctx_ns_comp_ctx _ _)) in H1.
          rewrite <- app_ctx_f_fuse in H1.
          apply num_occur_app_ctx in H1.
          destructAll; pi0.
          simpl in H6.
          rewrite rename_all_ns_fundefs_append in H6.
          rewrite gbvim in H6.
          simpl in H6.
          auto.
        }
        assert (Ht := gsr_clos_preserves_clos _ _ _ H H0 Hgsr_dead).
        destruct Ht as (Hub_dead, Hdj_dead).
        apply sig_inv_combine in H4. destruct H4 as (H4, H4c).
        assert (Hsig_dead := gsr_preserves_sig_dom _ _ _ _ H (closed_implies_Disjoint _ H0) Hgsr_dead H4).

        (* I.H. *)
        eapply IHfds_c in H5; eauto.
        * destructAll.
          unfold ce'; split; auto.
          replace (steps' - steps) with (0 + (steps' - steps)) by lia.
          eapply gsr_clos_trans. eassumption. eassumption.
        * intros.
          eapply Hcontract_corresp; eauto.
          etransitivity. apply H6. simpl.
          lia.
        * intro.
          specialize (H1 v0).
          unfold ce in H1.
          repeat normalize_ctx.
          apply num_occur_app_ctx in H1.
          destructAll.
          apply num_occur_ec_comp_ctx in H1.
          destructAll.
          simpl in H8.
          repeat normalize_ctx.
          inv H8.
          rewrite gbvim in H14.
          apply fundefs_append_num_occur' in H14. destructAll.
          simpl in H9. inv H9.
          eapply num_occur_n.
          apply num_occur_app_ctx. eexists; eexists.
          split.
          apply num_occur_ec_comp_ctx.
          eexists; eexists.
          split; eauto.
          simpl.
          repeat normalize_ctx.
          split. constructor; eauto.
          eapply fundefs_append_num_occur.  reflexivity.
          eauto. eauto.
          reflexivity.
          split; eauto.
          unfold dec_census.

          rewrite <- ((proj1 combine_minus_census_correct) _ _ _).
          rewrite gccombine_sub. rewrite H7.
          assert (get_c v0 (init_census (rename_all_ns sig e)) = n0).
          eapply (proj1 (num_occur_det _)).
          apply init_census_correct. auto.
          rewrite H9. lia.
        * intro. intro.
          apply H3 in H6.
          unfold ce in H6.
          destruct H6.
          split.
          {
            intro.
            apply H6.
            apply bound_var_app_ctx in H8.
            apply bound_var_app_ctx.
            inv H8.
            left.
            repeat (normalize_ctx; simpl).
            rewrite gbvim.
            simpl.
            rewrite (proj1 (bound_var_ctx_comp_ctx)).
            rewrite (proj1 (bound_var_ctx_comp_ctx)) in H9.
            inv H9; auto.
            right.
            normalize_bound_var_ctx'.
            simpl in H8.
            repeat (normalize_ctx; simpl).
            rewrite fundefs_append_bound_vars.
            2: reflexivity.
            normalize_bound_var.
            normalize_bound_var_ctx_in_ctx.
            rewrite fundefs_append_bound_vars in H8.
            2: reflexivity.
            destruct H8.
            left.
            destruct H8; auto.
            auto.
            right. auto.
          }
          {
            intros.
            apply H7 in H8.
            eapply Disjoint_Included_l.
            2: apply H8.
            repeat (normalize_ctx; simpl).
            do 2 (rewrite bound_var_app_ctx).
            do 2 (rewrite (proj1 bound_var_ctx_comp_ctx)).
            repeat normalize_bound_var_ctx'.
            rewrite fundefs_append_bound_vars.
            2: reflexivity.
            intro. intros.
            rewrite fundefs_append_bound_vars.
            2: reflexivity.
            rewrite gbvim.
            simpl.
            repeat normalize_bound_var.
            destruct H9; auto.
            destruct H9; auto.
            destruct H9; auto.
            destruct H9; auto.
            eauto 25 with Ensembles_DB.
          }
        * apply sig_inv_combine. split; auto.
          intro. intros.
          apply H4c in H6.
          inv H6.
          left.
          apply num_occur_app_ctx in H7. destructAll; pi0.
          repeat normalize_ctx.
          apply num_occur_ec_comp_ctx in H6.
          destructAll; pi0.
          simpl in H8. inv H8; pi0.
          rewrite inlined_fundefs_append in H14.
          rewrite rename_all_ns_fundefs_append in H14.
          apply fundefs_append_num_occur' in H14.
          destructAll; pi0.
          simpl in H9. rewrite gbvim in H9. simpl in H9. inv H9; pi0.
          simpl.
          apply num_occur_app_ctx. exists 0, 0.
          split; auto. apply num_occur_ec_comp_ctx. exists 0, 0.
          split; auto. split; auto.
          eapply num_occur_ec_n.
          constructor. constructor.
          rewrite inlined_fundefs_append.
          rewrite rename_all_ns_fundefs_append.
          eapply fundefs_append_num_occur.
          reflexivity.
          eauto. eauto. auto.
          (* either  y = v and y is dead in ce OR y <> v and y is bound stem *)
          repeat normalize_ctx.
          apply bound_stem_comp_ctx_mut in H7.
          inv H7.
          right.
          apply bound_stem_comp_ctx_mut. left; auto.
          simpl in H6. inv H6.
          rewrite inlined_fundefs_append in H10.
          rewrite rename_all_ns_fundefs_append in H10. simpl in H10.
          rewrite gbvim in H10.
          eapply fundefs_append_name_in_fundefs in H10.
          2: reflexivity.
          inv H10.
          (* fds *)
          right. apply bound_stem_comp_ctx_mut.
          right. simpl. constructor.
          repeat normalize_ctx.
          eapply fundefs_append_name_in_fundefs. reflexivity. auto.
          simpl in H6. inv H6.
          (* v case, dead *)
          inv H7.
          left.
          specialize (H1 y).
          rewrite gvc in H1.
          apply num_occur_app_ctx in H1. destructAll; pi0.
          repeat normalize_ctx.
          apply num_occur_ec_comp_ctx_mut in H1.
          destructAll; pi0.
          simpl in H7. inv H7; pi0.
          repeat normalize_ctx.
          apply fundefs_append_num_occur' in H13.
          destructAll; pi0.
          simpl in H8. rewrite gbvim in H8.
          simpl in H8. inv H8; pi0. simpl.
          apply num_occur_app_ctx. exists 0, 0. split; auto.
          apply num_occur_ec_comp_ctx_mut. exists 0, 0. split; auto.
          split; auto.
          eapply num_occur_ec_n. constructor; auto. constructor.
          repeat normalize_ctx. eapply fundefs_append_num_occur.
          reflexivity. eauto. eauto. auto.
          (* fds_c *)
          right. simpl.  apply bound_stem_comp_ctx_mut.
          right. simpl. constructor.
          repeat normalize_ctx.
          eapply fundefs_append_name_in_fundefs. reflexivity. auto.
          inv H10.
      + (* get_c v count = (S n) *)
        (* contract on e *)
        remember (contract sig count e sub im) as s.
        destruct s. destruct x. destruct p. destruct p.
        symmetry in Heqs.
        assert (
            rename_all_ctx_ns sig
                              (inlined_ctx_f
                                 (comp_ctx_f c
                                             (Efun1_c (fundefs_append fds (Fcons v f l e fds_c)) Hole_c))
                                 im) |[ rename_all_ns sig e0 ]| =
                                                                (rename_all_ctx_ns sig (inlined_ctx_f (comp_ctx_f c (
                                                                                                                    Efun2_c  (fundefs_ctx_append (inlined_fundefs_f fds im) (Fcons1_c v f l Hole_c (inlined_fundefs_f fds_c im))) e0)) im) |[ rename_all_ns sig e ]|)).
        {
          do 2 (rewrite <- (proj1 (rename_all_ns_app_ctx _ _))).
          repeat normalize_ctx.
          simpl.
          do 2 (rewrite <- app_ctx_f_fuse).
          simpl.
          repeat normalize_ctx.
          simpl.
          rewrite gbvim.
          simpl.
          rewrite inlined_fundefs_ctx_append1.
          rewrite rename_all_fundefs_ctx_append.
          rewrite app_f_ctx_fundefs_ctx_append.
          simpl.
          reflexivity.
        }
        unfold ce in *; rewrite H6 in *.

        eapply Hcontract_corresp with (c :=
                                         (comp_ctx_f c
                                                     (Efun2_c
                                                        (fundefs_ctx_append (inlined_fundefs_f fds im)
                                                                            (Fcons1_c v f l Hole_c (inlined_fundefs_f fds_c im))) e0))) in Heqs; eauto.
        2:{ unfold term_sub_inl_size; simpl. lia. }
        2: (apply cmap_view_efun2; auto).


        (* I H *)
        destruct Heqs.
        destruct H8.
        assert (Ht := gsr_clos_preserves_clos _ _ _ H H0 H7).
        destruct Ht as (Hub_post, Hdj_post).
        apply sig_inv_combine in H4.
        destruct H4 as (H4, H4c).
        rewrite H6 in H4.
        assert (Hsig_post := gsr_preserves_sig_dom _ _ _ _ H (closed_implies_Disjoint _ H0) H7 H4).

        destruct H9 as (H9, Hsig_r).

        assert (He1 : e1 = rename_all_ns sig e1).
        {
          rewrite <- (proj1 (rename_all_no_shadow _)).
          symmetry.
          apply rename_sig_dead.
          intro.             intros.
          apply Hsig_post in H10.
          apply not_bound_dead_or_free in H10.
          inv H10.
          2: apply Hdj_post in H11; inv H11.

          apply num_occur_app_ctx in H11.
          destructAll; pi0.
          auto.
          eapply sig_inv_dom_mon.
          2: apply Hsig_post.
          rewrite bound_var_app_ctx.
          right;
            auto.
        }


        assert
        ( (rename_all_ctx_ns sig
                             (inlined_ctx_f
                                (comp_ctx_f c
                                            (Efun2_c
                                               (fundefs_ctx_append (inlined_fundefs_f fds im)
                                                                   (Fcons1_c v f l Hole_c (inlined_fundefs_f fds_c im)))
                                               e0)) b0) |[ e1 ]|) =
          (rename_all_ctx_ns sig
                             (inlined_ctx_f
                                (comp_ctx_f c
                                            (Efun1_c
                                               (fundefs_append (fundefs_append fds (Fcons v f l e1 Fnil)) fds_c) Hole_c)) b0) |[ rename_all_ns sig e0 ]|)).
        {
          rewrite He1 at 1.
          clear He1.
          repeat (normalize_ctx; simpl).
          destruct (get_b v b0) eqn:gvb0.
          - (* v wasn't eligible to be inlined *)
            apply H9 in gvb0.
            destructAll.
            exfalso.
            apply H10.
            apply bound_var_app_ctx.
            left.
            normalize_bound_var_ctx.
            right.
            simpl.
            normalize_bound_var_ctx.
            left.
            rewrite <- (proj2 (bound_var_ctx_rename_all_ns _)).
            apply bound_var_fundefs_ctx_append_f.
            apply name_in_fundefs_ctx_append.
            right. simpl. auto.
          - simpl.
            do 2 (rewrite <- app_ctx_f_fuse).
            simpl.
            assert ((inlined_fundefs_ctx_f
                       (fundefs_ctx_append (inlined_fundefs_f fds im)
                                           (Fcons1_c v f l Hole_c (inlined_fundefs_f fds_c im))) b0)  =
                    fundefs_ctx_append (inlined_fundefs_f fds b0)
                                       (Fcons1_c v f l Hole_c (inlined_fundefs_f fds_c b0))).
            {
              rewrite inlined_fundefs_ctx_append_shallow.
              erewrite eq_b_inlined_fundefs.
              erewrite eq_b_inlined_fundefs with (fds := fds_c).
              reflexivity.
              {
                intro.
                intro.
                destruct (get_b x b0) eqn:gxb0.
                destruct (get_b x im) eqn:gxim.
                reflexivity.

                (* prove that this is false *)
                exfalso.
                apply H9 in gxb0.
                destruct gxb0.
                apply H11.
                apply bound_var_app_ctx.
                left.
                apply bound_var_ctx_comp_ctx.
                right.
                simpl.
                rewrite inlined_fundefs_ctx_append_shallow.
                normalize_bound_var_ctx.
                left.
                rewrite <- (proj2 (bound_var_ctx_rename_all_ns  _)).
                rewrite bound_var_fundefs_ctx_append.
                right.
                apply bound_var_Fcons1_c.
                right. right.
                right.
                apply name_in_fundefs_not_inlined'; auto.

                destruct (get_b x im) eqn:gxim.
                assert (H' := b).
                apply b_map_le_c in H'.
                simpl in H'.
                apply H' in gxim.
                rewrite gxim in gxb0.  auto.
                reflexivity.
              }
              {
                intro.
                intro.
                destruct (get_b x b0) eqn:gxb0.
                destruct (get_b x im) eqn:gxim.
                reflexivity.

                (* prove that this is false *)
                exfalso.
                apply H9 in gxb0.
                destruct gxb0.
                apply H11.
                apply bound_var_app_ctx.
                left.
                apply bound_var_ctx_comp_ctx.
                right.
                simpl.
                rewrite inlined_fundefs_ctx_append_shallow.
                normalize_bound_var_ctx.
                left.
                rewrite <- (proj2 (bound_var_ctx_rename_all_ns  _)).
                rewrite bound_var_fundefs_ctx_append.
                left.
                apply name_in_fundefs_not_inlined'; auto.

                destruct (get_b x im) eqn:gxim.
                assert (H' := b).
                apply b_map_le_c in H'.
                simpl in H'.
                apply H' in gxim.
                rewrite gxim in gxb0.  auto.
                reflexivity.
              }
            }
            rewrite H10.
            rewrite rename_all_fundefs_ctx_append.
            simpl.
            rewrite app_f_ctx_fundefs_ctx_append. simpl.
            rewrite <- fundefs_append_assoc.
            simpl. reflexivity.
        }

        rewrite H10 in *.
        remember ( postcontractfun oes
                                   (fun (rm : r_map) (cm : c_map)
                                        (es : prod (prod exp ctx_map) b_map)
                                        (_ : lt (term_sub_inl_size es) (term_sub_inl_size oes)) =>
                                      contract rm cm
                                               (@fst exp ctx_map (@fst (prod exp ctx_map) b_map es))
                                               (@snd exp ctx_map (@fst (prod exp ctx_map) b_map es))
                                               (@snd (prod exp ctx_map) b_map es)) sig c0 b0 sub fds_c
                                   (@subfds_Fcons v f l e fds_c
                                                  (@fst exp ctx_map (@fst (prod exp ctx_map) b_map oes))
                                                  (@eq_ind_r fundefs (Fcons v f l e fds_c)
                                                             (fun x : fundefs =>
                                                                subfds_e x
                                                                         (@fst exp ctx_map (@fst (prod exp ctx_map) b_map oes)))
                                                             pfe (Fcons v f l e fds_c)
                                                             (@eq_refl fundefs (Fcons v f l e fds_c)))) steps
                                   (@tsis_sub_pcf' sub im
                                                   (@snd exp ctx_map (@fst (prod exp ctx_map) b_map oes))
                                                   (@snd (prod exp ctx_map) b_map oes) b0 pfsub b)).
        destruct s. destruct x. destruct p. destruct p.
        symmetry in Heqs. assert (Hge := Heqs). eapply postcontractfun_steps_ge in Hge.
        eapply IHfds_c  in Heqs; eauto.
        clear He1.
        destruct Heqs as (H11, Heqs).
        destruct Heqs as (H12, Heqs).
        destruct Heqs as (H13, Heqs).
        inv H5.
        unfold ce'.
        split; auto.
        * replace (n0 + n1 - steps) with (n0 + (n1 - steps)) by lia. eapply gsr_clos_trans. eassumption.
          replace (fundefs_append fds (Fcons v f l e1 f0)) with (fundefs_append (fundefs_append fds (Fcons v f l e1 Fnil)) f0).
          2:{ rewrite <- fundefs_append_assoc. simpl. reflexivity. }
          eassumption.
        * split; auto.
          -- rewrite <- fundefs_append_assoc in H12.
             auto.
          -- rewrite <- fundefs_append_assoc in H13.
             split; [ now auto |].
             rewrite <- fundefs_append_assoc in Heqs. auto.
             destruct Heqs as (Heqs, Hf0).
             split; [ now auto |].
             { simpl.
               destruct (get_b v im') eqn:gbim'.
               -  (* v should not be eligible to be inlined *)
                 exfalso.
                 destruct Hf0.
                 inversion H14. specialize (H15 v).
                 apply H15. split.
                 eapply fundefs_append_name_in_fundefs. reflexivity.
                 right. constructor. auto.
                 auto.
               - destruct Hf0. split.
                 + simpl. rewrite H5.
                   assert (He1 : e1 = rename_all_ns sig e1).
                   {
                     clear H5.
                     rewrite <- (proj1 (rename_all_no_shadow _)).
                     symmetry.
                     apply rename_sig_dead.
                     intro.             intros.
                     apply Hsig_post in H5.
                     apply not_bound_dead_or_free in H5.
                     inversion H5.
                     2: apply Hdj_post in H15; inversion H15.
                     rewrite <- H10 in H15.
                     apply num_occur_app_ctx in H15.
                     destructAll; pi0.
                     auto.
                     rewrite <- H10 in Hsig_post.
                     eapply sig_inv_dom_mon.
                     2: apply Hsig_post.
                     rewrite bound_var_app_ctx.
                     right;
                       auto.
                   }
                   rewrite <- He1.
                   reflexivity.
                 + eapply Disjoint_Included_l.
                   2: apply H14.
                   intro. intro.
                   eapply fundefs_append_name_in_fundefs. reflexivity. auto. }
        * intros.
          eapply Hcontract_corresp; eauto.
          unfold term_sub_inl_size in *.
          simpl in *.
          etransitivity.
          apply H11.
          assert (sub_inl_size sub b0 <= sub_inl_size sub im).
          eapply sub_size_le.
          apply b_map_le_c; auto.
          lia.
        * rewrite <- H10 in H9.
          split; intro.
          intro. destruct H11. apply H9 in H12.
          inversion H12. apply H13.
          apply bound_var_app_ctx. left.
          apply bound_var_ctx_rename_all_ns.
          rewrite (proj1 inlined_comp_ctx).
          apply bound_var_ctx_comp_ctx. right. simpl.
          rewrite inlined_fundefs_ctx_append_shallow.
          constructor.
          eapply fundefs_append_name_in_fundefs in H11.
          2: reflexivity.
          apply bound_var_fundefs_ctx_append.
          inversion H11.
          -- left. rewrite Disjoint_inlined_fds.
             apply name_in_fundefs_bound_var_fundefs; auto. eauto.
          -- right. simpl in H15. inversion H15. inversion H17. constructor.
             inversion H17.
        * intro; intros.
          assert (H11' := H11).
          split.
          apply Hsig_post in H11. auto.
          apply Hsig_r in H11.
          inversion H11.
          -- left.
             apply num_occur_app_ctx in H12.  destruct H12. destruct H12. inversion H12.
             inversion H14. pi0.
             destruct H14.
             clear H14.
             clear H16.
             rewrite He1 in H15.
             clear He1.
             subst.
             repeat normalize_ctx.
             apply num_occur_ec_comp_ctx in H13.
             destructAll; pi0.
             simpl in H17. inv H17; pi0.
             rewrite inlined_fundefs_ctx_append_shallow in H24.
             rewrite rename_all_fundefs_ctx_append in H24.
             apply fundefs_ctx_append_num_occur' in H24.
             destructAll; pi0.
             simpl in H18.  inv H18; pi0.
             apply num_occur_app_ctx. exists 0, 0.
             split; auto.
             apply num_occur_ec_comp_ctx.
             exists 0, 0.
             split; auto. split; auto.
             simpl.
             eapply num_occur_ec_n. constructor.
             eauto.
             rewrite inlined_fundefs_append.
             rewrite rename_all_ns_fundefs_append.
             eapply fundefs_append_num_occur.
             reflexivity.
             rewrite inlined_fundefs_append.
             rewrite rename_all_ns_fundefs_append.
             eapply fundefs_append_num_occur.
             reflexivity.
             rewrite rename_all_fun_ns_inlined_fundefs in H17.
             rewrite rename_all_fun_ns_inlined_fundefs.
             eapply dead_occur_fds_le_antimon. simpl in b.
             apply b_map_le_c. eauto. auto.
             simpl. destruct (get_b v b0).
             simpl. constructor. simpl. eapply num_occur_fds_n.
             constructor. eauto. constructor.
             auto.
             rewrite rename_all_fun_ns_inlined_fundefs in H29.
             rewrite rename_all_fun_ns_inlined_fundefs.
             eapply dead_occur_fds_le_antimon. simpl in b.
             apply b_map_le_c. eauto. auto.
             auto.
          -- apply H4c in H11'.
             inversion H11'.
             ++ (* by no zombie *)
               rewrite <- H6 in H7.
               apply shrink_no_zombie in H7.
               apply H7 in H13. left; auto.
             ++ repeat normalize_ctx.
                apply bound_stem_comp_ctx_mut in H12.
                inversion H12.
                right.
                apply bound_stem_comp_ctx_mut.
                left; auto.
                simpl in H14.
                inversion H14.
                rewrite inlined_fundefs_ctx_append_shallow in H19.
                (* if inlined by b0, then dead, o.w. name *)
                destruct (get_b y b0) eqn:gbvb0.
                ** left.  apply H9 in gbvb0. destruct gbvb0.
                   apply not_bound_dead_or_free in H20.
                   inversion H20.
                   auto.
                   apply Hdj_post in H22.
                   inv H22.
                ** right. apply bound_stem_comp_ctx_mut.
                   right. simpl. constructor.
                   rewrite rename_all_fun_ns_inlined_fundefs.
                   apply name_in_fundefs_not_inlined; auto.
                   rewrite rename_all_fundefs_ctx_append in H19.
                   apply name_in_fundefs_ctx_append in H19.
                   rewrite rename_all_ns_fundefs_append.
                   eapply fundefs_append_name_in_fundefs.
                   reflexivity.
                   inversion H19.
                   left.
                   rewrite rename_all_ns_fundefs_append.
                   eapply fundefs_append_name_in_fundefs. reflexivity. left.
                   rewrite rename_all_fun_ns_inlined_fundefs in H20.
                   eapply Included_name_in_fundefs_inlined. eauto. simpl in H20.
                   inversion H20. inversion H22.
                   left.                   rewrite rename_all_ns_fundefs_append.
                   eapply fundefs_append_name_in_fundefs.
                   reflexivity. right. simpl. auto.
                   right.
                   eapply Included_name_in_fundefs_inlined.
                   rewrite rename_all_fun_ns_inlined_fundefs in H22.
                   eauto.
                ** rewrite inlined_fundefs_ctx_append_shallow in H19.
                   rewrite rename_all_fundefs_ctx_append in H19.
                   apply  bound_stem_fundefs_append in H19. simpl in H19.
                   rewrite bound_stem_Fcons1_c in H19. inversion H19.
                   inversion H20.
                   (* cannot be l because then violated unique_binding due to H13 *)
                   apply bound_stem_comp_ctx_mut in H13. inversion H13.
                   apply ub_app_ctx_f in H.
                   destruct H.
                   apply ub_comp_ctx_f in H. destruct H.
                   destruct H25.
                   inversion H26.
                   specialize (H27 y).  exfalso. apply H27.
                   split. apply bound_var_stem_or_not_stem; auto.
                   simpl. constructor.
                   rewrite inlined_fundefs_ctx_append_shallow.
                   rewrite rename_all_fundefs_ctx_append.
                   apply bound_var_fundefs_ctx_append.
                   right. simpl. constructor. auto.

                   simpl in H22. inversion H22.
                   rewrite rename_all_fun_ns_inlined_fundefs in H27.
                   { (* either y is inlined in b0 (and not in im) and then it is dead, o.w. bound stem *)
                     destruct (get_b y b0) eqn:gbvb0.
                     * left.  apply H9 in gbvb0. destruct gbvb0.
                       apply not_bound_dead_or_free in H28.
                       inversion H28.
                       auto.
                       apply Hdj_post in H30.
                       inv H30.
                     * right. apply bound_stem_comp_ctx_mut.
                       right. simpl. constructor.
                       rewrite rename_all_fun_ns_inlined_fundefs.
                       apply name_in_fundefs_not_inlined; auto.
                       apply Included_name_in_fundefs_inlined in H27.
                       rewrite <- fundefs_append_assoc. simpl.
                       repeat normalize_ctx.
                       eapply fundefs_append_name_in_fundefs in H27.
                       2: reflexivity.
                       eapply fundefs_append_name_in_fundefs. reflexivity.
                       inversion H27. auto. simpl in H28. inversion H28.
                       right; auto.
                       right. simpl. auto. }
                   inversion H27.
        * intro. intros. assert (H7' := H7).
          apply H4 in H7.
          destruct H7.
          split.
          rewrite <- H6.
          auto.
          inv H8.
          -- repeat normalize_ctx.
             apply num_occur_app_ctx in H9.
             destructAll; pi0.
             apply num_occur_ec_comp_ctx in H8.
             destructAll; pi0.
             simpl in H10. inv H10; pi0. repeat normalize_ctx.
             apply fundefs_append_num_occur' in H16. destructAll; pi0.
             simpl in H11. rewrite gbvim in H11. simpl in H11. inv H11; pi0.
             left.
             apply num_occur_app_ctx. exists 0, 0.
             split; auto.
             apply num_occur_ec_comp_ctx. exists 0, 0.
             split; auto.
             split; auto.
             simpl.
             eapply num_occur_ec_n.
             constructor; eauto.
             rewrite inlined_fundefs_ctx_append_shallow.
             rewrite rename_all_fundefs_ctx_append.
             apply fundefs_ctx_append_num_occur; eauto.
             simpl. constructor. constructor.
             eauto. auto.
          -- right.
             repeat normalize_ctx.
             apply bound_stem_comp_ctx_mut in H9.
             apply bound_stem_comp_ctx_mut.
             inversion H9.
             ++ left. auto.
             ++ simpl in H8. inv H8.
                right. simpl. constructor.
                repeat normalize_ctx.
                eapply fundefs_append_name_in_fundefs in H14.
                2: reflexivity.
                rewrite inlined_fundefs_ctx_append_shallow.
                rewrite rename_all_fundefs_ctx_append.
                apply name_in_fundefs_ctx_append.
                inv H14.
                auto.
                right. simpl in H8. rewrite gbvim in H8.
                simpl in H8. simpl. auto.
                inv H14. }
  Qed.

(** dec_census_all_case removes all the occurences of variables in all branches from their respective tally in count *)
  Theorem dec_census_all_case_count: forall sig count v l n,
                                       num_occur_case (rename_all_case sig l) v n  ->
                                       get_c v (dec_census_all_case sig l count) = get_c v count - n.
  Proof.
    induction l; intros.
    - simpl.
      inv H. lia.
    - simpl. simpl in H. destruct a.
      inv H.
      unfold dec_census.
      apply IHl in H6.
      assert (Hcc := combine_minus_census_correct).
      destruct Hcc. rewrite <- H.
      rewrite gccombine_sub.
      rewrite H6.
      assert (n0 = (get_c v (init_census (rename_all_ns sig e)))).
      eapply (proj1 (num_occur_det _)); eauto.
      apply init_census_correct.
      rewrite <- H1. lia.
  Qed.

  (** dec_census_case removes all the occurences of variables in all branches EXCEPT
      for the first branch matching the given tag from their respective tally in count  *)
  Theorem dec_census_case_count sig v c0 e m count l n :
    num_occur_case (rename_all_case sig l) v n ->
    findtag l c0 = Some e ->
    num_occur (rename_all_ns sig e) v m ->
    get_c v (dec_census_case sig l c0 count) = get_c v count -  (n - m).
  Proof.
    revert n; induction l; intros n.
    intros. inv H0.
    intros. simpl in *.
    destruct a.
    destruct (var_dec v0 c0).
    - destruct (M.elt_eq v0 c0).
      2: exfalso; auto.
      subst. inv H0. inv H.
      eapply dec_census_all_case_count in H7.
      rewrite H7.
      assert (n0 = m).
      eapply (proj1 (num_occur_det _)); eauto.
      subst. lia.
    - destruct (M.elt_eq v0 c0).
      exfalso; auto.
      inv H. specialize (IHl _ H8 H0 H1).
      unfold dec_census.
      assert (Hcc := combine_minus_census_correct).
      destruct Hcc. rewrite <- H.
      rewrite gccombine_sub. rewrite IHl.
      assert (Hinc := init_census_correct).
      destruct Hinc. specialize (H3 (rename_all_ns sig e0)).
      specialize (H3 v).

      assert (get_c v (init_census (rename_all_ns sig e0)) = n2). eapply (proj1 (num_occur_det _)); eauto.
      rewrite H5.
      assert (m <= m0).
      eapply num_occur_case_le.
      apply findtag_In in H0.

      eapply in_map with (f := (fun (p:var*exp) => let (k, e) := p in
                                                   (k, rename_all_ns sig e))) in H0.
      apply H0.
      apply H8. auto.
      lia.
  Qed.

  Lemma one_rename_all_ar: forall x y v sigma,
      ~ (exists z, M.get z sigma = Some x) ->
      (M.get x sigma = None) ->
      apply_r (M.set x y sigma) v = (apply_r (M.set x y (M.empty var)) (apply_r sigma v)).
  Proof.
    intros.
    destruct (var_dec x v).
    + subst. erewrite apply_r_some by apply M.gss.
      rewrite apply_r_none with (v := v); auto.
      erewrite apply_r_some by apply M.gss.
      auto.
    + rewrite apply_r_set2; auto.
      rewrite apply_r_set2; auto.
      apply apply_r_not_in_sig; auto.
  Qed.

  Lemma one_rename_all_list: forall y x l sigma,
      ~ (exists z, M.get z sigma = Some x) ->
      (M.get x sigma = None) ->
      apply_r_list (M.set x y sigma) l =  (apply_r_list (M.set x y (M.empty var)) (apply_r_list sigma l)).
  Proof.
    induction l; intros.
    reflexivity.
    simpl.
    rewrite IHl; auto.
    destruct (var_dec x a).
    - subst.
      erewrite apply_r_some by apply M.gss.
      erewrite apply_r_none with (v := a); auto.
      erewrite apply_r_some by apply M.gss.
      reflexivity.
    - rewrite apply_r_set2; auto.
      rewrite apply_r_set2; auto.
      apply apply_r_not_in_sig; auto.
  Qed.

  Lemma one_rename_all_ns_mut: forall y x sig,
      ~ Range_map sig x  ->
      ~ Dom_map sig x ->
      ( forall e,
          rename_all_ns (M.set x y (M.empty var)) (rename_all_ns sig e) =  rename_all_ns (M.set x y sig) e  ) /\
      ( forall f,
          rename_all_fun_ns (M.set x y (M.empty var)) (rename_all_fun_ns sig f) =  rename_all_fun_ns (M.set x y sig) f).
  Proof.
    intros y x sig Hr Hd.
    eapply exp_def_mutual_ind; intros; simpl.
    - rewrite H.
      rewrite <- one_rename_all_list; eauto.
    - rewrite <- one_rename_all_ar; auto.
    - simpl in H0. inv H0.
      rewrite H. auto.
    - rewrite <- one_rename_all_ar; auto.
      rewrite H. auto.
    - rewrite H.
      rewrite <- one_rename_all_list; eauto.
      rewrite <- one_rename_all_ar; auto.
    - rewrite H. rewrite H0. reflexivity.
    - rewrite <- one_rename_all_ar; auto.
      rewrite <- one_rename_all_list; auto.
    - now rewrite H.
    - rewrite <- one_rename_all_list; auto.
      rewrite H. auto.
    - rewrite <- one_rename_all_ar; auto.
    - rewrite H; rewrite H0; auto.
    - auto.
  Qed.

  Lemma one_rename_all_ns y x sig :
    forall e,
      ~ Range_map sig x  ->
      ~ Dom_map sig x ->
      rename_all_ns (M.set x y (M.empty var)) (rename_all_ns sig e) =  rename_all_ns (M.set x y sig) e.
  Proof.
    intros. apply one_rename_all_ns_mut; auto.
  Qed.

  (** dec_census_case properly updates the count after case folding *)
  Theorem c_count_fold_case:
    forall c c0 v e sig (l:list (ctor_tag * exp)) count,
      c_count (c |[rename_all_ns sig (Ecase v l) ]|)  count ->
      findtag l c0 = Some e ->
      c_count (c |[ rename_all_ns sig e ]|)
              (dec_census_case sig l c0 (dec_census_list sig [v] count)).
  Proof.
    intros. intro.
    specialize (H v0).
    apply num_occur_app_ctx in H.
    destructAll.
    assert (exists n, num_occur (rename_all_ns sig e) v0 n) by apply e_num_occur.
    destruct H3.
    apply num_occur_app_ctx. exists x, x1.
    split; auto. split; auto.
    inv H1.
    erewrite dec_census_case_count; eauto.
    unfold dec_census_list. simpl.
    simpl in H2.
    assert (x1 <= n).
    { eapply num_occur_case_le. 2: apply H8.
      apply findtag_In in H0.
      eapply in_map with (f := (fun (p:var*exp) => let (k, e) := p in
                                                   (k, rename_all_ns sig e))) in H0.
      apply H0.
      auto.
    }
    destruct (term_util.var_dec v0 (apply_r sig v)).
    - subst. rewrite gdss. rewrite H2.
      lia.
    - rewrite gdso by auto.
      unfold maps_util.getd.
      unfold get_c in H2.
      lia.
  Qed.

  Opaque contract.

  Section Contract_rename.

    Definition rename_sval sig (v : svalue) : svalue :=
      match v with
      | SVconstr x ys => SVconstr x (apply_r_list sig ys)
      | SVfun xs t e => SVfun xs t (rename_all_ns sig e)
      end.

    Definition map_eq_f f (im : b_map) (r1 r2 : ctx_map) :=
      (forall x c ys, M.get x r1 = Some (SVconstr c ys) -> M.get x r2 = option_map f (M.get x r1)) /\
      (forall x ys t e, M.get x r1 = Some (SVfun t ys e) ->
                        (exists e', M.get x r2 = Some (SVfun t ys e')) /\
                        (get_b x im = false -> M.get x r2 = option_map f (M.get x r1))) /\
      (forall x, M.get x r1 = None <-> M.get x r2 = None).

    Lemma map_eq_f_set sig im r1 r2 x v :
      map_eq_f (rename_sval sig) im r1 r2 ->
      map_eq_f (rename_sval sig) im (M.set x v r1) (M.set x (rename_sval sig v) r2).
    Proof.
      intros Heq. split; [| split ]; intros.
      - destruct (var_dec x x0); subst.
        + rewrite !M.gss in *. inv H. simpl. reflexivity.
        + rewrite !M.gso in *; eauto. eapply (proj1 Heq); eauto.
      - destruct (var_dec x x0); subst.
        + rewrite !M.gss in *. inv H. split; eauto. eexists; eauto. reflexivity.
        + rewrite !M.gso in *; eauto. eapply (proj2 Heq); eauto.
      - destruct (var_dec x x0); subst.
        + rewrite !M.gss in *. split; intros Hc; inv Hc.
        + rewrite !M.gso in *; eauto. eapply (proj2 Heq); eauto.
    Qed.

    Lemma map_eq_f_get_SVconstr f im r1 r2 x c ys :
      map_eq_f f im r1 r2 ->
      r1 ! x = Some (SVconstr c ys) ->
      r2 ! x = option_map f (Some (SVconstr c ys)).
    Proof.
      intros Heq1 Hg. assert (Hg' := Hg). eapply Heq1 in Hg.
      rewrite Hg' in *. eassumption.
    Qed.

    Lemma map_eq_f_get_SVfun_false f im r1 r2 x t xs e :
      map_eq_f f im r1 r2 ->
      get_b x im = false ->
      r1 ! x = Some (SVfun t xs e) ->
      r2 ! x = option_map f (Some (SVfun t xs e)).
    Proof.
      intros Heq1 Hf Hg. assert (Hg' := Hg). eapply Heq1 in Hg; eauto.
      rewrite Hg' in *. inv Hg. eauto.
    Qed.

    Lemma map_eq_f_get_SVfun f im r1 r2 x t xs e :
      map_eq_f f im r1 r2 ->
      r1 ! x = Some (SVfun t xs e) ->
      exists e, r2 ! x = Some (SVfun t xs e).
    Proof.
      intros Heq1 Hg. assert (Hg' := Hg). eapply Heq1 in Hg; eauto.
      rewrite Hg' in *. inv Hg. eauto.
    Qed.

    Lemma map_eq_f_get_None f im r1 r2 x:
      map_eq_f f im r1 r2 ->
      r1 ! x = None ->
      r2 ! x = None.
    Proof.
      intros Heq1 Hg. assert (Hg' := Hg). eapply Heq1 in Hg. eassumption.
    Qed.

    Lemma map_eq_f_antimon f im1 im2 r1 r2 :
      map_eq_f f im1 r1 r2 ->
      b_map_le_i im1 im2 ->
      map_eq_f f im2 r1 r2.
    Proof.
      intros Heq Hle. induction Hle; eauto.
      destruct (IHHle Heq) as [Heq1 [Heq2 He3]].
      split; [| split ]; eauto.
      intros. split. now eapply Heq2; eauto.
      intros. eapply Heq2; eauto.
      unfold get_b in *. destruct (peq v x); subst. rewrite M.gss in H0. inv H0.
      rewrite M.gso in H0; eauto.
    Qed.

    Lemma apply_r_join sig x y z :
      apply_r sig (apply_r (M.set x y (M.empty _)) z) =
      apply_r (M.set x (apply_r sig y) sig) z.
    Proof.
      destruct (var_dec x z); subst.
      - unfold apply_r. rewrite !M.gss. reflexivity.
      - unfold apply_r. rewrite !M.gso; eauto.
    Qed.

    Lemma findtag_map_res {A B} f l c res :
      findtag l c = res ->
      @findtag B (map (fun (p : ctor_tag * A) => let (c, e) := p in (c, f e)) l) c = option_map f res.
    Proof.
      induction l; intros H.
      - inv H. reflexivity.
      - simpl in H. destruct a as [c' a].
        unfold M.elt_eq in *. destruct (peq c' c); subst.
        + simpl. rewrite peq_true. reflexivity.
        + simpl. rewrite peq_false. eapply IHl. reflexivity. eauto.
    Qed.

    Lemma update_census_list_join sig l count x y f :
      update_census_list sig (apply_r_list (M.set x y (M.empty M.elt)) l) f count =
      update_census_list (M.set x (apply_r sig y) sig) l f count.
    Proof.
      revert sig count x y f; induction l; intros sig count x y f.
      - reflexivity.
      - simpl. rewrite !apply_r_join. rewrite IHl. reflexivity.
    Qed.

    Lemma update_census_list_Prop sig sig' l f count :
      map_get_r _ sig sig' ->
      update_census_list sig l f count =
      update_census_list sig' l f count.
    Proof.
      revert count. induction l; intros Heq count.
      - reflexivity.
      - simpl. erewrite prop_apply_r; [| eassumption ].
        rewrite IHl. eauto. eassumption.
    Qed.

    Lemma update_census_join_mut :
      (forall e sig f count x y,
          update_census (M.set x (apply_r sig y) sig) e f count =
          update_census sig (rename_all_ns (M.set x y (M.empty _)) e) f count) /\
      (forall B sig f count x y,
          update_census_f (M.set x (apply_r sig y) sig) B f count =
          update_census_f sig (rename_all_fun_ns (M.set x y (M.empty _)) B) f count).
    Proof.
      exp_defs_induction IHe IHl IHb; intros; simpl;
        (try rewrite !update_census_list_join); (try rewrite !apply_r_join);
          (try now (rewrite IHe; reflexivity)); try reflexivity.
      - rewrite IHe.
        simpl in IHl. rewrite IHl. rewrite !apply_r_join. reflexivity.
      - rewrite IHb, IHe. reflexivity.
      - rewrite IHb, IHe. reflexivity.
    Qed.

    Lemma update_census_Prop :
      (forall e sig sig' f count,
          map_get_r _ sig sig' ->
          update_census sig e f count = update_census sig' e f count) /\
      (forall B sig sig' f count,
          map_get_r _ sig sig' ->
          update_census_f sig B f count = update_census_f sig' B f count).
    Proof.
      exp_defs_induction IHe IHl IHb; intros; simpl;
        (try erewrite update_census_list_Prop; eauto);
        (try erewrite prop_apply_r; eauto).
      - simpl in IHl. erewrite <- IHl; [| eassumption ].
        erewrite <- prop_apply_r; [| eassumption ]. erewrite IHe. reflexivity. eassumption.
      - erewrite IHb, IHe; eauto.
      - erewrite IHb, IHe; eauto.
    Qed.

    Lemma apply_r_list_join sig z x y :
      apply_r_list sig (apply_r_list (M.set x y (M.empty _)) z) =
      apply_r_list (M.set x (apply_r sig y) sig) z.
    Proof.
      induction z. reflexivity.
      simpl. rewrite apply_r_join. rewrite IHz. reflexivity.
    Qed.

    Lemma dec_census_all_case_sub sig l x y v:
      dec_census_all_case (M.set x (apply_r sig y) sig) l v =
      dec_census_all_case sig (map (fun (p : ctor_tag * exp) => let (k, e0) := p in (k, rename_all_ns (M.set x y (M.empty M.elt)) e0)) l) v.
    Proof.
      induction l. reflexivity.
      simpl. destruct a. unfold dec_census. rewrite (proj1 update_census_join_mut).
      rewrite IHl. reflexivity.
    Qed.

    Lemma dec_census_case_sub sig l x y v c :
      dec_census_case (M.set x (apply_r sig y) sig) l v c =
      dec_census_case sig (map (fun (p : ctor_tag * exp) => let (k, e0) := p in (k, rename_all_ns (M.set x y (M.empty M.elt)) e0)) l) v c.
    Proof.
      induction l. reflexivity.
      simpl. destruct a. rewrite <- !IHl.
      rewrite <- !dec_census_all_case_sub.
      unfold dec_census. rewrite (proj1 update_census_join_mut). reflexivity.
    Qed.

    Lemma dec_census_all_case_Prop sig sig' l v :
      map_get_r _ sig sig' ->
      dec_census_all_case sig l v = dec_census_all_case sig' l v.
    Proof.
      induction l. intros Hc. reflexivity.
      intros Hc. simpl. destruct a. unfold dec_census. erewrite (proj1 update_census_Prop); [| eassumption ].
      rewrite IHl. reflexivity. eassumption.
    Qed.

    Lemma dec_census_case_Prop sig sig' l v c :
      map_get_r _ sig sig' ->
      dec_census_case sig l v c = dec_census_case sig' l v c.
    Proof.
      intros Hc. induction l. reflexivity.
      simpl. destruct a. rewrite <- !IHl; eauto.
      (erewrite (dec_census_all_case_Prop sig sig'); eauto).
      (erewrite <- (dec_census_all_case_Prop sig sig'); eauto).
      unfold dec_census. erewrite (proj1 update_census_Prop). reflexivity.
      eassumption.
    Qed.

    Definition bv_map (sub : ctx_map) :=
      (fun x => exists f ft xs e, sub ! f = Some (SVfun ft xs e) /\ x \in FromList xs :|: bound_var e).

    Lemma bv_map_set_Vconstr sub x c l :
      bv_map (M.set x (SVconstr c l) sub) \subset bv_map sub.
    Proof.
      intros z (f & ft & xs & e & Hget & Hin).
      do 4 eexists; split; eauto. rewrite M.gso in Hget. eassumption.
      intros Hc; subst. rewrite M.gss in Hget. congruence.
    Qed.

    Lemma bv_map_get_SVfun f sub ft xs e :
      M.get f sub = Some (SVfun ft xs e) ->
      FromList xs :|: bound_var e  \subset bv_map sub.
    Proof.
      intros Hget x Hin.
      do 4 eexists; split; eauto.
    Qed.

    Lemma bv_map_set_SVfun sub x ft xs e :
      bv_map (M.set x (SVfun ft xs e) sub) \subset FromList xs :|: bound_var e :|: bv_map sub.
    Proof.
      intros z (f & ft' & xs' & e' & Hget & Hin).
      destruct (peq x f); subst.
      - rewrite M.gss in Hget. inv Hget. now left.
      - right. do 4 eexists; split; eauto. rewrite M.gso in Hget; eauto.
    Qed.

    Definition map_eq_ren {A} f (m1 m2 : M.t A) :=
      forall v : positive, m1 ! v = m2 ! (f v).

    (* Lemma apply_rset_comm sig x v1 y v2 : *)
    (*   x <> y -> *)
    (*   apply_r (M.set x v1 (M.set x v2 sig)) x = apply_r (M.set x *)

    Theorem set_list_set {A} a (v : A) lx ly sig :
      ~ a \in FromList lx ->
      M.set a v (set_list (combine lx ly) sig) =mg= set_list (combine lx ly) (M.set a v sig).
    Proof.
      revert a v ly sig. induction lx. intros. simpl. now apply smg_refl.
      intros. destruct ly. simpl. now apply smg_refl.
      simpl.
      eapply smg_trans. eapply set_set. intros Hc; subst; eapply H; eauto.
      now left.
      eapply proper_set. eapply IHlx.
      intros Hc; eapply H. now right.
    Qed.

    Lemma apply_r_permut_set_setlist a v lx ly sig y :
      ~ a \in FromList lx ->
      apply_r (M.set a v (set_list (combine lx ly) sig)) y =
      apply_r (set_list (combine lx ly) (M.set a v sig)) y.
    Proof.
      intros. eapply prop_apply_r. eapply set_list_set. eassumption.
    Qed.

    Lemma set_list_map_get_d_prop {A} l (m1 m2 : M.t A) :
      m1 =mg= m2 ->
      set_list l m1 =mg= set_list l m2.
    Proof.
      intros Heq. induction l. simpl; eassumption.
      simpl. eapply proper_set. eassumption.
    Qed.

    Lemma nthN_None_l {A} (l l' : list A) n :
      nthN l n = None ->
      length l = length l' ->
      nthN l' n = None.
    Proof.
      revert l' n. induction l; intros; simpl.
      - destruct l'; simpl in *; eauto; congruence.
      - destruct l'; simpl in *; eauto. destruct n; try congruence.
        eapply IHl; eauto.
    Qed.


  Lemma rename_all_ns_join y x sig :
    (forall e, rename_all_ns (M.set x (apply_r sig y) sig) e = rename_all_ns sig (rename_all_ns (M.set x y (M.empty _)) e)) /\
    (forall f, rename_all_fun_ns (M.set x (apply_r sig y) sig) f = rename_all_fun_ns sig (rename_all_fun_ns (M.set x y (M.empty _)) f)).
  Proof.
    exp_defs_induction IHe IHl IHB; intros;
      simpl; (try rewrite apply_r_list_join); (try rewrite apply_r_join); (try rewrite IHe); try reflexivity.
    - simpl in IHl. inv IHl. rewrite H1. reflexivity.
    - rewrite IHB. reflexivity.
    - rewrite IHB. reflexivity.
  Qed.

  Lemma apply_r_pull x y z sig :
    ~ x \in Range_map sig ->
    ~ x \in Dom_map sig ->
    apply_r (M.set x (apply_r sig y) (M.empty _)) (apply_r sig z) = apply_r sig (apply_r (M.set x y (M.empty _)) z).
  Proof.
    intros. unfold apply_r.
    destruct (@PTree.get var z sig) eqn:Heqz.
    + rewrite M.gso with (i := z). rewrite M.gempty. unfold var, M.elt in *. rewrite Heqz.
      destruct (M.get y sig).
      * rewrite M.gso, M.gempty. reflexivity.
        intros Hc; subst.
        now eapply H; eexists; eauto.
      * rewrite M.gso, M.gempty. reflexivity.
        intros Hc; subst. eapply H; eexists; eauto.
      * intros Hc; subst. eapply H0; eexists; eauto.
    + destruct (peq x z); subst.
      * rewrite !M.gss. reflexivity.
      * rewrite !M.gso, !M.gempty; eauto. rewrite Heqz. reflexivity.
  Qed.


  Lemma apply_r_list_pull x y zs sig :
    ~ x \in Range_map sig ->
    ~ x \in Dom_map sig ->
    apply_r_list (M.set x (apply_r sig y) (M.empty _)) (apply_r_list sig zs) = apply_r_list sig (apply_r_list (M.set x y (M.empty _)) zs).
  Proof.
    intros. induction zs. reflexivity.
    simpl. rewrite apply_r_pull; eauto. rewrite IHzs. reflexivity.
  Qed.

  Lemma rename_all_ns_push y x sig :
    (forall e,
         ~ x \in Range_map sig -> ~ x \in Dom_map sig ->
        rename_all_ns (M.set x (apply_r sig y) (M.empty _)) (rename_all_ns sig e) = rename_all_ns sig (rename_all_ns (M.set x y (M.empty _)) e)) /\
    (forall f,
        ~ x \in Range_map sig -> ~ x \in Dom_map sig ->
        rename_all_fun_ns (M.set x (apply_r sig y) (M.empty _)) (rename_all_fun_ns sig f) =
        rename_all_fun_ns sig (rename_all_fun_ns (M.set x y (M.empty _)) f)).
  Proof.
    intros.
    exp_defs_induction IHe IHl IHB; intros;
      simpl; (try rewrite apply_r_list_pull; eauto); (try rewrite apply_r_pull; eauto); (try rewrite IHe; eauto); try reflexivity.
    - simpl in IHl. specialize (IHl H H0). inv IHl. reflexivity.
    - rewrite IHB; eauto.
    - rewrite IHB; eauto.
  Qed.


  Lemma rename_all_ns_list_join xs ys sig e :
    Disjoint _ (FromList xs) (FromList ys) ->
    rename_all_ns (set_list (combine xs (apply_r_list sig ys)) sig) e =
    rename_all_ns sig (rename_all_ns (set_list (combine xs ys) (M.empty _)) e).
  Proof.
    revert ys sig e; induction xs; intros.
    - simpl. rewrite <- (proj1 rename_all_ns_empty). reflexivity.
    - simpl. destruct ys as [| y ys].
      + simpl. rewrite <- (proj1 rename_all_ns_empty). reflexivity.
      + simpl. repeat normalize_sets.  rewrite <- (apply_r_set_list2 y sig  xs (apply_r_list sig ys)).
        rewrite (proj1 (rename_all_ns_join _ _ _)). rewrite IHxs.
        assert (Heqs: y = apply_r (set_list (combine xs ys) (M.empty positive)) y).
        { rewrite apply_r_set_list2. rewrite apply_r_empty . reflexivity.
          intros Hc; eapply H; eauto. }
        rewrite Heqs at 2. rewrite (proj1 (rename_all_ns_join _ _ _)). reflexivity.
        eapply Disjoint_Included; [| | eassumption ]; sets.
        intros Hc. eapply H; constructor; eauto.
  Qed.

  Lemma rename_all_ns_Disjoint m e :
    Disjoint _ (Dom_map m) (Complement _ (dead_var e)) ->
    rename_all_ns m e = e.
  Proof.
    intros. erewrite (proj1 eq_P_rename_all_ns).
    rewrite <- (proj1 rename_all_ns_empty). reflexivity.
    intros x Hin. inv H. rewrite M.gempty.
    destruct (m ! x) eqn:H; eauto.
    exfalso. eapply H0. constructor; eauto.
    eexists; eauto.
  Qed.


  Theorem rename_all_ctx_ns_empty:
    (forall C, C = rename_all_ctx_ns (M.empty var) C) /\
    (forall fds, fds = rename_all_fun_ctx_ns (M.empty var) fds).
  Proof.
    exp_fundefs_ctx_induction IHe IHB; intros; simpl;
      try rewrite apply_r_empty; try rewrite apply_r_list_empty;
        try rewrite <- IHe; try rewrite <- IHB;
          try rewrite <- (proj2 rename_all_ns_empty);
          try rewrite <- (proj1 rename_all_ns_empty);
          try reflexivity.
    - rewrite !(proj1 All_Forall.forall_map_id_spec). reflexivity.
      induction l0; eauto. constructor; eauto.
      destruct a. erewrite <- (proj1 rename_all_ns_empty). reflexivity.

      induction l; eauto. constructor; eauto.
      destruct a. erewrite <- (proj1 rename_all_ns_empty). reflexivity.
  Qed.


  Lemma rename_all_ctx_ns_Disjoint m e :
    Disjoint _ (Dom_map m) (Complement _ (dead_var_ctx e)) ->
    rename_all_ctx_ns m e = e.
  Proof.
    intros. erewrite (proj1 eq_P_rename_all_ctx_ns) with (sub' := M.empty _).
    rewrite <- (proj1 rename_all_ctx_ns_empty). reflexivity.
    intros x Hin. inv H. rewrite M.gempty.
    destruct (m ! x) eqn:H; eauto.
    exfalso. eapply H0. constructor; eauto.
    eexists; eauto.
  Qed.

  Lemma one_rename_all_ctx_ns_mut y x sig :
      (forall e,
          ~ Range_map sig x  -> ~ Dom_map sig x ->
          rename_all_ctx_ns (M.set x y (M.empty var)) (rename_all_ctx_ns sig e) =  rename_all_ctx_ns (M.set x y sig) e  ) /\
      (forall f,
          ~ Range_map sig x  -> ~ Dom_map sig x ->
          rename_all_fun_ctx_ns (M.set x y (M.empty var)) (rename_all_fun_ctx_ns sig f) =  rename_all_fun_ctx_ns (M.set x y sig) f).
  Proof.
    intros; exp_fundefs_ctx_induction IHe IHB; intros; simpl; eauto;
      (try (rewrite <- one_rename_all_list; eauto));
      (try (rewrite <- one_rename_all_ar; eauto));
      (try (rewrite (proj2 (one_rename_all_ns_mut _ _ _ H H0))));
      (try (rewrite (proj1 (one_rename_all_ns_mut _ _ _ H H0))));
      (try rewrite IHe; eauto);
      (try rewrite IHB; eauto).
    - simpl. f_equal; eauto.
      + induction l; eauto. destruct a. simpl; rewrite IHl. f_equal.
        rewrite one_rename_all_ns; eauto.
      + induction l0; eauto. simpl; rewrite IHl0. f_equal.
        destruct a. rewrite one_rename_all_ns; eauto.
  Qed.



  Theorem set_list_rename_all_ctx_ns:
    forall l0 l,
      (forall e sig,
         Included _ (FromList l0) (Union _ (Complement _ (Range_map sig)) (dead_var_ctx (rename_all_ctx_ns sig e))) ->
         Disjoint _ (FromList l0) (Dom_map sig) ->
         rename_all_ctx_ns (set_list (combine l0 (apply_r_list sig l)) (M.empty var))
                           (rename_all_ctx_ns sig e)  =
         rename_all_ctx_ns (set_list (combine l0 (apply_r_list sig l)) sig) e) /\
      (forall f sig,
         Included _ (FromList l0) (Union _ (Complement _ (Range_map sig)) (dead_var_fundefs_ctx (rename_all_fun_ctx_ns sig f))) ->
         Disjoint _ (FromList l0) (Dom_map sig) ->
         rename_all_fun_ctx_ns (set_list (combine l0 (apply_r_list sig l)) (M.empty var))
                               (rename_all_fun_ctx_ns sig f)  =
         rename_all_fun_ctx_ns (set_list (combine l0 (apply_r_list sig l)) sig) f).
  Proof.
    intros l0 l.
    assert (Hpr := prop_rename_all).
    destruct Hpr as (Hpr1, Hpr2).
    exp_fundefs_ctx_induction IHe IHB; intros; simpl; eauto.
    - rewrite set_list_rename_all_arl; auto. rewrite IHe; eauto.
      + eapply Included_trans. eassumption.
        eapply Included_Union_compat. reflexivity.
        simpl. intro; intros. inv H1. pi0; eauto.
      + intro. intro. apply H in H1. inv H1; auto.
        right. intro. simpl in H2. inv H2; pi0.
        apply not_occur_list_not_in in H2. auto.
    - rewrite set_list_rename_all_ar; auto. rewrite IHe; eauto.
      + eapply Included_trans. eassumption.
        eapply Included_Union_compat. reflexivity.
        simpl. intro; intros. inv H1. pi0; eauto.
      + intro. intro. apply H in H1. inv H1; auto.
        destruct (var_dec x (apply_r sig v0)); subst; eauto.
        right. intro. simpl in H2. inv H2; pi0.
        rewrite peq_true in H2; lia.
    - rewrite set_list_rename_all_arl; auto. rewrite IHe; eauto.
      rewrite set_list_rename_all_ar; auto.
      + intros. eapply H in H1. inv H1; eauto. inv H2; eauto.
        destruct (var_dec x (apply_r sig f)); subst; eauto.
        lia.
      + eapply Included_trans. eassumption.
        eapply Included_Union_compat. reflexivity.
        simpl. intro; intros. inv H1. pi0; eauto.
      + intro. intro. apply H in H1. inv H1; auto.
        simpl in H2. inv H2; pi0. dec_vars; pi0.
        right. intro. apply not_occur_list_not_in in H2; auto.
    - rewrite IHe; auto.
      eapply Included_trans. eassumption.
      eapply Included_Union_compat. reflexivity.
      simpl. intro; intros. inv H1. pi0; eauto.
    - rewrite set_list_rename_all_arl; auto. rewrite IHe; eauto.
      + eapply Included_trans. eassumption.
        eapply Included_Union_compat. reflexivity.
        simpl. intro; intros. inv H1. pi0; eauto.
      + intro. intro. apply H in H1. inv H1; auto.
        right. intro. simpl in H2. inv H2; pi0.
        apply not_occur_list_not_in in H2. auto.
    - simpl. f_equal.
      + rewrite set_list_rename_all_ar; auto.
        intros. eapply H in H1. inv H1; eauto. inv H2; eauto. pi0; dec_vars. eauto.
      + induction l1; simpl; eauto. destruct a. rewrite IHl1.
        f_equal.  f_equal. eapply set_list_rename_all_ns; eauto.
        eapply Included_trans. eapply H. eapply Included_Union_compat. reflexivity.
        intros x Hin. inv Hin; inv H7; pi0; dec_vars; now eauto.
        eapply Included_trans. eapply H. eapply Included_Union_compat. reflexivity.
        intros x Hin. inv Hin.
        assert (Hnum : num_occur_list [apply_r sig v] x = 0).
        { simpl. pi0; dec_vars. reflexivity. }
        pi0; dec_vars.
        unfold dead_var_ctx. replace 0 with (num_occur_list [apply_r sig v] x + 0 + 0 + 0) by lia.
        econstructor; eauto. inv H7; pi0. eassumption.
      + eapply IHe; eauto.
        * eapply Included_trans. eassumption.
          eapply Included_Union_compat. reflexivity.
          simpl. intro; intros. inv H1. pi0; eauto.
      + induction l2; simpl; eauto.
        destruct a. rewrite IHl2.
        f_equal.  f_equal. eapply set_list_rename_all_ns; eauto.
        eapply Included_trans. eapply H. eapply Included_Union_compat. reflexivity.
        intros x Hin. inv Hin; inv H10; pi0; dec_vars; now eauto.
        eapply Included_trans. eapply H. eapply Included_Union_compat. reflexivity.
        intros x Hin. inv Hin.
        assert (Hnum : num_occur_list [apply_r sig v] x = 0).
        { simpl. pi0; dec_vars. reflexivity. }
        pi0; dec_vars.
        unfold dead_var_ctx. replace 0 with (num_occur_list [apply_r sig v] x + 0 + 0 + 0) by lia.
        econstructor; eauto. inv H10; pi0. eassumption.
    - rewrite IHe; eauto.
      rewrite (proj2 (set_list_rename_all_ns _ _)); eauto.
      + eapply Included_trans. eapply H. eapply Included_Union_compat. reflexivity.
        intros x Hin. inv Hin. pi0; eauto.
      + eapply Included_trans. eapply H. eapply Included_Union_compat. reflexivity.
        intros x Hin. inv Hin. pi0; eauto.
    - rewrite IHB; eauto.
      rewrite (proj1 (set_list_rename_all_ns _ _)); eauto.
      + eapply Included_trans. eapply H. eapply Included_Union_compat. reflexivity.
        intros x Hin. inv Hin. pi0; eauto.
      + eapply Included_trans. eapply H. eapply Included_Union_compat. reflexivity.
        intros x Hin. inv Hin. pi0; eauto.
    - rewrite IHe; eauto.
      rewrite (proj2 (set_list_rename_all_ns _ _)); eauto.
      + eapply Included_trans. eapply H. eapply Included_Union_compat. reflexivity.
        intros x Hin. inv Hin. pi0; eauto.
      + eapply Included_trans. eapply H. eapply Included_Union_compat. reflexivity.
        intros x Hin. inv Hin. pi0; eauto.
    - rewrite IHB; eauto.
      rewrite (proj1 (set_list_rename_all_ns _ _)); eauto.
      + eapply Included_trans. eapply H. eapply Included_Union_compat. reflexivity.
        intros x Hin. inv Hin. pi0; eauto.
      + eapply Included_trans. eapply H. eapply Included_Union_compat. reflexivity.
        intros x Hin. inv Hin. pi0; eauto.
  Qed.


  Lemma complement_dead_var e :
    Complement _ (dead_var e) \subset (occurs_free e) :|: (bound_var e).
  Proof.
    intros x Hin. destruct (bound_var_dec e) as [Hdec]. destruct (Hdec x); eauto.
    eapply not_bound_dead_or_free in n. inv n; eauto.
    exfalso; eauto.
  Qed.


  Definition dead_var_map im sub :=
    fun x => (forall f ft xs e, get_b f im = false -> sub ! f = Some (SVfun ft xs e) -> x \in dead_var e) /\
             (forall z c l, sub ! z = Some (SVconstr c l) -> num_occur_list l x = 0).

  Lemma map_eq_f_Disjoint x y im sub :
    x \in dead_var_map im sub ->
   map_eq_f (rename_sval (M.set x y (M.empty _))) im sub sub.
  Proof.
    intros Hdead. split; [| split ]; intros; [| | reflexivity ].
    - rewrite H. simpl. rewrite Disjoint_apply_r_FromList. reflexivity.
      rewrite Dom_map_set, Dom_map_empty. normalize_sets.
      eapply Disjoint_Singleton_l.
      eapply Hdead in H. eapply not_occur_list. eassumption.
    - split. now eauto. intros. rewrite H.
      simpl. rewrite rename_all_ns_Disjoint. reflexivity.
      rewrite Dom_map_set, Dom_map_empty. normalize_sets.
      eapply Disjoint_Singleton_l. intros Hc.
      eapply Hdead in H. contradiction. eassumption.
  Qed.

  Ltac destruct_num_occur :=
    repeat normalize_ctx;
    repeat (match goal with (* messy because it might not match *)
            | [H : num_occur_fds _ _ _ |- _] => simpl in H
            | [H : num_occur _ _ _ |- _] => simpl in H
            | [H : num_occur_ec _ _ _ |- _] => simpl in H
            end);
    match goal with
    | [H : num_occur (comp_ctx_f _ _) _ _ |- _ ] => rewrite <- app_ctx_f_fuse in H
    | [H : num_occur (_ |[ _ ]|) _ _ |- _ ] => eapply (proj1 (num_occur_app_ctx_mut _ _)) in H; destructAll; pi0
    | [H : num_occur_ec (comp_ctx_f _ _ ) _ _ |- _] => eapply num_occur_ec_comp_ctx in H; destructAll; pi0
    | [H : num_occur (Eletapp _ _ _ _ _ ) _ _ |- _] => inv H; destructAll; pi0; dec_vars
    | [H : num_occur_ec (Efun1_c _ _) _ _ |- _ ] => inv H; destructAll; pi0
    | [H : num_occur_fds (fundefs_append _ _) _ _ |- _ ] => eapply fundefs_append_num_occur' in H; destructAll; pi0
    | [H : num_occur_fds (Fcons _ _ _ _ _) _ _ |- _ ] => inv H; pi0
    end.

  Ltac normalize_bound_var_lemmas :=
    match goal with
    | [H : _ \in bound_var (rename_all_ns _ _) |- _] => eapply bound_var_rename_all_ns in H
    | [H : _ \in bound_var_fundefs  (rename_all_fun_ns _ _) |- _] => eapply bound_var_rename_all_ns_fundefs in H
    | [H : _ \in bound_var_ctx (rename_all_ctx_ns _ _) |- _ ] => eapply (proj1 (bound_var_ctx_rename_all_ns _)) in H
    | [H : _ \in bound_stem_ctx (rename_all_ctx_ns _ _) |- _ ] => eapply (proj1 (bound_stem_ctx_rename_all_ns _)) in H
    | [H : _ \in bound_var_ctx (comp_ctx_f _ _) |- _ ] => eapply (proj1 bound_var_ctx_comp_ctx) in H
    | [H : _ \in bound_stem_ctx (comp_ctx_f _ _) |- _ ] => eapply (proj1 (bound_stem_comp_ctx_mut _)) in H
    | [H : _ \in bound_var (_ |[ _ ]|) |- _] => eapply bound_var_app_ctx in H
    | [H : _ \in bound_var_fundefs (_ |[ _ ]|) |- _] => eapply bound_var_app_f_ctx in H
    | [H : _ \in bound_var (comp_ctx_f _ _) |- _] => rewrite <- app_ctx_f_fuse in H
    | [H : _ \in bound_var_fundefs (comp_f_ctx_f _ _) |- _] => rewrite <- app_f_ctx_f_fuse in H
    | [H : _ \in bound_var_fundefs (fundefs_append ?X1 ?X2) |- _ ] =>
      rewrite fundefs_append_bound_vars in H; [| reflexivity ]
    end.

  Lemma cmap_view_ctx_dead_var im sub C :
    cmap_view_ctx sub C ->
    dead_var_ctx (inlined_ctx_f C im) \subset dead_var_map im sub.
  Proof.
    intros [Hm1 Hm2] x Hdead. split; intros.
    - eapply Hm2 in H0. destructAll. unfold dead_var, dead_var_ctx, In in *.
      repeat destruct_num_occur. rewrite H in H2. repeat destruct_num_occur.
      simpl. eassumption.
    - eapply Hm1 in H. destructAll. unfold dead_var, dead_var_ctx, In in *.
      repeat destruct_num_occur. inv H0. pi0. lia.
  Qed.

  Lemma Disjoint_dead_var S e :
    Disjoint _ S (bound_var e :|: occurs_free e) ->
    S \subset dead_var e.
  Proof.
    intros Hd x Hin. unfold dead_var.
    destruct (e_num_occur x e). destruct x0; eauto.
    exfalso. eapply Hd. constructor. eassumption.
    rewrite Union_commut. eapply complement_dead_var.
    intros Hc. unfold dead_var, In in *. eapply num_occur_det in H; [| clear H; eassumption ].
    congruence.
  Qed.

  Lemma apply_r_set_list_In sig l1 l2 x :
    x \in FromList l1 ->
    length l1 = length l2 ->
    apply_r (set_list (combine l1 l2) sig) x \in FromList l2.
  Proof.
    revert sig l2; induction l1; intros sig l2 Hin Hleq. now inv Hin.
    destruct l2; try now inv Hleq. inv Hleq.
    repeat normalize_sets. simpl. destruct (peq a x); subst.
    - unfold apply_r. rewrite M.gss. now left.
    - inv Hin. inv H; contradiction.
      rewrite apply_r_set2; eauto.
  Qed.

  Lemma num_occur_inline_letapp' e f C x x' :
    num_occur e f 0 ->
    inline_letapp e  x = Some (C, x') ->
    num_occur_ec C f 0.
  Proof.
    revert f C x x'.
    induction e using exp_ind'; intros g C y x' Hnum Hin; simpl in Hin;
      (try match goal with
           | [ _ : context [inline_letapp ?E ?X ] |- _] => destruct (inline_letapp E X) as [[C' x''] | ] eqn:Hin'; inv Hin
           end); try congruence.
    - inv Hnum. pi0. eapply IHe in H4; eauto.
      rewrite Nat.add_comm. constructor. eassumption.
    - inv Hnum. pi0. eapply IHe in H5; eauto. constructor. eassumption.
    - inv Hnum. pi0. eapply IHe in H5; eauto. constructor. eassumption.
    - inv Hnum. pi0. eapply IHe in Hin'; eauto. constructor; eauto.
    - inv Hin. inv Hnum. rewrite plus_n_O. econstructor. constructor.
    - inv Hnum. constructor. eauto.
    - inv Hnum. pi0. eapply IHe in H4; eauto. rewrite Nat.add_comm. constructor. eassumption.
    - inv Hin. inv Hnum. dec_vars. constructor.
  Qed.


  (* TODO move *)
  Lemma not_occurs_not_free_ctx :
    forall v, (forall e, num_occur_ec e v 0 -> ~ occurs_free_ctx e v ) /\
              (forall f, num_occur_fdc f v 0 -> ~ occurs_free_fundefs_ctx f v ).
  Proof.
    intro v.
    exp_fundefs_ctx_induction IHe IHB; unfold not in *; intros Hnum Hc; intros; try (inv Hnum; pi0); (try now inv Hc); inv Hc; eauto;
      (try now eapply not_occur_list_not_in; eauto);
      (try (match goal with
            | [H : context[var_dec ?X ?Y] |- _] => destruct (var_dec X Y); inv H; pi0
            end)); eauto.
    - inv H; eauto. eapply (proj1 (not_occurs_not_free _)); [| eassumption ].
      replace 0 with (num_occur_list [v0] v + 0).
      now constructor.
      simpl. destruct (term_util.var_dec v v0). exfalso; auto. auto.
      eapply (proj1 (not_occurs_not_free _)); [| eassumption ].
      replace 0 with (num_occur_list [v0] v + 0).
      now constructor.
      simpl. destruct (term_util.var_dec v v0). exfalso; auto. auto.
    - eapply (proj2 (not_occurs_not_free _)); eauto.
    - eapply (proj1 (not_occurs_not_free _)); eauto.
    - eapply (proj2 (not_occurs_not_free _)); eauto.
    - eapply (proj1 (not_occurs_not_free _)); eauto.
  Qed.


  Lemma complement_dead_var_ctx e :
    Complement _ (dead_var_ctx e) \subset (occurs_free_ctx e) :|: (bound_var_ctx e).
  Proof.
    intros x Hin. destruct (bound_var_ctx_dec e) as [Hdec]. destruct (Hdec x); eauto.
    eapply not_bound_dead_or_free_ctx  in n. inv n; eauto.
    exfalso; eauto.
  Qed.

  Lemma Disjoint_dead_var_ctx S e :
    Disjoint _ S (bound_var_ctx e :|: occurs_free_ctx e) ->
    S \subset dead_var_ctx e.
  Proof.
    intros Hd x Hin. unfold dead_var_ctx.
    destruct (e_num_occur_ec e x). destruct x0; eauto.
    exfalso. eapply Hd. constructor. eassumption.
    rewrite Union_commut. eapply complement_dead_var_ctx.
    intros Hc. unfold dead_var, In in *. eapply num_occur_ec_det in H; [| clear H; eassumption ].
    congruence.
  Qed.

  Theorem cmap_view_letapp:
    forall sub c v f t ys,
      cmap_view_ctx sub c -> cmap_view_ctx sub (comp_ctx_f c (Eletapp_c v f t ys Hole_c)).
  Proof.
    intros; split; intros; split; intros.
    - apply H in H0. destructAll.
      eexists; eexists.
      rewrite  comp_ctx_f_assoc.
      simpl. reflexivity.
    - apply H. destructAll.
      apply comp_ctx_split in H0.
      destruct H0; destructAll.
      + destruct x2; inv H0.
        eauto.
      + destruct x3; inv H2.
        destruct x3; inv H6.
    - apply H in H0.
      destructAll.
      eexists; eexists; eexists; eexists.
      rewrite  comp_ctx_f_assoc.
      simpl. reflexivity.
    - apply H.
      destructAll.
      apply comp_ctx_split in H0.
      destruct H0; destructAll.
      + destruct x3; inv H0.
        eauto.
      + destruct x4; inv H2.
        destruct x4; inv H6.
  Qed.


  Lemma inv_app_Eprim_val : forall (x : var) p (e : exp),
    Eprim_val x p e = Eprim_val_c x p Hole_c |[ e ]|.
  Proof. reflexivity. Qed.

  (** main theorem! contract produces an output term related to the input by the shrink rewrite system.
      The output count is correct for the output state, and the returned maps respect their respective invariant *)
  Theorem shrink_corresp:
    forall e sub im sig c count,
      let ce := (app_ctx_f (rename_all_ctx_ns sig (inlined_ctx_f c im)) (rename_all_ns sig e)) in
      unique_bindings ce ->
      closed_exp ce ->
      c_count ce count ->
      cmap_view_ctx sub c ->
      inl_inv im sub ce ->
      sig_inv_full sig (rename_all_ctx_ns sig (inlined_ctx_f c im)) (rename_all_ns sig e) ->
      forall e' steps count' im' BP,
        contract sig count e sub im = existT _ (e', steps, count', im') BP ->
        let ce' := (app_ctx_f (rename_all_ctx_ns sig (inlined_ctx_f c im')) e') in
        gsr_clos steps ce ce' /\ c_count ce' count' /\ inl_inv im' sub ce' /\
        sig_inv_codom sig (rename_all_ctx_ns sig (inlined_ctx_f c im')) e' .
  Proof.
    intros e sub inl. remember (1 + term_sub_inl_size (e, sub,inl)) as n.
    assert (n > term_sub_inl_size (e, sub, inl)) by lia. clear Heqn.
    revert e sub inl H. induction n; intros. now inv H. rewrite contract_eq in H6. destruct e; unfold contract_def in H6.
    - (* constr *)
      destruct (get_c v count) eqn:gvc.
      + (* dead constr *)
        unfold incr_steps in H6. simpl in H6.
        remember (contract sig (dec_census_list sig l count) e sub inl) as s.  destruct s as [[[[? ?] ?] ?] ?]. inv H6.
        symmetry in Heqs. simpl in ce.
        assert (gsr_clos 1 ce (rename_all_ctx_ns sig (inlined_ctx_f c inl) |[ (rename_all_ns sig e) ]|)).
        { unfold ce. replace 1 with (1 + 0) by lia. eapply Trans_srw; [| now constructor ].
          constructor. constructor.
          specialize (H2 v). unfold ce in H2.
          apply num_occur_app_ctx in H2. rewrite gvc in H2. destructAll; pi0.
          inv H6; pi0; auto. rewrite H7. auto. }
        assert (Hub := gsr_clos_preserves_clos _ _ _ H0 H1 H6).
        destruct Hub as (Hub, Hdj).
        assert (H5' := H5).
        apply sig_inv_combine in H5.
        destruct H5 as (H5, H5cod).
        assert (Hse := gsr_preserves_sig_dom _ _ _ _ H0 (closed_implies_Disjoint _ H1) H6 H5).
        simpl in Heqs. eapply IHn in Heqs; eauto.
        * destructAll. unfold ce'.
          split.
          -- rewrite Nat.add_comm. eapply gsr_clos_trans. eassumption. eassumption.
          -- now split; auto.
        * unfold term_sub_inl_size in *. simpl in *. lia.
        * intro. specialize (H2 v0). unfold ce in H2.
          apply num_occur_app_ctx in H2. destructAll. inv H7.
          apply num_occur_app_ctx. exists x, n1. repeat split; [ now auto | now auto | ].
          unfold dec_census_list. rewrite <- combine_minus_census_list, gccombine_sub.
          rewrite H8. rewrite update_census_list_correct. rewrite apply_r_list_empty.
          unfold get_c. rewrite M.gempty. lia.
        * intro. intros. apply H4 in H7. destructAll.
          assert (Included _ (bound_var (rename_all_ctx_ns sig (inlined_ctx_f c inl) |[ rename_all_ns sig e ]|)) (bound_var ce)).
          { unfold ce. repeat rewrite bound_var_app_ctx. apply Included_Union_compat. now sets.
            rewrite bound_var_Econstr. left; auto. }
          split; auto.
          -- intro; apply H7. apply H9. auto.
          -- intros. apply H8 in H10. eapply Disjoint_Included_l.
             2: apply H10. auto.
        * simpl in H5'. rewrite inv_app_Econstr in H5'. apply sig_inv_full_dead_l in H5'. auto.
      + (* live constr *)
        assert (M.get v sub = None) by (eapply sub_none_from_pre; simpl; eauto; simpl; auto).
        assert (rename_all_ctx_ns sig (inlined_ctx_f c inl)
               |[ rename_all_ns sig (Econstr v c0 l e)]|  =
                                                          (rename_all_ctx_ns sig (inlined_ctx_f (comp_ctx_f c (Econstr_c v c0 l Hole_c)) inl)
                                                          |[ rename_all_ns sig e ]|)) by ctx_inl_push.
        remember (contract sig count e (M.set v (SVconstr c0 l) sub) inl) as s. symmetry in Heqs.
        destruct s. destruct x. destruct p. destruct p.
        eapply IHn with (c := (comp_ctx_f c (Econstr_c v c0 l Hole_c))) in Heqs; unfold ce in *; try rewrite H8 in *; eauto.
        * { destruct Heqs. destruct H10. destruct H11 as (H11, Hsig).
            assert (rename_all_ctx_ns sig (inlined_ctx_f c im') |[ Econstr v c0 (apply_r_list sig l) e0 ]| =
                    (rename_all_ctx_ns sig (inlined_ctx_f (comp_ctx_f c (Econstr_c v c0 l Hole_c)) im') |[ e0 ]|)).
            rewrite (proj1 inlined_comp_ctx). rewrite (proj1 (rename_all_ctx_ns_comp_ctx _ _)). rewrite <- app_ctx_f_fuse.
            simpl. now auto.
            destruct (get_c v c1) eqn:gvc1.
            - (* dead post *) inv H6. split; [| split; [| split ]].
              + eapply gsr_clos_trans. eassumption.
                rewrite <- H12. unfold ce'. simpl. replace 1 with (1 + 0) by lia. eapply Trans_srw; [| eapply Refl_srw ].
                constructor. constructor.
                specialize (H10 v). rewrite gvc1 in H10. apply num_occur_app_ctx in H10; destructAll; pi0; auto.
              + intro. specialize (H10 v0). unfold ce'.
                apply num_occur_app_ctx in H10. destructAll.
                rewrite (proj1 inlined_comp_ctx) in H6.
                rewrite (proj1 (rename_all_ctx_ns_comp_ctx _ _)) in H6.
                apply num_occur_ec_comp_ctx in H6; destructAll.
                simpl in H14. inv H14. inv H21. simpl in H13.
                apply num_occur_app_ctx.
                exists x1, x0. split; auto. split; auto.
                unfold dec_census_list.
                rewrite <- combine_minus_census_list.
                rewrite gccombine_sub.
                rewrite H13.
                rewrite update_census_list_correct.
                rewrite apply_r_list_empty.
                unfold get_c. rewrite M.gempty. lia.
              + intro; intros. assert (H6' := H6).
                apply H11 in H6. destruct H6. split.
                intro; apply H6. unfold ce' in H14.
                apply bound_var_app_ctx in H14.
                apply bound_var_app_ctx. inv H14.
                left. rewrite (proj1 inlined_comp_ctx).
                rewrite (proj1 (rename_all_ctx_ns_comp_ctx _ _)). rewrite (proj1 bound_var_ctx_comp_ctx).
                left; auto. now right; auto.
                intros. destruct (var_dec f v); subst.
                * exfalso. apply H6; subst. apply bound_var_app_ctx.
                  left. rewrite (proj1 inlined_comp_ctx).
                  rewrite (proj1 (rename_all_ctx_ns_comp_ctx _ _)).
                  rewrite (proj1 bound_var_ctx_comp_ctx).
                  right. simpl. auto.
                * assert ( M.get f (M.set v (SVconstr c0 l) sub) = Some (SVfun t xs m) ).
                  rewrite M.gso; auto. apply H13 in H15.
                  eapply Disjoint_Included_l. 2: now apply H15.
                  unfold ce'. do 2 (rewrite bound_var_app_ctx).
                  rewrite (proj1 inlined_comp_ctx). rewrite (proj1 (rename_all_ctx_ns_comp_ctx _ _)).
                  rewrite (proj1 bound_var_ctx_comp_ctx). eauto with Ensembles_DB.
              + intro. intros. apply Hsig in H6.
                inv H6. left.
                apply num_occur_app_ctx in H13. destructAll; pi0.
                apply num_occur_app_ctx. exists 0, 0. repeat split; auto.
                repeat normalize_ctx. apply num_occur_ec_comp_ctx in H6.
                destructAll; pi0. auto.
                (* either y is v and it is dead OR it isn't and it is bound in c *)
                repeat normalize_ctx.
                apply bound_stem_comp_ctx_mut in H13. inv H13.
                right. auto. simpl in H6. inv H6.
                left. specialize (H10 y). rewrite gvc1 in H10.
                apply num_occur_app_ctx in H10.
                destructAll; pi0. apply num_occur_ec_comp_ctx in H6.
                destructAll; pi0.
                apply num_occur_app_ctx. eauto. inv H18.
            - (* live post *) inv H6.
              unfold ce'; rewrite H12.
              split; auto. split; auto. split; eauto.
              + intro. intros. assert (H6' := H6).
                apply H11 in H6. destruct H6.
                split; auto. intros.
                destruct (var_dec f v).
                * (* impossible, then v is inlined but bound *)
                  exfalso.
                  subst.
                  apply H11 in H6'.
                  destruct H6'.
                  apply H15.
                  rewrite (proj1 inlined_comp_ctx).
                  rewrite (proj1 (rename_all_ctx_ns_comp_ctx _ _)).
                  apply bound_var_app_ctx.
                  left.
                  apply bound_var_ctx_comp_ctx.
                  right. simpl. constructor.
                * assert ( M.get f (M.set v (SVconstr c0 l) sub) = Some (SVfun t xs m)).
                  rewrite M.gso; auto.
                  apply H13 in H15. auto.
              + intro. intros. assert (H6' := H6). apply Hsig in H6. inv H6.
                left. apply num_occur_app_ctx in H13. destructAll; pi0.
                repeat normalize_ctx. apply num_occur_ec_comp_ctx in H6. destructAll; pi0.
                simpl in H14. apply num_occur_app_ctx. exists 0, 0; split; auto.
                split; auto. eapply num_occur_n.
                constructor. eauto. inv H14; pi0. rewrite H14. auto.
                repeat normalize_ctx. apply bound_stem_comp_ctx_mut in H13.
                inv H13. right. auto. simpl in H6. inv H6.
                apply H5 in H6'. inv H6'. inv H13.
                specialize (H2 y). rewrite gvc in H2.
                assert (S n0 = 0). eapply (proj1 (num_occur_det _)); eauto.
                rewrite H8 in H14. auto. inv H13.
                exfalso. rewrite <- H8 in H0. apply ub_app_ctx_f in H0.
                destructAll. inv H15.
                specialize (H16 y). apply H16. split; auto.
                apply bound_stem_var. auto.
                simpl. constructor. inv H18. }
        * (* size *)
          eapply Nat.lt_le_trans.
          apply constr_sub_size.
          lia.
          (* cmap_view *)
        * apply cmap_view_constr; eauto.
        * (* inl_inv *)
          intro. intros. apply H4 in H9.
          destruct H9.
          split; auto.
          intros.
          destruct (var_dec f v).
          subst.
          rewrite M.gss in H11. inv H11.
          rewrite M.gso in H11; auto.
          eapply H10; eauto.
        * (* sig inv *)
          intro; intros. apply H5 in H9.
          destruct H9. split.
          simpl in H9. intro; apply H9.
          repeat normalize_ctx. rewrite <- app_ctx_f_fuse in H11.
          simpl in H11. auto. inv H10.
          left. repeat normalize_ctx.
          rewrite <- app_ctx_f_fuse. simpl. simpl in H11.
          auto. right. repeat normalize_ctx.
          apply bound_stem_comp_ctx_mut. auto.
    - (* case *)
      simpl in H6.
      destruct ( M.get (apply_r sig v) sub ) eqn:garvs; [destruct s|].
      + destruct (findtag l c0) eqn:ftlc0.
        * (* folded case *)
           assert (gsr_clos 1 ce (rename_all_ctx_ns sig (inlined_ctx_f c inl) |[ rename_all_ns sig e ]|)).
           { apply H3 in garvs. destructAll. unfold ce. repeat normalize_ctx. do 2 (rewrite <- app_ctx_f_fuse).
             replace 1 with (1 + 0) by lia. econstructor; [| eapply Refl_srw ]. constructor. simpl.
             eapply findtag_map in ftlc0. eapply find_tag_nth_findtag in ftlc0. destructAll.
             eapply Constr_case_s. eassumption. }
           assert (Hub' := gsr_clos_preserves_clos _ _ _ H0 H1 H7). destructAll.
           apply sig_inv_combine in H5. destruct H5 as (H5, H5c).
           assert (Hse := gsr_preserves_sig_dom _ _ _ _ H0 (closed_implies_Disjoint _ H1) H7 H5).
           assert (H_bv : Included _ (bound_var  (rename_all_ctx_ns sig (inlined_ctx_f c inl) |[ rename_all_ns sig e ]|)) (bound_var ce)).
           { unfold ce. do 2 (rewrite bound_var_app_ctx).
             apply Included_Union_compat. auto with Ensembles_DB.
             simpl. intro. intros. eapply Bound_Ecase with (c := c0).
             apply H10. apply findtag_In_patterns in ftlc0.
             eapply in_map with (f := (fun p : var * exp => let (k, e0) := p in (k, rename_all_ns sig e0))) in ftlc0. auto. }
           unfold incr_steps in H6. remember (contract sig (dec_census_case sig l c0 (dec_census_list sig [v] count)) e sub inl) as s.
           symmetry in Heqs. destruct s as [[[[? ?] ?] ?] ?]. inv H6. eapply IHn in Heqs; eauto.
           -- destructAll. split; eauto. rewrite Nat.add_comm. eapply gsr_clos_trans. eassumption. eassumption.
           -- unfold term_sub_inl_size in *. simpl in *.
              assert ( term_size e < term_size (Ecase v l)).
              { eapply case_size. apply findtag_In. eauto. }
              simpl in H6. lia.
           -- (* count for folded case *) apply c_count_fold_case; auto.
           -- (* inl for folded case *)
             intro. intros. apply H4 in H6.
             destruct H6. split.
             intro. apply H6. apply H_bv. now auto.
             intros. apply H10 in H11. eapply Disjoint_Included_l. apply H_bv. auto.
           -- (* sig inv for folded case *)
             intro. intros. split.
             apply H5 in H6. intro; apply H6.
             apply H_bv; auto. apply H5c in H6. inv H6; auto.
             left. apply num_occur_app_ctx in H10. destructAll; pi0.
             apply num_occur_app_ctx. exists 0, 0. split; auto. split; auto.
             simpl in H10. inv H10; pi0.
             assert (exists n, num_occur (rename_all_ns sig e) y n) by apply e_num_occur.
             destruct H11. assert (x0 <= 0). eapply num_occur_case_le. 2: apply H14.
             apply findtag_In in ftlc0.
             eapply in_map with (f := (fun p : var * exp => let (k, e0) := p in (k, rename_all_ns sig e0))) in ftlc0.
             now eauto. now eauto. apply Nat.le_0_r in H12; subst; auto. dec_vars. eassumption.
        * (* case not found, same as fun. contractcases_corresp with cl1 = nil and x = apply_r sig x*)
           remember (contractcases
                       (@pair (prod exp ctx_map) b_map
                              (@pair exp ctx_map (Ecase v l) sub) inl)
                       (fun (rm : r_map) (cm : c_map)
                            (es : prod (prod exp ctx_map) b_map)
                            (_ : lt (term_sub_inl_size es)
                                    (term_sub_inl_size
                                       (@pair (prod exp ctx_map) b_map
                                              (@pair exp ctx_map (Ecase v l) sub) inl))) =>
                          contract rm cm
                                   (@fst exp ctx_map (@fst (prod exp ctx_map) b_map es))
                                   (@snd exp ctx_map (@fst (prod exp ctx_map) b_map es))
                                   (@snd (prod exp ctx_map) b_map es)) sig count inl sub l
                       (@subcl_refl v l) (le_n (sub_inl_size sub inl))) as Hcc.
           destruct Hcc. destruct x. destruct p. destruct p. symmetry in HeqHcc.
           eapply contractcases_corresp with (x := apply_r sig v) (cl1 := nil) (c := c) in HeqHcc; eauto.
           2:{ intros. eapply IHn; eauto. unfold term_sub_inl_size in *. simpl in H7. simpl in *. lia. }
           inv H6. simpl in *. destructAll. split; auto.
      + (* fun *)
        remember (contractcases
                    (@pair (prod exp ctx_map) b_map
                           (@pair exp ctx_map (Ecase v l) sub) inl)
                    (fun (rm : r_map) (cm : c_map)
                         (es : prod (prod exp ctx_map) b_map)
                         (_ : lt (term_sub_inl_size es)
                                 (term_sub_inl_size
                                    (@pair (prod exp ctx_map) b_map
                                           (@pair exp ctx_map (Ecase v l) sub) inl))) =>
                       contract rm cm
                                (@fst exp ctx_map (@fst (prod exp ctx_map) b_map es))
                                (@snd exp ctx_map (@fst (prod exp ctx_map) b_map es))
                                (@snd (prod exp ctx_map) b_map es)) sig count inl sub l
                    (@subcl_refl v l) (le_n (sub_inl_size sub inl))) as Hcc.
        destruct Hcc. destruct x. destruct p. destruct p.
        symmetry in HeqHcc. eapply contractcases_corresp with (x := apply_r sig v) (cl1 := nil) (c := c) in HeqHcc; eauto.
        2:{ intros. eapply IHn; eauto. unfold term_sub_inl_size in *. simpl in H7. simpl in *. lia. }
        inv H6. simpl in *. destructAll. split; auto.
      + (* None *)
        remember (contractcases
                    (@pair (prod exp ctx_map) b_map
                           (@pair exp ctx_map (Ecase v l) sub) inl)
                    (fun (rm : r_map) (cm : c_map)
                         (es : prod (prod exp ctx_map) b_map)
                         (_ : lt (term_sub_inl_size es)
                                 (term_sub_inl_size
                                    (@pair (prod exp ctx_map) b_map
                                           (@pair exp ctx_map (Ecase v l) sub) inl))) =>
                       contract rm cm
                                (@fst exp ctx_map (@fst (prod exp ctx_map) b_map es))
                                (@snd exp ctx_map (@fst (prod exp ctx_map) b_map es))
                                (@snd (prod exp ctx_map) b_map es)) sig count inl sub l
                    (@subcl_refl v l) (le_n (sub_inl_size sub inl))) as Hcc.
        destruct Hcc. destruct x. destruct p. destruct p. symmetry in HeqHcc.
        eapply contractcases_corresp with (x := apply_r sig v) (cl1 := nil) (c := c) in HeqHcc; eauto.
        2:{ intros. eapply IHn; eauto. unfold term_sub_inl_size in *. simpl in H7. simpl in *. lia. }
        inv H6. simpl in *. destructAll. split; auto.
    - (* proj *)
      destruct (get_c v count) eqn: gvc.
      + (* dead v pre *)
        simpl in H6.
        assert (gsr_clos 1 ce (rename_all_ctx_ns sig (inlined_ctx_f c inl) |[ rename_all_ns sig e ]|)).
        { replace 1 with (1 + 0) by lia. eapply Trans_srw; [| now constructor ]. constructor.
          simpl. apply Proj_dead_s. specialize (H2 v). rewrite gvc in H2.
          apply num_occur_app_ctx in H2. destructAll; pi0. inv H7; pi0. dec_vars. auto. }
        assert (Hub := gsr_clos_preserves_clos _ _ _ H0 H1 H7).
        destruct Hub. apply sig_inv_combine in H5.
        destruct H5 as (H5, H5cod).
        assert (Hse := gsr_preserves_sig_dom _ _ _ _ H0 (closed_implies_Disjoint _ H1) H7 H5).
        unfold incr_steps in H6. remember (contract sig (dec_census_list sig [v0] count) e sub inl) as s. destruct s as [[[[? ?] ?] ?] ?].
        inv H6. symmetry in Heqs. apply IHn with (c := c) in Heqs; auto.
        * destructAll. split; eauto. rewrite Nat.add_comm. eapply gsr_clos_trans. eassumption. eassumption.
        * unfold term_sub_inl_size in *. simpl. simpl in H. lia.
        * intro. specialize (H2 v1). apply num_occur_app_ctx in H2.
          destructAll. simpl in H6. inv H6. eapply num_occur_n.
          apply num_occur_app_ctx. exists x, n2. split; auto.
          unfold dec_census_list.
          rewrite <- combine_minus_census_list, gccombine_sub.
          rewrite H10. rewrite update_census_list_correct.
          rewrite apply_r_list_empty. unfold get_c. rewrite M.gempty.
          simpl. lia.
        * eapply inl_inv_mon. 2: now apply H4.
          unfold ce. do 2 (rewrite bound_var_app_ctx).
          simpl. normalize_bound_var. now sets.
        * eapply sig_inv_full_dead_l. rewrite <- inv_app_Eproj.
          simpl in *. apply sig_inv_combine. split; eauto.
      + { simpl in H6.
          (* Factoring three same subcases *)
          assert (Hsame : (let (x, bp) := contract sig count e sub inl in
                           (let
                               (p, im') as x0
                               return (b_map_le_i inl (snd x0) -> contractT inl) := x in
                             let (p0, count') := p in
                             let (e', steps) := p0 in
                             fun bp0 : b_map_le_i inl im' =>
                               match get_c v count' with
                               | 0 =>
                                 existT
                                   (fun esir : exp * nat * c_map * b_map =>
                                      b_map_le_i inl (snd esir))
                                   (e', steps + 1, dec_census_list sig [v0] count', im') bp0
                               | S _ =>
                                 existT
                                   (fun esir : exp * nat * c_map * b_map =>
                                      b_map_le_i inl (snd esir))
                                   (Eproj v c0 n0 (apply_r sig v0) e', steps, count', im') bp0
                               end) bp) =
                          existT
                            (fun esir : exp * nat * c_map * b_map => b_map_le_i inl (snd esir))
                            (e', steps, count', im') BP  ->
                          gsr_clos steps ce ce' /\  c_count ce' count' /\ inl_inv im' sub ce' /\  sig_inv_codom sig (rename_all_ctx_ns sig (inlined_ctx_f c im')) e').
          { clear H6. intros H6.
            assert (rename_all_ctx_ns sig (inlined_ctx_f c inl) |[ rename_all_ns sig (Eproj v c0 n0 v0 e) ]| =
                                                                                                             rename_all_ctx_ns sig (inlined_ctx_f (comp_ctx_f c (Eproj_c v c0 n0 v0 Hole_c)) inl) |[ rename_all_ns sig e ]|) by ctx_inl_push.
            remember (contract sig count e sub inl) as s. destruct s. destruct x. destruct p. destruct p.
            symmetry in Heqs. unfold ce in *; rewrite H7 in *. eapply IHn in Heqs; eauto. destructAll.
            destruct (get_c v c1) eqn:gvc2.
            { (* dead v post *)
              inv H6. split; [| split; [| split ]].
              - eapply gsr_clos_trans. eassumption.
                unfold ce'. repeat normalize_ctx. rewrite <- app_ctx_f_fuse.
                replace 1 with (1 + 0) by lia. econstructor; [| now constructor ].
                simpl. constructor. eapply Proj_dead_s.
                specialize (H9 v). rewrite gvc2 in H9.
                apply num_occur_app_ctx in H9; destructAll; pi0.
                apply num_occur_ec_comp_ctx in H6; destructAll; pi0. eauto.
          - intro. specialize (H9 v1). apply num_occur_app_ctx in H9. destructAll.
                repeat normalize_ctx. apply num_occur_ec_comp_ctx in H6. destructAll. simpl in H13. inv H13.
                eapply num_occur_n. apply num_occur_app_ctx. exists x1, x0. split; auto.
                inv H21. unfold dec_census_list. rewrite <- combine_minus_census_list.
                rewrite gccombine_sub. rewrite H12. rewrite update_census_list_correct.
                rewrite apply_r_list_empty. unfold get_c. rewrite M.gempty. simpl. lia.
              - eapply inl_inv_mon. 2: apply H10. unfold ce'.
                do 2 (rewrite bound_var_app_ctx). repeat normalize_ctx.
                simpl. rewrite (proj1 bound_var_ctx_comp_ctx). now sets.
              - intro. intros. destruct (var_dec y v).
                (* y = v *)
                + subst. left. specialize (H9 v). rewrite gvc2 in H9.
                  apply num_occur_app_ctx in H9. destructAll; pi0.
                  repeat normalize_ctx. apply num_occur_ec_comp_ctx in H9; destructAll; pi0.
                  eapply num_occur_app_ctx. exists 0, 0; split; auto.
                + (* y <> v *)
                  apply H11 in H6. inv H6.
                  left. apply num_occur_app_ctx in H12; destructAll; pi0.
                  repeat normalize_ctx.
                  apply num_occur_ec_comp_ctx in H6; destructAll; pi0.
                  eapply num_occur_app_ctx. exists 0, 0; split; auto.
                  right. repeat normalize_ctx. apply bound_stem_comp_ctx_mut in H12.
                  inv H12. auto. exfalso. inv H6. auto. inv H18. }
            { inv H6.
              assert ((rename_all_ctx_ns sig (inlined_ctx_f (comp_ctx_f c (Eproj_c v c0 n0 v0 Hole_c)) im') |[ e0 ]|) =
                       rename_all_ctx_ns sig (inlined_ctx_f c im') |[ Eproj v c0 n0 (apply_r sig v0) e0 ]|) by ctx_inl_push.
              unfold ce';  rewrite <- H6.
              split; auto. split; auto. split; auto.
              (* sig_inv_codom push proj *)
              intro. intros. destruct (var_dec y v).
              (* y = v *)
              - subst. apply H5 in H12. inv H12. inv H14.
                (** by no zombie *)
                left. rewrite <- H6. eapply shrink_no_zombie. apply H8.
                rewrite H7 in H12. auto.
                (** imposible due to unique binding *)
                exfalso.
                apply ub_app_ctx_f in H0. destructAll.
                repeat normalize_ctx. apply ub_comp_ctx_f in H0.
                destructAll. inv H17. specialize (H18 v). apply H18.
                split. apply bound_stem_var. auto.
                simpl. constructor.
              - (* y <> v *)
                apply H11 in H12. inv H12.
                rewrite H6 in H13. auto. repeat normalize_ctx.
                apply bound_stem_comp_ctx_mut in H13. inv H13.
                auto. simpl in H12. inv H12. exfalso. auto. inv H19.
            }
            unfold term_sub_inl_size in *. simpl. simpl in H. lia.
            apply cmap_view_proj; auto. repeat normalize_ctx.
            apply sig_inv_full_push. simpl. simpl in H5. auto. }


          destruct (M.get (apply_r sig v0) sub) eqn:garv0s; [destruct s|].
          + (* constr *)
            destruct (nthN l n0) eqn:n0thl.
            * (* constant folding *)
              assert (Hgvs : M.get v sig = None).
              { destruct (M.get v sig) eqn:gvs.
                apply H5 in gvs. inv gvs. exfalso.
                apply H7. apply bound_var_app_ctx. right; simpl; auto. eauto. }
              assert (Hbv : ~ bound_var_ctx (rename_all_ctx_ns sig (inlined_ctx_f c inl)) v).
              { unfold ce in H0. apply ub_app_ctx_f in H0. intro. destructAll. inv H9.
                specialize (H10 v).
                apply H10. split; simpl; auto. }
              apply H3 in garv0s. destructAll.
              assert (H_rn_ctx:
                        (rename_all_ctx_ns (M.set v (apply_r sig v1) sig)
                                           (inlined_ctx_f (comp_ctx_f x (Econstr_c (apply_r sig v0) c1 l x0)) inl) =
                         (rename_all_ctx_ns sig
                                            (inlined_ctx_f (comp_ctx_f x (Econstr_c (apply_r sig v0) c1 l x0)) inl)))).
              { apply eq_P_rename_all_ctx_ns. intro; intro. destruct (var_dec x1 v).
                - subst. exfalso. apply H7. eapply not_occur_rename_ctx_not_dom with (sig := sig).
                  intro. inv H8. rewrite Hgvs in H9; inv H9.
                  assert (~ occurs_free_ctx (rename_all_ctx_ns sig
                                                           (inlined_ctx_f
                                                              (comp_ctx_f x (Econstr_c (apply_r sig v0) c1 l x0)) inl)) v).
                  intro. apply closed_app_ctx in H1. apply H1 in H8. inv H8.
                  apply not_free_dead_or_bound_ctx in H8. inv H8; auto. exfalso; auto.
                - rewrite M.gso; auto.
              }
              assert (Hee : rename_all_ns (M.set v (apply_r sig v1) (M.empty var)) (rename_all_ns sig e) =
                        ( rename_all_ns (M.set v (apply_r sig v1) sig) e )).
              { assert (Decidable (Range_map sig)) by apply Decidable_Range_map.
                assert (sig_inv_dom sig e).
                { intro. intros. apply H5 in H8; destructAll.
                  intro; apply H8. apply bound_var_app_ctx.
                  right. simpl; normalize_bound_var.
                  left. eapply bound_var_rename_all_ns in H10. eauto. }
                inv H7. specialize (Dec v). inv Dec.
                + (* then v doesn't occur *)
                  inv H7. apply H5 in H9. inv H9.
                  inv H10.
                  * (* by eq_P_rename_all_ns *)
                    assert ( rename_all_ns (M.set v (apply_r sig v1) sig) e =  rename_all_ns  sig e).
                    {
                      apply eq_P_rename_all_ns.
                      intro. intros. destruct (var_dec x2 v).
                      subst.
                      exfalso. apply H10.
                      apply num_occur_app_ctx in H9; destructAll; pi0.
                      simpl in H11. inv H11; pi0.
                      eapply not_occur_rename_not_dom; eauto.
                      intro. inv H12. rewrite Hgvs in H13. inv H13.
                      rewrite M.gso; auto.
                    }
                    rewrite H10.

                    assert (rename_all_ns (M.set v (apply_r sig v1) (M.empty var)) (rename_all_ns sig e)  = rename_all_ns (M.empty var) (rename_all_ns sig e)).
                    { unfold rename.
                      apply eq_P_rename_all_ns.
                      intro. intros. destruct (var_dec x2 v).
                      subst.
                      exfalso. apply H11. apply num_occur_app_ctx in H9.
                      destructAll; pi0.
                      simpl in H12; inv H12; pi0; auto.
                      rewrite M.gso; auto.
                    }
                    rewrite H11.
                    rewrite <- (proj1 rename_all_ns_empty).
                    reflexivity.
                  * (* Impossible due to unique_bindings *)
                    apply ub_app_ctx_f in H0.
                    destructAll.
                    inv H11. specialize (H12 v).
                    exfalso.
                    apply H12.
                    apply bound_stem_var in H9.
                    split; simpl; repeat normalize_ctx; auto.
                + (* then rename v (rename_all e) = rename_all+v e *)
                  rewrite one_rename_all_ns. reflexivity. eassumption.
                  intro. inv H9. unfold var in *. rewrite H10 in Hgvs. inv Hgvs.
              }
              assert (gsr_clos (1 + 0) (rename_all_ctx_ns sig
                                                          (inlined_ctx_f (comp_ctx_f x (Econstr_c (apply_r sig v0) c1 l x0))
                                                                         inl) |[ rename_all_ns sig (Eproj v c0 n0 v0 e) ]|)
                               (rename_all_ctx_ns (M.set v (apply_r sig v1) sig)
                                                  (inlined_ctx_f (comp_ctx_f x (Econstr_c (apply_r sig v0) c1 l x0)) inl)
                               |[ rename_all_ns (M.set v (apply_r sig v1) sig) e ]|)).
              { eapply Trans_srw.
                - simpl. rewrite (proj1 inlined_comp_ctx). simpl.
                  rewrite (proj1 (rename_all_ctx_ns_comp_ctx _ _)).
                  rewrite <- app_ctx_f_fuse.
                  simpl. econstructor. apply Constr_proj_s.
                  unfold apply_r_list. apply nthN_map. eauto.
                - (* 2 parts : *)
                  destruct (M.get v sig) eqn:gvs.
                  inv Hgvs.
                  (*) context is unchanged by extra sig *)
                  rewrite H_rn_ctx.
                  repeat normalize_ctx. simpl.
                  rewrite <- app_ctx_f_fuse.
                  (* ) rename v (rename_all e) = rename_all+v e by  *)
                  rewrite <- Hee. apply Refl_srw. }
              assert (Hub' := gsr_clos_preserves_clos _ _ _ H0 H1 H7).
              destructAll. unfold incr_steps in *.
              remember (contract (M.set v (apply_r sig v1) sig) (M.set v 0 (M.set (apply_r sig v1) (S (n1 + get_c (apply_r sig v1) count))
                                                                                  (M.set (apply_r sig v0)
                                                                                         (get_c (apply_r sig v0) count - 1) count))) e sub inl) as s.
              destruct s as [[[[? ?] ?] ?] ?]. inv H6. symmetry in Heqs.
              eapply IHn in Heqs; eauto.
              - assert (rename_all_ctx_ns (M.set v (apply_r sig v1) sig)
                                        (inlined_ctx_f
                                           (comp_ctx_f x (Econstr_c (apply_r sig v0) c1 l x0)) im')  =
                      (rename_all_ctx_ns sig
                                         (inlined_ctx_f
                                            (comp_ctx_f x (Econstr_c (apply_r sig v0) c1 l x0)) im'))).
                { apply eq_P_rename_all_ctx_ns. intro; intro.
                  destruct (var_dec x1 v).
                  - subst. exfalso. apply H6.
                    (* num occur e v <= num_occur (rename sig e) v, ~ bound occur and not occurs free so dead (also bound_var_ctx_inlined_antimon from inl to im' *)
                    assert (~ occurs_free_ctx  (rename_all_ctx_ns sig
                                                            (inlined_ctx_f
                                                               (comp_ctx_f x (Econstr_c (apply_r sig v0) c1 l x0)) inl)) v).
                    { apply closed_app_ctx in H1.
                      intro. apply H1 in H10. inv H10. }

                    apply not_free_dead_or_bound_ctx in H10. inv H10.
                    + apply not_occur_rename_ctx_not_dom in H11.
                      eapply dead_occur_ec_le_antimon; eauto.
                      apply b_map_le_c. auto.
                      intro. inv H10. apply H5 in H12.
                      inv H12. apply H10.
                      apply bound_var_app_ctx. right. simpl; auto.
                    + exfalso.
                      apply ub_app_ctx_f in H0.
                      destructAll.
                      inv H16. specialize (H17 v).
                      apply H17. split; auto. simpl. constructor.
                  - rewrite M.gso by auto; auto. }
                rewrite H6 in *. destruct Heqs as (H6', H11).
                destruct H11 as (H11, H12). destruct H12 as (H12, Hsigc). destructAll.
                split; auto.
                -- rewrite Nat.add_comm. eapply gsr_clos_trans. eassumption. eassumption.
                -- split. now auto. split. now auto.
                   (* returned sig_inv_codom *)
                   intro. intros.
                   assert (x1 <> v).
                   intro; subst.
                   rewrite H10 in Hgvs. inv Hgvs.
                   assert (M.get x1 (M.set v (apply_r sig v1) sig) = Some y).
                   rewrite M.gso; auto. apply Hsigc in H14. auto.
              - unfold term_sub_inl_size in *.
                simpl in *; lia.
              -  (* TODO: redo using rename_all_set_x *)
                rewrite H_rn_ctx. rewrite <- Hee.
                intro. assert (H2' := H2). specialize (H2 v2).
                apply num_occur_app_ctx in H2; destructAll.
                inv H6.

                assert (Hvv1 : v <> apply_r sig v1).
                { intro. unfold apply_r in H6.
                  destruct (@PTree.get _ v1 sig) eqn:gv1s.
                  subst. apply H5 in gv1s. destructAll.
                  inv H11.
                  specialize (H2' v3).
                  rewrite gvc in H2'. assert (S n1 = 0).
                  eapply (proj1 (num_occur_det _)); eauto. now inv H11.
                  apply ub_app_ctx_f in H0. destructAll.
                  inv H13.
                  specialize (H14 v3).
                  apply H14. split.
                  apply bound_stem_var. auto.
                  simpl. constructor.
                  subst.
                  assert (~ bound_var_ctx
                            (rename_all_ctx_ns sig
                                               (inlined_ctx_f x inl)) (apply_r sig v1)).
                  intro. apply Hbv. repeat normalize_ctx.
                  apply bound_var_ctx_comp_ctx. left.
                  unfold apply_r in H6. rewrite gv1s in H6. auto.
                  unfold ce in H1. repeat normalize_ctx.
                  rewrite <- app_ctx_f_fuse in H1.
                  assert (occurs_free (rename_all_ctx_ns sig
                                                         (inlined_ctx_f (Econstr_c (apply_r sig v0) c1 l x0) inl)
                                      |[ rename_all_ns sig (Eproj v1 c0 n0 v0 e) ]|) (apply_r sig v1)).
                  simpl. constructor.
                  apply nthN_In in n0thl.
                  apply apply_r_list_In. auto.
                  eapply occurs_free_ctx_not_bound in H11. 2: apply H6.
                  apply H1 in H11. inv H11. }

                assert (Hnv := H2' v). assert (Hnv1 := H2' (apply_r sig v1)).
                apply num_occur_app_ctx in Hnv. destruct Hnv. destruct H6.
                destruct H6 as (Hnvc, (Hnve, Hnv_c)).
                assert (x2 = 0).
                { eapply closed_not_occurs_in_context in Hbv.
                  eapply (num_occur_ec_det); eauto.
                  apply closed_app_ctx in H1. auto. }
                subst. inv Hnve. rename H18 into Hnve.
                apply num_occur_app_ctx in Hnv1. destruct Hnv1. destruct H6.
                destruct H6 as (Hnv1c, (Hnv1e, Hnv1_c)).
                inv Hnv1e. rename H18 into Hnv1e.
                assert (Hrm := num_occur_rename_mut).
                specialize (Hrm _ _ Hvv1). inv Hrm. clear H11.
                specialize (H6 _ _ _ H17 Hnv1e). (* ? *) destruct H6 as (Hnev_post, Hnev1_post).
                destruct (var_dec v2 v).
                { (* v2 = v *)
                  subst. simpl. rewrite gdss.
                  apply num_occur_app_ctx. exists 0, 0.
                  split; auto. }
                rewrite gdso; auto.
                destruct (var_dec v2 (apply_r sig v1)).
                (* v2 = (apply_r sig v1) *)
                { apply num_occur_app_ctx.
                  exists x2, (n4+n5). rewrite e0. split. now auto. split. now auto.
                  rewrite gdss. rewrite Hnv1_c. rewrite gvc in Hnv_c.
                  assert (num_occur_list [apply_r sig v0] v = 0). (* by UB *)
                  simpl. destruct (term_util.var_dec v (apply_r sig v0)); auto.
                  subst. exfalso. apply ub_app_ctx_f in H0; destructAll. inv H11.
                  specialize (H12 (apply_r sig v0)). apply H12. split.
                  - repeat normalize_ctx. apply bound_var_ctx_comp_ctx. right. simpl. constructor; auto.
                  - constructor.
                  - assert (num_occur_list [apply_r sig v0] (apply_r sig v1) = 0).
                    { simpl.  destruct (term_util.var_dec (apply_r sig v1) (apply_r sig v0)); auto.
                      subst. exfalso.
                      assert (~ bound_var_ctx (rename_all_ctx_ns sig (inlined_ctx_f x inl)) (apply_r sig v0)) (* by UB *).
                      { intro. apply ub_app_ctx_f in H0. destructAll.
                        repeat normalize_ctx. apply ub_comp_ctx_f in H0. destructAll. rewrite e1 in *.
                        inv H15. specialize (H16 (apply_r sig v0)). apply H16. split; auto. simpl. constructor. }
                      unfold ce in H1. repeat normalize_ctx.
                      rewrite <- app_ctx_f_fuse in H1.
                      assert (occurs_free (rename_all_ctx_ns sig
                                                             (inlined_ctx_f (Econstr_c (apply_r sig v0) c1 l x0) inl)
                                          |[ rename_all_ns sig (Eproj v c0 n0 v0 e) ]|) (apply_r sig v0)).
                      { simpl. constructor. rewrite <- e1. apply apply_r_list_In. apply nthN_In in n0thl. auto. }
                      eapply occurs_free_ctx_not_bound in H12.
                      2: eassumption. apply H1 in H12. inv H12. }
                    unfold var in *. rewrite H6 in *. rewrite H11. lia. }

                (* v2 <> v <> (apply_r sig v1) *)
                rewrite gdso; auto.
                apply num_occur_app_ctx.
                exists x1, n3. split. now auto. split.
                assert (exists n, num_occur
                                    (rename_all_ns (M.set v (apply_r sig v1) (M.empty var))
                                                   (rename_all_ns sig e)) v2  n) by apply e_num_occur. destruct H6.
                assert (n3 = x3).
                { eapply num_occur_sig_unaffected; eauto.
                  intro. inv H11. rewrite M.gso in H12 by auto.
                  rewrite M.gempty in H12. now inv H12.
                  intro. inv H11. destruct (var_dec x4 v).
                  - subst. rewrite M.gss in H12. inv H12; auto.
                  - rewrite M.gso in H12. rewrite M.gempty in H12. inv H12. auto. }
                subst. eassumption.
                rewrite get_c_minus. simpl in H10. rewrite H10.
                destruct (term_util.var_dec v2 (apply_r sig v0)).
                subst. rewrite gdss. lia.
                rewrite gdso by auto. rewrite gdempty. lia.
              - (* inl_inv *)
                intro. intros.
                apply H4 in H6. unfold ce in H6.
                destruct H6.
                split.
                ** intro; apply H6.
                   apply bound_var_app_ctx in H11. inv H11.
                   rewrite <- (proj1 (bound_var_ctx_rename_all_ns _ )) in H12.
                   apply bound_var_app_ctx. left.
                   rewrite <- (proj1 (bound_var_ctx_rename_all_ns _ )). auto.
                   apply bound_var_app_ctx. right.
                   apply bound_var_rename_all_ns. apply bound_var_rename_all_ns in H12. eauto.
                ** intros. apply H10 in H11. eapply Disjoint_Included_l.
                   2: now apply H11.
                   do 2 rewrite bound_var_app_ctx.
                  do 2 (rewrite <- (proj1 (bound_var_ctx_rename_all_ns _ ))).
                  do 2 (rewrite <- (bound_var_rename_all_ns)).
                  normalize_bound_var. now sets.
              - (* sig_inv *)
                intro. intros. destruct (var_dec x1 v).
                -- subst. rewrite M.gss in H6. inv H6.
                   split.
                   ++ rewrite H_rn_ctx. intro.
                      apply ub_app_ctx_f in H0. destructAll.
                      apply bound_var_app_ctx in H6. inv H6. now eauto.
                      inv H10.
                      rewrite <- !bound_var_rename_all_ns in H12. eapply H14.
                      eapply bound_var_rename_all_ns in H12. eassumption.
                   ++ (* apply_r sig v1  has to be bound in x since ce is closed by occurs_free_app_bound_stem *)
                     right. repeat normalize_ctx. apply bound_stem_comp_ctx_mut. left.
                     eapply occurs_free_app_bound_stem.
                     2:{ intro. rewrite <- app_ctx_f_fuse in H9. apply H9 in H6. inv H6. }
                     simpl. constructor. apply nthN_In in n0thl.
                     revert n0thl. apply apply_r_list_push.
                -- rewrite M.gso in H6 by auto. apply H5 in H6. destruct H6. split.
                   ++ intro; apply H6. apply bound_var_app_ctx.
                      apply bound_var_app_ctx in H11. inv H11.
                      apply bound_var_ctx_rename_all_ns in H12.
                      left. apply bound_var_ctx_rename_all_ns. auto.
                      right. simpl. constructor.
                      apply bound_var_rename_all_ns in H12.
                      apply bound_var_rename_all_ns. auto.
                   ++ inv H10.
                      ** (* y cannot be (apply_r sig v1) because the latter occurs in l *)
                        rewrite H_rn_ctx. left.
                        apply num_occur_app_ctx in H11. destructAll; pi0.
                        eapply num_occur_app_ctx. exists 0, 0.
                        split; auto. split; auto.
                        inv H11; pi0.
                        assert (y <> apply_r sig v1).
                        { intro. subst. repeat normalize_ctx.
                          apply num_occur_ec_comp_ctx in H10.
                          destructAll; pi0.
                          simpl in H12. inv H12; pi0.
                          apply not_occur_list_not_in in H12.
                          apply nthN_In in n0thl.
                          apply H12. apply in_map. auto. }
                        dec_vars. simpl.
                        apply num_occur_rename_all_ns_dead_set; auto.
                      ** apply bound_stem_ctx_rename_all_ns in H11.
                         right. apply bound_stem_ctx_rename_all_ns. auto.
          * eapply Hsame. eassumption.
      + (* fun *) eapply Hsame. eassumption.
      + (* none *) eapply Hsame. eassumption. }
    - (* letapp *)
      (* factoring out common case *)
      assert (Hsame : (let (x0, bp) as k return (k = contract sig count e sub inl -> contractT inl) :=
                           contract sig count e sub inl in
                       (let
                           (p, im') as x1
                           return
                           (forall bp0 : b_map_le_i inl (snd x1),
                               existT
                                 (fun esir : exp * nat * c_map * b_map =>
                                    b_map_le_i inl (snd esir)) x1 bp0 =
                               contract sig count e sub inl ->
                               contractT inl) := x0 in
                         let
                           (p0, count') as p0
                           return
                           (forall bp0 : b_map_le_i inl (snd (p0, im')),
                               existT
                                 (fun esir : exp * nat * c_map * b_map =>
                                    b_map_le_i inl (snd esir)) (p0, im') bp0 =
                               contract sig count e sub inl ->
                               contractT inl) := p in
                         let
                           (e', steps) as p1
                           return
                           (forall bp0 : b_map_le_i inl (snd (p1, count', im')),
                               existT
                                 (fun esir : exp * nat * c_map * b_map =>
                                    b_map_le_i inl (snd esir)) (p1, count', im') bp0 =
                               contract sig count e sub inl ->
                               contractT inl) := p0 in
                         fun (bp0 : b_map_le_i inl (snd (e', steps, count', im')))
                             (_ : existT
                                    (fun esir : exp * nat * c_map * b_map =>
                                       b_map_le_i inl (snd esir)) (e', steps, count', im')
                                    bp0 = contract sig count e sub inl) =>
                           existT
                             (fun esir : exp * nat * c_map * b_map =>
                                b_map_le_i inl (snd esir))
                             (Eletapp v (apply_r sig v0) f (apply_r_list sig l) e',
                              steps, count', im') bp0) bp) eq_refl =
                      existT
                        (fun esir : exp * nat * c_map * b_map =>
                           b_map_le_i inl (snd esir)) (e', steps, count', im') BP ->
                      gsr_clos steps ce ce' /\  c_count ce' count' /\ inl_inv im' sub ce' /\  sig_inv_codom sig (rename_all_ctx_ns sig (inlined_ctx_f c im')) e').
      { clear H6; intros H6.
        assert (Heqc1 : rename_all_ctx_ns sig (inlined_ctx_f c inl) |[ rename_all_ns sig (Eletapp v v0 f l e) ]| =
                                                                                                                 rename_all_ctx_ns sig (inlined_ctx_f (comp_ctx_f c (Eletapp_c v v0 f l Hole_c)) inl) |[ rename_all_ns sig e ]|) by ctx_inl_push.
        unfold ce in *. rewrite Heqc1 in *.
        remember (contract sig count e sub inl) as s. destruct s as [[[[ ? ? ] ? ] ? ] ? ].
        symmetry in Heqs. eapply IHn in Heqs; eauto. destructAll. inv H6.
        assert (Heqc2 : (rename_all_ctx_ns sig (inlined_ctx_f (comp_ctx_f c (Eletapp_c v v0 f l Hole_c)) im') |[ e0 ]|) =
                        rename_all_ctx_ns sig (inlined_ctx_f c im') |[ Eletapp v (apply_r sig v0) f (apply_r_list sig l) e0 ]|) by ctx_inl_push.
        unfold ce'. rewrite <- Heqc2.
        split; auto. split; auto. split; auto.
        (* sig_inv_codom push proj *)
        - intro. intros. destruct (var_dec y v).
          (* y = v *)
          +  subst. apply H5 in H6. inv H6. inv H12.
             (** by no zombie *)
             left. rewrite <- Heqc2. eapply shrink_no_zombie. eassumption.
             rewrite Heqc1 in H6. now auto.
             (** imposible due to unique binding *)
             exfalso.
             apply ub_app_ctx_f in H0. destructAll.
             repeat normalize_ctx. apply ub_comp_ctx_f in H0.
             destructAll. eapply H15. constructor. eapply bound_stem_var. eassumption.
             rewrite <- (proj1 (bound_var_ctx_rename_all_ns _ )). simpl. normalize_bound_var_ctx. eauto.
          + apply H10 in H6. inv H6.
            rewrite Heqc2 in H11. auto. repeat normalize_ctx.
            apply bound_stem_comp_ctx_mut in H11. inv H11.
            auto. simpl in H6. inv H6. exfalso. now auto. inv H17.
        - unfold term_sub_inl_size in *. simpl. simpl in H. lia.
        - apply cmap_view_letapp; auto.
        - repeat normalize_ctx. apply sig_inv_full_push. simpl. simpl in H5. auto. }

      destruct (get_c (apply_r sig v0) count) as [| [|] ] eqn:Hgetc.
      + (* 0 *) eapply Hsame. eassumption.
      + destruct (sub ! (apply_r sig v0)) as [[|] | ] eqn:Hsub.
        * (* f is Vconstr *) eapply Hsame; eassumption.
        * (* f in Vfun *)
          destruct ((f0 =? f)%positive && (Datatypes.length l =? Datatypes.length l0) && negb (get_b (apply_r sig v0) inl)) eqn:Hel.
          { (* function inlining *)

            apply andb_true_iff in Hel. destruct Hel as (Hel123, Hel4).
            apply andb_true_iff in Hel123. destruct Hel123 as (Hel12, Hel3).
            eapply Peqb_true_eq in Hel12. apply Nat.eqb_eq in Hel3. subst.

            assert (Hinbv : occurs_free (rename_all_ns sig (Eletapp v v0 f l e)) \subset
                            bound_stem_ctx (rename_all_ctx_ns sig (inlined_ctx_f c inl))).
            { intros x Hin. eapply occurs_free_app_bound_stem. eassumption. intros Hin'. eapply H1 in Hin'. inv Hin'. }

            assert (Hsub' := Hsub). apply H3 in Hsub. destructAll. simpl in ce. eapply negb_true_iff in Hel4.

            assert (Hd_bv : Disjoint _ (bound_var ce) (Dom_map sig)).
            { constructor. intros z Hand. inv Hand. destruct H8 as [y Hin]. eapply H5 in Hin.
              inv Hin; eauto. }
            assert (Hd_bv' : Disjoint _ (apply_r sig v0 |: [set v] :|: FromList l0) (Dom_map sig)).
            { eapply Disjoint_Included_l; [| eassumption ].
              unfold ce. rewrite !bound_var_app_ctx. rewrite <- (proj1 (bound_var_ctx_rename_all_ns _)). repeat normalize_bound_var.
              rewrite (proj1 inlined_comp_ctx). simpl. rewrite inlined_fundefs_append. simpl. rewrite Hel4.
              rewrite (proj1 bound_var_ctx_comp_ctx). normalize_bound_var_ctx.
              erewrite fundefs_append_bound_vars; [| reflexivity ]. normalize_bound_var. xsets. }

            assert (Hnin : Disjoint _ [set v] (* |: FromList l0) *) (apply_r sig v0 |: FromList (apply_r_list sig l))).
            { eapply ub_app_ctx_f in H0. destructAll. constructor. intros z Hc. inv Hc. inv H9.
              - eapply H8. constructor. eapply bound_stem_var. eapply Hinbv.
                simpl. normalize_occurs_free. inv H10; eauto. normalize_bound_var. sets. }

            (* assert (Hnin' : Disjoint _ [set (apply_r sig v0)] (FromList (apply_r_list sig l))). *)
            (* { eapply ub_app_ctx_f in H0. destructAll. constructor. intros z Hc. inv Hc. inv H9.  *)
            (*   eapply H8. constructor. eapply bound_stem_var. eapply Hinbv. *)
            (*   simpl. normalize_occurs_free. do 2 left. reflexivity. normalize_bound_var. inv H10; eauto. normalize_bound_var. sets. } *)

            assert (Hdisu :  Disjoint _ (v |: FromList l0)
                                      ((apply_r sig v0) |: bound_var_fundefs (inlined_fundefs_f x1 inl) :|: bound_var_fundefs (inlined_fundefs_f x2 inl) :|:
                                       bound_var_ctx (inlined_ctx_f x inl) :|: bound_var_ctx (inlined_ctx_f x0 inl) :|: bound_var e0)  /\ NoDup l0).
            { eapply ub_app_ctx_f in H0. destructAll. repeat normalize_ctx.
              simpl in *. rewrite inlined_fundefs_append in *. simpl in *. rewrite Hel4 in *.
              eapply ub_comp_ctx_f in H0. destructAll. inv H9. rewrite rename_all_ns_fundefs_append in *.
              simpl in H14. eapply fundefs_append_unique_bindings_l in H14; [| reflexivity ]. destructAll.
              repeat normalize_bound_var_in_ctx. inv H11. rewrite <- !Union_assoc. split; [| eassumption ]. eapply Union_Disjoint_r.
              - eapply Disjoint_Singleton_r. intros Hc. eapply H25. inv Hc; [| now eauto ].
                exfalso. eapply Hnin. now constructor; eauto.
              - rewrite <- bound_var_rename_all_ns_fundefs in *. eapply Union_Disjoint_l.
                + eapply Disjoint_sym. eapply Disjoint_Included; [| | eapply H8]. sets.
                  rewrite (proj1 (bound_var_ctx_comp_ctx)). simpl. normalize_bound_var_ctx.
                  erewrite (fundefs_append_bound_vars _ _ (fundefs_append _ _)); [| reflexivity ]. normalize_bound_var.
                  rewrite <- !(proj2 (bound_var_rename_all_ns_mut _)). rewrite <- !(proj1 (bound_var_ctx_rename_all_ns _)).
                  rewrite <- !(proj1 (bound_var_rename_all_ns_mut _)). xsets.
                + eapply Union_Disjoint_r; [ now sets | ].
                  eapply Union_Disjoint_r; [ now sets | ].
                  eapply Union_Disjoint_r.
                  * eapply Disjoint_sym. eapply Disjoint_Included; [| | eapply H10 ].
                    normalize_bound_var_ctx. simpl. rewrite fundefs_append_bound_vars; [| reflexivity ].
                    normalize_bound_var. now sets. rewrite <- (proj1 (bound_var_ctx_rename_all_ns _)). reflexivity.
                  * eapply Union_Disjoint_r.
                    -- eapply Disjoint_sym. eapply Disjoint_Included; [| | eapply H15 ].
                       rewrite fundefs_append_bound_vars; [| reflexivity ]. rewrite <- bound_var_rename_all_ns_fundefs.
                       rewrite <- bound_var_rename_all_ns_fundefs. normalize_bound_var. sets.
                       rewrite <- (proj1 (bound_var_ctx_rename_all_ns _)). sets.
                    -- rewrite <- bound_var_rename_all_ns in H22. sets. } destruct Hdisu as [Hdis' Hnd].

            assert (Hdisv0 :  ~ (apply_r sig v0) \in  (bound_var_fundefs (inlined_fundefs_f x1 inl) :|: bound_var_fundefs (inlined_fundefs_f x2 inl) :|:
                                                    bound_var_ctx (inlined_ctx_f x inl) :|: bound_var_ctx (inlined_ctx_f x0 inl) :|: bound_var e0 :|: bound_var e)).
            { eapply ub_app_ctx_f in H0. destructAll. repeat normalize_ctx.
              simpl in *. rewrite inlined_fundefs_append in *. simpl in *. rewrite Hel4 in *.
              eapply ub_comp_ctx_f in H0. destructAll. inv H9. rewrite rename_all_ns_fundefs_append in *.
              simpl in H14. eapply fundefs_append_unique_bindings_l in H14; [| reflexivity ]. destructAll.
              repeat normalize_bound_var_in_ctx. inv H11. inv H7. rewrite <- bound_var_rename_all_ns in *.
              intros Hc. inv Hc.
              - inv H7. 2:{ eapply H20. eapply (proj1 (bound_var_rename_all_ns _ _)). eassumption. }
                inv H11. 2:{ eapply H15. constructor. rewrite <- (proj1 (bound_var_ctx_rename_all_ns _)). eassumption.
                             rewrite fundefs_append_bound_vars; [| reflexivity ]. right. simpl. normalize_bound_var. eauto. }
                inv H7. 2:{ eapply H10. constructor. rewrite <- (proj1 (bound_var_ctx_rename_all_ns _)). eassumption.
                            normalize_bound_var_ctx. left. rewrite fundefs_append_bound_vars; [| reflexivity ]. right. simpl. normalize_bound_var. eauto. }
                inv H11. eapply H12. constructor. rewrite <- bound_var_rename_all_ns_fundefs. eassumption. now sets.
                eapply H21. eapply (proj1 (bound_var_rename_all_ns_fundefs _ _)). eassumption.
              - eapply H8. constructor. 2:{ left; eauto. } eapply bound_var_ctx_comp_ctx. right. normalize_bound_var_ctx. left.
                rewrite fundefs_append_bound_vars; [| reflexivity ]. right. simpl. normalize_bound_var. eauto. }

            assert (Hfv : ~ apply_r sig v0 \in occurs_free_ctx (rename_all_ctx_ns sig (inlined_ctx_f x inl)) :|: occurs_free_ctx (rename_all_ctx_ns sig (inlined_ctx_f x0 inl)) :|:
                                               occurs_free_fundefs (rename_all_fun_ns sig (inlined_fundefs_f (fundefs_append x1 x2) inl)) :|:
                                               occurs_free (rename_all_ns sig e0)).
            { specialize (H2 (apply_r sig v0)). rewrite Hgetc in H2. unfold ce in H2. repeat normalize_ctx. repeat destruct_num_occur.
              rewrite Hel4 in H9. repeat destruct_num_occur. simpl in H8. rewrite peq_true in H8.
              assert (x5 = 0) by lia. assert (n1 = 0) by lia. assert (x3 = 0) by lia. assert (n2 = 0) by lia. assert (m = 0) by lia.
              assert (n0 = 0) by lia. subst. assert (Hl : num_occur_list (apply_r_list sig l) (apply_r sig v0) = 0) by lia.
              intros Hc. inv Hc. 2:{ eapply not_occurs_not_free in H9; eauto. }
              inv H9. 2:{ eapply occurs_free_fundefs_append in H10; eauto. inv H10. inv H9; eapply not_occurs_not_free in H10; eauto. }
              inv H10; revert H9; eapply not_occurs_not_free_ctx; eauto. }

            assert (Hdis : Disjoint _ (FromList l0) (bound_var (rename_all_ns sig (Eletapp v v0 f l e)) :|:
                                                                occurs_free (rename_all_ns sig (Eletapp v v0 f l e)))).
            { eapply ub_app_ctx_f in H0. destructAll. eapply Union_Disjoint_r.
              + eapply Disjoint_Included; [| | eapply H8 ]. simpl. sets.
                rewrite <- (proj1 (bound_var_ctx_rename_all_ns _)).
                rewrite (proj1 inlined_comp_ctx). simpl. rewrite inlined_fundefs_append. simpl. rewrite Hel4.
                rewrite (proj1 bound_var_ctx_comp_ctx). normalize_bound_var_ctx.
                erewrite fundefs_append_bound_vars; [| reflexivity ]. normalize_bound_var. xsets.
              + eapply Disjoint_Included_r. eassumption.
                eapply Disjoint_Included; [| | eapply Hdis' ]; [| now sets ]. rewrite <- (proj1 (bound_stem_ctx_rename_all_ns _)).
                rewrite (proj1 inlined_comp_ctx) in *. simpl in *. rewrite inlined_fundefs_append in *. simpl in *. rewrite Hel4 in *.
                rewrite (proj1 (rename_all_ctx_ns_comp_ctx _ _)) in H0. simpl in H0.
                rewrite <- (proj1 (bound_stem_comp_ctx_mut _)). normalize_bound_stem_ctx.
                rewrite fundefs_append_name_in_fundefs; [| reflexivity ]. simpl.
                eapply Union_Included. eapply Included_trans. eapply bound_stem_var. sets.
                eapply Union_Included. eapply Union_Included. eapply Included_trans. eapply name_in_fundefs_bound_var_fundefs. now sets.
                eapply Union_Included. now sets. eapply Included_trans. eapply name_in_fundefs_bound_var_fundefs. now sets.
                eapply Included_trans. eapply bound_stem_var. sets. }

            assert (Hdis'' : ~ v \in FromList l0).
            { intros Hc. eapply Hdis. constructor. eassumption. left. rewrite <- bound_var_rename_all_ns.
              normalize_bound_var. sets. }

            destruct (inline_letapp e0 v) as [[Cinl x'] | ] eqn:Hinl.
            - assert (Hinl' := Hinl). eapply inline_letapp_rename with (sig := sig) in Hinl'.
              (* eapply inline_letapp_rename with (   *)
              2:{ eapply Disjoint_apply_r. sets. }
              eapply inline_letapp_rename with (sig := (set_list (combine l0 (apply_r_list sig l)) (M.empty var))) in Hinl'.
              2:{ rewrite apply_r_set_list2. rewrite apply_r_empty. reflexivity. intros Hin. eapply Disjoint_Singleton_In in Hin; tci .
                  sets. }
              assert (Hdead1 : FromList l0 \subset (dead_var (rename_all_ns sig e))).
              { eapply Disjoint_dead_var. eapply Disjoint_Included_r; [| eassumption ].
                eapply bound_var_occurs_free_Eletapp_Included. }

              assert (Hor : v |: FromList l0 \subset Complement var (Range_map sig) :|: dead_var (rename_all_ns sig (Cinl |[ e ]|))).
              { destruct (Decidable_Range_map sig). intros z Hinz. destruct (Dec z); [| now eauto ].
                destruct r as [w Hget]. eapply H5 in Hget. inv Hget. inv H8.
                repeat normalize_ctx.
                repeat destruct_num_occur. rewrite Hel4 in H11. repeat destruct_num_occur.
                right. eapply (proj1 (num_occur_app_ctx_mut _ _)). exists 0, 0. split.
                + assert (Hinl'' := Hinl). eapply inline_letapp_rename with (sig := sig) in Hinl''; eauto.
                  2:{ eapply Disjoint_apply_r. sets. } eapply num_occur_inline_letapp'; [| eassumption ]. eassumption.
                + split; eauto.
                + exfalso. eapply Hdis'. constructor. eassumption.
                  normalize_ctx. eapply (proj1 (bound_stem_ctx_rename_all_ns _)) in H9.
                  repeat normalize_bound_var_lemmas.
                  inv H9. eapply bound_stem_var in H8. do 2 left. right. repeat normalize_ctx. eassumption.
                  simpl in H8. normalize_bound_stem_ctx_in_ctx. inv H8.
                  * repeat normalize_ctx. simpl in H9. rewrite Hel4 in H9. rewrite fundefs_append_name_in_fundefs in H9; [| reflexivity ].
                    simpl in H9. inv H9. eapply name_in_fundefs_bound_var_fundefs in H8. left. now eauto.
                    inv H8. left. now eauto. eapply name_in_fundefs_bound_var_fundefs in H9. now eauto.
                  * eapply bound_stem_var in H9. repeat normalize_ctx. now eauto. }

              assert (Hold : forall x3 : M.elt, FromList l0 x3 -> x3 <> apply_r sig x' \/ ~ Range_map sig x3).
              { intros x3 Hin3. destruct (Decidable_Range_map sig). destruct (Dec x3) as [Hr | Hr ]; [| now eauto ].
                destruct Hr as [y3 Hget]. eapply H5 in Hget. destruct Hget as [Hg1 Hg2].
                assert (Hinl'' := Hinl). eapply inline_letapp_rename with (sig := sig) in Hinl''; eauto.
                assert (Hi := Hinl''). eapply inline_letapp_var_eq_alt' in Hi. inv Hi.
                - left. inv H7. intros Hc. eapply Hdis. constructor. eassumption. left. simpl. normalize_bound_var.
                  subst; eauto.
                - inv H7.
                  + left. intros Hc. eapply Hdis'. constructor. now right; eauto. repeat normalize_bound_var_lemmas.
                    subst; eauto.
                  + destruct (peq x3 (apply_r sig x')); subst; [| now eauto ].
                    right. destruct (e_num_occur (apply_r sig x') (rename_all_ns sig e0)). destruct x3.
                    eapply not_occurs_not_free in H7. contradiction. inv Hg2.
                    * repeat destruct_num_occur. rewrite Hel4 in H12. repeat destruct_num_occur.
                      eapply num_occur_det in H22; [| clear H22; eassumption ]. congruence.
                    * exfalso. eapply Hdis'. constructor. right. eassumption. repeat normalize_ctx. simpl in H9.
                      eapply (proj1 (bound_stem_comp_ctx_mut _)) in H9. inv H9.
                      left. left. right. eapply bound_stem_var. repeat normalize_bound_var_lemmas. eassumption.
                      normalize_bound_stem_ctx_in_ctx. inv H10.
                      -- rewrite <- name_in_fundefs_rename_all_ns in H9. repeat normalize_ctx.
                         eapply fundefs_append_name_in_fundefs in H9; [| reflexivity ]. simpl in H9. rewrite Hel4 in H9. simpl in H9.
                         inv H9. do 4 left. right. eapply name_in_fundefs_bound_var_fundefs. eassumption.
                         inv H10. do 5 left. now eauto. do 3 left. right. eapply name_in_fundefs_bound_var_fundefs. eassumption.
                      -- left. right. eapply bound_stem_var. repeat normalize_bound_var_lemmas. eassumption.
                - eapply Disjoint_apply_r. sets. }

              assert (Heq : rename_all_ns (set_list (combine l0 (apply_r_list sig l)) sig)
                                          (Cinl |[ rename_all_ns (M.set v x' (M.empty var)) e ]|) =
                            (rename_all_ctx_ns (set_list (combine l0 (apply_r_list sig l)) (M.empty _)) (rename_all_ctx_ns sig Cinl))
                             |[ rename_all_ns (M.set v (apply_r (set_list (combine l0 (apply_r_list sig l)) sig) x') (M.empty _)) (rename_all_ns sig e) ]|).
              { erewrite (proj1 (rename_all_ns_app_ctx _ _)). f_equal.
                - erewrite <- (proj1 (set_list_rename_all_ctx_ns _ _)). reflexivity.
                  eapply Included_trans. eapply Included_trans; [| eapply Hor ]. sets. eapply Included_Union_compat. reflexivity.
                  intros z1 Hl. unfold dead_var, In in *. repeat destruct_num_occur. eassumption. sets.
                - erewrite <- (proj1 (rename_all_ns_join _ v _)).
                  assert (Heq := proj1 (set_list_rename_all_ns [v] [x'] )). simpl in Heq. rewrite <- Heq. f_equal.
                  * eapply (proj1 eq_P_rename_all_ns).
                    eapply eq_env_P_antimon. eapply eq_P_set_list_not_in. eapply Complement_antimon.
                    intros z Hin. assert (Hin' := Hin).
                    eapply Hdead1 in Hin. unfold dead_var, In in *. destruct (e_num_occur z e). repeat destruct_num_occur.
                    eapply num_occur_rename_all_not_dom_mut in Hin; [| eassumption | ]. assert (x3 = 0) by lia. subst. eassumption.
                    intros Hc. eapply Hd_bv'. constructor. right. eassumption. eassumption.
                  * eapply Included_trans. 2:{ eapply Included_Union_compat. eapply Complement_antimon. eapply range_map_set_list. reflexivity. }
                    rewrite Union_DeMorgan. repeat normalize_sets. eapply Singleton_Included.
                    assert (Hin : v \in Complement var (Range_map sig) :|: dead_var (rename_all_ns sig (Cinl |[ e ]|))).
                    { eapply Hor; eauto. }
                    inv Hin.
                    -- left. eapply Included_Intersection. eapply Singleton_Included. eassumption.
                       eapply Singleton_Included. intros Hc. eapply Hnin. constructor; eauto. reflexivity.
                    -- right. unfold In, dead_var in *. repeat destruct_num_occur.
                       eapply dead_occur_rename_all_ns_set_list. intros Hc. eapply Hnin. constructor; eauto. eassumption.
                  * rewrite Dom_map_set_list. repeat normalize_sets. eapply Union_Disjoint_r. now sets. now sets.
                    rewrite length_apply_r_list. now eauto. }

              assert (Heq1 : inlined_ctx_f (comp_ctx_f x (Efun1_c (fundefs_append x1 (Fcons (apply_r sig v0) f l0 e0 x2)) x0))
                                           (M.set (apply_r sig v0) true inl) =
                             inlined_ctx_f (comp_ctx_f x (Efun1_c (fundefs_append x1 x2) x0)) inl).
              { repeat normalize_ctx. simpl. rewrite !inlined_fundefs_append.
                assert (Heq2 : inlined_fundefs_f (Fcons (apply_r sig v0) f l0 e0 x2) (M.set (apply_r sig v0) true inl) =
                               inlined_fundefs_f x2 (M.set (apply_r sig v0) true inl)).
                { simpl. unfold get_b. rewrite M.gss. reflexivity. }
                rewrite Heq2. rewrite <- !inlined_fundefs_append.
                replace (Efun1_c (inlined_fundefs_f (fundefs_append x1 x2) (M.set (apply_r sig v0) true inl)) (inlined_ctx_f x0 (M.set (apply_r sig v0) true inl)))
                  with (inlined_ctx_f (Efun1_c (fundefs_append x1 x2) x0) (M.set (apply_r sig v0) true inl)) by reflexivity.
                replace (Efun1_c (inlined_fundefs_f (fundefs_append x1 x2) inl) (inlined_ctx_f x0 inl)) with
                    (inlined_ctx_f (Efun1_c (fundefs_append x1 x2) x0) inl) by reflexivity.
                rewrite <- !(proj1 inlined_comp_ctx). rewrite inlined_ctx_f_staged.
                eapply Disjoint_inlined_ctx.
                eapply Disjoint_Included_r with (s2 := [set (apply_r sig v0)]).
                intros z Hin. unfold Dom_map_b, In, get_b in *. destruct (peq z (apply_r sig v0)).  subst. reflexivity.
                rewrite M.gso in Hin; eauto. rewrite M.gempty in Hin. congruence. eapply Disjoint_Singleton_r.
                intros Hc. eapply Hdisv0. repeat normalize_ctx. repeat normalize_bound_var_lemmas. simpl in Hc. repeat normalize_bound_var_ctx_in_ctx.
                inv Hc; eauto. inv H7; eauto. repeat normalize_ctx. repeat normalize_bound_var_lemmas. inv H8; eauto. left; eauto. left; eauto. }


              set (ce'' := rename_all_ctx_ns sig (inlined_ctx_f (comp_ctx_f x (Efun1_c (fundefs_append x1 x2) x0)) inl)
                           |[ rename_all_ns (set_list (combine l0 (apply_r_list sig l)) sig)
                                            (Cinl |[ rename_all_ns (M.set v x' (M.empty var)) e ]|) ]|).

              assert (Hclos : gsr_clos 1 ce ce'').
              { replace 1 with (1 + 0) by lia. eapply Trans_srw.
                * unfold ce. repeat normalize_ctx. simpl. do 1 (rewrite inlined_fundefs_append).
                  rewrite <- app_ctx_f_fuse. constructor. simpl. rewrite Hel4. repeat normalize_ctx. simpl.
                  eapply Fun_inline_letapp_s; [| | eassumption ]. rewrite length_apply_r_list. now eauto.
                  specialize (H2 (apply_r sig v0)). rewrite Hgetc in H2. unfold ce in H2. repeat normalize_ctx.
                  rewrite <- app_ctx_f_fuse in H2. eapply num_occur_app_ctx_mut in H2. destructAll.
                  assert (Heq0 : x3 = 0).
                  { eapply num_occur_app_ctx_mut in H7. destructAll. inv H9. simpl in H8.
                    rewrite peq_true in H8. lia. }
                  assert (x4 = 1) by lia; subst. simpl in H7. repeat normalize_ctx.
                  simpl in H7. rewrite Hel4 in H7. now eapply H7.
                * unfold ce''. rewrite Heq. rewrite !(proj1 inlined_comp_ctx). rewrite <- (proj1 inlined_comp_ctx).
                  repeat normalize_ctx. rewrite <- app_ctx_f_fuse. simpl.
                  rewrite !inlined_fundefs_append, !rename_all_ns_fundefs_append.
                  unfold var, M.elt. rewrite set_list_rename_all_ar. now constructor.
                  eassumption. now sets. }

              assert (Hun := Hclos). eapply gsr_clos_preserves_clos in Hun; [| eassumption | eassumption ]. destructAll.
              assert (Hbv := Hclos). eapply gsr_included_bv in Hbv.

              assert (Hdead: FromList l0 \subset (dead_var_ctx (rename_all_ctx_ns sig (inlined_ctx_f (comp_ctx_f x (Efun1_c (fundefs_append x1 x2) x0)) inl)))).
              { eapply Disjoint_dead_var_ctx. eapply Union_Disjoint_r.
                - eapply Disjoint_Included; [| | eapply Hdis' ]; [| now sets ].
                  intros z Hin. repeat normalize_ctx. repeat normalize_bound_var_lemmas. inv Hin.
                  repeat normalize_bound_var_lemmas. now eauto.
                  simpl in H9. repeat normalize_ctx. repeat normalize_bound_var_ctx_in_ctx.
                  inv H9. repeat normalize_bound_var_lemmas. inv H10.
                  repeat normalize_bound_var_lemmas. now left; eauto.
                  repeat normalize_bound_var_lemmas. now left; eauto.
                  repeat normalize_bound_var_lemmas. now left; eauto.
                - eapply Disjoint_Included_r. eapply occurs_free_included_ctx. eapply Disjoint_Included_r.
                  eapply H8. sets. }


              assert (Heq2 : rename_all_ctx_ns
                               (set_list (combine l0 (apply_r_list sig l)) sig)
                               (inlined_ctx_f (comp_ctx_f x (Efun1_c (fundefs_append x1 x2) x0)) inl) =
                             rename_all_ctx_ns sig (inlined_ctx_f (comp_ctx_f x (Efun1_c (fundefs_append x1 x2) x0)) inl)).
              { (* assert (Hrw := proj1 (set_list_rename_all_ctx_ns [v] [x'])). simpl in Hrw. rewrite <- Hrw.  *)
                rewrite <- (proj1 (set_list_rename_all_ctx_ns _ _)).
                rewrite rename_all_ctx_ns_Disjoint with (m := set_list _ _). reflexivity.
                - rewrite Dom_map_set_list, Dom_map_empty. normalize_sets.
                  eapply Disjoint_sym. eapply Complement_Disjoint. eassumption.
                  rewrite length_apply_r_list; eauto.
                - eapply Included_Union_preserv_r. eassumption.
                - sets. }

              assert (Hneq : apply_r sig v0 <> apply_r sig x').
              { assert (Hinl'' := Hinl). eapply inline_letapp_rename with (sig := sig) in Hinl''; eauto.
                eapply inline_letapp_var_eq_alt' in Hinl''. inv Hinl''.
                - destructAll. intros Hc. eapply Hnin. rewrite Hc. constructor; eauto.
                - inv H9. repeat normalize_bound_var_lemmas. intros Hc. eapply Hdisv0. rewrite <- Hc in H10.
                  left ; eauto.
                  intros Hc. eapply Hfv. rewrite <- Hc in H10. right; eauto.
                - eapply Disjoint_apply_r. eapply Disjoint_Singleton_r. intros Hc.
                  eapply Hd_bv'. constructor; eauto. }
              clear Hsame.
              match goal with
              | [ H : context[contract ?SIG ?CNT ?E ?SUB ?IM] |- _ ] =>
                (* remember (app_ctx_f (rename_all_ctx_ns SIG (inlined_ctx_f c IM)) (rename_all_ns SIG E)) as ce''; *)
                remember (contract SIG CNT E SUB IM) as s
              end.
              destruct s as [[[[? ?] ?] ?] ?]. symmetry in Heqs. inv H6.
              eapply IHn with (c := comp_ctx_f x (Efun1_c (fundefs_append x1 (Fcons (apply_r sig v0) f l0 e0 x2)) x0)) in Heqs.
              { destructAll. rewrite Heq1, Heq2 in H6.

                assert (Him : dead_var_ctx (inlined_ctx_f (comp_ctx_f x (Efun1_c (fundefs_append x1 x2) x0)) inl) \subset dead_var_ctx (inlined_ctx_f (comp_ctx_f x (Efun1_c (fundefs_append x1 (Fcons (apply_r sig v0) f l0 e0 x2)) x0)) im')).
                { repeat normalize_ctx. simpl. do 1 (rewrite !inlined_fundefs_append at 1). simpl.
                  assert (Hb : get_b (apply_r sig v0) im' = true).
                  { eapply b_map_le_c in b0. eapply b0. unfold get_b. now rewrite M.gss. }
                  rewrite Hb. rewrite <- !inlined_fundefs_append.
                  replace (Efun1_c (inlined_fundefs_f (fundefs_append x1 x2) im') (inlined_ctx_f x0 im')) with
                      (inlined_ctx_f (Efun1_c (fundefs_append x1 x2) x0) im') at 1 by reflexivity.
                  rewrite <- (proj1 inlined_comp_ctx).
                  eapply Included_trans.
                  2:{ intros z Hc. eapply dead_occur_ec_le_antimon. simpl in *. eapply b_map_le_c. eapply BP. eapply Hc. } simpl.
                  rewrite (proj1 inlined_comp_ctx). reflexivity. }

                  assert (Heqp : eq_env_P
                                 (Complement _ (dead_var_ctx
                                                  (inlined_ctx_f
                                                     (comp_ctx_f x (Efun1_c (fundefs_append x1 (Fcons (apply_r sig v0) f l0 e0 x2)) x0)) im')))
                                 (set_list (combine l0 (apply_r_list sig l)) sig) sig).
                { eapply eq_env_P_antimon. eapply eq_P_set_list_not_in.
                  eapply Complement_antimon.
                  eapply Included_trans; [| eassumption ]. intros xl Hin.
                  assert (Hin' := Hin). eapply Hdead in Hin'. unfold dead_var_ctx, In in *.
                  destruct (e_num_occur_ec  (inlined_ctx_f (comp_ctx_f x (Efun1_c (fundefs_append x1 x2) x0)) inl) xl).
                  eapply num_occur_rename_all_ctx_not_dom_mut in Hin'; [| eassumption | ]. assert (x3 = 0) by lia. subst. eassumption.
                  intros Hc. eapply Hd_bv'. constructor. now right; eauto. eassumption. }

                erewrite (proj1 eq_P_rename_all_ctx_ns) with
                    (e := inlined_ctx_f (comp_ctx_f x (Efun1_c (fundefs_append x1 (Fcons (apply_r sig v0) f l0 e0 x2)) x0)) im') (sub' := sig) in H6;
                  [| eassumption ].
                split; [| split; [| split ]].
                + rewrite Nat.add_comm. eapply gsr_clos_trans; [| eassumption ]. eassumption.
                + unfold ce'.
                  erewrite (proj1 eq_P_rename_all_ctx_ns) in H9; [| eassumption ].
                  eassumption.
                + unfold ce'.
                  erewrite (proj1 eq_P_rename_all_ctx_ns) in H10; [| eassumption ].
                  eassumption.
                + erewrite (proj1 eq_P_rename_all_ctx_ns) in H11; [| eassumption ].
                  intro; intros. eapply H11. rewrite get_set_list2. eassumption.
                  eapply H5 in H12. inv H12. intros Hc. eapply H13. rewrite <- (proj1 (rename_all_ns_app_ctx _ _)).
                  eapply (proj1 (bound_var_rename_all_ns _ _)). repeat normalize_ctx.
                  rewrite <- app_ctx_f_fuse. repeat rewrite bound_var_app_ctx. right. left.
                  simpl. normalize_bound_var_ctx. simpl. repeat normalize_ctx. simpl. rewrite Hel4.
                  rewrite fundefs_append_bound_vars; [| reflexivity ]. normalize_bound_var. sets. }
              + (* size for IH *)
                unfold term_sub_inl_size in *; simpl in H. simpl.
                eapply Nat.succ_lt_mono in H.
                apply -> Nat.le_succ_l. apply -> Nat.le_succ_l.
                eapply Nat.le_lt_trans.
                apply -> Nat.add_le_mono_r. eapply term_size_inline_letapp. eassumption.
                rewrite (proj1 (term_size_rename_all_ns _)). rewrite (Nat.add_comm (term_size e0)). rewrite <- Nat.add_assoc.
                rewrite (Nat.add_comm (term_size e0)). erewrite <- sub_inl_fun_size; eauto.
              + (* unique bindings *)
                rewrite Heq1, Heq2. eassumption.
              + (* closed *)
                rewrite Heq1, Heq2. eassumption.
              + { rewrite Heq1, Heq2. intros z.
                  assert (Hc := H2). specialize (H2 z). unfold ce in H2.
                  repeat destruct_num_occur. rewrite Hel4 in H10. simpl in H10. inv H10.

                  assert (Hdisl : Disjoint _ (FromList l0) (FromList (apply_r_list sig l))).
                  { eapply Disjoint_Included_r; [ | eapply Hdis ]. simpl. normalize_occurs_free. sets. }

                  assert (Hinl0 : FromList l0 \subset Complement var (Range_map sig) :|: dead_var (rename_all_ns sig e0)).
                  { intros r Hinr. destruct (Decidable_Range_map sig) as [D]. destruct (D r); [| now left; eauto ].
                    destruct r0 as [i Hgetr]. eapply H5 in Hgetr. destructAll. inv H11.
                    - repeat destruct_num_occur. simpl in H14. repeat destruct_num_occur. rewrite Hel4 in H15. simpl in H15.
                      repeat destruct_num_occur. now right.
                    - exfalso. eapply Hdis'. constructor. now right; eauto. eapply bound_stem_comp_ctx_mut in H13.
                      inv H13; repeat normalize_bound_var_lemmas. now eapply bound_stem_var in H11; eauto.
                      simpl in H11. repeat normalize_ctx. simpl in H11. rewrite Hel4 in H11. inv H11. repeat normalize_bound_var_lemmas.
                      eapply fundefs_append_name_in_fundefs in H16; [| reflexivity ]. simpl in H16. inv H16.
                      eapply name_in_fundefs_bound_var_fundefs in H11. left; now eauto. inv H11. now left; eauto.
                      eapply name_in_fundefs_bound_var_fundefs in H13. left; now eauto. eapply bound_stem_var in H16. now left; eauto. }

                  assert (Hneqv : ~ FromList (apply_r_list sig l) (apply_r sig v0)).
                  { specialize (Hc (apply_r sig v0)). rewrite Hgetc in Hc. unfold ce in Hc.
                    repeat normalize_ctx. repeat destruct_num_occur. simpl in H14. repeat destruct_num_occur.
                    rewrite Hel4 in H14. repeat destruct_num_occur. simpl in H13. rewrite peq_true in H13.
                    assert (x7 = 0) by lia. assert (n5 = 0) by lia. assert (x4 = 0) by lia. assert (n6 = 0) by lia. assert (m0 = 0) by lia.
                    assert (n4 = 0) by lia. subst. assert (Hl : num_occur_list (apply_r_list sig l) (apply_r sig v0) = 0) by lia.
                    eapply not_occur_list. eassumption. }

                  assert (Hneqv0 : apply_r (set_list (combine l0 (apply_r_list sig l)) sig) x' <> apply_r sig v0).
                  { destruct (Decidable_FromList l0). destruct (Dec x').
                    intros Hc1. eapply Hneqv. rewrite <- Hc1. eapply apply_r_set_list_In. eassumption. rewrite length_apply_r_list. now eauto.
                    rewrite apply_r_set_list2. eauto. eassumption. }

                  assert (Hoc : forall (x7 : var) (n1 : nat), FromList l0 x7 -> num_occur (rename_all_ns sig e0) x7 n1 ->
                                                              get_c x7 (M.set (apply_r sig v0) 0 count) = n1).
                  { intros. specialize (Hc x7). unfold ce in Hc. repeat normalize_ctx. repeat destruct_num_occur.
                    simpl in H16. repeat normalize_ctx. repeat destruct_num_occur. rewrite Hel4 in H16. repeat destruct_num_occur.
                    assert (Hl0d : num_occur (rename_all_ns sig (Eletapp v v0 f l e)) x7 0).
                    { eapply Disjoint_dead_var; eassumption. }
                    assert (n4 = get_c x7 count).
                    { simpl in *. inv Hl0d. pi0. dec_vars. rewrite H22. simpl.
                      eapply Hdead in H10. unfold dead_var_ctx, In in H10. repeat normalize_ctx. repeat destruct_num_occur. simpl in *.
                      repeat match goal with
                             | [H1 : num_occur ?e ?x ?n1, H2 : num_occur ?e ?x ?n2 |- _ ] => eapply num_occur_det in H1; [| eapply H2 ]; subst
                             | [H1 : num_occur_fds ?e ?x ?n1, H2 : num_occur_fds ?e ?x ?n2 |- _ ] => eapply num_occur_det in H1; [| eapply H2 ]; subst
                             | [H1 : num_occur_ec ?e ?x ?n1, H2 : num_occur_ec ?e ?x ?n2 |- _ ] => eapply num_occur_ec_det in H1; [| eapply H2 ]; subst
                             end.
                      lia. }
                    unfold get_c. rewrite !M.gso. rewrite H16. reflexivity.
                    intros hc. eapply Hdis'. subst. constructor. now right; eauto. left; eauto. }

                  assert (Hvd : ~ v \in bound_var_ctx (rename_all_ctx_ns sig (inlined_ctx_f (comp_ctx_f x (Efun1_c (fundefs_append x1 (Fcons (apply_r sig v0) f l0 e0 x2)) x0)) inl)) :|:
                                                      occurs_free_ctx (rename_all_ctx_ns sig (inlined_ctx_f (comp_ctx_f x (Efun1_c (fundefs_append x1 (Fcons (apply_r sig v0) f l0 e0 x2)) x0)) inl))).
                  { intros Hc1. inv Hc1.
                    - eapply Hdis'. constructor. now left.
                      repeat normalize_bound_var_lemmas. repeat normalize_ctx. repeat normalize_bound_var_lemmas.
                      inv H10. now left; eauto. simpl in H11. repeat normalize_bound_var_ctx_in_ctx. inv H11; [| now eauto ].
                      repeat normalize_ctx. repeat normalize_bound_var_lemmas. inv H10. now left; eauto.
                      simpl in H11. rewrite Hel4 in H11. repeat normalize_bound_var_in_ctx. inv H11; eauto. inv H10. do 5 left. reflexivity.
                      inv H10. exfalso. contradiction. inv H11; eauto.
                    - eapply closed_app_ctx in H10. inv H10. eassumption. }
                  assert (Hdeadv : num_occur_ec (rename_all_ctx_ns sig (inlined_ctx_f (comp_ctx_f x (Efun1_c (fundefs_append x1 (Fcons (apply_r sig v0) f l0 e0 x2)) x0)) inl)) v 0).
                  { eapply Disjoint_dead_var_ctx. eapply Disjoint_Singleton_l. eassumption. reflexivity. } clear Hvd.

                  assert (Hocv : num_occur (rename_all_ns sig e) v (get_c v count)).
                  { repeat normalize_ctx. repeat destruct_num_occur. simpl in H11. repeat destruct_num_occur. rewrite Hel4 in H13.
                    simpl in H13. repeat destruct_num_occur.
                    specialize (Hc v). unfold ce in Hc. repeat normalize_ctx. repeat destruct_num_occur. simpl in *.
                    repeat destruct_num_occur. rewrite Hel4 in H16. simpl in H16. repeat destruct_num_occur.
                    repeat match goal with
                           | [H1 : num_occur ?e ?x ?n1, H2 : num_occur ?e ?x ?n2 |- _ ] => eapply num_occur_det in H1; [| eapply H2 ]; subst
                           | [H1 : num_occur_fds ?e ?x ?n1, H2 : num_occur_fds ?e ?x ?n2 |- _ ] => eapply num_occur_det in H1; [| eapply H2 ]; subst
                           | [H1 : num_occur_ec ?e ?x ?n1, H2 : num_occur_ec ?e ?x ?n2 |- _ ] => eapply num_occur_ec_det in H1; [| eapply H2 ]; subst
                           end.
                    rewrite peq_false in H15.
                    assert (Hnin' : ~ v \in FromList (apply_r_list sig l)).
                    { intros Hc. eapply Hnin. constructor; sets. }
                    eapply not_occur_list in Hnin'. rewrite Hnin' in *. simpl in H15. rewrite H15. eassumption.
                    intros Hc. subst. eapply Hdis'. constructor; eauto. left; eauto. }

                  destruct (var_dec v z).
                  - subst.
                    match goal with
                    | [ _ : _ |- num_occur _ _ ?c ] => set (cnt := c)
                    end.
                    assert (Hceq : cnt = if var_dec z (apply_r (set_list (combine l0 (apply_r_list sig l)) sig) x') then get_c z count else 0).
                    { unfold cnt, update_count_letapp. destruct (var_dec _ _).
                      - subst.
                        assert (Heqz : apply_r (set_list (combine l0 (apply_r_list sig l)) sig) x' = apply_r sig x').
                        { destruct (Decidable_FromList l0). destruct (Dec x').
                          exfalso. eapply Hnin. constructor. reflexivity. right. eapply apply_r_set_list_In. eassumption.
                          rewrite length_apply_r_list. now eauto.
                          rewrite apply_r_set_list2. reflexivity. eassumption. }
                        rewrite Heqz in *. rewrite update_count_inlined_unaffected. unfold get_c. rewrite M.gso. reflexivity.
                        now eauto. eassumption. intros Hc1. eapply Hnin. constructor; eauto.
                      - unfold get_c. rewrite M.gso; eauto. rewrite M.gss. reflexivity. }

                    subst. eapply num_occur_app_ctx. exists 0, cnt. split; [| split; [| reflexivity ] ].
                    + repeat normalize_ctx. repeat destruct_num_occur. simpl in H11. repeat destruct_num_occur. rewrite Hel4 in H13.
                      simpl in H13. repeat destruct_num_occur. eapply num_occur_ec_comp_ctx. eexists 0, 0. split; [| split ]; eauto.
                      simpl. eapply num_occur_ec_eq. econstructor; eauto. repeat normalize_ctx.
                      eapply fundefs_append_num_occur. reflexivity. eassumption. eassumption. reflexivity.
                    + rewrite Heq.
                      eapply num_occur_app_ctx. exists 0, cnt. split; [| split; [| reflexivity ] ].
                      * eapply num_occur_inline_letapp'; [| eassumption ].
                        eapply dead_occur_rename_all_ns_set_list.
                        intros Hc1. eapply Hnin. constructor. reflexivity. now eauto.
                        rewrite <- (proj1 (rename_all_ns_empty)).
                        repeat normalize_ctx. repeat destruct_num_occur. simpl in H11. repeat destruct_num_occur. rewrite Hel4 in H13.
                        simpl in H13. repeat destruct_num_occur. eassumption.
                      * rewrite Hceq. destruct (var_dec _ _).
                        -- rewrite e1. rewrite rename_all_ns_same_set.
                           rewrite <- e1 in *. eassumption.
                        -- eapply num_occur_rename_all_ns. eassumption.
                  - edestruct (e_sum_range_n (rename_all_ns sig e0) z l0 (apply_r_list sig l)).
                    rewrite length_apply_r_list. now eauto.
                    destruct (Decidable_FromList l0) as [Dec]. destruct (Dec z).
                    + assert (Hneqz : z <> apply_r (set_list (combine l0 (apply_r_list sig l)) sig) x').
                      { rewrite set_list_rename_all_ar in Hinl'; [| eassumption | now sets ].
                        eapply inline_letapp_var_eq_alt' in Hinl'. inv Hinl'.
                        - destructAll. eauto.
                        - inv H11.
                          + repeat normalize_bound_var_lemmas. intros Hc1. eapply Hdis'.
                            constructor. now right; eauto. now subst; eauto.
                          + eapply of_rename_all_ns_mut in H13. inv H13.
                            intros Hc1. rewrite <- Hc1 in *. inv H11. rewrite Dom_map_set_list, Dom_map_empty in H14.
                            repeat normalize_sets. contradiction. rewrite length_apply_r_list. now eauto.
                            eapply Range_map_set_list in H11. intros Hc1.
                            eapply Hdis. constructor. eassumption. simpl. normalize_occurs_free. subst. eauto. }
                      assert (Heql : get_c z (update_count_letapp (apply_r (set_list (combine l0 (apply_r_list sig l)) sig) x')  v
                                                                  (update_count_inlined (apply_r_list sig l) l0 (M.set (apply_r sig v0) 0 count))) =
                                     0).
                      { unfold update_count_letapp. destruct (var_dec v (apply_r (set_list (combine l0 (apply_r_list sig l)) sig) x')); subst.
                        - rewrite update_count_inlined_dom. reflexivity. rewrite length_apply_r_list. now eauto. eassumption.
                          eapply Disjoint_sym. eapply Disjoint_Included_r; [| eapply Hdis ]. simpl. normalize_occurs_free. sets.
                        - unfold get_c. rewrite M.gso. rewrite M.gso; eauto.
                          eapply update_count_inlined_dom. rewrite length_apply_r_list. now eauto. eassumption.
                          eapply Disjoint_sym. eapply Disjoint_Included_r; [| eapply Hdis ]. simpl. normalize_occurs_free. sets.
                          eassumption. } rewrite Heql.
                      eapply num_occur_app_ctx. exists 0, 0. split; [| split; [| reflexivity ] ].
                      * eapply Hdead. eassumption.
                      * assert (Hinl1 := f0). eapply Included_Union_preserv_r with (s2 := [set v]) in Hinl1; [| reflexivity ].
                        eapply Hor in Hinl1. inv Hinl1.
                        -- rewrite <- (proj1 (rename_all_ns_app_ctx _ _)).
                           eapply num_occur_rename_all_ns_kill.
                           intros Hc1. eapply range_map_set_list in Hc1. inv Hc1. contradiction.
                           eapply Hdis. constructor; eauto. simpl. normalize_occurs_free. sets.
                           eapply Dom_map_set_list. rewrite length_apply_r_list. now eauto. now left.
                        -- rewrite Heq. unfold dead_var, In in H11. repeat destruct_num_occur.
                           eapply num_occur_app_ctx. exists 0, 0. split; [| split; [| reflexivity ]].
                           ++ eapply num_occur_inline_letapp'; [| eassumption ].
                              eapply num_occur_rename_all_ns_kill.
                              intros Hc1. eapply Range_map_set_list in Hc1. eapply Hdis. constructor. now eauto.
                              simpl. normalize_occurs_free. now eauto.
                              eapply Dom_map_set_list; [| now eauto ]. rewrite length_apply_r_list. now eauto.
                           ++ eapply num_occur_rename_all_ns_dead_set; [| rewrite <- (proj1 (rename_all_ns_empty)); eassumption ].
                              rewrite set_list_rename_all_ar in Hinl'; [| eassumption | now sets ]. eassumption.
                    + destruct (peq z (apply_r sig v0)).
                      * assert (Heqc : get_c z (update_count_letapp
                                                  (apply_r (set_list (combine l0 (apply_r_list sig l)) sig) x')
                                                  v (update_count_inlined (apply_r_list sig l) l0 (M.set (apply_r sig v0) 0 count))) = 0).
                        { subst. unfold update_count_letapp. destruct (var_dec v _).
                          - rewrite update_count_inlined_unaffected. unfold get_c. rewrite M.gss. reflexivity.
                            intros Hc1. eapply Hdis'. constructor; eauto. now left; eauto. eassumption.
                          - replace (get_c _ _) with
                                (get_c (apply_r sig v0) (update_count_inlined (apply_r_list sig l) l0 (M.set (apply_r sig v0) 0 count))).
                            2:{ unfold get_c. rewrite M.gso. rewrite M.gso. reflexivity.
                                intros Hc1. eapply Hdis'. constructor. now left. subst; now eauto.
                                destruct (Decidable_FromList l0). destruct (Dec x').
                                intros Hc1. eapply Hneqv. rewrite Hc1. eapply apply_r_set_list_In. eassumption. rewrite length_apply_r_list. now eauto.
                                rewrite apply_r_set_list2. eassumption. eassumption. }
                            erewrite update_count_inlined_unaffected. unfold get_c. rewrite M.gss. reflexivity.
                            intros Hc1. eapply Hdis'. constructor; eauto. now left; eauto. eassumption. }
                        clear Hdeadv.
                        rewrite Heqc. clear Heqc. subst. specialize (Hc (apply_r sig v0)). rewrite Hgetc in Hc. unfold ce in Hc.
                        repeat normalize_ctx. repeat destruct_num_occur. simpl in *. repeat destruct_num_occur.
                        rewrite Hel4 in H15. repeat destruct_num_occur. simpl in *. rewrite peq_true in H14.
                        simpl in *. repeat normalize_ctx. repeat destruct_num_occur.

                        assert (x8 = 0) by lia. assert (n7 = 0) by lia. assert (x6 = 0) by lia. assert (n8 = 0) by lia. assert (m0 = 0) by lia.
                        assert (n6 = 0) by lia. subst. assert (Hl : num_occur_list (apply_r_list sig l) (apply_r sig v0) = 0) by lia.
                        rewrite Heq.
                        eapply num_occur_app_ctx. exists 0, 0. split; [| split; [| reflexivity ]].
                        -- eapply num_occur_ec_comp_ctx_mut. exists 0, 0. split; [| split; [| reflexivity ]].
                           eassumption. simpl. eapply num_occur_ec_eq. constructor. eassumption. repeat normalize_ctx.
                           eapply fundefs_append_num_occur. reflexivity. eassumption. eassumption. reflexivity.
                        -- rewrite <- Heq. rewrite <- (proj1 (rename_all_ns_app_ctx _ _)).
                           eapply dead_occur_rename_all_ns_set_list. eassumption.
                           assert (Hinl'' := Hinl). eapply inline_letapp_rename with (sig := sig) in Hinl''.
                           normalize_ctx. eapply num_occur_app_ctx. exists 0, 0. split; [| split; [| reflexivity ]].
                           eapply num_occur_inline_letapp'; [| eassumption ]. eassumption.
                           rewrite <- (proj1 (rename_all_ns_join _ _ _)).
                           eapply num_occur_rename_all_ns_dead_set. eassumption. eassumption.
                           eapply Disjoint_apply_r. sets.
                      * destruct (peq z (apply_r (set_list (combine l0 (apply_r_list sig l)) sig) x')).
                        -- assert (Hinl'' := Hinl').
                           eapply inline_letapp_gt_zero in Hinl''.
                           2:{ rewrite set_list_rename_all_ar; [| eassumption | now sets ]. subst. eauto. } destructAll.
                           rewrite set_list_rename_all_ar in H13; [| eassumption | now sets ].
                           rewrite set_list_rename_all_ar in Hinl'; [| eassumption | now sets ].
                           eapply inline_letapp_num_occur in Hinl'; [| eassumption | eassumption ].
                           rewrite peq_true in Hinl'. destruct x6; [ lia | ].
                           eapply num_occur_set_list_r in H20; [ | | | | | eassumption | ].
                           assert (H13' := H13). rewrite (proj1 (set_list_rename_all_ns _ _)) in H13.
                           eapply num_occur_det in H13; [| clear H13; clear H13'; eassumption ].
                           rewrite H13 in *.

                           apply num_occur_app_ctx.  do 2 eexists. split; [| split ].
                           ++ apply num_occur_ec_comp_ctx. do 2 eexists.  split; [| split ].
                              eassumption. simpl. constructor. eassumption. repeat normalize_ctx. eapply fundefs_append_num_occur.
                              reflexivity. eassumption. eassumption. reflexivity.
                           ++ rewrite Heq. apply num_occur_app_ctx.
                              do 2 eexists.
                              split; [| split ].
                              ** eassumption.
                              ** eapply num_occur_rename_all_set_x. eassumption.
                                 intros Hc1. eapply Dom_map_empty in Hc1. now inv Hc1. eassumption.
                                 rewrite <- (proj1 (rename_all_ns_empty)). eassumption.
                              ** subst. reflexivity.
                           ++ unfold update_count_letapp.
                              destruct (var_dec v (apply_r (set_list (combine l0 (apply_r_list sig l)) sig) x')).
                              ** contradiction.
                              ** unfold get_c at 1. rewrite M.gss.
                                 rewrite update_count_inlined_unaffected.
                                 replace (get_c v (M.set (apply_r sig v0) 0 count)) with (get_c v count).
                                 2:{ unfold get_c. rewrite M.gso. reflexivity. intros Hc1. eapply Hnin.
                                     subst. constructor; eauto. }
                                 erewrite update_count_sum_range; [ | | | | | | ]; try eassumption.
                                 replace (get_c _ (M.set (apply_r sig v0) 0 count)) with
                                     (get_c (apply_r (set_list (combine l0 (apply_r_list sig l)) sig) x') count).
                                 2:{ unfold get_c. rewrite !M.gso; eauto. }
                                 rewrite H9. simpl. rewrite peq_false; [| now eauto ]. lia.
                                 unfold get_c in *. rewrite !M.gso. rewrite H9. simpl. rewrite peq_false. lia.
                                 eassumption. eassumption. sets. eassumption.
                                 intros hc. eapply Hnin. constructor; eauto.
                           ++ eassumption.
                           ++ sets.
                           ++ sets.
                           ++ eassumption.
                           ++ eassumption.
                           ++ eassumption.
                           ++ eassumption.
                        -- destruct (e_num_occur z (rename_all_ns (M.set v (apply_r (set_list (combine l0 (apply_r_list sig l)) sig) x')
                                                                         (M.empty M.elt)) (rename_all_ns sig e))).
                           assert (Hn := H11). eapply num_occur_sig_unaffected in H11; [| | | eassumption ]. subst.
                           apply num_occur_app_ctx. do 2 eexists. split; [| split ].
                           { apply num_occur_ec_comp_ctx. do 2 eexists.  split; [| split ].
                             eassumption. simpl. constructor. eassumption. repeat normalize_ctx. eapply fundefs_append_num_occur.
                             reflexivity. eassumption. eassumption. reflexivity. }
                           rewrite Heq. apply num_occur_app_ctx. do 2 eexists. split; [| split ].
                           ++ eapply inline_letapp_num_occur with (z := z) in Hinl'; [| eassumption |].
                              rewrite set_list_rename_all_ar in Hinl'; [| eassumption | now sets ].
                              rewrite peq_false in Hinl'. eassumption. eassumption.
                              rewrite (proj1 (set_list_rename_all_ns _ _)); try eassumption.
                              eapply num_occur_set_list_r; try eassumption. now sets. now sets.
                           ++ eassumption.
                           ++ reflexivity.
                           ++ assert (get_c z (update_count_letapp
                                                 (apply_r (set_list (combine l0 (apply_r_list sig l)) sig) x') v
                                                 (update_count_inlined (apply_r_list sig l) l0 (M.set (apply_r sig v0) 0 count))) =
                                      get_c z (update_count_inlined (apply_r_list sig l) l0 (M.set (apply_r sig v0) 0 count))).
                              { unfold update_count_letapp. destruct (var_dec v (apply_r (set_list (combine l0 (apply_r_list sig l)) sig) x')).
                                reflexivity. unfold get_c. rewrite M.gso; eauto. rewrite M.gso; eauto. }
                              rewrite H11.
                              erewrite update_count_sum_range; [ | | | | | | eassumption ]; try eassumption.
                              replace (get_c z (M.set (apply_r sig v0) 0 count)) with (get_c z count).
                              2:{ unfold get_c. rewrite !M.gso; eauto. }
                              rewrite H9. simpl. rewrite peq_false; [| now eauto ]. lia.
                              replace (get_c z (M.set (apply_r sig v0) 0 count)) with (get_c z count).
                              2:{ unfold get_c. rewrite !M.gso; eauto. }
                              rewrite H9. simpl. rewrite peq_false. lia. eassumption. now sets.
                           ++ intros Hc1. eapply Dom_map_set in Hc1. rewrite Dom_map_empty in Hc1. repeat normalize_sets.
                              inv Hc1; contradiction.
                           ++ intros Hc1. eapply Range_map_set_list with (xs := [v]) (vs := [apply_r (set_list (combine l0 (apply_r_list sig l)) sig) x']) in Hc1.
                              repeat normalize_sets. inv Hc1; contradiction. }
              + eassumption.
              + rewrite Heq1, Heq2.
                intros f1 Hget. destruct (peq f1 (apply_r sig v0)).
                * subst. split.
                  -- intros Hbv'. eapply bound_var_app_ctx in Hbv'. eapply Hdisv0. inv Hbv'.
                     ++ repeat normalize_ctx. repeat normalize_bound_var_lemmas. inv H6. left; eauto.
                        repeat normalize_bound_var_lemmas. now do 2 left; eauto.
                        repeat normalize_bound_var_lemmas. simpl in H9. repeat normalize_bound_var_ctx_in_ctx. inv H9; eauto.
                        repeat normalize_ctx. repeat normalize_bound_var_lemmas. inv H6; left; eauto.
                     ++ repeat normalize_ctx. repeat normalize_bound_var_lemmas. inv H6.
                        repeat normalize_bound_var_lemmas. eapply bound_var_inline_letapp in H9; [| eassumption ].
                        inv H9; [| now left; eauto ]. exfalso. eapply Hnin. inv H6. constructor. reflexivity. now sets.
                        repeat normalize_bound_var_lemmas. eauto.
                  -- intros. subst_exp. rewrite bound_var_app_ctx. eapply Union_Disjoint_l.
                     ++ eapply Disjoint_sym. eapply Disjoint_Included; [| | eapply Hdis' ]; [| now sets ].
                        intros z Hin. repeat normalize_ctx. repeat normalize_bound_var_lemmas. inv Hin.
                        eapply bound_var_ctx_rename_all_ns in H6. now eauto.
                        repeat normalize_bound_var_lemmas. simpl in H6. repeat normalize_bound_var_ctx_in_ctx.
                        inv H6; [| now eauto ]. repeat normalize_ctx. repeat normalize_bound_var_lemmas. inv H9; eauto. left. now eauto.
                     ++ rewrite <- bound_var_rename_all_ns. rewrite bound_var_app_ctx. rewrite <- bound_var_rename_all_ns. eapply Union_Disjoint_l.
                        eapply Disjoint_Included_l. eapply bound_var_inline_letapp. eassumption. sets.
                        eapply Union_Disjoint_l. eapply Disjoint_Singleton_l. eassumption.
                        eapply Disjoint_sym. eapply Disjoint_Included; [| | eapply Hdis' ]; now xsets.
                        eapply Disjoint_sym. eapply Disjoint_Included; [| | eapply Hdis ]; xsets. rewrite <- bound_var_rename_all_ns.
                        normalize_bound_var. now sets.
                * unfold get_b in Hget. rewrite M.gso in Hget; eauto. eapply H4 in Hget. inv Hget.
                  split.
                  -- intros Hb. eapply H6. eapply Hbv; eauto.
                  -- intros. eapply Disjoint_Included_l. eassumption. eauto.
              + unfold var, M.elt in *. rewrite Heq1, Heq2. intro; intros.
                split.
                * destruct (Decidable_FromList l0) as [Hdec]. destruct (Hdec x3).
                  ++ intros Hc. eapply bound_var_app_ctx in Hc. inv Hc.
                     ** eapply Hdis'. constructor. now right; eauto.
                        repeat normalize_bound_var_lemmas. repeat normalize_ctx. repeat normalize_bound_var_lemmas.
                        inv H9. now eauto.
                        simpl in H10. normalize_bound_var_ctx_in_ctx. inv H10.
                        repeat normalize_ctx. repeat normalize_bound_var_lemmas. inv H9; left; now eauto.
                        now eauto.
                     ** repeat normalize_bound_var_lemmas. inv H9.
                        --- eapply bound_var_inline_letapp in H10; [| eassumption ]. inv H10.
                            inv H9. eapply Hdis. constructor. eassumption. simpl. normalize_bound_var. now eauto.
                            eapply Hdis'. constructor. now right; eauto. eauto.
                        --- repeat normalize_bound_var_lemmas.
                            eapply Hdis. constructor. eassumption. simpl. normalize_bound_var.
                            rewrite <- bound_var_rename_all_ns. eauto.
                  ++ rewrite get_set_list2 in H6; eauto. eapply H5 in H6. inv H6. intros Hc. eapply H9.
                      eapply Hbv. eassumption.
                * destruct (Decidable_FromList l0) as [Hdec]. destruct (Hdec x3).
                  ++ eapply FromList_set_list in H6; [| now rewrite length_apply_r_list; eauto | eassumption ].
                     destruct (peq y (apply_r sig v0)); subst.
                     ** (* FromList (apply_r_list sig l) (apply_r sig v0) is contradiction *)
                        specialize (H2 (apply_r sig v0)). rewrite Hgetc in H2. unfold ce in H2. repeat normalize_ctx.
                        rewrite <- app_ctx_f_fuse in H2. eapply num_occur_app_ctx_mut in H2. destructAll. pi0.
                        eapply num_occur_app_ctx_mut in H9. destructAll. inv H11. simpl in H10.
                        rewrite peq_true in H10.
                        replace x4 with 0 in * by lia. replace x6 with 0 in * by lia.
                        replace n1 with 0 in * by lia.
                        assert (Hnum : num_occur_list (apply_r_list sig l) (apply_r sig v0) = 0) by lia.
                        eapply not_occur_list in Hnum. exfalso. eauto.
                     ** right.
                        assert (Hno : ~ y \in (occurs_free ce)).
                        { intros Hc. eapply H1 in Hc. inv Hc. }
                        eapply occurs_free_app_bound_stem in Hno. repeat normalize_ctx.
                        { eapply (proj1 (bound_stem_comp_ctx_mut _)).
                          eapply (proj1 (bound_stem_comp_ctx_mut _)) in Hno. simpl in *; repeat normalize_ctx.
                          inv Hno; eauto. repeat normalize_bound_stem_ctx. repeat normalize_bound_stem_ctx_in_ctx.
                          inv H9; eauto. right. left. rewrite fundefs_append_name_in_fundefs in *; [| reflexivity | reflexivity ].
                          inv H10; eauto. simpl in H9. rewrite Hel4 in H9. simpl in H9. inv H9; eauto.
                          now inv H10; exfalso; eauto. }
                        constructor; eauto. now right.
                  ++ rewrite get_set_list2 in H6; eauto.
                     assert (Hinv : num_occur ce'' (apply_r sig v0) 0). {
                       specialize (H2 (apply_r sig v0)). rewrite Hgetc in H2. unfold ce in H2. repeat normalize_ctx.
                       repeat destruct_num_occur. rewrite Hel4 in H11. repeat destruct_num_occur.
                       simpl in H10. rewrite peq_true in H10.
                       replace x4 with 0 in * by lia. replace x6 with 0 in * by lia. replace n3 with 0 in * by lia.
                       replace n4 with 0 in * by lia. replace n2 with 0 in * by lia. replace m with 0 in * by lia.
                       unfold ce''. repeat normalize_ctx.
                       rewrite <- app_ctx_f_fuse. eapply num_occur_app_ctx_mut. eexists 0, 0. split; [ eassumption |].
                       split; [| lia ]. eapply num_occur_app_ctx_mut. eexists 0, 0. split.
                       ** simpl. replace 0 with (0 + (0 + 0)) by lia. constructor.
                          eassumption. repeat normalize_ctx. eapply fundefs_append_num_occur. reflexivity.
                          eassumption. eassumption.
                       ** split; [| lia ].
                          eapply num_occur_app_ctx_mut. eexists 0, 0. split; eauto.
                          +++ assert (Hinl'' := Hinl).
                              eapply inline_letapp_rename with (sig := set_list (combine l0 (apply_r_list sig l)) sig) in Hinl''; eauto.
                              eapply num_occur_inline_letapp_leq in Hinl''. destructAll.
                              2:{ eapply dead_occur_rename_all_ns_set_list; [| eassumption ].
                                  eapply not_occur_list. lia. }
                              assert (x5 = 0) by lia. subst. eassumption.
                              rewrite apply_r_set_list2. eapply Disjoint_apply_r. sets. sets.
                          +++ split; [| lia ]. replace 0 with (0 + 0) by lia.
                              eapply dead_occur_rename_all_ns_set_list.
                              eapply not_occur_list. lia.
                              rewrite <- (proj1 (rename_all_ns_join _ _ _)).
                              destruct (e_num_occur (apply_r sig v0) (rename_all_ns (M.set v (apply_r sig x') sig) e)).
                              assert (Hren := H11).
                              eapply num_occur_rename_all_ns_set in H11; [| | eassumption ]. assert (x5 = 0) by lia; subst.
                              eassumption. eassumption.  }
                     destruct (peq y (apply_r sig v0)); subst. { left. eassumption. }
                     clear Hinv. assert (Hget := H6). rewrite Heq.
                     eapply H5 in H6. inv H6. inv H10.
                     {  repeat destruct_num_occur. rewrite Hel4 in H12. repeat destruct_num_occur. left. repeat normalize_ctx.
                       eapply num_occur_app_ctx_mut. eexists 0, 0. split; eauto.
                       --- eapply num_occur_ec_comp_ctx_mut. exists 0, 0. split; eauto. split; eauto. simpl.
                           replace 0 with (0 + (0 + 0)) by lia. constructor.
                           eassumption. repeat normalize_ctx. eapply fundefs_append_num_occur. reflexivity.
                           eassumption. eassumption.
                       --- split; [| lia ].
                           eapply num_occur_app_ctx_mut. eexists 0, 0. split; eauto.
                           +++ eapply num_occur_inline_letapp_leq in Hinl'. destructAll.
                               2:{ eapply dead_occur_rename_all_ns_set_list.
                                   2:{ rewrite <- (proj1 rename_all_ns_empty). eassumption. }
                                   eapply not_occur_list. eassumption. }
                               assert (x4 = 0) by lia. subst. eassumption.
                           +++ split; [| lia ].
                               destruct (e_num_occur v (rename_all_ns sig e)). destruct x4.
                               **** rewrite rename_all_ns_Disjoint. eassumption.
                                    rewrite Dom_map_set, Dom_map_empty. normalize_sets.
                                    eapply Disjoint_sym. eapply Complement_Disjoint. eapply Singleton_Included.
                                    eassumption.
                               **** { eapply num_occur_rename_all_ns_dead_set. rewrite <- set_list_rename_all_ar.
                                      intros Hc. symmetry in Hc. revert Hc. eapply num_occur_inline_letapp; [| eassumption |].
                                      - eapply dead_occur_rename_all_ns_set_list. eapply not_occur_list. eassumption.
                                        rewrite <- (proj1 rename_all_ns_empty). eassumption.
                                      - intros Hc; subst. eapply num_occur_det in H18; [| eassumption ]. congruence.
                                      - eassumption.
                                      - sets.
                                      - rewrite <- (proj1 rename_all_ns_empty). eassumption. } }
                     { right. repeat normalize_ctx. simpl in H6.
                       eapply (proj1 (bound_stem_comp_ctx_mut _)).
                       eapply (proj1 (bound_stem_comp_ctx_mut _)) in H6. simpl in *; repeat normalize_ctx.
                       inv H6; eauto. repeat normalize_bound_stem_ctx. repeat normalize_bound_stem_ctx_in_ctx.
                       inv H10; eauto. right. left. rewrite fundefs_append_name_in_fundefs in *; [| reflexivity | reflexivity ].
                       inv H6; eauto. simpl in H10. rewrite Hel4 in H10. simpl in H10.
                       inv H10; eauto. inv H6; now exfalso. }
            - eapply Hsame; eassumption. }
          eapply Hsame; eassumption.
        * eapply Hsame; eassumption.
      + eapply Hsame; eassumption.
    - (* fun *)
      remember (precontractfun sig count sub f). destruct p. destruct p.
      symmetry in Heqp. assert (Heqp' := Heqp).
      eapply precontractfun_corresp with (fds := Fnil) in Heqp; eauto.
      destruct Heqp as (H7, H8). destruct H8 as (H8, (H9, (H10, H_sig_pre))).
      assert (Hub' := gsr_clos_preserves_clos _ _ _ H0 H1 H7). destruct Hub'.
      assert (H5' := H5). apply sig_inv_combine in H5. destruct H5 as (H5, H5co).
      assert (Hse := gsr_preserves_sig_dom _ _ _ _ H0 (closed_implies_Disjoint _ H1) H7 H5).
      simpl in *.
      assert ((rename_all_ctx_ns sig (inlined_ctx_f c inl) |[ rename_all_ns sig (Efun f0 e) ]|) =
              (rename_all_ctx_ns sig (inlined_ctx_f (comp_ctx_f c (Efun1_c f0 Hole_c)) inl) |[ rename_all_ns sig e ]|)).
      { ctx_inl_push. rewrite Disjoint_inlined_fds. reflexivity. split. intros. intro.
        destruct H13. inv H14. apply H9 in H16. destruct H16. apply H14. apply bound_var_app_ctx.
        right. constructor. apply bound_var_rename_all_ns_fundefs. eapply name_in_fundefs_bound_var_fundefs. eassumption. }
      simpl in H13. rewrite H13 in *. remember (contract sig c1 e c0 inl ) as s. destruct s. destruct x. destruct p. destruct p.
      symmetry in Heqs. eapply IHn in Heqs; eauto. destructAll.
      + assert (Hube0 := gsr_clos_preserves_clos _ _ _ H11 H12 H14). destructAll.
        assert (Hse0 := gsr_preserves_sig_dom _ _ _ _ H11 (closed_implies_Disjoint _ H12) H14 Hse).
        (* show that e0 = rename_all_ns sig e0 *)
        assert (rename_all_ns sig e0 = e0).
        { rewrite <- (proj1 (rename_all_no_shadow _)). apply Disjoint_dom_rename_all.
          split. intro. intro. inv H20. inv H21. apply Hse0 in H20. apply not_bound_dead_or_free in H20.
          inv H20. apply num_occur_app_ctx in H21. destructAll; pi0. assert (Hne := (proj1 dead_not_free) e0).
          inv Hne. specialize (H23 x). auto. apply H19 in H21. inv H21. eapply sig_inv_dom_mon.
          2: apply Hse0. rewrite bound_var_app_ctx. sets. }
        (* replace f0 by fundefs_append Fnil f0 *)
        (* use postcontractfun_corresp *)
        remember ( postcontractfun
                     (@pair (prod exp ctx_map) b_map
                            (@pair exp ctx_map (Efun f0 e) sub) b0)
                     (fun (rm : r_map) (cm : c_map)
                          (es : prod (prod exp ctx_map) b_map)
                          (_ : lt (term_sub_inl_size es)
                                  (term_sub_inl_size
                                     (@pair (prod exp ctx_map) b_map
                                            (@pair exp ctx_map (Efun f0 e) sub) b0))) =>
                        contract rm cm
                                 (@fst exp ctx_map (@fst (prod exp ctx_map) b_map es))
                                 (@snd exp ctx_map (@fst (prod exp ctx_map) b_map es))
                                 (@snd (prod exp ctx_map) b_map es)) sig c2 b0 sub f0
                     (@subfds_refl e f0) 0 (le_n (sub_inl_size sub b0))) as s.
        destruct s. destruct x. destruct p. destruct p. symmetry in Heqs.
        assert (Hf0n := postcontractfun_name_in_fundefs Heqs).
        eapply postcontractfun_corresp with (c := c) (e := e0) (fds := Fnil) in Heqs; try (rewrite H20); eauto.
        2:{ intros. eapply IHn; eauto.
            assert  (funs_size f0 + sub_inl_size sub b0 < term_sub_inl_size (Efun f e, sub, inl)).
            { unfold term_sub_inl_size; simpl. assert (sub_inl_size sub b0 <= sub_inl_size sub inl).
              apply sub_size_le. apply b_map_le_c. auto. symmetry in Heqp'. apply precontractfun_size in Heqp'.
              lia. auto. }
            assert ( S n >  funs_size f0 + sub_inl_size sub b0) by lia.
            eapply Nat.lt_le_trans; revgoals.
            apply Nat.succ_le_mono. apply H30. auto. }
        * destruct Heqs as (Heqs1, (Heqs2, (Heqs3, (Heqs4, (Heqs5, Heqs6))))).
          rewrite H20 in *. simpl in *.
          assert (Heqs_ub := gsr_clos_preserves_clos _ _ _ H18 H19 Heqs1).
          destruct Heqs_ub as (Heqs_ub, Heqs_c).
          assert (Heqs_dom := gsr_preserves_sig_dom _ _ _ _ H18 (closed_implies_Disjoint _ H19) Heqs1 Hse0).
          assert (rename_all_ctx_ns sig (inlined_ctx_f (comp_ctx_f c (Efun1_c f1 Hole_c)) b2) |[ e0 ]| =
                  rename_all_ctx_ns sig (inlined_ctx_f c  b2) |[ Efun f1 e0 ]|).
          { repeat normalize_ctx. rewrite <- app_ctx_f_fuse. simpl.
            rewrite Heqs5. reflexivity. } rewrite H21 in *. clear H20. clear Heqs5.
          destruct f1.
          -- inv H6. split; auto. unfold ce'. unfold ce. replace (n0 + n1) with (0 + (n0 + n1)) by lia.
             eapply gsr_clos_trans. eassumption. eapply gsr_clos_trans. eassumption.
             replace n1 with (n1 - 0) by lia. eassumption .
             split. now auto. split. now auto.
             (* sig_inv_codom *)
             intro. intros. assert (H6' := H6). apply Heqs4 in H6.
             rewrite H21 in H6. inv H6. now auto. repeat normalize_ctx.
             apply bound_stem_comp_ctx_mut in H20. inv H20. now auto.
             inv H6. 2:{ inv H24. }
             assert (Hf2 := Decidable_name_in_fundefs f0). inv Hf2.
             specialize (Dec y). inv Dec.
             ++ apply H_sig_pre in H6'. destruct H6'. inv H22.
                left. eapply shrink_no_zombie.
                rewrite <- H13 in H14. eapply gsr_clos_trans. now eapply H14. eassumption.
                eassumption.
                (* violates unique_binding *)
                exfalso. rewrite <- H13 in H11. apply ub_app_ctx_f in H11. destructAll.
                inv H25. specialize (H26 y). apply H26. split.
                apply bound_stem_var. auto.
                constructor. apply bound_var_rename_all_ns_fundefs.
                apply name_in_fundefs_bound_var_fundefs. auto.
             ++ exfalso. apply H6. apply Hf0n.
                apply Included_name_in_fundefs_inlined with (im := im').
                simpl. apply name_in_fundefs_rename_all_ns in H24. auto.
          -- (* additional RW with Fun_dead_s on Fnil *)
             inv H6. split; [| split; [| split ] ]; eauto.
             ++ rewrite Nat.sub_0_r in Heqs1. replace (n0 + n1 + 1) with (0 + ((n0 + n1) + 1)) by lia. eapply gsr_clos_trans. eassumption.
                eapply gsr_clos_trans. eapply gsr_clos_trans. eassumption. eassumption.
                replace 1 with (1 + 0) by lia. eapply Trans_srw;[| now eapply Refl_srw  ]. constructor. constructor.
                now apply Forall_nil.
             ++ intro. specialize (Heqs2 v). apply num_occur_app_ctx in Heqs2. destructAll.
                apply num_occur_app_ctx. exists x, x0. inv H20. inv H28. split; auto.
                split; auto. rewrite Nat.add_0_r. auto.
             ++ eapply inl_inv_mon. 2: apply Heqs3.
                unfold ce'. do 2 (rewrite bound_var_app_ctx).
                repeat normalize_bound_var. now sets.
             ++ intro. intros. apply Heqs4 in H6.
                inv H6. rewrite H21 in H20. apply num_occur_app_ctx in H20.
                destructAll; pi0. inv H20; pi0. left.
                apply num_occur_app_ctx. exists 0, 0; auto. right.
                apply bound_stem_ctx_rename_all_ns.
                apply bound_stem_ctx_rename_all_ns in H20.
                normalize_ctx. apply bound_stem_comp_ctx_mut in H20.
                inv H20; auto. inv H6. inv H24. inv H24.
        * sets.
        * (* inl_inv pre post *)
          intro. intros. split.
          apply H16 in H21. destruct H21. apply H21. intros.
          assert (Hf := Decidable_name_in_fundefs f). inversion Hf. specialize (Dec f2). inversion Dec.
          -- destruct (get_b f2 inl) eqn:gf2i.
             ++ apply H4 in gf2i. destruct gf2i. apply H25 in H22.
                eapply Disjoint_Included_l. 2: now apply H22. eapply gsr_included_bv.
                eapply gsr_clos_trans. eassumption. eassumption.
             ++ (* this violates unique_binding *)
               exfalso. apply H3 in H22. clear H20. destructAll.
               apply ub_app_ctx_f in H0. destructAll. inv H22.
               specialize (H24 f2). apply H24. split.
               repeat normalize_ctx. apply bound_var_ctx_comp_ctx.
               right. simpl. constructor. rewrite inlined_fundefs_append.
               apply bound_var_rename_all_ns_fundefs.
               eapply fundefs_append_bound_vars. reflexivity.
               right. simpl. rewrite gf2i. constructor. auto.
               constructor. apply bound_var_rename_all_ns_fundefs.
               apply name_in_fundefs_bound_var_fundefs. auto.
          -- eapply H16. apply H21. erewrite <- H22.
             symmetry. eapply precontractfun_sig_nbv. apply Heqp'. apply H23.
        *(* sig_inv_full pre post *)
          apply sig_inv_combine. simpl. split; auto.
      + assert ((forall im, sub_inl_size c0 im <= funs_size f + sub_inl_size sub im /\ funs_size f0 <= funs_size f))%nat.
        { eapply precontractfun_size. eauto.  }
        unfold term_sub_inl_size. simpl. unfold term_sub_inl_size in H; simpl in H. specialize (H14 inl). lia.
      + (* sig_inv for rec call *)
        apply sig_inv_combine. split. auto.
        intro. intros. apply H_sig_pre in H14. inv H14.
        destruct H16. rewrite H13 in H14. auto. right.
        repeat normalize_ctx. now apply bound_stem_comp_ctx_mut; eauto.
    - (* app *)
      simpl in H6.
      destruct (get_c (apply_r sig v) count) eqn:garvc; [ | destruct n0].
      + (* dead fun -> impossible *)
        exfalso. specialize (H2 (apply_r sig v)). rewrite garvc in H2.
        unfold ce in H2. apply num_occur_app_ctx in H2.
        destructAll; pi0. simpl in H7. inv H7.
        destruct (term_util.var_dec (apply_r sig v) (apply_r sig v)).
        inv H13. now eauto.
      + (* only occ *)
        destruct (M.get (apply_r sig v) sub) eqn:garvs; [destruct s|].
        * (* constr, ill-typed but eh *)
          inv H6. unfold ce in *; unfold ce' in *.
          split; auto. simpl. eapply Refl_srw.
          split; auto. split; auto.
          simpl in H5. apply sig_inv_combine in H5. destruct H5. auto.
        * (* eligible to be inlined? *)
          destruct (andb (Pos.eqb f0 f) (andb (Init.Nat.eqb (List.length l) (List.length l0)) (negb (get_b (apply_r sig v) inl)))) eqn:Hel.
          { (* function inlining *)
            apply andb_true_iff in Hel. destruct Hel as (Hel1, Hel23).
            apply andb_true_iff in Hel23. destruct Hel23 as (Hel2, Hel3).
            apply Peqb_true_eq in Hel1. apply Nat.eqb_eq in Hel2. subst.
            assert (garvs' := garvs). apply H3 in garvs. destructAll. simpl in ce.
            (* sig v wasn't inlined before not dead *)
            assert (Hsvi : get_b (apply_r sig v) inl = false).
            { destruct (get_b (apply_r sig v) inl) eqn:gbvi.
              - (* impossible because not dead *)
                exfalso. apply H4 in gbvi. destructAll.
                apply not_bound_dead_or_free in H7. inv H7.
                2: apply H1 in H9; inv H9. apply num_occur_app_ctx in H9.
                destructAll; pi0.
                inv H9. rewrite peq_true in H15. inv H15.
              - reflexivity. }
            assert (H_inl_nbv : forall y,  In var (Union var [set apply_r sig v] (FromList l0)) y ->
                                           ~ bound_var_ctx (inlined_ctx_f (comp_ctx_f x (Efun1_c (fundefs_append x1 x2) x0)) inl) y).
            { intros. intro. apply ub_app_ctx_f in H0. destructAll.
              repeat normalize_ctx. apply ub_comp_ctx_f in H0. destructAll.
              simpl in H11. inv H11. rewrite inlined_fundefs_append in H16.
              rewrite rename_all_ns_fundefs_append in H16. eapply fundefs_append_unique_bindings_l in H16.
              2: reflexivity. destructAll. simpl in H13. rewrite Hsvi in H13.
              simpl in H13. inv H13. apply bound_var_ctx_comp_ctx in H8.
              inv H8. inv H12. specialize (H8 y). apply H8. split.
              apply bound_var_ctx_rename_all_ns. auto.
              apply bound_var_ctx_rename_all_ns. simpl. constructor.
              rewrite inlined_fundefs_append. eapply fundefs_append_bound_vars.
              reflexivity. right. simpl. rewrite Hsvi.
              now constructor.
              simpl in H13. inv H13.
              rewrite inlined_fundefs_append in H19.
              eapply fundefs_append_bound_vars in H19.
              2: reflexivity. inv H19.
              (* in x1 *)
              inv H14. specialize (H13 y). apply H13.
              split; auto.
              apply bound_var_rename_all_ns_fundefs. auto.
              simpl. rewrite Hsvi. simpl. constructor. auto.
              (* in x2 *)
              inv H7. apply H23. apply bound_var_rename_all_ns_fundefs. inv H13. auto.
              inv H25. specialize (H7 y). apply H7. split; auto.
              apply bound_var_rename_all_ns_fundefs. now auto.
              (* in x0 *)
              inv H17. specialize (H8 y). apply H8.
              split. apply bound_var_ctx_rename_all_ns.
              auto. apply bound_var_rename_all_ns_fundefs.
              rewrite inlined_fundefs_append. eapply fundefs_append_bound_vars.
              reflexivity. right. simpl; rewrite Hsvi.
              constructor.  auto. }

            assert (rename_all_ctx_ns sig
                                      (inlined_ctx_f
                                         (comp_ctx_f x
                                                     (Efun1_c
                                                        (fundefs_append x1 (Fcons (apply_r sig v) f l0 e x2)) x0))
                                         inl) |[ Eapp (apply_r sig v) f (apply_r_list sig l) ]| =
                                                                                                (rename_all_ctx_ns sig (inlined_ctx_f x inl)) |[
                      Efun (fundefs_append (rename_all_fun_ns sig (inlined_fundefs_f x1 inl)) (Fcons (apply_r sig v) f l0 (rename_all_ns sig e) (rename_all_fun_ns sig (inlined_fundefs_f x2 inl)))) (rename_all_ctx_ns sig (inlined_ctx_f x0 inl) |[ Eapp (apply_r sig v) f (apply_r_list sig l)  ]|)
                    ]|).
            { ctx_inl_push. rewrite inlined_fundefs_append.
              rewrite rename_all_ns_fundefs_append. simpl. rewrite Hsvi. auto. }

            assert (H_inl_ctx: (rename_all_ctx_ns (set_list (combine l0 (apply_r_list sig l)) sig)
                                                  (inlined_ctx_f (comp_ctx_f x (Efun1_c (fundefs_append x1 x2) x0))
                                                                 (M.set (apply_r sig v) true inl)) =
                                (rename_all_ctx_ns (set_list (combine l0 (apply_r_list sig l)) sig)
                                                   (inlined_ctx_f (comp_ctx_f x (Efun1_c (fundefs_append x1 (Fcons (apply_r sig v) f l0 e x2)) x0))
                                                                  (M.set (apply_r sig v) true inl))))).
            { repeat normalize_ctx. simpl. do 2 (rewrite inlined_fundefs_append).
              simpl. unfold get_b. rewrite M.gss. reflexivity. }


            assert (Hdjl0 : Disjoint _ (name_in_fundefs
                                          (rename_all_fun_ns sig
                                                             (inlined_fundefs_f
                                                                (fundefs_append x1 (Fcons (apply_r sig v) f l0 e x2)) inl))) (FromList l0)).
            { apply ub_app_ctx_f in H0; destructAll. repeat normalize_ctx.
              apply ub_comp_ctx_f in H0; destructAll. simpl in H10. inv H10. rewrite inlined_fundefs_append in H15.
              rewrite rename_all_ns_fundefs_append in H15. eapply fundefs_append_unique_bindings_l in H15.
              2: reflexivity.
              destructAll. split. intro. intro. inv H15. rewrite fundefs_append_name_in_fundefs in H17.
              2: reflexivity. inv H17. inv H13. specialize (H17 x3).
              apply H17. split. apply name_in_fundefs_bound_var_fundefs.
              auto. simpl. rewrite Hsvi. simpl. constructor. auto.
              simpl in H15. rewrite Hsvi in H15.
              simpl in H15. simpl in H12. rewrite Hsvi in H12.
              inv H12. inv H15. apply H28. inv H12; auto.
              inv H26. specialize (H15 x3).
              apply H15. split.
              apply name_in_fundefs_bound_var_fundefs. auto. auto. }

            assert (H8  := H_inl_nbv).

            assert (H_dead_l0 :
                      forall x3, FromList l0 x3 ->
                                 x3 \in (dead_var_ctx (inlined_ctx_f (comp_ctx_f x (Efun1_c (fundefs_append x1 x2) x0)) inl))).
            { assert (H9 := true).
              (* show that x3 cannot be in the Dom of sig *)
              intros.
              assert (~ (Dom_map sig x3)).
              { intro. inv H11. apply H5 in H12. destructAll.
                apply H11. apply bound_var_app_ctx. left.
                repeat normalize_ctx. apply bound_var_ctx_comp_ctx.
                right. simpl. constructor. apply bound_var_rename_all_ns_fundefs.
                rewrite inlined_fundefs_append. eapply fundefs_append_bound_vars. reflexivity.
                right. simpl. rewrite Hsvi. constructor. right. auto. }

              (* show that it cannot be in x, x1, x2 or x0 *)
              repeat normalize_ctx.
              assert ( ~ bound_var_ctx
                         (comp_ctx_f (inlined_ctx_f x inl)
                                     (inlined_ctx_f (Efun1_c (fundefs_append x1 x2) x0) inl)) x3) by (apply H8; auto).
              clear H8.
              apply num_occur_ec_comp_ctx. exists 0, 0; auto. split; [| split; [| lia ]].
              - (* x *)
                assert (~ bound_var_ctx (rename_all_ctx_ns sig (inlined_ctx_f x inl)) x3).
                intro; apply H12. apply bound_var_ctx_rename_all_ns in H8.
                apply bound_var_ctx_comp_ctx. auto.
                eapply not_occur_rename_ctx_not_dom. apply H11.
                apply closed_not_occurs_in_context; auto.
                unfold ce in H1. simpl in H1.
                repeat normalize_ctx. rewrite <- app_ctx_f_fuse in H1.
                apply closed_app_ctx in H1. auto.
              - unfold ce in H1. repeat normalize_ctx.
                rewrite <- app_ctx_f_fuse in H1.
                assert (~ occurs_free (rename_all_ctx_ns sig
                                                         (inlined_ctx_f
                                                            (Efun1_c
                                                               (fundefs_append x1 (Fcons (apply_r sig v) f l0 e x2)) x0)
                                                            inl) |[ Eapp (apply_r sig v) f (apply_r_list sig l) ]|) x3).
                { eapply not_occurs_free_ctx_not_bound. intro. apply H1 in H8. inv H8.
                  intro. apply H12. apply bound_var_ctx_comp_ctx. left.
                  apply bound_var_ctx_rename_all_ns in H8. auto. }
                simpl in H8. apply not_occur_free_Efun in H8. inv H8.
                rewrite inlined_fundefs_append in H13. rewrite rename_all_ns_fundefs_append in H13.
                apply not_occurs_free_fundefs_append in H13. inv H13.
                rewrite inlined_fundefs_append in H14. rewrite rename_all_ns_fundefs_append in H14.
                assert (H8' :
                          In var
                             (Complement var (occurs_free_fundefs
                                                (rename_all_fun_ns sig (inlined_fundefs_f x1 inl)))) x3).
                { intro. apply H8. split; auto. intro. inv Hdjl0. specialize (H17 x3). apply H17; auto. }
                clear H8.
                assert (H14' :
                          In var
                             (Complement var
                                         (occurs_free
                                            (rename_all_ctx_ns sig (inlined_ctx_f x0 inl)
                                            |[ Eapp (apply_r sig v) f (apply_r_list sig l) ]|))) x3).
                { intro. apply H14. split; auto. intro. inv Hdjl0. specialize (H16 x3). apply H16; auto. } clear H14.
                assert (H15' :
                          In var
                             (Complement var
                                         (occurs_free_fundefs
                                            (rename_all_fun_ns sig
                                                               (inlined_fundefs_f (Fcons (apply_r sig v) f l0 e x2)
                                                                                  inl)))) x3).
                { intro. apply H15. split; auto. intro. inv Hdjl0. specialize (H14 x3). apply H14; auto. } clear H15.
                eapply Complement_Proper in H15'.
                2:{ simpl. rewrite Hsvi. simpl. symmetry. apply occurs_free_fundefs_Fcons. }
                assert (H15'' : In var (Complement var
                                                 (occurs_free_fundefs
                                                    (rename_all_fun_ns sig (inlined_fundefs_f x2 inl)))) x3).
                { intro. apply H15'. right. split; auto.
                  intro. inv Hdjl0. specialize (H14 x3). apply H14. split; auto.
                  eapply fundefs_append_name_in_fundefs. reflexivity.
                  right. simpl. rewrite Hsvi. simpl. constructor. auto. }
                clear H15'. apply not_free_dead_or_bound in H14'. inv H14'.
                2:{ exfalso. apply H12. apply bound_var_app_ctx in H8. inv H8.
                    apply bound_var_ctx_comp_ctx. right. simpl. apply identifiers.Bound_Fun12_c.
                    apply bound_var_ctx_rename_all_ns in H13. auto. inv H13. }

                apply not_free_bound_or_not_occur in H8'. inv H8'.
                2:{ exfalso. apply H12. apply bound_var_ctx_comp_ctx.
                    right. constructor. rewrite inlined_fundefs_append.
                    apply bound_var_rename_all_ns_fundefs in H13.
                    eapply fundefs_append_bound_vars.
                    reflexivity. left; auto. }

              apply not_free_bound_or_not_occur in H15''. inv H15''.
              2:{ exfalso. apply H12. apply bound_var_ctx_comp_ctx.
                  right. constructor. rewrite inlined_fundefs_append.
                  apply bound_var_rename_all_ns_fundefs in H14.
                  eapply fundefs_append_bound_vars.
                  reflexivity. auto. }
              simpl. apply num_occur_app_ctx in H8; destructAll; pi0.
              apply not_occur_rename_ctx_not_dom in H8; auto.
              apply not_occur_rename_fun_not_dom in H13; auto.
              apply not_occur_rename_fun_not_dom in H14; auto.
              eapply num_occur_ec_n. constructor. apply H8.
              rewrite inlined_fundefs_append.  eapply fundefs_append_num_occur.
              reflexivity. now apply H13. now apply H14. lia. }

            assert (H_rn_ctx: rename_all_ctx_ns (set_list (combine l0 (apply_r_list sig l)) sig)
                                                (inlined_ctx_f (comp_ctx_f x (Efun1_c (fundefs_append x1 x2) x0))
                                                               inl) =
                              (rename_all_ctx_ns sig
                                                 (inlined_ctx_f (comp_ctx_f x (Efun1_c (fundefs_append x1 x2) x0)) inl))).
            { apply eq_P_rename_all_ctx_ns. intro. intro. assert (Hl0 := Decidable_FromList l0).
              inv Hl0. specialize (Dec x3). inv Dec.
              - exfalso. apply H9. apply H_dead_l0; auto.
              - apply eq_P_set_list_not_in. auto. } clear H8.

            assert (
                gsr_clos 1
                  (rename_all_ctx_ns sig (inlined_ctx_f x inl)
                  |[ Efun (fundefs_append (rename_all_fun_ns sig (inlined_fundefs_f x1 inl))
                                          (Fcons (apply_r sig v) f l0 (rename_all_ns sig e)
                                                 (rename_all_fun_ns sig (inlined_fundefs_f x2 inl))))
                          (rename_all_ctx_ns sig (inlined_ctx_f x0 inl) |[ Eapp (apply_r sig v) f (apply_r_list sig l) ]|) ]|)

                  (rename_all_ctx_ns (set_list (combine l0 (apply_r_list sig l)) sig)
                                     (inlined_ctx_f (comp_ctx_f x (Efun1_c (fundefs_append x1 (Fcons (apply_r sig v) f l0 e x2)) x0))
                                                    (M.set (apply_r sig v) true inl))
                  |[ rename_all_ns (set_list (combine l0 (apply_r_list sig l)) sig) e ]|)).
            { replace 1 with (1 + 0) by lia. eapply gsr_clos_trans.
              replace 1 with (1 + 0) by lia. econstructor; [| now constructor ]. constructor.
              apply Fun_inline_s.
              - rewrite length_apply_r_list. auto.
              - specialize (H2 (apply_r sig v)). rewrite garvc in H2.
                unfold ce in H2. rewrite H7 in H2.
                apply num_occur_app_ctx in H2. destructAll.
                (* x3 = 0 *)
                assert ( ~ bound_var_ctx (rename_all_ctx_ns sig (inlined_ctx_f x inl)) (apply_r sig v)).
                { (** by UB *) intro.
                  unfold ce in H0. rewrite H7 in H0. apply ub_app_ctx_f in H0. destructAll.
                  inv H12. specialize (H13 (apply_r sig v)). apply H13. split. auto. constructor.
                  eapply fundefs_append_bound_vars. reflexivity.
                  right. constructor. constructor. auto. }
                apply not_bound_dead_or_free_ctx in H10.
                inv H10. assert (x3 = 0). eapply num_occur_ec_det; eauto.
                subst. simpl in H9. rewrite H9; auto.
                (** cannot be free since closed so dead *)
                exfalso. eapply occurs_free_included_ctx in H11.
                unfold ce in H1. rewrite H7 in H1. apply H1 in H11.
                inv H11.
              - rewrite <- H_inl_ctx.
                (* should that (apply_r sig v) and l0 is not bound in x, x1, x2 and x0 s.t. cannot occur *)
                assert (H8 := H_inl_nbv). clear H_inl_nbv. rewrite inlined_ctx_f_staged.
                rewrite Disjoint_inlined_ctx with (im := (M.set (apply_r sig v) true (M.empty bool))).
                2:{ split. intro. intro. inv H9. inv H11.
                    revert H10. apply H8. constructor. unfold get_b in H12. destruct (var_dec x3 (apply_r sig v)).
                    subst; auto. rewrite M.gso in H12. rewrite M.gempty in H12. inv H12. auto. }

                rewrite H_rn_ctx. rewrite (proj1 (set_list_rename_all_ns _ _)).
                repeat normalize_ctx. rewrite <- app_ctx_f_fuse. simpl.
                rewrite inlined_fundefs_append. rewrite rename_all_ns_fundefs_append.
                now constructor 2.
                { (* l0 can be staged for sig *)
                  intro. intro.
                  assert (Decidable (Range_map sig)) by apply Decidable_Range_map.
                  inv H10. specialize (Dec x3). inv Dec.
                  2: now left; auto.

                  inv H10. apply H5 in H11. inv H11. inv H12.
                  - right. repeat normalize_ctx.
                    apply num_occur_app_ctx in H11; destructAll; pi0.
                    apply num_occur_ec_comp_ctx in H11; destructAll; pi0.
                    simpl in H13. inv H13; pi0. rewrite inlined_fundefs_append in H19.
                    rewrite rename_all_ns_fundefs_append in H19.
                    apply fundefs_append_num_occur' in H19; destructAll; pi0.
                    simpl in H14. rewrite Hsvi in H14.
                    simpl in H14. inv H14; pi0. auto.
                  - exfalso. (* this violates unique_binding (can use H8 and fact that apply_r sig v <> x3 \in l0 *)
                    unfold ce in H0.
                    repeat normalize_ctx.
                    apply ub_app_ctx_f in H0. destructAll.
                    apply ub_comp_ctx_f in H0. destructAll.

                    apply bound_stem_comp_ctx_mut in H11. inv H11.
                    inv H15. specialize (H11 x3). apply H11. split.
                    apply bound_stem_var. auto. simpl. constructor.
                    apply bound_var_rename_all_ns_fundefs.
                    rewrite inlined_fundefs_append. eapply fundefs_append_bound_vars.
                    reflexivity. right.
                    simpl. rewrite Hsvi. constructor. auto. simpl in H16. inv H16.
                    apply name_in_fundefs_rename_all_ns in H19.
                    rewrite inlined_fundefs_append in H19. eapply fundefs_append_name_in_fundefs in H19.
                    2: reflexivity. inv H14. rewrite inlined_fundefs_append in H18.
                    rewrite rename_all_ns_fundefs_append in H18. eapply fundefs_append_unique_bindings_l in H18.
                    2: reflexivity. destructAll. inv H19.
                    (* not a name of x1 *)
                    inv H16. specialize (H19 x3). apply H19. split. apply bound_var_rename_all_ns_fundefs.
                    apply name_in_fundefs_bound_var_fundefs. auto. simpl. rewrite Hsvi. constructor. auto.

                    simpl in H14. rewrite Hsvi in H14. inv H14.
                    simpl in H18. rewrite Hsvi in H18. inv H18.
                    inv H14; auto.
                    inv H28. specialize (H18 x3).
                    apply H18. split; auto. apply name_in_fundefs_bound_var_fundefs.
                    apply name_in_fundefs_rename_all_ns. auto.
                    inv H14.
                    inv H20. specialize (H11 x3). apply H11. split.
                    apply bound_stem_var. auto. apply bound_var_rename_all_ns_fundefs. rewrite inlined_fundefs_append.
                    eapply fundefs_append_bound_vars. reflexivity.
                    right. simpl. rewrite Hsvi. constructor. auto. }
                (* by sig_inv_dom *)
                split; intro. intro.
                inv H9. inv H11. apply H5 in H9. destruct H9. apply H9.
                apply bound_var_app_ctx. left. repeat normalize_ctx.
                apply bound_var_ctx_comp_ctx. right. simpl. constructor.
                apply bound_var_rename_all_ns_fundefs. rewrite inlined_fundefs_append.
                eapply fundefs_append_bound_vars. reflexivity.
                right. simpl. rewrite Hsvi. constructor. auto.
            }
            (* simplify the context for the hyp of the IH *)
            assert (H_inl_simpl:
                      (rename_all_ctx_ns (set_list (combine l0 (apply_r_list sig l)) sig)
                                         (inlined_ctx_f
                                            (comp_ctx_f x
                                                        (Efun1_c
                                                           (fundefs_append x1 (Fcons (apply_r sig v) f l0 e x2)) x0))
                                            (M.set (apply_r sig v) true inl))) =
                      (rename_all_ctx_ns sig
                                         (inlined_ctx_f
                                            (comp_ctx_f x
                                                        (Efun1_c
                                                           (fundefs_append x1 x2) x0))
                                            inl)
                      )).
            { rewrite <- H_inl_ctx.
              rewrite inlined_ctx_f_staged.
              rewrite Disjoint_inlined_ctx with (im := (M.set (apply_r sig v) true (M.empty bool))).
              rewrite H_rn_ctx. reflexivity. split. intro. intro. inv H9. inv H11.
              revert H10. apply H_inl_nbv. constructor. unfold get_b in H12.
              destruct (var_dec x3 (apply_r sig v)).
              subst; auto. rewrite M.gso in H12. rewrite M.gempty in H12. inv H12.
              auto.
            }

            remember (contract (set_list (combine l0 (apply_r_list sig l)) sig)
                               (update_count_inlined (apply_r_list sig l) l0
                                                     (M.set (apply_r sig v) 0 count)) e sub
                               (M.set (apply_r sig v) true inl)) as Hc.
            destruct Hc. destruct x3. destruct p. destruct p.
            symmetry in HeqHc. rewrite <- H7 in H8.
            assert (Hinc := gsr_clos_preserves_clos _ _ _ H0 H1 H8). destruct Hinc as (Hin_ub, Hin_cl).
            apply sig_inv_combine in H5. destruct H5 as (H5, H5co).
            assert (Hse := gsr_preserves_sig_dom _ _ _ _ H0 (closed_implies_Disjoint _ H1) H8 H5).
            eapply IHn with (c :=  (comp_ctx_f x
                                               (Efun1_c
                                                  (fundefs_append x1 (Fcons (apply_r sig v) f l0 e x2)) x0))) in HeqHc; auto.
            - inv H6.
              destructAll.
              assert (H_rn_ctx': rename_all_ctx_ns (set_list (combine l0 (apply_r_list sig l)) sig)
                                                   (inlined_ctx_f
                                                      (comp_ctx_f x
                                                                  (Efun1_c
                                                                     (fundefs_append x1 (Fcons (apply_r sig v) f l0 e x2)) x0))
                                                      im') =
                                 rename_all_ctx_ns  sig
                                                    (inlined_ctx_f
                                                       (comp_ctx_f x
                                                                   (Efun1_c
                                                                      (fundefs_append x1 (Fcons (apply_r sig v) f l0 e x2)) x0))
                                                     im')).
              { apply eq_P_rename_all_ctx_ns. intro. intro.
                assert (Hl0 := Decidable_FromList l0). inv Hl0. specialize (Dec x3). inv Dec.
                exfalso. apply H12.
                (* show that x3 cannot be in the Dom of sig *)
                assert (~ (Dom_map sig x3)).
                intro. inv H14. apply H5 in H15. apply H15. apply bound_var_app_ctx. left.
                repeat normalize_ctx. apply bound_var_ctx_comp_ctx.
                right. simpl. constructor. apply bound_var_rename_all_ns_fundefs.
                rewrite inlined_fundefs_append. eapply fundefs_append_bound_vars. reflexivity.
                right. simpl. rewrite Hsvi. constructor. right. auto.
                assert ( (inlined_ctx_f
                            (comp_ctx_f x
                                        (Efun1_c (fundefs_append x1 (Fcons (apply_r sig v) f l0 e x2))
                                                 x0)) im') =
                         (inlined_ctx_f
                            (comp_ctx_f x
                                        (Efun1_c (fundefs_append x1 x2)
                                                 x0)) im')).
                { repeat normalize_ctx. simpl. rewrite inlined_fundefs_append. simpl.
                  assert (get_b (apply_r sig v) im' = true).
                  { apply b_map_le_c in b.  apply b.
                    unfold get_b. rewrite M.gss. auto. }
                  rewrite H15. rewrite inlined_fundefs_append. auto. }

                rewrite H15. clear H15. eapply dead_occur_ec_le_antimon.
                simpl in BP. apply b_map_le_c. apply BP. apply H_dead_l0; auto.
                apply eq_P_set_list_not_in. auto. }

              split; [| split; [| split ]].
              + rewrite Nat.add_comm. eapply gsr_clos_trans. eassumption.
                unfold ce'. rewrite <- H_rn_ctx'. now apply H6.
              + unfold ce'. rewrite <- H_rn_ctx'. auto.
              + unfold ce'. rewrite <- H_rn_ctx'. auto.
              + (* inl for returned app inlined case *)
                intro. intros.
                (* x3 in l0 is dead, not in l0 is same as H11 *)
                assert (Hl0 := Decidable_FromList l0).
                inv Hl0. specialize (Dec x3).
                inv Dec.
                * exfalso. (* impossible since bound in the original term *)
                  apply H5 in H12.
                  apply H12. repeat normalize_ctx.
                  apply bound_var_app_ctx. left.
                  apply bound_var_ctx_comp_ctx. right.
                  apply bound_var_ctx_rename_all_ns.
                  simpl. constructor. rewrite inlined_fundefs_append.
                  eapply fundefs_append_bound_vars.
                  reflexivity. right. simpl. rewrite Hsvi.
                  constructor. auto.
                * rewrite H_rn_ctx' in H11.
                  eapply H11. rewrite <- H12.
                  rewrite get_set_list2. reflexivity. auto.
            - (* term size for IH *)
              unfold term_sub_inl_size in *; simpl in *.
              apply sub_inl_fun_size with (im := inl) in garvs'. lia.
              apply negb_true_iff. auto.
            - (* c_count for app inlined case *)
              rewrite H_inl_simpl.
              eapply count_inlining; eauto.
              apply sig_inv_combine; auto.
              specialize (H2 (apply_r sig v)). rewrite garvc in H2. auto.
            - (* inl for app inlined case *)
              intro. intro.
              destruct (var_dec f0 (apply_r sig v)).
              + subst. split. intro.
                * (* this would violate unique_bindings *)
                  rewrite H_inl_simpl in H10.
                  apply bound_var_app_ctx in H10. inv H10.
                  ++ apply bound_var_ctx_rename_all_ns in H11.
                     revert H11. apply H_inl_nbv. auto.
                  ++ (* violates unique binding *)
                    apply bound_var_rename_all_ns in H11.
                    apply ub_app_ctx_f in H0; destructAll.
                    repeat normalize_ctx.
                    apply ub_comp_ctx_f in H0; destructAll.
                    simpl in H13. inv H13. repeat normalize_ctx.
                    eapply fundefs_append_unique_bindings_l in H18.
                    2: reflexivity. destructAll.
                    simpl in H15. rewrite Hsvi in H15.
                    inv H15. apply H24.
                    apply bound_var_rename_all_ns; auto.
                * intros. rewrite H10 in garvs'. inv garvs'.
                  split. intro. intro. inv H11.
                  apply bound_var_app_ctx in H12. inv H12.
                  -- rewrite H_inl_simpl in H11.
                     apply bound_var_ctx_rename_all_ns in H11.
                     revert H11.
                     apply H_inl_nbv. auto.
                  -- (* violates unique binding *)
                    apply bound_var_rename_all_ns in H11.
                    apply ub_app_ctx_f in H0; destructAll.
                    repeat normalize_ctx.
                    apply ub_comp_ctx_f in H0; destructAll.
                    simpl in H15. inv H15. repeat normalize_ctx.
                    eapply fundefs_append_unique_bindings_l in H20.
                    2: reflexivity. destructAll.
                    simpl in H17. rewrite Hsvi in H17.
                    inv H17. inv H28.
                    specialize (H17 x3).
                    apply H17. split.
                    apply bound_var_rename_all_ns; auto. auto.
              + (* not bound var *)
                unfold get_b in H9. rewrite M.gso in H9 by auto.
                apply H4 in H9. destruct H9. split; intro; intros.
                * apply H9. unfold ce.
                  apply bound_var_app_ctx. left.
                  apply bound_var_app_ctx in H11.
                  apply  bound_var_ctx_rename_all_ns.
                  inv H11.
                  -- apply  bound_var_ctx_rename_all_ns in H12.
                     eapply bound_var_ctx_inlined_antimon.
                     apply b_map_le_true. apply H12.
                  -- apply bound_var_rename_all_ns in H12.
                     repeat normalize_ctx.
                     apply bound_var_ctx_comp_ctx.
                     right. simpl. constructor.
                     rewrite inlined_fundefs_append.
                     eapply fundefs_append_bound_vars.
                     reflexivity. right. simpl. rewrite Hsvi.
                     constructor 3. auto.
                * apply H10 in H11. eapply Disjoint_Included_l.
                  2: apply H11. unfold ce. do 2 (rewrite bound_var_app_ctx).
                  repeat normalize_bound_var. do 2 (rewrite <- (proj1 (bound_var_ctx_rename_all_ns _))).
                  rewrite Union_Empty_set_neut_r. apply Union_Included.
                  apply bound_var_ctx_inlined_antimon. apply b_map_le_true.
                  rewrite <- bound_var_rename_all_ns. repeat normalize_ctx.
                  rewrite (proj1 bound_var_ctx_comp_ctx). simpl. rewrite inlined_fundefs_append. simpl.
                  rewrite Hsvi. normalize_bound_var_ctx. intro. intro. right. left.
                  eapply fundefs_append_bound_vars. reflexivity. right. constructor 3. eauto.
            - (* sig for app inline  case *)
              rewrite H_inl_simpl. rewrite H_inl_simpl in Hse.
              intro; intros. assert (Decidable (FromList l0)) by apply Decidable_FromList. inv H10.
              (* either x3 is in l0 or not *)
              specialize (Dec x3). inv Dec.
              + (* x3 is from l0 *)
                (* then dom ->  dead OK,  *)
                split.
                * intro. apply bound_var_app_ctx in H11.
                  inv H11. apply bound_var_ctx_rename_all_ns in H12. revert H12.
                  apply H_inl_nbv. auto.
                  (** by UB *)
                  apply bound_var_rename_all_ns in H12.
                  apply ub_app_ctx_f in H0. destructAll.
                  repeat normalize_ctx.
                  apply ub_comp_ctx_f in H0. destructAll.
                  simpl in H14. inv H14. repeat normalize_ctx.
                  eapply fundefs_append_unique_bindings_l in H19.
                  2: reflexivity. destructAll.
                  simpl in H16. rewrite Hsvi in H16. inv H16.
                  inv H27. specialize (H16 x3). apply H16. split; auto.
                  apply bound_var_rename_all_ns. auto.
                  (* codom has to be bound on stem due to closed and occur before *)
                  (* bound on stem due to occurs_free_app_bound_stem *)
                * assert ( List.In y (apply_r_list sig l)).
                  eapply FromList_set_list. apply H9.
                  rewrite length_apply_r_list. auto. auto.
                  assert (occurs_free (rename_all_ns sig (Eapp v f l)) y).
                  simpl. constructor. auto.
                  assert (~ occurs_free ce y).
                  intro. apply H1 in H13. inv H13.
                  eapply  occurs_free_app_bound_stem in H12.
                  inv H12. clear H15. specialize (H14 _ H13).
                  right. repeat normalize_ctx.
                  apply bound_stem_comp_ctx_mut in H14. apply bound_stem_comp_ctx_mut.
                  inv H14; auto. simpl. simpl in H12. right. inv H12.
                  constructor. rewrite inlined_fundefs_append.
                  rewrite inlined_fundefs_append in H17. apply name_in_fundefs_rename_all_ns.
                  apply name_in_fundefs_rename_all_ns in H17.
                  eapply fundefs_append_name_in_fundefs. reflexivity.
                  eapply fundefs_append_name_in_fundefs in H17. 2: reflexivity.
                  inv H17; auto. simpl in H12. rewrite Hsvi in H12. inv H12.
                  (* apply_r sig l <> apply_r sig v because occ only once *)
                  exfalso. inv H14. specialize (H2 (apply_r sig v)). rewrite garvc in H2.
                  apply num_occur_app_ctx in H2. destructAll. inv H12.
                  simpl in H14.
                  destruct (term_util.var_dec (apply_r sig v) (apply_r sig v)); auto.
                  assert (num_occur_list (apply_r_list sig l) (apply_r sig v) = 0) by lia.
                  apply not_occur_list in H12. now auto. now auto. now auto.
              + (* x3 is not from l0 *)
                rewrite eq_P_set_list_not_in in H9 by auto. split.
                * apply Hse in H9. auto.
                * apply H5co in H9.
                  inv H9.
                  -- left.
                     apply num_occur_app_ctx in H11; destructAll; pi0.
                     repeat normalize_ctx.
                     apply num_occur_ec_comp_ctx in H9; destructAll; pi0.
                     simpl in H12. inv H12; pi0.
                     repeat normalize_ctx.
                     apply fundefs_append_num_occur' in H18; destructAll; pi0.
                     simpl in H13. rewrite Hsvi in H13.
                     simpl in H13. inv H13; pi0.
                     simpl.
                     apply num_occur_app_ctx. exists 0, 0; auto.
                     split; auto.
                     ++ apply num_occur_ec_comp_ctx. exists 0, 0; auto. split; auto. split; auto.
                        eapply num_occur_ec_n. constructor; eauto.
                        repeat normalize_ctx.
                        eapply fundefs_append_num_occur; eauto. lia.
                     ++ split; auto.
                        apply dead_occur_rename_all_ns_set_list. inv H11; pi0; dec_vars.
                        apply not_occur_list. auto. auto.
                  -- destruct (var_dec y (apply_r sig v)).
                     (* then dead *)
                     left. specialize (H2 (apply_r sig v)).
                     rewrite garvc in H2. apply num_occur_app_ctx in H2. destructAll.
                     inv H9. simpl in H12. destruct (term_util.var_dec (apply_r sig v) (apply_r sig v)).
                     2: exfalso; auto.
                     assert (x4 = 0) by lia.
                     assert (num_occur_list (apply_r_list sig l) (apply_r sig v) = 0) by lia.
                     clear H12. subst.
                     repeat normalize_ctx.
                     apply num_occur_ec_comp_ctx in H2; destructAll; pi0; dec_vars.
                     simpl in H9. inv H9; pi0.
                     repeat normalize_ctx. apply fundefs_append_num_occur' in H18. destructAll; pi0.
                     simpl in H12. rewrite Hsvi in H12. inv H12; destructAll; pi0.
                     simpl. eapply num_occur_n. apply num_occur_app_ctx.
                     exists 0, 0. split.
                     apply num_occur_ec_comp_ctx. exists 0, 0; auto.
                     split; auto. split.
                     eapply num_occur_ec_n. constructor; eauto.
                     repeat normalize_ctx.
                     eapply fundefs_append_num_occur. reflexivity.
                     eauto. eauto. auto. auto.
                     split.
                     apply dead_occur_rename_all_ns_set_list.
                     apply not_occur_list. auto. auto.
                     reflexivity. now auto.

                     right.
                     apply bound_stem_ctx_rename_all_ns.
                     apply bound_stem_ctx_rename_all_ns in H11.
                     repeat normalize_ctx.
                     apply bound_stem_comp_ctx_mut in H11.
                     apply bound_stem_comp_ctx_mut.
                     inv H11; auto. simpl. simpl in H9. right. inv H9.
                     constructor. rewrite inlined_fundefs_append.
                     rewrite inlined_fundefs_append in H14.
                     eapply fundefs_append_name_in_fundefs. reflexivity.
                     eapply fundefs_append_name_in_fundefs in H14.
                     2: reflexivity. inv H14; auto.
                     simpl in H9. rewrite Hsvi in H9.
                     simpl in H9. inv H9; auto.
                     exfalso. apply n1; inv H11; auto. auto. }
          (* not eligible to be inlined *)
          inv H6.
          unfold ce in *; unfold ce' in *.
          split; auto. simpl. now constructor.
          apply sig_inv_combine in H5. destruct H5. simpl in H6. split; auto.
        * (* not a known function *)
          inv H6. unfold ce in *; unfold ce' in *.
          split; auto. simpl. apply Refl_srw.
          apply sig_inv_combine in H5. destruct H5. simpl in H6. split; auto.
      + (* multiple occ *)
        inv H6. unfold ce in *; unfold ce' in *.
        split; auto. simpl. apply Refl_srw.
        apply sig_inv_combine in H5. destruct H5. simpl in H6. split; auto.
    - simpl in H6.
      assert ( rename_all_ctx_ns sig (inlined_ctx_f c inl)
            |[ rename_all_ns sig (Eprim_val v p e) ]| =
                                                    rename_all_ctx_ns sig (inlined_ctx_f (comp_ctx_f c (Eprim_val_c v p Hole_c)) inl) |[ rename_all_ns sig e ]|) by ctx_inl_push.
      remember (contract sig count e sub inl ) as s.
      destruct s as [[[[? ? ] ? ] ? ] ? ]. symmetry in Heqs.
      eapply  IHn with (c := (comp_ctx_f c (Eprim_val_c v p Hole_c))) in Heqs; try (rewrite <- H7; eauto).
      3: (apply cmap_view_prim_val; auto).
      assert ((rename_all_ctx_ns sig
                                (inlined_ctx_f (comp_ctx_f c (Eprim_val_c v p Hole_c)) im') |[ e0 ]|) =
              (rename_all_ctx_ns sig
                                (inlined_ctx_f c im') |[ Eprim_val v p e0 ]|)) by ctx_inl_push.
      inv H6.
      destruct Heqs as (H6, (H9, (H11, Hsig_r))).

      unfold ce; unfold ce'.
      rewrite H7.
      rewrite H8 in *.
      split; auto. split; auto. split; auto.
      intro. intros. assert (H10' := H10).

      apply Hsig_r in H10. inv H10.
      left. repeat normalize_ctx.
      apply num_occur_app_ctx in H12. destructAll; pi0.
      apply num_occur_ec_comp_ctx in H10. destructAll; pi0.
      simpl in H13. inv H13; pi0.
      apply num_occur_app_ctx. exists 0, 0.
      split; auto. split. eapply num_occur_n.
      constructor; eauto. auto. auto.

      destruct (var_dec v y).
      apply H5 in H10'. inv H10'. inv H13.
      (* by no zombie *)
      left. eapply shrink_no_zombie. apply H6. rewrite <- H7. auto.
      (* impossible by unique binding *)
      exfalso. apply ub_app_ctx_f in H0. destructAll. inv H15. specialize (H16 y).
      apply H16. split. apply bound_stem_var.  auto. simpl. constructor.
      right. repeat normalize_ctx.
      apply bound_stem_comp_ctx_mut in H12. inv H12. auto.
      exfalso.
      simpl in H10. inv H10. now eauto. now inv H16.


      unfold term_sub_inl_size in *.
      simpl in H.
      simpl. lia.
      {
        simpl in H5.
        rewrite inv_app_Eprim_val in H5.
        apply sig_inv_full_push in H5.
        rewrite (proj1 inlined_comp_ctx).
        rewrite (proj1 (rename_all_ctx_ns_comp_ctx _ _)).
        simpl; auto.
      }
    - (* prim *)
      (* destruct (get_c v count) eqn:gvc. *)
      (* { (* dead prim *) *)
      (*   assert (gsr_clos 1 ce *)
      (*                    (rename_all_ctx_ns sig (inlined_ctx_f c inl) *)
      (*                    |[ rename_all_ns sig  e ]| )). *)
      (*   { *)
      (*     unfold ce. replace 1 with (1 + 0). econstructor. constructor. *)
      (*     simpl. apply Prim_dead_s. *)
      (*     specialize (H2 v). rewrite gvc in H2. *)
      (*     apply num_occur_app_ctx in H2. *)
      (*     destructAll; pi0. *)
      (*     inv H7; pi0. rewrite H8. simpl. auto. *)
      (*     now constructor. reflexivity.  *)
      (*   } *)
      (*   assert (Hub' := gsr_clos_preserves_clos _ _ _ H0 H1 H7). destruct Hub'. *)
      (*   apply sig_inv_combine in H5. destruct H5. *)
      (*   assert (Hse := gsr_preserves_sig_dom _ _ _ _ H0 (closed_implies_Disjoint _ H1) H7 H5). *)
      (*   unfold incr_steps in H6. simpl in H6. *)
      (*   remember (contract sig (dec_census_list sig l count) e sub inl) as s.  destruct s as [[[[? ?] ?] ?] ?]. inv H6. *)
      (*   symmetry in Heqs. simpl in ce. eapply IHn with (c := c) in Heqs. destructAll. *)
      (*   split; auto. *)
      (*   rewrite Nat.add_comm. eapply gsr_clos_trans. eassumption. eassumption. *)
      (*   unfold term_sub_inl_size in *.  simpl in *. lia. *)
      (*   eassumption. eassumption. *)
      (*   { (* count on dead prim pre *) *)
      (*     intro. specialize (H2 v0). *)
      (*     apply num_occur_app_ctx in H2. *)
      (*     destructAll. *)
      (*     unfold ce'. *)
      (*     repeat normalize_ctx. *)
      (*     simpl in H6. inv H6. *)
      (*     eapply num_occur_n. *)
      (*     apply num_occur_app_ctx. *)
      (*     do 2 eexists. split. eassumption. split. eassumption. reflexivity. *)
      (*     unfold dec_census_list. *)
      (*     rewrite <- combine_minus_census_list. *)
      (*     rewrite gccombine_sub. *)
      (*     rewrite update_census_list_correct. *)
      (*     rewrite apply_r_list_empty. *)
      (*     rewrite H11. unfold get_c. rewrite M.gempty. lia. } *)
      (*   auto. eapply inl_inv_mon. *)
      (*   2: apply H4. *)
      (*   unfold ce. *)
      (*   do 2 (rewrite bound_var_app_ctx). *)
      (*   simpl. *)
      (*   rewrite bound_var_Eprim. *)
      (*   eauto with Ensembles_DB. *)
      (*   eapply sig_inv_full_dead_l. *)
      (*   simpl in H5. rewrite inv_app_Eprim in H5. *)
      (*   simpl in H10. rewrite inv_app_Eprim in H10. *)
      (*   apply sig_inv_combine. split; eauto. *)
      (* } *)
      simpl in H6.
      assert ( rename_all_ctx_ns sig (inlined_ctx_f c inl)
              |[ rename_all_ns sig (Eprim v p l e) ]| =
                                                      rename_all_ctx_ns sig (inlined_ctx_f (comp_ctx_f c (Eprim_c v p l Hole_c)) inl) |[ rename_all_ns sig e ]|) by ctx_inl_push.
      remember (contract sig count e sub inl ) as s.
      destruct s as [[[[? ? ] ? ] ? ] ? ]. symmetry in Heqs.
      eapply  IHn with (c := (comp_ctx_f c (Eprim_c v p l Hole_c))) in Heqs; try (rewrite <- H7; eauto).
      3: (apply cmap_view_prim; auto).
      assert ((rename_all_ctx_ns sig
                                 (inlined_ctx_f (comp_ctx_f c (Eprim_c v p l Hole_c)) im') |[ e0 ]|) =
              (rename_all_ctx_ns sig
                                 (inlined_ctx_f c im') |[ Eprim v p (apply_r_list sig l) e0 ]|)) by ctx_inl_push.
      inv H6.
      destruct Heqs as (H6, (H9, (H11, Hsig_r))).
      (* destruct (get_c v c0) eqn:gvc0. *)
      (* { (* dead prim post IH *) *)
      (*   inv H10. *)
      (*   assert (gsr_clos 1 *)
      (*             (rename_all_ctx_ns sig *)
      (*                                (inlined_ctx_f (comp_ctx_f c (Eprim_c v p l Hole_c)) im') |[ e'  ]|) ce'). *)
      (*   { unfold ce'. *)
      (*     repeat normalize_ctx. *)
      (*     rewrite <- app_ctx_f_fuse. replace 1 with (1 + 0). *)
      (*     econstructor. constructor. simpl. *)
      (*     apply Prim_dead_s. *)
      (*     specialize (H9 v). rewrite gvc0 in H9. *)
      (*     apply num_occur_app_ctx in H9; destructAll; pi0. *)
      (*     auto. now constructor. lia. } *)
      (*   split. eapply gsr_clos_trans. *)
      (*   rewrite <- H7 in H6. apply H6. eassumption. *)
      (*   split. *)
      (*   { (* count on dead post prim *) *)
      (*     intro. specialize (H9 v0). *)
      (*     apply num_occur_app_ctx in H9. *)
      (*     destructAll. *)
      (*     unfold ce'. *)
      (*     repeat normalize_ctx. *)
      (*     apply num_occur_ec_comp_ctx in H9. *)
      (*     destructAll. simpl in H14. inv H14. inv H21. *)
      (*     eapply num_occur_n. *)
      (*     apply num_occur_app_ctx. *)
      (*     exists x1, x0. *)
      (*     split; auto. *)
      (*     unfold dec_census_list. *)
      (*     rewrite <- combine_minus_census_list. *)
      (*     rewrite gccombine_sub. *)
      (*     rewrite update_census_list_correct. *)
      (*     rewrite apply_r_list_empty. *)
      (*     rewrite H13. unfold get_c. rewrite M.gempty. *)
      (*     lia. *)
      (*   } *)
      (*   split. *)
      (*   eapply inl_inv_mon. *)
      (*   2: apply H11. *)
      (*   unfold ce'. *)
      (*   repeat normalize_ctx. *)
      (*   do 2 (rewrite bound_var_app_ctx). *)
      (*   simpl. *)
      (*   rewrite (proj1 bound_var_ctx_comp_ctx). *)
      (*   rewrite bound_var_Eprim_c. *)
      (*   eauto with Ensembles_DB. *)
      (*   intro. intros. *)
      (*   destruct (var_dec y v). *)
      (*   (* dead v *) *)
      (*   left. subst. specialize (H9 v). *)
      (*   rewrite gvc0 in H9. *)
      (*   repeat normalize_ctx. *)
      (*   apply num_occur_app_ctx in H9; destructAll; pi0. *)
      (*   apply num_occur_ec_comp_ctx in H9; destructAll; pi0. *)
      (*   apply num_occur_app_ctx. *)
      (*   exists 0, 0. *)
      (*   split; auto. *)
      (*   apply Hsig_r in H12. inv H12. *)
      (*   left. *)
      (*   repeat normalize_ctx. *)
      (*   apply num_occur_app_ctx in H13; destructAll; pi0. *)
      (*   apply num_occur_ec_comp_ctx in H12; destructAll; pi0. *)
      (*   apply num_occur_app_ctx. exists 0, 0. *)
      (*   split; auto. *)
      (*   right. *)
      (*   repeat normalize_ctx. *)
      (*   apply bound_stem_comp_ctx_mut in H13. inv H13. *)
      (*   auto. *)
      (*   exfalso. inv H12. apply n2; auto. inv H18. *)
      (* } *)
      (* inv H10. *)
      unfold ce; unfold ce'.
      rewrite H7.
      rewrite H8 in *.
      split; auto. split; auto. split; auto.
      intro. intros. assert (H10' := H10).

      apply Hsig_r in H10. inv H10.
      left. repeat normalize_ctx.
      apply num_occur_app_ctx in H12. destructAll; pi0.
      apply num_occur_ec_comp_ctx in H10. destructAll; pi0.
      simpl in H13. inv H13; pi0. rewrite H13.
      apply num_occur_app_ctx. exists 0, 0.
      split; auto. split. eapply num_occur_n.
      constructor; eauto. auto. auto.

      destruct (var_dec v y).
      apply H5 in H10'. inv H10'. inv H13.
      (* by no zombie *)
      left. eapply shrink_no_zombie. apply H6. rewrite <- H7. auto.
      (* impossible by unique binding *)
      exfalso. apply ub_app_ctx_f in H0. destructAll. inv H15. specialize (H16 y).
      apply H16. split. apply bound_stem_var.  auto. simpl. constructor.
      right. repeat normalize_ctx.
      apply bound_stem_comp_ctx_mut in H12. inv H12. auto.
      exfalso.
      simpl in H10. inv H10. now eauto. now inv H17.


      unfold term_sub_inl_size in *.
      simpl in H.
      simpl. lia.
      {
        simpl in H5.
        rewrite inv_app_Eprim in H5.
        apply sig_inv_full_push in H5.
        rewrite (proj1 inlined_comp_ctx).
        rewrite (proj1 (rename_all_ctx_ns_comp_ctx _ _)).
        simpl; auto.
      }
    - (* halt *)
      inv H6.
      simpl in *.
      unfold ce.
      unfold ce'.
      split; auto. now constructor.
      split; auto. split; auto.
      apply sig_inv_combine in H5. inv H5. auto.
  Qed.




  (* To handle terms with disjoint bv and of instead of closed, used this with xs = fv (e) : *)
  Theorem sr_unwrap_halt:
    forall s f t xs e  e',
      gen_sr_rw s (Efun (Fcons f t xs e Fnil) (Ehalt f)) e' ->
      exists e'', e' = (Efun (Fcons f t xs e'' Fnil) (Ehalt f)) /\
                  gen_sr_rw s e e''.
  Proof.
    intros. inv H. destruct c; inv H0.
    - (* Impossible due to shape*)
      simpl in *; subst. inv H1.
      + simpl in H4. inv H4. inv H1.
        rewrite peq_true in H. lia.
      + exfalso. inv H4; pi0. inv H5; pi0. destruct B1; inv H.
        destruct B1; inv H7. rewrite peq_true in H3. lia.
      + destruct c; inv H0.
      + destruct c; inv H0.
    - destruct c; inv H3.
      simpl in H. subst. inv H1.
    - destruct f0; inv H2.
      simpl. exists (e1 |[ e'0 ]|). split; auto.
      constructor; auto.
      + (* Impossible *)
        destruct f0; inv H6.
  Qed.

  End Contract_rename.

End CONTRACT.
