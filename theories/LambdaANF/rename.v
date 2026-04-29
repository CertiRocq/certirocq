From Stdlib Require Import Lists.List SetoidList NArith.BinNat
     PArith.BinPos MSets.MSetRBT Sets.Ensembles micromega.Lia Logic.Decidable.
From compcert.lib Require Import Coqlib.
From CertiRocq.LambdaANF Require Import term term_util ctx set_util Ensembles_util
     List_util map_util identifiers functions.
From CertiRocq Require Import Libraries.maps_util.
Require Import LambdaANF.tactics.

Import ListNotations.

(** * Renamings for LambdaANF expressions *)

Definition subst := M.t var.

(** Apply substitutions to variables *)

Definition apply_r (sigma : subst) y :=
  match sigma ! y with
  | Some v => v
  | None => y
  end.

Definition apply_r_list sigma ys :=
  map (apply_r sigma) ys.

(** Apply substitutions to expressions *)

Fixpoint all_fun_name (fds : fundefs) : list var :=
  match fds with
  | Fcons f t ys e fds' => f :: (all_fun_name fds')
  | Fnil => []
  end.

Fixpoint remove_all (sigma: subst) (vs : list var) :=
  match vs with
  | v::vs' => M.remove v (remove_all sigma vs')
  | [] => sigma
  end.

Fixpoint rename_all (sigma: subst) (e : exp) : exp :=
  match e with
  | Econstr x t ys e' => Econstr x t (apply_r_list sigma ys) (rename_all (M.remove x sigma) e')
  | Eprim_val x p e' => Eprim_val x p (rename_all (M.remove x sigma) e')
  | Eprim x f ys e' => Eprim x f (apply_r_list sigma ys) (rename_all (M.remove x sigma) e')
  | Eletapp x f ft ys e' => Eletapp x (apply_r sigma f) ft (apply_r_list sigma ys)
                                    (rename_all (M.remove x sigma) e')
  | Eproj v t n y e' => Eproj v t n (apply_r sigma y) (rename_all (M.remove v sigma) e')
  | Ecase v cl =>
    Ecase (apply_r sigma v) (List.map (fun (p:var*exp) => let (k, e) := p in
                                                          (k, rename_all sigma e)) cl)
  | Efun fl e' =>
    let fs := all_fun_name fl in
    let fl' := rename_all_fun (remove_all sigma fs) fl in

    Efun fl' (rename_all (remove_all sigma fs) e')
  | Eapp f t ys =>
    Eapp (apply_r sigma f) t (apply_r_list sigma ys)
  | Ehalt v => Ehalt (apply_r sigma v)
  end
with rename_all_fun (sigma : subst) (fds : fundefs): fundefs :=
       match fds with
       | Fnil => Fnil
       | Fcons v' t ys e fds' => Fcons v' t ys (rename_all (remove_all sigma ys) e) (rename_all_fun sigma fds')
       end.

Fixpoint all_fun_name_ctx (cfds:fundefs_ctx) : list var :=
  match cfds with
  | Fcons1_c f t ys c fds' => f::(all_fun_name fds')
  | Fcons2_c f t ys e cfds' => f::(all_fun_name_ctx cfds')
  end.


Fixpoint rename_all_ctx (sigma:subst) (c:exp_ctx): exp_ctx :=
  match c with
  | Hole_c => Hole_c
  | Econstr_c x t ys c' =>
    Econstr_c x t (apply_r_list sigma ys) (rename_all_ctx (M.remove x sigma) c')
  | Eprim_val_c x p c' =>
    Eprim_val_c x p (rename_all_ctx (M.remove x sigma) c')
  | Eprim_c x f ys c' =>
    Eprim_c x f (apply_r_list sigma ys) (rename_all_ctx (M.remove x sigma) c')
  | Eproj_c v t n y c' => Eproj_c v t n (apply_r sigma y) (rename_all_ctx (M.remove v sigma) c')
  | Eletapp_c v f ft ys c' => Eletapp_c v (apply_r sigma f) ft (apply_r_list sigma ys)
                                        (rename_all_ctx (M.remove v sigma) c')
  | Ecase_c v l t c' l' =>
    let f cl := (List.map (fun (p:var*exp) => let (k, e) := p in
                                              (k, rename_all sigma e)) cl) in
    Ecase_c (apply_r sigma v) (f l) t (rename_all_ctx sigma c') (f l')
  | Efun1_c fl c' =>
    let fs := all_fun_name fl in
    let fl' := rename_all_fun (remove_all sigma fs) fl in
    Efun1_c fl' (rename_all_ctx (remove_all sigma fs) c')
  | Efun2_c cf e =>
    let fs := all_fun_name_ctx cf in
    let cf' := rename_all_fun_ctx (remove_all sigma fs) cf in
    Efun2_c cf' (rename_all (remove_all sigma fs) e)
  end
with rename_all_fun_ctx (sigma:subst) (fc:fundefs_ctx): fundefs_ctx :=
       match fc with
       | Fcons1_c f t ys c fds' =>  Fcons1_c f t ys (rename_all_ctx (remove_all sigma ys) c) (rename_all_fun sigma fds')
       | Fcons2_c f t ys e cfds' =>  Fcons2_c f t ys (rename_all (remove_all sigma ys) e) (rename_all_fun_ctx sigma cfds')
       end.

Definition rename y x e := rename_all (M.set x y (M.empty var)) e.

(* Version of rename_all assuming capture-avoiding subtitution . *)
Fixpoint rename_all_ns (sigma:subst) (e:exp) : exp :=
  match e with
  | Econstr x t ys e' => Econstr x t (apply_r_list sigma ys) (rename_all_ns sigma e')
  | Eprim_val x p e' => Eprim_val x p (rename_all_ns sigma e')
  | Eprim x f ys e' => Eprim x f (apply_r_list sigma ys) (rename_all_ns sigma e')
  | Eproj v t n y e' => Eproj v t n (apply_r sigma y) (rename_all_ns sigma e')
  | Eletapp v f t ys e' => Eletapp v (apply_r sigma f) t (apply_r_list sigma ys) (rename_all_ns sigma e')
  | Ecase v cl =>
    Ecase (apply_r sigma v) (List.map (fun (p:var*exp) => let (k, e) := p in
                                                          (k, rename_all_ns sigma e)) cl)
  | Efun fl e' =>
    let fl' := rename_all_fun_ns sigma fl in
    Efun fl' (rename_all_ns sigma e')
  | Eapp f t ys =>
    Eapp (apply_r sigma f) t (apply_r_list sigma ys)
  | Ehalt v => Ehalt (apply_r sigma v)
  end
with rename_all_fun_ns (sigma:subst) (fds:fundefs): fundefs :=
       match fds with
       | Fnil => Fnil
       | Fcons v' t ys e fds' => Fcons v' t ys (rename_all_ns sigma e) (rename_all_fun_ns sigma fds')
       end.


Fixpoint rename_all_ctx_ns (sigma:subst) (c:exp_ctx): exp_ctx :=
  match c with
  | Hole_c => Hole_c
  | Econstr_c x t ys c' =>
    Econstr_c x t (apply_r_list sigma ys) (rename_all_ctx_ns sigma c')
  | Eprim_val_c x p c' =>
    Eprim_val_c x p (rename_all_ctx_ns sigma c')
  | Eprim_c x f ys c' =>
    Eprim_c x f (apply_r_list sigma ys) (rename_all_ctx_ns sigma c')
  | Eproj_c v t n y c' => Eproj_c v t n (apply_r sigma y) (rename_all_ctx_ns sigma c')
  | Eletapp_c v f ft ys c' => Eletapp_c v (apply_r sigma f) ft (apply_r_list sigma ys)
                                        (rename_all_ctx_ns sigma c')
  | Ecase_c v l t c' l' =>
    let f cl := (List.map (fun (p:var*exp) => let (k, e) := p in
                                              (k, rename_all_ns sigma e)) cl) in
    Ecase_c (apply_r sigma v) (f l) t (rename_all_ctx_ns sigma c') (f l')
  | Efun1_c fl c' =>
    let fl' := rename_all_fun_ns sigma fl in
    Efun1_c fl' (rename_all_ctx_ns sigma c')
  | Efun2_c cf e =>
    let cf' := rename_all_fun_ctx_ns sigma cf in
    Efun2_c cf' (rename_all_ns sigma e)
  end
with rename_all_fun_ctx_ns (sigma:subst) (fc: fundefs_ctx): fundefs_ctx :=
       match fc with
       | Fcons1_c f t ys c fds' =>  Fcons1_c f t ys (rename_all_ctx_ns sigma c) (rename_all_fun_ns sigma fds')
       | Fcons2_c f t ys e cfds' =>  Fcons2_c f t ys (rename_all_ns sigma e) (rename_all_fun_ctx_ns sigma cfds')
       end.


(** * Lemmas about [apply_r] and [apply_r_list] *)

Lemma prop_apply_r v sub sub' :
  map_get_r _ sub sub' -> apply_r sub v = apply_r sub' v.
Proof.
  intros.
  unfold apply_r.
  destruct (M.get v sub) eqn:gvs.
  rewrite H in gvs. rewrite gvs. auto.
  rewrite H in gvs. rewrite gvs; auto.
Qed.

Lemma prop_apply_r_list l sub sub' :
  map_get_r _ sub sub' ->
  apply_r_list sub l = apply_r_list sub' l.
Proof.
  induction l; intros.
  reflexivity.
  simpl. erewrite IHl; eauto.
  erewrite prop_apply_r; eauto.
Qed.

#[global] Instance Proper_apply_r : Proper (@map_get_r _ ==> eq ==> eq) (apply_r).
Proof.
  intro; intros; intro; intros; subst. eapply prop_apply_r; eauto.
Qed.

#[global] Instance Proper_apply_r_list : Proper (@map_get_r _ ==> eq ==> eq) (apply_r_list).
Proof.
  intro; intros; intro; intros; subst. eapply prop_apply_r_list; eauto.
Qed.

Theorem apply_r_empty v : apply_r (M.empty var) v = v.
Proof.
  unfold apply_r. rewrite M.gempty. auto.
Qed.

Lemma apply_r_list_empty l : apply_r_list (M.empty var) l = l.
Proof.
  induction l; auto.
  simpl. rewrite IHl. rewrite apply_r_empty. reflexivity.
Qed.

Lemma image_apply_r_remove v m S :
  image (apply_r (M.remove v m)) S \subset v |: image (apply_r m) (S \\ [set v]).
Proof.
  intros z [y [Hin Heq]]; subst.
  destruct (peq y v); subst.
  - left. unfold In. unfold apply_r. rewrite M.grs. reflexivity.
  - right. eexists; split; eauto.
    constructor; eauto. intros Hc; inv Hc; eauto.
    unfold apply_r. rewrite M.gro; eauto.
Qed.

Lemma apply_r_remove_eq m v :
  apply_r (M.remove v m) v = v.
Proof.
  unfold apply_r. rewrite M.grs. reflexivity.
Qed.

Lemma apply_r_remove_neq m x v :
  x <> v ->
  apply_r (M.remove v m) x = apply_r m x.
Proof.
  intros Hneq.
  unfold apply_r. rewrite M.gro; eauto.
Qed.

Lemma apply_r_none v sigma :
  M.get v sigma = None ->
  apply_r sigma v = v.
Proof.
  intros. unfold apply_r.
  unfold M.get in H. unfold M.get. rewrite H.
  reflexivity.
Qed.

Lemma apply_r_some v y sigma :
  M.get v sigma = Some y ->
  apply_r sigma v = y.
Proof.
  intros. unfold apply_r.
  unfold M.get in *. rewrite H. reflexivity.
Qed.

Lemma apply_r_set1 x y sig :
  apply_r (M.set x y sig) x = y.
Proof.
  intros.
  unfold apply_r.
  rewrite M.gss. auto.
Qed.

Lemma apply_r_set2 x v y sigma :
  x <> v ->
  apply_r (M.set x y sigma) v = apply_r sigma v.
Proof.
  intros. unfold apply_r. rewrite M.gso by auto. auto.
Qed.

Lemma apply_r_not_in_sig x v sigma :
  ~ (exists z : M.elt, M.get z sigma = Some x) ->
  x <> v -> x <> apply_r sigma v.
Proof.
  intros. unfold apply_r.
  destruct (M.get v sigma) eqn:gvs.
  intro; subst. apply H. exists v; auto.
  auto.
Qed.

Lemma apply_r_list_refl m xs :
  (forall x, x \in FromList xs -> apply_r m x = x) ->
  apply_r_list m xs = xs.
Proof.
  induction xs; eauto.
  - simpl; intros Hyp. f_equal. eapply Hyp.
    now left. eapply IHxs.
    intros. eapply Hyp. now right.
Qed.

Lemma remove_apply_r_eq m v :
  (forall x, apply_r m x = x) ->
  (forall x, apply_r (M.remove v m) x =x).
Proof.
  intros Hyp x. unfold apply_r. destruct (peq x v); subst.
  - rewrite M.grs. reflexivity.
  - rewrite M.gro; eauto.
Qed.

Lemma remove_all_apply_r_eq m l :
  (forall x, apply_r m x = x) ->
  (forall x, apply_r (remove_all m l) x =x).
Proof.
  induction l; intros Hyp x; eauto.
  simpl. rewrite remove_apply_r_eq; eauto.
Qed.

Lemma FromList_apply_list m l :
  FromList (apply_r_list m l) <--> image (apply_r m) (FromList l).
Proof.
  induction l; simpl; repeat normalize_sets.
  - rewrite image_Empty_set. reflexivity.
  - rewrite image_Union. rewrite IHl. eapply Same_set_Union_compat; [| reflexivity ].
    rewrite image_Singleton. reflexivity.
Qed.

Lemma image_apply_r_remove_not_In m v S :
  ~ v \in S ->
          image (apply_r (M.remove v m)) S <--> image (apply_r m) S.
Proof.
  intros Hc.
  split; intros x [z [HIn Heq]]; subst.
  eexists; split; eauto. unfold apply_r.
  rewrite M.gro; eauto. now intros Hc'; subst; eauto.
  eexists; split; eauto. unfold apply_r.
  rewrite M.gro; eauto. intros Hi; subst; eauto.
Qed.

Lemma image_apply_r_set x v m S:
  image (apply_r (M.set x v m)) S \subset v |: image (apply_r m) (S \\ [set x]).
Proof.
  intros z [h [Hin Heq]]. subst.
  unfold In, apply_r. simpl. destruct (var_dec h x); subst.
  - rewrite M.gss. now left.
  - rewrite M.gso. right. eexists. split; eauto. constructor; eauto.
    intros Hc; inv Hc; eauto. eassumption.
Qed.

Lemma image_apply_r_set_list xs vs (m : M.t var) S :
  List.length xs = List.length vs ->
  image (apply_r (set_list (combine xs vs) m)) S \subset FromList vs :|: (image (apply_r m) (S \\ FromList xs)).
Proof.
  revert vs m S; induction xs; intros vs m S.
  - simpl. normalize_sets; sets.
  - intros Hlen. destruct vs. now inv Hlen.
    simpl. eapply Included_trans.
    eapply image_apply_r_set. normalize_sets.
    eapply Union_Included. now sets.
    eapply Included_trans. eapply (IHxs vs). inv Hlen. reflexivity.
    normalize_sets. rewrite Setminus_Union. sets.
Qed.

Lemma apply_r_set_f_eq v x sig :
  f_eq (apply_r (M.set v x sig)) (extend (apply_r sig) v x).
Proof.
  intros z. destruct (var_dec v z); subst.
  - unfold apply_r. rewrite M.gss, extend_gss. reflexivity.
  - unfold apply_r. rewrite M.gso, extend_gso; eauto.
Qed.

Lemma apply_r_set_list_f_eq xs ys sig :
  f_eq (apply_r (set_list (combine xs ys) sig)) (apply_r sig <{ xs ~> ys }>).
Proof.
  revert ys sig. induction xs; intros; simpl. reflexivity.
  destruct ys. reflexivity.
  simpl. eapply Equivalence_Transitive.
  eapply apply_r_set_f_eq. eapply f_eq_extend. eauto.
Qed.

Lemma eq_P_apply_r:
  forall x sub sub',
    eq_env_P (Singleton _ x) sub sub' ->
    apply_r sub x = apply_r sub' x.
Proof.
  intros.
  unfold apply_r.
  rewrite H.
  auto.
  constructor.
Qed.

Lemma eq_P_apply_r_list:
  forall sub sub' l,
    eq_env_P (FromList l) sub sub' ->
    apply_r_list sub l = apply_r_list sub' l.
Proof.
  induction l.
  auto.
  simpl.
  intros.
  erewrite eq_P_apply_r.
  erewrite IHl. auto.
  intro. intro. apply H.
  constructor 2; auto.
  intro. intro; apply H.
  constructor.
  inv H0. auto.
Qed.

Lemma apply_r_list_eq xs ys sig :
  NoDup xs ->
  length xs = length ys ->
  apply_r_list (set_list (combine xs ys) sig) xs = ys.
Proof.
  revert ys sig; induction xs; intros ys sig Hnd Hlen.
  - simpl. destruct ys; eauto. inv Hlen.
  - destruct ys; inv Hlen. inv Hnd.
    simpl. unfold apply_r. rewrite M.gss. f_equal.
    erewrite eq_P_apply_r_list. eapply IHxs. eassumption. eassumption.
    eapply eq_env_P_set_not_in_P_l. eapply eq_env_P_refl. eassumption.
Qed.

Lemma apply_r_sigma_in sigma a :
    apply_r sigma a \in  ([set a] \\ (Dom_map sigma) :|: Range_map sigma).
Proof.
  unfold apply_r.
  intros.
  destruct (@PTree.get var a sigma) eqn:gas.
  right. exists a. auto.
  left. split.
  constructor.
  intro. inv H. unfold var, M.elt in *. rewrite gas in H0. inv H0.
Qed.

Lemma FromList_apply_r_list sigma l:
  FromList (apply_r_list sigma l) \subset
  (FromList l \\ (Dom_map sigma) :|: Range_map sigma).
Proof.
  induction l.
  - simpl. intro. intro.
    inv H.
  - simpl.
    rewrite FromList_cons.
    rewrite FromList_cons.
    apply Union_Included.
    intro. intros.
    inv H.
    assert (Hrs := apply_r_sigma_in sigma a).
    inv Hrs. left.
    inv H.
    split; auto.
    right; auto.
    intro; intro.
    apply IHl in H.
    inv H.
    left. inv H0.
    split; auto.
    right; auto.
Qed.

Lemma Disjoint_apply_r sig x :
  Disjoint _ (Dom_map sig) (Singleton _ x) ->
  apply_r sig x = x.
Proof.
  intros. unfold apply_r.
  destruct (M.get x sig) eqn:gxs.
  exfalso; inv H. specialize (H0 x).
  apply H0.
  split; auto. exists v. auto.
  auto.
Qed.

Lemma Disjoint_apply_r_FromList sig l :
  Disjoint _ (Dom_map sig) (FromList l) ->
  apply_r_list sig l = l.
Proof.
  induction l; intros.
  - auto.
  - simpl. rewrite IHl.
    rewrite Disjoint_apply_r.
    auto.
    eapply Disjoint_Included_r.
    2: apply H. rewrite FromList_cons; auto with Ensembles_DB.
    eapply Disjoint_Included_r.
    2: apply H. rewrite FromList_cons; auto with Ensembles_DB.
Qed.


Lemma apply_r_list_In:
  forall v1 sig l,
    List.In v1 l ->
    List.In (apply_r sig v1) (apply_r_list sig l).
Proof.
  induction l.
  intro. inv H.
  intros. inv H.
  simpl. auto.
  apply IHl in H0. simpl. auto.
Qed.


(** * Lemmas about [all_fun_name] *)

Lemma rename_all_fun_name rho fds :
    name_in_fundefs (rename_all_fun rho fds) <--> name_in_fundefs fds.
Proof.
  induction fds.
  - simpl. eauto with Ensembles_DB.
  - reflexivity.
Qed.

Lemma all_fun_name_ctx_same e f:
  all_fun_name_ctx f = all_fun_name (f <[ e ]>).
Proof.
  induction f; auto.
  simpl. rewrite IHf. auto.
Qed.

Lemma forall_name_fundefs x P fds :
  Forall P (all_fun_name fds) ->
  name_in_fundefs fds x ->
  P x.
Proof.
  induction fds; intros.
  - inversion H0; inversion H; subst.
    + inversion H1; subst. auto.
    + apply IHfds; auto.
  - inversion H0.
Qed.

Lemma all_name_fundefs fds x :
  List.In x (all_fun_name fds) <-> name_in_fundefs fds x.
Proof.
  induction fds; simpl; intros; split; intros.
  - destruct H. subst. left; auto.
    right. apply IHfds; auto.
  - inversion H; subst. inversion H0; auto.
    right. apply IHfds; auto.
  - inversion H.
  - inversion H.
Qed.

Lemma Disjoint_occurs_free_name_in_fundefs e fds:
  Forall (fun v => num_occur e v 0) (all_fun_name fds) ->
  Disjoint var (occurs_free e) (name_in_fundefs fds).
Proof.
  intros.
  apply Disjoint_intro; intros.
  intro.
  inversion H0; subst.
  assert (Hof := (not_occurs_not_free x)).
  destruct Hof.
  specialize (H3 e).
  apply H3; auto.
  rewrite Forall_forall in H.
  apply H.
  apply all_name_fundefs; auto.
Qed.

Lemma Disjoint_occurs_free_name_in_fundefs_cor e fds :
  Forall (fun v => ~occurs_free e v) (all_fun_name fds) ->
  Disjoint var (occurs_free e) (name_in_fundefs fds).
Proof.
  intros.
  apply Disjoint_intro; intros.
  intro.
  inversion H0; subst.
  rewrite Forall_forall in H.
  specialize (H x).
  apply H.
  apply all_name_fundefs; auto. auto.
Qed.

Lemma name_fds_same: forall x fds,
    name_in_fundefs fds x <-> List.In x (all_fun_name fds).
Proof.
  induction fds; split; intros.
  - simpl in H. inversion H; subst.
    inversion H0; subst.
    constructor; auto.
    rewrite IHfds in H0.
    constructor 2. auto.
  - simpl.
    simpl in H.
    inversion H.
    subst; left; auto.
    right.
    apply IHfds. auto.
  - inversion H.
  - inversion H.
Qed.

Lemma Same_set_all_fun_name f:
  name_in_fundefs f <--> FromList (all_fun_name f).
Proof.
  split; intro; intro; apply name_fds_same; auto.
Qed.

Lemma image_apply_r_empty S :
  image (apply_r (M.empty var)) S <--> S.
Proof.
  split; intros x.
  - intros [z [Hin Heq]]; subst. unfold apply_r.
    rewrite M.gempty. eassumption.
  - intros Hin. eexists; split; eauto.
Qed.

(** * Lemmas about [remove_all] *)

Lemma prop_remove_all l sub sub' :
  map_get_r _ sub sub' -> map_get_r _ (remove_all sub l) (remove_all sub' l).
Proof.
  induction l; intros.
  - auto.
  - simpl. apply proper_remove. apply IHl; eauto.
Qed.

#[global] Instance Proper_remove_all : Proper (map_get_r _ ==> eq ==> map_get_r _) remove_all.
Proof.
  intro; intros; intro; intros; subst. eapply prop_remove_all; eauto.
Qed.

(* XXX : setoid rewrite doesn't seem to work with map_get_r *)


Lemma remove_all_empty l : map_get_r _ (remove_all (M.empty var) l) (M.empty var).
Proof.
  induction l; intros; simpl; auto.
  - apply smg_refl.
  - eapply smg_trans. eapply proper_remove. eassumption.
    apply remove_empty.
Qed.

Lemma remove_all_not_in x z l rho:
  ~ (List.In x l) ->
  map_get_r _ (remove_all (M.set x z rho) l) (M.set x z (remove_all rho l)).
Proof.
  induction l; intros; simpl.
  - apply smg_refl.
  - eapply smg_trans. eapply proper_remove.
    eapply IHl. intros Hc. eapply H; now right.
    apply remove_set_2. intros Hc; subst; eapply H; now left.
Qed.

Lemma remove_all_in x z l rho :
  List.In x l ->
  map_get_r _ (remove_all (M.set x z rho) l) (remove_all rho l).
Proof.
  induction l; intros; simpl; auto.
  - inversion H.
  - simpl in H.
    destruct (var_dec x a); subst.
    + edestruct (ListDec.In_decidable) with (l := l) (x := a) as [Hd | ].
      { intros x y. destruct (DecidableTypeEx.Positive_as_DT.eq_dec x y); subst; eauto.
        left; eauto. right; eauto. }
      * eapply proper_remove. eapply IHl. eauto.
      * eapply smg_trans. eapply proper_remove.
        eapply remove_all_not_in. eassumption.
        apply remove_set_1.
    + inv H. exfalso; eauto. eapply proper_remove. eapply IHl. eauto.
Qed.

(* TODO move *)
Lemma image'_get_not_In {A} v (m : M.t A) S :
  image' (fun x : positive => M.get x (M.remove v m)) S \subset
         image' (fun x : positive => M.get x m) (S \\ [set v]).
Proof.
  intros z [y [Hin Heq]]; subst.
  destruct (peq y v); subst.
  - rewrite M.grs in Heq. congruence.
  - rewrite M.gro in Heq; eauto. eexists; split; eauto.
    constructor; eauto. intros Hc; inv Hc. eauto.
Qed.

Lemma remove_all_none: forall x l sigma,
    M.get x sigma = None ->
    M.get x (remove_all sigma l) = None.
Proof.
  induction l.
  - intros. simpl. auto.
  - intros. simpl. apply gr_none. eapply IHl. eassumption.
Qed.

Lemma in_remove_all: forall x l sigma,
    FromList l x ->
    M.get x (remove_all sigma l) = None.
Proof.
  induction l; intros; simpl.
  - inv H.
  - destruct (peq x a); inv H; eauto; subst.
    + rewrite M.grs. reflexivity.
    + rewrite M.grs. reflexivity.
    + rewrite M.gro; eauto.
Qed.

Lemma not_in_remove_all: forall x l sigma,
    ~ (FromList l x) ->
    M.get x sigma = M.get x (remove_all sigma l).
Proof.
  induction l; intros.
  - reflexivity.
  - simpl.
    assert (Hin : ~ (a = x) /\ ~ (FromList l x)).
    { split; intro. apply H. constructor; auto.
      apply H. constructor 2; auto. }
    destruct Hin.
    rewrite M.gro; auto.
Qed.

Lemma image'_get_remove_all (m : M.t var) S l :
  image' (fun x : positive => M.get x (remove_all m l)) S \subset
         image' (fun x : positive => M.get x m) (S \\ FromList l).
Proof.
  revert m S; induction l; intros m S.
  - simpl. repeat normalize_sets. reflexivity.
  - simpl. eapply Included_trans.
    eapply image'_get_not_In.
    eapply Included_trans. eapply IHl.
    repeat normalize_sets. rewrite Setminus_Union. reflexivity.
Qed.

Lemma image_apply_r_remove_Singleton v m :
  image (apply_r (M.remove v m)) [set v] <--> [set v].
Proof.
  rewrite image_Singleton. unfold apply_r. rewrite M.grs. reflexivity.
Qed.

Lemma image_apply_r_remove_all_Singleton l v m :
  v \in FromList l ->
        image (apply_r (remove_all m l)) [set v] <--> [set v].
Proof.
  intros Hin.
  rewrite image_Singleton. unfold apply_r. rewrite in_remove_all. reflexivity.
  eassumption.
Qed.

Lemma image_remove_all_Disjoint  S m l :
  Disjoint _ S (FromList l) ->
  image (apply_r (remove_all m l)) S <--> image (apply_r m) S.
Proof.
  revert S. induction l; intros S Hc.
  - reflexivity.
  - simpl. normalize_sets. rewrite image_apply_r_remove_not_In.
    eapply IHl. sets.
    intros Hc'. eapply Hc. constructor; eauto.
Qed.

Lemma image_remove_all S m l :
  image (apply_r (remove_all m l)) S \subset image (apply_r m) (S \\ FromList l) :|: FromList l.
Proof.
  revert S. induction l; intros S.
  - simpl. rewrite !FromList_nil at 1. repeat normalize_sets. sets.
  - simpl. rewrite !FromList_cons at 1. repeat normalize_sets.
    eapply Included_trans. eapply image_apply_r_remove.
    eapply Union_Included. sets.
    eapply Included_trans. eapply IHl. rewrite Setminus_Union. sets.
Qed.

Lemma remove_all_some:
  forall x y l sigma,
    M.get x (remove_all sigma l) = Some y ->
    ~ (FromList l x).
Proof.
  induction l.
  - intros. intro. inv H0.
  - simpl. intros s Hget Hc. destruct (peq a x); subst; inv Hc; try contradiction.
    rewrite M.grs in Hget. congruence.
    rewrite M.grs in Hget. congruence.
    rewrite M.gro in Hget. eapply IHl; eauto.
    eauto.
Qed.

(** * Lemmas about [rename_all] *)

Lemma prop_rename_all: (forall e sub sub', map_get_r _ sub sub' -> rename_all sub e = rename_all sub' e) /\
                       (forall fds sub sub', map_get_r _ sub sub' -> rename_all_fun sub fds = rename_all_fun sub' fds) .
Proof.
  apply exp_def_mutual_ind; intros; simpl.
  - erewrite prop_apply_r_list; eauto. erewrite H; eauto. apply proper_remove; auto.
  - erewrite prop_apply_r; eauto.
  - erewrite H; eauto.
    erewrite prop_apply_r; eauto.
    apply H0 in H1. simpl in H1. inversion H1; subst. reflexivity.
  - erewrite prop_apply_r; eauto. erewrite H; eauto. apply proper_remove; auto.
  - erewrite prop_apply_r; eauto. erewrite prop_apply_r_list; eauto. erewrite H; eauto. apply proper_remove; auto.
  - erewrite H0; eauto. erewrite H; eauto.
    apply prop_remove_all; auto.
    apply prop_remove_all; auto.
  - erewrite prop_apply_r; eauto. erewrite prop_apply_r_list; eauto.
  - f_equal. apply H. now apply proper_remove.
  - erewrite prop_apply_r_list; eauto. erewrite H; eauto. apply proper_remove; auto.
  - erewrite prop_apply_r; eauto.
  - erewrite H; eauto. erewrite H0; eauto. apply prop_remove_all; auto.
  - reflexivity.
Qed.

#[global] Instance Proper_rename_all : Proper (map_get_r _ ==> eq ==> eq) rename_all.
Proof.
  intro; intros; intro; intros; subst. eapply prop_rename_all; eauto.
Qed.

Lemma rename_all_empty:
  (forall e, e = rename_all (M.empty var) e) /\
  (forall fds, fds = rename_all_fun (M.empty var) fds).
Proof.
  apply exp_def_mutual_ind; intros; simpl.
  - rewrite apply_r_list_empty.
    replace (rename_all (M.remove v (M.empty var)) e) with e. reflexivity.
  - rewrite apply_r_empty.  reflexivity.
  - rewrite apply_r_empty. rewrite <- H. simpl in H0. inversion H0.
    rewrite <- H2. rewrite <- H2. reflexivity.
  - rewrite apply_r_empty.
    replace (rename_all (M.remove v (M.empty var)) e) with e. reflexivity.
  - rewrite apply_r_empty, apply_r_list_empty.
    replace (rename_all (M.remove x (M.empty var)) e) with e. reflexivity.
  - replace (rename_all (remove_all (M.empty var) (all_fun_name f2)) e) with e.
    replace (rename_all_fun (remove_all (M.empty var) (all_fun_name f2)) f2) with f2; auto.
    rewrite H at 1.
    eapply prop_rename_all.
    apply smg_sym.
    apply remove_all_empty.
    rewrite H0 at 1.
    eapply prop_rename_all.
    apply smg_sym.
    apply remove_all_empty.
  - rewrite apply_r_empty.
    rewrite apply_r_list_empty. auto.
  - f_equal.
    replace (rename_all (M.remove v (M.empty var)) e) with e. reflexivity.
  - rewrite apply_r_list_empty.
    replace (rename_all (M.remove v (M.empty var)) e) with e. reflexivity.
  - rewrite apply_r_empty. auto.
  - rewrite <- H0.
    replace (rename_all (remove_all (M.empty var) l) e) with e.
    reflexivity.
    rewrite H at 1.
    eapply prop_rename_all.
    apply smg_sym.
    apply remove_all_empty.
  - auto.
Qed.

Lemma find_def_rename f t xs e sigma fds :
  find_def f fds = Some (t, xs, e) ->
  find_def f (rename_all_fun sigma fds) = Some (t, xs, rename_all (remove_all sigma xs) e).
Proof.
  induction fds; intros.
  - simpl in *. destruct (M.elt_eq f v).
    + subst; inversion H; reflexivity.
    + apply IHfds; auto.
  - inversion H.
Qed.


Lemma rename_all_empty_exp: forall e, e = rename_all (M.empty var) e.
Proof. eapply rename_all_empty. Qed.

Lemma rename_all_empty_fundefs: forall e, e = rename_all_fun (M.empty var) e.
Proof. eapply rename_all_empty. Qed.

Lemma rename_all_refl_mut :
  (forall e m (Hyp : forall x, apply_r m x = x), rename_all m e = e) /\
  (forall B m (Hyp : forall x, apply_r m x = x), rename_all_fun m B = B).
Proof.
  exp_defs_induction IHe IHl IHB; intros.
  - simpl. rewrite apply_r_list_refl; eauto. rewrite IHe. reflexivity.
    eapply remove_apply_r_eq. eassumption.
  - simpl. rewrite Hyp; eauto.
  - simpl. rewrite Hyp; eauto.
    rewrite IHe; eauto. eapply IHl in Hyp. simpl in Hyp.
    do 2 f_equal. inversion Hyp. rewrite H1. eassumption.
  - simpl. rewrite Hyp, IHe; eauto.
    eapply remove_apply_r_eq. eassumption.
  - simpl. rewrite Hyp, apply_r_list_refl, IHe; eauto.
    eapply remove_apply_r_eq. eassumption.
  - simpl. rewrite IHe, IHB; eauto.
    eapply remove_all_apply_r_eq; eauto.
    eapply remove_all_apply_r_eq; eauto.
  - simpl. rewrite Hyp, apply_r_list_refl; auto.
  - simpl. f_equal. apply IHe. now intros x; eapply remove_apply_r_eq.
  - simpl. rewrite apply_r_list_refl; eauto. rewrite IHe. reflexivity.
    eapply remove_apply_r_eq. eassumption.
  - simpl. rewrite Hyp; eauto.
  - simpl. rewrite IHe, IHB; eauto.
    eapply remove_all_apply_r_eq; eauto.
  - reflexivity.
Qed.

Corollary rename_all_refl :
  forall e m (Hyp : forall x, apply_r m x = x), rename_all m e = e.
Proof.
  eapply rename_all_refl_mut.
Qed.

(** * Lemmas about [rename_all_ns] *)

Lemma inline_letapp_rename e x C x' sig :
  apply_r sig x = x ->
  inline_letapp e x = Some (C, x') ->
  inline_letapp (rename_all_ns sig e) x = Some (rename_all_ctx_ns sig C, apply_r sig x').
Proof.
  revert x C x' sig; induction e; intros x C x' sig Hyp Hinl; simpl in *;
    try match goal with
        | [H : context[inline_letapp ?E ?X] |- _ ] => destruct (inline_letapp E X) as [[C' y] | ] eqn:Hinl'; inv Hinl
        end;
    try now (erewrite IHe; [| eassumption | ]).
  - inv Hinl.
  - inv Hinl; eauto. simpl. rewrite Hyp. reflexivity.
  - inv Hinl. reflexivity.
Qed.

Lemma rename_all_bound_var_mut :
  (forall e m, bound_var (rename_all m e) <--> bound_var e) /\
  (forall B m, bound_var_fundefs (rename_all_fun m B) <--> bound_var_fundefs B).
Proof.
  exp_defs_induction IHe IHl IHB; intros m;
    simpl; repeat normalize_bound_var;
      (try (rewrite IHe; reflexivity)); try reflexivity.
  - rewrite IHe.
    specialize (IHl m). simpl in IHl. rewrite IHl. reflexivity.
  - rewrite IHe, IHB. reflexivity.
  - rewrite IHe, IHB. reflexivity.
Qed.

Lemma rename_all_bound_var :
  forall e m, bound_var (rename_all m e) <--> bound_var e.
Proof.
  eapply rename_all_bound_var_mut.
Qed.

Lemma rename_all_bound_var_fundefs :
  (forall B m, bound_var_fundefs (rename_all_fun m B) <--> bound_var_fundefs B).
Proof.
  eapply rename_all_bound_var_mut.
Qed.

Lemma rename_all_occurs_free_mut :
  (forall e m,
      occurs_free (rename_all m e) \subset (image (apply_r m) (occurs_free e))) /\
  (forall B L m,
      name_in_fundefs B \subset FromList L ->
      occurs_free_fundefs (rename_all_fun (remove_all m L) B) \\ FromList L  \subset
                          image (apply_r m) (occurs_free_fundefs B \\ FromList L)).
Proof.
  exp_defs_induction IHe IHl IHB; intros m; simpl;
    repeat normalize_occurs_free; repeat normalize_bound_var.
  - rewrite FromList_apply_list, image_Union in *.
    eapply Included_Union_compat. reflexivity.
    eapply Setminus_Included_Included_Union.
    eapply Included_trans. eapply IHe. eapply Included_trans.
    eapply image_apply_r_remove. sets.
  - rewrite image_Singleton. reflexivity.
  - rewrite !image_Union, image_Singleton.
    eapply Union_Included; sets.
  - rewrite !image_Union, image_Singleton.
    eapply Union_Included; sets.
    eapply Setminus_Included_Included_Union.
    eapply Included_trans. eapply IHe. eapply Included_trans.
    eapply image_apply_r_remove. sets.
  - rewrite !image_Union, image_Singleton.
    eapply Union_Included; sets. eapply Union_Included; sets.
    rewrite FromList_apply_list. now sets.
    eapply Setminus_Included_Included_Union.
    eapply Included_trans. eapply IHe. eapply Included_trans.
    eapply image_apply_r_remove. sets.
  - specialize (IHB (all_fun_name f2) m).
    rewrite <- !Same_set_all_fun_name in IHB at 1.
    rewrite Setminus_Disjoint in IHB.
    2:{ rewrite <- rename_all_fun_name. eapply Disjoint_sym. eapply occurs_free_fundefs_name_in_fundefs_Disjoint. }

    rewrite !image_Union. eapply Union_Included.
    eapply Included_trans. eapply IHB. reflexivity. now sets.
    eapply Setminus_Included_Included_Union.
    eapply Included_trans. eapply IHe. rewrite rename_all_fun_name.
    eapply Included_trans. eapply image_remove_all.
    rewrite <- !Same_set_all_fun_name at 1. sets.
  - rewrite FromList_apply_list, image_Union, image_Singleton in *. sets.
  - eapply Setminus_Included_Included_Union.
    rewrite Union_commut.
    eapply Included_trans. 2:eapply image_apply_r_remove. sets.
  - rewrite FromList_apply_list, image_Union.
    eapply Included_Union_compat. sets. eapply Setminus_Included_Included_Union.
    eapply Included_trans. eapply IHe. eapply Included_trans.
    eapply image_apply_r_remove. sets.
  - rewrite image_Singleton. sets.
  - intros M Hsub (* Hdis *). repeat normalize_occurs_free; repeat normalize_bound_var.
    erewrite !Setminus_Union_distr, !Setminus_Union. apply Union_Included; sets.
    + eapply Setminus_Included_Included_Union.
      eapply Included_trans. eapply IHe. eapply Included_trans.
      eapply image_remove_all. eapply Union_Included; [| now sets ].
      eapply Included_trans. eapply image_remove_all.
      eapply Union_Included; [| now sets ].
      rewrite !image_Union. do 2 eapply Included_Union_preserv_l.
      rewrite !Setminus_Union. eapply image_monotonic. eapply Included_Setminus_compat.
      now sets. rewrite (Union_commut (FromList l)), Union_assoc. rewrite <- Union_assoc.
      eapply Union_Included. eapply Included_trans. eassumption. now sets. now sets.
    + rewrite (Union_commut [set v]) at 1. rewrite <- Setminus_Union.
      eapply Included_trans. eapply Included_Setminus_compat. eapply IHB.
      eapply Included_trans; [| eassumption ]. now sets. reflexivity.
      rewrite <- image_remove_all_Disjoint; [| eapply Disjoint_Setminus_l; reflexivity ].
      rewrite <- (image_apply_r_remove_all_Singleton m v) at 1.
      eapply Included_trans. eapply image_Setminus. now tci.
      rewrite image_remove_all_Disjoint.
      rewrite image_Union, Setminus_Union, !(Union_commut [set v]). now sets.
      now sets. eapply Hsub. sets.
  - intros M Hsub. rewrite !occurs_free_fundefs_Fnil at 1.
    sets.
Qed.

Lemma rename_all_occurs_free :
  forall e m,
    occurs_free (rename_all m e) \subset (image (apply_r m) (occurs_free e)).
Proof. eapply rename_all_occurs_free_mut. Qed.

Lemma bound_var_rename_all_ns_mut:
  forall sigma,
    (forall (e : exp),
        bound_var e <--> bound_var (rename_all_ns sigma e)) /\
    (forall (fds : fundefs),
        bound_var_fundefs fds <--> bound_var_fundefs (rename_all_fun_ns sigma fds)).
Proof.
  intro sig.
  apply exp_def_mutual_ind; intros; simpl;
    repeat (normalize_bound_var); split; try (rewrite H); try (rewrite H0); auto with Ensembles_DB.
Qed.

Lemma bound_var_rename_all_ns:
  (forall (e : exp) sigma,
      bound_var e <--> bound_var (rename_all_ns sigma e)).
Proof.
  intros. apply bound_var_rename_all_ns_mut.
Qed.

Lemma bound_var_rename_all_ns_fundefs:
  (forall (fds : fundefs) sigma,
      bound_var_fundefs fds <--> bound_var_fundefs (rename_all_fun_ns sigma fds)).
Proof.
  intros. apply bound_var_rename_all_ns_mut.
Qed.

Lemma unique_bindings_rename_all_ns:
  (forall e sigma,
      unique_bindings e -> unique_bindings (rename_all_ns sigma e)) /\
  (forall fds sigma,
      unique_bindings_fundefs fds -> unique_bindings_fundefs (rename_all_fun_ns sigma fds)).
Proof.
  apply exp_def_mutual_ind; intros; simpl.
  - inv H0. eapply H in H6.
    constructor; eauto.
    intro. apply H3.
    eapply (bound_var_rename_all_ns).
    apply H0.
  - constructor.
  - inv H1.
    constructor.
    eapply H0 in H5.
    simpl in H5. apply H5.
    apply H. auto.
    rewrite <- (bound_var_rename_all_ns).
    rewrite (bound_var_rename_all_ns) with (e := (Ecase v l)) in H8.
    simpl in H8.
    apply H8.
  - inv H0.
    constructor; auto.
    intro; apply H3.
    eapply (bound_var_rename_all_ns).
    eauto.
  - inv H0. eapply H in H7.
    constructor; eauto.
    intro. apply H3.
    eapply (bound_var_rename_all_ns).
    apply H0.
  - inv H1.
    constructor.
    apply H0. auto.
    apply H; auto.
    rewrite <- (bound_var_rename_all_ns).
    rewrite <- (bound_var_rename_all_ns_fundefs).
    auto.
  - constructor.
  - inv H0; constructor.
    intro; apply H3.
    eapply (bound_var_rename_all_ns).
    apply H0.
    apply H.
    auto.
  - inv H0; constructor.
    intro; apply H3.
    eapply (bound_var_rename_all_ns).
    apply H0.
    apply H.
    auto.
  - constructor.
  - inv H1.
    constructor; auto.
    intro; apply H7.
    eapply (bound_var_rename_all_ns).
    eauto.
    intro; apply H8.
    eapply (bound_var_rename_all_ns_fundefs).
    eauto.
    rewrite <- (bound_var_rename_all_ns). auto.
    rewrite <- (bound_var_rename_all_ns_fundefs). auto.
    rewrite <- (bound_var_rename_all_ns).
    rewrite <- (bound_var_rename_all_ns_fundefs).
    auto.
  - constructor.
Qed.
