Require Import LambdaANF.term LambdaANF.size_cps LambdaANF.term_util LambdaANF.eval LambdaANF.logical_relations LambdaANF.set_util LambdaANF.identifiers LambdaANF.ctx
        LambdaANF.Ensembles_util LambdaANF.List_util LambdaANF.alpha_conv LambdaANF.functions LambdaANF.uncurry
        LambdaANF.shrink_cps_correct.
From Stdlib Require Import FunInd.
From Stdlib Require Import ZArith.Znumtheory Relations.Relations Arith.Wf_nat Arith.
From Stdlib Require Import Strings.String.
From Stdlib Require Import Lists.List MSets.MSets MSets.MSetRBT Numbers.BinNums
        NArith.BinNat PArith.BinPos Sets.Ensembles micromega.Lia.
Require Import ExtLib.Structures.Monads ExtLib.Data.Monads.StateMonad.

Require Import Common.compM.

Import ListNotations MonadNotation.

Section list_lemmas.
  Lemma set_lists_length : forall {A} (l : list M.elt) (l1 : list A) (rho rho1 : M.t A),
    Some rho1 = set_lists l l1 rho -> length l = length l1.
  Proof.
    induction l; intros.
    - (* [] *) destruct l1; [easy|now simpl in H].
    - (* :: *) destruct l1; [now simpl in H|].
      simpl. apply f_equal.
      remember (set_lists l l1 rho).
      destruct o.
      + eapply IHl. simpl in H. eapply Heqo.
      + simpl in H. now rewrite <- Heqo in H.
  Qed.

  Lemma exists_set_lists_iff_length : forall {A} (l : list M.elt) (l1 : list A) (rho : M.t A),
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
    - (* :: <- *) destruct l1; [easy|]. simpl in H. apply Nat.succ_inj in H.
      rewrite <- IHl with (rho := rho) in H. destruct H.
      simpl. rewrite <- H. now exists (M.set a a0 x).
  Qed.

  Corollary exists_set_lists_length : forall {A} (l : list M.elt) (l1 : list A) (rho : M.t A),
    (exists rho1, Some rho1 = set_lists l l1 rho) -> length l = length l1.
  Proof. intros; now rewrite <- @exists_set_lists_iff_length with (rho := rho). Qed.

  Corollary length_exists_set_lists : forall {A} (l : list M.elt) (l1 : list A) (rho : M.t A),
     length l = length l1 -> (exists rho1, Some rho1 = set_lists l l1 rho).
  Proof. intros; now rewrite @exists_set_lists_iff_length with (rho := rho). Qed.

  (* nesting set_listss (TODO: move to term.v?) *)
  Lemma set_lists_set_lists : forall {A} (l l1 : list M.elt) (v v1 : list A) (rho rho1 rho2 : M.t A),
    Some rho1 = set_lists l v rho ->
    Some rho2 = set_lists l1 v1 rho1 ->
    Some rho2 = set_lists (l1 ++ l) (v1 ++ v) rho.
  Proof.
    induction l1.
    - (* [] *)
      intros. assert (v1 = []) by (apply set_lists_length in H0; now destruct v1). subst.
      inversion H0. now subst.
    - (* :: *)
      intros. destruct v1; [apply set_lists_length in H0; inversion H0|].
      simpl in *. remember (set_lists l1 v1 rho1). destruct o; [|congruence].
      now rewrite <- (IHl1 _ _ _ _ _ H Heqo).
  Qed.

  (* expose an M.set from a successful set_lists *)
  Lemma set_set_lists : forall {A} h h1 (t : list M.elt) (t1 : list A) (rho rho2 : M.t A),
    Some rho2 = set_lists (h :: t) (h1 :: t1) rho -> exists rho1,
    rho2 = M.set h h1 rho1 /\ Some rho1 = set_lists t t1 rho.
  Proof.
    simpl. intros. remember (set_lists t t1 rho). destruct o; [|congruence].
    inversion H. inversion H. subst. eauto.
  Qed.

  Lemma set_lists_set : forall {A} a b (l : list M.elt) (v : list A) (rho : M.t A),
    set_lists l v (M.set a b rho) = set_lists (l ++ [a]) (v ++ [b]) rho.
  Proof.
    induction l; intros.
    - (* [] *) destruct v; [easy|destruct v; easy].
    - (* :: *) destruct v. simpl.
      assert (set_lists (l ++ [a]) [] rho = None) by (now destruct l). now rewrite H.
      simpl in *.
      remember (set_lists l v (M.set a b rho)).
      remember (set_lists (l ++ [a]) (v ++ [b]) rho).
      destruct o, o0; [| | |auto].
      + rewrite <- IHl in Heqo0. rewrite <- Heqo in Heqo0. inversion Heqo0; now subst.
      + apply set_lists_length in Heqo.
        assert (length (l ++ [a]) = length (v ++ [b]))
          by (repeat rewrite length_app; now rewrite Heqo).
        apply @length_exists_set_lists with (rho := rho) in H. destruct H. congruence.
      + assert (length l = length v). {
          apply set_lists_length in Heqo0.
          repeat rewrite length_app in Heqo0. simpl in Heqo0. lia.
        }
        apply @length_exists_set_lists with (rho := (M.set a b rho)) in H. destruct H. congruence.
  Qed.

  Lemma list_length_cons : forall {A} {B} h (l : list A) (t : list B),
    length l = length (h :: t) -> exists h1 t1, l = h1 :: t1.
  Proof. intros. destruct l; [easy|now exists a, l]. Qed.

  Lemma list_length_snoc : forall {A} {B} (l : list A) (a : list B) b,
    length l = length (a ++ [b]) -> exists a1 b1, l = a1 ++ [b1].
  Proof.
    induction l; intros.
    - rewrite length_app in H. inversion H. rewrite Nat.add_comm in H1. inversion H1.
    - destruct a0.
      + assert (l = []) by (destruct l; [easy|inversion H]). subst.
        now exists [], a.
      + inversion H. destruct (IHl _ _ H1) as [a1 [b1 Hab1]].
        exists (a :: a1), b1. simpl. now apply f_equal.
  Qed.

  Lemma set_lists_fresh : forall {A} v1 v v2 w1 w w2 (rho rho1 : M.t A),
    length v1 = length w1 ->
    ~ List.In v v1 ->
    Some rho1 = set_lists (v1 ++ [v] ++ v2) (w1 ++ [w] ++ w2) rho ->
    M.get v rho1 = Some w.
  Proof.
    induction v1.
    - intros. assert (w1 = []) by (destruct w1; easy; inversion H). subst.
      simpl in H1. remember (set_lists v2 w2 rho).
      destruct o; [|congruence]. inversion H1. now rewrite M.gss.
    - intros. symmetry in H.
      destruct (list_length_cons _ _ _ H) as [w1h [w1t Hw1]]. subst.
      inversion H.
      simpl in H1. remember (set_lists (v1 ++ v :: v2) (w1t ++ w :: w2) rho).
      destruct o; [|congruence]. inversion H1; subst.
      rewrite not_in_cons in H0. destruct H0.
      rewrite M.gso; [|assumption].
      eapply IHv1; [symmetry; eassumption|assumption|simpl; eassumption].
  Qed.

  Lemma get_list_set_lists_app : forall {A} v v1 w w1 (rho rho1 : M.t A),
    length v = length w ->
    NoDup v ->
    Some rho1 = set_lists (v ++ v1) (w ++ w1) rho ->
    get_list v rho1 = Some w.
  Proof.
    induction v; intros.
    - assert (w = []) by (destruct w; easy; inversion H). now subst.
    - inversion H0; subst. destruct w; [inversion H|].
      simpl in H1. remember (set_lists (v ++ v1) (w ++ w1) rho).
      destruct o; [|congruence]. inversion H1; subst.
      simpl. rewrite get_list_set_neq; [|assumption].
      erewrite IHv; [now rewrite M.gss|now inversion H|assumption|eassumption].
  Qed.

  Lemma Disjoint_FromList_cons_right : forall {A} (a : list A) h t,
    Disjoint _ (FromList a) (FromList (h :: t)) ->
    Disjoint _ (FromList a) (FromList t).
  Proof.
    intros. constructor. intros x contra.
    inv contra. inv H.
    contradiction (H2 x).
    constructor; [|right]; assumption.
  Qed.

  Lemma get_list_set_lists_disjoint_app : forall {A} u v w v1 w1 (rho rho1 : M.t A),
    Disjoint _ (FromList u) (FromList v) ->
    length v = length w ->
    Some rho1 = set_lists (v ++ v1) (w ++ w1) rho ->
    exists rho2, Some rho2 = set_lists v1 w1 rho /\ get_list u rho1 = get_list u rho2.
  Proof.
    induction v; intros.
    - assert (w = []) by (destruct w; easy; inversion H). subst. now exists rho1.
    - destruct w; inversion H0.
      simpl in H1. remember (set_lists (v ++ v1) (w ++ w1) rho).
      destruct o; [inversion H1; subst|congruence].
      replace (get_list u (M.set a a0 t)) with (get_list u t).
      eapply IHv; [|eassumption|assumption].
      eapply Disjoint_FromList_cons_right. eassumption.
      symmetry. apply get_list_set_neq.
      intros contra. inversion H. contradiction (H2 a).
      split; [assumption|now left].
  Qed.

  Lemma list_in_iff_Included : forall {A} a (l : list A),
    List.In a l <-> In _ (FromList l) a.
  Proof. split; intros; auto. Qed.

  Lemma not_list_in_app : forall {A} a (l r : list A),
    ~ List.In a (l ++ r) <-> ~ List.In a l /\ ~ List.In a r.
  Proof.
    split; intros.
    - induction l. split; [auto|]. assumption.
      apply not_in_cons in H. destruct H.
      destruct (IHl H0) as [H1 H2].
      split; [|assumption].
      intros [HL|HR]; congruence.
    - destruct H. induction l. simpl. assumption.
      apply not_in_cons in H. destruct H.
      simpl. intros [HL|HR]; [congruence|now apply IHl in H1].
  Qed.
End list_lemmas.

(* need a stronger definition of size to prove that the functional
   induction scheme is well-founded *)
(* Print exp. *)
Fixpoint sizeof_exp e : nat :=
  match e with
    (Econstr x _ ys e) => 1 + length ys + sizeof_exp e
  | (Ecase x l) =>
    1 + (fix sizeof_l l :=
            match l with
              [] => 0
            | (t, e) :: l => 1 + sizeof_exp e + sizeof_l l
            end) l
  | (Eproj x _ _ y e) => 1 + sizeof_exp e
  | (Eletapp _ _ _ xs e) => 1 + length xs + sizeof_exp e
  | (Efun fds e) => 1 + sizeof_fundefs fds + sizeof_exp e
  | (Eapp x _ ys) => 1 + length ys
  | (Eprim x _ ys e) => 1 + length ys + sizeof_exp e
  | (Eprim_val x p e) => 1 + sizeof_exp e
  | (Ehalt x) => 1
  end
with sizeof_fundefs f : nat :=
  match f with
  | Fcons f t v e fds => 1 + sizeof_exp e + sizeof_fundefs fds
  | Fnil => 0
  end.

Definition sizeof (a : exp + fundefs) : nat :=
  match a with inl e => sizeof_exp e | inr f => sizeof_fundefs f end.

Definition reflect_eq_var (a b : var) : (a = b) + (a <> b) :=
  match Pos.eqb_spec a b with
    ReflectT yes => inl yes
  | ReflectF no => inr no
  end.

(* all variables in a list are distinct and disjoint from some set of used vars *)
Definition fresh_copies (s : Ensemble var) (l : list var) : Prop
  := Disjoint _ s (FromList l) /\ NoDup l.

(* "a small step" of uncurrying *)
Inductive uncurry_step :
  exp -> (* original expression *)
  Ensemble var -> (* used variables *)
  localMap -> (* already uncurried functions *)
  exp -> (* expression w/ 1 function uncurried *)
  Ensemble var -> (* new used variables *)
  localMap -> (* new uncurried functions *)
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
| uncurry_prim_val : forall x p e e1 s s1 m m1,
    uncurry_step e s m e1 s1 m1 ->
    uncurry_step (Eprim_val x p e) s m (Eprim_val x p e1) s1 m1
| uncurry_prim : forall x p args e e1 s s1 m m1,
    uncurry_step e s m e1 s1 m1 ->
    uncurry_step (Eprim x p args e) s m (Eprim x p args e1) s1 m1
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
      (* TODO: restrict ft1? *)
| uncurry_fundefs_curried_anf :
    forall f f1 ft ft1 fv fv1
           g gt gv gv1 ge fds s m s',
    match M.get g m with Some true => true | _ => false end = false ->
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

#[global] Hint Constructors uncurry_step : core.
#[global] Hint Constructors uncurry_fundefs_step : core.

Scheme uncurry_step_mut := Minimality for uncurry_step Sort Prop
with uncurry_step_fundefs_mut := Minimality for uncurry_fundefs_step Sort Prop.

Ltac uncurry_step_induction P Q IHuncurry IH :=
  apply uncurry_step_mut with (P := P) (P0 := Q);
  [ intros ? ? ? ? ? ? ? ? ? ? IHuncurry IH
  | intros ? ? ? ? ? ? ? ? ? IHuncurry IH
  | intros ? ? ? ? ? ? ? ? ? IHuncurry IH
  | intros ? ? ? ? ? ? ? ? IHuncurry IH
  | intros ? ? ? ? ? ? ? ? ? ? IHuncurry IH
  | intros ? ? ? ? ? ? ? ? IHuncurry IH
  | intros ? ? ? ? ? ? ? ? ? IHuncurry IH
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
(forall (x : var) p (e e1 : exp) (s s1 : Ensemble var) (m m1 : localMap),
 uncurry_step e s m e1 s1 m1 ->
 P e s m e1 s1 m1 -> P (Eprim_val x p e) s m (Eprim_val x p e1) s1 m1) ->
(forall (x : var) (p : prim) (args : list var) (e e1 : exp) (s s1 : Ensemble var) (m m1 : localMap),
 uncurry_step e s m e1 s1 m1 ->
 P e s m e1 s1 m1 -> P (Eprim x p args e) s m (Eprim x p args e1) s1 m1) ->
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
Ltac uncurry_step_induction_mut P Q IHuncurry IH :=
  apply uncurry_step_mutual_ind with (P := P) (P0 := Q);
  [ intros ? ? ? ? ? ? ? ? ? ? IHuncurry IH
  | intros ? ? ? ? ? ? ? ? ? IHuncurry IH
  | intros ? ? ? ? ? ? ? ? ? IHuncurry IH
  | intros ? ? ? ? ? ? ? ? IHuncurry IH
  | intros ? ? ? ? ? ? ? ? ? ? IHuncurry IH
  | intros ? ? ? ? ? ? ? ? IHuncurry IH
  | intros ? ? ? ? ? ? ? ? ? IHuncurry IH
  | intros ? ? ? ? ? ? ? IHuncurry IH
  | intros ? ? ? ? ? ? ? IHuncurry IH
  | intros ? ? ? ? ? ? ? ? ? ? IHuncurry IH
  | intros ? ? ? ? ? ? ? ? ? ? IHuncurry IH
  | intros
  | intros
  ].

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

Lemma set_lists_set_permut : forall {A} x (y : A) xs ys rho rho',
  ~ List.In x xs ->
  Some rho' = set_lists xs ys (M.set x y rho) -> exists rho1,
  Some rho1 = set_lists xs ys rho /\ forall a,
  M.get a rho' = M.get a (M.set x y rho1).
Proof.
  intros A x y xs ys rho rho' Hx Hrho.
  assert (Hrho1 : length xs = length ys) by now apply set_lists_length in Hrho.
  eapply length_exists_set_lists in Hrho1; destruct Hrho1 as [rho1 Hrho1].
  exists rho1; split; [apply Hrho1|].
  intros a.
  split_var_in_list a xs.
  - assert (forall A (l : list A), Forall2 eq l l) by (induction l; auto); specialize H with (l := ys).
    symmetry in Hrho, Hrho1.
    destruct (set_lists_Forall2_get _ _ _ _ _ _ _ _ _ H Hrho Hrho1 i)
      as [v1 [v2 [Hv1 [Hv2 Hv1_v2]]]]; subst.
    rewrite M.gso.
    transitivity (Some v2); auto.
    intros Ha; contradiction Hx; now subst.
  - erewrite <- set_lists_not_In; [|symmetry in Hrho; apply Hrho|assumption].
    split_var_eq a x; [subst; now do 2 rewrite M.gss|].
    do 2 (rewrite M.gso; [|assumption]).
    erewrite <- @set_lists_not_In with (rho' := rho1); eauto.
Qed.

Lemma Ensemble_In : forall {U : Type} S a,
  In U S a -> S a.
Proof. auto. Qed.

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

Lemma uncurry_step_preserves_ctag : forall x s m s1 m1 arms arms1,
  uncurry_step (Ecase x arms) s m (Ecase x arms1) s1 m1 ->
  Forall2 (fun p p' : ctor_tag * exp => fst p = fst p') arms arms1.
Proof.
  induction arms; intros.
  - destruct arms1; inv H.
  - destruct arms1; inv H; (constructor; [easy|]); auto.
    now apply List_util.Forall2_refl.
Qed.

Lemma Union_Included_subst_l: forall (A : Type) (a b b' c : Ensemble A),
  a :|: b' \subset c -> b \subset b' -> a :|: b \subset c.
Proof. intros; intros x Hx; destruct Hx; eauto with Ensembles_DB. Qed.

Lemma used_vars_fundefs_Fcons_Included: forall f t v e fds,
  used_vars_fundefs fds \subset used_vars_fundefs (Fcons f t v e fds).
Proof. intros; normalize_used_vars; auto with Ensembles_DB. Qed.

Lemma used_vars_Fcons_Included: forall f t v e fds,
  used_vars e \subset used_vars_fundefs (Fcons f t v e fds).
Proof. intros; normalize_used_vars; auto with Ensembles_DB. Qed.

Lemma used_vars_Eprim_cons_Included: forall x p a args e,
  used_vars (Eprim x p args e) \subset used_vars (Eprim x p (a :: args) e).
Proof. intros; repeat normalize_used_vars; normalize_sets; auto with Ensembles_DB. Qed.

Lemma used_vars_Efun_Included: forall fds e,
  used_vars e \subset used_vars (Efun fds e).
Proof. intros; normalize_used_vars; auto with Ensembles_DB. Qed.

Lemma used_vars_fundefs_Efun_Included: forall fds e,
  used_vars_fundefs fds \subset used_vars (Efun fds e).
Proof. intros; normalize_used_vars; auto with Ensembles_DB. Qed.

Lemma uncurry_step_s_nondecreasing_mut :
  let P := (fun e s m e1 s1 m1 => s \subset s1) in
  let Q := (fun f s m f1 s1 m1 => s \subset s1) in
  (forall e s m e1 s1 m1, uncurry_step e s m e1 s1 m1 -> P e s m e1 s1 m1) /\
  (forall f s m f1 s1 m1, uncurry_fundefs_step f s m f1 s1 m1 -> Q f s m f1 s1 m1).
Proof with auto with Ensembles_DB.
  intros P Q.
  uncurry_step_induction_mut P Q IHstep IH;
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
  uncurry_step_induction_mut P Q IHstep IH; subst P; subst Q; simpl in *; intros He;
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
  - apply uncurry_step_s_nondecreasing in IHstep. repeat normalize_used_vars; destruct_Union_Included.
    eapply Union_Included; eauto with Ensembles_DB.
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
  uncurry_step e s m e1 s1 m1 -> used_vars e \subset s -> used_vars e1 \subset s1.
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
  uncurry_step_induction_mut P Q IHstep IH; subst P; subst Q; simpl in *; intros;
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

Lemma uncurry_step_maintains_used_vars_mut :
  let P := (fun e s m e1 s1 m1 =>
              used_vars e \subset s -> used_vars e1 :&: s <--> used_vars e) in
  let Q := (fun f s m f1 s1 m1 =>
              used_vars_fundefs f \subset s ->
              used_vars_fundefs f1 :&: s <--> used_vars_fundefs f) in
  (forall e s m e1 s1 m1, uncurry_step e s m e1 s1 m1 -> P e s m e1 s1 m1) /\
  (forall f s m f1 s1 m1, uncurry_fundefs_step f s m f1 s1 m1 -> Q f s m f1 s1 m1).
Proof with eauto with Ensembles_DB.
  intros P Q.
  uncurry_step_induction_mut P Q IHstep IH; subst P; subst Q; simpl in *; intros;
  try destruct arm;
  try (
    repeat normalize_used_vars;
    rewrite Intersection_Union_distr;
    rewrite IH; [rewrite Intersection_Same_set; eauto with Ensembles_DB|];
    eapply Included_trans; [|eauto| |eauto]; eauto with Ensembles_DB).
  - (* Eletapp *)
    repeat rewrite used_vars_Eletapp in *.
    do 2 rewrite Intersection_Union_distr.
    rewrite IH.
    rewrite Intersection_Same_set...
    rewrite Intersection_Same_set...
    eapply Included_trans; [|eassumption]...
    eapply Included_trans; [|eassumption]...
  - (* Eproj *)
    repeat rewrite used_vars_Eproj.
    do 2 rewrite Intersection_Union_distr.
    rewrite IH.
    rewrite Intersection_Same_set...
    rewrite Intersection_Same_set...
    all: rewrite used_vars_Eproj in H...
    eapply Included_trans; eauto...
  - repeat normalize_used_vars. rewrite Intersection_Union_distr.
    rewrite IH; [rewrite Intersection_Same_set; eauto with Ensembles_DB|].
    eapply Included_trans; [|eauto]; eauto with Ensembles_DB.
  - (* Fcons fds *)
    repeat rewrite used_vars_Fcons.
    repeat rewrite Intersection_Union_distr.
    rewrite IH.
    repeat rewrite Intersection_Same_set...
    all: rewrite used_vars_Fcons in H.
    eapply Included_trans; [|eassumption]...
    eapply Union_Included_r.
    do 2 eapply Union_Included_l...
    do 3 eapply Union_Included_l...
    eapply Included_trans; [|eassumption]...
  - (* Fcons curried *)
    assert (Hsubst :
            used_vars_fundefs
              (Fcons f9 ft (k :: fv1)
                     (Efun (Fcons g gt gv1
                                  (Eapp f10 ft1 (gv1 ++ fv1))
                                  Fnil)
                           (Eapp k kt [g]))
                     (Fcons f10 ft1 (gv ++ fv) ge fds)) <-->
           used_vars_fundefs
              (Fcons f9 ft (k :: fv) (Efun (Fcons g gt gv ge Fnil) (Eapp k kt [g])) fds)
              :|: FromList (f10 :: fv1 ++ gv1)). {
      repeat (rewrite used_vars_Fcons + rewrite used_vars_Efun).
      repeat rewrite used_vars_Eapp.
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
    eapply Union_Included_l...
  - (* anf *)
    repeat normalize_used_vars; repeat normalize_sets.
    repeat rewrite Intersection_Union_distr.
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
    repeat rewrite In_or_Iff_Union.
    rewrite Hgv1, Hfv1, Hf11.
    repeat rewrite In_Empty_set.
    assert (False_neut_r : forall A, A \/ False <-> A) by tauto.
    assert (False_neut_l : forall A, False \/ A <-> A) by tauto.
    repeat (rewrite False_neut_l || rewrite False_neut_r).
    assert (Intersection_and_iff : forall S1 S2 x, In var (S1 :&: S2) x <-> In _ S1 x /\ In _ S2 x). {
      intros x; split; destruct 1; split; auto. }
    repeat rewrite Intersection_and_iff.
    rename H7 into Hused.
    clear - Hused.
    specialize (Hused arbitrary).
    repeat rewrite In_or_Iff_Union in Hused.
    tauto.
Qed.

Corollary uncurry_step_maintains_used_vars: forall e s m e1 s1 m1,
  uncurry_step e s m e1 s1 m1 ->
  used_vars e \subset s ->
  used_vars e1 :&: s <--> used_vars e.
Proof. apply uncurry_step_maintains_used_vars_mut. Qed.

Corollary uncurry_fundefs_step_maintains_used_vars: forall f s m f1 s1 m1,
  uncurry_fundefs_step f s m f1 s1 m1 ->
  used_vars_fundefs f \subset s ->
  used_vars_fundefs f1 :&: s <--> used_vars_fundefs f.
Proof. apply uncurry_step_maintains_used_vars_mut. Qed.

Corollary uncurry_step_maintains_used_vars_fn: forall e s m e1 s1 m1,
  uncurry_step e s m e1 s1 m1 ->
  used_vars e \subset s -> forall a,
  In _ (used_vars e1) a ->
  In _ s a ->
  In _ (used_vars e) a.
Proof. intros; rewrite <- uncurry_step_maintains_used_vars; eauto. Qed.

Corollary uncurry_fundefs_step_maintains_used_vars_fn: forall f s m f1 s1 m1,
  uncurry_fundefs_step f s m f1 s1 m1 ->
  used_vars_fundefs f \subset s -> forall a,
  In _ (used_vars_fundefs f1) a ->
  In _ s a ->
  In _ (used_vars_fundefs f) a.
Proof. intros; rewrite <- uncurry_fundefs_step_maintains_used_vars; eauto. Qed.

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
  uncurry_step_induction_mut P Q IHstep IH; subst P; subst Q; simpl in *; intros.
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
  - (* Eprim_val *)
    rewrite used_vars_Eprim_val in H; inv H0.
    assert (used_vars e \subset s).
    eapply Union_Included_r...
    constructor; auto.
    intros contra; contradiction H3; eapply uncurry_step_maintains_bindings_fn; eauto.
  - (* Eprim *)
    rewrite used_vars_Eprim in H; inv H0.
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
      intros contra; contradiction H6; apply H8; do 3 left; right; now left.
      intros contra; contradiction H6; apply H8; right; now left.
      constructor; intros a contra; inv contra.
      rewrite FromList_app in H15; destruct H15.
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
      apply List_util.NoDup_app.
      inv H9. inv H26. now inv H16.
      inv H9. now inv H25.
      constructor; intros a contra; inv contra.
      inv H9. inv H23. contradiction (H9 a); split; auto; now right.
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
    | |- NoDup (_ ++ _) => apply List_util.NoDup_app
    end...
    + intros Hin. apply (Disjoint_In_falso _ _ Hin)...
    + now apply Disjoint_sym.
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

#[global] Hint Constructors unique_bindings : core.

Lemma uncurry_fundefs_step_unique_names : forall a f s m f1 s1 m1,
  used_vars_fundefs f \subset s ->
  uncurry_fundefs_step f s m f1 s1 m1 ->
  name_in_fundefs f1 a ->
  ~ name_in_fundefs f a ->
  ~ In var s a.
Proof with eauto with Ensembles_DB.
  intros a f s m f1 s1 m1 Hused Hstep Hf1 Hf.
  induction Hstep; try solve [inv Hf1; [inv H0|]; contradiction Hf; [now left|now right]].
  - apply IHHstep.
    eapply Included_trans; [|eauto]; repeat normalize_used_vars...
    inv Hf1; auto.
    inv H; contradiction Hf; now left.
    intros contra; contradiction Hf; now right.
  - simpl in *.
    inv Hf1; inv H0; inv H8.
    + contradiction Hf; now left.
    + inv H0. intros contra; contradiction H6; now do 2 left.
    + contradiction Hf; now right.
  - simpl in *.
    inv Hf1.
    + contradiction Hf; now left.
    + destruct H7 as [Hf1|Hfds].
      * inv H7.
        intros Hin; contradiction H5; now do 2 left.
      * contradiction Hf; now right.
Qed.

Lemma uncurry_fundefs_step_preserves_names : forall a f s m f1 s1 m1,
  name_in_fundefs f a ->
  uncurry_fundefs_step f s m f1 s1 m1 ->
  name_in_fundefs f1 a.
Proof.
  intros a f s m f1 s1 m1 Hf Hstep.
  induction Hstep; try solve [inv Hf; [inv H0; now left|now right]].
  - inv Hf.
    inv H; now left.
    right; now apply IHHstep.
  - inv Hf.
    inv H7; now left.
    right; now right.
  - inv Hf.
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
  intros a f s m f1 s1 m1 t v e t1 v1 e1 Hused Hstep Hf Hf1.
  induction Hstep; simpl in Hf, Hf1; destruct (M.elt_eq a f); subst;
    inv Hf; inv Hf1; auto;
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
  intros a f s m f1 s1 m1 t v e t1 v1 e1 Hused Hstep Hf Hf1.
  induction Hstep; simpl in Hf, Hf1; destruct (M.elt_eq a f); subst;
    inv Hf; inv Hf1; auto;
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

Lemma Union_Setminus_Included : forall {U : Type} (A B : Ensemble U),
  A :|: B \\ B \subset A.
Proof.
  intros U A B a Ha.
  inv Ha.
  inv H; auto; contradiction.
Qed.

Lemma fundefs_append_assoc : forall A B C,
  fundefs_append A (fundefs_append B C) = fundefs_append (fundefs_append A B) C.
Proof.
  induction A.
  - intros B C; simpl. now rewrite IHA.
  - auto.
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

Lemma fds_noncircular : forall f t v e fds, Fcons f t v e fds <> fds.
Proof. induction fds; inversion 1; now subst. Qed.

Local Ltac circular_fds :=
  match goal with
  | [ H : Fcons ?f ?t ?v ?e ?fds = ?fds |- _ ] =>
    assert (Fcons f t v e fds <> fds) by apply fds_noncircular; contradiction
  | [ H : ?fds = Fcons ?f ?t ?v ?e ?fds |- _ ] =>
    symmetry in H; circular_fds
  end.

Lemma uncurry_step_not_reflexive_mut :
  let P := (fun e s m e1 s1 m1 => e <> e1 /\ s <> s1 /\ m <> m1) in
  let Q := (fun f s m f1 s1 m1 => f <> f1 /\ s <> s1 /\ m <> m1) in
  (forall e s m e1 s1 m1, uncurry_step e s m e1 s1 m1 -> P e s m e1 s1 m1) /\
  (forall f s m f1 s1 m1, uncurry_fundefs_step f s m f1 s1 m1 -> Q f s m f1 s1 m1).
Proof with eauto with Ensembles_DB.
  intros P Q.
  uncurry_step_induction_mut P Q IHstep IH; subst P; subst Q; simpl in *;
    (split; [|split]); try destruct IH as [? [? ?]]; auto;
    intros contra; inv contra; try easy.
  (* uncurry_fundefs_curried *)
  - circular_fds.
  - rewrite H7 in H6.
    contradiction H6.
    left; left; now right.
  - apply f_equal with
      (f := fun a =>
              match M.get g a with
              | Some true => true
              | _ => false
              end) in H8.
    rewrite H in H8.
    now rewrite M.gss in H8.
  (* anf *)
  - circular_fds.
  - rewrite H6 in H5.
    contradiction H5.
    left; left; now right.
  - apply f_equal with
      (f := fun a =>
              match M.get g a with
              | Some true => true
              | _ => false
              end) in H7.
    rewrite H in H7.
    now rewrite M.gss in H7.
Qed.

Local Ltac solve_uncurry_step_not_reflexive :=
  intros; intros H; destruct uncurry_step_not_reflexive_mut as [He Hf];
  try (now apply He in H);
  try (now apply Hf in H).

Corollary uncurry_step_not_reflexive : forall e s m s1 m1, ~ uncurry_step e s m e s1 m1.
Proof. solve_uncurry_step_not_reflexive. Qed.

Corollary uncurry_fundefs_step_not_reflexive : forall f s m s1 m1, ~ uncurry_fundefs_step f s m f s1 m1.
Proof. solve_uncurry_step_not_reflexive. Qed.

Corollary uncurry_step_not_reflexive_s : forall e s m e1 m1, ~ uncurry_step e s m e1 s m1.
Proof. solve_uncurry_step_not_reflexive. Qed.

Corollary uncurry_fundefs_step_not_reflexive_s : forall f s m f1 m1, ~ uncurry_fundefs_step f s m f1 s m1.
Proof. solve_uncurry_step_not_reflexive. Qed.

Corollary uncurry_step_not_reflexive_m : forall e s m e1 s1, ~ uncurry_step e s m e1 s1 m.
Proof. solve_uncurry_step_not_reflexive. Qed.

Corollary uncurry_fundefs_step_not_reflexive_m : forall f s m f1 s1, ~ uncurry_fundefs_step f s m f1 s1 m.
Proof. solve_uncurry_step_not_reflexive. Qed.

Local Ltac step_isnt_reflexive :=
  match goal with
  | [ H : uncurry_step ?a _ _ ?a _ _ |- _ ] =>
    now apply uncurry_step_not_reflexive in H
  | [ H : uncurry_fundefs_step ?a _ _ ?a _ _ |- _ ] =>
    now apply uncurry_fundefs_step_not_reflexive in H
  end.

Lemma circular_app_f_ctx : forall f t v e e1 e2 ctx,
  Fcons f t v e (ctx <[ e1 ]>) <> ctx <[ e2 ]>.
Proof.
  induction ctx; intros contra.
  inv contra. circular_fds.
  inv contra. contradiction.
Qed.

Lemma uncurry_step_subterm_invariant_mut :
  (forall c, (fun c => forall e s m e1 s1 m1,
    uncurry_step (c |[ e ]|) s m (c |[ e1 ]|) s1 m1 ->
    uncurry_step e s m e1 s1 m1) c) /\
  (forall f, (fun f => forall e s m e1 s1 m1,
    uncurry_fundefs_step (f <[ e ]>) s m (f <[ e1 ]>) s1 m1 ->
    uncurry_step e s m e1 s1 m1) f).
Proof. (* with eauto with Ensembles_DB.*)
  exp_fundefs_ctx_induction IHe IHf; simpl;
    try rename e into c;
    try intros arms e s m e1 s1 m1 Hstep;
    try intros e s m e1 s1 m1 Hstep;
    try solve [easy|inv Hstep; now apply IHe].
  - (* Efun1_c *)
    induction l.
    + inv Hstep.
      now apply IHe.
      step_isnt_reflexive.
    + apply IHl.
      inv Hstep.
      step_isnt_reflexive.
      assumption.
  - (* Efun2_c *)
    apply IHe.
    inv Hstep.
    assumption.
    step_isnt_reflexive.
  - (* Fcons1_c *)
    inv Hstep.
    step_isnt_reflexive.
    now apply IHf.
  - (* Fcons2_c *)
    inv Hstep.
    step_isnt_reflexive.
    now apply IHe.
    apply IHe.
    rewrite <- H2; rewrite <- H5.
    apply uncurry_fun_fds; auto.
    circular_fds.
    circular_fds.
  - (* Fcons3_c *)
    inv Hstep.
    + now apply IHf.
    + step_isnt_reflexive.
    + pose circular_app_f_ctx.
      exfalso; eapply n; eauto.
    + pose circular_app_f_ctx.
      exfalso; eapply n; eauto.
Qed.

Corollary uncurry_step_subterm_invariant : forall c e s m e1 s1 m1,
  uncurry_step (c |[ e ]|) s m (c |[ e1 ]|) s1 m1 ->
  uncurry_step e s m e1 s1 m1.
Proof. apply uncurry_step_subterm_invariant_mut. Qed.

Corollary uncurry_fundefs_step_subterm_invariant : forall f e s m e1 s1 m1,
  uncurry_fundefs_step (f <[ e ]>) s m (f <[ e1 ]>) s1 m1 ->
  uncurry_step e s m e1 s1 m1.
Proof. apply uncurry_step_subterm_invariant_mut. Qed.

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

Corollary app_ctx_uncurry_fundefs_step : forall f e s m e1 s1 m1,
    used_vars_fundefs (f <[ e ]>) \subset s ->
    uncurry_step e s m e1 s1 m1 ->
    uncurry_fundefs_step (f <[ e ]>) s m (f <[ e1 ]>) s1 m1.
Proof. apply app_ctx_uncurry_step_mut. Qed.

Lemma uncurry_step_increases_size_mut :
  let P := (fun e s m e1 s1 m1 => sizeOf_exp e < sizeOf_exp e1) in
  let Q := (fun f s m f1 s1 m1 => sizeOf_fundefs f < sizeOf_fundefs f1) in
  (forall e s m e1 s1 m1, uncurry_step e s m e1 s1 m1 -> P e s m e1 s1 m1) /\
  (forall f s m f1 s1 m1, uncurry_fundefs_step f s m f1 s1 m1 -> Q f s m f1 s1 m1).
Proof with eauto with Ensembles_DB.
  intros P Q.
  uncurry_step_induction_mut P Q IHstep IH; subst P; subst Q;
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

Local Ltac step_isnt_cyclic :=
  match goal with
  | [ H : uncurry_step ?a _ _ ?b _ _,
      H1 : uncurry_step ?b _ _ ?a _ _ |- _ ] =>
    destruct (uncurry_step_acyclic _ _ _ _ _ _ _ _ H H1)
  | [ H : uncurry_fundefs_step ?a _ _ ?b _ _,
      H1 : uncurry_fundefs_step ?b _ _ ?a _ _ |- _ ] =>
    destruct (uncurry_fundefs_step_acyclic _ _ _ _ _ _ _ _ H H1)
  end.

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
  uncurry_step_induction_mut P Q IHstep IH; subst P; subst Q; simpl in *;
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
  - (* Fcons term uncurry *)
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

Lemma uncurry_step_preserves_closed : forall e s m e1 s1 m1,
  used_vars e \subset s ->
  unique_bindings e ->
  uncurry_step e s m e1 s1 m1 -> closed_exp e -> closed_exp e1.
Proof with eauto with Ensembles_DB.
  unfold closed_exp; intros.
  destruct uncurry_step_preserves_occurs_free_mut.
  rewrite <- H3; eauto.
Qed.

Lemma uncurry_step_preserves_occurs_free : forall e s m e1 s1 m1,
  used_vars e \subset s ->
  unique_bindings e ->
  uncurry_step e s m e1 s1 m1 -> occurs_free e <--> occurs_free e1.
Proof with eauto with Ensembles_DB.
  destruct uncurry_step_preserves_occurs_free_mut. now eauto.
Qed.

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

#[global] Hint Constructors uncurry_rel : core.
#[global] Hint Constructors uncurry_rel_fundefs : core.

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

Lemma uncurry_rel_preserves_unique_bindings : forall n e s m e1 s1 m1,
  used_vars e \subset s ->
  unique_bindings e ->
  uncurry_rel n e s m e1 s1 m1 ->
  unique_bindings e1.
Proof.
  induction n; [inversion 3; subst; auto|].
  intros.
  inv H1.
  eapply IHn; [| |eassumption].
  eapply uncurry_step_preserves_used_vars; eauto.
  eapply uncurry_step_preserves_unique_bindings; eauto.
Qed.

Lemma uncurry_rel_preserves_closed : forall n e s m e1 s1 m1,
  used_vars e \subset s ->
  unique_bindings e ->
  closed_exp e ->
  uncurry_rel n e s m e1 s1 m1 ->
  closed_exp e1.
Proof.
  induction n; [inversion 4; subst; auto|].
  intros.
  inv H2.
  eapply IHn; [| | |eassumption].
  eapply uncurry_step_preserves_used_vars; eauto.
  eapply uncurry_step_preserves_unique_bindings; eauto.
  eapply uncurry_step_preserves_closed; eauto.
Qed.

Lemma uncurry_rel_preserves_occurs_free : forall n e s m e1 s1 m1,
  used_vars e \subset s ->
  unique_bindings e ->
  uncurry_rel n e s m e1 s1 m1 ->
  occurs_free e <--> occurs_free e1.
Proof.
  induction n; [inversion 3; subst; auto|].
  intros.
  inv H1. subst. reflexivity.
  intros. inv H1. eapply Same_set_trans.
  now eapply uncurry_step_preserves_occurs_free; eauto.
  eapply IHn; [| |eassumption].
  eapply uncurry_step_preserves_used_vars; eauto.
  eapply uncurry_step_preserves_unique_bindings; eauto.
Qed.

Lemma uncurry_rel_preserves_used_vars : forall n e s m e1 s1 m1,
  used_vars e \subset s ->
  uncurry_rel n e s m e1 s1 m1 ->
  used_vars e1 \subset s1.
Proof.
  induction n; [inversion 2; subst; auto|].
  intros.
  inv H0.
  eapply IHn; [|eassumption].
  eapply uncurry_step_preserves_used_vars; eauto.
Qed.

Lemma uncurry_rel_s_nondecreasing : forall n e s m e1 s1 m1,
  uncurry_rel n e s m e1 s1 m1 -> s \subset s1.
Proof.
  induction n; inversion 1; [eauto with Ensembles_DB|subst].
  eapply Included_trans.
  eapply uncurry_step_s_nondecreasing; eauto.
  eapply IHn; eauto.
Qed.

Lemma uncurry_fundefs_rel_s_nondecreasing : forall n f s m f1 s1 m1,
  uncurry_rel_fundefs n f s m f1 s1 m1 -> s \subset s1.
Proof.
  induction n; inversion 1; [eauto with Ensembles_DB|subst].
  eapply Included_trans.
  eapply uncurry_fundefs_step_s_nondecreasing; eauto.
  eapply IHn; eauto.
Qed.

Lemma uncurry_fundefs_rel_preserves_used_vars : forall n f s m f1 s1 m1,
  uncurry_rel_fundefs n f s m f1 s1 m1 ->
  used_vars_fundefs f \subset s ->
  used_vars_fundefs f1 \subset s1.
Proof.
  induction n; inversion 1; [eauto with Ensembles_DB|subst]; intros.
  apply uncurry_fundefs_step_preserves_used_vars in H1; auto.
  eapply IHn; eauto.
Qed.

Lemma uncurry_fundefs_rel_preserves_unique_bindings : forall n f s m f1 s1 m1,
  uncurry_rel_fundefs n f s m f1 s1 m1 ->
  used_vars_fundefs f \subset s ->
  unique_bindings_fundefs f ->
  unique_bindings_fundefs f1.
Proof.
  induction 1; intros; auto.
  apply IHuncurry_rel_fundefs.
  eapply uncurry_fundefs_step_preserves_used_vars; eauto.
  eapply uncurry_fundefs_step_preserves_unique_bindings; eauto.
Qed.

Lemma uncurry_rel_maintains_bindings_fn: forall n e s m e1 s1 m1,
  uncurry_rel n e s m e1 s1 m1 ->
  used_vars e \subset s -> forall a,
  In _ (bound_var e1) a ->
  In _ s a ->
  In _ (bound_var e) a.
Proof.
  induction 1; intros; auto.
  eapply uncurry_step_maintains_bindings_fn; eauto.
  eapply IHuncurry_rel; eauto.
  eapply uncurry_step_preserves_used_vars; eauto.
  eapply uncurry_step_s_nondecreasing; eauto.
Qed.

Lemma uncurry_fundefs_rel_maintains_bindings_fn: forall n f s m f1 s1 m1,
  uncurry_rel_fundefs n f s m f1 s1 m1 ->
  used_vars_fundefs f \subset s -> forall a,
  In _ (bound_var_fundefs f1) a ->
  In _ s a ->
  In _ (bound_var_fundefs f) a.
Proof.
  induction 1; intros; auto.
  eapply uncurry_fundefs_step_maintains_bindings_fn; eauto.
  eapply IHuncurry_rel_fundefs; eauto.
  eapply uncurry_fundefs_step_preserves_used_vars; eauto.
  eapply uncurry_fundefs_step_s_nondecreasing; eauto.
Qed.

Lemma uncurry_rel_maintains_used_vars_fn: forall n e s m e1 s1 m1,
  uncurry_rel n e s m e1 s1 m1 ->
  used_vars e \subset s -> forall a,
  In _ (used_vars e1) a ->
  In _ s a ->
  In _ (used_vars e) a.
Proof.
  induction 1; intros; auto.
  eapply uncurry_step_maintains_used_vars_fn; eauto.
  eapply IHuncurry_rel; eauto.
  eapply uncurry_step_preserves_used_vars; eauto.
  eapply uncurry_step_s_nondecreasing; eauto.
Qed.

Lemma uncurry_fundefs_rel_maintains_used_vars_fn: forall n f s m f1 s1 m1,
  uncurry_rel_fundefs n f s m f1 s1 m1 ->
  used_vars_fundefs f \subset s -> forall a,
  In _ (used_vars_fundefs f1) a ->
  In _ s a ->
  In _ (used_vars_fundefs f) a.
Proof.
  induction 1; intros; auto.
  eapply uncurry_fundefs_step_maintains_used_vars_fn; eauto.
  eapply IHuncurry_rel_fundefs; eauto.
  eapply uncurry_fundefs_step_preserves_used_vars; eauto.
  eapply uncurry_fundefs_step_s_nondecreasing; eauto.
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

Lemma uncurry_rel_fundefs_Efun : forall n f s m f1 s1 m1 e,
  uncurry_rel_fundefs n f s m f1 s1 m1 ->
  uncurry_rel n (Efun f e) s m (Efun f1 e) s1 m1.
Proof.
  induction n; intros; inv H; auto.
  eapply IHn in H2.
  econstructor; eauto.
Qed.

Lemma uncurry_step_Ecase_l : forall v arms s m arms1 s1 m1,
  uncurry_step (Ecase v arms) s m (Ecase v arms1) s1 m1 -> exists l c e e1 r,
  arms = l ++ (c, e) :: r /\ arms1 = l ++ (c, e1) :: r /\ uncurry_step e s m e1 s1 m1.
Proof.
  induction arms; intros; inv H.
  exists [], c, e, e1, arms; eauto.
  apply IHarms in H8.
  destruct H8 as [l [c [e [e1 [r [Harms [Harms2 Hstep]]]]]]].
  exists (a :: l), c, e, e1, r; split; [|split]; simpl; now f_equal.
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

Lemma uncurry_rel_fundefs_Fcons : forall n f' t v f s m f1 s1 m1 e,
  uncurry_rel_fundefs n f s m f1 s1 m1 ->
  uncurry_rel_fundefs n (Fcons f' t v e f) s m (Fcons f' t v e f1) s1 m1.
Proof.
  induction n; intros; inv H; auto.
  eapply IHn in H2.
  econstructor; eauto.
Qed.

Lemma uncurry_rel_case : forall n v l s m e s1 m1,
  uncurry_rel n (Ecase v l) s m e s1 m1 -> exists l', e = Ecase v l'.
Proof.
  induction n; intros.
  - inv H; eauto.
  - inv H; inv H1; now apply IHn in H2.
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
  uncurry_step_induction_mut P Q IHstep IH; subst P; subst Q; simpl in *; intros; try solve
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
