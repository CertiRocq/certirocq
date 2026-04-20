(* Evaluation contexts of the LambdaANF CPS language
 * Part of the CertiRocq project
 *)

From Stdlib Require Import Arith.Arith NArith.BinNat Lists.List micromega.Lia.
Require Import LambdaANF.tactics.
From CertiRocq.Common Require Import AstCommon.
From CertiRocq.LambdaANF Require Import term set_util.
Require Import ExtLib.Structures.Monad.

Import MonadNotation.
Import ListNotations.

(** Expression evaluation contexts *)
Inductive exp_ctx : Type :=
| Hole_c : exp_ctx
| Econstr_c : var -> ctor_tag -> list var -> exp_ctx -> exp_ctx
| Eproj_c  : var -> ctor_tag -> N -> var -> exp_ctx -> exp_ctx
| Eprim_val_c : var -> primitive_value -> exp_ctx -> exp_ctx
| Eprim_c : var -> prim -> list var -> exp_ctx -> exp_ctx
| Eletapp_c : var -> var -> fun_tag -> list var -> exp_ctx -> exp_ctx
| Ecase_c : var -> list (ctor_tag * exp) -> ctor_tag ->
            exp_ctx -> list (ctor_tag * exp) -> exp_ctx
| Efun1_c : fundefs -> exp_ctx -> exp_ctx
| Efun2_c : fundefs_ctx -> exp -> exp_ctx
with fundefs_ctx :=
     | Fcons1_c:  var -> ctor_tag -> list var -> exp_ctx -> fundefs -> fundefs_ctx
     | Fcons2_c:  var -> ctor_tag -> list var -> exp -> fundefs_ctx -> fundefs_ctx.

(** Evaluation context application - Relational definition *)
Inductive app_ctx: exp_ctx -> exp -> exp -> Prop :=
| Hole_ac: forall e, app_ctx Hole_c e e
| Constr_ac : forall x t c ys e ce,
                app_ctx c e ce ->
                app_ctx (Econstr_c x t ys c) e (Econstr x t ys ce)
| Proj_ac : forall x t n y e c ce,
              app_ctx c e ce ->
              app_ctx (Eproj_c x t n y c) e (Eproj x t n y ce)
| Letapp_ac : forall x f ft ys e c ce,
    app_ctx c e ce ->
    app_ctx (Eletapp_c x f ft ys c) e (Eletapp x f ft ys ce)
| Case_ac : forall x te t e te' c ce,
              app_ctx c e ce ->
              app_ctx (Ecase_c x te t c te') e
                      (Ecase x (te ++ (t, ce) :: te'))
| Prim_val_ac : forall x p e c ce,
              app_ctx c e ce ->
              app_ctx (Eprim_val_c x p c) e (Eprim_val x p ce)
| Prim_ac : forall x f ys e c ce,
              app_ctx c e ce ->
              app_ctx (Eprim_c x f ys c) e (Eprim x f ys ce)
| Fun1_ac : forall c e ce fds,
              app_ctx c e ce ->
              app_ctx (Efun1_c fds c) e (Efun fds ce)
| Fun2_ac : forall e cfds cfdse e',
              app_f_ctx cfds e cfdse ->
              app_ctx (Efun2_c cfds e') e (Efun cfdse e')
with app_f_ctx : fundefs_ctx -> exp -> fundefs -> Prop :=
     | Fcons1_ac : forall c e ce f t ys fds,
                     app_ctx c e ce ->
                     app_f_ctx (Fcons1_c f t ys c fds) e (Fcons f t ys ce fds)
     | Fcons2_ac: forall e cfdse f cfds ys e' t,
                    app_f_ctx cfds e cfdse ->
                    app_f_ctx (Fcons2_c f t ys e' cfds) e (Fcons f t ys e' cfdse).

#[global] Hint Constructors app_ctx app_f_ctx : core.

(** Evaluation context application - Computational definition *)
Fixpoint app_ctx_f (c:exp_ctx) (e:exp) : exp :=
  match c with
    | Hole_c => e
    | Econstr_c x t ys c => Econstr x t ys (app_ctx_f c e)
    | Eproj_c x t n y c => Eproj x t n y (app_ctx_f c e)
    | Eletapp_c x f ft ys c => Eletapp x f ft ys (app_ctx_f c e)
    | Ecase_c x te t c te' =>
      Ecase x (te ++ (t, app_ctx_f c e) :: te')
    | Eprim_val_c x p c => Eprim_val x p (app_ctx_f c e)
    | Eprim_c x f ys c => Eprim x f ys (app_ctx_f c e)
    | Efun1_c fds c => Efun fds (app_ctx_f c e)
    | Efun2_c cfds e' => Efun (app_f_ctx_f cfds e) e'
  end
with app_f_ctx_f (c: fundefs_ctx) (e:exp) : fundefs :=
       match c with
         | Fcons1_c f t ys c fds => Fcons f t ys (app_ctx_f c e) fds
         | Fcons2_c f t ys e' cfds => Fcons f t ys e' (app_f_ctx_f cfds e)
       end.

(** Composition of evaluation context - Relational definition *)
Inductive  comp_ctx: exp_ctx -> exp_ctx -> exp_ctx -> Prop :=
| Hole_cc: forall e, comp_ctx Hole_c e e
| Constr_cc : forall x t c ys e ce,
                comp_ctx c e ce ->
                comp_ctx (Econstr_c x t ys c) e (Econstr_c x t ys ce)
| Proj_cc : forall x t n y e c ce,
              comp_ctx c e ce ->
              comp_ctx (Eproj_c x t n y c) e (Eproj_c x t n y ce)
| Letapp_cc : forall x f ft ys e c ce,
              comp_ctx c e ce ->
              comp_ctx (Eletapp_c x f ft ys c) e (Eletapp_c x f ft ys ce)
| Case_cc : forall x te t c te' c' cc,
              comp_ctx c c' cc ->
              comp_ctx (Ecase_c x te t c te') c' (Ecase_c x te t cc te')
| Prim_val_cc : forall x p e c ce,
              comp_ctx c e ce ->
              comp_ctx (Eprim_val_c x p c) e (Eprim_val_c x p ce)
| Prim_cc : forall x f ys e c ce,
              comp_ctx c e ce ->
              comp_ctx (Eprim_c x f ys c) e (Eprim_c x f ys ce)
| Fun1_cc : forall c e ce fds,
              comp_ctx c e ce ->
              comp_ctx (Efun1_c fds c) e (Efun1_c fds ce)
| Fun2_cc : forall e cfds cfdse e',
              comp_f_ctx cfds e cfdse ->
              comp_ctx (Efun2_c cfds e') e (Efun2_c cfdse e')
with comp_f_ctx : fundefs_ctx -> exp_ctx -> fundefs_ctx -> Prop :=
     | Fcons1_cc :
         forall c e ce f t ys fds,
           comp_ctx c e ce ->
           comp_f_ctx (Fcons1_c f t ys c fds) e (Fcons1_c f t ys ce fds)
     | Fcons2_cc:
         forall e cfdse f cfds ys e' t,
           comp_f_ctx cfds e cfdse ->
           comp_f_ctx (Fcons2_c f t ys e' cfds) e (Fcons2_c f t ys e' cfdse).

(** Composition of evaluation context - Computational definition *)
Fixpoint comp_ctx_f (c1:exp_ctx) (c2:exp_ctx) : exp_ctx :=
  match c1 with
    | Hole_c => c2
    | Econstr_c x t ys c => Econstr_c x t ys (comp_ctx_f c c2)
    | Eproj_c x t n y c => Eproj_c x t n y (comp_ctx_f c c2)
    | Ecase_c x te t c te' => Ecase_c x te t (comp_ctx_f c c2) te'
    | Eletapp_c x f ft ys c => Eletapp_c x f ft ys (comp_ctx_f c c2)
    | Eprim_val_c x p c => Eprim_val_c x p (comp_ctx_f c c2)
    | Eprim_c x f ys c => Eprim_c x f ys (comp_ctx_f c c2)
    | Efun1_c fds c => Efun1_c fds (comp_ctx_f c c2)
    | Efun2_c cfds e' => Efun2_c (comp_f_ctx_f cfds c2) e'
  end
with comp_f_ctx_f (c: fundefs_ctx) (c2:exp_ctx) : fundefs_ctx :=
       match c with
         | Fcons1_c f t ys c fds =>
           Fcons1_c f t ys (comp_ctx_f c c2) fds
         | Fcons2_c f t ys e' cfds =>
           Fcons2_c f t ys e' (comp_f_ctx_f cfds c2)
       end.

Declare Scope ctx_scope.

Notation "c '|[' e ']|' " := (app_ctx_f c e)  (at level 28, no associativity)
                             : ctx_scope.
Notation "f '<[' e ']>'" := (app_f_ctx_f f e)  (at level 28, no associativity)
                            : ctx_scope.
Open Scope ctx_scope.

Scheme ctx_exp_mut := Induction for exp_ctx Sort Prop
with ctx_fundefs_mut := Induction for fundefs_ctx Sort Prop.

Scheme ctx_exp_mut' := Induction for exp_ctx Sort Type
with ctx_fundefs_mut' := Induction for fundefs_ctx Sort Type.

Lemma exp_fundefs_ctx_mutual_ind :
  forall (P : exp_ctx -> Prop) (P0 : fundefs_ctx -> Prop),
    P Hole_c ->
    (forall (v : var) (t : ctor_tag) (l : list var) (e : exp_ctx),
       P e -> P (Econstr_c v t l e)) ->
    (forall (v : var) (t : ctor_tag) (n : N) (v0 : var) (e : exp_ctx),
        P e -> P (Eproj_c v t n v0 e)) ->
    (forall (v : var) (f : var) (ft : fun_tag) (ys : list var) (e : exp_ctx),
        P e -> P (Eletapp_c v f ft ys e)) ->
    (forall (v : var) p e,
        P e -> P (Eprim_val_c v p e)) ->
    (forall (v : var) (p : prim) (l : list var) (e : exp_ctx),
       P e -> P (Eprim_c v p l e)) ->
    (forall (v : var) (l : list (ctor_tag * exp)) (t : ctor_tag) (e : exp_ctx),
       P e -> forall l0 : list (ctor_tag * exp), P (Ecase_c v l t e l0)) ->
    (forall (f4 : fundefs) (e : exp_ctx), P e -> P (Efun1_c f4 e)) ->
    (forall f5 : fundefs_ctx, P0 f5 -> forall e : exp, P (Efun2_c f5 e)) ->
    (forall (v : var) (t : fun_tag) (l : list var) (e : exp_ctx),
       P e -> forall f6 : fundefs, P0 (Fcons1_c v t l e f6)) ->
    (forall (v : var) (t : fun_tag) (l : list var)
            (e : exp) (f7 : fundefs_ctx), P0 f7 -> P0 (Fcons2_c v t l e f7)) ->
    (forall e : exp_ctx, P e) /\ (forall f : fundefs_ctx, P0 f).
Proof.
  intros. split.
  apply (ctx_exp_mut P P0); assumption.
  apply (ctx_fundefs_mut P P0); assumption.
Qed.


(** Name the induction hypotheses only *)
Ltac exp_fundefs_ctx_induction IH1 IH2 :=
  apply exp_fundefs_ctx_mutual_ind;
  [ | intros ? ? ? ? IH1
    | intros ? ? ? ? ? IH1
    | intros ? ? ? ? ? IH1
    | intros ? ? ? IH1
    | intros ? ? ? ? IH1
    | intros ? ? ? ? IH1
    | intros ? ? IH1
    | intros ? IH2 ?
    | intros ? ? ? ? IH1 ?
    | intros ? ? ? ? ? IH2 ].

(** Alternative definition of subterm relation *)
Definition subterm_e' (e':exp) (e:exp): Prop :=
  exists c, Hole_c <> c /\ app_ctx c e' e.

Definition subterm_or_eq' (e':exp) (e:exp) : Prop :=
  exists c, app_ctx c e' e.

(** Theorems about context application and composition *)
Lemma app_ctx_f_correct_mut:
  (forall c e e',
     c |[ e ]|  = e' <-> app_ctx c e e') /\
  (forall cf B B',
     cf <[ B ]> = B' <-> app_f_ctx cf B B').
Proof.
  exp_fundefs_ctx_induction IHe IHf; simpl; intros; split; intros H';
  first
    [ inversion H'; subst; constructor;
      eapply IHe; congruence
    | inversion H'; subst; repeat f_equal; eapply IHe;
      eassumption
    | inversion H'; subst; constructor;
      eapply IHf; congruence
    | inversion H'; subst; repeat f_equal; eapply IHf ];
  inversion H'; subst; eassumption.
Qed.

Corollary app_ctx_f_correct :
  forall c e e',
    c |[ e ]|  = e' <-> app_ctx c e e'.
Proof.
  now apply app_ctx_f_correct_mut.
Qed.

Corollary app_f_ctx_f_correct :
  forall cf B B',
    cf <[ B ]> = B' <-> app_f_ctx cf B B'.
Proof.
  now apply app_ctx_f_correct_mut.
Qed.

Lemma comp_ctx_f_correct_mut:
  (forall c c' cc',
     comp_ctx_f c c'  = cc' <-> comp_ctx c c' cc') /\
  (forall cf cf' ccf',
     comp_f_ctx_f cf cf' = ccf' <-> comp_f_ctx cf cf' ccf').
Proof.
  exp_fundefs_ctx_induction IHe IHf; simpl; intros; split; intros H';
  first
    [ inversion H'; subst; constructor;
      eapply IHe; congruence
    | inversion H'; subst; repeat f_equal; eapply IHe;
      eassumption
    | inversion H'; subst; constructor;
      eapply IHf; congruence
    | inversion H'; subst; repeat f_equal; eapply IHf ];
  inversion H'; subst; eassumption.
Qed.

Corollary comp_ctx_f_correct :
  forall c c' cc',
    comp_ctx_f c c'  = cc' <-> comp_ctx c c' cc'.
Proof.
  now apply comp_ctx_f_correct_mut.
Qed.

Corollary comp_f_ctx_f_correct :
  forall cf cf' ccf',
   comp_f_ctx_f cf cf' = ccf' <-> comp_f_ctx cf cf' ccf'.
Proof.
  now apply comp_ctx_f_correct_mut.
Qed.

Lemma app_ctx_f_fuse_mut :
  (forall c c' e,
     c |[ c' |[ e ]| ]| = (comp_ctx_f c c') |[ e ]|) /\
  (forall cf c e,
     cf <[ c |[ e ]| ]> = (comp_f_ctx_f cf c) <[ e ]>).
Proof.
  exp_fundefs_ctx_induction IHe IHf; simpl; intros;
  try (rewrite IHe; reflexivity); try (rewrite IHf; reflexivity).
  reflexivity.
Qed.

Corollary app_ctx_f_fuse :
  forall c c' e,
    c |[ c' |[ e ]| ]| = (comp_ctx_f c c') |[ e ]|.
Proof.
  now apply app_ctx_f_fuse_mut.
Qed.

Corollary app_f_ctx_f_fuse :
  forall cf c e,
    cf <[ c |[ e ]| ]> = (comp_f_ctx_f cf c) <[ e ]>.
Proof.
  now apply app_ctx_f_fuse_mut.
Qed.

Lemma app_ctx_fuse:
  forall (c c' : exp_ctx) (e1 e2 e3 : exp),
    app_ctx c e1 e2 ->
    app_ctx c' e2 e3 ->
    app_ctx (comp_ctx_f c' c) e1 e3.
Proof.
  intros c c' e1 e2 e3 H1 H2. rewrite <- app_ctx_f_correct.
  rewrite <- app_ctx_f_fuse.
  rewrite <- app_ctx_f_correct in H1, H2. rewrite H1. eauto.
Qed.

Lemma comp_ctx_f_assoc_mut:
  (forall c1 c2 c3,
     comp_ctx_f (comp_ctx_f c1 c2) c3 = comp_ctx_f c1 (comp_ctx_f c2 c3)) /\
  (forall f c2 c3, comp_f_ctx_f (comp_f_ctx_f f c2) c3 =
              comp_f_ctx_f f (comp_ctx_f c2 c3)).
Proof.
  exp_fundefs_ctx_induction IHc1 IHf; intros; simpl; auto; try (rewrite IHc1; auto).
  - rewrite IHf; auto.
  - rewrite IHf; auto.
Qed.

Theorem comp_ctx_f_assoc:
  (forall c1 c2 c3,
     comp_ctx_f (comp_ctx_f c1 c2) c3 = comp_ctx_f c1 (comp_ctx_f c2 c3)).
Proof.
  intros; apply comp_ctx_f_assoc_mut; auto.
Qed.

Theorem comp_f_ctx_f_assoc:
  (forall f c2 c3, comp_f_ctx_f (comp_f_ctx_f f c2) c3 =
              comp_f_ctx_f f (comp_ctx_f c2 c3)).
Proof.
  intros; apply comp_ctx_f_assoc_mut; auto.
Qed.

Theorem comp_ctx_split_mut:
  (forall c1 c2 c3 c4,
     comp_ctx_f c1 c2 = comp_ctx_f c3 c4 ->
     (exists c41 c42, c4 = comp_ctx_f c41 c42 /\ c1 = comp_ctx_f c3 c41 /\ c2 = c42) \/
     (exists c31 c32, c3 = comp_ctx_f c31 c32 /\ c1 = c31 /\ c2 = comp_ctx_f c32 c4)) /\
  (forall f1 c2 f3 c4, comp_f_ctx_f f1 c2 = comp_f_ctx_f f3 c4 ->
                  (exists c41 c42, c4 = comp_ctx_f c41 c42 /\ f1 = comp_f_ctx_f f3 c41 /\ c2 = c42) \/
                  (exists f31 c32, f3 = comp_f_ctx_f f31 c32 /\ f1 = f31 /\ c2 = comp_ctx_f c32 c4)).
Proof.
  exp_fundefs_ctx_induction IHc1 IHf; intros.
  - simpl in H.
    right.
    exists Hole_c, c3.
    auto.
  - simpl in H. destruct c3; inv H.
    + simpl in H0.
      left.
      destruct c4; inv H0.
      exists ( Econstr_c v0 c l0 e), c2.
      auto.
    + apply IHc1 in H4. destruct H4.
      * left.
        destructAll.
        exists x, x0.
        auto.
      * right. destructAll.
        exists (Econstr_c v0 c l0 x), x0.
        auto.
  - simpl in H. destruct c3; inv H.
    + simpl in H0.
      left.
      destruct c4; inv H0.
      exists ( Eproj_c v1 c n0 v2 e ),  c2; auto.
    + apply IHc1 in H5. destruct H5.
      * left.
        destructAll.
        exists x, x0.
        auto.
      * right. destructAll.
        exists ( Eproj_c v1 c n0 v2 x), x0;
          auto.
  - simpl in H. destruct c3; inv H.
    + simpl in H0.
      left.
      destruct c4; inv H0.
      exists (Eletapp_c v0 v1 f0 l e ),  c2; auto.
    + apply IHc1 in H5. destruct H5.
      * left.
        destructAll.
        exists x, x0.
        auto.
      * right. destructAll.
        exists (Eletapp_c v0 v1 f0 l x), x0;
          auto.
  - simpl in H. destruct c3; inv H.
    + simpl in H0.
      left.
      destruct c4; inv H0.
      exists ( Eprim_val_c v0 p0 e ),  c2; auto.
    + apply IHc1 in H3. destruct H3.
      * left.
        destructAll.
        exists x, x0.
        auto.
      * right. destructAll.
        exists (Eprim_val_c v0 p0 x ), x0;
          auto.
  - simpl in H. destruct c3; inv H.
    + simpl in H0.
      left.
      destruct c4; inv H0.
      exists ( Eprim_c v0 p0 l0 e ),  c2; auto.
    + apply IHc1 in H4. destruct H4.
      * left.
        destructAll.
        exists x, x0.
        auto.
      * right. destructAll.
        exists (Eprim_c v0 p0 l0 x ), x0;
          auto.
  - simpl in H. destruct c3; inv H.
    + simpl in H0. left.
      exists (Ecase_c v l t e l0), c2.
      auto.
    + apply IHc1 in H4.
      destruct H4; destructAll.
      * left.
        exists x, x0; auto.
      * right.
        exists (Ecase_c v0 l1 c x l2), x0.
        auto.
  - simpl in H.
    destruct c3; inv H.
    + simpl in H0.
      left.
      exists (Efun1_c f4 e), c2.
      auto.
    + apply IHc1 in H2.
      destruct H2; destructAll.
      * left.
        exists x, x0; auto.
      * right.
        exists (Efun1_c f x), x0.
        auto.
  - simpl in H.
    destruct c3; inv H.
    + simpl in H0.
      left.
      exists (Efun2_c f5 e), c2.
      auto.
    + apply IHf in H1.
      destruct H1.
      * left.
        destructAll.
        simpl. exists x, x0.
        auto.
      * right.
        destructAll.
        exists ( Efun2_c x e0), x0.
        auto.
  - destruct f3; inv H.
    apply IHc1 in H4.
    destruct H4; destructAll.
    * left.
      simpl.
      exists x, x0.
      auto.
    * right.
      exists (Fcons1_c v0 c l0 x f), x0; auto.
  - simpl in H.
    destruct f3; inv H.
    apply IHf in H5.
    destruct H5.
    * left.
      destructAll.
      simpl. exists x, x0.
      auto.
    * right.
      destructAll.
      exists (Fcons2_c v0 c l0 e0 x), x0.
      auto.
Qed.

Theorem comp_ctx_split:
  (forall c1 c2 c3 c4,
     comp_ctx_f c1 c2 = comp_ctx_f c3 c4 ->
     (exists c41 c42, c4 = comp_ctx_f c41 c42 /\ c1 = comp_ctx_f c3 c41 /\ c2 = c42) \/
     (exists c31 c32, c3 = comp_ctx_f c31 c32 /\ c1 = c31 /\ c2 = comp_ctx_f c32 c4)).
Proof.
  apply comp_ctx_split_mut; auto.
Qed.

Theorem comp_f_ctx_split:
  (forall f1 c2 f3 c4, comp_f_ctx_f f1 c2 = comp_f_ctx_f f3 c4 ->
                  (exists c41 c42, c4 = comp_ctx_f c41 c42 /\ f1 = comp_f_ctx_f f3 c41 /\ c2 = c42) \/
                  (exists f31 c32, f3 = comp_f_ctx_f f31 c32 /\ f1 = f31 /\ c2 = comp_ctx_f c32 c4)).
Proof.
  apply comp_ctx_split_mut; auto.
Qed.

(* prefix a fundefs ctx with a fundefs *)
Fixpoint app_fundefs_ctx (f:fundefs) (fc:fundefs_ctx): fundefs_ctx:=
  match f with
    | Fnil => fc
    | Fcons x t xs e f' =>
      Fcons2_c x t xs e (app_fundefs_ctx f' fc)
  end.

Lemma comp_ctx_f_Hole_c C :
  comp_ctx_f C Hole_c = C
with comp_f_ctx_f_Hole_c f :
       comp_f_ctx_f f Hole_c = f.
Proof.
  - destruct C; simpl; eauto;
      try (rewrite comp_ctx_f_Hole_c; reflexivity).
    rewrite comp_f_ctx_f_Hole_c. reflexivity.
  - destruct f; simpl; eauto.
    rewrite comp_ctx_f_Hole_c; reflexivity.
    rewrite comp_f_ctx_f_Hole_c. reflexivity.
Qed.
