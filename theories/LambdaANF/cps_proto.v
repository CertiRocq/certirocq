(* The stack-of-frames one-hole contexts, with the right indices, are isomorphic to
   [term.exp_ctx] and [term.fundefs_ctx] *)

From Stdlib Require Import ZArith.ZArith Lists.List Sets.Ensembles Strings.String.
From Stdlib Require Import Lia.
Import ListNotations.
From CertiRocq.Common Require AstCommon.
From CertiRocq.LambdaANF Require Import
     Prototype term term_util ctx
     identifiers Ensembles_util.

From MetaRocq Require Import Template.All.

From CertiRocq.LambdaANF Require Import PrototypeGenFrame term cps_proto_univ.

(* Print exp_univ. *)
(* Print exp_univD. *)

Global Instance Frame_exp : Frame exp_univ := exp_Frame_ops.
Global Instance AuxData_exp : AuxData exp_univ := exp_aux_data.

(* Print exp_frame_t. *)
(* Print exp_frameD. *)
(* Print exp_Frame_ops. *)

Open Scope list_scope.

(* The type of one-hole contexts *)
Definition exp_c : exp_univ -> exp_univ -> Set := frames_t.

(* term.exp_ctx -> exp_c _ _ *)

Definition c_of_ces (ces : list (term.ctor_tag * term.exp)) :
  exp_c exp_univ_list_prod_ctor_tag_exp exp_univ_list_prod_ctor_tag_exp :=
  fold_right
    (fun '(c, e) frames =>
      <[cons_prod_ctor_tag_exp1 (c, e)]> >++ frames)
    <[]>
    ces.

Definition c_of_ces_ctx' c_of_exp_ctx (ces1 : list (term.ctor_tag * term.exp)) (c : term.ctor_tag)
           (C : exp_ctx) (ces2 : list (term.ctor_tag * term.exp))
  : exp_c exp_univ_exp exp_univ_list_prod_ctor_tag_exp :=
  c_of_ces ces1
    >++ <[cons_prod_ctor_tag_exp0 ces2; pair_ctor_tag_exp1 c]>
    >++ c_of_exp_ctx C.

Fixpoint c_of_exp_ctx (C : exp_ctx) : exp_c exp_univ_exp exp_univ_exp
with c_of_fundefs_ctx (C : fundefs_ctx) : exp_c exp_univ_exp exp_univ_fundefs.
Proof.
  - refine (
      match C with
      | Hole_c => <[]>
      | Econstr_c x c ys C => <[Econstr3 x c ys]> >++ c_of_exp_ctx C
      | Eproj_c x c n y C => <[Eproj4 x c n y]> >++ c_of_exp_ctx C
      | Eprim_val_c x p C => <[Eprim_val2 x p]> >++ c_of_exp_ctx C
      | Eprim_c x p ys C => <[Eprim3 x p ys]> >++ c_of_exp_ctx C
      | Eletapp_c x f ft ys C => <[Eletapp4 x f ft ys]> >++ c_of_exp_ctx C
      | Ecase_c x ces1 c C ces2 => <[Ecase1 x]> >++ c_of_ces_ctx' c_of_exp_ctx ces1 c C ces2
      | Efun1_c fds C => <[Efun1 fds]> >++ c_of_exp_ctx C
      | Efun2_c C e => <[Efun0 e]> >++ c_of_fundefs_ctx C
      end).
  - refine (
      match C with
      | Fcons1_c f ft xs C fds => <[Fcons3 f ft xs fds]> >++ c_of_exp_ctx C
      | Fcons2_c f ft xs e C => <[Fcons4 f ft xs e]> >++ c_of_fundefs_ctx C
      end).
Defined.

Definition c_of_ces_ctx := c_of_ces_ctx' c_of_exp_ctx.

(* exp_c _ _ -> term.exp_ctx: directly writing a recursive function on exp_c is annoying because
   of the indices. Instead map each frame to a "slice" of an exp_ctx represented as a function
   ctx |-> slice + ctx. Then all the functions can be composed together and initialized with
   the empty context. *)

Definition univ_rep (A : exp_univ) : Set :=
  match A with
  | exp_univ_prod_ctor_tag_exp => term.ctor_tag * exp_ctx
  | exp_univ_list_prod_ctor_tag_exp =>
    list (term.ctor_tag * term.exp) * term.ctor_tag * exp_ctx * list (term.ctor_tag * term.exp)
  | exp_univ_fundefs => fundefs_ctx
  | exp_univ_exp => exp_ctx
  | exp_univ_var => False
  | exp_univ_fun_tag => False
  | exp_univ_ctor_tag => False
  | exp_univ_prim => False
  | exp_univ_N => False
  | exp_univ_list_var => False
  | exp_univ_primitive_value => False
  end.

Definition exp_frame_rep {A B} (f : exp_frame_t A B) : univ_rep A -> univ_rep B.
Proof.
  destruct f eqn:Hf; cbn;
  try lazymatch goal with |- False -> _ => inversion 1 end.
  - exact (fun ctx => (c, ctx)).
  - exact (fun '(c, e) => ([], c, e, l)).
  - exact (fun '(ces1, c, e, ces2) => (p :: ces1, c, e, ces2)).
  - exact (fun ctx => Fcons1_c v f0 l ctx f1).
  - exact (fun ctx => Fcons2_c v f0 l e ctx).
  - exact (fun ctx => Econstr_c v c l ctx).
  - exact (fun '(ces1, c, e, ces2) => Ecase_c v ces1 c e ces2).
  - exact (fun ctx => Eproj_c v c n v0 ctx).
  - exact (fun ctx => Eletapp_c v v0 f0 l ctx).
  - exact (fun ctx => Efun2_c ctx e).
  - exact (fun ctx => Efun1_c f0 ctx).
  - exact (fun ctx => Eprim_val_c v p ctx).
  - exact (fun ctx => Eprim_c v p l ctx).
Defined.

Fixpoint exp_c_rep {A B} (C : exp_c A B) : univ_rep A -> univ_rep B :=
  match C with
  | <[]> => fun x => x
  | C >:: f => fun x => exp_c_rep C (exp_frame_rep f x)
  end.

Definition exp_ctx_of_c (C : exp_c exp_univ_exp exp_univ_exp) : exp_ctx :=
  exp_c_rep C Hole_c.

Definition fundefs_ctx_of_c (C : exp_c exp_univ_exp exp_univ_fundefs) : fundefs_ctx :=
  exp_c_rep C Hole_c.

Lemma exp_c_rep_compose {A B C} (fs : exp_c A B) (gs : exp_c B C) x :
  exp_c_rep (gs >++ fs) x = exp_c_rep gs (exp_c_rep fs x).
Proof. induction fs as [ |A' AB B' f fs IHfs]; [reflexivity|cbn; now rewrite IHfs]. Qed.

(* exp_ctx -> exp_c -> exp_ctx *)

Lemma fold_right_cons {A B} (f : A -> B -> B) z x xs :
  fold_right f z (x :: xs) = f x (fold_right f z xs).
Proof. reflexivity. Qed.

Lemma ces_ctx_c_ces_ctx : forall ces ces1 c C ces2,
  exp_c_rep (c_of_ces ces) (ces1, c, C, ces2) = (ces ++ ces1, c, C, ces2).
Proof.
  clear; induction ces as [| [c e] ces IHces]; [reflexivity|]; intros ces1 ctr C ces2.
  unfold c_of_ces; rewrite fold_right_cons, exp_c_rep_compose.
  now rewrite IHces.
Qed.

Fixpoint exp_ctx_c_exp_ctx (C : exp_ctx) : exp_ctx_of_c (c_of_exp_ctx C) = C
with fundefs_ctx_c_fundefs_ctx (C : fundefs_ctx) : fundefs_ctx_of_c (c_of_fundefs_ctx C) = C.
Proof.
  all: unfold exp_ctx_of_c, fundefs_ctx_of_c in *;
    destruct C; simpl;
    try reflexivity;
    rewrite ?exp_c_rep_compose;
    try solve [(rewrite exp_ctx_c_exp_ctx + rewrite fundefs_ctx_c_fundefs_ctx); reflexivity].
  unfold c_of_ces_ctx'.
  rewrite !exp_c_rep_compose; cbn.
  now rewrite ces_ctx_c_ces_ctx, app_nil_r, exp_ctx_c_exp_ctx.
Qed.

(* exp_c -> exp_ctx -> exp_c: because exp_c is 'inside-out', destructing normally
   on (C : exp_c _ _) yields subcases like
     c_of_foo (foo_of_c (C >:: f)) = C
     <=> c_of_foo (exp_c_rep C (exp_frame_rep f Hole_c)) = C
   which isn't helpful because c_of_foo is stuck: exp_c_rep won't spit out a constructor
   until its consumed the rest of C.

   Fix: split C into <[]> and <[g]> >++ gs cases and use exp_c_rep_compose:
     c_of_foo (foo_of_c (<[f]> >++ C)) = C
     <=> c_of_foo (exp_c_rep (<[f]> >++ C Hole_c)) = C
     <=> c_of_foo (exp_c_rep <[f]> (exp_c_rep C Hole_c)) = C
     <=> c_of_foo (exp_frame_rep f (exp_c_rep C Hole_c)) = C
   [exp_frame_rep f] will expose constructors for c_of_foo. *)

Definition c_ctx_c_stmt {A B} : exp_c A B -> Prop :=
  match A, B with
  | exp_univ_exp, exp_univ_exp => fun C => c_of_exp_ctx (exp_ctx_of_c C) = C
  | exp_univ_exp, exp_univ_fundefs => fun C => c_of_fundefs_ctx (fundefs_ctx_of_c C) = C
  | exp_univ_exp, exp_univ_prod_ctor_tag_exp => fun C =>
    let '(c, ctx) := exp_c_rep C Hole_c in
    <[pair_ctor_tag_exp1 c]> >++ c_of_exp_ctx ctx = C
  | exp_univ_exp, exp_univ_list_prod_ctor_tag_exp => fun C =>
    let '(ces1, c, ctx, ces2) := exp_c_rep C Hole_c in
    c_of_ces_ctx ces1 c ctx ces2 = C
  | _, _ => fun _ => True
  end.

Lemma c_ctx_c {A B} (C : exp_c A B) : c_ctx_c_stmt C.
Proof.
  induction C as [|A AB B g gs IHgs] using frames_rev_ind.
  - destruct A; try exact I; reflexivity.
  - destruct g, A; try exact I;
      cbn; unfold exp_ctx_of_c, fundefs_ctx_of_c;
      rewrite ?exp_c_rep_compose; cbn;
      try match goal with
      | |- context [match ?e with end] =>
        let H := fresh "H" in assert (H : False) by exact e; inversion H
      end;
      match goal with |- context [exp_c_rep gs Hole_c] =>
        match type of gs with
        | frames_t' _ ?hole ?root =>
          unfold c_ctx_c_stmt in IHgs;
          unfold exp_ctx_of_c, fundefs_ctx_of_c in IHgs
        end
      end;
      try solve [erewrite IHgs; eauto; rewrite frames_len_compose; simpl; lia].
    + destruct (exp_c_rep gs Hole_c) as [c e] eqn:Hce.
      unfold c_of_ces_ctx, c_of_ces_ctx'.
      now rewrite <- IHgs, frames_rev_assoc.
    + destruct (exp_c_rep gs Hole_c) as [[[ces1 c] e] ces2] eqn:Hces12.
      destruct p as [c' e']; simpl.
      unfold c_of_ces_ctx, c_of_ces_ctx' in *.
      now rewrite <- IHgs, frames_rev_assoc.
    + destruct (exp_c_rep gs Hole_c) as [[[f ft] xs] ctx] eqn:Hces12.
      simpl; unfold c_of_ces_ctx, c_of_ces_ctx' in *.
      now erewrite <- IHgs, frames_rev_assoc.
Qed.

Corollary c_exp_ctx_c (C : exp_c exp_univ_exp exp_univ_exp) :
  c_of_exp_ctx (exp_ctx_of_c C) = C.
Proof. apply (c_ctx_c C). Qed.

Corollary c_fundefs_ctx_c (C : exp_c exp_univ_exp exp_univ_fundefs) :
  c_of_fundefs_ctx (fundefs_ctx_of_c C) = C.
Proof. apply (c_ctx_c C). Qed.

Ltac normalize_roundtrips :=
  try rewrite exp_c_rep_compose; simpl;
  try rewrite c_exp_ctx_c in *;
  try rewrite c_fundefs_ctx_c in *;
  try rewrite exp_ctx_c_exp_ctx in *;
  try rewrite fundefs_ctx_c_fundefs_ctx in *.

(* ---------- package all the above together ---------- *)

Class Iso A B := {
  isoAofB : B -> A;
  isoBofA : A -> B;
  isoABA : forall x, isoAofB (isoBofA x) = x;
  isoBAB : forall x, isoBofA (isoAofB x) = x }.

Notation "'![' e ']'" := (isoBofA e).
Notation "'[' e ']!'" := (isoAofB e).

#[global] Instance Iso_exp_c_exp_ctx : Iso (exp_c exp_univ_exp exp_univ_exp) exp_ctx := {
  isoAofB := c_of_exp_ctx;
  isoBofA := exp_ctx_of_c;
  isoABA := c_exp_ctx_c;
  isoBAB := exp_ctx_c_exp_ctx }.

#[global] Instance Iso_fundefs_c_fundefs_ctx : Iso (exp_c exp_univ_exp exp_univ_fundefs) fundefs_ctx := {
  isoAofB := c_of_fundefs_ctx;
  isoBofA := fundefs_ctx_of_c;
  isoABA := c_fundefs_ctx_c;
  isoBAB := fundefs_ctx_c_fundefs_ctx }.

Lemma iso_proof {A B} `{Iso A B} (P : A -> Prop) (Hxy : forall y, P [y]!) : forall x, P x.
Proof.
  intros x; specialize (Hxy ![x]).
  now rewrite isoABA in Hxy.
Qed.

Ltac iso x := pattern x; revert x; apply iso_proof; intros x.

Lemma iso_BofA_inj {A B} `{Iso A B} x y : ![x] = ![y] -> x = y.
Proof.
  intros Heq; apply f_equal with (f := fun x => [x]!) in Heq.
  now repeat rewrite isoABA in Heq.
Qed.

Lemma iso_AofB_inj {A B} `{Iso A B} x y : [x]! = [y]! -> x = y.
Proof.
  intros Heq; apply f_equal with (f := fun x => ![x]) in Heq.
  now repeat rewrite isoBAB in Heq.
Qed.

(* ---------- exp_c application agrees with app_ctx_f + app_f_ctx_f ---------- *)

Notation "C '⟦+' x '+⟧'" := (framesD C x) (at level 15).

Fixpoint app_exp_ctx_eq (C : exp_ctx) e {struct C} :
  C |[ e ]| = ([C]! : exp_c exp_univ_exp exp_univ_exp) ⟦+ e +⟧
with app_fundefs_ctx_eq (C : fundefs_ctx) e {struct C} :
  app_f_ctx_f C e = ([C]! : exp_c exp_univ_exp exp_univ_fundefs) ⟦+ e +⟧.
Proof.
  all: destruct C; simpl;
    try lazymatch goal with
    | |- context [(?fs >++ ?gs) ⟦+ _ +⟧] =>
      rewrite (@frames_compose_law exp_univ Frame_exp _ _ _ fs gs)
    end; simpl; normalize_roundtrips; try reflexivity;
    try solve [(rewrite <- app_exp_ctx_eq + rewrite <- app_fundefs_ctx_eq); reflexivity].
  - f_equal.
    unfold c_of_ces_ctx'.
    repeat rewrite frames_compose_law.
    rewrite <- app_exp_ctx_eq.
    simpl.
    assert (Harms : forall ces1 ces2, c_of_ces ces1 ⟦+ ces2 +⟧ = ces1 ++ ces2). {
      clear; induction ces1 as [| [c e] ces1 IHces]; intros ces2; [reflexivity|].
      unfold c_of_ces; now rewrite fold_right_cons, frames_compose_law, IHces. }
    now rewrite Harms.
Qed.

Local Ltac mk_corollary parent :=
  apply iso_BofA_inj; simpl; repeat normalize_roundtrips;
  symmetry; apply parent.

Corollary app_exp_c_eq (C : exp_c exp_univ_exp exp_univ_exp) :
  forall e, C ⟦+ e +⟧ = ![C] |[ e ]|.
Proof. iso C; intros e; now rewrite app_exp_ctx_eq, isoABA. Qed.

Corollary app_f_exp_c_eq (C : exp_c exp_univ_exp exp_univ_fundefs) :
  forall e, C ⟦+ e +⟧ = app_f_ctx_f ![C] e.
Proof. iso C; intros e. now rewrite app_fundefs_ctx_eq, isoABA. Qed.

(* ---------- exp_c composition agrees with comp_ctx_f + comp_f_ctx_f ---------- *)

Local Ltac fold_exp_c_reps :=
  lazymatch goal with
  | |- context [exp_c_rep ?C Hole_c] =>
    lazymatch type of C with
    | exp_c exp_univ_exp exp_univ_exp => change (exp_c_rep C Hole_c) with (exp_ctx_of_c C)
    end
  | H : context [exp_c_rep ?C Hole_c] |- _ =>
    lazymatch type of C with
    | exp_c exp_univ_exp exp_univ_exp => change (exp_c_rep C Hole_c) with (exp_ctx_of_c C) in H
    end
  end.

Fixpoint comp_exp_ctx_eq C D {struct C} : comp_ctx_f C D = ![[C]! >++ [D]!]
with comp_fundefs_ctx_eq C D {struct C} : comp_f_ctx_f C D = ![[C]! >++ [D]!].
Proof.
  all: simpl in *; destruct C; simpl; unfold exp_ctx_of_c, fundefs_ctx_of_c;
    repeat rewrite exp_c_rep_compose; simpl;
    fold_exp_c_reps; normalize_roundtrips; f_equal; try solve
    [reflexivity
    |match goal with
      | |- _ ?C ?D = _ =>
        let use_IH IH1 IH2 :=
          specialize (IH1 C D); clear IH2;
          unfold exp_ctx_of_c, fundefs_ctx_of_c in IH1;
          rewrite exp_c_rep_compose in IH1
        in
        use_IH comp_exp_ctx_eq comp_fundefs_ctx_eq + use_IH comp_fundefs_ctx_eq comp_exp_ctx_eq
     end; unfold exp_ctx_of_c in *;
     fold_exp_c_reps; normalize_roundtrips; assumption].
  unfold c_of_ces_ctx'.
  repeat rewrite exp_c_rep_compose; simpl.
  rewrite ces_ctx_c_ces_ctx, app_nil_r; normalize_roundtrips; f_equal.
  specialize (comp_exp_ctx_eq C D); unfold exp_ctx_of_c in comp_exp_ctx_eq.
  rewrite exp_c_rep_compose in comp_exp_ctx_eq; fold_exp_c_reps; now normalize_roundtrips.
Qed.

Corollary comp_exp_c_eq C D : C >++ D = [comp_ctx_f ![C] ![D]]!.
Proof. revert D; iso C; intros D; iso D; mk_corollary comp_exp_ctx_eq. Qed.

Corollary comp_fundefs_c_eq C D : C >++ D = [comp_f_ctx_f ![C] ![D]]!.
Proof. revert D; iso C; intros D; iso D; mk_corollary comp_fundefs_ctx_eq. Qed.

(* ---------- Facts about used variables ---------- *)

Fixpoint used_ces (ces : list (ctor_tag * exp)) : Ensemble term.var :=
  match ces with
  | [] => Empty_set _
  | (_, e) :: ces => used_vars e :|: used_ces ces
  end.

Definition used {A} : univD A -> Ensemble term.var :=
  match A with
  | exp_univ_prod_ctor_tag_exp => fun '(_, e) => used_vars e
  | exp_univ_list_prod_ctor_tag_exp => used_ces
  | exp_univ_fundefs => fun fds => used_vars_fundefs fds
  | exp_univ_exp => fun e => used_vars e
  | exp_univ_var => fun x => [set x]
  | exp_univ_fun_tag => fun _ => Empty_set _
  | exp_univ_ctor_tag => fun _ => Empty_set _
  | exp_univ_prim => fun _ => Empty_set _
  | exp_univ_N => fun _ =>  Empty_set _
  | exp_univ_list_var => fun xs => FromList xs
  | exp_univ_primitive_value => fun _ => Empty_set _
  end.

(*
(* TODO: use a prettier definition in terms of greatest lower bound of all [frameD f x]s.
   Then show that for every hole type can find x1, x2 such that
     glb_x (frameD f x) = frameD f x1 ∩ frameD f x2 *)
Definition used_c {A B} (C : exp_c A B) : Ensemble term.var :=
  fun x => forall e, In _ (used (C ⟦+ e +⟧)) x.

Local Ltac clearpose H x e :=
  pose (x := e); assert (H : x = e) by (subst x; reflexivity); clearbody x.

Local Ltac insts_disagree H spec1 spec2 :=
  pose (Hx1 := H spec1); clearbody Hx1; simpl in Hx1;
  pose (Hx2 := H spec2); clearbody Hx2; simpl in Hx2;
  repeat normalize_used_vars; inversion Hx1; now inversion Hx2.

Lemma used_c_nil {A} : used_c (<[]> : exp_c A A) <--> Empty_set _.
Proof.
  split; [|auto with Ensembles_DB].
  intros x Hx; unfold In, used_c in Hx; simpl in Hx.
  destruct A; simpl in Hx.
  - insts_disagree Hx (mk_ctor_tag xH, Ehalt (mk_var xH)) (mk_ctor_tag xH, Ehalt (mk_var (xO xH))).
  - specialize (Hx []); assumption.
  - specialize (Hx Fnil); simpl in Hx; now normalize_used_vars.
  - insts_disagree Hx (Ehalt (mk_var xH)) (Ehalt (mk_var (xO xH))).
  - insts_disagree Hx (mk_var xH) (mk_var (xO xH)).
  - apply Hx; exact (mk_fun_tag xH).
  - apply Hx; exact (mk_ctor_tag xH).
  - apply Hx; exact (mk_prim xH).
  - apply Hx; exact N0.
  - specialize (Hx []); inversion Hx.
Qed. *)

Definition used_frame {A B} (f : exp_frame_t A B) : Ensemble term.var. refine (
  match f with
  | pair_ctor_tag_exp0 e => used_vars e
  | pair_ctor_tag_exp1 c => Empty_set _
  | cons_prod_ctor_tag_exp0 ces => used_ces ces
  | cons_prod_ctor_tag_exp1 (_, e) => used_vars e
  | Fcons0 ft xs e fds => FromList xs :|: used_vars e :|: used_vars_fundefs fds
  | Fcons1 f xs e fds => f |: FromList xs :|: used_vars e :|: used_vars_fundefs fds
  | Fcons2 f ft e fds => f |: used_vars e :|: used_vars_fundefs fds
  | Fcons3 f ft xs fds => f |: FromList xs :|: used_vars_fundefs fds
  | Fcons4 f ft xs e => f |: FromList xs :|: used_vars e
  | Econstr0 c ys e => FromList ys :|: used_vars e
  | Econstr1 x ys e => x |: FromList ys :|: used_vars e
  | Econstr2 x c e => x |: used_vars e
  | Econstr3 x c ys => x |: FromList ys
  | Ecase0 ces => used_ces ces
  | Ecase1 x => [set x]
  | Eproj0 c n y e => y |: used_vars e
  | Eproj1 x n y e => x |: (y |: used_vars e)
  | Eproj2 x c y e => x |: (y |: used_vars e)
  | Eproj3 x c n e => x |: used_vars e
  | Eproj4 x c n y => x |: [set y]
  | Eletapp0 f ft ys e => f |: FromList ys :|: used_vars e
  | Eletapp1 x ft ys e => x |: FromList ys :|: used_vars e
  | Eletapp2 x f ys e => x |: (f |: FromList ys :|: used_vars e)
  | Eletapp3 x f ft e => x |: (f |: used_vars e)
  | Eletapp4 x f ft ys => x |: (f |: FromList ys)
  | Efun0 e => used_vars e
  | Efun1 fds => used_vars_fundefs fds
  | Eapp0 ft xs => FromList xs
  | Eapp1 f xs => f |: FromList xs
  | Eapp2 f ft => [set f]
  | Eprim_val0 p e => used_vars e
  | Eprim_val1 x e => x |: used_vars e
  | Eprim_val2 x p => [set x]
  | Eprim0 p ys e => FromList ys :|: used_vars e
  | Eprim1 x ys e => x |: FromList ys :|: used_vars e
  | Eprim2 x p e => x |: used_vars e
  | Eprim3 x p ys => x |: FromList ys
  | Ehalt0 => Empty_set _
  end).
Defined.

Lemma used_frameD {A B} (f : exp_frame_t A B) (x : univD A) :
  used (frameD f x) <--> used_frame f :|: used x.
Proof.
  destruct f; simpl in *|-;
  repeat match goal with p : _ * _ |- _ => destruct p end; simpl;
  repeat normalize_used_vars;
  repeat normalize_sets;
  try solve [rewrite Ensemble_iff_In_iff; intros arbitrary; repeat rewrite In_or_Iff_Union; tauto].
  - induction l as [| [c e] ces IHces]; simpl; repeat normalize_used_vars; [eauto with Ensembles_DB|].
    rewrite IHces; eauto with Ensembles_DB.
  - induction x as [| [c e] ces IHces]; simpl; repeat normalize_used_vars; [eauto with Ensembles_DB|].
    rewrite IHces; eauto with Ensembles_DB.
Qed.

Fixpoint used_c {A B} (C : exp_c A B) : Ensemble term.var :=
  match C with
  | <[]> => Empty_set _
  | C >:: f => used_c C :|: used_frame f
  end.

Lemma used_c_comp {A B root} (C : exp_c B root) (D : exp_c A B) :
  used_c (C >++ D) <--> used_c C :|: used_c D.
Proof. induction D; simpl; [|rewrite IHD]; eauto with Ensembles_DB. Qed.

Lemma used_app {A B} (C : exp_c A B) (e : univD A) :
  used (C ⟦+ e +⟧) <--> used_c C :|: used e.
Proof.
  induction C; simpl; [eauto with Ensembles_DB|].
  rewrite IHC, used_frameD; eauto with Ensembles_DB.
Qed.

Corollary used_vars_app (C : exp_c exp_univ_exp exp_univ_exp) (e : exp) :
  used_vars (C ⟦+ e +⟧) <--> used_c C :|: used_vars e.
Proof. change (used_vars ?e) with (@used exp_univ_exp e); apply @used_app. Qed.

Corollary used_vars_fundefs_app (C : exp_c exp_univ_fundefs exp_univ_exp) (fds : fundefs) :
  used_vars (C ⟦+ fds +⟧) <--> used_c C :|: used_vars_fundefs fds.
Proof. change (used_vars ?e) with (@used exp_univ_exp e); apply @used_app. Qed.

(* Useful fact for some of the passes: every C : exp_c exp_univ_fundefs exp_univ_exp
   can be decomposed into D, fds, e such that C = D ∘ (Efun (rev fds ++ _) e) *)

Fixpoint ctx_of_fds (fds : fundefs) : exp_c exp_univ_fundefs exp_univ_fundefs :=
  match fds with
  | Fnil => <[]>
  | Fcons f ft xs e fds => ctx_of_fds fds >:: Fcons4 f ft xs e
  end.

Fixpoint fundefs_rev (fds : fundefs) : fundefs :=
  match fds with
  | Fnil => Fnil
  | Fcons f ft xs e fds => fundefs_append (fundefs_rev fds) (Fcons f ft xs e Fnil)
  end.

Lemma ctx_of_fds_app (fds1 : fundefs) : forall fds2 : fundefs,
  ctx_of_fds fds1 ⟦+ fds2 +⟧ = fundefs_append (fundefs_rev fds1) fds2.
Proof.
  induction fds1 as [f ft xs e fds1 IHfds1|]; [|reflexivity].
  intros fds2; cbn. rewrite IHfds1, <- fundefs_append_assoc. reflexivity.
Qed.

Fixpoint decompose_fd_c' {A B} (C : exp_c A B) {struct C} :
  match A as A', B as B' return exp_c A' B' -> Set with
  | exp_univ_fundefs, exp_univ_exp => fun C => {'(D, fds, e) | C = D >:: Efun0 e >++ ctx_of_fds fds}
  | _, _ => fun _ => Datatypes.unit
  end C.
Proof.
  destruct C as [|A AB B f C]; [destruct A; exact tt|destruct f, B; try exact tt].
  - specialize (decompose_fd_c' exp_univ_fundefs exp_univ_exp C); simpl in decompose_fd_c'.
    destruct decompose_fd_c' as [[[C' fds'] e'] HCfdse'].
    exists (C', Fcons v f l e fds', e'); now simpl.
  - exists (C, Fnil, e); now simpl.
Defined.

Definition decompose_fd_c := @decompose_fd_c' exp_univ_fundefs exp_univ_exp.

(* Misc. facts that may or may not be useful when dealing with dependently typed [exp_c]s *)

#[global] Instance exp_Frame_inj : Frame_inj (U:=exp_univ).
Proof. intros A B f x y; destruct f; now inversion 1. Qed.

From Stdlib Require Import Logic.JMeq.
From Stdlib Require Import Logic.Eqdep.
Ltac inv_ex :=
  repeat progress match goal with
  | H : existT ?P ?T _ = existT ?P ?T _ |- _ => apply inj_pairT2 in H
  end.

(* Inhabited types *)

Class Inhabited A := inhabitant : A.

#[global] Instance Inhabited_pos : Inhabited positive := xH.
#[global] Instance Inhabited_N : Inhabited N := N0.

#[global] Instance Inhabited_list A : Inhabited (list A) := [].
#[global] Instance Inhabited_prod A B `{Inhabited A} `{Inhabited B} : Inhabited (A * B) := (inhabitant, inhabitant).

#[global] Instance Inhabited_exp : Inhabited exp := Ehalt inhabitant.
#[global] Instance Inhabited_fundefs : Inhabited fundefs := Fnil.

Import PrimInt63.

Global Instance Inhabited_primitive_value : Inhabited AstCommon.primitive_value :=
  { inhabitant := existT _ AstCommon.primInt 0%uint63 }.

Definition univ_inhabitant {A} : univD A :=
  match A with
  | exp_univ_prod_ctor_tag_exp => inhabitant
  | exp_univ_list_prod_ctor_tag_exp => inhabitant
  | exp_univ_fundefs => inhabitant
  | exp_univ_exp => inhabitant
  | exp_univ_var => inhabitant
  | exp_univ_fun_tag => inhabitant
  | exp_univ_ctor_tag => inhabitant
  | exp_univ_prim => inhabitant
  | exp_univ_N => inhabitant
  | exp_univ_list_var => inhabitant
  | exp_univ_primitive_value => inhabitant
  end.

Class Sized A := size : A -> nat.

#[global] Instance Sized_pos : Sized positive := fun _ => S O.
#[global] Instance Sized_N : Sized N := fun _ => S O.
#[global] Instance Sized_primitive : Sized AstCommon.primitive_value := fun _ => S O.

Definition size_list {A} (size : A -> nat) : list A -> nat := fold_right (fun x n => S (size x + n)) 1%nat.
Definition size_prod {A B} (sizeA : A -> nat) (sizeB : B -> nat) : A * B -> nat := fun '(x, y) => S (sizeA x + sizeB y).

#[global] Instance Size_list A `{Sized A} : Sized (list A) := size_list size.
#[global] Instance Size_prod A B `{Sized A} `{Sized B} : Sized (A * B) := size_prod size size.

Fixpoint size_exp (e : exp) : nat
with size_fundefs (fds : fundefs) : nat.
Proof.
- refine (match e with
  | Econstr x c ys e => S (size x + size c + size ys + size_exp e)
  | Ecase x ces => S (size x + size_list (size_prod size size_exp) ces)
  | Eproj x c n y e => S (size x + size c + size n + size y + size_exp e)
  | Eletapp x f ft ys e => S (size x + size f + size ft + size ys + size_exp e)
  | Efun fds e => S (size_fundefs fds + size_exp e)
  | Eapp f ft xs => S (size f + size ft + size xs)
  | Eprim_val x p e => S (size x + size p + size_exp e)
  | Eprim x p ys e => S (size x + size p + size ys + size_exp e)
  | Ehalt x => S (size x)
  end).
- refine (match fds with
  | Fnil => 1%nat
  | Fcons f ft xs e fds => S (size f + size ft + size xs + size_exp e + size_fundefs fds)
  end).
Defined.

#[global] Instance Sized_exp : Sized exp := size_exp.
#[global] Instance Sized_fundefs : Sized fundefs := size_fundefs.

Definition univ_size {A} : univD A -> nat :=
  match A with
  | exp_univ_prod_ctor_tag_exp => size
  | exp_univ_list_prod_ctor_tag_exp => size
  | exp_univ_fundefs => size
  | exp_univ_exp => size
  | exp_univ_var => size
  | exp_univ_fun_tag => size
  | exp_univ_ctor_tag => size
  | exp_univ_prim => size
  | exp_univ_N => size
  | exp_univ_list_var => size
  | exp_univ_primitive_value => size
  end.

Lemma size_app {A} `{Sized A} (xs ys : list A) : size (xs ++ ys) < size xs + size ys.
Proof. induction xs as [|x xs IHxs]; cbn; lia. Qed.

Lemma frame_size_gt {A B} (f : exp_frame_t A B) (x : univD A) :
  (univ_size (frameD f x) > univ_size x)%nat.
Proof.
  destruct f; cbn;
    try change (size_exp x) with (size x); cbn;
  try change (size_fundefs x) with (size x); cbn;
  try change (size_list (size_prod size size) x) with (size x); cbn;
  try change (size x) with 1; cbn;
  try lia.

  change ((fix size_exp (e : exp) : nat :=
            match e with
            | Ecase _ ces => S (S (size_list (size_prod size size_exp) ces))
            | Eproj _ _ _ _ e0 => S (S (S (S (S (size_exp e0)))))
            | Eletapp _ _ _ ys e0 => S (S (S (S (size ys + size_exp e0))))
            | Efun fds e0 => S (size_fundefs fds + size_exp e0)
            | Eapp _ _ xs => S (S (S (size xs)))
            | Eprim_val _ _ e0 => S (S (S (size_exp e0)))
            | Econstr _ _ ys e0 | Eprim _ _ ys e0 => S (S (S (size ys + size_exp e0)))
            | Ehalt x0 => S (size x0)
            end
            with size_fundefs (fds : fundefs) : nat :=
              match fds with
              | Fcons _ _ xs e fds0 => S (S (S (size xs + size_exp e + size_fundefs fds0)))
              | Fnil => 1
              end
                for
                size_exp) x) with (size x).
  cbn. lia.
  change ((fix size_exp (e0 : exp) : nat :=
             match e0 with
             | Ecase _ ces => S (S (size_list (size_prod size size_exp) ces))
             | Eproj _ _ _ _ e1 => S (S (S (S (S (size_exp e1)))))
             | Eletapp _ _ _ ys e1 => S (S (S (S (size ys + size_exp e1))))
             | Efun fds e1 => S (size_fundefs fds + size_exp e1)
             | Eapp _ _ xs => S (S (S (size xs)))
             | Eprim_val _ _ e1 => S (S (S (size_exp e1)))
             | Econstr _ _ ys e1 | Eprim _ _ ys e1 => S (S (S (size ys + size_exp e1)))
             | Ehalt x0 => S (size x0)
             end
             with size_fundefs (fds : fundefs) : nat :=
               match fds with
               | Fcons _ _ xs e0 fds0 => S (S (S (size xs + size_exp e0 + size_fundefs fds0)))
               | Fnil => 1
               end
                 for
                 size_fundefs) x) with (size x).
  cbn. lia.
Qed.

Lemma exp_c_size_ge {A B} (C : exp_c A B) (x : univD A) :
  (univ_size (C ⟦+ x +⟧) >= univ_size x)%nat.
Proof.
  induction C as [|A AB B f C]; simpl; [lia|].
  assert (univ_size (C ⟦+ exp_frameD A AB f x +⟧) >= univ_size (frameD f x))%nat by apply IHC.
  assert (univ_size (frameD f x) > univ_size x)%nat by apply frame_size_gt.
  lia.
Qed.

Definition exp_c_size_eq {A B} (C : exp_c A B) (x : univD A) :
  univ_size (C ⟦+ x +⟧) = univ_size x -> JMeq C (<[]> : exp_c A A).
Proof.
  destruct C as [|A AB B f C]; simpl; [constructor|intros HC].
  assert (univ_size (C ⟦+ exp_frameD A AB f x +⟧) >= univ_size (exp_frameD A AB f x))%nat
   by apply exp_c_size_ge.
  assert (univ_size (exp_frameD A AB f x) > univ_size x)%nat by apply frame_size_gt.
  lia.
Qed.

Lemma exp_ext_nil {A B} (C : exp_c A B) : A = B -> (forall x, JMeq x (C ⟦+ x +⟧)) -> JMeq C (<[]> : exp_c A A).
Proof.
  destruct C as [|A AB B f C]; [constructor|simpl].
  intros HeqB Hext; subst; specialize (Hext univ_inhabitant).
  inversion Hext; inv_ex.
  apply f_equal with (f := univ_size) in H.
  match type of Hext with
  | JMeq _ (?C ⟦+ ?f +⟧) =>
    match f with
    | exp_frameD _ _ _ ?x =>
      assert (univ_size (C ⟦+ f +⟧) >= univ_size f)%nat by apply exp_c_size_ge;
      assert (univ_size f > univ_size x)%nat by apply frame_size_gt;
      lia
    end
  end.
Qed.

Corollary exp_ext_nil' {A B} (C : exp_c A B) : A = B -> (forall x, JMeq x (C ⟦+ x +⟧)) -> JMeq C (<[]> : exp_c B B).
Proof. intros; subst; now apply exp_ext_nil. Qed.
