From Stdlib Require Import NArith.BinNat Arith Relations.Relations MSets.MSets MSets.MSetRBT
     Lists.List micromega.Lia Sets.Ensembles.

Require Import LambdaANF.term LambdaANF.eval LambdaANF.Ensembles_util LambdaANF.List_util LambdaANF.tactics LambdaANF.set_util LambdaANF.ctx
        LambdaANF.logical_relations LambdaANF.logical_relations_cc LambdaANF.algebra LambdaANF.inline_letapp LambdaANF.lambda_lifting_correct.
Require Import LambdaANF.closure_conversion_correct ctx.

From Stdlib Require Import micromega.Lia.

Import ListNotations.

Open Scope alg_scope.


Section Bounds.


  (* ***** Fuel ***** *)

  Global Program Instance fuel_res_pre : @resource fin nat :=
    { zero := 0;
      one_i fin := 1;
      plus x y  := x + y; }.
  Solve Obligations with (simpl; lia).


  Global Program Instance fuel_res_ordered : @ordered fin nat fuel_res_pre :=
    { lt := Peano.lt }.
  Solve Obligations with (try (intro; intros; simpl; lia)).
  Solve Obligations with (try (simpl; lia)).
  Next Obligation.
    destruct (Compare_dec.lt_dec x y); auto. right. eexists (x - y). lia.
  Qed.

  Global Program Instance fuel_res_ones : @resource_ones fin nat fuel_res_pre.

  Global Program Instance fuel_res_hom : @nat_hom fin nat fuel_res_pre :=
    { to_nat y := y }.

  Global Program Instance fuel_res_exp : @exp_resource nat :=
    { HRes := fuel_res_pre }.

  Global Instance fuel_res : @fuel_resource nat.
  Proof.
    econstructor.
    eapply fuel_res_ordered.
    eapply fuel_res_ones.
    eapply fuel_res_hom.
  Defined.


  (* ***** Trace ***** *)


  Global Program Instance trace_res_pre : @resource fin (nat * nat) :=
    { zero := (0, 0);
      one_i fin :=
        match fin with
        | Four => (0, 1)
        | Six => (0, 1)
        | _ => (1, 0)
        end;
      plus x y := (fst x + fst y, snd x + snd y) }.
  Solve Obligations with (try (simpl; lia)).
  Solve Obligations with (try (split; congruence)).
  Next Obligation. simpl. f_equal; lia. Qed.
  Next Obligation. simpl. f_equal; lia. Qed.
  Next Obligation. simpl. f_equal; lia. Qed.

  Global Program Instance trace_res_exp : @exp_resource (nat * nat) :=
    { HRes := trace_res_pre }.

  Global Instance trace_res : @trace_resource (nat * nat).
  Proof.
    econstructor. eapply trace_res_exp.
  Defined.

  Ltac unfold_all :=
    try unfold zero in *;
    try unfold one_ctx in *;
    try unfold one in *;
    try unfold one_i in *;
    try unfold HRes in *;
    try unfold HRexp_f in *; try unfold fuel_res in *; try unfold fuel_res_exp in *; try unfold fuel_res_pre in *;
    try unfold HRexp_t in *; try unfold trace_res in *; try unfold trace_res_exp in *; try unfold trace_res_pre in *.


  Section Inline_bound.

    (* bound for inlining *)
    Definition inline_bound (L G : nat) : PostT :=
      fun '(e1, rho1, c1, (t1, tapp1)) '(e2, rho2, c2, (t2, tapp2)) =>
        c1 <= c2 + 2 * G * tapp1 + 2 * L /\
        tapp1 <= tapp2 + 2 * G * tapp2 + L /\
        t2 + tapp2 = c2.

    Context (cenv : ctor_env).

    Instance inline_bound_compat L G (Hi : L <= G) :
      Post_properties cenv (inline_bound L G) (inline_bound L G) (inline_bound G G).
    Proof.
      constructor; (try (intro; intros; intro; intros; destruct cout1; destruct cout2;
                         unfold inline_bound in *; unfold_all; simpl; split; [| split ]; lia)).
      - intro; intros. intro; intros. destruct cout1; destruct cout2. destruct cout1'; destruct cout2'.
        unfold inline_bound in *; unfold_all; simpl. destructAll. split. lia. split; lia.

      - intro; intros. intro; intros.
        unfold inline_bound in *; unfold_all; simpl.
        assert (c = 0). eapply Nat.lt_1_r. eassumption. subst. lia.
      - intro; intros. unfold post_base'.
        unfold inline_bound in *; unfold_all; simpl. lia.
      - intro; intros; unfold inline_bound in *.
        destruct x as [[[? ?] ?] [? ?]]; destruct y as [[[? ?] ?] [? ?]]. split; [| split ]; lia.
    Qed.

    Lemma inline_bound_post_Eapp_l i G v t l rho1 x rho2 :
      post_Eapp_l (inline_bound i G) (inline_bound (S i) G) v t l rho1 x rho2.
    Proof.
      intro; intros. unfold inline_bound in *. unfold_all. simpl in *.
      destruct cout1; destruct cout2. simpl in *. destructAll.
      split; [| split ]; try lia.
    Qed.

    Lemma inline_bound_remove_steps_letapp_OOT i j G :
      remove_steps_letapp_OOT cenv (inline_bound j G) (inline_bound (S (i + j)) G).
    Proof.
      intro; intros. unfold inline_bound in *. unfold_all. simpl in *.
      destruct cout1; destruct cout2. simpl in *.
      split; [| split ]; lia.
    Qed.

    Lemma inline_bound_remove_steps_letapp i j G :
      remove_steps_letapp cenv (inline_bound i G) (inline_bound j G) (inline_bound (S (i + j)) G).
    Proof.
      intro; intros. unfold inline_bound in *. unfold_all; simpl in *.
      destruct cout1; destruct cout2. destruct cout1'; destruct cout2'. simpl in *. lia.
    Qed.


    (* This allows us to prove divergence preservation *)
    Lemma inline_bound_post_upper_bound L G :
      post_upper_bound (inline_bound L G).
    Proof.
      intro; intros. unfold inline_bound in *. unfold_all.
      eexists (fun x => (1 + 2 * G + 2 * G * 2 * G) * x + 2 * L * 2 * G + 2 * L).
      intros.
      destruct cout1 as [t1 tapp1]; destruct cout2 as [t2 tapp2].

      destruct H. destruct H0.
      assert (Hleq : tapp1 <= cin2 + 2 * G * cin2 + L) by lia. clear H0 H1.

      assert (Hleq' : (1 + 2 * G + 2 * G * 2 * G) * cin1 + 2 * L * 2 * G + 2 * L <=
                      (1 + 2 * G + 2 * G * 2 * G) * cin2 + 2 * L * 2 * G + 2 * L).
      { eapply Nat.le_trans. eassumption. eapply Nat.le_trans.
        apply -> Nat.add_le_mono_r. apply -> Nat.add_le_mono_l.
        eapply Nat.mul_le_mono_l. eassumption.
        lia. }

      assert (Hleq'' : cin1 <= cin2).
      { eapply Nat.add_le_mono_r in Hleq'. eapply Nat.add_le_mono_r in Hleq'.
        eapply Nat.mul_le_mono_pos_l in Hleq'. eassumption. lia. }

      eexists (cin2 - cin1). simpl. lia.
    Qed.

    (* bound for inlining, toplevel *)
    Definition inline_bound_top (G : nat) : @PostT nat (nat * nat) :=
      fun '(e1, rho1, c1, (t1, tapp1)) '(e2, rho2, c2, (t2, tapp2)) =>
        let A := 1 + 2 * G + 2 * G * 2 * G in
        c1 <= A * c2 + A.

    Lemma inline_bound_top_impl (G : nat) :
      inclusion _ (inline_bound G G) (inline_bound_top G).
    Proof.
      intros [[[? ?] ?] [? ?]] [[[? ?] ?] [? ?]]. unfold inline_bound, inline_bound_top in *. unfold_all.
      intros. destructAll.
      eapply Nat.le_trans. eassumption.
      eapply Nat.le_trans. apply -> Nat.add_le_mono_r.
      apply -> Nat.add_le_mono_l.
      eapply Nat.mul_le_mono_l. eassumption.
      lia.
    Qed.

    (* For shrink reduction *)
    Open Scope ctx_scope.

    Lemma inline_bound_ctx1 :
      forall (C : exp_ctx) (e1 : exp) (rho1 rho1' : env) (e2 : exp) (rho2 : env) (cin1 cin2 : nat)
             (cout1 cout2 : nat * nat),
        ctx_to_rho C rho1 rho1' ->
        len_exp_ctx C = 1%nat ->
        inline_bound 0 1 (e1, rho1', cin1, cout1) (e2, rho2, cin2, cout2) ->
        inline_bound 1 1 (C |[ e1 ]|, rho1, cin1 <+> one (C |[ e1 ]|), cout1 <+> one (C |[ e1 ]|))
                     (e2, rho2, cin2, cout2).
    Proof.
      intro; intros. unfold inline_bound in *. unfold_all; simpl in *.
      destruct cout1; destruct cout2. simpl in *. destructAll.
      destruct (C |[ e1 ]|); simpl; try lia.
    Qed.


    Lemma inline_bound_Ecase :
      forall x cl t e n rho1 rho2 cin1 cout1 cin2 cout2,
        term_util.find_tag_nth cl t e n ->
        inline_bound 0 1 (e, rho1, cin1, cout1) (e, rho2, cin2, cout2) ->
        inline_bound 1 1 (Ecase x cl, rho1, cin1 <+> one (Ecase x cl), cout1 <+> one (Ecase x cl)) (e, rho2, cin2, cout2).
    Proof.
      intro; intros. unfold inline_bound in *. unfold_all; simpl in *.
      destruct cout1; destruct cout2. simpl in *. destructAll. lia.
    Qed.


  End Inline_bound.

  Section SimpleBound.

    Context (cenv : ctor_env).

    (* Simple bound for transformations that don't decrease steps *)
    Definition simple_bound (L : nat) : @PostT nat (nat * nat) :=
      fun '(e1, rho1, c1, (t1, tapp1)) '(e2, rho2, c2, (t2, tapp2)) =>
        c1 <= c2 + L.


    Instance simple_bound_compat k :
      Post_properties cenv (simple_bound 0) (simple_bound k) (simple_bound 0).
    Proof.
      constructor; (try (intro; intros; intro; intros; destruct cout1; destruct cout2;
                         unfold simple_bound  in *; unfold_all; simpl; lia)).
      - intro; intros. intro; intros. destruct cout1; destruct cout2. destruct cout1'; destruct cout2'.
        unfold simple_bound in *; unfold_all; simpl. destructAll. lia.
      - intro; intros. intro; intros.
        unfold simple_bound in *; unfold_all; simpl. lia.
      - intro; intros. unfold post_base'.
        unfold simple_bound in *; unfold_all; simpl. lia.
      - intro; intros; unfold simple_bound in *.
        destruct x as [[[? ?] ?] [? ?]]; destruct y as [[[? ?] ?] [? ?]]. lia.
    Qed.


    (* CC bound properties *)

    Lemma Hpost_locals_r :
      forall (n : nat) (rho1 rho2  rho2' : env)(e1 : exp) (e2 : exp)
             (cin1 : nat) (cout1 : nat * nat)
             (cin2 : nat) (cout2 : nat * nat) (C : exp_ctx),
        ctx_to_rho C rho2 rho2' ->
        simple_bound (n + to_nat (one_ctx C)) (e1, rho1, cin1, cout1)
                     (e2, rho2', cin2, cout2) ->
        simple_bound n (e1, rho1, cin1, cout1)
                     (C |[ e2 ]|, rho2, cin2 <+> (one_ctx C), cout2 <+> (one_ctx C)).
    Proof.
      intros. destruct cout1; destruct cout2. unfold simple_bound in *. unfold_all. simpl in *.
      lia.
    Qed.


    Lemma Hpost_locals_l :
      forall (n : nat) (rho1 rho2  rho2' : env)(e1 : exp) (e2 : exp)
             (cin1 : nat) (cout1 : nat * nat)
             (cin2 : nat) (cout2 : nat * nat) (C : exp_ctx),
        ctx_to_rho C rho2 rho2' ->
        simple_bound n (e1, rho1, cin1, cout1)
                     (C |[ e2 ]|, rho2, cin2 <+> (one_ctx C), cout2 <+> (one_ctx C)) ->
        simple_bound (n + to_nat (one_ctx C)) (e1, rho1, cin1, cout1)
                     (e2, rho2', cin2, cout2).
    Proof.
      intros. destruct cout1; destruct cout2. unfold simple_bound in *. unfold_all. simpl in *.
      lia.
    Qed.

    Lemma Hpost_locals_l0 :
      forall (n : nat) (rho1 rho2  rho2' : env)(e1 : exp) (e2 : exp)
             (cin1 : nat) (cout1 : nat * nat)
             (cin2 : nat) (cout2 : nat * nat) (C : exp_ctx),
        ctx_to_rho C rho2 rho2' ->
        simple_bound n (e1, rho1, cin1, cout1)
                     (C |[ e2 ]|, rho2, cin2, cout2) ->
        simple_bound (n + to_nat (one_ctx C)) (e1, rho1, cin1, cout1)
                     (e2, rho2', cin2, cout2).
    Proof.
      intros. destruct cout1; destruct cout2. unfold simple_bound in *. unfold_all. simpl in *.
      lia.
    Qed.

    Lemma HOOT : forall j, post_OOT (simple_bound j).
    Proof.
      intros. intro; intros. intro; intros.
      unfold simple_bound in *. unfold_all. simpl in *.
      lia.
    Qed.

    Lemma Hbase : forall j, post_base (simple_bound j).
    Proof.
      intros. intro; intros. unfold post_base'.
      unfold simple_bound in *. unfold_all. simpl in *.
      lia.
    Qed.

    Context (clo_tag : ctor_tag).

    Lemma HPost_letapp_cc :
      forall f x t xs e1 rho1 n k,
        k <= 4 + 4 * length xs  ->
        post_letapp_compat_cc' cenv clo_tag f x t xs e1 rho1 (simple_bound n) (simple_bound (n + k)) (simple_bound 0).
    Proof.
      intro; intros. intro; intros. destruct cout1; destruct cout2. destruct cout1'; destruct cout2'.
      unfold simple_bound in *; unfold_all; simpl. destructAll. lia.
    Qed.


    Lemma HPost_letapp_OOT_cc :
      forall f x t xs e1 rho1 n k,
        k <= 4 + 4 * length xs ->
        post_letapp_compat_cc_OOT' clo_tag f x t xs e1 rho1 (simple_bound (n + k)) (simple_bound 0).
    Proof.
      intro; intros. intro; intros. destruct cout1; destruct cout2.
      unfold simple_bound in *; unfold_all; simpl. destructAll. lia.
    Qed.


    Lemma HPost_app :
      forall k v t l rho1,
        k <= 4 + 4 * length l -> post_app_compat_cc' clo_tag v t l rho1 (simple_bound k) (simple_bound 0).
    Proof.
      intro; intros. intro; intros. destruct cout1; destruct cout2.
      unfold simple_bound in *; unfold_all; simpl. destructAll. lia.
    Qed.


    (* This allows us to prove divergence preservation *)
    Lemma simple_bound_post_upper_bound L :
      post_upper_bound (simple_bound L).
    Proof.
      intro; intros. unfold simple_bound in *. unfold_all.
      eexists (fun x => x +  L).
      intros.
      destruct cout1 as [t1 tapp1]; destruct cout2 as [t2 tapp2].
      eapply Nat.add_le_mono_r in H.

      eexists (cin2 - cin1). simpl. lia.
    Qed.

  End SimpleBound.

  Section HoistingBound.

    Context (cenv : ctor_env).

    Definition hoisting_bound (L G : nat) : @PostT nat (nat * nat) :=
      fun '(e1, rho1, c1, (t1, tapp1)) '(e2, rho2, c2, (t2, tapp2)) =>
        c1 <= c2 + G * c2 + L.

    Instance hoisting_bound_compat L G (Hi : L <= G) :
      Post_properties cenv (hoisting_bound L G) (hoisting_bound L G) (hoisting_bound G G).
    Proof.
      constructor; (try (intro; intros; intro; intros; destruct cout1; destruct cout2;
                         unfold hoisting_bound in *; unfold_all; simpl; lia)).
      - intro; intros. intro; intros. destruct cout1; destruct cout2. destruct cout1'; destruct cout2'.
        unfold hoisting_bound in *; unfold_all; simpl. destructAll. lia.
      - intro; intros. intro; intros.
        unfold hoisting_bound in *; unfold_all; simpl. lia.
      - intro; intros. unfold post_base'.
        unfold hoisting_bound in *; unfold_all; simpl. lia.
      - intro; intros; unfold hoisting_bound in *.
        destruct x as [[[? ?] ?] [? ?]]; destruct y as [[[? ?] ?] [? ?]]. lia.
    Qed.

    Lemma hoisting_bound_mon n m G :
      n <= m -> inclusion _ (hoisting_bound n G) (hoisting_bound m G).
    Proof.
      intros Hleq.
      intro; intros; unfold hoisting_bound in *.
      destruct x as [[[? ?] ?] [? ?]]; destruct y as [[[? ?] ?] [? ?]]. lia.
    Qed.


    Lemma hoisting_bound_post_Efun_l n G :
      post_Efun_l (hoisting_bound n G) (hoisting_bound (S n) G).
    Proof.
      intro; intros. unfold hoisting_bound in *. unfold_all. simpl in *.
      destruct cout1; destruct cout2. lia.
    Qed.

    Lemma hoisting_bound_post_Efun_r n m :
      (n <= m)%nat -> post_Efun_r (hoisting_bound n m) (hoisting_bound m m).
    Proof.
      intros Hleq.
      intro; intros. unfold hoisting_bound in *. unfold_all. simpl in *.
      destruct cout1; destruct cout2. lia.
    Qed.

    Lemma hoisting_bound_post_upper_bound n G :
      post_upper_bound (hoisting_bound n G).
    Proof.
      intro; intros. unfold hoisting_bound in *. unfold_all.
      eexists (fun x => G * x + x + n).
      intros.
      destruct cout1 as [t1 tapp1]; destruct cout2 as [t2 tapp2].
      eapply Nat.add_le_mono_r in H.
      replace (cin2 + G * cin2) with ((1 + G) * cin2) in H by lia.
      replace (G * cin1 + cin1) with ((1 + G) * cin1) in H by lia.
      eapply Nat.mul_le_mono_pos_l in H.
      eexists (cin2 - cin1). simpl. lia.
      lia.
    Qed.

  End HoistingBound.

  Section LambdaLiftingBound.

    Definition ll_bound (l : nat) := simple_bound 0.

    Context (cenv : ctor_env).

    Instance ll_bound_compat k m n :
      Post_properties cenv (ll_bound k) (ll_bound m) (ll_bound n).
    Proof. unfold ll_bound in *. eapply simple_bound_compat. Qed.

    Lemma ll_bound_local_steps :
      forall {A} e1 rho1 c1 t1 e2 rho2 c2 t2 fvs f B1 rhoc x t xs1 l,
        M.get f rho1 = Some (Vfun rhoc B1 x) ->
        find_def x B1 = Some (t, xs1, e1) ->
        ll_bound l (e1, rho1, c1, t1) (e2, rho2, c2, t2) ->
        l <= 1 + length xs1 + @length A fvs + 1 ->
        ll_bound 0 (e1, rho1, c1, t1) (e2, rho2, c2, t2).
    Proof.
      intros. destruct t1, t2.
      unfold simple_bound  in *; unfold_all; simpl in *. lia.
    Qed.

    Lemma ll_bound_mon :
      forall l l', l <= l' -> inclusion _ (ll_bound l) (ll_bound l').
    Proof.
      intros. intro; intros. eassumption.
    Qed.

   Lemma ll_bound_local_app :
     forall (e1 : exp) (rho1 : env) (f : var) (ft : fun_tag) (ys : list var) (rho2 : env),
       post_Eapp_r (ll_bound 0) (ll_bound (1 + Datatypes.length ys)) e1 rho1 f ft ys rho2.
   Proof.
     intros. intro; intros. destruct cout1, cout2.
     unfold simple_bound  in *; unfold_all; simpl in *. lia.
   Qed.


   Lemma ll_bound_local_app' :
     forall (e1 : exp) (rho1 : env) (f : var) (ft : fun_tag) (ys : list var) (rho2 : env),
       post_Eapp_r (ll_bound 1) (ll_bound (1 + Datatypes.length ys + 1)) e1 rho1 f ft ys rho2.
   Proof.
     intros. intro; intros. destruct cout1, cout2.
     unfold simple_bound  in *; unfold_all; simpl in *. lia.
   Qed.


   Lemma ll_bound_local_steps_let_app :
      forall e1 rho1 c1 t1 c1' t1' e2 rho2 e2' rho2' e2'' rho2'' c2  t2 c2' t2'
             f B1 e1' rhoc rhoc' x ft ys ys' xs1 vs1 v fvs ft' f',
        M.get f rho1 = Some (Vfun rhoc B1 f') ->
        find_def f' B1 = Some (ft, xs1, e1') ->
        set_lists xs1 vs1 (def_funs B1 B1 rhoc rhoc) = Some rhoc' ->
        (* maybe bstep is needed but ignore for now *)
        ll_bound 1 (e1', rhoc', c1, t1) (e2', rho2', c2, t2) ->
        ll_bound 0 (e1, M.set x v rho1, c1', t1') (e2'', rho2'', c2', t2') ->
        ll_bound 0 (Eletapp x f ft ys e1, rho1, c1 <+> c1' <+> one (Eletapp x f ft ys e1), t1 <+> t1' <+> one (Eletapp x f ft ys e1))
                 (e2, rho2, c2 <+> c2' <+> one (Eletapp x f' ft' (ys' ++ fvs) e2''),
                  t2 <+> t2' <+> one (Eletapp x f' ft' (ys' ++ fvs) e2'')).
   Proof.
     intros. destruct t1, t2, t1', t2'.
     unfold simple_bound  in *; unfold_all; simpl in *. lia.
   Qed.

   Lemma ll_bound_local_steps_let_app_OOT :
     forall e1 rho1 c1 t1  e2 rho2 e2' rho2' e2'' c2  t2
            f B1 e1' rhoc rhoc' x ft ys ys' xs1 vs1 fvs ft' f' f'',
       M.get f rho1 = Some (Vfun rhoc B1 f'') ->
       find_def f'' B1 = Some (ft, xs1, e1') ->
       set_lists xs1 vs1 (def_funs B1 B1 rhoc rhoc) = Some rhoc' ->
       (* maybe bstep is needed but ignore for now *)
       ll_bound 1 (e1', rhoc', c1, t1) (e2', rho2', c2, t2) ->
       ll_bound 0 (Eletapp x f ft ys e1, rho1, c1 <+> one (Eletapp x f ft ys e1), t1 <+> one (Eletapp x f ft ys e1))
                (e2, rho2, c2 <+> one (Eletapp x f' ft' (ys' ++ fvs) e2''),
                 t2 <+> one (Eletapp x f' ft' (ys' ++ fvs) e2'')).
   Proof.
     intros. destruct t1, t2.
     unfold simple_bound  in *; unfold_all; simpl in *. lia.
   Qed.



   Lemma ll_bound_local_steps_app :
     forall rho1 c1 t1 e2 rho2 e2' rho2' c2 t2
            f B1 e1' rhoc rhoc' f' ft ys xs1 vs1 f'' ft' ys' fvs,
       M.get f rho1 = Some (Vfun rhoc B1 f') ->
       find_def f' B1 = Some (ft, xs1, e1') ->
       set_lists xs1 vs1 (def_funs B1 B1 rhoc rhoc) = Some rhoc' ->
       (* maybe bstep is needed but ignore for now *)
       ll_bound 1 (e1', rhoc', c1, t1) (e2', rho2', c2, t2) ->
       ll_bound 0 (Eapp f ft ys, rho1, c1 <+> one (Eapp f ft ys), t1 <+> one (Eapp f ft ys))
                (e2, rho2, c2 <+> one (Eapp f'' ft' (ys' ++ fvs)), t2 <+> one (Eapp f' ft' (ys' ++ fvs))).
   Proof.
     intros. destruct t1, t2.
     unfold simple_bound  in *; unfold_all; simpl in *. lia.
   Qed.


   Lemma ll_bound_ctx_r :
     forall (n : nat) (e1 e2 : exp) (C : exp_ctx) (rho1 rho2 rho2' : env)
            (C0 : exp_ctx) c1 c2 cout1 cout2,
       ctx_to_rho C rho2 rho2' ->
       ll_bound n (e1, rho1, c1, cout1) (e2, rho2', c2, cout2) ->
       ll_bound (n + to_nat (one_ctx C0)) (e1, rho1, c1, cout1)
                (C |[ e2 ]|, rho2, plus c2 (one_ctx C), plus cout2 (one_ctx C)).
   Proof.
     intros. destruct cout1, cout2.
     unfold simple_bound  in *; unfold_all; simpl in *. lia.
   Qed.

  End LambdaLiftingBound.


  Section UncurryBound.


    Lemma Hpost_curry :
      forall e rho rho' rho'' c1 c2 cout1 cout2 f1 ft1 fv1 gv1,
        simple_bound 0 (e, rho, c1, cout1) (e, rho'', c2, cout2) ->
        simple_bound 0 (e, rho, c1, cout1) (Eapp f1 ft1 (gv1 ++ fv1), rho', plus c2 (one (Eapp f1 ft1 (gv1 ++ fv1))), plus cout2 (one (Eapp f1 ft1 (gv1 ++ fv1)))).
    Proof.
      intros. destruct cout1; destruct cout2. unfold simple_bound in *. unfold_all. simpl in *.
      lia.
    Qed.

    Lemma Hpost_idemp : inclusion _ (comp (simple_bound 0) (simple_bound 0)) (simple_bound 0).
    Proof.
      intro; intros.
      destruct x as [[[? ?] ?] [? ?]]; destruct y as [[[? ?] ?] [? ?]].
      unfold comp, simple_bound in *. unfold_all. destructAll.
      destruct x as [[[? ?] ?] [? ?]]. simpl in *. lia.
    Qed.

  End UncurryBound.
End Bounds.
