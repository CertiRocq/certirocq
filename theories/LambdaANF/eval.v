From Stdlib Require Import NArith.BinNat Relations.Relations MSets.MSets
     MSets.MSetRBT Lists.List micromega.Lia Sets.Ensembles
     Relations.Relations.

From CertiRocq.Common Require Import AstCommon exceptionMonad.

From CertiRocq Require Import LambdaANF.term LambdaANF.List_util LambdaANF.size_cps LambdaANF.ctx LambdaANF.term_util LambdaANF.set_util LambdaANF.map_util
     LambdaANF.identifiers LambdaANF.tactics LambdaANF.Ensembles_util.

Require Import compcert.lib.Coqlib.
Require Import LambdaANF.algebra.

Require Import MetaRocq.Utils.bytestring.

Import ListNotations.

(** An [env]ironment maps [var]s to their [val]ues *)
Definition env := M.t val.

(** A pair of an environment and an expression. The small step semantics is a transition system between this state *)
Definition state := (env * exp)%type.

(** Primitive functions map. *)
Definition prims := M.t (list val -> option val).

Section EVAL.

  Variable (pr : prims).

  Variable (cenv : ctor_env).


  (** Big step semantics with fuel and trace resources.
      Will raise OOT (out-of-time exception) if fuel is not enough,
      that lets us prove divergence preservation *)

  Inductive res {A} : Type :=
  | OOT
  | Res : A -> res.


  Context {fuel : Type} {Hf : @fuel_resource fuel} {trace : Type} {Ht : @trace_resource trace}.

  Open Scope alg_scope.

  Inductive bstep :  env -> exp -> fuel -> @res val -> trace -> Prop :=
  | BStept_constr :
      forall (x : var) (t : ctor_tag) (ys :list var) (e : exp)
             (rho rho' : env) (vs : list val) (v : res) (cin : fuel) (cout : trace),
        get_list ys rho = Some vs ->
        M.set x (Vconstr t vs) rho = rho' ->
        bstep_fuel rho' e cin v cout ->
        bstep rho (Econstr x t ys e) cin v cout
  | BStept_proj :
      forall (t : ctor_tag) (vs : list val)
             (rho : env) (x : var) (n : N) (y : var)
             (e : exp) (v : val) (v' : res) (cin : fuel) (cout : trace),
        M.get y rho = Some (Vconstr t vs) ->
        nthN vs n = Some v ->
        bstep_fuel (M.set x v rho) e cin v' cout ->
        bstep rho (Eproj x t n y e) cin v' cout
  | BStept_case :
      forall (y : var) (v : res) (e : exp) (t : ctor_tag) (cl : list (ctor_tag * exp))
             (vl : list val) (rho : env) (cin : fuel) (n : nat) (cout : trace),
        M.get y rho = Some (Vconstr t vl) ->
        caseConsistent cenv cl t ->
        find_tag_nth cl t e n ->
        bstep_fuel rho e cin v cout ->
        bstep rho (Ecase y cl) cin v cout
  | BStept_app :
      forall (rho' : env) (fl : fundefs) (f' : var) (vs : list val)
             (xs : list var) (e : exp) (rho'' rho : env) (f : var)
             (t : ctor_tag) (ys : list var) (v : res) (cin : fuel) (cout : trace),
        M.get f rho = Some (Vfun rho' fl f') ->
        get_list ys rho = Some vs ->
        (* The number of instructions generated here should be
         * independent of the size of B. We just need to
         * jump to a label *)
        find_def f' fl = Some (t,xs,e) ->
        set_lists xs vs (def_funs fl fl rho' rho') = Some rho'' ->
        bstep_fuel rho'' e cin v cout ->
        bstep rho (Eapp f t ys) cin v cout
  | BStept_letapp :
      forall (rho' : env) (fl : fundefs) (f' : var) (vs : list val)
             (xs : list var) (e_body e : exp) (rho'' rho : env) (x f : var)
             (t : ctor_tag) (ys : list var) (v : val) (v' : res)
             (cin1 cin2 : fuel) (cout1 cout2 : trace),
        (* evaluate application *)
        M.get f rho = Some (Vfun rho' fl f') ->
        get_list ys rho = Some vs ->
        find_def f' fl = Some (t,xs,e_body) ->
        set_lists xs vs (def_funs fl fl rho' rho') = Some rho'' ->
        bstep_fuel rho'' e_body cin1 (Res v) cout1 -> (* body evaluates to v *)
        (* evaluate let continuation *)
        bstep_fuel (M.set x v rho) e cin2 v' cout2 ->
        bstep rho (Eletapp x f t ys e) (cin1 <+> cin2) v' (cout1 <+> cout2)
  | BStept_letapp_oot :
      forall (rho' : env) (fl : fundefs) (f' : var) (vs : list val)
             (xs : list var) (e_body e : exp) (rho'' rho : env) (x f : var)
             (t : ctor_tag) (ys : list var) (cin : fuel) (cout : trace),
        M.get f rho = Some (Vfun rho' fl f') ->
        get_list ys rho = Some vs ->
        find_def f' fl = Some (t,xs,e_body) ->
        set_lists xs vs (def_funs fl fl rho' rho') = Some rho'' ->
        bstep_fuel rho'' e_body cin OOT cout -> (* body times out*)
        bstep rho (Eletapp x f t ys e) cin OOT cout
  | BStept_fun :
      forall (rho : env) (B : fundefs) (e : exp) (v : res) (cin : fuel) (cout : trace),
        bstep_fuel (def_funs B B rho rho) e cin v cout ->
        (* The definition of a function incur cost proportional to the number of FVs
        (to make the bound of the current cc independent of the term) *)
        bstep rho (Efun B e) cin v cout
  (* | BStept_prim :
      forall (vs : list val) (rho' rho : env) (x : var) (f : prim)
        (f' : list val -> option val) (ys : list var) (e : exp)
        (v : val) (v' : res) (cin : nat),
          get_list ys rho = Some vs ->
          M.get f pr = Some f' ->
          f' vs = Some v ->
          M.set x v rho = rho' ->
          bstep_fuel rho' e v' cin ->
          bstep rho (Eprim x f ys e) v' cin *)
  | BStept_halt :
      forall x v rho,
        M.get x rho = Some v ->
        bstep rho (Ehalt x) <0> (Res v) <0>
  with bstep_fuel :  env -> exp -> fuel -> @res val -> trace -> Prop :=
  | BStepf_OOT : (* not enought time units to take a step *)
      forall rho (e : exp) (c : fuel),
        (c << <1> e) -> (* not enough fuel *)
        bstep_fuel rho e c OOT <0>
  | BStepf_run : (* take a step *)
      forall rho e r (cin : fuel) (cout : trace),
        bstep rho e cin r cout ->
        bstep_fuel rho e (cin <+> (<1> e)) r (cout <+> (<1> e)).

  Scheme bstep_ind' := Minimality for bstep Sort Prop
    with bstep_fuel_ind' := Minimality for bstep_fuel Sort Prop.

  Definition not_stuck (rho : env) (e : exp) :=
    (exists cin v cout, bstep_fuel rho e cin (Res v) cout) \/
    (forall cin, exists cout, bstep_fuel rho e cin OOT cout).

  Ltac destruct_bstep :=
    match goal with
    | [ H : bstep _ _ _ _ |- _ ] => inv H
    end.


  Lemma find_tag_nth_deterministic l c e n e' n' :
    find_tag_nth l c e n ->
    find_tag_nth l c e' n' ->
    e = e' /\ n = n'.
  Proof.
    intros H1.
    revert e' n'; induction H1; intros e1 n1 H2;
      inv H2; try congruence; eauto. eapply IHfind_tag_nth in H8.
    inv H8; eauto.
  Qed.


  (** * Lemmas about bstep_fuel *)
  Lemma step_deterministic_aux rho e r v cin cin' r' v' cout cout' :
    bstep rho e cin r cout ->
    bstep rho e cin' r' cout' ->
    r = Res v -> r' = Res v' ->
    v = v' /\ cin = cin' /\ cout = cout'.
  Proof.
    set (P := fun rho e cin r cout =>
                forall v cin' r' v' cout',
                  bstep rho e cin' r' cout' ->
                  r = Res v -> r' = Res v' ->
                  v = v' /\ cin = cin' /\ cout = cout').
    set (P0 := fun rho e cin r cout =>
                 forall v cin' r' v' cout',
                   bstep_fuel rho e cin' r' cout' ->
                   r = Res v -> r' = Res v' ->
                   v = v' /\ cin = cin' /\ cout = cout').
    intros Hstep.
    revert v cin' r' v' cout'.
    induction Hstep using bstep_ind' with (P := P) (P0 := P0); unfold P, P0 in *;
      intros v1 r2 v2 cin2' cout2' Hstep2 Heq1 Heq2; subst;
        try now (inv Hstep2; repeat subst_exp; eapply IHHstep; eauto).
    - inv Hstep2. repeat subst_exp.
      eapply find_tag_nth_deterministic in H1; [| eapply H8 ]. inv H1.
      eapply IHHstep; eauto.
    - inv Hstep2. repeat subst_exp. eapply IHHstep in H18; eauto. destructAll.
      eapply IHHstep0 in H19; eauto. destructAll. eauto.
    - inv Hstep2. inv Heq1. repeat subst_exp. eauto.
    - inv Heq1.
    - inv Hstep2. eapply IHHstep in H; eauto.  destructAll. eauto.
  Qed.

  Lemma bstep_fuel_deterministic rho e v cin cin' v' cout cout' :
    bstep_fuel rho e cin (Res v) cout ->
    bstep_fuel rho e cin' (Res v') cout' ->
    v = v' /\ cin = cin' /\ cout = cout'.
  Proof.
    intros H1 H2; inv H1; inv H2; eauto.
    eapply step_deterministic_aux in H0; [ | eapply H | reflexivity | reflexivity ].
    destructAll; eauto.
  Qed.

  Lemma bstep_deterministic rho e v cin cin' v' cout cout' :
    bstep rho e cin (Res v) cout ->
    bstep rho e cin' (Res v') cout' ->
    v = v' /\ cin = cin' /\ cout = cout'.
  Proof.
    intros H1 H2. eapply step_deterministic_aux; eauto.
  Qed.


  Lemma bstep_lt_OOT_aux rho e r cin (v : val) cout cin':
    bstep rho e cin r cout ->
    r = Res v ->
    cin' << cin ->
    exists cout' c, bstep rho e cin' OOT cout' /\ cout = (c <+> cout').
  Proof.
    set (P := fun rho e cin r cout =>
                forall (v : val) cin',
  		  r = Res v -> cin' << cin ->
		  exists cout' c, bstep rho e cin' OOT cout' /\ cout = (c <+> cout')).
    set (P0 := fun rho e cin r cout =>
                 forall (v : val) cin',
  		   r = Res v -> cin' << cin ->
		   exists cout' c, bstep_fuel rho e cin' OOT cout' /\ cout = (c <+> cout')).
    intros Hstep. revert v cin'.
    induction Hstep using bstep_ind' with (P := P) (P0 := P0); unfold P, P0 in *;
      intros v1 cin' Heq Hlt; subst;
    try (now edestruct IHHstep;
         [reflexivity | eassumption | destructAll; do 2 eexists; split; eauto; econstructor; eauto ]).

    - edestruct (lt_all_dec cin' cin1).
      + edestruct IHHstep. reflexivity. eassumption. destructAll.
        do 2 eexists. split. eapply BStept_letapp_oot; eauto. rewrite plus_assoc. rewrite (plus_comm x0).
        rewrite <- plus_assoc. reflexivity.
      + inv H5. rewrite (plus_comm cin1) in Hlt. eapply plus_stable in Hlt.
        edestruct IHHstep0. reflexivity. eassumption. destructAll.
        do 2 eexists. split. rewrite plus_comm.
        eapply BStept_letapp; eauto.
        rewrite <- !plus_assoc. rewrite (plus_comm cout1). reflexivity.
    - inv Heq.
    - eapply lt_zero in Hlt. contradiction.
    - inv Heq.
    - edestruct (lt_all_dec cin' (one e)).
      + subst. do 2 eexists. split. econstructor 1; eauto.
        rewrite (plus_comm _ <0>). rewrite plus_zero. reflexivity.
      + destructAll. eapply plus_stable in Hlt.
        edestruct IHHstep. reflexivity. eassumption. destructAll.
        do 2 eexists. split. econstructor 2. eassumption. rewrite plus_assoc. reflexivity.
  Qed.

  Lemma bstep_lt_OOT rho e v cin cout cin' :
    bstep rho e cin (Res v) cout ->
    cin' << cin ->
    exists cout' c, bstep rho e cin' OOT cout' /\ cout = (c <+> cout').
  Proof.
    intros Hbstep Hlt. eapply bstep_lt_OOT_aux; eauto.
  Qed.

  Lemma bstep_fuel_lt_OOT rho e v cin cout cin' :
    bstep_fuel rho e cin (Res v) cout ->
    cin' << cin ->
    exists cout' c, bstep_fuel rho e cin' OOT cout' /\ cout = (c <+> cout').
  Proof.
    intros H1 Hlt; inv H1.
    edestruct (lt_all_dec cin' (one e)).
      + subst. do 2 eexists. split. econstructor 1; eauto.
        rewrite (plus_comm _ <0>). rewrite plus_zero. reflexivity.
      + destructAll. eapply plus_stable in Hlt.
        edestruct bstep_lt_OOT. eassumption. eassumption. destructAll.
        do 2 eexists. split. econstructor 2. eassumption. rewrite plus_assoc. reflexivity.
  Qed.


  Lemma bstep_OOT_subtrace_aux rho e (r : @res val) v cin cout cin' cout' :
    bstep rho e cin r cout ->
    r = Res v ->
    bstep rho e cin' OOT cout' ->
    (exists c', cout = (c' <+> cout')).
  Proof.
    set (P := fun rho e (cin : fuel) (r : @res val) cout =>
                forall v cin' cout',
                  r = Res v ->
                  bstep rho e cin' OOT cout' ->
                  (exists c', cout = (c' <+> cout'))).
    set (P0 := fun rho e (cin : fuel) (r : @res val) cout =>
                forall v cin' cout',
                  r = Res v ->
                  bstep_fuel rho e cin' OOT cout' ->
                  (exists c', cout = (c' <+> cout'))).
    intros Hstep. revert v cin' cout'.
    induction Hstep using bstep_ind' with (P := P) (P0 := P0); unfold P, P0 in *;
    intros v1 cin' cout' Heq Hs'; try (now subst; inv Hs'; repeat subst_exp; eauto).
    - inv Hs'; repeat subst_exp. eapply find_tag_nth_deterministic in H8; [| clear H8; eauto ]. inv H8.
      eapply IHHstep; eauto.
    - inv Hs'; repeat subst_exp; eauto.
      + eapply bstep_fuel_deterministic in H18; [| clear H18; eauto ]; destructAll.
        edestruct IHHstep0; [| eassumption | ]; eauto. subst.
        eexists.
        rewrite <- (plus_assoc cout0). rewrite (plus_comm cout0) at 1.
        rewrite plus_assoc at 1. reflexivity.
      + edestruct IHHstep; [| eassumption | ]; eauto. subst.
        eexists.
        rewrite (plus_assoc x0). rewrite (plus_comm cout') at 1.
        rewrite <- plus_assoc at 1. reflexivity.
    - subst. inv Hs'; repeat subst_exp; eauto.
      + eexists. rewrite (plus_comm _ <0>). rewrite plus_zero. reflexivity.
      + eapply IHHstep in H; eauto. destructAll.
        eexists.
        rewrite plus_assoc at 1. reflexivity.
  Qed.

  Lemma bstep_OOT_subtrace rho e v cin cout cin' cout' :
    bstep rho e cin (Res v) cout ->
    bstep rho e cin' OOT cout' ->
    (exists c', cout = (c' <+> cout')).
  Proof.
    intros Hs1 Hs2. eapply bstep_OOT_subtrace_aux. eassumption. reflexivity. eassumption.
  Qed.

  Lemma bstep_fuel_OOT_subtrace rho e v cin cout cin' cout' :
    bstep_fuel rho e cin (Res v) cout ->
    bstep_fuel rho e cin' OOT cout' ->
    (exists c', cout = (c' <+> cout')).
  Proof.
    intros Hs1 Hs2. inv Hs1. inv Hs2.
    + eexists. rewrite (plus_comm _ <0>). rewrite plus_zero. reflexivity.
    + eapply bstep_OOT_subtrace in H; eauto. destructAll.
      eexists.
      rewrite plus_assoc at 1. reflexivity.
  Qed.


  Lemma bstep_OOT_determistic_aux rho e (r r' : @res val) cin cout cin' cout' c :
    bstep rho e cin r cout ->
    r = OOT ->
    cin = (c <+> cin') ->
    bstep rho e cin' r' cout' ->
    r' = OOT /\ (exists c', cout = (c' <+> cout')).
  Proof.
    set (P := fun rho e cin (r : @res val) cout =>
                forall r' cin' cout' c,
                  r = OOT ->
                  cin = (c <+> cin') ->
                  bstep rho e cin' r' cout' ->
                  r' = OOT /\ (exists c', cout = (c' <+> cout'))).
    set (P0 := fun rho e cin (r : @res val) cout =>
                 forall r' cin' cout' c,
                   r = OOT ->
                   cin = (c <+> cin') ->
                   bstep_fuel rho e cin' r' cout' ->
                   r' = OOT /\ (exists c', cout = (c' <+> cout'))).
    intros Hstep. revert r' cin' cout' c.
    induction Hstep using bstep_ind' with (P := P) (P0 := P0); unfold P, P0 in *;
      intros r' cin' cout' c1 Heq Hleq Hs'; subst; try now (inv Hs'; repeat subst_exp; eauto).
    - inv Hs'; repeat subst_exp. eapply find_tag_nth_deterministic in H8; [| clear H8; eauto ]. inv H8.
      eapply IHHstep; eauto.
    - inv Hs'; repeat subst_exp; eauto.
      + eapply bstep_fuel_deterministic in H18; [| clear H18; eauto ]; destructAll.
        rewrite !(plus_comm cin0), <- plus_assoc in Hleq.
        eapply plus_inv in Hleq. subst.
        edestruct IHHstep0; [| | eassumption | ]; eauto. destructAll. split; eauto. eexists.
        rewrite <- (plus_assoc cout0). rewrite (plus_comm cout0) at 1.
        rewrite plus_assoc at 1. reflexivity.
      + split. reflexivity.
        eapply bstep_fuel_OOT_subtrace in H3; [| eassumption ]. destructAll.
        eexists.
        rewrite (plus_assoc x0). rewrite (plus_comm cout') at 1.
        rewrite <- plus_assoc at 1. reflexivity.
    - inv Hs'; repeat subst_exp; eauto. exfalso.
      eapply IHHstep in H17; eauto. inv H17. congruence.
      rewrite (plus_comm cin1). rewrite <- plus_assoc. reflexivity.
    - inv Hs'; eauto.
      + split; eauto. eexists <0>. rewrite plus_zero. reflexivity.
      + rewrite <- plus_assoc, plus_comm in H. eapply plus_lt in H.
        eapply lt_antisym in H. contradiction.
    - inv Hs'; eauto.
      + split; eauto. eexists. rewrite (plus_comm _ <0>). rewrite plus_zero. reflexivity.
      + rewrite <- plus_assoc in Hleq. eapply plus_inv in Hleq. subst.
        edestruct IHHstep. reflexivity. reflexivity. eassumption. destructAll.
        split. reflexivity. eexists. rewrite plus_assoc. reflexivity.
  Qed.

  Lemma bstep_OOT_determistic rho e r' cin cout c cout' :
    bstep rho e (c <+> cin) OOT cout ->
    bstep rho e cin r' cout' ->
    r' = OOT /\ (exists c', cout = (c' <+> cout')).
  Proof.
    intros; eapply bstep_OOT_determistic_aux; [ | reflexivity | | ]; eauto.
  Qed.

  Lemma bstep_fuel_OOT_determistic rho e r' cin cout c cout' :
    bstep_fuel rho e (c <+> cin) OOT cout ->
    bstep_fuel rho e cin r' cout' ->
    r' = OOT /\ (exists c', cout = (c' <+> cout')).
  Proof.
    intros Hs1 Hs2. inv Hs1.
    - inv Hs2; eauto.
      + split; eauto. eexists <0>. rewrite plus_zero. reflexivity.
      + rewrite <- plus_assoc, plus_comm in H. eapply plus_lt in H.
        eapply lt_antisym in H. contradiction.
    - inv Hs2; eauto.
      + split; eauto. eexists. rewrite (plus_comm _ <0>). rewrite plus_zero. reflexivity.
      + rewrite <- plus_assoc in H. eapply plus_inv in H. subst.
        edestruct bstep_OOT_determistic_aux. eapply H2. reflexivity. reflexivity. eassumption.
        destructAll.
        split. reflexivity. eexists. rewrite plus_assoc. reflexivity.
  Qed.



  Lemma bstep_gt_aux rho e r cin (v : val) cout cin' r' cout' :
    bstep rho e cin r cout ->
    r = Res v -> cin << cin' ->
    ~ bstep rho e cin' r' cout'.
  Proof.
    set (P := fun rho e cin r (cout : trace) =>
                forall (v : val) r' cin' cout',
                  r = Res v ->
                  cin << cin' ->
                  ~ bstep rho e cin' r' cout').
    set (P0 := fun rho e cin r (cout : trace) =>
                forall (v : val) r' cin' cout',
                  r = Res v ->
                  cin << cin' ->
                  ~ bstep_fuel rho e cin' r' cout').
    intros Hstep. revert v r' cin' cout'.
    induction Hstep using bstep_ind' with (P := P) (P0 := P0); unfold P, P0 in *;
      intros v1 r' cin' cout' Heq Hlt Hstep'; subst; (try now (inv Hstep'; repeat subst_exp; eauto));
        try now (inv Hstep'; repeat subst_exp; eauto; eapply IHHstep; eauto).
    - inv Hstep'; repeat subst_exp; eauto.
      eapply find_tag_nth_deterministic in H8; [| clear H8; eauto ]. inv H8.
      eapply IHHstep; eauto.
    - inv Hstep'; repeat subst_exp; eauto.
      + eapply bstep_fuel_deterministic in H18; [| clear H18; eauto ]; destructAll.
        eapply IHHstep0; [| | eapply H19 ]. reflexivity.
        rewrite !(plus_comm cin0) in Hlt. eapply plus_stable in Hlt.
        eassumption.
      + eapply IHHstep; [| | eassumption ]. reflexivity.
        eapply plus_lt. eapply Hlt.
    - inv Hstep'. eapply lt_antisym in Hlt. contradiction.
    - inv Hstep'.
      + rewrite plus_comm in Hlt. eapply plus_lt in Hlt.
        eapply lt_trans in Hlt. specialize (Hlt H). eapply lt_antisym in Hlt. eassumption.
      + eapply IHHstep; [| | eassumption ]. reflexivity.
        eapply plus_stable in Hlt. eassumption.
  Qed.

  Lemma bstep_gt rho e cin (v : val) cout cin' r cout' :
    bstep rho e cin (Res v) cout ->
    cin << cin' ->
    ~ bstep rho e cin' r cout'.
  Proof.
    intros; eapply bstep_gt_aux; eauto.
  Qed.

  Lemma bstep_fuel_gt rho e cin (v : val) cout cin' r cout' :
    bstep_fuel rho e cin (Res v) cout ->
    cin << cin' ->
    ~ bstep_fuel rho e cin' r cout'.
  Proof.
    intros Hstep Hlt Hstep'. inv Hstep. inv Hstep'.
    - rewrite plus_comm in Hlt. eapply plus_lt in Hlt.
      eapply lt_trans in Hlt. specialize (Hlt H0). eapply lt_antisym in Hlt. eassumption.
    - eapply bstep_gt; [| | eassumption ]. eassumption.
      eapply plus_stable in Hlt. eassumption.
  Qed.

  Lemma bstep_OOT_monotonic_aux rho e r cin cout cin' c :
    bstep rho e cin r cout ->
    r = OOT ->
    cin = (c <+> cin') ->
    exists cout' c, bstep rho e cin' OOT cout' /\ cout = (c <+> cout').
  Proof.
    set (P := fun rho e cin (r : @res val)  (cout : trace) =>
                forall c cin',
                  r = OOT ->
                  cin = (c <+> cin') ->
                  exists cout' c, bstep rho e cin' OOT cout' /\ cout = (c <+> cout')).
    set (P0 := fun rho e cin (r : @res val)  (cout : trace) =>
                 forall c cin',
                   r = OOT ->
                   cin = (c <+> cin') ->
                   exists cout' c, bstep_fuel rho e cin' OOT cout' /\ cout = (c <+> cout')).
    intros Hstep. revert c cin'.
    induction Hstep using bstep_ind' with (P := P) (P0 := P0); unfold P, P0 in *;
      intros c' cin' Heq Hleq; subst;
        try now (edestruct IHHstep; eauto; destructAll; do 2 eexists; split;
                 [ econstructor; eauto | reflexivity ]).
    - edestruct (lt_all_dec cin' cin1).
      + edestruct bstep_fuel_lt_OOT. eassumption. eassumption. destructAll.
        do 2 eexists. split. eapply BStept_letapp_oot; eauto.
        rewrite plus_assoc. rewrite (plus_comm x0). rewrite <- plus_assoc. reflexivity.
      + inv H5. rewrite <- plus_assoc, (plus_comm cin1) in Hleq.
        eapply plus_inv in Hleq. subst.
        edestruct IHHstep0. reflexivity. reflexivity. destructAll.
        do 2 eexists. split. rewrite plus_comm. econstructor; eauto.
        rewrite <- plus_assoc. rewrite (plus_comm _ x2). rewrite plus_assoc. reflexivity.
    - congruence.
    - do 2 eexists. split. econstructor 1. eapply plus_lt. rewrite plus_comm. eassumption.
      rewrite plus_zero. reflexivity.
    - edestruct (lt_all_dec cin' (one e)).
      + do 2 eexists. split.
        now econstructor; eauto. rewrite (plus_comm _ <0>). rewrite plus_zero. reflexivity.
      + destructAll. rewrite <- plus_assoc in Hleq. eapply plus_inv in Hleq. subst.
        edestruct IHHstep. reflexivity. reflexivity. destructAll.
        do 2 eexists. split. econstructor 2; eauto. rewrite plus_assoc. reflexivity.
  Qed.

  Lemma bstep_OOT_monotonic rho e c1 c2 cout :
    bstep rho e (c1 <+> c2) OOT cout ->
    exists cout' c, bstep rho e c2 OOT cout' /\ cout = (c <+> cout').
  Proof.
    intros; eapply bstep_OOT_monotonic_aux; eauto.
  Qed.

  Lemma bstep_fuel_OOT_monotonic rho e c1 c2 cout :
    bstep_fuel rho e (c1 <+> c2) OOT cout ->
    exists cout' c, bstep_fuel rho e c2 OOT cout' /\ cout = (c <+> cout').
  Proof.
    intros Hs; inv Hs.
    - do 2 eexists. split. econstructor 1. eapply plus_lt. rewrite plus_comm. eassumption.
      rewrite plus_zero. reflexivity.
    - edestruct (lt_all_dec c2 (one e)).
      + do 2 eexists. split.
        now econstructor; eauto. rewrite (plus_comm _ <0>). rewrite plus_zero. reflexivity.
      + destructAll. rewrite <- plus_assoc in H. eapply plus_inv in H. subst.
        edestruct bstep_OOT_monotonic. eassumption. destructAll.
        do 2 eexists. split. econstructor 2; eauto. rewrite plus_assoc. reflexivity.
  Qed.


  Lemma bstep_fuel_zero_OOT rho e :
    bstep_fuel rho e <0> OOT <0>.
  Proof.
    econstructor. eapply zero_one_lt.
  Qed.

  Lemma bstep_deterministic_res rho e cin r r' cout cout' :
    bstep rho e cin r cout ->
    bstep rho e cin r' cout' ->
    r = r' /\ cout = cout'.
  Proof.
    set (P := fun rho e cin r cout =>
                forall r' cout',
                  bstep rho e cin r' cout' ->
                  r = r' /\ cout = cout').
    set (P0 := fun rho e cin r cout =>
                forall r' cout',
                  bstep_fuel rho e cin r' cout' ->
                  r = r' /\ cout = cout').
    intros Hstep.
    revert r' cout'.
    induction Hstep using bstep_ind' with (P := P) (P0 := P0); unfold P, P0 in *; intros r' cout' Hstep';
      try now (inv Hstep'; repeat subst_exp; eapply IHHstep; eauto).
    - inv Hstep'. repeat subst_exp.
      eapply find_tag_nth_deterministic in H1; [| eapply H8 ]. inv H1.
      eapply IHHstep; eauto.
    - inv Hstep'; repeat subst_exp.
      + eapply bstep_fuel_deterministic in H18; [| clear H18; eauto ]. destructAll.
        rewrite !(plus_comm cin0) in H10. eapply plus_inv in H10.
        subst. edestruct IHHstep0. eapply H19. subst. now eauto.
      + rewrite plus_comm in H18. eapply bstep_fuel_OOT_monotonic in H18. destructAll.
        eapply IHHstep in H5. inv H5. congruence.
    - inv Hstep'; repeat subst_exp; eauto.
      eapply bstep_fuel_OOT_determistic in H17. inv H17. congruence.
      rewrite plus_comm. eassumption.
    - inv Hstep'. repeat subst_exp; eauto.
    - inv Hstep'; eauto. rewrite plus_comm in H. eapply plus_lt in H. eapply lt_antisym in H.
      contradiction.
    - inv Hstep'; eauto.
      rewrite plus_comm in H. eapply plus_lt in H. eapply lt_antisym in H. contradiction.
      eapply plus_inv in H. subst. edestruct IHHstep. eassumption. subst; eauto.
  Qed.

  Lemma bstep_fuel_deterministic_res rho e cin r r' cout cout' :
    bstep_fuel rho e cin r cout ->
    bstep_fuel rho e cin r' cout' ->
    r = r' /\ cout = cout'.
  Proof.
    intros H1 H2. inv H1; inv H2; eauto.
    rewrite plus_comm in H. eapply plus_lt in H. eapply lt_antisym in H. contradiction.
    rewrite plus_comm in H0. eapply plus_lt in H0. eapply lt_antisym in H0. contradiction.
    eapply plus_inv in H0. subst. eapply bstep_deterministic_res  in H; [| eassumption ].
    destructAll. eauto.
  Qed.


  Definition diverge (rho : env) (e: exp) : Prop :=
    forall cin, exists cout, bstep_fuel rho e cin OOT cout.

  (** * Interpretation of (certain) evaluation contexts as environments *)

  Inductive ctx_to_rho : exp_ctx -> env -> env -> Prop :=
  | Hole_c_to_rho :
      forall rho,
        ctx_to_rho Hole_c rho rho
  | Eproj_c_to_rho :
      forall rho rho' t y N Γ C vs v,
        M.get Γ rho = Some (Vconstr t vs) ->
        nthN vs N = Some v ->
        ctx_to_rho C (M.set y v rho) rho' ->
        ctx_to_rho (Eproj_c y t N Γ C) rho rho'
  | Econstr_c_to_rho :
      forall rho rho' x t ys C vs,
        get_list ys rho = Some vs ->
        ctx_to_rho C (M.set x (Vconstr t vs) rho) rho' ->
        ctx_to_rho (Econstr_c x t ys C) rho rho'
  | Efun_c_to_rho :
      forall rho rho' C B,
        ctx_to_rho C (def_funs B B rho rho) rho' ->
        ctx_to_rho (Efun1_c B C) rho rho'.


  (** * Lemmas about [ctx_to_rho] *)

  Lemma ctx_to_rho_comp_ctx_l C C1 C2 rho rho' :
    ctx_to_rho C rho rho' ->
    comp_ctx C1 C2 C ->
    exists rho'',
      ctx_to_rho C1 rho rho'' /\
      ctx_to_rho C2 rho'' rho'.
  Proof.
    intros Hctx. revert C1 C2.
    induction Hctx; intros C1 C2 Hcomp.
    - inv Hcomp. eexists; split; constructor.
    - inv Hcomp.
      + edestruct IHHctx as [rho'' [H1 H2]].
        constructor. inv H1.
        eexists; split. constructor.
        econstructor; eauto.
      + edestruct IHHctx as [rho'' [H1 H2]]. eassumption.
        eexists; split. econstructor; eauto.
        eassumption.
    - inv Hcomp.
      + edestruct IHHctx as [rho'' [H1 H2]].
        constructor. inv H1.
        eexists; split. constructor.
        econstructor; eauto.
      + edestruct IHHctx as [rho'' [H1 H2]]. eassumption.
        eexists; split. econstructor; eauto.
        eassumption.
    - inv Hcomp.
      eexists; split. econstructor; eauto. econstructor. now eauto.
      edestruct IHHctx as [rho'' [H1 H2']]. eassumption.
      eexists; split. econstructor; eauto.
      eassumption.
  Qed.

  Lemma ctx_to_rho_comp_ctx_f_r C1 C2 rho1 rho2 rho3 :
    ctx_to_rho C1 rho1 rho2 ->
    ctx_to_rho C2 rho2 rho3 ->
    ctx_to_rho (comp_ctx_f C1 C2) rho1 rho3.
  Proof.
    revert C2 rho1 rho2 rho3.
    induction C1; intros C2 rho1 rho2 rho3 Hctx1 GHctx2; inv Hctx1.
    - eassumption.
    - simpl; econstructor; eauto.
    - simpl; econstructor; eauto.
    - simpl; econstructor; eauto.
  Qed.

  (** * Interpretation of interprable evaluation contexts as environments *)

  Fixpoint interprable (C : exp_ctx) : bool :=
    match C with
    | Hole_c => true
    | Econstr_c _ _ _ C
    | Eproj_c _ _ _ _ C
    | Eprim_val_c _ _ C
    | Eprim_c _ _ _ C
    | Efun1_c _ C
    | Eletapp_c _ _ _ _ C => interprable C
    | Ecase_c _ _ _ _ _
    | Efun2_c _ _ => false
    end.


  Definition cost_ctx (c : exp_ctx) : nat :=
    match c with
    | Econstr_c x t ys c => 1 (* + length ys *)
    | Eproj_c x t n y c => 1
    | Ecase_c _ _ _ _ _ => 1
    | Eletapp_c x f t ys c => 1 (* + length ys *)
    | Efun1_c B c => 1
    | Efun2_c _ _ => 1
    | Eprim_val_c _ _ _ => 1
    | Eprim_c _ _ _ c => 1 (* + length ys *)
    | Hole_c => 0
    end.

  Inductive interpret_ctx : exp_ctx -> env -> fuel -> @res env -> trace -> Prop :=
  | Eproj_c_i :
      forall rho r t y N Γ C vs v (cin : fuel) (cout : trace),
        M.get Γ rho = Some (Vconstr t vs) ->
        nthN vs N = Some v ->
        interpret_ctx_fuel C (M.set y v rho) cin r cout ->
        interpret_ctx (Eproj_c y t N Γ C) rho cin r cout
  | Econstr_c_i :
      forall rho r x t ys C vs (cin : fuel) (cout : trace),
        get_list ys rho = Some vs ->
        interpret_ctx_fuel C (M.set x (Vconstr t vs) rho) cin r cout ->
        interpret_ctx (Econstr_c x t ys C) rho cin r cout
  | Efun_c_i :
      forall rho r C B (cin : fuel) (cout : trace),
        interpret_ctx_fuel C (def_funs B B rho rho) cin r cout ->
        interpret_ctx (Efun1_c B C) rho cin r cout
  | Eletapp_c_i :
      forall rho fl rhoc rhoc' f' vs xs e_body c x f t ys v r
             (cin1 cin2 : fuel) (cout1 cout2 : trace),
        rho ! f = Some (Vfun rhoc fl f') ->
        get_list ys rho = Some vs ->
        find_def f' fl = Some (t, xs, e_body) ->
        set_lists xs vs (def_funs fl fl rhoc rhoc) = Some rhoc' ->
        bstep_fuel rhoc' e_body cin1 (Res v) cout1 ->
        interpret_ctx_fuel c (M.set x v rho) cin2 r cout2 ->
        interpret_ctx (Eletapp_c x f t ys c) rho (cin1 <+> cin2) r (cout1 <+> cout2)
  | Eletapp_c_i_OOT :
      forall rho fl rhoc rhoc' f' vs xs e_body c x f t ys (cin : fuel) (cout : trace),
        rho ! f = Some (Vfun rhoc fl f') ->
        get_list ys rho = Some vs ->
        find_def f' fl = Some (t, xs, e_body) ->
        set_lists xs vs (def_funs fl fl rhoc rhoc) = Some rhoc' ->
        bstep_fuel rhoc' e_body cin OOT cout ->
        interpret_ctx (Eletapp_c x f t ys c) rho cin OOT cout
  with interpret_ctx_fuel : exp_ctx -> env -> fuel -> @res env -> trace -> Prop :=
  | ctx_hole:
      forall rho,
        interpret_ctx_fuel Hole_c rho <0> (Res rho) <0>
  | ctx_OOT :
      forall C rho cin,
        lt cin (one_ctx C) ->
        C <> Hole_c ->
        interpret_ctx_fuel C rho cin OOT <0>
  | ctx_step :
      forall C rho r (cin : fuel) (cout : trace),
        C <> Hole_c ->
        interpret_ctx C rho cin r cout ->
        interpret_ctx_fuel C rho (cin <+> one_ctx C) r (cout <+> one_ctx C).


  Lemma interpret_ctx_bstep_l C e rho v cin cout:
    bstep_fuel rho (C|[ e ]|) cin (Res v) cout ->
    interprable C = true ->
    exists rho' cin1 cout1 cin2 cout2,
      (cin1 <+> cin2) = cin /\
      (cout1 <+> cout2) = cout /\
      interpret_ctx_fuel C rho cin1 (Res rho') cout1 /\
      bstep_fuel rho' e cin2 (Res v) cout2.
  Proof.
    revert e rho v cin cout; induction C; intros e1 rho v' cin cout Hb Hi; try now inv Hi.
    - simpl in Hb. eexists rho, (@zero _ fuel _), <0>, cin, cout. split; [| split; eauto ].
      rewrite plus_zero. reflexivity.
      rewrite plus_zero. reflexivity.
      econstructor. econstructor. eassumption.
    - simpl in Hb, Hi. inv Hb. inv H.
      edestruct IHC. eassumption. eassumption. destructAll.
      do 5 eexists. split; [| split ].
      3:{ split. econstructor 3. now congruence. econstructor; eauto. eassumption. }
      rewrite !plus_assoc. rewrite (plus_comm x2). reflexivity.
      rewrite !plus_assoc. rewrite (plus_comm x3). reflexivity.
    - simpl in Hb, Hi. inv Hb. inv H.
      edestruct IHC. eassumption. eassumption. destructAll.
      do 5 eexists. split; [| split ].
      3:{ split. econstructor 3. now congruence. econstructor; eauto. eassumption. }
      rewrite !plus_assoc. rewrite (plus_comm x2). reflexivity.
      rewrite !plus_assoc. rewrite (plus_comm x3). reflexivity.
    - simpl in Hb, Hi. inv Hb. inv H.
    - simpl in Hb, Hi. inv Hb. inv H.
    - simpl in Hb, Hi. inv Hb. inv H.
      edestruct IHC. eassumption. eassumption. destructAll. repeat subst_exp.
      do 5 eexists. split; [| split ].
      3:{ split; [| eassumption ].
          econstructor 3. now congruence. econstructor; eauto. }
      rewrite !plus_assoc. rewrite (plus_comm x2). reflexivity.
      rewrite !plus_assoc. rewrite (plus_comm x3). reflexivity.
    - simpl in Hb, Hi. inv Hb. inv H.
      edestruct IHC. eassumption. eassumption. destructAll.
      do 5 eexists. split; [| split ].
      3:{ split. econstructor 3. now congruence. econstructor; eauto. eassumption. }
      rewrite !plus_assoc. rewrite (plus_comm x2). reflexivity.
      rewrite !plus_assoc. rewrite (plus_comm x3). reflexivity.
  Qed.

  Lemma interpret_ctx_bstep_r C e rho rho' r cin1 cin2 cout1 cout2 :
    interpret_ctx_fuel C rho cin1 (Res rho') cout1 ->
    bstep_fuel rho' e cin2 r cout2 ->
    bstep_fuel rho (C|[ e ]|) (cin1 <+> cin2) r (cout1 <+> cout2).
  Proof.
    revert e rho rho' r cin1 cin2 cout1 cout2; induction C;
      intros e1 rho rho' r cin1 cin2 cout1 cout2 Hi Hs1; (try now inv Hi);
              try (now (inv Hi; inv H0;
                        rewrite !plus_assoc, !(plus_comm (one_ctx _)), <- !plus_assoc;
                        econstructor; econstructor; eauto)).
    - inv Hi. simpl. rewrite !plus_zero. eassumption. inv H0.
    - inv Hi. inv H0. simpl.
      rewrite !plus_assoc, !(plus_comm (one_ctx _)), <- !plus_assoc.
      econstructor. rewrite !plus_assoc. econstructor; eauto.
  Qed.

  Lemma interpret_ctx_OOT_bstep C e rho cin cout:
    interpret_ctx_fuel C rho cin OOT cout ->
    bstep_fuel rho (C|[ e ]|) cin OOT cout.
  Proof.
    revert e rho cin cout; induction C; intros e1 rho cin cout' Hi; (try now inv Hi);
      try now (inv Hi; [ econstructor; eauto
                       | inv H0; econstructor 2; eauto;  simpl; econstructor; eauto ]).
  Qed.

  Lemma interprable_comp_f_l C1 C2:
    interprable C1 = true -> interprable C2 = true ->
    interprable (comp_ctx_f C1 C2) = true.
  Proof.
    induction C1; intros H1 H2; simpl in *; eauto.
  Qed.

  Lemma interprable_comp_f_r C1 C2:
    interprable (comp_ctx_f C1 C2) = true ->
    interprable C1 = true /\ interprable C2 = true.
  Proof.
    induction C1; intros H1; simpl in *; eauto.
    congruence. congruence.
  Qed.

  Lemma interprable_inline_letapp e x C z :
    inline_letapp e x = Some (C, z) ->
    interprable C = true.
  Proof.
    revert x C z; induction e; intros x C z Hin; simpl in *;
      try match goal with
          | [ _ : context[inline_letapp ?E ?X] |- _] =>
            destruct (inline_letapp E X) as [ [C' z'] |] eqn:Hin'; inv Hin; simpl; eauto
          end.
    now inv Hin. inv Hin. reflexivity. inv Hin. reflexivity.
  Qed.


  Lemma eval_ctx_app_OOT_Eprim rho C x p xs e1 e2 cin cout :
    bstep_fuel rho (C |[ Eprim x p xs e1 ]|) cin OOT cout ->
    interprable C = true ->
    bstep_fuel rho (C |[ Eprim x p xs e2 ]|) cin OOT cout.
  Proof.
    revert rho cin cout.
    induction C; intros rho cin cout Hs Hi; eauto;
      try congruence;
      try now (inv Hs;
               [ econstructor; eassumption |
                 inv H; unfold one; simpl;
                 constructor 2; econstructor; eauto ]).

    Unshelve. exact 0%nat.
  Qed.

  Lemma eval_ctx_app_OOT_Eprim_val rho C x p e1 e2 cin cout :
    bstep_fuel rho (C |[ Eprim_val x p e1 ]|) cin OOT cout ->
    interprable C = true ->
    bstep_fuel rho (C |[ Eprim_val x p e2 ]|) cin OOT cout.
  Proof.
    revert rho cin cout.
    induction C; intros rho cin cout Hs Hi; eauto;
      try congruence;
      try now (inv Hs;
               [ econstructor; eassumption |
                 inv H; unfold one; simpl;
                 constructor 2; econstructor; eauto ]).

    Unshelve. exact 0%nat.
  Qed.

  Lemma eval_ctx_app_OOT_Eapp rho C e cin cout x f t xs :
    bstep_fuel rho (C |[ Eapp f t xs ]|) cin OOT cout ->
    interprable C = true ->
    bstep_fuel rho (C |[ Eletapp x f t xs e ]|) cin OOT cout.
  Proof.
    revert rho e cin cout.
    induction C; intros rho e1 cin cout Hs Hi; eauto;
      try congruence;
      try now (inv Hs;
               [ econstructor; eassumption |
                 inv H; unfold one; simpl; constructor 2; econstructor; eauto ]).

    Unshelve. exact 0%nat.
  Qed.

  Lemma eval_ctx_app_Ehalt_div rho C e cin cout x :
    bstep_fuel rho (C |[ Ehalt x ]|) cin OOT cout ->
    interprable C = true ->
    bstep_fuel rho (C |[ e ]|) cin OOT cout.
  Proof.
    revert rho e cin cout.
    induction C; intros rho e1 cin cout Hs Hi; eauto;
      try congruence;
      try now (inv Hs;
               [ econstructor; eassumption |
                 inv H; unfold one; simpl; constructor 2; econstructor; eauto ]).
    simpl in *. inv Hs.
    2:{ inv H. }
    econstructor. unfold one. erewrite one_eq. eassumption.

    Unshelve. exact 0%nat.
  Qed.


  Lemma interpret_ctx_eq_env_P S C rho rho' cin cout :
    interpret_ctx_fuel C rho cin (Res rho') cout ->
    Disjoint _ (bound_var_ctx C) S ->
    eq_env_P S rho rho'.
  Proof.
    revert rho rho' cin cout; induction C; intros rho rho' cin cout Hin Hd; inv Hin.
    - eapply eq_env_P_refl.
    - inv H0.
    - inv H0. rewrite bound_var_Econstr_c in *.
      eapply eq_env_P_trans; [| eapply IHC; [ eassumption | now sets ] ].
      eapply eq_env_P_sym. eapply eq_env_P_set_not_in_P_l; eauto.
      eapply eq_env_P_refl. eapply Disjoint_In_l. sets. auto.
    - inv H0. rewrite bound_var_Eproj_c in *.
      eapply eq_env_P_trans; [| eapply IHC; [ eassumption | now sets ] ].
      eapply eq_env_P_sym. eapply eq_env_P_set_not_in_P_l; eauto.
      eapply eq_env_P_refl. eapply Disjoint_In_l. sets. auto.
    - inv H0.
    - inv H0.
    - inv H0. rewrite bound_var_Eletapp_c in *.
      eapply eq_env_P_trans; [| eapply IHC; [ eassumption | now sets ] ].
      eapply eq_env_P_sym. eapply eq_env_P_set_not_in_P_l; eauto.
      eapply eq_env_P_refl. eapply Disjoint_In_l. sets. auto.
    - inv H0.
    - inv H0. rewrite bound_var_Fun1_c in *.
      eapply eq_env_P_trans; [| eapply IHC; [ eassumption | now sets ] ].
      eapply eq_env_P_def_funs_not_in_P_r. eapply eq_env_P_refl.
      eapply Disjoint_Included_r. eapply name_in_fundefs_bound_var_fundefs. sets.
    - inv H0.
  Qed.


  Scheme interpret_ctx_ind' := Minimality for interpret_ctx Sort Prop
    with interpret_ctx_fuel_ind' := Minimality for interpret_ctx_fuel Sort Prop.

  Lemma interpret_ctx_deterministic_aux rho C r v cin cout r' v' cin' cout' :
    interpret_ctx C rho cin r cout ->
    interpret_ctx C rho cin' r' cout' ->
    r = Res v -> r' = Res v' ->
    v = v' /\ cin = cin' /\ cout = cout'.
  Proof.
    set (R := fun C rho cin r cout =>
                forall v r' v' cin' cout',
                  interpret_ctx C rho cin' r' cout' ->
                  r = Res v -> r' = Res v' ->
                  v = v' /\ cin = cin' /\ cout = cout').
    set (R0 := fun C rho cin r cout =>
                forall v r' v' cin' cout',
                  interpret_ctx_fuel C rho cin' r' cout' ->
                  r = Res v -> r' = Res v' ->
                  v = v' /\ cin = cin' /\ cout = cout').
    intros Hint.
    revert v r' v' cin' cout'.
    induction Hint using interpret_ctx_ind' with (P := R) (P0 := R0); unfold R, R0 in *;
      intros v1 r2 v2 cin' cout' Hint2 Heq1 Heq2; subst;
        (try now inv Hint2; repeat subst_exp; eapply IHHint; [ eassumption | reflexivity | reflexivity ]).
    - inv Hint2. repeat subst_exp.
      eapply bstep_fuel_deterministic in H18; [| clear H18; eassumption ]. destructAll.
      eapply IHHint in H19; eauto. destructAll. split; eauto.
    - inv Heq1.
    - inv Hint2. inv Heq1; eauto. inv H0.
    - inv Heq1.
    - inv Hint2. congruence.
      eapply IHHint in H1; eauto. destructAll. split; eauto.
  Qed.

  Lemma interpret_ctx_fuel_deterministic C rho v v' cin cin' cout cout' :
    interpret_ctx_fuel C rho cin (Res v) cout ->
    interpret_ctx_fuel C rho cin' (Res v') cout' ->
    v = v' /\ cin = cin' /\ cout = cout'.
  Proof.
    intros H1 H2; inv H1; inv H2; eauto.
    - congruence.
    - congruence.
    - eapply interpret_ctx_deterministic_aux in H0; [ | clear H0; eassumption | reflexivity | reflexivity ].
      destructAll. eauto.
  Qed.

  Lemma interpret_ctx_deterministic C rho v v' cin cin' cout cout' :
    interpret_ctx C rho cin (Res v) cout ->
    interpret_ctx C rho cin' (Res v') cout' ->
    v = v' /\ cin = cin' /\ cout = cout'.
  Proof.
    intros H1 H2.
    eapply interpret_ctx_deterministic_aux; eauto.
  Qed.

  Lemma bstep_fuel_ctx_OOT rho C e cin cout :
    bstep_fuel rho (C |[ e ]|) cin OOT cout ->
    interprable C = true ->
    interpret_ctx_fuel C rho cin OOT cout \/
    exists rho' cin1 cin2 cout1 cout2,
      interpret_ctx_fuel C rho cin1 (Res rho') cout1 /\
      bstep_fuel rho' e cin2 OOT cout2 /\
      cin = (cin1 <+> cin2) /\ cout = (cout1 <+> cout2).
  Proof.
    revert rho e cin cout. induction C; intros rho e1 cin cout Hstep Hi; (try now inv Hi); simpl in Hi.
    - simpl in Hstep. right. do 5 eexists. split. econstructor. split. eassumption.
      rewrite !plus_zero; eauto.
    - inv Hstep.
      + left. econstructor; [| congruence ]. eassumption.
      + inv H. eapply IHC in H10; eauto. inv H10.
        * left. eapply ctx_step; [ congruence | econstructor; eauto ].
        * destructAll. right. do 5 eexists.
          split; [| split ]; [| eassumption |]. econstructor. congruence. econstructor; eauto.
          rewrite (plus_assoc _ _ x1), (plus_comm (one_ctx _) x1), <- plus_assoc.
          rewrite (plus_assoc _ _ x3), (plus_comm (one_ctx _) x3), <- plus_assoc. eauto.
    - inv Hstep.
      + left. econstructor; [| congruence ]. eassumption.
      + inv H. eapply IHC in H11; eauto. inv H11.
        * left. eapply ctx_step; [ congruence | econstructor; eauto ].
        * destructAll. right. do 5 eexists.
          split; [| split ]; [| eassumption |]. econstructor. congruence. econstructor; eauto.
          rewrite (plus_assoc _ _ x1), (plus_comm (one_ctx _) x1), <- plus_assoc.
          rewrite (plus_assoc _ _ x3), (plus_comm (one_ctx _) x3), <- plus_assoc. eauto.
    - inv Hstep.
      + left. econstructor; [| congruence ]. eassumption.
      + inv H.
    - inv Hstep.
      + left. econstructor; [| congruence ]. eassumption.
      + inv H.
    - inv Hstep.
      + left. econstructor; [| congruence ]. eassumption.
      + inv H.
        * eapply IHC in H14. inv H14.
          -- left. eapply ctx_step. congruence. econstructor; eauto.
          -- destructAll. right. do 5 eexists.
             split; [| split ].
             econstructor. congruence. now econstructor; eauto. eassumption. split.
             rewrite (plus_assoc _ _ x1), (plus_comm (one_ctx _) x1), <- !plus_assoc. reflexivity.
             rewrite (plus_assoc _ _ x3), (plus_comm (one_ctx _) x3), <- !plus_assoc. reflexivity.
          -- eassumption.
        * left. eapply ctx_step. congruence. econstructor; eauto.
    - inv Hstep.
      + left. econstructor; [| congruence ]. eassumption.
      + inv H. eapply IHC in H6; eauto. inv H6.
        * left. unfold one_ctx. eapply ctx_step; [ congruence | econstructor; eauto ].
        * destructAll. right. do 5 eexists.
          split; [| split ]; [| eassumption |]. econstructor. congruence. econstructor; eauto.
          rewrite (plus_assoc _ _ x1), (plus_comm (one_ctx _) x1), <- plus_assoc.
          rewrite (plus_assoc _ _ x3), (plus_comm (one_ctx _) x3), <- plus_assoc. eauto.
  Qed.



  (** * SMALL STEP SEMANTICS DEFS *)
  (* fuel-based evaluator, could also use n from bstep_e with a termination lex (n, e) *)

  Definition l_opt {A} (e:option A) (s:string):exception A :=
    match e with
    | None => Exc s
    | Some e => Ret e
    end.

  (* TODO : Small step for letapp? *)
  (*
  Definition sstep_f (rho:env) (e:exp) : exception (env* exp) :=
    match e with
      | Eprim x f ys e' =>
        do vs  <- l_opt (getlist ys rho) ("Eprim: failed to getlist");
        do f' <- l_opt (M.get f pr) ("Eprim: prim not found");
        do v <- l_opt (f' vs) ("Eprim: prim did not compute");
        let rho' := M.set x v rho in
        Ret (rho', e')
      | Econstr x t ys e' =>
        do vs <- l_opt (get_list ys rho) ("Econstr: failed to get args");
          let rho' := M.set x (Vconstr t vs) rho in
          Ret (rho', e')
      | Eproj x t m y e' =>
        (match (M.get y rho) with
           | Some (Vconstr t' vs) =>
             if Pos.eqb t t' then
               do v <- l_opt (nthN vs m) ("Eproj: projection failed");
               let rho' := M.set x v rho in
               Ret (rho', e')
             else (exceptionMonad.Exc "Proj: tag check failed")
           | _ => (exceptionMonad.Exc "Proj: var not found")
         end)
      | Efun fl e' =>
        let rho' := def_funs fl fl rho rho in
        Ret (rho', e')
      | Ehalt x =>
        (exceptionMonad.Exc "Halt: can't step")
      | Ecase y cl =>
        match M.get y rho with
          | Some (Vconstr t vs) =>
            do e <- l_opt (findtag cl t) ("Case: branch not found");
              if caseConsistent_f cenv cl t then
                Ret (rho, e)
               else     (exceptionMonad.Exc "Case: consistency failure")
          | Some _ =>  (exceptionMonad.Exc "Case: arg is not a constructor")
          | None => (exceptionMonad.Exc "Case: arg not found")
        end
      | Eletapp x f t ys e =>
        (match (M.get f rho) with
           | Some (Vfun rho' fl f') =>
             do vs <- l_opt (get_list ys rho) ("App: failed to get args");
               (match  find_def f' fl with
                | Some (t', xs ,e_body) =>
                  if (Pos.eqb t t') then
                  do rho'' <- l_opt (set_lists xs vs (def_funs fl fl rho' rho')) ("Fun: set_lists failed");
                    Ret (rho'', e)
                  else (exceptionMonad.Exc "Fun: tag check failed")
              | _ => (exceptionMonad.Exc "Fun: function not found in bundle")
            end)
           |  _ => (exceptionMonad.Exc "Fun: Bundle not found")
         end)
    end.

      | Eapp f t ys =>
        (match (M.get f rho) with
           | Some (Vfun rho' fl f') =>
             do vs <- l_opt (get_list ys rho) ("App: failed to get args");
           (match  find_def f' fl with
              | Some (t', xs ,e) =>
                if (Pos.eqb t t') then
                  do rho'' <- l_opt (set_lists xs vs (def_funs fl fl rho' rho')) ("Fun: set_lists failed");
                  Ret (rho'', e)
                else (exceptionMonad.Exc "Fun: tag check failed")
              | _ => (exceptionMonad.Exc "Fun: function not found in bundle")
            end)
           |  _ => (exceptionMonad.Exc "Fun: Bundle not found")
         end)
    end.
   *)

  Open Scope bs_scope.

  (* Either fail with an Exn, runs out of fuel and return (Ret) inl of the current state or finish to evaluate and return inr of a val *)
  Fixpoint bstep_f (rho:env) (e:exp) (n:nat): exception ((env * exp) + val) :=
    match n with
    | O => exceptionMonad.Ret (inl (rho, e))
    | S n' =>
      ( match e with
        | Eprim_val x p e' =>
          let rho' := M.set x (Vprim p) rho in
          bstep_f rho' e' n'
        | Eprim x f ys e' =>
          do vs <- l_opt (get_list ys rho) ("Eprim: failed to get_list");
          do f' <- l_opt (M.get f pr) ("Eprim: prim not found");
          do v <- l_opt (f' vs) ("Eprim: prim did not compute");
          let rho' := M.set x v rho in
          bstep_f rho' e' n'
        | Econstr x t ys e' =>
          do vs <- l_opt (get_list ys rho) ("Econstr: failed to get args");
          let rho' := M.set x (Vconstr t vs) rho in
          bstep_f rho' e' n'
        | Eproj x t m y e' =>
          (match (M.get y rho) with
           | Some (Vconstr t' vs) =>
             if Pos.eqb t t' then
               do v <- l_opt (nthN vs m) ("Eproj: projection failed");
               let rho' := M.set x v rho in
               bstep_f rho' e' n'
             else (exceptionMonad.Exc "Proj: tag check failed")
           | _ => (exceptionMonad.Exc "Proj: var not found")
           end)
        | Efun fl e' =>
          let rho' := def_funs fl fl rho rho in
          bstep_f rho' e' n'
        | Ehalt x =>
          match (M.get x rho) with
          | Some v => exceptionMonad.Ret (inr v)
          | None => (exceptionMonad.Exc "Halt: value not found")
          end
        | Ecase y cl =>
          match M.get y rho with
          | Some (Vconstr t vs) =>
            do e <- l_opt (findtag cl t) ("Case: branch not found");
            if caseConsistent_f cenv cl t then
              bstep_f rho e n'
            else (exceptionMonad.Exc "Case: consistency failure")
          | _ => (exceptionMonad.Exc "Case: branch not found")
          end
        | Eletapp x f t ys e =>
          (match (M.get f rho) with
           | Some (Vfun rho' fl f') =>
             do vs <- l_opt (get_list ys rho) ("App: failed to get args");
             (match  find_def f' fl with
              | Some (t', xs ,e_body) =>
                if (Pos.eqb t t') then
                  do rho'' <- l_opt (set_lists xs vs (def_funs fl fl rho' rho')) ("Fun: set_lists failed");
                  do v <- bstep_f rho'' e_body n';
                  match v with
                  | inl st => Ret (inl st)
                  | inr v => bstep_f (M.set x v rho) e n'
                  end
                else (exceptionMonad.Exc "Fun: tag check failed")
              | _ => (exceptionMonad.Exc "Fun: function not found in bundle")
              end)
           |  _ => (exceptionMonad.Exc "Fun: Bundle not found")
           end)
        | Eapp f t ys =>
          (match (M.get f rho) with
           | Some (Vfun rho' fl f') =>
             do vs <- l_opt (get_list ys rho) ("App: failed to get args");
             (match  find_def f' fl with
              | Some (t', xs ,e) =>
                if (Pos.eqb t t') then
                  do rho'' <- l_opt (set_lists xs vs (def_funs fl fl rho' rho')) ("Fun: set_lists failed");
                  bstep_f rho'' e n'
                else (exceptionMonad.Exc "Fun: tag check failed")
              | _ => (exceptionMonad.Exc "Fun: function not found in bundle")
              end)
           |  _ => (exceptionMonad.Exc "Fun: Bundle not found")
           end)
        end)
    end.


  (** Small step semantics -- Relational definition *)
  Inductive step: state -> state -> Prop :=
  | Step_constr: forall vs rho x t ys e,
      get_list ys rho = Some vs ->
      step (rho, Econstr x t ys e) (M.set x (Vconstr t vs) rho, e)
  | Step_proj: forall vs v rho x t n y e,
      M.get y rho = Some (Vconstr t vs) ->
      nthN vs n = Some v ->
      step (rho, Eproj x t n y e) (M.set x v rho, e)
  | Step_case: forall t vl e' rho y cl,
      M.get y rho = Some (Vconstr t vl) ->
      caseConsistent cenv cl t ->
      findtag cl t = Some e' ->
      step (rho, Ecase y cl) (rho, e')
  | Step_fun: forall rho fl e,
      step (rho, Efun fl e) (def_funs fl fl rho rho, e)
  | Step_app: forall rho' fl f' vs xs e rho'' rho f t ys,
      M.get f rho = Some (Vfun rho' fl f') ->
      get_list ys rho = Some vs ->
      find_def f' fl = Some (t,xs,e) ->
      set_lists xs vs (def_funs fl fl rho' rho') = Some rho'' ->
      step (rho, Eapp f t ys) (rho'', e)
  | Step_prim: forall vs v rho' rho x f f' ys e,
      get_list ys rho = Some vs ->
      M.get f pr = Some f' ->
      f' vs = Some v ->
      M.set x v rho = rho' ->
      step (rho, Eprim x f ys e) (rho', e)
  (* need to go from value to exp somehow ... *)
  (* | Step_halt : forall x v rho, *)
  (*                 M.get x rho = Some v -> *)
  (*                 step (rho, Ehalt x) (rho, v) *).





  (* small-step matches big-step *)


  Inductive halt_state: (env * exp) -> val -> Prop :=
  | Chalt :
      forall rho x v,
        M.get x rho = Some v ->
        halt_state (rho, Ehalt x) v.



  (* Other (older) definitions of big-step semantics *)

  (** Big step semantics with cost counting *)
  Inductive bstep_e : env -> exp -> val -> nat -> Prop :=
  | BStep_constr :
      forall (x : var) (t : ctor_tag) (ys :list var) (e : exp)
             (rho rho' : env) (vs : list val) (v : val) (c : nat),
        get_list ys rho = Some vs ->
        M.set x (Vconstr t vs) rho = rho' ->
        bstep_e rho' e v c ->
        bstep_e rho (Econstr x t ys e) v c
  | BStep_proj :
      forall (t : ctor_tag) (vs : list val) (v : val)
             (rho : env) (x : var) (n : N) (y : var)
             (e : exp) (ov : val) (c : nat),
        M.get y rho = Some (Vconstr t vs) ->
        nthN vs n = Some v ->
        bstep_e (M.set x v rho) e ov c ->
        bstep_e rho (Eproj x t n y e) ov c (* force equality on [t] *)
  | BStep_case :
      forall (y : var) (v : val) (e : exp) (t : ctor_tag) (cl : list (ctor_tag * exp))
             (vl : list val) (rho : env) (c : nat),
        M.get y rho = Some (Vconstr t vl) ->
        caseConsistent cenv cl t -> (* NEW *)
        findtag cl t = Some e ->
        bstep_e rho e v c ->
        bstep_e rho (Ecase y cl) v c
  | BStep_app :
      forall (rho' : env) (fl : fundefs) (f' : var) (vs : list val)
             (xs : list var) (e : exp) (rho'' rho : env) (f : var)
             (t : ctor_tag) (ys : list var) (v : val) (c : nat),
        M.get f rho = Some (Vfun rho' fl f') ->
        get_list ys rho = Some vs ->
        find_def f' fl = Some (t,xs,e) ->
        set_lists xs vs (def_funs fl fl rho' rho') = Some rho'' ->
        bstep_e rho'' e v c ->
        bstep_e rho (Eapp f t ys) v (c+1)  (* force equality on [t] *)
  | BStep_letapp :
      forall (rho' : env) (fl : fundefs) (f' : var) (vs : list val)
             (xs : list var) (e_body e : exp) (rho'' rho : env) (x f : var)
             (t : ctor_tag) (ys : list var) (v v' : val) (c c' : nat),
        (* evaluate application *)
        M.get f rho = Some (Vfun rho' fl f') ->
        get_list ys rho = Some vs ->
        find_def f' fl = Some (t,xs,e_body) ->
        set_lists xs vs (def_funs fl fl rho' rho') = Some rho'' ->
        bstep_e rho'' e_body v c -> (* body evaluates to v *)
        (* evaluate let continuation *)
        bstep_e (M.set x v rho) e v' c' ->
        bstep_e rho (Eletapp x f t ys e) v' (c + c' + 1)  (* force equality on [t] *)
  | BStep_fun :
      forall (rho : env) (fl : fundefs) (e : exp) (v : val) (c : nat),
        bstep_e (def_funs fl fl rho rho) e v c ->
        bstep_e rho (Efun fl e) v c
  | BStep_prim_val :
    forall (rho' rho : env) (x : var) (p : primitive_value)
             (e : exp) (v : val) (c : nat),
        M.set x (Vprim p) rho = rho' ->
        bstep_e rho' e v c ->
        bstep_e rho (Eprim_val x p e) v c
  | BStep_prim :
      forall (vs : list val) (rho' rho : env) (x : var) (f : prim)
             (f' : list val -> option val) (ys : list var) (e : exp)
             (v v' : val) (c : nat),
        get_list ys rho = Some vs ->
        M.get f pr = Some f' ->
        f' vs = Some v ->
        M.set x v rho = rho' ->
        bstep_e rho' e v' c ->
        bstep_e rho (Eprim x f ys e) v' c
  | BStep_halt :
      forall x v rho,
        M.get x rho = Some v ->
        bstep_e rho (Ehalt x) v 0.



  (** Big step semantics with a more precise cost model.
   * The goal is that the number of machine instructions that
   * correspond to each rule is proportional to the assigned cost. *)
  Inductive bstep_cost :  env -> exp -> val -> nat -> Prop :=
  | BStepc_constr :
      forall (x : var) (t : ctor_tag) (ys :list var) (e : exp)
             (rho rho' : env) (vs : list val) (v : val) (c : nat),
        get_list ys rho = Some vs ->
        M.set x (Vconstr t vs) rho = rho' ->
        bstep_cost rho' e v c ->
        bstep_cost rho (Econstr x t ys e) v (c + 1 + (List.length ys))
  | BStepc_proj :
      forall (t : ctor_tag) (vs : list val)
             (rho : env) (x : var) (n : N) (y : var)
             (e : exp) (v v': val) (c : nat),
        M.get y rho = Some (Vconstr t vs) ->
        (* The number of instructions generated here should be
         * independent of n. We just need to add an offset *)
        nthN vs n = Some v ->
        bstep_cost (M.set x v rho) e v' c ->
        bstep_cost rho (Eproj x t n y e) v' (c + 1)
  | BStepc_case :
      forall (y : var) (v : val) (e : exp) (t : ctor_tag) (cl : list (ctor_tag * exp))
             (vl : list val) (rho : env) (n c : nat),
        M.get y rho = Some (Vconstr t vl) ->
        caseConsistent cenv cl t ->
        find_tag_nth cl t e n ->
        bstep_cost rho e v c ->
        bstep_cost rho (Ecase y cl) v (c + n)
  | BStepc_app :
      forall (rho' : env) (fl : fundefs) (f' : var) (vs : list val)
             (xs : list var) (e : exp) (rho'' rho : env) (f : var)
             (t : ctor_tag) (ys : list var) (v : val) (c : nat),
        M.get f rho = Some (Vfun rho' fl f') ->
        get_list ys rho = Some vs ->
        (* The number of instructions generated here should be
         * independent of the size of B. We just need to
         * jump to a label *)
        find_def f' fl = Some (t,xs,e) ->
        set_lists xs vs (def_funs fl fl rho' rho') = Some rho'' ->
        bstep_cost rho'' e v c ->
        bstep_cost rho (Eapp f t ys) v (c + 1 + List.length ys)
  | BStepc_letapp :
      forall (rho' : env) (fl : fundefs) (f' : var) (vs : list val)
             (xs : list var) (e_body e : exp) (rho'' rho : env) (x f : var)
             (t : ctor_tag) (ys : list var) (v v' : val) (c c' : nat),
        (* evaluate application *)
        M.get f rho = Some (Vfun rho' fl f') ->
        get_list ys rho = Some vs ->
        find_def f' fl = Some (t,xs,e_body) ->
        set_lists xs vs (def_funs fl fl rho' rho') = Some rho'' ->
        bstep_cost rho'' e_body v c -> (* body evaluates to v *)
        (* evaluate let continuation *)
        bstep_cost (M.set x v rho) e v' c' ->
        bstep_cost rho (Eletapp x f t ys e) v' (c + c' + 1 + List.length ys)  (* force equality on [t] *)
  | BStepc_fun :
      forall (rho : env) (B : fundefs) (e : exp) (v : val) (c : nat),
        bstep_cost (def_funs B B rho rho) e v c ->
        (* The definition of a function incur cost proportional to the number of FVs
           (to make the bound of the current cc independent of the term) *)
        (* TODO eventually remove the unit cost, it helps but it shouldn't be required *)
        bstep_cost rho (Efun B e) v (c + (1 + PS.cardinal (fundefs_fv B)))
  | BStepc_prim_val :
      forall (rho' rho : env) (x : var) (p : primitive_value)
             (e : exp)
             (v v' : val) (c : nat),
        M.set x (Vprim p) rho = rho' ->
        bstep_cost rho' e v' c ->
        bstep_cost rho (Eprim_val x p e) v' (c + 1)

  | BStepc_prim :
      forall (vs : list val) (rho' rho : env) (x : var) (f : prim)
             (f' : list val -> option val) (ys : list var) (e : exp)
             (v v' : val) (c : nat),
        get_list ys rho = Some vs ->
        M.get f pr = Some f' ->
        f' vs = Some v ->
        M.set x v rho = rho' ->
        bstep_cost rho' e v' c ->
        bstep_cost rho (Eprim x f ys e) v' (c + 1 + List.length ys)
  | BStepc_halt :
      forall x v rho,
        M.get x rho = Some v ->
        bstep_cost rho (Ehalt x) v 1.


  Lemma bstep_cost_deterministic e rho v1 v2 c1 c2 :
    bstep_cost rho e v1 c1 ->
    bstep_cost rho e v2 c2 ->
    v1 = v2 /\ c1 = c2.
  Proof.
    intros Heval1 Heval2.
    revert v2 c2 Heval2; induction Heval1; intros v2 c2 Heval2;
      inv Heval2; repeat subst_exp; eauto;
        try now edestruct IHHeval1 as [Heq1 Heq2]; eauto.
    + eapply find_tag_nth_deterministic in H7; [| clear H7; eauto ]; inv H7.
      eapply IHHeval1 in H10. inv H10. split; congruence.
    + eapply IHHeval1_1 in H15. inv H15.
      eapply IHHeval1_2 in H16. inv H16.
      split; congruence.
  Qed.


    Theorem bstep_f_sound:
    forall n rho e v,
      bstep_f rho e n = Ret (inr v) ->
      exists m, bstep_e rho e v m.
  Proof.
    induction n; intros. inv H.
    simpl in H.
    destruct e.
    - destruct (get_list l rho) eqn:glr; [| inv H].
      apply IHn in H. inv H.
      exists x. econstructor; eauto.
    - destruct (M.get v0 rho) eqn:gv0r.
      destruct v1. destruct (findtag l c) eqn:flc.
      destruct (caseConsistent_f cenv l c) eqn:clc.
      apply caseConsistent_c in clc.
      apply IHn in H. inv H. exists x.
      econstructor; eauto.
      inv H. inv H. inv H. inv H. inv H. inv H.
    - destruct (M.get v1 rho) eqn:gv1r; [|inv H].
      destruct v2; [ | inv H | inv H | inv H].
      destruct (c=?c0)%positive eqn:eqcc0; [| inv H].
      destruct (nthN l n0) eqn:nln0; [| inv H].
      apply IHn in H. inv H.
      apply Peqb_true_eq in eqcc0. subst.
      exists x. econstructor; eauto.
    - destruct (M.get v1 rho) eqn:gv0r; [| inv H].
      destruct v2; [inv H| | inv H | inv H].
      destruct (get_list l rho) eqn:glr; [| inv H].
      destruct (find_def v2 f0) eqn:gv1f0; [| inv H].
      destruct p. destruct p.
      destruct (f =? f1)%positive eqn:ff1; [| inv H].
      apply Peqb_true_eq in ff1. subst.
      simpl in H.
      destruct (set_lists l1 l0 (def_funs f0 f0 t t)) eqn:ll0; [| inv H].
      simpl in H.
      destruct (bstep_f t0 e0 n) as [ exc | [ oot | v' ] ] eqn:Heval; simpl.
      + simpl in H. congruence.
      + simpl in H. congruence.
      + simpl in H.
        apply IHn in H. inv H.
        apply IHn in Heval. inv Heval.
        eexists. eapply BStep_letapp; try eassumption.
    - apply IHn in H. inv H.
      exists x.
      constructor;
        auto.
    - destruct (M.get v0 rho) eqn:gv0r; [| inv H].
      destruct v1; [inv H| | inv H | inv H].
      destruct (get_list l rho) eqn:glr; [| inv H].
      destruct (find_def v1 f0) eqn:gv1f0; [| inv H].
      destruct p. destruct p.
      destruct (f =? f1)%positive eqn:ff1; [| inv H].
      apply Peqb_true_eq in ff1. subst. simpl in *.
      destruct (set_lists l1 l0 (def_funs f0 f0 t t)) eqn:ll0; [| inv H].
      simpl in H.
      apply IHn in H. inv H. exists (x+1)%nat.
      econstructor; eauto.
    - simpl in H. apply IHn in H.
      destruct H as [m ev]; exists m.
      simpl. cbn. econstructor; eauto.
    - destruct (get_list l rho) eqn:glr; [| inv H].
      destruct (M.get p pr) eqn:ppr; [| inv H].
      destruct (o l0) eqn:ol0; [| inv H].
      simpl in H. rewrite ol0 in H. simpl in H.
      apply IHn in H. inv H. exists x.
      econstructor; eauto.
      rewrite ol0 in H1. simpl in H1. inv H1.
    - destruct (M.get v0 rho) eqn:gv0r.
      inv H.
      exists 0%nat. constructor; auto.
      inv H.
  Qed.

    Theorem bstep_step_corresp:
    forall n rho e v rho' e',
      step (rho, e) (rho', e') ->
      bstep_e rho e v n ->
      exists n', bstep_e rho' e' v n'.
  Proof.
    intros. inversion H; subst.
    - inversion H0; subst. exists n.
      rewrite H2 in H9. inv H9; auto.
    - inv H0. rewrite H4 in H11. inv H11.
      rewrite H12 in H6. inv H6.
      exists n; auto.
    - inv H0. rewrite H5 in H3. inv H3.
      rewrite H9 in H7; inv H7.
      exists n; auto.
    - inversion H0; subst. eauto.
    - inv H0. rewrite H5 in H4; inv H4.
      rewrite H11 in H7; inv H7.
      rewrite H6 in H9; inv H9.
      rewrite H8 in H14; inv H14.
      eauto.
    - inv H0. rewrite H5 in H8; inv H8.
      rewrite H6 in H10; inv H10.
      rewrite H13 in H7; inv H7.
      eauto.
  Qed.

  Theorem step_pre_bstep_corresp:
    forall n rho e v rho' e',
      step (rho, e) (rho', e') ->
      bstep_e rho' e' v n ->
      exists n', bstep_e rho e v n'.
  Proof.
    intros. inversion H; subst; try solve [eexists; econstructor; eauto].
  Qed.

  (** Correspondence of the two small step semantics definitions *)
  (*  Lemma sstep_f_complete:
    forall (rho : env) (e : exp) (rho':env) (e':exp),  step (rho,e) (rho', e') -> sstep_f rho e = Ret (rho', e').
  Proof.
    intros rho e rho' e' H;
    inv H; simpl;
    repeat match goal with
             | H: ?A = Some _ |- context [ l_opt ?A] => rewrite H; simpl; clear H
             | H: ?A= _ |- match ?A with _ => _ end = _ => rewrite H
             | [ |- context [(?A =? ?A)%positive]] => rewrite Pos.eqb_refl
           end; auto.
    apply caseConsistent_c in H5. rewrite H5. auto.
  Qed.


  Theorem sstep_f_sound:
    forall (rho : env) (e : exp) (rho':env) (e':exp), sstep_f rho e = Ret (rho', e') -> step (rho,e) (rho', e').
  Proof.
    intros rho e rho' e' H.
    destruct e; simpl in H;
    repeat
      match goal with
        | H: match ?A with _ => _ end = Ret _ |- _ => destruct A eqn:?; inv H
        | H: exceptionMonad.bind ?A _ = Ret _ |- _ => destruct A eqn:?; try (solve [inv H]); simpl in H
        | H: l_opt ?A _ = Ret _ |- _ => destruct A eqn:?; try (solve [inv H]); simpl in H
        | H: Some _ = Some _ |- _ => inv H
        | H: Ret _ = Ret _ |- _ => inv H
        | H : (_ =? _)%positive = true |- _ => apply Peqb_true_eq in H; subst
      end;
    try solve [econstructor; eauto].
    - apply caseConsistent_c in Heqb.
      econstructor; eauto.
    - inv H.
  Qed.


   *)

  (** Reflexive transitive closure of the small-step relation *)
  Definition mstep : relation state := clos_refl_trans_1n state step.

  (** The evalutation semantics is deterministic *)
  Lemma bstep_e_deterministic e rho v1 v2 c1 c2 :
    bstep_e rho e v1 c1 ->
    bstep_e rho e v2 c2 ->
    v1 = v2 /\ c1 = c2.
  Proof.
    intros Heval1 Heval2.
    revert v2 c2 Heval2; induction Heval1; intros v2 c2 Heval2;
      inv Heval2; repeat subst_exp; eauto.
    split; f_equal; eapply IHHeval1; eauto.

    eapply IHHeval1_1 in H15. inv H15.
    eapply IHHeval1_2 in H16. inv H16.
    split; congruence.
  Qed.

  Lemma step_deterministic:
    forall s s' s'',
      step s s' -> step s s'' -> s' = s''.
  Proof.
    intros.
    inversion H; inversion H0; subst;
      repeat match goal with
             | [ |- ?P = ?P] => reflexivity
             | [H: ( Some _ = Some _ ) |- _ ] => inversion H; subst
             | [H1: (?P = Some _), H2:(?P = Some _) |- _ ] => rewrite H1 in H2;
                                                                inversion H2; subst
             | [H: ((?rho0, _) = (?rho, _)) |- _ ] => inversion H; subst
             end;
      try now (repeat subst_exp; reflexivity).
  Qed.

  Lemma step_confluent :
    forall s sv1 sv2,
      mstep s sv1 -> mstep s sv2 ->
      (exists s', mstep sv1 s' /\ mstep sv2 s').
  Proof.
    intros s sv1 sv2 Hs1. revert sv2. induction Hs1.
    - intros z Hs.
      eexists. split. eassumption. now constructor.
    - intros s2 Hs2.
      inv Hs2.
      + eexists z. split; [ now constructor |].
        econstructor 2; eassumption.
      + assert (Heq : y = y0) by (eapply step_deterministic; eassumption).
        subst. apply IHHs1.  eassumption.
  Qed.

  (* proof of equivalence of small and big step semantics *)
  Lemma bstep_then_mstep:
    forall rho e v n,
      bstep_e rho e v n ->
      exists rho' x,
        mstep (rho, e) (rho', Ehalt x) /\ M.get x rho' = Some v.
  Proof.
    (* intros. induction H. *)
    (* - destruct IHbstep_e. destruct H2. destruct H2. *)
    (*   exists x0, x1. split. econstructor 2. constructor; eauto. rewrite H0. *)
    (*   apply H2. auto. *)
    (* - destruct IHbstep_e. destruct H2. inv H2. exists x0, x1. *)
    (*   exists x0, x1. split; auto. *)
    (*   econstructor 2. econstructor; eauto. auto. *)
    (* - exists rho, x. *)
    (*   split; auto. *)
    (*   constructor. *)
  Abort.

  Lemma mstep_then_bstep:
    forall s s',
      mstep s s' ->
      forall v,
        halt_state s' v ->
        exists n, bstep_e (fst s) (snd s) v n.
  Proof.
    intros s s' H.
    induction H; intros.
    - inv H. exists 0%nat; simpl.
      constructor; auto.
    - apply IHclos_refl_trans_1n in H1.
      destruct H1.
      destruct x; destruct y; simpl in *.
      eapply step_pre_bstep_corresp; eauto.
  Qed.

  Theorem bstep_mstep_equiv:
    forall s v,
      (exists s', mstep s s' /\ halt_state s' v) <-> (exists n, bstep_e (fst s) (snd s) v n).
  Proof.
    intros. split; intros.
    - do 2 (destruct H).
      eapply mstep_then_bstep; eauto.
    - destruct H. destruct s. simpl in H.
      (* apply bstep_then_mstep in H. do 3 (destruct H). *)
      (* exists (x0, Ehalt x1). split; auto. *)
      (* constructor; auto. *)
  Abort.

End EVAL.


Ltac destruct_bstep :=
  match goal with
  | [ H : bstep _ _ _ _ _ |- _ ] => inv H
  end.
