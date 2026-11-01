From Stdlib Require Import Unicode.Utf8 List Classes.Morphisms.
Require Import MetaRocq.Utils.bytestring.
From ExtLib Require Import Monads.

Import MonadNotation ListNotations.

Open Scope monad.

Unset Universe Polymorphism.

Fixpoint mapM {M : Type -> Type} {A B : Type} `{Monad M} (f : A -> M B)
         (l : list A)  : M (list B) :=
  match l with
  | [] => ret []
  | x :: xs =>
    let sx' := f x in
    x' <- sx';;
    xs' <- mapM f xs ;;
    ret (x' :: xs')
  end.

Fixpoint sequence {M : Type -> Type} {A : Type} `{Monad M}
         (l : list (M A))  : M (list A) :=
  match l with
  | [] => ret []
  | x :: xs =>
    x' <- x ;;
    xs' <- sequence xs ;;
    ret (x' :: xs')
  end.


(** * A <<Compilation Monad>>. *)
(** Used to compose the pipeline, by threading through the state, compilation
  * options, errors *)
(** Used in LambdaANF for stateful transformations that require a state for (e.g.,) fresh names,
  * environment information, etc. *)

Section CompM.

  Inductive error (A : Type) : Type :=
    Err : string -> error A | Ret : A -> error A.

  Global Arguments Err {_} _.
  Global Arguments Ret {_} _.

  Global Instance MonadError : Monad error.
  Proof.
    constructor.
    - (* ret *)
      intros T t. exact (Ret t).

    - (* bind *)
      intros T U [s | r] m2.
      exact (Err s).
      exact (m2 r).
  Defined.

  (* A transformers for the error monad *)
  Section Trans.

    Context (M : Type -> Type)
            {HM : Monad M}.

    Definition errorT A := M (error A).

    Global Instance MonadErrorT : Monad errorT :=
      { ret A x := ret (Ret x);
        bind A B m f :=
          @bind M HM (error A) (error B) m (fun r =>
           match r with
           | Err s => @ret M HM _ (Err s)
           | Ret a => f a
           end)
      }.

    Global Instance MonadT_errorT : MonadT errorT M :=
      { lift := (fun (A : Type) (m : M A) => @liftM M HM _ _ (@ret error _ _) m) }.

  End Trans.

  Variable (R W : Type).

  (* A state monad with a readable and a writable component *)
  (* Should be equivalent to (writerT R) (state W) *)

  Record state (A : Type) : Type := State { runState : R -> W -> A * W }.

  Global Instance MonadState : Monad state  :=
    { ret A x := State A (fun r w  => (x, w));
      bind A B m f :=
        State B (fun r w => let (a, w') := runState A m r w in
                         runState B (f a) r w')
    }.

  (* Compilation effect : A stateful computation with a state that has a
     writable and a readable component and can raise an error *)

  Definition compM := errorT state.

  (* Actions *)

  Definition get : compM W := State _ (fun r w => (Ret w, w)).

  Definition put (w : W) : compM unit := State _ (fun r _ => (Ret tt, w)).

  Definition failwith {A : Type} (s : string) : compM A :=
    State _ (fun r w => (Err s, w)).

  Definition ask : compM R := State _ (fun r w => (Ret r, w)).

  Definition local {A} (f : R -> R) (m : compM A) : compM A :=
    State _ (fun r w => runState _ m (f r) w).

End CompM.


Global Arguments State {_ _ _} _.

Global Arguments runState {_ _ _} _ _.

Global Arguments put {_ _} _.

Global Arguments get {_ _}.

Global Arguments failwith {_ _ _} _.

Global Arguments ask {_ _}.

Section Hoare.

  (* Reasoning about computations *)

  Definition triple {R W A} (pre :  R -> W -> Prop) (m : compM R W A)
             (post : R -> W -> A -> W -> Prop) : Prop :=
    forall r w,
      pre r w ->
      let '(x, w') := runState m r w in
      match x with
      | Err _ => False (* The hoare triple holds if an error is *not* raise. If
                     this ends up beinf too string we can change to False *)
      | Ret x => post r w x w'
      end.

  (* Relational reasoning about computations, useful to express linking properties *)
  Definition bitriple {R W A} (pre : (R * W) -> (R * W) -> Prop) (m1 m2 : compM R W A)
             (post : (R * W * W) -> (R * W * W) -> A -> A -> Prop) : Prop :=
    forall r1 w1 r2 w2,
      pre (r1, w1) (r2, w2) ->
      let '(x1, w1') := runState m1 r1 w1 in
      let '(x2, w2') := runState m2 r2 w2 in
      match x1, x2 with
      | Err _, Err _ => True
      | Ret x1, Ret x2 => post (r1, w1, w1') (r2, w2, w2') x1 x2
      | _ , _ => False
      end.

  Notation "{{ p }} e {{ q }}" :=
    (triple p e q) (at level 90, e at next level).

  Notation "{{{ p }}} e1 | e2 {{{ q }}}" :=
    (bitriple p e1 e2 q) (at level 90, e1 at next level, e2 at next level).


  (* Extensional equality *)
  Definition st_eq {R W A} (m1 m2 : compM R W A) :=
    forall r w, runState m1 r w = runState m2 r w.

  (* Triple respects extensional equality on computations *)
  Global Instance triple_Proper {R W A} : Proper (Logic.eq ==> st_eq ==> Logic.eq ==> iff) (@triple R W A).
  Proof.
    intros P1 P2 Heq1 m1 m2 Hfeq P3 P4 Heq2; subst; split; intros H.
    - intros s HP2. rewrite <- Hfeq. eapply H.
    - intros s HP2. rewrite  Hfeq. eapply H.
  Qed.

  Global Instance bind_Proper_l {R W A B} : Proper (st_eq ==> Logic.eq ==> st_eq)
                                                   (@bind (compM R W) _ A B).
  Proof.
    intros [m1] [m2] Hfeq f1 f2 Heq r w; subst.
    unfold st_eq, runState, bind in *. simpl.
    rewrite Hfeq. reflexivity.
  Qed.

  Global Instance bind_Proper_r {R W A B} :
    Proper (Logic.eq ==> (fun f1 f2 => forall x, st_eq (f1 x) (f2 x)) ==> st_eq) (@bind (compM R W) _ A B).
  Proof.
    intros m1 [fm2] Hfeq f1 f2 Heq m; subst; intros s.
    unfold st_eq in Heq. simpl. destruct (fm2 m s), e; auto.
  Qed.

  Lemma st_eq_transitive {R W A} (m1 m2 m3 : compM R W A) :
    st_eq m1 m2 -> st_eq m2 m3 -> st_eq m1 m3.
  Proof.
    intros Hs1 Hs2 r w. congruence.
  Qed.

  Global Instance st_eq_Proper_l {R W A} : Proper (st_eq ==> Logic.eq ==> iff) (@st_eq R W A).
  Proof.
    intros m1 m2 Heq1 m3 m4 Heq2; subst; split; intros; congruence.
  Qed.

  Global Instance st_eq_Proper_r {R W A} : Proper (Logic.eq ==> st_eq ==> iff) (@st_eq R W A).
  Proof.
    intros m1 m2 Heq1 m3 m4 Heq2; subst; split; intros; congruence.
  Qed.

  (** * Monad Laws *)

  Lemma left_id {R W A B} (x : A) (f : A -> compM R W B) :
    st_eq (bind (ret x) f) (f x).
  Proof.
    intros m1. reflexivity.
  Qed.

  Lemma right_id {R W A} : forall (m : compM R W A), st_eq (bind m ret) m.
  Proof.
    intros m. unfold st_eq. intros r w. destruct m. simpl.
    destruct (runState0 r w), e; reflexivity.
  Qed.

  Lemma assoc {R W A B C} : forall (m : compM R W A) (f : A -> compM R W B)  (g : B -> compM R W C),
      st_eq (bind (bind m f) g) (bind m (fun x => bind (f x) g)).
  Proof.
    intros [fm] f g.
    unfold st_eq. intros r w. simpl.
    destruct (fm r w), e; try reflexivity.
  Qed.

  (** * Useful lemmas about triples *)

  Context {R W : Type}.

  Definition Pre := R -> W -> Prop.
  Definition Post A := R -> W -> A -> W -> Prop.

  Definition BiPre := (R * W) -> (R * W) -> Prop.
  Definition BiPost A := (R * W * W) -> (R * W * W) -> A -> A -> Prop.

  Ltac destruct_compM :=
    let e := fresh "e" in
    let p := fresh "p" in
    destruct (runState _ _ _) as [e p]; destruct e.

  Ltac destruct_compM_eqn eqn :=
    let e := fresh "e" in
    let p := fresh "p" in
    destruct (runState _ _ _) as [e p] eqn:eqn; destruct e.

  Lemma pre_strenghtening {A} (P P' : Pre) (Q : Post A) e :
    (forall st s, P' st s -> P st s) ->
    {{ P }} e {{ Q }} ->
    {{ P' }} e {{ Q }}.
  Proof.
    intros H. unfold triple. intros; eauto. eapply H0. eauto.
  Qed.

  Lemma post_weakening {A} (P : Pre) (Q Q' : Post A) e :
    (forall r w x w', P r w -> Q r w x w' -> Q' r w x w') ->
    {{ P }} e {{ Q }} ->
    {{ P }} e {{ Q' }}.
  Proof.
    intros H. unfold triple. intros Hyp r w HP.
    specialize (Hyp r w HP). destruct_compM; eauto.
  Qed.

  Lemma triple_consequence : forall {A} (P P' : Pre) (Q Q' : Post A) (e : compM R W A),
    {{P}} e {{Q}} ->
    (forall r w, P' r w -> P r w) ->
    (forall r w x w', P r w -> Q r w x w' -> Q' r w x w' ) ->
    {{P'}} e {{Q'}}.
  Proof. intros. eapply pre_strenghtening; [|eapply post_weakening]; eauto. Qed.

  Lemma pre_eq_state_lr : forall {A} (P : Pre) (Q : Post A) (e : compM R W A),
    (forall r w, P r w ->
            {{fun r' w' => r = r' /\ w = w' }}
              e
            {{fun r' w' x w'' => r = r' /\ w = w' -> Q r' w' x w''}}) ->
    {{ P }} e {{ Q }}.
  Proof.
    unfold triple; intros.
    specialize (H r w H0 r w).
    destruct_compM; auto.
  Qed.

  Lemma pre_post_copy : forall {A} (P : Pre) (Q : Post A) (e : compM R W A),
    {{P}} e {{fun r w x w' => P r w /\ Q r w x w' }} <->
    {{P}} e {{Q}}.
  Proof.
    unfold triple; split; intros;
    specialize (H r w H0);
    destruct_compM_eqn Heq; try split; easy.
  Qed.

  Lemma pre_post_mp_l {A} (P : Pre) (Q : Post A) e :
    {{ fun r w => True }} e {{ fun r w x w' => P r w -> Q r w x w' }} ->
    {{ fun r w => P r w }} e {{ fun r w x w' => Q r w x w' }}.
  Proof.
    intros H.
    eapply post_weakening; [| eapply pre_strenghtening; [| eassumption ] ];
    simpl; eauto.
  Qed.

  Lemma pre_state_irrelevant {A} (Q : Post A) (P : Prop) (e : compM R W A) :
    (P -> {{ fun _ _ => True }} e {{ Q }}) ->
    {{ fun _ _ => P }} e {{ fun r w x w' => Q r w x w' }}.
  Proof.
    intros H. unfold triple in *; intros. specialize (H H0 r w).
    destruct_compM; auto.
  Qed.


  (* Works if triple is True on failure
     Lemma pre_post_mp_r {A} (P : Pre) (Q : Post A) e :
    {{ P }} e {{ fun r w x w' => Q r w x w' }} ->
    {{ fun r w => True }} e {{ fun r w x w' => P r w -> Q r w x w' }}.
  Proof.
    unfold triple.
    intros H r w HP'.
    specialize (H st s).
    destruct_compM; auto.
  Abort. *)

  Lemma pre_eq_state_l {A} (P : Pre) (Q : Post A) e :
    (forall r w, P r w -> {{ fun r' w' => r = r' /\ w = w' }} e {{ Q }}) ->
    {{ P }} e {{ Q }}.
  Proof.
    intros H st s HP. specialize (H st s HP).
    unfold triple in H. eapply H. auto.
  Qed.

  Lemma pre_eq_state_r {A} (P : Pre) (Q : Post A) e :
    {{ P }} e {{ Q }} ->
    (forall r w, P r w -> {{ fun r' w' => r = r' /\ w = w' }} e {{ Q }}).
  Proof.
    intros H st s HP.  intros st' s' [Hst Hs]; subst. eapply H; auto.
  Qed.

  Lemma post_eq_l {A} (P : Pre) (Q : Post A) e r w x wf :
    {{ P }} e {{ fun r' w' x' wf' => r = r' /\ w = w' /\ x = x' /\ wf = wf' }} ->
    Q r w x wf ->
    {{ P }} e {{ Q }}.
  Proof.
    intros H HQ st s HP. specialize (H st s HP).
    unfold triple in H. destruct_compM; auto.
    intuition; subst; auto.
  Qed.

  Lemma post_eq_r {A} (P : Pre) (Q : Post A) e r w x wf :
    {{ P }} e {{ Q }} ->
    {{ P }} e {{ fun r' w' x' wf' => r = r' /\ w = w' /\ x = x' /\ wf = wf' }} ->
    P r w ->
    Q r w x wf.
  Proof.
    intros H H' HP. specialize (H r w HP). specialize (H' r w HP).
    destruct_compM; [contradiction | intuition; subst; auto].
  Qed.

  Lemma post_conj {A} (P : Pre) (Q1 Q2 : Post A) e :
    {{ P }} e {{ Q1 }} ->
    {{ P }} e {{ Q2 }} ->
    {{ P }} e {{ fun r w x w' => Q1 r w x w' /\ Q2 r w x w' }}.
  Proof.
    unfold triple. intros.
    specialize (H r w); specialize (H0 r w).
    destruct_compM; auto.
  Qed.

  (* Needs true on failure *)
  (* Lemma post_trivial {A} (P : Pre)  (e : compM R W A) : *)
  (*   {{ P }} e {{ fun _ _ _ _ => True }}. *)
  (* Proof. *)
  (*   unfold triple. intros; destruct_compM; auto. *)
  (* Qed. *)

  Lemma frame_rule {A} (P : Pre) (Post : Post A) (P' : Pre) (e : compM R W A) :
    {{ P }} e {{ Post }} ->
    {{ fun r w => P' r w /\ P r w }} e {{ fun r w x w' => P' r w /\ Post r w x w' }}.
  Proof.
    unfold triple. intros.
    specialize (H r w). destruct_compM; intuition.
  Qed.

  Lemma frame_rule_trivial_pre {A} (Q : Post A) (P : Prop) (e : compM R W A) :
    (P -> {{ fun _ _ => True }} e {{ Q }}) ->
    {{ fun _ _ => P }} e {{ fun r w x w' => P /\ Q r w x w' }}.
  Proof.
    intros H. unfold triple in *; intros. specialize (H H0 r w).
    destruct_compM; auto.
  Qed.

  (* Lemma frame_rule_trivial {A} (P : Pre) (e : compM A) : *)
  (*   {{ P }} e {{ fun st s _ _ _ => P st s }}. *)
  (* Proof. *)
  (*   eapply post_weakening; [| eapply pre_strenghtening; *)
  (*                             [| eapply frame_rule with (P0 := (fun _ _ => True)); *)
  (*                                eapply post_trivial]]; simpl in *. *)
  (*   intros. destruct H0; eauto. *)
  (*   intros; eauto. *)
  (* Qed. *)

  Lemma pre_existential {A B} (P : B -> Pre) (Q : Post A) e :
    (forall b, {{ P b }} e {{ Q }}) ->
    ({{ fun st s => exists b, P b st s }} e {{ Q }}).
  Proof.
    intros Hb st s [b' Hre]. eapply Hb. eassumption.
  Qed.

  Lemma post_universal : forall {A B} (P : Pre) (Q : B -> Post A) (e : compM R W A),
    inhabited B ->
    (forall y : B, {{ P }} e {{ Q y }}) ->
    {{ P }} e {{ fun r w x w'  => forall y : B, Q y r w x w' }}.
  Proof.
    unfold triple; intros.
    destruct_compM_eqn Heq; eauto.
    destruct H.
    specialize (H0 X r w H1). rewrite Heq in H0. eassumption.

    intros y. specialize (H0 y r w H1). rewrite Heq in H0.
    eassumption.
  Qed.

  Lemma post_universal' : forall {A B} (P : Pre) (Q : Post A) (F : B -> Prop) (e : compM R W A),
    (∃ x, F x) ->
    (forall y : B, F y -> {{ P }} e {{ Q }}) ->
    {{ P }} e {{ fun r w x w' => forall y : B, F y -> Q r w x w' }}.
  Proof.
    unfold triple; intros.
    destruct_compM_eqn Heq. destruct H as [x Hf].
    specialize (H0 x Hf r w H1). rewrite Heq in H0; eauto.
    intros.
    specialize (H0 y H2 r w H1). rewrite Heq in H0; eauto.
  Qed.

  Lemma pre_curry_l {A} (P : Pre) (Q : Post A) (P' : Prop) e :
    (P' -> {{ P }} e {{ Q }}) ->
    {{ fun r w => P' /\ P r w }} e {{ Q }}.
  Proof.
    intros Hyp st s [Hpre HP]. eapply Hyp; eauto.
  Qed.

  Lemma pre_curry_r {A} (P : Pre) (Q : Post A) (P' : Prop) e :
    (P' -> {{ P }} e {{ Q }}) ->
    {{ fun st s => P st s /\ P' }} e {{ Q }}.
  Proof.
    intros Hyp st s [Hpre HP]. eapply Hyp; eauto.
  Qed.

  Lemma post_mp {A} (P : Pre) (Q Q' : Post A) (e : compM R W A) :
    {{ P }} e {{ Q' }} ->
    {{ P }} e {{ fun r w x w' => Q' r w x w' -> Q r w x w' }} ->
    {{ P }} e {{ Q }}.
  Proof.
    unfold triple.
    intros Ht1 Ht2 st s HPre. specialize (Ht1 st s HPre); specialize (Ht2 st s HPre).
    destruct_compM; auto.
  Qed.

  Lemma pre_transfer_r {A} (P : Pre) (Q : Post A) (e : compM R W A) :
    {{ P }} e {{ fun r w x w' => Q r w x w' }} ->
    {{ P }} e {{ fun r w x w' => P r w /\ Q r w x w' }}.
  Proof.
    intros.
    eapply pre_strenghtening with (P := fun st s => P st s /\ P st s).
    now firstorder. eapply frame_rule. eassumption.
  Qed.

  Lemma pre_strenghtening_true {A} (P : Pre) (Q : Post A) e :
    {{ fun _ _ => True }} e {{ Q }} ->
    {{ P }} e {{ Q }}.
  Proof.
    intros.
    eapply pre_strenghtening; [| eassumption ].
    now firstorder.
  Qed.

  Lemma triple_concretize {A} (P : Pre) (Q : Post A) e :
    {{ P }} e {{ Q }} ->
    forall (r1 : R) (w1 : W),
      P r1 w1 ->
      exists (x : A) (w2 : W),
        {{ fun r w => r1 = r /\ w1 = w }} e {{ fun r w x' w' => r = r1 /\ w = w1 /\ x' = x /\ w' = w2 }} /\
        Q r1 w1 x w2.
  Proof.
    intros H r1 w1 HP.
    unfold triple in *. specialize (H r1 w1 HP).
    destruct_compM_eqn Heq; auto. exfalso; eauto.
    do 2 eexists. split; eauto. intros r' w' [Heq1 Heq2]; subst.
    rewrite Heq. intuition.
  Qed.

  Lemma triple_concretize_read {A} (P : R -> Prop) Q e :
    {{ fun r w => P r }} e {{ fun r w x w' => Q r x }} ->
    forall (r1 : R) (w1 : W),
      P r1 ->
      exists (x : A) (w2 : W),
        {{ fun r w => r1 = r }} e {{ fun r w x' w' => r = r1 /\ x' = x /\ w' = w2 }} /\
        Q r1 x.
  Proof.
  (*   intros H r1 HP. *)
  (*   unfold triple in *. specialize (H r1 HP). *)
  (*   destruct_compM_eqn Heq; auto. exfalso; eauto. *)
  (*   do 2 eexists. split; eauto. intros r' w' Heq1; subst. *)

  (*   rewrite Heq. intuition. *)
  Abort.

  (** * Lemmas about monadic combinators *)

  Lemma return_triple {A} (x : A) (P : Pre) (Q : Post A) :
    (forall r w, P r w -> Q r w x w) ->
    {{ P }} (ret x) {{ Q }}.
  Proof.
    unfold triple. auto.
  Qed.

  Lemma bind_triple {A B} (m : compM R W A) (f : A -> compM R W B)
        (P : Pre) (Q : Post B) (Q' : Post A) :
    {{ P }} m {{ Q' }} ->
    (forall (x : A) w, {{ fun r w' => Q' r w x w' }} f x {{ fun r _ x' w' => Q r w x' w' }}) ->
    {{ P }} bind m f {{ Q }}.
  Proof.
    simpl. unfold triple; simpl.
    intros H1 H2 r w HP.

    (* pose (Hm := H1 st s HP). *)
    destruct m as [fm].
    unfold runState in *; simpl in *.
    destruct (fm r w) eqn:Heq_fm, e; auto.
    specialize (H1 r w HP). rewrite Heq_fm in H1. eassumption.
    specialize (H1 r w HP). rewrite Heq_fm in H1.
    eapply H2. eassumption.
  Qed.

  Lemma bind_triple' : forall {A B} (m : compM R W A) (f : A -> compM R W B) (P : Pre)
    (Q : Post B) (Q' : Post A),
    {{P}} m {{fun r w x w' => P r w /\ Q' r w x w' }} ->
    (forall (x : A) w, {{fun r w' => P r w /\ Q' r w x w' }} f x {{fun r _ => Q r w}}) ->
    {{P}} bind m f {{Q}}.
  Proof. intros; eapply bind_triple; eauto. Qed.

  Lemma bind_triple'' {A B} (m : compM R W A) (f : A -> compM R W B)
        (P : Pre) (Q : Post B) (Q' : Post A) :
    (forall w x, {{ fun r => Q' r w x }} f x {{ fun r _ y w' => Q r w y w' }}) ->
    {{ P }} m {{ Q' }} ->
    {{ P }} bind m f {{ Q }}.
  Proof. intros; eapply bind_triple; eauto. Qed.

  Lemma get_triple : {{ fun (_ : R) (_ : W) => True }} get {{ fun r w x w' => x = w /\ w = w' }}.
  Proof. unfold triple; intros. simpl. eauto. Qed.

  Lemma put_triple x : {{ fun (_ : R) (_ : W) => True }} put x {{ fun _ _ _ w' => x = w' }}.
  Proof. unfold triple; intros. reflexivity. Qed.

  Lemma sequence_triple {A} (P : Pre) (P' : A -> Prop) (l : list (compM R W A)) :
    Forall (fun e => {{ P }} e {{ fun  r _ e' w' => P' e' /\ P r w' }}) l ->
    {{ P }} sequence l {{fun r _ l' w' => Forall P' l' /\ P r w' }}.
  Proof.
    induction l; intros Hall.
    - inversion Hall. apply return_triple.
      intros i Hp. split; eauto.
    - inversion Hall; subst. eapply bind_triple.
      eassumption.
      intros x w. eapply bind_triple.
      eapply frame_rule. eapply IHl; eassumption.
      intros x' w'. eapply return_triple.
      intros r w'' [HP [Hall' Hpre]]. split; eauto.
  Qed.

  Lemma map_sequence_triple {A} (P : Pre) (P' : A -> A -> Prop) (f : A -> compM R W A) (l : list A) :
    Forall (fun e => {{ P }} f e {{ fun r _ e' w' => P' e e' /\ P r w' }}) l ->
    {{ P }} sequence (map f l) {{fun r _ l' w' => Forall2 P' l l' /\ P r w' }}.
  Proof.
    induction l; intros Hall.
    - inversion Hall. apply return_triple.
      intros i Hp. split; eauto.
    - inversion Hall; subst. eapply bind_triple.
      eassumption.
      intros x w. eapply bind_triple.
      eapply frame_rule. eapply IHl; eassumption.
      intros x' w'. eapply return_triple.
      intros r w'' [HP [Hall' Hpre]]. split; eauto.
  Qed.

  (* TODO move in appropriate LambdaANF file *)
  (* Definition from_maxvar v := fun a => (a < v)%positive. *)
  (* Definition from_fresh st := from_maxvar (next_var st). *)


  (** * Lemmas about bitriples *)

  Lemma bitriple_pre_eq_state_l {A} (P : BiPre) (Q : BiPost A) e1 e2 :
    (forall s1 s2, P s1 s2 -> {{{ fun s1' s2' => s1' = s1 /\ s2' = s2 }}} e1 | e2 {{{ Q }}}) ->
    {{{ P }}} e1 | e2 {{{ Q }}}.
  Proof.
    intros H r1 w1 r2 w2 HP. specialize (H (r1, w1) (r2, w2) HP).
    unfold bitriple in H.
    eapply H. split; reflexivity.
  Qed.

  Lemma triple_to_bitriple {A} (Q : BiPost A)
        (m1 m2 : compM R W A) (r1 r2 : R) (w1 w1' w2 w2' : W) res1 res2 :
    {{ fun r1i w1i => (r1i, w1i) = (r1, w1) }}
      m1
    {{ fun r1i w1i e1 w1i' => (r1i, w1i, w1i') = (r1, w1, w1') /\ e1 = res1 }} ->
    {{ fun r2i w2i => (r2i, w2i) = (r2, w2) }}
      m2
    {{ fun r2i w2i e2 w2i' => (r2i, w2i, w2i') = (r2, w2, w2') /\ e2 = res2 }} ->
    Q (r1, w1, w1') (r2, w2, w2') res1 res2 ->
    {{{ fun s1 s2 => s1 = (r1, w1) /\ s2 = (r2, w2) }}} m1 | m2 {{{ fun s1' s2' r1 r2 => Q s1' s2' r1 r2 }}}.
  Proof.
    intros H1 H2 Hyp.
    unfold triple, bitriple in *.
    intros r1i w1i r2i w2i [Heq1 Heq2]; inversion Heq1; inversion Heq2; subst.
    specialize (H1 r1 w1 ltac:(reflexivity)).
    specialize (H2 r2 w2 ltac:(reflexivity)).
    destruct_compM; eauto.
    destruct_compM; eauto.
    destruct_compM; eauto.
    inversion H1; subst.
    inversion H2; subst. congruence.
  Qed.



  Opaque triple bitriple bind ret.

End Hoare.

Notation "{{ p }} e {{ q }}" :=
  (triple p e q) (at level 90, e at next level).


Notation "{{{ p }}} e1 | e2 {{{ q }}}" :=
  (bitriple p e1 e2 q) (at level 90, e1 at next level, e2 at next level).
