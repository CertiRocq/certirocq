(* Facts about the functions of [LambdaANF_to_C] that do not involve execution: lists of
   variables, the layout of the roots, the layout of a switch, and the analyses. *)

From Stdlib Require Import ZArith.ZArith Lists.List SetoidList Bool.Bool micromega.Lia
     Sorting.Permutation.
From compcert Require Import lib.Coqlib lib.Maps lib.Integers common.AST
     cfrontend.Ctypes cfrontend.Clight.
From CertiRocq.Common Require Import compM Pipeline_utils.
From CertiRocq.LambdaANF Require Import Ensembles_util set_util List_util term term_util
     identifiers.
From CertiRocq.Codegen Require Import LambdaANF_to_C.

Import ListNotations.

(** * Lists of variables *)

Lemma in_list_In x l : in_list x l = true <-> In x l.
Proof.
  unfold in_list. rewrite existsb_exists. split.
  - intros (y & Hy & Heq). apply Pos.eqb_eq in Heq. subst. auto.
  - intros H. exists x. split; auto. apply Pos.eqb_refl.
Qed.

Lemma in_list_not_In x l : in_list x l = false <-> ~ In x l.
Proof.
  rewrite <- in_list_In. destruct (in_list x l); split; congruence.
Qed.

Lemma index_of_nth x : forall l j, index_of x l = Some j -> nth_error l j = Some x.
Proof.
  induction l as [| y l IH]; simpl; intros j H; [discriminate |].
  destruct (Pos.eqb x y) eqn:Heq.
  - inv H. apply Pos.eqb_eq in Heq. subst. reflexivity.
  - destruct (index_of x l) as [j' |]; simpl in H; inv H. simpl. auto.
Qed.

Lemma index_of_In x : forall l, In x l -> exists j, index_of x l = Some j.
Proof.
  induction l as [| y l IH]; simpl; intros H; [contradiction |].
  destruct (Pos.eqb x y) eqn:Heq; eauto.
  destruct H as [-> | H]; [rewrite Pos.eqb_refl in Heq; discriminate |].
  destruct (IH H) as [j Hj]. rewrite Hj. simpl. eauto.
Qed.

Lemma nth_error_NoDup {A} (l : list A) i j x :
  NoDup l -> nth_error l i = Some x -> nth_error l j = Some x -> i = j.
Proof.
  intros Hnd Hi Hj. rewrite NoDup_nth_error in Hnd. apply Hnd; [| congruence].
  apply nth_error_Some. congruence.
Qed.

Lemma Forall2_firstn {A B} (R : A -> B -> Prop) : forall k l1 l2,
    Forall2 R l1 l2 -> Forall2 R (firstn k l1) (firstn k l2).
Proof.
  induction k as [| k IH]; intros l1 l2 H; [constructor |].
  destruct H; simpl; constructor; auto.
Qed.

Lemma Forall2_skipn {A B} (R : A -> B -> Prop) : forall k l1 l2,
    Forall2 R l1 l2 -> Forall2 R (skipn k l1) (skipn k l2).
Proof.
  induction k as [| k IH]; intros l1 l2 H; [exact H |].
  destruct H as [| x y l1 l2 Hxy Hl]; simpl; [constructor | apply IH; exact Hl].
Qed.

Lemma Forall_firstn {A} (P : A -> Prop) : forall k l, Forall P l -> Forall P (firstn k l).
Proof.
  induction k as [| k IH]; intros l H; [constructor |].
  destruct H; simpl; constructor; auto.
Qed.

Lemma Forall_skipn {A} (P : A -> Prop) : forall k l, Forall P l -> Forall P (skipn k l).
Proof.
  induction k as [| k IH]; intros l H; [exact H |].
  destruct H as [| x l Hx Hl]; simpl; [constructor | apply IH; exact Hl].
Qed.

Lemma NoDup_norepet {A} (l : list A) : NoDup l -> list_norepet l.
Proof. induction 1; constructor; auto. Qed.

Lemma skipn_In {A} (x : A) k l : In x (skipn k l) -> In x l.
Proof.
  intros H. rewrite <- (firstn_skipn k l). apply in_or_app. now right.
Qed.

Lemma NoDup_firstn_skipn {A} (x : A) : forall k l,
    NoDup l -> In x (firstn k l) -> In x (skipn k l) -> False.
Proof.
  induction k as [| k IH]; intros l Hnd H1 H2; [contradiction |].
  destruct l as [| a l]; [contradiction |]. inversion Hnd as [| ? ? Ha Hnd']; subst.
  simpl in H1, H2. destruct H1 as [-> | H1].
  - apply Ha. eapply skipn_In. exact H2.
  - eapply IH; eauto.
Qed.

Lemma firstn_In {A} (x : A) : forall k l, In x (firstn k l) -> In x l.
Proof.
  induction k; intros l H; [contradiction |].
  destruct l; simpl in *; [contradiction |]. destruct H; auto.
Qed.

Lemma NoDup_firstn {A} : forall k (l : list A), NoDup l -> NoDup (firstn k l).
Proof.
  induction k; intros l H; [constructor |].
  destruct l; simpl; [constructor |]. inv H. constructor; auto.
  intros Hin. apply firstn_In in Hin. contradiction.
Qed.

Lemma filter_length_le {A} (f : A -> bool) l : (length (List.filter f l) <= length l)%nat.
Proof. induction l; simpl; [lia | destruct (f a); simpl; lia]. Qed.

Lemma filter_partition_length {A} (f : A -> bool) l :
  (length (List.filter f l) + length (List.filter (fun x => negb (f x)) l) = length l)%nat.
Proof. induction l; simpl; [lia | destruct (f a); simpl; lia]. Qed.

(* Two lists without duplicates and with the same elements have the same length *)
Lemma NoDup_same_length {A} (l1 l2 : list A) :
  NoDup l1 -> NoDup l2 -> (forall x, In x l1 <-> In x l2) -> length l1 = length l2.
Proof.
  intros H1 H2 H. apply Permutation_length. apply NoDup_Permutation; auto.
Qed.

(* A list of witnesses for the elements of [l] *)
Lemma list_choice {A B} : forall (l : list A) (R : nat -> A -> B -> Prop),
    (forall j a, nth_error l j = Some a -> exists b, R j a b) ->
    exists l', length l' = length l /\
               forall j a b, nth_error l j = Some a -> nth_error l' j = Some b -> R j a b.
Proof.
  induction l as [| a l IH]; intros R H.
  - exists []. split; auto. intros j a b Hj. destruct j; discriminate.
  - destruct (H 0%nat a eq_refl) as [b Hb].
    destruct (IH (fun j => R (S j))) as (l' & Hlen & Hl').
    { intros j a' Hj. apply (H (S j)). exact Hj. }
    exists (b :: l'). split; [simpl; congruence |].
    intros j a' b' Hj Hj'. destruct j; simpl in *.
    + inv Hj. inv Hj'. auto.
    + eauto.
Qed.

(** * The layout of the roots *)

Section Place.

  Context (live : var -> bool).

  (* The variables of the first [k] positions of [old] that stay in place *)
  Definition kept (k : nat) (old : list var) : list var := List.filter live (firstn k old).

  Lemma kept_length k old : (length (kept k old) <= k)%nat.
  Proof.
    unfold kept. etransitivity; [apply filter_length_le |]. apply firstn_le_length.
  Qed.

  Lemma place_length : forall k old new,
      (k - length (kept k old) <= length new)%nat ->
      length (place k old new live) = k.
  Proof.
    induction k as [| k IH]; intros old new H; [reflexivity |].
    destruct old as [| x old]; simpl in *.
    - destruct new as [| y new]; simpl in *; [lia |]. f_equal. apply IH.
      unfold kept. rewrite firstn_nil. simpl. lia.
    - unfold kept in H. simpl in H. destruct (live x) eqn:Hx; simpl in *.
      + f_equal. apply IH. unfold kept. lia.
      + pose proof (kept_length k old). unfold kept in *.
        destruct new as [| y new]; simpl in *; [lia |]. f_equal. apply IH. unfold kept. lia.
  Qed.

  (* A live variable in the first [k] positions keeps its position *)
  Lemma place_kept : forall k old new p x,
      (k - length (kept k old) <= length new)%nat ->
      nth_error old p = Some x -> (p < k)%nat -> live x = true ->
      nth_error (place k old new live) p = Some x.
  Proof.
    induction k as [| k IH]; intros old new p x H Hp Hlt Hx; [lia |].
    destruct old as [| y old]; [destruct p; discriminate |].
    unfold kept in H. simpl in *. destruct (live y) eqn:Hy; simpl in H.
    - destruct p as [| p]; simpl in *; [congruence |].
      apply IH; auto; try (unfold kept in *; lia).
    - pose proof (kept_length k old). unfold kept in *.
      destruct new as [| z new]; simpl in H; [lia |].
      destruct p as [| p]; simpl in *; [congruence |].
      apply IH; auto; try (unfold kept in *; lia).
  Qed.

  Lemma place_In : forall k old new x,
      In x (place k old new live) -> In x (kept k old) \/ In x new.
  Proof.
    induction k as [| k IH]; intros old new x H; [contradiction |].
    destruct old as [| y old]; simpl in *.
    - destruct new as [| z new]; [contradiction |]. destruct H as [-> | H]; [right; now left |].
      destruct (IH _ _ _ H) as [Hk | Hn]; [| right; now right].
      unfold kept in Hk. rewrite firstn_nil in Hk. contradiction.
    - unfold kept. simpl. destruct (live y) eqn:Hy.
      + destruct H as [-> | H]; [left; now left |].
        destruct (IH _ _ _ H); [left; now right | now right].
      + destruct new as [| z new]; [contradiction |]. destruct H as [-> | H]; [right; now left |].
        destruct (IH _ _ _ H); [now left | right; now right].
  Qed.

  (* All of [new] is placed when it fills the free positions exactly *)
  Lemma place_new : forall k old new x,
      (length new <= k - length (kept k old))%nat ->
      In x new -> In x (place k old new live).
  Proof.
    induction k as [| k IH]; intros old new x H Hin.
    - destruct new; [contradiction | simpl in H; lia].
    - destruct old as [| y old]; simpl in *.
      + destruct new as [| z new]; [contradiction |]. destruct Hin as [-> | Hin]; [now left |].
        right. apply IH; auto. unfold kept in *. rewrite firstn_nil in *. simpl in *. lia.
      + unfold kept in H. simpl in H. destruct (live y) eqn:Hy; simpl in H.
        * right. apply IH; auto.
        * destruct new as [| z new]; [contradiction |].
          destruct Hin as [-> | Hin]; [now left |]. right. apply IH; auto. simpl in H.
          unfold kept. lia.
  Qed.

  Lemma place_NoDup : forall k old new,
      NoDup old -> NoDup new ->
      (forall x, In x new -> ~ In x (kept k old)) ->
      NoDup (place k old new live).
  Proof.
    induction k as [| k IH]; intros old new Ho Hn Hd; [constructor |].
    destruct old as [| y old]; simpl.
    - destruct new as [| z new]; [constructor |]. inv Hn. constructor.
      + intros Hin. apply place_In in Hin. destruct Hin as [Hin | Hin]; auto.
        unfold kept in Hin. rewrite firstn_nil in Hin. contradiction.
      + apply IH; auto. intros x _ Hin.
        unfold kept in Hin. rewrite firstn_nil in Hin. contradiction.
    - inv Ho. unfold kept in Hd. simpl in Hd. destruct (live y) eqn:Hy.
      + constructor.
        * intros Hin. apply place_In in Hin. destruct Hin as [Hin | Hin].
          -- unfold kept in Hin. apply filter_In in Hin. destruct Hin as [Hin _].
             apply firstn_In in Hin. contradiction.
          -- apply (Hd y Hin). now left.
        * apply IH; auto. intros x Hx Hin. apply (Hd x Hx). now right.
      + destruct new as [| z new]; [constructor |]. inv Hn. constructor.
        * intros Hin. apply place_In in Hin. destruct Hin as [Hin | Hin]; auto.
          apply (Hd z); [now left | exact Hin].
        * apply IH; auto. intros x Hx Hin. apply (Hd x); [now right | exact Hin].
  Qed.

End Place.

Section RootLayout.

  (* The roots for the variables [live]: the same variables, each once, and a variable
     that was a root in the first positions keeps its position *)
  Lemma root_layout_spec st live :
    NoDup (st_slots st) -> NoDup live ->
    let slots := root_layout st live in
    length slots = length live /\
    NoDup slots /\
    (forall x, In x slots <-> In x live) /\
    (forall p x, nth_error (st_slots st) p = Some x -> (p < length live)%nat -> In x live ->
                 nth_error slots p = Some x).
  Proof.
    intros Ho Hl. unfold root_layout.
    set (lv := fun x => in_list x live).
    set (k := length live).
    set (stay := List.filter lv (firstn k (st_slots st))).
    set (new := List.filter (fun x => negb (in_list x stay)) live).
    assert (Hstay : stay = kept lv k (st_slots st)) by reflexivity.
    assert (Hsd : NoDup stay).
    { apply NoDup_filter. apply NoDup_firstn; auto. }
    assert (Hsl : forall x, In x stay -> In x live).
    { intros x Hx. apply filter_In in Hx. destruct Hx as [_ Hx]. now apply in_list_In. }
    assert (Hnew : (length new + length stay = k)%nat).
    { pose proof (filter_partition_length (fun x => in_list x stay) live) as Hp.
      fold new in Hp. fold k in Hp. rewrite <- Hp.
      rewrite (Nat.add_comm (length (List.filter _ live))). f_equal.
      apply NoDup_same_length; auto.
      - now apply NoDup_filter.
      - intros x. rewrite filter_In, in_list_In. split; [intros H; split; auto | tauto]. }
    assert (Hlen : (k - length (kept lv k (st_slots st)) <= length new)%nat).
    { rewrite <- Hstay. lia. }
    assert (Hnd : forall x, In x new -> ~ In x (kept lv k (st_slots st))).
    { intros x Hx. rewrite <- Hstay. apply filter_In in Hx. destruct Hx as [_ Hx].
      apply negb_true_iff in Hx. now apply in_list_not_In. }
    assert (Hnl : forall x, In x new -> In x live).
    { intros x Hx. apply filter_In in Hx. tauto. }
    simpl. repeat split.
    - apply place_length; auto.
    - apply place_NoDup; auto. now apply NoDup_filter.
    - intros Hin. apply place_In in Hin. destruct Hin as [Hin | Hin]; auto.
    - intros Hin. destruct (in_dec Pos.eq_dec x stay) as [Hs | Hs].
      + rewrite Hstay in Hs. unfold kept in Hs. apply filter_In in Hs. destruct Hs as [Hs _].
        destruct (In_nth_error _ _ Hs) as [p Hp].
        assert (Hpk : (p < k)%nat).
        { assert (p < length (firstn k (st_slots st)))%nat by (apply nth_error_Some; congruence).
          pose proof (firstn_le_length k (st_slots st)). lia. }
        eapply nth_error_In. apply place_kept; eauto.
        * rewrite nth_error_firstn in Hp. destruct (Nat.ltb p k) eqn:E; [exact Hp | discriminate].
        * now apply in_list_In.
      + apply place_new.
        * rewrite <- Hstay. lia.
        * apply filter_In. split; auto. apply negb_true_iff. now apply in_list_not_In.
    - intros p x Hp Hlt Hx. apply place_kept; auto. now apply in_list_In.
  Qed.

End RootLayout.

(** * The layout of a switch *)

(* The first case of [l] with the key [z] is [s] *)
Definition first_key (l : list (Z * statement)) (z : Z) (s : statement) : Prop :=
  exists pre post, l = pre ++ (z, s) :: post /\ forall z' s', In (z', s') pre -> z' <> z.

Lemma first_key_head l z s : first_key ((z, s) :: l) z s.
Proof. exists [], l. split; [reflexivity | intros z' s' []]. Qed.

Lemma first_key_cons l z s z0 s0 :
  z0 <> z -> first_key l z s -> first_key ((z0, s0) :: l) z s.
Proof.
  intros Hne (pre & post & -> & Hpre). exists ((z0, s0) :: pre), post. split; [reflexivity |].
  intros z' s' [Heq | Hin]; [congruence | eauto].
Qed.

Lemma first_key_not_nil z s : ~ first_key [] z s.
Proof. intros (pre & post & H & _). destruct pre; discriminate. Qed.

Lemma select_switch_labeled : forall l z s,
    first_key l z s ->
    exists o ls, select_switch z (labeled l) = LScons o s ls.
Proof.
  intros l z s (pre & post & -> & Hpre). induction pre as [| [z' s'] pre IH]; simpl.
  - destruct post as [| c post].
    + exists None, LSnil. reflexivity.
    + exists (Some z), (labeled (c :: post)). unfold select_switch. simpl.
      destruct (zeq z z); [reflexivity | congruence].
  - assert (Hne : z' <> z) by (eapply Hpre; now left).
    destruct IH as (o & ls & IH). { intros z0 s0 Hin. eapply Hpre. right. eauto. }
    exists o, ls.
    destruct (pre ++ (z, s) :: post) as [| c rest] eqn:Hl; [destruct pre; discriminate |].
    rewrite <- IH. unfold select_switch. simpl.
    destruct (zeq z' z); [contradiction |]. reflexivity.
Qed.

Lemma first_key_single z0 s0 z s : first_key [(z0, s0)] z s -> s0 = s.
Proof.
  intros (pre & post & H & _). destruct pre as [| p pre]; simpl in H.
  - congruence.
  - destruct pre; discriminate.
Qed.

(* Two constructors of a case that passed the test of the generator have different keys *)
Lemma clashes_false cenv t r cs t' e' r' :
  clashes cenv t r cs = false ->
  In (t', e') cs -> t' <> t ->
  ctor_rep_of cenv t' = Ret r' ->
  match r', r with
  | Constant o, Constant o' | Block o _, Block o' _ => o <> o'
  | _, _ => True
  end.
Proof.
  intros Hc Hin Hne Hrep.
  assert (Hno : forall o o', r' = Constant o /\ r = Constant o' \/
                             (exists a a', r' = Block o a /\ r = Block o' a') -> o <> o').
  { intros o o' Hr ->.
    assert (Ht : clashes cenv t r cs = true); [| congruence].
    apply existsb_exists. exists (t', e'). split; [exact Hin |]. cbn [fst].
    apply andb_true_iff. split; [apply negb_true_iff, Pos.eqb_neq; exact Hne |].
    rewrite Hrep. destruct Hr as [[-> ->] | (a & a' & -> & ->)]; apply Z.eqb_refl. }
  destruct r' as [o | o a], r as [o' | o' a']; try exact I; apply Hno;
    [left | right; exists a, a']; split; reflexivity.
Qed.

(** * The analyses *)

Section Analyses.

  Context (prims : M.t primitive) (fenv : M.t nat).

  Lemma alloc_need_case y cs t e :
    In (t, e) cs -> (alloc_need prims e <= alloc_need prims (Ecase y cs))%nat.
  Proof.
    simpl. induction cs as [| [t' e'] cs IH]; intros H; [contradiction |].
    destruct H as [H | H].
    - inv H. apply Nat.le_max_l.
    - etransitivity; [apply IH; auto | apply Nat.le_max_r].
  Qed.

  Lemma max_roots_case y cs t e :
    In (t, e) cs -> (max_roots prims fenv e <= max_roots prims fenv (Ecase y cs))%nat.
  Proof.
    simpl. induction cs as [| [t' e'] cs IH]; intros H; [contradiction |].
    destruct H as [H | H].
    - inv H. apply Nat.le_max_l.
    - etransitivity; [apply IH; auto | apply Nat.le_max_r].
  Qed.

  Lemma uses_now_case y cs t e x :
    In (t, e) cs -> PS.In x (uses_now prims e) -> PS.In x (uses_now prims (Ecase y cs)).
  Proof.
    simpl. intros H Hx. apply PS.add_spec. right.
    induction cs as [| [t' e'] cs IH]; [contradiction |].
    apply PS.union_spec. destruct H as [H | H].
    - inv H. now left.
    - right. auto.
  Qed.

  Lemma uses_now_case_var y cs : PS.In y (uses_now prims (Ecase y cs)).
  Proof. simpl. apply PS.add_spec. now left. Qed.

  Lemma calls_itself_case f n y cs t e :
    In (t, e) cs -> calls_itself f n e = true -> calls_itself f n (Ecase y cs) = true.
  Proof.
    simpl. induction cs as [| [t' e'] cs IH]; intros H Hc; [contradiction |].
    apply orb_true_iff. destruct H as [H | H].
    - inv H. now left.
    - right. auto.
  Qed.

  (** The variables that are live *)

  Lemma live_vars_spec e x :
    In x (live_vars fenv e) <-> (occurs_free e x /\ M.get x fenv = None).
  Proof.
    unfold live_vars, is_fun. rewrite filter_In.
    assert (Hfv : In x (PS.elements (exp_fv e)) <-> occurs_free e x).
    { split; intros H; apply (exp_fv_correct e); exact H. }
    rewrite Hfv. destruct (M.get x fenv); simpl; split; intros [? ?]; split; auto; discriminate.
  Qed.

  Lemma live_vars_NoDup e : NoDup (live_vars fenv e).
  Proof.
    unfold live_vars. apply NoDup_filter.
    pose proof (PS.elements_spec2w (exp_fv e)) as H.
    induction H; constructor; auto.
    intros Hin. apply H. apply InA_alt. eauto.
  Qed.

  Lemma live_after_spec x e y :
    In y (live_after fenv x e) <-> (occurs_free e y /\ M.get y fenv = None /\ y <> x).
  Proof.
    unfold live_after. rewrite filter_In, live_vars_spec, negb_true_iff, Pos.eqb_neq. tauto.
  Qed.

  Lemma live_after_NoDup x e : NoDup (live_after fenv x e).
  Proof. unfold live_after. apply NoDup_filter. apply live_vars_NoDup. Qed.

End Analyses.

(** The variables that an expression binds *)

Lemma bound_vars_bound : forall e z, In z (bound_vars e) -> bound_var e z.
Proof.
  induction e using exp_ind'; simpl; intros z H; try contradiction.
  - destruct H as [-> | H]; [constructor | constructor; auto].
  - apply in_app_or in H. destruct H as [H | H].
    + apply Bound_Ecase with (c := c) (e := e); [apply IHe; exact H | now left].
    + specialize (IHe0 z H). inv IHe0.
      match goal with
      | [ Hb : bound_var ?e1 z, Hi : In (?c1, ?e1) l |- _ ] =>
        apply Bound_Ecase with (c := c1) (e := e1); [exact Hb | now right]
      end.
  - destruct H as [-> | H]; [constructor | constructor; auto].
  - destruct H as [-> | H]; [constructor | constructor; auto].
  - destruct H as [-> | H]; [constructor | constructor; auto].
  - destruct H as [-> | H]; [constructor | constructor; auto].
Qed.

(** The arities of the functions *)

(** * Lists of values *)

Lemma nthN_nth_error {A} : forall (l : list A) n v,
    nthN l n = Some v -> nth_error l (N.to_nat n) = Some v.
Proof.
  induction l as [| a l IH]; intros n v H; [destruct n; discriminate |].
  destruct n as [| p]; [exact H |].
  cbn [nthN] in H. apply IH in H.
  replace (N.to_nat (N.pos p)) with (S (N.to_nat (N.pos p - 1))) by lia. exact H.
Qed.

Lemma set_lists_nth {A} : forall xs (vs : list A) rho rho' j x v,
    NoDup xs -> set_lists xs vs rho = Some rho' ->
    nth_error xs j = Some x -> nth_error vs j = Some v -> M.get x rho' = Some v.
Proof.
  induction xs as [| y xs IH]; intros vs rho rho' j x v Hnd Hset Hx Hv.
  - destruct j; discriminate.
  - destruct vs as [| w vs]; [discriminate |]. simpl in Hset.
    destruct (set_lists xs vs rho) as [rho1 |] eqn:Hrho1; [| discriminate].
    injection Hset as <-. inversion Hnd as [| ? ? Hy Hnd']; subst.
    destruct j as [| j]; simpl in Hx, Hv.
    + injection Hx as ->. injection Hv as ->. apply M.gss.
    + rewrite M.gso; [eapply IH; eauto |]. intros ->. apply Hy. eapply nth_error_In; eauto.
Qed.

(** * Spare identifiers *)

Lemma idents_from_length : forall n p, length (idents_from p n) = n.
Proof. induction n; intros p; simpl; auto. Qed.

Lemma idents_from_ge : forall n p x, In x (idents_from p n) -> (p <= x)%positive.
Proof.
  induction n as [| n IH]; intros p x H; [contradiction |].
  destruct H as [<- | H]; [lia |]. apply IH in H. lia.
Qed.

Lemma idents_from_NoDup : forall n p, NoDup (idents_from p n).
Proof.
  induction n as [| n IH]; intros p; simpl; constructor; auto.
  intros H. apply idents_from_ge in H. lia.
Qed.

Lemma fun_arities_find fds : forall f,
    M.get f (fun_arities fds) =
    match find_def f fds with
    | Some (_, xs, _) => Some (length xs)
    | None => None
    end.
Proof.
  induction fds as [g t xs e fds IH |]; intros f; simpl.
  - destruct (M.elt_eq f g) as [-> | Hne].
    + now rewrite M.gss.
    + rewrite M.gso; auto.
  - apply M.gempty.
Qed.

Lemma fun_arities_name fds f :
  M.get f (fun_arities fds) <> None <-> name_in_fundefs fds f.
Proof.
  rewrite fun_arities_find. split.
  - destruct (find_def f fds) as [[[t xs] e] |] eqn:H; [| congruence].
    intros _. eapply find_def_name_in_fundefs; eauto.
  - intros H. apply name_in_fundefs_find_def_is_Some in H.
    destruct H as (t & xs & e & ->). discriminate.
Qed.

(** * Headers *)

Local Open Scope Z_scope.

(* The low 8 bits of a header are the ordinal *)
Lemma header_tag ord n :
  0 <= ord <= max_block_ordinal -> 0 <= n ->
  Int64.unsigned (Int64.and (Int64.repr (block_header ord n)) (Int64.repr 255)) = ord.
Proof.
  intros Hord Hn. unfold max_block_ordinal in Hord.
  change 255 with (two_p 8 - 1). rewrite <- Int64.zero_ext_and by lia.
  rewrite Int64.zero_ext_mod by (compute; split; congruence).
  rewrite Int64.unsigned_repr_eq.
  change Int64.modulus with (two_p 8 * two_p 56).
  rewrite <- Zmod_div_mod; [| reflexivity | reflexivity | exists (two_p 56); ring].
  unfold block_header. rewrite Z.shiftl_mul_pow2 by lia.
  change (2 ^ 10) with (4 * two_p 8). rewrite Z.mul_assoc, Z.add_comm, Z_mod_plus_full.
  apply Z.mod_small. change (two_p 8) with 256. lia.
Qed.

(** * Variables of the analyses *)

Section Uses.

  Context (prims : M.t primitive).

  (* The variables that [uses_now] returns are free or bound in the expression *)
  Lemma uses_now_vars : forall e z,
      PS.In z (uses_now prims e) -> occurs_free e z \/ bound_var e z.
  Proof.
    induction e using exp_ind'; simpl; intros z H.
    - apply union_list_spec in H. destruct H as [H | H].
      + destruct (IHe z H) as [Hf | Hb]; [| right; now constructor].
        destruct (Pos.eq_dec v z) as [-> | Hne]; [right; constructor | left; now constructor].
      + left. now constructor.
    - apply PS.add_spec in H. destruct H as [-> | H]; [left; constructor |].
      apply PS.empty_spec in H. contradiction.
    - apply PS.add_spec in H. destruct H as [-> | H]; [left; constructor |].
      apply PS.union_spec in H. destruct H as [H | H].
      + destruct (IHe z H) as [Hf | Hb].
        * left. now apply Free_Ecase2.
        * right. eapply Bound_Ecase; [exact Hb | now left].
      + assert (H' : PS.In z (uses_now prims (Ecase v l))) by (simpl; apply PS.add_spec; now right).
        destruct (IHe0 z H') as [Hf | Hb].
        * left. now apply Free_Ecase3.
        * right. inv Hb. eapply Bound_Ecase; [eassumption | right; eassumption].
    - apply PS.add_spec in H. destruct H as [-> | H]; [left; constructor |].
      destruct (IHe z H) as [Hf | Hb]; [| right; now constructor].
      destruct (Pos.eq_dec v z) as [-> | Hne]; [right; constructor | left; now constructor].
    - apply PS.add_spec in H. destruct H as [-> | H].
      + left. constructor. now left.
      + apply union_list_spec in H. destruct H as [H | H].
        * apply PS.empty_spec in H. contradiction.
        * left. constructor. now right.
    - apply PS.empty_spec in H. contradiction.
    - apply PS.add_spec in H. destruct H as [-> | H]; [left; constructor |].
      apply union_list_spec in H. destruct H as [H | H].
      + apply PS.empty_spec in H. contradiction.
      + left. now constructor.
    - destruct (IHe z H) as [Hf | Hb]; [| right; now constructor].
      destruct (Pos.eq_dec v z) as [-> | Hne]; [right; constructor | left; now constructor].
    - destruct (allocates prims p).
      + apply union_list_spec in H. destruct H as [H | H].
        * apply PS.empty_spec in H. contradiction.
        * left. now constructor.
      + apply union_list_spec in H. destruct H as [H | H].
        * destruct (IHe z H) as [Hf | Hb]; [| right; now constructor].
          destruct (Pos.eq_dec v z) as [-> | Hne]; [right; constructor | left; now constructor].
        * left. now constructor.
    - apply PS.singleton_spec in H. subst. left. constructor.
  Qed.

End Uses.
