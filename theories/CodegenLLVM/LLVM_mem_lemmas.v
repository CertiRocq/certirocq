(** * Frame lemmas for Vellvm's concrete memory model (64-bit finite pointers). *)

From Stdlib Require Import ZArith NArith List Lia String.
From ITree Require Import ITree Eq.Eqit.
From ExtLib Require Import Structures.Monads.

From Vellvm Require Import
  Utils Syntax Params
  Interfaces.Memory Implementations.Memory
  Implementations.ParamsV Implementations.IPtrFinite
  Semantics.DynamicValues Semantics.MemoryBytes Semantics.LLVMEvents
  Handlers.
From Vellvm Require Import Utils.IntMaps Semantics.Operations.Gep Semantics.EOU.

From CertiRocq.CodegenLLVM Require Import LambdaANF_to_LLVM_statement.

Import ListNotations.
Import MonadNotation.
Open Scope monad_scope.
Open Scope Z_scope.

Set Bullet Behavior "Strict Subproofs".
Unset Implicit Arguments.

(* ------------------------------------------------------------------ *)
(** ** Generic facts about [memS_runs] *)

Lemma memS_runs_det {X} st (m : memM X) st1 x1 st2 x2 :
  memS_runs st m st1 x1 -> memS_runs st m st2 x2 -> st1 = st2 /\ x1 = x2.
Proof.
  intros H; revert st2 x2; induction H; intros st2 x2 H2; inversion H2; subst; auto.
Qed.

Lemma memS_runs_bind {X Y} st (m : memM X) (k : X -> memM Y) st1 x st' y :
  memS_runs st m st1 x -> memS_runs st1 (k x) st' y ->
  memS_runs st (bind m k) st' y.
Proof.
  intros H; revert st' y; induction H; intros st'' y Hk; cbn in *.
  - exact Hk.
  - constructor. apply IHmemS_runs. exact Hk.
  - constructor. apply IHmemS_runs. exact Hk.
Qed.

Lemma memS_runs_bind_inv {X Y} st (m : memM X) (k : X -> memM Y) st' y :
  memS_runs st (bind m k) st' y ->
  exists st1 x, memS_runs st m st1 x /\ memS_runs st1 (k x) st' y.
Proof.
  revert st; induction m; intros st0 H'; cbn in H'.
  - do 2 eexists; split; [constructor | exact H'].
  - inversion H'.
  - inversion H'.
  - inversion H'.
  - inversion H'; subst.
    destruct (H _ _ ltac:(eassumption)) as (st1 & x & H1 & H3).
    exists st1, x; split; [constructor; exact H1 | exact H3].
  - inversion H'; subst.
    destruct (H tt _ ltac:(eassumption)) as (st1 & x & H1 & H3).
    exists st1, x; split; [constructor; exact H1 | exact H3].
  - inversion H'.
Qed.

Lemma memS_runs_get_inv {X} st (k : state -> memM X) st' x :
  memS_runs st (Mget k) st' x -> memS_runs st (k st) st' x.
Proof. intros H; inversion H; subst; auto. Qed.

Lemma memS_runs_put_inv {X} st st0 (k : unit -> memM X) st' x :
  memS_runs st (Mput st0 k) st' x -> memS_runs st0 (k tt) st' x.
Proof. intros H; inversion H; subst; auto. Qed.

Lemma memS_runs_ret_inv {X} st (x : X) st' y :
  memS_runs st (ret x) st' y -> st' = st /\ y = x.
Proof. intros H; inversion H; subst; auto. Qed.

Lemma memS_runs_lift_inv {X} st (c : EOU.EOU X) st' x :
  memS_runs st (lift c) st' x -> c = EOU.raise_ret x /\ st' = st.
Proof. destruct c; cbn; intros H; inversion H; subst; auto. Qed.

Lemma memS_runs_lift {X} st (x : X) :
  memS_runs st (lift (EOU.raise_ret x)) st x.
Proof. constructor. Qed.

(* ------------------------------------------------------------------ *)
(** ** [get_consecutive_ptrs] *)

Lemma map_monad_acc_EOU {A B} (f : A -> EOU.EOU B) :
  forall l acc res,
    (fix loop (acc : list B) (l : list A) : EOU.EOU (list B) :=
       match l with
       | [] => ret (rev_append acc [])
       | a :: l' => b <- f a;; loop (b :: acc) l'
       end) acc l = ret res ->
    exists bs, Forall2 (fun a b => f a = ret b) l bs /\ res = rev_append acc bs.
Proof.
  induction l as [| a l IH]; intros acc res H; cbn in H.
  - inversion H; subst. exists []; split; auto.
  - destruct (f a) eqn:E; try discriminate.
    destruct (IH _ _ H) as (bs & HF & ->).
    exists (x :: bs); split; auto.
Qed.

Lemma map_monad_acc_EOU' {A B} (f : A -> EOU.EOU B) l res :
  map_monad_acc f l = ret res -> Forall2 (fun a b => f a = ret b) l res.
Proof.
  intros H. unfold map_monad_acc in H.
  apply map_monad_acc_EOU in H. destruct H as (bs & HF & ->). exact HF.
Qed.

Lemma Forall2_nth_error_l {A B} (R : A -> B -> Prop) l1 l2 i b :
  Forall2 R l1 l2 -> nth_error l2 i = Some b -> exists a, nth_error l1 i = Some a /\ R a b.
Proof.
  intros HF; revert i; induction HF; intros [|i] Hn; cbn in *; try discriminate.
  - inversion Hn; subst; eauto.
  - eauto.
Qed.

Lemma nth_error_Nseq' : forall len start i,
    (i < len)%nat -> nth_error (Nseq start len) i = Some (start + N.of_nat i)%N.
Proof.
  induction len as [| len IH]; intros start i Hi; [lia|].
  destruct i; cbn [Nseq nth_error].
  - f_equal; lia.
  - rewrite IH by lia. f_equal; lia.
Qed.

Lemma Nseq_length : forall len start, length (Nseq start len) = len.
Proof. induction len; intros; cbn; auto. Qed.

Definition consec (p : ptr) (ptrs : list ptr) : Prop :=
  forall i q, nth_error ptrs i = Some q ->
         ptr_to_int q = ptr_to_int p + Z.of_nat i /\ ptr_provenance q = ptr_provenance p.

Lemma gcp_spec p n ptrs :
  get_consecutive_ptrs p n = ret ptrs ->
  length ptrs = N.to_nat n /\ consec p ptrs.
Proof.
  unfold get_consecutive_ptrs. cbn [bind EOU.EOU_monad].
  destruct (intptr_seq 0 n) as [| | | ixs] eqn:Hseq; try discriminate.
  intros H. apply map_monad_acc_EOU' in H.
  unfold intptr_seq in Hseq. rewrite EOU.seq_map_monad_acc_eq, N_to_nat_safe_eq in Hseq.
  apply EOU.map_monad_EOU_Forall2 in Hseq.
  pose proof (Forall2_length H) as L1. pose proof (Forall2_length Hseq) as L2.
  rewrite Nseq_length in L2.
  split.
  - lia.
  - intros i q Hq.
    destruct (Forall2_nth_error_l _ _ _ _ _ H Hq) as (ix & Hix & Hg).
    destruct (Forall2_nth_error_l _ _ _ _ _ Hseq Hix) as (k & Hk & Hf).
    assert (Hi : (i < N.to_nat n)%nat).
    { rewrite L2. apply nth_error_Some. congruence. }
    rewrite nth_error_Nseq' in Hk by exact Hi. inversion Hk; subst k.
    unfold Basics.compose in Hf.
    apply from_Z_to_Z in Hf.
    split.
    + apply handle_gep_ptr_ix in Hg. rewrite Hg, Hf.
      replace (sizeof_dtyp (DTYPE_I 8)) with 1%N by reflexivity. rewrite nat_N_Z. lia.
    + cbn in Hg. destruct from_Z_bits in Hg; inversion Hg; reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(** ** Reads *)

(** The byte [b] can be read through [q] in [st]. *)
Definition byte_ok (st : state) (q : ptr) (b : memory_byte) : Prop :=
  exists aid, IntMaps.lookup (ptr_to_int q) (mem_of st) = Some (b, aid) /\
         access_allowed (ptr_provenance q) aid = true.

Lemma Read_byte_runs st q st' b :
  memS_runs st (Read_byte q) st' b <-> st' = st /\ byte_ok st q b.
Proof.
  unfold Read_byte, read_byte_raw, byte_ok, mem_of. split.
  - intros H. cbn [bind memS_mon memS_bind get] in H. apply memS_runs_get_inv in H.
    cbn [bind memS_mon memS_bind ret] in H.
    destruct read_byte_raw_mem as [[b0 aid]|] eqn:E; cbn [memS_bind] in H; [|inversion H].
    destruct access_allowed eqn:A; inversion H; subst.
    split; auto. exists aid; split; auto.
  - intros (-> & aid & E & A). cbn [bind memS_mon memS_bind get]. apply MR_get.
    cbn [bind memS_mon memS_bind ret].
    unfold read_byte_raw_mem. unfold IntMaps.lookup in E. change (state_get_memory st) with (state_memory_stack st). rewrite E. cbn [memS_bind].
    rewrite A. constructor.
Qed.

Lemma read_loop_runs :
  forall ptrs acc st st' res,
    memS_runs st
      ((fix loop (acc : list memory_byte) (l : list ptr) : memM (list memory_byte) :=
          match l with
          | [] => ret (rev_append acc [])
          | a :: l' => b <- Read_byte a;; loop (b :: acc) l'
          end) acc ptrs) st' res <->
    st' = st /\ exists bs, Forall2 (byte_ok st) ptrs bs /\ res = rev_append acc bs.
Proof.
  induction ptrs as [|q ptrs IH]; intros acc st st' res.
  - split.
    + intros H. inversion H; subst. split; auto. exists []; auto.
    + intros (-> & bs & HF & ->). inversion HF; subst. constructor.
  - split.
    + intros H. apply memS_runs_bind_inv in H. destruct H as (st1 & b & H1 & H2).
      apply Read_byte_runs in H1. destruct H1 as [-> Hb].
      apply IH in H2. destruct H2 as (-> & bs & HF & ->).
      split; auto. exists (b :: bs); split; auto.
    + intros (-> & bs & HF & ->). inversion HF; subst.
      eapply memS_runs_bind; [apply Read_byte_runs; split; eauto|].
      apply IH. split; auto. eexists; split; eauto.
Qed.

Lemma read_bytes_runs st p n st' bs :
  memS_runs st (read_bytes p n) st' bs <->
  st' = st /\ exists ptrs, get_consecutive_ptrs p n = ret ptrs /\ Forall2 (byte_ok st) ptrs bs.
Proof.
  unfold read_bytes. split.
  - intros H. apply memS_runs_bind_inv in H. destruct H as (st1 & ptrs & H1 & H2).
    apply memS_runs_lift_inv in H1. destruct H1 as [E ->].
    apply read_loop_runs in H2. destruct H2 as (-> & bs' & HF & ->).
    split; auto. exists ptrs; split; auto.
  - intros (-> & ptrs & E & HF).
    eapply memS_runs_bind; [rewrite E; apply memS_runs_lift|].
    apply read_loop_runs. split; auto. eexists; split; eauto.
Qed.

Lemma read_dvalue_runs st t p st' v :
  memS_runs st (read_dvalue t p) st' v <->
  st' = st /\ exists ptrs bs, get_consecutive_ptrs p (sizeof_dtyp t) = ret ptrs /\
                         Forall2 (byte_ok st) ptrs bs /\
                         memory_bytes_to_dvalue bs t = ret v.
Proof.
  unfold read_dvalue. split.
  - intros H. apply memS_runs_bind_inv in H. destruct H as (st1 & bs & H1 & H2).
    apply read_bytes_runs in H1. destruct H1 as (-> & ptrs & E & HF).
    apply memS_runs_lift_inv in H2. destruct H2 as [E2 ->].
    split; auto. exists ptrs, bs; auto.
  - intros (-> & ptrs & bs & E & HF & E2).
    eapply memS_runs_bind; [apply read_bytes_runs; split; eauto|].
    rewrite E2. apply memS_runs_lift.
Qed.

Lemma In_consec p ptrs q :
  consec p ptrs -> In q ptrs ->
  exists i, (i < length ptrs)%nat /\ ptr_to_int q = ptr_to_int p + Z.of_nat i /\
       ptr_provenance q = ptr_provenance p.
Proof.
  intros C Hin. apply In_nth_error in Hin. destruct Hin as (i & Hi).
  exists i. split; [apply nth_error_Some; congruence|]. apply C; auto.
Qed.

Lemma byte_ok_frame st st2 ptrs bs :
  Forall2 (byte_ok st) ptrs bs ->
  (forall q, In q ptrs -> IntMaps.lookup (ptr_to_int q) (mem_of st2) =
                    IntMaps.lookup (ptr_to_int q) (mem_of st)) ->
  Forall2 (byte_ok st2) ptrs bs.
Proof.
  induction 1 as [|q b ptrs bs Hb HF IH]; intros Hag; constructor.
  - destruct Hb as (aid & E & A). exists aid. rewrite Hag by (left; auto). auto.
  - apply IH. intros; apply Hag; right; auto.
Qed.

(** Bytes [n] bytes from address [a] agree. *)
Definition same_bytes (st st2 : state) (a : Z) (n : Z) : Prop :=
  forall a', a <= a' < a + n -> IntMaps.lookup a' (mem_of st2) = IntMaps.lookup a' (mem_of st).

Lemma read_dvalue_frame st t p st' v :
  memS_runs st (read_dvalue t p) st' v ->
  st' = st /\
  forall st2, same_bytes st st2 (ptr_to_int p) (Z.of_N (sizeof_dtyp t)) ->
         memS_runs st2 (read_dvalue t p) st2 v.
Proof.
  intros H. apply read_dvalue_runs in H. destruct H as (-> & ptrs & bs & E & HF & E2).
  split; auto. intros st2 Hs.
  apply read_dvalue_runs. split; auto. exists ptrs, bs. repeat split; auto.
  apply gcp_spec in E. destruct E as [L C].
  eapply byte_ok_frame; eauto.
  intros q Hq. destruct (In_consec _ _ _ C Hq) as (i & Hi & Eq & _).
  apply Hs. rewrite Eq. lia.
Qed.

Lemma sizeof_i64 : sizeof_dtyp (DTYPE_I 64) = 8%N.
Proof. reflexivity. Qed.
Lemma sizeof_ptr : sizeof_dtyp DTYPE_Pointer = 8%N.
Proof. reflexivity. Qed.

Lemma reads_word_frame st st2 p z :
  reads_word st p z -> same_bytes st st2 (ptr_to_int p) 8 -> reads_word st2 p z.
Proof.
  intros (st' & H) Hs. apply read_dvalue_frame in H. destruct H as [-> H].
  exists st2. apply H. rewrite sizeof_i64. exact Hs.
Qed.

Lemma reads_ptr_frame st st2 p q :
  reads_ptr st p q -> same_bytes st st2 (ptr_to_int p) 8 -> reads_ptr st2 p q.
Proof.
  intros (st' & H) Hs. apply read_dvalue_frame in H. destruct H as [-> H].
  exists st2. apply H. rewrite sizeof_ptr. exact Hs.
Qed.

Lemma reads_word_state st p z st' :
  memS_runs st (read_dvalue (DTYPE_I 64) p) st' (I64 z) -> st' = st.
Proof. intros H. apply read_dvalue_frame in H. tauto. Qed.

Lemma reads_word_runs st p z : reads_word st p z -> memS_runs st (read_dvalue (DTYPE_I 64) p) st (I64 z).
Proof. intros (st' & H). pose proof H as H'. apply reads_word_state in H'. subst. exact H. Qed.

Lemma reads_ptr_runs st p q :
  reads_ptr st p q -> memS_runs st (read_dvalue DTYPE_Pointer p) st (DVALUE_Base (DVALUE_Pointer q)).
Proof.
  intros (st' & H). pose proof H as H'. apply read_dvalue_frame in H'. destruct H' as [-> _]. exact H.
Qed.

(* ------------------------------------------------------------------ *)
(** ** Writes *)

Definition set_mem (st : state) (m : memory) : state :=
  mkState (mkMemoryStack m (frames_of st) (heap_of st)) (state_provenance st).

Lemma Write_byte_runs st q b st' u :
  memS_runs st (Write_byte q b) st' u <->
  exists b0 aid, IntMaps.lookup (ptr_to_int q) (mem_of st) = Some (b0, aid) /\
            access_allowed (ptr_provenance q) aid = true /\
            st' = set_mem st (IM.add (ptr_to_int q) (b, aid) (mem_of st)).
Proof.
  unfold Write_byte, read_byte_raw, set_byte_raw, get_mem, upd_mem, app_mem. split.
  - intros H. cbn [bind memS_mon memS_bind get] in H. apply memS_runs_get_inv in H.
    cbn [bind memS_mon memS_bind ret] in H.
    destruct read_byte_raw_mem as [[b0 aid]|] eqn:E; cbn [memS_bind] in H; [|inversion H].
    destruct access_allowed eqn:A; [|inversion H].
    apply memS_runs_get_inv, memS_runs_get_inv, memS_runs_put_inv in H.
    inversion H; subst.
    exists b0, aid. split; [exact E|]. split; [exact A|]. reflexivity.
  - intros (b0 & aid & E & A & ->).
    cbn [bind memS_mon memS_bind get]. apply MR_get.
    cbn [bind memS_mon memS_bind ret].
    unfold read_byte_raw_mem. unfold IntMaps.lookup, mem_of in E.
    change (state_get_memory st) with (state_memory_stack st). rewrite E. cbn [memS_bind].
    rewrite A. repeat constructor. destruct u. constructor.
Qed.

(** The allocation id stored at address [a] (if allocated). *)
Definition aid_at (st : state) (a : Z) : option allocationId :=
  option_map snd (IntMaps.lookup a (mem_of st)).

(** [q] may be written in [st]. *)
Definition writable_at (st : state) (q : ptr) : Prop :=
  exists aid, aid_at st (ptr_to_int q) = Some aid /\ access_allowed (ptr_provenance q) aid = true.

Lemma lookup_add_eq {A} k (v : A) m : IntMaps.lookup k (IM.add k v m) = Some v.
Proof. unfold IntMaps.lookup. apply IntMaps.IP.F.add_eq_o. reflexivity. Qed.

Lemma lookup_add_neq {A} k k' (v : A) m :
  k <> k' -> IntMaps.lookup k' (IM.add k v m) = IntMaps.lookup k' m.
Proof. intros H. unfold IntMaps.lookup. apply IntMaps.IP.F.add_neq_o. exact H. Qed.

Lemma Write_byte_aid st q b st' u a :
  memS_runs st (Write_byte q b) st' u -> aid_at st' a = aid_at st a.
Proof.
  intros H. apply Write_byte_runs in H. destruct H as (b0 & aid & E & A & ->).
  unfold aid_at; cbn [mem_of set_mem state_memory_stack Memory_stack_memory].
  destruct (Z.eq_dec (ptr_to_int q) a) as [<-|ne].
  - rewrite lookup_add_eq. rewrite E. reflexivity.
  - rewrite lookup_add_neq by exact ne. reflexivity.
Qed.

Lemma writable_at_aid st st2 q :
  writable_at st q -> aid_at st2 (ptr_to_int q) = aid_at st (ptr_to_int q) -> writable_at st2 q.
Proof. intros (aid & E & A) E2. exists aid. rewrite E2. auto. Qed.

Lemma Write_byte_exists st q b :
  writable_at st q -> exists st', memS_runs st (Write_byte q b) st' tt.
Proof.
  intros (aid & E & A). unfold aid_at in E.
  destruct (IntMaps.lookup (ptr_to_int q) (mem_of st)) as [[b0 aid0]|] eqn:E'; inversion E; subst.
  eexists. apply Write_byte_runs. exists b0, aid. repeat split; eauto.
Qed.

Section WriteLoop.
  Let f := (fun '(ptr, byte) => @write_byte _ MemoryModelPrimitivesV ptr byte)
             : ptr * memory_byte -> memM unit.

  Lemma write_loop_runs :
    forall ptrs bytes st st' u,
      length ptrs = length bytes ->
      memS_runs st (loop_monad f (zip ptrs bytes)) st' u ->
      st' = set_mem st (mem_of st') /\
      (forall a, ~ In a (map ptr_to_int ptrs) ->
            IntMaps.lookup a (mem_of st') = IntMaps.lookup a (mem_of st)) /\
      (forall a, aid_at st' a = aid_at st a) /\
      (NoDup (map ptr_to_int ptrs) -> Forall2 (byte_ok st') ptrs bytes).
  Proof.
    induction ptrs as [|q ptrs IH]; intros [|b bytes] st st' u L H; try discriminate.
    - cbn in H. inversion H; subst. repeat split; auto.
      + destruct st' as [[]]. reflexivity.
    - cbn [zip zipWith loop_monad] in H. injection L as L.
      apply memS_runs_bind_inv in H. destruct H as (st1 & u1 & H1 & H2).
      change (memS_runs st (Write_byte q b) st1 u1) in H1.
      pose proof (fun a => Write_byte_aid _ _ _ _ _ a H1) as Haid1.
      apply Write_byte_runs in H1. destruct H1 as (b0 & aid & E & A & ->).
      destruct (IH _ _ _ _ L H2) as (Hst & Hout & Haid & Hrb).
      split; [|split; [|split]].
      + rewrite Hst. reflexivity.
      + intros a Ha. rewrite Hout by (intros Hin; apply Ha; right; exact Hin).
        cbn [mem_of set_mem state_memory_stack Memory_stack_memory].
        apply lookup_add_neq. intros Heq; apply Ha; left; exact Heq.
      + intros a. rewrite Haid. apply Haid1.
      + intros ND. inversion ND as [|x y Hnin ND']; subst. constructor.
        * exists aid. split; [|exact A].
          rewrite Hout by exact Hnin.
          cbn [mem_of set_mem state_memory_stack Memory_stack_memory].
          apply lookup_add_eq.
        * apply Hrb. exact ND'.
  Qed.

  Lemma write_loop_exists :
    forall ptrs bytes st,
      length ptrs = length bytes ->
      (forall q, In q ptrs -> writable_at st q) ->
      exists st', memS_runs st (loop_monad f (zip ptrs bytes)) st' tt.
  Proof.
    induction ptrs as [|q ptrs IH]; intros [|b bytes] st L W; try discriminate.
    - exists st. constructor.
    - cbn [zip zipWith loop_monad]. injection L as L.
      destruct (Write_byte_exists st q b) as (st1 & H1); [apply W; left; auto|].
      destruct (IH bytes st1 L) as (st' & H2).
      + intros q' Hq'. eapply writable_at_aid; [apply W; right; exact Hq'|].
        eapply Write_byte_aid; eauto.
      + exists st'. eapply memS_runs_bind; [exact H1|exact H2].
  Qed.
End WriteLoop.

Lemma consec_NoDup p ptrs : consec p ptrs -> NoDup (map ptr_to_int ptrs).
Proof.
  intros C. apply NoDup_nth_error. intros i j Hi Heq.
  rewrite length_map in Hi.
  rewrite !nth_error_map in Heq.
  destruct (nth_error ptrs i) as [qi|] eqn:Ei; [|apply nth_error_Some in Hi; congruence].
  destruct (nth_error ptrs j) as [qj|] eqn:Ej; cbn in Heq; [|discriminate].
  injection Heq as Heq.
  apply C in Ei, Ej. destruct Ei as [Ei _], Ej as [Ej _].
  change (ptr_to_int qi = ptr_to_int qj) in Heq. lia.
Qed.

Lemma consec_not_in p ptrs a :
  consec p ptrs -> ~ (ptr_to_int p <= a < ptr_to_int p + Z.of_nat (length ptrs)) ->
  ~ In a (map ptr_to_int ptrs).
Proof.
  intros C Ha Hin. apply in_map_iff in Hin. destruct Hin as (q & <- & Hq).
  destruct (In_consec _ _ _ C Hq) as (i & Hi & E & _). apply Ha. lia.
Qed.

Lemma dvalue_to_memory_bytes_length v t :
  length (dvalue_to_memory_bytes v t) = N.to_nat (sizeof_dtyp t).
Proof.
  unfold dvalue_to_memory_bytes. rewrite seq_map_acc_eq, length_map, Nseq_length.
  apply N_to_nat_safe_eq.
Qed.

Lemma N_length_nat {A} (l : list A) : N_length l = N.of_nat (length l).
Proof.
  rewrite N_length_eq. induction l; cbn [N.length length]; [reflexivity|]. rewrite IHl. lia.
Qed.

Lemma write_dvalue_runs st t p v st' u :
  memS_runs st (write_dvalue t p v) st' u ->
  st' = set_mem st (mem_of st') /\
  (forall a, ~ (ptr_to_int p <= a < ptr_to_int p + Z.of_N (sizeof_dtyp t)) ->
        IntMaps.lookup a (mem_of st') = IntMaps.lookup a (mem_of st)) /\
  (forall a, aid_at st' a = aid_at st a) /\
  exists ptrs, get_consecutive_ptrs p (sizeof_dtyp t) = ret ptrs /\
          Forall2 (byte_ok st') ptrs (dvalue_to_memory_bytes v t).
Proof.
  unfold write_dvalue, write_bytes. intros H.
  apply memS_runs_bind_inv in H. destruct H as (st1 & ptrs & H1 & H2).
  apply memS_runs_lift_inv in H1. destruct H1 as [E ->].
  rewrite N_length_nat, dvalue_to_memory_bytes_length, N2Nat.id in E.
  pose proof (gcp_spec _ _ _ E) as [L C].
  rewrite zip_acc_eq in H2.
  apply write_loop_runs in H2;
    [|rewrite L, dvalue_to_memory_bytes_length; reflexivity].
  destruct H2 as (Hst & Hout & Haid & Hrb).
  split; [exact Hst|]. split; [|split; [exact Haid|]].
  - intros a Ha. apply Hout. eapply consec_not_in; eauto. rewrite L.
    rewrite N_nat_Z. exact Ha.
  - exists ptrs. split; [exact E|]. apply Hrb. eapply consec_NoDup; eauto.
Qed.

Lemma write_dvalue_exists st t p v ptrs :
  get_consecutive_ptrs p (sizeof_dtyp t) = ret ptrs ->
  (forall q, In q ptrs -> writable_at st q) ->
  exists st', memS_runs st (write_dvalue t p v) st' tt.
Proof.
  intros E W. pose proof (gcp_spec _ _ _ E) as [L C].
  destruct (write_loop_exists ptrs (dvalue_to_memory_bytes v t) st) as (st' & H);
    [rewrite L, dvalue_to_memory_bytes_length; reflexivity | exact W |].
  exists st'. unfold write_dvalue, write_bytes.
  eapply memS_runs_bind.
  - rewrite N_length_nat, dvalue_to_memory_bytes_length, N2Nat.id, E. apply memS_runs_lift.
  - rewrite zip_acc_eq. exact H.
Qed.

Lemma write_dvalue_heap st t p v st' u :
  memS_runs st (write_dvalue t p v) st' u ->
  heap_of st' = heap_of st /\ frames_of st' = frames_of st /\
  state_provenance st' = state_provenance st.
Proof.
  intros H. apply write_dvalue_runs in H. destruct H as (Hst & _).
  rewrite Hst. auto.
Qed.

Lemma write_dvalue_read st t p v st' u v' :
  memS_runs st (write_dvalue t p v) st' u ->
  memory_bytes_to_dvalue (dvalue_to_memory_bytes v t) t = ret v' ->
  memS_runs st' (read_dvalue t p) st' v'.
Proof.
  intros H E. apply write_dvalue_runs in H. destruct H as (_ & _ & _ & ptrs & Eg & HF).
  apply read_dvalue_runs. split; auto. exists ptrs, (dvalue_to_memory_bytes v t). auto.
Qed.

(* ------------------------------------------------------------------ *)
(** ** Byte (de)serialisation of 64-bit words and pointers *)

Lemma concat_extract_Z : forall n k u, 0 <= u ->
  concat_bytes_Z (map (fun i => extract_byte_Z u (Z.of_nat i)) (seq k n)) =
  (u / 2 ^ (8 * Z.of_nat k)) mod 2 ^ (8 * Z.of_nat n).
Proof.
  induction n as [|n IH]; intros k u Hu.
  - cbn. rewrite Z.mod_1_r. reflexivity.
  - cbn [seq map concat_bytes_Z]. rewrite IH by exact Hu.
    unfold extract_byte_Z. rewrite Z.shiftr_div_pow2 by lia.
    rewrite Z.shiftl_mul_pow2 by lia.
    replace (8 * Z.of_nat (S k)) with (8 * Z.of_nat k + 8) by lia.
    replace (8 * Z.of_nat (S n)) with (8 + 8 * Z.of_nat n) by lia.
    rewrite Z.pow_add_r by lia. rewrite Z.pow_add_r by lia.
    rewrite <- Z.div_div by lia.
    rewrite Z.mul_comm with (n := Z.of_nat k) (m := 8).
    set (w := u / 2 ^ (8 * Z.of_nat k)).
    rewrite (Z.rem_mul_r w (2 ^ 8) (2 ^ (8 * Z.of_nat n))) by lia.
    change (2 ^ 8) with 256. ring.
Qed.

Lemma ptr_to_int_range (q : ptr) : 0 <= ptr_to_int q < 2 ^ 64.
Proof.
  destruct q as [i pr]. cbn. pose proof (@Integers.unsigned_range 64 i) as H.
  change (@Integers.modulus 64) with (2 ^ 64) in H. lia.
Qed.

Lemma concat_extract_8 u : 0 <= u < 2 ^ 64 ->
  concat_bytes_Z
    [extract_byte_Z u 0; extract_byte_Z u 1; extract_byte_Z u 2; extract_byte_Z u 3;
     extract_byte_Z u 4; extract_byte_Z u 5; extract_byte_Z u 6; extract_byte_Z u 7] = u.
Proof.
  intros Hu.
  change [extract_byte_Z u 0; extract_byte_Z u 1; extract_byte_Z u 2; extract_byte_Z u 3;
          extract_byte_Z u 4; extract_byte_Z u 5; extract_byte_Z u 6; extract_byte_Z u 7]
    with (map (fun i => extract_byte_Z u (Z.of_nat i)) (seq 0 8)).
  rewrite concat_extract_Z by lia. cbn [Z.of_nat]. rewrite Z.mul_0_r, Z.pow_0_r, Z.div_1_r.
  apply Z.mod_small. exact Hu.
Qed.

Lemma repr_mod (a : Z) : @Integers.repr 64 a = Integers.repr (a mod 2 ^ 64).
Proof.
  rewrite <- (Integers.repr_unsigned (Integers.repr a)).
  rewrite Integers.unsigned_repr_eq. reflexivity.
Qed.

Lemma unsigned_repr64 (a : Z) : @Integers.unsigned 64 (Integers.repr a) = a mod 2 ^ 64.
Proof. rewrite Integers.unsigned_repr_eq. reflexivity. Qed.

Lemma concat_bytes_vint_Z (bs : list Z) :
  @concat_bytes_Z_vint (@Integers.bit_int 64) _ bs = Integers.repr (concat_bytes_Z bs).
Proof.
  unfold concat_bytes_Z_vint. induction bs as [|b bs IH]; [reflexivity|].
  cbn [map concat_bytes_vint concat_bytes_Z]. rewrite IH.
  cbn -[Z.shiftl]. unfold Integers.add, Integers.shl.
  rewrite !unsigned_repr64. rewrite (Z.mod_small 8) by lia.
  rewrite !Z.shiftl_mul_pow2 by lia.
  rewrite repr_mod. rewrite (repr_mod (b + _)). f_equal.
  rewrite Z.add_mod_idemp_r by lia. rewrite Z.add_mod_idemp_l by lia.
  rewrite Z.add_mod by lia. rewrite (Z.add_mod b) by lia.
  rewrite Z.mul_mod_idemp_l by lia. reflexivity.
Qed.

Lemma extract_byte_vint_Z (x : @Integers.bit_int 64) (i : Z) : 0 <= i < 8 ->
  extract_byte_vint x i = extract_byte_Z (Integers.unsigned x) i.
Proof.
  intros Hi. unfold extract_byte_vint, extract_byte_Z. cbn -[Z.shiftr Z.mul].
  unfold Integers.modu, Integers.shru.
  pose proof (@Integers.unsigned_range 64 x) as Hx.
  change (@Integers.modulus 64) with (2 ^ 64) in Hx.
  rewrite !Integers.Z_mod_modulus_eq. change (@Integers.modulus 64) with (2 ^ 64).
  rewrite (Z.mod_small (i * 8)) by lia.
  rewrite Z.shiftr_div_pow2 by lia.
  assert (Hp : 0 < 2 ^ (i * 8)) by (apply Z.pow_pos_nonneg; lia).
  assert (Hy : Integers.unsigned x / 2 ^ (i * 8) <= Integers.unsigned x)
    by (apply Z.div_le_upper_bound; nia).
  assert (Hy0 : 0 <= Integers.unsigned x / 2 ^ (i * 8)) by (apply Z.div_pos; lia).
  rewrite (Z.mod_small (_ / _) (2 ^ 64)) by lia.
  apply Z.mod_small. pose proof (Z.mod_pos_bound (Integers.unsigned x / 2 ^ (i * 8)) 256). lia.
Qed.

Lemma bytes_roundtrip_i64 z :
  memory_bytes_to_dvalue (dvalue_to_memory_bytes (I64 z) (DTYPE_I 64)) (DTYPE_I 64) = ret (I64 z).
Proof.
  unfold I64. cbn -[extract_byte_vint concat_bytes_Z_vint].
  set (x := @Integers.repr 64 z).
  rewrite !extract_byte_vint_Z by lia.
  rewrite concat_bytes_vint_Z, concat_extract_8.
  - rewrite Integers.repr_unsigned. reflexivity.
  - pose proof (@Integers.unsigned_range 64 x) as Hx.
    change (@Integers.modulus 64) with (2 ^ 64) in Hx. exact Hx.
Qed.

Lemma bytes_roundtrip_ptr (q : ptr) :
  exists q', memory_bytes_to_dvalue
          (dvalue_to_memory_bytes (DVALUE_Base (DVALUE_Pointer q)) DTYPE_Pointer) DTYPE_Pointer
        = ret (DVALUE_Base (DVALUE_Pointer q')) /\
        ptr_to_int q' = ptr_to_int q /\ ptr_provenance q' = wildcard_prov.
Proof.
  cbn -[extract_byte_Z concat_bytes_Z ptr_to_int int_to_ptr].
  rewrite concat_extract_8 by apply ptr_to_int_range.
  destruct (int_to_ptr_ptr_to_int_exists q wildcard_prov) as (q' & E & E1 & E2).
  exists q'. split; [|split; [exact E1|exact E2]].
  cbn in E |- *. destruct from_Z_bits; inversion E; subst. reflexivity.
Qed.

(** Read-after-write. *)
Lemma write_read_word st p z st' u :
  memS_runs st (write_dvalue (DTYPE_I 64) p (I64 z)) st' u -> reads_word st' p z.
Proof.
  intros H. exists st'. eapply write_dvalue_read; [exact H|]. apply bytes_roundtrip_i64.
Qed.

Lemma write_read_ptr st p q st' u :
  memS_runs st (write_dvalue DTYPE_Pointer p (DVALUE_Base (DVALUE_Pointer q))) st' u ->
  exists q', reads_ptr st' p q' /\ ptr_to_int q' = ptr_to_int q /\
        ptr_provenance q' = wildcard_prov.
Proof.
  intros H. destruct (bytes_roundtrip_ptr q) as (q' & E & E1 & E2).
  exists q'. split; auto. exists st'. eapply write_dvalue_read; eauto.
Qed.

(* ------------------------------------------------------------------ *)
(** ** [writable_word] *)

(** [writable_word] in terms of the allocation ids of the word's bytes. *)
Definition word_writable (st : state) (p : ptr) : Prop :=
  exists ptrs, get_consecutive_ptrs p 8 = ret ptrs /\ forall q, In q ptrs -> writable_at st q.

Lemma Forall2_In_l {A B} (R : A -> B -> Prop) l1 l2 a :
  Forall2 R l1 l2 -> In a l1 -> exists b, In b l2 /\ R a b.
Proof.
  induction 1; intros Hin; [destruct Hin|]. destruct Hin as [<-|Hin].
  - exists y; split; [left|]; auto.
  - destruct (IHForall2 Hin) as (b & ? & ?). exists b; split; [right|]; auto.
Qed.

Lemma byte_ok_writable_at st q b : byte_ok st q b -> writable_at st q.
Proof. intros (aid & E & A). exists aid. unfold aid_at. rewrite E. auto. Qed.

Lemma write_dvalue_writable_at st t p v st' u :
  memS_runs st (write_dvalue t p v) st' u ->
  exists ptrs, get_consecutive_ptrs p (sizeof_dtyp t) = ret ptrs /\
          forall q, In q ptrs -> writable_at st q.
Proof.
  intros H. apply write_dvalue_runs in H. destruct H as (_ & _ & Haid & ptrs & E & HF).
  exists ptrs. split; auto. intros q Hq.
  destruct (Forall2_In_l _ _ _ _ HF Hq) as (b & _ & Hb).
  eapply writable_at_aid; [eapply byte_ok_writable_at; eauto|]. auto.
Qed.

Lemma writable_word_iff st p : writable_word st p <-> word_writable st p.
Proof.
  split.
  - intros W. destruct (W 0) as (st' & H & _).
    apply write_dvalue_writable_at in H. rewrite sizeof_i64 in H. exact H.
  - intros (ptrs & E & W) z.
    destruct (write_dvalue_exists st (DTYPE_I 64) p (I64 z) ptrs) as (st' & H);
      [rewrite sizeof_i64; exact E | exact W |].
    exists st'. split; auto. eapply write_read_word; eauto.
Qed.

(** [writable_word] only depends on the allocation ids of the word's bytes. *)
Lemma writable_word_aid st st2 p :
  writable_word st p ->
  (forall a, ptr_to_int p <= a < ptr_to_int p + 8 -> aid_at st2 a = aid_at st a) ->
  writable_word st2 p.
Proof.
  rewrite !writable_word_iff. intros (ptrs & E & W) Hag. exists ptrs. split; auto.
  intros q Hq. eapply writable_at_aid; [apply W; exact Hq|].
  apply gcp_spec in E. destruct E as [L C].
  destruct (In_consec _ _ _ C Hq) as (i & Hi & Eq & _). apply Hag. lia.
Qed.

Lemma same_bytes_aid st st2 a n a' :
  same_bytes st st2 a n -> a <= a' < a + n -> aid_at st2 a' = aid_at st a'.
Proof. intros H Ha. unfold aid_at. rewrite H by exact Ha. reflexivity. Qed.

Lemma writable_word_frame st st2 p :
  writable_word st p -> same_bytes st st2 (ptr_to_int p) 8 -> writable_word st2 p.
Proof. intros W H. eapply writable_word_aid; eauto. intros; eapply same_bytes_aid; eauto. Qed.

(** Any write preserves every [writable_word] (writes keep allocation ids). *)
Lemma write_dvalue_writable_word st t q v st' u p :
  memS_runs st (write_dvalue t q v) st' u -> writable_word st p -> writable_word st' p.
Proof.
  intros H W. apply write_dvalue_runs in H. destruct H as (_ & _ & Haid & _).
  eapply writable_word_aid; eauto.
Qed.

(** A word that is read can be read again after a write elsewhere. *)
Lemma write_dvalue_same_bytes st t q v st' u a n :
  memS_runs st (write_dvalue t q v) st' u ->
  (forall a', a <= a' < a + n -> ~ (ptr_to_int q <= a' < ptr_to_int q + Z.of_N (sizeof_dtyp t))) ->
  same_bytes st st' a n.
Proof.
  intros H D a' Ha'. apply write_dvalue_runs in H. destruct H as (_ & Hout & _).
  apply Hout. apply D. exact Ha'.
Qed.

(* ------------------------------------------------------------------ *)
(** ** Stack operations *)

Lemma Mempush_runs st st' u :
  memS_runs st Mempush st' u ->
  mem_of st' = mem_of st /\ heap_of st' = heap_of st /\
  frames_of st' = Snoc (frames_of st) [] /\ state_provenance st' = state_provenance st.
Proof.
  unfold Mempush, app_frame_stack. intros H.
  apply memS_runs_bind_inv in H. destruct H as (st1 & x & H1 & H2).
  apply memS_runs_get_inv, memS_runs_ret_inv in H1. destruct H1 as [-> ->].
  apply memS_runs_put_inv, memS_runs_ret_inv in H2. destruct H2 as [-> _].
  repeat split.
Qed.

Lemma lookup_delete_neq {A} k k' (m : IntMap A) :
  k <> k' -> IntMaps.lookup k' (IntMaps.delete k m) = IntMaps.lookup k' m.
Proof. intros H. unfold IntMaps.lookup, IntMaps.delete. apply IntMaps.IP.F.remove_neq_o. exact H. Qed.

Lemma free_frame_memory_out (f : Frame) : forall (m : memory) a,
  ~ In a (map ptr_to_int f) -> IntMaps.lookup a (free_frame_memory f m) = IntMaps.lookup a m.
Proof.
  unfold free_frame_memory.
  induction f as [|k f IH]; intros m a Ha; cbn [fold_left]; [reflexivity|].
  rewrite IH by (intros Hin; apply Ha; right; exact Hin).
  unfold free_byte. apply lookup_delete_neq. intros E; apply Ha; left; exact E.
Qed.

Lemma Mempop_runs st st' u :
  memS_runs st Mempop st' u ->
  exists fs f, frames_of st = Snoc fs f /\ frames_of st' = fs /\
          heap_of st' = heap_of st /\ state_provenance st' = state_provenance st /\
          mem_of st' = free_frame_memory f (mem_of st).
Proof.
  unfold Mempop, get_frame, get_frame_stack, app_frame_stack_eob, get_framestack,
    app_frame_stack, app_mem. intros H.
  apply memS_runs_bind_inv in H. destruct H as (st1 & f & H1 & H2).
  apply memS_runs_bind_inv in H1. destruct H1 as (st2 & fs & H3 & H4).
  apply memS_runs_bind_inv in H3. destruct H3 as (st3 & s & H5 & H6).
  apply memS_runs_get_inv, memS_runs_ret_inv in H5. destruct H5 as [-> ->].
  apply memS_runs_ret_inv in H6. destruct H6 as [-> ->].
  apply memS_runs_bind_inv in H2. destruct H2 as (st4 & x & H7 & H8).
  apply memS_runs_bind_inv in H7. destruct H7 as (st5 & fs' & H9 & H10).
  apply memS_runs_bind_inv in H9. destruct H9 as (st6 & s & H11 & H12).
  apply memS_runs_get_inv, memS_runs_ret_inv in H11. destruct H11 as [-> ->].
  apply memS_runs_ret_inv in H12. destruct H12 as [-> ->].
  apply memS_runs_bind_inv in H10. destruct H10 as (st7 & fs'' & H13 & H14).
  apply memS_runs_lift_inv in H13. destruct H13 as [E ->].
  apply memS_runs_bind_inv in H14. destruct H14 as (st8 & s & H15 & H16).
  apply memS_runs_get_inv, memS_runs_ret_inv in H15. destruct H15 as [-> ->].
  apply memS_runs_put_inv, memS_runs_ret_inv in H16. destruct H16 as [-> _].
  apply memS_runs_bind_inv in H8. destruct H8 as (st9 & s & H17 & H18).
  apply memS_runs_get_inv, memS_runs_ret_inv in H17. destruct H17 as [-> ->].
  apply memS_runs_put_inv, memS_runs_ret_inv in H18. destruct H18 as [-> _].
  change (state_get_memory st) with (state_memory_stack st) in H4.
  destruct (Memory_stack_frame_stack (state_memory_stack st)) as [f0|fs0 f0] eqn:Efs;
    apply memS_runs_ret_inv in H4; destruct H4 as [-> ->];
    change (state_get_memory st) with (state_memory_stack st) in E;
    rewrite Efs in E; cbn in E; inversion E; subst.
  do 2 eexists. split; [exact Efs|]. repeat split.
Qed.

(** Popping only frees addresses of the popped frame. *)
Lemma Mempop_lookup st st' u :
  memS_runs st Mempop st' u ->
  heap_of st' = heap_of st /\
  exists fs f, frames_of st = Snoc fs f /\ frames_of st' = fs /\
          forall a, ~ In a (map ptr_to_int f) ->
               IntMaps.lookup a (mem_of st') = IntMaps.lookup a (mem_of st).
Proof.
  intros H. apply Mempop_runs in H. destruct H as (fs & f & E1 & E2 & E3 & _ & E5).
  split; auto. exists fs, f. repeat split; auto.
  intros a Ha. rewrite E5. apply free_frame_memory_out. exact Ha.
Qed.

(* ------------------------------------------------------------------ *)
(** ** Runs with choices (allocation)

    [memS_runs] has no rule for [Mchoose], so it cannot describe an
    allocation.  [memS_runs_c] resolves the choices exactly as Vellvm's
    [memM_interp] does. *)

Inductive memS_runs_c {X} : state -> memM X -> state -> X -> Prop :=
| MRC_ret st x : memS_runs_c st (Mret x) st x
| MRC_get st k st' x : memS_runs_c st (k st) st' x -> memS_runs_c st (Mget k) st' x
| MRC_put st st0 k st' x : memS_runs_c st0 (k tt) st' x -> memS_runs_c st (Mput st0 k) st' x
| MRC_next_key st sz al (k : Z -> memM X) st' x :
    memS_runs_c st (k (next_key_with_alignment (mem_of st) al)) st' x ->
    memS_runs_c st (Mchoose (Cnext_key sz al) k) st' x
| MRC_fresh st (k : provenance -> memM X) st' x :
    memS_runs_c {| state_memory_stack := state_memory_stack st;
                   state_provenance := next_provenance (state_provenance st) |}
                (k (next_provenance (state_provenance st))) st' x ->
    memS_runs_c st (Mchoose Cfresh_prov k) st' x
| MRC_exposed st (k : option provenance -> memM X) st' x :
    memS_runs_c st (k None) st' x -> memS_runs_c st (Mchoose Cexposed_prov k) st' x.

Lemma memS_runs_runs_c {X} st (m : memM X) st' x :
  memS_runs st m st' x -> memS_runs_c st m st' x.
Proof. induction 1; constructor; auto. Qed.

Lemma memM_interp_runs_c {E} `{FailureE -< E} `{UBE -< E} `{OOME -< E}
      {X} st (m : memM X) st' x :
  memS_runs_c st m st' x ->
  @memM_interp _ E _ _ _ X m st ≈ Ret (st', x).
Proof.
  induction 1; cbn; try reflexivity; try assumption.
  rewrite Eqit.bind_ret_l. cbn. assumption.
Qed.

Lemma memS_runs_c_bind {X Y} st (m : memM X) (k : X -> memM Y) st1 x st' y :
  memS_runs_c st m st1 x -> memS_runs_c st1 (k x) st' y ->
  memS_runs_c st (bind m k) st' y.
Proof.
  intros H; revert st' y; induction H; intros st'' y Hk; cbn in *; try constructor; auto.
Qed.

Definition choose_step {X} (st : state) (c : memC) (st' : state) (x : X) :
  (@memCType provenance c -> memM X) -> Prop :=
  match c as c' return (@memCType provenance c' -> memM X) -> Prop with
  | Cnext_key _ al => fun k => memS_runs_c st (k (next_key_with_alignment (mem_of st) al)) st' x
  | Cfresh_prov => fun k =>
      memS_runs_c {| state_memory_stack := state_memory_stack st;
                     state_provenance := next_provenance (state_provenance st) |}
                  (k (next_provenance (state_provenance st))) st' x
  | Cexposed_prov => fun k => memS_runs_c st (k None) st' x
  end.

Lemma memS_runs_c_choose_inv {X} st c k st' (x : X) :
  memS_runs_c st (Mchoose c k) st' x -> choose_step st c st' x k.
Proof.
  intros H.
  refine (match H in memS_runs_c st m st' x
                return match m with Mchoose c k => choose_step st c st' x k | _ => True end
          with
          | MRC_next_key _ _ _ _ _ _ H1 => H1
          | MRC_fresh _ _ _ _ H1 => H1
          | MRC_exposed _ _ _ _ H1 => H1
          | _ => I
          end).
Qed.

Lemma memS_runs_c_bind_inv {X Y} st (m : memM X) (k : X -> memM Y) st' y :
  memS_runs_c st (bind m k) st' y ->
  exists st1 x, memS_runs_c st m st1 x /\ memS_runs_c st1 (k x) st' y.
Proof.
  revert st; induction m; intros st0 H'; cbn in H'.
  - do 2 eexists; split; [constructor | exact H'].
  - inversion H'.
  - inversion H'.
  - inversion H'.
  - inversion H'; subst.
    destruct (H _ _ ltac:(eassumption)) as (st1 & x & H1 & H3).
    exists st1, x; split; [constructor; exact H1 | exact H3].
  - inversion H'; subst.
    destruct (H tt _ ltac:(eassumption)) as (st1 & x & H1 & H3).
    exists st1, x; split; [constructor; exact H1 | exact H3].
  - apply memS_runs_c_choose_inv in H'.
    destruct c; cbn in H'; destruct (H _ _ H') as (st1 & x & H1 & H3);
      exists st1, x; split; auto; constructor; exact H1.
Qed.

Lemma memS_runs_c_get_inv {X} st (k : state -> memM X) st' x :
  memS_runs_c st (Mget k) st' x -> memS_runs_c st (k st) st' x.
Proof. intros H; inversion H; subst; auto. Qed.

Lemma memS_runs_c_put_inv {X} st st0 (k : unit -> memM X) st' x :
  memS_runs_c st (Mput st0 k) st' x -> memS_runs_c st0 (k tt) st' x.
Proof. intros H; inversion H; subst; auto. Qed.

Lemma memS_runs_c_ret_inv {X} st (x : X) st' y :
  memS_runs_c st (ret x) st' y -> st' = st /\ y = x.
Proof. intros H; inversion H; subst; auto. Qed.

Lemma memS_runs_c_lift_inv {X} st (c : EOU.EOU X) st' x :
  memS_runs_c st (lift c) st' x -> c = EOU.raise_ret x /\ st' = st.
Proof. destruct c; cbn; intros H; inversion H; subst; auto. Qed.

Ltac inv_runs_c H :=
  match type of H with
  | memS_runs_c _ (bind _ _) _ _ =>
      let st := fresh "st" in let x := fresh "x" in
      let H1 := fresh "H" in let H2 := fresh "H" in
      apply memS_runs_c_bind_inv in H; destruct H as (st & x & H1 & H2);
      inv_runs_c H1; inv_runs_c H2
  | memS_runs_c _ get _ _ =>
      apply memS_runs_c_get_inv, memS_runs_c_ret_inv in H; destruct H as [? ?]; subst
  | memS_runs_c _ (put _) _ _ =>
      apply memS_runs_c_put_inv, memS_runs_c_ret_inv in H; destruct H as [? ?]; subst
  | memS_runs_c _ (ret _) _ _ =>
      apply memS_runs_c_ret_inv in H; destruct H as [? ?]; subst
  | _ => idtac
  end.

Lemma Allocate_runs st init align pr st' p :
  memS_runs_c st (Allocate_bytes_with_pr init align pr) st' p ->
  ptr_to_int p = next_key_with_alignment (mem_of st) align /\
  ptr_provenance p = allocation_id_to_prov (provenance_to_allocation_id pr) /\
  state_provenance st' = state_provenance st /\
  exists ptrs, get_consecutive_ptrs p (N_length init) = ret ptrs /\
     state_memory_stack st' =
       add_all_to_frame ptrs
         (mkMemoryStack
            (add_all_index_acc (memory_bytes_to_bytes (provenance_to_allocation_id pr) init)
                               (ptr_to_int p) (mem_of st))
            (frames_of st) (heap_of st)).
Proof.
  unfold Allocate_bytes_with_pr, get_free_block, add_block_to_stack, add_block,
    add_ptrs_to_frame, get_mem, upd_mem, app_mem, app_mem_stack. intros H.
  apply memS_runs_c_bind_inv in H. destruct H as (st1 & [p1 ptrs] & H1 & H2).
  apply memS_runs_c_bind_inv in H1. destruct H1 as (st2 & addr & H3 & H4).
  apply memS_runs_c_choose_inv in H3. cbn [choose_step] in H3.
  apply memS_runs_c_ret_inv in H3. destruct H3 as [-> ->].
  apply memS_runs_c_bind_inv in H4. destruct H4 as (st3 & p2 & H5 & H6).
  apply memS_runs_c_lift_inv in H5. destruct H5 as [E1 ->].
  apply memS_runs_c_bind_inv in H6. destruct H6 as (st4 & ptrs2 & H7 & H8).
  apply memS_runs_c_lift_inv in H7. destruct H7 as [E2 ->].
  apply memS_runs_c_ret_inv in H8. destruct H8 as [-> E3]. inversion E3; subst p2 ptrs2. clear E3.
  inv_runs_c H2.
  split; [eapply ptr_to_int_int_to_ptr; eauto|].
  split; [eapply int_to_ptr_provenance; eauto|].
  split; [reflexivity|].
  exists ptrs. split; [exact E2|]. reflexivity.
Qed.

Lemma add_to_frame_parts ms k :
  Memory_stack_memory (add_to_frame ms k) = Memory_stack_memory ms /\
  Memory_stack_heap (add_to_frame ms k) = Memory_stack_heap ms /\
  Memory_stack_frame_stack (add_to_frame ms k) =
    match Memory_stack_frame_stack ms with
    | Singleton f => Singleton (k :: f)
    | Snoc s f => Snoc s (k :: f)
    end.
Proof. destruct ms as [m [f|s f] h]; repeat split. Qed.

Definition push_top (ks : list ptr) (fs : Framestack) : Framestack :=
  match fs with
  | Singleton f => Singleton (rev ks ++ f)
  | Snoc s f => Snoc s (rev ks ++ f)
  end.

Lemma add_all_to_frame_parts ks : forall ms,
  Memory_stack_memory (add_all_to_frame ks ms) = Memory_stack_memory ms /\
  Memory_stack_heap (add_all_to_frame ks ms) = Memory_stack_heap ms /\
  Memory_stack_frame_stack (add_all_to_frame ks ms) =
    push_top ks (Memory_stack_frame_stack ms).
Proof.
  unfold add_all_to_frame. induction ks as [|k ks IH]; intros ms; cbn [fold_left].
  - destruct ms as [m [f|s f] h]; repeat split.
  - destruct (IH (add_to_frame ms k)) as (E1 & E2 & E3).
    destruct (add_to_frame_parts ms k) as (F1 & F2 & F3).
    rewrite E1, E2, E3, F1, F2, F3. repeat split.
    destruct (Memory_stack_frame_stack ms); cbn; rewrite <- app_assoc; reflexivity.
Qed.

Lemma add_all_index_acc_out {A} : forall (l : list A) z m k,
  (k < z \/ z + Z.of_nat (length l) <= k) ->
  IntMaps.lookup k (add_all_index_acc l z m) = IntMaps.lookup k m.
Proof.
  induction l as [|v l IH]; intros z m k Hk; cbn [add_all_index_acc]; [reflexivity|].
  rewrite IH by (cbn [length] in Hk; lia).
  apply lookup_add_neq. cbn [length] in Hk; lia.
Qed.

Lemma add_all_index_acc_in {A} : forall (l : list A) z m k,
  z <= k < z + Z.of_nat (length l) ->
  exists v, In v l /\ IntMaps.lookup k (add_all_index_acc l z m) = Some v.
Proof.
  induction l as [|v l IH]; intros z m k Hk; cbn [length] in Hk; [lia|].
  cbn [add_all_index_acc].
  destruct (Z.eq_dec k z) as [->|ne].
  - exists v. split; [left; auto|].
    rewrite add_all_index_acc_out by lia. apply lookup_add_eq.
  - destruct (IH (z + 1) (IntMaps.add z v m) k) as (v' & Hin & E); [lia|].
    exists v'. split; [right; auto|exact E].
Qed.

Lemma next_key_with_alignment_gt {A} (m : IntMap A) (align : N) (a : Z) :
  IM.In a m -> a < next_key_with_alignment m align.
Proof.
  intros IN.
  pose proof IN as GK.
  unfold next_key_with_alignment.
  eapply IM_greatest_key_In' in GK.
  destruct GK as (gk & GK).
  rewrite GK.
  apply IM_greatest_key_lt in GK.
  red in GK.
  specialize (GK a).
  assert (Hagk : (a < 1 + gk)%Z).
  { destruct m; cbn in IN.
    unfold IM.In in IN.
    apply IM.Raw.Proofs.In_alt in IN.
    apply GK in IN. auto. }
  assert (Hle : (1 + Z.to_N gk <= pad_to align (1 + Z.to_N gk))%N)
    by (unfold pad_to; lia).
  apply N2Z.inj_le in Hle.
  rewrite N2Z.inj_add in Hle.
  change (Z.of_N 1) with 1%Z in Hle.
  assert (Hgk : (gk <= Z.of_N (Z.to_N gk))%Z) by (destruct gk; simpl; lia).
  lia.
Qed.

Lemma next_key_fresh {A} (m : IntMap A) align a :
  next_key_with_alignment m align <= a -> IntMaps.lookup a m = None.
Proof.
  intros H. destruct (IntMaps.lookup a m) eqn:E; [|reflexivity].
  exfalso. assert (IM.In a m) as Hin.
  { exists a0. apply IM.find_2. exact E. }
  apply (next_key_with_alignment_gt m align) in Hin. lia.
Qed.

Lemma repeatN_concat_length {A} (l : list A) n :
  length (List.concat (repeatN n l)) = (N.to_nat n * length l)%nat.
Proof.
  induction n using N.peano_ind; unfold repeatN in *.
  - reflexivity.
  - rewrite N.recursion_succ; try (repeat intro; subst; auto).
    cbn [List.concat]. rewrite length_app, IHn. rewrite N2Nat.inj_succ. lia.
Qed.

Lemma allocate_dtyp_bytes_length t n :
  length (concat_acc (repeatN n (generate_poison_bytes t))) = N.to_nat (n * sizeof_dtyp t).
Proof.
  rewrite concat_acc_eq, repeatN_concat_length.
  unfold generate_poison_bytes, generate_num_poison_bytes, generate_num_poison_bytes_h.
  rewrite seq_map_acc_eq, length_map, Nseq_length, N_to_nat_safe_eq. lia.
Qed.

Lemma allocate_dtyp_runs st t n align st' p :
  memS_runs_c st (allocate_dtyp t n align) st' p ->
  heap_of st' = heap_of st /\
  (exists ptrs, consec p ptrs /\ length ptrs = N.to_nat (n * sizeof_dtyp t) /\
           frames_of st' = push_top ptrs (frames_of st)) /\
  ptr_to_int p = next_key_with_alignment (mem_of st) align /\
  (forall a, ptr_to_int p <= a -> IntMaps.lookup a (mem_of st) = None) /\
  (forall a, a < ptr_to_int p \/ ptr_to_int p + Z.of_N (n * sizeof_dtyp t) <= a ->
        IntMaps.lookup a (mem_of st') = IntMaps.lookup a (mem_of st)) /\
  (forall q, ptr_provenance q = ptr_provenance p ->
        ptr_to_int p <= ptr_to_int q < ptr_to_int p + Z.of_N (n * sizeof_dtyp t) ->
        writable_at st' q).
Proof.
  unfold allocate_dtyp. destruct dtyp_eqb; intros H; [inversion H|].
  unfold allocate_bytes in H.
  apply memS_runs_c_bind_inv in H. destruct H as (st1 & pr & H1 & H2).
  apply memS_runs_c_choose_inv in H1. cbn [choose_step] in H1.
  apply memS_runs_c_ret_inv in H1. destruct H1 as [-> ->].
  change (memS_runs_c {| state_memory_stack := state_memory_stack st;
                         state_provenance := next_provenance (state_provenance st) |}
            (Allocate_bytes_with_pr (concat_acc (repeatN n (generate_poison_bytes t))) align
               (next_provenance (state_provenance st))) st' p) in H2.
  apply Allocate_runs in H2. destruct H2 as (Ep & Eprov & _ & ptrs & Eg & Est).
  change (mem_of {| state_memory_stack := state_memory_stack st;
                    state_provenance := next_provenance (state_provenance st) |}) with (mem_of st) in *.
  change (frames_of {| state_memory_stack := state_memory_stack st;
                       state_provenance := next_provenance (state_provenance st) |}) with (frames_of st) in *.
  change (heap_of {| state_memory_stack := state_memory_stack st;
                     state_provenance := next_provenance (state_provenance st) |}) with (heap_of st) in *.
  pose proof (allocate_dtyp_bytes_length t n) as L.
  set (init := concat_acc (repeatN n (generate_poison_bytes t))) in *.
  rewrite N_length_nat, L, N2Nat.id in Eg.
  apply gcp_spec in Eg. destruct Eg as [Lp C].
  destruct (add_all_to_frame_parts ptrs
              {| Memory_stack_memory :=
                   add_all_index_acc (memory_bytes_to_bytes (provenance_to_allocation_id (next_provenance (state_provenance st))) init)
                     (ptr_to_int p) (mem_of st);
                 Memory_stack_frame_stack := frames_of st;
                 Memory_stack_heap := heap_of st |}) as (M1 & M2 & M3).
  rewrite <- Est in M1, M2, M3. cbn [Memory_stack_memory Memory_stack_heap Memory_stack_frame_stack] in M1, M2, M3.
  assert (Lb : length (memory_bytes_to_bytes (provenance_to_allocation_id (next_provenance (state_provenance st))) init) =
               N.to_nat (n * sizeof_dtyp t)).
  { unfold memory_bytes_to_bytes. rewrite map_acc_eq, length_map. exact L. }
  split; [exact M2|]. split; [exists ptrs; auto|]. split; [exact Ep|].
  split; [intros a Ha; apply next_key_fresh with (align := align); lia|].
  split.
  - intros a Ha. unfold mem_of at 1. rewrite M1. apply add_all_index_acc_out.
    rewrite Lb, N_nat_Z. lia.
  - intros q Hq Hr.
    destruct (add_all_index_acc_in (memory_bytes_to_bytes (provenance_to_allocation_id (next_provenance (state_provenance st))) init)
                (ptr_to_int p) (mem_of st) (ptr_to_int q)) as (v & Hin & E);
      [rewrite Lb, N_nat_Z; lia|].
    unfold memory_bytes_to_bytes in Hin. rewrite map_acc_eq in Hin.
    apply in_map_iff in Hin. destruct Hin as (b & <- & _).
    exists (provenance_to_allocation_id (next_provenance (state_provenance st))). split.
    + unfold aid_at, mem_of. rewrite M1. rewrite E. reflexivity.
    + rewrite Hq, Eprov. cbn. rewrite N.eqb_refl. reflexivity.
Qed.

(** [Alloca] as handled by [handle_memoryM]. *)
Lemma alloca_runs st t n align st' v :
  memS_runs_c st (handle_memoryM (Alloca t n align)) st' v ->
  exists p, v = DVALUE_Base (DVALUE_Pointer p) /\
       memS_runs_c st (allocate_dtyp t n (match align with None => 8%N | Some a => a end)) st' p.
Proof.
  cbn [handle_memoryM]. intros H.
  apply memS_runs_c_bind_inv in H. destruct H as (st1 & p & H1 & H2).
  apply memS_runs_c_ret_inv in H2. destruct H2 as [-> ->]. eauto.
Qed.
