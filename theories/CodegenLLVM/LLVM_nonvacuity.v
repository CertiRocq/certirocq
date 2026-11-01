(** * Non-vacuity of the LambdaANF -> LLVM correctness theorem

    [LambdaANF_to_LLVM_correct_statement] (in [LambdaANF_to_LLVM_statement.v])
    has two kinds of hypotheses: the runtime contract [runtime_correct] and
    the source-side conditions ([llvm_restricted], [bstep_e]).  Its
    conclusion is a disjunction "out of memory, or returns a word
    representing the value".  This file checks that the hypotheses can be met
    in a way that does not make the conclusion trivial.

    - A concrete runtime ([nv_make_tinfo], [nv_gc], [nv_heap_inv]), written
      as Vellvm [MCFGtop] code, satisfies [runtime_correct]
      ([nv_runtime_correct]).  Its [make_tinfo] really [malloc]s a block of
      [nv_block_size] bytes (Vellvm's [malloc] intrinsic), puts an 8232-byte
      [thread_info] at offset 8 of the block and a nursery of 1024 words right
      after it, and stores [alloc], [limit] and the (null) frame pointer; it
      takes the [returns] branch of the first clause
      ([nv_make_tinfo_returns], [nv_make_tinfo_not_oom]).  The collector
      [nv_gc] always reports out of memory, which the collector clause of
      [runtime_correct] allows.  With the witness runtime the theorem thus
      says something about runs that never need a collection (programs
      allocating at most 1024 words).  A returning collector can also meet
      the clause: [nalloc] is bounded ([0 <= nalloc < 2^61]), the collector
      may free from-space, and only the root slots' allocation ids must be
      kept.  [nv_gc_check] is such a collector: it returns without changes
      when the nursery already has [nalloc] free words, and reports out of
      memory otherwise; [nv_runtime_correct_check] shows that it meets the
      clause (it is not a model of CertiRocq's moving collector).
    - A program, [ex_prog = Efun Fnil (Econstr x C [] (Ehalt x))], satisfies
      [llvm_restricted] and evaluates to [C] ([ex_hypotheses]), so with the
      witness runtime the theorem's conclusion is really asserted for it:
      [ex_correct] says the compiled program runs out of memory or returns 1.
      [LLVM_nonvacuity_run.v] runs the compiled program and shows that it
      returns 1 ([ex_returns], [ex_not_oom]).
    - [oom_runtime_correct] / [oom_runtime_vacuous] record the vacuous
      instance the statement also admits: a [make_tinfo] that runs out of
      memory at once satisfies [runtime_correct] and makes the conclusion
      trivially true.

    Everything here is [Qed] and, by [Print Assumptions], uses only the
    standard library's axioms (classical logic, proof irrelevance,
    functional extensionality) and primitive types.  [ex_correct] is an
    instance of the proved theorem [LambdaANF_to_LLVM_correct] (from
    [LLVM_sim_exp.v]). *)

From Stdlib Require Import ZArith NArith List Lia String Program Morphisms.
From ITree Require Import ITree Eq.Eqit Interp.InterpFacts Events.State Events.StateFacts.
From ExtLib Require Import Structures.Monads.
From CertiRocq.LambdaANF Require Import term term_util eval identifiers.
From MetaRocq.Common Require Import BasicAst.
From CertiRocq.CodegenLLVM Require Import LambdaANF_to_LLVM_statement LLVM_interp_lemmas LLVM_call_lemmas
     LLVM_exp_lemmas LLVM_mem_lemmas LLVM_instr_lemmas LLVM_toplevel_link.
From CertiRocq.CodegenLLVM Require LLVM_sim_exp.
From Vellvm Require Import
  Utils Syntax Params
  Interfaces.Memory Implementations.Memory
  Semantics.DynamicValues Semantics.LLVMEvents Semantics.Denotation
  Semantics.InterpretationStack Semantics.TopLevel Semantics.Libraries Handlers.
From Vellvm Require Import Utils.IntMaps Semantics.Operations.Gep Semantics.EOU.
Import ListNotations.
Import MonadNotation.
Open Scope monad_scope.
Open Scope Z_scope.
Unset Implicit Arguments.
Set Bullet Behavior "Strict Subproofs".

(* ------------------------------------------------------------------ *)
(** ** [malloc] in Vellvm's concrete memory model *)

(** [malloc] is a memory intrinsic: [interp_intrinsics] passes it through and
    the fused handler runs [handle_intrinsicM]. *)
Lemma interp_mcfg_malloc t args va st rest st' x :
  memS_runs_c st (handle_intrinsicM (Intrinsic t "malloc" args va)) st' x ->
  interp_mcfg (ITree.trigger (subevent _ (Intrinsic t "malloc" args va))) (st, rest) ≈ Ret ((st', rest), x).
Proof.
  intros Hrun.
  unfold interp_mcfg.
  rewrite interp_intrinsics_trigger. cbn.
  rewrite interp_state_trigger. cbn.
  unfold fused_intrinsic, on_mem, handle_intrinsic.
  rewrite (memM_interp_runs_c _ _ _ _ Hrun).
  cbn; rewrite Eqit.bind_ret_l. reflexivity.
Qed.


Lemma handle_malloc_eq t n :
  handle_intrinsicM (Intrinsic t "malloc" [I64 n] None) =
  bind (malloc_bytes (generate_num_poison_bytes (Z.to_N (@Integers.unsigned 64 (Integers.repr n))) (DTYPE_I 8)) 8)
       (fun p => ret (inr (DVALUE_Base (DVALUE_Pointer p)))).
Proof. reflexivity. Qed.

Lemma map_monad_acc_EOU_intro' {A B} (f : A -> EOU.EOU B) l bs :
  Forall2 (fun a b => f a = ret b) l bs -> map_monad_acc f l = ret bs.
Proof.
  intros H. unfold map_monad_acc.
  assert (G : forall acc, (fix loop (acc : list B) (l : list A) : EOU.EOU (list B) :=
       match l with
       | [] => ret (rev_append acc [])
       | a :: l' => b <- f a;; loop (b :: acc) l'
       end) acc l = ret (rev_append acc bs)).
  { induction H as [|a b l bs Hab H IH]; intros acc; [reflexivity|].
    cbn [bind EOU.EOU_monad]. rewrite Hab. cbn. apply IH. }
  apply G.
Qed.

Lemma gcp_exists p n :
  ptr_to_int p + Z.of_N n <= 2 ^ 64 -> exists ptrs, get_consecutive_ptrs p n = ret ptrs.
Proof.
  intros Hn. unfold get_consecutive_ptrs, intptr_seq. rewrite EOU.seq_map_monad_acc_eq, N_to_nat_safe_eq.
  pose proof (ptr_to_int_range p) as Hp.
  assert (Hix : exists ixs, map_monad (from_Z ∘ Z.of_N) (Nseq 0 (N.to_nat n)) = ret ixs /\
                 Forall (fun ix => 0 <= to_Z ix < Z.of_N n) ixs).
  { assert (G : forall len start, (Z.of_N start + Z.of_nat len <= Z.of_N n)%Z ->
              exists ixs, map_monad (from_Z ∘ Z.of_N) (Nseq start len) = ret ixs /\
                 Forall (fun ix => 0 <= to_Z ix < Z.of_N n) ixs).
    { induction len as [|len IH]; intros start Hs; [exists []; split; [reflexivity|constructor]|].
      destruct (IH (N.succ start)) as (ixs & E & F); [lia|].
      assert (Hr : 0 <= Z.of_N start < 2 ^ 64) by lia.
      assert (Ef : exists ix, (from_Z ∘ Z.of_N) start = ret ix /\ to_Z ix = Z.of_N start).
      { cbn. unfold IPtrFinite.from_Z_bits.
        replace ((Z.of_N start <=? @Integers.max_unsigned 64) && (Z.of_N start >=? 0)) with true
          by (symmetry; apply andb_true_iff; split; [apply Z.leb_le; cbn; lia|apply Z.geb_le; lia]).
        eexists; split; [reflexivity|]. apply Integers.unsigned_repr. cbn; lia. }
      destruct Ef as (ix & Ef & Eix).
      exists (ix :: ixs). split.
      - cbn [Nseq map_monad]. cbn [bind EOU.EOU_monad]. rewrite Ef. rewrite E. reflexivity.
      - constructor; [lia|exact F]. }
    apply G. lia. }
  destruct Hix as (ixs & E & F). rewrite E. cbn [bind EOU.EOU_monad].
  assert (G : exists ptrs, Forall2 (fun ix q => handle_gep_ptr (DTYPE_I 8) p [DVALUE_Base (DVALUE_Iptr ix)] = ret q) ixs ptrs).
  { clear E. induction F as [|ix ixs Hix F IH]; [exists []; constructor|].
    destruct IH as (ptrs & H).
    assert (Hr : 0 <= ptr_to_int p + Z.of_N (sizeof_dtyp (DTYPE_I 8)) * to_Z ix < 2 ^ 64).
    { replace (sizeof_dtyp (DTYPE_I 8)) with 1%N by reflexivity. lia. }
    destruct (@int_to_ptr_total _ (ptr_provenance p) Hr) as (q & Eq & _).
    exists (q :: ptrs). constructor; [|exact H]. apply handle_gep_ptr_ix'. rewrite Eq. reflexivity. }
  destruct G as (ptrs & G). exists ptrs. apply map_monad_acc_EOU_intro', G.
Qed.

Lemma next_key_nonneg {A} (m : IntMap A) al : 0 <= next_key_with_alignment m al.
Proof. unfold next_key_with_alignment. destruct IM_greatest_key; lia. Qed.

Lemma malloc_bytes_runs st init :
  let pr := next_provenance (state_provenance st) in
  let a := next_key_with_alignment (mem_of st) 8 in
  a + Z.of_N (N_length init) < 2 ^ 64 ->
  exists p ptrs st',
    memS_runs_c st (malloc_bytes init 8) st' p /\
    ptr_to_int p = a /\
    ptr_provenance p = allocation_id_to_prov (provenance_to_allocation_id pr) /\
    get_consecutive_ptrs p (N_length init) = ret ptrs /\
    state_provenance st' = pr /\
    state_memory_stack st' =
      add_all_to_heap ptrs
        (mkMemoryStack
           (add_all_index_acc (memory_bytes_to_bytes (provenance_to_allocation_id pr) init) a (mem_of st))
           (frames_of st) (heap_of st)).
Proof.
  intros pr a Ha.
  pose proof (next_key_nonneg (mem_of st) 8) as Ha0. fold a in Ha0.
  destruct (@int_to_ptr_total a (allocation_id_to_prov (provenance_to_allocation_id pr))) as (p & Ep & Ep1 & Ep2);
    [pose proof (N2Z.is_nonneg (N_length init)); lia|].
  destruct (gcp_exists p (N_length init)) as (ptrs & Eg); [lia|].
  exists p, ptrs. eexists. split; [|split; [exact Ep1|split; [exact Ep2|split; [exact Eg|split]]]].
  - unfold malloc_bytes, Malloc_bytes_with_pr, get_free_block, add_block_to_heap, add_block,
      add_ptrs_to_heap, get_mem, upd_mem, app_mem, app_mem_stack.
    eapply memS_runs_c_bind; [apply MRC_fresh; apply MRC_ret|].
    change (malloc_bytes_with_pr init 8 ?q) with (Malloc_bytes_with_pr init 8 q).
    unfold Malloc_bytes_with_pr, get_free_block, add_block_to_heap, add_block,
      add_ptrs_to_heap, get_mem, upd_mem, app_mem, app_mem_stack.
    eapply memS_runs_c_bind.
    { eapply memS_runs_c_bind; [apply MRC_next_key, MRC_ret|].
      eapply memS_runs_c_bind.
      { change (mem_of {| state_memory_stack := state_memory_stack st; state_provenance := next_provenance (state_provenance st) |}) with (mem_of st). change (next_key_with_alignment (mem_of st) 8) with a. change (next_provenance (state_provenance st)) with pr. rewrite Ep. apply MRC_ret. }
      eapply memS_runs_c_bind; [rewrite Eg; apply MRC_ret|]. apply MRC_ret. }
    cbn. repeat econstructor.
  - reflexivity.
  - cbn. rewrite <- Ep1. reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(** ** The heap block of a [malloc], and pointer arithmetic *)

Lemma generate_num_poison_bytes_length n t :
  N_length (generate_num_poison_bytes n t) = n.
Proof.
  rewrite N_length_nat.
  unfold generate_num_poison_bytes, generate_num_poison_bytes_h.
  rewrite seq_map_acc_eq, length_map, Nseq_length, N_to_nat_safe_eq. lia.
Qed.

Definition olist {A} (o : option (list A)) : list A := match o with Some l => l | None => [] end.

Lemma lookup_add_with_eq {A} r (v : A) (h : IntMap (list A)) :
  IntMaps.lookup r (add_with r v ret cons h) = Some (v :: olist (IntMaps.lookup r h)).
Proof. unfold add_with. unfold IntMaps.lookup at 2. destruct (IM.find r h); apply lookup_add_eq. Qed.

Lemma lookup_add_with_neq {A} r k (v : A) (h : IntMap (list A)) :
  k <> r -> IntMaps.lookup k (add_with r v ret cons h) = IntMaps.lookup k h.
Proof. intros H. unfold add_with. destruct (IM.find r h); apply lookup_add_neq; congruence. Qed.

Lemma heap_fold (root : ptr) : forall ks ms,
  Memory_stack_memory (add_all_to_heap' ms root ks) = Memory_stack_memory ms /\
  Memory_stack_frame_stack (add_all_to_heap' ms root ks) = Memory_stack_frame_stack ms /\
  (forall k, k <> ptr_to_int root ->
     IntMaps.lookup k (Memory_stack_heap (add_all_to_heap' ms root ks)) = IntMaps.lookup k (Memory_stack_heap ms)) /\
  (ks <> [] -> IntMaps.lookup (ptr_to_int root) (Memory_stack_heap (add_all_to_heap' ms root ks))
               = Some (rev ks ++ olist (IntMaps.lookup (ptr_to_int root) (Memory_stack_heap ms)))%list).
Proof.
  unfold add_all_to_heap'. induction ks as [|k ks IH]; intros ms.
  - cbn. repeat split; auto. intros H; congruence.
  - cbn [fold_left]. destruct (IH (add_to_heap ms root k)) as (E1 & E2 & E3 & E4).
    assert (A1 : Memory_stack_memory (add_to_heap ms root k) = Memory_stack_memory ms /\
                 Memory_stack_frame_stack (add_to_heap ms root k) = Memory_stack_frame_stack ms /\
                 (forall k', k' <> ptr_to_int root ->
                    IntMaps.lookup k' (Memory_stack_heap (add_to_heap ms root k)) = IntMaps.lookup k' (Memory_stack_heap ms)) /\
                 IntMaps.lookup (ptr_to_int root) (Memory_stack_heap (add_to_heap ms root k))
                   = Some (k :: olist (IntMaps.lookup (ptr_to_int root) (Memory_stack_heap ms)))).
    { destruct ms as [m s h]. unfold add_to_heap.
      cbn [Memory_stack_memory Memory_stack_frame_stack Memory_stack_heap].
      split; [reflexivity|split; [reflexivity|split]].
      - intros k' Hk'. apply lookup_add_with_neq. exact Hk'.
      - apply lookup_add_with_eq. }
    destruct A1 as (A1 & A2 & A3 & A4).
    split; [congruence|]. split; [congruence|]. split.
    + intros k' Hk'. rewrite E3 by exact Hk'. apply A3, Hk'.
    + intros _. destruct ks as [|k2 ks'].
      * cbn [fold_left]. rewrite A4. reflexivity.
      * rewrite E4 by discriminate. rewrite A4. cbn [olist]. f_equal.
        change (rev (k :: k2 :: ks')) with (rev (k2 :: ks') ++ [k])%list. rewrite <- app_assoc. reflexivity.
Qed.

Lemma ptr_off_int' p off q : ptr_off p off q -> ptr_to_int q = ptr_to_int p + off.
Proof. unfold ptr_off. intros H. eapply ptr_to_int_int_to_ptr; eauto. Qed.

Lemma ptr_off_prov' p off q : ptr_off p off q -> ptr_provenance q = ptr_provenance p.
Proof. unfold ptr_off. intros H. eapply int_to_ptr_provenance; eauto. Qed.

Lemma ptr_off_det p off q q' : ptr_off p off q -> ptr_off p off q' -> q = q'.
Proof. unfold ptr_off. intros H H'. rewrite H in H'. injection H'. auto. Qed.

Lemma reads_ptr_det' st p q q' : reads_ptr st p q -> reads_ptr st p q' -> q = q'.
Proof.
  intros (s1 & H1) (s2 & H2). destruct (memS_runs_det _ _ _ _ _ _ H1 H2) as [_ E].
  injection E. auto.
Qed.

Lemma field_det' st t off q q' : field st t off q -> field st t off q' -> q = q'.
Proof.
  intros (a & Ha & Hr) (a' & Ha' & Hr').
  rewrite (ptr_off_det _ _ _ _ Ha Ha') in Hr. eapply reads_ptr_det'; eauto.
Qed.

(** [p + o] bytes, keeping [p]'s provenance (total, for use in the runtime's code). *)
Definition off (p : ptr) (o : Z) : ptr :=
  match int_to_ptr (ptr_to_int p + o) (ptr_provenance p) with
  | EOU.raise_ret q => q
  | _ => p
  end.

Lemma off_spec p o : 0 <= ptr_to_int p + o < 2 ^ 64 ->
  ptr_off p o (off p o) /\ ptr_to_int (off p o) = ptr_to_int p + o /\
  ptr_provenance (off p o) = ptr_provenance p.
Proof.
  intros H. destruct (@int_to_ptr_total _ (ptr_provenance p) H) as (q & Eq & E1 & E2).
  unfold off, ptr_off. rewrite Eq. auto.
Qed.

(* ------------------------------------------------------------------ *)
(** ** The witness runtime

    One [malloc]'d block of [nv_block_size] bytes, at address 0 (the first
    allocation in Vellvm's concrete model):
    - bytes [0, 8): unused (so that [thread_info] is not at address 0);
    - bytes [8, 8240): [thread_info] ([alloc] @0, [limit] @8, [fp] @8216,
      [nalloc] @8224 relative to it);
    - bytes [8240, 16432): the nursery, 1024 words.
    [alloc] points to the start of the nursery, [limit] to its end, and the
    frame pointer is the block's base pointer, whose address is 0 (the
    statement's null pointer: the shadow stack is empty).  [nalloc] is left
    uninitialised (the statement only asks for it to be writable). *)

Definition nv_block_size : Z := 8 + 8232 + 8 * 1024.

Definition rt_malloc (n : Z) : MCFGtop (exc + dvalue) :=
  ITree.trigger (subevent _ (Intrinsic DTYPE_Pointer "malloc" [I64 n] None)).

Definition store_ptr (a v : ptr) : MCFGtop unit :=
  ITree.trigger (subevent _ (Store DTYPE_Pointer (DVALUE_Base (DVALUE_Pointer a)) (DVALUE_Base (DVALUE_Pointer v)))).

Definition nv_make_tinfo : MCFGtop dvalue :=
  r <- rt_malloc nv_block_size ;;
  match r with
  | inr (DVALUE_Base (DVALUE_Pointer b)) =>
      let tinfo := off b 8 in
      store_ptr (off tinfo off_alloc) (off b (8 + 8232)) ;;
      store_ptr (off tinfo off_limit) (off b nv_block_size) ;;
      store_ptr (off tinfo off_fp) b ;;
      ret (DVALUE_Base (DVALUE_Pointer tinfo))
  | _ => raiseOOM "nv_make_tinfo: malloc failed"
  end.

Definition nv_gc (args : list dvalue) : MCFGtop (exc + dvalue) :=
  raiseOOM "nv_gc: out of memory".

Definition nv_heap_inv (st : state) (tinfo : ptr) : Prop := True.

(* ------------------------------------------------------------------ *)
(** ** Running the witness *)

Lemma truns_store st rest a v st' :
  memS_runs st (write_dvalue DTYPE_Pointer a (DVALUE_Base (DVALUE_Pointer v))) st' tt ->
  truns (store_ptr a v) (st, rest) (st', rest) tt.
Proof. intros H. unfold truns, store_ptr. apply interp_mcfg_memory. exact H. Qed.

Lemma truns_malloc st rest n st' x :
  memS_runs_c st (handle_intrinsicM (Intrinsic DTYPE_Pointer "malloc" [I64 n] None)) st' x ->
  truns (rt_malloc n) (st, rest) (st', rest) x.
Proof. intros H. unfold truns, rt_malloc. apply interp_mcfg_malloc. exact H. Qed.

Lemma interp_mcfg_raiseOOM {X} msg s : ends_in_oom (interp_mcfg (@raiseOOM MCFGEtop _ X msg) s).
Proof.
  unfold ends_in_oom, raiseOOM, trigger_cast'. eexists. rewrite interp_mcfg_bind.
  unfold interp_mcfg at 1. rewrite interp_intrinsics_trigger. cbn. unfold F_trigger.
  rewrite interp_state_trigger. cbn. destruct (print_msg msg).
  rewrite !Eqit.bind_bind. rewrite bind_trigger. reflexivity.
Qed.

Definition nv_aid : allocationId := provenance_to_allocation_id (next_provenance initial_provenance).

(** The memory after the runtime's [malloc]: one heap block [0, nv_block_size),
    and no other allocated byte. *)
Definition blk_ok (st : state) : Prop :=
  (forall a, 0 <= a < nv_block_size -> aid_at st a = Some nv_aid) /\
  (forall a, in_heap st a <-> 0 <= a < nv_block_size) /\
  frames_of st = Singleton [] /\
  (forall a, IntMaps.lookup a (mem_of st) <> None -> 0 <= a < nv_block_size).

Lemma malloc_initial :
  exists p st1,
    memS_runs_c (fst initial_fused) (handle_intrinsicM (Intrinsic DTYPE_Pointer "malloc" [I64 nv_block_size] None))
                st1 (inr (DVALUE_Base (DVALUE_Pointer p))) /\
    ptr_to_int p = 0 /\ ptr_provenance p = allocation_id_to_prov nv_aid /\ blk_ok st1.
Proof.
  rewrite handle_malloc_eq.
  assert (Hlen : N_length (generate_num_poison_bytes (Z.to_N (@Integers.unsigned 64 (Integers.repr nv_block_size))) (DTYPE_I 8)) = Z.to_N nv_block_size).
  { rewrite generate_num_poison_bytes_length. reflexivity. }
  remember (generate_num_poison_bytes (Z.to_N (@Integers.unsigned 64 (Integers.repr nv_block_size))) (DTYPE_I 8)) as init eqn:Einit.
  clear Einit.
  assert (Hkey : next_key_with_alignment (mem_of (fst initial_fused)) 8 = 0) by reflexivity.
  destruct (malloc_bytes_runs (fst initial_fused) init) as (p & ptrs & st1 & Hrun & Hp & Hprov & Eg & Eprov & Est).
  { cbv zeta. rewrite Hkey, Hlen. cbn. lia. }
  rewrite Hkey in Hp, Est.
  exists p, st1. split; [eapply memS_runs_c_bind; [exact Hrun|apply MRC_ret]|].
  split; [exact Hp|]. split; [exact Hprov|].
  apply gcp_spec in Eg. destruct Eg as [Lp C]. rewrite Hlen in Lp.
  assert (Lz : Z.of_nat (length ptrs) = nv_block_size) by (rewrite Lp; reflexivity).
  destruct ptrs as [|r ptrs'] eqn:Eptrs; [cbn in Lp; discriminate|].
  rewrite <- Eptrs in *.
  set (ms := {| Memory_stack_memory := add_all_index_acc (memory_bytes_to_bytes (provenance_to_allocation_id (next_provenance (state_provenance (fst initial_fused)))) init) 0 (mem_of (fst initial_fused));
                Memory_stack_frame_stack := frames_of (fst initial_fused);
                Memory_stack_heap := heap_of (fst initial_fused) |}) in Est.
  assert (Eh : add_all_to_heap ptrs ms = add_all_to_heap' ms r ptrs) by (rewrite Eptrs; reflexivity).
  destruct (heap_fold r ptrs ms) as (H1 & H2 & H3 & H4).
  rewrite <- Eh in H1, H2, H3, H4. rewrite <- Est in H1, H2, H3, H4.
  assert (Hlb : length (memory_bytes_to_bytes (provenance_to_allocation_id (next_provenance (state_provenance (fst initial_fused)))) init) = Z.to_nat nv_block_size).
  { unfold memory_bytes_to_bytes. rewrite map_acc_eq, length_map. apply Nat2N.inj. rewrite <- N_length_nat, Hlen. reflexivity.
  }
  split; [|split; [|split]].
  - intros a Ha. unfold aid_at, mem_of. rewrite H1. unfold ms. cbn [Memory_stack_memory].
    destruct (add_all_index_acc_in (memory_bytes_to_bytes (provenance_to_allocation_id (next_provenance (state_provenance (fst initial_fused)))) init) 0 (mem_of (fst initial_fused)) a) as (v & Hin & E).
    { rewrite Hlb. lia. }
    rewrite E. unfold memory_bytes_to_bytes in Hin. rewrite map_acc_eq in Hin.
    apply in_map_iff in Hin. destruct Hin as (b & <- & _). reflexivity.
  - intros a. unfold in_heap, heap_of. split.
    + intros (root & blk & Hl & Hin).
      destruct (Z.eq_dec root (ptr_to_int r)) as [->|ne].
      * rewrite H4 in Hl by (rewrite Eptrs; discriminate). injection Hl as <-.
        unfold ms in Hin. cbn [Memory_stack_heap olist] in Hin. rewrite app_nil_r in Hin.
        apply in_map_iff in Hin. destruct Hin as (q & <- & Hq). rewrite <- in_rev in Hq.
        destruct (In_consec _ _ _ C Hq) as (i & Hi & Eq & _). rewrite Eq, Hp. lia.
      * rewrite H3 in Hl by exact ne. cbn in Hl. discriminate.
    + intros Ha. exists (ptr_to_int r).
      eexists. split; [apply H4; rewrite Eptrs; discriminate|].
      destruct (nth_error ptrs (Z.to_nat a)) as [q|] eqn:Eq.
      * apply in_map_iff. exists q. split.
        -- destruct (C _ _ Eq) as [E1 _]. rewrite E1, Hp. lia.
        -- apply in_or_app. left. rewrite <- in_rev. eapply nth_error_In; eauto.
      * apply nth_error_None in Eq. lia.
  - unfold frames_of. rewrite H2. reflexivity.
  - intros a Ha. unfold mem_of in Ha. rewrite H1 in Ha. unfold ms in Ha.
    cbn [Memory_stack_memory] in Ha.
    destruct (Z_lt_le_dec a 0) as [Hlt|Hge]; [|destruct (Z_lt_le_dec a nv_block_size) as [Hlt'|Hge']].
    + rewrite add_all_index_acc_out in Ha by lia. exfalso; apply Ha; reflexivity.
    + lia.
    + rewrite add_all_index_acc_out in Ha by (rewrite Hlb; unfold nv_block_size in *; lia).
      exfalso; apply Ha; reflexivity.
Qed.

Lemma nv_access p : ptr_provenance p = allocation_id_to_prov nv_aid -> access_allowed (ptr_provenance p) nv_aid = true.
Proof. intros ->. reflexivity. Qed.

Lemma nv_access_wild p : ptr_provenance p = wildcard_prov -> access_allowed (ptr_provenance p) nv_aid = true.
Proof. intros ->. reflexivity. Qed.

(** Every word inside the block is writable through a pointer with the
    block's provenance (or a wildcard one). *)
Lemma blk_word_writable st p :
  blk_ok st -> 0 <= ptr_to_int p -> ptr_to_int p + 8 <= nv_block_size ->
  access_allowed (ptr_provenance p) nv_aid = true ->
  word_writable st p.
Proof.
  intros (B1 & _) H0 H1 Hacc.
  destruct (gcp_exists p 8) as (ptrs & Eg); [unfold nv_block_size in H1; lia|].
  exists ptrs. split; [exact Eg|]. intros q Hq.
  apply gcp_spec in Eg. destruct Eg as [L C].
  destruct (In_consec _ _ _ C Hq) as (i & Hi & Eq & Pq).
  rewrite L in Hi. change (N.to_nat 8) with 8%nat in Hi.
  exists nv_aid. split; [apply B1; lia|]. rewrite Pq. exact Hacc.
Qed.

Lemma blk_store st a v :
  blk_ok st -> 0 <= ptr_to_int a -> ptr_to_int a + 8 <= nv_block_size ->
  access_allowed (ptr_provenance a) nv_aid = true ->
  exists st',
    memS_runs st (write_dvalue DTYPE_Pointer a (DVALUE_Base (DVALUE_Pointer v))) st' tt /\
    blk_ok st' /\
    (exists q, reads_ptr st' a q /\ ptr_to_int q = ptr_to_int v /\ ptr_provenance q = wildcard_prov) /\
    (forall b, ~ (ptr_to_int a <= b < ptr_to_int a + 8) ->
       IntMaps.lookup b (mem_of st') = IntMaps.lookup b (mem_of st)).
Proof.
  intros Hb H0 H1 Hacc.
  destruct (blk_word_writable st a Hb H0 H1 Hacc) as (ptrs & Eg & W).
  destruct (write_dvalue_exists st DTYPE_Pointer a (DVALUE_Base (DVALUE_Pointer v)) ptrs) as (st' & Hw);
    [rewrite sizeof_ptr; exact Eg|exact W|].
  exists st'. split; [exact Hw|].
  pose proof (write_dvalue_runs _ _ _ _ _ _ Hw) as (_ & Hout & Haid & _).
  pose proof (write_dvalue_heap _ _ _ _ _ _ Hw) as (Hh & Hf & _).
  split; [|split].
  - destruct Hb as (B1 & B2 & B3 & B4). split; [|split; [|split]].
    + intros b Hb. rewrite Haid. apply B1, Hb.
    + intros b. unfold in_heap. rewrite Hh. apply B2.
    + rewrite Hf. exact B3.
    + intros b Hb. destruct (Z_lt_le_dec b (ptr_to_int a)) as [Hlt|Hge];
        [|destruct (Z_lt_le_dec b (ptr_to_int a + 8)) as [Hlt'|Hge']].
      * apply B4. rewrite <- Hout by (rewrite sizeof_ptr; lia). exact Hb.
      * unfold nv_block_size in *; lia.
      * apply B4. rewrite <- Hout by (rewrite sizeof_ptr; lia). exact Hb.
  - destruct (write_read_ptr _ _ _ _ _ Hw) as (q & Hr & E1 & E2). exists q. auto.
  - intros b Hn. apply Hout. rewrite sizeof_ptr. exact Hn.
Qed.

Lemma same_bytes_of st st' a :
  (forall b, ~ (a <= b < a + 8) -> IntMaps.lookup b (mem_of st') = IntMaps.lookup b (mem_of st)) ->
  forall a', a' + 8 <= a \/ a + 8 <= a' -> same_bytes st st' a' 8.
Proof. intros H a' Ha' b Hb. apply H. lia. Qed.

(** The run of [nv_make_tinfo]. *)
Lemma nv_make_tinfo_runs :
  exists stF t qa ql qf,
    truns nv_make_tinfo initial_fused (stF, snd initial_fused) (DVALUE_Base (DVALUE_Pointer t)) /\
    ptr_to_int t = 8 /\ ptr_provenance t = allocation_id_to_prov nv_aid /\
    blk_ok stF /\
    reads_ptr stF (off t off_alloc) qa /\ ptr_to_int qa = 8 + 8232 /\ ptr_provenance qa = wildcard_prov /\
    reads_ptr stF (off t off_limit) ql /\ ptr_to_int ql = nv_block_size /\
    reads_ptr stF (off t off_fp) qf /\ ptr_to_int qf = 0.
Proof.
  destruct malloc_initial as (p & st1 & Hm & Hp & Hprov & Hb1).
  set (t := off p 8).
  destruct (off_spec p 8) as (_ & Et & Pt); [rewrite Hp; lia|]. fold t in Et, Pt.
  rewrite Hp in Et. rewrite Hprov in Pt.
  destruct (off_spec t off_alloc) as (_ & Ea & Pa); [rewrite Et; unfold off_alloc; lia|].
  destruct (off_spec t off_limit) as (_ & El & Pl); [rewrite Et; unfold off_limit; lia|].
  destruct (off_spec t off_fp) as (_ & Ef & Pf); [rewrite Et; unfold off_fp; lia|].
  destruct (off_spec p (8 + 8232)) as (_ & En & _); [rewrite Hp; lia|].
  destruct (off_spec p nv_block_size) as (_ & Eb & _); [rewrite Hp; unfold nv_block_size; lia|].
  rewrite Et in Ea, El, Ef. rewrite Hp in En, Eb. rewrite Pt in Pa, Pl, Pf.
  unfold off_alloc, off_limit, off_fp in *.
  destruct (blk_store st1 (off t 0) (off p (8 + 8232)) Hb1) as (st2 & W2 & Hb2 & (qa & Ra & Eqa & Pqa) & O2);
    [rewrite Ea; lia|rewrite Ea; unfold nv_block_size; lia|apply nv_access, Pa|].
  destruct (blk_store st2 (off t 8) (off p nv_block_size) Hb2) as (st3 & W3 & Hb3 & (ql & Rl & Eql & _) & O3);
    [rewrite El; lia|rewrite El; unfold nv_block_size; lia|apply nv_access, Pl|].
  destruct (blk_store st3 (off t 8216) p Hb3) as (st4 & W4 & Hb4 & (qf & Rf & Eqf & _) & O4);
    [rewrite Ef; lia|rewrite Ef; unfold nv_block_size; lia|apply nv_access, Pf|].
  exists st4, t, qa, ql, qf.
  split; [|split; [exact Et|split; [exact Pt|split; [exact Hb4|]]]].
  - unfold nv_make_tinfo.
    change initial_fused with (fst initial_fused, snd initial_fused).
    eapply truns_bind; [apply truns_malloc; exact Hm|].
    cbv beta iota zeta. fold t.
    eapply truns_bind; [apply truns_store; exact W2|].
    eapply truns_bind; [apply truns_store; exact W3|].
    eapply truns_bind; [apply truns_store; exact W4|].
    apply truns_ret.
  - split; [|split; [rewrite Eqa; exact En|split; [exact Pqa|split; [|split; [rewrite Eql; exact Eb|split; [exact Rf|rewrite Eqf; exact Hp]]]]]].
    + eapply reads_ptr_frame; [eapply reads_ptr_frame; [exact Ra|]|].
      * eapply same_bytes_of; [exact O3|]. rewrite Ea, El. lia.
      * eapply same_bytes_of; [exact O4|]. rewrite Ea, Ef. lia.
    + eapply reads_ptr_frame; [exact Rl|]. eapply same_bytes_of; [exact O4|]. rewrite El, Ef. lia.
Qed.

(* ------------------------------------------------------------------ *)
(** ** The witness satisfies [runtime_correct] *)

Lemma nv_make_tinfo_returns :
  exists st tinfo fp,
    returns (interp_mcfg nv_make_tinfo initial_fused)
            ((st, snd initial_fused), DVALUE_Base (DVALUE_Pointer tinfo)) /\
    rt_ok nv_heap_inv st tinfo fp [] /\ ptr_to_int fp = 0 /\
    ptr_to_int tinfo + 8232 < 2 ^ 64.
Proof.
  destruct nv_make_tinfo_runs as (st & t & qa & ql & qf & Hrun & Et & Pt & Hb & Ra & Eqa & Pqa & Rl & Eql & Rf & Eqf).
  pose proof Hb as (B1 & B2 & B3 & _).
  assert (Hfield : forall o q, 0 <= o <= 8224 -> reads_ptr st (off t o) q -> field st t o q).
  { intros o q Ho Hr. exists (off t o). split; [|exact Hr]. apply off_spec. rewrite Et. lia. }
  assert (Fa : field st t off_alloc qa) by (apply Hfield; [unfold off_alloc; lia|exact Ra]).
  assert (Fl : field st t off_limit ql) by (apply Hfield; [unfold off_limit; lia|exact Rl]).
  assert (Ff : field st t off_fp qf) by (apply Hfield; [unfold off_fp; lia|exact Rf]).
  exists st, t, qf.
  split; [exact Hrun|]. split; [|split; [exact Eqf|rewrite Et; lia]].
  split; [exact I|]. split; [|split; [|split; [|split; [exact Ff|apply SS_nil, Eqf]]]].
  - (* tinfo_ok *)
    split; [|split].
    + intros o a Hin Ha.
      assert (Ho : 0 <= o <= 8224).
      { unfold off_alloc, off_limit, off_fp, off_nalloc in Hin.
        destruct Hin as [<-|[<-|[<-|[<-|[]]]]]; lia. }
      pose proof (ptr_off_int' _ _ _ Ha) as Ea. pose proof (ptr_off_prov' _ _ _ Ha) as Pa.
      split.
      * apply writable_word_iff. apply blk_word_writable; [exact Hb|rewrite Ea, Et; lia|rewrite Ea, Et; unfold nv_block_size; lia|].
        apply nv_access. rewrite Pa. exact Pt.
      * intros b Hb'. unfold field_addr in Hb'. apply B2. rewrite Et in Hb'. unfold nv_block_size. lia.
    + exists qf, []. split; [exact Ff|]. apply SS_nil, Eqf.
    + exists qa, ql. split; [exact Fa|]. split; [exact Fl|].
      split; [rewrite Eqa; reflexivity|]. split; [rewrite Eqa, Eql; unfold nv_block_size; lia|]. split; [|split].
      * intros a Ha. apply B2. rewrite Eqa, Eql in Ha. lia.
      * intros i q Hi Hq. pose proof (ptr_off_int' _ _ _ Hq) as Eq. pose proof (ptr_off_prov' _ _ _ Hq) as Pq.
        rewrite Eqa, Eql in Hi. unfold nv_block_size in Hi.
        apply writable_word_iff. apply blk_word_writable; [exact Hb|rewrite Eq, Eqa; lia|rewrite Eq, Eqa; unfold nv_block_size; lia|].
        apply nv_access_wild. rewrite Pq. exact Pqa.
      * rewrite Eql. reflexivity.
  - (* mem_ok_stmt *)
    split.
    + intros a Ha. apply B2 in Ha. specialize (B1 a Ha). unfold aid_at in B1.
      destruct (IntMaps.lookup a (mem_of st)); [discriminate|discriminate].
    + intros a Ha. unfold in_frames_stmt in Ha. rewrite B3 in Ha. cbn in Ha. contradiction.
  - (* nursery_tinfo_disjoint_stmt *)
    intros a (alloc & limit & Fa' & Fl' & Ha).
    rewrite (field_det' _ _ _ _ _ Fa' Fa) in Ha. rewrite Eqa in Ha. rewrite Et. lia.
Qed.

Theorem nv_runtime_correct cenv fds :
  runtime_correct cenv fds nv_heap_inv nv_gc nv_make_tinfo.
Proof.
  split; [|split].
  - right. exact nv_make_tinfo_returns.
  - intros. exact I.
  - intros. left. unfold nv_gc. apply interp_mcfg_raiseOOM.
Qed.

(** Our [make_tinfo] does not run out of memory: it takes the [returns]
    branch of the first clause of [runtime_correct]. *)
Lemma nv_make_tinfo_not_oom : ~ ends_in_oom (interp_mcfg nv_make_tinfo initial_fused).
Proof.
  intros (k & Hk). destruct nv_make_tinfo_returns as (st & t & fp & Hret & _).
  unfold returns in Hret. rewrite Hret in Hk. apply eqit_inv in Hk. exact Hk.
Qed.

(* ------------------------------------------------------------------ *)
(** ** A collector that returns

    [nv_gc] above always reports out of memory.  [nv_gc_check] shows that
    the collector clause of [runtime_correct] also admits a collector that
    returns: it reads [alloc], [limit] and [nalloc] from [thread_info] and,
    if the nursery already has [nalloc] free words
    ([limit - alloc >= 8 * nalloc], compared on the integer addresses and the
    unsigned value of the [nalloc] word), returns without touching memory;
    otherwise it reports out of memory.  This is NOT a model of CertiRocq's
    collector (which moves objects to a fresh to-space and updates the
    roots); it only shows that the strengthened clause (bounded [nalloc],
    root slots keeping their allocation ids, frame conditions) can be met by
    a collector that takes the returning branch.  With [nv_make_tinfo]'s
    1024-word nursery, a request that fits is answered by returning. *)

Definition load_dv (t : dtyp) (a : ptr) : MCFGtop dvalue :=
  ITree.trigger (subevent _ (Load t (DVALUE_Base (DVALUE_Pointer a)))).

(** The address of a pointer value, and the unsigned value of an integer. *)
Definition dv_addr (v : dvalue) : Z :=
  match v with DVALUE_Base (DVALUE_Pointer q) => ptr_to_int q | _ => 0 end.

Definition dv_unsigned (v : dvalue) : Z :=
  match v with DVALUE_Base (DVALUE_I _ x) => Integers.unsigned x | _ => 0 end.

Definition nv_gc_check (args : list dvalue) : MCFGtop (exc + dvalue) :=
  match args with
  | [DVALUE_Base (DVALUE_Pointer t)] =>
      va <- load_dv DTYPE_Pointer (off t off_alloc) ;;
      vl <- load_dv DTYPE_Pointer (off t off_limit) ;;
      vn <- load_dv (DTYPE_I 64) (off t off_nalloc) ;;
      if Z.leb (8 * dv_unsigned vn) (dv_addr vl - dv_addr va)
      then ret (inr (DVALUE_Base DVALUE_None))
      else raiseOOM "nv_gc_check: not enough room in the nursery"
  | _ => raiseOOM "nv_gc_check: bad arguments"
  end.

Lemma off_of_ptr_off p o q : ptr_off p o q -> off p o = q.
Proof. unfold ptr_off, off. intros ->. reflexivity. Qed.

Lemma truns_load st rest t a v :
  memS_runs st (read_dvalue t a) st v -> truns (load_dv t a) (st, rest) (st, rest) v.
Proof. intros H. unfold truns, load_dv. apply interp_mcfg_memory. exact H. Qed.

Lemma dv_unsigned_I64 z : 0 <= z < 2 ^ 64 -> dv_unsigned (I64 z) = z.
Proof.
  intros Hz. cbn [dv_unsigned I64]. rewrite unsigned_repr64. apply Z.mod_small, Hz.
Qed.

(** One run of [nv_gc_check] from a state with a well-formed [thread_info]
    and a bounded [nalloc]: it returns without changing anything and there
    is room for [nalloc] words, or it runs out of memory. *)
Lemma nv_gc_check_run (tinfo : ptr) (st : state) rest nalloc :
  tinfo_ok st tinfo -> 0 <= nalloc < 2 ^ 61 ->
  (exists a, ptr_off tinfo off_nalloc a /\ reads_word st a nalloc) ->
  ends_in_oom (interp_mcfg (nv_gc_check [DVALUE_Base (DVALUE_Pointer tinfo)]) (st, rest))
  \/ (returns (interp_mcfg (nv_gc_check [DVALUE_Base (DVALUE_Pointer tinfo)]) (st, rest))
              ((st, rest), inr (DVALUE_Base DVALUE_None)) /\
      room st tinfo nalloc).
Proof.
  intros (_ & _ & alloc & limit & Fa & Fl & _) Hn (an & Han & Rn).
  pose proof Fa as (aa & Haa & Ra). pose proof Fl as (al & Hal & Rl).
  assert (Ta : truns (load_dv DTYPE_Pointer (off tinfo off_alloc)) (st, rest) (st, rest)
                     (DVALUE_Base (DVALUE_Pointer alloc))).
  { rewrite (off_of_ptr_off _ _ _ Haa). apply truns_load, reads_ptr_runs, Ra. }
  assert (Tl : truns (load_dv DTYPE_Pointer (off tinfo off_limit)) (st, rest) (st, rest)
                     (DVALUE_Base (DVALUE_Pointer limit))).
  { rewrite (off_of_ptr_off _ _ _ Hal). apply truns_load, reads_ptr_runs, Rl. }
  assert (Tn : truns (load_dv (DTYPE_I 64) (off tinfo off_nalloc)) (st, rest) (st, rest) (I64 nalloc)).
  { rewrite (off_of_ptr_off _ _ _ Han). apply truns_load, reads_word_runs, Rn. }
  assert (En : dv_unsigned (I64 nalloc) = nalloc) by (apply dv_unsigned_I64; lia).
  destruct (Z.leb (8 * nalloc) (ptr_to_int limit - ptr_to_int alloc)) eqn:Eb.
  - right. split.
    + unfold returns. change (truns (nv_gc_check [DVALUE_Base (DVALUE_Pointer tinfo)]) (st, rest) (st, rest)
                                  (inr (DVALUE_Base DVALUE_None))).
      unfold nv_gc_check.
      eapply truns_bind; [exact Ta|]. eapply truns_bind; [exact Tl|]. eapply truns_bind; [exact Tn|].
      cbn [dv_addr]. rewrite En, Eb. apply truns_ret.
    + exists alloc, limit. split; [exact Fa|]. split; [exact Fl|]. apply Z.leb_le in Eb. lia.
  - left. change (toom (nv_gc_check [DVALUE_Base (DVALUE_Pointer tinfo)]) (st, rest)).
    unfold nv_gc_check.
    eapply toom_bind_r; [exact Ta|]. eapply toom_bind_r; [exact Tl|]. eapply toom_bind_r; [exact Tn|].
    cbn [dv_addr]. rewrite En, Eb. apply interp_mcfg_raiseOOM.
Qed.

(** [nv_gc_check] meets the collector clause, with [st' = st]: every frame
    condition is trivial and [room] comes from the branch condition. *)
Theorem nv_runtime_correct_check cenv fds :
  runtime_correct cenv fds nv_heap_inv nv_gc_check nv_make_tinfo.
Proof.
  split; [|split].
  - right. exact nv_make_tinfo_returns.
  - intros. exact I.
  - intros genv tinfo st ls fp rs vs nalloc Hok_rt Hroots Hn Hna.
    pose proof Hok_rt as (_ & Hok & _).
    destruct (nv_gc_check_run tinfo st (ls, genv) nalloc Hok Hn Hna) as [Ho|(Hr & Hroom)];
      [left; exact Ho|right].
    exists st. split; [exact Hr|]. split; [exact Hok_rt|]. split; [exact Hroots|].
    split; [exact Hroom|]. split; [reflexivity|]. split; [intros; reflexivity|].
    split; [intros a Ha; left; exact Ha|]. intros; reflexivity.
Qed.


(* ------------------------------------------------------------------ *)
(** ** A program: [let x = C in halt x] *)

Definition ex_cenv : ctor_env :=
  M.set 1%positive (Build_ctor_ty_info nAnon nAnon 1%positive 0%N 0%N) (M.empty _).

Definition ex_main : term.exp := Econstr 1%positive 1%positive [] (Ehalt 1%positive).
Definition ex_prog : term.exp := Efun Fnil ex_main.

Lemma ex_get t i : M.get t ex_cenv = Some i -> t = 1%positive /\ i = Build_ctor_ty_info nAnon nAnon 1%positive 0%N 0%N.
Proof.
  unfold ex_cenv. destruct (Pos.eq_dec t 1%positive) as [ -> | ne ].
  - rewrite M.gss. intros H; injection H; auto.
  - rewrite M.gso by exact ne. rewrite M.gempty. discriminate.
Qed.

Lemma ex_restricted : llvm_restricted ex_cenv Fnil ex_main.
Proof.
  split; [|split; [|split; [|split]]].
  - constructor.
  - constructor.
    + split; [eexists; reflexivity|]. split; reflexivity.
    + reflexivity.
    + cbn. lia.
    + constructor.
  - intros (y & Hy). inversion Hy; subst.
    + match goal with H : occurs_free ex_main _ |- _ => inversion H; subst end.
      * match goal with H : In _ [] |- _ => destruct H end.
      * match goal with H : occurs_free (Ehalt _) _ |- _ => inversion H; subst end. congruence.
    + match goal with H : occurs_free_fundefs Fnil _ |- _ => inversion H end.
  - constructor.
    + constructor; [|constructor]. intros Hb. inversion Hb.
    + constructor.
    + constructor. intros z Hz. inversion Hz as [? _ Hf]. inversion Hf.
  - intros t t' i i' Hne Ht Ht'. apply ex_get in Ht, Ht'.
    destruct Ht as [-> _], Ht' as [-> _]. congruence.
Qed.

(** [cenv_ok] is satisfiable the way the pipeline numbers constructors: an
    inductive with a nullary and a boxed constructor, both of ordinal 0
    (as [nat]'s [O] and [S]). *)
Definition nat_cenv : ctor_env :=
  M.set 2%positive (Build_ctor_ty_info nAnon nAnon 1%positive 1%N 0%N)
    (M.set 1%positive (Build_ctor_ty_info nAnon nAnon 1%positive 0%N 0%N) (M.empty _)).

Lemma nat_cenv_ok : cenv_ok nat_cenv.
Proof.
  assert (G : forall t i, M.get t nat_cenv = Some i ->
            (t = 1%positive /\ i = Build_ctor_ty_info nAnon nAnon 1%positive 0%N 0%N) \/
            (t = 2%positive /\ i = Build_ctor_ty_info nAnon nAnon 1%positive 1%N 0%N)).
  { intros t i. unfold nat_cenv.
    destruct (Pos.eq_dec t 2%positive) as [->|ne2]; [rewrite M.gss; intros H; injection H as <-; auto|].
    rewrite M.gso by exact ne2.
    destruct (Pos.eq_dec t 1%positive) as [->|ne1]; [rewrite M.gss; intros H; injection H as <-; auto|].
    rewrite M.gso by exact ne1. rewrite M.gempty. discriminate. }
  intros t t' i i' Hne Ht Ht'.
  destruct (G _ _ Ht) as [[-> ->]|[-> ->]], (G _ _ Ht') as [[-> ->]|[-> ->]]; cbn;
    try congruence; intros _ _; split; intros; lia.
Qed.

Lemma ex_eval (pfs : prims) : bstep_e pfs ex_cenv (M.empty _) ex_prog (Vconstr 1%positive []) 0.
Proof.
  apply BStep_fun. cbn. eapply BStep_constr; [reflexivity|reflexivity|]. apply BStep_halt. reflexivity.
Qed.

(** All hypotheses of [LambdaANF_to_LLVM_correct_statement] hold for this
    program and the witness runtime, so its conclusion is really asserted. *)
Theorem ex_hypotheses (pfs : prims) :
  runtime_correct ex_cenv Fnil nv_heap_inv nv_gc nv_make_tinfo /\
  llvm_restricted ex_cenv Fnil ex_main /\
  bstep_e pfs ex_cenv (M.empty _) ex_prog (Vconstr 1%positive []) 0.
Proof. split; [apply nv_runtime_correct|split; [apply ex_restricted|apply ex_eval]]. Qed.

(** What the theorem then says about the compiled program: out of memory, or
    it returns [1] (the unboxed representation [0 * 2 + 1] of the nullary
    constructor).  An instance of [LLVM_sim_exp.LambdaANF_to_LLVM_correct]. *)
Theorem ex_correct (pfs : prims) (prim_of : positive -> option (string * bool)) :
  ends_in_oom (run_program nv_gc nv_make_tinfo (emitted ex_cenv prim_of ex_prog))
  \/ exists st ls genv,
      returns (run_program nv_gc nv_make_tinfo (emitted ex_cenv prim_of ex_prog))
              ((st, (ls, genv)), I64 1).
Proof.
  destruct (ex_hypotheses pfs) as (Hrt & Hprog & Hev).
  destruct (LLVM_sim_exp.LambdaANF_to_LLVM_correct ex_cenv pfs prim_of nv_heap_inv nv_gc nv_make_tinfo
              Fnil ex_main (Vconstr 1%positive []) 0%nat Hrt Hprog Hev) as [Ho|(st & ls & genv & z & Hr & Hrep)].
  - left. exact Ho.
  - right. exists st, ls, genv. inversion Hrep; subst; [|congruence]. exact Hr.
Qed.

(* ------------------------------------------------------------------ *)
(** ** The vacuous runtime the statement also admits *)

(** A [make_tinfo] that immediately runs out of memory satisfies
    [runtime_correct] (first clause, left disjunct), and then every program
    trivially satisfies the conclusion of the theorem (its OOM disjunct).
    The witness above avoids this ([nv_make_tinfo_not_oom]). *)
Definition oom_make_tinfo : MCFGtop dvalue := raiseOOM "no thread_info".

Lemma oom_runtime_correct cenv fds :
  runtime_correct cenv fds nv_heap_inv nv_gc oom_make_tinfo.
Proof.
  split; [|split].
  - left. apply interp_mcfg_raiseOOM.
  - intros. exact I.
  - intros. left. unfold nv_gc. apply interp_mcfg_raiseOOM.
Qed.

Lemma oom_runtime_vacuous cenv prim_of e :
  ends_in_oom (run_program nv_gc oom_make_tinfo (emitted cenv prim_of e)).
Proof. unfold run_program. apply toom_bind_l. apply interp_mcfg_raiseOOM. Qed.
