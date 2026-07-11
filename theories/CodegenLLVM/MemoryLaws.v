(* ------------------------------------------------------------------ *)
(*  Phase-2 VIR proof: the local [MemoryModelLaws] interface,          *)
(*  discharged against Vellvm v3.0's concrete [MemoryModelPrimitivesV] *)
(*  (Semantics/Implementations/Memory.v).                              *)
(*                                                                     *)
(*  The four laws are stated over a small big-step [Runs] relation on  *)
(*  the syntactic memory monad [memS] (Interfaces/Memory.v), and       *)
(*  reduce to [IM.find]/[IM.add] map algebra + the [access_allowed]    *)
(*  guard.                                                             *)
(* ------------------------------------------------------------------ *)

From Stdlib Require Import ZArith NArith List Lia.
From ExtLib Require Import Structures.Monad.

(* L3 support imports.  Placed BEFORE the memory-model imports below so   *)
(* that the monadic [get]/[put] re-exported by Interfaces.Memory /        *)
(* Implementations.Memory win name resolution (some of these modules      *)
(* introduce an unrelated [get] that would otherwise shadow it).          *)
From Vellvm Require Import Utils.ListUtil.
From Vellvm Require Import Numeric.Rocqlib.
From Vellvm Require Import Semantics.EOU.
From Vellvm Require Import Semantics.Operations.Gep.
From Vellvm Require Import Semantics.MemoryBytes.

From Vellvm Require Import Syntax.
From Vellvm Require Import Params.
From Vellvm Require Import Interfaces.Memory.
From Vellvm Require Import Semantics.Implementations.Memory.
From Vellvm Require Import Utils.IntMaps.

Import Monad.
Import ListNotations.

Set Bullet Behavior "Strict Subproofs".

(* ================================================================== *)
(*  Generic list helpers (no [Params] needed), imported for L3.       *)
(* ================================================================== *)

Lemma Forall2_nth_error :
  forall {A B} (R : A -> B -> Prop) l1 l2 i a,
    Forall2 R l1 l2 ->
    nth_error l1 i = Some a ->
    exists b, nth_error l2 i = Some b /\ R a b.
Proof.
  intros A B R l1 l2 i a HF. revert i a.
  induction HF as [| x y l1' l2' Hxy HF IH]; intros i a Hnth.
  - destruct i; cbn in Hnth; discriminate.
  - destruct i; cbn in Hnth.
    + inversion Hnth; subst. exists y. split; [reflexivity | exact Hxy].
    + apply IH. exact Hnth.
Qed.

Lemma nth_error_Nseq :
  forall len start i,
    (i < len)%nat ->
    nth_error (Nseq start len) i = Some (start + N.of_nat i)%N.
Proof.
  induction len as [| len IH]; intros start i Hi; [lia|].
  destruct i; cbn [Nseq nth_error].
  - f_equal; lia.
  - rewrite IH by lia. f_equal; lia.
Qed.

Lemma list_nth_z_nth_error :
  forall {A} (l : list A) i,
    list_nth_z l (Z.of_nat i) = nth_error l i.
Proof.
  induction l as [| x l IH]; intros i; destruct i as [| j]; cbn [list_nth_z nth_error].
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - destruct (zeq (Z.of_nat (S j)) 0) as [E | _]; [lia|].
    replace (Z.pred (Z.of_nat (S j))) with (Z.of_nat j) by lia.
    apply IH.
Qed.

Lemma N_to_nat_length :
  forall {A} (l : list A), N.to_nat (N.length l) = Datatypes.length l.
Proof.
  induction l as [| x l IH]; cbn [N.length Datatypes.length]; [reflexivity|].
  rewrite <- IH. lia.
Qed.

(* ================================================================== *)
(*  L4 frontier support (inlined verbatim from MemoryLaws_L4.v).       *)
(*                                                                     *)
(*  [next_key_with_alignment] is the concrete value Vellvm's           *)
(*  [Mnext_key] handler returns (Semantics/Handlers/Memory.v:48-58).   *)
(*  Under this file's NON-deterministic [Runs] (RunsNext picks an      *)
(*  arbitrary key) the fact that the allocated [ptr] sits at that      *)
(*  value is NOT derivable, so for L4 it is supplied as an explicit    *)
(*  premise -- a genuine precondition satisfied by the concrete        *)
(*  interpreter (and proved outright in MemoryLaws_L4.v).              *)
(* ================================================================== *)

Definition pad_amount (align : N) (offset : N) : N :=
  ((align - (offset mod align)) mod align)%N.

Definition pad_to (align : N) (sz : N) : N :=
  (sz + pad_amount align sz)%N.

Definition next_key_with_alignment {A} (m : IntMap A) (align : N) : Z :=
  match IM_greatest_key m with
  | Some k => Z.of_N (pad_to align (1 + Z.to_N k))
  | None => 0
  end.

(* The concrete [next_key] value is strictly above every present key.  *)
Lemma next_key_with_alignment_gt :
  forall {A} (m : IntMap A) (align : N) (a : Z),
    IM.In a m ->
    (a < next_key_with_alignment m align)%Z.
Proof.
  intros A m align a IN.
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

Section MemoryLaws.
  Context {Pa : Params}.

  (* The concrete memory-model state / primitives instances. *)
  Existing Instance MemoryModelStateV.
  Existing Instance MemoryModelPrimitivesV.

  (* The concrete state type and the memory it carries. *)
  Notation ST := (@state Pa MemoryModelStateV).
  Notation MM := (@memS ST addr provenance).

  (* The IntMap of bytes stored in a state. *)
  Definition memOf (s : ST) : memory :=
    Memory_stack_memory (state_get_memory s).

  (* ---------------------------------------------------------------- *)
  (*  Big-step evaluation of the syntactic monad [memS].              *)
  (*  [Runs s op s' r]: folding [op]'s continuations from state [s]   *)
  (*  terminates in [Mret r] with final state [s'].  The              *)
  (*  UB/OOM/error leaves ([Mub]/[Moom]/[Merr]) have no rule, i.e.    *)
  (*  they do not "run" -- exactly the notion of a *successful* run.  *)
  (*  [Mnext_key]/[Mfresh_prov] are relationally non-deterministic:   *)
  (*  any key / provenance the handler could return is admitted.      *)
  (* ---------------------------------------------------------------- *)
  Inductive Runs {X : Type} : ST -> MM X -> ST -> X -> Prop :=
  | RunsRet   : forall s x, Runs s (Mret x) s x
  | RunsGet   : forall s (k : ST -> MM X) s' r,
      Runs s (k s) s' r -> Runs s (Mget k) s' r
  | RunsPut   : forall s sigma (k : MM X) s' r,
      Runs sigma k s' r -> Runs s (Mput sigma k) s' r
  | RunsNext  : forall s sz al (a : Z) (k : Z -> MM X) s' r,
      Runs s (k a) s' r -> Runs s (Mnext_key sz al k) s' r
  | RunsFresh : forall s (p : provenance) (k : provenance -> MM X) s' r,
      Runs s (k p) s' r -> Runs s (Mfresh_prov k) s' r.

  (* ------------------------- inversion helpers -------------------- *)
  Lemma inv_ret : forall X s s' (x r : X),
      Runs s (Mret x) s' r -> s' = s /\ r = x.
  Proof. intros X s s' x r H; inversion H; subst; auto. Qed.

  Lemma inv_get : forall X (k : ST -> MM X) s s' r,
      Runs s (Mget k) s' r -> Runs s (k s) s' r.
  Proof. intros X k s s' r H; inversion H; subst; auto. Qed.

  Lemma inv_put : forall X sigma (k : MM X) s s' r,
      Runs s (Mput sigma k) s' r -> Runs sigma k s' r.
  Proof. intros X sigma k s s' r H; inversion H; subst; auto. Qed.

  Lemma inv_next : forall X sz al (k : Z -> MM X) s s' r,
      Runs s (Mnext_key sz al k) s' r -> exists a, Runs s (k a) s' r.
  Proof. intros X sz al k s s' r H; inversion H; subst; eauto. Qed.

  Lemma inv_fresh : forall X (k : provenance -> MM X) s s' r,
      Runs s (Mfresh_prov k) s' r -> exists p, Runs s (k p) s' r.
  Proof. intros X k s s' r H; inversion H; subst; eauto. Qed.

  Lemma inv_ub : forall X s s' (r : X) msg, Runs s (Mub msg) s' r -> False.
  Proof. intros X s s' r msg H; inversion H. Qed.

  Lemma inv_oom : forall X s s' (r : X) msg, Runs s (Moom msg) s' r -> False.
  Proof. intros X s s' r msg H; inversion H. Qed.

  Lemma inv_err : forall X s s' (r : X) msg, Runs s (Merr msg) s' r -> False.
  Proof. intros X s s' r msg H; inversion H. Qed.

  (* -------------------------- bind algebra ------------------------ *)
  (* The class-level [bind] on [memS] is definitionally [memS_bind]. *)
  Lemma bind_is_memS : forall X Y (c : MM X) (k : X -> MM Y),
      bind c k = memS_bind c k.
  Proof. reflexivity. Qed.

  Lemma Runs_bind : forall X Y (c : MM X) (k : X -> MM Y) s s1 x s' r,
      Runs s c s1 x -> Runs s1 (k x) s' r -> Runs s (memS_bind c k) s' r.
  Proof.
    intros X Y c k s s1 x s' r Hc. revert Y k s' r.
    induction Hc; intros Yr kk sf rr Hk; cbn [memS_bind].
    - exact Hk.
    - apply RunsGet. apply IHHc. exact Hk.
    - apply RunsPut. apply IHHc. exact Hk.
    - eapply RunsNext. apply IHHc. exact Hk.
    - eapply RunsFresh. apply IHHc. exact Hk.
  Qed.

  Lemma Runs_bind_inv : forall X Y (c : MM X) (k : X -> MM Y) s s' r,
      Runs s (memS_bind c k) s' r ->
      exists s1 x, Runs s c s1 x /\ Runs s1 (k x) s' r.
  Proof.
    intros X Y c. revert Y.
    induction c; intros Yr k0 si so ro Hd; cbn [memS_bind] in Hd.
    - exists si, x. split; [constructor | exact Hd].
    - apply inv_oom in Hd; contradiction.
    - apply inv_ub in Hd; contradiction.
    - apply inv_err in Hd; contradiction.
    - apply inv_get in Hd.
      edestruct H as (s1 & x & Hc & Hk); [exact Hd|].
      exists s1, x. split; [apply RunsGet; exact Hc | exact Hk].
    - apply inv_put in Hd.
      edestruct IHc as (s1 & x & Hc & Hk); [exact Hd|].
      exists s1, x. split; [apply RunsPut; exact Hc | exact Hk].
    - apply inv_next in Hd. destruct Hd as [a Hd].
      edestruct H as (s1 & x & Hc & Hk); [exact Hd|].
      exists s1, x. split; [eapply RunsNext; exact Hc | exact Hk].
    - apply inv_fresh in Hd. destruct Hd as [p Hd].
      edestruct H as (s1 & x & Hc & Hk); [exact Hd|].
      exists s1, x. split; [eapply RunsFresh; exact Hc | exact Hk].
  Qed.

  (* Convenient: convert the class-level [bind] appearing in the       *)
  (* concrete op bodies into [memS_bind] before decomposing/composing. *)
  Ltac to_memS := repeat rewrite bind_is_memS in *.

  (* ------------------------- primitive runs ----------------------- *)
  Lemma Runs_ret : forall X s (x : X), Runs s (ret x) s x.
  Proof. intros; apply RunsRet. Qed.

  Lemma Runs_get : forall s, Runs s (get : MM ST) s s.
  Proof. intros s; apply RunsGet; apply RunsRet. Qed.

  Lemma Runs_put : forall s sigma, Runs s (put sigma : MM unit) sigma tt.
  Proof. intros s sigma; apply RunsPut; apply RunsRet. Qed.

  (* Reading the raw byte map: forward and inversion. *)
  Lemma Runs_read_byte_raw_Some : forall s msg pa v,
      read_byte_raw_mem (memOf s) pa = Some v ->
      Runs s (read_byte_raw msg pa) s v.
  Proof.
    intros s msg pa v H. unfold read_byte_raw. to_memS.
    eapply Runs_bind; [apply Runs_get|].
    unfold memOf in H. cbn beta. rewrite H. apply RunsRet.
  Qed.

  Lemma Runs_read_byte_raw_inv : forall s msg pa s' v,
      Runs s (read_byte_raw msg pa) s' v ->
      s' = s /\ read_byte_raw_mem (memOf s) pa = Some v.
  Proof.
    intros s msg pa s' v H. unfold read_byte_raw in H. to_memS.
    apply Runs_bind_inv in H. destruct H as (s1 & x & Hget & Hrest).
    apply inv_get in Hget. apply inv_ret in Hget. destruct Hget; subst.
    cbn beta in Hrest. unfold memOf.
    destruct (read_byte_raw_mem (Memory_stack_memory (state_get_memory s)) pa) eqn:E.
    - apply inv_ret in Hrest. destruct Hrest; subst. auto.
    - apply inv_ub in Hrest; contradiction.
  Qed.

  (* [set_byte_raw pa v] overwrites key [pa] with [v] in the byte map. *)
  Lemma Runs_set_byte_raw_inv : forall s pa v s' u,
      Runs s (set_byte_raw pa v) s' u ->
      memOf s' = IM.add pa v (memOf s).
  Proof.
    intros s pa v s' u H.
    unfold set_byte_raw, get_mem, upd_mem, app_mem in H. to_memS.
    apply Runs_bind_inv in H. destruct H as (s1 & m & Hgm & Hupd).
    (* get_mem runs get then returns the memory of s *)
    apply Runs_bind_inv in Hgm. destruct Hgm as (sa & sx & Hget & Hret).
    apply inv_get in Hget. apply inv_ret in Hget. destruct Hget; subst.
    apply inv_ret in Hret. destruct Hret; subst.
    (* upd_mem: get then put the new state *)
    apply Runs_bind_inv in Hupd. destruct Hupd as (sb & sy & Hget2 & Hput).
    apply inv_get in Hget2. apply inv_ret in Hget2. destruct Hget2; subst.
    apply inv_put in Hput. apply inv_ret in Hput. destruct Hput; subst.
    unfold memOf. cbn. unfold set_byte_raw_mem. reflexivity.
  Qed.

  (* ================================================================ *)
  (*  L1  read_write_eq : read-your-write at the same address         *)
  (* ================================================================ *)

  (* Decompose a successful [Write_byte]: it found some [(mb,aid)] at  *)
  (* the key, the [access_allowed] guard held, and the resulting map   *)
  (* has [(b,aid)] at that key.                                        *)
  Lemma Write_byte_inv : forall s a b s' u,
      Runs s (Write_byte a b) s' u ->
      exists mb aid,
        read_byte_raw_mem (memOf s) (ptr_to_int a) = Some (mb, aid) /\
        access_allowed (address_provenance a) aid = true /\
        memOf s' = IM.add (ptr_to_int a) (b, aid) (memOf s).
  Proof.
    intros s a b s' u H. unfold Write_byte in H. to_memS.
    apply Runs_bind_inv in H. destruct H as (s1 & pr & Hrd & Hrest).
    apply Runs_read_byte_raw_inv in Hrd. destruct Hrd as [Hs1 Hfind]; subst s1.
    destruct pr as [mb aid].
    cbn in Hrest.
    destruct (access_allowed (address_provenance a) aid) eqn:Hga.
    - apply Runs_set_byte_raw_inv in Hrest.
      exists mb, aid. repeat split; auto.
    - apply inv_ub in Hrest; contradiction.
  Qed.

  Lemma L1_read_write_eq : forall s s' a b,
      Runs s (Write_byte a b) s' tt ->
      Runs s' (Read_byte a) s' b.
  Proof.
    intros s s' a b H. apply Write_byte_inv in H.
    destruct H as (mb & aid & Hfind & Hga & Hmem).
    unfold Read_byte. to_memS.
    eapply Runs_bind.
    - apply Runs_read_byte_raw_Some with (v := (b, aid)).
      unfold read_byte_raw_mem. rewrite Hmem.
      rewrite IntMaps.IP.F.add_eq_o; reflexivity.
    - cbn. rewrite Hga. apply RunsRet.
  Qed.

  (* ================================================================ *)
  (*  L2  write_read_neq : a disjoint write does not disturb a read    *)
  (* ================================================================ *)

  Lemma L2_write_read_neq : forall s s' a1 a2 b2 r1,
      ptr_to_int a1 <> ptr_to_int a2 ->
      Runs s  (Read_byte a1) s  r1 ->
      Runs s  (Write_byte a2 b2) s' tt ->
      Runs s' (Read_byte a1) s' r1.
  Proof.
    intros s s' a1 a2 b2 r1 Hneq Hrd Hwr.
    (* Decompose the read at a1 in s. *)
    unfold Read_byte in Hrd. to_memS.
    apply Runs_bind_inv in Hrd. destruct Hrd as (sa & pr & Hrd1 & Hrest).
    apply Runs_read_byte_raw_inv in Hrd1. destruct Hrd1 as [Hsa Hfind1]; subst sa.
    destruct pr as [mb1 aid1].
    cbn in Hrest.
    destruct (access_allowed (address_provenance a1) aid1) eqn:Hg1;
      [| apply inv_ub in Hrest; contradiction ].
    apply inv_ret in Hrest. destruct Hrest as [_ Hr1]; subst r1.
    (* Decompose the write at a2. *)
    apply Write_byte_inv in Hwr. destruct Hwr as (mb2 & aid2 & _ & _ & Hmem').
    (* Reconstruct the read at a1 in s'. *)
    unfold Read_byte. to_memS.
    eapply Runs_bind.
    - apply Runs_read_byte_raw_Some with (v := (mb1, aid1)).
      unfold read_byte_raw_mem. rewrite Hmem'.
      rewrite IntMaps.IP.F.add_neq_o by (apply not_eq_sym; exact Hneq).
      unfold read_byte_raw_mem in Hfind1. exact Hfind1.
    - cbn. rewrite Hg1. apply RunsRet.
  Qed.

  (* ================================================================ *)
  (*  L3  allocate_read_new  -- CLOSED (ported from MemoryLaws_L3.v)   *)
  (* ================================================================ *)
  (* [Allocate_bytes_with_pr] runs [get_free_block], whose              *)
  (* [get_consecutive_ptrs ptr size = intptr_seq 0 size >>= map_monad   *)
  (*  (fun ix => handle_gep_addr (DTYPE_I 8) ptr [DVALUE_Iptr ix])].    *)
  (*   - [add_block]'s effect is [add_all_index (map (.,aid) init)      *)
  (*     (ptr_to_int ptr) (memOf s)]; the byte at key [ptr_to_int ptr+i]*)
  (*     is [(init[i], aid)] by [lookup_add_all_index_in] (IntMaps.v);  *)
  (*   - the i-th consecutive pointer has key [ptr_to_int ptr + i]      *)
  (*     ([handle_gep_addr_ix] + [sizeof_dtyp (DTYPE_I 8) = 1]) and     *)
  (*     provenance [address_provenance ptr]                            *)
  (*     ([handle_gep_addr_preserves_provenance], Operations/Gep.v);    *)
  (*   - the read guard is then [access_allowed_refl].                  *)
  (* The [intptr_seq]/[map_monad] nth spec and the [lift : EOU ~> memM] *)
  (* run inversion are supplied by the helper lemmas below.             *)

  (* ---- PIECE (1): the [intptr_seq]/[get_consecutive_ptrs] nth spec ---*)
  Lemma intptr_seq_nth : forall size ixs i,
      intptr_seq 0 size = ret ixs ->
      (i < N.to_nat size)%nat ->
      exists ix, nth_error ixs i = Some ix /\ to_Z ix = Z.of_nat i.
  Proof.
    intros size ixs i Hseq Hi.
    unfold intptr_seq in Hseq.
    apply map_monad_EOU_Forall2 in Hseq.
    assert (Hn : nth_error (Nseq 0 (N.to_nat size)) i = Some (0 + N.of_nat i)%N)
      by (apply nth_error_Nseq; exact Hi).
    eapply Forall2_nth_error in Hseq; [| exact Hn].
    destruct Hseq as [ix [Hix Hf]].
    exists ix. split; [exact Hix|].
    unfold Basics.compose in Hf.
    apply from_Z_to_Z in Hf.
    rewrite Hf. lia.
  Qed.

  Lemma get_consecutive_ptrs_nth :
    forall (ptr : addr) (size : N) (ptrs : list addr) (i : nat),
      get_consecutive_ptrs ptr size = ret ptrs ->
      (i < N.to_nat size)%nat ->
      exists a_i,
        nth_error ptrs i = Some a_i /\
        ptr_to_int a_i = (ptr_to_int ptr + Z.of_nat i)%Z /\
        address_provenance a_i = address_provenance ptr.
  Proof.
    intros ptr size ptrs i Hgcp Hi.
    unfold get_consecutive_ptrs in Hgcp.
    destruct (intptr_seq 0 size) as [se | so | su | ixs] eqn:Hseq;
      cbn in Hgcp; try discriminate.
    destruct (intptr_seq_nth size ixs i Hseq Hi) as [ix [Hixnth HtoZ]].
    apply map_monad_EOU_Forall2 in Hgcp.
    eapply Forall2_nth_error in Hgcp; [| exact Hixnth].
    destruct Hgcp as [a_i [Hnth Hgep]].
    exists a_i. split; [exact Hnth|].
    split.
    - apply ptr_to_int_int_to_ptr in Hgep.
      rewrite Hgep, sizeof_dtyp_i8, HtoZ. lia.
    - eapply int_to_ptr_provenance. exact Hgep.
  Qed.

  (* ---- PIECE (2): [lookup_add_all_index_in] specialised ------------ *)
  Lemma find_add_all_index_map_nth :
    forall (aid : allocationId) (init : list memory_byte) (base : Z)
           (i : nat) (b : memory_byte) (mem : memory),
      nth_error init i = Some b ->
      IM.find (base + Z.of_nat i)%Z
        (add_all_index (memory_bytes_to_bytes aid init) base mem)
      = Some (b, aid).
  Proof.
    intros aid init base i b mem Hnth.
    assert (Hi : (i < Datatypes.length init)%nat)
      by (apply nth_error_Some; rewrite Hnth; discriminate).
    replace (IM.find (base + Z.of_nat i)%Z
               (add_all_index (memory_bytes_to_bytes aid init) base mem))
      with (lookup (base + Z.of_nat i)%Z
              (add_all_index (memory_bytes_to_bytes aid init) base mem))
      by reflexivity.
    apply lookup_add_all_index_in.
    - unfold memory_bytes_to_bytes.
      rewrite Zlength_correct, length_map.
      apply inj_lt in Hi. lia.
    - replace (base + Z.of_nat i - base)%Z with (Z.of_nat i) by lia.
      unfold memory_bytes_to_bytes.
      rewrite list_nth_z_map, list_nth_z_nth_error, Hnth. reflexivity.
  Qed.

  (* ---- PIECE (3): decompose a successful [Allocate_bytes_with_pr] --- *)

  (* A successfully-run [lift c] forces [c] to be [raise_ret r].       *)
  Lemma inv_lift : forall X (c : EOU X) s s' (r : X),
      Runs s (lift c) s' r -> c = raise_ret r /\ s' = s.
  Proof.
    intros X c s s' r H. destruct c; cbn in H.
    - apply inv_err in H; contradiction.
    - apply inv_oom in H; contradiction.
    - apply inv_ub in H; contradiction.
    - apply inv_ret in H. destruct H; subst; auto.
  Qed.

  (* [get_mem] returns the current byte map, unchanged. *)
  Lemma Runs_get_mem_inv : forall s s' m,
      Runs s get_mem s' m -> s' = s /\ m = memOf s.
  Proof.
    intros s s' m H. unfold get_mem in H. to_memS.
    apply Runs_bind_inv in H. destruct H as (s1 & x & Hget & Hret).
    apply inv_get in Hget. apply inv_ret in Hget. destruct Hget; subst.
    apply inv_ret in Hret. destruct Hret; subst. unfold memOf. auto.
  Qed.

  (* [upd_mem m] installs [m] as the byte map. *)
  Lemma Runs_upd_mem_inv : forall s s' m u,
      Runs s (upd_mem m) s' u -> memOf s' = m.
  Proof.
    intros s s' m u H. unfold upd_mem, app_mem in H. to_memS.
    apply Runs_bind_inv in H. destruct H as (s1 & x & Hget & Hput).
    apply inv_get in Hget. apply inv_ret in Hget. destruct Hget; subst.
    apply inv_put in Hput. apply inv_ret in Hput. destruct Hput; subst.
    unfold memOf. cbn. reflexivity.
  Qed.

  (* [add_block] writes the [init] bytes at [ptr_to_int ptr .. +len). *)
  Lemma Runs_add_block_inv : forall s s' aid ptr ptrs init u,
      Runs s (add_block aid ptr ptrs init) s' u ->
      memOf s' =
        add_all_index (memory_bytes_to_bytes aid init) (ptr_to_int ptr) (memOf s).
  Proof.
    intros s s' aid ptr ptrs init u H. unfold add_block in H. to_memS.
    apply Runs_bind_inv in H. destruct H as (s1 & m & Hgm & Hupd).
    apply Runs_get_mem_inv in Hgm. destruct Hgm as [Hs1 Hm]. subst.
    apply Runs_upd_mem_inv in Hupd. exact Hupd.
  Qed.

  (* Registering pointers in a frame does not touch the byte map. *)
  Lemma add_to_frame_mem : forall ms k,
      Memory_stack_memory (add_to_frame ms k) = Memory_stack_memory ms.
  Proof. intros [m s h] k. destruct s; reflexivity. Qed.

  Lemma add_all_to_frame_mem : forall ks ms,
      Memory_stack_memory (add_all_to_frame ks ms) = Memory_stack_memory ms.
  Proof.
    unfold add_all_to_frame. induction ks as [| k ks IH]; intros ms; cbn; auto.
    rewrite IH. apply add_to_frame_mem.
  Qed.

  Lemma Runs_add_ptrs_to_frame_inv : forall s s' ptrs u,
      Runs s (add_ptrs_to_frame ptrs) s' u -> memOf s' = memOf s.
  Proof.
    intros s s' ptrs u H. unfold add_ptrs_to_frame, app_mem_stack in H. to_memS.
    apply Runs_bind_inv in H. destruct H as (s1 & x & Hget & Hput).
    apply inv_get in Hget. apply inv_ret in Hget. destruct Hget; subst.
    apply inv_put in Hput. apply inv_ret in Hput. destruct Hput; subst.
    unfold memOf. cbn. apply add_all_to_frame_mem.
  Qed.

  (* [add_block_to_stack] has the same byte-map effect as [add_block]. *)
  Lemma Runs_add_block_to_stack_inv : forall s s' aid ptr ptrs init u,
      Runs s (add_block_to_stack aid ptr ptrs init) s' u ->
      memOf s' =
        add_all_index (memory_bytes_to_bytes aid init) (ptr_to_int ptr) (memOf s).
  Proof.
    intros s s' aid ptr ptrs init u H. unfold add_block_to_stack in H. to_memS.
    apply Runs_bind_inv in H. destruct H as (s1 & u1 & Hab & Haf).
    apply Runs_add_block_inv in Hab.
    apply Runs_add_ptrs_to_frame_inv in Haf.
    rewrite Haf, Hab. reflexivity.
  Qed.

  (* [get_free_block] is state-preserving, picks a [ptr] with the      *)
  (* allocation's provenance, and succeeds at [get_consecutive_ptrs].  *)
  Lemma get_free_block_inv :
    forall s s' size align pr res,
      Runs s (get_free_block size align pr) s' res ->
      s' = s /\
      exists ptr ptrs,
        res = (ptr, ptrs) /\
        address_provenance ptr =
          allocation_id_to_prov (provenance_to_allocation_id pr) /\
        get_consecutive_ptrs ptr size = ret ptrs.
  Proof.
    intros s s' size align pr res H. unfold get_free_block in H.
    cbv zeta in H. to_memS.
    apply Runs_bind_inv in H. destruct H as (s1 & addr0 & Hnk & H).
    unfold next_key in Hnk. apply inv_next in Hnk. destruct Hnk as [an Hnk].
    apply inv_ret in Hnk. destruct Hnk as [Hs1 _]. subst s1.
    apply Runs_bind_inv in H. destruct H as (s2 & ptr0 & Hlift & H).
    apply inv_lift in Hlift. destruct Hlift as [Hitp Hs2]. subst s2.
    apply Runs_bind_inv in H. destruct H as (s3 & ptrs0 & Hlift2 & H).
    apply inv_lift in Hlift2. destruct Hlift2 as [Hgcp Hs3]. subst s3.
    apply inv_ret in H. destruct H as [Hs' Hres]. subst.
    split; [reflexivity|]. exists ptr0, ptrs0. repeat split.
    - eapply int_to_ptr_provenance. exact Hitp.
    - exact Hgcp.
  Qed.

  (* The whole allocation: the returned [ptr] carries the fresh        *)
  (* provenance, its consecutive pointers all exist, and the final     *)
  (* byte map is the [init] block written at [ptr_to_int ptr].         *)
  Lemma Allocate_bytes_inv :
    forall s s' init align pr ptr,
      Runs s (Allocate_bytes_with_pr init align pr) s' ptr ->
      address_provenance ptr =
        allocation_id_to_prov (provenance_to_allocation_id pr) /\
      (exists ptrs, get_consecutive_ptrs ptr (N.length init) = ret ptrs) /\
      memOf s' =
        add_all_index
          (memory_bytes_to_bytes (provenance_to_allocation_id pr) init)
          (ptr_to_int ptr) (memOf s).
  Proof.
    intros s s' init align pr ptr H. unfold Allocate_bytes_with_pr in H.
    cbv zeta in H. to_memS.
    apply Runs_bind_inv in H. destruct H as (s1 & res & Hgfb & H).
    apply get_free_block_inv in Hgfb.
    destruct Hgfb as [Hs1 (ptr0 & ptrs0 & Hres & Hprov & Hgcp)].
    subst s1 res. cbn beta iota in H.
    apply Runs_bind_inv in H. destruct H as (s2 & u & Habs & Hret).
    apply inv_ret in Hret. destruct Hret as [Hs' Hptr]. subst s2 ptr.
    apply Runs_add_block_to_stack_inv in Habs.
    repeat split.
    - exact Hprov.
    - exists ptrs0. exact Hgcp.
    - exact Habs.
  Qed.

  Lemma L3_allocate_read_new : forall s s' init align pr ptr i b,
      Runs s (Allocate_bytes_with_pr init align pr) s' ptr ->
      nth_error init i = Some b ->
      exists a_i,
        ptr_to_int a_i = (ptr_to_int ptr + Z.of_nat i)%Z /\
        address_provenance a_i =
          allocation_id_to_prov (provenance_to_allocation_id pr) /\
        Runs s' (Read_byte a_i) s' b.
  Proof.
    intros s s' init align pr ptr i b Halloc Hnth.
    apply Allocate_bytes_inv in Halloc.
    destruct Halloc as (Hprov & (ptrs & Hgcp) & Hmem).
    assert (Hi : (i < N.to_nat (N.length init))%nat).
    { rewrite N_to_nat_length. apply nth_error_Some. rewrite Hnth. discriminate. }
    destruct (get_consecutive_ptrs_nth ptr (N.length init) ptrs i Hgcp Hi)
      as [a_i (Hnth_i & Hint & Hprov_i)].
    exists a_i. split; [exact Hint|]. split; [rewrite Hprov_i; exact Hprov|].
    unfold Read_byte. to_memS.
    eapply Runs_bind.
    - apply Runs_read_byte_raw_Some
        with (v := (b, provenance_to_allocation_id pr)).
      unfold read_byte_raw_mem. rewrite Hmem, Hint.
      apply find_add_all_index_map_nth. exact Hnth.
    - cbn. rewrite Hprov_i, Hprov, access_allowed_refl. apply RunsRet.
  Qed.

  (* Inversion of a successful [Read_byte]: the raw byte is present    *)
  (* (with some allocation id [aid] whose provenance guard passed),    *)
  (* the returned value is that byte, and the state is unchanged.      *)
  Lemma Read_byte_inv : forall s s' a r,
      Runs s (Read_byte a) s' r ->
      exists aid,
        read_byte_raw_mem (memOf s) (ptr_to_int a) = Some (r, aid) /\
        access_allowed (address_provenance a) aid = true /\
        s' = s.
  Proof.
    intros s s' a r H. unfold Read_byte in H. cbv zeta in H. to_memS.
    apply Runs_bind_inv in H. destruct H as (s1 & x & Hrbr & H).
    apply Runs_read_byte_raw_inv in Hrbr. destruct Hrbr as [Hs1 Hfind].
    subst s1.
    destruct x as [rb aid]. cbn beta iota in H.
    destruct (access_allowed (address_provenance a) aid) eqn:Hacc.
    - apply inv_ret in H. destruct H as [Hs' Hr]. subst.
      exists aid. split; [exact Hfind | split; [exact Hacc | reflexivity]].
    - apply inv_ub in H. contradiction.
  Qed.

  (* ================================================================ *)
  (*  L4  allocate_provenance_fresh  -- CLOSED (frontier premise)      *)
  (* ================================================================ *)
  (* The disjointness [ptr_to_int a < ptr_to_int ptr] is a             *)
  (* *monotone-frontier* invariant of the concrete [next_key] handler  *)
  (* ("every already-allocated key is < next_key size align").  This   *)
  (* file's [Runs] treats [Mnext_key] non-deterministically (any key), *)
  (* so the invariant is not derivable here.  It is therefore supplied  *)
  (* as the explicit premise                                           *)
  (*   [ptr_to_int ptr = next_key_with_alignment (memOf s) align]      *)
  (* -- a genuine precondition satisfied by the concrete interpreter    *)
  (* [memM_interp] and discharged outright in MemoryLaws_L4.v (whose    *)
  (* [RunsNext] is pinned to the concrete handler value).  Given the    *)
  (* premise, freshness follows from [next_key_with_alignment_gt] and   *)
  (* heap monotonicity from [lookup_add_all_index_out].                 *)
  Lemma L4_allocate_provenance_fresh : forall s s' init align pr ptr a r,
      Runs s (Allocate_bytes_with_pr init align pr) s' ptr ->
      Runs s (Read_byte a) s r ->
      ptr_to_int ptr = next_key_with_alignment (memOf s) align ->
      ptr_to_int a < ptr_to_int ptr /\ Runs s' (Read_byte a) s' r.
  Proof.
    intros s s' init align pr ptr a r Halloc Hread Hnk.
    (* Decompose the pre-existing read. *)
    apply Read_byte_inv in Hread.
    destruct Hread as (aid & Hfind & Hacc & _).
    (* Decompose the allocation. *)
    apply Allocate_bytes_inv in Halloc.
    destruct Halloc as (_ & _ & Hmem).
    (* (a) The pre-existing key is below the concrete frontier = ptr's key. *)
    assert (HIn : IM.In (ptr_to_int a) (memOf s)).
    { exists (r, aid). apply IM.find_2.
      unfold read_byte_raw_mem in Hfind. exact Hfind. }
    pose proof (next_key_with_alignment_gt (memOf s) align (ptr_to_int a) HIn)
      as Hfront.
    rewrite <- Hnk in Hfront.
    split; [exact Hfront|].
    (* (b) The allocation writes only at keys >= ptr's key > a's key,   *)
    (*     so the raw read at [a] is unchanged and the same provenance  *)
    (*     guard still passes; hence [Read_byte a] returns [r] in [s'].  *)
    unfold Read_byte. cbv zeta. to_memS.
    eapply Runs_bind.
    - apply Runs_read_byte_raw_Some with (v := (r, aid)).
      unfold read_byte_raw_mem. rewrite Hmem.
      replace (IM.find (ptr_to_int a)
                 (add_all_index
                    (memory_bytes_to_bytes (provenance_to_allocation_id pr) init)
                    (ptr_to_int ptr) (memOf s)))
        with (lookup (ptr_to_int a)
                (add_all_index
                   (memory_bytes_to_bytes (provenance_to_allocation_id pr) init)
                   (ptr_to_int ptr) (memOf s)))
        by reflexivity.
      rewrite lookup_add_all_index_out by (left; exact Hfront).
      unfold read_byte_raw_mem in Hfind. exact Hfind.
    - cbn beta iota. rewrite Hacc. apply RunsRet.
  Qed.

  (* ================================================================ *)
  (*  The local [MemoryModelLaws] interface, instantiated.            *)
  (* ================================================================ *)
  Class MemoryModelLaws : Prop := {
    law_read_write_eq :
      forall s s' a b, Runs s (Write_byte a b) s' tt -> Runs s' (Read_byte a) s' b ;
    law_write_read_neq :
      forall s s' a1 a2 b2 r1,
        ptr_to_int a1 <> ptr_to_int a2 ->
        Runs s (Read_byte a1) s r1 ->
        Runs s (Write_byte a2 b2) s' tt ->
        Runs s' (Read_byte a1) s' r1 ;
    law_allocate_read_new :
      forall s s' init align pr ptr i b,
        Runs s (Allocate_bytes_with_pr init align pr) s' ptr ->
        nth_error init i = Some b ->
        exists a_i,
          ptr_to_int a_i = (ptr_to_int ptr + Z.of_nat i)%Z /\
          address_provenance a_i =
            allocation_id_to_prov (provenance_to_allocation_id pr) /\
          Runs s' (Read_byte a_i) s' b ;
    law_allocate_provenance_fresh :
      forall s s' init align pr ptr a r,
        Runs s (Allocate_bytes_with_pr init align pr) s' ptr ->
        Runs s (Read_byte a) s r ->
        ptr_to_int ptr = next_key_with_alignment (memOf s) align ->
        ptr_to_int a < ptr_to_int ptr /\ Runs s' (Read_byte a) s' r ;
  }.

  Instance MemoryModelLawsV : MemoryModelLaws :=
    {| law_read_write_eq := L1_read_write_eq ;
       law_write_read_neq := L2_write_read_neq ;
       law_allocate_read_new := L3_allocate_read_new ;
       law_allocate_provenance_fresh := L4_allocate_provenance_fresh |}.

End MemoryLaws.
