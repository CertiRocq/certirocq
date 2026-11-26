(* Lemmas about the relation of [LambdaANF_to_C_rel] and the memory of CompCert. *)

From Stdlib Require Import ZArith.ZArith Lists.List micromega.Lia.
From compcert Require Import lib.Coqlib lib.Maps lib.Integers common.AST common.Values
     common.Memory common.Events common.Globalenvs common.Smallstep
     cfrontend.Ctypes cfrontend.Clight Clightdefs.
From MetaRocq.Utils Require Import bytestring.
From CertiRocq.Common Require Import compM.
From CertiRocq.LambdaANF Require Import term algebra eval.
From CertiRocq.Codegen Require Import LambdaANF_to_C LambdaANF_to_C_rel.

Import ListNotations.
Local Open Scope Z_scope.
Local Open Scope bs_scope.

Local Arguments Z.mul : simpl never.
Local Arguments Z.add : simpl never.
Local Arguments Z.sub : simpl never.

Lemma ptr64 : Archi.ptr64 = true.
Proof. reflexivity. Qed.

(* Arithmetic with the offsets of the fields *)
Ltac ofs_lia :=
  unfold tinfo_size in *; unfold fp_ofs in *;
  unfold alloc_ofs, limit_ofs, heap_ofs, args_ofs, next_ofs, root_ofs, prev_ofs, max_args in *;
  lia.

Lemma Forall2_nth_r {A B} (R : A -> B -> Prop) l1 l2 :
  Forall2 R l1 l2 ->
  forall n y, nth_error l2 n = Some y -> exists x, nth_error l1 n = Some x /\ R x y.
Proof.
  induction 1; intros n y' Hn; destruct n; simpl in *; try discriminate.
  - inv Hn. eauto.
  - eauto.
Qed.

Lemma Forall2_nth_l {A B} (R : A -> B -> Prop) l1 l2 :
  Forall2 R l1 l2 ->
  forall n x, nth_error l1 n = Some x -> exists y, nth_error l2 n = Some y /\ R x y.
Proof.
  induction 1; intros n x' Hn; destruct n; simpl in *; try discriminate.
  - inv Hn. eauto.
  - eauto.
Qed.

(* The data and the objects of [h] are data and objects of [h'] *)
Definition heap_le (h h' : heap) : Prop :=
  (forall b o, allocated h b o -> allocated h' b o) /\
  (forall b o, heap_objects h b o -> heap_objects h' b o).

Lemma heap_le_refl h : heap_le h h.
Proof. split; auto. Qed.

Lemma heap_le_trans h1 h2 h3 : heap_le h1 h2 -> heap_le h2 h3 -> heap_le h1 h3.
Proof. intros [A1 O1] [A2 O2]. split; auto. Qed.

#[export] Hint Resolve heap_le_refl : core.

Section Properties.

  Context (cenv : ctor_env) (ge : genv) (nparam ratio : nat).
  Context (gc_inv : heap -> mem -> block -> Z -> Prop).
  Context {fuel : Type} {Hf : @fuel_resource fuel} {trace : Type} {Ht : @trace_resource trace}.

  Notation repr_val := (repr_val cenv ge).
  Notation repr_fields := (repr_fields cenv ge).
  Notation is_value := (is_value cenv ge).
  Notation frame_ok := (frame_ok cenv ge).
  Notation still_represented := (still_represented cenv ge).
  Notation fun_rel := (fun_rel cenv ge nparam ratio gc_inv).
  Notation val_rel := (val_rel cenv ge nparam ratio gc_inv).
  Notation tinfo_wf := (tinfo_wf cenv ge gc_inv).
  Notation tinfo_ok := (tinfo_ok cenv ge gc_inv).
  Notation call_post := (call_post cenv ge gc_inv).
  Notation call_returns := (call_returns cenv ge gc_inv).
  Notation call_outcome := (call_outcome cenv ge gc_inv).

  Hypothesis Hcol : collector_ok cenv ge gc_inv.

  (** * Values *)

  Scheme repr_val_mut := Minimality for LambdaANF_to_C_rel.repr_val Sort Prop
    with repr_fields_mut := Minimality for LambdaANF_to_C_rel.repr_fields Sort Prop.

  (* The relation holds for a larger [F] and a larger heap *)
  Lemma repr_val_mono F F' h h' m :
    (forall v fd, F v fd -> F' v fd) ->
    heap_le h h' ->
    forall v w, repr_val F h m v w -> repr_val F' h' m v w.
  Proof.
    intros HF [HA HO].
    apply (repr_val_mut cenv ge F h m
             (fun v w => repr_val F' h' m v w)
             (fun vs b o => repr_fields F' h' m vs b o)); intros.
    - now constructor.
    - econstructor; eauto.
    - econstructor; eauto.
    - constructor.
    - econstructor; eauto.
  Qed.

  (* The relation does not depend on the memory outside the data of the heap *)
  Lemma repr_val_unchanged F h m m' :
    Mem.unchanged_on (allocated h) m m' ->
    forall v w, repr_val F h m v w -> repr_val F h m' v w.
  Proof.
    intros Hun.
    apply (repr_val_mut cenv ge F h m
             (fun v w => repr_val F h m' v w)
             (fun vs b o => (forall i, o <= i < o + 8 * Z.of_nat (length vs) -> allocated h b i) ->
                            repr_fields F h m' vs b o)); intros.
    - now constructor.
    - econstructor; eauto.
      + eapply Mem.load_unchanged_on; eauto.
        intros i Hi. apply H3. change (size_chunk Mptr) with 8 in Hi. lia.
      + apply H6. intros i Hi. apply H3. lia.
    - econstructor; eauto.
    - constructor.
    - simpl length in H4. econstructor.
      + eapply Mem.load_unchanged_on; eauto.
        intros i Hi. apply H4. change (size_chunk Mptr) with 8 in Hi. lia.
      + auto.
      + apply H3. intros i Hi. apply H4. lia.
  Qed.

  (* The field number [n] of a block *)
  Lemma repr_fields_nth F h m vs b o :
    repr_fields F h m vs b o ->
    forall n v, nth_error vs n = Some v ->
                exists w, Mem.load Mptr m b (o + 8 * Z.of_nat n) = Some w /\ repr_val F h m v w.
  Proof.
    induction 1; intros n v' Hn.
    - destruct n; discriminate.
    - destruct n; simpl in Hn.
      + inv Hn. exists w. split; auto. now rewrite Z.add_0_r.
      + destruct (IHrepr_fields _ _ Hn) as [w' [Hl Hr]].
        exists w'. split; auto. rewrite <- Hl. f_equal. lia.
  Qed.

  (** * Functions *)

  (* What [fun_rel] says of a function for one more step *)
  Lemma fun_rel_S k rho fds f fd :
    fun_rel (S k) (Vfun rho fds f) fd <->
    exists t xs e,
      find_def f fds = Some (t, xs, e) /\
      type_of_fundef fd = fun_ty nparam (length xs) /\
      forall (j : nat) vs rho' (c : fuel) r (tr : trace) ws tb tofs h fs m,
        (j <= k)%nat ->
        set_lists xs vs (def_funs fds fds rho rho) = Some rho' ->
        bstep_fuel cenv rho' e c r tr ->
        (to_nat c <= j)%nat ->
        tinfo_ok h fs m tb tofs ->
        Forall2 (val_rel j h m) vs ws ->
        args_in_tinfo nparam m tb tofs ws ->
        call_outcome r (S (to_nat c / ratio)) (fun _ _ => False)
                     (fun v' h' m' w' => val_rel (j - to_nat c) h' m' v' w')
                     0 tb tofs fs h m
                     fd (Vptr tb (Ptrofs.repr tofs) :: firstn nparam ws).
  Proof.
    unfold val_rel. simpl.
    split; intros (t & xs & e & Hf' & Hty & H); exists t, xs, e; repeat split; auto;
      intros j vs rho' c r tr ws tb tofs h fs m Hj Hs Hb Hc Ht' Hvs Ha;
      specialize (H j vs rho' c r tr ws tb tofs h fs m Hj Hs Hb Hc Ht');
      replace (k - (k - j))%nat with j in * by lia; auto.
  Qed.

  Lemma fun_rel_0 rho fds f fd :
    fun_rel 0 (Vfun rho fds f) fd <->
    exists t xs e,
      find_def f fds = Some (t, xs, e) /\ type_of_fundef fd = fun_ty nparam (length xs).
  Proof.
    simpl. split; intros (t & xs & e & H1 & H2); exists t, xs, e; tauto.
  Qed.

  (* A function related for [k] steps is related for fewer steps *)
  Lemma fun_rel_mono j k v fd :
    (j <= k)%nat -> fun_rel k v fd -> fun_rel j v fd.
  Proof.
    intros Hle H. destruct v as [? ? | rho fds f | ? | ?]; try (destruct k; contradiction).
    destruct k as [|k].
    - assert (j = 0)%nat by lia. subst. auto.
    - apply fun_rel_S in H. destruct H as (t & xs & e & Hf' & Hty & H).
      destruct j as [|j].
      + apply fun_rel_0. eauto.
      + apply fun_rel_S. exists t, xs, e. repeat split; auto.
        intros. eapply H; eauto. lia.
  Qed.

  Lemma val_rel_mono j k h m v w :
    (j <= k)%nat -> val_rel k h m v w -> val_rel j h m v w.
  Proof.
    intros Hle. apply repr_val_mono; auto.
    intros. eapply fun_rel_mono; eauto.
  Qed.

  (** * Roots and changes *)

  Lemma still_represented_refl h m b o :
    still_represented h m h m b o.
  Proof. intros w Hw. exists w. auto. Qed.

  Lemma still_represented_trans h1 m1 h2 m2 h3 m3 b o :
    still_represented h1 m1 h2 m2 b o ->
    still_represented h2 m2 h3 m3 b o ->
    still_represented h1 m1 h3 m3 b o.
  Proof.
    intros H1 H2 w Hw.
    destruct (H1 w Hw) as (w2 & Hw2 & H12). destruct (H2 w2 Hw2) as (w3 & Hw3 & H23).
    exists w3. split; auto.
  Qed.

  (* The data of [h] in [m] is in [m'], where the heap is [h'] *)
  Definition data_kept (h : heap) (m : mem) (h' : heap) (m' : mem) : Prop :=
    Mem.unchanged_on (allocated h) m m' /\ heap_le h h'.

  Lemma data_kept_refl h m : data_kept h m h m.
  Proof. split; auto. apply Mem.unchanged_on_refl. Qed.

  Lemma data_kept_trans h1 m1 h2 m2 h3 m3 :
    data_kept h1 m1 h2 m2 -> data_kept h2 m2 h3 m3 -> data_kept h1 m1 h3 m3.
  Proof.
    intros [U1 I1] [U2 I2]. split; [| eapply heap_le_trans; eauto].
    eapply Mem.unchanged_on_trans; [exact U1 |].
    eapply Mem.unchanged_on_implies; [exact U2 |]. intros b o Ha _. apply (proj1 I1). exact Ha.
  Qed.

  Lemma repr_val_kept F h m h' m' v w :
    data_kept h m h' m' -> repr_val F h m v w -> repr_val F h' m' v w.
  Proof.
    intros [Hun Hle] H. apply repr_val_mono with (F := F) (h := h); auto.
    eapply repr_val_unchanged; eauto.
  Qed.

  Lemma is_value_kept h m h' m' w :
    data_kept h m h' m' -> is_value h m w -> is_value h' m' w.
  Proof. intros Hk [v Hv]. exists v. eapply repr_val_kept; eauto. Qed.

  (* A word that does not change is still represented when the data is kept *)
  Lemma still_represented_kept h m h' m' b o :
    data_kept h m h' m' ->
    (forall w, Mem.load Mptr m b o = Some w -> Mem.load Mptr m' b o = Some w) ->
    still_represented h m h' m' b o.
  Proof.
    intros Hk Hl w Hw. exists w. split; auto. intros. eapply repr_val_kept; eauto.
  Qed.

  Lemma changes_refl X tb tofs fs h m :
    changes X tb tofs fs h m h m.
  Proof.
    split; [apply Mem.unchanged_on_refl | split; auto].
  Qed.

  Lemma changes_trans X tb tofs fs h1 m1 h2 m2 h3 m3 :
    changes X tb tofs fs h1 m1 h2 m2 ->
    changes X tb tofs fs h2 m2 h3 m3 ->
    changes X tb tofs fs h1 m1 h3 m3.
  Proof.
    intros (U1 & P1 & N1) (U2 & P2 & N2).
    assert (Hnew : forall b, Mem.valid_block m1 b -> ~ heap_blocks h1 b -> ~ heap_blocks h2 b).
    { intros b Hv Hn Hh. destruct (N1 b Hh); auto. }
    assert (Hvalid : forall b, Mem.valid_block m1 b -> Mem.valid_block m2 b).
    { intros b Hv. unfold Mem.valid_block in *.
      eapply Pos.lt_le_trans; eauto. apply (Mem.unchanged_on_nextblock _ _ _ U1). }
    split; [| split].
    - constructor.
      + eapply Ple_trans; eapply Mem.unchanged_on_nextblock; eauto.
      + intros b o k p (Hh & Hti & Hr & Hx) Hv.
        rewrite (Mem.unchanged_on_perm _ _ _ U1 b o k p); auto.
        apply (Mem.unchanged_on_perm _ _ _ U2); auto.
      + intros b o (Hh & Hti & Hr & Hx) Hp.
        assert (Hv : Mem.valid_block m1 b) by (eapply Mem.perm_valid_block; eauto).
        rewrite (Mem.unchanged_on_contents _ _ _ U2 b o).
        * apply (Mem.unchanged_on_contents _ _ _ U1); auto.
        * auto.
        * apply (Mem.unchanged_on_perm _ _ _ U1 b o Cur Readable); auto.
    - intros b o k p Hh Hx Hp. apply P2; auto.
      apply Hnew; auto. eapply Mem.perm_valid_block; eauto.
    - intros b Hh. destruct (N2 b Hh) as [Hh2 | Hv2].
      + auto.
      + right. intro Hv. auto.
  Qed.

  (** * Frames *)

  (* The bytes of the structs of the frames [fs] *)
  Definition in_frames (fs : list frame) (b : block) (o : Z) : Prop :=
    exists fr, In fr fs /\ b = frame_block fr /\ frame_ofs fr <= o < frame_ofs fr + 24.

  Lemma frames_unchanged m m' fp fs :
    frames m fp fs -> Mem.unchanged_on (in_frames fs) m m' -> frames m' fp fs.
  Proof.
    induction 1; intros Hun.
    - constructor.
    - assert (Hl : forall o v, (o = next_ofs \/ o = root_ofs \/ o = prev_ofs) ->
                               Mem.load Mptr m (frame_block fr) (frame_ofs fr + o) = Some v ->
                               Mem.load Mptr m' (frame_block fr) (frame_ofs fr + o) = Some v).
      { intros o v Ho Hv. eapply Mem.load_unchanged_on; eauto.
        intros i Hi. exists fr. change (size_chunk Mptr) with 8 in Hi.
        unfold next_ofs, root_ofs, prev_ofs in Ho. split; [now left | split; [reflexivity | lia]]. }
      econstructor; eauto.
      apply IHframes. eapply Mem.unchanged_on_implies; eauto.
      intros b o (fr' & Hin & Hb & Ho) _. exists fr'. split; [now right | auto].
  Qed.

  (** * The thread info *)

  (* The permissions of block [b] are kept from [m] to [m'] *)
  Definition keeps_perm (m m' : mem) (b : block) : Prop :=
    forall o k p, Mem.perm m b o k p -> Mem.perm m' b o k p.

  Lemma store_keeps_perm chunk m b o v m' b' :
    Mem.store chunk m b o v = Some m' -> keeps_perm m m' b'.
  Proof. intros H o' k p. eapply Mem.perm_store_1; eauto. Qed.

  Lemma free_ok_unchanged h m m' :
    free_ok h m -> keeps_perm m m' (free_block h) -> free_ok h m'.
  Proof.
    intros [? ? ? ? Hp] Hk. constructor; auto. intros o Ho. apply Hk. auto.
  Qed.

  Lemma frame_ok_unchanged h m m' tb fr :
    frame_ok h m tb fr ->
    Mem.unchanged_on (fun b o => allocated h b o \/ in_roots [fr] b o) m m' ->
    keeps_perm m m' (frame_block fr) ->
    keeps_perm m m' (roots_block fr) ->
    frame_ok h m' tb fr.
  Proof.
    intros [? ? ? Hp Hv [Hvf Hvr] ? (Hs1 & Hs2 & Hsp)] Hun Hkf Hk. constructor; auto.
    - intros o Ho. apply Hk. auto.
    - intros i Hi. destruct (Hv i Hi) as (w & Hw & Hval). exists w. split.
      + eapply Mem.load_unchanged_on; eauto.
        intros o Ho. change (size_chunk Mptr) with 8 in Ho. right.
        exists fr. split; [now left | split; [reflexivity | lia]].
      + eapply is_value_kept; eauto. split; auto.
        eapply Mem.unchanged_on_implies; eauto. intros. now left.
    - split; eapply Mem.valid_block_unchanged_on; eauto.
    - split; [exact Hs1 | split; [exact Hs2 |]]. intros o Ho. apply Hkf. auto.
  Qed.

  (* The bytes that [tinfo_wf] reads *)
  Definition tinfo_dep (h : heap) (fs : list frame) (tb : block) (tofs : Z) (b : block) (o : Z)
    : Prop :=
    gc_owned h tb tofs b o \/ in_frames fs b o \/ in_roots fs b o \/
    (b = tb /\ (tofs + limit_ofs <= o < tofs + limit_ofs + 8 \/
                tofs + fp_ofs <= o < tofs + fp_ofs + 8)).

  Lemma allocated_owned h tb tofs b o : allocated h b o -> gc_owned h tb tofs b o.
  Proof. intros [Hh Hlt]. left. split; auto. intros [Hb Ho]. specialize (Hlt Hb). lia. Qed.

  Lemma tinfo_wf_unchanged h fs m m' tb tofs :
    tinfo_wf h fs m tb tofs ->
    Mem.unchanged_on (tinfo_dep h fs tb tofs) m m' ->
    keeps_perm m m' tb ->
    keeps_perm m m' (free_block h) ->
    (forall fr, In fr fs -> keeps_perm m m' (frame_block fr) /\ keeps_perm m m' (roots_block fr)) ->
    tinfo_wf h fs m' tb tofs.
  Proof.
    intros [Hrange Hperm Hblock Hlimit Hfree [fp [Hfp Hframes]] Hfs Hvalid Hgc] Hun Hk1 Hk2 Hk3.
    constructor; auto.
    - intros o Ho. apply Hk1. auto.
    - eapply Mem.load_unchanged_on; eauto.
      intros i Hi. change (size_chunk Mptr) with 8 in Hi. right. right. right. split; auto.
    - eapply free_ok_unchanged; eauto.
    - exists fp. split.
      + eapply Mem.load_unchanged_on; eauto.
        intros i Hi. change (size_chunk Mptr) with 8 in Hi. right. right. right. split; auto.
      + eapply frames_unchanged; eauto.
        eapply Mem.unchanged_on_implies; eauto. intros. right. now left.
    - rewrite Forall_forall in *. intros fr Hin. destruct (Hk3 fr Hin).
      eapply frame_ok_unchanged; eauto.
      eapply Mem.unchanged_on_implies; eauto.
      intros b o [Ha | (fr' & [Heq | []] & Hb & Ho)] _; [left; now apply allocated_owned |].
      subst fr'. right. right. left. exists fr. auto.
    - intros b Hb. eapply Mem.valid_block_unchanged_on; eauto.
    - eapply (gc_stable _ _ _ Hcol); eauto.
      eapply Mem.unchanged_on_implies; eauto. intros. now left.
  Qed.

  (* Where the bytes that [tinfo_wf] reads are: in the heap outside the free space, in a
     frame, or in the thread info outside [alloc] and [args] *)
  Lemma tinfo_dep_inv h fs m tb tofs b o :
    tinfo_wf h fs m tb tofs ->
    tinfo_dep h fs tb tofs b o ->
    (heap_blocks h b /\ ~ (b = free_block h /\ free_start h <= o < free_end h)) \/
    (~ heap_blocks h b /\ b <> tb /\ exists fr, In fr fs /\ (b = frame_block fr \/ b = roots_block fr)) \/
    (b = tb /\ (tofs + limit_ofs <= o < tofs + args_ofs \/
                tofs + fp_ofs <= o < tofs + tinfo_size)).
  Proof.
    intros Hwf Hdep.
    pose proof (wf_frames _ _ _ _ _ _ _ _ Hwf) as Hfs. rewrite Forall_forall in Hfs.
    destruct Hdep as [[Hown | [Hb Ho]] | [(fr & Hin & Hb & Ho) | [(fr & Hin & Hb & Ho) | [Hb Ho]]]].
    - now left.
    - right. right. split; [exact Hb | ofs_lia].
    - right. left. destruct (Hfs fr Hin) as [[? ?] [? ?] _ _ _]. subst b. repeat split; eauto.
    - right. left. destruct (Hfs fr Hin) as [[? ?] [? ?] _ _ _]. subst b. repeat split; eauto.
    - right. right. split; [exact Hb | ofs_lia].
  Qed.

  (* A change outside the bytes that [tinfo_wf] reads *)
  Lemma tinfo_wf_region h fs m m' tb tofs (R : block -> Z -> Prop) :
    tinfo_wf h fs m tb tofs ->
    Mem.unchanged_on (fun b o => ~ R b o) m m' ->
    (forall b, keeps_perm m m' b) ->
    (forall b o, R b o -> ~ tinfo_dep h fs tb tofs b o) ->
    tinfo_wf h fs m' tb tofs.
  Proof.
    intros Hwf Hun Hk HR. eapply tinfo_wf_unchanged; eauto.
    eapply Mem.unchanged_on_implies; eauto. intros b o Hd _ Hr. eapply HR; eauto.
  Qed.

  (* A store outside the bytes of the collector keeps its invariant *)
  Lemma gc_inv_store h m m' tb tofs chunk b o v :
    gc_inv h m tb tofs ->
    Mem.store chunk m b o v = Some m' ->
    (forall i, o <= i < o + size_chunk chunk -> ~ gc_owned h tb tofs b i) ->
    gc_inv h m' tb tofs.
  Proof.
    intros Hgc Hst Hout. eapply (gc_stable _ _ _ Hcol); eauto.
    eapply Mem.store_unchanged_on; eauto.
  Qed.

  (* The frames [fs] do not use the block [b] *)
  Definition not_in_frames (b : block) (fs : list frame) : Prop :=
    forall fr, In fr fs -> b <> frame_block fr /\ b <> roots_block fr.

  Lemma tinfo_wf_store h fs m m' tb tofs chunk b o v :
    tinfo_wf h fs m tb tofs ->
    Mem.store chunk m b o v = Some m' ->
    (forall i, o <= i < o + size_chunk chunk -> ~ tinfo_dep h fs tb tofs b i) ->
    tinfo_wf h fs m' tb tofs.
  Proof.
    intros Hwf Hst Hout. eapply tinfo_wf_unchanged; eauto using store_keeps_perm.
    eapply Mem.store_unchanged_on; eauto.
  Qed.

  (* A store in the field [alloc] or the field [args] of the thread info *)
  Lemma tinfo_wf_store_tinfo h fs m m' tb tofs chunk o v :
    tinfo_wf h fs m tb tofs ->
    Mem.store chunk m tb o v = Some m' ->
    (o + size_chunk chunk <= tofs + limit_ofs \/
     (tofs + args_ofs <= o /\ o + size_chunk chunk <= tofs + fp_ofs)) ->
    tinfo_wf h fs m' tb tofs.
  Proof.
    intros Hwf Hst Ho. eapply tinfo_wf_store; eauto.
    intros i Hi Hd. destruct (tinfo_dep_inv _ _ _ _ _ _ _ Hwf Hd) as [[Hh _] | [(_ & Hn & _) | [_ Hr]]].
    - eapply wf_block; eauto.
    - congruence.
    - ofs_lia.
  Qed.

  (* A store in a block that is not of the heap, the thread info or a frame *)
  Lemma tinfo_wf_store_other h fs m m' tb tofs chunk b o v :
    tinfo_wf h fs m tb tofs ->
    Mem.store chunk m b o v = Some m' ->
    ~ heap_blocks h b -> b <> tb -> not_in_frames b fs ->
    tinfo_wf h fs m' tb tofs.
  Proof.
    intros Hwf Hst Hh Hti Hfr. eapply tinfo_wf_store; eauto.
    intros i Hi Hd.
    destruct (tinfo_dep_inv _ _ _ _ _ _ _ Hwf Hd) as [[Hh' _] | [(_ & _ & fr & Hin & Hb) | [Hb _]]];
      auto.
    destruct (Hfr fr Hin). destruct Hb; auto.
  Qed.

  Lemma tinfo_wf_free h fs m m' tb tofs b lo hi :
    tinfo_wf h fs m tb tofs ->
    Mem.free m b lo hi = Some m' ->
    ~ heap_blocks h b -> b <> tb -> not_in_frames b fs ->
    tinfo_wf h fs m' tb tofs.
  Proof.
    intros Hwf Hfree Hh Hti Hfr.
    pose proof (free_heap _ _ (wf_free _ _ _ _ _ _ _ _ Hwf)) as Hhf.
    eapply tinfo_wf_unchanged; eauto.
    - eapply Mem.free_unchanged_on; eauto. intros i Hi Hd.
      destruct (tinfo_dep_inv _ _ _ _ _ _ _ Hwf Hd) as [[Hh' _] | [(_ & _ & fr & Hin & Hb) | [Hb _]]];
        auto.
      destruct (Hfr fr Hin). destruct Hb; auto.
    - intros o' k p. eapply Mem.perm_free_1; eauto.
    - intros o' k p. eapply Mem.perm_free_1; eauto. left. congruence.
    - intros fr Hin. destruct (Hfr fr Hin).
      split; intros o' k p; eapply Mem.perm_free_1; eauto; left; congruence.
  Qed.

  (** * Frames of the running function *)

  Lemma store_data_kept h chunk m b o v m' :
    Mem.store chunk m b o v = Some m' ->
    (forall i, o <= i < o + size_chunk chunk -> ~ allocated h b i) ->
    data_kept h m h m'.
  Proof.
    intros Hst Hout. split; auto. eapply Mem.store_unchanged_on; eauto.
  Qed.

  Lemma frame_ok_store h m m' tb fr chunk b o v :
    frame_ok h m tb fr ->
    Mem.store chunk m b o v = Some m' ->
    ~ heap_blocks h b -> b <> roots_block fr ->
    frame_ok h m' tb fr.
  Proof.
    intros Hfr Hst Hh Hb. eapply frame_ok_unchanged; eauto using store_keeps_perm.
    eapply Mem.store_unchanged_on; eauto.
    intros i _ [[Ha _] | (fr' & [Heq | []] & Hb' & _)]; [auto | subst fr'; auto].
  Qed.

  Lemma frames_store m m' fp fs chunk b o v :
    frames m fp fs ->
    Mem.store chunk m b o v = Some m' ->
    (forall fr, In fr fs -> b <> frame_block fr) ->
    frames m' fp fs.
  Proof.
    intros Hfr Hst Hb. eapply frames_unchanged; eauto.
    eapply Mem.store_unchanged_on; eauto.
    intros i _ (fr & Hin & Heq & _). eapply Hb; eauto.
  Qed.

  (* A word that is the layout of a value is read as it was written *)
  Lemma repr_val_load_result F h m v w :
    repr_val F h m v w -> Val.load_result Mptr w = w.
  Proof. intros H; inv H; reflexivity. Qed.

  Lemma frames_load_result m fp fs :
    frames m fp fs -> Val.load_result Mptr fp = fp.
  Proof. intros H; inv H; reflexivity. Qed.

  (* [tinfo->fp = &frame] adds the frame [fr], whose fields are written *)
  Lemma tinfo_wf_link h fs m m' tb tofs fr fp :
    tinfo_wf h fs m tb tofs ->
    Mem.load Mptr m tb (tofs + fp_ofs) = Some fp ->
    Mem.load Mptr m (frame_block fr) (frame_ofs fr + next_ofs)
    = Some (Vptr (roots_block fr) (Ptrofs.repr (roots_ofs fr + 8 * roots_num fr))) ->
    Mem.load Mptr m (frame_block fr) (frame_ofs fr + root_ofs)
    = Some (Vptr (roots_block fr) (Ptrofs.repr (roots_ofs fr))) ->
    Mem.load Mptr m (frame_block fr) (frame_ofs fr + prev_ofs) = Some fp ->
    frame_ok h m tb fr ->
    Mem.store Mptr m tb (tofs + fp_ofs) (Vptr (frame_block fr) (Ptrofs.repr (frame_ofs fr)))
    = Some m' ->
    tinfo_wf h (fr :: fs) m' tb tofs.
  Proof.
    intros [Hrange Hperm Hblock Hlimit Hfree [fp0 [Hfp0 Hframes]] Hfs Hvalid Hgc]
           Hfp Hnext Hroot Hprev Hfr Hst.
    assert (Hvalid' : forall b, heap_blocks h b -> Mem.valid_block m' b).
    { intros b Hb. eapply Mem.store_valid_block_1; eauto. }
    assert (Hgc' : gc_inv h m' tb tofs).
    { eapply gc_inv_store; eauto. intros i Hi [[Hh _] | [_ Hr]]; [contradiction |].
      change (size_chunk Mptr) with 8 in Hi. ofs_lia. }
    assert (fp0 = fp) by congruence. subst fp0.
    assert (Hnt : forall fr', In fr' (fr :: fs) -> frame_block fr' <> tb /\ roots_block fr' <> tb).
    { intros fr' [Heq | Hin]; [subst; apply (frame_tinfo _ _ _ _ _ _ Hfr) |].
      rewrite Forall_forall in Hfs. apply (frame_tinfo _ _ _ _ _ _ (Hfs _ Hin)). }
    assert (Hother : forall b o, b <> tb -> Mem.load Mptr m' b o = Mem.load Mptr m b o).
    { intros. eapply Mem.load_store_other; eauto. }
    constructor; auto.
    - intros o Ho. eapply Mem.perm_store_1; eauto.
    - rewrite <- Hlimit. eapply Mem.load_store_other; eauto.
      right. left. change (size_chunk Mptr) with 8. ofs_lia.
    - eapply free_ok_unchanged; eauto using store_keeps_perm.
    - exists (Vptr (frame_block fr) (Ptrofs.repr (frame_ofs fr))). split.
      + erewrite Mem.load_store_same; eauto. reflexivity.
      + destruct (Hnt fr (or_introl eq_refl)). econstructor; try rewrite Hother; eauto.
        eapply frames_store; eauto. intros fr' Hin. apply not_eq_sym, Hnt. now right.
    - rewrite Forall_forall in *. intros fr' Hin.
      destruct (Hnt fr' Hin). eapply frame_ok_store; eauto.
      destruct Hin as [Heq | Hin]; [subst; auto | auto].
  Qed.

  (* [tinfo->fp = frame.prev] removes the first frame *)
  Lemma tinfo_wf_unlink h fs m m' tb tofs fr prev :
    tinfo_wf h (fr :: fs) m tb tofs ->
    Mem.load Mptr m (frame_block fr) (frame_ofs fr + prev_ofs) = Some prev ->
    Mem.store Mptr m tb (tofs + fp_ofs) prev = Some m' ->
    tinfo_wf h fs m' tb tofs.
  Proof.
    intros [Hrange Hperm Hblock Hlimit Hfree [fp0 [Hfp0 Hframes]] Hfs Hvalid Hgc] Hprev Hst.
    assert (Hvalid' : forall b, heap_blocks h b -> Mem.valid_block m' b).
    { intros b Hb. eapply Mem.store_valid_block_1; eauto. }
    assert (Hgc' : gc_inv h m' tb tofs).
    { eapply gc_inv_store; eauto. intros i Hi [[Hh _] | [_ Hr]]; [contradiction |].
      change (size_chunk Mptr) with 8 in Hi. ofs_lia. }
    inversion Hframes as [| ? prev0 ? Hnext Hroot Hprev0 Hfrs]; subst.
    assert (prev0 = prev) by congruence. subst prev0.
    inversion Hfs as [| ? ? Hfr Hfs']; subst.
    assert (Hnt : forall fr', In fr' fs -> frame_block fr' <> tb /\ roots_block fr' <> tb).
    { intros fr' Hin. rewrite Forall_forall in Hfs'. apply (frame_tinfo _ _ _ _ _ _ (Hfs' _ Hin)). }
    constructor; auto.
    - intros o Ho. eapply Mem.perm_store_1; eauto.
    - rewrite <- Hlimit. eapply Mem.load_store_other; eauto.
      right. left. change (size_chunk Mptr) with 8. ofs_lia.
    - eapply free_ok_unchanged; eauto using store_keeps_perm.
    - exists prev. split.
      + erewrite Mem.load_store_same; eauto. f_equal. eapply frames_load_result; eauto.
      + eapply frames_store; eauto. intros fr' Hin. apply not_eq_sym, Hnt. auto.
    - rewrite Forall_forall in *. intros fr' Hin.
      destruct (Hnt fr' Hin). eapply frame_ok_store; eauto.
  Qed.

  (* [frame.next = roots + n] changes the number of roots of the first frame *)
  Lemma tinfo_wf_set_next h fs m m' tb tofs fr n :
    let fr' := mkFrame (frame_block fr) (frame_ofs fr) (roots_block fr) (roots_ofs fr) n in
    tinfo_wf h (fr :: fs) m tb tofs ->
    Mem.store Mptr m (frame_block fr) (frame_ofs fr + next_ofs)
              (Vptr (roots_block fr) (Ptrofs.repr (roots_ofs fr + 8 * n))) = Some m' ->
    frame_ok h m tb fr' ->
    frame_block fr <> roots_block fr ->
    not_in_frames (frame_block fr) fs ->
    tinfo_wf h (fr' :: fs) m' tb tofs.
  Proof.
    intros fr' [Hrange Hperm Hblock Hlimit Hfree [fp0 [Hfp0 Hframes]] Hfs Hvalid Hgc]
           Hst Hfr' Hne Hnot.
    assert (Hvalid' : forall b, heap_blocks h b -> Mem.valid_block m' b).
    { intros b Hb. eapply Mem.store_valid_block_1; eauto. }
    inversion Hframes as [| ? prev ? Hnext Hroot Hprev Hfrs]; subst.
    inversion Hfs as [| ? ? Hfr Hfs']; subst.
    destruct (frame_tinfo _ _ _ _ _ _ Hfr) as [Hfb Hrb].
    destruct (frame_heap _ _ _ _ _ _ Hfr) as [Hfh Hrh].
    assert (Hgc' : gc_inv h m' tb tofs).
    { eapply gc_inv_store; eauto. intros i Hi [[Hh _] | [Heq _]]; contradiction. }
    constructor; auto.
    - intros o Ho. eapply Mem.perm_store_1; eauto.
    - rewrite <- Hlimit. eapply Mem.load_store_other; eauto.
    - eapply free_ok_unchanged; eauto using store_keeps_perm.
    - exists (Vptr (frame_block fr) (Ptrofs.repr (frame_ofs fr))). split.
      + rewrite <- Hfp0. eapply Mem.load_store_other; eauto.
      + apply (Frames_cons m' fr' prev fs); simpl.
        * erewrite Mem.load_store_same; eauto. reflexivity.
        * rewrite <- Hroot. eapply Mem.load_store_other; eauto.
          right. right. change (size_chunk Mptr) with 8. ofs_lia.
        * rewrite <- Hprev. eapply Mem.load_store_other; eauto.
          right. right. change (size_chunk Mptr) with 8. ofs_lia.
        * eapply frames_store; eauto. intros fr0 Hin. apply (Hnot fr0 Hin).
    - constructor.
      + eapply frame_ok_store; eauto.
      + rewrite Forall_forall in *. intros fr0 Hin. eapply frame_ok_store; eauto.
        apply (Hnot fr0 Hin).
  Qed.

  (* The block of the roots of the first frame changes, and the roots still hold values *)
  Lemma tinfo_wf_roots h fs m m' tb tofs fr :
    tinfo_wf h (fr :: fs) m tb tofs ->
    Mem.unchanged_on (fun b o => b <> roots_block fr) m m' ->
    (forall b, keeps_perm m m' b) ->
    frame_block fr <> roots_block fr ->
    not_in_frames (roots_block fr) fs ->
    (forall i, 0 <= i < roots_num fr ->
               exists w, Mem.load Mptr m' (roots_block fr) (roots_ofs fr + 8 * i) = Some w /\
                         is_value h m' w) ->
    tinfo_wf h (fr :: fs) m' tb tofs.
  Proof.
    intros [Hrange Hperm Hblock Hlimit Hfree [fp0 [Hfp0 Hframes]] Hfs Hvalid Hgc]
           Hun Hkp Hne Hnot Hvals.
    assert (Hvalid' : forall b, heap_blocks h b -> Mem.valid_block m' b).
    { intros b Hb. eapply Mem.valid_block_unchanged_on; eauto. }
    inversion Hfs as [| ? ? Hfr Hfs']; subst.
    destruct (frame_tinfo _ _ _ _ _ _ Hfr) as [Hfb Hrb].
    destruct (frame_heap _ _ _ _ _ _ Hfr) as [Hfh Hrh].
    assert (Hgc' : gc_inv h m' tb tofs).
    { eapply (gc_stable _ _ _ Hcol); eauto. eapply Mem.unchanged_on_implies; eauto.
      intros b o [[Hh _] | [Heq _]] _; simpl; intros Hb; rewrite Hb in *; contradiction. }
    constructor; auto.
    - intros o Ho. apply Hkp. auto.
    - eapply Mem.load_unchanged_on; eauto. intros. simpl. congruence.
    - eapply free_ok_unchanged; eauto.
    - exists fp0. split.
      + eapply Mem.load_unchanged_on; eauto. intros. simpl. congruence.
      + eapply frames_unchanged; eauto. eapply Mem.unchanged_on_implies; eauto.
        intros b o (fr0 & [<- | Hin] & -> & _) _; simpl; [auto | apply not_eq_sym, (Hnot fr0 Hin)].
    - constructor.
      + destruct Hfr as [? ? ? Hp Hv [Hvf Hvr] ? (Hs1 & Hs2 & Hsp)]. constructor; auto.
        * intros o Ho. apply Hkp. auto.
        * split; eapply Mem.valid_block_unchanged_on; eauto.
        * split; [exact Hs1 | split; [exact Hs2 |]]. intros o Ho. apply Hkp. auto.
      + rewrite Forall_forall in *. intros fr0 Hin. eapply frame_ok_unchanged; eauto.
        eapply Mem.unchanged_on_implies; eauto.
        intros b o [[Hh _] | (fr1 & [<- | []] & -> & _)] _; simpl.
        * intros ->. contradiction.
        * apply not_eq_sym, (Hnot fr0 Hin).
  Qed.

  (** * Allocation *)

  Lemma allocated_alloc_block h n b o :
    0 <= n -> allocated h b o -> allocated (alloc_block h n) b o.
  Proof.
    intros Hn [Hh Hlt]. split; auto. unfold alloc_block; simpl. intros Hb. specialize (Hlt Hb). lia.
  Qed.

  Lemma heap_le_alloc_block h n : 0 <= n -> heap_le h (alloc_block h n).
  Proof.
    intros Hn. split; [intros; now apply allocated_alloc_block | intros b o Ho; simpl; now left].
  Qed.

  Lemma store_words_unchanged ws : forall m b o m',
    store_words m b o ws = Some m' ->
    Mem.unchanged_on (fun b' o' => ~ (b' = b /\ o <= o' < o + 8 * Z.of_nat (length ws))) m m'.
  Proof.
    induction ws as [| w ws IH]; simpl; intros m b o m' H.
    - inv H. apply Mem.unchanged_on_refl.
    - destruct (Mem.store Mptr m b o w) as [m1 |] eqn:Hst; [| discriminate].
      eapply Mem.unchanged_on_trans.
      + eapply Mem.store_unchanged_on; eauto.
        intros i Hi Hn. apply Hn. change (size_chunk Mptr) with 8 in Hi. split; auto. lia.
      + eapply Mem.unchanged_on_implies; [apply (IH _ _ _ _ H) |].
        intros b' o' Hn _ [Hb Ho]. apply Hn. split; auto. lia.
  Qed.

  Lemma store_words_perm ws : forall m b o m' b',
    store_words m b o ws = Some m' -> keeps_perm m m' b'.
  Proof.
    induction ws as [| w ws IH]; simpl; intros m b o m' b' H.
    - inv H. intros o' k p Hp. auto.
    - destruct (Mem.store Mptr m b o w) as [m1 |] eqn:Hst; [| discriminate].
      intros o' k p Hp. eapply IH; eauto. eapply Mem.perm_store_1; eauto.
  Qed.

  Lemma store_words_load ws : forall m b o m' i w,
    store_words m b o ws = Some m' ->
    nth_error ws i = Some w -> Val.load_result Mptr w = w ->
    Mem.load Mptr m' b (o + 8 * Z.of_nat i) = Some w.
  Proof.
    induction ws as [| w0 ws IH]; simpl; intros m b o m' i w H Hn Hw.
    - destruct i; discriminate.
    - destruct (Mem.store Mptr m b o w0) as [m1 |] eqn:Hst; [| discriminate].
      destruct i as [| i]; simpl in Hn.
      + inv Hn. eapply Mem.load_unchanged_on; [apply (store_words_unchanged _ _ _ _ _ H) | |].
        * intros j Hj [_ Hr]. change (size_chunk Mptr) with 8 in Hj. lia.
        * rewrite Z.add_0_r. erewrite Mem.load_store_same; eauto. congruence.
      + replace (o + 8 * Z.of_nat (S i)) with (o + 8 + 8 * Z.of_nat i) by lia. eauto.
  Qed.

  Lemma repr_fields_stored F h m b : forall vs ws o,
    Forall2 (repr_val F h m) vs ws ->
    (forall i w, nth_error ws i = Some w -> Mem.load Mptr m b (o + 8 * Z.of_nat i) = Some w) ->
    repr_fields F h m vs b o.
  Proof.
    induction vs as [| v vs IH]; intros ws o Hfa Hl; inv Hfa.
    - constructor.
    - econstructor; eauto.
      + specialize (Hl 0%nat y eq_refl). now rewrite Z.add_0_r in Hl.
      + eapply IH; eauto. intros i w Hn.
        specialize (Hl (S i) w Hn). rewrite <- Hl. f_equal. lia.
  Qed.

  (* Writing a header and the words [ws] at the start of the free space lays out a block,
     and keeps the data and the thread info *)
  Lemma new_block_repr F h fs m m0 m' tb tofs t vs ws ord :
    tinfo_wf h fs m tb tofs ->
    ctor_rep_of cenv t = Ret (Block ord (length vs)) ->
    0 <= ord <= max_block_ordinal -> vs <> [] ->
    Forall2 (repr_val F h m) vs ws ->
    free_start h + 8 * (Z.of_nat (length vs) + 1) <= free_end h ->
    Mem.store Mptr m (free_block h) (free_start h)
              (Vlong (Int64.repr (block_header ord (Z.of_nat (length vs))))) = Some m0 ->
    store_words m0 (free_block h) (free_start h + 8) ws = Some m' ->
    repr_val F (alloc_block h (Z.of_nat (length vs))) m' (Vconstr t vs)
             (Vptr (free_block h) (Ptrofs.repr (free_start h + 8))) /\
    data_kept h m (alloc_block h (Z.of_nat (length vs))) m' /\
    tinfo_wf (alloc_block h (Z.of_nat (length vs))) fs m' tb tofs.
  Proof.
    intros Hwf Hrep Hord Hnil Hvs Hroom Hst Hws.
    pose proof (wf_free _ _ _ _ _ _ _ _ Hwf) as [Hheap [Hs He] Hsize Hal Hp].
    pose proof (Forall2_length Hvs) as Hlen.
    (* the memory changes in the new block only *)
    assert (Hun : Mem.unchanged_on
                    (fun b o => ~ (b = free_block h /\
                                   free_start h <= o < free_start h + 8 * (Z.of_nat (length vs) + 1)))
                    m m').
    { eapply Mem.unchanged_on_trans.
      - eapply Mem.store_unchanged_on; eauto. intros i Hi Hnot. apply Hnot.
        change (size_chunk Mptr) with 8 in Hi. split; [reflexivity | lia].
      - eapply Mem.unchanged_on_implies; [apply (store_words_unchanged _ _ _ _ _ Hws) |].
        intros b o Hnot _ [Hb Ho]. apply Hnot. split; [exact Hb |]. rewrite <- Hlen in Ho. lia. }
    assert (Hkp : forall b, keeps_perm m m' b).
    { intros b o k p Hperm. eapply store_words_perm; [exact Hws |].
      eapply Mem.perm_store_1; eauto. }
    assert (Hk : data_kept h m (alloc_block h (Z.of_nat (length vs))) m').
    { split; [| apply heap_le_alloc_block; lia].
      eapply Mem.unchanged_on_implies; [exact Hun |].
      intros b o [_ Hlt] _ [Hb Ho]. specialize (Hlt Hb). lia. }
    assert (Hu : Ptrofs.unsigned (Ptrofs.repr (free_start h + 8)) = free_start h + 8).
    { apply Ptrofs.unsigned_repr. lia. }
    split; [| split; [exact Hk |]].
    - (* the new block *)
      econstructor; eauto; rewrite Hu.
      + simpl. right. split; reflexivity.
      + lia.
      + lia.
      + intros o Ho. split; auto. unfold alloc_block; simpl. intros _. lia.
      + replace (free_start h + 8 - 8) with (free_start h) by lia.
        eapply Mem.load_unchanged_on; [apply (store_words_unchanged _ _ _ _ _ Hws) | |].
        * intros i Hi [_ Hr]. change (size_chunk Mptr) with 8 in Hi. lia.
        * erewrite Mem.load_store_same; eauto. reflexivity.
      + eapply repr_fields_stored.
        * eapply Forall2_impl; [| eassumption]. intros. eapply repr_val_kept; eauto.
        * intros i w Hn. eapply store_words_load; eauto.
          destruct (Forall2_nth_r _ _ _ Hvs _ _ Hn) as (v & _ & Hv).
          eapply repr_val_load_result; eauto.
    - (* the thread info *)
      assert (Hwf1 : tinfo_wf h fs m' tb tofs).
      { eapply tinfo_wf_region
          with (R := fun b o => b = free_block h /\
                                free_start h <= o < free_start h + 8 * (Z.of_nat (length vs) + 1));
          eauto.
        intros b o [-> Ho] Hdep.
        destruct (tinfo_dep_inv _ _ _ _ _ _ _ Hwf Hdep) as [[_ Hn] | [(Hnh & _) | [Hb _]]].
        - apply Hn. split; [reflexivity | lia].
        - contradiction.
        - rewrite Hb in Hheap. eapply wf_block; eauto. }
      destruct Hwf1 as [Hrange Hperm Hblock Hlimit Hfree Hfp Hfs Hvalid Hgc1].
      constructor; auto.
      + destruct Hfree as [? [? ?] ? Hal' Hp']. constructor; unfold alloc_block; simpl; auto; try lia.
        * apply Z.divide_add_r; auto. apply Z.divide_factor_l.
        * intros o Ho. apply Hp'. lia.
      + rewrite Forall_forall in *. intros fr Hin.
        destruct (Hfs fr Hin) as [? ? ? ? Hv ? ? ?]. constructor; auto.
        intros i Hi. destruct (Hv i Hi) as (w & Hw & Hval). exists w. split; auto.
        eapply is_value_kept; [| exact Hval].
        split; [apply Mem.unchanged_on_refl | apply heap_le_alloc_block; lia].
      + (* the collector's invariant *)
        rewrite Hlen. apply (gc_alloc _ _ _ Hcol h m m0 m' tb tofs ord ws).
        * exact (wf_gc _ _ _ _ _ _ _ _ Hwf).
        * exact Hord.
        * intros Hw. apply Hnil. destruct vs; [reflexivity |]. rewrite Hw in Hlen. discriminate.
        * apply Forall_forall. intros w Hin. destruct (In_nth_error _ _ Hin) as [j Hj].
          destruct (Forall2_nth_r _ _ _ Hvs _ _ Hj) as (v & _ & Hv). exists v.
          eapply repr_val_mono; [| apply heap_le_refl | exact Hv]. auto.
        * rewrite <- Hlen. exact Hroom.
        * rewrite <- Hlen. exact Hst.
        * exact Hws.
  Qed.

  (** * The collector *)

  (* A change in [tinfo->args] *)
  Lemma tinfo_args_change h fs m m' tb tofs :
    tinfo_ok h fs m tb tofs ->
    Mem.unchanged_on (fun b o => ~ (b = tb /\ tofs + args_ofs <= o < tofs + fp_ofs)) m m' ->
    (forall b, keeps_perm m m' b) ->
    tinfo_ok h fs m' tb tofs /\ data_kept h m h m' /\
    (forall b o, root_at tb tofs 0 fs b o -> still_represented h m h m' b o) /\
    changes (fun _ _ => False) tb tofs fs h m h m'.
  Proof.
    intros [Hwf Hal] Hun Hkp.
    assert (Hk : data_kept h m h m').
    { split; auto. eapply Mem.unchanged_on_implies; eauto.
      intros b o [Hh _] _ [Hb _]. rewrite Hb in Hh. eapply wf_block; eauto. }
    split; [| split; [exact Hk | split]].
    - split.
      + eapply tinfo_wf_region
          with (R := fun b o => b = tb /\ tofs + args_ofs <= o < tofs + fp_ofs); eauto.
        intros b o [-> Ho] Hdep.
        destruct (tinfo_dep_inv _ _ _ _ _ _ _ Hwf Hdep) as [[Hh _] | [(_ & Hne & _) | [_ Hr]]].
        * eapply wf_block; eauto.
        * congruence.
        * ofs_lia.
      + eapply Mem.load_unchanged_on; [exact Hun | | exact Hal].
        intros i Hi [_ Hr]. change (size_chunk Mptr) with 8 in Hi. ofs_lia.
    - intros b o [[_ (j & Hj & _)] | (fr & j & Hin & Hj & -> & ->)]; [lia |].
      apply still_represented_kept; auto. intros w Hw.
      eapply Mem.load_unchanged_on; [exact Hun | | exact Hw]. intros o' _ [Heq _].
      pose proof (wf_frames _ _ _ _ _ _ _ _ Hwf) as Hfs. rewrite Forall_forall in Hfs.
      destruct (frame_tinfo _ _ _ _ _ _ (Hfs fr Hin)) as [_ Hrt]. contradiction.
    - split; [| split].
      + eapply Mem.unchanged_on_implies; [exact Hun |].
        intros b o (_ & Hnt & _) _ [-> Ho]. apply Hnt. split; auto. ofs_lia.
      + intros b o k p _ _ Hp. apply Hkp. exact Hp.
      + intros b Hb. now left.
  Qed.

End Properties.
