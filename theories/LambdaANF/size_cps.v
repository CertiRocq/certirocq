(* Size of LambdaANF term, values, environments, etc. Part of the CertiRocq project.
 * Author: Anonymized, 2017
 *)


From Stdlib Require Import ZArith List SetoidList NArith.BinNat PArith.BinPos
     MSets.MSetRBT Sets.Ensembles micromega.Lia Sorting.Permutation.
From CertiRocq.LambdaANF Require Import List_util term ctx identifiers Ensembles_util set_util term_util map_util.

Require Import compcert.lib.Maps.

Import ListNotations.


(** * Size of LambdaANF terms, values and environments, needed to express the upper bound on the execution cost of certain transformations *)

(** The size of LambdaANF expressions. Right now we only count the number of
  * variables in a program (free or not), the number of functions and
  * the number of function definition blocks *)
Fixpoint sizeOf_exp (e : exp) : nat :=
  match e with
    | Econstr x _ ys e => length ys + sizeOf_exp e
    | Ecase x l =>
      1  + (fix sizeOf_l l :=
              match l with
                | [] => 0
                | (t, e) :: l => sizeOf_exp e + sizeOf_l l
              end) l
    | Eproj x _ _ y e => 1 + sizeOf_exp e
    | Eletapp x f _ ys e => 1 + length ys + sizeOf_exp e
    | Efun B e => 1 + sizeOf_fundefs B + sizeOf_exp e
    | Eapp x _ ys => 1 + length ys
    | Eprim_val x _ e => 1 + sizeOf_exp e
    | Eprim x _ ys e => 1 + length ys + sizeOf_exp e
    | Ehalt x => 1
  end
with sizeOf_fundefs (B : fundefs) : nat :=
       match B with
         | Fcons _ _ xs e B =>
           1 + sizeOf_exp e + sizeOf_fundefs B
         | Fnil => 0
       end.

Definition cost_cc (e : exp) : nat :=
  match e with
  | Econstr x t ys e => 1 + length ys
  | Eproj x t n y e => 1
  | Ecase y cl => 1
  | Eapp f t ys => 1 + length ys
  | Eletapp x f t ys e => 1 + length ys
  | Efun B e => 1 + PS.cardinal (fundefs_fv B)
  | Eprim_val x p e => 1
  | Eprim x f ys e => 1 + length ys
  | Ehalt x => 1
  end.

(** The size of evaluation contexts *)
Fixpoint sizeOf_exp_ctx (c : exp_ctx) : nat :=
  match c with
    | Hole_c => 0
    | Econstr_c _ _ ys c => 1 + length ys + sizeOf_exp_ctx c
    | Eproj_c _ _ _ _ c => 1 + sizeOf_exp_ctx c
    | Eprim_val_c _ _ c => 1 + sizeOf_exp_ctx c
    | Eprim_c _ _ ys c => 1 + length ys + sizeOf_exp_ctx c
    | Eletapp_c _ f _ ys c => 1 + length ys + sizeOf_exp_ctx c
    | Ecase_c _ l1 _ c l2  =>
      1 + sizeOf_exp_ctx c
      + fold_left (fun s p => s + sizeOf_exp (snd p)) l1 0
      + fold_left (fun s p => s + sizeOf_exp (snd p)) l2 0
    | Efun1_c B c => 1 + sizeOf_exp_ctx c
    | Efun2_c B e => 1 + sizeOf_fundefs_ctx B + sizeOf_exp e
  end
with sizeOf_fundefs_ctx (B : fundefs_ctx) : nat :=
       match B with
         | Fcons1_c _ _ xs c B =>
           1 + length xs + sizeOf_exp_ctx c + sizeOf_fundefs B
         | Fcons2_c _ _ xs e B =>
           1 + length xs + sizeOf_exp e + sizeOf_fundefs_ctx B
       end.

(* Compute the maximum of a tree given a measure function *)
Definition max_ptree_with_measure {A} (f : A -> nat) (i : nat) (rho : M.t A) :=
  M.fold (fun c _ v => max c (f v)) rho i.

Lemma Mfold_monotonic {A} f1 f2 (rho : M.t A) n1 n2 :
  (forall x1 x1' x2 x3, x1 <= x1' -> f1 x1 x2 x3 <= f2 x1' x2 x3) ->
  n1 <= n2 ->
  M.fold f1 rho n1 <= M.fold f2 rho n2.
Proof.
  rewrite !M.fold_spec.
  intros. eapply fold_left_monotonic; eauto.
Qed.

Lemma max_ptree_with_measure_spec1 {A} (f : A -> nat) i rho x v :
  rho ! x = Some v ->
  f v <= max_ptree_with_measure f i rho.
Proof.
  intros Hget. unfold max_ptree_with_measure.
  rewrite M.fold_spec.
  assert (List.In (x, v) (M.elements rho))
    by (eapply PTree.elements_correct; eauto).
  revert H. generalize (M.elements rho).
  intros l Hin. induction l. now inv Hin.
  inv Hin.
  - simpl. eapply Nat.le_trans. now apply Nat.le_max_r.
    eapply fold_left_extensive.
    intros [y u] n; simpl. now apply Nat.le_max_l.
  - simpl. eapply Nat.le_trans. now eapply IHl; eauto.
    eapply fold_left_monotonic.
    intros. now eapply Nat.max_le_compat_r; eauto.
    now apply Nat.le_max_l.
Qed.


(** Stratified size for values *)
Fixpoint sizeOf_val' (i : nat) (v : val) : nat :=
  match i with
    | 0 => 0
    | S i' =>
      (fix aux v : nat :=
       let sizeOf_env rho := max_ptree_with_measure (sizeOf_val' i') 0 rho in
       match v with
         | Vconstr _ vs => max_list_nat_with_measure aux 0 vs
         | Vfun rho B f =>
           max (sizeOf_fundefs B) (sizeOf_env rho)
         | Vprim _ => 0
         (* Ignore Vint, it's not used *)
         | Vint x => 0
       end) v
  end.

(** Size of environments.
  * The size of an environment is the size of the maximum value stored in it *)
Definition sizeOf_env i rho := max_ptree_with_measure (sizeOf_val' i) 0 rho.

(** Equivalent definition *)
Definition sizeOf_val (i : nat) (v : val) : nat :=
  match i with
    | 0 => 0
    | S i' =>
      match v with
        | Vconstr _ vs =>
          max_list_nat_with_measure (sizeOf_val' i) 0 vs
        | Vfun rho B f =>
          max (sizeOf_fundefs B) (sizeOf_env i' rho)
        | Vprim _ => 0
        | Vint x => 0
      end
  end.

Lemma sizeOf_val_eq i v :
  sizeOf_val' i v = sizeOf_val i v.
Proof.
  revert v; induction i; eauto.
  induction v using val_ind'; eauto.
Qed.

Opaque sizeOf_val'.

Lemma sizeOf_val_Vconstr_unfold i t v l:
  sizeOf_val i (Vconstr t (v :: l)) =
  max (sizeOf_val i v) (sizeOf_val i (Vconstr t l)).
Proof.
  destruct i; simpl (sizeOf_val _ (Vconstr t _)); eauto.
  rewrite <- (Nat.max_0_l (sizeOf_val' (S i) v)).
  unfold max_list_nat_with_measure.
  rewrite (fold_left_comm (fun (c : nat) (v0 : val) => Init.Nat.max c (sizeOf_val' (S i) v0))); eauto.
  rewrite Nat.max_comm, sizeOf_val_eq. reflexivity.
  intros. now rewrite <- !Nat.max_assoc, (Nat.max_comm (sizeOf_val' (S i) y)).
Qed.

Lemma sizeOf_val_monotic i i' v :
  i <= i' ->
  sizeOf_val i v <= sizeOf_val i' v.
Proof.
  revert i' v. induction i as [i IHi] using lt_wf_rec1; intros i' v.
  destruct i; try (simpl; lia). intros Hlt.
  induction v using val_ind'.
  - destruct i'; simpl; lia.
  - destruct i'; try now (simpl; lia).
    rewrite !sizeOf_val_Vconstr_unfold.
    eapply Nat.max_le_compat; eauto.
  - destruct i'; try now (simpl; lia).
    eapply Nat.max_le_compat; eauto.
    unfold sizeOf_env. eapply Mfold_monotonic; eauto.
    intros. eapply Nat.max_le_compat; eauto.
    rewrite !sizeOf_val_eq; eapply IHi; lia.
  - destruct i'; simpl; lia.
  - destruct i'; simpl; lia.
Qed.

Lemma sizeOf_env_monotic i i' v :
  i <= i' ->
  sizeOf_env i v <= sizeOf_env i' v.
Proof.
  intros Hi. unfold sizeOf_env.
  eapply Mfold_monotonic; eauto.
  intros. eapply Nat.max_le_compat; eauto.
  rewrite !sizeOf_val_eq. now eapply sizeOf_val_monotic.
Qed.

Lemma sizeOf_env_O rho :
  sizeOf_env 0 rho = 0.
Proof.
  unfold sizeOf_env, max_ptree_with_measure.
  rewrite M.fold_spec. generalize (M.elements rho).
  induction l; eauto.
Qed.

(** Number of function definitions in an expression *)
Fixpoint num_fundefs_in_exp (e : exp) : nat :=
  match e with
    | Econstr x _ ys e => num_fundefs_in_exp e
    | Ecase x l =>
      1 + (fix num l :=
             match l with
               | [] => 0
               | (t, e) :: l => num_fundefs_in_exp e + num l
             end) l
    (* Maybe 1 + should be removed?*)
    | Eproj x _ _ y e => 1 + num_fundefs_in_exp e
    | Eletapp x _ _ y e => num_fundefs_in_exp e
    | Efun B e => 1 + num_fundefs_in_fundefs B + num_fundefs_in_exp e
    | Eapp x _ ys => 0
    | Eprim_val x _ e => num_fundefs_in_exp e
    | Eprim x _ ys e => num_fundefs_in_exp e
    | Ehalt x => 0
  end
with num_fundefs_in_fundefs (B : fundefs) : nat :=
  match B with
    | Fcons _ _ xs e B => num_fundefs_in_exp e + num_fundefs_in_fundefs B
    | Fnil => 0
  end.

Fixpoint num_fundefs_val (i : nat) (v : val) :=
  match i with
  | 0 => 0
  | S i' =>
    (fix aux v : nat :=
     let num_fundefs_in_env rho := max_ptree_with_measure (num_fundefs_val i') 0 rho in
     match v with
       | Vconstr _ vs => max_list_nat_with_measure aux 0 vs
       | Vfun rho B f =>
         max (num_fundefs_in_fundefs B) (num_fundefs_in_env rho)
       | Vprim _ => 0
       | Vint x => 0
     end) v
  end.

Definition num_fundefs_in_env i rho := max_ptree_with_measure (num_fundefs_val i) 0 rho.

Definition num_fundefs_in_exp_env i e rho := max (num_fundefs_in_exp e) (num_fundefs_in_env i rho).

Lemma numOf_fundefs_le_sizeOf_fundefs B :
  numOf_fundefs B <= sizeOf_fundefs B.
Proof.
  induction B; eauto; simpl; lia.
Qed.

Lemma sizeOf_env_set k rho x v :
  sizeOf_env k (M.set x v rho) = max (sizeOf_val k v) (sizeOf_env k rho).
Proof.
(* Obvious but seems painful, admitting for now *)
Abort.

Lemma max_list_nat_acc_spec {A} (xs : list A) f acc :
  max_list_nat_with_measure f acc xs =
  max acc (max_list_nat_with_measure f 0 xs).
Proof.
  rewrite <- (Nat.max_0_r acc) at 1. generalize 0.
  revert acc. induction xs; intros acc n; simpl; eauto.
  rewrite <- Nat.max_assoc. eauto.
Qed.

Lemma sizeOf_env_set_lists k rho rho' xs vs :
  set_lists xs vs rho = Some rho' ->
  sizeOf_env k rho' = max (max_list_nat_with_measure (sizeOf_val k) 0 vs) (sizeOf_env k rho).
Proof.
  (* revert vs rho rho'. induction xs; intros vs rho rho' Hset. *)
  (* - destruct vs; try discriminate. inv Hset. *)
  (*   reflexivity. *)
  (* - destruct vs; try discriminate. *)
  (*   simpl in Hset. destruct (set_lists xs vs rho) eqn:Hset'; try discriminate. *)
  (*   inv Hset. rewrite sizeOf_env_set; simpl. *)
  (*   rewrite max_list_nat_acc_spec. *)
  (*   rewrite <- Nat.max_assoc. eapply Nat.max_compat. reflexivity. *)
  (*   eauto. *)
Abort.

Lemma sizeOf_env_get k rho x v :
  rho ! x = Some v ->
  sizeOf_val k v <= sizeOf_env k rho.
Proof.
  intros Hget.
  unfold sizeOf_env. rewrite <- sizeOf_val_eq.
  eapply max_ptree_with_measure_spec1.
  eassumption.
Qed.

Lemma sizeOf_env_get_list k rho xs vs :
  get_list xs rho = Some vs ->
  max_list_nat_with_measure (sizeOf_val k) 0 vs  <= sizeOf_env k rho.
Proof.
  revert vs. induction xs; intros vs Hgetl.
  - destruct vs; try discriminate; simpl; lia.
  - simpl in Hgetl.
    destruct (rho ! a) eqn:Hgeta; try discriminate.
    destruct (get_list xs rho) eqn:Hgetl'; try discriminate.
    destruct vs; try discriminate. inv Hgetl. simpl.
    eapply Nat.le_trans.
    + rewrite <- (Nat.max_0_l (sizeOf_val k v0)).
      unfold max_list_nat_with_measure.
      rewrite (fold_left_comm (fun (c : nat) (v : val) => Init.Nat.max c (sizeOf_val k v))).
      eapply Nat.max_le_compat. eapply IHxs. reflexivity.
      eapply sizeOf_env_get. eassumption.
      intros x v1 v2. rewrite <- !Nat.max_assoc, (Nat.max_comm (sizeOf_val k v1)).
      reflexivity.
    + eapply Nat.max_lub; lia.
Qed.



Lemma max_list_nat_monotonic (A : Type) (f1 f2 : A -> nat) (l : list A) (n1 n2 : nat) :
  (forall (x1 : A), f1 x1 <= f2 x1) ->
  n1 <= n2 ->
  max_list_nat_with_measure f1 n1 l <= max_list_nat_with_measure f2 n2 l.
Proof.
  unfold max_list_nat_with_measure.
  intros. eapply fold_left_monotonic; eauto.
  intros. eapply Nat.max_le_compat; eauto.
Qed.


Lemma sizeOf_exp_grt_1 e :
  1 <= sizeOf_exp e.
Proof.
  induction e using exp_ind'; simpl; eauto; lia.
Qed.

(** Lemmas about context sizes *)
Lemma sizeOf_exp_ctx_comp_ctx_mut :
  (forall C1 C2,
     sizeOf_exp_ctx (comp_ctx_f C1 C2) = sizeOf_exp_ctx C1 + sizeOf_exp_ctx C2) /\
  (forall B e,
     sizeOf_fundefs_ctx (comp_f_ctx_f B e) = sizeOf_fundefs_ctx B + sizeOf_exp_ctx e).
Proof.
  exp_fundefs_ctx_induction IHe IHB;
  try (intros C; simpl; eauto; rewrite IHe; lia);
  try (intros C; simpl; eauto; rewrite IHB; lia).
  (* probably tactic misses an intro pattern *)
  intros l' C. simpl. rewrite IHe; lia.
Qed.

Corollary sizeOf_exp_ctx_comp_ctx :
  forall C1 C2,
    sizeOf_exp_ctx (comp_ctx_f C1 C2) = sizeOf_exp_ctx C1 + sizeOf_exp_ctx C2.
Proof.
  eapply sizeOf_exp_ctx_comp_ctx_mut; eauto.
Qed.

Corollary sizeOf_fundefs_ctx_comp_f_ctx :
  forall B e,
    sizeOf_fundefs_ctx (comp_f_ctx_f B e) = sizeOf_fundefs_ctx B + sizeOf_exp_ctx e.
Proof.
  eapply sizeOf_exp_ctx_comp_ctx_mut; eauto.
Qed.


Lemma fun_in_fundefs_sizeOf_exp B f tau xs e :
  fun_in_fundefs B (f, tau, xs, e) ->
  sizeOf_exp e <= sizeOf_fundefs B.
Proof.
  intros Hin. induction B; inv Hin.
  - inv H. simpl; lia.
  - eapply Nat.le_trans. eapply IHB; eauto.
    simpl. lia.
Qed.

  (** *  Useful definitions and lemmas for the  bound. *)

Definition max_exp_env (k : nat) (e : exp) rho :=
  max (sizeOf_exp e) (sizeOf_env k rho).


Lemma max_exp_env_grt_1 k e rho :
  1 <= max_exp_env k e rho.
Proof.
  unfold max_exp_env.
  eapply Nat.le_trans. now apply sizeOf_exp_grt_1.
  eapply Nat.le_max_l.
Qed.

(** Lemmas used to establish the upper bound given the IH *)

Lemma max_exp_env_Econstr k x t ys e rho :
  max_exp_env k e rho <= max_exp_env k (Econstr x t ys e) rho.
Proof.
  eapply Nat.max_le_compat_r.
  simpl. lia.
Qed.

Lemma max_exp_env_Eproj k x t N y e rho :
  max_exp_env k e rho <= max_exp_env k (Eproj x t N y e) rho.
Proof.
  eapply Nat.max_le_compat_r.
  simpl. lia.
Qed.

Lemma max_exp_env_Ecase_cons_hd k x c e l rho :
  max_exp_env k e rho <= max_exp_env k (Ecase x ((c, e) :: l)) rho.
Proof.
  eapply Nat.max_le_compat_r.
  simpl. lia.
Qed.

Lemma max_exp_env_Ecase_cons_tl k x c e l rho :
  max_exp_env k (Ecase x l) rho <= max_exp_env k (Ecase x ((c, e) :: l)) rho.
Proof.
  eapply Nat.max_le_compat_r.
  simpl. lia.
Qed.

Lemma max_exp_env_Eprim k x f ys e rho :
  max_exp_env k e rho <= max_exp_env k (Eprim x f ys e) rho.
Proof.
  eapply Nat.max_le_compat_r.
  simpl. lia.
Qed.

(* Lemma about the number of free variables *)
Lemma occurs_free_cardinality_mut :
  (forall e FVs,
     FromList FVs \subset occurs_free e ->
     NoDup FVs ->
     length FVs <= sizeOf_exp e) /\
  (forall B FVs,
     FromList FVs \subset occurs_free_fundefs B ->
     NoDup FVs ->
     length FVs <= sizeOf_fundefs B).
Proof.
  exp_defs_induction IHe IHl IHb; intros FVs Heq Hnd;
  try repeat normalize_occurs_free_in_ctx; simpl.
  - edestruct (@FromList_Union_split var) as [l1 [l2 [HP [Hin1 Hin2]]]].
    eassumption.
    rewrite <- HP in Hnd.
    eapply Permutation_length in HP. rewrite <- HP.
    rewrite length_app.
    eapply (Included_trans (FromList l2) (Setminus var (occurs_free e) [set v])) in Hin2;
      [| now apply Setminus_Included ].
    eapply Same_set_FromList_length in Hin1.
    eapply IHe in Hin2. lia.
    eapply NoDup_cons_r; eauto.
    eapply NoDup_cons_l; eauto.
  - rewrite <- (Union_Empty_set_neut_r [set v]) in Heq.
    rewrite <- FromList_nil, <- FromList_cons in Heq.
    eapply Same_set_FromList_length in Heq; eauto.
  - rewrite Union_commut, <- Union_assoc, (Union_commut (occurs_free (Ecase v l))),
    (Union_Same_set [set v]) in Heq.
    edestruct (@FromList_Union_split var) as [l1 [l2 [HP [Hin1 Hin2]]]].
    eassumption.
    rewrite <- HP in Hnd.
    eapply Permutation_length in HP. rewrite <- HP.
    rewrite !length_app.
    eapply IHe in Hin1. eapply IHl in Hin2. simpl in *. lia.
    eapply NoDup_cons_r; eauto.
    eapply NoDup_cons_l; eauto.
    eapply Singleton_Included. eauto.
  - edestruct (@FromList_Union_split var) as [l1 [l2 [HP [Hin1 Hin2]]]].
    eassumption.
    rewrite <- HP in Hnd.
    eapply Permutation_length in HP. rewrite <- HP.
    rewrite length_app.
    eapply (Included_trans (FromList l2) (Setminus var (occurs_free e) [set v])) in Hin2;
      [| now apply Setminus_Included ].
    rewrite <- (Union_Empty_set_neut_r [set v0]) in Hin1.
    rewrite <- FromList_nil, <- FromList_cons in Hin1.
    eapply Same_set_FromList_length in Hin1.
    eapply IHe in Hin2. simpl in *. lia.
    eapply NoDup_cons_r; eauto.
    eapply NoDup_cons_l; eauto.
  - edestruct (@FromList_Union_split var) as [l1 [l2 [HP [Hin1 Hin2]]]].
    eassumption.
    rewrite <- HP in Hnd.
    eapply Permutation_length in HP. rewrite <- HP.
    rewrite length_app.
    eapply (Included_trans (FromList l2) (Setminus var (occurs_free e) [set x])) in Hin2;
      [| now apply Setminus_Included ].
    rewrite <- FromList_cons in Hin1.
    eapply Same_set_FromList_length in Hin1.
    eapply IHe in Hin2. simpl in Hin1. lia.
    eapply NoDup_cons_r; eauto.
    eapply NoDup_cons_l; eauto.
  - edestruct (@FromList_Union_split var) as [l1 [l2 [HP [Hin1 Hin2]]]].
    eassumption.
    rewrite <- HP in Hnd.
    eapply Permutation_length in HP. rewrite <- HP.
    rewrite length_app.
    eapply (Included_trans (FromList l2) (Setminus var (occurs_free e) _)) in Hin2;
      [| now apply Setminus_Included ].
    eapply IHb in Hin1. eapply IHe in Hin2. lia.
    eapply NoDup_cons_r; eauto.
    eapply NoDup_cons_l; eauto.
  - edestruct (@FromList_Union_split var) as [l1 [l2 [HP [Hin1 Hin2]]]].
    eassumption. rewrite <- HP in Hnd.
    eapply Same_set_FromList_length in Hin1; eauto.
    eapply Permutation_length in HP. rewrite <- HP.
    rewrite length_app.
    rewrite <- (Union_Empty_set_neut_r [set v]) in Hin2.
    rewrite <- FromList_nil, <- FromList_cons in Hin2.
    eapply Same_set_FromList_length in Hin2.
    simpl in *. lia.
    eapply NoDup_cons_r; eauto.
    eapply NoDup_cons_l; eauto.
  - etransitivity. eapply IHe; eauto; try lia.
    2:{ lia. }
    now eapply (Included_trans (FromList FVs) (Setminus var (occurs_free e) [set v])) in Heq;
    [| now apply Setminus_Included ].
  - edestruct (@FromList_Union_split var) as [l1 [l2 [HP [Hin1 Hin2]]]].
    eassumption.
    rewrite <- HP in Hnd.
    eapply Permutation_length in HP. rewrite <- HP.
    rewrite length_app.
    eapply (Included_trans (FromList l2) (Setminus var (occurs_free e) [set v])) in Hin2;
      [| now apply Setminus_Included ].
    eapply Same_set_FromList_length in Hin1.
    eapply IHe in Hin2. lia.
    eapply NoDup_cons_r; eauto.
    eapply NoDup_cons_l; eauto.
  - rewrite <- (Union_Empty_set_neut_r [set v]) in Heq.
    rewrite <- FromList_nil, <- FromList_cons in Heq.
    eapply Same_set_FromList_length in Heq; eauto.
  - edestruct (@FromList_Union_split var) as [l1 [l2 [HP [Hin1 Hin2]]]].
    eassumption. rewrite <- HP in Hnd.
    eapply Permutation_length in HP. rewrite <- HP.
    rewrite length_app.
    eapply (Included_trans (FromList l2) (Setminus var _ [set v])) in Hin2;
      [| now apply Setminus_Included ].
    eapply (Included_trans (FromList l1) (Setminus var _ _)) in Hin1;
      [| now apply Setminus_Included ].
    eapply IHe in Hin1. eapply IHb in Hin2. lia.
    eapply NoDup_cons_r; eauto.
    eapply NoDup_cons_l; eauto.
  - rewrite <- FromList_nil in Heq.
    apply Same_set_FromList_length in Heq; eauto.
Qed.

Corollary occurs_free_cardinality :
  (forall e FVs,
     FromList FVs \subset occurs_free e ->
     NoDup FVs ->
     length FVs <= sizeOf_exp e).
Proof.
  eapply occurs_free_cardinality_mut.
Qed.

Corollary occurs_free_fundefs_cardinality :
  (forall B FVs,
     FromList FVs \subset occurs_free_fundefs B ->
     NoDup FVs ->
     length FVs <= sizeOf_fundefs B).
Proof.
  eapply occurs_free_cardinality_mut.
Qed.
