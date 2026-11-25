(* Correctness of [merge_dup_funs], which merges alpha-equivalent functions of
   the outermost function block.

   This file proves that one round of merging gives a term related to its input
   by the logical relation ([merge_round_correct]), and that it keeps unique
   bindings and adds no bound or free variables ([merge_round_syntax]). Then it
   proves the same for any number of rounds ([merge_dup_funs_iter]). *)

From Stdlib Require Import Lists.List NArith.BinNat PArith.BinPos micromega.Lia
     Sets.Ensembles Relations.Relations Arith.
Require Import compcert.lib.Coqlib.
Require Import LambdaANF.rel_comp.
Require Import LambdaANF.term LambdaANF.eval LambdaANF.identifiers LambdaANF.Ensembles_util
        LambdaANF.List_util LambdaANF.tactics LambdaANF.map_util LambdaANF.set_util
        LambdaANF.functions LambdaANF.term_util LambdaANF.algebra
        LambdaANF.logical_relations LambdaANF.alpha_conv LambdaANF.rename
        LambdaANF.shrink_cps_correct.
Require Import LambdaANF.merge_dup_funs.

Import ListNotations.

Close Scope Z_scope.


(** * Syntactic facts *)

(** [rename_exp] is the renaming [rename_all_ns] of [rename.v]. *)
Lemma rename_exp_rename_all_ns σ :
  (forall e, rename_exp σ e = rename_all_ns σ e) /\
  (forall B, rename_fds σ B = rename_all_fun_ns σ B).
Proof.
  exp_defs_induction IHe IHl IHB; intros; simpl; try rewrite IHe; try rewrite IHB;
    try reflexivity.
  simpl in IHl. injection IHl as Hl. now rewrite Hl.
Qed.

Lemma rename_exp_ns σ e : rename_exp σ e = rename_all_ns σ e.
Proof. apply rename_exp_rename_all_ns. Qed.

Lemma rename_fds_ns σ B : rename_fds σ B = rename_all_fun_ns σ B.
Proof. apply rename_exp_rename_all_ns. Qed.

Lemma rn_apply_r σ x : rn σ x = apply_r σ x.
Proof. reflexivity. Qed.

Lemma bound_var_rename_exp σ e : bound_var (rename_exp σ e) <--> bound_var e.
Proof. rewrite rename_exp_ns. symmetry. apply bound_var_rename_all_ns. Qed.

Lemma bound_var_rename_fds σ B :
  bound_var_fundefs (rename_fds σ B) <--> bound_var_fundefs B.
Proof. rewrite rename_fds_ns. symmetry. apply bound_var_rename_all_ns_fundefs. Qed.

Lemma name_in_fundefs_rename_fds σ B :
  name_in_fundefs (rename_fds σ B) <--> name_in_fundefs B.
Proof. induction B; simpl; [ rewrite IHB |]; reflexivity. Qed.

Lemma name_in_fundefs_rename_fds_iff σ B x :
  name_in_fundefs (rename_fds σ B) x <-> name_in_fundefs B x.
Proof. destruct (name_in_fundefs_rename_fds σ B) as [H1 H2]. split; [ apply H1 | apply H2 ]. Qed.

Lemma find_def_rename_fds σ f B t xs e :
  find_def f B = Some (t, xs, e) ->
  find_def f (rename_fds σ B) = Some (t, xs, rename_exp σ e).
Proof.
  induction B; simpl; intros H; [| discriminate ].
  destruct (M.elt_eq f v); [ inv H; reflexivity | eauto ].
Qed.

(** Function blocks as lists *)

Lemma list_to_fds_fds_to_list B : list_to_fds (fds_to_list B) = B.
Proof. induction B; simpl; congruence. Qed.

Lemma fun_in_fundefs_list_to_fds l f t xs e :
  fun_in_fundefs (list_to_fds l) (f, t, xs, e) <-> List.In (f, t, xs, e) l.
Proof.
  induction l as [| [[[g tg] ys] eg] l IH]; simpl.
  - split; intros H; inv H.
  - split; intros H.
    + inv H.
      * inv H0. now left.
      * right. now apply IH.
    + destruct H as [H | H].
      * inv H. left. constructor.
      * right. now apply IH.
Qed.

Lemma name_in_fundefs_list_to_fds l x :
  name_in_fundefs (list_to_fds l) x <-> List.In x (map fundef_name l).
Proof.
  induction l as [| [[[g tg] ys] eg] l IH]; simpl.
  - split; intros H; inv H.
  - split; intros H.
    + inv H.
      * inv H0. now left.
      * right. now apply IH.
    + destruct H as [H | H].
      * subst. left. constructor.
      * right. now apply IH.
Qed.

Lemma name_in_fundefs_fds_to_list B x :
  name_in_fundefs B x <-> List.In x (map fundef_name (fds_to_list B)).
Proof.
  rewrite <- name_in_fundefs_list_to_fds, list_to_fds_fds_to_list. reflexivity.
Qed.

Lemma unique_bindings_fundefs_NoDup_names B :
  unique_bindings_fundefs B -> NoDup (map fundef_name (fds_to_list B)).
Proof.
  induction B; simpl; intros Hun; inv Hun; constructor; eauto.
  intros Hin. apply name_in_fundefs_fds_to_list in Hin.
  apply H5. now apply name_in_fundefs_bound_var_fundefs.
Qed.


(** Parameter lists *)

Lemma bind_vars_notin σ0 xs ys x :
  ~ List.In x xs -> M.get x (bind_vars σ0 xs ys) = M.get x σ0.
Proof.
  revert σ0 ys. induction xs as [| x' xs IH]; intros σ0 [| y' ys] Hnin; simpl; auto.
  rewrite IH by (intros Hc; apply Hnin; now right).
  rewrite M.gso; auto. intros ->. apply Hnin. now left.
Qed.

Lemma bind_vars_In σ0 xs ys x :
  List.In x xs -> length xs = length ys -> exists y, M.get x (bind_vars σ0 xs ys) = Some y.
Proof.
  revert σ0 ys. induction xs as [| x' xs IH]; intros σ0 [| y' ys] Hin Hlen;
    simpl in *; try discriminate; try contradiction.
  destruct (in_dec Pos.eq_dec x xs) as [Hin' | Hnin'].
  - apply IH; auto.
  - destruct Hin as [-> | Hin]; [| contradiction ].
    exists y'. rewrite bind_vars_notin by assumption. apply M.gss.
Qed.

Lemma bind_vars_get σ0 xs ys x y :
  M.get x (bind_vars σ0 xs ys) = Some y ->
  (exists i, nth_error xs i = Some x /\ nth_error ys i = Some y) \/ M.get x σ0 = Some y.
Proof.
  revert σ0 ys. induction xs as [| x' xs IH]; intros σ0 [| y' ys] Hget;
    simpl in Hget; auto.
  destruct (IH _ _ Hget) as [[i [Hx Hy]] | Hget'].
  - left. exists (S i). auto.
  - destruct (Pos.eq_dec x x') as [-> | Hneq].
    + rewrite M.gss in Hget'. inv Hget'. left. exists 0%nat. auto.
    + rewrite M.gso in Hget' by auto. auto.
Qed.

Lemma set_lists_nth_error {A} xs vs (rho rho' : M.t A) i x v :
  NoDup xs -> set_lists xs vs rho = Some rho' ->
  nth_error xs i = Some x -> nth_error vs i = Some v -> M.get x rho' = Some v.
Proof.
  revert vs rho' i. induction xs as [| y xs IH]; intros vs rho' i Hnd Hset Hx Hv.
  - destruct i; discriminate.
  - destruct vs as [| w vs]; [ discriminate |]. simpl in Hset.
    destruct (set_lists xs vs rho) as [rho0 |] eqn:Hset0; [| discriminate ].
    inv Hset. inv Hnd.
    destruct i as [| i]; simpl in Hx, Hv.
    + inv Hx. inv Hv. apply M.gss.
    + rewrite M.gso.
      * eapply IH; eauto.
      * intros ->. apply H1. eapply nth_error_In. eassumption.
Qed.

Lemma Forall2_nth_error_r {A B} (R : A -> B -> Prop) l1 l2 i a :
  Forall2 R l1 l2 -> nth_error l1 i = Some a ->
  exists b, nth_error l2 i = Some b /\ R a b.
Proof.
  intros Hall. revert i. induction Hall; intros [| i] Hnth; simpl in *; try discriminate.
  - inv Hnth. eauto.
  - eauto.
Qed.


(** * The specification of [merge_list] *)

Lemma andb_lazy_true (a b : bool) :
  (if a then b else false) = true -> a = true /\ b = true.
Proof. destruct a; auto; discriminate. Qed.

Lemma find_dup_spec d reps g :
  find_dup d reps = Some g ->
  exists r, List.In r reps /\ fundef_name r = g /\ fundef_eqb d r = true.
Proof.
  induction reps as [| r reps IH]; simpl; intros H; [ discriminate |].
  destruct (fundef_eqb d r) eqn:Heq.
  - inv H. eexists; eauto.
  - destruct (IH H) as [r' [Hin [Hn He]]]. eexists; eauto.
Qed.

Lemma find_callee_spec d gs keptm g :
  find_callee d gs keptm = Some g ->
  exists r, M.get g keptm = Some r /\ fundef_eqb d r = true.
Proof.
  induction gs as [| g' gs IH]; simpl; intros H; [ discriminate |].
  destruct (M.get g' keptm) as [r |] eqn:Hget; eauto.
  destruct (fundef_eqb d r) eqn:Heq; eauto.
  inv H. eauto.
Qed.

Lemma get_bucket_add_In t n d bs t' n' r :
  List.In r (get_bucket t' n' (add_to_bucket t n d bs)) ->
  r = d \/ List.In r (get_bucket t' n' bs).
Proof.
  unfold add_to_bucket. unfold get_bucket at 1.
  destruct (Pos.eq_dec t' t) as [-> | Hneq].
  - rewrite M.gss. destruct (Pos.eq_dec n' n) as [-> | Hneq'].
    + rewrite M.gss. intros [H | H]; auto.
    + rewrite M.gso by auto. unfold get_bucket.
      destruct (M.get t bs) as [m |]; auto.
  - rewrite M.gso by auto. auto.
Qed.

(** [merge_list] keeps a sub-block of the functions. Every other function is
    renamed to a kept function that [fundef_eqb] accepts. *)
Lemma merge_list_spec funs l :
  forall kept bs keptm σ K σ',
    NoDup (map fundef_name l) ->
    (forall t n r, List.In r (get_bucket t n bs) -> List.In r kept) ->
    (forall g r, M.get g keptm = Some r -> List.In r kept /\ fundef_name r = g) ->
    merge_list funs l kept bs keptm σ = (K, σ') ->
    exists K_new,
      K = rev kept ++ K_new /\
      incl K_new l /\
      (exists Brm, split_fds (list_to_fds K_new) Brm (list_to_fds l)) /\
      (forall x, ~ List.In x (map fundef_name l) -> M.get x σ' = M.get x σ) /\
      (forall d, List.In d K_new -> M.get (fundef_name d) σ' = M.get (fundef_name d) σ) /\
      (forall d, List.In d l ->
                 List.In d K_new \/
                 exists r, List.In r K /\ M.get (fundef_name d) σ' = Some (fundef_name r) /\
                           fundef_eqb d r = true).
Proof.
  induction l as [| d l IH]; intros kept bs keptm σ K σ' Hnd Hbs Hkm Hm.
  - simpl in Hm. inv Hm. exists [].
    split; [ now rewrite app_nil_r |].
    split; [ intros x [] |].
    split; [ exists Fnil; constructor |].
    split; [ auto |].
    split; intros d [].
  - destruct d as [[[f t] xs] e]. simpl in Hnd. inv Hnd.
    assert (Hfresh : forall x, List.In x (map fundef_name l) -> x <> f).
    { intros x Hin Heq. subst. contradiction. }
    (* the case where [d] is merged with a kept function [r] named [g] *)
    assert (Hmerged :
              forall g r,
                List.In r kept -> fundef_name r = g -> fundef_eqb (f, t, xs, e) r = true ->
                merge_list funs l kept bs keptm (M.set f g σ) = (K, σ') ->
                exists K_new,
                  K = rev kept ++ K_new /\
                  incl K_new ((f, t, xs, e) :: l) /\
                  (exists Brm, split_fds (list_to_fds K_new) Brm
                                         (list_to_fds ((f, t, xs, e) :: l))) /\
                  (forall x, ~ List.In x (map fundef_name ((f, t, xs, e) :: l)) ->
                             M.get x σ' = M.get x σ) /\
                  (forall d, List.In d K_new ->
                             M.get (fundef_name d) σ' = M.get (fundef_name d) σ) /\
                  (forall d, List.In d ((f, t, xs, e) :: l) ->
                             List.In d K_new \/
                             exists r, List.In r K /\
                                       M.get (fundef_name d) σ' = Some (fundef_name r) /\
                                       fundef_eqb d r = true)).
    { intros g r Hr Hrn Heqb Hm'.
      edestruct IH as (K_new & HK & Hincl & [Brm Hsplit] & Hout & Hkept & Hall);
        [ eassumption | eassumption | eassumption | eassumption |].
      exists K_new. split; [ eassumption |].
      split; [ intros x Hx; right; now apply Hincl |].
      split; [ eexists; constructor 2; eassumption |].
      split.
      { intros x Hx. rewrite Hout.
        - rewrite M.gso; auto. intros Heq. apply Hx. left. now subst.
        - intros Hc. apply Hx. now right. }
      split.
      { intros d' Hd'. rewrite Hkept by assumption. rewrite M.gso; auto.
        apply Hfresh. apply in_map. now apply Hincl. }
      intros d' [Hd' | Hd'].
      - subst d'. right. exists r. split; [| split; [| eassumption ] ].
        + rewrite HK. apply in_or_app. left. now apply -> in_rev.
        + simpl. rewrite Hout by assumption. rewrite M.gss. congruence.
      - now apply Hall. }
    simpl in Hm.
    destruct (find_callee (f, t, xs, e) (exp_callees funs f e []) keptm) as [g |] eqn:Hcal.
    + destruct (find_callee_spec _ _ _ _ Hcal) as [r [Hget Heqb]].
      destruct (Hkm _ _ Hget) as [Hr_kept Hr_name].
      eapply Hmerged; eassumption.
    + match type of Hm with
      | context [ find_dup ?d ?reps ] => destruct (find_dup d reps) as [g |] eqn:Hdup
      end.
      * destruct (find_dup_spec _ _ _ Hdup) as [r [Hr [Hr_name Heqb]]].
        eapply Hmerged; [ eapply Hbs; eassumption | eassumption | eassumption | eassumption ].
      * (* [d] is kept *)
        edestruct IH as (K_new & HK & Hincl & [Brm Hsplit] & Hout & Hkept & Hall);
          [ eassumption | | | eassumption |].
        { intros t' n' r Hr. apply get_bucket_add_In in Hr as [-> | Hr].
          - now left.
          - right. eapply Hbs. eassumption. }
        { intros g r Hget. destruct (Pos.eq_dec g f) as [-> | Hneq].
          - rewrite M.gss in Hget. inv Hget. split; [ now left | reflexivity ].
          - rewrite M.gso in Hget by auto. edestruct Hkm as [Hr Hn]; [ eassumption |].
            split; [ now right | assumption ]. }
        exists ((f, t, xs, e) :: K_new).
        split; [ rewrite HK; simpl; now rewrite <- app_assoc |].
        split; [ intros x [Hx | Hx]; [ now left | right; now apply Hincl ] |].
        split; [ eexists; constructor; eassumption |].
        split.
        { intros x Hx. apply Hout. intros Hc. apply Hx. now right. }
        split.
        { intros d' [Hd' | Hd'].
          - subst d'. simpl. apply Hout. assumption.
          - now apply Hkept. }
        intros d' [Hd' | Hd'].
        -- left. now left.
        -- destruct (Hall d' Hd') as [Hin | Hex].
           ++ left. now right.
           ++ right. exact Hex.
Qed.

(** The properties of one round of merging that the correctness proof uses.
    [B] is the original block, [K] the kept functions and [σ] the renaming. *)
Record merge_props (B : fundefs) (K : list fundef) (σ : M.t var) : Prop :=
  { mp_split : exists Brm, split_fds (list_to_fds K) Brm B;
    mp_dom : forall x y, M.get x σ = Some y -> name_in_fundefs B x;
    mp_range : forall x y, M.get x σ = Some y -> name_in_fundefs (list_to_fds K) y;
    mp_kept : forall x, name_in_fundefs (list_to_fds K) x -> M.get x σ = None;
    mp_funs :
      forall f t xs e,
        fun_in_fundefs B (f, t, xs, e) ->
        fun_in_fundefs (list_to_fds K) (f, t, xs, e) \/
        exists g t' xs' e',
          fun_in_fundefs (list_to_fds K) (g, t', xs', e') /\
          M.get f σ = Some g /\
          fundef_eqb (f, t, xs, e) (g, t', xs', e') = true }.

Lemma merge_list_props funs B K σ :
  unique_bindings_fundefs B ->
  merge_list funs (fds_to_list B) [] (M.empty _) (M.empty _) (M.empty _) = (K, σ) ->
  merge_props B K σ.
Proof.
  intros Hun Hm.
  edestruct (merge_list_spec funs (fds_to_list B) [] (M.empty _) (M.empty _) (M.empty _) K σ)
    as (K_new & HK & Hincl & [Brm Hsplit] & Hout & Hkept & Hall).
  - now apply unique_bindings_fundefs_NoDup_names.
  - intros t n r Hr. unfold get_bucket in Hr. rewrite M.gempty in Hr. inv Hr.
  - intros g r Hget. rewrite M.gempty in Hget. discriminate.
  - exact Hm.
  - simpl in HK. subst K_new.
    rewrite list_to_fds_fds_to_list in Hsplit.
    assert (Hdom : forall x y, M.get x σ = Some y ->
                               List.In x (map fundef_name (fds_to_list B))).
    { intros x y Hget.
      destruct (in_dec Pos.eq_dec x (map fundef_name (fds_to_list B))) as [Hin | Hnin];
        auto.
      rewrite Hout in Hget by assumption. rewrite M.gempty in Hget. discriminate. }
    constructor.
    + eauto.
    + intros x y Hget. apply name_in_fundefs_fds_to_list. eapply Hdom. eassumption.
    + intros x y Hget. pose proof (Hdom _ _ Hget) as Hx.
      apply in_map_iff in Hx as [d [Hdn Hd]].
      destruct (Hall d Hd) as [HdK | [r [HrK [Hget' _]]]].
      * pose proof (Hkept d HdK) as Hk. rewrite M.gempty, Hdn, Hget in Hk. discriminate.
      * subst x. rewrite Hget in Hget'. inv Hget'.
        apply name_in_fundefs_list_to_fds. now apply in_map.
    + intros x Hx. apply name_in_fundefs_list_to_fds in Hx.
      apply in_map_iff in Hx as [d [<- Hd]]. rewrite Hkept by assumption.
      apply M.gempty.
    + intros f t xs e Hf.
      assert (HinB : List.In (f, t, xs, e) (fds_to_list B)).
      { apply fun_in_fundefs_list_to_fds. now rewrite list_to_fds_fds_to_list. }
      destruct (Hall _ HinB) as [HinK | [[[[g t'] xs'] e'] [HrK [Hget Heqb]]]].
      * left. now apply fun_in_fundefs_list_to_fds.
      * right. exists g, t', xs', e'.
        split; [ now apply fun_in_fundefs_list_to_fds |].
        split; [ exact Hget | exact Heqb ].
Qed.

Section MergeProps.

  Context (B : fundefs) (K : list fundef) (σ : M.t var)
          (Hun : unique_bindings_fundefs B)
          (Hmp : merge_props B K σ).

  Lemma merge_props_unique_K : unique_bindings_fundefs (list_to_fds K).
  Proof.
    destruct (mp_split _ _ _ Hmp) as [Brm Hsplit].
    edestruct split_fds_unique_bindings_fundefs_l as [H1 _]; eassumption.
  Qed.

  Lemma merge_props_names_K : name_in_fundefs (list_to_fds K) \subset name_in_fundefs B.
  Proof.
    destruct (mp_split _ _ _ Hmp) as [Brm Hsplit].
    rewrite (split_fds_name_in_fundefs _ _ _ Hsplit). now sets.
  Qed.

  Lemma merge_props_fun_in_K f t xs e :
    fun_in_fundefs (list_to_fds K) (f, t, xs, e) -> fun_in_fundefs B (f, t, xs, e).
  Proof.
    destruct (mp_split _ _ _ Hmp) as [Brm Hsplit].
    intros Hin. eapply split_fds_fun_in_fundefs; [ eassumption |]. now left.
  Qed.

  (** Every function name of [B] is renamed to the name of a kept function. *)
  Lemma merge_props_rn_names x :
    name_in_fundefs B x -> name_in_fundefs (list_to_fds K) (rn σ x).
  Proof.
    intros Hx.
    destruct (name_in_fundefs_find_def_is_Some _ _ Hx) as (t & xs & e & Hfind).
    apply find_def_correct in Hfind.
    destruct (mp_funs _ _ _ Hmp _ _ _ _ Hfind) as [HK | (g & t' & xs' & e' & HK & Hget & _)].
    - apply fun_in_fundefs_name_in_fundefs in HK.
      unfold rn. rewrite (mp_kept _ _ _ Hmp _ HK). exact HK.
    - unfold rn. rewrite Hget. eapply fun_in_fundefs_name_in_fundefs. eassumption.
  Qed.

  Lemma merge_props_sig_vars : Dom_map σ :|: Range_map σ \subset name_in_fundefs B.
  Proof.
    intros x [x' [y Hget] | x' [y Hget]].
    - eapply mp_dom; eassumption.
    - eapply merge_props_names_K. eapply mp_range; eassumption.
  Qed.

  (** Where the code of each function of [B] can be found after merging. *)
  Lemma merge_props_find_def f t xs e :
    find_def f B = Some (t, xs, e) ->
    (M.get f σ = None /\ find_def f (list_to_fds K) = Some (t, xs, e)) \/
    (exists g xs' e',
        M.get f σ = Some g /\
        find_def g (list_to_fds K) = Some (t, xs', e') /\
        fundef_eqb (f, t, xs, e) (g, t, xs', e') = true).
  Proof.
    intros Hfind. apply find_def_correct in Hfind.
    assert (HunK := unique_bindings_fundefs_unique_functions _ merge_props_unique_K).
    destruct (mp_funs _ _ _ Hmp _ _ _ _ Hfind) as [HK | (g & t' & xs' & e' & HK & Hget & Heqb)].
    - left. split.
      + eapply mp_kept; [ eassumption |]. eapply fun_in_fundefs_name_in_fundefs. eassumption.
      + now apply find_def_complete.
    - right.
      assert (Ht : t = t').
      { unfold fundef_eqb in Heqb. apply andb_lazy_true in Heqb as [Heqb _].
        apply andb_lazy_true in Heqb as [Heqb _]. now apply Pos.eqb_eq. }
      subst t'. exists g, xs', e'. split; [ exact Hget |]. split; [| exact Heqb ].
      now apply find_def_complete.
  Qed.

  (** The functions that are not kept are renamed. *)
  Lemma merge_props_removed Brm :
    split_fds (list_to_fds K) Brm B -> name_in_fundefs Brm \subset Dom_map σ.
  Proof.
    intros Hsplit x Hx.
    destruct (name_in_fundefs_find_def_is_Some _ _ Hx) as (t & xs & e & Hfind).
    apply find_def_correct in Hfind.
    assert (HfB : fun_in_fundefs B (x, t, xs, e)).
    { eapply split_fds_fun_in_fundefs; [ eassumption |]. now right. }
    destruct (mp_funs _ _ _ Hmp _ _ _ _ HfB) as [HK | (g & t' & xs' & e' & HK & Hget & _)].
    - exfalso.
      edestruct split_fds_unique_bindings_fundefs_l as [_ [_ [Hdis]]];
        [ exact Hun | exact Hsplit |].
      apply (Hdis x). constructor.
      + apply name_in_fundefs_bound_var_fundefs.
        eapply fun_in_fundefs_name_in_fundefs. eassumption.
      + now apply name_in_fundefs_bound_var_fundefs.
    - eexists. eassumption.
  Qed.

End MergeProps.


(** * Semantic correctness *)

Section Correct.

  Context (cenv : ctor_env).
  Context {fuel : Type} {Hf : @fuel_resource fuel} {trace : Type} {Ht : @trace_resource trace}.
  Context (P1 : @logical_relations.PostT fuel trace) (PG : @logical_relations.PostGT fuel trace)
          (Hprops : Post_properties cenv P1 P1 PG).

  (** ** Renaming *)

  (** The relation holds between a term and its renaming, when the renaming
      does not touch the bound variables of the term. *)
  Lemma rename_exp_correct k σ e rho1 rho2 :
    Disjoint _ (Dom_map σ :|: Range_map σ) (bound_var e) ->
    preord_env_P_inj cenv PG (occurs_free e) k (apply_r σ) rho1 rho2 ->
    preord_exp cenv P1 PG k (e, rho1) (rename_exp σ e, rho2).
  Proof.
    intros Hdis Henv.
    rewrite rename_exp_ns.
    rewrite <- (proj1 (Disjoint_dom_rename_all_eq σ)).
    - eapply (rename_all_correct cenv (fun _ => P1) PG (fun _ _ => Hprops) k σ e rho1 rho2 0);
        [ lia | | exact Henv ].
      eapply Disjoint_Included_l; [| exact Hdis ].
      intros y [x [_ Hget]]. right. eexists. exact Hget.
    - eapply Disjoint_Included_l; [| exact Hdis ]. now sets.
  Qed.

  (** ** Alpha-equivalence *)

  Section Alpha.

    (* The renaming of the round of merging *)
    Context (σ : M.t var).

    Definition sig_vars : Ensemble var := Dom_map σ :|: Range_map σ.

    Lemma rn_not_sig_vars x : ~ x \in sig_vars -> rn σ x = x.
    Proof.
      intros Hx. unfold rn. destruct (M.get x σ) eqn:Hget; auto.
      exfalso. apply Hx. left. eexists. eassumption.
    Qed.

    Lemma rn_neq_not_sig_vars x y : ~ y \in sig_vars -> x <> y -> rn σ x <> y.
    Proof.
      intros Hy Hxy. unfold rn. destruct (M.get x σ) eqn:Hget; auto.
      intros ->. apply Hy. right. eexists. eassumption.
    Qed.

    Lemma Disjoint_sig_vars_binder (S : Ensemble var) x :
      Disjoint _ S sig_vars -> S x -> ~ x \in sig_vars.
    Proof. intros [Hd] Hx Hc. apply (Hd x). now constructor. Qed.

    Lemma var_eqb_set f1 f2 σb ρb x1 x2 x y :
      var_eqb f1 f2 (M.set x1 x2 σb) (M.set x2 x1 ρb) x y = true ->
      (x = x1 /\ y = x2) \/ (x <> x1 /\ y <> x2 /\ var_eqb f1 f2 σb ρb x y = true).
    Proof.
      unfold var_eqb. intros H.
      destruct (Pos.eq_dec x x1) as [-> | Hx].
      - rewrite M.gss in H. destruct (Pos.eq_dec y x2) as [-> | Hy]; [ now left |].
        rewrite M.gso in H by auto. destruct (M.get y ρb); [| discriminate ].
        apply andb_lazy_true in H as [H _]. apply Pos.eqb_eq in H. congruence.
      - rewrite M.gso in H by auto. destruct (Pos.eq_dec y x2) as [-> | Hy].
        + rewrite M.gss in H. destruct (M.get x σb); [| discriminate ].
          apply andb_lazy_true in H as [_ H]. apply Pos.eqb_eq in H. congruence.
        + rewrite M.gso in H by auto. right. auto.
    Qed.

    (* The environment invariant of the alpha-equivalence proof: related
       variables of the two terms hold related values. *)
    Definition alpha_env f1 f2 σb ρb (S : Ensemble var) k rho1 rho2 :=
      forall x y, var_eqb f1 f2 σb ρb x y = true -> S x ->
                  preord_var_env cenv PG k rho1 rho2 x (rn σ y).

    Lemma alpha_env_antimon f1 f2 σb ρb S S' k j rho1 rho2 :
      alpha_env f1 f2 σb ρb S k rho1 rho2 -> S' \subset S -> j <= k ->
      alpha_env f1 f2 σb ρb S' j rho1 rho2.
    Proof.
      intros Henv Hsub Hle x y Hxy Hx.
      eapply preord_var_env_monotonic; [| eassumption ].
      eapply Henv; [ eassumption | now apply Hsub ].
    Qed.

    Lemma alpha_env_set f1 f2 σb ρb (S S' : Ensemble var) k j rho1 rho2 x1 x2 v1 v2 :
      alpha_env f1 f2 σb ρb S k rho1 rho2 ->
      (forall x, S' x -> x <> x1 -> S x) ->
      ~ x2 \in sig_vars ->
      preord_val cenv PG j v1 v2 ->
      j <= k ->
      alpha_env f1 f2 (M.set x1 x2 σb) (M.set x2 x1 ρb) S' j
                (M.set x1 v1 rho1) (M.set x2 v2 rho2).
    Proof.
      intros Henv HS Hx2 Hval Hle x y Hxy Hx.
      apply var_eqb_set in Hxy as [[-> ->] | [Hx1 [Hy2 Hxy]]].
      - rewrite rn_not_sig_vars by assumption.
        intros v Hget. rewrite M.gss in Hget. inv Hget.
        eexists. rewrite M.gss. split; [ reflexivity | exact Hval ].
      - intros v Hget. rewrite M.gso in Hget by assumption.
        edestruct (Henv x y Hxy (HS x Hx Hx1)) as [v' [Hget' Hval']]; [ eassumption |].
        eexists. split.
        + rewrite M.gso; [ eassumption |]. now apply rn_neq_not_sig_vars.
        + eapply preord_val_monotonic; eassumption.
    Qed.

    Lemma alpha_env_vars f1 f2 σb ρb (S : Ensemble var) k rho1 rho2 xs ys :
      alpha_env f1 f2 σb ρb S k rho1 rho2 ->
      FromList xs \subset S ->
      vars_eqb f1 f2 σb ρb xs ys = true ->
      Forall2 (preord_var_env cenv PG k rho1 rho2) xs (map (rn σ) ys).
    Proof.
      intros Henv. revert ys.
      induction xs as [| x xs IH]; intros [| y ys] Hsub Heqb; simpl in Heqb;
        try discriminate; simpl; constructor.
      - apply andb_lazy_true in Heqb as [Hxy _].
        eapply Henv; [ eassumption |]. apply Hsub. now left.
      - apply andb_lazy_true in Heqb as [_ Heqb].
        eapply IH; [| eassumption ].
        intros z Hz. apply Hsub. now right.
    Qed.

    Lemma exp_alpha_eqb_Ecase_fst f1 f2 σb ρb x1 x2 bs1 bs2 :
      exp_alpha_eqb f1 f2 σb ρb (Ecase x1 bs1) (Ecase x2 bs2) = true ->
      Forall2 (fun p p' => fst p = fst p') bs1 bs2.
    Proof.
      revert bs2. induction bs1 as [| [c1 b1] bs1 IH]; intros [| [c2 b2] bs2] Heqb;
        simpl in Heqb; apply andb_lazy_true in Heqb as [Hx Heqb]; try discriminate.
      - constructor.
      - apply andb_lazy_true in Heqb as [Heqb Hgo].
        apply andb_lazy_true in Heqb as [Hc _].
        constructor; [ simpl; now apply Pos.eqb_eq |].
        apply IH. simpl. rewrite Hx. exact Hgo.
    Qed.

    (** The check [exp_alpha_eqb f1 f2] is sound: the first term is related
        to the renaming of the second one, when related variables hold related
        values. *)
    Lemma exp_alpha_eqb_correct f1 f2 e1 :
      forall e2 σb ρb k rho1 rho2,
        exp_alpha_eqb f1 f2 σb ρb e1 e2 = true ->
        Disjoint _ (bound_var e2) sig_vars ->
        alpha_env f1 f2 σb ρb (occurs_free e1) k rho1 rho2 ->
        preord_exp cenv P1 PG k (e1, rho1) (rename_exp σ e2, rho2).
    Proof.
      induction e1 using exp_ind'; intros e2 σb ρb k rho1 rho2 Heqb Hdis Henv;
        destruct e2; simpl in Heqb; try discriminate; assert (Hp := Hprops); inv Hp; simpl.
      - (* Econstr *)
        apply andb_lazy_true in Heqb as [Heqb Hk].
        apply andb_lazy_true in Heqb as [Htg Hys]. apply Pos.eqb_eq in Htg. subst.
        eapply preord_exp_constr_compat; [ now eauto | now eauto | | ].
        + eapply alpha_env_vars; [ eassumption | | eassumption ].
          normalize_occurs_free. now sets.
        + intros m vs1 vs2 Hlt Hvs. eapply IHe1; [ eassumption | |].
          * eapply Disjoint_Included_l; [| eassumption ]. normalize_bound_var. now sets.
          * eapply alpha_env_set; [ eassumption | | | | lia ].
            -- intros z Hz Hneq. eapply Free_Econstr2; [ congruence | exact Hz ].
            -- eapply Disjoint_sig_vars_binder; [ eassumption | now constructor ].
            -- rewrite preord_val_eq. split; [ reflexivity | exact Hvs ].
      - (* Ecase nil *)
        apply andb_lazy_true in Heqb as [Hx Hgo].
        destruct l; [| discriminate ].
        eapply preord_exp_case_nil_compat. now eauto.
      - (* Ecase cons *)
        apply andb_lazy_true in Heqb as [Hx Hgo].
        destruct l0 as [| [c' e'] l0]; [ discriminate |].
        apply andb_lazy_true in Hgo as [Hhd Hgo].
        apply andb_lazy_true in Hhd as [Hc He]. apply Pos.eqb_eq in Hc. subst c'.
        eapply preord_exp_case_cons_compat; [ now eauto | now eauto | now eauto | | | | ].
        + assert (Hfst : Forall2 (fun p p' => fst p = fst p') l l0).
          { eapply exp_alpha_eqb_Ecase_fst with (x1 := v) (x2 := v0).
            simpl. rewrite Hx. exact Hgo. }
          clear -Hfst. induction Hfst; simpl; constructor; auto.
        + eapply Henv; [ eassumption |]. now constructor.
        + intros m Hlt. eapply IHe1; [ eassumption | |].
          * eapply Disjoint_Included_l; [| eassumption ]. normalize_bound_var. now sets.
          * eapply alpha_env_antimon; [ eassumption | | lia ].
            normalize_occurs_free. now sets.
        + specialize (IHe0 (Ecase v0 l0) σb ρb k rho1 rho2).
          refine (IHe0 _ _ _).
          * simpl. rewrite Hx. exact Hgo.
          * eapply Disjoint_Included_l; [| eassumption ]. normalize_bound_var. now sets.
          * eapply alpha_env_antimon; [ eassumption | | lia ].
            normalize_occurs_free. now sets.
      - (* Eproj *)
        apply andb_lazy_true in Heqb as [Heqb Hk].
        apply andb_lazy_true in Heqb as [Heqb Hy].
        apply andb_lazy_true in Heqb as [Htg Hn].
        apply Pos.eqb_eq in Htg. apply N.eqb_eq in Hn. subst.
        eapply preord_exp_proj_compat; [ now eauto | now eauto | | ].
        + eapply Henv; [ eassumption |]. now constructor.
        + intros m w1 w2 Hlt Hval. eapply IHe1; [ eassumption | |].
          * eapply Disjoint_Included_l; [| eassumption ]. normalize_bound_var. now sets.
          * eapply alpha_env_set; [ eassumption | | | eassumption | lia ].
            -- intros z Hz Hneq. eapply Free_Eproj2; [ congruence | exact Hz ].
            -- eapply Disjoint_sig_vars_binder; [ eassumption | now constructor ].
      - (* Eletapp *)
        apply andb_lazy_true in Heqb as [Heqb Hk].
        apply andb_lazy_true in Heqb as [Heqb Hys].
        apply andb_lazy_true in Heqb as [Hf' Htg].
        apply Pos.eqb_eq in Htg. subst.
        eapply preord_exp_letapp_compat; [ now eauto | now eauto | now eauto | | | ].
        + eapply Henv; [ eassumption |]. eapply Free_Eletapp1. now left.
        + eapply alpha_env_vars; [ eassumption | | eassumption ].
          normalize_occurs_free. now sets.
        + intros m w1 w2 Hlt Hval. eapply IHe1; [ eassumption | |].
          * eapply Disjoint_Included_l; [| eassumption ]. normalize_bound_var. now sets.
          * eapply alpha_env_set; [ eassumption | | | eassumption | lia ].
            -- intros z Hz Hneq. eapply Free_Eletapp2; [ congruence | exact Hz ].
            -- eapply Disjoint_sig_vars_binder; [ eassumption | now constructor ].
      - (* Eapp *)
        apply andb_lazy_true in Heqb as [Heqb Hys].
        apply andb_lazy_true in Heqb as [Hf' Htg].
        apply Pos.eqb_eq in Htg. subst.
        eapply preord_exp_app_compat; [ now eauto | now eauto | | ].
        + eapply Henv; [ eassumption |]. now constructor.
        + eapply alpha_env_vars; [ eassumption | | eassumption ].
          normalize_occurs_free. now sets.
      - (* Eprim *)
        apply andb_lazy_true in Heqb as [Heqb Hk].
        apply andb_lazy_true in Heqb as [Hpr Hys].
        apply Pos.eqb_eq in Hpr. subst.
        eapply preord_exp_prim_compat; [ now eauto | ].
        eapply alpha_env_vars; [ eassumption | | eassumption ].
        normalize_occurs_free. now sets.
      - (* Ehalt *)
        eapply preord_exp_halt_compat; [ now eauto | now eauto | ].
        eapply Henv; [ eassumption |]. now constructor.
    Qed.

  End Alpha.

  (** ** Function values of the merged block *)

  Section Funs.

    Context (B : fundefs) (K : list fundef) (σ : M.t var)
            (Hun : unique_bindings_fundefs B)
            (Hmp : merge_props B K σ).

    Let B' := rename_fds σ (list_to_fds K).

    Lemma name_in_merged x : name_in_fundefs B' x -> name_in_fundefs B x.
    Proof.
      unfold B'. rewrite name_in_fundefs_rename_fds_iff. intros Hx.
      eapply merge_props_names_K; eassumption.
    Qed.

    Lemma not_sig_vars_of_not_name x : ~ name_in_fundefs B x -> ~ x \in sig_vars σ.
    Proof.
      intros Hx Hc. apply Hx. eapply merge_props_sig_vars; eassumption.
    Qed.

    (** The free variables of a function body *)
    Lemma fun_body_fv f t xs e x :
      fun_in_fundefs B (f, t, xs, e) -> occurs_free e x ->
      List.In x xs \/ name_in_fundefs B x \/
      (~ name_in_fundefs B x /\ occurs_free_fundefs B x).
    Proof.
      intros Hfun Hx.
      destruct (occurs_free_in_fun _ _ _ _ _ Hfun x Hx) as [z Hc | z Hc]; [ now left |].
      destruct (@Dec _ _ (Decidable_name_in_fundefs B) z) as [Hn | Hn]; [ now right; left |].
      destruct Hc as [z' Hc | z' Hc]; [ contradiction | now right; right ].
    Qed.

    (** In the body of a function, a function of the block is related to its
        renaming. *)
    Lemma fun_body_env_fun j rho1 rho2 xs1 xs2 vs1 vs2 rho1' rho2' x :
      (forall h, name_in_fundefs B h ->
                 preord_val cenv PG j (Vfun rho1 B h) (Vfun rho2 B' (rn σ h))) ->
      Disjoint _ (FromList xs2) (name_in_fundefs B) ->
      set_lists xs1 vs1 (def_funs B B rho1 rho1) = Some rho1' ->
      set_lists xs2 vs2 (def_funs B' B' rho2 rho2) = Some rho2' ->
      ~ List.In x xs1 -> name_in_fundefs B x ->
      preord_var_env cenv PG j rho1' rho2' x (rn σ x).
    Proof.
      intros Hfuns Hdis2 Hset1 Hset2 Hx1 Hx v1 Hget1.
      rewrite <- (set_lists_not_In _ _ _ _ _ Hset1 Hx1) in Hget1.
      rewrite def_funs_eq in Hget1 by assumption. inv Hget1.
      assert (Hrn : name_in_fundefs (list_to_fds K) (rn σ x))
        by (eapply merge_props_rn_names; eassumption).
      eexists. split.
      - rewrite <- (set_lists_not_In _ _ _ _ _ Hset2).
        + apply def_funs_eq. unfold B'. now apply name_in_fundefs_rename_fds_iff.
        + intros Hc. destruct Hdis2 as [Hdis2]. apply (Hdis2 (rn σ x)). constructor.
          * exact Hc.
          * eapply merge_props_names_K; eassumption.
      - now apply Hfuns.
    Qed.

    (** In the body of a function, a free variable of the block is related to
        itself. *)
    Lemma fun_body_env_free j rho1 rho2 xs1 xs2 vs1 vs2 rho1' rho2' x :
      (forall y, occurs_free_fundefs B y -> preord_var_env cenv PG j rho1 rho2 y y) ->
      set_lists xs1 vs1 (def_funs B B rho1 rho1) = Some rho1' ->
      set_lists xs2 vs2 (def_funs B' B' rho2 rho2) = Some rho2' ->
      ~ List.In x xs1 -> ~ List.In x xs2 ->
      ~ name_in_fundefs B x -> occurs_free_fundefs B x ->
      preord_var_env cenv PG j rho1' rho2' x (rn σ x).
    Proof.
      intros Hfv Hset1 Hset2 Hx1 Hx2 Hnin Hx v1 Hget1.
      rewrite <- (set_lists_not_In _ _ _ _ _ Hset1 Hx1) in Hget1.
      rewrite def_funs_neq in Hget1 by assumption.
      rewrite rn_not_sig_vars by (now apply not_sig_vars_of_not_name).
      edestruct (Hfv x Hx v1 Hget1) as [v2 [Hget2 Hval]].
      eexists. split; [| exact Hval ].
      rewrite <- (set_lists_not_In _ _ _ _ _ Hset2 Hx2).
      rewrite def_funs_neq; [ exact Hget2 |].
      intros Hc. apply Hnin. now apply name_in_merged.
    Qed.

    (** Every function of the block is related to its renaming in the merged
        block. *)
    Lemma merged_funs_correct k rho1 rho2 :
      (forall y, occurs_free_fundefs B y -> preord_var_env cenv PG k rho1 rho2 y y) ->
      forall h, name_in_fundefs B h ->
                preord_val cenv PG k (Vfun rho1 B h) (Vfun rho2 B' (rn σ h)).
    Proof.
      assert (Hincl : inclusion _ P1 PG) by (destruct Hprops; assumption).
      induction k as [k IH] using lt_wf_rec1. intros Hfv h Hh.
      destruct (name_in_fundefs_find_def_is_Some _ _ Hh) as (t & xs & e & Hfind).
      assert (Hfun := find_def_correct _ _ _ _ _ Hfind).
      edestruct (unique_bindings_fun_in_fundefs _ _ _ _ _ Hfun Hun)
        as (Hun_e & Hh_e & Hh_xs & Hdis_e & Hdis_xs & Hdis_exs & Hnd_xs).
      assert (IHj : forall j, j < k ->
                forall h', name_in_fundefs B h' ->
                           preord_val cenv PG j (Vfun rho1 B h') (Vfun rho2 B' (rn σ h'))).
      { intros j Hj h' Hh'. eapply IH; [ exact Hj | | exact Hh' ].
        intros y Hy. eapply preord_var_env_monotonic; [ now apply Hfv | lia ]. }
      assert (Hfvj : forall j, j <= k ->
                forall y, occurs_free_fundefs B y -> preord_var_env cenv PG j rho1 rho2 y y).
      { intros j Hj y Hy. eapply preord_var_env_monotonic; [ now apply Hfv | lia ]. }
      destruct (merge_props_find_def _ _ _ Hun Hmp _ _ _ _ Hfind)
        as [[Hnone HfindK] | (g & xs' & e' & Hget & HfindK & Heqb)].
      - (* [h] is kept: its body is renamed *)
        assert (Hrn : rn σ h = h) by (unfold rn; now rewrite Hnone).
        rewrite Hrn.
        eapply preord_val_fun; [ exact Hfind | eapply find_def_rename_fds; exact HfindK |].
        intros rho1' j vs1 vs2 Hlen Hset1.
        edestruct (set_lists_length (def_funs B B rho1 rho1) (def_funs B' B' rho2 rho2)
                                    rho1' xs vs1 vs2) as [rho2' Hset2];
          [ exact Hlen | now symmetry |].
        exists rho2'. split; [ now symmetry |].
        intros Hj Hvs.
        eapply preord_exp_post_monotonic; [ exact Hincl |].
        eapply rename_exp_correct.
        + eapply Disjoint_Included_l; [ eapply merge_props_sig_vars; eassumption |].
          now apply Disjoint_sym.
        + intros x Hx. rewrite <- rn_apply_r.
          destruct (in_dec Pos.eq_dec x xs) as [Hin | Hnin].
          * (* a parameter *)
            rewrite rn_not_sig_vars.
            -- intros v1 Hget1.
               edestruct (set_lists_Forall2_get (preord_val cenv PG j) xs vs1 vs2 _ _
                                                rho1' rho2' x Hvs (eq_sym Hset1) Hset2 Hin)
                 as (v1' & v2' & Hg1 & Hg2 & Hv).
               rewrite Hget1 in Hg1. inv Hg1. eauto.
            -- intros Hc. destruct Hdis_xs as [Hdis_xs]. apply (Hdis_xs x). constructor.
               ++ exact Hin.
               ++ eapply merge_props_sig_vars; eassumption.
          * destruct (fun_body_fv _ _ _ _ _ Hfun Hx) as [Hc | [Hc | [Hn Hc]]];
              [ contradiction | |].
            -- eapply fun_body_env_fun with (xs1 := xs) (xs2 := xs); try eassumption.
               ++ intros h' Hh'. eapply IHj; [ exact Hj | exact Hh' ].
               ++ now symmetry.
            -- eapply fun_body_env_free with (xs1 := xs) (xs2 := xs); try eassumption.
               ++ eapply Hfvj. lia.
               ++ now symmetry.
      - (* [h] is merged with [g]: its body is alpha-equivalent to the body of [g] *)
        assert (Hrn : rn σ h = g) by (unfold rn; now rewrite Hget).
        rewrite Hrn.
        unfold fundef_eqb in Heqb.
        apply andb_lazy_true in Heqb as [Heqb Halpha].
        apply andb_lazy_true in Heqb as [_ Hlen_eq]. apply Nat.eqb_eq in Hlen_eq.
        assert (HfunK : fun_in_fundefs B (g, t, xs', e')).
        { eapply merge_props_fun_in_K; [ eassumption |]. eapply find_def_correct. eassumption. }
        assert (Hg_kept : name_in_fundefs (list_to_fds K) g).
        { eapply fun_in_fundefs_name_in_fundefs. eapply find_def_correct. eassumption. }
        assert (Hrng : rn σ g = g) by (unfold rn; now rewrite (mp_kept _ _ _ Hmp _ Hg_kept)).
        edestruct (unique_bindings_fun_in_fundefs _ _ _ _ _ HfunK Hun)
          as (Hun_e' & Hg_e' & Hg_xs' & Hdis_e' & Hdis_xs' & Hdis_exs' & Hnd_xs').
        eapply preord_val_fun; [ exact Hfind | eapply find_def_rename_fds; exact HfindK |].
        intros rho1' j vs1 vs2 Hlen Hset1.
        assert (Hlen1 : length xs = length vs1)
          by exact (set_lists_length_eq _ _ _ _ (eq_sym Hset1)).
        assert (Hlen2 : length xs' = length vs2) by lia.
        destruct (set_lists_length3 (def_funs B' B' rho2 rho2) xs' vs2 Hlen2) as [rho2' Hset2].
        exists rho2'. split; [ now symmetry |].
        intros Hj Hvs.
        eapply preord_exp_post_monotonic; [ exact Hincl |].
        eapply exp_alpha_eqb_correct; [ exact Halpha | |].
        + eapply Disjoint_Included_r; [ eapply merge_props_sig_vars; eassumption |].
          exact Hdis_e'.
        + intros x y Hxy Hx.
          unfold var_eqb in Hxy.
          destruct (M.get x (bind_vars (M.empty _) xs xs')) as [y' |] eqn:Hgx;
            destruct (M.get y (bind_vars (M.empty _) xs' xs)) as [x' |] eqn:Hgy;
            try discriminate.
          * (* both are parameters, at the same position *)
            apply andb_lazy_true in Hxy as [Hy _]. apply Pos.eqb_eq in Hy. subst y'.
            destruct (bind_vars_get _ _ _ _ _ Hgx) as [[i [Hxi Hyi]] | Habs];
              [| rewrite M.gempty in Habs; discriminate ].
            assert (Hy_xs' : List.In y xs') by (eapply nth_error_In; eassumption).
            rewrite rn_not_sig_vars.
            2:{ intros Hc. destruct Hdis_xs' as [Hdis_xs']. apply (Hdis_xs' y). constructor.
                - exact Hy_xs'.
                - eapply merge_props_sig_vars; eassumption. }
            intros v1 Hget1.
            assert (Hi : (i < length vs1)%nat).
            { rewrite <- Hlen1. apply nth_error_Some. congruence. }
            destruct (nth_error vs1 i) as [w1 |] eqn:Hw1;
              [| apply nth_error_Some in Hi; contradiction ].
            rewrite (set_lists_nth_error _ _ _ _ _ _ _ Hnd_xs (eq_sym Hset1) Hxi Hw1) in Hget1.
            inv Hget1.
            destruct (Forall2_nth_error_r _ _ _ _ _ Hvs Hw1) as [w2 [Hw2 Hval]].
            exists w2. split; [| exact Hval ].
            eapply set_lists_nth_error; eassumption.
          * (* neither is a parameter *)
            apply Pos.eqb_eq in Hxy.
            assert (Hx_xs : ~ List.In x xs).
            { intros Hc. destruct (bind_vars_In (M.empty _) xs xs' x Hc Hlen_eq) as [z Hz].
              congruence. }
            assert (Hy_xs' : ~ List.In y xs').
            { intros Hc. destruct (bind_vars_In (M.empty _) xs' xs y Hc (eq_sym Hlen_eq))
                as [z Hz].
              congruence. }
            destruct (Pos.eqb x h) eqn:Hxh.
            -- apply Pos.eqb_eq in Hxh. subst x y. rewrite Hrng, <- Hrn.
               eapply fun_body_env_fun with (xs1 := xs) (xs2 := xs'); try eassumption.
               ++ intros h' Hh'. eapply IHj; [ exact Hj | exact Hh' ].
               ++ now symmetry.
            -- subst y.
               destruct (fun_body_fv _ _ _ _ _ Hfun Hx) as [Hc | [Hc | [Hn Hc]]];
                 [ contradiction | |].
               ++ eapply fun_body_env_fun with (xs1 := xs) (xs2 := xs'); try eassumption.
                  ** intros h' Hh'. eapply IHj; [ exact Hj | exact Hh' ].
                  ** now symmetry.
               ++ eapply fun_body_env_free with (xs1 := xs) (xs2 := xs'); try eassumption.
                  ** eapply Hfvj. lia.
                  ** now symmetry.
    Qed.

  End Funs.

  (** ** One round of merging *)

  Theorem merge_round_correct B K σ e k rho1 rho2 :
    unique_bindings (Efun B e) ->
    merge_props B K σ ->
    preord_env_P cenv PG (occurs_free (Efun B e)) k rho1 rho2 ->
    preord_exp cenv P1 PG k (Efun B e, rho1)
               (Efun (rename_fds σ (list_to_fds K)) (rename_exp σ e), rho2).
  Proof.
    intros Hun Hmp Henv. inv Hun.
    assert (Hp := Hprops). inv Hp.
    eapply preord_exp_fun_compat; [ now eauto | now eauto |].
    eapply rename_exp_correct.
    - eapply Disjoint_Included_l; [ eapply merge_props_sig_vars; eassumption |].
      eapply Disjoint_Included_l; [ apply name_in_fundefs_bound_var_fundefs |].
      now apply Disjoint_sym.
    - intros x Hx. rewrite <- rn_apply_r.
      destruct (@Dec _ _ (Decidable_name_in_fundefs B) x) as [Hin | Hnin].
      + intros v1 Hget1. rewrite def_funs_eq in Hget1 by assumption. inv Hget1.
        eexists. split.
        * apply def_funs_eq. apply name_in_fundefs_rename_fds_iff.
          eapply merge_props_rn_names; eassumption.
        * eapply merged_funs_correct; [ eassumption | eassumption | | exact Hin ].
          intros y Hy.
          eapply preord_var_env_monotonic; [ apply Henv; now apply Free_Efun2 | lia ].
      + rewrite rn_not_sig_vars.
        2:{ intros Hc. apply Hnin. eapply merge_props_sig_vars; eassumption. }
        intros v1 Hget1. rewrite def_funs_neq in Hget1 by assumption.
        edestruct (Henv x) as [v2 [Hget2 Hval]]; [ now apply Free_Efun1 | eassumption |].
        eexists. split.
        * rewrite def_funs_neq; [ exact Hget2 |].
          rewrite name_in_fundefs_rename_fds_iff. intros Hc. apply Hnin.
          eapply merge_props_names_K; eassumption.
        * eapply preord_val_monotonic; [ eassumption | lia ].
  Qed.

End Correct.


(** * Syntactic properties of one round *)

Lemma merge_round_syntax B K σ e :
  unique_bindings (Efun B e) ->
  merge_props B K σ ->
  unique_bindings (Efun (rename_fds σ (list_to_fds K)) (rename_exp σ e)) /\
  bound_var (Efun (rename_fds σ (list_to_fds K)) (rename_exp σ e)) \subset
    bound_var (Efun B e) /\
  occurs_free (Efun (rename_fds σ (list_to_fds K)) (rename_exp σ e)) \subset
    occurs_free (Efun B e).
Proof.
  intros Hun Hmp. inv Hun. rename H1 into Hun_e. rename H2 into Hun_B. rename H3 into Hdis.
  destruct (mp_split _ _ _ Hmp) as [Brm Hsplit].
  assert (Hbv_K : bound_var_fundefs (list_to_fds K) \subset bound_var_fundefs B).
  { rewrite (split_fds_bound_vars _ _ _ Hsplit). now sets. }
  assert (Hnames : forall x, ~ name_in_fundefs (rename_fds σ (list_to_fds K)) x ->
                             ~ x \in Range_map σ).
  { intros x Hnin [y Hget]. apply Hnin. apply name_in_fundefs_rename_fds_iff.
    eapply mp_range; eassumption. }
  split; [| split ].
  - constructor.
    + rewrite rename_exp_ns. now apply unique_bindings_rename_all_ns.
    + rewrite rename_fds_ns. apply unique_bindings_rename_all_ns.
      eapply merge_props_unique_K; eassumption.
    + rewrite bound_var_rename_exp, bound_var_rename_fds.
      eapply Disjoint_Included_r; [ exact Hbv_K | exact Hdis ].
  - rewrite !bound_var_Efun, bound_var_rename_exp, bound_var_rename_fds. now sets.
  - rewrite !occurs_free_Efun. intros x Hx. destruct Hx as [x Hx | x [Hx Hnin]].
    + (* a free variable of the merged block *)
      assert (Hnin : ~ name_in_fundefs (rename_fds σ (list_to_fds K)) x).
      { intros Hc.
        destruct (occurs_free_fundefs_name_in_fundefs_Disjoint
                    (rename_fds σ (list_to_fds K))) as [Hd].
        apply (Hd x). now constructor. }
      rewrite rename_fds_ns in Hx.
      destruct (proj2 of_rename_all_ns_mut (list_to_fds K) σ x Hx) as [x [Hx' Hdom] | x Hran].
      * left. rewrite (split_fds_occurs_free_fundefs _ _ _ Hsplit). left.
        constructor; [ exact Hx' |].
        intros Hc. apply Hdom. eapply merge_props_removed; eassumption.
      * exfalso. eapply Hnames; eassumption.
    + (* a free variable of the renamed body *)
      rewrite rename_exp_ns in Hx.
      destruct (proj1 of_rename_all_ns_mut e σ x Hx) as [x [Hx' Hdom] | x Hran].
      * right. constructor; [ exact Hx' |].
        intros Hc. apply Hnin. apply name_in_fundefs_rename_fds_iff.
        assert (Hrn : name_in_fundefs (list_to_fds K) (rn σ x))
          by (eapply merge_props_rn_names; eassumption).
        unfold rn in Hrn. destruct (M.get x σ) eqn:Hget; [| exact Hrn ].
        exfalso. apply Hdom. eexists. eassumption.
      * exfalso. eapply Hnames; eassumption.
Qed.


(** * Unfolding one round of [merge_dup_funs] *)

Definition funs_of (B : fundefs) : M.t unit :=
  fold_left (fun m d => M.set (fundef_name d) tt m) (fds_to_list B) (M.empty _).

Lemma merge_dup_funs_S fuel B e :
  merge_dup_funs (S fuel) (Efun B e) =
  let '(kept, σ) :=
    merge_list (funs_of B) (fds_to_list B) [] (M.empty _) (M.empty _) (M.empty _) in
  if Nat.eqb (length kept) (length (fds_to_list B)) then Efun B e
  else merge_dup_funs fuel (Efun (rename_fds σ (list_to_fds kept)) (rename_exp σ e)).
Proof. reflexivity. Qed.


(** * Any number of rounds *)

Section Iter.

  Context (cenv : ctor_env).
  Context {fuel : Type} {Hf : @fuel_resource fuel} {trace : Type} {Ht : @trace_resource trace}.
  Context (P : @logical_relations.PostT fuel trace) (PG : @logical_relations.PostGT fuel trace)
          (Hpp : post_prop cenv P PG).

  Lemma merge_dup_funs_iter rounds e :
    well_scoped e ->
    well_scoped (merge_dup_funs rounds e) /\
    bound_var (merge_dup_funs rounds e) \subset bound_var e /\
    occurs_free (merge_dup_funs rounds e) \subset occurs_free e /\
    exists n, preord_exp_n cenv preserves_fv (post_prop cenv) n e (merge_dup_funs rounds e).
  Proof.
    assert (Hrefl : forall e',
               exists n, preord_exp_n cenv preserves_fv (post_prop cenv) n e' e').
    { intros e'. exists 1%nat. eapply preord_exp_n_refl; [| exact Hpp ].
      intro. unfold preserves_fv. sets. }
    revert e. induction rounds as [| rounds IH]; intros e Hws.
    - (* no round left *)
      split; [ exact Hws |]. split; [ now sets |]. split; [ now sets |]. apply Hrefl.
    - destruct e as [ | | | | B e0 | | | | ];
        try (split; [ exact Hws |]; split; [ now sets |]; split; [ now sets |];
             apply Hrefl).
      rewrite merge_dup_funs_S.
      match goal with
      | |- context [ merge_list ?a ?b ?c ?d ?e ?f ] =>
          destruct (merge_list a b c d e f) as [kept σ] eqn:Hm
      end.
      destruct (Nat.eqb _ _).
      + (* nothing was merged *)
        split; [ exact Hws |]. split; [ now sets |]. split; [ now sets |]. apply Hrefl.
      + destruct Hws as [Hun Hdis].
        assert (Hmp : merge_props B kept σ).
        { eapply merge_list_props; [| exact Hm ]. now inv Hun. }
        destruct (merge_round_syntax _ _ _ e0 Hun Hmp) as [Hun1 [Hbv1 Hfv1]].
        set (e1 := Efun (rename_fds σ (list_to_fds kept)) (rename_exp σ e0)) in *.
        assert (Hws1 : well_scoped e1).
        { split; [ exact Hun1 |].
          eapply Disjoint_Included; [ exact Hfv1 | exact Hbv1 | exact Hdis ]. }
        destruct (IH e1 Hws1) as [Hws2 [Hbv2 [Hfv2 [n Hn]]]].
        split; [ exact Hws2 |].
        split; [ eapply Included_trans; eassumption |].
        split; [ eapply Included_trans; eassumption |].
        exists (1 + n)%nat. econstructor 2; [| exact Hn ].
        econstructor 1; [| exact Hfv1 | exact Hpp ].
        intros k rho1 rho2 Henv _.
        eapply merge_round_correct;
          [ exact (proj1 Hpp) | exact Hun | exact Hmp | exact Henv ].
  Qed.

End Iter.
