From Stdlib Require Import Strings.String Classes.Morphisms Relations.Relations.
From Stdlib Require Import PArith.BinPos Sets.Ensembles Lia.
Require Import LambdaANF.identifiers LambdaANF.Prototype LambdaANF.cps_proto_univ LambdaANF.cps_proto LambdaANF.term LambdaANF.term_util.
Require Import LambdaANF.Ensembles_util LambdaANF.rename LambdaANF.shrink_cps LambdaANF.map_util.

From Stdlib Require Import Lists.List.
Import ListNotations.

Definition fresher_than (x : var) (S : Ensemble var) : Prop :=
  forall y, y \in S -> (x > y)%positive.

Lemma fresher_than_not_In x S : fresher_than x S -> ~ x \in S.
Proof. intros Hfresh Hin; assert (x > x)%positive by now apply Hfresh. lia. Qed.

Lemma fresher_than_antimon x S1 S2 : S1 \subset S2 -> fresher_than x S2 -> fresher_than x S1.
Proof. intros HS12 Hfresh y Hy; apply Hfresh, HS12, Hy. Qed.

Lemma fresher_than_monotonic x y S : (y >= x -> fresher_than x S -> fresher_than y S)%positive.
Proof. intros Hxy Hfresh z Hz. assert (x > z)%positive by now apply Hfresh. lia. Qed.

Lemma fresher_than_Union x S1 S2 : fresher_than x S1 -> fresher_than x S2 -> fresher_than x (S1 :|: S2).
Proof. intros HS1 HS2 y Hy; destruct Hy as [y Hy|y Hy]; auto. Qed.

#[global] Instance Proper_fresher_than_r : Proper (Logic.eq ==> Same_set _ ==> iff) fresher_than.
Proof.
  unfold Proper, "==>", fresher_than.
  intros x y Hxy x0 y0 Hxy0; subst; split; intros Hforall dummy; now (rewrite <- Hxy0 || rewrite Hxy0).
Qed.

Definition fresh_copies (S : Ensemble var) (l : list var) : Prop := Disjoint _ S (FromList l) /\ NoDup l.

Definition gensym (x : var) : var * var := (x + 1, x)%positive.

Lemma gensym_spec x S x' y :
  fresher_than x S ->
  (x', y) = gensym x ->
  ~ y \in S /\ fresher_than x' (y |: S).
Proof.
  unfold gensym; intros Hfresh Hgen; split.
  - intros Hy.
    assert (y = x) by now simpl in *.
    assert (x > y)%positive by now apply Hfresh.
    lia.
  - assert (x' = (x + 1)%positive) by easy; assert (y = x) by easy.
    assert (x' > y)%positive by lia.
    apply fresher_than_Union; [|eapply fresher_than_monotonic; try eassumption; lia].
    simpl; intros z Hz; inversion Hz; lia.
Qed.

Fixpoint gensyms {A} (x : var) (xs : list A) : var * list var :=
  match xs with
  | [] => (x, [])
  | _ :: xs => let '(x', xs') := gensyms (x + 1)%positive xs in (x', x :: xs')
  end.

Lemma gensyms_len' {A} : forall x (xs : list A) x' xs', (x', xs') = gensyms x xs -> length xs' = length xs.
Proof.
  intros x xs; revert x; induction xs as [|x xs IHxs]; intros x0 x' xs' Hgen; [simpl in Hgen; now inv Hgen|].
  unfold gensyms in Hgen; fold @gensyms in Hgen.
  destruct (gensyms (x0 + 1)%positive xs) as [x'' xs''] eqn:Hx0. inv Hgen;  simpl. f_equal.
  eapply IHxs. now symmetry.
Qed.

Lemma gensyms_increasing' {A} :
  forall x (xs : list A) x' xs', (x', xs') = gensyms x xs ->
  forall y, List.In y xs' -> (y >= x)%positive.
Proof.
  intros x xs; revert x; induction xs as [|x xs IHxs]; intros x0 x' xs' Hgen y Hy;
    [simpl in Hgen; now inv Hgen|].
  unfold gensyms in Hgen; fold @gensyms in Hgen.
  destruct (gensyms (x0 + 1)%positive xs) as [x'' xs''] eqn:Hx0; inv Hgen; simpl.
  simpl in Hy; destruct Hy as [H|H]; [inversion H; simpl; lia|].
  specialize IHxs with (x := (x0 + 1)%positive) (y := y).
  rewrite Hx0 in IHxs; unfold snd in IHxs.
  specialize (IHxs x'' xs'' eq_refl H); lia.
Qed.

Local Ltac mk_corollary parent :=
  intros x xs x' xs';
  pose (Hparent := parent _ x xs); clearbody Hparent; intros H;
  destruct (gensyms x xs); now inversion H.

Lemma gensyms_upper {A} x (xs : list A) :
  (fst (gensyms x xs) >= x)%positive /\
  forall y, List.In y (snd (gensyms x xs)) -> (fst (gensyms x xs) > y)%positive.
Proof.
  revert x; induction xs; [simpl; split; [lia|easy]|intros x; split; [|intros y Hy]].
  - unfold gensyms; fold @gensyms.
    destruct (gensyms _ _) as [x' xs'] eqn:Hxs'; unfold fst.
    specialize (IHxs (x + 1)%positive); rewrite Hxs' in IHxs; unfold fst in IHxs.
    destruct IHxs; lia.
  - unfold gensyms in *; fold @gensyms in *.
    destruct (gensyms _ _) as [x' xs'] eqn:Hxs'; unfold fst; unfold snd in Hy.
    specialize (IHxs (x + 1)%positive); rewrite Hxs' in IHxs; unfold fst in IHxs.
    destruct IHxs as [IHxs IHxsy].
    destruct Hy as [Hy|Hy]; [inversion Hy; simpl; lia|].
    now specialize (IHxsy y Hy).
Qed.

Corollary gensyms_upper1 {A} : forall x (xs : list A) x' xs', (x', xs') = gensyms x xs -> (x' >= x)%positive.
Proof. mk_corollary @gensyms_upper. Qed.

Corollary gensyms_upper2 {A} :
  forall x (xs : list A) x' xs', (x', xs') = gensyms x xs ->
  forall y, List.In y xs' -> (x' > y)%positive.
Proof. mk_corollary @gensyms_upper. Qed.

Lemma gensyms_NoDup {A} x (xs : list A) : NoDup (snd (gensyms x xs)).
Proof.
  revert x; induction xs; intros; [now constructor|].
  unfold gensyms; fold @gensyms.
  destruct (gensyms _ _) as [x' xs'] eqn:Hxs'; unfold snd.
  specialize (IHxs (x + 1)%positive); rewrite Hxs' in IHxs; unfold snd in IHxs.
  constructor; [|auto].
  pose (Hinc := gensyms_increasing' (x + 1)%positive xs); clearbody Hinc.
  rewrite Hxs' in Hinc; unfold snd in Hinc.
  remember (snd (gensyms (x + 1)%positive xs)) as ys; clear - Hinc.
  induction xs'; auto.
  specialize (Hinc x' (a :: xs')).
  intros [|Hin_ys]; [|apply IHxs'; auto; intros; apply Hinc; auto; now right].
  assert (Hxa : In x (a :: xs')) by now left.
  specialize (Hinc eq_refl x Hxa); lia.
Qed.

Corollary gensyms_NoDup' {A} : forall x (xs : list A) x' xs', (x', xs') = gensyms x xs -> NoDup xs'.
Proof. mk_corollary @gensyms_NoDup. Qed.

Lemma gensyms_fresher_than {A} (xs : list A) :
  forall x y S x' xs',
  fresher_than x S ->
  (y >= x)%positive ->
  (x', xs') = gensyms y xs ->
  Disjoint _ S (FromList xs').
Proof.
  induction xs.
  - simpl; intros x y S x' xs' Hfresh Hyx Hgen; inversion Hgen; subst.
    simpl; normalize_sets; eauto with Ensembles_DB.
  - unfold gensyms; fold @gensyms; intros x y S x' xs' Hfresh Hyx Hgen.
    destruct (gensyms (y + 1)%positive xs) as [x'' xs''] eqn:Hxs.
    inversion Hgen; subst; simpl; normalize_sets.
    apply Union_Disjoint_r; [|eapply (IHxs (y + 1)%positive); eauto; try lia].
    + unfold fresher_than in Hfresh.
      constructor; intros arb; intros HSx; unfold Ensembles.In in HSx.
      destruct HSx as [arb HS Hx]; inversion Hx; subst.
      specialize (Hfresh _ HS); lia.
    + eapply fresher_than_monotonic; eauto; lia.
Qed.

Ltac show_Disjoint arb Harbx Harby :=
  let Harb := fresh "Harb" in
  constructor; intros arb Harb; unfold Ensembles.In in Harb;
  destruct Harb as [arb Harbx Harby].

Lemma gensyms_disjoint {A B} (xs : list A) (ys : list B) x0 x1 x2 xs' ys' :
  (x1, xs') = gensyms x0 xs ->
  (x2, ys') = gensyms x1 ys ->
  Disjoint _ (FromList xs') (FromList ys').
Proof.
  intros Hxs' Hys'; show_Disjoint arb Harbx Harby.
  unfold Ensembles.In, FromList in Harbx, Harby.
  assert (x1 > arb)%positive by (eapply gensyms_upper2; eassumption); simpl in *.
  assert (arb >= x1)%positive by (eapply gensyms_increasing'; eassumption); simpl in *.
  lia.
Qed.

Lemma gensyms_list_fresher {A} x y (ys : list A) y' ys' S :
  fresher_than x S ->
  (y >= x)%positive ->
  (y', ys') = gensyms y ys ->
  Disjoint _ S (FromList ys').
Proof.
  intros Hfresh Hyx Hgen; show_Disjoint arb Harbx Harby.
  unfold Ensembles.In, FromList in Harby.
  assert (arb >= y)%positive by (eapply gensyms_increasing'; eauto); simpl in *.
  assert (x > arb)%positive by now apply Hfresh.
  lia.
Qed.

Lemma gensyms_spec {A} x S (xs : list A) x' xs' :
  fresher_than x S ->
  (x', xs') = gensyms x xs ->
  fresh_copies S xs' /\ fresher_than x' (S :|: FromList xs') /\ length xs' = length xs.
Proof.
  intros Hfresh Hgen; unfold fresh_copies; split; [split|split].
  - show_Disjoint arb Harbx Harby.
    unfold Ensembles.In, FromList in Harby.
    assert (x > arb)%positive by now apply Hfresh.
    assert (arb >= x)%positive by (eapply gensyms_increasing'; eauto).
    simpl in *; lia.
  - eapply gensyms_NoDup'; eauto.
  - intros y Hy; destruct Hy as [y Hy|y Hy].
    + assert (x > y)%positive by now apply Hfresh.
      assert (x' >= x)%positive by (eapply gensyms_upper1; eauto); lia.
    + unfold Ensembles.In, FromList in Hy.
      simpl in Hy; normalize_roundtrips.
      eapply gensyms_upper2; eauto.
  - eapply gensyms_len'; eauto.
Qed.

Section RunRewriter.

Context
  {Root : exp_univ} {fueled : bool} {metric : Metric Root fueled} {Rstep : relation (univD Root)}
  {D : Set} {I_D : forall A, univD A -> D -> Prop} `{@Delayed _ Frame_exp D I_D}
  {R : Set} {I_R : forall A, frames_t A Root -> R -> Prop}
  {S : Set} {I_S : forall A, frames_t A Root -> univD A -> S -> Prop}
  `{@Preserves_R _ Frame_exp _ R I_R}
  `{@Preserves_S_dn _ Frame_exp _ S I_S}
  `{@Preserves_S_up _ Frame_exp _ S I_S}
  (rw : rewriter Root fueled metric Rstep D I_D R I_R S I_S).

Definition run_rewriter' :
  forall (e : univD Root), Param I_R (erase <[]>) -> State I_S (erase <[]>) e ->
  result Rstep I_S (erase <[]>) e.
Proof.
  intros e r s; unfold rewriter, rewriter', rw_for in rw.
  destruct fueled.
  - specialize (rw lots_of_fuel _ (erase <[]>) _ e (delay_id _)).
    rewrite delay_id_law in rw.
    specialize (rw (erase (Pos.to_nat lots_of_fuel)) _ r s); apply rw; unerase.
    unfold run_metric; destruct metric; reflexivity.
  - specialize (rw I _ (erase <[]>) _ e (delay_id _)).
    rewrite delay_id_law in rw; unshelve eapply rw;
    try lazymatch goal with
    | |- erased nat => refine (erase _)
    | |- Param _ _ => assumption
    | |- State _ _ _ => assumption
    end;
    try lazymatch goal with
    | |- e_ok (erase _) => apply erase_ok
    | |- «_» => unerase; reflexivity
    end.
Defined.

Definition run_rewriter (e : univD Root)
           (r : Param I_R (erase <[]>)) (s : State I_S (erase <[]>) e) : univD Root :=
  let '{| resTree := e' |} := run_rewriter' e r s in e'.

End RunRewriter.

Definition I_S_fresh {A} (C : exp_c A exp_univ_exp) (e : univD A) (x : var) : Prop :=
  fresher_than x (used_vars (C ⟦ e ⟧)).

(* We don't have to do anything to preserve a fresh variable as we move around *)
#[global] Instance Preserves_S_dn_S_fresh : Preserves_S_dn (@I_S_fresh).
Proof. unfold Preserves_S_dn; intros A B C C_ok f x s; exact s. Defined.
#[global] Instance Preserves_S_up_S_fresh : Preserves_S_up (@I_S_fresh).
Proof. unfold Preserves_S_up; intros A B C C_ok f x s; exact s. Defined.
Extraction Inline Preserves_S_dn_S_fresh Preserves_S_up_S_fresh.

(* Compute an initial fresh variable *)
Definition initial_fresh (e : exp) : State (@I_S_fresh) (erase <[]>) e.
Proof.
  exists (1 + max_var e 1)%positive; unerase; unfold I_S_fresh.
  change (![ <[]> ⟦ ?e ⟧ ]) with e; unfold fresher_than.
  intros y Hy; enough (y <= max_var e 1)%positive by lia.
  destruct Hy; [now apply bound_var_leq_max_var|now apply occurs_free_leq_max_var].
Defined.

(* Some passes assume unique bindings *)
Definition I_S_uniq {A} (C : exp_c A exp_univ_exp) (e : univD A) (_ : unit) : Prop :=
  unique_bindings (C ⟦ e ⟧).
#[global] Instance Preserves_S_dn_S_uniq : Preserves_S_dn (@I_S_uniq).
Proof. unfold Preserves_S_dn; intros A B C C_ok f x s; exact s. Defined.
#[global] Instance Preserves_S_up_S_uniq : Preserves_S_up (@I_S_uniq).
Proof. unfold Preserves_S_up; intros A B C C_ok f x s; exact s. Defined.
Extraction Inline Preserves_S_dn_S_uniq Preserves_S_up_S_uniq.

(* Additional facts about variables *)

Fixpoint bound_var_ces (ces : list (term.ctor_tag * term.exp)) :=
  match ces with
  | [] => Empty_set _
  | (c, e) :: ces => bound_var e :|: bound_var_ces ces
  end.

Lemma bound_var_Ecase x ces : bound_var (term.Ecase x ces) <--> bound_var_ces ces.
Proof.
  induction ces as [|[c e] ces IHces].
  - rewrite bound_var_Ecase_nil; now cbn.
  - rewrite bound_var_Ecase_cons; cbn; rewrite IHces; eauto with Ensembles_DB.
Qed.

Fixpoint used_vars_ces (ces : list (term.ctor_tag * term.exp)) :=
  match ces with
  | [] => Empty_set _
  | (c, e) :: ces => used_vars e :|: used_vars_ces ces
  end.

Lemma used_vars_Ecase x ces : used_vars (term.Ecase x ces) <--> x |: used_vars_ces ces.
Proof.
  induction ces as [|[c e] ces IHces].
  - rewrite used_vars_Ecase_nil; cbn; now normalize_sets.
  - rewrite used_vars_Ecase_cons; cbn; rewrite IHces; eauto with Ensembles_DB.
Qed.

(* Renaming *)

(* TODO: combine with shrink_cps renaming *)

Definition r_map : Set := M.tree var.

(* Require Import LambdaANF.shrink_cps_correct. *)

Definition image'' σ : Ensemble var := fun y => exists x, M.get x σ = Some y.

Lemma apply_r_vars σ x : [set apply_r σ x] \subset x |: image'' σ.
Proof.
  unfold apply_r.
  destruct (term.M.get x σ) as [y|] eqn:Hget; [|eauto with Ensembles_DB].
  intros arb Harb; inv Harb; right; unfold image'', Ensembles.In; now exists x.
Qed.

Lemma apply_r_list_vars σ xs :
  FromList (apply_r_list σ xs) \subset FromList xs :|: image'' σ.
Proof.
  induction xs as [|x xs IHxs]; [eauto with Ensembles_DB|cbn in *].
  repeat normalize_sets.
  apply Union_Included.
  - eapply Included_trans; [apply apply_r_vars|]; eauto with Ensembles_DB.
  - eapply Included_trans; [apply IHxs|]; eauto with Ensembles_DB.
Qed.

Fixpoint rename_all_used σ e {struct e} :
  used_vars (rename_all_ns σ e) \subset used_vars e :|: image'' σ.
Proof.
  destruct e; cbn in *; repeat normalize_used_vars.
  Ltac solve_easy_rename_used IH :=
    lazymatch goal with
    | |- _ :|: _ \subset _ => apply Union_Included; solve_easy_rename_used IH
    | |- [set apply_r _ _] \subset _ =>
      clear IH; eapply Included_trans; [apply apply_r_vars|]; eauto with Ensembles_DB
    | |- FromList (apply_r_list _ _) \subset _ =>
      clear IH; eapply Included_trans; [apply apply_r_list_vars|]; eauto with Ensembles_DB
    | |- used_vars _ \subset _ => eapply Included_trans; [apply IH|]; eauto with Ensembles_DB
    | |- _ => solve [eauto with Ensembles_DB]
    end.
  all: try solve [solve_easy_rename_used rename_all_used].
  - rewrite used_vars_Ecase; apply Union_Included; [solve_easy_rename_used rename_all_used|].
    induction l as [|[c e] ces IHces]; cbn; [eauto with Ensembles_DB|].
    repeat normalize_used_vars.
    apply Union_Included; [solve_easy_rename_used rename_all_used|].
    eapply Included_trans; [apply IHces|]; eauto with Ensembles_DB.
  - apply Union_Included; [|solve_easy_rename_used rename_all_used].
    induction f as [f ft xs e_body fds IHfds|]; cbn; [|eauto with Ensembles_DB].
    repeat normalize_used_vars.
    apply Union_Included; [solve_easy_rename_used rename_all_used|].
    eapply Included_trans; [apply IHfds|]; eauto with Ensembles_DB.
Qed.

Lemma empty_image : image'' (M.empty _) <--> Empty_set _.
Proof.
  unfold image'', Ensembles.In; split; intros x Hx; inv Hx.
  now rewrite M.gempty in H.
Qed.

Lemma set_lists_image'' xs ys σ σ' :
  set_lists xs ys σ = Some σ' ->
  image'' σ' \subset image'' σ :|: FromList ys.
Proof.
  revert ys σ σ'; induction xs as [|x xs IHxs]; destruct ys as [|y ys]; try solve [inversion 1].
  - inversion 1; eauto with Ensembles_DB.
  - intros σ σ' Hset; cbn in Hset.
    destruct (set_lists xs ys σ) as [σ''|] eqn:Hσ''; inv Hset.
    specialize (IHxs ys σ σ'' Hσ'').
    intros arb [x' Hx']; specialize (IHxs arb); unfold Ensembles.In, image'' in *.
    unfold apply_r in Hx'.
    destruct (Pos.eq_dec x' x) as [Heq|Hne]; [subst x'; rewrite M.gss in Hx'|rewrite M.gso in Hx' by auto].
    + right; subst; now left.
    + destruct IHxs as [Hσ|Hin_ys]; [eexists; eassumption|left|right; right]; auto.
Qed.

Lemma fresher_than_Empty_set x : fresher_than x (Empty_set _).
Proof. intros y []. Qed.

(* Some passes maintain map of known functions *)

Definition fun_map : Set := M.tree (fun_tag * list var * exp).

Fixpoint add_fundefs (fds : fundefs) (ρ : fun_map) : fun_map :=
  match fds with
  | Fcons f ft xs e fds => M.set f (ft, xs, e) (add_fundefs fds ρ)
  | Fnil => ρ
  end.

Fixpoint add_fundefs_Some f ft xs e ρ fds {struct fds} :
  M.get f (add_fundefs fds ρ) = Some (ft, xs, e) ->
  (exists fds1 fds2, fds = fundefs_append fds1 (Fcons f ft xs e fds2)) \/
  M.get f ρ = Some (ft, xs, e).
Proof.
  destruct fds as [g gt ys e' fds|]; [cbn; intros Hget|now right].
  destruct (Pos.eq_dec f g); [subst; rewrite M.gss in Hget; inv Hget; left; now exists Fnil, fds|].
  rewrite M.gso in Hget by auto.
  specialize (add_fundefs_Some _ _ _ _ ρ fds Hget).
  destruct add_fundefs_Some as [[fds1 [fds2 Heq]]|Hin]; [|now right].
  left; subst fds. exists (Fcons g gt ys e' fds1), fds2. reflexivity.
Qed.
