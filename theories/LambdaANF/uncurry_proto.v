(** Uncurrying written as a guarded rewrite rule *)

From Stdlib Require Import Classes.Morphisms.
From Stdlib Require Import NArith.BinNat PArith.BinPos Sets.Ensembles Lia.
Require Import Common.
Require Import LambdaANF.Prototype.
Require Import LambdaANF.proto_util.
Require Import LambdaANF.term LambdaANF.cps_proto_univ LambdaANF.cps_proto.
Require Import identifiers.  (* for max_var, occurs_in_exp, .. *)
Require Import LambdaANF.Ensembles_util LambdaANF.List_util LambdaANF.term_util LambdaANF.state.

From Stdlib Require Import Lists.List.
Import ListNotations.

(* Set Universe Polymorphism. *)
Unset MetaRocq Strict Unquote Universe Mode.

(** * Uncurrying as a guarded rewrite rule *)

(* Hack: the pretty-printer uses cdata to associate strings with freshly generated names.
   In order to be able to pretty-print our terms, we'll need to update cdata accordingly even
   though we don't use it to generate fresh names. [set_name] and [set_names_lst] are analogues
   of [get_name] and [get_names_lst] from state.v. *)

Definition set_name old_var new_var suff cdata :=
  let '{| next_var := n; nect_ctor_tag := c; next_ind_tag := i; next_fun_tag := f;
          cenv := e; fenv := fenv; nenv := names; inline_map := imap; log := log |} := cdata
  in
  let names' := add_entry names new_var old_var suff in
  {| next_var := (1 + Pos.max old_var new_var)%positive; nect_ctor_tag := c;
     next_ind_tag := i; next_fun_tag := f; cenv := e; fenv := fenv;
     nenv := names'; inline_map := imap; log := log |}.

Definition set_names_lst olds news suff cdata :=
  fold_right (fun '(old, new) cdata => set_name old new suff cdata) cdata (combine olds news).

(** * Auxiliary data used by the rewriter *)

(* true if in cps mode *)
Definition I_R : forall {A}, frames_t A exp_univ_exp -> bool -> Prop := (I_R_plain (R:=bool)).

(* pair of
   1 - max number of arguments
   2 - encoding of inlining decision for beta-contraction phase *)
Definition St : Set := (nat * (term.M.tree nat))%type.
(* 0 -> Do not inline, 1 -> uncurried function, 2 -> continuation of uncurried function *)

(* Maps (arity+1) to the right fun_tag *)
Definition arity_map : Set := term.M.tree fun_tag.
Definition local_map : Set := term.M.tree bool.

(* The state for this includes
   1 - a boolean for tracking whether or not a reduction happens
   2 - Map recording the (new) fun_tag associated to each arity
   3 - local map from var to if function has already been uncurried
   4 - Map for uncurried functions for a version of inlining *)
Definition S_misc : Set := bool * arity_map * local_map * St * comp_data.

(* Based on [get_fun_tag] from uncurry.v *)
Definition get_fun_tag (n : N) (ms : S_misc) : fun_tag * S_misc :=
  let '(b, aenv, lm, s, cdata) := ms in
  let n' := N.succ_pos n in
  match M.get n' aenv with
  | Some ft => (ft, ms)
  | None =>
    let '(mft, (cdata, tt)) := compM.runState (get_ftag n) tt (cdata, tt) in
    match mft with
    | compM.Err _ => (xH, ms) (* bogus *)
    | compM.Ret ft =>
      (ft, (b, M.set n' ft aenv, lm, s, cdata))
    end
  end.

Inductive uncurry_step : exp -> exp -> Prop :=
(* Uncurrying for CPS *)
| uncurry_cps :
  forall (C : @frames_t exp_univ Frame_exp exp_univ_fundefs exp_univ_exp)
    (f f1 : var) (ft ft1 : fun_tag) (k k' : var) (kt : fun_tag) (fv fv1 : list var)
    (g g' : var) (gt : fun_tag) (gv gv1 : list var) (ge : exp) (fds : fundefs)
    (lhs fds' rhs : fundefs) fp_numargs (ms ms' : S_misc),
  (* Non-linear LHS constraints *)
  k = k' /\
  g = g' /\
  (* Guards: *)
  (* (1) g can't be recursive or invoke k *)
  ~ g \in used_vars ge /\
  ~ k \in used_vars ge /\
  (* (2) gv1, fv1, f1 must be fresh and contain no duplicates *)
  lhs = Fcons f ft (k :: fv) (Efun (Fcons g gt gv ge Fnil) (Eapp k' kt [g'])) fds /\
  fds' = Fcons f1 ft1 (gv ++ fv) ge fds /\
  rhs = Fcons f ft (k :: fv1) (Efun (Fcons g gt gv1 (Eapp f1 ft1 (gv1 ++ fv1)) Fnil) (Eapp k kt [g])) fds' /\
  fresh_copies (used_vars (C ⟦ lhs ⟧)) gv1 /\ length gv1 = length gv /\
  fresh_copies (used_vars (C ⟦ lhs ⟧) :|: FromList gv1) fv1 /\ length fv1 = length fv /\
  ~ f1 \in (used_vars (C ⟦ lhs ⟧) :|: FromList gv1 :|: FromList fv1) /\
  (* (3) generate fun_tag + update ms *)
  fp_numargs = length fv + length gv /\
  (ft1, ms') = get_fun_tag (N.of_nat fp_numargs) ms ->
  (* The rewrite *)
  uncurry_step
    (C ⟦ Fcons f ft (k :: fv) (Efun (Fcons g gt gv ge Fnil) (Eapp k' kt [g'])) fds ⟧)
    (C ⟦ (* Rewrite f as a wrapper around the uncurried f1 and recur on fds *)
         (Fcons f ft (k :: fv1) (Efun (Fcons g gt gv1 (Eapp f1 ft1 (gv1 ++ fv1)) Fnil) (Eapp k kt [g]))
          (Rec fds')) ⟧)
(* Uncurrying for ANF *)
| uncurry_anf :
  forall (C : frames_t exp_univ_fundefs exp_univ_exp)
    (f f1 : var) (ft ft1 : fun_tag) (fv fv1 : list var)
    (g g' : var) (gt : fun_tag) (gv gv1 : list var) (ge : exp) (fds : fundefs)
    (lhs fds' rhs : fundefs)
    fp_numargs (ms ms' : S_misc),
  (* Non-linear LHS constraints *)
  g = g' /\
  (* Guards: *)
  (* (1) g can't be recursive *)
  ~ g \in used_vars ge /\
  (* (2) gv1, fv1, f1 must be fresh and contain no duplicates *)
  lhs = Fcons f ft fv (Efun (Fcons g gt gv ge Fnil) (Ehalt g')) fds /\
  fds' = Fcons f1 ft1 (gv ++ fv) ge fds /\
  rhs = Fcons f ft fv1 (Efun (Fcons g gt gv1 (Eapp f1 ft1 (gv1 ++ fv1)) Fnil) (Ehalt g)) fds' /\
  fresh_copies (used_vars (C ⟦ lhs ⟧)) gv1 /\ length gv1 = length gv /\
  fresh_copies (used_vars (C ⟦ lhs ⟧) :|: FromList gv1) fv1 /\ length fv1 = length fv /\
  ~ f1 \in (used_vars (C ⟦ lhs ⟧) :|: FromList gv1 :|: FromList fv1) /\
  (* (3) generate fun_tag + update ms *)
  fp_numargs = length fv + length gv /\
  (ft1, ms') = get_fun_tag (N.of_nat fp_numargs) ms ->
  (* The rewrite *)
  uncurry_step
    (C ⟦ Fcons f ft fv (Efun (Fcons g gt gv ge Fnil) (Ehalt g')) fds ⟧)
    (C ⟦ (* Rewrite f as a wrapper around the uncurried f1 and recur on fds *)
         (Fcons f ft fv1 (Efun (Fcons g gt gv1 (Eapp f1 ft1 (gv1 ++ fv1)) Fnil) (Ehalt g))
          (Rec fds')) ⟧).

Definition I_S : forall {A}, frames_t A exp_univ_exp -> univD A -> _ -> Prop :=
  I_S_prod (I_S_plain (S:=S_misc)) (@I_S_fresh).

(** * Uncurrying as a recursive function *)

(* Set Printing Universes. *)

Lemma bool_true_false b : b = false -> b <> true. Proof. now destruct b. Qed.

Local Ltac clearpose H x e :=
  pose (x := e); assert (H : x = e) by (subst x; reflexivity); clearbody x.

Definition metadata_update (f g f1 : var) fp_numargs (fv gv fv1 gv1 : list var) (ms : S_misc) : S_misc :=
  let '(b, aenv, lm, s, cdata) := ms in
  (* Set flag to indicate that a rewrite was performed (used to iterate to fixed point) *)
  let b := true in
  (* Mark g as uncurried *)
  let lm := M.set g true lm in
  (* Update inlining heuristic so inliner knows to inline fully saturated calls to f *)
  let s := (max (fst s) fp_numargs, (M.set f 1 (M.set g 2 (snd s)))) in
  (* Hack: update cdata to agree with fresh names generated above *)
  let cdata :=
    set_name f f1 "_uncurried"%bs
    (set_names_lst fv fv1 ""
    (set_names_lst gv gv1 "" cdata))
  in
  (b, aenv, lm, s, cdata).

Definition rw_uncurry :
  rewriter exp_univ_exp false (fun A C e => @univ_size A e)
           uncurry_step _ (I_D_plain (D:=Datatypes.unit)) _ (@I_R) _ (@I_S).
Proof.
  mk_rw; mk_easy_delay;
    try lazymatch goal with
    (* Solve easy obligations about termination *)
    | |- MetricDecreasing -> _ =>
      intros _; cbn in *;
        try change (size_exp ?e) with (size e);
        try change (size_list _ ?x) with (size x);
        try change (size_fundefs ?x) with (size x);
        lia
    end.
  (* Obligation 1: uncurry_cps side conditions *)
  - intros; unfold delayD, Delayed_id_Delay in *.
    (* Check nonlinearities *)
    destruct (eq_var k k') eqn:Hkk'; [|cond_failure].
    destruct (eq_var g g') eqn:Hgg'; [|cond_failure].
    rewrite Pos.eqb_eq in Hkk', Hgg'.
    (* Unpack parameter and state *)
    rename r into mr; unfold Param, I_R, I_R_plain in mr; destruct mr as [mr _].
    destruct s as [[ms next_x] Hnext_x] eqn:Hs.
    destruct ms as [[[[b aenv] lm] heuristic] cdata] eqn:Hms.
    (* Check whether g has already been uncurried before *)
    destruct (mr && negb (match M.get g lm with Some true => true | _ => false end))%bool
      as [|] eqn:Huncurried; [|cond_failure].
    (* Check that {g, k} ∩ vars(ge) = ∅ *)
    destruct (occurs_in_exp g ge) eqn:Hocc_g; [cond_failure|].
    destruct (occurs_in_exp k ge) eqn:Hocc_k; [cond_failure|].
    apply bool_true_false in Hocc_g; apply bool_true_false in Hocc_k.
    rewrite occurs_in_exp_iff_used_vars in Hocc_g, Hocc_k.
    (* Generate ft1 + new misc state ms *)
    pose (fp_numargs := length fv + length gv).
    cond_success success; specialize success with (ms := ms) (fp_numargs := fp_numargs).
    destruct (get_fun_tag (BinNatDef.N.of_nat fp_numargs) ms) as [ft1 ms'] eqn:Hms'.
    (* Generate f1, fv1, gv1, next_x *)
    clearpose Hxgv1 xgv1 (gensyms next_x gv); destruct xgv1 as [next_x0 gv1].
    clearpose Hxfv1 xfv1 (gensyms next_x0 fv); destruct xfv1 as [next_x1 fv1].
    clearpose Hf1 f1 next_x1.
    specialize success with (f1 := f1) (fv1 := fv1) (gv1 := gv1).
    (* Prove that all the above code actually satisfies the side condition *)
    unfold I_S, I_S_prod, I_S_plain, I_S_fresh in *.
    pose (fds' := Fcons f1 ft1 (gv ++ fv) ge fds).
    specialize (success fds' d f ft k fv g gt gv ge k' kt g' fds ft1).
    pose (lhs := Fcons f ft (k :: fv)
                   (Efun (Fcons g gt gv ge Fnil) (Eapp k' kt [g'])) fds).
    pose (rhs := Fcons f ft (k :: fv1)
                  (Efun (Fcons g gt gv1 (Eapp f1 ft1 (gv1 ++ fv1)) Fnil)
                    (Eapp k kt [g])) fds').
    specialize (success lhs fds' rhs ms').
    eapply success; [|reflexivity|reflexivity| |];
    try lazymatch goal with
    | |- «_» => unerase; destruct Hnext_x as [? Hnext_x];
      (edestruct (@gensyms_spec var) as [Hgv_copies [Hfresh_gv Hgv_len]]; try exact Hxgv1; [eassumption|]);
      (edestruct (@gensyms_spec var) as [Hfv_copies [Hfresh_fv Hfv_len]]; try exact Hxfv1; [eassumption|]);
      repeat match goal with |- _ /\ _ => split end;
      try solve [reflexivity|eassumption|subst;reflexivity|reflexivity]
    | |- Delay _ _ => exact d
    | |- Param _ _ => exists mr; unerase; exact I
    end.
    + apply fresher_than_not_In; subst f1; exact Hfresh_fv.
    + (* Explain how to update state.
         There are two parts: update various pieces of metadata and show that next_x is still fresh *)
      exists (metadata_update f g f1 fp_numargs fv gv fv1 gv1 ms', next_x1 + 1)%positive.
      unerase; split; [exact I|].
      destruct Hnext_x as [? Hnext_x];
      edestruct (@gensyms_spec var) as [Hgv_copies [Hfresh_gv Hgv_len]]; try exact Hxgv1; [eassumption|].
      edestruct (@gensyms_spec var) as [Hfv_copies [Hfresh_fv Hfv_len]]; try exact Hxfv1; [eassumption|].
      match type of Hfresh_fv with
      | fresher_than _ ?S =>
        assert (Hunion : fresher_than (next_x1 + 1)%positive (S :|: [set f1]))
      end.
      apply fresher_than_Union; [|subst; simpl; intros y Hy; inversion Hy; lia].
      eapply fresher_than_monotonic; eauto; lia.
      eapply fresher_than_antimon; [|eassumption].
      subst fds'; unfold Rec.
      rewrite used_vars_fundefs_app. (repeat normalize_used_vars).
      rewrite used_vars_fundefs_app. (repeat normalize_used_vars).
      repeat normalize_sets.
      intros arbitrary; rewrite !In_or_Iff_Union; clear; tauto.
  (* Obligation 2: uncurry_anf side conditions *)
  - intros; unfold delayD, Delayed_id_Delay in *.
    (* Check nonlinearities *)
    destruct (eq_var g g') eqn:Hgg'; [|cond_failure].
    rewrite Pos.eqb_eq in Hgg'.
    (* Unpack parameter and state *)
    rename r into mr; unfold Param, I_R, I_R_plain in mr; destruct mr as [mr _].
    destruct s as [[ms next_x] Hnext_x] eqn:Hs.
    destruct ms as [[[[b aenv] lm] heuristic] cdata] eqn:Hms.
    (* Check whether g has already been uncurried before *)
    destruct (negb mr && negb (match M.get g lm with Some true => true | _ => false end))%bool
      as [|] eqn:Huncurried; [|cond_failure].
    (* Check that {g, k} ∩ vars(ge) = ∅ *)
    destruct (occurs_in_exp g ge) eqn:Hocc_g; [cond_failure|].
    apply bool_true_false in Hocc_g.
    rewrite occurs_in_exp_iff_used_vars in Hocc_g.
    (* Generate ft1 + new misc state ms *)
    pose (fp_numargs := length fv + length gv).
    cond_success success; specialize success with (ms := ms) (fp_numargs := fp_numargs).
    destruct (get_fun_tag (BinNatDef.N.of_nat fp_numargs) ms) as [ft1 ms'] eqn:Hms'.
    (* Generate f1, fv1, gv1, next_x *)
    clearpose Hxgv1 xgv1 (gensyms next_x gv); destruct xgv1 as [next_x0 gv1].
    clearpose Hxfv1 xfv1 (gensyms next_x0 fv); destruct xfv1 as [next_x1 fv1].
    clearpose Hf1 f1 next_x1.
    specialize success with (f1 := f1) (fv1 := fv1) (gv1 := gv1).
    pose (fds' := Fcons f1 ft1 (gv ++ fv) ge fds).
    specialize (success fds' d f ft fv g gt gv ge g' fds ft1).
    pose (lhs := Fcons f ft fv (Efun (Fcons g gt gv ge Fnil) (Ehalt g')) fds).
    pose (rhs := Fcons f ft fv1
                   (Efun (Fcons g gt gv1 (Eapp f1 ft1 (gv1 ++ fv1)) Fnil) (Ehalt g))
                 fds').
    specialize (success lhs fds' rhs ms').
    (* Prove that all the above code actually satisfies the side condition *)
    eapply success; [|reflexivity|reflexivity| |];
    try lazymatch goal with
    | |- «_» => unerase; destruct Hnext_x as [? Hnext_x];
      (edestruct (@gensyms_spec var) as [Hgv_copies [Hfresh_gv Hgv_len]]; try exact Hxgv1; [eassumption|]);
      (edestruct (@gensyms_spec var) as [Hfv_copies [Hfresh_fv Hfv_len]]; try exact Hxfv1; [eassumption|]);
      repeat match goal with |- _ /\ _ => split end;
      try solve [reflexivity|eassumption|subst;reflexivity|reflexivity]
    | |- Delay _ _ => exact d
    | |- Param _ _ => exists mr; unerase; exact I
    end.
    + apply fresher_than_not_In; subst f1; exact Hfresh_fv.
    + exists (metadata_update f g f1 fp_numargs fv gv fv1 gv1 ms', next_x1 + 1)%positive.
      unerase; split; [exact I|].
      destruct Hnext_x as [? Hnext_x];
      edestruct (@gensyms_spec var) as [Hgv_copies [Hfresh_gv Hgv_len]]; try exact Hxgv1; [eassumption|].
      edestruct (@gensyms_spec var) as [Hfv_copies [Hfresh_fv Hfv_len]]; try exact Hxfv1; [eassumption|].
      match type of Hfresh_fv with
      | fresher_than _ ?S =>
        assert (Hunion : fresher_than (next_x1 + 1)%positive (S :|: [set f1]))
      end.
      apply fresher_than_Union; [|subst; simpl; intros y Hy; inversion Hy; lia].
      eapply fresher_than_monotonic; eauto; lia.
      eapply fresher_than_antimon; [|eassumption].
      subst fds'; unfold Rec.
      rewrite used_vars_fundefs_app. (repeat normalize_used_vars).
      rewrite used_vars_fundefs_app. (repeat normalize_used_vars).
      repeat normalize_sets.
      intros arbitrary; rewrite !In_or_Iff_Union; clear; tauto.
  (* Obligations 3 and 4: must prove that recursive call made by ANF and CPS uncurry are on smaller terms *)
  - cbn in *; subst fds'0. decompose [and] H; subst fds'; cbn; intros _.
    assert (size (gv ++ fv) < size gv + size fv) by now apply size_app.
    lia.
  - cbn in *; subst fds'0. decompose [and] H; subst fds'; cbn; intros _.
    assert (size (gv ++ fv) < size gv + size fv) by now apply size_app.
    lia.
  - cbn in *.
    change ((fix size_exp (e1 : exp) : nat :=
               match e1 with
               | Ecase _ ces => S (S (size_list (size_prod size size_exp) ces))
               | Eproj _ _ _ _ e2 => S (S (S (S (S (size_exp e2)))))
               | Eletapp _ _ _ ys e2 => S (S (S (S (size ys + size_exp e2))))
               | Efun fds e2 => S (size_fundefs fds + size_exp e2)
               | Eapp _ _ xs => S (S (S (size xs)))
               | Eprim_val _ _ e2 => S (S (S (size_exp e2)))
               | Econstr _ _ ys e2 | Eprim _ _ ys e2 => S (S (S (size ys + size_exp e2)))
               | Ehalt x => S (size x)
               end
               with size_fundefs (fds : fundefs) : nat :=
                 match fds with
                 | Fcons _ _ xs e1 fds0 => S (S (S (size xs + size_exp e1 + size_fundefs fds0)))
                 | Fnil => 1
                 end
                   for
                   size_exp) e0) with (size e0). cbn. lia.
  - cbn in *.
    change ((fix size_exp (e1 : exp) : nat :=
               match e1 with
               | Ecase _ ces => S (S (size_list (size_prod size size_exp) ces))
               | Eproj _ _ _ _ e2 => S (S (S (S (S (size_exp e2)))))
               | Eletapp _ _ _ ys e2 => S (S (S (S (size ys + size_exp e2))))
               | Efun fds e2 => S (size_fundefs fds + size_exp e2)
               | Eapp _ _ xs => S (S (S (size xs)))
               | Eprim_val _ _ e2 => S (S (S (size_exp e2)))
               | Econstr _ _ ys e2 | Eprim _ _ ys e2 => S (S (S (size ys + size_exp e2)))
               | Ehalt x => S (size x)
               end
               with size_fundefs (fds : fundefs) : nat :=
                 match fds with
                 | Fcons _ _ xs e1 fds0 => S (S (S (size xs + size_exp e1 + size_fundefs fds0)))
                 | Fnil => 1
                 end
                   for
                   size_fundefs) f) with (size f). cbn. lia.
Defined.

Set Extraction Flag 2031. (* default + linear let + linear beta *)
(* Recursive Extraction rw_uncurry. *)

Definition uncurry_top (cps : bool) (e : exp) (c : state.comp_data) : compM.error exp * state.comp_data.
  destruct (Pos.ltb_spec0 (max_var e 1) (state.next_var c))%positive as [Hlt|Hge].
  2: { exact (compM.Err "uncurry_top: max_var computation failed", c). }
  unshelve refine (let res := run_rewriter' rw_uncurry e _ _ in _).
  - unshelve econstructor; [exact cps|unerase; exact I].
  - unshelve econstructor; [refine ((false, M.empty _, M.empty _, (0, M.empty _), c), state.next_var c)|].
    unerase; unfold I_S, I_S_prod; split; [exact I|]; unfold I_S_fresh.
    unfold fresher_than; simpl.
    intros _ [y' Hbv|y' Hfv].
    + abstract (apply bound_var_leq_max_var with (y := 1%positive) in Hbv; lia).
    + abstract (apply occurs_free_leq_max_var with (y := 1%positive) in Hfv; lia).
  - destruct res as [e' [[[[_ s] c'] fresh] _] _].
    exact (compM.Ret e',
           mkCompData fresh c'.(nect_ctor_tag) c'.(next_ind_tag)
                                                    c'.(next_fun_tag) c'.(cenv) c'.(fenv) c'.(nenv) (snd s) c'.(log)).
Defined.
