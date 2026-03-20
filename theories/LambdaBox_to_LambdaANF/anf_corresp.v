(* Correspondence between the monadic ANF transformation (convert_anf)
   and the relational specification (anf_cvt_rel).
   Proves that convert_anf satisfies the anf_cvt_rel spec. *)

(** Stdlib *)
From Stdlib Require Import ZArith.ZArith NArith.NArith Lists.List micromega.Lia Arith
     Ensembles Relations.Relation_Definitions.

(** MetaRocq *)
From MetaRocq.Erasure Require Import EAst EGlobalEnv EWellformed.
From MetaRocq.Common Require Import BasicAst Kernames.
From MetaRocq.Utils Require Import bytestring.

(** CompCert *)
From compcert Require Import lib.Maps lib.Coqlib.

(** ExtLib *)
From ExtLib Require Import Structures.Monads Data.Monads.OptionMonad.

(** CertiRocq *)
From CertiRocq.Common Require Import AstCommon compM.
From CertiRocq Require Import Pipeline_utils.
From CertiRocq.LambdaANF Require Import
  cps cps_util ctx List_util Ensembles_util
  identifiers state set_util.

From CertiRocq.LambdaBox_to_LambdaANF Require Import common ANF.

Import ListNotations.
Import Monad.MonadNotation.

Open Scope monad_scope.
Open Scope bs_scope.


Section Corresp.

  Context (func_tag default_tag : positive)
          (prim_map : M.t primitive)
          (tgm : conId_map)
          (prims : list (primitive * positive))
          (cmap : const_map).


  (** * var_map correctness *)

  (** Connects the computational var_map (M.t var * N) to the
      relational variable name list (list var). *)
  Definition var_map_correct (vm : var_map) (vn : list var) : Prop :=
    forall i, get_var_name vm (N.of_nat i) = nth_error vn i.

  Lemma var_map_correct_nil :
    var_map_correct new_var_map [].
  Proof.
    unfold var_map_correct, new_var_map, get_var_name. intros i.
    simpl. destruct i; reflexivity.
  Qed.

  (** Helper: get_var_name at index 0 after add gives the added variable *)
  Lemma get_var_name_add_0 vm x :
    get_var_name (add_var_name vm x) 0%N = Some x.
  Proof.
    unfold add_var_name, get_var_name. destruct vm as [m p].
    rewrite N.sub_0_r. rewrite M.gss. reflexivity.
  Qed.

  (** Helper: get_var_name at index (N.succ n) after add = get_var_name at n *)
  Lemma get_var_name_add_succ vm x n :
    get_var_name (add_var_name vm x) (N.succ n) = get_var_name vm n.
  Proof.
    unfold add_var_name, get_var_name. destruct vm as [m p].
    (* LHS: match (Npos (N.succ_pos p) - N.succ n) with ... end
       where the map is M.set (N.succ_pos p) x m
       RHS: match (p - n) with ... end
       where the map is m *)
    replace (Npos (N.succ_pos p) - N.succ n)%N with (p - n)%N.
    2:{ change (Npos (N.succ_pos p)) with (N.pos (N.succ_pos p)).
        rewrite N.succ_pos_spec. lia. }
    destruct (p - n)%N eqn:Hsub.
    - reflexivity.
    - rewrite M.gso; [ reflexivity | ].
      (* pos ≠ N.succ_pos p because Npos pos = p - n ≤ p < N.succ p = Npos (N.succ_pos p) *)
      intros Heq. subst.
      exfalso. subst.
      assert (N.pos (N.succ_pos p) = N.succ p) by apply N.succ_pos_spec.
      lia.
  Qed.

  Lemma var_map_correct_cons vm vn x :
    var_map_correct vm vn ->
    var_map_correct (add_var_name vm x) (x :: vn).
  Proof.
    unfold var_map_correct.
    intros Hvm i. destruct i as [ | i'].
    - (* i = 0 *)
      simpl. exact (get_var_name_add_0 vm x).
    - (* i = S i' *)
      simpl. rewrite <- (Hvm i').
      assert (Heq : N.pos (Pos.of_succ_nat i') = N.succ (N.of_nat i')).
      { rewrite <- Nat2N.inj_succ. reflexivity. }
      rewrite Heq.
      exact (get_var_name_add_succ vm x (N.of_nat i')).
  Qed.


  (** * Correspondence specification *)

  (** Hoare-style spec for convert_anf:
      If fresh S holds initially, then convert_anf produces a result
      satisfying anf_cvt_rel, and freshness is maintained. *)
  Definition anf_cvt_exp_corresp :=
    forall e vn vm S,
      var_map_correct vm vn ->
      {{ fun _ s => identifiers.fresh S (next_var (fst s)) }}
        convert_anf func_tag default_tag prim_map tgm prims cmap e vm
      {{ fun _ s p s' =>
           let '(r, C) := p in
           exists S',
             ANF.anf_cvt_rel func_tag default_tag tgm cmap S e vn S' C r /\
             identifiers.fresh S' (next_var (fst s')) }}.

  (* Shorthand for the conversion function with parameters applied *)
  Let cvt := convert_anf func_tag default_tag prim_map tgm prims cmap.

  (** Hoare-style spec for convert_anf_args *)
  Definition anf_cvt_args_corresp :=
    forall args vn vm S,
      var_map_correct vm vn ->
      {{ fun _ s => identifiers.fresh S (next_var (fst s)) }}
        convert_anf_args cvt args vm
      {{ fun _ s p s' =>
           let '(xs, C) := p in
           exists S',
             ANF.anf_cvt_rel_args func_tag default_tag tgm cmap S args vn S' C xs /\
             identifiers.fresh S' (next_var (fst s')) }}.

  (** failwith FALSIFIES any triple (error = False in the triple def) *)
  (* Note: {{ P }} failwith s {{ Q }} is NOT provable for arbitrary P.
     It's only true when P is False (i.e., when the error path is unreachable). *)

  (** Main soundness theorem — proved case by case *)

  (** tRel case: just a variable lookup, no monadic operations *)
  Lemma anf_cvt_sound_tRel :
    forall n vn vm S,
      var_map_correct vm vn ->
      (n < List.length vn)%nat ->
      {{ fun _ s => identifiers.fresh S (next_var (fst s)) }}
        cvt (EAst.tRel n) vm
      {{ fun _ s p s' =>
           let '(r, C) := p in
           exists S',
             ANF.anf_cvt_rel func_tag default_tag tgm cmap S (EAst.tRel n) vn S' C r /\
             identifiers.fresh S' (next_var (fst s')) }}.
  Proof.
    intros n vn vm S Hvm Hlt.
    simpl.
    unfold var_map_correct in Hvm.
    rewrite (Hvm n).
    (* n < length vn ensures nth_error succeeds *)
    destruct (nth_error vn n) eqn:Hnth.
    - eapply return_triple.
      intros _ s Hfresh.
      eexists S. split; [ | exact Hfresh ].
      econstructor. exact Hnth.
    - exfalso. apply nth_error_None in Hnth. lia.
  Qed.

  (** tConst case (non-primitive): lookup in cmap, no state change *)
  Lemma anf_cvt_sound_tConst :
    forall s vn vm S v,
      var_map_correct vm vn ->
      find_prim prims s = None ->
      lookup_const cmap s = Some v ->
      {{ fun _ st => identifiers.fresh S (next_var (fst st)) }}
        cvt (EAst.tConst s) vm
      {{ fun _ st p st' =>
           let '(r, C) := p in
           exists S',
             ANF.anf_cvt_rel func_tag default_tag tgm cmap S (EAst.tConst s) vn S' C r /\
             identifiers.fresh S' (next_var (fst st')) }}.
  Proof.
    intros s vn vm S v Hvm Hprim Hlookup.
    simpl. rewrite Hprim. rewrite Hlookup.
    eapply return_triple.
    intros _ st Hfresh.
    eexists S. split; [ | exact Hfresh ].
    econstructor. exact Hlookup.
  Qed.

  (** Spec for get_named: allocates one fresh variable from S *)
  (* Specs for get_named and get_named_str follow the pattern of
     get_name_spec in state.v. They allocate next_var, increment it,
     and maintain freshness of S \\ {x}. *)
  Lemma get_named_spec' S0 na :
    {{ fun (_ : unit) (s : comp_data * unit) => identifiers.fresh S0 (next_var (fst s)) }}
      @get_named unit na
    {{ fun (_ : unit) (s : comp_data * unit) (x : var) (s' : comp_data * unit) =>
         x \in S0 /\
         (next_var (fst s) < next_var (fst s'))%positive /\
         identifiers.fresh (S0 \\ [set x]) (next_var (fst s')) }}.
  Proof.
    (* get_named has the same freshness behavior as get_name.
       Derive from get_name_spec by showing extensional equivalence
       on the next_var field. *)
    intros r w Hpre.
    unfold get_named. unfold compM.get, compM.put.
    Transparent bind ret.
    simpl. destruct w as [cd []]. destruct cd. simpl in *.
    split.
    - eapply Hpre. reflexivity.
    - split. zify; lia.
      simpl. intros z Hin. constructor.
      + eapply Hpre; eauto. zify. lia.
      + intros Hc. inv Hc. zify; lia.
  Qed.
  Opaque bind ret.

  Lemma get_named_str_spec' S0 str :
    {{ fun (_ : unit) (s : comp_data * unit) => identifiers.fresh S0 (next_var (fst s)) }}
      @get_named_str unit str
    {{ fun (_ : unit) (s : comp_data * unit) (x : var) (s' : comp_data * unit) =>
         x \in S0 /\
         (next_var (fst s) < next_var (fst s'))%positive /\
         identifiers.fresh (S0 \\ [set x]) (next_var (fst s')) }}.
  Proof.
    intros r w Hpre.
    unfold get_named_str. unfold compM.get, compM.put.
    Transparent bind ret.
    simpl. destruct w as [cd []]. destruct cd. simpl in *.
    split.
    - eapply Hpre. reflexivity.
    - split. zify; lia.
      simpl. intros z Hin. constructor.
      + eapply Hpre; eauto. zify. lia.
      + intros Hc. inv Hc. zify; lia.
  Qed.
  Opaque bind ret.

  (** tBox case: allocate one fresh variable for the constructor *)
  Lemma anf_cvt_sound_tBox :
    forall vn vm S,
      var_map_correct vm vn ->
      {{ fun _ st => identifiers.fresh S (next_var (fst st)) }}
        cvt EAst.tBox vm
      {{ fun _ st p st' =>
           let '(r, C) := p in
           exists S',
             ANF.anf_cvt_rel func_tag default_tag tgm cmap S EAst.tBox vn S' C r /\
             identifiers.fresh S' (next_var (fst st')) }}.
  Proof.
    intros vn vm S Hvm.
    simpl.
    eapply bind_triple.
    - eapply get_named_str_spec'.
    - intros x w. eapply return_triple.
      intros _ st [Hx_in [_ Hfresh']].
      eexists (S \\ [set x]). split; [ | exact Hfresh' ].
      econstructor. exact Hx_in.
  Qed.

  (** tPrim case: translate primitive value, allocate one fresh variable *)
  Lemma anf_cvt_sound_tPrim :
    forall p pv vn vm S,
      var_map_correct vm vn ->
      trans_prim_val p = Some pv ->
      {{ fun _ st => identifiers.fresh S (next_var (fst st)) }}
        cvt (EAst.tPrim p) vm
      {{ fun _ st r st' =>
           let '(x, C) := r in
           exists S',
             ANF.anf_cvt_rel func_tag default_tag tgm cmap S (EAst.tPrim p) vn S' C x /\
             identifiers.fresh S' (next_var (fst st')) }}.
  Proof.
    intros p pv vn vm S Hvm Htrans.
    simpl. rewrite Htrans.
    eapply bind_triple.
    - eapply get_named_str_spec'.
    - intros x w. eapply return_triple.
      intros _ st [Hx_in [_ Hfresh']].
      eexists (S \\ [set x]). split; [ | exact Hfresh' ].
      econstructor; eassumption.
  Qed.

  (** Helper: generalized get_named_spec that carries extra info *)
  Lemma get_named_carry {P : Prop} S0 na :
    {{ fun (_ : unit) (s : comp_data * unit) =>
         P /\ identifiers.fresh S0 (next_var (fst s)) }}
      @get_named unit na
    {{ fun (_ : unit) (_ : comp_data * unit) (x : var) (s' : comp_data * unit) =>
         P /\ x \in S0 /\ identifiers.fresh (S0 \\ [set x]) (next_var (fst s')) }}.
  Proof.
    intros r w [HP Hfresh].
    unfold get_named, compM.get, compM.put.
    Transparent bind ret.
    simpl. destruct w as [cd []]. destruct cd. simpl in *.
    split; [ exact HP | ].
    split.
    - eapply Hfresh. reflexivity.
    - simpl. intros z Hin. constructor.
      + eapply Hfresh; eauto. zify. lia.
      + intros Hc. inv Hc. zify; lia.
  Qed.
  Opaque bind ret.

  Lemma get_named_str_carry {P : Prop} S0 str :
    {{ fun (_ : unit) (s : comp_data * unit) =>
         P /\ identifiers.fresh S0 (next_var (fst s)) }}
      @get_named_str unit str
    {{ fun (_ : unit) (_ : comp_data * unit) (x : var) (s' : comp_data * unit) =>
         P /\ x \in S0 /\ identifiers.fresh (S0 \\ [set x]) (next_var (fst s')) }}.
  Proof.
    intros r w [HP Hfresh].
    unfold get_named_str, compM.get, compM.put.
    Transparent bind ret.
    simpl. destruct w as [cd []]. destruct cd. simpl in *.
    split; [ exact HP | ].
    split.
    - eapply Hfresh. reflexivity.
    - simpl. intros z Hin. constructor.
      + eapply Hfresh; eauto. zify. lia.
      + intros Hc. inv Hc. zify; lia.
  Qed.
  Opaque bind ret.

  (** tProj case: convert scrutinee, then allocate fresh variable for projection *)
  Lemma anf_cvt_sound_tProj :
    forall p c vn vm S,
      var_map_correct vm vn ->
      (forall vn' vm' S',
          var_map_correct vm' vn' ->
          {{ fun _ st => identifiers.fresh S' (next_var (fst st)) }}
            cvt c vm'
          {{ fun _ st r st' =>
               let '(x, C) := r in
               exists S'',
                 ANF.anf_cvt_rel func_tag default_tag tgm cmap S' c vn' S'' C x /\
                 identifiers.fresh S'' (next_var (fst st')) }}) ->
      {{ fun _ st => identifiers.fresh S (next_var (fst st)) }}
        cvt (EAst.tProj p c) vm
      {{ fun _ st r st' =>
           let '(x, C) := r in
           exists S',
             ANF.anf_cvt_rel func_tag default_tag tgm cmap S (EAst.tProj p c) vn S' C x /\
             identifiers.fresh S' (next_var (fst st')) }}.
  Proof.
    intros p c vn vm S Hvm IHc.
    simpl.
    eapply bind_triple with
      (Q' := fun _ _ xC st' =>
               let '(x0, C0) := xC in
               exists S2,
                 ANF.anf_cvt_rel func_tag default_tag tgm cmap S c vn S2 C0 x0 /\
                 identifiers.fresh S2 (next_var (fst st'))).
    - eapply IHc. exact Hvm.
    - intros [x C_sub] w.
      eapply pre_existential. intros S2.
      eapply bind_triple.
      + eapply @get_named_carry with
          (P := ANF.anf_cvt_rel func_tag default_tag tgm cmap S c vn S2 C_sub x).
      + intros y w1.
        eapply return_triple.
        intros _ st [Hrel [Hy_in Hfresh']].
        eexists (S2 \\ [set y]). split; [ | exact Hfresh' ].
        econstructor; [ reflexivity | exact Hrel | exact Hy_in ].
  Qed.

  (** tLetIn case: convert binding, then body with extended var_map *)
  Lemma anf_cvt_sound_tLetIn :
    forall na b t vn vm S,
      var_map_correct vm vn ->
      (forall vn' vm' S',
          var_map_correct vm' vn' ->
          {{ fun _ st => identifiers.fresh S' (next_var (fst st)) }}
            cvt b vm'
          {{ fun _ st r st' =>
               let '(x, C) := r in
               exists S'',
                 ANF.anf_cvt_rel func_tag default_tag tgm cmap S' b vn' S'' C x /\
                 identifiers.fresh S'' (next_var (fst st')) }}) ->
      (forall vn' vm' S',
          var_map_correct vm' vn' ->
          {{ fun _ st => identifiers.fresh S' (next_var (fst st)) }}
            cvt t vm'
          {{ fun _ st r st' =>
               let '(x, C) := r in
               exists S'',
                 ANF.anf_cvt_rel func_tag default_tag tgm cmap S' t vn' S'' C x /\
                 identifiers.fresh S'' (next_var (fst st')) }}) ->
      {{ fun _ st => identifiers.fresh S (next_var (fst st)) }}
        cvt (EAst.tLetIn na b t) vm
      {{ fun _ st r st' =>
           let '(x, C) := r in
           exists S',
             ANF.anf_cvt_rel func_tag default_tag tgm cmap S (EAst.tLetIn na b t) vn S' C x /\
             identifiers.fresh S' (next_var (fst st')) }}.
  Proof.
    intros na b t vn vm S Hvm IHb IHt.
    simpl.
    eapply bind_triple with
      (Q' := fun _ _ xC st' =>
               let '(x1, C1) := xC in
               exists S2,
                 ANF.anf_cvt_rel func_tag default_tag tgm cmap S b vn S2 C1 x1 /\
                 identifiers.fresh S2 (next_var (fst st'))).
    - eapply IHb. exact Hvm.
    - intros [x1 C1] w.
      eapply pre_existential. intros S2.
      eapply bind_triple'' with
        (Q' := fun _ _ xC st' =>
                 let '(r, C2) := xC in
                 ANF.anf_cvt_rel func_tag default_tag tgm cmap S b vn S2 C1 x1 /\
                 exists S3,
                   ANF.anf_cvt_rel func_tag default_tag tgm cmap S2 t (x1::vn) S3 C2 r /\
                   identifiers.fresh S3 (next_var (fst st'))).
      + intros w0 [r C2].
        eapply return_triple.
        intros _ st [Hrel_b [S3 [Hrel_t Hfresh3]]].
        eexists S3. split; [ | exact Hfresh3 ].
        econstructor; eassumption.
      + eapply post_weakening.
        2:{ eapply @pre_strenghtening.
            2:{ eapply IHt. eapply var_map_correct_cons. exact Hvm. }
            intros _ st [Hrel_b Hfresh]. exact Hfresh. }
        intros _ w0 xC w' [Hrel_b _].
        destruct xC as [r C2].
        intros [S3 [Hrel_t Hfresh3]].
        split; [ exact Hrel_b | ].
        exists S3. split; [ exact Hrel_t | exact Hfresh3 ].
  Qed.

  (** tApp case: convert function, argument, then allocate fresh result var *)
  Lemma anf_cvt_sound_tApp :
    forall u v vn vm S,
      var_map_correct vm vn ->
      (forall vn' vm' S',
          var_map_correct vm' vn' ->
          {{ fun _ st => identifiers.fresh S' (next_var (fst st)) }}
            cvt u vm'
          {{ fun _ st r st' =>
               let '(x, C) := r in
               exists S'',
                 ANF.anf_cvt_rel func_tag default_tag tgm cmap S' u vn' S'' C x /\
                 identifiers.fresh S'' (next_var (fst st')) }}) ->
      (forall vn' vm' S',
          var_map_correct vm' vn' ->
          {{ fun _ st => identifiers.fresh S' (next_var (fst st)) }}
            cvt v vm'
          {{ fun _ st r st' =>
               let '(x, C) := r in
               exists S'',
                 ANF.anf_cvt_rel func_tag default_tag tgm cmap S' v vn' S'' C x /\
                 identifiers.fresh S'' (next_var (fst st')) }}) ->
      {{ fun _ st => identifiers.fresh S (next_var (fst st)) }}
        cvt (EAst.tApp u v) vm
      {{ fun _ st r st' =>
           let '(x, C) := r in
           exists S',
             ANF.anf_cvt_rel func_tag default_tag tgm cmap S (EAst.tApp u v) vn S' C x /\
             identifiers.fresh S' (next_var (fst st')) }}.
  Proof.
    intros u v vn vm S Hvm IHu IHv.
    simpl.
    eapply bind_triple with
      (Q' := fun _ _ xC st' =>
               let '(x1, C1) := xC in
               exists S2,
                 ANF.anf_cvt_rel func_tag default_tag tgm cmap S u vn S2 C1 x1 /\
                 identifiers.fresh S2 (next_var (fst st'))).
    - eapply IHu. exact Hvm.
    - intros [x1 C1] w.
      eapply pre_existential. intros S2.
      eapply bind_triple'' with
        (Q' := fun _ _ xC st' =>
                 let '(x2, C2) := xC in
                 exists S3,
                   ANF.anf_cvt_rel func_tag default_tag tgm cmap S u vn S2 C1 x1 /\
                   ANF.anf_cvt_rel func_tag default_tag tgm cmap S2 v vn S3 C2 x2 /\
                   identifiers.fresh S3 (next_var (fst st'))).
      + intros w0 [x2 C2].
        eapply pre_existential. intros S3.
        eapply bind_triple.
        * eapply pre_strenghtening.
          2:{ eapply @get_named_carry with
                (P := ANF.anf_cvt_rel func_tag default_tag tgm cmap S u vn S2 C1 x1 /\
                      ANF.anf_cvt_rel func_tag default_tag tgm cmap S2 v vn S3 C2 x2)
                (S0 := S3). }
          intros _ st [Hu [Hv Hfresh]].
          split; [ split; [ exact Hu | exact Hv ] | exact Hfresh ].
        * intros r w2.
          eapply return_triple.
          intros _ st [[Hrel_u Hrel_v] [Hr_in Hfresh']].
          eexists (S3 \\ [set r]). split; [ | exact Hfresh' ].
          eapply anf_App; eassumption.
      + eapply post_weakening.
        2:{ eapply @pre_strenghtening.
            2:{ eapply IHv. exact Hvm. }
            intros _ st [Hrel_u Hfresh]. exact Hfresh. }
        intros _ w0 xC w' [Hrel_u _].
        destruct xC as [x2 C2].
        intros [S3 [Hrel_v Hfresh3]].
        exists S3. split; [ exact Hrel_u | ].
        split; [ exact Hrel_v | exact Hfresh3 ].
  Qed.

  (** tLambda case: allocate param var, function name, then convert body *)
  Lemma anf_cvt_sound_tLambda :
    forall na body vn vm S,
      var_map_correct vm vn ->
      (forall vn' vm' S',
          var_map_correct vm' vn' ->
          {{ fun _ st => identifiers.fresh S' (next_var (fst st)) }}
            cvt body vm'
          {{ fun _ st r st' =>
               let '(x, C) := r in
               exists S'',
                 ANF.anf_cvt_rel func_tag default_tag tgm cmap S' body vn' S'' C x /\
                 identifiers.fresh S'' (next_var (fst st')) }}) ->
      {{ fun _ st => identifiers.fresh S (next_var (fst st)) }}
        cvt (EAst.tLambda na body) vm
      {{ fun _ st r st' =>
           let '(x, C) := r in
           exists S',
             ANF.anf_cvt_rel func_tag default_tag tgm cmap S (EAst.tLambda na body) vn S' C x /\
             identifiers.fresh S' (next_var (fst st')) }}.
  Proof.
    intros na body vn vm S Hvm IHbody.
    simpl.
    eapply bind_triple.
    - eapply get_named_spec'.
    - intros x w.
      eapply bind_triple.
      + eapply pre_strenghtening.
        2:{ eapply @get_named_carry with (P := x \in S) (S0 := S \\ [set x]). }
        intros _ st [Hx [_ Hfresh]].
        split; [ exact Hx | exact Hfresh ].
      + intros f w1.
        eapply bind_triple'' with
          (Q' := fun _ _ xC st' =>
                   let '(r, C_body) := xC in
                   exists S',
                     x \in S /\ f \in (S \\ [set x]) /\
                     ANF.anf_cvt_rel func_tag default_tag tgm cmap
                       (S \\ [set x] \\ [set f]) body (x :: vn) S' C_body r /\
                     identifiers.fresh S' (next_var (fst st'))).
        * intros w2 [r C_body].
          eapply return_triple.
          intros _ st [S' [Hx_in [Hf_in [Hrel Hfresh']]]].
          eexists S'. split; [ | exact Hfresh' ].
          econstructor; eassumption.
        * eapply post_weakening.
          2:{ eapply @pre_strenghtening.
              2:{ eapply IHbody. eapply var_map_correct_cons. exact Hvm. }
              intros _ st [Hx_in [Hf_in Hfresh]]. exact Hfresh. }
          intros _ w2 xC w' [Hx_in [Hf_in _]].
          destruct xC as [r C_body].
          intros [S' [Hrel Hfresh']].
          exists S'. split; [ exact Hx_in | ].
          split; [ exact Hf_in | ].
          split; [ exact Hrel | exact Hfresh' ].
  Qed.

  (** tConstruct case: allocate name, convert args, build constructor *)
  Lemma anf_cvt_sound_tConstruct :
    forall ind c args vn vm S,
      var_map_correct vm vn ->
      (forall vn' vm' S',
          var_map_correct vm' vn' ->
          {{ fun _ st => identifiers.fresh S' (next_var (fst st)) }}
            convert_anf_args cvt args vm'
          {{ fun _ st r st' =>
               let '(xs, C) := r in
               exists S'',
                 ANF.anf_cvt_rel_args func_tag default_tag tgm cmap S' args vn' S'' C xs /\
                 identifiers.fresh S'' (next_var (fst st')) }}) ->
      {{ fun _ st => identifiers.fresh S (next_var (fst st)) }}
        cvt (EAst.tConstruct ind c args) vm
      {{ fun _ st r st' =>
           let '(x, C) := r in
           exists S',
             ANF.anf_cvt_rel func_tag default_tag tgm cmap S (EAst.tConstruct ind c args) vn S' C x /\
             identifiers.fresh S' (next_var (fst st')) }}.
  Proof.
    intros ind c args vn vm S Hvm IHargs.
    simpl.
    eapply bind_triple.
    - eapply get_named_spec'.
    - intros x w.
      eapply bind_triple'' with
        (Q' := fun _ _ xsC st' =>
                 let '(xs, C) := xsC in
                 x \in S /\
                 exists S2,
                   ANF.anf_cvt_rel_args func_tag default_tag tgm cmap
                     (S \\ [set x]) args vn S2 C xs /\
                   identifiers.fresh S2 (next_var (fst st'))).
      + intros w0 [ys C_args].
        eapply return_triple.
        intros _ st [Hx_in [S2 [Hrel_args Hfresh2]]].
        eexists S2. split; [ | exact Hfresh2 ].
        econstructor; [ reflexivity | exact Hx_in | exact Hrel_args ].
      + eapply post_weakening.
        2:{ eapply @pre_strenghtening.
            2:{ eapply IHargs. exact Hvm. }
            intros _ st [Hx_in [_ Hfresh]]. exact Hfresh. }
        intros _ w0 xsC w' [Hx_in _].
        destruct xsC as [xs C_args].
        intros [S2 [Hrel_args Hfresh2]].
        split; [ exact Hx_in | ].
        exists S2. split; [ exact Hrel_args | exact Hfresh2 ].
  Qed.

  (** Soundness for convert_anf_args: nil case *)
  Lemma anf_cvt_sound_args_nil :
    forall vn vm S,
      var_map_correct vm vn ->
      {{ fun _ st => identifiers.fresh S (next_var (fst st)) }}
        convert_anf_args cvt [] vm
      {{ fun _ st r st' =>
           let '(xs, C) := r in
           exists S',
             ANF.anf_cvt_rel_args func_tag default_tag tgm cmap S [] vn S' C xs /\
             identifiers.fresh S' (next_var (fst st')) }}.
  Proof.
    intros vn vm S Hvm.
    simpl.
    eapply return_triple.
    intros _ st Hfresh.
    eexists S. split; [ econstructor | exact Hfresh ].
  Qed.

  (** Soundness for convert_anf_args: cons case *)
  Lemma anf_cvt_sound_args_cons :
    forall t ts vn vm S,
      var_map_correct vm vn ->
      (forall vn' vm' S',
          var_map_correct vm' vn' ->
          {{ fun _ st => identifiers.fresh S' (next_var (fst st)) }}
            cvt t vm'
          {{ fun _ st r st' =>
               let '(x, C) := r in
               exists S'',
                 ANF.anf_cvt_rel func_tag default_tag tgm cmap S' t vn' S'' C x /\
                 identifiers.fresh S'' (next_var (fst st')) }}) ->
      (forall vn' vm' S',
          var_map_correct vm' vn' ->
          {{ fun _ st => identifiers.fresh S' (next_var (fst st)) }}
            convert_anf_args cvt ts vm'
          {{ fun _ st r st' =>
               let '(xs, C) := r in
               exists S'',
                 ANF.anf_cvt_rel_args func_tag default_tag tgm cmap S' ts vn' S'' C xs /\
                 identifiers.fresh S'' (next_var (fst st')) }}) ->
      {{ fun _ st => identifiers.fresh S (next_var (fst st)) }}
        convert_anf_args cvt (t :: ts) vm
      {{ fun _ st r st' =>
           let '(xs, C) := r in
           exists S',
             ANF.anf_cvt_rel_args func_tag default_tag tgm cmap S (t :: ts) vn S' C xs /\
             identifiers.fresh S' (next_var (fst st')) }}.
  Proof.
    intros t ts vn vm S Hvm IHt IHts.
    simpl.
    eapply bind_triple with
      (Q' := fun _ _ xC st' =>
               let '(y, C1) := xC in
               exists S2,
                 ANF.anf_cvt_rel func_tag default_tag tgm cmap S t vn S2 C1 y /\
                 identifiers.fresh S2 (next_var (fst st'))).
    - eapply IHt. exact Hvm.
    - intros [y C1] w.
      eapply pre_existential. intros S2.
      eapply bind_triple'' with
        (Q' := fun _ _ xsC st' =>
                 let '(ys, C2) := xsC in
                 ANF.anf_cvt_rel func_tag default_tag tgm cmap S t vn S2 C1 y /\
                 exists S3,
                   ANF.anf_cvt_rel_args func_tag default_tag tgm cmap S2 ts vn S3 C2 ys /\
                   identifiers.fresh S3 (next_var (fst st'))).
      + intros w0 [ys C2].
        eapply return_triple.
        intros _ st [Hrel_t [S3 [Hrel_ts Hfresh3]]].
        eexists S3. split; [ | exact Hfresh3 ].
        econstructor; eassumption.
      + eapply post_weakening.
        2:{ eapply @pre_strenghtening.
            2:{ eapply IHts. exact Hvm. }
            intros _ st [Hrel Hfresh]. exact Hfresh. }
        intros _ w0 xsC w' [Hrel _].
        destruct xsC as [ys C2].
        intros [S3 [Hrel_ts Hfresh3]].
        split; [ exact Hrel | ].
        exists S3. split; [ exact Hrel_ts | exact Hfresh3 ].
  Qed.

  (** Helper: carry a Prop through a Hoare triple *)
  Lemma pre_curry_prop {A : Type} (P : Prop)
        (Pre0 : unit -> (comp_data * unit) -> Prop)
        (Q : unit -> (comp_data * unit) -> A -> (comp_data * unit) -> Prop)
        (e : @compM' unit A) :
    (P -> {{ Pre0 }} e {{ Q }}) ->
    {{ fun r w => P /\ Pre0 r w }} e {{ fun r w x w' => P /\ Q r w x w' }}.
  Proof.
    unfold triple. intros H r w [HP Hpre].
    specialize (H HP r w Hpre).
    destruct e as [fe]. unfold runState in *. simpl in *.
    destruct (fe r w) as [[? | ?] ?]; auto.
  Qed.

  (** tCase case *)
  Lemma anf_cvt_sound_tCase :
    forall ind npars mch brs vn vm S,
      var_map_correct vm vn ->
      (forall vn' vm' S',
          var_map_correct vm' vn' ->
          {{ fun _ st => identifiers.fresh S' (next_var (fst st)) }}
            cvt mch vm'
          {{ fun _ st r st' =>
               let '(x, C) := r in
               exists S'',
                 ANF.anf_cvt_rel func_tag default_tag tgm cmap S' mch vn' S'' C x /\
                 identifiers.fresh S'' (next_var (fst st')) }}) ->
      (forall y S',
          {{ fun _ st => identifiers.fresh S' (next_var (fst st)) }}
            convert_anf_branches default_tag tgm cvt ind brs 0%N y vm
          {{ fun _ st r st' =>
               exists S'',
                 ANF.anf_cvt_rel_branches func_tag default_tag tgm cmap
                   S' ind brs 0%N vn y S'' r /\
                 identifiers.fresh S'' (next_var (fst st')) }}) ->
      {{ fun _ st => identifiers.fresh S (next_var (fst st)) }}
        cvt (EAst.tCase (ind, npars) mch brs) vm
      {{ fun _ st r st' =>
           let '(x, C) := r in
           exists S',
             ANF.anf_cvt_rel func_tag default_tag tgm cmap S
               (EAst.tCase (ind, npars) mch brs) vn S' C x /\
             identifiers.fresh S' (next_var (fst st')) }}.
  Proof.
    intros ind npars mch brs vn vm S Hvm IHmch IHbrs.
    simpl.
    (* f <- get_named_str "f_case" *)
    eapply bind_triple. { eapply get_named_str_spec'. }
    intros f w.
    (* y <- get_named_str "s" *)
    eapply bind_triple.
    { eapply pre_strenghtening.
      2:{ eapply @get_named_str_carry with (P := f \in S) (S0 := S \\ [set f]). }
      intros _ st [Hf [_ Hfresh]]. exact (conj Hf Hfresh). }
    intros y w1.
    (* Unfold the triple to work directly with state *)
    intros r0 w0 [Hf_in [Hy_in Hfresh_fy]].
    Transparent bind ret.
    unfold bind, ret in *. simpl in *.
    (* Apply IHmch *)
    specialize (IHmch vn vm (S \\ [set f] \\ [set y]) Hvm r0 w0 Hfresh_fy).
    destruct (runState (cvt mch vm) r0 w0) as [[? | [x1 C1]] w2]; [exact IHmch | ].
    destruct IHmch as [S2 [Hrel_mch Hfresh2]].
    (* Apply IHbrs *)
    specialize (IHbrs y S2 r0 w2 Hfresh2).
    unfold triple in IHbrs. simpl in IHbrs.
    destruct (convert_anf_branches default_tag tgm cvt ind brs 0%N y vm) as [fe_brs] eqn:Hbrs_eq.
    simpl in *.
    destruct (fe_brs r0 w2) as [[? | pats] w3]; [exact IHbrs | ].
    destruct IHbrs as [S3 [Hrel_brs Hfresh3]].
    (* get_named def_name + ret are now unfolded inline *)
    (* The goal after unfold is a match on the overall computation result.
       After get_named (which is unfolded by `unfold get_named, compM.get, compM.put; simpl`),
       we need to show the postcondition for the final Ret value. *)
    unfold get_named, compM.get, compM.put.
    destruct w3 as [cd3 []]. cbn [fst snd runState].
    destruct cd3 as [nv ? ? ? ? ? ? ? ?]. simpl.
    exists (S3 \\ [set nv]). split.
    - eapply anf_Case; try eassumption.
      + eapply Hfresh3. reflexivity.
    - simpl in *. intros z Hz. constructor.
      + eapply Hfresh3. zify. lia.
      + intros Hc. inv Hc. zify. lia.
  Qed.
  Opaque bind ret.

End Corresp.
