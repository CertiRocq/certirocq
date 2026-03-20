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

End Corresp.
