From compcert Require Import
  Coqlib
  lib.Integers common.Memory.

From CertiRocq Require Import
  LambdaANF.term LambdaANF.eval LambdaANF.term_util
  LambdaANF.List_util LambdaANF.identifiers
  CodegenWasm.LambdaANF_to_Wasm
  CodegenWasm.LambdaANF_to_Wasm_restrictions
  CodegenWasm.LambdaANF_to_Wasm_primitives
  Libraries.maps_util.

From Wasm Require Import
  datatypes operations host instantiation_spec type_preservation
  instantiation_properties opsem properties.

From Stdlib Require Import
  List ListDec
  Logic.Decidable
  Relations.Relations Relations.Relation_Operators
  Lia
  Uint63.

Import Common.compM Common.Pipeline_utils.
Import bytestring.
Import ExtLib.Structures.Monad MonadNotation.
Import ssreflect ssrbool eqtype.
Import Wasm_int.

Import ListNotations.
Import seq.

Ltac unfold_serialise :=
  unfold serialise_num, serialise_i32, serialise_i64, serialise_f32,
         serialise_f64, encode_int, rev_if_be;
    destruct Archi.big_endian.

Ltac simpl_modulus_in H :=
  unfold Wasm_int.Int32.modulus, Wasm_int.Int64.modulus,
         Wasm_int.Int32.half_modulus, Wasm_int.Int64.half_modulus,
         two_power_nat in H; cbn in H.

Ltac simpl_modulus :=
  unfold Wasm_int.Int64.max_unsigned, Wasm_int.Int32.modulus,
         Wasm_int.Int64.modulus, Wasm_int.Int32.half_modulus,
         Wasm_int.Int64.half_modulus, two_power_nat.


(* helpers for stepping through a list of Wasm instructions *)
Ltac separate_instr :=
  cbn;
  repeat match goal with
  |- context C [?x :: ?l] =>
     lazymatch l with [::] => fail | _ => rewrite -(cat1s x l) end
  end.

(** The lemmas [r_eliml] and [r_elimr] are relicts,
    kept for compatability for now, TODO rework (use new context representation) **)
Lemma r_eliml `{ho : host} : forall hs s f es hs' s' f' es' lconst,
  const_list lconst ->
  reduce hs s f es hs' s' f' es' ->
  reduce hs s f (lconst ++ es) hs' s' f' (lconst ++ es').
Proof.
  move => hs s f es hs' s' f' es' lconst HConst H.
  apply const_es_exists in HConst. destruct HConst as [vs ?].
  eapply r_label with (lh:=LH_base vs []). eassumption.
  - cbn. rewrite cats0. congruence.
  - cbn. rewrite cats0. congruence.
Qed.

Lemma r_elimr `{ho : host} : forall hs s f es hs' s' f' es' les,
  reduce hs s f es hs' s' f' es' ->
  reduce hs s f (es ++ les) hs' s' f' (es' ++ les).
Proof.
  move => hs s f es hs' s' f' es' les H.
  eapply r_label with (lh:=LH_base [] les); eauto.
Qed.

(* isolate instr. + n leading args, e.g. with n=2 for add:
   [const 1, const 2, add, remaining instr] => [const 1, const 2, add]  *)
Ltac elimr_nary_instr n :=
  let H := fresh "H" in
  match n with
  | 0 => lazymatch goal with
         | |- reduce _ _ _ ([:: ?instr])        _ _ _ _ => idtac
         | |- reduce _ _ _ ([:: ?instr] ++ ?l3) _ _ _ _ => apply r_elimr
         end
  | 1 => lazymatch goal with
         | |- reduce _ _ _ ([::$VN ?c1] ++ [:: ?instr])        _ _ _ _ => idtac
         | |- reduce _ _ _ ([::$VN ?c1] ++ [:: ?instr] ++ ?l3) _ _ _ _ =>
            assert ([::$VN c1] ++ [:: instr] ++ l3 =
                    [:: $VN c1; instr] ++ l3) as H by reflexivity; rewrite H;
                                                       apply r_elimr; clear H
         end
  | 2 => lazymatch goal with
         | |- reduce _ _ _ ([::$VN ?c1] ++ [::$VN ?c2] ++ [:: ?instr])        _ _ _ _ => idtac
         | |- reduce _ _ _ ([::$VN ?c1] ++ [::$VN ?c2] ++ [:: ?instr] ++ ?l3) _ _ _ _ =>
            assert ([::$VN c1] ++ [:: $VN c2] ++ [:: instr] ++ l3 =
                    [::$VN c1; $VN c2; instr] ++ l3) as H by reflexivity; rewrite H;
                                                       apply r_elimr; clear H
         end
  end.

(* single step *)
Ltac dostep :=
  eapply rt_trans with (y := (?[hs], ?[sr], ?[f'], ?[s] ++ ?[t]));
  first (apply rt_step; separate_instr).

(* single step, only returns single list of instructions *)
Ltac dostep' :=
   eapply rt_trans with (y := (?[hs], ?[sr], ?[f'], ?[s]));
   first (apply rt_step; separate_instr).

(* single step, n-ary instruction *)
Ltac dostep_nary n :=
  dostep; first elimr_nary_instr n.

(* single step, n-ary instruction *)
Ltac dostep_nary' n :=
  dostep'; first elimr_nary_instr n.

(* single step, n-ary instruction. Additionally, leave n' leading values untouched *)
Ltac dostep_nary_eliml n n' :=
  dostep; first ((do n'! (apply r_eliml; auto)); elimr_nary_instr n).


Section General.

Lemma notNone_Some {A} : forall (o : option A),
  o <> None <-> exists v, o = Some v.
Proof.
  intros. destruct o; split; intros.
  eauto. congruence. contradiction. now destruct H.
Qed.

Lemma Some_notNone {A} : forall (o : option A) v,
  o = Some v -> o <> None.
Proof.
  congruence.
Qed.

Lemma In_map {A} {B} (f : A -> B) x xs : In x xs -> In (f x) (map f xs).
Proof.
  induction xs; auto; simpl.
  intros [Heq|Hin]; auto.
  intuition congruence.
Qed.

Lemma NoDup_app_In {A} : forall l1 l2 (x:A),
  NoDup (l1 ++ l2) ->
  In x l1 ->
  ~ In x l2.
Proof.
  induction l1; cbn; intros; auto.
  destruct H0.
  { (* a = x *)
    subst. intro. inv H. apply H3.
    now apply in_app_iff. }
  { intro Hcontra. inv H. now eapply IHl1. }
Qed.

Lemma NoDup_app_remove_middle : forall A (a b c : list A),
  NoDup (a ++ b ++ c) -> NoDup (a ++ c).
Proof.
  intros. generalize dependent a. revert c.
  induction b; intros; auto.
  cbn in H. now apply NoDup_remove_1 in H.
Qed.

Lemma NoDup_incl_NoDup' {A} : forall (l1' l1 l2 : list A),
  NoDup (l1 ++ l2) -> NoDup l1' -> incl l1' l1 -> NoDup (l1' ++ l2).
Proof.
  induction l1'; intros.
  - destruct l1. assumption. cbn. inv H. now apply NoDup_app_remove_l in H5.
  - cbn. inv H0.
    assert (Hincl: incl l1' l1). { intros a' Hain'. apply H1. now right. }
    constructor. intro Hcontra. apply in_app_or in Hcontra. destruct Hcontra; auto.
    assert (In a l1). apply H1. now left. now eapply NoDup_app_In in H.
    now eapply IHl1'.
Qed.

Lemma set_nth_nth_error_same : forall {X:Type} (l:seq X) e e' i vd,
    nth_error l i = Some e ->
    nth_error (set_nth vd l i e') i = Some e'.
Proof.
  intros. revert l H. induction i; intros.
  - inv H. destruct l; inv H1. reflexivity.
  - cbn in H. destruct l. inv H. now apply IHi in H.
Qed.


Lemma set_nth_nth_error_other : forall {X:Type} (l:seq X) e i j vd,
    i <> j -> j < length l ->
    List.nth_error (set_nth vd l j e) i = List.nth_error l i.
Proof.
  induction l; intros.
  - cbn in H0. lia.
  - cbn in H0. destruct i.  cbn. destruct j. contradiction. reflexivity. cbn in *.
    destruct j; cbn; auto. apply IHl. lia. lia.
Qed.

Lemma nthN_nth_error {A} : forall (l : list A) i,
  nthN l (N.of_nat i) = nth_error l i.
Proof.
  induction l; intros.
  - destruct i; reflexivity.
  - destruct i; try reflexivity.
    replace (N.of_nat (S i)) with (1 + N.of_nat i)%N by lia.
    cbn. rewrite -IHl. cbn.
    destruct (N.of_nat i) eqn:Heqn; auto.
    destruct p; auto.
    replace (N.pos (Pos.succ p)~0 - 1)%N with (N.pos p~1)%N by lia. reflexivity.
Qed.

Lemma map_repeat_eq {A} {B} : forall (l : list A) (v : B),
  repeat v (Datatypes.length l) = map (fun _ => v) l.
Proof.
  induction l; cbn; intros; auto. f_equal. apply IHl.
Qed.

Lemma map_map_seq {A B C}: forall (l:seq A) (f: A -> B) (g : B -> C),
   [seq g (f a) | a <- l] = [seq (g v) | v <- [seq f a | a <- l]].
Proof.
  induction l; intros; cbn; auto. f_equal. now apply IHl.
Qed.

Lemma mapi_aux_acc_snoc {A B} : forall xs idx l a (f : nat -> A -> B),
  mapi_aux (idx, l ++ [::a]) f xs = a :: mapi_aux (idx, l) f xs.
Proof.
  induction xs; intros.
  - cbn. by rewrite rev_app_distr.
  - cbn. by rewrite -IHxs.
Qed.

Lemma mapi_aux_nth_error {A B} : forall xs i x (f : nat -> A -> B) idx,
  nth_error xs i = Some x ->
  nth_error (mapi_aux (idx, []) f xs) i = Some (f (idx + i) x).
Proof.
  induction xs; intros. destruct i=>//.
  cbn. rewrite (mapi_aux_acc_snoc _ _ []).
  destruct i. injection H as <-. cbn. do 2 f_equal. lia.
  replace (idx + S i) with (S idx + i) by lia.
  rewrite -IHxs; auto. cbn.
  do 4 f_equal. lia.
Qed.

Lemma mapi_nth_error {A B} : forall xs i x (f : nat -> A -> B),
  nth_error xs i = Some x ->
  nth_error (mapi f xs) i = Some (f i x).
Proof.
  intros.
  by eapply mapi_aux_nth_error.
Qed.

Lemma mapi_aux_nth_error_None {A B} : forall xs i (f : nat -> A -> B) idx,
  nth_error xs i = None ->
  nth_error (mapi_aux (idx, []) f xs) i = None.
Proof.
  induction xs; intros. destruct i=>//.
  cbn. rewrite (mapi_aux_acc_snoc _ _ []).
  destruct i=>//.
  cbn. erewrite <-IHxs; eauto.
Qed.

Lemma mapi_nth_error_None {A B} : forall xs i (f : nat -> A -> B),
  nth_error xs i = None ->
  nth_error (mapi f xs) i = None.
Proof.
  intros.
  by eapply mapi_aux_nth_error_None.
Qed.

Lemma mapi_aux_length {A B} : forall xs idx l (f : nat -> A -> B) ys,
  mapi_aux (idx, l) f xs = ys ->
  length xs + length l = length ys.
Proof.
  induction xs; cbn; intros.
  - subst ys. by rewrite length_rev.
  - apply IHxs in H. cbn in H. lia.
Qed.

Lemma mapi_length {A B} : forall xs (f : nat -> A -> B) ys,
  mapi f xs = ys ->
  length xs = length ys.
Proof.
  intros.
  apply mapi_aux_length in H. cbn in H. lia.
Qed.

Lemma drop_is_skipn {A} : forall l n, @drop A n l = List.skipn n l.
Proof.
  induction l; intros; auto.
  - induction n; cbn; auto.
  - destruct n. reflexivity. cbn. now rewrite IHl.
Qed.

Lemma take_drop_is_set_nth {B} : forall a (b : B) (l : list B),
  a < length l ->
  take a l ++ b :: drop (a + 1) l = set_nth b l a b.
Proof.
  intros. apply nth_error_ext; intros.
  assert (Hlen: length (take a l) = a). {
    rewrite length_is_size size_take -length_is_size.
    assert (ssrnat.leq (S a) (Datatypes.length l)). { apply /ssrnat.leP. lia. }
    now rewrite H0. }
  destruct (Nat.lt_total n a). 2: destruct H0.
  { (* n < a *)
    erewrite set_nth_nth_error_other; auto; try lia.
    assert (n < Datatypes.length (take a l)). {
      rewrite length_is_size size_take -length_is_size.
      destruct (ssrnat.leq (S a) (Datatypes.length l)); lia. }
    rewrite nth_error_app1; auto.
    assert (H': n < length l) by lia. apply nth_error_Some in H'. apply notNone_Some in H'.
    destruct H'.
    erewrite nth_error_take; eauto. apply /ssrnat.leP. lia. }
  { (* n=a *)
    subst.
    have H' := H. apply nth_error_Some in H'. apply notNone_Some in H'. destruct H'.
    erewrite set_nth_nth_error_same; eauto.
    rewrite nth_error_app2. replace (a - Datatypes.length (take a l)) with 0.
    reflexivity. lia. lia. }
  { (* a < n *)
    rewrite nth_error_app2. 2: lia.
    rewrite set_nth_nth_error_other; try lia.
    rewrite Hlen drop_is_skipn.
    destruct n; first lia. destruct l; first inv H.
    replace (a + 1) with (S a) by lia.
    replace (S n - a) with (S (n - a)) by lia. cbn.
    rewrite MRList.nth_error_skipn. cbn.
    now replace (a + (n - a)) with n by lia. }
Qed.

End General.


Section Vars.

Fixpoint fds_collect_local_variables (fds : fundefs) : list term.var :=
  match fds with
  | Fnil => []
  | Fcons _ _ ys e fds' => (ys ++ collect_local_variables e) ++ (fds_collect_local_variables fds')
  end.

Definition collect_all_local_variables (e : term.exp) : list term.var :=
  match e with
  | Efun fds e' => collect_local_variables e' ++ fds_collect_local_variables fds
  | _ => collect_local_variables e
  end.

Lemma find_def_collect_all_local_variables : forall fds f t ys e e',
  find_def f fds = Some (t, ys, e) ->
  incl (ys ++ collect_local_variables e) (collect_all_local_variables (Efun fds e')).
Proof.
  unfold incl.
  induction fds; intros. 2: inv H.
  cbn in H. destruct (M.elt_eq f0 v).
  { (* f0=v *) subst v. inv H. cbn. apply in_or_app. right. apply in_or_app. now left. }
  { (* f0<>v *) have H' := IHfds _ _ _ _ e H _ H0. cbn. cbn in H'.
    apply in_or_app. right. rewrite <-app_assoc. apply in_or_app. now right. }
Qed.


Lemma NoDup_collect_all_local_variables_find_def : forall fds e f t ys e0,
 NoDup
   (collect_all_local_variables (Efun fds e) ++
    collect_function_vars (Efun fds e))%list ->
  find_def f fds = Some (t, ys, e0) ->
 NoDup
  ((ys ++ collect_local_variables e0) ++
   collect_function_vars (Efun fds e0)).
Proof.
  intros.
  assert (Hnodup: NoDup (ys ++ collect_local_variables e0)). {
    generalize dependent e. generalize dependent e0. revert f t ys.
    induction fds; intros. 2: inv H0. cbn in H0. destruct (M.elt_eq f0 v).
    { (* v=f0 *) inv H0. cbn in H. rewrite <- catA in H. apply NoDup_app_remove_l in H.
      apply NoDup_app_remove_r in H. now apply NoDup_app_remove_r in H. }
    { (* v<>f0 *)
      eapply IHfds with (e:=e1); eauto. cbn in H. cbn.
      rewrite <- catA. repeat rewrite <- catA in H. apply NoDup_app_remove_middle in H.
      apply NoDup_app_remove_middle in H. rewrite catA in H.
      replace (v
       :: (fix iter (fds : fundefs) : seq var :=
             match fds with
             | Fcons x _ _ _ fds' => x :: iter fds'
             | Fnil => [::]
             end) fds) with ([v] ++
       (fix iter (fds : fundefs) : seq var :=
             match fds with
             | Fcons x _ _ _ fds' => x :: iter fds'
             | Fnil => [::]
             end) fds) in H by reflexivity.
      apply NoDup_app_remove_middle in H. rewrite <- catA in H. assumption.
    }}
  have Hincl := find_def_collect_all_local_variables _ _ _ _ _ e H0.
  now eapply NoDup_incl_NoDup'.
Qed.

Lemma NoDup_case: forall cl t e y,
    findtag cl t  = Some e ->
    NoDup (collect_local_variables (Ecase y cl)) ->
    NoDup (collect_local_variables e).
Proof.
  induction cl; intros.
  - inv H.
  - destruct a.
    destruct (M.elt_eq c t). inv H.
    assert (e = e0). { destruct (M.elt_eq t t). now inv H2. destruct n. reflexivity. }
    subst e0.
    cbn in H0.
    now apply NoDup_app_remove_r in H0.
    cbn in H0.
    apply NoDup_app_remove_l in H0.
    apply IHcl with (t:=t) (e:=e) (y:=y); auto.
    inv H. now destruct (M.elt_eq c t).
Qed.

Lemma find_def_in_collect_function_vars : forall fds f e,
  find_def f fds <> None <->
  In f (collect_function_vars (Efun fds e)).
Proof.
  induction fds; intros; split.
  - intro H. cbn in H.
    destruct (M.elt_eq f0 v).
    (* v=f0*) subst. now cbn.
    (* v<>f0*) right. eapply IHfds. eassumption.
  - intros H Hcontra. cbn in H. cbn in Hcontra.
    destruct (M.elt_eq f0 v).
    (* v=f0*) subst. now cbn.
    (* v<>f0*) destruct H as [H | H]. now subst.
               eapply IHfds. eassumption. assumption.
  - intro H. contradiction.
  - intro H. inv H.
  Unshelve. all: auto.
Qed.

Lemma find_def_not_in_collect_function_vars : forall fds f e,
  find_def f fds = None ->
  ~ In f (collect_function_vars (Efun fds e)).
Proof.
  intros ? ? ? Hfd Hcontra.
  by apply find_def_in_collect_function_vars in Hcontra.
Qed.

Lemma collect_function_vars_length : forall fds e,
  length (collect_function_vars (Efun fds e)) = numOf_fundefs fds.
Proof.
  induction fds; intros; auto. cbn. f_equal. now eapply IHfds with (e:=e).
Qed.

(* Var maps: var -> local idx / fn idx *)

Definition map_injective (m : M.tree u32) := forall x y x' y',
  x <> y ->
  m ! x = Some x' ->
  m ! y = Some y' ->
  x' <> y'.

Definition domains_disjoint (m1 m2: M.tree u32) :=
  (forall x v1, m1 ! x = Some v1 -> m2 ! x = None) /\
  (forall x v2, m2 ! x = Some v2 -> m1 ! x = None).

Lemma HfenvWf_None {fenv} : forall fds,
  (forall f : var,
    (exists res : fun_tag * seq var * exp, find_def f fds = Some res) <->
    (exists i : N, fenv ! f = Some i)) ->

  (forall f, find_def f fds = None <-> fenv ! f = None).
Proof.
  intros. split; intros; specialize H with f.
  - assert (~ exists p, fenv ! f = Some p). {
      intro Hcontra. rewrite <- H in Hcontra. now destruct Hcontra. }
    destruct (fenv ! f); auto. exfalso. now apply H1.
  - assert (~ exists p, find_def f fds = Some p). {
      intro Hcontra. rewrite H in Hcontra. now destruct Hcontra. }
    destruct (find_def f fds); auto. exfalso. now apply H1.
Qed.

Lemma var_mapping_list_lt_length' {nenv} : forall l loc loc' err_str n,
  translate_var nenv (create_var_mapping n l (M.empty _)) loc err_str = Ret loc' ->
  N.to_nat loc' < length l + N.to_nat n.
Proof.
  intros ? ? ? ? ? H.
  unfold translate_var in H.
  destruct (create_var_mapping n l (M.empty _)) ! loc eqn:Heqn; rewrite Heqn in H; inv H.
  generalize dependent loc. revert loc' err_str n.
  induction l; intros. inv Heqn.
  destruct (var_dec loc a).
  (* loc = a *) subst. cbn in Heqn. rewrite Maps.PTree.gss in Heqn. inv Heqn. cbn. lia.
  (* loc <> a *) cbn in Heqn. rewrite Maps.PTree.gso in Heqn; auto. cbn.
  replace (S (Datatypes.length l + N.to_nat n)) with (Datatypes.length l + N.to_nat (N.succ n)) by lia.
  eapply IHl; eauto.
Qed.

Lemma var_mapping_list_lt_length {nenv} : forall l loc loc' err_str,
  translate_var nenv (create_local_variable_mapping l) loc err_str = Ret loc' ->
  N.to_nat loc' < length l.
Proof.
  intros. apply var_mapping_list_lt_length' in H. lia.
Qed.

Lemma var_mapping_list_lt_length_nth_error_idx {nenv} : forall l i n x err,
  NoDup l ->
  lookup_N l i = Some x ->
  translate_var nenv (create_var_mapping n l (M.empty _)) x err = Ret (n + i)%N.
Proof.
  induction l; intros.
  - unfold lookup_N in H0.
    destruct (N.to_nat i)=>//.
  - destruct (var_dec a x).
    + (* x=a *)
      subst. unfold lookup_N in H0.
      destruct (N.to_nat i) eqn:Hi.
      * cbn. unfold translate_var. rewrite M.gss. f_equal. lia.
      * cbn in H0. apply nth_error_In in H0.
        apply NoDup_cons_iff in H. now destruct H.
    + (* x<> a *)
      (* cbn. rewrite M.gso; auto. cbn. *)
      unfold lookup_N in H0. destruct i; cbn in H0; first by inv H0.
      destruct (Pos.to_nat p) eqn:Hp; try lia. cbn in H0.
      replace (n + N.pos p)%N with (N.succ n + N.of_nat n1)%N by lia.
      cbn. unfold translate_var. rewrite M.gso; auto.
      inv H. apply IHl; auto.
      rewrite -H0. unfold lookup_N. f_equal. lia.
Qed.

Lemma local_variable_mapping_gt_idx : forall l idx x x',
  (create_var_mapping idx l (M.empty u32)) ! x = Some x' -> (x' >= idx)%N.
Proof.
  induction l; intros. inv H.
  cbn in H.
  destruct (Pos.eq_dec a x).
  - (* a=x *)
    subst a. rewrite M.gss in H. inv H. lia.
  - (* a<>x *)
    rewrite M.gso in H; auto.
    apply IHl in H. lia.
Qed.

Lemma variable_mapping_Some_In : forall l x v idx lenv,
  lenv ! x = None ->
  (create_var_mapping idx l lenv) ! x = Some v ->
  In x l.
Proof.
  induction l; intros.
  - inv H0. congruence.
  - cbn in H0. destruct (var_dec a x).
    + (* a = x*) subst. now cbn.
    + (* a <> x *) right. rewrite M.gso in H0; auto.
      eapply IHl; eauto.
Qed.

 Lemma variable_mapping_NotIn_None : forall l x idx lenv,
  ~ In x l ->
  lenv ! x = None ->
  (create_var_mapping idx l lenv) ! x = None.
Proof.
  induction l; intros; cbn; auto. cbn in H.
  assert (x <> a) by auto.
  assert (~ In x l) by auto. clear H.
  rewrite M.gso; auto.
Qed.

Lemma variable_mapping_In_Some : forall l x idx lenv,
  NoDup l ->
  In x l ->
  (create_var_mapping idx l lenv) ! x <> None.
Proof.
  induction l; intros.
  - inv H0.
  - cbn in H0. destruct H0.
    (* a = x*) subst. cbn. intro. now rewrite M.gss in H0.
    (* In x l *) cbn. inv H. rewrite M.gso; auto. intro. now subst.
Qed.

Lemma variable_mappings_nodup_disjoint : forall l1 l2 idx1 idx2,
  NoDup (l1 ++ l2) ->
  domains_disjoint (create_var_mapping idx1 l1 (M.empty _))
                   (create_var_mapping idx2 l2 (M.empty _)).
Proof.
  intros. unfold domains_disjoint.
  split; intros.
  - apply variable_mapping_Some_In in H0; auto.
    apply variable_mapping_NotIn_None; auto. intro. now eapply NoDup_app_In.
  - apply variable_mapping_Some_In in H0; auto.
    apply variable_mapping_NotIn_None; auto. intro. now eapply NoDup_app_In.
Qed.

Lemma create_local_variable_mapping_injective : forall l idx,
   NoDup l -> map_injective (create_var_mapping idx l (M.empty u32)).
Proof.
  induction l; intros. { cbn. intros ????? H1. inv H1. }
  inv H. cbn. unfold map_injective in *. intros.
  destruct (Pos.eq_dec a x).
  - (* a=x *)
    subst a. intro. subst y'.
    rewrite M.gss in H0. inv H0. rewrite M.gso in H1; auto.
    apply local_variable_mapping_gt_idx in H1. lia.
  - (* a<>x *)
    destruct (Pos.eq_dec a y).
    + (* a=y *)
      subst a. intro. subst y'. rewrite M.gss in H1. inv H1.
      rewrite M.gso in H0; auto. apply local_variable_mapping_gt_idx in H0. lia.
    + (* a<>y *)
      rewrite M.gso in H0; auto.
      rewrite M.gso in H1; auto.
      clear n n0.
      eapply IHl; eassumption.
Qed.

End Vars.


Section LambdaANF.

(* some of the following taken from C backend *)

Inductive dsubval_v: LambdaANF.term.val -> LambdaANF.term.val -> Prop :=
| dsubval_constr: forall v vs c,
  List.In v vs ->
  dsubval_v v (Vconstr c vs)
| dsubval_fun : forall x fds rho f,
  name_in_fundefs fds x ->
    dsubval_v (Vfun rho fds x) (Vfun rho fds f).

Definition subval_v := clos_trans _ dsubval_v.
Definition subval_or_eq := clos_refl_trans _ dsubval_v.

Lemma t_then_rt:
  forall A R (v v':A),
  clos_trans _ R v v'  ->
  clos_refl_trans _ R v v'.
Proof.
  intros. induction H.
  apply rt_step. auto.
  eapply rt_trans; eauto.
Qed.

Lemma rt_then_t_or_eq:
  forall A R (v v':A),
    clos_refl_trans _ R v v' ->
    v = v' \/ clos_trans _ R v v'.
Proof.
  intros. induction H.
  right. apply t_step; auto.
  left; auto.
  inv IHclos_refl_trans1; inv IHclos_refl_trans2.
  left; auto.
  right; auto.
  right; auto. right.
  eapply t_trans; eauto.
Qed.

Lemma dsubterm_case_cons:
  forall v l e',
    dsubterm_e e' (Ecase v l) ->
  forall a, dsubterm_e e' (Ecase v (a:: l)).
Proof.
  intros. inv H. econstructor.
  right; eauto.
Qed.

Lemma subterm_case:
forall v l e',
  subterm_e e' (Ecase v l) ->
  forall a, subterm_e e' (Ecase v (a:: l)).
Proof.
  intros. remember (Ecase v l) as y.
  generalize dependent v. revert l. induction H.
  - intros. subst. constructor.
    eapply dsubterm_case_cons; eauto.
  - intros. apply IHclos_trans2 in Heqy.
    now eapply t_trans.
Qed.

Lemma subval_fun: forall v rho fl x,
    name_in_fundefs fl x ->
        subval_or_eq v (Vfun rho fl x) ->
        exists l, v = Vfun rho fl l /\ name_in_fundefs fl l.
Proof.
  intros. apply rt_then_t_or_eq in H0.
  inv H0.
  exists x; auto.
  remember (Vfun rho fl x) as y.
  assert (exists x, y = Vfun rho fl x /\ name_in_fundefs fl x ) by eauto.
  clear H. clear Heqy. clear x.
  induction H1.  destructAll. subst. inv H. eauto.
  destructAll.
  assert (exists x, Vfun rho fl x0 = Vfun rho fl x /\ name_in_fundefs fl x) by eauto.
  apply IHclos_trans2 in H. apply IHclos_trans1 in H. auto.
Qed.

Lemma subval_or_eq_constr:
forall v v' vs c,
  subval_or_eq v v' ->
  List.In v' vs ->
  subval_or_eq v (Vconstr c vs).
Proof.
  intros.
  eapply rt_trans; eauto.
  apply rt_step. constructor; auto.
Qed.

Lemma subval_v_constr:
  forall v vs t,
  subval_v v (Vconstr t vs) ->
  exists v',
    subval_or_eq v v' /\ List.In v' vs.
Proof.
  intros.
  remember (Vconstr t vs) as v'. revert t vs Heqv'.
  induction H; intros; subst.
  - inv H. exists x. split.
    apply rt_refl. apply H2.
  -  specialize (IHclos_trans2 t vs Logic.eq_refl).
     destruct IHclos_trans2.
     exists x0. destruct H1. split.
     apply t_then_rt in H.
     eapply rt_trans; eauto.
     auto.
Qed.

Lemma subval_or_eq_fun:
  forall rho' fds f vs t,
  subval_or_eq (Vfun rho' fds f) (Vconstr t vs) ->
  exists v',
    subval_or_eq (Vfun rho' fds f) v' /\ List.In v' vs.
Proof.
  intros.
  apply rt_then_t_or_eq in H. destruct H.
  inv H.
  eapply subval_v_constr; eauto.
Qed.

Lemma subval_or_eq_fun_not_prim :
 forall v p,
  (forall p', v <> Vprim p') ->
  ~ subval_or_eq v (Vprim p).
Proof.
  intros ? ? HnotPrim Hcontra.
  remember (Vprim p) as v'.
  generalize dependent p.
  apply clos_rt_rt1n in Hcontra. induction Hcontra; intros; subst.
  now specialize HnotPrim with p.
  eapply IHHcontra; eauto.
  intros p' Hcontra'. subst. inv H.
Qed.


Lemma dsubterm_fds_e_find_def : forall (fds : fundefs) (e : exp) (eAny : exp),
  NoDup (collect_function_vars (Efun fds eAny)) ->
  dsubterm_fds_e e fds ->
  exists f ys t, find_def f fds = Some (t, ys, e).
Proof.
  induction fds; intros. 2: inv H0.
  inv H0. { exists v, l, f. cbn. now destruct (M.elt_eq v v). }
  eapply IHfds in H3. destruct H3 as [f' [ys' [t' H']]].
  assert (f' <> v). { intro. subst.
    assert (find_def v fds <> None). { now apply notNone_Some. }
    eapply find_def_in_collect_function_vars in H0.
    now inv H. } exists f'.
  cbn. now destruct (M.elt_eq f' v).
  now inv H.
  Unshelve. all: assumption.
Qed.

Lemma set_lists_In : forall {A} x xs (v:A) vs rho rho' ,
  In x xs ->
  M.get x rho' = Some v ->
  set_lists xs vs rho = Some rho' ->
  List.In v vs.
Proof.
  induction xs; intros.
  - inv H.
  - destruct vs. simpl in H1; inv H1. simpl in H1.
    destruct (set_lists xs vs rho) eqn:Hsl; inv H1.
    destruct (var_dec x a).
    + subst.
      rewrite M.gss in H0. inv H0. constructor; reflexivity.
    + rewrite M.gso in H0=>//.
      constructor 2.
      inv H. exfalso; apply n; reflexivity.
      eapply IHxs; eauto.
Qed.


(* a bit stronger than set_lists_In *)
Lemma set_lists_nth_error {A} : forall xs (vs : list A) rho rho' x v,
  In x xs ->
  M.get x rho' = Some v ->
  set_lists xs vs rho = Some rho' ->
  exists k, nth_error vs k = Some v /\ nth_error xs k = Some x.
Proof.
  induction xs; intros.
  - inv H.
  - destruct H.
    + (* a=v *)
      subst a. destruct vs. inv H1. cbn in H1.
      destruct (set_lists xs vs rho) eqn:Heqn; inv H1.
      rewrite M.gss in H0. inv H0. exists 0. now cbn.
    + (* a<>v *)
      destruct vs. inv H1. cbn in H1.
      destruct (set_lists xs vs rho) eqn:Heqn; inv H1.
      destruct (var_dec a x).
      * subst. rewrite M.gss in H0; inv H0. exists 0; now cbn.
      * rewrite M.gso in H0; auto.
        destruct (IHxs _ _ _ _ _ H H0 Heqn ) as [k [Hk1 Hk2]]. exists (S k). now cbn.
Qed.


Lemma def_funs_find_def : forall fds fds' rho f,
  find_def f fds <> None ->
    (def_funs fds' fds rho rho) ! f = Some (Vfun rho fds' f).
Proof.
  induction fds; intros; last contradiction.
  cbn in H. destruct (M.elt_eq f0 v).
  (* f0 = v *) subst. cbn. now rewrite M.gss.
  (* f0 <> v *) cbn. now rewrite M.gso.
Qed.

Lemma def_funs_not_find_def : forall fds fds' rho f,
  find_def f fds = None ->
    (def_funs fds' fds rho rho) ! f = rho ! f.
Proof.
  induction fds; intros ? ? ? H; auto.
  cbn in H. destruct (M.elt_eq f0 v).
  (* f0 = v *) inv H.
  (* f0 <> v *) cbn. now rewrite M.gso.
Qed.

End LambdaANF.


Section ConstrEnv.

Lemma constr_size_ge_32 {cenv} : forall t constr_size arity,
  get_ctor_size cenv t = Ret constr_size ->
  get_ctor_arity cenv t = Ret arity ->
  arity > 0 ->
  (constr_size >= 32)%N.
Proof.
  intros ??? Hsize Harr ?.
  unfold get_ctor_size in Hsize.
  rewrite Harr in Hsize. cbn in Hsize.
  destruct (arity=?0) eqn:Ha; inv Hsize; lia.
Qed.

Lemma constr_size_0 {cenv} : forall t constr_size,
  get_ctor_size cenv t = Ret constr_size ->
  get_ctor_arity cenv t = Ret 0 ->
  (constr_size = 0)%N.
Proof.
  intros ?? Hsize Harr.
  unfold get_ctor_size in Hsize.
  rewrite Harr in Hsize. cbn in Hsize.
  now inv Hsize.
Qed.

Lemma ctor_ord_restricted {cenv} : forall y cl t e ord,
  expression_restricted cenv (Ecase y cl) ->
  In (t, e) cl ->
  get_ctor_ord cenv t = Ret ord ->
  (-1 < Z.of_N ord < Wasm_int.Int32.half_modulus)%Z.
Proof.
  intros ????? Hr Hin Hord. inv Hr.
  rewrite Forall_forall in H1. apply H1 in Hin.
  destruct Hin as [Hr' _].
  simpl_modulus. cbn. cbn in Hr'.
  unfold ctor_ordinal_restricted in Hr'.
  apply Hr' in Hord. simpl_modulus_in Hord. destruct ord; lia.
Qed.

Lemma cases_same_ind_tag {cenv} : forall cl t t' e' cinfo cinfo',
  caseConsistent cenv cl t ->
  findtag cl t' = Some e' ->
  M.get t cenv = Some cinfo ->
  M.get t' cenv = Some cinfo' ->
  ctor_ind_tag cinfo = ctor_ind_tag cinfo'.
Proof.
  induction cl=>//; intros.
  inv H. inv H0.
  now destruct (M.elt_eq _ _).
Qed.

Lemma nullary_ctor_ords_in_case_disjoint {cenv} : forall cl t t' e e' ord ord',
  cenv_restricted cenv ->
  caseConsistent cenv cl t ->
  t <> t' ->
  findtag cl t = Some e ->
  findtag cl t' = Some e' ->
  get_ctor_arity cenv t = Ret 0 ->
  get_ctor_arity cenv t' = Ret 0 ->
  get_ctor_ord cenv t = Ret ord ->
  get_ctor_ord cenv t' = Ret ord' ->
  ord <> ord'.
Proof.
  intros ???????????????? <-.
  unfold cenv_restricted, get_ctor_ord, get_ctor_arity in *.
  destruct (M.get t cenv) eqn:Ht=>//.
  destruct (M.get t' cenv) eqn:Ht'=>//.
  destruct c, c0.
  injection H6 as <-. injection H7 as <-.
  assert (ctor_arity = 0%N). { injection H4. lia. } subst ctor_arity.
  assert (ctor_arity0 = 0%N). { injection H5. lia. } subst ctor_arity0.
  have H' := H t _ _ _ 0%N _ Ht t' H1.
  have H'' := @Logic.eq_refl _ 0%N. apply H' in H''. clear H'.
  have I := cases_same_ind_tag cl t t' e' _ _ H0 H3 Ht Ht'.
  cbn in I. subst. eauto.
Qed.

Lemma nonnullary_ctor_ords_in_case_disjoint {cenv} : forall cl t t' e e' a a' ord ord',
  cenv_restricted cenv ->
  caseConsistent cenv cl t ->
  t <> t' ->
  findtag cl t = Some e ->
  findtag cl t' = Some e' ->
  get_ctor_arity cenv t = Ret a ->
  get_ctor_arity cenv t' = Ret a' ->
  0 < a ->
  0 < a' ->
  get_ctor_ord cenv t = Ret ord ->
  get_ctor_ord cenv t' = Ret ord' ->
  ord <> ord'.
Proof.
  intros.
  unfold cenv_restricted, get_ctor_ord, get_ctor_arity in *.
  destruct (M.get t cenv) eqn:Ht=>//.
  destruct (M.get t' cenv) eqn:Ht'=>//.
  destruct c, c0.
  assert (ctor_arity = N.of_nat a). { inv H4. lia. } subst ctor_arity.
  assert (ctor_ordinal = ord). { inv H8. lia. } subst ctor_ordinal.
  have H' := H t _ _ _ (N.of_nat a) ord Ht t' H1.
  destruct H' as [_ H'].
  assert (H'' : (0 < N.of_nat a)%N) by lia.
  apply H' in H''. clear H'.
  injection H9 as <-.
  assert (ctor_arity0 = N.of_nat a'). { inv H5. lia. } subst ctor_arity0.
  have I := cases_same_ind_tag cl t t' e' _ _ H0 H3 Ht Ht'. cbn in I.
  intro Hcontra. subst. eauto.
Qed.

Lemma correct_cenv_of_exp_get_ctor_arity {cenv} : forall v t ys e,
  correct_cenv_of_exp cenv (Econstr v t ys e) ->
  get_ctor_arity cenv t = Ret (length ys).
Proof.
  intros.
  apply Forall_constructors_in_constr in H.
  unfold get_ctor_arity.
  destruct (cenv ! t)=>//.
  now destruct c.
Qed.


End ConstrEnv.


Section Wasm.
Import Nnat Znat.

Context `{ho : host}.

Lemma length_serialise_num_i32 : forall v, length (serialise_num (VAL_int32 v)) = 4.
Proof. auto. Qed.

Lemma length_serialise_num_i64 : forall v, length (serialise_num (VAL_int64 v)) = 8.
Proof. auto. Qed.

Lemma and_1_odd : forall n,
  (-1 < Z.of_nat (N.to_nat (2 * n + 1)) < Wasm_int.Int32.modulus)%Z ->
  Wasm_int.Int32.iand (Wasm_int.Int32.repr (Z.of_N (2 * n + 1))) (Wasm_int.Int32.repr 1) = Wasm_int.Int32.one.
Proof.
  intros.
  unfold Wasm_int.Int32.iand, Wasm_int.Int32.and. cbn.
  destruct n. cbn. reflexivity.
  rewrite Wasm_int.Int32.Z_mod_modulus_id; last lia. reflexivity.
Qed.

Lemma and_1_even : forall n,
  (-1 < Z.of_N (2 * n) < Wasm_int.Int32.modulus)%Z ->
  Wasm_int.Int32.iand (Wasm_int.Int32.repr (Z.of_N (2 * n))) (Wasm_int.Int32.repr 1) = Wasm_int.Int32.zero.
Proof.
  intros ? H.
  unfold Wasm_int.Int32.iand, Wasm_int.Int32.and.
  - destruct n. now cbn.
  - remember (Z.of_N _) as fd. cbn.
    now rewrite Wasm_int.Int32.Z_mod_modulus_id; subst.
Qed.


(* easier to use with $VN *)
Lemma r_local_get' : forall f v j s hs,
  lookup_N (f_locs f) j = Some (VAL_num v) ->
  reduce hs s f [:: AI_basic (BI_local_get j)] hs s f [:: $VN v].
Proof.
  intros.
  by apply r_local_get with (v:=VAL_num v).
Qed.

Lemma r_local_set' : forall f f' i v s vd hs,
  f_inst f' = f_inst f ->
  ssrnat.leq (S (N.to_nat i)) (Datatypes.length (f_locs f)) ->
  f_locs f' = set_nth vd (f_locs f) (N.to_nat i) (VAL_num v) ->
  reduce hs s f [:: $VN v; AI_basic (BI_local_set i)] hs s f' [::].
Proof.
  intros.
  now eapply r_local_set with (v:=VAL_num v).
Qed.

Lemma r_global_get' : forall s f i v hs,
  sglob_val s (f_inst f) i = Some (VAL_num v) ->
  reduce hs s f [:: AI_basic (BI_global_get i)] hs s f [:: $VN v].
Proof.
  intros.
  now eapply r_global_get with (v:=VAL_num v).
Qed.

Lemma r_global_set' : forall s f i v s' hs,
  supdate_glob s (f_inst f) i (VAL_num v) = Some s' ->
  reduce hs s f [:: $VN v; AI_basic (BI_global_set i)] hs s' f [::].
Proof.
  intros.
  now eapply r_global_set with (v:=VAL_num v).
Qed.


Lemma store_length (m m': meminst) (n: N) (off: static_offset) (bs: bytes) :
  store m n off bs (length bs) = Some m' ->
  mem_length m = mem_length m'.
Proof.
  unfold store, write_bytes_meminst. intros.
  destruct ((n + off + N.of_nat (Datatypes.length bs) <=? mem_length m)%N) eqn:Hlen=>//.
  destruct (write_bytes _ _ _) eqn:Hb=>//. inv H.
  apply write_bytes_preserve_length in Hb.
  unfold mem_length.
  now rewrite Hb.
Qed.

Lemma enough_space_to_store m k off bs :
  (k + off + N.of_nat (length bs) <= mem_length m)%N ->
  store m k off bs (length bs) <> None.
Proof.
  intros. unfold store, write_bytes_meminst, bytes_takefill.
  apply N.leb_le in H. rewrite H.
  intro Hcontra.
  destruct (write_bytes _ _ _) eqn:Hby=>//. clear Hcontra.
  destruct (length bs <? length bs) eqn:Hcontra; first lia. clear Hcontra.
  generalize dependent k. revert off m.
  induction bs; intros=>//.
  cbn in Hby, H.
  destruct (mem_update _ _ _) eqn:Hupd.
  2:{ eapply mem_update_ib; eauto. unfold mem_length in H. lia. }
  assert ((k + (N.succ off) + N.of_nat (Datatypes.length bs) <=? mem_length m)%N = true)
      as Hlen by lia.
  clear H.
  eapply (IHbs _ (Build_meminst (meminst_type m) m0)); last eassumption.
  apply mem_update_length in Hupd.
  unfold mem_length in *. rewrite Hupd. lia.
Qed.

Definition load_i32 m addr : option value_num :=
  match load m addr 0%N 4 with (* offset: 0, 4 bytes *)
  | None => None
  | Some bs => Some (wasm_deserialise bs T_i32)
  end.

Definition store_i32 mem addr (v : value_num) : option meminst :=
  store mem addr 0%N (serialise_num v) 4.


Definition load_i64 m addr : option value_num :=
  match load m addr 0%N 8 with (* offset: 0, 4 bytes *)
  | None => None
  | Some bs => Some (wasm_deserialise bs T_i64)
  end.

Definition store_i64 mem addr (v : value_num) : option meminst :=
    store mem addr 0%N (serialise_num v) 8.


Definition tag_to_i32 (t : ctor_tag) :=
  Wasm_int.Int32.repr (BinInt.Z.of_nat (Pos.to_nat t)).

Inductive wasm_value :=
  | Val_unboxed : u32 -> wasm_value
  | Val_ptr     : u32 -> wasm_value
  | Val_funidx  : u32 -> wasm_value.

Definition wasm_value_to_u32 (v : wasm_value) :=
  match v with
  | Val_unboxed i => i
  | Val_ptr i => i
  | Val_funidx i => i
  end.

Definition wasm_value_to_i32 (v : wasm_value) :=
  Wasm_int.Int32.repr (BinInt.Z.of_N (wasm_value_to_u32 v)).

(* memory TODO cleanup/automate *)


Lemma write_bytes_read_bytes_i32 : forall m addr v m0,
  length v = 4 ->
  write_bytes (meminst_data m) addr (bytes_takefill #00 4 v) = Some m0 ->
  read_bytes {| meminst_type := meminst_type m; meminst_data := m0 |} addr 4 = Some v.
Proof.
  intros. do 5 destruct v=>//. cbn in H0.
  rewrite -!N.add_assoc in H0. cbn in H0.
  destruct (mem_update addr _ _) eqn:Hu1=>//.
  destruct (mem_update (addr + 1) _ _) eqn:Hu2=>//.
  destruct (mem_update (addr + 2) _ _) eqn:Hu3=>//.
  destruct (mem_update (addr + 3) _ _) eqn:Hu4=>//. inv H0.
  unfold read_bytes, those. cbn.
  replace (mem_lookup (addr + 3) m0) with (Some b2).
  2:{ now apply mem_update_lookup in Hu4. }

  replace (mem_lookup (addr + 2) m0) with (Some b1).
  2:{ apply mem_update_lookup in Hu3.
      erewrite mem_update_lookup_ne; eauto. lia. }

  replace (mem_lookup (addr + 1) m0) with (Some b0).
  2:{ apply mem_update_lookup_ne with (i:=(addr + 1)%N) in Hu4, Hu3; try lia.
      rewrite Hu4 Hu3. now erewrite mem_update_lookup. }

  replace (addr + 0)%N with addr by lia.
  replace (mem_lookup addr m0) with (Some b).
  2: { apply mem_update_lookup_ne with (i:=addr) in Hu4, Hu3, Hu2; try lia.
       rewrite Hu4 Hu3 Hu2. now erewrite mem_update_lookup. }
  reflexivity.
Qed.

Lemma store_load_i32 : forall m m' addr v,
  length v = 4 ->
  store m addr 0%N v 4 = Some m' ->
  load_i32 m' addr = Some (wasm_deserialise v T_i32).
Proof.
  unfold load_i32, store, write_bytes_meminst. intros.
  destruct (addr + 0 + N.of_nat 4 <=? mem_length m)%N eqn:Hlen=>//.
  destruct (write_bytes _ _ _) eqn:Hby=>//. inv H0.
  unfold load. cbn.
  have Hlen' := (write_bytes_preserve_length Hby). unfold mem_length in *. cbn.
  destruct (addr + 4 <=? memory.mem_length m0)%N eqn:Hlen''; try lia.
  cbn.
  now erewrite write_bytes_read_bytes_i32.
Qed.


Lemma write_bytes_read_bytes_i64 : forall m addr v m0,
  length v = 8 ->
  write_bytes (meminst_data m) addr (bytes_takefill #00 8 v) = Some m0 ->
  read_bytes {| meminst_type := meminst_type m; meminst_data := m0 |} addr 8 = Some v.
Proof.
  intros. do 9 destruct v=>//. cbn in H0.
  rewrite -!N.add_assoc in H0. cbn in H0.
  destruct (mem_update addr _ _) eqn:Hu1=>//.
  destruct (mem_update (addr + 1) _ _) eqn:Hu2=>//.
  destruct (mem_update (addr + 2) _ _) eqn:Hu3=>//.
  destruct (mem_update (addr + 3) _ _) eqn:Hu4=>//.
  destruct (mem_update (addr + 4) _ _) eqn:Hu5=>//.
  destruct (mem_update (addr + 5) _ _) eqn:Hu6=>//.
  destruct (mem_update (addr + 6) _ _) eqn:Hu7=>//.
  destruct (mem_update (addr + 7) _ _) eqn:Hu8=>//. inv H0.
  unfold read_bytes, those. cbn.
  replace (mem_lookup (addr + 7) m0) with (Some b6).
  2:{ now eapply mem_update_lookup in Hu8. }

  replace (mem_lookup (addr + 6) m0) with (Some b5).
  2:{ apply mem_update_lookup_ne with (i:=(addr + 6)%N) in Hu8.
      rewrite Hu8. now erewrite mem_update_lookup. lia. }

  replace (mem_lookup (addr + 5) m0) with (Some b4).
  2:{ apply mem_update_lookup_ne with (i:=(addr + 5)%N) in Hu8, Hu7; try lia.
      rewrite Hu8 Hu7. now erewrite mem_update_lookup. }

  replace (mem_lookup (addr + 4) m0) with (Some b3).
  2:{ apply mem_update_lookup_ne with (i:=(addr + 4)%N) in Hu8, Hu7, Hu6; try lia.
      rewrite Hu8 Hu7 Hu6. now erewrite mem_update_lookup. }

  replace (mem_lookup (addr + 3) m0) with (Some b2).
  2:{ apply mem_update_lookup_ne with (i:=(addr + 3)%N) in Hu8, Hu7, Hu6, Hu5; try lia.
      rewrite Hu8 Hu7 Hu6 Hu5. now erewrite mem_update_lookup. }

  replace (mem_lookup (addr + 2) m0) with (Some b1).
  2:{ apply mem_update_lookup_ne with (i:=(addr + 2)%N) in Hu8, Hu7, Hu6, Hu5, Hu4;
        try lia.
      rewrite Hu8 Hu7 Hu6 Hu5 Hu4. now erewrite mem_update_lookup. }

  replace (mem_lookup (addr + 1) m0) with (Some b0).
  2:{ apply mem_update_lookup_ne with (i:=(addr + 1)%N) in Hu8, Hu7, Hu6, Hu5, Hu4, Hu3; try lia.
      rewrite Hu8 Hu7 Hu6 Hu5 Hu4 Hu3. now erewrite mem_update_lookup. }

  replace (addr + 0)%N with addr by lia.
  replace (mem_lookup addr m0) with (Some b).
  2: { apply mem_update_lookup_ne with (i:=addr) in Hu8, Hu7, Hu6, Hu5, Hu4, Hu3, Hu2; try lia.
       rewrite Hu8 Hu7 Hu6 Hu5 Hu4 Hu3 Hu2. now erewrite mem_update_lookup. }
  reflexivity.
Qed.

Lemma store_load_i64 : forall m m' addr v,
  length v = 8 ->
  store m addr 0%N v 8 = Some m' ->
  load_i64 m' addr = Some (wasm_deserialise v T_i64).
Proof.
  unfold load_i64, store, write_bytes_meminst. intros.
  destruct (addr + 0 + N.of_nat 8 <=? mem_length m)%N eqn:Hlen=>//.
  destruct (write_bytes _ _ _) eqn:Hby=>//. inv H0.
  unfold load. cbn.
  have Hlen' := (write_bytes_preserve_length Hby). unfold mem_length in *. cbn.
  destruct (addr + 8 <=? memory.mem_length m0)%N eqn:Hlen''; try lia.
  now erewrite write_bytes_read_bytes_i64.
Qed.

Lemma enough_space_to_load m k :
  (k + 4 <= mem_length m)%N ->
  exists v, load_i32 m k = Some v.
Proof.
  unfold load_i32, load. intros. cbn.
  apply N.leb_le in H. rewrite H.
  unfold read_bytes, those. cbn.
  apply N.leb_le in H. unfold mem_length in H.
  destruct (mem_lookup (k + 0 + 0) (meminst_data m)) eqn:Hc.
  destruct (mem_lookup (k + 0 + 1) (meminst_data m)) eqn:Hc0.
  destruct (mem_lookup (k + 0 + 2) (meminst_data m)) eqn:Hc1.
  destruct (mem_lookup (k + 0 + 3) (meminst_data m)) eqn:Hc2; eauto.
  all: exfalso; eapply mem_lookup_ib; eauto; lia.
Qed.

Lemma enough_space_to_load_i64 m k :
  (k + 8 <= mem_length m)%N ->
  exists v, load_i64 m k = Some v.
Proof.
  unfold load_i64, load. intros. cbn.
  apply N.leb_le in H. rewrite H.
  unfold read_bytes, those. cbn.
  apply N.leb_le in H. unfold mem_length in H.
  destruct (mem_lookup (k + 0 + 0) (meminst_data m)) eqn:Hc.
  destruct (mem_lookup (k + 0 + 1) (meminst_data m)) eqn:Hc0.
  destruct (mem_lookup (k + 0 + 2) (meminst_data m)) eqn:Hc1.
  destruct (mem_lookup (k + 0 + 3) (meminst_data m)) eqn:Hc2.
  destruct (mem_lookup (k + 0 + 4) (meminst_data m)) eqn:Hc3.
  destruct (mem_lookup (k + 0 + 5) (meminst_data m)) eqn:Hc4.
  destruct (mem_lookup (k + 0 + 6) (meminst_data m)) eqn:Hc5.
  destruct (mem_lookup (k + 0 + 7) (meminst_data m)) eqn:Hc6; eauto.
  all: exfalso; eapply mem_lookup_ib; eauto; lia.
Qed.

Lemma store_lim_max : forall (m m' : meminst) v x l,
   store m x 0%N v l = Some m' ->
   m.(meminst_type).(lim_max) = m'.(meminst_type).(lim_max).
Proof.
  intros.
  unfold store in H.
  destruct ((x + 0 + N.of_nat l <=? mem_length m)%N). 2 : inv H.
  unfold write_bytes_meminst in H.
  by destruct (write_bytes _ _ _); inv H.
Qed.

Lemma mem_grow_length : forall (m m' : meminst) sgrow,
  mem_grow m sgrow = Some m' ->
  mem_length m' = ((sgrow * 65536) + mem_length m)%N.
Proof.
  unfold mem_grow. intros.
  destruct ((mem_size m + sgrow <=? mem_limit_bound)%N) eqn:Hsize=>//.
  destruct (memory.mem_grow (sgrow * page_size) (meminst_data m)) eqn:Hgrow=>//.
  apply mem_grow_length in Hgrow. unfold mem_length.
  destruct (lim_max (meminst_type m)) eqn:Htype=>//.
  - destruct (mem_size m + sgrow <=? u)%N =>//. inv H.
    rewrite Hgrow. unfold page_size. lia.
  - inv H. rewrite Hgrow. unfold page_size. lia.
Qed.

Lemma mem_grow_mem_size : forall (m m' : meminst) sgrow,
  mem_grow m sgrow = Some m' ->
  mem_size m' = (sgrow + mem_size m)%N.
Proof.
  intros. apply mem_grow_length in H.
  unfold mem_size. rewrite H.
  unfold page_size. lia.
Qed.

Lemma mem_grow_lim_max : forall n m m' bytes,
  mem_grow m bytes = Some m' ->
  m.(meminst_type).(lim_max) = Some n ->
  m'.(meminst_type).(lim_max) = Some n.
Proof.
  intros. unfold mem_grow in H.
  destruct ((mem_size m + bytes <=? mem_limit_bound)%N)=>//. cbn in H.
  destruct (memory.mem_grow (bytes * page_size) (meminst_data m))=>//.
  destruct (lim_max (meminst_type m))=>//.
  destruct ((mem_size m + bytes <=? u)%N)=>//. inv H0. inv H.
  reflexivity.
Qed.

Lemma smem_grow_funcs : forall sr fr bytes sr' size,
  smem_grow sr (f_inst fr) bytes = Some (sr', size) ->
  s_funcs sr = s_funcs sr'.
Proof.
  intros. unfold smem_grow in H.
  destruct (lookup_N (inst_mems (f_inst fr)) 0)=>//.
  destruct (lookup_N (s_mems sr) m)=>//.
  destruct (mem_grow m0 bytes)=>//. inv H. reflexivity.
Qed.

Lemma smem_grow_sglob_val : forall sr fr bytes sr' size var,
  smem_grow sr (f_inst fr) bytes = Some (sr', size) ->
  sglob_val sr (f_inst fr) var = sglob_val sr' (f_inst fr) var.
Proof.
  intros. unfold smem_grow in H.
  destruct (lookup_N (inst_mems (f_inst fr)) 0)=>//.
  destruct (lookup_N (s_mems sr) m)=>//.
  destruct (mem_grow m0 bytes)=>//. inv H. reflexivity.
Qed.

Lemma mem_grow_load : forall a m m' maxlim,
  (m.(meminst_type).(lim_max) = Some maxlim)%N ->
  mem_grow m 1 = Some m' ->
  (a + 8 <= mem_length m)%N ->
  load_i32 m a = load_i32 m' a /\ load_i64 m a = load_i64 m' a.
Proof.
  unfold load_i32, load_i64, load, mem_grow. intros.
  destruct ((mem_size m + 1 <=? mem_limit_bound)%N) eqn:Hbnd=>//.
  destruct (memory.mem_grow (1 * page_size) (meminst_data m)) eqn:Hgrow=>//.
  destruct (lim_max (meminst_type m)) eqn:Hlim=>//.
  destruct (mem_size m + 1 <=? u)%N eqn:Hsize=>//.
  split.
  - (* i32 *)
    destruct (a + (0 + 4) <=? mem_length m)%N eqn:Hb; try lia.
    destruct (a + (0 + 4) <=? mem_length m')%N eqn:Hb'.
    2:{ apply memory.mem_grow_length in Hgrow. inv H0. unfold mem_length in Hb', Hb.
        cbn in Hb', Hgrow. rewrite Hgrow in Hb'. lia. }
    inv H0.
    unfold read_bytes, those. cbn. unfold mem_length in Hb.
    erewrite <- memory.mem_grow_lookup; eauto; try lia.
      destruct (mem_lookup (a + 0 + 0) m0)=>//.
    erewrite <- memory.mem_grow_lookup; eauto; try lia.
      destruct (mem_lookup (a + 0 + 1) m0)=>//.
    erewrite <- memory.mem_grow_lookup; eauto; try lia.
      destruct (mem_lookup (a + 0 + 2) m0)=>//.
    erewrite <- memory.mem_grow_lookup; eauto; lia.
  - (* i64 *)
    destruct (a + (0 + 8) <=? mem_length m)%N eqn:Hb; try lia.
    destruct (a + (0 + 8) <=? mem_length m')%N eqn:Hb'.
    2:{ apply memory.mem_grow_length in Hgrow. inv H0. unfold mem_length in Hb', Hb.
        cbn in Hb', Hgrow. rewrite Hgrow in Hb'. lia. }
    inv H0.
    unfold read_bytes, those. cbn. unfold mem_length in Hb.
    erewrite <- memory.mem_grow_lookup; eauto; try lia.
      destruct (mem_lookup (a + 0 + 0) m0)=>//.
    erewrite <- memory.mem_grow_lookup; eauto; try lia.
      destruct (mem_lookup (a + 0 + 1) m0)=>//.
    erewrite <- memory.mem_grow_lookup; eauto; try lia.
      destruct (mem_lookup (a + 0 + 2) m0)=>//.
    erewrite <- memory.mem_grow_lookup; eauto; try lia.
      destruct (mem_lookup (a + 0 + 3) m0)=>//.
    erewrite <- memory.mem_grow_lookup; eauto; try lia.
      destruct (mem_lookup (a + 0 + 4) m0)=>//.
    erewrite <- memory.mem_grow_lookup; eauto; try lia.
      destruct (mem_lookup (a + 0 + 5) m0)=>//.
    erewrite <- memory.mem_grow_lookup; eauto; try lia.
      destruct (mem_lookup (a + 0 + 6) m0)=>//.
    erewrite <- memory.mem_grow_lookup; eauto; lia.
Qed.

Lemma mem_length_upper_bound : forall m,
  (mem_size m <= max_mem_pages)%N ->
  (mem_length m <= (max_mem_pages + 1) * page_size)%N.
Proof.
  intros.
  unfold mem_size, page_size in H. unfold page_size. cbn in *.
  remember (mem_length m) as n. clear Heqn m.
  assert (Z.of_N n / 65536 <= Z.of_N max_mem_pages)%Z as Hn by lia. clear H.
  unfold max_mem_pages in Hn.
  assert (Hs: (65536 > 0)%Z) by lia.
  destruct (Zdiv_eucl_exist Hs (Z.of_N n)) as [[z z0] [H1 H2]].
  rewrite H1 in Hn.
  rewrite Z.add_comm in Hn.
  rewrite Z.mul_comm in Hn.
  rewrite Z.div_add in Hn; lia.
Qed.


Lemma load_store_load_i32 : forall m m' a1 a2 v w,
  length w = 4 ->
  (a1 + 4 <= a2)%N ->
  load_i32 m a1 = Some v ->
  store m a2 0%N w 4 = Some m' ->
  load_i32 m' a1 = Some v.
Proof.
  unfold store, load_i32, load, write_bytes_meminst. intros.
  do 5 destruct w=>//.
  destruct (a2 + 0 + N.of_nat 4 <=? mem_length m)%N eqn:Hlen=>//.
  destruct (a1 + (0 + 4) <=? mem_length m)%N eqn:Hlen'=>//.
  destruct (read_bytes _ _ _) eqn:Hread=>//.
  destruct (write_bytes _ _ _) eqn:Hwrite=>//. inv H2. inv H1.
  have Hlen'' := write_bytes_preserve_length Hwrite.
  unfold mem_length. cbn. rewrite -Hlen'' Hlen'.
  unfold read_bytes, those in *. cbn. rewrite -!N.add_assoc. cbn.
  cbn in Hread. rewrite -!N.add_assoc in Hread. cbn in Hread.
  destruct (mem_lookup (a1 + 0) _) eqn:Hl0=>//.
  destruct (mem_lookup (a1 + 1) _) eqn:Hl1=>//.
  destruct (mem_lookup (a1 + 2) _) eqn:Hl2=>//.
  destruct (mem_lookup (a1 + 3) _) eqn:Hl3=>//. inv Hread.

  cbn in Hwrite. rewrite -!N.add_assoc in Hwrite. cbn in Hwrite.
  destruct (mem_update (a2 + 0) _ _) eqn:Hu0=>//.
  destruct (mem_update (a2 + 1) _ _) eqn:Hu1=>//.
  destruct (mem_update (a2 + 2) _ _) eqn:Hu2=>//.
  destruct (mem_update (a2 + 3) _ _) eqn:Hu3=>//. inv Hwrite.

  replace (mem_lookup (a1 + 0) m0) with (Some b4).
  2:{ apply mem_update_lookup_ne with (i:=(a1+0)%N) in Hu0, Hu1, Hu2, Hu3; try lia. congruence. }

  replace (mem_lookup (a1 + 1) m0) with (Some b5).
  2:{ apply mem_update_lookup_ne with (i:=(a1+1)%N) in Hu0, Hu1, Hu2, Hu3; try lia. congruence. }

  replace (mem_lookup (a1 + 2) m0) with (Some b6).
  2:{ apply mem_update_lookup_ne with (i:=(a1+2)%N) in Hu0, Hu1, Hu2, Hu3; try lia. congruence. }

  replace (mem_lookup (a1 + 3) m0) with (Some b7).
  2:{ apply mem_update_lookup_ne with (i:=(a1+3)%N) in Hu0, Hu1, Hu2, Hu3; try lia. congruence. }

  reflexivity.
Qed.


(* TODO: The following helper lemmas may be removed in the future
   once the new memory model in WasmCert has been finalized.
   Then reduce verbosity.
*)
Lemma load_store_load_i32' : forall m m' a1 a2 v w,
  length w = 8 ->
  (a1 + 4 <= a2)%N ->
  load_i32 m a1 = Some v ->
  store m a2 0%N w 8 = Some m' ->
  load_i32 m' a1 = Some v.
Proof.
  unfold store, load_i32, load, write_bytes_meminst. intros.
  do 9 destruct w=>//.
  destruct (a2 + 0 + N.of_nat 8 <=? mem_length m)%N eqn:Hlen=>//.
  destruct (a1 + (0 + 4) <=? mem_length m)%N eqn:Hlen'=>//.
  destruct (read_bytes _ _ _) eqn:Hread=>//.
  destruct (write_bytes _ _ _) eqn:Hwrite=>//. inv H2. inv H1.
  have Hlen'' := write_bytes_preserve_length Hwrite.
  unfold mem_length. cbn. rewrite -Hlen'' Hlen'.
  unfold read_bytes, those in *. cbn. rewrite -!N.add_assoc. cbn.
  cbn in Hread. rewrite -!N.add_assoc in Hread. cbn in Hread.
  destruct (mem_lookup (a1 + 0) _) eqn:Hl0=>//.
  destruct (mem_lookup (a1 + 1) _) eqn:Hl1=>//.
  destruct (mem_lookup (a1 + 2) _) eqn:Hl2=>//.
  destruct (mem_lookup (a1 + 3) _) eqn:Hl3=>//. inv Hread.

  cbn in Hwrite. rewrite -!N.add_assoc in Hwrite. cbn in Hwrite.
  destruct (mem_update (a2 + 0) _ _) eqn:Hu0=>//.
  destruct (mem_update (a2 + 1) _ _) eqn:Hu1=>//.
  destruct (mem_update (a2 + 2) _ _) eqn:Hu2=>//.
  destruct (mem_update (a2 + 3) _ _) eqn:Hu3=>//.
  destruct (mem_update (a2 + 4) _ _) eqn:Hu4=>//.
  destruct (mem_update (a2 + 5) _ _) eqn:Hu5=>//.
  destruct (mem_update (a2 + 6) _ _) eqn:Hu6=>//.
  destruct (mem_update (a2 + 7) _ _) eqn:Hu7=>//. inv Hwrite.

  replace (mem_lookup (a1 + 0) m0) with (Some b8).
  2:{ apply mem_update_lookup_ne with (i:=(a1+0)%N) in Hu0, Hu1, Hu2, Hu3, Hu4, Hu5, Hu6, Hu7; try lia. congruence. }
  replace (mem_lookup (a1 + 1) m0) with (Some b9).
  2:{ apply mem_update_lookup_ne with (i:=(a1+1)%N) in Hu0, Hu1, Hu2, Hu3, Hu4, Hu5, Hu6, Hu7; try lia. congruence. }
  replace (mem_lookup (a1 + 2) m0) with (Some b10).
  2:{ apply mem_update_lookup_ne with (i:=(a1+2)%N) in Hu0, Hu1, Hu2, Hu3, Hu4, Hu5, Hu6, Hu7; try lia. congruence. }
  replace (mem_lookup (a1 + 3) m0) with (Some b11).
  2:{ apply mem_update_lookup_ne with (i:=(a1+3)%N) in Hu0, Hu1, Hu2, Hu3, Hu4, Hu5, Hu6, Hu7; try lia. congruence. }

  reflexivity.
Qed.


Lemma load_store_load_i64 : forall m m' a1 a2 v w,
  length w = 4 ->
  (a1 + 8 <= a2)%N ->
  load_i64 m a1 = Some v ->
  store m a2 0%N w 4 = Some m' ->
  load_i64 m' a1 = Some v.
Proof.
  unfold store, load_i32, load_i64, load, write_bytes_meminst. intros.
  do 5 destruct w=>//.
  destruct (a2 + 0 + N.of_nat 4 <=? mem_length m)%N eqn:Hlen=>//.
  destruct (a1 + (0 + 8) <=? mem_length m)%N eqn:Hlen'=>//.
  destruct (read_bytes _ _ _) eqn:Hread=>//.
  destruct (write_bytes _ _ _) eqn:Hwrite=>//. inv H2. inv H1.
  have Hlen'' := write_bytes_preserve_length Hwrite.
  unfold mem_length. cbn. rewrite -Hlen'' Hlen'.
  unfold read_bytes, those in *. cbn. rewrite -!N.add_assoc. cbn.
  cbn in Hread. rewrite -!N.add_assoc in Hread. cbn in Hread.
  destruct (mem_lookup (a1 + 0) _) eqn:Hl0=>//.
  destruct (mem_lookup (a1 + 1) _) eqn:Hl1=>//.
  destruct (mem_lookup (a1 + 2) _) eqn:Hl2=>//.
  destruct (mem_lookup (a1 + 3) _) eqn:Hl3=>//.
  destruct (mem_lookup (a1 + 4) _) eqn:Hl4=>//.
  destruct (mem_lookup (a1 + 5) _) eqn:Hl5=>//.
  destruct (mem_lookup (a1 + 6) _) eqn:Hl6=>//.
  destruct (mem_lookup (a1 + 7) _) eqn:Hl7=>//. inv Hread.

  cbn in Hwrite. rewrite -!N.add_assoc in Hwrite. cbn in Hwrite.
  destruct (mem_update (a2 + 0) _ _) eqn:Hu0=>//.
  destruct (mem_update (a2 + 1) _ _) eqn:Hu1=>//.
  destruct (mem_update (a2 + 2) _ _) eqn:Hu2=>//.
  destruct (mem_update (a2 + 3) _ _) eqn:Hu3=>//. inv Hwrite.

  replace (mem_lookup (a1 + 0) m0) with (Some b4).
  2:{ apply mem_update_lookup_ne with (i:=(a1+0)%N) in Hu0, Hu1, Hu2, Hu3; try lia. congruence. }
  replace (mem_lookup (a1 + 1) m0) with (Some b5).
  2:{ apply mem_update_lookup_ne with (i:=(a1+1)%N) in Hu0, Hu1, Hu2, Hu3; try lia. congruence. }
  replace (mem_lookup (a1 + 2) m0) with (Some b6).
  2:{ apply mem_update_lookup_ne with (i:=(a1+2)%N) in Hu0, Hu1, Hu2, Hu3; try lia. congruence. }
  replace (mem_lookup (a1 + 3) m0) with (Some b7).
  2:{ apply mem_update_lookup_ne with (i:=(a1+3)%N) in Hu0, Hu1, Hu2, Hu3; try lia. congruence. }
  replace (mem_lookup (a1 + 4) m0) with (Some b8).
  2:{ apply mem_update_lookup_ne with (i:=(a1+4)%N) in Hu0, Hu1, Hu2, Hu3; try lia. congruence. }
  replace (mem_lookup (a1 + 5) m0) with (Some b9).
  2:{ apply mem_update_lookup_ne with (i:=(a1+5)%N) in Hu0, Hu1, Hu2, Hu3; try lia. congruence. }
  replace (mem_lookup (a1 + 6) m0) with (Some b10).
  2:{ apply mem_update_lookup_ne with (i:=(a1+6)%N) in Hu0, Hu1, Hu2, Hu3; try lia. congruence. }
  replace (mem_lookup (a1 + 7) m0) with (Some b11).
  2:{ apply mem_update_lookup_ne with (i:=(a1+7)%N) in Hu0, Hu1, Hu2, Hu3; try lia. congruence. }

  reflexivity.
Qed.

Lemma load_store_load_i64' : forall m m' a1 a2 v w,
  length w = 8 ->
  (a1 + 8 <= a2)%N ->
  load_i64 m a1 = Some v ->
  store m a2 0%N w 8 = Some m' ->
  load_i64 m' a1 = Some v.
Proof.
  unfold store, load_i32, load_i64, load, write_bytes_meminst. intros.
  do 9 destruct w=>//.
  destruct (a2 + 0 + N.of_nat 8 <=? mem_length m)%N eqn:Hlen=>//.
  destruct (a1 + (0 + 8) <=? mem_length m)%N eqn:Hlen'=>//.
  destruct (read_bytes _ _ _) eqn:Hread=>//.
  destruct (write_bytes _ _ _) eqn:Hwrite=>//. inv H2. inv H1.
  have Hlen'' := write_bytes_preserve_length Hwrite.
  unfold mem_length. cbn. rewrite -Hlen'' Hlen'.
  unfold read_bytes, those in *. cbn. rewrite -!N.add_assoc. cbn.
  cbn in Hread. rewrite -!N.add_assoc in Hread. cbn in Hread.
  destruct (mem_lookup (a1 + 0) _) eqn:Hl0=>//.
  destruct (mem_lookup (a1 + 1) _) eqn:Hl1=>//.
  destruct (mem_lookup (a1 + 2) _) eqn:Hl2=>//.
  destruct (mem_lookup (a1 + 3) _) eqn:Hl3=>//.
  destruct (mem_lookup (a1 + 4) _) eqn:Hl4=>//.
  destruct (mem_lookup (a1 + 5) _) eqn:Hl5=>//.
  destruct (mem_lookup (a1 + 6) _) eqn:Hl6=>//.
  destruct (mem_lookup (a1 + 7) _) eqn:Hl7=>//. inv Hread.

  cbn in Hwrite. rewrite -!N.add_assoc in Hwrite. cbn in Hwrite.
  destruct (mem_update (a2 + 0) _ _) eqn:Hu0=>//.
  destruct (mem_update (a2 + 1) _ _) eqn:Hu1=>//.
  destruct (mem_update (a2 + 2) _ _) eqn:Hu2=>//.
  destruct (mem_update (a2 + 3) _ _) eqn:Hu3=>//.
  destruct (mem_update (a2 + 4) _ _) eqn:Hu4=>//.
  destruct (mem_update (a2 + 5) _ _) eqn:Hu5=>//.
  destruct (mem_update (a2 + 6) _ _) eqn:Hu6=>//.
  destruct (mem_update (a2 + 7) _ _) eqn:Hu7=>//. inv Hwrite.

  replace (mem_lookup (a1 + 0) m0) with (Some b8).
  2:{ apply mem_update_lookup_ne with (i:=(a1+0)%N) in Hu0, Hu1, Hu2, Hu3, Hu4, Hu5, Hu6, Hu7; try lia. congruence. }
  replace (mem_lookup (a1 + 1) m0) with (Some b9).
  2:{ apply mem_update_lookup_ne with (i:=(a1+1)%N) in Hu0, Hu1, Hu2, Hu3, Hu4, Hu5, Hu6, Hu7; try lia. congruence. }
  replace (mem_lookup (a1 + 2) m0) with (Some b10).
  2:{ apply mem_update_lookup_ne with (i:=(a1+2)%N) in Hu0, Hu1, Hu2, Hu3, Hu4, Hu5, Hu6, Hu7; try lia. congruence. }
  replace (mem_lookup (a1 + 3) m0) with (Some b11).
  2:{ apply mem_update_lookup_ne with (i:=(a1+3)%N) in Hu0, Hu1, Hu2, Hu3, Hu4, Hu5, Hu6, Hu7; try lia. congruence. }
  replace (mem_lookup (a1 + 4) m0) with (Some b12).
  2:{ apply mem_update_lookup_ne with (i:=(a1+4)%N) in Hu0, Hu1, Hu2, Hu3, Hu4, Hu5, Hu6, Hu7; try lia. congruence. }
  replace (mem_lookup (a1 + 5) m0) with (Some b13).
  2:{ apply mem_update_lookup_ne with (i:=(a1+5)%N) in Hu0, Hu1, Hu2, Hu3, Hu4, Hu5, Hu6, Hu7; try lia. congruence. }
  replace (mem_lookup (a1 + 6) m0) with (Some b14).
  2:{ apply mem_update_lookup_ne with (i:=(a1+6)%N) in Hu0, Hu1, Hu2, Hu3, Hu4, Hu5, Hu6, Hu7; try lia. congruence. }
  replace (mem_lookup (a1 + 7) m0) with (Some b15).
  2:{ apply mem_update_lookup_ne with (i:=(a1+7)%N) in Hu0, Hu1, Hu2, Hu3, Hu4, Hu5, Hu6, Hu7; try lia. congruence. }

  reflexivity.
Qed.


(* taken from iriswasm (deserialise_bits) *)
Lemma deserialise_serialise v t :
  typeof_num v == t -> wasm_deserialise (serialise_num v) t = v.
Proof.
  intros Htv.
  unfold wasm_deserialise.
  destruct t ;
    unfold serialise_num ;
    destruct v ; (try by inversion Htv).
  rewrite Memdata.decode_encode_int.
  rewrite Z.mod_small.
  by rewrite Wasm_int.Int32.repr_unsigned.
  destruct i ; simpl; replace (two_power_pos _)
    with Wasm_int.Int32.modulus ; [lia | done].
  rewrite Memdata.decode_encode_int.
  rewrite Z.mod_small.
  by rewrite Wasm_int.Int64.repr_unsigned.
  destruct i ; simpl ; replace (two_power_pos _)
    with Wasm_int.Int64.modulus ; [lia | done].
  rewrite Memdata.decode_encode_int_4.
  by rewrite Wasm_float.FloatSize32.of_to_bits.
  rewrite Memdata.decode_encode_int_8.
  by rewrite Wasm_float.FloatSize64.of_to_bits.
Qed.

(* global vars *)

Lemma update_global_get_same : forall sr sr' i val fr,
  supdate_glob sr (f_inst fr) i val = Some sr' ->
  sglob_val sr' (f_inst fr) i = Some val.
Proof.
  unfold supdate_glob, supdate_glob_s, sglob_val, sglob, sglob_ind. cbn. intros.
  destruct (lookup_N (inst_globals (f_inst fr)) i) eqn:H1. 2: inv H. cbn in H.
  destruct (lookup_N (s_globals sr) g) eqn:H2. 2: inv H. inv H. cbn.
  unfold lookup_N.
  erewrite set_nth_nth_error_same; auto. eassumption.
Qed.

Lemma update_global_get_other : forall i j sr sr' fr num val,
  NoDup (inst_globals (f_inst fr)) ->
  i <> j ->
  sglob_val sr (f_inst fr) i = Some (VAL_num val) ->
  supdate_glob sr (f_inst fr) j (VAL_num num) = Some sr' ->
  sglob_val sr' (f_inst fr) i = Some (VAL_num val).
Proof.
  intros ? ? ? ? ? ? ? Hnodup Hneq Hr Hw.
  unfold supdate_glob, sglob_ind, supdate_glob_s in *.
  destruct (lookup_N (inst_globals (f_inst fr)) j) eqn:Heqn. 2: inv Hw. cbn in Hw.
  destruct (lookup_N (s_globals sr) g) eqn:Heqn'. 2: inv Hw. inv Hw.
  unfold sglob_val, sglob, sglob_ind in *.
  destruct (lookup_N (inst_globals (f_inst fr)) i) eqn:Heqn''.  2: inv Hr.
  cbn. cbn in Hr.
  assert (g <> g1). {
    intro. subst. rewrite <- Heqn'' in Heqn.
    apply Hneq. unfold lookup_N in Heqn, Heqn''.
    eapply NoDup_nth_error in Heqn; eauto. lia.
    apply nth_error_Some. congruence. }
  unfold lookup_N in *.
  erewrite set_nth_nth_error_other; auto; try lia.
  assert (Hl: N.to_nat g < length (s_globals sr)). { apply nth_error_Some. intro. congruence. }
  lia.
Qed.

Lemma update_global_preserves_memory : forall sr sr' fr v j,
  supdate_glob sr (f_inst fr) j v = Some sr' ->
  smem sr (f_inst fr) = smem sr' (f_inst fr).
Proof.
  intros.
  unfold supdate_glob, supdate_glob_s, sglob_ind in H. cbn in H.
  destruct (lookup_N (inst_globals (f_inst fr)) j). 2: inv H. cbn in H.
  destruct (lookup_N (s_globals sr) g). inv H. reflexivity. inv H.
Qed.

Lemma update_global_preserves_funcs : forall sr sr' fr v j,
  supdate_glob sr (f_inst fr) j v = Some sr' ->
  sr.(s_funcs) = sr'.(s_funcs).
Proof.
  intros.
  unfold supdate_glob, supdate_glob_s, sglob_ind in H. cbn in H.
  destruct (lookup_N (inst_globals (f_inst fr)) j). 2: inv H. cbn in H.
  destruct (lookup_N (s_globals sr) g). inv H. reflexivity. inv H.
Qed.

Lemma update_memory_preserves_globals (sr : store_record) (fr : frame) : forall g gv sr' m,
  sglob_val sr (f_inst fr) g = Some gv ->
  sr' = upd_s_mem sr (set_nth m sr.(s_mems) 0 m) ->
  sglob_val sr' (f_inst fr) g = Some gv.
Proof.
  intros; subst sr'.
  unfold upd_s_mem, sglob_val, sglob, sglob_ind in H |- *; cbn.
  now destruct (lookup_N (inst_globals (f_inst fr))) eqn:Hinstglob.
Qed.

Lemma store_offset_eq : forall m addr off w,
  store m addr off (serialise_num w) (length (serialise_num w)) =
  store m (addr + off) 0%N (serialise_num w) (length (serialise_num w)).
Proof.
  intros. unfold store.
  now replace (addr + off + 0)%N with (addr + off)%N.
Qed.


Lemma reduce_trans_label : forall instr instr' hs hs' sr sr' fr fr' i (lh : lholed i),
  reduce_trans (hs, sr, fr, instr) (hs', sr', fr', instr') ->
  reduce_trans (hs, sr, fr, lfill lh instr) (hs', sr', fr', lfill lh instr').
Proof.
  intros.
  apply clos_rt_rt1n in H.
  remember (hs, sr, fr, instr) as x. remember (hs', sr', fr', instr') as x'.
  generalize dependent hs. generalize dependent hs'.
  revert fr fr' sr sr' instr instr'.
  induction H; intros; subst.
  - inv Heqx. apply rt_refl.
  - destruct y as [[[? ?] ?] ?].
    eapply rt_trans with (y := (?[hs], ?[sr], ?[f'], ?[instr])).
    eapply rt_step. eapply r_label with (k:=i) (lh:=lh); eauto.
    now apply IHclos_refl_trans_1n.
Qed.

Lemma reduce_trans_label0 : forall instr instr' hs hs' sr sr' fr fr',
  reduce_trans (hs, sr, fr, instr) (hs', sr', fr', instr') ->
  reduce_trans (hs, sr, fr, [:: AI_label 0 [::] instr]) (hs', sr', fr', [:: AI_label 0 [::] instr']).
Proof.
  intros.
  remember (LH_rec [] 0 [] (LH_base [] []) []) as lh.
  have H' := reduce_trans_label instr instr' _ _ _ _ _ _ _ lh. subst lh. cbn in H'.
  do 2! rewrite cats0 in H'. eapply rt_trans. eapply H'; auto. eassumption.
  apply rt_refl.
Qed.

Lemma reduce_trans_label1 : forall instr instr' hs hs' sr sr' fr fr',
  reduce_trans (hs,  sr, fr, instr) (hs', sr', fr', instr') ->
  reduce_trans (hs,  sr, fr, [:: AI_label 1 [::] instr]) (hs', sr', fr', [:: AI_label 1 [::] instr']).
Proof.
  intros.
  remember (LH_rec [] 1 [] (LH_base [] []) []) as lh.
  have H' := reduce_trans_label instr instr' _ _ _ _ _ _ _ lh. subst lh. cbn in H'.
  do 2! rewrite cats0 in H'. eapply rt_trans. eapply H'; auto. eassumption.
  apply rt_refl.
Qed.

Lemma reduce_trans_frame : forall instr instr' hs hs' sr sr' fr fr' f0,
  reduce_trans (hs, sr, fr, instr) (hs', sr', fr', instr') ->
  reduce_trans (hs, sr, f0, [:: AI_frame 0 fr instr]) (hs', sr', f0, [:: AI_frame 0 fr' instr']).
Proof.
  intros.
  apply clos_rt_rt1n in H.
  remember (hs, sr, fr, instr) as x. remember (hs', sr', fr', instr') as x'.
  generalize dependent hs. generalize dependent hs'. revert instr instr' fr fr' f0 sr sr'.
  induction H; intros; subst.
  - inv Heqx. apply rt_refl.
  - destruct y as [[[? ?] ?] ?].
    have IH := IHclos_refl_trans_1n _ _ _ _ _ _ _ _ Logic.eq_refl _ Logic.eq_refl.
    eapply rt_trans with (y := (?[hs], ?[sr], f0, [:: AI_frame 0 ?[f'] ?[instr]])).
    2: by apply IH.
    eapply rt_step. now eapply r_frame.
Qed.

Lemma app_trans: forall s f es s' f' es' les hs hs',
  reduce_trans (hs, s, f, es) (hs', s', f', es') ->
  reduce_trans (hs, s, f, (es ++ les)) (hs', s', f', (es' ++ les)).
Proof.
  intros. apply clos_rt_rt1n in H. remember (hs, s, f, es) as x.
  remember (hs', s', f', es') as x'. generalize dependent hs. generalize dependent hs'.
  revert s s' f f' es es'. induction H; intros; subst.
  - inv Heqx. apply rt_refl.
  - destruct y as [[[hs0 s0] f0] es0].
    eapply rt_trans with (y := (?[hs], ?[sr], ?[f'], ?[l])). apply rt_step.
    eapply r_label with (k:=0) (lh:=LH_base [] les). apply H.
    reflexivity. reflexivity.
    apply IHclos_refl_trans_1n; auto.
Qed.

Lemma app_trans_const : forall hs hs' s s' f f' es es' lconst,
  const_list lconst ->
  reduce_trans (hs, s, f, es) (hs', s', f', es') ->
  reduce_trans (hs, s, f, (lconst ++ es)) (hs', s', f', (lconst ++ es')).
Proof.
  intros ? ? ? ? ? ? ? ? ? Hconst Hred. apply clos_rt_rt1n in Hred.
  remember (hs, s, f, es) as x. remember (hs', s', f', es') as x'.
  generalize dependent hs. generalize dependent hs'. generalize dependent lconst.
  revert s s' f f' es es'.
  induction Hred; intros; subst.
  - inv Heqx. apply rt_refl.
  - destruct y as [[[hs'' s''] f''] es''].
    eapply rt_trans with (y := (?[hs], ?[sr], ?[f'], ?[instr])).
    apply rt_step. apply r_eliml. cbn. now rewrite Hconst. eassumption.
    apply IHHred; auto.
Qed.


Lemma decode_int32_bounds : forall b m addr,
  load m addr 0%N 4 = Some b ->
  (-1 < decode_int b < Wasm_int.Int32.modulus)%Z.
Proof.
  intros.
  (* length b = 4 bytes *)
  unfold load in H.
  destruct (addr + (0 + 4) <=? mem_length m)%N=>//.
  unfold read_bytes in H. cbn in H.
  destruct (mem_lookup (addr + 0 + 0)%N (meminst_data m))=>//.
  destruct (mem_lookup (addr + 0 + 1)%N (meminst_data m))=>//.
  destruct (mem_lookup (addr + 0 + 2)%N (meminst_data m))=>//.
  destruct (mem_lookup (addr + 0 + 3)%N (meminst_data m))=>//.
  inv H.
  unfold decode_int, int_of_bytes, rev_if_be, Wasm_int.Int32.modulus, two_power_nat.
  destruct Archi.big_endian;
    destruct b0, b1, b2, b3; cbn;
      unfold Byte.modulus, Byte.wordsize, two_power_nat, Wordsize_8.wordsize in *;
        cbn in *; lia.
Qed.

Lemma decode_int64_bounds : forall b m addr,
  load m addr 0%N 8 = Some b ->
  (-1 < decode_int b < Wasm_int.Int64.modulus)%Z.
Proof.
  intros.
  (* length b = 8 bytes *)
  unfold load in H.
  destruct (addr + (0 + 8) <=? mem_length m)%N=>//.
  unfold read_bytes in H. cbn in H.
  destruct (mem_lookup (addr + 0 + 0)%N (meminst_data m))=>//.
  destruct (mem_lookup (addr + 0 + 1)%N (meminst_data m))=>//.
  destruct (mem_lookup (addr + 0 + 2)%N (meminst_data m))=>//.
  destruct (mem_lookup (addr + 0 + 3)%N (meminst_data m))=>//.
  destruct (mem_lookup (addr + 0 + 4)%N (meminst_data m))=>//.
  destruct (mem_lookup (addr + 0 + 5)%N (meminst_data m))=>//.
  destruct (mem_lookup (addr + 0 + 6)%N (meminst_data m))=>//.
  destruct (mem_lookup (addr + 0 + 7)%N (meminst_data m))=>//.
  inv H.
  unfold decode_int, int_of_bytes, rev_if_be, Wasm_int.Int64.modulus, two_power_nat.
  destruct Archi.big_endian;
    destruct b0, b1, b2, b3, b4, b5, b6, b7; cbn;
      unfold Byte.modulus, Byte.wordsize, two_power_nat, Wordsize_8.wordsize in *;
        cbn in *; lia.
Qed.

Lemma lholed_nested_label : forall k (lh : lholed k) es es',
  exists k' (lh' : lholed k'),
  lfill lh ([:: AI_label 0 [::] es] ++ es') = lfill lh' es.
Proof.
  intros. induction lh; cbn.
  - eexists. exists (LH_rec l 0 [] (LH_base [] []) (es' ++ l0)). cbn.
    by rewrite cats0.
  - destruct IHlh as [k' [lh' Heq]]. cbn.
    eexists. exists (LH_rec l n l0 lh' l1). cbn.
    now rewrite Heq.
Qed.

Lemma lholed_nested_label2 : forall k (lh : lholed k) es es',
  exists k' (lh' : lholed k'),
  lfill lh ([:: AI_label 0 [::] [:: AI_label 0 [::] es]] ++ es') = lfill lh' es.
Proof.
  intros. induction lh; cbn.
  - eexists. exists (LH_rec l 0 [] (LH_rec [] 0 [] (LH_base [] []) []) (es' ++ l0)). cbn.
    by rewrite cats0.
  - destruct IHlh as [k' [lh' Heq]]. cbn.
    eexists. exists (LH_rec l n l0 lh' l1). cbn.
    now rewrite Heq.
Qed.

Lemma lholed_tail : forall k (lh : lholed k) es es',
  exists k' (lh' : lholed k'),
  lfill lh (es ++ es') = lfill lh' es.
Proof.
  intros.
  induction lh; cbn.
  - eexists. exists (LH_base l (es' ++ l0)). now rewrite -catA.
  - destruct IHlh as [k' [lh' Heq]].
    eexists. rewrite Heq.
    exists (LH_rec l n l0 lh' l1).
    reflexivity.
Qed.

End Wasm.

Section Arith.

Lemma signed_upper_bound : forall x,
  (Wasm_int.Int32.signed (Wasm_int.Int32.repr x) < Wasm_int.Int32.half_modulus)%Z.
Proof.
  intros x.
  unfold Wasm_int.Int32.signed. destruct (zlt _ _); auto.
  unfold Wasm_int.Int32.unsigned in *. clear g.
  have H' := Wasm_int.Int32.Z_mod_modulus_range x. simpl_modulus_in H'. simpl_modulus. cbn. lia.
Qed.

Lemma div_page_size_neq_i32_half_modulus : forall v,
  (Int32.signed v ÷ (Z.of_N page_size) <> 2147483648)%Z.
Proof.
  unfold Wasm_int.Int32.signed. cbn.
  intros v vBounds.
  have H'' := signed_upper_bound (Int32.unsigned v).
  simpl_modulus_in H''.
  destruct (zlt _ _); try lia.
  destruct v; cbn in *. lia.
Qed.

Lemma N_div_ge0 : forall a b,
  (a / b >= 0)%N.
Proof.
  intros.
  remember (a / b)%N as n.
  lia.
Qed.

Lemma small_signed_repr_n_n : forall n,
  (0 <= n <= Z.of_N max_mem_pages)%Z->
  Wasm_int.Int32.signed (Wasm_int.Int32.repr n) = n.
Proof.
  intros n H. unfold max_mem_pages in H.
  unfold Wasm_int.Int32.signed. cbn.
  rewrite zlt_true.
  rewrite Wasm_int.Int32.Z_mod_modulus_id; simpl_modulus; cbn; lia.
  rewrite Wasm_int.Int32.Z_mod_modulus_id; simpl_modulus; cbn; lia.
Qed.

Lemma i32_exists_N : forall (x : i32),
  exists n, x = N_to_i32 n /\ (-1 < Z.of_N n < Wasm_int.Int32.modulus)%Z.
Proof.
  intros [val H]. exists (Z.to_N val). split; try lia.
  destruct (N_to_i32 (Z.to_N val)) eqn:He. inv He. revert intrange.
  rewrite Wasm_int.Int32.Z_mod_modulus_id; try lia.
  rewrite Z2N.id; try lia. intros.
  destruct H as [low high].
  destruct intrange as [low' high'].
  rewrite (Wasm_int.Int32.Z_lt_irrelevant low low').
  rewrite (Wasm_int.Int32.Z_lt_irrelevant high high'). reflexivity.
Qed.

Lemma default_vals_i32_Some : forall n,
  default_vals (repeat (T_num T_i32) n) = Some (repeat (VAL_num (nat_to_value 0)) n).
Proof.
  induction n=>//. unfold default_vals in *. cbn in *.
  rewrite -cat1s. rewrite <- (cat1s (VAL_num (nat_to_value 0))).
  apply those_cat=>//.
Qed.

End Arith.

Section Primitives.

Context `{ho : host}.

(* Misc. helpers and results about Coq's unsigned 63-bit integers
   and relation to Wasm i64s and 64-bit operations.
 *)

(* Avoid unfolding during proofs *)
Opaque Uint63.to_Z.

(* Add some extra power to lia *)
Ltac Zify.zify_post_hook ::= Z.div_mod_to_equations.

Local Coercion Z_to_i64_co z := Z_to_i64 z.
Local Coercion Z_to_i64val_co z := Z_to_VAL_i64 z.

Hint Resolve eq_sym eq_trans : core.
Hint Extern 1 => symmetry : core.

Remark int64_modulus_eq_pow64 : Int64.modulus = (2^64)%Z.
Proof. now unfold Int64.modulus, Int64.half_modulus, two_power_nat. Qed.

Hint Resolve int64_modulus_eq_pow64 : core.

Lemma uint63_lt_pow64 : forall (x : uint63), (0 <= to_Z x < 2^64)%Z.
Proof.
  intros; have H := (to_Z_bounded x).
  cbn in H.
  lia.
Qed.

Hint Resolve uint63_lt_pow64 : core.

Lemma lt_pow64_mod_modulus_id : forall x, (0 <= x < 2^64)%Z -> Int64.Z_mod_modulus x = x.
Proof.
  intros. now rewrite Int64.Z_mod_modulus_id.
Qed.

Hint Resolve lt_pow64_mod_modulus_id : core.

Lemma lt_pow64_unsigned_id : forall x, (0 <= x < 2^64)%Z -> Int64.unsigned x = x.
Proof.
  intros. now cbn.
Qed.

Hint Resolve lt_pow64_unsigned_id : core.

Corollary uint63_mod_modulus_id : forall (x : uint63), Int64.Z_mod_modulus (to_Z x) = to_Z x.
Proof. intros; auto. Qed.

Hint Resolve uint63_mod_modulus_id : core.

Corollary uint63_unsigned_id : forall (x : uint63), Int64.unsigned (to_Z x) = to_Z x.
Proof. intros; auto. Qed.

Hint Resolve uint63_unsigned_id : core.

Hint Resolve Z.mod_pos_bound : core.

Lemma Z_bitmask_modulo_equivalent :
  forall (n : Z), Z.land n maxuint63 = Z.modulo n wB.
Proof.
  intros; now (replace maxuint63 with (Z.ones 63); [rewrite Z.land_ones|cbn]).
Qed.

Lemma int64_bitmask_modulo :
  forall (x : Z),  Int64.iand x maxuint63 = Z.modulo x wB.
Proof.
  intros.
  unfold Int64.iand, Int64.and. simpl.
  rewrite Int64.Z_mod_modulus_eq.
  rewrite Int64.modulus_twice_half_modulus.
  replace (Z.land (x mod (2 * Int64.half_modulus)) 9223372036854775807)
    with (Z.modulo (x mod (2 * Int64.half_modulus)) Int64.half_modulus) by now rewrite Z_bitmask_modulo_equivalent.
  now rewrite Zaux.Zmod_mod_mult.
Qed.

Lemma uint63_eq_int64_eq :
  forall x y, to_Z x = to_Z y -> Int64.eq (to_Z x) (to_Z y) = true.
Proof.
  intros; unfold Int64.eq; rewrite H; now rewrite zeq_true.
Qed.

Lemma uint63_neq_int64_neq :
  forall x y, to_Z x <> to_Z y -> Int64.eq (to_Z x) (to_Z y) = false.
Proof.
  intros; unfold Int64.eq; do 2 rewrite uint63_unsigned_id; now rewrite zeq_false.
Qed.

Lemma to_Z_neq_uint63_eqb_false :
  forall x y, to_Z x <> to_Z y -> (x =? y)%uint63 = false.
Proof.
  intros; rewrite eqb_false_spec; intro Hcontra; now rewrite Hcontra in H.
Qed.

Lemma uint63_lt_int64_lt :
  forall x y, (to_Z x < to_Z y)%Z -> Int64.ltu (to_Z x) (to_Z y) = true.
Proof. intros; unfold Int64.ltu; repeat rewrite uint63_unsigned_id; now rewrite zlt_true. Qed.

Lemma uint63_nlt_int64_nlt :
  forall x y, ~ (to_Z x < to_Z y)%Z -> Int64.ltu (to_Z x) (to_Z y) = false.
Proof. intros; unfold Int64.ltu; do 2 rewrite uint63_unsigned_id; now rewrite zlt_false. Qed.

Lemma to_Z_nlt_uint63_ltb_false :
  forall x y, ~ (to_Z x < to_Z y)%Z -> (x <? y)%uint63 = false.
Proof. intros; have H' := reflect_iff _ _ (ltbP x y); now destruct (x <? y)%uint63. Qed.

Lemma uint63_le_int64_le :
  forall x y, (to_Z x <= to_Z y)%Z -> negb (Int64.ltu (to_Z y) (to_Z x)) = true.
Proof. intros; unfold Int64.ltu; repeat rewrite uint63_unsigned_id; rewrite zlt_false; auto; lia. Qed.

Lemma uint63_nle_int64_nle :
  forall x y, ~ (to_Z x <= to_Z y)%Z -> negb (Int64.ltu (to_Z y) (to_Z x)) = false.
Proof. intros; unfold Int64.ltu; do 2 rewrite uint63_unsigned_id; rewrite zlt_true; auto; lia. Qed.

Lemma to_Z_nle_uint63_leb_false :
  forall x y, ~ (to_Z x <= to_Z y)%Z -> (x <=? y)%uint63 = false.
Proof. intros; have H' := reflect_iff _ _ (lebP x y); now destruct (x <=? y)%uint63. Qed.

Local Ltac solve_arith_op d1 d2 spec :=
  intros; unfold d1, d2; (repeat rewrite uint63_unsigned_id); (try rewrite int64_bitmask_modulo); now rewrite spec.

(* Helper lemmas to show that the Wasm arithmetic is correct w.r.t. 63 bit arithmetic.
   Helps prove that E.g. the instructions

   i64.const x
   i64.const y
   i64.add
   i64.const (2^63 - 1)
   i64.and

   reduce to

   i64.const ((x + y) mod 2^63)
 *)
Lemma uint63_add_i64_add : forall x y, Int64.iand (Int64.iadd (to_Z x) (to_Z y)) maxuint63 = to_Z (x + y).
Proof. solve_arith_op Int64.iadd Int64.add add_spec. Qed.

Lemma uint63_add_i64_add' : forall x y z,
    Int64.iand (Int64.iadd (Int64.iadd (to_Z x) (to_Z y)) (to_Z z)) maxuint63 = to_Z (x + y + z).
Proof.
  intros. unfold Int64.iadd, Int64.add.
  do 3 rewrite uint63_unsigned_id.
  rewrite int64_bitmask_modulo.
  cbn. rewrite Int64.Z_mod_modulus_eq.
  rewrite Int64.modulus_twice_half_modulus.
  rewrite -Zplus_mod_idemp_l.
  rewrite Zaux.Zmod_mod_mult; [|lia|now cbn].
  now do 2 rewrite -add_spec.
Qed.

Lemma uint63_sub_i64_sub : forall x y, Int64.iand (Int64.isub (to_Z x) (to_Z y)) maxuint63 = to_Z (x - y).
Proof. solve_arith_op Int64.isub Int64.sub sub_spec. Qed.

Lemma uint63_sub_i64_sub' : forall x y z,
    Int64.iand (Int64.isub (Int64.isub (to_Z x) (to_Z y)) (to_Z z)) maxuint63 = to_Z (x - y - z).
Proof.
  intros. unfold Int64.isub, Int64.sub.
  do 3 rewrite uint63_unsigned_id.
  rewrite int64_bitmask_modulo.
  cbn. rewrite Int64.Z_mod_modulus_eq.
  rewrite Int64.modulus_twice_half_modulus.
  rewrite -Zminus_mod_idemp_l.
  rewrite Zaux.Zmod_mod_mult; [|lia|now cbn].
  now do 2 rewrite -sub_spec.
Qed.

Lemma uint63_mul_i64_mul : forall x y, Int64.iand (Int64.imul (to_Z x) (to_Z y)) maxuint63 = to_Z (x * y).
Proof. solve_arith_op Int64.imul Int64.mul mul_spec. Qed.

Local Ltac solve_div_mod d1 d2 spec :=
  intros; unfold d1, d2;
  repeat rewrite uint63_unsigned_id;
  rewrite spec;
  now (replace Int64.zero with (Int64.repr (to_Z 0)); [rewrite uint63_neq_int64_neq|rewrite to_Z_0]).

Lemma uint63_div_i64_div : forall x y,
    to_Z y <> to_Z 0 -> Int64.idiv_u (to_Z x) (to_Z y) = Some (Int64.repr (to_Z (x / y))).
Proof. solve_div_mod Int64.idiv_u Int64.divu div_spec. Qed.

Lemma uint63_div0 : forall x y,
    to_Z y = to_Z 0 -> to_Z (x / y) = to_Z 0.
Proof.
  intros; rewrite div_spec H to_Z_0; unfold Z.div, Z.div_eucl; now destruct (to_Z x).
Qed.

Lemma uint63_mod_i64_mod : forall x y,
    to_Z y <> to_Z 0 -> Int64.irem_u (to_Z x) (to_Z y) = Some (Int64.repr (to_Z (x mod y))).
Proof. solve_div_mod Int64.irem_u Int64.modu mod_spec. Qed.

Lemma uint63_mod0 : forall x y,
    to_Z y = to_Z 0 -> to_Z (x mod y) = to_Z x.
Proof.
  intros; rewrite mod_spec H to_Z_0; unfold Z.modulo, Z.div_eucl; now destruct (to_Z x).
Qed.

Lemma uint63_land_i64_and : forall x y, Int64.iand (to_Z x) (to_Z y) = to_Z (x land y).
Proof. solve_arith_op Int64.iand Int64.and land_spec'. Qed.

Lemma uint63_lor_i64_or : forall x y, Int64.ior (to_Z x) (to_Z y) = to_Z (x lor y).
Proof. solve_arith_op Int64.ior Int64.or lor_spec'. Qed.

Lemma uint63_lxor_i64_xor : forall x y, Int64.ixor (to_Z x) (to_Z y) = to_Z (x lxor y).
Proof. solve_arith_op Int64.ixor Int64.xor lxor_spec'. Qed.

Lemma lsl_bits_high : forall x y,
    (to_Z 63 <= to_Z y)%Z ->
    forall i, bit (x << y) i = false.
Proof.
  intros.
  destruct (digits <=? i)%uint63 eqn:Hi.
  now apply bit_M.
  rewrite bit_lsl; unfold digits in *.
  assert (to_Z i < to_Z 63)%Z as Hi1 by
      now destruct (reflect_dec _ _ (lebP 63 i)) as [H'|H']; [rewrite (reflect_iff _ _ (lebP 63 i)) in H'|].
  assert (to_Z i < to_Z y)%Z as Hi2 by now replace (to_Z 63) with 63%Z in *; [lia|cbn].
  now replace (i <? y)%uint63 with true; [cbn|rewrite (reflect_iff _ _ (ltbP i y)) in Hi2].
Qed.

Lemma uint63_bits_inj_0 i : (forall j, bit i j = false) -> i = 0%uint63.
Proof.
  intros.
  assert (forall n, bit i n = bit 0 n) by now intros; rewrite bit_0; apply H.
  now apply bit_ext.
Qed.

Lemma uint63_lsl63 : forall x y,
  (to_Z 63 <= to_Z y)%Z ->
  to_Z (x << y) = to_Z 0.
Proof.
  intros;
  now replace (x << y)%uint63 with 0%uint63;[reflexivity|rewrite (uint63_bits_inj_0 _ (lsl_bits_high x y H))].
Qed.

Lemma uint63_lsl_i64_shl : forall x y,
  (to_Z y < to_Z 63)%Z ->
  Int64.iand (Int64.ishl (to_Z x) (to_Z y)) maxuint63 = to_Z (x << y).
Proof.
  intros.
  have H' := to_Z_bounded y.
  unfold Int64.ishl, Int64.shl, Int64.wordsize, Integers.Wordsize_64.wordsize.
  replace (to_Z 63) with 63%Z in H by now cbn.
  do 2 rewrite uint63_unsigned_id.
  replace (Int64.unsigned (Z_to_i64 (to_Z y mod 64%nat))) with (to_Z y). 2: now rewrite Z.mod_small; [rewrite uint63_unsigned_id|].
  rewrite Z.shiftl_mul_pow2. 2: lia.
  now rewrite lsl_spec; rewrite int64_bitmask_modulo.
Qed.

Lemma uint63_lsr63 : forall x y,
  (to_Z 63 <= to_Z y)%Z ->
  to_Z (x >> y) = to_Z 0.
Proof.
  intros;
  rewrite (reflect_iff _ _ (lebP 63 y)) in H;
  now replace (x >> y)%uint63 with 0%uint63; [reflexivity|rewrite lsr_M_r].
Qed.

Lemma uint63_lsr_i64_shr : forall x y,
  (to_Z y < to_Z 63)%Z ->
  Int64.ishr_u (to_Z x) (to_Z y) = to_Z (x >> y).
Proof.
  intros.
  have H' := to_Z_bounded y.
  unfold Int64.ishr_u, Int64.shru, Int64.wordsize, Integers.Wordsize_64.wordsize.
  replace (to_Z 63) with 63%Z in H by now cbn.
  do 2 rewrite uint63_unsigned_id.
  replace (Int64.unsigned (Z_to_i64 (to_Z y mod 64%nat))) with (to_Z y).
  2: now rewrite Z.mod_small; [rewrite uint63_unsigned_id|].
  rewrite Z.shiftr_div_pow2. 2: lia.
  now rewrite lsr_spec.
Qed.

Lemma uint63_diveucl_0 : forall x y,
  to_Z y = to_Z 0 ->
  to_Z (fst (diveucl x y)) = to_Z 0 /\ to_Z (snd (diveucl x y)) = to_Z x.
Proof.
  intros.
  rewrite diveucl_def_spec; unfold diveucl_def; simpl.
  rewrite ->div_spec, ->mod_spec.
  unfold Z.div, Z.modulo, Z.div_eucl.
  split; rewrite H; destruct (to_Z x); auto.
Qed.

(* mulc *)

Lemma Z_bitmask_modulo32_equivalent : forall (n : Z),
  Z.land n 4294967295%Z = Z.modulo n (2^32)%Z.
Proof.
  intros.
  replace 4294967295%Z with (Z.ones 32)=>//.
  now rewrite Z.land_ones.
Qed.

Ltac unfold_modulus64 := unfold Int64.modulus, Int64.half_modulus, two_power_nat in *; cbn in *.

Lemma lt_pow32_mod_modulus_id : forall x,
  (0 <= x < 2^32)%Z ->
  Int64.Z_mod_modulus x = x.
Proof.
  intros. rewrite Int64.Z_mod_modulus_id=>//.
  rewrite int64_modulus_eq_pow64. lia.
Qed.

Hint Resolve lt_pow32_mod_modulus_id : core.

Lemma lt_pow32_unsigned_id : forall x, (0 <= x < 2^32)%Z -> Int64.unsigned x = x.
Proof. intros; now cbn. Qed.

Hint Resolve lt_pow32_unsigned_id : core.


Lemma low32_max_int32 : forall x,
  (0 <= x mod 2^32 < 2^32)%Z.
Proof. intros; lia. Qed.

Lemma low32_modulo64_id : forall x,
  Int64.unsigned (x mod 2^32)%Z = (x mod 2^32)%Z.
Proof. intros; auto. Qed.

Lemma low32_modulo64_id' : forall x,
  Int64.Z_mod_modulus (x mod 2^32)%Z = (x mod 2^32)%Z.
Proof. intros; auto. Qed.

Lemma int64_low32' : forall x,
  (0 <= x < 2^64)%Z -> (Int64.iand x 4294967295%Z = x mod 2^32)%Z.
Proof.
  intros.
  unfold Int64.iand, Int64.and.
  replace (Int64.unsigned x) with x; auto.
  replace (Int64.unsigned 4294967295%Z) with 4294967295%Z; auto.
  now rewrite Z_bitmask_modulo32_equivalent.
Qed.

Lemma int64_low32 : forall x,
  (0 <= x < 2^64)%Z ->
  Int64.unsigned (Int64.iand x 4294967295%Z) = (x mod 2^32)%Z.
Proof.
intros. rewrite int64_low32'; auto.
Qed.

Lemma high32_max_int32 : forall x,
  (0 <= x < 2^64)%Z ->
  (0 <= x / 2^32 < 2^32)%Z.
Proof. lia. Qed.

Lemma high32_max_int32' : forall x,
  (0 <= x < 2^64)%Z ->
  (0 <= x / 4294967296 < 4294967296)%Z.
Proof. lia. Qed.

Lemma int64_high32 : forall x,
  (0 <= x < 2^64)%Z ->
  Int64.ishr_u x 32 = (x / 2^32)%Z.
Proof.
intros.
unfold Int64.ishr_u, Int64.shru.
replace (Int64.unsigned (Z_to_i64 (Int64.unsigned 32 mod Int64.wordsize))) with (Int64.unsigned 32%Z) by now cbn.
replace (Int64.unsigned x) with x; auto.
replace (Int64.unsigned 32%Z) with 32%Z; auto.
now rewrite Z.shiftr_div_pow2; auto.
Qed.

Lemma max32bit_mul_modulo64_id : forall x y,
  (0 <= x < 2^32)%Z -> (0 <= y < 2^32)%Z -> Int64.imul x y = (x * y)%Z.
Proof.
intros.
unfold Int64.imul, Int64.mul.
replace (Int64.unsigned x) with x; replace (Int64.unsigned y) with y; auto.
Qed.

Definition lo x := (x mod 2^32)%Z.
Definition hi x := (x / 2^32)%Z.
Definition cross x y := (hi (lo x * lo y) + lo (hi x * lo y) + lo x * hi y)%Z.
Definition lower x y := ((cross x y) * 2^32 + (lo (lo x * lo y)))%Z.
Definition upper x y := (hi (hi x * lo y) + hi (cross x y) + (hi x * hi y))%Z.

Hint Transparent lo hi cross lower upper : core.

Lemma lo_range : forall x, (0 <= x < 2^64)%Z -> (0 <= lo x < 2^32)%Z.
Proof. intros. eauto. Qed.

Lemma hi_range : forall x, (0 <= x < 2^64)%Z -> (0 <= hi x < 2^32)%Z.
Proof. intros. unfold hi; lia. Qed.

Lemma hi_range_63bit : forall x,
  (0 <= x < 2^63)%Z ->
  (0 <= hi x < 2^31)%Z.
Proof. intros. unfold hi; lia. Qed.

Hint Resolve lo_range hi_range hi_range_63bit : core.

Lemma lo_hi_product_63bit : forall x y,
  (0 <= x < 2^63)%Z ->
  (0 <= y < 2^63)%Z ->
  (0 <= lo x * hi y <= (2^32 - 1) * (2^31 - 1))%Z.
Proof.
  intros ?? Hx Hy.
  have Hxlo := lo_range x. have Hyhi := hi_range_63bit y Hy.
  nia.
Qed.

Corollary hi_lo_product_63bit : forall x y,
  (0 <= x < 2^63)%Z ->
  (0 <= y < 2^63)%Z ->
  (0 <= hi x * lo y <= (2^31 - 1) * (2^32 - 1))%Z.
Proof.
  intros. replace (hi x * lo y)%Z with (lo y * hi x)%Z by lia.
  now apply lo_hi_product_63bit.
Qed.

Lemma lo_lo_product_63bit : forall x y,
  (0 <= x < 2^63)%Z -> (0 <= y < 2^63)%Z ->
  (0 <= lo x * lo y <= (2^32 -1) * (2^32 - 1))%Z.
Proof.
  intros ?? Hx Hy.
  have Hxlo := lo_range x. have Hylo := lo_range y.
  nia.
Qed.

Lemma hi_hi_product_63bit : forall x y,
  (0 <= x < 2^63)%Z ->
  (0 <= y < 2^63)%Z ->
  (0 <= hi x * hi y <= (2^31 - 1) * (2^31 - 1))%Z.
Proof.
  intros ?? Hx Hy.
  have Hxhi := hi_range_63bit x Hx. have Hyhi := hi_range_63bit y Hy.
  nia.
Qed.

Lemma lo_hi_lo_range : forall x y,
  (0 <= x < 2^63)%Z ->
  (0 <= y < 2^63)%Z ->
  (0<= lo (hi x * lo y) <= 2^32)%Z.
Proof.
  intros ?? Hx Hy.
  have H := hi_lo_product_63bit x y Hx Hy.
  unfold lo, hi in *; lia.
Qed.

Lemma sum1_range : forall x y,
  (0 <= x < 2^63)%Z -> (0 <= y < 2^63)%Z ->
  (0 <= hi (lo x * lo y) + lo (hi x * lo y) <= 2^32-1 + 2^32-1)%Z.
Proof.
  intros ?? Hx Hy.
  have H := lo_lo_product_63bit x y Hx Hy. have H' := hi_lo_product_63bit x y Hx Hy.
  unfold lo, hi in *; lia.
Qed.

Lemma sum1_i64 : forall x y,
  (0 <= x < 2^63)%Z -> (0 <= y < 2^63)%Z ->
  Int64.iadd (Int64.repr (hi (lo x * lo y)))
             (Int64.repr (lo (hi x * lo y))) =
    Int64.repr (hi (lo x * lo y) + lo (hi x * lo y))%Z.
Proof.
  intros ?? Hx Hy.
  unfold Int64.iadd, Int64.add.
  have H := lo_lo_product_63bit x y Hx Hy. have H' := hi_lo_product_63bit x y Hx Hy.
  repeat rewrite lt_pow64_unsigned_id. reflexivity.
  all: unfold hi, lo in *; lia.
Qed.

Lemma cross_range : forall x y,
  (0 <= x < 2^63)%Z -> (0 <= y < 2^63)%Z ->
  (0 <= cross x y <= (2^32-1 + 2^32-1) + (2^32-1) * (2^31-1))%Z.
Proof.
  intros ?? Hx Hy.
  have H := sum1_range x y Hx Hy. have H' := lo_hi_product_63bit x y Hx Hy.
  unfold cross, lo, hi in *; lia.
Qed.

Lemma cross_i64 : forall x y,
  (0 <= x < 2^63)%Z -> (0 <= y < 2^63)%Z ->
  Int64.iadd (Int64.repr (hi (lo x * lo y) + lo (hi x * lo y)))
             (Int64.repr (lo x * hi y)) =
    Int64.repr ((hi (lo x * lo y) + lo (hi x * lo y)) + lo x * hi y)%Z.
Proof.
  intros ?? Hx Hy.
  unfold Int64.iadd, Int64.add.
  have H := lo_lo_product_63bit x y Hx Hy.
  have H' := hi_lo_product_63bit x y Hx Hy.
  have H'' := lo_hi_product_63bit x y Hx Hy.
  repeat rewrite lt_pow64_unsigned_id; unfold hi, lo in *; auto; lia.
Qed.

Lemma hi_cross_range : forall x y,
  (0 <= x < 2^63)%Z ->
  (0 <= y < 2^63)%Z ->
  (0 <= hi (cross x y) <= 2^31)%Z.
Proof.
  intros ?? Hx Hy. have H := cross_range x y Hx Hy. unfold hi; lia.
Qed.

Lemma hi_hi_lo_range : forall x y,
  (0 <= x < 2^63)%Z ->
  (0 <= y < 2^63)%Z ->
  (0 <= hi (hi x * lo y) <= 2^31 - 2)%Z.
Proof.
  intros ?? Hx Hy. have H := hi_lo_product_63bit x y Hx Hy. unfold hi in *; lia.
Qed.

Lemma sum2_range : forall x y,
  (0 <= x < 2^63)%Z -> (0 <= y < 2^63)%Z ->
  (0 <= hi (hi x * lo y) + hi (cross x y) <= (2^31 - 2) + 2^31)%Z.
Proof.
intros ?? Hx Hy.
  have H := hi_cross_range x y Hx Hy. have H' := hi_hi_lo_range x y Hx Hy.
  unfold hi in *; lia.
Qed.

Lemma sum2_i64 : forall x y,
  (0 <= x < 2^63)%Z -> (0 <= y < 2^63)%Z ->
  Int64.iadd (Int64.repr (hi (hi x * lo y)))
             (Int64.repr (hi (cross x y))) =
    Int64.repr (hi (hi x * lo y) + hi (cross x y))%Z.
Proof.
  intros ?? Hx Hy.
  have H := hi_cross_range x y Hx Hy. have H' := hi_hi_lo_range x y Hx Hy.
  unfold Int64.iadd, Int64.add.
  repeat rewrite lt_pow64_unsigned_id. reflexivity.
  all: unfold hi in *; lia.
Qed.

Lemma upper_range : forall x y,
  (0 <= x < 2^63)%Z -> (0 <= y < 2^63)%Z ->
  (0 <= upper x y <= ((2^31 - 2) + 2^31) + (2^31 - 1) * (2^31-1))%Z.
Proof.
  intros ?? Hx Hy.
  have H := sum2_range x y Hx Hy. have H' := hi_hi_product_63bit x y Hx Hy.
  unfold upper, hi in *; lia.
Qed.

Lemma upper_i64 : forall x y,
  (0 <= x < 2^63)%Z -> (0 <= y < 2^63)%Z ->
  Int64.iadd (Int64.repr (hi (hi x * lo y) + hi (cross x y)))
             (Int64.repr (hi x * hi y)) =
    Int64.repr ((hi (hi x * lo y) + hi (cross x y)) + hi x * hi y)%Z.
Proof.
  intros ?? Hx Hy.
  have H := sum2_range x y Hx Hy. have H' := hi_hi_product_63bit x y Hx Hy.
  unfold Int64.iadd, Int64.add.
  repeat rewrite lt_pow64_unsigned_id; auto; lia.
Qed.

Lemma lo_lo_lo_range : forall x y,
  (0 <= x < 2^63)%Z ->
  (0 <= y < 2^63)%Z ->
  (0 <= lo (lo x * lo y) < 2^32)%Z.
Proof.
  intros ?? Hx Hy. have H := lo_lo_product_63bit x y Hx Hy. unfold lo in *; lia.
Qed.

Lemma upper_shifted_range : forall x y,
  (0 <= x < 2^63)%Z ->
  (0 <= y < 2^63)%Z ->
  (0 <= (upper x y) * 2 <= 2^63-2)%Z.
Proof.
  intros ?? Hx Hy. have H := upper_range x y Hx Hy; lia.
Qed.

Lemma upper_shifted_i64 : forall x y,
  (0 <= x < 2^63)%Z -> (0 <= y < 2^63)%Z ->
  Int64.ishl (Int64.repr (upper x y)) (Int64.repr 1) = Int64.repr (upper x y * 2)%Z.
Proof.
  intros ?? Hx Hy. have H := upper_range x y Hx Hy.
  unfold Int64.ishl, Int64.shl.
  repeat rewrite lt_pow64_unsigned_id.
  replace (1 mod Int64.wordsize)%Z with 1%Z by now cbn.
  rewrite Z.shiftl_mul_pow2. f_equal. lia.
  all: cbn; lia.
Qed.

Lemma lower_or_i64 : forall x y,
  (0 <= x < 2^63)%Z ->
  (0 <= y < 2^63)%Z ->
  Int64.ior (Int64.shl (Int64.repr (cross x y)) (Int64.repr 32))
            (Int64.repr (lo (lo x * lo y))) =
    Int64.repr ((cross x y) * 2^32 + lo (lo x * lo y)).
Proof.
  intros ?? Hx Hy.
  have H := cross_range x y Hx Hy.
  have H' := lo_lo_lo_range x y Hx Hy.
  unfold Int64.ior.
  rewrite Int64.shifted_or_is_add; unfold two_p, two_power_pos; auto.
  repeat rewrite lt_pow64_unsigned_id; auto; lia.
  cbn. lia.
  rewrite lt_pow64_unsigned_id; cbn; lia.
Qed.

Lemma lower_shifted_range : forall x y,
  (0 <= x < 2^63)%Z ->
  (0 <= y < 2^63)%Z ->
  (0 <= (lower x y mod 2^64) / 2^63 <= 1)%Z.
Proof. intros. lia. Qed.

Lemma lower_shifted_i64 : forall x y,
  (0 <= x < 2^63)%Z ->
  (0 <= y < 2^63)%Z ->
  Int64.ishr_u (Int64.repr (lower x y)) (Int64.repr 63) =
    Int64.repr ((lower x y) mod 2^64 / 2^63).
Proof.
  intros ?? Hx Hy.
  unfold Int64.ishr_u, Int64.shru.
  replace (Int64.unsigned (Int64.repr (lower x y))) with ((lower x y) mod 2^64)%Z.
  repeat rewrite lt_pow64_unsigned_id.
  replace (63 mod Int64.wordsize)%Z with 63%Z by now cbn.
  rewrite Z.shiftr_div_pow2. reflexivity.
  lia. lia. cbn; lia. lia.
  cbn. rewrite Int64.Z_mod_modulus_eq. now rewrite int64_modulus_eq_pow64.
Qed.

Lemma upper63_range : forall x y,
    (0 <= x < 2^63)%Z -> (0 <= y < 2^63)%Z ->
    (0 <= (upper x y) * 2 + ((lower x y mod 2^64) / 2^63) < 2^63)%Z.
Proof.
  intros ?? Hx Hy.
  have H := upper_shifted_range x y Hx Hy. have H' := lower_shifted_range x y Hx Hy.
  lia.
Qed.

Lemma upper63_i64 : forall x y,
  (0 <= x < 2^63)%Z -> (0 <= y < 2^63)%Z ->
  Int64.iadd (Int64.repr (upper x y * 2)) (Int64.repr (lower x y mod 2^64 / 2^63)) =
    Int64.repr (upper x y * 2 + lower x y mod 2^64 / 2^63).
Proof.
  intros ?? Hx Hy.
  have H := upper_shifted_range _ _ Hx Hy.
  unfold Int64.iadd, Int64.add.
  repeat rewrite lt_pow64_unsigned_id; auto; lia.
Qed.

Lemma lower_of_product : forall x y,
  (0 <= x < 2^64)%Z ->
  (0 <= y < 2^64)%Z ->
  ((x * y) mod 2^64 = lower x y mod 2^64)%Z.
Proof.
  intros x y Hx Hy.
  unfold lower, cross, lo, hi. lia.
Qed.

Lemma upper_of_product : forall x y,
  (0 <= x < 2^64)%Z ->
  (0 <= y < 2^64)%Z ->
  ((x * y) / 2^64 = upper x y)%Z.
Proof.
  intros x y Hx Hy. unfold upper, cross, hi, lo. lia.
Qed.

Corollary decompose_product : forall x y,
  (0 <= x < 2^64)%Z ->
  (0 <= y < 2^64)%Z ->
  (x * y = 2^64 * upper x y + lower x y mod 2^64)%Z.
Proof.
  intros.
  unfold upper, lower, cross, lo, hi. lia.
Qed.

Lemma lower_of_product_63bit : forall x y,
  (0 <= x < 2^64)%Z -> (0 <= y < 2^64)%Z ->
  ((x * y) mod 2^63 = (lower x y) mod 2^63)%Z.
Proof.
  intros. unfold lower, cross, lo, hi. lia.
Qed.

Lemma upper_of_product_63bit : forall x y,
  (0 <= x < 2^64)%Z -> (0 <= y < 2^64)%Z ->
  ((x * y) / 2^63 = 2 * (upper x y) + ((lower x y mod 2^64) / 2^63))%Z.
Proof.
  intros. unfold upper, lower, cross, lo, hi. lia.
Qed.

Corollary decompose_product_63bit : forall x y,
  (0 <= x < 2^64)%Z ->
  (0 <= y < 2^64)%Z ->
  (x * y = (2 * (upper x y) + ((lower x y mod 2^64) / 2^63)) * 2^63 + (lower x y mod 2^63))%Z.
Proof.
  intros. unfold upper, lower, cross, lo, hi. lia.
Qed.

Lemma mulc_spec_alt : forall x y,
  to_Z (fst (mulc x y)) = (((to_Z x) * (to_Z y)) / 2^63)%Z /\ to_Z (snd (mulc x y)) = (((to_Z x) * (to_Z y)) mod 2^63)%Z.
Proof.
  intros.
  have Hspec := mulc_spec x y.
  have Hx := to_Z_bounded x.
  have Hy := to_Z_bounded y.
  cbn in Hx, Hy, Hspec.
  assert (0 <= to_Z (snd (mulc x y)) < 2^63)%Z as Hrem by apply to_Z_bounded.
  lia.
Qed.

Theorem mulc_fst : forall x y,
  (to_Z (fst (mulc x y)) = ((2 * (upper (to_Z x) (to_Z y)) + ((lower (to_Z x) (to_Z y) mod 2^64) / 2^63))))%Z.
Proof.
  intros.
  destruct (mulc_spec_alt x y) as [Hfst _].
  have Hx := to_Z_bounded x; have Hy := to_Z_bounded y.
  rewrite <- upper_of_product_63bit; auto.
Qed.

Theorem mulc_snd : forall x y,
  (to_Z (snd (mulc x y)) = (lower (to_Z x) (to_Z y) mod 2^63))%Z.
Proof.
  intros.
  destruct (mulc_spec_alt x y) as [_ Hsnd].
  rewrite <-lower_of_product_63bit; auto.
Qed.

Lemma low32step : forall state sr fr num,
  (0 <= num < 2^64)%Z ->
  reduce state sr fr ([$VN (VAL_int64 (Int64.repr num))] ++
    [ AI_basic (BI_const_num (VAL_int64 (Int64.repr 4294967295))) ] ++
    [ AI_basic (BI_binop T_i64 (Binop_i BOI_and)) ])
         state sr fr [$VN (VAL_int64 (Int64.repr (lo num))) ].
Proof.
  intros.
  constructor. apply rs_binop_success; auto. cbn.
  unfold Int64.iand, Int64.and. cbn.
  rewrite Z_bitmask_modulo32_equivalent.
  rewrite Int64.Z_mod_modulus_id=>//.
  now replace Int64.modulus with (2^64)%Z.
Qed.

Lemma high32step : forall state sr fr num,
  (0<= num < 2^64)%Z ->
  reduce state sr fr ([$VN (VAL_int64 (Int64.repr num))] ++
    [ AI_basic (BI_const_num (VAL_int64 (Int64.repr 32))) ] ++
                        [ AI_basic (BI_binop T_i64 (Binop_i (BOI_shr SX_U))) ])
         state sr fr [ $VN (VAL_int64 (Int64.repr (hi num))) ].
Proof.
  intros.
  constructor. apply rs_binop_success; auto.
  unfold app_binop. simpl.
  rewrite int64_high32. reflexivity. lia.
Qed.

(* head0 related *)

Lemma head0_spec_alt: forall x : uint63,
  (0 < φ (x)%uint63)%Z ->
  (to_Z (head0 x) = 62 - Z.log2 (to_Z x))%Z.
Proof.
  intros.
  have H' := head0_spec _ H.
  replace (wB/2)%Z with (2^62)%Z in H' by now cbn. replace wB with (2^63)%Z in H' by now cbn.
  destruct H'.
  assert (Hlog1: (Z.log2 (2^62) <= Z.log2 (2 ^ (to_Z (head0 x)) * to_Z x))%Z) by now apply Z.log2_le_mono.
  assert (Hlog2: (Z.log2 (2 ^ (to_Z (head0 x)) * to_Z x) < 63)%Z).
  apply Z.log2_lt_pow2; lia.
  replace (2 ^ (to_Z (head0 x)) * to_Z x)%Z with (to_Z x * 2 ^ (to_Z (head0 x)))%Z in Hlog1, Hlog2 by lia.
  rewrite Z.log2_mul_pow2 in Hlog1, Hlog2. 2: lia. 2: apply to_Z_bounded.
  replace (Z.log2 (2 ^ 62)) with 62%Z in Hlog1 by now rewrite Z.log2_pow2.
  lia.
Qed.

Lemma powserie_nonneg : forall l,
  (forall x, In x l -> 0 <= x)%Z ->
  (0 <= Zbits.powerserie l)%Z.
Proof.
  induction l.
  intros.
  discriminate.
  intros.
  unfold Zbits.powerserie.
  fold Zbits.powerserie.
  assert (In a (a :: l)) by (constructor; reflexivity).
  assert (0 <= a)%Z by now apply H.
  assert (forall x, In x l -> 0 <= x)%Z.
  intros.
  assert (In x (a :: l)). right. assumption.
  now apply H.
  assert (0 <= Zbits.powerserie l)%Z by now apply IHl.

  apply Z.add_nonneg_nonneg.
  have Htwop := two_p_gt_ZERO a H1. lia. lia.
Qed.

Lemma in_Z_one_bits_pow : forall l i,
  (i \in l) ->
  (forall x, In x l -> 0 <= x)%Z ->
  (2^i <= Zbits.powerserie l)%Z.
Proof.
  induction l; intros.
  discriminate.
  unfold Zbits.powerserie.
  destruct (Z.eq_dec i a).
  fold Zbits.powerserie.
  rewrite <-e.
  rewrite two_p_equiv.
  assert (0 <= Zbits.powerserie l)%Z. apply powserie_nonneg; auto.
  assert (forall x, In x l -> 0 <= x)%Z.
  intros.
  assert (In x (a :: l)). right. assumption.
  now apply H0.
  assumption.
  lia.
  fold Zbits.powerserie.
  assert (i \in l).
  have H' := in_cons a l i.
  have Hrefl := reflect_iff.
  have H''' := eqP.
  specialize (H''' _ i a).
  specialize (Hrefl _ _ H''').
  destruct Hrefl.
  destruct (i == a)%Z eqn:Heqb. specialize (H2 Logic.eq_refl). contradiction.
  rewrite orb_false_l in H'. auto.
  rewrite <-H'. assumption.
  assert (forall x, In x l -> 0 <= x)%Z.
  intros.
  assert (In x (a :: l)). right. assumption.
  now apply H0.
  assert (0 <= a)%Z. apply H0; auto. now constructor.
  have Htwop := two_p_gt_ZERO a H3.
  assert (2^i <= Zbits.powerserie l)%Z. apply IHl; auto. lia.
Qed.

Lemma one_bits_non_zero : forall n x,
  0 < n ->
  (0 < x < two_power_nat n)%Z ->
  Zbits.Z_one_bits n x 0%Z <> nil.
Proof.
  intros.
  have Hz := Zbits.Z_one_bits_zero n 0.
  intro Hcontra.
  rewrite <-Hz in Hcontra.
  have Hps := Zbits.Z_one_bits_powerserie n x.
  assert (0 <= x < two_power_nat n)%Z by lia. apply Hps in H1.
  rewrite Hcontra in H1. rewrite Hz in H1. cbn in H1. lia.
Qed.

Lemma convert_from_bits_head : forall l i,
  i < size l ->
  i = find (fun b => b == true)  l ->
  (fun b => b == true) (nth false l i) = true ->
  (forall k, k < i -> (fun b => b == true) (nth false l k) = false) ->
  (Zbits.powerserie (Int64.convert_from_bits_to_Z_one_bits l) < two_p (Z.of_nat ((size l - i) - 1) + 1))%Z.
Proof.
assert (Hhead : forall l i',
             i' < size l ->
             i' = find (fun b => b==true) l ->
             (fun b => b == true) (nth false l i') = true ->
             (forall k, k < i' -> (fun b => b == true) (nth false l k) = false) ->
             exists l', Z.of_nat ((seq.size l) - i' - 1) :: l' = Int64.convert_from_bits_to_Z_one_bits l). {
    induction l.
    now intros.
    intros i' Hi1 Hi2 Hi3 Hk.
    simpl.
    simpl in Hi1.
    simpl in Hi2.
    destruct a.
    rewrite Hi2.
    rewrite Nat.sub_0_r. exists (Int64.convert_from_bits_to_Z_one_bits l).
    simpl. rewrite Nat.sub_0_r.
    reflexivity.
    simpl in Hi2.
    simpl in IHl.
    assert (i' - 1 =  (find (fun b => b == true) l)).
    { rewrite Hi2. simpl. rewrite Nat.sub_0_r. reflexivity. }
    assert (forall k, k < (i' - 1) -> (fun b => b == true) (nth false l k) = false). {
      intros k' Hk'.
      assert (ssrnat.leq (S k') (find (fun b => b == true) l)).
      rewrite -?(rwP ssrnat.leP). lia.
      have Hbf := before_find _ H0.
      apply Hbf; auto. }
    destruct (IHl (i' - 1)).
    simpl in Hi1. rewrite Hi2 in Hi1. rewrite H. simpl in Hi1. lia.
    rewrite Hi2. now cbn. rewrite Hi2. simpl.
    rewrite Hi2 in Hi3. simpl in Hi3. rewrite Nat.sub_0_r. assumption. assumption.
    assert (size l - (i' - 1) = S (size l) - i'). lia. simpl in H2.
    rewrite H2 in H1.
    exists x. assumption. }
  assert (forall l,
             (Zbits.powerserie (Int64.convert_from_bits_to_Z_one_bits l) < two_p (S (size l)))%Z).
  induction l.
  cbn. unfold two_power_pos. cbn. lia.
  destruct a. rewrite two_p_equiv.
  replace (S (size (true :: l))) with (size l + 2).
  simpl. rewrite two_p_equiv in IHl. rewrite two_p_equiv. replace  (S (size l)) with (size l + 1) in IHl.
  replace (2^ ((size l) + 1)%nat)%Z with (2^(Z.of_nat (size l) + 1))%Z in IHl.
  replace (2^ ((size l) + 2)%nat)%Z with (2^(Z.of_nat (size l) + 2))%Z.
  assert (2 ^ (size l) +  2 ^ (Z.of_nat (size l) + 1) < 2^ (Z.of_nat (size l) + 2))%Z. {

    replace (2^ (Z.of_nat (size l)) + 2^(Z.of_nat (size l) + 1))%Z with (2^(size l) * 3)%Z.
    replace (2^(Z.of_nat (size l) + 2))%Z with (2^(size l) * 4)%Z.

    apply Zmult_lt_compat_l. lia. lia. replace 4%Z with (2 * 2)%Z by lia.
    replace (2 * 2)%Z with (2^2)%Z by lia. rewrite Z.pow_add_r. reflexivity. lia. lia.
    replace 3%Z with (1 + 2)%Z.

    rewrite Z.mul_add_distr_l.
    replace (2 ^ (size l) * 2)%Z with (2^(size l + 1))%Z. rewrite Z.mul_1_r. reflexivity.
    rewrite Z.pow_add_r. lia. lia. lia. lia. }
  lia. lia. lia. lia. simpl. lia.
  replace (S (size (false  :: l))) with (size l + 2) by now cbn.
  replace (Z.of_nat (size l + 2))%Z with ((Z.of_nat (size l) + 2))%Z by lia.
  rewrite two_p_equiv.
  simpl. rewrite two_p_equiv in IHl.
  replace (2^ (S (size l))%nat)%Z with (2^(Z.of_nat (size l) + 1))%Z in IHl by lia.
  assert (2^ (Z.of_nat (size l) + 1) < 2^ (Z.of_nat (size l) + 2))%Z. {
    replace (2^ (Z.of_nat (size l) + 1))%Z with (2^(Z.of_nat (size l)) * 2)%Z.
    replace (2^ (Z.of_nat (size l) + 2))%Z with (2^(Z.of_nat (size l)) * 4)%Z.
    apply Zmult_lt_compat_l. lia. lia. rewrite Z.pow_add_r=>//. lia.
    rewrite Z.pow_add_r; lia. } lia.


  assert (forall xs x,
             (Zbits.powerserie (Int64.convert_from_bits_to_Z_one_bits (x :: xs)) < two_p (size (x :: xs)))%Z). {
    induction xs. intros.
    cbn.
    destruct x. cbn. unfold two_power_pos. cbn. lia. cbn. unfold two_power_pos. lia.
    intros.
    specialize (IHxs a).
    destruct x.
    assert (Z.of_nat (size (true :: a :: xs)) = Z.of_nat (size (a :: xs)) + 1)%Z. unfold size. fold (size xs). rewrite <-Nat.add_1_l. rewrite Nat2Z.inj_add. rewrite Z.add_comm. reflexivity.
    rewrite H0.
    unfold Int64.convert_from_bits_to_Z_one_bits. fold (Int64.convert_from_bits_to_Z_one_bits (a :: xs)).
    unfold Zbits.powerserie. fold (Zbits.powerserie (Int64.convert_from_bits_to_Z_one_bits (a :: xs))).
    assert (two_p (Z.of_nat (size (a :: xs))) < two_p (Z.of_nat (size (a :: xs)) + 1))%Z.
    rewrite two_p_equiv.
    rewrite two_p_equiv.
    rewrite Z.pow_add_r.
    lia.
    lia. lia.
    assert (forall x y y' z, y < y' -> x + y' < z -> x + y < z)%Z. intros. lia.
    assert (forall x y z, x < y -> z = 2 * y -> x + y  < z)%Z. intros. lia.
    assert (two_p (Z.of_nat (size (a :: xs)) + 1) = 2 * two_p (Z.of_nat (size (a :: xs))))%Z.
    rewrite two_p_equiv.
    rewrite two_p_equiv.
    rewrite Z.pow_add_r.
    lia.
    lia. lia.
    rewrite Z.add_comm.
    apply H3.
    assumption.
    assumption.
    assert (Z.of_nat (size (false :: a :: xs)) = Z.of_nat (size (a :: xs)) + 1)%Z. unfold size. fold (size xs). rewrite <-Nat.add_1_l. rewrite Nat2Z.inj_add. rewrite Z.add_comm. reflexivity. rewrite H0.

    assert (two_p (Z.of_nat (size (a :: xs))) < two_p (Z.of_nat (size (a :: xs)) + 1))%Z.
    rewrite two_p_equiv.
    rewrite two_p_equiv.
    rewrite Z.pow_add_r.
    lia.
    lia. lia.
    unfold Int64.convert_from_bits_to_Z_one_bits. fold (Int64.convert_from_bits_to_Z_one_bits (a :: xs)). lia. }
  induction l. now intros.
  intros i Hi1 Hi2 Hi3 Hk.
  have Hds := H0 l a.
  simpl in Hi1.
  simpl in Hi2.
  simpl in Hi3.
  remember (a :: l) as xs.
  destruct a.
  simpl in *. rewrite Hi2.
  simpl.
  rewrite Nat.sub_0_r.
  assert (two_p (Z.of_nat (size xs)) = two_power_pos (Pos.of_succ_nat (size l))). subst xs. cbn. reflexivity.
  rewrite <-H1 in Hds.
  assert (size xs - 1 = size l). subst xs. cbn. lia.
  rewrite H2. rewrite Heqxs. simpl. assert (Z.of_nat (size l) + 1 = Z.of_nat (size xs))%Z. subst xs. simpl. lia. rewrite H3. assumption.
  simpl in Hds.
  assert (two_p (Z.of_nat (size xs)) = two_power_pos (Pos.of_succ_nat (size l))). subst xs. cbn. reflexivity.
  simpl in H1.
  rewrite <-H1 in Hds.
  simpl.
  assert (Zbits.powerserie (Int64.convert_from_bits_to_Z_one_bits xs) = Zbits.powerserie (Int64.convert_from_bits_to_Z_one_bits l)). {
    subst xs. cbn. reflexivity. }
  rewrite H2.
  simpl in Hi2.
  assert (i - 1 < size l). rewrite Hi2. simpl. rewrite Nat.sub_0_r. lia.
  assert (i - 1 = find (fun b => b == true) l). subst i. cbn. lia.
  assert ((nth false l (i - 1) == true) = true).
  rewrite Hi2. simpl. rewrite Nat.sub_0_r.
  rewrite Hi2 in Hi3. simpl in Hi3. assumption.
  assert (forall k, k < (i - 1) -> (nth false l k == true) = false).
  intros k Hk'.
  assert (ssrnat.leq (S k) (find (fun b => b == true) l)). rewrite -?(rwP ssrnat.leP). lia.      have Hbf := before_find _ H6.
  simpl in Hbf. apply Hbf.
  have IH := IHl (i - 1) H3 H4 H5 H6.
  simpl in IH.
  assert (size l - (i - 1) = size l + 1 - i). lia. rewrite H7 in IH.
  assert (size xs = size l + 1). subst xs. cbn. lia. rewrite H8.
  assumption.
Qed.

Lemma clz_last : forall x i,
  i < Int64.wordsize ->
  i = Z.to_nat (Int64.intval (Int64.clz x)) ->
  (Int64.intval x < two_p (Z.of_nat (Int64.wordsize - i)))%Z.
Proof.
  intros x i Hi Hclz.
  unfold Int64.clz in Hclz.
  remember (Z.of_nat (Int64.wordsize - i - 1)) as j eqn:Hj.
  remember (Z.of_nat (ssrnat.subn (ssrnat.subn Int64.wordsize i) 1)) as j' eqn:Hj'.
  assert (j = j') by now rewrite <- ssrnat.minusE in Hj'.
  remember (fun b : Datatypes_bool__canonical__eqtype_Equality => b == true) as a eqn:Ha.
  remember (Int64.intval x) as x' eqn:Hx'.
  remember (Int64.wordsize) as n eqn:Hn.
  remember (j' \in Zbits.Z_one_bits n x' 0) as inbits eqn:Hinbits.
  assert (nth false (Int64.convert_to_bits x) i = inbits). {
    rewrite Hinbits. rewrite  Hj'. rewrite Hn. rewrite  Hx'.
    apply Int64.convert_to_bits_nth. rewrite Hn in Hi.
    rewrite -?(rwP ssrnat.leP). lia.  }
  remember (Int64.convert_to_bits x) as s eqn:Hs.
  have Hsize := Int64.convert_to_bits_size x. rewrite <-Hs in Hsize.
  have : Int64.wordsize = 64. by unfold Int64.wordsize, Integers.Wordsize_64.wordsize.
  intro Hws.
  have : find a s <= 64.
  have Hsize' := find_size a s. rewrite <-Hws.
  rewrite -?(rwP ssrnat.leP) in Hsize'. simpl in Hsize'. rewrite Hsize in  Hsize'. auto.
  intro Hfindleq. simpl in Hfindleq.
  have : (Int64.intval (Z_to_i64 (find a s)) = Z.of_nat (find a s)).
  unfold Z_to_i64. simpl.
  rewrite Int64.Z_mod_modulus_id. reflexivity.
  rewrite int64_modulus_eq_pow64. cbn. lia.
  intro Hint.
  have : (i = find a s).
  rewrite Hint in Hclz. by rewrite Nat2Z.id in Hclz.
  intro Hieq. simpl in Hieq.
  have : has a s. rewrite has_find. rewrite -?(rwP ssrnat.leP). simpl. rewrite <-Hieq. rewrite ->Hsize, ->Hws. lia.
  intro Hhas.
  have :  a inbits.
  rewrite Hj' in Hinbits. rewrite Hn in Hinbits. rewrite Hx' in Hinbits.
  rewrite <-Int64.convert_to_bits_nth in Hinbits. rewrite Hieq in Hinbits. rewrite  Hs in Hinbits.
  rewrite Hinbits.
  apply nth_find. by subst s.
  rewrite -?(rwP ssrnat.leP). rewrite Hws. lia.
  intro Hinbits'.
  rewrite Ha in Hinbits'. rewrite eqb_id in Hinbits'.
  have Hsize' := find_size a s. rewrite (rwP ssrnat.leP) in Hfindleq.
  have : forall k, k < i -> a (nth false s k) = false. intros k Hk.
  have : (ssrnat.leq (S k) (find a s)). rewrite -?(rwP ssrnat.leP). simpl. rewrite <- Hieq. lia.
  intro.
  now apply before_find.
  intro Hbefore.
  assert (a (nth false s i) = true).
  rewrite Hieq.
  apply nth_find.
  assumption.
  have Hkl := convert_from_bits_head s i.
  assert (i < size s).
  rewrite has_find in Hhas. rewrite -?(rwP ssrnat.leP) in Hhas. lia.
  simpl in Hkl.
  rewrite Ha in Hieq. rewrite Ha in H1. rewrite Ha in Hbefore.
  specialize (Hkl H2 Hieq H1 Hbefore).
  rewrite Hsize in Hkl. rewrite Hws in Hkl.
  rewrite Hsize in H2.
  rewrite Hws in H2.
  rewrite Hn.
  rewrite Hws.
  assert (Z.of_nat (64 - i - 1) = Z.of_nat (63 - i))%Z by lia. rewrite H3 in Hkl.
  assert (Z.of_nat (63 - i) + 1 = Z.of_nat (64 - i))%Z by lia. rewrite H4 in Hkl.
  assert (two_p (Z.of_nat (64 - i)) <= Int64.modulus)%Z.
  rewrite two_p_equiv in Hkl.
  rewrite int64_modulus_eq_pow64. rewrite Nat2Z.inj_sub in Hkl. replace (Z.of_nat 64) with 64%Z in Hkl by lia.
  rewrite two_p_equiv.

  replace (Z.of_nat (64 - i))%Z with (64 - Z.of_nat i)%Z by lia.
  apply Z.pow_le_mono_r. lia. lia. lia.
  assert (forall l,
             0 <= Zbits.powerserie (Int64.convert_from_bits_to_Z_one_bits l))%Z. {
    induction l.
    cbn. lia.
    cbn.
    destruct a0.
    cbn.
    assert (two_p (Z.of_nat (size l)) > 0)%Z. apply two_p_gt_ZERO. lia. lia. lia. }

  assert (Zbits.powerserie (Int64.convert_from_bits_to_Z_one_bits s) < Int64.modulus)%Z by lia.
  have Hlow := H6 s.
  assert (Int64.intval (Int64.repr (Zbits.powerserie (Int64.convert_from_bits_to_Z_one_bits s))) = (Zbits.powerserie (Int64.convert_from_bits_to_Z_one_bits s))). {
    simpl. rewrite Int64.Z_mod_modulus_id. reflexivity. lia. }
  assert (x' = Zbits.powerserie (Int64.convert_from_bits_to_Z_one_bits s)).
    have : x = Int64.convert_from_bits (Int64.convert_to_bits x).
    apply Int64.convert_to_from_bits.
    intro Htofrom.
    unfold Int64.convert_from_bits in Htofrom.
    rewrite Hx'. rewrite Htofrom.
    rewrite Hs. rewrite Hs in H8.
    rewrite H8. reflexivity.
    rewrite H9. assumption.
Qed.

Lemma clz_lowerbound : forall x i,
  (-1 < Int64.intval x < Int64.modulus)%Z ->
  i < Int64.wordsize ->
  i = Z.to_nat (Int64.intval (Int64.clz x)) ->
  (two_power_nat (Int64.wordsize - i - 1) <= Int64.intval x)%Z.
Proof.
  intros x i Hrange Hi Hclz.
  unfold Int64.clz in Hclz.
  remember (Z.of_nat (Int64.wordsize - i - 1)) as j eqn:Hj.
  remember (Z.of_nat (ssrnat.subn (ssrnat.subn Int64.wordsize i) 1)) as j' eqn:Hj'.
  assert (j = j') by now rewrite <- ssrnat.minusE in Hj'.
  remember (fun b : Datatypes_bool__canonical__eqtype_Equality => b == true) as a eqn:Ha.
  remember (Int64.intval x) as x' eqn:Hx'.
  remember (Int64.wordsize) as n eqn:Hn.
  remember (j' \in Zbits.Z_one_bits n x' 0) as inbits eqn:Hinbits.
  assert (nth false (Int64.convert_to_bits x) i = inbits). {
    rewrite Hinbits. rewrite  Hj'. rewrite Hn. rewrite  Hx'.
    apply Int64.convert_to_bits_nth. rewrite Hn in Hi.
    rewrite -?(rwP ssrnat.leP). lia.  }
  remember (Int64.convert_to_bits x) as s eqn:Hs.
  have Hsize := Int64.convert_to_bits_size x. rewrite <-Hs in Hsize.
  have : Int64.wordsize = 64. by unfold Int64.wordsize, Integers.Wordsize_64.wordsize.
  intro Hws.
  have : find a s <= 64.
  have Hsize' := find_size a s. rewrite <-Hws.
  rewrite -?(rwP ssrnat.leP) in Hsize'. simpl in Hsize'. rewrite Hsize in  Hsize'. auto.
  intro Hfindleq. simpl in Hfindleq.
  have : (Int64.intval (Z_to_i64 (find a s)) = Z.of_nat (find a s)).
  unfold Z_to_i64. simpl.
  rewrite Int64.Z_mod_modulus_id. reflexivity.
  rewrite int64_modulus_eq_pow64. cbn. lia.
  intro Hint.
  have : (i = find a s).
  rewrite Hint in Hclz. by rewrite Nat2Z.id in Hclz.
  intro Hieq. simpl in Hieq.
  have : has a s. rewrite has_find. rewrite -?(rwP ssrnat.leP). simpl. rewrite <-Hieq. rewrite ->Hsize, ->Hws. lia.
  intro Hhas.
  have :  a inbits.
  rewrite Hj' in Hinbits. rewrite Hn in Hinbits. rewrite Hx' in Hinbits.
  rewrite <-Int64.convert_to_bits_nth in Hinbits. rewrite Hieq in Hinbits. rewrite  Hs in Hinbits.
  rewrite Hinbits.
  apply nth_find. by subst s.
  rewrite -?(rwP ssrnat.leP). rewrite Hws. lia.
  intro Hinbits'.
  rewrite Ha in Hinbits'. rewrite eqb_id in Hinbits'.
  have Hsize' := find_size a s. rewrite (rwP ssrnat.leP) in Hfindleq.
  assert (forall k, In k (Zbits.Z_one_bits Int64.wordsize (Int64.intval x) 0) -> 0 <= k)%Z. {
    intros k Hk.
    have Hk' := Zbits.Z_one_bits_range _ _ _ Hk; lia. }
  assert (Hx'': (0 <= (Int64.intval x) < two_power_nat Int64.wordsize)%Z).
  rewrite two_power_nat_equiv. unfold Int64.wordsize, Integers.Wordsize_64.wordsize. rewrite int64_modulus_eq_pow64 in Hrange. lia.
  have Hpow := Zbits.Z_one_bits_powerserie 64 (Int64.intval x) Hx''.
  rewrite two_power_nat_equiv.
  rewrite Hx'. rewrite Hpow.
  have Hpow' := in_Z_one_bits_pow.
  specialize (Hpow' (Zbits.Z_one_bits 64 (Int64.intval x) 0)).
  specialize (Hpow' j).
  rewrite <-H in Hinbits. rewrite Hinbits in Hinbits'.
  rewrite Hn in Hinbits'. rewrite Hws in Hinbits'. rewrite Hx' in Hinbits'.
  specialize (Hpow' Hinbits').
  rewrite Hws in H1.
  specialize (Hpow' H1).
  rewrite <-Hj . assumption.
Qed.

Lemma clz_spec : forall x,
  (0 < x < Int64.modulus)%Z ->
  (2^63 <= 2^(Int64.intval (Int64.clz (Int64.repr x))) * x < 2^64)%Z.
Proof.
  intros x Hx.
  have Hclz_last := clz_last.
  assert (Hsize : size (Int64.convert_to_bits (Z_to_i64 x)) = Int64.wordsize).
  apply Int64.convert_to_bits_size.
  remember (Int64.intval (Int64.clz (Z_to_i64 x))) as i eqn:Hi.
  assert (0 <= Int64.intval (Int64.clz (Z_to_i64 x)) < Int64.wordsize)%Z.
  have Hi' := Hi.
  unfold Int64.clz in Hi.
  remember (Int64.convert_to_bits (Z_to_i64 x)) as bits eqn:Hc2b.
  remember (fun b => b == true) as a eqn:Ha.
  assert (0 <= Z.of_nat (find a bits))%Z. lia.
  assert (ssrnat.leq (find a bits) Int64.wordsize)%Z.
  rewrite <-Hsize. apply find_size.
  rewrite -?(rwP ssrnat.leP) in H0.
  unfold Int64.clz.
  rewrite <- Hc2b. rewrite <-Ha.
  destruct (le_lt_eq_dec (find a bits) Int64.wordsize) as [Hlt|Heq]. assumption.
  simpl.
  rewrite Int64.Z_mod_modulus_id. unfold Int64.wordsize, Integers.Wordsize_64.wordsize in Hlt. simpl in Hlt. lia.
  unfold Int64.wordsize, Integers.Wordsize_64.wordsize in Hlt. simpl in Hlt.
  rewrite int64_modulus_eq_pow64. lia.
  rewrite Heq in Hi.
  simpl in Hi.
  assert (Int64.repr x = Int64.repr 0).
  apply Int64.clz_wordsize.
  remember (Int64.clz (Z_to_i64 x)) as clz eqn:Hclz.
  assert (Int64.intval (Z_to_i64 i) = (Int64.intval clz)).
  rewrite Hi'. simpl.
  rewrite Int64.Z_mod_modulus_id. reflexivity. rewrite <-Hi'. rewrite Hi. rewrite int64_modulus_eq_pow64. lia.

  apply Int64.eq_T_intval in H1.
  rewrite <-H1. simpl. now rewrite Hi.
  apply Int64.repr_inv in H1. lia. lia. lia.
  assert (Z.to_nat i < Int64.wordsize). lia.
  specialize (Hclz_last (Int64.repr x) (Z.to_nat i) H0).
  rewrite <-Hi in Hclz_last. specialize (Hclz_last Logic.eq_refl).
  replace (Int64.intval (Z_to_i64 x)) with x in Hclz_last. 2: simpl; rewrite Int64.Z_mod_modulus_id; lia.
  rewrite Nat2Z.inj_sub in Hclz_last. 2: lia.

  rewrite Z2Nat.id in Hclz_last.
  replace (Z.of_nat Int64.wordsize) with 64%Z in Hclz_last by now cbn.
  rewrite two_p_equiv in Hclz_last.
  assert (2^i * x < 2^64)%Z.
  replace (2^64)%Z with (2^i * 2^(64 - i))%Z.
  apply Zmult_lt_compat_l. lia. lia.
  rewrite <-Z.pow_add_r. replace (i + (64 - i))%Z with 64%Z by lia. reflexivity. lia.
  unfold Int64.wordsize, Integers.Wordsize_64.wordsize in H0. lia.
  assert (2^63 <= 2^i * x)%Z.
  have Hlower := clz_lowerbound.
  assert (-1 < Int64.intval x < Int64.modulus)%Z. simpl. rewrite Int64.Z_mod_modulus_id; lia.
  specialize (Hlower (Int64.repr x) (Z.to_nat i) H2 H0).
  rewrite <-Hi in Hlower.
  specialize (Hlower Logic.eq_refl).
  rewrite two_power_nat_equiv in Hlower.
  replace (Int64.intval (Int64.repr x)) with x in Hlower.
  unfold Int64.wordsize, Integers.Wordsize_64.wordsize in Hlower.
  assert (Z.of_nat (64 - Z.to_nat i - 1) = 63 - i)%Z. rewrite Nat2Z.inj_sub. rewrite Nat2Z.inj_sub. lia. unfold Int64.wordsize, Integers.Wordsize_64.wordsize in H0. lia. unfold Int64.wordsize, Integers.Wordsize_64.wordsize in H0. lia.
  rewrite H3 in Hlower.
  assert (2^(63 - i) = 2^63/2^i)%Z.
  rewrite Z.pow_sub_r; lia.
  assert ((2^i * x) / 2^i = x)%Z.
  rewrite Z.mul_comm. rewrite Z_div_mult. reflexivity.
  lia.
  assert (63 = (63 - i) + i)%Z. lia.
  rewrite H6.
  rewrite Z.pow_add_r.
  rewrite Z.mul_comm.
  apply Zmult_le_compat. lia.  assumption.  lia.  lia. lia.
  lia.
  simpl. rewrite Int64.Z_mod_modulus_id; lia.
  lia. lia.
Qed.

Lemma clz_spec_alt : forall x,
  (0 < x < Int64.modulus)%Z ->
  Int64.intval (Int64.clz (Int64.repr x)) = (63 - Z.log2 (Int64.intval (Int64.repr x)))%Z.
Proof.
  intros.
  have H' := clz_spec _ H.
  destruct H' as [Hle1 Hle2].
  assert (Hlog1: (Z.log2 (2^63) <= Z.log2 (2 ^ (Int64.intval (Int64.clz (Int64.repr x))) * x))%Z) by (apply Z.log2_le_mono; assumption).
  assert (Hlog2: (Z.log2 (2 ^ (Int64.intval (Int64.clz (Int64.repr x))) * x) < 64)%Z) by (apply Z.log2_lt_pow2; lia).
  replace (2 ^ (Int64.intval (Int64.clz (Int64.repr x))) * x)%Z with (x * 2 ^ (Int64.intval (Int64.clz (Int64.repr x))))%Z in Hlog1, Hlog2 by lia.
  rewrite Z.log2_mul_pow2 in Hlog1, Hlog2.
  replace (Z.log2 (2 ^ 63)) with 63%Z in Hlog1 by (rewrite Z.log2_pow2; lia).
  replace (Int64.intval (Z_to_i64 x)) with x.
  lia.
  simpl. rewrite Int64.Z_mod_modulus_id; lia. lia.
  unfold Int64.clz.
  assert (forall n, 0 <= Int64.intval (Z_to_i64 (Z.of_nat n)))%Z. intro. simpl.
  rewrite Int64.Z_mod_modulus_eq. lia.
  apply H0.
Qed.

Lemma head0_int64_clz : forall x,
  (0 < to_Z x)%Z ->
  to_Z (head0 x) = (Int64.unsigned (Int64.clz (Int64.repr (to_Z x))) - 1)%Z.
Proof.
  intros.
  unfold Int64.unsigned.
  rewrite clz_spec_alt.
  replace (63 - Z.log2 (Int64.intval (Z_to_i64 φ (x)%uint63)) - 1)%Z with (62 - Z.log2 (Int64.intval (Z_to_i64 φ (x)%uint63)))%Z by lia.
  replace (Int64.intval (Z_to_i64 (to_Z x))) with (to_Z  x). rewrite head0_spec_alt; auto.
  simpl. rewrite uint63_mod_modulus_id.
  reflexivity. auto.
  rewrite int64_modulus_eq_pow64. split; auto. apply uint63_lt_pow64.
Qed.

(* tail0 related *)

Lemma powerserie_convert_from_bits_rev : forall l i,
  i < size l ->
  i = find (fun b => b == true)  (rev l) ->
  (fun b => b == true) (nth false (rev l) i) = true ->
  (forall k, k < i -> (fun b => b == true) (nth false (rev l) k) = false) ->
  exists y,
    Zbits.powerserie (Int64.convert_from_bits_to_Z_one_bits l) = ((y * 2 + 1) * 2^i)%Z.
Proof.
  induction l.
  now intros.
  intros i Hsize Hfind Hnth Hbefore.
  assert (ssrnat.leq (S i) (size (a :: l))).
  simpl. simpl in Hsize.
  rewrite -?(rwP ssrnat.leP). lia.
  destruct (size l - i) eqn:Hdiff.
  { (* Special case? is is the index of the _last_ 1 bit in (a :: l), i.e. i = size l *)
    have Hnth' := Hnth.
    rewrite nth_rev in Hnth'.
    assert (Hsize' : i = size l). simpl in Hsize, Hdiff |-*. lia.
    unfold ssrnat.subn in Hnth'; simpl in Hnth'.
    rewrite Hdiff in Hnth'.
    simpl in Hnth'.
    rewrite eqb_id in Hnth'. rewrite Hnth'.
    simpl. rewrite two_p_equiv. rewrite Hsize'.
    remember (Zbits.powerserie (Int64.convert_from_bits_to_Z_one_bits l)) as ps eqn:Hps.
    have Hbefore' := Hbefore.
    assert (Hps0 : forall l' i',
               i' = size l' ->
               (forall k : nat, k < i' -> (nth false (rev l') k == true) = false) ->
               Zbits.powerserie (Int64.convert_from_bits_to_Z_one_bits l') = 0). {
      induction l'. now intros.
      intros.
      have : (nth false (a0 :: l') 0 == true) = false.
      assert ((i' - 1) < i'). simpl in H0. simpl. lia.
      apply H1 in H2.
      rewrite nth_rev in H2. rewrite <-H0 in H2.
      unfold ssrnat.subn in H2. simpl in H2.
      assert (i' - S (i' - 1) = 0). lia. rewrite H3 in H2. assumption.
      rewrite -(rwP ssrnat.leP). simpl in H0 |- *. lia.
      intro Ha0.
      rewrite eqb_id in Ha0. simpl in Ha0.
      rewrite Ha0. simpl.
      apply IHl' with (i' - 1). simpl in H0 |- *. lia.
      intros k Hk.
      have Hrcons := rev_cons a0 l'.
      have Hnc := nth_rcons false (rev l') a0 k.
      assert (Hk' : k < i'). lia.
      have Hbf' := H1 k Hk'.
      rewrite Hrcons in Hbf'.
      assert (ssrnat.leq (S k) (size (rev l'))).
      rewrite -(rwP ssrnat.leP). simpl. rewrite size_rev. simpl in H0. lia.
      rewrite H2 in Hnc. rewrite <- Hnc. assumption.  }

    have : ps = 0%Z.
    rewrite Hps. apply Hps0 with (i':=i); auto.
    intros k Hk.
    have Hrcons := rev_cons a l.
    have Hnc := nth_rcons false (rev l) a k.
    assert (Hk' : k < i). lia.
    have Hbf' := Hbefore k Hk'.
    rewrite Hrcons in Hbf'.
    assert (ssrnat.leq (S k) (size (rev l))).
    rewrite -(rwP ssrnat.leP). simpl. rewrite size_rev. simpl. simpl in Hsize'. rewrite <-Hsize'. lia.
    rewrite H0 in Hnc.
    simpl. simpl in Hnc.
    rewrite <- Hnc. assumption.
    intro Hps0'. exists 0%Z.
    rewrite Z.mul_0_l.
    rewrite Z.add_0_l.
    rewrite Hps0'. rewrite Z.add_0_r.
    rewrite Z.mul_1_l. reflexivity.
    rewrite -(rwP ssrnat.leP). simpl. simpl in Hsize. lia. }
  { (* inductive case: i < size l *)
  assert (Hsize' : i = size l - S n). lia. assert (Hn : n < size l). lia.
  assert (Hnth' : (nth false (rev l) i) == true).
  assert (Hsize'' : (size l) - (S n) = i). by rewrite Hsize'.
  assert (Hsize''' :n = (size l) - (S i)). lia.
  rewrite nth_rev in Hnth; auto.
  rewrite nth_rev.
  rewrite ssrnat.subnE in Hnth |- *. simpl in Hnth |- *.
  rewrite eqb_id in Hnth.
  simpl in Hnth.
  rewrite Hdiff in Hnth. simpl in Hnth. simpl in Hsize'''. rewrite <-Hsize'''. rewrite eqb_id. assumption.
  rewrite -(rwP ssrnat.leP). simpl in Hsize', Hsize''. simpl in Hsize', Hdiff. lia.
  assert (Hfind' : i = find (fun b => b == true) (rev l)).
  rewrite <-cat1s in Hfind.
  rewrite rev_cat in Hfind. rewrite find_cat in Hfind.
  unfold ssrnat.addn in Hfind.
  destruct (has (fun b => b == true) (rev l)). assumption.
  simpl in Hfind. destruct a; simpl in Hfind. rewrite size_rev in Hfind. simpl in Hdiff, Hsize'. lia. rewrite size_rev in Hfind. simpl in Hdiff, Hsize'. lia.
  assert (Hbefore' : forall k, k < i -> (nth false (rev l) k == true) = false).
  intros k Hk.
  have Hbf := before_find.
  assert (ssrnat.leq (S k) i). rewrite -(rwP ssrnat.leP). lia. rewrite Hfind' in H0. apply Hbf with (x0:=false) in H0. assumption.
  assert (Hsizei : i < (size l)). lia.
  have IH := IHl i Hsizei Hfind' Hnth' Hbefore'.
  destruct IH as [y Hy].
  simpl. destruct a.
  exists (2^(size l - i - 1) + y)%Z.
  rewrite [((2 ^ (size l - i - 1) + y) * 2)%Z] Z.mul_add_distr_r.
  replace 2%Z with (2^1)%Z at 2. rewrite <- Z.pow_add_r. rewrite Z.sub_add.
  rewrite Z.mul_add_distr_r.
  rewrite Z.mul_add_distr_r. rewrite <- Z.pow_add_r. rewrite Z.sub_add.
  rewrite <-Z.add_assoc. rewrite <-Z.mul_add_distr_r.
  simpl. rewrite two_p_equiv.
  rewrite Hy. reflexivity. simpl in Hsize'.  lia. lia. lia. lia. lia.
  exists y. assumption. }
Qed.

Lemma to_from_bits_modulus : forall x,
  (-1 < x < Int64.modulus)%Z ->
  x = Zbits.powerserie (Int64.convert_from_bits_to_Z_one_bits (Int64.convert_to_bits (Int64.repr x))).
Proof.
  intros x Hx.
  rewrite Int64.convert_from_bits_to_Z_one_bits_power_index_to_bits.
  have E: filter (fun x => Coqlib.zlt x Int64.wordsize) (Zbits.Z_one_bits Int64.wordsize (Int64.intval x) 0) = Zbits.Z_one_bits Int64.wordsize (Int64.intval x) 0.
  rewrite filter_for_all => //.
  rewrite list_all_forall => e. rewrite -List_In_in_mem => I.
  apply Int64.Zbits_Z_one_bits_range in I. destruct Coqlib.zlt => //. lia.
  rewrite E.
  replace (Int64.intval (Z_to_i64_co x)) with x.
  apply Zbits.Z_one_bits_powerserie.
  rewrite int64_modulus_eq_pow64 in Hx. unfold Int64.wordsize, Integers.Wordsize_64.wordsize.
  unfold two_power_nat. simpl. lia.
  simpl. rewrite Int64.Z_mod_modulus_id; lia.
  by apply Int64.Zbits_Z_one_bits_uniq.
Qed.

Lemma ctz_non_zero : forall x i,
  (0 < x < Int64.modulus)%Z ->
  i < Int64.wordsize ->
  i = Z.to_nat (Int64.intval (Int64.ctz (Int64.repr x))) ->
  exists y,
    (x = (y * 2 + 1) * 2^i)%Z.
Proof.
  intros x i Hx Hi Hctz.
  unfold Int64.ctz in Hctz.
  remember (Int64.convert_to_bits (Int64.repr x)) as s eqn:Hs.
  have Hsize := Int64.convert_to_bits_size (Int64.repr x). rewrite <-Hs in Hsize.
  have : Int64.wordsize = 64. by unfold Int64.wordsize, Integers.Wordsize_64.wordsize.
  intro Hws.
  have : i = find (fun b => b == true) (rev s).
  rewrite Hctz. cbn. rewrite Int64.Z_mod_modulus_id.
  rewrite Nat2Z.id. reflexivity.
  have : find (fun b => b == true) (rev s) <= size (rev s).
  rewrite (rwP ssrnat.leP).
  apply find_size.
  rewrite size_rev.
  cbn.
  intro Hfindsize.
  rewrite int64_modulus_eq_pow64.
  lia.
  have Hex := powerserie_convert_from_bits_rev.
  assert (Hleq : ssrnat.leq (S i) (size (rev s))).
  rewrite -(rwP ssrnat.leP).
  rewrite size_rev. rewrite Hsize.  rewrite Hws in Hi. lia.
  intro Hifind.
  have Hnth := Hleq.
  rewrite Hifind in Hnth.
  rewrite <-has_find in Hnth.
  apply nth_find with (x0:=false) in Hnth.
  assert ((nth false (rev s) i == true) = true).
  rewrite Hifind. auto.
  have Hbefore := before_find.
  assert (Hbf: forall k, k < i -> (nth false (rev s) k == true) = false). {
    intros k Hk.
    specialize (Hbefore (Equality.sort Datatypes_bool__canonical__eqtype_Equality) false (fun b => b == true) (rev s) k).
    rewrite <-Hifind in Hbefore.
    apply Hbefore.
    rewrite -(rwP ssrnat.leP). lia. }
  assert (Hisize : i < size s). rewrite Hws in Hi. lia.
  assert (Hinth : (nth false (rev s) i == true) = true). rewrite Hifind; auto.
  specialize (Hex s i Hisize Hifind Hinth Hbf).
  destruct Hex as [c Hc].
  assert (x = Zbits.powerserie (Int64.convert_from_bits_to_Z_one_bits s)).
  rewrite Hs. apply to_from_bits_modulus. lia.
  exists c. now subst x.
Qed.

Lemma ctz_spec : forall x,
  (0 < x < Int64.modulus)%Z ->
  exists y, (x = (y * 2 + 1) * 2^(Int64.unsigned (Int64.ctz (Int64.repr x))))%Z.
Proof.
intros x Hx.
have Hctz := ctz_non_zero.
assert (Hsize : size (Int64.convert_to_bits (Z_to_i64 x)) = Int64.wordsize).
apply Int64.convert_to_bits_size.
remember (Int64.intval (Int64.ctz (Z_to_i64 x))) as i eqn:Hi.
assert (0 <= Int64.intval (Int64.ctz (Z_to_i64 x)) < Int64.wordsize)%Z.
have Hi' := Hi.
unfold Int64.ctz in Hi.
remember (Int64.convert_to_bits (Z_to_i64 x)) as bits eqn:Hc2b.
remember (fun b => b == true) as a eqn:Ha.
assert (0 <= Z.of_nat (find a (rev bits)))%Z. lia.
assert (ssrnat.leq (find a (rev bits)) Int64.wordsize)%Z.
rewrite <-Hsize. rewrite <-size_rev.  apply find_size.
rewrite -?(rwP ssrnat.leP) in H0.
unfold Int64.ctz.
rewrite <- Hc2b. rewrite <-Ha.
destruct (le_lt_eq_dec (find a (rev bits)) Int64.wordsize) as [Hlt|Heq]. assumption.
cbn.
rewrite Int64.Z_mod_modulus_id. unfold Int64.wordsize, Integers.Wordsize_64.wordsize in Hlt. cbn in Hlt. lia.
unfold Int64.wordsize, Integers.Wordsize_64.wordsize in Hlt. cbn in Hlt.
rewrite int64_modulus_eq_pow64. lia.
rewrite Heq in Hi.
cbn in Hi.
assert (Int64.repr x = Int64.repr 0).
apply Int64.ctz_wordsize.
remember (Int64.ctz (Z_to_i64 x)) as ctz eqn:Hctzv.
assert (Int64.intval (Z_to_i64 i) = (Int64.intval ctz)).
rewrite Hi'. cbn.
rewrite Int64.Z_mod_modulus_id. reflexivity. rewrite <-Hi'. rewrite Hi. rewrite int64_modulus_eq_pow64. lia.
apply Int64.eq_T_intval in H1.
rewrite <-H1. simpl. now rewrite Hi.
apply Int64.repr_inv in H1. lia. lia. lia.
assert (Z.to_nat i < Int64.wordsize). lia.
specialize (Hctz x (Z.to_nat i) Hx H0).
rewrite Hi in Hctz. specialize (Hctz Logic.eq_refl).
replace (Int64.intval (Z_to_i64 x)) with x in Hctz. 2: cbn; rewrite Int64.Z_mod_modulus_id; lia.
rewrite Z2Nat.id in Hctz.
destruct Hctz as [c Hc].
unfold Int64.unsigned.
exists c. exact Hc.
lia.
Qed.

Lemma unique_greatest_power_of_two_divisor : forall x n m,
  (0 < x)%Z ->
  (0 <= n)%Z ->
  (0 <= m)%Z ->
  (exists y, x = (2 * y + 1) * 2^n)%Z ->
  (exists y', x = (2 * y' + 1) * 2^m)%Z ->
  n = m.
Proof.
  assert (forall i, 0 < i -> Z.odd (2^i) = false)%Z as Hpow2odd. {
    intros i Hi.
    replace (2^i)%Z with (2^(i - 1) * (2 ^ 1))%Z. rewrite Z.odd_mul. simpl. lia.
    rewrite <-Z.pow_add_r. now rewrite Z.sub_add.
    lia. lia. }
  intros x n m Hxnz Hnge0 Hmge0 [y Hxn] [y' Hxm].
  remember (2 * y + 1)%Z as a eqn:Ha.
  remember (2 * y' + 1)%Z as b eqn:Hb.
  assert (a * 2^n = b * 2^m)%Z as Heq. rewrite <- Hxn, <- Hxm. reflexivity.
  destruct (Z_lt_dec n  m) as [Hlt | Hnlt]. {
    assert (a = b * 2^(m - n))%Z as Ha'. {
      rewrite Z.pow_sub_r; [|lia|lia].
      rewrite <-Znumtheory.Zdivide_Zdiv_eq_2. 2: lia.
      replace a with (a * 2^n / 2^n)%Z by nia.
      rewrite <-Hxn. rewrite <-Hxm. reflexivity.
      exists (2^(m - n))%Z. rewrite <-Z.pow_add_r.
      now rewrite Z.sub_add. lia. lia. }
    assert (Z.odd a = true) as Hodda. {
      subst a.
      rewrite Z.add_comm. rewrite Z.odd_add_mul_2.
      reflexivity. }
    assert (Z.odd a = false) as Hodda'. {
      rewrite Ha'. rewrite Z.mul_comm.
      rewrite Z.odd_mul. rewrite Hpow2odd. reflexivity. lia. }
    rewrite Hodda' in Hodda. discriminate. }
  destruct (Z_lt_dec m n) as [Hlt' | Hnlt']. {
    assert (b = a * 2^(n - m))%Z as Hb'. {
      rewrite Z.pow_sub_r; [|lia|lia].
      rewrite <-Znumtheory.Zdivide_Zdiv_eq_2. 2: lia.
      replace b with (b * 2^m / 2^m)%Z by nia.
      rewrite <-Hxn. rewrite <-Hxm. reflexivity.
      exists (2^(n - m))%Z. rewrite <-Z.pow_add_r.
      now rewrite Z.sub_add. lia. lia. }
    assert (Z.odd b = true) as Hoddb. {
      subst b.
      rewrite Z.add_comm. rewrite Z.odd_add_mul_2.
      reflexivity. }
    assert (Z.odd b = false) as Hoddb'. {
      rewrite Hb'. rewrite Z.mul_comm.
      rewrite Z.odd_mul. rewrite Hpow2odd. reflexivity. lia. }
    rewrite Hoddb' in Hoddb. discriminate. }
  lia.
Qed.

Lemma tail0_int64_ctz : forall x,
  (0 < to_Z x)%Z ->
  Int64.repr (to_Z (tail0 x)) = (Int64.ctz (Int64.repr (to_Z x))).
Proof.
  intros.
  have HxBounded := to_Z_bounded x.
  assert (0 < to_Z x < Int64.modulus)%Z as HxBounded'. rewrite int64_modulus_eq_pow64. cbn in HxBounded. lia.
  have Hctz := ctz_spec (to_Z x) HxBounded'.
  have Htail0 := tail0_spec x H.
  assert (to_Z (tail0 x) = Int64.unsigned (Int64.ctz (Int64.repr (to_Z x)))). {
    apply unique_greatest_power_of_two_divisor with (x:=to_Z x); auto.
    destruct (to_Z_bounded (tail0 x)). lia.
    destruct (Int64.unsigned_range (Int64.ctz (Z_to_i64 φ (x)%uint63))). lia.
    destruct Htail0 as [y [_ Hy]]. exists y. auto.
    destruct Hctz as [y Hy]. rewrite - [(y * 2)%Z] Z.mul_comm in Hy.
    exists y; auto. }
  rewrite H0.
  rewrite Int64.repr_unsigned.
  reflexivity.
Qed.

End Primitives.
