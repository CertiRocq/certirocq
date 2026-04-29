From Wasm Require Import datatypes operations.

From Stdlib Require Import
  Program.Program
  Relations.Relations Relations.Relation_Operators
  Lia ZArith Nnat Uint63
  List Lists.ListDec.

From ExtLib Require Import Structures.Monad.

From CertiRocq Require Import
  LambdaANF.toplevel
  LambdaANF.term_util
  Common.Pipeline_utils
  Common.Common
  LambdaANF.term
  LambdaANF.cps_show.

From MetaRocq.Utils Require Import bytestring MRString.

Import MonadNotation compM ssreflect.

(* ***** RESTRICTIONS ON lANF EXPRESSIONS ****** *)
Definition max_function_args := 100%Z.       (* should be possible to vary without breaking much *)
Definition max_num_functions := 1_000_000%Z. (* should be possible to vary without breaking much *)
Definition max_constr_args   := 1024%Z.      (* should be possible to vary without breaking much *)

Definition max_constr_alloc_size := (max_constr_args * 4 + 4)%Z. (* bytes, don't change this *)

Definition assert (b : bool) (err : string) : error Datatypes.unit :=
  if b then Ret tt else Err err.

Definition get_ctor_ord (cenv : ctor_env) (t : ctor_tag) : error N:=
  match M.get t cenv with
  | Some c => Ret (ctor_ordinal c)
  | None => Err ("Constructor with tag " ++ (string_of_positive t) ++ " in constructor expression not found in constructor environment")%bs
  end.


(* enforces size restrictions on the lambdaANF expression *)
Fixpoint check_restrictions (cenv : ctor_env) (e : exp) : error Datatypes.unit :=
  match e with
  | Econstr _ t ys e' =>
      ord <- get_ctor_ord cenv t ;;
      _ <- assert (Z.of_N ord <? Wasm_int.Int32.half_modulus)%Z "Constructor ordinal too large" ;;
      _ <- assert (Z.of_nat (Datatypes.length ys) <=? max_constr_args)%Z
             "found constructor with too many args, check max_constr_args";;
      check_restrictions cenv e'
  | Ecase x ms =>
      (* _ <- check_case_list_ordinals cenv ms;; *)
      _ <- sequence (map (fun '(t, e') =>
                            ord <- get_ctor_ord cenv t ;;
                            _ <- assert (Z.of_N ord <? Wasm_int.Int32.half_modulus)%Z "Constructor ordinal too large" ;;
                            check_restrictions cenv e') ms) ;;
      Ret tt
  | Eproj _ _ _ _ e' => check_restrictions cenv  e'
  | Eletapp _ _ _ ys e' =>
      _ <- assert (Z.of_nat (Datatypes.length ys) <=? max_function_args)%Z
                "found function application with too many function params, check max_function_args";;
      check_restrictions cenv e'
  | Efun fds e' =>
      _ <- assert (Z.of_nat (numOf_fundefs fds) <=? max_num_functions)%Z
                "too many functions, check max_num_functions";;
      _ <- ((fix iter (fds : fundefs) : error Datatypes.unit :=
              match fds with
              | Fnil => Ret tt
              | Fcons _ _ ys e' fds' =>
                  _ <- assert (Z.of_nat (length ys) <=? max_function_args)%Z
                       "found fundef with too many function args, check max_function_args";;
                  _ <- (iter fds');;
                  check_restrictions cenv e'
              end) fds);;
      check_restrictions cenv e'
  | Eapp _ _ ys => assert (Z.of_nat (Datatypes.length ys) <=? max_function_args)%Z
                        "found function application with too many function params, check max_function_args"
  | Eprim_val _ _ e' => check_restrictions cenv e'
  | Eprim _ _ _ e' => check_restrictions cenv e'
  | Ehalt _ => Ret tt
  end.


(* copy-pasted from C backend TODO: move this to term_util *)
Definition Forall_constructors_in_e (P: var -> ctor_tag -> list var -> Prop) (e:exp) :=
  forall x t  ys e',
    subterm_or_eq (Econstr x t ys e') e -> P x t ys.

Definition Forall_exp_in_caselist (P: exp -> Prop) (cl:list (ctor_tag * exp)) :=
  forall g e, List.In (g, e) cl -> P e.

Lemma crt_incl_ct:
          forall T P e e',
          clos_trans T P e e' ->
          clos_refl_trans T P e e'.
Proof.
  intros. induction H. constructor; auto.
  eapply rt_trans; eauto.
Qed.

Lemma Forall_constructors_subterm:
  forall P e e' ,
  Forall_constructors_in_e P e ->
  subterm_e e' e ->
  Forall_constructors_in_e P e'.
Proof.
  intros. intro; intros.
  eapply H.
  assert (subterm_or_eq e' e).
  apply crt_incl_ct.
  apply H0.
  eapply rt_trans; eauto.
Qed.

Lemma Forall_constructors_in_constr:
  forall P x t ys e,
  Forall_constructors_in_e P (Econstr x t ys e) ->
  P x t ys.
Proof.
  intros.
  unfold Forall_constructors_in_e in *.
  eapply H.
  apply rt_refl.
Qed.

Lemma find_def_dsubterm_fds_e : forall fds f t ys e,
   find_def f fds = Some (t, ys, e) ->
   dsubterm_fds_e e fds.
Proof.
  induction fds; intros. 2: inv H.
  cbn in H. destruct (M.elt_eq f0 v).
  (* f0=v *) inv H. constructor.
  (* f0<>v *) constructor. eapply IHfds; eauto.
Qed.

(* END move to term_util *)


(* TODO: incorporate into expression_restricted *)
(* all constructors in the exp exists in cenv and are applied to
   the right number of args *)
Definition correct_cenv_of_exp: LambdaANF.term.ctor_env -> exp -> Prop :=
    fun cenv e =>
      Forall_constructors_in_e (fun x t ys =>
                                  match (M.get t cenv) with
                                  | Some (Build_ctor_ty_info _ _ _ a ord) =>
                                    N.of_nat (length ys) = a
                                  | None => False
                                  end) e.

(* All constructors in the constr. env satisfy the following:
   1. The ordinals of all nullary constructors are different
   2. The ordinals of all non-nullary constructors are different *)
Definition cenv_restricted (cenv : ctor_env) : Prop :=
  forall t name iname it a ord,
    M.get t cenv = Some (Build_ctor_ty_info name iname it a ord) ->
    forall t',
      t <> t' ->
      (a = 0%N -> ~ (exists name' iname', M.get t' cenv = Some (Build_ctor_ty_info name' iname' it 0%N ord))) /\
        ((0 < a)%N -> ~ (exists name' iname' a', M.get t' cenv = Some (Build_ctor_ty_info name' iname' it a' ord))).

Definition ctor_ordinal_restricted (cenv : ctor_env) (t : ctor_tag) : Prop :=
  forall n, get_ctor_ord cenv t = Ret n ->
      (Z.of_N n < Wasm_int.Int32.half_modulus)%Z.


Inductive expression_restricted : ctor_env -> term.exp -> Prop :=
| ER_constr : forall x t ys e cenv,
    ctor_ordinal_restricted cenv t ->
      (Z.of_nat (Datatypes.length ys) <= max_constr_args)%Z ->
      expression_restricted cenv e ->
      expression_restricted cenv (Econstr x t ys e)
  | ER_case : forall x ms cenv,
      Forall (fun p =>
                ctor_ordinal_restricted cenv (fst p) /\
                        expression_restricted cenv (snd p)) ms ->
      expression_restricted cenv (Ecase x ms)
  | ER_proj : forall x t n y e cenv,
      expression_restricted cenv e ->
      expression_restricted cenv (Eproj x t n y e)
  | ER_letapp : forall f x ft ys e cenv,
      expression_restricted cenv e ->
      (Z.of_nat (Datatypes.length ys) <= max_function_args)%Z ->
      expression_restricted cenv (Eletapp x f ft ys e)
  | ER_fun : forall e fds cenv,
      expression_restricted cenv e ->
      (forall f t ys e', find_def f fds = Some (t, ys, e') ->
                   Z.of_nat (length ys) <= max_function_args /\
                   expression_restricted cenv e')%Z ->
      (Z.of_nat (numOf_fundefs fds) <= max_num_functions)%Z ->
      expression_restricted cenv (Efun fds e)
  | ER_app : forall f ft ys cenv,
      (Z.of_nat (Datatypes.length ys) <= max_function_args)%Z ->
      expression_restricted cenv (Eapp f ft ys)
  | ER_prim_val : forall x p e cenv,
      expression_restricted cenv e ->
      expression_restricted cenv (Eprim_val x p e)
  | ER_prim : forall x p ys e cenv,
      expression_restricted cenv e ->
      expression_restricted cenv (Eprim x p ys e)
  | ER_halt : forall x cenv,
      expression_restricted cenv (Ehalt x).

Local Hint Constructors expression_restricted : core.


Theorem check_restrictions_expression_restricted {cenv} : forall e e',
  check_restrictions cenv e = Ret () ->
  subterm_or_eq e' e ->
  expression_restricted cenv e'.
Proof.
  have IH := exp_mut
    (fun e => check_restrictions cenv e = Ret () -> forall e',
                subterm_or_eq e' e -> expression_restricted cenv e')
    (fun fds => ((fix iter (fds : fundefs) : error Datatypes.unit :=
                   match fds with
                   | Fnil => Ret ()
                   | Fcons _ _ ys e' fds' =>
                       _ <- assert (Z.of_nat (length ys) <=? max_function_args)%Z
                            "found fundef with too many function args, check max_function_args";;
                       _ <- (iter fds');;
                       check_restrictions cenv e'
                   end) fds) = Ret () -> forall e' e'',
               dsubterm_fds_e e' fds -> subterm_or_eq e'' e' -> expression_restricted cenv e'').
  intros. eapply IH; eauto; clear IH.
  - (* Econstr *)
    intros ???? IHe Hrestr ? Hsub. inv Hrestr.
    destruct (get_ctor_ord cenv t) eqn:Hord=>//. cbn [Monad.bind MonadError] in H2.
    destruct (Z.of_N n <? Wasm_int.Int32.half_modulus)%Z eqn:Htupper=>//.
    destruct (Z.of_nat (Datatypes.length l) <=? max_constr_args)%Z eqn:Hlen=>//.
    cbn in H2.
    apply Z.ltb_lt in Htupper.
    apply Z.leb_le in Hlen. apply clos_rt_rtn1 in Hsub.
    inv Hsub. constructor; auto.
    unfold ctor_ordinal_restricted.
    intros. by replace n0 with n by congruence.
    apply IHe; auto. by apply rt_refl.
    inv H1. apply IHe; auto. by apply clos_rtn1_rt.
  - (* Ecase nil *)
    intros ??? Hsub.
    apply clos_rt_rtn1 in Hsub. inv Hsub. constructor. apply Forall_nil.
    now inv H2.
  - (* Ecase cons *)
    intros ???? IHe IHe0 Hrestr ? Hsub. inv Hrestr.
    clear H0 H e. rename e0 into e.
    destruct (get_ctor_ord cenv c) eqn:Hord=>//.
    cbn [Monad.bind MonadError] in H2.
    destruct ((Z.of_N n <? Wasm_int.Int32.half_modulus)%Z) eqn:Hupper=>//.
    cbn in H2. destruct (check_restrictions cenv e) eqn:Hrestr=>//.
    destruct (sequence _ ) eqn:Hseq; inv H2. destruct u.
    assert (check_restrictions cenv (Ecase v l) = Ret ()). {
      unfold check_restrictions. simpl. now rewrite Hseq. }
    assert (expression_restricted cenv (Ecase v l)). {
       apply IHe0; auto. apply rt_refl. }
    apply clos_rt_rtn1 in Hsub. inv Hsub.
    { constructor. apply Forall_cons. simpl. split.
      unfold ctor_ordinal_restricted. intros.
      now replace n0 with n by congruence.
      apply IHe; auto. apply rt_refl. now inv H0. }
    inv H1. destruct H5.
    { inv H1. apply IHe; auto. now apply clos_rtn1_rt. }
    { apply IHe0; auto. apply clos_rtn1_rt in H2.
      assert (subterm_or_eq y (Ecase v l)). {
        constructor. now econstructor. }
      now eapply rt_trans. }
  - (* Eproj *)
    intros ????? IHe Hrestr ? Hsub. inv Hrestr. clear H e H0.
    apply clos_rt_rtn1 in Hsub. inv Hsub. constructor.
    apply IHe; auto. apply rt_refl.
    inv H. apply IHe; auto. now apply clos_rtn1_rt.
  - (* Eletapp *)
    intros ????? IHe Hrestr ? Hsub. inv Hrestr. clear H H0 e.
    destruct (Z.of_nat (Datatypes.length ys) <=? max_function_args)%Z eqn:Hlen=>//.
    apply Z.leb_le in Hlen. apply clos_rt_rtn1 in Hsub. inv Hsub. constructor; auto.
    apply IHe; auto. apply rt_refl. inv H. apply IHe; auto.
    now apply clos_rtn1_rt.
  - (* Efun *)
    intros ? IHfds ? IHe Hrestr ? Hsub. inv Hrestr.
    destruct (Z.of_nat (numOf_fundefs f2) <=? max_num_functions)%Z eqn:HmaxFns=>//.
    cbn in H2.
    destruct ((fix iter (fds : fundefs) := _) f2) eqn:Hfds=>//. destruct u.
    apply clos_rt_rtn1 in Hsub. inv Hsub.
    { constructor.
      - apply IHe; auto. apply rt_refl.
      - intros. split.
        { clear IHfds H0 H IHe HmaxFns H2. clear e e'.
          rename e'0 into e, f2 into fds.
          generalize dependent f. revert t ys e.
          induction fds; intros. 2: inv H1.
          cbn in H1. destruct (M.elt_eq f0 v).
          + (* f0=v *)
            inv H1. cbn in Hfds.
            destruct (Z.of_nat (Datatypes.length ys) <=? max_function_args)%Z eqn:Hlen.
            2: inv Hfds. now apply Z.leb_le in Hlen.
          + (* f0<>v *)
            cbn in Hfds.
            destruct (Z.of_nat (Datatypes.length l) <=? max_function_args)%Z.
            2:inv Hfds. cbn in Hfds.
            destruct ((fix iter (fds : fundefs) := _) fds) eqn:Hfds'. inv Hfds.
            destruct u. eapply IHfds; eauto.
        }
        apply find_def_dsubterm_fds_e in H1. eapply IHfds; eauto. apply rt_refl.
      - now apply Z.leb_le in HmaxFns.
    }
    inv H1. { eapply IHfds; eauto. now apply clos_rtn1_rt. }
    apply IHe; auto. now apply clos_rtn1_rt.
  - (* Eapp *)
    intros ??? Hrestr ? Hsub. inv Hrestr.
    destruct (Z.of_nat (Datatypes.length l) <=? max_function_args)%Z eqn:Hlen=>//.
    apply Z.leb_le in Hlen.
    apply clos_rt_rtn1 in Hsub. now inv Hsub.
  - (* Eprim_val *)
    intros ??? IHe Hrestr ? Hsub. inv Hrestr. clear H e H0.
    apply clos_rt_rtn1 in Hsub. inv Hsub. constructor.
    apply IHe; auto. apply rt_refl.
    inv H. apply IHe; auto. now apply clos_rtn1_rt.
  - (* Eprim *)
    intros ???? IHe Hrestr ? Hsub. inv Hrestr. clear H e H0.
    apply clos_rt_rtn1 in Hsub. inv Hsub. constructor.
    apply IHe; auto. apply rt_refl.
    inv H. apply IHe; auto. now apply clos_rtn1_rt.
  - (* Ehalt *)
    intros ??? Hsub.
    apply clos_rt_rtn1 in Hsub. inv Hsub. constructor. inv H2.
  - (* base case 1 *)
    intros ???? IHe ? IHfds ?????.
    cbn in H1.
    destruct (Z.of_nat (Datatypes.length l) <=? max_function_args)%Z=>//.
    cbn in H1.
    destruct ((fix iter (fds : fundefs) := _) f5) eqn:Hfds=>//.
    destruct u. inv H2.
    { apply IHe; auto. }
    { eapply IHfds; eauto. }
  - (* base case 2 *) intros. by inv H2.
Qed.
