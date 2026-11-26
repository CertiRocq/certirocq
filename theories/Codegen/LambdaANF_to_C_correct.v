(* Correctness of the translation of LambdaANF to Clight in [LambdaANF_to_C]. The main
   steps are [trans_correct] (an expression), [fun_correct] (a call), [program_correct] and
   [compile_correct]. *)

From Stdlib Require Import ZArith.ZArith Lists.List Relations.Relations Sets.Ensembles
     micromega.Lia.
From compcert Require Import lib.Coqlib lib.Maps lib.Integers common.AST common.Values
     common.Errors common.Memory common.Events common.Globalenvs common.Smallstep
     cfrontend.Ctypes cfrontend.Cop cfrontend.Clight Clightdefs.
From ExtLib Require Import Structures.Monads.
From MetaRocq.Utils Require Import bytestring.
From CertiRocq.Common Require Import compM Pipeline_utils.
From CertiRocq.LambdaANF Require Import Ensembles_util List_util map_util set_util term term_util
     identifiers rename algebra eval.
From CertiRocq.Codegen Require Import LambdaANF_to_C LambdaANF_to_C_static LambdaANF_to_C_rel
     LambdaANF_to_C_memory LambdaANF_to_C_clight.

Import ListNotations.
Local Open Scope Z_scope.
Local Open Scope bs_scope.

Local Arguments Z.mul : simpl never.
Local Arguments Z.add : simpl never.
Local Arguments Z.sub : simpl never.

(** * The source program *)

(* The functions of a program *)
Definition functions (e : exp) : fundefs :=
  match e with
  | Efun fds _ => fds
  | _ => Fnil
  end.

(* The main expression of a program *)
Definition main_exp (e : exp) : exp :=
  match e with
  | Efun _ main => main
  | _ => e
  end.

Lemma functions_bound e f :
  bound_var_fundefs (functions e) f -> bound_var e f.
Proof.
  destruct e; simpl; intros H; try solve [inv H]. now apply Bound_Efun1.
Qed.

Lemma functions_unique e :
  unique_bindings e -> unique_bindings_fundefs (functions e).
Proof.
  destruct e; simpl; intros H; try solve [constructor]. now inv H.
Qed.

(* No primitive operations and no primitive values *)
Definition no_prims (e : exp) : Prop :=
  forall e', subterm_or_eq e' e ->
             match e' with
             | Eprim_val _ _ _ | Eprim _ _ _ _ => False
             | _ => True
             end.

(* Two constructors of a type that are both constants or both blocks have different
   ordinals *)
Definition distinct_ordinals (cenv : ctor_env) : Prop :=
  forall t1 t2 i1 i2,
    M.get t1 cenv = Some i1 -> M.get t2 cenv = Some i2 ->
    ctor_ind_tag i1 = ctor_ind_tag i2 ->
    (ctor_arity i1 = 0%N <-> ctor_arity i2 = 0%N) ->
    ctor_ordinal i1 = ctor_ordinal i2 ->
    t1 = t2.

(* Sizes that the generator does not check: the ordinals fit in a word, no check for heap
   room asks for more than the nursery, and the roots of a function fit in memory *)
Definition within_limits (prims : M.t primitive) (cenv : ctor_env) (e : exp) : Prop :=
  (forall t i, M.get t cenv = Some i -> Z.of_N (ctor_ordinal i) < Int64.half_modulus) /\
  (forall e', subterm_or_eq e' e ->
              Z.of_nat (alloc_need prims e') <= nursery_size /\
              8 * Z.of_nat (max_roots prims (fun_arities (functions e)) e') <= Ptrofs.max_signed).

(** * The C program *)

Lemma composites_ok : exists ce, build_composite_env composites = Errors.OK ce.
Proof.
  destruct (build_composite_env composites) as [ce | msg] eqn:H.
  - eauto.
  - vm_compute in H. discriminate.
Qed.

Lemma ctypes_make_program_inv types defs public main (p : Clight.program) :
  Ctypes.make_program types defs public main = Errors.OK p ->
  prog_defs p = defs /\ prog_types p = types.
Proof.
  assert (G : forall (r : Errors.res composite_env) (e : r = build_composite_env types),
             match r as a return (a = build_composite_env types -> Errors.res (Ctypes.program function)) with
             | Errors.OK ce => fun Heq =>
                          Errors.OK {| prog_defs := defs; prog_public := public; prog_main := main;
                                prog_types := types; prog_comp_env := ce;
                                prog_comp_env_eq := Ctypes.make_program_obligation_1 types Heq |}
             | Errors.Error e => fun _ => Errors.Error e
             end e = Errors.OK p -> prog_defs p = defs /\ prog_types p = types).
  { intros r e. destruct r; intros Heq; inv Heq. simpl; auto. }
  intros H. exact (G _ eq_refl H).
Qed.

(* A program built with [make_program] has the given definitions and structs *)
Lemma make_program_inv types defs p :
  make_program types defs = Ret p ->
  prog_defs p = defs /\ build_composite_env types = Errors.OK (prog_comp_env p).
Proof.
  unfold make_program.
  destruct (Ctypes.make_program types defs [bodyId] mainId) as [p' | msg] eqn:H; intros Heq; inv Heq.
  destruct (ctypes_make_program_inv _ _ _ _ _ H) as [Hd Ht]. split; auto.
  rewrite <- Ht. apply prog_comp_env_eq.
Qed.

(* The program with the definitions of the structs can always be built *)
Lemma make_program_composites defs :
  exists p, make_program composites defs = Ret p.
Proof.
  destruct composites_ok as [ce Hce].
  unfold make_program.
  destruct (Ctypes.make_program composites defs [bodyId] mainId) as [p | msg] eqn:H; eauto.
  exfalso. revert H. unfold Ctypes.make_program.
  assert (G : forall (r : Errors.res composite_env) (e : r = build_composite_env composites),
             r = Errors.OK ce ->
             match r as a return (a = build_composite_env composites -> Errors.res (Ctypes.program function)) with
             | Errors.OK ce => fun Heq =>
                          Errors.OK {| prog_defs := defs; prog_public := [bodyId]; prog_main := mainId;
                                prog_types := composites; prog_comp_env := ce;
                                prog_comp_env_eq := Ctypes.make_program_obligation_1 composites Heq |}
             | Errors.Error e => fun _ => Errors.Error e
             end e <> Errors.Error msg).
  { intros r e Hr. destruct r; discriminate. }
  exact (G _ eq_refl Hce).
Qed.

Lemma bind_ret_inv {A B} (m : error A) (f : A -> error B) (y : B) :
  bind m f = Ret y -> exists x, m = Ret x /\ f x = Ret y.
Proof. destruct m; simpl; intros H; [discriminate | eauto]. Qed.

(* Unlike [injection], applying this lemma does not simplify the two sides *)
Lemma Ret_inj {A} (x y : A) : Ret x = Ret y -> x = y.
Proof. congruence. Qed.

(* Splits a hypothesis [x <- m ;; f x = Ret y] of the error monad *)
Ltac bind_inv H :=
  let x := fresh "x" in
  let E := fresh "E" in
  apply bind_ret_inv in H; destruct H as (x & E & H).

Ltac bind_inv_as H x E := apply bind_ret_inv in H; destruct H as (x & E & H).

(* The identifiers of the pipeline are not the variables that the generator adds *)
Lemma pipeline_ident x :
  (100 <= x)%positive ->
  x <> tinfoId /\ x <> allocId /\ x <> resultId /\ x <> boxedId /\ x <> frameId /\ x <> rootsId.
Proof.
  unfold tinfoId, allocId, resultId, boxedId, frameId, rootsId. intros H.
  split; [lia |]. split; [lia |]. split; [lia |]. split; [lia |]. split; lia.
Qed.

Lemma map_fst_tvalue (l : list ident) : map fst (map (fun x => (x, tvalue)) l) = l.
Proof. induction l; simpl; congruence. Qed.

Lemma map_snd_tvalue (l : list ident) :
  map snd (map (fun x => (x, tvalue)) l) = repeat tvalue (length l).
Proof. induction l; simpl; congruence. Qed.

(* Keeps the reduction tactics from unfolding the generator *)
Local Opaque translate_function.

Section Program.

  Context (nparam : nat) (prims : M.t primitive) (cenv : ctor_env) (tmp : positive).

  (* What the proof uses of the global environment [ge] of the C program: the structs,
     the two functions of the runtime, and the functions of the source program *)
  Record program_ok (ge : genv) (fds : fundefs) (main : exp) : Prop :=
    { prog_structs : structs_ok ge;
      prog_gc : exists b fd,
          Genv.find_symbol ge gcArgsId = Some b /\
          Genv.find_funct_ptr ge b = Some fd /\
          type_of_fundef fd = gc_args_ty;
      prog_is_ptr : exists b,
          Genv.find_symbol ge isPtrId = Some b /\
          Genv.find_funct_ptr ge b
          = Some (External (extern "certirocq_is_ptr" is_ptr_params tbool)
                           is_ptr_params tbool cc_default);
      prog_funs : forall f t ps e,
          find_def f fds = Some (t, ps, e) ->
          exists b fn,
            Genv.find_symbol ge f = Some b /\
            Genv.find_funct_ptr ge b = Some (Internal fn) /\
            translate_function nparam prims cenv (fun_arities fds) tmp (Some f) ps e = Ret fn;
      prog_body : exists b fn,
          Genv.find_symbol ge bodyId = Some b /\
          Genv.find_funct_ptr ge b = Some (Internal fn) /\
          translate_function nparam prims cenv (fun_arities fds) tmp None [] main = Ret fn }.

  Lemma translate_fundefs_names fenv : forall fds funs,
      translate_fundefs nparam prims cenv fenv tmp fds = Ret funs ->
      map fst funs = all_fun_name fds.
  Proof.
    induction fds as [f t ps e fds IH |]; cbn [translate_fundefs all_fun_name]; intros funs H.
    - bind_inv H. bind_inv H. inv H. cbn [map fst]. f_equal. auto.
    - inv H. reflexivity.
  Qed.

  Lemma translate_fundefs_find fenv : forall fds funs f t ps e,
      translate_fundefs nparam prims cenv fenv tmp fds = Ret funs ->
      find_def f fds = Some (t, ps, e) ->
      exists fn, translate_function nparam prims cenv fenv tmp (Some f) ps e = Ret fn /\
                 In (f, Gfun (Internal fn)) funs.
  Proof.
    induction fds as [f0 t0 ps0 e0 fds IH |]; cbn [translate_fundefs find_def];
      intros funs f t ps e H Hfind.
    - bind_inv H. bind_inv H. inv H.
      destruct (M.elt_eq f f0) as [-> | Hne].
      + inv Hfind. eexists; split; eauto. now left.
      + destruct (IH _ _ _ _ _ E0 Hfind) as (fn & Hfn & Hin).
        exists fn. split; auto. now right.
    - discriminate.
  Qed.

  (* A definition of a program whose names are distinct is in its global environment *)
  Lemma program_function (p : Clight.program) id fd :
    list_norepet (map fst (prog_defs p)) ->
    In (id, Gfun fd) (prog_defs p) ->
    exists b, Genv.find_symbol (globalenv p) id = Some b /\
              Genv.find_funct_ptr (globalenv p) b = Some fd.
  Proof.
    intros Hnr Hin.
    assert (Hmap : (prog_defmap p) ! id = Some (Gfun fd)).
    { apply PTree_Properties.of_list_norepet; auto. }
    apply Genv.find_def_symbol in Hmap. destruct Hmap as (b & Hb & Hd).
    exists b. split; auto. apply Genv.find_funct_ptr_iff. auto.
  Qed.

  Lemma all_fun_name_bound fds f :
    In f (all_fun_name fds) -> bound_var_fundefs fds f.
  Proof.
    intros Hin. apply name_in_fundefs_bound_var_fundefs.
    apply Same_set_all_fun_name. auto.
  Qed.

  Lemma all_fun_name_norepet fds :
    unique_bindings_fundefs fds -> list_norepet (all_fun_name fds).
  Proof.
    induction 1; simpl; constructor; auto.
    intros Hin. apply all_fun_name_bound in Hin. auto.
  Qed.

  (* The global environment of the program that [translate_program] builds *)
  Lemma translate_program_ok e defs p :
    translate_program nparam prims cenv tmp e = Ret defs ->
    make_program composites defs = Ret p ->
    unique_bindings e ->
    (forall x, bound_var e x -> (100 <= x)%positive) ->
    program_ok (globalenv p) (functions e) (main_exp e).
  Proof.
    intros Htr Hmk Hub Hid.
    destruct (make_program_inv _ _ _ Hmk) as [Hdefs Hce].
    unfold translate_program in Htr.
    replace (match e with Efun fds main => (fds, main) | _ => (Fnil, e) end)
      with (functions e, main_exp e) in Htr by (destruct e; reflexivity).
    bind_inv Htr. bind_inv Htr. injection Htr as Htr. rewrite <- Htr in Hdefs. clear Htr.
    rename x into funs. rename x0 into body. rename E into Hfuns. rename E0 into Hbody.
    assert (Hfb : forall f, bound_var_fundefs (functions e) f -> (100 <= f)%positive).
    { intros f Hf. apply Hid. now apply functions_bound. }
    pose proof (functions_unique _ Hub) as Hfu.
    assert (Hnr : list_norepet (map fst (prog_defs p))).
    { rewrite Hdefs. unfold runtime_defs. cbn [map fst app]. rewrite map_app. cbn [map fst].
      replace (map fst funs) with (all_fun_name (functions e))
        by (symmetry; exact (translate_fundefs_names _ _ _ Hfuns)).
      assert (Hno : forall id, (id < 100)%positive -> ~ In id (all_fun_name (functions e))).
      { intros id Hlt Hin. apply all_fun_name_bound, Hfb in Hin. lia. }
      constructor; [| constructor].
      - intros [Heq | Hin]; [discriminate |].
        apply in_app_or in Hin. destruct Hin as [Hin | [Heq | []]]; [| discriminate].
        apply (Hno gcArgsId); [reflexivity | auto].
      - intros Hin. apply in_app_or in Hin. destruct Hin as [Hin | [Heq | []]]; [| discriminate].
        apply (Hno isPtrId); [reflexivity | auto].
      - apply list_norepet_append; auto using all_fun_name_norepet.
        + constructor; [intros [] | constructor].
        + intros x y Hx [Hy | []] Heq. subst. apply (Hno bodyId); [reflexivity | auto]. }
    constructor.
    - exists (prog_comp_env p). split; [exact Hce | auto].
    - destruct (program_function
                  p gcArgsId
                  (External (extern "garbage_collect_args" gc_args_params tvoid)
                            gc_args_params tvoid cc_default) Hnr) as (b & Hb & Hgcb).
      { rewrite Hdefs. now left. }
      exists b. eexists. split; [exact Hb | split; [exact Hgcb | reflexivity]].
    - apply program_function; auto. rewrite Hdefs. right. now left.
    - intros f t ps e' Hfind.
      destruct (translate_fundefs_find _ _ _ _ _ _ _ Hfuns Hfind) as (fn & Hfn & Hin').
      destruct (program_function p f (Internal fn) Hnr) as (b & Hb & Hf).
      { rewrite Hdefs. right. right. apply in_or_app. now left. }
      exists b, fn. auto.
    - destruct (program_function p bodyId (Internal body) Hnr) as (b & Hb & Hf).
      { rewrite Hdefs. right. right. apply in_or_app. right. now left. }
      exists b, body. auto.
  Qed.

End Program.

(** * A function that runs *)

(* An expression that the proof covers: it is not a primitive, and its check for heap
   room asks for at most the nursery *)
Definition good (prims : M.t primitive) (e : exp) : Prop :=
  Z.of_nat (alloc_need prims e) <= nursery_size /\
  match e with
  | Eprim_val _ _ _ | Eprim _ _ _ _ => False
  | _ => True
  end.

Lemma ctor_rep_of_inv cenv t r :
  ctor_rep_of cenv t = Ret r ->
  exists info,
    M.get t cenv = Some info /\
    ((ctor_arity info = 0%N /\ r = Constant (Z.of_N (ctor_ordinal info))) \/
     (ctor_arity info <> 0%N /\ Z.of_N (ctor_ordinal info) <= max_block_ordinal /\
      r = Block (Z.of_N (ctor_ordinal info)) (N.to_nat (ctor_arity info)))).
Proof.
  unfold ctor_rep_of. destruct (M.get t cenv) as [info |]; [| discriminate].
  intros H. exists info. split; auto.
  destruct (ctor_arity info =? 0)%N eqn:Ha.
  - apply N.eqb_eq in Ha. inv H. now left.
  - apply N.eqb_neq in Ha.
    destruct (Z.of_N (ctor_ordinal info) <=? max_block_ordinal) eqn:Ho; [| discriminate].
    apply Z.leb_le in Ho. inv H. right. auto.
Qed.

Section Correct.

  Context {fuel : Type} {Hf : @fuel_resource fuel} {trace : Type} {Ht : @trace_resource trace}.
  Context (nparam : nat) (prims : M.t primitive) (cenv : ctor_env) (tmp : positive).
  Context (fds : fundefs) (main : exp) (rho0 : eval.env) (ge : genv).
  Context (gc_inv : heap -> mem -> block -> Z -> Prop).

  Let fenv := fun_arities fds.

  Notation val_rel := (val_rel cenv ge nparam gc_inv).
  Notation fun_rel := (fun_rel cenv ge nparam gc_inv).
  Notation repr_val := (repr_val cenv ge).
  Notation tinfo_wf := (tinfo_wf cenv ge gc_inv).
  Notation tinfo_ok := (tinfo_ok cenv ge gc_inv).
  Notation is_value := (is_value cenv ge).
  Notation still_represented := (still_represented cenv ge).

  (* What the proof uses of a function body [e] with the parameters [ps] *)
  Record body_ok (ps : list var) (e : exp) : Prop :=
    { bo_unique : unique_bindings e;
      bo_params : NoDup ps;
      bo_bound : forall x, bound_var e x -> ~ In x ps /\ M.get x fenv = None;
      bo_params_funs : forall x, In x ps -> M.get x fenv = None;
      bo_free : forall x, occurs_free e x -> In x ps \/ M.get x fenv <> None;
      bo_ids : forall x, bound_var e x \/ In x ps -> (100 <= x < tmp)%positive;
      bo_sub : forall e', subterm_or_eq e' e -> good prims e';
      bo_roots : 8 * Z.of_nat (max_roots prims fenv e) <= Ptrofs.max_signed;
      bo_arity : Z.of_nat (length ps) <= max_args }.

  Hypothesis Hprog : program_ok nparam prims cenv tmp ge fds main.
  Hypothesis Hgc : collector_ok cenv ge gc_inv.
  Hypothesis Hisptr : is_ptr_spec ge.
  Hypothesis Hord : distinct_ordinals cenv.
  Hypothesis Hsmall : forall t i, M.get t cenv = Some i ->
                                  Z.of_N (ctor_ordinal i) < Int64.half_modulus.
  Hypothesis Hbodies : forall f t ps e, find_def f fds = Some (t, ps, e) -> body_ok ps e.
  Hypothesis Hmain : body_ok [] main.
  Hypothesis Hfnames : forall f, M.get f fenv <> None -> (100 <= f < tmp)%positive.
  Hypothesis Htmp : (100 <= tmp)%positive.

  (* The proof for a number of steps [K], assuming it for fewer steps *)
  Section Index.

  (* The functions of the program are related for fewer than [K] steps *)
  Variable K : nat.
  Hypothesis Hrel : forall j f t xs e b fd,
      (j < K)%nat ->
      find_def f fds = Some (t, xs, e) ->
      Genv.find_symbol ge f = Some b ->
      Genv.find_funct_ptr ge b = Some fd ->
      fun_rel j (Vfun rho0 fds f) fd.

  Let Hstructs := prog_structs _ _ _ _ _ _ _ Hprog.

  (* The name of a function stands for a pointer to its C function *)
  Lemma fun_word i f :
    (i < K)%nat -> M.get f fenv <> None ->
    exists b fd, Genv.find_symbol ge f = Some b /\
                 Genv.find_funct_ptr ge b = Some fd /\
                 fun_rel i (Vfun rho0 fds f) fd.
  Proof.
    intros Hi Hfn. unfold fenv in Hfn. rewrite fun_arities_find in Hfn.
    destruct (find_def f fds) as [[[t xs] e] |] eqn:Hfind; [| congruence].
    destruct (prog_funs _ _ _ _ _ _ _ Hprog _ _ _ _ Hfind) as (b & fn & Hb & Hfp & _).
    exists b, (Internal fn). repeat split; auto. eapply Hrel; eauto.
  Qed.

  Lemma val_rel_word i h m v w : val_rel i h m v w -> is_word w.
  Proof. intros H. inv H; exact I. Qed.

  Lemma val_rel_is_value i h m v w : val_rel i h m v w -> is_value h m w.
  Proof. intros H. exists v. eapply repr_val_mono; [| | exact H]; auto. Qed.

  Lemma val_rel_kept i h m h' m' v w :
    data_kept h m h' m' -> val_rel i h m v w -> val_rel i h' m' v w.
  Proof. intros. eapply repr_val_kept; eauto. Qed.

  Lemma bstep_fuel_halt rho x (c : fuel) v (t : trace) :
    bstep_fuel cenv rho (Ehalt x) c (Res v) t -> M.get x rho = Some v.
  Proof.
    intros H. inv H. match goal with [ H0 : bstep _ _ _ _ _ _ |- _ ] => inv H0 end. assumption.
  Qed.

  (* One function of the program, or its main expression *)
  Section Body.

    (* The function that runs: its body, its code and the size of its roots *)
    Variables (self : option (var * list var)) (params : list var) (body : exp).
    Variables (fn : function) (nroots : nat) (tmps : list ident) (loops : bool).
    Variables (s_check : statement) (st1 : state) (s_body : statement).

    Let code : statement := seq s_check s_body.

    Hypothesis Hreturn : fn_return fn = tvalue.
    Hypothesis Henter :
      enter prims fenv (Z.of_nat nroots) init_state body = Ret (s_check, st1).
    Hypothesis Htrans :
      trans nparam prims cenv fenv self (Z.of_nat nroots) tmps st1 body = Ret s_body.
    Hypothesis Hbody : body_ok params body.
    Hypothesis Hself : forall g ps,
        self = Some (g, ps) ->
        ps = params /\
        (exists t, find_def g fds = Some (t, ps, body)) /\
        tmps = idents_from tmp (length ps) /\
        loops = calls_itself g (length ps) body.
    Hypothesis Hroots_body : (max_roots prims fenv body <= nroots)%nat.
    Hypothesis Hnroots : 8 * Z.of_nat nroots <= Ptrofs.max_signed.

    (* Its parameters, its C variables and its body *)
    Hypothesis Hfn_params :
      fn_params fn = (tinfoId, tptr tinfoT) :: map (fun x => (x, tvalue)) (firstn nparam params).
    Hypothesis Hfn_vars :
      fn_vars fn = if Nat.eqb nroots 0 then []
                   else [(frameId, frameT); (rootsId, tarray tvalue (Z.of_nat nroots))].
    Hypothesis Hfn_temps : list_disjoint (var_names (fn_params fn)) (var_names (fn_temps fn)).
    Hypothesis Hfn_body :
      fn_body fn = seq (load_args nparam (skipn nparam params))
                       (if loops then Sloop code Sskip else code).

    Lemma nroots_unsigned : 8 * Z.of_nat nroots <= Ptrofs.max_unsigned.
    Proof. pose proof Hnroots as H. rewrite ptrofs_max_signed in H. rewrite ptrofs_max_unsigned. lia. Qed.

    (* The C variables [frame] and [roots] are in the blocks [fb] and [rb] *)
    Definition local_env (fb rb : block) : Clight.env :=
      if Nat.eqb nroots 0 then empty_env
      else PTree.set rootsId (rb, tarray tvalue (Z.of_nat nroots))
                     (PTree.set frameId (fb, frameT) empty_env).

    (* One call of the function *)
    Section Call.

    (* The thread info, the frames of the callers, and the frame and roots of the function *)
    Variables (tb : block) (tofs : Z) (fs0 : list frame) (fb rb : block).

    Let lenv : Clight.env := local_env fb rb.

    Hypothesis Hown : nroots <> 0%nat ->
                      fb <> rb /\ fb <> tb /\ rb <> tb /\
                      not_in_frames fb fs0 /\ not_in_frames rb fs0.

    (** ** The variables of the function *)

    Lemma lenv_frame : nroots <> 0%nat -> lenv ! frameId = Some (fb, frameT).
    Proof.
      intros H. unfold lenv, local_env. destruct (Nat.eqb nroots 0) eqn:E.
      - apply Nat.eqb_eq in E. contradiction.
      - rewrite PTree.gso by discriminate. apply PTree.gss.
    Qed.

    Lemma lenv_roots :
      nroots <> 0%nat -> lenv ! rootsId = Some (rb, tarray tvalue (Z.of_nat nroots)).
    Proof.
      intros H. unfold lenv, local_env. destruct (Nat.eqb nroots 0) eqn:E.
      - apply Nat.eqb_eq in E. contradiction.
      - apply PTree.gss.
    Qed.

    Lemma lenv_other x : x <> frameId -> x <> rootsId -> lenv ! x = None.
    Proof.
      intros H1 H2. unfold lenv, local_env. destruct (Nat.eqb nroots 0).
      - apply PTree.gempty.
      - rewrite !PTree.gso by auto. apply PTree.gempty.
    Qed.

    Lemma lenv_fun x : M.get x fenv <> None -> lenv ! x = None.
    Proof.
      intros H. apply Hfnames in H. apply lenv_other; intros ->; unfold frameId, rootsId in H; lia.
    Qed.

    (** ** Continuations *)

    (* The continuations of the code of the function, when its caller continues with [k0] *)
    Inductive cont_ok (k0 : cont) : cont -> Prop :=
    | Cont_fun : loops = false -> cont_ok k0 k0
    | Cont_loop : loops = true -> cont_ok k0 (Kloop1 code Sskip k0)
    | Cont_seq : forall s k, cont_ok k0 k -> cont_ok k0 (Kseq s k)
    | Cont_switch : forall k, cont_ok k0 k -> cont_ok k0 (Kswitch k).

    Lemma cont_ok_call_cont k0 k : is_call_cont k0 -> cont_ok k0 k -> call_cont k = k0.
    Proof.
      intros Hk0. induction 1; simpl; auto; destruct k0; simpl in *; auto; contradiction.
    Qed.

    (* [continue] goes back to the start of the code *)
    Lemma cont_ok_continue k0 k le m :
      cont_ok k0 k -> loops = true ->
      star step2 ge (Clight.State fn Scontinue k lenv le m) E0
           (Clight.State fn code (Kloop1 code Sskip k0) lenv le m).
    Proof.
      intros Hk Hl. induction Hk.
      - congruence.
      - eapply star_step; [apply step_skip_or_continue_loop1; now right | | reflexivity].
        eapply star_step; [apply step_skip_loop2 | | reflexivity].
        apply star_one. apply step_loop.
      - eapply star_step; [apply step_continue_seq | exact IHHk | reflexivity].
      - eapply star_step; [apply step_continue_switch | exact IHHk | reflexivity].
    Qed.

    (** ** The invariant *)

    (* The frame and the roots of the function *)
    Definition own_blocks (b : block) (o : Z) : Prop :=
      nroots <> 0%nat /\ (b = fb \/ b = rb).

    (* The frame of the function when [k] of its roots are in use *)
    Definition own (k : nat) : frame := mkFrame fb 0 rb 0 (Z.of_nat k).

    Definition cur_frames (st : state) : list frame :=
      if st_linked st then own (length (st_slots st)) :: fs0 else fs0.

    Record locals_ok (h : heap) (m : mem) : Prop :=
      { lo_frame : nroots <> 0%nat -> Mem.range_perm m fb 0 24 Cur Freeable;
        lo_roots : nroots <> 0%nat -> Mem.range_perm m rb 0 (8 * Z.of_nat nroots) Cur Freeable;
        lo_heap : nroots <> 0%nat -> ~ heap_blocks h fb /\ ~ heap_blocks h rb }.

    (* What the code generator knows in [st] is consistent *)
    Record st_ok (st : state) : Prop :=
      { so_dirty : st_dirty st = true -> st_room st = true;
        so_stale : incl (st_stale st) (st_slots st);
        so_linked : st_linked st = false -> st_slots st = [];
        so_frame : st_linked st = true -> nroots <> 0%nat;
        so_nodup : NoDup (st_slots st);
        so_nslots : (length (st_slots st) <= nroots)%nat }.

    (* The memory: the thread info, [tinfo->alloc] and the roots of the function *)
    Record mem_inv (i : nat) (st : state) (rho : eval.env) (h : heap) (m : mem) : Prop :=
      { mi_wf : tinfo_wf h (cur_frames st) m tb tofs;
        mi_sync : st_dirty st = false ->
                  Mem.load Mptr m tb (tofs + alloc_ofs)
                  = Some (Vptr (free_block h) (Ptrofs.repr (free_start h)));
        mi_slots : forall j x, nth_error (st_slots st) j = Some x ->
                               exists v w, M.get x rho = Some v /\
                                           Mem.load Mptr m rb (8 * Z.of_nat j) = Some w /\
                                           val_rel i h m v w;
        mi_locals : locals_ok h m }.

    (* The C variables: [tinfo], [alloc] and the variables of the source program *)
    Record tmp_inv (i : nat) (st : state) (rho : eval.env) (e : exp) (le : temp_env)
           (h : heap) (m : mem) : Prop :=
      { ti_tinfo : le ! tinfoId = Some (Vptr tb (Ptrofs.repr tofs));
        ti_room : st_room st = true ->
                  le ! allocId = Some (Vptr (free_block h) (Ptrofs.repr (free_start h))) /\
                  free_start h + 8 * Z.of_nat (alloc_need prims e) <= free_end h;
        ti_vars : forall x, occurs_free e x -> M.get x fenv = None ->
                            exists v, M.get x rho = Some v /\
                                      (~ In x (st_stale st) ->
                                       exists w, le ! x = Some w /\ val_rel i h m v w);
        ti_funs : forall f, M.get f fenv <> None -> M.get f rho = Some (Vfun rho0 fds f) }.

    Definition inv (i : nat) (st : state) (rho : eval.env) (e : exp) (le : temp_env)
               (h : heap) (m : mem) : Prop :=
      mem_inv i st rho h m /\ st_ok st /\ tmp_inv i st rho e le h m.

    (* The expression [e] that the code is at *)
    Record exp_ok (st : state) (e : exp) : Prop :=
      { eo_unique : unique_bindings e;
        eo_bound : forall x, bound_var e x ->
                             (100 <= x < tmp)%positive /\ M.get x fenv = None /\
                             ~ In x (st_slots st) /\ ~ occurs_free e x;
        eo_free : forall x, occurs_free e x -> (100 <= x < tmp)%positive;
        eo_sub : forall e', subterm_or_eq e' e -> good prims e';
        eo_roots : (max_roots prims fenv e <= nroots)%nat;
        eo_loop : forall g ps, self = Some (g, ps) ->
                               calls_itself g (length ps) e = true -> loops = true }.

    (* What the function does to its callers from [h, m] to [h', m'] *)
    Definition step_ok (h : heap) (m : mem) (h' : heap) (m' : mem) : Prop :=
      (forall b o, root_at tb tofs 0 fs0 b o -> still_represented h m h' m' b o) /\
      changes own_blocks tb tofs fs0 h m h' m'.

    Lemma step_ok_refl h m : step_ok h m h m.
    Proof.
      split; [intros; apply still_represented_refl | apply changes_refl].
    Qed.

    Lemma step_ok_trans h1 m1 h2 m2 h3 m3 :
      step_ok h1 m1 h2 m2 -> step_ok h2 m2 h3 m3 -> step_ok h1 m1 h3 m3.
    Proof.
      intros [R1 C1] [R2 C2]. split.
      - intros b o Hr. eapply still_represented_trans; eauto.
      - eapply changes_trans; eauto.
    Qed.

    (** ** Keeping the invariant *)

    Lemma mem_inv_mono i j st rho h m :
      (j <= i)%nat -> mem_inv i st rho h m -> mem_inv j st rho h m.
    Proof.
      intros Hle [Hwf Hsync Hslots Hloc]. constructor; auto.
      intros p x Hp. destruct (Hslots p x Hp) as (v & w & Hv & Hw & Hr).
      exists v, w. repeat split; auto. eapply val_rel_mono; eauto.
    Qed.

    Lemma fs0_frame_ok i st rho h m fr :
      mem_inv i st rho h m -> In fr fs0 -> frame_ok cenv ge h m tb fr.
    Proof.
      intros Hm Hin. pose proof (wf_frames _ _ _ _ _ _ _ _ (mi_wf _ _ _ _ _ Hm)) as Hfs.
      rewrite Forall_forall in Hfs. apply Hfs. unfold cur_frames.
      destruct (st_linked st); [now right | auto].
    Qed.

    (* The memory changes and the data is kept *)
    Lemma mem_inv_kept i st rho h m h' m' :
      mem_inv i st rho h m ->
      data_kept h m h' m' ->
      tinfo_wf h' (cur_frames st) m' tb tofs ->
      (st_dirty st = false ->
       Mem.load Mptr m' tb (tofs + alloc_ofs)
       = Some (Vptr (free_block h') (Ptrofs.repr (free_start h')))) ->
      (forall j w, (j < length (st_slots st))%nat ->
                   Mem.load Mptr m rb (8 * Z.of_nat j) = Some w ->
                   Mem.load Mptr m' rb (8 * Z.of_nat j) = Some w) ->
      locals_ok h' m' ->
      mem_inv i st rho h' m'.
    Proof.
      intros [Hwf Hsync Hslots Hloc] Hk Hwf' Hsync' Hl Hloc'. constructor; auto.
      intros p x Hp. destruct (Hslots p x Hp) as (v & w & Hv & Hw & Hr).
      exists v, w. repeat split; auto.
      - apply Hl; auto. apply nth_error_Some. congruence.
      - eapply val_rel_kept; eauto.
    Qed.

    Lemma tmp_inv_kept i st rho e le h m h' m' :
      tmp_inv i st rho e le h m ->
      data_kept h m h' m' ->
      (st_room st = true ->
       free_block h' = free_block h /\ free_start h' = free_start h /\ free_end h' = free_end h) ->
      tmp_inv i st rho e le h' m'.
    Proof.
      intros [Hti Hroom Hvars Hfuns] Hk Hfree. constructor; auto.
      - intros Hr. destruct (Hfree Hr) as (-> & -> & ->). auto.
      - intros x Hx Hnf. destruct (Hvars x Hx Hnf) as (v & Hv & Hw).
        exists v. split; auto. intros Hns. destruct (Hw Hns) as (w & Hlw & Hr).
        exists w. split; auto. eapply val_rel_kept; eauto.
    Qed.

    (* A variable is bound *)
    Lemma mem_inv_set i st rho h m x v :
      mem_inv i st rho h m -> ~ In x (st_slots st) -> mem_inv i st (M.set x v rho) h m.
    Proof.
      intros [Hwf Hsync Hslots Hloc] Hx. constructor; auto.
      intros p y Hp. destruct (Hslots p y Hp) as (v' & w & Hv & Hw & Hr).
      exists v', w. repeat split; auto. rewrite M.gso; auto.
      intros ->. apply Hx. eapply nth_error_In; eauto.
    Qed.

    Lemma tmp_inv_set i st rho e e' le h m x v w :
      tmp_inv i st rho e le h m ->
      val_rel i h m v w ->
      x <> tinfoId -> x <> allocId -> M.get x fenv = None ->
      (forall y, occurs_free e' y -> y = x \/ occurs_free e y) ->
      (alloc_need prims e' <= alloc_need prims e)%nat ->
      tmp_inv i st (M.set x v rho) e' (PTree.set x w le) h m.
    Proof.
      intros [Hti Hroom Hvars Hfuns] Hr Hx1 Hx2 Hxf Hfv Hneed. constructor.
      - rewrite PTree.gso; auto.
      - intros Hrm. destruct (Hroom Hrm) as [Ha Hroom']. split.
        + rewrite PTree.gso; auto.
        + lia.
      - intros y Hy Hnf. destruct (Pos.eq_dec y x) as [-> | Hne].
        + exists v. split; [apply M.gss |]. intros _. exists w. split; auto. apply PTree.gss.
        + destruct (Hfv y Hy) as [-> | Hy']; [contradiction |].
          destruct (Hvars y Hy' Hnf) as (v' & Hv & Hw).
          exists v'. split; [rewrite M.gso; auto |].
          intros Hns. destruct (Hw Hns) as (w' & Hlw & Hr'). exists w'. split; auto.
          rewrite PTree.gso; auto.
      - intros f Hfn. rewrite M.gso; auto. intros ->. contradiction.
    Qed.

    (* The code goes into a part [e'] of the expression *)
    Lemma tmp_inv_sub i st rho e e' le h m :
      tmp_inv i st rho e le h m ->
      (forall y, occurs_free e' y -> occurs_free e y) ->
      (alloc_need prims e' <= alloc_need prims e)%nat ->
      tmp_inv i st rho e' le h m.
    Proof.
      intros [Hti Hroom Hvars Hfuns] Hfv Hneed. constructor; auto.
      intros Hrm. destruct (Hroom Hrm) as [Ha Hroom']. split; auto. lia.
    Qed.

    (* The word of a variable that the code reads *)
    Lemma var_word i st rho e le h m x :
      (i < K)%nat ->
      tmp_inv i st rho e le h m -> occurs_free e x -> ~ In x (st_stale st) ->
      exists v w, M.get x rho = Some v /\ var_val ge le fenv x w /\ val_rel i h m v w.
    Proof.
      intros Hi [Hti Hroom Hvars Hfuns] Hx Hns. unfold var_val.
      destruct (M.get x fenv) as [n |] eqn:Hfx.
      - destruct (fun_word i x Hi) as (b & fd & Hb & Hfp & Hr); [congruence |].
        exists (Vfun rho0 fds x), (Vptr b Ptrofs.zero). repeat split.
        + apply Hfuns. congruence.
        + eauto.
        + econstructor; eauto.
      - destruct (Hvars x Hx Hfx) as (v & Hv & Hw). destruct (Hw Hns) as (w & Hlw & Hr).
        exists v, w. auto.
    Qed.

    Lemma vars_words i st rho e le h m : forall ys,
        (i < K)%nat ->
        tmp_inv i st rho e le h m ->
        (forall y, In y ys -> occurs_free e y /\ ~ In y (st_stale st)) ->
        exists vs ws, get_list ys rho = Some vs /\
                      Forall2 (var_val ge le fenv) ys ws /\
                      Forall2 (val_rel i h m) vs ws.
    Proof.
      induction ys as [| y ys IH]; intros Hi Htm Hys.
      - exists [], []. repeat split; constructor.
      - destruct (Hys y (or_introl eq_refl)) as [Hy Hns].
        destruct (var_word i st rho e le h m y Hi Htm Hy Hns) as (v & w & Hv & Hvw & Hr).
        destruct IH as (vs & ws & Hvs & Hvws & Hrs); auto.
        { intros z Hz. apply Hys. now right. }
        exists (v :: vs), (w :: ws). repeat split.
        + simpl. rewrite Hv, Hvs. reflexivity.
        + constructor; auto.
        + constructor; auto.
    Qed.

    (** ** Stores of the function *)

    Lemma own_not_heap i st rho h m b o :
      mem_inv i st rho h m -> own_blocks b o -> ~ heap_blocks h b.
    Proof.
      intros Hm [Hn Hb]. destruct (lo_heap _ _ (mi_locals _ _ _ _ _ Hm) Hn). destruct Hb; subst; auto.
    Qed.

    Lemma locals_ok_kept h m m' :
      locals_ok h m -> (forall b, keeps_perm m m' b) -> locals_ok h m'.
    Proof.
      intros [H1 H2 H3] Hk. constructor; auto.
      - intros Hn o Ho. apply Hk. apply (H1 Hn). exact Ho.
      - intros Hn o Ho. apply Hk. apply (H2 Hn). exact Ho.
    Qed.

    Lemma locals_ok_store h m chunk b o v m' :
      locals_ok h m -> Mem.store chunk m b o v = Some m' -> locals_ok h m'.
    Proof.
      intros [H1 H2 H3] Hst. constructor; auto.
      - intros Hn o' Ho'. eapply Mem.perm_store_1; [exact Hst | apply H1; auto].
      - intros Hn o' Ho'. eapply Mem.perm_store_1; [exact Hst | apply H2; auto].
    Qed.

    (* A store in the free space, in the thread info or in a variable of the function
       keeps the data and changes nothing for the callers *)
    Lemma step_ok_store i st rho h m chunk b o v m' :
      mem_inv i st rho h m ->
      Mem.store chunk m b o v = Some m' ->
      (heap_blocks h b /\ (forall j, o <= j < o + size_chunk chunk -> ~ allocated h b j)) \/
      own_blocks b o \/
      (b = tb /\ tofs <= o /\ o + size_chunk chunk <= tofs + tinfo_size) ->
      data_kept h m h m' /\ step_ok h m h m'.
    Proof.
      intros Hm Hst Hb.
      pose proof (wf_block _ _ _ _ _ _ _ _ (mi_wf _ _ _ _ _ Hm)) as Htb.
      assert (Hk : data_kept h m h m').
      { eapply store_data_kept; eauto. intros j Hj Ha.
        destruct Hb as [[_ Hna] | [Hown' | [-> _]]].
        - exact (Hna j Hj Ha).
        - destruct Ha as [Hh _]. eapply own_not_heap; eauto.
        - destruct Ha as [Hh _]. contradiction. }
      split; auto. split.
      - intros b' o' [[_ (j & Hj & _)] | (fr & j & Hin & Hj & -> & ->)]; [lia |].
        apply still_represented_kept; auto. intros w Hw. rewrite <- Hw.
        eapply Mem.load_store_other; eauto. left.
        pose proof (fs0_frame_ok _ _ _ _ _ _ Hm Hin) as Hfr.
        destruct (frame_heap _ _ _ _ _ _ Hfr) as [_ Hrh].
        destruct (frame_tinfo _ _ _ _ _ _ Hfr) as [_ Hrt].
        destruct Hb as [[Hh _] | [[Hn [-> | ->]] | [-> _]]].
        + intros Heq. rewrite Heq in Hrh. contradiction.
        + destruct (Hown Hn) as (_ & _ & _ & Hnf & _). apply not_eq_sym. apply (Hnf fr Hin).
        + destruct (Hown Hn) as (_ & _ & _ & _ & Hnr). apply not_eq_sym. apply (Hnr fr Hin).
        + exact Hrt.
      - split; [| split].
        + eapply Mem.store_unchanged_on; eauto.
          intros j Hj (Hnh & Hnt & _ & Hno).
          destruct Hb as [[Hh _] | [[Hn Hown'] | [-> Hr]]].
          * contradiction.
          * apply Hno. split; auto.
          * apply Hnt. split; auto. lia.
        + intros b' o' k p _ _ Hp. eapply Mem.perm_store_1; eauto.
        + intros b' Hb'. now left.
    Qed.

    (* A change in the free space, in the thread info or in the variables of the function
       keeps the data and changes nothing for the callers *)
    Lemma step_ok_region i st rho h m m' (R : block -> Z -> Prop) :
      mem_inv i st rho h m ->
      Mem.unchanged_on (fun b o => ~ R b o) m m' ->
      (forall b, keeps_perm m m' b) ->
      (forall b o, R b o -> (heap_blocks h b /\ ~ allocated h b o) \/ own_blocks b o \/
                            in_tinfo tb tofs b o) ->
      data_kept h m h m' /\ step_ok h m h m'.
    Proof.
      intros Hm Hun Hkp HR.
      pose proof (wf_block _ _ _ _ _ _ _ _ (mi_wf _ _ _ _ _ Hm)) as Htb.
      assert (Hk : data_kept h m h m').
      { split; auto. eapply Mem.unchanged_on_implies; eauto.
        intros b o Ha _ Hr. destruct (HR b o Hr) as [[_ Hna] | [Hown' | [-> _]]].
        - contradiction.
        - destruct Ha as [Hh _]. eapply own_not_heap; eauto.
        - destruct Ha as [Hh _]. contradiction. }
      split; auto. split.
      - intros b' o' [[_ (j & Hj & _)] | (fr & j & Hin & Hj & -> & ->)]; [lia |].
        apply still_represented_kept; auto. intros w Hw.
        eapply Mem.load_unchanged_on; eauto. intros o _ Hr.
        pose proof (fs0_frame_ok _ _ _ _ _ _ Hm Hin) as Hfr.
        destruct (frame_heap _ _ _ _ _ _ Hfr) as [_ Hrh].
        destruct (frame_tinfo _ _ _ _ _ _ Hfr) as [_ Hrt].
        destruct (HR _ _ Hr) as [[Hh _] | [[Hn [Heq | Heq]] | [Heq _]]].
        + contradiction.
        + destruct (Hown Hn) as (_ & _ & _ & Hnf & _). destruct (Hnf fr Hin). congruence.
        + destruct (Hown Hn) as (_ & _ & _ & _ & Hnr). destruct (Hnr fr Hin). congruence.
        + contradiction.
      - split; [| split].
        + eapply Mem.unchanged_on_implies; eauto.
          intros b o (Hnh & Hnt & _ & Hno) _ Hr.
          destruct (HR b o Hr) as [[Hh _] | [Hown' | Hti]]; contradiction.
        + intros b' o' k p _ _ Hp. apply Hkp. exact Hp.
        + intros b' Hb'. now left.
    Qed.

    (* A change of the code generator's state that does not concern the memory *)
    Lemma mem_inv_state i st st' rho h m :
      mem_inv i st rho h m ->
      st_linked st' = st_linked st -> st_slots st' = st_slots st ->
      (st_dirty st' = false ->
       Mem.load Mptr m tb (tofs + alloc_ofs)
       = Some (Vptr (free_block h) (Ptrofs.repr (free_start h)))) ->
      mem_inv i st' rho h m.
    Proof.
      intros [Hwf Hsync Hslots Hloc] Hl Hsl Hsy. constructor; auto.
      - unfold cur_frames in *. rewrite Hl, Hsl. exact Hwf.
      - rewrite Hsl. exact Hslots.
    Qed.

    (** ** After a call *)

    (* After a call the roots of the function still hold the values of their variables *)
    Lemma slots_after_call i st rho h m h' m' n :
      mem_inv i st rho h m -> st_ok st ->
      (forall b o, root_at tb tofs n (cur_frames st) b o -> still_represented h m h' m' b o) ->
      forall j x, nth_error (st_slots st) j = Some x ->
                  exists v w, M.get x rho = Some v /\
                              Mem.load Mptr m' rb (8 * Z.of_nat j) = Some w /\
                              val_rel i h' m' v w.
    Proof.
      intros Hm Hs Hroots j x Hj.
      destruct (mi_slots _ _ _ _ _ Hm j x Hj) as (v & w & Hv & Hw & Hr).
      assert (Hlinked : st_linked st = true).
      { destruct (st_linked st) eqn:E; auto. rewrite (so_linked _ Hs E) in Hj.
        destruct j; discriminate. }
      destruct (Hroots rb (8 * Z.of_nat j)) with (w := w) as (w' & Hw' & Hrep); auto.
      { right. unfold cur_frames. rewrite Hlinked.
        exists (own (length (st_slots st))), (Z.of_nat j). split; [now left |].
        simpl. split; [| split; [reflexivity | lia]].
        assert (j < length (st_slots st))%nat by (apply nth_error_Some; congruence). lia. }
      exists v, w'. repeat split; auto. apply Hrep. exact Hr.
    Qed.

    Lemma locals_after_call i st rho h m h' m' fs :
      mem_inv i st rho h m ->
      changes (fun _ _ => False) tb tofs fs h m h' m' ->
      locals_ok h' m'.
    Proof.
      intros Hm (_ & Hp & Hn). destruct (mi_locals _ _ _ _ _ Hm) as [Hfp Hrp Hh].
      constructor.
      - intros Hnr o Ho. apply Hp; [apply (Hh Hnr) | tauto | apply (Hfp Hnr); exact Ho].
      - intros Hnr o Ho. apply Hp; [apply (Hh Hnr) | tauto | apply (Hrp Hnr); exact Ho].
      - intros Hnr. destruct (Hh Hnr) as [Hfh Hrh].
        split; intros Hb; destruct (Hn _ Hb) as [| Hv]; auto.
        + apply Hv. eapply Mem.perm_valid_block. apply (Hfp Hnr 0). lia.
        + apply Hv. eapply Mem.perm_valid_block. apply (Hrp Hnr 0). lia.
    Qed.

    Lemma step_ok_call st h m h' m' n :
      st_ok st ->
      (forall b o, root_at tb tofs n (cur_frames st) b o -> still_represented h m h' m' b o) ->
      changes (fun _ _ => False) tb tofs (cur_frames st) h m h' m' ->
      step_ok h m h' m'.
    Proof.
      intros Hs Hroots (U & P & N). split.
      - intros b o [[_ (j & Hj & _)] | (fr & j & Hin & Hj & Hb & Ho)]; [lia |].
        apply Hroots. right. exists fr, j.
        split; [| split; [exact Hj | split; [exact Hb | exact Ho]]].
        unfold cur_frames. destruct (st_linked st); [now right | auto].
      - split; [| split]; auto.
        eapply Mem.unchanged_on_implies; eauto.
        intros b o (Hh & Hti & Hr & Ho) _. repeat split; auto.
        intros (fr & Hin & Hb & Hrange). unfold cur_frames in Hin.
        destruct (st_linked st) eqn:E.
        + destruct Hin as [<- | Hin].
          * simpl in Hb. apply Ho. split; [exact (so_frame _ Hs E) | now right].
          * apply Hr. exists fr. auto.
        + apply Hr. exists fr. auto.
    Qed.

    (* The words of C variables that were read back *)
    Lemma temps_words i st rho e le h m : forall xs,
        tmp_inv i st rho e le h m ->
        (forall x, In x xs -> occurs_free e x /\ M.get x fenv = None /\ ~ In x (st_stale st)) ->
        exists vs ws, Forall2 (fun x v => M.get x rho = Some v) xs vs /\
                      Forall2 (fun x w => le ! x = Some w) xs ws /\
                      Forall2 (val_rel i h m) vs ws.
    Proof.
      induction xs as [| x xs IH]; intros Htm Hxs.
      - exists [], []. repeat split; constructor.
      - destruct (Hxs x (or_introl eq_refl)) as (Hx & Hfx & Hns).
        destruct (ti_vars _ _ _ _ _ _ _ Htm x Hx Hfx) as (v & Hv & Hw).
        destruct (Hw Hns) as (w & Hlw & Hr).
        destruct IH as (vs & ws & Hvs & Hws & Hrs); auto.
        { intros z Hz. apply Hxs. now right. }
        exists (v :: vs), (w :: ws). repeat split; constructor; auto.
    Qed.

    (* A field of the thread info can be written *)
    Lemma tinfo_field_store h fs m delta v :
      tinfo_wf h fs m tb tofs ->
      0 <= delta -> delta + 8 <= tinfo_size -> (8 | delta) ->
      exists m', Mem.store Mptr m tb (tofs + delta) v = Some m'.
    Proof.
      intros Hwf H0 H1 H2. destruct (wf_range _ _ _ _ _ _ _ _ Hwf) as (Hlo & Hhi & Hal).
      destruct (Mem.valid_access_store m Mptr tb (tofs + delta) v) as [m' Hm']; eauto.
      split.
      - intros o Ho. apply (wf_perm _ _ _ _ _ _ _ _ Hwf). change (size_chunk Mptr) with 8 in Ho. lia.
      - apply Z.divide_add_r; auto.
    Qed.

    Lemma tinfo_address h fs m delta :
      tinfo_wf h fs m tb tofs -> 0 <= delta <= tinfo_size ->
      Ptrofs.unsigned (Ptrofs.repr (tofs + delta)) = tofs + delta.
    Proof.
      intros Hwf Hd. destruct (wf_range _ _ _ _ _ _ _ _ Hwf) as (Hlo & Hhi & Hal).
      apply Ptrofs.unsigned_repr. lia.
    Qed.

    Lemma frames_word m fp fs : frames m fp fs -> is_word fp.
    Proof. intros H; inv H; exact I. Qed.

    (** ** Leaving the function *)

    (* [tinfo->alloc = alloc], if the code has allocated *)
    Lemma sync_correct i st rho e le h m :
      inv i st rho e le h m ->
      exists m',
        runs ge fn lenv (sync st) le m le m' /\
        mem_inv i st rho h m' /\
        Mem.load Mptr m' tb (tofs + alloc_ofs)
        = Some (Vptr (free_block h) (Ptrofs.repr (free_start h))) /\
        data_kept h m h m' /\ step_ok h m h m' /\
        tmp_inv i st rho e le h m'.
    Proof.
      intros (Hm & Hs & Htm). unfold sync. destruct (st_dirty st) eqn:Hd.
      - destruct (ti_room _ _ _ _ _ _ _ Htm (so_dirty _ Hs Hd)) as [Hal _].
        pose proof (mi_wf _ _ _ _ _ Hm) as Hwf.
        destruct (tinfo_field_store h _ m alloc_ofs
                    (Vptr (free_block h) (Ptrofs.repr (free_start h))) Hwf)
          as [m' Hm']; try (unfold alloc_ofs; ofs_lia). { apply Z.divide_0_r. }
        destruct (step_ok_store _ _ _ _ _ _ _ _ _ _ Hm Hm') as [Hk Hstep].
        { right. right. split; auto. change (size_chunk Mptr) with 8. ofs_lia. }
        assert (Hl : Mem.load Mptr m' tb (tofs + alloc_ofs)
                     = Some (Vptr (free_block h) (Ptrofs.repr (free_start h)))).
        { erewrite Mem.load_store_same; eauto. reflexivity. }
        exists m'. split; [| split; [| split; [| split; [| split]]]]; auto.
        + eapply runs_assign.
          * apply eval_tinfo_alloc; auto. exact (ti_tinfo _ _ _ _ _ _ _ Htm).
          * apply eval_Etempvar. exact Hal.
          * reflexivity.
          * reflexivity.
          * exact I.
          * erewrite tinfo_address by (eauto; ofs_lia). exact Hm'.
        + eapply mem_inv_kept; eauto.
          * eapply tinfo_wf_store_tinfo; eauto. left. change (size_chunk Mptr) with 8. ofs_lia.
          * intros j w Hj Hw. rewrite <- Hw. eapply Mem.load_store_other; eauto. left.
            assert (Hn : nroots <> 0%nat) by (pose proof (so_nslots _ Hs); lia).
            apply (Hown Hn).
          * eapply locals_ok_store; eauto. exact (mi_locals _ _ _ _ _ Hm).
        + eapply tmp_inv_kept; eauto.
      - exists m. split; [apply runs_skip |]. split; [exact Hm |].
        split; [exact (mi_sync _ _ _ _ _ Hm Hd) |].
        split; [apply data_kept_refl |]. split; [apply step_ok_refl | exact Htm].
    Qed.

    (* [tinfo->alloc = alloc; tinfo->fp = frame.prev], as far as they are needed *)
    Lemma leave_correct i st rho e le h m :
      inv i st rho e le h m ->
      exists m',
        runs ge fn lenv (leave st) le m le m' /\
        tinfo_ok h fs0 m' tb tofs /\
        data_kept h m h m' /\ step_ok h m h m' /\ locals_ok h m'.
    Proof.
      intros Hinv. pose proof Hinv as (_ & Hs & _).
      destruct (sync_correct _ _ _ _ _ _ _ Hinv) as (m1 & Hrun1 & Hm1 & Hal1 & Hk1 & Hst1 & Htm1).
      unfold leave, unlink. pose proof (mi_wf _ _ _ _ _ Hm1) as Hwf.
      unfold cur_frames in Hwf. destruct (st_linked st) eqn:Hl.
      - pose proof (so_frame _ Hs Hl) as Hn.
        destruct (wf_fp _ _ _ _ _ _ _ _ Hwf) as (fp & Hfp & Hfr).
        inversion Hfr as [| ? prev ? Hnext Hroot Hprev Hfrs]; subst. simpl in Hprev.
        destruct (tinfo_field_store h _ m1 fp_ofs prev Hwf) as [m2 Hm2]; try ofs_lia.
        { exists 1027. reflexivity. }
        destruct (step_ok_store _ _ _ _ _ _ _ _ _ _ Hm1 Hm2) as [Hk2 Hst2].
        { right. right. split; auto. change (size_chunk Mptr) with 8. ofs_lia. }
        exists m2. split; [| split; [| split; [| split]]].
        + eapply runs_seq; [exact Hrun1 |].
          eapply runs_assign.
          * apply eval_tinfo_fp; auto. exact (ti_tinfo _ _ _ _ _ _ _ Htm1).
          * eapply eval_load.
            -- apply eval_frame_prev; auto. apply lenv_frame; auto.
            -- reflexivity.
            -- exact Hprev.
          * reflexivity.
          * reflexivity.
          * eapply frames_word; eauto.
          * erewrite tinfo_address by (eauto; ofs_lia). exact Hm2.
        + split.
          * eapply tinfo_wf_unlink; eauto.
          * rewrite <- Hal1. eapply Mem.load_store_other; eauto.
            right. left. change (size_chunk Mptr) with 8. ofs_lia.
        + destruct Hk1 as [U1 I1]. destruct Hk2 as [U2 I2]. split; auto.
          eapply Mem.unchanged_on_trans; eauto.
        + eapply step_ok_trans; eauto.
        + eapply locals_ok_store; eauto. exact (mi_locals _ _ _ _ _ Hm1).
      - exists m1. split; [| split; [| split; [| split]]]; auto.
        + eapply runs_seq; [exact Hrun1 | apply runs_skip].
        + split; auto.
        + exact (mi_locals _ _ _ _ _ Hm1).
    Qed.

    (* The C variables change, but not those that the invariant reads *)
    Lemma tmp_inv_temps i st rho e le le' h m :
      tmp_inv i st rho e le h m ->
      le' ! tinfoId = le ! tinfoId ->
      (st_room st = true -> le' ! allocId = le ! allocId) ->
      (forall x, occurs_free e x -> M.get x fenv = None -> ~ In x (st_stale st) ->
                 le' ! x = le ! x) ->
      tmp_inv i st rho e le' h m.
    Proof.
      intros [Hti Hroom Hvars Hfuns] H1 H2 H3. constructor; auto.
      - congruence.
      - intros Hr. destruct (Hroom Hr). split; auto. rewrite H2; auto.
      - intros x Hx Hfx. destruct (Hvars x Hx Hfx) as (v & Hv & Hw).
        exists v. split; auto. intros Hns. destruct (Hw Hns) as (w & Hlw & Hr).
        exists w. split; auto. rewrite H3; auto.
    Qed.

    (** ** The expression *)

    Lemma good_sub e e' :
      (forall e0, subterm_or_eq e0 e -> good prims e0) -> dsubterm_e e' e ->
      forall e0, subterm_or_eq e0 e' -> good prims e0.
    Proof.
      intros H Hd e0 He0. apply H. eapply rt_trans; [exact He0 |]. apply rt_step. exact Hd.
    Qed.

    Lemma exp_ok_slots st st' e :
      exp_ok st e ->
      (forall x, In x (st_slots st') -> In x (st_slots st) \/ occurs_free e x) ->
      exp_ok st' e.
    Proof.
      intros [Hu Hb Hfr Hs Hr Hl] Hsl. constructor; auto.
      intros x Hx. destruct (Hb x Hx) as (H1 & H2 & H3 & H4).
      split; [exact H1 | split; [exact H2 | split; [| exact H4]]].
      intros Hin. destruct (Hsl x Hin); contradiction.
    Qed.

    (* The expression after a binding of [x] *)
    Lemma exp_ok_bind st e x e' :
      exp_ok st e ->
      dsubterm_e e' e ->
      unique_bindings e' -> bound_var e x -> ~ bound_var e' x ->
      (forall y, bound_var e' y -> bound_var e y) ->
      (forall y, occurs_free e' y -> y = x \/ occurs_free e y) ->
      (max_roots prims fenv e' <= max_roots prims fenv e)%nat ->
      (forall g n, calls_itself g n e' = true -> calls_itself g n e = true) ->
      exp_ok st e'.
    Proof.
      intros [Hu Hb Hfr Hs Hr Hl] Hd Hu' Hbx Hx Hbv Hfv Hmr Hci. constructor; auto.
      - intros y Hy. destruct (Hb y (Hbv y Hy)) as (H1 & H2 & H3 & H4).
        split; [exact H1 | split; [exact H2 | split; [exact H3 |]]].
        intros Hfy. destruct (Hfv y Hfy) as [-> | Hfy']; contradiction.
      - intros y Hy. destruct (Hfv y Hy) as [-> | Hy']; [apply (Hb x Hbx) | auto].
      - eapply good_sub; eauto.
      - lia.
      - intros g ps Hg Hc. eapply Hl; eauto.
    Qed.

    (* The expression of a branch *)
    Lemma exp_ok_sub st e e' :
      exp_ok st e ->
      dsubterm_e e' e ->
      unique_bindings e' ->
      (forall y, bound_var e' y -> bound_var e y) ->
      (forall y, occurs_free e' y -> occurs_free e y) ->
      (max_roots prims fenv e' <= max_roots prims fenv e)%nat ->
      (forall g n, calls_itself g n e' = true -> calls_itself g n e = true) ->
      exp_ok st e'.
    Proof.
      intros [Hu Hb Hfr Hs Hr Hl] Hd Hu' Hbv Hfv Hmr Hci. constructor; auto.
      - intros y Hy. destruct (Hb y (Hbv y Hy)) as (H1 & H2 & H3 & H4).
        split; [exact H1 | split; [exact H2 | split; [exact H3 |]]].
        intros Hfy. apply H4. auto.
      - eapply good_sub; eauto.
      - lia.
      - intros g ps Hg Hc. eapply Hl; eauto.
    Qed.

    (** ** The check for heap room *)

    Lemma st_ok_with_room st : st_ok st -> st_ok (with_room st).
    Proof.
      intros [H1 H2 H3 H4 H5 H6]. constructor; simpl; auto.
    Qed.

    Lemma enter_correct i st rho e le h m s st' :
      (i < K)%nat ->
      inv i st rho e le h m ->
      exp_ok st e ->
      enter prims fenv (Z.of_nat nroots) st e = Ret (s, st') ->
      exists le' h' m',
        runs ge fn lenv s le m le' m' /\
        inv i st' rho e le' h' m' /\
        step_ok h m h' m' /\
        st_stale st' = st_stale st /\ st_slots st' = st_slots st /\
        st_linked st' = st_linked st.
    Proof.
      intros Hi Hinv Hexp Hent. unfold enter in Hent.
      destruct (st_room st) eqn:Hroom.
      { apply Ret_inj in Hent. assert (s = Sskip) by congruence. assert (st' = st) by congruence.
        subst. exists le, h, m. split; [apply runs_skip |].
        split; [exact Hinv |]. split; [apply step_ok_refl | auto]. }
      destruct (check_here prims e) eqn:Hch.
      2:{ apply Ret_inj in Hent. assert (s = Sskip) by congruence.
          assert (st' = st) by congruence.
          subst. exists le, h, m. split; [apply runs_skip |].
          split; [exact Hinv |]. split; [apply step_ok_refl | auto]. }
      bind_inv Hent. apply Ret_inj in Hent. rename E into Hcr.
      assert (Hs_eq : s = x) by congruence. assert (Hst_eq : st' = with_room st) by congruence.
      subst s st'. clear Hent. rename x into s.
      destruct Hinv as (Hm & Hs & Htm).
      unfold check_room in Hcr.
      remember (live_vars fenv e) as live eqn:Hlive.
      remember (alloc_need prims e) as n eqn:Hneed.
      remember (List.filter (fun x => negb (in_list x (st_slots st))) live) as saved eqn:Hsaved_def.
      destruct (max_args <? Z.of_nat (length saved)) eqn:Hsaved; [discriminate |].
      apply Z.ltb_ge in Hsaved. apply Ret_inj in Hcr. subst s.
      (* the state before the check *)
      assert (Hd : st_dirty st = false).
      { destruct (st_dirty st) eqn:E; auto. rewrite (so_dirty _ Hs E) in Hroom. discriminate. }
      pose proof (mi_sync _ _ _ _ _ Hm Hd) as Hsync.
      pose proof (mi_wf _ _ _ _ _ Hm) as Hwf.
      pose proof (wf_free _ _ _ _ _ _ _ _ Hwf) as [Hfh [Hfr1 Hfr2] Hfs Hfa Hfp].
      pose proof (wf_range _ _ _ _ _ _ _ _ Hwf) as (Ht0 & Htmax & Htal).
      pose proof (ti_tinfo _ _ _ _ _ _ _ Htm) as Hti.
      assert (Hn : 0 <= Z.of_nat n <= nursery_size).
      { split; [lia |]. subst n. apply (eo_sub _ _ Hexp e). apply rt_refl. }
      assert (Hvar_ne : forall x, occurs_free e x -> x <> allocId /\ x <> tinfoId).
      { intros x Hx. apply (eo_free _ _ Hexp) in Hx. unfold allocId, tinfoId. split; lia. }
      set (le1 := PTree.set allocId (Vptr (free_block h) (Ptrofs.repr (free_start h))) le).
      assert (Hti1 : le1 ! tinfoId = Some (Vptr tb (Ptrofs.repr tofs))).
      { unfold le1. rewrite PTree.gso by discriminate. exact Hti. }
      assert (Hrun1 : runs ge fn lenv (Sset allocId tinfo_alloc) le m le1 m).
      { apply runs_set. eapply eval_load.
        - apply eval_tinfo_alloc; [exact Hstructs | exact Hti].
        - reflexivity.
        - erewrite tinfo_address by (eauto; ofs_lia). exact Hsync. }
      assert (Htest : eval_expr ge lenv le1 m
                (Ebinop Olt (Ebinop Osub tinfo_limit alloc tintnat)
                        (const (Z.of_nat n) tintnat) tint)
                (Val.of_bool (if zlt ((free_end h - free_start h) / 8) (Z.of_nat n)
                              then true else false))).
      { apply eval_room_test with (ab := free_block h); auto.
        - unfold nursery_size in Hn. rewrite int64_max_signed. lia.
        - eapply eval_load.
          + apply eval_tinfo_limit; [exact Hstructs | exact Hti1].
          + reflexivity.
          + erewrite tinfo_address by (eauto; ofs_lia). exact (wf_limit _ _ _ _ _ _ _ _ Hwf).
        - unfold le1. apply PTree.gss. }
      assert (Htm1 : tmp_inv i st rho e le1 h m).
      { eapply tmp_inv_temps; eauto.
        - rewrite Hti1. auto.
        - intros Hr. congruence.
        - intros y Hy _ _. unfold le1. apply PTree.gso. apply (Hvar_ne y Hy). }
      destruct (zlt ((free_end h - free_start h) / 8) (Z.of_nat n)) as [Hlt | Hge].
      2:{ (* there is room *)
        exists le1, h, m. split; [| split; [| split; [apply step_ok_refl | auto]]].
        - eapply runs_seq; [exact Hrun1 |].
          eapply runs_ifthenelse; [exact Htest | apply bool_val_of_bool | apply runs_skip].
        - split; [| split; [apply st_ok_with_room; auto |]].
          + eapply mem_inv_state; eauto.
          + destruct Htm1 as [T1 T2 T3 T4]. constructor; auto.
            intros _. split; [unfold le1; apply PTree.gss |].
            pose proof (Z.mul_div_le (free_end h - free_start h) 8). rewrite <- Hneed. lia. }
      (* the collector is called *)
      assert (Hsv : forall y, In y saved ->
                              occurs_free e y /\ M.get y fenv = None /\ ~ In y (st_stale st)).
      { intros y Hy. rewrite Hsaved_def in Hy. apply filter_In in Hy. destruct Hy as [Hl Hns].
        rewrite Hlive in Hl. apply live_vars_spec in Hl. destruct Hl as [Hl1 Hl2].
        apply negb_true_iff, in_list_not_In in Hns. split; [exact Hl1 | split; [exact Hl2 |]].
        intros Hst. apply Hns. apply (so_stale _ Hs). exact Hst. }
      assert (Hsaved_nd : NoDup saved).
      { rewrite Hsaved_def. apply NoDup_filter. rewrite Hlive. apply live_vars_NoDup. }
      destruct (temps_words i st rho e le1 h m saved Htm1 Hsv) as (vs & ws & Hvs & Hws & Hrs).
      pose proof (Forall2_length _ _ _ Hws) as Hlen_ws.
      change (@length positive saved) with (@length var saved) in Hlen_ws.
      pose proof (Forall2_length _ _ _ Hrs) as Hlen_vs.
      assert (Hwords : Forall is_word ws).
      { apply Forall_forall. intros w Hw. destruct (In_nth_error _ _ Hw) as [j Hj].
        destruct (Forall2_nth_r _ _ _ Hrs _ _ Hj) as (v & _ & Hr). eapply val_rel_word; eauto. }
      destruct (store_words_exists ws m tb (tofs + args_ofs + 8 * Z.of_nat 0)) as [m1 Hm1].
      { intros o Ho. apply (wf_perm _ _ _ _ _ _ _ _ Hwf). clear - Ho Hsaved Hlen_ws. ofs_lia. }
      { apply Z.divide_add_r; [apply Z.divide_add_r; auto |]; [exists 3; reflexivity | exists 0; reflexivity]. }
      assert (Hrun_save : runs ge fn lenv (save_args 0 saved) le1 m le1 m1).
      { eapply runs_save_args; eauto; lia. }
      set (R := fun (b : block) (o : Z) =>
                  b = tb /\ tofs + args_ofs <= o < tofs + args_ofs + 8 * Z.of_nat (length ws)).
      assert (Hun1 : Mem.unchanged_on (fun b o => ~ R b o) m m1).
      { eapply Mem.unchanged_on_implies; [apply (store_words_unchanged _ _ _ _ _ Hm1) |].
        intros b o Hnr _ [Hb Ho]. apply Hnr. split; auto. lia. }
      assert (Hkp1 : forall b, keeps_perm m m1 b).
      { intros b. eapply store_words_perm; eauto. }
      destruct (step_ok_region i st rho h m m1 R Hm Hun1 Hkp1) as [Hk1 Hst1].
      { intros b o [-> Ho]. right. right. split; auto. clear - Ho Hsaved Hlen_ws. ofs_lia. }
      assert (Hwf1 : tinfo_wf h (cur_frames st) m1 tb tofs).
      { eapply tinfo_wf_region; eauto. intros b o [-> Ho] Hdep.
        destruct (tinfo_dep_inv _ _ _ _ _ _ _ _ _ _ Hwf Hdep) as [[Hh _] | [(_ & Hne & _) | [_ Hr]]].
        - eapply wf_block; eauto.
        - congruence.
        - clear - Ho Hr Hsaved Hlen_ws. ofs_lia. }
      assert (Hsync1 : Mem.load Mptr m1 tb (tofs + alloc_ofs)
                       = Some (Vptr (free_block h) (Ptrofs.repr (free_start h)))).
      { eapply Mem.load_unchanged_on; eauto.
        intros o Ho [_ Hr]. change (size_chunk Mptr) with 8 in Ho. clear - Ho Hr. ofs_lia. }
      assert (Hm1inv : mem_inv i st rho h m1).
      { eapply mem_inv_kept; eauto.
        - intros j w Hj Hw. eapply Mem.load_unchanged_on; eauto. intros o _ [Hb _].
          assert (Hnr : nroots <> 0%nat) by (pose proof (so_nslots _ Hs); lia).
          destruct (Hown Hnr) as (_ & _ & Hrt & _). congruence.
        - eapply locals_ok_kept; eauto. exact (mi_locals _ _ _ _ _ Hm). }
      assert (Hargs1 : forall j w, nth_error ws j = Some w ->
                Mem.load Mptr m1 tb (tofs + args_ofs + 8 * Z.of_nat j) = Some w).
      { intros j w Hj. replace (tofs + args_ofs + 8 * Z.of_nat j)
          with (tofs + args_ofs + 8 * Z.of_nat 0 + 8 * Z.of_nat j) by lia.
        eapply store_words_load; eauto.
        rewrite Forall_forall in Hwords. specialize (Hwords w (nth_error_In _ _ Hj)).
        destruct w; try contradiction; reflexivity. }
      destruct (prog_gc _ _ _ _ _ _ _ Hprog) as (bgc & fdgc & Hbgc & Hfgc & Htygc).
      destruct (gc_collect _ _ _ Hgc bgc fdgc tb tofs h (cur_frames st) m1
                           (Z.of_nat (length saved)) (Z.of_nat n) Hbgc Hfgc)
        as (wg & h' & m2 & Hcall & Hroom' & Hok' & Hroots' & Hch').
      { split; auto. }
      { lia. }
      { exact Hn. }
      { intros j Hj. destruct (nth_error ws (Z.to_nat j)) as [w |] eqn:Hw.
        - exists w. split.
          + rewrite <- (Hargs1 _ _ Hw). f_equal. lia.
          + destruct (Forall2_nth_r _ _ _ Hrs _ _ Hw) as (v & _ & Hr).
            eapply val_rel_is_value. eapply val_rel_kept; eauto.
        - apply nth_error_None in Hw. lia. }
      destruct Hok' as [Hwf2 Hsync2].
      (* the variables are read back *)
      destruct (list_choice ws
                  (fun j w w' =>
                     Mem.load Mptr m2 tb (tofs + args_ofs + 8 * Z.of_nat j) = Some w' /\
                     forall F v, repr_val F h m1 v w -> repr_val F h' m2 v w'))
        as (ws' & Hlen' & Hws').
      { intros j w Hj. apply (Hroots' tb (tofs + args_ofs + 8 * Z.of_nat j)); auto.
        left. split; auto. exists (Z.of_nat j). split; auto.
        assert (j < length ws)%nat by (apply nth_error_Some; congruence). lia. }
      set (le2 := set_temps saved ws' le1).
      assert (Hsaved_ids : forall y, In y saved -> y <> tinfoId /\ y <> allocId).
      { intros y Hy. destruct (Hsv y Hy) as (Hfy & _). destruct (Hvar_ne y Hfy). auto. }
      assert (Hrun_load : runs ge fn lenv (load_args 0 saved) le1 m2 le2 m2).
      { eapply runs_load_args; eauto; try lia.
        - intros Hin. destruct (Hsaved_ids _ Hin). congruence.
        - rewrite Hlen'. symmetry. exact Hlen_ws.
        - intros j w' Hj. simpl.
          destruct (nth_error ws j) as [w |] eqn:Hw.
          + apply (Hws' j w w' Hw Hj).
          + apply nth_error_None in Hw.
            assert (j < length ws')%nat by (apply nth_error_Some; congruence). lia. }
      assert (Hslots2 : forall j y, nth_error (st_slots st) j = Some y ->
                exists v w, M.get y rho = Some v /\
                            Mem.load Mptr m2 rb (8 * Z.of_nat j) = Some w /\
                            val_rel i h' m2 v w).
      { eapply slots_after_call; eauto. }
      set (reread := fun y => in_list y live && negb (in_list y (st_stale st))).
      assert (Hre_free : forall y, reread y = true -> occurs_free e y /\ M.get y fenv = None).
      { intros y Hy. unfold reread in Hy. apply andb_true_iff in Hy. destruct Hy as [Hy _].
        apply in_list_In in Hy. rewrite Hlive in Hy. apply live_vars_spec in Hy. exact Hy. }
      assert (Hread : exists le3,
                 runs ge fn lenv (read_roots (Z.of_nat nroots) reread 0 (st_slots st)) le2 m2 le3 m2 /\
                 (forall y, ~ (In y (st_slots st) /\ reread y = true) -> le3 ! y = le2 ! y) /\
                 (forall j y, nth_error (st_slots st) j = Some y -> reread y = true ->
                              exists w, Mem.load Mptr m2 rb (8 * Z.of_nat j) = Some w /\
                                        le3 ! y = Some w)).
      { destruct (Nat.eq_dec nroots 0) as [Hz | Hnz].
        - assert (Hnil : st_slots st = []).
          { pose proof (so_nslots _ Hs). destruct (st_slots st); [auto | simpl in *; lia]. }
          rewrite Hnil. exists le2. split; [apply runs_skip |]. split; auto.
          intros j y Hj. destruct j; discriminate.
        - destruct (runs_read_roots ge fn lenv rb (Z.of_nat nroots) (lenv_roots Hnz) m2 reread
                                    (st_slots st) 0 le2) as (le3 & Hr3 & Ho3 & Hs3).
          + intros j y Hj _. destruct (Hslots2 j y Hj) as (v & w & _ & Hw & _). eauto.
          + pose proof (so_nslots _ Hs). pose proof nroots_unsigned. lia.
          + exists le3. split; [exact Hr3 |]. split; [exact Ho3 |].
            intros j y Hj Hk. apply (Hs3 (so_nodup _ Hs) j y Hj Hk). }
      destruct Hread as (le3 & Hrun_read & Hother3 & Hset3).
      set (le4 := PTree.set allocId (Vptr (free_block h') (Ptrofs.repr (free_start h'))) le3).
      assert (Hti2 : le2 ! tinfoId = Some (Vptr tb (Ptrofs.repr tofs))).
      { unfold le2. rewrite set_temps_other; auto.
        intros Hin. destruct (Hsaved_ids _ Hin). congruence. }
      assert (Hti3 : le3 ! tinfoId = Some (Vptr tb (Ptrofs.repr tofs))).
      { rewrite Hother3; auto. intros [_ Hre]. destruct (Hre_free _ Hre) as [Hfv _].
        destruct (Hvar_ne _ Hfv). congruence. }
      assert (Hrun_last : runs ge fn lenv (Sset allocId tinfo_alloc) le3 m2 le4 m2).
      { apply runs_set. eapply eval_load.
        - apply eval_tinfo_alloc; [exact Hstructs | exact Hti3].
        - reflexivity.
        - erewrite tinfo_address by (eauto; ofs_lia). exact Hsync2. }
      assert (Hrun_call : runs ge fn lenv
                (Scall None (Evar gcArgsId gc_args_ty)
                       [tinfo; const (Z.of_nat (length saved)) tvalue;
                        const (Z.of_nat n) tvalue]) le1 m1 le1 m2).
      { change le1 with (set_opttemp None wg le1) at 2.
        eapply runs_call with (vf := Vptr bgc Ptrofs.zero).
        - reflexivity.
        - eapply eval_Elvalue.
          + apply eval_Evar_global; [apply lenv_other; discriminate | exact Hbgc].
          + apply deref_loc_reference. reflexivity.
        - econstructor; [apply eval_Etempvar; exact Hti1 | reflexivity |].
          econstructor; [apply eval_const | reflexivity |].
          econstructor; [apply eval_const | reflexivity |].
          constructor.
        - simpl. destruct (Ptrofs.eq_dec Ptrofs.zero Ptrofs.zero); [exact Hfgc | congruence].
        - exact Htygc.
        - exact Hcall. }
      exists le4, h', m2. split; [| split; [| split]].
      - eapply runs_seq; [exact Hrun1 |].
        eapply runs_ifthenelse; [exact Htest | apply bool_val_of_bool |].
        eapply runs_seq; [exact Hrun_save |].
        eapply runs_seq; [exact Hrun_call |].
        eapply runs_seq; [exact Hrun_load |].
        eapply runs_seq; [exact Hrun_read | exact Hrun_last].
      - split; [| split; [apply st_ok_with_room; auto |]].
        + constructor.
          * exact Hwf2.
          * intros _. exact Hsync2.
          * exact Hslots2.
          * eapply locals_after_call; eauto.
        + constructor.
          * unfold le4. rewrite PTree.gso by discriminate. exact Hti3.
          * intros _. split; [unfold le4; apply PTree.gss |]. rewrite <- Hneed. lia.
          * intros y Hy Hfy. destruct (ti_vars _ _ _ _ _ _ _ Htm y Hy Hfy) as (v & Hv & _).
            exists v. split; auto. intros Hns.
            assert (Hy4 : le4 ! y = le3 ! y).
            { unfold le4. apply PTree.gso. apply (Hvar_ne y Hy). }
            assert (Hlive_y : In y live).
            { rewrite Hlive. apply live_vars_spec. auto. }
            destruct (in_dec Pos.eq_dec y (st_slots st)) as [Hin | Hnin].
            -- destruct (In_nth_error _ _ Hin) as [j Hj].
               destruct (Hslots2 j y Hj) as (v' & w' & Hv' & Hw' & Hr').
               assert (v' = v) by congruence. subst v'.
               assert (Hre : reread y = true).
               { unfold reread. apply andb_true_iff. split; [apply in_list_In; auto |].
                 apply negb_true_iff. apply in_list_not_In. exact Hns. }
               destruct (Hset3 j y Hj Hre) as (w'' & Hw'' & Hle3).
               assert (w'' = w') by congruence. subst w''.
               exists w'. split; [congruence | exact Hr'].
            -- assert (Hsy : In y saved).
               { rewrite Hsaved_def. apply filter_In. split; auto.
                 apply negb_true_iff. apply in_list_not_In. exact Hnin. }
               destruct (In_nth_error _ _ Hsy) as [j Hj].
               destruct (Forall2_nth_l _ _ _ Hvs _ _ Hj) as (v0 & Hv0 & Hgv0).
               assert (v0 = v) by congruence. subst v0.
               destruct (Forall2_nth_l _ _ _ Hrs _ _ Hv0) as (w & Hw & Hr).
               destruct (nth_error ws' j) as [w' |] eqn:Hw'.
               2:{ apply nth_error_None in Hw'.
                   assert (j < length ws)%nat by (apply nth_error_Some; congruence). lia. }
               destruct (Hws' j w w' Hw Hw') as [_ Hrep].
               exists w'. split.
               ++ rewrite Hy4, Hother3 by tauto. unfold le2. eapply set_temps_nth; eauto.
               ++ apply Hrep. eapply val_rel_kept; eauto.
          * exact (ti_funs _ _ _ _ _ _ _ Htm).
      - eapply step_ok_trans; [exact Hst1 |]. eapply step_ok_call; eauto.
      - auto.
    Qed.

    (** ** The roots before a call *)

    (* The roots hold the values of the variables [slots] *)
    Definition slots_hold (i : nat) (slots : list var) (rho : eval.env) (h : heap) (m : mem)
      : Prop :=
      forall j x, nth_error slots j = Some x ->
                  exists v w, M.get x rho = Some v /\
                              Mem.load Mptr m rb (8 * Z.of_nat j) = Some w /\
                              val_rel i h m v w.

    Lemma roots_writable h m k :
      locals_ok h m -> nroots <> 0%nat -> (k <= nroots)%nat ->
      Mem.range_perm m rb 0 (8 * Z.of_nat k) Cur Writable.
    Proof.
      intros Hl Hn Hk o Ho. eapply Mem.perm_implies; [apply (lo_roots _ _ Hl Hn); lia | constructor].
    Qed.

    Lemma own_frame_ok i k slots rho h m :
      locals_ok h m -> nroots <> 0%nat -> (k <= nroots)%nat -> length slots = k ->
      slots_hold i slots rho h m ->
      frame_ok cenv ge h m tb (own k).
    Proof.
      intros Hl Hn Hk Hlen Hsl. destruct (Hown Hn) as (Hfr & Hft & Hrt & _).
      constructor; simpl.
      - apply (lo_heap _ _ Hl Hn).
      - auto.
      - pose proof nroots_unsigned. lia.
      - replace (0 + 8 * Z.of_nat k) with (8 * Z.of_nat k) by lia. eapply roots_writable; eauto.
      - intros j Hj. destruct (nth_error slots (Z.to_nat j)) as [x |] eqn:Hx.
        + destruct (Hsl _ _ Hx) as (v & w & _ & Hw & Hr). exists w. split.
          * rewrite <- Hw. f_equal. lia.
          * eapply val_rel_is_value; eauto.
        + apply nth_error_None in Hx. lia.
      - split; eapply Mem.perm_valid_block.
        + apply (lo_frame _ _ Hl Hn 0). lia.
        + apply (lo_roots _ _ Hl Hn 0). lia.
      - lia.
      - split; [lia | split; [rewrite ptrofs_max_unsigned; lia |]].
        intros o Ho. eapply Mem.perm_implies; [apply (lo_frame _ _ Hl Hn); lia | constructor].
    Qed.

    (* [tinfo->alloc = alloc], with the facts about the memory only *)
    Lemma sync_run st le h fs m :
      tinfo_wf h fs m tb tofs ->
      le ! tinfoId = Some (Vptr tb (Ptrofs.repr tofs)) ->
      (st_dirty st = true ->
       le ! allocId = Some (Vptr (free_block h) (Ptrofs.repr (free_start h)))) ->
      (st_dirty st = false ->
       Mem.load Mptr m tb (tofs + alloc_ofs)
       = Some (Vptr (free_block h) (Ptrofs.repr (free_start h)))) ->
      exists m',
        runs ge fn lenv (sync st) le m le m' /\
        Mem.load Mptr m' tb (tofs + alloc_ofs)
        = Some (Vptr (free_block h) (Ptrofs.repr (free_start h))) /\
        tinfo_wf h fs m' tb tofs /\
        Mem.unchanged_on (fun b o => ~ (b = tb /\ tofs <= o < tofs + 8)) m m' /\
        (forall b, keeps_perm m m' b).
    Proof.
      intros Hwf Hti Hal Hsy. unfold sync. destruct (st_dirty st) eqn:Hd.
      - destruct (tinfo_field_store h _ m alloc_ofs
                    (Vptr (free_block h) (Ptrofs.repr (free_start h))) Hwf)
          as [m' Hm']; try (unfold alloc_ofs; ofs_lia). { apply Z.divide_0_r. }
        exists m'. split; [| split; [| split; [| split]]].
        + eapply runs_assign.
          * apply eval_tinfo_alloc; [exact Hstructs | exact Hti].
          * apply eval_Etempvar. auto.
          * reflexivity.
          * reflexivity.
          * exact I.
          * erewrite tinfo_address by (eauto; ofs_lia). exact Hm'.
        + erewrite Mem.load_store_same; eauto. reflexivity.
        + eapply tinfo_wf_store_tinfo; eauto. left. change (size_chunk Mptr) with 8. ofs_lia.
        + eapply Mem.store_unchanged_on; eauto. intros j Hj Hn. apply Hn.
          change (size_chunk Mptr) with 8 in Hj. split; auto. ofs_lia.
        + intros b. eapply store_keeps_perm; eauto.
      - exists m. split; [apply runs_skip |]. split; [auto |]. split; [auto |].
        split; [apply Mem.unchanged_on_refl | intros b o k p Hp; exact Hp].
    Qed.

    (* [frame.next = roots + k] *)
    Lemma set_next_run le m m' k :
      nroots <> 0%nat ->
      Mem.store Mptr m fb next_ofs (Vptr rb (Ptrofs.repr (8 * Z.of_nat k))) = Some m' ->
      runs ge fn lenv (set_next (Z.of_nat nroots) k) le m le m'.
    Proof.
      intros Hn Hst. unfold set_next. eapply runs_assign.
      - apply eval_frame_next; [exact Hstructs | apply lenv_frame; auto].
      - eapply eval_roots_plus. apply lenv_roots; auto.
      - reflexivity.
      - reflexivity.
      - exact I.
      - exact Hst.
    Qed.

    (* [frame.root = roots; frame.prev = tinfo->fp; tinfo->fp = &frame] *)
    Lemma link_run le m ma mb mc fp :
      nroots <> 0%nat ->
      le ! tinfoId = Some (Vptr tb (Ptrofs.repr tofs)) ->
      0 <= tofs -> tofs + tinfo_size <= Ptrofs.max_unsigned ->
      Mem.store Mptr m fb root_ofs (Vptr rb Ptrofs.zero) = Some ma ->
      Mem.load Mptr ma tb (tofs + fp_ofs) = Some fp -> is_word fp ->
      Mem.store Mptr ma fb prev_ofs fp = Some mb ->
      Mem.store Mptr mb tb (tofs + fp_ofs) (Vptr fb Ptrofs.zero) = Some mc ->
      runs ge fn lenv (link (Z.of_nat nroots)) le m le mc.
    Proof.
      intros Hn Hti Ht0 Htmax Ha Hfp Hw Hb Hc. unfold link.
      assert (Haddr : Ptrofs.unsigned (Ptrofs.repr (tofs + fp_ofs)) = tofs + fp_ofs).
      { apply Ptrofs.unsigned_repr. ofs_lia. }
      eapply runs_seq; [| eapply runs_seq].
      - eapply runs_assign.
        + apply eval_frame_root; [exact Hstructs | apply lenv_frame; auto].
        + eapply eval_roots. apply lenv_roots; auto.
        + reflexivity.
        + reflexivity.
        + exact I.
        + exact Ha.
      - eapply runs_assign.
        + apply eval_frame_prev; [exact Hstructs | apply lenv_frame; auto].
        + eapply eval_load.
          * apply eval_tinfo_fp; [exact Hstructs | exact Hti].
          * reflexivity.
          * rewrite Haddr. exact Hfp.
        + reflexivity.
        + reflexivity.
        + exact Hw.
        + exact Hb.
      - eapply runs_assign.
        + apply eval_tinfo_fp; [exact Hstructs | exact Hti].
        + apply eval_frame_addr. apply lenv_frame; auto.
        + reflexivity.
        + reflexivity.
        + exact I.
        + rewrite Haddr. exact Hc.
    Qed.

    (* The variables [live] are written to the roots *)
    Lemma write_roots_correct i st rho e le h m live :
      (i < K)%nat -> inv i st rho e le h m ->
      NoDup live ->
      (forall x, In x live -> occurs_free e x /\ M.get x fenv = None) ->
      (length live <= nroots)%nat -> nroots <> 0%nat ->
      exists m',
        runs ge fn lenv (write_roots (Z.of_nat nroots) st 0 (st_slots st) (root_layout st live))
             le m le m' /\
        Mem.unchanged_on (fun b o => ~ (b = rb /\ 0 <= o < 8 * Z.of_nat (length live))) m m' /\
        (forall b, keeps_perm m m' b) /\
        slots_hold i (root_layout st live) rho h m'.
    Proof.
      intros Hi (Hm & Hs & Htm) Hnd Hlive Hlen Hn.
      destruct (root_layout_spec st live (so_nodup _ Hs) Hnd) as (Hslen & Hsnd & Hsin & Hskeep).
      remember (root_layout st live) as slots eqn:Hslots.
      pose proof (mi_locals _ _ _ _ _ Hm) as Hloc.
      set (src := fun x : var =>
                    if in_list x (st_stale st)
                    then match index_of x (st_slots st) with
                         | Some j => match Mem.load Mptr m rb (8 * Z.of_nat j) with
                                     | Some w => w
                                     | None => Vundef
                                     end
                         | None => Vundef
                         end
                    else match le ! x with
                         | Some w => w
                         | None => Vundef
                         end).
      (* the word of a variable that is written *)
      assert (Hsrc : forall p x, nth_error slots p = Some x -> nth_error (st_slots st) p <> Some x ->
                (exists v, M.get x rho = Some v /\ val_rel i h m v (src x)) /\
                if in_list x (st_stale st)
                then exists j, index_of x (st_slots st) = Some j /\ (length live <= j)%nat /\
                               8 * Z.of_nat j <= Ptrofs.max_unsigned /\
                               Mem.load Mptr m rb (8 * Z.of_nat j) = Some (src x)
                else le ! x = Some (src x)).
      { intros p x Hp Hne.
        assert (Hxl : In x live) by (apply Hsin; eapply nth_error_In; eauto).
        destruct (Hlive x Hxl) as [Hfx Hnf]. unfold src.
        destruct (in_list x (st_stale st)) eqn:Hst.
        - apply in_list_In in Hst. apply (so_stale _ Hs) in Hst.
          destruct (index_of_In _ _ Hst) as [j Hj]. rewrite Hj.
          pose proof (index_of_nth _ _ _ Hj) as Hjx.
          destruct (mi_slots _ _ _ _ _ Hm j x Hjx) as (v & w & Hv & Hw & Hr). rewrite Hw.
          split; [eauto |]. exists j. split; [reflexivity |]. split; [| split; [| exact Hw]].
          + destruct (le_lt_dec (length live) j) as [Hle | Hlt]; auto.
            exfalso. apply Hne. pose proof (Hskeep j x Hjx Hlt Hxl) as Hjs.
            assert (p = j) by (eapply nth_error_NoDup; eauto). subst p. exact Hjx.
          + assert (j < length (st_slots st))%nat by (apply nth_error_Some; congruence).
            pose proof (so_nslots _ Hs). pose proof nroots_unsigned. lia.
        - apply in_list_not_In in Hst.
          destruct (ti_vars _ _ _ _ _ _ _ Htm x Hfx Hnf) as (v & Hv & Hw).
          destruct (Hw Hst) as (w & Hlw & Hr). rewrite Hlw. split; eauto. }
      destruct (runs_write_roots ge fn lenv rb (Z.of_nat nroots) (lenv_roots Hn) le st src
                                 (length live) slots (st_slots st) 0 m)
        as (m' & Hrun & Hun & Hkp & Hw & Hsame).
      { simpl. exact Hslen. }
      { pose proof nroots_unsigned. lia. }
      { eapply roots_writable; eauto. }
      { intros p x Hp Hne. destruct (Hsrc p x Hp Hne) as [(v & _ & Hr) Hx].
        split; [eapply val_rel_word; eauto | exact Hx]. }
      assert (Hk : data_kept h m h m').
      { split; auto. eapply Mem.unchanged_on_implies; eauto.
        intros b o [Hh _] _ [-> _]. apply (lo_heap _ _ Hloc Hn). exact Hh. }
      exists m'. split; [exact Hrun |]. split; [exact Hun |]. split; [exact Hkp |].
      intros p x Hp.
      destruct (nth_error (st_slots st) p) as [y |] eqn:Hy;
        [destruct (Pos.eq_dec y x) as [-> | Hne] |].
      - destruct (mi_slots _ _ _ _ _ Hm p x Hy) as (v & w & Hv & Hlw & Hr).
        exists v, w. split; [auto |]. split; [| eapply val_rel_kept; eauto].
        rewrite <- Hlw. apply (Hsame p x Hp Hy).
      - destruct (Hsrc p x Hp) as [(v & Hv & Hr) _]; [congruence |].
        exists v, (src x). split; [auto |]. split; [| eapply val_rel_kept; eauto].
        apply (Hw p x Hp). congruence.
      - destruct (Hsrc p x Hp) as [(v & Hv & Hr) _]; [congruence |].
        exists v, (src x). split; [auto |]. split; [| eapply val_rel_kept; eauto].
        apply (Hw p x Hp). congruence.
    Qed.

    Lemma slots_hold_kept i slots rho h m m' :
      slots_hold i slots rho h m ->
      data_kept h m h m' ->
      (forall j w, Mem.load Mptr m rb (8 * Z.of_nat j) = Some w ->
                   Mem.load Mptr m' rb (8 * Z.of_nat j) = Some w) ->
      slots_hold i slots rho h m'.
    Proof.
      intros Hsl Hk Hl j x Hj. destruct (Hsl j x Hj) as (v & w & Hv & Hw & Hr).
      exists v, w. split; [auto |]. split; [auto | eapply val_rel_kept; eauto].
    Qed.

    (* A store in the frame of the function or in the thread info keeps the roots *)
    Lemma slots_hold_store i slots rho h m chunk b o v m' :
      slots_hold i slots rho h m ->
      Mem.store chunk m b o v = Some m' ->
      ~ heap_blocks h b -> b <> rb ->
      slots_hold i slots rho h m'.
    Proof.
      intros Hsl Hst Hh Hb. eapply slots_hold_kept; eauto.
      - eapply store_data_kept; eauto. intros j _ [Ha _]. contradiction.
      - intros j w Hw. rewrite <- Hw. eapply Mem.load_store_other; eauto.
    Qed.

    Lemma frame_field_store h m delta v :
      locals_ok h m -> nroots <> 0%nat -> (delta = 0 \/ delta = 8 \/ delta = 16) ->
      exists m', Mem.store Mptr m fb delta v = Some m'.
    Proof.
      intros Hl Hn Hd. destruct (Mem.valid_access_store m Mptr fb delta v) as [m' Hm']; eauto.
      split.
      - intros o Ho. change (size_chunk Mptr) with 8 in Ho.
        eapply Mem.perm_implies; [apply (lo_frame _ _ Hl Hn); lia | constructor].
      - destruct Hd as [-> | [-> | ->]]; [exists 0 | exists 1 | exists 2]; reflexivity.
    Qed.

    (* The statements before a call after which the variables [live] are needed *)
    Lemma push_roots_correct i st rho e le h m live s stp :
      (i < K)%nat -> inv i st rho e le h m ->
      NoDup live ->
      (forall x, In x live -> occurs_free e x /\ M.get x fenv = None) ->
      (length live <= nroots)%nat ->
      push_roots (Z.of_nat nroots) st live = (s, stp) ->
      exists m',
        runs ge fn lenv s le m le m' /\
        tinfo_wf h (cur_frames stp) m' tb tofs /\
        slots_hold i (st_slots stp) rho h m' /\
        Mem.load Mptr m' tb (tofs + alloc_ofs) = Mem.load Mptr m tb (tofs + alloc_ofs) /\
        data_kept h m h m' /\ step_ok h m h m' /\ locals_ok h m' /\
        st_ok stp /\ st_stale stp = st_slots stp /\
        st_room stp = false /\ st_dirty stp = false /\
        (forall x, In x (st_slots stp) <-> In x live).
    Proof.
      intros Hi Hinv Hnd Hlive Hlen Hpush. pose proof Hinv as (Hm & Hs & Htm).
      unfold push_roots in Hpush. apply pair_equal_spec in Hpush. destruct Hpush as [Hs_eq Hst_eq].
      destruct (root_layout_spec st live (so_nodup _ Hs) Hnd) as (Hslen & Hsnd & Hsin & Hskeep).
      remember (root_layout st live) as slots eqn:Hslots.
      pose proof (mi_wf _ _ _ _ _ Hm) as Hwf.
      pose proof (mi_locals _ _ _ _ _ Hm) as Hloc.
      pose proof (wf_range _ _ _ _ _ _ _ _ Hwf) as (Ht0 & Htmax & Htal).
      pose proof (wf_block _ _ _ _ _ _ _ _ Hwf) as Htb.
      assert (Hstok : forall l, (l = true -> nroots <> 0%nat) -> (l = false -> slots = []) ->
                                st_ok (mkState l slots slots false false)).
      { intros l Hl1 Hl2. constructor; simpl; auto.
        - apply incl_refl.
        - lia. }
      destruct (Nat.eq_dec nroots 0) as [Hz | Hn].
      { (* the function has no roots *)
        assert (Hlnil : slots = []) by (destruct slots; [auto | simpl in *; lia]).
        assert (Honil : st_slots st = []).
        { pose proof (so_nslots _ Hs). destruct (st_slots st); [auto | simpl in *; lia]. }
        assert (Hlk : st_linked st = false).
        { destruct (st_linked st) eqn:E; auto. exfalso. apply (so_frame _ Hs E). exact Hz. }
        rewrite ?Hlnil, ?Honil, ?Hlk in Hs_eq. rewrite ?Hlnil, ?Honil, ?Hlk in Hst_eq.
        simpl in Hs_eq, Hst_eq. subst s stp.
        exists m. split; [apply runs_skip |]. simpl.
        split; [unfold cur_frames in *; rewrite Hlk in Hwf; exact Hwf |].
        split; [intros j x Hj; destruct j; discriminate |].
        split; [reflexivity |]. split; [apply data_kept_refl |]. split; [apply step_ok_refl |].
        split; [exact Hloc |].
        split; [constructor; simpl; auto; try discriminate; try apply incl_refl; try constructor; lia |].
        split; [reflexivity |]. split; [reflexivity |]. split; [reflexivity |].
        intros x. rewrite <- Hsin. rewrite Hlnil. tauto. }
      destruct (Hown Hn) as (Hfr & Hft & Hrt & Hnf & Hnr).
      destruct (lo_heap _ _ Hloc Hn) as [Hfh Hrh].
      destruct (write_roots_correct i st rho e le h m live Hi Hinv Hnd Hlive Hlen Hn)
        as (m1 & Hrun1 & Hun1 & Hkp1 & Hhold1).
      rewrite <- Hslots in Hrun1, Hhold1.
      set (R := fun (b : block) (o : Z) =>
                  own_blocks b o \/ (b = tb /\ tofs + fp_ofs <= o < tofs + fp_ofs + 8)).
      assert (Hun1' : Mem.unchanged_on (fun b o => ~ R b o) m m1).
      { eapply Mem.unchanged_on_implies; eauto. intros b o HnR _ [-> _]. apply HnR.
        left. split; auto. }
      assert (Hstore_un : forall chunk ma b o v mb,
                 Mem.store chunk ma b o v = Some mb ->
                 (forall j, o <= j < o + size_chunk chunk -> R b j) ->
                 Mem.unchanged_on (fun b o => ~ R b o) ma mb).
      { intros chunk ma b o v mb Hst HR. eapply Mem.store_unchanged_on; [exact Hst |].
        intros j Hj HnR. apply HnR. auto. }
      (* what follows from the changes being in the frame, the roots and [tinfo->fp] *)
      assert (Hfinish : forall m',
                 Mem.unchanged_on (fun b o => ~ R b o) m m' -> (forall b, keeps_perm m m' b) ->
                 Mem.load Mptr m' tb (tofs + alloc_ofs) = Mem.load Mptr m tb (tofs + alloc_ofs) /\
                 data_kept h m h m' /\ step_ok h m h m' /\ locals_ok h m').
      { intros m' Hun Hkp. split; [| split; [| split]].
        - eapply Mem.load_unchanged_on_1; eauto.
          + eapply Mem.perm_valid_block. apply (wf_perm _ _ _ _ _ _ _ _ Hwf tofs). ofs_lia.
          + intros o Ho [[_ [Hb | Hb]] | [_ Hr]]; try congruence.
            change (size_chunk Mptr) with 8 in Ho. ofs_lia.
        - eapply step_ok_region; eauto. intros b o [Ho | [-> Hr]]; [auto |].
          right. right. split; auto. ofs_lia.
        - eapply step_ok_region; eauto. intros b o [Ho | [-> Hr]]; [auto |].
          right. right. split; auto. ofs_lia.
        - eapply locals_ok_kept; eauto. }
      destruct (Hfinish m1 Hun1' Hkp1) as (Hal1 & Hk1 & Hst1 & Hloc1).
      assert (Hin_iff : forall x, In x slots <-> In x live) by (intros; apply Hsin).
      destruct (st_linked st) eqn:Hlinked.
      - (* the frame is registered *)
        unfold cur_frames in Hwf. rewrite Hlinked in Hwf.
        assert (Hwf1 : tinfo_wf h (own (length (st_slots st)) :: fs0) m1 tb tofs).
        { eapply tinfo_wf_roots; eauto.
          - eapply Mem.unchanged_on_implies; [exact Hun1 |].
            intros b o Hb _ [Heq _]. simpl in Hb. congruence.
          - intros j Hj. simpl in Hj. simpl.
            destruct (le_lt_dec (length live) (Z.to_nat j)) as [Hge | Hlt].
            + destruct (nth_error (st_slots st) (Z.to_nat j)) as [y |] eqn:Hy.
              2:{ apply nth_error_None in Hy. lia. }
              destruct (mi_slots _ _ _ _ _ Hm _ _ Hy) as (v & w & _ & Hw & Hr).
              exists w. split.
              * eapply Mem.load_unchanged_on; [exact Hun1 | |].
                -- intros o Ho [_ Hrange]. change (size_chunk Mptr) with 8 in Ho. lia.
                -- rewrite <- Hw. f_equal. lia.
              * eapply val_rel_is_value. eapply val_rel_kept; eauto.
            + destruct (nth_error slots (Z.to_nat j)) as [y |] eqn:Hy.
              2:{ apply nth_error_None in Hy. lia. }
              destruct (Hhold1 _ _ Hy) as (v & w & _ & Hw & Hr).
              exists w. split; [| eapply val_rel_is_value; eauto].
              rewrite <- Hw. f_equal. lia. }
        cbn [orb andb negb] in Hs_eq, Hst_eq.
        destruct (Nat.eqb (length slots) (length (st_slots st))) eqn:Hkk.
        + (* the same number of roots *)
          apply Nat.eqb_eq in Hkk. cbn [orb andb negb] in Hs_eq. subst s stp.
          exists m1. split; [eapply runs_seq; [exact Hrun1 | eapply runs_seq; apply runs_skip] |].
          simpl. unfold cur_frames. simpl. rewrite Hkk.
          split; [exact Hwf1 |]. split; [exact Hhold1 |].
          split; [exact Hal1 |]. split; [exact Hk1 |]. split; [exact Hst1 |].
          split; [exact Hloc1 |]. split; [apply Hstok; [auto | discriminate] |].
          split; [reflexivity |]. split; [reflexivity |]. split; [reflexivity | exact Hin_iff].
        + (* [frame.next] changes *)
          cbn [orb andb negb] in Hs_eq. subst s stp.
          destruct (frame_field_store h m1 next_ofs
                      (Vptr rb (Ptrofs.repr (8 * Z.of_nat (length slots)))) Hloc1 Hn)
            as [m2 Hm2]; [now left |].
          assert (Hun2 : Mem.unchanged_on (fun b o => ~ R b o) m m2).
          { eapply Mem.unchanged_on_trans; [exact Hun1' |]. eapply Hstore_un; eauto.
            intros j _. left. split; auto. }
          assert (Hkp2 : forall b, keeps_perm m m2 b).
          { intros b o k p Hp. eapply Mem.perm_store_1; eauto. apply Hkp1. exact Hp. }
          destruct (Hfinish m2 Hun2 Hkp2) as (Hal2 & Hk2 & Hst2 & Hloc2).
          exists m2. split; [| split; [| split; [| split; [| split; [| split; [| split]]]]]]; auto.
          * eapply runs_seq; [exact Hrun1 |].
            eapply runs_seq; [eapply set_next_run; eauto | apply runs_skip].
          * simpl. unfold cur_frames. simpl.
            apply (tinfo_wf_set_next cenv ge gc_inv Hgc h fs0 m1 m2 tb tofs (own (length (st_slots st)))
                                     (Z.of_nat (length slots))); auto.
            eapply own_frame_ok; eauto. lia.
          * simpl. eapply slots_hold_store; eauto.
          * split; [apply Hstok; [auto | discriminate] |].
            split; [reflexivity |]. split; [reflexivity |]. split; [reflexivity | exact Hin_iff].
      - (* the frame is not registered *)
        unfold cur_frames in Hwf. rewrite Hlinked in Hwf.
        assert (Honil : st_slots st = []) by (apply (so_linked _ Hs Hlinked)).
        assert (Hwf1 : tinfo_wf h fs0 m1 tb tofs).
        { eapply tinfo_wf_region with (R := fun b o => b = rb); eauto.
          - eapply Mem.unchanged_on_implies; [exact Hun1 |]. intros b o Hb _ [Heq _]. congruence.
          - intros b o -> Hdep.
            destruct (tinfo_dep_inv _ _ _ _ _ _ _ _ _ _ Hwf Hdep)
              as [[Hh _] | [(_ & _ & fr & Hin & Hb) | [Hb _]]]; auto.
            destruct (Hnr fr Hin). destruct Hb; auto. }
        rewrite Honil in Hs_eq, Hrun1.
        cbn [orb andb negb length] in Hs_eq, Hst_eq.
        destruct (length slots) as [| k'] eqn:Hk.
        + (* nothing to keep *)
          assert (Hlnil : slots = []) by (destruct slots; [auto | discriminate]).
          cbn [orb andb negb length Nat.ltb Nat.leb Nat.eqb] in Hs_eq, Hst_eq. subst s stp.
          exists m1. split; [eapply runs_seq; [exact Hrun1 | eapply runs_seq; apply runs_skip] |].
          simpl. unfold cur_frames. simpl.
          split; [exact Hwf1 |]. split; [exact Hhold1 |].
          split; [exact Hal1 |]. split; [exact Hk1 |]. split; [exact Hst1 |].
          split; [exact Hloc1 |]. split; [apply Hstok; [discriminate | auto] |].
          split; [reflexivity |]. split; [reflexivity |]. split; [reflexivity | exact Hin_iff].
        + (* the frame is registered now *)
          cbn [orb andb negb length Nat.ltb Nat.leb Nat.eqb] in Hs_eq, Hst_eq. subst s stp.
          destruct (wf_fp _ _ _ _ _ _ _ _ Hwf1) as (fp0 & Hfp0 & Hfrs0).
          destruct (frame_field_store h m1 next_ofs
                      (Vptr rb (Ptrofs.repr (8 * Z.of_nat (S k')))) Hloc1 Hn)
            as [m2 Hm2]; [now left |].
          assert (Hloc2 : locals_ok h m2) by (eapply locals_ok_store; [exact Hloc1 | exact Hm2]).
          destruct (frame_field_store h m2 root_ofs (Vptr rb Ptrofs.zero) Hloc2 Hn)
            as [m3 Hm3]; [right; now left |].
          assert (Hloc3 : locals_ok h m3) by (eapply locals_ok_store; [exact Hloc2 | exact Hm3]).
          destruct (frame_field_store h m3 prev_ofs fp0 Hloc3 Hn) as [m4 Hm4]; [right; now right |].
          assert (Hwf4 : tinfo_wf h fs0 m4 tb tofs).
          { eapply (tinfo_wf_store_other _ _ _ Hgc); [| exact Hm4 | auto | auto | auto].
            eapply (tinfo_wf_store_other _ _ _ Hgc); [| exact Hm3 | auto | auto | auto].
            eapply (tinfo_wf_store_other _ _ _ Hgc); [| exact Hm2 | auto | auto | auto]. exact Hwf1. }
          destruct (tinfo_field_store h fs0 m4 fp_ofs (Vptr fb Ptrofs.zero) Hwf4) as [m5 Hm5];
            try ofs_lia. { exists 1027. reflexivity. }
          assert (Hfp3 : Mem.load Mptr m3 tb (tofs + fp_ofs) = Some fp0).
          { rewrite <- Hfp0. erewrite Mem.load_store_other; [| exact Hm3 | now left].
            eapply Mem.load_store_other; [exact Hm2 | now left]. }
          assert (Hun5 : Mem.unchanged_on (fun b o => ~ R b o) m m5).
          { eapply Mem.unchanged_on_trans; [exact Hun1' |].
            eapply Mem.unchanged_on_trans; [eapply Hstore_un; [exact Hm2 |] |].
            { intros j _. left. split; auto. }
            eapply Mem.unchanged_on_trans; [eapply Hstore_un; [exact Hm3 |] |].
            { intros j _. left. split; auto. }
            eapply Mem.unchanged_on_trans; [eapply Hstore_un; [exact Hm4 |] |].
            { intros j _. left. split; auto. }
            eapply Hstore_un; [exact Hm5 |]. intros j Hj. right. split; auto. }
          assert (Hkp5 : forall b, keeps_perm m m5 b).
          { intros b o k p Hp.
            eapply Mem.perm_store_1; [exact Hm5 |]. eapply Mem.perm_store_1; [exact Hm4 |].
            eapply Mem.perm_store_1; [exact Hm3 |]. eapply Mem.perm_store_1; [exact Hm2 |].
            apply Hkp1. exact Hp. }
          destruct (Hfinish m5 Hun5 Hkp5) as (Hal5 & Hk5 & Hst5 & Hloc5).
          assert (Hhold4 : slots_hold i slots rho h m4).
          { eapply slots_hold_store; [| exact Hm4 | auto | auto].
            eapply slots_hold_store; [| exact Hm3 | auto | auto].
            eapply slots_hold_store; [| exact Hm2 | auto | auto]. exact Hhold1. }
          assert (Hloc4 : locals_ok h m4) by (eapply locals_ok_store; [exact Hloc3 | exact Hm4]).
          exists m5. split; [| split; [| split; [| split; [| split; [| split; [| split]]]]]]; auto.
          * eapply runs_seq; [exact Hrun1 |].
            eapply runs_seq; [eapply set_next_run; eauto |].
            eapply link_run; eauto.
            -- exact (ti_tinfo _ _ _ _ _ _ _ Htm).
            -- eapply frames_word; eauto.
          * simpl. unfold cur_frames. simpl. rewrite Hk.
            apply (tinfo_wf_link cenv ge gc_inv Hgc h fs0 m4 m5 tb tofs (own (S k')) fp0); auto.
            -- rewrite <- Hfp3. eapply Mem.load_store_other; [exact Hm4 | now left].
            -- simpl. erewrite Mem.load_store_other; [| exact Hm4 |].
               2:{ right. left. change (size_chunk Mptr) with 8. ofs_lia. }
               erewrite Mem.load_store_other; [| exact Hm3 |].
               2:{ right. left. change (size_chunk Mptr) with 8. ofs_lia. }
               erewrite Mem.load_store_same; [| exact Hm2]. reflexivity.
            -- simpl. erewrite Mem.load_store_other; [| exact Hm4 |].
               2:{ right. left. change (size_chunk Mptr) with 8. ofs_lia. }
               erewrite Mem.load_store_same; [| exact Hm3]. reflexivity.
            -- simpl. erewrite Mem.load_store_same; [| exact Hm4]. f_equal.
               eapply frames_load_result; eauto.
            -- eapply own_frame_ok with (slots := slots); eauto. lia.
          * simpl. eapply slots_hold_store; [exact Hhold4 | exact Hm5 | auto | auto].
          * split; [apply Hstok; [auto | discriminate] |].
            split; [reflexivity |]. split; [reflexivity |]. split; [reflexivity | exact Hin_iff].
    Qed.

    (** ** Reading the roots back *)

    (* The variables that the code reads before its next call have been read back *)
    Definition uses_ok (st : state) (e : exp) : Prop :=
      forall x, PS.In x (uses_now prims e) -> ~ In x (st_stale st).

    Lemma uses_now_range st e x :
      exp_ok st e -> PS.In x (uses_now prims e) -> (100 <= x < tmp)%positive.
    Proof.
      intros Hexp Hx. destruct (uses_now_vars prims e x Hx) as [Hfx | Hbx].
      - apply (eo_free _ _ Hexp x Hfx).
      - apply (eo_bound _ _ Hexp x Hbx).
    Qed.

    Lemma reload_correct i st rho e le h m s st3 :
      inv i st rho e le h m ->
      exp_ok st e ->
      reload (Z.of_nat nroots) st (uses_now prims e) = (s, st3) ->
      exists le',
        runs ge fn lenv s le m le' m /\
        inv i st3 rho e le' h m /\
        uses_ok st3 e /\
        st_slots st3 = st_slots st /\ st_linked st3 = st_linked st.
    Proof.
      intros (Hm & Hs & Htm) Hexp Hre. unfold reload in Hre.
      apply pair_equal_spec in Hre. destruct Hre as [Hs_eq Hst_eq]. subst s st3.
      set (keep := fun x => in_list x (st_stale st) && PS.mem x (uses_now prims e)).
      assert (Hkeep : forall x, keep x = true -> In x (st_stale st) /\ PS.In x (uses_now prims e)).
      { intros x Hx. unfold keep in Hx. apply andb_true_iff in Hx. destruct Hx as [H1 H2].
        split; [apply in_list_In; auto | apply PS.mem_spec; auto]. }
      assert (Hread : exists le',
                 runs ge fn lenv (read_roots (Z.of_nat nroots) keep 0 (st_slots st)) le m le' m /\
                 (forall y, ~ (In y (st_slots st) /\ keep y = true) -> le' ! y = le ! y) /\
                 (forall j y, nth_error (st_slots st) j = Some y -> keep y = true ->
                              exists w, Mem.load Mptr m rb (8 * Z.of_nat j) = Some w /\
                                        le' ! y = Some w)).
      { destruct (Nat.eq_dec nroots 0) as [Hz | Hnz].
        - assert (Hnil : st_slots st = []).
          { pose proof (so_nslots _ Hs). destruct (st_slots st); [auto | simpl in *; lia]. }
          rewrite Hnil. exists le. split; [apply runs_skip |]. split; auto.
          intros j y Hj. destruct j; discriminate.
        - destruct (runs_read_roots ge fn lenv rb (Z.of_nat nroots) (lenv_roots Hnz) m keep
                                    (st_slots st) 0 le) as (le3 & Hr3 & Ho3 & Hs3).
          + intros j y Hj _. destruct (mi_slots _ _ _ _ _ Hm j y Hj) as (v & w & _ & Hw & _). eauto.
          + pose proof (so_nslots _ Hs). pose proof nroots_unsigned. lia.
          + exists le3. split; [exact Hr3 |]. split; [exact Ho3 |].
            intros j y Hj Hk. apply (Hs3 (so_nodup _ Hs) j y Hj Hk). }
      destruct Hread as (le' & Hrun & Hother & Hset).
      assert (Hres : forall x, (x < 100)%positive -> le' ! x = le ! x).
      { intros x Hx. apply Hother. intros [_ Hk]. destruct (Hkeep x Hk) as [_ Hu].
        pose proof (uses_now_range _ _ _ Hexp Hu). lia. }
      exists le'. split; [exact Hrun |]. split; [| split; [| split; reflexivity]].
      - split; [| split].
        + eapply mem_inv_state; eauto. simpl. exact (mi_sync _ _ _ _ _ Hm).
        + destruct Hs as [S1 S2 S3 S4 S5 S6]. constructor; simpl; auto.
          intros x Hx. apply filter_In in Hx. apply S2. tauto.
        + destruct Htm as [T1 T2 T3 T4]. constructor; simpl.
          * rewrite Hres; [exact T1 | reflexivity].
          * intros Hr. destruct (T2 Hr) as [Ha Hroom]. split; auto.
            rewrite Hres; [exact Ha | reflexivity].
          * intros x Hx Hfx. destruct (T3 x Hx Hfx) as (v & Hv & Hw).
            exists v. split; auto. intros Hns.
            destruct (in_dec Pos.eq_dec x (st_stale st)) as [Hst | Hnst].
            -- (* [x] is read back *)
               assert (Hu : PS.mem x (uses_now prims e) = true).
               { destruct (PS.mem x (uses_now prims e)) eqn:E; auto. exfalso. apply Hns.
                 apply filter_In. split; auto. rewrite E. reflexivity. }
               assert (Hk : keep x = true).
               { unfold keep. apply andb_true_iff. split; auto. apply in_list_In. auto. }
               destruct (In_nth_error _ _ (so_stale _ Hs _ Hst)) as [j Hj].
               destruct (Hset j x Hj Hk) as (w & Hlw & Hle').
               destruct (mi_slots _ _ _ _ _ Hm j x Hj) as (v' & w' & Hv' & Hw' & Hr').
               exists w. split; auto. assert (v' = v) by congruence. assert (w' = w) by congruence.
               subst. exact Hr'.
            -- destruct (Hw Hnst) as (w & Hlw & Hr). exists w. split; auto.
               rewrite Hother; auto. intros [_ Hk]. destruct (Hkeep x Hk). contradiction.
          * exact T4.
      - intros x Hx Hin. simpl in Hin. apply filter_In in Hin. destruct Hin as [_ Hn].
        apply PS.mem_spec in Hx. rewrite Hx in Hn. discriminate.
    Qed.

    (** ** Returning *)

    Lemma free_own h m b lo hi m' :
      tinfo_ok h fs0 m tb tofs ->
      Mem.free m b lo hi = Some m' ->
      nroots <> 0%nat -> b = fb \/ b = rb -> ~ heap_blocks h b ->
      tinfo_ok h fs0 m' tb tofs /\ data_kept h m h m' /\ step_ok h m h m'.
    Proof.
      intros [Hwf Hal] Hfree Hn Hb Hnh.
      destruct (Hown Hn) as (Hfr & Hft & Hrt & Hnf & Hnr).
      assert (Hbt : b <> tb) by (destruct Hb; subst; auto).
      assert (Hbf : not_in_frames b fs0) by (destruct Hb; subst; auto).
      assert (Hk : data_kept h m h m').
      { split; auto. eapply Mem.free_unchanged_on; eauto. intros j _ [Hh _]. contradiction. }
      split; [| split; [exact Hk |]].
      - split.
        + eapply tinfo_wf_free; eauto.
        + rewrite <- Hal. eapply Mem.load_free; [exact Hfree | left; congruence].
      - split.
        + intros b' o' [[_ (j & Hj & _)] | (fr & j & Hin & Hj & -> & ->)]; [lia |].
          apply still_represented_kept; auto. intros w Hw. rewrite <- Hw.
          eapply Mem.load_free; [exact Hfree |]. left. intros Heq. destruct (Hbf fr Hin). congruence.
        + split; [| split].
          * eapply Mem.free_unchanged_on; eauto. intros j _ (_ & _ & _ & Hno).
            apply Hno. split; auto.
          * intros b' o' k p _ Hno Hp. eapply Mem.perm_free_1; [exact Hfree | | exact Hp]. left.
            intros ->. apply Hno. split; auto.
          * intros b' Hb'. now left.
    Qed.

    (* The frame and the roots of the function are freed when it returns *)
    Lemma free_locals h m :
      locals_ok h m -> tinfo_ok h fs0 m tb tofs ->
      exists m',
        Mem.free_list m (blocks_of_env ge lenv) = Some m' /\
        tinfo_ok h fs0 m' tb tofs /\ data_kept h m h m' /\ step_ok h m h m'.
    Proof.
      intros Hloc Hti. unfold lenv, local_env. destruct (Nat.eqb nroots 0) eqn:E.
      - exists m. split; [reflexivity |]. split; [exact Hti |].
        split; [apply data_kept_refl | apply step_ok_refl].
      - apply Nat.eqb_neq in E. destruct (lo_heap _ _ Hloc E) as [Hfh Hrh].
        destruct (Hown E) as (Hfr & _).
        change (blocks_of_env ge (PTree.set rootsId (rb, tarray tvalue (Z.of_nat nroots))
                                            (PTree.set frameId (fb, frameT) empty_env)))
          with [(fb, 0, sizeof ge frameT); (rb, 0, sizeof ge (tarray tvalue (Z.of_nat nroots)))].
        rewrite (sizeof_frame _ Hstructs), sizeof_roots.
        replace (Z.max 0 (Z.of_nat nroots)) with (Z.of_nat nroots) by lia.
        destruct (Mem.range_perm_free m fb 0 24 (lo_frame _ _ Hloc E)) as [m1 Hm1].
        assert (Hfb : fb = fb \/ fb = rb) by (left; reflexivity).
        assert (Hrb : rb = fb \/ rb = rb) by (right; reflexivity).
        destruct (free_own h m fb 0 24 m1 Hti Hm1 E Hfb Hfh) as (Hti1 & Hk1 & Hs1).
        destruct (Mem.range_perm_free m1 rb 0 (8 * Z.of_nat nroots)) as [m2 Hm2].
        { intros o Ho. eapply Mem.perm_free_1; [exact Hm1 | left; congruence |].
          apply (lo_roots _ _ Hloc E). exact Ho. }
        destruct (free_own h m1 rb 0 _ m2 Hti1 Hm2 E Hrb Hrh) as (Hti2 & Hk2 & Hs2).
        exists m2. split; [| split; [exact Hti2 | split]].
        + cbn [Mem.free_list]. rewrite Hm1. cbn [Mem.free_list]. rewrite Hm2. reflexivity.
        + eapply data_kept_trans; eauto.
        + eapply step_ok_trans; eauto.
    Qed.

    (** ** The call statement *)

    (* The call statement, for a function value that is related for [i] steps and whose
       body evaluates with less fuel *)
    Lemma call_correct i le h m fs r f ys c rho' fl f' wf vs ws xs t e_body rho''
          (cin : fuel) v (cout : trace) :
      (to_nat cin < i)%nat ->
      call nparam fenv r f ys = Ret c ->
      tinfo_ok h fs m tb tofs ->
      le ! tinfoId = Some (Vptr tb (Ptrofs.repr tofs)) ->
      var_val ge le fenv f wf -> val_rel i h m (Vfun rho' fl f') wf ->
      Forall2 (var_val ge le fenv) ys ws -> Forall2 (val_rel i h m) vs ws ->
      find_def f' fl = Some (t, xs, e_body) ->
      set_lists xs vs (def_funs fl fl rho' rho') = Some rho'' ->
      bstep_fuel cenv rho'' e_body cin (Res v) cout ->
      exists w h' m',
        runs ge fn lenv c le m (PTree.set r w le) m' /\
        val_rel (i - 1 - to_nat cin) h' m' v w /\
        tinfo_ok h' fs m' tb tofs /\
        (forall b o, root_at tb tofs 0 fs b o -> still_represented h m h' m' b o) /\
        changes (fun _ _ => False) tb tofs fs h m h' m'.
    Proof.
      intros Hi Hc Hti Hle Hvf Hrf Hys Hrs Hfind Hset Hbstep.
      pose proof Hti as [Hwf Hal].
      pose proof (wf_range _ _ _ _ _ _ _ _ Hwf) as (Ht0 & Htmax & Htal).
      pose proof (Forall2_length _ _ _ Hys) as Hlen_ys.
      pose proof (Forall2_length _ _ _ Hrs) as Hlen_vs.
      pose proof (set_lists_length_eq _ _ _ _ Hset) as Hlen_xs.
      assert (Hwords : Forall is_word ws).
      { apply Forall_forall. intros w Hw. destruct (In_nth_error _ _ Hw) as [j Hj].
        destruct (Forall2_nth_r _ _ _ Hrs _ _ Hj) as (v0 & _ & Hr). eapply val_rel_word; eauto. }
      unfold call in Hc.
      destruct (max_args <? Z.of_nat (length ys)) eqn:Hmax; [discriminate |].
      apply Z.ltb_ge in Hmax.
      bind_inv Hc. apply Ret_inj in Hc. subst c. rename x into callee. rename E into Hcallee.
      (* the function *)
      inversion Hrf as [| | ? ? ? b fd Hfp Hfr]; subst.
      destruct i as [| i']; [lia |].
      destruct (proj1 (fun_rel_S cenv ge nparam gc_inv i' rho' fl f' fd) Hfr)
        as (t0 & xs0 & e0 & Hfind0 & Hty & Hcall).
      assert (Hxs0 : xs0 = xs) by congruence. assert (He0 : e0 = e_body) by congruence.
      subst xs0 e0. clear Hfind0.
      assert (Hcallee_ok :
                classify_fun (typeof callee)
                = fun_case_f (tptr tinfoT :: repeat tvalue (Nat.min (length ys) nparam))
                             tvalue cc_default /\
                forall m0, eval_expr ge lenv le m0 callee (Vptr b Ptrofs.zero)).
      { unfold var_val in Hvf. destruct (M.get f fenv) as [k |] eqn:Hfk.
        - destruct (Nat.eqb k (length ys)); [| discriminate]. apply Ret_inj in Hcallee.
          subst callee. destruct Hvf as (b' & Hb' & Heq). assert (b' = b) by congruence. subst b'.
          split; [reflexivity |]. intros m0. eapply eval_Elvalue.
          + apply eval_Evar_global; [apply lenv_fun; congruence | exact Hb'].
          + apply deref_loc_reference. reflexivity.
        - apply Ret_inj in Hcallee. subst callee. split; [reflexivity |]. intros m0.
          eapply eval_Ecast; [apply eval_Etempvar; exact Hvf |].
          apply sem_cast_word; [reflexivity | exact I]. }
      destruct Hcallee_ok as [Hclass Hcallee_eval].
      (* the arguments in [tinfo->args] *)
      assert (Hargs : exists m1,
                 store_words m tb (tofs + args_ofs + 8 * Z.of_nat nparam) (skipn nparam ws)
                 = Some m1 /\
                 runs ge fn lenv (store_args nparam fenv nparam (skipn nparam ys)) le m le m1).
      { destruct (le_lt_dec (length ys) nparam) as [Hshort | Hlong].
        - rewrite (skipn_all2 ys) by lia. rewrite (skipn_all2 ws) by lia.
          exists m. split; [reflexivity | apply runs_skip].
        - destruct (store_words_exists (skipn nparam ws) m tb
                                       (tofs + args_ofs + 8 * Z.of_nat nparam)) as [m1 Hm1].
          + intros o Ho. apply (wf_perm _ _ _ _ _ _ _ _ Hwf). rewrite length_skipn in Ho.
            clear - Ho Hmax Hlen_ys Hlong. ofs_lia.
          + apply Z.divide_add_r; [apply Z.divide_add_r; auto |];
              [exists 3; reflexivity | apply Z.divide_factor_l].
          + exists m1. split; [exact Hm1 |].
            eapply (runs_store_args ge Hstructs nparam fenv fn lenv tb tofs (conj Ht0 Htmax))
              with (ws := skipn nparam ws).
            * exact Hle.
            * apply Forall2_skipn. exact Hys.
            * apply Forall_skipn. exact Hwords.
            * intros y _ Hfy. apply lenv_fun. exact Hfy.
            * rewrite length_skipn. lia.
            * exact Hm1. }
      destruct Hargs as (m1 & Hm1 & Hrun1).
      destruct (tinfo_args_change cenv ge gc_inv Hgc h fs m m1 tb tofs Hti) as (Hti1 & Hk1 & Hroots1 & Hch1).
      { eapply Mem.unchanged_on_implies; [apply (store_words_unchanged _ _ _ _ _ Hm1) |].
        intros b0 o Hnr _ [Hb Ho]. apply Hnr. split; auto. rewrite length_skipn in Ho.
        clear - Ho Hmax Hlen_ys. ofs_lia. }
      { intros b0. eapply store_words_perm; eauto. }
      destruct (Hcall i' vs rho'' cin v cout ws tb tofs h fs m1)
        as (w & h' & m' & Hstar & Hres & Hti' & Hroots' & Hch'); auto.
      { lia. }
      { clear - Hrs Hk1. induction Hrs; constructor; auto.
        eapply val_rel_mono with (k := S i'); [lia |]. eapply repr_val_kept; eauto. }
      { intros j w Hj Hw.
        replace (tofs + args_ofs + 8 * Z.of_nat j)
          with (tofs + args_ofs + 8 * Z.of_nat nparam + 8 * Z.of_nat (j - nparam)) by lia.
        eapply store_words_load; [exact Hm1 | |].
        - rewrite nth_error_skipn. rewrite <- Hw. f_equal. lia.
        - rewrite Forall_forall in Hwords. specialize (Hwords w (nth_error_In _ _ Hw)).
          destruct w; try contradiction; reflexivity. }
      exists w, h', m'. split; [| split; [| split; [exact Hti' | split]]].
      - eapply runs_seq; [exact Hrun1 |].
        change (PTree.set r w le) with (set_opttemp (Some r) w le).
        eapply runs_call.
        + exact Hclass.
        + apply Hcallee_eval.
        + econstructor.
          * apply eval_Etempvar. exact Hle.
          * reflexivity.
          * replace (Nat.min (length ys) nparam) with (length (firstn nparam ys))
              by (rewrite length_firstn; apply Nat.min_comm).
            apply eval_var_exprs.
            -- apply Forall2_firstn. exact Hys.
            -- apply Forall_firstn. exact Hwords.
            -- intros y _ Hfy. apply lenv_fun. exact Hfy.
        + rewrite Genv.find_funct_find_funct_ptr. exact Hfp.
        + rewrite Hty. unfold fun_ty. do 3 f_equal. f_equal.
          transitivity (length ws); [| symmetry; exact Hlen_ys].
          transitivity (length vs); [exact Hlen_xs | exact Hlen_vs].
        + exact Hstar.
      - replace (S i' - 1 - to_nat cin)%nat with (i' - to_nat cin)%nat by lia. exact Hres.
      - intros b0 o Hr. eapply still_represented_trans; [apply Hroots1 | apply Hroots']; exact Hr.
      - eapply changes_trans; eauto.
    Qed.

    (** ** The start of the code *)

    Lemma st_ok_init : st_ok init_state.
    Proof.
      constructor; simpl; auto; try discriminate.
      - apply incl_refl.
      - constructor.
      - lia.
    Qed.

    Lemma mem_inv_init i rho h m :
      tinfo_ok h fs0 m tb tofs -> locals_ok h m -> mem_inv i init_state rho h m.
    Proof.
      intros [Hwf Hal] Hloc. constructor; auto.
      intros j x Hj. destruct j; discriminate.
    Qed.

    (* The invariant when the parameters hold the arguments *)
    Lemma start_inv i vs ws rho le h m :
      set_lists params vs (def_funs fds fds rho0 rho0) = Some rho ->
      Forall2 (val_rel i h m) vs ws ->
      (forall j p w, nth_error params j = Some p -> nth_error ws j = Some w -> le ! p = Some w) ->
      le ! tinfoId = Some (Vptr tb (Ptrofs.repr tofs)) ->
      tinfo_ok h fs0 m tb tofs -> locals_ok h m ->
      inv i init_state rho body le h m.
    Proof.
      intros Hset Hrs Hle Hti Htok Hloc. split; [| split].
      - apply mem_inv_init; auto.
      - exact st_ok_init.
      - constructor.
        + exact Hti.
        + intros Hr. discriminate.
        + intros x Hx Hfx. destruct (bo_free _ _ Hbody x Hx) as [Hin | Hfn]; [| contradiction].
          destruct (In_nth_error _ _ Hin) as [j Hj].
          pose proof (set_lists_length_eq _ _ _ _ Hset) as Hlen.
          destruct (nth_error vs j) as [v0 |] eqn:Hv0.
          2:{ apply nth_error_None in Hv0.
              assert (Hlt : (j < length vs)%nat).
              { rewrite <- Hlen. apply nth_error_Some. intros Hnone.
                pose proof (eq_trans (eq_sym Hj) Hnone). discriminate. }
              lia. }
          destruct (Forall2_nth_l _ _ _ Hrs _ _ Hv0) as (w0 & Hw0 & Hr0).
          exists v0. split.
          * eapply set_lists_nth; eauto. exact (bo_params _ _ Hbody).
          * intros _. exists w0. split; [eapply Hle; eauto | exact Hr0].
        + intros f Hfn. rewrite <- (set_lists_not_In _ _ _ _ _ Hset).
          * apply def_funs_eq. apply fun_arities_name. exact Hfn.
          * intros Hin. apply Hfn. apply (bo_params_funs _ _ Hbody). exact Hin.
    Qed.

    Lemma start_exp_ok : exp_ok init_state body.
    Proof.
      constructor.
      - exact (bo_unique _ _ Hbody).
      - intros x Hx. destruct (bo_bound _ _ Hbody x Hx) as [Hnp Hnf].
        split; [apply (bo_ids _ _ Hbody); now left |]. split; [exact Hnf |].
        split; [intros [] |].
        intros Hfx. destruct (bo_free _ _ Hbody x Hfx) as [Hin | Hfn]; [contradiction | congruence].
      - intros x Hx. destruct (bo_free _ _ Hbody x Hx) as [Hin | Hfn].
        + apply (bo_ids _ _ Hbody). now right.
        + apply Hfnames. exact Hfn.
      - exact (bo_sub _ _ Hbody).
      - exact Hroots_body.
      - intros g ps Hg Hc. destruct (Hself g ps Hg) as (_ & _ & _ & Hl). congruence.
    Qed.

    (** ** Expressions *)

    (* The parts of an expression are expressions that the proof covers *)
    Lemma exp_ok_constr st x t ys e : exp_ok st (Econstr x t ys e) -> exp_ok st e.
    Proof.
      intros Hexp. pose proof (eo_unique _ _ Hexp) as Hub. inv Hub.
      apply (exp_ok_bind st (Econstr x t ys e) x e Hexp).
      - constructor.
      - assumption.
      - constructor.
      - assumption.
      - intros z Hz. now constructor.
      - intros z Hz. destruct (Pos.eq_dec z x) as [-> | Hne]; [now left | right].
        apply Free_Econstr2; [congruence | exact Hz].
      - apply Nat.le_refl.
      - intros g n Hg. exact Hg.
    Qed.

    Lemma exp_ok_proj st x t n y e : exp_ok st (Eproj x t n y e) -> exp_ok st e.
    Proof.
      intros Hexp. pose proof (eo_unique _ _ Hexp) as Hub. inv Hub.
      apply (exp_ok_bind st (Eproj x t n y e) x e Hexp).
      - constructor.
      - assumption.
      - constructor.
      - assumption.
      - intros z Hz. now constructor.
      - intros z Hz. destruct (Pos.eq_dec z x) as [-> | Hne]; [now left | right].
        apply Free_Eproj2; [congruence | exact Hz].
      - apply Nat.le_refl.
      - intros g k Hg. exact Hg.
    Qed.

    Lemma exp_ok_letapp st x f t ys e : exp_ok st (Eletapp x f t ys e) -> exp_ok st e.
    Proof.
      intros Hexp. pose proof (eo_unique _ _ Hexp) as Hub. inv Hub.
      apply (exp_ok_bind st (Eletapp x f t ys e) x e Hexp).
      - constructor.
      - assumption.
      - constructor.
      - assumption.
      - intros z Hz. now constructor.
      - intros z Hz. destruct (Pos.eq_dec z x) as [-> | Hne]; [now left | right].
        apply Free_Eletapp2; [congruence | exact Hz].
      - cbn [max_roots]. destruct (returns x e) eqn:R; [| lia].
        destruct e; try discriminate. simpl. lia.
      - intros g k Hg. cbn [calls_itself]. destruct (returns x e) eqn:R; [| exact Hg].
        destruct e; discriminate.
    Qed.

    Lemma exp_ok_case st y cl t e : exp_ok st (Ecase y cl) -> In (t, e) cl -> exp_ok st e.
    Proof.
      intros Hexp Hin. destruct (in_split _ _ Hin) as (cl1 & cl2 & ->).
      destruct (unique_bindings_Ecase_l _ _ _ _ _ (eo_unique _ _ Hexp)) as (Hue & _).
      apply (exp_ok_sub st (Ecase y (cl1 ++ (t, e) :: cl2)) e Hexp).
      - econstructor. exact Hin.
      - exact Hue.
      - intros z Hz. eapply Bound_Ecase; eauto.
      - intros z Hz. eapply occurs_free_Ecase_Included; eauto.
      - eapply max_roots_case; eauto.
      - intros g k Hg. eapply calls_itself_case; eauto.
    Qed.

    (* The heap after an allocation *)
    Lemma step_ok_alloc h m n : 0 <= n -> step_ok h m (alloc_block h n) m.
    Proof.
      intros Hn. split.
      - intros b o _. apply still_represented_kept; [| auto].
        split; [apply Mem.unchanged_on_refl | apply heap_le_alloc_block; exact Hn].
      - split; [apply Mem.unchanged_on_refl |]. split; [auto |]. intros b Hb. now left.
    Qed.

    (* The code of [e], run when [rho] holds the values of its variables, returns the
       layout of [v]. [c] is the fuel that [e] takes, without [d]. *)
    Definition exp_correct (rho : eval.env) (e : exp) (c : fuel) (v : val) (d : nat) : Prop :=
      forall i st s le h m,
        (to_nat c + d <= i)%nat -> (i < K)%nat ->
        trans nparam prims cenv fenv self (Z.of_nat nroots) tmps st e = Ret s ->
        inv i st rho e le h m -> uses_ok st e -> exp_ok st e ->
        exists w h' m',
          (forall k0 k, is_call_cont k0 -> cont_ok k0 k ->
                        star step2 ge (Clight.State fn s k lenv le m) E0 (Returnstate w k0 m')) /\
          val_rel (i - to_nat c - d) h' m' v w /\
          tinfo_ok h' fs0 m' tb tofs /\
          step_ok h m h' m'.

    (* The code of the function, run from its start *)
    Lemma code_correct rho (c : fuel) v i vs ws le h m :
      exp_correct rho body c v 0 ->
      (to_nat c <= i)%nat -> (i < K)%nat ->
      set_lists params vs (def_funs fds fds rho0 rho0) = Some rho ->
      Forall2 (val_rel i h m) vs ws ->
      (forall j p w, nth_error params j = Some p -> nth_error ws j = Some w -> le ! p = Some w) ->
      le ! tinfoId = Some (Vptr tb (Ptrofs.repr tofs)) ->
      tinfo_ok h fs0 m tb tofs -> locals_ok h m ->
      exists w h' m',
        (forall k0 k, is_call_cont k0 -> cont_ok k0 k ->
                      star step2 ge (Clight.State fn code k lenv le m) E0 (Returnstate w k0 m')) /\
        val_rel (i - to_nat c) h' m' v w /\
        tinfo_ok h' fs0 m' tb tofs /\
        step_ok h m h' m'.
    Proof.
      intros IH Hc Hi Hset Hrs Hle Hti Htok Hloc.
      pose proof (start_inv i vs ws rho le h m Hset Hrs Hle Hti Htok Hloc) as Hinv0.
      destruct (enter_correct i init_state rho body le h m s_check st1 Hi Hinv0 start_exp_ok Henter)
        as (le1 & h1 & m1 & Hrun & Hinv1 & Hstep1 & Hstale & Hslots & Hlinked).
      destruct (IH i st1 s_body le1 h1 m1) as (w & h' & m' & Hstar & Hres & Hti' & Hstep'); auto.
      { lia. }
      { intros x _ Hin. rewrite Hstale in Hin. exact Hin. }
      { eapply exp_ok_slots; [apply start_exp_ok |]. intros x Hin. rewrite Hslots in Hin. now left. }
      exists w, h', m'. split; [| split; [| split; [exact Hti' |]]].
      - intros k0 k Hk0 Hcont. unfold code.
        eapply star_trans; [apply seq_star; exact Hrun | apply Hstar; auto | reflexivity].
      - replace (i - to_nat c)%nat with (i - to_nat c - 0)%nat by lia. exact Hres.
      - eapply step_ok_trans; eauto.
    Qed.

    Lemma halt_correct rho x v (c : fuel) :
      M.get x rho = Some v -> exp_correct rho (Ehalt x) c v 1.
    Proof.
      intros Hx i st s le h m Hc Hi Htr Hinv Huse Hexp.
      cbn [trans] in Htr. apply Ret_inj in Htr. subst s.
      pose proof Hinv as (Hm & Hs & Htm).
      destruct (leave_correct i st rho (Ehalt x) le h m Hinv) as (m1 & Hrun & Hti & Hk & Hstep & Hloc).
      destruct (free_locals h m1 Hloc Hti) as (m2 & Hfree & Hti2 & Hk2 & Hstep2).
      destruct (var_word i st rho (Ehalt x) le h m x Hi Htm) as (v' & w & Hv' & Hvw & Hr).
      { constructor. }
      { apply Huse. simpl. apply PS.singleton_spec. reflexivity. }
      assert (v' = v) by congruence. subst v'.
      exists w, h, m2. split; [| split; [| split; [exact Hti2 |]]].
      - intros k0 k Hk0 Hcont.
        eapply star_trans; [apply seq_star; exact Hrun | | reflexivity].
        rewrite <- (cont_ok_call_cont k0 k Hk0 Hcont).
        eapply star_return; [| | exact Hfree].
        + apply eval_var_expr; [exact Hvw | eapply val_rel_word; eauto |].
          intros Hfx. apply lenv_fun. exact Hfx.
        + rewrite typeof_var_expr, Hreturn.
          apply sem_cast_word; [reflexivity | eapply val_rel_word; eauto].
      - eapply val_rel_mono with (k := i); [lia |].
        eapply val_rel_kept; [exact Hk2 |]. eapply val_rel_kept; [exact Hk | exact Hr].
      - eapply step_ok_trans; eauto.
    Qed.

    Lemma uses_ok_state st st' e :
      uses_ok st e -> st_stale st' = st_stale st -> uses_ok st' e.
    Proof. intros H Heq x Hx. rewrite Heq. apply H. exact Hx. Qed.

    Lemma constr_correct rho (x : var) t (ys : list var) e vs (c : fuel) v :
      get_list ys rho = Some vs ->
      exp_correct (M.set x (Vconstr t vs) rho) e c v 0 ->
      exp_correct rho (Econstr x t ys e) c v 1.
    Proof.
      intros Hvs IH i st s le h m Hc Hi Htr Hinv Huse Hexp.
      pose proof Hinv as (Hm & Hs & Htm).
      pose proof (exp_ok_constr _ _ _ _ _ Hexp) as Hexp'.
      destruct (eo_bound _ _ Hexp x) as (Hxr & Hxf & Hxs & Hxfree); [constructor |].
      destruct (pipeline_ident x) as (Hx1 & Hx2 & _); [lia |].
      assert (Huse' : uses_ok st e).
      { intros z Hz. apply Huse. simpl. apply union_list_spec. now left. }
      cbn [trans] in Htr. bind_inv_as Htr r Hrep.
      destruct r as [ord | ord n].
      - (* a constant *)
        destruct ys as [| y ys]; [| discriminate].
        bind_inv_as Htr s' Htr'. apply Ret_inj in Htr. subst s.
        simpl in Hvs. injection Hvs as <-.
        assert (Hr : val_rel i h m (Vconstr t []) (Vlong (Int64.repr (constant_value ord)))).
        { constructor. exact Hrep. }
        destruct (IH i st s' (PTree.set x (Vlong (Int64.repr (constant_value ord))) le) h m)
          as (w' & h' & m' & Hstar & Hres & Hti & Hstep); auto.
        + lia.
        + split; [| split; [exact Hs |]].
          * apply mem_inv_set; auto.
          * apply (tmp_inv_set i st rho (Econstr x t [] e) e le h m x _ _ Htm Hr Hx1 Hx2 Hxf).
            -- intros z Hz. destruct (Pos.eq_dec z x) as [-> | Hne]; [now left | right].
               apply Free_Econstr2; [congruence | exact Hz].
            -- simpl. lia.
        + exists w', h', m'. split; [| split; [| split]]; auto.
          * intros k0 k Hk0 Hcont.
            eapply star_trans; [apply seq_star; apply runs_set; apply eval_const | | reflexivity].
            apply Hstar; auto.
          * eapply val_rel_mono; [| exact Hres]. lia.
      - (* a block *)
        destruct (negb (Nat.eqb (length ys) n)) eqn:Hn; [discriminate |].
        apply negb_false_iff, Nat.eqb_eq in Hn.
        destruct (st_room st) eqn:Hroom; [| discriminate].
        bind_inv_as Htr s' Htr'. apply Ret_inj in Htr. subst s.
        pose proof (get_list_length_eq _ _ _ Hvs) as Hlen.
        assert (Hnv : n = length vs) by (rewrite <- Hn; exact Hlen). clear Hn. subst n.
        destruct (ctor_rep_of_inv _ _ _ Hrep) as (info & Hinfo & [[_ Hkind] | (Har & Hord_le & Hkind)]);
          [discriminate |].
        assert (Hord_eq : ord = Z.of_N (ctor_ordinal info)) by congruence.
        assert (Hnz : length vs <> 0%nat).
        { assert (Hl : length vs = N.to_nat (ctor_arity info)) by congruence. lia. }
        assert (Hneed : alloc_need prims (Econstr x t ys e)
                        = (S (length vs) + alloc_need prims e)%nat).
        { destruct ys as [| y0 ys'].
          - exfalso. apply Hnz. symmetry. exact Hlen.
          - cbn [alloc_need]. f_equal. f_equal. exact Hlen. }
        destruct (ti_room _ _ _ _ _ _ _ Htm Hroom) as [Hal Hspace]. rewrite Hneed in Hspace.
        pose proof (mi_wf _ _ _ _ _ Hm) as Hwf.
        pose proof (wf_free _ _ _ _ _ _ _ _ Hwf) as [Hfh [Hfr1 Hfr2] Hfs Hfa Hfp].
        (* the words of the fields *)
        destruct (vars_words i st rho (Econstr x t ys e) le h m ys Hi Htm) as (vs' & ws & Hvs' & Hws & Hrs).
        { intros z Hz. split; [now constructor |]. apply Huse. simpl. apply union_list_spec. now right. }
        assert (vs' = vs) by congruence. subst vs'.
        pose proof (Forall2_length _ _ _ Hrs) as Hlen_ws.
        assert (Hwords : Forall is_word ws).
        { apply Forall_forall. intros w Hw. destruct (In_nth_error _ _ Hw) as [j Hj].
          destruct (Forall2_nth_r _ _ _ Hrs _ _ Hj) as (v0 & _ & Hr). eapply val_rel_word; eauto. }
        (* the stores *)
        remember (block_header ord (Z.of_nat (length vs))) as hdr eqn:Hhdr.
        destruct (Mem.valid_access_store m Mptr (free_block h) (free_start h)
                                         (Vlong (Int64.repr hdr))) as [m0 Hm0].
        { split; [| exact Hfa]. intros o Ho. change (size_chunk Mptr) with 8 in Ho. apply Hfp. lia. }
        destruct (store_words_exists ws m0 (free_block h) (free_start h + 8)) as [m' Hm'].
        { intros o Ho. eapply Mem.perm_store_1; [exact Hm0 |]. apply Hfp. lia. }
        { apply Z.divide_add_r; [exact Hfa | exists 1; reflexivity]. }
        subst hdr.
        assert (Hord_r : 0 <= ord <= max_block_ordinal) by (rewrite Hord_eq; lia).
        assert (Hvs_nil : vs <> []) by (intros ->; apply Hnz; reflexivity).
        destruct (new_block_repr cenv ge gc_inv Hgc (fun_rel i) h (cur_frames st) m m0 m' tb tofs
                                 t vs ws ord Hwf Hrep Hord_r Hvs_nil Hrs)
          as (Hnew & Hk & Hwf'); auto.
        { lia. }
        set (h' := alloc_block h (Z.of_nat (length vs))) in *.
        set (wx := Vptr (free_block h) (Ptrofs.repr (free_start h + 8))) in *.
        set (le1 := PTree.set allocId
                      (Vptr (free_block h)
                            (Ptrofs.repr (free_start h + 8 * (Z.of_nat (length vs) + 1))))
                      (PTree.set x wx le)).
        assert (Hun : Mem.unchanged_on
                        (fun b o => ~ (b = free_block h /\ free_start h <= o)) m m').
        { eapply Mem.unchanged_on_trans.
          - eapply Mem.store_unchanged_on; [exact Hm0 |]. intros j Hj Hnot. apply Hnot.
            split; [reflexivity | lia].
          - eapply Mem.unchanged_on_implies; [apply (store_words_unchanged _ _ _ _ _ Hm') |].
            intros b o Hnot _ [Hb Ho]. apply Hnot. split; [exact Hb | lia]. }
        assert (Hkp : forall b, keeps_perm m m' b).
        { intros b o k p Hp. eapply store_words_perm; [exact Hm' |].
          eapply Mem.perm_store_1; [exact Hm0 | exact Hp]. }
        assert (Hofs : Ptrofs.unsigned (Ptrofs.repr (free_start h + 8)) = free_start h + 8).
        { apply Ptrofs.unsigned_repr. lia. }
        assert (Hrun1 : runs ge fn lenv
                          (new_block x (block_header ord (Z.of_nat (length vs)))
                                     (Z.of_nat (length vs))) le m le1 m0).
        { apply runs_new_block; auto; lia. }
        assert (Hrun2 : runs ge fn lenv (store_fields x 0 (map (var_expr nparam fenv) ys))
                             le1 m0 le1 m').
        { eapply runs_store_fields with (ws := ws) (b := free_block h)
                                        (ofs := Ptrofs.repr (free_start h + 8)).
          - unfold le1. rewrite PTree.gso by auto. apply PTree.gss.
          - unfold le1. apply vars_val_set.
            + intros Hin. assert (Hfa' : occurs_free (Econstr x t ys e) allocId) by now constructor.
              apply (eo_free _ _ Hexp) in Hfa'. unfold allocId in Hfa'. lia.
            + apply vars_val_set; [| exact Hws].
              intros Hin. apply Hxfree. now constructor.
          - exact Hwords.
          - intros z _ Hfz. apply lenv_fun. exact Hfz.
          - rewrite Hofs.
            replace (Z.of_nat (length ys)) with (Z.of_nat (length vs)) by (f_equal; symmetry; exact Hlen).
            lia.
          - rewrite Hofs. replace (free_start h + 8 + 8 * Z.of_nat 0) with (free_start h + 8) by lia.
            exact Hm'. }
        (* the invariant after the allocation *)
        assert (Hrb : forall j, (j < length (st_slots st))%nat -> rb <> free_block h).
        { intros j Hj Heq. assert (Hnr : nroots <> 0%nat) by (pose proof (so_nslots _ Hs); lia).
          destruct (lo_heap _ _ (mi_locals _ _ _ _ _ Hm) Hnr) as [_ Hrh]. rewrite Heq in Hrh.
          contradiction. }
        assert (Hloc' : locals_ok h' m').
        { destruct (mi_locals _ _ _ _ _ Hm) as [L1 L2 L3]. constructor.
          - intros Hnr o Ho. apply Hkp. apply (L1 Hnr). exact Ho.
          - intros Hnr o Ho. apply Hkp. apply (L2 Hnr). exact Ho.
          - exact L3. }
        assert (Hm1 : mem_inv i (LambdaANF_to_C.allocated st) (M.set x (Vconstr t vs) rho) h' m').
        { apply mem_inv_set; [| exact Hxs].
          apply (mem_inv_kept i (LambdaANF_to_C.allocated st) rho h m h' m').
          - eapply mem_inv_state; [exact Hm | reflexivity | reflexivity |].
            intros Hd. simpl in Hd. discriminate.
          - exact Hk.
          - exact Hwf'.
          - intros Hd. simpl in Hd. discriminate.
          - intros j w0 Hj Hw0. eapply Mem.load_unchanged_on; [exact Hun | | exact Hw0].
            intros o _ [Heq _]. exact (Hrb j Hj Heq).
          - exact Hloc'. }
        assert (Htm1 : tmp_inv i (LambdaANF_to_C.allocated st) (M.set x (Vconstr t vs) rho) e le1 h' m').
        { destruct Htm as [T1 T2 T3 T4]. constructor.
          - unfold le1. rewrite PTree.gso by discriminate. rewrite PTree.gso by congruence.
            exact T1.
          - intros _. split; [unfold le1; apply PTree.gss |].
            unfold h', alloc_block. simpl. lia.
          - intros z Hz Hfz. destruct (Pos.eq_dec z x) as [-> | Hne].
            + exists (Vconstr t vs). split; [apply M.gss |]. intros _. exists wx. split; [| exact Hnew].
              unfold le1. rewrite PTree.gso by auto. apply PTree.gss.
            + assert (Hz' : occurs_free (Econstr x t ys e) z).
              { apply Free_Econstr2; [congruence | exact Hz]. }
              destruct (T3 z Hz' Hfz) as (v0 & Hv0 & Hw0). exists v0.
              split; [rewrite M.gso; auto |].
              intros Hns. destruct (Hw0 Hns) as (w0 & Hlw & Hr0). exists w0. split.
              * unfold le1. rewrite PTree.gso; [rewrite PTree.gso; [exact Hlw | exact Hne] |].
                apply (eo_free _ _ Hexp) in Hz'. unfold allocId. lia.
              * eapply val_rel_kept; eauto.
          - intros f0 Hf0. rewrite M.gso; [apply T4; exact Hf0 |]. intros ->. contradiction. }
        assert (Hs1 : st_ok (LambdaANF_to_C.allocated st)).
        { destruct Hs as [S1 S2 S3 S4 S5 S6]. constructor; auto. }
        destruct (IH i (LambdaANF_to_C.allocated st) s' le1 h' m') as (w' & h'' & m'' & Hstar & Hres & Hti & Hstep); auto.
        + lia.
        + split; [exact Hm1 | split; [exact Hs1 | exact Htm1]].
        + eapply exp_ok_slots; [exact Hexp' |]. intros z Hz. now left.
        + exists w', h'', m''. split; [| split; [| split]]; auto.
          * intros k0 k Hk0 Hcont.
            eapply star_trans; [apply seq_star; exact Hrun1 | | reflexivity].
            eapply star_trans; [apply seq_star; exact Hrun2 | | reflexivity].
            apply Hstar; auto.
          * eapply val_rel_mono; [| exact Hres]. lia.
          * eapply step_ok_trans; [| exact Hstep].
            eapply step_ok_trans; [| apply step_ok_alloc; lia].
            eapply (step_ok_region i st rho h m m'
                      (fun b o => b = free_block h /\ free_start h <= o) Hm Hun Hkp).
            intros b o [-> Ho]. left. split; [exact Hfh |]. intros [_ Hlt].
            specialize (Hlt eq_refl). lia.
    Qed.

    Lemma proj_correct rho (x : var) t n (y : var) e vs v0 (c : fuel) v :
      M.get y rho = Some (Vconstr t vs) -> nthN vs n = Some v0 ->
      exp_correct (M.set x v0 rho) e c v 0 ->
      exp_correct rho (Eproj x t n y e) c v 1.
    Proof.
      intros Hy Hn IH i st s le h m Hc Hi Htr Hinv Huse Hexp.
      pose proof Hinv as (Hm & Hs & Htm).
      pose proof (exp_ok_proj _ _ _ _ _ _ Hexp) as Hexp'.
      destruct (eo_bound _ _ Hexp x) as (Hxr & Hxf & Hxs & Hxfree); [constructor |].
      destruct (pipeline_ident x) as (Hx1 & Hx2 & _); [lia |].
      cbn [trans] in Htr. bind_inv_as Htr s' Htr'. apply Ret_inj in Htr. subst s.
      destruct (var_word i st rho (Eproj x t n y e) le h m y Hi Htm) as (vy & wy & Hvy & Hwy & Hry).
      { constructor. }
      { apply Huse. simpl. apply PS.add_spec. now left. }
      assert (vy = Vconstr t vs) by congruence. subst vy.
      apply nthN_nth_error in Hn.
      assert (Hlt : (N.to_nat n < length vs)%nat).
      { apply nth_error_Some. intros Hnone. rewrite Hnone in Hn. discriminate. }
      inversion Hry as [? ? Hrep | ? ? ord b ofs Hrep Hobj Hlo Hhi Hreg Hhdr Hfields |]; subst.
      { simpl in Hlt. lia. }
      destruct (repr_fields_nth _ _ _ _ _ _ _ _ Hfields _ _ Hn) as (w0 & Hw0 & Hr0).
      assert (Heval : eval_expr ge lenv le m (field (var_expr nparam fenv y) (Z.of_N n)) w0).
      { eapply eval_load.
        - apply eval_field.
          + apply eval_var_expr; [exact Hwy | exact I |]. intros Hfy. apply lenv_fun. exact Hfy.
          + rewrite typeof_var_expr. reflexivity.
        - reflexivity.
        - rewrite field_address by lia. rewrite <- Hw0. f_equal. lia. }
      destruct (IH i st s' (PTree.set x w0 le) h m) as (w' & h' & m' & Hstar & Hres & Hti & Hstep); auto.
      - lia.
      - split; [| split; [exact Hs |]].
        + apply mem_inv_set; auto.
        + apply (tmp_inv_set i st rho (Eproj x t n y e) e le h m x _ _ Htm Hr0 Hx1 Hx2 Hxf).
          * intros z Hz. destruct (Pos.eq_dec z x) as [-> | Hne]; [now left | right].
            apply Free_Eproj2; [congruence | exact Hz].
          * simpl. lia.
      - intros z Hz. apply Huse. simpl. apply PS.add_spec. now right.
      - exists w', h', m'. split; [| split; [| split]]; auto.
        + intros k0 k Hk0 Hcont.
          eapply star_trans; [apply seq_star; apply runs_set; exact Heval | | reflexivity].
          apply Hstar; auto.
        + eapply val_rel_mono; [| exact Hres]. lia.
    Qed.

    (** ** Case analysis *)

    (* The branch that the source program takes is the first one of its key *)
    Lemma case_branches st
          (go : list (ctor_tag * exp) -> error (list (Z * statement) * list (Z * statement))) :
      go [] = Ret ([], []) ->
      (forall t e' cs',
          go ((t, e') :: cs') =
          bind (ctor_rep_of cenv t) (fun r =>
          bind (enter prims fenv (Z.of_nat nroots) st e') (fun '(s_chk, st') =>
          bind (trans nparam prims cenv fenv self (Z.of_nat nroots) tmps st' e') (fun s =>
          bind (go cs') (fun '(blocks, constants) =>
          match r with
          | Block ordinal _ => ret ((ordinal, seq s_chk s) :: blocks, constants)
          | Constant ordinal => ret (blocks, (constant_value ordinal, seq s_chk s) :: constants)
          end))))) ->
      forall cl blocks constants,
        go cl = Ret (blocks, constants) ->
        forall t e n,
          find_tag_nth cl t e n -> caseConsistent cenv cl t ->
          exists r s_chk st' s_e,
            ctor_rep_of cenv t = Ret r /\
            enter prims fenv (Z.of_nat nroots) st e = Ret (s_chk, st') /\
            trans nparam prims cenv fenv self (Z.of_nat nroots) tmps st' e = Ret s_e /\
            match r with
            | Block ord _ => first_key blocks ord (seq s_chk s_e)
            | Constant ord => first_key constants (constant_value ord) (seq s_chk s_e)
            end.
    Proof.
      intros Hnil Hcons.
      induction cl as [| [t0 e0] cl IH]; intros blocks constants Hgo t e n Hfind Hcc.
      - inversion Hfind.
      - rewrite Hcons in Hgo.
        bind_inv_as Hgo r0 Hrep0. bind_inv_as Hgo p Hent0. destruct p as [s_chk0 st0].
        cbv beta iota in Hgo.
        bind_inv_as Hgo s0 Htr0. bind_inv_as Hgo q Hgo'. destruct q as [blocks' constants'].
        cbv beta iota in Hgo.
        inversion Hcc as [| info info' ? ? ? ? Hinfo Hinfo' Htag Hcc']; subst.
        inversion Hfind as [| ? ? ? ? ? n' Hfind' Hne]; subst.
        + (* the first branch *)
          exists r0, s_chk0, st0, s0. split; [exact Hrep0 |]. split; [exact Hent0 |].
          split; [exact Htr0 |].
          destruct r0; apply Ret_inj in Hgo; apply pair_equal_spec in Hgo; destruct Hgo as [<- <-];
            apply first_key_head.
        + (* a later branch *)
          destruct (IH _ _ Hgo' _ _ _ Hfind' Hcc')
            as (r & s_chk & st' & s_e & Hrep & Hent & Htr & Hkey).
          exists r, s_chk, st', s_e. split; [exact Hrep |]. split; [exact Hent |].
          split; [exact Htr |].
          destruct (ctor_rep_of_inv _ _ _ Hrep0) as (i0 & Hi0 & Hk0).
          destruct (ctor_rep_of_inv _ _ _ Hrep) as (i1 & Hi1 & Hk1).
          assert (Hi0' : i0 = info') by congruence. assert (Hi1' : i1 = info) by congruence.
          subst i0 i1.
          assert (Hdiff : (ctor_arity info' = 0%N <-> ctor_arity info = 0%N) ->
                          ctor_ordinal info' <> ctor_ordinal info).
          { intros Har Heq. apply Hne.
            exact (Hord t0 t info' info Hinfo' Hinfo (eq_sym Htag) Har Heq). }
          destruct Hk0 as [[Ha0 ->] | (Ha0 & Ho0 & ->)];
            destruct Hk1 as [[Ha1 ->] | (Ha1 & Ho1 & ->)];
            apply Ret_inj in Hgo; apply pair_equal_spec in Hgo; destruct Hgo as [<- <-].
          * apply first_key_cons; [| exact Hkey]. unfold constant_value.
            assert (ctor_ordinal info' <> ctor_ordinal info) by (apply Hdiff; tauto). lia.
          * exact Hkey.
          * exact Hkey.
          * apply first_key_cons; [| exact Hkey].
            assert (ctor_ordinal info' <> ctor_ordinal info) by (apply Hdiff; tauto). lia.
    Qed.

    (* The case analysis of a block goes to the statement of its ordinal *)
    Lemma case_block_star le m (y : var) b ofs ord len blocks constants s_br :
      var_val ge le fenv y (Vptr b ofs) -> (100 <= y)%positive ->
      8 <= Ptrofs.unsigned ofs -> (2 | Ptrofs.unsigned ofs) ->
      Mem.load Mptr m b (Ptrofs.unsigned ofs - 8)
      = Some (Vlong (Int64.repr (block_header ord len))) ->
      0 <= ord <= max_block_ordinal -> 0 <= len ->
      first_key blocks ord s_br ->
      exists le',
        (forall x, x <> boxedId -> le' ! x = le ! x) /\
        forall k, exists k',
          star step2 ge
               (Clight.State fn (case_stmt (var_expr nparam fenv y) blocks constants) k lenv le m)
               E0 (Clight.State fn s_br k' lenv le' m) /\
          (k' = k \/ exists rest, k' = Kseq rest (Kswitch k)).
    Proof.
      intros Hy Hy100 Hofs Heven Hhdr Hord_r Hlen Hkey.
      assert (Htag : forall le0 k1,
                 var_val ge le0 fenv y (Vptr b ofs) ->
                 exists k',
                   star step2 ge
                        (Clight.State fn (switch (tag (var_expr nparam fenv y)) blocks) k1 lenv le0 m)
                        E0 (Clight.State fn s_br k' lenv le0 m) /\
                   (k' = k1 \/ exists rest, k' = Kseq rest (Kswitch k1))).
      { intros le0 k1 Hy0.
        apply (star_switch ge fn lenv le0 m (tag (var_expr nparam fenv y)) blocks
                           (Vlong (Int64.and (Int64.repr (block_header ord len)) (Int64.repr 255)))
                           ord s_br k1).
        - apply eval_tag with (b := b) (ofs := ofs); auto.
          + apply eval_var_expr; [exact Hy0 | exact I |]. intros Hfy. apply lenv_fun. exact Hfy.
          + rewrite typeof_var_expr. reflexivity.
        - change (typeof (tag (var_expr nparam fenv y))) with tuintnat.
          rewrite switch_arg_long. f_equal. apply header_tag; auto.
        - exact Hkey. }
      unfold case_stmt.
      destruct blocks as [| bl0 blocks']; [exfalso; eapply first_key_not_nil; eauto |].
      destruct constants as [| cn0 constants'].
      - exists le. split; [auto |]. intros k. exact (Htag le k Hy).
      - destruct (prog_is_ptr _ _ _ _ _ _ _ Hprog) as (bp & Hbp & Hfp).
        destruct Hisptr as [Hptr _].
        set (le1 := PTree.set boxedId Vtrue le).
        assert (Hy1 : var_val ge le1 fenv y (Vptr b ofs)).
        { apply var_val_set; auto. intros ->. unfold boxedId in Hy100. lia. }
        exists le1. split; [intros x Hx; unfold le1; apply PTree.gso; exact Hx |].
        intros k. destruct (Htag le1 k Hy1) as (k' & Hstar & Hk').
        exists k'. split; [| exact Hk'].
        eapply star_trans; [apply seq_star | | reflexivity].
        { change le1 with (set_opttemp (Some boxedId) Vtrue le).
          eapply runs_call with (vf := Vptr bp Ptrofs.zero) (vargs := [Vptr b ofs]).
          - reflexivity.
          - eapply eval_Elvalue.
            + apply eval_Evar_global; [apply lenv_other; discriminate | exact Hbp].
            + apply deref_loc_reference. reflexivity.
          - econstructor; [| | constructor].
            + apply eval_var_expr; [exact Hy | exact I |]. intros Hfy. apply lenv_fun. exact Hfy.
            + rewrite typeof_var_expr. reflexivity.
          - rewrite Genv.find_funct_find_funct_ptr. exact Hfp.
          - reflexivity.
          - intros k1 _. apply star_one. apply step_external_function. apply Hptr. exact Heven. }
        eapply star_step with (t1 := E0) (t2 := E0); [| exact Hstar | reflexivity].
        apply step_ifthenelse with (v1 := Vtrue) (b := true).
        + apply eval_Etempvar. apply PTree.gss.
        + reflexivity.
    Qed.

    (* The case analysis of a constant goes to the statement of its value *)
    Lemma case_constant_star le m (y : var) ord blocks constants s_br :
      var_val ge le fenv y (Vlong (Int64.repr (constant_value ord))) -> (100 <= y)%positive ->
      0 <= ord < Int64.half_modulus ->
      first_key constants (constant_value ord) s_br ->
      exists le',
        (forall x, x <> boxedId -> le' ! x = le ! x) /\
        forall k, exists k',
          star step2 ge
               (Clight.State fn (case_stmt (var_expr nparam fenv y) blocks constants) k lenv le m)
               E0 (Clight.State fn s_br k' lenv le' m) /\
          (k' = k \/ exists rest, k' = Kseq rest (Kswitch k)).
    Proof.
      intros Hy Hy100 Hord_r Hkey.
      assert (Hunsigned : Int64.unsigned (Int64.repr (constant_value ord)) = constant_value ord).
      { apply Int64.unsigned_repr. unfold constant_value, Int64.max_unsigned.
        rewrite Int64.half_modulus_modulus. lia. }
      assert (Hsw : forall le0 k1,
                 var_val ge le0 fenv y (Vlong (Int64.repr (constant_value ord))) ->
                 exists k',
                   star step2 ge
                        (Clight.State fn (switch (Ecast (var_expr nparam fenv y) tuintnat) constants)
                                      k1 lenv le0 m)
                        E0 (Clight.State fn s_br k' lenv le0 m) /\
                   (k' = k1 \/ exists rest, k' = Kseq rest (Kswitch k1))).
      { intros le0 k1 Hy0.
        apply (star_switch ge fn lenv le0 m (Ecast (var_expr nparam fenv y) tuintnat) constants
                           (Vlong (Int64.repr (constant_value ord))) (constant_value ord) s_br k1).
        - eapply eval_Ecast.
          + apply eval_var_expr; [exact Hy0 | exact I |]. intros Hfy. apply lenv_fun. exact Hfy.
          + rewrite typeof_var_expr. apply sem_cast_word; [reflexivity | exact I].
        - change (typeof (Ecast (var_expr nparam fenv y) tuintnat)) with tuintnat.
          rewrite switch_arg_long, Hunsigned. reflexivity.
        - exact Hkey. }
      unfold case_stmt.
      destruct constants as [| cn0 constants']; [exfalso; eapply first_key_not_nil; eauto |].
      destruct blocks as [| bl0 blocks'].
      - exists le. split; [auto |]. intros k. exact (Hsw le k Hy).
      - destruct (prog_is_ptr _ _ _ _ _ _ _ Hprog) as (bp & Hbp & Hfp).
        destruct Hisptr as [_ Hint].
        set (le1 := PTree.set boxedId Vfalse le).
        assert (Hy1 : var_val ge le1 fenv y (Vlong (Int64.repr (constant_value ord)))).
        { apply var_val_set; auto. intros ->. unfold boxedId in Hy100. lia. }
        exists le1. split; [intros x Hx; unfold le1; apply PTree.gso; exact Hx |].
        intros k. destruct (Hsw le1 k Hy1) as (k' & Hstar & Hk').
        exists k'. split; [| exact Hk'].
        eapply star_trans; [apply seq_star | | reflexivity].
        { change le1 with (set_opttemp (Some boxedId) Vfalse le).
          eapply runs_call with (vf := Vptr bp Ptrofs.zero)
                                (vargs := [Vlong (Int64.repr (constant_value ord))]).
          - reflexivity.
          - eapply eval_Elvalue.
            + apply eval_Evar_global; [apply lenv_other; discriminate | exact Hbp].
            + apply deref_loc_reference. reflexivity.
          - econstructor; [| | constructor].
            + apply eval_var_expr; [exact Hy | exact I |]. intros Hfy. apply lenv_fun. exact Hfy.
            + rewrite typeof_var_expr. reflexivity.
          - rewrite Genv.find_funct_find_funct_ptr. exact Hfp.
          - reflexivity.
          - intros k1 _. apply star_one. apply step_external_function. apply Hint.
            rewrite Hunsigned. unfold constant_value. rewrite Z.add_comm, Z.odd_add_mul_2.
            reflexivity. }
        eapply star_step with (t1 := E0) (t2 := E0); [| exact Hstar | reflexivity].
        apply step_ifthenelse with (v1 := Vfalse) (b := false).
        + apply eval_Etempvar. apply PTree.gss.
        + reflexivity.
    Qed.

    Lemma case_correct rho (y : var) t vs cl e n (c : fuel) v :
      M.get y rho = Some (Vconstr t vs) ->
      caseConsistent cenv cl t ->
      find_tag_nth cl t e n ->
      exp_correct rho e c v 0 ->
      exp_correct rho (Ecase y cl) c v 1.
    Proof.
      intros Hy Hcc Hfind IH i st s le h m Hc Hi Htr Hinv Huse Hexp.
      pose proof Hinv as (Hm & Hs & Htm).
      pose proof (find_tag_nth_In_patterns _ _ _ _ Hfind) as Hin.
      pose proof (exp_ok_case _ _ _ _ _ Hexp Hin) as Hexp'.
      assert (Hy100 : (100 <= y)%positive).
      { assert (Hfy : occurs_free (Ecase y cl) y) by constructor.
        apply (eo_free _ _ Hexp) in Hfy. lia. }
      cbn [trans] in Htr. bind_inv_as Htr cases Hcases. apply Ret_inj in Htr. subst s.
      destruct cases as [blocks constants]. cbn [fst snd].
      match type of Hcases with
      | ?g cl = _ =>
        destruct (case_branches st g eq_refl (fun _ _ _ => eq_refl) cl blocks constants Hcases
                                t e n Hfind Hcc)
          as (r & s_chk & st' & s_e & Hrep & Hent & Htr_e & Hkey)
      end.
      (* the value that is analysed *)
      destruct (var_word i st rho (Ecase y cl) le h m y Hi Htm) as (vy & wy & Hvy & Hwy & Hry).
      { constructor. }
      { apply Huse. apply uses_now_case_var. }
      assert (vy = Vconstr t vs) by congruence. subst vy.
      (* the code reaches the branch *)
      assert (Hbranch : exists le1,
                 (forall x, x <> boxedId -> le1 ! x = le ! x) /\
                 forall k, exists k',
                   star step2 ge
                        (Clight.State fn (case_stmt (var_expr nparam fenv y) blocks constants)
                                      k lenv le m)
                        E0 (Clight.State fn (seq s_chk s_e) k' lenv le1 m) /\
                   (k' = k \/ exists rest, k' = Kseq rest (Kswitch k))).
      { inversion Hry as [? ord Hrep' | ? ? ord b ofs Hrep' Hobj Hlo Hhi Hreg Hhdr Hfields |]; subst.
        - assert (Hr : r = Constant ord) by congruence. subst r.
          destruct (ctor_rep_of_inv _ _ _ Hrep) as (info & Hinfo & [[_ Hkind] | (_ & _ & Hkind)]);
            [| discriminate].
          assert (Ho : ord = Z.of_N (ctor_ordinal info)) by congruence.
          apply (case_constant_star le m y ord blocks constants (seq s_chk s_e)); auto.
          rewrite Ho. split; [lia | apply (Hsmall _ _ Hinfo)].
        - assert (Hr : r = Block ord (length vs)) by congruence. subst r.
          destruct (ctor_rep_of_inv _ _ _ Hrep)
            as (info & Hinfo & [[_ Hkind] | (_ & Hle_ord & Hkind)]); [discriminate |].
          assert (Ho : ord = Z.of_N (ctor_ordinal info)) by congruence.
          apply (case_block_star le m y b ofs ord (Z.of_nat (length vs)) blocks constants
                                 (seq s_chk s_e)); auto.
          + destruct (Mem.load_valid_access _ _ _ _ _ Hhdr) as [_ Hal].
            change (align_chunk Mptr) with 8 in Hal. destruct Hal as [q Hq].
            exists (4 * (q + 1)). lia.
          + rewrite Ho. lia.
          + lia. }
      destruct Hbranch as (le1 & Hle1 & Hbr).
      assert (Hinv1 : inv i st rho e le1 h m).
      { split; [exact Hm | split; [exact Hs |]].
        apply (tmp_inv_temps i st rho e le le1 h m).
        - eapply tmp_inv_sub; [exact Htm | |].
          + intros z Hz. eapply occurs_free_Ecase_Included; eauto.
          + eapply alloc_need_case; eauto.
        - apply Hle1. discriminate.
        - intros _. apply Hle1. discriminate.
        - intros z Hz _ _. apply Hle1.
          assert (Hfz : occurs_free (Ecase y cl) z) by (eapply occurs_free_Ecase_Included; eauto).
          apply (eo_free _ _ Hexp) in Hfz. unfold boxedId. lia. }
      assert (Huse1 : uses_ok st e).
      { intros z Hz. apply Huse. eapply uses_now_case; eauto. }
      destruct (enter_correct i st rho e le1 h m s_chk st' Hi Hinv1 Hexp' Hent)
        as (le2 & h2 & m2 & Hrun2 & Hinv2 & Hstep2 & Hstale2 & Hslots2 & Hlinked2).
      destruct (IH i st' s_e le2 h2 m2) as (w & h' & m' & Hstar & Hres & Hti & Hstep); auto.
      { lia. }
      { eapply uses_ok_state; eauto. }
      { eapply exp_ok_slots; [exact Hexp' |]. intros z Hz. rewrite Hslots2 in Hz. now left. }
      exists w, h', m'. split; [| split; [| split; [exact Hti |]]].
      - intros k0 k Hk0 Hcont. destruct (Hbr k) as (k' & Hstar1 & Hk').
        eapply star_trans; [exact Hstar1 | | reflexivity].
        eapply star_trans; [apply seq_star; exact Hrun2 | | reflexivity].
        apply Hstar; auto.
        destruct Hk' as [-> | [rest ->]]; [exact Hcont | constructor; constructor; exact Hcont].
      - eapply val_rel_mono; [| exact Hres]. lia.
      - eapply step_ok_trans; eauto.
    Qed.

    (** ** Calls of the expression *)

    (* A change in the thread info keeps the roots of the function *)
    Lemma slots_hold_tinfo i slots rho h m m' :
      slots_hold i slots rho h m -> (length slots <= nroots)%nat ->
      data_kept h m h m' ->
      Mem.unchanged_on (fun b o => b <> tb) m m' ->
      slots_hold i slots rho h m'.
    Proof.
      intros Hsl Hlen Hk Hun. destruct (Nat.eq_dec nroots 0) as [Hz | Hnz].
      - intros j x Hj. destruct slots; [destruct j; discriminate | simpl in Hlen; lia].
      - eapply slots_hold_kept; eauto. intros j w Hw.
        eapply Mem.load_unchanged_on; [exact Hun | | exact Hw].
        intros o _. simpl. apply (Hown Hnz).
    Qed.

    (* A call whose result the function returns *)
    Lemma tail_call_correct e (r : ident) (f : var) (ys : list var) rho rho' fl f' vs
          (xs : list var) t e_body rho'' (c : fuel) v (tr : trace) :
      (forall y, y = f \/ In y ys -> occurs_free e y /\ PS.In y (uses_now prims e)) ->
      (forall g ps, self = Some (g, ps) ->
                    Pos.eqb f g && Nat.eqb (length ys) (length ps) = true ->
                    calls_itself g (length ps) e = true) ->
      M.get f rho = Some (Vfun rho' fl f') ->
      get_list ys rho = Some vs ->
      find_def f' fl = Some (t, xs, e_body) ->
      set_lists xs vs (def_funs fl fl rho' rho') = Some rho'' ->
      bstep_fuel cenv rho'' e_body c (Res v) tr ->
      exp_correct rho'' e_body c v 0 ->
      forall i st s le h m,
        (to_nat c + 1 <= i)%nat -> (i < K)%nat ->
        tail_call nparam fenv self tmps st r f ys = Ret s ->
        inv i st rho e le h m -> uses_ok st e -> exp_ok st e ->
        exists w h' m',
          (forall k0 k, is_call_cont k0 -> cont_ok k0 k ->
                        star step2 ge (Clight.State fn s k lenv le m) E0 (Returnstate w k0 m')) /\
          val_rel (i - to_nat c - 1) h' m' v w /\
          tinfo_ok h' fs0 m' tb tofs /\
          step_ok h m h' m'.
    Proof.
      intros Hfree Hloop Hfun Hys Hfind Hset Hbstep IH i st s le h m Hc Hi Htc Hinv Huse Hexp.
      pose proof Hinv as (Hm & Hs & Htm).
      pose proof (ti_tinfo _ _ _ _ _ _ _ Htm) as Hle_ti.
      destruct (var_word i st rho e le h m f Hi Htm) as (vf & wf & Hvf & Hvalf & Hrf).
      { apply Hfree. now left. }
      { apply Huse. apply Hfree. now left. }
      assert (vf = Vfun rho' fl f') by congruence. subst vf.
      destruct (vars_words i st rho e le h m ys Hi Htm) as (vs' & ws & Hvs' & Hws & Hrs).
      { intros y Hy. destruct (Hfree y) as [H1 H2]; [right; exact Hy |].
        split; [exact H1 | apply Huse; exact H2]. }
      assert (vs' = vs) by congruence. subst vs'.
      destruct (leave_correct i st rho e le h m Hinv) as (m1 & Hrun1 & Hti1 & Hk1 & Hstep1 & Hloc1).
      assert (Hrs1 : Forall2 (val_rel i h m1) vs ws).
      { eapply Forall2_impl; [| exact Hrs]. intros a b0 Hab. eapply val_rel_kept; eauto. }
      (* a call of another function *)
      assert (Hother :
                bind (call nparam fenv r f ys)
                     (fun c0 => ret (seq (leave st) (seq c0 (Sreturn (Some (Etempvar r tvalue))))))
                = Ret s ->
                exists w h' m',
                  (forall k0 k, is_call_cont k0 -> cont_ok k0 k ->
                                star step2 ge (Clight.State fn s k lenv le m) E0
                                     (Returnstate w k0 m')) /\
                  val_rel (i - to_nat c - 1) h' m' v w /\
                  tinfo_ok h' fs0 m' tb tofs /\
                  step_ok h m h' m').
      { intros Hb. bind_inv_as Hb c0 Hcall. apply Ret_inj in Hb. subst s.
        assert (Hlt : (to_nat c < i)%nat) by lia.
        assert (Hrf1 : val_rel i h m1 (Vfun rho' fl f') wf) by (eapply val_rel_kept; eauto).
        destruct (call_correct i le h m1 fs0 r f ys c0 rho' fl f' wf vs ws xs t e_body rho'' c v tr
                               Hlt Hcall Hti1 Hle_ti Hvalf Hrf1 Hws Hrs1 Hfind Hset Hbstep)
          as (w & h' & m2 & Hrun2 & Hres & Hti2 & Hroots2 & Hch2).
        assert (Hloc2 : locals_ok h' m2).
        { eapply locals_after_call; [apply (mem_inv_init i rho h m1 Hti1 Hloc1) | exact Hch2]. }
        destruct (free_locals h' m2 Hloc2 Hti2) as (m3 & Hfree3 & Hti3 & Hk3 & Hstep3).
        exists w, h', m3. split; [| split; [| split; [exact Hti3 |]]].
        - intros k0 k Hk0 Hcont.
          eapply star_trans; [apply seq_star; exact Hrun1 | | reflexivity].
          eapply star_trans; [apply seq_star; exact Hrun2 | | reflexivity].
          rewrite <- (cont_ok_call_cont k0 k Hk0 Hcont).
          eapply star_return; [apply eval_Etempvar; apply PTree.gss | | exact Hfree3].
          rewrite Hreturn. apply sem_cast_word; [reflexivity | eapply val_rel_word; eauto].
        - eapply val_rel_kept; [exact Hk3 |].
          replace (i - to_nat c - 1)%nat with (i - 1 - to_nat c)%nat by lia. exact Hres.
        - eapply step_ok_trans; [exact Hstep1 |]. eapply step_ok_trans; [| exact Hstep3].
          apply (step_ok_call init_state h m1 h' m2 0 st_ok_init Hroots2 Hch2). }
      revert Htc. unfold tail_call. cbv zeta.
      case_eq self; [intros [g ps] Hself_eq | intros Hself_eq]; intros Htc; [| exact (Hother Htc)].
      match type of Htc with
      | (if ?b then _ else _) = _ => destruct b eqn:Hloopb; [| exact (Hother Htc)]
      end.
      (* the function calls itself: the code goes back to its start *)
      clear Hother. apply Ret_inj in Htc. subst s.
      pose proof (Hloop g ps Hself_eq Hloopb) as Hci.
      pose proof (eo_loop _ _ Hexp g ps Hself_eq Hci) as Hloops.
      apply andb_true_iff in Hloopb. destruct Hloopb as [Hfg Hlen_eq].
      apply Pos.eqb_eq in Hfg. apply Nat.eqb_eq in Hlen_eq. subst g.
      destruct (Hself f ps Hself_eq) as (Hps & [t' Hfind_g] & Htmps & _). subst ps.
      assert (Hff : M.get f fenv <> None).
      { unfold fenv. rewrite fun_arities_find, Hfind_g. discriminate. }
      pose proof (ti_funs _ _ _ _ _ _ _ Htm f Hff) as Hfun'.
      assert (Heq : Vfun rho' fl f' = Vfun rho0 fds f) by congruence.
      injection Heq as -> -> ->.
      assert (Hxs : xs = params) by congruence. assert (He : e_body = body) by congruence.
      subst xs e_body.
      destruct (runs_assign_params ge nparam fn lenv m1 fenv tmps params ys le)
        as (le2 & Hrun2 & Hset2 & Hother2).
      { exact (bo_params _ _ Hbody). }
      { rewrite Htmps. apply idents_from_NoDup. }
      { symmetry. exact Hlen_eq. }
      { rewrite Htmps, idents_from_length. apply Nat.le_refl. }
      { intros y Hy. destruct (In_nth_error _ _ Hy) as [j Hj].
        destruct (Forall2_nth_l _ _ _ Hws _ _ Hj) as (w & Hw & Hvw).
        exists w. split; [exact Hvw |].
        destruct (Forall2_nth_r _ _ _ Hrs _ _ Hw) as (v0 & _ & Hr). eapply val_rel_word; eauto. }
      { intros y _ Hfy. apply lenv_fun. exact Hfy. }
      { exact (bo_params_funs _ _ Hbody). }
      { intros t0 Hin0. rewrite Htmps in Hin0. apply idents_from_ge in Hin0. split.
        - intros Hin. assert (Hr0 : (100 <= t0 < tmp)%positive).
          { apply (bo_ids _ _ Hbody). right. exact Hin. }
          lia.
        - intros Hin. destruct (Hfree t0) as [Hft _]; [right; exact Hin |].
          apply (eo_free _ _ Hexp) in Hft. lia. }
      assert (Hle2 : forall j p w, nth_error params j = Some p -> nth_error ws j = Some w ->
                                   le2 ! p = Some w).
      { intros j p w Hp Hw. destruct (Forall2_nth_r _ _ _ Hws _ _ Hw) as (y & Hy & Hvw).
        eapply Hset2; eauto. }
      assert (Hti2 : le2 ! tinfoId = Some (Vptr tb (Ptrofs.repr tofs))).
      { rewrite Hother2; [exact Hle_ti | |].
        - intros Hin. assert (Hr : (100 <= tinfoId < tmp)%positive).
          { apply (bo_ids _ _ Hbody). right. exact Hin. }
          unfold tinfoId in Hr. lia.
        - rewrite Htmps. intros Hin. apply idents_from_ge in Hin. unfold tinfoId in Hin. lia. }
      assert (Hc' : (to_nat c <= i)%nat) by lia.
      destruct (code_correct rho'' c v i vs ws le2 h m1 IH Hc' Hi Hset Hrs1 Hle2 Hti2 Hti1 Hloc1)
        as (w & h' & m' & Hstar & Hres & Hti' & Hstep').
      exists w, h', m'. split; [| split; [| split; [exact Hti' |]]].
      - intros k0 k Hk0 Hcont.
        eapply star_trans; [apply seq_star; exact Hrun1 | | reflexivity].
        eapply star_trans; [apply seq_star; exact Hrun2 | | reflexivity].
        eapply star_trans; [apply cont_ok_continue; [exact Hcont | exact Hloops] | | reflexivity].
        apply Hstar; [exact Hk0 | apply Cont_loop; exact Hloops].
      - eapply val_rel_mono; [| exact Hres]. lia.
      - eapply step_ok_trans; eauto.
    Qed.

    (* A call followed by the rest of the expression *)
    Lemma letapp_correct rho (x f : var) t (ys : list var) e rho' fl f' vs (xs : list var)
          e_body rho'' (c1 c2 : fuel) v v' (tr1 : trace) :
      returns x e = false ->
      M.get f rho = Some (Vfun rho' fl f') ->
      get_list ys rho = Some vs ->
      find_def f' fl = Some (t, xs, e_body) ->
      set_lists xs vs (def_funs fl fl rho' rho') = Some rho'' ->
      bstep_fuel cenv rho'' e_body c1 (Res v) tr1 ->
      exp_correct (M.set x v rho) e c2 v' 0 ->
      exp_correct rho (Eletapp x f t ys e) (algebra.plus c1 c2) v' 1.
    Proof.
      intros Hret Hfun Hys Hfind Hset Hbstep IH i st s le h m Hc Hi Htr Hinv Huse Hexp.
      pose proof Hinv as (Hm & Hs & Htm).
      rewrite to_nat_add in Hc.
      pose proof (exp_ok_letapp _ _ _ _ _ _ Hexp) as Hexp'.
      pose proof (ti_tinfo _ _ _ _ _ _ _ Htm) as Hle_ti.
      destruct (eo_bound _ _ Hexp x) as (Hxr & Hxf & Hxs & Hxfree); [constructor |].
      destruct (pipeline_ident x) as (Hx1 & Hx2 & _); [lia |].
      cbn [trans] in Htr. rewrite Hret in Htr.
      bind_inv_as Htr c0 Hcall. unfold call_then in Htr.
      remember (live_after fenv x e) as live eqn:Hlive_def in *.
      match type of Htr with
      | context [push_roots ?a ?b ?l] => destruct (push_roots a b l) as [s_roots stp] eqn:Hpush
      end.
      cbv beta iota in Htr.
      bind_inv_as Htr p Hent. destruct p as [s_chk st2]. cbv beta iota in Htr.
      match type of Htr with
      | context [reload ?a ?b ?u] => destruct (reload a b u) as [s_reload st3] eqn:Hreload
      end.
      cbv beta iota in Htr.
      bind_inv_as Htr s_e Htr_e. apply Ret_inj in Htr. subst s.
      (* the words of the function and of the arguments *)
      destruct (var_word i st rho (Eletapp x f t ys e) le h m f Hi Htm)
        as (vf & wf & Hvf & Hvalf & Hrf).
      { constructor. now left. }
      { apply Huse. simpl. apply PS.add_spec. now left. }
      assert (vf = Vfun rho' fl f') by congruence. subst vf.
      destruct (vars_words i st rho (Eletapp x f t ys e) le h m ys Hi Htm)
        as (vs' & ws & Hvs' & Hws & Hrs).
      { intros z Hz. split; [constructor; now right |].
        apply Huse. simpl. apply PS.add_spec. right. apply union_list_spec. now right. }
      assert (vs' = vs) by congruence. subst vs'.
      (* the variables that are needed after the call go to the roots *)
      assert (Hlive : forall z, In z live ->
                                occurs_free (Eletapp x f t ys e) z /\ M.get z fenv = None).
      { intros z Hz. rewrite Hlive_def in Hz. apply live_after_spec in Hz.
        destruct Hz as (Hz1 & Hz2 & Hz3). split; [| exact Hz2].
        apply Free_Eletapp2; [congruence | exact Hz1]. }
      assert (Hlive_len : (length live <= nroots)%nat).
      { pose proof (eo_roots _ _ Hexp) as Hr. cbn [max_roots] in Hr. rewrite Hret in Hr.
        rewrite <- Hlive_def in Hr. lia. }
      assert (Hlive_nd : NoDup live) by (rewrite Hlive_def; apply live_after_NoDup).
      destruct (push_roots_correct i st rho (Eletapp x f t ys e) le h m live s_roots stp Hi Hinv
                                   Hlive_nd Hlive Hlive_len Hpush)
        as (m1 & Hrun1 & Hwf1 & Hhold1 & Hal1 & Hk1 & Hstep1 & Hloc1 & Hsp & Hstale_p & Hroom_p
            & Hdirty_p & Hslots_p).
      (* [tinfo->alloc] *)
      destruct (sync_run st le h (cur_frames stp) m1 Hwf1 Hle_ti)
        as (m2 & Hrun2 & Hal2 & Hwf2 & Hun2 & Hkp2).
      { intros Hd. apply (proj1 (ti_room _ _ _ _ _ _ _ Htm (so_dirty _ Hs Hd))). }
      { intros Hd. rewrite Hal1. exact (mi_sync _ _ _ _ _ Hm Hd). }
      assert (Hm1 : mem_inv i (LambdaANF_to_C.allocated stp) rho h m1).
      { constructor.
        - exact Hwf1.
        - intros Hd. simpl in Hd. discriminate.
        - exact Hhold1.
        - exact Hloc1. }
      destruct (step_ok_region i _ rho h m1 m2 (fun b o => b = tb /\ tofs <= o < tofs + 8)
                               Hm1 Hun2 Hkp2) as [Hk2 Hstep2].
      { intros b o [-> Ho]. right. right. split; [reflexivity | ofs_lia]. }
      assert (Hm2 : mem_inv i stp rho h m2).
      { constructor.
        - exact Hwf2.
        - intros _. exact Hal2.
        - eapply slots_hold_tinfo; [exact Hhold1 | exact (so_nslots _ Hsp) | exact Hk2 |].
          eapply Mem.unchanged_on_implies; [exact Hun2 |]. intros b o Hb _ [Heq _]. contradiction.
        - eapply locals_ok_kept; [exact Hloc1 | exact Hkp2]. }
      (* the call *)
      assert (Hrf2 : val_rel i h m2 (Vfun rho' fl f') wf).
      { eapply val_rel_kept; [exact Hk2 |]. eapply val_rel_kept; [exact Hk1 | exact Hrf]. }
      assert (Hrs2 : Forall2 (val_rel i h m2) vs ws).
      { eapply Forall2_impl; [| exact Hrs]. intros a b0 Hab.
        eapply val_rel_kept; [exact Hk2 |]. eapply val_rel_kept; [exact Hk1 | exact Hab]. }
      assert (Hlt : (to_nat c1 < i)%nat) by lia.
      destruct (call_correct i le h m2 (cur_frames stp) x f ys c0 rho' fl f' wf vs ws xs t e_body
                             rho'' c1 v tr1 Hlt Hcall (conj Hwf2 Hal2) Hle_ti Hvalf Hrf2 Hws Hrs2
                             Hfind Hset Hbstep)
        as (w & h3 & m3 & Hrun3 & Hres3 & Hti3 & Hroots3 & Hch3).
      (* the state after the call *)
      remember (i - 1 - to_nat c1)%nat as i2 eqn:Hi2 in *.
      assert (Hloc3 : locals_ok h3 m3) by (eapply locals_after_call; [exact Hm2 | exact Hch3]).
      assert (Hx_live : ~ In x (st_slots stp)).
      { intros Hin. apply Hslots_p in Hin. rewrite Hlive_def in Hin. apply live_after_spec in Hin.
        destruct Hin as (_ & _ & Hne). congruence. }
      assert (Hm3 : mem_inv i2 stp (M.set x v rho) h3 m3).
      { apply mem_inv_set; [| exact Hx_live].
        apply (mem_inv_mono i i2); [lia |]. destruct Hti3 as [Hwf3 Hal3]. constructor.
        - exact Hwf3.
        - intros _. exact Hal3.
        - exact (slots_after_call i stp rho h m2 h3 m3 0 Hm2 Hsp Hroots3).
        - exact Hloc3. }
      assert (Htm3 : tmp_inv i2 stp (M.set x v rho) e (PTree.set x w le) h3 m3).
      { destruct Htm as [T1 T2 T3 T4]. constructor.
        - rewrite PTree.gso by congruence. exact T1.
        - intros Hr. rewrite Hroom_p in Hr. discriminate.
        - intros z Hz Hfz. destruct (Pos.eq_dec z x) as [-> | Hne].
          + exists v. split; [apply M.gss |]. intros _. exists w. split; [apply PTree.gss |].
            exact Hres3.
          + assert (Hz' : occurs_free (Eletapp x f t ys e) z).
            { apply Free_Eletapp2; [congruence | exact Hz]. }
            destruct (T3 z Hz' Hfz) as (v0 & Hv0 & _). exists v0. split; [rewrite M.gso; auto |].
            intros Hns. exfalso. apply Hns. rewrite Hstale_p. apply Hslots_p. rewrite Hlive_def.
            apply live_after_spec. split; [exact Hz | split; [exact Hfz | exact Hne]].
        - intros f0 Hf0. rewrite M.gso; [apply T4; exact Hf0 |]. intros ->. contradiction. }
      assert (Hinv3 : inv i2 stp (M.set x v rho) e (PTree.set x w le) h3 m3).
      { split; [exact Hm3 | split; [exact Hsp | exact Htm3]]. }
      assert (Hexp_p : exp_ok stp e).
      { eapply exp_ok_slots; [exact Hexp' |]. intros z Hz. right. apply Hslots_p in Hz.
        rewrite Hlive_def in Hz. apply live_after_spec in Hz. tauto. }
      assert (Hi2K : (i2 < K)%nat) by lia.
      destruct (enter_correct i2 stp (M.set x v rho) e (PTree.set x w le) h3 m3 s_chk st2
                              Hi2K Hinv3 Hexp_p Hent)
        as (le4 & h4 & m4 & Hrun4 & Hinv4 & Hstep4 & Hstale4 & Hslots4 & Hlinked4).
      assert (Hexp2 : exp_ok st2 e).
      { eapply exp_ok_slots; [exact Hexp_p |]. intros z Hz. rewrite Hslots4 in Hz. now left. }
      destruct (reload_correct i2 st2 (M.set x v rho) e le4 h4 m4 s_reload st3 Hinv4 Hexp2 Hreload)
        as (le5 & Hrun5 & Hinv5 & Huse5 & Hslots5 & Hlinked5).
      assert (Hexp3 : exp_ok st3 e).
      { eapply exp_ok_slots; [exact Hexp2 |]. intros z Hz. rewrite Hslots5 in Hz. now left. }
      assert (Hc2 : (to_nat c2 + 0 <= i2)%nat) by lia.
      destruct (IH i2 st3 s_e le5 h4 m4 Hc2 Hi2K Htr_e Hinv5 Huse5 Hexp3)
        as (w' & h5 & m5 & Hstar & Hres & Hti5 & Hstep5).
      exists w', h5, m5. split; [| split; [| split; [exact Hti5 |]]].
      - intros k0 k Hk0 Hcont.
        eapply star_trans; [apply seq_star; exact Hrun1 | | reflexivity].
        eapply star_trans; [apply seq_star; exact Hrun2 | | reflexivity].
        eapply star_trans; [apply seq_star; exact Hrun3 | | reflexivity].
        eapply star_trans; [apply seq_star; exact Hrun4 | | reflexivity].
        eapply star_trans; [apply seq_star; exact Hrun5 | | reflexivity].
        apply Hstar; auto.
      - rewrite to_nat_add.
        replace (i - (to_nat c1 + to_nat c2) - 1)%nat with (i2 - to_nat c2 - 0)%nat by lia.
        exact Hres.
      - eapply step_ok_trans; [exact Hstep1 |]. eapply step_ok_trans; [exact Hstep2 |].
        eapply step_ok_trans; [apply (step_ok_call stp h m2 h3 m3 0 Hsp Hroots3 Hch3) |].
        eapply step_ok_trans; [exact Hstep4 | exact Hstep5].
    Qed.

    Lemma app_correct rho (f : var) t (ys : list var) rho' fl f' vs (xs : list var)
          e_body rho'' (c : fuel) v (tr : trace) :
      M.get f rho = Some (Vfun rho' fl f') ->
      get_list ys rho = Some vs ->
      find_def f' fl = Some (t, xs, e_body) ->
      set_lists xs vs (def_funs fl fl rho' rho') = Some rho'' ->
      bstep_fuel cenv rho'' e_body c (Res v) tr ->
      exp_correct rho'' e_body c v 0 ->
      exp_correct rho (Eapp f t ys) c v 1.
    Proof.
      intros Hfun Hys Hfind Hset Hbstep IH i st s le h m Hc Hi Htr Hinv Huse Hexp.
      cbn [trans] in Htr.
      assert (Hfree : forall y, y = f \/ In y ys ->
                                occurs_free (Eapp f t ys) y /\
                                PS.In y (uses_now prims (Eapp f t ys))).
      { intros y [-> | Hy].
        - split; [constructor |]. simpl. apply PS.add_spec. now left.
        - split; [now constructor |]. simpl. apply PS.add_spec. right.
          apply union_list_spec. now right. }
      assert (Hloop : forall g ps, self = Some (g, ps) ->
                                   Pos.eqb f g && Nat.eqb (length ys) (length ps) = true ->
                                   calls_itself g (length ps) (Eapp f t ys) = true).
      { intros g ps _ Hb. exact Hb. }
      exact (tail_call_correct _ resultId f ys rho rho' fl f' vs xs t e_body rho'' c v tr
                               Hfree Hloop Hfun Hys Hfind Hset Hbstep IH
                               i st s le h m Hc Hi Htr Hinv Huse Hexp).
    Qed.

    (* A call whose result is returned at once *)
    Lemma letapp_tail_correct rho (x f : var) t (ys : list var) rho' fl f' vs (xs : list var)
          e_body rho'' (c1 c2 : fuel) v (tr1 : trace) :
      M.get f rho = Some (Vfun rho' fl f') ->
      get_list ys rho = Some vs ->
      find_def f' fl = Some (t, xs, e_body) ->
      set_lists xs vs (def_funs fl fl rho' rho') = Some rho'' ->
      bstep_fuel cenv rho'' e_body c1 (Res v) tr1 ->
      exp_correct rho'' e_body c1 v 0 ->
      exp_correct rho (Eletapp x f t ys (Ehalt x)) (algebra.plus c1 c2) v 1.
    Proof.
      intros Hfun Hys Hfind Hset Hbstep IH i st s le h m Hc Hi Htr Hinv Huse Hexp.
      cbn [trans returns] in Htr. rewrite Pos.eqb_refl in Htr.
      rewrite to_nat_add in Hc.
      assert (Hc1 : (to_nat c1 + 1 <= i)%nat) by lia.
      assert (Hfree : forall y, y = f \/ In y ys ->
                                occurs_free (Eletapp x f t ys (Ehalt x)) y /\
                                PS.In y (uses_now prims (Eletapp x f t ys (Ehalt x)))).
      { intros y [-> | Hy].
        - split; [constructor; now left |]. simpl. apply PS.add_spec. now left.
        - split; [constructor; now right |]. simpl. apply PS.add_spec. right.
          apply union_list_spec. now right. }
      assert (Hloop : forall g ps, self = Some (g, ps) ->
                                   Pos.eqb f g && Nat.eqb (length ys) (length ps) = true ->
                                   calls_itself g (length ps) (Eletapp x f t ys (Ehalt x)) = true).
      { intros g ps _ Hb. cbn [calls_itself returns]. rewrite Pos.eqb_refl. exact Hb. }
      destruct (tail_call_correct _ x f ys rho rho' fl f' vs xs t e_body rho'' c1 v tr1
                                  Hfree Hloop Hfun Hys Hfind Hset Hbstep IH
                                  i st s le h m Hc1 Hi Htr Hinv Huse Hexp)
        as (w & h' & m' & Hstar & Hres & Hti & Hstep).
      exists w, h', m'. split; [exact Hstar |]. split; [| split; [exact Hti | exact Hstep]].
      rewrite to_nat_add. eapply val_rel_mono; [| exact Hres]. lia.
    Qed.

    (* The code of an expression that evaluates to a value returns the layout of the value *)
    Lemma trans_correct :
      forall rho e (c : fuel) r (t : trace),
        bstep_fuel cenv rho e c r t -> forall v, r = Res v -> exp_correct rho e c v 0.
    Proof.
      apply (bstep_fuel_ind' cenv
               (fun rho e c r t => forall v, r = Res v -> exp_correct rho e c v 1)
               (fun rho e c r t => forall v, r = Res v -> exp_correct rho e c v 0)).
      - intros x t ys e rho rho' vs r cin cout Hys Hrho Hstep IH v Hv. subst.
        eapply constr_correct; eauto.
      - intros t vs rho x n y e v0 r cin cout Hy Hn Hstep IH v Hv. subst.
        eapply proj_correct; eauto.
      - intros y r e t cl vl rho cin n cout Hy Hcc Hfind Hstep IH v Hv. subst.
        eapply case_correct; eauto.
      - intros rho' fl f' vs xs e rho'' rho f t ys r cin cout Hfun Hys Hfind Hset Hstep IH v Hv.
        subst. eapply app_correct; eauto.
      - intros rho' fl f' vs xs e_body e rho'' rho x f t ys v0 r cin1 cin2 cout1 cout2
               Hfun Hys Hfind Hset Hstep1 IH1 Hstep2 IH2 v Hv. subst.
        destruct (returns x e) eqn:Hret.
        + destruct e; try discriminate. simpl in Hret. apply Pos.eqb_eq in Hret. subst.
          apply bstep_fuel_halt in Hstep2. rewrite M.gss in Hstep2. injection Hstep2 as <-.
          eapply letapp_tail_correct; eauto.
        + eapply letapp_correct; eauto.
      - intros. discriminate.
      - intros rho B e r cin cout Hstep IH v Hv i st s le h m Hc Hi Htr.
        cbn [trans] in Htr. discriminate.
      - intros rho' rho x p e r cin cout Hrho Hstep IH v Hv i st s le h m Hc Hi Htr Hinv Huse Hexp.
        assert (Hg : good prims (Eprim_val x p e)) by (apply (eo_sub _ _ Hexp); apply rt_refl).
        destruct Hg as [_ []].
      - intros x v0 rho Hx v Hv. injection Hv as <-. apply halt_correct. exact Hx.
      - intros. discriminate.
      - intros rho e r cin cout Hstep IH v Hv. subst r.
        intros i st s le h m Hc Hi Htr Hinv Huse Hexp.
        rewrite to_nat_add in Hc. unfold one in Hc. rewrite to_nat_one in Hc.
        assert (Hc' : (to_nat cin + 1 <= i)%nat) by lia.
        destruct (IH v eq_refl i st s le h m Hc' Hi Htr Hinv Huse Hexp)
          as (w & h' & m' & Hstar & Hres & Hti & Hstep').
        exists w, h', m'. split; [exact Hstar |]. split; [| split; [exact Hti | exact Hstep']].
        rewrite to_nat_add. unfold one. rewrite to_nat_one.
        replace (i - (to_nat cin + 1) - 0)%nat with (i - to_nat cin - 1)%nat by lia. exact Hres.
    Qed.

    End Call.

    (** ** A call of the function *)

    (* The function called with the layouts of the arguments returns the layout of the
       result *)
    Lemma fun_correct i vs ws rho (c : fuel) v (tr : trace) tb tofs h fs m :
      (to_nat c <= i)%nat -> (i < K)%nat ->
      set_lists params vs (def_funs fds fds rho0 rho0) = Some rho ->
      bstep_fuel cenv rho body c (Res v) tr ->
      tinfo_ok h fs m tb tofs ->
      Forall2 (val_rel i h m) vs ws ->
      args_in_tinfo nparam m tb tofs ws ->
      call_returns cenv ge gc_inv (fun _ _ => False)
                   (fun h' m' w' => val_rel (i - to_nat c) h' m' v w')
                   0 tb tofs fs h m (Internal fn) (Vptr tb (Ptrofs.repr tofs) :: firstn nparam ws).
    Proof.
      intros Hc Hi Hset Hbstep Hti Hrs Hargs.
      pose proof Hti as [Hwf Hal].
      pose proof (wf_range _ _ _ _ _ _ _ _ Hwf) as (Ht0 & Htmax & Htal).
      pose proof (set_lists_length_eq _ _ _ _ Hset) as Hlen_ps.
      pose proof (Forall2_length _ _ _ Hrs) as Hlen_vs.
      assert (Hlen : length params = length ws).
      { transitivity (length vs); [exact Hlen_ps | exact Hlen_vs]. }
      assert (Hti_par : ~ In tinfoId params).
      { intros Hin. assert (Hr : (100 <= tinfoId < tmp)%positive).
        { apply (bo_ids _ _ Hbody). right. exact Hin. }
        unfold tinfoId in Hr. lia. }
      (* the frame and the roots are allocated *)
      assert (Hentry : exists fb rb m1,
                 alloc_variables ge empty_env m (fn_vars fn) (local_env fb rb) m1 /\
                 (nroots <> 0%nat ->
                  ~ Mem.valid_block m fb /\ ~ Mem.valid_block m rb /\ fb <> rb) /\
                 (forall P, Mem.unchanged_on P m m1) /\
                 (forall b o k p, Mem.perm m b o k p -> Mem.perm m1 b o k p) /\
                 (forall b, Mem.valid_block m b -> Mem.valid_block m1 b) /\
                 (nroots <> 0%nat ->
                  Mem.range_perm m1 fb 0 24 Cur Freeable /\
                  Mem.range_perm m1 rb 0 (8 * Z.of_nat nroots) Cur Freeable)).
      { rewrite Hfn_vars. unfold local_env. destruct (Nat.eqb nroots 0) eqn:E.
        - apply Nat.eqb_eq in E. exists tb, tb, m. split; [constructor |].
          split; [intros Hn; contradiction |]. split; [intros P; apply Mem.unchanged_on_refl |].
          split; [auto |]. split; [auto |]. intros Hn. contradiction.
        - apply Nat.eqb_neq in E.
          destruct (Mem.alloc m 0 (sizeof ge frameT)) as [m0 fb] eqn:Ha1.
          destruct (Mem.alloc m0 0 (sizeof ge (tarray tvalue (Z.of_nat nroots))))
            as [m1 rb] eqn:Ha2.
          exists fb, rb, m1. split.
          { econstructor; [exact Ha1 |]. econstructor; [exact Ha2 |]. constructor. }
          split.
          { intros _. split; [eapply Mem.fresh_block_alloc; eauto |]. split.
            - intros Hv. eapply Mem.fresh_block_alloc; [exact Ha2 |].
              eapply Mem.valid_block_alloc; eauto.
            - intros Heq. eapply Mem.fresh_block_alloc; [exact Ha2 |]. rewrite <- Heq.
              eapply Mem.valid_new_block; eauto. }
          split.
          { intros P. eapply Mem.unchanged_on_trans; eapply Mem.alloc_unchanged_on; eauto. }
          split.
          { intros b o k p Hp. eapply Mem.perm_alloc_1; [exact Ha2 |].
            eapply Mem.perm_alloc_1; [exact Ha1 | exact Hp]. }
          split.
          { intros b Hb. eapply Mem.valid_block_alloc; [exact Ha2 |].
            eapply Mem.valid_block_alloc; [exact Ha1 | exact Hb]. }
          intros _. rewrite (sizeof_frame _ Hstructs) in Ha1. rewrite sizeof_roots in Ha2.
          replace (Z.max 0 (Z.of_nat nroots)) with (Z.of_nat nroots) in Ha2 by lia. split.
          + intros o Ho. eapply Mem.perm_alloc_1; [exact Ha2 |].
            eapply Mem.perm_alloc_2; [exact Ha1 | exact Ho].
          + intros o Ho. eapply Mem.perm_alloc_2; [exact Ha2 | exact Ho]. }
      destruct Hentry as (fb & rb & m1 & Halloc & Hfresh & Hun1 & Hperm1 & Hvalid1 & Hranges).
      assert (Htb_valid : Mem.valid_block m tb).
      { eapply Mem.perm_valid_block. apply (wf_perm _ _ _ _ _ _ _ _ Hwf tofs). ofs_lia. }
      assert (Hown' : nroots <> 0%nat ->
                      fb <> rb /\ fb <> tb /\ rb <> tb /\
                      not_in_frames fb fs /\ not_in_frames rb fs).
      { intros Hn. destruct (Hfresh Hn) as (Hf1 & Hf2 & Hf3).
        pose proof (wf_frames _ _ _ _ _ _ _ _ Hwf) as Hfs. rewrite Forall_forall in Hfs.
        split; [exact Hf3 |].
        split; [intros Heq; apply Hf1; rewrite Heq; exact Htb_valid |].
        split; [intros Heq; apply Hf2; rewrite Heq; exact Htb_valid |].
        split.
        - intros fr Hin. destruct (frame_valid _ _ _ _ _ _ (Hfs fr Hin)) as [Hvf Hvr].
          split; intros Heq; apply Hf1; rewrite Heq; assumption.
        - intros fr Hin. destruct (frame_valid _ _ _ _ _ _ (Hfs fr Hin)) as [Hvf Hvr].
          split; intros Heq; apply Hf2; rewrite Heq; assumption. }
      assert (Hk1 : data_kept h m h m1) by (split; [apply Hun1 | auto]).
      assert (Htok1 : tinfo_ok h fs m1 tb tofs).
      { split.
        - eapply (tinfo_wf_unchanged _ _ _ Hgc); [exact Hwf | apply Hun1 | | |].
          + intros o k p Hp. apply Hperm1. exact Hp.
          + intros o k p Hp. apply Hperm1. exact Hp.
          + intros fr _. split; intros o k p Hp; apply Hperm1; exact Hp.
        - eapply Mem.load_unchanged_on; [apply (Hun1 (fun _ _ => True)) | | exact Hal].
          intros; exact I. }
      assert (Hloc1 : locals_ok fb rb h m1).
      { constructor.
        - intros Hn. apply (Hranges Hn).
        - intros Hn. apply (Hranges Hn).
        - intros Hn. destruct (Hfresh Hn) as (Hf1 & Hf2 & _).
          split; intros Hh; [apply Hf1 | apply Hf2]; eapply wf_heap; eauto. }
      assert (Hrs1 : Forall2 (val_rel i h m1) vs ws).
      { eapply Forall2_impl; [| exact Hrs]. intros a b0 Hab. eapply val_rel_kept; eauto. }
      (* the parameters *)
      set (le0 := PTree.set tinfoId (Vptr tb (Ptrofs.repr tofs))
                            (create_undef_temps (fn_temps fn))).
      set (lef := set_temps (firstn nparam params) (firstn nparam ws) le0).
      set (le1 := set_temps params ws le0).
      assert (Hlen_first : length (firstn nparam params) = length (firstn nparam ws)).
      { rewrite !length_firstn. rewrite Hlen. reflexivity. }
      assert (Hbind : bind_parameter_temps (fn_params fn)
                                           (Vptr tb (Ptrofs.repr tofs) :: firstn nparam ws)
                                           (create_undef_temps (fn_temps fn)) = Some lef).
      { rewrite Hfn_params. cbn [bind_parameter_temps]. apply bind_parameter_temps_set.
        exact Hlen_first. }
      assert (Hrun_load : runs ge fn (local_env fb rb) (load_args nparam (skipn nparam params))
                               lef m1 le1 m1).
      { assert (Hle1 : le1 = set_temps (skipn nparam params) (skipn nparam ws) lef).
        { unfold le1, lef. rewrite <- set_temps_app by exact Hlen_first.
          rewrite !firstn_skipn. reflexivity. }
        rewrite Hle1. destruct (le_lt_dec (length params) nparam) as [Hshort | Hlong].
        - rewrite (skipn_all2 params) by exact Hshort. apply runs_skip.
        - apply (runs_load_args ge Hstructs fn (local_env fb rb) tb tofs (conj Ht0 Htmax) m1).
          + unfold lef. rewrite set_temps_other; [unfold le0; apply PTree.gss |].
            intros Hin. apply firstn_In in Hin. contradiction.
          + intros Hin. apply skipn_In in Hin. contradiction.
          + rewrite !length_skipn. rewrite Hlen. reflexivity.
          + intros j w Hj. rewrite nth_error_skipn in Hj.
            eapply Mem.load_unchanged_on; [apply (Hun1 (fun _ _ => True)) | intros; exact I |].
            apply Hargs; [lia | exact Hj].
          + rewrite length_skipn. pose proof (bo_arity _ _ Hbody). lia. }
      assert (Hle1_par : forall j p w, nth_error params j = Some p -> nth_error ws j = Some w ->
                                       le1 ! p = Some w).
      { intros j p w Hp Hw. unfold le1. eapply set_temps_nth; eauto. exact (bo_params _ _ Hbody). }
      assert (Hle1_ti : le1 ! tinfoId = Some (Vptr tb (Ptrofs.repr tofs))).
      { unfold le1. rewrite set_temps_other by exact Hti_par. unfold le0. apply PTree.gss. }
      (* the body *)
      destruct (code_correct tb tofs fs fb rb Hown' rho c v i vs ws le1 h m1
                             (trans_correct tb tofs fs fb rb Hown' rho body c (Res v) tr
                                            Hbstep v eq_refl)
                             Hc Hi Hset Hrs1 Hle1_par Hle1_ti Htok1 Hloc1)
        as (w & h' & m' & Hstar & Hres & Hti' & Hroots' & Hch').
      exists w, h', m'. split.
      - intros k Hk.
        eapply star_step with (t1 := E0) (t2 := E0); [| | reflexivity].
        { apply step_internal_function. constructor.
          - rewrite Hfn_vars. destruct (Nat.eqb nroots 0); [constructor |].
            constructor; [intros [Heq | []]; discriminate |].
            constructor; [intros [] | constructor].
          - rewrite Hfn_params. unfold var_names. cbn [map fst]. rewrite map_fst_tvalue.
            constructor.
            + intros Hin. apply firstn_In in Hin. contradiction.
            + apply NoDup_norepet. apply NoDup_firstn. exact (bo_params _ _ Hbody).
          - exact Hfn_temps.
          - exact Halloc.
          - exact Hbind. }
        rewrite Hfn_body.
        eapply star_trans; [apply seq_star; exact Hrun_load | | reflexivity].
        case_eq loops; intros Hloops.
        + eapply star_step with (t1 := E0) (t2 := E0); [apply step_loop | | reflexivity].
          apply Hstar; [exact Hk | apply Cont_loop; exact Hloops].
        + apply Hstar; [exact Hk | apply Cont_fun; exact Hloops].
      - split; [exact Hres |]. split; [exact Hti' |].
        assert (Hnot_own : forall b o, Mem.valid_block m b -> ~ own_blocks fb rb b o).
        { intros b o Hv [Hn Hb]. destruct (Hfresh Hn) as (Hf1 & Hf2 & _).
          destruct Hb as [-> | ->]; contradiction. }
        split.
        + intros b o Hr. eapply still_represented_trans; [| apply Hroots'; exact Hr].
          apply still_represented_kept; [exact Hk1 |]. intros w0 Hw0.
          eapply Mem.load_unchanged_on; [apply (Hun1 (fun _ _ => True)) | intros; exact I |
                                         exact Hw0].
        + destruct Hch' as (U & P & N). split; [| split].
          * apply Mem.unchanged_on_implies with
                (P := fun b o => (~ heap_blocks h b /\ ~ in_tinfo tb tofs b o /\
                                  ~ in_roots fs b o /\ ~ False) /\ Mem.valid_block m b).
            -- eapply Mem.unchanged_on_trans; [apply Hun1 |].
               eapply Mem.unchanged_on_implies; [exact U |].
               intros b o [(H1 & H2 & H3 & _) Hv] _.
               split; [exact H1 |]. split; [exact H2 |]. split; [exact H3 |].
               apply Hnot_own. exact Hv.
            -- intros b o HX Hv. split; [exact HX | exact Hv].
          * intros b o k p Hh _ Hp. apply P; [exact Hh | | apply Hperm1; exact Hp].
            apply Hnot_own. eapply Mem.perm_valid_block. exact Hp.
          * intros b Hb. destruct (N b Hb) as [Hh | Hnv]; [now left | right].
            intros Hv. apply Hnv. apply Hvalid1. exact Hv.
    Qed.

  End Body.

  (** * The functions of the program *)

  Local Transparent translate_function.

  (* The parts of a function that [translate_function] builds *)
  Lemma translate_function_inv fname ps e fn :
    translate_function nparam prims cenv fenv tmp fname ps e = Ret fn ->
    Z.of_nat (length ps) <= max_args /\
    exists s_check st1 s_body,
      enter prims fenv (Z.of_nat (max_roots prims fenv e)) init_state e = Ret (s_check, st1) /\
      trans nparam prims cenv fenv (option_map (fun f => (f, ps)) fname)
            (Z.of_nat (max_roots prims fenv e)) (idents_from tmp (length ps)) st1 e
      = Ret s_body /\
      fn_return fn = tvalue /\ fn_callconv fn = cc_default /\
      fn_params fn = (tinfoId, tptr tinfoT) :: map (fun x => (x, tvalue)) (firstn nparam ps) /\
      fn_vars fn = (if Nat.eqb (max_roots prims fenv e) 0 then []
                    else [(frameId, frameT);
                          (rootsId, tarray tvalue (Z.of_nat (max_roots prims fenv e)))]) /\
      fn_body fn = seq (load_args nparam (skipn nparam ps))
                       (if match fname with
                           | Some f => calls_itself f (length ps) e
                           | None => false
                           end
                        then Sloop (seq s_check s_body) Sskip else seq s_check s_body) /\
      (forall x, In x (var_names (fn_temps fn)) ->
                 In x (skipn nparam ps) \/ In x (bound_vars e) \/ x = allocId \/ x = resultId \/
                 x = boxedId \/ In x (idents_from tmp (length ps))).
  Proof.
    unfold translate_function.
    destruct (max_args <? Z.of_nat (length ps)) eqn:Hmax; [discriminate |].
    apply Z.ltb_ge in Hmax. intros H. split; [exact Hmax |]. cbv zeta in H.
    bind_inv_as H p Hent. destruct p as [s_check st1]. cbv beta iota in H.
    bind_inv_as H s_body Htr. apply Ret_inj in H. subst fn.
    exists s_check, st1, s_body.
    split; [exact Hent |]. split; [exact Htr |].
    split; [reflexivity |]. split; [reflexivity |]. split; [reflexivity |].
    split; [reflexivity |]. split; [reflexivity |].
    intros x Hx. unfold var_names in Hx. cbn [fn_temps] in Hx.
    rewrite map_app, map_fst_tvalue in Hx. apply in_app_or in Hx. destruct Hx as [Hx | Hx].
    - apply in_app_or in Hx. destruct Hx; [now left | right; now left].
    - apply in_map_iff in Hx. destruct Hx as ([y ty] & Heq & Hin). cbn [fst] in Heq. subst y.
      apply filter_In in Hin. destruct Hin as [Hin _].
      destruct Hin as [Heq | [Heq | [Heq | Hin]]].
      + injection Heq as <- _. right. right. now left.
      + injection Heq as <- _. right. right. right. now left.
      + injection Heq as <- _. right. right. right. right. now left.
      + apply in_map_iff in Hin. destruct Hin as (z & Heq & Hz). injection Heq as <- _.
        right. right. right. right. right. exact Hz.
  Qed.

  Local Opaque translate_function.

  (* The C function of a function of the program, or of its main expression: its type,
     and what a call of it does *)
  Lemma translated_correct fname ps e fn :
    translate_function nparam prims cenv fenv tmp fname ps e = Ret fn ->
    body_ok ps e ->
    (forall f, fname = Some f -> exists t, find_def f fds = Some (t, ps, e)) ->
    type_of_function fn = fun_ty nparam (length ps) /\
    forall i vs ws rho (c : fuel) v (tr : trace) tb tofs h fs m,
      (to_nat c <= i)%nat -> (i < K)%nat ->
      set_lists ps vs (def_funs fds fds rho0 rho0) = Some rho ->
      bstep_fuel cenv rho e c (Res v) tr ->
      tinfo_ok h fs m tb tofs ->
      Forall2 (val_rel i h m) vs ws ->
      args_in_tinfo nparam m tb tofs ws ->
      call_returns cenv ge gc_inv (fun _ _ => False)
                   (fun h' m' w' => val_rel (i - to_nat c) h' m' v w')
                   0 tb tofs fs h m (Internal fn) (Vptr tb (Ptrofs.repr tofs) :: firstn nparam ws).
  Proof.
    intros Htf Hbo Hname.
    destruct (translate_function_inv _ _ _ _ Htf)
      as (Harity & s_check & st1 & s_body & Hent & Htr & Hret & Hcc & Hpar & Hvars & Hbody_eq
          & Htemps).
    assert (Hps : forall p, In p ps -> (100 <= p < tmp)%positive).
    { intros p Hp. apply (bo_ids _ _ Hbo). right. exact Hp. }
    split.
    - unfold type_of_function. rewrite Hpar, Hret, Hcc. unfold fun_ty, type_of_params.
      cbn [map snd]. rewrite map_snd_tvalue, length_firstn, Nat.min_comm. reflexivity.
    - apply (fun_correct (option_map (fun f => (f, ps)) fname) ps e fn (max_roots prims fenv e)
                         (idents_from tmp (length ps))
                         (match fname with
                          | Some f => calls_itself f (length ps) e
                          | None => false
                          end)
                         s_check st1 s_body Hret Hent Htr Hbo).
      + intros g ps' Hg. destruct fname as [f |]; [| discriminate]. simpl in Hg.
        injection Hg as <- <-. split; [reflexivity |]. split; [apply Hname; reflexivity |].
        split; reflexivity.
      + apply Nat.le_refl.
      + exact (bo_roots _ _ Hbo).
      + exact Hpar.
      + exact Hvars.
      + intros x y Hx Hy Heq. subst y. apply Htemps in Hy.
        rewrite Hpar in Hx. unfold var_names in Hx. cbn [map fst] in Hx.
        rewrite map_fst_tvalue in Hx. destruct Hx as [<- | Hx].
        * destruct Hy as [Hy | [Hy | [Hy | [Hy | [Hy | Hy]]]]]; try discriminate.
          -- apply skipn_In in Hy. apply Hps in Hy. unfold tinfoId in Hy. lia.
          -- apply bound_vars_bound in Hy.
             assert (Hr : (100 <= tinfoId < tmp)%positive).
             { apply (bo_ids _ _ Hbo). left. exact Hy. }
             unfold tinfoId in Hr. lia.
          -- apply idents_from_ge in Hy. unfold tinfoId in Hy. lia.
        * pose proof (Hps x (firstn_In _ _ _ Hx)) as Hxr.
          destruct Hy as [Hy | [Hy | [Hy | [Hy | [Hy | Hy]]]]].
          -- eapply NoDup_firstn_skipn; [exact (bo_params _ _ Hbo) | exact Hx | exact Hy].
          -- apply bound_vars_bound in Hy. destruct (bo_bound _ _ Hbo x Hy) as [Hnp _].
             apply Hnp. eapply firstn_In; eauto.
          -- rewrite Hy in Hxr. unfold allocId in Hxr. lia.
          -- rewrite Hy in Hxr. unfold resultId in Hxr. lia.
          -- rewrite Hy in Hxr. unfold boxedId in Hxr. lia.
          -- apply idents_from_ge in Hy. lia.
      + exact Hbody_eq.
  Qed.

  (* The C function of a function of the program is related to it for up to [K] steps *)
  Lemma fun_related j f t xs e b fd :
    (j <= K)%nat ->
    find_def f fds = Some (t, xs, e) ->
    Genv.find_symbol ge f = Some b ->
    Genv.find_funct_ptr ge b = Some fd ->
    fun_rel j (Vfun rho0 fds f) fd.
  Proof.
    intros Hj Hfind Hb Hfd.
    destruct (prog_funs _ _ _ _ _ _ _ Hprog _ _ _ _ Hfind) as (b' & fn & Hb' & Hfn & Htf).
    assert (b' = b) by congruence. subst b'. assert (fd = Internal fn) by congruence. subst fd.
    destruct (translated_correct (Some f) xs e fn Htf (Hbodies _ _ _ _ Hfind)) as [Hty Hcall].
    { intros f0 Hf0. injection Hf0 as <-. eauto. }
    destruct j as [| j'].
    - apply fun_rel_0. exists t, xs, e. split; [exact Hfind | exact Hty].
    - apply fun_rel_S. exists t, xs, e. split; [exact Hfind |]. split; [exact Hty |].
      intros i vs rho' c v' tr ws tb tofs h fs m Hi Hset Hbstep Hc Hti Hrs Hargs.
      apply (Hcall i vs ws rho' c v' tr tb tofs h fs m); auto. lia.
  Qed.

  End Index.

  (* The functions of the program are related for every number of steps *)
  Lemma funs_related : forall K j f t xs e b fd,
      (j < K)%nat ->
      find_def f fds = Some (t, xs, e) ->
      Genv.find_symbol ge f = Some b ->
      Genv.find_funct_ptr ge b = Some fd ->
      fun_rel j (Vfun rho0 fds f) fd.
  Proof.
    induction K as [| K IH]; intros j f t xs e b fd Hj Hfind Hb Hfd; [lia |].
    apply (fun_related K IH j f t xs e b fd); auto. lia.
  Qed.

  (* The function of the main expression returns the layout of its value *)
  Lemma main_correct fn (c : fuel) v (tr : trace) :
    translate_function nparam prims cenv fenv tmp None [] main = Ret fn ->
    bstep_fuel cenv (def_funs fds fds rho0 rho0) main c (Res v) tr ->
    type_of_function fn = Tfunction [tptr tinfoT] tvalue cc_default /\
    forall k tb tofs h fs m,
      tinfo_ok h fs m tb tofs ->
      call_returns cenv ge gc_inv (fun _ _ => False) (fun h' m' w => val_rel k h' m' v w)
                   0 tb tofs fs h m (Internal fn) [Vptr tb (Ptrofs.repr tofs)].
  Proof.
    intros Htf Hbstep.
    assert (Hnone : forall f : var, @None var = Some f ->
                                    exists t, find_def f fds = Some (t, @nil var, main)).
    { intros f Hf0. discriminate. }
    split.
    - destruct (translated_correct 1 (funs_related 1) None [] main fn Htf Hmain Hnone) as [Hty _].
      exact Hty.
    - intros k tb tofs h fs m Hti.
      destruct (translated_correct (S (k + to_nat c)) (funs_related (S (k + to_nat c)))
                                   None [] main fn Htf Hmain Hnone) as [_ Hcall].
      specialize (Hcall (k + to_nat c)%nat [] [] (def_funs fds fds rho0 rho0) c v tr tb tofs h fs m).
      replace (k + to_nat c - to_nat c)%nat with k in Hcall by lia.
      rewrite firstn_nil in Hcall. apply Hcall; auto.
      + lia.
      + intros i w _ Hw. destruct i; discriminate.
  Qed.

End Correct.

(** * The hypotheses on the source program *)

Lemma functions_free e x : occurs_free_fundefs (functions e) x -> occurs_free e x.
Proof. destruct e; simpl; intros H; try solve [inv H]. now apply Free_Efun2. Qed.

Lemma functions_subterm e e' : dsubterm_fds_e e' (functions e) -> subterm_or_eq e' e.
Proof.
  destruct e; simpl; intros H; try solve [inv H]. apply rt_step. apply dsubterm_fds. exact H.
Qed.

Lemma find_def_subterm : forall fds f t ps e,
    find_def f fds = Some (t, ps, e) -> dsubterm_fds_e e fds.
Proof.
  induction fds as [g t0 ps0 e0 fds IH |]; simpl; intros f t ps e H; [| discriminate].
  destruct (M.elt_eq f g).
  - injection H as _ _ <-. apply dsubterm_cons.
  - apply dsubterm_cons_fds. eauto.
Qed.

Lemma main_exp_unique e : unique_bindings e -> unique_bindings (main_exp e).
Proof. destruct e; simpl; intros H; auto; now inv H. Qed.

Lemma main_exp_bound e x : bound_var (main_exp e) x -> bound_var e x.
Proof. destruct e; simpl; intros H; auto; now apply Bound_Efun2. Qed.

Lemma main_exp_free e x :
  occurs_free (main_exp e) x -> M.get x (fun_arities (functions e)) <> None \/ occurs_free e x.
Proof.
  destruct e; simpl; intros H; auto.
  destruct (M.get x (fun_arities f)) eqn:Hx; [left; congruence | right].
  apply Free_Efun1; [| exact H]. intros Hn. apply fun_arities_name in Hn. congruence.
Qed.

Lemma main_exp_subterm e : subterm_or_eq (main_exp e) e.
Proof. destruct e; simpl; try apply rt_refl. apply rt_step. apply dsubterm_fds2. Qed.

Lemma main_exp_disjoint e x :
  unique_bindings e -> bound_var (main_exp e) x -> ~ bound_var_fundefs (functions e) x.
Proof.
  destruct e; simpl; intros Hu Hb Hf; try solve [inv Hf].
  inv Hu.
  match goal with
  | [ H : Disjoint _ (bound_var _) (bound_var_fundefs _) |- _ ] => destruct H as [Hd]
  end.
  apply (Hd x). split; assumption.
Qed.

(* The evaluation of a program is the evaluation of its main expression *)
Lemma main_exp_step {fuel : Type} {Hf : @fuel_resource fuel} {trace : Type}
      {Ht : @trace_resource trace} cenv e (c : fuel) v (t : trace) :
  bstep_fuel cenv (M.empty val) e c (Res v) t ->
  exists (c' : fuel) (t' : trace),
    bstep_fuel cenv (def_funs (functions e) (functions e) (M.empty val) (M.empty val))
               (main_exp e) c' (Res v) t'.
Proof.
  intros H. destruct e; try (exists c, t; exact H).
  inv H. match goal with [ H0 : bstep _ _ (Efun _ _) _ _ _ |- _ ] => inv H0 end. eauto.
Qed.

Lemma fold_max_ge {A} (t : M.t A) acc :
  (acc <= M.fold (fun m x _ => Pos.max m x) t acc)%positive.
Proof.
  rewrite M.fold_spec. generalize (M.elements t). intros l. revert acc.
  induction l as [| p l IH]; intros acc; simpl; [lia |].
  eapply Pos.le_trans; [| apply IH]. lia.
Qed.

Section Source.

  Context (prims : M.t primitive) (cenv : ctor_env) (e : exp) (tmp : positive).

  Hypothesis Hids : forall x, bound_var e x -> (100 <= x)%positive.
  Hypothesis Hub : unique_bindings e.
  Hypothesis Hclosed : closed_exp e.
  Hypothesis Hnoprims : no_prims e.
  Hypothesis Hlimits : within_limits prims cenv e.
  Hypothesis Htmp : (max_var e 100 < tmp)%positive.

  Lemma source_ids x : bound_var e x -> (100 <= x < tmp)%positive.
  Proof.
    intros H. split; [auto |].
    pose proof (proj1 bound_var_leq_max_var_mut e x 100%positive H). lia.
  Qed.

  Lemma source_good e' : subterm_or_eq e' e -> good prims e'.
  Proof.
    intros H. split; [apply (proj1 (proj2 Hlimits e' H)) | apply (Hnoprims e' H)].
  Qed.

  (* What the proof uses of a function of the program *)
  Lemma source_fun_ok f t ps e' :
    find_def f (functions e) = Some (t, ps, e') ->
    Z.of_nat (length ps) <= max_args ->
    body_ok prims tmp (functions e) ps e'.
  Proof.
    intros Hfind Harity.
    pose proof (find_def_correct _ _ _ _ _ Hfind) as Hin.
    destruct (unique_bindings_fun_in_fundefs _ _ _ _ _ Hin (functions_unique _ Hub))
      as (Hue & Hfb & Hfx & [Hdn] & [Hdx] & [Hdbx] & Hnd).
    assert (Hsub : subterm_or_eq e' e).
    { apply functions_subterm. eapply find_def_subterm; eauto. }
    constructor.
    - exact Hue.
    - exact Hnd.
    - intros x Hx. split.
      + intros Hin'. apply (Hdbx x). split; assumption.
      + destruct (M.get x (fun_arities (functions e))) eqn:Hfx'; [| reflexivity]. exfalso.
        apply (Hdn x). split; [exact Hx |]. apply fun_arities_name. congruence.
    - intros x Hx. destruct (M.get x (fun_arities (functions e))) eqn:Hfx'; [| reflexivity].
      exfalso. apply (Hdx x). split; [exact Hx |]. apply fun_arities_name. congruence.
    - intros x Hx. pose proof (occurs_free_in_fun _ _ _ _ _ Hin x Hx) as Hu.
      inversion Hu as [? Hy | ? Hy]; subst; [left; exact Hy |].
      inversion Hy as [? Hz | ? Hz]; subst.
      + right. apply fun_arities_name. exact Hz.
      + exfalso. apply functions_free in Hz. apply (proj1 Hclosed) in Hz. inv Hz.
    - intros x Hx. apply source_ids. apply functions_bound.
      eapply fun_in_fundefs_bound_var_fundefs; [exact Hin |].
      destruct Hx; [right; right; assumption | right; left; assumption].
    - intros e0 He0. apply source_good. eapply rt_trans; [exact He0 | exact Hsub].
    - apply (proj2 (proj2 Hlimits e' Hsub)).
    - exact Harity.
  Qed.

  (* What the proof uses of the main expression *)
  Lemma source_main_ok : body_ok prims tmp (functions e) [] (main_exp e).
  Proof.
    constructor.
    - apply main_exp_unique. exact Hub.
    - constructor.
    - intros x Hx. split; [intros [] |].
      destruct (M.get x (fun_arities (functions e))) eqn:Hfx; [| reflexivity]. exfalso.
      eapply main_exp_disjoint; [exact Hub | exact Hx |].
      apply name_in_fundefs_bound_var_fundefs. apply fun_arities_name. congruence.
    - intros x [].
    - intros x Hx. right. destruct (main_exp_free _ _ Hx) as [Hn | Hfr]; [exact Hn |].
      apply (proj1 Hclosed) in Hfr. inv Hfr.
    - intros x [Hx | []]. apply source_ids. apply main_exp_bound. exact Hx.
    - intros e0 He0. apply source_good. eapply rt_trans; [exact He0 | apply main_exp_subterm].
    - apply (proj2 (proj2 Hlimits _ (main_exp_subterm e))).
    - simpl. unfold max_args. lia.
  Qed.

  Lemma source_fnames f :
    M.get f (fun_arities (functions e)) <> None -> (100 <= f < tmp)%positive.
  Proof.
    intros Hfn. apply source_ids. apply functions_bound.
    apply name_in_fundefs_bound_var_fundefs. apply fun_arities_name. exact Hfn.
  Qed.

End Source.

(** * The theorems *)

(* If the program [e] evaluates to [v], the call of its C function with a thread info
   returns the layout of [v]. This holds in every global environment [ge] that has the
   generated functions, for example that of a program linked with the collector. *)
Theorem program_correct
        {fuel : Type} {Hf : @fuel_resource fuel} {trace : Type} {Ht : @trace_resource trace} :
  forall nparam prims e cenv tmp ge gc_inv,
    program_ok nparam prims cenv tmp ge (functions e) (main_exp e) ->
    (max_var e 100 < tmp)%positive ->
    (* the source program *)
    (forall x, bound_var e x -> (100 <= x)%positive) ->
    distinct_ordinals cenv ->
    unique_bindings e ->
    closed_exp e ->
    no_prims e ->
    within_limits prims cenv e ->
    (* the runtime *)
    collector_ok cenv ge gc_inv ->
    is_ptr_spec ge ->
    forall v (c : fuel) (t : trace),
      bstep_fuel cenv (M.empty val) e c (Res v) t ->
      exists b fn,
        Genv.find_symbol ge bodyId = Some b /\
        Genv.find_funct_ptr ge b = Some (Internal fn) /\
        type_of_function fn = Tfunction [tptr tinfoT] tvalue cc_default /\
        forall k tb tofs h fs m,
          tinfo_ok cenv ge gc_inv h fs m tb tofs ->
          call_returns cenv ge gc_inv (fun _ _ => False)
                       (fun h' m' w => val_rel cenv ge nparam gc_inv k h' m' v w)
                       0 tb tofs fs h m
                       (Internal fn) [Vptr tb (Ptrofs.repr tofs)].
Proof.
  intros nparam prims e cenv tmp ge gc_inv Hprog Htmp
         Hids Hord Hub Hclosed Hnoprims Hlimits Hgc Hisptr v c t Hstep.
  destruct (main_exp_step _ _ _ _ _ Hstep) as (c' & t' & Hstep').
  assert (Htmp100 : (100 <= tmp)%positive).
  { pose proof (proj1 acc_leq_max_var_mut e 100%positive). lia. }
  destruct (prog_body _ _ _ _ _ _ _ Hprog) as (b & fn & Hb & Hfn & Htf).
  exists b, fn. split; [exact Hb |]. split; [exact Hfn |].
  (* the hypotheses on the functions *)
  assert (Hbodies : forall f t0 ps e',
             find_def f (functions e) = Some (t0, ps, e') ->
             body_ok prims tmp (functions e) ps e').
  { intros f t0 ps e' Hfind. eapply source_fun_ok; eauto.
    destruct (prog_funs _ _ _ _ _ _ _ Hprog _ _ _ _ Hfind) as (b' & fn' & _ & _ & Htf').
    apply translate_function_inv in Htf'. exact (proj1 Htf'). }
  assert (Hmain : body_ok prims tmp (functions e) [] (main_exp e)).
  { eapply source_main_ok; eauto. }
  assert (Hfnames : forall f, M.get f (fun_arities (functions e)) <> None ->
                              (100 <= f < tmp)%positive).
  { intros f Hfn0. eapply source_fnames; eauto. }
  exact (main_correct nparam prims cenv tmp (functions e) (main_exp e) (M.empty val) ge gc_inv
                      Hprog Hgc Hisptr Hord (proj1 Hlimits) Hbodies Hmain Hfnames Htmp100
                      fn c' v t' Htf Hstep').
Qed.

(* The program of [compile], with the definitions of the structs, has the generated
   functions. Its collector is an external function. *)
Lemma compile_program_ok body_name nparam prims e cenv nenv names header prog p :
  compile body_name nparam prims e cenv nenv = Ret (names, header, prog) ->
  make_program composites (prog_defs prog) = Ret p ->
  (forall x, bound_var e x -> (100 <= x)%positive) ->
  unique_bindings e ->
  exists tmp,
    (max_var e 100 < tmp)%positive /\
    program_ok nparam prims cenv tmp (globalenv p) (functions e) (main_exp e).
Proof.
  intros Hcomp Hmk Hids Hub.
  unfold compile in Hcomp. rewrite ptr64 in Hcomp. cbv beta iota zeta in Hcomp.
  bind_inv_as Hcomp defs Hdefs. bind_inv_as Hcomp prog' Hprog'. bind_inv_as Hcomp header' Hheader.
  apply Ret_inj in Hcomp. assert (Hprog_eq : prog' = prog) by congruence. subst prog'.
  destruct (make_program_inv _ _ _ Hprog') as [Hdefs_eq _]. rewrite Hdefs_eq in Hmk.
  match type of Hdefs with
  | translate_program _ _ _ ?x _ = _ => remember x as tmp eqn:Htmp_def
  end.
  exists tmp. split.
  - rewrite Htmp_def. apply Pos.lt_succ_r.
    eapply Pos.le_trans; [| apply fold_max_ge]. apply fold_max_ge.
  - exact (translate_program_ok nparam prims cenv tmp e defs p Hdefs Hmk Hub Hids).
Qed.

(* The theorem for the program of [compile] *)
Theorem compile_correct
        {fuel : Type} {Hf : @fuel_resource fuel} {trace : Type} {Ht : @trace_resource trace} :
  forall body_name nparam prims e cenv nenv names header prog p gc_inv,
    compile body_name nparam prims e cenv nenv = Ret (names, header, prog) ->
    make_program composites (prog_defs prog) = Ret p ->
    let ge := globalenv p in
    (* the source program *)
    (forall x, bound_var e x -> (100 <= x)%positive) ->
    distinct_ordinals cenv ->
    unique_bindings e ->
    closed_exp e ->
    no_prims e ->
    within_limits prims cenv e ->
    (* the runtime *)
    collector_ok cenv ge gc_inv ->
    is_ptr_spec ge ->
    forall v (c : fuel) (t : trace),
      bstep_fuel cenv (M.empty val) e c (Res v) t ->
      exists b fn,
        Genv.find_symbol ge bodyId = Some b /\
        Genv.find_funct_ptr ge b = Some (Internal fn) /\
        type_of_function fn = Tfunction [tptr tinfoT] tvalue cc_default /\
        forall k tb tofs h fs m,
          tinfo_ok cenv ge gc_inv h fs m tb tofs ->
          call_returns cenv ge gc_inv (fun _ _ => False)
                       (fun h' m' w => val_rel cenv ge nparam gc_inv k h' m' v w)
                       0 tb tofs fs h m
                       (Internal fn) [Vptr tb (Ptrofs.repr tofs)].
Proof.
  intros body_name nparam prims e cenv nenv names header prog p gc_inv Hcomp Hmk ge
         Hids Hord Hub Hclosed Hnoprims Hlimits Hgc Hisptr v c t Hstep.
  destruct (compile_program_ok _ _ _ _ _ _ _ _ _ _ Hcomp Hmk Hids Hub) as (tmp & Htmp & Hprog).
  eapply program_correct; eauto.
Qed.
