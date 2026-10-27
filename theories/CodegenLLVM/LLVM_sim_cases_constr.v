(** * The [Econstr] case of [LLVM_sim.sim_exp].

    [sim_case_constr] proves [sim_stmt rho (Econstr x t ys e') v] from the
    induction hypothesis [sim_stmt (M.set x (Vconstr t vs) rho) e' v]. *)

From Stdlib Require Import ZArith NArith List Lia String Program Morphisms Classical_Prop.
From ITree Require Import ITree Eq.Eqit Interp.InterpFacts Interp.RecursionFacts.
From ExtLib Require Import Structures.Monads.
From CertiRocq.LambdaANF Require Import term term_util eval identifiers Ensembles_util set_util.
From CertiRocq.Common Require Import AstCommon.
From CertiRocq.CodegenLLVM Require Import LambdaANF_to_LLVM Flatten
     LambdaANF_to_LLVM_statement LLVM_interp_lemmas LLVM_call_lemmas LLVM_convert
     LLVM_exp_lemmas LLVM_mem_lemmas LLVM_emit_syntax LLVM_emit_facts.
From CertiRocq.CodegenLLVM Require Flatten_sem LLVM_instr_lemmas LLVM_sim.
From Vellvm Require Import Semantics.Operations.Gep.
From Vellvm Require Import
  Utils Syntax Params
  Interfaces.Memory Implementations.Memory
  Semantics.DynamicValues Semantics.LLVMEvents Semantics.Denotation
  Semantics.InterpretationStack Semantics.TopLevel Handlers.
Import ListNotations.
Import MonadNotation.
Open Scope monad_scope.
Open Scope Z_scope.
Open Scope list_scope.
Unset Implicit Arguments.
Set Bullet Behavior "Strict Subproofs".

(* ------------------------------------------------------------------ *)
(** ** Syntactic facts about binders *)

Lemma disj_elim {A} (S1 S2 : Ensembles.Ensemble A) x :
  Ensembles.Disjoint A S1 S2 -> S1 x -> S2 x -> False.
Proof. intros [H] H1 H2. apply (H x). constructor; assumption. Qed.

Lemma dsubterm_bound_var e e' x :
  dsubterm_e e e' -> bound_var e x -> bound_var e' x.
Proof.
  intros H Hx. destruct H; eauto.
  all: try (eapply Bound_Ecase; eauto; fail).
  all: apply Bound_Efun1; induction H; eauto.
Qed.

Lemma subterm_or_eq_bound_var e e' x :
  subterm_or_eq e e' -> bound_var e x -> bound_var e' x.
Proof.
  intros H. induction H as [a b H| a | a b c _ IH1 _ IH2]; auto.
  intros Hx. eapply dsubterm_bound_var; eauto.
Qed.

Lemma fun_ids_bound fds f : In f (fun_ids fds) -> bound_var_fundefs fds f.
Proof.
  induction fds as [g t ys e fds IH|]; cbn; [|tauto].
  intros [<-|H]; [apply Bound_Fcons1; left; constructor|apply Bound_Fcons2, IH, H].
Qed.

(** Variables bound inside a function body are not function names. *)
Lemma body_not_fun fds e x :
  unique_bindings_fundefs fds -> dsubterm_fds_e e fds -> bound_var e x -> ~ In x (fun_ids fds).
Proof.
  induction 1 as [f tau ys e0 defs Hf Hfd _ _ Hdis _ _ _ _ IH|]; intros Hd Hx Hin;
    [|inversion Hd].
  cbn in Hin. inversion Hd; subst.
  - destruct Hin as [<-|Hin]; [exact (Hf Hx)|].
    eapply disj_elim; [exact Hdis|exact Hx|apply fun_ids_bound, Hin].
  - destruct Hin as [<-|Hin].
    + apply Hfd. match goal with H : dsubterm_fds_e _ defs |- _ => clear -H Hx; induction H; eauto end.
    + eapply IH; eauto.
Qed.


Lemma subterm_or_eq_inv e P :
  subterm_or_eq e P -> e = P \/ exists e1, dsubterm_e e1 P /\ subterm_or_eq e e1.
Proof.
  intros H. apply Operators_Properties.clos_rt_rtn1 in H.
  destruct H as [|e1 e2 H Hr]; [left; reflexivity|right].
  exists e1. split; [exact H|]. apply Operators_Properties.clos_rtn1_rt. exact Hr.
Qed.

Lemma bound_not_fun fds main e x :
  unique_bindings (Efun fds main) -> subterm_or_eq e (Efun fds main) ->
  (forall fds' e'', e <> Efun fds' e'') -> bound_var e x -> ~ In x (fun_ids fds).
Proof.
  intros Hu Hs Hne Hx Hin. inversion Hu as [| | | | |defs e0 Hum Huf Hdis| | | |]; subst.
  destruct (subterm_or_eq_inv _ _ Hs) as [->|(e1 & Hd & Hs1)]; [eapply Hne; reflexivity|].
  pose proof (subterm_or_eq_bound_var _ _ _ Hs1 Hx) as Hx1.
  inversion Hd; subst.
  - eapply body_not_fun; eauto.
  - eapply disj_elim; [exact Hdis|exact Hx1|apply fun_ids_bound, Hin].
Qed.

Lemma is_fun_false fs x : ~ In x fs -> is_fun fs x = false.
Proof.
  intros H. unfold is_fun. apply Bool.not_true_iff_false. intros E.
  apply existsb_exists in E. destruct E as (y & Hy & E). apply Pos.eqb_eq in E. subst. auto.
Qed.

Lemma is_fun_true fs x : is_fun fs x = true -> In x fs.
Proof.
  intros E. apply existsb_exists in E. destruct E as (y & Hy & E). apply Pos.eqb_eq in E. subst. auto.
Qed.

Lemma subterm_constr x t ys e' P :
  subterm_or_eq (Econstr x t ys e') P -> subterm_or_eq e' P.
Proof. intros H. eapply Relation_Operators.rt_trans; [apply Relation_Operators.rt_step; constructor|exact H]. Qed.

Lemma disjoint_constr x t ys e' :
  unique_bindings (Econstr x t ys e') ->
  Ensembles.Disjoint _ (bound_var (Econstr x t ys e')) (occurs_free (Econstr x t ys e')) ->
  Ensembles.Disjoint _ (bound_var e') (occurs_free e').
Proof.
  intros Hu Hd. inversion Hu; subst. constructor. intros y [y' Hb Hf].
  destruct (Pos.eq_dec x y') as [<-|Hne]; [contradiction|].
  eapply disj_elim; [exact Hd|apply Bound_Econstr2, Hb|apply Free_Econstr2; auto].
Qed.

Lemma x_not_free x t ys e' :
  Ensembles.Disjoint _ (bound_var (Econstr x t ys e')) (occurs_free (Econstr x t ys e')) ->
  ~ occurs_free (Econstr x t ys e') x.
Proof. intros Hd Hf. eapply disj_elim; [exact Hd|apply Bound_Econstr1|exact Hf]. Qed.

(* ------------------------------------------------------------------ *)
(** ** The translation only reads the SSA environment at the variables of
    the expression *)

Definition FB (e : term.exp) (y : var) : Prop := occurs_free e y \/ bound_var e y.

Lemma store_fields_ext fs env env' vp i ys :
  (forall y, In y ys -> env y = env' y) -> store_fields fs env vp i ys = store_fields fs env' vp i ys.
Proof.
  revert i. induction ys as [|y ys IH]; intros i H; [reflexivity|]. cbn [store_fields].
  unfold gvar, nvar. rewrite (H y (or_introl eq_refl)), IH; [reflexivity|]. intros; apply H; right; auto.
Qed.

Lemma spill_code_ext env env' rp aty i rs :
  (forall y, In y rs -> env y = env' y) -> spill_code env rp aty i rs = spill_code env' rp aty i rs.
Proof.
  revert i. induction rs as [|y rs IH]; intros i H; [reflexivity|]. cbn [spill_code].
  unfold nvar. rewrite (H y (or_introl eq_refl)), IH; [reflexivity|]. intros; apply H; right; auto.
Qed.

Lemma phi_list_ext env env' s c g i rs :
  (forall y, In y rs -> env y = env' y) -> phi_list env s c g i rs = phi_list env' s c g i rs.
Proof.
  revert i. induction rs as [|y rs IH]; intros i H; [reflexivity|]. cbn [phi_list].
  unfold nvar. rewrite (H y (or_introl eq_refl)), IH; [reflexivity|]. intros; apply H; right; auto.
Qed.

Lemma call_args_ext fs env env' ys :
  (forall y, In y ys -> env y = env' y) -> call_args fs env ys = call_args fs env' ys.
Proof.
  intros H. unfold call_args. f_equal. apply map_ext_in. intros y Hy. unfold gvar, nvar. rewrite H; auto.
Qed.

Lemma env_set_list_ext env env' vs rs y :
  length rs = length vs ->
  (In y vs \/ env y = env' y) -> env_set_list env vs rs y = env_set_list env' vs rs y.
Proof.
  revert rs. induction vs as [|v vs IH]; intros rs L H; destruct rs as [|r rs]; cbn [env_set_list];
    try discriminate; [destruct H as [[]|H]; exact H|].
  unfold env_set. destruct (Pos.eqb y v) eqn:E; [reflexivity|].
  apply IH; [cbn in L; lia|]. destruct H as [[<-|Hin]|H]; auto. rewrite Pos.eqb_refl in E. discriminate.
Qed.

Lemma arm_loop_ext (tr1 tr2 : term.exp -> positive -> list (LLVMAst.block typ) * positive) go ga arms fr :
  (forall c e fr, In (c, e) arms -> tr1 e fr = tr2 e fr) ->
  arm_loop_d tr1 go ga arms fr = arm_loop_d tr2 go ga arms fr.
Proof.
  revert fr. induction arms as [|[c e] arms IH]; intros fr H; [reflexivity|].
  simpl. rewrite (H c e fr (or_introl eq_refl)). destruct (tr2 e fr) as [ab fr1].
  rewrite IH; [reflexivity|]. intros; eapply H; right; eauto.
Qed.

Lemma FB_constr x t ys e y : FB e y -> FB (Econstr x t ys e) y.
Proof.
  intros [Hf|Hb]; [|right; apply Bound_Econstr2, Hb].
  destruct (Pos.eq_dec x y) as [<-|Hne]; [right; constructor|left; apply Free_Econstr2; auto].
Qed.
Lemma FB_proj x tg n z e y : FB e y -> FB (Eproj x tg n z e) y.
Proof.
  intros [Hf|Hb]; [|right; apply Bound_Eproj2, Hb].
  destruct (Pos.eq_dec x y) as [<-|Hne]; [right; constructor|left; apply Free_Eproj2; auto].
Qed.
Lemma FB_letapp x f ft ys e y : FB e y -> FB (Eletapp x f ft ys e) y.
Proof.
  intros [Hf|Hb]; [|right; apply Bound_Eletapp2, Hb].
  destruct (Pos.eq_dec x y) as [<-|Hne]; [right; constructor|left; apply Free_Eletapp2; auto].
Qed.
Lemma FB_prim_val x p e y : FB e y -> FB (Eprim_val x p e) y.
Proof.
  intros [Hf|Hb]; [|right; apply Bound_Eprim_val2, Hb].
  destruct (Pos.eq_dec x y) as [<-|Hne]; [right; constructor|left; apply Free_Eprim_val; auto].
Qed.
Lemma FB_prim x p ys e y : FB e y -> FB (Eprim x p ys e) y.
Proof.
  intros [Hf|Hb]; [|right; apply Bound_Eprim2, Hb].
  destruct (Pos.eq_dec x y) as [<-|Hne]; [right; constructor|left; apply Free_Eprim2; auto].
Qed.
Lemma FB_fun fds e y : FB e y -> FB (Efun fds e) y.
Proof.
  intros [Hf|Hb]; [|right; apply Bound_Efun2, Hb].
  destruct (Decidable_name_in_fundefs fds) as [Dec]. destruct (Dec y) as [Hn|Hn].
  - right. apply Bound_Efun1. apply name_in_fundefs_bound_var_fundefs. exact Hn.
  - left. apply Free_Efun1; auto.
Qed.
Lemma FB_case x arms c e y : In (c, e) arms -> FB e y -> FB (Ecase x arms) y.
Proof.
  intros Hin [Hf|Hb]; [left|right; eapply Bound_Ecase; eauto].
  induction arms as [|[c' e'] arms IH]; [destruct Hin|].
  destruct Hin as [E|Hin]; [injection E as -> ->; apply Free_Ecase2, Hf|apply Free_Ecase3, IH, Hin].
Qed.

Section TrExt.
  Variables (go ga : ctor_tag -> N) (po : positive -> option (string * bool)) (fs : list positive).
  Notation tr := (translate_cfg go ga po fs).

  Lemma tr_env_ext e : forall env env' chunk fresh,
    (forall y, FB e y -> env y = env' y) -> tr env chunk e fresh = tr env' chunk e fresh.
  Proof.
    induction e as [x t ys e IH|y arms IH|x tg n z e IH|x f ft ys e IH|fds e IH|f ft ys|x pv e IH|x p ys e IH|x]
      using exp_ind_nested; intros env env' chunk fresh H.
    - destruct ys as [|y0 ys0] eqn:Eys.
      + cbn [translate_cfg]. rewrite (IH env env'); [reflexivity|]. intros; apply H, FB_constr; auto.
      + subst ys. set (ys := y0 :: ys0).
        assert (Hys : forall y, In y ys -> env y = env' y) by (intros; apply H; left; constructor; auto).
        destruct (N.leb (hd_nwords ys) chunk) eqn:Hl.
        * destruct (tr env (chunk - hd_nwords ys) e (Pos.succ fresh)) as [blks f'] eqn:E.
          rewrite (tr_constr_member go ga po fs env chunk x t ys e fresh blks f'); [|discriminate|exact Hl|exact E].
          rewrite (IH env env') in E by (intros; apply H, FB_constr; auto).
          rewrite (tr_constr_member go ga po fs env' chunk x t ys e fresh blks f'); [|discriminate|exact Hl|exact E].
          unfold alloc_code. rewrite (store_fields_ext fs env env'); auto.
        * destruct (tr (hd_env fs env fresh x ys e) (chunk_words e) e (Pos.succ fresh)) as [blks f0] eqn:E.
          rewrite (tr_constr_head go ga po fs env chunk x t ys e fresh blks f0); [|discriminate|exact Hl|exact E].
          assert (Hroot : forall r, In r (hd_roots fs x ys e) -> env r = env' r).
          { intros r Hr. apply hd_roots_spec in Hr. destruct Hr as [_ [[Hr Hne]|Hr]]; apply H; left.
            - apply Free_Econstr2; auto.
            - constructor; auto. }
          assert (Henv : forall r, FB e r -> hd_env fs env fresh x ys e r = hd_env fs env' fresh x ys e r).
          { intros r Hr. unfold hd_env, safepoint_env. apply env_set_list_ext; [rewrite length_map, length_seq; reflexivity|].
            destruct (in_dec Pos.eq_dec r (hd_roots fs x ys e)) as [Hi|Hi]; [left; exact Hi|right].
            apply H, FB_constr, Hr. }
          rewrite (IH _ _ _ _ Henv) in E.
          rewrite (tr_constr_head go ga po fs env' chunk x t ys e fresh blks f0); [|discriminate|exact Hl|exact E].
          unfold hd_gc_blk, hd_alloc_blk. rewrite (spill_code_ext env env'), (phi_list_ext env env') by exact Hroot.
          assert (Hst : forall y, In y ys -> hd_env fs env fresh x ys e y = hd_env fs env' fresh x ys e y).
          { intros y Hy. unfold hd_env, safepoint_env. apply env_set_list_ext; [rewrite length_map, length_seq; reflexivity|].
            destruct (in_dec Pos.eq_dec y (hd_roots fs x ys e)) as [Hi|Hi]; [left; exact Hi|right; auto]. }
          unfold alloc_code. rewrite (store_fields_ext fs _ _ _ _ _ Hst). reflexivity.
    - rewrite !tr_case_unfold.
      rewrite (arm_loop_ext (fun ae fr => tr env 0%N ae fr) (fun ae fr => tr env' 0%N ae fr)).
      + destruct (arm_loop_d _ go ga arms fresh) as [[ab ae] f1]. cbn [case_result].
        unfold case_test_blk, case_unboxed_blk, case_boxed_blk, load_header, nvar.
        rewrite (H y) by (left; constructor). reflexivity.
      + intros c e fr Hin. rewrite Forall_forall in IH. apply (IH (c, e) Hin).
        intros r Hr. apply H. eapply FB_case; eauto.
    - destruct (tr env chunk e fresh) as [blks f'] eqn:E.
      rewrite (tr_proj go ga po fs env chunk x tg n z e fresh blks f' E).
      rewrite (IH env env') in E by (intros; apply H, FB_proj; auto).
      rewrite (tr_proj go ga po fs env' chunk x tg n z e fresh blks f' E).
      unfold load_field, gep_field, nvar. rewrite (H z) by (left; constructor). reflexivity.
    - destruct (tr (la_env fs env fresh x e) 0%N e (Pos.succ fresh)) as [blks f'] eqn:E.
      rewrite (tr_letapp go ga po fs env chunk x f ft ys e fresh blks f' E).
      assert (Hroot : forall r, In r (la_roots fs x e) -> env r = env' r).
      { intros r Hr. apply la_roots_spec in Hr. destruct Hr as (_ & Hr & Hne). apply H. left.
        apply Free_Eletapp2; auto. }
      rewrite (IH _ (la_env fs env' fresh x e)) in E.
      + rewrite (tr_letapp go ga po fs env' chunk x f ft ys e fresh blks f' E).
        unfold la_code. rewrite (spill_code_ext env env') by exact Hroot.
        rewrite (call_args_ext fs env env') by (intros; apply H; left; constructor; right; auto).
        unfold gcallee, nvar. rewrite (H f) by (left; constructor; left; auto). reflexivity.
      + intros r Hr. unfold la_env. apply env_set_list_ext; [rewrite length_map, length_seq; reflexivity|].
        destruct (in_dec Pos.eq_dec r (la_roots fs x e)) as [Hi|Hi]; [left; exact Hi|right].
        apply H, FB_letapp, Hr.
    - rewrite !tr_fun. apply IH. intros; apply H, FB_fun; auto.
    - cbn [translate_cfg]. rewrite (call_args_ext fs env env') by (intros; apply H; left; constructor; auto).
      unfold gcallee, nvar. rewrite (H f) by (left; constructor). reflexivity.
    - cbn [translate_cfg]. rewrite (IH env env'); [reflexivity|]. intros; apply H, FB_prim_val; auto.
    - cbn [translate_cfg]. rewrite (IH env env') by (intros; apply H, FB_prim; auto).
      destruct (tr env' 0%N e fresh). f_equal. f_equal. f_equal. f_equal.
      destruct (po p) as [[nm b]|]; [destruct b|]; f_equal; f_equal;
        try (apply map_ext_in; intros y Hy; unfold gvar, nvar; rewrite (H y) by (left; constructor; auto); reflexivity).
      f_equal. apply map_ext_in; intros y Hy; unfold gvar, nvar; rewrite (H y) by (left; constructor; auto); reflexivity.
    - cbn [translate_cfg]. unfold gvar, nvar. rewrite (H x) by (left; constructor). reflexivity.
  Qed.
End TrExt.

(* ------------------------------------------------------------------ *)
(** ** Stepping through flattened code, backwards *)

Section Stepping.
  Variable ctx : CallE ~> itree (CallE +' MCFGEtop).
  Variable va : option ptr.
  Variable g : global_env.
  Notation RUN t s := (Flatten_sem.run ctx t s).
  Notation R := ((block_id * block_id) + dvalue)%type.

  Definition closedP (P : MCFGbot (Res R) -> Prop) : Prop :=
    forall t t', t ≈ t' -> P t -> P t'.

  (** [P] holds of the flattened tail of [l; tmt] from every frame agreeing
      with [sf] off the flattening names [[lo, c)]. *)
  Definition fgoal (P : MCFGbot (Res R) -> Prop) (lo : positive) (l : code dtyp)
             (tmt : instr_id * terminator dtyp * list (metadata dtyp)) (K : block_id + dvalue -> CFGtop R)
             (st : state) (sf : stack_frame) (stk : stack) : Prop :=
    forall c sf', (lo <= c)%positive -> Flatten_sem.agree_except lo c sf sf' ->
      P (RUN (Flatten_sem.flat_tail va l tmt c K) (st, ((sf', stk), g))).

  Lemma fgoal_instr P lo i l tmt K st sf stk st1 sf1 :
    closedP P -> Flatten_sem.instr_ok i -> Flatten_sem.instr_evals st sf stk g i ->
    LLVM_instr_lemmas.runs ctx (denote_instr i va) (st, ((sf, stk), g)) (st1, ((sf1, stk), g)) tt ->
    fgoal P lo l tmt K st1 sf1 stk -> fgoal P lo (i :: l) tmt K st sf stk.
  Proof.
    intros HP Hok Hev Hr H c sf' Hlo Hag.
    destruct (Flatten_sem.flat_tail_instr ctx va lo c i l tmt K st sf sf' stk g st1 sf1 stk g
                Hok Hev Hlo Hag Hr) as (Hc & sf1' & Hag1 & E).
    eapply HP; [symmetry; exact E|]. apply H; [lia|exact Hag1].
  Qed.

  Lemma fgoal_oom P lo i l tmt K st sf stk :
    (forall t, ends_in_oom t -> P t) -> Flatten_sem.instr_ok i -> Flatten_sem.instr_evals st sf stk g i ->
    LLVM_instr_lemmas.oom ctx (denote_instr i va) (st, ((sf, stk), g)) ->
    fgoal P lo (i :: l) tmt K st sf stk.
  Proof.
    intros HP Hok Hev Ho c sf' Hlo Hag. apply HP.
    eapply Flatten_sem.flat_tail_instr_oom; eauto.
  Qed.

  (** The terminator. *)
  Lemma fgoal_term P lo tid tm tmd K st sf stk st1 sf1 r :
    closedP P -> Flatten_sem.term_ok tm -> Flatten_sem.term_evals st sf stk g tm ->
    LLVM_instr_lemmas.runs ctx (denote_terminator (tid, tm, tmd)) (st, ((sf, stk), g)) (st1, ((sf1, stk), g)) r ->
    (forall sf1', Flatten_sem.agree_noflat sf1 sf1' -> P (RUN (K r) (st1, ((sf1', stk), g)))) ->
    fgoal P lo [] (tid, tm, tmd) K st sf stk.
  Proof.
    intros HP Hok Hev Hr H c sf' Hlo Hag.
    destruct (Flatten_sem.flat_tail_term ctx va lo c tid tm tmd K st sf sf' stk g st1 sf1 stk g r
                Hok Hev Hlo Hag Hr) as (_ & sf1' & Hag1 & E).
    eapply HP; [symmetry; exact E|]. apply H. eapply Flatten_sem.agree_except_noflat'; eauto.
  Qed.

  (** Entry into the flattened tail of a block. *)
  Lemma tail_of_flat B b c s :
    RUN (LLVM_sim.tail_of va B (LLVM_sim.flatB b c)) s
    ≈ RUN (Flatten_sem.flat_tail va (blk_code b) (blk_term b) c (LLVM_sim.continue va B (blk_id b))) s.
  Proof.
    unfold LLVM_sim.tail_of, LLVM_sim.flatB. rewrite Flatten_sem.flat_blockP_id.
    apply Flatten_sem.flat_block_tail.
  Qed.
End Stepping.

Lemma cblock_prepend x (b : LLVMAst.block typ) :
  blk_id (cblock (mk_block (blk_id b) (blk_phis b) (x ++ blk_code b)%list (blk_term b) (blk_comments b))) = blk_id (cblock b) /\
  blk_code (cblock (mk_block (blk_id b) (blk_phis b) (x ++ blk_code b)%list (blk_term b) (blk_comments b))) =
    (ccode x ++ blk_code (cblock b))%list /\
  blk_term (cblock (mk_block (blk_id b) (blk_phis b) (x ++ blk_code b)%list (blk_term b) (blk_comments b))) = blk_term (cblock b).
Proof. rewrite !cblock_eq. cbn. rewrite ccode_app. auto. Qed.

Lemma cblock_id (b : LLVMAst.block typ) : blk_id (cblock b) = blk_id b.
Proof. rewrite cblock_eq. reflexivity. Qed.

Lemma ccode_single id i : ccode [(id, i, [])] = [(id, cinstr i, [])].
Proof. rewrite ccode_cons. reflexivity. Qed.

(* ------------------------------------------------------------------ *)
(** ** Restricting the SSA environment to the free variables *)

Definition restrict (env : nenv) (e : term.exp) : nenv :=
  fun y => if in_dec Pos.eq_dec y (PS.elements (exp_fv e)) then env y else Raw (Zpos y).

Lemma restrict_fv env e y : occurs_free e y -> restrict env e y = env y.
Proof.
  intros H. unfold restrict. destruct (in_dec _ _ _) as [_|Hn]; [reflexivity|].
  exfalso. apply Hn, In_elements_fv, H.
Qed.

Lemma restrict_nfv env e y : ~ occurs_free e y -> restrict env e y = Raw (Zpos y).
Proof.
  intros H. unfold restrict. destruct (in_dec _ _ _) as [Hi|_]; [|reflexivity].
  exfalso. apply H, In_elements_fv, Hi.
Qed.

(* ------------------------------------------------------------------ *)
(** ** Memory helpers *)

Lemma reads_ptr_wild st p q : reads_ptr st p q -> ptr_provenance q = wildcard_prov.
Proof.
  intros (st' & H). apply read_dvalue_runs in H. destruct H as (_ & ptrs & bs & _ & _ & E).
  unfold MemoryBytes.memory_bytes_to_dvalue in E. cbn [MemoryBytes.memory_bytes_to_dvalue_base] in E.
  unfold MemoryBytes.absorb_pois in E.
  destruct (map_monad _ bs) as [ | | | [|zs]] eqn:Em; cbn in E; try discriminate.
  destruct (IPtrFinite.from_Z_bits _); cbn in E; try discriminate.
  injection E as <-. reflexivity.
Qed.

Lemma header_lor (a o : nat) :
  (o < 1024)%nat -> Z.of_nat (Nat.lor (Nat.shiftl a 10) o) = Z.of_nat a * 1024 + Z.of_nat o.
Proof.
  intros Ho.
  assert (Hl : Nat.land (Nat.shiftl a 10) o = 0%nat).
  { apply Nat.bits_inj. intros i. rewrite Nat.land_spec, Nat.bits_0.
    destruct (Nat.lt_ge_cases i 10) as [Hi|Hi].
    - rewrite Nat.shiftl_spec_low by exact Hi. reflexivity.
    - assert (Hb : Nat.testbit o i = false).
      { apply Nat.testbit_false. rewrite Nat.div_small; [reflexivity|]. eapply Nat.lt_le_trans; [exact Ho|].
        change 1024%nat with (2 ^ 10)%nat. apply Nat.pow_le_mono_r; lia. }
      rewrite Hb. apply Bool.andb_false_r. }
  rewrite <- Nat.lxor_lor by exact Hl. rewrite <- Nat.add_nocarry_lxor by exact Hl.
  rewrite Nat.shiftl_mul_pow2. change (2 ^ 10)%nat with 1024%nat. lia.
Qed.


Lemma ccode_alloc_code go ga fs env fresh x t ys :
  ccode (alloc_code go ga fs env fresh x t ys) =
  (IId (ssname fresh 7), INSTR_Load (DTYPE_Pointer : dtyp) ((DTYPE_Pointer : dtyp), cexp (gep_tinfo 0)) [], [])
  :: (IVoid 6%Z, INSTR_Store ((DTYPE_I 64 : dtyp), cexp (header_word go ga t))
                   ((DTYPE_Pointer : dtyp), cexp (gep_at (EXP_Ident (ID_Local (ssname fresh 7))) 0)) [], [])
  :: (IId (ssname fresh 8), INSTR_Op (cexp (gep_at (EXP_Ident (ID_Local (ssname fresh 7))) 1)), [])
  :: ccode (store_fields fs env (EXP_Ident (ID_Local (ssname fresh 8))) 0 ys)
  ++ (IId (Raw (Zpos x)), INSTR_Op (OP_Conversion (CONV_Impure Ptrtoint) (DTYPE_Pointer : dtyp)
                                      (EXP_Ident (ID_Local (ssname fresh 8))) (DTYPE_I 64 : dtyp)), [])
  :: (IId (ssname fresh 9), INSTR_Op (cexp (gep_at (EXP_Ident (ID_Local (ssname fresh 7))) (hd_nwords ys))), [])
  :: (IVoid 7%Z, INSTR_Store ((DTYPE_Pointer : dtyp), EXP_Ident (ID_Local (ssname fresh 9)))
                   ((DTYPE_Pointer : dtyp), cexp (gep_tinfo 0)) [], [])
  :: [].
Proof.
  unfold alloc_code. rewrite !ccode_cons, ccode_app, !ccode_cons, ccode_nil.
  rewrite !cinstr_Load, !cinstr_Store, !cinstr_Op. unfold ctexp. cbn [fst snd].
  rewrite cexp_Conversion, !cexp_Ident, cty_ptr, cty_val. reflexivity.
Qed.

Section StoreHelpers.
  Variable ctx : CallE ~> itree (CallE +' MCFGEtop).
  Variable va : option ptr.
  Variable g : global_env.

  Definition wpost (st st' : state) (qs : list ptr) : Prop :=
    LLVM_instr_lemmas.writes_post st st' qs /\ (forall a, aid_at st' a = aid_at st a).

  Lemma store_word_aid n ev ep w q st sf stk :
    exp_eval st sf stk g (Some (DTYPE_I 64 : dtyp)) ev (I64 w) ->
    exp_eval st sf stk g (Some (DTYPE_Pointer : dtyp)) ep (Ptr q) ->
    writable_word st q ->
    exists st',
      LLVM_instr_lemmas.runs ctx (denote_instr (IVoid n, INSTR_Store ((DTYPE_I 64 : dtyp), ev) ((DTYPE_Pointer : dtyp), ep) [], []) va)
           (st, ((sf, stk), g)) (st', ((sf, stk), g)) tt /\
      reads_word st' q w /\ LLVM_instr_lemmas.write_post st st' q /\ (forall a, aid_at st' a = aid_at st a).
  Proof.
    intros Hv Hp Hw. destruct (Hw w) as (st' & Hrun & Hr).
    exists st'. split; [eapply LLVM_instr_lemmas.instr_store_run; eauto|]. split; [exact Hr|].
    split; [eapply LLVM_instr_lemmas.write_dvalue_post; [apply sizeof_i64|exact Hrun]|].
    apply write_dvalue_runs in Hrun. tauto.
  Qed.

  Lemma store_ptr_aid n ev ep p' q st sf stk :
    exp_eval st sf stk g (Some (DTYPE_Pointer : dtyp)) ev (Ptr p') ->
    exp_eval st sf stk g (Some (DTYPE_Pointer : dtyp)) ep (Ptr q) ->
    writable_word st q ->
    exists st' p'',
      LLVM_instr_lemmas.runs ctx (denote_instr (IVoid n, INSTR_Store ((DTYPE_Pointer : dtyp), ev) ((DTYPE_Pointer : dtyp), ep) [], []) va)
           (st, ((sf, stk), g)) (st', ((sf, stk), g)) tt /\
      reads_ptr st' q p'' /\ ptr_to_int p'' = ptr_to_int p' /\ ptr_provenance p'' = wildcard_prov /\
      LLVM_instr_lemmas.write_post st st' q /\ (forall a, aid_at st' a = aid_at st a).
  Proof.
    intros Hv Hp Hw. apply writable_word_iff in Hw. destruct Hw as (ptrs & E & W).
    destruct (write_dvalue_exists st DTYPE_Pointer q (Ptr p') ptrs) as (st' & Hrun);
      [rewrite sizeof_ptr; exact E | exact W |].
    destruct (write_read_ptr _ _ _ _ _ Hrun) as (p'' & Hr & E1 & E2).
    exists st', p''. split; [eapply LLVM_instr_lemmas.instr_store_run; eauto|].
    split; [exact Hr|]. split; [exact E1|]. split; [exact E2|].
    split; [eapply LLVM_instr_lemmas.write_dvalue_post; [apply sizeof_ptr|exact Hrun]|].
    apply write_dvalue_runs in Hrun. tauto.
  Qed.

  (** A straight-line sequence of word stores with non-flattening operands. *)
  Inductive fstores (sf : stack_frame) (stk : stack) : code dtyp -> list (ptr * Z) -> Prop :=
  | fstores_nil : fstores sf stk [] []
  | fstores_cons n ev ep w q c l :
      Flatten_sem.noflat_exp ev -> Flatten_sem.noflat_exp ep ->
      (forall st0, exp_eval st0 sf stk g (Some (DTYPE_I 64 : dtyp)) ev (I64 w)) ->
      (forall st0, exp_eval st0 sf stk g (Some (DTYPE_Pointer : dtyp)) ep (Ptr q)) ->
      fstores sf stk c l ->
      fstores sf stk ((IVoid n, INSTR_Store ((DTYPE_I 64 : dtyp), ev) ((DTYPE_Pointer : dtyp), ep) [], []) :: c) ((q, w) :: l).

  Lemma wpost_nil st : wpost st st [].
  Proof. split; [apply LLVM_instr_lemmas.writes_post_nil|auto]. Qed.

  Lemma fgoal_stores P lo c l rest tmt K st sf stk :
    closedP P -> fstores sf stk c l ->
    Forall (fun qw => writable_word st (fst qw)) l ->
    ForallOrdPairs (fun a b => LLVM_instr_lemmas.disj8 (fst a) (fst b)) l ->
    (forall st', wpost st st' (map fst l) -> Forall (fun qw => reads_word st' (fst qw) (snd qw)) l ->
                 fgoal ctx va g P lo rest tmt K st' sf stk) ->
    fgoal ctx va g P lo (c ++ rest) tmt K st sf stk.
  Proof.
    intros HP H. revert st. induction H as [|n ev ep w q c l Hnv Hnp Hv Hp Hc IH]; intros st W D Hk.
    - apply Hk; [apply wpost_nil|constructor].
    - inversion W as [|? ? Wq Wl]; subst. inversion D as [|? ? Dq Dl]; subst.
      destruct (store_word_aid n ev ep w q st sf stk (Hv st) (Hp st) Wq) as (st1 & R1 & Rq & P1 & A1).
      cbn [app]. eapply fgoal_instr; [exact HP| | | exact R1|].
      + cbn. split; assumption.
      + split; eexists; [apply Hv|apply Hp].
      + apply IH.
        * eapply Forall_impl; [|exact Wl]. intros [q' w'] Wq'. apply P1, Wq'.
        * exact Dl.
        * intros st' [P2 A2] Rl. apply Hk.
          -- split; [eapply LLVM_instr_lemmas.writes_post_cons; eauto|]. intros a. rewrite A2, A1. reflexivity.
          -- constructor; [|exact Rl]. cbn. apply P2; [exact Rq|].
             rewrite Forall_forall in Dq |- *. intros q' Hin. apply in_map_iff in Hin.
             destruct Hin as ([q'' w''] & <- & Hin). apply (Dq _ Hin).
  Qed.
End StoreHelpers.

(* ------------------------------------------------------------------ *)
(** ** Slots, address arithmetic, expression shapes *)

Lemma slot_ptrs_range p i qs :
  LLVM_instr_lemmas.slot_ptrs p i qs ->
  Forall (fun q => exists j, (i <= j < i + length qs)%nat /\ ptr_to_int q = ptr_to_int p + 8 * Z.of_nat j) qs.
Proof.
  revert i. induction qs as [|q qs IH]; intros i H; constructor.
  - destruct H as [Hq _]. exists i. split; [cbn; lia|]. apply LLVM_sim.ptr_off_int in Hq. exact Hq.
  - destruct H as [_ H]. specialize (IH (S i) H). eapply Forall_impl; [|exact IH].
    intros q' (j & Hj & E). exists j. cbn [length]. split; [lia|exact E].
Qed.

Lemma slot_ptrs_ex p i n :
  ptr_to_int p + 8 * Z.of_nat (i + n) <= 2 ^ 64 ->
  exists qs, length qs = n /\ LLVM_instr_lemmas.slot_ptrs p i qs.
Proof.
  revert i. induction n as [|n IH]; intros i H; [exists []; split; [reflexivity|exact I]|].
  destruct (LLVM_sim.ptr_off_ex p (8 * Z.of_nat i)) as (q & Hq).
  { pose proof (ptr_to_int_range p). rewrite Nat2Z.inj_add, Nat2Z.inj_succ in H. lia. }
  destruct (IH (S i)) as (qs & L & Hs); [rewrite Nat2Z.inj_add, Nat2Z.inj_succ in *; lia|].
  exists (q :: qs). split; [cbn; f_equal; exact L|]. split; assumption.
Qed.

Lemma slot_ptrs_nth p i qs j q :
  LLVM_instr_lemmas.slot_ptrs p i qs -> nth_error qs j = Some q -> ptr_off p (8 * Z.of_nat (i + j)) q.
Proof.
  revert i j. induction qs as [|q0 qs IH]; intros i j H Hj; [destruct j; discriminate|].
  destruct H as [Hq H]. destruct j as [|j]; cbn in Hj.
  - injection Hj as <-. rewrite Nat.add_0_r. exact Hq.
  - replace (i + S j)%nat with (S i + j)%nat by lia. eapply IH; eauto.
Qed.

(** A word whose bytes avoid [thread_info] is disjoint from each of its fields. *)
Lemma disj8_tinfo (tinfo q a : ptr) off :
  (forall b, ptr_to_int q <= b < ptr_to_int q + 8 -> ~ (ptr_to_int tinfo <= b < ptr_to_int tinfo + 8232)) ->
  0 <= off -> off + 8 <= 8232 -> ptr_to_int a = ptr_to_int tinfo + off ->
  LLVM_instr_lemmas.disj8 q a.
Proof.
  intros H H1 H2 E. unfold LLVM_instr_lemmas.disj8.
  destruct (Z_le_gt_dec (ptr_to_int q + 8) (ptr_to_int a)) as [|Ha]; [left; assumption|].
  destruct (Z_le_gt_dec (ptr_to_int a + 8) (ptr_to_int q)) as [|Hb]; [right; assumption|].
  exfalso. apply (H (Z.max (ptr_to_int q) (ptr_to_int a))); lia.
Qed.

Lemma noflat_gep_tinfo n : Flatten_sem.noflat_exp (cexp (gep_tinfo n)).
Proof. rewrite cexp_gep_tinfo. cbn. repeat split; reflexivity. Qed.

Lemma noflat_gep_at_ss s k n : Flatten_sem.noflat_exp (cexp (gep_at (EXP_Ident (ID_Local (ssname s k))) n)).
Proof. rewrite cexp_gep_at, cexp_Ident. cbn. repeat split. all: try exact I. all: try apply Flatten_sem.is_flat_ssname. Qed.

Lemma noflat_ss s k : Flatten_sem.noflat_exp (EXP_Ident (ID_Local (ssname s k))).
Proof. apply Flatten_sem.is_flat_ssname. Qed.

Lemma eval_gep_tinfo_field st sf stk g tinfo n off a t :
  LLVM_sim.tinfo_local tinfo sf ->
  (n, off) = (0%nat, 0) \/ (n, off) = (1%nat, 8) \/ (n, off) = (4%nat, 8216) \/ (n, off) = (5%nat, 8224) ->
  ptr_off tinfo off a ->
  exp_eval st sf stk g t (cexp (gep_tinfo n)) (Ptr a).
Proof.
  intros Ht Hn Ha. rewrite cexp_gep_tinfo, cty_tinfo_struct. unfold dlit.
  change (DTYPE_Struct false _) with tinfo_dt.
  eapply exp_eval_gep_tinfo; [exact Hn| |exact Ha]. apply exp_eval_local, Ht.
Qed.

Lemma eval_gep_at_local st sf stk g r p n q t :
  RM.find r (stack_vars sf) = Some (Ptr p) -> Z.of_nat n < 2 ^ 63 -> ptr_off p (8 * Z.of_nat n) q ->
  exp_eval st sf stk g t (cexp (gep_at (EXP_Ident (ID_Local r)) (N.of_nat n))) (Ptr q).
Proof.
  intros Hr Hn Hq. rewrite cexp_gep_at, cexp_Ident. unfold dlit. rewrite Nat2N.id.
  eapply exp_eval_gep_at; [exact Hn| |exact Hq]. apply exp_eval_local, Hr.
Qed.

Section StoreFields.
  Variable g : global_env.

  Lemma fstores_store_fields sf stk fs env vp i ys ws p qs :
    (forall st0, exp_eval st0 sf stk g (Some (DTYPE_Pointer : dtyp)) (cexp vp) (Ptr p)) ->
    Flatten_sem.noflat_exp (cexp vp) ->
    Forall2 (fun y w => forall st0, exp_eval st0 sf stk g (Some (DTYPE_I 64 : dtyp)) (cexp (gvar fs env y)) (I64 w)) ys ws ->
    (forall y, In y ys -> Flatten_sem.noflat_exp (cexp (gvar fs env y))) ->
    Z.of_nat (N.to_nat i + length ys) < 2^63 ->
    LLVM_instr_lemmas.slot_ptrs p (N.to_nat i) qs -> length qs = length ws ->
    fstores g sf stk (ccode (store_fields fs env vp i ys)) (combine qs ws).
  Proof.
    intros Hp Hnp. revert i qs ws. induction ys as [|y ys IH]; intros i qs ws Hys Hnf Hi Hs L.
    - inversion Hys; subst. destruct qs; [|discriminate]. rewrite ccode_store_fields_nil. constructor.
    - inversion Hys as [|? w ? ws' Hy Hys']; subst. destruct qs as [|q qs]; [discriminate|].
      destruct Hs as [Hq Hs]. rewrite ccode_store_fields_cons. cbn [combine].
      apply fstores_cons.
      + apply Hnf. left. reflexivity.
      + rewrite cexp_gep_at. cbn. split; [exact Hnp|repeat split].
      + exact Hy.
      + intros st0. rewrite cexp_gep_at. unfold LLVM_emit_facts.i64.
        eapply exp_eval_gep_at; [cbn [length] in Hi; lia|apply Hp|exact Hq].
      + apply IH; auto.
        * intros y' Hy'. apply Hnf. right. exact Hy'.
        * rewrite N2Nat.inj_succ. cbn [length] in Hi. lia.
        * rewrite N2Nat.inj_succ. exact Hs.
  Qed.
End StoreFields.


Lemma combine_nth_In {A B} (l : list A) (l' : list B) i a b :
  nth_error l i = Some a -> nth_error l' i = Some b -> In (a, b) (combine l l').
Proof.
  revert l' i. induction l as [|x l IH]; intros [|y l'] [|i] H1 H2; cbn in *; try discriminate.
  - injection H1 as ->. injection H2 as ->. left. reflexivity.
  - right. eapply IH; eauto.
Qed.

Lemma aid_alloc st st' a :
  aid_at st' a = aid_at st a -> IntMaps.lookup a (mem_of st) <> None -> IntMaps.lookup a (mem_of st') <> None.
Proof.
  unfold aid_at. intros E H. destruct (IntMaps.lookup a (mem_of st')); [discriminate|].
  destruct (IntMaps.lookup a (mem_of st)); [discriminate|contradiction].
Qed.

Lemma disj8_sym p q : LLVM_instr_lemmas.disj8 p q -> LLVM_instr_lemmas.disj8 q p.
Proof. unfold LLVM_instr_lemmas.disj8. lia. Qed.


(* ------------------------------------------------------------------ *)
(** ** Phis and jumps *)

Lemma phi_upd_other ivs m r :
  (forall iv, In iv ivs -> fst iv <> r) ->
  RM.find r (LLVM_instr_lemmas.phi_upd ivs m) = RM.find r m.
Proof.
  revert m. induction ivs as [|[id v] ivs IH]; intros m H; [reflexivity|].
  unfold LLVM_instr_lemmas.phi_upd. cbn [fold_left]. fold (LLVM_instr_lemmas.phi_upd ivs (Maps.add id v m)).
  rewrite IH; [|intros; apply H; right; auto].
  apply LLVM_instr_lemmas.rfind_add_neq. apply (H (id, v)). left. reflexivity.
Qed.

Lemma phi_upd_ivs seed i ws m j w :
  nth_error ws j = Some w ->
  RM.find (ssname seed (2000 + (i + j))) (LLVM_instr_lemmas.phi_upd (LLVM_instr_lemmas.phi_ivs seed i ws) m) = Some w.
Proof.
  revert i j m. induction ws as [|w0 ws IH]; intros i j m Hj; [destruct j; discriminate|].
  cbn [LLVM_instr_lemmas.phi_ivs]. unfold LLVM_instr_lemmas.phi_upd. cbn [fold_left].
  fold (LLVM_instr_lemmas.phi_upd (LLVM_instr_lemmas.phi_ivs seed (S i) ws) (Maps.add (ssname seed (2000 + i)) w0 m)).
  destruct j as [|j]; cbn in Hj.
  - injection Hj as ->. rewrite phi_upd_other.
    + rewrite Nat.add_0_r. apply LLVM_instr_lemmas.rfind_add_eq.
    + intros iv Hin.
      assert (H : forall i' iv, In iv (LLVM_instr_lemmas.phi_ivs seed i' ws) ->
                  exists k, (i' <= k)%nat /\ fst iv = ssname seed (2000 + k)).
      { clear. induction ws as [|w ws IH]; intros i' iv Hin; [destruct Hin|].
        destruct Hin as [<-|Hin]; [exists i'; split; [lia|reflexivity]|].
        destruct (IH (S i') iv Hin) as (k & Hk & E). exists k. split; [lia|exact E]. }
      intros E. destruct (H (S i) iv Hin) as (k & Hk & E').
      pose proof (eq_trans (eq_sym E') E) as E2.
      apply ssname_inj in E2. destruct E2 as [_ E2]. lia.
  - replace (i + S j)%nat with (S i + j)%nat by lia. apply IH. exact Hj.
Qed.

Section Jumps.
  Variable ctx : CallE ~> itree (CallE +' MCFGEtop).
  Notation RUN t s := (Flatten_sem.run ctx t s).

  Lemma ocfg_phis_jump va B from l b' :
    RM.find l (ocfg_map B) = Some b' ->
    denote_ocfg B va (from, l) ≈ ITree.bind (denote_phis from (blk_phis b')) (fun _ => LLVM_sim.tail_of va B b').
  Proof.
    intros Hf.
    assert (Hid : l = blk_id b').
    { rewrite ScopeTheory.ocfg_map_find_block in Hf.
      eapply ScopeTheory.find_block_has_id; exact Hf. }
    subst l. unfold denote_ocfg. rewrite (LLVM_instr_lemmas.denote_ocfg_map_unfold va _ _ _ _ Hf).
    unfold LLVM_sim.tail_of, denote_block. cbn [bind Monad_itree].
    rewrite !Eqit.bind_bind. apply eutt_eq_bind. intros _.
    rewrite !Eqit.bind_bind. apply eutt_eq_bind. intros _.
    apply eutt_eq_bind. intros [l'|dv]; reflexivity.
  Qed.

  Lemma run_phis_jump va B from l b' st sf stk g st' sf' (P : _ -> Prop) :
    closedP P ->
    RM.find l (ocfg_map B) = Some b' ->
    LLVM_instr_lemmas.runs ctx (denote_phis from (blk_phis b')) (st, ((sf, stk), g)) (st', ((sf', stk), g)) tt ->
    P (RUN (LLVM_sim.tail_of va B b') (st', ((sf', stk), g))) ->
    P (RUN (denote_ocfg B va (from, l)) (st, ((sf, stk), g))).
  Proof.
    intros HP Hf Hr H. eapply HP; [|exact H]. symmetry.
    rewrite (ocfg_phis_jump va B from l b' Hf). rewrite Flatten_sem.run_bind.
    unfold LLVM_instr_lemmas.runs in Hr. change (interp_mcfg (interp_mrec ctx ?t) ?s) with (RUN t s) in Hr.
    rewrite Hr, Eqit.bind_ret_l. reflexivity.
  Qed.

  Lemma run_jump va B from l b' s (P : _ -> Prop) :
    closedP P ->
    RM.find l (ocfg_map B) = Some b' -> blk_phis b' = [] ->
    P (RUN (LLVM_sim.tail_of va B b') s) ->
    P (RUN (denote_ocfg B va (from, l)) s).
  Proof.
    intros HP Hf Hp H. eapply HP; [|exact H]. symmetry.
    rewrite (LLVM_sim.denote_ocfg_jump va B from l b' Hf Hp). reflexivity.
  Qed.
End Jumps.

(** An [alloca] steps the memory without touching allocated bytes. *)
Lemma mstep_weaken st st' (W W' : Z -> Prop) :
  LLVM_sim.mstep st st' W -> (forall a, W a -> W' a) -> LLVM_sim.mstep st st' W'.
Proof. intros (E & M & A & F) H. split; [exact E|]. split; [|split; assumption]. intros a Ha. apply M. auto. Qed.

Lemma alloca_mstep st st' sz p :
  LLVM_instr_lemmas.alloc_post st st' sz p -> LLVM_sim.mstep st st' (fun _ => False).
Proof.
  intros Hp. pose proof Hp as (Hh & (ptrs & Hc & _ & Hf) & Hfree & _).
  split; [exact Hh|]. split; [|split].
  - intros a _ Ha. eapply LLVM_instr_lemmas.alloc_post_allocated; eauto.
  - intros a Ha. unfold aid_at. rewrite (LLVM_instr_lemmas.alloc_post_allocated _ _ _ _ _ Hp Ha). reflexivity.
  - exists ptrs. split; [exact Hf|]. rewrite Forall_forall. intros q Hq.
    destruct (In_consec _ _ _ Hc Hq) as (i & _ & E & _). apply Hfree. lia.
Qed.


Lemma ccode_check_blk fs x ys e' fresh f0 :
  blk_code (cblock (hd_check_blk fs x ys e' fresh f0)) =
  [ (IId (ssname fresh 1), INSTR_Alloca (DTYPE_Array false (N.of_nat (length (hd_roots fs x ys e'))) (DTYPE_I 64)) [], []);
    (IId (ssname fresh 2), INSTR_Alloca (DTYPE_Struct false [(DTYPE_Pointer : dtyp); (DTYPE_Pointer : dtyp); (DTYPE_Pointer : dtyp)]) [], []);
    (IId (ssname fresh 3), INSTR_Load (DTYPE_Pointer : dtyp) ((DTYPE_Pointer : dtyp), cexp (gep_tinfo 0)) [], []);
    (IId (ssname fresh 4), INSTR_Load (DTYPE_Pointer : dtyp) ((DTYPE_Pointer : dtyp), cexp (gep_tinfo 1)) [], []);
    (IId (ssname fresh 5), INSTR_Op (OP_IBinop (Sub false false) (DTYPE_I 64 : dtyp)
        (OP_Conversion (CONV_Impure Ptrtoint) (DTYPE_Pointer : dtyp) (EXP_Ident (ID_Local (ssname fresh 4))) (DTYPE_I 64 : dtyp))
        (OP_Conversion (CONV_Impure Ptrtoint) (DTYPE_Pointer : dtyp) (EXP_Ident (ID_Local (ssname fresh 3))) (DTYPE_I 64 : dtyp))), []);
    (IId (ssname fresh 6), INSTR_Op (OP_ICmp false Uge (DTYPE_I 64 : dtyp) (EXP_Ident (ID_Local (ssname fresh 5)))
        (dlit (8 * N.to_nat (hd_nwords ys + chunk_words e')))), []) ] /\
  blk_term (cblock (hd_check_blk fs x ys e' fresh f0)) =
  (IVoid 2%Z, TERM_Br ((DTYPE_I 1 : dtyp), EXP_Ident (ID_Local (ssname fresh 6)))
                (Anon (Zpos (Pos.succ (Pos.succ f0)))) (Anon (Zpos (Pos.succ f0))), []) /\
  blk_id (cblock (hd_check_blk fs x ys e' fresh f0)) = Anon (Zpos f0).
Proof.
  rewrite cblock_eq. unfold hd_check_blk. cbn [blk_code blk_term blk_id].
  rewrite !ccode_cons, ccode_nil, !cinstr_Alloca, !cinstr_Load, !cinstr_Op. unfold ctexp. cbn [fst snd].
  rewrite cty_val_array, cty_frame, cty_ptr, !cexp_IBinop, !cexp_Conversion, cexp_ICmp, !cexp_Ident, cexp_lit, !cty_val, cty_ptr.
  rewrite cterm_Br. unfold ctexp. cbn [fst snd]. rewrite cty_i1, cexp_Ident. auto.
Qed.

(* ------------------------------------------------------------------ *)
(** ** Consecutive pointers, provenance-independent reads *)

Lemma Forall2_exists {A B} (R : A -> B -> Prop) (l : list A) :
  (forall a, In a l -> exists b, R a b) -> exists res, Forall2 R l res.
Proof.
  induction l as [|a l IH]; intros H; [exists []; constructor|].
  destruct (H a (or_introl eq_refl)) as (b & Hb). destruct IH as (res & Hr); [intros; apply H; right; auto|].
  exists (b :: res). constructor; auto.
Qed.

Lemma Forall2_In_r' {A B} (R : A -> B -> Prop) l1 l2 b :
  Forall2 R l1 l2 -> In b l2 -> exists a, In a l1 /\ R a b.
Proof.
  induction 1 as [|x y l1 l2 Hxy Hl IH]; intros Hin; [destruct Hin|].
  destruct Hin as [<-|Hin]; [exists x; split; [left|]; auto|].
  destruct (IH Hin) as (a & Ha & Hr). exists a; split; [right|]; auto.
Qed.

Lemma map_monad_acc_ret {A B} (f : A -> EOU.EOU B) l res :
  Forall2 (fun a b => f a = ret b) l res -> map_monad_acc f l = ret res.
Proof.
  intros H. unfold map_monad_acc.
  assert (G : forall acc, (fix loop (acc : list B) (l : list A) : EOU.EOU (list B) :=
       match l with
       | [] => ret (rev_append acc [])
       | a :: l' => b <- f a;; loop (b :: acc) l'
       end) acc l = ret (rev_append acc res)).
  { induction H as [|a b l res Hab Hr IH]; intros acc; cbn; [reflexivity|].
    rewrite Hab. cbn. apply IH. }
  apply G.
Qed.

Lemma in_Nseq a s m : In a (ListUtil.Nseq s m) -> (s <= a < s + N.of_nat m)%N.
Proof.
  revert s. induction m as [|m IH]; intros s H; [destruct H|].
  destruct H as [<-|H]; [lia|]. apply IH in H. lia.
Qed.

Lemma gcp_exists (p : ptr) n :
  ptr_to_int p + Z.of_N n <= 2 ^ 64 -> exists ptrs, get_consecutive_ptrs p n = ret ptrs.
Proof.
  intros Hn. pose proof (ptr_to_int_range p) as Rp.
  unfold get_consecutive_ptrs, intptr_seq. rewrite EOU.seq_map_monad_acc_eq, ListUtil.N_to_nat_safe_eq.
  destruct (Forall2_exists (fun a b => (from_Z ∘ Z.of_N) a = ret b) (ListUtil.Nseq 0 (N.to_nat n))) as (ixs & Hix).
  { intros a Ha. apply in_Nseq in Ha. unfold Basics.compose. cbn. unfold IPtrFinite.from_Z_bits.
    assert (E : (Z.of_N a <=? @Integers.max_unsigned 64) && (Z.of_N a >=? 0) = true).
    { unfold Integers.max_unsigned. rewrite modulus64. apply andb_true_intro; split; [apply Z.leb_le|apply Z.geb_le]; lia. }
    rewrite E. eexists; reflexivity. }
  apply EOU.map_monad_EOU_Forall2 in Hix. rewrite Hix. cbn [bind EOU.EOU_monad].
  destruct (Forall2_exists (fun ix q => handle_gep_ptr (DTYPE_I 8) p [DVALUE_Base (DVALUE_Iptr ix)] = ret q) ixs) as (ptrs & Hp).
  { intros ix Hin. apply EOU.map_monad_EOU_Forall2 in Hix.
    destruct (Forall2_In_r' _ _ _ _ Hix Hin) as (a & Ha & Hf). apply in_Nseq in Ha.
    apply from_Z_to_Z in Hf.
    destruct (@int_to_ptr_total (ptr_to_int p + Z.of_N (sizeof_dtyp (DTYPE_I 8)) * to_Z ix) (ptr_provenance p)) as (q & Hq & _).
    { rewrite Hf. rewrite N2Nat.id in Ha. change (Z.of_N (sizeof_dtyp (DTYPE_I 8))) with 1. lia. }
    exists q. cbn. exact Hq. }
  exists ptrs. apply map_monad_acc_ret, Hp.
Qed.

Lemma Forall2_of_nth {A B} (R : A -> B -> Prop) l1 l2 :
  length l1 = length l2 ->
  (forall i a b, nth_error l1 i = Some a -> nth_error l2 i = Some b -> R a b) -> Forall2 R l1 l2.
Proof.
  revert l2. induction l1 as [|a l1 IH]; intros [|b l2] L H; try discriminate; constructor.
  - apply (H 0%nat); reflexivity.
  - apply IH; [cbn in L; lia|]. intros i a' b' H1 H2. apply (H (S i)); assumption.
Qed.

Lemma consec_bound p ptrs : consec p ptrs -> ptrs <> [] -> ptr_to_int p + Z.of_nat (length ptrs) <= 2 ^ 64.
Proof.
  intros C Hne. destruct (nth_error ptrs (length ptrs - 1)) as [q|] eqn:E.
  - destruct (C _ _ E) as [Eq _]. pose proof (ptr_to_int_range q). destruct ptrs; [congruence|]. cbn [length] in *. lia.
  - apply nth_error_None in E. destruct ptrs; [congruence|]. cbn [length] in *. lia.
Qed.

Lemma gcp_bound p n ptrs : get_consecutive_ptrs p n = ret ptrs -> ptr_to_int p + Z.of_N n <= 2 ^ 64.
Proof.
  intros E. apply gcp_spec in E. destruct E as [L C]. pose proof (ptr_to_int_range p).
  destruct ptrs as [|q ptrs].
  - cbn in L. assert (n = 0%N) by lia. subst. lia.
  - pose proof (consec_bound _ _ C ltac:(discriminate)) as B. rewrite L in B. rewrite N_nat_Z in B. exact B.
Qed.

Lemma read_reprov st t q q' v :
  memS_returns st (read_dvalue t q) v -> ptr_to_int q' = ptr_to_int q ->
  (forall b, ptr_to_int q <= b < ptr_to_int q + Z.of_N (sizeof_dtyp t) ->
     exists aid, aid_at st b = Some aid /\ access_allowed (ptr_provenance q') aid = true) ->
  memS_returns st (read_dvalue t q') v.
Proof.
  intros (st0 & H) Eq Hacc. apply read_dvalue_runs in H. destruct H as (_ & ptrs & bs & E & HF & Hc).
  pose proof (gcp_bound _ _ _ E) as B. pose proof E as E0. apply gcp_spec in E0. destruct E0 as [L C].
  destruct (gcp_exists q' (sizeof_dtyp t)) as (ptrs' & E'); [lia|].
  pose proof E' as E1. apply gcp_spec in E1. destruct E1 as [L' C'].
  exists st. apply read_dvalue_runs. split; [reflexivity|]. exists ptrs', bs. split; [exact E'|]. split; [|exact Hc].
  pose proof (Forall2_length HF) as LB.
  apply Forall2_of_nth; [lia|]. intros i a b Ha Hb.
  destruct (nth_error ptrs i) as [r|] eqn:Er; [|apply nth_error_None in Er; assert (i < length ptrs')%nat by (apply nth_error_Some; congruence); lia].
  destruct (LLVM_sim.nth_error_Forall2 _ _ _ _ _ HF Er) as (b' & Hb' & (aid & Hl & Hacc0)). rewrite Hb in Hb'. injection Hb' as <-.
  destruct (C _ _ Er) as [Er1 _]. destruct (C' _ _ Ha) as [Ea1 Ea2].
  assert (Hi : (i < length ptrs)%nat) by (apply nth_error_Some; congruence).
  destruct (Hacc (ptr_to_int a)) as (aid' & Ha' & Hacc'); [rewrite L in Hi; lia|].
  exists aid. split.
  - rewrite Ea1, Eq, <- Er1. exact Hl.
  - unfold aid_at in Ha'. rewrite Ea1, Eq, <- Er1, Hl in Ha'. cbn in Ha'. injection Ha' as ->. rewrite Ea2. exact Hacc'.
Qed.

Lemma writable_word_of st q :
  ptr_to_int q + 8 <= 2 ^ 64 ->
  (forall b, ptr_to_int q <= b < ptr_to_int q + 8 ->
     exists aid, aid_at st b = Some aid /\ access_allowed (ptr_provenance q) aid = true) ->
  writable_word st q.
Proof.
  intros Hb H. apply writable_word_iff. destruct (gcp_exists q 8) as (ptrs & E); [exact Hb|].
  exists ptrs. split; [exact E|]. apply gcp_spec in E. destruct E as [L C].
  intros r Hr. destruct (In_consec _ _ _ C Hr) as (i & Hi & E1 & E2).
  destruct (H (ptr_to_int r)) as (aid & Ha & Hacc); [rewrite L in Hi; cbn in Hi; lia|].
  exists aid. rewrite E2. auto.
Qed.

Lemma alloc_post_access st st' sz p :
  LLVM_instr_lemmas.alloc_post st st' sz p ->
  ptr_to_int p + Z.of_N sz <= 2 ^ 64 /\
  forall b, ptr_to_int p <= b < ptr_to_int p + Z.of_N sz ->
    exists aid, aid_at st' b = Some aid /\ access_allowed (ptr_provenance p) aid = true.
Proof.
  intros Hp. pose proof Hp as (_ & (ptrs & C & L & _) & _ & _ & W).
  assert (B : ptr_to_int p + Z.of_N sz <= 2 ^ 64).
  { destruct ptrs as [|q ptrs].
    - cbn in L. assert (sz = 0%N) by lia. subst. pose proof (ptr_to_int_range p). lia.
    - pose proof (consec_bound _ _ C ltac:(discriminate)) as B. rewrite L, N_nat_Z in B. exact B. }
  split; [exact B|]. intros b Hb.
  destruct (@int_to_ptr_total b (ptr_provenance p)) as (q & _ & E1 & E2); [pose proof (ptr_to_int_range p); lia|].
  destruct (W q E2 ltac:(lia)) as (aid & Ha & Hacc). exists aid. rewrite <- E1, <- E2. auto.
Qed.

Lemma access_wild aid : access_allowed wildcard_prov aid = true.
Proof. reflexivity. Qed.


(* ------------------------------------------------------------------ *)
(** ** Helpers for the collection path *)

Lemma slots_build st n : forall s e,
  ptr_to_int e = ptr_to_int s + 8 * Z.of_nat n -> ptr_to_int e < 2 ^ 64 ->
  exists rs, slots_from st s e rs /\ length rs = n /\
    forall i r, nth_error rs i = Some r ->
      ptr_to_int r = ptr_to_int s + 8 * Z.of_nat i /\ ptr_provenance r = ptr_provenance s.
Proof.
  induction n as [|n IH]; intros s e E B.
  - exists []. split; [apply Slots_done; lia|]. split; [reflexivity|]. intros [|i] r H; discriminate.
  - pose proof (ptr_to_int_range s) as Rs.
    destruct (LLVM_sim.ptr_off_ex s 8) as (s' & Hs'); [rewrite Nat2Z.inj_succ in E; lia|].
    pose proof (LLVM_sim.ptr_off_int _ _ _ Hs') as E'. pose proof (LLVM_sim.ptr_off_prov _ _ _ Hs') as P'.
    destruct (IH s' e) as (rs & Hrs & L & Hn); [rewrite Nat2Z.inj_succ in E; lia|exact B|].
    exists (s :: rs). split; [apply Slots_more with (s' := s'); [rewrite Nat2Z.inj_succ in E; lia|exact Hs'|exact Hrs]|].
    split; [cbn; f_equal; exact L|]. intros [|i] r Hi; cbn in Hi.
    + injection Hi as <-. split; [lia|reflexivity].
    + destruct (Hn i r Hi) as [H1 H2]. split; [rewrite H1, E'; lia|congruence].
Qed.

Lemma eval_gep_arr_local st sf stk g r p n i q t :
  RM.find r (stack_vars sf) = Some (Ptr p) -> Z.of_nat i < 2 ^ 63 -> ptr_off p (8 * Z.of_nat i) q ->
  exp_eval st sf stk g t (cexp (gep_arr (TYPE_Array n val_ty) (EXP_Ident (ID_Local r)) i)) (Ptr q).
Proof.
  intros Hr Hi Hq. rewrite cexp_gep_arr, cexp_Ident. unfold dlit, LLVM_emit_facts.i64, LLVM_emit_facts.i32.
  eapply exp_eval_gep_arr; [exact Hi| |exact Hq]. apply exp_eval_local, Hr.
Qed.

Lemma eval_gep_struct_local st sf stk g r p j q t :
  RM.find r (stack_vars sf) = Some (Ptr p) -> (j <= 2)%nat -> ptr_off p (8 * Z.of_nat j) q ->
  exp_eval st sf stk g t (cexp (gep_struct frame_ty (EXP_Ident (ID_Local r)) j)) (Ptr q).
Proof.
  intros Hr Hj Hq. rewrite cexp_gep_struct, cexp_Ident, cty_frame. unfold dlit, LLVM_emit_facts.i32.
  change (DTYPE_Struct false _) with frame_dt.
  eapply exp_eval_gep_frame; [exact Hj| |exact Hq]. apply exp_eval_local, Hr.
Qed.

Lemma noflat_gep_arr_ss n s k i : Flatten_sem.noflat_exp (cexp (gep_arr (TYPE_Array n val_ty) (EXP_Ident (ID_Local (ssname s k))) i)).
Proof. rewrite cexp_gep_arr, cexp_Ident. cbn. repeat split. all: try exact I. all: try apply Flatten_sem.is_flat_ssname. Qed.

Lemma noflat_gep_struct_ss s k j : Flatten_sem.noflat_exp (cexp (gep_struct frame_ty (EXP_Ident (ID_Local (ssname s k))) j)).
Proof. rewrite cexp_gep_struct, cexp_Ident. cbn. repeat split. all: try exact I. all: try apply Flatten_sem.is_flat_ssname. Qed.

Section Spill.
  Variable g : global_env.

  Lemma fstores_spill sf stk env r0 p n i rs zs qs :
    RM.find r0 (stack_vars sf) = Some (Ptr p) ->
    Forall2 (fun r z => RM.find (env r) (stack_vars sf) = Some (I64 z)) rs zs ->
    (forall r, In r rs -> Flatten_sem.is_flat (env r) = false) ->
    Flatten_sem.is_flat r0 = false ->
    Z.of_nat (i + length rs) < 2^63 ->
    LLVM_instr_lemmas.slot_ptrs p i qs -> length qs = length zs ->
    fstores g sf stk (ccode (spill_code env (EXP_Ident (ID_Local r0)) (TYPE_Array n val_ty) i rs)) (combine qs zs).
  Proof.
    intros Hp. revert i qs zs. induction rs as [|r rs IH]; intros i qs zs Hz Hnf Hn0 Hi Hs L.
    - inversion Hz; subst. destruct qs; [|discriminate]. rewrite ccode_spill_nil. constructor.
    - inversion Hz as [|? z ? zs' Hr Hz']; subst. destruct qs as [|q qs]; [discriminate|].
      destruct Hs as [Hq Hs]. rewrite ccode_spill_cons. cbn [combine].
      apply fstores_cons.
      + apply Hnf. left. reflexivity.
      + rewrite cexp_gep_arr, cexp_Ident. cbn. repeat split; try exact I. exact Hn0.
      + intros st0. apply exp_eval_local, Hr.
      + intros st0. apply eval_gep_arr_local with (p := p); [exact Hp|cbn [length] in Hi; lia|exact Hq].
      + apply IH; auto.
        * intros r' Hr'. apply Hnf. right. exact Hr'.
        * cbn [length] in Hi. lia.
  Qed.
End Spill.

Lemma ccode_gc_blk fs env x ys e' fresh f0 :
  let roots := hd_roots fs x ys e' in
  let aty := TYPE_Array (N.of_nat (length roots)) val_ty in
  let rootse := EXP_Ident (ID_Local (ssname fresh 1)) in
  let framee := EXP_Ident (ID_Local (ssname fresh 2)) in
  blk_code (cblock (hd_gc_blk fs env x ys e' fresh f0)) =
  ccode (spill_code env rootse aty 0 roots) ++
  [ (IVoid 0%Z, INSTR_Store ((DTYPE_Pointer : dtyp), cexp (gep_arr aty rootse (length roots)))
                  ((DTYPE_Pointer : dtyp), cexp (gep_struct frame_ty framee 0)) [], []);
    (IVoid 0%Z, INSTR_Store ((DTYPE_Pointer : dtyp), cexp (gep_arr aty rootse 0))
                  ((DTYPE_Pointer : dtyp), cexp (gep_struct frame_ty framee 1)) [], []);
    (IId (ssname fresh 10), INSTR_Load (DTYPE_Pointer : dtyp) ((DTYPE_Pointer : dtyp), cexp (gep_tinfo 4)) [], []);
    (IVoid 0%Z, INSTR_Store ((DTYPE_Pointer : dtyp), EXP_Ident (ID_Local (ssname fresh 10)))
                  ((DTYPE_Pointer : dtyp), cexp (gep_struct frame_ty framee 2)) [], []);
    (IVoid 0%Z, INSTR_Store ((DTYPE_Pointer : dtyp), EXP_Ident (ID_Local (ssname fresh 2))) ((DTYPE_Pointer : dtyp), cexp (gep_tinfo 4)) [], []);
    (IVoid 0%Z, INSTR_Store ((DTYPE_I 64 : dtyp), dlit (N.to_nat (hd_nwords ys + chunk_words e')))
                  ((DTYPE_Pointer : dtyp), cexp (gep_tinfo 5)) [], []);
    (IVoid 0%Z, INSTR_Call ((DTYPE_Void : dtyp), EXP_Ident (ID_Global (Name "garbage_collect")))
                  [(((DTYPE_Pointer : dtyp), EXP_Ident (ID_Local (Name "tinfo"))), [])] [] [], []) ] ++
  ccode (reload_code fresh rootse aty 0 roots) ++
  [ (IVoid 0%Z, INSTR_Store ((DTYPE_Pointer : dtyp), EXP_Ident (ID_Local (ssname fresh 10)))
                  ((DTYPE_Pointer : dtyp), cexp (gep_tinfo 4)) [], []) ] /\
  blk_term (cblock (hd_gc_blk fs env x ys e' fresh f0)) = (IVoid 5%Z, TERM_Br_1 (Anon (Zpos (Pos.succ (Pos.succ f0)))), []).
Proof.
  intros. rewrite cblock_eq. unfold hd_gc_blk. cbn [blk_code blk_term].
  rewrite !ccode_app, !ccode_cons, !ccode_nil, !cinstr_Store, cinstr_Load, cinstr_Call. unfold ctexp. cbn [fst snd map].
  rewrite cterm_Br_1, !cty_tinfo, !cexp_Ident, cty_Void, cty_val, cexp_lit, cty_ptr. unfold etinfo. rewrite cexp_Ident.
  split; reflexivity.
Qed.


Lemma reload_locals_find m seed i ws j w :
  nth_error ws j = Some w ->
  RM.find (ssname seed (1000 + (i + j))) (LLVM_instr_lemmas.reload_locals m seed i ws) = Some (I64 w).
Proof.
  revert m i j. induction ws as [|w0 ws IH]; intros m i j Hj; [destruct j; discriminate|].
  cbn [LLVM_instr_lemmas.reload_locals]. destruct j as [|j]; cbn in Hj.
  - injection Hj as ->. rewrite LLVM_instr_lemmas.reload_locals_other.
    + rewrite Nat.add_0_r. apply LLVM_instr_lemmas.rfind_add_eq.
    + intros k _ E. apply ssname_inj in E. lia.
  - replace (i + S j)%nat with (S i + j)%nat by lia. apply IH. exact Hj.
Qed.

Section CallReload.
  Variable ctx : CallE ~> itree (CallE +' MCFGEtop).
  Variable va : option ptr.
  Variable g : global_env.

  Lemma fgoal_reload P lo seed r0 p n rest tmt K st stk : forall rs i ws sf,
    closedP P ->
    RM.find r0 (stack_vars sf) = Some (Ptr p) ->
    (forall k, ssname seed (1000 + (i + k)) <> r0) -> Flatten_sem.is_flat r0 = false ->
    length ws = length rs -> Z.of_nat (i + length rs) < 2^63 ->
    LLVM_instr_lemmas.slots_ok (fun q w => reads_word st q w) p i ws ->
    fgoal ctx va g P lo rest tmt K st (upd_local_sf sf (LLVM_instr_lemmas.reload_locals (stack_vars sf) seed i ws)) stk ->
    fgoal ctx va g P lo (ccode (reload_code seed (EXP_Ident (ID_Local r0)) (TYPE_Array n val_ty) i rs) ++ rest) tmt K st sf stk.
  Proof.
    induction rs as [|r rs IH]; intros i ws sf HP Hr0 Hne Hfl L Hi R H.
    - destruct ws; [|discriminate]. rewrite ccode_reload_nil. cbn [app LLVM_instr_lemmas.reload_locals] in *.
      rewrite upd_local_sf_id in H. exact H.
    - destruct ws as [|w ws]; [discriminate|]. destruct R as ((q & Hq & Rq) & R).
      rewrite ccode_reload_cons. cbn [app].
      assert (Ev : exp_eval st sf stk g (Some (DTYPE_Pointer : dtyp))
                     (cexp (gep_arr (TYPE_Array n val_ty) (EXP_Ident (ID_Local r0)) i)) (Ptr q)).
      { eapply eval_gep_arr_local; [exact Hr0|cbn [length] in Hi; lia|exact Hq]. }
      eapply fgoal_instr; [exact HP| |eexists; exact Ev|apply (LLVM_instr_lemmas.instr_load_word ctx va _ _ q w); [exact Ev|exact Rq]|].
      { split; [apply Flatten_sem.is_flat_ssname|]. rewrite cexp_gep_arr, cexp_Ident. cbn. repeat split; try exact I. exact Hfl. }
      refine (IH (S i) ws _ HP _ _ Hfl _ _ R _).
      + rewrite LLVM_instr_lemmas.stack_vars_upd, LLVM_instr_lemmas.rfind_add_neq; [exact Hr0|].
        specialize (Hne 0%nat). rewrite Nat.add_0_r in Hne. exact Hne.
      + intros k. specialize (Hne (S k)). rewrite Nat.add_succ_r in Hne. exact Hne.
      + cbn [length] in L. lia.
      + cbn [length] in Hi. lia.
      + rewrite LLVM_instr_lemmas.upd_local_sf_twice, LLVM_instr_lemmas.stack_vars_upd. exact H.
  Qed.

  Lemma fgoal_call_gc P lo n l tmt K st sf stk gp tinfo0 :
    closedP P -> (forall t, ends_in_oom t -> P t) ->
    RM.find (Name "tinfo") (stack_vars sf) = Some (Ptr tinfo0) ->
    RM.find (Name "garbage_collect") g = Some (Ptr gp) ->
    (forall sf2, Flatten_sem.agree_noflat sf sf2 ->
       LLVM_instr_lemmas.oom ctx (ctx _ (Call DTYPE_Void (Ptr gp) [Ptr tinfo0])) (st, ((sf2, stk), g)) \/
       exists st', LLVM_instr_lemmas.runs ctx (ctx _ (Call DTYPE_Void (Ptr gp) [Ptr tinfo0])) (st, ((sf2, stk), g))
                                          (st', ((sf2, stk), g)) (inr (DVALUE_Base DVALUE_None)) /\
                   fgoal ctx va g P lo l tmt K st' sf stk) ->
    fgoal ctx va g P lo
      ((IVoid n, INSTR_Call ((DTYPE_Void : dtyp), EXP_Ident (ID_Global (Name "garbage_collect")))
                   [(((DTYPE_Pointer : dtyp), EXP_Ident (ID_Local (Name "tinfo"))), [])] [] [], []) :: l)
      tmt K st sf stk.
  Proof.
    intros HP Hoom Ht Hg H c sf' Hc Hag.
    assert (Hnf : Flatten_sem.agree_noflat sf sf') by (eapply Flatten_sem.agree_except_noflat'; eauto).
    destruct (Flatten_sem.flat_tail_call ctx va (IVoid n) DTYPE_Void (EXP_Ident (ID_Global (Name "garbage_collect")))
                [(((DTYPE_Pointer : dtyp), EXP_Ident (ID_Local (Name "tinfo"))), [])] [] [] [] l tmt c K
                st sf sf' stk g (Ptr gp) [Ptr tinfo0])
      as (Hc' & af & args' & sf2 & Hag2 & _ & Haf & Hevf & Hmap & Hevs & Eq).
    - exact I.
    - constructor; [reflexivity|constructor].
    - apply exp_eval_global, Hg.
    - constructor; [apply exp_eval_local, Ht|constructor].
    - exact Hnf.
    - rewrite (Haf eq_refl) in Eq.
      destruct args' as [|[[t' e'] pa] [|]]; cbn in Hmap; try discriminate.
      injection Hmap as -> ->. cbn in Hevs. inversion Hevs as [|? ? ? ? He' _]; subst.
      assert (Hnf2 : Flatten_sem.agree_noflat sf sf2).
      { intros r Hr. rewrite (Flatten_sem.agree_except_noflat _ _ _ _ _ Hag2 Hr). apply Hnf, Hr. }
      destruct (H sf2 Hnf2) as [Ho|(st' & Hr & Hk)].
      + apply Hoom. rewrite Eq.
        apply Flatten_sem.ends_in_oom_bind. eapply LLVM_instr_lemmas.oom_instr_call_gc; [exact He'|exact Hg|exact Ho].
      + eapply HP; [symmetry; exact Eq|].
        pose proof (LLVM_instr_lemmas.instr_call_gc ctx va n e' tinfo0 gp st sf2 stk g st' (sf2, stk) g _ He' Hg Hr) as Hi.
        unfold LLVM_instr_lemmas.runs in Hi. change (interp_mcfg (interp_mrec ctx ?t) ?s) with (Flatten_sem.run ctx t s) in Hi.
        eapply HP; [symmetry; rewrite Hi, Eqit.bind_ret_l; reflexivity|].
        apply Hk; [eapply Pos.le_trans; [exact Hc|exact Hc']|]. eapply (Flatten_sem.agree_except_trans lo c c _ lo); [lia|exact (Pos.le_refl _)|exact Hc|exact (Pos.le_refl _)|exact Hag|exact Hag2].
  Qed.
End CallReload.


Lemma app_eq_len {A} (l1 l2 l1' l2' : list A) :
  length l1 = length l1' -> (l1 ++ l2 = l1' ++ l2')%list -> l1 = l1' /\ l2 = l2'.
Proof.
  revert l1'. induction l1 as [|a l1 IH]; intros [|a' l1'] L E; try discriminate; [split; auto|].
  cbn in E. injection E as -> E. destruct (IH l1' ltac:(cbn in L; lia) E) as [-> ->]. auto.
Qed.

Lemma stack_ok_unlink st f e s fp rs1 rs :
  LLVM_sim.frame_fields st f e s fp -> LLVM_sim.stack_ok st f (rs1 ++ rs) ->
  LLVM_sim.stack_ok st fp rs /\
  (forall a, LLVM_sim.frame_bytes f a -> LLVM_sim.alloc_nonheap st a /\ ~ LLVM_sim.slot_bytes (rs1 ++ rs) a).
Proof.
  intros (Hnz & _ & _ & (a16 & Ha16 & Hp16)) ((frs & Hc & Hfa & Hfs) & Hsl).
  inversion Hc as [? H0|? prev frs' Hnz' (b & Hb & Hpb) Hc']; subst; [contradiction|].
  assert (b = a16) by (unfold ptr_off in Ha16, Hb; congruence). subst b.
  pose proof (LLVM_sim.reads_ptr_det _ _ _ _ Hp16 Hpb) as <-.
  split; [split|].
  - exists frs'. split; [exact Hc'|]. split.
    + intros g Hg. apply (Hfa g). right. exact Hg.
    + intros g Hg a Ha (r & Hr & Hra). apply (Hfs g (or_intror Hg) a Ha). exists r. split; [apply in_or_app; auto|exact Hra].
  - intros a (r & Hr & Hra). apply Hsl. exists r. split; [apply in_or_app; auto|exact Hra].
  - intros a Ha. split; [apply (Hfa f); [left; reflexivity|exact Ha]|apply (Hfs f); [left; reflexivity|exact Ha]].
Qed.


Lemma slots_ok_intro (P : ptr -> Z -> Prop) p : forall ws i,
  (forall j w, nth_error ws j = Some w -> exists q, ptr_off p (8 * Z.of_nat (i + j)) q /\ P q w) ->
  LLVM_instr_lemmas.slots_ok P p i ws.
Proof.
  induction ws as [|w ws IH]; intros i H; [exact I|]. split.
  - destruct (H 0%nat w eq_refl) as (q & Hq & HP). rewrite Nat.add_0_r in Hq. eauto.
  - apply IH. intros j w' Hj. destruct (H (S j) w' Hj) as (q & Hq & HP). exists q.
    replace (S i + j)%nat with (i + S j)%nat by lia. auto.
Qed.


Lemma Forall2_seq_map (P : nat -> dvalue -> Prop) zs n :
  length zs = n -> (forall j z, nth_error zs j = Some z -> P j (I64 z)) ->
  Forall2 P (seq 0 n) (map I64 zs).
Proof.
  intros L H. apply Forall2_of_nth; [rewrite length_seq, length_map; lia|].
  intros i a b Ha Hb. rewrite nth_error_seq in Ha. destruct (Nat.ltb i n); [|discriminate].
  injection Ha as <-. rewrite nth_error_map in Hb. destruct (nth_error zs i) eqn:E; [|discriminate].
  injection Hb as <-. apply H, E.
Qed.

Lemma split_rel (P : term.val -> Z -> Prop) (R1 : var -> term.val -> Prop) roots (wsd : list dvalue) :
  Forall2 (fun r w => exists v z, w = I64 z /\ R1 r v /\ P v z) roots wsd ->
  exists vs zs, wsd = map I64 zs /\ Forall2 R1 roots vs /\ Forall2 P vs zs.
Proof.
  induction 1 as [|r w roots wsd (v & z & -> & H1 & H2) _ (vs & zs & -> & F1 & F2)].
  - exists [], []. repeat constructor.
  - exists (v :: vs), (z :: zs). split; [reflexivity|]. split; constructor; auto.
Qed.

Lemma join_rel (P : term.val -> Z -> Prop) (R1 : var -> term.val -> Prop) roots vs zs :
  Forall2 R1 roots vs -> Forall2 P vs zs ->
  Forall2 (fun r w => exists v z, w = I64 z /\ R1 r v /\ P v z) roots (map I64 zs).
Proof.
  intros H1. revert zs. induction H1 as [|r v roots vs Hr _ IH]; intros zs H2; inversion H2; subst; constructor; eauto.
Qed.

(* ------------------------------------------------------------------ *)
(** ** The simulation context *)

Section Constr.

  Variable cenv : ctor_env.
  Variable pfs : prims.
  Variable prim_of : positive -> option (string * bool).
  Variable fds : fundefs.
  Variable heap_inv : state -> ptr -> Prop.
  Variable gc : list dvalue -> MCFGtop (exc + dvalue).
  Variable G : global_env.
  Variable ctx : CallE ~> itree (CallE +' MCFGEtop).
  Variable tinfo : ptr.
  Variable main : term.exp.

  Notation go := (ord_of cenv).
  Notation ga := (arity_of cenv).
  Notation fs := (fun_ids fds).
  Notation tr := (translate_cfg go ga prim_of fs).
  Notation INV := (LLVM_sim.INV cenv fds heap_inv G tinfo).
  Notation env_rel := (LLVM_sim.env_rel cenv fds G tinfo).
  Notation env_ok := LLVM_sim.env_ok.
  Notation stable_repr := (LLVM_sim.stable_repr cenv fds G tinfo).
  Notation sim_result := (LLVM_sim.sim_result cenv fds heap_inv G tinfo).
  Notation sim_stmt := (LLVM_sim.sim_stmt cenv prim_of fds heap_inv G ctx tinfo main).
  Notation RUN t s := (Flatten_sem.run ctx t s).
  Notation tinfo_local := (LLVM_sim.tinfo_local tinfo).

  Hypothesis Hmut : forall st st2 alloc alloc2 limit,
       heap_inv st tinfo -> tinfo_ok st tinfo ->
       heap_agree_except st st2 (mutator_writes st tinfo) ->
       field st tinfo off_alloc alloc -> field st tinfo off_limit limit ->
       field st2 tinfo off_alloc alloc2 ->
       (ptr_to_int alloc <= ptr_to_int alloc2 <= ptr_to_int limit)%Z ->
       (ptr_to_int alloc2 mod 8 = 0)%Z ->
       heap_inv st2 tinfo.
  Hypothesis Hgc : forall (st : state) ls fp rs vs nalloc,
       heap_inv st tinfo -> tinfo_ok st tinfo -> LLVM_sim.mem_ok st -> LLVM_sim.nursery_tinfo_disjoint st tinfo ->
       field st tinfo off_fp fp ->
       shadow_stack st fp rs ->
       roots_ok cenv fds G st tinfo rs vs ->
       0 <= nalloc < 2 ^ 61 ->
       (exists a, ptr_off tinfo off_nalloc a /\ reads_word st a nalloc) ->
       ends_in_oom (interp_mcfg (gc [Ptr tinfo]) (st, (ls, G)))
       \/ exists st',
           returns (interp_mcfg (gc [Ptr tinfo]) (st, (ls, G)))
                   ((st', (ls, G)), inr (DVALUE_Base DVALUE_None)) /\
           frames_of st' = frames_of st /\
           heap_inv st' tinfo /\ tinfo_ok st' tinfo /\ LLVM_sim.mem_ok st' /\ LLVM_sim.nursery_tinfo_disjoint st' tinfo /\
           field st' tinfo off_fp fp /\
           shadow_stack st' fp rs /\
           roots_ok cenv fds G st' tinfo rs vs /\
           room st' tinfo nalloc /\
           (forall a, ~ in_heap st a -> ~ LLVM_sim.slot_bytes rs a ->
                      IntMaps.lookup a (mem_of st') = IntMaps.lookup a (mem_of st)) /\
           (forall a, in_heap st' a -> in_heap st a \/ IntMaps.lookup a (mem_of st) = None) /\
           (forall a, LLVM_sim.slot_bytes rs a -> aid_at st' a = aid_at st a).
  Hypothesis Htinfo_range : ptr_to_int tinfo + 8232 < 2^64.
  Hypothesis ctx_fun : forall f ft xs e fp,
    fun_in_fundefs fds (f, ft, xs, e) ->
    RM.find (Anon (Zpos f)) G = Some (Ptr fp) ->
    forall dt p args, ptr_to_int p = ptr_to_int fp ->
      ctx _ (Call dt (Ptr p) args) ≈ denote_function (LLVM_sim.fun_def cenv prim_of fds f xs e) args.
  Hypothesis ctx_gc : forall gp,
    RM.find (Name "garbage_collect") G = Some (Ptr gp) ->
    forall dt p args, ptr_to_int p = ptr_to_int gp ->
      ctx _ (Call dt (Ptr p) args) ≈ lift_top (gc args).
  Hypothesis G_funs : forall f, In f fs -> exists fp, RM.find (Anon (Zpos f)) G = Some (Ptr fp).
  Hypothesis G_gc : exists gp, RM.find (Name "garbage_collect") G = Some (Ptr gp).
  Hypothesis Hprog : llvm_restricted cenv fds main.

  (* ---------------------------------------------------------------- *)
  (** *** Program facts *)

  Lemma prog_ub : unique_bindings (Efun fds main).
  Proof. destruct Hprog as (_ & _ & _ & H & _). exact H. Qed.

  Lemma prog_constr x t ys e :
    subterm_or_eq (Econstr x t ys e) (Efun fds main) ->
    tag_ok cenv t /\ arity_of cenv t = N.of_nat (length ys).
  Proof.
    intros H. destruct (LLVM_sim.prog_constr _ _ _ Hprog _ _ _ _ H) as (H1 & H2 & _). exact (conj H1 H2).
  Qed.

  Lemma prog_chunk_small x t ys e' :
    subterm_or_eq (Econstr x t ys e') (Efun fds main) -> ys <> [] ->
    8 * Z.of_N (hd_nwords ys + chunk_words e') < 2 ^ 64.
  Proof.
    intros Hs Hne. destruct (LLVM_sim.prog_constr _ _ _ Hprog _ _ _ _ Hs) as (_ & _ & H).
    destruct ys as [|y ys0]; [congruence|].
    cbn [chunk_words] in H. unfold hd_nwords. exact H.
  Qed.

  Lemma constr_not_fun x t ys e :
    subterm_or_eq (Econstr x t ys e) (Efun fds main) -> is_fun fs x = false.
  Proof.
    intros H. apply is_fun_false.
    apply (bound_not_fun fds main (Econstr x t ys e)); [apply prog_ub|exact H| |constructor].
    intros ? ? E; discriminate.
  Qed.

  (* ---------------------------------------------------------------- *)
  (** *** [sim_result] *)

  Lemma sim_result_closed st stk fp rs vs v : closedP (sim_result st stk fp rs vs v).
  Proof.
    intros t t' E [H|(st' & sf' & z & Hr & H)]; [left|right].
    - destruct H as [k Hk]. exists k. rewrite <- E. exact Hk.
    - exists st', sf', z. split; [|exact H]. unfold returns in *. rewrite <- E. exact Hr.
  Qed.

  Lemma sim_result_oom st stk fp rs vs v t : ends_in_oom t -> sim_result st stk fp rs vs v t.
  Proof. left. assumption. Qed.

  (** Memory frames only extended (at addresses that were not allocated
      stack memory), and the stack kept relative to the root slots [rs]. *)
  Definition fext (rs : list ptr) (st st1 : state) : Prop :=
    (exists ks, frames_of st1 = push_top ks (frames_of st) /\
                Forall (fun k => ~ LLVM_sim.alloc_nonheap st (ptr_to_int k)) ks) /\
    LLVM_sim.keeps_stack st st1 rs.

  Lemma fext_refl rs st : fext rs st st.
  Proof.
    split; [exists []; split; [symmetry; apply LLVM_sim.push_top_nil|constructor]|apply LLVM_sim.keeps_stack_refl].
  Qed.

  Lemma frames_trans rs st st1 st2 :
    fext rs st st1 ->
    (exists ks, frames_of st2 = push_top ks (frames_of st1) /\
                Forall (fun k => ~ LLVM_sim.alloc_nonheap st1 (ptr_to_int k)) ks) ->
    (exists ks, frames_of st2 = push_top ks (frames_of st) /\
                Forall (fun k => ~ LLVM_sim.alloc_nonheap st (ptr_to_int k)) ks).
  Proof.
    intros [(ks & F1 & K1) Kp] (ks' & F2 & K2).
    exists (ks ++ ks')%list. split; [rewrite F2, F1; apply LLVM_sim.push_top_app|].
    apply Forall_app. split; [exact K1|]. eapply Forall_impl; [|exact K2].
    intros k Hk Ha. apply Hk. eapply LLVM_sim.keeps_stack_nonheap; [exact Kp|exact Ha].
  Qed.

  Lemma fext_trans rs st st1 st2 : fext rs st st1 -> fext rs st1 st2 -> fext rs st st2.
  Proof.
    intros H1 H2. split; [eapply frames_trans; [exact H1|apply H2]|].
    eapply LLVM_sim.keeps_stack_trans; [apply H1|apply H2].
  Qed.

  (** Composition with a step under the extended root slots [rs1 ++ rs],
      where the new slots were not allocated stack memory before. *)
  Lemma fext_trans_slots rs rs1 st st1 st2 :
    fext rs st st1 -> fext (rs1 ++ rs) st1 st2 ->
    (forall a, LLVM_sim.slot_bytes rs1 a -> ~ LLVM_sim.alloc_nonheap st a) ->
    fext rs st st2.
  Proof.
    intros H1 H2 Hfr. split; [eapply frames_trans; [exact H1|apply H2]|].
    eapply LLVM_sim.keeps_stack_slots; [apply H1|apply H2|exact Hfr].
  Qed.

  Lemma fext_of_mstep rs st st' W :
    LLVM_sim.mstep st st' W -> (forall a, W a -> in_heap st a) -> fext rs st st'.
  Proof.
    intros H HW. split; [|eapply LLVM_sim.keeps_stack_mstep; eauto].
    destruct H as (_ & _ & _ & (ks & F & K)). exists ks. split; [exact F|].
    eapply Forall_impl; [|exact K]. intros k Hk (Ha & _). exact (Ha Hk).
  Qed.

  Lemma fext_mstep_empty rs st st' : LLVM_sim.mstep st st' (fun _ => False) -> fext rs st st'.
  Proof. intros H. eapply fext_of_mstep; [exact H|intros a []]. Qed.

  Lemma sim_result_ext st st1 stk fp rs vs v t :
    fext rs st st1 -> sim_result st1 stk fp rs vs v t -> sim_result st stk fp rs vs v t.
  Proof.
    intros Hx [H|(st' & sf' & z & Hr & Hs & HI & Hf & Hk)]; [left; exact H|right].
    exists st', sf', z. split; [exact Hr|split; [exact Hs|split; [exact HI|split]]].
    - eapply frames_trans; eauto.
    - eapply LLVM_sim.keeps_stack_trans; [apply Hx|exact Hk].
  Qed.

  (* ---------------------------------------------------------------- *)
  (** *** The continuation's SSA environment *)

  Lemma env_rel_ext S rho env env' sf st :
    (forall y, S y -> env y = env' y) -> env_rel S rho env sf st -> env_rel S rho env' sf st.
  Proof.
    intros E H y Hy. destruct (H y Hy) as (v & Hv & Hc). exists v. split; [exact Hv|].
    destruct (is_fun fs y); [exact Hc|]. rewrite <- (E y Hy). exact Hc.
  Qed.

  (** The continuation [e'] of [Econstr x t ys e'] is compiled under [env']; its
      restriction to the free variables of [e'] satisfies [env_ok] and gives
      the same code. *)
  Lemma cont_env x t ys e' env' fresh' chunk' fresh0 :
    unique_bindings (Econstr x t ys e') ->
    Ensembles.Disjoint _ (bound_var (Econstr x t ys e')) (occurs_free (Econstr x t ys e')) ->
    (forall y, occurs_free e' y -> env' y = Raw (Zpos y) \/
                                   exists s k, (s < fresh')%positive /\ env' y = ssname s k) ->
    (forall y, bound_var e' y -> env' y = Raw (Zpos y)) ->
    env_ok (occurs_free e') (restrict env' e') fresh' /\
    tr (restrict env' e') chunk' e' fresh0 = tr env' chunk' e' fresh0.
  Proof.
    intros Hub Hdis Hfv Hbv. pose proof (disjoint_constr _ _ _ _ Hub Hdis) as Hd'. split.
    - intros y. split.
      + intros Hy. rewrite restrict_fv by exact Hy. apply Hfv, Hy.
      + intros Hy. apply restrict_nfv, Hy.
    - apply tr_env_ext. intros y [Hy|Hy].
      + apply restrict_fv, Hy.
      + rewrite restrict_nfv; [symmetry; apply Hbv, Hy|].
        intros Hf. eapply disj_elim; [exact Hd'|exact Hy|exact Hf].
  Qed.

  (** For the environment of the [Econstr] itself. *)
  Lemma env_cont_same x t ys e' env fresh fresh' :
    (fresh <= fresh')%positive ->
    unique_bindings (Econstr x t ys e') ->
    Ensembles.Disjoint _ (bound_var (Econstr x t ys e')) (occurs_free (Econstr x t ys e')) ->
    env_ok (occurs_free (Econstr x t ys e')) env fresh ->
    (forall y, occurs_free e' y -> env y = Raw (Zpos y) \/
                                   exists s k, (s < fresh')%positive /\ env y = ssname s k) /\
    (forall y, bound_var e' y -> env y = Raw (Zpos y)) /\
    env x = Raw (Zpos x).
  Proof.
    intros Hle Hub Hdis Henv.
    assert (Hx : env x = Raw (Zpos x)).
    { destruct (Henv x) as [_ H]. apply H. apply x_not_free, Hdis. }
    split; [|split; [|exact Hx]].
    - intros y Hy. destruct (Pos.eq_dec x y) as [<-|Hne]; [left; exact Hx|].
      destruct (Henv y) as [H _]. destruct (H (Free_Econstr2 _ _ _ _ _ Hne Hy)) as [E|(s & k & Hs & E)];
        [left; exact E|right; exists s, k; split; [lia|exact E]].
    - intros y Hy. destruct (Henv y) as [_ H]. apply H. intros Hf.
      eapply disj_elim; [exact Hdis|apply Bound_Econstr2, Hy|exact Hf].
  Qed.

  Lemma blocks_in_prepend B x b rest :
    LLVM_sim.blocks_in B (prepend_code x (b :: rest)) -> LLVM_sim.blocks_in B (b :: rest).
  Proof. intros H. exact H. Qed.

  Lemma hd_prepend x b rest :
    LLVM_sim.hd_blk (prepend_code x (b :: rest)) =
    mk_block (blk_id b) (blk_phis b) (x ++ blk_code b)%list (blk_term b) (blk_comments b).
  Proof. reflexivity. Qed.

  (** Applying the induction hypothesis at the entry block [b] of the
      continuation, from any frame agreeing with [sf1] off the flattening
      names. *)
  Lemma apply_ih rho' e' v env' chunk' fresh' b rest f' B va st1 sf1 stk fp rs vs lo :
    sim_stmt rho' e' v ->
    body_ok cenv e' -> subterm_or_eq e' (Efun fds main) -> unique_bindings e' ->
    Ensembles.Disjoint _ (bound_var e') (occurs_free e') ->
    env_ok (occurs_free e') env' fresh' ->
    tr env' chunk' e' fresh' = (b :: rest, f') ->
    LLVM_sim.blocks_in B (b :: rest) ->
    INV st1 fp rs vs -> tinfo_local sf1 ->
    env_rel (occurs_free e') rho' env' sf1 st1 ->
    room st1 tinfo (Z.of_N chunk') ->
    fgoal ctx va G (sim_result st1 stk fp rs vs v) lo (blk_code (cblock b)) (blk_term (cblock b))
          (LLVM_sim.continue va B (blk_id b)) st1 sf1 stk.
  Proof.
    intros IH Hb Hs Hu Hd Henv Htr Hbin HI Htl Hrel Hroom c sf' _ Hag.
    pose proof (Flatten_sem.agree_except_noflat' _ _ _ _ Hag) as Hnf.
    specialize (IH env' chunk' fresh' (b :: rest) f' B va c st1 sf' stk fp rs vs Hb Hs Hu Hd Henv Htr Hbin HI
                  (LLVM_sim.tinfo_local_noflat _ _ _ Htl Hnf)
                  (LLVM_sim.env_rel_noflat _ _ _ _ _ _ _ _ _ _ _ _ Henv Hrel Hnf) Hroom).
    eapply sim_result_closed; [|exact IH]. cbn [LLVM_sim.hd_blk].
    change (interp_mcfg (interp_mrec ctx ?t) ?s) with (RUN t s).
    rewrite tail_of_flat, cblock_id. reflexivity.
  Qed.

  (* ---------------------------------------------------------------- *)
  (** *** Nullary constructors *)

  Lemma stable_repr_unboxed st t :
    arity_of cenv t = 0%N -> stable_repr st (Vconstr t []) (2 * Z.of_nat (N.to_nat (go t)) + 1).
  Proof.
    intros Ha st2 _. replace (2 * Z.of_nat (N.to_nat (go t)) + 1) with (Z.of_N (go t) * 2 + 1)
      by (rewrite N_nat_Z; lia).
    apply Repr_unboxed, Ha.
  Qed.

  Lemma sim_case_constr_nil x t e' rho v :
    sim_stmt (M.set x (Vconstr t []) rho) e' v -> sim_stmt rho (Econstr x t [] e') v.
  Proof.
    intros IH env chunk fresh blks f' B va c st sf stk fp rs vs Hbo Hsub Hub Hdis Henv Htr Hbin HI Htl Hrel Hroom.
    inversion Hbo as [? ? ? ? _ _ _ Hbo'| | | | | |]; subst.
    inversion Hub as [? ? ? ? Hxe Hub'| | | | | | | | |]; subst.
    destruct (tr env chunk e' fresh) as [blks0 f0] eqn:E.
    rewrite (tr_constr_nil go ga prim_of fs env chunk x t e' fresh blks0 f0 E) in Htr.
    injection Htr as <- <-.
    destruct (translate_cfg_entry go ga prim_of fs env chunk e' fresh blks0 f0 E) as (b & rest & q & -> & _).
    destruct (env_cont_same x t [] e' env fresh fresh (Pos.le_refl _) Hub Hdis Henv) as (Hfv & Hbv & Hx).
    destruct (cont_env x t [] e' env fresh chunk fresh Hub Hdis Hfv Hbv) as (Henv' & Htr').
    rewrite <- Htr' in E.
    pose proof (constr_not_fun _ _ _ _ Hsub) as Hnfx.
    destruct (prog_constr _ _ _ _ Hsub) as [_ Har].
    set (z := 2 * Z.of_nat (N.to_nat (go t)) + 1).
    assert (Hev : forall st0 sf0, exp_eval st0 sf0 stk G None (cexp (val_long (lit (N.to_nat (go t))))) (I64 z)).
    { intros. rewrite cexp_val_long, cexp_lit. apply exp_eval_val_long, exp_eval_lit64. }
    rewrite hd_prepend.
    change (interp_mcfg (interp_mrec ctx ?t) ?s) with (RUN t s).
    eapply sim_result_closed; [symmetry; apply tail_of_flat|].
    destruct (cblock_prepend [(IId (Raw (Zpos x)), INSTR_Op (val_long (lit (N.to_nat (go t)))), [])] b) as (E1 & E2 & E3).
    rewrite E1, E2, E3, cblock_id, ccode_single, cinstr_Op. cbn [app].
    match goal with |- sim_result _ _ _ _ _ _ (RUN (Flatten_sem.flat_tail _ ?l ?tm _ ?K) _) =>
      enough (Hf : fgoal ctx va G (sim_result st stk fp rs vs v) c l tm K st sf stk)
        by (apply Hf; [lia|apply Flatten_sem.agree_except_refl]) end.
    eapply fgoal_instr.
    - apply sim_result_closed.
    - change (Flatten_sem.noflat (Raw (Zpos x)) /\ Flatten_sem.noflat_exp (cexp (val_long (lit (N.to_nat (go t)))))).
      split; [apply Flatten_sem.is_flat_pos|]. rewrite cexp_val_long, cexp_lit. cbn. tauto.
    - eexists. apply Hev.
    - apply LLVM_instr_lemmas.instr_op, Hev.
    - eapply apply_ih with (env' := restrict env e') (chunk' := chunk) (fresh' := fresh).
      + exact IH.
      + exact Hbo'.
      + eapply subterm_constr; exact Hsub.
      + exact Hub'.
      + eapply disjoint_constr; eauto.
      + exact Henv'.
      + exact E.
      + eapply blocks_in_prepend; exact Hbin.
      + exact HI.
      + apply LLVM_sim.tinfo_local_write; [exact Htl|discriminate].
      + eapply env_rel_ext; [intros y Hy; symmetry; apply restrict_fv, Hy|].
        apply (LLVM_sim.env_rel_bind cenv fds G tinfo (occurs_free (Econstr x t [] e'))); auto.
        * intros y Hy. destruct (Pos.eq_dec y x) as [->|Hne]; [left; reflexivity|right].
          apply Free_Econstr2; auto.
        * intros y Hy _. eapply (LLVM_sim.env_ok_not_pos cenv prim_of); eauto.
          -- apply x_not_free, Hdis.
          -- intros ->. exact (x_not_free _ _ _ _ Hdis Hy).
        * apply stable_repr_unboxed. rewrite Har. reflexivity.
      + exact Hroom.
  Qed.
  (* ---------------------------------------------------------------- *)
  (** *** The words of the constructor's arguments *)

  Lemma env_rel_words S rho env0 sf stk st ys vs :
    env_rel S rho env0 sf st -> (forall y, In y ys -> S y) -> get_list ys rho = Some vs ->
    exists zs, Forall2 (fun y w => forall st0, exp_eval st0 sf stk G (Some (DTYPE_I 64 : dtyp)) (cexp (gvar fs env0 y)) (I64 w)) ys zs /\
               Forall2 (stable_repr st) vs zs.
  Proof.
    intros Hrel. revert vs. induction ys as [|y ys IH]; intros vs HS Hg.
    - cbn in Hg. injection Hg as <-. exists []. split; constructor.
    - cbn in Hg. destruct (M.get y rho) as [v|] eqn:Ey; [|discriminate].
      destruct (get_list ys rho) as [vs'|] eqn:Eys; [|discriminate]. injection Hg as <-.
      destruct (IH vs' (fun y' H => HS y' (or_intror H)) eq_refl) as (zs & H1 & H2).
      destruct (Hrel y (HS y (or_introl eq_refl))) as (v' & Ev & Hc). rewrite Ey in Ev. injection Ev as <-.
      destruct (is_fun fs y) eqn:Ef.
      + destruct Hc as (rho' & ->). destruct (G_funs y (is_fun_true _ _ Ef)) as (fp & Hfp).
        exists (ptr_to_int fp :: zs). split; constructor; auto.
        * intros st0. rewrite cexp_gvar_fun by exact Ef. unfold LLVM_emit_facts.dptr, LLVM_emit_facts.i64.
          apply exp_eval_ptrtoint, exp_eval_global, Hfp.
        * intros st2 _. apply Repr_fun. exact Hfp.
      + destruct Hc as (z & Hz & Hs). exists (z :: zs). split; constructor; auto.
        intros st0. rewrite cexp_gvar_local by exact Ef. apply exp_eval_local, Hz.
  Qed.

  Lemma noflat_gvar env0 y :
    (is_fun fs y = false -> Flatten_sem.is_flat (env0 y) = false) ->
    Flatten_sem.noflat_exp (cexp (gvar fs env0 y)).
  Proof.
    intros H. destruct (is_fun fs y) eqn:Ef.
    - rewrite cexp_gvar_fun by exact Ef. cbn. exact I.
    - rewrite cexp_gvar_local by exact Ef. apply H. reflexivity.
  Qed.

  Lemma get_list_length {A} ys (rho : M.t A) vs : get_list ys rho = Some vs -> length vs = length ys.
  Proof.
    revert vs. induction ys as [|y ys IH]; intros vs H; cbn in H.
    - injection H as <-. reflexivity.
    - destruct (M.get y rho); [|discriminate]. destruct (get_list ys rho) eqn:E; [|discriminate].
      injection H as <-. cbn. f_equal. apply IH. reflexivity.
  Qed.

  (* ---------------------------------------------------------------- *)
  (** *** The allocation sequence [alloc_code] *)

  Lemma alloc_fgoal va P lo env0 fresh x t ys vs k S1 S2 rho rest tmt K st sf stk fp rs vsr :
    closedP P ->
    INV st fp rs vsr -> tinfo_local sf ->
    room st tinfo (Z.of_N (hd_nwords ys + k)) ->
    tag_ok cenv t -> arity_of cenv t = N.of_nat (length ys) -> is_fun fs x = false ->
    get_list ys rho = Some vs -> ys <> [] ->
    env_rel S1 rho env0 sf st -> (forall y, In y ys -> S1 y) ->
    (forall y, In y ys -> is_fun fs y = false -> Flatten_sem.is_flat (env0 y) = false) ->
    (forall y, S1 y -> is_fun fs y = false ->
       env0 y <> Raw (Zpos x) /\ env0 y <> ssname fresh 7 /\ env0 y <> ssname fresh 8 /\ env0 y <> ssname fresh 9) ->
    env0 x = Raw (Zpos x) ->
    (forall y, S2 y -> y = x \/ S1 y) ->
    (forall st1 sf1, INV st1 fp rs vsr -> fext rs st st1 -> tinfo_local sf1 ->
       env_rel S2 (M.set x (Vconstr t vs) rho) env0 sf1 st1 -> room st1 tinfo (Z.of_N k) ->
       fgoal ctx va G P lo rest tmt K st1 sf1 stk) ->
    fgoal ctx va G P lo (ccode (alloc_code go ga fs env0 fresh x t ys) ++ rest) tmt K st sf stk.
  Proof.
    intros HP HI Htl Hroom Htag Har Hxf Hget Hne Hrel HyS Hyflat Hnc Hx HS' Hk.
    pose proof HI as (Hhi & Hok & Hmem & Hdis & Hfp & Hss & Hsk & Hroots).
    destruct Hroom as (alloc & limit & Ha & Hl & Hroom).
    pose proof Hok as (Hflds & _ & alloc' & limit' & Ha' & Hl' & Halign & Hle & Hinh & Hwr & _).
    rewrite (LLVM_sim.field_det tinfo st off_alloc alloc' alloc Ha' Ha) in *.
    rewrite (LLVM_sim.field_det tinfo st off_limit limit' limit Hl' Hl) in *.
    clear alloc' limit' Ha' Hl'.
    pose proof Ha as (aA & HaA & HrA). pose proof Hl as (aL & HaL & HrL).
    pose proof (LLVM_sim.ptr_off_int _ _ _ HaA) as EaA. pose proof (LLVM_sim.ptr_off_int _ _ _ HaL) as EaL.
    unfold off_alloc, off_limit in EaA, EaL.
    set (n := length ys) in *.
    assert (Hnw : hd_nwords ys = N.of_nat (Datatypes.S n)) by (unfold hd_nwords, n; lia).
    pose proof (ptr_to_int_range limit) as Rl. pose proof (ptr_to_int_range alloc) as Ra.
    assert (Hroom' : ptr_to_int limit - ptr_to_int alloc >= 8 * (Z.of_nat (Datatypes.S n) + Z.of_N k)).
    { rewrite Hnw in Hroom. rewrite N2Z.inj_add, nat_N_Z in Hroom. exact Hroom. }
    assert (Hk0 : 0 <= Z.of_N k) by lia.
    assert (Hwild : ptr_provenance alloc = wildcard_prov) by (eapply reads_ptr_wild; eauto).
    assert (Hnurs : forall b, ptr_to_int alloc <= b < ptr_to_int limit -> nursery st tinfo b).
    { intros b Hb. exists alloc, limit. auto. }
    assert (Hnt : forall b, ptr_to_int alloc <= b < ptr_to_int limit ->
                            ~ (ptr_to_int tinfo <= b < ptr_to_int tinfo + 8232)).
    { intros b Hb. apply Hdis, Hnurs, Hb. }
    assert (Hdq : forall q, ptr_to_int alloc <= ptr_to_int q -> ptr_to_int q + 8 <= ptr_to_int limit ->
                  forall a off, 0 <= off -> off + 8 <= 8232 -> ptr_to_int a = ptr_to_int tinfo + off ->
                  LLVM_instr_lemmas.disj8 q a).
    { intros q H1 H2 a off Ho1 Ho2 Ea. eapply disj8_tinfo; [|exact Ho1|exact Ho2|exact Ea].
      intros b Hb. apply Hnt. lia. }
    (* pointers *)
    destruct (LLVM_sim.ptr_off_ex alloc 8) as (p & HaP); [lia|].
    pose proof (LLVM_sim.ptr_off_int _ _ _ HaP) as EP.
    destruct (LLVM_sim.ptr_off_ex alloc (8 * Z.of_nat (Datatypes.S n))) as (alloc2 & Ha2); [lia|].
    pose proof (LLVM_sim.ptr_off_int _ _ _ Ha2) as E2.
    (* frames *)
    set (sf7 := upd_local_sf sf (Maps.add (ssname fresh 7) (Ptr alloc) (stack_vars sf))).
    set (sf8 := upd_local_sf sf7 (Maps.add (ssname fresh 8) (Ptr p) (stack_vars sf7))).
    set (sfx := upd_local_sf sf8 (Maps.add (Raw (Zpos x)) (I64 (ptr_to_int p)) (stack_vars sf8))).
    set (sf9 := upd_local_sf sfx (Maps.add (ssname fresh 9) (Ptr alloc2) (stack_vars sfx))).
    assert (F7_8 : RM.find (ssname fresh 7) (stack_vars sf8) = Some (Ptr alloc)).
    { unfold sf8, sf7. rewrite !LLVM_instr_lemmas.stack_vars_upd, LLVM_instr_lemmas.rfind_add_neq, LLVM_instr_lemmas.rfind_add_eq;
        [reflexivity|]. intros E. apply ssname_inj in E. lia. }
    assert (F8_8 : RM.find (ssname fresh 8) (stack_vars sf8) = Some (Ptr p)).
    { unfold sf8. rewrite LLVM_instr_lemmas.stack_vars_upd, LLVM_instr_lemmas.rfind_add_eq. reflexivity. }
    assert (F7_x : RM.find (ssname fresh 7) (stack_vars sfx) = Some (Ptr alloc)).
    { unfold sfx. rewrite LLVM_instr_lemmas.stack_vars_upd, LLVM_instr_lemmas.rfind_add_neq; [exact F7_8|]. apply not_eq_sym, ssname_not_pos. }
    assert (F8_x : RM.find (ssname fresh 8) (stack_vars sfx) = Some (Ptr p)).
    { unfold sfx. rewrite LLVM_instr_lemmas.stack_vars_upd, LLVM_instr_lemmas.rfind_add_neq; [exact F8_8|]. apply not_eq_sym, ssname_not_pos. }
    assert (F9_9 : RM.find (ssname fresh 9) (stack_vars sf9) = Some (Ptr alloc2)).
    { unfold sf9. rewrite LLVM_instr_lemmas.stack_vars_upd, LLVM_instr_lemmas.rfind_add_eq. reflexivity. }
    assert (Htl7 : tinfo_local sf7) by (apply LLVM_sim.tinfo_local_write; [exact Htl|unfold ssname; discriminate]).
    assert (Htl8 : tinfo_local sf8) by (apply LLVM_sim.tinfo_local_write; [exact Htl7|unfold ssname; discriminate]).
    assert (Htlx : tinfo_local sfx) by (apply LLVM_sim.tinfo_local_write; [exact Htl8|discriminate]).
    assert (Htl9 : tinfo_local sf9) by (apply LLVM_sim.tinfo_local_write; [exact Htlx|unfold ssname; discriminate]).
    assert (Hrel8 : env_rel S1 rho env0 sf8 st).
    { apply LLVM_sim.env_rel_write; [apply LLVM_sim.env_rel_write; [exact Hrel|]|];
        intros y Hy Hf; apply (Hnc y Hy Hf). }
    destruct (env_rel_words S1 rho env0 sf8 stk st ys vs Hrel8 HyS Hget) as (zs & Hzs & Hsz).
    assert (Hlz : length zs = n) by (symmetry; eapply Forall2_length; eauto).
    destruct (slot_ptrs_ex p 0 n) as (qs & Lqs & Sqs); [cbn [Nat.add]; lia|].
    pose proof (slot_ptrs_range _ _ _ Sqs) as Rqs. rewrite Lqs in Rqs. cbn [Nat.add] in Rqs.
    assert (Hqn : forall q, In q qs -> ptr_to_int alloc + 8 <= ptr_to_int q /\ ptr_to_int q + 8 <= ptr_to_int alloc + 8 * Z.of_nat (Datatypes.S n)).
    { intros q Hq. rewrite Forall_forall in Rqs. destruct (Rqs q Hq) as (j & Hj & Eq). rewrite Nat2Z.inj_succ. lia. }
    set (hw := Z.of_nat (Nat.lor (Nat.shiftl (N.to_nat (ga t)) 10) (N.to_nat (go t)))).
    assert (Ehw : hw = Z.of_N (ga t) * 1024 + Z.of_N (go t)).
    { unfold hw. destruct Htag as (_ & Ho & _). rewrite header_lor, !N_nat_Z; [reflexivity|]. lia. }
    rewrite ccode_alloc_code. cbn [app]. rewrite <- app_assoc. cbn [app].
    (* 1: a7 := load alloc *)
    assert (Ev7 : forall st0 sf0 t0, tinfo_local sf0 -> exp_eval st0 sf0 stk G t0 (cexp (gep_tinfo 0)) (Ptr aA)).
    { intros. eapply eval_gep_tinfo_field; [eassumption|left; reflexivity|exact HaA]. }
    eapply fgoal_instr; [exact HP| | |apply (LLVM_instr_lemmas.instr_load_ptr ctx va _ _ aA alloc); [apply Ev7, Htl|exact HrA]|].
    { split; [apply Flatten_sem.is_flat_ssname|apply noflat_gep_tinfo]. }
    { eexists. apply Ev7, Htl. }
    fold sf7.
    (* 2: header *)
    assert (Hw0 : writable_word st alloc).
    { apply (Hwr 0 alloc); [lia|]. rewrite Z.mul_0_r. apply LLVM_sim.ptr_off_0. }
    assert (Ehv : exp_eval st sf7 stk G (Some (DTYPE_I 64 : dtyp)) (cexp (header_word go ga t)) (I64 hw)).
    { rewrite cexp_header_word. unfold dlit. apply exp_eval_lit64. }
    assert (Ehp : forall st0, exp_eval st0 sf7 stk G (Some (DTYPE_Pointer : dtyp))
                    (cexp (gep_at (EXP_Ident (ID_Local (ssname fresh 7))) 0)) (Ptr alloc)).
    { intros st0. change 0%N with (N.of_nat 0). eapply eval_gep_at_local; [|lia|rewrite Z.mul_0_r; apply LLVM_sim.ptr_off_0].
      unfold sf7. rewrite LLVM_instr_lemmas.stack_vars_upd. apply LLVM_instr_lemmas.rfind_add_eq. }
    destruct (store_word_aid ctx va G 6 _ _ hw alloc st sf7 stk Ehv (Ehp st) Hw0) as (st2 & R2 & Rh2 & P2 & A2).
    eapply fgoal_instr; [exact HP| | |exact R2|].
    { split; [rewrite cexp_header_word; exact I|apply noflat_gep_at_ss]. }
    { split; eexists; [exact Ehv|apply Ehp]. }
    (* 3: a8 := alloc + 8 *)
    assert (Ev8 : exp_eval st2 sf7 stk G None (cexp (gep_at (EXP_Ident (ID_Local (ssname fresh 7))) 1)) (Ptr p)).
    { change 1%N with (N.of_nat 1). eapply eval_gep_at_local; [|lia|exact HaP].
      unfold sf7. rewrite LLVM_instr_lemmas.stack_vars_upd. apply LLVM_instr_lemmas.rfind_add_eq. }
    eapply fgoal_instr; [exact HP| | |apply LLVM_instr_lemmas.instr_op, Ev8|].
    { split; [apply Flatten_sem.is_flat_ssname|apply noflat_gep_at_ss]. }
    { eexists. exact Ev8. }
    fold sf8.
    (* 4: the fields *)
    eapply fgoal_stores with (l := combine qs zs); [exact HP| | | |].
    { eapply fstores_store_fields with (p := p); [| | exact Hzs | | | exact Sqs | lia].
      - intros st0. rewrite cexp_Ident. apply exp_eval_local, F8_8.
      - rewrite cexp_Ident. apply Flatten_sem.is_flat_ssname.
      - intros y Hy. apply noflat_gvar. intros Hf. apply Hyflat; auto.
      - cbn. lia. }
    { rewrite Forall_forall. intros [q w] Hin. apply in_combine_l in Hin. cbn [fst].
      apply In_nth_error in Hin. destruct Hin as (j & Hj).
      pose proof (slot_ptrs_nth _ _ _ _ _ Sqs Hj) as Hq.
      assert (Hjn : (j < n)%nat) by (rewrite <- Lqs; apply nth_error_Some; rewrite Hj; discriminate).
      apply P2. apply (Hwr (Z.of_nat (Datatypes.S j))); [rewrite Nat2Z.inj_succ in *; lia|].
      replace (8 * Z.of_nat (Datatypes.S j)) with (8 + 8 * Z.of_nat (0 + j)) by lia.
      exact (LLVM_sim.ptr_off_add alloc 8 p _ q HaP Hq). }
    { exact (LLVM_instr_lemmas.slot_ptrs_disj p 0 qs zs Sqs). }
    intros st3 [W3 A3] R3. rewrite LLVM_instr_lemmas.map_fst_combine in W3 by lia.
    (* 5: x := ptrtoint a8 *)
    assert (Evx : exp_eval st3 sf8 stk G None
                    (OP_Conversion (CONV_Impure Ptrtoint) (DTYPE_Pointer : dtyp) (EXP_Ident (ID_Local (ssname fresh 8))) (DTYPE_I 64 : dtyp))
                    (I64 (ptr_to_int p))).
    { apply exp_eval_ptrtoint, exp_eval_local, F8_8. }
    eapply fgoal_instr; [exact HP| | |apply LLVM_instr_lemmas.instr_op, Evx|].
    { split; [apply Flatten_sem.is_flat_pos|apply Flatten_sem.is_flat_ssname]. }
    { eexists. exact Evx. }
    fold sfx.
    (* 6: a9 := alloc + 8 (n+1) *)
    assert (Ev9 : exp_eval st3 sfx stk G None (cexp (gep_at (EXP_Ident (ID_Local (ssname fresh 7))) (hd_nwords ys))) (Ptr alloc2)).
    { rewrite Hnw. eapply eval_gep_at_local; [exact F7_x| |exact Ha2]. lia. }
    eapply fgoal_instr; [exact HP| | |apply LLVM_instr_lemmas.instr_op, Ev9|].
    { split; [apply Flatten_sem.is_flat_ssname|apply noflat_gep_at_ss]. }
    { eexists. exact Ev9. }
    fold sf9.
    (* 7: alloc := a9 *)
    assert (HwA : writable_word st3 aA).
    { apply W3, P2. apply (Hflds off_alloc aA); [left; reflexivity|exact HaA]. }
    assert (Ev9' : exp_eval st3 sf9 stk G (Some (DTYPE_Pointer : dtyp)) (EXP_Ident (ID_Local (ssname fresh 9))) (Ptr alloc2)).
    { apply exp_eval_local, F9_9. }
    destruct (store_ptr_aid ctx va G 7 _ _ alloc2 aA st3 sf9 stk Ev9' (Ev7 st3 sf9 _ Htl9) HwA)
      as (st4 & alloc2' & R4 & Ra4 & Ea4 & Pa4 & P4 & A4).
    eapply fgoal_instr; [exact HP| | |exact R4|].
    { split; [apply Flatten_sem.is_flat_ssname|apply noflat_gep_tinfo]. }
    { split; eexists; [exact Ev9'|apply Ev7, Htl9]. }
    (* the state after the allocation *)
    destruct P2 as (H2h & H2f & _ & H2m & H2w & H2r & H2p).
    destruct W3 as (H3h & H3f & _ & H3m & H3w & H3r & H3p).
    destruct P4 as (H4h & H4f & _ & H4m & H4w & H4r & H4p).
    set (W := fun b => (ptr_to_int alloc <= b < ptr_to_int alloc + 8 * Z.of_nat (Datatypes.S n)) \/ field_addr tinfo off_alloc b).
    assert (Hms : LLVM_sim.mstep st st4 W).
    { split; [congruence|]. split; [|split].
      - intros b Hb _. rewrite H4m, H3m, H2m; [reflexivity| | |].
        + intros Hb'. apply Hb. left. rewrite Nat2Z.inj_succ. lia.
        + rewrite Forall_forall. intros q Hq Hb'. apply Hb. left. destruct (Hqn q Hq). lia.
        + intros Hb'. apply Hb. right. unfold field_addr, off_alloc. lia.
      - intros b _. rewrite A4, A3, A2. reflexivity.
      - exists []. split; [rewrite LLVM_sim.push_top_nil; congruence|constructor]. }
    assert (Hfa2 : field st4 tinfo off_alloc alloc2') by (exists aA; auto).
    assert (Hrng : ptr_to_int alloc <= ptr_to_int alloc2' <= ptr_to_int limit).
    { rewrite Ea4, E2. rewrite Nat2Z.inj_succ in *. lia. }
    assert (Hal2 : ptr_to_int alloc2' mod 8 = 0).
    { rewrite Ea4, E2. replace (ptr_to_int alloc + 8 * Z.of_nat (Datatypes.S n)) with (ptr_to_int alloc + Z.of_nat (Datatypes.S n) * 8) by lia.
      rewrite Z_mod_plus_full. exact Halign. }
    assert (HW : forall b, W b -> mutator_writes st tinfo b).
    { intros b [Hb|Hb]; [left; apply Hnurs; rewrite Nat2Z.inj_succ in *; lia|right; left; exact Hb]. }
    assert (Hfpw : forall b, W b -> ~ field_addr tinfo off_fp b).
    { intros b [Hb|Hb] Hf; unfold field_addr, off_fp, off_alloc in *.
      - apply (Hnt b); [rewrite Nat2Z.inj_succ in *; lia|lia].
      - lia. }
    assert (HI4 : INV st4 fp rs vsr).
    { eapply (LLVM_sim.INV_mstep cenv fds heap_inv G tinfo Hmut Htinfo_range st st4 W fp rs vsr alloc alloc2' limit);
        eauto. rewrite Pa4, Hwild. reflexivity. }
    pose proof HI4 as (_ & _ & _ & _ & Hfp4 & Hss4 & _).
    destruct (LLVM_sim.INV_mstep_gen cenv fds heap_inv G tinfo Hmut Htinfo_range st st4 W fp rs vsr alloc alloc2' limit fp rs
                HI Hms HW Ha Hl Hfa2 Hrng Hal2 ltac:(rewrite Pa4, Hwild; reflexivity) Hfp4 Hss4)
      as (_ & _ & _ & _ & _ & _ & _ & Hnm & Hag).
    assert (Hheap4 : heap_of st4 = heap_of st) by congruence.
    (* the limit field survives *)
    assert (Hfl4 : field st4 tinfo off_limit limit).
    { exists aL. split; [exact HaL|]. apply H4p; [apply H3p; [apply H2p; [exact HrL|]|]|].
      - apply disj8_sym. apply (Hdq alloc) with (off := 8); [lia|rewrite Nat2Z.inj_succ in *; lia|lia|lia|exact EaL].
      - rewrite Forall_forall. intros q Hq. apply disj8_sym. destruct (Hqn q Hq).
        apply (Hdq q) with (off := 8); [lia|rewrite Nat2Z.inj_succ in *; lia|lia|lia|exact EaL].
      - unfold LLVM_instr_lemmas.disj8 in *. lia. }
    apply Hk.
    - exact HI4.
    - apply fext_of_mstep with W; [exact Hms|].
      intros b Hb. apply (LLVM_sim.mutator_in_heap tinfo Htinfo_range st b Hok (HW b Hb)).
    - exact Htl9.
    - apply LLVM_sim.env_rel_write.
      + apply (LLVM_sim.env_rel_bind cenv fds G tinfo S1 S2); auto.
        * eapply LLVM_sim.env_rel_mono; [exact Hrel8|exact Hag|exact Hheap4|exact Hnm].
        * intros y Hy Hf. apply (Hnc y Hy Hf).
        * eapply (LLVM_sim.stable_repr_boxed cenv prim_of fds G tinfo st st4 t vs zs alloc p); eauto.
          -- rewrite (get_list_length _ _ _ Hget). exact Har.
          -- intros E. subst vs. destruct ys; [congruence|discriminate (get_list_length _ _ _ Hget)].
          -- intros b Hb0. rewrite (get_list_length _ _ _ Hget) in Hb0.
             assert (Hb : ptr_to_int alloc <= b < ptr_to_int alloc + 8 * (Z.of_nat n + 1)) by exact Hb0. split.
             ++ apply Hinh. rewrite Nat2Z.inj_succ in *. lia.
             ++ intros [(al & li & Hal & Hli & Hb')|Ht].
                ** rewrite (LLVM_sim.field_det tinfo st4 off_alloc al alloc2' Hal Hfa2) in Hb'. lia.
                ** apply (Hnt b); [rewrite Nat2Z.inj_succ in *; unfold n in *; lia|exact Ht].
          -- rewrite <- Ehw. apply H4r; [apply H3r; [exact Rh2|]|].
             ++ rewrite Forall_forall. intros q Hq. destruct (Hqn q Hq). unfold LLVM_instr_lemmas.disj8. lia.
             ++ apply (Hdq alloc) with (off := 0); [lia|rewrite Nat2Z.inj_succ in *; lia|lia|lia|exact EaA].
          -- intros i z Hz.
             assert (Hi : (i < n)%nat) by (rewrite <- Hlz; apply nth_error_Some; rewrite Hz; discriminate).
             destruct (nth_error qs i) as [q|] eqn:Hq; [|apply nth_error_None in Hq; lia].
             exists q. split; [exact (slot_ptrs_nth _ _ _ _ _ Sqs Hq)|].
             rewrite Forall_forall in R3. pose proof (R3 _ (combine_nth_In _ _ _ _ _ Hq Hz)) as Rq. cbn in Rq.
             assert (Hqi : In q qs) by (eapply nth_error_In; eauto). destruct (Hqn q Hqi).
             apply H4r; [exact Rq|]. apply (Hdq q) with (off := 0); [lia|rewrite Nat2Z.inj_succ in *; lia|lia|lia|exact EaA].
      + intros y Hy Hf. destruct (HS' y Hy) as [->|HyS']; [rewrite Hx; apply not_eq_sym, ssname_not_pos|].
        apply (Hnc y HyS' Hf).
    - exists alloc2', limit. split; [exact Hfa2|]. split; [exact Hfl4|].
      rewrite Ea4, E2. rewrite Nat2Z.inj_succ in *. lia.
  Qed.

  Lemma fgoal_mono va (P1 P2 : MCFGbot (Res ((block_id * block_id) + dvalue)) -> Prop) lo l tmt K st sf stk :
    (forall t, P1 t -> P2 t) -> fgoal ctx va G P1 lo l tmt K st sf stk -> fgoal ctx va G P2 lo l tmt K st sf stk.
  Proof. intros H H1 c sf' Hc Hag. apply H, H1; assumption. Qed.

  (* ---------------------------------------------------------------- *)
  (** *** Chunk members: unchecked allocation *)

  Lemma sim_case_constr_member x t ys e' rho v vs :
    ys <> [] ->
    get_list ys rho = Some vs ->
    sim_stmt (M.set x (Vconstr t vs) rho) e' v ->
    forall env chunk fresh blks f' B va c st sf stk fp rs vsr,
      N.leb (hd_nwords ys) chunk = true ->
      body_ok cenv (Econstr x t ys e') ->
      subterm_or_eq (Econstr x t ys e') (Efun fds main) ->
      unique_bindings (Econstr x t ys e') ->
      Ensembles.Disjoint _ (bound_var (Econstr x t ys e')) (occurs_free (Econstr x t ys e')) ->
      env_ok (occurs_free (Econstr x t ys e')) env fresh ->
      tr env chunk (Econstr x t ys e') fresh = (blks, f') ->
      LLVM_sim.blocks_in B blks ->
      INV st fp rs vsr -> tinfo_local sf ->
      env_rel (occurs_free (Econstr x t ys e')) rho env sf st ->
      room st tinfo (Z.of_N chunk) ->
      sim_result st stk fp rs vsr v
        (interp_mcfg (interp_mrec ctx (LLVM_sim.tail_of va B (LLVM_sim.flatB (cblock (LLVM_sim.hd_blk blks)) c)))
                     (st, ((sf, stk), G))).
  Proof.
    intros Hne Hget IH env chunk fresh blks f' B va c st sf stk fp rs vsr Hleb
      Hbo Hsub Hub Hdis Henv Htr Hbin HI Htl Hrel Hroom.
    inversion Hbo as [? ? ? ? _ _ _ Hbo'| | | | | |]; subst.
    inversion Hub as [? ? ? ? Hxe Hub'| | | | | | | | |]; subst.
    destruct (tr env (chunk - hd_nwords ys) e' (Pos.succ fresh)) as [blks0 f0] eqn:E.
    rewrite (tr_constr_member go ga prim_of fs env chunk x t ys e' fresh blks0 f0 Hne Hleb E) in Htr.
    injection Htr as <- <-.
    destruct (translate_cfg_entry go ga prim_of fs env _ e' _ blks0 f0 E) as (b & rest & q & -> & _).
    destruct (env_cont_same x t ys e' env fresh (Pos.succ fresh) ltac:(lia) Hub Hdis Henv) as (Hfv & Hbv & Hx).
    destruct (cont_env x t ys e' env (Pos.succ fresh) (chunk - hd_nwords ys) (Pos.succ fresh) Hub Hdis Hfv Hbv)
      as (Henv' & Htr').
    rewrite <- Htr' in E.
    pose proof (constr_not_fun _ _ _ _ Hsub) as Hnfx.
    destruct (prog_constr _ _ _ _ Hsub) as [Htag Har].
    rewrite hd_prepend.
    change (interp_mcfg (interp_mrec ctx ?t) ?s) with (RUN t s).
    eapply sim_result_closed; [symmetry; apply tail_of_flat|].
    destruct (cblock_prepend (alloc_code go ga fs env fresh x t ys) b) as (E1 & E2 & E3).
    rewrite E1, E2, E3, cblock_id.
    match goal with |- sim_result _ _ _ _ _ _ (RUN (Flatten_sem.flat_tail _ ?l ?tm _ ?K) _) =>
      enough (Hf : fgoal ctx va G (sim_result st stk fp rs vsr v) c l tm K st sf stk)
        by (apply Hf; [lia|apply Flatten_sem.agree_except_refl]) end.
    apply N.leb_le in Hleb.
    refine (alloc_fgoal va _ c env fresh x t ys vs (chunk - hd_nwords ys)
              (occurs_free (Econstr x t ys e')) (occurs_free e') rho _ _ _ st sf stk fp rs vsr
              (sim_result_closed _ _ _ _ _ _) HI Htl _ Htag Har Hnfx Hget Hne Hrel _ _ _ Hx _ _).
    - replace (hd_nwords ys + (chunk - hd_nwords ys))%N with chunk by lia. exact Hroom.
    - intros y Hy. apply Free_Econstr1, Hy.
    - intros y _ _. eapply LLVM_sim.env_ok_not_flat; eauto.
    - intros y Hy Hf. split; [|split; [|split]].
      + eapply (LLVM_sim.env_ok_not_pos cenv prim_of); eauto.
        * apply x_not_free, Hdis.
        * intros ->. exact (x_not_free _ _ _ _ Hdis Hy).
      + eapply (LLVM_sim.env_ok_not_ssname cenv prim_of); eauto. lia.
      + eapply (LLVM_sim.env_ok_not_ssname cenv prim_of); eauto. lia.
      + eapply (LLVM_sim.env_ok_not_ssname cenv prim_of); eauto. lia.
    - intros y Hy. destruct (Pos.eq_dec y x) as [->|Hne']; [left; reflexivity|right].
      apply Free_Econstr2; auto.
    - intros st1 sf1 HI1 Hfx Htl1 Hrel1 Hroom1.
      eapply fgoal_mono; [intros t0 Ht0; eapply sim_result_ext; [exact Hfx|exact Ht0]|].
      eapply apply_ih with (env' := restrict env e') (chunk' := (chunk - hd_nwords ys)%N) (fresh' := Pos.succ fresh).
      + exact IH.
      + exact Hbo'.
      + eapply subterm_constr; exact Hsub.
      + exact Hub'.
      + eapply disjoint_constr; eauto.
      + exact Henv'.
      + exact E.
      + eapply blocks_in_prepend; exact Hbin.
      + exact HI1.
      + exact Htl1.
      + eapply env_rel_ext; [intros y Hy; symmetry; apply restrict_fv, Hy|exact Hrel1].
      + exact Hroom1.
  Qed.

  (* ---------------------------------------------------------------- *)
  (** *** Chunk heads: the allocation block *)

  Lemma hd_env_root env fresh x ys e' y i :
    nth_error (hd_roots fs x ys e') i = Some y -> hd_env fs env fresh x ys e' y = ssname fresh (2000 + i).
  Proof. intros H. unfold hd_env. apply safepoint_env_root; [apply hd_roots_nodup|exact H]. Qed.

  Lemma hd_env_other env fresh x ys e' y :
    ~ In y (hd_roots fs x ys e') -> hd_env fs env fresh x ys e' y = env y.
  Proof. intros H. unfold hd_env. apply safepoint_env_other, H. Qed.

  Lemma root_of_fv x t ys e' y :
    occurs_free (Econstr x t ys e') y -> is_fun fs y = false -> In y (hd_roots fs x ys e').
  Proof.
    intros Hy Hf. apply hd_roots_spec. split; [exact Hf|].
    inversion Hy; subst; [right; assumption|left; split; auto].
  Qed.

  Lemma root_fv x t ys e' y : In y (hd_roots fs x ys e') -> occurs_free (Econstr x t ys e') y.
  Proof.
    intros H. apply hd_roots_spec in H. destruct H as [_ [[H1 H2]|H]].
    - apply Free_Econstr2; auto.
    - apply Free_Econstr1, H.
  Qed.

  Lemma alloc_block_sim x t ys e' rho v vs env fresh f0 b0 rest0 c0 B va c_a st0 st sf stk fp rs vsr from wsd :
    sim_stmt (M.set x (Vconstr t vs) rho) e' v ->
    ys <> [] -> get_list ys rho = Some vs ->
    body_ok cenv e' -> subterm_or_eq (Econstr x t ys e') (Efun fds main) ->
    unique_bindings (Econstr x t ys e') ->
    Ensembles.Disjoint _ (bound_var (Econstr x t ys e')) (occurs_free (Econstr x t ys e')) ->
    env_ok (occurs_free (Econstr x t ys e')) env fresh ->
    tr (hd_env fs env fresh x ys e') (chunk_words e') e' (Pos.succ fresh) = (b0 :: rest0, f0) ->
    LLVM_sim.blocks_in B (b0 :: rest0) ->
    RM.find (blk_id b0) (ocfg_map B) = Some (LLVM_sim.flatB (cblock b0) c0) ->
    RM.find (Anon (Zpos (Pos.succ (Pos.succ f0)))) (ocfg_map B) =
      Some (LLVM_sim.flatB (cblock (hd_alloc_blk go ga fs env x t ys e' fresh f0 (entry_id (b0 :: rest0) f0))) c_a) ->
    INV st fp rs vsr -> fext rs st0 st -> tinfo_local sf ->
    room st tinfo (Z.of_N (hd_nwords ys + chunk_words e')) ->
    (forall y, occurs_free (Econstr x t ys e') y -> is_fun fs y = true -> exists rho', M.get y rho = Some (Vfun rho' fds y)) ->
    Forall2 (fun r w => exists v' z, w = I64 z /\ M.get r rho = Some v' /\ stable_repr st v' z)
            (hd_roots fs x ys e') wsd ->
    (from = Anon (Zpos f0) /\
       Forall2 (fun r w => RM.find (env r) (stack_vars sf) = Some w) (hd_roots fs x ys e') wsd) \/
    (from = Anon (Zpos (Pos.succ f0)) /\
       Forall2 (fun j w => RM.find (ssname fresh (1000 + j)) (stack_vars sf) = Some w)
               (seq 0 (length (hd_roots fs x ys e'))) wsd) ->
    sim_result st0 stk fp rs vsr v
      (RUN (denote_ocfg B va (from, Anon (Zpos (Pos.succ (Pos.succ f0))))) (st, ((sf, stk), G))).
  Proof.
    intros IH Hne Hget Hbo' Hsub Hub Hdis Henv Etr Hbin Hb0 Ha HI Hfx Htl Hroom Hfun Hws Hfrom.
    inversion Hub as [? ? ? ? Hxe Hub'| | | | | | | | |]; subst.
    set (roots := hd_roots fs x ys e') in *.
    set (env2 := hd_env fs env fresh x ys e') in *.
    pose proof (constr_not_fun _ _ _ _ Hsub) as Hnfx.
    destruct (prog_constr _ _ _ _ Hsub) as [Htag Har].
    assert (Hxnr : ~ In x roots).
    { intros H. apply (x_not_free _ _ _ _ Hdis). apply (root_fv x t ys e' x H). }
    assert (Hx : env2 x = Raw (Zpos x)).
    { unfold env2. rewrite hd_env_other by exact Hxnr. destruct (Henv x) as [_ H]. apply H, x_not_free, Hdis. }
    (* the continuation's environment *)
    destruct (cont_env x t ys e' env2 (Pos.succ fresh) (chunk_words e') (Pos.succ fresh) Hub Hdis) as (Henv' & Htr').
    { intros y Hy. destruct (in_dec Pos.eq_dec y roots) as [Hr|Hr].
      - apply In_nth_error in Hr. destruct Hr as (i & Hi). right. exists fresh, (2000 + i)%nat.
        split; [lia|apply hd_env_root, Hi].
      - unfold env2. rewrite hd_env_other by exact Hr.
        destruct (env_cont_same x t ys e' env fresh (Pos.succ fresh) ltac:(lia) Hub Hdis Henv) as (H & _). apply H, Hy. }
    { intros y Hy. assert (Hr : ~ In y roots).
      { intros Hr. eapply disj_elim; [exact Hdis|apply Bound_Econstr2, Hy|apply (root_fv x t ys e' y Hr)]. }
      unfold env2. rewrite hd_env_other by exact Hr.
      destruct (env_cont_same x t ys e' env fresh fresh ltac:(lia) Hub Hdis Henv) as (_ & H & _). apply H, Hy. }
    rewrite <- Htr' in Etr.
    (* the phis *)
    set (sfa := upd_local_sf sf (LLVM_instr_lemmas.phi_upd (LLVM_instr_lemmas.phi_ivs fresh 0 wsd) (stack_vars sf))).
    assert (Hphis : blk_phis (LLVM_sim.flatB (cblock (hd_alloc_blk go ga fs env x t ys e' fresh f0 (entry_id (b0 :: rest0) f0))) c_a)
                    = LLVM_instr_lemmas.phi_list_d env fresh (Anon (Zpos f0)) (Anon (Zpos (Pos.succ f0))) 0 roots).
    { rewrite LLVM_sim.flatB_phis, cblock_eq. cbn [blk_phis hd_alloc_blk]. apply LLVM_instr_lemmas.cphi_list. }
    eapply run_phis_jump; [apply sim_result_closed|exact Ha| |].
    { rewrite Hphis. destruct Hfrom as [[-> Hf]|[-> Hf]].
      - apply LLVM_instr_lemmas.runs_phi_list_chk, Hf.
      - apply LLVM_instr_lemmas.runs_phi_list_gc; [|exact Hf]. intros E. injection E. lia. }
    fold sfa.
    change (interp_mcfg (interp_mrec ctx ?t) ?s) with (RUN t s).
    eapply sim_result_closed; [symmetry; apply tail_of_flat|].
    rewrite cblock_eq. cbn [blk_code blk_term blk_id hd_alloc_blk]. rewrite cterm_Br_1.
    rewrite <- (app_nil_r (ccode _)).
    match goal with |- sim_result _ _ _ _ _ _ (RUN (Flatten_sem.flat_tail _ ?l ?tm _ ?K) _) =>
      enough (Hf : fgoal ctx va G (sim_result st0 stk fp rs vsr v) c_a l tm K st sfa stk)
        by (apply Hf; [lia|apply Flatten_sem.agree_except_refl]) end.
    (* lookups of the roots after the phis *)
    assert (Hroot : forall y i, nth_error roots i = Some y ->
               exists v' z, env2 y = ssname fresh (2000 + i) /\ RM.find (env2 y) (stack_vars sfa) = Some (I64 z) /\
                            M.get y rho = Some v' /\ stable_repr st v' z).
    { intros y i Hi. destruct (LLVM_sim.nth_error_Forall2 _ _ _ _ _ Hws Hi) as (w & Hw & (v' & z & -> & Hv & Hs)).
      exists v', z. assert (E : env2 y = ssname fresh (2000 + i)) by (apply hd_env_root, Hi).
      split; [exact E|]. split; [|split; assumption].
      rewrite E. unfold sfa. rewrite LLVM_instr_lemmas.stack_vars_upd.
      replace (2000 + i)%nat with (2000 + (0 + i))%nat by lia. apply phi_upd_ivs, Hw. }
    assert (Hrel : env_rel (occurs_free (Econstr x t ys e')) rho env2 sfa st).
    { intros y Hy. destruct (is_fun fs y) eqn:Ef.
      - destruct (Hfun y Hy Ef) as (rho' & Hv). exists (Vfun rho' fds y). split; [exact Hv|]. eauto.
      - pose proof (root_of_fv x t ys e' y Hy Ef) as Hr. apply In_nth_error in Hr. destruct Hr as (i & Hi).
        destruct (Hroot y i Hi) as (v' & z & _ & Hz & Hv & Hs). exists v'. split; [exact Hv|]. eauto. }
    refine (alloc_fgoal va _ c_a env2 fresh x t ys vs (chunk_words e')
              (occurs_free (Econstr x t ys e')) (occurs_free e') rho _ _ _ st sfa stk fp rs vsr
              (sim_result_closed _ _ _ _ _ _) HI _ Hroom Htag Har Hnfx Hget Hne Hrel _ _ _ Hx _ _).
    - unfold sfa. unfold tinfo_local, LLVM_sim.tinfo_local. rewrite LLVM_instr_lemmas.stack_vars_upd, phi_upd_other; [exact Htl|].
      intros iv Hin. assert (H : forall i' ws', In iv (LLVM_instr_lemmas.phi_ivs fresh i' ws') -> exists k, fst iv = ssname fresh k).
      { intros i' ws'. revert i'. induction ws' as [|w ws' IHw]; intros i' H; [destruct H|].
        destruct H as [<-|H]; [eexists; reflexivity|eapply IHw; eauto]. }
      destruct (H 0%nat wsd Hin) as (k & E). intros E'. pose proof (eq_trans (eq_sym E) E') as E2.
      unfold ssname in E2. discriminate.
    - intros y Hy. apply Free_Econstr1, Hy.
    - intros y Hy Hf. pose proof (root_of_fv x t ys e' y (Free_Econstr1 _ _ _ _ _ Hy) Hf) as Hr.
      apply In_nth_error in Hr. destruct Hr as (i & Hi). destruct (Hroot y i Hi) as (_ & _ & E & _).
      rewrite E. apply Flatten_sem.is_flat_ssname.
    - intros y Hy Hf. pose proof (root_of_fv x t ys e' y Hy Hf) as Hr.
      apply In_nth_error in Hr. destruct Hr as (i & Hi). destruct (Hroot y i Hi) as (_ & _ & E & _).
      rewrite E. split; [apply ssname_not_pos|].
      split; [|split]; intros E'; apply ssname_inj in E'; destruct E' as [_ E']; lia.
    - intros y Hy. destruct (Pos.eq_dec y x) as [->|Hne']; [left; reflexivity|right].
      apply Free_Econstr2; auto.
    - intros st1 sf1 HI1 Hfx1 Htl1 Hrel1 Hroom1.
      eapply fgoal_term; [apply sim_result_closed|exact I|exact I|apply LLVM_instr_lemmas.term_br_1|].
      intros sf1' Hag1. cbn [LLVM_sim.continue]. cbn [entry_id].
      eapply run_jump; [apply sim_result_closed|exact Hb0|rewrite LLVM_sim.flatB_phis, cblock_eq;
        destruct (translate_cfg_entry go ga prim_of fs _ _ e' _ _ _ Etr) as (b' & rest' & q' & E' & Hp' & _);
        injection E' as <- <-; cbn [blk_phis]; rewrite Hp'; reflexivity|].
      change (interp_mcfg (interp_mrec ctx ?t) ?s) with (RUN t s).
      eapply sim_result_closed; [symmetry; apply tail_of_flat|].
      eapply sim_result_ext; [eapply fext_trans; [exact Hfx|exact Hfx1]|].
      rewrite cblock_id.
      eapply (apply_ih (M.set x (Vconstr t vs) rho) e' v (restrict env2 e') (chunk_words e') (Pos.succ fresh) b0 rest0 f0
                B va st1 sf1' stk fp rs vsr c0); eauto.
      + eapply subterm_constr; exact Hsub.
      + eapply disjoint_constr; eauto.
      + apply (LLVM_sim.tinfo_local_noflat _ _ _ Htl1 Hag1).
      + eapply (LLVM_sim.env_rel_noflat cenv fds G tinfo _ _ _ _ _ _ _ _ Henv'); [|exact Hag1].
        eapply env_rel_ext; [intros y Hy; symmetry; apply restrict_fv, Hy|exact Hrel1].
      + lia.
      + apply Flatten_sem.agree_except_refl.
  Qed.

  (* ---------------------------------------------------------------- *)
  (** *** Chunk heads: the check block *)

  Lemma roots_words S rho env0 sf st roots :
    env_rel S rho env0 sf st -> (forall r, In r roots -> S r /\ is_fun fs r = false) ->
    exists wsd, Forall2 (fun r w => RM.find (env0 r) (stack_vars sf) = Some w) roots wsd /\
                Forall2 (fun r w => exists v' z, w = I64 z /\ M.get r rho = Some v' /\ stable_repr st v' z) roots wsd.
  Proof.
    intros Hrel. induction roots as [|r roots IH]; intros H; [exists []; split; constructor|].
    destruct IH as (wsd & H1 & H2); [intros; apply H; right; auto|].
    destruct (H r (or_introl eq_refl)) as [Hr Hf].
    destruct (Hrel r Hr) as (v' & Hv & Hc). rewrite Hf in Hc. destruct Hc as (z & Hz & Hs).
    exists (I64 z :: wsd). split; constructor; eauto.
  Qed.

  (* ---------------------------------------------------------------- *)
  (** *** Chunk heads: linking the safepoint frame *)

  Lemma tinfo_field_alloc st off a :
    tinfo_ok st tinfo -> In off [off_alloc; off_limit; off_fp; off_nalloc] -> ptr_off tinfo off a ->
    forall b, ptr_to_int a <= b < ptr_to_int a + 8 -> IntMaps.lookup b (mem_of st) <> None.
  Proof.
    intros (Hf & _) Hoff Ha. destruct (Hf off a Hoff Ha) as [W _]. apply LLVM_sim.writable_word_alloc, W.
  Qed.

  Lemma link_fgoal va P lo env fresh roots st st1 st2 sf stk fp rs vsr pR pF rest tmt K vs1 zs1 cwz :
    closedP P ->
    INV st fp rs vsr ->
    LLVM_instr_lemmas.alloc_post st st1 (8 * N.of_nat (length roots)) pR ->
    LLVM_instr_lemmas.alloc_post st1 st2 24 pF ->
    RM.find (ssname fresh 1) (stack_vars sf) = Some (Ptr pR) ->
    RM.find (ssname fresh 2) (stack_vars sf) = Some (Ptr pF) ->
    tinfo_local sf ->
    Forall2 (fun r z => RM.find (env r) (stack_vars sf) = Some (I64 z)) roots zs1 ->
    Forall2 (stable_repr st) vs1 zs1 ->
    (forall r, In r roots -> Flatten_sem.is_flat (env r) = false) ->
    (forall st6 f e s rs1,
       INV st6 f (rs1 ++ rs) (vs1 ++ vsr) ->
       LLVM_sim.frame_fields st6 f e s fp -> slots_from st6 s e rs1 ->
       ptr_to_int f = ptr_to_int pF -> length rs1 = length roots ->
       (forall i r, nth_error rs1 i = Some r -> ptr_to_int r = ptr_to_int pR + 8 * Z.of_nat i) ->
       (exists aN, ptr_off tinfo off_nalloc aN /\ reads_word st6 aN (Z.of_nat cwz)) ->
       LLVM_sim.mstep st st6 (fun a => field_addr tinfo off_fp a \/ field_addr tinfo off_nalloc a) ->
       (forall b, aid_at st6 b = aid_at st2 b) ->
       ptr_to_int pR + 8 * Z.of_nat (length roots) < 2 ^ 64 ->
       fgoal ctx va G P lo rest tmt K st6 (upd_local_sf sf (Maps.add (ssname fresh 10) (Ptr fp) (stack_vars sf))) stk) ->
    fgoal ctx va G P lo
      (ccode (spill_code env (EXP_Ident (ID_Local (ssname fresh 1))) (TYPE_Array (N.of_nat (length roots)) val_ty) 0 roots) ++
       (IVoid 0%Z, INSTR_Store ((DTYPE_Pointer : dtyp), cexp (gep_arr (TYPE_Array (N.of_nat (length roots)) val_ty) (EXP_Ident (ID_Local (ssname fresh 1))) (length roots)))
                     ((DTYPE_Pointer : dtyp), cexp (gep_struct frame_ty (EXP_Ident (ID_Local (ssname fresh 2))) 0)) [], [])
       :: (IVoid 0%Z, INSTR_Store ((DTYPE_Pointer : dtyp), cexp (gep_arr (TYPE_Array (N.of_nat (length roots)) val_ty) (EXP_Ident (ID_Local (ssname fresh 1))) 0))
                     ((DTYPE_Pointer : dtyp), cexp (gep_struct frame_ty (EXP_Ident (ID_Local (ssname fresh 2))) 1)) [], [])
       :: (IId (ssname fresh 10), INSTR_Load (DTYPE_Pointer : dtyp) ((DTYPE_Pointer : dtyp), cexp (gep_tinfo 4)) [], [])
       :: (IVoid 0%Z, INSTR_Store ((DTYPE_Pointer : dtyp), EXP_Ident (ID_Local (ssname fresh 10)))
                     ((DTYPE_Pointer : dtyp), cexp (gep_struct frame_ty (EXP_Ident (ID_Local (ssname fresh 2))) 2)) [], [])
       :: (IVoid 0%Z, INSTR_Store ((DTYPE_Pointer : dtyp), EXP_Ident (ID_Local (ssname fresh 2))) ((DTYPE_Pointer : dtyp), cexp (gep_tinfo 4)) [], [])
       :: (IVoid 0%Z, INSTR_Store ((DTYPE_I 64 : dtyp), dlit cwz) ((DTYPE_Pointer : dtyp), cexp (gep_tinfo 5)) [], [])
       :: rest) tmt K st2 sf stk.
  Proof.
    intros HP HI AP1 AP2 F1 F2 Htl Hzs Hvs Hfl Hk.
    pose proof HI as (Hhi & Hok & Hmem & Hdis & Hfp & Hss & Hsk & Hroots).
    pose proof Hok as (Hflds & _ & alloc & limit & Ha0 & Hl0 & Halign & Hle & Hinh & Hwr & _).
    pose proof Ha0 as (aA & HaA & HrA). pose proof Hfp as (aFP & HaFP & HrFP).
    destruct (LLVM_sim.tinfo_field_ex tinfo Htinfo_range off_nalloc ltac:(unfold off_nalloc; lia) ltac:(unfold off_nalloc; lia)) as (aN & HaN).
    pose proof (LLVM_sim.ptr_off_int _ _ _ HaA) as EaA. pose proof (LLVM_sim.ptr_off_int _ _ _ HaFP) as EaFP.
    pose proof (LLVM_sim.ptr_off_int _ _ _ HaN) as EaN.
    unfold off_alloc, off_fp, off_nalloc in EaA, EaFP, EaN.
    set (nr := length roots) in *.
    destruct (alloc_post_access _ _ _ _ AP1) as (BR & ACR). destruct (alloc_post_access _ _ _ _ AP2) as (BF & ACF).
    pose proof AP1 as (_ & _ & FrR & OutR & _). pose proof AP2 as (_ & _ & FrF & OutF & _).
    rewrite N2Z.inj_mul, nat_N_Z in BR, ACR, OutR. change (Z.of_N 24) with 24 in BF, ACF, OutF.
    (* allocated in st => below pR; allocated in st1 => below pF *)
    assert (Lst : forall b, IntMaps.lookup b (mem_of st) <> None -> b < ptr_to_int pR).
    { intros b Hb. destruct (Z_lt_le_dec b (ptr_to_int pR)) as [|Hge]; [assumption|]. exfalso. apply Hb, FrR, Hge. }
    assert (Lst1 : forall b, IntMaps.lookup b (mem_of st1) <> None -> b < ptr_to_int pF).
    { intros b Hb. destruct (Z_lt_le_dec b (ptr_to_int pF)) as [|Hge]; [assumption|]. exfalso. apply Hb, FrF, Hge. }
    assert (A01 : forall b, IntMaps.lookup b (mem_of st) <> None -> IntMaps.lookup b (mem_of st1) <> None).
    { intros b Hb. rewrite (LLVM_instr_lemmas.alloc_post_allocated _ _ _ _ _ AP1 Hb). exact Hb. }
    assert (Aid12 : forall b, IntMaps.lookup b (mem_of st1) <> None -> aid_at st2 b = aid_at st1 b).
    { intros b Hb. unfold aid_at. rewrite (LLVM_instr_lemmas.alloc_post_allocated _ _ _ _ _ AP2 Hb). reflexivity. }
    assert (Aid01 : forall b, IntMaps.lookup b (mem_of st) <> None -> aid_at st1 b = aid_at st b).
    { intros b Hb. unfold aid_at. rewrite (LLVM_instr_lemmas.alloc_post_allocated _ _ _ _ _ AP1 Hb). reflexivity. }
    assert (RinF : forall b, ptr_to_int pR <= b < ptr_to_int pR + 8 * Z.of_nat nr -> b < ptr_to_int pF).
    { intros b Hb. apply Lst1. destruct (ACR b Hb) as (aid & Ha & _). unfold aid_at in Ha.
      destruct (IntMaps.lookup b (mem_of st1)); [discriminate|discriminate]. }
    assert (HRF : nr = 0%nat \/ ptr_to_int pR + 8 * Z.of_nat nr <= ptr_to_int pF).
    { destruct nr as [|k] eqn:En; [left; reflexivity|right].
      pose proof (RinF (ptr_to_int pR + 8 * Z.of_nat (S k) - 1)). rewrite Nat2Z.inj_succ in *. lia. }
    assert (Hfa : forall off a, In off [off_alloc; off_limit; off_fp; off_nalloc] -> ptr_off tinfo off a ->
                  ptr_to_int a + 8 <= ptr_to_int pR /\ ptr_to_int a + 8 <= ptr_to_int pF).
    { intros off a Hoff Ha.
      assert (Hb : IntMaps.lookup (ptr_to_int a + 7) (mem_of st) <> None).
      { apply (tinfo_field_alloc st off a Hok Hoff Ha). lia. }
      pose proof (Lst _ Hb). pose proof (Lst1 _ (A01 _ Hb)). lia. }
    destruct (Hfa off_alloc aA ltac:(left; reflexivity) HaA) as [BA1 BA2].
    destruct (Hfa off_fp aFP ltac:(right; right; left; reflexivity) HaFP) as [BP1 BP2].
    destruct (Hfa off_nalloc aN ltac:(right; right; right; left; reflexivity) HaN) as [BN1 BN2].
    pose proof (ptr_to_int_range pR) as RgR. pose proof (ptr_to_int_range pF) as RgF.
    assert (BR' : ptr_to_int pR + 8 * Z.of_nat nr < 2 ^ 64) by (destruct HRF as [->|H]; lia).
    (* the slots *)
    destruct (slot_ptrs_ex pR 0 nr) as (qs & Lqs & Sqs); [cbn [Nat.add]; lia|].
    pose proof (slot_ptrs_range _ _ _ Sqs) as Rqs. rewrite Lqs in Rqs. cbn [Nat.add] in Rqs.
    assert (Hqs : forall q, In q qs -> ptr_to_int pR <= ptr_to_int q /\ ptr_to_int q + 8 <= ptr_to_int pR + 8 * Z.of_nat nr
                                       /\ ptr_provenance q = ptr_provenance pR).
    { intros q Hq. pose proof Hq as Hq'. rewrite Forall_forall in Rqs. destruct (Rqs q Hq) as (j & Hj & Eq).
      apply In_nth_error in Hq'. destruct Hq' as (i & Hi). pose proof (slot_ptrs_nth _ _ _ _ _ Sqs Hi) as Ho.
      split; [lia|split; [lia|apply LLVM_sim.ptr_off_prov in Ho; exact Ho]]. }
    assert (Hlz : length zs1 = nr) by (symmetry; eapply Forall2_length; eauto).
    eapply fgoal_stores with (l := combine qs zs1); [exact HP| | | |].
    { eapply fstores_spill with (p := pR); [exact F1|exact Hzs|exact Hfl|apply Flatten_sem.is_flat_ssname| |exact Sqs|lia].
      cbn [Nat.add]. lia. }
    { rewrite Forall_forall. intros [q w] Hin. apply in_combine_l in Hin. cbn [fst].
      destruct (Hqs q Hin) as (H1 & H2 & H3). apply writable_word_of; [lia|].
      intros b Hb. destruct (ACR b ltac:(lia)) as (aid & Ha & Hacc). exists aid. rewrite H3. split; [|exact Hacc].
      rewrite Aid12; [exact Ha|]. unfold aid_at in Ha. destruct (IntMaps.lookup b (mem_of st1)); discriminate. }
    { exact (LLVM_instr_lemmas.slot_ptrs_disj pR 0 qs zs1 Sqs). }
    intros st3 [W3 A3] R3. rewrite LLVM_instr_lemmas.map_fst_combine in W3 by lia.
    destruct W3 as (H3h & H3f & _ & H3m & H3w & H3r & H3p).
    (* frame word access *)
    assert (AF3 : forall q, ptr_provenance q = ptr_provenance pF -> ptr_to_int pF <= ptr_to_int q ->
                  ptr_to_int q + 8 <= ptr_to_int pF + 24 -> forall st', (forall b, aid_at st' b = aid_at st3 b) -> writable_word st' q).
    { intros q Hp H1 H2 st' Ast. apply writable_word_of; [lia|]. intros b Hb.
      destruct (ACF b ltac:(lia)) as (aid & Ha & Hacc). exists aid. rewrite Hp. split; [|exact Hacc].
      rewrite Ast, A3. exact Ha. }
    (* s1 *)
    destruct (LLVM_sim.ptr_off_ex pR (8 * Z.of_nat nr)) as (eR & HeR); [lia|].
    assert (Ev1 : exp_eval st3 sf stk G (Some (DTYPE_Pointer : dtyp))
                    (cexp (gep_arr (TYPE_Array (N.of_nat nr) val_ty) (EXP_Ident (ID_Local (ssname fresh 1))) nr)) (Ptr eR)).
    { eapply eval_gep_arr_local; [exact F1|lia|exact HeR]. }
    assert (Ep1 : forall st0, exp_eval st0 sf stk G (Some (DTYPE_Pointer : dtyp))
                    (cexp (gep_struct frame_ty (EXP_Ident (ID_Local (ssname fresh 2))) 0)) (Ptr pF)).
    { intros st0. eapply eval_gep_struct_local; [exact F2|lia|]. rewrite Z.mul_0_r. apply LLVM_sim.ptr_off_0. }
    destruct (store_ptr_aid ctx va G 0 _ _ eR pF st3 sf stk Ev1 (Ep1 st3) (AF3 pF eq_refl ltac:(lia) ltac:(lia) st3 (fun _ => eq_refl)))
      as (st4 & eR4 & R4 & Rd4 & Ee4 & Pe4 & P4 & A4).
    eapply fgoal_instr; [exact HP| |split; eexists; [exact Ev1|apply Ep1]|exact R4|].
    { split; [apply noflat_gep_arr_ss|apply noflat_gep_struct_ss]. }
    destruct P4 as (H4h & H4f & _ & H4m & H4w & H4r & H4p).
    (* s2 *)
    destruct (LLVM_sim.ptr_off_ex pF 8) as (pF8 & HpF8); [lia|].
    pose proof (LLVM_sim.ptr_off_int _ _ _ HpF8) as EpF8.
    assert (Ev2 : exp_eval st4 sf stk G (Some (DTYPE_Pointer : dtyp))
                    (cexp (gep_arr (TYPE_Array (N.of_nat nr) val_ty) (EXP_Ident (ID_Local (ssname fresh 1))) 0)) (Ptr pR)).
    { eapply eval_gep_arr_local; [exact F1|lia|]. rewrite Z.mul_0_r. apply LLVM_sim.ptr_off_0. }
    assert (Ep2 : exp_eval st4 sf stk G (Some (DTYPE_Pointer : dtyp))
                    (cexp (gep_struct frame_ty (EXP_Ident (ID_Local (ssname fresh 2))) 1)) (Ptr pF8)).
    { eapply eval_gep_struct_local; [exact F2|lia|exact HpF8]. }
    destruct (store_ptr_aid ctx va G 0 _ _ pR pF8 st4 sf stk Ev2 Ep2
                (AF3 pF8 (LLVM_sim.ptr_off_prov _ _ _ HpF8) ltac:(lia) ltac:(lia) st4 A4))
      as (st5 & sR5 & R5 & Rd5 & Es5 & Ps5 & P5 & A5).
    eapply fgoal_instr; [exact HP| |split; eexists; [exact Ev2|exact Ep2]|exact R5|].
    { split; [apply noflat_gep_arr_ss|apply noflat_gep_struct_ss]. }
    destruct P5 as (H5h & H5f & _ & H5m & H5w & H5r & H5p).
    (* l3: prev := tinfo->fp *)
    assert (HrFP5 : reads_ptr st5 aFP fp).
    { apply H5p; [apply H4p; [apply H3p|]|]; [| |unfold LLVM_instr_lemmas.disj8 in *; lia|unfold LLVM_instr_lemmas.disj8 in *; lia].
      - eapply LLVM_instr_lemmas.alloc_post_reads_ptr; [exact AP2|]. eapply LLVM_instr_lemmas.alloc_post_reads_ptr; [exact AP1|exact HrFP].
      - rewrite Forall_forall. intros q Hq. destruct (Hqs q Hq) as (H1 & _). unfold LLVM_instr_lemmas.disj8. lia. }
    pose proof (eval_gep_tinfo_field st5 sf stk G tinfo 4 8216 aFP (Some (DTYPE_Pointer : dtyp)) Htl
                  ltac:(right; right; left; reflexivity) HaFP) as Ev3.
    eapply fgoal_instr; [exact HP| |eexists; exact Ev3|apply (LLVM_instr_lemmas.instr_load_ptr ctx va _ _ aFP fp); [exact Ev3|exact HrFP5]|].
    { split; [apply Flatten_sem.is_flat_ssname|apply noflat_gep_tinfo]. }
    set (sf10 := upd_local_sf sf (Maps.add (ssname fresh 10) (Ptr fp) (stack_vars sf))).
    assert (F10 : RM.find (ssname fresh 10) (stack_vars sf10) = Some (Ptr fp)).
    { unfold sf10. rewrite LLVM_instr_lemmas.stack_vars_upd. apply LLVM_instr_lemmas.rfind_add_eq. }
    assert (F2' : RM.find (ssname fresh 2) (stack_vars sf10) = Some (Ptr pF)).
    { unfold sf10. rewrite LLVM_instr_lemmas.stack_vars_upd, LLVM_instr_lemmas.rfind_add_neq; [exact F2|].
      intros E'. apply ssname_inj in E'. lia. }
    assert (Htl10 : tinfo_local sf10) by (apply LLVM_sim.tinfo_local_write; [exact Htl|unfold ssname; discriminate]).
    (* s4: frame->prev := prev *)
    destruct (LLVM_sim.ptr_off_ex pF 16) as (pF16 & HpF16); [lia|].
    pose proof (LLVM_sim.ptr_off_int _ _ _ HpF16) as EpF16.
    assert (Ev4 : exp_eval st5 sf10 stk G (Some (DTYPE_Pointer : dtyp)) (EXP_Ident (ID_Local (ssname fresh 10))) (Ptr fp))
      by (apply exp_eval_local, F10).
    assert (Ep4 : exp_eval st5 sf10 stk G (Some (DTYPE_Pointer : dtyp))
                    (cexp (gep_struct frame_ty (EXP_Ident (ID_Local (ssname fresh 2))) 2)) (Ptr pF16)).
    { eapply eval_gep_struct_local; [exact F2'|lia|exact HpF16]. }
    destruct (store_ptr_aid ctx va G 0 _ _ fp pF16 st5 sf10 stk Ev4 Ep4
                (AF3 pF16 (LLVM_sim.ptr_off_prov _ _ _ HpF16) ltac:(lia) ltac:(lia) st5 (fun b => eq_trans (A5 b) (A4 b))))
      as (st6a & fp6 & R6a & Rd6a & Efp6 & Pfp6 & P6a & A6a).
    eapply fgoal_instr; [exact HP| |split; eexists; [exact Ev4|exact Ep4]|exact R6a|].
    { split; [apply Flatten_sem.is_flat_ssname|apply noflat_gep_struct_ss]. }
    destruct P6a as (H6ah & H6af & _ & H6am & H6aw & H6ar & H6ap).
    assert (Eqfp : fp6 = fp).
    { apply LLVM_sim.ptr_ext; [exact Efp6|]. rewrite Pfp6. symmetry. eapply reads_ptr_wild; exact HrFP. }
    subst fp6.
    (* s5: tinfo->fp := frame *)
    assert (WFP : forall st', (forall p, writable_word st' p <-> writable_word st5 p) -> writable_word st' aFP).
    { intros st' Hw. apply Hw, H5w, H4w, H3w.
      eapply LLVM_instr_lemmas.alloc_post_writable_word; [exact AP2|].
      eapply LLVM_instr_lemmas.alloc_post_writable_word; [exact AP1|].
      apply (Hflds off_fp aFP); [right; right; left; reflexivity|exact HaFP]. }
    assert (Ev5 : exp_eval st6a sf10 stk G (Some (DTYPE_Pointer : dtyp)) (EXP_Ident (ID_Local (ssname fresh 2))) (Ptr pF))
      by (apply exp_eval_local, F2').
    pose proof (eval_gep_tinfo_field st6a sf10 stk G tinfo 4 8216 aFP (Some (DTYPE_Pointer : dtyp)) Htl10
                  ltac:(right; right; left; reflexivity) HaFP) as Ep5.
    destruct (store_ptr_aid ctx va G 0 _ _ pF aFP st6a sf10 stk Ev5 Ep5 (WFP st6a H6aw))
      as (st6b & f6 & R6b & Rd6b & Ef6 & Pf6 & P6b & A6b).
    eapply fgoal_instr; [exact HP| |split; eexists; [exact Ev5|exact Ep5]|exact R6b|].
    { split; [apply Flatten_sem.is_flat_ssname|apply noflat_gep_tinfo]. }
    destruct P6b as (H6bh & H6bf & _ & H6bm & H6bw & H6br & H6bp).
    (* s6: tinfo->nalloc := cw *)
    assert (Ev6 : exp_eval st6b sf10 stk G (Some (DTYPE_I 64 : dtyp)) (dlit cwz) (I64 (Z.of_nat cwz)))
      by (unfold dlit; apply exp_eval_lit64).
    pose proof (eval_gep_tinfo_field st6b sf10 stk G tinfo 5 8224 aN (Some (DTYPE_Pointer : dtyp)) Htl10
                  ltac:(right; right; right; reflexivity) HaN) as Ep6.
    assert (WN : writable_word st6b aN).
    { apply H6bw, H6aw, H5w, H4w, H3w.
      eapply LLVM_instr_lemmas.alloc_post_writable_word; [exact AP2|].
      eapply LLVM_instr_lemmas.alloc_post_writable_word; [exact AP1|].
      apply (Hflds off_nalloc aN); [right; right; right; left; reflexivity|exact HaN]. }
    destruct (store_word_aid ctx va G 0 _ _ (Z.of_nat cwz) aN st6b sf10 stk Ev6 Ep6 WN) as (st6 & R6 & Rn6 & P6 & A6).
    eapply fgoal_instr; [exact HP| |split; eexists; [exact Ev6|exact Ep6]|exact R6|].
    { split; [exact I|apply noflat_gep_tinfo]. }
    destruct P6 as (H6h & H6f & _ & H6m & H6w & H6r & H6p).
    (* the state after linking *)
    set (W := fun a => field_addr tinfo off_fp a \/ field_addr tinfo off_nalloc a).
    assert (Hms02 : LLVM_sim.mstep st st2 (fun _ => False)).
    { eapply LLVM_sim.mstep_trans; [eapply alloca_mstep; exact AP1|eapply alloca_mstep; exact AP2|]. intros a []. }
    set (W2 := fun a => (ptr_to_int pR <= a < ptr_to_int pR + 8 * Z.of_nat nr) \/ (ptr_to_int pF <= a < ptr_to_int pF + 24) \/ W a).
    assert (Hms26 : LLVM_sim.mstep st2 st6 W2).
    { split; [congruence|]. split; [|split].
      - intros a Ha _. unfold W2, W, field_addr, off_fp, off_nalloc in Ha.
        rewrite H6m, H6bm, H6am, H5m, H4m, H3m; [reflexivity|..]; try lia.
        rewrite Forall_forall. intros q Hq. destruct (Hqs q Hq). lia.
      - intros a _. rewrite A6, A6b, A6a, A5, A4, A3. reflexivity.
      - exists []. split; [rewrite LLVM_sim.push_top_nil; congruence|constructor]. }
    assert (Hms : LLVM_sim.mstep st st6 W).
    { eapply LLVM_sim.mstep_trans; [eapply mstep_weaken; [exact Hms02|intros ? []]|exact Hms26|]. intros a Ha Hal. unfold W2 in Ha.
      pose proof (Lst _ Hal). destruct Ha as [Ha|[Ha|Ha]]; [lia| |exact Ha].
      pose proof (Lst1 _ (A01 _ Hal)). lia. }
    (* reads in st6 *)
    assert (RpF : reads_ptr st6 pF eR4).
    { apply H6p; [apply H6bp; [apply H6ap; [apply H5p|]|]|]; [exact Rd4|..]; unfold LLVM_instr_lemmas.disj8; lia. }
    assert (RpF8 : reads_ptr st6 pF8 sR5).
    { apply H6p; [apply H6bp; [apply H6ap|]|]; [exact Rd5|..]; unfold LLVM_instr_lemmas.disj8; lia. }
    assert (RpF16 : reads_ptr st6 pF16 fp).
    { apply H6p; [apply H6bp|]; [exact Rd6a|..]; unfold LLVM_instr_lemmas.disj8; lia. }
    assert (RFP : reads_ptr st6 aFP f6).
    { apply H6p; [exact Rd6b|]. unfold LLVM_instr_lemmas.disj8; lia. }
    assert (Ff6 : field st6 tinfo off_fp f6) by (exists aFP; auto).
    assert (Fa6 : field st6 tinfo off_alloc alloc).
    { exists aA. split; [exact HaA|].
      apply H6p; [apply H6bp; [apply H6ap; [apply H5p; [apply H4p; [apply H3p|]|]|]|]|];
        try (unfold LLVM_instr_lemmas.disj8; lia).
      - eapply LLVM_instr_lemmas.alloc_post_reads_ptr; [exact AP2|]. eapply LLVM_instr_lemmas.alloc_post_reads_ptr; [exact AP1|exact HrA].
      - rewrite Forall_forall. intros q Hq. destruct (Hqs q Hq) as (H1 & _). unfold LLVM_instr_lemmas.disj8. lia. }
    (* the frame read through the wildcard pointer [f6] *)
    assert (Hwread : forall q q' t0 v0, memS_returns st6 (read_dvalue t0 q) v0 -> ptr_to_int q' = ptr_to_int q ->
                       ptr_provenance q' = wildcard_prov -> memS_returns st6 (read_dvalue t0 q') v0).
    { intros q q' t0 v0 H E Pw. apply (read_reprov st6 t0 q q' v0 H E). intros b Hb.
      destruct H as (st0 & H). apply read_dvalue_runs in H. destruct H as (_ & ptrs & bs & Eg & HF & _).
      pose proof (gcp_spec _ _ _ Eg) as [L C].
      destruct (nth_error ptrs (Z.to_nat (b - ptr_to_int q))) as [r|] eqn:Er; [|apply nth_error_None in Er; lia].
      destruct (C _ _ Er) as [Er1 _]. destruct (LLVM_sim.nth_error_Forall2 _ _ _ _ _ HF Er) as (bb & _ & (aid & Hl & _)).
      exists aid. rewrite Pw. split; [|apply access_wild]. unfold aid_at.
      replace b with (ptr_to_int r) by lia. rewrite Hl. reflexivity. }
    destruct (LLVM_sim.ptr_off_ex f6 8) as (f8 & Hf8); [lia|].
    destruct (LLVM_sim.ptr_off_ex f6 16) as (f16 & Hf16); [lia|].
    pose proof (LLVM_sim.ptr_off_int _ _ _ Hf8) as Ef8. pose proof (LLVM_sim.ptr_off_int _ _ _ Hf16) as Ef16.
    pose proof (LLVM_sim.ptr_off_prov _ _ _ Hf8) as Pf8. pose proof (LLVM_sim.ptr_off_prov _ _ _ Hf16) as Pf16.
    assert (Hff : LLVM_sim.frame_fields st6 f6 eR4 sR5 fp).
    { split; [|split; [|split]].
      - pose proof (Hfa off_fp aFP ltac:(right; right; left; reflexivity) HaFP). pose proof (ptr_to_int_range aFP). lia.
      - apply (Hwread pF f6); [exact RpF|exact Ef6|exact Pf6].
      - exists f8. split; [exact Hf8|]. apply (Hwread pF8 f8); [exact RpF8|lia|congruence].
      - exists f16. split; [exact Hf16|]. apply (Hwread pF16 f16); [exact RpF16|lia|congruence]. }
    (* the root slots, through [sR5] *)
    destruct (slots_build st6 nr sR5 eR4) as (rs1 & Hsl & L1 & Hn1).
    { rewrite Ee4, Es5. apply LLVM_sim.ptr_off_int in HeR. exact HeR. }
    { rewrite Ee4. apply LLVM_sim.ptr_off_int in HeR. lia. }
    assert (Hrd1 : Forall2 (reads_word st6) rs1 zs1).
    { apply Forall2_of_nth; [lia|]. intros i r z Hr Hz.
      assert (Hi : (i < nr)%nat) by (rewrite <- L1; apply nth_error_Some; rewrite Hr; discriminate).
      destruct (nth_error qs i) as [q|] eqn:Hq; [|apply nth_error_None in Hq; lia].
      pose proof (slot_ptrs_nth _ _ _ _ _ Sqs Hq) as Ho. apply LLVM_sim.ptr_off_int in Ho.
      destruct (Hn1 i r Hr) as [E1 E2].
      rewrite Forall_forall in R3. pose proof (R3 _ (combine_nth_In _ _ _ _ _ Hq Hz)) as Rq. cbn in Rq.
      assert (Hqi : In q qs) by (eapply nth_error_In; eauto). destruct (Hqs q Hqi) as (Q1 & Q2 & _).
      cbn [Nat.add] in Ho.
      apply (Hwread q r); [|lia|rewrite E2; exact Ps5].
      apply H6r; [apply H6br; [apply H6ar; [apply H5r; [apply H4r|]|]|]|]; [exact Rq|..]; unfold LLVM_instr_lemmas.disj8; lia. }
    assert (Hnth1 : forall i r, nth_error rs1 i = Some r -> ptr_to_int r = ptr_to_int pR + 8 * Z.of_nat i).
    { intros i r Hr. destruct (Hn1 i r Hr) as [E1 _]. rewrite E1, Es5. reflexivity. }
    assert (Hslot1 : forall a, LLVM_sim.slot_bytes rs1 a -> ptr_to_int pR <= a < ptr_to_int pR + 8 * Z.of_nat nr).
    { intros a (r & Hr & Ha). apply In_nth_error in Hr. destruct Hr as (i & Hi).
      assert (Hin : (i < nr)%nat) by (rewrite <- L1; apply nth_error_Some; rewrite Hi; discriminate).
      rewrite (Hnth1 i r Hi) in Ha. lia. }
    assert (Al6 : forall a, IntMaps.lookup a (mem_of st1) <> None -> IntMaps.lookup a (mem_of st6) <> None).
    { intros a Ha. apply (aid_alloc st1); [|exact Ha]. rewrite A6, A6b, A6a, A5, A4, A3. apply Aid12, Ha. }
    assert (Al26 : forall a, IntMaps.lookup a (mem_of st2) <> None -> IntMaps.lookup a (mem_of st6) <> None).
    { intros a Ha. apply (aid_alloc st2); [|exact Ha]. rewrite A6, A6b, A6a, A5, A4, A3. reflexivity. }
    assert (NH : forall a, IntMaps.lookup a (mem_of st) = None -> ~ in_heap st6 a).
    { intros a Ha Hh. destruct Hms as (Eh & _). unfold in_heap in Hh. rewrite Eh in Hh.
      destruct Hmem as [Hm _]. apply (Hm a Hh), Ha. }
    assert (Fr0 : forall a, ptr_to_int pR <= a -> IntMaps.lookup a (mem_of st) = None) by exact FrR.
    assert (Fr0F : forall a, ptr_to_int pF <= a -> IntMaps.lookup a (mem_of st) = None).
    { intros a Ha. destruct (IntMaps.lookup a (mem_of st)) eqn:E; [|reflexivity].
      exfalso. apply (A01 a); [rewrite E; discriminate|apply FrF, Ha]. }
    assert (HI6 : INV st6 f6 (rs1 ++ rs) (vs1 ++ vsr)).
    { refine (LLVM_sim.INV_link cenv fds heap_inv G tinfo Hmut Htinfo_range st st6 W fp rs vsr alloc limit f6 eR4 sR5 rs1 zs1 vs1
                HI Hms _ Ha0 Hl0 Fa6 Ff6 Hff Hsl Hrd1 Hvs _ _).
      - intros a [H|H]; [right; right; left; exact H|right; right; right; exact H].
      - intros a Ha. unfold LLVM_sim.frame_bytes in Ha. rewrite Ef6 in Ha.
        split; [split|split].
        + apply Al26. destruct (ACF a ltac:(lia)) as (aid & Hid & _). unfold aid_at in Hid.
          destruct (IntMaps.lookup a (mem_of st2)); [discriminate|discriminate].
        + apply NH, Fr0F. lia.
        + intros (r & Hr & Hra). apply in_app_iff in Hr. destruct Hr as [Hr|Hr].
          * assert (Hs : LLVM_sim.slot_bytes rs1 a) by (exists r; auto). apply Hslot1 in Hs.
            destruct HRF as [E0|E0]; [rewrite E0 in Hs; cbn in Hs; lia|lia].
          * destruct Hsk as (_ & Hsl0). destruct (Hsl0 a ltac:(exists r; auto)) as (Hal & _).
            apply Hal, Fr0F. lia.
        + apply Fr0F. lia.
      - intros a Ha. apply Hslot1 in Ha. split; [split|].
        + apply Al6. destruct (ACR a Ha) as (aid & Hid & _). unfold aid_at in Hid.
          destruct (IntMaps.lookup a (mem_of st1)); [discriminate|discriminate].
        + apply NH, FrR. lia.
        + apply FrR. lia. }
    apply (Hk st6 f6 eR4 sR5 rs1 HI6 Hff Hsl Ef6 ltac:(lia) Hnth1); [|exact Hms| |exact BR'].
    - exists aN. split; [exact HaN|exact Rn6].
    - intros b. rewrite A6, A6b, A6a, A5, A4, A3. reflexivity.
  Qed.

  (* ---------------------------------------------------------------- *)
  (** *** Chunk heads: the collection *)

  Lemma gc_call_eq gp s :
    RM.find (Name "garbage_collect") G = Some (Ptr gp) ->
    interp_mcfg (interp_mrec ctx (ctx _ (Call DTYPE_Void (Ptr gp) [Ptr tinfo]))) s ≈ interp_mcfg (gc [Ptr tinfo]) s.
  Proof.
    intros Hg. rewrite (ctx_gc gp Hg DTYPE_Void gp [Ptr tinfo] eq_refl).
    rewrite (interp_mrec_lift_top ctx). reflexivity.
  Qed.

  Lemma gc_reload_fgoal va P lo fresh roots st6 f e s rs1 sf10 stk fp rs vsr vs1 pR cwz rest tmt K :
    closedP P -> (forall t, ends_in_oom t -> P t) ->
    INV st6 f (rs1 ++ rs) (vs1 ++ vsr) ->
    LLVM_sim.frame_fields st6 f e s fp -> slots_from st6 s e rs1 ->
    length rs1 = length roots -> length vs1 = length roots ->
    (forall i r, nth_error rs1 i = Some r -> ptr_to_int r = ptr_to_int pR + 8 * Z.of_nat i) ->
    Z.of_nat cwz < 2 ^ 61 ->
    (exists aN, ptr_off tinfo off_nalloc aN /\ reads_word st6 aN (Z.of_nat cwz)) ->
    (forall b, ptr_to_int pR <= b < ptr_to_int pR + 8 * Z.of_nat (length roots) ->
       exists aid, aid_at st6 b = Some aid /\ access_allowed (ptr_provenance pR) aid = true) ->
    ptr_to_int pR + 8 * Z.of_nat (length roots) < 2 ^ 64 ->
    RM.find (ssname fresh 1) (stack_vars sf10) = Some (Ptr pR) ->
    RM.find (ssname fresh 10) (stack_vars sf10) = Some (Ptr fp) ->
    tinfo_local sf10 ->
    (forall st_f zs, INV st_f fp rs vsr -> fext (rs1 ++ rs) st6 st_f -> room st_f tinfo (Z.of_nat cwz) ->
       Forall2 (stable_repr st_f) vs1 zs -> length zs = length roots ->
       fgoal ctx va G P lo rest tmt K st_f
             (upd_local_sf sf10 (LLVM_instr_lemmas.reload_locals (stack_vars sf10) fresh 0 zs)) stk) ->
    fgoal ctx va G P lo
      ((IVoid 0%Z, INSTR_Call ((DTYPE_Void : dtyp), EXP_Ident (ID_Global (Name "garbage_collect")))
                     [(((DTYPE_Pointer : dtyp), EXP_Ident (ID_Local (Name "tinfo"))), [])] [] [], [])
       :: ccode (reload_code fresh (EXP_Ident (ID_Local (ssname fresh 1))) (TYPE_Array (N.of_nat (length roots)) val_ty) 0 roots)
       ++ (IVoid 0%Z, INSTR_Store ((DTYPE_Pointer : dtyp), EXP_Ident (ID_Local (ssname fresh 10)))
                        ((DTYPE_Pointer : dtyp), cexp (gep_tinfo 4)) [], []) :: rest)
      tmt K st6 sf10 stk.
  Proof.
    intros HP HPo HI6 Hff Hsl L1 Lv Hn1 Hcw HaN HacR BR F1 F10 Htl Hk.
    destruct G_gc as (gp & Hgp).
    apply (fgoal_call_gc ctx va G P lo 0 _ tmt K st6 sf10 stk gp tinfo HP HPo Htl Hgp).
    intros sf2 Hnf2.
    pose proof HI6 as (Hhi6 & Hok6 & Hmem6 & Hdis6 & Hfp6 & Hss6 & Hsk6 & Hroots6).
    destruct (Hgc st6 (sf2, stk) f (rs1 ++ rs) (vs1 ++ vsr) (Z.of_nat cwz) Hhi6 Hok6 Hmem6 Hdis6 Hfp6 Hss6 Hroots6 ltac:(lia) HaN)
      as [Hoom|(stg & Hret & Hfr & Hhig & Hokg & Hmemg & Hdisg & Hfpg & Hssg & Hrootsg & Hroomg & Hnh & Hgrow & Hslaid)].
    { left. unfold LLVM_instr_lemmas.oom. rewrite gc_call_eq by exact Hgp. exact Hoom. }
    right. exists stg. split; [unfold LLVM_instr_lemmas.runs; rewrite gc_call_eq by exact Hgp; exact Hret|].
    assert (Kg : LLVM_sim.keeps_stack st6 stg (rs1 ++ rs))
      by (apply LLVM_sim.keeps_stack_gc; assumption).
    assert (HIg : INV stg f (rs1 ++ rs) (vs1 ++ vsr))
      by (eapply LLVM_sim.INV_gc; eauto).
    (* the roots after the collection *)
    destruct (LLVM_sim.roots_ok_split' cenv fds G tinfo stg rs1 rs (vs1 ++ vsr) Hrootsg)
      as (vs1' & vs' & zs & Evs & Hrd & Hst & Hroots').
    assert (Lz : length zs = length roots) by (rewrite <- L1; symmetry; eapply Forall2_length; eauto).
    assert (Lv' : length vs1' = length roots) by (rewrite <- Lz; eapply Forall2_length; eauto).
    destruct (app_eq_len vs1 vsr vs1' vs' ltac:(lia) Evs) as [<- <-].
    (* reload *)
    set (nr := length roots) in *.
    assert (Hsok : LLVM_instr_lemmas.slots_ok (fun q w => reads_word stg q w) pR 0 zs).
    { apply slots_ok_intro. intros j w Hj. cbn [Nat.add].
      assert (Hjn : (j < nr)%nat) by (rewrite <- Lz; apply nth_error_Some; rewrite Hj; discriminate).
      destruct (nth_error rs1 j) as [r|] eqn:Hr; [|apply nth_error_None in Hr; lia].
      destruct (LLVM_sim.ptr_off_ex pR (8 * Z.of_nat j)) as (q & Hq); [pose proof (ptr_to_int_range pR); lia|].
      exists q. split; [exact Hq|].
      pose proof (LLVM_sim.ptr_off_int _ _ _ Hq) as Eq. pose proof (LLVM_sim.ptr_off_prov _ _ _ Hq) as Pq.
      pose proof (Hn1 j r Hr) as Er.
      destruct (LLVM_sim.nth_error_Forall2 _ _ _ _ _ Hrd Hr) as (w' & Hw' & Rr). rewrite Hj in Hw'. injection Hw' as <-.
      apply (read_reprov stg _ r q _ Rr); [lia|]. intros b Hb. rewrite sizeof_i64 in Hb.
      destruct (HacR b ltac:(lia)) as (aid & Ha & Hacc). exists aid. rewrite Pq. split; [|exact Hacc].
      rewrite Hslaid; [exact Ha|]. exists r. split; [apply in_or_app; left; eapply nth_error_In; exact Hr|lia]. }
    apply (fgoal_reload ctx va G P lo fresh (ssname fresh 1) pR (N.of_nat nr) _ tmt K stg stk roots 0 zs sf10 HP F1).
    { intros k E. apply ssname_inj in E. lia. }
    { apply Flatten_sem.is_flat_ssname. }
    { lia. }
    { cbn [Nat.add]. pose proof (ptr_to_int_range pR). lia. }
    { exact Hsok. }
    set (sfR := upd_local_sf sf10 (LLVM_instr_lemmas.reload_locals (stack_vars sf10) fresh 0 zs)).
    assert (F10R : RM.find (ssname fresh 10) (stack_vars sfR) = Some (Ptr fp)).
    { unfold sfR. rewrite LLVM_instr_lemmas.stack_vars_upd, LLVM_instr_lemmas.reload_locals_other; [exact F10|].
      intros k _ E. apply ssname_inj in E. lia. }
    assert (TlR : tinfo_local sfR).
    { unfold sfR, tinfo_local, LLVM_sim.tinfo_local. rewrite LLVM_instr_lemmas.stack_vars_upd, LLVM_instr_lemmas.reload_locals_other; [exact Htl|].
      intros k _ E. unfold ssname in E. discriminate. }
    pose proof Hfpg as (aFP & HaFP & HrFPg).
    pose proof (LLVM_sim.ptr_off_int _ _ _ HaFP) as EaFP. unfold off_fp in EaFP.
    assert (WFP : writable_word stg aFP).
    { destruct Hokg as (Hf & _). apply (Hf off_fp aFP); [right; right; left; reflexivity|exact HaFP]. }
    pose proof (eval_gep_tinfo_field stg sfR stk G tinfo 4 8216 aFP (Some (DTYPE_Pointer : dtyp)) TlR
                  ltac:(right; right; left; reflexivity) HaFP) as Ep.
    assert (Ev : exp_eval stg sfR stk G (Some (DTYPE_Pointer : dtyp)) (EXP_Ident (ID_Local (ssname fresh 10))) (Ptr fp))
      by (apply exp_eval_local, F10R).
    destruct (store_ptr_aid ctx va G 0 _ _ fp aFP stg sfR stk Ev Ep WFP) as (stf & fp2 & R & Rd & Efp & Pfp & Wp & Af).
    eapply fgoal_instr; [exact HP| |split; eexists; [exact Ev|exact Ep]|exact R|].
    { split; [apply Flatten_sem.is_flat_ssname|apply noflat_gep_tinfo]. }
    destruct Wp as (Hfh & Hff' & _ & Hfm & Hfw & Hfrd & Hfp').
    (* the frame survives the collection *)
    destruct (stack_ok_unlink _ _ _ _ _ _ _ Hff Hsk6) as [_ Hfb].
    assert (Hsame : forall q, ptr_to_int f <= ptr_to_int q -> ptr_to_int q + 8 <= ptr_to_int f + 24 ->
                      same_bytes st6 stg (ptr_to_int q) 8).
    { intros q H1 H2 a Ha. destruct (Hfb a ltac:(unfold LLVM_sim.frame_bytes; lia)) as ((_ & Hnh') & Hns).
      apply Hnh; assumption. }
    assert (Hffg : LLVM_sim.frame_fields stg f e s fp).
    { destruct Hff as (Hnz & He & (a8 & Ha8 & Hs8) & (a16 & Ha16 & Hp16)).
      pose proof (LLVM_sim.ptr_off_int _ _ _ Ha8). pose proof (LLVM_sim.ptr_off_int _ _ _ Ha16).
      split; [exact Hnz|split; [|split]].
      - eapply reads_ptr_frame; [exact He|apply Hsame; lia].
      - exists a8. split; [exact Ha8|]. eapply reads_ptr_frame; [exact Hs8|apply Hsame; lia].
      - exists a16. split; [exact Ha16|]. eapply reads_ptr_frame; [exact Hp16|apply Hsame; lia]. }
    assert (Hfpw : ptr_provenance fp = wildcard_prov).
    { destruct Hff as (_ & _ & _ & (a16 & _ & Hp16)). eapply reads_ptr_wild; exact Hp16. }
    assert (Efp2 : fp2 = fp) by (apply LLVM_sim.ptr_ext; [exact Efp|congruence]). subst fp2.
    pose proof (LLVM_sim.slots_from_state st6 stg s e rs1 Hsl) as Hslg.
    destruct (LLVM_sim.shadow_stack_unlink stg f e s fp rs1 (rs1 ++ rs) Hffg Hslg Hssg) as (rs0 & Ers & Hssg0).
    apply app_inv_head in Ers. subst rs0.
    pose proof HIg as (_ & _ & _ & _ & _ & _ & Hskg & _).
    destruct (stack_ok_unlink _ _ _ _ _ _ _ Hffg Hskg) as [Hskg0 _].
    set (W1 := fun a => field_addr tinfo off_fp a).
    assert (Hms : LLVM_sim.mstep stg stf W1).
    { split; [exact Hfh|]. split; [|split].
      - intros a Ha _. apply Hfm. intros Ha'. apply Ha. unfold W1, field_addr, off_fp. lia.
      - intros a _. apply Af.
      - exists []. split; [rewrite LLVM_sim.push_top_nil; exact Hff'|constructor]. }
    assert (HW1 : forall a, W1 a -> in_heap stg a).
    { intros a Ha. eapply (LLVM_sim.field_addr_in_heap tinfo Htinfo_range stg off_fp); [exact Hokg|right; right; left; reflexivity|exact Ha]. }
    destruct (LLVM_sim.stack_ok_mstep stg stf W1 fp rs Hms HW1 Hssg0 Hskg0) as [Hssf Hskf].
    pose proof Hokg as (_ & _ & alloc & limit & Hag0 & Hlg0 & Halign & Hle & _).
    pose proof Hag0 as (aA & HaA & HrA). pose proof Hlg0 as (aL & HaL & HrL).
    pose proof (LLVM_sim.ptr_off_int _ _ _ HaA) as EaA. pose proof (LLVM_sim.ptr_off_int _ _ _ HaL) as EaL.
    unfold off_alloc, off_limit in EaA, EaL.
    assert (Haf : field stf tinfo off_alloc alloc).
    { exists aA. split; [exact HaA|]. apply Hfp'; [exact HrA|]. lia. }
    assert (Hlf : field stf tinfo off_limit limit).
    { exists aL. split; [exact HaL|]. apply Hfp'; [exact HrL|]. lia. }
    assert (Hfpf : field stf tinfo off_fp fp) by (exists aFP; auto).
    destruct (LLVM_sim.INV_mstep_gen cenv fds heap_inv G tinfo Hmut Htinfo_range stg stf W1 f (rs1 ++ rs) (vs1 ++ vsr)
                alloc alloc limit fp rs HIg Hms ltac:(intros a Ha; right; right; left; exact Ha)
                Hag0 Hlg0 Haf ltac:(lia) Halign eq_refl Hfpf Hssf)
      as (Hhif & Hokf & Hmemf & Hdisf & _ & _ & _ & Hnm & Hagf).
    assert (Hrootsf : roots_ok cenv fds G stf tinfo rs vsr).
    { eapply LLVM_sim.roots_ok_mono; [exact Hroots'|exact Hagf|exact Hfh|exact Hnm|].
      intros r Hr a Ha. destruct Hskg0 as (_ & Hslr). destruct (Hslr a ltac:(exists r; auto)) as (Hal & Hnh').
      apply Hfm. intros Ha'. apply Hnh', HW1. unfold W1, field_addr, off_fp. lia. }
    apply Hk.
    - split; [exact Hhif|split; [exact Hokf|split; [exact Hmemf|split; [exact Hdisf|split; [exact Hfpf|
        split; [exact Hssf|split; [exact Hskf|exact Hrootsf]]]]]]].
    - split.
      + exists []. split; [rewrite LLVM_sim.push_top_nil; congruence|constructor].
      + eapply LLVM_sim.keeps_stack_trans; [exact Kg|eapply LLVM_sim.keeps_stack_mstep; [exact Hms|exact HW1]].
    - destruct Hroomg as (al & li & Hal & Hli & Hr). exists al, li.
      rewrite (LLVM_sim.field_det tinfo stg off_alloc al alloc Hal Hag0), (LLVM_sim.field_det tinfo stg off_limit li limit Hli Hlg0) in *.
      split; [exact Haf|split; [exact Hlf|exact Hr]].
    - eapply Forall2_impl; [|exact Hst]. intros v0 z0 Hz. eapply LLVM_sim.stable_repr_mono; eauto.
    - exact Lz.
  Qed.

  Lemma gc_path_sim x t ys e' rho v vs env fresh f0 b0 rest0 c0 B va c_a c_g st st1 st2 sf stk fp rs vsr pR pF :
    sim_stmt (M.set x (Vconstr t vs) rho) e' v ->
    ys <> [] -> get_list ys rho = Some vs ->
    body_ok cenv e' -> subterm_or_eq (Econstr x t ys e') (Efun fds main) ->
    unique_bindings (Econstr x t ys e') ->
    Ensembles.Disjoint _ (bound_var (Econstr x t ys e')) (occurs_free (Econstr x t ys e')) ->
    env_ok (occurs_free (Econstr x t ys e')) env fresh ->
    tr (hd_env fs env fresh x ys e') (chunk_words e') e' (Pos.succ fresh) = (b0 :: rest0, f0) ->
    LLVM_sim.blocks_in B (b0 :: rest0) ->
    RM.find (blk_id b0) (ocfg_map B) = Some (LLVM_sim.flatB (cblock b0) c0) ->
    RM.find (Anon (Zpos (Pos.succ (Pos.succ f0)))) (ocfg_map B) =
      Some (LLVM_sim.flatB (cblock (hd_alloc_blk go ga fs env x t ys e' fresh f0 (entry_id (b0 :: rest0) f0))) c_a) ->
    RM.find (Anon (Zpos (Pos.succ f0))) (ocfg_map B) =
      Some (LLVM_sim.flatB (cblock (hd_gc_blk fs env x ys e' fresh f0)) c_g) ->
    INV st fp rs vsr ->
    LLVM_instr_lemmas.alloc_post st st1 (8 * N.of_nat (length (hd_roots fs x ys e'))) pR ->
    LLVM_instr_lemmas.alloc_post st1 st2 24 pF ->
    INV st2 fp rs vsr ->
    RM.find (ssname fresh 1) (stack_vars sf) = Some (Ptr pR) ->
    RM.find (ssname fresh 2) (stack_vars sf) = Some (Ptr pF) ->
    tinfo_local sf ->
    env_rel (occurs_free (Econstr x t ys e')) rho env sf st ->
    sim_result st stk fp rs vsr v
      (RUN (denote_ocfg B va (Anon (Zpos f0), Anon (Zpos (Pos.succ f0)))) (st2, ((sf, stk), G))).
  Proof.
    intros IH Hne Hget Hbo' Hsub Hub Hdis Henv Etr Hbin Hb0 Ha Hg HI AP1 AP2 HI2 F1 F2 Htl Hrel.
    set (roots := hd_roots fs x ys e') in *.
    set (cw := (hd_nwords ys + chunk_words e')%N).
    destruct (roots_words _ rho env sf st roots Hrel) as (wsd & Hw1 & Hw2).
    { intros r Hr. split; [apply (root_fv x t ys e' r Hr)|apply hd_roots_spec in Hr; tauto]. }
    destruct (split_rel _ _ roots wsd Hw2) as (vs1 & zs1 & -> & Hv1 & Hz1).
    assert (Hzs : Forall2 (fun r z => RM.find (env r) (stack_vars sf) = Some (I64 z)) roots zs1).
    { clear -Hw1. revert zs1 Hw1. induction roots as [|r roots IH]; intros [|z zs] H; inversion H; subst; constructor; auto. }
    assert (Lr : length vs1 = length roots) by (symmetry; eapply Forall2_length; eauto).
    eapply run_jump; [apply sim_result_closed|exact Hg|rewrite LLVM_sim.flatB_phis, cblock_eq; reflexivity|].
    change (interp_mcfg (interp_mrec ctx ?t) ?s) with (RUN t s).
    eapply sim_result_closed; [symmetry; apply tail_of_flat|].
    destruct (ccode_gc_blk fs env x ys e' fresh f0) as (Ec & Et). fold roots in Ec. fold cw in Ec.
    rewrite Ec, Et, cblock_id. cbn [blk_id hd_gc_blk]. cbn [app].
    match goal with |- sim_result _ _ _ _ _ _ (RUN (Flatten_sem.flat_tail _ ?l ?tm _ ?K) _) =>
      enough (Hf : fgoal ctx va G (sim_result st stk fp rs vsr v) c_g l tm K st2 sf stk)
        by (apply Hf; [lia|apply Flatten_sem.agree_except_refl]) end.
    refine (link_fgoal va _ c_g env fresh roots st st1 st2 sf stk fp rs vsr _ _ _ _ _ vs1 zs1 (N.to_nat cw)
              (sim_result_closed _ _ _ _ _ _) HI AP1 AP2 F1 F2 Htl Hzs Hz1 _ _).
    { intros r Hr. eapply LLVM_sim.env_ok_not_flat; eauto. }
    intros st6 f e s rs1 HI6 Hff Hsl Ef L1 Hn1 HaN Hms Aid62 BR.
    pose proof (alloc_post_access _ _ _ _ AP1) as (_ & ACR).
    rewrite N2Z.inj_mul, nat_N_Z in ACR.
    set (sf10 := upd_local_sf sf (Maps.add (ssname fresh 10) (Ptr fp) (stack_vars sf))).
    refine (gc_reload_fgoal va _ c_g fresh roots st6 f e s rs1 sf10 stk fp rs vsr vs1 pR (N.to_nat cw) [] _ _
              (sim_result_closed _ _ _ _ _ _) (sim_result_oom _ _ _ _ _ _) HI6 Hff Hsl L1 Lr Hn1 _ HaN _ BR _ _ _ _).
    - pose proof (prog_chunk_small x t ys e' Hsub Hne) as Hc8. fold cw in Hc8. rewrite N_nat_Z. lia.
    - intros b Hb. destruct (ACR b ltac:(lia)) as (aid & Ha1 & Hacc). exists aid. split; [|exact Hacc].
      rewrite Aid62. unfold aid_at in Ha1 |- *.
      rewrite (LLVM_instr_lemmas.alloc_post_allocated _ _ _ _ _ AP2); [exact Ha1|].
      destruct (IntMaps.lookup b (mem_of st1)); [discriminate|discriminate].
    - unfold sf10. rewrite LLVM_instr_lemmas.stack_vars_upd, LLVM_instr_lemmas.rfind_add_neq; [exact F1|].
      intros E. apply ssname_inj in E. lia.
    - unfold sf10. rewrite LLVM_instr_lemmas.stack_vars_upd. apply LLVM_instr_lemmas.rfind_add_eq.
    - apply LLVM_sim.tinfo_local_write; [exact Htl|unfold ssname; discriminate].
    - intros stf zs HIf Hfx Hroomf Hstf Lz.
      eapply fgoal_term; [apply sim_result_closed|exact I|exact I|apply LLVM_instr_lemmas.term_br_1|].
      intros sfR' Hag. cbn [LLVM_sim.continue].
      eapply (alloc_block_sim x t ys e' rho v vs env fresh f0 b0 rest0 c0 B va c_a st stf sfR' stk fp rs vsr
                (Anon (Zpos (Pos.succ f0))) (map I64 zs)); eauto.
      + eapply fext_trans_slots; [eapply fext_of_mstep; [exact Hms|]|exact Hfx|].
        * intros a [Hw|Hw]; eapply (LLVM_sim.field_addr_in_heap tinfo Htinfo_range st);
            [apply HI| |exact Hw|apply HI| |exact Hw]; cbn; tauto.
        * intros a (r & Hr & Hra) (Hal & _). apply In_nth_error in Hr. destruct Hr as (i & Hi).
          pose proof (Hn1 i r Hi) as Er. destruct AP1 as (_ & _ & Hfree & _).
          apply Hal, Hfree. lia.
      + unfold tinfo_local, LLVM_sim.tinfo_local. rewrite (Hag _ (Flatten_sem.is_flat_Name _)).
        rewrite LLVM_instr_lemmas.stack_vars_upd, LLVM_instr_lemmas.reload_locals_other.
        * unfold sf10. rewrite LLVM_instr_lemmas.stack_vars_upd, LLVM_instr_lemmas.rfind_add_neq; [exact Htl|].
          unfold ssname. discriminate.
        * intros k _ E. unfold ssname in E. discriminate.
      + fold cw. rewrite <- (N_nat_Z cw). exact Hroomf.
      + intros y Hy Hf. destruct (Hrel y Hy) as (v' & Hv & Hc). rewrite Hf in Hc. destruct Hc as (rho' & ->). eauto.
      + exact (join_rel _ _ roots vs1 zs Hv1 Hstf).
      + right. split; [reflexivity|]. apply Forall2_seq_map; [exact Lz|].
        intros j z Hj. rewrite (Hag _ (Flatten_sem.is_flat_ssname _ _)), LLVM_instr_lemmas.stack_vars_upd.
        replace (1000 + j)%nat with (1000 + (0 + j))%nat by lia. apply reload_locals_find, Hj.
  Qed.

  Lemma sim_case_constr_head x t ys e' rho v vs :
    ys <> [] ->
    get_list ys rho = Some vs ->
    sim_stmt (M.set x (Vconstr t vs) rho) e' v ->
    forall env chunk fresh blks f' B va c st sf stk fp rs vsr,
      N.leb (hd_nwords ys) chunk = false ->
      body_ok cenv (Econstr x t ys e') ->
      subterm_or_eq (Econstr x t ys e') (Efun fds main) ->
      unique_bindings (Econstr x t ys e') ->
      Ensembles.Disjoint _ (bound_var (Econstr x t ys e')) (occurs_free (Econstr x t ys e')) ->
      env_ok (occurs_free (Econstr x t ys e')) env fresh ->
      tr env chunk (Econstr x t ys e') fresh = (blks, f') ->
      LLVM_sim.blocks_in B blks ->
      INV st fp rs vsr -> tinfo_local sf ->
      env_rel (occurs_free (Econstr x t ys e')) rho env sf st ->
      sim_result st stk fp rs vsr v
        (interp_mcfg (interp_mrec ctx (LLVM_sim.tail_of va B (LLVM_sim.flatB (cblock (LLVM_sim.hd_blk blks)) c)))
                     (st, ((sf, stk), G))).
  Proof.
    intros Hne Hget IH env chunk fresh blks f' B va c st sf stk fp rs vsr Hleb
      Hbo Hsub Hub Hdis Henv Htr Hbin HI Htl Hrel.
    inversion Hbo as [? ? ? ? _ _ _ Hbo'| | | | | |]; subst.
    destruct (tr (hd_env fs env fresh x ys e') (chunk_words e') e' (Pos.succ fresh)) as [blks0 f0] eqn:E.
    rewrite (tr_constr_head go ga prim_of fs env chunk x t ys e' fresh blks0 f0 Hne Hleb E) in Htr.
    injection Htr as <- <-.
    destruct (translate_cfg_entry go ga prim_of fs _ _ e' _ blks0 f0 E) as (b0 & rest0 & q & -> & _).
    set (roots := hd_roots fs x ys e') in *.
    set (cw := (hd_nwords ys + chunk_words e')%N).
    destruct (Hbin (hd_gc_blk fs env x ys e' fresh f0) ltac:(left; reflexivity)) as (c_g & Hg).
    destruct (Hbin (hd_alloc_blk go ga fs env x t ys e' fresh f0 (entry_id (b0 :: rest0) f0)) ltac:(right; left; reflexivity))
      as (c_a & Ha).
    destruct (Hbin b0 ltac:(right; right; left; reflexivity)) as (c0 & Hb0).
    assert (Hbin0 : LLVM_sim.blocks_in B (b0 :: rest0)) by (intros b Hb; apply Hbin; right; right; right; exact Hb).
    cbn [blk_id hd_gc_blk hd_alloc_blk] in Hg, Ha.
    cbn [LLVM_sim.hd_blk].
    change (interp_mcfg (interp_mrec ctx ?t) ?s) with (RUN t s).
    eapply sim_result_closed; [symmetry; apply tail_of_flat|].
    destruct (ccode_check_blk fs x ys e' fresh f0) as (Ec & Et & Ei). fold roots in Ec. rewrite Ec, Et, Ei.
    match goal with |- sim_result _ _ _ _ _ _ (RUN (Flatten_sem.flat_tail _ ?l ?tm _ ?K) _) =>
      enough (Hf : fgoal ctx va G (sim_result st stk fp rs vsr v) c l tm K st sf stk)
        by (apply Hf; [lia|apply Flatten_sem.agree_except_refl]) end.
    pose proof HI as (Hhi & Hok & Hmem & Hdis' & Hfp & Hss & Hsk & Hroots).
    pose proof Hok as (Hflds & _ & alloc & limit & Ha0 & Hl0 & Halign & Hle & Hinh & Hwr & _).
    pose proof Ha0 as (aA & HaA & HrA). pose proof Hl0 as (aL & HaL & HrL).
    (* 1, 2: the allocas *)
    destruct (LLVM_instr_lemmas.instr_alloca_arr_cases ctx va (ssname fresh 1) (N.of_nat (length roots)) st sf stk G)
      as [Hoom|(st1 & pR & R1 & AP1)].
    { eapply fgoal_oom; [apply sim_result_oom|split; [apply Flatten_sem.is_flat_ssname|intros ? []]|exact I|exact Hoom]. }
    eapply fgoal_instr; [apply sim_result_closed|split; [apply Flatten_sem.is_flat_ssname|intros ? []]|exact I|exact R1|].
    set (sf1 := LLVM_instr_lemmas.alloca_locals sf (ssname fresh 1) pR).
    destruct (LLVM_instr_lemmas.instr_alloca_frame_cases ctx va (ssname fresh 2) st1 sf1 stk G)
      as [Hoom|(st2 & pF & R2 & AP2)].
    { eapply fgoal_oom; [apply sim_result_oom|split; [apply Flatten_sem.is_flat_ssname|intros ? []]|exact I|exact Hoom]. }
    eapply fgoal_instr; [apply sim_result_closed|split; [apply Flatten_sem.is_flat_ssname|intros ? []]|exact I|exact R2|].
    set (sf2 := LLVM_instr_lemmas.alloca_locals sf1 (ssname fresh 2) pF).
    assert (Htl2 : tinfo_local sf2).
    { apply LLVM_sim.tinfo_local_write; [apply LLVM_sim.tinfo_local_write; [exact Htl|]|]; unfold ssname; discriminate. }
    assert (Hms : LLVM_sim.mstep st st2 (fun _ => False)).
    { eapply LLVM_sim.mstep_trans; [eapply alloca_mstep; exact AP1|eapply alloca_mstep; exact AP2|]. intros a []. }
    assert (HrA2 : reads_ptr st2 aA alloc).
    { eapply LLVM_instr_lemmas.alloc_post_reads_ptr; [exact AP2|]. eapply LLVM_instr_lemmas.alloc_post_reads_ptr; [exact AP1|exact HrA]. }
    assert (HrL2 : reads_ptr st2 aL limit).
    { eapply LLVM_instr_lemmas.alloc_post_reads_ptr; [exact AP2|]. eapply LLVM_instr_lemmas.alloc_post_reads_ptr; [exact AP1|exact HrL]. }
    assert (Ha2 : field st2 tinfo off_alloc alloc) by (exists aA; auto).
    assert (Hl2 : field st2 tinfo off_limit limit) by (exists aL; auto).
    assert (HI2 : INV st2 fp rs vsr).
    { exact (LLVM_sim.INV_mstep cenv fds heap_inv G tinfo Hmut Htinfo_range st st2 (fun _ => False) fp rs vsr alloc alloc limit
               HI Hms (fun _ H => False_ind _ H) (fun _ H => False_ind _ H) Ha0 Hl0 Ha2 ltac:(lia) Halign eq_refl). }
    pose proof HI2 as (_ & _ & _ & _ & Hfp2 & Hss2 & _).
    destruct (LLVM_sim.INV_mstep_gen cenv fds heap_inv G tinfo Hmut Htinfo_range st st2 (fun _ => False) fp rs vsr alloc alloc limit fp rs
                HI Hms (fun _ H => False_ind _ H) Ha0 Hl0 Ha2 ltac:(lia) Halign eq_refl Hfp2 Hss2)
      as (_ & _ & _ & _ & _ & _ & _ & Hnm & Hag).
    assert (Hheap2 : heap_of st2 = heap_of st) by (destruct Hms; auto).
    assert (Hrel2 : env_rel (occurs_free (Econstr x t ys e')) rho env sf st2)
      by (eapply LLVM_sim.env_rel_mono; eauto).
    (* 3, 4: alloc and limit *)
    pose proof (eval_gep_tinfo_field st2 sf2 stk G tinfo 0 0 aA (Some (DTYPE_Pointer : dtyp)) Htl2 (or_introl eq_refl) HaA) as Ev3.
    eapply fgoal_instr; [apply sim_result_closed| |eexists; exact Ev3|apply (LLVM_instr_lemmas.instr_load_ptr ctx va _ _ aA alloc); [exact Ev3|exact HrA2]|].
    { split; [apply Flatten_sem.is_flat_ssname|apply noflat_gep_tinfo]. }
    set (sf3 := upd_local_sf sf2 (Maps.add (ssname fresh 3) (Ptr alloc) (stack_vars sf2))).
    assert (Htl3 : tinfo_local sf3) by (apply LLVM_sim.tinfo_local_write; [exact Htl2|unfold ssname; discriminate]).
    pose proof (eval_gep_tinfo_field st2 sf3 stk G tinfo 1 8 aL (Some (DTYPE_Pointer : dtyp)) Htl3 (or_intror (or_introl eq_refl)) HaL) as Ev4.
    eapply fgoal_instr; [apply sim_result_closed| |eexists; exact Ev4|apply (LLVM_instr_lemmas.instr_load_ptr ctx va _ _ aL limit); [exact Ev4|exact HrL2]|].
    { split; [apply Flatten_sem.is_flat_ssname|apply noflat_gep_tinfo]. }
    set (sf4 := upd_local_sf sf3 (Maps.add (ssname fresh 4) (Ptr limit) (stack_vars sf3))).
    (* 5: avail *)
    assert (Ev5 : exp_eval st2 sf4 stk G None
              (OP_IBinop (Sub false false) (DTYPE_I 64 : dtyp)
                 (OP_Conversion (CONV_Impure Ptrtoint) (DTYPE_Pointer : dtyp) (EXP_Ident (ID_Local (ssname fresh 4))) (DTYPE_I 64 : dtyp))
                 (OP_Conversion (CONV_Impure Ptrtoint) (DTYPE_Pointer : dtyp) (EXP_Ident (ID_Local (ssname fresh 3))) (DTYPE_I 64 : dtyp)))
              (I64 (ptr_to_int limit - ptr_to_int alloc))).
    { apply exp_eval_sub; apply exp_eval_ptrtoint, exp_eval_local; unfold sf4, sf3.
      - rewrite LLVM_instr_lemmas.stack_vars_upd. apply LLVM_instr_lemmas.rfind_add_eq.
      - rewrite !LLVM_instr_lemmas.stack_vars_upd, LLVM_instr_lemmas.rfind_add_neq; [apply LLVM_instr_lemmas.rfind_add_eq|].
        intros E'. apply ssname_inj in E'. lia. }
    eapply fgoal_instr; [apply sim_result_closed| |eexists; exact Ev5|apply LLVM_instr_lemmas.instr_op, Ev5|].
    { split; [apply Flatten_sem.is_flat_ssname|]. cbn. repeat split; apply Flatten_sem.is_flat_ssname. }
    set (sf5 := upd_local_sf sf4 (Maps.add (ssname fresh 5) (I64 (ptr_to_int limit - ptr_to_int alloc)) (stack_vars sf4))).
    (* 6: the comparison *)
    set (bb := (Z.of_nat (8 * N.to_nat cw) mod 2 ^ 64 <=? (ptr_to_int limit - ptr_to_int alloc) mod 2 ^ 64)).
    assert (Ev6 : exp_eval st2 sf5 stk G None
              (OP_ICmp false Uge (DTYPE_I 64 : dtyp) (EXP_Ident (ID_Local (ssname fresh 5))) (dlit (8 * N.to_nat cw)))
              (I1 bb)).
    { apply exp_eval_uge; [|apply exp_eval_lit64]. apply exp_eval_local. unfold sf5.
      rewrite LLVM_instr_lemmas.stack_vars_upd. apply LLVM_instr_lemmas.rfind_add_eq. }
    eapply fgoal_instr; [apply sim_result_closed| |eexists; exact Ev6|apply LLVM_instr_lemmas.instr_op, Ev6|].
    { split; [apply Flatten_sem.is_flat_ssname|]. cbn. split; [apply Flatten_sem.is_flat_ssname|exact I]. }
    set (sf6 := upd_local_sf sf5 (Maps.add (ssname fresh 6) (I1 bb) (stack_vars sf5))).
    (* the branch *)
    assert (Ev7 : exp_eval st2 sf6 stk G (Some (DTYPE_I 1 : dtyp)) (EXP_Ident (ID_Local (ssname fresh 6))) (I1 bb)).
    { apply exp_eval_local. unfold sf6. rewrite LLVM_instr_lemmas.stack_vars_upd. apply LLVM_instr_lemmas.rfind_add_eq. }
    eapply fgoal_term; [apply sim_result_closed|apply Flatten_sem.is_flat_ssname|eexists; exact Ev7|apply LLVM_instr_lemmas.term_br, Ev7|].
    intros sf6' Hag6. cbn [LLVM_sim.continue].
    (* frames *)
    assert (Hfind : forall r, (forall k, (1 <= k <= 6)%nat -> r <> ssname fresh k) -> Flatten_sem.is_flat r = false ->
                              RM.find r (stack_vars sf6') = RM.find r (stack_vars sf)).
    { intros r Hr Hfl. rewrite (Hag6 r Hfl). unfold sf6, sf5, sf4, sf3, sf2, sf1, LLVM_instr_lemmas.alloca_locals.
      rewrite !LLVM_instr_lemmas.stack_vars_upd.
      rewrite !LLVM_instr_lemmas.rfind_add_neq; [reflexivity|..]; intros E'; (eapply Hr; [|symmetry; exact E']); lia. }
    assert (Htl6 : tinfo_local sf6').
    { unfold tinfo_local, LLVM_sim.tinfo_local. rewrite Hfind; [exact Htl| |reflexivity].
      intros k _ E'. unfold ssname in E'. discriminate. }
    assert (Hrel6 : env_rel (occurs_free (Econstr x t ys e')) rho env sf6' st2).
    { intros y Hy. destruct (Hrel2 y Hy) as (v' & Hv & Hc). exists v'. split; [exact Hv|].
      destruct (is_fun fs y); [exact Hc|]. destruct Hc as (z & Hz & Hs). exists z. split; [|exact Hs].
      rewrite Hfind; [exact Hz| |eapply LLVM_sim.env_ok_not_flat; eauto].
      intros k _. eapply (LLVM_sim.env_ok_not_ssname cenv prim_of); eauto. lia. }
    destruct bb eqn:Ebb.
    - (* enough room: allocate directly *)
      assert (Hroom2 : room st2 tinfo (Z.of_N cw)).
      { exists alloc, limit. split; [exact Ha2|]. split; [exact Hl2|].
        pose proof (prog_chunk_small x t ys e' Hsub Hne) as Hc8. fold cw in Hc8.
        unfold bb in Ebb. apply Z.leb_le in Ebb.
        pose proof (ptr_to_int_range limit). pose proof (ptr_to_int_range alloc).
        rewrite Nat2Z.inj_mul, N_nat_Z in Ebb. rewrite !Z.mod_small in Ebb; lia. }
      destruct (roots_words _ rho env sf6' st2 roots Hrel6) as (wsd & Hw1 & Hw2).
      { intros r Hr. split; [apply (root_fv x t ys e' r Hr)|apply hd_roots_spec in Hr; tauto]. }
      eapply alloc_block_sim; eauto.
      + apply fext_mstep_empty, Hms.
      + intros y Hy Hf. destruct (Hrel y Hy) as (v' & Hv & Hc). rewrite Hf in Hc. destruct Hc as (rho' & ->). eauto.
    - (* collect *)
      assert (Hssn : forall k v0, RM.find (ssname fresh k) (stack_vars sf6) = Some v0 ->
                                 RM.find (ssname fresh k) (stack_vars sf6') = Some v0).
      { intros k v0 H. rewrite (Hag6 _ (Flatten_sem.is_flat_ssname _ _)). exact H. }
      assert (Hrel6' : env_rel (occurs_free (Econstr x t ys e')) rho env sf6' st).
      { intros y Hy. destruct (Hrel y Hy) as (v' & Hv & Hc). exists v'. split; [exact Hv|].
        destruct (is_fun fs y); [exact Hc|]. destruct Hc as (z & Hz & Hs). exists z. split; [|exact Hs].
        rewrite Hfind; [exact Hz| |eapply LLVM_sim.env_ok_not_flat; eauto].
        intros k _. eapply (LLVM_sim.env_ok_not_ssname cenv prim_of); eauto. lia. }
      eapply gc_path_sim; eauto.
      + apply Hssn. unfold sf6, sf5, sf4, sf3, sf2, sf1, LLVM_instr_lemmas.alloca_locals.
        rewrite !LLVM_instr_lemmas.stack_vars_upd.
        repeat (rewrite LLVM_instr_lemmas.rfind_add_eq ||
                (rewrite LLVM_instr_lemmas.rfind_add_neq by (intros E'; apply ssname_inj in E'; lia))).
        reflexivity.
      + apply Hssn. unfold sf6, sf5, sf4, sf3, sf2, sf1, LLVM_instr_lemmas.alloca_locals.
        rewrite !LLVM_instr_lemmas.stack_vars_upd.
        repeat (rewrite LLVM_instr_lemmas.rfind_add_eq ||
                (rewrite LLVM_instr_lemmas.rfind_add_neq by (intros E'; apply ssname_inj in E'; lia))).
        reflexivity.
  Qed.

  (* ---------------------------------------------------------------- *)
  (** *** The [Econstr] case *)

  Theorem sim_case_constr x t ys e' rho v vs :
    get_list ys rho = Some vs ->
    sim_stmt (M.set x (Vconstr t vs) rho) e' v ->
    sim_stmt rho (Econstr x t ys e') v.
  Proof.
    intros Hget IH. destruct ys as [|y ys0].
    - cbn in Hget. injection Hget as <-. apply sim_case_constr_nil, IH.
    - intros env chunk fresh blks f' B va c st sf stk fp rs vsr Hbo Hsub Hub Hdis Henv Htr Hbin HI Htl Hrel Hroom.
      destruct (N.leb (hd_nwords (y :: ys0)) chunk) eqn:Hl.
      + apply (sim_case_constr_member x t (y :: ys0) e' rho v vs ltac:(discriminate) Hget IH env chunk fresh blks f' B va c
                 st sf stk fp rs vsr Hl Hbo Hsub Hub Hdis Henv Htr Hbin HI Htl Hrel Hroom).
      + apply (sim_case_constr_head x t (y :: ys0) e' rho v vs ltac:(discriminate) Hget IH env chunk fresh blks f' B va c
                 st sf stk fp rs vsr Hl Hbo Hsub Hub Hdis Henv Htr Hbin HI Htl Hrel).
  Qed.

End Constr.
