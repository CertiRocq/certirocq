(** * The read-only cases of [LLVM_sim.sim_exp]

    [Ehalt], [Eproj], [Eprim_val] and [Ecase], each stated as an implication
    between [LLVM_sim.sim_stmt] instances (premise: the induction hypothesis
    for the continuation).

    Helper lemmas proved here that other cases also need:
    - [tr_env_ext]: [translate_cfg] only depends on the SSA environment at
      the free and bound variables of the expression;
    - [env_restrict] / [env_ok_restrict]: [env_ok] is not monotone in its set
      of live variables (a variable that is no longer live must be under its
      ANF name), so the induction hypothesis for a continuation [e'] is used
      with the environment restricted to the free variables of [e'];
    - [bound_not_fun]: a variable bound in a function body is not a
      top-level function;
    - [reads_word_wild]: a word readable through some pointer is readable
      through the wildcard-provenance pointer at the same address
      ([inttoptr]);
    - [sim_result_eutt]: [sim_result] is invariant under [eutt]. *)

From Stdlib Require Import ZArith NArith List Lia String Program Morphisms Classical_Prop Bool Relations.Relation_Operators Relations.Operators_Properties.
From ITree Require Import ITree Eq.Eqit Interp.InterpFacts Interp.RecursionFacts.
From ExtLib Require Import Structures.Monads.

From CertiRocq.LambdaANF Require Import term term_util eval identifiers List_util set_util.
From CertiRocq.Common Require Import AstCommon.
From CertiRocq.CodegenLLVM Require Import LambdaANF_to_LLVM Flatten
     LambdaANF_to_LLVM_statement LLVM_interp_lemmas LLVM_call_lemmas LLVM_convert
     LLVM_exp_lemmas LLVM_mem_lemmas LLVM_emit_syntax LLVM_emit_facts.
From CertiRocq.CodegenLLVM Require Flatten_sem LLVM_instr_lemmas LLVM_sim.

From Vellvm Require Import
  Utils Syntax Params
  Interfaces.Memory Implementations.Memory
  Semantics.DynamicValues Semantics.LLVMEvents Semantics.Denotation
  Semantics.InterpretationStack Semantics.TopLevel Handlers.
From Vellvm Require Import Semantics.Operations.Gep.

Import ListNotations.
Import MonadNotation.
Open Scope monad_scope.
Open Scope Z_scope.

Unset Implicit Arguments.
Set Bullet Behavior "Strict Subproofs".

Local Notation exp := term.exp.

(* ------------------------------------------------------------------ *)
(** ** Syntactic helpers *)

Lemma nthN_nth_error {A} (l : list A) n : nthN l n = nth_error l (N.to_nat n).
Proof.
  revert n. induction l as [|a l IH]; intros n.
  - rewrite nthN_equation. destruct n as [|p]; [reflexivity|]. destruct (N.to_nat (N.pos p)); reflexivity.
  - destruct n as [|p] eqn:E.
    + reflexivity.
    + rewrite nthN_equation. rewrite IH.
      replace (N.to_nat (N.pos p)) with (S (N.to_nat (N.pos p - 1))) by lia. reflexivity.
Qed.

Fixpoint fds_bodies (fds : fundefs) : list exp :=
  match fds with Fnil => [] | Fcons _ _ _ e fds' => e :: fds_bodies fds' end.

Lemma dsubterm_fds_bodies e fds : dsubterm_fds_e e fds -> In e (fds_bodies fds).
Proof. induction 1; simpl; auto. Qed.

Lemma bodies_bound fds e x : In e (fds_bodies fds) -> bound_var e x -> bound_var_fundefs fds x.
Proof.
  induction fds as [f t ys e' fds IH|]; simpl; [|tauto].
  intros [<-|H] Hx; [constructor 3; exact Hx|constructor 2; apply IH; auto].
Qed.

Lemma bound_var_dsubterm e e2 : dsubterm_e e e2 -> forall x, bound_var e x -> bound_var e2 x.
Proof.
  intros H x Hx. destruct H; try (now eauto); try (now econstructor; eauto).
  apply Bound_Efun1. apply dsubterm_fds_bodies in H. eapply bodies_bound; eauto.
Qed.

Lemma bound_var_subterm_or_eq e e2 : subterm_or_eq e e2 -> forall x, bound_var e x -> bound_var e2 x.
Proof.
  induction 1; intros; eauto. eapply bound_var_dsubterm; eauto.
Qed.

Lemma In_fun_ids fds f : In f (fun_ids fds) -> name_in_fundefs fds f.
Proof.
  induction fds as [g t xs e fds IH|]; simpl; [|tauto].
  intros [<-|H]; [left; constructor|right; apply IH, H].
Qed.

Lemma is_fun_true fs f : is_fun fs f = true -> In f fs.
Proof.
  unfold is_fun. intros H. apply existsb_exists in H. destruct H as (g & Hg & E).
  apply Pos.eqb_eq in E. subst. exact Hg.
Qed.

Lemma ub_fundefs_names fds :
  unique_bindings_fundefs fds ->
  forall e, In e (fds_bodies fds) -> forall x, bound_var e x -> ~ name_in_fundefs fds x.
Proof.
  induction 1 as [f t ys e defs Hf1 Hf2 D1 D2 D3 Hys Hnd Hub Hubf IH|]; simpl; [|tauto].
  intros e' [<-|Hin] x Hx Hn.
  - destruct Hn as [? Hn|? Hn].
    + inversion Hn; subst. contradiction.
    + apply name_in_fundefs_bound_var_fundefs in Hn. destruct D3 as [D3]. apply (D3 x). split; auto.
  - destruct Hn as [? Hn|? Hn].
    + inversion Hn; subst. apply Hf2. eapply bodies_bound; eauto.
    + eapply IH; eauto.
Qed.

(** A variable bound in a (non-[Efun]) subterm of the program is not a
    top-level function. *)
Lemma bound_not_fun fds main e x :
  unique_bindings (Efun fds main) ->
  subterm_or_eq e (Efun fds main) ->
  (forall fds' e0, e <> Efun fds' e0) ->
  bound_var e x -> is_fun (fun_ids fds) x = false.
Proof.
  intros Hub Hsub Hnf Hx.
  destruct (is_fun (fun_ids fds) x) eqn:E; [|reflexivity]. exfalso.
  apply is_fun_true, In_fun_ids in E.
  inversion Hub as [| | | | |? ? Hubm Hubf D| | | |]; subst.
  apply clos_rt_rtn1 in Hsub. inversion Hsub as [|y z Hd Hrt]; subst; [eapply Hnf; reflexivity|].
  apply clos_rtn1_rt in Hrt. pose proof (bound_var_subterm_or_eq _ _ Hrt x Hx) as Hy.
  inversion Hd; subst.
  - eapply ub_fundefs_names; eauto. apply dsubterm_fds_bodies; auto.
  - destruct D as [D]. apply (D x). split; auto. apply name_in_fundefs_bound_var_fundefs; auto.
Qed.

(* ------------------------------------------------------------------ *)
(** ** [translate_cfg] only reads the environment at free and bound variables *)

Section EnvExt.
  Variables (go ga : ctor_tag -> N) (po : positive -> option (string * bool)) (fs : list positive).
  Notation tr := (translate_cfg go ga po fs).

  Lemma gvar_ext env env' v : env v = env' v -> gvar fs env v = gvar fs env' v.
  Proof. intros H. unfold gvar, nvar. rewrite H. reflexivity. Qed.

  Lemma gcallee_ext env env' v : env v = env' v -> gcallee fs env v = gcallee fs env' v.
  Proof. intros H. unfold gcallee, nvar. rewrite H. reflexivity. Qed.

  Lemma store_fields_ext env env' vp i ys :
    (forall y, In y ys -> env y = env' y) -> store_fields fs env vp i ys = store_fields fs env' vp i ys.
  Proof.
    revert i. induction ys as [|y ys IH]; intros i H; [reflexivity|]. simpl.
    rewrite (gvar_ext env env' y) by (apply H; left; reflexivity).
    rewrite IH by (intros; apply H; right; assumption). reflexivity.
  Qed.

  Lemma spill_code_ext env env' rp aty i rs :
    (forall y, In y rs -> env y = env' y) -> spill_code env rp aty i rs = spill_code env' rp aty i rs.
  Proof.
    revert i. induction rs as [|y rs IH]; intros i H; [reflexivity|]. simpl. unfold nvar.
    rewrite (H y) by (left; reflexivity).
    rewrite IH by (intros; apply H; right; assumption). reflexivity.
  Qed.

  Lemma phi_list_ext env env' seed chk gc i rs :
    (forall y, In y rs -> env y = env' y) -> phi_list env seed chk gc i rs = phi_list env' seed chk gc i rs.
  Proof.
    revert i. induction rs as [|y rs IH]; intros i H; [reflexivity|]. simpl. unfold nvar.
    rewrite (H y) by (left; reflexivity).
    rewrite IH by (intros; apply H; right; assumption). reflexivity.
  Qed.

  Lemma call_args_ext env env' ys :
    (forall y, In y ys -> env y = env' y) -> call_args fs env ys = call_args fs env' ys.
  Proof.
    intros H. unfold call_args. f_equal. apply map_ext_in. intros y Hy. rewrite (gvar_ext env env' y); auto.
  Qed.

  Lemma prim_call_ext env env' p ys :
    (forall y, In y ys -> env y = env' y) -> prim_call po fs env p ys = prim_call po fs env' p ys.
  Proof.
    intros H. unfold prim_call.
    assert (E : map (fun y => ((val_ty, gvar fs env y), @nil param_attr)) ys =
                map (fun y => ((val_ty, gvar fs env' y), @nil param_attr)) ys).
    { apply map_ext_in. intros y Hy. rewrite (gvar_ext env env' y); auto. }
    rewrite E. reflexivity.
  Qed.

  Lemma env_set_list_ext (P : var -> Prop) env env' vs rs :
    (forall z, P z -> env z = env' z) -> forall z, P z -> env_set_list env vs rs z = env_set_list env' vs rs z.
  Proof.
    intros H. revert rs. induction vs as [|v vs IH]; intros [|r rs] z Hz; simpl; auto.
    unfold env_set. destruct (Pos.eqb z v); auto.
  Qed.

  Lemma alloc_code_ext env env' fresh x t ys :
    (forall y, In y ys -> env y = env' y) ->
    alloc_code go ga fs env fresh x t ys = alloc_code go ga fs env' fresh x t ys.
  Proof. intros H. unfold alloc_code. rewrite (store_fields_ext env env'); auto. Qed.

  Definition fvbv (e : exp) (z : var) : Prop := occurs_free e z \/ bound_var e z.

  Definition tr_ext (e : exp) : Prop :=
    forall env env' chunk fresh, (forall z, fvbv e z -> env z = env' z) ->
      tr env chunk e fresh = tr env' chunk e fresh.

  Lemma arm_loop_ext env env' arms fr :
    Forall (fun a => tr_ext (snd a)) arms ->
    (forall c e, In (c, e) arms -> forall z, fvbv e z -> env z = env' z) ->
    arm_loop_d (fun ae fr => tr env 0%N ae fr) go ga arms fr =
    arm_loop_d (fun ae fr => tr env' 0%N ae fr) go ga arms fr.
  Proof.
    revert fr. induction arms as [|[c e] arms IH]; intros fr HF H; [reflexivity|].
    inversion HF as [|? ? He HF']; subst. simpl in He.
    destruct (tr env' 0%N e fr) as [ab fr1] eqn:E.
    rewrite (arm_loop_cons _ _ (fun ae fr => tr env' 0%N ae fr) c e arms fr ab fr1 E).
    rewrite <- (He env env') in E by (eapply H; left; reflexivity).
    rewrite (arm_loop_cons _ _ (fun ae fr => tr env 0%N ae fr) c e arms fr ab fr1 E).
    rewrite IH; auto. intros c' e' Hin. eapply H. right. exact Hin.
  Qed.

  Lemma occurs_free_Ecase_In y arms c e z :
    In (c, e) arms -> occurs_free e z -> occurs_free (Ecase y arms) z.
  Proof.
    induction arms as [|[c' e'] arms IH]; intros Hin Hz; [destruct Hin|].
    destruct Hin as [E|Hin]; [injection E as -> ->; constructor; exact Hz|].
    apply Free_Ecase3. apply IH; auto.
  Qed.

  Theorem tr_env_ext : forall e, tr_ext e.
  Proof.
    apply exp_ind_nested; unfold tr_ext, fvbv.
    - (* Econstr *)
      intros x t ys e' IH env env' chunk fresh H.
      assert (H' : forall z, occurs_free e' z \/ bound_var e' z -> env z = env' z).
      { intros z [Hz|Hz]; apply H; [|right; constructor 2; exact Hz].
        destruct (Pos.eq_dec x z) as [<-|Hne]; [right; constructor|left; constructor 2; auto]. }
      assert (Hys : forall y, In y ys -> env y = env' y) by (intros y Hy; apply H; left; constructor; exact Hy).
      destruct ys as [|y0 ys0] eqn:Eys.
      + cbn [translate_cfg]. rewrite (IH env env') by exact H'. reflexivity.
      + rewrite <- Eys in *. assert (Hne : ys <> []) by (subst; discriminate).
        destruct (N.leb (hd_nwords ys) chunk) eqn:Hl.
        * destruct (tr env' (chunk - hd_nwords ys)%N e' (Pos.succ fresh)) as [blks f'] eqn:E.
          rewrite (tr_constr_member _ _ _ _ env' chunk x t ys e' fresh blks f' Hne Hl E).
          rewrite <- (IH env env') in E by exact H'.
          rewrite (tr_constr_member _ _ _ _ env chunk x t ys e' fresh blks f' Hne Hl E).
          rewrite (alloc_code_ext env env'); auto.
        * assert (Hroots : forall r, In r (hd_roots fs x ys e') -> env r = env' r).
          { intros r Hr. apply hd_roots_spec in Hr. destruct Hr as [_ [[H1 H2]|H1]]; apply H; left.
            - constructor 2; auto.
            - constructor; exact H1. }
          assert (Henv : forall z, occurs_free (Econstr x t ys e') z \/ bound_var (Econstr x t ys e') z ->
                    hd_env fs env fresh x ys e' z = hd_env fs env' fresh x ys e' z).
          { intros z Hz. unfold hd_env, safepoint_env. eapply env_set_list_ext; [exact H|exact Hz]. }
          destruct (tr (hd_env fs env' fresh x ys e') (chunk_words e') e' (Pos.succ fresh)) as [blks f0] eqn:E.
          rewrite (tr_constr_head _ _ _ _ env' chunk x t ys e' fresh blks f0 Hne Hl E).
          rewrite <- (IH (hd_env fs env fresh x ys e')) in E.
          2:{ intros z [Hz|Hz]; apply Henv; [|right; constructor 2; exact Hz].
              destruct (Pos.eq_dec x z) as [<-|Hne']; [right; constructor|left; constructor 2; auto]. }
          rewrite (tr_constr_head _ _ _ _ env chunk x t ys e' fresh blks f0 Hne Hl E).
          unfold hd_gc_blk, hd_alloc_blk.
          rewrite (spill_code_ext env env') by exact Hroots.
          rewrite (phi_list_ext env env') by exact Hroots.
          rewrite (alloc_code_ext (hd_env fs env fresh x ys e') (hd_env fs env' fresh x ys e')).
          -- reflexivity.
          -- intros y Hy. apply Henv. left. constructor. exact Hy.
    - (* Ecase *)
      intros y arms HF env env' chunk fresh H.
      rewrite !tr_case_unfold. rewrite (arm_loop_ext env env').
      + destruct (arm_loop_d _ go ga arms fresh) as [[ab ae] f1].
        unfold case_result, case_test_blk, case_unboxed_blk, case_boxed_blk, load_header, nvar.
        rewrite (H y) by (left; constructor). reflexivity.
      + exact HF.
      + intros c e Hin z [Hz|Hz]; apply H; [left; eapply occurs_free_Ecase_In; eauto|right; econstructor; eauto].
    - (* Eproj *)
      intros x t n y e' IH env env' chunk fresh H. cbn [translate_cfg].
      rewrite (IH env env').
      + unfold load_field, gep_field, nvar. rewrite (H y) by (left; apply Free_Eproj1). reflexivity.
      + intros z [Hz|Hz]; apply H; [|right; apply Bound_Eproj2; exact Hz].
        destruct (Pos.eq_dec x z) as [<-|Hne]; [right; apply Bound_Eproj1|left; apply Free_Eproj2; auto].
    - (* Eletapp *)
      intros x f ft ys e' IH env env' chunk fresh H.
      assert (Hroots : forall r, In r (la_roots fs x e') -> env r = env' r).
      { intros r Hr. apply la_roots_spec in Hr. destruct Hr as (_ & H1 & H2). apply H. left. apply Free_Eletapp2; auto. }
      destruct (tr (la_env fs env' fresh x e') 0%N e' (Pos.succ fresh)) as [blks f'] eqn:E.
      rewrite (tr_letapp _ _ _ _ env' chunk x f ft ys e' fresh blks f' E).
      rewrite <- (IH (la_env fs env fresh x e')) in E.
      2:{ intros z Hz. unfold la_env. eapply env_set_list_ext with (P := fvbv (Eletapp x f ft ys e')); [exact H|].
          destruct Hz as [Hz|Hz]; [|right; apply Bound_Eletapp2; exact Hz].
          destruct (Pos.eq_dec x z) as [<-|Hne]; [right; apply Bound_Eletapp1|left; apply Free_Eletapp2; auto]. }
      rewrite (tr_letapp _ _ _ _ env chunk x f ft ys e' fresh blks f' E).
      unfold la_code. rewrite (spill_code_ext env env') by exact Hroots.
      rewrite (gcallee_ext env env' f) by (apply H; left; apply Free_Eletapp1; left; reflexivity).
      rewrite (call_args_ext env env') by (intros y Hy; apply H; left; apply Free_Eletapp1; right; exact Hy).
      reflexivity.
    - (* Efun *)
      intros fds e' IH env env' chunk fresh H. rewrite !tr_fun. apply IH.
      intros z [Hz|Hz]; apply H; [|right; apply Bound_Efun2; exact Hz].
      destruct (classic (name_in_fundefs fds z)) as [Hn|Hn].
      + right. apply Bound_Efun1. apply name_in_fundefs_bound_var_fundefs. exact Hn.
      + left. constructor; auto.
    - (* Eapp *)
      intros f ft ys env env' chunk fresh H. rewrite !tr_app.
      rewrite (gcallee_ext env env' f) by (apply H; left; constructor).
      rewrite (call_args_ext env env') by (intros y Hy; apply H; left; constructor; exact Hy).
      reflexivity.
    - (* Eprim_val *)
      intros x pv e' IH env env' chunk fresh H. cbn [translate_cfg].
      rewrite (IH env env'); [reflexivity|].
      intros z [Hz|Hz]; apply H; [|right; apply Bound_Eprim_val2; exact Hz].
      destruct (Pos.eq_dec x z) as [<-|Hne]; [right; apply Bound_Eprim_val1|left; apply Free_Eprim_val; auto].
    - (* Eprim *)
      intros x p ys e' IH env env' chunk fresh H.
      destruct (tr env' 0%N e' fresh) as [blks f'] eqn:E.
      rewrite (tr_prim _ _ _ _ env' chunk x p ys e' fresh blks f' E).
      rewrite <- (IH env env') in E.
      2:{ intros z [Hz|Hz]; apply H; [|right; apply Bound_Eprim2; exact Hz].
          destruct (Pos.eq_dec x z) as [<-|Hne]; [right; apply Bound_Eprim1|left; apply Free_Eprim2; auto]. }
      rewrite (tr_prim _ _ _ _ env chunk x p ys e' fresh blks f' E).
      rewrite (prim_call_ext env env') by (intros y Hy; apply H; left; apply Free_Eprim1; exact Hy).
      reflexivity.
    - (* Ehalt *)
      intros x env env' chunk fresh H. rewrite !tr_halt.
      rewrite (gvar_ext env env' x) by (apply H; left; constructor). reflexivity.
  Qed.
End EnvExt.

(* ------------------------------------------------------------------ *)
(** ** Restricting the SSA environment to the live variables *)

Definition env_restrict (e : exp) (env : nenv) : nenv :=
  fun z => if in_dec Pos.eq_dec z (PS.elements (exp_fv e)) then env z else Raw (Zpos z).

Lemma env_restrict_fv e env z : occurs_free e z -> env_restrict e env z = env z.
Proof.
  intros H. unfold env_restrict. destruct (in_dec _ _ _) as [_|Hn]; [reflexivity|].
  exfalso. apply Hn. apply In_elements_fv. exact H.
Qed.

Lemma env_restrict_nfv e env z : ~ occurs_free e z -> env_restrict e env z = Raw (Zpos z).
Proof.
  intros H. unfold env_restrict. destruct (in_dec _ _ _) as [Hi|_]; [|reflexivity].
  exfalso. apply H. apply In_elements_fv. exact Hi.
Qed.

Lemma env_ok_restrict S e env fresh fresh' :
  LLVM_sim.env_ok S env fresh -> (fresh <= fresh')%positive ->
  LLVM_sim.env_ok (occurs_free e) (env_restrict e env) fresh'.
Proof.
  intros H Hle y. split.
  - intros Hy. rewrite env_restrict_fv by exact Hy. destruct (H y) as [H1 H2].
    destruct (classic (S y)) as [HS|HS].
    + destruct (H1 HS) as [E|(s & k & Hs & E)]; [left; exact E|right; exists s, k; split; [lia|exact E]].
    + left. apply H2, HS.
  - intros Hy. apply env_restrict_nfv, Hy.
Qed.

(** The translation under the restricted environment is the same, provided
    the bound variables of [e] are not live (so that [env_ok] puts them under
    their ANF names). *)
Lemma tr_restrict go ga po fs S env fresh e chunk fr :
  LLVM_sim.env_ok S env fresh -> (forall z, bound_var e z -> ~ S z) ->
  translate_cfg go ga po fs env chunk e fr = translate_cfg go ga po fs (env_restrict e env) chunk e fr.
Proof.
  intros H Hb. apply tr_env_ext. intros z [Hz|Hz].
  - rewrite env_restrict_fv; auto.
  - destruct (classic (occurs_free e z)) as [Hf|Hf]; [rewrite env_restrict_fv; auto|].
    rewrite env_restrict_nfv by exact Hf. destruct (H z) as [_ H2]. apply H2, Hb, Hz.
Qed.

Lemma env_rel_restrict cenv fds G tinfo e rho env sf st :
  LLVM_sim.env_rel cenv fds G tinfo (occurs_free e) rho env sf st ->
  LLVM_sim.env_rel cenv fds G tinfo (occurs_free e) rho (env_restrict e env) sf st.
Proof. intros H x Hx. rewrite env_restrict_fv by exact Hx. apply H, Hx. Qed.

(** [env_ok] for a set containing the live variables of the continuation,
    and the continuation's binder (which must be dead before). *)
Lemma env_ok_bind S S' env fresh :
  LLVM_sim.env_ok S env fresh -> (forall y, S y -> S' y) ->
  LLVM_sim.env_ok S' env fresh.
Proof.
  intros H Hs y. destruct (H y) as [H1 H2]. split.
  - intros Hy. destruct (classic (S y)) as [HS|HS]; [apply H1, HS|left; apply H2, HS].
  - intros Hy. apply H2. intros HS. apply Hy, Hs, HS.
Qed.

(* ------------------------------------------------------------------ *)
(** ** Reading through a wildcard pointer *)

Lemma map_monad_acc_EOU_intro {A B} (f : A -> EOU.EOU B) l bs :
  Forall2 (fun a b => f a = ret b) l bs -> map_monad_acc f l = ret bs.
Proof.
  intros H. unfold map_monad_acc.
  assert (G : forall acc, (fix loop (acc : list B) (l : list A) : EOU.EOU (list B) :=
       match l with
       | [] => ret (rev_append acc [])
       | a :: l' => b <- f a;; loop (b :: acc) l'
       end) acc l = ret (rev_append acc bs)).
  { induction H as [|a b l bs Hab H IH]; intros acc; [reflexivity|].
    cbn [bind EOU.EOU_monad]. rewrite Hab. cbn. apply IH. }
  apply G.
Qed.

Lemma int_to_ptr_range z pr q : int_to_ptr z pr = EOU.raise_ret q -> 0 <= z < 2 ^ 64.
Proof.
  intros H. assert (E : ptr_to_int q = z) by (eapply ptr_to_int_int_to_ptr; eauto). pose proof (ptr_to_int_range q). lia.
Qed.

Lemma reads_word_wild st q q' z :
  reads_word st q z -> ptr_to_int q' = ptr_to_int q -> ptr_provenance q' = wildcard_prov ->
  reads_word st q' z.
Proof.
  intros Hr E P. apply reads_word_runs, read_dvalue_runs in Hr.
  destruct Hr as (_ & ptrs & bs & Hp & HF & Hv).
  unfold get_consecutive_ptrs in Hp. cbn [bind EOU.EOU_monad] in Hp.
  destruct (intptr_seq 0 (sizeof_dtyp (DTYPE_I 64))) as [| | |ixs] eqn:Es; try discriminate.
  apply map_monad_acc_EOU' in Hp.
  assert (Hq : exists ptrs', Forall2 (fun ix r => handle_gep_ptr (DTYPE_I 8) q' [DVALUE_Base (DVALUE_Iptr ix)] = ret r) ixs ptrs' /\
                        Forall2 (fun r' r => ptr_to_int r' = ptr_to_int r /\ ptr_provenance r' = wildcard_prov) ptrs' ptrs).
  { clear HF Hv Es. induction Hp as [|ix r ixs ptrs Hr Hp IH]; [exists []; split; constructor|].
    destruct IH as (ptrs' & H1 & H2).
    assert (Hi : ptr_to_int r = ptr_to_int q + Z.of_N (sizeof_dtyp (DTYPE_I 8)) * to_Z ix) by (eapply handle_gep_ptr_ix; exact Hr).
    assert (Hrange : 0 <= ptr_to_int q' + Z.of_N (sizeof_dtyp (DTYPE_I 8)) * to_Z ix < 2 ^ 64).
    { rewrite E, <- Hi. apply ptr_to_int_range. }
    destruct (@int_to_ptr_total _ wildcard_prov Hrange) as (r' & Hr' & Hi' & Hp').
    exists (r' :: ptrs'). split; constructor; auto.
    - apply handle_gep_ptr_ix'. rewrite P, Hr'. reflexivity.
    - split; [rewrite Hi', E, Hi; reflexivity|exact Hp']. }
  destruct Hq as (ptrs' & H1 & H2).
  exists st. apply read_dvalue_runs. split; [reflexivity|]. exists ptrs', bs. split; [|split; [|exact Hv]].
  - unfold get_consecutive_ptrs. cbn [bind EOU.EOU_monad]. rewrite Es. apply map_monad_acc_EOU_intro. exact H1.
  - clear Hp H1 Es Hv. revert bs HF. induction H2 as [|r' r ptrs' ptrs [Hi Hw] H2 IH]; intros bs HF;
      inversion HF as [|? b ? bs' Hb HF']; subst; constructor; [|apply IH; exact HF'].
    destruct Hb as (aid & Hl & _). exists aid. rewrite Hi. split; [exact Hl|]. rewrite Hw. reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(** ** Running the tail of a flattened block *)

Lemma tail_flat ctx va B (b : LLVMAst.block dtyp) c s :
  Flatten_sem.run ctx (LLVM_sim.tail_of va B (LLVM_sim.flatB b c)) s
  ≈ Flatten_sem.run ctx (Flatten_sem.flat_tail va (blk_code b) (blk_term b) c
                           (LLVM_sim.continue va B (blk_id b))) s.
Proof.
  unfold LLVM_sim.tail_of. rewrite LLVM_sim.flatB_id. unfold LLVM_sim.flatB.
  apply Flatten_sem.flat_block_tail.
Qed.

(** Stepping over one instruction prepended by [prepend_code]. *)
Lemma tail_prepend ctx va B id ins (b : LLVMAst.block typ) rest c st sf stk g st1 sf1 stk1 g1 :
  let ci := (id, cinstr ins, []) in
  Flatten_sem.instr_ok ci -> Flatten_sem.instr_evals st sf stk g ci ->
  LLVM_instr_lemmas.runs ctx (denote_instr ci va) (st, ((sf, stk), g)) (st1, ((sf1, stk1), g1)) tt ->
  exists c1 sf1', Flatten_sem.agree_except c c1 sf1 sf1' /\
    Flatten_sem.run ctx (LLVM_sim.tail_of va B (LLVM_sim.flatB (cblock (LLVM_sim.hd_blk (prepend_code [(id, ins, [])] (b :: rest)))) c))
                     (st, ((sf, stk), g))
    ≈ Flatten_sem.run ctx (LLVM_sim.tail_of va B (LLVM_sim.flatB (cblock (LLVM_sim.hd_blk (b :: rest))) c1))
                     (st1, ((sf1', stk1), g1)).
Proof.
  intros ci Hok Hev Hr. cbn [prepend_code LLVM_sim.hd_blk].
  setoid_rewrite tail_flat. rewrite !cblock_eq. cbn [blk_id blk_phis blk_code blk_term blk_comments app].
  rewrite ccode_cons.
  destruct (Flatten_sem.flat_tail_instr ctx va c c ci (ccode (blk_code b))
              (let '(id0, t, md) := blk_term b in (id0, cterm t, tfmap (typ_to_dtyp []) md))
              (LLVM_sim.continue va B (blk_id b)) st sf sf stk g st1 sf1 stk1 g1
              Hok Hev (Pos.le_refl _) (Flatten_sem.agree_except_refl _ _ _) Hr) as (_ & sf1' & Hag & E).
  exists (snd (Flatten_sem.flat_instrP ci c)), sf1'. split; [exact Hag|exact E].
Qed.

(* ------------------------------------------------------------------ *)
(** ** The [Ecase] dispatch tables *)

Section Arms.
  Variables (go ga : ctor_tag -> N) (po : positive -> option (string * bool)) (fs : list positive).
  Notation tr := (translate_cfg go ga po fs).

  Lemma arm_loop_lits env arms fr ab aedges f1 :
    arm_loop_d (fun ae fr => tr env 0%N ae fr) go ga arms fr = (ab, aedges, f1) ->
    Forall (fun ed => LLVM_instr_lemmas.lit64 (snd ed)) aedges.
  Proof.
    revert fr ab aedges f1. induction arms as [|[t0 e0] rest IH]; intros fr ab aedges f1 H.
    - rewrite arm_loop_nil in H. injection H as _ <- _. constructor.
    - destruct (tr env 0%N e0 fr) as [a1 fr1] eqn:E.
      rewrite (arm_loop_cons _ _ _ t0 e0 rest fr a1 fr1 E) in H.
      destruct (arm_loop_d _ go ga rest fr1) as [[rb re] f2] eqn:Er. injection H as _ <- _.
      constructor; [apply LLVM_instr_lemmas.lit64_nat|eapply IH; exact Er].
  Qed.

  Lemma Forall_lit64_filter (P : N -> bool) (aedges : list (N * (tint_literal * block_id))) :
    Forall (fun ed => LLVM_instr_lemmas.lit64 (snd ed)) aedges ->
    Forall LLVM_instr_lemmas.lit64 (map snd (filter (fun ae => P (fst ae)) aedges)).
  Proof.
    intros H. apply Forall_map. apply Forall_forall. intros x Hx.
    apply filter_In in Hx. rewrite Forall_forall in H. apply H, Hx.
  Qed.

  (** The switch on the ordinal of [t] over the arms of the class [P]
      selects the entry block of the first arm with tag [t]. *)
  Lemma arm_loop_find env arms fr ab aedges f1 t e' (P : N -> bool) dflt :
    arm_loop_d (fun ae fr => tr env 0%N ae fr) go ga arms fr = (ab, aedges, f1) ->
    findtag arms t = Some e' ->
    P (ga t) = true ->
    (go t < 1024)%N ->
    (forall t', In t' (map fst arms) -> (go t' < 1024)%N) ->
    (forall t', In t' (map fst arms) -> t' <> t -> P (ga t') = true -> go t' <> go t) ->
    exists fr0 ablks fr1,
      (fr <= fr0)%positive /\ tr env 0%N e' fr0 = (ablks, fr1) /\ ablks <> [] /\
      (forall b, In b ablks -> In b ab) /\
      LLVM_instr_lemmas.switch_dest (Z.of_N (go t)) dflt (map snd (filter (fun ae => P (fst ae)) aedges))
      = entry_id ablks fr0.
  Proof.
    revert fr ab aedges f1. induction arms as [|[t0 e0] rest IH]; intros fr ab aedges f1 H Hf HP Ht Hall Hd.
    - discriminate.
    - destruct (tr env 0%N e0 fr) as [a1 fr1] eqn:E.
      pose proof (translate_cfg_ok go ga po fs e0 env 0%N fr a1 fr1 E) as Hok.
      rewrite (arm_loop_cons _ _ _ t0 e0 rest fr a1 fr1 E) in H.
      destruct (arm_loop_d _ go ga rest fr1) as [[rb re] f2] eqn:Er. injection H as <- <- <-.
      assert (Ht0 : (go t0 < 1024)%N) by (apply Hall; left; reflexivity).
      cbn [findtag] in Hf. cbn [filter fst].
      destruct (M.elt_eq t0 t) as [->|Hne].
      + injection Hf as <-. rewrite HP. cbn [map snd].
        rewrite LLVM_instr_lemmas.switch_dest_nat by lia. rewrite N_nat_Z, Z.eqb_refl.
        exists fr, a1, fr1. split; [lia|]. split; [exact E|]. split; [exact (co_ne _ _ _ _ Hok)|].
        split; [intros b Hb; apply in_app_iff; left; exact Hb|reflexivity].
      + assert (Hrest := IH fr1 rb re f2 Er Hf HP Ht (fun t' H => Hall t' (or_intror H))
                           (fun t' H => Hd t' (or_intror H))).
        destruct Hrest as (fr0 & ablks & fr2 & Hle & E0 & Hne0 & Hin & Hsw).
        assert (Hlt := co_lt _ _ _ _ Hok).
        exists fr0, ablks, fr2. split; [lia|]. split; [exact E0|]. split; [exact Hne0|].
        split; [intros b Hb; apply in_app_iff; right; apply Hin, Hb|].
        destruct (P (ga t0)) eqn:HP0; [|exact Hsw].
        cbn [map snd]. rewrite LLVM_instr_lemmas.switch_dest_nat by lia.
        rewrite N_nat_Z. destruct (Z.eqb_spec (Z.of_N (go t)) (Z.of_N (go t0))) as [Eq|_]; [|exact Hsw].
        exfalso. apply (Hd t0 (or_introl eq_refl) Hne HP0). lia.
  Qed.
End Arms.

(* ------------------------------------------------------------------ *)
(** ** Source-side facts for [Ecase] *)

Lemma ub_case_arm y arms c e : unique_bindings (Ecase y arms) -> In (c, e) arms -> unique_bindings e.
Proof.
  induction arms as [|[c' e'] arms IH]; intros H Hin; [destruct Hin|].
  inversion H; subst. destruct Hin as [E|Hin]; [injection E as -> ->; assumption|]. apply IH; auto.
Qed.

(** Ordinals of distinct constructors of the same inductive in the same
    representation class are distinct ([cenv_ok]). *)
Lemma case_ords_distinct cenv arms t :
  cenv_ok cenv -> caseConsistent cenv arms t ->
  forall t', In t' (map fst arms) -> t' <> t -> ord_of cenv t' = ord_of cenv t ->
  (arity_of cenv t = 0%N <-> arity_of cenv t' <> 0%N).
Proof.
  intros Hc. induction 1 as [t|info info' l t t0 e Hg Hg' Hind Hcc IH]; intros t' Hin Hne Eord; [destruct Hin|].
  destruct Hin as [E|Hin]; [|apply IH; auto]. cbn in E. subst t'.
  unfold ord_of, arity_of in *. rewrite Hg, Hg' in Eord |- *. cbn in *.
  exact (Hc t t0 info info' (fun E => Hne (eq_sym E)) Hg Hg' Hind (eq_sym Eord)).
Qed.

Section CasesRead.

  Variable cenv : ctor_env.
  Variable pfs : prims.
  Variable prim_of : positive -> option (string * bool).
  Variable fds : fundefs.
  Variable heap_inv : state -> ptr -> Prop.
  Variable gc : list dvalue -> MCFGtop (exc + dvalue).
  Variable G : global_env.
  Variable ctx : CallE ~> itree (CallE +' MCFGEtop).
  Variable tinfo : ptr.

  Notation fs := (fun_ids fds).
  Notation tr := (translate_cfg (ord_of cenv) (arity_of cenv) prim_of (fun_ids fds)).
  Notation sim_result := (LLVM_sim.sim_result cenv fds heap_inv G tinfo).
  Notation env_rel := (LLVM_sim.env_rel cenv fds G tinfo).
  Notation stable_repr := (LLVM_sim.stable_repr cenv fds G tinfo).
  Notation INV := (LLVM_sim.INV cenv fds heap_inv G tinfo).
  Notation RUN := (Flatten_sem.run ctx).

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

  Variable main : term.exp.
  Hypothesis Hprog : llvm_restricted cenv fds main.

  Notation sim_stmt := (LLVM_sim.sim_stmt cenv prim_of fds heap_inv G ctx tinfo main).

  Lemma sim_result_eutt st stk fp rs vs v t t' :
    t ≈ t' -> sim_result st stk fp rs vs v t' -> sim_result st stk fp rs vs v t.
  Proof.
    intros E [(k & H)|(st' & sf' & z & H & R)].
    - left. exists k. etransitivity; [exact E|exact H].
    - right. exists st', sf', z. split; [|exact R]. unfold returns. etransitivity; [exact E|exact H].
  Qed.

  (** A returned word, with the invariant unchanged. *)
  Lemma sim_result_ret st stk fp rs vs v sf z t :
    t ≈ Ret ((st, ((sf, stk), G)), inr (I64 z)) ->
    INV st fp rs vs -> stable_repr st v z ->
    sim_result st stk fp rs vs v t.
  Proof.
    intros E HI Hs. right. exists st, sf, z. split; [exact E|]. split; [exact Hs|]. split; [exact HI|].
    split; [exists []; split; [symmetry; apply LLVM_sim.push_top_nil|constructor]|apply LLVM_sim.keeps_stack_refl].
  Qed.

  (** The value of a live variable, as an operand. *)
  Lemma env_rel_operand S rho env sf stk st x v :
    env_rel S rho env sf st -> S x -> M.get x rho = Some v ->
    exists z, exp_eval st sf stk G (Some (DTYPE_I 64 : dtyp)) (cexp (gvar fs env x)) (I64 z) /\ stable_repr st v z.
  Proof.
    intros Henv Hx Hget. destruct (Henv x Hx) as (v0 & Hv0 & Hc). rewrite Hget in Hv0. injection Hv0 as <-.
    destruct (is_fun fs x) eqn:Ef.
    - destruct Hc as (rho' & ->). destruct (G_funs x (is_fun_true _ _ Ef)) as (fp & Hfp).
      exists (ptr_to_int fp). split.
      + rewrite cexp_gvar_fun by exact Ef. apply exp_eval_ptrtoint, exp_eval_global, Hfp.
      + intros st2 _. constructor. exact Hfp.
    - destruct Hc as (z & Hz & Hs). exists z. split; [|exact Hs].
      rewrite cexp_gvar_local by exact Ef. apply exp_eval_local, Hz.
  Qed.

  (* ---------------------------------------------------------------- *)
  (** *** [Ehalt] *)

  Lemma sim_case_halt rho x v :
    M.get x rho = Some v -> sim_stmt rho (Ehalt x) v.
  Proof.
    intros Hx env chunk fresh blks f' B va c st sf stk fp rs vs
      Hbo Hsub Hub Hdis Hok Htr Hbl HI Htl Henv Hroom.
    rewrite tr_halt in Htr. injection Htr as <- <-. cbn [LLVM_sim.hd_blk].
    destruct (env_rel_operand _ _ _ _ stk _ x v Henv (Free_Ehalt x) Hx) as (z & Hz & Hs).
    change (sim_result st stk fp rs vs v
              (RUN (LLVM_sim.tail_of va B (LLVM_sim.flatB (cblock
                 (mk_block (Anon (Zpos fresh)) [] [] (IVoid 1%Z, TERM_Ret (val_ty, gvar fs env x), []) None)) c))
                 (st, ((sf, stk), G)))).
    rewrite cblock_eq. cbn [blk_id blk_phis blk_code blk_term blk_comments map].
    rewrite cterm_Ret. unfold ctexp. cbn [fst snd]. rewrite cty_val.
    set (tm := TERM_Ret (DTYPE_I 64 : dtyp, cexp (gvar fs env x))).
    assert (Hrun : LLVM_instr_lemmas.runs ctx (denote_terminator (IVoid 1%Z, tm, tfmap (typ_to_dtyp []) []))
                     (st, ((sf, stk), G)) (st, ((sf, stk), G)) (inr (I64 z))).
    { apply LLVM_instr_lemmas.term_ret. exact Hz. }
    assert (Htok : Flatten_sem.term_ok tm).
    { subst tm. cbn [Flatten_sem.term_ok]. destruct (is_fun fs x) eqn:Ef.
      - rewrite cexp_gvar_fun by exact Ef. exact I.
      - rewrite cexp_gvar_local by exact Ef. eapply LLVM_sim.env_ok_not_flat; exact Hok. }
    destruct (Flatten_sem.flat_tail_term ctx va c c (IVoid 1%Z) tm (tfmap (typ_to_dtyp []) [])
                (LLVM_sim.continue va B (Anon (Zpos fresh))) st sf sf stk G st sf stk G (inr (I64 z))
                Htok (ex_intro _ _ Hz) (Pos.le_refl _) (Flatten_sem.agree_except_refl _ _ _) Hrun)
      as (_ & sf1 & _ & Hfl).
    eapply sim_result_eutt; [rewrite tail_flat; exact Hfl|].
    eapply sim_result_ret; [|exact HI|exact Hs].
    cbn [LLVM_sim.continue]. apply Flatten_sem.run_ret.
  Qed.

  (* ---------------------------------------------------------------- *)
  (** *** Straight-line binders emitted with [prepend_code]

      Generic step: [e] is translated as one instruction binding [x],
      consed onto the entry block of the translation of [e'] (same
      environment, chunk and counter).  The instruction runs without
      touching memory and binds [x] to a word stably representing [v']. *)

  Lemma sim_prepend_bind (e e' : exp) (x : var) (ins : nenv -> instr typ) rho v' v :
    (forall env chunk fresh blks f', tr env chunk e' fresh = (blks, f') ->
       tr env chunk e fresh = (prepend_code [(IId (Raw (Zpos x)), ins env, [])] blks, f')) ->
    dsubterm_e e' e ->
    (forall fds' e0, e <> Efun fds' e0) ->
    (body_ok cenv e -> body_ok cenv e') ->
    (unique_bindings e -> unique_bindings e' /\ ~ bound_var e' x) ->
    bound_var e x ->
    (forall z, bound_var e' z -> bound_var e z) ->
    (forall z, occurs_free e' z -> z <> x -> occurs_free e z) ->
    (forall env fresh sf st stk va,
       LLVM_sim.env_ok (occurs_free e) env fresh ->
       env_rel (occurs_free e) rho env sf st ->
       exists zi, stable_repr st v' zi /\
         let ci := (IId (Raw (Zpos x)), cinstr (ins env), []) in
         Flatten_sem.instr_ok ci /\ Flatten_sem.instr_evals st sf stk G ci /\
         LLVM_instr_lemmas.runs ctx (denote_instr ci va) (st, ((sf, stk), G))
           (st, ((upd_local_sf sf (Maps.add (Raw (Zpos x)) (I64 zi) (stack_vars sf)), stk), G)) tt) ->
    sim_stmt (M.set x v' rho) e' v -> sim_stmt rho e v.
  Proof.
    intros Hshape Hds Hnf Hbo' Hub' Hbx Hbv Hfv Hsem IH
      env chunk fresh blks f' B va c st sf stk fp rs vs Hbo Hsub Hub Hdis Hok Htr Hbl HI Htl Henv Hroom.
    destruct (tr env chunk e' fresh) as [blks' f''] eqn:Ht'.
    rewrite (Hshape _ _ _ _ _ Ht') in Htr. injection Htr as <- <-.
    destruct blks' as [|b' rest].
    { exfalso. eapply co_ne; [eapply translate_cfg_ok; exact Ht'|reflexivity]. }
    assert (Hprog_ub : unique_bindings (Efun fds main)) by (destruct Hprog as (_ & _ & _ & H & _); exact H).
    destruct (Hub' Hub) as [Hub1 Hxe'].
    assert (HxS : ~ occurs_free e x) by (intros H; destruct Hdis as [D]; apply (D x); split; auto).
    assert (Hfunx : is_fun fs x = false).
    { eapply bound_not_fun; [exact Hprog_ub|exact Hsub|exact Hnf|exact Hbx]. }
    destruct (Hsem env fresh sf st stk va Hok Henv) as (zi & Hzi & Hiok & Hiev & Hrun).
    destruct (tail_prepend ctx va B (IId (Raw (Zpos x))) (ins env) b' rest c st sf stk G st _ stk G
                Hiok Hiev Hrun) as (c1 & sf1' & Hag & E).
    eapply sim_result_eutt; [exact E|].
    set (sf1 := upd_local_sf sf (Maps.add (Raw (Zpos x)) (I64 zi) (stack_vars sf))) in *.
    assert (Hnf1 : Flatten_sem.agree_noflat sf1 sf1') by (eapply Flatten_sem.agree_except_noflat'; exact Hag).
    assert (Hbv_dead : forall z, bound_var e' z -> ~ occurs_free e z).
    { intros z Hz H. destruct Hdis as [D]. apply (D z). split; auto. }
    apply (IH (env_restrict e' env) chunk fresh (b' :: rest) f'' B va c1 st sf1' stk fp rs vs).
    - apply Hbo', Hbo.
    - eapply rt_trans; [apply rt_step; exact Hds|exact Hsub].
    - exact Hub1.
    - constructor. intros z [z' Hb Hf]. destruct (Pos.eq_dec z' x) as [->|Hne]; [contradiction|].
      destruct Hdis as [D]. apply (D z'). split; auto.
    - eapply env_ok_restrict; [exact Hok|lia].
    - rewrite <- (tr_restrict _ _ _ _ (occurs_free e) env fresh); [exact Ht'|exact Hok|exact Hbv_dead].
    - exact Hbl.
    - exact HI.
    - eapply LLVM_sim.tinfo_local_noflat; [|exact Hnf1].
      apply LLVM_sim.tinfo_local_write; [exact Htl|discriminate].
    - apply env_rel_restrict.
      eapply LLVM_sim.env_rel_noflat; [exact Hok| |exact Hnf1].
      eapply LLVM_sim.env_rel_bind; [exact Henv| | | |exact Hfunx|exact Hzi].
      + intros y Hy. destruct (Pos.eq_dec y x) as [->|Hne]; [left; reflexivity|right; apply Hfv; auto].
      + intros y Hy _. eapply (LLVM_sim.env_ok_not_pos cenv prim_of); [exact Hok|exact HxS|exact Hy|].
        intros ->. contradiction.
      + destruct (Hok x) as [_ H2]. apply H2, HxS.
    - exact Hroom.
  Qed.

  (* ---------------------------------------------------------------- *)
  (** *** [Eprim_val] (primitive integers only, by [body_ok]) *)

  Lemma sim_case_prim_val rho x p e' v :
    sim_stmt (M.set x (Vprim p) rho) e' v -> sim_stmt rho (Eprim_val x p e') v.
  Proof.
    intros IH. destruct p as [[] pv].
    2,3: intros ? ? ? ? ? ? ? ? ? ? ? ? ? ? Hbo; exfalso; inversion Hbo.
    apply (sim_prepend_bind _ e' x (fun _ => INSTR_Op (prim_val_exp (existT _ primInt pv))) rho (Vprim (existT _ primInt pv)) v).
    - intros env chunk fresh blks f' H. apply tr_prim_val. exact H.
    - constructor.
    - discriminate.
    - intros H. inversion H. assumption.
    - intros H. inversion H. auto.
    - apply Bound_Eprim_val1.
    - intros z Hz. apply Bound_Eprim_val2, Hz.
    - intros z Hz Hne. apply Free_Eprim_val; auto.
    - intros env fresh sf st stk va Hok Henv.
      set (z := Uint63.to_Z pv).
      assert (Hev : exp_eval st sf stk G None (cexp (prim_val_exp (existT _ primInt pv))) (I64 (2 * z + 1))).
      { unfold prim_val_exp. cbn [prim_val_Z projT1 projT2]. rewrite cexp_val_long, cexp_litZ.
        apply exp_eval_val_long, exp_eval_litZ. }
      exists (2 * z + 1). split.
      + intros st2 _. replace (2 * z + 1) with (Uint63.to_Z pv * 2 + 1) by (subst z; lia). constructor.
      + cbv zeta. rewrite cinstr_Op. split; [|split].
        * cbn [Flatten_sem.instr_ok]. split; [apply Flatten_sem.is_flat_pos|].
          unfold prim_val_exp. cbn [prim_val_Z projT1 projT2]. rewrite cexp_val_long, cexp_litZ.
          cbn. tauto.
        * exists (I64 (2 * z + 1)). exact Hev.
        * apply LLVM_instr_lemmas.instr_op. exact Hev.
    - exact IH.
  Qed.

  (* ---------------------------------------------------------------- *)
  (** *** [Eproj] *)

  Lemma sim_case_proj rho x t n y e' vs v' v :
    M.get y rho = Some (Vconstr t vs) -> nthN vs n = Some v' ->
    sim_stmt (M.set x v' rho) e' v -> sim_stmt rho (Eproj x t n y e') v.
  Proof.
    intros Hy Hn IH.
    apply (sim_prepend_bind _ e' x (fun env => load_field env y n) rho v' v).
    - intros env chunk fresh blks f' H. apply tr_proj. exact H.
    - constructor.
    - discriminate.
    - intros H. inversion H. assumption.
    - intros H. inversion H. auto.
    - apply Bound_Eproj1.
    - intros z Hz. apply Bound_Eproj2, Hz.
    - intros z Hz Hne. apply Free_Eproj2; auto.
    - intros env fresh sf st stk va Hok Henv.
      destruct (Henv y (Free_Eproj1 y x t n e')) as (v0 & Hv0 & Hc). rewrite Hy in Hv0. injection Hv0 as <-.
      destruct (is_fun fs y) eqn:Ef; [destruct Hc as (? & E); discriminate|].
      destruct Hc as (z & Hz & Hs).
      rewrite nthN_nth_error in Hn. set (i := N.to_nat n) in *.
      destruct (LLVM_sim.stable_repr_field cenv prim_of fds G tinfo st t vs z i v' Hs Hn) as (q & zi & Hq & Hr & Hzi).
      assert (Hz0 : 0 <= z < 2 ^ 64).
      { pose proof (Hs st (fun a _ _ => eq_refl)) as Hrep.
        inversion Hrep; subst; [destruct i; discriminate|apply ptr_to_int_range]. }
      pose proof (ptr_to_int_range q) as Hqr.
      assert (Hloc : exp_eval st sf stk G (Some (DTYPE_I 64 : dtyp)) (EXP_Ident (ID_Local (env y))) (I64 z))
        by (apply exp_eval_local; exact Hz).
      destruct (exp_eval_inttoptr' (Some (DTYPE_Pointer : dtyp)) Hloc) as (q0 & Hq0 & Hp0 & Hev0).
      rewrite Z.mod_small in Hq0 by exact Hz0.
      assert (Hrange : 0 <= z + 8 * Z.of_nat i < 2 ^ 64) by lia.
      destruct (@int_to_ptr_total (z + 8 * Z.of_nat i) (ptr_provenance q0) Hrange) as (q1 & Hq1 & Hi1 & Hp1).
      assert (Hoff : ptr_off q0 (8 * Z.of_nat i) q1) by (unfold ptr_off; rewrite Hq0; exact Hq1).
      assert (Hev1 : exp_eval st sf stk G (Some (DTYPE_Pointer : dtyp)) (cexp (gep_field (nvar env y) n)) (Ptr q1)).
      { rewrite cexp_gep_field, cexp_nvar. eapply exp_eval_gep_at; [lia|exact Hev0|exact Hoff]. }
      assert (Hr1 : reads_word st q1 zi).
      { eapply reads_word_wild; [exact Hr|lia|rewrite Hp1; exact Hp0]. }
      exists zi. split; [exact Hzi|]. cbv zeta. rewrite cinstr_load_field. split; [|split].
      + cbn [Flatten_sem.instr_ok]. split; [apply Flatten_sem.is_flat_pos|].
        rewrite cexp_gep_field, cexp_nvar. cbn. repeat split.
        eapply LLVM_sim.env_ok_not_flat. exact Hok.
      + exists (Ptr q1). exact Hev1.
      + eapply LLVM_instr_lemmas.instr_load_word; [exact Hev1|exact Hr1].
    - exact IH.
  Qed.

  (* ---------------------------------------------------------------- *)
  (** *** [Ecase] *)

  Lemma INV_room0 st fp rs vs : INV st fp rs vs -> room st tinfo (Z.of_N 0).
  Proof.
    intros (_ & (_ & _ & alloc & limit & Ha & Hl & _ & Hle & _) & _).
    exists alloc, limit. split; [exact Ha|]. split; [exact Hl|]. change (Z.of_N 0) with 0. lia.
  Qed.

  (** Jumping to the arm selected by the switch, and running it. *)
  Lemma case_arm_jump rho y arms t e' v (P : N -> bool) env fresh ab aedges f1 B va from dflt
        st sf stk fp rs vs :
    arm_loop_d (fun ae fr => tr env 0%N ae fr) (ord_of cenv) (arity_of cenv) arms fresh = (ab, aedges, f1) ->
    (forall b, In b ab -> exists c, RM.find (blk_id b) (CFG.ocfg_map B) = Some (LLVM_sim.flatB (cblock b) c)) ->
    findtag arms t = Some e' -> P (arity_of cenv t) = true ->
    (forall t', In t' (map fst arms) -> t' <> t -> P (arity_of cenv t') = true -> ord_of cenv t' <> ord_of cenv t) ->
    sim_stmt rho e' v ->
    body_ok cenv (Ecase y arms) -> subterm_or_eq (Ecase y arms) (Efun fds main) -> unique_bindings (Ecase y arms) ->
    Ensembles.Disjoint _ (bound_var (Ecase y arms)) (occurs_free (Ecase y arms)) ->
    LLVM_sim.env_ok (occurs_free (Ecase y arms)) env fresh ->
    INV st fp rs vs -> LLVM_sim.tinfo_local tinfo sf ->
    env_rel (occurs_free (Ecase y arms)) rho env sf st ->
    sim_result st stk fp rs vs v
      (RUN (denote_ocfg B va (from, LLVM_instr_lemmas.switch_dest (Z.of_N (ord_of cenv t)) dflt
                                        (map snd (filter (fun ae => P (fst ae)) aedges))))
           (st, ((sf, stk), G))).
  Proof.
    intros Ha Hab Hf HP Hd IH Hbo Hsub Hub Hdis Hok HI Htl Henv.
    assert (Hin_t := findtag_In _ _ _ Hf).
    assert (Htag : forall t', In t' (map fst arms) -> (ord_of cenv t' < 1024)%N).
    { intros t' Ht'. apply in_map_iff in Ht'. destruct Ht' as ([t'' e''] & <- & Hin).
      destruct (LLVM_sim.prog_case _ _ _ Hprog _ _ _ _ Hsub Hin) as (_ & Hlt & _). cbn [fst] in *. lia. }
    destruct (arm_loop_find _ _ _ _ env arms fresh ab aedges f1 t e' P dflt Ha Hf HP
                (Htag t (in_map fst _ _ Hin_t)) Htag Hd) as (fr0 & ablks & fr1 & Hle & Etr & Hne & Hsubl & Hsw).
    rewrite Hsw. destruct ablks as [|b0 rest0]; [contradiction|]. cbn [entry_id].
    destruct (Hab b0 (Hsubl b0 (or_introl eq_refl))) as (c0 & Hfind).
    pose proof (translate_cfg_ok _ _ _ _ e' env 0%N fr0 (b0 :: rest0) fr1 Etr) as Hcfg.
    assert (Hph : blk_phis (LLVM_sim.flatB (cblock b0) c0) = []).
    { rewrite LLVM_sim.flatB_phis. apply LLVM_instr_lemmas.cblock_phis_nil. eapply co_entry; [exact Hcfg|reflexivity]. }
    eapply sim_result_eutt.
    { rewrite (LLVM_sim.denote_ocfg_jump va B from (blk_id b0) _ Hfind Hph). reflexivity. }
    assert (Hbv : forall z, bound_var e' z -> ~ occurs_free (Ecase y arms) z).
    { intros z Hz H. destruct Hdis as [D]. apply (D z). split; [econstructor; eauto|exact H]. }
    assert (Hfv : forall z, occurs_free e' z -> occurs_free (Ecase y arms) z).
    { intros z Hz. eapply occurs_free_Ecase_In; eauto. }
    apply (IH (env_restrict e' env) 0%N fr0 (b0 :: rest0) fr1 B va c0 st sf stk fp rs vs).
    - inversion Hbo as [| |? ? HF| | | |]; subst. rewrite Forall_forall in HF. exact (proj2 (HF (t, e') Hin_t)).
    - eapply rt_trans; [apply rt_step; econstructor; exact Hin_t|exact Hsub].
    - eapply ub_case_arm; eauto.
    - constructor. intros z [z' Hb Hf']. apply (Hbv z' Hb). apply Hfv, Hf'.
    - eapply env_ok_restrict; [exact Hok|exact Hle].
    - rewrite <- (tr_restrict _ _ _ _ (occurs_free (Ecase y arms)) env fresh); [exact Etr|exact Hok|exact Hbv].
    - intros b Hb. apply Hab, Hsubl. right. exact Hb.
    - exact HI.
    - exact Htl.
    - apply env_rel_restrict. eapply LLVM_sim.env_rel_weaken; [exact Henv|exact Hfv].
    - eapply INV_room0; exact HI.
  Qed.

  Lemma noflat_trans sf1 sf2 sf3 :
    Flatten_sem.agree_noflat sf1 sf2 -> Flatten_sem.agree_noflat sf2 sf3 -> Flatten_sem.agree_noflat sf1 sf3.
  Proof. intros H1 H2 r Hr. rewrite H2 by exact Hr. apply H1, Hr. Qed.

  (** A code-free block: its terminator runs. *)
  Lemma tail_term_step va B (b : LLVMAst.block dtyp) c st sf stk tid tm tmd r :
    blk_code b = [] -> blk_term b = (tid, tm, tmd) ->
    Flatten_sem.term_ok tm -> Flatten_sem.term_evals st sf stk G tm ->
    LLVM_instr_lemmas.runs ctx (denote_terminator (tid, tm, tmd)) (st, ((sf, stk), G)) (st, ((sf, stk), G)) r ->
    exists sf', Flatten_sem.agree_noflat sf sf' /\
      RUN (LLVM_sim.tail_of va B (LLVM_sim.flatB b c)) (st, ((sf, stk), G))
      ≈ RUN (LLVM_sim.continue va B (blk_id b) r) (st, ((sf', stk), G)).
  Proof.
    intros Hc Ht Hok Hev Hr.
    destruct (Flatten_sem.flat_tail_term ctx va c c tid tm tmd (LLVM_sim.continue va B (blk_id b))
                st sf sf stk G st sf stk G r Hok Hev (Pos.le_refl _) (Flatten_sem.agree_except_refl _ _ _) Hr)
      as (_ & sf' & Hag & E).
    exists sf'. split; [eapply Flatten_sem.agree_except_noflat'; exact Hag|].
    rewrite tail_flat, Hc, Ht. exact E.
  Qed.

  (** A block with one non-call instruction, then its terminator. *)
  Lemma tail_instr_term_step va B (b : LLVMAst.block dtyp) c st sf stk i sf1 tid tm tmd r :
    blk_code b = [i] -> blk_term b = (tid, tm, tmd) ->
    Flatten_sem.instr_ok i -> Flatten_sem.instr_evals st sf stk G i ->
    LLVM_instr_lemmas.runs ctx (denote_instr i va) (st, ((sf, stk), G)) (st, ((sf1, stk), G)) tt ->
    Flatten_sem.term_ok tm -> Flatten_sem.term_evals st sf1 stk G tm ->
    LLVM_instr_lemmas.runs ctx (denote_terminator (tid, tm, tmd)) (st, ((sf1, stk), G)) (st, ((sf1, stk), G)) r ->
    exists sf', Flatten_sem.agree_noflat sf1 sf' /\
      RUN (LLVM_sim.tail_of va B (LLVM_sim.flatB b c)) (st, ((sf, stk), G))
      ≈ RUN (LLVM_sim.continue va B (blk_id b) r) (st, ((sf', stk), G)).
  Proof.
    intros Hc Ht Hiok Hiev Hir Hok Hev Hr.
    destruct (Flatten_sem.flat_tail_instr ctx va c c i [] (tid, tm, tmd) (LLVM_sim.continue va B (blk_id b))
                st sf sf stk G st sf1 stk G Hiok Hiev (Pos.le_refl _) (Flatten_sem.agree_except_refl _ _ _) Hir)
      as (Hle & sf1' & Hag1 & E1).
    destruct (Flatten_sem.flat_tail_term ctx va c _ tid tm tmd (LLVM_sim.continue va B (blk_id b))
                st sf1 sf1' stk G st sf1 stk G r Hok Hev Hle Hag1 Hr) as (_ & sf' & Hag & E).
    exists sf'. split; [eapply Flatten_sem.agree_except_noflat'; exact Hag|].
    rewrite tail_flat, Hc, Ht, E1. exact E.
  Qed.

  (** The [Ecase] case.  The boxed branch uses that the representation of a
      boxed constructor is an even word (the emitted dispatch tests the low
      bit): [LLVM_sim.stable_repr_even], from the alignment premise of
      [Repr_boxed]. *)
  Lemma sim_case_case rho y arms t vs e' v :
    M.get y rho = Some (Vconstr t vs) -> findtag arms t = Some e' -> caseConsistent cenv arms t ->
    sim_stmt rho e' v -> sim_stmt rho (Ecase y arms) v.
  Proof.
    intros Hy Hf Hcc IH env chunk fresh blks f' B va c st sf stk fp rs vs0
      Hbo Hsub Hub Hdis Hok Htr Hbl HI Htl Henv Hroom.
    destruct (arm_loop_d (fun ae fr => tr env 0%N ae fr) (ord_of cenv) (arity_of cenv) arms fresh)
      as [[ab aedges] f1] eqn:Ha.
    rewrite (tr_case _ _ _ _ env chunk y arms fresh ab aedges f1 Ha) in Htr. injection Htr as <- <-.
    set (dflt := entry_id ab (Pos.succ (Pos.succ f1))).
    assert (Hab : forall b, In b ab -> exists c, RM.find (blk_id b) (CFG.ocfg_map B) = Some (LLVM_sim.flatB (cblock b) c))
      by (intros b Hb; apply Hbl; right; right; exact Hb).
    destruct (Hbl (case_unboxed_blk env y f1 dflt aedges) (or_introl eq_refl)) as (cu & Hfu).
    destruct (Hbl (case_boxed_blk env y f1 dflt aedges) (or_intror (or_introl eq_refl))) as (cb & Hfb).
    change (blk_id (case_unboxed_blk env y f1 dflt aedges)) with (Anon (Zpos (Pos.succ f1))) in Hfu.
    change (blk_id (case_boxed_blk env y f1 dflt aedges)) with (Anon (Zpos f1)) in Hfb.
    destruct (Henv y (Free_Ecase1 y arms)) as (v0 & Hv0 & Hc). rewrite Hy in Hv0. injection Hv0 as <-.
    destruct (is_fun fs y) eqn:Ef; [destruct Hc as (? & E); discriminate|].
    destruct Hc as (z & Hz & Hs).
    assert (Hcok : cenv_ok cenv) by (destruct Hprog as (_ & _ & _ & _ & H); exact H).
    assert (Hdist := case_ords_distinct cenv arms t Hcok Hcc).
    assert (Htag : (ord_of cenv t < 1024)%N).
    { destruct (LLVM_sim.prog_case _ _ _ Hprog _ _ _ _ Hsub (findtag_In _ _ _ Hf)) as (_ & Hlt & _). lia. }
    assert (Hyf : Flatten_sem.is_flat (env y) = false) by (eapply LLVM_sim.env_ok_not_flat; exact Hok).
    (* the test block *)
    assert (Hloc : exp_eval st sf stk G (Some (DTYPE_I 64 : dtyp)) (EXP_Ident (ID_Local (env y))) (I64 z))
      by (apply exp_eval_local; exact Hz).
    pose proof (exp_eval_is_block (Some (DTYPE_I 1 : dtyp)) Hloc) as Hev.
    set (bt := case_test_blk env y f1).
    assert (Hct : blk_code (cblock bt) = []) by (rewrite cblock_eq; reflexivity).
    assert (Htt : blk_term (cblock bt) =
      (IVoid 3%Z, TERM_Br (DTYPE_I 1 : dtyp, OP_ICmp false Eq i64 (OP_IBinop And i64 (EXP_Ident (ID_Local (env y))) (dlit 1)) (dlit 0))
                    (Anon (Zpos f1)) (Anon (Zpos (Pos.succ f1))), [])).
    { rewrite cblock_eq. cbn [blk_term bt case_test_blk]. rewrite cterm_Br. unfold ctexp. cbn [fst snd].
      rewrite cty_i1, cexp_is_block, cexp_nvar. reflexivity. }
    destruct (tail_term_step va B (cblock bt) c st sf stk _ _ _ _ Hct Htt
                ltac:(cbn; repeat split; exact Hyf) (ex_intro _ _ Hev)
                (LLVM_instr_lemmas.term_br ctx _ _ _ _ _ _ st sf stk G Hev)) as (sfa & Hnfa & Ea).
    cbn [LLVM_sim.hd_blk]. fold bt. eapply sim_result_eutt; [exact Ea|]. cbn [LLVM_sim.continue].
    assert (Hloca : exp_eval st sfa stk G (Some (DTYPE_I 64 : dtyp)) (EXP_Ident (ID_Local (env y))) (I64 z))
      by (apply exp_eval_local; rewrite Hnfa by exact Hyf; exact Hz).
    assert (Henva : env_rel (occurs_free (Ecase y arms)) rho env sfa st)
      by (eapply LLVM_sim.env_rel_noflat; [exact Hok|exact Henv|exact Hnfa]).
    assert (Htla : LLVM_sim.tinfo_local tinfo sfa) by (eapply LLVM_sim.tinfo_local_noflat; [exact Htl|exact Hnfa]).
    destruct vs as [|v1 vs1].
    - (* unboxed constructor *)
      assert (Hzu : z = Z.of_N (ord_of cenv t) * 2 + 1 /\ arity_of cenv t = 0%N).
      { pose proof (Hs st (fun a _ _ => eq_refl)) as Hrep. inversion Hrep; subst; auto; congruence. }
      destruct Hzu as [Ez Har]. subst z.
      replace ((Z.of_N (ord_of cenv t) * 2 + 1) mod 2 =? 0) with false.
      2:{ rewrite Z.add_comm, Z.mod_add by lia. reflexivity. }
      cbn [Datatypes.negb].
      eapply sim_result_eutt.
      { rewrite (LLVM_sim.denote_ocfg_jump va B _ _ _ Hfu)
          by (rewrite LLVM_sim.flatB_phis; apply LLVM_instr_lemmas.cblock_phis_nil; reflexivity).
        reflexivity. }
      set (bu := case_unboxed_blk env y f1 dflt aedges).
      set (brs := map snd (filter (fun ae => N.eqb (fst ae) 0) aedges)).
      assert (Hcu : blk_code (cblock bu) = []) by (rewrite cblock_eq; reflexivity).
      assert (Htu : blk_term (cblock bu) =
        (IVoid 4%Z, TERM_Switch (DTYPE_I 64 : dtyp, OP_IBinop (AShr false) i64 (EXP_Ident (ID_Local (env y))) (dlit 1))
                      dflt brs, [])).
      { rewrite cblock_eq. cbn [blk_term bu case_unboxed_blk]. rewrite cterm_Switch. unfold ctexp. cbn [fst snd].
        rewrite cty_val, cexp_long_val, cexp_nvar. reflexivity. }
      assert (Hrz : -2^63 <= Z.of_N (ord_of cenv t) * 2 + 1 < 2^63) by lia.
      assert (Hev2 := exp_eval_long_val_small (Some (DTYPE_I 64 : dtyp)) Hrz Hloca).
      replace ((Z.of_N (ord_of cenv t) * 2 + 1) / 2) with (Z.of_N (ord_of cenv t)) in Hev2.
      2:{ rewrite Z.div_add_l by lia. change (1 / 2) with 0. lia. }
      assert (HF : Forall LLVM_instr_lemmas.lit64 brs)
        by (apply (Forall_lit64_filter (fun a => N.eqb a 0)); eapply arm_loop_lits; exact Ha).
      destruct (tail_term_step va B (cblock bu) cu st sfa stk _ _ _ _ Hcu Htu
                  ltac:(cbn; repeat split; exact Hyf) (ex_intro _ _ Hev2)
                  (LLVM_instr_lemmas.term_switch ctx _ _ _ _ _ _ st sfa stk G HF Hev2)) as (sfb & Hnfb & Eb).
      eapply sim_result_eutt; [exact Eb|]. cbn [LLVM_sim.continue].
      eapply (case_arm_jump rho y arms t e' v (fun a => N.eqb a 0)); eauto.
      + rewrite Har. reflexivity.
      + intros t' Hin Hne HP' Eq. apply (proj1 (Hdist t' Hin Hne Eq) Har). apply N.eqb_eq. exact HP'.
      + eapply LLVM_sim.tinfo_local_noflat; [exact Htla|exact Hnfb].
      + eapply LLVM_sim.env_rel_noflat; [exact Hok|exact Henva|exact Hnfb].
    - (* boxed constructor *)
      assert (Hne : v1 :: vs1 <> []) by discriminate.
      rewrite (LLVM_sim.stable_repr_even cenv prim_of fds G tinfo st t (v1 :: vs1) z Hne Hs).
      cbn [Z.eqb Datatypes.negb].
      destruct (LLVM_sim.stable_repr_header cenv prim_of fds G tinfo st t (v1 :: vs1) z Hne Hs)
        as (Har & ph & Hph & Hhdr).
      set (hdr := Z.of_N (arity_of cenv t) * 1024 + Z.of_N (ord_of cenv t)) in *.
      eapply sim_result_eutt.
      { rewrite (LLVM_sim.denote_ocfg_jump va B _ _ _ Hfb)
          by (rewrite LLVM_sim.flatB_phis; apply LLVM_instr_lemmas.cblock_phis_nil; reflexivity).
        reflexivity. }
      set (bb := case_boxed_blk env y f1 dflt aedges).
      set (brs := map snd (filter (fun ae => negb (N.eqb (fst ae) 0)) aedges)).
      set (ld := OP_Conversion (CONV_Impure Inttoptr) i64
                   (OP_IBinop (Sub false false) i64 (EXP_Ident (ID_Local (env y))) (dlit 8)) dptr).
      set (ci := (IId (ntmp f1 1), INSTR_Load i64 (dptr, ld) [], @nil (metadata dtyp))).
      assert (Hcb : blk_code (cblock bb) = [ci]).
      { rewrite cblock_eq. cbn [blk_code bb case_boxed_blk]. rewrite ccode_cons, ccode_nil, cinstr_load_header.
        reflexivity. }
      assert (Htb : blk_term (cblock bb) =
        (IVoid 5%Z, TERM_Switch (DTYPE_I 64 : dtyp, OP_IBinop And i64 (EXP_Ident (ID_Local (ntmp f1 1))) (dlit 1023))
                      dflt brs, [])).
      { rewrite cblock_eq. cbn [blk_term bb case_boxed_blk]. rewrite cterm_Switch. unfold ctexp. cbn [fst snd].
        rewrite cty_val, cexp_IBinop, cty_val, cexp_Ident, cexp_lit. reflexivity. }
      pose proof (ptr_to_int_range ph) as Hphr.
      assert (Hsub8 : exp_eval st sfa stk G (Some (DTYPE_I 64 : dtyp))
                        (OP_IBinop (Sub false false) i64 (EXP_Ident (ID_Local (env y))) (dlit 8)) (I64 (z - 8)))
        by (apply (exp_eval_sub (Some (DTYPE_I 64 : dtyp)) Hloca (exp_eval_lit64 st sfa stk G 8))).
      destruct (exp_eval_inttoptr' (Some (DTYPE_Pointer : dtyp)) Hsub8) as (q0 & Hq0 & Hp0 & Hevp).
      rewrite Z.mod_small in Hq0 by lia.
      assert (Hrd : reads_word st q0 hdr) by (eapply reads_word_wild; [exact Hhdr|lia|exact Hp0]).
      set (sfl := upd_local_sf sfa (Maps.add (ntmp f1 1) (I64 hdr) (stack_vars sfa))).
      assert (Hrun := LLVM_instr_lemmas.instr_load_word ctx va (ntmp f1 1) ld q0 hdr st sfa stk G Hevp Hrd).
      assert (Hev3 : exp_eval st sfl stk G (Some (DTYPE_I 64 : dtyp))
                       (OP_IBinop And i64 (EXP_Ident (ID_Local (ntmp f1 1))) (dlit 1023)) (I64 (Z.of_N (ord_of cenv t)))).
      { replace (Z.of_N (ord_of cenv t)) with (hdr mod 1024).
        - apply exp_eval_and1023. apply exp_eval_local. apply LLVM_instr_lemmas.rfind_add_eq.
        - subst hdr. rewrite Z.add_comm, Z.mod_add by lia. apply Z.mod_small. lia. }
      assert (HF : Forall LLVM_instr_lemmas.lit64 brs)
        by (apply (Forall_lit64_filter (fun a => negb (N.eqb a 0))); eapply arm_loop_lits; exact Ha).
      destruct (tail_instr_term_step va B (cblock bb) cb st sfa stk ci sfl _ _ _ _ Hcb Htb
                  ltac:(cbn; repeat split; first [apply Flatten_sem.is_flat_ntmp|exact Hyf])
                  (ex_intro _ _ Hevp) Hrun
                  ltac:(cbn; repeat split; apply Flatten_sem.is_flat_ntmp) (ex_intro _ _ Hev3)
                  (LLVM_instr_lemmas.term_switch ctx _ _ _ _ _ _ st sfl stk G HF Hev3)) as (sfb & Hnfb & Eb).
      eapply sim_result_eutt; [exact Eb|]. cbn [LLVM_sim.continue].
      eapply (case_arm_jump rho y arms t e' v (fun a => negb (N.eqb a 0))); eauto.
      + rewrite Har. reflexivity.
      + intros t' Hin Hne' HP' Eq.
        assert (H := proj2 (Hdist t' Hin Hne' Eq) (proj1 (N.eqb_neq _ _) (proj1 (negb_true_iff _) HP'))).
        rewrite Har in H. discriminate.
      + eapply LLVM_sim.tinfo_local_noflat; [|exact Hnfb].
        apply LLVM_sim.tinfo_local_write; [exact Htla|discriminate].
      + eapply LLVM_sim.env_rel_noflat; [exact Hok| |exact Hnfb].
        apply LLVM_sim.env_rel_write; [exact Henva|].
        intros x _ _. eapply LLVM_sim.env_ok_not_ntmp; exact Hok.
  Qed.

End CasesRead.
