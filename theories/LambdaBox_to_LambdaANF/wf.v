(* Well-formedness predicates for source values and environments *)

(** Stdlib *)
From Stdlib Require Import Lists.List Arith Bool Lia.

(** MetaRocq *)
From MetaRocq.Erasure Require Import EAst EGlobalEnv EWellformed.
From MetaRocq.Common Require Import BasicAst Kernames.

(** CertiRocq *)
From CertiRocq.Common Require Import AstCommon.
From CertiRocq.LambdaBox_to_LambdaANF Require Import fuel_sem common.

Import ListNotations.


Section WF.

  Context {efl : EEnvFlags}.
  Context (Σ : global_context).

  (** A term is well-formed in an environment of size [n] *)
  Definition well_formed_in_env (t : EAst.term) (rho : env) :=
    wellformed Σ (List.length rho) t = true.

  (** Well-formedness of source values.
      Closure bodies must be well-formed w.r.t. their captured environment.
      Fix bodies must be lambdas, well-formed in an environment extended
      by all mutual functions. *)
  Inductive well_formed_val : value -> Prop :=
  | Wf_Con :
      forall dc vs,
        Forall well_formed_val vs ->
        well_formed_val (Con_v dc vs)
  | Wf_Clos :
      forall vs na body,
        Forall well_formed_val vs ->
        wellformed Σ (S (List.length vs)) body = true ->
        well_formed_val (Clos_v vs na body)
  | Wf_ClosFix :
      forall vs mfix idx,
        Forall well_formed_val vs ->
        (idx < List.length mfix)%nat ->
        Forall (fun d =>
                  EAst.isLambda d.(EAst.dbody) = true /\
                  wellformed Σ (List.length mfix + List.length vs) d.(EAst.dbody) = true)
               mfix ->
        well_formed_val (ClosFix_v vs mfix idx).

  Definition well_formed_env (rho : env) : Prop :=
    Forall well_formed_val rho.


  (** ** Wellformed decomposition lemmas *)

  Lemma wellformed_tRel k n :
    wellformed Σ k (EAst.tRel n) = true ->
    (n < k)%nat.
  Proof.
    unfold wellformed. simpl. intro H.
    apply andb_true_iff in H as [_ H].
    apply Nat.ltb_lt in H. exact H.
  Qed.

  Lemma wellformed_tLambda n na body :
    wellformed Σ n (EAst.tLambda na body) = true ->
    wellformed Σ (S n) body = true.
  Proof.
    unfold wellformed. simpl. fold (@wellformed efl).
    intro H. apply andb_true_iff in H. exact (proj2 H).
  Qed.

  Lemma wellformed_tApp n e1 e2 :
    wellformed Σ n (EAst.tApp e1 e2) = true ->
    wellformed Σ n e1 = true /\ wellformed Σ n e2 = true.
  Proof.
    unfold wellformed. simpl. fold (@wellformed efl).
    intro H. apply andb_true_iff in H as [H1 H2].
    apply andb_true_iff in H1 as [_ H1].
    split; assumption.
  Qed.

  Lemma wellformed_tLetIn n na b t' :
    wellformed Σ n (EAst.tLetIn na b t') = true ->
    wellformed Σ n b = true /\ wellformed Σ (S n) t' = true.
  Proof.
    unfold wellformed. simpl. fold (@wellformed efl).
    intro H. apply andb_true_iff in H as [H1 H2].
    apply andb_true_iff in H1 as [_ H1].
    split; assumption.
  Qed.

  Lemma wellformed_tFix n mfix idx :
    wellformed Σ n (EAst.tFix mfix idx) = true ->
    (idx < List.length mfix)%nat /\
    Forall (fun d => EAst.isLambda d.(EAst.dbody) = true /\
                     wellformed Σ (List.length mfix + n) d.(EAst.dbody) = true) mfix.
  Proof.
    unfold wellformed. simpl. fold (@wellformed efl).
    intro H.
    apply andb_true_iff in H as [H1 H2].
    apply andb_true_iff in H1 as [_ Hlam].
    (* H2 = wf_fix_gen ... *)
    unfold wf_fix_gen in H2.
    apply andb_true_iff in H2 as [Hidx Hbodies].
    apply Nat.ltb_lt in Hidx.
    split; [exact Hidx |].
    apply Forall_forall. intros d Hd.
    split.
    - rewrite forallb_forall in Hlam. exact (Hlam d Hd).
    - rewrite forallb_forall in Hbodies. exact (Hbodies d Hd).
  Qed.

  Lemma wellformed_tCase_mch n ind npars mch brs :
    wellformed Σ n (EAst.tCase (ind, npars) mch brs) = true ->
    wellformed Σ n mch = true.
  Proof.
    unfold wellformed. simpl. fold (@wellformed efl).
    intro H. apply andb_true_iff in H as [_ H].
    apply andb_true_iff in H as [H _].
    apply andb_true_iff in H as [_ H]. exact H.
  Qed.

  Lemma wellformed_tProj n p c :
    wellformed Σ n (EAst.tProj p c) = true ->
    wellformed Σ n c = true.
  Proof.
    unfold wellformed. simpl. fold (@wellformed efl).
    intro H. apply andb_true_iff in H as [_ H2]. exact H2.
  Qed.

  Lemma wellformed_tConstruct n ind c args :
    wellformed Σ n (EAst.tConstruct ind c args) = true ->
    Forall (fun e => wellformed Σ n e = true) args.
  Proof.
    unfold wellformed. simpl. fold (@wellformed efl).
    intro H. apply List.Forall_forall. intros e He.
    destruct cstr_as_blocks.
    - apply andb_true_iff in H as [_ Hwf_args].
      apply andb_true_iff in Hwf_args as [_ Hwf_args].
      rewrite forallb_forall in Hwf_args. exact (Hwf_args e He).
    - apply andb_true_iff in H as [_ Hnil].
      destruct args; [inv He | simpl in Hnil; discriminate].
  Qed.

  Lemma find_branch_wellformed n ind npars mch brs c nargs body :
    wellformed Σ n (EAst.tCase (ind, npars) mch brs) = true ->
    find_branch ind c nargs brs = Some body ->
    wellformed Σ (n + nargs) body = true.
  Proof.
    intros Hwf Hfind.
    simpl in Hwf. apply andb_true_iff in Hwf as [_ Hwf].
    apply andb_true_iff in Hwf as [_ Hwf_brs].
    revert c Hfind. induction brs as [| [names e_br] brs' IH]; intros c Hfind.
    - discriminate.
    - simpl in Hfind. simpl in Hwf_brs.
      apply andb_true_iff in Hwf_brs as [Hwf_hd Hwf_tl].
      destruct (Nat.eqb c 0) eqn:Hc.
      + destruct (Nat.eqb (Datatypes.length names) nargs) eqn:Hlen;
          [| discriminate].
        apply Nat.eqb_eq in Hlen. subst nargs.
        inversion Hfind. subst.
        replace (n + Datatypes.length names) with (Datatypes.length names + n) by lia.
        exact Hwf_hd.
      + exact (IH Hwf_tl _ Hfind).
  Qed.


  (** ** make_rec_env helpers *)

  Lemma make_rec_env_length mfix rho :
    Datatypes.length (make_rec_env mfix rho) =
    (Datatypes.length mfix + Datatypes.length rho)%nat.
  Proof.
    unfold make_rec_env.
    generalize (Datatypes.length mfix) as n.
    induction n as [| n' IH]; simpl; lia.
  Qed.

  Lemma well_formed_env_make_rec_env mfix rho :
    Forall well_formed_val rho ->
    Forall (fun d =>
              EAst.isLambda d.(EAst.dbody) = true /\
              wellformed Σ (Datatypes.length mfix + Datatypes.length rho) d.(EAst.dbody) = true)
           mfix ->
    well_formed_env (make_rec_env mfix rho).
  Proof.
    intros Hwf_rho Hwf_mfix.
    unfold well_formed_env, make_rec_env.
    set (n := Datatypes.length mfix).
    assert (Hn : (n <= Datatypes.length mfix)%nat) by lia.
    clearbody n. revert Hn.
    induction n as [| n' IH]; intros Hn.
    - simpl. exact Hwf_rho.
    - simpl. constructor.
      + apply Wf_ClosFix.
        * exact Hwf_rho.
        * lia.
        * exact Hwf_mfix.
      + apply IH. lia.
  Qed.

End WF.


(** ** Evaluation preserves well-formedness *)

Section WF_EVAL.

  Context {efl : EEnvFlags}.
  Context {trace : Type}
          {Hf : @LambdaBox_resource nat}
          {Ht : @LambdaBox_resource trace}.
  Context (Σ : EAst.global_context).
  Context (box_dc : dcon).

  Hypothesis globals_wellformed :
    forall k decl body,
      declared_constant Σ k decl ->
      decl.(EAst.cst_body) = Some body ->
      wellformed Σ 0 body = true.

  Lemma eval_preserves_wf rho e v f t :
    well_formed_env Σ rho ->
    wellformed Σ (List.length rho) e = true ->
    eval_env_fuel Σ box_dc rho e (Val v) f t ->
    well_formed_val Σ v.
  Proof.
    intros Hwf_env Hwf_e Heval.
    set (Pwf := fun (rho : env) (e : EAst.term) (r : result) (f : nat) (t : trace) =>
      well_formed_env Σ rho ->
      wellformed Σ (List.length rho) e = true ->
      match r with Val v => well_formed_val Σ v | OOT => True end).
    set (Pmany := fun (rho : env) (es : list EAst.term) (vs : list value)
                      (fs : nat) (ts : trace) =>
      well_formed_env Σ rho ->
      Forall (fun e => wellformed Σ (List.length rho) e = true) es ->
      Forall (well_formed_val Σ) vs).
    enough (Haux : Pwf rho e (Val v) f t) by exact (Haux Hwf_env Hwf_e).
    apply (eval_env_fuel_ind' Σ box_dc Pwf Pmany Pwf); try exact Heval;
    unfold Pwf, Pmany; try solve [intros; exact I].
    (* eval_App_step: e1 → Clos_v *)
    - intros e1 e2 body v2 r na rho0 rho' f1 f2 f3 t1 t2 t3
             _ IH1 _ IH2 _ IH3 Hwfe Hwft.
      destruct r; [| exact I].
      apply wellformed_tApp in Hwft as [Hwf1 Hwf2].
      specialize (IH1 Hwfe Hwf1). inversion IH1 as [| ? ? ? Hwf_rho' Hwf_body |]. subst.
      specialize (IH2 Hwfe Hwf2).
      apply IH3.
      + constructor; assumption.
      + simpl. exact Hwf_body.
    (* eval_FixApp_step: e1 → ClosFix_v *)
    - intros e1 e2 body rho0 rho' rho'' idx na mfix v2 r
             f1 f2 f3 t1 t2 t3
             _ IH1 Hfb Hmre _ IH2 _ IH3 Hwfe Hwft.
      destruct r; [| exact I].
      apply wellformed_tApp in Hwft as [Hwf1 Hwf2].
      specialize (IH1 Hwfe Hwf1).
      inversion IH1 as [| | ? ? ? Hwf_rho' Hidx Hwf_mfix]. subst.
      specialize (IH2 Hwfe Hwf2).
      unfold fix_body in Hfb.
      destruct (nth_error mfix idx) as [d |] eqn:Hd; [| discriminate].
      injection Hfb as Hbody_eq.
      assert (Hwf_d := proj1 (Forall_forall _ _) Hwf_mfix d (nth_error_In _ _ Hd)).
      destruct Hwf_d as [Hlam_d Hwf_dbody].
      apply IH3.
      + constructor; [assumption |].
        apply well_formed_env_make_rec_env; assumption.
      + simpl. rewrite make_rec_env_length.
        rewrite Hbody_eq in Hwf_dbody.
        now apply wellformed_tLambda in Hwf_dbody.
    (* eval_LetIn_step *)
    - intros na b t0 v1' r rho0 f1 f2 t1 t2 _ IH1 _ IH2 Hwfe Hwft.
      destruct r; [| exact I].
      apply wellformed_tLetIn in Hwft as [Hwfb Hwft0].
      specialize (IH1 Hwfe Hwfb).
      apply IH2.
      + constructor; assumption.
      + simpl. exact Hwft0.
    (* eval_Construct_step *)
    - intros ind c args vs dc rho0 fs ts Hdc _ IHmany Hwfe Hwft.
      apply wellformed_tConstruct in Hwft.
      constructor. exact (IHmany Hwfe Hwft).
    (* eval_Case_step *)
    - intros ind npars mch brs rho0 dc vs body c r f1 f2 t1 t2
             _ IH1 Hdc Hfind _ IH2 Hwfe Hwft.
      destruct r; [| exact I].
      pose proof (wellformed_tCase_mch Σ _ _ _ _ _ Hwft) as Hwf_mch.
      specialize (IH1 Hwfe Hwf_mch). inversion IH1 as [? ? Hwf_vs | |]. subst.
      pose proof (find_branch_wellformed Σ _ _ _ _ _ _ _ _ Hwft Hfind) as Hwf_body.
      apply IH2.
      + unfold well_formed_env. apply Forall_app. split.
        * apply Forall_rev. exact Hwf_vs.
        * exact Hwfe.
      + rewrite length_app, length_rev. rewrite Nat.add_comm.
        exact Hwf_body.
    (* eval_Proj_step *)
    - intros p c rho0 vs v0 f1 t1 _ IH Hnth Hwfe Hwft.
      apply (wellformed_tProj Σ) in Hwft.
      specialize (IH Hwfe Hwft). inversion IH as [? ? Hwf_vs | |]. subst.
      eapply Forall_forall in Hwf_vs; [exact Hwf_vs |].
      eapply nth_error_In. exact Hnth.
    (* eval_Const_step *)
    - intros k body v0 decl rho0 t0 Hdecl Hbody _ IH Hwfe Hwft.
      apply IH.
      + constructor.
      + exact (globals_wellformed _ _ _ Hdecl Hbody).
    (* eval_many_nil *)
    - intros rho0 _ _. constructor.
    (* eval_many_cons *)
    - intros rho0 e0 es v0 vs f1 fs t1 ts _ IH_e _ IH_es Hwfe Hwft.
      inversion Hwft as [| ? ? Hwf_hd Hwf_tl]. subst.
      constructor.
      + exact (IH_e Hwfe Hwf_hd).
      + exact (IH_es Hwfe Hwf_tl).
    (* eval_Rel_fuel *)
    - intros n rho0 v0 Hnth Hwfe Hwft.
      apply wellformed_tRel in Hwft.
      unfold well_formed_env in Hwfe.
      eapply Forall_forall in Hwfe; [exact Hwfe |].
      eapply nth_error_In. exact Hnth.
    (* eval_Lam_fuel *)
    - intros body rho0 na Hwfe Hwft.
      apply wellformed_tLambda in Hwft.
      apply Wf_Clos; [exact Hwfe | exact Hwft].
    (* eval_Fix_fuel *)
    - intros mfix idx rho0 Hwfe Hwft.
      apply wellformed_tFix in Hwft as [Hidx Hwf_mfix].
      apply Wf_ClosFix; assumption.
    (* eval_Box_fuel *)
    - intros rho0 _ _. constructor. constructor.
    (* eval_step *)
    - intros rho0 e0 r f0 t0 _ IH. exact IH.
  Qed.

End WF_EVAL.
