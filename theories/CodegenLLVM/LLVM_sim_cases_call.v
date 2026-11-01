(** * The call cases of [LLVM_sim.sim_exp]: [Efun], [Eapp], [Eletapp].

    See [LLVM_sim.v] for the simulation statement ([sim_stmt]); this file
    re-declares the context of its Section [Simulation] and proves the cases
    as implications between [sim_stmt]-like instances.

    - [sim_case_fun] (and [sim_case_fun_fr]): vacuous, [body_ok] excludes
      [Efun].
    - [sim_case_app_fr]: the tail call [Eapp].
    - [sim_case_letapp_fr]: the non-tail call [Eletapp] (safepoint set-up
      [la_pre_run], call [callee_run], reload and unlink [INV_unlink],
      [la_spec_holds]; the glue with the continuation is
      [sim_case_letapp_of_la_spec]).
    - [sim_case_app], [sim_case_letapp]: the same in [sim_stmt] form, with
      the premises of [BStep_app] / [BStep_letapp], for the assembly of
      [sim_exp].

    The call cases are proved for [sim_stmt_fr], which differs from
    [LLVM_sim.sim_stmt] only in its environment premise: [env_ok2] is weaker
    than [LLVM_sim.env_ok] (which is not preserved by safepoints).  The two
    are interchangeable: [sim_stmt_fr_weaken : sim_stmt_fr -> sim_stmt] and
    [sim_stmt_fr_of_sim_stmt : sim_stmt -> sim_stmt_fr] (by restricting the
    SSA environment to the live variables).  The frame condition needed to
    compose activations is [LLVM_sim.keeps_stack], part of
    [LLVM_sim.sim_result]. *)

From Stdlib Require Import ZArith NArith List Lia String Program Morphisms Classical_Prop.
From ITree Require Import ITree Eq.Eqit Interp.InterpFacts Interp.RecursionFacts.
From ExtLib Require Import Structures.Monads.

From CertiRocq.LambdaANF Require Import term term_util eval identifiers map_util Ensembles_util.
From CertiRocq.Common Require Import AstCommon.
From CertiRocq.CodegenLLVM Require Import LambdaANF_to_LLVM Flatten
     LambdaANF_to_LLVM_statement LLVM_interp_lemmas LLVM_call_lemmas LLVM_convert
     LLVM_exp_lemmas LLVM_mem_lemmas LLVM_emit_syntax LLVM_emit_facts LLVM_instr_lemmas.
From CertiRocq.CodegenLLVM Require Flatten_sem LLVM_sim LLVM_sim_cases_read.
From Vellvm Require Syntax.ScopeTheory.
From Vellvm Require Import Semantics.Operations.Gep Semantics.EOU Utils.IntMaps Implementations.IPtrFinite.

From Vellvm Require Import
  Utils Syntax Params
  Interfaces.Memory Implementations.Memory
  Semantics.DynamicValues Semantics.MemoryBytes Semantics.LLVMEvents Semantics.Denotation
  Semantics.InterpretationStack Semantics.TopLevel Handlers.

Import ListNotations.
Import MonadNotation.
Open Scope monad_scope.
Open Scope Z_scope.

Unset Implicit Arguments.
Set Bullet Behavior "Strict Subproofs".

Section CallCases.

  Variable cenv : ctor_env.
  Variable pfs : prims.
  Variable prim_of : positive -> option (string * bool).
  Variable fds : fundefs.
  Variable heap_inv : state -> ptr -> Prop.
  Variable gc : list dvalue -> MCFGtop (exc + dvalue).

  Notation go := (ord_of cenv).
  Notation ga := (arity_of cenv).
  Notation fs := (fun_ids fds).
  Notation tr := (translate_cfg go ga prim_of fs).

  Variable G : global_env.
  Variable ctx : CallE ~> itree (CallE +' MCFGEtop).
  Variable tinfo : ptr.

  Notation INV := (LLVM_sim.INV cenv fds heap_inv G tinfo).
  Notation stable_repr := (LLVM_sim.stable_repr cenv fds G tinfo).
  Notation env_rel := (LLVM_sim.env_rel cenv fds G tinfo).
  Notation sim_result := (LLVM_sim.sim_result cenv fds heap_inv G tinfo).
  Notation fun_def := (LLVM_sim.fun_def cenv prim_of fds).
  Notation slot_bytes := LLVM_sim.slot_bytes.
  Notation alloc_nonheap := LLVM_sim.alloc_nonheap.
  Notation in_frames := LLVM_sim.in_frames.
  Notation mem_ok := LLVM_sim.mem_ok.

  Hypothesis Hmut : forall st st2 alloc alloc2 limit,
       heap_inv st tinfo -> tinfo_ok st tinfo ->
       heap_agree_except st st2 (mutator_writes st tinfo) ->
       field st tinfo off_alloc alloc -> field st tinfo off_limit limit ->
       field st2 tinfo off_alloc alloc2 ->
       (ptr_to_int alloc <= ptr_to_int alloc2 <= ptr_to_int limit)%Z ->
       (ptr_to_int alloc2 mod 8 = 0)%Z ->
       heap_inv st2 tinfo.
  Hypothesis Hgc : forall (st : state) ls fp rs vs nalloc,
       heap_inv st tinfo -> tinfo_ok st tinfo -> mem_ok st -> LLVM_sim.nursery_tinfo_disjoint st tinfo ->
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
           heap_inv st' tinfo /\ tinfo_ok st' tinfo /\ mem_ok st' /\ LLVM_sim.nursery_tinfo_disjoint st' tinfo /\
           field st' tinfo off_fp fp /\
           shadow_stack st' fp rs /\
           roots_ok cenv fds G st' tinfo rs vs /\
           room st' tinfo nalloc /\
           (forall a, ~ in_heap st a -> ~ slot_bytes rs a ->
                      IntMaps.lookup a (mem_of st') = IntMaps.lookup a (mem_of st)) /\
           (forall a, in_heap st' a -> in_heap st a \/ IntMaps.lookup a (mem_of st) = None) /\
           (forall a, slot_bytes rs a -> aid_at st' a = aid_at st a).
  Hypothesis Htinfo_range : ptr_to_int tinfo + 8232 < 2^64.
  Hypothesis ctx_fun : forall f ft xs e fp,
    fun_in_fundefs fds (f, ft, xs, e) ->
    RM.find (Anon (Zpos f)) G = Some (Ptr fp) ->
    forall dt p args, ptr_to_int p = ptr_to_int fp ->
      ctx _ (Call dt (Ptr p) args) ≈ denote_function (fun_def f xs e) args.
  Hypothesis ctx_gc : forall gp,
    RM.find (Name "garbage_collect") G = Some (Ptr gp) ->
    forall dt p args, ptr_to_int p = ptr_to_int gp ->
      ctx _ (Call dt (Ptr p) args) ≈ lift_top (gc args).
  Hypothesis G_funs : forall f, In f fs -> exists fp, RM.find (Anon (Zpos f)) G = Some (Ptr fp).
  Hypothesis G_gc : exists gp, RM.find (Name "garbage_collect") G = Some (Ptr gp).

  Variable main : term.exp.
  Hypothesis Hprog : llvm_restricted cenv fds main.

  Notation sim_stmt := (LLVM_sim.sim_stmt cenv prim_of fds heap_inv G ctx tinfo main).

  (* ================================================================ *)
  (** ** [Efun]: vacuous, nested [Efun] is excluded by [body_ok] *)

  Lemma body_ok_Efun fl e : body_ok cenv (Efun fl e) -> False.
  Proof. intros H. inversion H. Qed.

  Lemma sim_case_fun rho fl e v :
    sim_stmt (def_funs fl fl rho rho) e v -> sim_stmt rho (Efun fl e) v.
  Proof.
    intros _ env chunk fresh blks f' B va c st sf stk fp rs vs Hok.
    exfalso. exact (body_ok_Efun _ _ Hok).
  Qed.


  (* ================================================================ *)
  (** ** [sim_stmt_fr]: [sim_stmt] with a weaker environment premise

      The frame condition of a function activation is [LLVM_sim.keeps_stack]
      (part of [LLVM_sim.sim_result]): the caller's stack memory other than
      the root slots is left alone, stays allocated, does not become heap,
      and keeps its allocation ids.  It is needed to recover the caller's
      shadow-stack frames after a call, and to re-read the root slots
      through the [alloca]'d root array.  [sim_result_fr] is just
      [LLVM_sim.sim_result]. *)
  Notation keeps_stack := LLVM_sim.keeps_stack.
  Notation sim_result_fr := sim_result (only parsing).

  (** [env_ok2]: [LLVM_sim.env_ok]'s clause for dead variables (they
      are under their ANF name) is not preserved by safepoints: after
      [Eletapp x f ft ys e'], an argument [y] of the call that a previous
      safepoint had renamed to an [ssname] and that is dead in [e'] keeps
      its [ssname] in the continuation's environment.  [env_ok2] only asks
      that the variables bound in [e] are under their ANF name (which holds
      for the emitter's environments by unique bindings), and that every
      variable is under its ANF name or an [ssname] with an older seed.
      [env_ok] implies [env_ok2] under [sim_stmt]'s premises
      ([env_ok_env_ok2]). *)
  Definition env_ok2 (e : term.exp) (env : nenv) (fresh : positive) : Prop :=
    forall y, (bound_var e y -> env y = Raw (Zpos y)) /\
              (env y = Raw (Zpos y) \/ exists s k, (s < fresh)%positive /\ env y = ssname s k).

  Lemma env_ok_env_ok2 e env fresh :
    Ensembles.Disjoint _ (bound_var e) (occurs_free e) ->
    LLVM_sim.env_ok (occurs_free e) env fresh -> env_ok2 e env fresh.
  Proof.
    intros Hd H y. destruct (H y) as [H1 H2]. split.
    - intros Hb. apply H2. intros Hf. inversion Hd as [Hd']. apply (Hd' y). constructor; assumption.
    - destruct (classic (occurs_free e y)) as [Hy|Hy]; [apply H1, Hy|left; apply H2, Hy].
  Qed.

  Lemma env_ok2_not_flat e env fresh : env_ok2 e env fresh -> forall y, Flatten_sem.is_flat (env y) = false.
  Proof.
    intros H y. destruct (H y) as [_ [E|(s & k & _ & E)]]; rewrite E;
      [apply Flatten_sem.is_flat_pos|apply Flatten_sem.is_flat_ssname].
  Qed.

  Definition sim_stmt_fr (rho : eval.env) (e : term.exp) (v : term.val) : Prop :=
    forall env chunk fresh blks f' (B : list (LLVMAst.block dtyp)) va c st sf stk fp rs vs,
      body_ok cenv e ->
      subterm_or_eq e (Efun fds main) ->
      unique_bindings e ->
      Ensembles.Disjoint _ (bound_var e) (occurs_free e) ->
      env_ok2 e env fresh ->
      tr env chunk e fresh = (blks, f') ->
      LLVM_sim.blocks_in B blks ->
      INV st fp rs vs ->
      LLVM_sim.tinfo_local tinfo sf ->
      env_rel (occurs_free e) rho env sf st ->
      room st tinfo (Z.of_N chunk) ->
      sim_result_fr st stk fp rs vs v
        (interp_mcfg (interp_mrec ctx (LLVM_sim.tail_of va B (LLVM_sim.flatB (cblock (LLVM_sim.hd_blk blks)) c)))
                     (st, ((sf, stk), G))).

  Lemma sim_result_fr_weaken st stk fp rs vs v t :
    sim_result_fr st stk fp rs vs v t -> sim_result st stk fp rs vs v t.
  Proof. exact (fun H => H). Qed.

  Lemma sim_stmt_fr_weaken rho e v : sim_stmt_fr rho e v -> sim_stmt rho e v.
  Proof.
    intros H env chunk fresh blks f' B va c st sf stk fp rs vs H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11.
    apply sim_result_fr_weaken. eapply H; eauto. apply env_ok_env_ok2; assumption.
  Qed.

  Lemma sim_case_fun_fr rho fl e v :
    sim_stmt_fr (def_funs fl fl rho rho) e v -> sim_stmt_fr rho (Efun fl e) v.
  Proof.
    intros _ env chunk fresh blks f' B va c st sf stk fp rs vs Hok.
    exfalso. exact (body_ok_Efun _ _ Hok).
  Qed.

  (* ================================================================ *)
  (** ** Transporting the invariant to a state with the same heap *)

  Lemma in_heap_same st st' a : heap_of st' = heap_of st -> (in_heap st' a <-> in_heap st a).
  Proof. intros E. unfold in_heap. rewrite E. reflexivity. Qed.

  Lemma field_transfer st st' off q :
    tinfo_ok st tinfo -> In off [off_alloc; off_limit; off_fp; off_nalloc] ->
    (forall a, in_heap st a -> IntMaps.lookup a (mem_of st') = IntMaps.lookup a (mem_of st)) ->
    field st tinfo off q -> field st' tinfo off q.
  Proof.
    intros Hok Hoff Hh Hf. eapply LLVM_sim.field_frame; [exact Hf|].
    intros a Ha. apply Hh. eapply (LLVM_sim.field_addr_in_heap tinfo Htinfo_range st off); eauto.
  Qed.

  Lemma INV_transfer st st' fp rs vs :
    INV st fp rs vs -> heap_of st' = heap_of st ->
    (forall a, in_heap st a -> IntMaps.lookup a (mem_of st') = IntMaps.lookup a (mem_of st)) ->
    (forall frs, LLVM_sim.chain st fp frs -> forall f, In f frs -> same_bytes st st' (ptr_to_int f) 24) ->
    (forall a, slot_bytes rs a -> IntMaps.lookup a (mem_of st') = IntMaps.lookup a (mem_of st)) ->
    (forall a, in_frames st' a -> in_frames st a) ->
    INV st' fp rs vs.
  Proof.
    intros (Hhi & Hok & Hmem & Hdis & Hfp & Hss & Hsk & Hroots) Eh Hh Hfr Hsl Hin.
    pose proof Hok as (Hf1 & _ & alloc & limit & Ha & Hl & Hal & Hle & Hnin & Hnw & Hlal).
    assert (Ha' : field st' tinfo off_alloc alloc) by (eapply field_transfer; eauto; simpl; auto).
    assert (Hl' : field st' tinfo off_limit limit) by (eapply field_transfer; eauto; simpl; auto).
    assert (Hfp' : field st' tinfo off_fp fp) by (eapply field_transfer; eauto; simpl; auto 6).
    assert (Hnurs : forall a, nursery st' tinfo a -> nursery st tinfo a).
    { intros a (al & li & Hal' & Hli' & Hr). exists al, li.
      rewrite (LLVM_sim.field_det tinfo st' off_alloc al alloc Hal' Ha') in *.
      rewrite (LLVM_sim.field_det tinfo st' off_limit li limit Hli' Hl') in *. auto. }
    destruct Hsk as ((frs & Hc & Hfb & Hfs) & Hslots).
    destruct (LLVM_sim.shadow_stack_chain st st' fp rs frs Hss Hc (Hfr frs Hc)) as [Hss' Hc'].
    split; [|split; [|split; [|split; [|split; [exact Hfp'|split; [exact Hss'|split]]]]]].
    - eapply Hmut; eauto.
      + split; [exact Eh|]. intros a Ha0 _. apply Hh, Ha0.
      + lia.
    - split; [|split].
      + intros off a Hoff Hoa. destruct (Hf1 off a Hoff Hoa) as [Hw Hbh]. split.
        * eapply writable_word_aid; [exact Hw|]. intros b Hb. unfold aid_at. rewrite Hh; [reflexivity|].
          apply Hbh. unfold field_addr. rewrite (LLVM_sim.ptr_off_int _ _ _ Hoa) in Hb. lia.
        * intros b Hb. apply (in_heap_same _ _ _ Eh). apply Hbh, Hb.
      + exists fp, rs. auto.
      + exists alloc, limit. split; [exact Ha'|]. split; [exact Hl'|]. split; [exact Hal|]. split; [exact Hle|].
        split; [|split; [|exact Hlal]].
        * intros a Ha0. apply (in_heap_same _ _ _ Eh). apply Hnin, Ha0.
        * intros i q Hi Hq. eapply writable_word_aid; [eapply Hnw; eauto|].
          intros b Hb. unfold aid_at. rewrite Hh; [reflexivity|]. apply Hnin.
          rewrite (LLVM_sim.ptr_off_int _ _ _ Hq) in Hb.
          assert (ptr_to_int alloc + 8 * i + 8 <= ptr_to_int limit).
          { assert (Hm : (ptr_to_int limit - ptr_to_int alloc - 8 * i) mod 8 = 0).
            { rewrite Zminus_mod, (Zminus_mod (ptr_to_int limit)), Hal, Hlal.
              rewrite Z.mul_comm, Z_mod_mult. reflexivity. }
            apply Z.mod_divide in Hm; [|lia]. destruct Hm as [k Hk]. lia. }
          lia.
    - destruct Hmem as [Hm1 Hm2]. split.
      + intros a Ha0. apply (in_heap_same _ _ _ Eh) in Ha0. rewrite Hh by exact Ha0. apply Hm1, Ha0.
      + intros a Ha0 Hh0. apply (Hm2 a (Hin a Ha0)). apply (in_heap_same _ _ _ Eh), Hh0.
    - intros a Hn. apply Hdis, Hnurs, Hn.
    - split.
      + exists frs. split; [exact Hc'|]. split; [|exact Hfs].
        intros f Hf a Ha0. destruct (Hfb f Hf a Ha0) as [Hal0 Hnh]. split.
        * rewrite (Hfr frs Hc f Hf a Ha0). exact Hal0.
        * rewrite (in_heap_same _ _ _ Eh). exact Hnh.
      + intros a Ha0. destruct (Hslots a Ha0) as [Hal0 Hnh]. split.
        * rewrite Hsl by exact Ha0. exact Hal0.
        * rewrite (in_heap_same _ _ _ Eh). exact Hnh.
    - eapply LLVM_sim.roots_ok_mono; [exact Hroots| |exact Eh|exact Hnurs|].
      + intros a Ha0 _. apply Hh, Ha0.
      + intros r Hr a Ha0. apply Hsl. exists r. split; [exact Hr|exact Ha0].
  Qed.

  Lemma in_frames_snoc st fs0 f a :
    frames_of st = Snoc fs0 f ->
    in_frames st a <-> In a (map ptr_to_int f) \/ In a (map ptr_to_int (LLVM_sim.frames_ptrs fs0)).
  Proof.
    intros E. unfold in_frames. rewrite E. cbn [LLVM_sim.frames_ptrs]. rewrite map_app, in_app_iff. reflexivity.
  Qed.

  (** Pushing a call frame. *)
  Lemma INV_push st st1 fp rs vs : INV st fp rs vs -> push_post st st1 -> INV st1 fp rs vs.
  Proof.
    intros HI (Eh & Ef & Hm). eapply INV_transfer; [exact HI|exact Eh|intros; apply Hm|..].
    - intros frs _ f _ a _. apply Hm.
    - intros a _. apply Hm.
    - intros a Ha. apply (in_frames_snoc _ _ _ _ Ef) in Ha. destruct Ha as [[]|Ha]. exact Ha.
  Qed.

  Lemma chain_det st f frs frs' : LLVM_sim.chain st f frs -> LLVM_sim.chain st f frs' -> frs = frs'.
  Proof.
    intros H. revert frs'. induction H as [g H0|g prev frs Hnz Hp Hc IH]; intros frs' H'.
    - inversion H'; subst; [reflexivity|contradiction].
    - inversion H' as [|? prev' frs'' Hnz' Hp' Hc']; subst; [contradiction|].
      destruct Hp as (a & Ha & Hr). destruct Hp' as (a' & Ha' & Hr').
      assert (a' = a). { unfold ptr_off in Ha, Ha'. rewrite Ha in Ha'. injection Ha'. auto. }
      subst a'. assert (prev' = prev) by (eapply LLVM_sim.reads_ptr_det; eauto). subst prev'.
      f_equal. apply IH. exact Hc'.
  Qed.

  Lemma alloc_nonheap_same st st' a :
    heap_of st' = heap_of st -> IntMaps.lookup a (mem_of st') = IntMaps.lookup a (mem_of st) ->
    alloc_nonheap st a -> alloc_nonheap st' a.
  Proof. intros Eh Em [H1 H2]. split; [rewrite Em; exact H1|rewrite (in_heap_same _ _ _ Eh); exact H2]. Qed.

  (** Popping the callee's call frame [f]: [f]'s addresses were not
      allocated before the call, so the caller's stack memory survives. *)
  Lemma INV_pop st st2 st3 fp rs vs f :
    INV st fp rs vs -> INV st2 fp rs vs -> keeps_stack st st2 rs ->
    frames_of st2 = Snoc (frames_of st) f ->
    (forall a, In a (map ptr_to_int f) -> ~ alloc_nonheap st a) ->
    pop_post st2 st3 (frames_of st) f ->
    INV st3 fp rs vs /\ keeps_stack st st3 rs.
  Proof.
    intros HI HI2 (Hk1 & Hk2 & Hk & Hk4) Ef Hfresh (Eh & Ef3 & _ & Hm).
    assert (Hnot : forall a, alloc_nonheap st a -> ~ In a (map ptr_to_int f)).
    { intros a Ha Hin. exact (Hfresh a Hin Ha). }
    pose proof HI as (_ & _ & _ & _ & _ & Hss & ((frs & Hc & Hfb & Hfs) & Hslots) & _).
    pose proof HI2 as (_ & _ & Hmem2 & _).
    assert (Hb : forall g, In g frs -> same_bytes st st2 (ptr_to_int g) 24).
    { intros g Hg a Ha. apply Hk; [apply (Hfb g Hg a Ha)|apply (Hfs g Hg a Ha)]. }
    destruct (LLVM_sim.shadow_stack_chain st st2 fp rs frs Hss Hc Hb) as [_ Hc2].
    split.
    - eapply INV_transfer; [exact HI2|exact Eh|..].
      + intros a Ha. apply Hm. intros Hin. destruct Hmem2 as [_ Hm2].
        apply (Hm2 a); [|exact Ha]. apply (in_frames_snoc _ _ _ _ Ef). left. exact Hin.
      + intros frs' Hc' g Hg a Ha. rewrite <- (chain_det _ _ _ _ Hc2 Hc') in Hg.
        apply Hm, Hnot. apply (Hfb g Hg a Ha).
      + intros a Ha. apply Hm, Hnot. apply (Hslots a Ha).
      + intros a Ha. apply (in_frames_snoc _ _ _ _ Ef). right. unfold in_frames in Ha. rewrite Ef3 in Ha. exact Ha.
    - split; [|split].
      + intros a Ha. rewrite Hm; [apply Hk1, Ha|]. apply Hnot, Ha.
      + intros a Ha. rewrite (in_heap_same _ _ _ Eh). apply Hk2, Ha.
      + split.
        * intros a Ha Hs. rewrite Hm; [apply Hk; auto|]. apply Hnot, Ha.
        * intros a Ha. unfold aid_at. rewrite Hm; [apply Hk4, Ha|]. apply Hnot, Ha.
  Qed.

  (* ================================================================ *)
  (** ** Source-level facts about the callee *)

  Lemma in_fun_ids B x : In x (fun_ids B) <-> name_in_fundefs B x.
  Proof.
    induction B as [g gt gxs ge B IH|]; cbn [fun_ids].
    - split.
      + intros [<-|H]; [left; constructor|right; apply IH, H].
      + intros H. inversion H as [? H1|? H1]; subst.
        * inversion H1; subst. left; reflexivity.
        * right. apply IH, H1.
    - split; [intros []|intros H; inversion H].
  Qed.

  Lemma is_fun_name B x : is_fun (fun_ids B) x = true <-> name_in_fundefs B x.
  Proof.
    unfold is_fun. rewrite existsb_exists, <- in_fun_ids. split.
    - intros (y & Hy & E). apply Pos.eqb_eq in E. subst. exact Hy.
    - intros H. exists x. split; [exact H|apply Pos.eqb_refl].
  Qed.

  Lemma is_fun_not_name B x : is_fun (fun_ids B) x = false <-> ~ name_in_fundefs B x.
  Proof.
    rewrite <- is_fun_name. destruct (is_fun (fun_ids B) x); split; congruence.
  Qed.

  Lemma fun_in_dsubterm B f ft xs e : fun_in_fundefs B (f, ft, xs, e) -> dsubterm_fds_e e B.
  Proof.
    induction B as [g gt gxs ge B IH|]; intros H; cbn in H; [|inversion H].
    inversion H as [? H1|? H1]; subst.
    - inversion H1; subst. constructor.
    - constructor 2. apply IH, H1.
  Qed.

  Lemma fundefs_ok_fun B f ft xs e : fundefs_ok cenv B -> fun_in_fundefs B (f, ft, xs, e) -> body_ok cenv e.
  Proof.
    induction 1 as [|g gt gxs ge B Hb HB IH]; intros H; cbn in H; [inversion H|].
    inversion H as [? H1|? H1]; subst; [inversion H1; subst; exact Hb|apply IH, H1].
  Qed.

  Lemma callee_facts f ft xs e : fun_in_fundefs fds (f, ft, xs, e) ->
    body_ok cenv e /\ subterm_or_eq e (Efun fds main) /\ unique_bindings e /\
    Ensembles.Disjoint _ (bound_var e) (occurs_free e) /\ NoDup xs /\
    (forall x, occurs_free e x -> In x xs \/ name_in_fundefs fds x) /\
    (forall x, In x xs -> ~ name_in_fundefs fds x).
  Proof.
    intros Hin. destruct Hprog as (Hfok & _ & Hclosed & Hub & _).
    inversion Hub as [| | | | |? ? Hube Hubf Hdis| | | |]; subst.
    destruct (unique_bindings_fun_in_fundefs _ _ _ _ _ Hin Hubf)
      as (Hue & _ & _ & Hdbn & Hdxn & Hdbx & Hnd).
    assert (Hfv : forall x, occurs_free e x -> In x xs \/ name_in_fundefs fds x).
    { intros x Hx. destruct (occurs_free_in_fun _ _ _ _ _ Hin x Hx) as [? Hx'|? [? Hx'|? Hx']].
      - left. exact Hx'.
      - right. exact Hx'.
      - exfalso. apply Hclosed. eexists. apply Free_Efun2. exact Hx'. }
    split; [eapply fundefs_ok_fun; eauto|]. split.
    { apply Relation_Operators.rt_step. apply dsubterm_fds. eapply fun_in_dsubterm; eauto. }
    split; [exact Hue|]. split.
    { constructor. intros x Hx. inversion Hx as [? Hb Hf]; subst.
      destruct (Hfv x Hf) as [H|H].
      - inversion Hdbx as [Hd]. apply (Hd x). constructor; [exact Hb|exact H].
      - inversion Hdbn as [Hd]. apply (Hd x). constructor; [exact Hb|exact H]. }
    split; [exact Hnd|]. split; [exact Hfv|].
    intros x Hx Hn. inversion Hdxn as [Hd]. apply (Hd x). constructor; [exact Hx|exact Hn].
  Qed.

  (* ================================================================ *)
  (** ** The callee's frame *)

  Lemma set_lists_frame (R : term.val -> dvalue -> Prop) xs : forall vs dvs rho0 rho'',
    NoDup xs -> set_lists xs vs rho0 = Some rho'' -> Forall2 R vs dvs ->
    forall x, In x xs -> exists v d, M.get x rho'' = Some v /\ R v d /\
      RM.find (Raw (Zpos x)) (fold_right (fun '(x, dv) => Maps.add x dv) Maps.empty
                                          (combine (map (fun v => Raw (Zpos v)) xs) dvs)) = Some d.
  Proof.
    induction xs as [|x0 xs IH]; intros vs dvs rho0 rho'' Hnd Hset HF x Hx; [destruct Hx|].
    destruct vs as [|v0 vs]; [discriminate|]. cbn in Hset.
    destruct (set_lists xs vs rho0) as [rho1|] eqn:E; [|discriminate]. injection Hset as <-.
    inversion HF as [|? d0 ? dvs' Hr HF']; subst. inversion Hnd as [|? ? Hn Hnd']; subst.
    cbn [map combine fold_right].
    destruct (Pos.eq_dec x x0) as [->|Hne].
    - exists v0, d0. rewrite M.gss. split; [reflexivity|]. split; [exact Hr|]. apply rfind_add_eq.
    - destruct Hx as [->|Hx]; [congruence|].
      destruct (IH vs dvs' rho0 rho1 Hnd' E HF' x Hx) as (v & d & H1 & H2 & H3).
      exists v, d. rewrite M.gso by exact Hne. split; [exact H1|]. split; [exact H2|].
      rewrite rfind_add_neq; [exact H3|]. intros E'. injection E' as E'. congruence.
  Qed.

  Definition callee_frame (xs : list var) (dvs : list dvalue) : stack_frame :=
    new_frame (combine (Name "tinfo" :: map (fun v => Raw (Zpos v)) xs) (Ptr tinfo :: dvs)).

  Lemma callee_tinfo xs dvs : LLVM_sim.tinfo_local tinfo (callee_frame xs dvs).
  Proof. unfold LLVM_sim.tinfo_local, callee_frame, new_frame. cbn. apply rfind_add_eq. Qed.

  Lemma callee_env_rel st e xs vs dvs rho' rho'' :
    NoDup xs -> (forall x, In x xs -> ~ name_in_fundefs fds x) ->
    (forall x, occurs_free e x -> In x xs \/ name_in_fundefs fds x) ->
    set_lists xs vs (def_funs fds fds rho' rho') = Some rho'' ->
    Forall2 (fun v d => exists z, d = I64 z /\ stable_repr st v z) vs dvs ->
    env_rel (occurs_free e) rho'' base_env (callee_frame xs dvs) st.
  Proof.
    intros Hnd Hxn Hfv Hset HF x Hx. destruct (in_dec Pos.eq_dec x xs) as [Hin|Hnin].
    - destruct (set_lists_frame _ xs vs dvs _ _ Hnd Hset HF x Hin) as (v & d & H1 & (z & -> & Hz) & H3).
      exists v. split; [exact H1|]. rewrite (proj2 (is_fun_not_name fds x) (Hxn x Hin)).
      exists z. split; [|exact Hz]. unfold callee_frame, new_frame, base_env. cbn [stack_vars combine fold_right map].
      rewrite rfind_add_neq; [exact H3|discriminate].
    - destruct (Hfv x Hx) as [H|Hn]; [contradiction|].
      exists (Vfun rho' fds x). split.
      + erewrite <- set_lists_not_In; [|exact Hset|exact Hnin]. apply def_funs_eq, Hn.
      + rewrite (proj2 (is_fun_name fds x) Hn). exists rho'. reflexivity.
  Qed.

  (* ================================================================ *)
  (** ** The callee's CFG *)

  Lemma cblock_id (b : LLVMAst.block typ) : blk_id (cblock b) = blk_id b.
  Proof. rewrite cblock_eq. reflexivity. Qed.

  Lemma flat_blocksP_in (bs : list (LLVMAst.block dtyp)) : forall n b, In b bs ->
    exists c, In (fst (Flatten_sem.flat_blockP b c)) (fst (Flatten_sem.flat_blocksP bs n)).
  Proof.
    induction bs as [|b0 bs IH]; intros n b Hb; [destruct Hb|]. cbn [Flatten_sem.flat_blocksP].
    rewrite (Flatten_sem.flat_blockP_fst_snd b0 n).
    destruct (Flatten_sem.flat_blocksP bs (snd (Flatten_sem.flat_blockP b0 n))) as [rs n2] eqn:E. cbn [fst].
    destruct Hb as [<-|Hb].
    - exists n. left. reflexivity.
    - destruct (IH (snd (Flatten_sem.flat_blockP b0 n)) b Hb) as [c Hc]. rewrite E in Hc.
      exists c. right. exact Hc.
  Qed.

  Lemma callee_blocks_in b rest n1 :
    NoDup (map blk_id (b :: rest)) ->
    LLVM_sim.blocks_in (fst (Flatten_sem.flat_blockP (cblock b) 1) ::
                        fst (Flatten_sem.flat_blocksP (map cblock rest) n1)) (b :: rest).
  Proof.
    intros Hnd b' Hb'. cbn [tl] in Hb'.
    destruct (flat_blocksP_in (map cblock rest) n1 (cblock b') (in_map _ _ _ Hb')) as [c Hc].
    exists c. unfold LLVM_sim.flatB.
    rewrite <- (cblock_id b'), <- (Flatten_sem.flat_blockP_id (cblock b') c).
    apply find_ocfg_map; [|right; exact Hc].
    cbn [map]. rewrite Flatten_sem.flat_blockP_id, Flatten_sem.flat_blocksP_ids, map_map, cblock_id.
    rewrite (map_ext _ _ cblock_id). exact Hnd.
  Qed.

  (** The callee [f]'s definition: entry block, arguments, and the other
      blocks for [blocks_in]. *)
  Lemma fun_def_shape f xs e bl fN :
    tr base_env 0%N e 1%positive = (bl, fN) ->
    let df := fun_def f xs e in
    let b0 := LLVM_sim.flatB (cblock (LLVM_sim.hd_blk bl)) 1 in
    init (df_instrs df) = blk_id b0 /\
    RM.find (blk_id b0) (ocfg_map (blks (df_instrs df))) = Some b0 /\
    blk_phis b0 = [] /\
    df_args df = Name "tinfo" :: map (fun v => Raw (Zpos v)) xs /\
    LLVM_sim.blocks_in (blks (df_instrs df)) bl.
  Proof.
    intros Htr df b0.
    destruct (mk_fun_spec go ga prim_of fs (Anon (Zpos f)) xs e bl fN Htr) as (b & rest & -> & Hdi & _ & Hargs).
    destruct (translate_cfg_entry go ga prim_of fs base_env 0%N e 1%positive _ fN Htr)
      as (b' & rest' & q & E & Hph & _). injection E as <- <-.
    destruct (translate_cfg_labels go ga prim_of fs base_env 0%N e 1%positive _ fN Htr) as [_ Hnd].
    pose proof (Flatten_sem.conv_def_flat_def (mk_fun go ga prim_of fs (Anon (Zpos f)) xs e)) as Hcd.
    cbv zeta in Hcd. rewrite Hdi in Hcd. cbn [fst snd] in Hcd.
    unfold df, LLVM_sim.fun_def. rewrite Hcd. cbn [df_instrs df_args init blks LLVM_sim.hd_blk].
    unfold b0, LLVM_sim.flatB. cbn [LLVM_sim.hd_blk].
    split; [rewrite Flatten_sem.flat_blockP_id, cblock_id; reflexivity|].
    split; [apply find_ocfg_map_cons|].
    split; [rewrite Flatten_sem.flat_blockP_phis; apply cblock_phis_nil, Hph|].
    split; [exact Hargs|]. apply callee_blocks_in, Hnd.
  Qed.

  (* ================================================================ *)
  (** ** A whole call of a top-level function *)

  (** Transport of [stable_repr] to a state with the same heap, whose heap
      bytes are unchanged. *)
  Lemma stable_repr_same_heap st st' v z :
    tinfo_ok st tinfo -> heap_of st' = heap_of st ->
    (forall a, in_heap st a -> IntMaps.lookup a (mem_of st') = IntMaps.lookup a (mem_of st)) ->
    stable_repr st v z -> stable_repr st' v z.
  Proof.
    intros Hok Eh Hh Hs. eapply LLVM_sim.stable_repr_mono; [exact Hs| |exact Eh|].
    - intros a Ha _. apply Hh, Ha.
    - pose proof Hok as (_ & _ & alloc & limit & Ha & Hl & _).
      assert (Ha' : field st' tinfo off_alloc alloc) by (eapply field_transfer; eauto; simpl; auto).
      assert (Hl' : field st' tinfo off_limit limit) by (eapply field_transfer; eauto; simpl; auto).
      intros a (al & li & Hal & Hli & Hr). exists al, li.
      rewrite (LLVM_sim.field_det tinfo st' off_alloc al alloc Hal Ha') in *.
      rewrite (LLVM_sim.field_det tinfo st' off_limit li limit Hli Hl') in *. auto.
  Qed.

  Lemma room_0 st fp rs vs : INV st fp rs vs -> room st tinfo (Z.of_N 0).
  Proof.
    intros (_ & (_ & _ & alloc & limit & Ha & Hl & _ & Hle & _) & _). exists alloc, limit. auto with zarith.
  Qed.

  Lemma callee_run f ft xs e rho' rho'' vs dvs st sf stk fp rs vs0 v p fpf dt :
    fun_in_fundefs fds (f, ft, xs, e) ->
    RM.find (Anon (Zpos f)) G = Some (Ptr fpf) -> ptr_to_int p = ptr_to_int fpf ->
    set_lists xs vs (def_funs fds fds rho' rho') = Some rho'' ->
    Forall2 (fun v d => exists z, d = I64 z /\ stable_repr st v z) vs dvs ->
    sim_stmt_fr rho'' e v ->
    INV st fp rs vs0 ->
    oom ctx (ctx _ (Call dt (Ptr p) (Ptr tinfo :: dvs))) (st, ((sf, stk), G)) \/
    exists st3 z,
      runs ctx (ctx _ (Call dt (Ptr p) (Ptr tinfo :: dvs))) (st, ((sf, stk), G)) (st3, ((sf, stk), G)) (inr (I64 z)) /\
      stable_repr st3 v z /\ INV st3 fp rs vs0 /\ frames_of st3 = frames_of st /\ keeps_stack st st3 rs.
  Proof.
    intros Hin Hg Hp Hset HF IH HI.
    destruct (callee_facts f ft xs e Hin) as (Hbok & Hsub & Hub & Hdis & Hnd & Hfv & Hxn).
    assert (Hctx := ctx_fun f ft xs e fpf Hin Hg dt p (Ptr tinfo :: dvs) Hp).
    destruct (tr base_env 0%N e 1%positive) as [bl fN] eqn:Htr.
    destruct (fun_def_shape f xs e bl fN Htr) as (Hinit & Hfind & Hphis & Hargs & Hbin).
    set (df := fun_def f xs e) in *.
    assert (Hlen : length (Ptr tinfo :: dvs) = length (df_args df)).
    { rewrite Hargs. cbn [length]. rewrite length_map. f_equal.
      rewrite <- (Forall2_length HF). symmetry. eapply set_lists_length_eq; eauto. }
    destruct (push_call_frame_cases ctx df (Ptr tinfo :: dvs) st sf stk G Hlen) as [Hoom|(st1 & p0 & Hpush & Hpp)].
    { left. eapply oom_eutt; [symmetry; exact Hctx|]. apply oom_denote_function_push, Hoom. }
    assert (HI1 : INV st1 fp rs vs0) by (eapply INV_push; eauto).
    pose proof Hpp as (Eh1 & Ef1 & Hm1).
    pose proof HI as (_ & Hok & _).
    assert (Henv : env_rel (occurs_free e) rho'' base_env (callee_frame xs dvs) st1).
    { eapply callee_env_rel; eauto. eapply Forall2_impl; [|exact HF].
      intros v0 d (z & -> & Hz). exists z. split; [reflexivity|].
      eapply stable_repr_same_heap; [exact Hok|exact Eh1| |exact Hz]. intros a _. apply Hm1. }
    assert (Hframe : new_frame (combine (df_args df) (Ptr tinfo :: dvs)) = callee_frame xs dvs)
      by (rewrite Hargs; reflexivity).
    rewrite Hframe in Hpush.
    assert (Hok1 : env_ok2 e base_env 1%positive)
      by (intros y; split; [intros _|left]; reflexivity).
    destruct (IH base_env 0%N 1%positive bl fN (blks (df_instrs df)) (Some p0) 1%positive st1
                (callee_frame xs dvs) (sf :: stk) fp rs vs0 Hbok Hsub Hub Hdis Hok1 Htr Hbin HI1
                (callee_tinfo xs dvs) Henv (room_0 _ _ _ _ HI1))
      as [Hoom|(st2 & sfb & z & Hret & Hz & HI2 & (ks & Hfr & Hks) & Hkeep)].
    { left. eapply oom_eutt; [symmetry; exact Hctx|].
      eapply oom_denote_function_body; [exact Hinit|exact Hfind|exact Hphis| |exact Hoom].
      exact Hpush. }
    rewrite Ef1 in Hfr. cbn [push_top] in Hfr.
    rewrite <- Hframe in Hpush.
    destruct (denote_function_runs ctx df _ (Ptr tinfo :: dvs) st sf stk G st1 p0 st2 sfb sf stk G (I64 z)
                (frames_of st) (rev ks ++ [])%list Hinit Hfind Hphis Hpush) as (st3 & Hrun & Hpop);
      [rewrite Hframe; exact Hret|exact Hfr|].
    assert (Hkeep0 : keeps_stack st st2 rs).
    { destruct Hkeep as (K1 & K2 & K3 & K4). split; [|split; [|split]].
      - intros a Ha. apply K1. eapply alloc_nonheap_same; eauto.
      - intros a Ha. apply K2. eapply alloc_nonheap_same; eauto.
      - intros a Ha Hs. rewrite K3; [apply Hm1|eapply alloc_nonheap_same; eauto|exact Hs].
      - intros a Ha. rewrite K4; [unfold aid_at; rewrite Hm1; reflexivity|eapply alloc_nonheap_same; eauto]. }
    assert (Hfresh : forall a, In a (map ptr_to_int (rev ks ++ [])%list) -> ~ alloc_nonheap st a).
    { intros a Ha Han. rewrite app_nil_r, map_rev, <- in_rev in Ha. apply in_map_iff in Ha.
      destruct Ha as (k & <- & Hk). rewrite Forall_forall in Hks. apply (Hks k Hk).
      eapply alloc_nonheap_same; eauto. }
    destruct (INV_pop st st2 st3 fp rs vs0 _ HI HI2 Hkeep0 Hfr Hfresh Hpop) as [HI3 Hkeep3].
    right. exists st3, z. split; [|split; [|split; [exact HI3|split; [apply Hpop|exact Hkeep3]]]].
    - eapply runs_eutt; [symmetry; exact Hctx|exact Hrun].
    - pose proof HI2 as (_ & Hok2 & (_ & Hm2) & _). destruct Hpop as (Eh3 & _ & _ & Hm3).
      eapply stable_repr_same_heap; [exact Hok2|exact Eh3| |exact Hz].
      intros a Ha. apply Hm3. intros Hin'. apply (Hm2 a); [|exact Ha].
      apply (in_frames_snoc _ _ _ _ Hfr). left. exact Hin'.
  Qed.

  (* ================================================================ *)
  (** ** The caller's side: callee pointer and arguments *)

  Lemma is_fun_In x : is_fun fs x = true -> In x fs.
  Proof. intros H. apply in_fun_ids, is_fun_name, H. Qed.

  Lemma stable_repr_fun st rho0 y fp :
    RM.find (Anon (Zpos y)) G = Some (Ptr fp) -> stable_repr st (Vfun rho0 fds y) (ptr_to_int fp).
  Proof. intros H st2 _. apply Repr_fun. exact H. Qed.

  Lemma repr_val_fun_inv st rho0 fl g z :
    repr_val cenv fds G st (Vfun rho0 fl g) z ->
    fl = fds /\ exists fp, RM.find (Anon (Zpos g)) G = Some (Ptr fp) /\ z = ptr_to_int fp.
  Proof.
    intros H. inversion H as [| | |r g' fp Hfp]; subst. split; [reflexivity|]. exists fp. auto.
  Qed.

  Lemma callee_value S e rho env fresh sf stk st f rho' fl f' :
    env_ok2 e env fresh -> env_rel S rho env sf st -> S f ->
    M.get f rho = Some (Vfun rho' fl f') ->
    fl = fds /\ exists fpf p,
      RM.find (Anon (Zpos f')) G = Some (Ptr fpf) /\ ptr_to_int p = ptr_to_int fpf /\
      exp_eval st sf stk G None (cexp (gcallee fs env f)) (Ptr p) /\
      Flatten_sem.noflat_exp (cexp (gcallee fs env f)) /\
      IntrinsicsDefinitions.intrinsic_exp (cexp (gcallee fs env f)) = None.
  Proof.
    intros Hok Henv Hf Hget. destruct (Henv f Hf) as (w & Hw & Hc). rewrite Hget in Hw. injection Hw as <-.
    destruct (is_fun fs f) eqn:Ef.
    - destruct Hc as (rho0 & E). injection E as -> -> ->. split; [reflexivity|].
      destruct (G_funs f (is_fun_In f Ef)) as (fpf & Hg).
      exists fpf, fpf. split; [exact Hg|]. split; [reflexivity|]. rewrite cexp_gcallee_fun by exact Ef.
      split; [apply exp_eval_global, Hg|]. split; [exact I|reflexivity].
    - destruct Hc as (z & Hz & Hs). specialize (Hs st (LLVM_sim.heap_bytes_agree_refl _ _)).
      destruct (repr_val_fun_inv _ _ _ _ _ Hs) as (-> & fpf & Hg & ->). split; [reflexivity|].
      rewrite cexp_gcallee_local by exact Ef.
      assert (Hloc : exp_eval st sf stk G (Some i64) (EXP_Ident (ID_Local (env f))) (I64 (ptr_to_int fpf)))
        by (apply exp_eval_local, Hz).
      destruct (exp_eval_inttoptr' None Hloc) as (q & Hq & _ & Hev).
      exists fpf, q. split; [exact Hg|]. split.
      + rewrite Hq. apply Z.mod_small, ptr_to_int_range.
      + split; [exact Hev|]. split; [|reflexivity]. cbn. apply (env_ok2_not_flat _ _ _ Hok).
  Qed.

  Lemma args_eval S e rho env fresh sf stk st ys : forall vs,
    env_ok2 e env fresh -> env_rel S rho env sf st -> (forall y, In y ys -> S y) ->
    get_list ys rho = Some vs ->
    exists dvs,
      Forall2 (fun '(t, e) v => exp_eval st sf stk G (Some t) e v)
              (map (fun y => (i64, cexp (gvar fs env y))) ys) dvs /\
      Forall2 (fun v d => exists z, d = I64 z /\ stable_repr st v z) vs dvs /\
      Forall (fun y => Flatten_sem.noflat_exp (cexp (gvar fs env y))) ys.
  Proof.
    induction ys as [|y ys IH]; intros vs Hok Henv Hys Hget.
    - injection Hget as <-. exists []. split; [constructor|split; constructor].
    - cbn in Hget. destruct (M.get y rho) as [v|] eqn:Hv; [|discriminate].
      destruct (get_list ys rho) as [vs'|] eqn:Hvs; [|discriminate]. injection Hget as <-.
      destruct (IH vs' Hok Henv (fun y' H => Hys y' (or_intror H)) eq_refl) as (dvs & H1 & H2 & H3).
      destruct (Henv y (Hys y (or_introl eq_refl))) as (w & Hw & Hc). rewrite Hv in Hw. injection Hw as <-.
      destruct (is_fun fs y) eqn:Ef.
      + destruct Hc as (rho0 & ->). destruct (G_funs y (is_fun_In y Ef)) as (fp & Hg).
        exists (I64 (ptr_to_int fp) :: dvs). split; [|split].
        * cbn [map]. constructor; [|exact H1]. rewrite cexp_gvar_fun by exact Ef.
          apply exp_eval_ptrtoint, exp_eval_global, Hg.
        * constructor; [|exact H2]. exists (ptr_to_int fp). split; [reflexivity|]. apply stable_repr_fun, Hg.
        * constructor; [|exact H3]. rewrite cexp_gvar_fun by exact Ef. exact I.
      + destruct Hc as (z & Hz & Hs). exists (I64 z :: dvs). split; [|split].
        * cbn [map]. constructor; [|exact H1]. rewrite cexp_gvar_local by exact Ef. apply exp_eval_local, Hz.
        * constructor; [|exact H2]. exists z. auto.
        * constructor; [|exact H3]. rewrite cexp_gvar_local by exact Ef. cbn.
          apply (env_ok2_not_flat _ _ _ Hok).
  Qed.

  (* ================================================================ *)
  (** ** [Eapp]: tail call *)

  Lemma app_block_shape env fresh f ys :
    let blk := mk_block (Anon (Zpos fresh)) []
                 [ (IId (ntmp fresh 1), INSTR_Call (val_ty, gcallee fs env f) (call_args fs env ys) [] [], []) ]
                 (IVoid 1%Z, TERM_Ret (val_ty, EXP_Ident (ID_Local (ntmp fresh 1))), []) None in
    blk_code (cblock blk) =
      [ (IId (ntmp fresh 1),
         INSTR_Call (i64, cexp (gcallee fs env f))
           (((dptr, EXP_Ident (ID_Local (Name "tinfo"))), []) ::
            map (fun y => ((i64, cexp (gvar fs env y)), [])) ys) [] [], []) ] /\
    blk_term (cblock blk) = (IVoid 1%Z, TERM_Ret (i64, EXP_Ident (ID_Local (ntmp fresh 1))), []).
  Proof.
    intros blk. unfold blk. rewrite cblock_eq. cbn [blk_code blk_term]. split.
    - rewrite ccode_cons, ccode_nil, cinstr_Call, call_args_conv. unfold ctexp. cbn [fst snd]. rewrite cty_val. reflexivity.
    - rewrite cterm_Ret. unfold ctexp. cbn [fst snd]. rewrite cty_val, cexp_Ident. reflexivity.
  Qed.

  Lemma sim_case_app_fr rho rho' fl f' vs xs e_body rho'' f ft ft' ys v :
    M.get f rho = Some (Vfun rho' fl f') ->
    get_list ys rho = Some vs ->
    find_def f' fl = Some (ft', xs, e_body) ->
    set_lists xs vs (def_funs fl fl rho' rho') = Some rho'' ->
    sim_stmt_fr rho'' e_body v ->
    sim_stmt_fr rho (Eapp f ft ys) v.
  Proof.
    intros Hf Hys Hfd Hset IH env chunk fresh blks fN B va c st sf stk fp rs vs0
           Hbok Hsub Hub Hdis Hok Htr Hbin HI Htl Henv Hroom.
    rewrite tr_app in Htr. injection Htr as <- <-.
    destruct (callee_value _ _ rho env fresh sf stk st f rho' fl f' Hok Henv (Free_Eapp1 f ys ft) Hf)
      as (-> & fpf & p & Hg & Hp & Hevf & Hnff & Hintr).
    destruct (args_eval _ _ rho env fresh sf stk st ys vs Hok Henv (fun y Hy => Free_Eapp2 y f ft ys Hy) Hys)
      as (dvs & Hev & Hst & Hnf).
    pose proof (find_def_correct _ _ _ _ _ Hfd) as Hin.
    cbn [LLVM_sim.hd_blk].
    destruct (app_block_shape env fresh f ys) as [Hcode Hterm].
    match goal with |- context [LLVM_sim.flatB (cblock ?b) c] => set (blk := b) in * end.
    set (r := ntmp fresh 1) in *.
    set (K := LLVM_sim.continue va B (blk_id (LLVM_sim.flatB (cblock blk) c))).
    assert (E1 : interp_mcfg (interp_mrec ctx (LLVM_sim.tail_of va B (LLVM_sim.flatB (cblock blk) c))) (st, ((sf, stk), G))
                 ≈ Flatten_sem.run ctx (Flatten_sem.flat_tail va (blk_code (cblock blk)) (blk_term (cblock blk)) c K)
                     (st, ((sf, stk), G)))
      by exact (Flatten_sem.flat_block_tail ctx va (cblock blk) c K _).
    rewrite Hcode, Hterm in E1.
    edestruct (Flatten_sem.flat_tail_call ctx va (IId r) i64 (cexp (gcallee fs env f))
                 (((dptr, EXP_Ident (ID_Local (Name "tinfo"))), []) ::
                  map (fun y => ((i64, cexp (gvar fs env y)), [])) ys) [] [] [] []
                 (IVoid 1%Z, TERM_Ret (i64, EXP_Ident (ID_Local r)), []) c K st sf sf stk G (Ptr p) (Ptr tinfo :: dvs))
      as (_ & af & args' & sf2 & _ & Hi & _ & Hevf2 & _ & Hevargs2 & Heq).
    { exact Hnff. }
    { constructor; [apply Flatten_sem.is_flat_Name|]. rewrite Forall_map. exact Hnf. }
    { exact Hevf. }
    { cbn [map fst]. constructor; [apply exp_eval_local, Htl|]. rewrite map_map. exact Hev. }
    { apply Flatten_sem.agree_noflat_refl. }
    match type of Heq with context [Flatten_sem.flat_tail va [] _ ?cc K] => set (c' := cc) in Heq end.
    assert (Hi' : IntrinsicsDefinitions.intrinsic_exp af = None) by (rewrite Hi; exact Hintr).
    destruct (callee_run f' ft' xs e_body rho' rho'' vs dvs st sf2 stk fp rs vs0 v p fpf i64 Hin Hg Hp Hset Hst IH HI)
      as [Hoom|(st3 & z & Hrun & Hz & HI3 & Hfr3 & Hkeep3)].
    - left. rewrite E1, Heq. apply Flatten_sem.ends_in_oom_bind.
      exact (oom_instr_call ctx va r i64 af args' p (Ptr tinfo :: dvs) st sf2 stk G Hi' Hevf2 Hevargs2 Hoom).
    - right.
      pose proof (instr_call ctx va r i64 af args' p (Ptr tinfo :: dvs) st sf2 stk G st3 sf2 stk G (I64 z)
                    Hi' Hevf2 Hevargs2 Hrun) as Hcall.
      set (sfr := upd_local_sf sf2 (Maps.add r (I64 z) (stack_vars sf2))) in Hcall.
      edestruct (Flatten_sem.flat_tail_term ctx va c' c' (IVoid 1%Z) (TERM_Ret (i64, EXP_Ident (ID_Local r))) []
                   K st3 sfr sfr stk G st3 sfr stk G (inr (I64 z))) as (_ & sf1' & _ & Ht).
      { apply Flatten_sem.is_flat_ntmp. }
      { exists (I64 z). apply exp_eval_local. apply rfind_add_eq. }
      { apply Pos.le_refl. }
      { apply Flatten_sem.agree_except_refl. }
      { apply term_ret. apply exp_eval_local. apply rfind_add_eq. }
      exists st3, sf1', z. split; [|split; [exact Hz|split; [exact HI3|split]]].
      + unfold returns. rewrite E1, Heq.
        unfold runs in Hcall. change (interp_mcfg (interp_mrec ctx ?t) ?s) with (Flatten_sem.run ctx t s) in Hcall.
        rewrite Hcall, Eqit.bind_ret_l. cbv beta iota. rewrite Ht. unfold K. cbn [LLVM_sim.continue].
        apply Flatten_sem.run_ret.
      + exists []. split; [rewrite Hfr3; symmetry; apply LLVM_sim.push_top_nil|constructor].
      + exact Hkeep3.
  Qed.

  (* ================================================================ *)
  (** ** [Eletapp]: source-level facts *)

  Lemma dsubterm_fds_bound e B y : dsubterm_fds_e e B -> bound_var e y -> bound_var_fundefs B y.
  Proof.
    induction 1 as [e g gt gys B|e B g gt gys ge H IH]; intros Hy.
    - apply Bound_Fcons3. exact Hy.
    - apply Bound_Fcons2. apply IH, Hy.
  Qed.

  Lemma dsubterm_bound e1 e2 y : dsubterm_e e1 e2 -> bound_var e1 y -> bound_var e2 y.
  Proof.
    intros H Hy. inversion H; subst.
    - apply Bound_Econstr2, Hy.
    - apply Bound_Eproj2, Hy.
    - apply Bound_Eprim_val2, Hy.
    - apply Bound_Eprim2, Hy.
    - apply Bound_Eletapp2, Hy.
    - eapply Bound_Ecase; eauto.
    - apply Bound_Efun1. eapply dsubterm_fds_bound; eauto.
    - apply Bound_Efun2, Hy.
  Qed.

  Lemma subterm_bound e1 e2 y : subterm_or_eq e1 e2 -> bound_var e1 y -> bound_var e2 y.
  Proof.
    induction 1 as [a b H|a|a b c H1 IH1 H2 IH2]; intros Hy.
    - eapply dsubterm_bound; eauto.
    - exact Hy.
    - apply IH2, IH1, Hy.
  Qed.

  Lemma dsubterm_fds_fun e B : dsubterm_fds_e e B -> exists g gt gxs, fun_in_fundefs B (g, gt, gxs, e).
  Proof.
    induction 1 as [e g gt gys B|e B g gt gys ge H IH].
    - exists g, gt, gys. left. constructor.
    - destruct IH as (g' & gt' & gxs' & Hin). exists g', gt', gxs'. right. exact Hin.
  Qed.

  Lemma subterm_top e : subterm_or_eq e (Efun fds main) ->
    e = Efun fds main \/ subterm_or_eq e main \/
    exists g gt gxs ge, fun_in_fundefs fds (g, gt, gxs, ge) /\ subterm_or_eq e ge.
  Proof.
    intros H. apply Operators_Properties.clos_rt_rtn1 in H.
    inversion H as [|y z Hyz Hy]; subst; [left; reflexivity|right].
    apply Operators_Properties.clos_rtn1_rt in Hy.
    inversion Hyz as [| | | | | |e' fds' e0 Hd|fds' e0]; subst.
    - right. destruct (dsubterm_fds_fun _ _ Hd) as (g & gt & gxs & Hin). exists g, gt, gxs, y. auto.
    - left. exact Hy.
  Qed.

  Lemma bound_not_fun e x :
    subterm_or_eq e (Efun fds main) -> body_ok cenv e -> bound_var e x -> ~ name_in_fundefs fds x.
  Proof.
    intros Hs Hb Hx Hn. destruct Hprog as (_ & _ & _ & Hub & _).
    inversion Hub as [| | | | |? ? Hube Hubf Hdis| | | |]; subst.
    destruct (subterm_top e Hs) as [->|[Hm|(g & gt & gxs & ge & Hin & Hg)]].
    - exact (body_ok_Efun _ _ Hb).
    - inversion Hdis as [Hd]. apply (Hd x). constructor.
      + eapply subterm_bound; eauto.
      + apply name_in_fundefs_bound_var_fundefs, Hn.
    - destruct (unique_bindings_fun_in_fundefs _ _ _ _ _ Hin Hubf) as (_ & _ & _ & Hdbn & _).
      inversion Hdbn as [Hd]. apply (Hd x). constructor; [eapply subterm_bound; eauto|exact Hn].
  Qed.

  Lemma letapp_cont_facts x f ft ys e' :
    body_ok cenv (Eletapp x f ft ys e') -> subterm_or_eq (Eletapp x f ft ys e') (Efun fds main) ->
    unique_bindings (Eletapp x f ft ys e') ->
    Ensembles.Disjoint _ (bound_var (Eletapp x f ft ys e')) (occurs_free (Eletapp x f ft ys e')) ->
    body_ok cenv e' /\ subterm_or_eq e' (Efun fds main) /\ unique_bindings e' /\
    Ensembles.Disjoint _ (bound_var e') (occurs_free e') /\
    is_fun fs x = false /\ ~ occurs_free (Eletapp x f ft ys e') x /\
    (forall y, occurs_free e' y -> y <> x -> occurs_free (Eletapp x f ft ys e') y) /\
    (forall y, bound_var e' y -> bound_var (Eletapp x f ft ys e') y).
  Proof.
    intros Hb Hs Hu Hd. inversion Hb as [| | | ? ? ? ? ? Hb'| | |]; subst.
    inversion Hu as [| |? ? ? ? ? Hx Hu'| | | | | | |]; subst.
    split; [exact Hb'|]. split.
    { eapply Relation_Operators.rt_trans; [apply Relation_Operators.rt_step; constructor|exact Hs]. }
    split; [exact Hu'|]. split.
    { constructor. intros y Hy. inversion Hy as [? Hy1 Hy2]; subst. inversion Hd as [Hd'].
      apply (Hd' y). constructor; [apply Bound_Eletapp2, Hy1|].
      apply Free_Eletapp2; [|exact Hy2]. intros ->. apply Hx, Hy1. }
    split; [apply is_fun_not_name; eapply bound_not_fun; eauto; constructor|].
    split; [intros Hf; inversion Hd as [Hd']; apply (Hd' x); constructor; [constructor|exact Hf]|].
    split; [intros y Hy Hne; apply Free_Eletapp2; [intros E; apply Hne; symmetry; exact E|exact Hy]|].
    intros y Hy. apply Bound_Eletapp2, Hy.
  Qed.

  Lemma la_env_ok2 x f ft ys e' env fresh :
    env_ok2 (Eletapp x f ft ys e') env fresh ->
    Ensembles.Disjoint _ (bound_var e') (occurs_free e') ->
    env_ok2 e' (la_env fs env fresh x e') (Pos.succ fresh).
  Proof.
    intros Hok Hd y. split.
    - intros Hb. rewrite la_env_other.
      + apply (Hok y). apply Bound_Eletapp2, Hb.
      + rewrite la_roots_spec. intros (_ & Hf & _). inversion Hd as [Hd']. apply (Hd' y). constructor; assumption.
    - destruct (In_dec Pos.eq_dec y (la_roots fs x e')) as [Hin|Hnin].
      + apply In_nth_error in Hin. destruct Hin as [i Hi]. rewrite (la_env_root _ _ _ _ _ _ _ Hi).
        right. exists fresh, (1000 + i)%nat. split; [lia|reflexivity].
      + rewrite la_env_other by exact Hnin. destruct (Hok y) as [_ [E|(s & k & Hs & E)]]; [left; exact E|].
        right. exists s, k. split; [lia|exact E].
  Qed.

  Lemma cblock_prepend (x : code typ) (b : LLVMAst.block typ) :
    let b1 := mk_block (blk_id b) (blk_phis b) (x ++ blk_code b)%list (blk_term b) (blk_comments b) in
    blk_code (cblock b1) = (ccode x ++ blk_code (cblock b))%list /\
    blk_term (cblock b1) = blk_term (cblock b) /\ blk_id (cblock b1) = blk_id b.
  Proof. intros b1. unfold b1. rewrite !cblock_eq. cbn. rewrite ccode_app. auto. Qed.

  (** What running the safepoint code [la_code] of [Eletapp x f ft ys e']
      achieves (in its flattened form, followed by the continuation's entry
      block [l], [tmt]): out of memory, or the call returned, the result is
      bound to [x], the live variables of [e'] are reloaded into their new
      names, and the shadow stack is back to its state before the call. *)
  Definition la_spec : Prop :=
    forall va x f ft ft' ys e' rho rho' fl f' vs_a xs e_body rho'' v env fresh sf stk st fp rs vs
           l tmt c (K : block_id + dvalue -> CFGtop ((block_id * block_id) + dvalue)),
      M.get f rho = Some (Vfun rho' fl f') -> get_list ys rho = Some vs_a ->
      find_def f' fl = Some (ft', xs, e_body) ->
      set_lists xs vs_a (def_funs fl fl rho' rho') = Some rho'' -> sim_stmt_fr rho'' e_body v ->
      env_ok2 (Eletapp x f ft ys e') env fresh ->
      env_rel (occurs_free (Eletapp x f ft ys e')) rho env sf st ->
      is_fun fs x = false -> ~ occurs_free (Eletapp x f ft ys e') x ->
      INV st fp rs vs -> LLVM_sim.tinfo_local tinfo sf ->
      ends_in_oom (Flatten_sem.run ctx
                     (Flatten_sem.flat_tail va (ccode (la_code fs env fresh x f ys e') ++ l)%list tmt c K)
                     (st, ((sf, stk), G))) \/
      exists st4 sf4 c1 ks,
        Flatten_sem.run ctx (Flatten_sem.flat_tail va (ccode (la_code fs env fresh x f ys e') ++ l)%list tmt c K)
                        (st, ((sf, stk), G))
        ≈ Flatten_sem.run ctx (Flatten_sem.flat_tail va l tmt c1 K) (st4, ((sf4, stk), G)) /\
        INV st4 fp rs vs /\ keeps_stack st st4 rs /\
        frames_of st4 = push_top ks (frames_of st) /\
        Forall (fun k => IntMaps.lookup (ptr_to_int k) (mem_of st) = None) ks /\
        env_rel (occurs_free e') (M.set x v rho) (la_env fs env fresh x e') sf4 st4 /\
        LLVM_sim.tinfo_local tinfo sf4.

  Lemma sim_case_letapp_of_la_spec rho rho' fl f' vs_a xs e_body rho'' x f ft ft' ys e' v v' :
    la_spec ->
    M.get f rho = Some (Vfun rho' fl f') ->
    get_list ys rho = Some vs_a ->
    find_def f' fl = Some (ft', xs, e_body) ->
    set_lists xs vs_a (def_funs fl fl rho' rho') = Some rho'' ->
    sim_stmt_fr rho'' e_body v ->
    sim_stmt_fr (M.set x v rho) e' v' ->
    sim_stmt_fr rho (Eletapp x f ft ys e') v'.
  Proof.
    intros Hla Hf Hys Hfd Hset IHb IHk env chunk fresh blks fN B va c st sf stk fp rs vs
           Hbok Hsub Hub Hdis Hok Htr Hbin HI Htl Henv Hroom.
    destruct (letapp_cont_facts x f ft ys e' Hbok Hsub Hub Hdis)
      as (Hbok' & Hsub' & Hub' & Hdis' & Hxf & Hxfree & _ & _).
    destruct (tr (la_env fs env fresh x e') 0%N e' (Pos.succ fresh)) as [blks' fN'] eqn:Htr'.
    rewrite (tr_letapp go ga prim_of fs env chunk x f ft ys e' fresh blks' fN' Htr') in Htr.
    injection Htr as <- <-.
    destruct (translate_cfg_entry go ga prim_of fs _ 0%N e' (Pos.succ fresh) _ fN' Htr')
      as (b' & rest' & q & -> & _ & _).
    cbn [prepend_code LLVM_sim.hd_blk].
    destruct (cblock_prepend (la_code fs env fresh x f ys e') b') as (Hcode & Hterm & Hid).
    match goal with |- context [LLVM_sim.flatB (cblock ?b) c] => set (hd := b) in * end.
    set (K := LLVM_sim.continue va B (blk_id (LLVM_sim.flatB (cblock hd) c))).
    assert (E1 : interp_mcfg (interp_mrec ctx (LLVM_sim.tail_of va B (LLVM_sim.flatB (cblock hd) c))) (st, ((sf, stk), G))
                 ≈ Flatten_sem.run ctx (Flatten_sem.flat_tail va (blk_code (cblock hd)) (blk_term (cblock hd)) c K)
                     (st, ((sf, stk), G)))
      by exact (Flatten_sem.flat_block_tail ctx va (cblock hd) c K _).
    rewrite Hcode, Hterm in E1.
    destruct (Hla va x f ft ft' ys e' rho rho' fl f' vs_a xs e_body rho'' v env fresh sf stk st fp rs vs
                (blk_code (cblock b')) (blk_term (cblock b')) c K Hf Hys Hfd Hset IHb Hok Henv Hxf Hxfree HI Htl)
      as [Hoom|(st4 & sf4 & c1 & ks4 & Hrun & HI4 & Hk4 & Hfr4 & Hks4 & Henv4 & Htl4)].
    { left. rewrite E1. exact Hoom. }
    assert (HK : K = LLVM_sim.continue va B (blk_id (LLVM_sim.flatB (cblock b') c1))).
    { unfold K. rewrite !LLVM_sim.flatB_id, Hid, cblock_id. reflexivity. }
    assert (E2 : Flatten_sem.run ctx (Flatten_sem.flat_tail va (blk_code (cblock b')) (blk_term (cblock b')) c1 K)
                   (st4, ((sf4, stk), G))
                 ≈ interp_mcfg (interp_mrec ctx (LLVM_sim.tail_of va B (LLVM_sim.flatB (cblock b') c1)))
                     (st4, ((sf4, stk), G))).
    { rewrite HK. symmetry. exact (Flatten_sem.flat_block_tail ctx va (cblock b') c1 _ _). }
    destruct (IHk (la_env fs env fresh x e') 0%N (Pos.succ fresh) (b' :: rest') fN' B va c1 st4 sf4 stk fp rs vs
                Hbok' Hsub' Hub' Hdis' (la_env_ok2 x f ft ys e' env fresh Hok Hdis') Htr' Hbin HI4 Htl4 Henv4
                (room_0 _ _ _ _ HI4))
      as [Hoom|(st5 & sf5 & z & Hret & Hz & HI5 & (ks5 & Hfr5 & Hks5) & Hk5)].
    { left. rewrite E1, Hrun, E2. exact Hoom. }
    right. exists st5, sf5, z. split; [|split; [exact Hz|split; [exact HI5|split]]].
    - unfold returns. rewrite E1, Hrun, E2. exact Hret.
    - exists (ks4 ++ ks5)%list. split.
      + rewrite Hfr5, Hfr4. apply LLVM_sim.push_top_app.
      + apply Forall_app. split.
        * eapply Forall_impl; [|exact Hks4]. intros k Hk Han. exact (proj1 Han Hk).
        * eapply Forall_impl; [|exact Hks5]. intros k Hk Han. apply Hk.
          eapply LLVM_sim.keeps_stack_nonheap; [exact Hk4|exact Han].
    - eapply LLVM_sim.keeps_stack_trans; eauto.
  Qed.

  (* ================================================================ *)
  (** ** Reading through pointers with another provenance *)

  Lemma mbtd_ptr_prov bs q :
    memory_bytes_to_dvalue bs DTYPE_Pointer = ret (DVALUE_Base (DVALUE_Pointer q)) ->
    ptr_provenance q = wildcard_prov.
  Proof.
    intros H. cbn -[int_to_ptr] in H.
    match type of H with context [match ?m with EOU.raise_error _ => _ | _ => _ end] =>
      match m with context [map_monad] => destruct m as [| | |[|v]] eqn:E0 end end;
      cbn -[int_to_ptr] in H; try discriminate.
    match type of H with context [match ?m with EOU.raise_error _ => _ | _ => _ end] =>
      match m with int_to_ptr _ _ => destruct m as [| | |q0] eqn:E end end;
      cbn in H; try discriminate.
    injection H as <-. eapply int_to_ptr_provenance; exact E.
  Qed.

  Lemma reads_ptr_wild st a q : reads_ptr st a q -> ptr_provenance q = wildcard_prov.
  Proof.
    intros (st' & H). apply read_dvalue_runs in H. destruct H as (_ & ptrs & bs & _ & _ & H).
    eapply mbtd_ptr_prov; eauto.
  Qed.

  Lemma Forall2_rev_append {A B} (R : A -> B -> Prop) acc acc' l l' :
    Forall2 R acc acc' -> Forall2 R l l' -> Forall2 R (rev_append acc l) (rev_append acc' l').
  Proof.
    intros H. revert l l'. induction H as [|a b acc acc' Hab H IH]; intros l l' Hl; [exact Hl|].
    cbn. apply IH. constructor; assumption.
  Qed.

  Lemma map_monad_acc_sim {A B C} (f : A -> EOU.EOU B) (g : A -> EOU.EOU C) (R : B -> C -> Prop) :
    (forall a b, f a = ret b -> exists c, g a = ret c /\ R b c) ->
    forall l acc acc' res,
      Forall2 R acc acc' ->
      (fix loop (acc : list B) (l : list A) : EOU.EOU (list B) :=
         match l with
         | [] => ret (rev_append acc [])
         | a :: l' => b <- f a;; loop (b :: acc) l'
         end) acc l = ret res ->
      exists res', (fix loop (acc : list C) (l : list A) : EOU.EOU (list C) :=
         match l with
         | [] => ret (rev_append acc [])
         | a :: l' => b <- g a;; loop (b :: acc) l'
         end) acc' l = ret res' /\ Forall2 R res res'.
  Proof.
    intros Hfg. induction l as [|a l IH]; intros acc acc' res Hacc H; cbn in H |- *.
    - inversion H; subst. eexists. split; [reflexivity|]. apply Forall2_rev_append; [exact Hacc|constructor].
    - destruct (f a) as [| | |b] eqn:E; cbn in H; try discriminate.
      destruct (Hfg a b E) as (c & Ec & Hbc). rewrite Ec. cbn.
      apply (IH (b :: acc) (c :: acc') res); [constructor; assumption|exact H].
  Qed.

  Lemma hgp_eq p ix :
    handle_gep_ptr (DTYPE_I 8) p [DVALUE_Base (DVALUE_Iptr ix)] =
    int_to_ptr (ptr_to_int p + to_Z ix) (ptr_provenance p).
  Proof. cbn -[int_to_ptr]. f_equal. destruct (Integers.unsigned ix); reflexivity. Qed.

  Lemma gcp_reprov p p' n ptrs :
    get_consecutive_ptrs p n = ret ptrs -> ptr_to_int p' = ptr_to_int p ->
    exists ptrs', get_consecutive_ptrs p' n = ret ptrs' /\
      Forall2 (fun q q' => ptr_to_int q' = ptr_to_int q /\ ptr_provenance q' = ptr_provenance p') ptrs ptrs'.
  Proof.
    intros H Hp. unfold get_consecutive_ptrs in *. cbn [bind EOU.EOU_monad] in *.
    destruct (intptr_seq 0 n) as [| | | ixs]; try discriminate.
    unfold map_monad_acc in *.
    eapply (map_monad_acc_sim _ _ (fun q q' => ptr_to_int q' = ptr_to_int q /\ ptr_provenance q' = ptr_provenance p'));
      [|constructor|exact H].
    intros ix q Hq. cbn beta in Hq |- *. rewrite hgp_eq in Hq |- *.
    pose proof (ptr_to_int_int_to_ptr _ _ Hq) as Hi.
    assert (Hr : 0 <= ptr_to_int p + to_Z ix < 2^64) by (rewrite <- Hi; apply ptr_to_int_range).
    destruct (int_to_ptr_total (ptr_provenance p') Hr) as (q' & Eq' & Hq1 & Hq2).
    rewrite Hp, Eq'. exists q'. split; [reflexivity|]. split; [|exact Hq2]. lia.
  Qed.

  Lemma access_wild aid : access_allowed wildcard_prov aid = true.
  Proof. reflexivity. Qed.

  Lemma read_reprov t st p p' v :
    memS_returns st (read_dvalue t p) v -> ptr_to_int p' = ptr_to_int p ->
    (forall a aid, ptr_to_int p <= a < ptr_to_int p + Z.of_N (sizeof_dtyp t) ->
                   aid_at st a = Some aid -> access_allowed (ptr_provenance p') aid = true) ->
    memS_returns st (read_dvalue t p') v.
  Proof.
    intros (st0 & H) Hp Hacc. apply read_dvalue_runs in H. destruct H as (-> & ptrs & bs & Eg & HF & Ev).
    destruct (gcp_reprov p p' _ ptrs Eg Hp) as (ptrs' & Eg' & HF').
    exists st. apply read_dvalue_runs. split; [reflexivity|]. exists ptrs', bs.
    split; [exact Eg'|]. split; [|exact Ev].
    apply gcp_spec in Eg. destruct Eg as [L C].
    assert (Hin : forall q, In q ptrs -> ptr_to_int p <= ptr_to_int q < ptr_to_int p + Z.of_N (sizeof_dtyp t)).
    { intros q Hq. destruct (In_consec _ _ _ C Hq) as (i & Hi & Eq & _). rewrite L in Hi. lia. }
    clear Eg' C L Ev. revert ptrs' HF'.
    induction HF as [|q b ptrs0 bs0 Hb HF IH]; intros ptrs' HF'; inversion HF' as [|? q' ? ptrs1 (Hq1 & Hq2) HF1]; subst;
      constructor.
    - destruct Hb as (aid & Hl & _). exists aid. rewrite Hq1. split; [exact Hl|]. rewrite Hq2.
      apply (Hacc (ptr_to_int q)); [apply Hin; left; reflexivity|]. unfold aid_at. rewrite Hl. reflexivity.
    - apply IH; [intros q0 Hq0; apply Hin; right; exact Hq0|exact HF1].
  Qed.

  Lemma reads_word_wild st q q' z :
    reads_word st q z -> ptr_to_int q' = ptr_to_int q -> ptr_provenance q' = wildcard_prov -> reads_word st q' z.
  Proof. intros H E P. eapply read_reprov; [exact H|exact E|]. intros. rewrite P. reflexivity. Qed.

  Lemma reads_ptr_wild' st q q' r :
    reads_ptr st q r -> ptr_to_int q' = ptr_to_int q -> ptr_provenance q' = wildcard_prov -> reads_ptr st q' r.
  Proof. intros H E P. eapply read_reprov; [exact H|exact E|]. intros. rewrite P. reflexivity. Qed.

  (* ================================================================ *)
  (** ** Stepping through flattened straight-line code *)

  (** A run of (unflattened) code, one transferable instruction at a time. *)
  Inductive orig_runs (va : option ptr) (stk : stack) (g : global_env) :
    code dtyp -> state -> stack_frame -> state -> stack_frame -> Prop :=
  | OR_nil st sf : orig_runs va stk g [] st sf st sf
  | OR_cons i l st sf st1 sf1 st2 sf2 :
      Flatten_sem.instr_ok i -> Flatten_sem.instr_evals st sf stk g i ->
      runs ctx (denote_instr i va) (st, ((sf, stk), g)) (st1, ((sf1, stk), g)) tt ->
      orig_runs va stk g l st1 sf1 st2 sf2 -> orig_runs va stk g (i :: l) st sf st2 sf2.

  Lemma orig_runs_app va stk g l1 l2 st sf st1 sf1 st2 sf2 :
    orig_runs va stk g l1 st sf st1 sf1 -> orig_runs va stk g l2 st1 sf1 st2 sf2 ->
    orig_runs va stk g (l1 ++ l2)%list st sf st2 sf2.
  Proof. induction 1; intros Hl2; [exact Hl2|]. econstructor; eauto. Qed.

  Lemma orig_runs_one va stk g i st sf st1 sf1 :
    Flatten_sem.instr_ok i -> Flatten_sem.instr_evals st sf stk g i ->
    runs ctx (denote_instr i va) (st, ((sf, stk), g)) (st1, ((sf1, stk), g)) tt ->
    orig_runs va stk g [i] st sf st1 sf1.
  Proof. intros. econstructor; eauto. constructor. Qed.

  Lemma flat_tail_orig {R} va stk g l st sf st' sf' :
    orig_runs va stk g l st sf st' sf' ->
    forall lo c sfF l2 tmt (K : block_id + dvalue -> CFGtop R),
      (lo <= c)%positive -> Flatten_sem.agree_except lo c sf sfF ->
      exists c' sfF', (c <= c')%positive /\ Flatten_sem.agree_except lo c' sf' sfF' /\
        Flatten_sem.run ctx (Flatten_sem.flat_tail va (l ++ l2)%list tmt c K) (st, ((sfF, stk), g))
        ≈ Flatten_sem.run ctx (Flatten_sem.flat_tail va l2 tmt c' K) (st', ((sfF', stk), g)).
  Proof.
    induction 1 as [st sf|i l st sf st1 sf1 st2 sf2 Hok Hev Hrun H IH];
      intros lo c sfF l2 tmt K Hlo Hag.
    - exists c, sfF. split; [apply Pos.le_refl|]. split; [exact Hag|reflexivity].
    - destruct (Flatten_sem.flat_tail_instr ctx va lo c i (l ++ l2)%list tmt K st sf sfF stk g st1 sf1 stk g
                  Hok Hev Hlo Hag Hrun) as (Hc & sf1F & Hag1 & E).
      destruct (IH lo (snd (Flatten_sem.flat_instrP i c)) sf1F l2 tmt K ltac:(lia) Hag1) as (c' & sfF' & Hc' & Hag' & E').
      exists c', sfF'. split; [lia|]. split; [exact Hag'|].
      cbn [app]. rewrite E. exact E'.
  Qed.

  Lemma flat_tail_orig_oom {R} va stk g l st sf st' sf' i lo c sfF l2 tmt (K : block_id + dvalue -> CFGtop R) :
    orig_runs va stk g l st sf st' sf' ->
    Flatten_sem.instr_ok i -> Flatten_sem.instr_evals st' sf' stk g i ->
    oom ctx (denote_instr i va) (st', ((sf', stk), g)) ->
    (lo <= c)%positive -> Flatten_sem.agree_except lo c sf sfF ->
    ends_in_oom (Flatten_sem.run ctx (Flatten_sem.flat_tail va (l ++ i :: l2)%list tmt c K) (st, ((sfF, stk), g))).
  Proof.
    intros H Hok Hev Hoom Hlo Hag.
    destruct (flat_tail_orig va stk g l st sf st' sf' H lo c sfF (i :: l2) tmt K Hlo Hag) as (c' & sfF' & Hc & Hag' & E).
    rewrite E. eapply (Flatten_sem.flat_tail_instr_oom ctx va lo c'); eauto. lia.
  Qed.

  (* ================================================================ *)
  (** ** The safepoint code of [Eletapp], converted *)

  Definition locE (r : raw_id) : LLVMAst.exp dtyp := EXP_Ident (ID_Local r).
  Definition gepA (n : nat) (r : raw_id) (i : nat) : LLVMAst.exp dtyp :=
    OP_GetElementPtr (DTYPE_Array false (N.of_nat n) i64) (dptr, locE r) [(i32, dlit 0); (i64, dlit i)].
  Definition gepF (r : raw_id) (j : nat) : LLVMAst.exp dtyp :=
    OP_GetElementPtr frame_dt (dptr, locE r) [(i32, dlit 0); (i32, dlit j)].
  Definition gepT (n : nat) : LLVMAst.exp dtyp :=
    OP_GetElementPtr tinfo_dt (dptr, locE (Name "tinfo")) [(i32, dlit 0); (i32, dlit n)].

  Definition la_pre (env : nenv) (fresh : positive) (roots : list var) : code dtyp :=
    let nr := length roots in
    let R := ssname fresh 1 in let F := ssname fresh 2 in let P := ssname fresh 3 in
    ((IId R, INSTR_Alloca (DTYPE_Array false (N.of_nat nr) i64) [], [])
     :: (IId F, INSTR_Alloca frame_dt [], [])
     :: ccode (spill_code env (EXP_Ident (ID_Local R)) (TYPE_Array (N.of_nat nr) val_ty) 0 roots)
     ++ [ (IVoid 0%Z, INSTR_Store (dptr, gepA nr R nr) (dptr, gepF F 0) [], []);
          (IVoid 0%Z, INSTR_Store (dptr, gepA nr R 0) (dptr, gepF F 1) [], []);
          (IId P, INSTR_Load dptr (dptr, gepT 4) [], []);
          (IVoid 0%Z, INSTR_Store (dptr, locE P) (dptr, gepF F 2) [], []);
          (IVoid 0%Z, INSTR_Store (dptr, locE F) (dptr, gepT 4) [], []) ])%list.

  Definition la_callI (env : nenv) (x f : var) (ys : list var) : instr_id * instr dtyp * list (metadata dtyp) :=
    (IId (Raw (Zpos x)),
     INSTR_Call (i64, cexp (gcallee fs env f))
       (((dptr, EXP_Ident (ID_Local (Name "tinfo"))), []) :: map (fun y => ((i64, cexp (gvar fs env y)), [])) ys)
       [] [], []).

  Definition la_post (fresh : positive) (roots : list var) : code dtyp :=
    let nr := length roots in
    (ccode (reload_code fresh (EXP_Ident (ID_Local (ssname fresh 1))) (TYPE_Array (N.of_nat nr) val_ty) 0 roots)
     ++ [ (IVoid 0%Z, INSTR_Store (dptr, locE (ssname fresh 3)) (dptr, gepT 4) [], []) ])%list.

  Lemma ccode_la_code env fresh x f ys e' :
    ccode (la_code fs env fresh x f ys e') =
    (la_pre env fresh (la_roots fs x e') ++ la_callI env x f ys :: la_post fresh (la_roots fs x e'))%list.
  Proof.
    unfold la_code. cbn zeta. rewrite ccode_cons. rewrite ccode_cons. rewrite !ccode_app.
    rewrite !ccode_cons, !ccode_nil, cinstr_Alloca, cinstr_Alloca, !cinstr_Store, cinstr_Load, cinstr_Call, call_args_conv.
    unfold la_pre, la_post, la_callI. cbn zeta. cbn [app]. rewrite <- !app_assoc. cbn [app].
    unfold ctexp. cbn [fst snd].
    rewrite !cty_tinfo, !cty_val, cty_val_array, !cexp_gep_arr, !cexp_gep_struct, !cexp_gep_tinfo, !cty_frame, cty_tinfo_struct,
      !cexp_Ident.
    reflexivity.
  Qed.

  (* ================================================================ *)
  (** ** Original runs of the safepoint's instruction forms *)

  Lemma instr_store_ptr_aid va n ev ep p' q st sf stk g :
    exp_eval st sf stk g (Some dptr) ev (Ptr p') ->
    exp_eval st sf stk g (Some dptr) ep (Ptr q) ->
    writable_word st q ->
    exists st' p'',
      runs ctx (denote_instr (IVoid n, INSTR_Store (dptr, ev) (dptr, ep) [], []) va)
           (st, ((sf, stk), g)) (st', ((sf, stk), g)) tt /\
      reads_ptr st' q p'' /\ ptr_to_int p'' = ptr_to_int p' /\ ptr_provenance p'' = wildcard_prov /\
      write_post st st' q /\ (forall a, aid_at st' a = aid_at st a).
  Proof.
    intros Hv Hp Hw. apply writable_word_iff in Hw. destruct Hw as (ptrs & E & W).
    destruct (write_dvalue_exists st DTYPE_Pointer q (Ptr p') ptrs) as (st' & Hrun);
      [rewrite sizeof_ptr; exact E | exact W |].
    destruct (write_read_ptr _ _ _ _ _ Hrun) as (p'' & Hr & E1 & E2).
    exists st', p''. split; [eapply instr_store_run; eauto|].
    split; [exact Hr|]. split; [exact E1|]. split; [exact E2|]. split.
    - eapply write_dvalue_post; [apply sizeof_ptr|exact Hrun].
    - apply write_dvalue_runs in Hrun. apply Hrun.
  Qed.

  Lemma instr_store_word_aid va n ev ep w q st sf stk g :
    exp_eval st sf stk g (Some i64) ev (I64 w) ->
    exp_eval st sf stk g (Some dptr) ep (Ptr q) ->
    writable_word st q ->
    exists st',
      runs ctx (denote_instr (IVoid n, INSTR_Store (i64, ev) (dptr, ep) [], []) va)
           (st, ((sf, stk), g)) (st', ((sf, stk), g)) tt /\
      reads_word st' q w /\ write_post st st' q /\ (forall a, aid_at st' a = aid_at st a).
  Proof.
    intros Hv Hp Hw. destruct (Hw w) as (st' & Hrun & Hr).
    exists st'. split; [eapply instr_store_run; eauto|]. split; [exact Hr|]. split.
    - eapply write_dvalue_post; [apply sizeof_i64|exact Hrun].
    - apply write_dvalue_runs in Hrun. apply Hrun.
  Qed.

  Lemma stores_orig va sf stk g c l st :
    stores sf stk g c l -> Forall Flatten_sem.instr_ok c ->
    Forall (fun qw => writable_word st (fst qw)) l ->
    ForallOrdPairs (fun a b => disj8 (fst a) (fst b)) l ->
    exists st', orig_runs va stk g c st sf st' sf /\ writes_post st st' (map fst l) /\
      Forall (fun qw => reads_word st' (fst qw) (snd qw)) l /\ (forall a, aid_at st' a = aid_at st a).
  Proof.
    intros H. revert st. induction H as [|n ev ep w q c l Hv Hp Hc IH]; intros st Hok W D.
    - exists st. split; [constructor|split; [apply writes_post_nil|split; [constructor|reflexivity]]].
    - inversion Hok as [|? ? Hok1 Hokc]; subst.
      inversion W as [|? ? Wq Wl]; subst. inversion D as [|? ? Dq Dl]; subst.
      destruct (instr_store_word_aid va n ev ep w q st sf stk g (Hv st) (Hp st) Wq) as (st1 & R1 & Rq & P1 & A1).
      destruct (IH st1 Hokc) as (st2 & R2 & P2 & Rl & A2); [|exact Dl|].
      { eapply Forall_impl; [|exact Wl]. intros [q' w'] Wq'. apply P1, Wq'. }
      exists st2. split; [|split; [eapply writes_post_cons; eauto|split]].
      + econstructor; [exact Hok1| |exact R1|exact R2]. cbn. split; eexists; [apply Hv|apply Hp].
      + constructor; [|exact Rl]. cbn. apply P2; [exact Rq|].
        rewrite Forall_forall in Dq |- *. intros q' Hin. apply in_map_iff in Hin.
        destruct Hin as ([q'' w''] & <- & Hin). apply (Dq _ Hin).
      + intros a. rewrite A2, A1. reflexivity.
  Qed.

  Lemma spill_stores env R n i rs ws p qs sf stk g :
    (forall st0, exp_eval st0 sf stk g (Some dptr) (EXP_Ident (ID_Local R)) (Ptr p)) ->
    Forall2 (fun r w => RM.find (env r) (stack_vars sf) = Some (I64 w)) rs ws ->
    Z.of_nat (i + length rs) < 2^63 ->
    slot_ptrs p i qs -> length qs = length ws ->
    stores sf stk g (ccode (spill_code env (EXP_Ident (ID_Local R)) (TYPE_Array n val_ty) i rs)) (combine qs ws).
  Proof.
    intros Hp. revert i qs ws. induction rs as [|r rs IH]; intros i qs ws Hrs Hi S L.
    - inversion Hrs; subst. destruct qs; [|discriminate]. rewrite ccode_spill_nil. constructor.
    - inversion Hrs as [|? w ? ws' Hr Hrs']; subst. destruct qs as [|q qs]; [discriminate|].
      destruct S as [Hq S]. rewrite ccode_spill_cons. cbn [combine].
      apply stores_cons.
      + intros st0. apply exp_eval_local, Hr.
      + intros st0. rewrite cexp_gep_arr, cexp_Ident. unfold LLVM_emit_facts.i64.
        eapply exp_eval_gep_arr; [cbn [length] in Hi; lia|apply Hp|exact Hq].
      + apply IH; auto. cbn [length] in Hi. lia.
  Qed.

  Lemma spill_ok env R n i rs :
    Flatten_sem.is_flat R = false -> (forall r, Flatten_sem.is_flat (env r) = false) ->
    Forall Flatten_sem.instr_ok (ccode (spill_code env (EXP_Ident (ID_Local R)) (TYPE_Array n val_ty) i rs)).
  Proof.
    intros HR Henv. revert i. induction rs as [|r rs IH]; intros i.
    - rewrite ccode_spill_nil. constructor.
    - rewrite ccode_spill_cons. constructor; [|apply IH].
      rewrite cexp_gep_arr, cexp_Ident. cbn. split; [apply Henv|]. auto.
  Qed.

  Lemma reload_orig va seed R n i rs ws p st sf stk g :
    RM.find R (stack_vars sf) = Some (Ptr p) ->
    Flatten_sem.is_flat R = false ->
    (forall k, (k < length rs)%nat -> ssname seed (1000 + (i + k)) <> R) ->
    length ws = length rs ->
    Z.of_nat (i + length rs) < 2^63 ->
    slots_ok (fun q w => reads_word st q w) p i ws ->
    orig_runs va stk g (ccode (reload_code seed (EXP_Ident (ID_Local R)) (TYPE_Array n val_ty) i rs))
              st sf st (upd_local_sf sf (reload_locals (stack_vars sf) seed i ws)).
  Proof.
    intros Hr0 HR Hne. revert i ws sf Hr0 Hne. induction rs as [|r rs IH]; intros i ws sf Hr0 Hne L Hi Rd.
    - destruct ws; [|discriminate]. rewrite ccode_reload_nil. cbn [reload_locals].
      replace (upd_local_sf sf (stack_vars sf)) with sf by (destruct sf; reflexivity). constructor.
    - destruct ws as [|w ws]; [discriminate|]. destruct Rd as ((q & Hq & Rq) & Rd).
      rewrite ccode_reload_cons.
      assert (Hev : exp_eval st sf stk g (Some dptr) (cexp (gep_arr (TYPE_Array n val_ty) (EXP_Ident (ID_Local R)) i)) (Ptr q)).
      { rewrite cexp_gep_arr, cexp_Ident. unfold LLVM_emit_facts.i64.
        eapply exp_eval_gep_arr; [cbn [length] in Hi; lia|apply exp_eval_local, Hr0|exact Hq]. }
      econstructor.
      + rewrite cexp_gep_arr, cexp_Ident. cbn. split; [apply Flatten_sem.is_flat_ssname|]. auto.
      + cbn. eexists. exact Hev.
      + unfold LLVM_emit_facts.i64, LLVM_emit_facts.dptr. apply (instr_load_word ctx va _ _ q w); [exact Hev|exact Rq].
      + cbn [reload_locals].
        set (m := Maps.add (ssname seed (1000 + i)) (I64 w) (stack_vars sf)).
        change (reload_locals m seed (S i) ws) with (reload_locals (stack_vars (upd_local_sf sf m)) seed (S i) ws).
        rewrite <- (upd_local_sf_twice sf m (reload_locals (stack_vars (upd_local_sf sf m)) seed (S i) ws)).
        apply IH.
        * change (RM.find R m = Some (Ptr p)). subst m. rewrite rfind_add_neq; [exact Hr0|].
          specialize (Hne 0%nat). rewrite Nat.add_0_r in Hne. apply Hne. cbn. lia.
        * intros k Hk. specialize (Hne (S k)). rewrite Nat.add_succ_r in Hne. apply Hne. cbn. lia.
        * cbn in L. lia.
        * cbn [length] in Hi. lia.
        * exact Rd.
  Qed.

  (* ================================================================ *)
  (** ** Freshly [alloca]'d words are writable *)

  Lemma Forall_Nseq (P : N -> Prop) len : forall start,
    (forall k, (start <= k < start + N.of_nat len)%N -> P k) -> Forall P (Nseq start len).
  Proof.
    induction len as [|len IH]; intros start H; cbn [Nseq]; constructor.
    - apply H. lia.
    - apply IH. intros k Hk. apply H. lia.
  Qed.

  Lemma loop_exists {A B} (f : A -> EOU.EOU B) : forall l acc,
    (forall a, In a l -> exists b, f a = ret b) ->
    exists res, (fix loop (acc : list B) (l : list A) : EOU.EOU (list B) :=
         match l with
         | [] => ret (rev_append acc [])
         | a :: l' => b <- f a;; loop (b :: acc) l'
         end) acc l = ret res.
  Proof.
    induction l as [|a l IH]; intros acc H; cbn; [eexists; reflexivity|].
    destruct (H a (or_introl eq_refl)) as (b & Eb). rewrite Eb. cbn.
    apply IH. intros a' Ha'. apply H. right. exact Ha'.
  Qed.

  Lemma gcp_exists q n :
    ptr_to_int q + Z.of_N n <= 2^64 -> exists ptrs, get_consecutive_ptrs q n = ret ptrs.
  Proof.
    intros Hq. pose proof (ptr_to_int_range q) as Hr.
    unfold get_consecutive_ptrs, intptr_seq. rewrite seq_map_monad_acc_eq, N_to_nat_safe_eq.
    set (ixs := map (fun k => @Integers.repr 64 (Z.of_N k)) (Nseq 0 (N.to_nat n))).
    match goal with |- context [map_monad ?f ?l] => assert (Hm : map_monad f l = EOU.raise_ret ixs) end.
    { apply map_monad_EOU_Forall2. unfold ixs.
      assert (HF : Forall (fun k => (k < n)%N) (Nseq 0 (N.to_nat n))) by (apply Forall_Nseq; intros k Hk; lia).
      induction HF as [|k l Hk HF IH]; cbn [map]; constructor; [|exact IH].
      cbn. unfold from_Z_bits.
      replace ((Z.of_N k <=? Integers.max_unsigned) && (Z.of_N k >=? 0)) with true; [reflexivity|].
      symmetry. apply andb_true_intro. unfold Integers.max_unsigned. rewrite modulus64.
      split; [apply Z.leb_le|apply Z.geb_le]; lia. }
    rewrite Hm. cbn [bind EOU.EOU_monad]. unfold map_monad_acc.
    apply loop_exists. intros ix Hix. rewrite hgp_eq.
    unfold ixs in Hix. apply in_map_iff in Hix. destruct Hix as (k & Eix & Hk).
    assert (Hkn : (k < n)%N).
    { apply In_nth_error in Hk. destruct Hk as [i Hi].
      assert (Hl : (i < length (Nseq 0 (N.to_nat n)))%nat).
      { apply nth_error_Some. rewrite Hi. discriminate. }
      rewrite Nseq_length in Hl.
      rewrite nth_error_Nseq' in Hi by exact Hl. injection Hi as <-. lia. }
    assert (Ht : to_Z ix = Z.of_N k).
    { apply from_Z_to_Z. rewrite <- Eix. cbn. unfold from_Z_bits.
      replace ((Z.of_N k <=? Integers.max_unsigned) && (Z.of_N k >=? 0)) with true; [reflexivity|].
      symmetry. apply andb_true_intro. unfold Integers.max_unsigned. rewrite modulus64.
      split; [apply Z.leb_le|apply Z.geb_le]; lia. }
    rewrite Ht. destruct (@int_to_ptr_total (ptr_to_int q + Z.of_N k) (ptr_provenance q)) as (q' & E & _); [lia|].
    exists q'. exact E.
  Qed.

  Lemma alloc_post_end st st1 sz p : (0 < sz)%N -> alloc_post st st1 sz p -> ptr_to_int p + Z.of_N sz <= 2^64.
  Proof.
    intros Hsz (_ & (ptrs & C & L & _) & _).
    destruct (nth_error ptrs (N.to_nat sz - 1)) as [q|] eqn:E;
      [|apply nth_error_None in E; lia].
    destruct (C _ _ E) as [Hi _]. pose proof (ptr_to_int_range q). lia.
  Qed.

  Lemma alloc_word_writable st st1 sz p off q :
    alloc_post st st1 sz p -> ptr_off p off q -> 0 <= off -> off + 8 <= Z.of_N sz ->
    writable_word st1 q.
  Proof.
    intros Ha Hq H0 H8. pose proof (alloc_post_end st st1 sz p ltac:(lia) Ha) as Hend.
    pose proof (LLVM_sim.ptr_off_int _ _ _ Hq) as Eq. pose proof (LLVM_sim.ptr_off_prov _ _ _ Hq) as Pq.
    apply writable_word_iff. assert (H8q : ptr_to_int q + Z.of_N 8 <= 2^64) by (change (Z.of_N 8) with 8; lia).
    destruct (gcp_exists q 8 H8q) as (ptrs & E).
    exists ptrs. split; [exact E|]. intros q' Hq'.
    apply gcp_spec in E. destruct E as [L C]. destruct (In_consec _ _ _ C Hq') as (i & Hi & Ei & Pi).
    destruct Ha as (_ & _ & _ & _ & Hw). apply Hw; [congruence|]. rewrite L in Hi. cbn in Hi. lia.
  Qed.

  (* ================================================================ *)
  (** ** Small facts for the safepoint *)

  Lemma slots_build st n : forall s e,
    ptr_to_int e = ptr_to_int s + 8 * Z.of_nat n -> ptr_to_int e < 2^64 ->
    exists rs1, slots_from st s e rs1 /\ length rs1 = n /\
      (forall i r, nth_error rs1 i = Some r -> ptr_off s (8 * Z.of_nat i) r).
  Proof.
    induction n as [|n IH]; intros s e He Hr.
    - exists []. split; [constructor; lia|]. split; [reflexivity|]. intros [|i] r H; discriminate.
    - rewrite Nat2Z.inj_succ in He. pose proof (ptr_to_int_range s) as Hs.
      destruct (LLVM_sim.ptr_off_ex s 8 ltac:(lia)) as [s' Hs'].
      pose proof (LLVM_sim.ptr_off_int _ _ _ Hs') as E'.
      destruct (IH s' e ltac:(lia) Hr) as (rs1 & Hsl & Hl & Hn).
      exists (s :: rs1). split; [econstructor; [lia|exact Hs'|exact Hsl]|]. split; [cbn; f_equal; exact Hl|].
      intros [|i] r H; cbn in H.
      + injection H as <-. replace (8 * Z.of_nat 0) with 0 by lia. apply LLVM_sim.ptr_off_0.
      + replace (8 * Z.of_nat (S i)) with (8 + 8 * Z.of_nat i) by lia.
        eapply LLVM_sim.ptr_off_add; [exact Hs'|apply Hn, H].
  Qed.

  Lemma roots_vals S rho env sf st roots :
    (forall r, In r roots -> S r /\ is_fun fs r = false) -> env_rel S rho env sf st ->
    exists vs1 ws,
      Forall2 (fun r w => RM.find (env r) (stack_vars sf) = Some (I64 w)) roots ws /\
      Forall2 (stable_repr st) vs1 ws /\ Forall2 (fun r v => M.get r rho = Some v) roots vs1.
  Proof.
    intros Hr Henv. induction roots as [|r roots IH].
    - exists [], []. repeat constructor.
    - destruct (IH (fun r' H => Hr r' (or_intror H))) as (vs1 & ws & H1 & H2 & H3).
      destruct (Hr r (or_introl eq_refl)) as [HS Hf].
      destruct (Henv r HS) as (v & Hv & Hc). rewrite Hf in Hc. destruct Hc as (w & Hw & Hs).
      exists (v :: vs1), (w :: ws). repeat constructor; assumption.
  Qed.

  Lemma reload_locals_nth m seed ws : forall i k w,
    nth_error ws k = Some w ->
    RM.find (ssname seed (1000 + (i + k))) (reload_locals m seed i ws) = Some (I64 w).
  Proof.
    revert m. induction ws as [|w0 ws IH]; intros m i k w H; [destruct k; discriminate|].
    cbn [reload_locals]. destruct k as [|k]; cbn in H.
    - injection H as <-. rewrite reload_locals_other.
      + rewrite Nat.add_0_r. apply rfind_add_eq.
      + intros k Hk E. apply ssname_inj in E. lia.
    - replace (1000 + (i + S k))%nat with (1000 + (S i + k))%nat by lia. apply IH, H.
  Qed.

  Lemma disj8_of p q (P : Z -> Prop) :
    (forall a, ptr_to_int p <= a < ptr_to_int p + 8 -> P a) ->
    (forall a, ptr_to_int q <= a < ptr_to_int q + 8 -> ~ P a) -> disj8 p q.
  Proof.
    intros Hp Hq. unfold disj8.
    destruct (Z_le_gt_dec (ptr_to_int p + 8) (ptr_to_int q)) as [H|H]; [left; exact H|].
    destruct (Z_le_gt_dec (ptr_to_int q + 8) (ptr_to_int p)) as [H'|H']; [right; exact H'|].
    exfalso. destruct (Z_le_gt_dec (ptr_to_int p) (ptr_to_int q)) as [H1|H1].
    - apply (Hq (ptr_to_int q)); [lia|]. apply Hp. lia.
    - apply (Hq (ptr_to_int p)); [lia|]. apply Hp. lia.
  Qed.

  (* ================================================================ *)
  (** ** Unlinking the safepoint frame *)

  Lemma app_inv_len {A} (l1 l2 l1' l2' : list A) :
    (l1 ++ l2 = l1' ++ l2')%list -> length l1 = length l1' -> l1 = l1' /\ l2 = l2'.
  Proof.
    revert l1'. induction l1 as [|a l1 IH]; intros [|a' l1'] E L; try discriminate; [split; auto|].
    cbn in E. injection E as -> E. destruct (IH l1' E ltac:(cbn in L; lia)) as [-> ->]. auto.
  Qed.

  Lemma roots_ok_drop st rs1 rs vs1 vs :
    roots_ok cenv fds G st tinfo (rs1 ++ rs) (vs1 ++ vs) -> length vs1 = length rs1 ->
    roots_ok cenv fds G st tinfo rs vs /\
    exists zs1, Forall2 (reads_word st) rs1 zs1 /\ Forall2 (stable_repr st) vs1 zs1.
  Proof.
    intros H L. destruct (LLVM_sim.roots_ok_split' cenv fds G tinfo st rs1 rs _ H) as (vs1' & vs' & zs1 & E & H1 & H2 & H3).
    assert (L' : length vs1 = length vs1').
    { rewrite L, (Forall2_length H1), (Forall2_length H2). reflexivity. }
    destruct (app_inv_len _ _ _ _ E L') as [<- <-]. split; [exact H3|]. exists zs1. auto.
  Qed.

  Lemma INV_unlink st9 st11 f e s fp rs1 rs vs1 vs a_fp :
    INV st9 f (rs1 ++ rs) (vs1 ++ vs) ->
    LLVM_sim.frame_fields st9 f e s fp -> slots_from st9 s e rs1 -> length vs1 = length rs1 ->
    ptr_off tinfo off_fp a_fp ->
    write_post st9 st11 a_fp -> (forall a, aid_at st11 a = aid_at st9 a) ->
    reads_ptr st11 a_fp fp ->
    INV st11 fp rs vs /\ heap_bytes_agree_except st9 st11 (not_object st9 tinfo) /\
    (forall a, nursery st11 tinfo a -> nursery st9 tinfo a) /\
    (forall a, ~ field_addr tinfo off_fp a -> IntMaps.lookup a (mem_of st11) = IntMaps.lookup a (mem_of st9)).
  Proof.
    intros HI Hff Hsl L Hafp (Eh & Ef & _ & Hout & _) Haid Hrd.
    pose proof HI as (Hhi & Hok & Hmem & Hdis & Hfp9 & Hss & Hsk & Hroots).
    pose proof (LLVM_sim.ptr_off_int _ _ _ Hafp) as Eafp.
    assert (Hout' : forall a, ~ field_addr tinfo off_fp a -> IntMaps.lookup a (mem_of st11) = IntMaps.lookup a (mem_of st9)).
    { intros a Ha. apply Hout. unfold field_addr in Ha. lia. }
    assert (Hm : LLVM_sim.mstep st9 st11 (field_addr tinfo off_fp)).
    { split; [exact Eh|]. split; [intros a Ha _; apply Hout', Ha|]. split; [intros a _; apply Haid|].
      exists []. split; [rewrite Ef; symmetry; apply LLVM_sim.push_top_nil|constructor]. }
    assert (HW : forall a, field_addr tinfo off_fp a -> mutator_writes st9 tinfo a) by (intros a Ha; right; right; left; exact Ha).
    assert (HWh : forall a, field_addr tinfo off_fp a -> in_heap st9 a).
    { intros a Ha. eapply (LLVM_sim.field_addr_in_heap tinfo Htinfo_range st9 off_fp); [exact Hok|simpl; auto 6|exact Ha]. }
    pose proof Hok as (_ & _ & alloc & limit & Ha & Hl & Hal & Hle & _).
    assert (Ha' : field st11 tinfo off_alloc alloc).
    { eapply LLVM_sim.field_frame; [exact Ha|]. intros a Hra. apply Hout'. unfold field_addr, off_alloc, off_fp in *. lia. }
    assert (Hfp11 : field st11 tinfo off_fp fp) by (exists a_fp; auto).
    (* the shadow stack below [f] *)
    destruct (LLVM_sim.shadow_stack_unlink st9 f e s fp rs1 (rs1 ++ rs) Hff Hsl Hss) as (rs0 & E0 & Hss0).
    destruct (app_inv_len rs1 rs rs1 rs0 E0 eq_refl) as [_ <-].
    destruct Hsk as ((frs & Hc & Hfb & Hfs) & Hslots).
    pose proof Hff as (Hnz & _ & _ & (a16 & Ha16 & Hp16)).
    inversion Hc as [? H0|? prev frs' Hnz' (b16 & Hb16 & Hpb) Hc' E1 E2]; subst; [contradiction|].
    assert (b16 = a16). { unfold ptr_off in Ha16, Hb16. rewrite Ha16 in Hb16. injection Hb16. auto. } subst b16.
    assert (prev = fp) by (eapply LLVM_sim.reads_ptr_det; eauto). subst prev.
    assert (Hb : forall g, In g frs' -> same_bytes st9 st11 (ptr_to_int g) 24).
    { intros g Hg a Ha0. apply Hout'. intros Hw. destruct (Hfb g (or_intror Hg) a Ha0) as [_ Hnh]. apply Hnh, HWh, Hw. }
    destruct (LLVM_sim.shadow_stack_chain st9 st11 fp rs frs' Hss0 Hc' Hb) as [Hss11 Hc11].
    destruct (LLVM_sim.alloc_le_limit tinfo st9 alloc limit Hok Ha Hl) as [Hle' Hal'].
    destruct (LLVM_sim.INV_mstep_gen cenv fds heap_inv G tinfo Hmut Htinfo_range st9 st11 _ f (rs1 ++ rs) (vs1 ++ vs)
                alloc alloc limit fp rs HI Hm HW Ha Hl Ha' ltac:(lia) Hal' eq_refl Hfp11 Hss11)
      as (H1 & H2 & H3 & H4 & _ & _ & H7 & H8 & H9).
    split; [|split; [exact H9|split; [exact H8|exact Hout']]].
    split; [exact H1|split; [exact H2|split; [exact H3|split; [exact H4|split; [exact Hfp11|split; [exact Hss11|split]]]]]].
    - split.
      + exists frs'. split; [exact Hc11|]. split.
        * intros g Hg a Ha0. destruct (Hfb g (or_intror Hg) a Ha0) as [Hal0 Hnh].
          split; [rewrite (Hb g Hg a Ha0); exact Hal0|rewrite (in_heap_same _ _ _ Eh); exact Hnh].
        * intros g Hg a Ha0 (r & Hr & Hra). apply (Hfs g (or_intror Hg) a Ha0). exists r. split; [apply in_or_app; right; exact Hr|exact Hra].
      + intros a (r & Hr & Hra). destruct (Hslots a (ex_intro _ r (conj (in_or_app _ _ _ (or_intror Hr)) Hra))) as [Hal0 Hnh].
        split; [|rewrite (in_heap_same _ _ _ Eh); exact Hnh].
        rewrite Hout'; [exact Hal0|]. intros Hw. apply Hnh, HWh, Hw.
    - apply (roots_ok_drop st11 rs1 rs vs1 vs H7 L).
  Qed.

  (* ================================================================ *)
  (** ** Bookkeeping of memory steps *)

  Definition allocd (st : state) (a : Z) : Prop := IntMaps.lookup a (mem_of st) <> None.

  Lemma allocd_aid st a : allocd st a <-> aid_at st a <> None.
  Proof. unfold allocd, aid_at. destruct (IntMaps.lookup a (mem_of st)); cbn; split; congruence. Qed.

  (** The allocated bytes of [st] are unchanged in [st']. *)
  Definition pres (st st' : state) : Prop :=
    heap_of st' = heap_of st /\
    (forall a, allocd st a -> IntMaps.lookup a (mem_of st') = IntMaps.lookup a (mem_of st)).

  (** Allocated bytes of [st] stay allocated with the same allocation id. *)
  Definition aidp (st st' : state) : Prop := forall a, allocd st a -> aid_at st' a = aid_at st a.

  Lemma pres_refl st : pres st st.
  Proof. split; auto. Qed.

  Lemma pres_allocd st st' a : pres st st' -> allocd st a -> allocd st' a.
  Proof. intros (_ & H) Ha. unfold allocd. rewrite H; assumption. Qed.

  Lemma aidp_allocd st st' a : aidp st st' -> allocd st a -> allocd st' a.
  Proof. intros H Ha. apply allocd_aid. rewrite H by exact Ha. apply allocd_aid, Ha. Qed.

  Lemma aidp_trans st1 st2 st3 : aidp st1 st2 -> aidp st2 st3 -> aidp st1 st3.
  Proof. intros H1 H2 a Ha. rewrite H2 by (eapply aidp_allocd; eauto). apply H1, Ha. Qed.

  Lemma aidp_all st st' : (forall a, aid_at st' a = aid_at st a) -> aidp st st'.
  Proof. intros H a _. apply H. Qed.

  Lemma aidp_pres st st' : pres st st' -> aidp st st'.
  Proof. intros (_ & H) a Ha. unfold aid_at. rewrite H by exact Ha. reflexivity. Qed.

  Lemma pres_alloc st0 st st1 sz p :
    pres st0 st -> alloc_post st st1 sz p -> pres st0 st1.
  Proof.
    intros (E & H) Hap. pose proof Hap as (E1 & _). split; [congruence|].
    intros a Ha. rewrite (alloc_post_allocated _ _ _ _ _ Hap); [apply H, Ha|].
    eapply pres_allocd; [split; eauto|exact Ha].
  Qed.

  Lemma pres_write st0 st st1 q :
    pres st0 st -> write_post st st1 q ->
    (forall a, ptr_to_int q <= a < ptr_to_int q + 8 -> ~ allocd st0 a) -> pres st0 st1.
  Proof.
    intros (E & H) (E1 & _ & _ & Hout & _) Hq. split; [congruence|].
    intros a Ha. rewrite Hout; [apply H, Ha|]. intros Hr. apply (Hq a Hr Ha).
  Qed.

  Lemma pres_writes st0 st st1 qs :
    pres st0 st -> writes_post st st1 qs ->
    (forall a, Exists (fun q => ptr_to_int q <= a < ptr_to_int q + 8) qs -> ~ allocd st0 a) -> pres st0 st1.
  Proof.
    intros (E & H) (E1 & _ & _ & Hout & _) Hq. split; [congruence|].
    intros a Ha. rewrite Hout; [apply H, Ha|].
    apply Forall_forall. intros q Hin Hr. apply (Hq a); [apply Exists_exists; eauto|exact Ha].
  Qed.

  Lemma slots_ok_intro (P : ptr -> Z -> Prop) p ws : forall i0,
    (forall k w, nth_error ws k = Some w -> exists q, ptr_off p (8 * Z.of_nat (i0 + k)) q /\ P q w) ->
    slots_ok P p i0 ws.
  Proof.
    induction ws as [|w ws IH]; intros i0 H; [exact I|]. split.
    - destruct (H 0%nat w eq_refl) as (q & Hq & Pq). exists q. rewrite Nat.add_0_r in Hq. auto.
    - apply IH. intros k w' Hk. destruct (H (S k) w' Hk) as (q & Hq & Pq). exists q.
      rewrite Nat.add_succ_r in Hq. cbn [Nat.add] in Hq |- *. replace (S i0 + k)%nat with (S (i0 + k)) by lia. auto.
  Qed.

  Lemma slot_ptrs_nth p i0 qs : slot_ptrs p i0 qs ->
    forall k q, nth_error qs k = Some q -> ptr_off p (8 * Z.of_nat (i0 + k)) q.
  Proof.
    revert i0. induction qs as [|q0 qs IH]; intros i0 H k q Hk; [destruct k; discriminate|].
    destruct H as [H0 H]. destruct k as [|k]; cbn in Hk.
    - injection Hk as <-. rewrite Nat.add_0_r. exact H0.
    - rewrite Nat.add_succ_r. apply (IH (S i0) H k q Hk).
  Qed.

  Lemma alloc_post_allocd st st1 sz p a :
    alloc_post st st1 sz p -> ptr_to_int p <= a < ptr_to_int p + Z.of_N sz ->
    exists aid, aid_at st1 a = Some aid /\ access_allowed (ptr_provenance p) aid = true.
  Proof.
    intros Hap Ha. pose proof (alloc_post_end st st1 sz p ltac:(lia) Hap) as Hend.
    destruct (@int_to_ptr_total a (ptr_provenance p)) as (q & _ & Eq & Pq); [pose proof (ptr_to_int_range p); lia|].
    destruct Hap as (_ & _ & _ & _ & Hw). destruct (Hw q Pq ltac:(lia)) as (aid & Haid & Hacc).
    exists aid. rewrite Eq in Haid. rewrite Pq in Hacc. auto.
  Qed.

  Lemma alloc_post_fresh st st1 sz p a : alloc_post st st1 sz p -> ptr_to_int p <= a -> ~ allocd st a.
  Proof. intros (_ & _ & Hf & _) Ha H. apply H, Hf, Ha. Qed.

  Lemma alloc_post_frames st st1 sz p :
    alloc_post st st1 sz p ->
    exists ks, frames_of st1 = push_top ks (frames_of st) /\ Forall (fun k => ~ allocd st (ptr_to_int k)) ks.
  Proof.
    intros Hap. pose proof Hap as (_ & (ptrs & C & _ & Ef) & _). exists ptrs. split; [exact Ef|].
    apply Forall_forall. intros k Hk. destruct (In_consec _ _ _ C Hk) as (i & _ & Ei & _).
    eapply alloc_post_fresh; [exact Hap|]. lia.
  Qed.

  Lemma noflat_ss s k : Flatten_sem.is_flat (ssname s k) = false.
  Proof. apply Flatten_sem.is_flat_ssname. Qed.

  Lemma Forall2_of_nth {A B} (R : A -> B -> Prop) l1 l2 :
    length l1 = length l2 ->
    (forall i a b, nth_error l1 i = Some a -> nth_error l2 i = Some b -> R a b) -> Forall2 R l1 l2.
  Proof.
    revert l2. induction l1 as [|a l1 IH]; intros [|b l2] L H; try discriminate; constructor.
    - apply (H 0%nat); reflexivity.
    - apply IH; [cbn in L; lia|]. intros i a' b' H1 H2. apply (H (S i)); assumption.
  Qed.

  Lemma Forall_combine_nth {A B} (P : A * B -> Prop) l1 l2 i a b :
    Forall P (combine l1 l2) -> nth_error l1 i = Some a -> nth_error l2 i = Some b -> P (a, b).
  Proof.
    revert l2 i. induction l1 as [|a0 l1 IH]; intros [|b0 l2] i HF H1 H2; try (destruct i; discriminate).
    inversion HF as [|? ? Hp HF']; subst. destruct i as [|i]; cbn in H1, H2.
    - injection H1 as <-. injection H2 as <-. exact Hp.
    - eapply IH; eauto.
  Qed.

  (* ================================================================ *)
  (** ** The safepoint before the call: allocate, spill, link *)

  Definition la_sf (sf : stack_frame) (fresh : positive) (pR pF fp : ptr) : stack_frame :=
    upd_local_sf sf (Maps.add (ssname fresh 3) (Ptr fp) (Maps.add (ssname fresh 2) (Ptr pF)
                       (Maps.add (ssname fresh 1) (Ptr pR) (stack_vars sf)))).

  Lemma la_pre_run va env fresh roots SV rho sf stk st fp rs vs :
    INV st fp rs vs -> LLVM_sim.tinfo_local tinfo sf ->
    (forall r, In r roots -> SV r /\ is_fun fs r = false) -> env_rel SV rho env sf st ->
    (forall y k, env y <> ssname fresh k) -> (forall y, Flatten_sem.is_flat (env y) = false) ->
    oom ctx (denote_instr (IId (ssname fresh 1), INSTR_Alloca (DTYPE_Array false (N.of_nat (length roots)) i64) [], []) va)
        (st, ((sf, stk), G)) \/
    (exists st1 sf1,
       orig_runs va stk G [(IId (ssname fresh 1), INSTR_Alloca (DTYPE_Array false (N.of_nat (length roots)) i64) [], [])]
                 st sf st1 sf1 /\
       oom ctx (denote_instr (IId (ssname fresh 2), INSTR_Alloca frame_dt [], []) va) (st1, ((sf1, stk), G))) \/
    exists st8 pR pF fF eR sR rs1 vs1 a_fp ks,
      orig_runs va stk G (la_pre env fresh roots) st sf st8 (la_sf sf fresh pR pF fp) /\
      INV st8 fF (rs1 ++ rs) (vs1 ++ vs) /\
      LLVM_sim.frame_fields st8 fF eR sR fp /\ slots_from st8 sR eR rs1 /\
      length rs1 = length roots /\ length vs1 = length roots /\
      Forall2 (fun r v => M.get r rho = Some v) roots vs1 /\
      (forall i r, nth_error rs1 i = Some r -> exists q, ptr_off pR (8 * Z.of_nat i) q /\ ptr_to_int r = ptr_to_int q) /\
      (forall a, ptr_to_int pR <= a < ptr_to_int pR + 8 * Z.of_nat (length roots) ->
         exists aid, aid_at st8 a = Some aid /\ access_allowed (ptr_provenance pR) aid = true) /\
      ptr_to_int pR + 8 * Z.of_nat (length roots) < 2^64 /\
      ptr_off tinfo off_fp a_fp /\
      LLVM_sim.mstep st st8 (field_addr tinfo off_fp) /\
      frames_of st8 = push_top ks (frames_of st) /\
      Forall (fun k => IntMaps.lookup (ptr_to_int k) (mem_of st) = None) ks /\
      (forall a, slot_bytes rs1 a \/ LLVM_sim.frame_bytes fF a -> ~ allocd st a).
  Proof.
    intros HI Htl Hroots Henv HnR Hnf.
    set (nr := length roots).
    pose proof HI as (Hhi & Hok0 & Hmem & Hdis & (a_fp & Hafp & Hrfp) & Hss & Hsk & Hroots0).
    pose proof (LLVM_sim.ptr_off_int _ _ _ Hafp) as Eafp.
    assert (Hwfp : writable_word st a_fp)
      by (pose proof Hok0 as (Hf1 & _); apply (Hf1 off_fp a_fp); [simpl; auto 6|exact Hafp]).
    assert (Hafp_al : forall a, ptr_to_int a_fp <= a < ptr_to_int a_fp + 8 -> allocd st a)
      by (intros a Ha; eapply LLVM_sim.writable_word_alloc; eauto).
    (* 1. alloca roots *)
    destruct (instr_alloca_arr_cases ctx va (ssname fresh 1) (N.of_nat nr) st sf stk G)
      as [Hoom1|(st1 & pR & Hrun1 & Hap1)]; [left; exact Hoom1|right].
    set (sf1 := alloca_locals sf (ssname fresh 1) pR).
    assert (Hor1 : orig_runs va stk G [(IId (ssname fresh 1), INSTR_Alloca (DTYPE_Array false (N.of_nat nr) i64) [], [])]
                             st sf st1 sf1).
    { apply orig_runs_one; [split; [apply noflat_ss|intros a []]|cbn; exact I|exact Hrun1]. }
    (* 2. alloca frame *)
    destruct (instr_alloca_frame_cases ctx va (ssname fresh 2) st1 sf1 stk G)
      as [Hoom2|(st2 & pF & Hrun2 & Hap2)]; [left; exists st1, sf1; split; [exact Hor1|exact Hoom2]|right].
    set (sf2 := alloca_locals sf1 (ssname fresh 2) pF).
    assert (Hp1 : pres st st1) by (eapply pres_alloc; [apply pres_refl|exact Hap1]).
    assert (Hp2 : pres st st2) by (eapply pres_alloc; [exact Hp1|exact Hap2]).
    assert (HFfresh : forall a, ptr_to_int pF <= a -> ~ allocd st a).
    { intros a Ha Hal. apply (alloc_post_fresh _ _ _ _ a Hap2 Ha). eapply pres_allocd; eauto. }
    assert (HRfresh : forall a, ptr_to_int pR <= a -> ~ allocd st a) by (intros; eapply alloc_post_fresh; eauto).
    assert (HFend : ptr_to_int pF + 24 <= 2^64) by (apply (alloc_post_end st1 st2 24 pF); [lia|exact Hap2]).
    assert (HRblk : forall a, ptr_to_int pR <= a < ptr_to_int pR + 8 * Z.of_nat nr ->
                     (exists aid, aid_at st1 a = Some aid /\ access_allowed (ptr_provenance pR) aid = true) /\
                     a < ptr_to_int pF).
    { intros a Ha. destruct (alloc_post_allocd _ _ _ _ a Hap1 ltac:(lia)) as (aid & Haid & Hacc).
      split; [exists aid; auto|]. destruct (Z_lt_le_dec a (ptr_to_int pF)) as [Hlt|Hle]; [exact Hlt|].
      exfalso. apply (alloc_post_fresh _ _ _ _ a Hap2 Hle). apply allocd_aid. rewrite Haid. discriminate. }
    assert (HRend : ptr_to_int pR + 8 * Z.of_nat nr < 2^64).
    { destruct nr as [|n] eqn:Enr; [pose proof (ptr_to_int_range pR); lia|].
      destruct (HRblk (ptr_to_int pR + 8 * Z.of_nat (S n) - 1) ltac:(lia)) as [_ Hlt]. lia. }
    (* 3. spill *)
    destruct (roots_vals SV rho env sf st roots Hroots Henv) as (vs1 & ws & Hws & Hvs1 & Hget1).
    assert (Hlen_ws : length ws = nr) by (symmetry; exact (Forall2_length Hws)).
    assert (HfR : RM.find (ssname fresh 1) (stack_vars sf2) = Some (Ptr pR)).
    { unfold sf2, sf1, alloca_locals. rewrite !stack_vars_upd, rfind_add_neq, rfind_add_eq; [reflexivity|].
      intros E. apply ssname_inj in E. lia. }
    assert (HfF : RM.find (ssname fresh 2) (stack_vars sf2) = Some (Ptr pF)).
    { unfold sf2, sf1, alloca_locals. rewrite !stack_vars_upd, rfind_add_eq. reflexivity. }
    assert (Hws2 : Forall2 (fun r w => RM.find (env r) (stack_vars sf2) = Some (I64 w)) roots ws).
    { eapply Forall2_impl; [|exact Hws]. intros r w Hr.
      unfold sf2, sf1, alloca_locals. rewrite !stack_vars_upd, !rfind_add_neq; [exact Hr| |];
        intros E; eapply HnR; symmetry; exact E. }
    assert (Htl2 : RM.find (Name "tinfo") (stack_vars sf2) = Some (Ptr tinfo)).
    { unfold sf2, sf1, alloca_locals. rewrite !stack_vars_upd, !rfind_add_neq; [exact Htl|discriminate|discriminate]. }
    assert (Hslw : slots_ok (fun q _ => writable_word st2 q) pR 0 ws).
    { apply slots_ok_intro. intros k w Hk. cbn [Nat.add].
      assert (Hkl : (k < nr)%nat) by (rewrite <- Hlen_ws; apply nth_error_Some; rewrite Hk; discriminate).
      destruct (LLVM_sim.ptr_off_ex pR (8 * Z.of_nat k)) as [q Hq]; [pose proof (ptr_to_int_range pR); lia|].
      exists q. split; [exact Hq|]. eapply alloc_post_writable_word; [exact Hap2|].
      eapply alloc_word_writable; [exact Hap1|exact Hq|lia|]. rewrite N2Z.inj_mul, nat_N_Z. lia. }
    destruct (slots_ok_ptrs _ _ _ _ Hslw) as (qs & Hqs & Hlq & Wq).
    assert (Hst3 := spill_stores env (ssname fresh 1) (N.of_nat nr) 0 roots ws pR qs sf2 stk G
                      (fun st0 => exp_eval_local st0 sf2 stk G (Some dptr) _ HfR) Hws2
                      ltac:(cbn [Nat.add]; change (length roots) with nr; pose proof (ptr_to_int_range pR); lia) Hqs Hlq).
    destruct (stores_orig va sf2 stk G _ _ st2 Hst3) as (st3 & Hor3 & Hwp3 & Hrd3 & Haid3).
    { apply spill_ok; [apply noflat_ss|exact Hnf]. }
    { exact Wq. }
    { eapply slot_ptrs_disj, Hqs. }
    rewrite map_fst_combine in Hwp3 by exact Hlq.
    assert (Hp3 : pres st st3).
    { eapply pres_writes; [exact Hp2|exact Hwp3|]. intros a Ha. apply Exists_exists in Ha.
      destruct Ha as (q & Hq & Hqa). apply HRfresh. pose proof (slot_ptrs_ge _ _ _ Hqs) as G0.
      rewrite Forall_forall in G0. specialize (G0 q Hq). change (Z.of_nat 0) with 0 in G0. lia. }
    assert (HwF : forall off q, ptr_off pF off q -> 0 <= off -> off + 8 <= 24 -> writable_word st3 q).
    { intros off q Hq H0 H1. destruct Hwp3 as (_ & _ & _ & _ & Hw & _). apply Hw.
      eapply alloc_word_writable; [exact Hap2|exact Hq|exact H0|exact H1]. }
    (* 4. frame.end := &roots[nr] *)
    destruct (LLVM_sim.ptr_off_ex pR (8 * Z.of_nat nr)) as [eP HeP]; [pose proof (ptr_to_int_range pR); lia|].
    assert (Hev4 : exp_eval st3 sf2 stk G (Some dptr) (gepA nr (ssname fresh 1) nr) (Ptr eP)).
    { unfold gepA, locE. eapply exp_eval_gep_arr; [pose proof (ptr_to_int_range pR); lia|apply exp_eval_local, HfR|exact HeP]. }
    assert (HpF0 : ptr_off pF (8 * Z.of_nat 0) pF) by apply LLVM_sim.ptr_off_0.
    assert (HevF0 : forall st0, exp_eval st0 sf2 stk G (Some dptr) (gepF (ssname fresh 2) 0) (Ptr pF)).
    { intros st0. unfold gepF, locE. eapply exp_eval_gep_frame; [lia|apply exp_eval_local, HfF|exact HpF0]. }
    destruct (instr_store_ptr_aid va 0%Z _ _ eP pF st3 sf2 stk G Hev4 (HevF0 st3) (HwF 0 pF HpF0 ltac:(lia) ltac:(lia)))
      as (st4 & eR & Hrun4 & HreR & EeR & PeR & Hwp4 & Haid4).
    assert (Hp4 : pres st st4).
    { eapply pres_write; [exact Hp3|exact Hwp4|]. intros a Ha. apply HFfresh. lia. }
    (* 5. frame.start := &roots[0] *)
    assert (HpR0 : ptr_off pR (8 * Z.of_nat 0) pR) by apply LLVM_sim.ptr_off_0.
    assert (Hev5 : exp_eval st4 sf2 stk G (Some dptr) (gepA nr (ssname fresh 1) 0) (Ptr pR)).
    { unfold gepA, locE. eapply exp_eval_gep_arr; [pose proof (ptr_to_int_range pR); lia|apply exp_eval_local, HfR|exact HpR0]. }
    destruct (LLVM_sim.ptr_off_ex pF 8) as [pF8 HpF8]; [pose proof (ptr_to_int_range pF); lia|].
    assert (HevF8 : forall st0, exp_eval st0 sf2 stk G (Some dptr) (gepF (ssname fresh 2) 1) (Ptr pF8)).
    { intros st0. unfold gepF, locE. eapply exp_eval_gep_frame; [lia|apply exp_eval_local, HfF|exact HpF8]. }
    assert (Hw5 : writable_word st4 pF8) by (apply Hwp4; apply (HwF 8 pF8 HpF8); lia).
    destruct (instr_store_ptr_aid va 0%Z _ _ pR pF8 st4 sf2 stk G Hev5 (HevF8 st4) Hw5)
      as (st5 & sR & Hrun5 & HrsR & EsR & PsR & Hwp5 & Haid5).
    pose proof (LLVM_sim.ptr_off_int _ _ _ HpF8) as EpF8.
    assert (Hp5 : pres st st5).
    { eapply pres_write; [exact Hp4|exact Hwp5|]. intros a Ha. apply HFfresh. lia. }
    (* 6. prev := tinfo->fp *)
    assert (HevT : forall st0 sf0, RM.find (Name "tinfo") (stack_vars sf0) = Some (Ptr tinfo) ->
                     exp_eval st0 sf0 stk G (Some dptr) (gepT 4) (Ptr a_fp)).
    { intros st0 sf0 H. unfold gepT, locE. eapply exp_eval_gep_tinfo; [right; right; left; reflexivity|apply exp_eval_local, H|exact Hafp]. }
    assert (Hrfp5 : reads_ptr st5 a_fp fp).
    { eapply reads_ptr_frame; [exact Hrfp|]. intros a Ha. destruct Hp5 as (_ & H5). apply H5, Hafp_al, Ha. }
    set (sf6 := upd_local_sf sf2 (Maps.add (ssname fresh 3) (Ptr fp) (stack_vars sf2))).
    assert (Hrun6 : runs ctx (denote_instr (IId (ssname fresh 3), INSTR_Load dptr (dptr, gepT 4) [], []) va)
                      (st5, ((sf2, stk), G)) (st5, ((sf6, stk), G)) tt)
      by (apply (instr_load_ptr ctx va _ _ a_fp fp); [apply HevT, Htl2|exact Hrfp5]).
    assert (Hfind6 : forall r, r <> ssname fresh 3 -> RM.find r (stack_vars sf6) = RM.find r (stack_vars sf2)).
    { intros r Hr. unfold sf6. rewrite stack_vars_upd, rfind_add_neq; [reflexivity|]. intros E. apply Hr. symmetry. exact E. }
    assert (Hss3 : ssname fresh 3 <> ssname fresh 2 /\ ssname fresh 3 <> ssname fresh 1).
    { split; intros E; apply ssname_inj in E; lia. }
    (* 7. frame.prev := prev *)
    destruct (LLVM_sim.ptr_off_ex pF 16) as [pF16 HpF16]; [pose proof (ptr_to_int_range pF); lia|].
    pose proof (LLVM_sim.ptr_off_int _ _ _ HpF16) as EpF16.
    assert (HevF16 : forall st0, exp_eval st0 sf6 stk G (Some dptr) (gepF (ssname fresh 2) 2) (Ptr pF16)).
    { intros st0. unfold gepF, locE. eapply exp_eval_gep_frame; [lia|apply exp_eval_local|exact HpF16].
      rewrite Hfind6 by (intros E; apply (proj1 Hss3); symmetry; exact E). exact HfF. }
    assert (HevP : forall st0, exp_eval st0 sf6 stk G (Some dptr) (locE (ssname fresh 3)) (Ptr fp)).
    { intros st0. apply exp_eval_local. unfold sf6. rewrite stack_vars_upd. apply rfind_add_eq. }
    assert (Hw7 : writable_word st5 pF16).
    { apply Hwp5, Hwp4. apply (HwF 16 pF16 HpF16); lia. }
    destruct (instr_store_ptr_aid va 0%Z _ _ fp pF16 st5 sf6 stk G (HevP st5) (HevF16 st5) Hw7)
      as (st7 & prv & Hrun7 & Hrprv & Eprv & Pprv & Hwp7 & Haid7).
    assert (prv = fp).
    { apply LLVM_sim.ptr_ext; [exact Eprv|]. rewrite Pprv. symmetry. eapply reads_ptr_wild; exact Hrfp. }
    subst prv.
    assert (Hp7 : pres st st7).
    { eapply pres_write; [exact Hp5|exact Hwp7|]. intros a Ha. apply HFfresh. lia. }
    (* 8. tinfo->fp := frame *)
    assert (HevF : forall st0, exp_eval st0 sf6 stk G (Some dptr) (locE (ssname fresh 2)) (Ptr pF)).
    { intros st0. apply exp_eval_local. rewrite Hfind6 by (intros E; apply (proj1 Hss3); symmetry; exact E). exact HfF. }
    assert (Htl6 : RM.find (Name "tinfo") (stack_vars sf6) = Some (Ptr tinfo)) by (rewrite Hfind6 by discriminate; exact Htl2).
    assert (Hw8 : writable_word st7 a_fp).
    { eapply writable_word_aid; [exact Hwfp|]. intros a Ha. apply aidp_pres; [exact Hp7|]. apply Hafp_al, Ha. }
    destruct (instr_store_ptr_aid va 0%Z _ _ pF a_fp st7 sf6 stk G (HevF st7) (HevT st7 sf6 Htl6) Hw8)
      as (st8 & fF & Hrun8 & HrfF & EfF & PfF & Hwp8 & Haid8).
    (* the memory after the safepoint set-up *)
    pose proof Hp7 as (Eh7 & Hm7). pose proof Hwp8 as (Eh8 & Ef8 & _ & Hout8 & _ & Hrw8 & Hrp8).
    pose proof Hwp7 as (_ & Ef7 & _ & _ & _ & Hrw7 & Hrp7).
    pose proof Hwp5 as (_ & Ef5 & _ & _ & _ & Hrw5 & Hrp5).
    pose proof Hwp4 as (_ & Ef4 & _ & _ & _ & Hrw4 & Hrp4).
    pose proof Hwp3 as (_ & Ef3 & _).
    assert (Haid28 : aidp st2 st8).
    { eapply aidp_trans; [apply aidp_all, Haid3|]. eapply aidp_trans; [apply aidp_all, Haid4|].
      eapply aidp_trans; [apply aidp_all, Haid5|]. eapply aidp_trans; [apply aidp_all, Haid7|apply aidp_all, Haid8]. }
    assert (Haid18 : aidp st1 st8).
    { eapply aidp_trans; [|exact Haid28]. apply aidp_pres. eapply pres_alloc; [apply pres_refl|exact Hap2]. }
    assert (Hnotafp : forall a, ~ field_addr tinfo off_fp a -> ~ (ptr_to_int a_fp <= a < ptr_to_int a_fp + 8)).
    { intros a Ha H. apply Ha. unfold field_addr. rewrite Eafp in H. exact H. }
    assert (Hd_afp : forall p, (forall a, ptr_to_int p <= a < ptr_to_int p + 8 -> ~ allocd st a) -> disj8 p a_fp).
    { intros p Hp. apply (disj8_of p a_fp (fun a => ~ allocd st a)); [exact Hp|]. intros a Ha Hn. apply Hn, Hafp_al, Ha. }
    assert (Hd_F : forall p q, (forall a, ptr_to_int p <= a < ptr_to_int p + 8 -> a < ptr_to_int pF) ->
                               ptr_to_int pF <= ptr_to_int q -> disj8 p q).
    { intros p q Hp Hq. apply (disj8_of p q (fun a => a < ptr_to_int pF)); [exact Hp|]. intros a Ha. lia. }
    assert (HmF : forall a, ptr_to_int pF <= a -> ~ allocd st a) by exact HFfresh.
    (* mstep *)
    destruct (alloc_post_frames _ _ _ _ Hap1) as (ksR & EfR & HksR).
    destruct (alloc_post_frames _ _ _ _ Hap2) as (ksF & EfrF & HksF).
    assert (Hms : LLVM_sim.mstep st st8 (field_addr tinfo off_fp)).
    { split; [congruence|]. split.
      - intros a Hw Ha. rewrite Hout8 by (apply Hnotafp, Hw). apply Hm7, Ha.
      - split.
        + intros a Ha. rewrite Haid8. apply aidp_pres; [exact Hp7|exact Ha].
        + exists (ksR ++ ksF)%list. split.
          * rewrite Ef8, Ef7, Ef5, Ef4, Ef3, EfrF, EfR. apply LLVM_sim.push_top_app.
          * apply Forall_app. split.
            -- eapply Forall_impl; [|exact HksR]. intros k Hk. destruct (IntMaps.lookup _ _) eqn:E; [|reflexivity].
               exfalso. apply Hk. unfold allocd. rewrite E. discriminate.
            -- eapply Forall_impl; [|exact HksF]. intros k Hk. destruct (IntMaps.lookup _ _) eqn:E; [|reflexivity].
               exfalso. apply Hk. eapply pres_allocd; [exact Hp1|]. unfold allocd. rewrite E. discriminate. }
    (* the frame's fields *)
    assert (HpFbytes : forall a, ptr_to_int pF <= a -> ~ allocd st a) by exact HFfresh.
    assert (HreR8 : reads_ptr st8 pF eR).
    { apply Hrp8; [|apply Hd_afp; intros a Ha; apply HFfresh; lia].
      apply Hrp7; [|unfold disj8; lia]. apply Hrp5; [exact HreR|unfold disj8; lia]. }
    assert (HrsR8 : reads_ptr st8 pF8 sR).
    { apply Hrp8; [|apply Hd_afp; intros a Ha; apply HFfresh; lia]. apply Hrp7; [exact HrsR|unfold disj8; lia]. }
    assert (Hrprv8 : reads_ptr st8 pF16 fp).
    { apply Hrp8; [exact Hrprv|apply Hd_afp; intros a Ha; apply HFfresh; lia]. }
    assert (Hafp_lt : ptr_to_int a_fp < ptr_to_int pF).
    { destruct (Z_lt_le_dec (ptr_to_int a_fp) (ptr_to_int pF)) as [H|H]; [exact H|].
      exfalso. apply (HFfresh (ptr_to_int a_fp) H). apply Hafp_al. lia. }
    assert (Hff : LLVM_sim.frame_fields st8 fF eR sR fp).
    { pose proof (ptr_to_int_range a_fp). split; [lia|]. split.
      { eapply reads_ptr_wild'; [exact HreR8|exact EfF|exact PfF]. }
      split.
      - destruct (LLVM_sim.ptr_off_ex fF 8) as [a Ha]; [lia|]. exists a. split; [exact Ha|].
        eapply reads_ptr_wild'; [exact HrsR8| |].
        + rewrite (LLVM_sim.ptr_off_int _ _ _ Ha). lia.
        + rewrite (LLVM_sim.ptr_off_prov _ _ _ Ha). exact PfF.
      - destruct (LLVM_sim.ptr_off_ex fF 16) as [a Ha]; [lia|]. exists a. split; [exact Ha|].
        eapply reads_ptr_wild'; [exact Hrprv8| |].
        + rewrite (LLVM_sim.ptr_off_int _ _ _ Ha). lia.
        + rewrite (LLVM_sim.ptr_off_prov _ _ _ Ha). exact PfF. }
    (* the root slots *)
    pose proof (LLVM_sim.ptr_off_int _ _ _ HeP) as EeP.
    destruct (slots_build st8 nr sR eR ltac:(lia) ltac:(pose proof (ptr_to_int_range eR); lia))
      as (rs1 & Hsl & Hlrs1 & Hnth1).
    assert (Hrs1 : forall i r, nth_error rs1 i = Some r ->
                     ptr_to_int r = ptr_to_int pR + 8 * Z.of_nat i /\ ptr_provenance r = wildcard_prov).
    { intros i r H. specialize (Hnth1 i r H).
      rewrite (LLVM_sim.ptr_off_int _ _ _ Hnth1), (LLVM_sim.ptr_off_prov _ _ _ Hnth1). split; [lia|exact PsR]. }
    assert (Hlqs : length qs = nr) by lia.
    assert (Hrd8 : Forall2 (reads_word st8) rs1 ws).
    { apply Forall2_of_nth; [lia|]. intros i r w Hr Hw.
      assert (Hi : (i < nr)%nat) by (rewrite <- Hlrs1; apply nth_error_Some; rewrite Hr; discriminate).
      destruct (nth_error qs i) as [q|] eqn:Hq; [|apply nth_error_None in Hq; lia].
      pose proof (slot_ptrs_nth _ _ _ Hqs i q Hq) as Hoq. cbn [Nat.add] in Hoq.
      pose proof (LLVM_sim.ptr_off_int _ _ _ Hoq) as Eq.
      assert (Hrq3 := Forall_combine_nth _ _ _ _ _ _ Hrd3 Hq Hw). cbn in Hrq3.
      assert (Hqb : forall a, ptr_to_int q <= a < ptr_to_int q + 8 -> a < ptr_to_int pF).
      { intros a Ha. apply (HRblk a). lia. }
      assert (Hrq8 : reads_word st8 q w).
      { apply Hrw8; [|apply Hd_afp; intros a Ha; apply HRfresh; lia].
        apply Hrw7; [|apply Hd_F; [exact Hqb|lia]].
        apply Hrw5; [|apply Hd_F; [exact Hqb|lia]].
        apply Hrw4; [exact Hrq3|apply Hd_F; [exact Hqb|lia]]. }
      destruct (Hrs1 i r Hr) as [Er Pr]. eapply reads_word_wild; [exact Hrq8|lia|exact Pr]. }
    (* the new bytes *)
    assert (Hnone : forall a, ~ allocd st a -> IntMaps.lookup a (mem_of st) = None).
    { intros a Ha. destruct (IntMaps.lookup a (mem_of st)) eqn:E; [|reflexivity]. exfalso. apply Ha. unfold allocd. rewrite E. discriminate. }
    assert (Hnh8 : forall a, ~ allocd st a -> ~ in_heap st8 a).
    { intros a Ha Hh. rewrite (in_heap_same _ _ _ (eq_trans Eh8 Eh7)) in Hh. apply Ha. apply (proj1 Hmem a Hh). }
    assert (HslR : forall a, slot_bytes rs1 a -> ptr_to_int pR <= a < ptr_to_int pR + 8 * Z.of_nat nr).
    { intros a (r & Hr & Hra). apply In_nth_error in Hr. destruct Hr as [i Hi].
      assert (Hil : (i < nr)%nat) by (rewrite <- Hlrs1; apply nth_error_Some; rewrite Hi; discriminate).
      destruct (Hrs1 i r Hi) as [Er _]. lia. }
    assert (HfrB : forall a, LLVM_sim.frame_bytes fF a -> ptr_to_int pF <= a < ptr_to_int pF + 24).
    { intros a Ha. unfold LLVM_sim.frame_bytes in Ha. lia. }
    assert (Hfb : forall a, LLVM_sim.frame_bytes fF a ->
                    alloc_nonheap st8 a /\ ~ slot_bytes (rs1 ++ rs) a /\ IntMaps.lookup a (mem_of st) = None).
    { intros a Ha. apply HfrB in Ha. split; [split|split].
      - destruct (alloc_post_allocd _ _ _ _ a Hap2 ltac:(change (Z.of_N 24) with 24; lia)) as (aid & Haid & _).
        apply allocd_aid. rewrite Haid28; [rewrite Haid; discriminate|]. apply allocd_aid. rewrite Haid. discriminate.
      - apply Hnh8, HFfresh. lia.
      - intros (r & Hr & Hra). apply in_app_iff in Hr. destruct Hr as [Hr|Hr].
        + assert (Hs : slot_bytes rs1 a) by (exists r; auto). apply HslR in Hs.
          destruct (HRblk a Hs) as [_ Hlt]. lia.
        + destruct Hsk as (_ & Hsl0). destruct (Hsl0 a (ex_intro _ r (conj Hr Hra))) as [Hal _].
          apply (HFfresh a); [lia|exact Hal].
      - apply Hnone, HFfresh. lia. }
    assert (Hsb : forall a, slot_bytes rs1 a -> alloc_nonheap st8 a /\ IntMaps.lookup a (mem_of st) = None).
    { intros a Ha. apply HslR in Ha. destruct (HRblk a Ha) as ((aid & Haid & _) & _). split; [split|].
      - apply allocd_aid. rewrite Haid18; [rewrite Haid; discriminate|]. apply allocd_aid. rewrite Haid. discriminate.
      - apply Hnh8, HRfresh. lia.
      - apply Hnone, HRfresh. lia. }
    (* the invariant with the new frame *)
    pose proof Hok0 as (_ & _ & alloc & limit & Ha & Hl & _).
    assert (Ha8 : field st8 tinfo off_alloc alloc).
    { eapply LLVM_sim.field_frame; [exact Ha|]. intros a Hra. destruct Hms as (_ & Hms & _). apply Hms.
      - unfold field_addr, off_alloc, off_fp in *. lia.
      - apply (proj1 Hmem). eapply (LLVM_sim.field_addr_in_heap tinfo Htinfo_range st off_alloc); [exact Hok0|simpl; auto|].
        unfold field_addr. lia. }
    assert (Hfp8 : field st8 tinfo off_fp fF) by (exists a_fp; auto).
    assert (HI8 : INV st8 fF (rs1 ++ rs) (vs1 ++ vs)).
    { eapply (LLVM_sim.INV_link cenv fds heap_inv G tinfo Hmut Htinfo_range st st8 _ fp rs vs alloc limit fF eR sR rs1 ws vs1);
        eauto. intros a Hw. right; right; left. exact Hw. }
    (* the run of the code *)
    assert (Esf : la_sf sf fresh pR pF fp = sf6).
    { unfold la_sf, sf6, sf2, sf1, alloca_locals. rewrite !stack_vars_upd, !upd_local_sf_twice. reflexivity. }
    assert (Hor : orig_runs va stk G (la_pre env fresh roots) st sf st8 (la_sf sf fresh pR pF fp)).
    { rewrite Esf. unfold la_pre. cbn zeta.
      econstructor; [split; [apply noflat_ss|intros ? []]|cbn; exact I|exact Hrun1|].
      econstructor; [split; [apply noflat_ss|intros ? []]|cbn; exact I|exact Hrun2|].
      eapply orig_runs_app; [exact Hor3|].
      econstructor; [cbn; repeat split; apply noflat_ss|split; eexists; [exact Hev4|apply HevF0]|exact Hrun4|].
      econstructor; [cbn; repeat split; apply noflat_ss|split; eexists; [exact Hev5|apply HevF8]|exact Hrun5|].
      econstructor; [cbn; repeat split; apply noflat_ss|eexists; apply HevT, Htl2|exact Hrun6|].
      econstructor; [cbn; repeat split; apply noflat_ss|split; eexists; [apply HevP|apply HevF16]|exact Hrun7|].
      econstructor; [cbn; repeat split; first [apply noflat_ss|reflexivity]|split; eexists; [apply HevF|apply HevT, Htl6]|exact Hrun8|].
      constructor. }
    pose proof Hms as (_ & _ & _ & ks' & Efr & Hks').
    exists st8, pR, pF, fF, eR, sR, rs1, vs1, a_fp, ks'.
    split; [exact Hor|]. split; [exact HI8|]. split; [exact Hff|]. split; [exact Hsl|].
    split; [exact Hlrs1|]. split; [rewrite <- (Forall2_length Hget1); reflexivity|]. split; [exact Hget1|].
    split.
    { intros i r Hr. destruct (Hrs1 i r Hr) as [Er _].
      assert (Hil : (i < nr)%nat) by (rewrite <- Hlrs1; apply nth_error_Some; rewrite Hr; discriminate).
      destruct (LLVM_sim.ptr_off_ex pR (8 * Z.of_nat i)) as [q Hq]; [pose proof (ptr_to_int_range pR); lia|].
      exists q. split; [exact Hq|]. rewrite (LLVM_sim.ptr_off_int _ _ _ Hq). exact Er. }
    split.
    { intros a Hra. destruct (HRblk a Hra) as ((aid & Haid & Hacc) & _). exists aid. split; [|exact Hacc].
      rewrite Haid18; [exact Haid|]. apply allocd_aid. rewrite Haid. discriminate. }
    split; [exact HRend|]. split; [exact Hafp|]. split; [exact Hms|].
    split; [exact Efr|]. split; [exact Hks'|].
    intros a [Hs|Hs]; [apply HRfresh, HslR, Hs|apply HFfresh, HfrB, Hs].
  Qed.

  (* ================================================================ *)
  (** ** Helpers for the call and the reload *)

  Lemma env_rel_locals S rho env sf sf' st :
    env_rel S rho env sf st ->
    (forall y, S y -> is_fun fs y = false -> RM.find (env y) (stack_vars sf') = RM.find (env y) (stack_vars sf)) ->
    env_rel S rho env sf' st.
  Proof.
    intros H Hf y Hy. destruct (H y Hy) as (w & Hw & Hc). exists w. split; [exact Hw|].
    destruct (is_fun fs y) eqn:E; [exact Hc|]. destruct Hc as (z & Hz & Hs). exists z. rewrite Hf; auto.
  Qed.

  Lemma env_rel_agree S rho env sf sf' st :
    env_rel S rho env sf st -> Flatten_sem.agree_noflat sf sf' ->
    (forall y, S y -> Flatten_sem.is_flat (env y) = false) -> env_rel S rho env sf' st.
  Proof. intros H Ha Hn. apply env_rel_locals with (sf := sf); [exact H|]. intros y Hy _. apply Ha, Hn, Hy. Qed.

  Lemma mstep_fp_mono st st2 fp rs vs :
    INV st fp rs vs -> LLVM_sim.mstep st st2 (field_addr tinfo off_fp) ->
    heap_bytes_agree_except st st2 (not_object st tinfo) /\ (forall a, nursery st2 tinfo a -> nursery st tinfo a).
  Proof.
    intros (_ & Hok & (Hm1 & _) & _) (_ & Hm & _).
    assert (Hs : forall off q, In off [off_alloc; off_limit] -> field st tinfo off q -> field st2 tinfo off q).
    { intros off q Hoff Hq. eapply LLVM_sim.field_frame; [exact Hq|]. intros a Ha. apply Hm.
      - unfold field_addr. destruct Hoff as [<-|[<-|[]]]; unfold off_alloc, off_limit, off_fp in *; lia.
      - apply Hm1. eapply (LLVM_sim.field_addr_in_heap tinfo Htinfo_range st off); [exact Hok| |unfold field_addr; lia].
        destruct Hoff as [<-|[<-|[]]]; simpl; auto. }
    split.
    - intros a Hh Hn. apply Hm; [|apply Hm1, Hh]. intros Hw. apply Hn. right. unfold field_addr, off_fp in Hw. lia.
    - pose proof Hok as (_ & _ & alloc & limit & Ha & Hl & _).
      intros a (al & li & Hal & Hli & Hr). exists alloc, limit. split; [exact Ha|]. split; [exact Hl|].
      rewrite (LLVM_sim.field_det tinfo st2 off_alloc al alloc Hal (Hs off_alloc alloc (or_introl eq_refl) Ha)) in Hr.
      rewrite (LLVM_sim.field_det tinfo st2 off_limit li limit Hli (Hs off_limit limit (or_intror (or_introl eq_refl)) Hl)) in Hr. exact Hr.
  Qed.

  Lemma frame_fields_keep st st' f e s p rs' vs' :
    INV st f rs' vs' -> LLVM_sim.frame_fields st f e s p -> keeps_stack st st' rs' ->
    LLVM_sim.frame_fields st' f e s p.
  Proof.
    intros (_ & _ & _ & _ & _ & _ & ((frs & Hc & Hfb & Hfs) & _) & _) Hff (_ & _ & Hk & _).
    pose proof Hff as (Hnz & He & (a8 & Ha8 & Hs8) & (a16 & Ha16 & Hp16)).
    inversion Hc as [? H0|? prev frs' _ _ _ E1 E2]; subst; [contradiction|].
    assert (Hb : forall a, ptr_to_int f <= a < ptr_to_int f + 24 ->
                   IntMaps.lookup a (mem_of st') = IntMaps.lookup a (mem_of st)).
    { intros a Ha. apply Hk; [apply (Hfb f (or_introl eq_refl) a Ha)|apply (Hfs f (or_introl eq_refl) a Ha)]. }
    pose proof (LLVM_sim.ptr_off_int _ _ _ Ha8) as E8. pose proof (LLVM_sim.ptr_off_int _ _ _ Ha16) as E16.
    split; [exact Hnz|]. split; [|split].
    - eapply reads_ptr_frame; [exact He|]. intros a Ha. apply Hb. lia.
    - exists a8. split; [exact Ha8|]. eapply reads_ptr_frame; [exact Hs8|]. intros a Ha. apply Hb. lia.
    - exists a16. split; [exact Ha16|]. eapply reads_ptr_frame; [exact Hp16|]. intros a Ha. apply Hb. lia.
  Qed.

  (* ================================================================ *)
  (** ** [la_spec] holds *)

  Lemma la_spec_holds : la_spec.
  Proof.
    intros va x f ft ft' ys e' rho rho' fl f' vs_a xs e_body rho'' v env fresh sf stk st fp rs vs l tmt c K
           Hf Hys Hfd Hset IHb Hok Henv Hxf Hxfree HI Htl.
    set (S := occurs_free (Eletapp x f ft ys e')) in *.
    set (roots := la_roots fs x e').
    set (nr := length roots).
    assert (Hroots : forall r, In r roots -> S r /\ is_fun fs r = false).
    { intros r Hr. apply la_roots_spec in Hr. destruct Hr as (Hfr & Hfv & Hne).
      split; [apply Free_Eletapp2; [intros E; apply Hne; symmetry; exact E|exact Hfv]|exact Hfr]. }
    assert (HnR : forall y k, env y <> ssname fresh k).
    { intros y k E. destruct (Hok y) as [_ [E'|(s & k' & Hs & E')]]; rewrite E' in E.
      - symmetry in E. exact (ssname_not_pos _ _ _ E).
      - apply ssname_inj in E. lia. }
    assert (Hnf : forall y, Flatten_sem.is_flat (env y) = false) by apply (env_ok2_not_flat _ _ _ Hok).
    rewrite ccode_la_code. fold roots. rewrite <- app_assoc. cbn [app].
    destruct (la_pre_run va env fresh roots S rho sf stk st fp rs vs HI Htl Hroots Henv HnR Hnf)
      as [Hoom1|[(st1 & sf1 & Hor1 & Hoom2)|
                 (st8 & pR & pF & fF & eR & sR & rs1 & vs1 & a_fp & ks & Hor & HI8 & Hff & Hsl & Hlrs1 & Hlvs1 &
                  Hget1 & Hrs1 & Hacc & HRend & Hafp & Hms & Hfr8 & Hks8 & Hnew)]].
    { left. unfold la_pre. cbn zeta.
      apply (flat_tail_orig_oom va stk G [] st sf st sf _ c c sf); [constructor| |cbn; exact I|exact Hoom1|apply Pos.le_refl|apply Flatten_sem.agree_except_refl].
      split; [apply noflat_ss|intros ? []]. }
    { left. unfold la_pre. cbn zeta.
      apply (flat_tail_orig_oom va stk G _ st sf st1 sf1 _ c c sf _ tmt K Hor1); [| cbn; exact I|exact Hoom2|apply Pos.le_refl|apply Flatten_sem.agree_except_refl].
      split; [apply noflat_ss|intros ? []]. }
    set (sf8 := la_sf sf fresh pR pF fp) in *.
    destruct (flat_tail_orig va stk G _ st sf st8 sf8 Hor c c sf (la_callI env x f ys :: (la_post fresh roots ++ l)%list)
                tmt K (Pos.le_refl c) (Flatten_sem.agree_except_refl _ _ _))
      as (c8 & sfF8 & Hc8 & Hag8 & E8).
    (* the source environment at the call *)
    assert (Hfind8 : forall r, (forall k, r <> ssname fresh k) -> RM.find r (stack_vars sf8) = RM.find r (stack_vars sf)).
    { intros r Hr. unfold sf8, la_sf. rewrite stack_vars_upd, !rfind_add_neq; [reflexivity|..];
        intros E; eapply Hr; symmetry; exact E. }
    destruct (mstep_fp_mono st st8 fp rs vs HI Hms) as [Hagr8 Hnurs8].
    assert (Henv8 : env_rel S rho env sf8 st8).
    { eapply LLVM_sim.env_rel_mono; [|exact Hagr8|apply Hms|exact Hnurs8].
      apply env_rel_locals with (sf := sf); [exact Henv|]. intros y _ _. apply Hfind8. intros k. apply HnR. }
    assert (Htl8 : LLVM_sim.tinfo_local tinfo sf8).
    { unfold LLVM_sim.tinfo_local. rewrite Hfind8; [exact Htl|]. intros k E. unfold ssname in E. discriminate. }
    destruct (callee_value S (Eletapp x f ft ys e') rho env fresh sf8 stk st8 f rho' fl f' Hok Henv8
                (Free_Eletapp1 f x f ft ys e' (or_introl eq_refl)) Hf)
      as (-> & fpf & p & Hg & Hp & Hevf & Hnff & Hintr).
    destruct (args_eval S (Eletapp x f ft ys e') rho env fresh sf8 stk st8 ys vs_a Hok Henv8
                (fun y Hy => Free_Eletapp1 y x f ft ys e' (or_intror Hy)) Hys)
      as (dvs & Hev & Hst & Hnfa).
    pose proof (find_def_correct _ _ _ _ _ Hfd) as Hin.
    edestruct (Flatten_sem.flat_tail_call ctx va (IId (Raw (Zpos x))) i64 (cexp (gcallee fs env f))
                 (((dptr, EXP_Ident (ID_Local (Name "tinfo"))), []) ::
                  map (fun y => ((i64, cexp (gvar fs env y)), [])) ys) [] [] []
                 (la_post fresh roots ++ l)%list tmt c8 K st8 sf8 sfF8 stk G (Ptr p) (Ptr tinfo :: dvs))
      as (Hc9 & af & args' & sf2F & Hag9 & Hi & _ & Hevf2 & _ & Hevargs2 & Heq9).
    { exact Hnff. }
    { constructor; [apply Flatten_sem.is_flat_Name|]. rewrite Forall_map. exact Hnfa. }
    { exact Hevf. }
    { cbn [map fst]. constructor; [apply exp_eval_local, Htl8|]. rewrite map_map. exact Hev. }
    { eapply Flatten_sem.agree_except_noflat'. exact Hag8. }
    match type of Hc9 with (_ <= ?cc)%positive => set (c9 := cc) in * end.
    assert (Hi' : IntrinsicsDefinitions.intrinsic_exp af = None) by (rewrite Hi; exact Hintr).
    destruct (callee_run f' ft' xs e_body rho' rho'' vs_a dvs st8 sf2F stk fF (rs1 ++ rs) (vs1 ++ vs) v p fpf i64
                Hin Hg Hp Hset Hst IHb HI8)
      as [Hoom|(st9 & z & Hrun9 & Hz & HI9 & Hfr9 & Hk9)].
    { left. rewrite E8, Heq9. apply Flatten_sem.ends_in_oom_bind.
      exact (oom_instr_call ctx va (Raw (Zpos x)) i64 af args' p (Ptr tinfo :: dvs) st8 sf2F stk G Hi' Hevf2 Hevargs2 Hoom). }
    right.
    pose proof (instr_call ctx va (Raw (Zpos x)) i64 af args' p (Ptr tinfo :: dvs) st8 sf2F stk G st9 sf2F stk G (I64 z)
                  Hi' Hevf2 Hevargs2 Hrun9) as Hcall.
    set (sf9 := upd_local_sf sf8 (Maps.add (Raw (Zpos x)) (I64 z) (stack_vars sf8))).
    set (sf9F := upd_local_sf sf2F (Maps.add (Raw (Zpos x)) (I64 z) (stack_vars sf2F))) in Hcall.
    assert (Hag9' : Flatten_sem.agree_except c c9 sf9 sf9F).
    { unfold sf9, sf9F. rewrite !Flatten_sem.upd_add_eq. apply Flatten_sem.agree_except_add.
      - apply Flatten_sem.flat_in_noflat, Flatten_sem.is_flat_pos.
      - eapply (Flatten_sem.agree_except_trans c c8 c8 c9 c c9); [lia|lia|lia|lia|exact Hag8|exact Hag9]. }
    (* the reload *)
    pose proof HI9 as (_ & Hok9 & _ & _ & _ & _ & _ & Hroots9a).
    assert (Hlv : length vs1 = length rs1) by lia.
    destruct (roots_ok_drop st9 rs1 rs vs1 vs Hroots9a Hlv) as (Hroots9 & zs1 & Hrdz & Hstz).
    assert (Hlz : length zs1 = nr) by (rewrite <- (Forall2_length Hrdz); exact Hlrs1).
    assert (Hslots9 : slots_ok (fun q w => reads_word st9 q w) pR 0 zs1).
    { apply slots_ok_intro. intros k w Hk. cbn [Nat.add].
      destruct (nth_error rs1 k) as [r|] eqn:Hr;
        [|apply nth_error_None in Hr; assert (k < nr)%nat by (rewrite <- Hlz; apply nth_error_Some; rewrite Hk; discriminate); lia].
      destruct (Hrs1 k r Hr) as (q & Hq & Eq). exists q. split; [exact Hq|].
      destruct (LLVM_sim.nth_error_Forall2 _ _ _ _ _ Hrdz Hr) as (w' & Hw' & Hrw). rewrite Hk in Hw'. injection Hw' as <-.
      eapply read_reprov; [exact Hrw|symmetry; exact Eq|].
      intros a aid Ha Haid. rewrite sizeof_i64 in Ha.
      assert (Hkl : (k < nr)%nat) by (unfold nr; rewrite <- Hlrs1; apply nth_error_Some; rewrite Hr; discriminate).
      assert (HaR : ptr_to_int pR <= a < ptr_to_int pR + 8 * Z.of_nat nr).
      { rewrite (LLVM_sim.ptr_off_int _ _ _ Hq) in Eq. lia. }
      destruct (Hacc a HaR) as (aid8 & Haid8 & Hacc8).
      assert (Hsl8 : alloc_nonheap st8 a).
      { pose proof HI8 as (_ & _ & _ & _ & _ & _ & (_ & Hsl8) & _). apply Hsl8.
        exists r. split; [apply in_or_app; left; eapply nth_error_In; exact Hr|]. change (Z.of_N 8) with 8 in Ha. lia. }
      destruct Hk9 as (_ & _ & _ & Hk9a). rewrite Hk9a in Haid by exact Hsl8. rewrite Haid8 in Haid.
      injection Haid as <-. rewrite (LLVM_sim.ptr_off_prov _ _ _ Hq). exact Hacc8. }
    assert (HfR9 : RM.find (ssname fresh 1) (stack_vars sf9) = Some (Ptr pR)).
    { unfold sf9, sf8, la_sf. rewrite !stack_vars_upd.
      rewrite rfind_add_neq, rfind_add_neq, rfind_add_neq, rfind_add_eq; [reflexivity|..];
        intros E; try (apply ssname_inj in E; lia). exact (ssname_not_pos _ _ _ (eq_sym E)). }
    assert (Hor10 := reload_orig va fresh (ssname fresh 1) (N.of_nat nr) 0 roots zs1 pR st9 sf9 stk G HfR9 (noflat_ss _ _)
                       ltac:(intros k _ E; apply ssname_inj in E; lia) Hlz
                       ltac:(cbn [Nat.add]; change (length roots) with nr; pose proof (ptr_to_int_range pR); lia) Hslots9).
    set (sf10 := upd_local_sf sf9 (reload_locals (stack_vars sf9) fresh 0 zs1)) in Hor10.
    assert (Hfind10 : forall r, (forall k, r <> ssname fresh (1000 + (0 + k))) ->
                        RM.find r (stack_vars sf10) = RM.find r (stack_vars sf9)).
    { intros r Hr. unfold sf10. rewrite stack_vars_upd. apply reload_locals_other. intros k _ E. apply (Hr k). symmetry. exact E. }
    assert (HnotR : forall k, ssname fresh 3 <> ssname fresh (1000 + (0 + k))) by (intros k E; apply ssname_inj in E; lia).
    assert (HP10 : RM.find (ssname fresh 3) (stack_vars sf10) = Some (Ptr fp)).
    { rewrite Hfind10 by exact HnotR. unfold sf9, sf8, la_sf. rewrite !stack_vars_upd.
      rewrite rfind_add_neq, rfind_add_eq; [reflexivity|]. intros E. exact (ssname_not_pos _ _ _ (eq_sym E)). }
    assert (Htl10 : RM.find (Name "tinfo") (stack_vars sf10) = Some (Ptr tinfo)).
    { rewrite Hfind10 by (intros k E; discriminate). unfold sf9. rewrite stack_vars_upd, rfind_add_neq; [exact Htl8|discriminate]. }
    pose proof Hok9 as (Hf9 & _).
    assert (Hw11 : writable_word st9 a_fp) by (apply (Hf9 off_fp a_fp); [simpl; auto 6|exact Hafp]).
    assert (HevT9 : exp_eval st9 sf10 stk G (Some dptr) (gepT 4) (Ptr a_fp)).
    { unfold gepT, locE. eapply exp_eval_gep_tinfo; [right; right; left; reflexivity|apply exp_eval_local, Htl10|exact Hafp]. }
    assert (HevP10 : exp_eval st9 sf10 stk G (Some dptr) (locE (ssname fresh 3)) (Ptr fp)) by (apply exp_eval_local, HP10).
    destruct (instr_store_ptr_aid va 0%Z _ _ fp a_fp st9 sf10 stk G HevP10 HevT9 Hw11)
      as (st11 & fp' & Hrun11 & Hrfp11 & Efp' & Pfp' & Hwp11 & Haid11).
    assert (fp' = fp).
    { apply LLVM_sim.ptr_ext; [exact Efp'|]. rewrite Pfp'. symmetry.
      pose proof HI as (_ & _ & _ & _ & (a0 & _ & Hr0) & _). eapply reads_ptr_wild; exact Hr0. }
    subst fp'.
    assert (Hor11 : orig_runs va stk G (la_post fresh roots) st9 sf9 st11 sf10).
    { unfold la_post. eapply orig_runs_app; [exact Hor10|].
      econstructor; [cbn; repeat split; first [apply noflat_ss|reflexivity]|split; eexists; [exact HevP10|exact HevT9]|exact Hrun11|].
      constructor. }
    destruct (flat_tail_orig va stk G _ st9 sf9 st11 sf10 Hor11 c c9 sf9F l tmt K ltac:(lia) Hag9')
      as (c11 & sfF11 & Hc11 & Hag11 & E11).
    (* the invariant after unlinking *)
    assert (Hff9 : LLVM_sim.frame_fields st9 fF eR sR fp) by exact (frame_fields_keep st8 st9 fF eR sR fp (rs1 ++ rs)%list (vs1 ++ vs)%list HI8 Hff Hk9).
    destruct (INV_unlink st9 st11 fF eR sR fp rs1 rs vs1 vs a_fp HI9 Hff9 (LLVM_sim.slots_from_state _ _ _ _ _ Hsl)
                Hlv Hafp Hwp11 Haid11 Hrfp11) as (HI11 & Hagr11 & Hnurs11 & Hout11).
    pose proof Hwp11 as (Eh11 & Ef11 & _).
    exists st11, sfF11, c11, ks. split.
    { rewrite E8, Heq9.
      change (interp_mcfg (interp_mrec ctx ?t) ?s) with (Flatten_sem.run ctx t s) in Hcall.
      unfold runs in Hcall. rewrite Hcall, Eqit.bind_ret_l. cbv beta iota. exact E11. }
    split; [exact HI11|].
    (* keeps_stack *)
    pose proof Hms as (Ehm & Hmm & Hma & _).
    assert (HWh : forall a, field_addr tinfo off_fp a -> in_heap st a).
    { intros a Ha. pose proof HI as (_ & Hok0 & _).
      eapply (LLVM_sim.field_addr_in_heap tinfo Htinfo_range st off_fp); [exact Hok0|simpl; auto 6|exact Ha]. }
    assert (Hn8 : forall a, alloc_nonheap st a -> alloc_nonheap st8 a).
    { intros a (Ha & Hnh). split.
      - apply allocd_aid. rewrite Hma by exact Ha. apply allocd_aid, Ha.
      - rewrite (in_heap_same _ _ _ Ehm). exact Hnh. }
    destruct Hk9 as (K1 & K2 & K3 & K4).
    split.
    { split; [|split; [|split]].
      - intros a Ha. apply allocd_aid. rewrite Haid11. apply allocd_aid, K1, Hn8, Ha.
      - intros a Ha. rewrite (in_heap_same _ _ _ Eh11). apply K2, Hn8, Ha.
      - intros a Ha Hs. rewrite Hout11.
        + rewrite K3; [|apply Hn8, Ha|].
          * apply Hmm; [|apply Ha]. intros Hw. apply (proj2 Ha), HWh, Hw.
          * intros (r & Hr & Hra). apply in_app_iff in Hr. destruct Hr as [Hr|Hr].
            -- apply (Hnew a); [left; exists r; auto|apply Ha].
            -- apply Hs. exists r. auto.
        + intros Hw. apply (proj2 Ha), HWh, Hw.
      - intros a Ha. rewrite Haid11, K4 by (apply Hn8, Ha). apply Hma, Ha. }
    split; [rewrite Ef11, Hfr9; exact Hfr8|]. split; [exact Hks8|].
    (* the continuation's environment *)
    assert (Hagn11 : Flatten_sem.agree_noflat sf10 sfF11) by (eapply Flatten_sem.agree_except_noflat'; exact Hag11).
    assert (Hmono : forall w zz, stable_repr st9 w zz -> stable_repr st11 w zz)
      by (intros w zz Hw; eapply LLVM_sim.stable_repr_mono; eauto).
    assert (Henv10 : env_rel (occurs_free e') (M.set x v rho) (la_env fs env fresh x e') sf10 st11).
    { intros y Hy. destruct (Pos.eq_dec y x) as [->|Hne].
      - exists v. rewrite M.gss. split; [reflexivity|]. rewrite Hxf. exists z. split; [|apply Hmono, Hz].
        rewrite la_env_other by (rewrite la_roots_spec; intros (_ & _ & E); apply E; reflexivity).
        destruct (Hok x) as [Hb _]. rewrite (Hb (Bound_Eletapp1 x f ft ys e')).
        rewrite Hfind10 by (intros k E; exact (ssname_not_pos _ _ _ (eq_sym E))).
        unfold sf9. rewrite stack_vars_upd. apply rfind_add_eq.
      - rewrite M.gso by exact Hne. destruct (is_fun fs y) eqn:Ef.
        + destruct (Henv y (Free_Eletapp2 y x f ft ys e' (fun E => Hne (eq_sym E)) Hy)) as (w & Hw & Hc).
          rewrite Ef in Hc. exists w. split; [exact Hw|]. exact Hc.
        + assert (Hyr : In y roots) by (apply la_roots_spec; auto).
          apply In_nth_error in Hyr. destruct Hyr as [i Hiy].
          destruct (LLVM_sim.nth_error_Forall2 _ _ _ _ _ Hget1 Hiy) as (vy & Hvy & Hgy).
          destruct (LLVM_sim.nth_error_Forall2 _ _ _ _ _ Hstz Hvy) as (zi & Hzi & Hsz).
          exists vy. split; [exact Hgy|]. exists zi. split; [|apply Hmono, Hsz].
          rewrite (la_env_root _ _ _ _ _ _ _ Hiy). unfold sf10. rewrite stack_vars_upd.
          replace (1000 + i)%nat with (1000 + (0 + i))%nat by lia. apply reload_locals_nth, Hzi. }
    split.
    { eapply env_rel_agree; [exact Henv10|exact Hagn11|]. intros y _.
      destruct (In_dec Pos.eq_dec y roots) as [Hyin|Hnin].
      - apply In_nth_error in Hyin. destruct Hyin as [i Hiy]. rewrite (la_env_root _ _ _ _ _ _ _ Hiy). apply noflat_ss.
      - rewrite la_env_other by exact Hnin. apply Hnf. }
    eapply LLVM_sim.tinfo_local_noflat; [exact Htl10|exact Hagn11].
  Qed.

  (* ================================================================ *)
  (** ** The [Eletapp] case *)

  Lemma sim_case_letapp_fr rho rho' fl f' vs_a xs e_body rho'' x f ft ft' ys e' v v' :
    M.get f rho = Some (Vfun rho' fl f') ->
    get_list ys rho = Some vs_a ->
    find_def f' fl = Some (ft', xs, e_body) ->
    set_lists xs vs_a (def_funs fl fl rho' rho') = Some rho'' ->
    sim_stmt_fr rho'' e_body v ->
    sim_stmt_fr (M.set x v rho) e' v' ->
    sim_stmt_fr rho (Eletapp x f ft ys e') v'.
  Proof. apply sim_case_letapp_of_la_spec, la_spec_holds. Qed.

  (* ================================================================ *)
  (** ** From [sim_stmt] to [sim_stmt_fr], and the cases in [sim_stmt] form *)

  (** [sim_stmt] implies [sim_stmt_fr]: restrict the SSA environment to the
      live variables ([LLVM_sim_cases_read.env_restrict]).  The bound
      variables of [e] are dead and under their ANF names ([env_ok2]), so
      the translation is unchanged; the live ones keep their names, so
      [env_ok] and [env_rel] hold for the restriction. *)
  Lemma sim_stmt_fr_of_sim_stmt rho e v : sim_stmt rho e v -> sim_stmt_fr rho e v.
  Proof.
    intros H env chunk fresh blks f' B va c st sf stk fp rs vs
           Hbok Hsub Hub Hdis Hok Htr Hbin HI Htl Henv Hroom.
    set (env' := LLVM_sim_cases_read.env_restrict e env).
    assert (Htr' : tr env' chunk e fresh = (blks, f')).
    { rewrite <- Htr. apply (LLVM_sim_cases_read.tr_env_ext go ga prim_of fs).
      unfold LLVM_sim_cases_read.fvbv. intros z [Hz|Hz]; unfold env'.
      - apply LLVM_sim_cases_read.env_restrict_fv, Hz.
      - assert (Hnf : ~ occurs_free e z)
          by (intros Hf; inversion Hdis as [Hd]; apply (Hd z); constructor; assumption).
        rewrite LLVM_sim_cases_read.env_restrict_nfv by exact Hnf. symmetry. apply (Hok z), Hz. }
    assert (Hok' : LLVM_sim.env_ok (occurs_free e) env' fresh).
    { intros y. unfold env'. split.
      - intros Hy. rewrite LLVM_sim_cases_read.env_restrict_fv by exact Hy.
        destruct (Hok y) as [_ [E|(s & k & Hs & E)]]; [left; exact E|right; exists s, k; auto].
      - intros Hy. apply LLVM_sim_cases_read.env_restrict_nfv, Hy. }
    exact (H env' chunk fresh blks f' B va c st sf stk fp rs vs Hbok Hsub Hub Hdis Hok' Htr' Hbin HI Htl
             (LLVM_sim_cases_read.env_rel_restrict _ _ _ _ _ _ _ _ _ Henv) Hroom).
  Qed.

  (** The [Eapp] case, with the premises of [BStep_app]. *)
  Lemma sim_case_app rho' fl f' vs xs e rho'' rho f t ys v :
    M.get f rho = Some (Vfun rho' fl f') ->
    get_list ys rho = Some vs ->
    find_def f' fl = Some (t, xs, e) ->
    set_lists xs vs (def_funs fl fl rho' rho') = Some rho'' ->
    sim_stmt rho'' e v ->
    sim_stmt rho (Eapp f t ys) v.
  Proof.
    intros H1 H2 H3 H4 IH. apply sim_stmt_fr_weaken.
    exact (sim_case_app_fr rho rho' fl f' vs xs e rho'' f t t ys v H1 H2 H3 H4 (sim_stmt_fr_of_sim_stmt _ _ _ IH)).
  Qed.

  (** The [Eletapp] case, with the premises of [BStep_letapp]. *)
  Lemma sim_case_letapp rho' fl f' vs xs e_body e rho'' rho x f t ys v v' :
    M.get f rho = Some (Vfun rho' fl f') ->
    get_list ys rho = Some vs ->
    find_def f' fl = Some (t, xs, e_body) ->
    set_lists xs vs (def_funs fl fl rho' rho') = Some rho'' ->
    sim_stmt rho'' e_body v ->
    sim_stmt (M.set x v rho) e v' ->
    sim_stmt rho (Eletapp x f t ys e) v'.
  Proof.
    intros H1 H2 H3 H4 IHb IHk. apply sim_stmt_fr_weaken.
    exact (sim_case_letapp_fr rho rho' fl f' vs xs e_body rho'' x f t t ys e v v' H1 H2 H3 H4
             (sim_stmt_fr_of_sim_stmt _ _ _ IHb) (sim_stmt_fr_of_sim_stmt _ _ _ IHk)).
  Qed.

End CallCases.
