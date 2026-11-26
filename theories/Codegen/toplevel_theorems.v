(* Top-level theorems for the C code generator *)

From Stdlib Require Import ZArith.ZArith Lists.List Sets.Ensembles micromega.Lia.
From compcert Require Import lib.Coqlib lib.Maps lib.Integers common.AST common.Values
     common.Memory common.Events common.Globalenvs common.Smallstep
     cfrontend.Ctypes cfrontend.Clight Clightdefs.
From CertiRocq.Common Require Import compM Pipeline_utils.
From CertiRocq.LambdaANF Require Import term term_util identifiers Ensembles_util algebra eval
     rel_comp.
From CertiRocq.Codegen Require Import LambdaANF_to_C LambdaANF_to_C_rel LambdaANF_to_C_memory
     LambdaANF_to_C_correct.

Import ListNotations.
Local Open Scope Z_scope.

Section Refinement.

  Context {fuel : Type} {Hf : @fuel_resource fuel} {trace : Type} {Ht : @trace_resource trace}.

  Context (cenv : ctor_env).

  (* The C program *)
  Context (p : Clight.program).

  Local Notation ge := (globalenv p).

  (* Its collector, with the invariant [gc_inv], and its pointer test meet their
     specifications *)
  Context (gc_inv : heap -> mem -> block -> Z -> Prop)
          (Hgc : collector_ok cenv ge gc_inv)
          (Hptr : is_ptr_spec ge).

  (* The thread info at [tb, tofs] is set up in the memory [m] *)
  Context (tb : block) (tofs : Z) (h : heap) (fs : list frame) (m : mem)
          (Htinfo : tinfo_ok cenv ge gc_inv h fs m tb tofs).

  Local Notation tinfo := (Vptr tb (Ptrofs.repr tofs)).

  (* Value refinement: [w] is the layout of [v] in the memory [m']. Functions are not
     compared. *)
  Definition value_ref_C (v : val) (m' : mem) (w : Values.val) : Prop :=
    exists h', repr_val cenv ge (fun _ _ => True) h' m' v w.

  (* The function [id], called with [args] from the memory [m1], returns [w] and the memory
     [m']. [k] is what its caller does next. *)
  Definition call_evaluates (id : ident) (args : list Values.val) (m1 : mem)
             (w : Values.val) (m' : mem) : Prop :=
    exists b fd,
      Genv.find_symbol ge id = Some b /\
      Genv.find_funct_ptr ge b = Some fd /\
      forall k, is_call_cont k ->
                star step2 ge (Callstate fd args k m1) E0 (Returnstate w k m').

  (* The same call makes [n] steps *)
  Definition call_steps (id : ident) (args : list Values.val) (m1 : mem) (n : nat) : Prop :=
    exists b fd,
      Genv.find_symbol ge id = Some b /\
      Genv.find_funct_ptr ge b = Some fd /\
      forall k, is_call_cont k -> exists s, starN step2 ge n (Callstate fd args k m1) E0 s.

  (* The first [n] steps of a longer run *)
  Lemma starN_prefix n j s s' :
    starN step2 ge (n + j) s E0 s' -> exists s1, starN step2 ge n s E0 s1.
  Proof.
    revert s. induction n as [| n IH]; intros s H.
    - exists s. constructor.
    - simpl in H. inversion H as [| ? ? ? t1 s2 t2 ? Hstep Hrest Heq]; subst.
      destruct (Eapp_E0_inv _ _ (eq_sym Heq)) as [-> ->].
      destruct (IH _ Hrest) as [s1 Hs1]. exists s1.
      eapply starN_step; [exact Hstep | exact Hs1 | reflexivity].
  Qed.

  Lemma call_runs_steps id b fd args m1 lb n :
    Genv.find_symbol ge id = Some b ->
    Genv.find_funct_ptr ge b = Some fd ->
    call_runs ge lb m1 fd args ->
    (n <= lb)%nat ->
    call_steps id args m1 n.
  Proof.
    intros Hb Hfd Hruns Hle. exists b, fd. split; [exact Hb |]. split; [exact Hfd |].
    intros k Hk. destruct (Hruns k Hk) as (s & j & Hj & Hs).
    apply (starN_prefix n (j - n) _ s). replace (n + (j - n))%nat with j by lia. exact Hs.
  Qed.

  (** * A program that is compiled alone *)

  (* The function [bodyId] of the C program refines the behavior of [e] *)
  Definition refines_C (e : exp) : Prop :=
    forall (v : val) (c : fuel) (t : trace),
      bstep_fuel cenv (M.empty val) e c (Res v) t ->
      exists (w : Values.val) (m' : mem),
        call_evaluates bodyId [tinfo] m w m' /\
        value_ref_C v m' w.

  (* The call of the function [bodyId] makes [n] steps, for every [n] *)
  Definition diverges_C : Prop :=
    forall n, call_steps bodyId [tinfo] m n.

  Theorem compile_top_correct body_name nparam prims e nenv names header prog :
    closed_exp e ->
    unique_bindings e ->
    (forall x, x \in bound_var e -> (100 <= x)%positive) ->
    no_prims e ->
    compile body_name bodyId [] nparam prims e cenv nenv = Ret (names, header, prog) ->
    make_program bodyId composites (prog_defs prog) = Ret p ->
    refines_C e.
  Proof.
    intros Hcl Hub Hid Hnp Hcomp Hmk.
    destruct (compile_correct (fuel := fuel) (trace := trace)
                              _ _ _ _ _ _ _ _ _ _ _ gc_inv Hcomp Hmk Hid Hub Hcl Hnp
                              (bodyId_ok e Hid) Hgc Hptr)
      as (b & body & Hb & Hbody & _ & Hcorrect).
    intros v c t Hstep.
    destruct (Hcorrect (Res v) c t Hstep 0%nat tb tofs h fs m Htinfo)
      as (w & h' & m' & Hsteps & Hres & _).
    exists w, m'. split.
    - exists b, (Internal body). split; [exact Hb |]. split; [exact Hbody |].
      intros k Hk. destruct (Hsteps k Hk) as (j & _ & Hs). eapply starN_star. exact Hs.
    - exists h'. eapply repr_val_mono; [| apply heap_le_refl | exact Hres]. auto.
  Qed.

  Theorem compile_top_divergence_correct body_name nparam prims e nenv names header prog :
    closed_exp e ->
    unique_bindings e ->
    (forall x, x \in bound_var e -> (100 <= x)%positive) ->
    no_prims e ->
    compile body_name bodyId [] nparam prims e cenv nenv = Ret (names, header, prog) ->
    make_program bodyId composites (prog_defs prog) = Ret p ->
    diverge cenv (M.empty val) e ->
    diverges_C.
  Proof.
    intros Hcl Hub Hid Hnp Hcomp Hmk Hdiv n.
    destruct (compile_correct (fuel := fuel) (trace := trace)
                              _ _ _ _ _ _ _ _ _ _ _ gc_inv Hcomp Hmk Hid Hub Hcl Hnp
                              (bodyId_ok e Hid) Hgc Hptr)
      as (b & body & Hb & Hbody & _ & Hcorrect).
    destruct (fuel_for_steps e n) as [c Hc]. destruct (Hdiv c) as [t Hstep].
    exact (call_runs_steps _ _ _ _ _ _ _ Hb Hbody
                           (Hcorrect OOT c t Hstep 0%nat tb tofs h fs m Htinfo) Hc).
  Qed.

  (** * Two programs that are compiled separately *)

  (* The C program has the structs, the two functions of the runtime, and the functions of
     the programs [prog1] and [prog2] *)
  Definition linked (prog1 prog2 : Clight.program) : Prop :=
    runtime_ok ge /\
    has_functions ge (prog_defs prog1) /\
    has_functions ge (prog_defs prog2).

  (* The functions of the two main expressions *)
  Context (id1 id2 : ident).

  (* The function [id1] returns [w1], and then the function [id2], called with [w1],
     returns [w] and the memory [m'] *)
  Definition link_evaluates (w : Values.val) (m' : mem) : Prop :=
    exists (w1 : Values.val) (m1 : mem),
      call_evaluates id1 [tinfo] m w1 m1 /\
      call_evaluates id2 [tinfo; w1] m1 w m'.

  (* The two functions refine the behavior of the linked programs [e] *)
  Definition refines_link_C (e : exp) : Prop :=
    forall (v : val) (c : fuel) (t : trace),
      bstep_fuel cenv (M.empty val) e c (Res v) t ->
      exists (w : Values.val) (m' : mem),
        link_evaluates w m' /\
        value_ref_C v m' w.

  (* For every [n], the function [id1] makes [n] steps, or it returns and then the function
     [id2] makes [n] steps *)
  Definition diverges_link_C : Prop :=
    forall n,
      call_steps id1 [tinfo] m n \/
      exists (w1 : Values.val) (m1 : mem),
        call_evaluates id1 [tinfo] m w1 m1 /\
        call_steps id2 [tinfo; w1] m1 n.

  (* The second program uses [x], in its main expression only. Its C function takes [x] as
     an argument. *)
  Theorem compile_link_correct lf x e1 e2 name1 name2 nparam prims1 prims2 nenv1 nenv2
          names1 names2 header1 header2 prog1 prog2 :

    closed_exp e1 ->
    unique_bindings e1 ->
    (forall y, y \in bound_var e1 -> (100 <= y)%positive) ->
    no_prims e1 ->

    occurs_free e2 \subset [set x] ->
    closed_fundefs (functions e2) ->
    unique_bindings e2 ->
    (forall y, y \in bound_var e2 -> (100 <= y)%positive) ->
    (100 <= x)%positive ->
    ~ x \in bound_var e2 ->
    no_prims e2 ->

    compile name1 id1 [] nparam prims1 e1 cenv nenv1 = Ret (names1, header1, prog1) ->
    compile name2 id2 [x] nparam prims2 e2 cenv nenv2 = Ret (names2, header2, prog2) ->
    (0 < nparam)%nat ->
    linked prog1 prog2 ->

    refines_link_C (rel_comp.link lf x e1 e2).
  Proof.
    intros Hcl1 Hub1 Hid1 Hnp1 Hfv2 Hfuns2 Hub2 Hid2 Hx Hxb Hnp2 Hcomp1 Hcomp2 Hnparam
           (Hrt & Hhas1 & Hhas2).
    destruct (compile_program_ok _ _ _ _ _ _ _ _ _ _ _ _ Hcomp1 Hrt Hhas1)
      as (tmp1 & Htmp1 & _ & Hprog1).
    destruct (compile_program_ok _ _ _ _ _ _ _ _ _ _ _ _ Hcomp2 Hrt Hhas2)
      as (tmp2 & Htmp2 & Himp2 & Hprog2).
    destruct (link_correct (fuel := fuel) (trace := trace)
                           nparam prims1 prims2 cenv tmp1 tmp2 ge gc_inv lf x e1 e2 id1 id2
                           Hprog1 Hprog2 Htmp1 Htmp2 Hnparam Hid1 Hub1 Hcl1 Hnp1 Hid2 Hub2 Hnp2
                           Hfv2 Hfuns2)
      as (b1 & fn1 & b2 & fn2 & Hb1 & Hfn1 & Hb2 & Hfn2 & Hlink); auto.
    { split; [exact Hx | apply Himp2; now left]. }
    intros v c t Hstep.
    destruct (Hlink (Res v) c t Hstep 0%nat tb tofs h fs m Htinfo)
      as (w1 & m1 & w & h' & m' & Hs1 & Hs2 & Hv & _).
    exists w, m'. split.
    - exists w1, m1. split.
      + exists b1, (Internal fn1). auto.
      + exists b2, (Internal fn2). auto.
    - exists h'. eapply repr_val_mono; [| apply heap_le_refl | exact Hv]. auto.
  Qed.

  Theorem compile_link_divergence_correct lf x e1 e2 name1 name2 nparam prims1 prims2
          nenv1 nenv2 names1 names2 header1 header2 prog1 prog2 :

    closed_exp e1 ->
    unique_bindings e1 ->
    (forall y, y \in bound_var e1 -> (100 <= y)%positive) ->
    no_prims e1 ->

    occurs_free e2 \subset [set x] ->
    closed_fundefs (functions e2) ->
    unique_bindings e2 ->
    (forall y, y \in bound_var e2 -> (100 <= y)%positive) ->
    (100 <= x)%positive ->
    ~ x \in bound_var e2 ->
    no_prims e2 ->

    compile name1 id1 [] nparam prims1 e1 cenv nenv1 = Ret (names1, header1, prog1) ->
    compile name2 id2 [x] nparam prims2 e2 cenv nenv2 = Ret (names2, header2, prog2) ->
    (0 < nparam)%nat ->
    linked prog1 prog2 ->

    diverge cenv (M.empty val) (rel_comp.link lf x e1 e2) ->
    diverges_link_C.
  Proof.
    intros Hcl1 Hub1 Hid1 Hnp1 Hfv2 Hfuns2 Hub2 Hid2 Hx Hxb Hnp2 Hcomp1 Hcomp2 Hnparam
           (Hrt & Hhas1 & Hhas2) Hdiv n.
    destruct (compile_program_ok _ _ _ _ _ _ _ _ _ _ _ _ Hcomp1 Hrt Hhas1)
      as (tmp1 & Htmp1 & _ & Hprog1).
    destruct (compile_program_ok _ _ _ _ _ _ _ _ _ _ _ _ Hcomp2 Hrt Hhas2)
      as (tmp2 & Htmp2 & Himp2 & Hprog2).
    destruct (link_correct (fuel := fuel) (trace := trace)
                           nparam prims1 prims2 cenv tmp1 tmp2 ge gc_inv lf x e1 e2 id1 id2
                           Hprog1 Hprog2 Htmp1 Htmp2 Hnparam Hid1 Hub1 Hcl1 Hnp1 Hid2 Hub2 Hnp2
                           Hfv2 Hfuns2)
      as (b1 & fn1 & b2 & fn2 & Hb1 & Hfn1 & Hb2 & Hfn2 & Hlink); auto.
    { split; [exact Hx | apply Himp2; now left]. }
    destruct (link_fuel_for_steps e1 e2 n) as [c Hc]. destruct (Hdiv c) as [t Hstep].
    destruct (Hlink OOT c t Hstep 0%nat tb tofs h fs m Htinfo)
      as [Hruns | (w1 & m1 & Hs1 & Hruns)].
    - left. exact (call_runs_steps _ _ _ _ _ _ _ Hb1 Hfn1 Hruns Hc).
    - right. exists w1, m1. split.
      + exists b1, (Internal fn1). auto.
      + exact (call_runs_steps _ _ _ _ _ _ _ Hb2 Hfn2 Hruns Hc).
  Qed.

End Refinement.
