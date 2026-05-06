From Stdlib Require Import List Unicode.Utf8 Strings.Byte.
From Stdlib Require Import PArith.
From ExtLib Require Import Monads.
Require Import MetaRocq.Utils.bytestring.
Require Import Common.AstCommon Common.compM.
From MetaRocq.ErasurePlugin Require Import Erasure.
#[global] Hint Resolve Bool.absurd_eq_true Bool.trans_eq_bool f_equal2_nat f_equal_nat : core.
Import MonadNotation ListNotations.

Notation ret := (ExtLib.Structures.Monad.ret).
Notation bind := (ExtLib.Structures.Monad.bind).

Open Scope monad_scope.
Open Scope bs_scope.

(** * Common Interface for composing CertiRocq Transformations *)
(* Author: Anonymized, 2019 *)

Record primitive := mk_primitive {
  prim_name : kername;
  prim_target : string;
  prim_arity : nat;
  prim_alloc : bool }.

Definition primitives := list primitive.

(* Compiler options *)
Record Options :=
  { erasure_config : erasure_configuration;
    inductives_mapping : EProgram.inductives_mapping; (* Mapping for inductives, set by global declarations in the plugin *)
    direct   : bool;  (* direct or CPS code *)
    c_args   : nat;   (* numbers of C arguments *)
    anf_variant : nat;  (* experimental ANF pipeline variant *)

    show_anf : bool;  (* show ANF IR. TODO generalize for other IR's of the compiler,
                       * (perhaps add Show lang instances ?) *)
    o_level  : nat;   (* optimization level *)
    time     : bool;  (* Track timing information *)
    time_anf : bool;  (* Track timing for the ANF pipeline *)
    debug    : bool;  (* Log debug messages *)
    prefix   : string; (* prefix to generated FFI *)

    body_name : string; (* Name of the toplevel function *)
    prims    : primitives;
    (* List of constants that are realized in the target code.
     * kername: constant name, string: name of target primitive *)
  }.


(* Compilation info, such as timing, debug and error messages *)
Record CompInfo :=
  { time_log    : list string;
    log         : list string;
    debug_log   : list string;
  }.

Definition pipelineM := compM Options CompInfo.


(* TODO use more efficient string representation as in cps_show *)

Section Translation.

  Context (Src Dst : Type).


  Definition CertiRocqTrans := Src -> pipelineM Dst.

  (* TODO make something like that work *)
  (* Notation "' e1 ;;; .. ;;; em ;;; en" := *)
  (*   ( fun p => bind ( e1 p ) (  .. ( bind ( em p ) ( fun p => en p ) ) .. )) (at level 110, right associativity). *)

  Definition get_options : pipelineM Options := @compM.ask _ _.

  (* Goal MonadState CompInfo pipelineM. *)
  (* Proof. *)
  (*   exact _. *)

  Definition log_msg (s : string) : pipelineM unit :=
    '(Build_CompInfo tm log dbg) <- get ;;
    put (Build_CompInfo tm (s :: log) dbg).

  Definition debug_msg (s : string) : pipelineM unit :=
    o <- get_options ;;
    if (debug o) then
    '(Build_CompInfo tm log dbg) <- get ;;
     @put Options CompInfo (Build_CompInfo tm log (s :: dbg))
    else ret tt.

  Definition log_time (s : string) : pipelineM unit :=
    '(Build_CompInfo tm log dbg) <- get ;;
    put (Build_CompInfo (s :: tm) log dbg).

  Definition chr_newline : Byte.byte := "010"%byte.
  Definition newline : string := (String.String chr_newline String.EmptyString).

  Definition log_to_string (log : list string) : string :=
    (String.concat newline ("Debug messages" :: (List.rev log)))%bs.

  Definition run_pipeline (o : Options) (src : Src) (m : CertiRocqTrans) : (error Dst * string (* debug *)) :=
    let w := Build_CompInfo [] [] [] in
    let '(res, c_info) := runState (m src) o w in
    (res, log_to_string (debug_log c_info)).

End Translation.

Definition timePhase_opt {A} (o : Options) (s : string) (f : unit -> A) : A :=
  if time o then
    timePhase s f tt
  else f tt.

Definition BuildCertiRocqTrans {Src Trg}
           (name : string)
           (f : Src -> Options -> CompInfo -> compM.error Trg * CompInfo)
  : CertiRocqTrans Src Trg := fun s => State (fun o inf  => timePhase_opt o name (fun _ => f s o inf)).

Definition LiftCertiRocqTrans {Src Trg}
           (name : string) (f : Src -> Trg)
  : CertiRocqTrans Src Trg :=
  fun s =>
    o <- get_options ;;
    ret (timePhase_opt o name (fun _ => f s)).

Definition LiftErrorCertiRocqTrans {Src Trg}
           (name : string) (f : Src -> error Trg)
  : CertiRocqTrans Src Trg :=
  fun s => State (fun o inf  => timePhase_opt o name (fun _ => (f s,  inf))).

Definition LiftErrorLogCertiRocqTrans {Src Trg}
           (name : string) (f : Src -> error Trg * string)
  : CertiRocqTrans Src Trg :=
  fun s =>
    State (fun o inf  =>
             timePhase_opt o name
                           (fun _ =>
                              let (res, dbg) := f s in
                              let inf' := Build_CompInfo (time_log inf) (log inf) (dbg :: debug_log inf) in
                              (res, inf'))).


Section Lang.

  (** ** CertiRocq Language properties *)

  Class Lang (Term : Type) :=
    { Value   : Type ;
      TermWf  : Term -> Prop ;
      BigStep : Term -> Value -> Prop }.

  (** ** Extensions of this Class can be defined as subclasses. *)

  (* Example: Deterministic semantics *)

  Class Deterministic (Term : Type) {HL : Lang Term} :=
    { Det : forall (t : Term) (v1 v2 : Value), BigStep t v1 -> BigStep t v2 -> v1 = v2 }.

  (* Example: a language with a notion of divergence to show divergence
     preservation *)

  Inductive xor (A B : Prop) : Prop :=
  | xor_introl : A → ~ B -> xor A B
  | or_intror : ~ A -> B → xor A B.

  Definition Terminates {Term : Type} {_ : Lang Term} (t : Term) :=
    exists v, BigStep t v.

  Class Div (Term : Type) {HL : Lang Term}  :=
    { Diverges : Term -> Prop ;
      DivSane  : forall (t : Term), xor (Diverges t) (Terminates t) }.

End Lang.

(** ** CertiRocq Corrrectness *)
Section Correctness.

  Context {Src Trg : Type} {Hs : Lang Src} {Hd : Lang Trg}.


  (* Enforces that the translation in total if the input is well-formed and that
     the output is also well-formed *)
  (* Also enforces that the translation is total on WF terms. Should this be a
     problem for any CertiRocq translation we can change the definition of the
     Hoare triple *)
  Definition WfPreserving (trans : CertiRocqTrans Src Trg) :=
    forall src,
      TermWf src ->
      {{ fun r w => (* No preconditions on the state *) True }}
        trans src
      {{ fun r w trg w' => TermWf trg }}.


  Definition obs_eq :=
    @Value Src _ -> @Value Trg _ -> Prop.

  (* Zoe: Use a very simple notion of refinement for now. To internalize the
     transitivity of the obs relation we can use a "observation question" a la
     Abhishek's classes. However, this is not required for linking (a la
     SepCompCert) or to be able to observe functions (for this compilation
     should commute with function application, and it doesn't have to be part of
     the value refinement) *)

  Definition ForwardSim (R : obs_eq) (src : Src) (trg : Trg) :=
    forall v_src, BigStep src v_src ->
             exists v_trg, BigStep trg v_trg /\ R v_src v_trg.


  Definition SemPreserving (R : obs_eq) (trans : CertiRocqTrans Src Trg) :=
    forall src,
      TermWf src ->
      {{ fun r w => (* No preconditions on the state *) True }}
        trans src
      {{ fun r w trg w' => ForwardSim R src trg }}.


  Class TransWfPreserving (trans : CertiRocqTrans Src Trg) :=
    { trans_WfPreserving : WfPreserving trans; }.

  Class TransSemPreserving (trans : CertiRocqTrans Src Trg) (R : obs_eq) :=
    { trans_SemPreserving : SemPreserving R trans }.

End Correctness.

Arguments obs_eq _ _ {_ _}.

Section Composition.

  Context { Src Int Trg : Type }
          { Hs : Lang Src } { Hi : Lang Int } { Hd : Lang Trg }.

  Definition compose {A B C : Type} (R1 : A -> B -> Prop) (R2 : B -> C -> Prop) : A -> C -> Prop :=
    fun a c => exists b, R1 a b /\ R2 b c.

  Definition inclusion {A B : Type} (R1 : A -> B -> Prop) (R2 : A -> B -> Prop) : Prop :=
    forall a b, R1 a b -> R2 a b.

  Lemma ForwardSim_compose R1 R2 (src : Src) (int : Int) (trg : Trg):
    ForwardSim R1 src int ->
    ForwardSim R2 int trg →
    ForwardSim (compose R1 R2) src trg.
  Proof.
    unfold ForwardSim. intros H1 H2 v1 Hs1.
    edestruct H1 as [v2 [Hs2 Heq2]]. eassumption.
    edestruct H2 as [v3 [Hs3 Heq3]]. eassumption.
    eexists. split; eauto. eexists; split; eauto.
  Qed.

  Instance TransWfPreserving_compose
           (trans1 : CertiRocqTrans Src Int)
           {Ht1 : TransWfPreserving trans1}
           (trans2 : CertiRocqTrans Int Trg)
           {Ht2 : TransWfPreserving trans2}
    : TransWfPreserving (fun (s : Src) => bind (trans1 s) (fun (i : Int) => trans2 i)).
  Proof.
    destruct Ht1 as [Hwf1]. destruct Ht2 as [Hwf2].
    constructor.
    unfold WfPreserving. intros src Hwfs.
    eapply bind_triple. eapply Hwf1. eassumption.
    intros int w. simpl.
    eapply pre_state_irrelevant. intros Hwfi.
    eauto.
  Qed.

  Instance TransSemPreserving_compose
           (trans1 : CertiRocqTrans Src Int) (R1 : obs_eq Src Int)
           {Hwf1 : TransWfPreserving trans1} {Ht1 : TransSemPreserving trans1 R1}
           (trans2 : CertiRocqTrans Int Trg) (R2 : obs_eq Int Trg)
           {Ht2 : TransSemPreserving trans2 R2}
    : TransSemPreserving (fun (s : Src) => bind (trans1 s) (fun (i : Int) => trans2 i)) (compose R1 R2).
  Proof.
    destruct Ht1 as [Hcor1]. destruct Ht2 as [Hcor2]. destruct Hwf1 as [Hwf1].
    constructor.
    unfold SemPreserving. intros src Hwfs.
    eapply bind_triple.
    * eapply post_conj. eapply Hwf1. eassumption.
      eapply Hcor1. eassumption.
    * intros int w.
      simpl.
      eapply pre_state_irrelevant. intros [Hwfi Hcori].
      eapply post_weakening; [| now eapply Hcor2; eauto ].
      simpl. intros r w' trg w'' _ Hf1.
      eapply ForwardSim_compose; eauto.
  Qed.


  (* Zoe : With [TransSemPreserving_compose] we will get that that pipeline is
     correct w.r.t to the composition of the intermediate relations. Then we
     prove that the composition of the intermediate relations implies the
     end-to-end relation and use [TransCorrect_subsumption] to derive the
     correctness theorem *)

End Composition.

Section Commutation.

  Context (Src Trg : Type) {Hs : Lang Src} {Hd : Lang Trg}
          (op_src : Src -> Src -> Src) (op_trg : Trg -> Trg -> Trg).

  (* Translation commutes with a term operator *)

  (* Zoe: Only require the readable part of the state to be equal. Intuition:
     the writable part only helps threading comp info but doesn't change the translation *)

  Definition Commutes (trans : CertiRocqTrans Src Trg) :=
    forall r src1 src2 trg1 trg2,
      TermWf src1 -> TermWf src2 ->
      {{ fun r' w' => r = r' }} trans src1 {{ fun r w trg w' => trg = trg1 }} ->
      {{ fun r' w' => r = r' }} trans src2 {{ fun r w trg w' => trg = trg2 }} ->
      {{ fun r' w' => r = r' }} trans (op_src src1 src2) {{ fun r w trg w' => trg = op_trg trg1 trg2 }}.

  (* A relation is compositional wrt linking *)
  Definition Compositional (R : Src -> Prop) :=
    forall src1 src2,
      R src1 -> R src2 -> R (op_src src1 src2).

  (* Level A correctness as per SepCompCert terminology, that is to link
     a program with an other program compiled with exactly the same pipeline *)
  Definition ForwardSimLink (R : obs_eq Src Trg) (src1 src2 : Src) (trg1 trg2 : Trg) :=
    ForwardSim R (op_src src1 src2) (op_trg trg1 trg2).

  (* A CertiRocq translation has "Level A correctness"  *)
  Definition SepCompSemPreserving (R : obs_eq Src Trg) (trans : CertiRocqTrans Src Trg) :=
    forall src1 src2,
      TermWf src1 -> TermWf src2 ->
      (* This can be relaxed, not all components of the state are relevant *)
      {{{ fun s1 s2 => s1 = s2 }}}
        trans src1 | trans src2
      {{{ fun s1' s2' trg1 trg2 => ForwardSimLink R src1 src2 trg1 trg2 }}}.


  (* If a CertiRocqTrans is [Correct] and [Commutative] for the linking operator
     then separate compilation is also correct. *)
  Lemma Commutes_implies_SepCompSemPreserving (Rel : obs_eq Src Trg) (trans : CertiRocqTrans Src Trg)
        {Hwf : TransWfPreserving trans}
        {Hc : TransSemPreserving trans Rel} : (* If the translation is correct *)
    Compositional TermWf -> (* TermWf is compositional *)
    Commutes trans ->
    SepCompSemPreserving Rel trans.
  Proof.
    destruct Hwf as [Hwf]; destruct Hc as [Hsem]. intros Hwf12 Hcom.
    unfold WfPreserving, SemPreserving, Commutes, SepCompSemPreserving in *.
    intros s1 s2 Hwf1 Hwf2. specialize (Hwf12 _ _ Hwf1 Hwf2).
    assert (Hwf' := Hwf). assert (Hsem' := Hsem).
    specialize (Hsem' (op_src s1 s2) Hwf12).

    eapply bitriple_pre_eq_state_l. intros st1 st2 Heq; subst.

    specialize (Hwf s1 Hwf1). specialize (Hwf' s2 Hwf2).
    destruct st2 as [r1 w1].
    edestruct (triple_concretize _ _ _ Hwf r1 w1) as [t1 [wf1 [Ht1 Hp1]]]. now intuition.
    edestruct (triple_concretize _ _ _ Hwf' r1 w1) as [t2 [wf2 [Ht2 Hp2]]]. now intuition.


    (* assert (Hls : {{λ (r' : Options) (w' : CompInfo), r1 = r' }} trans (op_src s1 s2) *)
    (*               {{λ (_ : Options) (_ : CompInfo) (trg : Trg) (_ : CompInfo), trg = op_trg t1 t2}} ). *)
    (* { eapply Hcom; eauto.  *)
    (*   eapply triple_consequence. eassumption. simpl. now intuition. now intuition. *)
    (*   eapply triple_consequence. eassumption. now intuition. now intuition. } *)

    (* eapply triple_to_bitriple. *)

    (* eapply triple_consequence. exact Ht1. *)
    (* simpl. intros. inversion H; subst. split; congruence. *)
    (* simpl. intros ? ? ? ? [? ?] [? [? [? ?]]]; subst. split; reflexivity. *)

    (* eapply triple_consequence. exact Ht2. *)
    (* simpl. intros. inversion H; subst. split; congruence. *)
    (* simpl. intros ? ? ? ? [? ?] [? [? [? ?]]]; subst. split; reflexivity. *)

    (* eapply post_conj in Hls; [| eapply pre_strenghtening; [| eapply Hsem' ]; intuition ]. simpl in *.  *)
    (* edestruct (triple_concretize _ _ _ Hls r1 w1) as [t12 [wf12 [Ht12 Hp12]]]. now intuition.     *)
    (* simpl in *. destruct Hp12 as [Hsim Heq]. *)
    (* unfold ForwardSimLink, ForwardSim in *. setoid_rewrite <- Heq. eassumption. *)
  Abort.

End Commutation.


Section Linking.

  (*  A language with a link operator *)
  Class Linkable (Term : Type) {HL : Lang Term} :=
    { Link : Term -> Term -> Term }.

  Context {Src Trg Int : Type} {Hs : Lang Src} {Hd : Lang Trg}
          {Hsl : Linkable Src} {Hdl : Linkable Trg}.


  (* A Linkable language with level A correctness *)
  Class LinkableCorrectA (trans : CertiRocqTrans Src Trg) (R : obs_eq Src Trg) :=
    { trans_LinkSemPreserving : SepCompSemPreserving Src Trg Link Link R trans }.

  Class LinkableCompositional (trans : CertiRocqTrans Src Trg) :=
    { WfCompositional : Compositional Src Link TermWf;
      TransCommutes   : Commutes Src Trg Link Link trans }.

End Linking.

Section ComposeLinking.

  Context (Src Trg Int : Type) {Hs : Lang Src} {Hd : Lang Trg} {Hi : Lang Int}
          {Hsl : Linkable Src} {Hdl : Linkable Trg} {Hil : Linkable Int}.

  (* To prove linking correctness end to end, we can either
     1. prove it for each phase and compose at the linking theorem
        level (this most likely doesn't make much sense because
        we use Compositionality to derive it for each translation)
     2. prove Compositionality for each phase and compose these proofs
        to derive the linking theorem *)


  Instance LinkableCorrect_compose
           (trans1 : CertiRocqTrans Src Int) (R1 : obs_eq Src Int)
           {Hc1 : TransWfPreserving trans1}
           {Ht1 : LinkableCorrectA trans1 R1}
           (trans2 : CertiRocqTrans Int Trg) (R2 : obs_eq Int Trg)
           {Hc2 : TransWfPreserving trans2}
           {Ht2 : LinkableCorrectA trans2 R2}
    : LinkableCorrectA (fun (s : Src) => bind (trans1 s) (fun (i : Int) => trans2 i)) (compose R1 R2).
  Proof.
    (* TODO fill in if needed *)
  Abort.


  Instance Compositional_compose
           (trans1 : CertiRocqTrans Src Int)
           {Hwf1 : TransWfPreserving trans1}
           {Hc1 : LinkableCompositional trans1}
           (trans2 : CertiRocqTrans Int Trg)
           {Hwf2 : TransWfPreserving trans2}
           {Hc2 : LinkableCompositional trans2}
    : LinkableCompositional (fun (s : Src) => bind (trans1 s) (fun (i : Int) => trans2 i)).
  Proof.
    destruct Hwf1 as [Hwf1]. destruct Hwf2 as [Hwf2].
    destruct Hc1 as [Hc1 Htc1]. destruct Hc2 as [Hc2 Htc2].
    constructor.
    - eassumption.
    - unfold Commutes in *.
      intros r w s1 s2 t1 t2 Hw1 Hw2 Ht1 Ht2.
      assert (Hwf1' := Hwf1). assert (Hwf2' := Hwf2).

      (* specialize (Hwf1 s1 Hw1). specialize (Hwf1' s2 Hw2). *)
      (* edestruct (triple_concretize _ _ _ Hwf1 r w) as [i1 [wf1 [Hi1 Hp1]]]. now intuition. *)
      (* edestruct (triple_concretize _ _ _ Hwf1' r w) as [i2 [wf2 [Hi2 Hp2]]]. now intuition. *)

      (* assert (Hl1 : {{λ (r' : Options) (w' : CompInfo), r = r' ∧ w = w'}}  *)
      (*                 trans1 (Link s1 s2) *)
      (*               {{λ (_ : Options) (_ : CompInfo) (trg : Int) (_ : CompInfo), trg = Link i1 i2}}). *)
      (* { eapply Htc1. eassumption. eassumption. *)
      (*   eapply post_weakening; [| eassumption ]. now intuition. *)
      (*   eapply post_weakening; [| eassumption ]. now intuition. } *)


      (* eapply bind_triple. eassumption. *)

      (* simpl.  *)
      (* intros x _. eapply pre_eq_state_l. intros r1 w1 Heq; subst. *)

      (* specialize (Hwf2 i1 Hp1). specialize (Hwf2' i2 Hp2). *)
      (* edestruct (triple_concretize _ _ _ Hwf2 r w) as [t1' [wft1 [Ht1' Ht1'']]]. now intuition. *)
      (* edestruct (triple_concretize _ _ _ Hwf2' r w) as [t2' [wft2 [Ht2' Ht2'']]]. now intuition. *)


      (* eapply Htc2; eauto.  *)
      (* specialize (Hwf1 s1 Hw1). specialize (Hwf2 s2 Hw2). *)

      (* edestruct (triple_concretize _ _ _ Hwf1 r w) as [i1 [wf1 [Hi1 Hp1]]]. now intuition. *)
      (* edestruct (triple_concretize _ _ _ Hwf2 r w) as [i2 [wf2 [Hi2 Hp2]]]. now intuition. *)

      (* edestruct (triple_concretize _ _ _ Hwf' r1 w1) as [t2 [wf2 [Ht2 Hp2]]]. now intuition. *)


      (* specialize (Htc1 r w s1 s2 t1 t2 Hw1 Hw2). *)
  Abort.

End ComposeLinking.
