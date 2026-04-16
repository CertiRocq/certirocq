From Equations Require Import Equations.
From Stdlib Require Import Uint63 Wf_nat ZArith Lia Arith.
From CertiRocq Require Import CertiRocq.
CertiRocq -help.
Set CertiRocq Build Directory "_build".

(* This warns about uses of primitive operations, but we compile them fine *)
Set Warnings "-primitive-turned-into-axiom".
From Stdlib Require Vector Fin.
Import Vector.VectorNotations.

Program Definition long_vector n : Vector.t nat n :=
  Vector.of_list (List.repeat 1000 n).
  Next Obligation. now rewrite List.repeat_length. Qed.

Definition silent_long_vector :=
 Vector.eqb _ Nat.eqb (long_vector 5000) (long_vector 5000).

(* Time Eval vm_compute in silent_long_vector. (* Blows up *) *)
(* 1.23s *)
(* Set Debug "certirocq-reify". *)
(* Set Debug "backtrace". *)
CertiRocq Eval -time -debug silent_long_vector.
CertiRocq Eval -time -debug silent_long_vector.
CertiRocq Eval -time -debug silent_long_vector.

Definition inspect {A} (a : A) : {b | a = b} :=
  exist _ a eq_refl.
Notation " x 'eqn:' H " := (exist _ x H) (at level 20, only parsing).

Section FactPrim.
  Local Open Scope Z_scope.

  Equations fact (n : int) : int
    by wf (Z.to_nat (to_Z n)) lt :=
  | n with inspect (Uint63.eqb n 0) :=
    | true eqn:_ => 1
    | false eqn:heq => n * fact (pred n).
  Next Obligation.
    pose proof (to_Z_bounded n).
    pose proof (to_Z_bounded (pred n)).
    red.
    eapply Uint63.eqb_false_spec in heq.
    rewrite <- Z2Nat.inj_succ.
    assert (φ (n)%uint63 <> 0). intros hq.
    pose proof (of_to_Z n). rewrite hq in H1. cbn in H1. congruence.
    2:lia.
    rewrite pred_spec in H0 |- *.
    assert (to_Z n - 1 < wB)%Z. lia.
    eapply Z2Nat.inj_le. lia. lia.
    rewrite Z.mod_small. 2:lia. lia.
  Qed.
End FactPrim.
From CertiRocq.Benchmarks Require Import sha256.
From Stdlib Require Import String.
Definition test := "Coq is a formal proof management system. It provides a formal language to write mathematical definitions, executable algorithms and theorems together with an environment for semi-interactive development of machine-checked proofs. Typical applications include the certification of properties of programming languages (e.g. the CompCert compiler certification project, the Verified Software Toolchain for verification of C programs, or the Iris framework for concurrent separation logic), the formalization of mathematics (e.g. the full formalization of the Feit-Thompson theorem, or homotopy type theory), and teaching."%string.

Definition sha := sha256.SHA_256 (sha256.str_to_bytes test).

Definition sha_fast := sha256.SHA_256' (sha256.str_to_bytes test).

Definition sha_fast_noproofs := let x := sha_fast in tt.

Time Eval vm_compute in sha_fast_noproofs.
(* Executed in 0.004 sec *)

CertiRocq Eval -time sha_fast_noproofs.
(* Executed in 0.037175 sec *)

Time CertiRocq Eval sha_fast_noproofs.
(* Finished transaction in 0.02 sec *)

CertiRocq Eval -time sha_fast_noproofs.
(* Executed in 0.045 sec *)
CertiRocq Eval -time sha_fast_noproofs.


From CertiRocq.Benchmarks Require Import Color.

Time Eval vm_compute in Color.main.

From CertiRocq.Benchmarks Require Import vs.
Import VeriStar.

Definition vs_easy :=
  (fix loop (n : nat) (res : veristar_result) :=
     match n with
     | 0%nat =>
       match res with
       | Valid => true
       | _ => false
       end
     | S n =>
       let res := check_entailment example_ent in
       loop n res
     end) 100 Valid.

Definition vs_hard :=
  match vs.main_h with
  | vs.VeriStar.Valid => true
  | _ => false
  end.

(*
(* Blows up *) Time Eval vm_compute in vs_easy.
(* Blows up *) Time Eval vm_compute in vs_hard.
*)

CertiRocq Eval -time vs_hard.
(* Executed in 0.06s *)
CertiRocq Eval -time vs_hard.

(* CertiRocq Eval -time vs_easy. *)
(* Executed in 0.007s *)
