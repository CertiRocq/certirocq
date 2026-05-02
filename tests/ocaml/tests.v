From Stdlib Require Import Arith List String.
Require Import CertiRocq.Tests.lib.vs.
Require Import CertiRocq.Tests.lib.Binom.
Require Import CertiRocq.Tests.lib.Color.
Require Import CertiRocq.Tests.lib.sha256.

From CertiRocq.Plugin Require Import CertiRocq.

Open Scope string.

Import ListNotations.
Import VeriStar.

(* The same tests as CertiRocq tests, but slightly modified
   to suspend computations with unit so we can run multiple times *)


(* Demo 1 *)

Definition demo1  (_ : unit) := List.app (List.repeat true 500) (List.repeat false 300).

(* Demo 2 *)

Fixpoint repeat2 {A : Type} (x y : A) (n : nat) :=
  match n with
  | 0 => []
  | S n => x :: y :: repeat2 x y n
  end.

Definition demo2 (_ : unit) := List.map negb (repeat2 true false 100).

(* List sum *)

Definition list_sum  (_ : unit) := List.fold_left plus (List.repeat 1 100) 0.

(* Veristar *)
Definition example_ent_thunk (_ : unit) := example_ent.

Definition harder_ent_thunk (_ : unit) := vs.harder_ent.

Definition main_h_thunk (_ : unit) := check_entailment (harder_ent_thunk tt).

Definition vs_easy (_ : unit) :=
  (fix loop (n : nat) (res : veristar_result) :=
     match n with
     | 0 =>
       match res with
       | Valid => true
       | _ => false
       end
     | S n =>
       let res := check_entailment (example_ent_thunk tt) in
       loop n res
     end) 100  Valid.

Definition vs_hard (_ : unit) :=
  match main_h_thunk tt with
  | Valid => true
  | _ => false
  end.

(* Binom *)

Definition binom (_ : unit) :=
  let a := Binom.insert_list (Binom.make_list 2000 []) Binom.empty in
  let b := Binom.insert_list (Binom.make_list 2001 []) Binom.empty in
  let c := Binom.merge a b in
  match Binom.delete_max c with
  | Some (k, _) => k
  | None => 0
  end.

(* Color *)
Definition color (_ : unit) := Color.main.

(* Sha *)

(* From the Coq website *)
Definition test := "Coq is a formal proof management system. It provides a formal language to write mathematical definitions, executable algorithms and theorems together with an environment for semi-interactive development of machine-checked proofs. Typical applications include the certification of properties of programming languages (e.g. the CompCert compiler certification project, the Verified Software Toolchain for verification of C programs, or the Iris framework for concurrent separation logic), the formalization of mathematics (e.g. the full formalization of the Feit-Thompson theorem, or homotopy type theory), and teaching.".

Definition sha (_ : unit) := sha256.SHA_256 (sha256.str_to_bytes test).

Definition sha_fast (_ : unit) := sha256.SHA_256' (sha256.str_to_bytes test).

Extraction "demo1" demo1.
Extraction "demo2" demo2.
Extraction "list_sum" list_sum.
Extraction "vs_easy" vs_easy.
Extraction "vs_hard" vs_hard.
Extraction "binom" binom.
(* Not compiled in this OCaml test harness. *)
(* Extraction "color" color. *)
(* Extraction "sha" sha. *)
Extraction "sha_fast" sha_fast.
