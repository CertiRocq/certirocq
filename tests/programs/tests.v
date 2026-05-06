Require Import Corelib.Init.Nat.
From Stdlib Require Import Arith ZArith List String.
Require Import CertiRocq.Tests.lib.vs.
Require Import CertiRocq.Tests.lib.Binom.
Require Import CertiRocq.Tests.lib.Color.
Require Import CertiRocq.Tests.lib.sha256.
Require Import CertiRocq.Tests.lib.coind.
From MetaRocq.Utils Require Import bytestring MRString.
From CertiRocq.Plugin Require Import CertiRocq.

Open Scope string.
Open Scope nat.

Import ListNotations.
Import VeriStar.


(* Demo 1 *)

Definition demo1 := List.app (List.repeat true 500) (List.repeat false 300).

(* Demo 2 *)

Fixpoint repeat2 {A : Type} (x y : A) (n : nat) :=
  match n with
  | 0 => []
  | S n => x :: y :: repeat2 x y n
  end.

Definition demo2 := List.map negb (repeat2 true false 100).

(* List sum *)

Definition list_sum := List.fold_left plus (List.repeat 1 100) 0.

(* VeriStar *)

Definition vs_easy :=
  match vs.main with
  | Valid => true
  | _ => false
  end.

Definition vs_hard :=
  match vs.main_h with
  | Valid => true
  | _ => false
  end.

(* Binom *)

Definition binom := Binom.main.

(* Color *)
Definition color := Color.main.

(* Clos *)

Fixpoint loop_add n (f : Datatypes.unit -> nat) : nat :=
  match n with
  | 0 => f tt
  | S n => f tt + loop_add n f
  end.

Definition clos_loop (u : unit) : nat :=
  (fix list_add k1 k2 k3 l : nat :=
     match l with
     | [] => 0
     | x::xs =>
       (* this gets inlined *)
       let clos z := k1 + k2 + k3 + z in
       (clos x) + list_add k1 k2 k3 xs
     end) 0 0 0 (List.repeat 0 1).

Definition clos := loop_add 1 clos_loop.

(* Rec Clos *)

Definition addxy (x y w : nat) (l : list nat) :=
  let f := (fix aux l :=
     match l with
     | [] => []
     | z :: zs => (z + x + y + w) :: aux zs
     end) in
  f l.

Definition rec_clos := addxy 1 2 3 (List.repeat 0 (100*500)).

(* Rec Clos 2 *)

Definition intxy (x y w : nat) (l : list nat):=
  let f := (fix aux l acc :=
     match l with
     | [] => acc
     | z :: zs => aux zs (z :: x :: y :: w :: acc)
     end) in
  f l [].

Definition rec_clos2 := intxy 1 2 3 (repeat 0 (100*500)).

(* Sha-256 *)

(* From the Coq website *)
Definition sha_input := "Coq is a formal proof management system. It provides a formal language to write mathematical definitions, executable algorithms and theorems together with an environment for semi-interactive development of machine-checked proofs. Typical applications include the certification of properties of programming languages (e.g. the CompCert compiler certification project, the Verified Software Toolchain for verification of C programs, or the Iris framework for concurrent separation logic), the formalization of mathematics (e.g. the full formalization of the Feit-Thompson theorem, or homotopy type theory), and teaching.".

Definition sha_fast := sha256.SHA_256' (sha256.str_to_bytes sha_input).

(* Lazy factorial. Disabled for now until the needed MetaRocq pass is enabled
   and CertiRocq compiles lazy and force. *)

Definition lazy_factorial := string_of_Z (coind.lfact 150).

Eval compute in "Compiling demo1".

CertiRocq Compile --output-suffix "_default" demo1.
CertiRocq Compile -O 0 --output-suffix "_O0" demo1.
CertiRocq Compile --cps --output-suffix "_cps" demo1.

CertiRocq Generate Glue --output "glue_demo1" [ bool, list ].


Eval compute in "Compiling demo2".

CertiRocq Compile --output-suffix "_default" demo2.
CertiRocq Compile -O 0 --output-suffix "_O0" demo2.
CertiRocq Compile --cps --output-suffix "_cps" demo2.

CertiRocq Generate Glue --output "glue_demo2" [ bool, list ].


Eval compute in "Compiling list_sum".

CertiRocq Compile --output-suffix "_default" list_sum.
CertiRocq Compile -O 0 --output-suffix "_O0" list_sum.
CertiRocq Compile --cps --output-suffix "_cps" list_sum.

CertiRocq Generate Glue --output "glue_list_sum" [ nat ].


Eval compute in "Compiling vs_easy".

CertiRocq Compile --output-suffix "_default" vs_easy.
CertiRocq Compile -O 0 --output-suffix "_O0" vs_easy.
CertiRocq Compile --cps --output-suffix "_cps" vs_easy.

CertiRocq Generate Glue --output "glue_vs_easy" [ bool, list, vs.space_atom, vs.clause ].


Eval compute in "Compiling vs_hard".

CertiRocq Compile --output-suffix "_default" vs_hard.
CertiRocq Compile -O 0 --output-suffix "_O0" vs_hard.
(* FIXME: --cps currently overflows the C stack for this larger VeriStar test. *)
(* CertiRocq Compile --cps --output-suffix "_cps" vs_hard. *)

CertiRocq Generate Glue --output "glue_vs_hard" [ bool, vs.space_atom, vs.clause ].


Eval compute in "Compiling binom".

CertiRocq Compile --output-suffix "_default" binom.
CertiRocq Compile -O 0 --output-suffix "_O0" binom.
CertiRocq Compile --cps --output-suffix "_cps" binom.

CertiRocq Generate Glue --output "glue_binom" [ nat ].


Eval compute in "Compiling color".

CertiRocq Compile --output-suffix "_default" color.
CertiRocq Compile -O 0 --output-suffix "_O0" color.
(* FIXME: --cps currently overflows the C stack for this program. *)
(* CertiRocq Compile --cps --output-suffix "_cps" color. *)

CertiRocq Generate Glue --output "glue_color" [ nat, list, prod, Z ].


Eval compute in "Compiling clos".

CertiRocq Compile --output-suffix "_default" clos.
CertiRocq Compile -O 0 --output-suffix "_O0" clos.
CertiRocq Compile --cps --output-suffix "_cps" clos.

CertiRocq Generate Glue --output "glue_clos" [ nat, list ].


Eval compute in "Compiling rec_clos".

CertiRocq Compile --output-suffix "_default" rec_clos.
CertiRocq Compile -O 0 --output-suffix "_O0" rec_clos.
(* FIXME: --cps currently overflows the C stack for this program. *)
(* CertiRocq Compile --cps --output-suffix "_cps" rec_clos. *)

CertiRocq Generate Glue --output "glue_rec_clos" [ nat, list ].


Eval compute in "Compiling rec_clos2".

CertiRocq Compile --output-suffix "_default" rec_clos2.
CertiRocq Compile -O 0 --output-suffix "_O0" rec_clos2.
(* FIXME: --cps currently overflows the C stack for this program. *)
(* CertiRocq Compile --cps --output-suffix "_cps" rec_clos2. *)

CertiRocq Generate Glue --output "glue_rec_clos2" [ nat, list ].

Eval compute in "Compiling sha_fast".

CertiRocq Compile --output-suffix "_default" sha_fast.
CertiRocq Compile -O 0 --output-suffix "_O0" sha_fast.
(* FIXME: --cps currently overflows the C stack for this program. *)
(* CertiRocq Compile --cps --output-suffix "_cps" sha_fast. *)

CertiRocq Generate Glue --output "glue_sha_fast" [ bool, list ].


(* Eval compute in "Compiling lazy factorial (using unsafe passes)".

CertiRocq Compile --allow-unsafe-erasure --output-suffix "_default" lazy_factorial.
CertiRocq Compile --allow-unsafe-erasure -O 0 --output-suffix "_O0" lazy_factorial.
CertiRocq Compile --allow-unsafe-erasure --cps --output-suffix "_cps" lazy_factorial.

CertiRocq Generate Glue --output "glue_lazy_factorial" [ bool, list ]. *)
