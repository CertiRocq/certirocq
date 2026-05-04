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

CertiRocq Compile -O 1 -ext "_opt" demo1.
CertiRocq Compile -config 1 -O 1 -ext "_opt1" demo1.
CertiRocq Compile -config 2 -O 1 -ext "_opt2" demo1.
CertiRocq Compile -config 3 -O 1 -ext "_opt3" demo1.
CertiRocq Compile -config 4 -O 1 -ext "_opt4" demo1.
CertiRocq Compile -config 5 -O 1 -ext "_opt5" demo1.

CertiRocq Generate Glue -file "glue_demo1" [ bool, list ].


Eval compute in "Compiling demo2".

CertiRocq Compile -O 1 -ext "_opt" demo2.
CertiRocq Compile -config 1 -O 1 -ext "_opt1" demo2.
CertiRocq Compile -config 2 -O 1 -ext "_opt2" demo2.
CertiRocq Compile -config 3 -O 1 -ext "_opt3" demo2.
CertiRocq Compile -config 4 -O 1 -ext "_opt4" demo2.
CertiRocq Compile -config 5 -O 1 -ext "_opt5" demo2.

CertiRocq Generate Glue -file "glue_demo2" [ bool, list ].


Eval compute in "Compiling list_sum".

CertiRocq Compile -O 1 -ext "_opt" list_sum.
CertiRocq Compile -config 1 -O 1 -ext "_opt1" list_sum.
CertiRocq Compile -config 2 -O 1 -ext "_opt2" list_sum.
CertiRocq Compile -config 3 -O 1 -ext "_opt3" list_sum.
CertiRocq Compile -config 4 -O 1 -ext "_opt4" list_sum.
CertiRocq Compile -config 5 -O 1 -ext "_opt5" list_sum.

CertiRocq Generate Glue -file "glue_list_sum" [ nat ].


Eval compute in "Compiling vs_easy".

CertiRocq Compile -O 1 -ext "_opt" vs_easy.
CertiRocq Compile -config 1 -O 1 -ext "_opt1" vs_easy.
CertiRocq Compile -config 2 -O 1 -ext "_opt2" vs_easy.
CertiRocq Compile -config 3 -O 1 -ext "_opt3" vs_easy.
CertiRocq Compile -config 4 -O 1 -ext "_opt4" vs_easy.
CertiRocq Compile -config 5 -O 1 -ext "_opt5" vs_easy.

CertiRocq Generate Glue -file "glue_vs_easy" [ bool, list, vs.space_atom, vs.clause ].


Eval compute in "Compiling vs_hard".

CertiRocq Compile -O 1 -ext "_opt" vs_hard.
CertiRocq Compile -config 1 -O 1 -ext "_opt1" vs_hard.
CertiRocq Compile -config 2 -O 1 -ext "_opt2" vs_hard.
CertiRocq Compile -config 3 -O 1 -ext "_opt3" vs_hard.
CertiRocq Compile -config 4 -O 1 -ext "_opt4" vs_hard.
CertiRocq Compile -config 5 -O 1 -ext "_opt5" vs_hard.

CertiRocq Generate Glue -file "glue_vs_hard" [ bool, vs.space_atom, vs.clause ].


Eval compute in "Compiling binom".

CertiRocq Compile -O 1 -ext "_opt" binom.
CertiRocq Compile -config 1 -O 1 -ext "_opt1" binom.
CertiRocq Compile -config 2 -O 1 -ext "_opt2" binom.
CertiRocq Compile -config 3 -O 1 -ext "_opt3" binom.
CertiRocq Compile -config 4 -O 1 -ext "_opt4" binom.
CertiRocq Compile -config 5 -O 1 -ext "_opt5" binom.

CertiRocq Generate Glue -file "glue_binom" [ nat ].


Eval compute in "Compiling color".

CertiRocq Compile -O 1 -ext "_opt" color.
CertiRocq Compile -config 1 -O 1 -ext "_opt1" color.
CertiRocq Compile -config 2 -O 1 -ext "_opt2" color.
CertiRocq Compile -config 3 -O 1 -ext "_opt3" color.
CertiRocq Compile -config 4 -O 1 -ext "_opt4" color.
CertiRocq Compile -config 5 -O 1 -ext "_opt5" color.

CertiRocq Generate Glue -file "glue_color" [ nat, list, prod, Z ].


Eval compute in "Compiling clos".

CertiRocq Compile -O 1 -ext "_opt" clos.
CertiRocq Compile -config 1 -O 1 -ext "_opt1" clos.
CertiRocq Compile -config 2 -O 1 -ext "_opt2" clos.
CertiRocq Compile -config 3 -O 1 -ext "_opt3" clos.
CertiRocq Compile -config 4 -O 1 -ext "_opt4" clos.
CertiRocq Compile -config 5 -O 1 -ext "_opt5" clos.

CertiRocq Generate Glue -file "glue_clos" [ nat, list ].


Eval compute in "Compiling rec_clos".

CertiRocq Compile -O 1 -ext "_opt" rec_clos.
CertiRocq Compile -config 1 -O 1 -ext "_opt1" rec_clos.
CertiRocq Compile -config 2 -O 1 -ext "_opt2" rec_clos.
CertiRocq Compile -config 3 -O 1 -ext "_opt3" rec_clos.
CertiRocq Compile -config 4 -O 1 -ext "_opt4" rec_clos.
CertiRocq Compile -config 5 -O 1 -ext "_opt5" rec_clos.

CertiRocq Generate Glue -file "glue_rec_clos" [ nat, list ].


Eval compute in "Compiling rec_clos2".

CertiRocq Compile -O 1 -ext "_opt" rec_clos2.
CertiRocq Compile -config 1 -O 1 -ext "_opt1" rec_clos2.
CertiRocq Compile -config 2 -O 1 -ext "_opt2" rec_clos2.
CertiRocq Compile -config 3 -O 1 -ext "_opt3" rec_clos2.
CertiRocq Compile -config 4 -O 1 -ext "_opt4" rec_clos2.
CertiRocq Compile -config 5 -O 1 -ext "_opt5" rec_clos2.

CertiRocq Generate Glue -file "glue_rec_clos2" [ nat, list ].

Eval compute in "Compiling sha_fast".

CertiRocq Compile -O 1 -ext "_opt" sha_fast.
CertiRocq Compile -config 1 -O 1 -ext "_opt1" sha_fast.
CertiRocq Compile -config 2 -O 1 -ext "_opt2" sha_fast.
CertiRocq Compile -config 3 -O 1 -ext "_opt3" sha_fast.
CertiRocq Compile -config 4 -O 1 -ext "_opt4" sha_fast.
CertiRocq Compile -config 5 -O 1 -ext "_opt5" sha_fast.

CertiRocq Generate Glue -file "glue_sha_fast" [ bool, list ].


(* Eval compute in "Compiling lazy factorial (using unsafe passes)".

CertiRocq Compile -unsafe-erasure -O 1 -ext "_opt" lazy_factorial.
CertiRocq Compile -unsafe-erasure -config 1 -O 1 -ext "_opt1" lazy_factorial.
CertiRocq Compile -unsafe-erasure -config 2 -O 1 -ext "_opt2" lazy_factorial.
CertiRocq Compile -unsafe-erasure -config 3 -O 1 -ext "_opt3" lazy_factorial.
CertiRocq Compile -unsafe-erasure -config 4 -O 1 -ext "_opt4" lazy_factorial.
CertiRocq Compile -unsafe-erasure -config 5 -O 1 -ext "_opt5" lazy_factorial.

CertiRocq Generate Glue -file "glue_lazy_factorial" [ bool, list ]. *)
