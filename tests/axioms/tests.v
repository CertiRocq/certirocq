From CertiRocq.Plugin Require Import CertiRocq.

From Stdlib Require Import Arith PArith List String Ascii.
Require Import ExtLib.Data.String.

Import ListNotations.

(* Example 1: printing axioms *)

Axiom (print_nat : nat -> unit).
Axiom (print_str : string -> unit).
Axiom (new_line : unit -> unit).

Definition print_list (l : list nat) : unit :=
  let aux :=
      fix aux l :=
        match l with
        | [] => tt
        | [x] => print_nat x
        | x :: l =>
          let _ := print_nat x in
          let _ := print_str ";" in
          aux l
        end in
  let _ := print_str "[" in
  let _ := aux l in
  let _ := print_str "]" in new_line tt.


Definition print_lst := print_list [1;2;3;4;5].

CertiRocq Compile print_lst
Extract Constants [ print_nat => "print_gallina_nat", print_str => "print_gallina_string", new_line => "print_new_line" ]
Include [ "print.h" ].

(* Example 2: int 63 *)

Axiom (int63 : Type).
Axiom (add_int63 : int63 -> int63 -> int63).
Axiom (minus : int63 -> int63 -> int63).
Axiom (mul : int63 -> int63 -> int63).
Axiom (print_int63 : int63 -> unit).

Axiom (zero_int63 : int63).
Axiom (one_int63 : int63).


Fixpoint fib_aux (n : nat) (prev0 prev1 : int63) :=
  match n with
  | 0 => prev0
  | 1 => prev1
  | S n => fib_aux n prev1 (add_int63 prev0 prev1)
  end.

Definition fib (n : nat) := fib_aux n zero_int63 one_int63.

Definition fibn : unit :=
  let _ := print_int63 (fib 11) in
  new_line tt.

CertiRocq Compile fibn
Extract Constants [ add_int63 => "add_int63", zero_int63 => "zero_int63", one_int63 => "one_int63", print_int63 => "print_int63", new_line => "print_new_line" ]
Include [ "int63.h" ].


(* Example 3: list_sum with int63 -- add_int63 is first class *)

Definition list_sum_int63 :=
  let n := List.fold_left add_int63 (List.repeat one_int63 100) zero_int63 in
  let _ := print_int63 n in new_line tt.


CertiRocq Compile list_sum_int63
Extract Constants [ add_int63 => "add_int63", zero_int63 => "zero_int63", one_int63 => "one_int63", print_int63 => "print_int63", new_line => "print_new_line" ]
Include [ "int63.h" ].


(* "Dummy" example with tinfo (tifno is not used by the C function) *)

Definition list_sum_int63_tinfo :=
  let n := List.fold_left add_int63 (List.repeat one_int63 100) zero_int63 in
  let _ := print_int63 n in new_line tt.

CertiRocq Compile list_sum_int63_tinfo
Extract Constants [ add_int63 => "add_int63" with tinfo, zero_int63 => "zero_int63", one_int63 => "one_int63", print_int63 => "print_int63" with tinfo, new_line => "print_new_line" ]
Include [ "int63_tinfo.h" ].


CertiRocq Generate Glue -file "glue" [ nat, bool, String ].
