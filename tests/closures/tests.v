From CertiRocq.Plugin Require Import CertiRocq.

From Stdlib Require Import Arith List String.

Import ListNotations.

Axiom (print_nat : nat -> unit).
Axiom (print_str : string -> unit).
Axiom (new_line : unit -> unit).

Definition print_list (l : list nat) : unit :=
  let aux :=
      fix aux l :=
        match l with
        | [] => tt
        | [x] => print_nat x
        | x :: xs =>
          let _ := print_nat x in
          let _ := print_str ";" in
          aux xs
        end in
  let _ := print_str "[" in
  let _ := aux l in
  let _ := print_str "]" in
  new_line tt.

Fixpoint loop_add n (f : unit -> nat) : nat :=
  match n with
  | 0 => f tt
  | S n => f tt + loop_add n f
  end.

(* Local closure with a fixed captured environment. The closure body ignores the
   current list element, so only the surrounding environment matters. *)
Definition clos_loop (_ : unit) : nat :=
  (fix list_add k1 k2 k3 l : nat :=
     match l with
     | [] => 0
     | x :: xs =>
       let clos z := k1 + k2 + k3 + z in
       clos 7 + list_add k1 k2 k3 xs
     end) 1 2 3 [4; 5].

Definition clos : unit :=
  let _ := print_nat (loop_add 1 clos_loop) in
  new_line tt.

CertiRocq Compile clos
Extract Constants [ print_nat => "print_gallina_nat", print_str => "print_gallina_string", new_line => "print_new_line" ]
Include [ "print.h" ].

(* Local closure that captures both the surrounding environment and the current
   recursive argument. *)
Definition clos_capture_loop (_ : unit) : nat :=
  (fix list_add k1 k2 k3 l : nat :=
     match l with
     | [] => 0
     | x :: xs =>
       let clos z := x + k1 + k2 + k3 in
       clos x + list_add k1 k2 k3 xs
     end) 1 2 3 [4; 5].

Definition clos_capture : unit :=
  let _ := print_nat (loop_add 1 clos_capture_loop) in
  new_line tt.

CertiRocq Compile clos_capture
Extract Constants [ print_nat => "print_gallina_nat", print_str => "print_gallina_string", new_line => "print_new_line" ]
Include [ "print.h" ].

(* Recursive closure over a list, with an environment carried by the enclosing
   function arguments. *)
Definition addxy (x y w : nat) (l : list nat) :=
  let f :=
      fix aux l :=
        match l with
        | [] => []
        | z :: zs => (z + x + y + w) :: aux zs
        end in
  f l.

Definition rec_clos : unit :=
  print_list (addxy 1 2 3 [0; 1; 2]).

CertiRocq Compile rec_clos
Extract Constants [ print_nat => "print_gallina_nat", print_str => "print_gallina_string", new_line => "print_new_line" ]
Include [ "print.h" ].

(* Recursive closure with an accumulator argument, stressing environment capture
   across tail-recursive calls. *)
Definition intxy (x y w : nat) (l : list nat) :=
  let f :=
      fix aux l acc :=
        match l with
        | [] => acc
        | z :: zs => aux zs (z :: x :: y :: w :: acc)
        end in
  f l [].

Definition rec_clos2 : unit :=
  print_list (intxy 1 2 3 [0; 1]).

CertiRocq Compile rec_clos2
Extract Constants [ print_nat => "print_gallina_nat", print_str => "print_gallina_string", new_line => "print_new_line" ]
Include [ "print.h" ].

(* Direct recursive variant of the previous example, without the accumulator. *)
Definition intxy' (x y w : nat) (l : list nat) :=
  let f :=
      fix aux l :=
        match l with
        | [] => []
        | z :: zs => z :: x :: y :: w :: aux zs
        end in
  f l.

Definition rec_clos2_direct : unit :=
  print_list (intxy' 1 2 3 [0; 1]).

CertiRocq Compile rec_clos2_direct
Extract Constants [ print_nat => "print_gallina_nat", print_str => "print_gallina_string", new_line => "print_new_line" ]
Include [ "print.h" ].

CertiRocq Generate Glue --output "glue" [ nat, bool, String ].
