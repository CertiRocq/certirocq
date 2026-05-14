From CertiRocq.Plugin Require Import CertiRocq.

From Stdlib Require Import Arith Bool List.

Import ListNotations.

Definition no_gc_bool : bool := negb false.

Definition no_gc_list : list bool := repeat true 8.

Definition no_gc_closure_loop (_ : unit) : nat :=
  (fix list_add k1 k2 k3 l : nat :=
     match l with
     | [] => 0
     | _ :: xs =>
       let clos z := k1 + k2 + k3 + z in
       clos 7 + list_add k1 k2 k3 xs
     end) 1 2 3 [4; 5].

Fixpoint no_gc_loop_add n (f : unit -> nat) : nat :=
  match n with
  | 0 => f tt
  | S n => f tt + no_gc_loop_add n f
  end.

Definition no_gc_closure : nat := no_gc_loop_add 0 no_gc_closure_loop.

CertiRocq Compile --no-gc no_gc_bool.

CertiRocq Compile --no-gc no_gc_list.

CertiRocq Compile -O 0 --no-gc no_gc_closure.
