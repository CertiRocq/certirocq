From Stdlib Require Import Arith List ZArith Uint63 PrimFloat PrimString.
From CertiRocq.Plugin Require Import CertiRocq.

Import ListNotations.

Set Warnings "-primitive-turned-into-axiom".

(* Every test is a natural number. The expected numbers are in expected_outputs. *)

(* A loop that exchanges two of its parameters *)
Fixpoint swap_loop (n : nat) (a b : nat) : nat :=
  match n with
  | 0 => a
  | S n => swap_loop n b a
  end.

Definition t_swap := swap_loop (1000 * 100 + 1) 3 7.

(* A loop that rotates three parameters and keeps one *)
Fixpoint rot_loop (n : nat) (k a b c : nat) : nat :=
  match n with
  | 0 => a + 2 * b + 3 * c + k
  | S n => rot_loop n k c a (S b)
  end.

Definition t_rot := rot_loop 1000 5 1 2 3.

(* Functions with many parameters *)
Fixpoint many (n a b c d e f g : nat) : nat :=
  match n with
  | 0 => a + b + c + d + e + f + g
  | S n => many n g a b c d e (S f)
  end.

Fixpoint many2 (n a b c d e f g : nat) : nat :=
  match n with
  | 0 => a + 2 * b + c + d + e + f + g
  | S n => S (many2 n b a (c + 1) d e f g)
  end.

Definition t_many := many 50 1 2 3 4 5 6 7 + many2 30 1 2 3 4 5 6 7.

(* Two functions that call each other in tail position *)
Fixpoint ev (n : nat) (acc : nat) {struct n} : nat :=
  match n with
  | 0 => acc
  | S n => od n (S acc)
  end
with od (n : nat) (acc : nat) {struct n} : nat :=
  match n with
  | 0 => acc + 1000
  | S n => ev n acc
  end.

Definition t_mutual := ev 3001 0.

(* Deep recursion that is not in tail position *)
Fixpoint len {A} (l : list A) : nat :=
  match l with
  | [] => 0
  | _ :: l => S (len l)
  end.

Definition t_deep := len (List.repeat true (200 * 100)).

(* Closures *)
Definition compose_all (fs : list (nat -> nat)) (x : nat) : nat :=
  List.fold_left (fun acc f => f acc) fs x.

Definition t_clos :=
  let k := 3 in
  compose_all (List.map (fun n m => n + m + k) (List.seq 0 50)) 1.

(* A type with several constructors with and without arguments *)
Inductive shape :=
| Dot | Line | Empty | Full
| Circle (r : nat) | Rect (w h : nat) | Tri (a b c : nat) | Poly (l : list nat).

Definition area (s : shape) : nat :=
  match s with
  | Dot => 1 | Line => 2 | Empty => 0 | Full => 100
  | Circle r => 3 * r * r
  | Rect w h => w * h
  | Tri a b c => a + b + c
  | Poly l => List.fold_left Nat.add l 0
  end.

Definition t_shape :=
  List.fold_left (fun acc s => acc + area s)
    [Dot; Circle 2; Line; Rect 3 4; Empty; Tri 1 2 3; Full; Poly [1;2;3;4]; Poly []; Circle 0] 0.

(* Many variables that are needed after several calls *)
Definition busy (a b c d e f g h : nat) : nat :=
  let x1 := len (List.repeat a b) in
  let x2 := len (List.repeat c d) in
  let x3 := len (List.repeat e f) in
  let x4 := len (List.repeat g h) in
  a + b + c + d + e + f + g + h + x1 + 2 * x2 + 3 * x3 + 4 * x4.

Definition t_busy := busy 1 2 3 4 5 6 7 8.

(* Trees: half of the calls are for leaves *)
Inductive tree := Leaf | Node (l : tree) (x : nat) (r : tree).

Fixpoint build (d : nat) (x : nat) : tree :=
  match d with
  | 0 => Leaf
  | S d => Node (build d (2 * x)) x (build d (2 * x + 1))
  end.

Fixpoint tsum (t : tree) : nat :=
  match t with
  | Leaf => 0
  | Node l x r => tsum l + x + tsum r
  end.

Fixpoint tmap (f : nat -> nat) (t : tree) : tree :=
  match t with
  | Leaf => Leaf
  | Node l x r => Node (tmap f l) (f x) (tmap f r)
  end.

Definition t_tree := tsum (tmap (fun x => x mod 7) (build 12 1)).

(* A match with no cases, in code that does not run *)
Definition absurd (n : nat) (H : n < 0) : nat := match Nat.nlt_0_r n H with end.

Definition pick (n : nat) : nat :=
  match lt_dec n 0 with
  | left H => absurd n H
  | right _ => n + 1
  end.

Definition t_absurd := pick 41.

(* Loops with 1,000,000 iterations. They overflow the C stack if a call in tail position
   is compiled as an ordinary call. *)
Fixpoint count (n : nat) (acc : list bool) : list bool :=
  match n with
  | 0 => acc
  | S n => count n (true :: acc)
  end.

Fixpoint len_acc (l : list bool) (acc : nat) : nat :=
  match l with
  | [] => acc
  | _ :: l => len_acc l (S acc)
  end.

Definition million := 1000 * 1000.

Definition t_loop := if Nat.eqb (len_acc (count million []) 0) million then 1 else 0.

(* The same with a call that is not in tail position in every iteration *)
Definition step (b : bool) (acc : nat) : nat := if b then S acc else acc.

Fixpoint len_with (f : bool -> nat -> nat) (l : list bool) (acc : nat) : nat :=
  match l with
  | [] => acc
  | b :: l => len_with f l (f b acc)
  end.

Definition t_loop_call := if Nat.eqb (len_with step (count million []) 0) million then 1 else 0.

Definition calls : list nat :=
  [t_swap; t_rot; t_many; t_mutual; t_deep; t_clos; t_shape; t_busy; t_tree; t_absurd;
   t_loop; t_loop_call].

(* Primitive integers *)
Fixpoint isum (n : nat) (i acc : int) : int :=
  match n with
  | 0 => acc
  | S n => isum n (i + 1)%uint63 (acc + i * i)%uint63
  end.

Definition t_int := Z.to_nat (to_Z (isum 1000 0%uint63 0%uint63 mod 1009)%uint63).

(* Additions with carry *)
Fixpoint carries (n : nat) (x : int) (acc : nat) : nat :=
  match n with
  | 0 => acc
  | S n =>
    match (x +c x)%uint63 with
    | C0 y => carries n (y + 12345)%uint63 acc
    | C1 y => carries n (y + 1)%uint63 (S acc)
    end
  end.

Definition t_carry := carries 500 4611686018427387000%uint63 0.

(* Floats *)
Fixpoint fsum (n : nat) (x acc : float) : float :=
  match n with
  | 0 => acc
  | S n => fsum n (x + 0.5)%float (acc + x * 2)%float
  end.

Definition t_float := if (PrimFloat.eqb (fsum 100 1.5 0) 5250)%float then 1 else 0.

(* Strings *)
Definition t_string :=
  let s := PrimString.cat "hello, " "world!"%pstring in
  Z.to_nat (to_Z (PrimString.length s)) +
  Z.to_nat (to_Z (PrimString.get s 4)) +
  Z.to_nat (to_Z (PrimString.length "12345678"%pstring)).

Definition prims : list nat := [t_int; t_carry; t_float; t_string].

CertiRocq Compile --output-suffix "_default" calls.
CertiRocq Compile -O 0 --output-suffix "_O0" calls.
CertiRocq Compile --cps --output-suffix "_cps" calls.
CertiRocq Compile --c-args 0 --output-suffix "_cargs0" calls.
CertiRocq Compile --c-args 2 --output-suffix "_cargs2" calls.

CertiRocq Compile --output-suffix "_default" prims.
CertiRocq Compile -O 0 --output-suffix "_O0" prims.
CertiRocq Compile --cps --output-suffix "_cps" prims.

CertiRocq Generate Glue --output "glue" [ nat, list ].
