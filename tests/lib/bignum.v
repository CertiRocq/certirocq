Require Coq.Numbers.Cyclic.Int31.Int31.
Require Coq.Numbers.Natural.BigN.BigN.
Require Import ZArith.


Definition add31c' (n m: Int31.int31) : bool * Int31.int31 :=
 let npm := Int31.add31 n m in
   (negb (Z.eqb (Int31.phi npm) (Int31.phi n + Int31.phi m)), npm).

Definition sub31c' (n m: Int31.int31) : bool * Int31.int31 :=
 let npm := Int31.sub31 n m in
   (negb (Z.eqb (Int31.phi npm) (Int31.phi n - Int31.phi m)), npm).

(****
 In L1 or LambdaBoxMut, recognize the following functions and treat them
  opaquely (i.e., delete their function bodies, and let them be
 free variables with distinguished names):

  Int31.add31, Int31.add31c, Int31.add31carryc,
    Int31.iszero, and many others...

  and,    add31c', sub31c'  (* defined in this file *)

 Then, in translation to LambdaANF, replace these free variables as follows:
  where they occur in function-position,
    use  Eprim operators (primops);
  where they occur otherwise, use eta-expanded Eprim operators.

  We'll define the evaluation semantics of the Eprim operators
  w.r.t. the respective Coq functions.

****)


Module Bignum.
Import BigN.

SearchAbout (BigN.t -> Prop).

Definition maxint31 := sub31 0 1.
Definition maxint31b := BigN.N0 maxint31.

Inductive bignum :=
| BN_int: int31 -> bignum
| BN_big: forall i:BigN.t, BigN.lt maxint31b i -> bignum.

Definition t : Type := bignum.

Eval compute in BigN.of_pos (Pos.pow 2 32).

Fixpoint zn_last n (w: word BigN.w1 n) {struct n}: int31 :=
  match n  with
  | O =>
      fun w0 : word BigN.w1 O =>
      match w0 with
      | W0 => On
      | WW _ t1 => t1
      end
  | S n0 =>
      fun w0 : word BigN.w1 (S n0) =>
      match w0 with
      | W0 => On
      | WW _ w2 => zn_last n0 w2
      end
  end w.

Lemma w6_w1: forall n, word BigN.w6 (S n) = word BigN.w1 (6+n).
intros.
simpl.
rewrite !Nbasic.zn2z_word_comm.
reflexivity.
Qed.

Definition last_w6_plus (n : nat) (w : word BigN.w6 (S n)) : int31 :=
     zn_last (6 + n)
       (eq_rect (word BigN.w6 (S n)) (fun T : Type => T) w
          (word BigN.w1 (6 + n)) (w6_w1 n)).

Definition bign_to_int31 (a: BigN.t) : int31 :=
 match a with
 | BigN.N0 i => i
 | BigN.N1 w => zn_last O w
 | BigN.N2 w => zn_last 1 w
 | BigN.N3 w => zn_last 2 w
 | BigN.N4 w => zn_last 3 w
 | BigN.N5 w => zn_last 4 w
 | BigN.N6 w => zn_last 5 w
 | BigN.Nn n w => last_w6_plus n w
 end.

Lemma BigN_lt_dec: forall i j, {BigN.lt i j}+{~BigN.lt i j}.
Proof.
intros.
destruct (BigN.ltb i j) eqn:?; [left|right].
apply BigN.ltb_lt; auto.
apply BigN.ltb_nlt; auto.
Defined.

Definition normalize (a: BigN.t) :=
 match a with
 | BigN.N0 i => BN_int i
 | _ => match BigN_lt_dec maxint31b a with
            | left p => BN_big a p
            | right _ => BN_int (bign_to_int31 a)
            end
 end.

Definition add' (a b : bignum) : bignum :=
match a, b with
| BN_int i, BN_int j =>
     normalize (BigN.add (BigN.N0 i) (BigN.N0 j))
| BN_int i, BN_big j _ =>  normalize (BigN.add (BigN.N0 i) j)
| BN_big i _, BN_int j => normalize (BigN.add i (BigN.N0 j))
| BN_big i _, BN_big j _ => normalize (BigN.add i j)
end.

Definition add (a b : bignum) : bignum :=
match a, b with
| BN_int i, BN_int j =>
   match add31c' i j with
   | (false, k) => BN_int k
   | (true, _) => add' a b
   end
| _, _ => add' a b
end.

Definition sub' (a b : bignum) : bignum :=
match a, b with
| BN_int i, BN_int j =>
     normalize (BigN.sub (BigN.N0 i) (BigN.N0 j))
| BN_int i, BN_big j _ =>  normalize (BigN.sub (BigN.N0 i) j)
| BN_big i _, BN_int j => normalize (BigN.sub i (BigN.N0 j))
| BN_big i _, BN_big j _ => normalize (BigN.sub i j)
end.

Definition sub (a b : bignum) : bignum :=
match a, b with
| BN_int i, BN_int j =>
   match sub31c' i j with
   | (false, k) => BN_int k
   | (true, _) => sub' a b
   end
| _, _ => sub' a b
end.



Definition iszero (a: bignum) : bool :=
  match a with
  | BN_int i => iszero i
  | _ => false
  end.

Definition of_Z (n: Z) : bignum :=
 match n with
 | Zpos p => normalize (BigN.of_pos p)
 | Z0 => BN_int On
 | _ => BN_int On
 end.

Definition of_pos (n: positive) : bignum :=
  normalize (BigN.of_pos n).
Search (int31 -> nat).


Search (int31 -> nat).

Definition to_nat (a: bignum) : nat :=
 match a with
 | BN_int i => Z.to_nat (phi i)
 | BN_big i _ => Z.to_nat (BigN.to_Z i)
 end.

End Bignum.

(** Now, this is the code we'd like to optimize: *)

Definition add10 (x: Bignum.t) := Bignum.add x (Bignum.of_pos 10).

Eval compute in  add10 (Bignum.of_pos 5).
Eval compute in  add10 (Bignum.of_pos 2147483636).
Eval compute in  add10 (Bignum.of_pos 2147483646).

Require Import Recdef.

Lemma bignum_decr_less:
 forall n : Bignum.t,
 Bignum.iszero n = false ->
 Bignum.to_nat (Bignum.sub n (Bignum.of_Z 1)) < Bignum.to_nat n.
Admitted.

Function triang (n: Bignum.t) {measure Bignum.to_nat n}: Bignum.t :=
  if Bignum.iszero n
  then n
  else Bignum.add n (triang (Bignum.sub n (Bignum.of_Z 1))).
Proof.
exact bignum_decr_less.
Defined.

Eval compute in triang (Bignum.of_Z 3000).
