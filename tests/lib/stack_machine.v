(* Occam's razor, program computing with different number representations: N,nat,PrimInt *)

Require Import Nat Arith String List Uint63 BinNat ZArith.
Import ListNotations.

Inductive id : Type :=
| Id: string -> id.

Definition beq_id (a b: id) : bool :=
  match a, b with
  | Id a', Id b' => if string_dec a' b' then true else false
  end.

Definition total_map (A: Type) := id -> A.

Definition t_empty {A: Type} (v: A) : total_map A :=
  fun (_ : id) => v.

Definition t_update {A: Type} (m: total_map A) (k: id) (v: A) : total_map A :=
  fun (x : id) => if beq_id k x then v else m x.

Class Numeric A : Type :=
  {
    plus : A -> A -> A ;
    minus : A -> A -> A ;
    mult : A -> A -> A ;
    zero : A ;
  }.

#[export] Instance NumericNat : Numeric nat :=
  {
    plus := Nat.add ;
    minus := Nat.sub ;
    mult := Nat.mul ;
    zero := 0
  }.

#[export] Instance NumericBinNat : Numeric N :=
  {
    plus := fun x y => (x + y)%N ;
    minus := fun x y => (x - y)%N ;
    mult := fun x y => (x * y)%N ;
    zero := 0%N
  }.

#[export] Instance NumericPrimInt : Numeric int :=
  {
    plus := fun x y => (x + y)%uint63 ;
    minus := fun x y => (x - y)%uint63 ;
    mult := fun x y => (x * y)%uint63 ;
    zero := 0%uint63
  }.

Definition state {A} `{Numeric A} := total_map A.

Inductive aexp {A} `{Numeric A} : Type :=
  | ANum : A -> aexp
  | AId : id -> aexp
  | APlus : aexp -> aexp -> aexp
  | AMinus : aexp -> aexp -> aexp
| AMult : aexp -> aexp -> aexp.

Fixpoint aeval {A} `{Numeric A} (st : state) (a : aexp) : A :=
  match a with
  | ANum n => n
  | AId x => st x
  | APlus a1 a2 => plus (aeval st a1) (aeval st a2)
  | AMinus a1 a2  => minus (aeval st a1) (aeval st a2)
  | AMult a1 a2 => mult (aeval st a1) (aeval st a2)
  end.

Definition aeval' {A} `{Numeric A} :=
  aeval (t_empty zero).


Inductive sinstr {A} `{Numeric A} : Type :=
| SPush : A -> sinstr
| SLoad : id -> sinstr
| SPlus : sinstr
| SMinus : sinstr
| SMult : sinstr.

Fixpoint s_compile {A} `{Numeric A} (e : aexp) : list sinstr :=
  match e with
  | ANum x => [SPush x]
  | AId k => [SLoad k]
  | APlus a1 a2 => (s_compile a1) ++ (s_compile a2) ++ [SPlus]
  | AMinus a1 a2 => (s_compile a1) ++ (s_compile a2) ++ [SMinus]
  | AMult a1 a2 => (s_compile a1) ++ (s_compile a2) ++ [SMult]
  end.

Fixpoint s_execute {A} `{Numeric A} (st : state) (stack : list A)
                   (prog : list sinstr)
                 : list A :=
  match prog with
  | [] => stack
  | (SPush n) :: prog' => s_execute st (n :: stack) prog'
  | (SLoad k) :: prog' => s_execute st ((st k) :: stack) prog'
  | SPlus :: prog' => s_execute st ((plus (hd zero (tl stack)) (hd zero stack)) :: (tl (tl stack)))
                                prog'
  | SMinus :: prog' => s_execute st ((minus (hd zero (tl stack)) (hd zero stack)) :: (tl (tl stack)))
                                prog'
  | SMult :: prog' => s_execute st ((mult (hd zero (tl stack)) (hd zero stack)) :: (tl (tl stack)))
                                prog'
  end.

Definition s_execute' {A} `{Numeric A} :=
  s_execute (t_empty zero) [].
  
Lemma s_execute_app {A} `{Numeric A}: forall st stack si1 si2,
  s_execute st stack (si1 ++ si2) =
  s_execute st (s_execute st stack si1) si2.
Proof.
  intros.
  generalize dependent st.
  generalize dependent stack.
  generalize dependent si2.
  induction si1; intros.
  - reflexivity.
  - destruct a; simpl; apply IHsi1.
Qed.

Lemma s_compile_append {A} `{Numeric A}: forall st stack e,
  s_execute st stack (s_compile e) =
  (aeval st e) :: stack.
Proof.
  intros.
  generalize dependent st.
  generalize dependent stack.
  induction e; simpl; intros;
    try reflexivity;
    repeat rewrite s_execute_app;
    rewrite IHe1; rewrite IHe2;
    reflexivity.
Qed.

Theorem s_compile_correct {A} `{Numeric A} : forall (st : state) (e : aexp),
  s_execute st [] (s_compile e) = [ aeval st e ].
Proof.
  intros.
  apply s_compile_append.
Qed.

Fixpoint gauss_sum_aexp_nat n :=
  match n with
  | 0 => ANum 0
  | S n' => APlus (ANum n) (gauss_sum_aexp_nat n')
  end.

Fixpoint gauss_sum_aexp_N_aux (guard : nat) (n : N) :=
  match guard with
  | O => ANum 0%N
  | S g' => APlus (ANum n) (gauss_sum_aexp_N_aux g' (n - 1)%N)
  end.

Definition gauss_sum_aexp_N (n : N) :=
  gauss_sum_aexp_N_aux (N.to_nat n) n.

Fixpoint gauss_sum_aexp_PrimInt_aux (guard : nat) (n : int) :=
  match guard with
  | O => ANum 0%uint63
  | S g' => APlus (ANum n) (gauss_sum_aexp_PrimInt_aux g' (n - 1)%uint63)
  end.

Definition gauss_sum_aexp_PrimInt (n : int) :=
  gauss_sum_aexp_PrimInt_aux (Z.to_nat (Uint63.to_Z n)) n.

Definition gauss_sum_sintrs_nat (n : nat) :=
  s_compile (gauss_sum_aexp_nat n).

Definition gauss_sum_sintrs_N (n : N) :=
  s_compile (gauss_sum_aexp_N n).

Definition gauss_sum_sintrs_PrimInt (n : int) :=
  s_compile (gauss_sum_aexp_PrimInt n).
