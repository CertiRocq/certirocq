Require Import MetaRocq.Utils.bytestring.
Set Implicit Arguments.
From ExtLib Require Import Monads.
Import MonadNotation.

Inductive exception (A:Type) := Exc (_:string) | Ret (_:A).
Arguments Ret [A].
Arguments Exc [A] _%_bs.

Definition ret {A: Type} (x: A) := Ret x.
Definition raise {A: Type} (str:string) := @Exc A str.
Arguments raise {A} _%_bs.

Definition bind
    {A B: Type} (a: exception A) (f: A -> exception B): exception B :=
  match a with
    | Ret x => f x
    | Exc str => Exc str
  end.

Notation "A >>= F" := (bind A F).
Notation "'do' X <- A ; B" := (bind A (fun X => B))
    (at level 200, X name, A at level 100, B at level 200).

Lemma mon_left_id: forall (A B: Type) (a: A) (f: A -> exception B),
  ret a >>= f = f a.
intros.
reflexivity.
Qed.

Lemma mon_right_id: forall (A: Type) (a: exception A),
  a >>= ret = a.
intros.
induction a; repeat reflexivity.
Qed.
 
Lemma mon_assoc :
  forall (A B C: Type) (a: exception A)
         (f: A -> exception B) (g: B -> exception C),
    (a >>= f) >>= g = a >>= (fun x => f x >>= g).
intros.
induction a; repeat reflexivity.
Qed.

#[global] Instance exn_monad : Monad exception :=
  { ret := @ret; bind := @bind }.

Definition catch {T} (e : exception T) (f : string -> exception T) : exception T :=
  match e with
  | Ret x => Ret x
  | Exc s => f s
  end.

#[global] Instance exn_monad_exc : MonadExc string (fun A => exception A) :=
  { raise := @raise; catch := @catch }.

Definition econs
  (B:Type) (b:exception B) (bs:exception (list B)): exception (list B) :=
  do bb <- b;
  do bbs <- bs;
  ret (cons bb bbs).

Fixpoint emap (A B: Type) (f: A -> exception B) (cs: list A) :
                       exception (list B) :=
  match cs with
    | nil => ret nil
    | cons c cs => do C <- f c;
                   do Cs <- emap f cs;
                   ret (cons C Cs)
  end.

Definition epair2
  (A B:Type) (a:A) (b:exception B): exception (A * B) :=
  do bb <- b;
  ret (pair a bb).

Definition option_exception (A:Type) (o:option A) : exception A :=
  match o with
    | Some a => Ret a
    | None => raise "option_exception: None"
  end.

Definition exception_option (A:Type) (e:exception A) : option A :=
  match e with
    | Ret a => Some a
    | Exc s => None
  end.

Definition exception_map {A B:Type} (f: A->B) (e: exception A) : exception B:=
match e with
| Ret a => Ret (f a)
| Exc s => Exc s
end.
