(** * Expected outputs for the LLVM end-to-end tests, computed by Rocq.

    [to_sexp v] renders the value [v] the way [llvm_main.c] renders the word
    returned by the compiled [@certirocq_main], following [repr_val] of
    [theories/CodegenLLVM/LambdaANF_to_LLVM_statement.v]:

    - an unboxed word (a nullary constructor, or a primitive integer) prints
      as the decoded integer: the constructor's ordinal;
    - a boxed constructor prints as [(C<ord> f0 ... fn-1)].

    Ordinals are CertiRocq's: nullary and non-nullary constructors of an
    inductive are numbered separately, in declaration order
    ([LambdaBoxLocal_to_LambdaANF.v]), after the inductive remapping
    registered by the plugin's [Loader.v] ([bool => [1 0]]: true is 1,
    false is 0).  Type parameters are erased, so [cons] has two fields.

    One [SExp] instance per type used by a test; the instance states the
    ordinal/arity layout by hand. *)

From Stdlib Require Import String List NArith Decimal DecimalString.
Import ListNotations.
Open Scope string_scope.

Class SExp (A : Type) := to_sexp : A -> string.

Definition unboxed (ord : nat) : string := NilEmpty.string_of_uint (Nat.to_uint ord).
Definition boxed (ord : nat) (fields : list string) : string :=
  "(C" ++ NilEmpty.string_of_uint (Nat.to_uint ord) ++
  fold_right (fun f acc => " " ++ f ++ acc) "" fields ++ ")".

#[export] Instance SExp_unit : SExp unit := fun _ => unboxed 0.

#[export] Instance SExp_bool : SExp bool :=
  fun b => if b then unboxed 1 else unboxed 0.

(** [nat] is printed through an accumulator so that large numbers do not
    blow the stack of [vm_compute]: [S^n O] is [(C0 (C0 ... 0))]. *)
#[export] Instance SExp_nat : SExp nat :=
  fun n =>
    (fix go (n : nat) (acc : string) : string :=
       match n with
       | O => acc
       | S n => go n ("(C0 " ++ acc ++ ")")
       end) n (unboxed 0).

#[export] Instance SExp_positive : SExp positive :=
  fix go (p : positive) : string :=
    match p with
    | xI p => boxed 0 [go p]
    | xO p => boxed 1 [go p]
    | xH => unboxed 0
    end.

#[export] Instance SExp_N : SExp N :=
  fun n => match n with N0 => unboxed 0 | Npos p => boxed 0 [to_sexp p] end.

#[export] Instance SExp_list {A} `{SExp A} : SExp (list A) :=
  fix go (l : list A) : string :=
    match l with
    | [] => unboxed 0
    | x :: l => boxed 0 [to_sexp x; go l]
    end.

#[export] Instance SExp_prod {A B} `{SExp A} `{SExp B} : SExp (A * B) :=
  fun '(a, b) => boxed 0 [to_sexp a; to_sexp b].

#[export] Instance SExp_option {A} `{SExp A} : SExp (option A) :=
  fun o => match o with Some a => boxed 0 [to_sexp a] | None => unboxed 0 end.
