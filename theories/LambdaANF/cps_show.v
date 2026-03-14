(** Pretty printer for LambdaANF CPS language.

    [show_exp e] constructs a string representing the term that has some
    minimal formatting so that it's much more readable.
*)
From Stdlib Require Import List.
Require Import LambdaANF.cps.
Require Import ExtLib.Data.Positive.
Require Import ExtLib.Structures.Monad.
Require Import ExtLib.Structures.MonadState.
Require Import ExtLib.Data.Monads.StateMonad.
From MetaRocq.Utils Require Import bytestring MRString. (* For identifier names *)
From MetaRocq.Common Require Import BasicAst Primitive. (* For identifier names *)
From MetaRocq.PCUIC Require Import PCUICPrimitive. (* For identifier names *)
Require Import Common.AstCommon.

Import MonadNotation.

Open Scope monad_scope.

Definition name_env : Set := M.tree Common.BasicAst.name.

Section PP.

  Variable (nenv:name_env).
  Variable (cenv:ctor_env).
  Variable (ftag_flag:bool). (* true if print tag *)

(* Convert various numbers to strings *)
Definition show_nat n := string_of_nat n.
Definition show_pos x := string_of_positive x.
Definition show_binnat x := show_nat (BinNat.N.to_nat x).

(* Add a separator [s] inbetween each element of a list [xs] *)
Fixpoint sep {A} (s:A) (xs:list A) : list A :=
  match xs with
  | nil => nil
  | h::nil => h::nil
  | h::t => h :: s :: (sep s t)
  end.

(* It's too expensive to append strings everywhere, so we
   accumulate a tree and then flatten it once to avoid this
   quadratic overhead. *)
Inductive string_tree :=
| Emp : string_tree
| Str : string -> string_tree
| App : string_tree -> string_tree -> string_tree.

Local Coercion Str : string >-> string_tree.

Infix "+++" := App (at level 100).

Fixpoint show_tree_c (t : string_tree) (acc : string) : string :=
  match t with
  | Emp => acc
  | App t1 t2 => show_tree_c t1 (show_tree_c t2 acc)
  | Str s => (s ++ acc)%bs
  end.

Definition show_tree t := (show_tree_c t "")%bs.

(* Variables are shown using "x" as a prefix if their original name is not known*)
Definition show_var (x:positive) :=
  match M.get x nenv with
    | Some (nNamed s) => (s+++("_")+++(show_pos x))%bs
    | _ => ("x" +++ (show_pos x))%bs
  end.

Definition show_name (no:BasicAst.name) (d:string) :=
  match no with
    | nNamed s => s
    | nAnon => d
  end.

Definition show_con (tg:ctor_tag) :=
  match M.get tg cenv with
    | Some {|ctor_name := nNamed s |} => s
    | _ => ("con_"+++(show_pos tg))%bs
  end.

Definition show_ftag (tg:fun_tag) :=
  if ftag_flag then ("<"+++(show_pos tg)+++">")%bs else ""%bs.

(* Show a list of variables as comma separated and wrapped in parens. *)
Definition show_vars (xs:list positive) :=
  ("(" +++ (List.fold_right (fun x y => x +++ y) ""
                            (sep (",":string_tree) (List.map show_var xs))) +++ ")")%bs.

(* We accumulate a string_tree as we convert the expressions to strings. *)
Definition M := state string_tree.
Import MonadNotation.

Definition emit (s:string_tree) : M unit :=
  st <- get ;;
  put (App st s).

Fixpoint tab (n:nat) : M unit :=
  match n with
  | 0 => ret tt
  | S n => emit " "%bs ;; tab n
  end.

(* Might need to add linefeed for windows? *)
Definition chr_newline : Byte.byte := "010"%byte.

Definition newline : M unit := emit (String.String chr_newline String.EmptyString).

Definition emit_prim (p : primitive) : M unit :=
  match projT1 p as tag return prim_value tag -> M unit with
  | primInt => fun f => emit "(int: " ;; emit (Show.string_of_prim_int f) ;; emit ")"
  | primFloat => fun f => emit "(float: " ;; emit (AstCommon.string_of_float f) ;; emit ")"
  | primString => fun f => emit "(string: " ;; emit (Show.string_of_pstring f) ;; emit ")"
  end%bs (projT2 p).

(* We assume each expression starts on a fresh newline, and that it
   should be indented by [indent] characters. *)
Fixpoint emit_exp (indent:nat) (e:exp) {struct e} : M unit :=
  tab indent ;;
  match e with
  | Econstr x tg xs e =>
    emit "let " ;; emit (show_var x) ;;
         (* emit " := con_" ;; emit (show_pos tg) ;; *)
    emit " := " ;; emit (show_con tg) ;;
    emit (show_vars xs) ;; emit " in " ;; newline ;;
    emit_exp indent e
  | Eproj x tg n y e =>
    emit "let " ;; emit (show_var x) ;;
    emit " := proj_" ;; emit (show_binnat n) ;; emit " " ;;
    emit (show_pos tg) ;; emit " " ;;
    emit (show_var y) ;; emit " in " ;; newline ;;
    emit_exp indent e
  | Eprim_val x p e =>
    emit "let " ;; emit (show_var x) ;;
    emit " := prim: " ;; emit_prim p ;;
    emit " in " ;; newline ;;
    emit_exp indent e
  | Eprim x p ys e =>
    emit "let " ;; emit (show_var x) ;;
    emit " := prim_" ;; emit (show_pos p) ;; emit (show_vars ys) ;;
    emit " in " ;; newline ;;
    emit_exp indent e
  | Eletapp x f ft ys e =>
    emit "let " ;; emit (show_var x) ;;
    emit " := app " ;;  emit (show_var f) ;; emit (show_ftag ft);; emit (show_vars ys) ;;
    emit " in " ;; newline ;;
    emit_exp indent e
  | Ecase x arms =>
    emit "case " ;; emit (show_var x) ;; emit " of {" ;; newline ;;
         (fix iter (xs : list (ctor_tag*exp)) : M unit :=
            match xs with
            | nil => ret tt
            | p::tail =>
              let (tg,e) := p in
              tab indent ;; emit "| " ;; emit (show_con tg) ;;
                  emit " => " ;; newline ;;
                  emit_exp (2 + indent) e ;;
                  iter tail
            end) arms ;;
         tab indent ;; emit "}" ;; newline
  | Efun fds e =>
    emit "letrec [" ;; newline ;;
         (fix iter (fds : fundefs) : M unit :=
            match fds with
            | Fnil => ret tt
            | Fcons x tg xs e fds' =>
              tab (2 + indent) ;;
                  emit "fun " ;; emit (show_var x) ;;
                   emit (show_ftag tg);;
                   emit (show_vars xs) ;; emit " := " ;; newline ;;
                   emit_exp (4 + indent) e ;;
                   iter fds'
            end) fds ;;
         tab indent ;; emit "] in" ;; newline ;; emit_exp indent e
  | Eapp x ft ys => emit (show_var x) ;; emit (show_ftag ft);; emit (show_vars ys) ;; newline
  | Ehalt x  => emit "halt " ;; emit (show_var x) ;; newline
  end%bs.

Fixpoint emit_val (indent:nat) (v:val) {struct v}: M unit :=
  tab indent ;;
      match v with
        | Vconstr tg l =>
          emit "constr "%bs;;emit (show_con tg);;emit " "%bs;; newline;;
               fold_left (fun u v => emit_val (indent+1) v) l newline
        | Vfun rho fds f =>
          (match  find_def f fds with
             | Some (t', xs ,e) =>
               emit "fun "%bs ;; emit (show_var f);;emit (show_vars xs);;emit ":="%bs;;newline;;emit_exp (4 + indent) e ;; newline
            (* emit "fun "%bs ;; emit (show_var f);;emit (show_ftag t');;emit (show_vars xs);;emit ":="%bs;; emit "..."%bs ;; newline *)
             | None => emit "ERROR! FUN "%bs ;; emit (show_var f);;emit " NOT FOUND!"%bs;;newline
           end)
        | Vprim p => emit "Primitive "%bs ;; emit_prim p ;; newline
        | Vint i => emit "Int "%bs;;newline
      end.
(*
with emit_vals (indent:nat) (vl:list val): M unit :=
       match vl with
         | v::vl' =>
           emit_val indent v;;
                     newline;;
                     emit_vals indent vl'
         | nil => newline
       end. *)

Definition show_val (v:val) : string :=
  String.String chr_newline
          (show_tree (snd (runState (emit_val 0 v) Emp))).


Fixpoint emit_env' (indent:nat) (rhol:list (positive* val)) {struct rhol}:M unit :=
  match rhol with
    | cons (p, v)  rhol' =>
      emit "| "%bs;;emit (show_var p);;emit " |->"%bs;; newline;;
           emit_val (indent+1) v;;newline
      ;; emit_env' indent rhol'
    | nil => newline
  end.


Fixpoint emit_cenv' (indent:nat) (cenvl:list (positive*ctor_ty_info)) {struct cenvl} : M unit :=
  match cenvl with
  | cons (p, info) cenvl' =>
    emit "| "%bs;;
         emit (show_pos p) ;;
         emit " |-> ("%bs ;;
         emit (show_name (ctor_name info) ("cons_"++(show_pos p)))%bs ;;
         emit " "%bs ;;
         emit (show_pos (ctor_ind_tag info)) ;;
         emit " "%bs ;; emit (show_binnat (ctor_arity info)) ;;
         emit " "%bs ;; emit (show_binnat (ctor_ordinal info)) ;;
         emit " )"%bs ;;
         newline ;;
         emit_cenv' indent cenvl'
    | nil => newline
  end.


Definition emit_env (indent:nat) (rho:M.t val): M unit :=
  emit "rho:{"%bs;;newline;;emit_env' indent (M.elements rho);;emit "}"%bs.


Definition emit_cenv (indent:nat) (cenv:M.t ctor_ty_info):M unit :=
  emit "cenv:{"%bs;;newline;;emit_cenv' indent (M.elements cenv);;emit "}"%bs.

Definition show_env (rho:M.t val) : string :=
  String.String chr_newline
         (show_tree (snd (runState (emit_env 0 rho) Emp))).

(* We add an extra newline at the front so that Coq will display the
   whole program correctly when we evaluate. *)
Definition show_exp (x:exp) : string :=
  String.String chr_newline
         (show_tree (snd (runState (emit_exp 0 x) Emp))).

(*  Some tests -- commented out for now. *)
(*
Require Import L5_to_LambdaANF.

Let P1 :=
  (Efun
     (Fcons 10 L5_to_LambdaANF.ty_con (13 :: nil)
        (Efun
           (Fcons 5 L5_to_LambdaANF.ty_con
              (11 :: 12 :: nil)
              (Eapp 15 (11 :: 12 :: nil)) Fnil)
           (Eapp 13 (14 :: nil)))
        (Fcons 15 L5_to_LambdaANF.ty_con (6 :: 7 :: nil)
           (Eapp 6 nil) Fnil))
     (Eapp 2 (10 :: nil)))%positive.

Eval vm_compute in show_exp P1.

Let P2 :=
(Efun
     (Fcons 32 L5_to_LambdaANF.ty_con (3 :: nil)
        (Efun
           (Fcons 10 L5_to_LambdaANF.ty_con (4 :: nil)
              (Efun
                 (Fcons 9 L5_to_LambdaANF.ty_fun
                    (5 :: 6 :: nil)
                    (Efun
                       (Fcons 8 L5_to_LambdaANF.ty_con
                          (7 :: nil)
                          (Eapp 7 (5 :: nil)) Fnil)
                       (Eapp 8 (6 :: nil))) Fnil)
                 (Eapp 4 (9 :: nil))) Fnil)
           (Efun
              (Fcons 31 L5_to_LambdaANF.ty_con (11 :: nil)
                 (Efun
                    (Fcons 28 L5_to_LambdaANF.ty_con
                       (12 :: nil)
                       (Efun
                          (Fcons 27 L5_to_LambdaANF.ty_fun
                             (13 :: 14 :: nil)
                             (Efun
                                (Fcons 26 L5_to_LambdaANF.ty_con
                                   (15 :: nil)
                                   (Efun
                                      (Fcons 17 L5_to_LambdaANF.ty_con
                                         (16 :: nil)
                                         (Eapp 16
                                            (13 :: nil)) Fnil)
                                      (Efun
                                         (Fcons 25 L5_to_LambdaANF.ty_con
                                            (18 :: nil)
                                            (Ecase 18
                                               ((1,
                                                Efun
                                                 (Fcons 24
                                                 L5_to_LambdaANF.ty_con
                                                 (23 :: nil)
                                                 (Eapp 23
                                                 (1 :: nil)) Fnil)
                                                 (Eapp 24
                                                 (15 :: nil)))
                                                ::
                                                (2,
                                                Eproj 19 L5_to_LambdaANF.ty
                                                 0 18
                                                 (Efun
                                                 (Fcons 22
                                                 L5_to_LambdaANF.ty_con
                                                 (20 :: nil)
                                                 (Econstr 21
                                                 L5_to_LambdaANF.ty 1 nil
                                                 (Eapp 20
                                                 (21 :: nil))) Fnil)
                                                 (Eapp 22
                                                 (15 :: nil))))
                                                :: nil)) Fnil)
                                         (Eapp 17
                                            (25 :: nil)))) Fnil)
                                (Eapp 26 (14 :: nil))) Fnil)
                          (Eapp 12 (27 :: nil))) Fnil)
                    (Efun
                       (Fcons 30 L5_to_LambdaANF.ty_con
                          (29 :: nil)
                          (Eapp 1 (1 :: 3 :: nil))
                          Fnil) (Eapp 28 (30 :: nil))))
                 Fnil) (Eapp 10 (31 :: nil)))) Fnil)
     (Eapp 2 (32 :: nil)))%positive.

Eval vm_compute in show_exp P2.
 *)

End PP.
