From Stdlib Require Import ZArith.ZArith
        Program.Basics
        Lists.List Lia.
From Stdlib Require PrimInt63 PrimString Uint63.
Require Import List_util.

Definition char_to_Z x := Uint63.to_Z x.
Import ListNotations.
Open Scope list_scope.

Fixpoint encode_list (l : list PrimString.char63) : list Z :=
  match l with
  | nil => [7]
  | [ x ] => (* ch 0%byte 0 0 0 0 0 07 *)
      [two_power_pos 56 * char_to_Z x + 6]
  | x :: y :: [] =>
      [two_power_pos 56 * char_to_Z x +
      two_power_pos 48 * char_to_Z y + 5]
  | x :: y :: z :: [] =>
      [two_power_pos 56 * char_to_Z x +
      two_power_pos 48 * char_to_Z y +
      two_power_pos 40 * char_to_Z z + 4]
  | x :: y :: z :: w :: [] =>
      [two_power_pos 56 * char_to_Z x +
      two_power_pos 48 * char_to_Z y +
      two_power_pos 40 * char_to_Z z +
      two_power_pos 32 * char_to_Z w + 3]
  | x :: y :: z :: w :: lx :: [] =>
      [two_power_pos 56 * char_to_Z x +
      two_power_pos 48 * char_to_Z y +
      two_power_pos 40 * char_to_Z z +
      two_power_pos 32 * char_to_Z w +
      two_power_pos 24 * char_to_Z lx + 2]
  | x :: y :: z :: w :: lx :: ly :: [] =>
      [two_power_pos 56 * char_to_Z x +
      two_power_pos 48 * char_to_Z y +
      two_power_pos 40 * char_to_Z z +
      two_power_pos 32 * char_to_Z w +
      two_power_pos 24 * char_to_Z lx +
      two_power_pos 16 * char_to_Z ly + 1]
  | x :: y :: z :: w :: lx :: ly :: lz :: [] =>
      [two_power_pos 56 * char_to_Z x +
      two_power_pos 48 * char_to_Z y +
      two_power_pos 40 * char_to_Z z +
      two_power_pos 32 * char_to_Z w +
      two_power_pos 24 * char_to_Z lx +
      two_power_pos 16 * char_to_Z ly +
      two_power_pos 8 * char_to_Z lz]
  | x :: y :: z :: w :: lx :: ly :: lz :: lw :: l =>
      (two_power_pos 56 * char_to_Z x +
      two_power_pos 48 * char_to_Z y +
      two_power_pos 40 * char_to_Z z +
      two_power_pos 32 * char_to_Z w +
      two_power_pos 24 * char_to_Z lx +
      two_power_pos 16 * char_to_Z ly +
      two_power_pos 8 * char_to_Z lz +
      char_to_Z lw) :: encode_list l
  end%Z.

Require Import ExtLib.Structures.Monads
               ExtLib.Data.Monads.OptionMonad
               ExtLib.Data.Monads.StateMonad.

Import MonadNotation.
Open Scope monad_scope.
From MetaRocq.Common Require Import BasicAst.

From compcert Require Import
  common.AST
  common.Errors
  lib.Integers
  cfrontend.Cop
  cfrontend.Ctypes
  cfrontend.Clight
  common.Values
  Clightdefs.

Require Import LambdaANF.cps
               LambdaANF.identifiers
               LambdaANF.cps_show.
Require LambdaANF.toplevel.

From MetaRocq.Utils Require Import bytestring MRString.

Section TRANSLATION.

(* Stand-in for arbitrary identifiers *)
Variable (argsIdent : ident).
Variable (allocIdent : ident).
Variable (limitIdent : ident).
Variable (gcIdent : ident).
Variable (mainIdent : ident).
Variable (bodyIdent : ident).
Variable (bodyName : string).
Variable (threadInfIdent : ident).
Variable (tinfIdent : ident).
Variable (heapInfIdent : ident).
Variable (numArgsIdent : ident).
Variable (isptrIdent : ident). (* ident for the is_ptr external function *)
Variable (caseIdent : ident). (* ident for the case variable , TODO: generate that automatically and only when needed *)

Variable (nParam : nat).

Variable (prims : LambdaANF.toplevel.prim_env).

Definition maxArgs : Z := 1024%Z.

(* temporary function to get something working *)
(* returns (n-1) :: (n-2) :: ... :: 0 :: nil for a list of size n *)
Fixpoint makeArgList' (vs : list positive) : list N :=
  match vs with
  | nil => nil
  | x :: vs' => (N.of_nat (length vs')) :: (makeArgList' vs')
  end.

Definition makeArgList (vs : list positive) : list N := rev (makeArgList' vs).



Definition fun_info_env : Type := M.t (positive * fun_tag).

(* Compute a fun_env by looking at the number of arguments functions
   are applied to, assumes that all functions sharing the same tags have the same arity *)
Fixpoint compute_fun_env' (n : nat) (fenv : fun_env) (e : exp) : fun_env :=
  match n with
  | 0 => fenv
  | S n' =>
    match e with
    | Econstr x t vs e' => compute_fun_env' n' fenv e'
    | Ecase x cs => fold_left (compute_fun_env' n') (map snd cs) fenv
    | Eproj x t n v e' => compute_fun_env' n' fenv e'
    | Eletapp x f t vs e' => compute_fun_env' n' (M.set t (N.of_nat (length vs), makeArgList vs) fenv) e'
    | Efun fnd e' => compute_fun_env' n' (compute_fun_env_fundefs n' fnd fenv) e'
    | Eapp x t vs => M.set t (N.of_nat (length vs) , makeArgList vs) fenv
    | Eprim_val x p e' => compute_fun_env' n' fenv e'
    | Eprim x p vs e' => compute_fun_env' n' fenv e'
    | Ehalt x => fenv
    end
  end
with compute_fun_env_fundefs n fnd fenv :=
  match n with
  | 0 => fenv
  | S n' =>
    match fnd with
    | Fnil => fenv
    | Fcons f t vs e fnd' =>
      let fenv' := M.set t (N.of_nat (length vs) , makeArgList vs) fenv in
      compute_fun_env_fundefs n' fnd' (compute_fun_env' n' fenv' e)
    end
  end.



Fixpoint max_depth (e : exp) : nat :=
  match e with
  | Econstr x t vs e' => S (max_depth e')
  | Ecase x cs => S (fold_left Nat.max (map (compose max_depth snd) cs) (S 0))
  | Eproj x t n v e' => S (max_depth e')
  | Eletapp x f t ys e' => S (max_depth e')
  | Efun fnd e' => S (Nat.max (max_depth_fundefs fnd) (max_depth e'))
  | Eapp x t vs => 1
  | Eprim_val x p e' => S (max_depth e')
  | Eprim x p vs e' => S (max_depth e')
  | Ehalt x => 1
  end
with max_depth_fundefs fnd :=
  match fnd with
  | Fnil => S 0
  | Fcons _ _ _ e fnd' => S (Nat.max (max_depth e) (max_depth_fundefs fnd'))
  end.

(* OS: this only computes fenv for known function. *)
Fixpoint compute_fun_env_fds fnd fenv:=
  match fnd with
  | Fnil => fenv
  | Fcons f t vs e fnd' =>
    let fenv' := M.set t (N.of_nat (length vs) , makeArgList vs) fenv in
    compute_fun_env_fds fnd' fenv'
  end.

(* fun_env maps tags to function info  *)


(* fun_env maps tags to function info *)
Definition compute_fun_env (e : exp) : fun_env :=
  compute_fun_env' (max_depth e) (M.empty fun_ty_info) e.


Fixpoint get_allocs (e : exp) : list positive :=
  match e with
  | Econstr x t vs e' => x :: (get_allocs e')
  | Ecase x cs =>
    (fix helper (cs : list (ctor_tag * exp)) :=
       match cs with
       | nil => nil
       | cons (z, e') cs' => (get_allocs e') ++ (helper cs')
       end) cs
  | Eproj x t n v e' => x :: (get_allocs e')
  | Eletapp x f t xs e' => x :: (get_allocs e')
  | Efun fnd e' => (get_allocs_fundefs fnd) ++ (get_allocs e')
  | Eapp x t vs => nil (* stores into args, not alloc new vars *)
  | Eprim_val x p e' => x :: (get_allocs e')
  | Eprim x p vs e' => x :: (get_allocs e')
  | Ehalt x => nil
  end
with get_allocs_fundefs (fnd : fundefs) :=
  match fnd with
  | Fnil => nil
  | Fcons f t vs e fnd' => vs ++ (get_allocs e) ++ (get_allocs_fundefs fnd')
  end.

(* Max number of value-sized words allocated by the translation of expression e
  For constructor: 1 word per argument + 1 for header if boxed (more than 1 param), otherwise 0 (since enum) *)
Fixpoint max_allocs (e : exp) : nat :=
  match e with
  | Econstr x t vs e' =>
    match vs with
    | nil => max_allocs e'
    | _ => S (max_allocs e' + length vs)
    end
  | Ecase x cs =>
    (fix helper (cs : list (ctor_tag * exp)) :=
       match cs with
       | nil => 0
       | cons (z, e') cs' => max (max_allocs e') (helper cs')
       end) cs
  | Eproj x t n v e' => max_allocs e'
  | Eletapp x f t ys e' => max_allocs e' (* XXX Zoe : This doesn't include the allocation happening by the function *)
  | Efun fnd e' => max (max_allocs_fundefs fnd) (max_allocs e')
  | Eapp x t vs => 0
  | Eprim_val x p e' => max_allocs e'
  | Eprim x p vs e' => max_allocs e'
  | Ehalt x => 0
  end
with max_allocs_fundefs (fnd : fundefs) :=
  match fnd with
  | Fnil => 0
  | Fcons f t vs e fnd' => max ((length vs) + (max_allocs e))
                              (max_allocs_fundefs fnd')
  end.

(* Compute the max number of parameters a function has in the term exp  *)
Fixpoint max_args (e : exp) : nat :=
  match e with
  | Econstr x t vs e' => max_args e'
  | Ecase x cs =>
    (fix helper (cs : list (ctor_tag * exp)) :=
       match cs with
       | nil => 0
       | cons (z, e') cs' => max (max_args e') (helper cs')
       end) cs
  | Eproj x t n v e' => max_args e'
  | Eletapp x f n xs e' => max_args e'
  | Efun fnd e' => max (max_args_fundefs fnd) (max_args e')
  | Eapp x t vs => 0
  | Eprim_val x p e' => max_args e'
  | Eprim x p vs e' => max_args e'
  | Ehalt x => 2
  end
with max_args_fundefs (fnd : fundefs) :=
  match fnd with
  | Fnil => 0
  | Fcons f t vs e fnd' => max (max (length vs) (max_args e))
                               (max_allocs_fundefs fnd')
  end.

(* Maybe move this to cps and replace the current definition of ind_ty_info? *)
(* 1) name of inductive type
   2) list containing the constructor info *)
Definition n_ind_ty_info : Type := BasicAst.name * list ctor_ty_info.

Definition n_ind_env := M.t n_ind_ty_info.

Definition update_ind_env (ienv : n_ind_env) (p : positive) (cInf : ctor_ty_info) : n_ind_env :=
  let '{| ctor_name := name
        ; ctor_ind_name := nameTy
        ; ctor_ind_tag := t
        ; ctor_arity := arity
        ; ctor_ordinal := ord
        |} := cInf in
  match (M.get t ienv) with
  | None => M.set t (nameTy, (cInf :: nil)) ienv
  | Some (nameTy, iInf) => M.set t (nameTy, cInf :: iInf) ienv
  end.

Definition compute_ind_env (cenv : ctor_env) : n_ind_env :=
  M.fold update_ind_env cenv (M.empty _).


Inductive ctor_rep : Type :=
| enum : N -> ctor_rep
(* [enum t] represents a constructor with no parameters with ordinal [t] *)
| boxed : N -> N -> ctor_rep.
(* [boxed t a] represents a construct with arity [a] and ordinal [t]  *)


Definition make_ctor_rep (cenv : ctor_env) (ct : ctor_tag) : option ctor_rep :=
  p <- M.get ct cenv ;;
  if ((ctor_arity p) =? 0)%N
    then ret (enum (ctor_ordinal p))
    else ret (boxed (ctor_ordinal p) (ctor_arity p)).


Definition threadStructInf : type := Tstruct threadInfIdent noattr.
Definition threadInf : type := Tpointer threadStructInf noattr.

(* NOTE: in Clight, SIZEOF_PTR == SIZEOF_INT *)
Definition intTy : type :=
  Tint I32 Signed {| attr_volatile := false; attr_alignas := None |}.
Definition uintTy : type :=
  Tint I32 Unsigned {| attr_volatile := false; attr_alignas := None |}.
Definition longTy : type :=
  Tlong Signed {| attr_volatile := false; attr_alignas := None |}.
Definition ulongTy : type :=
  Tlong Unsigned {| attr_volatile := false; attr_alignas := None |}.

Definition int_chunk : memory_chunk := if Archi.ptr64 then Mint64 else Mint32.
(* NOTE for val: in Clight, SIZEOF_PTR == SIZEOF_INT *)

(* Definition val : type := if Archi.ptr64 then ulongTy else uintTy. *)
Definition val : type := talignas (if Archi.ptr64 then 3%N else 2%N) (tptr tvoid).
Definition uval : type := if Archi.ptr64 then ulongTy else uintTy.
Definition sval : type := if Archi.ptr64 then longTy else intTy.
Definition val_typ : xtype := if Archi.ptr64 then Xlong else Xany32.
Definition Init_int (x : Z) : init_data :=
  if Archi.ptr64 then (Init_int64 (Int64.repr x)) else (Init_int32 (Int.repr x)).
Definition make_vint (z : Z) : Values.val :=
  if Archi.ptr64 then Vlong (Int64.repr z) else Values.Vint (Int.repr z).
Definition make_cint (z : Z) (t : type) : expr :=
  if Archi.ptr64 then Econst_long (Int64.repr z) t else (Econst_int (Int.repr z) t).
Transparent val.
Transparent uval.
Transparent val_typ.
Transparent Init_int.
Transparent make_vint.
Transparent make_cint.

Definition funTy : type :=
  Tfunction (cons threadInf nil) Tvoid cc_default.

Definition pfunTy : type := Tpointer funTy noattr.

Notation Tcons := cons.
Notation Tnil := nil.

Definition gcTy : type :=
  Tfunction (Tcons (Tpointer val noattr) (Tcons threadInf Tnil)) Tvoid cc_default.

Definition isptrTy : type :=
  Tfunction (Tcons val Tnil) (Tint IBool Unsigned noattr) cc_default.

Definition valPtr : type :=
  Tpointer val {| attr_volatile := false; attr_alignas := None |}.

Definition argvTy : type :=
  Tpointer val {| attr_volatile := false; attr_alignas := None |}.

Definition boolTy : type :=
  Tint IBool Unsigned noattr.

Fixpoint mkFunTyList (n : nat) : list type :=
  match n with
  | 0 => Tnil
  | S n' => Tcons val (mkFunTyList n')
  end.

Definition mkFunTy (n : nat) : type :=
  Tfunction (Tcons threadInf (mkFunTyList n)) Tvoid cc_default.

Definition mkPrimTy (n : nat) :=
  Tfunction (mkFunTyList n) val cc_default.

Definition mkPrimTyTinfo (n : nat) :=
  (Tfunction (Tcons threadInf (mkFunTyList n)) val cc_default).

Definition make_tinfoTy : type :=
  (Tfunction Tnil threadInf cc_default).

Definition exportTy : type :=
  Tfunction (Tcons threadInf Tnil) valPtr cc_default.


Notation "'var' x" := (Etempvar x val) (at level 20).
Notation "'ptrVar' x" := (Etempvar x valPtr) (at level 20).

Notation "'bvar' x" := (Etempvar x boolTy) (at level 20).
Notation "'funVar' x" := (Evar x funTy) (at level 20).

Definition allocPtr : expr := Etempvar allocIdent valPtr.
Definition limitPtr : expr := Etempvar limitIdent valPtr.
Definition args     : expr := Etempvar argsIdent valPtr.
Definition gc       : expr := Evar gcIdent gcTy.
Definition ptr      : expr := Evar isptrIdent isptrTy.

(* changed tinf to be tempvar and have type Tstruct rather than Tptr Tstruct *)
Definition tinf  : expr := (Etempvar tinfIdent threadInf).
Definition tinfd : expr := (Ederef tinf threadStructInf).

Notation heapInf := (Tstruct heapInfIdent noattr).

Definition add (a b : expr) := Ebinop Oadd a b valPtr.
Notation " a '+'' b " := (add a b) (at level 30).

Definition sub (a b: expr) := Ebinop Osub a b valPtr.
Notation " a '-'' b " := (sub a b) (at level 30).

Definition int_eq (a b : expr) := Ebinop Oeq a b type_bool.
Notation " a '='' b " := (int_eq a b) (at level 35).

Definition not (a : expr) := Eunop Onotbool a type_bool.
Notation "'!' a " := (not a) (at level 40).

Notation seq := Ssequence.

Notation " p ';;;' q " := (seq p q)
                         (at level 100, format " p ';;;' '//' q ").

Notation " a '::=' b " := (Sset a b) (at level 50).
Notation " a ':::=' b " := (Sassign a b) (at level 50).

Notation "'*' p " := (Ederef p val) (at level 40).

Notation "'&' p " := (Eaddrof p valPtr) (at level 40).

Definition c_int (n : Z) (t : type) : expr :=
  if Archi.ptr64
    then Econst_long (Int64.repr n) t
    else Econst_int (Int.repr n%Z) t.

Notation "'while(' a ')' '{' b '}'" :=
  (Swhile a b) (at level 60).

Notation "'call' f " := (Scall None f (tinf :: nil)) (at level 35).

Notation "'[' t ']' e " := (Ecast e t) (at level 34).

Notation "'Field(' t ',' n ')'" :=
  ( *(add ([valPtr] t) (c_int n%Z val))) (at level 36). (* what is the type of int being added? *)

Notation "'args[' n ']'" :=
  ( *(add args (c_int n%Z val))) (at level 36).



Definition reserve_body (funInf : positive) (l : Z) : statement :=
  let arr := (Evar funInf (Tarray uval l noattr)) in
  Sifthenelse
    (!(Ebinop Ole (Ederef arr uval) (limitPtr -' allocPtr) type_bool))
    (Scall None gc (arr :: tinf :: nil) ;;;
     allocIdent ::= Efield tinfd allocIdent valPtr)
    Sskip.


Definition reserve_body' (funInf : positive) (l : Z) : statement :=
  let arr := (Evar funInf (Tarray uval l noattr)) in
  let allocF := Efield tinfd allocIdent valPtr in
  let limitF := Efield tinfd limitIdent valPtr in
  Sifthenelse
    (!(Ebinop Ole (Ederef arr uval) (limitF -' allocF) type_bool))
    (Scall None gc (arr :: tinf :: nil))
    Sskip.


(* Don't shift the tag for boxed, make sure it is under 255 *)
Definition makeTagZ (cenv : ctor_env) (ct : ctor_tag) : option Z :=
      match make_ctor_rep cenv ct with
      | Some (enum t) => Some ((Z.shiftl (Z.of_N t) 1) + 1)%Z
      | Some (boxed t a) => Some  ((Z.shiftl (Z.of_N a) 10) + (Z.of_N t))%Z
      | None => None
      end.

Definition makeTag (cenv : ctor_env) (ct : ctor_tag) : option expr :=
  match makeTagZ cenv ct with
    | Some t =>
      Some (c_int t val)
    | None => None
  end.

Definition mkFunVar (x : ident) (locs : list N) : expr :=
  Evar x (mkFunTy (length (firstn nParam locs))).

Definition makeVar
           (x : positive)
           (fenv : fun_env)
           (map : fun_info_env) : expr :=
  match M.get x map with
  | None => var x
  | Some (_ , t) =>
    match M.get t fenv with
    | None => var x
    | Some (_ , locs) => mkFunVar x locs
    end
  end.

(* OS: assignConstructor' without the rev *)
Fixpoint assignConstructorS'
         (fenv : fun_env)
         (map : fun_info_env)
         (x : positive)
         (cur : nat)
         (vs : list positive): statement :=
  match vs with
  | nil => (* shouldn't be reached *)
       Sskip
  | cons v nil =>
    let vv := makeVar v fenv map in
    (Field(var x, Z.of_nat cur) :::= (*[val]*) vv)
  | cons v vs' =>
    let vv := makeVar v fenv map in
    let prog := assignConstructorS' fenv map x (cur+1)  vs'  in
         (* if v is a function name, funVar, otherwise lvar *)
             (Field(var x, Z.of_nat cur) :::= (*[val]*) vv ;;; prog)
  end.


Definition assignConstructorS
           (cenv : ctor_env)
           (ienv : n_ind_env)
           (fenv : fun_env)
           (map : fun_info_env)
           (x : positive)
           (t : ctor_tag)
           (vs : list positive) :=
  tag <- makeTag cenv t;;
  rep <- make_ctor_rep cenv t ;;
  match rep with
  | enum _ =>
      ret (x ::= tag)
  | boxed _ a =>
      let stm := assignConstructorS' fenv map x 0 vs in
      ret (x ::= [val] (allocPtr +' (c_int Z.one val)) ;;;
           allocIdent ::= allocPtr +' (c_int (Z.of_N (a + 1)) val) ;;;
           Field(var x, -1) :::= tag ;;;
           stm)
  end.

(* This is not valid in Clight if x is a Vptr, implementing instead as an external function
Definition isPtr (x : positive) :=
  int_eq
    (Ebinop Oand
            ([val] (var x))
            (c_int 1 val)
            val)
    (c_int 0 val).
 *)

Definition isPtr (retId : positive) (v : positive) : statement :=
  Scall (Some retId) ptr ([val](var v) :: nil).

Definition isBoxed (cenv : ctor_env) (ienv : n_ind_env) (ct : ctor_tag) : bool :=
  match make_ctor_rep cenv ct with
  | None => false
  | Some rep => match rep with
                | enum t => false
                | boxed t a => true
                end
  end.

Fixpoint mkCallVars
         (fenv : fun_env)
         (map: fun_info_env)
         (n : nat)
         (vs : list positive) : option (list expr) :=
  match n , vs with
  | 0 , nil => Some nil
  | S n , cons v vs' =>
    let vv := makeVar v fenv map in
    rest <- mkCallVars fenv map n vs' ;;
        ret (vv :: rest)
  | _ , _ => None
  end.

Definition mkCall
           (fenv : fun_env)
           (map: fun_info_env)
           (f : expr)
           (n : nat)
           (vs : list positive) : option statement :=
  match (mkCallVars fenv map n (firstn nParam vs)) with
  | Some v => Some (Scall None f (tinf :: v))
  | None => None
  end.

Definition mkPrimCall (res : positive) (pr : positive) (ar : nat)  (fenv : fun_env) (map: fun_info_env) (vs : list positive) : option statement :=
  args <- mkCallVars fenv map ar vs ;;
  ret (Scall (Some res) ([mkPrimTy ar] (Evar pr (mkPrimTy ar))) args).

Definition mkPrimCallTinfo (res : positive) (pr : positive) (ar : nat)  (fenv : fun_env) (map: fun_info_env) (vs : list positive) : option statement :=
  args <- mkCallVars fenv map ar vs ;;
  ret (Scall (Some res) ([mkPrimTyTinfo ar] (Evar pr (mkPrimTy ar))) (tinf :: args)).

Fixpoint asgnFunVars'
         (vs : list positive) (ind : list N) : option statement :=
  match vs with
  | nil =>
    match ind with
    | nil => ret Sskip
    | cons _ _ => None
    end
  | cons v vs' =>
    match ind with
    | nil => None
    | cons i ind' =>
      rest <- asgnFunVars' vs' ind' ;;
           ret  (v ::= args[ Z.of_N i ] ;;;
                rest)
    end
  end.

Definition asgnFunVars
           (vs : list positive) (ind : list N) : option statement :=
  asgnFunVars' (skipn nParam vs) (skipn nParam ind).

Fixpoint asgnAppVars''
         (vs : list positive)
         (ind : list N)
         (fenv : fun_env)
         (map : fun_info_env) : option statement :=
  match vs, ind with
  | nil, nil => ret Sskip
  | cons v vs' , cons i ind' =>
      let s_iv :=  args[ Z.of_N i ] :::= (makeVar v fenv map) in
        rest <- asgnAppVars'' vs' ind' fenv map ;;
        ret (rest ;;; s_iv)
  | _, _ => None
  end.

Definition asgnAppVars'
           (vs : list positive)
           (ind : list N)
           (fenv : fun_env)
           (map : fun_info_env) : option statement :=
  asgnAppVars'' (skipn nParam vs) (skipn nParam ind) fenv map.

Fixpoint get_ind {A : Type}
         (Aeq : A -> A -> bool) (l : list A) (a : A) : option nat :=
  match l with
  | nil => None
  | x :: l' =>
    match Aeq a x with
    | true => Some 0
    | false =>
      n <- get_ind Aeq l' a ;;
        ret (S n)
    end
  end.

Fixpoint remove_AppVars
         (myvs vs : list positive)
         (myind ind : list N) : option (list positive * list N) :=
  match vs , ind with
  | nil , nil => Some (nil , nil)
  | v :: vs , i :: ind =>
    '(vs' , ind') <- remove_AppVars myvs vs myind ind ;;
    match get_ind Pos.eqb myvs v with
    | Some n =>
      match nth_error myind n with
      | Some i' =>
        match N.eqb i i' with
        | true => ret (vs' , ind')
        | false => ret (v :: vs' , i :: ind')
        end
      | None => ret (v :: vs' , i :: ind')
      end
    | None => ret (v :: vs' , i :: ind')
    end
  | _ , _ => None
  end.

Definition asgnAppVars_fast'
           (myvs vs : list positive)
           (myind ind : list N)
           (fenv : fun_env)
           (map : fun_info_env) : option statement :=
  '(vs' , ind') <- remove_AppVars myvs (skipn nParam vs) myind (skipn nParam ind) ;;
  asgnAppVars'' vs' ind' fenv map.

(* Optional, reduce register pressure *)
Definition asgnAppVars
           (vs : list positive)
           (ind : list N)
           (fenv : fun_env)
           (map : fun_info_env) : option statement :=
  match asgnAppVars' vs ind fenv map with
    | Some s =>
     ret (argsIdent ::= Efield tinfd argsIdent (Tarray uval maxArgs noattr) ;;; s)
    | None => None
  end.

Definition asgnAppVars_fast
           (myvs vs : list positive)
           (myind ind : list N)
           (fenv : fun_env)
           (map : fun_info_env) : option statement :=
  match asgnAppVars_fast' myvs vs myind ind fenv map with
    | Some s =>
     ret (argsIdent ::= Efield tinfd argsIdent (Tarray uval maxArgs noattr) ;;; s)
    | None => None
  end.

Definition reserve
           (funInf : positive)
           (l : Z)
           (vs : list positive)
           (ind : list N)
           (fenv : fun_env)
           (map : fun_info_env) : option statement :=
  let arr := (Evar funInf (Tarray uval l noattr)) in
  match asgnAppVars'' (firstn nParam vs) (firstn nParam ind) fenv map , asgnFunVars' (firstn nParam vs) (firstn nParam ind) with
  | Some bef , Some aft =>
    Some (Sifthenelse
            (!(Ebinop Ole (Ederef arr uval) (limitPtr -' allocPtr) type_bool))
            (bef ;;;
             Scall None gc (arr :: tinf :: nil) ;;;
             allocIdent ::= Efield tinfd allocIdent valPtr ;;;
             aft)
            Sskip)
  | _, _ => None
  end.

Definition reserve'
           (funInf : positive)
           (l : Z)
           (vs : list positive)
           (ind : list N)
           (fenv : fun_env)
           (map : fun_info_env) : option statement :=
  let arr := (Evar funInf (Tarray uval l noattr)) in
  let allocF := Efield tinfd allocIdent valPtr in
  let limitF := Efield tinfd limitIdent valPtr in
  match asgnAppVars'' (firstn nParam vs) (firstn nParam ind) fenv map ,
        asgnFunVars' (firstn nParam vs) (firstn nParam ind) with
  | Some bef , Some aft =>
    Some (Sifthenelse
            (!(Ebinop Ole (Ederef arr uval) (limitF -' allocF) type_bool))
            (bef ;;; Scall None gc (arr :: tinf :: nil) ;;; aft)
            Sskip)
  | _, _ => None
  end.

Definition make_case_switch
           (x : positive)
           (ls : labeled_statements)
           (ls' : labeled_statements) : statement :=
  isPtr caseIdent x;;;
  Sifthenelse
    (bvar caseIdent)
    (Sswitch (Ebinop Oand (Field(var x, -1)) (make_cint 255 val) val) ls)
    (Sswitch (Ebinop Oshr (var x) (make_cint 1 val) val) ls').

Definition to_int64 (i : PrimInt63.int) : int64.
  exists (Uint63.to_Z i * 2 + 1)%Z.
  pose proof (Uint63.to_Z_bounded i).
  unfold Uint63.wB in H. unfold Int64.modulus, Int64.wordsize, Wordsize_64.wordsize.
  unfold Uint63.size in H. rewrite two_power_nat_correct. unfold Zpower_nat. simpl.
  destruct H. split. lia. lia.
Defined.

Definition float64_to_model (f : PrimFloat.float) : float64_model :=
  exist (FloatOps.Prim2SF f) (FloatAxioms.Prim2SF_valid f).

Definition model_to_ff (f : float64_model) : Binary.full_float :=
  Binary.SF2FF (proj1_sig f).

Program Definition to_float (f : PrimFloat.float) : Floats.float :=
  Binary.FF2B _ _ (model_to_ff (float64_to_model f)) _.
Next Obligation.
  unfold model_to_ff.
  pose proof (FloatAxioms.Prim2SF_valid f).
  rewrite Binary.valid_binary_SF2FF. exact H.
  unfold float64_to_model.
  unfold FloatOps.Prim2SF. cbn.
  Admitted.

Definition compile_float (cenv : ctor_env) (ienv : n_ind_env) (fenv : fun_env) (map : fun_info_env)
  (x : positive) (f : Floats.float) :=
  let tag := c_int 1277%Z (Tlong Unsigned noattr) in
  x ::= [val] (allocPtr +' (c_int Z.one val)) ;;;
  allocIdent ::= allocPtr +' (c_int 2 val) ;;;
  Field(var x, -1) :::= tag ;;;
  Field(var x, 0) :::= Econst_float f (Tfloat F64 noattr).

Definition compile_string (cenv : ctor_env) (ienv : n_ind_env) (fenv : fun_env) (map : fun_info_env)
  (x : positive) (f : PrimString.string) :=
  let len := Uint63.to_Z (PrimString.length f) in
  let words := ((len / 8) + 1)%Z in
  let tag := c_int (words * two_power_pos 10 + 252) (Tlong Unsigned noattr) in
  x ::= [val] (allocPtr +' (c_int Z.one val)) ;;;
  allocIdent ::= allocPtr +' (c_int (1 + words) val) ;;;
  let acc := Field(var x, -1) :::= tag in
  let l := PrimStringAxioms.to_list f in
  MRList.fold_left_i
    (fun acc i ch =>
       acc ;;;
       Field(var x, Z.of_nat i) :::= Econst_long (Int64.repr ch) (Tlong Unsigned noattr)) (encode_list l) acc.

Definition compile_primitive (cenv : ctor_env) (ienv : n_ind_env) (fenv : fun_env) (map : fun_info_env) (x : positive) (p : AstCommon.primitive) : statement :=
  match projT1 p as tag return AstCommon.prim_value tag -> statement with
  | AstCommon.primInt => fun i => x ::= Econst_long (to_int64 i) (Tlong Unsigned noattr)
  | AstCommon.primFloat => fun f => compile_float cenv ienv fenv map x (to_float f)
  | AstCommon.primString => fun f => compile_string cenv ienv fenv map x f
  end (projT2 p).

Fixpoint translate_body
         (e : exp)
         (fenv : fun_env)
         (cenv : ctor_env)
         (ienv : n_ind_env)
         (map : fun_info_env) : option statement :=
  match e with
  | Econstr x t vs e' =>
      prog <- assignConstructorS cenv ienv fenv map x t vs ;;
      prog' <- translate_body e' fenv cenv ienv map ;;
      ret (prog ;;; prog')
  | Ecase x cs =>
    (* ls <- boxed cases (Vptr), ls <- unboxed (Vint) *)
    p <- ((fix makeCases (l : list (ctor_tag * exp)) :=
            match l with
            | nil => ret (LSnil, LSnil)
            | cons p l' =>
              prog <- translate_body (snd p) fenv cenv ienv map ;;
                   p' <- makeCases l' ;;
                   let '(ls , ls') := p' in
                   match (make_ctor_rep cenv (fst p)) with
                   | Some (boxed t a ) =>
                     let tag := ((Z.shiftl (Z.of_N a) 10) + (Z.of_N t))%Z in
                     (match ls with
                     | LSnil =>
                       ret ((LScons None
                                    (prog ;;; Sbreak)
                                    ls), ls')
                     | LScons _ _ _ =>
                       ret ((LScons (Some (Z.land tag 255))
                                    (prog ;;; Sbreak)
                                    ls), ls')
                     end)
                   | Some (enum t) =>
                     let tag := ((Z.shiftl (Z.of_N t) 1) + 1)%Z in
                     (match ls' with
                     | LSnil =>
                       ret (ls, (LScons None
                                        (prog ;;; Sbreak)
                                        ls'))
                     | LScons _ _ _ =>
                       ret (ls, (LScons (Some (Z.shiftr tag 1))
                                        (prog ;;; Sbreak)
                                        ls'))
                     end)
                   | None => None
                   end
            end) cs) ;;
      let '(ls , ls') := p in
      ret (make_case_switch x ls ls')
  | Eletapp x f t vs e' =>
    prog <- translate_body e' fenv cenv ienv map ;;
    inf <- M.get t fenv ;;
    asgn <- asgnAppVars vs (snd inf) fenv map ;;
    let vv :=  makeVar f fenv map in
    let pnum := min (N.to_nat (fst inf)) nParam in
    c <- (mkCall fenv map ([Tpointer (mkFunTy pnum) noattr] vv) pnum vs) ;;
    ret (asgn ;;; Efield tinfd allocIdent valPtr  :::= allocPtr ;;; Efield tinfd limitIdent valPtr  :::= limitPtr ;;; c ;;; allocIdent ::= Efield tinfd allocIdent valPtr ;;; x ::= Field(args, Z.of_nat 1) ;;; prog)
  | Eproj x t n v e' =>
      prog <- translate_body e' fenv cenv ienv map ;;
      ret (x ::= Field(var v, Z.of_N n) ;;; prog)
  | Efun fnd e => None
  | Eapp x t vs =>
    inf <- M.get t fenv ;;
    asgn <- asgnAppVars vs (snd inf) fenv map ;;
    let vv :=  makeVar x fenv map in
    let pnum := min (N.to_nat (fst inf)) nParam in
    c <- (mkCall fenv map ([Tpointer (mkFunTy pnum) noattr] vv) pnum vs) ;;
    ret (asgn ;;;
         Efield tinfd allocIdent valPtr :::= allocPtr ;;;
         Efield tinfd limitIdent valPtr :::= limitPtr ;;;
         c)
  | Eprim_val x p e' =>
    prog <- translate_body e' fenv cenv ienv map ;;
    ret (compile_primitive cenv ienv fenv map x p ;;; prog)
  | Eprim x p vs e' =>
    match prims ! p with
    | Some (_, _, false, _) => (* compile without tinfo *)
      prog <- translate_body e' fenv cenv ienv map ;;
      pr_call <- mkPrimCall x p (length vs) fenv map vs ;;
      ret (pr_call ;;; prog)
    | Some (_, _, true, _) => (* compile with tinfo *)
      prog <- translate_body e' fenv cenv ienv map ;;
      pr_call <- mkPrimCallTinfo x p (length vs) fenv map vs ;;
      ret (Efield tinfd allocIdent valPtr :::= allocPtr ;;;
           Efield tinfd limitIdent valPtr :::= limitPtr ;;;
           pr_call ;;;
           allocIdent ::= Efield tinfd allocIdent valPtr ;;;
           limitIdent ::= Efield tinfd limitIdent valPtr ;;;
           prog)
    | None => None (* Unknown primitive identifier *)
    end
  | Ehalt x =>
    (* set args[1] to x and return *)
    ret (Efield tinfd allocIdent valPtr :::= allocPtr ;;;
         Efield tinfd limitIdent valPtr :::= limitPtr ;;;
         args[ Z.of_nat 1 ] :::= (makeVar x fenv map))
  end.

Fixpoint translate_body_fast
         (e : exp)
         (fenv : fun_env)
         (cenv : ctor_env)
         (ienv : n_ind_env)
         (map : fun_info_env)
         (myvs : list positive)
         (myind : list N) : option statement :=
  match e with
  | Econstr x t vs e' =>
      prog <- assignConstructorS cenv ienv fenv map x t vs ;;
      prog' <- translate_body_fast e' fenv cenv ienv map myvs myind ;;
      ret (prog ;;; prog')
  | Ecase x cs =>
    (* ls <- boxed cases (Vptr), ls <- unboxed (Vint) *)
    p <- ((fix makeCases (l : list (ctor_tag * exp)) :=
            match l with
            | nil => ret (LSnil, LSnil)
            | cons p l' =>
              prog <- translate_body_fast (snd p) fenv cenv ienv map myvs myind ;;
                   p' <- makeCases l' ;;
                   let '(ls , ls') := p' in
                   match (make_ctor_rep cenv (fst p)) with
                   | Some (boxed t a ) =>
                     let tag := ((Z.shiftl (Z.of_N a) 10) + (Z.of_N t))%Z in
                     (match ls with
                     | LSnil =>
                       ret ((LScons None
                                    (prog ;;; Sbreak)
                                    ls), ls')
                     | LScons _ _ _ =>
                       ret ((LScons (Some (Z.land tag 255))
                                    (prog ;;; Sbreak)
                                    ls), ls')
                     end)
                   | Some (enum t) =>
                     let tag := ((Z.shiftl (Z.of_N t) 1) + 1)%Z in
                     (match ls' with
                     | LSnil =>
                       ret (ls, (LScons None
                                        (prog ;;; Sbreak)
                                        ls'))
                     | LScons _ _ _ =>
                       ret (ls, (LScons (Some (Z.shiftr tag 1))
                                        (prog ;;; Sbreak)
                                        ls'))
                     end)
                   | None => None
                   end
            end) cs) ;;
      let '(ls , ls') := p in
      ret (make_case_switch x ls ls')
  | Eletapp x f t vs e' =>
    prog <- translate_body_fast e' fenv cenv ienv map myvs myind;;
    inf <- M.get t fenv ;;
    asgn <- asgnAppVars_fast myvs vs myind (snd inf) fenv map ;;
    let vv :=  makeVar f fenv map in
    let pnum := min (N.to_nat (fst inf)) nParam in
    c <- (mkCall fenv map ([Tpointer (mkFunTy pnum) noattr] vv) pnum vs) ;;
    ret (asgn ;;; Efield tinfd allocIdent valPtr :::= allocPtr ;;; Efield tinfd limitIdent valPtr :::= limitPtr ;;; c ;;; allocIdent ::= Efield tinfd allocIdent valPtr ;;; x ::= Field(args, Z.of_nat 1) ;;; prog)
  | Eproj x t n v e' =>
    prog <- translate_body_fast e' fenv cenv ienv map myvs myind ;;
    ret (x ::= Field(var v, Z.of_N n) ;;; prog)
  | Efun fnd e => None
  | Eapp x t vs =>
    inf <- M.get t fenv ;;
    asgn <- asgnAppVars_fast myvs vs myind (snd inf) fenv map ;;
    let vv :=  makeVar x fenv map in
    let pnum := min (N.to_nat (fst inf)) nParam in
    c <- (mkCall fenv map ([mkFunTy pnum] vv) pnum vs) ;;
    ret (asgn ;;;
         Efield tinfd allocIdent valPtr :::= allocPtr ;;;
         Efield tinfd limitIdent valPtr :::= limitPtr ;;;
         c)
  | Eprim_val x p e' =>
    prog <- translate_body e' fenv cenv ienv map ;;
    ret (compile_primitive cenv ienv fenv map x p ;;; prog)
  | Eprim x p vs e' =>
    match prims ! p with
    | Some (_, _, false, _) => (* compile without tinfo *)
      prog <- translate_body_fast e' fenv cenv ienv map myvs myind ;;
      pr_call <- mkPrimCall x p (length vs) fenv map vs ;;
      ret (pr_call ;;; prog)
    | Some (_, _, true, _) => (* compile with tinfo *)
      prog <- translate_body_fast e' fenv cenv ienv map myvs myind ;;
      pr_call <- mkPrimCallTinfo x p (length vs) fenv map vs ;;
      ret (pr_call ;;; prog)
    | None => None (* Unknown primitive identifier *)
    end
  | Ehalt x =>
    (* set args[1] to x and return *)
    ret (Efield tinfd allocIdent valPtr :::= allocPtr ;;;
         Efield tinfd limitIdent valPtr :::= limitPtr ;;;
         args[ Z.of_nat 1 ] :::= (makeVar x fenv map))
  end.

Definition mkFun
           (vs : list positive)
           (loc : list positive)
           (body : statement) : function :=
{|
  fn_return := Tvoid;
  fn_callconv := cc_default;
  fn_params := ((tinfIdent, threadInf) :: (map (fun x => (x, val)) (firstn nParam vs)));
  fn_vars := nil;
  fn_temps := ((map (fun x => (x, val)) ((skipn nParam vs) ++ loc)) ++ (allocIdent, valPtr) :: (limitIdent, valPtr) :: (argsIdent, valPtr) :: (caseIdent, boolTy) :: nil);
  fn_body := body;
|}.

Fixpoint translate_fundefs
         (fnd : fundefs)
         (fenv : fun_env)
         (cenv: ctor_env)
         (ienv : n_ind_env)
         (map : fun_info_env)
  : option (list (positive * globdef Clight.fundef type)) :=
  match fnd with
  | Fnil => ret nil
  | Fcons f t vs e fnd' =>
    match translate_fundefs fnd' fenv cenv ienv map with
    | None => None
    | Some rest =>
      match translate_body e fenv cenv ienv map with
      | None => None
      | Some body =>
        match M.get t fenv with
        | None => None
        | Some inf =>
          let '(l, locs) := inf in
          match asgnFunVars vs locs with
          | None => None
          | Some asgn =>
            match M.get f map with
            | None => None
            | Some gcArrIdent =>
              match reserve (fst gcArrIdent) (Z.of_N (l + 2)) vs locs fenv map with
              | None => None
              | Some res =>
                ret ((f , Gfun (Internal
                                  (mkFun vs (get_allocs e)
                                         ((allocIdent ::= Efield tinfd allocIdent valPtr ;;;
                                           limitIdent ::= Efield tinfd limitIdent valPtr ;;;
                                           argsIdent ::= Efield tinfd argsIdent (Tarray uval maxArgs noattr);;;
                                           res) ;;;
                                           asgn ;;;
                                           body)))) :: rest)
              end
            end
          end
        end
      end
    end
  end.

Fixpoint translate_fundefs_fast
         (fnd : fundefs)
         (fenv : fun_env)
         (cenv: ctor_env)
         (ienv : n_ind_env)
         (map : fun_info_env)
         : option (list (positive * globdef Clight.fundef type)) :=
  match fnd with
  | Fnil => ret nil
  | Fcons f t vs e fnd' =>
    match translate_fundefs_fast fnd' fenv cenv ienv map with
    | None => None
    | Some rest =>
      match M.get t fenv with
      | None => None
      | Some inf =>
         let '(l, locs) := inf in
         match translate_body_fast e fenv cenv ienv map vs locs  with
         | None => None
         | Some body =>
             match asgnFunVars vs locs with
             | None => None
             | Some asgn =>
                  match M.get f map with
                  | None => None
                  | Some gcArrIdent =>
                    match reserve (fst gcArrIdent) (Z.of_N (l + 2)) vs locs fenv map with
                    | None => None
                    | Some res =>
                         ret ((f , Gfun (Internal
                                           (mkFun vs (get_allocs e)
                                                  ((allocIdent ::= Efield tinfd allocIdent valPtr ;;;
                                                    limitIdent ::= Efield tinfd limitIdent valPtr ;;;
                                                    argsIdent ::= Efield tinfd argsIdent (Tarray uval maxArgs noattr);;;
                                                    res) ;;;
                                                    asgn ;;;
                                                    body)))) :: rest)
                         end
                  end
             end
         end
      end
    end
  end.


Definition make_extern_decl
           (nenv : name_env)
           (def : positive * globdef Clight.fundef type)
           (gv : bool)
           : option (positive * globdef Clight.fundef type) :=
  match def with
  | (fIdent, Gfun (Internal f)) =>
    (match M.get fIdent nenv with
     | Some (nNamed f_string) =>
       Some (fIdent, Gfun (External (EF_external (String.to_string f_string)
                                                 (signature_of_type (type_of_params (fn_params f))
                                                                    (fn_return f)
                                                                    (fn_callconv f)))
                                    (type_of_params (fn_params f)) (fn_return f) (fn_callconv f)))
     | _ => None
     end)
  | (vIdent, Gvar (mkglobvar v_info v_init v_r v_v)) =>
      if gv
      then Some (vIdent, Gvar (mkglobvar v_info nil v_r v_v))
      else None
  | _ => None
  end.


Fixpoint make_extern_decls
         (nenv : name_env)
         (defs : list (positive * globdef Clight.fundef type))
         (gv : bool)
         : list (positive * globdef Clight.fundef type) :=
  match defs with
  | fdefs::defs' =>
    let decls := make_extern_decls nenv defs' gv in
    (match make_extern_decl nenv fdefs gv with
    | Some decl =>
      decl :: decls
    | None => decls
    end)
  | nil => nil
  end.

Definition body_external_decl : positive * globdef Clight.fundef type :=
  let params := type_of_params ((tinfIdent, threadInf) :: nil) in
  (bodyIdent, Gfun (External (EF_external (String.to_string bodyName)
                                          (signature_of_type  params Tvoid cc_default))
                             params Tvoid cc_default)).


Definition translate_funs
         (e : exp)
         (fenv : fun_env)
         (cenv: ctor_env)
         (ienv : n_ind_env)
         (m : fun_info_env)
         : option (list (positive * globdef Clight.fundef type)) :=
  match e with
  | Efun fnd e => (* currently assuming e is body *)
      funs <- translate_fundefs fnd fenv cenv ienv m  ;;
      let localVars := get_allocs e in (* ADD ALLOC ETC>>> HERE *)
      body <- translate_body e fenv cenv ienv m ;;
      '(gcArrIdent , _) <- M.get mainIdent m ;;
      let argsExpr := Efield tinfd argsIdent (Tarray uval maxArgs noattr) in
      ret ((bodyIdent, Gfun (Internal {|
        fn_return := val;
        fn_callconv := cc_default;
        fn_params := (tinfIdent, threadInf)::nil;
        fn_vars := nil;
        fn_temps := (map (fun x => (x, val)) localVars) ++ (allocIdent, valPtr) :: (limitIdent, valPtr) :: (argsIdent, valPtr) :: nil;
        fn_body :=
          allocIdent ::= Efield tinfd allocIdent valPtr ;;;
          limitIdent ::= Efield tinfd limitIdent valPtr ;;;
          argsIdent ::= argsExpr ;;;
          reserve_body gcArrIdent 2%Z ;;;
          body ;;;
          Sreturn (Some (Field(argsExpr, Z.of_nat 1)))
      |})) :: funs)
  | _ => None
  end.

Definition translate_funs_fast
         (e : exp)
         (fenv : fun_env)
         (cenv: ctor_env)
         (ienv : n_ind_env)
         (m : fun_info_env)
         : option (list (positive * globdef Clight.fundef type)) :=
  match e with
  | Efun fnd e => (* currently assuming e is body *)
      funs <- translate_fundefs_fast fnd fenv cenv ienv m ;;
      let localVars := get_allocs e in (* ADD ALLOC ETC>>> HERE *)
      body <- translate_body e fenv cenv ienv m ;;
      '(gcArrIdent , _) <- M.get mainIdent m ;;
      ret ((bodyIdent, Gfun (Internal {|
        fn_return := Tvoid;
        fn_callconv := cc_default;
        fn_params := (tinfIdent, threadInf)::nil;
        fn_vars := nil;
        fn_temps := (map (fun x => (x, val)) localVars) ++ (allocIdent, valPtr) :: (limitIdent, valPtr) :: (argsIdent, valPtr) :: nil;
        fn_body :=
          allocIdent ::= Efield tinfd allocIdent valPtr ;;;
          limitIdent ::= Efield tinfd limitIdent valPtr ;;;
          argsIdent ::= Efield tinfd argsIdent (Tarray uval maxArgs noattr);;;
          reserve_body gcArrIdent 2%Z ;;;
          body
      |})) :: funs)
  | _ => None
  end.

Definition nState := ExtLib.Data.Monads.StateMonad.state positive.

Definition getName : nState positive :=
  n <- get ;;
    put (n+1)%positive ;;
    ret n.

Fixpoint make_ind_array (l : list N) : list init_data :=
  match l with
  | nil => nil
  | n :: l' => (Init_int (Z.of_N n)) :: (make_ind_array l')
  end.

  (* representation of pos as string *)
Fixpoint pos2string' p s :=
  match p with
  | xI p' => pos2string' p' (String.String "1" s)
  | xO p' => pos2string' p' (String.String "0" s)
  | xH => String.String "1" s
  end.

(* Definition pos2string p := *)
(*  pos2string' p "". *)


(* Definition show_pos x :=  pos2string x. (*nat2string10 (Pos.to_nat x). *) *)

Definition update_name_env_fun_info
           (f f_inf : positive)
           (nenv : name_env) : name_env :=
  match M.get f nenv with
  | None => M.set f_inf (nNamed (String.append (show_pos f) "_info")) nenv
  | Some n => match n with
              | nAnon => M.set f_inf (nNamed (String.append (String.append "x" (show_pos f)) "_info")) nenv
              | nNamed s => M.set f_inf (nNamed (String.append s "_info")) nenv
              end
  end.

(* see runtime for description and uses of fundef_info.
  In summary,
  fi[0] = number of words that can be allocated by function
  fi[1] = number of live roots at startof function
  rest = indices of live roots in args array
*)

Fixpoint make_fundef_info
         (fnd : fundefs)
         (fenv : fun_env)
         (nenv : name_env)
         : nState (option (list (positive * globdef Clight.fundef type) * fun_info_env * name_env)) :=
  match fnd with
  | Fnil => ret (Some (nil, M.empty (positive * fun_tag), nenv))
  | Fcons x t vs e fnd' =>
    match M.get t fenv with
    | None => ret None
    | Some inf =>
      let '(n, l) := inf in
      rest <- make_fundef_info fnd' fenv nenv ;;
           match rest with
           | None => ret None
           | Some rest' =>
             let '(defs, map, nenv') := rest' in
             info_name <- getName ;;
                       let len := Z.of_nat (length l) in
                       (* it should be the case that n (computed arity from tag) = len (actual arity) *)
                       let ind :=
                           mkglobvar
                             (Tarray uval
                                     (len + 2%Z)
                                     noattr)
                            ((Init_int (Z.of_nat (max_allocs e))) :: (Init_int len) :: (make_ind_array l)) true false in
                       ret (Some (((info_name , Gvar ind) :: defs) ,
                                  M.set x (info_name , t) map ,
                                  update_name_env_fun_info x info_name nenv'))
           end
    end
  end.



Definition add_bodyinfo
         (e : exp)
         (fenv : fun_env)
         (nenv : name_env)
         (map : fun_info_env)
         (defs : list (positive * globdef Clight.fundef type)) :=
  info_name <- getName ;;
  let ind :=
      mkglobvar
        (Tarray uval
                2%Z
                noattr)
        ((Init_int (Z.of_nat (max_allocs e))) :: (Init_int 0%Z) :: nil) true false in
  ret (Some (((info_name , Gvar ind) :: defs),
              (M.set mainIdent (info_name , 1%positive) map),
              (M.set info_name (nNamed "body_info"%bs) nenv))).



(* Make fundef_info for functions in fnd (if any), and for the body of the program *)
Definition make_funinfo
         (e : exp)
         (fenv : fun_env)
         (nenv : name_env)
         : nState (option (list (positive * globdef Clight.fundef type) * fun_info_env * name_env)) :=
  match e with
  | Efun fnd e' =>
    p <- make_fundef_info fnd fenv nenv;;
      match p with
      | None => ret None
      | Some p' =>
        let '(defs, map, nenv') := p' in
        add_bodyinfo e' fenv nenv' map defs
      end
  | _ => ret None
  end.


Definition global_defs (e : exp)
           : list (positive * globdef Clight.fundef type) :=
(*  let maxArgs := (Z.of_nat (max_args e)) in
  (allocIdent, Gvar (mkglobvar valPtr ((Init_int(Int.zero)) :: nil) false false))
    :: (limitIdent , Gvar (mkglobvar valPtr  ((Init_int(Int.zero)) :: nil) false false))
    :: (argsIdent , Gvar (mkglobvar (Tarray val maxArgs noattr)
                                    ((Init_int(Int.zero)) :: nil)
                                    false false))
    :: *)
  (* (gcIdent, *)
  (*  Gfun (External (EF_external (String.to_string "garbage_collect") *)
  (*                 (mksignature (val_typ :: nil) AST.Tvoid cc_default)) *)
  (*     (Tcons (Tpointer val noattr) (Tcons threadInf Tnil)) *)
  (*     Tvoid *)
  (*     cc_default)) :: *)
  (* (isptrIdent, *)
  (*  Gfun (External (EF_external (String.to_string "is_ptr") *)
  (*                            (mksignature (val_typ :: nil) AST.Tvoid cc_default)) *)
  (*     (Tcons val Tnil) (Tint IBool Unsigned noattr) *)
  (*     cc_default)) :: *)
  nil.


Definition make_defs
           (e : exp)
           (fenv : fun_env)
           (cenv: ctor_env)
           (ienv : n_ind_env)
           (nenv : M.t BasicAst.name)
           : nState (exceptionMonad.exception (M.t BasicAst.name * (list (positive * globdef Clight.fundef type)))) :=
  fun_inf' <- make_funinfo e fenv nenv ;;
  match fun_inf' with
  | Some p =>
    let '(fun_inf, map, nenv') := p in
    match translate_funs e fenv cenv ienv map with
    | None => ret (exceptionMonad.Exc "translate_funs")
    | Some fun_defs' =>
      let fun_defs := rev fun_defs' in
      ret (exceptionMonad.Ret (nenv',
                               ((((global_defs e) ++ fun_inf ++ fun_defs)))))
    end
  | None => ret (exceptionMonad.Exc "make_funinfo")
  end.

Definition make_defs_fast
           (e : exp)
           (fenv : fun_env)
           (cenv: ctor_env)
           (ienv : n_ind_env)
           (nenv : M.t BasicAst.name)
           : nState (option (M.t BasicAst.name * (list (positive * globdef Clight.fundef type)))) :=
  fun_inf' <- make_funinfo e fenv nenv ;;
  match fun_inf' with
  | Some p =>
    let '(fun_inf, map, nenv') := p in
    match translate_funs_fast e fenv cenv ienv map with
    | None => ret None
    | Some fun_defs' =>
      let fun_defs := rev fun_defs' in
      ret (Some (nenv',
                ((((global_defs e) ++ fun_inf ++ fun_defs)))))
    end
  | None => ret None
  end.

Definition composites : list composite_definition :=
  (* Composite threadInfIdent Struct *)
  (*   (Member_plain allocIdent valPtr :: *)
  (*   Member_plain limitIdent valPtr :: *)
  (*   Member_plain heapInfIdent (tptr (Tstruct heapInfIdent noattr)) :: *)
  (*   Member_plain argsIdent (Tarray uval maxArgs noattr) :: *)
  (*    nil) noattr :: *)
  nil.

Definition mk_prog_opt
           (defs : list (ident * globdef Clight.fundef type))
           (main : ident)
           (add_comp : bool) : option Clight.program :=
  let composites := if add_comp then composites else nil in
  let res := Ctypes.make_program composites defs (bodyIdent :: nil) main in
  match res with
  | Error e => None
  | OK p => Some p
  end.



(* Wrap program in empty Efun if e.g. fully inlined *)
Definition wrap_in_fun (e:exp) : exp :=
  match e with
  | Efun fds e' => e
  | _ => Efun Fnil e
  end.

Definition add_inf_vars (nenv : name_env) : name_env :=
  M.set isptrIdent (nNamed "is_ptr"%bs) (
  M.set argsIdent (nNamed "args"%bs) (
          M.set allocIdent (nNamed "alloc"%bs) (
                  M.set limitIdent (nNamed "limit"%bs) (
                        M.set gcIdent (nNamed "garbage_collect"%bs) (
                                M.set mainIdent (nNamed "main"%bs) (
                                       M.set bodyIdent (nNamed bodyName%bs) (
                                               M.set threadInfIdent (nNamed "thread_info"%bs) (
                                                       M.set tinfIdent (nNamed "tinfo"%bs) (
                                                               M.set heapInfIdent (nNamed "heap"%bs) (
                                                                     M.set caseIdent (nNamed "arg"%bs) (
                                                                           M.set numArgsIdent (nNamed "num_args"%bs) nenv))))))))))).

Definition ensure_unique : M.t name -> M.t name :=
  fun l => M.map (fun x n =>
                    match n with
                    | nAnon =>  nAnon
                    | nNamed s => nNamed (String.append s (String.append "_"%bs (show_pos x)))
                  end) l.



Fixpoint make_proj (recExpr : expr) (start : nat) (left : nat) : list expr :=
  match left with
  | 0 => nil
  | S n =>
    let s := make_proj recExpr (S start) n in
    (Field(recExpr, Z.of_nat start))::s
  end.

Fixpoint make_Asgn (les : list expr) (res : list expr) :=
  match les, res with
  | (hl :: les), (hr :: res) =>
    (Sassign hl hr) ;;; (make_Asgn les res)
  | _, _ => Sskip
  end.


Fixpoint make_argList' (n : nat) (nenv : name_env) : nState (name_env * list (ident * type)) :=
  match n with
  | 0 => ret (nenv, nil)
  | (S n') =>
    new_id <- getName;;
           let new_name := String.append "arg" (MRString.string_of_nat n') in
           let nenv := M.set new_id (nNamed new_name) nenv in
           rest <- make_argList' n' nenv;;
                let (nenv, rest_id) := rest in
                ret (nenv, (new_id,val)::rest_id)
  end.

Definition make_argList (n:nat) (nenv:name_env) : nState (name_env * list (ident * type)) :=
  rest <- make_argList' n nenv;;
       let (nenv, rest_l) := rest in
       ret (nenv, rev rest_l).

Fixpoint make_constrAsgn' (argv:ident) (argList:list (ident * type)) (n:nat) :=
  match argList with
  | nil => Sskip
  | (id, ty)::argList' =>
    let s' := make_constrAsgn' argv argList' (S n) in
    (Sassign (Field(var argv, Z.of_nat n)) (Etempvar id ty) ;;; s')
  end.

Definition make_constrAsgn (argv:ident) (argList:list (ident * type)) :=
    make_constrAsgn' argv argList 1.

Import String (append).

(* Compute the header file comprising of:
   1) Constructors and eliminators for every inductive types in the n_ind_env
   2) Direct style calling functions for the original (named) functions *)

Fixpoint make_constructors
         (cenv : ctor_env)
         (nTy : Kernames.ident)
         (ctors : list ctor_ty_info)
         (nenv : name_env)
         : nState (name_env * (list (positive * globdef Clight.fundef type))) :=
  let make_name (nTy nCtor : Kernames.ident) : BasicAst.name :=
    nNamed (String.append "make_" (append nTy (append "_" nCtor))) in
  match ctors with
  | nil => ret (nenv, nil)
  | {| ctor_name := nAnon |} :: ctors =>
      make_constructors cenv nTy ctors nenv
  | {| ctor_name := nNamed nCtor ; ctor_arity := 0%N ; ctor_ordinal := ord |} :: ctors => (* unboxed *)
      constr_fun_id <- getName;;
      let constr_body :=
         Sreturn (Some (Econst_int (Int.repr (Z.add (Z.shiftl (Z.of_N ord) 1) 1)) val)) in
      let constr_fun := Internal ({|
        fn_return := val;
        fn_callconv := cc_default;
        fn_params := nil;
        fn_vars := nil;
        fn_temps := nil;
        fn_body := constr_body|}) in
      let nenv :=
          M.set constr_fun_id (make_name nTy nCtor) nenv in
      (* elet cFun :=  (Internal (mkFun )) *)
      l <- make_constructors cenv nTy ctors nenv ;;
      let (nenv, funs) := l in
      ret (nenv, (constr_fun_id ,(Gfun constr_fun))::funs)
  | {| ctor_name := nNamed nCtor ; ctor_arity := Npos arr ; ctor_ordinal := ord |} :: ctors => (* boxed *)
      constr_fun_id <- getName;;
      argvIdent <- getName;;
      argList <- make_argList (Pos.to_nat arr) nenv;;
      let (nenv, argList) := argList in
      let asgn_s := make_constrAsgn argvIdent argList in
      let header := c_int (Z.of_N ((N.shiftl (Npos arr) 10) + ord)) val in
      let constr_body :=
          Sassign (Field(var argvIdent, 0%Z)) header ;;;
          asgn_s ;;;
          Sreturn (Some (add (Evar argvIdent argvTy) (c_int 1%Z val))) in
      let constr_fun := Internal ({|
          fn_return := val;
          fn_callconv := cc_default;
          fn_params := argList ++ ((argvIdent, argvTy) :: nil);
          fn_vars := nil;
          fn_temps := nil;
          fn_body := constr_body
        |}) in
      let nenv :=
          M.set argvIdent (nNamed "argv"%bs) (
            M.set constr_fun_id (make_name nTy nCtor) nenv) in
      (* elet cFun :=  (Internal (mkFun )) *)
      l <- make_constructors cenv nTy ctors nenv;;
      let (nenv, funs) := l in
      ret (nenv, (constr_fun_id, Gfun constr_fun) :: funs)
  end.

(* make a function discriminating over the different constructors of an inductive type *)

Notation charPtrTy := (Tpointer tschar noattr).
Notation nameTy    := (Tpointer charPtrTy noattr).
Notation arityTy   := (Tpointer val noattr).


Definition make_elim_Asgn (argv:ident) (valIdent:ident) (arr:nat): statement :=
  let argv_proj := make_proj (var argv) 0%nat arr in
  let val_proj := make_proj (var valIdent) 0%nat arr in
  make_Asgn argv_proj val_proj.

Fixpoint asgn_string_init (s : string) : list init_data :=
  match s with
  | String.EmptyString => Init_int8 Int.zero :: nil
  | String.String c s' =>
      let i := Int.repr (Z.of_N (Byte.to_N c)) in
      Init_int8 i :: asgn_string_init s'
  end.

(* create a global variable with a string constant, return its id *)
Definition asgn_string_gv (s : string)
           : nState (ident * type * globdef Clight.fundef type) :=
  strIdent <- getName;;
  let len := String.length s in
  let init := asgn_string_init s in
  let ty := tarray tschar (Z.of_nat len) in
  let gv := Gvar (mkglobvar ty init true false) in
  ret (strIdent, ty, gv).

Definition asgn_string
           (charPtr:ident) (n:name)
           : nState (statement *  list (ident * globdef Clight.fundef type)) :=
  match n with
  | nAnon =>
    ret (Sassign (Field(Etempvar charPtr charPtrTy, 0%Z)) (Econst_int (Int.repr 0%Z) tschar) , nil)
  | nNamed s =>
    '(i, _, gv) <- asgn_string_gv  s;;
    ret (Sassign (Etempvar charPtr charPtrTy) (Evar i charPtrTy), (i, gv) :: nil)
  end.

Definition make_arities_gv
           (arity_list : list N)
           : globdef Clight.fundef type :=
  Gvar (mkglobvar (tarray tint (Z.of_nat (length arity_list)))
                     (List.map (fun n => Init_int (Z.of_N n)) arity_list)
                     true false).

Definition pad_char_init (l : list init_data) (n :nat) : list init_data :=
  let m := n - (length l) in
  l ++ List.repeat (Init_int8 Int.zero) m.

Fixpoint make_names_init (nameList : list name) (n : nat) : nat * list init_data :=
  match nameList with
  | nil => (n, nil)
  | nNamed s :: nameList' =>
      let (max_len, init_l) := make_names_init nameList' (max n (String.length s + 1)) in
      let i := pad_char_init (asgn_string_init s) max_len in
      (max_len, i ++ init_l)
  | nAnon :: nameList' =>
      let (max_len, init_l) := make_names_init nameList' n in
      let i := pad_char_init (asgn_string_init ""%bs) max_len in
      (max_len, i ++ init_l)
  end.

Definition make_names_gv
           (nameList : list name) : globdef Clight.fundef type * type :=
  let (max_len, init_l) := make_names_init nameList 1 in
  let ty := tarray (tarray tschar (Z.of_nat max_len))
                   (Z.of_nat (length nameList)) in
  (Gvar (mkglobvar ty init_l true false), ty).

Definition make_eliminator
           (itag : ind_tag)
           (cenv : ctor_env)
           (nTy : Kernames.ident)
           (ctors : list ctor_ty_info)
           (nenv : name_env)
           : nState (name_env * list (ident * globdef Clight.fundef type)) :=
  valIdent <- getName ;;
  ordIdent <- getName ;;
  argvIdent <- getName ;;
  elim_fun_id <- getName ;;
  nameIdent <- getName ;;
  gv_aritiesIdent <- getName ;;
  gv_namesIdent <- getName ;;
  temp <-
    (fix make_elim_cases
         (ctors : list ctor_ty_info)
         (currOrd : nat)
         : nState (labeled_statements * labeled_statements * list name * list N) :=
       match ctors with
       | nil => ret (LSnil, LSnil, nil, nil)
       | ctor :: ctors =>
           temp <- make_elim_cases ctors (S currOrd) ;;
           let '(ls, ls', nameList, arrList) := temp in
(*           name_p <- asgn_string nameIdent nName;;
           let '(name_s, name_gv) := name_p in *)
           let curr_s :=
               (* Ssequence (* name_s *) Sskip *)
                 ((Sassign (Field(var ordIdent, 0%Z)) (c_int (Z.of_nat currOrd) val)) ;;;
                   (make_elim_Asgn argvIdent valIdent (N.to_nat (ctor_arity ctor))) ;;; Sbreak) in
           let arity := ctor_arity ctor in
           (match arity with
            | 0%N =>
                ret (ls,
                     LScons (Some (Z.of_N (ctor_ordinal ctor))) curr_s ls',
                     ctor_name ctor :: nameList,
                     arity :: arrList)
            | Npos p =>
                ret (LScons (Some (Z.of_N (ctor_ordinal ctor))) curr_s ls,
                     ls',
                     ctor_name ctor :: nameList,
                     arity :: arrList)
           end)
         end) ctors 0 ;;
  let '(ls, ls', nameList, arrList) := temp in
  let (gv_names, ty_gv_names) := make_names_gv nameList in
  let gv_arities :=  make_arities_gv arrList in
  let elim_body := (make_case_switch valIdent ls  ls') in
  let elim_fun :=
      Internal ({|
        fn_return := Tvoid;
        fn_callconv := cc_default;
        fn_params := ((valIdent, val) :: (ordIdent, valPtr) :: (argvIdent, argvTy) :: nil);
        fn_vars := nil;
        fn_temps := ((caseIdent, boolTy) :: nil);
        fn_body := elim_body;
      |}) in
  let nenv :=
      set_list ((gv_namesIdent, nNamed (append "names_of_" nTy)) ::
                (gv_aritiesIdent, nNamed (append "arities_of_" nTy)) ::
                (ordIdent, nNamed "ordinal"%bs) ::
                (valIdent, nNamed "val"%bs) ::
                (argvIdent, nNamed "argv"%bs) ::
                (elim_fun_id, nNamed (append "elim_" nTy)) ::
                nil) nenv in
  ret (nenv,
       (gv_namesIdent, gv_names) ::
       (gv_aritiesIdent, gv_arities) ::
       (elim_fun_id, Gfun elim_fun) :: nil).

(* End Clight. (* hide the notations in the Clight section *) *)

Fixpoint make_interface
         (cenv : ctor_env)
         (ienv_list : list (ind_tag * n_ind_ty_info))
         (nenv : name_env)
         : nState (name_env * list (ident * globdef Clight.fundef type)) :=
  match ienv_list with
  | nil => ret (nenv, nil)
  | (_, (nAnon, _)) :: ienv_list' =>
    (* skip anon-types *)
      make_interface cenv ienv_list' nenv
  | (itag, (nNamed nTy, lCtr)) :: ienv_list' =>
      '(nenv, def1) <- make_constructors cenv nTy lCtr nenv ;;
      '(nenv, def2) <- make_eliminator itag cenv nTy lCtr nenv ;;
      '(nenv, def3) <- make_interface cenv ienv_list' nenv ;;
      ret (nenv, (def1 ++ def2 ++ def3))
  end.


Definition make_tinfoIdent := 20%positive.
Definition exportIdent := 21%positive.

(* Definition Tret (x : typ) := *)
(*   match x with *)
(*   | AST.Tlong then  *)

Definition make_tinfo_rec : positive * globdef Clight.fundef type :=
  (make_tinfoIdent,
   Gfun (External (EF_external (String.to_string "make_tinfo")
                               (mksignature (nil) (val_typ) cc_default))
                  Tnil
                  threadInf
                  cc_default)).

Definition export_rec : positive * globdef Clight.fundef type :=
  (exportIdent,
   Gfun (External (EF_external (String.to_string "export")
                               (mksignature (cons val_typ nil) (val_typ) cc_default))
                  (Tcons threadInf Tnil)
                  valPtr
                  cc_default)).


(* generate a function equivalent to halt, received a tinfo, desired results is already in tinfo.args[1], and
 a halting continuation closure *)
Definition make_halt
           (nenv : name_env)
           : nState (name_env * (ident * globdef Clight.fundef type)
                              * (ident * globdef Clight.fundef type)) :=
  haltIdent <- getName;;
  halt_cloIdent <- getName;;
  let nenv := M.set halt_cloIdent (nNamed "halt_clo"%bs)
                (M.set haltIdent (nNamed "halt"%bs) nenv) in
  ret (nenv,
       (haltIdent, Gfun (Internal ({|
          fn_return := Tvoid;
          fn_callconv := cc_default;
          fn_params := (tinfIdent, threadInf) :: nil;
          fn_vars := nil;
          fn_temps := nil;
          fn_body := Sreturn None
        |}))),
       (halt_cloIdent,
        Gvar (mkglobvar (tarray uval 2)
                        ((Init_addrof haltIdent Ptrofs.zero) :: Init_int 1 :: nil)
                        true false))).


(* make b? call^n_export; call^n

call_export has n+1 arguments (all values), returns a value:
 a value containing the function closure
 followed by n arguments to the closure

the arguments are placed in args[2]...args[2+n-1]
halt is placed in args[1]
env is placed in args[0]

if b, then export the resulting value

TODO: fix the access to threadInf with Ederef
TODO: make a global threadinfo variable, make_tinfo if NULL, use it otherwise


 *)

Definition make_call
           (closExpr : expr)
           (fIdent : ident)
           (envIdent : ident)
           (argsExpr : expr)
           (argIdent : ident)
           (haltIdent : ident) : statement :=
  (fIdent ::=  (Field(closExpr , Z.of_nat 0)) ;;;
  envIdent ::= (Field(closExpr, Z.of_nat 1)) ;;;
  (Sassign (Field(argsExpr, Z.of_nat 0)) (Etempvar envIdent val)) ;;;
  (Sassign (Field(argsExpr, Z.of_nat 1)) (Evar haltIdent val)) ;;;
  (Sassign (Field(argsExpr, Z.of_nat 2)) (Etempvar argIdent val)) ;;;
  (call ([pfunTy] (funVar fIdent)))).

Fixpoint make_n_calls
         (n : nat)
         (closIdent : ident)
         (fIdent : ident)
         (envIdent : ident)
         (argsExpr : expr)
         (argPairs : list (ident * type))
         (retIdent : ident)
         (haltIdent : ident) : statement :=
  match n, argPairs with
  | S 0, (argIdent, argTy) :: tl =>
    make_call (Etempvar closIdent valPtr) fIdent envIdent argsExpr argIdent haltIdent
  | S (S n), (argIdent, _) :: tl =>
    let s := make_n_calls (S n) closIdent  fIdent envIdent argsExpr tl retIdent haltIdent in
    s ;;;
    retIdent ::= (Field(argsExpr, Z.of_nat 1)) ;;;
    make_call (Etempvar retIdent valPtr) fIdent envIdent argsExpr argIdent haltIdent
  | _, _ => Sskip
  end.


Definition make_call_n_export_b
           (nenv : name_env)
           (n : nat)
           (export : bool)
           (haltIdent : ident)
           : nState (name_env * (ident * globdef Clight.fundef type)) :=
    callIdent <- getName ;;
    retIdent <- getName ;;
    clo_ident <- getName ;;
    f_ident <- getName ;;
    env_ident <- getName ;;
    t <- make_argList n nenv ;;
    (*    let tinfo_s := if export then (Scall (Some tinfIdent) (Evar make_tinfoIdent make_tinfoTy) nil) else Sskip in *)
    let tinfo_s := Sifthenelse (Ebinop Oeq (Evar tinfIdent threadInf)
                 (Ecast (Econst_int (Int.repr 0) tint) (tptr tvoid)) tint) (Scall (Some tinfIdent) (Evar make_tinfoIdent make_tinfoTy) nil) Sskip in
    let (nenv, argsL) := t in
    let argsS :=  (Efield tinfd argsIdent valPtr) in
    let left_args := make_proj argsS 2 n in
    let asgn_s := make_n_calls n clo_ident f_ident env_ident argsS (rev argsL) retIdent haltIdent in
    let export_s := if export then
                      Scall (Some retIdent) (Evar exportIdent exportTy) (cons tinf nil)
                    else
                       (retIdent ::= (Field(argsS, Z.of_nat 1))) in
    let body_s := Ssequence
                    (tinfo_s ;;; asgn_s)
                    (export_s ;;; Sreturn  (Some (Etempvar retIdent valPtr))) in
    let callStr := append "call_" (MRString.string_of_nat n) in
    let callStr := if export then append callStr "_export" else callStr in
    let nenv :=
      set_list ((env_ident, nNamed "envi"%bs) ::
                (clo_ident, nNamed "clos"%bs) ::
                (callIdent, nNamed callStr) ::
                (f_ident, nNamed "f"%bs) ::
                (retIdent, nNamed "ret"%bs) ::
                nil) nenv in
    (* if export, tinf is local, otherwise is a param *)
    let params := (clo_ident, val) :: argsL in
    let vars := (f_ident, valPtr) :: (env_ident, valPtr) :: (retIdent, valPtr) :: nil in
    ret (nenv, (callIdent, Gfun (Internal ({|
      fn_return := Tpointer Tvoid noattr;
      fn_callconv := cc_default;
      fn_params := params;
      fn_vars := nil;
      fn_temps := vars;
      fn_body := body_s
    |})))).

Definition tinf_def : globdef Clight.fundef type :=
  Gvar (mkglobvar threadInf ((Init_space 4%Z)::nil) false false).

Definition make_empty_header
           (cenv : ctor_env)
           (ienv : n_ind_env)
           (e : exp)
           (nenv : name_env)
           : nState (option (name_env * list (ident * globdef Clight.fundef type))) :=
  ret (Some (nenv, nil)).

Definition make_header
           (cenv : ctor_env)
           (ienv : n_ind_env)
           (e : exp)
           (nenv : M.t BasicAst.name)
           : nState (option (M.t BasicAst.name  * (list (ident * globdef Clight.fundef type)))) :=
  (* l <- make_interface cenv (M.elements ienv) nenv;; *)
  (* let (nenv, inter_l) := l in *)
  l <- make_halt nenv ;;
  let  '(nenv, halt_f, (halt_cloIdent, halt_clo_def)) := l in
  l <- make_call_n_export_b nenv 1 false halt_cloIdent ;;
  let  '(nenv, call_0) := l in
  l <- make_call_n_export_b nenv 2 false halt_cloIdent ;;
  let  '(nenv, call_2) := l in
  l <- make_call_n_export_b nenv 1 true halt_cloIdent ;;
  let  '(nenv, call_1) := l in
  l <- make_call_n_export_b nenv 3 true halt_cloIdent ;;
  let  '(nenv, call_3) := l in
  ret (Some (nenv, (halt_f :: (halt_cloIdent, halt_clo_def) ::
                   (tinfIdent, tinf_def) ::
                   call_0 :: call_1 :: call_2 :: call_3 :: nil))).



(* end of header file *)


Definition compile (e : exp) (cenv : ctor_env) (nenv : M.t BasicAst.name) :
  exceptionMonad.exception (M.t BasicAst.name * option Clight.program * option Clight.program) :=
  let e := wrap_in_fun e in
  let fenv := compute_fun_env e in
  let ienv := compute_ind_env cenv in
  let p'' := make_defs e fenv cenv ienv nenv in
  let n := ((max_var e 100) + 1)%positive in
  let p' :=  (p''.(runState) n) in
  let m := snd p' in
  match fst p' with
  | exceptionMonad.Exc s => exceptionMonad.Exc (append "LambdaANF_to_Clight: Failure in make_defs:" s)
  | exceptionMonad.Ret p =>
    let '(nenv, defs) := p in
    let nenv := (add_inf_vars (ensure_unique nenv)) in
    let forward_defs := make_extern_decls nenv defs false in
    let header_pre := make_empty_header cenv ienv e nenv in
    (*     let header_p := (header_pre.(runState) m%positive) in *)
    let header_p := (header_pre.(runState) 1000000%positive) in (* should be m, but m causes collision in nenv for some reason *)
    (match fst header_p with
     | None => exceptionMonad.Exc "LambdaANF_to_Clight: Failure in make_header"
     | Some (nenv, hdefs) =>
       exceptionMonad.Ret
         ((M.set make_tinfoIdent (nNamed "make_tinfo"%bs)
                (M.set exportIdent (nNamed "export"%bs) nenv),
          mk_prog_opt (body_external_decl ::
                      (make_extern_decls nenv hdefs true)) mainIdent false,
          mk_prog_opt (make_tinfo_rec :: export_rec ::
                      forward_defs ++ defs ++ hdefs) mainIdent true))
     end)
  end.


Definition compile_fast (e : exp) (cenv : ctor_env) (nenv : M.t BasicAst.name) :
  (M.t BasicAst.name * option Clight.program * option Clight.program) :=
  let e := wrap_in_fun e in
  let fenv := compute_fun_env e in
  let ienv := compute_ind_env cenv in
  let p'' := make_defs_fast e fenv cenv ienv nenv in
  let n := ((max_var e 100) + 1)%positive in
  let p' :=  (p''.(runState) n) in
  let m := snd p' in
  match fst p' with
  | None => (nenv, None, None)
  | Some (nenv, defs) =>
    let nenv := (add_inf_vars (ensure_unique nenv)) in
    let forward_defs := make_extern_decls nenv defs false in
    let header_pre := make_empty_header cenv ienv e nenv in
    (*     let header_p := (header_pre.(runState) m%positive) in *)
    let header_p := (header_pre.(runState) 1000000%positive) in (* should be m, but m causes collision in nenv for some reason *)
    (match fst header_p with
     | None => (nenv, None, None)
     | Some (nenv, hdefs) =>
       (M.set make_tinfoIdent (nNamed "make_tinfo"%bs)
              (M.set exportIdent (nNamed "export"%bs) nenv),
        mk_prog_opt (body_external_decl ::
                     (make_extern_decls nenv hdefs true)) mainIdent false,
        mk_prog_opt (make_tinfo_rec :: export_rec ::
                     forward_defs ++ defs ++ hdefs) mainIdent true)
     end)
  end.

Definition err {A : Type} (s : String.string) : res A :=
  Error ((MSG s) :: nil).

Definition empty_program : Clight.program :=
  Build_program nil nil mainIdent nil eq_refl.

Definition stripOption (p : (option Clight.program)) : Clight.program :=
  match p with
  | None => empty_program
  | Some p' => p'
  end.


End TRANSLATION.
