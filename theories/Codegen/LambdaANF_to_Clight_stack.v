Require Import Common.compM.

From Stdlib Require Import ZArith.ZArith
        Program.Basics
        Strings.String
        Lists.List Lia.
Require Import List_util.
From Stdlib Require PrimInt63 PrimString Uint63.
Require Import List_util.

Definition char_to_Z x := Uint63.to_Z x.
Import ListNotations.
Open Scope list_scope.

(* Use the same byte-packing encoding as OCaml
  https://ocaml.org/docs/memory-representation#string-values *)
Fixpoint encode_list (l : list PrimString.char63) : list Z :=
  match l with
  | nil => [7 * two_power_pos 56]
  | [ x ] =>
      [6 * two_power_pos 56 + char_to_Z x]
  | x :: y :: [] =>
      [5 * two_power_pos 56 + char_to_Z x +
      two_power_pos 8 * char_to_Z y]
  | x :: y :: z :: [] =>
      [4 * two_power_pos 56 + char_to_Z x +
      two_power_pos 8 * char_to_Z y +
      two_power_pos 16 * char_to_Z z]
  | x :: y :: z :: w :: [] =>
      [3 * two_power_pos 56 + char_to_Z x +
      two_power_pos 8 * char_to_Z y +
      two_power_pos 16 * char_to_Z z +
      two_power_pos 24 * char_to_Z w]
  | x :: y :: z :: w :: lx :: [] =>
      [2 * two_power_pos 56 + char_to_Z x +
      two_power_pos 8 * char_to_Z y +
      two_power_pos 16 * char_to_Z z +
      two_power_pos 24 * char_to_Z w +
      two_power_pos 32 * char_to_Z lx]
  | x :: y :: z :: w :: lx :: ly :: [] =>
      [1 * two_power_pos 56 + char_to_Z x +
      two_power_pos 8 * char_to_Z y +
      two_power_pos 16 * char_to_Z z +
      two_power_pos 24 * char_to_Z w +
      two_power_pos 32 * char_to_Z lx +
      two_power_pos 40 * char_to_Z ly]
  | x :: y :: z :: w :: lx :: ly :: lz :: [] =>
      [char_to_Z x +
      two_power_pos 8 * char_to_Z y +
      two_power_pos 16 * char_to_Z z +
      two_power_pos 24 * char_to_Z w +
      two_power_pos 32 * char_to_Z lx +
      two_power_pos 40 * char_to_Z ly +
      two_power_pos 48 * char_to_Z lz]
  | x :: y :: z :: w :: lx :: ly :: lz :: lw :: l =>
      (char_to_Z x +
      two_power_pos 8 * char_to_Z y +
      two_power_pos 16 * char_to_Z z +
      two_power_pos 24 * char_to_Z w +
      two_power_pos 32 * char_to_Z lx +
      two_power_pos 40 * char_to_Z ly +
      two_power_pos 48 * char_to_Z lz +
      two_power_pos 56 * char_to_Z lw)
      :: encode_list l
  end%Z.

Require Import ExtLib.Structures.Monads
        ExtLib.Data.Monads.OptionMonad
        ExtLib.Data.Monads.StateMonad.

Import MonadNotation ListNotations.
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

Require Import
  LambdaANF.set_util
  LambdaANF.cps
  LambdaANF.identifiers
  LambdaANF.cps_show
  LambdaANF.state
  LambdaANF.toplevel.

From MetaRocq.Utils Require Import bytestring MRString.
Section TRANSLATION.

(* Stand-in for arbitrary identifiers *)
Variable (argsIdent : ident).
Variable (allocIdent : ident).
Variable (nallocIdent : ident).
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
Variable (resultIdent : ident).
(* resultIdent is used for returning the function call result in the Eapp case.
   Clight doesn't allow returning the function call expression
   because function calls are only available as statements in Clight.
   We could have generated unique identifiers
   but that might have required refactoring LambdaANF expressions. *)
Variable (nParam:nat).

Variable (prims : prim_env).

Definition show_name (name : BasicAst.name) : string :=
  match name with
  | nAnon => "anon"
  | nNamed d => d
  end.

Definition get_fname f (nenv : name_env) : string :=
  match M.get f nenv with
  | Some name => show_name name
  | None => "Undef"
  end.

Definition maxArgs : Z := 1024%Z.

(* temporary function to get something working *)
(* returns (n-1) :: (n-2) :: ... :: 0 :: nil for a list of size n *)
Fixpoint makeArgList' (vs : list positive) : list N :=
  match vs with
  | nil => nil
  | x :: vs' => (N.of_nat (length vs')) :: (makeArgList' vs')
  end.

Definition makeArgList (vs : list positive) : list N :=
  rev (makeArgList' vs).


Definition fun_info_env : Type := M.t (positive * fun_tag).

(* Compute a fun_env by looking at the number of arguments functions
   are applied to, assumes that all functions sharing the same tags have the same arity *)
Fixpoint compute_fun_env'
         (n : nat)
         (nenv : name_env)
         (fenv : fun_env)
         (e : exp) : fun_env :=
  match n with
  | 0 => fenv
  | S n' =>
    match e with
    | Econstr x t vs e' => compute_fun_env' n' nenv fenv e'
    | Ecase x cs => fold_left (fun p e => compute_fun_env' n' nenv p e) (map snd cs) fenv
    | Eproj x t n v e' => compute_fun_env' n' nenv fenv e'
    | Eletapp x f t vs e' =>
      compute_fun_env' n' nenv (M.set t (N.of_nat (length vs), makeArgList vs) fenv) e'
    | Efun fnd e' =>
      let fenv' := compute_fun_env_fundefs n' nenv fnd fenv in
      compute_fun_env' n' nenv fenv' e'
    | Eapp x t vs => M.set t (N.of_nat (length vs) , makeArgList vs) fenv
    | Eprim_val x p e' => compute_fun_env' n' nenv fenv e'
    | Eprim x p vs e' => compute_fun_env' n' nenv fenv e'
    | Ehalt x => fenv
    end
  end
with compute_fun_env_fundefs
     (n : nat)
     (nenv : name_env)
     (fnd : fundefs)
     (fenv : fun_env) : fun_env :=
  match n with
  | 0 => fenv
  | S n' =>
    match fnd with
    | Fnil => fenv
    | Fcons f t vs e fnd' =>
      let fenv' := M.set t (N.of_nat (length vs) , makeArgList vs) fenv in
      let fenv'' := compute_fun_env' n' nenv fenv' e in
      compute_fun_env_fundefs n' nenv fnd' fenv''
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
with max_depth_fundefs (fnd : fundefs) :=
  match fnd with
  | Fnil => S 0
  | Fcons _ _ _ e fnd' => S (Nat.max (max_depth e) (max_depth_fundefs fnd'))
  end.

(* fun_env maps tags to function info *)
Definition compute_fun_env (nenv : name_env) (e : exp) : fun_env :=
  compute_fun_env' (max_depth e) nenv (M.empty fun_ty_info) e.

(* Computes the local variables of a function body *)
Fixpoint get_locals (e : exp) : list positive :=
  match e with
  | Econstr x t vs e' => x :: (get_locals e')
  | Ecase x cs =>
    (fix helper (cs : list (ctor_tag * exp)) :=
       match cs with
       | nil => nil
       | cons (z, e') cs' => (get_locals e' ++ helper cs')%list
       end) cs
  | Eproj x t n v e' => x :: (get_locals e')
  | Eletapp x f t xs e' => x :: (get_locals e')
  | Efun fnd e' => (get_locals_fundefs fnd) ++ (get_locals e')
  | Eapp x t vs => nil
  | Eprim_val x p e' => x :: (get_locals e')
  | Eprim x p vs e' => x :: (get_locals e')
  | Ehalt x => nil
  end
with get_locals_fundefs (fnd : fundefs) :=
  match fnd with
  | Fnil => nil
  | Fcons f t vs e fnd' => vs ++ (get_locals e) ++ (get_locals_fundefs fnd')
  end.

(* Max number of value-sized words allocated by the translation of expression e until the next function call
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
  | Eletapp x f t ys e' => 0
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

(* Computes the max number of parameters a function has in the term exp  *)
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


(* named ienv *)
(* TODO: move this to cps and replace the current definition of ind_ty_info *)
(* 1) name of inductive type
   2) list containing
      2.1 name of the constructor
      2.2 tag of the contructor (in ctor_env)
      2.3 arity of the constructor
      2.4 ordinal of the constructor *)
Definition n_ind_ty_info : Type := BasicAst.name * list (BasicAst.name * ctor_tag * N * N).

Definition n_ind_env := M.t n_ind_ty_info.

Definition update_ind_env
           (ienv : n_ind_env)
           (p : positive)
           (cInf : ctor_ty_info) : n_ind_env :=
  let '{| ctor_name := name
        ; ctor_ind_name := nameTy
        ; ctor_ind_tag := t
        ; ctor_arity := arity
        ; ctor_ordinal := ord
        |} := cInf in
  match (M.get t ienv) with
  | None => M.set t (nameTy, ((name, p, arity, ord) :: nil)) ienv
  | Some (nameTy, iInf) => M.set t (nameTy, (name, p, arity, ord) :: iInf) ienv
  end.

Definition compute_ind_env (cenv : ctor_env) : n_ind_env :=
  M.fold update_ind_env cenv (M.empty _).


Inductive ctor_rep : Type :=
| enum : N -> ctor_rep
(* [enum t] represents a constructor with no parameters with ordinal [t] *)
| boxed : N -> N -> ctor_rep.
(* [boxed t a] represents a construct with arity [a] and ordinal [t]  *)


Definition make_ctor_rep (cenv : ctor_env) (ct : ctor_tag) : error ctor_rep :=
  match M.get ct cenv with
  | Some p =>
    if ((ctor_arity p) =? 0)%N
    then ret (enum (ctor_ordinal p))
    else ret (boxed (ctor_ordinal p) (ctor_arity p))
  | None => Err ("make_ctor_rep: unknown constructor with tag " ++ show_pos ct)
  end.

Notation threadStructInf := (Tstruct threadInfIdent noattr).
Notation threadInf := (Tpointer threadStructInf noattr).


Notation intTy := (Tint I32 Signed
                        {| attr_volatile := false; attr_alignas := None |}).

Notation uintTy := (Tint I32 Unsigned
                         {| attr_volatile := false; attr_alignas := None |}).

Notation longTy := (Tlong Signed
                          {| attr_volatile := false; attr_alignas := None |}).

Notation ulongTy := (Tlong Unsigned
                           {| attr_volatile := false; attr_alignas := None |}).


Definition int_chunk := if Archi.ptr64 then Mint64 else Mint32.
(* NOTE for val: in Clight, SIZEOF_PTR == SIZEOF_INT *)

Definition val : type := talignas (if Archi.ptr64 then 3%N else 2%N) (tptr tvoid).
(* Definition val := if Archi.ptr64 then ulongTy else uintTy. *)
Definition uval := if Archi.ptr64 then ulongTy else uintTy.
Definition sval := if Archi.ptr64 then longTy else intTy.
Definition val_typ := if Archi.ptr64 then  Xlong else (Xany32:xtype).
Definition Init_int x := if Archi.ptr64 then (Init_int64 (Int64.repr x)) else (Init_int32 (Int.repr x)).
Definition make_vint (z:Z) := if Archi.ptr64 then Vlong (Int64.repr z) else Values.Vint (Int.repr z).
Definition make_cint z t := if Archi.ptr64 then Econst_long (Int64.repr z) t else (Econst_int (Int.repr z) t).
Transparent val.
Transparent uval.
Transparent val_typ.
Transparent Init_int.
Transparent make_vint.
Transparent make_cint.

Notation Tcons := cons.
Notation Tnil := nil.
Notation typelist := (list type).

Notation funTy := (Tfunction (threadInf :: nil) val cc_default).

Notation pfunTy := (Tpointer funTy noattr).

Notation gcTy := (Tfunction ((Tpointer val noattr) :: threadInf :: nil) Tvoid cc_default).

Notation isptrTy := (Tfunction (Tcons val Tnil) (Tint IBool Unsigned noattr) cc_default).

Notation valPtr := (Tpointer val {| attr_volatile := false; attr_alignas := None |}).
Notation valPtrPtr := (Tpointer valPtr {| attr_volatile := false; attr_alignas := None |}).

Notation argvTy := (Tpointer val {| attr_volatile := false; attr_alignas := None |}).

Definition floatType := Tfloat F64 noattr.
Notation floatPtr := (Tpointer floatType {| attr_volatile := false; attr_alignas := None |}).

Notation boolTy := (Tint IBool Unsigned noattr).

Fixpoint mkFunTyList (n : nat) : typelist :=
  match n with
  | 0 => Tnil
  | S n' => Tcons val (mkFunTyList n')
  end.

Definition mkFunTy (n : nat) :=
  (Tfunction (Tcons threadInf (mkFunTyList n)) val cc_default).

Definition mkPrimTy (n : nat) :=
  (Tfunction (mkFunTyList n) val cc_default).

Definition mkPrimTyTinfo (n : nat) :=
  (Tfunction (Tcons threadInf (mkFunTyList n)) val cc_default).


Notation "'var' x" := (Etempvar x val) (at level 20).
Notation "'ptrVar' x" := (Etempvar x valPtr) (at level 20).
Notation "'ptrptrVar' x" := (Etempvar x valPtrPtr) (at level 20).

Notation "'bvar' x" := (Etempvar x boolTy) (at level 20).
Notation "'funVar' x" := (Evar x funTy) (at level 20).

Notation allocPtr := (Etempvar allocIdent valPtr).
Notation limitPtr := (Etempvar limitIdent valPtr).
Notation args := (Etempvar argsIdent valPtr).
Notation gc := (Evar gcIdent gcTy).
Notation ptr := (Evar isptrIdent isptrTy).

(* changed tinf to be tempvar and have type Tstruct rather than Tptr Tstruct *)
Notation tinf := (Etempvar tinfIdent threadInf).
Notation tinfd := (Ederef tinf threadStructInf).

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

Notation " p ';' q " := (seq p q)
                         (at level 100, format " p ';' '//' q ").

Notation " a '::=' b " := (Sset a b) (at level 50).
Notation " a ':::=' b " := (Sassign a b) (at level 50).

Notation "'*' p " := (Ederef p val) (at level 40).

Notation "'&' p " := (Eaddrof p valPtr) (at level 40).

Definition c_int' n t := if Archi.ptr64 then Econst_long (Int64.repr n) t else Econst_int (Int.repr n%Z) t.

Notation c_int := c_int'.

Notation "'while(' a ')' '{' b '}'" :=
  (Swhile a b) (at level 60).

Notation "'call' f " := (Scall None f (tinf :: nil)) (at level 35).

Notation "'[' t ']' e " := (Ecast e t) (at level 34).

Notation "'Field(' t ',' n ')'" :=
  ( *(add ([valPtr] t) (c_int n%Z val))) (at level 36). (* what is the type of int being added? *)

Notation "'args[' n ']'" :=
  ( *(add args (c_int n%Z val))) (at level 36).


(** * Shadow stack definitions *)

(* Stack-related ids *)
Variable (stackframeTIdent : ident). (* the stack_frame type *)
Variable (frameIdent : ident). (* the stack frame of the current function *)
Variable (rootIdent : ident). (* live roots array *)
Variable (fpIdent : ident). (* frame pointer, part of thread_info *)
(* Fields of stack_frame struct *)
Variable (nextFld : ident).
Variable (rootFld : ident).
Variable (prevFld : ident).

(* The type of the stack_frame struct *)
Definition stackframeT := Tstruct stackframeTIdent noattr.
(* The type of a pointer the stack_frame struct *)
Definition stackframeTPtr := Tpointer stackframeT noattr.
(* The type of the root array for each frame. *)
Definition rootT size := Tarray val size noattr.
(* Pointer to the root array *)
Definition rootTPtr := valPtr.

(* local vars declared when a function uses the stack *)
(* struct stack_frame frame; val roots[MAX_LOCS]; *)
Definition stack_decl size : list (ident * type)  :=
  (frameIdent, stackframeT) :: (* local variable for local stack frame *)
  (rootIdent, rootT size) :: nil. (* local variable for the live array *)

(* Notation for handling the roots array *)
Notation roots := (Evar rootIdent valPtr).
Notation "'roots[' n ']'" := ( *(add roots (c_int n%Z val))) (at level 36).

(* Initialize local stack frame. Called before the first function call that uses the current stack *)
Definition init_stack : statement :=
  (* frame.next = roots; *)
  (Efield (Evar frameIdent stackframeT) nextFld valPtr :::= Evar rootIdent rootTPtr);
  (* frame.roots = roots; *)
  (Efield (Evar frameIdent stackframeT) rootFld rootTPtr :::= Evar rootIdent rootTPtr);
  (* frame.prev = tinf->fp; *)
  (Efield (Evar frameIdent stackframeT) prevFld stackframeTPtr :::= Efield tinfd fpIdent stackframeTPtr).


(* Updates the stack pointer and frame pointers before a call *)
(* b is true if the stack is already set. I.e. it's a call to the GC after a normal call *)
Definition set_stack (sp : N) (b : bool) : statement :=
if ((sp =? 0)%N || b)%bool then Sskip else
  (* tinfo->fp = &frame; *)
  (Efield tinfd fpIdent stackframeTPtr :::= Eaddrof (Evar frameIdent stackframeT) stackframeTPtr).

(* Updates the stack pointer and frame pointers before a call *)
Definition update_stack (sp : N) : statement :=
  if (sp =? 0)%N then Sskip else
    (* frame.next = root + SP *)
    (Efield (Evar frameIdent stackframeT) nextFld valPtr :::= (add roots (c_int (Z.of_N sp) val))).

(* Resets the frame pointer after a call, so that if subsequent calls don't use the stack the empty frame is not pushed. *)
(* b is true if it's a call to the GC after a normal call, so the stack will be reset anyway *)
Definition reset_stack (sp : N) (b : bool) : statement :=
  if ((sp =? 0)%N || b)%bool then Sskip else
   (* Current frame points to the old frame again *)
   Efield tinfd fpIdent stackframeTPtr :::= Efield (Evar frameIdent stackframeT) prevFld valPtr.

(* Pushes single var in frame *)
Definition push_var (sp : N) (x : positive) :=
  roots[ Z.of_N sp ] :::= Etempvar x valPtr.

(* Pops single var from frame *)
Definition pop_var (sp : N) (x : positive) :=
  x ::= roots[ Z.of_N sp ].

Definition push_live_vars_offset (off : N) (xs : list positive) : statement * N :=
  (fix aux xs (n : N) (stmt : statement) : statement * N :=
     match xs with
     | nil => (stmt, n)
     | x :: xs => aux xs (n+1)%N (push_var n x; stmt)
     end) xs off Sskip.

Definition pop_live_vars_offset (off : N) (xs : list positive) : statement :=
  (fix aux xs n stmt : statement :=
     match xs with
     | nil => stmt
     | x :: xs => aux xs (n+1)%N (pop_var n x; stmt)
     end) xs off Sskip.

Definition push_live_vars (xs : list positive) : statement * N := push_live_vars_offset 0%N xs.

Definition pop_live_vars (xs : list positive) : statement := pop_live_vars_offset 0%N xs.

(** * Shadow stack defs END *)

(* Don't shift the tag for boxed, make sure it is under 255 *)
Definition makeTagZ (cenv:ctor_env) (ct : ctor_tag) : error Z :=
  p <- make_ctor_rep cenv ct ;;
  match p with
  | enum t => ret ((Z.shiftl (Z.of_N t) 1) + 1)%Z
  | boxed t a => ret ((Z.shiftl (Z.of_N a) 10) + (Z.of_N t))%Z
  end.

Definition makeTag (cenv: ctor_env) (ct : ctor_tag) : error expr :=
  t <- makeTagZ cenv ct ;;
  ret (c_int t val).

Definition mkFunVar x (locs : list N) := (Evar x (mkFunTy (length (firstn nParam locs)))).

Definition makeVar (x:positive) (fenv : fun_env) (map :fun_info_env) :=
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
         (vs : list positive) : statement :=
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
    (Field(var x, Z.of_nat cur) :::= (*[val]*) vv; prog)
  end.

Definition assignConstructorS
           (cenv : ctor_env)
           (ienv : n_ind_env)
           (fenv : fun_env)
           (map: fun_info_env)
           (x : positive)
           (t : ctor_tag)
           (vs : list positive) : error statement :=
  tag <- makeTag cenv t;;
  rep <- make_ctor_rep cenv t ;;
  match rep with
  | enum _ =>
    ret (x ::= tag)
  | boxed _ a =>
    let stm := assignConstructorS' fenv map x 0 vs in
    ret (x ::= [val] (allocPtr +' (c_int Z.one val));
         allocIdent ::= allocPtr +'
         (c_int (Z.of_N (a + 1)) val) ;
         Field(var x, -1) :::= tag; stm)
      end.

(* Zoe: inlining the isPtr function to avoid extra function call in C *)
Definition isPtr
           (retId : positive)
           (v : positive) : expr:=
  Ebinop Oeq (Ebinop Oand (Etempvar v val) (Econst_int Int.one intTy) boolTy)
         (Econst_int Int.zero intTy) boolTy.


Fixpoint mkCallVars
         (fenv : fun_env)
         (map: fun_info_env)
         (n : nat)
         (vs : list positive) : error (list expr) :=
  match n , vs with
  | 0 , nil => ret nil
  | S n , cons v vs' =>
    let vv := makeVar v fenv map in
    rest <- mkCallVars fenv map n vs' ;;
    ret (vv :: rest)
  | _ , _ => Err "mkCallVars"
  end.

Definition mkCall
           (loc : option positive)
           (fenv : fun_env)
           (map: fun_info_env)
           (f : expr)
           (n : nat)
           (vs : list positive) : error statement :=
  v <- mkCallVars fenv map n (firstn nParam vs) ;;
  ret (Scall loc f (tinf :: v)).

Definition mkPrimCall
           (res : positive)
           (pr : positive)
           (ar : nat)
           (fenv : fun_env)
           (map: fun_info_env)
           (vs : list positive) : error statement :=
  args <- mkCallVars fenv map ar vs ;;
  ret (Scall (Some res) ([mkPrimTy ar] (Evar pr (mkPrimTy ar))) args).

Definition mkPrimCallTinfo
           (res : positive)
           (pr : positive)
           (ar : nat)
           (fenv : fun_env)
           (map: fun_info_env)
           (vs : list positive) : error statement :=
  args <- mkCallVars fenv map ar vs ;;
  ret (Scall (Some res) ([mkPrimTyTinfo ar] (Evar pr (mkPrimTyTinfo ar))) (tinf :: args)).


Fixpoint asgnFunVars' (vs : list positive) (ind : list N) : error statement :=
  match vs with
  | nil =>
    match ind with
    | nil => ret Sskip
    | cons _ _ => Err "asgnFunVars': nill expected"
    end
  | cons v vs' =>
    match ind with
    | nil => Err "asgnFunVars': cons expected"
    | cons i ind' =>
      rest <- asgnFunVars' vs' ind' ;;
      ret  (v ::= args[ Z.of_N i ] ; rest)
    end
  end.

Definition asgnFunVars (vs : list positive) (ind : list N) : error statement :=
  asgnFunVars' (skipn nParam vs) (skipn nParam ind).


Fixpoint asgnAppVars''
         (vs : list positive)
         (ind : list N)
         (fenv : fun_env)
         (map : fun_info_env)
         (name : string) : error statement :=
  match vs, ind with
  | nil, nil => ret Sskip
  | cons v vs' , cons i ind' =>
    let s_iv :=  args[ Z.of_N i ] :::= (makeVar v fenv map) in
    rest <- asgnAppVars'' vs' ind' fenv map name ;;
    ret (rest ; s_iv)
  | _, _ => Err ("asgnAppVars'' " ++ name)%bs
  end.

Definition asgnAppVars'
           (vs : list positive)
           (ind : list N)
           (fenv : fun_env)
           (map : fun_info_env) (name : string) : error statement :=
  asgnAppVars'' (skipn nParam vs) (skipn nParam ind) fenv map name.

Fixpoint get_ind {A} (Aeq : A -> A -> bool) (l : list A) (a : A) : error nat :=
  match l with
  | nil => Err "get_ind: cons expected"
  | x :: l' =>
    match Aeq a x with
    | true => ret 0
    | false =>
      n <- get_ind Aeq l' a ;;
      ret (S n)
    end
  end.

Fixpoint remove_AppVars
         (myvs vs : list positive)
         (myind ind : list N) : error (list positive * list N) :=
  match vs , ind with
  | nil , nil => ret (nil , nil)
  | v :: vs , i :: ind =>
    '(vs' , ind') <- remove_AppVars myvs vs myind ind ;;
     n <- get_ind Pos.eqb myvs v ;;
     match nth_error myind n with
     | Some i' =>
       match N.eqb i i' with
       | true => ret (vs' , ind')
       | false => ret (v :: vs' , i :: ind')
       end
     | None => ret (v :: vs' , i :: ind')
     end
  | _ , _ => Err "remove_AppVars"
  end.

Definition asgnAppVars_fast' (myvs vs : list positive) (myind ind : list N) (fenv : fun_env) (map : fun_info_env) name : error statement :=
  '(vs' , ind') <- remove_AppVars myvs (skipn nParam vs) myind (skipn nParam ind) ;;
  asgnAppVars'' vs' ind' fenv map name.

(* Optional, reduce register pressure *)
Definition asgnAppVars vs ind (fenv : fun_env) (map : fun_info_env) name :=
  s <- asgnAppVars' vs ind fenv map name ;;
  ret (argsIdent ::= Efield tinfd argsIdent (Tarray uval maxArgs noattr);s).

Definition asgnAppVars_fast myvs vs myind ind (fenv : fun_env) (map : fun_info_env) name :=
  s <- asgnAppVars_fast' myvs vs myind ind fenv map name ;;
  ret (argsIdent ::= Efield tinfd argsIdent (Tarray uval maxArgs noattr);s).

Definition set_nalloc (num : expr) : statement :=
  Efield tinfd nallocIdent val :::= num.

(** * GC call *)
Definition make_GC_call (num_allocs : nat) (stack_vars : list positive) (stack_offset : N) : statement * N :=
  let after_call := negb (stack_offset =? 0)%N in
  let (push, slots) := push_live_vars_offset stack_offset stack_vars in
  let make_gc_stack := push ; update_stack slots ; set_stack slots after_call in
  let discard_stack := pop_live_vars_offset stack_offset stack_vars; reset_stack slots after_call in
  let nallocs := c_int (Z.of_nat num_allocs) val in
  if (num_allocs =? 0)%nat then (Sskip, stack_offset) else
    ((Sifthenelse
        (!(Ebinop Ole nallocs (limitPtr -' allocPtr) type_bool))
        (make_gc_stack;
         set_nalloc nallocs;
         Scall None gc (tinf :: nil) ;
         discard_stack;
         allocIdent ::= Efield tinfd allocIdent valPtr; limitIdent ::= Efield tinfd limitIdent valPtr)
        Sskip), slots).

Definition make_case_switch
          (x : positive)
          (ls : labeled_statements)
          (ls': labeled_statements) : statement :=
  (Sifthenelse
     (isPtr caseIdent x)
     (Sswitch (Ebinop Oand (Field(var x, -1)) (make_cint 255 val) val) ls)
     (Sswitch (Ebinop Oshr (var x) (make_cint 1 val) val)
              ls')).


(** * Shadow stack strategy *)
(* ZOE TODO: update text

 1. Before the first non-tail call create a local (stored in the stack) array and a frame
    struct with pointer to the array and the previous frame. Modify the stack pointer of
    tinfo to point to the newly created stack frame
 2. Before the last (tail) call or return modify tinfo to point to the previous stack frame

 *)

(* To create the shadow stack:

   long long int live[MAX_live];
   frame_pointer fp = { next = *live; roots=*live; prev:=tinfo->sp}
   long long int *next = fp.next;
   tinfo->sp = *fp
 *)

(* To push a value to the shadow stack:

   live[NEXT] := x;
   next = next + 1LLU;
*)

(* To discard the current stack:

  tinfo->sp = fp.prev
*)


(* Create a new shadow stack frame *)
(* Definition make_shadow_stack () : statement :=  *)

(* The program returns the translated code and the set of live vars at the next call *)

Definition to_int64 (i : PrimInt63.int) : int64.
  exists (Uint63.to_Z i * 2 + 1)%Z.
  pose proof (Uint63.to_Z_bounded i).
  unfold Uint63.wB in H. unfold Int64.modulus, Int64.wordsize, Wordsize_64.wordsize.
  unfold Uint63.size in H. rewrite two_power_nat_correct. unfold Zpower_nat. simpl.
  destruct H. split. lia. lia.
Defined.

Definition float64_to_model (f : PrimFloat.float) : float64_model :=
  exist (FloatOps.Prim2SF f) (FloatAxioms.Prim2SF_valid f).

Definition model_to_binary (f : float64_model) : Floats.float :=
  match proj1_sig f as x return is_true (SpecFloat.valid_binary FloatOps.prec FloatOps.emax x) -> Floats.float with
  | SpecFloat.S754_zero s => fun _ => Binary.B754_zero _ _ s
  | SpecFloat.S754_infinity s => fun _ => Binary.B754_infinity _ _ s
  | SpecFloat.S754_nan => fun _ => Binary.B754_nan FloatOps.prec FloatOps.emax false xH eq_refl
  | SpecFloat.S754_finite s m e => fun h => Binary.B754_finite _ _ s m e h
  end (proj2_sig f).

Definition to_float (f : PrimFloat.float) : Floats.float :=
  model_to_binary (float64_to_model f).

Definition compile_float (cenv : ctor_env) (ienv : n_ind_env) (fenv : fun_env) (map : fun_info_env)
  (x : positive) (f : Floats.float) :=
  let tag := c_int 1277 %Z (Tlong Unsigned noattr) in
  x ::= [val] (allocPtr +' (c_int Z.one val)) ;
  allocIdent ::= allocPtr +' (c_int 2 val) ;
  Field(var x, -1) :::= tag ;
  *([floatPtr] (var x)) :::= Econst_float f floatType.

Definition compile_string (cenv : ctor_env) (ienv : n_ind_env) (fenv : fun_env) (map : fun_info_env)
  (x : positive) (f : PrimString.string) :=
  let len := Uint63.to_Z (PrimString.length f) in
  let words := ((len / 8) + 1)%Z in
  let tag := c_int (words * two_power_pos 10 + 252) (Tlong Unsigned noattr) in
  x ::= [val] (allocPtr +' (c_int Z.one val)) ;
  allocIdent ::= allocPtr +' (c_int (words + 1) val) ;
  let acc := Field(var x, -1) :::= tag in
  let l := PrimStringAxioms.to_list f in
  MRList.fold_left_i
    (fun acc i ch =>
       acc ;
       Field(var x, Z.of_nat i) :::= Econst_long (Int64.repr ch) (Tlong Unsigned noattr)) (encode_list l) acc.

Definition compile_primitive (cenv : ctor_env) (ienv : n_ind_env) (fenv : fun_env) (map : fun_info_env) (x : positive) (p : AstCommon.primitive_value) : statement :=
  match projT1 p as tag return AstCommon.prim_value tag -> statement with
  | AstCommon.primInt => fun i => x ::= Econst_long (to_int64 i) (Tlong Unsigned noattr)
  | AstCommon.primFloat => fun f => compile_float cenv ienv fenv map x (to_float f)
  | AstCommon.primString => fun f => compile_string cenv ienv fenv map x f
  end (projT2 p).

Section Translation.

  Context (args_opt : bool).

  Section Body.
    Context
      (prim_map : list (kername * string * nat * positive))
      (fun_vars : list positive)
      (loc_vars : FVSet) (* The set of local vars including definitions and arguments *)
      (locs : list N)
      (nenv : name_env).

(* Returns the statement and the number of stack slots needed *)

    Fixpoint translate_body
             (e : exp)
             (fenv : fun_env)
             (cenv : ctor_env)
             (ienv : n_ind_env)
             (map : fun_info_env)
             (slots : N) : error (statement * N):=
      match e with
      | Econstr x t vs e' =>
        prog <- assignConstructorS cenv ienv fenv map x t vs ;;
        progn <- translate_body e' fenv cenv ienv map slots ;;
        ret ((prog ; (fst progn)), snd progn)
      | Ecase x cs =>
        p <- ((fix makeCases (l : list (ctor_tag * exp)) : error (labeled_statements * labeled_statements * N) :=
                 match l with
                 | nil => ret (LSnil, LSnil, slots)
                 | cons p l' =>
                   progn <- translate_body (snd p) fenv cenv ienv map slots ;;
                   pn <- makeCases l' ;;
                   let (prog, n) := (progn : statement * N) in
                   let '(ls , ls', n') := (pn : labeled_statements * labeled_statements * N) in
                   p <- make_ctor_rep cenv (fst p) ;;
                   match p with
                   | boxed t a =>
                     let tag := ((Z.shiftl (Z.of_N a) 10) + (Z.of_N t))%Z in
                     (match ls with
                      | LSnil =>
                        ret ((LScons None (Ssequence prog Sbreak) ls), ls', N.max n n')
                      | LScons _ _ _ =>
                        ret ((LScons (Some (Z.land tag 255)) (Ssequence prog Sbreak) ls), ls', N.max n n')
                      end)
                   | enum t =>
                     let tag := ((Z.shiftl (Z.of_N t) 1) + 1)%Z in
                     (match ls' with
                      | LSnil =>
                        ret (ls, (LScons None (Ssequence prog Sbreak) ls'), N.max n n')
                      | LScons _ _ _ =>
                        ret (ls, (LScons (Some (Z.shiftr tag 1)) (Ssequence prog Sbreak) ls'), N.max n n')
                      end)
                   end
                 end) cs) ;;
        let '(ls , ls', slots') := p in
        ret ((make_case_switch x ls ls'), slots')
      | Eletapp x f t vs e' =>
        (* Compute the local variables that are live after the call  *)
        let fvs_post_call := PS.inter (exp_fv e') loc_vars in
        let fvs := PS.remove x fvs_post_call in
        let fvs_list := PS.elements fvs in
        (* Check if the new binding has to be pushed to the frame during the GC call *)
        let fv_gc := if PS.mem x fvs_post_call then cons x nil else nil in
        (* push live vars to the stack. We're pushing exactly the vars that are live beyond the current point. *)
        let '(make_stack, slots_call) :=
            let (push, slots) := push_live_vars fvs_list in
            (push ; update_stack slots; set_stack slots false, slots)
        in
        match M.get t fenv return (error (statement * N)) with
        | Some inf =>
          let name :=
              match M.get f nenv with
              | Some n => show_name n
              | None => "not an entry"
              end
          in
          asgn <- (if args_opt then asgnAppVars_fast fun_vars vs locs (snd inf) fenv map name
                   else asgnAppVars vs (snd inf) fenv map name) ;;
          let f_var := makeVar f fenv map in
          let pnum := min (N.to_nat (fst inf)) nParam in
          c <- (mkCall (Some x) fenv map ([Tpointer (mkFunTy pnum) noattr] f_var) pnum vs) ;;
          let alloc := max_allocs e' in
          (* Call GC after the call if needed *)
          let (gc_call, slots_gc) := make_GC_call alloc fv_gc slots_call in
          (* Pop live vars from the stack *)
          let discard_stack := pop_live_vars fvs_list; reset_stack slots_call false in
          progn <- translate_body e' fenv cenv ienv map (N.max slots slots_gc);;
          Ret ((asgn ; Efield tinfd allocIdent valPtr :::= allocPtr ; Efield tinfd limitIdent valPtr  :::= limitPtr;
               make_stack;
               c;
               allocIdent ::= Efield tinfd allocIdent valPtr;
               limitIdent ::= Efield tinfd limitIdent valPtr;
               gc_call;
               discard_stack;
               fst progn),
               snd progn)
        | None => Err "translate_body: Unknown function application in Eletapp"
        end
  | Eproj x t n v e' =>
    progn <- translate_body e' fenv cenv ienv map slots ;;
    Ret ((x ::= Field(var v, Z.of_N n) ; fst progn), snd progn)
  | Efun fnd e => Err "translate_body: Nested function detected"
  | Eapp x t vs =>
    match M.get t fenv with
    | Some inf =>
      let name :=
          match M.get x nenv with
          | Some n => show_name n
          | None => "not an entry"
          end
      in
      asgn <- (if args_opt then asgnAppVars_fast fun_vars vs locs (snd inf) fenv map name else asgnAppVars vs (snd inf) fenv map name) ;;
      let f_var := makeVar x fenv map in
      let pnum := min (N.to_nat (fst inf)) nParam in
      (* Using the same result identifier every time *)
      c <- (mkCall (Some resultIdent) fenv map ([Tpointer (mkFunTy pnum) noattr] f_var) pnum vs) ;;
      ret (asgn ;
           Efield tinfd allocIdent valPtr :::= allocPtr ;
           Efield tinfd limitIdent valPtr :::= limitPtr ;
           c ;
           Sreturn (Some (makeVar resultIdent fenv map)),
           slots)
    | None => Err "translate_body: Unknown function application in Eapp"
    end
  | Eprim_val x p e' =>
    progn <- translate_body e' fenv cenv ienv map slots ;;
    Ret ((compile_primitive cenv ienv fenv map x p ; fst progn), snd progn)

  | Eprim x p vs e' =>
    match prims ! p with
    | Some {| Pipeline_utils.prim_alloc := false |} => (* compile without tinfo *)
      c <- mkPrimCall x p (length vs) fenv map vs ;;
      '(prog, slots) <- translate_body e' fenv cenv ienv map slots ;;
      ret (c; prog, slots)
    | Some {| Pipeline_utils.prim_alloc := true |} =>
      (* Compute the local variables that are live after the call  *)
        let fvs_post_call := PS.inter (exp_fv e') loc_vars in
        let fvs := PS.remove x fvs_post_call in
        let fvs_list := PS.elements fvs in
        (* Check if the new binding has to be pushed to the frame during the GC call *)
        let fv_gc := if PS.mem x fvs_post_call then cons x nil else nil in
        (* push live vars to the stack. We're pushing exactly the vars that are live beyond the current point. *)
        let '(make_stack, slots_call) :=
            let (push, slots) := push_live_vars fvs_list in
            (push ; update_stack slots; set_stack slots false, slots)
        in
        c <- mkPrimCallTinfo x p (length vs) fenv map vs ;;
        let alloc := max_allocs e' in
        (* Call GC after the call if needed *)
        let (gc_call, slots_gc) := make_GC_call alloc fv_gc slots_call in
        (* Pop live vars from the stack *)
        let discard_stack := pop_live_vars fvs_list; reset_stack slots_call false in
        '(prog, slots) <- translate_body e' fenv cenv ienv map (N.max slots slots_gc);;
        Ret ((Efield tinfd allocIdent valPtr :::= allocPtr ; Efield tinfd limitIdent valPtr  :::= limitPtr;
             make_stack;
             c;
             allocIdent ::= Efield tinfd allocIdent valPtr; limitIdent ::= Efield tinfd limitIdent valPtr;
             gc_call;
             discard_stack;
             prog),
             slots)
    | None => Err "translate_body: Unknown primitive identifier"
    end
  | Ehalt x =>
    ret (Efield tinfd allocIdent valPtr :::= allocPtr;
         Efield tinfd limitIdent valPtr :::= limitPtr;
         Sreturn (Some (makeVar x fenv map)),
         slots)
    end.

  End Body.

Definition mkFun
           (root_size : Z) (* size of roots array *)
           (vs : list positive) (* args *)
           (loc : list positive) (* local vars *)
           (body : statement) : function :=
  mkfunction val
             cc_default
             ((tinfIdent , threadInf) :: (map (fun x => (x , val)) (firstn nParam vs)))
             (stack_decl root_size)
             ((map (fun x => (x , val)) ((skipn nParam vs) ++ loc)) ++
                (allocIdent, valPtr) :: (limitIdent, valPtr) ::
                (argsIdent, valPtr) :: (caseIdent, boolTy) :: (resultIdent, val) :: nil)
             body.

Fixpoint translate_fundefs
         (fnd : fundefs)
         (fenv : fun_env)
         (cenv: ctor_env)
         (ienv : n_ind_env)
         (map : fun_info_env)
         (nenv : name_env) : error (list (positive * globdef Clight.fundef type)) :=
  match fnd with
  | Fnil => Ret nil
  | Fcons f t vs e fnd' =>
    rest <- translate_fundefs fnd' fenv cenv ienv map nenv ;;
    match M.get t fenv with
    | None => Err "translate_fundefs: Unknown function tag"
    | Some inf =>
      let '(l, locs) := inf in
      asgn <- asgnFunVars vs locs ;; (* project remaining params out of args array *)
      let num_allocs := max_allocs e in
      let loc_vars := get_locals e in
      let var_set := union_list PS.empty vs in
      let loc_ids := union_list var_set loc_vars  in
      let live_vars := PS.elements (PS.inter (exp_fv e) var_set) in
      let (gc, _) := make_GC_call num_allocs live_vars 0%N in
      '(body, stack_slots) <- translate_body vs loc_ids locs nenv e fenv cenv ienv map 0 ;;
      let stack_slots := N.max (N.of_nat (length live_vars)) stack_slots in
      Ret ((f , Gfun (Internal
                      (mkFun (Z.of_N stack_slots) vs loc_vars
                             ((allocIdent ::= Efield tinfd allocIdent valPtr ;
                               limitIdent ::= Efield tinfd limitIdent valPtr ;
                               argsIdent ::= Efield tinfd argsIdent (Tarray uval maxArgs noattr);
                               asgn ;
                               init_stack ;
                               gc;
                               body))))) :: rest)
    end
  end.

Definition make_extern_decl
           (nenv : name_env)
           (def : positive * globdef Clight.fundef type)
           (gv : bool) : option (positive * globdef Clight.fundef type) :=
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
    if gv then
      Some (vIdent, Gvar (mkglobvar v_info nil v_r v_v))
    else None
  | _ => None
  end.


Fixpoint make_extern_decls
         (nenv : name_env)
         (defs : list (positive * globdef Clight.fundef type))
         (gv : bool) : list (positive * globdef Clight.fundef type) :=
  match defs with
  | fdefs :: defs' =>
    let decls := make_extern_decls nenv defs' gv in
    match make_extern_decl nenv fdefs gv with
    | Some decl => decl :: decls
    | None => decls
    end
  | nil => nil
  end.

Definition body_external_decl : positive * globdef Clight.fundef type :=
  let params := type_of_params ((tinfIdent, threadInf) :: nil) in
  (bodyIdent, Gfun (External (EF_external (String.to_string bodyName)
                                (signature_of_type  params val cc_default))
                             params val cc_default)).

End Translation.

(* TODO move *)
Definition lift_error {A : Type} (o : option A) (s : string) : error A :=
  match o with
  | Some a => ret a
  | None => Err s
  end.

Definition translate_program
           (args_opt : bool)
           (e : exp)
           (fenv : fun_env)
           (cenv: ctor_env)
           (ienv : n_ind_env)
           (fmap : fun_info_env)
           (nenv : name_env) : error (list (positive * globdef Clight.fundef type)) :=
  match e with
  | Efun fnd e =>
    let localVars := get_locals e in
    funs <- translate_fundefs args_opt fnd fenv cenv ienv fmap nenv ;;
    let allocs := max_allocs e in
    let (gc_call, _) := make_GC_call allocs nil (* no live roots to push *) 0%N in
    '(body, slots) <- translate_body args_opt [] (union_list PS.empty localVars) [] nenv e fenv cenv ienv fmap 0 ;;
    let argsExpr := Efield tinfd argsIdent (Tarray uval maxArgs noattr) in
    ret ((bodyIdent,
          Gfun (Internal (mkfunction
                    val
                    cc_default
                    ((tinfIdent, threadInf) :: nil)
                    (stack_decl (Z.of_N slots))
                    (map (fun x => (x , val)) localVars ++
                    (allocIdent, valPtr) :: (limitIdent, valPtr) :: (argsIdent, valPtr) :: nil)
                    (allocIdent ::= Efield tinfd allocIdent valPtr ;
                    limitIdent ::= Efield tinfd limitIdent valPtr ;
                    argsIdent ::= Efield tinfd argsIdent (Tarray uval maxArgs noattr);
                    init_stack ;
                    gc_call;
                    body)))) :: funs)
  | _ => Err "translate_program: Missing toplevel function block"
  end.

Definition nState := @compM' positive.

Definition getName : nState positive :=
  '(cd, n) <- compM.get ;;
  compM.put (cd, n+1)%positive ;;
  ret n.

Fixpoint make_ind_array (l : list N) : list init_data :=
  match l with
  | nil => nil
  | n :: l' => (Init_int (Z.of_N n)) :: (make_ind_array l')
  end.

Import MetaRocq.Utils.bytestring.String (append).

Definition update_name_env_fun_info (f f_inf : positive) (nenv : name_env) : name_env :=
  match M.get f nenv with
  | None => M.set f_inf (nNamed (append (show_pos f) "_info")) nenv
  | Some n => match n with
              | nAnon => M.set f_inf (nNamed (append (append "x" (show_pos f)) "_info")) nenv
              | nNamed s => M.set f_inf (nNamed (append s "_info")) nenv
              end
  end.

(* see runtime for description and uses of fundef_info.
  In summary,
  fi[0] = number of words that can be allocated by function
  fi[1] = number of live roots at startof function
  rest = indices of live roots in args array
*)

Fixpoint make_fundef_info (fnd : fundefs) (fenv : fun_env) (nenv : name_env)
  : nState (list (positive * globdef Clight.fundef type) * fun_info_env * name_env) :=
  match fnd with
  | Fnil => ret (nil, M.empty (positive * fun_tag), nenv)
  | Fcons x t vs e fnd' =>
    match M.get t fenv with
    | None => failwith "make_fundef_info: Unknown tag"
    | Some inf =>
      let '(n, l) := inf in
      rest <- make_fundef_info fnd' fenv nenv ;;
      let '(defs, map, nenv') := rest in
      info_name <- getName ;;
      let len := Z.of_nat (length l) in
      (* it should be the case that n (computed arity from tag) = len (actual arity) *)
      let ind :=
          mkglobvar
            (Tarray uval
                    (len + 2%Z)
                    noattr)
            ((Init_int (Z.of_nat (max_allocs e))) :: (Init_int len) :: (make_ind_array l)) true false in
      ret ((info_name , Gvar ind) :: defs,
           M.set x (info_name , t) map,
           update_name_env_fun_info x info_name nenv')
    end
  end.



Definition add_bodyinfo (e : exp) (fenv : fun_env) (nenv : name_env) (map: fun_info_env) (defs:list (positive * globdef Clight.fundef type)) :=
  info_name <- getName ;;
  let ind :=
      mkglobvar
        (Tarray uval
                2%Z
                noattr)
        ((Init_int (Z.of_nat (max_allocs e))) :: (Init_int 0%Z) :: nil) true false in
  ret ((info_name , Gvar ind) :: defs,
       M.set mainIdent (info_name , 1%positive) map,
       M.set info_name (nNamed "body_info"%bs) nenv).


(* Make fundef_info for functions in fnd (if any), and for the body of the program *)
Definition make_funinfo (e : exp) (fenv : fun_env) (nenv : name_env)
  : nState (list (positive * globdef Clight.fundef type) * fun_info_env * name_env) :=
  match e with
  | Efun fnd e' =>
    p <- make_fundef_info fnd fenv nenv;;
    let '(defs, map, nenv') := p in
    add_bodyinfo e' fenv nenv' map defs
  | _ => failwith "make_funinfo: Function block expected"
  end.


Definition global_defs (e : exp) : list (positive * globdef Clight.fundef type) :=
  (* (gcIdent , Gfun (External (EF_external "garbage_collect"%string *)
  (*                                        (mksignature (val_typ :: nil) AST.Tvoid cc_default)) *)
  (*                           (Tcons threadInf Tnil) *)
  (*                           Tvoid *)
  (*                           cc_default )) :: *)
  (* (isptrIdent , Gfun (External (EF_external "is_ptr" *)
  (*                                           (mksignature (val_typ :: nil) AST.Tvoid cc_default)) *)
  (*                              (Tcons val Tnil) (Tint IBool Unsigned noattr) *)
  (*                              cc_default )) :: *)
  nil.

Definition make_defs (args_opt : bool) (e : exp) (fenv : fun_env) (cenv: ctor_env) (ienv : n_ind_env) (nenv : name_env) :
  nState (name_env * (list (positive * globdef Clight.fundef type))) :=
  fun_inf' <- make_funinfo e fenv nenv ;;
  let '(fun_inf, map, nenv') := fun_inf' in
  match translate_program args_opt e fenv cenv ienv map nenv with
  | Err s => failwith s
  | Ret fun_defs' =>
    let fun_defs := rev fun_defs' in
    ret (nenv', (global_defs e ++ fun_inf ++ fun_defs)%list)
  end.

Definition to_plain_members (l : list (ident * type)) : list member :=
  map (fun '(x, y) => Member_plain x y) l.

(* Types declared at the begining of the program *)
Definition composites : list composite_definition :=
  (* Composite stackframeTIdent Struct *)
  (*           (to_plain_members ((nextFld, valPtr) :: *)
  (*            (rootFld, valPtr) :: *)
  (*            (prevFld, (tptr stackframeT)) :: nil)) *)
  (*           noattr :: *)
  (* Composite threadInfIdent Struct *)
  (*           (to_plain_members ((allocIdent, valPtr) :: *)
  (*            (limitIdent, valPtr) :: *)
  (*            (heapInfIdent, (tptr (Tstruct heapInfIdent noattr))) :: *)
  (*            (argsIdent, (Tarray uval maxArgs noattr)) :: *)
  (*            (fpIdent, (tptr stackframeT)) :: *)
  (*            (nallocIdent, val) :: nil)) (1* Zoe : This is the number of allocations until the next GC call so that GC can perform a test. *)
  (*                                        * Note that it will be coerced to UL from ULL. That should be safe for the values we're using but *)
  (*                                        * consider changing it too. *1) *)
  (*           noattr :: *)
   nil.

Definition mk_prog_opt (defs: list (ident * globdef Clight.fundef type))
           (main : ident) (add_comp:bool): error Clight.program :=
  let composites := if add_comp then composites else nil in
  let res := Ctypes.make_program composites defs (bodyIdent :: nil) main in
  match res with
  | Error e => Err "mk_prog_opt"
  | OK p => ret p
  end.

(* Wrap program in empty Efun if e.g. fully inlined *)
Definition wrap_in_fun (e:exp) :=
  match e with
  | Efun fds e' =>
    e
  | _ => Efun Fnil e
  end.

Definition inf_vars :=
  (isptrIdent, (nNamed "is_ptr"%bs)) ::
  (argsIdent, (nNamed "args"%bs)) ::
  (allocIdent, (nNamed "alloc"%bs)) ::
  (nallocIdent, (nNamed "nalloc"%bs)) ::
  (limitIdent, (nNamed "limit"%bs)) ::
  (gcIdent, (nNamed "garbage_collect"%bs)) ::
  (mainIdent, (nNamed "main"%bs)) ::
  (bodyIdent, (nNamed bodyName)) ::
  (threadInfIdent, (nNamed "thread_info"%bs)) ::
  (tinfIdent, (nNamed "tinfo"%bs)) ::
  (heapInfIdent, (nNamed "heap"%bs)) ::
  (caseIdent, (nNamed "arg"%bs)) ::
  (numArgsIdent, (nNamed "num_args"%bs)) ::
  (stackframeTIdent, (nNamed "stack_frame"%bs)) ::
  (frameIdent, nNamed "frame"%bs) ::
  (rootIdent, nNamed "roots"%bs) ::
  (fpIdent, nNamed "fp"%bs) ::
  (nextFld, nNamed "next"%bs) ::
  (rootFld, nNamed "root"%bs) ::
  (prevFld, nNamed "prev"%bs) ::
  (resultIdent, nNamed "result"%bs) :: nil.


Definition add_inf_vars (nenv: name_env): name_env :=
  List.fold_left (fun nenv inf => M.set (fst inf) (snd inf) nenv) inf_vars nenv.

Definition ensure_unique : name_env -> name_env :=
  fun l => M.map (fun x n =>
                    match n with
                    | nAnon =>  nAnon
                    | nNamed s => nNamed (append s (append "_"%bs (show_pos x)))
                  end) l.

Fixpoint make_proj (recExpr:expr) (start:nat) (left:nat): list expr  :=
  match left with
  | 0 => nil
  | S n =>
    let s := make_proj recExpr (S start) n in
    (Field(recExpr, Z.of_nat start))::s
  end.

Fixpoint make_Asgn (les:list expr) (res:list expr) :=
  match les, res with
  | (hl::les), (hr:: res) =>
    Ssequence (Sassign hl hr) (make_Asgn les res)
  | _, _ => Sskip
  end.

Fixpoint make_constrAsgn' (argv:ident) (argList:list (ident * type)) (n:nat) :=
  match argList with
  | nil => Sskip
  | (id, ty)::argList' =>
    let s' := make_constrAsgn' argv argList' (S n) in
    (Sassign (Field(var argv, Z.of_nat n)) (Evar id ty) ; s')
  end.

Definition make_constrAsgn (argv:ident) (argList:list (ident * type)) :=
    make_constrAsgn' argv argList 1.

Section Check. (* Just for debugging purposes. TODO eventually delete*)

  Context (fenv : fun_env) (nenv : name_env).

  Fixpoint check_tags_fundefs' (B : fundefs) (log : list string) : list string :=
         match B with
         | Fcons f t xs e B' =>
           let s :=
               match M.get t fenv with
               | Some (n, l) =>
                 "Definition " ++ get_fname f nenv ++ " has tag " ++ (show_pos t) ++ Pipeline_utils.newline ++
                 "Def: Function " ++ get_fname f nenv ++ " has arity " ++ (show_binnat n) ++ " " ++
                 MRString.string_of_nat (length l)
               | None =>
                 "Def: Function " ++ get_fname f nenv ++ " was not found in fun_env"
               end
           in check_tags_fundefs' B' (s :: log)
         | Fnil => log
         end.

  Fixpoint check_tags' (e : exp) (log : list string) :=
    match e with
    | Econstr _ _ _ e | Eproj _ _ _ _ e | Eprim_val _ _ e | Eprim _ _ _ e => check_tags' e log

    | Ecase _ bs =>
      fold_left (fun a b => check_tags' (snd b) a) bs log

    | Eletapp x f t ys e =>
      let s :=
          match M.get t fenv with
          | Some (n, l) =>
            "LetApp: Function " ++ get_fname f nenv ++ " has arity " ++ (show_binnat n) ++ " " ++
            (MRString.string_of_nat (length l))
          | None =>
            "LetApp: Function " ++ get_fname f nenv ++ " was not found in fun_env"
          end
      in check_tags' e (s :: log)

    | Efun B e =>
      let s := check_tags_fundefs' B log in
      check_tags' e s

    | Eapp f t ys =>
      let s :=
          match M.get t fenv with
          | Some (n, l) =>
            "App: Function " ++ get_fname f nenv ++ " has arity " ++ (show_binnat n) ++ " " ++
            MRString.string_of_nat (length l)
          | None =>
            "App: Function " ++ get_fname f nenv ++ " was not found in fun_env"
          end
      in
      s :: log
    | Ehalt x => log
    end.


  Definition check_tags (e : exp) :=
    String.concat Pipeline_utils.newline (rev (check_tags' e [])).

End Check.

Definition make_tinfoIdent := 20%positive.

Definition make_tinfo_rec : positive * globdef Clight.fundef type :=
  (make_tinfoIdent,
   Gfun (External (EF_external "make_tinfo"
                               (mksignature (nil) (val_typ) cc_default))
                  Tnil
                  threadInf
                  cc_default)).

Definition compile (args_opt : bool) (e : exp) (cenv : ctor_env) (nenv0 : name_env) :
  error (name_env * Clight.program * Clight.program) * string :=
  let e := wrap_in_fun e in
  let fenv := compute_fun_env nenv0 e in
  let ienv := compute_ind_env cenv in
  (* debug *)
  (* let dbg := (cps_show.show_exp nenv0 cenv false e) ++ Pipeline_utils.newline ++ log ++ Pipeline_utils.newline ++ check_tags fenv nenv0 e in *)
  (* end debug *)
  let p'' := make_defs args_opt e fenv cenv ienv nenv0 in
  (* state *)
  let n := ((max_var e 100) + 1)%positive in
  let comp_d := pack_data 1%positive 1%positive  1%positive 1%positive cenv fenv nenv0 (M.empty nat) [] in (* XXX dummy *)
  (* run compM *)
  let err : error (name_env * Clight.program * Clight.program) :=
      let '(res, (p, m)) := run_compM p'' comp_d n in
      '(nenv1, defs) <- res ;;
       let nenv := (add_inf_vars (ensure_unique nenv1)) in
       let forward_defs := make_extern_decls nenv defs false in
       body <- mk_prog_opt [body_external_decl] mainIdent false;;
       head <- mk_prog_opt (make_tinfo_rec :: forward_defs ++ defs)%list mainIdent true ;;
       ret (M.set make_tinfoIdent (nNamed "make_tinfo"%bs) nenv, body, head)
  in
  (err, "").

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
