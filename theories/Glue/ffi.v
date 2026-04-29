(*
  The module that generates glue code
  for a vernacular command that takes an FFI type class:

  Class StringFFI : Type :=
    { print_string : string -> IO unit
    ; scan_string : IO string
    }.
  CertiRocq FFI StringFFI.
*)
Require Import Common.Pipeline_utils.

From Stdlib Require Import ZArith.ZArith
               Program.Basics
               Strings.String
               Lists.List.
Require Import List_util.

Require Import ExtLib.Structures.Monads
               ExtLib.Structures.Traversable
               ExtLib.Data.Monads.OptionMonad
               ExtLib.Data.String.

From MetaRocq.Utils Require Import bytestring.
From MetaRocq.Common Require Import BasicAst.
Require MetaRocq.Template.All.

Require Import compcert.common.AST
               compcert.common.Errors
               compcert.lib.Integers
               compcert.cfrontend.Cop
               compcert.cfrontend.Ctypes
               compcert.cfrontend.Clight
               compcert.common.Values
               compcert.export.Clightdefs.

Require Import LambdaANF.term
               LambdaANF.identifiers
               LambdaANF.cps_show
               LambdaANF_to_Clight
               compM
               glue_utils.

Import MonadNotation.
Open Scope monad_scope.

Notation Tcons := cons.
Notation Tnil := nil.
Notation typelist := (list type).

Section FState.

  Record fstate_data : Type :=
    Build_fstate_data
      { fstate_gensym : ident
      ; fstate_nenv   : name_env
      ; fstate_log    : list string
      }.

  Definition ffiM : Type -> Type := compM Options fstate_data.

  Definition gets {A : Type} (f : fstate_data -> A) : ffiM A :=
    s <- get ;; ret (f s).

  (* generate fresh [ident] and record it to the [name_env]
     with the given [string] *)
  Definition gensym (s : string) : ffiM ident :=
    '(Build_fstate_data n nenv log) <- get ;;
    let nenv := M.set n (nNamed s) nenv in
    put (Build_fstate_data ((n+1)%positive) nenv log) ;;
    ret n.

  (* logs are appended to the list and the list is reversed
     at the end to keep them in chronological order *)
  Definition log (s : string) : ffiM unit :=
    '(Build_fstate_data n nenv  log) <- get ;;
    put (Build_fstate_data n nenv (s :: log)).

End FState.

(* Takes a MetaRocq type for an FFI function,
   returns its arity and whether it's in IO. *)
(* TODO currently the IO name is hardcoded
   but we should change that at some point *)
Fixpoint type_to_args
         (e : Ast.term) : nat * bool :=
  match e with
  | Ast.tProd _ _ e' =>
      let (n, b) := type_to_args e' in (S n, b)
  | Ast.tApp (Ast.tConst ((_, "IO")%bs) _) _ => (0, true)
  | _ => (0, false)
  end.

(* Takes a MetaRocq constructor type (a pi type),
   skips the number of parameters in the type.
   Doesn't fail if there aren't enough pi types etc. *)
Fixpoint skip_params
         (params : nat)
         (e : Ast.term) : Ast.term :=
  match params, e with
  | S params', Ast.tProd _ _ e' => skip_params params' e'
  | _ , _ => e
  end.

(* Same function as [repeat] but for [typelist]s instead of [list]s. *)
Fixpoint repeat_typelist (t : type) (n : nat) : typelist :=
  match n with
  | 0 => Tnil
  | S n' => Tcons t (repeat_typelist t n')
  end.

Variant Backend := ANF | CPS.

(* A way to project arguments saved in a closure out of the env.
   e.g. if you want to get the last argument,
        you call [env_proj 0] with some env [expr]
        and get "*((value * ) env)".
        But [env_proj 1] gives you
        "*((value * ) *((value * ) env + 1LLU))"
*)
Fixpoint env_proj
         (i : nat) (* index from the end w.r.t. argument order *)
         (env : expr)
         : expr :=
  match i with
  | 0 => *([tptr val] env)
  | S i' => env_proj i' (Field(env, 1))
  end.

Local Open Scope bs_scope.

Definition make_curried_fn
         (* The sanitized unqual. name of the FFI function we're dealing with *)
           (kn : sanitized_name)
         (* initially the arity but it gets smaller with every call *)
           (num : nat)
         (* constant argument, always the arity *)
           (arity : nat)
         (* whether the function is in the IO monad or not *)
           (is_io : bool)
         (* the next function to put in the closure or in the 0 arity case, to call *)
           (_next_fn : ident)
           : ffiM def :=
  opts <- ask ;;
  let c_args : nat := c_args opts in
  let backend := if direct opts then ANF else CPS in
  _curried <- gensym (match num with
                      | S _ => kn ++ "_" ++ show_nat num
                      | _ => kn ++ "_world"
                      end) ;;

  (* FIXME some of these names should be kept in a toolbox,
     just like we do in the glue.v file, instead of being [gensym]ed every time.
     This works for C generation sorta by accident, but if we wanted to
     prove anything about the Clight code we generate, this wouldn't work. *)
  _thread_info <- gensym "thread_info" ;;
  _alloc <- gensym "alloc" ;;
  _args <- gensym "args" ;;
  _tinfo <- gensym "tinfo" ;;
  _env <- gensym "env" ;;
  _k <- gensym "k" ;;
  _arg <- gensym "arg" ;;
  _call <- gensym "call" ;;

  (* Adjusting the parameters and the local variables of the function
     with respect to the options, namely CPS/ANF and the args number *)
  let all_anf := ((_env, val) :: (_arg, val) :: nil) in
  let all_cps := ((_env, val) :: (_k, val) :: (_arg, val) :: nil) in
  let all := match backend with ANF => all_anf | CPS => all_cps end in
  let params := firstn c_args all in
  let vars := skipn c_args all in

  (* Extracting the inputs from tinfo->args if the args setting is too low *)
  let args_expr := Efield (tinfd _thread_info _tinfo) _args valPtr in
  let handle_input : statement :=
      multiple (skipn c_args
                (* if c_args is 0 don't skip any, if it's 1 skip the first one and so on *)
                 match backend with
                 | ANF =>
                    (Sassign (Etempvar _env val) (Field(args_expr, Z.of_nat 0)) ::
                     Sassign (Etempvar _arg val) (Field(args_expr, Z.of_nat 1)) :: nil)
                 | CPS =>
                    (Sassign (Etempvar _env val) (Field(args_expr, Z.of_nat 0)) ::
                     Sassign (Evar _k val)       (Field(args_expr, Z.of_nat 1)) ::
                     Sassign (Etempvar _arg val) (Field(args_expr, Z.of_nat 2)) :: nil)
                 end) in



  (* tinfo->alloc *)
  let alloc_expr :=
      (Efield (Ederef (Evar _tinfo (threadInf _thread_info))
                      (threadStructInf _thread_info))
              _alloc (tptr val)) in
  (* e += n; *)
  let self_incr (e : expr) (n : Z) :=
      Sassign e (add e (c_int n val)) in
  let ptr_self_incr (e : expr) (n : Z) :=
      Sassign e (add ([tptr val] e) (c_int n val)) in
  (* tinfo->alloc += n; *)
  let alloc_incr (n : Z) :=
      self_incr alloc_expr n in
  (* Now, there are two different kinds of functions we can generate here.
     One for currying (if arity > 0) and
     one for calling linked C function from the extern. (if arity = 0) *)
  '(_ret, vars' , rest) <-
      match num , is_io with
      | 0 , _ (* world function for IO *)
      | 1 , false (* pure FFI function *)=>
           (* We should project the content of the env
              and call the extern function here *)
        let args_to_extract : nat :=
            if is_io then arity else pred arity in
        let l := RandyPrelude.list_to_zero args_to_extract in

        let make_arg (n : nat) : ffiM ((ident * type) * statement) :=
            _n <- gensym ("arg" ++ show_nat n) ;;
            let s := Sassign (Etempvar _n val) (env_proj n (Evar _env val)) in
            ret ((_n, val), s) in

        res <- mapM make_arg l ;;
        let '(args, ss) := List.split res in
        let all_args := if is_io then args
                        else (args ++ ((_arg, val) :: nil))%list in
        _res <- gensym "result" ;;
        let call := Scall (Some _res)
                          (Evar _next_fn
                                (Tfunction (Tcons (threadInf _thread_info)
                                                  (repeat_typelist val arity))
                                           val cc_default))
                          (Evar _tinfo (threadInf _thread_info) ::
                           map (fun '(_n, t) => Etempvar _n t) all_args) in
        if is_io
          then (* Put the result in a pair of [A * World]
                  because that's how [IO] is defined *)
            _pair <- gensym "pair" ;;
            let s :=
                Sassign (Etempvar _pair val) ([val] alloc_expr) ;;;
                Sassign (Field(var _pair, 0%Z)) (c_int 2048 val) ;;;
                Sassign (Field(var _pair, 1%Z)) (Evar _res val) ;;;
                Sassign (Field(var _pair, 2%Z)) (Evar _arg val) ;;;
                alloc_incr 3%Z ;;;
                ptr_self_incr (Etempvar _pair val) 1%Z in
            ret (_pair,
                (_res, val) :: (_pair, val) :: args,
                multiple ss ;;; call ;;; s)
          else (* Just return the result *)
            ret (_res,
                (_res, val) :: args,
                multiple ss ;;; call)
      | S _ , _ => (* We should create an env and a closure *)
        _new_env <- gensym "new_env" ;;
        _new_clo <- gensym "new_clo" ;;
        let create_env :=
            Sassign (Etempvar _new_env val) ([val] alloc_expr) ;;;
            Sassign (Field(var _new_env, 0%Z)) (c_int 2048 val) ;;;
            Sassign (Field(var _new_env, 1%Z)) (Evar _arg val) ;;;
            Sassign (Field(var _new_env, 2%Z)) (Evar _env val) ;;;
            alloc_incr 3%Z ;;;
            ptr_self_incr (Etempvar _new_env val) 1%Z in
        let create_clo :=
            Sassign (Etempvar _new_clo val) ([val] alloc_expr) ;;;
            Sassign (Field(var _new_clo, 0%Z)) (c_int 2048 val) ;;;
            Sassign (Field(var _new_clo, 1%Z)) (Evar _next_fn val) ;;;
            Sassign (Field(var _new_clo, 2%Z)) (Evar _new_env val) ;;;
            alloc_incr 3%Z ;;;
            ptr_self_incr (Etempvar _new_clo val) 1%Z in
        ret (_new_clo,
             (_new_env, val) :: (_new_clo, val) :: nil,
             create_env ;;; create_clo)
      end ;;
  (* Return whatever temp variable is supposed to be returned,
     either the closure in the numbered functions,
     or the final result in the world function *)
  let final _ret :=
      match backend with
      | ANF =>
          (* Returning a value in ANF is as easy
            as putting it in tinfo->args[1] *)
          Sassign (Field(args_expr, Z.of_nat 1)) (Etempvar _ret val)
      | CPS =>
        (* Returning a value in CPS means calling the continuation,
            but we have the args setting that changes a lot *)
        let fargs := tinf _thread_info _tinfo ::
                      Etempvar _env val ::
                      Etempvar _arg val :: nil in
        let forcelist :=
            nth c_args ((* if c_args = 0 *) Tnil ::
                        (* if c_args = 1 *) Tcons val Tnil :: nil)
                (* else *) (Tcons val (Tcons val Tnil)) in
        let ret_ty := Tpointer (Tfunction (Tcons (threadInf _thread_info) forcelist)
                                          Tvoid cc_default) noattr in
        multiple (skipn c_args
          (Sassign (Field(args_expr, Z.of_nat 0)) (Field(var _k, 1%Z)) ::
           Sassign (Field(args_expr, Z.of_nat 1)) (Evar _ret val) :: nil)) ;;;
        Scall None ([ret_ty] (Field(var _k, 0%Z)))
              ((Evar _tinfo (threadInf _thread_info)) ::
                firstn c_args ((Field(var _k, 1%Z)) :: (Evar _ret val) :: nil))
      end ;;; Sreturn None in
  ret (_curried,
       Gfun (Internal
               {| fn_return := Tvoid
                ; fn_callconv := cc_default
                ; fn_params := (_tinfo, (threadInf _thread_info)) ::
                               params
                ; fn_vars := vars ++ vars'
                ; fn_temps := nil
                ; fn_body := handle_input ;;; rest ;;; final _ret
                |})).

Fixpoint make_curried_fns
         (* The sanitized unqual. name of the FFI function we're dealing with *)
           (kn : sanitized_name)
         (* initially the arity but it gets smaller with every call *)
           (num : nat)
         (* constant argument, always the arity *)
           (arity : nat)
         (* whether the function is in the IO monad or not *)
           (is_io : bool)
         (* the extern function to call in the 0 arity case *)
           (_final_fn : ident)
         : ffiM defs :=
  match num , is_io with
  | 0 , _ (* world function for IO *)
  | 1 , false (* pure FFI function *) =>
      (* generate a function that takes in the world *)
      x <- make_curried_fn kn num arity is_io _final_fn ;;
      ret (x :: nil)
  | S num' , _ =>
      rest <- make_curried_fns kn num' arity is_io _final_fn ;;
      match rest with
      | nil =>
          (* There will always be a world function for 0 arity *)
          failwith "Impossible: no world function"
      | (_prev_fn, _) :: _ =>
          d <- make_curried_fn kn num arity is_io _prev_fn ;;
          ret (d :: rest)
      end
  end.

(* Take a field name as a [kername],
   which is supposed to be an FFI function name,
   and its Coq type as a MetaRocq type.
   Generate the necessary Clight functions and closures from that. *)
Definition make_one_field
           (field : sanitized_name * Ast.term)
           : ffiM defs :=
  let (kn, t) := field in
  let (arity, is_io) := type_to_args t in
  _extern_fn <- gensym kn ;;
  _thread_info <- gensym "thread_info" ;;
  let extern_def :=
    (_extern_fn,
     Gfun (External (EF_external (String.to_string kn)
                 (mksignature (val_typ :: nil) Xvoid cc_default))
               (Tcons (threadInf _thread_info) (repeat_typelist val arity))
               val cc_default)) in
  rest <- make_curried_fns kn arity arity is_io _extern_fn ;;
  match rest with
  | nil => failwith "No curried functions!"
  | (_entry, _) :: _ =>
    _clo <- gensym (kn ++ "_clo") ;;
    let clo_ty := tarray val 2 in
    let clo_data := Init_addrof _entry Ptrofs.zero :: Init_int8 (Int.repr 1) :: nil in
    let clo_def := (_clo, Gvar (mkglobvar clo_ty clo_data true false)) in
    (* We have to put [clo_def] at the end so that it's a declared identifier *)
    ret (extern_def :: rev rest ++ (clo_def :: nil))
  end.

Fixpoint make_all_fields
         (fields : list (sanitized_name * Ast.term))
         : ffiM defs :=
  match fields with
  | nil => ret nil
  | f :: fs =>
      f' <- make_one_field f ;;
      fs' <- make_all_fields fs ;;
      ret (f' ++ fs')%list
  end.

Definition make_toolbox : ffiM composite_definitions :=
  _thread_info <- gensym "thread_info" ;;
  _alloc <- gensym "alloc" ;;
  _limit <- gensym "limit" ;;
  _heap <- gensym "heap" ;;
  _args <- gensym "args" ;;
  let comp :=
    Composite _thread_info Struct
      (Member_plain _alloc valPtr ::
       Member_plain _limit valPtr ::
       Member_plain _heap (tptr (Tstruct _heap noattr)) ::
       Member_plain _args (Tarray uval max_args noattr) :: nil) noattr :: nil in
  ret comp.

Definition make_ffi_program
           (fields : list (sanitized_name * Ast.term))
           : ffiM (option Clight.program * option Clight.program) :=
  composites <- make_toolbox ;;
  field_defs <- make_all_fields fields ;;
  let glob_defs := field_defs in
  nenv <- gets fstate_nenv ;;
  ret (mk_prog_opt composites (make_extern_decls nenv glob_defs true)
                   main_ident true,
       mk_prog_opt composites glob_defs
                   main_ident true).

(* Takes the full MetaRocq program representing a type,
   like an [FFI] type class.
   Returns the fields in that type class. *)
Definition get_constructors
           (p : Ast.Env.program)
           : ffiM (list (sanitized_name * Ast.term)) :=
  opts <- ask ;;
  let prefix : string := Pipeline_utils.prefix opts in
  log ("Using the prefix '" ++ prefix ++ "' for the generated FFI functions") ;;
  let '(globs, _) := p in

  let fix pi_types_to_class_fields
          (e : Ast.term) : ffiM (list (sanitized_name * Ast.term)) :=
    match e with
    | Ast.tProd (mkBindAnn (nNamed field_name) _) t e' =>
        log ("Handing the field " ++ field_name) ;;
        (* TODO MAYBE convert field_name to kername by qualifying it *)
        (* right now we qualify the names with the option the user provides *)
        rest <- pi_types_to_class_fields e' ;;
        ret ((sanitize_string (String.append prefix field_name), t) :: rest)
    | Ast.tRel _ => ret nil
    | Ast.tApp _ _ => ret nil
    | _ =>
      failwith "Unrecognized pattern in converting pi types to class fields."
    end in

  match last_error (rev globs.(Ast.Env.declarations)) with
  | Some (ind_name, Ast.Env.InductiveDecl mut) =>
      (* Assuming we don't have mutually recursive type classes *)
      match Ast.Env.ind_bodies mut with
      | one :: nil =>
          match Ast.Env.ind_ctors one with
          | ctor :: nil =>
            let pi_types := ctor.(Ast.Env.cstr_type) in
              let pi_types' := skip_params (Ast.Env.ind_npars mut) pi_types in
              pi_types_to_class_fields pi_types'
          | _ => failwith "Not a single constructor in the type."
          end
      | _ => failwith "Not a single type in the mutually inductive block."
      end
  | Some _ => failwith "The last declaration is not an inductive declaration."
  | None => failwith "The quoted term didn't contain any inductive types."
  end.

Definition generate_ffi
           (opts : Options)
           (p : Ast.Env.program)
           : error (name_env * Clight.program * Clight.program * list string) :=
  let init : fstate_data :=
      {| fstate_gensym := 2%positive
       ; fstate_nenv   := M.empty _
       ; fstate_log    := nil
       |} in
  let '(err, st) :=
      runState ((get_constructors >=> make_ffi_program) p) opts init in
  let nenv := fstate_nenv st in
  match err with
  | Err s => Err s
  | Ret (Some header, Some source) =>
    Ret (nenv (* the name environment to be passed to C generation *) ,
         header (* the header content *),
         source (* the source content *),
         rev (fstate_log st) (* logged messages *))
  | Ret _ => Err "No Clight program generated"
  end.
