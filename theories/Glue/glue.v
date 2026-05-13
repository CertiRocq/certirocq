Require Import Common.Pipeline_utils.

From Stdlib Require Import ZArith.ZArith
               Program.Basics
               Strings.String
               Lists.List.
Require Import List_util.

Require Import ExtLib.Structures.Monads
               ExtLib.Data.Monads.OptionMonad.

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
               LambdaANF_to_Clight_stack
               compM
               glue_utils.

From MetaRocq.Utils Require Import bytestring MRString.

Notation Tcons := cons.
Notation Tnil := nil.
Notation typelist := (list type).

Import MonadNotation ListNotations.
Open Scope monad_scope.
Local Open Scope bs_scope.

Definition val : type := talignas (if Archi.ptr64 then 3%N else 2%N) (tptr tvoid).
Definition uval := if Archi.ptr64 then ulongTy else uintTy.
Definition argvTy : type := tptr val.

Notation "'Field(' t ',' n ')'" :=
  ( *(add t (c_int n%Z val))) (at level 36). (* what is the type of int being added? *)

(* Shared constructor assignment helper. *)
Fixpoint make_constrAsgn' (argv:ident) (argList:list (ident * type)) (n:nat) :=
  match argList with
  | nil => Sskip
  | (id, ty)::argList' =>
    let s' := make_constrAsgn' argv argList' (S n) in
    (Sassign (Field(var argv, Z.of_nat n)) (Etempvar id ty) ;;; s')
  end.

Definition make_constrAsgn (argv:ident) (argList:list (ident * type)) :=
    make_constrAsgn' argv argList 1.

(* An enumeration of L1 types.
   This is separate from the [ind_tag] values generated in LambdaANF.
   These are generated only for gluing purposes.
   There is no good reason for this, except for easier plumbing. *)
Definition ind_L1_tag : Type := positive.
Definition ind_L1_env : Type := M.t ty_info.

(* Matches [ind_L1_tag]s to a [ident] (i.e. [positive]) that holds
   the name of the get_tag_... function in C. *)
Definition get_tag_env : Type := M.t ident.

(* Matches [ind_L1_tag]s to a [ident] (i.e. [positive]) that holds
   the name and type of the names array in C. *)
Definition ctor_names_env : Type := M.t (ident * type).

(* An enumeration of constructors in a type starting from 1.
   Should preserve the ordering of the ctors in the original Coq definition.
   Should coincide with the index the glue functions return.
   But that index should start from 0, while this one starts from 1. *)
Definition ctor_L1_index : Type := positive.

(* Matches [ind_L1_tag]s to a [ident] (i.e. [positive]) that holds
   the name of the print function in C. *)
Definition print_env : Type := M.t ident.

(* A Clight ident and a Clight type packed together *)
Definition def_info : Type := positive * type.

Section Helpers.
  Record closure_bundle (A : Type) : Type :=
    Build_closure_bundle
      { closure_type : A
      ; func_info : A
      ; env_info : A
      }.

  Record stack_frame_bundle (A : Type) : Type :=
    Build_stack_frame_bundle
      { stack_frame_type : A
      ; next_info : A
      ; root_info : A
      ; prev_info : A
      }.

  Record thread_info_bundle (A : Type) : Type :=
    Build_thread_info_bundle
      { thread_info_type : A
      ; alloc_info : A
      ; limit_info : A
      ; heap_info : A
      ; args_info : A
      ; fp_info : A
      ; nalloc_info : A
      }.

  Record literals_bundle (A : Type) : Type :=
    Build_literals_bundle
      { lparen_info : A
      ; rparen_info : A
      ; space_info  : A
      ; fun'_info   : A
      ; type'_info  : A
      ; unk_info    : A
      ; prop_info   : A
      }.

  (* printf, is_ptr and these literals will be used by multiple functions
     so we want to reuse them, not redefine every time.
     Hence we keep references to them in this "toolbox".
   *)

  Record toolbox_info : Type :=
    Build_toolbox_info
      { printf_info : def_info
      ; is_ptr_info : def_info
      ; literals_info : literals_bundle def_info
      ; get_unboxed_ordinal_info : def_info
      ; get_boxed_ordinal_info : def_info
      ; get_args_info : def_info
      ; thread_info_info : thread_info_bundle ident
      ; closure_info : closure_bundle ident
      ; stack_frame_info : stack_frame_bundle ident
      ; halt_clo_info : def_info
      }.

End Helpers.

(* A state monad for the glue code generation *)
Section GState.

  Record gstate_data : Type :=
    Build_gstate_data
      { gstate_gensym : ident
      ; gstate_ienv   : ind_L1_env
      ; gstate_nenv   : name_env
      ; gstate_gtenv  : get_tag_env
      ; gstate_cnenv  : ctor_names_env
      ; gstate_penv   : print_env
      ; gstate_log    : list string
      }.

  Definition glueM : Type -> Type := compM Options gstate_data.

  Definition gets {A : Type} (f : gstate_data -> A) : glueM A :=
    s <- get ;; ret (f s).

  Variant backend := ANF | CPS.
  Definition get_backend : glueM backend :=
    opts <- ask ;;
    ret (if direct opts then ANF else CPS).

  (* generate fresh [ident] and record it to the [name_env]
     with the given [string] *)
  Definition gensym (s : string) : glueM ident :=
    '(Build_gstate_data n ienv nenv gtenv cnenv penv log) <- get ;;
    let nenv := M.set n (nNamed s) nenv in
    put (Build_gstate_data ((n+1)%positive) ienv nenv gtenv cnenv penv log) ;;
    ret n.

  Definition set_print_env (k : ind_L1_tag) (v : ident) : glueM unit :=
    '(Build_gstate_data n ienv nenv gtenv cnenv penv log) <- get ;;
    let penv := M.set k v penv in
    put (Build_gstate_data n ienv nenv gtenv cnenv penv log).

  Definition get_print_env (k : ind_L1_tag) : glueM (option ident) :=
    penv <- gets gstate_penv ;;
    ret (M.get k penv).

  Definition set_get_tag_env (k : ind_L1_tag) (v : ident) : glueM unit :=
    '(Build_gstate_data n ienv nenv gtenv cnenv penv log) <- get ;;
    let gtenv := M.set k v gtenv in
    put (Build_gstate_data n ienv nenv gtenv cnenv penv log).

  Definition get_get_tag_env (k : ind_L1_tag) : glueM (option ident) :=
    gtenv <- gets gstate_gtenv ;;
    ret (M.get k gtenv).

  Definition get_ctor_names_env (k : ind_L1_tag) : glueM (option (ident * type)) :=
    cnenv <- gets gstate_cnenv ;;
    ret (M.get k cnenv).

  Definition set_ctor_names_env (k : ind_L1_tag) (v : ident * type) : glueM unit :=
    '(Build_gstate_data n ienv nenv gtenv cnenv penv log) <- get ;;
    let cnenv := M.set k v cnenv in
    put (Build_gstate_data n ienv nenv gtenv cnenv penv log).

  Definition get_ind_L1_env (k : ind_L1_tag) : glueM (option ty_info) :=
    ienv <- gets gstate_ienv ;;
    ret (M.get k ienv).

  (* A hacky way to get the [ind_L1_tag] of a type from its name.
     This is necessary because of a shortcoming of Template Stdlib.
     (mutually recursive type names aren't fully qualified) *)
  Definition get_tag_from_type_name (s : kername) : glueM (option ind_L1_tag) :=
    let find (prev : option ind_L1_tag)
             (tag : ind_L1_tag)
             (info : ty_info) : option ind_L1_tag :=
      match prev with
      | None => if Kername.eqb s (ty_name info) then Some tag else None
      | _ => prev
      end in
    ienv <- gets gstate_ienv ;;
    ret (M.fold find ienv None).

  (* A hacky way to get the [ind_L1_tag] of a type from its [inductive] value.
     This is necessary because of a shortcoming of Template Stdlib. *)
  Definition get_tag_from_inductive (i : inductive) : glueM (option ind_L1_tag) :=
    let find (prev : option ind_L1_tag)
             (tag : ind_L1_tag)
             (info : ty_info) : option ind_L1_tag :=
      match prev with
      | None => if eq_inductive i (ty_inductive info) then Some tag else None
      | _ => prev
      end in
    ienv <- gets gstate_ienv ;;
    ret (M.fold find ienv None).

  Definition put_ind_L1_env (ienv : ind_L1_env) : glueM unit :=
    '(Build_gstate_data n _ nenv gtenv cnenv penv log) <- get ;;
    put (Build_gstate_data n ienv nenv gtenv cnenv penv log).

  (* logs are appended to the list and the list is reversed
     at the end to keep them in chronological order *)
  Definition log (s : string) : glueM unit :=
    '(Build_gstate_data n ienv nenv gtenv cnenv penv log) <- get ;;
    put (Build_gstate_data n ienv nenv gtenv cnenv penv (s :: log)).

End GState.

Section Externs.

  (* Converts Coq string to Clight array *)
  Fixpoint string_as_array (s : string) : list init_data :=
    match s with
    | String.EmptyString => Init_int8 Int.zero :: nil
    | String.String c s' =>
        Init_int8 (Int.repr (Z.of_N (Byte.to_N c))) :: string_as_array s'
    end.

  (* Creates a global variable with a string literal constant *)
  Definition string_literal (name : string) (literal : string)
            : glueM (ident * type * globdef fundef type) :=
    ident <- gensym name ;;
    let len := String.length literal in
    let init := string_as_array literal in
    let ty := tarray tschar (Z.of_nat (S len)) in
    let gv := Gvar (mkglobvar ty init true false) in
    ret (ident, ty, gv).

  Definition ty_printf : type :=
    Tfunction (Tcons (tptr tschar) Tnil) tint cc_default.

  Definition get_unboxed_ordinal : glueM def :=
    gname <- gensym "get_unboxed_ordinal" ;;
    _v <- gensym "v" ;;
    ret (gname,
         Gfun (Internal
                 {| fn_return := uval
                  ; fn_callconv := cc_default
                  ; fn_params := (_v, val) :: nil
                  ; fn_vars := nil
                  ; fn_temps := nil
                  ; fn_body := (Sreturn (Some
                                 (Ebinop Oshr (Ecast (var _v) uval)
                                              (make_cint 1 val) val)))
                  |})).

  Definition get_boxed_ordinal : glueM def :=
    gname <- gensym "get_boxed_ordinal" ;;
    _v <- gensym "v" ;;
    ret (gname,
         Gfun (Internal
                 {| fn_return := uval
                  ; fn_callconv := cc_default
                  ; fn_params := (_v, val) :: nil
                  ; fn_vars := nil
                  ; fn_temps := nil
                  ; fn_body :=
                      (Sreturn (Some
                        (Ebinop Oand
                          (Ecast (Field(Ecast (var _v) (tptr uval), -1)) uval)
                          (make_cint 255 val) val)))
                  |})).

  Definition get_args : glueM def :=
    gname <- gensym "get_args" ;;
    _v <- gensym "v" ;;
    ret (gname,
         Gfun (Internal
                 {| fn_return := tptr val
                  ; fn_callconv := cc_default
                  ; fn_params := (_v, val) :: nil
                  ; fn_vars := nil
                  ; fn_temps := nil
                  ; fn_body :=
                      (Sreturn (Some (Ecast (var _v) (tptr val))))
                  |})).

  Definition make_literals_bundle : glueM (literals_bundle def_info * defs) :=
    '(_lparen, ty_lparen, def_lparen) <- string_literal "lparen_lit" "(" ;;
    '(_rparen, ty_rparen, def_rparen) <- string_literal "rparen_lit" ")" ;;
    '(_space,  ty_space,  def_space)  <- string_literal "space_lit"  " " ;;
    '(_fun',   ty_fun',   def_fun')   <- string_literal "fun_lit"    "<fun>" ;;
    '(_type',  ty_type',  def_type')  <- string_literal "type_lit"   "<type>" ;;
    '(_unk,    ty_unk,    def_unk)    <- string_literal "unk_lit"    "<unk>" ;;
    '(_prop,   ty_prop,   def_prop)   <- string_literal "prop_lit"   "<prop>" ;;
    let literals :=
      {| lparen_info := (_lparen, ty_lparen)
       ; rparen_info := (_rparen, ty_rparen)
       ; space_info  := (_space,  ty_space)
       ; fun'_info   := (_fun',   ty_fun')
       ; type'_info  := (_type',  ty_type')
       ; unk_info    := (_unk,    ty_unk)
       ; prop_info   := (_prop,   ty_prop)
       |} in
  let defs := (_lparen, def_lparen) ::
              (_rparen, def_rparen) ::
              (_space, def_space) ::
              (_fun', def_fun') ::
              (_type', def_type') ::
              (_unk, def_unk) ::
              (_prop, def_prop) :: nil in
  ret (literals, defs).

  Definition make_externs : glueM (composite_definitions * defs * toolbox_info) :=
    '(literals, literal_defs) <- make_literals_bundle ;;
    _printf <- gensym "printf" ;;
    _is_ptr <- gensym "is_ptr" ;;
    '(_guo, def_guo) <- get_unboxed_ordinal ;;
    '(_gbo, def_gbo) <- get_boxed_ordinal ;;
    '(_get_args, def_get_args) <- get_args ;;

    _thread_info <- gensym "thread_info" ;;
    _alloc <- gensym "alloc";;
    _limit <- gensym "limit";;
    _heap <- gensym "heap";;
    _args <- gensym "args";;
    _fp <- gensym "fp";;
    _nalloc <- gensym "nalloc";;

    _closure <- gensym "closure" ;;
    _func <- gensym "func" ;;
    _env <- gensym "env" ;;

    _stack_frame <- gensym "stack_frame" ;;
    _next <- gensym "next" ;;
    _root <- gensym "root" ;;
    _prev <- gensym "prev" ;;

    _halt_clo <- gensym "halt_clo" ;;
    let ty_halt_clo := Tarray val 2 noattr in

    let tinfo : thread_info_bundle ident :=
        {| thread_info_type := _thread_info
         ; alloc_info := _alloc
         ; limit_info := _limit
         ; heap_info := _heap
         ; args_info := _args
         ; fp_info := _fp
         ; nalloc_info := _nalloc
         |} in
    let closure : closure_bundle ident :=
        {| closure_type := _closure
         ; func_info := _func
         ; env_info := _env
         |} in
    let stack_frame : stack_frame_bundle ident :=
      {| stack_frame_type := _stack_frame
       ; next_info := _next
       ; root_info := _root
       ; prev_info := _prev
       |} in
    backend <- get_backend ;;
    let comp :=
      match backend with
      | ANF =>
        Composite _closure Struct
         (Member_plain _func
                      (tptr (Tfunction (Tcons (tptr (Tstruct _thread_info noattr))
                                       (Tcons val (Tcons val Tnil))) val cc_default)) ::
          Member_plain _env val :: nil) noattr ::
        (* Composite _stack_frame Struct *)
        (*  (Member_plain _next (tptr val) :: *)
        (*   Member_plain _root (tptr val) :: *)
        (*   Member_plain _prev (tptr (Tstruct _stack_frame noattr)) :: nil) noattr :: *)
        (* Composite _thread_info Struct *)
        (*  (Member_plain _alloc (tptr val) :: *)
        (*   Member_plain _limit (tptr val) :: *)
        (*   Member_plain _heap (tptr (Tstruct _heap noattr)) :: *)
        (*   Member_plain _args (Tarray val max_args noattr) :: *)
        (*   Member_plain _fp (tptr (Tstruct _stack_frame noattr)) :: *)
        (*   Member_plain _nalloc tulong :: nil) noattr :: *)
          nil
      | CPS =>
        Composite _closure Struct
         (Member_plain _func
                      (tptr (Tfunction (Tcons (tptr (Tstruct _thread_info noattr))
                                       (Tcons val (Tcons val Tnil))) Tvoid cc_default)) ::
          Member_plain _env val :: nil) noattr ::
        (* Composite _thread_info Struct *)
        (*  (Member_plain _alloc (tptr val) :: *)
        (*   Member_plain _limit (tptr val) :: *)
        (*   Member_plain _heap (tptr (Tstruct _heap noattr)) :: *)
        (*   Member_plain _args (Tarray val max_args noattr) :: nil) noattr :: *)
          nil
      end in
    let toolbox :=
        {| printf_info :=
              (_printf, Tfunction (Tcons (tptr tschar) Tnil) tint cc_default)
         ; is_ptr_info :=
              (_is_ptr, Tfunction (Tcons val Tnil) tint cc_default)
         ; literals_info := literals
         ; get_unboxed_ordinal_info :=
              (_guo, Tfunction (Tcons val Tnil) tuint cc_default)
         ; get_boxed_ordinal_info :=
              (_gbo, Tfunction (Tcons val Tnil) tuint cc_default)
         ; get_args_info :=
              (_get_args, Tfunction (Tcons val Tnil) (tptr val) cc_default)
         ; thread_info_info := tinfo
         ; stack_frame_info := stack_frame
         ; closure_info := closure
         ; halt_clo_info := (_halt_clo, ty_halt_clo)
         |} in
    let dfs :=
      (literal_defs ++
       (*
       (_printf,
        Gfun (External (EF_external "printf"
                          (mksignature (AST.Tint :: nil)
                                       (Tret AST.Tint)
                                       cc_default))
                        (Tcons (tptr tschar) Tnil) tint cc_default)) ::
       *)
       (_is_ptr,
         Gfun (External (EF_external "is_ptr"
                          (mksignature (val_typ :: nil) Xvoid cc_default))
                        (Tcons val Tnil)
                        tint cc_default)) ::
       (_guo, def_guo) ::
       (_gbo, def_gbo) ::
       (_get_args, def_get_args) ::
       nil)%list in
    ret (comp, dfs, toolbox).

End Externs.

Section L1Types.

  Fixpoint get_max_ctor_arity
          (ctors : list (Ast.Env.constructor_body)) : nat :=
    match ctors with
    | nil => 0
    | ctor :: ctors' =>
        max ctor.(Ast.Env.cstr_arity) (get_max_ctor_arity ctors')
    end.

  (* takes an inductive type declaration and returns
     the qualifying prefix for the name and the type definition *)
  Definition extract_mut_ind
            (name : kername)
            (g : Ast.Env.global_decl)
            : option (modpath * Ast.Env.mutual_inductive_body) :=
    match g with
    | Ast.Env.InductiveDecl body => Some (fst name, body)
    | _ => None
    end.

  Definition context_names (ctx : Ast.Env.context) : list string :=
    map (fun d => match binder_name (decl_name d) with
                  | nNamed x => x
                  | _ => "" (* TODO error handling *)
                  end) ctx.

  Fixpoint get_single_types
           (gs : Ast.Env.global_declarations)
           : list ty_info :=
    match gs with
    | nil => nil
    | (name, g) :: gs' =>
      match extract_mut_ind name g with
      | Some (qual_pre, b) =>
          (* This relies on the assumption that mutually recursive types
             must exist in the same namespace. So if we only have one of them
             fully qualified, then we can apply the same qualification to
             the other types in the mut rec type declaration.
             Type names in one_inductive_body are NOT qualified,
             which makes them globally nonunique. *)
        let tys := map (fun '(i, o) =>
                          {| ty_name := (qual_pre, Ast.Env.ind_name o)%bs
                           ; ty_body := o
                           ; ty_inductive :=
                               {| inductive_mind := name ; inductive_ind := i |}
                           ; ty_params := context_names (rev (Ast.Env.ind_params b))
                           |}) (enumerate_nat (Ast.Env.ind_bodies b)) in
          tys ++ get_single_types gs'
      | None => get_single_types gs'
      end
    end.

  (* Generates the initial ind_L1_env *)
  Definition propagate_types
             (gs : Ast.Env.global_declarations)
             : glueM (list (ind_L1_tag * ty_info)) :=
    let singles := get_single_types gs in
    let res := enumerate_pos singles in
    let ienv : ind_L1_env := set_list res (M.empty _) in
    put_ind_L1_env ienv ;;
    ret res.

  (* Checks is the type in question is of sort [Prop]. *)
  Definition is_prop_type (info : ty_info) : bool :=
    let fix check_last (e : Ast.term) : bool :=
        match e with
          | Ast.tProd _ _ e' => check_last e'
          | Ast.tSort u =>
              MetaRocq.Common.Universes.Sort.is_prop u
          | _ => false
        end
    in check_last (Ast.Env.ind_type (ty_body info)).

  (* Takes in a list of types and removes the ones that are of sort [Prop].
     [Set] and [Type] are fine. CertiRocq erases [Prop]s early on,
     so no glue code is needed for those types. *)
  Fixpoint filter_prop_types
           (l : list (ind_L1_tag * ty_info)) : glueM (list (ind_L1_tag * ty_info)) :=
    match l with
    | nil => ret nil
    | (itag, info) :: xs =>
      if is_prop_type info
      then
        log ("Skipping type of sort Prop: " ++ string_of_kername (ty_name info)) ;;
        filter_prop_types xs
      else
        log ("Including type: " ++ string_of_kername (ty_name info)) ;;
        rest <- filter_prop_types xs ;;
        ret ((itag, info) :: rest)
    end.

End L1Types.

Section Printers.
  (* We need a preliminary pass to generate the names for all
    printer functions for each type because they can be mutually recursive. *)
  Fixpoint make_printer_names
          (tys : list (ind_L1_tag * ty_info))
          : glueM unit :=
    match tys with
    | nil => ret tt
    | (tag, {| ty_name := kn ; ty_body := ty |}) :: tys' =>
        pname <- gensym ("print_" ++ sanitize_qualified kn) ;;
        set_print_env tag pname ;;
        make_printer_names tys'
    end.

  Fixpoint gen_param_fun_names (params : list string) : glueM (list (string * ident)) :=
    match params with
    | nil => ret nil
    | x :: xs =>
        x' <- gensym ("print_param_" ++ x) ;;
        xs' <- gen_param_fun_names xs ;;
        ret ((x, x') :: xs')
    end.

  Fixpoint find_param_fun_name
           (param : string) (params : list (string * ident)) : option ident :=
    match params with
    | nil => None
    | (s, i) :: xs =>
        if String.eqb param s
        then Some i
        else find_param_fun_name param xs
    end.

  (* FIXME currently we assume all print functions have the same type,
     but that's not correct.
     Print functions for parametrized types take > 1 arguments. *)
  Definition ty_printer : type := Tfunction (Tcons val Tnil) tvoid cc_default.

  Definition report_inductive (i : inductive) : string :=
    "type #" ++ show_nat (inductive_ind i) ++ " in the "
             ++ string_of_kername (inductive_mind i) ++ " block".

  (* Takes a spine of the type that is about to be printed,
     and returns the correct list of printer functions for it,
     some of which may be the parameters of the type *)
  Fixpoint spine_to_args
           (spine : list dissected_type)
           (params : list (string * ident)) : glueM (option (list expr)) :=
    match spine with
    | nil => ret (Some nil)
    | dParam p :: spine' =>
        match find_param_fun_name p params with
        | None => ret None
        | Some i =>
            rest <- spine_to_args spine' params ;;
            match rest with
            | None => ret None
            | Some rest' => ret (Some ((Etempvar i ty_printer) :: rest'))
            end
        end
    | dInd arg_ind :: spine' =>
        (* We check [arg_ind] against the collection of [inductive]s
           in the L1 env. This is a bit hacky but there is no other way
           for a [dissected_type] to contain the precise [kername]
           of a type from a mutually inductive block, since we fake [kernames]
           for non-primary mutually inductive types. *)
        tagM <- get_tag_from_inductive arg_ind ;;
        match tagM with
        | None => ret None
        | Some tag =>
            printerM <- get_print_env tag ;;
            match printerM with
            | None =>
                log ("Can't find printer for the spine type "
                      ++ report_inductive arg_ind) ;;
                ret None
            | Some printer => (* success! *)
                rest <- spine_to_args spine' params ;;
                match rest with
                | None => ret None
                | Some rest' => ret (Some ((Evar printer ty_printer) :: rest'))
                end
            end
        end
    | _ :: _ => ret None
    end.

  Variable toolbox : toolbox_info.

  Definition generate_printer
             (info : ind_L1_tag * ty_info)
            : glueM (option def) :=
    let '(itag, {| ty_name := name
                 ; ty_body := b
                 ; ty_inductive := ind
                 ; ty_params := params |}) := info in
    let basename := Ast.Env.ind_name b in
    let ctors := Ast.Env.ind_ctors b in
    pnameM <- get_print_env itag ;;
    gtnameM <- get_get_tag_env itag ;;
    cnnameM <- get_ctor_names_env itag ;;
    iM <- get_ind_L1_env itag ;;
    match pnameM, gtnameM, cnnameM, iM with
    | Some pname (* name of the current print function *),
      Some gtname (* name of the elim function this will use *),
      Some (cnname, ty_names) (* name of the names array this will use *),
      Some iinfo (* L1 info about the inductive type *) =>
        _v <- gensym "v" ;;
        _tag <- gensym "tag" ;;
        _args <- gensym "args" ;;
        param_table <- gen_param_fun_names params ;;

        (* We need the maximum arity of all the ctors because
          we will declare an array for the arguments of the constructor
          of the resulting value from the eliminator *)
        let max_ctor_arity : nat := get_max_ctor_arity (Ast.Env.ind_ctors b) in

        (* if none of the constructors take any args *)
        let won't_take_args : bool := Nat.eqb max_ctor_arity 0 in

        (* names and Clight types of printf and string literals *)
        let (_printf, ty_printf) := printf_info toolbox in
        let (_get_args, ty_get_args) := get_args_info toolbox in
        let (_space, ty_space) := space_info _ (literals_info toolbox) in
        let (_lparen, ty_lparen) := lparen_info _ (literals_info toolbox) in
        let (_rparen, ty_rparen) := rparen_info _ (literals_info toolbox) in
        let (_fun, ty_fun) := fun'_info _ (literals_info toolbox) in
        let (_type, ty_type) := type'_info _ (literals_info toolbox) in
        let (_unk, ty_unk) := unk_info _ (literals_info toolbox) in
        let (_prop, ty_prop) := prop_info _ (literals_info toolbox) in

        (* function calls to printf *)
        let print_ctor_name : statement :=
          Scall None
            (Evar _printf ty_printf)
            ((Ederef
                (Ebinop Oadd
                  (Evar cnname ty_names)
                  (Etempvar _tag tint) ty_names)
                ty_names) :: nil) in
        let print_lparen : statement :=
            Scall None (Evar _printf ty_printf)
                       (Evar _lparen ty_lparen :: nil) in
        let print_rparen : statement :=
            Scall None (Evar _printf ty_printf)
                       (Evar _rparen ty_rparen :: nil) in
        let print_space : statement :=
            Scall None (Evar _printf ty_printf)
                       (Evar _space ty_space :: nil) in
        let print_unk : statement :=
            Scall None (Evar _printf ty_printf)
                       (Evar _unk ty_unk :: nil) in
        let print_prop : statement :=
            Scall None (Evar _printf ty_printf)
                       (Evar _prop ty_prop :: nil) in

        (* Generates a single function call to a printer with the right argument type *)
        let rec_print_call
            (arg : nat * dissected_type) : glueM statement :=
          match arg with
          | (_, dFun) =>
              ret (Scall None (Evar _printf ty_printf)
                              (Evar _fun ty_fun :: nil))
          | (_, dInvalid) =>
              ret print_unk
          | (_, dSort) =>
              ret (Scall None (Evar _printf ty_printf)
                              (Evar _type ty_type :: nil))
          | (i, dParam p) =>
              match find_param_fun_name p param_table with
              | None =>
                  log ("Found an unexpected param " ++ p ++ " for type " ++ string_of_kername name) ;;
                  ret print_unk
              | Some fn_name =>
                  ret (Scall None (Etempvar fn_name ty_printer)
                          (Ederef
                              (Ebinop Oadd
                                      (Ecast
                                        (Etempvar _args (tptr tvoid))
                                        (tptr val))
                                      (Econst_int (Int.repr (Z.of_nat i)) val)
                                      (tptr val)) val :: nil))
              end
          | (i, dApp (dInd arg_ind) _ as dt) (* for indexed/polymorphic types *)
          | (i, dInd arg_ind as dt) (* for monomorphic types *) =>
              (* in order to get the disjunctive pattern work
                 we need a separate match to get the spine *)
              let spine := match dt with dApp _ s => s | _ => nil end in
              (* We check [arg_ind] against the collection of [inductive]s
                 in the L1 env. This is a bit hacky but there is no other way
                 for a [dissected_type] to contain the precise [kername]
                 of a type from a mutually inductive block, since we fake [kernames]
                 for non-primary mutually inductive types. *)
              tagM <- get_tag_from_inductive arg_ind ;;
              match tagM with
              | None =>
                  log ("No L1 tag for the type " ++ string_of_kername name ++
                       " for the #" ++ show_nat i ++
                       " constructor that takes " ++ report_inductive arg_ind) ;;
                  ret Sskip (* ideally shouldn't happen *)
              | Some tag =>
                  infoM <- get_ind_L1_env tag ;;
                  match infoM with
                  | None =>
                      log ("Can't find info for the type " ++ string_of_kername name ++
                           " in recursive call") ;;
                      ret Sskip
                  | Some info =>
                      if is_prop_type info
                      then ret print_prop
                      else
                        spineM <- spine_to_args spine param_table ;;
                        printerM <- get_print_env tag ;;
                        match spineM, printerM with
                        | None , _ =>
                            log ("Couldn't create spine application for the type " ++ string_of_kername name ++
                                " for the #" ++ show_nat i ++
                                " constructor that takes " ++ report_inductive arg_ind) ;;
                            ret Sskip (* ideally shouldn't happen *)
                        | _ , None =>
                            log ("Can't find printer for the type " ++ string_of_kername name) ;;
                            ret Sskip
                        | Some spine_args , Some printer =>
                            let spine_args := (* taking in only the parameters *)
                                firstn (length (ty_params info)) spine_args in
                            ret (Scall None (Evar printer ty_printer) (* FIXME wrong type *)
                                  (Ederef
                                      (Ebinop Oadd
                                              (Ecast
                                                (Etempvar _args (tptr tvoid))
                                                (tptr val))
                                              (Econst_int (Int.repr (Z.of_nat i)) val)
                                              (tptr val)) val :: spine_args))
                        end
                  end
             end
          | _ => (* TODO expand this for other cases *)
              log ("Found a non-inductive constructor argument for " ++ string_of_kername name) ;;
              ret print_unk
          end in

        (* Generates function calls to printers with the right argument types *)
        let fix rec_print_calls
                (args : list (nat * dissected_type))
                : glueM statement :=
          match args with
          | nil => ret Sskip
          | arg :: nil => (* to handle the separator *)
              rec_print_call arg
          | arg :: args' =>
              rest <- rec_print_calls args' ;;
              call <- rec_print_call arg ;;
              ret (call ;;; print_space ;;; rest)
          end in

        (* Generates cases for the switch statement in the print function *)
        let fix switch_cases
                (ctors : list (ctor_L1_index * Ast.Env.constructor_body))
                : glueM labeled_statements :=
          match ctors with
          | nil => ret LSnil
          | (ctag, ctor) :: ctors' =>
            let ty := ctor.(Ast.Env.cstr_type) in
            let arity := ctor.(Ast.Env.cstr_arity) in
            let (args, rt) := dissect_types params (dInd ind :: nil) ty in
            calls <- rec_print_calls (enumerate_nat args) ;;
            rest <- switch_cases ctors' ;;
            ret (LScons (Some (Zpos ctag - 1)%Z)
                  (if Nat.eqb arity 0
                    then print_ctor_name ;;; Sbreak
                    else
                      Scall (Some _args) (Evar _get_args ty_get_args)
                            (Etempvar _v val :: nil) ;;;
                      print_lparen ;;;
                      print_ctor_name ;;;
                      print_space ;;;
                      calls ;;;
                      print_rparen ;;;
                      Sbreak)
                  rest)
          end in

        entire_switch <- switch_cases (enumerate_pos ctors) ;;
        let body :=
          Scall (Some _tag)
             (Evar gtname (Tfunction (Tcons val Tnil) tuint cc_default))
             ((Etempvar _v val) :: nil) ;;;
          (if won't_take_args
            then print_ctor_name
            else Sswitch (Etempvar _tag val) entire_switch) in


        (* declare an args array if any of the constructors take args,
          if not then prodArr will not be declared at all *)
        let vars : list (ident * type) :=
            if won't_take_args then nil
            else (_args, tptr tvoid) :: nil in

        (* to handle polymorphic data types *)
        let param_pairs : list (ident * type) :=
            map (fun p => let '(_, i) := p in (i, ty_printer)) param_table in

        let f := {| fn_return := tvoid
                  ; fn_callconv := cc_default
                  ; fn_params := (_v, val) :: param_pairs
                  ; fn_vars := nil
                  ; fn_temps := (_tag, tuint) :: vars
                  ; fn_body := body
                |} in
        ret (Some (pname, Gfun (Internal f)))

    (* pnameM, gtnameM, cnnameM, iM *)
    | None, _, _, _ =>
        log ("No print function name for " ++ string_of_kername name ++ ".") ;; ret None
    | _, None, _, _ =>
        log ("No get_tag_... function name for " ++ string_of_kername name ++ ".") ;; ret None
    | _, _, None, _ =>
        log ("No constructor names array name for " ++ string_of_kername name ++ ".") ;; ret None
    | _, _, _, None =>
        log ("No L1 info for the inductive type  " ++ string_of_kername name ++ ".") ;; ret None
    end.

  Fixpoint generate_printers
          (tys : list (ind_L1_tag * ty_info))
          : glueM defs :=
    match tys with
    | nil => ret nil
    | ty :: tys' =>
        rest <- generate_printers tys' ;;
        def <- generate_printer ty ;;
        match def with
        | Some def => ret (def :: rest)
        | None => ret rest
        end
    end.

End Printers.

Section CtorArrays.

  (* Pad a list by adding zeros to the end, to reach a list length of n. *)
  Definition pad_char_init (l : list init_data) (n : nat) : list init_data :=
    l ++ List.repeat (Init_int8 Int.zero) (n - (length l)).

  Fixpoint normalized_names_array
           (ctors : list Ast.Env.constructor_body)
           (n : nat) : nat * list init_data :=
    match ctors with
    | nil => (n, Init_space 0 :: nil)
             (* This may cause a warning in some C compilers.
                This is a hacky solution for that for now. *)
    | ctor :: ctors' =>
        let s := ctor.(Ast.Env.cstr_name) in
        let (max_len, init_l) :=
          normalized_names_array ctors' (max n (String.length s + 1)) in
        let i := pad_char_init (string_as_array s) max_len in
        (max_len, (i ++ init_l)%list)
    end.

  Definition make_name_array
             (tag : ind_L1_tag)
             (kn : kername)
             (ctors : list Ast.Env.constructor_body)
             : glueM def :=
    let (max_len, init_l) := normalized_names_array ctors 1 in
    let ty := tarray (tarray tschar (Z.of_nat max_len))
                     (Z.of_nat (length ctors)) in
    nname <- gensym ("names_of_" ++ sanitize_qualified kn) ;;
    set_ctor_names_env tag (nname, ty) ;;
    ret (nname, Gvar (mkglobvar ty init_l true false)).

  Fixpoint make_name_arrays
           (tys : list (ind_L1_tag * ty_info))
           : glueM defs :=
    match tys with
    | nil => ret nil
    | (tag, {| ty_name := kn; ty_body := b |}) :: tys' =>
        rest <- make_name_arrays tys' ;;
        def <- make_name_array tag kn (Ast.Env.ind_ctors b) ;;
        ret (def :: rest)
    end.

End CtorArrays.

Section CtorEnumTag.
  Variable toolbox : toolbox_info.

  Fixpoint match_ordinals_with_tag
           (ctors : list Ast.Env.constructor_body)
           (boxed unboxed total : nat)
           : list (nat * nat) * list (nat * nat) :=
    match ctors with
    | nil => (nil, nil)
    | ctor :: ctors' =>
        if unbox_check ctor
        then
          let (bs, us) := match_ordinals_with_tag ctors' boxed (S unboxed) (S total) in
          (bs, (unboxed, total) :: us)
        else
          let (bs, us) := match_ordinals_with_tag ctors' (S boxed) unboxed (S total) in
          ((boxed, total) :: bs, us)
    end.

  Fixpoint matches_to_LS
           (pairs : list (nat * nat)) : labeled_statements :=
    match pairs with
    | nil => LSnil
    | (ordinal, tag) :: pairs' =>
      LScons (Some (Z.of_nat ordinal))
             (Sreturn (Some (Econst_int (Int.repr (Z.of_nat tag)) uval)))
             (matches_to_LS pairs')
    end.

  Fixpoint get_enum_tag_from_types
          (tys : list (ind_L1_tag * ty_info))
          : glueM defs :=
    match tys with
    | nil => ret nil
    | (itag, {| ty_name := kn ; ty_body := one |}) :: tys' =>
        _b <- gensym "b" ;;
        _t <- gensym "t" ;;
        _v <- gensym "v" ;;
        let (_is_ptr, ty_is_ptr) := is_ptr_info toolbox in
        let (_guo, ty_guo) := get_unboxed_ordinal_info toolbox in
        let (_gbo, ty_gbo) := get_boxed_ordinal_info toolbox in
        let (boxed, unboxed) := match_ordinals_with_tag (Ast.Env.ind_ctors one) 0 0 0 in
        let (vars, body) := match boxed, unboxed with
          | nil, nil => (* if there are no constructors, just return 0 *)
             (nil, Sreturn (Some (Econst_int (Int.repr 0) uval)))
          | nil, _ => (* if all ctors are unboxed, then just call get_unboxed_ordinal *)
             ((_t, uval) :: nil,
              Scall (Some _t) (Evar _guo ty_guo) (Etempvar _v val :: nil) ;;;
              Sreturn (Some (Etempvar _t uval)))
          | _, nil => (* if all ctors are unboxed, then just call get_boxed_ordinal *)
             ((_t, uval) :: nil,
              Scall (Some _t) (Evar _gbo ty_gbo) (Etempvar _v val :: nil) ;;;
              Sreturn (Some (Etempvar _t uval)))
          | _, _ => (* if there are boxed and unboxed constructors, then if and switch *)
            let body :=
              Scall (Some _b) (Evar _is_ptr ty_is_ptr) (Etempvar _v val :: nil) ;;;
              Sifthenelse
                (Etempvar _b tbool)
                (Scall (Some _t) (Evar _gbo ty_gbo) (Etempvar _v val :: nil) ;;;
                Sswitch (Etempvar _t uval) (matches_to_LS boxed))
                (Scall (Some _t) (Evar _guo ty_guo) (Etempvar _v val :: nil) ;;;
                Sswitch (Etempvar _t uval) (matches_to_LS unboxed))
            in ((_b, tbool) :: (_t, uval) :: nil, body)
          end in
        gname <- gensym ("get_" ++ sanitize_qualified kn ++ "_tag") ;;
        let f := (gname,
                  Gfun (Internal
                         {| fn_return := uval
                          ; fn_callconv := cc_default
                          ; fn_params := (_v, val) :: nil
                          ; fn_vars := nil
                          ; fn_temps := vars
                          ; fn_body := body
                          |})) in
        set_get_tag_env itag gname ;;
        rest <- get_enum_tag_from_types tys' ;;
        ret (f :: rest)
    end.

End CtorEnumTag.

Section CConstructors.

  Fixpoint make_arg_list'
           (n : nat) : glueM (list (ident * type)) :=
    match n with
    | O => ret nil
    | S n' =>
        new_id <- gensym ("arg" ++ MRString.string_of_nat n')%bs ;;
        rest_id <- make_arg_list' n' ;;
        ret ((new_id, val) :: rest_id)
    end.

  Definition make_arg_list
             (n : nat) : glueM (list (ident * type)) :=
    rest <- make_arg_list' n ;;
    ret (rev rest).


  Variable toolbox : toolbox_info.
  Let _thread_info : ident := thread_info_type _ (thread_info_info toolbox).
  Let _alloc : ident := alloc_info _ (thread_info_info toolbox).

  Fixpoint constructors_from_ctors
          (name_ty : kername) (* like bool or nat *)
          (ctors : list ctor_info) (* name, arity, ordinal *)
          : glueM defs :=
    let make_name (cname : string) : string :=
      ("make_" ++ sanitize_qualified name_ty ++ "_" ++ cname)%bs in
    match ctors with
    | nil => ret nil
    | (* Unboxed *) {| ctor_name := cname ; ctor_arity := O ; ctor_ordinal := ord |} :: ctors =>
        constr_fun_id <- gensym (make_name cname) ;;
        let body :=
          Sreturn (Some (Ecast (Econst_int (Int.repr (Z.add (Z.shiftl (Z.of_nat ord) 1) 1)) val) val)) in
        let f := (constr_fun_id,
                  Gfun (Internal
                          {| fn_return := val
                           ; fn_callconv := cc_default
                           ; fn_params := nil
                           ; fn_vars := nil
                           ; fn_temps := nil
                           ; fn_body := body
                           |})) in
        rest <- constructors_from_ctors name_ty ctors ;;
        ret (f :: rest)
    | (* Boxed *) {| ctor_name := cname ; ctor_arity := ar ; ctor_ordinal := ord |} :: ctors =>
        (* We generate two different kind of constructors,
           one that takes an address to write to,
           and one that writes to the GC heap. *)

        (* 1st kind of constructor: takes address *)
        constr_fun_id <- gensym (make_name cname) ;;
        argv_ident <- gensym "argv" ;;
        arg_list <- make_arg_list ar ;;
        let asgn_s := make_constrAsgn argv_ident arg_list in
        let header := c_int ((Z.shiftl (Z.of_nat ar) 10) + (Z.of_nat ord)) val in
        let body :=
            Sassign (Field(var argv_ident, 0%Z)) ([val] header) ;;;
            asgn_s ;;;
            Sreturn (Some (add (Etempvar argv_ident argvTy) (c_int 1%Z val))) in

        let f := (constr_fun_id,
                  Gfun (Internal
                          {| fn_return := val
                           ; fn_callconv := cc_default
                           ; fn_params := arg_list ++ ((argv_ident, argvTy) :: nil)
                           ; fn_vars := nil
                           ; fn_temps := nil
                           ; fn_body := body
                           |})) in

        (* 2nd kind of constructor: writes to GC heap *)
        constr_fun_id <- gensym ("alloc_" ++ make_name cname) ;;
        _tinfo <- gensym "tinfo" ;;
        (* tinfo->alloc *)
        let alloc_expr :=
            (Efield (Ederef (Etempvar _tinfo (threadInf _thread_info))
                            (threadStructInf _thread_info))
                    _alloc (tptr val)) in
        (* e += n; *)
        let self_incr (e : expr) (n : Z) :=
            Sassign e (add e (c_int n val)) in
        (* tinfo->alloc += n; *)
        let alloc_incr (n : Z) :=
            self_incr alloc_expr n in

        let body :=
            Sassign (Etempvar argv_ident argvTy) alloc_expr ;;;
            Sassign (Field(var argv_ident, 0%Z)) header ;;;
            asgn_s ;;;
            alloc_incr (Z.of_nat (S ar)) ;;;
            Sreturn (Some (add (Etempvar argv_ident argvTy) (c_int 1%Z val))) in

        let g := (constr_fun_id,
                  Gfun (Internal
                          {| fn_return := val
                           ; fn_callconv := cc_default
                           ; fn_params := ((_tinfo, threadInf _thread_info) :: nil)
                                          ++ arg_list
                           ; fn_vars := nil
                           ; fn_temps := ((argv_ident, argvTy) :: nil)
                           ; fn_body := body
                           |})) in

        rest <- constructors_from_ctors name_ty ctors ;;
        ret (f :: g :: rest)
    end.

  Fixpoint constructors_for_tys
          (tys : list (ind_L1_tag * ty_info))
          : glueM defs :=
    match tys with
      | nil => ret nil
      | (itag, {| ty_name := kn ; ty_body := ty |}) :: tys' =>
          nameM <- get_ind_L1_env itag ;;
          match nameM with
          | None => constructors_for_tys tys'
          | Some info =>
              s' <- constructors_from_ctors
                      (ty_name info)
                      (process_ctors (Ast.Env.ind_ctors ty)) ;;
              rest <- constructors_for_tys tys' ;;
              ret (app s' rest)
          end
    end.

End CConstructors.

Section FunctionCalls.
  (* Glue code for function calls, adapted by Kathrin Stark from
     Olivier Savary Belanger's work with different number of parameters *)

  Variable toolbox : toolbox_info.
  (* Variable opts : Options. *)
  Let _thread_info : ident := thread_info_type _ (thread_info_info toolbox).
  Let _args : ident := args_info _ (thread_info_info toolbox).
  Let _closure : ident := closure_type _ (closure_info toolbox).
  Let _cfunc : ident := func_info _ (closure_info toolbox).
  Let _cenv : ident := env_info _ (closure_info toolbox).
  (* Let c_args : nat := c_args opts. *)

  (* Notations, from OSB *)
  Notation " a '::=' b " := (Sset a b) (at level 50).
  Notation "'funVar' x" := (Evar x (funTy _thread_info)) (at level 20).

  (* Definition of halt and halt_clo.
      Generate a function equivalent to halt, receives a tinfo and
      - for c_args = 1 the environment,
      - for c_args >= 2 the environment and the result.
      Hence, if c_args >= 2 we additionally have to put
      the result into *tinfo.args[1]. *)
  Definition make_halt : glueM defs :=
    opts <- ask ;;
    let c_args : nat := c_args opts in
    _env <- gensym "env" ;;
    _arg <- gensym "arg" ;;
    _tinfo <- gensym "tinfo" ;;
    _halt <- gensym "halt" ;;
    let '(_halt_clo, ty_halt_clo) := halt_clo_info toolbox in
    let argsExpr := Efield (tinfd _thread_info _tinfo) _args valPtr in (* TODO: Duplication? *)
    let args_halt := (_tinfo, (threadInf _thread_info)) ::
                     (_env, val) ::
                     (_arg, val) :: nil in
    let halt_stm := if 2 <=? c_args
                    then Sassign (Field(argsExpr, Z.of_nat 1)) (Etempvar _arg val);;; Sreturn None
                    else (Sreturn None) in
    backend <- get_backend ;;
    ret (match backend with
         | ANF => nil
         | CPS =>
            (_halt,
              Gfun (Internal (mkfunction Tvoid cc_default
                                        (firstn (S c_args) args_halt)
                                        nil nil halt_stm))) ::
            (_halt_clo,
              Gvar (mkglobvar ty_halt_clo
                              ((Init_addrof _halt Ptrofs.zero) :: Init_int 1 :: nil)
                              true false)) :: nil
         end).

  (* Function calls.

    For the CPS backend: (written by Kathrin)
    What to push in the argument array depends on c_args:
    If c_args = 0, then environment, the halting closure,
                    and the (single) argument have to be put into
                    arg[0], arg[1], and arg[2] respectively.
    If c_args = 1, as before but omit the environment and hand it over directly.
    If c_args = 2, as before but omit the environment and the halting closure.
    If c_args >= 3, no elements have to be put into the argument array.
    Call function with respective arguments.

    For the ANF backend: (added by Joomy)
    This is just tentative.
    It does the same except it doesn't assign/pass the halting closure.
    It probably needs to do something with stack frames at some point,
    we leave that as TODO for now.
    This version works for some examples in ANF but it's not extensively tested.

    It may also be a good idea to separate the ANF call function entirely.
    Maybe a separate call_anf function in C or
    a separate make_call_anf function in the glue code generator.
  *)

  Definition make_call : glueM def :=
    opts <- ask ;;
    let c_args : nat := c_args opts in
    let backend := if direct opts then ANF else CPS in

    _clo <- gensym "clo" ;;
    _f <- gensym "f" ;;
    _env <- gensym "envi" ;;
    _arg <- gensym "arg" ;;
    _tinfo <- gensym "tinfo";;
    _tmp <- gensym "tmp";;
    let '(_halt_clo, _) := halt_clo_info toolbox in

    let argsExpr := Efield (tinfd _thread_info _tinfo) _args valPtr in

    let closExpr := Etempvar _clo valPtr in
    let fargs_anf := tinf _thread_info _tinfo ::
                     Etempvar _env val ::
                     Etempvar _arg val :: nil in
    let fargs_cps := tinf _thread_info _tinfo ::
                     Etempvar _env val ::
                     Evar _halt_clo val ::
                     Etempvar _arg val :: nil in
    let fargs := match backend with ANF => fargs_anf | CPS => fargs_cps end in
    let forcelist_anf :=
        nth c_args ((* if c_args = 0 *) Tnil ::
                    (* if c_args = 1 *) Tcons val Tnil :: nil)
            (* else *) (Tcons val (Tcons val Tnil)) in
    let forcelist_cps :=
        nth c_args ((* if c_args = 0 *) Tnil ::
                    (* if c_args = 1 *) Tcons val Tnil ::
                    (* if c_args = 2 *) Tcons val (Tcons val Tnil) :: nil)
            (* else *) (Tcons val (Tcons val (Tcons val Tnil))) in
    let forcelist := match backend with ANF => forcelist_anf | CPS => forcelist_cps end in
    let ret_ty :=
      match backend with
      | ANF =>
        Tpointer (Tfunction (Tcons (threadInf _thread_info) forcelist)
                            val cc_default) noattr
      | CPS =>
        Tpointer (Tfunction (Tcons (threadInf _thread_info) forcelist)
                            Tvoid cc_default) noattr
      end in
    let deref_cast_clo :=
      Ederef (Ecast closExpr (Tpointer (Tstruct _closure noattr) noattr))
             (Tstruct _closure noattr) in
    let body :=
      _f ::= Efield deref_cast_clo _cfunc val ;;;
      _env ::= Efield deref_cast_clo _cenv val ;;;
      multiple (skipn c_args
                (* if c_args is 0 don't skip any, if it's 1 skip the first one and so on *)
                 match backend with
                 | ANF =>
                    (Sassign (Field(argsExpr, Z.of_nat 0)) (Etempvar _env val) ::
                     Sassign (Field(argsExpr, Z.of_nat 1)) (Etempvar _arg val) :: nil)
                 | CPS =>
                    (Sassign (Field(argsExpr, Z.of_nat 0)) (Etempvar _env val) ::
                     Sassign (Field(argsExpr, Z.of_nat 1)) (Evar _halt_clo val) ::
                     Sassign (Field(argsExpr, Z.of_nat 2)) (Etempvar _arg val) :: nil)
                 end) ;;;
      match backend with
      | ANF =>
        Scall (Some _tmp) ([ret_ty] (var _f)) (firstn (S c_args) fargs) ;;;
        Sreturn (Some (Etempvar _tmp val))
      | CPS =>
        Scall None ([ret_ty] (var _f)) (firstn (S c_args) fargs) ;;;
        Sreturn (Some (Field(argsExpr, Z.of_nat 1)))
      end in

    let params := (_tinfo, (threadInf _thread_info)) ::
                  (_clo, val) ::
                  (_arg, val) :: nil in
    let vars := (_f, val) ::
                (_env, val) ::
                match backend with
                | ANF => (_tmp, val) :: nil
                | CPS => nil
                end in
    _call <- gensym "call" ;;
    ret (_call,
         Gfun (Internal
                 {| fn_return := val
                  ; fn_callconv := cc_default
                  ; fn_params := params
                  ; fn_vars := nil
                  ; fn_temps := vars
                  ; fn_body := body
                  |})).

End FunctionCalls.

(* Generates the header and the source programs *)
Definition make_glue_program
           (gs : Ast.Env.global_declarations)
           : glueM (option Clight.program * option Clight.program) :=
  '(composites, externs, toolbox) <- make_externs ;;
  singles <- (propagate_types >=> filter_prop_types) gs ;;
  name_defs <- make_name_arrays singles ;;
  ctor_defs <- constructors_for_tys toolbox singles ;;
  get_tag_defs <- get_enum_tag_from_types toolbox singles ;;
  make_printer_names singles;;
  printer_defs <- generate_printers toolbox singles ;;
  halt_defs <- make_halt toolbox ;;
  call_def <- make_call toolbox ;;
  nenv <- gets gstate_nenv ;;
  let glob_defs := (externs ++ name_defs ++ ctor_defs ++ get_tag_defs ++
                   printer_defs ++ halt_defs ++ call_def :: nil)%list in
  let pi := map fst glob_defs in
  ret (mk_prog_opt nil (make_extern_decls nenv glob_defs true)
                   main_ident true,
       mk_prog_opt composites glob_defs
                   main_ident true).

(* The entry point for glue code generation *)
Definition generate_glue
           (opts : Options)
           (globs : Ast.Env.global_declarations) (* an L1 program *)
           : error (name_env * Clight.program * Clight.program * list string) :=
  let init : gstate_data :=
      {| gstate_gensym := 2%positive
       ; gstate_ienv   := M.empty _
       ; gstate_nenv   := M.empty _
       ; gstate_gtenv  := M.empty _
       ; gstate_cnenv  := M.empty _
       ; gstate_penv   := M.empty _
       ; gstate_log    := nil
       |} in
  let '(err, st) := runState (make_glue_program (rev globs)) opts init in
  let nenv := gstate_nenv st in
  match err with
  | Err s => Err s
  | Ret (Some header, Some source) =>
    Ret (nenv (* the name environment to be passed to C generation *) ,
         header (* the header content *),
         source (* the source content *),
         rev (gstate_log st) (* logged messages *))
  | Ret _ => Err "No Clight program generated"
  end.
