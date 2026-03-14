(**********************************************************************)
(* CertiRocq                                                           *)
(* Copyright (c) 2017                                                 *)
(**********************************************************************)

open Printer
open Metarocq_template_plugin.Ast_quoter
open ExceptionMonad
open AstCommon
open Plugin_utils

let get_stringopt_option key =
  let open Goptions in
  match get_option_value key with
  | Some get -> fun () ->
      begin match get () with
      | StringOptValue b -> b
      | _ -> assert false
      end
  | None ->
    (declare_stringopt_option_and_ref ~key ~value:None ()).get

let get_build_dir_opt =
  get_stringopt_option ["CertiRocq"; "Build"; "Directory"]

let get_ocamlfind =
  get_stringopt_option ["CertiRocq"; "ocamlfind"]

let get_c_compiler =
  get_stringopt_option ["CertiRocq"; "CC"]
        
(* Taken from Coq's increment_subscript, but works on strings rather than idents *)
let increment_subscript id =
  let len = String.length id in
  let rec add carrypos =
    let c = id.[carrypos] in
    if Util.is_digit c then
      if Int.equal (Char.code c) (Char.code '9') then begin
        assert (carrypos>0);
        add (carrypos-1)
      end
      else begin
        let newid = Bytes.of_string id in
        Bytes.fill newid (carrypos+1) (len-1-carrypos) '0';
        Bytes.set newid carrypos (Char.chr (Char.code c + 1));
        newid
      end
    else begin
      let newid = Bytes.of_string (id^"0") in
      if carrypos < len-1 then begin
        Bytes.fill newid (carrypos+1) (len-1-carrypos) '0';
        Bytes.set newid (carrypos+1) '1'
      end;
      newid
    end
  in String.of_bytes (add (len-1))

let debug_reify = CDebug.create ~name:"certirocq-reify" ()

external get_unboxed_ordinal : Obj.t -> int = "get_unboxed_ordinal" [@@noalloc]

external get_boxed_ordinal : Obj.t -> (int [@untagged]) = "get_boxed_ordinal" "get_boxed_ordinal" [@@noalloc]

(** Various Utils *)

let pr_string s = Pp.str (Caml_bytestring.caml_string_of_bytestring s)

(* remove duplicates but preserve order, keep the leftmost element *)
let nub (xs : 'a list) : 'a list = 
  List.fold_right (fun x xs -> if List.mem x xs then xs else x :: xs) xs []

let rec coq_nat_of_int x =
  match x with
  | 0 -> Datatypes.O
  | n -> Datatypes.S (coq_nat_of_int (pred n))

let debug_msg (flag : bool) (s : string) =
  if flag then
    Feedback.msg_debug (Pp.str s)
  else ()

(* Separate registration of primitive extraction *)

type prim = ((Kernames.kername * Kernames.ident) * bool)
let global_registers = 
  Summary.ref (([], []) : prim list * import list) ~name:"CertiRocq Registration"

let global_registers_name = "certirocq-registration"

let cache_registers (prims, imports) =
  let (prims', imports') = !global_registers in
  global_registers := (prims @ prims', imports @ imports')
let global_registers_input = 
  let open Libobject in 
  declare_object 
    (global_object_nodischarge global_registers_name
    ~cache:(fun r -> cache_registers r)
    ~subst:None) (*(fun (msub, r) -> r)) *)

let register (prims : prim list) (imports : import list) : unit =
  let curlib = Sys.getcwd () in
  let newr = (prims, List.map (fun i -> 
    match i with
    | FromAbsolutePath s -> FromRelativePath (Filename.concat curlib s)
    | _ -> i) imports) in
  (* Feedback.msg_debug Pp.(str"Prims: " ++ prlist_with_sep spc (fun ((x, y), wt) -> str (string_of_bytestring y)) (fst newr)); *)
  Lib.add_leaf (global_registers_input newr)

let get_global_prims () = fst !global_registers
let get_global_includes () = snd !global_registers

(* Extract Inductive *)
type inductive_mapping = Kernames.inductive * (string * int list) (* Target inductive type and mapping of constructor names to constructor tags *)
type inductives_mapping = inductive_mapping list

let global_inductive_registers = 
  Summary.ref ([] : inductives_mapping) ~name:"CertiRocq Extract Inductive Registration"

let global_inductive_registers_name = "certirocq-extract-inductive-registration"

let cache_inductive_registers inds =
  let inds' = !global_inductive_registers in
  global_inductive_registers := inds @ inds'

let global_inductive_registers_input = 
  let open Libobject in 
  declare_object 
    (global_object_nodischarge global_inductive_registers_name
    ~cache:(fun r -> cache_inductive_registers r)
    ~subst:None)

let register_inductives (inds : inductives_mapping) : unit =
  Lib.add_leaf (global_inductive_registers_input inds)

let get_global_inductives_mapping () = !global_inductive_registers

(* Extract Inductive to Constants *)

type extract_inductive = { cstrs : Kernames.kername list; elim : Kernames.kername }
type extract_inductives = (Kernames.kername * extract_inductive list) list

let global_inductive_constant_registers =
  Summary.ref ([] : extract_inductives) ~name:"CertiRocq Inductive to Constants Registration"

let global_inductive_constant_registers_name = "certirocq-inductive-constants-registration"

let cache_inductive_constant_registers inds =
  let inds' = !global_inductive_constant_registers in
  global_inductive_constant_registers := inds @ inds'

let global_inductive_constant_registers_input =
  let open Libobject in
  declare_object
    (global_object_nodischarge global_inductive_constant_registers_name
    ~cache:(fun r -> cache_inductive_constant_registers r)
    ~subst:None)

let register_constant_inductives (extr : extract_inductives) : unit =
  Lib.add_leaf (global_inductive_constant_registers_input extr)

let get_global_inductives_constant_mapping () = !global_inductive_constant_registers

(* Support for dynamically-linked certirocq-compiled programs *)
type certirocq_run_function = unit -> Obj.t

let certirocq_run_functions =
  Summary.ref ~local:true ~name:"CertiRocq Run Functions Table"
    (CString.Map.empty : certirocq_run_function CString.Map.t)

let certirocq_run_functions_name = "certirocq-run-functions-registration"

let all_run_functions = ref CString.Set.empty

let cache_certirocq_run_function (s, s', fn) =
  let fns = !certirocq_run_functions in
  all_run_functions := CString.Set.add s (CString.Set.add s' !all_run_functions);
  certirocq_run_functions := CString.Map.add s fn fns

let certirocq_run_function_input =
  let open Libobject in
  declare_object 
    (local_object_nodischarge certirocq_run_functions_name
    ~cache:(fun r -> cache_certirocq_run_function r))

let register_certirocq_run s s' fn =
  (* Feedback.msg_debug Pp.(str"Registering function " ++ str s ++ str " in certirocq_run"); *)
  Lib.add_leaf (certirocq_run_function_input (s, s', fn))

let exists_certirocq_run s =
  (* Feedback.msg_debug Pp.(str"Looking up " ++ str s ++ str " in certirocq_run_functions"); *)
  let res = CString.Map.find_opt s !certirocq_run_functions in
  (* if Option.is_empty res then Feedback.msg_debug Pp.(str"Not found"); *)
  res
  
let run_certirocq_run s =
  try CString.Map.find s !certirocq_run_functions
  with Not_found -> CErrors.user_err Pp.(str"Could not find certirocq run function associated to " ++ str s)

(** Coq FFI: message channels and raising user errors. *)

let rocq_msg_info s =
  let s = Caml_bytestring.caml_string_of_bytestring s in
  Feedback.msg_info (Pp.str s)
  
let _ = Callback.register "rocq_msg_info" rocq_msg_info

let rocq_msg_debug s =
  Feedback.msg_debug Pp.(str (Caml_bytestring.caml_string_of_bytestring s))
  
let _ = Callback.register "rocq_msg_debug" rocq_msg_debug

let rocq_msg_notice s =
  Feedback.msg_notice Pp.(str (Caml_bytestring.caml_string_of_bytestring s))
  
let _ = Callback.register "rocq_msg_notice" rocq_msg_notice
  
let rocq_user_error s =
  CErrors.user_err Pp.(str (Caml_bytestring.caml_string_of_bytestring s))

let _ = Callback.register "rocq_user_error" rocq_user_error

(** Compilation Command Arguments *)

type command_args =
 | TYPED_ERASURE
 | UNSAFE_ERASURE
 | BYPASS_QED
 | CPS
 | TIME
 | TIMEANF
 | OPT of int
 | DEBUG
 | ARGS of int
 | ANFCONFIG of int (* To measure different ANF configurations *)
 | BUILDDIR of string (* Directory name to be prepended to the file name *)
 | EXT of string (* Filename extension to be appended to the file name *)
 | DEV of int    (* For development purposes *)
 | PREFIX of string (* Prefix to add to the generated FFI fns, avoids clashes with C fns *)
 | TOPLEVEL_NAME of string (* Name of the toplevel function ("body" by default) *)
 | FILENAME of string (* Name of the generated file *)

type options =
  { typed_erasure : bool;
    unsafe_erasure : bool;
    bypass_qed : bool;
    cps       : bool;
    time      : bool;
    time_anf  : bool;
    olevel    : int;
    debug     : bool;
    args      : int;
    anf_conf  : int;
    build_dir : string;
    filename  : string;
    ext       : string;
    dev       : int;
    prefix    : string;
    toplevel_name : string;
    prims     : ((Kernames.kername * Kernames.ident) * bool) list;
    inductives_mapping : inductives_mapping;
    extracted_inductives : extract_inductives;
  }

let check_build_dir d =
  if d = "" then "." else
  let isdir = 
    try Unix.((stat d).st_kind = S_DIR)
    with Unix.Unix_error (Unix.ENOENT, _, _) ->
      CErrors.user_err Pp.(str "Could not compile: build directory " ++ str d ++ str " not found.")
  in
  if not isdir then 
    CErrors.user_err Pp.(str "Could not compile: " ++ str d ++ str " is not a directory.")
  else d
  
let default_options () : options =
  { typed_erasure = false;
    unsafe_erasure = false;
    bypass_qed = false;
    cps       = false;
    time      = false;
    time_anf  = false;
    olevel    = 1;
    debug     = false;
    args      = 5;
    anf_conf  = 0;
    build_dir = (match get_build_dir_opt () with None -> "." | Some s -> check_build_dir s);
    filename  = "";
    ext       = "";
    dev       = 0;
    prefix    = "";
    toplevel_name = "body";
    prims     = [];
    inductives_mapping = get_global_inductives_mapping ();
    extracted_inductives = get_global_inductives_constant_mapping ();
  }

let make_options (l : command_args list) (pr : ((Kernames.kername * Kernames.ident) * bool) list) (fname : string) : options =
  let rec aux (o : options) l =
    match l with
    | [] -> o
    | TYPED_ERASURE :: xs -> aux {o with typed_erasure = true} xs
    | UNSAFE_ERASURE :: xs -> aux {o with unsafe_erasure = true} xs
    | BYPASS_QED :: xs -> aux {o with bypass_qed = true} xs
    | CPS      :: xs -> aux {o with cps = true} xs
    | TIME     :: xs -> aux {o with time = true} xs
    | TIMEANF  :: xs -> aux {o with time_anf = true} xs
    | OPT n    :: xs -> aux {o with olevel = n} xs
    | DEBUG    :: xs -> aux {o with debug = true} xs
    | ARGS n   :: xs -> aux {o with args = n} xs
    | ANFCONFIG n :: xs -> aux {o with anf_conf = n} xs
    | BUILDDIR s  :: xs ->
      let s = check_build_dir s in
      aux {o with build_dir = s} xs
    | EXT s    :: xs -> aux {o with ext = s} xs
    | DEV n    :: xs -> aux {o with dev = n} xs
    | PREFIX s :: xs -> aux {o with prefix = s} xs
    | TOPLEVEL_NAME s :: xs -> aux {o with toplevel_name = s} xs
    | FILENAME s :: xs -> aux {o with filename = s} xs
  in
  let opts = { (default_options ()) with filename = fname } in
  let o = aux opts l in
  {o with prims = pr}

let make_unsafe_passes b = 
  let open Erasure0 in
  { cofix_to_lazy = b;
    inlining = b; 
    unboxing = b;
    betared = b;
    inductives_extraction = b }

let all_unsafe_passes = make_unsafe_passes true
let no_unsafe_passes = make_unsafe_passes false

let quote_inductives_mapping l =
  List.map (fun (hd, (na, cstrs)) -> (hd, (bytestring_of_string na, List.map (fun i -> coq_nat_of_int i) cstrs))) l

let make_pipeline_options (opts : options) =
  let erasure_config = 
      Erasure0.({ 
        enable_typed_erasure = opts.typed_erasure; 
        enable_unsafe = if opts.unsafe_erasure then all_unsafe_passes else no_unsafe_passes;
        dearging_config = default_dearging_config;
        inlined_constants = Kernames.KernameSet.empty;
        extracted_inductives = Obj.magic opts.extracted_inductives; (* kername and list representation are the same *)
        })
  in
  let cps    = opts.cps in
  let args = coq_nat_of_int opts.args in
  let olevel = coq_nat_of_int opts.olevel in
  let timing = opts.time in
  let timing_anf = opts.time_anf in
  let debug  = opts.debug in
  let anfc = coq_nat_of_int opts.anf_conf in
  let dev = coq_nat_of_int opts.dev in
  let prefix = bytestring_of_string opts.prefix in
  let toplevel_name = bytestring_of_string opts.toplevel_name in
  let prims = get_global_prims () @ opts.prims in
  let inductives_mapping = quote_inductives_mapping opts.inductives_mapping in
  (* Feedback.msg_debug Pp.(str"Prims: " ++ prlist_with_sep spc (fun ((x, y), wt) -> str (string_of_bytestring y)) prims); *)
  Pipeline.make_opts erasure_config inductives_mapping cps args anfc olevel timing timing_anf debug dev prefix toplevel_name prims

(** Main Compilation Functions *)

(* Get fully qualified name of a constant *)
let get_name (gr : Names.GlobRef.t) : string =
  match gr with
  | Names.GlobRef.ConstRef c -> Names.KerName.to_string (Names.Constant.canonical c)
  | _ -> CErrors.user_err Pp.(Printer.pr_global gr ++ str " is not a constant definition")


(* Quote Coq term *)
let quote_term ~opaque_access opts env sigma c =
  let debug = opts.debug in
  let bypass = opts.bypass_qed in
  debug_msg debug "Quoting";
  let time = Unix.gettimeofday() in
  let term = Metarocq_template_plugin.Ast_quoter.quote_term_rec ~bypass ~opaque_access env sigma (EConstr.to_constr sigma c) in
  let time = (Unix.gettimeofday() -. time) in
  debug_msg debug (Printf.sprintf "Finished quoting in %f s.. compiling to L7." time);
  term

let quote ~opaque_access opts gr =
  let env = Global.env () in
  let sigma = Evd.from_env env in
  let sigma, c = Evd.fresh_global env sigma gr in
  quote_term ~opaque_access opts env sigma c

(* Compile Quoted term with CertiRocq *)

module type CompilerInterface = sig
  type name_env
  val compile : Pipeline_utils.coq_Options -> Ast0.Env.program -> ((name_env * Clight.program) * Clight.program) CompM.error * Bytestring.String.t
  val printProg : Clight.program -> name_env -> string -> import list -> unit

  val generate_glue : Pipeline_utils.coq_Options -> Ast0.Env.global_declarations -> 
    (((name_env * Clight.program) * Clight.program) * Bytestring.String.t list) CompM.error
  
  val generate_ffi :
    Pipeline_utils.coq_Options -> Ast0.Env.program -> (((name_env * Clight.program) * Clight.program) * Bytestring.String.t list) CompM.error
  
end


module FixRepr = 
struct

(** The ML value representation of an erased quoted program does not directly match 
  the one expected by CertiRocq erase function as singleton inductive types are unboxed,
  we use Obj.t surgery to transform the value. 
  
  This involves the transformation of universes sets, constraints sets and the representation
  of universe values.
  *)

let fix_set u =
  let block = Obj.new_block 0 1 in
  Obj.set_field block 0 (Obj.magic u);
  block

let fix_universe u =
  let open Universes0.Sort in
  let fix_ues ues : Obj.t = 
    let block = Obj.new_block 0 1 in
    Obj.set_field block 0 (Obj.magic ues);
    block
  in
  let fix_neues neues : Obj.t = 
    let ues = fix_ues neues in
    let block = Obj.new_block 0 1 in
    Obj.set_field block 0 ues;
    block
  in
  match u with 
  | Coq_sProp -> Coq_sProp
  | Coq_sSProp -> Coq_sSProp
  | Coq_sType neues -> Coq_sType (Obj.magic (fix_neues neues))

let fix_term (p : Ast0.term) : Ast0.term =
  let open Ast0 in
  let open BasicAst in
  let open List in
  let rec aux p = 
  match p with
  | Coq_tRel _ | Coq_tVar _ | Coq_tConst _ | Coq_tInd _ | Coq_tConstruct _ -> p
  | Coq_tEvar (k, l) -> Coq_tEvar (k, map aux l)
  | Coq_tSort u -> Coq_tSort (fix_universe u)
  | Coq_tCast (t, k, t') -> Coq_tCast (aux t, k, aux t')
  | Coq_tProd (na, t, t') -> Coq_tProd (na, aux t, aux t')
  | Coq_tLambda (na, t, t') -> Coq_tLambda (na, aux t, aux t')
  | Coq_tLetIn (na, t, b, t') -> Coq_tLetIn (na, aux t, aux b, aux t')
  | Coq_tApp (t, l) -> Coq_tApp (aux t, map aux l)
  | Coq_tCase (ci, p, c, brs) -> Coq_tCase (ci, aux_pred p, aux c, map aux_branch brs)
  | Coq_tProj (p, t) -> Coq_tProj (p, aux t)
  | Coq_tFix (mfix, i) -> Coq_tFix (map aux_def mfix, i)
  | Coq_tCoFix (mfix, i) -> Coq_tCoFix (map aux_def mfix, i)
  | Coq_tInt i -> p
  | Coq_tFloat f -> p
  | Coq_tString s -> p
  | Coq_tArray (u, v, def, ty) -> Coq_tArray (u, map aux v, aux def, aux ty)
  and aux_pred { puinst = puinst; pparams = pparams; pcontext = pcontext; preturn = preturn } =
    { puinst; pparams = map aux pparams; pcontext; preturn = aux preturn }
  and aux_branch { bcontext = bcontext; bbody = bbody } =
    { bcontext; bbody = aux bbody }
  and aux_def { dname = dname; dtype = dtype; dbody = dbody; rarg = rarg } =
    { dname; dtype = aux dtype; dbody = aux dbody; rarg }
  in aux p

let option_map f (x : 'a option) = 
  match x with
  | None -> Datatypes.None
  | Some x -> Datatypes.Some (f x)

let fix_rel_context ctx =
  let open BasicAst in 
  let fix_decl {decl_name; decl_body; decl_type} =
    {decl_name; decl_body = option_map fix_term (Obj.magic decl_body); decl_type = fix_term decl_type}
  in
  List.map fix_decl ctx
  
open Ast0
open Universes0

let fix_universes_decl = function
  | Monomorphic_ctx -> Monomorphic_ctx
  | Polymorphic_ctx (names, set) -> Polymorphic_ctx (names, Obj.magic (fix_set set))
  
let fix_universes (levels, cstrs) = 
  (Obj.magic (fix_set levels), Obj.magic (fix_set cstrs))

let fix_declarations decls = 
  let open Ast0.Env in
  let fix_constructor {cstr_name; cstr_args; cstr_indices; cstr_type; cstr_arity} = 
    {cstr_name; cstr_args = fix_rel_context cstr_args; 
     cstr_indices = List.map fix_term cstr_indices; 
     cstr_type = fix_term cstr_type; 
     cstr_arity}
  in
  let fix_projection {proj_name; proj_relevance; proj_type} =
    { proj_name; proj_relevance; proj_type = fix_term proj_type }
  in  
  let fix_ind_body {ind_name; ind_indices; ind_sort; ind_type; ind_kelim; ind_ctors; ind_projs; ind_relevance} =
    {ind_name; ind_indices = fix_rel_context ind_indices; ind_sort = fix_universe ind_sort;
     ind_type = fix_term ind_type; ind_kelim; 
     ind_ctors = List.map fix_constructor ind_ctors; 
     ind_projs = List.map fix_projection ind_projs; 
     ind_relevance}
  in
  let fix_decl (kn, decl) =
    let decl' = match decl with
    | Ast0.Env.ConstantDecl {cst_type; cst_body; cst_universes; cst_relevance} ->
      Ast0.Env.ConstantDecl { cst_type = fix_term cst_type; cst_body = option_map fix_term (Obj.magic cst_body);
      cst_universes = fix_universes_decl cst_universes; cst_relevance }
    | Ast0.Env.InductiveDecl { ind_finite; ind_npars; ind_params; ind_bodies; ind_universes; ind_variance} ->
      Ast0.Env.InductiveDecl { ind_finite; ind_npars; ind_params = fix_rel_context ind_params; 
      ind_bodies = List.map fix_ind_body ind_bodies; 
      ind_universes = fix_universes_decl ind_universes; 
      ind_variance}
    in (kn, decl')
  in
  List.map fix_decl decls

let fix_quoted_program (p : Ast0.Env.program) = 
  let ({ Ast0.Env.universes = universes; declarations = declarations; retroknowledge = retro }, term) = p in
  let term = fix_term term in
  let universes = fix_universes universes in
  let declarations = fix_declarations declarations in
  { Ast0.Env.universes = universes; declarations; retroknowledge = retro }, term

end

let fix_opts opts = 
  Pipeline_utils.{ opts with erasure_config = 
    { opts.erasure_config with Erasure0.inlined_constants = Obj.magic (FixRepr.fix_set opts.erasure_config.Erasure0.inlined_constants) } }

module MLCompiler : CompilerInterface with 
  type name_env = BasicAst.name Cps.M.t
  = struct
  type name_env = BasicAst.name Cps.M.t
  let compile opts prg =
    let opts = fix_opts opts in
    Pipeline.compile opts (FixRepr.fix_quoted_program prg)
  let printProg prog names (dest : string) (imports : import list) =
    let imports' = List.map (fun i -> match i with
      | FromRelativePath s -> "#include \"" ^ s ^ "\""
      | FromLibrary (s, _) -> "#include <" ^ s ^ ">"
      | FromAbsolutePath s ->
          failwith "Import with absolute path should have been filled") imports in
    PrintClight.print_dest_names_imports prog (Cps.M.elements names) dest imports'

  let generate_glue opts decls = 
    let opts = fix_opts opts in
    Glue.generate_glue opts (FixRepr.fix_declarations decls)
  let generate_ffi opts prg =
    let opts = fix_opts opts in
    Ffi.generate_ffi opts (FixRepr.fix_quoted_program prg)
end


module CompileFunctor (CI : CompilerInterface) = struct

  let make_fname opts str =
    Filename.concat opts.build_dir str

  type line = 
  | EOF
  | Info of string
  | Error of string
  
  let read_line stdout stderr =
    try Info (input_line stdout)
    with End_of_file -> 
      try Error (input_line stderr)
    with End_of_file -> EOF
  
  let push_line buf line =
    Buffer.add_string buf line; 
    Buffer.add_string buf "\n"
  
  let string_of_buffer buf = Bytes.to_string (Buffer.to_bytes buf)
    
  let execute cmd =
    debug Pp.(fun () -> str "Executing: " ++ str cmd ++ str " in environemt: " ++ 
      prlist_with_sep spc str (Array.to_list (Unix.environment ())));
    let (stdout, stdin, stderr) = Unix.open_process_full cmd (Unix.environment ()) in
    let continue = ref true in
    let outbuf, errbuf = Buffer.create 100, Buffer.create 100 in
    let push_info = push_line outbuf in
    let push_error = push_line errbuf in
    while !continue do
      match read_line stdout stderr with
      | EOF -> debug Pp.(fun () -> str "Program terminated"); continue := false
      | Info s -> push_info s
      | Error s -> push_error s
    done;
    let status = Unix.close_process_full (stdout, stdin, stderr) in
    status, string_of_buffer outbuf, string_of_buffer errbuf
    
  let execute ?loc cmd =
    let status, out, err = execute cmd in
    match status with
    | Unix.WEXITED 0 -> out, err
    | Unix.WEXITED n -> 
      CErrors.user_err ?loc Pp.(str"Command" ++ spc () ++ str cmd ++ spc () ++
        str"exited with code " ++ int n ++ str "." ++ fnl () ++
        str"stdout: " ++ spc () ++ str out ++ fnl () ++ str "stderr: " ++ str err)
    | Unix.WSIGNALED n | Unix.WSTOPPED n -> 
      CErrors.user_err ?loc Pp.(str"Command" ++ spc () ++ str cmd ++ spc () ++ 
      str"was signaled with code " ++ int n ++ str"." ++ fnl () ++
      str"stdout: " ++ spc () ++ str out ++ fnl () ++ str "stderr: " ++ str err)
    
  let compile opts term imports =
    let debug = opts.debug in
    let options = make_pipeline_options opts in
    let runtime_imports = [FromLibrary ((if opts.cps then "gc.h" else "gc_stack.h"), None)] in
    let curlib = Sys.getcwd () in
    let imports = List.map (fun i -> 
      match i with
      | FromAbsolutePath s -> FromRelativePath (Filename.concat curlib s)
      | _ -> i) imports in
    let imports = runtime_imports @ get_global_includes () @ imports in
    let p = CI.compile options term in
    match p with
    | (CompM.Ret ((nenv, header), prg), dbg) ->
      debug_msg debug "Finished compiling, printing to file.";
      let time = Unix.gettimeofday() in
      let fname = opts.filename in
      let suff = opts.ext in
      let cstr = fname ^ suff ^ ".c" in
      let hstr = fname ^ suff ^ ".h" in
      let cstr' = make_fname opts cstr in
      let hstr' = make_fname opts hstr in
      CI.printProg prg nenv cstr' (imports @ [FromRelativePath hstr]);
      CI.printProg header nenv hstr' (runtime_imports);

      (* let cstr = Metarocq_template_plugin.Tm_util.string_to_list (Names.KerName.to_string (Names.Constant.canonical const) ^ suff ^ ".c") in
      * let hstr = Metarocq_template_plugin.Tm_util.string_to_list (Names.KerName.to_string (Names.Constant.canonical const) ^ suff ^ ".h") in
      * Pipeline.printProg (nenv,prg) cstr;
      * Pipeline.printProg (nenv,header) hstr; *)
      let time = (Unix.gettimeofday() -. time) in
      debug_msg debug (Printf.sprintf "Printed to file %s in %f s.." cstr' time);
      debug_msg debug "Pipeline debug:";
      debug_msg debug (string_of_bytestring dbg)
    | (CompM.Err s, dbg) ->
      debug_msg debug "Pipeline debug:";
      debug_msg debug (string_of_bytestring dbg);
      CErrors.user_err Pp.(str "Could not compile: " ++ (pr_string s) ++ str "\n")


  (* Generate glue code for the compiled program *)
  let generate_glue (standalone : bool) opts globs =
    if standalone && opts.filename = "" then
      CErrors.user_err Pp.(str "You need to provide a file name with the -file option.")
    else
    let debug = opts.debug in
    let options = make_pipeline_options opts in
    let runtime_imports = 
      [ FromLibrary ((if opts.cps then "gc.h" else "gc_stack.h"), None); FromLibrary ("stdio.h", None) ] in
    let time = Unix.gettimeofday() in
    (match CI.generate_glue options globs with
    | CompM.Ret (((nenv, header), prg), logs) ->
      let time = (Unix.gettimeofday() -. time) in
      debug_msg debug (Printf.sprintf "Generated glue code in %f s.." time);
      (match logs with [] -> () | _ ->
        debug_msg debug (Printf.sprintf "Logs:\n%s" (String.concat "\n" (List.map string_of_bytestring logs))));
      let time = Unix.gettimeofday() in
      let suff = opts.ext in
      let fname = opts.filename in
      let cstr = if standalone then fname ^ ".c" else "glue." ^ fname ^ suff ^ ".c" in
      let hstr = if standalone then fname ^ ".h" else "glue." ^ fname ^ suff ^ ".h" in
      let cstr' = make_fname opts cstr in
      let hstr' = make_fname opts hstr in
      CI.printProg prg nenv cstr' (runtime_imports @ [FromRelativePath hstr]);
      CI.printProg header nenv hstr' runtime_imports;

      let time = (Unix.gettimeofday() -. time) in
      debug_msg debug (Printf.sprintf "Printed glue code to file %s in %f s.." cstr time)
    | CompM.Err s ->
      CErrors.user_err Pp.(str "Could not generate glue code: " ++ pr_string s))

  let compile_only ~opaque_access (opts : options) (gr : Names.GlobRef.t) (imports : import list) : unit =
    let term = quote ~opaque_access opts gr in
    compile opts (Obj.magic term) imports

  let generate_glue_only ~opaque_access opts gr =
    let term = quote ~opaque_access opts gr in
    generate_glue true opts (Ast0.Env.declarations (fst (Obj.magic term)))
    
  let find_executable debug cmd = 
    let whichcmd = Unix.open_process_in cmd in
    let result = 
      try Stdlib.input_line whichcmd 
      with End_of_file -> ""
    in
    let status = Unix.close_process_in whichcmd in
    match status with
    | Unix.WEXITED 0 -> 
      if debug then Feedback.msg_debug Pp.(str "Compiler is " ++ str result);
      result
    | _ -> failwith "Compiler not found"

  let compiler_executable debug = 
    match get_c_compiler () with
    | None -> find_executable debug "which gcc || which clang-11"
    | Some s -> s
  
  let ocamlfind_executable debug = 
    match get_ocamlfind () with
    | None -> find_executable debug "which ocamlfind"
    | Some s -> s
      
  let read_line stdout stderr =
    try Info (input_line stdout)
    with End_of_file -> 
      try Error (input_line stderr)
      with End_of_file -> EOF
  
  let run_program debug prog =
    let (stdout, stdin, stderr) = Unix.open_process_full ("./" ^ prog) (Unix.environment ()) in
    let continue = ref true in
    while !continue do 
      match read_line stdout stderr with
      | EOF -> debug_msg debug ("Program terminated"); continue := false
      | Info s -> Feedback.msg_notice Pp.(str prog ++ str": " ++ str s)
      | Error s -> Feedback.msg_warning Pp.(str prog ++ str": " ++ str s)
    done;
    ignore (Unix.close_process_full (stdout, stdin, stderr))

  let runtime_dir () = 
    let open Boot in
    let env = Env.init_with ~coqlib:None in
    Path.relative (Path.relative (Path.relative (Env.user_contrib env) "CertiRocq") "Plugin") "runtime"

  let make_rt_file na =
    Boot.Env.Path.(to_string (relative (runtime_dir ()) na))

  let compile_C ~opaque_access opts gr imports =
    let () = compile_only ~opaque_access opts gr imports in
    let imports = get_global_includes () @ imports in
    let debug = opts.debug in
    let fname = opts.filename in
    let suff = opts.ext in
    let name = make_fname opts (fname ^ suff) in
    let compiler = compiler_executable debug in
    let rt_dir = runtime_dir () in
    let cmd =
        Printf.sprintf "%s -Wno-everything -O2 -fomit-frame-pointer -g -I %s -I %s -c -o %s %s" 
          compiler opts.build_dir (Boot.Env.Path.to_string rt_dir) (name ^ ".o") (name ^ ".c") 
    in
    let importso =
      let oname s = 
        assert (CString.is_suffix ".h" s);
        String.sub s 0 (String.length s - 2) ^ ".o"
      in 
      let imports' = List.concat (List.map (fun i -> 
        match i with 
        | FromAbsolutePath s -> [oname s]
        | FromRelativePath s -> [oname s]
        | FromLibrary (s, _) -> [make_rt_file (oname s)]) imports) in
      let l = make_rt_file "certirocq_run_main.o" :: imports' in
      String.concat " " l
    in
    let gc_stack_o = make_rt_file "gc_stack.o" in
    debug_msg debug (Printf.sprintf "Executing command: %s" cmd);
    match Unix.system cmd with
    | Unix.WEXITED 0 -> 
      let linkcmd =
        Printf.sprintf "%s -Wno-everything -g -L %s -L %s -o %s %s %s %s" 
          compiler opts.build_dir (Boot.Env.Path.to_string rt_dir) name gc_stack_o (name ^ ".o") importso
      in
      debug_msg debug (Printf.sprintf "Executing command: %s" linkcmd);
      (match Unix.system linkcmd with
      | Unix.WEXITED 0 ->
          debug_msg debug (Printf.sprintf "Compilation ran fine, running %s" name);
          run_program debug name
      | Unix.WEXITED n -> CErrors.user_err Pp.(str"Compiler exited with code " ++ int n ++ str" while running " ++ str linkcmd)
      | Unix.WSIGNALED n | Unix.WSTOPPED n -> CErrors.user_err Pp.(str"Compiler was signaled with code " ++ int n))
    | Unix.WEXITED n -> CErrors.user_err Pp.(str"Compiler exited with code " ++ int n ++ str" while running " ++ str cmd)
    | Unix.WSIGNALED n | Unix.WSTOPPED n -> CErrors.user_err Pp.(str"Compiler was signaled with code " ++ int n  ++ str" while running " ++ str cmd)
    
  type reifyable_type =
  | IsInductive of Names.inductive * UVars.Instance.t * Constr.t list
  | IsPrimitive of Names.Constant.t * UVars.Instance.t * Constr.t list
  
  let type_of_reifyable_type = function
    | IsInductive (hd, u, args) -> Term.applistc (Constr.mkIndU ((hd, u))) args
    | IsPrimitive (c, u, args) -> Term.applistc (Constr.mkConstU ((c, u))) args
  
  let pr_reifyable_type env sigma ty =
    Printer.pr_constr_env env sigma (type_of_reifyable_type ty)

  let find_nth_constant n ar =
    let open Inductiveops in
    let rec aux i const = 
      if Array.length ar <= i then raise Not_found
      else if CList.is_empty ar.(i).cs_args then  (* FIXME lets in constructors *)
        if const = n then i 
        else aux (i + 1) (const + 1)
      else aux (i + 1) const
    in aux 0 0
  
  let find_nth_non_constant n ar =
    let open Inductiveops in
    let rec aux i nconst = 
      if Array.length ar <= i then raise Not_found
      else if not (CList.is_empty ar.(i).cs_args) then 
        if nconst = n then i 
        else aux (i + 1) (nconst + 1)
      else aux (i + 1) nconst
    in aux 0 0

  let check_reifyable env sigma ty =
    (* We might have bound universes though. It's fine! *)
    try let (hd, u), args = Inductiveops.find_inductive env sigma ty in
      IsInductive (hd, EConstr.EInstance.kind sigma u, List.map (EConstr.to_constr sigma) args)
    with Not_found -> 
      let hnf = Reductionops.whd_all env sigma ty in
      let hd, args = EConstr.decompose_app sigma hnf in
      match EConstr.kind sigma hd with
      | Const (c, u) when Environ.is_primitive_type env c -> 
        IsPrimitive (c, EConstr.EInstance.kind sigma u, CArray.map_to_list EConstr.Unsafe.to_constr args)
      | _ -> CErrors.user_err 
        Pp.(str"Cannot reify values of non-inductive or non-primitive type: " ++ 
          Printer.pr_econstr_env env sigma ty)

  let ill_formed env sigma ty =
    match ty with
    | IsInductive _ -> 
      CErrors.anomaly ~label:"certirocq-reify-ill-formed"
      Pp.(str "Ill-formed inductive value representation in CertiRocq's reification for type " ++
        pr_reifyable_type env sigma ty)
    | IsPrimitive _ ->
      CErrors.anomaly ~label:"certirocq-reify-ill-formed"
      Pp.(str "Ill-formed primitive value representation in CertiRocq's reification for type " ++
        pr_reifyable_type env sigma ty)

  (* let ocaml_get_boxed_ordinal v = 
    (* tag is the header of the object *)
    let tag = Array.unsafe_get (Obj.magic v : Obj.t array) (-1) in
    (* We turn it into an ocaml int usable for arithmetic operations *)
    let tag_int = (Stdlib.Int.shift_left (Obj.magic (Obj.repr tag)) 1) + 1 in
    Feedback.msg_debug (Pp.str (Printf.sprintf "Ocaml tag: %i" (Obj.tag tag)));
    Feedback.msg_debug (Pp.str (Printf.sprintf "Ocaml get_boxed_ordinal int: %u" tag_int));
    Feedback.msg_debug (Pp.str (Printf.sprintf "Ocaml get_boxed_ordinal ordinal: %u" (tag_int land 255)));
    tag_int land 255 *)


  let time ~(msg:Pp.t) f =
    let start = Unix.gettimeofday() in
    let res = f () in
    let time = Unix.gettimeofday () -. start in
    Feedback.msg_notice Pp.(msg ++ str (Printf.sprintf " executed in %f sec" time));
    res

  let apply_reordering hd m cstrs =
    try
      let find_ind_ord (ind, (na, tags)) =
        if Kernames.eq_inductive_def ind hd then
          Some (Array.of_list (List.map (fun i -> cstrs.(i)) tags))
        else None
      in
      CList.find_map_exn find_ind_ord m
    with Not_found -> cstrs

  let find_reverse_mapping hd m cstr =
    try
      let find_ind_ord (ind, (na, tags)) =
        if Kernames.eq_inductive_def ind hd then
          Some (CList.index0 Int.equal cstr tags)
        else None
      in
      CList.find_map_exn find_ind_ord m
    with Not_found -> cstr

  let reify im env sigma ty v : Constr.t = 
    let open Declarations in
    let debug s = debug_reify Pp.(fun () -> str s) in
    let rec aux ty v =
    Control.check_for_interrupt ();
    let () = debug_reify Pp.(fun () -> str "Reifying value of type " ++ pr_reifyable_type env sigma ty) in
    match ty with
    | IsInductive (hd, u, args) -> 
      let open Inductive in
      let open Inductiveops in
      let qhd = match Metarocq_template_plugin.Ast_quoter.quote_global_reference (IndRef hd) with Metarocq_template_plugin.Kernames.IndRef i -> (Obj.magic i : Kernames.inductive) | _ -> assert false in
      let spec = lookup_mind_specif env hd in
      let npars = inductive_params spec in
      let params, _indices = CList.chop npars args in
      let indfam = make_ind_family ((hd, EConstr.EInstance.make u), List.map (EConstr.of_constr) params) in
      let cstrs = get_constructors env indfam in
      let cstrs = apply_reordering qhd im cstrs in
      if Obj.is_block v then
        let ord = get_boxed_ordinal v in
        let () = debug (Printf.sprintf "Reifying constructor block of tag %i" ord) in
        let coqidx = 
          try find_nth_non_constant ord cstrs 
          with Not_found -> ill_formed env sigma ty
        in
        let cstr = cstrs.(coqidx) in
        let coqidx = find_reverse_mapping qhd im coqidx in
        let ctx = Vars.smash_rel_context (EConstr.to_rel_context sigma cstr.cs_args) in
        let vargs = List.init (List.length ctx) (Obj.field v) in
        let args' = List.map2 (fun decl v -> 
          let argty = check_reifyable env sigma 
          (EConstr.of_constr (Context.Rel.Declaration.get_type decl)) in
          aux argty v) (List.rev ctx) vargs in
        Term.applistc (Constr.mkConstructU ((hd, coqidx + 1), u)) (params @ args')
      else (* Constant constructor *)
        let ord = (Obj.magic v : int) in
        let () = debug (Printf.sprintf "Reifying constant constructor: %i" ord) in
        let coqidx = 
          try find_nth_constant ord cstrs 
          with Not_found -> ill_formed env sigma ty 
        in
        let coqidx = find_reverse_mapping qhd im coqidx in
        let () = debug (Printf.sprintf "Reifying constant constructor: %i is %i in Coq" ord coqidx) in
        Term.applistc (Constr.mkConstructU ((hd, coqidx + 1), u)) params
    | IsPrimitive (c, u, _args) -> 
      if Environ.is_array_type env c then 
        CErrors.user_err Pp.(str "Primitive arrays are not supported yet in CertiRocq reification")
      else if Environ.is_float64_type env c then
        Constr.mkFloat (Obj.magic v)
      else if Environ.is_int63_type env c then
        Constr.mkInt (Obj.magic v)
      else CErrors.user_err Pp.(str "Unsupported primitive type in CertiRocq reification")
    in aux ty v

  let reify opts env sigma tyinfo result =
    if opts.time then time ~msg:(Pp.str "Reification") (fun () -> reify opts.inductives_mapping env sigma tyinfo result)
    else reify opts.inductives_mapping env sigma tyinfo result 

  let template name = 
    Printf.sprintf "\nvalue %s ()\n { struct thread_info* tinfo = make_tinfo(); return %s_body(tinfo); }\n" name name
  let template_header name = 
    Printf.sprintf "#include <gc_stack.h>\nextern value %s ();\n" name

  let write_c_driver opts name = 
    let fname = make_fname opts (opts.filename ^ ".c") in
    let fhname = make_fname opts (opts.filename ^ ".h") in
    let fd = Unix.(openfile fname [O_CREAT; O_APPEND; O_WRONLY] 0o640) in
    let chan = Unix.out_channel_of_descr fd in
    output_string chan (template name);
    flush chan;
    close_out chan;
    let chan = open_out fhname in
    output_string chan (template_header name);
    flush chan; close_out chan;
    fname
  
  let template_ocaml id filename name = 
    Printf.sprintf "external %s : unit -> Obj.t = \"%s\"\nlet _ = Certirocq_vanilla_plugin.Certirocq.register_certirocq_run \"%s\" \"%s\" (Obj.magic %s)" name name id filename name
  
  let write_ocaml_driver id opts name = 
    let fname = make_fname opts (opts.filename ^ "_wrapper.ml") in
    let chan = open_out fname in
    output_string chan (template_ocaml id opts.filename name);
    flush chan; close_out chan; fname

  let certirocq_eval_named ~opaque_access opts env sigma c global_id imports =
    let prog = quote_term ~opaque_access opts env sigma c in
    let tyinfo = 
      let ty = Retyping.get_type_of env sigma c in
      (* assert (Evd.is_empty sigma); *)
      check_reifyable env sigma ty
    in
    let id = opts.toplevel_name in
    let () = compile { opts with toplevel_name = id ^ "_body" } (Obj.magic prog) imports in
    (* Write wrapping code *)
    let c_driver = write_c_driver opts id in
    let ocaml_driver = write_ocaml_driver global_id opts id in      
    let imports = get_global_includes () @ imports in
    let debug = opts.debug in
    let suff = opts.ext in
    let compiler = compiler_executable debug in
    let ocamlfind = ocamlfind_executable debug in
    let rt_dir = runtime_dir () in
    let cmd =
        Printf.sprintf "%s -Wno-everything -O2 -fomit-frame-pointer -g -I %s -I %s -c -o %s %s" 
          compiler opts.build_dir (Boot.Env.Path.to_string rt_dir) (Filename.remove_extension c_driver ^ ".o") c_driver
    in
    let importso =
      let oname s = 
        assert (CString.is_suffix ".h" s);
        String.sub s 0 (String.length s - 2) ^ ".o"
      in 
      let imports' = List.concat (List.map (fun i -> 
        match i with 
        | FromAbsolutePath s -> [oname s]
        | FromRelativePath s -> [oname s]
        | FromLibrary (_, Some s) -> [make_rt_file (oname s)]
        | FromLibrary (s, None) -> [make_rt_file (oname s)]) imports) in
      let l = imports' in
      String.concat " " l
    in
    let gc_stack_o = make_rt_file "gc_stack.o" in
    debug_msg debug (Printf.sprintf "Executing command: %s" cmd);
    let packages = ["rocq-runtime"; "rocq-runtime.plugins.ltac"; "rocq-metarocq-template-ocaml";
      "rocq-runtime.interp"; "rocq-runtime.kernel"; "rocq-runtime.library"] in
    let pkgs = String.concat "," packages in
    let dontlink = "str,unix,dynlink,threads,zarith,rocq-runtime,rocq-runtime.plugins.ltac,rocq-runtime.interp" in
    let () = ignore (execute cmd) in
    let shared_lib = make_fname opts opts.filename ^ suff ^ ".cmxs" in
    let linkcmd =
      Printf.sprintf "%s ocamlopt -shared -linkpkg -dontlink %s -thread -rectypes -package %s \
      -I %s -package rocq-certirocq-vanilla -o %s %s %s %s %s"
      ocamlfind dontlink pkgs opts.build_dir shared_lib ocaml_driver gc_stack_o 
      (make_fname opts opts.filename ^ ".o") importso
    in
    debug_msg debug (Printf.sprintf "Executing command: %s" linkcmd);
    let _out, _err = execute linkcmd in
    Dynlink.loadfile_private shared_lib;
    debug_msg debug (Printf.sprintf "Dynamic linking succeeded, retrieving function %s" global_id);
    let result = 
      if opts.time then time ~msg:(Pp.str id) (run_certirocq_run global_id)
      else run_certirocq_run global_id ()
    in
    debug_msg debug (Printf.sprintf "Running the dynamic linked program succeeded, reifying result");
    reify opts env sigma tyinfo result
    
  let next_string_away_from s bad =
    let rec name_rec s = if bad s then name_rec (increment_subscript s) else s in
    name_rec s
  
  let find_fresh s map = 
    Feedback.msg_debug Pp.(str "Looking for fresh " ++ str s ++ str " in " ++ prlist_with_sep spc str (CString.Set.elements map));
    let freshs = next_string_away_from s (fun s -> CString.Set.mem s map) in
    Feedback.msg_debug Pp.(str "Found " ++ str freshs);
    freshs
    
  let toplevel_name_of_filename s = 
    let comps = CString.split_on_char '.' s in
    CString.uncapitalize_ascii (CString.concat "_" comps)

  let certirocq_eval ~opaque_access opts env sigma c imports =
    let global_id = opts.filename in
    let fresh_name = find_fresh global_id !all_run_functions in
    let opts = { opts with toplevel_name = toplevel_name_of_filename fresh_name; filename = fresh_name } in
    certirocq_eval_named ~opaque_access opts env sigma c global_id imports

  let run_existing opts env sigma c id run =
    let tyinfo = 
      let ty = Retyping.get_type_of env sigma c in        
      check_reifyable env sigma ty
    in
    let result = 
      if opts.time then time ~msg:Pp.(str"Running " ++ id) run
      else run ()
    in
    debug_msg opts.debug (Printf.sprintf "Running the dynamic linked program succeeded, reifying result");
    reify opts env sigma tyinfo result
    
  let eval ~opaque_access opts env sigma c imports =
    match exists_certirocq_run opts.filename with
    | None -> certirocq_eval ~opaque_access opts env sigma c imports
    | Some run -> 
      debug_msg opts.debug (Printf.sprintf "Retrieved earlier compiled code for %s" opts.filename);
      run_existing opts env sigma c (Pp.str opts.filename) run

  let eval_gr ~opaque_access opts gr imports =
    let env = Global.env () in
    let sigma = Evd.from_env env in
    let sigma, c = Evd.fresh_global env sigma gr in
    let filename = get_name gr in
    let name = toplevel_name_of_filename filename in
    let opts = { opts with toplevel_name = name; filename = filename } in
    eval ~opaque_access opts env sigma c imports
    
  let print_to_file (s : string) (file : string) =
    let f = open_out file in
    Printf.fprintf f "%s\n" s;
    close_out f


  let show_ir ~opaque_access opts gr =
    let term = quote ~opaque_access opts gr in
    let debug = opts.debug in
    let options = make_pipeline_options opts in
    let p = Pipeline.show_IR options (Obj.magic term) in
    match p with
    | (CompM.Ret prg, dbg) ->
      debug_msg debug "Finished compiling, printing to file.";
      let time = Unix.gettimeofday() in
      let suff = opts.ext in
      let fname = opts.filename in
      let file = fname ^ suff ^ ".ir" in
      print_to_file (string_of_bytestring prg) file;
      let time = (Unix.gettimeofday() -. time) in
      debug_msg debug (Printf.sprintf "Printed to file %s in %f s.." file time);
      debug_msg debug "Pipeline debug:";
      debug_msg debug (string_of_bytestring dbg)
    | (CompM.Err s, dbg) ->
      debug_msg debug "Pipeline debug:";
      debug_msg debug (string_of_bytestring dbg);
      CErrors.user_err Pp.(str "Could not compile: " ++ (pr_string s) ++ str "\n")


  (* Quote Coq inductive type *)
  let quote_ind ~opaque_access opts gr : Metarocq_template_plugin.Ast_quoter.quoted_program * string =
    let debug = opts.debug in
    let env = Global.env () in
    let sigma = Evd.from_env env in
    let sigma, c = Evd.fresh_global env sigma gr in
    let name = match gr with
      | Names.GlobRef.IndRef i -> 
          let (mut, _) = i in
          Names.KerName.to_string (Names.MutInd.canonical mut)
      | _ -> CErrors.user_err
        Pp.(Printer.pr_global gr ++ str " is not an inductive type") in
    debug_msg debug "Quoting";
    let time = Unix.gettimeofday() in
    let term = quote_term_rec ~bypass:true ~opaque_access env sigma (EConstr.to_constr sigma c) in
    let time = (Unix.gettimeofday() -. time) in
    debug_msg debug (Printf.sprintf "Finished quoting in %f s.." time);
    (term, name)

  let ffi_command ~opaque_access opts gr =
    let (term, name) = quote_ind ~opaque_access opts gr in
    let debug = opts.debug in
    let options = make_pipeline_options opts in

    let time = Unix.gettimeofday() in
    (match CI.generate_ffi options (Obj.magic term) with
    | CompM.Ret (((nenv, header), prg), logs) ->
      let time = (Unix.gettimeofday() -. time) in
      debug_msg debug (Printf.sprintf "Generated FFI glue code in %f s.." time);
      (match logs with [] -> () | _ ->
        debug_msg debug (Printf.sprintf "Logs:\n%s" (String.concat "\n" (List.map string_of_bytestring logs))));
      let time = Unix.gettimeofday() in
      let suff = opts.ext in
      let cstr = ("ffi." ^ name ^ suff ^ ".c") in
      let hstr = ("ffi." ^ name ^ suff ^ ".h") in
      CI.printProg prg nenv cstr [];
      CI.printProg header nenv hstr [];

      let time = (Unix.gettimeofday() -. time) in
      debug_msg debug (Printf.sprintf "Printed FFI glue code to file in %f s.." time)
    | CompM.Err s ->
      CErrors.user_err Pp.(str "Could not generate FFI glue code: " ++ pr_string s))

  let glue_command ~opaque_access opts grs =
    let terms = grs |> List.rev
                |> List.map (fun gr -> Metarocq_template_plugin.Ast0.Env.declarations (fst (quote ~opaque_access opts gr)))
                |> List.concat |> nub in
    generate_glue true opts (Obj.magic terms)

end

module MLCompile = CompileFunctor (MLCompiler)
include MLCompile
