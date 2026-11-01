open Tm_util
open Pp
open Universes0
open BasicAst
open Ast0
open Toplevel0
open Pipeline_utils

external certirocq_pipeline : rocq_Options -> Ast0.Env.program -> rocq_Cprogram CompM.error * Bytestring.String.t = "certirocq_pipeline_wrapper"
let info s = Feedback.msg_info (Pp.str s)

let msg_info s =
  let s = Caml_bytestring.caml_string_of_bytestring s in
  Feedback.msg_info (str s)
  
let _ = Callback.register "rocq_msg_info" msg_info
let user_error s = 
  CErrors.user_err (str (Caml_bytestring.caml_string_of_bytestring s))
  
let _ = Callback.register "rocq_user_error" user_error

let msg_debug s = 
  Feedback.msg_debug (str (Caml_bytestring.caml_string_of_bytestring s))
  
let _ = Callback.register "rocq_msg_debug" msg_debug

(** The ML value representation of an erased quoted program does not directly match 
  the one expected by CertiRocq erase function as singleton inductive types are unboxed,
  we use Obj.t surgery to transform the value. 
  
  This involves the transformation of universes sets, constraints sets and the representation
  of universe values.
  *)

let fix_set u =
  (* The representation of a proof object *)
  let proof_obj = Obj.magic 1 in
  let block = Obj.new_block 0 2 in
  Obj.set_field block 0 (Obj.magic u);
  Obj.set_field block 1 proof_obj;
  block

(* A universe is a non-empty set of level expressions *)
let fix_neues neues : Obj.t =
  let proof_obj = Obj.magic 1 in
  let block = Obj.new_block 0 2 in
  Obj.set_field block 0 (fix_set neues);
  Obj.set_field block 1 proof_obj;
  block

let fix_universe u =
  let open Universes0.Sort in
  match u with
  | Rocq_sProp -> Rocq_sProp
  | Rocq_sSProp -> Rocq_sSProp
  | Rocq_sType neues -> Rocq_sType (Obj.magic (fix_neues neues))

(* Instances are lists of universes *)
let fix_instance u =
  Obj.magic (List.map fix_neues (Obj.magic u))

(* Raw AVL trees: Leaf | Node of height * tree * elt * tree *)
let rec fix_tree fix_elt (t : Obj.t) : Obj.t =
  if Obj.is_int t then t
  else begin
    let block = Obj.new_block (Obj.tag t) 4 in
    Obj.set_field block 0 (Obj.field t 0);
    Obj.set_field block 1 (fix_tree fix_elt (Obj.field t 1));
    Obj.set_field block 2 (fix_elt (Obj.field t 2));
    Obj.set_field block 3 (fix_tree fix_elt (Obj.field t 3));
    block
  end

(* Constraints relate two universes: ((l, d), r) *)
let fix_constraint (c : Obj.t) : Obj.t =
  let ld = Obj.field c 0 in
  Obj.repr ((fix_neues (Obj.field ld 0), Obj.field ld 1), fix_neues (Obj.field c 1))

let fix_constraint_set cstrs =
  fix_set (fix_tree fix_constraint (Obj.repr cstrs))

let fix_term (p : Ast0.term) : Ast0.term =
  let open List in
  let rec aux p =
  match p with
  | Rocq_tRel _ | Rocq_tVar _ -> p
  | Rocq_tConst (kn, u) -> Rocq_tConst (kn, fix_instance u)
  | Rocq_tInd (ind, u) -> Rocq_tInd (ind, fix_instance u)
  | Rocq_tConstruct (ind, k, u) -> Rocq_tConstruct (ind, k, fix_instance u)
  | Rocq_tEvar (k, l) -> Rocq_tEvar (k, map aux l)
  | Rocq_tSort u -> Rocq_tSort (fix_universe u)
  | Rocq_tCast (t, k, t') -> Rocq_tCast (aux t, k, aux t')
  | Rocq_tProd (na, t, t') -> Rocq_tProd (na, aux t, aux t')
  | Rocq_tLambda (na, t, t') -> Rocq_tLambda (na, aux t, aux t')
  | Rocq_tLetIn (na, t, b, t') -> Rocq_tLetIn (na, aux t, aux b, aux t')
  | Rocq_tApp (t, l) -> Rocq_tApp (aux t, map aux l)
  | Rocq_tCase (ci, p, c, brs) -> Rocq_tCase (ci, aux_pred p, aux c, map aux_branch brs)
  | Rocq_tProj (p, t) -> Rocq_tProj (p, aux t)
  | Rocq_tFix (mfix, i) -> Rocq_tFix (map aux_def mfix, i)
  | Rocq_tCoFix (mfix, i) -> Rocq_tCoFix (map aux_def mfix, i)
  | Rocq_tInt i -> Rocq_tInt i
  | Rocq_tFloat f -> Rocq_tFloat f
  | Rocq_tString f -> Rocq_tString f
  | Rocq_tArray (u, v, def, ty) -> Rocq_tArray (Obj.magic (fix_neues u), map aux v, aux def, aux ty)
  and aux_pred { puinst = puinst; pparams = pparams; pcontext = pcontext; preturn = preturn } =
    { puinst = fix_instance puinst; pparams = map aux pparams; pcontext; preturn = aux preturn }
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
  
let fix_universes_decl = function
  | Monomorphic_ctx -> Monomorphic_ctx
  | Polymorphic_ctx (names, cstrs) -> Polymorphic_ctx (names, Obj.magic (fix_constraint_set cstrs))

let fix_universes (levels, cstrs) =
  (Obj.magic (fix_set levels), Obj.magic (fix_constraint_set cstrs))

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

let rec print_obj depth x = 
  if depth <= 0 then Printf.printf "_"
  else
  let x = Obj.magic x in
  if Obj.is_block x then let size = Obj.size x in
                            if Obj.tag x = 247 then
                              Printf.printf "POINTER%!"
                            else
                            (Printf.printf ("(block[%i] (tag %i) %!") (Obj.size x) (Obj.tag x) ;
                            for i = 0 to size - 1 do
                              print_obj (pred depth) (Obj.field x i)
                            done;
                            Printf.printf ")")
  else Printf.printf ("%i %!") x
  
(* The inlined constants are a kername set in MetaRocq's representation *)
let fix_opts opts =
  Pipeline_utils.{ opts with erasure_config =
    { opts.erasure_config with Erasure0.inlined_constants = Obj.magic (fix_set opts.erasure_config.Erasure0.inlined_constants) } }

let compile opts prog =
  info "Calling certirocq-compiled certirocq";
  let opts = fix_opts opts in
  (* let pretty= Pretty.print_program false (Obj.magic (Caml_nat.nat_of_caml_int 100)) (Obj.magic prog) in *)
  (* let _ = info (Caml_bytestring.caml_string_of_bytestring (Obj.magic pretty)) in *)
  let prog = fix_quoted_program prog in
  info "Fixed quoted program";
  (* time (str"Compilation with bootstrapped compiler") *)
  let res = certirocq_pipeline opts prog in
  info "Certirocq pipeline ran";
  (* print_obj 10 (Obj.repr (fst res)); *)
  res
