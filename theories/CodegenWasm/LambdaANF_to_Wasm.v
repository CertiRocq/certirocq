From Wasm Require Import datatypes operations.

From Stdlib Require Import
  FMapAVL MSetAVL
  POrderedType
  ZArith BinNat List Lia.

From ExtLib Require Import Structures.Monad.

From CertiRocq Require Import
  LambdaANF.toplevel
  LambdaANF.cps_util
  Common.Pipeline_utils
  Common.Common
  LambdaANF.cps
  LambdaANF.cps_show
  CodegenWasm.LambdaANF_to_Wasm_restrictions
  CodegenWasm.LambdaANF_to_Wasm_primitives.

From MetaRocq.Utils Require Import bytestring MRString.

Import MonadNotation compM.


(* Main file for compiler backend targeting Wasm. *)

(* memory can grow to at most 64KB * max_mem_pages *)
Definition max_mem_pages := 30000%N.


(* ***** FUNCTIONS and GLOBALS ****** *)

(* In Wasm, functions and globals are referred to by their index in the order they are listed.
   Function 0 is main, then follow the translated lANF functions.  *)

(* main function: contains the translated main expression *)
Definition main_function_name := "main_function".
Definition main_function_idx : funcidx := 0%N.

(* Index of the first translated lANF function. *)
Definition num_custom_funs := 1.

(* global vars *)
Definition glob_mem_ptr    : globalidx := 0%N. (* ptr to next free memory, increased after allocation, there is no GC *)
Definition glob_cap        : globalidx := 1%N. (* i32 pointer used during constructor allocation *)
Definition glob_result     : globalidx := 2%N. (* final result *)
Definition glob_out_of_mem : globalidx := 3%N. (* ran out of memory *)

(* globals used for primitive ops *)
Definition glob_tmp1 : globalidx := 4%N.
Definition glob_tmp2 : globalidx := 5%N.
Definition glob_tmp3 : globalidx := 6%N.
Definition glob_tmp4 : globalidx := 7%N.

(* ***** MAPPINGS ****** *)
Definition localvar_env := M.tree localidx. (* maps variables to their id (id=index in list of local vars) *)
Definition fname_env    := M.tree funcidx.  (* maps function variables to their id (id=index in list of functions) *)


(* ***** UTILS and BASIC TRANSLATIONS ****** *)

(* target type for generating functions,
   in addition to WasmCert's *module_func*, it contains:
   fidx and export_name *)
Record wasm_function :=
  { fidx : funcidx
  ; export_name : string
  ; type : N
  ; locals : list value_type
  ; body : list basic_instruction
  }.

(* generates list of n arguments *)
Fixpoint arg_list (n : nat) : list (localidx * value_type) :=
  match n with
  | 0 => []
  | S n' => arg_list n' ++ [(N.of_nat n', T_num T_i32)]
  end.

Definition nat_to_i32 (n : nat) :=
  Wasm_int.Int32.repr (BinInt.Z.of_nat n).

Definition nat_to_i64 (n : nat) :=
  Wasm_int.Int64.repr (BinInt.Z.of_nat n).

Definition N_to_i32 (n : N) :=
  Wasm_int.Int32.repr (Z.of_N n).

Definition nat_to_value (n : nat) :=
  VAL_int32 (nat_to_i32 n).

Definition nat_to_value64 (n : nat) :=
  VAL_int64 (nat_to_i64 n).

Definition Z_to_value (z : Z) :=
  VAL_int32 (Wasm_int.Int32.repr z).

Definition N_to_value (n : N) :=
  Z_to_value (Z.of_N n).

Definition translate_var (nenv : name_env) (lenv : localvar_env) (v : cps.var) (err : string)
  : error u32 :=
  match M.get v lenv with
  | Some n => Ret n
  | None => Err ("expected to find id for variable " ++ (show_tree (show_var nenv v)) ++ " in var/fvar mapping: " ++ err)
  end.

Definition is_function_var (fenv : fname_env) (v : cps.var) : bool :=
  match M.get v fenv with
  | Some _ => true
  | None => false
  end.

Definition instr_local_var_read (nenv : name_env) (lenv : localvar_env) (fenv : fname_env) (v : cps.var)
  : error basic_instruction :=
  if is_function_var fenv v then
    fidx <- translate_var nenv fenv v "translate local var read: obtaining function idx" ;;
    Ret (BI_const_num (N_to_value fidx)) (* passing function idx *)
  else
    var <- translate_var nenv lenv v "instr_local_var_read: normal var";;
    Ret (BI_local_get var).

Definition get_ctor_arity (cenv : ctor_env) (t : ctor_tag) :=
  match M.get t cenv with
  | Some {| ctor_arity := n |} => Ret (N.to_nat n)
  | _ => Err "found constructor without ctor_arity set"
  end.

Definition get_ctor_size (cenv : ctor_env) (t : ctor_tag) : error N :=
  arity <- get_ctor_arity cenv t;;
  Ret (if arity =? 0 then 0%N else N.of_nat (4 * (arity + 1) + 24)). (* size in bytes plus 24 for some luft for invariants *)

(* ***** FUNCTION CALLS ****** *)

(* every function has type: T_i32^{#args} -> [] *)

Fixpoint pass_function_args (nenv : name_env) (lenv: localvar_env) (fenv : fname_env) (args : list cps.var) : error (list basic_instruction) :=
  match args with
  | [] => Ret []
  | a0 :: args' =>
      a0' <- instr_local_var_read nenv lenv fenv a0;;
      args'' <- pass_function_args nenv lenv fenv args';;
      Ret (a0' :: args'')
  end.

Definition translate_call (nenv : name_env) (lenv : localvar_env) (fenv : fname_env) (f : cps.var) (args : list cps.var) (tailcall : bool)
  : error (list basic_instruction) :=
  instr_pass_params <- pass_function_args nenv lenv fenv args;;
  instr_fidx <- instr_local_var_read nenv lenv fenv f;;
  let call := (fun num_args : nat => if tailcall then BI_return_call_indirect 0%N (N.of_nat num_args)
                                                 else BI_call_indirect 0%N (N.of_nat num_args)) in
  Ret (instr_pass_params ++ [instr_fidx] ++ [call (length args)]).
  (* all fns return nothing, type = num args *)


(* ***** CONSTRUCTOR REPRESENTATION (as CertiRocq's C backend/OCaml) ****** *)

(* Example placement of constructors in the linear memory (each cell is 4 bytes):
   data BTree := Leaf | Node BTree Nat BTree

   Leaf: nullary constructor (ordinal 0), thus the i32 value 2*0+1 = 1

   Node: non-nullary constructor (ordinal 0), thus the i32 pointer to
          --> +---+---+---+---+
              | 0 | L | V | R |
              +---+---+---+---+
   L, V, R constructors
*)

(* store argument pointers in memory *)
Fixpoint store_constructor_args (nenv : name_env) (lenv : localvar_env) (fenv : fname_env) (args : list cps.var) (current : nat) : error (list basic_instruction) :=
  match args with
  | [] => Ret []
  | y :: ys =>
      read_y <- instr_local_var_read nenv lenv fenv y;;
      remaining <- store_constructor_args nenv lenv fenv ys (1 + current);;

      Ret ([ BI_global_get glob_cap
           ; BI_const_num (nat_to_value (4 * (1 + current))) (* plus 1 : skip tag *)
           ; BI_binop T_i32 (Binop_i BOI_add)
           ; read_y
           ; BI_store T_i32 None {| memarg_offset:=0%N; memarg_align:=2%N |}

           (* increase gmp by 4 *)
           ; BI_global_get glob_mem_ptr
           ; BI_const_num (nat_to_value 4)
           ; BI_binop T_i32 (Binop_i BOI_add)
           ; BI_global_set glob_mem_ptr

           ] ++ remaining)
  end.


Definition store_constructor (nenv : name_env) (cenv : ctor_env) (lenv : localvar_env) (fenv : fname_env) (c : ctor_tag) (ys : list cps.var) : error (list basic_instruction) :=
  ord <- get_ctor_ord cenv c ;;
  store_constr_args <- store_constructor_args nenv lenv fenv ys 0;;
  Ret ([ BI_global_get glob_mem_ptr
       ; BI_global_set glob_cap

       (* store tag *)
       ; BI_global_get glob_cap
       ; BI_const_num (nat_to_value (N.to_nat ord))
       ; BI_store T_i32 None {| memarg_offset:=0%N; memarg_align:=2%N |}
       (* increase gmp by 4 *)
       ; BI_global_get glob_mem_ptr
       ; BI_const_num (nat_to_value 4)
       ; BI_binop T_i32 (Binop_i BOI_add)
       ; BI_global_set glob_mem_ptr

       ] ++ store_constr_args).

Fixpoint create_case_nested_if_chain (boxed : bool) (v : localidx) (es : list (N * list basic_instruction)) : list basic_instruction :=
  match es with
  | [] => [ BI_unreachable ]
  | (ord, instrs) :: tl =>
      (* if boxed (pointer), then load tag from memory;
         otherwise, the unboxed representation is (ord << 1) + 1 = 2 * ord + 1.
       *)
      BI_local_get v ::
      (if boxed then
         [ BI_load T_i32 None {| memarg_offset:=0%N; memarg_align:=2%N |}
         ; BI_const_num (nat_to_value (N.to_nat ord)) ]
       else
         [ BI_const_num (nat_to_value (N.to_nat (2 * ord + 1)%N)) ]) ++
      [ BI_relop T_i32 (Relop_i ROI_eq)
      ; BI_if (BT_valtype None)
          instrs
          (create_case_nested_if_chain boxed v tl)
      ]
  end.


(* **** TRANSLATE PRIMITIVE VALUES **** *)

Definition translate_primitive_value (p : AstCommon.primitive) : error Wasm_int.Int64.int :=
  match projT1 p as tag return prim_value tag -> error Wasm_int.Int64.T with
  | AstCommon.primInt => fun i => Ret (Wasm_int.Int64.repr (Uint63.to_Z i))
  | AstCommon.primFloat => fun f => Err "Extraction of floats to Wasm not yet supported"
  | AstCommon.primString => fun f => Err "Extraction of strings to Wasm not yet supported"
  end (projT2 p).


(* **** TRANSLATE PRIMITIVE OPERATIONS **** *)

(* actual translation in _primitives file *)
Definition translate_primitive_operation (nenv : name_env) (lenv : localvar_env) (p : (kername * string * bool * nat)) (args : list var) : error (list basic_instruction) :=
  let '(op_name, _, _, _) := p in
  match KernameMap.find op_name primop_map with
  | Some op =>
      match args with
      | [ x ] =>
          x_var <- translate_var nenv lenv x "translate primitive unop operand";;
          translate_primitive_unary_op glob_mem_ptr op x_var

      | [ x ; y ] =>
          x_var <- translate_var nenv lenv x "translate primitive binary operator 1st operand";;
          y_var <- translate_var nenv lenv y "translate primitive binary operator 2nd operand";;
          translate_primitive_binary_op glob_mem_ptr glob_tmp1 glob_tmp2 glob_tmp3 glob_tmp4 op x_var y_var

      | [ x ; y ; z ] =>
          x_var <- translate_var nenv lenv x "translate primitive ternary operator 1st operand" ;;
          y_var <- translate_var nenv lenv y "translate primitive ternary operator 2nd operand" ;;
          z_var <- translate_var nenv lenv z "translate primitive ternary operator 3rd operand" ;;
          translate_primitive_ternary_op glob_mem_ptr glob_tmp1 glob_tmp2 glob_tmp3 glob_tmp4 glob_cap op x_var y_var z_var

      | _ => Err "Only primitive operations with 1, 2 or 3 arguments are supported"
      end
  | _ => Err ("Unsupported primitive operator: " ++ (Kernames.string_of_kername op_name))
  end.

(* **** GROWING THE LINEAR MEMORY **** *)

(* a page is 2^16 bytes, expected num of required bytes in local 0 *)
Definition grow_memory_if_necessary : list basic_instruction :=
  (* required number of total pages *)
  [ BI_global_get glob_mem_ptr
  ; BI_const_num (N_to_value page_size)
  ; BI_binop T_i32 (Binop_i BOI_add)
  ; BI_const_num (Z_to_value (Z.pow 2 16))
  ; BI_binop T_i32 (Binop_i (BOI_div SX_S))

  (* current number of pages *)
  ; BI_memory_size
  ; BI_relop T_i32 (Relop_i (ROI_ge SX_S))
  (* allocate one page if necessary *)
  ; BI_if (BT_valtype None)
      [ BI_const_num (nat_to_value 1)
      ; BI_memory_grow (* returns -1 on alloc failure *)
      ; BI_const_num (Z_to_value (-1))
      ; BI_relop T_i32 (Relop_i ROI_eq)
      ; BI_if (BT_valtype None)
         [ BI_const_num (nat_to_value 1); BI_global_set glob_out_of_mem; BI_return ] (* out of memory, abort *)
         []
      ]
      []
  ].

(* mem is lower bound of linmem known to be available statically (in bytes)
   allocated bytes are counted to omit unnecessary checks of the memory size. *)
Definition call_grow_mem_if_necessary (mem : N) (required_bytes : N) : list basic_instruction * N :=
  if (required_bytes <=? mem)%N
  then ([], mem - required_bytes)%N
  else (grow_memory_if_necessary, 65536 - required_bytes)%N.


(* ***** EXPRESSIONS (except fundefs) ****** *)

Fixpoint translate_body (nenv : name_env) (cenv : ctor_env) (lenv: localvar_env) (fenv : fname_env) (penv : prim_env) (e : exp) (mem : N) : error (list basic_instruction) :=
   match e with
   | Efun fundefs e' => Err "unexpected nested function definition"
   | Econstr x tg ys e' =>
      x_var <- translate_var nenv lenv x "translate_body constr";;
      match ys with
      | [] =>
          (* unboxed *)
          ord <- get_ctor_ord cenv tg ;;
          following_instr <- translate_body nenv cenv lenv fenv penv e' mem ;;
          Ret ([ BI_const_num (nat_to_value (N.to_nat (2 * ord + 1)%N)) ; BI_local_set x_var ] ++ following_instr)
      | _ =>
          (* n > 0 ary constructor, boxed representation *)
          store_constr <- store_constructor nenv cenv lenv fenv tg ys;;
          constr_size <- get_ctor_size cenv tg;;
          let p := call_grow_mem_if_necessary mem constr_size in
          let grow_mem_instr := fst p in
          let mem' := snd p in
          following_instr <- translate_body nenv cenv lenv fenv penv e' mem' ;;
          Ret (grow_mem_instr ++
               store_constr ++
               [ BI_global_get glob_cap
               ; BI_local_set x_var
               ] ++ following_instr)
      end
   | Ecase x arms =>
      (* split arms into boxed and unboxed constructors *)
      let fix translate_case_branch_expressions (arms : list (ctor_tag * exp))
        : error (list (N * list basic_instruction) * list (N  * list basic_instruction)) :=
        match arms with
        | [] => Ret ([], [])
        | (t, e)::tl =>
            instrs <- translate_body nenv cenv lenv fenv penv e mem;;
            '(arms_boxed, arms_unboxed) <- translate_case_branch_expressions tl ;;
            ord <- get_ctor_ord cenv t ;;
            arity <- get_ctor_arity cenv t ;;
            if arity =? 0 then
              Ret (arms_boxed, (ord, instrs) :: arms_unboxed)
            else
              Ret ((ord, instrs) :: arms_boxed, arms_unboxed)
        end
      in
      x_var <- translate_var nenv lenv x "translate_body case" ;;
      '(arms_boxed, arms_unboxed) <- translate_case_branch_expressions arms ;;
      Ret ([ BI_local_get x_var
           ; BI_const_num (nat_to_value 1)
           ; BI_binop T_i32 (Binop_i BOI_and)
           ; BI_testop T_i32 TO_eqz
           ; BI_if (BT_valtype None)
               (create_case_nested_if_chain true x_var arms_boxed)
               (create_case_nested_if_chain false x_var arms_unboxed)
           ])

   | Eproj x tg n y e' =>
      following_instr <- translate_body nenv cenv lenv fenv penv e' mem;;
      y_var <- translate_var nenv lenv y "translate_body proj y";;
      x_var <- translate_var nenv lenv x "translate_body proj x";;

      Ret ([ BI_local_get y_var
           ; BI_const_num (nat_to_value (((N.to_nat n) + 1) * 4)) (* skip ctor_id and previous constr arguments *)
           ; BI_binop T_i32 (Binop_i BOI_add)
           ; BI_load T_i32 None {| memarg_offset:=0%N; memarg_align:=2%N |}
           ; BI_local_set x_var
           ] ++ following_instr)

   | Eletapp x f ft ys e' =>
      x_var <- translate_var nenv lenv x "translate_body proj x";;
      following_instr <- translate_body nenv cenv lenv fenv penv e' 0%N;; (* after function call, no static guarantees for available memory *)
      instr_call <- translate_call nenv lenv fenv f ys false;;
      Ret (instr_call ++ [ BI_global_get glob_out_of_mem
                         ; BI_if (BT_valtype None)
                             [ BI_return ]
                             []
                         ; BI_global_get glob_result
                         ; BI_local_set x_var
                         ] ++ following_instr)

   | Eapp f ft ys => translate_call nenv lenv fenv f ys true

   | Eprim_val x p e' =>
       x_var <- translate_var nenv lenv x "translate_body prim val" ;;
       val <- translate_primitive_value p ;;
       let instrs :=
            [ BI_global_get glob_mem_ptr
            ; BI_const_num (VAL_int64 val)
            ; BI_store T_i64 None {| memarg_offset:=0%N; memarg_align:=2%N |}
            ; BI_global_get glob_mem_ptr
            ; BI_local_set x_var
            ; BI_global_get glob_mem_ptr
            ; BI_const_num (nat_to_value 8)
            ; BI_binop T_i32 (Binop_i BOI_add)
            ; BI_global_set glob_mem_ptr
            ]
       in
       let p := call_grow_mem_if_necessary mem 32%N in  (* 8 bytes plus 24 for some luft for invariants *)
       let grow_instr := fst p in
       let mem' := snd p in
       following_instr <- translate_body nenv cenv lenv fenv penv e' mem' ;;
       Ret (grow_instr ++ instrs ++ following_instr)
   | Eprim x p ys e' =>
       match M.get p penv with
       | None => Err "Primitive operation not found in prim_env"
       | Some p' =>
           x_var <- translate_var nenv lenv x "translate_exp prim op" ;;
           prim_op_instrs <- translate_primitive_operation nenv lenv p' ys ;;
           let p := call_grow_mem_if_necessary mem 52%N in (* 28 bytes plus 24 for some luft for invariants *)
           let grow_instr := fst p in
           let mem' := snd p in
           following_instr <- translate_body nenv cenv lenv fenv penv e' mem' ;;
           Ret (grow_instr ++ prim_op_instrs ++ [ BI_local_set x_var ]  ++ following_instr)
       end
   | Ehalt x =>
     x_var <- translate_var nenv lenv x "translate_body halt";;
     Ret [ BI_local_get x_var; BI_global_set glob_result; BI_return ]
   end.


(* ***** FUNCTIONS ****** *)

(* unique, vars are only assigned once *)
Fixpoint collect_local_variables (e : exp) : list cps.var :=
  match e with
  | Efun _ e' => collect_local_variables e'
  | Econstr x _ _ e' => x :: collect_local_variables e'
  | Ecase _ arms => flat_map (fun a => collect_local_variables (snd a)) arms
  | Eproj x _ _ _ e' => x :: collect_local_variables e'
  | Eletapp x _ _ _ e' => x :: collect_local_variables e'
  | Eprim x _ _ e' => x :: collect_local_variables e'
  | Eprim_val x _ e' => x :: collect_local_variables e'
  | Eapp _ _ _ => []
  | Ehalt _ => []
  end.

(* create mapping from vars to nats counting up from start_id, used for both fns and vars *)
Fixpoint create_var_mapping (start_id : u32) (vars : list cps.var) (env : M.tree u32) : M.tree u32 :=
   match vars with
   | [] => env
   | v :: l' => let mapping := create_var_mapping (N.succ start_id) l' env in
                M.set v start_id mapping
   end.

Definition create_local_variable_mapping (vars : list cps.var) : localvar_env :=
  create_var_mapping 0%N vars (M.empty _).

Definition translate_function (nenv : name_env) (cenv : ctor_env) (fenv : fname_env) (penv : prim_env)
                              (f : cps.var) (args : list cps.var) (body : exp) : error wasm_function :=
  let locals := collect_local_variables body in
  let lenv := create_local_variable_mapping (args ++ locals) in

  fn_idx <- translate_var nenv fenv f "translate function" ;;
  body_res <- translate_body nenv cenv lenv fenv penv body 0%N ;;
  Ret {| fidx := fn_idx
       ; export_name := show_tree (show_var nenv f)
       ; type := N.of_nat (length args)
       ; locals := map (fun _ => T_num T_i32) locals
       ; body := body_res
       |}.

Fixpoint translate_functions (nenv : name_env) (cenv : ctor_env) (fenv : fname_env) (penv : prim_env)
                             (fds : fundefs) : error (list wasm_function) :=
  match fds with
  | Fnil => Ret []
  | Fcons x tg xs e fds' =>
      fn <- translate_function nenv cenv fenv penv x xs e ;;
      following <- translate_functions nenv cenv fenv penv fds' ;;
      Ret (fn :: following)
  end.

Definition sanitize_function_name (s : string) (prefix_id : nat) : string :=
  let prefix_bytes := String.print (string_of_nat prefix_id) ++ ["_"%byte; "_"%byte] in
  let s_bytes := String.print s in
  let s_bytes' := map (fun b => match b with | "."%byte => "_"%byte |_ => b end) s_bytes in
  let bytes'' := "_"%byte :: prefix_bytes ++ s_bytes' in
  String.parse bytes''.

(* prefix function names with unique number *)
Definition unique_export_names (fns : list wasm_function) :=
  mapi (fun i fn =>
          {| fidx := fn.(fidx)
           ; export_name := sanitize_function_name fn.(export_name) i
           ; type := fn.(type)
           ; locals := fn.(locals)
           ; body := fn.(body)
           |}) fns.

(* ***** MAIN: GENERATE COMPLETE WASM_MODULE FROM lambdaANF EXP ****** *)

Definition collect_function_vars (e : cps.exp) : list cps.var :=
    match e with
    | Efun fds exp => (* fundefs only allowed here (uppermost level) *)
      (fix iter (fds : fundefs) : list cps.var :=
          match fds with
          | Fnil => []
          | Fcons x _ _ e' fds' => x :: (iter fds')
          end) fds
    | _ => []
    end.

(* maps function names to ids (id=index in function list of module) *)
Definition create_fname_mapping (e : exp) : fname_env :=
  let fun_vars := collect_function_vars e in
  create_var_mapping (N.of_nat num_custom_funs) fun_vars (M.empty _).

Fixpoint list_function_types (n : nat) : list function_type :=
  match n with
  | 0 => [Tf [] []]
  | S n' => (Tf [] []) :: map (fun t => match t with Tf args rt => Tf (T_num T_i32 :: args) rt end) (list_function_types n')
  end.

(* for indirect calls maps fun ids to themselves *)
Fixpoint table_element_mapping (len : nat) (startidx : nat) : list module_element :=
  match len with
  | 0 => []
  | S len' => {| modelem_mode := ME_active 0%N [BI_const_num (nat_to_value startidx)]
               ; modelem_init := [[ BI_ref_func (N.of_nat startidx) ]]
               ; modelem_type := T_funcref
               |} :: (table_element_mapping len' (S startidx))
  end.

Definition LambdaANF_to_Wasm (nenv : name_env) (cenv : ctor_env) (penv : prim_env) (e : exp) : error (module * fname_env * localvar_env) :=
  _ <- check_restrictions cenv e;;

  let fname_mapping := create_fname_mapping e in

  fns <- match e with
         | Efun fds exp => translate_functions nenv cenv fname_mapping penv fds
         | _ => Err "unreachable" (* can't happen, see toplevel.v *)
         end ;;

  main_expr <- match e with
               | Efun _ exp => Ret exp
               | _ => Err "unreachable"
               end;;

  let main_vars := collect_local_variables main_expr in
  let main_lenv := create_local_variable_mapping main_vars in
  main_instr <- translate_body nenv cenv main_lenv fname_mapping penv main_expr 0%N;;

  let main_function := {| fidx := main_function_idx
                        ; export_name := main_function_name
                        ; type := 0%N (* [] -> [] *)
                        ; locals := map (fun _ => T_num T_i32) main_vars
                        ; body := main_instr
                        |}
  in
  let functions := [main_function] ++ unique_export_names fns in

  let exports := map (fun f => {| modexp_name := String.print f.(export_name)
                                ; modexp_desc := MED_func (f.(fidx))
                                |}) functions (* function exports for debug names *)
                 ++ {| modexp_name := String.print "out_of_mem"
                     ; modexp_desc := MED_global glob_out_of_mem
                     |} ::
                    {| modexp_name := String.print "mem_ptr"
                     ; modexp_desc := MED_global glob_mem_ptr
                     |} ::
                    {| modexp_name := String.print "result"
                     ; modexp_desc := MED_global glob_result
                    |} ::
                    {| modexp_name := String.print "memory"
                     ; modexp_desc := MED_mem 0%N
                    |} :: nil
  in

  let elements := table_element_mapping (length fns + num_custom_funs) 0 in

  let functions_final := map (fun f => {| modfunc_type := f.(type)
                                        ; modfunc_locals := f.(locals)
                                        ; modfunc_body := f.(body)
                                       |}) functions in

  let ftys := (list_function_types (Z.to_nat max_function_args)) in
  let module :=
      {| mod_types := ftys (* more than required, doesn't hurt*)

       ; mod_funcs := functions_final
       ; mod_tables := [ {| modtab_type := {| tt_limits := {| lim_min := N.of_nat (List.length fns + num_custom_funs)
                                                            ; lim_max := None |}
                                            ; tt_elem_type := T_funcref
                                            |} |}]

       ; mod_mems := {| modmem_type :=
                         {| lim_min := 1%N  (* initial memory size in pages (1 page = 2^16 = 64 KiB), is grown as needed *)
                          ; lim_max := Some max_mem_pages (* to ensure, i32 ptr doesn't overflow, but memory grow fails instead *)
                          |}
                      |} :: nil

       ; mod_globals := {| modglob_type := {| tg_mut := MUT_var; tg_t := T_num T_i32 |}  (* glob_mem_ptr *)
                         ; modglob_init := [BI_const_num (nat_to_value 0)]
                         |} ::
                        {| modglob_type := {| tg_mut := MUT_var; tg_t := T_num T_i32 |}  (* glob_cap *)
                         ; modglob_init := [BI_const_num (nat_to_value 0)]
                         |} ::
                        {| modglob_type := {| tg_mut := MUT_var; tg_t := T_num T_i32 |}  (* glob_result *)
                         ; modglob_init := [BI_const_num (nat_to_value 0)]
                         |} ::
                        {| modglob_type := {| tg_mut := MUT_var; tg_t := T_num T_i32 |}  (* out of memory indicator *)
                         ; modglob_init := [BI_const_num (nat_to_value 0)]
                         |} ::
                        {| modglob_type := {| tg_mut := MUT_var; tg_t := T_num T_i64 |}  (* glob_tmp1 *)
                         ; modglob_init := [BI_const_num (nat_to_value64 0)]
                         |} ::
                        {| modglob_type := {| tg_mut := MUT_var; tg_t := T_num T_i64 |}  (* glob_tmp2 *)
                         ; modglob_init := [BI_const_num (nat_to_value64 0)]
                         |} ::
                        {| modglob_type := {| tg_mut := MUT_var; tg_t := T_num T_i64 |}  (* glob_tmp3 *)
                         ; modglob_init := [BI_const_num (nat_to_value64 0)]
                         |} ::
                        {| modglob_type := {| tg_mut := MUT_var; tg_t := T_num T_i64 |}  (* glob_tmp4 *)
                         ; modglob_init := [BI_const_num (nat_to_value64 0)]
                         |} :: nil

       ; mod_elems := elements
       ; mod_datas := []
       ; mod_start := None
       ; mod_imports := []
       ; mod_exports := exports
       |}
       in
       (* also return mappings to access them in proof *)
       Ret (module, fname_mapping, main_lenv).
