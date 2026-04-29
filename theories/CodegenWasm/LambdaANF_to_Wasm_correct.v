(* Proof of correctness of the Wasm code generation phase of CertiRocq,
   this file is based on the proof for the Clight backend.

 > Codegen relation: relates expressions to Wasm instructions
 > Value relation:   relates LambdaANF values to Wasm values
 > Environment relation:
     for vars free in the expression: provides value stored in the local vars
     containing the result of previous execution steps,
     also provides the index for every function
     (it is also called "memory relation" in Clight)

 > Main statement: relates LambdaANF states to Wasm states according
                   to operational semantics

  TODO: consider using Ensemble like the Clight backend
 *)
Set Printing Compact Contexts.

From compcert Require Import
  Coqlib
  lib.Integers common.Memory.

From CertiRocq Require Import
  LambdaANF.term LambdaANF.eval LambdaANF.term_util LambdaANF.List_util
  LambdaANF.Ensembles_util LambdaANF.identifiers
  LambdaANF.shrink_cps_corresp
  Libraries.maps_util
  CodegenWasm.LambdaANF_to_Wasm
  CodegenWasm.LambdaANF_to_Wasm_utils
  CodegenWasm.LambdaANF_to_Wasm_restrictions
  CodegenWasm.LambdaANF_to_Wasm_primitives.

From MetaRocq Require Import Common.Kernames.

From Stdlib Require Import
  Program.Program Sets.Ensembles
  Logic.Decidable Lists.ListDec
  Relations.Relations Relations.Relation_Operators Lia
  EqdepFacts
  List Nnat Uint63.

From Wasm Require Import
  datatypes operations host opsem
  type_preservation properties common numerics.

Import ssreflect eqtype ssrbool eqtype.
Import LambdaANF.toplevel LambdaANF.term compM.
Import bytestring.
Import ExtLib.Structures.Monad MonadNotation.
Import bytestring.
Import ListNotations SigTNotations.
Import seq.
Import Wasm_int.

(* Avoid unfolding during proofs *)
Opaque Uint63.to_Z.


(* Codegen relation *)
Section CODEGEN.

Variable cenv : LambdaANF.term.ctor_env.
Variable funenv : LambdaANF.term.fun_env.
Variable fenv : CodegenWasm.LambdaANF_to_Wasm.fname_env.
Variable nenv : LambdaANF.cps_show.name_env.
Variable penv : LambdaANF.toplevel.prim_env.

(* list can be empty *)
Inductive Forall_statements_in_seq' {A} :
  (nat -> A -> list basic_instruction -> Prop) -> list A ->
                           list basic_instruction -> nat -> Prop :=
| Fsis_nil : forall (R: nat  -> A -> list basic_instruction -> Prop) n,
   Forall_statements_in_seq' R [] [] n
| Fsis_cons : forall R v vs s s' n,
   Forall_statements_in_seq' R vs s' (S n) ->  R n v s ->
   Forall_statements_in_seq' R (v::vs) (s ++ s') n.

(* This is true for R, vs and S iff forall i, R i (nth vs) (nth s)
   > nth on statement is taken as nth on a list of sequenced statement (;) *)
Definition Forall_statements_in_seq {A} :
  (nat  -> A -> list basic_instruction -> Prop) -> list A ->
                                   list basic_instruction -> Prop :=
  fun P vs s =>  Forall_statements_in_seq' P vs s 0.

(* like Forall_statements_in_seq, but starting from index 1 *)
Definition Forall_statements_in_seq_from_1 {A} :
  (nat  -> A -> list basic_instruction -> Prop) -> list A ->
                                   list basic_instruction -> Prop :=
  fun P vs s =>  Forall_statements_in_seq' P vs s 1.

Inductive repr_var {lenv} : positive -> localidx -> Prop :=
| repr_var_V : forall s err_str i,
    translate_var nenv lenv s err_str = Ret i ->
    repr_var s i.

Inductive repr_funvar : positive -> funcidx -> Prop :=
| repr_funvar_FV : forall s i errMsg,
    translate_var nenv fenv s errMsg = Ret i ->
    repr_funvar s i.

Inductive repr_read_var_or_funvar {lenv} : positive -> basic_instruction -> Prop :=
| repr_var_or_funvar_V : forall p i,
    repr_var (lenv:=lenv) p i -> repr_read_var_or_funvar p (BI_local_get i)
| repr_var_or_funvar_FV : forall p i,
    repr_funvar p i -> repr_read_var_or_funvar p (BI_const_num (N_to_value i)).

Lemma repr_var_det {lenv} : forall a a' a'',
  repr_var (lenv:=lenv) a a' ->
  repr_var (lenv:=lenv) a a'' ->
  a' = a''.
Proof.
  intros ??? Ha' Ha''. inv Ha'. inv Ha''.
  unfold translate_var in *.
  destruct (lenv ! a) eqn:Heqn=>//.
  congruence.
Qed.

Lemma repr_var_inj {lenv} : forall x x' i,
  map_injective lenv ->
  repr_var (lenv:=lenv) x' i ->
  repr_var (lenv:=lenv) x i ->
  x = x'.
Proof.
  intros ??? Hinj Hx Hx'.
  inv Hx. inv Hx'.
  unfold translate_var in *.
  destruct (lenv ! x) eqn:Hx; rewrite Hx in H0=>//.
  inv H0.
  destruct (lenv ! x') eqn:Hx'; rewrite Hx' in H=>//.
  inv H.
  destruct (var_dec x x') as [?|H] =>//.
  now have H' := Hinj _ _ _ _ _ Hx Hx'.
Qed.

Lemma repr_funvar_det : forall a a' a'',
  repr_funvar a a' ->
  repr_funvar a a'' ->
  a' = a''.
Proof.
  intros ??? Ha' Ha''. inv Ha'. inv Ha''.
  unfold translate_var in *.
  destruct (fenv ! a) eqn:Heqn=>//;
    rewrite Heqn in H, H0=>//.
  congruence.
Qed.


(* glob_cap: pointer to linear_memory[p + 4 + 4*n] = value v *)
Inductive store_nth_constr_arg {lenv} : nat -> var -> list basic_instruction -> Prop :=
  Make_nth_proj: forall (v : var) n instr,
    repr_read_var_or_funvar (lenv:=lenv) v instr ->
    store_nth_constr_arg n v
      [ BI_global_get glob_cap
      ; BI_const_num (nat_to_value ((1 + n) * 4))
      ; BI_binop T_i32 (Binop_i BOI_add)
      ; instr
      ; BI_store T_i32 None {| memarg_offset:=0%N; memarg_align:=2%N |}
      ; BI_global_get glob_mem_ptr
      ; BI_const_num (nat_to_value 4)
      ; BI_binop T_i32 (Binop_i BOI_add)
      ; BI_global_set glob_mem_ptr
      ].

(* args are pushed on the stack before calling a function *)
Inductive repr_fun_args_Wasm {lenv} : list LambdaANF.term.var ->
                                      list basic_instruction -> Prop :=
(* base case: no args *)
| FA_nil :
    repr_fun_args_Wasm [] []
(* arg is local var *)
| FA_cons_var : forall a a' args instr,
    repr_var (lenv:=lenv) a a' ->
    repr_fun_args_Wasm args instr ->
    repr_fun_args_Wasm (a :: args) ([BI_local_get a'] ++ instr)
(* arg is function -> lookup id for handling indirect calls later *)
| FA_cons_fun : forall a a' args instr,
    repr_funvar a a' ->
    repr_fun_args_Wasm args instr ->
    repr_fun_args_Wasm (a :: args) ([BI_const_num (N_to_value a')] ++ instr).

Inductive repr_asgn_constr_Wasm {lenv} : localidx -> ctor_tag -> list var -> list basic_instruction -> list basic_instruction ->  Prop :=
| Rconstr_asgn_boxed :
  forall x' t vs sargs scont arity ord,
    get_ctor_ord cenv t = Ret ord ->
    get_ctor_arity cenv t = Ret arity ->
    arity > 0 ->
    (* store args *)
    Forall_statements_in_seq (store_nth_constr_arg (lenv:=lenv)) vs sargs ->

    repr_asgn_constr_Wasm x' t vs scont
      ([ BI_global_get glob_mem_ptr
       ; BI_global_set glob_cap
       ; BI_global_get glob_cap
       ; BI_const_num (nat_to_value (N.to_nat ord))
       ; BI_store T_i32 None {| memarg_offset:=0%N; memarg_align:=2%N |}
       ; BI_global_get glob_mem_ptr
       ; BI_const_num (nat_to_value 4)
       ; BI_binop T_i32 (Binop_i BOI_add)
       ; BI_global_set glob_mem_ptr
       ] ++ sargs ++ [BI_global_get glob_cap; BI_local_set x'] ++ scont)

| Rconstr_asgn_unboxed :
  forall x' t scont ord,
    get_ctor_ord cenv t = Ret ord ->
    get_ctor_arity cenv t = Ret 0 ->
    repr_asgn_constr_Wasm x' t [] scont
      ([ BI_const_num (nat_to_value (N.to_nat (2 * ord + 1)%N))
       ; BI_local_set x' ] ++ scont ).


Inductive repr_case_boxed: localidx -> list (N * list basic_instruction) -> list basic_instruction -> Prop :=
| Rcase_boxed_nil: forall v, repr_case_boxed v [] [ BI_unreachable ]
| Rcase_boxed_cons: forall v ord instrs brs instrs_more,
    repr_case_boxed v brs instrs_more ->
    repr_case_boxed v ((ord, instrs) :: brs)
      [ BI_local_get v
      ; BI_load T_i32 None {| memarg_offset:=0%N; memarg_align:=2%N |}
      ; BI_const_num (nat_to_value (N.to_nat ord))
      ; BI_relop T_i32 (Relop_i ROI_eq)
      ; BI_if (BT_valtype None)
          instrs
          instrs_more
      ].

Inductive repr_case_unboxed: localidx -> list (N * list basic_instruction) -> list basic_instruction -> Prop :=
| Rcase_unboxed_nil: forall v, repr_case_unboxed v [] [ BI_unreachable ]
| Rcase_unboxed_cons: forall v ord instrs brs instrs_more,
    repr_case_unboxed v brs instrs_more ->
    repr_case_unboxed v ((ord, instrs) :: brs)
      [ BI_local_get v
      ; BI_const_num (nat_to_value (N.to_nat (2 * ord + 1)%N))
      ; BI_relop T_i32 (Relop_i ROI_eq)
      ; BI_if (BT_valtype None)
          instrs
          instrs_more
      ].


Inductive repr_primitive_unary_operation : primop -> localidx -> list basic_instruction -> Prop :=
| Rprim_head0: forall x,
    repr_primitive_unary_operation PrimInt63head0 x (head0_instrs glob_mem_ptr x)

| Rprim_tail0: forall x,
    repr_primitive_unary_operation PrimInt63tail0 x (tail0_instrs glob_mem_ptr x).

Inductive repr_primitive_binary_operation : primop -> localidx -> localidx -> list basic_instruction -> Prop :=
| Rprim_add : forall x y,
    repr_primitive_binary_operation PrimInt63add x y
      (apply_binop_and_store_i64 glob_mem_ptr BOI_add x y true)

| Rprim_sub : forall x y,
    repr_primitive_binary_operation PrimInt63sub x y
      (apply_binop_and_store_i64 glob_mem_ptr BOI_sub x y true)

| Rprim_mul : forall x y,
    repr_primitive_binary_operation PrimInt63mul x y
      (apply_binop_and_store_i64 glob_mem_ptr BOI_mul x y true)

| Rprim_div : forall x y,
    repr_primitive_binary_operation PrimInt63div x y (div_instrs glob_mem_ptr x y)

| Rprim_mod : forall x y,
    repr_primitive_binary_operation PrimInt63mod x y (mod_instrs glob_mem_ptr x y)

| Rprim_land : forall x y,
    repr_primitive_binary_operation PrimInt63land x y
      (apply_binop_and_store_i64 glob_mem_ptr BOI_and x y false)

| Rprim_lor : forall x y,
    repr_primitive_binary_operation PrimInt63lor x y
      (apply_binop_and_store_i64 glob_mem_ptr BOI_or x y false)

| Rprim_lxor : forall x y,
    repr_primitive_binary_operation PrimInt63lxor x y
      (apply_binop_and_store_i64 glob_mem_ptr BOI_xor x y false)

| Rprim_lsl : forall x y,
    repr_primitive_binary_operation PrimInt63lsl x y (shift_instrs glob_mem_ptr x y BOI_shl true)

| Rprim_lsr : forall x y,
    repr_primitive_binary_operation PrimInt63lsr x y (shift_instrs glob_mem_ptr x y (BOI_shr SX_U) false)

| Rprim_eqb : forall x y,
    repr_primitive_binary_operation PrimInt63eqb x y
      (make_boolean_valued_comparison x y ROI_eq)

| Rprim_ltb : forall x y,
    repr_primitive_binary_operation PrimInt63ltb x y
      (make_boolean_valued_comparison x y (ROI_lt SX_U))

| Rprim_leb : forall x y,
    repr_primitive_binary_operation PrimInt63leb x y
      (make_boolean_valued_comparison x y (ROI_le SX_U))

| Rprim_compare : forall x y,
    repr_primitive_binary_operation PrimInt63compare x y (compare_instrs x y)

| Rprim_addc : forall x y,
    repr_primitive_binary_operation PrimInt63addc x y
      (apply_add_carry_operation glob_mem_ptr glob_tmp1 x y false)

| Rprim_addcarryc : forall x y,
    repr_primitive_binary_operation PrimInt63addcarryc x y
      (apply_add_carry_operation glob_mem_ptr glob_tmp1 x y true)

| Rprim_subc : forall x y,
    repr_primitive_binary_operation PrimInt63subc x y
      (apply_sub_carry_operation glob_mem_ptr glob_tmp1 x y false)

| Rprim_subcarryc : forall x y,
    repr_primitive_binary_operation PrimInt63subcarryc x y
      (apply_sub_carry_operation glob_mem_ptr glob_tmp1 x y true)

| Rprim_mulc : forall x y,
    repr_primitive_binary_operation PrimInt63mulc x y
      (mulc_instrs glob_mem_ptr glob_tmp1 glob_tmp2 glob_tmp3 glob_tmp4 x y)

| Rprim_diveucl : forall x y,
    repr_primitive_binary_operation PrimInt63diveucl x y
      (diveucl_instrs glob_mem_ptr glob_tmp1 glob_tmp2 x y).

Inductive repr_primitive_ternary_operation : primop -> localidx -> localidx -> localidx -> list basic_instruction -> Prop :=
| Rprim_diveucl_21 : forall xh xl y,
    repr_primitive_ternary_operation PrimInt63diveucl_21 xh xl y
      (diveucl_21_instrs glob_mem_ptr glob_tmp1 glob_tmp2 glob_tmp3 glob_tmp4 glob_cap xh xl y)

| Rprim_addmuldiv : forall p x y,
    repr_primitive_ternary_operation PrimInt63addmuldiv p x y
      (addmuldiv_instrs glob_mem_ptr  p x y).

Inductive repr_primitive_operation {lenv} : primop -> list positive  -> list basic_instruction -> Prop :=
| Rprim_unop :
  forall op x x' instr,
    repr_var (lenv:=lenv) x x' ->
    repr_primitive_unary_operation op x' instr ->
    repr_primitive_operation op [ x ] instr

| Rprim_binop :
  forall op x x' y y' instr,
    repr_var (lenv:=lenv) x x' ->
    repr_var (lenv:=lenv) y y' ->
    repr_primitive_binary_operation op x' y' instr ->
    repr_primitive_operation op [ x ; y ] instr

| Rprim_ternop :
  forall op x x' y y' z z' instr,
    repr_var (lenv:=lenv) x x' ->
    repr_var (lenv:=lenv) y y' ->
    repr_var (lenv:=lenv) z z' ->
    repr_primitive_ternary_operation op x' y' z' instr ->
    repr_primitive_operation op [ x ; y ; z ] instr.


Inductive repr_call_grow_mem_if_necessary : N (* at least mem available, known statically *) ->
                                            N (* bytes required for alloc *) ->
                                            N (* at least mem available after allocation *) ->
                                            list basic_instruction (* generated instr *) -> Prop :=
| G_enough_mem : forall mem mem' bytes,
  (bytes <= mem)%N ->
  (mem' = mem - bytes)%N ->
  repr_call_grow_mem_if_necessary mem bytes mem' []

| G_call_grow_mem : forall mem mem' bytes,
  (bytes > mem)%N ->
  (mem' = 65536 - bytes)%N ->
  repr_call_grow_mem_if_necessary mem bytes mem' grow_memory_if_necessary
.


(* CODEGEN RELATION: relatates LambdaANF expression and result of translate_body *)
Inductive repr_expr_LambdaANF_Wasm {lenv} : LambdaANF.term.exp -> N -> list basic_instruction -> Prop :=
| R_halt_e: forall x x' mem,
    repr_var (lenv:=lenv) x x' ->
    repr_expr_LambdaANF_Wasm (Ehalt x) mem
      [ BI_local_get x'
      ; BI_global_set glob_result
      ; BI_return
      ]
| Rproj_e: forall x x' t n y y' e e' mem,
    repr_expr_LambdaANF_Wasm e mem e' ->
    repr_var (lenv:=lenv) x x' ->
    repr_var (lenv:=lenv) y y' ->
    repr_expr_LambdaANF_Wasm (Eproj x t n y e) mem
      ([ BI_local_get y'
       ; BI_const_num (nat_to_value (((N.to_nat n) + 1) * 4))
       ; BI_binop T_i32 (Binop_i BOI_add)
       ; BI_load T_i32 None {| memarg_offset:=0%N; memarg_align:=2%N |}
       ; BI_local_set x'
       ] ++ e')

| Rconstr_e: forall x x' t vs e arity instrs e' grow_mem_instr constr_size mem mem',
    get_ctor_arity cenv t = Ret arity ->
    get_ctor_size cenv t = Ret constr_size ->
    length vs = arity ->
    repr_call_grow_mem_if_necessary mem constr_size mem' grow_mem_instr ->
    repr_expr_LambdaANF_Wasm e mem' e' ->
    repr_var (lenv:=lenv) x x' ->
    repr_asgn_constr_Wasm (lenv:=lenv) x' t vs e' instrs ->
    repr_expr_LambdaANF_Wasm (Econstr x t vs e) mem (grow_mem_instr ++ instrs)

| Rcase_e : forall y y' cl brs1 brs2 e1' e2' mem,
    repr_var (lenv:=lenv) y y' ->
    repr_branches y' cl mem brs1 brs2 ->
    repr_case_boxed y' brs1 e1' ->
    repr_case_unboxed y' brs2 e2' ->
    repr_expr_LambdaANF_Wasm (Ecase y cl) mem
      [ BI_local_get y'
      ; BI_const_num (nat_to_value 1)
      ; BI_binop T_i32 (Binop_i BOI_and)
      ; BI_testop T_i32 TO_eqz
      ; BI_if (BT_valtype None)
          e1'
          e2'
      ]

| R_app_e : forall v instr t args args' mem,
    (* args are provided properly *)
    repr_fun_args_Wasm (lenv:=lenv) args args' ->
    (* instr reduces to const containing funidx to call *)
    repr_read_var_or_funvar (lenv:=lenv) v instr ->
    repr_expr_LambdaANF_Wasm (Eapp v t args) mem
      (args' ++ [instr] ++ [BI_return_call_indirect 0%N (N.of_nat (length args))])

| R_letapp_e : forall x x' v instr t args args' e e' mem,
    (* translated assigned var *)
    repr_var (lenv:=lenv) x x' ->
    (* following expression *)
    repr_expr_LambdaANF_Wasm e 0%N e' ->
    (* args are provided properly *)
    repr_fun_args_Wasm (lenv:=lenv) args args' ->
    (* instr reduces to const containing funidx to call *)
    repr_read_var_or_funvar (lenv:=lenv) v instr ->
    repr_expr_LambdaANF_Wasm (Eletapp x v t args e) mem
      (args' ++
       [ instr
       ; BI_call_indirect 0%N (N.of_nat (length args))
       ; BI_global_get glob_out_of_mem
       ; BI_if (BT_valtype None)
           (* grow mem failed *)
           [ BI_return ]
           []
       ; BI_global_get glob_result
       ; BI_local_set x'
       ] ++ e')

| R_prim_val : forall x x' p v e e' mem instr_grow_mem mem',
    repr_var (lenv:=lenv) x x' ->
    repr_expr_LambdaANF_Wasm e mem' e' ->
    translate_primitive_value p = Ret v ->
    repr_call_grow_mem_if_necessary mem 32%N mem' instr_grow_mem ->

    repr_expr_LambdaANF_Wasm (Eprim_val x p e) mem
      (instr_grow_mem ++
       [ BI_global_get glob_mem_ptr
       ; BI_const_num (VAL_int64 v)
       ; BI_store T_i64 None {| memarg_offset:=0%N; memarg_align:=2%N |}
       ; BI_global_get glob_mem_ptr
       ; BI_local_set x'
       ; BI_global_get glob_mem_ptr
       ; BI_const_num (nat_to_value 8)
       ; BI_binop T_i32 (Binop_i BOI_add)
       ; BI_global_set glob_mem_ptr
       ] ++ e')

| R_prim : forall x x' p op_name s b n op ys e e' prim_instrs mem mem' grow_instr,
    repr_var (lenv:=lenv) x x' ->
    repr_expr_LambdaANF_Wasm e mem' e' ->
    M.get p penv = Some (Pipeline_utils.mk_primitive op_name s b n) ->
    KernameMap.find op_name primop_map = Some op ->
    repr_primitive_operation (lenv:=lenv) op ys prim_instrs ->
    repr_call_grow_mem_if_necessary mem 52%N mem' grow_instr ->

    repr_expr_LambdaANF_Wasm (Eprim x p ys e) mem
      (grow_instr ++ prim_instrs ++ [ BI_local_set x' ] ++  e')

with repr_branches {lenv}: localidx -> list (ctor_tag * exp) -> N -> list (N * list basic_instruction) -> list (N * list basic_instruction) -> Prop :=
| Rbranch_nil : forall x mem,
    repr_branches x [] mem [] []

| Rbranch_cons_boxed : forall x cl t e ord n e' brs1 brs2 mem,
    repr_branches x cl mem brs1 brs2 ->
    get_ctor_ord cenv t = Ret ord ->
    get_ctor_arity cenv t = Ret n ->
    0 < n ->
    repr_expr_LambdaANF_Wasm e mem e' ->
    repr_branches x ((t, e) :: cl) mem ((ord,e') :: brs1) brs2

| Rbranch_cons_unboxed : forall x cl t e ord n e' brs1 brs2 mem,
    repr_branches x cl mem brs1 brs2 ->
    get_ctor_ord cenv t = Ret ord ->
    get_ctor_arity cenv t = Ret n ->
    n = 0 ->
    repr_expr_LambdaANF_Wasm e mem e' ->
    repr_branches x ((t, e) :: cl) mem brs1 ((ord,e') :: brs2).

Scheme repr_expr_LambdaANF_Wasm_mut := Induction for repr_expr_LambdaANF_Wasm Sort Prop
    with repr_branches_mut :=
      Induction for repr_branches Sort Prop.


Lemma pass_function_args_correct {lenv} : forall l instr,
  pass_function_args nenv lenv fenv l = Ret instr ->
  @repr_fun_args_Wasm lenv l instr.
Proof.
  induction l; intros; first by inv H; constructor.
  cbn in H. destruct (instr_local_var_read nenv lenv fenv a) eqn:Hvar. inv H.
  destruct (pass_function_args nenv lenv fenv l) eqn:prep. inv H. inv H.
  unfold instr_local_var_read in Hvar.
  destruct (is_function_var fenv a) eqn:Hfname.
  - destruct (translate_var nenv fenv a _) eqn:fun_var; inv Hvar.
    constructor. econstructor. eassumption.
    apply IHl; auto.
  - destruct (translate_var nenv lenv a _) eqn:var_var; inv Hvar.
    constructor. econstructor. eassumption. apply IHl; auto.
Qed.

Lemma store_nth_constr_arg_correct {lenv} : forall  l instr n,
  store_constructor_args nenv lenv fenv l n = Ret instr ->
  Forall_statements_in_seq' (@store_nth_constr_arg lenv) l instr n.
Proof.
  induction l; intros. { inv H. econstructor; auto. }
  cbn in H. destruct (instr_local_var_read _ _ _ _) eqn:Hvar. inv H.
  destruct (store_constructor_args _ _ _ _) eqn:Harg. inv H. inv H.
  separate_instr. do 8! rewrite catA. constructor. auto.
  replace (nat_to_value (S (n + S (n + S (n + S (n + 0)))))) with
          (nat_to_value ((1 + n) * 4)) by (f_equal; lia).
  constructor.
  unfold instr_local_var_read in Hvar.
  destruct (is_function_var fenv a) eqn:Hfn.
  - destruct (translate_var nenv fenv a _) eqn:Hvar'. inv Hvar. inv Hvar.
    constructor. now econstructor.
  - destruct (translate_var nenv lenv a _) eqn:Hloc. inv Hvar. inv Hvar.
    constructor. now econstructor.
Qed.

Lemma call_grow_mem_if_necessary_correct : forall mem bytes p,
  call_grow_mem_if_necessary mem bytes = p ->
  repr_call_grow_mem_if_necessary mem bytes (snd p) (fst p).
Proof.
  intros.
  unfold call_grow_mem_if_necessary in H.
  destruct ((bytes <=? mem)%N) eqn:Henough.
  - (* enough *)
    inv H. apply G_enough_mem=>//.
    now apply N.leb_le in Henough.
  - (* need more *)
    apply N.leb_gt in Henough.
    subst.
    apply G_call_grow_mem=>//. lia.
Qed.

Theorem translate_body_correct {lenv} : forall e instructions mem,
  correct_cenv_of_exp cenv e ->
  translate_body nenv cenv lenv fenv penv e mem = Ret instructions ->
  @repr_expr_LambdaANF_Wasm lenv e mem instructions.
Proof.
  induction e using exp_ind'; intros instr mem Hcenv H.
  - (* Econstr *)
    simpl in H.
    destruct (translate_var nenv lenv v _) eqn:H_translate_var. inv H.
    destruct l as [|v0 l'].
    + (* Nullary constructor *)
      destruct (get_ctor_ord cenv t) eqn:Hord. inv H.
      destruct (translate_body nenv cenv lenv fenv penv e mem) eqn:H_eqTranslate; inv H.
      assert (get_ctor_size cenv t = Ret 0%N). {
      apply correct_cenv_of_exp_get_ctor_arity in Hcenv.
        unfold get_ctor_size. now rewrite Hcenv. }
      eapply Rconstr_e with (e':=l) (grow_mem_instr:=[]) (mem':=mem); eauto.
      eapply correct_cenv_of_exp_get_ctor_arity. eassumption.
      apply G_enough_mem; lia.
      apply IHe; auto.
      assert (subterm_e e (Econstr v t [] e) ). { constructor; constructor. }
      eapply Forall_constructors_subterm. eassumption. assumption.
      econstructor; eauto.
      eapply Rconstr_asgn_unboxed; eauto.
      apply Forall_constructors_in_constr in Hcenv.
      destruct (cenv ! t) eqn:Hc; auto. destruct c. inv Hcenv.
      unfold get_ctor_arity. now rewrite Hc.
    + (* Non-nullary constructor *)
      remember (v0 :: l') as l.
      destruct (store_constructor nenv cenv lenv fenv t l) eqn:Hstore_constr; cbn [bind MonadError] in H; inv H.
      destruct (get_ctor_size _ _) eqn:HconstrSize; cbn [bind MonadError] in H1. inv H1.
      destruct (call_grow_mem_if_necessary mem n) eqn:Hgrow. inv H1.
      unfold store_constructor in Hstore_constr.
      destruct (get_ctor_ord cenv t) eqn:Hord; first by inv Hstore_constr.
      cbn [bind MonadError] in Hstore_constr.
      destruct (store_constructor_args nenv lenv fenv (v0 :: l') 0) eqn:Hconstrargs; first by inv Hstore_constr.
      cbn [bind MonadError] in Hstore_constr.
      destruct (translate_body _ _ _ _ _ _ _) eqn:Hbody. inv H0.
      cbn [bind MonadError] in H0. inv H0.
      inv Hstore_constr. cbn.
      repeat rewrite <- app_assoc.
      apply call_grow_mem_if_necessary_correct in Hgrow.

      eapply Rconstr_e with (e' := l2); eauto.
      eapply correct_cenv_of_exp_get_ctor_arity. eassumption.
      apply IHe.
      assert (subterm_e e (Econstr v t (v0 :: l') e) ). { constructor; constructor. }
      eapply Forall_constructors_subterm. eassumption. assumption. assumption.
      econstructor. eassumption.
      apply Forall_constructors_in_constr in Hcenv; auto.
      destruct (cenv ! t) eqn:Hc. 2:auto. destruct c. inv Hcenv.
      apply Rconstr_asgn_boxed with (arity:=S (length l')); eauto.
      unfold get_ctor_arity. rewrite Hc. f_equal. cbn. lia. lia.
      apply store_nth_constr_arg_correct.
      by assumption.
  - (* Ecase nil *)
    simpl in H. destruct (translate_var nenv lenv v _) eqn:Hvar; inv H.
    econstructor; try by constructor. now econstructor.
  - (* Ecase const *)
    simpl in H.
    destruct (translate_var nenv lenv v _) eqn:Hvar. inv H.
    destruct (translate_body nenv cenv lenv fenv penv e mem) eqn:He. inv H.
    destruct (translate_body nenv cenv lenv fenv penv (Ecase v l) mem) eqn:Hl.
    simpl in Hl. destruct (_ l) eqn:Hm. inv H. rewrite Hvar in Hl. destruct p. inv Hl.
    assert (correct_cenv_of_exp cenv (Ecase v l)). {
      intros ?????. eapply Hcenv. apply rt_then_t_or_eq in H0. inv H0. inv H1.
      apply t_then_rt. apply subterm_case. by eauto.
    }
    specialize (IHe0 l1 mem H0 Hl).
    simpl in Hl.
    destruct (_ l) eqn:Hm. inv H. rewrite Hvar in Hl. inv Hl. destruct p.
    assert (correct_cenv_of_exp cenv e). {
      intros ?????. eapply Hcenv.
      eapply rt_trans; eauto.
      constructor. econstructor. now left.
    }
    specialize (IHe l0 mem H1 He).
    inv IHe0. inv H2.
    unfold create_case_nested_if_chain in H7.
    unfold create_case_nested_if_chain in H10.
    destruct (get_ctor_ord cenv c) eqn:Hord. inv H.
    rename n into ord.
    destruct (get_ctor_arity cenv c) eqn:Har. inv H.
    destruct n eqn:Hn.
    + (* Unboxed branch *)
      inv H. destruct l3. econstructor; eauto.
      econstructor; eauto. econstructor; eauto. cbn in H7.
      by repeat (econstructor; eauto).
    + (* Boxed branch *)
      inv H.
      destruct l2; econstructor; eauto; econstructor; eauto; lia.
  - (* Eproj *)
    simpl in H.
    destruct (translate_body nenv cenv lenv fenv penv e) eqn:He. inv H.
    destruct (translate_var nenv lenv v0 _) eqn:Hy. inv H.
    destruct (translate_var nenv lenv v _) eqn:Hx. inv H.
    injection H => instr'. subst. clear H. constructor. apply IHe; auto.
    unfold correct_cenv_of_exp in Hcenv.
    eapply Forall_constructors_subterm. eassumption.
    unfold subterm_e. constructor. constructor.
    econstructor; eauto. by econstructor; eauto.
  - (* Eletapp *)
    simpl in H.
    destruct (translate_var nenv lenv x _) eqn:Hvar. inv H.
    destruct (translate_body nenv cenv lenv fenv penv e) eqn:H_eqTranslate. inv H.
    unfold translate_call in H.
    destruct (pass_function_args nenv lenv fenv ys) eqn:Hargs. inv H.
    destruct (instr_local_var_read nenv lenv fenv f) eqn:Hloc. inv H. inv H.
    rewrite <- app_assoc. constructor. econstructor. eassumption.
    apply IHe; auto.
    eapply Forall_constructors_subterm; eauto. constructor. constructor.
    apply pass_function_args_correct. assumption.
    unfold instr_local_var_read in Hloc.
    destruct (is_function_var fenv f) eqn:Hfname.
    + destruct (translate_var nenv fenv f _) eqn:fun_var; inv Hloc.
      constructor. econstructor. eassumption.
    + destruct (translate_var  nenv lenv f _) eqn:var_var; inv Hloc.
      constructor. now econstructor.
  - (* Efun *) by inv H.
  - (* Eapp *)
    simpl in H. unfold translate_call in H.
    destruct (pass_function_args nenv lenv fenv l) eqn:Hargs. inv H.
    destruct (instr_local_var_read nenv lenv fenv v) eqn:Hloc. inv H. inv H. constructor.
    apply pass_function_args_correct. assumption.
    unfold instr_local_var_read in Hloc.
    destruct (is_function_var fenv v) eqn:Hfname.
    + destruct (translate_var nenv fenv v _) eqn:fun_var; inv Hloc.
      constructor. now econstructor.
    + destruct (translate_var  nenv lenv v _) eqn:var_var; inv Hloc.
      constructor. now econstructor.
  - (* Eprim_val *)
    inv H.
    destruct (translate_var nenv lenv v _) eqn:Hvar. inv H1.
    destruct (translate_primitive_value p) eqn:Hprim. inv H1.
    destruct (call_grow_mem_if_necessary mem 32) eqn:Hgrow. inv H1.
    destruct (translate_body nenv cenv lenv fenv penv e _) eqn:H_eqTranslate. inv H0.
    inv H0.
    apply call_grow_mem_if_necessary_correct in Hgrow.
    eapply R_prim_val; eauto.
    + now econstructor.
    + assert (Hcenv': correct_cenv_of_exp cenv e). {
        intro; intros. eapply Hcenv. eapply rt_trans. eauto. constructor.
        now econstructor.
      }
      now eapply IHe.
  - (* Eprim *)
    inv H.
    destruct (penv ! p) eqn:Hp. 2: inv H1.
    destruct (translate_var nenv lenv v _) eqn:Hvar. inv H1.
    destruct (translate_primitive_operation _) eqn:Hprimop. inv H1.
    destruct (call_grow_mem_if_necessary mem 52) eqn:Hgrow. inv H1.
    destruct (translate_body nenv cenv lenv fenv penv e _) eqn:H_eqTranslate. inv H0.
    unfold translate_primitive_operation in Hprimop.
    destruct p0.
    destruct (KernameMap.find _) eqn:Hker. 2: inv Hprimop.
    inv H0. cbn.
    apply call_grow_mem_if_necessary_correct in Hgrow.
    eapply R_prim; eauto.
    econstructor; eauto.
    assert (Hcenv': correct_cenv_of_exp cenv e). {
      intro; intros. eapply Hcenv. eapply rt_trans. eauto. constructor.
      now econstructor.
    }
    now eapply IHe.
    simpl in Hprimop.
    destruct l. inv Hprimop.
    destruct l.
    { (* Unary operations *)
      destruct (translate_var nenv lenv v0 _) eqn:Hx. inv Hprimop.
      unfold translate_primitive_unary_op in Hprimop.
      destruct p0; inv Hprimop; econstructor; econstructor; eauto.
    }
    destruct l.
    { (* Binary operations *)
      destruct (translate_var nenv lenv v0 _) eqn:Hx. inv Hprimop.
      destruct (translate_var nenv lenv v1 _) eqn:Hy. inv Hprimop.
      unfold translate_primitive_binary_op in Hprimop.
      destruct p0; try inv Hprimop; econstructor; econstructor; eauto.
    }
    destruct l. 2: inv Hprimop.
    { (* Ternary ops *)
      destruct (translate_var nenv lenv v0 _) eqn:Hx. inv Hprimop.
      destruct (translate_var nenv lenv v1 _) eqn:Hy. inv Hprimop.
      destruct (translate_var nenv lenv v2 _) eqn:Hz. inv Hprimop.
      unfold translate_primitive_ternary_op in Hprimop.
      destruct p0; try inv Hprimop; econstructor; econstructor; eauto.
    }
  - (* Ehalt *)
    simpl in H. destruct (translate_var nenv lenv v _) eqn:Hvar. inv H.
    injection H => instr'. subst. constructor. now econstructor.
Qed.

End CODEGEN.


Section MAIN.

Variable cenv : LambdaANF.term.ctor_env.
Variable funenv : LambdaANF.term.fun_env.
Variable fenv : CodegenWasm.LambdaANF_to_Wasm.fname_env.
Variable nenv : LambdaANF.cps_show.name_env.
Variable penv : LambdaANF.toplevel.prim_env.

Let repr_expr_LambdaANF_Wasm := @repr_expr_LambdaANF_Wasm cenv fenv nenv penv.
Let repr_funvar := @repr_funvar fenv nenv.

Context `{ho : host}.

(* VALUE RELATION *)
(* immediate is pointer to linear memory or function id *)
Inductive repr_val_LambdaANF_Wasm : LambdaANF.term.val -> store_record -> moduleinst -> wasm_value -> Prop :=
| Rconstr_unboxed_v : forall v (t : ctor_tag) (sr : store_record) inst ord,
    get_ctor_ord cenv t = Ret ord ->
    (ord * 2 + 1 = v)%N ->
    (-1 < Z.of_N v < Wasm_int.Int32.modulus)%Z ->
    get_ctor_arity cenv t = Ret 0 ->
    repr_val_LambdaANF_Wasm (Vconstr t []) sr inst (Val_unboxed v)

| Rconstr_boxed_v : forall v t vs (sr : store_record) inst gmp m (addr : u32) arity ord,
    (* simple memory model: gmp is increased whenever new mem is needed,
       gmp only increases *)
    sglob_val sr inst glob_mem_ptr = Some (VAL_num (VAL_int32 (N_to_i32 gmp))) ->
    (-1 < Z.of_N gmp < Wasm_int.Int32.modulus)%Z ->
    (* constr arity > 0 *)
    get_ctor_ord cenv t = Ret ord ->
    get_ctor_arity cenv t = Ret arity ->
    arity > 0 ->
    (* addr in bounds of linear memory (later INV: gmp + 4 < length of memory) *)
    (addr + 4 <= gmp)%N ->
    (exists n, addr = 2 * n)%N ->
    (* store_record contains memory *)
    smem sr inst = Some m ->
    (* constructor tag is set, see LambdaANF_to_W, constr alloc structure*)
    v = (nat_to_i32 (N.to_nat ord)) ->
    load_i32 m addr = Some (VAL_int32 v) ->
    (* arguments are set properly *)
    repr_val_constr_args_LambdaANF_Wasm vs sr inst (4 + addr)%N ->
    repr_val_LambdaANF_Wasm (Vconstr t vs) sr inst (Val_ptr addr)

| Rfunction_v : forall fds f func sr inst tag xs e e' idx,
      repr_funvar f idx ->
      find_def f fds = Some (tag, xs, e) ->
      func = {| modfunc_type := N.of_nat (length xs)
              ; modfunc_locals := repeat (T_num T_i32) (length (collect_local_variables e))
              ; modfunc_body := e'
              |} ->
      (* find runtime representation of function *)
      lookup_N sr.(s_funcs) idx = Some (FC_func_native (Tf (repeat (T_num T_i32) (length xs)) []) inst func) ->
      repr_expr_LambdaANF_Wasm (create_local_variable_mapping (xs ++ collect_local_variables e)) e 0%N e' ->
      repr_val_LambdaANF_Wasm (Vfun (M.empty _) fds f) sr inst (Val_funidx idx)

|  Rprim_v : forall n sr inst gmp m addr,
    sglob_val sr inst glob_mem_ptr = Some (VAL_num (VAL_int32 (N_to_i32 gmp))) ->
    (-1 < Z.of_N gmp < Wasm_int.Int32.modulus)%Z ->
    (addr+8 <= gmp)%N ->
    (exists n, addr = 2 * n)%N ->
    smem sr inst = Some m ->
    load_i64 m addr = Some (VAL_int64 (Z_to_i64 (Uint63.to_Z n))) ->
    repr_val_LambdaANF_Wasm (Vprim (primInt n)) sr inst (Val_ptr addr)

with repr_val_constr_args_LambdaANF_Wasm : list LambdaANF.term.val -> store_record -> moduleinst -> u32 -> Prop :=
     | Rnil_l: forall sr fr addr,
        repr_val_constr_args_LambdaANF_Wasm nil sr fr addr

     | Rcons_l: forall v wal vs sr inst m addr gmp,
        (* store_record contains memory *)
        smem sr inst = Some m ->

        sglob_val sr inst glob_mem_ptr = Some (VAL_num (VAL_int32 (N_to_i32 gmp))) ->
        (-1 < Z.of_N gmp < Wasm_int.Int32.modulus)%Z ->
        (addr + 4 <= gmp)%N ->

        (* constr arg is ptr related to value v *)
        load_i32 m addr = Some (VAL_int32 (wasm_value_to_i32 wal)) ->
        repr_val_LambdaANF_Wasm v sr inst wal ->

        (* following constr args are also related *)
        repr_val_constr_args_LambdaANF_Wasm vs sr inst (4 + addr)%N ->
        repr_val_constr_args_LambdaANF_Wasm (v::vs) sr inst addr.

Scheme repr_val_LambdaANF_Wasm_mut := Induction for repr_val_LambdaANF_Wasm Sort Prop
  with repr_val_constr_args_LambdaANF_Wasm_mut :=
    Induction for repr_val_constr_args_LambdaANF_Wasm Sort Prop.

Lemma val_relation_func_depends_on_funcs : forall val s s' inst i,
  s_funcs s = s_funcs s' ->
  repr_val_LambdaANF_Wasm val s  inst (Val_funidx i) ->
  repr_val_LambdaANF_Wasm val s' inst (Val_funidx i).
Proof.
  intros ? ? ? ? ? Hfuncs Hval.
  inv Hval. now econstructor; eauto.
Qed.


(* TODO move somewhere else *)
Ltac simpl_eq :=
  repeat lazymatch goal with
  | H: nat_to_i32 _ = nat_to_i32 _ |- _ =>
        injection H as H
  | H: N_to_i32 _ = N_to_i32 _ |- _ =>
        injection H as H
  | H: _ = Wasm_int.Int32.Z_mod_modulus _ |- _ =>
         rewrite Wasm_int.Int32.Z_mod_modulus_id in H; last lia
  | H: Wasm_int.Int32.Z_mod_modulus _ = _ |- _ =>
          rewrite Wasm_int.Int32.Z_mod_modulus_id in H; last lia
  | H: Z.of_nat _ = Z.of_nat _ |- _ =>
         apply Nat2Z.inj in H
  | H: Z.of_N _ = Z.of_N _ |- _ =>
         apply N2Z.inj in H
  end.

Ltac solve_eq_global x y :=
  assert (x = y); first
    (try assert (N_to_i32 x = N_to_i32 y) by congruence; simpl_eq; done); subst y.

(* TODO add case when global was updated etc. *)
Ltac solve_eq_mem m1 m2 :=
  assert (m1 = m2) by congruence; subst m2.

(* proves and substitutes equality on given vars, the first one is kept *)
Ltac solve_eq x y :=
  lazymatch goal with
  (* equality on global mems *)
  | H: smem ?s _ = Some x |- _ => solve_eq_mem x y
  (* equality on globals *)
  | H: _ |- _ => solve_eq_global x y
  end.

Lemma val_relation_depends_on_mem_smaller_than_gmp_and_funcs : forall v sr sr' m m' inst gmp gmp' value,
  sr.(s_funcs) = sr'.(s_funcs) ->
  smem sr inst = Some m ->
  smem sr' inst = Some m' ->
  (* memories agree on values < gmp *)
  sglob_val sr inst glob_mem_ptr = Some (VAL_num (VAL_int32 (N_to_i32 gmp))) ->
  (Z.of_N gmp + 8 <= Z.of_N (mem_length m) < Wasm_int.Int32.modulus)%Z ->
  sglob_val sr' inst glob_mem_ptr = Some (VAL_num (VAL_int32 (N_to_i32 gmp'))) ->
  (Z.of_N gmp' + 8 <= Z.of_N (mem_length m') < Wasm_int.Int32.modulus)%Z ->
  (gmp' >= gmp)%N ->
  (forall a, (a + 4 <= gmp)%N -> load_i32 m a = load_i32 m' a) ->
  (forall a, (a + 8 <= gmp)%N -> load_i64 m a = load_i64 m' a) ->

  repr_val_LambdaANF_Wasm v sr inst value ->
  repr_val_LambdaANF_Wasm v sr' inst value.
Proof.
  intros. inv H9.
  (* Nullary constructor value *)
  { now econstructor. }
  (* Non-nullary constructor value *)
  {
  have indPrinciple := repr_val_constr_args_LambdaANF_Wasm_mut
  (fun (v : term.val) (s : store_record) (inst : moduleinst) (w : wasm_value)
       (H: repr_val_LambdaANF_Wasm v s inst w) =>
       (forall a s' m m',
          s_funcs s = s_funcs s' ->
          smem s inst = Some m ->
          smem s' inst = Some m' ->
          (* memories agree on values < gmp *)
          sglob_val s inst glob_mem_ptr = Some (VAL_num (VAL_int32 (N_to_i32 gmp))) ->
          (Z.of_N gmp + 8 <= Z.of_N (mem_length m) < Wasm_int.Int32.modulus)%Z ->
          sglob_val s' inst glob_mem_ptr = Some (VAL_num (VAL_int32 (N_to_i32 gmp'))) ->
          (Z.of_N gmp' + 8 <= Z.of_N (mem_length m') < Wasm_int.Int32.modulus)%Z ->
          (gmp' >= gmp)%N ->
          (forall a, (a + 4<= gmp)%N -> load_i32 m a = load_i32 m' a) ->
          (forall a, (a + 8<= gmp)%N -> load_i64 m a = load_i64 m' a) ->
              repr_val_LambdaANF_Wasm v s' inst w)
    )
  (fun (l : seq term.val) (s : store_record) (inst : moduleinst) (addr : u32)
       (H: repr_val_constr_args_LambdaANF_Wasm l s inst addr) =>
       (forall a s' m m',
          s_funcs s = s_funcs s' ->
          smem s inst = Some m ->
          smem s' inst = Some m' ->
          (* memories agree on values < gmp *)
          sglob_val s inst glob_mem_ptr = Some (VAL_num (VAL_int32 (N_to_i32 gmp))) ->
          (Z.of_N gmp + 8 <= Z.of_N (mem_length m) < Wasm_int.Int32.modulus)%Z ->
          sglob_val s' inst glob_mem_ptr = Some (VAL_num (VAL_int32 (N_to_i32 gmp'))) ->
          (Z.of_N gmp' + 8 <= Z.of_N (mem_length m') < Wasm_int.Int32.modulus)%Z ->
          (gmp' >= gmp)%N ->
          (forall a, (a + 4 <= gmp)%N -> load_i32 m a = load_i32 m' a) ->
          (forall a, (a + 8 <= gmp)%N -> load_i64 m a = load_i64 m' a) ->
             repr_val_constr_args_LambdaANF_Wasm l s' inst addr)
  ). have H20' := H20.
    eapply indPrinciple in H20; intros; clear indPrinciple; try eassumption; try lia.
    { solve_eq gmp0 gmp.
      solve_eq m m0.
      econstructor; try eassumption. lia. lia. reflexivity.
      rewrite <- H7. assumption. lia. }
    { now econstructor. }
    { solve_eq gmp gmp0. solve_eq gmp gmp1.
      solve_eq m m0. solve_eq m1 m2.
      econstructor; eauto. lia. rewrite <- H28; auto; try lia. }
    { econstructor; eauto. congruence. }
    { econstructor; eauto.
      solve_eq gmp gmp1. lia.
      solve_eq m1 m2. rewrite <- H28. assumption. solve_eq gmp gmp1. lia. }
    { econstructor. }
    { solve_eq gmp gmp0. solve_eq gmp gmp1.
      econstructor; eauto; try lia.
      rewrite <- H29. assert (m1 = m2) by congruence. subst m2. eassumption.
      lia. eapply H9; eauto; lia. }
    { solve_eq m m0. lia. }
    { solve_eq m m0. apply H7. lia. }
    { solve_eq m m0. apply H8. lia. }
  }
  (* function *)
  { econstructor; eauto. by rewrite <- H. }
  (* primitive value *)
  { econstructor; eauto. lia. solve_eq gmp gmp0. lia. solve_eq m m0.
    rewrite <- H8. assumption. solve_eq gmp gmp0. lia. }
Qed.


(* RESULT RELATION *)
Definition result_val_LambdaANF_Wasm (val : LambdaANF.term.val) (sr : store_record) (inst : moduleinst) : Prop :=
     (exists res_i32 wasmval,
       (* global var *glob_result* contains correct return value *)
       sglob_val sr inst glob_result = Some (VAL_num (VAL_int32 res_i32))
         /\ wasm_value_to_i32 wasmval = res_i32
         /\ repr_val_LambdaANF_Wasm val sr inst wasmval
         /\ (sglob_val sr inst glob_out_of_mem = Some (VAL_num (nat_to_value 0))))
  \/ (sglob_val sr inst glob_out_of_mem = Some (VAL_num (nat_to_value 1))).


(* ENVIRONMENT RELATION (also named memory relation in C-backend) *)

Definition stored_in_locals {lenv} (x : term.var) (v : wasm_value) (f : frame ) :=
  exists i,
  @repr_var nenv lenv x i /\
  lookup_N f.(f_locs) i = Some (VAL_num (VAL_int32 (wasm_value_to_i32 v))).

Definition rel_env_LambdaANF_Wasm {lenv} (e : exp) (rho : LambdaANF.eval.env)
                    (sr : store_record) (fr : frame) (fds : fundefs) :=
  (forall x f v fds' rho',
   rho ! x = Some v ->
   (* f is var in fds, v is either a Vfun or Vconstr value *)
   subval_or_eq (Vfun rho' fds' f) v ->
   (* fds only on toplevel, thus the two equalities *)
   rho' = M.empty _ /\ fds' = fds /\ name_in_fundefs fds f)
/\
  (forall f,
   name_in_fundefs fds f ->
   (* i is index of function f *)
   exists i, repr_funvar f i /\
   (* function def is related to function index *)
   repr_val_LambdaANF_Wasm (Vfun (M.empty _) fds f) sr (f_inst fr) (Val_funidx i))
/\
  (* free variables are related to local var containing a
     memory pointer or a function index *)
  (forall x,
   occurs_free e x ->
   (* not a function var *)
   find_def x fds = None ->
   (exists v w,
    rho ! x = Some v /\
    stored_in_locals (lenv:=lenv) x w fr /\
    repr_val_LambdaANF_Wasm v sr (f_inst fr) w)).

(* INVARIANTS *)

Notation i32_glob gidx := (In gidx [ glob_result; glob_out_of_mem; glob_mem_ptr; glob_cap ]).
Notation i64_glob gidx := (In gidx [ glob_tmp1; glob_tmp2; glob_tmp3; glob_tmp4 ]).

Definition globals_all_mut32 s f := forall gidx g g0,
    i32_glob gidx ->
    lookup_N (inst_globals (f_inst f)) gidx = Some g ->
    lookup_N (s_globals s) g = Some g0 ->
    exists val,
      g0 = {| g_type := {| tg_mut := MUT_var; tg_t := T_num T_i32 |}
           ; g_val := VAL_num (VAL_int32 val)
           |}.

Definition globals_all_mut64 s f := forall gidx g g0,
    i64_glob gidx ->
    lookup_N (inst_globals (f_inst f)) gidx = Some g ->
    lookup_N (s_globals s) g = Some g0 ->
    exists val,
      g0 = {| g_type := {| tg_mut := MUT_var; tg_t := T_num T_i64 |}
             ; g_val := VAL_num (VAL_int64 val)
             |}.

Definition globals_all_mut s f :=
    globals_all_mut32 s f /\ globals_all_mut64 s f.

Definition global_var_w var (s : store_record) (f : frame) := forall val,
  exists s', supdate_glob s (f_inst f) var (VAL_num val) = Some s'.

Definition global_var_r var (s : store_record) (f : frame) :=
   exists v, sglob_val s (f_inst f) var = Some (VAL_num v).

Definition INV_glob_result_writable := global_var_w glob_result.
Definition INV_glob_out_of_mem_writable := global_var_w glob_out_of_mem.
Definition INV_glob_mem_ptr_writable := global_var_w glob_mem_ptr.
Definition INV_glob_cap_writable := global_var_w glob_cap.
Definition INV_globals_all_mut := globals_all_mut.
Definition INV_i64_glob_tmps_writable (s : store_record) (f : frame) := forall gidx, i64_glob gidx -> global_var_w gidx s f.
(* indicates all good, didn't run out of mem *)
Definition INV_glob_out_of_mem_is_zero s f :=
  sglob_val s (f_inst f) glob_out_of_mem = Some (VAL_num (VAL_int32 (nat_to_i32 0))).

Definition INV_linear_memory sr fr :=
  inst_mems (f_inst fr) = [0%N] /\
  exists m, smem sr (f_inst fr) = Some m
   /\ exists size, mem_size m = size
   /\ m.(meminst_type).(lim_max) = Some max_mem_pages
   /\ (size <= max_mem_pages)%N.

Definition INV_glob_mem_ptr_in_linear_memory s f := forall gmp_v m,
  smem s (f_inst f) = Some m ->
  sglob_val s (f_inst f) glob_mem_ptr = Some (VAL_num (VAL_int32 (N_to_i32 gmp_v))) ->
  (-1 < Z.of_N gmp_v < Wasm_int.Int32.modulus)%Z ->
  (* enough space to store an i64 *)
  (gmp_v + 8 <= mem_length m)%N.

Definition INV_glob_cap_in_linear_memory s f := forall addr t m,
  sglob_val s (f_inst f) glob_cap = Some (VAL_num (VAL_int32 addr)) ->
  exists m', store m (Wasm_int.N_of_uint i32m addr) 0%N
                     (serialise_num (nat_to_value (Pos.to_nat t))) 4 = Some m'.

Definition INV_locals_all_i32 f := forall i v,
  nth_error (f_locs f) i = Some v -> exists v', v = VAL_num (VAL_int32 v').

Definition INV_num_functions_bounds sr fr :=
  (Z.of_nat num_custom_funs <= Z.of_nat (length (s_funcs sr)) <= max_num_functions + Z.of_nat num_custom_funs)%Z /\
  length (inst_elems (f_inst fr)) <= Z.to_nat max_num_functions + num_custom_funs.

Definition INV_inst_globals_nodup f :=
  NoDup (inst_globals (f_inst f)).

Definition INV_table_id sr fr := forall f i,
  repr_funvar f i ->
  stab_elem sr (f_inst fr) 0%N i = Some (VAL_ref_func i).

Definition INV_fvar_idx_inbounds sr := forall fvar fIdx,
  repr_funvar fvar fIdx ->
  (fIdx < N.of_nat (length (s_funcs sr)))%N.

Definition INV_types (fr : frame) := forall i,
  (Z.of_N i <= max_function_args)%Z ->
  lookup_N (inst_types (f_inst fr)) i = Some (Tf (List.repeat (T_num T_i32) (N.to_nat i)) [::]).

Definition INV_glob_mem_ptr_multiple_of_two s f := forall gmp_v m,
  smem s (f_inst f) = Some m ->
  sglob_val s (f_inst f) glob_mem_ptr = Some (VAL_num (VAL_int32 (N_to_i32 gmp_v))) ->
  (-1 < Z.of_N gmp_v < Wasm_int.Int32.modulus)%Z ->
  exists n, (gmp_v = 2 * n)%N.

Definition INV_inst_funcs_id sr f := forall i,
  (i < N.of_nat (length (s_funcs sr)))%N ->
  lookup_N (inst_funcs (f_inst f)) i = Some i.

(* invariants that need to hold throughout the execution of the Wasm program,
   (except when memory runs, until program terminates)

   also depends on fenv, shouldn't depend on lenv *)
Definition INV (s : store_record) (f : frame) :=
    INV_glob_result_writable s f
 /\ INV_glob_out_of_mem_writable s f
 /\ INV_glob_out_of_mem_is_zero s f
 /\ INV_glob_mem_ptr_writable s f
 /\ INV_glob_cap_writable s f
 /\ INV_globals_all_mut s f
 /\ INV_linear_memory s f
 /\ INV_glob_mem_ptr_in_linear_memory s f
 /\ INV_locals_all_i32 f
 /\ INV_num_functions_bounds s f
 /\ INV_inst_globals_nodup f
 /\ INV_table_id s f
 /\ INV_types f
 /\ INV_glob_mem_ptr_multiple_of_two s f
 /\ INV_inst_funcs_id s f
 /\ INV_i64_glob_tmps_writable s f.

Lemma globs_disjoint : forall i i',
  i32_glob i -> i64_glob i' -> (i < i')%N.
Proof.
  cbn.
  intros ?? [?|[?|[?|[?|?]]]] [?|[?|[?|[?|?]]]];
    cbv delta in * |-; subst; lia.
Qed.


Lemma update_global_preserves_globals_all_mut : forall sr sr' i f num,
  NoDup (inst_globals (f_inst f)) ->
  ((i32_glob i /\ typeof_num num = T_i32) \/ (i64_glob i /\ typeof_num num = T_i64)) ->
  globals_all_mut sr f ->
  supdate_glob sr (f_inst f) i (VAL_num num) = Some sr' ->
  globals_all_mut sr' f.
Proof.
  intros ????? Hnodup Hi Hmut Hupd.
  unfold globals_all_mut, globals_all_mut32, globals_all_mut64 in *.
  destruct Hmut as [Hmut32 Hmut64].
  unfold supdate_glob, supdate_glob_s, sglob_ind in Hupd.
  destruct Hi as [[Hi Hi32] | [Hi Hi64]];
    split; intros ??? Hgidx Hinstglobs Hstoreglobs.
  2: { (* absurd case *)
    have H := globs_disjoint _ _ Hi Hgidx.
    destruct (lookup_N (inst_globals (f_inst f)) i) eqn:Heqn=>//. cbn in Hupd.
    destruct (lookup_N (s_globals sr) g1) eqn:Heqn'=>//. inv Hupd.
    cbn in Hstoreglobs. unfold lookup_N in *.
    erewrite set_nth_nth_error_other in Hstoreglobs; eauto;
      last now apply nth_error_Some.
    intro Hcontra. apply N2Nat.inj in Hcontra. subst g1.
    rewrite <- Heqn in Hinstglobs.
    eapply NoDup_nth_error in Hinstglobs; eauto; try lia.
    now apply nth_error_Some. }
  2: { (* absurd case *)
    have H := globs_disjoint _ _ Hgidx Hi.
    destruct (lookup_N (inst_globals (f_inst f)) i) eqn:Heqn=>//. cbn in Hupd.
    destruct (lookup_N (s_globals sr) g1) eqn:Heqn'=>//. inv Hupd.
    cbn in Hstoreglobs. unfold lookup_N in *.
    erewrite set_nth_nth_error_other in Hstoreglobs; eauto;
      last now apply nth_error_Some.
    intro Hcontra. apply N2Nat.inj in Hcontra. subst g1.
    rewrite <- Heqn in Hinstglobs.
    eapply NoDup_nth_error in Hinstglobs; eauto; try lia.
    now apply nth_error_Some. }

  all: destruct (lookup_N (inst_globals (f_inst f)) i) eqn:Heqn; last now inv Hupd.
  all: cbn in Hupd; destruct (lookup_N (s_globals sr) g1) eqn:Heqn'=>//.
  all: inv Hupd; cbn in Hstoreglobs; destruct (N.lt_total g g1) as [Heq | [Heq | Heq]];
    unfold lookup_N in *.
  (* Discharge cases where the global index is different from the one being updated *)
  1,3,4,6: erewrite set_nth_nth_error_other in Hstoreglobs;
             [eauto | lia | now apply nth_error_Some].

  - (* i32 globals *)
    subst. erewrite set_nth_nth_error_same in Hstoreglobs; eauto. inv Hstoreglobs.
    destruct num; unfold typeof_num in Hi32; try discriminate.
    assert (g2.(g_type) = {| tg_mut := MUT_var; tg_t := T_num T_i32 |}). {
      apply Hmut32 with (gidx:=i) in Heqn'; auto. destruct Heqn'. now subst. }
    now rewrite H.
  - (* i64 globals *)
    subst. erewrite set_nth_nth_error_same in Hstoreglobs; eauto. inv Hstoreglobs.
    destruct num; unfold typeof_num in Hi64; try discriminate.
    assert (g2.(g_type) = {| tg_mut := MUT_var; tg_t := T_num T_i64 |}). {
      apply Hmut64 with (gidx:=i) in Heqn'; auto. destruct Heqn'. now subst. }
    now rewrite H.
Qed.


Lemma update_global_preserves_global_var_w : forall i j sr sr' f num,
  global_var_w i sr f ->
  supdate_glob sr (f_inst f) j (VAL_num num) = Some sr' ->
  global_var_w i sr' f.
Proof.
  intros ? ? ? ? ? ? HG. unfold global_var_w. intro. unfold global_var_w in HG.
  unfold supdate_glob, supdate_glob_s, sglob_ind in *.
  destruct (lookup_N (inst_globals (f_inst f)) i) eqn:Heqn=>//.
  specialize HG with num. cbn in HG.
  destruct (lookup_N (s_globals sr) g) eqn:Heqn'. 2:{ now destruct HG. }
  destruct HG as [? _].
  destruct (lookup_N (inst_globals (f_inst f)) j) eqn:Heqn''=>//. cbn in H.
  destruct (lookup_N (s_globals sr) g1) eqn:Heqn'''=>//. inv H. cbn.
  destruct (lookup_N (set_nth _ (s_globals sr) _ _)) eqn:Heqn''''; cbn; eauto.
  exfalso. unfold lookup_N in *.
  apply nth_error_Some in Heqn''''=>//.
  erewrite nth_error_set_nth_length; eauto.
  now apply nth_error_Some.
Qed.

Lemma update_global_preserves_glob_out_of_mem_is_zero : forall i sr sr' f num,
  INV_glob_out_of_mem_is_zero sr f ->
  INV_inst_globals_nodup f ->
  glob_out_of_mem <> i ->
  supdate_glob sr (f_inst f) i (VAL_num num) = Some sr' ->
  INV_glob_out_of_mem_is_zero sr' f.
Proof.
  unfold INV_glob_out_of_mem_is_zero. intros.
  now eapply update_global_get_other.
Qed.

Lemma update_global_preserves_linear_memory : forall j sr sr' f  num,
  INV_linear_memory sr f ->
  supdate_glob sr (f_inst f) j (VAL_num num) = Some sr' ->
  INV_linear_memory sr' f.
Proof.
  intros.
  unfold supdate_glob, sglob_ind, supdate_glob_s in H0.
  destruct (lookup_N (inst_globals (f_inst f))) eqn:Heqn=>//. cbn in H0.
  destruct (lookup_N (s_globals sr) g)=>//.
  now inv H0.
Qed.

Lemma update_global_preserves_num_functions_bounds : forall j sr sr' f  num,
  INV_num_functions_bounds sr f ->
  supdate_glob sr (f_inst f) j (VAL_num num) = Some sr' ->
  INV_num_functions_bounds sr' f.
Proof.
  unfold INV_num_functions_bounds. intros.
  assert (s_funcs sr = s_funcs sr') as Hfuncs. {
    unfold supdate_glob, supdate_glob_s in H0.
    destruct (sglob_ind sr (f_inst f) j)=>//. cbn in H0.
    destruct (lookup_N (s_globals sr) g)=>//. now inv H0. }
  by rewrite Hfuncs in H.
Qed.

Lemma update_global_preserves_glob_mem_ptr_in_linear_memory : forall j sr sr' f m num,
  INV_glob_mem_ptr_in_linear_memory sr f ->
  INV_inst_globals_nodup f ->
  smem sr (f_inst f) = Some m ->
  (j = glob_mem_ptr ->
   forall n, num = VAL_int32 (N_to_i32 n) /\ (-1 < Z.of_N n < Wasm_int.Int32.modulus)%Z -> n + 8 <= mem_length m)%N ->
  supdate_glob sr (f_inst f) j (VAL_num num) = Some sr' ->
  INV_glob_mem_ptr_in_linear_memory sr' f.
Proof.
  unfold INV_glob_mem_ptr_in_linear_memory.
  intros ?????? Hinv Hnodup Hmem  Hcond Hupd ?? Hm Hglob Hunbound.
  assert (m = m0). { now apply update_global_preserves_memory in Hupd. }
  subst m0. destruct (N.eq_dec j glob_mem_ptr).
  - (* g = glob_mem_ptr *)
     have H' := update_global_get_same _ _ _ _ _ Hupd.
     specialize (Hcond e).
     rewrite -e in Hglob. rewrite H' in Hglob. inv Hglob.
     specialize (Hcond gmp_v (conj Logic.eq_refl Hunbound)).
     lia.
  - (* g <> glob_mem_ptr *)
    assert (Hgmp_r : sglob_val sr (f_inst f) glob_mem_ptr = Some (VAL_num (VAL_int32 (N_to_i32 gmp_v)))). {
      unfold sglob_val, sglob, sglob_ind in Hglob |- *.
      destruct (lookup_N (inst_globals (f_inst f)) glob_mem_ptr) eqn:Heqn=>//.
      cbn in Hglob.
      destruct (lookup_N (s_globals sr') g) eqn:Heqn'; inv Hglob. cbn.
      unfold supdate_glob, supdate_glob_s, sglob_ind in Hupd.
      destruct (lookup_N (inst_globals (f_inst f)) j) eqn:Heqn''. 2: inv Hupd.
      cbn in Hupd. destruct (lookup_N (s_globals sr) g1) eqn:Heqn'''; inv Hupd.
      cbn in Heqn'. unfold lookup_N in *.
      erewrite set_nth_nth_error_other in Heqn'; eauto.
      + now rewrite Heqn'.
      + intro. assert (g = g1) by lia. subst g1.
        apply n. apply N2Nat.inj.
        eapply NoDup_nth_error; eauto; last congruence.
        now apply nth_error_Some.
      + now apply nth_error_Some. }
    auto.
Qed.

Lemma update_global_preserves_table_id : forall j sr sr' f m num,
  INV_table_id sr f ->
  INV_inst_globals_nodup f ->
  smem sr (f_inst f) = Some m ->
  supdate_glob sr (f_inst f) j (VAL_num num) = Some sr' ->
  INV_table_id sr' f.
Proof.
  unfold INV_table_id, stab_elem. intros.
  apply H in H3.
  destruct (inst_tables (f_inst f)). inv H3. rewrite -H3.
  unfold supdate_glob, supdate_glob_s in H2.
  destruct (sglob_ind sr (f_inst f) j). 2: inv H2.
  cbn in H2. destruct (lookup_N (s_globals sr) g)=>//; inv H2.
  reflexivity.
Qed.

Lemma update_global_preserves_types : forall j sr sr' f m num,
  INV_types f ->
  INV_inst_globals_nodup f ->
  smem sr (f_inst f) = Some m ->
  supdate_glob sr (f_inst f) j (VAL_num num) = Some sr' ->
  INV_types f.
Proof.
  unfold INV_types, stab_elem. intros.
  apply H in H3. now rewrite -H3.
Qed.


Lemma update_global_preserves_glob_mem_ptr_multiple_of_two : forall j sr sr' f m num,
  INV_glob_mem_ptr_multiple_of_two sr f ->
  INV_inst_globals_nodup f ->
  smem sr (f_inst f) = Some m ->
  (j = glob_mem_ptr -> forall n,
      num = VAL_int32 (N_to_i32 n) /\ (-1 < Z.of_N n < Wasm_int.Int32.modulus)%Z -> exists n', n = 2  * n')%N ->
  supdate_glob sr (f_inst f) j (VAL_num num) = Some sr' ->
  INV_glob_mem_ptr_multiple_of_two sr' f.
Proof.
  unfold INV_glob_mem_ptr_multiple_of_two.
  intros j sr sr' f m num. intros Hinv Hnodups Hnth Hj Hupd.
  intros gmp_v m0 ? Hglob Hrange'.
  assert (m = m0). { now apply update_global_preserves_memory in Hupd. } subst m0.
  destruct (N.eq_dec j glob_mem_ptr).
  - (* g = glob_mem_ptr *)
    have H' := update_global_get_same _ _ _ _ _ Hupd.
    subst j.
    rewrite H' in Hglob. injection Hglob as Hglob.
    now destruct (Hj Logic.eq_refl gmp_v (conj Hglob Hrange')).
  - (* g <> glob_mem_ptr *)
    assert (Hgmp_r : sglob_val sr (f_inst f) glob_mem_ptr = Some (VAL_num (VAL_int32 (N_to_i32 gmp_v)))). {
      unfold sglob_val, sglob, sglob_ind in Hglob.
      unfold sglob_val, sglob, sglob_ind.
      destruct (lookup_N (inst_globals (f_inst f)) glob_mem_ptr) eqn:Heqn=>//.
      cbn in Hglob.
      destruct (lookup_N (s_globals sr') g) eqn:Heqn'; inv Hglob. cbn.
      unfold supdate_glob, supdate_glob_s, sglob_ind in Hupd.
      destruct (lookup_N (inst_globals (f_inst f)) j) eqn:Heqn''. 2: inv Hupd.
      cbn in Hupd. destruct (lookup_N (s_globals sr) g1) eqn:Heqn'''; inv Hupd.
      cbn in Heqn'. unfold lookup_N in *.
      erewrite set_nth_nth_error_other in Heqn'; eauto.
      + now rewrite Heqn'.
      + intro. assert (g = g1) by lia. subst g1. apply n.
        apply N2Nat.inj. eapply NoDup_nth_error; eauto; last congruence.
        now apply nth_error_Some. now apply nth_error_Some. }
    eauto.
Qed.

Lemma update_global_preserves_inst_funcs_id : forall j sr sr' fr f  num,
  INV_inst_funcs_id sr fr ->
  supdate_glob sr (f_inst f) j (VAL_num num) = Some sr' ->
  INV_inst_funcs_id sr' fr.
Proof.
  unfold INV_inst_funcs_id. intros.
  assert (s_funcs sr = s_funcs sr') as Hfuncs. {
    unfold supdate_glob, supdate_glob_s in H0.
    destruct (sglob_ind sr (f_inst f) j). 2:inv H0. cbn in H0.
    destruct (lookup_N (s_globals sr) g). 2: inv H0. inv H0. reflexivity. }
  rewrite Hfuncs in H. by apply H.
Qed.

Lemma update_global_preserves_i64_glob_tmps_writable : forall j sr sr' fr num,
  INV_i64_glob_tmps_writable sr fr ->
  supdate_glob sr (f_inst fr) j (VAL_num num) = Some sr' ->
  INV_i64_glob_tmps_writable sr' fr.
Proof.
  unfold INV_i64_glob_tmps_writable. intros.
  now eapply update_global_preserves_global_var_w.
Qed.


Corollary update_global_preserves_INV : forall sr sr' i f m num,
  (i32_glob i /\ typeof_num num = T_i32) \/ (i64_glob i /\ typeof_num num = T_i64) ->
  INV sr f ->
  (* if glob_out_of_mem is set (to 1), INV doesn't need to hold anymore *)
  glob_out_of_mem <> i ->
  (* if updated gmp, new value in mem *)
  smem sr (f_inst f) = Some m ->
  (i = glob_mem_ptr -> forall n, num = VAL_int32 (N_to_i32 n) /\ (-1 < Z.of_N n < Wasm_int.Int32.modulus)%Z -> n + 8 <= mem_length m)%N ->
  (i = glob_mem_ptr -> forall n, num = VAL_int32 (N_to_i32 n) /\ (-1 < Z.of_N n < Wasm_int.Int32.modulus)%Z -> exists n', n = 2  * n')%N ->
  supdate_glob sr (f_inst f) i (VAL_num num) = Some sr' ->
  INV sr' f.
Proof with eassumption.
  intros. unfold INV. destruct H0 as [?[?[?[?[?[?[?[?[?[?[?[?[?[?[??]]]]]]]]]]]]]]].
  split. eapply update_global_preserves_global_var_w...
  split. eapply update_global_preserves_global_var_w...
  split. eapply update_global_preserves_glob_out_of_mem_is_zero...
  split. eapply update_global_preserves_global_var_w...
  split. eapply update_global_preserves_global_var_w...
  split. eapply update_global_preserves_globals_all_mut...
  split. eapply update_global_preserves_linear_memory...
  split. eapply update_global_preserves_glob_mem_ptr_in_linear_memory...
  split. assumption.
  split. eapply update_global_preserves_num_functions_bounds...
  split. assumption.
  split. eapply update_global_preserves_table_id...
  split. eapply update_global_preserves_types...
  split. eapply update_global_preserves_glob_mem_ptr_multiple_of_two with (sr:=sr); eauto.
  split. eapply update_global_preserves_inst_funcs_id...
  eapply update_global_preserves_i64_glob_tmps_writable...
Qed.

Corollary update_local_preserves_INV : forall sr f f' x' v,
  INV sr f ->
  x' < length (f_locs f) ->
  f' = {| f_locs := set_nth (VAL_num (VAL_int32 v)) (f_locs f) x' (VAL_num (VAL_int32 v))
        ; f_inst := f_inst f
        |} ->
  INV sr f'.
Proof with eauto.
  intros. unfold INV. destruct H as [?[?[?[?[?[?[?[?[?[?[??]]]]]]]]]]]. subst.
  repeat (split; auto).
  unfold INV_locals_all_i32 in *. cbn. intros.
  destruct (Nat.eq_dec x' i).
  - (* i=x' *)
    subst. apply nth_error_Some in H0. apply notNone_Some in H0. destruct H0.
    erewrite set_nth_nth_error_same in H1; eauto. now inv H1.
  - (* i<>x' *)
    now rewrite set_nth_nth_error_other in H1.
Qed.

Corollary change_locals_preserves_INV : forall sr f f' l,
  INV sr f ->
  INV_locals_all_i32 f' ->
  f' = {| f_locs := l
        ; f_inst := f_inst f
        |} ->
  INV sr f'.
Proof with eauto.
  intros. unfold INV.
  destruct H as [?[?[?[?[?[?[?[?[?[?[?[?[?[?[??]]]]]]]]]]]]]]]. subst.
  repeat (split; auto).
Qed.

Corollary init_locals_preserves_INV : forall sr f f' args n,
  INV sr f ->
  f' = {| f_locs := [seq (VAL_num (N_to_value a)) | a <- args] ++ repeat (VAL_num (nat_to_value 0)) n
        ; f_inst := f_inst f
        |} ->
  INV sr f'.
Proof with eauto.
  intros. subst.
  eapply change_locals_preserves_INV; eauto.
  unfold INV_locals_all_i32 in *. cbn. intros.
  destruct (Nat.ltb_spec i (length args)).
  - (* i < length args *)
    rewrite nth_error_app1 in H0. 2: {
       now rewrite length_is_size size_map -length_is_size. }
    apply nth_error_In in H0.
    apply in_map_iff in H0. now destruct H0 as [x [Heq Hin]].
  - (* i >= length args *)
    assert (Hlen: i < length ([seq (VAL_num (N_to_value a)) | a <- args]
                                        ++ repeat (VAL_num (nat_to_value 0)) n)). {
      apply nth_error_Some. congruence. }
    rewrite length_app length_is_size size_map -length_is_size repeat_length in Hlen.
    rewrite nth_error_app2 in H0. 2: {
      now rewrite length_is_size size_map -length_is_size. }
    have H' := H0.
    rewrite nth_error_repeat in H'.
    2: { rewrite length_is_size size_map -length_is_size. lia. }
    inv H'. eexists. reflexivity.
Qed.

(* writable implies readable *)
Lemma global_var_w_implies_global_var_r : forall (s : store_record) fr var,
  i32_glob var \/ i64_glob var ->
  globals_all_mut s fr ->
  global_var_w var s fr ->
  global_var_r var s fr.
Proof.
  intros s fr i Hi Hmut GVW.
  destruct Hi as [Hi32 | Hi64].
  unfold global_var_w, global_var_r, supdate_glob, sglob_val, sglob, sglob_ind in GVW |- *. cbn in GVW |- *.
  destruct GVW with (val:=Z_to_value 42).
  unfold global_var_r, sglob_val, sglob, sglob_ind.
  destruct ((lookup_N (inst_globals (f_inst fr)) i)) eqn:Hv. 2: inv H.
  cbn in H. cbn. unfold supdate_glob_s in H.
  destruct (lookup_N (s_globals s) g) eqn:Hg=>//.
  inv H.
  destruct Hmut as [Hmut32 _].
  apply (Hmut32 i g g0 Hi32 Hv) in Hg.
  destruct Hg.
  inv H. eexists.
  reflexivity.
  unfold global_var_w, global_var_r, supdate_glob, sglob_val, sglob, sglob_ind in GVW |- *.
  cbn in GVW |- *.
  destruct GVW with (val:=Z_to_value 42).
  unfold global_var_r, sglob_val, sglob, sglob_ind.
  destruct ((lookup_N (inst_globals (f_inst fr)) i)) eqn:Hv. 2: inv H.
  cbn in H. cbn. unfold supdate_glob_s in H.
  destruct (lookup_N (s_globals s) g) eqn:Hg=>//. cbn.
  inv H.
  destruct Hmut as [_ Hmut64].
  apply (Hmut64 i g g0 Hi64 Hv) in Hg as [? Hg].
  inv Hg. now eexists.
Qed.

Lemma update_mem_preserves_global_var_w : forall i s f s' m vd,
  global_var_w i s f ->
  upd_s_mem s (set_nth vd (s_mems s) 0 m) = s' ->
  global_var_w i s' f.
Proof.
  intros.
  unfold global_var_w.
  intros. unfold upd_s_mem in H0. subst. destruct H with (val:=val).
  unfold supdate_glob, sglob_ind, supdate_glob_s in *. cbn in *.
  destruct (lookup_N (inst_globals (f_inst f)) i). 2: inv H0. cbn in *.
  destruct (lookup_N (s_globals s) g). 2: inv H0. now cbn in *.
Qed.

Lemma update_mem_preserves_glob_out_of_mem_is_zero : forall s f s' m vd,
  INV_glob_out_of_mem_is_zero s f ->
  upd_s_mem s (set_nth vd (s_mems s) 0 m) = s' ->
  INV_glob_out_of_mem_is_zero s' f.
Proof.
  unfold INV_glob_out_of_mem_is_zero, sglob_val, sglob, sglob_ind, nat_to_i32.
  intros. subst. cbn in *.
  destruct (inst_globals (f_inst f)). inv H.
  destruct l. inv H.
  destruct l. inv H.
  now destruct l.
Qed.

Lemma update_mem_preserves_all_mut : forall s s' f m vd,
  globals_all_mut s f ->
  upd_s_mem s (set_nth vd (s_mems s) 0 m) = s' ->
  globals_all_mut s' f.
Proof.
  unfold globals_all_mut, globals_all_mut32, globals_all_mut64, upd_s_mem. intros.
  assert (s_globals s = s_globals s') as Hglob. {
   subst. destruct s. reflexivity. }
  destruct H as [Hmut32 Hmut64].
  split.
  - rewrite Hglob in Hmut32; eapply Hmut32; eauto.
  - rewrite Hglob in Hmut64; eapply Hmut64; eauto.
Qed.

Lemma update_mem_preserves_linear_memory : forall s s' f m vd,
  INV_linear_memory s f  ->
  m.(meminst_type).(lim_max) = Some max_mem_pages ->
  (exists size, mem_size m = size /\ size <= max_mem_pages)%N ->
  upd_s_mem s (set_nth vd (s_mems s) 0 m) = s' ->
  INV_linear_memory s' f.
Proof.
  unfold INV_linear_memory.
  intros s s' f m m' [H1 [m'' [H2 [size [H3 H4]]]]] H' [size' [H6 H7]] H8.
  split =>//.
  exists m.
  split; eauto. subst.
  unfold smem. rewrite H1.
  now destruct (s_mems s).
Qed.

Lemma update_mem_preserves_glob_mem_ptr_in_linear_memory : forall s s' f m m',
  INV_glob_mem_ptr_in_linear_memory s f ->
  INV_glob_mem_ptr_writable s f ->
  INV_globals_all_mut s f ->
  smem s (f_inst f) = Some m ->
  inst_mems (f_inst f) = [0%N] ->
  (mem_length m' >= mem_length m)%N ->
  upd_s_mem s (set_nth m' (s_mems s) 0 m') = s' ->
  INV_glob_mem_ptr_in_linear_memory s' f.
Proof.
  unfold INV_glob_mem_ptr_in_linear_memory.
  intros ????? H Hinv Hinv' ?????????. subst.
  unfold smem in *.
  destruct (s_mems s) eqn:Hm'.
  { rewrite -> H0 in *. destruct (lookup_N _ _)=>//.
    unfold lookup_N in *. now destruct (N.to_nat m1). }
  eapply update_mem_preserves_global_var_w in Hinv; eauto.
  apply global_var_w_implies_global_var_r in Hinv.
  assert (gmp_v + 8 <= mem_length m)%N. { unfold smem in *. apply H; auto. }
  cbn in H4. rewrite H1 in H4. inv H4. lia.
  left. now cbn.
  eapply update_mem_preserves_all_mut; eauto.
  Unshelve. assumption. assumption.
Qed.

Lemma update_mem_preserves_global_glob_cap_in_linear_memory : forall s s' f m m' vd,
  INV_glob_cap_in_linear_memory s f  ->
  INV_glob_cap_writable s f ->
  INV_globals_all_mut s f ->
  smem s (f_inst f) = Some m ->
  (mem_length m' >= mem_length m)%N ->
  upd_s_mem s (set_nth vd (s_mems s) 0 m') = s' ->
  INV_glob_cap_in_linear_memory s' f.
Proof.
  unfold INV_glob_cap_in_linear_memory.
  intros ? ? ? ? ? ? H Hinv Hinv' ? ? ? ? ? ? ?.
  eapply update_mem_preserves_global_var_w in Hinv; eauto.
  apply global_var_w_implies_global_var_r in Hinv.
  unfold global_var_r in Hinv. destruct Hinv as [v Hv].
  rewrite H3 in Hv. inv Hv.
  eapply H in H3; eauto.
  now cbn.
  now eapply update_mem_preserves_all_mut.
Qed.

Lemma update_mem_preserves_num_functions_bounds : forall s s' f m vd,
  INV_num_functions_bounds s f ->
  upd_s_mem s (set_nth vd (s_mems s) 0 m) = s' ->
  INV_num_functions_bounds s' f.
Proof.
  unfold INV_num_functions_bounds.
  intros. subst. assumption.
Qed.

Lemma update_mem_preserves_table_id : forall s s' f m vd,
  INV_table_id s f ->
  upd_s_mem s (set_nth vd (s_mems s) 0 m) = s' ->
  INV_table_id s' f.
Proof.
  unfold INV_table_id.
  intros. now subst.
Qed.

Lemma update_mem_preserves_types : forall s s' f m vd,
  INV_types f ->
  upd_s_mem s (set_nth vd (s_mems s) 0 m) = s' ->
  INV_types f.
Proof.
  unfold INV_types. intros. subst. auto.
Qed.

Lemma update_mem_preserves_fvar_idx_inbounds : forall s s' m vd,
  INV_fvar_idx_inbounds s ->
  upd_s_mem s (set_nth vd (s_mems s) 0 m) = s' ->
  INV_fvar_idx_inbounds s'.
Proof.
  unfold INV_fvar_idx_inbounds. intros. subst. eauto.
Qed.

Lemma update_mem_preserves_glob_mem_ptr_multiple_of_two : forall s s' f m m' vd,
  INV_glob_mem_ptr_multiple_of_two s f ->
  smem s (f_inst f)  = Some m ->
  upd_s_mem s (set_nth vd (s_mems s) 0 m') = s' ->
  INV_glob_mem_ptr_multiple_of_two s' f.
Proof.
  unfold INV_glob_mem_ptr_multiple_of_two.
  intros. now subst.
Qed.

Lemma update_mem_preserves_inst_funcs_id : forall s s' f m vd,
  INV_inst_funcs_id s f ->
  upd_s_mem s (set_nth vd (s_mems s) 0 m) = s' ->
  INV_inst_funcs_id s' f.
Proof.
  unfold INV_inst_funcs_id.
  intros. now subst.
Qed.

Corollary update_mem_preserves_INV : forall s s' f m m' vd,
  INV s f ->
  smem s (f_inst f) = Some m ->
  (mem_length m' >= mem_length m)%N ->
  m'.(meminst_type).(lim_max) = Some max_mem_pages ->
  (exists size, mem_size m' = size /\ size <= max_mem_pages)%N ->
  upd_s_mem s (set_nth vd (s_mems s) 0 m') = s' ->
  INV s' f.
Proof with eassumption.
  intros. unfold INV.
  destruct H as [?[?[?[?[?[?[?[?[?[?[?[?[?[?[??]]]]]]]]]]]]]]].
  split. eapply update_mem_preserves_global_var_w...
  split. eapply update_mem_preserves_global_var_w...
  split. eapply update_mem_preserves_glob_out_of_mem_is_zero...
  split. eapply update_mem_preserves_global_var_w...
  split. eapply update_mem_preserves_global_var_w...
  split. eapply update_mem_preserves_all_mut...
  split. eapply update_mem_preserves_linear_memory...
  split. eapply update_mem_preserves_glob_mem_ptr_in_linear_memory; eauto. apply H10.
  split. assumption.
  split. eapply update_mem_preserves_num_functions_bounds...
  split. assumption.
  split. eapply update_mem_preserves_table_id...
  split. eapply update_mem_preserves_types...
  split. eapply update_mem_preserves_glob_mem_ptr_multiple_of_two...
  split. eapply update_mem_preserves_inst_funcs_id...
  unfold INV_i64_glob_tmps_writable. intros. now eapply update_mem_preserves_global_var_w.
Qed.

Corollary smem_grow_preserves_INV : forall sr sr' fr bytes size,
  INV sr fr ->
  smem_grow sr (f_inst fr) bytes = Some (sr', size) ->
  INV sr' fr.
Proof.
  intros ????? Hinv Hgrow.
  have I := Hinv. destruct I as [_ [INVresM_w [_ [INVgmp_w [INVcap_w [INVmuti32 [INVlinmem [HgmpInM [? [? [HglobNodup _]]]]]]]]]]].
  have I := INVlinmem. destruct I as [Hm1 [m [Hm2 [size' [Hm3 [Hm4 Hm5]]]]]].
  unfold smem_grow, smem in Hgrow, Hm2.
  rewrite Hm1 in Hgrow, Hm2. cbn in Hgrow, Hm2. rewrite Hm2 in Hgrow.
  destruct (mem_grow m bytes) eqn:Hgrow'=>//. inv Hgrow.
  eapply update_mem_preserves_INV with (m:=m) (m':=m0); eauto.
  - unfold smem. rewrite Hm1 Hm2. reflexivity.
  - apply LambdaANF_to_Wasm_utils.mem_grow_length in Hgrow'. lia.
  - erewrite mem_grow_lim_max; eauto.
  - exists (mem_size m0). split=>//.
    have Hgrow := Hgrow'.
    unfold mem_grow in Hgrow'.
    destruct ((mem_size m + bytes <=? mem_limit_bound)%N)=>//.
    rewrite Hm4 in Hgrow'.
    destruct (memory.mem_grow _ _) eqn:Hsize=>//.
    destruct ((mem_size m + bytes <=? max_mem_pages)%N) eqn:Hsize' =>//.  inv Hgrow'.
    apply LambdaANF_to_Wasm_utils.mem_grow_mem_size in Hgrow.
    rewrite Hgrow.
    lia.
Qed.

Lemma value_bounds : forall wal v sr fr,
  INV_num_functions_bounds sr fr ->
  repr_val_LambdaANF_Wasm v sr (f_inst fr) wal ->
  (-1 < Z.of_N (wasm_value_to_u32 wal) < Wasm_int.Int32.modulus)%Z.
Proof.
  intros ? ? ? ? [Hbound1 Hbound2] H.
  inv H.
  - (* constr. value unboxed *) cbn. lia.
  - (* constr. value boxed *) cbn. lia.
  - (* function value *)
    cbn.
    assert (N.to_nat idx < length (s_funcs sr)). {
      apply nth_error_Some. unfold lookup_N in *. congruence. }
    unfold INV_num_functions_bounds in Hbound1.
    unfold max_num_functions, num_custom_funs in *. simpl_modulus. cbn. lia.
  - (* prim. value boxed *) cbn. lia.
Qed.

Lemma extract_constr_arg : forall n vs v sr fr addr m,
  INV_num_functions_bounds sr fr ->
  nthN vs n = Some v ->
  smem sr (f_inst fr) = Some m ->
  (* addr points to the first arg after the constructor tag *)
  repr_val_constr_args_LambdaANF_Wasm vs sr (f_inst fr) addr ->
  exists bs wal, load m (addr + 4 * n)%N 0%N 4 = Some bs /\
             VAL_int32 (wasm_value_to_i32 wal) = wasm_deserialise bs T_i32 /\
             repr_val_LambdaANF_Wasm v sr (f_inst fr) wal.
Proof.
  intros n vs v sr fr addr m Hinv H H1 H2. generalize dependent v.
  generalize dependent n. generalize dependent m. remember (f_inst fr) as inst.
  generalize dependent fr.
  induction H2; intros; subst. 1: inv H.
  generalize dependent v0.
  induction n using N.peano_ind; intros.
  - (* n = 0 *)
    inv H7. assert (m = m0) by congruence. subst m0. rewrite N.add_comm. unfold load_i32 in H3.
    destruct (load m addr 0%N 4) eqn:Hl; inv H3. exists b, wal.
    repeat split; auto.
    unfold wasm_value_to_i32.
    have H'' := value_bounds wal.
    unfold wasm_deserialise. f_equal. f_equal.
    have H' := decode_int32_bounds _ _ _ Hl. simpl_eq.
    rewrite Wasm_int.Int32.Z_mod_modulus_id in H8; auto.
    eapply value_bounds; eauto.
  - (* n = succ n0 *)
    cbn in H7.
    destruct (N.succ n) eqn:Hn; first by lia. rewrite <-Hn in *.
    replace (N.succ n - 1)%N with n in H7 by lia. clear Hn p.
    edestruct IHrepr_val_constr_args_LambdaANF_Wasm; eauto.
    destruct H8 as [wal' [Hl [Heq Hval]]].
    exists x, wal'. repeat split; auto.
    rewrite -Hl. f_equal. lia.
Qed.

Lemma memory_grow : forall m sr fr,
  smem sr (f_inst fr) = Some m ->
     (exists s' old_size, smem_grow sr (f_inst fr) 1 = Some (s', old_size)
     /\ mem_size m + 1 <= mem_limit_bound)%N
  \/ (smem_grow sr (f_inst fr) 1 = None).
Proof.
  intros m sr fr H. unfold smem_grow, mem_grow.
  have Hm := H. unfold smem in H.
  destruct (lookup_N (inst_mems (f_inst fr)) 0) eqn:H'=>//.
  rewrite H.
  destruct (mem_size m + 1 <=? mem_limit_bound)%N eqn:Hlim; eauto.
  destruct (memory.mem_grow (1 * page_size) (meminst_data m)); eauto.
  destruct (lim_max (meminst_type m)).
  - (* lim_max *)
    destruct (mem_size m + 1 <=? u)%N; eauto.
    left. do 3 eexists; eauto. lia.
  - (* no lim_max *)
    left. do 3 eexists; eauto. lia.
Qed.


(* statically known available memory (minimum) *)
Definition min_available_memory (sr : store_record) (inst : moduleinst) (bytes : N) :=
  forall m gmp,
  smem sr inst = Some m ->
  sglob_val sr inst glob_mem_ptr = Some (VAL_num (VAL_int32 (N_to_i32 gmp))) ->
  (-1 < Z.of_N gmp < Wasm_int.Int32.modulus)%Z ->
  (gmp + bytes < mem_length m)%N.


Lemma memory_grow_reduce_check_grow_mem : forall state sr fr gmp m,
  INV sr fr ->
  (* need more memory *)
  sglob_val sr (f_inst fr) glob_mem_ptr = Some (VAL_num (VAL_int32 (N_to_i32 gmp))) ->
  smem sr (f_inst fr) = Some m ->
  (-1 < Z.of_N gmp < Wasm_int.Int32.modulus)%Z ->
  ~~ Wasm_int.Int32.lt
       (Wasm_int.Int32.repr
          (Wasm_int.Int32.signed
             (Wasm_int.Int32.iadd (N_to_i32 gmp)
                (N_to_i32 page_size)) ÷ 65536))
       (Wasm_int.Int32.repr (Z.of_N (mem_size m))) = true ->

   (exists sr', reduce_trans
   (state, sr, fr, [seq AI_basic i | i <- grow_memory_if_necessary])
   (state, sr', fr, [])
   /\ s_funcs sr = s_funcs sr'
   /\ (forall wal val, repr_val_LambdaANF_Wasm val sr (f_inst fr) wal ->
                       repr_val_LambdaANF_Wasm val sr' (f_inst fr) wal)
   (* enough memory to alloc. constructor *)
   /\ INV sr' fr /\
      (forall m, smem sr' (f_inst fr) = Some m ->
          sglob_val sr' (f_inst fr) glob_mem_ptr = Some (VAL_num (VAL_int32 (N_to_i32 gmp))) /\
          (Z.of_N gmp + Z.of_N page_size < Z.of_N (mem_length m))%Z)
  ) \/
  (* ran out of memory *)
  (forall k (lh: lholed k),
  exists sr' k' (lh': lholed k'),
    reduce_trans
      (state, sr,  fr, (lfill lh (map AI_basic grow_memory_if_necessary)))
      (state, sr', fr, (lfill lh' [::AI_basic BI_return]))
   /\ s_funcs sr = s_funcs sr'
   /\ (forall wal val, repr_val_LambdaANF_Wasm val sr (f_inst fr) wal ->
                       repr_val_LambdaANF_Wasm val sr' (f_inst fr) wal)
   /\ (sglob_val sr' (f_inst fr) glob_out_of_mem = Some (VAL_num (VAL_int32 (nat_to_i32 1))))).
Proof.
  (* grow memory if necessary *)
  intros state sr fr gmp m Hinv Hgmp Hm HgmpBound HneedMoreMem.
  unfold grow_memory_if_necessary. cbn. have I := Hinv.
  destruct I as [_ [INVresM_w [_ [INVgmp_w [INVcap_w [INVmuti32 [INVlinmem [HgmpInM [? [? [HglobNodup HinvRest]]]]]]]]]]].
  have I := INVlinmem. destruct I as [Hm1 [m' [Hm2 [size [Hm3 [Hm4 Hm5]]]]]].
  assert (m = m') by congruence. subst m'.

  assert (global_var_r glob_mem_ptr sr fr) as H2. {
    apply global_var_w_implies_global_var_r; auto. cbn. tauto.
  }
  have H' := HgmpInM _ _ Hm2 Hgmp HgmpBound.
  (* need to grow memory *)

  have Hgrow := memory_grow _ _ _ Hm2.
  destruct Hgrow as [[s' [size' [Hgrow HgrowSize]]] | HgrowFail].
  { (* grow memory success *)
    left. eexists. split.
    (* load glob_mem_ptr *)
    dostep_nary 0. apply r_global_get. eassumption.
    (* add required bytes *)
    dostep_nary 2. constructor. apply rs_binop_success=>//.
    dostep_nary 2. constructor. apply rs_binop_success=>//. cbn. unfold is_left.
    rewrite zeq_false. reflexivity. now apply div_page_size_neq_i32_half_modulus.
    dostep. apply r_eliml; auto.
    elimr_nary_instr 0. now eapply r_memory_size.
    dostep_nary 2. constructor. apply rs_relop=>//.

    dostep'. constructor. subst.
    rewrite HneedMoreMem. apply rs_if_true. intro H3'. inv H3'.

    dostep'. eapply r_block with (t1s:=[::]) (t2s:=[::])(vs:=[::]); auto.
    cbn. eapply rt_trans. apply reduce_trans_label0.
    dostep_nary 1. eapply r_memory_grow_success. apply Hgrow.
    dostep_nary 2. constructor. apply rs_relop=>//. cbn.
    dostep'. constructor. apply rs_if_false.
    { unfold Int32.eq. cbn. rewrite zeq_false. reflexivity. intro.
      unfold smem, smem_grow in Hgrow, Hm2.
      rewrite Hm1 in Hgrow, Hm2. cbn in Hgrow, Hm2.
      destruct (s_mems sr)=>//. inv Hm2.
      destruct (mem_grow m 1)=>//. inv Hgrow.
      rewrite Wasm_int.Int32.Z_mod_modulus_id in H1.
      unfold mem_limit_bound in HgrowSize. lia.
      unfold mem_limit_bound in HgrowSize. simpl_modulus. cbn. lia. }
    dostep'. eapply r_block with (t1s:=[::]) (t2s:=[::])(vs:=[::]); auto.
    cbn. dostep'. constructor. apply rs_label_const=>//. apply rt_refl.
    dostep'. constructor. apply rs_label_const=>//. apply rt_refl.

    intros. split. eapply smem_grow_funcs; eauto. split.
    { (* value relation preserved *)
      intros.
      unfold smem_grow in Hgrow. rewrite Hm1 in Hgrow, Hm2. cbn in Hgrow.
      destruct (s_mems sr) eqn:Hm'=>//.
      unfold smem in Hm. rewrite Hm1 Hm' in Hm. injection Hm as ->.
      destruct (mem_grow m 1) eqn:Hgrow'=>//. inv Hgrow.
      eapply val_relation_depends_on_mem_smaller_than_gmp_and_funcs. 11: apply H1.
      - reflexivity.
      - unfold smem. rewrite Hm1 Hm'. reflexivity.
      - unfold smem. rewrite Hm1. reflexivity.
      - eassumption.
      - subst. apply mem_length_upper_bound in Hm5; cbn in Hm5. simpl_modulus; cbn.
        apply LambdaANF_to_Wasm_utils.mem_grow_length in Hgrow'. lia.
      - rewrite <- Hgmp. reflexivity.
      - subst. apply mem_length_upper_bound in Hm5; cbn in Hm5.
        apply LambdaANF_to_Wasm_utils.mem_grow_length in Hgrow'. simpl_modulus; cbn; lia.
      - lia.
      - intros. eapply mem_grow_load; eauto; unfold max_mem_pages, page_limit; lia.
      - intros. eapply mem_grow_load; eauto; unfold max_mem_pages, page_limit; lia.
    } split.
    { (* invariant *)
      eapply smem_grow_preserves_INV; eauto. }
    { (* enough memory available *)
      intros. split.
      - erewrite <- smem_grow_sglob_val; eauto.
      - unfold smem, smem_grow in Hgrow, H1, Hm2.
        rewrite Hm1 in H1, Hgrow, Hm2. cbn in H1, Hgrow, Hm2. rewrite Hm2 in Hgrow.
        destruct (mem_grow m 1) eqn:Hgrow'=>//. inv Hgrow. cbn in H1.
        destruct (s_mems sr)=>//. injection Hm2 as ->. injection H1 as ->.
        apply LambdaANF_to_Wasm_utils.mem_grow_length in Hgrow'. lia.
    }
  }

  { (* growing memory fails *)
    edestruct INVresM_w as [sr'' HresM]. right. intros.

    have Hlh := lholed_nested_label2 _ lh [::AI_basic BI_return] [::].
    destruct Hlh as [k' [lh' Hlheq]].

    eexists. exists k', lh'. split.
    eapply rt_trans. apply reduce_trans_label. separate_instr.
    (* load glob_mem_ptr *)
    dostep_nary 0. apply r_global_get. eassumption.
    (* add required bytes *)
    dostep_nary 2. constructor.
    apply rs_binop_success=>//.
    dostep_nary 2. constructor.
    apply rs_binop_success=>//. cbn. unfold is_left.
    rewrite zeq_false. reflexivity. now apply div_page_size_neq_i32_half_modulus.
    dostep. apply r_eliml; auto.
    elimr_nary_instr 0. now eapply r_memory_size.

    dostep_nary 2. constructor. apply rs_relop=>//.

    dostep'. constructor. subst. rewrite HneedMoreMem. apply rs_if_true. discriminate.
    dostep'. eapply r_block with (t1s:=[::]) (t2s:=[::])(vs:=[::]); auto.
    apply reduce_trans_label0.
    dostep_nary 1. eapply r_memory_grow_failure. apply HgrowFail.
    dostep_nary 2. constructor. apply rs_relop=>//. cbn.
    dostep'. constructor. apply rs_if_true. intro Hcontra. inv Hcontra.
    dostep'. eapply r_block with (t1s:=[::]) (t2s:=[::])(vs:=[::]); auto.
    apply reduce_trans_label0. cbn.
    dostep_nary' 1. apply r_global_set'. eassumption. apply rt_refl.
    cbn. rewrite -Hlheq. apply rt_refl.
    (* correct resulting environment *)
    split. eapply update_global_preserves_funcs; eassumption.
    split.
    { (* val relation preserved *)
      intros. subst size.
      have Hlength := mem_length_upper_bound _ Hm5.
      unfold page_size, max_mem_pages in Hlength. cbn in Hlength.
      eapply val_relation_depends_on_mem_smaller_than_gmp_and_funcs. 11: apply H1. all: eauto.
      - eapply update_global_preserves_funcs. eassumption.
      - erewrite <- update_global_preserves_memory; eassumption.
      - simpl_modulus. cbn. lia.
      - eapply update_global_get_other; try apply HresM; eauto. now intro.
      - simpl_modulus. cbn. lia.
      - lia.
   }
   intros. eapply update_global_get_same. eassumption. }
Qed.


Lemma memory_grow_reduce_check_enough : forall state sr fr gmp m,
  (* INV only for the properties on s *)
  INV sr fr ->
  sglob_val sr (f_inst fr) glob_mem_ptr = Some (VAL_num (VAL_int32 (N_to_i32 gmp))) ->
  smem sr (f_inst fr) = Some m ->
  (-1 < Z.of_N gmp < Wasm_int.Int32.modulus)%Z ->
  (* already enough memory *)
  ~~ Wasm_int.Int32.lt
       (Wasm_int.Int32.repr
          (Wasm_int.Int32.signed
             (Wasm_int.Int32.iadd (N_to_i32 gmp)
                (N_to_i32 page_size)) ÷ 65536))
       (Wasm_int.Int32.repr (Z.of_N (mem_size m))) = false ->

  (* enough memory (reduction can't run out of memory)*)
  exists sr', reduce_trans
  (state, sr, fr, [seq AI_basic i | i <- grow_memory_if_necessary])
  (state, sr', fr, [])
  /\ s_funcs sr = s_funcs sr'
  /\ (forall wal val, repr_val_LambdaANF_Wasm val sr (f_inst fr) wal ->
                      repr_val_LambdaANF_Wasm val sr' (f_inst fr) wal)
  (* enough memory to alloc. constructor *)
  /\ INV sr' fr /\
     (forall m, smem sr' (f_inst fr) = Some m ->
         sglob_val sr' (f_inst fr) glob_mem_ptr = Some (VAL_num (VAL_int32 (N_to_i32 gmp))) /\
         (Z.of_N gmp + Z.of_N page_size < Z.of_N (mem_length m))%Z).
Proof.
  have _x := Wasm_int.Int32.repr 42. (* witness *)
  (* grow memory if necessary *)
  intros state sr fr gmp m Hinv Hgmp Hm HgmpBound HenoughMem.
  unfold grow_memory_if_necessary. cbn. have I := Hinv.
  destruct I as [_ [INVresM_w [_ [INVgmp_w [INVcap_w [INVmut [INVlinmem [HgmpInM _]]]]]]]].
  have I := INVlinmem. destruct I as [Hm1 [m' [Hm2 [size [Hm3 [Hm4 Hm5]]]]]].
  assert (m' = m) by congruence. subst m'.

  have H' := HgmpInM _ _ Hm2 Hgmp HgmpBound.

  (* enough space already *)
  exists sr. split.
  (* load glob_mem_ptr *)
  dostep_nary 0. apply r_global_get. eassumption.
  (* add required bytes *)
  dostep_nary 2. constructor.
  apply rs_binop_success=>//.
  dostep_nary 2. constructor.
  apply rs_binop_success=>//. cbn. unfold is_left.
  rewrite zeq_false. reflexivity. now apply div_page_size_neq_i32_half_modulus.
  dostep. apply r_eliml; auto.
  elimr_nary_instr 0. now eapply r_memory_size.

  dostep_nary 2. constructor. apply rs_relop=>//.

  dostep'. constructor. subst.
  rewrite HenoughMem. apply rs_if_false. reflexivity.

  dostep'. eapply r_block with (t1s:=[::]) (t2s:=[::])(vs:=[::]); auto. cbn.
  dostep'. constructor. apply rs_label_const=>//. apply rt_refl.
  split. reflexivity. split. auto.
  split. assumption.

  (* enough space *)
  intros. unfold max_mem_pages in *. subst size.
  split. assumption.
  solve_eq m m0.
  unfold Wasm_int.Int32.lt in HenoughMem.
  edestruct (zlt _ _) as [Ha|Ha]. 2: inv HenoughMem. clear HenoughMem.
  unfold Wasm_int.Int32.iadd, Wasm_int.Int32.add in Ha. cbn in Ha.

  rewrite Wasm_int.Int32.Z_mod_modulus_id in Ha. 2: {
    simpl_modulus. cbn.
    apply mem_length_upper_bound in Hm5; cbn in Hm5. lia. }

  remember (Wasm_int.Int32.signed (Wasm_int.Int32.repr (Z.of_N gmp + 65536)) ÷ 65536)%Z as y.
  unfold Wasm_int.Int32.signed, Wasm_int.Int32.unsigned in Heqy.
  have Hlength := mem_length_upper_bound _ Hm5.
  unfold page_size, max_mem_pages in Hlength. cbn in Hlength.

  rewrite zlt_true in Heqy. 2: {
    cbn. rewrite Wasm_int.Int32.Z_mod_modulus_id. lia. simpl_modulus. cbn. lia. }

  unfold Wasm_int.Int32.signed in Heqy. cbn in Heqy.
  rewrite Wasm_int.Int32.Z_mod_modulus_id in Heqy. 2: { simpl_modulus. cbn. lia. }
  cbn in Heqy. replace (Z.of_nat (Pos.to_nat 65536)) with 65536%Z in Heqy by lia.
  rewrite (Z.quot_add (Z.of_N gmp) 1 65536) in Heqy; try lia.

  remember (Wasm_int.Int32.signed
      (Wasm_int.Int32.repr (Z.of_N (mem_size m)))) as n.
  unfold Wasm_int.Int32.signed in Ha.
  subst y. unfold Wasm_int.Int32.signed in Ha. cbn in Ha.

  rewrite Wasm_int.Int32.Z_mod_modulus_id in Ha. 2: {
    simpl_modulus. cbn. lia.
  }

  rewrite small_signed_repr_n_n in Heqn; last by unfold max_mem_pages; lia.
  unfold Wasm_int.Int32.signed in Heqn. cbn in Heqn.

  (* 100000 arbitrary *)
  assert ((Z.of_N gmp ÷ 65536 < 100000)%Z) as H'' by lia.
  rewrite zlt_true in Ha; try lia. subst.
  rewrite N2Z.inj_div in Ha. cbn in Ha. lia.
Qed.

Lemma glob_result_i32_glob : i32_glob glob_result.
Proof. now constructor. Qed.

Lemma glob_out_of_mem_i32_glob : i32_glob glob_out_of_mem.
Proof. now cbn. Qed.

Lemma gmp_i32_glob : i32_glob glob_mem_ptr.
Proof. now cbn. Qed.

Lemma cap_i32_glob : i32_glob glob_cap.
Proof. now cbn. Qed.

Lemma i32_glob_implies_i32_val : forall sr fr gidx,
  i32_glob gidx ->
  global_var_w gidx sr fr ->
  INV_globals_all_mut sr fr ->
  exists v,
    sglob_val sr (f_inst fr) gidx = Some (VAL_num (VAL_int32 v)).
Proof.
  intros ??? Hi32 Hread Hmut.
  destruct (global_var_w_implies_global_var_r sr fr gidx (or_introl Hi32) Hmut Hread) as [v Hv].
  unfold sglob_val, sglob, sglob_ind in Hv |- *.
  destruct (lookup_N (inst_globals (f_inst fr)) gidx) eqn:Hinst_glob. 2: inv Hv.
  destruct (lookup_N (s_globals sr) g) eqn:Hsr_glob. 2: inv Hv.
  destruct Hmut as [Hmut32 _].
  destruct (Hmut32 gidx g g0 Hi32 Hinst_glob Hsr_glob) as [vi32 Hvi32]. inv Hv. inv H0.
  now exists vi32.
Qed.

Lemma memory_grow_reduce : forall state sr fr required_bytes mem grow_mem_instr gmp mem',
  (required_bytes < page_size)%N ->
  min_available_memory sr (f_inst fr) mem ->
  repr_call_grow_mem_if_necessary mem required_bytes mem' grow_mem_instr ->

  (* INV only for the properties on s *)
  INV sr fr ->

  sglob_val sr (f_inst fr) glob_mem_ptr = Some (VAL_num (VAL_int32 (N_to_i32 gmp))) ->
  (-1 < Z.of_N gmp < Wasm_int.Int32.modulus)%Z ->

  (* enough memory *)
  (exists sr', reduce_trans
   (state, sr, fr, [seq AI_basic i | i <- grow_mem_instr])
   (state, sr', fr, [])
   /\ s_funcs sr = s_funcs sr'
   /\ (forall wal val, repr_val_LambdaANF_Wasm val sr (f_inst fr) wal ->
                       repr_val_LambdaANF_Wasm val sr' (f_inst fr) wal)
   (* enough memory to alloc. constructor *)
   /\ INV sr' fr /\
      (forall m, smem sr' (f_inst fr) = Some m ->
          sglob_val sr' (f_inst fr) glob_mem_ptr = Some (VAL_num (VAL_int32 (N_to_i32 gmp))) /\
          (Z.of_N gmp + Z.of_N required_bytes + Z.of_N mem' < Z.of_N (mem_length m))%Z)
  ) \/
  (* ran out of memory *)
  (forall k (lh: lholed k),
  exists sr' k' (lh': lholed k'),
    reduce_trans
      (state, sr,  fr, (lfill lh (map AI_basic grow_mem_instr)))
      (state, sr', fr, (lfill lh' [::AI_basic BI_return]))
   /\ s_funcs sr = s_funcs sr'
   /\ (forall wal val, repr_val_LambdaANF_Wasm val sr (f_inst fr) wal ->
                       repr_val_LambdaANF_Wasm val sr' (f_inst fr) wal)
   /\ (sglob_val sr' (f_inst fr) glob_out_of_mem = Some (VAL_num (VAL_int32 (nat_to_i32 1))))).
Proof.
  (* grow memory if necessary *)
  intros ???????? Hbytes HmemAvail Hgrow Hinv Hgmp HgmpBound.
  inv Hgrow.
  { (* enough memory statically, no check needed *)
    unfold min_available_memory in HmemAvail.
    have I := Hinv. destruct I as [_ [INVresM_w [_ [INVgmp_w [INVcap_w [INVmut [INVlinmem [HgmpInM [? ?]]]]]]]]].
    assert (global_var_r glob_mem_ptr sr fr) as Hgmp_r.
    { apply global_var_w_implies_global_var_r.
      now left; cbn. apply Hinv.
      destruct Hinv as [_[_[_[Hgmp_w _]]]]. assumption. }
    left. exists sr.
    split. apply rt_refl.
    repeat split=>//.
    have H' := HmemAvail _ _ H2 Hgmp HgmpBound. lia.
  }
  { (* needs dynamic check if memory should be grown *)
    have I := Hinv.
    destruct I as [_ [INVresM_w [_ [INVgmp_w [INVcap_w [INVmut [INVlinmem [HgmpInM [? ?]]]]]]]]].
    destruct INVlinmem as [Hm1 [m [Hm2 [size [Hm3 [Hm4 Hm5]]]]]].
    destruct ((~~ Wasm_int.Int32.lt
                 (Wasm_int.Int32.repr
                   (Wasm_int.Int32.signed
                     (Wasm_int.Int32.iadd (N_to_i32 gmp)
                        (N_to_i32 page_size)) ÷ 65536))
                 (Wasm_int.Int32.repr (Z.of_N (mem_size m))))) eqn:HneedMoreMem.
    2: rename HneedMoreMem into HenoughMem.
    { (* need to grow memory *)
      have H' := memory_grow_reduce_check_grow_mem state _ _ _ _ Hinv Hgmp Hm2 HgmpBound HneedMoreMem.
      destruct H' as [[sr' [Hred [Hfuncs [HvalPreserved [Hinv' HenoughM]]]]] | H'].
      { (* success *)
        left. exists sr'. repeat split=>//.
        - destruct (HenoughM _ H2) as [? _]. assumption.
        - destruct (HenoughM _ H2) as [_ ?]. unfold page_size in *. lia. }
      { (* out of mem *)
        right. intros.
        destruct (H' _ lh) as [sr' [k' [lh' [Hred [Hfuncs [HvalPreserved HoutofMem]]]]]].
        exists sr', k', lh'. by repeat split. }
    }
    { (* enough space already *)
     have H' := memory_grow_reduce_check_enough state _ _ _ _ Hinv Hgmp Hm2 HgmpBound HenoughMem.
     destruct H' as [sr' [Hred [Hfuncs [HvalPreserved [Hinv' HenoughM]]]]].
     (* success *)
     left. exists sr'. repeat split=>//.
     - destruct (HenoughM _ H2) as [? _]. assumption.
     - destruct (HenoughM _ H2) as [_ ?]. unfold page_size in *. lia.
    }
  }
Qed.

(* TODO use automation instead *)
Lemma N_to_i32_eq_modulus: forall n m,
  (-1 < Z.of_N n < Wasm_int.Int32.modulus)%Z ->
  (-1 < Z.of_N m < Wasm_int.Int32.modulus)%Z ->
  Some (VAL_num (VAL_int32 (N_to_i32 n))) = Some (VAL_num (VAL_int32 (N_to_i32 m))) ->
  n = m.
Proof.
  intros. inv H1. now solve_eq n m.
Qed.

Lemma store_constr_args_reduce {lenv} : forall ys offset vs sargs state rho fds s f m v_cap num_args,
  domains_disjoint lenv fenv ->
  (forall f, (exists res, find_def f fds = Some res) <-> (exists i, fenv ! f = Some i)) ->
  INV s f ->
  smem s (f_inst f) = Some m ->
  sglob_val s (f_inst f) glob_cap = Some (VAL_num (VAL_int32 (N_to_i32 v_cap))) ->
  (v_cap + N.of_nat (4 * (num_args + 1) + 24) < mem_length m)%N ->
  offset + length ys = num_args ->
  sglob_val s (f_inst f) glob_mem_ptr = Some (VAL_num (VAL_int32 (N_to_i32 (4 + (4*(N.of_nat offset)) + v_cap)))%N) ->
  Forall_statements_in_seq' (@store_nth_constr_arg fenv nenv lenv) ys sargs offset ->
  get_list ys rho = Some vs ->
  (* from environment relation: ys are available as locals in frame f *)
  (forall y, In y ys -> find_def y fds = None ->
                                  (exists v6 val, M.get y rho = Some v6
                                     /\ @stored_in_locals lenv y val f
                                     /\ repr_val_LambdaANF_Wasm v6 s (f_inst f) val)) ->
  (* correspondence of fenv and fds *)
  (forall y y' v, rho ! y = Some v -> repr_funvar y y' ->
         repr_val_LambdaANF_Wasm v s (f_inst f) (Val_funidx y')) ->
  exists s', reduce_trans
                  (state, s, f, [seq AI_basic i | i <- sargs])
                  (state, s', f, [])
            /\ INV s' f
            (* constructor args val *)
            /\ sglob_val s' (f_inst f) glob_cap = Some (VAL_num (VAL_int32 (N_to_i32 v_cap)))
            /\ (0 <= Z.of_N v_cap < Wasm_int.Int32.modulus)%Z
            /\ repr_val_constr_args_LambdaANF_Wasm vs s' (f_inst f) (4 + (4*(N.of_nat offset)) + v_cap)%N
            /\ sglob_val s' (f_inst f) glob_mem_ptr = Some (VAL_num (VAL_int32 (N_to_i32 ((4 + (4*(N.of_nat offset)) + v_cap) + 4 * N.of_nat (length ys)))))
            /\ s_funcs s = s_funcs s'
            /\ (forall (wal : wasm_value) (val : term.val),
                    repr_val_LambdaANF_Wasm val s (f_inst f) wal ->
                    repr_val_LambdaANF_Wasm val s' (f_inst f) wal)
            (* previous mem including tag unchanged *)
            /\ exists m', smem s' (f_inst f) = Some m'
                       /\ mem_length m = mem_length m'
                       /\ forall a, (a <= v_cap + 4 * N.of_nat offset)%N -> load_i32 m a = load_i32 m' a.
Proof.
  induction ys; intros offset vs sargs state rho fds s f m v_cap num_args HenvsDisjoint HfenvWf Hinv
                       Hm Hcap Hlen Hargs Hgmp H Hvs HmemR HfVal.
  { inv H. inv Hvs. exists s. split. apply rt_refl. split. assumption.
    have I := Hinv. destruct I as [_ [_ [_ [Hgmp_r [Hcap_r [Hmut _]]]]]].
    destruct (i32_glob_implies_i32_val s f glob_cap cap_i32_glob Hcap_r Hmut) as [v Hv].
    edestruct i32_exists_N as [x [Hx ?]]. erewrite Hx in Hv. clear Hx v.
    destruct (i32_glob_implies_i32_val s f glob_mem_ptr gmp_i32_glob Hgmp_r Hmut) as [v' Hv'].
    edestruct i32_exists_N as [x' [Hx' ?]]. erewrite Hx' in Hv'. clear Hx' v'.
    split. eassumption.
     have I := Hinv. destruct I as [_ [_ [_ [_ [_ [_ [Hinv_linmem _]]]]]]].
    destruct Hinv_linmem as [Hmem1 [m' [Hmem2 [size [Hmem3 [Hmem4 Hmem5]]]]]].
    assert (m = m') by congruence. subst m' size.
    apply mem_length_upper_bound in Hmem5; cbn in Hmem5.
    split. simpl_modulus. cbn. lia.
    split. constructor.
    split. rewrite Hgmp. do 4! f_equal. cbn. lia.
    split. auto. split. auto.
    now exists m. }
  { inv H. inv H6. rename s' into instr_args. rename a into y.
    destruct vs. { cbn in Hvs. destruct (rho ! y)=>//.
                   now destruct (get_list ys rho). }
    assert (Hgetlist: get_list ys rho = Some vs). {
      cbn in Hvs. destruct (rho ! y)=>//.
      now destruct (get_list ys rho). }
    assert (Hrhoy: rho ! y = Some v). {
      cbn in Hvs. destruct (rho ! y)=>//.
      now destruct (get_list ys rho). }
    clear Hvs. rename Hgetlist into Hvs.
    (* instr reduces to const related to value *)
    assert (Hinstr: exists wal,
      reduce_trans (state, s, f, [AI_basic instr])
                   (state, s, f, [AI_basic (BI_const_num (VAL_int32 (wasm_value_to_i32 wal)))]) /\
      repr_val_LambdaANF_Wasm v s (f_inst f) wal). {
        inv H. rename i into y'.
      { (* var *)
        assert (Htmp: In y (y :: ys)) by (cbn; auto).
        assert (HfdNone: find_def y fds = None). {
          inv H0. rewrite (HfenvWf_None _ HfenvWf). unfold translate_var in H.
          destruct (lenv ! y) eqn:Hy. rewrite Hy in H.
          inv H. now apply HenvsDisjoint in Hy. now rewrite Hy in H. }
        destruct (HmemR _ Htmp HfdNone) as [val [wal [Hrho [[y0' [Htv Hly']] Hy_val]]]].
        assert (val = v) by congruence. subst v. clear Hrhoy.
        assert (y' = y0') by now eapply repr_var_det. subst y0'.
        clear Htmp. exists wal.
        split; auto.
        constructor. now apply r_local_get'.
      }
      { (* fun idx *)
        eapply HfVal in Hrhoy; eauto.
        exists (Val_funidx i).
        split; auto. apply rt_refl.
      }
    }
    destruct Hinstr as [wal [HinstrRed HinstrVal]].
    {
      (* invariants *)
      have I := Hinv. destruct I as [_ [_ [_ [Hinv_gmp [Hinv_cap [Hinv_mut [Hinv_linmem
                                    [Hinv_gmpM [_ [_ [Hinv_nodup _]]]]]]]]]]].
      destruct (i32_glob_implies_i32_val s f glob_cap cap_i32_glob Hinv_cap Hinv_mut) as [cap ?].
      destruct (i32_glob_implies_i32_val s f glob_mem_ptr gmp_i32_glob Hinv_gmp Hinv_mut) as [gmp ?].
      destruct Hinv_linmem as [Hmem1 [m' [Hmem2 [size [Hmem3 [Hmem4 Hmem5]]]]]]. subst size.

      assert (m = m') by congruence. subst m'. clear Hmem2.

      destruct (i32_exists_N cap) as [x1 [Hx ?]]. subst cap. rename x1 into cap.
      destruct (i32_exists_N gmp) as [x1 [Hx' ?]]. subst gmp. rename x1 into gmp.
      assert (exists m0, store m (Wasm_int.N_of_uint i32m (Wasm_int.Int32.iadd
                                   (N_to_i32 v_cap)
                                   (nat_to_i32 (S (S (S (S (offset * 4)))))))) 0%N
                        (serialise_num (VAL_int32 (wasm_value_to_i32 wal))) 4 = Some m0) as Hm0. {
       intros.
       have H'' := mem_length_upper_bound _ Hmem5. unfold max_mem_pages, page_size in H''.
       replace (length (serialise_num (VAL_int32 (wasm_value_to_i32 wal)))) with 4 by reflexivity.
       unfold Wasm_int.Int32.iadd, Wasm_int.Int32.add.
       remember (S (S (S (S (offset * 4))))) as n. cbn. cbn in Hlen.
       repeat rewrite Wasm_int.Int32.Z_mod_modulus_id; simpl_modulus; cbn; try lia.
       cbn.
       apply notNone_Some.
       eapply enough_space_to_store; eauto.
       rewrite length_serialise_num_i32. lia.
     }
      (* prepare IH *)

      remember (S offset + length ys) as num_args. symmetry in Heqnum_args.

      destruct Hm0 as [m0 Hm0].
      remember (upd_s_mem s (set_nth m0 (s_mems s) 0 m0)) as s'.
      assert (Hm0': smem_store s (f_inst f)
                      (Wasm_int.N_of_uint i32m
                         (Wasm_int.Int32.iadd (N_to_i32 v_cap)
                            (nat_to_i32 (S (S (S (S (offset * 4)))))))) 0%N
                      (VAL_int32 (wasm_value_to_i32 wal)) T_i32 = Some s'). {
       unfold smem_store. remember (nat_to_i32 _) as xdf. rewrite Hmem1.
       unfold smem in Hm. rewrite Hmem1 in Hm. destruct (s_mems s)=>//.
       injection Hm as ->. cbn. cbn in Hm0. rewrite Hm0. subst. reflexivity. }

      assert (Hinv' : INV s' f). {
        eapply update_mem_preserves_INV. 6: subst; reflexivity. assumption. eassumption.
        apply store_length in Hm0. lia.
        apply store_lim_max in Hm0. congruence.
        eexists. split. reflexivity.
        apply store_length in Hm0. unfold mem_size in Hmem5.
        now rewrite Hm0 in Hmem5. }

      have I := Hinv'. destruct I as [_ [_ [_ [Hgmp_w [_ [_ [_ [? [_ [_ [_ [_ [_ [Hgmp_mult_two _]]]]]]]]]]]]]].
      destruct (Hgmp_w (VAL_int32 (Wasm_int.Int32.iadd (N_to_i32 gmp) (N_to_i32 4)))) as [s_before_IH ?].
      assert (Hmem_before_IH : smem s_before_IH (f_inst f) = Some m0). {
        subst s'. erewrite <- update_global_preserves_memory; try eassumption.
        cbn. unfold smem in Hm. rewrite Hmem1 in Hm.
        destruct (s_mems s)=>//.
        injection Hm as ->. unfold smem. by rewrite Hmem1. }

      assert (Hinv_before_IH : INV s_before_IH f). {
        apply update_global_preserves_INV with (sr:=s') (i:=glob_mem_ptr) (num:=VAL_int32 (N_to_i32 (gmp+4))) (m:=m0)=>//. cbn; tauto.
       unfold upd_s_mem in Heqs'.
       subst s'.
       unfold smem in Hm |- *. rewrite Hmem1 in Hm |- *. cbn in Hm |- *.
       destruct (s_mems s)=>//.
       move => _. intros.
       destruct H7 as [Heqn Hnbound].
       assert (gmp+ 4 = n)%N. {
         have H' := Hinv_gmpM _ _ Hm H1 H4.
         assert (Z.of_N (mem_length m) < Wasm_int.Int32.modulus)%Z. {
           have H'' := mem_length_upper_bound _ Hmem5. unfold max_mem_pages, page_size in H''. simpl_modulus. cbn. lia. }
         inversion Heqn.
         repeat rewrite Wasm_int.Int32.Z_mod_modulus_id in H9.
         now rewrite <-N2Z.inj_iff.
         assumption.
         lia. }
       subst n.
       assert (-1 < Z.of_nat (4 + 4 * offset + N.to_nat v_cap) < Wasm_int.Int32.modulus)%Z. {
         simpl_modulus. apply mem_length_upper_bound in Hmem5; cbn in Hmem5. cbn in Hlen.
         cbn. lia. }
       assert (Hnats : (N.of_nat (4 + 4 * offset + N.to_nat v_cap) =  (4 + 4 * N.of_nat offset + v_cap))%N) by lia.
       rewrite -Hnats in Hgmp.
      assert (gmp = N.of_nat (4 + 4 * offset + N.to_nat v_cap))%N. {
        apply N_to_i32_eq_modulus; auto.
        now rewrite <-Hgmp. }
      cbn. unfold page_size in Hlen.
      rewrite Hnats in H8.
      subst gmp.
      apply store_length in Hm0. cbn in Hlen. lia.
      move => _.
      intros.
      replace n with (gmp + 4)%N.
      destruct (Hgmp_mult_two gmp m0) as [n' Htwo]; eauto.
      subst s'. unfold smem in Hm |- *. rewrite Hmem1 in Hm |- *. cbn in Hm |- *.
      destruct (s_mems s)=>//.
      eapply update_memory_preserves_globals; eauto.
      exists (2 + n')%N. lia.
      destruct H7.
      inv H7.
      repeat rewrite Wasm_int.Int32.Z_mod_modulus_id in H10; try lia.
      have H' := Hinv_gmpM _ _ Hm H1 H4.
      assert (Z.of_N (mem_length m) < Wasm_int.Int32.modulus)%Z. {
        have H'' := mem_length_upper_bound _ Hmem5. unfold max_mem_pages, page_size in H''. simpl_modulus. cbn. lia. }
      simpl_modulus. simpl_modulus_in H7. cbn. lia.
      unfold Wasm_int.Int32.iadd, Wasm_int.Int32.add in H6.
      cbn in H6.
      repeat rewrite Wasm_int.Int32.Z_mod_modulus_id in H6; try lia.
      replace 4%Z with (Z.of_N 4) in H6 by lia.
      rewrite -N2Z.inj_add in H6.
      now unfold N_to_i32. }
      assert (Hcap_before_IH: sglob_val s_before_IH (f_inst f) glob_cap = Some (VAL_num (VAL_int32 (N_to_i32 v_cap)))). {
        subst. eapply update_global_get_other; try apply H6; auto. now intro. }

      assert (Hlen_m0: (v_cap + N.of_nat (4 * (length ys + 1) + 24) < mem_length m0)%N). {
        apply store_length in Hm0. cbn. cbn in Hlen. lia. }

      assert (HrelE_before_IH: (forall y : var,
        In y ys ->
        find_def y fds = None ->
        exists (v6 : term.val) (val : wasm_value),
          rho ! y = Some v6 /\
          @stored_in_locals lenv y val f /\
          repr_val_LambdaANF_Wasm v6 s_before_IH (f_inst f) val)). {
        intros y0 H7 HfdNone. assert (Htmp : In y0 (y :: ys)) by (right; assumption).
        destruct (HmemR _ Htmp HfdNone) as [val' [wal' [? [? ?]]]].
        subst s'. exists val', wal'. repeat split; try assumption.

        { edestruct i32_exists_N as [? [Hn ?]]. erewrite Hn in H6.
          rewrite H1 in Hgmp.
          assert (-1 < Z.of_nat (4 + 4 * offset + N.to_nat v_cap) < Wasm_int.Int32.modulus)%Z. {
         simpl_modulus. apply mem_length_upper_bound in Hmem5; cbn in Hmem5.
         cbn. lia. }

         assert (gmp = N.of_nat (4 + 4 * offset + N.to_nat v_cap))%N. {
           apply N_to_i32_eq_modulus; auto. rewrite Hgmp. do 4! f_equal. lia. }
         clear Hgmp.

         assert ((4 + 4 * N.of_nat offset + v_cap) + 4 = x)%N. {
           assert ((-1 < Z.of_N (4 + 4 * N.of_nat offset + v_cap + 4) < Wasm_int.Int32.modulus)%Z).
             { apply store_length in Hm0.
               apply mem_length_upper_bound in Hmem5; cbn in Hmem5.
               assert (Z.of_N gmp + 4 < Wasm_int.Int32.modulus)%Z.
                 simpl_modulus; cbn; lia. lia. }

              inv Hn. repeat rewrite Wasm_int.Int32.Z_mod_modulus_id in H16; try lia.
              repeat rewrite Wasm_int.Int32.Z_mod_modulus_id; lia. } subst x. clear Hn.

          apply mem_length_upper_bound in Hmem5. cbn in Hmem5.
          unfold page_size in Hlen_m0. cbn in Hlen_m0.
          assert (mem_length m0 = mem_length m). { now apply store_length in Hm0. }

          eapply val_relation_depends_on_mem_smaller_than_gmp_and_funcs; subst. 11: apply H10.
          apply update_global_preserves_funcs in H6. rewrite -H6. reflexivity.
          eassumption. eassumption. eassumption.
          have I := Hinv. destruct I as [_ [_ [_ [_ [_ [_ [_ [INVgmp_M _]]]]]]]].
          have H' := INVgmp_M _ _ Hm H1 H4. simpl_modulus. cbn. lia.
          eapply update_global_get_same in H6. eassumption.
          split; first lia. simpl_modulus. cbn. lia.
          lia.
          intros. assert (Hex: exists v, load_i32 m a = Some v). {
            apply enough_space_to_load. lia. } destruct Hex.
          rewrite H15. symmetry. erewrite load_store_load_i32; try apply Hm0; auto.
          unfold Wasm_int.Int32.iadd, Wasm_int.Int32.add. remember (S (S (S (S (offset * 4))))) as n.
          cbn. subst.
          repeat (rewrite Wasm_int.Int32.Z_mod_modulus_id); try lia.
          intros. assert (Hex: exists v, load_i64 m a = Some v). {
            apply enough_space_to_load_i64. lia. } destruct Hex.
          rewrite H15. symmetry. erewrite load_store_load_i64; try apply Hm0; auto.
          unfold Wasm_int.Int32.iadd, Wasm_int.Int32.add. remember (S (S (S (S (offset * 4))))) as n.
          cbn. subst.
          repeat (rewrite Wasm_int.Int32.Z_mod_modulus_id); try lia. }
      }

      assert (Hgmp_before_IH: sglob_val s_before_IH (f_inst f) glob_mem_ptr =
  Some (VAL_num (VAL_int32 (N_to_i32 (4 + 4 * N.of_nat (S offset) + v_cap))))). {
        subst.
        apply update_global_get_same in H6. rewrite H6. f_equal. f_equal.

        unfold Wasm_int.Int32.iadd, Wasm_int.Int32.add. unfold N_to_i32. repeat f_equal.
        remember (Z.of_N (4 + 4 * N.of_nat (S offset) + v_cap)) as x. cbn.
        rewrite Wasm_int.Int32.Z_mod_modulus_id; try lia. unfold nat_to_i32. f_equal.
        assert ((-1 < Z.of_nat (4 + 4 * offset + N.to_nat v_cap) < Wasm_int.Int32.modulus)%Z). {
          unfold page_size in Hlen_m0. cbn in Hlen_m0.
          apply store_length in Hm0.
          apply mem_length_upper_bound in Hmem5. cbn in Hmem5.
          split; try lia. simpl_modulus. cbn. lia. }
        rewrite Hgmp in H1. apply N_to_i32_eq_modulus in H1; try lia.
      }

     assert (HfVal_before_IH: (forall (y : positive) (y' : funcidx) (v : term.val),
       rho ! y = Some v -> repr_funvar y y' ->
       repr_val_LambdaANF_Wasm v s_before_IH (f_inst f) (Val_funidx y'))).
     { intros. have H' := HfVal _ _ _ H7 H8.
       eapply val_relation_func_depends_on_funcs; last apply H'. subst.
       now apply update_global_preserves_funcs in H6. }

      assert (Hlen': (v_cap + N.of_nat (4 * (num_args + 1) + 24) < mem_length m0)%N). {
        apply store_length in Hm0. cbn. cbn in Hlen. lia. }

      have IH := IHys _ _ _ state _ _ _ _ _ _ _ HenvsDisjoint HfenvWf Hinv_before_IH Hmem_before_IH
                 Hcap_before_IH Hlen' Heqnum_args Hgmp_before_IH H3 Hvs HrelE_before_IH HfVal_before_IH.
      clear IHys Hmem_before_IH Hinv_before_IH HrelE_before_IH Hcap_before_IH.
      destruct IH as [sr [Hred [Hinv'' [Hv1 [? [Hv2 [? [? [? [m1 [Hm1 [? ?]]]]]]]]]]]].

      assert (sglob_val s (f_inst f) glob_cap
            = sglob_val (upd_s_mem s (set_nth m0 (s_mems s) 0 m0)) (f_inst f) glob_cap)
      as Hglob_cap by reflexivity.
      have HlenBound := mem_length_upper_bound _ Hmem5. cbn in HlenBound.

      rewrite H0 in Hcap. apply N_to_i32_eq_modulus in Hcap; try lia. subst v_cap.
      eexists. split.
      (* reduce *)
      dostep_nary 0. apply r_global_get. rewrite Hglob_cap. eassumption.
      dostep_nary 2. constructor. constructor. reflexivity. reflexivity.
      eapply rt_trans. apply app_trans_const; auto. apply app_trans. eassumption.

      dostep_nary 2. eapply r_store_success; eassumption.
      dostep_nary 0. apply r_global_get. subst s'. eassumption.
      dostep_nary 2. constructor. apply rs_binop_success=>//.
      dostep_nary 1. apply r_global_set'. eassumption.
      apply Hred.
      split. assumption. split. assumption. split. simpl_modulus. cbn. lia. split.
      econstructor. apply Hm1. eassumption. {
        simpl_modulus.
        apply mem_length_upper_bound in Hmem5. cbn in Hmem5.
        apply store_length in Hm0.
        remember (Z.of_N (4 + 4 * N.of_nat (S offset) + cap + 4 * N.of_nat (length ys))) as ndfs'.
        cbn. lia. } lia.

      { (* load val *)
        rewrite -H12; try lia.
        apply store_load_i32 in Hm0=>//.
        assert ((4 + 4 * N.of_nat offset + cap)%N =
                (Wasm_int.N_of_uint i32m (Wasm_int.Int32.iadd (N_to_i32 cap)
                            (nat_to_i32 (S (S (S (S (offset * 4))))))))) as Har. {
          remember (S (S (S (S (offset * 4))))) as o.
          remember ((4 + 4 * N.of_nat offset + cap)%N) as o'. cbn.
          repeat rewrite Wasm_int.Int32.Z_mod_modulus_id; simpl_modulus; cbn; lia.
      }
        rewrite deserialise_serialise in Hm0=>//. rewrite Har. eassumption. }

      { rewrite H1 in Hgmp.
        assert ((-1 < Z.of_nat (4 + 4 * offset + N.to_nat cap) < Wasm_int.Int32.modulus)%Z). {
          unfold page_size in Hlen_m0; cbn in Hlen_m0.
          simpl_modulus. cbn. lia. }
        apply N_to_i32_eq_modulus in Hgmp; auto. subst gmp.

        apply H10.
        eapply val_relation_depends_on_mem_smaller_than_gmp_and_funcs with (sr:=s);
          try apply Hy_val; try eassumption.
        - subst. apply update_global_preserves_funcs in H6. cbn in H6. congruence.
        - apply update_global_preserves_memory in H6. rewrite <- H6.
          cbn. unfold smem. rewrite Hmem1. cbn. subst s'.
          unfold smem in Hm. by destruct (s_mems s).
        - have I := Hinv. destruct I as [_ [_ [_ [_ [_ [_ [_ [Hgmp_M _]]]]]]]].
          have H' := Hgmp_M _ _ Hm H1 H4. apply mem_length_upper_bound in Hmem5.
          cbn in Hmem5. simpl_modulus. cbn. cbn in H'. lia.
        - simpl_modulus.
          unfold page_size in Hlen_m0; cbn in Hlen_m0.
          apply store_length in Hm0.
          remember (4 + 4 * N.of_nat (S offset) + cap)%N as nfd. cbn. lia.
        - lia.
        - intros.
          assert (Hex: exists v, load_i32 m a = Some v). {
            apply enough_space_to_load.
            unfold page_size in Hlen; cbn in Hlen. lia.
          } destruct Hex.
          symmetry. erewrite load_store_load_i32; try apply Hm0 ; eauto.
          remember (S (S (S (S (offset * 4))))) as n. cbn.
          repeat rewrite Wasm_int.Int32.Z_mod_modulus_id; simpl_modulus; cbn; lia.
        - intros.
          assert (Hex: exists v, load_i64 m a = Some v). {
            apply enough_space_to_load_i64.
            unfold page_size in Hlen; cbn in Hlen. lia.
          } destruct Hex.
          symmetry. erewrite load_store_load_i64; try apply Hm0 ; eauto.
          remember (S (S (S (S (offset * 4))))) as n. cbn.
          repeat rewrite Wasm_int.Int32.Z_mod_modulus_id; try lia. lia.
      }

      replace (4 + (4 + 4 * N.of_nat offset + cap))%N with (4 + 4 * N.of_nat (S offset) + cap)%N by lia.
      apply Hv2.
      split. subst. auto. rewrite H8. do 4! f_equal.
      replace (4 + 4 * N.of_nat (S offset) + cap)%N with (4 + (4 + 4 * N.of_nat offset + cap))%N by lia.
       remember (4 + 4 * N.of_nat offset + cap)%N as m'.
       replace (length (y :: ys)) with (1 + (length ys)) by now cbn. lia.
      split. apply update_global_preserves_funcs in H6. subst s'. cbn in H6. congruence.
      split. {
        intros. apply H10.
        assert (Heq: N_to_i32 gmp = (N_to_i32 (4 + 4 * N.of_nat offset + cap))%N) by congruence.
        assert ((-1 < Z.of_N (4 + 4 * N.of_nat offset + cap) < Wasm_int.Int32.modulus)%Z).
        { remember (4 + 4 * N.of_nat offset + cap)%N as ndf. simpl_modulus. cbn. lia. }
        assert (Htmp: (Some (VAL_num (VAL_int32 (N_to_i32 gmp))) =
                       Some (VAL_num (VAL_int32 (N_to_i32 (4 + 4 * N.of_nat offset + cap)))))%N) by congruence.

        apply N_to_i32_eq_modulus in Htmp; auto. subst gmp.

        eapply val_relation_depends_on_mem_smaller_than_gmp_and_funcs. 11: apply H13.
        all: try eassumption.
        - apply update_global_preserves_funcs in H6. subst s'. cbn in H6.
          congruence.
        - apply update_global_preserves_memory in H6. rewrite <- H6.
          unfold smem. rewrite Hmem1. unfold smem in Hm. rewrite Hmem1 in Hm.
          destruct (s_mems s)=>//. subst s'. reflexivity.
        - have I := Hinv. destruct I as [_ [_ [_ [_ [_ [_ [_ [Hgmp_M _]]]]]]]].
          have H' := Hgmp_M _ _ Hm H1 H4. apply mem_length_upper_bound in Hmem5.
          cbn in Hmem5. remember (4 + 4 * N.of_nat offset + cap)%N as df. simpl_modulus. cbn. lia.
        - simpl_modulus.
          unfold page_size in Hlen_m0; cbn in Hlen_m0.
          apply store_length in Hm0.
          remember (Z.of_N (4 + 4 * N.of_nat (S offset) + cap)) as mdf. cbn. lia.
        - lia.
        { intros.
          assert (Hex: exists v, load_i32 m a = Some v). {
          have Hm0'' := Hm0.
          apply enough_space_to_load. unfold store in Hm0''.
          destruct ((Wasm_int.N_of_uint i32m (Wasm_int.Int32.iadd (N_to_i32 cap)
                        (nat_to_i32 (S (S (S (S (offset * 4))))))) + 0 +
                   N.of_nat 4 <=? mem_length m)%N) eqn:Har. 2: inv Hm0''.
              apply store_length in Hm0.
             unfold page_size in Hlen_m0. lia. } destruct Hex.
          assert (Har: (a + 4 <=
              Wasm_int.N_of_uint i32m
                (Wasm_int.Int32.iadd (N_to_i32 cap)
                   (nat_to_i32 (S (S (S (S (offset * 4))))))))%N). {
            unfold Wasm_int.Int32.iadd, Wasm_int.Int32.add.
            remember ((S (S (S (S (offset * 4)))))) as o. cbn.
            repeat rewrite Wasm_int.Int32.Z_mod_modulus_id; simpl_modulus; cbn; lia. }

          have Ht := load_store_load_i32 _ _ _ _ _ _ _ Har H16 Hm0.
          clear Har. rewrite Ht; auto. }
        { intros.
          assert (Hex: exists v, load_i64 m a = Some v). {
            have Hm0'' := Hm0.
            apply enough_space_to_load_i64. unfold store in Hm0''.
            destruct ((Wasm_int.N_of_uint i32m
             (Wasm_int.Int32.iadd (N_to_i32 cap)
                (nat_to_i32 (S (S (S (S (offset * 4))))))) + 0 +
           N.of_nat 4 <=? mem_length m)%N) eqn:Har. 2: inv Hm0''.
             apply store_length in Hm0.
            unfold page_size in Hlen_m0. lia. } destruct Hex.
          assert (Har: (a + 8 <=
                          Wasm_int.N_of_uint i32m
                            (Wasm_int.Int32.iadd (N_to_i32 cap)
                               (nat_to_i32 (S (S (S (S (offset * 4))))))))%N). {
            unfold Wasm_int.Int32.iadd, Wasm_int.Int32.add.
            remember ((S (S (S (S (offset * 4)))))) as o. cbn.
            repeat rewrite Wasm_int.Int32.Z_mod_modulus_id; lia. }

          have Ht := load_store_load_i64 _ _ _ _ _ _ _ Har H16 Hm0.
          clear Har. rewrite Ht; auto. }
      }

      exists m1. split. assumption.
      split. apply store_length in Hm0. congruence.
      { intros.
        assert (exists v, load_i32 m a = Some v). {
          have Hm0'' := Hm0.
          apply enough_space_to_load. unfold store in Hm0''.
          destruct ((Wasm_int.N_of_uint i32m
             (Wasm_int.Int32.iadd (N_to_i32 cap)
                (nat_to_i32 (S (S (S (S (offset * 4))))))) + 0 +
           N.of_nat 4 <=? mem_length m)%N) eqn:Har. 2: inv Hm0''.
             apply store_length in Hm0.
             unfold page_size in Hlen_m0. lia.
        } destruct H14. rewrite -H12; try lia.

        symmetry. erewrite load_store_load_i32; try apply Hm0; eauto.
        remember (S (S (S (S (offset * 4))))) as n.
        cbn. repeat rewrite Wasm_int.Int32.Z_mod_modulus_id; simpl_modulus; cbn; lia. } } }
Qed.


Lemma store_constr_reduce {lenv} : forall state s f rho fds ys (vs : list term.val) t n sargs m gmp_v ord constr_size mem',
  get_ctor_size cenv t = Ret constr_size ->
  get_ctor_ord cenv t = Ret ord ->
  get_ctor_arity cenv t = Ret n ->
  n > 0 ->
  n = length ys ->
  domains_disjoint lenv fenv ->
  (forall f, (exists res, find_def f fds = Some res) <-> (exists i, fenv ! f = Some i)) ->
  INV s f ->
  (* enough memory available *)
  smem s (f_inst f) = Some m ->
  sglob_val s (f_inst f) glob_mem_ptr = Some (VAL_num (VAL_int32 (N_to_i32 gmp_v))) ->
  (Z.of_N gmp_v + Z.of_N constr_size + Z.of_N mem' < Z.of_N (mem_length m))%Z ->
  (* from memory relation: ys available as local vars *)
  (forall y : var,
         In y ys ->
         find_def y fds = None ->
         exists (v6 : term.val) (val : wasm_value),
           rho ! y = Some v6 /\
           @stored_in_locals lenv y val f /\
           repr_val_LambdaANF_Wasm v6 s (f_inst f) val) ->
  (Z.of_nat (length ys) <= max_constr_args)%Z ->
  Forall_statements_in_seq (@store_nth_constr_arg fenv nenv lenv) ys sargs ->
  get_list ys rho = Some vs ->

  (* function indices: value relation *)
  (forall (y : positive) (y' : funcidx) (v : term.val),
         rho ! y = Some v ->
         repr_funvar y y' ->
         repr_val_LambdaANF_Wasm v s (f_inst f) (Val_funidx y')) ->

  exists s', reduce_trans
    (state, s, f,
      [:: AI_basic (BI_global_get glob_mem_ptr)] ++
      [:: AI_basic (BI_global_set glob_cap)] ++
      [:: AI_basic (BI_global_get glob_cap)] ++
      [:: AI_basic (BI_const_num (nat_to_value (N.to_nat ord)))] ++
      [:: AI_basic (BI_store T_i32 None {| memarg_offset:=0%N; memarg_align:=2%N |})] ++
      [:: AI_basic (BI_global_get glob_mem_ptr)] ++
      [:: AI_basic (BI_const_num (nat_to_value 4))] ++
      [:: AI_basic (BI_binop T_i32 (Binop_i BOI_add))] ++
      [:: AI_basic (BI_global_set glob_mem_ptr)] ++
      [seq AI_basic i | i <- sargs]) (state, s', f, []) /\
    INV s' f /\
    s_funcs s = s_funcs s' /\
    (forall m', smem s' (f_inst f) = Some m' -> mem_length m = mem_length m') /\
    (forall (wal : wasm_value) (val : term.val),
      repr_val_LambdaANF_Wasm val s (f_inst f) wal ->
      repr_val_LambdaANF_Wasm val s' (f_inst f) wal) /\
      (* cap points to value *)
    (exists cap_v wasmval, sglob_val s' (f_inst f) glob_cap = Some (VAL_num (VAL_int32 cap_v))
          /\ wasm_value_to_i32 wasmval = cap_v
          /\ repr_val_LambdaANF_Wasm (Vconstr t vs) s' (f_inst f) wasmval) /\
    sglob_val s' (f_inst f) glob_mem_ptr = Some (VAL_num (VAL_int32
                    (N_to_i32 (4 + gmp_v + 4 * N.of_nat (length ys))))).
Proof.
  intros ??????????????? Hsize Hord Harr HarrGt0 -> HenvsDisjoint HfenvWf Hinv HenoughM1 HenoughM2 HenoughM3
                      HmemR Hmaxargs Hsetargs Hrho HfVal.

  have I := Hinv. destruct I as [_ [_ [_ [INVgmp_w [INVcap_w [INVmut [INVmem [_ [_ [_ [INV_instglobs [_ [_ [INV_gmp_mult_two _]]]]]]]]]]]]]].
  have INVgmp_r := global_var_w_implies_global_var_r _ _ _ (or_introl gmp_i32_glob) INVmut INVgmp_w.

  assert(HgmpBound: (-1 < Z.of_N gmp_v < Wasm_int.Int32.modulus)%Z). {
    destruct INVmem as [Hmem1 [m' [Hmem2 [? [<- [Hmem4 Hmem5]]]]]]. solve_eq m m'.
    apply mem_length_upper_bound in Hmem5. cbn in Hmem5.
    simpl_modulus. cbn. simpl_modulus_in HenoughM3. lia. }

  destruct (INV_gmp_mult_two gmp_v m) as [n0 Hgmp_mult_two]; eauto. clear INV_gmp_mult_two.
  (* invariants after set_global cap *)
  destruct (INVcap_w (VAL_int32 (N_to_i32 gmp_v))) as [s' ?]. clear INVcap_w.
  (* INV after set_global cap *)
  assert (INV s' f) as Hinv'. {
    eapply update_global_preserves_INV. 7: apply H. all: eauto.
    left. split=>//. right; right; right; now constructor.
    now intro.
    all: intros Hcontra; inv Hcontra. }

   have I := Hinv'. destruct I as [_ [_ [_ [_ [INVcap_w'' [INVmut'' [INVlinmem'' _ ]]]]]]].

  (* invariants mem *)
  edestruct INVlinmem'' as [Hmem1'' [m' [Hmem2'' [size'' [Hmem3'' [Hmem4'' Hmem5'']]]]]].
  assert (m' = m). { apply update_global_preserves_memory in H. congruence. } subst m' size''.

  assert (exists mem, store m (Wasm_int.N_of_uint i32m (N_to_i32 gmp_v)) 0%N
                        (serialise_num (nat_to_value (N.to_nat ord))) 4 = Some mem) as Htest. {
    apply notNone_Some. apply enough_space_to_store. cbn.
    rewrite length_serialise_num_i32.
    rewrite Wasm_int.Int32.Z_mod_modulus_id; try lia.
    destruct Hinv' as [_ [_ [_ [_ [_ [_ [Hlinmem [INVgmp_M _]]]]]]]].
    destruct Hlinmem as [Hmem1 [m' [Hmem2 [size [Hmem3 [Hmem4 Hmem5]]]]]].

    solve_eq m' m.
    assert (Hgmp_r : sglob_val s' (f_inst f) glob_mem_ptr =
              Some (VAL_num (VAL_int32 (N_to_i32 gmp_v)))). { eapply update_global_get_other; try eassumption.
               unfold glob_mem_ptr, glob_cap. lia. }
    have Htest := INVgmp_M _ _ Hmem2 Hgmp_r. lia. }
  destruct Htest as [m' Hstore].
  remember (upd_s_mem s' (set_nth m' s'.(s_mems) 0 m')) as s_tag.
  assert (Hstore' : smem_store s' (f_inst f) (Wasm_int.N_of_uint i32m (N_to_i32 gmp_v))
                    0%N (nat_to_value (N.to_nat ord)) T_i32 = Some s_tag). {
    unfold smem_store. rewrite Hmem1''. cbn.
    unfold smem in Hmem2''. rewrite Hmem1'' in Hmem2''. destruct (s_mems s')=>//.
    injection Hmem2'' as ->. now rewrite Hstore. }

  assert (Hinv_tag : INV s_tag f). { subst.
    assert (mem_length m = mem_length m'). { apply store_length in Hstore. congruence. }
    assert (m.(meminst_type).(lim_max) = m'.(meminst_type).(lim_max)). { apply store_lim_max in Hstore. congruence. }
    eapply update_mem_preserves_INV. apply Hinv'. eassumption. erewrite <- H0. lia.
    congruence. exists (mem_size m); split; auto. unfold mem_size. congruence. reflexivity. }

  have I := Hinv_tag. destruct I as [_ [_ [_ [Hgmp_w _]]]].
  destruct (Hgmp_w (VAL_int32 (Wasm_int.Int32.iadd (N_to_i32 gmp_v) (nat_to_i32 4)))) as [s_before_args ?].
  edestruct i32_exists_N as [gmp [HgmpEq HgmpBound']].
  erewrite HgmpEq in H0.
  assert (gmp = gmp_v + 4)%N. {
    inversion HgmpEq. repeat rewrite Wasm_int.Int32.Z_mod_modulus_id in H2; try lia.
    unfold store in Hstore.
    destruct ((Wasm_int.N_of_uint i32m (N_to_i32 gmp_v) + 0 +
            N.of_nat 4 <=? mem_length m)%N) eqn:Har. 2: inv Hstore.
    apply N.leb_le in Har. cbn in Har.
    rewrite Wasm_int.Int32.Z_mod_modulus_id in Har; try lia.
    apply mem_length_upper_bound in Hmem5''. cbn in Hmem5''.
    rewrite Wasm_int.Int32.Z_mod_modulus_id; try lia.
    simpl_modulus. cbn. lia.
  } subst gmp.

 (* INV after set_global gmp *)
  assert (Hinv_before_args : INV s_before_args f). {
    eapply update_global_preserves_INV with (num:=(VAL_int32 (N_to_i32 (gmp_v + 4)))) (i:=glob_mem_ptr).
    by cbn; tauto.
    eassumption. now intro.
    subst s_tag. unfold smem. rewrite Hmem1''. cbn. destruct (s_mems s')=>//.
    move => _ n1 [Heqn1 Hrangen1].
    unfold page_size in HenoughM3; cbn in HenoughM3.
    replace n1 with (gmp_v + 4)%N.
    { apply store_length in Hstore.
      have Hge32 := constr_size_ge_32 _ _ _ Hsize Harr HarrGt0. lia. }
    inversion Heqn1. by simpl_eq.
    move => _. intros n1 [Heqn1 Hrangen1].
    inv Heqn1. simpl_eq.
    exists (2 + n0)%N. lia.
    assumption. }

  assert (Hmem: smem s_before_args (f_inst f) = Some m'). {
    subst s_tag. cbn.
    apply update_global_preserves_memory in H0. rewrite -H0. cbn.
    unfold smem. rewrite Hmem1''. by destruct (s_mems s'). }

  assert (Hglob_cap: sglob_val s_before_args (f_inst f) glob_cap = Some (VAL_num (VAL_int32 (N_to_i32 gmp_v)))). {
    subst.
    replace (sglob_val (upd_s_mem s' (set_nth m' (s_mems s') 0 m')) (f_inst f) glob_cap)
       with (sglob_val s' (f_inst f) glob_cap) by reflexivity.
    apply update_global_get_same in H.
    eapply update_global_get_other in H0; eauto. now intro. }

  assert (HenoughM': (gmp_v + N.of_nat (4 * (0 + length ys + 1) + 24) < mem_length m')%N). {
    have I := Hinv. destruct I as [_ [_ [_ [_ [_ [_ [Hlinmem _]]]]]]].
    destruct Hlinmem as [Hmem1 [m'' [Hmem2 [size [Hmem3 [Hmem4 Hmem5]]]]]].
    assert (mem_length m = mem_length m'). {
      apply store_length in Hstore.
      apply update_global_preserves_memory in H0, H.
      by simpl_eq. }
    unfold get_ctor_size in Hsize.
    rewrite Harr in Hsize. cbn in Hsize.
    destruct (length ys =? 0) eqn:Hl; inv Hsize; lia. }

  assert (HlenBound: (-1 < Z.of_nat (length ys + 0) < 2 * max_constr_args)%Z). {
    rewrite Nat.add_0_r. cbn. unfold max_constr_args in Hmaxargs. lia. }

  assert (HrelE': forall y : var,
    In y ys ->
    find_def y fds = None ->
    exists (v6 : term.val) (val : wasm_value),
      rho ! y = Some v6 /\
      @stored_in_locals lenv y val f /\
      repr_val_LambdaANF_Wasm v6 s_before_args (f_inst f) val). {
    intros y Hy Hfd. apply HmemR in Hy; auto. destruct Hy as [val [wal [Hrho' [Hylocal Hval]]]].
    exists val, wal. repeat (split; auto).

    eapply val_relation_depends_on_mem_smaller_than_gmp_and_funcs; last apply Hval.
    { subst. apply update_global_preserves_funcs in H, H0. cbn.
      assert (s_funcs (upd_s_mem s' (set_nth m' (s_mems s') 0 m')) = s_funcs s') by reflexivity. congruence. }
    { erewrite update_global_preserves_memory. 2: eassumption. eassumption. }
    { apply update_global_preserves_memory in H0. subst. rewrite <- H0. cbn.
      unfold smem. rewrite Hmem1''. by destruct (s_mems s'). }
    { eassumption. }
    { apply store_length in Hstore.
      subst. apply mem_length_upper_bound in Hmem5''. cbn in Hmem5''.
      simpl_modulus.
      have Hge32 := constr_size_ge_32 _ _ _ Hsize Harr HarrGt0.
      cbn. cbn in HenoughM'. lia. }
    { subst. eapply update_global_get_same. eassumption. }
    { cbn in HlenBound. rewrite Nat.add_0_r in HlenBound.
      simpl_modulus_in HenoughM'. cbn in HenoughM'. unfold page_size in HenoughM'.
      remember (Z.of_N (2 * n0 + 4) + 8 <= Z.of_N (mem_length m'))%Z as jklj. simpl_modulus. cbn. subst.
      apply mem_length_upper_bound in Hmem5''. cbn in Hmem5''. apply store_length in Hstore.
      have Hge8 := constr_size_ge_32 _ _ _ Hsize Harr HarrGt0.
      cbn. cbn in HenoughM'. lia. }
    { lia. }
    { intros.
      assert (Hv: exists v, load_i32 m a = Some v). { apply enough_space_to_load. subst.
        simpl_modulus_in HenoughM'. apply store_length in Hstore. lia. }
      destruct Hv as [? Hv].
      assert (load_i32 m' a = Some x). {
        eapply load_store_load_i32 ; try apply Hstore; eauto. cbn.
        rewrite Wasm_int.Int32.Z_mod_modulus_id; lia. }
      congruence. }
    { intros.
      assert (exists v, load_i64 m a = Some v) as [? Hv]. {
        apply enough_space_to_load_i64. subst.
        simpl_modulus_in HenoughM'. apply store_length in Hstore. lia. }
      assert (load_i64 m' a = Some x). {
        eapply load_store_load_i64 ; try apply Hstore; eauto. cbn.
        rewrite Wasm_int.Int32.Z_mod_modulus_id; lia. }
      congruence. }
  }

  assert (Hgmp_before_args : sglob_val  s_before_args (f_inst f) glob_mem_ptr =
        Some (VAL_num (VAL_int32 (N_to_i32 (4 + gmp_v)%N)))).
  { apply update_global_get_same in H0. rewrite H0. do 4! f_equal. lia. }

  assert (HfVal_before_args: (forall (y : positive) (y' : funcidx) (v : term.val),
         rho ! y = Some v ->
         repr_funvar y y' ->
         repr_val_LambdaANF_Wasm v s_before_args (f_inst f) (Val_funidx y'))).
  { intros. have H' := HfVal _ _ _ H1 H2.
    eapply val_relation_func_depends_on_funcs; last eassumption.
    apply update_global_preserves_funcs in H, H0. subst. now cbn in H0.
  }
  have Hargs := store_constr_args_reduce _ 0 _ _ state _ _ _ _ _ _ _ HenvsDisjoint HfenvWf
                  Hinv_before_args Hmem Hglob_cap HenoughM' Logic.eq_refl Hgmp_before_args
                    Hsetargs Hrho HrelE' HfVal_before_args.
  destruct Hargs as [s_final [Hred [Hinv_final [Hcap_v [? [Hargs_val [Hglobsame
                    [Hfuncs [HvalPreserved [m'' [Hm' [Hmemlen Hmemsame]]]]]]]]]]]].
  {
  cbn in Hargs_val. clear Hsetargs Hrho HenoughM' HlenBound.

  exists s_final. split.
  (* steps *)
  dostep_nary 0. apply r_global_get. eassumption.
  dostep_nary 1. apply r_global_set'. eassumption.
  dostep_nary 0. apply r_global_get. eapply update_global_get_same. eassumption.
  (* write tag *)
  dostep_nary 2. eapply r_store_success. eassumption.
  dostep_nary 0. apply r_global_get. {
    subst s_tag. replace (sglob_val (upd_s_mem s' (set_nth m' (s_mems s') 0 m')))
                    with (sglob_val s') by reflexivity.
    eapply update_global_get_other with (j:= glob_cap). assumption. now intro.
    2: eassumption. eassumption. }

  dostep_nary 2. constructor. apply rs_binop_success=>//.
  dostep_nary 1. apply r_global_set'. rewrite HgmpEq. eassumption.
  cbn. apply Hred. split. assumption.
  split. apply update_global_preserves_funcs in H, H0. subst s_tag. cbn in H0. congruence.
  split. {
    intros. assert (m'0 = m'') by congruence. subst m'0.
    now apply store_length in Hstore. }
  split. {
    intros.
    assert (Hmeq: mem_length m = mem_length m') by
      apply store_length in Hstore=>//.
    unfold page_size in HenoughM3; cbn in HenoughM3.
    apply HvalPreserved.
    eapply val_relation_depends_on_mem_smaller_than_gmp_and_funcs; last apply H2. all: eauto.
    { apply update_global_preserves_funcs in H, H0. subst. cbn in H0. congruence. }
    { apply mem_length_upper_bound in Hmem5''; cbn in Hmem5''.
      destruct Hinv' as [_[_[_[_[_[_[_[HgmpInM [_[_[HglobNodup _]]]]]]]]]]].
      assert (Hneq: glob_mem_ptr <> glob_cap) by now intro.
      have H' := update_global_get_other _ _ _ _ _ _ _ HglobNodup Hneq HenoughM2 H.
      have H'' := HgmpInM _ _ Hmem2'' H' HgmpBound. simpl_modulus. cbn. lia. }
    { apply store_length in Hstore.
      apply mem_length_upper_bound in Hmem5''; cbn in Hmem5''.
      destruct Hinv_before_args as [_[_[_[_[_[_[_[HgmpInM _]]]]]]]].
      assert (Hneq: glob_mem_ptr <> glob_cap) by now intro.
      have H' := update_global_get_same _ _ _ _ _ H0.
      have H'' := HgmpInM _ _ Hmem H' HgmpBound'.
      remember (Z.of_N (4 + gmp_v) + 8)%Z as dfd.
      simpl_modulus; cbn. lia. }
    { lia. }
    { intros. assert (exists v, load_i32 m a = Some v). {
        apply enough_space_to_load. unfold store in Hstore.
        destruct ((Wasm_int.N_of_uint i32m (N_to_i32 gmp_v) + 0 + N.of_nat 4 <=?
            mem_length m)%N%N). 2: inv Hstore. lia. } destruct H4.
      symmetry. erewrite load_store_load_i32; try apply Hstore; eauto.
      cbn. rewrite Wasm_int.Int32.Z_mod_modulus_id; lia. }
    { intros. assert (exists v, load_i64 m a = Some v). {
        apply enough_space_to_load_i64. unfold store in Hstore.
        destruct ((Wasm_int.N_of_uint i32m (N_to_i32 gmp_v) + 0 +
            N.of_nat 4 <=?
            mem_length m)%N). 2: inv Hstore. lia. } destruct H4.
      symmetry. erewrite load_store_load_i64; try apply Hstore; eauto.
      cbn. rewrite Wasm_int.Int32.Z_mod_modulus_id; lia. }
  }
  split; last assumption. (* constr value in memory *)
  { eexists. exists (Val_ptr gmp_v). split. eassumption.
    split. reflexivity.
    econstructor; try eassumption. {
      assert (Hm'': smem s (f_inst f) = Some m).
      erewrite update_global_preserves_memory; eassumption.
      apply mem_length_upper_bound in Hmem5''. cbn in Hmem5''.
      unfold page_size in HenoughM3; cbn in HenoughM3.
      unfold max_constr_args in Hmaxargs.
      remember ((4 + 4 * N.of_nat 0 + gmp_v + 4 * N.of_nat (length ys)))%N as dfd.
      simpl_modulus. cbn. lia. }
    lia. exists n0. auto.
    reflexivity.
    apply store_load_i32 in Hstore.
    rewrite deserialise_serialise in Hstore; auto.
    assert ((Wasm_int.N_of_uint i32m (N_to_i32 gmp_v)) = gmp_v) as Heq. {
    unfold nat_to_i32. cbn. rewrite Wasm_int.Int32.Z_mod_modulus_id; lia. }
    rewrite Heq in Hstore.
    unfold nat_to_value in Hstore.
    unfold nat_to_i32 in Hstore.
    rewrite -Hmemsame. eassumption. lia. reflexivity. }
  }
Qed.


Inductive const_val_list : list term.val -> store_record -> frame -> list u32 -> Prop :=
  | CV_nil  : forall s f, const_val_list [] s f []
  | CV_cons : forall s f v vs n w ns,
       repr_val_LambdaANF_Wasm v s (f_inst f) w ->
       n = wasm_value_to_u32 w ->
       const_val_list vs s f ns ->
       const_val_list (v::vs) s f (n::ns).

Lemma map_const_const_list : forall args,
  const_list [seq AI_basic (BI_const_num (N_to_value a)) | a <- args].
Proof.
  induction args; auto.
Qed.

Lemma const_val_list_length_eq : forall vs s f ns,
  const_val_list vs s f ns -> length vs = length ns.
Proof.
  induction vs; intros.
  - inv H. reflexivity.
  - cbn. inv H. now erewrite IHvs.
Qed.

Lemma const_val_list_nth_error : forall vs s f ns v j,
  const_val_list vs s f ns ->
  nth_error vs j = Some v ->
  exists w, repr_val_LambdaANF_Wasm v s (f_inst f) w /\
            nth_error [seq (VAL_num (N_to_value i)) | i <- ns] j =
               Some (VAL_num (VAL_int32 (wasm_value_to_i32 w))).
Proof.
  induction vs; intros.
  - destruct j; inv H0.
  - inv H. destruct j.
    + (* j=0*)
      inv H0. cbn.
      intros. exists w. eauto.
    + (* j=S j'*)
      cbn. eapply IHvs; eauto.
Qed.

Lemma rel_env_app_letapp {lenv} : forall f t ys rho sr fr fds x e,
  @rel_env_LambdaANF_Wasm lenv (Eletapp x f t ys e) rho sr fr fds ->
  @rel_env_LambdaANF_Wasm lenv (Eapp f t ys) rho sr fr fds.
Proof.
  intros ? ? ? ? ? ? ? ? ? [Hfun1 [Hfun2 Hvar]]. split; auto. split; auto.
  intros x' Hocc Hfd.
  assert (Hocc': occurs_free (Eletapp x f t ys e) x'). { inv Hocc; constructor; cbn; auto. }
  now destruct (Hvar _ Hocc' Hfd) as [v' [w [Hrho [Hloc Hval]]]].
Qed.

Lemma fun_args_reduce {lenv} : forall state fr sr fds (ys : seq term.var) rho vs f t args_instr,
  INV sr fr ->
  get_list ys rho = Some vs ->
  domains_disjoint lenv fenv ->
  (forall f, (exists res, find_def f fds = Some res) <-> (exists i, fenv ! f = Some i)) ->
  (forall a v, rho ! a = Some v -> find_def a fds <> None -> v = Vfun (M.empty term.val) fds a) ->
  @rel_env_LambdaANF_Wasm lenv (Eapp f t ys) rho sr fr fds ->
  @repr_fun_args_Wasm fenv nenv lenv ys args_instr ->
  exists args,
    reduce_trans (state, sr, fr, map AI_basic args_instr)
                 (state, sr, fr, (map (fun a => AI_basic (BI_const_num (N_to_value a))) args))
    /\ const_val_list vs sr fr args.
Proof.
  intros ? ? ? ? ? ? ? ? ? ? Hinv Hgetlist HenvsDisjoint HfenvWf HfenvRho HrelE Hargs.
  generalize dependent f. generalize dependent rho. generalize dependent sr.
  revert vs t fr state. induction Hargs; intros.
  { inv Hgetlist. exists []. cbn. split. apply rt_refl. constructor. }
  { (* var *) destruct vs.
    { cbn in Hgetlist. destruct (rho ! a), (get_list args rho); inv Hgetlist. }
    assert (HrelE': @rel_env_LambdaANF_Wasm lenv (Eapp f t args) rho sr fr fds). {
          destruct HrelE as [Hfun1 [Hfun2 Hvar]]. split. assumption. split. assumption.
          intros. assert (Hocc : (occurs_free (Eapp f t (a :: args)) x)). {
          inv H0. constructor. constructor. right. assumption.  }
           destruct (Hvar _ Hocc) as [val [wal [Hrho' [Hlocals Hval]]]]; auto. }
    assert (Hgetlist': get_list args rho = Some vs). {
      cbn in Hgetlist. destruct (rho ! a), (get_list args rho); inv Hgetlist; auto. }
    assert (Ha: rho ! a = Some v). {
      cbn in Hgetlist. destruct (rho ! a), (get_list args rho); inv Hgetlist; auto.
    }
    have IH := IHHargs _ _ _ state _ Hinv _ Hgetlist' HfenvRho _ HrelE'.
    destruct IH as [args' [Hred HconstL]].
    unfold rel_env_LambdaANF_Wasm in HrelE.

    destruct HrelE as [_ [_ Hvar]].
    assert (Hocc: occurs_free (Eapp f t (a :: args)) a). { constructor. cbn. auto. }
    assert (Hf: find_def a fds = None). { apply HfenvWf_None with (f:=a) in HfenvWf.
      rewrite HfenvWf. inv H. unfold translate_var in H0.
      destruct (lenv ! a) eqn:Ha'; rewrite Ha' in H0; inv H0.
      now apply HenvsDisjoint in Ha'. }
    destruct (Hvar _ Hocc Hf) as [val [wal [Hrho' [Hlocs Hval]]]].
    assert (v = val) by congruence. subst val.
    destruct Hlocs as [a'' [Ha'' HlVar]].
    have H' := repr_var_det _ _ _ _ Ha'' H. subst a''.

    exists (wasm_value_to_u32 wal :: args'). cbn. split.
    dostep_nary 0. apply r_local_get. eassumption.
    separate_instr. apply app_trans_const; auto.
    econstructor; eauto.
  }
  { (* fun *) destruct vs.
    - cbn in Hgetlist. destruct (rho ! a), (get_list args rho); inv Hgetlist.
    - assert (HrelE': @rel_env_LambdaANF_Wasm lenv (Eapp f t args) rho sr fr fds). {
        destruct HrelE as [Hfun1 [Hfun2 Hvar]]. split. assumption. split. assumption.
        intros. assert (Hocc : (occurs_free (Eapp f t (a :: args)) x)). {
          inv H0. constructor. constructor. right. assumption. } auto. }
      assert (Hgetlist': get_list args rho = Some vs). {
        cbn in Hgetlist. destruct (rho ! a), (get_list args rho); inv Hgetlist; auto. }
      assert (Ha: rho ! a = Some v). {
        cbn in Hgetlist. destruct (rho ! a), (get_list args rho); inv Hgetlist; auto. }
      have IH := IHHargs _ _ _ state _ Hinv _ Hgetlist' HfenvRho _ HrelE'.
      destruct IH as [args' [Hred HconstL]].

      exists (a' :: args'). split. cbn.
      apply app_trans_const with (lconst := [AI_basic (BI_const_num (N_to_value a'))]); auto.
      assert (v = Vfun (M.empty _) fds a). {
        specialize HfenvWf with a. inv H. unfold translate_var in H0.
        destruct (fenv ! a) eqn:Ha'; rewrite Ha' in H0; inv H0.
        destruct HfenvWf as [H H0]. edestruct H0; eauto.
        eapply HfenvRho; auto. congruence.
      }
      subst v.
      destruct HrelE as [Hfun1 [Hfun2 _]].
      eapply Hfun1 in Ha. 2:apply rt_refl.
      destruct Ha as [_ [_ Ha]].
      apply Hfun2 in Ha.
      destruct Ha as [a'' [HtransF Hrepr]]. econstructor; eauto.
      cbn. now eapply repr_funvar_det.
   }
Qed.


(* Supported primitive functions do not return functions *)
Definition prim_funs_env_returns_no_funvalues (prim_funs : M.t (list val -> option val)) : Prop :=
  forall rho fds f f' f0 vs v,
    M.get f prim_funs = Some f' ->
    f' vs = Some v ->
    ~ subval_or_eq (Vfun rho fds f0) v.

(* for fn values returned by the fn body of Eletapp, it holds that rho=M.empty etc. *)
Lemma step_preserves_empty_env_fds : forall rho e v c fds rho' fds' f'  (pfs : M.t (list val -> option val)),
  (forall (x : positive) (rho' : M.t val) (fds' : fundefs) (f' : var) (v0 : val),
	  rho ! x = Some v0 ->
	  subval_or_eq (Vfun rho' fds' f') v0 ->
	  fds' = fds /\ rho' = M.empty val /\ name_in_fundefs fds f') ->
	(forall e' e'' eAny fdsAny,
	  (subterm_or_eq e' e \/ (subterm_or_eq e' e'' /\ dsubterm_fds_e e'' fds))
	  -> e' <> Efun fdsAny eAny) ->
        prim_funs_env_returns_no_funvalues pfs ->
  bstep_e pfs cenv rho e v c ->
  subval_or_eq (Vfun rho' fds' f') v ->
  fds' = fds /\ rho' = M.empty val /\ name_in_fundefs fds f'.
Proof.
  intros ? ? ? ? ? ? ? ? ? Hrho HnoFd Hpfs Hstep Hsubval.
  generalize dependent f'. generalize dependent fds'. generalize dependent rho'.
  induction Hstep; intros; subst.
  - (* Econstr *)
    eapply IHHstep; try eassumption.
    + intros x0 ???? H0 H1. destruct (var_dec x0 x).
      * (* x = x0 *)
        subst x0. rewrite M.gss in H0. inv H0.
        apply subval_or_eq_fun in H1. destruct H1 as [v' [H2 H3]].
        have H' := get_list_In_val _ _ _ _ H H3. destruct H' as [y [HyIn Hrho']].
        have H' := Hrho _ _ _ _ _ Hrho' H2. by assumption.
      * (* x <> x0 *)
        rewrite M.gso in H0; auto.
        have H' := Hrho _ _ _ _ _ H0 H1. by assumption.
    + intros ? ? ? ? [H' | H']; last now eapply HnoFd.
      eapply HnoFd. left. eapply rt_trans; try eassumption.
      apply rt_step. by constructor.
  - (* Eproj *)
    eapply IHHstep; try eassumption.
    + intros. destruct (var_dec x x0).
      * (* x = x0 *)
        subst x0. rewrite M.gss in H1. symmetry in H1. inv H1.
        apply nthN_In in H0.
        have H' := subval_or_eq_constr _ _ _ t H2 H0.
        by eauto.
      * (* x <> x0*)
        by rewrite M.gso in H1; eauto.
    + intros ? ? ? ? [H' | H']. 2: now eapply HnoFd.
      eapply HnoFd. left. eapply rt_trans; try eassumption.
      apply rt_step. by constructor.
  - (* Ecase *)
    eapply IHHstep; try eassumption.
    intros ? ? ? ? [H' | H']. 2: now eapply HnoFd.
    eapply HnoFd. left. eapply rt_trans; try eassumption.
    apply rt_step. econstructor. now apply findtag_In_patterns.
  - (* Eapp *)
    assert (subval_or_eq (Vfun rho' fl f') (Vfun rho' fl f')). {
      constructor. constructor. now eapply find_def_name_in_fundefs.
    }
    have H' := Hrho _ _ _ _ _ H H3. destruct H'. subst.
    eapply IHHstep; try eassumption.
    + intros.
      assert (Hdec: decidable_eq var). { intros n m.
        unfold Decidable.decidable. now destruct (var_dec n m). }
      have H' := In_decidable Hdec x xs. destruct H'.
      * (* In x xs *)
        have H' := set_lists_In _ _ _ _ _ _ H7 H4 H2.
        destruct (get_list_In_val _ _ _ _ H0 H') as [y [HyIn HyRho]].
        by eauto.
      * (* ~In x xs *)
        have H' := set_lists_not_In _ _ _ _ _ H2 H7.
        rewrite H4 in H'.
        erewrite def_funs_find_def in H'. 2: {
          intro Hcontra. eapply def_funs_not_find_def  in Hcontra.
          erewrite Hcontra in H'. destruct H5. subst. inv H'. }
        inv H'.
        have H' := set_lists_not_In _ _ _ _ _ H2 H7.
        rewrite H4 in H'.
        apply subval_fun in H6. destruct H6 as [ff [Heq Hfundef]].
        now inv Heq.
        apply def_funs_spec in H'. destruct H' as [[? ?] | [? ?]]; auto.
        destruct H5. now subst.
    + intros ? ? ? ? [H' | H']. 2: now eapply HnoFd.
      eapply HnoFd. right. split. eassumption.
      now eapply find_def_dsubterm_fds_e.
  - (* Eletapp *)
    eapply IHHstep2; try eassumption.
    + intros x0 ???? H3 H4.
      destruct (var_dec x x0); last (* x <> x0 *) by rewrite M.gso in H3; eauto.
      (* x = x0 *)
      subst x0. rewrite M.gss in H3. symmetry in H3. inv H3.
      (* same as Eapp *)
      assert (subval_or_eq (Vfun rho' fl f') (Vfun rho' fl f')). {
        constructor. constructor. now eapply find_def_name_in_fundefs.
      }
      have H' := Hrho _ _ _ _ _ H H3. destruct H'. subst.
      eapply IHHstep1; try eassumption.
      * intros x0 ???? H5 H7. assert (Hdec: decidable_eq var). { intros n m.
          unfold Decidable.decidable. now destruct (var_dec n m). }
        have H' := In_decidable Hdec x0 xs. destruct H'.
        -- (* In x0 xs *)
           have H' := set_lists_In _ _ _ _ _ _ H8 H5 H2.
           destruct (get_list_In_val _ _ _ _ H0 H') as [y [HyIn HyRho]].
           by eauto.
        -- (* ~In x0 xs *)
           have H' := set_lists_not_In _ _ _ _ _ H2 H8.
           rewrite H5 in H'.
           erewrite def_funs_find_def in H'. 2: {
             intro Hcontra. eapply def_funs_not_find_def  in Hcontra.
             erewrite Hcontra in H'. inv H'. destruct H6. now subst. }
           inv H'.
           have H' := set_lists_not_In _ _ _ _ _ H2 H8.
           rewrite H5 in H'.
           apply subval_fun in H7. destruct H7 as [ff [Heq Hfundef]].
           now inv Heq.
           apply def_funs_spec in H'. destruct H' as [[? ?] | [? Hcontra]].
           assumption. destruct H6. now subst.
      * intros ???? [H' | H']; last now eapply HnoFd.
        eapply HnoFd. right. split. eassumption.
        now eapply find_def_dsubterm_fds_e.
    + intros ? ? ? ? [H' | H']. 2: now eapply HnoFd.
      eapply HnoFd. left. eapply rt_trans. eassumption.
      apply rt_step. by constructor.
  - (* Efun: absurd *)
    exfalso. eapply HnoFd. left. apply rt_refl. reflexivity.
  - (* Eprim_val *) eapply IHHstep; eauto.
    + intros x0 ???? H H0. destruct (var_dec x0 x).
      * (* x = x0 *)
        subst x0. rewrite M.gss in H. inv H.
        now apply subval_or_eq_fun_not_prim in H0.
      * (* x <> x0 *) rewrite M.gso in H; auto. by eauto.
    + intros ? ? ? ? [H' | H']. 2: now eapply HnoFd.
      eapply HnoFd. left. eapply rt_trans; try eassumption.
      apply rt_step. by constructor.
  - (* Eprim *)
    eapply IHHstep; eauto.
    + intros x0 ???? H2 H3.
      destruct (var_dec x0 x); last (* x <> x0 *) by rewrite M.gso in H2; eauto.
      subst x0. rewrite M.gss in H2.
      inversion H2. subst v0.
      have H' := Hpfs _ _ _ _ _ _ _ H0 H1.
      specialize (H' rho' fds'0 f'1). contradiction.
    + intros ? ? ? ? [H' | H']. 2: now eapply HnoFd.
      eapply HnoFd. left. eapply rt_trans; try eassumption.
      apply rt_step. by constructor.
  - (* Ehalt *) by eauto.
  Unshelve. all: assumption.
Qed.

Lemma repr_expr_LambdaANF_Wasm_no_Efun_subterm {lenv} : forall e_body eAny mem,
  repr_expr_LambdaANF_Wasm lenv e_body mem eAny ->

  forall (e' eAny : exp) (fdsAny : fundefs),
  subterm_or_eq e' e_body ->
  e' <> Efun fdsAny eAny.
Proof.
  intros ??? Hexpr. revert mem eAny Hexpr.
  induction e_body using exp_ind'; intros.
  - (* Econstr *)
    inv Hexpr.
    have H' := IHe_body _ _ H10.
    apply rt_then_t_or_eq in H. destruct H as [H | H]. congruence.
    apply clos_trans_tn1 in H. inv H. inv H0.
    eapply H'. apply rt_refl. inv H0.
    apply clos_tn1_trans in H1. eapply H'. by apply t_then_rt.
  - (* Ecase [] *)
    apply rt_then_t_or_eq in H. destruct H; first congruence.
    apply clos_trans_tn1 in H. inv H. { inv H0. inv H2. }
    inv H0. by inv H3.
  - (* Ecase cons *)
    inv Hexpr. inv H3.
    + (* boxed *)
      inv H4.
      apply rt_then_t_or_eq in H. destruct H as [H | H]; first congruence.
      apply clos_trans_tn1 in H. inv H.
      { inv H0. destruct H3 as [H3 | H3].
        - inv H3. eapply IHe_body; first eassumption. apply rt_refl.
        - eapply IHe_body0. eapply Rcase_e; eauto. eapply rt_step. now econstructor. }
      { apply clos_tn1_trans in H1. inv H0. destruct H4 as [H4 | H4].
        - inv H4. eapply IHe_body; try eassumption. now apply t_then_rt.
        - eapply IHe_body0. eapply Rcase_e; eauto. eapply rt_trans. now apply t_then_rt.
          apply rt_step. now econstructor. }
    + (* unboxed *)
      inv H7.
      apply rt_then_t_or_eq in H. destruct H as [? | H]; first congruence.
      apply clos_trans_tn1 in H. inv H.
      { inv H0. destruct H3 as [H3 | H3].
        - inv H3. eapply IHe_body; try eassumption. apply rt_refl.
        - eapply IHe_body0. eapply Rcase_e; eauto.
          eapply rt_step. now econstructor. }
      { apply clos_tn1_trans in H1. inv H0. destruct H5 as [H5 | H5].
        - inv H5. eapply IHe_body; try eassumption. now apply t_then_rt.
        - eapply IHe_body0. eapply Rcase_e; eauto. eapply rt_trans. now apply t_then_rt.
          apply rt_step. now econstructor. }
  - (* Eproj *)
    inv Hexpr.
    have H' := IHe_body _ _ H7.
    apply rt_then_t_or_eq in H. destruct H as [H | H]. congruence.
    apply clos_trans_tn1 in H. inv H. inv H0.
    eapply H'. apply rt_refl. inv H0.
    apply clos_tn1_trans in H1. eapply H'. by apply t_then_rt.
  - (* Eletapp *)
    inv Hexpr.
    have H' := IHe_body _ _ H8. apply rt_then_t_or_eq in H.
    destruct H as [H|H]; first congruence. apply clos_trans_tn1 in H. inv H.
    inv H0. eapply H'. apply rt_refl. inv H0.
    eapply H'. apply clos_tn1_trans in H1. by apply t_then_rt.
  - (* Efun *) by inv Hexpr.
  - (* Eapp *)
    apply rt_then_t_or_eq in H. inv H; first congruence.
    apply clos_trans_tn1 in H0. inv H0. inv H. by inv H.
  - (* Eprim_val *)
    inv Hexpr.
    have H' := IHe_body _ _ H4.
    apply rt_then_t_or_eq in H.
    destruct H as [H|H]. congruence.
    apply clos_trans_tn1 in H. inv H.
    inv H0. eapply H'. apply rt_refl. inv H0.
    eapply H'. apply clos_tn1_trans in H1. now apply t_then_rt.
  - (* Eprim *)
    inv Hexpr.
    have H' := IHe_body _ _ H5.
    apply rt_then_t_or_eq in H.
    destruct H as [H|H]. congruence.
    apply clos_trans_tn1 in H. inv H.
    inv H0. eapply H'. apply rt_refl. inv H0.
    eapply H'. apply clos_tn1_trans in H1. now apply t_then_rt.
  - (* Ehalt *)
    apply rt_then_t_or_eq in H. destruct H; first congruence.
    apply clos_trans_tn1 in H. inv H. inv H0. by inv H0.
Qed.

Fixpoint select_nested_if (boxed : bool) (v : localidx) (ord : N) (es : list (N * list basic_instruction)) : list basic_instruction :=
  match es with
  | [] => [ BI_unreachable ]
  | (ord0, _) :: es' =>
      if N.eqb ord0 ord then
        create_case_nested_if_chain boxed v es
      else
        select_nested_if boxed v ord es'
  end.

Lemma create_case_nested_if_chain_repr_case_unboxed : forall v brs es,
  repr_case_unboxed v brs es ->
  create_case_nested_if_chain false v brs = es.
Proof.
  intros v brs.
  generalize dependent v.
  induction brs; intros.
  - inv H. reflexivity.
  - destruct a. inv H.
    cbn. apply IHbrs in H5. now rewrite H5.
Qed.

Lemma create_case_nested_if_chain_repr_case_boxed : forall v brs es,
  repr_case_boxed v brs es ->
  create_case_nested_if_chain true v brs = es.
Proof.
  intros v brs.
  generalize dependent v.
  induction brs; intros.
  - inv H. reflexivity.
  - destruct a. inv H.
    cbn. apply IHbrs in H5. now rewrite H5.
Qed.


Lemma unboxed_nested_if_chain_reduces : forall cl fAny y t e v lenv mem brs1 brs2 e2' f hs sr ord,
  lookup_N (f_locs f) v = Some (VAL_num (VAL_int32 (wasm_value_to_i32 (Val_unboxed (ord  * 2 + 1)%N)))) ->
  cenv_restricted cenv ->
  expression_restricted cenv (Ecase y cl) ->
  caseConsistent cenv cl t ->
  findtag cl t = Some e ->
  get_ctor_ord cenv t = Ret ord ->
  get_ctor_arity cenv t = Ret 0 ->
  @repr_branches cenv fenv nenv penv lenv v cl mem brs1 brs2 ->
  repr_case_unboxed v brs2 e2' ->
  exists e' e'',
    select_nested_if false v ord brs2 =
      [ BI_local_get v
      ; BI_const_num (nat_to_value (N.to_nat (2 * ord + 1)))
      ; BI_relop T_i32 (Relop_i ROI_eq)
      ; BI_if (BT_valtype None)
          e'
          e'' ]
    /\ (forall k (lh : lholed k),
        exists k0 (lh0 : lholed k0),
          reduce_trans (hs, sr, fAny, [AI_frame 0 f (lfill lh (map AI_basic e2'))])
                       (hs, sr, fAny, [AI_frame 0 f (lfill lh0 (map AI_basic e'))]))
    /\ repr_expr_LambdaANF_Wasm lenv e mem e'.
Proof.
  induction cl; first by move => ???????????????? //=.
  intros fAny y t e v lenv mem brs1 brs2 e2' f hs sr ord Hval HcenvRestr HcaseRestr
         HcaseConsistent Hfindtag Hord Hunboxed Hbranches Hunboxedcase.
  destruct a as [t0 e0].
  have HcaseRestr' := HcaseRestr.
  inv HcaseRestr.
  clear H1.
  have Hfindtag' := Hfindtag.
  cbn in Hfindtag.
  destruct (M.elt_eq t0 t).
  { (* t0 = t, enter the then-branch *)
    subst t0. inv Hfindtag.
    inv Hbranches.
    { (* Impossible case: t0 cannot be the tag of a non-nullary constructor *)
      assert (n=0) by congruence. lia. }
    inv Hunboxedcase.
    assert (ord0 = ord) by congruence. subst ord0.
    exists e', instrs_more.
    split. simpl.
    assert (create_case_nested_if_chain false v brs3 = instrs_more). { now apply create_case_nested_if_chain_repr_case_unboxed. }
    rewrite N.eqb_refl. now rewrite H.
    split=>//.
    intros.
    have Hlh := lholed_nested_label _ lh [seq AI_basic i | i <- e'] [::].
    destruct Hlh as [k' [lh' Hlheq]].
    exists k', lh'.
    (* Step through the if-then-else into the then-branch *)
    eapply reduce_trans_frame.
    eapply rt_trans. apply reduce_trans_label.
    dostep_nary 0. apply r_local_get. eauto.
    dostep_nary 2. constructor. apply rs_relop=>//.
    dostep'. constructor. apply rs_if_true.
    { rewrite N.mul_comm.
      unfold wasm_value_to_i32, wasm_value_to_u32, nat_to_value, nat_to_i32.
      unfold Wasm_int.Int32.eq.
      rewrite N_nat_Z. rewrite zeq_true.
      intro Hcontra. inv Hcontra. }
    dostep'. eapply r_block with (t1s:=[::]) (t2s:=[::])(vs:=[::]); auto.
    apply rt_refl.
    rewrite Hlheq. apply rt_refl.
  }
  { (* t0 <> t, enter the else branch (induction hypothesis) *)
    assert (Hrestr : expression_restricted cenv (Ecase y cl)). {
      constructor.
      inv HcaseRestr'.
      now inv H1.
    }
    inv Hbranches.
    { (* t0 is the tag of a non-nullary constructor, not even in the nested if-chain *)
      inv HcaseConsistent. eapply IHcl; eauto. }

    assert (HcaseConsistent' : caseConsistent cenv cl t). { inv HcaseConsistent. assumption. }
    inv Hunboxedcase.
    assert (Hord_neq : ord0 <> ord). {
      symmetry.
      eapply nullary_ctor_ords_in_case_disjoint with (cl:=((t0, e0)::cl)); eauto.
      cbn. destruct (M.elt_eq t0 t0). auto. contradiction. }
    have IH := IHcl fAny y t e v lenv mem brs1 brs3 instrs_more f hs sr ord  Hval HcenvRestr
               Hrestr HcaseConsistent' Hfindtag Hord Hunboxed H2 H7.
    destruct IH as [e1' [e'' [Hsel [Hred Hrep]]]].
    exists e1', e''.
    split.
    { unfold select_nested_if. apply N.eqb_neq in Hord_neq. rewrite Hord_neq.
      fold select_nested_if. assumption. }
    split=>//.
    intros.
    have Hlh := lholed_nested_label _ lh [seq AI_basic i | i <- instrs_more] [::].
    destruct Hlh as [k' [lh' Hlheq]].
    have Hred' := Hred k' lh'.
    destruct Hred' as [k0 [lh0 Hstep]].
    exists k0, lh0.
    (* Step through the if-then-else into the else-branch *)
    eapply rt_trans. apply reduce_trans_frame. apply reduce_trans_label. eapply rt_trans.
    dostep_nary 0. apply r_local_get. eauto.
    dostep_nary 2. constructor. apply rs_relop=>//.
    dostep'. constructor. apply rs_if_false.
    { (* (t0 << 1) + 1 <> (t << 1) *)
      rewrite N.mul_comm. cbn.
      unfold wasm_value_to_i32, wasm_value_to_u32, nat_to_i32, Wasm_int.Int32.eq.
      rewrite zeq_false. reflexivity.
      assert (H': (-1 < (Z.of_N ord0) < Wasm_int.Int32.half_modulus)%Z). {
        eapply ctor_ord_restricted with (ord:=ord0) in HcaseRestr'; eauto.
        now left. }
      assert (H'': (-1 < (Z.of_N ord) < Wasm_int.Int32.half_modulus)%Z). {
        cbn in Hfindtag'. destruct (M.elt_eq t0 t)=>//.
        eapply ctor_ord_restricted in Hord; eauto.
        eapply findtag_In; eauto. }
      simpl_modulus_in H'. simpl_modulus_in H''.
      destruct ord, ord0; auto; rewrite N_nat_Z;
        try rewrite !Wasm_int.Int32.unsigned_repr; simpl_modulus; cbn; lia. }
    dostep'. eapply r_block with (t1s:=[::]) (t2s:=[::])(vs:=[::]); auto.
    apply rt_refl. apply rt_refl.
    rewrite Hlheq.
    apply Hstep.
  }
Qed.

Lemma boxed_nested_if_chain_reduces :
  forall cl fAny y t vs e addr v lenv mem brs1 brs2 e1' (hs : host_state) (sr : store_record) (f : frame) ord,
    INV_linear_memory sr f ->
    repr_val_LambdaANF_Wasm (Vconstr t vs) sr (f_inst f) (Val_ptr addr) ->
    lookup_N (f_locs f) v = Some (VAL_num (VAL_int32 (wasm_value_to_i32 (Val_ptr addr)))) ->
    cenv_restricted cenv ->
    expression_restricted cenv (Ecase y cl) ->
    caseConsistent cenv cl t ->
    get_ctor_ord cenv t = Ret ord ->
    findtag cl t = Some e ->
    @repr_branches cenv fenv nenv penv lenv v cl mem brs1 brs2 ->
    repr_case_boxed v brs1 e1' ->
    exists e' e'',
      select_nested_if true v ord brs1 =
        [ BI_local_get v
        ; BI_load T_i32 None {| memarg_offset:=0%N; memarg_align:=2%N |}
        ; BI_const_num (nat_to_value (N.to_nat ord))
        ; BI_relop T_i32 (Relop_i ROI_eq)
        ; BI_if (BT_valtype None)
            e'
            e'' ]
      /\ (forall k (lh : lholed k),
            exists k0 (lh0 : lholed k0),
            reduce_trans (hs, sr, fAny, [AI_frame 0 f (lfill lh (map AI_basic e1'))]) (hs, sr, fAny, [AI_frame 0 f (lfill lh0 (map AI_basic e'))]))
      /\ repr_expr_LambdaANF_Wasm lenv e mem e'.
Proof.
  induction cl=>//.
  intros fAny y t vs e addr v lenv mem brs1 brs2 e1' hs sr f ord Hmem Hval Hlocs HcenvRestr HcaseRestr HcaseConsistent Hord Hfindtag Hbranches Hboxedcase.
  destruct a as [t0 e0].
  have HcaseRestr' := HcaseRestr.
  inv HcaseRestr.
  have Hmem' := Hmem.
  destruct Hmem as [Hsmem [m [Hmem0 Hmemsize]]].
  have Hfindtag' := Hfindtag.
  have Hval' := Hval.
  assert (exists arity, get_ctor_arity cenv t = Ret arity /\ arity > 0). {
    inv Hval. by exists arity.
  }
  destruct H as [n [Hn Hngt0]].
  cbn in Hfindtag.
  destruct (M.elt_eq t0 t).
  { (* t0 = t, enter the then-branch *)
    subst t0. inv Hfindtag.
    inv Hbranches.
    2: { (* Impossible case: t cannot be the tag of a nullary constructor *)
      assert (n=0) by congruence. lia. }
    assert (ord0 = ord) by congruence. subst ord0.
    assert (n0 = n) by congruence. subst n0.
    clear Hn Hngt0.
    inv Hboxedcase.
    exists e', instrs_more.
    split. cbn.
    assert (create_case_nested_if_chain true v brs0 = instrs_more). { now apply create_case_nested_if_chain_repr_case_boxed. }
    rewrite N.eqb_refl. congruence.
    split=>//.
    intros.
    have Hlh := lholed_nested_label _ lh (map AI_basic e') [::].
    destruct Hlh as [k' [lh' Hlheq]].
    exists k', lh'.

    (* Step through the if-then-else into the then-branch *)
    eapply reduce_trans_frame.
    eapply rt_trans. apply reduce_trans_label.
    dostep_nary 0. apply r_local_get. eauto.
    inv Hval.
    solve_eq m m0.
    unfold load_i32 in H20.
    destruct (load m addr (N.of_nat 0) 4) eqn:Hload. 2: { cbn in Hload. rewrite Hload in H20. inv H20. }
    dostep_nary 1. eapply r_load_success; try eassumption.
    assert (addr = (Wasm_int.N_of_uint i32m (wasm_value_to_i32 (Val_ptr addr)))). {
      cbn. rewrite Wasm_int.Int32.Z_mod_modulus_id; lia.
    }
    rewrite <- H. apply Hload.
    dostep_nary 2. constructor. apply rs_relop=>//.
    dostep'. constructor. apply rs_if_true. {
      (* Check that ord = t *)
      cbn.
      unfold nat_to_i32.
      unfold Wasm_int.Int32.eq.
      cbn in Hload.
      rewrite Hload in H20.
      injection H20 => H20'.
      destruct (zeq (Wasm_int.Int32.unsigned (Wasm_int.Int32.repr (decode_int b)))
                  (Wasm_int.Int32.unsigned (Wasm_int.Int32.repr (Z.of_nat (N.to_nat ord))))) eqn:Heq.
      discriminate.
      replace ord0 with ord in H20' by congruence.
      contradiction.
    }
    dostep'. eapply r_block with (t1s:=[::]) (t2s:=[::])(vs:=[::]); auto. apply rt_refl.
    rewrite Hlheq. apply rt_refl.
  }
  { (* t0 <> t, enter the else branch (induction hypothesis) *)
    assert (Hrestr : expression_restricted cenv (Ecase y cl)). {
      constructor.
      inv HcaseRestr'.
      now inv H1.
    }
    inv Hbranches.
    2: { (* t0 is the tag of a nullary constructor, not even in the nested if-chain *)
      inv HcaseConsistent. eapply IHcl; eauto. }
    {
      assert (HcaseConsistent' : caseConsistent cenv cl t). { inv HcaseConsistent. assumption. }
      inv Hboxedcase.
      have IH := IHcl fAny y t vs e addr v lenv mem brs0 brs2 instrs_more hs sr f ord Hmem' Hval Hlocs HcenvRestr Hrestr HcaseConsistent' Hord Hfindtag H3 H8.
      destruct IH as [e0' [e'' [Hsel [Hred Hrep]]]].
      exists e0', e''.
      split.
      unfold select_nested_if.
      assert (Hord_neq : ord <> ord0).
      {
        eapply nonnullary_ctor_ords_in_case_disjoint with (cl:=((t0, e0)::cl)); eauto.
        cbn. destruct (M.elt_eq t0 t0). auto. contradiction.
      }
      assert (Hord_neq' : ord0 <> ord) by auto.
      apply N.eqb_neq in Hord_neq'. rewrite Hord_neq'. fold select_nested_if. assumption.
      split=>//.
      intros.
      have Hlh := lholed_nested_label _ lh [seq AI_basic i | i <- instrs_more] [::].
      destruct Hlh as [k' [lh' Hlheq]].
      have Hred' := Hred k' lh'.
      destruct Hred' as [k0 [lh0 Hstep]].
      exists k0, lh0.

      (* Step through the if-then-else into the else-branch *)
      eapply rt_trans. apply reduce_trans_frame. apply reduce_trans_label. eapply rt_trans.
      dostep_nary 0. apply r_local_get. eauto.
      inv Hval.
      solve_eq m m0.
      unfold load_i32 in H20.
      destruct (load m addr (N.of_nat 0) 4) eqn:Hload. 2: { cbn in Hload. rewrite Hload in H20. inv H20. }
      dostep_nary 1. eapply r_load_success; try eassumption.
      assert (addr = (Wasm_int.N_of_uint i32m (wasm_value_to_i32 (Val_ptr addr)))) as H. {
        cbn. rewrite Wasm_int.Int32.Z_mod_modulus_id; lia.
      }
      rewrite <- H. apply Hload.
      dostep_nary 2. constructor. apply rs_relop=>//.
      dostep'. constructor. apply rs_if_false.
      { (* Check that the ord of t0 is not equal to ord of t;
         requires some arithmetic gymnastics  *)
        assert (ord1 = ord) by congruence. subst ord1.
        assert ((-1 < Z.of_N ord < Wasm_int.Int32.half_modulus)%Z). {
          have Hr := Forall_forall (fun p : ctor_tag * exp =>
             ctor_ordinal_restricted cenv (fst p) /\
             expression_restricted cenv (snd p)) ((t0, e0) :: cl).
          inv HcaseRestr'. cbn.
          destruct Hr as [Hr' _].
          apply Hr' with (x:=(t, e)) in H2.
          unfold ctor_ordinal_restricted in H2. cbn in H2.
          destruct H2 as [HordRestr _].
          apply HordRestr in Hord.
          cbn in Hord.
          lia.
          inv Hfindtag.
          destruct (M.elt_eq t0 t).
          - subst t0. inv H1. now constructor.
          - apply findtag_In in H0=>/=. tauto.
        }
        assert ((-1 < Z.of_N ord0 < Wasm_int.Int32.half_modulus)%Z). {
          have Hr := Forall_forall (fun p : ctor_tag * exp =>
             ctor_ordinal_restricted cenv (fst p) /\
             expression_restricted cenv (snd p)) ((t0, e0) :: cl).
          inv HcaseRestr'.
          destruct Hr as [Hr' _].
          apply Hr' with (x:=(t0, e0)) in H17. cbn.
          destruct H17 as [HordRestr _].
          apply HordRestr in H4.
          cbn in H4.
          lia.
          now constructor.
        }

        cbn.
        unfold nat_to_i32.
        unfold Wasm_int.Int32.eq.
        cbn in Hload.
        rewrite Hload in H20.
        injection H20 => H20'.
        destruct (zeq (Wasm_int.Int32.unsigned (Wasm_int.Int32.repr (decode_int b)))
                    (Wasm_int.Int32.unsigned (Wasm_int.Int32.repr (Z.of_nat (N.to_nat ord0))))); auto.
        inv e1.
        assert (ord <> ord0).
        {
        eapply nonnullary_ctor_ords_in_case_disjoint with (cl:=((t0, e0)::cl)); eauto.
        cbn. destruct (M.elt_eq t0 t0). auto. contradiction.
        }
        rewrite H20' in H17.
        rewrite Wasm_int.Int32.Z_mod_modulus_id in H17.
        2: { simpl_modulus. cbn. simpl_modulus_in H. lia. }
        rewrite Wasm_int.Int32.Z_mod_modulus_id in H17.
        2: { simpl_modulus. cbn. simpl_modulus_in H0. lia. }
        lia.
      }
      dostep'. eapply r_block with (t1s:=[::]) (t2s:=[::])(vs:=[::]); auto.
      eapply rt_refl. apply rt_refl.
      rewrite Hlheq.
      apply Hstep.
    }
  }
Qed.

Definition fds_translated_correctly fds sr finst := forall a t ys e,
  find_def a fds = Some (t, ys, e) ->
  exists fidx, repr_funvar a fidx /\
               repr_val_LambdaANF_Wasm (Vfun (M.empty term.val) fds a) sr finst (Val_funidx fidx).

Definition fds_restricted fds := forall a t ys e,
  find_def a fds = Some (t, ys, e) ->
  expression_restricted cenv e /\
  (forall x, occurs_free e x -> In x ys \/ find_def x fds <> None) /\
  NoDup (ys ++ collect_local_variables e ++ collect_function_vars (Efun fds e)).

(* This is assumed here, the proof was moved to LambdaANF_to_Wasm_primitives_correct.v *)
Definition primitive_operation_reduces pfs : Prop :=
  forall lenv state s f fds f' (x : var) (x' : localidx) (p : prim) op_name str b op_arr op
         (ys : list var) (e : exp) (vs : list val) (rho : env) (v : val) instrs mem,
    M.get p pfs = Some f' ->
    M.get p penv = Some (Pipeline_utils.mk_primitive op_name str b op_arr) ->
    KernameMap.find op_name primop_map = Some op ->
    map_injective lenv ->
    domains_disjoint lenv fenv ->
    (forall f, (exists res, find_def f fds = Some res) <-> (exists i, fenv ! f = Some i)) ->
    (forall var varIdx, @repr_var nenv lenv var varIdx -> N.to_nat varIdx < length (f_locs f)) ->
    @repr_var nenv lenv x x' ->
    @rel_env_LambdaANF_Wasm lenv (Eprim x p ys e) rho s f fds ->
    @repr_primitive_operation nenv lenv op ys instrs ->
    INV s f ->
    min_available_memory s (f_inst f) (52 + mem)%N ->
    get_list ys rho = Some vs ->
    f' vs = Some v ->
    exists s' f',
      reduce_trans (state, s, f, map AI_basic (instrs ++ [ BI_local_set x' ])) (state, s', f', []) /\
      INV s' f' /\
      f_inst f = f_inst f' /\
      s_funcs s = s_funcs s' /\
      min_available_memory s' (f_inst f) mem /\
      @rel_env_LambdaANF_Wasm lenv e (M.set x v rho) s' f' fds /\
      (forall (wal : wasm_value) (val : term.val),
         repr_val_LambdaANF_Wasm val s (f_inst f) wal ->
         repr_val_LambdaANF_Wasm val s' (f_inst f') wal) /\
      (exists wal,
         f' = {|f_locs := set_nth (VAL_num (VAL_int32 (wasm_value_to_i32 wal))) (f_locs f)
                                  (N.to_nat x') (VAL_num (VAL_int32 (wasm_value_to_i32 wal)))
               ; f_inst := f_inst f
               |} /\
      repr_val_LambdaANF_Wasm v s' (f_inst f') wal).

(* GENERALIZED CORRECTNESS THEOREM *)
Theorem repr_bs_LambdaANF_Wasm_related :
  (* rho is environment containing outer fundefs. e is body of LambdaANF program *)
  forall lenv pfs (rho : eval.env) (v : term.val) (e : exp) (memAvail : N) (n : nat) (vars : list term.var) (fds : fundefs)
                               fAny k (lh : lholed k),
    primitive_operation_reduces pfs ->
    cenv_restricted cenv ->
    (* restrictions on prim_funs env *)
    prim_funs_env_returns_no_funvalues pfs ->
    (* restrictions on lenv, fenv *)
    map_injective lenv ->
    domains_disjoint lenv fenv ->
    (* bound vars globally unique *)
    vars = (collect_local_variables e) ++ (collect_function_vars (Efun fds e))%list ->
    NoDup vars ->
    (* fenv maps f vars to the index of the corresponding wasm function *)
    (forall f, (exists res, find_def f fds = Some res) <-> (exists i, fenv ! f = Some i)) ->
    (* find_def a fds <> None, rho ! a imply fn value *)
    (forall (a : positive) (v : term.val), rho ! a = Some v -> find_def a fds <> None ->
             v = Vfun (M.empty term.val) fds a) ->

    (* restricts size of e so all vars fit in i32s *)
    expression_restricted cenv e ->
    fds_restricted fds ->

    (* SSA form, let-bound vars not assigned yet *)
    (forall x, In x (collect_local_variables e) -> rho ! x = None) ->
    bstep_e pfs cenv rho e v n ->  (* e n-steps to v *)
    forall (hs : host_state) (sr : store_record) (f : frame) (e' : list basic_instruction),

      (* translated fds in sr *)
      fds_translated_correctly fds sr (f_inst f) ->

      (* local vars from lenv in bound *)
      (forall var varIdx, @repr_var nenv lenv var varIdx -> N.to_nat varIdx < length (f_locs f)) ->

      (* invariants *)
      INV sr f ->
      (* memory known to be available statically *)
      min_available_memory sr (f_inst f) memAvail ->

      (* translate_body e returns instructions *)
      repr_expr_LambdaANF_Wasm lenv e memAvail e' ->

      (* relates a LambdaANF evaluation environment [rho] to a Wasm environment (store,frame) *)
      @rel_env_LambdaANF_Wasm lenv e rho sr f fds ->
      exists (sr' : store_record) (f' : frame) k' (lh' : lholed k'),
        reduce_trans (hs, sr,  fAny, [AI_frame 0 f (lfill lh (map AI_basic e'))])
                     (hs, sr', fAny, [AI_frame 0 f' (lfill lh' [::AI_basic BI_return])]) /\
        (* value sr'.res points to value related to v *)
        result_val_LambdaANF_Wasm v sr' (f_inst f) /\
        f_inst f = f_inst f' /\ s_funcs sr = s_funcs sr' /\
        (* previous values are preserved *)
        (forall wal val, repr_val_LambdaANF_Wasm val sr (f_inst f) wal ->
                         repr_val_LambdaANF_Wasm val sr' (f_inst f') wal) /\
        (* INV holds if program will continue to run *)
        (INV_glob_out_of_mem_is_zero sr' f' -> INV sr' f').
Proof with eauto.
  intros lenv pfs rho v e memAvail n _ fds fAny k lh HprimOpReduce HcenvRestr HprimFunsRet
    HlenvInjective HenvsDisjoint -> Hnodup HfenvWf HfenvRho HeRestr HfdsRestr Hunbound Hev.
  generalize dependent lenv. generalize dependent lh. revert k fAny memAvail.
  induction Hev; intros k fAny mem lh lenv HlenvInjective HenvsDisjoint state sr fr instructions
                        Hfds HlocInBound Hinv HmemAvail Hrepr_e HrelE.
  - (* Econstr *)
    inversion Hrepr_e.
    inversion H13.
    { (* boxed constructor *)
      assert (Hmaxargs: (Z.of_nat (length ys) <= max_constr_args)%Z). { now inv HeRestr. }
      subst t0 x0 vs0 e0 mem0 x'0 vs1 t1 scont. rename H12 into Hx'. rename H11 into Hexp.
      assert (arity = arity0) by congruence. subst arity0. subst arity.

      cbn. rewrite map_cat.

      (* prepare calling memory_grow_reduce *)
      have I := Hinv. destruct I as [_[_[_[Hgmp_w[_[Hmut[_[_[_[HfnsBound[_[_[_[_ [HfuncGrow _]]]]]]]]]]]]]]].
      assert (HpageSize: (constr_size < page_size)%N). {
        unfold get_ctor_size in H6. rewrite H5 in H6.
        inv H6.
        destruct (length ys =? 0)=>//.
        unfold max_constr_args, page_size in *. lia.
      }

     destruct (i32_glob_implies_i32_val _ _ _ gmp_i32_glob Hgmp_w Hmut) as [g' Hgmp].
     destruct (i32_exists_N g') as [gmp [-> HgmpBound]].

      have Hgrowmem := memory_grow_reduce state sr _ _ _ _ _ _ HpageSize HmemAvail H8 Hinv Hgmp HgmpBound.
      destruct Hgrowmem as [[s' [Hred [Hsfuncs [HvalPreserved [Hinv' Henoughmem]]]]]
                            | HRedRet].

      { (* grow mem success *)
        (* invariants after reducing grow *)
        have I := Hinv'. destruct I as [_ [_ [_ [_ [_ [_ [Hlinmem _]]]]]]].
        destruct Hlinmem as [Hmem1 [m [Hmem2 [size [Hmem3 [Hmem4 Hmem5]]]]]].
        have HenoughM := Henoughmem _ Hmem2. destruct HenoughM as [Hgmp' HenoughM]. clear Henoughmem.

        assert (HrelE' : (forall y : var,
             In y ys ->
             find_def y fds = None ->
             exists (v6 : term.val) (val : wasm_value),
               rho ! y = Some v6 /\
               @stored_in_locals lenv y val fr /\
               repr_val_LambdaANF_Wasm v6 s' (f_inst fr) val)). {
                destruct HrelE as [_ Hvar]. intros.
          assert (Hocc: occurs_free (Econstr x t ys e) y) by (constructor; auto).
          apply Hvar in Hocc; auto. destruct Hocc as [val [wal [Hrho [Hloc Hval]]]].
          exists val, wal. by repeat split; auto.
        }

        assert (HfVal' : (forall (y : positive) (y' : funcidx) (v : term.val),
             rho ! y = Some v ->
             repr_funvar y y' ->
             repr_val_LambdaANF_Wasm v s' (f_inst fr) (Val_funidx y'))). {
          intros. destruct HrelE as [Hfun1 [Hfun2 _]].
          assert (Hfd: (exists i : N, fenv ! y = Some i)). {
            inv H2. unfold translate_var in H3. destruct (fenv ! y) eqn:Hy; rewrite Hy in H3=>//.
            now exists f. }
          apply HfenvWf in Hfd. apply notNone_Some in Hfd.

           have H' := HfenvRho _ _ H1 Hfd. subst v0.
           apply notNone_Some in Hfd. destruct Hfd as [[[f' ys''] e''] ?H].

           assert (Hsubval: subval_or_eq (Vfun (M.empty _) fds y)
            (Vfun (M.empty term.val) fds y)) by constructor.

           have H' := Hfun1 _ _ _ _ _ H1 Hsubval. destruct H' as [_ [_ H']].
           apply Hfun2 in H'.
           destruct H' as [i [HvarI Hval]].
           assert (i = y') by (eapply repr_funvar_det; eassumption). subst i.
           eapply val_relation_func_depends_on_funcs; try apply Hval. auto.
        }

        have Hconstr := store_constr_reduce state _ _ _ _ _ _ t _ _ _ _ _ _ _ H6 H14 H5 H16 Logic.eq_refl HenvsDisjoint HfenvWf Hinv'
        Hmem2 Hgmp' HenoughM HrelE' Hmaxargs H17 H HfVal'.
        destruct Hconstr as [s_v [Hred_v [Hinv_v [Hfuncs' [HmemLen [HvalPreserved' [[cap_v [wal [? [<- Hvalue]]]] Hgmp_v]]]]]]].
        have I := Hinv'. destruct I as [_ [_ [HoutM0 _]]].

        have Hl := HlocInBound _ _ Hx'. apply nth_error_Some in Hl.
        apply notNone_Some in Hl. destruct Hl as [? Hlx].

        remember ({|f_locs := set_nth (VAL_num (VAL_int32 (wasm_value_to_i32 wal))) (f_locs fr) (N.to_nat x') (VAL_num (VAL_int32 (wasm_value_to_i32 wal)));
       f_inst := f_inst fr|}) as f_before_IH.

       assert (Hfds': fds_translated_correctly fds s_v (f_inst f_before_IH)). {
         intros ???? Hfd. subst f_before_IH. cbn.
         apply Hfds in Hfd as [fidx [Ha Hv]]. exists fidx.
         split=>//.
         eapply val_relation_func_depends_on_funcs; eauto. }

      assert (HlocInBound': (forall (var : positive) (varIdx : localidx),
          @repr_var nenv lenv var varIdx -> N.to_nat varIdx < length (f_locs f_before_IH))). {
          intros ?? Hvar. subst f_before_IH. cbn.
          rewrite length_is_size size_set_nth maxn_nat_max -length_is_size.
          apply HlocInBound in Hvar. lia. }

      (* prepare IH *)
      assert (Hinv_before_IH: INV s_v f_before_IH). {
        eapply update_local_preserves_INV; try eassumption.
        apply nth_error_Some. congruence. }

      assert (HmemAvail': min_available_memory s_v (f_inst f_before_IH) mem'). {
        intros ?? Hmem Hglob Hbound. subst f_before_IH.
        rewrite Hgmp_v in Hglob.
        have I := Hinv. destruct I as [_ [_ [_ [_ [_ [_ [Hlinmem _]]]]]]].
        destruct Hlinmem as [Hmem1' [m' [Hmem2' [size' [<- [Hmem4' Hmem5']]]]]].
        have H'' := HmemAvail _ _ Hmem2' Hgmp HgmpBound.
        apply HmemLen in Hmem.

        unfold get_ctor_size in H6. rewrite H5 in H6. cbn in H6.
        destruct ((length ys) =? 0) eqn:Heq.
        1: { apply Nat.eqb_eq in Heq. lia. }

        apply Nat.eqb_neq in Heq. injection H6 as <-.
        remember (4 + gmp + 4 * N.of_nat (length ys))%N as n.
        inv Hglob. repeat rewrite Int32.Z_mod_modulus_id in H3; try lia.

        apply mem_length_upper_bound in Hmem5. cbn in Hmem5.
        remember (4 + gmp + 4 * N.of_nat (length ys))%N as n.
        simpl_modulus. cbn. lia.
      }

      (* evironment relation *)
      assert (HrelE_v : @rel_env_LambdaANF_Wasm lenv e rho' s_v f_before_IH fds).
      { clear IHHev Hinv Hmem1 Hmem2 Hmem3 Hmem4 Hinv' Hred_v.
        destruct HrelE as [Hfun1 [Hfun2 Hvar]]. unfold rel_env_LambdaANF_Wasm. split.
        { (* fns1 *) intros ????? Hrho Hv. subst rho'.
           destruct (var_dec x x1).
           { (* x=x1 *) subst x1. rewrite M.gss in Hrho. inv Hrho.
             apply subval_or_eq_fun in Hv. destruct Hv as [v1 [Hr1 Hr2]].
             have H'' := get_list_In_val _ _ _ _ H Hr2.
             destruct H'' as [x2 [Hin Hrho]].
             have H' := Hfun1 _ _ _ _ _ Hrho Hr1. assumption.
           }
           { (* x<>x1 *) rewrite M.gso in Hrho; eauto. }
        } split.
        { (* fns2 *)
          intros ? Hnfd. apply Hfun2 in Hnfd.
          destruct Hnfd as [i [Htrans Hval]].
          assert (Hfs: s_funcs sr = s_funcs s_v) by congruence.
          exists i. split. assumption.
          eapply val_relation_func_depends_on_funcs. eassumption.
          subst f_before_IH. assumption.
        }
        { (* local vars *)
          intros ? Hocc Hfd. destruct (var_dec x x1).
          { (* x = x1 *)
            subst x1. exists (Vconstr t vs), wal.
            subst rho'. rewrite M.gss. split; auto. split.
            subst f_before_IH. exists x'. cbn.
            split. assumption.
            unfold lookup_N.
            erewrite set_nth_nth_error_same; eauto.
            subst f_before_IH. assumption.
          }
          { (* x <> x1 *)
            assert (Hocc': occurs_free (Econstr x t ys e) x1). { now apply Free_Econstr2. }
            have H' := Hvar _ Hocc' Hfd.
            destruct H' as [val' [wal' [Hrho [Hloc Hval]]]].
            exists val', wal'. split.
            subst rho'. rewrite M.gso; auto.
            split.
            - destruct Hloc as [i [Hl1 Hl2]].
              unfold stored_in_locals. exists i. split; auto.
              subst f_before_IH. cbn.
              unfold lookup_N.
              rewrite set_nth_nth_error_other; auto.
              intro. assert (i=x') by lia. subst x'.
              have Hcontra := repr_var_inj _ _ _ _ HlenvInjective Hl1 Hx'.
              contradiction.
              apply nth_error_Some. congruence.
              subst f_before_IH.
              apply HvalPreserved'. apply HvalPreserved. assumption.
          }
        }
      }

      assert (HeRestr' : expression_restricted cenv e). { now inv HeRestr. }

      assert (Hunbound' : (forall x : var, In x (collect_local_variables e) ->
                                                           rho' ! x = None)). {
        subst rho'. intros.
        assert (~ In x (collect_local_variables e)). {
          apply NoDup_app_remove_r in Hnodup. cbn in Hnodup.
          now apply NoDup_cons_iff in Hnodup. }
        rewrite M.gso; last congruence.
        apply Hunbound. now right.
      }

      assert (Hnodup': NoDup (collect_local_variables e ++
                              collect_function_vars (Efun fds e))). {
       cbn in Hnodup. apply NoDup_cons_iff in Hnodup.
       now destruct Hnodup. }

       assert (HfenvRho' : forall (a : positive) (v : term.val),
          rho' ! a = Some v -> find_def a fds <> None -> v = Vfun (M.empty term.val) fds a). {
          intros ?? Hrho Hfd. apply HfenvRho; auto. subst rho'.
          rewrite M.gso in Hrho; auto. intro Hcontra. subst a.
          apply notNone_Some in Hfd. apply HfenvWf in Hfd. destruct Hfd.
          inv Hx'. destruct HenvsDisjoint as [Hd1 Hd2].
          apply Hd2 in H0. unfold translate_var in H2. now rewrite H0 in H2. }

      have IH := IHHev Hnodup' HfenvRho' HeRestr' Hunbound' _ fAny _ lh _ HlenvInjective HenvsDisjoint
                 state s_v f_before_IH _ Hfds' HlocInBound' Hinv_before_IH HmemAvail' Hexp HrelE_v.
      destruct IH as [s_final [f_final [k' [lh' [Hred_IH [Hval [Hfinst [Hsfuncs' [HvalPres H_INV]]]]]]]]].
      clear IHHev HfenvRho' Hunbound' Hnodup' HlocInBound' Hinv_before_IH Hfds Hfds'.
      cbn in Hfinst.

      exists s_final, f_final, k', lh'. split.
      (* steps *)

      subst instrs instructions.

      eapply rt_trans. apply reduce_trans_frame. apply reduce_trans_label.
      apply app_trans. apply Hred. cbn. rewrite map_cat.

      eapply rt_trans. eapply reduce_trans_frame. apply reduce_trans_label.
      eapply app_trans in Hred_v. apply Hred_v. cbn.
      clear Hred_v. separate_instr. rewrite catA.

      eapply rt_trans. apply reduce_trans_frame. apply reduce_trans_label.
      dostep_nary 0. apply r_global_get. eassumption.

      assert (f_inst f_before_IH = f_inst fr) as Hfinst'. { subst. reflexivity. }
      dostep_nary 1. eapply r_local_set'. eassumption.
      apply /ssrnat.leP. apply nth_error_Some. congruence. subst. reflexivity. apply rt_refl.
      apply Hred_IH.

      subst f_before_IH.
      repeat (split; auto). congruence.
    }
    { (* grow mem failed *)
    subst instructions instrs.

    (* split of dead instructions after return *)
     match goal with
     |- context C [reduce_trans (_, _, _, [:: AI_frame _ _ (lfill _
        (_ ++ ?es))])] =>
         let es_tail := fresh "es_tail" in
         remember es as es_tail
     end.

     have Hlh := lholed_tail _ lh (map AI_basic grow_mem_instr) es_tail.

     destruct Hlh as [k' [lh' Heq']]. cbn in Heq'.
     have Hbad := HRedRet _ lh'.
     destruct Hbad as [sr' [k'' [lh'' [Hred [Hfuncs [HvalPreserved HoutofM]]]]]].


     exists sr', fr, k'', lh''. split.
     rewrite -Heq' in Hred.
     apply reduce_trans_frame. apply Hred.

     split. right. assumption. split. reflexivity. split. congruence.
     split. auto.
     intro Hcontra. rewrite Hcontra in HoutofM. inv HoutofM. } }
    { (* Nullary constructor case *)

      subst. injection H as <-.
      remember ({|f_locs := set_nth (VAL_num (nat_to_value (N.to_nat (2 * ord + 1)))) (f_locs fr) (N.to_nat x') (VAL_num (nat_to_value (N.to_nat (2 * ord + 1)))) ; f_inst := f_inst fr|}) as f_before_IH.
      assert (HNoDup' : NoDup (collect_local_variables e ++ collect_function_vars (Efun fds e))). {
        cbn in Hnodup. apply NoDup_cons_iff in Hnodup.
        destruct Hnodup. assumption.
      }
      assert (HfenvRho' : (forall (a : positive) (v : val),
        (map_util.M.set x (Vconstr t []) rho) ! a = Some v ->
        find_def a fds <> None -> v = Vfun (M.empty val) fds a)). {
        intros. apply HfenvRho. rewrite M.gso in H. assumption.
        intro. subst a. apply notNone_Some in H0. apply HfenvWf in H0. destruct H0.
        inv H12. destruct HenvsDisjoint as [Hd1 Hd2]. apply Hd2 in H. unfold translate_var in H0. rewrite H in H0. inv H0. assumption.
      }
      assert (Herestr' :  expression_restricted cenv e). {
        inv HeRestr. assumption.
      }

      assert (Hunbound' : (forall x0 : var,
          In x0 (collect_local_variables e) ->
          (map_util.M.set x (Vconstr t []) rho) ! x0 = None)). {
        intros. apply NoDup_app_remove_r in Hnodup. cbn in Hnodup.
        apply NoDup_cons_iff in Hnodup. rewrite M.gso. apply Hunbound.
        unfold collect_local_variables. cbn. fold collect_local_variables.
        right. assumption. destruct Hnodup as [Hx _ ].
        unfold not. unfold not in Hx. intros Heq. subst x. apply Hx in H. contradiction.
      }

      assert (Hfds' : fds_translated_correctly fds sr (f_inst f_before_IH)). {
        intros ???? Hfd. subst f_before_IH. cbn.
        apply Hfds in Hfd as [fidx [Ha Hv]]. now exists fidx. }

      assert (HlocInBound': (forall (var : positive) (varIdx : u32),
        @repr_var nenv lenv var varIdx -> N.to_nat varIdx < length (f_locs f_before_IH))). {
        intros ?? Hvar. subst f_before_IH. cbn.
        rewrite length_is_size size_set_nth maxn_nat_max -length_is_size.
        apply HlocInBound in Hvar, H12. lia. }

      assert (Hinv' : INV sr f_before_IH). {
        eapply update_local_preserves_INV; try eassumption.
        now destruct (HlocInBound x x').
      }

      assert (HmemAvail': min_available_memory sr (f_inst f_before_IH) mem'). {
        intros ?????.
        have Hsize0 := constr_size_0 _ _ H6 H15. subst constr_size.
        inv H8; try lia.
        have H' := HmemAvail _ _ H H0 H1.
        lia.
      }

      assert (HrelE' : @rel_env_LambdaANF_Wasm lenv e (map_util.M.set x (Vconstr t []) rho) sr f_before_IH fds). {
        have Hl := HlocInBound _ _ H12.
        apply nth_error_Some in Hl.
        apply notNone_Some in Hl. destruct Hl as [? Hlx].

        destruct HrelE as [Hfun1 [Hfun2 Hvar]]. unfold rel_env_LambdaANF_Wasm. split.
        { intros. destruct (var_dec x x1).
          - subst x1. rewrite M.gss in H. inv H.
            apply subval_or_eq_fun in H0.
            destruct H0 as [v1 [Hr1 Hr2]]. inv Hr2.
          - by rewrite M.gso in H; eauto.
        } split.
        { intros ? Hnfd. apply Hfun2 in Hnfd.
          destruct Hnfd as [i [Htrans Hval]].
          exists i. split. assumption. subst f_before_IH. assumption.
        }
        { intros. destruct (var_dec x x1).
          { (* x = x1 *)
            subst x1.

            assert (Wasm_int.Int32.half_modulus < Wasm_int.Int32.modulus)%Z. {
              now rewrite Wasm_int.Int32.half_modulus_modulus.
            }

            exists (Vconstr t []), (Val_unboxed (2 * ord + 1)%N).
            rewrite M.gss. split. reflexivity.
            split.
            { unfold stored_in_locals. exists x'.
              split. assumption.
              subst f_before_IH. cbn.
              unfold lookup_N, nat_to_value, nat_to_i32, wasm_value_to_i32.
              repeat f_equal.
              erewrite set_nth_nth_error_same; eauto. by rewrite N_nat_Z.
            }
            econstructor; eauto; first lia.
            inv HeRestr.
            unfold ctor_ordinal_restricted in H9.
            apply H9 in H14.
            simpl_modulus.
            simpl_modulus_in H14.
            cbn. destruct ord; lia.
          }
          { (* x <> x 1*)
            assert (Hocc: occurs_free (Econstr x t [] e) x1). { now apply Free_Econstr2. }
            have H' := Hvar _ Hocc H0.
            destruct H' as [val' [wal' [Hrho [Hloc Hval]]]].
            exists val', wal'.
            split. rewrite M.gso; auto.
            split. 2: now subst f_before_IH.
            destruct Hloc as [i [Hl1 Hl2]].
            unfold stored_in_locals. exists i. split; auto.
            subst f_before_IH.
            unfold lookup_N.
            rewrite set_nth_nth_error_other; auto.
            intro. assert (x' = i) by lia. subst x'.
            have Hcontra := repr_var_inj _ _ _ _ HlenvInjective Hl1 H12.
            contradiction.

            apply nth_error_Some. congruence.
          }
        }
      }

      assert (grow_mem_instr = []). {
        inv H8=>//.
        have H' := constr_size_0 _ _ H6 H5. lia.
      } subst grow_mem_instr.

      have IH := IHHev HNoDup' HfenvRho' Herestr' Hunbound' _ fAny _ lh _ HlenvInjective HenvsDisjoint
                 state sr f_before_IH _ Hfds' HlocInBound' Hinv' HmemAvail' H11 HrelE'.
      destruct IH as [sr' [f' [k' [lh' [Hred [Hval [Hfinst [Hsfuncs [HvalPres H_INV]]]]]]]]].

      exists sr', f', k', lh'.
      split. eapply rt_trans. apply reduce_trans_frame. apply reduce_trans_label.
      dostep_nary 1. eapply r_local_set' with (f':=f_before_IH).
      subst f_before_IH. reflexivity.
      apply /ssrnat.leP. eapply HlocInBound.
      eassumption.
      subst f_before_IH. reflexivity.
      apply rt_refl.

      (* IH *)
      apply Hred.

      subst f_before_IH.
      by repeat (split; auto).
    }
  - (* Eproj: let x := proj_n y in e *)
    { inv Hrepr_e.
      rename H9 into Hx', H10 into Hy'.

      (* y is constr value with correct tag, arity *)
      assert (Hy : occurs_free (Eproj x t n y e) y) by constructor.
      have HrelE' := HrelE.
      destruct HrelE' as [Hfun1 [Hfun2 Hvar]].
      assert (HfdNone: find_def y fds = None). {
        apply HfenvWf_None with (f:=y) in HfenvWf. rewrite HfenvWf.
        inv Hy'. unfold translate_var in H1.
        destruct (lenv ! y) eqn:Hy'; rewrite Hy' in H1=>//. injection H1 as ->. now apply HenvsDisjoint in Hy'. }
      apply Hvar in Hy; auto. destruct Hy as [v6 [wal [Hrho [Hlocal Hrepr]]]].
      rewrite Hrho in H. inv H.
      have Hrepr' := Hrepr. inv Hrepr'.
      (* unboxed absurd *) inv H0.
      (* boxed *)
      inv Hlocal. destruct H.

      have I := Hinv. destruct I as [_ [_ [_ [_ [_ [_ [_ [_ [_ [HfnsUpperBound [_ [_ _]]]]]]]]]]]].
      have Hextr := extract_constr_arg n vs v _ _ _ _ HfnsUpperBound H0 H10 H16.
      destruct Hextr as [bs [wal [Hload [Heq Hbsval]]]].

      remember {| f_locs := set_nth (VAL_num (wasm_deserialise bs T_i32)) (f_locs fr) (N.to_nat x') (VAL_num (wasm_deserialise bs T_i32))
                ; f_inst := f_inst fr
                |} as f_before_IH.

      assert (Hrm: @rel_env_LambdaANF_Wasm lenv e (map_util.M.set x v rho) sr f_before_IH fds). {
        split; intros.
        { (* funs1 *)
          destruct (var_dec x x1).
          { (* x = x1 *)
            subst x1.
            rewrite M.gss in H11. inv H11. rename v0 into v.
            apply nthN_In in H0.
            have H' := subval_or_eq_constr _ _ _ t H13 H0.
            have HF := Hfun1 _ _ _ _ _ Hrho H'. destruct HF as [? [? HF]]. subst.
            apply Hfun2 in HF.
            destruct HF as [i [Htrans Hval]].
            inv Hval. do 2 split => //.
            eapply find_def_name_in_fundefs. eassumption.
          }
          { (* x <> x1*)
            rewrite M.gso in H11; auto.
            have H' := Hfun1 _ _ _ _ _ H11 H13. destruct H' as [? [? H']]. subst.
            apply Hfun2 in H'.
            destruct H' as [i [Htf Hval]].
            inv Hval. do 2 split => //.
            eapply find_def_name_in_fundefs. eassumption.
           }
        } split.
        { (* funs2 *)
          intros ? Hnfd. apply Hfun2 in Hnfd.
          destruct Hnfd as [i [Htrans Hval]].
          exists i. split. assumption. subst f_before_IH. assumption.
        }
        { (* local vars *)
          intros. destruct (var_dec x x1).
          { (* x = x1 *)
            subst x1.
            exists v. exists wal. split.
            rewrite map_util.M.gsspec.
            apply peq_true.
            split. exists x'. split. assumption.
            unfold wasm_deserialise in Heq. rewrite Heq.
            have Hl := HlocInBound _ _ Hx'. apply nth_error_Some in Hl.
            apply notNone_Some in Hl. destruct Hl.
            subst f_before_IH. eapply set_nth_nth_error_same. eassumption.
            subst f_before_IH. assumption. }
          { (* x <> x1 *)
            assert (Hocc: occurs_free (Eproj x t n y e) x1). { constructor; assumption. }
            apply Hvar in Hocc; auto. destruct Hocc as [v6 [wal' [Henv [Hloc Hval]]]].
            exists v6. exists wal'.
            subst f_before_IH.
            repeat split; auto.
            rewrite map_util.M.gsspec.
            rewrite peq_false. assumption. congruence.
            destruct Hloc as [x1' [? ?]].
            unfold stored_in_locals. cbn.

            assert (x1' <> x'). {
              intro. subst x1'.
              have Hcontra := repr_var_inj _ _ _ _ HlenvInjective H14 Hx'.
              contradiction. }
          exists x1'.
          split; auto.
          unfold lookup_N.
          rewrite set_nth_nth_error_other; auto; try lia.
          eapply HlocInBound. eassumption.
        }
     }}

     assert (Hfds': fds_translated_correctly fds sr (f_inst f_before_IH)).  {
       intros ???? Hfd. subst f_before_IH. cbn.
       apply Hfds in Hfd as [fidx [Ha Hv]]. now exists fidx. }

     assert (HlocInBound': (forall (var : positive) (varIdx : localidx),
        @repr_var nenv lenv var varIdx -> N.to_nat varIdx < length (f_locs f_before_IH))). {
      intros ?? Hvar'. cbn. subst f_before_IH.
      rewrite length_is_size size_set_nth maxn_nat_max -length_is_size.
      apply HlocInBound in Hvar'. lia. }

     assert (Hinv': INV sr f_before_IH). {
       subst f_before_IH. cbn.
       eapply update_local_preserves_INV. 3: reflexivity.
       assumption. apply nth_error_Some. intros. apply nth_error_Some.
       eapply HlocInBound. eassumption. }

     assert (HmemAvail' :  min_available_memory sr (f_inst f_before_IH) mem) by now subst f_before_IH.

     assert (HeRestr' : expression_restricted cenv e). { now inv HeRestr. }
     assert (Hunbound': (forall x0 : var, In x0 (collect_local_variables e) ->
                                          (map_util.M.set x v rho) ! x0 = None)). {
       intros.
       assert (~ In x (collect_local_variables e)). {
         apply NoDup_app_remove_r in Hnodup. cbn in Hnodup.
         now apply NoDup_cons_iff in Hnodup. }
       rewrite M.gso; last congruence.
       apply Hunbound. now right.
     }

     assert (Hnodup' : NoDup (collect_local_variables e ++
                              collect_function_vars (Efun fds e))). {
       cbn in Hnodup. apply NoDup_cons_iff in Hnodup.
       now destruct Hnodup. }

     assert (HfenvRho' : forall (a : positive) (v0 : term.val),
              (map_util.M.set x v rho) ! a = Some v0 ->
              find_def a fds <> None ->
              v0 = Vfun (M.empty term.val) fds a). {
       intros. apply HfenvRho; auto.
       rewrite M.gso in H11; auto. intro Hcontra. subst a.
       apply notNone_Some in H13. apply HfenvWf in H13. destruct H13.
       inv Hx'. destruct HenvsDisjoint as [Hd1 Hd2].
       apply Hd2 in H11. unfold translate_var in H13. now rewrite H11 in H13. }

     have IH := IHHev Hnodup' HfenvRho' HeRestr' Hunbound' _ fAny _ lh _ HlenvInjective HenvsDisjoint
                      state _ _ _ Hfds' HlocInBound' Hinv' HmemAvail' H8 Hrm.
     destruct IH as [sr' [f' [k' [lh' [Hred [Hval [Hfinst [Hsfuncs [HvalPres H_INV]]]]]]]]]. cbn in Hfinst.

     exists sr', f', k', lh'. cbn. split.
     { (* take steps *)
       have I := Hinv'. destruct I as [_ [_ [_ [_ [_ [_ [Hlinmem _]]]]]]].
       have Hly := HlocInBound _ _ Hy'.
       have Hlx := HlocInBound _ _ Hx'.
       assert (x0 = y'). { eapply repr_var_det; eassumption. } subst x0.

       eapply rt_trans. apply reduce_trans_frame. apply reduce_trans_label.
       (* get_local y' *)
       dostep_nary 0. apply r_local_get. apply H1.
       (* add offset n *)
       dostep_nary 2. constructor. apply rs_binop_success=>//.
       assert (Har: Wasm_int.N_of_uint i32m (Wasm_int.Int32.iadd (wasm_value_to_i32 (Val_ptr addr))
            (nat_to_i32 ((N.to_nat n + 1) * 4))) = ((4 + addr) + 4 * n)%N). {
          replace (4 + addr)%N with (addr + 4)%N by lia. replace (4*n)%N with (n*4)%N by lia. cbn.
       unfold load in Hload.
       destruct (4 + addr + 4 * n + (0 + 4) <=? mem_length m)%N eqn:Heqn. 2: by inv Hload.
       apply N.leb_le in Heqn.
       destruct Hlinmem as [Hmem1 [m' [Hmem2 [size [Hmem3 [Hmem4 Hmem5]]]]]].
       assert (m' = m). { unfold smem in H10, Hmem2. subst f_before_IH. rewrite Hmem1 in H10, Hmem2.
        congruence. } subst.
       apply mem_length_upper_bound in Hmem5. cbn in Hmem5.
       by repeat (rewrite Wasm_int.Int32.Z_mod_modulus_id; simpl_modulus; cbn; try lia). }

       dostep_nary 1. eapply r_load_success. eassumption. rewrite Har. apply Hload.
       (* save result in x' *)
       dostep_nary 1. eapply r_local_set' with (f':=f_before_IH); subst f_before_IH=>//.
       apply /ssrnat.leP. now apply HlocInBound in Hx'.
       apply rt_refl. apply Hred. }
     subst f_before_IH. by repeat (split; auto).
    }
  - (* Ecase *)
    {
      intros.
      assert (caseConsistent cenv cl t). { assumption. }
      inv Hrepr_e.
      rename H5 into Hy'.
      assert (Hy : occurs_free (Ecase y cl) y) by constructor.
      have HrelE' := HrelE.
      destruct HrelE' as [Hfun1 [Hfun2 Hvar]].
      assert (HfdNone: find_def y fds = None). {
        apply HfenvWf_None with (f:=y) in HfenvWf. rewrite HfenvWf.
        inv Hy'. unfold translate_var in H3. destruct (lenv ! y) eqn:Hy'; rewrite Hy' in H3=>//.
        injection H3 as ->.
        now apply HenvsDisjoint in Hy'.
      }
      have Hy0 := Hy.
      apply Hvar in Hy0; auto.
      destruct Hy0 as [v0 [wal [Hrho [Hlocals Hval]]]].
      assert (v0 = (Vconstr t vl)) by congruence. subst v0.
      (* Assert that we can step into either
         the unboxed or boxed cases,
         and from there into the correct branch *)
      assert (Hstep_case:
               exists e' k0 (lh0 : lholed k0),
                 reduce_trans
                     (state, sr, fAny,
                       [ AI_frame 0 fr (lfill lh
                            ([seq AI_basic i | i <-
                                [ BI_local_get y'
                                ; BI_const_num (nat_to_value 1)
                                ; BI_binop T_i32 (Binop_i BOI_and)
                                ; BI_testop T_i32 TO_eqz
                                ; BI_if (BT_valtype None)
                                    e1'
                                    e2']
                             ]))
                       ])
                     (state, sr, fAny, [AI_frame 0 fr (lfill lh0 (map AI_basic e'))])
                 /\ repr_expr_LambdaANF_Wasm lenv e mem e'). {
        have Hval' := Hval.
        inv Hval.
        { (* Unboxed cases (nullary) *)
          assert (exists e' e'',
             select_nested_if false y' ord brs2 =
               [ BI_local_get y'
               ; BI_const_num (nat_to_value (N.to_nat (2 * ord + 1)))
               ; BI_relop T_i32 (Relop_i ROI_eq)
               ; BI_if (BT_valtype None)
                  e'
                  e'' ]
             /\ (forall k0 (lh0 : lholed k0), exists k0' (lh0' : lholed k0'),
                    reduce_trans
                      (state, sr, fAny, [AI_frame 0 fr (lfill lh0 (map AI_basic e2'))])
                      (state, sr, fAny, [AI_frame 0 fr (lfill lh0' (map AI_basic e'))]))
                 /\ repr_expr_LambdaANF_Wasm lenv e mem e').
          {
            destruct Hlocals as [i [Htrans_y Hlocs]].
            assert (i = y'). { eapply repr_var_det; eassumption. } subst i.
            have Hif_red := unboxed_nested_if_chain_reduces cl fAny y t e y' lenv mem brs1 brs2 e2' fr state sr ord Hlocs HcenvRestr HeRestr H2 H1 H5 H14 H6 H10.
            destruct Hif_red as [e' [e'' [Hsel [Hred Hrep]]]].
            by exists e', e''.
          }
          destruct H3 as [e' [e'' [_ [Hred Hrep]]]].
          have Hholednested := lholed_nested_label k lh (map AI_basic e2') [].
          destruct Hholednested as [k0' [lh0' He2']].
          have Hred' := Hred k0' lh0'.
          destruct Hred' as [k0 [lh0 Hred']].
          exists e', k0, lh0. split; auto.
          have Hlocals' := Hlocals.
          destruct Hlocals' as [i [Htrans_y Hntherror]].
          assert (i = y'). { eapply repr_var_det; eassumption. } subst i.
          eapply rt_trans. apply reduce_trans_frame. apply reduce_trans_label.
          dostep_nary 0. apply r_local_get. eauto.
          dostep_nary 2. constructor. apply rs_binop_success; first done.
          cbn.
          assert (Heq: Wasm_int.Int32.iand (wasm_value_to_i32 (Val_unboxed (ord * 2 + 1)%N)) (nat_to_i32 1) = Wasm_int.Int32.one).
          {
            rewrite N.mul_comm.
            unfold wasm_value_to_i32; unfold wasm_value_to_u32; unfold N_to_i32.
            cbn.
            eapply and_1_odd. lia.
          }
          rewrite Heq. reflexivity.
          dostep_nary 1. constructor. eapply rs_testop_i32.
          dostep'. constructor. apply rs_if_false. reflexivity.
          dostep'. eapply r_block with (t1s:=[::]) (t2s:=[::])(vs:=[::]); auto.
          apply rt_refl.
          rewrite -He2' in Hred'. apply Hred'.
        }
        { (* Boxed cases (non-nullary) *)
          assert (exists e' e'',
                     select_nested_if true y' ord brs1 =
                       [ BI_local_get y'
                       ; BI_load T_i32 None {| memarg_offset:=0%N; memarg_align:=2%N |}
                       ; BI_const_num (nat_to_value (N.to_nat ord))
                       ; BI_relop T_i32 (Relop_i ROI_eq)
                       ; BI_if (BT_valtype None)
                           e'
                           e'' ]
                     /\ (forall k0 (lh0 : lholed k0),
                           exists k0' (lh0' : lholed k0'),
                           reduce_trans
                             (state, sr, fAny, [AI_frame 0 fr (lfill lh0 (map AI_basic e1'))])
                             (state, sr, fAny, [AI_frame 0 fr (lfill lh0' (map AI_basic e'))]))
                     /\ repr_expr_LambdaANF_Wasm lenv e mem e').
          {
            destruct Hlocals as [i [Htrans_y Hlocs]].
            assert (i = y'). { eapply repr_var_det; eassumption. } subst i.
            destruct Hinv as [_ [_ [_ [_ [_ [_ [Hmem _]]]]]]].
            have Hif_red := boxed_nested_if_chain_reduces cl fAny y t vl e addr y' lenv mem brs1 brs2 e1' state sr fr ord Hmem Hval' Hlocs HcenvRestr HeRestr H2 H9 H1 H6 H7.
            destruct Hif_red as [e' [e'' [Hsel [Hred Hrep]]]].
            have Hred' := Hred k lh.
            by exists e', e''.
          }
          destruct H3 as [e' [e'' [_ [Hred Hrep]]]].
          have Hholednested := lholed_nested_label k lh (map AI_basic e1') [].
          destruct Hholednested as [k0' [lh0' He1']].
          destruct (Hred k0' lh0') as [k0 [lh0 Hred']].
          exists e', k0, lh0. split; auto.
          destruct Hlocals as [i [Htrans_y Hntherror]].
          assert (i = y'). { eapply repr_var_det; eassumption. } subst i.
          eapply rt_trans. apply reduce_trans_frame. apply reduce_trans_label.
          dostep_nary 0. apply r_local_get. eauto.
          assert (Hand : Wasm_int.Int32.iand (wasm_value_to_i32 (Val_ptr addr)) (nat_to_i32 1) = Wasm_int.Int32.zero). {
            destruct H14 as [n0 Hn0].
            rewrite Hn0.
            apply and_1_even.
            lia.
          }
          dostep_nary 2. constructor. apply rs_binop_success=>//.
          dostep_nary 1. constructor. apply rs_testop_i32. cbn.
          dostep'. constructor. apply rs_if_true. by rewrite Hand.
          dostep'. eapply r_block with (t1s:=[::]) (t2s:=[::])(vs:=[::]); auto.
          apply rt_refl.
          rewrite -He1' in Hred'. apply Hred'.
        }
      }
      have I := Hinv. destruct I as [_ [_ [_ [_ [_ [_ [Hlinmem [_ [_ [_ [_ [_  _]]]]]]]]]]]].

      assert (Hrel: @rel_env_LambdaANF_Wasm lenv e rho sr fr fds).
      { unfold rel_env_LambdaANF_Wasm.
        split. intros. eauto.
        split. eauto. intros.
        assert (occurs_free (Ecase y cl) x).
        eapply occurs_free_Ecase_Included.
        apply findtag_In. eauto. eauto.
        apply Hvar; auto.
      }

      assert (HeRestr': expression_restricted cenv e). {
        inv HeRestr.
        rewrite Forall_forall in H5.
        apply H5 with (x:=(t,e)).
        by apply findtag_In.
      }

      assert (Hunbound': (forall x : var, In x (collect_local_variables e) ->
                                     rho ! x = None)). {
        intros. apply Hunbound. cbn.
        apply in_flat_map.
        exists (t,e). split; auto.
        by apply findtag_In.
      }

      destruct Hstep_case as [e' [k0 [lh0 [Hred Hrepre]]]].

      assert (Hnodup': NoDup (collect_local_variables e ++
                                collect_function_vars (Efun fds e))). {
        apply NoDup_incl_NoDup' with (l1:=collect_local_variables (Ecase y cl)) =>//.
        apply NoDup_case with (cl:=cl) (t:=t) (y:=y)=>//.
        apply NoDup_app_remove_r in Hnodup. assumption.
        assert (In (t, e) cl). { by apply findtag_In. }
        intros ??. apply in_flat_map. by exists (t, e).
      }

      have IH := IHHev Hnodup' HfenvRho HeRestr' Hunbound' k0 fAny _ lh0 _ HlenvInjective HenvsDisjoint
                       state _ _ _ Hfds HlocInBound Hinv HmemAvail Hrepre Hrel.
      destruct IH as [sr' [fr' [k1 [lh1 [Hstep [Hval_e [Hfinst [HvalPres H_INV]]]]]]]].

      exists  sr', fr', k1, lh1. split.
      { (* steps *)
        eapply rt_trans. apply Hred.
        apply Hstep.
      }
      split. apply Hval_e.
      split. apply Hfinst.
      split. apply HvalPres.
      apply H_INV.
    }
  - (* Eapp *)
    { inv Hrepr_e. rename args' into args_instr.
      assert (HfdsRhoEq: fl = fds /\ rho' = M.empty _). { destruct HrelE as [Hfun1 _]. eapply Hfun1 in H. now destruct H. apply rt_refl. } destruct HfdsRhoEq. subst fl rho'.
      (* treat direct + indirect calls in one *)
      assert (Hval: exists fidx,
        reduce_trans (state, sr, fr, [AI_basic instr])
                     (state, sr, fr, [AI_basic (BI_const_num (N_to_value fidx))]) /\
        repr_val_LambdaANF_Wasm (Vfun (M.empty _) fds f') sr (f_inst fr) (Val_funidx fidx)). {

      inv H9.
      { (* indirect call *)
        assert (Hocc: occurs_free (Eapp f t ys) f) by constructor.
        have Hrel := HrelE. destruct Hrel as [Hfun1 [_ Hvar]].
        assert (HfNone: find_def f fds = None). {
          apply HfenvWf_None with (f:=f) in HfenvWf. rewrite HfenvWf.
          inv H3. unfold translate_var in H4. destruct (lenv ! f) eqn:Hf'; rewrite Hf' in H4=>//.
          injection H4 as ->. now apply HenvsDisjoint in Hf'. }
        apply Hvar in Hocc; auto. destruct Hocc as [val [wal [Hrho [[j [Htrans Hwal]] Hval]]]].
        assert (j = i). { eapply repr_var_det; eassumption. } subst j.
        rewrite H in Hrho. inv Hrho. inv Hval.
        exists idx. split.
        dostep'. apply r_local_get. eassumption. apply rt_refl.
        econstructor; eauto. }
      { (* direct call *)
        inv H3. unfold translate_var in H4. destruct (fenv ! f) eqn:Hf; rewrite Hf in H4=>//.
        injection H4 as ->.
        assert (Hf': exists i, fenv ! f = Some i) by eauto.
        apply HfenvWf in Hf'.
        assert (Htemp: f' = f). { apply HfenvRho in H. now inv H. now destruct Hf'. }
        inv Htemp.
        destruct HrelE as [Hfun1 [Hfun2 _]].
        assert (Hsubval: subval_or_eq (Vfun (M.empty term.val) fds f)
                                      (Vfun (M.empty term.val) fds f)) by constructor.
        have H' := Hfun1 _ _ _ _ _ H Hsubval. destruct H' as [_ [_ H']].
        apply Hfun2 in H'.
        destruct H' as [idx [HtransF Hval]].
        assert (idx = i). { inv HtransF. unfold translate_var in H3. now rewrite Hf in H3. }
        subst idx. exists i. split. apply rt_refl.
        assumption.
      }
    }

    destruct Hval as [fidx [HredF Hval]]. inv Hval.
    rewrite H7 in H1. inv H1. rename H14 into Hexpr.

    repeat rewrite map_cat. cbn.
    have Hfargs := fun_args_reduce state _ _ _ _ _ _ _ _ _ Hinv H0 HenvsDisjoint HfenvWf HfenvRho HrelE H8.
    destruct Hfargs as [args [HfargsRed HfargsRes]].

    remember {| f_locs := [seq (VAL_num (N_to_value a)) | a <- args] ++
                   (repeat (VAL_num (N_to_value 0)) (length (collect_local_variables e)))
              ; f_inst := f_inst fr |} as f_before_IH.

    (* prepare IH *)
    remember (create_local_variable_mapping (xs ++ collect_local_variables e)) as lenv_before_IH.

    assert (Hfds_before_IH: fds_translated_correctly fds sr (f_inst f_before_IH)). {
      intros ???? Hfd. subst f_before_IH. cbn.
      apply Hfds in Hfd as [fidx' [Ha Hv]]. now exists fidx'. }

    assert (HlocInBound_before_IH: (forall (var : positive) (varIdx : localidx),
          @repr_var nenv (create_local_variable_mapping (xs ++ collect_local_variables e)) var varIdx ->
           N.to_nat varIdx < length (f_locs f_before_IH))). {
      intros ?? Hvar. subst f_before_IH. cbn. inv Hvar. apply var_mapping_list_lt_length in H1.
      rewrite length_app in H1. apply const_val_list_length_eq in HfargsRes.
      rewrite length_app. rewrite length_map -HfargsRes.
      rewrite map_repeat_eq. rewrite length_map. apply set_lists_length_eq in H2.
      now rewrite -H2.
    }

    assert (Hinv_before_IH : INV sr f_before_IH). {
       subst. now eapply init_locals_preserves_INV. }

    assert (HmemAvail_before_IH: min_available_memory sr (f_inst f_before_IH) 0). {
       intros ????.
       destruct Hinv_before_IH as [_[_[_[_[_[_[_[HgmpInM _]]]]]]]].
       eapply HgmpInM in H3;eauto.
        lia. }

    assert (HrelE': @rel_env_LambdaANF_Wasm lenv_before_IH e rho'' sr f_before_IH fds). {
      unfold rel_env_LambdaANF_Wasm. split.
      { (* funs1 *)
        intros.
        assert (Hdec: decidable_eq var). {
          intros n m. unfold Decidable.decidable. now destruct (var_dec n m). }
       destruct (In_decidable Hdec x xs); clear Hdec.
       - (* In x xs *)
         have H' := set_lists_In _ _ _ _ _ _ H4 H1 H2.
         destruct (get_list_In_val _ _ _ _ H0 H') as [y [Hiny HyRho]].
         now destruct HrelE as [Hfun1 [Hfun2 _]]; eauto.
       - (* ~In x xs *)
         have H' := set_lists_not_In _ _ _ _ _ H2 H4. rewrite H1 in H'.
         erewrite def_funs_find_def in H'.
         2:{ intro Hcontra. apply def_funs_not_find_def with (fds':=fds) (rho:=M.empty _) in Hcontra.
             rewrite Hcontra in H'. inv H'. } inv H'.
         have H' := set_lists_not_In _ _ _ _ _ H2 H4.
         rewrite H1 in H'.
         apply def_funs_spec in H'. destruct H' as [[? ?] | [? Hcontra]]. 2: inv Hcontra.
         apply subval_fun in H3. 2: assumption.
         destruct H3 as [f1 [?H ?H]]. inv H3. now inv H10.
      } split.
      { (* fun2 *)
        destruct HrelE as [_ [Hfun2 _]].
        intros ? Hnfd. apply Hfun2 in Hnfd.
        destruct Hnfd as [i [Htrans Hval]].
        exists i. split. assumption. subst f_before_IH. assumption. }
      { (* vars *)
        intros. destruct HrelE as [_ HrelVars].
        assert (In x xs). {
          apply HfdsRestr in H7.
          destruct H7 as [? [Hxxs ?]].
          have H' := Hxxs _ H1. now destruct H'. }
        destruct (get_set_lists_In_xs _ _ _ _ _ H4 H2) as [v' Hv'].
        have H' := set_lists_nth_error _ _ _ _ _ _ H4 Hv' H2.
        destruct H' as [k' [Hvk Hxk]].
        have H'' := const_val_list_nth_error _ _ _ _ _ _ HfargsRes Hvk.
        destruct H'' as [w [Hw Hnth]].
        exists v', w. split; auto. split; auto.

        unfold stored_in_locals. subst lenv_before_IH f_before_IH. exists (N.of_nat k').
        split. {
          econstructor; eauto.
          intros. unfold create_local_variable_mapping.
          rewrite (var_mapping_list_lt_length_nth_error_idx _ (N.of_nat k')); auto.
          apply HfdsRestr in H7. destruct H7 as [_ [_ HnodupE]].
          rewrite catA in HnodupE. apply NoDup_app_remove_r in HnodupE. assumption.
          unfold lookup_N.
          rewrite Nat2N.id.
          rewrite nth_error_app1; auto. apply nth_error_Some. intro.
          rewrite H5 in Hxk. inv Hxk. }
        cbn. unfold lookup_N.
        rewrite nth_error_app1. 2: {
          rewrite length_is_size size_map -length_is_size.
          apply const_val_list_length_eq in HfargsRes.
          rewrite -HfargsRes.
          apply nth_error_Some. rewrite Nat2N.id. congruence. }
        rewrite Nat2N.id. assumption.
        subst f_before_IH. assumption. }
    }

    assert (HeRestr' : expression_restricted cenv e). {
        apply HfdsRestr in H7. now destruct H7. }

    assert (Hunbound': (forall x : var, In x (collect_local_variables e) -> rho'' ! x = None)). {
      intros.
      assert (~ exists v, find_def x fds = Some v). {
        intro Hcontra. destruct Hcontra as [? Hfd].
        assert (Hfd': find_def x fds <> None) by congruence.
        clear Hfd. rename Hfd' into Hfd.
        eapply find_def_in_collect_function_vars in Hfd.
        apply HfdsRestr in H7. destruct H7 as [_ [_ HnodupE]].
        apply NoDup_app_remove_l in HnodupE.
        eapply NoDup_app_In in HnodupE; eauto. }
      assert (Hfd: find_def x fds = None). { destruct (find_def x fds); eauto. exfalso. eauto. }
      apply def_funs_not_find_def with (fds':=fds) (rho:=M.empty _) in Hfd.
      assert (HxIn: ~ In x xs). {
        intro Hcontra.
        apply HfdsRestr in H7. destruct H7 as [_ [_ HnodupE]].
        rewrite catA in HnodupE. apply NoDup_app_remove_r in HnodupE.
        eapply NoDup_app_In in HnodupE; eauto. }
      have H'' := set_lists_not_In _ _ _ _ _ H2 HxIn. rewrite <- H''.
      now rewrite Hfd.
    }

    assert (HlenvInjective': map_injective lenv_before_IH). {
      subst lenv_before_IH.
      apply create_local_variable_mapping_injective.
      apply HfdsRestr in H7. destruct H7 as [_ [_ HnodupE]].
      rewrite catA in HnodupE. now apply NoDup_app_remove_r in HnodupE.
    }

    assert (HenvsDisjoint': domains_disjoint lenv_before_IH fenv). {
      apply HfdsRestr in H7. destruct H7 as [_ [_ HnodupE]].
      subst lenv_before_IH. unfold domains_disjoint. split; intros.
      { (* -> *)
        apply variable_mapping_Some_In in H1; auto.
        assert (~ exists v, fenv ! x = Some v). {
          intro Hcontra. apply HfenvWf in Hcontra.
          apply notNone_Some in Hcontra.
          eapply find_def_in_collect_function_vars in Hcontra.
          rewrite catA in HnodupE. eapply NoDup_app_In in HnodupE; eauto. }
          destruct (fenv ! x) eqn:Hx; auto. exfalso. eauto. }
      { (* <- *)
         assert (exists res : fun_tag * seq var * exp, find_def x fds = Some res).
           apply HfenvWf; eauto.
         apply notNone_Some in H3.
         eapply find_def_in_collect_function_vars in H3.
         apply variable_mapping_NotIn_None; auto.
         rewrite catA in HnodupE. intro Hcontra.
         eapply NoDup_app_In in HnodupE; eauto. }
    }

    assert (Hnodup': NoDup (collect_local_variables e ++
                            collect_function_vars (Efun fds e))). {
      apply HfdsRestr in H7. destruct H7 as [_ [_ HnodupE]].
      apply NoDup_app_remove_l in HnodupE.
      assumption. }

    assert (HfenvRho': forall (a : positive) (v : term.val),
      rho'' ! a = Some v ->
      find_def a fds <> None -> v = Vfun (M.empty _) fds a). {
      intros.
      assert (HaXs: ~ In a xs). {
        apply HfdsRestr in H7. destruct H7 as [_ [_ HnodupE]].
        apply NoDup_app_remove_middle in HnodupE.
        intro Hcontra. eapply find_def_in_collect_function_vars in H3.
        eapply NoDup_app_In in HnodupE; eauto. }

    have H' := set_lists_not_In _ _ _ _ _ H2 HaXs.
    rewrite <- H' in H1.
    eapply def_funs_find_def in H3. now erewrite H' in H3. }

    remember (LH_rec [] 0 [] (LH_base [] []) []) as lh_IH.

    subst lenv_before_IH.
    have IH := IHHev Hnodup' HfenvRho' HeRestr' Hunbound' _ fAny _ lh_IH _ HlenvInjective' HenvsDisjoint'
                   state _ _ _ Hfds_before_IH HlocInBound_before_IH Hinv_before_IH HmemAvail_before_IH Hexpr HrelE'.

    destruct IH as [sr_final [fr_final [k' [lh' [Hred [Hval [Hfinst [Hfuncs [HvalPres H_INV]]]]]]]]].
    clear IHHev.
    subst lh_IH. cbn in Hred. rewrite cats0 in Hred.

    (* start execution *)
    do 4! eexists. split.
    eapply rt_trans. apply reduce_trans_frame. apply reduce_trans_label.

    eapply rt_trans. apply app_trans. apply HfargsRed.
    eapply rt_trans. apply app_trans_const. apply map_const_const_list.
    separate_instr. apply app_trans. apply HredF.
    apply app_trans_const. apply map_const_const_list.
    dostep'. apply r_return_call_indirect_success with (v:=VAL_num (N_to_value fidx)). eapply r_call_indirect_success; eauto.
    { (* table identity map *)
      have I := Hinv. destruct I as [_ [_ [_ [_ [_ [_ [_ [_ [_ [_ [_ [Htableid _]]]]]]]]]]]].
      cbn. rewrite Wasm_int.Int32.Z_mod_modulus_id.
      - rewrite N2Z.id. eapply Htableid. eassumption.
      - unfold lookup_N in H13. apply Some_notNone in H13. apply nth_error_Some in H13.
        have I := Hinv. destruct I as [_ [_ [_ [_ [_ [_ [_ [_ [_ [[HfnsBound _] _]]]]]]]]]].
        unfold max_num_functions, num_custom_funs in HfnsBound. simpl_modulus. cbn. lia. }
    { (* type *)
      have I := Hinv. destruct I as [_ [_ [_ [_ [_ [_ [_ [_ [_ [_ [_ [_ [Htype _]]]]]]]]]]]]].
      assert (Hlen: length xs = length ys). {
        apply set_lists_length_eq in H2.
        apply get_list_length_eq in H0. rewrite H2 H0. reflexivity. }
      rewrite Htype. 2: { inv HeRestr. lia. }
      rewrite -Hlen. cbn. now rewrite Nat2N.id. }
    apply rt_refl.

    dostep'. eapply r_return_invoke with (a:=fidx); try eassumption; try reflexivity.
    apply map_const_const_list.
    rewrite length_map repeat_length.
    apply const_val_list_length_eq in HfargsRes.
    apply set_lists_length_eq in H2. rewrite H2. symmetry. assumption.

    dostep'.
    eapply r_invoke_native with (vs:= map (fun a => VAL_num (N_to_value a)) args);
      try eassumption; try reflexivity.
    - unfold v_to_e_list. by rewrite -map_map_seq.
    - rewrite repeat_length length_map. apply const_val_list_length_eq in HfargsRes.
      apply set_lists_length_eq in H2. rewrite H2. assumption.
    - by apply default_vals_i32_Some.
    (* apply IH *)
    subst f_before_IH. apply Hred.

    subst f_before_IH. cbn in Hfinst.
    repeat (split; auto).
    }
  - (* Eletapp *)
    (* needs 2 IH, first one for the function body (mostly copy paste from Eapp, could be refactored),
                   second one for the continuation, similar to the other cases *)
    { inv Hrepr_e. rename args' into args_instr. rename e into e_cont, x into x_res.
      assert (Htemp: fl = fds /\ rho' = M.empty _). {
        destruct HrelE as [Hfun1 _]. eapply Hfun1 in H.
        now destruct H. apply rt_refl. }
      destruct Htemp. subst fl rho'.
      (* treat direct + indirect calls in one *)
      assert (Hval: exists fidx,
        reduce_trans (state, sr, fr, [AI_basic instr])
                     (state, sr, fr, [AI_basic (BI_const_num (N_to_value fidx))])
     /\ @repr_val_LambdaANF_Wasm (Vfun (M.empty _) fds f') sr (f_inst fr) (Val_funidx fidx)
     /\ exists e_body', repr_expr_LambdaANF_Wasm
          (create_local_variable_mapping (xs ++ collect_local_variables e_body)) e_body 0%N e_body'). {
      inv H13.
      { (* indirect call *)
        assert (Hocc: occurs_free (Eletapp x_res f t ys e_cont) f). { constructor. by left. }
        have Hrel := HrelE. destruct Hrel as [_ Hlocals].
        assert (HfNone: find_def f fds = None). {
          apply HfenvWf_None with (f:=f) in HfenvWf. rewrite HfenvWf.
          inv H3. unfold translate_var in H4. destruct (lenv ! f) eqn:Hf'; rewrite Hf' in H4=>//.
          injection H4 as ->.
          now apply HenvsDisjoint in Hf'. }
        apply Hlocals in Hocc; auto.
        destruct Hocc as [val [wal [Hrho [[j [Htrans Hwal]] Hval]]]].
        assert (i = j). { eapply repr_var_det; eassumption. } subst j.
        rewrite H in Hrho. inv Hrho. inv Hval.
        rewrite H1 in H7. inv H7.
        rename i into locIdx.
        exists idx. split.
        dostep'. apply r_local_get. eassumption. apply rt_refl. split.
        econstructor; eauto. eauto. }
      { (* direct call *)
        inv H3. unfold translate_var in H4. destruct (fenv ! f) eqn:Hf; rewrite Hf in H4=>//.
        injection H4 as ->.
        assert (Hf': exists i, fenv ! f = Some i) by eauto.
        apply HfenvWf in Hf'.
        assert (Htemp: f' = f). { apply HfenvRho in H. now inv H. now destruct Hf'. } inv Htemp.
        destruct HrelE as [Hfun1 [Hfun2 _]].
        assert (Hsubval: subval_or_eq (Vfun (M.empty term.val) fds f)
                                      (Vfun (M.empty term.val) fds f)) by constructor.
        have H' := Hfun1 _ _ _ _ _ H Hsubval. destruct H' as [_ [_ H']].
        apply Hfun2 in H'.
        destruct H' as [idx [HtransF Hval]].
        assert (idx = i). { inv HtransF. unfold translate_var in H3. now rewrite Hf in H3. }
        subst idx. exists i. split. apply rt_refl.
        split. assumption. inv Hval. rewrite H7 in H1. inv H1. eauto.
      }
    }

    destruct Hval as [fidx [HredF [Hval [e_body' HexprBody]]]]. inv Hval.
    rewrite H7 in H1. inv H1. rename H16 into Hexpr.

    repeat rewrite map_cat. cbn.
    have HrelE' := rel_env_app_letapp _ _ _ _ _ _ _ _ _ HrelE.
    have Hfargs := fun_args_reduce state _ _ _ _ _ _ _ _ _ Hinv H0 HenvsDisjoint HfenvWf HfenvRho HrelE' H12.
    destruct Hfargs as [args [HfargsRed HfargsRes]].

    remember {| f_locs := [seq (VAL_num (N_to_value a)) | a <- args] ++
                     (repeat (VAL_num (N_to_value 0)) (length (collect_local_variables e_body)));
               f_inst := f_inst fr |} as f_before_IH.

    (* prepare IH1 for e_body *)
    remember (create_local_variable_mapping (xs ++ collect_local_variables e_body)) as lenv_before_IH.

    assert (Hfds_before_IH: fds_translated_correctly fds sr (f_inst f_before_IH)). {
      intros ???? Hfd. subst f_before_IH. cbn.
      apply Hfds in Hfd as [fidx' [Ha Hv]]. now exists fidx'. }

    assert (HlocInBound_before_IH: (forall (var : positive) (varIdx : localidx),
       @repr_var nenv (create_local_variable_mapping (xs ++ collect_local_variables e_body)) var varIdx -> N.to_nat varIdx < length (f_locs f_before_IH))). {
      intros ?? Hvar. subst f_before_IH. cbn. inv Hvar. apply var_mapping_list_lt_length in H1.
      rewrite length_app in H1. apply const_val_list_length_eq in HfargsRes.
      rewrite length_app. rewrite length_map -HfargsRes.
      rewrite map_repeat_eq. rewrite length_map. apply set_lists_length_eq in H2.
      now rewrite -H2.
    }

    assert (Hinv_before_IH : INV sr f_before_IH). {
       subst. now eapply init_locals_preserves_INV. }

    assert (HmemAvail_before_IH : min_available_memory sr (f_inst f_before_IH) 0). {
      intros ?? Hm Hglob Hbound.
      destruct Hinv_before_IH as [_[_[_[_[_[_[_[HgmpInM _]]]]]]]].
      have H' := HgmpInM _ _ Hm Hglob Hbound. lia. }

    assert (HrelE_before_IH: @rel_env_LambdaANF_Wasm lenv_before_IH e_body rho'' sr f_before_IH fds). {
      unfold rel_env_LambdaANF_Wasm. split.
      { (* funs1 *) intros.
        assert (Hdec: decidable_eq var). {
          intros n m. unfold Decidable.decidable. now destruct (var_dec n m). }
       have H' := In_decidable Hdec x xs. clear Hdec. destruct H'.
       - (* In x xs *)
         have H' := set_lists_In _ _ _ _ _ _ H4 H1 H2.
         destruct (get_list_In_val _ _ _ _ H0 H') as [y [Hiny HyRho]].
         now destruct HrelE as [Hfun1 [Hfun2 _]]; eauto.
       - (* ~In x xs *)
         have H' := set_lists_not_In _ _ _ _ _ H2 H4. rewrite H1 in H'.
         erewrite def_funs_find_def in H'.
         2:{ intro Hcontra. apply def_funs_not_find_def with (fds':=fds) (rho:=M.empty _) in Hcontra.
             rewrite Hcontra in H'. inv H'. } inv H'.
         have H' := set_lists_not_In _ _ _ _ _ H2 H4.
         rewrite H1 in H'.
         apply def_funs_spec in H'. destruct H' as [[? ?] | [? Hcontra]]. 2: inv Hcontra.
         apply subval_fun in H3. 2: assumption.
         destruct H3 as [f1 [?H ?H]]. inv H3. inv H8 => //.
      } split.
      { (* funs2 *)
        intros ? Hnfd. destruct HrelE as [_ [Hfun2 _]].
        apply Hfun2 in Hnfd.
        destruct Hnfd as [i [Htrans Hval]].
        exists i. split. assumption. subst f_before_IH. assumption. }
      { (* vars *)
        intros. destruct HrelE as [_ HrelVars].
        assert (In x xs). {
          apply HfdsRestr in H7. destruct H7 as [? [Hxxs ?]].
          have H' := Hxxs _ H1. now destruct H'. }
        have H' := get_set_lists_In_xs _ _ _ _ _ H4 H2. destruct H' as [v'' Hv'].
        have H' := set_lists_nth_error _ _ _ _ _ _ H4 Hv' H2.
        destruct H' as [k' [Hvk' Hxk']].
        have H'' := const_val_list_nth_error _ _ _ _ _ _ HfargsRes Hvk'.
        destruct H'' as [w [Hw Hnth]].
        exists v'', w. split; auto. split; auto.

        unfold stored_in_locals. subst lenv_before_IH f_before_IH. exists (N.of_nat k').
        split. {
          econstructor. intros. unfold create_local_variable_mapping.
          rewrite (var_mapping_list_lt_length_nth_error_idx _ (N.of_nat k')); auto.
          apply HfdsRestr in H7. destruct H7 as [_ [_ HnodupE]].
          rewrite catA in HnodupE. apply NoDup_app_remove_r in HnodupE. assumption.
          unfold lookup_N. rewrite Nat2N.id.
          rewrite nth_error_app1; auto. apply nth_error_Some. intro.
          rewrite H5 in Hxk'. inv Hxk'. }
        cbn.
        unfold lookup_N. rewrite Nat2N.id.
        rewrite nth_error_app1. 2: {
          rewrite length_is_size size_map -length_is_size.
          apply const_val_list_length_eq in HfargsRes.
          rewrite -HfargsRes.
          apply nth_error_Some. congruence. } assumption.
        subst f_before_IH. assumption. }
    }

    assert (HeRestr' : expression_restricted cenv e_body). {
        apply HfdsRestr in H7. now destruct H7. }

    assert (Hunbound': (forall x : var, In x (collect_local_variables e_body) -> rho'' ! x = None)). {
      intros.
      assert (~ exists v, find_def x fds = Some v). {
        intro Hcontra. destruct Hcontra as [? Hfd].
        assert (Hfd': find_def x fds <> None) by congruence.
        clear Hfd. rename Hfd' into Hfd.
        eapply find_def_in_collect_function_vars in Hfd.
        apply HfdsRestr in H7. destruct H7 as [_ [_ HnodupE]].
        apply NoDup_app_remove_l in HnodupE.
        eapply NoDup_app_In in HnodupE; eauto. }
      assert (Hfd: find_def x fds = None). { destruct (find_def x fds); eauto. exfalso. eauto. }
      apply def_funs_not_find_def with (fds':=fds) (rho:=M.empty _) in Hfd.
      assert (HxIn: ~ In x xs). {
        intro Hcontra.
        apply HfdsRestr in H7. destruct H7 as [_ [_ HnodupE]].
        rewrite catA in HnodupE. apply NoDup_app_remove_r in HnodupE.
        eapply NoDup_app_In in HnodupE; eauto. }
      have H'' := set_lists_not_In _ _ _ _ _ H2 HxIn. rewrite <- H''.
      now rewrite Hfd.
    }

    assert (HlenvInjective': map_injective lenv_before_IH). {
      subst lenv_before_IH.
      apply create_local_variable_mapping_injective.
      apply HfdsRestr in H7. destruct H7 as [_ [_ HnodupE]].
      rewrite catA in HnodupE. now apply NoDup_app_remove_r in HnodupE.
    }

    assert (HenvsDisjoint': domains_disjoint lenv_before_IH fenv). {
      apply HfdsRestr in H7. destruct H7 as [_ [_ HnodupE]].
      subst lenv_before_IH. unfold domains_disjoint. split; intros.
      { (* -> *)
        apply variable_mapping_Some_In in H1; auto.
        assert (~ exists v, fenv ! x = Some v). {
          intro Hcontra. apply HfenvWf in Hcontra.
          apply notNone_Some in Hcontra.
          eapply find_def_in_collect_function_vars in Hcontra.
          rewrite catA in HnodupE. eapply NoDup_app_In in HnodupE; eauto. }
          destruct (fenv ! x) eqn:Hx; auto. exfalso. eauto. }
      { (* <- *)
         assert (exists res : fun_tag * seq var * exp, find_def x fds = Some res).
           apply HfenvWf; eauto.
         apply notNone_Some in H3.
         eapply find_def_in_collect_function_vars in H3.
         apply variable_mapping_NotIn_None; auto.
         rewrite catA in HnodupE. intro Hcontra.
         eapply NoDup_app_In in HnodupE; eauto. }
    }

    assert (Hnodup': NoDup (collect_local_variables e_body ++
                            collect_function_vars (Efun fds e_body))). {
      apply HfdsRestr in H7. destruct H7 as [_ [_ HnodupE]].
      apply NoDup_app_remove_l in HnodupE.
      assumption. }

    assert (HfenvRho': forall (a : positive) (v : term.val),
      rho'' ! a = Some v ->
      find_def a fds <> None -> v = Vfun (M.empty _) fds a). {
      intros.
      assert (HaXs: ~ In a xs). {
        apply HfdsRestr in H7. destruct H7 as [_ [_ HnodupE]].
        apply NoDup_app_remove_middle in HnodupE.
        intro Hcontra. eapply find_def_in_collect_function_vars in H3.
        eapply NoDup_app_In in HnodupE; eauto. }

      have H' := set_lists_not_In _ _ _ _ _ H2 HaXs.
      rewrite <- H' in H1.
      eapply def_funs_find_def in H3. now erewrite H' in H3. }

    remember (LH_rec [] 0 [] (LH_base [] []) []) as lh_before_IH.

    subst lenv_before_IH.
    have IH_body := IHHev1 Hnodup' HfenvRho' HeRestr' Hunbound' _ fr _ lh_before_IH _ HlenvInjective' HenvsDisjoint'
                   state _ _ _ Hfds_before_IH HlocInBound_before_IH Hinv_before_IH HmemAvail_before_IH Hexpr HrelE_before_IH.

    destruct IH_body as [sr_after_call [fr_after_call [k0 [lh0 [Hred [Hval [Hfinst [Hfuncs [HvalPres H_INV]]]]]]]]].
    clear HfenvRho' Hnodup' Hunbound' HeRestr' IHHev1.
    subst lh_before_IH. cbn in Hred. rewrite cats0 in Hred.

    assert (Hcont: exists (sr_final : store_record) (fr_final : frame) k' (lh' : lholed k'),
      reduce_trans (state, sr_after_call, fAny, [AI_frame 0 fr
                      (lfill lh ([ AI_basic (BI_global_get glob_out_of_mem)
                                 ; AI_basic (BI_if (BT_valtype None) [:: BI_return ] [::])
                                 ; AI_basic (BI_global_get glob_result)
                                 ; AI_basic (BI_local_set x') ] ++ (map AI_basic e')))])
                   (state, sr_final, fAny, [AI_frame 0 fr_final (lfill lh' [:: AI_basic BI_return])])
         /\ result_val_LambdaANF_Wasm v' sr_final (f_inst fr_final)
         /\ f_inst fr_final = f_inst fr
         /\ s_funcs sr_final = s_funcs sr
            (* previous values are preserved *)
         /\ (forall wal val, repr_val_LambdaANF_Wasm val sr (f_inst fr) wal ->
                             repr_val_LambdaANF_Wasm val sr_final (f_inst fr) wal)
         /\ (INV_glob_out_of_mem_is_zero sr_final fr_final -> INV sr_final fr_final)). {
      destruct Hval as [Hsuccess | HOutOfMem].
      { (* success *)
        clear Hexpr. rename H11 into Hexpr.
        destruct Hsuccess as [w [wal [Hres [Heq [Hval HresM]]]]].
        remember ({|f_locs := set_nth (VAL_num (VAL_int32 w)) (f_locs fr) (N.to_nat x') (VAL_num (VAL_int32 (wasm_value_to_i32 wal)));
                    f_inst := f_inst fr|}) as f_before_cont.

        (* prepare IH for continuation *)
        assert (Hnodup': NoDup (collect_local_variables e_cont ++
                                collect_function_vars (Efun fds e_cont))). {
          cbn in Hnodup. now inv Hnodup.
        }

        assert (HfenvRho': forall (a : positive) (v0 : val),
          (map_util.M.set x_res v rho) ! a = Some v0 ->
          find_def a fds <> None -> v0 = Vfun (M.empty val) fds a). {
          intros. apply HfenvRho; auto.
          rewrite M.gso in H1; auto. intro Hcontra. subst a.
          apply notNone_Some in H3. apply HfenvWf in H3. destruct H3.
          destruct HenvsDisjoint as [Hd1 Hd2].
          apply Hd2 in H1. inv H10. unfold translate_var in H3. now rewrite H1 in H3.
        }

        assert (HeRestr': expression_restricted cenv e_cont). { now inv HeRestr. }

        assert (Hunbound': (forall x : var, In x (collect_local_variables e_cont) ->
                               (map_util.M.set x_res v rho) ! x = None)). {
          intros.
          assert (~ In x_res (collect_local_variables e_cont)). {
            apply NoDup_app_remove_r in Hnodup. cbn in Hnodup.
            now apply NoDup_cons_iff in Hnodup. }
          rewrite M.gso; auto.
          apply Hunbound. now right. now intro.
        }

        assert (HlocInBound_before_cont_IH: (forall (var : positive) (varIdx : localidx),
          @repr_var nenv lenv var varIdx -> N.to_nat varIdx < length (f_locs f_before_cont))). {
           intros ?? Hvar. subst f_before_cont. cbn.
          rewrite length_is_size size_set_nth maxn_nat_max -length_is_size.
          apply HlocInBound in Hvar. lia. }

        assert (Hinv_before_cont_IH: INV sr_after_call f_before_cont). {
          subst f_before_cont f_before_IH; cbn in Hfinst.
          eapply update_local_preserves_INV. 3: subst w; reflexivity.
          eapply change_locals_preserves_INV with (l := f_locs fr).
          apply H_INV. rewrite Hfinst in HresM. apply HresM.
          have I := Hinv. destruct I as [_ [_ [_ [_ [_ [_ [_ [_ [Hlocs32 _]]]]]]]]]. assumption.
          rewrite -Hfinst. now destruct fr.
          eapply HlocInBound. eassumption. }

        assert (HmemAvail_before_cont_IH : min_available_memory sr_after_call (f_inst f_before_cont) 0). {
          intros ?? Hm Hglob Hbound.
          destruct Hinv_before_cont_IH as [_[_[_[_[_[_[_[HgmpInM _]]]]]]]].
          have H' := HgmpInM _ _ Hm Hglob Hbound. lia. }

        assert (Hfds_before_cont_IH : fds_translated_correctly fds sr_after_call (f_inst f_before_cont)). {
          intros ???? Hfd. subst f_before_cont. cbn.
          apply Hfds in Hfd as [fidx' [Ha Hv]]. exists fidx'.
          split=>//.
          eapply val_relation_func_depends_on_funcs; eauto. }

        assert (HrelE_before_cont_IH: @rel_env_LambdaANF_Wasm lenv e_cont (map_util.M.set x_res v rho) sr_after_call f_before_cont fds). {
          unfold rel_env_LambdaANF_Wasm. split; intros.
          { (* funs1 *)
            destruct (var_dec x x_res).
            { (* x = x_res *)
              subst x_res. rewrite M.gss in H1. inv H1. rename v0 into v.
              destruct HrelE as [Hfun1 [Hfun2 _]].
              assert (Hsubval: subval_or_eq (Vfun (M.empty val) fds f0)
                                            (Vfun (M.empty val) fds f0)).
              { apply rt_refl. }
              have H''1 := Hfun1 _ _ _ _ _ _ Hsubval.
              have H' := step_preserves_empty_env_fds _ _ _ _ _ _ fds' _ _ _ _ HprimFunsRet Hev1 H3.
              edestruct H'.
              { intros ? ? ? ? ? Hrho Hsubval'.
                assert (Hdec: decidable_eq var). { intros n m.
                unfold Decidable.decidable. now destruct (var_dec n m). }
                have H'' := In_decidable Hdec x0 xs. destruct H''.
                - (* In x0 xs *)
                  have H'' := set_lists_In _ _ _ _ _ _ H1 Hrho H2.
                  destruct (get_list_In_val _ _ _ _ H0 H'') as [y [HyIn HyRho]].
                  have H12' := Hfun1 _ _ _ _ _ HyRho Hsubval'.
                  now destruct H12' as [?[??]].
                - (* ~In x0 xs *)
                  have H'' := set_lists_not_In _ _ _ _ _ H2 H1.
                  rewrite Hrho in H''.
                  erewrite def_funs_find_def in H''. 2: {
                    intro Hcontra. eapply def_funs_not_find_def  in Hcontra.
                    erewrite Hcontra in H''. inv H''. }
                  inv H''.
                  have H'' := set_lists_not_In _ _ _ _ _ H2 H1.
                  rewrite Hrho in H''.
                  apply subval_fun in Hsubval'.
                  destruct Hsubval' as [ff [Heq Hfundef]]. now inv Heq.
                  apply def_funs_spec in H''. destruct H'' as [[tuple Hfd] | Hcontra].
                  assumption. now destruct Hcontra.
              }
              {
                intros ? ? ? ? [HbodyNofun | HfdsNofun].
              - eapply repr_expr_LambdaANF_Wasm_no_Efun_subterm; eauto.
              - destruct HfdsNofun as [Hsub HsubFds].
                eapply dsubterm_fds_e_find_def in HsubFds.
                2:{ now apply NoDup_app_remove_l in Hnodup. }
                destruct HsubFds as [? [? [? Hfd]]].
                have Hfd' := Hfd.
                eapply Hfds in Hfd. destruct Hfd as [? [_ HvalFun]]. inv HvalFun.
                assert (e = e'') by congruence. subst e''.
                eapply repr_expr_LambdaANF_Wasm_no_Efun_subterm; eauto. }
              { now destruct H4. }
           }
           { (* x <> x_res*)
             rewrite M.gso in H1; auto.
             destruct HrelE' as [Hfun1 [Hfun2 Hvar]].
             have H' := Hfun1 _ _ _ _ _ H1 H3. assumption.
           }
         } split.
         { (* funs2 *)
            intros ? Hnfd. destruct HrelE as [_ [Hfun2 _]].
            apply Hfun2 in Hnfd.
            destruct Hnfd as [i [Htrans' Hval']].
            exists i. split. assumption.
            eapply val_relation_func_depends_on_funcs with (s:=sr). congruence.
            subst f_before_cont. assumption.
          }
          { (* local vars *)
            intros. destruct (var_dec x x_res).
            { (* x = x_res *)
              subst x_res.
              exists v. exists wal. split.
              now rewrite M.gss.
              split. exists x'. split. assumption.
              have Hl := HlocInBound _ _ H10. apply nth_error_Some in Hl.
              apply notNone_Some in Hl. destruct Hl. subst f_before_cont.
              eapply set_nth_nth_error_same. eassumption.
              subst f_before_cont f_before_IH. assumption. }
            { (* x <> x_res *)
              assert (Hocc: occurs_free (Eletapp x_res f t ys e_cont) x).
              { now apply Free_Eletapp2. }
              destruct HrelE as [_ [_ Hvar]].

              apply Hvar in Hocc; auto. destruct Hocc as [v6 [wal' [Henv' [Hloc' Hval']]]].
              exists v6. exists wal'. repeat split; auto.
              rewrite M.gso. assumption. auto.
              destruct Hloc' as [x1' [? ?]].
              unfold stored_in_locals. cbn.

              assert (x1' <> x'). {
                intro. subst x1'.
                have Hcontra := repr_var_inj _ _ _ _ HlenvInjective H10 H4.
                contradiction. }
              exists x1'. split; auto. subst f_before_cont. cbn.
              unfold lookup_N.
              rewrite set_nth_nth_error_other; eauto.
              have Hl := HlocInBound _ _ H10. now intro.
              subst f_before_cont f_before_IH. rewrite -Hfinst in HvalPres.
              apply HvalPres. assumption.
            }
          }
        }

        have IH_cont := IHHev2 Hnodup' HfenvRho' HeRestr' Hunbound' _ fAny _ lh lenv HlenvInjective HenvsDisjoint
                   state _ _ _ Hfds_before_cont_IH HlocInBound_before_cont_IH Hinv_before_cont_IH HmemAvail_before_cont_IH Hexpr HrelE_before_cont_IH.
        destruct IH_cont as [sr_final [fr_final [k_final [lh_final [Hred' [Hval' [Hfinst' [Hfuncs' [HvalPres' H_INV']]]]]]]]]. clear IHHev2.

        exists sr_final, fr_final, k_final, lh_final. split.

        eapply rt_trans. apply reduce_trans_frame.
        apply reduce_trans_label. apply app_trans.
        dostep_nary 0. apply r_global_get. subst f_before_IH. eassumption.
        dostep_nary 1. constructor. apply rs_if_false. reflexivity.
        dostep_nary 0. eapply r_block with (t1s:=[::]) (t2s:=[::])(vs:=[::]); auto. cbn.
        dostep_nary 0. constructor. apply rs_label_const =>//.
        dostep_nary 0. apply r_global_get. subst f_before_IH. eassumption.
        dostep_nary' 1. eapply r_local_set' with (f' := f_before_cont).
        subst f_before_cont. reflexivity.
        apply /ssrnat.leP. eapply HlocInBound. eassumption.
        subst f_before_cont w. reflexivity. apply rt_refl.
        (* IH *)
        cbn. apply Hred'.

        subst f_before_cont f_before_IH. rewrite -Hfinst'.
        repeat (split; auto).
        congruence.
        intros. { rewrite -Hfinst' in HvalPres'. apply HvalPres'.
                  cbn. rewrite -Hfinst in HvalPres. apply HvalPres. assumption. }
      }
      { (* out of mem *)

       (* split of dead instructions after
         (BI_if (BT_valtype None) [:: BI_return] [::]) *)
        separate_instr.
        match goal with
        |- context C [reduce_trans (_, _, _, [:: AI_frame _ _ (lfill _
           (_ ++ [:: AI_basic (BI_if (BT_valtype None) [:: BI_return] [::])] ++ ?es))])] =>
            let es_tail := fresh "es_tail" in
            remember es as es_tail
        end.

        have Hlh := lholed_nested_label _ lh [AI_basic BI_return] es_tail. subst es_tail.
        destruct Hlh as [k' [lh' Heq']]. cbn in Heq'.

        exists sr_after_call, fr. eexists. exists lh'. split.

        eapply rt_trans.
        apply reduce_trans_frame. apply reduce_trans_label.
        dostep_nary 0. apply r_global_get. subst f_before_IH. eassumption.
        dostep_nary 1. constructor. apply rs_if_true. intro Hcontra. inv Hcontra.
        dostep_nary 0. eapply r_block with (t1s:=[::]) (t2s:=[::])(vs:=[::]); auto.
        apply rt_refl. rewrite Heq'. apply rt_refl.

        split. right. subst f_before_IH. assumption.
        split. reflexivity. split. congruence. split.
        { intros. subst f_before_IH. cbn in Hfinst.
          rewrite -Hfinst in HvalPres. apply HvalPres.
          assumption. }
        intro Hcontra. unfold INV_glob_out_of_mem_is_zero in Hcontra.
        subst f_before_IH. cbn in Hfinst.
        rewrite HOutOfMem in Hcontra. inv Hcontra.
      }
    }
    destruct Hcont as [sr_final [fr_final [k_final [lh_final [Hred_final [Hval_final [Hfinst' [Hfuncs' [HvalPres' H_INV']]]]]]]]].

    (* start execution *)
    do 4! eexists. split.
    eapply rt_trans. eapply reduce_trans_frame. apply reduce_trans_label.
    eapply rt_trans. apply app_trans. apply HfargsRed.
    eapply rt_trans. apply app_trans_const. apply map_const_const_list.
    separate_instr. apply app_trans. apply HredF.
    eapply rt_trans. apply app_trans_const. apply map_const_const_list.
    apply app_trans with (es :=
             [:: AI_basic (BI_const_num (N_to_value fidx));
                 AI_basic (BI_call_indirect 0%N (N.of_nat (length ys)))]).
    dostep'. eapply r_call_indirect_success; eauto.
    { (* table identity map *)
      have I := Hinv. destruct I as [_ [_ [_ [_ [_ [_ [_ [_ [_ [_ [_ [Htableid _]]]]]]]]]]]].
      cbn. rewrite Wasm_int.Int32.Z_mod_modulus_id.
      - rewrite N2Z.id. eapply Htableid. eassumption.
      - unfold lookup_N in H15. apply Some_notNone in H15. apply nth_error_Some in H15.
        have I := Hinv. destruct I as [_ [_ [_ [_ [_ [_ [_ [_ [_ [[HfnsBound _] _]]]]]]]]]].
        unfold max_num_functions, num_custom_funs in HfnsBound. simpl_modulus. cbn. lia. }
    { (* type *)
      have I := Hinv. destruct I as [_ [_ [_ [_ [_ [_ [_ [_ [_ [_ [_ [_ [Htype _]]]]]]]]]]]]].
      assert (Hlen: length xs = length ys). {
        apply set_lists_length_eq in H2.
        apply get_list_length_eq in H0. rewrite H2 H0. reflexivity. }
      rewrite Htype. 2: { inv HeRestr. lia. } rewrite -Hlen. cbn. now rewrite Nat2N.id. } apply rt_refl.
    rewrite catA. cbn. eapply rt_trans.
    eapply app_trans with (es := ([seq AI_basic (BI_const_num (N_to_value a)) | a <- args] ++ [:: AI_invoke fidx])).
    (* enter function *)
    dostep'. eapply r_invoke_native with (vs:= map (fun a => (VAL_num (N_to_value a))) args); try eassumption.
    reflexivity. reflexivity.
    unfold v_to_e_list. now rewrite -map_map_seq.
    reflexivity. reflexivity.
    { rewrite repeat_length length_map.
      apply const_val_list_length_eq in HfargsRes.
      apply set_lists_length_eq in H2. now rewrite H2. }
    reflexivity. cbn. apply default_vals_i32_Some.
    (* apply IH1: function body *)
    subst f_before_IH. apply Hred. apply rt_refl.
    eapply rt_trans. apply reduce_trans_frame. apply reduce_trans_label.
    dostep_nary 0. constructor. apply rs_return with (lh:=lh0) (vs:=[::]) => //.
    cbn. apply rt_refl.
    (* apply IH2: continuation *)
    eapply rt_trans. apply Hred_final. apply rt_refl.
    rewrite Hfinst' in Hval_final.
    rewrite Hfinst'.
    by repeat (split; auto).
    }
  - (* Efun *)
    inv Hrepr_e. (* absurd, fn defs only on topmost level *)
  - (* Eprim_val *)
    { inv Hrepr_e.
      (* prepare calling memory_grow_reduce *)
      have I := Hinv. destruct I as [_[_[_[Hgmp_w[_[Hmut[_[_[_[HfnsBound[_[_[_[_ [HfuncGrow HfuncsId]]]]]]]]]]]]]]].
      assert (HpageSize : (32 < page_size)%N). { unfold page_size. lia. }

      destruct (i32_glob_implies_i32_val _ _ _ gmp_i32_glob Hgmp_w Hmut) as [g' Hgmp].
      destruct (i32_exists_N g') as [gmp [-> HgmpBound]].

      have Hgrowmem := memory_grow_reduce state sr _ _ _ _ _ _ HpageSize HmemAvail H8 Hinv Hgmp HgmpBound.
      destruct Hgrowmem as [[s' [Hred [Hsfuncs [HvalPreserved [Hinv' Henoughmem]]]]]
                            | HRedRet].
      { (* Successfully grow memory if necessary *)
        (* invariants after reducing grow *)
        have I := Hinv'. destruct I as [_ [_ [_ [_ [_ [_ [Hlinmem _]]]]]]].
        destruct Hlinmem as [Hmem1 [m [Hmem2 [size [<- [Hmem4 Hmem5]]]]]].
        have HenoughM := Henoughmem _ Hmem2. destruct HenoughM as [Hgmp' HenoughM]. clear Henoughmem.
        assert ((Z.of_N gmp < Wasm_int.Int32.modulus)%Z). {
          apply mem_length_upper_bound in Hmem5. cbn in Hmem5. simpl_modulus. cbn. lia. }

        (* There exists memory containing the new value *)
        assert (exists mem, store m (Wasm_int.N_of_uint i32m (N_to_i32 gmp)) 0%N
                                    (serialise_num (VAL_int64 v0)) 8 = Some mem)
            as [m_after_store Hm_after_store].
        { apply notNone_Some. apply enough_space_to_store. cbn.
          rewrite length_serialise_num_i64.
          rewrite Wasm_int.Int32.Z_mod_modulus_id; lia. }

        remember (upd_s_mem s' (set_nth m_after_store s'.(s_mems) 0 m_after_store)) as s_prim.
        assert (HmStore: smem_store s' (f_inst fr) (Wasm_int.N_of_uint i32m (N_to_i32 gmp))
                         0%N (VAL_int64 v0) T_i64 = Some s_prim).
        { subst s_prim.
          unfold smem_store. rewrite Hmem1. cbn.
          unfold smem in Hmem2. rewrite Hmem1 in Hmem2. destruct (s_mems s')=>//.
          injection Hmem2 as ->. now rewrite Hm_after_store. }

        assert (HgmpPreserved: sglob_val s_prim (f_inst fr) glob_mem_ptr = Some (VAL_num (VAL_int32 (N_to_i32 gmp)))). {
          subst s_prim.
          unfold upd_s_mem, sglob_val, sglob. cbn.
          unfold sglob_val, sglob in Hgmp'. cbn in Hgmp'.
          now destruct (inst_globals (f_inst fr)).
        }

        assert (Hgmp_v_mult_two: exists n, (gmp = 2 * n)%N). {
          destruct Hinv' as [_ [_ [_ [_ [_ [_ [_ [_ [_ [_ [_ [_ [_ Hgmp_mult_two]]]]]]]]]]]]].
          eapply Hgmp_mult_two; try eassumption; try lia.
        }

        assert (HmemLengthPreserved: mem_length m = mem_length m_after_store). {
          apply store_length in Hm_after_store. congruence. }

        assert (HmemPreserved: smem s_prim (f_inst fr) = Some m_after_store). {
          subst s_prim. cbn.
          unfold smem. rewrite Hmem1. cbn. by destruct (s_mems s').
        }

        assert (Hinv_prim : INV s_prim fr). {
          subst.
          assert (mem_length m = mem_length m_after_store). {
            apply store_length in Hm_after_store. congruence. }
          apply store_lim_max in Hm_after_store.
          eapply update_mem_preserves_INV with (m':=m_after_store); eauto; first lia.
          congruence. exists (mem_size m). split; auto. now unfold mem_size. }

        remember ({|f_locs := set_nth (VAL_num (VAL_int32 (N_to_i32 gmp))) (f_locs fr) (N.to_nat x') (VAL_num (VAL_int32 (N_to_i32 gmp)));
                    f_inst := f_inst fr|}) as f_before_IH.


        have I := Hinv_prim. destruct I as [_ [_ [_ [Hgmp_w' _]]]].

        (* New store with gmp incremented by 8 *)
        destruct (Hgmp_w' (VAL_int32 (Wasm_int.Int32.iadd (N_to_i32 gmp) (N_to_i32 8)))) as [s_before_IH Hs_before_IH].
        edestruct i32_exists_N as [gmp' [HgmpEq HgmpBound']].
        erewrite HgmpEq in Hs_before_IH.
        assert (gmp' = gmp + 8)%N. {
          inversion HgmpEq.
          repeat rewrite Wasm_int.Int32.Z_mod_modulus_id in H1; try lia.
          unfold store in Hm_after_store.
          destruct ((Wasm_int.N_of_uint i32m (N_to_i32 gmp) + 0 + N.of_nat 8
                     <=? mem_length m)%N) eqn:Har. 2: by now inv Har.
          apply N.leb_le in Har. cbn in Har.
          simpl_eq.
          apply mem_length_upper_bound in Hmem5. cbn in Hmem5.
          simpl_modulus. cbn. simpl_eq. rewrite Wasm_int.Int32.Z_mod_modulus_id; lia. }
        subst gmp'.

        assert (Hinv_before_IH : INV s_before_IH f_before_IH). {
          assert (INV s_prim f_before_IH). { eapply update_local_preserves_INV; eauto. }
          eapply update_global_preserves_INV with (i:=glob_mem_ptr) (num:=(VAL_int32 (N_to_i32 (gmp + 8)))); eauto.
          left. split. apply gmp_i32_glob. now cbn.
          discriminate.
          now subst f_before_IH.
          { move => _.
            intros n [Heqn Hboundn].
            assert ((8 + 8 < Z.of_N page_size)%Z). { unfold page_size. lia. }
            replace n with (gmp + 8)%N.
            lia.
            inv Heqn. now simpl_eq. }
          { move => _.
            intros n [Heqn Hboundn].
            destruct Hgmp_v_mult_two as [n' Hn'].
            replace n with (gmp + 8)%N.
            exists (n' + 4)%N. lia.
            inv Heqn. now simpl_eq. }
          subst f_before_IH. by apply Hs_before_IH.
        }

        assert (HmemAvail_before_IH : min_available_memory s_before_IH (f_inst f_before_IH) mem'). {
          intros ?? Hmem Hgmp'' HgmpBound''.
          subst f_before_IH.
          have Hm := Hs_before_IH. apply update_global_preserves_memory in Hm.
          apply update_global_get_same in Hs_before_IH.
          rewrite Hs_before_IH in Hgmp''.
          inversion Hgmp''. simpl_eq. subst gmp0.
          apply store_length in Hm_after_store.
          rewrite -Hm in Hmem. solve_eq m0 m_after_store.
          lia.
        }

        assert (HmemPreserved': smem s_before_IH (f_inst fr) = Some m_after_store). {
          subst s_prim. cbn.
          apply update_global_preserves_memory in Hs_before_IH. rewrite -Hs_before_IH. cbn.
          by destruct (s_mems s'). }

        assert (HlocInBound' : forall (var : positive) (varIdx : localidx),
                   @repr_var nenv lenv var varIdx -> N.to_nat varIdx < length (f_locs f_before_IH)). {
          intros ?? Hvar. subst f_before_IH. cbn.
          rewrite length_is_size size_set_nth maxn_nat_max -length_is_size.
          apply HlocInBound in Hvar, H3. lia.
        }

        assert (Hnodup' : NoDup (collect_local_variables e ++ collect_function_vars (Efun fds e)) ). {
          cbn in Hnodup. apply NoDup_cons_iff in Hnodup. now destruct Hnodup.
        }

        assert (HfenvRho' :  forall (a : positive) (v : val),
                   (map_util.M.set x (Vprim p) rho) ! a = Some v -> find_def a fds <> None -> v = Vfun (M.empty val) fds a). {
          intros. apply HfenvRho; auto. rewrite M.gso in H0. assumption.
          intro. subst a. apply notNone_Some in H1. apply HfenvWf in H1. destruct H1. inv H0.
          destruct HenvsDisjoint as [Hd1 Hd2]. apply Hd2 in H2. unfold translate_var in H2.
          inv H3. unfold translate_var in H0. rewrite H2 in H0. inv H0.
        }

        assert (HeRestr' : expression_restricted cenv e) by now inv HeRestr.

        assert (Hunbound' : forall x0 : var, In x0 (collect_local_variables e) -> (map_util.M.set x (Vprim p) rho) ! x0 = None). {
          intros.
          apply NoDup_app_remove_r in Hnodup.
          cbn in Hnodup.
          apply NoDup_cons_iff in Hnodup.
          rewrite M.gso.
          apply Hunbound.
          unfold collect_local_variables.
          cbn.
          fold collect_local_variables.
          right. assumption.
          destruct Hnodup as [Hx _ ].
          unfold not. unfold not in Hx. intros Heq. subst x.
          apply Hx in H0. contradiction.
        }

        (* Equivalence of store functions *)
        assert (HfsEq1: s_funcs s' = s_funcs s_prim) by now subst.
        assert (HfsEq2: s_funcs s_prim = s_funcs s_before_IH) by now apply update_global_preserves_funcs in Hs_before_IH.
        assert (HfsEq3: s_funcs s' = s_funcs s_before_IH) by now subst.
        assert (HfsEq4: s_funcs sr = s_funcs s_before_IH) by now subst.
        assert (Hfds' : fds_translated_correctly fds s_before_IH (f_inst f_before_IH)). {
          intros ???? Hfd. subst f_before_IH. cbn.
          apply Hfds in Hfd as [fidx' [Ha Hv]]. exists fidx'.
          split=>//.
          eapply val_relation_func_depends_on_funcs; eauto. }

        assert (Hv_int: exists n, p = primInt n) by now destruct p; destruct x0.
        destruct Hv_int as [n Hn].
        assert (Hv0: v0 = Z_to_i64 (to_Z n)). {
          rewrite Hn in H7. unfold translate_primitive_value in *.
          now simpl in H7.
        }

        assert (Hvalue : repr_val_LambdaANF_Wasm (Vprim (primInt n)) s_before_IH (f_inst f_before_IH) (Val_ptr gmp)). {
          apply Rprim_v with (gmp := (gmp + 8)%N) (m := m_after_store) (addr := gmp); auto; try lia.
          { apply update_global_get_same with (sr:=s_prim). subst f_before_IH. assumption. }
          { subst f_before_IH. assumption. }
          { apply store_load_i64 in Hm_after_store; auto.
            assert (wasm_deserialise (serialise_num (VAL_int64 v0)) T_i64 = VAL_int64 v0)
                by now apply deserialise_serialise.

            rewrite H0 in Hm_after_store.
            replace (Wasm_int.N_of_uint i32m (N_to_i32 gmp)) with gmp in Hm_after_store.
            rewrite <-Hv0. assumption.
            cbn. rewrite Wasm_int.Int32.Z_mod_modulus_id; lia.
          }
        }

        assert (HmemLengthBound: (Z.of_N (mem_length m) < Wasm_int.Int32.modulus)%Z). {
          apply mem_length_upper_bound in Hmem5. simpl_modulus_in Hmem5. cbn in Hmem5.
          simpl_modulus. cbn. lia.
        }

        (* Before the continuation, the gmp global contains the old gmp value incremented by 8 *)
        assert (HglobalUpdatedGmp: sglob_val s_before_IH (f_inst fr) glob_mem_ptr = Some (VAL_num (VAL_int32 (N_to_i32 (gmp + 8)))))
            by now apply update_global_get_same with (sr:=s_prim) (sr':=s_before_IH).

        (* All values in memory below the gmp are preserved *)
        assert (HvalsInMemPreserved: forall a, (a + 4 <= gmp)%N -> load_i32 m a = load_i32 m_after_store a). {
          intros a Ha.
          assert (Hex: exists v, load_i32 m a = Some v). {
            apply enough_space_to_load. lia. }
          destruct Hex as [v' Hv'].
          rewrite Hv'. symmetry.
          apply (load_store_load_i32' m m_after_store a (Wasm_int.N_of_uint i32m (N_to_i32 gmp)) v' (serialise_num (VAL_int64 v0))); auto.
          cbn. rewrite Wasm_int.Int32.Z_mod_modulus_id; lia.
        }

        assert (HvalsInMemPreserved': forall a, (a + 8 <= gmp)%N -> load_i64 m a = load_i64 m_after_store a). {
          intros a Ha.
          assert (Hex: exists v, load_i64 m a = Some v). {
            apply enough_space_to_load_i64. lia. }
          destruct Hex as [v' Hv'].
          rewrite Hv'. symmetry.
          apply (load_store_load_i64' m m_after_store a (Wasm_int.N_of_uint i32m (N_to_i32 gmp)) v' (serialise_num (VAL_int64 v0))); auto.
          cbn. rewrite Wasm_int.Int32.Z_mod_modulus_id; lia.
        }

        assert (HrelE' : @rel_env_LambdaANF_Wasm lenv e (map_util.M.set x (Vprim p) rho) s_before_IH f_before_IH fds). {
          have Hl := HlocInBound _ _ H3.
          apply nth_error_Some in Hl.
          apply notNone_Some in Hl. destruct Hl as [? Hlx].
          unfold rel_env_LambdaANF_Wasm.
          destruct HrelE as [Hfun1 [Hfun2 Hvar]].
          split.
          { (* funs1 *)
            intros. destruct (var_dec x x1).
            { (* x = x1 *)
              subst x1. rewrite M.gss in H0. inv H0.
              assert (~ subval_or_eq (Vfun rho' fds' f) (Vprim (primInt n))). { apply subval_or_eq_fun_not_prim. intros. congruence. }
              contradiction.
            }
            { (* x <> x1 *) rewrite M.gso in H0; eauto. }
          } split.
          { intros ? Hnfd. apply Hfun2 in Hnfd.
            destruct Hnfd as [i [Htrans Hval]].
            exists i. split. assumption.
            eapply val_relation_func_depends_on_funcs. eassumption.
            subst f_before_IH. assumption.
          }
          {
            intros. destruct (var_dec x x1).
            { (* x = x1 *)
              subst x1. exists (Vprim (primInt n)), (Val_ptr gmp).
              rewrite M.gss. split; auto. rewrite Hn; auto. split.
              subst f_before_IH. exists x'. cbn. split. assumption.
              unfold lookup_N.
              erewrite set_nth_nth_error_same; eauto.
              subst f_before_IH. assumption.
            }
            { (* x <> x1 *)
              assert (Hocc : occurs_free (Eprim_val x p e) x1) by now apply Free_Eprim_val.
              have H' := Hvar _ Hocc H1.
              destruct H' as [val' [wal' [Hrho [Hloc Hval]]]].
              exists val', wal'. split.
              rewrite M.gso; auto. split.
              destruct Hloc as [i [Hl1 Hl2]].
              unfold stored_in_locals. exists i. split; auto.
              subst f_before_IH.
              unfold lookup_N.
              rewrite set_nth_nth_error_other; auto.

              intro. assert (i = x') by lia. subst x'.
              have Hcontra := repr_var_inj _ _ _ _ HlenvInjective Hl1 H3.
              contradiction.

              apply nth_error_Some. congruence.

              subst f_before_IH.
              by eapply val_relation_depends_on_mem_smaller_than_gmp_and_funcs with (sr:=s')
                  (sr':=s_before_IH) (gmp' := (gmp + 8)%N); eauto; lia.
            }
          }
        }

        have IH := IHHev Hnodup' HfenvRho' HeRestr' Hunbound' _ fAny _ lh lenv HlenvInjective HenvsDisjoint state _ _ _ Hfds' HlocInBound' Hinv_before_IH HmemAvail_before_IH H4 HrelE'.
        destruct IH as [s_final [f_final [k'' [lh'' [Hred_IH [Hval [Hfinst [Hsfuncs' [HvalPres H_INV]]]]]]]]].

        assert (Hfinst': f_inst f_before_IH = f_inst fr) by now subst.

        exists s_final, f_final, k'', lh''.

        split.
        eapply rt_trans. apply reduce_trans_frame. apply reduce_trans_label.
        rewrite map_cat. apply app_trans. apply Hred. cbn.

        eapply rt_trans. apply reduce_trans_frame. apply reduce_trans_label.
        cbn.
        dostep_nary 0. apply r_global_get. eassumption.
        dostep_nary 2. eapply r_store_success; eauto.
        dostep_nary 0. apply r_global_get. apply HgmpPreserved.
        cbn. dostep_nary 1. eapply r_local_set' with (f':=f_before_IH). subst f_before_IH. reflexivity.
        apply /ssrnat.leP.
        apply HlocInBound in H3. lia. subst. reflexivity.
        cbn.
        dostep_nary 0. apply r_global_get. now rewrite Hfinst'.
        dostep_nary 2. constructor. apply rs_binop_success=>//.
        dostep_nary 1. apply r_global_set'. rewrite HgmpEq. subst f_before_IH. eassumption.
        apply rt_refl.
        (* apply IH *)
        apply Hred_IH.

        repeat split=>//; try congruence.
        intros wal val Hval'. subst f_before_IH.
        apply HvalPres.
        by eapply val_relation_depends_on_mem_smaller_than_gmp_and_funcs with
           (sr:=s') (gmp:=gmp) (gmp':=(gmp + 8)%N); eauto; try lia.
      } { (* Growing the memory failed *)
        (* hide instrs after return instr in block context, won't be executed *)
        remember (_ ++ e') as es_tail.
        have Hlh := lholed_tail _ lh (map AI_basic instr_grow_mem) (map AI_basic es_tail).

        destruct Hlh as [k' [lh' Heq']]. cbn in Heq'.
        have Hbad := HRedRet _ lh'.
        destruct Hbad as [sr' [k'' [lh'' [Hred [Hfuncs [HvalPreserved HoutofM]]]]]].

        exists sr', fr, k'', lh''. split.
        rewrite -Heq' in Hred. rewrite map_cat.
        apply reduce_trans_frame. apply Hred.

        split. right. assumption. split. reflexivity. split. congruence.
        split. auto.
        intro Hcontra. rewrite Hcontra in HoutofM. inv HoutofM. }
    }
  - (* Eprim *)
    { cbn. inv Hrepr_e.
      have I := Hinv. destruct I as [_[_[_[Hgmp_w[_[Hmut[Horglinmem [_[_[HfnsBound[_[_[_[_ [HfuncGrow _]]]]]]]]]]]]]]].
      destruct Horglinmem as [Horgmem1 [orgm [Horgmem2 [orgsize [<- [Horgmem4 Horgmem5]]]]]].

      destruct (i32_glob_implies_i32_val _ _ _ gmp_i32_glob Hgmp_w Hmut) as [g' Hgmp].
      destruct (i32_exists_N g') as [gmp [-> HgmpBound]].

      assert (HpageSize: (52 < page_size)%N). { unfold page_size. lia. }
      have Hgrowmem := memory_grow_reduce state sr _ 52%N mem _ _ _ HpageSize HmemAvail H14 Hinv Hgmp HgmpBound. clear HpageSize.
      destruct Hgrowmem as [[s' [Hred [Hsfuncs [HvalPreserved [Hinv' Henoughmem]]]]]
                            | HRedRet].
      { (* Successfully grow memory if necessary *)
        (* invariants after reducing grow *)
        have I := Hinv'. destruct I as [_ [_ [_ [_ [_ [_ [Hlinmem _]]]]]]].
        destruct Hlinmem as [Hmem1 [m [Hmem2 [size [<- [Hmem4 Hmem5]]]]]].

        assert (HenoughM : min_available_memory s' (f_inst fr) (52 + mem')). {
          have H' := Henoughmem _ Hmem2. destruct H' as [Hgmp' HenoughM].
          intros ?????.
          solve_eq m m0. solve_eq gmp gmp0.
          lia. } clear Henoughmem.

        assert (Hlocals : (forall y : var,
                              In y ys ->
                              find_def y fds = None ->
                              exists (v6 : term.val) (val : wasm_value),
                                rho ! y = Some v6 /\
                                  @stored_in_locals lenv y val fr /\
                                  repr_val_LambdaANF_Wasm v6 s' (f_inst fr) val)). {
          destruct HrelE as [_ Hvar]. intros.
          assert (Hocc: occurs_free (Eprim x f ys e) y) by (constructor; auto).
          apply Hvar in Hocc; auto. destruct Hocc as [val [wal [Hrho [Hloc Hval]]]].
          exists val, wal. by repeat split; auto.
        }

        assert (HrelE': @rel_env_LambdaANF_Wasm lenv (Eprim x f ys e) rho s' fr fds). {
          destruct HrelE as [Hfun1 [Hfun2 Hvar]]. split. assumption.
          split.
          intros.
          destruct (Hfun2 _ H2) as [idx [Htrans_idx Hrepr_idx]].
          exists idx. split. assumption.
          eapply val_relation_func_depends_on_funcs; eauto.
          intros.
          destruct (Hvar _ H2) as [val [wal [Hrho' [Hlocs Hval]]]]; auto.
          exists val. exists wal.
          split. assumption.
          split. assumption.
          now apply HvalPreserved.
        }

        have Hprim_red := HprimOpReduce lenv state s' fr fds f' x x' f
                            op_name s b n op ys e vs rho v prim_instrs _ H0 H9 H12 HlenvInjective HenvsDisjoint HfenvWf HlocInBound H7 HrelE' H13 Hinv' HenoughM H H1.

        clear HrelE'.

        destruct Hprim_red as [sr_before_IH [fr_before_IH [Hred' [Hinv_before_IH [Hfinst [Hsfs [HenoughM' [HrelE' [HvalsPreserved [wal [Hfr_eq Hrepr_val]]]]]]]]]]].


        rewrite Hfinst in HenoughM'.
        have Hrepr_e' := H8.

        assert (Hnodup' : NoDup (collect_local_variables e ++ collect_function_vars (Efun fds e))). {
          cbn in Hnodup. apply NoDup_cons_iff in Hnodup. now destruct Hnodup.
        }

        assert (HfenvRho' : forall (a : positive) (v0 : val),
                 (map_util.M.set x v rho) ! a = Some v0 ->
                 find_def a fds <> None -> v0 = Vfun (M.empty val) fds a). {
          intros ?? Hrho Hfd. apply HfenvRho; auto. rewrite M.gso in Hrho. assumption.
          intro. subst a. apply notNone_Some in Hfd. apply HfenvWf in Hfd. destruct Hfd.
          destruct HenvsDisjoint as [Hd1 Hd2]. apply Hd2 in H2.
          inv H7. unfold translate_var in H3. rewrite H2 in H3. inv H3.
        }
        assert (HeRestr' : expression_restricted cenv e) by now inv HeRestr.

        assert (Hunbound' : (forall x0 : var,
                   In x0 (collect_local_variables e) ->
                   (map_util.M.set x v rho) ! x0 = None)). {
          intros.
          apply NoDup_app_remove_r in Hnodup.
          cbn in Hnodup.
          apply NoDup_cons_iff in Hnodup.
          rewrite M.gso.
          apply Hunbound.
          unfold collect_local_variables.
          cbn.
          fold collect_local_variables.
          right. assumption.
          destruct Hnodup as [Hx _ ].
          unfold not. unfold not in Hx. intros Heq. subst x.
          apply Hx in H2. contradiction. }

        assert (HfVal' : forall (y : positive) (y' : funcidx) (v : term.val),
                  rho ! y = Some v ->
                  repr_funvar y y' ->
                  repr_val_LambdaANF_Wasm v sr_before_IH (f_inst fr_before_IH) (Val_funidx y')).
        { intros. destruct HrelE as [Hfun1 [Hfun2 _]].
          assert (Hfd: (exists i : funcidx, fenv ! y = Some i)). {
            inv H3. unfold translate_var in H4. destruct (fenv ! y) eqn:Hy; rewrite Hy in H4. eauto. discriminate. }
          apply HfenvWf in Hfd. apply notNone_Some in Hfd.

          have H' := HfenvRho _ _ H2 Hfd. subst v0.
          apply notNone_Some in Hfd. destruct Hfd as [[[f'' ys''] e''] ?H].

          assert (Hsubval: subval_or_eq (Vfun (M.empty _) fds y)
                             (Vfun (M.empty term.val) fds y)) by constructor.

          have H' := Hfun1 _ _ _ _ _ H2 Hsubval. destruct H' as [_ [_ H']].
          apply Hfun2 in H'.
          destruct H' as [i [HvarI Hval]].
          assert (i = y') by (eapply repr_funvar_det; eassumption). subst i.
          apply val_relation_func_depends_on_funcs with (s:=sr).
          now rewrite -Hsfs. now subst fr_before_IH.
        }

        assert (Hfds' : fds_translated_correctly fds sr_before_IH (f_inst fr_before_IH)). {
          intros ???? Hfd. subst fr_before_IH. cbn.
          apply Hfds in Hfd as [fidx [Ha Hv]]. exists fidx.
          split. assumption.
          eapply val_relation_func_depends_on_funcs; eauto. }

        assert (HlocInBound' : (forall (var : positive) (varIdx : localidx),
                                   repr_var (lenv:=lenv) nenv var varIdx -> N.to_nat varIdx < length (f_locs fr_before_IH))).
        {
          intros ?? Hvar. subst fr_before_IH.
          rewrite length_is_size size_set_nth maxn_nat_max -length_is_size.
          apply HlocInBound in Hvar, H7. lia.
        }


        have IH := IHHev Hnodup' HfenvRho' HeRestr' Hunbound' _ fAny _ lh lenv HlenvInjective HenvsDisjoint state _ _ _ Hfds' HlocInBound' Hinv_before_IH HenoughM' Hrepr_e' HrelE'.

        destruct IH as [s_final [f_final [k'' [lh'' [Hred_IH [Hval [Hfinst' [Hsfuncs' [HvalPres H_INV]]]]]]]]].

        exists s_final, f_final, k'', lh''.

        split.

        eapply rt_trans. apply reduce_trans_frame. apply reduce_trans_label.
        rewrite map_cat. apply app_trans. apply Hred.

        rewrite catA. rewrite map_cat. cbn.
        eapply rt_trans. apply reduce_trans_frame. apply reduce_trans_label.
        apply app_trans. cbn. apply Hred'.
        apply Hred_IH.
        subst fr_before_IH.
        replace (s_funcs s_final) with (s_funcs s') by now rewrite -Hsfuncs';rewrite -Hsfs.
        by repeat (split; auto).
        }
      { (* Growing the memory failed *)

        (* hide instrs after return instr in block context, won't be executed *)
        have Hlh := lholed_tail _ lh (map AI_basic grow_instr) (map AI_basic (prim_instrs ++ [:: BI_local_set x'] ++ e')).
        destruct Hlh as [k' [lh' Heq']].
        have Hbad := HRedRet _ lh'.
        destruct Hbad as [sr' [k'' [lh'' [Hred [Hfuncs [HvalPreserved HoutofM]]]]]].
        exists sr', fr, k'', lh''. split.
        rewrite -Heq' in Hred. rewrite map_cat.
        apply reduce_trans_frame. apply Hred.

        split. right. assumption. split. reflexivity. split. congruence.
        split.
        now apply HvalPreserved.
        intro Hcontra. rewrite Hcontra in HoutofM. inv HoutofM. }
    }
  - (* Ehalt *)
    cbn. inv Hrepr_e. destruct HrelE as [_ [_ Hvar]].
    assert (HfNone: find_def x fds = None). {
      apply HfenvWf_None with (f:=x) in HfenvWf. rewrite HfenvWf.
      inv H1. unfold translate_var in H0. destruct (lenv ! x) eqn:Hx; rewrite Hx in H0=>//. injection H0 as ->.
      now apply HenvsDisjoint in Hx. }
     destruct (Hvar x) as [v6 [wal [Henv [Hloc Hrepr]]]]; auto.
    rewrite Henv in H. inv H.

    have I := Hinv. destruct I as [INVres [_ [HMzero [Hgmp_r [_ [Hmuti32 [Hlinmem [HgmpInMem [_ [Hfuncs [Hinstglobs [_ [_ Hgmp_mult_two]]]]]]]]]]]]].
    destruct (i32_glob_implies_i32_val _ _ _ gmp_i32_glob Hgmp_r Hmuti32) as [gmp Hgmp].

    edestruct i32_exists_N as [x'' [Hx'' ?]]. erewrite Hx'' in Hgmp. subst.

    destruct Hlinmem as [Hmem1 [m [Hmem2 [size [Hmem3 [Hmem4 Hmem5]]]]]]. subst.
    assert (Hmemlengthbound: (Z.of_N (mem_length m) < Int32.modulus)%Z). {
      apply mem_length_upper_bound in Hmem5. cbn in Hmem5.
      simpl_modulus. simpl_modulus_in H. cbn. lia. }
    apply mem_length_upper_bound in Hmem5. cbn in Hmem5.
    have HinM := HgmpInMem _ _ Hmem2 Hgmp.

    unfold INV_glob_result_writable, global_var_w in INVres.
    destruct (INVres (VAL_int32 (wasm_value_to_i32 wal))) as [s' Hs].
    destruct Hloc as [ilocal [H4 Hilocal]].
    assert (x' = ilocal). { eapply repr_var_det; eassumption. } subst ilocal.

    exists s', fr, k, lh.  cbn. split.

    (* execute wasm instructions *)
    apply reduce_trans_frame. apply reduce_trans_label.
    dostep_nary 0. eapply r_local_get. eassumption.
    dostep_nary' 1. apply r_global_set'. eassumption. apply rt_refl.

    split.
    left. exists (wasm_value_to_i32 wal). exists wal.
    repeat split. eapply update_global_get_same. eassumption.
    eapply val_relation_depends_on_mem_smaller_than_gmp_and_funcs; last apply Hrepr; eauto.
    eapply update_global_preserves_funcs; try eassumption.
    erewrite <- update_global_preserves_memory; try eassumption.
    simpl_modulus. cbn. lia.
    eapply update_global_get_other; try eassumption.
    unfold glob_mem_ptr, glob_result. lia.
    simpl_modulus. cbn. lia. lia.
    eapply update_global_get_other; try eassumption. now intro. split; first auto.
    split. eapply update_global_preserves_funcs; eassumption.
    split. { intros.
      assert (smem s' (f_inst fr) = Some m). {
        now rewrite -(update_global_preserves_memory _ _ _ _ _ Hs). }
      assert (sglob_val s' (f_inst fr) glob_mem_ptr = Some (VAL_num (VAL_int32 (N_to_i32 x'')))). {
      erewrite update_global_get_other; try eassumption. reflexivity. now intro.
    }
    eapply val_relation_depends_on_mem_smaller_than_gmp_and_funcs with (sr:=sr); eauto.
      eapply update_global_preserves_funcs. eassumption.
      simpl_modulus. cbn. lia.
      simpl_modulus. cbn. lia.
      lia.
    }
    intro H_INV.
    eapply update_global_preserves_INV with (i:=glob_result) (num:=(VAL_int32 (wasm_value_to_i32 wal))); eauto=>//.
    cbn; tauto.
    Unshelve. all: try assumption; try apply ""%bs.
Qed.

End MAIN.
