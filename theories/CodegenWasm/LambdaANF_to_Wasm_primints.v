From Stdlib Require Import ZArith BinNat List Uint63.
From Wasm Require Import datatypes.
From CertiRocq Require Import Common.compM Common.Pipeline_utils.
From MetaRocq Require Import Common.Kernames Utils.bytestring Utils.MRString.

Import ListNotations SigTNotations Wasm_int.


Notation "'primInt' x" := (AstCommon.primInt ; x) (at level 0).

(* Define convenience wrappers as notations to allow easy unfolding during proofs *)
Notation uint63 := Uint63.int.
Notation Z_to_i64 z := (Int64.repr z).
Notation Z_to_VAL_i64 z := (VAL_int64 (Int64.repr z)).
Notation nat_to_VAL_i32 n := (VAL_int32 (Wasm_int.Int32.repr (BinInt.Z.of_nat n))).
Notation N_to_VAL_i32 n := (VAL_int32 (Wasm_int.Int32.repr (BinInt.Z.of_N n))).

Local Coercion Z_to_i64_co z := Z_to_i64 z.
Local Coercion Z_to_i64val_co z := Z_to_VAL_i64 z.

Section TRANSLATION.

Variables glob_mem_ptr glob_tmp1 glob_tmp2 glob_tmp3 glob_tmp4 loop_counter : globalidx.

Definition maxuint31 := 2147483647%Z.
Definition maxuint63 := 9223372036854775807%Z.


(* Ordinals of constructors *)
Definition true_ord  := 1%N.
Definition false_ord := 0%N.

Definition Eq_ord    := 0%N.
Definition Lt_ord    := 1%N.
Definition Gt_ord    := 2%N.

Definition C0_ord    := 0%N.
Definition C1_ord    := 1%N.

Definition pair_ord  := 0%N.


(* Path of the PrimInt63 module in the kernel: Corelib.Numbers.Cyclic.Int63.PrimInt63 *)
Definition primInt63ModPath : Kernames.modpath :=
  Kernames.MPfile [ "PrimInt63"%bs ; "Int63"%bs ; "Cyclic"%bs ; "Numbers"%bs ; "Corelib"%bs ].

(* Supported operators defined as data type to avoid pattern matching on kernel name (bytestrings) *)
Inductive primop :=
| PrimInt63add
| PrimInt63sub
| PrimInt63mul
| PrimInt63div
| PrimInt63mod
| PrimInt63lsl
| PrimInt63lsr
| PrimInt63land
| PrimInt63lor
| PrimInt63lxor
| PrimInt63eqb
| PrimInt63ltb
| PrimInt63leb
| PrimInt63compare
| PrimInt63addc
| PrimInt63addcarryc
| PrimInt63subc
| PrimInt63subcarryc
| PrimInt63mulc
| PrimInt63head0
| PrimInt63tail0
| PrimInt63diveucl
| PrimInt63diveucl_21
| PrimInt63addmuldiv.

Definition primop_map : KernameMap.t primop :=
  KernameMap.add (primInt63ModPath, "add") PrimInt63add
    (KernameMap.add (primInt63ModPath, "sub") PrimInt63sub
    (KernameMap.add (primInt63ModPath, "mul") PrimInt63mul
    (KernameMap.add (primInt63ModPath, "div") PrimInt63div
    (KernameMap.add (primInt63ModPath, "mod") PrimInt63mod
    (KernameMap.add (primInt63ModPath, "lsl") PrimInt63lsl
    (KernameMap.add (primInt63ModPath, "lsr") PrimInt63lsr
    (KernameMap.add (primInt63ModPath, "land") PrimInt63land
    (KernameMap.add (primInt63ModPath, "lor") PrimInt63lor
    (KernameMap.add (primInt63ModPath, "lxor") PrimInt63lxor
    (KernameMap.add (primInt63ModPath, "eqb") PrimInt63eqb
    (KernameMap.add (primInt63ModPath, "ltb") PrimInt63ltb
    (KernameMap.add (primInt63ModPath, "leb") PrimInt63leb
    (KernameMap.add (primInt63ModPath, "compare") PrimInt63compare
    (KernameMap.add (primInt63ModPath, "addc") PrimInt63addc
    (KernameMap.add (primInt63ModPath, "addcarryc") PrimInt63addcarryc
    (KernameMap.add (primInt63ModPath, "subc") PrimInt63subc
    (KernameMap.add (primInt63ModPath, "subcarryc") PrimInt63subcarryc
    (KernameMap.add (primInt63ModPath, "mulc") PrimInt63mulc
    (KernameMap.add (primInt63ModPath, "head0") PrimInt63head0
    (KernameMap.add (primInt63ModPath, "tail0") PrimInt63tail0
    (KernameMap.add (primInt63ModPath, "diveucl") PrimInt63diveucl
    (KernameMap.add (primInt63ModPath, "diveucl_21") PrimInt63diveucl_21
    (KernameMap.add (primInt63ModPath, "addmuldiv") PrimInt63addmuldiv
    (KernameMap.empty primop)))))))))))))))))))))))).

Definition load_local_i64 (i : localidx) : list basic_instruction :=
  [ BI_local_get i ; BI_load T_i64 None {| memarg_offset:=0%N; memarg_align:=2%N |} ].

Definition increment_glob_mem_ptr i :=
  [ BI_global_get glob_mem_ptr
  ; BI_const_num (N_to_VAL_i32 i)
  ; BI_binop T_i32 (Binop_i BOI_add)
  ; BI_global_set glob_mem_ptr
  ].

Definition bitmask_instrs := [ BI_const_num maxuint63 ; BI_binop T_i64 (Binop_i BOI_and) ].

Definition apply_binop_and_store_i64 (op : binop_i) (x y : localidx) (apply_bitmask : bool) : list basic_instruction :=
  BI_global_get glob_mem_ptr ::                   (* Address to store the result of the operation *)
  load_local_i64 x ++                               (* Load the arguments onto the stack *)
  load_local_i64 y ++
  [ BI_binop T_i64 (Binop_i op) ] ++
  (if apply_bitmask then bitmask_instrs else []) ++ (* apply bitmask to zero MSB if necessary *)
  [ BI_store T_i64 None {| memarg_offset:=0%N; memarg_align:=2%N |} (* Store the result *)
  ; BI_global_get glob_mem_ptr                    (* Put the result address on the stack *)
  ] ++
  increment_glob_mem_ptr 8%N.

(* Assume argument is stored in global gidx *)
Definition make_carry (ord : N) (gidx : globalidx) : list basic_instruction:=
  [ BI_global_get glob_mem_ptr
  ; BI_global_get gidx
  ; BI_store T_i64 None {| memarg_offset:=0%N; memarg_align:=2%N |}
  ; BI_global_get glob_mem_ptr
  ; BI_const_num (N_to_VAL_i32 ord)
  ; BI_store T_i32 None {| memarg_offset:=8%N; memarg_align:=2%N |}
  ; BI_global_get glob_mem_ptr
  ; BI_global_get glob_mem_ptr
  ; BI_store T_i32 None {| memarg_offset:=12%N; memarg_align:=2%N |}
  ; BI_global_get glob_mem_ptr
  ; BI_const_num (nat_to_VAL_i32 8)
  ; BI_binop T_i32 (Binop_i BOI_add)
  ] ++ increment_glob_mem_ptr 16%N.

Definition apply_add_carry_operation (x y : localidx) (addone : bool) : list basic_instruction :=
    load_local_i64 x ++ load_local_i64 y ++
    [ BI_binop T_i64 (Binop_i BOI_add) ] ++
    (if addone then
       [ BI_const_num 1%Z ; BI_binop T_i64 (Binop_i BOI_add) ]
     else []) ++
    bitmask_instrs ++
    [BI_global_set glob_tmp1 ;BI_global_get glob_tmp1 ] ++
    load_local_i64 x ++
    [ BI_relop T_i64 (Relop_i ((if addone then ROI_le else ROI_lt) SX_U))
    ; BI_if (BT_valtype (Some (T_num T_i32))) (make_carry C1_ord glob_tmp1) (make_carry C0_ord glob_tmp1)
    ].

Definition apply_sub_carry_operation (x y : localidx) (subone : bool) : list basic_instruction :=
    load_local_i64 x ++ load_local_i64 y ++
    [ BI_binop T_i64 (Binop_i BOI_sub) ] ++
    (if subone then
       [ BI_const_num 1%Z ; BI_binop T_i64 (Binop_i BOI_sub) ]
     else []) ++
    bitmask_instrs ++
    [ BI_global_set glob_tmp1 ] ++
    load_local_i64 y ++
    load_local_i64 x ++
    [ BI_relop T_i64 (Relop_i ((if subone then ROI_lt else ROI_le) SX_U))
    ; BI_if (BT_valtype (Some (T_num T_i32))) (make_carry C0_ord glob_tmp1) (make_carry C1_ord glob_tmp1)
    ].

(* Assume 1st element is stored in global gidx1, 2nd element in global gidx2 *)
Definition make_product (gidx1 gidx2 : N) : list basic_instruction :=
  [ BI_global_get glob_mem_ptr
  ; BI_global_get gidx1
  ; BI_store T_i64 None {| memarg_offset:=0%N; memarg_align:=2%N |}
  ; BI_global_get glob_mem_ptr
  ; BI_global_get gidx2
  ; BI_store T_i64 None {| memarg_offset:=8%N; memarg_align:=2%N |}
  ; BI_global_get glob_mem_ptr
  ; BI_const_num (N_to_VAL_i32 pair_ord)
  ; BI_store T_i32 None {| memarg_offset:=16%N; memarg_align:=2%N |}
  ; BI_global_get glob_mem_ptr
  ; BI_global_get glob_mem_ptr
  ; BI_store T_i32 None {| memarg_offset:=20%N; memarg_align:=2%N |}
  ; BI_global_get glob_mem_ptr
  ; BI_global_get glob_mem_ptr
  ; BI_const_num (nat_to_VAL_i32 8)
  ; BI_binop T_i32 (Binop_i BOI_add)
  ; BI_store T_i32 None {| memarg_offset:=24%N; memarg_align:=2%N |}
  ; BI_global_get glob_mem_ptr
  ; BI_const_num (nat_to_VAL_i32 16)
  ; BI_binop T_i32 (Binop_i BOI_add)
  ] ++ increment_glob_mem_ptr 28%N.

Definition make_boolean_valued_comparison x y relop : list basic_instruction :=
  load_local_i64 x ++            (* Load the arguments onto the stack *)
  load_local_i64 y ++
  [ BI_relop T_i64 (Relop_i relop)
  ; BI_if (BT_valtype (Some (T_num T_i32)))
      [ BI_const_num (N_to_VAL_i32 (2 * true_ord + 1)) ]
      [ BI_const_num (N_to_VAL_i32 (2 * false_ord + 1)) ]
  ].

Definition compare_instrs x y : list basic_instruction :=
  [ BI_local_get x
  ; BI_load T_i64 None {| memarg_offset:=0%N; memarg_align:=2%N |}
  ; BI_local_get y
  ; BI_load T_i64 None {| memarg_offset:=0%N; memarg_align:=2%N |}
  ; BI_relop T_i64 (Relop_i (ROI_lt SX_U))
  ; BI_if (BT_valtype (Some (T_num T_i32)))
      [ BI_const_num (N_to_VAL_i32 (2 * Lt_ord + 1)) ]
      (load_local_i64 x ++
       load_local_i64 y ++
       [ BI_relop T_i64 (Relop_i ROI_eq)
       ; BI_if (BT_valtype (Some (T_num T_i32)))
           [ BI_const_num (N_to_VAL_i32 (2 * Eq_ord + 1)) ]
           [ BI_const_num (N_to_VAL_i32 (2 * Gt_ord + 1)) ]
       ])
  ].

Definition div_instrs (x y : localidx) : list basic_instruction :=
  BI_global_get glob_mem_ptr ::
    load_local_i64 y ++
    [ BI_testop T_i64 TO_eqz
    ; BI_if (BT_valtype (Some (T_num T_i64)))
        [ BI_const_num 0%Z ]
        (load_local_i64 x ++ load_local_i64 y ++ [ BI_binop T_i64 (Binop_i (BOI_div SX_U)) ])
    ; BI_store T_i64 None {| memarg_offset:=0%N; memarg_align:=2%N |}
    ; BI_global_get glob_mem_ptr
    ] ++ increment_glob_mem_ptr 8%N.


Definition mod_instrs (x y : localidx) : list basic_instruction :=
  BI_global_get glob_mem_ptr ::
    load_local_i64 y ++
    [ BI_testop T_i64 TO_eqz
    ; BI_if (BT_valtype (Some (T_num T_i64)))
        (load_local_i64 x)
        (load_local_i64 x ++ load_local_i64 y ++ [ BI_binop T_i64 (Binop_i (BOI_rem SX_U)) ])
    ; BI_store T_i64 None {| memarg_offset:=0%N; memarg_align:=2%N |}
    ; BI_global_get glob_mem_ptr
    ] ++ increment_glob_mem_ptr 8%N.

Definition shift_instrs (x y : localidx) shiftop (mask : bool) : list basic_instruction :=
  BI_global_get glob_mem_ptr ::
    load_local_i64 y ++
    [ BI_const_num 63%Z
    ; BI_relop T_i64 (Relop_i (ROI_lt SX_U))
    ; BI_if (BT_valtype (Some (T_num T_i64)))
        (load_local_i64 x ++
         load_local_i64 y ++
         BI_binop T_i64 (Binop_i shiftop) ::
         (if mask then bitmask_instrs else []))
        [ BI_const_num 0%Z ]
    ; BI_store T_i64 None {| memarg_offset:=0%N; memarg_align:=2%N |}
    ; BI_global_get glob_mem_ptr
    ] ++ increment_glob_mem_ptr 8%N.

Definition low32 := [ BI_const_num 4294967295%Z ; BI_binop T_i64 (Binop_i BOI_and) ].
Definition high32 := [ BI_const_num 32%Z ; BI_binop T_i64 (Binop_i (BOI_shr SX_U)) ].

Definition mulc_instrs (x y : localidx) : list basic_instruction :=
  (* Compute cross products *)
  (* glob_tmp1 = xlow * ylow *)
  load_local_i64 x ++ low32 ++
  load_local_i64 y ++ low32 ++
  [ BI_binop T_i64 (Binop_i BOI_mul) ; BI_global_set glob_tmp1 ] ++
  (* glob_tmp2 = xhigh * ylow *)
  load_local_i64 x ++ high32 ++
  load_local_i64 y ++ low32 ++
  [ BI_binop T_i64 (Binop_i BOI_mul) ; BI_global_set glob_tmp2 ] ++
  (* glob_tmp3 = xlow * yhigh *)
  load_local_i64 x ++ low32 ++
  load_local_i64 y ++ high32 ++
  [ BI_binop T_i64 (Binop_i BOI_mul) ; BI_global_set glob_tmp3 ] ++
  (* glob_tmp4 = xhigh * yhigh *)
  load_local_i64 x ++ high32 ++
  load_local_i64 y ++ high32 ++
  [ BI_binop T_i64 (Binop_i BOI_mul) ; BI_global_set glob_tmp4 ] ++
  (* Add the cross products together *)
  [ BI_global_get glob_tmp1 ] ++ high32 ++ (* (xlow * ylow) >> 32 *)
  [ BI_global_get glob_tmp2 ] ++ low32 ++ (* (xhigh * ylow) & 0xFFFFFFFF *)
  [ BI_binop T_i64 (Binop_i BOI_add)
  ; BI_global_get glob_tmp3
  ; BI_binop T_i64 (Binop_i BOI_add)
  (* We don't need xlow * yhigh, so we can store the intermediate cross in glob_tmp3  *)
  ; BI_global_set glob_tmp3
  ] ++
  [ BI_global_get glob_tmp2 ] ++ high32 ++
  [ BI_global_get glob_tmp3 ] ++ high32 ++
  [ BI_binop T_i64 (Binop_i BOI_add) ] ++
  [ BI_global_get glob_tmp4
  ; BI_binop T_i64 (Binop_i BOI_add)
  ; BI_global_set glob_tmp2 (* glob_tmp2 = upper 64 bits of 128 bit product *)
  ] ++
  [ BI_global_get glob_tmp3 ; BI_const_num 32%Z ; BI_binop T_i64 (Binop_i BOI_shl) ] ++
  [ BI_global_get glob_tmp1 ] ++ low32 ++
  [ BI_binop T_i64 (Binop_i BOI_or)
  ; BI_global_set glob_tmp1 (* glob_tmp1 = lower 64 bits of 128 bit product *)
  ] ++
  (* Now adjust such that glob_tmp2 = upper _63_ bits of _126_ bit product *)
  [ BI_global_get glob_tmp2
  ; BI_const_num 1%Z
  ; BI_binop T_i64 (Binop_i BOI_shl)
  ; BI_global_get glob_tmp1
  ; BI_const_num 63%Z
  ; BI_binop T_i64 (Binop_i (BOI_shr SX_U))
  ; BI_binop T_i64 (Binop_i BOI_add)
  ; BI_global_set glob_tmp2
  ] ++
  (* And glob_tmp1 = lower _63_ bits of _126_ bit product *)
  [ BI_global_get glob_tmp1
  ; BI_const_num maxuint63
  ; BI_binop T_i64 (Binop_i BOI_and)
  ; BI_global_set glob_tmp1
  ] ++ make_product glob_tmp2 glob_tmp1. (* (upper, lower) *)


Definition diveucl_instrs (x y : localidx) : list basic_instruction :=
  [ BI_local_get x
  ; BI_load T_i64 None {| memarg_offset:=0%N; memarg_align:=2%N |}
  ; BI_testop T_i64 TO_eqz
  ; BI_if (BT_valtype None)
      [ BI_const_num (VAL_int64 (Z_to_i64 0))
      ; BI_global_set glob_tmp1
      ; BI_const_num 0%Z
      ; BI_global_set glob_tmp2
      ]
      [ BI_local_get y
      ; BI_load T_i64 None {| memarg_offset:=0%N; memarg_align:=2%N |}
      ; BI_testop T_i64 TO_eqz
      ; BI_if (BT_valtype None)
          [ BI_const_num (VAL_int64 (Z_to_i64 0))
          ; BI_global_set glob_tmp1
          ; BI_local_get x
          ; BI_load T_i64 None {| memarg_offset:=0%N; memarg_align:=2%N |}
          ; BI_global_set glob_tmp2
          ]
          (load_local_i64 x ++
             load_local_i64 y ++
             [ BI_binop T_i64 (Binop_i (BOI_div SX_U)) ; BI_global_set glob_tmp1 ] ++
             load_local_i64 x ++
             load_local_i64 y ++
             [ BI_binop T_i64 (Binop_i (BOI_rem SX_U)) ; BI_global_set glob_tmp2 ])
      ]
  ] ++ make_product glob_tmp1 glob_tmp2.

Definition translate_primitive_binary_op op (x y : localidx) : error (list basic_instruction) :=
  match op with
  | PrimInt63add       => Ret (apply_binop_and_store_i64 BOI_add x y true)
  | PrimInt63sub       => Ret (apply_binop_and_store_i64 BOI_sub x y true)
  | PrimInt63mul       => Ret (apply_binop_and_store_i64 BOI_mul x y true)
  | PrimInt63div       => Ret (div_instrs x y)
  | PrimInt63mod       => Ret (mod_instrs x y)
  | PrimInt63lsl       => Ret (shift_instrs x y BOI_shl true)
  | PrimInt63lsr       => Ret (shift_instrs x y (BOI_shr SX_U) false)
  | PrimInt63land      => Ret (apply_binop_and_store_i64 BOI_and x y false)
  | PrimInt63lor       => Ret (apply_binop_and_store_i64 BOI_or x y false)
  | PrimInt63lxor      => Ret (apply_binop_and_store_i64 BOI_xor x y false)
  | PrimInt63eqb       => Ret (make_boolean_valued_comparison x y ROI_eq)
  | PrimInt63ltb       => Ret (make_boolean_valued_comparison x y (ROI_lt SX_U))
  | PrimInt63leb       => Ret (make_boolean_valued_comparison x y (ROI_le SX_U))
  | PrimInt63compare   => Ret (compare_instrs x y)
  | PrimInt63addc      => Ret (apply_add_carry_operation x y false)
  | PrimInt63addcarryc => Ret (apply_add_carry_operation x y true)
  | PrimInt63subc      => Ret (apply_sub_carry_operation x y false)
  | PrimInt63subcarryc => Ret (apply_sub_carry_operation x y true)
  | PrimInt63mulc      => Ret (mulc_instrs x y)
  | PrimInt63diveucl   => Ret (diveucl_instrs x y)
  | _ => Err "Unknown primitive binary operator"
  end.

(* head0 x computes the leading number of zeros in x
   OBS: need to subtract 1 since we're dealing with 63-bit integers *)
Definition head0_instrs (x : localidx) : list basic_instruction :=
  BI_global_get glob_mem_ptr ::
    load_local_i64 x ++
    [ BI_unop T_i64 (Unop_i UOI_clz)
    ; BI_const_num 1%Z
    ; BI_binop T_i64 (Binop_i BOI_sub)
    ; BI_store T_i64 None {| memarg_offset:=0%N; memarg_align:=2%N |}
    ; BI_global_get glob_mem_ptr
    ] ++ increment_glob_mem_ptr 8%N.

(* tail0 x computes the trailing number of zeros in x
   OBS: if x is 0, then result is 63 (can't just use wasm ctz op) ) *)
Definition tail0_instrs (x : localidx) : list basic_instruction :=
  BI_global_get glob_mem_ptr ::
    load_local_i64 x ++
    [ BI_testop T_i64 TO_eqz
    ; BI_if (BT_valtype (Some (T_num T_i64)))
        [ BI_const_num 63%Z ]
        (load_local_i64 x ++ [ BI_unop T_i64 (Unop_i UOI_ctz) ])
    ; BI_store T_i64 None {| memarg_offset:=0%N; memarg_align:=2%N |}
    ; BI_global_get glob_mem_ptr
    ] ++ increment_glob_mem_ptr 8%N.

Definition translate_primitive_unary_op op (x : localidx) : error (list basic_instruction) :=
  match op with
  | PrimInt63head0 => Ret (head0_instrs x)
  | PrimInt63tail0 => Ret (tail0_instrs x)
  | _ => Err "Unknown primitive unary operator"
  end.

Definition diveucl_21_loop_body glob_xh glob_xl glob_y glob_q :=
  [ BI_global_get glob_xl
  ; BI_const_num 1%Z
  ; BI_binop T_i64 (Binop_i BOI_shl)
  ; BI_global_set glob_xl
  (* xl := xl << 1 *)

  ; BI_global_get glob_xh
  ; BI_const_num 1%Z
  ; BI_binop T_i64 (Binop_i BOI_shl)
  ; BI_global_get glob_xl
  ; BI_const_num 63%Z
  ; BI_binop T_i64 (Binop_i (BOI_shr SX_U))
  ; BI_binop T_i64 (Binop_i BOI_or)
  ; BI_global_set glob_xh
  (* xh := (xh << 1) || (xl >> 63) *)

  ; BI_global_get glob_q
  ; BI_const_num 1%Z
  ; BI_binop T_i64 (Binop_i BOI_shl)
  ; BI_global_set glob_q
  (* q := q << 1 *)

  ; BI_global_get glob_xh
  ; BI_global_get glob_y
  ; BI_relop T_i64 (Relop_i (ROI_ge SX_U))
  (* if xh >= y: *)
  ; BI_if (BT_valtype None)
      ([ BI_global_get glob_q
       ; BI_const_num 1%Z
       ; BI_binop T_i64 (Binop_i BOI_or)
       ; BI_global_set glob_q
       (* q := q || 1 *)
       ] ++
       [ BI_global_get glob_xh
       ; BI_global_get glob_y
       ; BI_binop T_i64 (Binop_i BOI_sub)
       ; BI_global_set glob_xh
       (* xh := xh - y *)
       ])
      []
  ].

Definition diveucl_21_loop glob_xh glob_xl glob_y glob_q iterations :=
  [ BI_global_get loop_counter
  ; BI_const_num (VAL_int32 (Int32.repr iterations))
  ; BI_relop T_i32 (Relop_i (ROI_lt SX_U))
  ; BI_if (BT_valtype None)
      ((diveucl_21_loop_body glob_xh glob_xl glob_y glob_q) ++
       [ BI_global_get loop_counter
       ; BI_const_num (VAL_int32 (Int32.repr 1))
       ; BI_binop T_i32 (Binop_i BOI_add)
       ; BI_global_set loop_counter
       ; BI_br 1%N
       ])
      []
  ].

Definition diveucl_21_instrs (xh xl y : localidx) : list basic_instruction :=
  load_local_i64 y ++
    load_local_i64 xh ++
    [ BI_relop T_i64 (Relop_i (ROI_le SX_U))
    ; BI_if (BT_valtype (Some (T_num T_i32)))
        (* if y <= xh, then the result is always 0 *)
        ([ BI_const_num 0%Z ; BI_global_set glob_tmp1] ++ make_product glob_tmp1 glob_tmp1)
        ( (* glob_tmp1 = xh *)
          load_local_i64 xh ++ [ BI_global_set glob_tmp1 ] ++
          (* glob_tmp2 = xl *)
          load_local_i64 xl ++ [ BI_global_set glob_tmp2 ] ++
          (* glob_tmp3 = y *)
          load_local_i64 y  ++ [ BI_global_set glob_tmp3 ] ++
          [ (* glob_tmp4 = q (the quotient, initialised to 0) *)
          BI_const_num (VAL_int64 (Int64.repr 0%Z))
          ; BI_global_set glob_tmp4
          (* Initialise the loop counter to 0 *)
          ; BI_const_num (VAL_int32 (Int32.repr 0%Z))
          ; BI_global_set loop_counter

          (* execute 62 iterations of the loop *)
          ; BI_loop (BT_valtype None) (diveucl_21_loop glob_tmp1 glob_tmp2 glob_tmp3 glob_tmp4 63%Z)
          ] ++ (make_product glob_tmp4 glob_tmp1))
    ].


Definition addmuldiv_instrs p x y :=
  BI_global_get glob_mem_ptr ::
    load_local_i64 p ++
    [ BI_const_num 63%Z
    ; BI_relop T_i64 (Relop_i (ROI_gt SX_U))
    ; BI_if (BT_valtype (Some (T_num T_i64)))
        [ BI_const_num 0%Z ]
        (* Compute x << p on the stack *)
        (load_local_i64 x ++
           load_local_i64 p ++
           [ BI_binop T_i64 (Binop_i BOI_shl) ] ++
           (* Put y on the stack *)
           load_local_i64 y ++
           (* Compute 63 - p on the stack *)
           [ BI_const_num 63%Z ] ++
           load_local_i64 p ++
           [ BI_binop T_i64 (Binop_i BOI_sub)
           (* Compute y >> (63 - p) on the stack *)
           ; BI_binop T_i64 (Binop_i (BOI_shr SX_U))
           (* Finally, compute (x << p) | (y >> (63 - p)) on the stack *)
           ; BI_binop T_i64 (Binop_i BOI_or)
           ; BI_const_num maxuint63
           ; BI_binop T_i64 (Binop_i BOI_and)
           ])
    ; BI_store T_i64 None {| memarg_offset:=0%N; memarg_align:=2%N |}
    ; BI_global_get glob_mem_ptr
    ] ++ increment_glob_mem_ptr 8%N.

Definition translate_primitive_ternary_op op (x y z : localidx) : error (list basic_instruction) :=
  match op with
  | PrimInt63diveucl_21 => Ret (diveucl_21_instrs x y z)
  | PrimInt63addmuldiv  => Ret (addmuldiv_instrs x y z)
  | _ => Err "Unknown primitive ternary operator"
  end.

End TRANSLATION.
