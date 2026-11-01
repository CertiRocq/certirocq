(** * LLIR -> Wasm (WasmCert-Coq [basic_instruction]) — the THIRD and final of
    the three LLIR backends, completing the LLIR-as-common-subset demonstration.

    LLIR (issue #121) is the common subset of LLVM IR that CompCert-Clight and
    WebAssembly can also express.  With [LLIR_to_VIR.v] (near-identity) and
    [LLIR_to_Clight.v] (statement/expression split) already in place, this file
    is the *structure-adding* lowering: WasmCert-Coq's [basic_instruction] stream
    is a stack machine, so every LLIR operation that names an operand must
    bracket it with [BI_local_get]/[BI_local_set] or [BI_const_num], and the
    higher-level LLIR constructs synthesise structure that Wasm lacks natively:

      - [Tswitch] has NO Wasm counterpart (no [switch], and we do not use
        [br_table] here) — it becomes a nested [BI_if] cascade, one compare per
        arm, mirroring the C-Rocq backend's [create_case_nested_if_chain].
      - [Ialloc] has NO collector — Wasm has no GC — so it is a plain monotone
        bump of the [glob_mem_ptr] global (get / add / set), with none of the
        VIR/Clight root-spill + [garbage_collect] safepoint machinery.
      - [Icall]/[Icall_indirect] dispatch through the module's function table 0
        via [BI_call_indirect]; the result is handed back through the
        [glob_result] global (all Wasm functions are typed [... -> ()]).
      - [Iptrtoint]/[Iinttoptr] are REJECTED: linear memory is *indexed*, not
        punned, so there is no [inttoptr].  The portable LLIR fragment never
        emits them (I2); we map them to [BI_unreachable] (a trap) with a
        prominent comment, keeping [lower_instr] total.

    See [LOWERINGS.md] (the "Wasm" column) for the per-op table this file
    implements.

    -------------------------------------------------------------------------
    The one non-portable width fact (LOWERINGS §"Shared preliminaries").  LLIR's
    [word] is an i64 (I3), and VIR/Clight honour that with 8-byte cells; the Wasm
    backend represents the *same* tagged ABI in **4-byte i32 cells**
    ([BI_store]/[BI_load T_i32], memory index arithmetic in i32).  So a field's
    word offset [n] scales by **8** on VIR/Clight but by **4** on Wasm, and the
    header/tag word is skipped by folding it into a leading [+1] (offset
    [(n+1)*4]).  That scale constant is the Wasm lowering's choice, not a change
    of semantics — the identical constant appears in the C-Rocq Wasm backend
    ([LambdaANF_to_Wasm.v], the [Eproj] case: [((N.to_nat n) + 1) * 4]).
    Immediates and register values therefore materialise as [VAL_int32], and
    [word_to_value] truncates the i64 word to the i32 cell exactly as
    [nat_to_value]/[Z_to_value] do in the C-Rocq backend.

    -------------------------------------------------------------------------
    SSA register -> Wasm local (the stack-machine mapping).  A Wasm value lives
    on the operand stack, not in a named SSA temp, so a def-use pair becomes a
    [BI_local_set] into a local followed by [BI_local_get] out of it.  Each LLIR
    SSA register [r : positive] maps to the Wasm local whose index is [N.pos r]
    ([reg_local] below).  The integrated pass allocates the function's *locals
    vector* — one [T_i32] local per SSA register plus any temporaries — as part
    of the [module_func] record ([modfunc_locals]); this per-instruction lowering
    assumes that vector exists and only reads/writes it by index.

    -------------------------------------------------------------------------
    Note on [Module LLIR] below.  The canonical LLIR AST is the sibling file
    [LLIR.v].  In the integrated dune / coq_makefile build this file opens with
    [From LLIR Require Import LLIR] and the module is deleted.  Under the MCP-only
    verification workflow ([rocq_compile_file] compiles each file ephemerally,
    installs no local [.vo] and forbids cross-file [Require] of an uninstalled
    sibling), the LLIR AST is mirrored inline, *verbatim* from [LLIR.v], inside
    [Module LLIR] and then [Import]ed — the same workaround [LLIR_to_VIR.v] and
    [LLIR_to_Clight.v] use. *)

(** The WasmCert-Coq imports, mirrored verbatim from the C-Rocq Wasm backend
    [CertiRocq/CodegenWasm/LambdaANF_to_Wasm.v] (its [From Wasm Require Import]
    line).  These put [basic_instruction] and its constructors
    ([BI_const_num], [BI_binop], [BI_load], [BI_store], [BI_if],
    [BI_call_indirect], [BI_return], [BI_local_get]/[BI_local_set],
    [BI_global_get]/[BI_global_set], [BI_relop], [BI_testop]), the numeric
    vocabulary ([value_num]/[VAL_int32]/[VAL_int64], [number_type]/[T_i32],
    [binop_i]/[BOI_add]…, [relop_i]/[ROI_eq]…, [testop]/[TO_eqz], [sx]),
    [block_type]/[BT_valtype], the [memarg] record, and [Wasm_int] in scope. *)
From Wasm Require Import datatypes operations.

From Stdlib Require Import BinNums BinPos BinNat BinInt List String.
Import ListNotations.
(* No [Open Scope string_scope]: the LLIR AST uses [string] for [funsym] but this
   file constructs no string literals, and leaving [list_scope] on top keeps [++]
   bound to list append throughout the stack-machine instruction lists. *)

(** ** LLIR AST — verbatim mirror of the canonical [LLIR.v]; see that file for
       the full design commentary.  In the integrated build, replace this whole
       module with [From LLIR Require Import LLIR]. *)
Module LLIR.

  Definition reg    : Type := positive.
  Definition word   : Type := Z.
  Definition funsym : Type := string.

  Inductive operand : Type :=
  | Oreg : reg  -> operand
  | Oimm : word -> operand.

  Inductive binop : Type :=
  | Badd | Bsub | Bmul
  | Bshl | Bashr | Blshr
  | Band | Bor  | Bxor
  | Beq  | Bne
  | Blt_s | Blt_u.

  Inductive instr : Type :=
  | Iconst : reg -> word -> instr
  | Ibinop : reg -> binop -> operand -> operand -> instr
  | Ialloc : reg -> N -> instr
  | Iload  : reg -> operand -> N -> instr
  | Istore : operand -> N -> operand -> instr
  | Igep   : reg -> operand -> N -> instr
  | Icall  : reg -> funsym -> list operand -> instr
  | Icall_indirect : reg -> operand -> list operand -> instr
  | Iptrtoint : reg -> operand -> instr        (* LLVM-ONLY *)
  | Iinttoptr : reg -> operand -> instr.       (* LLVM-ONLY *)

  Inductive term : Type :=
  | Tseq    : instr -> term -> term
  | Tswitch : operand -> list (word * term) -> term -> term
  | Tret    : operand -> term.

  Record function : Type := mk_function {
    fn_name   : funsym;
    fn_params : list reg;
    fn_body   : term
  }.

  Record program : Type := mk_program {
    prog_funs  : list function;
    prog_entry : funsym
  }.

End LLIR.

Import LLIR.

(** ** Runtime globals (mirrored from [LambdaANF_to_Wasm.v] L44-47).

    Wasm has no GC and no [thread_info] pointer: the heap frontier and the
    function result live in module globals, not on the stack.  [glob_mem_ptr] is
    the bump pointer [Ialloc] advances; [glob_result] is the answer slot [Tret]
    stores into before [BI_return] (mirroring Clight's [tinfo->args[1]]). *)
Definition glob_mem_ptr : globalidx := 0%N.
Definition glob_result  : globalidx := 2%N.

(** ** Literals, locals, operands. *)

(** A machine word -> a Wasm i32 constant value.  The tagged ABI is realised in
    i32 cells on Wasm (the one non-portable width fact), so the i64 [word]
    materialises as a [VAL_int32] — [Wasm_int.Int32.repr] truncates, exactly as
    the C-Rocq backend's [Z_to_value]/[nat_to_value] do. *)
Definition word_to_value (w : LLIR.word) : value_num :=
  VAL_int32 (Wasm_int.Int32.repr w).

(** A byte count (a field offset or an allocation size) -> an i32 constant. *)
Definition bytes_value (z : Z) : value_num :=
  VAL_int32 (Wasm_int.Int32.repr z).

(** The Wasm local index of an SSA register: the register's [positive], viewed
    as the [localidx = N] index into the function's locals vector. *)
Definition reg_local (r : LLIR.reg) : localidx := N.pos r.

(** The shared memarg for every field load/store: zero static offset (the
    displacement is computed as an explicit i32 add so it is uniform with the
    address-only [Igep] case), natural 4-byte alignment ([memarg_align] is the
    log2, so [2] = align 4).  Verbatim from [LambdaANF_to_Wasm.v] L369/L182. *)
Definition field_memarg : memarg := {| memarg_offset := 0%N; memarg_align := 2%N |}.

(** [lower_operand] — an operand is a value already in hand, and on a stack
    machine "having a value in hand" means "push it onto the operand stack".  An
    SSA register maps to a [BI_local_get] of its local ([reg = positive =
    localidx], variable-preserving); an immediate to a [BI_const_num]. *)
Definition lower_operand (o : LLIR.operand) : list basic_instruction :=
  match o with
  | LLIR.Oreg r => [ BI_local_get (reg_local r) ]
  | LLIR.Oimm w => [ BI_const_num (word_to_value w) ]
  end.

(** [lower_binop op] — the Wasm operator that consumes the two operands already
    pushed on the stack and pushes the result.  Arithmetic and bitwise ops are
    [BI_binop T_i32 (Binop_i …)]; the two shifts differ only in the signedness
    tag of [BOI_shr] ([SX_S] arithmetic vs [SX_U] logical); the comparisons are
    [BI_relop T_i32 (Relop_i …)] and already yield the 0/1 word Wasm's relops
    produce.  Every LLIR [binop] (I3) is thus one native Wasm instruction — no
    structure synthesis, the cleanest column (LOWERINGS §"Ibinop"). *)
Definition lower_binop (op : LLIR.binop) : basic_instruction :=
  match op with
  | LLIR.Badd  => BI_binop T_i32 (Binop_i BOI_add)
  | LLIR.Bsub  => BI_binop T_i32 (Binop_i BOI_sub)
  | LLIR.Bmul  => BI_binop T_i32 (Binop_i BOI_mul)
  | LLIR.Bshl  => BI_binop T_i32 (Binop_i BOI_shl)
  | LLIR.Bashr => BI_binop T_i32 (Binop_i (BOI_shr SX_S))
  | LLIR.Blshr => BI_binop T_i32 (Binop_i (BOI_shr SX_U))
  | LLIR.Band  => BI_binop T_i32 (Binop_i BOI_and)
  | LLIR.Bor   => BI_binop T_i32 (Binop_i BOI_or)
  | LLIR.Bxor  => BI_binop T_i32 (Binop_i BOI_xor)
  | LLIR.Beq   => BI_relop T_i32 (Relop_i ROI_eq)
  | LLIR.Bne   => BI_relop T_i32 (Relop_i ROI_ne)
  | LLIR.Blt_s => BI_relop T_i32 (Relop_i (ROI_lt SX_S))
  | LLIR.Blt_u => BI_relop T_i32 (Relop_i (ROI_lt SX_U))
  end.

(** The [Is_block v = (v & 1) == 0] tag test as a stack fragment: given the
    scrutinee already pushed, [BI_binop And 1] then [BI_testop eqz] leaves 1 iff
    [v] is boxed.  This is the boxed/unboxed discriminator the C-Rocq backend
    emits before splitting a case into its boxed and unboxed [BI_if] chains
    ([LambdaANF_to_Wasm.v] L352-355).  At the LLIR level the front pass has
    already resolved each [Tswitch] arm's key into a concrete word, so [lower_
    term] emits a single unified compare cascade rather than two header/ordinal
    chains; this fragment is exposed so the [BI_binop And]/[BI_testop eqz]
    construct the boxed/unboxed dispatch is built from is on record. *)
Definition is_block_test : list basic_instruction :=
  [ BI_const_num (bytes_value 1)
  ; BI_binop T_i32 (Binop_i BOI_and)
  ; BI_testop T_i32 TO_eqz ].

(** Function-symbol -> function-table index.  Every callable is a table entry
    (the module's [ME_active] element segment lists them all), so a direct call
    pushes the callee's *index* and dispatches through [BI_call_indirect].  A
    real pass threads a name environment [funsym -> funcidx]; placeholder
    identity here keeps [lower_instr] a pure per-instruction function, exactly as
    [LLIR_to_Clight.v]'s [fun_ident] and [LLIR_to_VIR.v] do. *)
Definition fun_idx (f : LLIR.funsym) : funcidx := 0%N.

(** Retrieve a call's result from [glob_result] into the callee's result local.
    All Wasm functions are typed [… -> ()]; the answer comes back through the
    global (LOWERINGS §"Icall" / §"Tret"). *)
Definition load_call_result (r : LLIR.reg) : list basic_instruction :=
  [ BI_global_get glob_result ; BI_local_set (reg_local r) ].

(** ** [lower_instr] — one straight-line LLIR instruction to a Wasm instruction
    *list* (a stack machine has no single-instruction analogue of a
    register-defining op: each is "push operands; operate; [BI_local_set]").

    Per [LOWERINGS.md] (Wasm column):
      - [Iconst]/[Ibinop] -> push operand(s), the const/[BI_binop], then set r.
      - [Iload] -> push base; add byte offset [(n+1)*4]; [BI_load T_i32]; set r.
      - [Istore] -> push base; add offset; push value; [BI_store T_i32].
      - [Igep] -> push base; add offset; set r — [Iload] without the [BI_load]
        (an address is just an i32 index, so [Igep] is the cheapest op on Wasm).
      - [Icall]/[Icall_indirect] -> push args; push callee index / [fp];
        [BI_call_indirect] through table 0 with arity as the type index; then
        pull the result out of [glob_result].
      - [Ialloc] -> a collector-free bump of [glob_mem_ptr] (get/add/set).
      - [Iptrtoint]/[Iinttoptr] -> **REJECTED** (see below). *)
Definition lower_instr (i : LLIR.instr) : list basic_instruction :=
  match i with
  | LLIR.Iconst r w =>
      [ BI_const_num (word_to_value w) ; BI_local_set (reg_local r) ]
  | LLIR.Ibinop r op a b =>
      lower_operand a ++ lower_operand b
                      ++ [ lower_binop op ; BI_local_set (reg_local r) ]
  | LLIR.Iload r b n =>
      (* r := mem[b + n words].  Word offset n rescales by 4 (i32 cells) and the
         header/tag word is skipped by the leading +1: byte offset (n+1)*4. *)
      lower_operand b
        ++ [ BI_const_num (bytes_value (Z.of_N ((n + 1) * 4)))
           ; BI_binop T_i32 (Binop_i BOI_add)
           ; BI_load T_i32 None field_memarg
           ; BI_local_set (reg_local r) ]
  | LLIR.Istore b n v =>
      (* mem[b + n words] := v.  Wasm's BI_store pops [address; value], so the
         address (base + (n+1)*4) is pushed first, then the value. *)
      lower_operand b
        ++ [ BI_const_num (bytes_value (Z.of_N ((n + 1) * 4)))
           ; BI_binop T_i32 (Binop_i BOI_add) ]
        ++ lower_operand v
        ++ [ BI_store T_i32 None field_memarg ]
  | LLIR.Igep r b n =>
      (* r := &b[n] — the field address, no load.  Pure i32 arithmetic. *)
      lower_operand b
        ++ [ BI_const_num (bytes_value (Z.of_N ((n + 1) * 4)))
           ; BI_binop T_i32 (Binop_i BOI_add)
           ; BI_local_set (reg_local r) ]
  | LLIR.Icall r f args =>
      (* Direct call: all callables are table entries, so we push the callee's
         table index as a const and dispatch through call_indirect on table 0,
         the callee arity being the type index.  The integrated pass additionally
         guards on [glob_out_of_mem] after the call ([LambdaANF_to_Wasm.v]
         L377-380); omitted here for a per-instruction shape. *)
      List.concat (List.map lower_operand args)
        ++ [ BI_const_num (bytes_value (Z.of_N (fun_idx f)))
           ; BI_call_indirect 0%N (N.of_nat (List.length args)) ]
        ++ load_call_result r
  | LLIR.Icall_indirect r fp args =>
      (* Indirect call through code-pointer word [fp] (a table index). *)
      List.concat (List.map lower_operand args)
        ++ lower_operand fp
        ++ [ BI_call_indirect 0%N (N.of_nat (List.length args)) ]
        ++ load_call_result r
  | LLIR.Ialloc r n =>
      (* r := alloc n words.  NO GC — Wasm has no collector.  A plain monotone
         bump of the [glob_mem_ptr] frontier: return the current frontier as the
         allocation base, then advance it by n*4 bytes (i32 cells).  None of the
         VIR/Clight root-spill / [garbage_collect] safepoint / [tinfo] reload
         machinery exists here (LOWERINGS §"Ialloc" — the maximally-divergent
         op).  A real emitter additionally guards with a grow-or-abort
         ([grow_memory_if_necessary]); that guard is orthogonal plumbing. *)
      [ BI_global_get glob_mem_ptr
      ; BI_local_set (reg_local r)
      ; BI_global_get glob_mem_ptr
      ; BI_const_num (bytes_value (Z.of_N (n * 4)))
      ; BI_binop T_i32 (Binop_i BOI_add)
      ; BI_global_set glob_mem_ptr ]
  | LLIR.Iptrtoint r p =>
      (* LLVM-ONLY (I2 escape hatch) — REJECTED on Wasm: linear memory is
         *indexed*, not punned; there is no [inttoptr]/[ptrtoint].  A well-formed
         *portable* LLIR program never contains these (the word->address
         reinterpretation lives inside [Iload]/[Istore]/[Igep], I2), so a real
         Wasm lowering would [reject] any program using them.  To keep this
         per-instruction function total we emit a trap ([BI_unreachable]) rather
         than a silent no-op, so a program that illegitimately reached this case
         aborts at run time instead of miscompiling. *)
      [ BI_unreachable ]
  | LLIR.Iinttoptr r p =>
      [ BI_unreachable ]   (* LLVM-ONLY; REJECTED on Wasm — see [Iptrtoint] above *)
  end.

(** ** [lower_term] — LLIR's structured control-flow tree to a Wasm instruction
    list.

    [Tret] -> push the value, store it to [glob_result], [BI_return].
    [Tseq]  -> instruction-list concatenation ([++]) — the trivial sequencing
               Wasm's flat body affords (LOWERINGS §"Tseq").
    [Tswitch] -> a **nested [BI_if] cascade**: Wasm has no [switch]/[br_table]
               here, so each arm becomes one equality compare + [BI_if], with the
               default falling out at the end of the chain.  This mirrors the
               C-Rocq backend's [create_case_nested_if_chain]
               ([LambdaANF_to_Wasm.v] L212-230): [<scrutinee>; <key const>;
               [BI_relop eq]; [BI_if <arm> <rest>]].  The inner [fix] recurses on
               [arms] (structurally decreasing) and calls [lower_term] on each
               arm term and on [default] — all structural subterms of the
               [Tswitch], so the definition is well-founded (same pattern as
               [LLIR_to_Clight.v]'s [arms_ls]).  This is the op that forces the
               most structure-adding on Wasm: O(#arms) compares in place of one
               native dispatch. *)
Fixpoint lower_term (t : LLIR.term) {struct t} : list basic_instruction :=
  match t with
  | LLIR.Tret v =>
      lower_operand v ++ [ BI_global_set glob_result ; BI_return ]
  | LLIR.Tseq i k =>
      lower_instr i ++ lower_term k
  | LLIR.Tswitch s arms default =>
      let fix chain (arms : list (LLIR.word * LLIR.term)) {struct arms}
            : list basic_instruction :=
          match arms with
          | [] => lower_term default
          | (k, arm) :: rest =>
              lower_operand s
                ++ [ BI_const_num (word_to_value k)
                   ; BI_relop T_i32 (Relop_i ROI_eq)
                   ; BI_if (BT_valtype None)
                       (lower_term arm)
                       (chain rest) ]
          end in
      chain arms
  end.

(** ** [lower_function] — a whole Wasm function body instruction list.

    A faithful skeleton: the SSA body lowers to one [list basic_instruction]; a
    real WasmCert [module_func] additionally needs the type index
    ([modfunc_type]), the locals vector ([modfunc_locals]: one [T_i32] per SSA
    register + temporaries — the "locals vector" the stack-machine mapping
    assumes), and the module-level function table + element segment that
    [BI_call_indirect] dispatches through.  Those are orthogonal plumbing; the
    interesting content — the instruction/term walk — is [lower_term] of the
    body. *)
Definition lower_function_body (f : LLIR.function) : list basic_instruction :=
  lower_term (LLIR.fn_body f).

(** ** Smoke tests — pin the lowered Wasm shape of a few instructions/terms. *)

(** [Iconst]: push the i32 const, set the result local. *)
Example lower_iconst_shape :
  lower_instr (LLIR.Iconst 3%positive 7%Z)
  = [ BI_const_num (VAL_int32 (Wasm_int.Int32.repr 7)) ; BI_local_set 3%N ].
Proof. reflexivity. Qed.

(** [Ibinop add]: get local 2, push const 5, [BI_binop add], set local 1 — the
    stack-machine bracketing of [r1 := r2 + 5]. *)
Example lower_ibinop_add_shape :
  lower_instr (LLIR.Ibinop 1%positive LLIR.Badd (LLIR.Oreg 2%positive) (LLIR.Oimm 5%Z))
  = [ BI_local_get 2%N
    ; BI_const_num (VAL_int32 (Wasm_int.Int32.repr 5))
    ; BI_binop T_i32 (Binop_i BOI_add)
    ; BI_local_set 1%N ].
Proof. reflexivity. Qed.

(** [Iload r5 (Oreg 1) 2]: the ×4 rescale + header skip — field 2 of base r1 is
    byte offset (2+1)*4 = 12 — then [BI_load T_i32], set r5. *)
Example lower_iload_offset_x4 :
  lower_instr (LLIR.Iload 5%positive (LLIR.Oreg 1%positive) 2%N)
  = [ BI_local_get 1%N
    ; BI_const_num (VAL_int32 (Wasm_int.Int32.repr 12))
    ; BI_binop T_i32 (Binop_i BOI_add)
    ; BI_load T_i32 None {| memarg_offset := 0%N; memarg_align := 2%N |}
    ; BI_local_set 5%N ].
Proof. reflexivity. Qed.

(** [Ialloc r4 3]: collector-free bump — take the frontier as the base, advance
    [glob_mem_ptr] by 3*4 = 12 bytes.  No GC safepoint anywhere in the list. *)
Example lower_ialloc_is_bump :
  lower_instr (LLIR.Ialloc 4%positive 3%N)
  = [ BI_global_get glob_mem_ptr
    ; BI_local_set 4%N
    ; BI_global_get glob_mem_ptr
    ; BI_const_num (VAL_int32 (Wasm_int.Int32.repr 12))
    ; BI_binop T_i32 (Binop_i BOI_add)
    ; BI_global_set glob_mem_ptr ].
Proof. reflexivity. Qed.

(** The rejected [Iptrtoint] traps (portable LLIR never emits it). *)
Example lower_iptrtoint_traps :
  lower_instr (LLIR.Iptrtoint 6%positive (LLIR.Oreg 1%positive)) = [ BI_unreachable ].
Proof. reflexivity. Qed.

(** [Tret]: push the value, hand it back through [glob_result], [BI_return]. *)
Example lower_tret_shape :
  lower_term (LLIR.Tret (LLIR.Oreg 1%positive))
  = [ BI_local_get 1%N ; BI_global_set glob_result ; BI_return ].
Proof. reflexivity. Qed.

(** [Tswitch] over one matching arm (key 0 -> return imm 9) plus a default
    (return the scrutinee r1) lowers to the nested-[BI_if] cascade: compare r1
    to 0, and on match run the arm, else the default term. *)
Example lower_tswitch_nested_if :
  lower_term (LLIR.Tswitch (LLIR.Oreg 1%positive)
                [(0%Z, LLIR.Tret (LLIR.Oimm 9%Z))]
                (LLIR.Tret (LLIR.Oreg 1%positive)))
  = [ BI_local_get 1%N
    ; BI_const_num (VAL_int32 (Wasm_int.Int32.repr 0))
    ; BI_relop T_i32 (Relop_i ROI_eq)
    ; BI_if (BT_valtype None)
        [ BI_const_num (VAL_int32 (Wasm_int.Int32.repr 9))
        ; BI_global_set glob_result ; BI_return ]
        [ BI_local_get 1%N ; BI_global_set glob_result ; BI_return ] ].
Proof. reflexivity. Qed.

(** [Tseq (Iload r5 (Oreg 1) 2) (Tret r5)] -> the load list concatenated before
    the return list. *)
Compute lower_term
  (LLIR.Tseq (LLIR.Iload 5%positive (LLIR.Oreg 1%positive) 2%N)
             (LLIR.Tret (LLIR.Oreg 5%positive))).
