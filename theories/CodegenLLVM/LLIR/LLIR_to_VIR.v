(** * LLIR -> VIR (Vellvm [LLVMAst]) — the thinnest of the three LLIR backends.

    LLIR (issue #121) is the common subset of LLVM IR that Clight and Wasm can
    also express.  Because VIR *is* LLVM IR, this lowering is near-identity: every
    straight-line [instr] becomes one Vellvm instruction of the same shape, and
    each [term] re-embeds LLIR's control-flow *tree* into VIR's basic-block CFG
    (LLVM has a CFG; LLIR has a tree, so a [Tswitch] opens fresh blocks).  See
    [LOWERINGS.md] for the per-op table this file implements.

    Value/ABI helpers ([val_ty], [ptr_ty], [gep_field], the tag/untag shifts,
    [call_args]) are the ones fixed by [LambdaANF_to_LLVM.v]; they are reused here
    verbatim so the two VIR emitters share one ABI.

    ---------------------------------------------------------------------------
    Note on [Module LLIR] below.  The canonical LLIR AST is the sibling file
    [LLIR.v].  In the integrated dune / coq_makefile build this file opens with

        From LLIR Require Import LLIR.

    and the module below is deleted.  Under the MCP-only verification workflow
    ([rocq_compile_file] compiles each file ephemerally, installs no local [.vo]
    and forbids [Load]), a cross-file [Require] of the sibling cannot resolve, so
    the LLIR AST is mirrored inline, *verbatim* from [LLIR.v], inside [Module
    LLIR] and then [Import]ed — exactly the workaround [LambdaANF_to_LLIR.v]
    uses.  [Import LLIR] brings the identical datatype names. *)

From Vellvm Require Import Syntax.LLVMAst.
From Stdlib Require Import BinNums BinPos BinNat BinInt List String.
Import ListNotations.
Open Scope string_scope.

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

(** ** Runtime ABI types (shared with [LambdaANF_to_LLVM.v]). *)

(** A CertiRocq [value] / LLIR [word] is a machine word. *)
Definition val_ty : typ := TYPE_I 64%positive.
(** Heap objects are addressed as [i64*]. *)
Definition ptr_ty : typ := TYPE_Pointer (Some (TYPE_I 64%positive)).
(** Every emitted function takes the [thread_info] pointer as arg 0. *)
Definition tinfo_ty : typ := TYPE_Pointer None.

(** The [thread_info*] parameter every emitted function receives. *)
Definition etinfo : exp typ := EXP_Ident (ID_Local (Name "tinfo")).

(** ** Literals.  [int_syntax = Number.signed_int]; [Z.to_num_int] is the
       canonical [Z -> int_syntax] injection. *)
Definition lit_z (w : LLIR.word) : exp typ := EXP_Integer (Z.to_num_int w).
Definition lit_n (n : N) : exp typ := EXP_Integer (Z.to_num_int (Z.of_N n)).

(** ** SSA reg -> VIR local id.  LLIR [reg = positive]; serialise as
       [Raw (Zpos r)] both as a definition site ([IId]) and as an operand
       ([EXP_Ident (ID_Local ...)]). *)
Definition reg_id (r : LLIR.reg) : instr_id := IId (Raw (Zpos r)).
Definition reg_exp (r : LLIR.reg) : exp typ := EXP_Ident (ID_Local (Raw (Zpos r))).

(** [lower_operand] — an operand is a value already in hand. *)
Definition lower_operand (o : LLIR.operand) : exp typ :=
  match o with
  | LLIR.Oreg r => reg_exp r
  | LLIR.Oimm w => lit_z w
  end.

(** [lower_binop op a b] — the arithmetic [binop]s map 1:1 to a Vellvm [ibinop]
    ([OP_IBinop]); the four comparisons ([Beq/Bne/Blt_s/Blt_u]) have no [ibinop]
    and instead map to [OP_ICmp] (their result is an i1, as [is_block] in
    [LambdaANF_to_LLVM.v]). *)
Definition lower_binop (op : LLIR.binop) (a b : exp typ) : exp typ :=
  match op with
  | LLIR.Badd  => OP_IBinop (LLVMAst.Add false false) val_ty a b
  | LLIR.Bsub  => OP_IBinop (Sub false false) val_ty a b
  | LLIR.Bmul  => OP_IBinop (Mul false false) val_ty a b
  | LLIR.Bshl  => OP_IBinop (Shl false false) val_ty a b
  | LLIR.Bashr => OP_IBinop (AShr false) val_ty a b
  | LLIR.Blshr => OP_IBinop (LShr false) val_ty a b
  | LLIR.Band  => OP_IBinop And val_ty a b
  | LLIR.Bor   => OP_IBinop (Or false) val_ty a b
  | LLIR.Bxor  => OP_IBinop Xor val_ty a b
  | LLIR.Beq   => OP_ICmp false Eq  val_ty a b
  | LLIR.Bne   => OP_ICmp false Ne  val_ty a b
  | LLIR.Blt_s => OP_ICmp false Slt val_ty a b
  | LLIR.Blt_u => OP_ICmp false Ult val_ty a b
  end.

(** Address of word [n] of a boxed base operand: the LLVM [getelementptr] whose
    [inttoptr] internalises the word->address reinterpretation (I2).  Mirrors
    [gep_field] of [LambdaANF_to_LLVM.v]. *)
Definition gep_field (base : exp typ) (n : N) : exp typ :=
  OP_GetElementPtr val_ty
    (ptr_ty, OP_Conversion Inttoptr val_ty base ptr_ty)
    [(val_ty, lit_n n)].

(** Call argument list: [%tinfo] first, then the value args verbatim. *)
Definition lower_args (args : list LLIR.operand)
  : list (texp typ * list param_attr) :=
  ((tinfo_ty, etinfo), @nil param_attr)
  :: map (fun o => ((val_ty, lower_operand o), @nil param_attr)) args.

(** ** [lower_instr] — one straight-line LLIR instruction to one VIR
    instruction, tagged with its result [instr_id].  Register-defining instrs
    get [IId (Raw (Zpos r))]; [Istore] is void, [IVoid 0].

    Per [LOWERINGS.md]: [Iconst]->[INSTR_Op] literal, [Ibinop]->[OP_IBinop]/
    [OP_ICmp], [Iload]->[INSTR_Load]+GEP, [Istore]->[INSTR_Store]+GEP,
    [Igep]->[INSTR_Op] (bare GEP), [Iptrtoint]/[Iinttoptr]->[OP_Conversion],
    [Icall]->[INSTR_Call] on a named global, [Icall_indirect]->[INSTR_Call] on
    the operand.  [Ialloc] is NOT a single-instruction op — its portable form is
    the multi-block GC safepoint (see [LOWERINGS.md] and the [Econstr]-boxed CFG
    of [LambdaANF_to_LLVM.v]); to keep [lower_instr] total and per-instruction it
    is emitted here as a thin call to the runtime allocator, with the real
    safepoint expansion left to the block-level emitter. *)
Definition lower_instr (i : LLIR.instr) : instr_id * LLVMAst.instr typ :=
  match i with
  | LLIR.Iconst r w =>
      (reg_id r, INSTR_Op (lit_z w))
  | LLIR.Ibinop r op a b =>
      (reg_id r, INSTR_Op (lower_binop op (lower_operand a) (lower_operand b)))
  | LLIR.Iload r b n =>
      (reg_id r, INSTR_Load val_ty (ptr_ty, gep_field (lower_operand b) n) [])
  | LLIR.Istore b n v =>
      (IVoid 0%Z,
       INSTR_Store (val_ty, lower_operand v) (ptr_ty, gep_field (lower_operand b) n) [])
  | LLIR.Igep r b n =>
      (reg_id r, INSTR_Op (gep_field (lower_operand b) n))
  | LLIR.Iptrtoint r p =>
      (reg_id r, INSTR_Op (OP_Conversion Ptrtoint ptr_ty (lower_operand p) val_ty))
  | LLIR.Iinttoptr r p =>
      (reg_id r, INSTR_Op (OP_Conversion Inttoptr val_ty (lower_operand p) ptr_ty))
  | LLIR.Icall r f args =>
      (reg_id r,
       INSTR_Call (val_ty, EXP_Ident (ID_Global (Name f))) (lower_args args) [] [])
  | LLIR.Icall_indirect r fp args =>
      (reg_id r,
       INSTR_Call (val_ty, lower_operand fp) (lower_args args) [] [])
  | LLIR.Ialloc r n =>
      (* Thin placeholder (see the doc comment): a call to the runtime
         allocator; the multi-block GC-safepoint expansion is the backend's. *)
      (reg_id r,
       INSTR_Call (val_ty, EXP_Ident (ID_Global (Name "certirocq_alloc")))
         [((val_ty, lit_n n), @nil param_attr)] [] [])
  end.

(** Prepend straight-line [extra] code to the entry block of [blks].  A [Tseq]
    before a branching/terminal construct conses its instruction onto the
    continuation's entry rather than opening a new block. *)
Definition prepend_code (extra : code typ) (blks : list (block typ))
  : list (block typ) :=
  match blks with
  | b :: rest =>
      mk_block (blk_id b) (blk_phis b) ((extra ++ blk_code b)%list)
        (blk_term b) (blk_comments b) :: rest
  | [] => []
  end.

(** ** [lower_term] — LLIR's control-flow tree to a VIR basic-block CFG.

    [lower_term_aux t fresh] returns [(blocks, fresh')] with [blocks] non-empty
    and its head the entry block; [fresh]/[fresh'] thread a monotone fresh
    block-id counter (as [Anon (Zpos _)]).  [Tret] is one [TERM_Ret] block;
    [Tseq] prepends its instruction onto the continuation's entry; [Tswitch]
    opens a fresh [TERM_Switch] block over one block-chain per arm plus the
    default's chain (the tree->CFG re-embedding). *)
Fixpoint lower_term_aux (t : LLIR.term) (fresh : positive) {struct t}
  : list (block typ) * positive :=
  match t with
  | LLIR.Tret v =>
      ( [ mk_block (Anon (Zpos fresh)) []
            []
            (IVoid 0%Z, TERM_Ret (val_ty, lower_operand v), []) None ],
        Pos.succ fresh )
  | LLIR.Tseq i k =>
      let '(blks, f') := lower_term_aux k fresh in
      let '(id, ins) := lower_instr i in
      ( prepend_code [(id, ins, [])] blks, f' )
  | LLIR.Tswitch s arms default =>
      let '(dblks, f1) := lower_term_aux default fresh in
      let default_lbl :=
        match dblks with b :: _ => blk_id b | [] => Anon (Zpos f1) end in
      let fix arm_loop (arms : list (LLIR.word * LLIR.term)) (fr : positive)
            {struct arms}
            : list (block typ) * list (tint_literal * block_id) * positive :=
        match arms with
        | [] => ([], [], fr)
        | (w, at_) :: rest =>
            let '(ablks, fr1) := lower_term_aux at_ fr in
            let lbl :=
              match ablks with b :: _ => blk_id b | [] => Anon (Zpos fr) end in
            let '(rblks, redges, fr2) := arm_loop rest fr1 in
            ( (ablks ++ rblks)%list,
              (TInt_Literal 64 (Z.to_num_int w), lbl) :: redges,
              fr2 )
        end in
      let '(arm_blks, edges, f2) := arm_loop arms f1 in
      let sw_lbl := Anon (Zpos f2) in
      let sw_blk :=
        mk_block sw_lbl [] []
          (IVoid 0%Z, TERM_Switch (val_ty, lower_operand s) default_lbl edges, [])
          None in
      ( (sw_blk :: arm_blks ++ dblks)%list, Pos.succ f2 )
  end.

Definition lower_term (t : LLIR.term) : list (block typ) :=
  fst (lower_term_aux t 1%positive).

(** ** [lower_function] — a whole VIR [define].

    [define i64 @name(ptr %tinfo, i64 %p0, ...) { entry: ... ; rest }].  The CFG
    body form [block typ * list (block typ)] (entry + rest) is what [ShowAST]
    renders.  Mirrors [mk_fun] of [LambdaANF_to_LLVM.v]. *)
Definition lower_function (f : LLIR.function)
  : definition typ (block typ * list (block typ)) :=
  let blks := lower_term (LLIR.fn_body f) in
  let entry :=
    match blks with
    | b :: _ => b
    | [] => mk_block (Name "entry") [] [] (IVoid 0%Z, TERM_Unreachable, []) None
    end in
  let rest := match blks with _ :: r => r | [] => [] end in
  let params := LLIR.fn_params f in
  let nargs := S (List.length params) in
  let decl :=
    @mk_declaration typ
      (Name (LLIR.fn_name f))
      (TYPE_Function val_ty (tinfo_ty :: map (fun _ => val_ty) params) false)
      ([], List.repeat (@nil param_attr) nargs)
      []
      [] in
  @mk_definition typ (block typ * list (block typ))
    decl
    (Name "tinfo" :: map (fun v => Raw (Zpos v)) params)
    (entry, rest).

(** ** [lower_program] — one top-level [define] per LLIR function. *)
Definition lower_program (p : LLIR.program)
  : list (toplevel_entity typ (block typ * list (block typ))) :=
  map (fun f => TLE_Definition (lower_function f)) (LLIR.prog_funs p).

(** ** Smoke tests — pin the lowered shape of a few instructions/terms. *)

Example lower_iconst_shape :
  lower_instr (LLIR.Iconst 3%positive 7%Z)
  = (IId (Raw (Zpos 3)), INSTR_Op (EXP_Integer (Z.to_num_int 7))).
Proof. reflexivity. Qed.

Example lower_ibinop_add_shape :
  lower_instr (LLIR.Ibinop 1%positive LLIR.Badd (LLIR.Oreg 2%positive) (LLIR.Oimm 5%Z))
  = (IId (Raw (Zpos 1)),
     INSTR_Op (OP_IBinop (LLVMAst.Add false false) val_ty
                (EXP_Ident (ID_Local (Raw (Zpos 2))))
                (EXP_Integer (Z.to_num_int 5)))).
Proof. reflexivity. Qed.

Example lower_bne_is_icmp :
  lower_instr (LLIR.Ibinop 4%positive LLIR.Bne (LLIR.Oreg 1%positive) (LLIR.Oimm 0%Z))
  = (IId (Raw (Zpos 4)),
     INSTR_Op (OP_ICmp false Ne val_ty
                (EXP_Ident (ID_Local (Raw (Zpos 1))))
                (EXP_Integer (Z.to_num_int 0)))).
Proof. reflexivity. Qed.

Example lower_tret_shape :
  lower_term (LLIR.Tret (LLIR.Oreg 1%positive))
  = [ mk_block (Anon (Zpos 1)) [] []
        (IVoid 0%Z, TERM_Ret (val_ty, EXP_Ident (ID_Local (Raw (Zpos 1)))), []) None ].
Proof. reflexivity. Qed.

(** [Tseq (Iload r y n) (Tret r)] lowers to a single block whose entry code is
    the load and whose terminator returns [r]. *)
Compute lower_term
  (LLIR.Tseq (LLIR.Iload 5%positive (LLIR.Oreg 1%positive) 2%N)
             (LLIR.Tret (LLIR.Oreg 5%positive))).
