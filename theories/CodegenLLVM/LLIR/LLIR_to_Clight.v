(** * LLIR -> Clight (CompCert [Clight.statement]) — the second of the three
    LLIR backends, and the heaviest.

    LLIR (issue #121) is the common subset of LLVM IR that CompCert-Clight and
    Wasm can also express.  This lowering is the *statement/expression split*
    made concrete: LLIR's flat instruction stream (every [instr] both computes a
    value and lives in a linear sequence) fans out into Clight l-value
    **statements** ([Sassign] for [Istore], [Sset] for temp binds, [Scall],
    [Sswitch]) built over C **expressions** ([Ebinop], [Ederef], [Ecast],
    [Econst_long]).  See [LOWERINGS.md] for the per-op table this file implements,
    and the "Clight" column in particular ([Iload]->[Ederef (Ebinop Oadd ...)],
    [Tswitch]->[Sswitch] over [LScons] arms, [Icall_indirect]->[Scall] through a
    cast function pointer).

    Because Clight has real structured statements — [Ssequence], [Sswitch] with
    [Sbreak]-terminated [LScons] arms, [Sreturn] — LLIR's control-flow *tree*
    (I1) maps directly onto Clight's *statement* tree, with no CFG re-embedding
    (contrast [LLIR_to_VIR.v], where a [Tswitch] must open fresh basic blocks).
    That makes [lower_term] here a plain structural recursion returning one
    [statement].

    ---------------------------------------------------------------------------
    Note on [Module LLIR] below.  The canonical LLIR AST is the sibling file
    [LLIR.v].  In the integrated dune / coq_makefile build this file opens with

        From LLIR Require Import LLIR.

    and the module below is deleted.  Under the MCP-only verification workflow
    ([rocq_compile_file] compiles each file ephemerally, installs no local [.vo]
    and forbids [Load]), a cross-file [Require] of the sibling cannot resolve, so
    the LLIR AST is mirrored inline, *verbatim* from [LLIR.v], inside [Module
    LLIR] and then [Import]ed — exactly the workaround [LLIR_to_VIR.v] uses.
    [Import LLIR] brings the identical datatype names. *)

(** The CompCert Clight imports, mirrored from the C backend
    [CertiRocq/Codegen/LambdaANF_to_Clight_stack.v] (its [From compcert Require
    Import] block).  These put Clight's [statement]/[expr]/[Sset]/[Sassign]/
    [Ebinop]/[Ederef]/[Sswitch]/[Scall] and the [Ctypes]/[Cop]/[Integers]
    vocabulary in scope. *)
From compcert Require Import
  common.AST
  lib.Integers
  cfrontend.Cop
  cfrontend.Ctypes
  cfrontend.Clight
  common.Values.
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

(** ** Runtime ABI types (the 64-bit view of the C backend's [val]).

    The C backend defines its value cell as [talignas 3 (tptr tvoid)] — an
    8-byte-aligned [void*].  LLIR's [word] is that same 8-byte cell viewed as an
    i64 (I3); every [binop] is word arithmetic on it, and the boxed/unboxed tag
    bit lives in its low bit.  We take the untagged i64 view [Tlong Unsigned] as
    the register/value type [val], its signed sibling [sval] for arithmetic
    shifts and signed compares, and [valPtr = val*] as the heap-address type the
    [Iload]/[Istore]/[Igep] triple casts through (I2).  A comparison yields a C
    [int] ([tint]). *)
Definition val    : type := Tlong Unsigned noattr.
Definition sval   : type := Tlong Signed noattr.
Definition valPtr : type := Tpointer val noattr.
Definition tint   : type := Tint I32 Signed noattr.

(** The [thread_info] handle every emitted function receives as arg 0 (ABI:
    [fn_params] head).  Placeholder identity — the integrated pass threads the
    real [thread_info*] type and the parameter's [ident]; here it is a fixed
    temp so [lower_instr] can stay a pure per-instruction function. *)
Definition tinfo_id : ident := 1%positive.
Definition tinfo_ty : type := valPtr.
Definition etinfo   : expr := Etempvar tinfo_id tinfo_ty.

(** ** Literals and operands. *)

(** An immediate machine word -> a Clight [long] constant.  (On a 32-bit target
    the C backend uses [Econst_int]; the portable 64-bit LLIR word is a
    [Econst_long].) *)
Definition c_int (z : Z) : expr := Econst_long (Int64.repr z) val.

(** [lower_operand] — an operand is a value already in hand: an SSA register maps
    to a [Etempvar] (LLIR [reg = positive = Clight ident], variable-preserving),
    an immediate to a [Econst_long]. *)
Definition lower_operand (o : LLIR.operand) : expr :=
  match o with
  | LLIR.Oreg r => Etempvar r val
  | LLIR.Oimm w => c_int w
  end.

(** [lower_binop op a b] — each [binop] maps to one Clight [Ebinop] over the
    matching [binary_operation] of [Cop].  CompCert's [Ebinop] carries no
    signedness on the operator itself — [Oshr]/[Olt] read signed-vs-unsigned off
    the *operand types* — so the two shifts and the two less-thans differ only in
    whether the left/both operands are first [Ecast] to [sval]:

      - [Bashr] (arithmetic >>) casts the shiftee to [sval]; [Blshr] (logical >>)
        keeps the unsigned [val], and both emit [Oshr].
      - [Blt_s] casts both operands to [sval]; [Blt_u] keeps [val]; both emit
        [Olt].
      - [Beq]/[Bne] -> [Oeq]/[One]; comparisons yield a C [int] (0/1 word). *)
Definition lower_binop (op : LLIR.binop) (a b : expr) : expr :=
  match op with
  | LLIR.Badd  => Ebinop Oadd a b val
  | LLIR.Bsub  => Ebinop Osub a b val
  | LLIR.Bmul  => Ebinop Omul a b val
  | LLIR.Bshl  => Ebinop Oshl a b val
  | LLIR.Bashr => Ebinop Oshr (Ecast a sval) b val
  | LLIR.Blshr => Ebinop Oshr a b val
  | LLIR.Band  => Ebinop Oand a b val
  | LLIR.Bor   => Ebinop Oor  a b val
  | LLIR.Bxor  => Ebinop Oxor a b val
  | LLIR.Beq   => Ebinop Oeq  a b tint
  | LLIR.Bne   => Ebinop One  a b tint
  | LLIR.Blt_s => Ebinop Olt  (Ecast a sval) (Ecast b sval) tint
  | LLIR.Blt_u => Ebinop Olt  a b tint
  end.

(** ** Field addressing — the one controlled word->address site (I2).

    [field_addr b n] is the C address [&((cast to val-ptr b)[n])] =
    [Ebinop Oadd (cast b to valPtr) n], the C
    address of word [n] of a boxed base.  Clight pointer arithmetic scales [n] by
    [sizeof val = 8] automatically, so [n] is the field *index*, not a byte
    offset (LOWERINGS: the ×8 is C's, not ours).  [field b n] dereferences it.
    This mirrors the C backend's [Field(t,n)] notation
    ([*(add ([valPtr] t) (c_int n val))]). *)
Definition field_addr (b : expr) (n : N) : expr :=
  Ebinop Oadd (Ecast b valPtr) (c_int (Z.of_N n)) valPtr.
Definition field (b : expr) (n : N) : expr :=
  Ederef (field_addr b n) val.

(** Call argument list: the [thread_info] handle first, then the value args. *)
Definition lower_call_args (args : list LLIR.operand) : list expr :=
  etinfo :: map lower_operand args.

(** The Clight function *type* of an [argc]-ary CertiRocq callee:
    [val (thread_info*, val, ..., val)]. *)
Definition fun_sig (argc : nat) : type :=
  Tfunction (tinfo_ty :: List.repeat val argc) val cc_default.

(** Global-symbol resolution.  Clight function designators are [Evar] over an
    [ident] ([positive]), not a string — so a real pass threads a name
    environment [funsym -> ident].  Placeholder identity here so [lower_instr]
    keeps its clean [instr -> statement] signature; the integrated build
    substitutes the global [genv] lookup. *)
Definition fun_ident (f : LLIR.funsym) : ident := 1%positive.

(** The runtime allocator symbol used by the [Ialloc] placeholder. *)
Definition alloc_id : ident := 2%positive.
Definition alloc_ty : type := Tfunction (tinfo_ty :: val :: nil) val cc_default.

(** ** [lower_instr] — one straight-line LLIR instruction to one Clight
    statement.  Register-defining instrs become [Sset r e] (temp bind);
    [Istore] becomes an l-value [Sassign]; calls become [Scall (Some r) ...].

    Per [LOWERINGS.md] (Clight column):
      - [Iconst]/[Ibinop] -> [Sset r] of a constant / an [Ebinop].
      - [Iload] -> [Sset r (Ederef (address expr))]  (= [Sset r Field(b,n)]).
      - [Istore] -> [Sassign (Ederef ...) v]  (= [Field(b,n) := v]).
      - [Igep] -> [Sset r (Ebinop Oadd ...)] — the field *address*, no deref
        (the C backend's [Eaddrof Field] folded to the [add]).
      - [Icall] -> [Scall (Some r)] on the named global, [tinfo] prepended.
      - [Icall_indirect] -> [Scall (Some r)] through an [Ecast] of the code-
        pointer word to a function-pointer type.
      - [Iptrtoint]/[Iinttoptr] -> [Sset r (Ecast ...)] to [val] / [valPtr].
        CompCert *permits* this [Ecast], but it is NOT wildcard-provenance
        punning: casting an arbitrary integer to a pointer and dereferencing it
        is undefined in CompCert's memory model.  These are LLVM-ONLY (I2 escape
        hatch); the **portable** LLIR fragment never emits them (LOWERINGS §
        "Iptrtoint/Iinttoptr"), so a real Clight lowering would [reject] any
        program containing them.  They are handled here only for totality.
      - [Ialloc] -> a placeholder [Scall] to [certirocq_alloc].  The real
        lowering is a shadow-stack GC safepoint + bump macro (LOWERINGS §
        "Ialloc"); that expansion is deferred to the block-level emitter, exactly
        as on the VIR side. *)
Definition lower_instr (i : LLIR.instr) : statement :=
  match i with
  | LLIR.Iconst r w =>
      Sset r (c_int w)
  | LLIR.Ibinop r op a b =>
      Sset r (lower_binop op (lower_operand a) (lower_operand b))
  | LLIR.Iload r b n =>
      Sset r (field (lower_operand b) n)
  | LLIR.Istore b n v =>
      Sassign (field (lower_operand b) n) (lower_operand v)
  | LLIR.Igep r b n =>
      Sset r (field_addr (lower_operand b) n)
  | LLIR.Iptrtoint r p =>
      Sset r (Ecast (lower_operand p) val)      (* LLVM-ONLY; portable LLIR never emits *)
  | LLIR.Iinttoptr r p =>
      Sset r (Ecast (lower_operand p) valPtr)   (* LLVM-ONLY; portable LLIR never emits *)
  | LLIR.Icall r f args =>
      Scall (Some r)
        (Evar (fun_ident f) (fun_sig (List.length args)))
        (lower_call_args args)
  | LLIR.Icall_indirect r fp args =>
      Scall (Some r)
        (Ecast (lower_operand fp) (Tpointer (fun_sig (List.length args)) noattr))
        (lower_call_args args)
  | LLIR.Ialloc r n =>
      (* Thin placeholder (see the doc comment): a call to the runtime
         allocator; the shadow-stack GC-safepoint + bump expansion is the
         block-level emitter's job. *)
      Scall (Some r)
        (Evar alloc_id alloc_ty)
        (etinfo :: c_int (Z.of_N n) :: nil)
  end.

(** ** [lower_term] — LLIR's control-flow tree to one Clight [statement].

    [Tret] -> [Sreturn (Some v)]; [Tseq] -> [Ssequence]; [Tswitch] -> [Sswitch]
    over a [labeled_statements] chain: each matching arm is
    [LScons (Some key) (arm ; Sbreak)] and the mandatory default is the closing
    [LScons None default LSnil].  The nested [fix] over [arms] recurses back into
    [lower_term] on each arm term and on [default] — both structural subterms of
    the [Tswitch], so the definition is well-founded (same pattern as
    [LLIR_to_VIR.v]'s [arm_loop]). *)
Fixpoint lower_term (t : LLIR.term) {struct t} : statement :=
  match t with
  | LLIR.Tret v =>
      Sreturn (Some (lower_operand v))
  | LLIR.Tseq i k =>
      Ssequence (lower_instr i) (lower_term k)
  | LLIR.Tswitch s arms default =>
      let fix arms_ls (arms : list (LLIR.word * LLIR.term)) {struct arms}
            : labeled_statements :=
          match arms with
          | [] => LScons None (lower_term default) LSnil
          | (w, at_) :: rest =>
              LScons (Some w)
                     (Ssequence (lower_term at_) Sbreak)
                     (arms_ls rest)
          end in
      Sswitch (lower_operand s) (arms_ls arms)
  end.

(** ** [lower_function] — a whole Clight function body statement.

    A faithful skeleton: the SSA body lowers to one [statement]; a real
    [Clight.function] record additionally needs the parameter list, the temp
    declarations, the return type, and the shadow-stack frame prologue/epilogue
    ([init_stack]/[discard_stack]) that the C backend threads.  Those are
    orthogonal plumbing; the interesting content — the instruction/term walk —
    is [lower_term] of the body. *)
Definition lower_function_body (f : LLIR.function) : statement :=
  lower_term (LLIR.fn_body f).

(** ** Smoke tests — pin the lowered Clight shape of a few instructions/terms. *)

Example lower_iconst_shape :
  lower_instr (LLIR.Iconst 3%positive 7%Z)
  = Sset 3%positive (Econst_long (Int64.repr 7) val).
Proof. reflexivity. Qed.

Example lower_ibinop_add_shape :
  lower_instr (LLIR.Ibinop 1%positive LLIR.Badd (LLIR.Oreg 2%positive) (LLIR.Oimm 5%Z))
  = Sset 1%positive
      (Ebinop Oadd (Etempvar 2%positive val) (Econst_long (Int64.repr 5) val) val).
Proof. reflexivity. Qed.

Example lower_bne_is_Oone :
  lower_instr (LLIR.Ibinop 4%positive LLIR.Bne (LLIR.Oreg 1%positive) (LLIR.Oimm 0%Z))
  = Sset 4%positive
      (Ebinop One (Etempvar 1%positive val) (Econst_long (Int64.repr 0) val) tint).
Proof. reflexivity. Qed.

Example lower_iload_is_deref :
  lower_instr (LLIR.Iload 5%positive (LLIR.Oreg 1%positive) 2%N)
  = Sset 5%positive
      (Ederef
        (Ebinop Oadd (Ecast (Etempvar 1%positive val) valPtr)
                (Econst_long (Int64.repr 2) val) valPtr)
        val).
Proof. reflexivity. Qed.

Example lower_istore_is_assign :
  lower_instr (LLIR.Istore (LLIR.Oreg 1%positive) 0%N (LLIR.Oreg 2%positive))
  = Sassign
      (Ederef
        (Ebinop Oadd (Ecast (Etempvar 1%positive val) valPtr)
                (Econst_long (Int64.repr 0) val) valPtr)
        val)
      (Etempvar 2%positive val).
Proof. reflexivity. Qed.

Example lower_tret_shape :
  lower_term (LLIR.Tret (LLIR.Oreg 1%positive))
  = Sreturn (Some (Etempvar 1%positive val)).
Proof. reflexivity. Qed.

(** [Tswitch] over one matching arm (key 0 -> return 9) plus a default
    (return the scrutinee register) lowers to a [Sswitch] whose [labeled_
    statements] chain is [LScons (Some 0) (return 9 ; break) (LScons None
    (return r1) LSnil)]. *)
Example lower_tswitch_shape :
  lower_term (LLIR.Tswitch (LLIR.Oreg 1%positive)
                [(0%Z, LLIR.Tret (LLIR.Oimm 9%Z))]
                (LLIR.Tret (LLIR.Oreg 1%positive)))
  = Sswitch (Etempvar 1%positive val)
      (LScons (Some 0%Z)
              (Ssequence (Sreturn (Some (Econst_long (Int64.repr 9) val))) Sbreak)
              (LScons None (Sreturn (Some (Etempvar 1%positive val))) LSnil)).
Proof. reflexivity. Qed.

(** [Tseq (Iload r1 (Oreg 1) 2) (Tret r1)] -> a load statement sequenced before
    the return. *)
Compute lower_term
  (LLIR.Tseq (LLIR.Iload 5%positive (LLIR.Oreg 1%positive) 2%N)
             (LLIR.Tret (LLIR.Oreg 5%positive))).
