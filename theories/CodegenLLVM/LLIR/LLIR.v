(** * LLIR — the shared low-level IR of CertiRocq issue #121.

    LLIR is the layer each machine-code backend of CertiRocq collapses onto: a
    single [LambdaANF -> LLIR] pass, then three thin lowerings [LLIR -> VIR],
    [LLIR -> Clight], [LLIR -> Wasm].  Its defining constraint — the whole point
    of the layer — is that it is *not* full LLVM IR but the **common subset of
    LLVM IR that CompCert-Clight AND WebAssembly can also express** (see
    [LLIR_AND_ISSUE_121.md] §2).  Every constructor below is chosen to lower to
    all three targets; the two exceptions are quarantined and flagged LLVM-ONLY.

    Three invariants keep LLIR a common subset, and each is enforced by the
    *shape* of a datatype here, not by a side condition:

      (I1) Structured control flow.  Control is a tree of nested [term]s whose
           only join is a [Tswitch] whose arms are themselves complete [term]s.
           There is no label, no [goto], no basic-block CFG.  Wasm has only
           structured control flow (nested blocks + [br_table]); Clight has
           [switch] but no first-class CFG.  A free CFG would lower to neither.

      (I2) Explicit memory, no pointer/integer punning.  Heap objects come from
           [Ialloc] (allocate n machine words) and are touched only through
           [Iload]/[Istore]/[Igep] at a *base operand + word offset*.  The
           reinterpretation "this machine word denotes a heap address" lives
           inside those three primitives, at one controlled site each backend
           implements natively (Clight: typed pointer + field; Wasm: linear-
           memory index; LLVM: [getelementptr]).  LLIR exposes no free
           [inttoptr]/[ptrtoint] in its portable fragment — that is exactly what
           lets the tagged-pointer ABI survive down to Wasm and Clight.

      (I3) Machine-word-only values.  The single value type is the machine word
           ([word], an i64).  Registers are SSA temporaries.  There are no
           aggregates, no unbounded integers, no floats-in-values; a boxed value
           is *by ABI convention* a word whose low bit is 0 and which addresses a
           heap object, tested with an ordinary bitwise [Band].  All three
           targets have i64 words and word arithmetic.

    Value ABI (shared verbatim with [LOWERING.md] / [values.h]):
      - [value = i64].
      - unboxed integer [n]:  [Val_long n = (n << 1) | 1],  [Long_val v = v >>a 1].
      - boxed block: heap array of words, [value] points at field 0, word[-1] is
        the header [(wosize << 10) | tag].
      - [Is_block v = (v & 1) == 0]. *)

From Stdlib Require Import BinNums BinPos BinNat BinInt List String.
Import ListNotations.

(** ** Scalars *)

(** SSA temporary.  [positive] mirrors LambdaANF's [var] so the lowering is
    variable-preserving; each register is assigned at most once. *)
Definition reg : Type := positive.

(** A machine word — the i64 that is LLIR's one and only value type (I3). *)
Definition word : Type := Z.

(** A function symbol (a global).  All three targets have named globals, so a
    direct call names one; nothing here needs a first-class function-pointer
    *type* — an indirect call goes through a word operand (I2/I3). *)
Definition funsym : Type := string.

(** An operand is a value already in hand: an SSA register or an immediate word.
    No memory operand — memory is reached only through the explicit [Iload]/
    [Istore]/[Igep] instructions (I2). *)
Inductive operand : Type :=
| Oreg : reg  -> operand
| Oimm : word -> operand.

(** ** Machine-word operations

    Every [binop] is a total function on i64 words and exists in Clight, Wasm and
    LLVM alike.  [Bshl]/[Bashr] are called out because they are the tag/untag
    shifts of the value ABI: [Val_long] is [Bshl _ 1] then [Bor _ 1];
    [Long_val] is [Bashr _ 1].  Comparisons return the word 0 or 1. *)
Inductive binop : Type :=
| Badd | Bsub | Bmul
| Bshl                    (* logical shift left  — Val_long tags with [<< 1]   *)
| Bashr                   (* arithmetic shift right — Long_val untags with [>>a 1] *)
| Blshr                   (* logical shift right — header field extraction      *)
| Band | Bor  | Bxor      (* Band _ 1 is the [Is_block]/[Is_long] tag test       *)
| Beq  | Bne              (* equality of words                                  *)
| Blt_s | Blt_u.          (* signed / unsigned less-than                        *)

(** ** Instructions

    A straight-line instruction.  Each register-defining instruction assigns its
    result register exactly once (SSA).  None of these transfers control — that
    is the [term] type's job (I1). *)
Inductive instr : Type :=
(** [r := imm]. *)
| Iconst : reg -> word -> instr
(** [r := a `op` b] over machine words. *)
| Ibinop : reg -> binop -> operand -> operand -> instr
(** [r := alloc n words].  Explicit allocation — the portable answer to
    issue #121's "explicit memory".  Returns a fresh heap base as a word.  NOT an
    [inttoptr]: the word is a first-class allocation handle each backend backs
    with its own allocator (nursery bump-pointer under [gc_stack]). *)
| Ialloc : reg -> N -> instr
(** [r := mem[base + off words]].  Field load.  This is the [Eproj]/[Field]
    primitive.  The base operand is a value the ABI says is a heap address; the
    word->address reinterpretation is internal to this instruction (I2). *)
| Iload  : reg -> operand -> N -> instr
(** [mem[base + off words] := v].  Field store (constructor initialisation). *)
| Istore : operand -> N -> operand -> instr
(** [r := &base[off]].  Field *address* without loading — the header write and
    interior-pointer cases.  [getelementptr] in LLVM, [&p->f] in Clight, an
    address computation in Wasm. *)
| Igep   : reg -> operand -> N -> instr
(** [r := f(args)].  Direct call to a named global. *)
| Icall  : reg -> funsym -> list operand -> instr
(** [r := fp(args)] through a code-pointer *word* [fp].  Indirect call.  Wasm lowers
    it to [call_indirect] via a function table; Clight to a call through a
    function-pointer cast; LLVM to a [call] on a bitcast operand. *)
| Icall_indirect : reg -> operand -> list operand -> instr
(** LLVM-ONLY (I2 escape hatch).  Raw word<->pointer casts.  These do NOT lower
    to Wasm (no [inttoptr]; linear memory is indexed, not punned) or to Clight
    (CompCert forbids fabricating a pointer with wildcard provenance from an
    integer).  They exist only so the [LLIR -> VIR] branch may realise the
    tagged-pointer ABI with LLVM's [ptrtoint]/[inttoptr] verbatim, as PHASE2
    §2.1 does.  A well-formed *portable* LLIR program contains neither; the Wasm
    and Clight lowerings reject any program that uses them. *)
| Iptrtoint : reg -> operand -> instr        (* LLVM-ONLY *)
| Iinttoptr : reg -> operand -> instr.       (* LLVM-ONLY *)

(** ** Structured control-flow terms (I1)

    A [term] is a block: a possibly-empty run of instructions ending in exactly
    one control transfer.  The only branch is [Tswitch]; each of its arms and its
    default is again a complete [term], so control forms a tree with no shared
    labels and no back-edge.  This is precisely the fragment Wasm's structured
    control flow and Clight's [switch] can both express; it is a strict subset of
    LLVM's br/switch CFG, which the [LLIR -> VIR] lowering trivially re-embeds. *)
Inductive term : Type :=
(** Run an instruction, then continue. *)
| Tseq    : instr -> term -> term
(** Switch on a scrutinee word: matching-value arms plus a mandatory default.
    Arms nest full [term]s, keeping control structured (no fallthrough, no
    goto).  This is the [Ecase] dispatch. *)
| Tswitch : operand -> list (word * term) -> term -> term
(** Return a value from the current function.  This is [Ehalt]. *)
| Tret    : operand -> term.

(** ** Top level *)

(** A function: a name, its SSA parameter registers (the first is the
    thread_info/heap handle by ABI convention), and its structured body. *)
Record function : Type := mk_function {
  fn_name   : funsym;
  fn_params : list reg;
  fn_body   : term
}.

(** A program: the flat list of top-level functions (LambdaANF's [Efun] block,
    already closure-converted and flattened) plus the entry symbol. *)
Record program : Type := mk_program {
  prog_funs  : list function;
  prog_entry : funsym
}.
