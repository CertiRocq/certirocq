(** * LambdaANF -> LLIR lowering (scaffold).

    The single front pass of CertiRocq issue #121: LambdaANF's [cps.exp] down to
    the target-neutral [LLIR.term].  This file implements two constructs against
    the shared value ABI and leaves the rest as documented placeholders; the
    point is the *shape* of the pass, so that filling each remaining arm is a
    local edit that inherits LLIR's common-subset guarantees.

    Two cases are concrete:

      - [Ehalt x]  -> [Tret (Oreg x)].  Return the value bound to [x].

      - [Eproj x t n y e]  ->  [Tseq (Iload x (Oreg y) n) (translate e)].
        [Eproj] is a field load at base+word-offset, exactly the value ABI's
        [Field(y, n)] (see [LOWERING.md]): [x := mem[y + n]], then continue.
        This is the [Iload] primitive of invariant (I2), verbatim.

    LambdaANF's [var] and LLIR's [reg] are both [positive] (in fact
    [var = M.elt = positive] and [reg = positive]), so the lowering is
    variable-preserving: an ANF variable becomes the identically-numbered SSA
    register.  The field index [n : N] carries across unchanged.

    ---------------------------------------------------------------------------
    Note on [Module LLIR] below.  The canonical LLIR AST is the sibling file
    [LLIR.v] (deliverable #1), which compiles on its own.  In the integrated
    dune / coq_makefile build this file opens with

        From LLIR Require Import LLIR.

    and the module below is deleted.  Under the MCP-only verification workflow
    used here, [rocq_compile_file] compiles each file ephemerally — it installs
    no local [.vo] and forbids [Load] — so a cross-file [Require] of the sibling
    cannot resolve.  To keep this file independently MCP-verifiable, the LLIR AST
    is mirrored inline, *verbatim* from [LLIR.v], inside [Module LLIR] and then
    [Import]ed.  [Import LLIR] brings exactly the names [Require Import LLIR]
    would; [translate] is therefore checked against the identical datatype. *)

From CertiRocq.LambdaANF Require Import cps.
From Stdlib Require Import BinNums BinPos BinNat BinInt List String.
Import ListNotations.

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

(** A documented placeholder for the not-yet-lowered constructs.  It returns the
    unit-like unboxed value [Val_long 0 = 1], a well-typed [term] standing in for
    the real lowering of [Econstr]/[Ecase]/[Eletapp]/[Efun]/[Eapp]/[Eprim_val]/
    [Eprim].  Each will become: [Econstr] -> [Ialloc] + [Istore]* ; [Ecase] ->
    [Tswitch] on the [Is_block]/tag scrutinee ; [Eapp]/[Eletapp] ->
    [Icall_indirect] ; [Eprim] -> [Icall] to the primitive symbol. *)
Definition todo : term := Tret (Oimm 1%Z).

(** [translate e] lowers an ANF expression to an LLIR block ([term]).  It
    recurses only on the structural subterm of the concretely-handled [Eproj];
    the placeholder arms do not recurse, keeping this a plain structural
    [Fixpoint]. *)
Fixpoint translate (e : exp) : term :=
  match e with
  | Ehalt x =>
      (* Return the answer value. *)
      Tret (Oreg x)
  | Eproj x t n y e' =>
      (* x := Field(y, n) = load at base [y], word offset [n]; then continue. *)
      Tseq (Iload x (Oreg y) n) (translate e')
  | Econstr _ _ _ _   => todo
  | Ecase _ _         => todo
  | Eletapp _ _ _ _ _ => todo
  | Efun _ _          => todo
  | Eapp _ _ _        => todo
  | Eprim_val _ _ _   => todo
  | Eprim _ _ _ _     => todo
  end.

(** Sanity checks that the two real cases compute to the intended LLIR. *)
Example ehalt_ok : forall x, translate (Ehalt x) = Tret (Oreg x).
Proof. reflexivity. Qed.

Example eproj_ok :
  forall x t n y,
    translate (Eproj x t n y (Ehalt x))
    = Tseq (Iload x (Oreg y) n) (Tret (Oreg x)).
Proof. reflexivity. Qed.
