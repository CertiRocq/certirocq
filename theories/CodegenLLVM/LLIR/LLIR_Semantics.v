(** * LLIR_Semantics — a small-step operational semantics for the shared LLIR.

    This is the object the two-stage LLIR correctness proof needs
    (COMPOSITION.md §"the required LLIR semantics", §1.0):

      - a *small-step* relation over the structured [term] (I1: control is a
        tree whose only join is [Tswitch]);
      - a **provenance-free, word-addressed abstract heap** [lmem] (I2/I3: the
        one value type is the i64 [word], and the "this word is a heap address"
        reinterpretation lives *inside* the four memory primitives, so the LLIR
        semantics carries no Vellvm-style provenance);
      - the same tagged value ABI (registers and heap cells hold plain [word]s);
      - GC as an external event: [Ialloc] is the abstract bump allocation, the
        collector is called-never-compiled and is a no-op at this level.

    The [Iptrtoint]/[Iinttoptr] constructors are LLVM-ONLY.  Because the LLIR
    heap has *no provenance*, both denote the **identity on [word]** — which is
    exactly WHY they are the LLVM-only ops: there is nothing for a word<->pointer
    cast to *do* on a provenance-free word heap, so the portable fragment needs
    neither, and the meaning here is the trivial one.

    The AST is inlined as [Module LLIR] verbatim from LLIR.v (the MCP cross-file
    workaround: this file is self-contained and checks under rocq_compile_file
    with no Require of LLIR.v). *)

From Stdlib Require Import BinNums BinPos BinNat BinInt List String.
Import ListNotations.

(** ** The LLIR AST (inlined copy of LLIR.v) *)

Module LLIR.

  Definition reg : Type := positive.
  Definition word : Type := Z.
  Definition funsym : Type := string.

  Inductive operand : Type :=
  | Oreg : reg  -> operand
  | Oimm : word -> operand.

  Inductive binop : Type :=
  | Badd | Bsub | Bmul
  | Bshl
  | Bashr
  | Blshr
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

(** ** Machine state

    A [regfile] is a partial map [positive -> option word] (SSA temporaries).
    An [lmem] is the provenance-FREE abstract heap: a word-addressed partial map
    [Z -> option word] together with a bump frontier [lm_next : Z].  There are no
    blocks, no provenance, no typing — just words at word addresses. *)

Definition regfile : Type := positive -> option word.

Record lmem : Type := mk_lmem {
  lm_mem  : Z -> option word;   (* the word-addressed cells, provenance-free *)
  lm_next : Z                    (* the bump-allocation frontier             *)
}.

Definition empty_regfile : regfile := fun _ => None.

Definition set_reg (rf : regfile) (r : reg) (w : word) : regfile :=
  fun r' => if Pos.eqb r r' then Some w else rf r'.

Definition initial_lmem : lmem := mk_lmem (fun _ => None) 0%Z.

(** Bump the frontier by [n] words (the abstract allocation). *)
Definition bump_mem (lm : lmem) (n : N) : lmem :=
  mk_lmem (lm_mem lm) (Z.add (lm_next lm) (Z.of_N n)).

(** Write [w] at word address [addr]. *)
Definition store_mem (lm : lmem) (addr : Z) (w : word) : lmem :=
  mk_lmem (fun a => if Z.eqb a addr then Some w else lm_mem lm a) (lm_next lm).

(** ** Operand and binop evaluation *)

Definition eval_operand (rf : regfile) (o : operand) : option word :=
  match o with
  | Oreg r => rf r
  | Oimm w => Some w
  end.

Definition b2w (b : bool) : word := if b then 1%Z else 0%Z.

(** The arithmetic, the ABI tag shifts, and the comparisons (which yield 0/1).
    Every case is a total function on i64 words (I3). *)
Definition eval_binop (op : binop) (a b : word) : word :=
  match op with
  | Badd  => Z.add a b
  | Bsub  => Z.sub a b
  | Bmul  => Z.mul a b
  | Bshl  => Z.shiftl a b        (* Val_long tags with [<< 1] *)
  | Bashr => Z.shiftr a b        (* Long_val untags with [>>a 1] *)
  | Blshr => Z.shiftr a b        (* header-field extraction *)
  | Band  => Z.land a b          (* Band _ 1 is the Is_block tag test *)
  | Bor   => Z.lor a b
  | Bxor  => Z.lxor a b
  | Beq   => b2w (Z.eqb a b)
  | Bne   => b2w (negb (Z.eqb a b))
  | Blt_s => b2w (Z.ltb a b)
  | Blt_u => b2w (Z.ltb a b)
  end.

(** ** Small-step instruction relation

    [step_instr (rf,lm) i (rf',lm')]: executing the straight-line instruction [i]
    takes state [(rf,lm)] to [(rf',lm')].  Only the portable straight-line
    instructions have rules; [Icall]/[Icall_indirect] are external events (the GC
    and runtime calls) handled at a higher layer and given no rule here. *)

Inductive step_instr : (regfile * lmem) -> instr -> (regfile * lmem) -> Prop :=

(** [r := imm]. *)
| SI_const : forall rf lm r w,
    step_instr (rf, lm) (Iconst r w) (set_reg rf r w, lm)

(** [r := a op b]. *)
| SI_binop : forall rf lm r op a b va vb,
    eval_operand rf a = Some va ->
    eval_operand rf b = Some vb ->
    step_instr (rf, lm) (Ibinop r op a b)
               (set_reg rf r (eval_binop op va vb), lm)

(** [r := alloc n].  Bind [r] to the current frontier (the fresh base) and bump
    [next] by [n].  GC is an external no-op at this level. *)
| SI_alloc : forall rf lm r n,
    step_instr (rf, lm) (Ialloc r n)
               (set_reg rf r (lm_next lm), bump_mem lm n)

(** [r := mem[base + off]].  The base operand is a word the ABI says is a heap
    address; the word->address reinterpretation is internal to this rule (I2). *)
| SI_load : forall rf lm r b off base v,
    eval_operand rf b = Some base ->
    lm_mem lm (Z.add base (Z.of_N off)) = Some v ->
    step_instr (rf, lm) (Iload r b off) (set_reg rf r v, lm)

(** [mem[base + off] := v]. *)
| SI_store : forall rf lm b off vo base w,
    eval_operand rf b = Some base ->
    eval_operand rf vo = Some w ->
    step_instr (rf, lm) (Istore b off vo)
               (rf, store_mem lm (Z.add base (Z.of_N off)) w)

(** [r := &base[off]] — the address, no load. *)
| SI_gep : forall rf lm r b off base,
    eval_operand rf b = Some base ->
    step_instr (rf, lm) (Igep r b off)
               (set_reg rf r (Z.add base (Z.of_N off)), lm)

(** LLVM-ONLY.  On a provenance-free word heap a ptr<->int cast has nothing to
    do: it is the IDENTITY on [word].  This is precisely why the portable
    fragment omits them. *)
| SI_ptrtoint : forall rf lm r o w,
    eval_operand rf o = Some w ->
    step_instr (rf, lm) (Iptrtoint r o) (set_reg rf r w, lm)
| SI_inttoptr : forall rf lm r o w,
    eval_operand rf o = Some w ->
    step_instr (rf, lm) (Iinttoptr r o) (set_reg rf r w, lm).

(** ** Term evaluation

    A whole [term] evaluates to a [result] = the returned word plus the final
    heap.  The relation is inductive (no fuel needed: the [term] tree is finite
    and each [Tseq]/[Tswitch] rule recurses on a structural subterm). *)

Definition result : Type := (word * lmem)%type.

(** Switch dispatch: find the arm whose key matches the scrutinee word. *)
Fixpoint find_arm (arms : list (word * term)) (k : word) : option term :=
  match arms with
  | [] => None
  | (k', t) :: rest => if Z.eqb k k' then Some t else find_arm rest k
  end.

Inductive step_term : (regfile * lmem) -> term -> result -> Prop :=

(** [Tret o] returns [eval_operand o] and the current heap. *)
| ST_ret : forall rf lm o w,
    eval_operand rf o = Some w ->
    step_term (rf, lm) (Tret o) (w, lm)

(** [Tseq i t]: step the instruction, then continue on [t]. *)
| ST_seq : forall rf lm i t rf' lm' res,
    step_instr (rf, lm) i (rf', lm') ->
    step_term (rf', lm') t res ->
    step_term (rf, lm) (Tseq i t) res

(** [Tswitch]: an arm matches the scrutinee word. *)
| ST_switch_arm : forall rf lm o arms d k t res,
    eval_operand rf o = Some k ->
    find_arm arms k = Some t ->
    step_term (rf, lm) t res ->
    step_term (rf, lm) (Tswitch o arms d) res

(** [Tswitch]: no arm matches — take the default. *)
| ST_switch_default : forall rf lm o arms d k res,
    eval_operand rf o = Some k ->
    find_arm arms k = None ->
    step_term (rf, lm) d res ->
    step_term (rf, lm) (Tswitch o arms d) res.

(** ** Whole-function / whole-program evaluation *)

(** Bind the SSA parameter registers to the actual argument words. *)
Fixpoint init_regs (params : list reg) (args : list word) : regfile :=
  match params, args with
  | p :: ps, a :: qs => set_reg (init_regs ps qs) p a
  | _, _ => empty_regfile
  end.

(** Run a function on [args] from the empty heap. *)
Definition run_function (f : function) (args : list word) (res : result) : Prop :=
  step_term (init_regs (fn_params f) args, initial_lmem) (fn_body f) res.

(** Find a top-level function by name. *)
Fixpoint find_fun (fs : list function) (name : funsym) : option function :=
  match fs with
  | [] => None
  | f :: rest => if String.eqb (fn_name f) name then Some f else find_fun rest name
  end.

(** Run a whole program: dispatch to the entry function. *)
Definition run_program (p : program) (args : list word) (res : result) : Prop :=
  exists f, find_fun (prog_funs p) (prog_entry p) = Some f /\ run_function f args res.

(** ** Examples *)

(** [Tseq (Iconst 1 42) (Tret (Oreg 1))] evaluates to [42]. *)
Example ex_const_ret :
  step_term (empty_regfile, initial_lmem)
            (Tseq (Iconst 1%positive 42%Z) (Tret (Oreg 1%positive)))
            (42%Z, initial_lmem).
Proof.
  eapply ST_seq.
  - apply SI_const.
  - apply ST_ret. reflexivity.
Qed.

(** An [Iload] after an [Istore] reads back the stored word.
    [alloc r1] gives base [0]; [store *r1[0] := 7]; [load r2 := *r1[0]]; return 7. *)
Example ex_store_load :
  exists m,
    step_term (empty_regfile, initial_lmem)
      (Tseq (Ialloc 1%positive 1%N)
      (Tseq (Istore (Oreg 1%positive) 0%N (Oimm 7%Z))
      (Tseq (Iload 2%positive (Oreg 1%positive) 0%N)
            (Tret (Oreg 2%positive)))))
      (7%Z, m).
Proof.
  eexists.
  eapply ST_seq.
  { apply SI_alloc. }
  eapply ST_seq.
  { eapply SI_store; reflexivity. }
  eapply ST_seq.
  { eapply SI_load.
    - reflexivity.
    - reflexivity. }
  apply ST_ret. reflexivity.
Qed.

(** A whole-program run of the constant example. *)
Example ex_run_program :
  run_program
    (mk_program
       [ mk_function "main"%string [] (Tseq (Iconst 1%positive 42%Z) (Tret (Oreg 1%positive))) ]
       "main"%string)
    []
    (42%Z, initial_lmem).
Proof.
  exists (mk_function "main"%string [] (Tseq (Iconst 1%positive 42%Z) (Tret (Oreg 1%positive)))).
  split.
  - reflexivity.
  - unfold run_function. simpl.
    eapply ST_seq.
    + apply SI_const.
    + apply ST_ret. reflexivity.
Qed.
