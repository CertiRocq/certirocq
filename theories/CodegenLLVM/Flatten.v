(** * CodegenLLVM.Flatten — linearize the emitter's tree-structured VIR.

    [LambdaANF_to_LLVM.compile_prog] builds VIR whose operands are nested
    operation-expressions (e.g. [br (icmp eq (and %y 1) 0)]).  Vellvm's AST and
    semantics permit that, but LLVM's concrete syntax does not: every operand
    must be atomic (a register or a literal), and the [and]/[icmp]/[getelementptr]
    constant-expression forms with runtime operands are rejected outright.
    [flatten_prog] lifts every compound operand to its own [INSTR_Op] binding
    with a fresh SSA name, yielding a program whose printed [.ll] parses and
    links.

    Fresh names are [Raw (Zneg (16*c))].  The emitter's own temporaries are
    [Raw (Zneg (seed*16+k))] with [k >= 1] (see [LambdaANF_to_LLVM.ntmp]), so
    multiples of sixteen are disjoint from them; real ANF variables are
    [Raw (Zpos _)].  Every fresh name is therefore distinct from any name the
    emitter produces. *)

From Vellvm Require Import Syntax.LLVMAst.
From Stdlib Require Import BinNums BinPos List.
Import ListNotations.

Definition flat_id (c : positive) : raw_id := Raw (Zneg (16 * c)).

(** [atomize e c] returns [(extra, a, c')] where [a] is an atomic expression
    (register or literal) denoting [e], [extra] is the code that computes it, and
    [c'] the next fresh counter.  Only the operation-expressions the emitter
    produces are decomposed; anything else (identifiers, literals) is already
    atomic and returned unchanged. *)
Fixpoint atomize (e : exp typ) (c : positive) {struct e}
  : code typ * exp typ * positive :=
  match e with
  | OP_IBinop op t e1 e2 =>
      let '(c1, a1, n1) := atomize e1 c in
      let '(c2, a2, n2) := atomize e2 n1 in
      let fid := flat_id n2 in
      ((c1 ++ c2 ++ [(IId fid, INSTR_Op (OP_IBinop op t a1 a2), [])])%list,
       EXP_Ident (ID_Local fid), Pos.succ n2)
  | OP_ICmp ss cmp t e1 e2 =>
      let '(c1, a1, n1) := atomize e1 c in
      let '(c2, a2, n2) := atomize e2 n1 in
      let fid := flat_id n2 in
      ((c1 ++ c2 ++ [(IId fid, INSTR_Op (OP_ICmp ss cmp t a1 a2), [])])%list,
       EXP_Ident (ID_Local fid), Pos.succ n2)
  | OP_Conversion cv t1 e1 t2 =>
      let '(c1, a1, n1) := atomize e1 c in
      let fid := flat_id n1 in
      ((c1 ++ [(IId fid, INSTR_Op (OP_Conversion cv t1 a1 t2), [])])%list,
       EXP_Ident (ID_Local fid), Pos.succ n1)
  | OP_GetElementPtr t ptr idxs =>
      let '(pt, pe) := ptr in
      let '(cp, ape, np) := atomize pe c in
      let fix aidx (l : list (typ * exp typ)) (k : positive) {struct l}
            : code typ * list (typ * exp typ) * positive :=
          match l with
          | [] => ([], [], k)
          | (it, ie) :: rest =>
              let '(ci, ai, k1) := atomize ie k in
              let '(cr, ar, k2) := aidx rest k1 in
              ((ci ++ cr)%list, (it, ai) :: ar, k2)
          end in
      let '(cidx, aidxs, ni) := aidx idxs np in
      let fid := flat_id ni in
      ((cp ++ cidx ++ [(IId fid, INSTR_Op (OP_GetElementPtr t (pt, ape) aidxs), [])])%list,
       EXP_Ident (ID_Local fid), Pos.succ ni)
  | _ => ([], e, c)
  end.

Fixpoint atomize_idxs (l : list (typ * exp typ)) (k : positive) {struct l}
  : code typ * list (typ * exp typ) * positive :=
  match l with
  | [] => ([], [], k)
  | (it, ie) :: rest =>
      let '(ci, ai, k1) := atomize ie k in
      let '(cr, ar, k2) := atomize_idxs rest k1 in
      ((ci ++ cr)%list, (it, ai) :: ar, k2)
  end.

Definition atomize_texp (te : typ * exp typ) (c : positive)
  : code typ * (typ * exp typ) * positive :=
  let '(t, e) := te in
  let '(cc, ae, n) := atomize e c in
  (cc, (t, ae), n).

(** For [INSTR_Op op]: keep the top operation as the instruction (LLVM requires
    [INSTR_Op] to hold an [OP_] form) but atomize its immediate operands. *)
Definition atomize_op (e : exp typ) (c : positive)
  : code typ * exp typ * positive :=
  match e with
  | OP_IBinop op t e1 e2 =>
      let '(c1, a1, n1) := atomize e1 c in
      let '(c2, a2, n2) := atomize e2 n1 in
      ((c1 ++ c2)%list, OP_IBinop op t a1 a2, n2)
  | OP_ICmp ss cmp t e1 e2 =>
      let '(c1, a1, n1) := atomize e1 c in
      let '(c2, a2, n2) := atomize e2 n1 in
      ((c1 ++ c2)%list, OP_ICmp ss cmp t a1 a2, n2)
  | OP_Conversion cv t1 e1 t2 =>
      let '(c1, a1, n1) := atomize e1 c in
      (c1, OP_Conversion cv t1 a1 t2, n1)
  | OP_GetElementPtr t ptr idxs =>
      let '(pt, pe) := ptr in
      let '(cp, ape, np) := atomize pe c in
      let '(cidx, aidxs, ni) := atomize_idxs idxs np in
      ((cp ++ cidx)%list, OP_GetElementPtr t (pt, ape) aidxs, ni)
  | _ => ([], e, c)
  end.

Fixpoint atomize_args (l : list (texp typ * list param_attr)) (k : positive)
         {struct l} : code typ * list (texp typ * list param_attr) * positive :=
  match l with
  | [] => ([], [], k)
  | (te, pa) :: rest =>
      let '(cc, te', k1) := atomize_texp te k in
      let '(cr, ar, k2) := atomize_args rest k1 in
      ((cc ++ cr)%list, (te', pa) :: ar, k2)
  end.

Fixpoint flat_code (l : code typ) (c : positive) {struct l} : code typ * positive :=
  match l with
  | [] => ([], c)
  | (id, i, md) :: rest =>
      let '(ci, n1) :=
        match i with
        | INSTR_Op e =>
            let '(cc, e', n) := atomize_op e c in
            ((cc ++ [(id, INSTR_Op e', md)])%list, n)
        | INSTR_Load t ptr anns =>
            let '(cc, ptr', n) := atomize_texp ptr c in
            ((cc ++ [(id, INSTR_Load t ptr' anns, md)])%list, n)
        | INSTR_Store val ptr anns =>
            let '(c1, val', n1) := atomize_texp val c in
            let '(c2, ptr', n2) := atomize_texp ptr n1 in
            ((c1 ++ c2 ++ [(id, INSTR_Store val' ptr' anns, md)])%list, n2)
        | INSTR_Call fn args anns obs =>
            let '(c1, fn', n1) := atomize_texp fn c in
            let '(c2, args', n2) := atomize_args args n1 in
            ((c1 ++ c2 ++ [(id, INSTR_Call fn' args' anns obs, md)])%list, n2)
        | _ => ([(id, i, md)], c)
        end in
      let '(cr, n2) := flat_code rest n1 in
      ((ci ++ cr)%list, n2)
  end.

Definition flat_term (tm : terminator typ) (c : positive)
  : code typ * terminator typ * positive :=
  match tm with
  | TERM_Ret v      => let '(cc, v', n) := atomize_texp v c in (cc, TERM_Ret v', n)
  | TERM_Br v b1 b2 => let '(cc, v', n) := atomize_texp v c in (cc, TERM_Br v' b1 b2, n)
  | TERM_Switch v d brs =>
      let '(cc, v', n) := atomize_texp v c in (cc, TERM_Switch v' d brs, n)
  | _ => ([], tm, c)
  end.

Definition flat_block (b : block typ) (c : positive) : block typ * positive :=
  let '(cc, n1) := flat_code (blk_code b) c in
  let '(tid, tm, tmd) := blk_term b in
  let '(tc, tm', n2) := flat_term tm n1 in
  (mk_block (blk_id b) (blk_phis b) (cc ++ tc)%list (tid, tm', tmd) (blk_comments b), n2).

Fixpoint flat_blocks (bs : list (block typ)) (c : positive) {struct bs}
  : list (block typ) * positive :=
  match bs with
  | [] => ([], c)
  | b :: rest =>
      let '(b', n1) := flat_block b c in
      let '(rs, n2) := flat_blocks rest n1 in
      (b' :: rs, n2)
  end.

Definition flat_def (d : definition typ (block typ * list (block typ)))
  : definition typ (block typ * list (block typ)) :=
  let '(entry, rest) := df_instrs d in
  let '(entry', n1) := flat_block entry 1%positive in
  let '(rest', _)   := flat_blocks rest n1 in
  @mk_definition typ (block typ * list (block typ))
    (df_prototype d) (df_args d) (entry', rest').

Definition flatten_tle (t : toplevel_entity typ (block typ * list (block typ)))
  : toplevel_entity typ (block typ * list (block typ)) :=
  match t with
  | TLE_Definition d => TLE_Definition (flat_def d)
  | _ => t
  end.

Definition flatten_prog
    (ts : list (toplevel_entity typ (block typ * list (block typ))))
  : list (toplevel_entity typ (block typ * list (block typ))) :=
  map flatten_tle ts.
