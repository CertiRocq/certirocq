(** * LambdaANF -> LLVM IR (Vellvm VIR) code generation — Phase 1, v2.

    v2 closes the gaps the v1 skeleton documented:

      1. A ctor-environment interface [(get_ord, get_arity : ctor_tag -> N)] is
         threaded through the whole emitter, replacing the [lit 0]/[Pos.to_nat]
         placeholders with real constructor ordinals and object headers.
      2. Code generation is refactored to a single block-producing
         [translate_cfg : exp -> positive -> list (block typ) * positive] that
         threads a fresh block-id/SSA counter and folds the [Ecase] dispatch CFG
         in as the real [Ecase] case (structural recursion, one Fixpoint).
      3. [Econstr] boxed allocation carries a real GC safepoint: a limit-check
         block branching to a [garbage_collect] block (which reloads alloc/limit
         and loops back) or falling through to the allocation block, modelling
         [poc/runtime_interop.ll].
      4. [Efun] lifts each top-level [Fcons] to its own VIR [definition] via
         [mk_fun]; [compile_prog] emits the whole program as a list of
         [toplevel_entity].
      5. [Eprim_val] materialises a (documented placeholder) literal constant.

    The value representation and runtime/calling convention are the ones fixed by
    the existing CertiRocq C runtime ([values.h], [gc_stack.c]) and validated end
    to end by the hand-written LLVM PoCs under [poc/]; see [LOWERING.md]. *)

From CertiRocq.LambdaANF Require Import cps identifiers set_util.
From CertiRocq.Common Require Import AstCommon.   (* primitive_value / primInt / Uint63 *)
From Vellvm Require Import Syntax.LLVMAst.
From Stdlib Require Import BinNums BinPos BinNat BinInt List String ZArith.
Import ListNotations.
Open Scope string_scope.

(** ** LLVM types used by the runtime ABI *)

(** A CertiRocq [value] is a machine word. *)
Definition val_ty : typ := TYPE_I 64%positive.

(** Heap objects are addressed as [i64*]. *)
Definition ptr_ty : typ := TYPE_Pointer (Some (TYPE_I 64%positive)).

(** Every emitted function takes the thread_info pointer plus its value args:
    [i64 @fn(ptr %tinfo, i64 %a0, ...)]. *)
Definition tinfo_ty : typ := TYPE_Pointer None.

(** The [thread_info] struct layout (gc_stack.h):
    [{ value* alloc; value* limit; heap* h; value args[MAX_ARGS];
       stack_frame* fp; uintnat nalloc; void* odata }].  [args] is an inline
    array of [MAX_ARGS = 1024] words, so it must be modelled as an array type,
    not a single pointer: otherwise the struct GEP for [fp]/[nalloc] (field
    indices 4/5) computes the wrong byte offset and the [nalloc] store before a
    GC safepoint corrupts memory.  Used only by the GC safepoint's field GEPs
    ([gep_tinfo 0]=alloc, [1]=limit, [5]=nalloc). *)
Definition tinfo_struct_ty : typ :=
  TYPE_Struct [ptr_ty; ptr_ty; ptr_ty; TYPE_Array 1024%N val_ty; ptr_ty; val_ty].

Notation Lexp   := (LLVMAst.exp typ).
Notation Linstr := (LLVMAst.instr typ).
Notation Lcode  := (code typ).
Notation Lterm  := (terminator typ).

(** ** Value-representation helpers (mirror [values.h] / [poc/valuerep.ll]) *)

Definition lit (n : nat) : Lexp := EXP_Integer (Nat.to_num_int n).

(** An i64 literal from a [Z] directly (not via [nat] — a primInt value can be up
    to [2^63], whose unary [nat] would be catastrophic). *)
Definition litZ (z : Z) : Lexp := EXP_Integer (Z.to_num_int z).

(** The machine-integer value of a [primitive_value] literal, as [Z] (only
    primitive ints; floats/strings are not materialised at this ABI layer). *)
Definition prim_val_Z (pv : primitive_value) : option Z :=
  match projT1 pv as t return prim_value t -> option Z with
  | primInt => fun i => Some (Uint63.to_Z i)
  | _ => fun _ => None
  end (projT2 pv).

(** ANF variables are [positive]; each becomes a distinct SSA local. *)
Definition evar (v : var) : Lexp := EXP_Ident (ID_Local (Raw (Zpos v))).

(** ** SSA-name environment (for GC safepoints)

    A moving collector relocates objects, so a pointer held in an SSA register
    across a GC point is stale unless reloaded from a root.  In SSA the reloaded
    value is a *new* name, so past a safepoint a live variable must be referred to
    by that new name.  [nenv] maps each ANF variable to its CURRENT SSA name; it
    is the identity ([Raw (Zpos v)]) everywhere except for the live variables a
    safepoint has just reloaded and merged with a phi.  This environment IS the
    [env_rel] the correctness proof threads, which is why the lowering carries it
    explicitly rather than substituting after the fact. *)
Definition nenv := var -> raw_id.
Definition base_env : nenv := fun v => Raw (Zpos v).
Definition env_set (env : nenv) (v : var) (r : raw_id) : nenv :=
  fun w => if Pos.eqb w v then r else env w.
Fixpoint env_set_list (env : nenv) (vs : list var) (rs : list raw_id) : nenv :=
  match vs, rs with
  | v :: vs', r :: rs' => env_set (env_set_list env vs' rs') v r
  | _, _ => env
  end.
(** A variable used as a value, resolved through the current environment. *)
Definition nvar (env : nenv) (v : var) : Lexp := EXP_Ident (ID_Local (env v)).

(** A variable reference that knows the top-level function set [fs].  Top-level
    functions are emitted by [mk_fun] as GLOBALs named [Anon (Zpos f)], so any
    reference to such an [f] — a direct callee, or a code pointer stored into a
    closure record — must be [ID_Global], not [ID_Local].  All other variables
    are ordinary SSA locals.  (The v1/v2 emitter used [ID_Local] for every
    reference, so calls resolved to undefined locals and closure code pointers
    were stored as undefined values.) *)
Definition is_fun (fs : list positive) (v : var) : bool :=
  List.existsb (Pos.eqb v) fs.

(** A variable used as a VALUE (stored into a closure field, passed as an
    argument, or returned).  A top-level function's value is its address as a
    machine word: [ptrtoint @f].  With Vellvm/LLVM opaque pointers the source
    type is the generic [ptr], so the exact function signature is irrelevant
    here.  Non-functions are ordinary SSA locals. *)
Definition gvar (fs : list positive) (env : nenv) (v : var) : Lexp :=
  if is_fun fs v
  then OP_Conversion Ptrtoint (TYPE_Pointer None)
         (EXP_Ident (ID_Global (Anon (Zpos v)))) val_ty
  else nvar env v.

(** A variable used as a CALL TARGET.  A top-level function is called directly
    ([call @f]).  A local code pointer is an integer word that must be cast back
    to a pointer before the indirect call ([inttoptr %f]). *)
Definition gcallee (fs : list positive) (env : nenv) (f : var) : Lexp :=
  if is_fun fs f
  then EXP_Ident (ID_Global (Anon (Zpos f)))
  else OP_Conversion Inttoptr val_ty (nvar env f) (TYPE_Pointer None).

(** [Val_long n = (n << 1) | 1]. *)
Definition val_long (n : Lexp) : Lexp :=
  OP_IBinop (Or false) val_ty (OP_IBinop (Shl false false) val_ty n (lit 1)) (lit 1).

(** [Long_val v = v >>a 1]  (arithmetic shift). *)
Definition long_val (v : Lexp) : Lexp :=
  OP_IBinop (AShr false) val_ty v (lit 1).

(** [Is_block v = (v & 1) == 0] — even words are heap pointers. *)
Definition is_block (v : Lexp) : Lexp :=
  OP_ICmp false Eq val_ty (OP_IBinop And val_ty v (lit 1)) (lit 0).

(** Address of field [n] of a boxed value: [gep i64, (inttoptr v), n]. *)
Definition gep_field (base : Lexp) (n : N) : Lexp :=
  OP_GetElementPtr val_ty
    (ptr_ty, OP_Conversion Inttoptr val_ty base ptr_ty)
    [(val_ty, lit (N.to_nat n))].

(** [Field(y, n)]: load the n-th field of the block held in [y]. *)
Definition load_field (env : nenv) (y : var) (n : N) : Linstr :=
  INSTR_Load val_ty (ptr_ty, gep_field (nvar env y) n) [].

(** ** Extra helpers for the allocation / call lowering *)

(** The [thread_info*] parameter every emitted function receives. *)
Definition etinfo : Lexp := EXP_Ident (ID_Local (Name "tinfo")).

(** GEP field [n] of an *already-typed pointer* SSA value (no [inttoptr]). Used
    to walk the freshly-bumped nursery pointer, which is already an [i64*]. *)
Definition gep_at (base : Lexp) (n : N) : Lexp :=
  OP_GetElementPtr val_ty (ptr_ty, base) [(val_ty, lit (N.to_nat n))].

(** GEP of [thread_info] field [n] (a two-index struct GEP: [0, n], i32
    indices).  Yields the address of the field, e.g. [&tinfo->alloc]. *)
Definition gep_tinfo (n : nat) : Lexp :=
  OP_GetElementPtr tinfo_struct_ty
    (tinfo_ty, etinfo)
    [(TYPE_I 32%positive, lit 0); (TYPE_I 32%positive, lit n)].

(** Deterministic fresh SSA temporaries for the alloc/call lowering.  Real ANF
    variables serialise as [Raw (Zpos v)]; generated temporaries use [Raw (Zneg
    _)], so the two name-spaces never collide.  Keyed off a seed [positive] times
    sixteen, giving fifteen disjoint slots per seed — enough for the GC-safepoint
    block's several temporaries. *)
Definition ntmp (seed : positive) (k : positive) : raw_id :=
  Raw (Zneg (seed * 16 + k)).

(** Call argument list: [%tinfo] first, then the value args [ys].  Args that are
    themselves top-level functions ([fs]) are passed as global code pointers. *)
Definition call_args (fs : list positive) (env : nenv) (ys : list var)
  : list (texp typ * list param_attr) :=
  ((tinfo_ty, etinfo), @nil param_attr)
  :: map (fun y => ((val_ty, gvar fs env y), @nil param_attr)) ys.

(** Store [ys] into consecutive fields of the value pointer [vp].  A stored
    field that is a top-level function ([fs]) is its global code pointer — this
    is how a closure record captures its function. *)
Fixpoint store_fields (fs : list positive) (env : nenv) (vp : Lexp) (i : N) (ys : list var) : Lcode :=
  match ys with
  | [] => []
  | y :: ys' =>
      (IVoid (Z.of_N i), INSTR_Store (val_ty, gvar fs env y) (ptr_ty, gep_at vp i) [], [])
        :: store_fields fs env vp (N.succ i) ys'
  end.

(** ** ctor-env interface (the v1 placeholders' replacement)

    v1 could not tell a nullary from a boxed tag nor recover a constructor's
    real ordinal, so it emitted [lit 0] / [Pos.to_nat t].  v2 takes two pure
    functions supplied by the caller (the constructor environment of the
    LambdaANF program):

      [get_ord t]   — the constructor's ordinal within its inductive (the value
                      an unboxed constructor carries, and the low 10 bits of a
                      boxed block's header / the [switch] key);
      [get_arity t] — the constructor's arity = the boxed block's word size
                      (0 ⇒ the constructor is unboxed). *)

(** Object header word: [(get_arity t << 10) | get_ord t]. *)
Definition header_word (get_ord get_arity : ctor_tag -> N) (t : ctor_tag) : Lexp :=
  lit (Nat.lor (Nat.shiftl (N.to_nat (get_arity t)) 10) (N.to_nat (get_ord t))).

(** Load the header word of a boxed value: [load (inttoptr (y - 8))]. *)
Definition load_header (env : nenv) (y : var) : Linstr :=
  INSTR_Load val_ty
    (ptr_ty, OP_Conversion Inttoptr val_ty
       (OP_IBinop (Sub false false) val_ty (nvar env y) (lit 8)) ptr_ty) [].

(** ** Block plumbing *)

(** Prepend straight-line [extra] code to the head block of [blks].  The
    straight-line constructs ([Eproj], [Econstr]-unboxed, [Eprim], [Eprim_val],
    [Eletapp]) emit no new basic block: they cons their instructions onto the
    entry of their continuation's CFG. *)
Definition prepend_code (extra : Lcode) (blks : list (block typ)) : list (block typ) :=
  match blks with
  | b :: rest =>
      mk_block (blk_id b) (blk_phis b) ((extra ++ blk_code b)%list) (blk_term b) (blk_comments b)
        :: rest
  | [] => []
  end.

(** ** GC-safepoint shadow-stack helpers (CertiGC root registration)

    A moving collector relocates objects, so at a GC point every live value must
    be reachable as a root through the [tinfo->fp] frame chain, and reloaded
    afterward.  Per boxed [Econstr] safepoint we [alloca] a [roots] array and a
    [stack_frame] in the (dominating, once-per-activation) check block, spill the
    live set on the collect path, link the frame, collect, reload, pop, and merge
    the original vs.\ reloaded values with a phi at the alloc block.  The
    continuation then reads the dominating phi results.  Fresh names live in a
    high [Zneg] range keyed off the safepoint seed, disjoint from ANF variables
    ([Zpos]), the [ntmp] temporaries ([seed*16+k]) and the flattener ([16*c]). *)
Definition ssname (seed : positive) (k : nat) : raw_id :=
  Raw (Zneg (seed * 4294967296 + Pos.of_succ_nat k)).

(** [stack_frame] = [{ value* next; value* root; stack_frame* prev }]. *)
Definition frame_ty : typ := TYPE_Struct [tinfo_ty; tinfo_ty; tinfo_ty].

(** [&base[i]] into an [alloca]'d array of type [arr_ty] (two-index GEP). *)
Definition gep_arr (arr_ty : typ) (base : Lexp) (i : nat) : Lexp :=
  OP_GetElementPtr arr_ty (tinfo_ty, base)
    [(TYPE_I 32%positive, lit 0); (val_ty, lit i)].

(** [&base->field j] of an [alloca]'d struct of type [sty]. *)
Definition gep_struct (sty : typ) (base : Lexp) (j : nat) : Lexp :=
  OP_GetElementPtr sty (tinfo_ty, base)
    [(TYPE_I 32%positive, lit 0); (TYPE_I 32%positive, lit j)].

(** Spill each live root [r] to [roots[i]] before the collector runs. *)
Fixpoint spill_code (env : nenv) (rootsp : Lexp) (arr_ty : typ) (i : nat)
                    (rs : list var) : Lcode :=
  match rs with
  | [] => []
  | r :: rs' =>
      (IVoid 0%Z, INSTR_Store (val_ty, nvar env r) (tinfo_ty, gep_arr arr_ty rootsp i) [], [])
        :: spill_code env rootsp arr_ty (S i) rs'
  end.

(** Reload each root from [roots[i]] after the collector, into [ssname seed
    (100+i)] (values may have moved). *)
Fixpoint reload_code (seed : positive) (rootsp : Lexp) (arr_ty : typ) (i : nat)
                     (rs : list var) : Lcode :=
  match rs with
  | [] => []
  | _ :: rs' =>
      (IId (ssname seed (1000 + i)), INSTR_Load val_ty (tinfo_ty, gep_arr arr_ty rootsp i) [], [])
        :: reload_code seed rootsp arr_ty (S i) rs'
  end.

(** Phi at the alloc block: for each root, pick the original value (direct
    [check] path, no GC) or the reloaded value (via [gc]).  Result name is
    [ssname seed (200+i)]; the continuation is compiled to read these. *)
Fixpoint phi_list (env : nenv) (seed : positive) (chk gc : block_id) (i : nat)
                  (rs : list var) : list (local_id * phi typ * list (metadata typ)) :=
  match rs with
  | [] => []
  | r :: rs' =>
      (ssname seed (2000 + i),
       Phi val_ty [(chk, nvar env r);
                   (gc, EXP_Ident (ID_Local (ssname seed (1000 + i))))], [])
        :: phi_list env seed chk gc (S i) rs'
  end.

(** The environment the continuation is compiled under: each root maps to its
    phi result. *)
Definition safepoint_env (env : nenv) (seed : positive) (roots : list var) : nenv :=
  env_set_list env roots (map (fun i => ssname seed (2000 + i)) (seq 0 (List.length roots))).

(** ** Chunk allocation (safepoint batching)

    A *chunk* is a maximal straight-line run of allocations with no intervening
    GC-triggering construct (call, allocating prim) or branch.  [chunk_words e]
    sums the boxed-[Econstr] sizes along the spine of [e] until the chunk ends, so
    one limit-check at the chunk head can cover them all — matching the \C{}
    backend's per-function [nalloc] and removing the per-allocation check/spill
    overhead.  A single [garbage_collect] with [nalloc = chunk_words] guarantees
    the whole chunk fits (CertiGC's contract), so the allocations inside run
    unchecked. *)
Fixpoint chunk_words (e : cps.exp) : N :=
  match e with
  | Econstr _ _ ys e' =>
      match ys with
      | [] => chunk_words e'                       (* unboxed: no allocation *)
      | _  => (1 + N.of_nat (List.length ys) + chunk_words e')%N
      end
  | Eproj _ _ _ _ e' => chunk_words e'
  | Eprim_val _ _ e'  => chunk_words e'
  | Efun _ e'         => chunk_words e'
  | _ => 0%N   (* Ecase / Eapp / Eletapp / Eprim / Ehalt end the chunk *)
  end.

(** ** Per-[exp] block-list code generation.

    [translate_cfg get_ord get_arity e fresh] returns [(blocks, fresh')] where
    [blocks] is a non-empty CFG whose FIRST element is the entry block, and
    [fresh] / [fresh'] thread a monotone block-label / SSA supply.  Terminal
    constructs ([Ehalt], [Eapp]) and control-flow constructs ([Ecase],
    [Econstr]-boxed) allocate their own block(s); straight-line constructs
    cons onto their continuation's entry via [prepend_code].  A single
    [Fixpoint] with a nested [fix] over the [Ecase] arms keeps the traversal
    structurally recursive (guarded). *)

Fixpoint translate_cfg (get_ord get_arity : ctor_tag -> N)
                       (prim_of : positive -> option (string * bool))
                       (fs : list positive)
                       (env : nenv) (chunk : N) (e : cps.exp) (fresh : positive) {struct e}
  : list (block typ) * positive :=
  match e with
  | Ehalt x =>
      ( [ mk_block (Anon (Zpos fresh)) []
            []
            (IVoid 1%Z, TERM_Ret (val_ty, gvar fs env x), []) None ],
        Pos.succ fresh )
  | Eproj x _ n y e' =>
      let '(blks, f') := translate_cfg get_ord get_arity prim_of fs env chunk e' fresh in
      ( prepend_code [ (IId (Raw (Zpos x)), load_field env y n, []) ] blks, f' )
  | Econstr x t ys e' =>
      match ys with
      | [] =>
          (* Nullary constructor: unboxed [x := Val_long(get_ord t)]. *)
          let '(blks, f0) := translate_cfg get_ord get_arity prim_of fs env chunk e' fresh in
          ( prepend_code
              [ (IId (Raw (Zpos x)),
                 INSTR_Op (val_long (lit (N.to_nat (get_ord t)))), []) ]
              blks, f0 )
      | _ =>
          (* Boxed allocation, with safepoint BATCHING.  If the enclosing chunk
             head already limit-checked and GC'd for [chunk >= nwords] words, this
             block allocates UNCHECKED (a member); otherwise it is the chunk HEAD
             and checks once for the whole chunk ([cw = chunk_words]), registers
             roots + collects if needed, then allocates, compiling the continuation
             with [chunk = cw - nwords] so its members run unchecked.  One
             [garbage_collect] with [nalloc = cw] covers the chunk — CertiGC's
             contract (see [CertiGC_Contract]). *)
          let nwords    := (1 + N.of_nat (List.length ys))%N in
          let allocp    := gep_tinfo 0 in
          if N.leb nwords chunk then
            (* MEMBER: unchecked straight-line allocation; no roots (no GC here). *)
            let '(blks, f') :=
              translate_cfg get_ord get_arity prim_of fs env (chunk - nwords)%N e' (Pos.succ fresh) in
            let a0n  := ssname fresh 7 in let a0e := EXP_Ident (ID_Local a0n) in
            let vpn  := ssname fresh 8 in let vpe := EXP_Ident (ID_Local vpn) in
            let naen := ssname fresh 9 in
            let alloc_code :=
              ( (IId a0n, INSTR_Load ptr_ty (ptr_ty, allocp) [], [])
                :: (IVoid 6%Z, INSTR_Store (val_ty, header_word get_ord get_arity t)
                      (ptr_ty, gep_at a0e 0) [], [])
                :: (IId vpn, INSTR_Op (gep_at a0e 1), [])
                :: store_fields fs env vpe 0 ys
                ++ (IId (Raw (Zpos x)), INSTR_Op (OP_Conversion Ptrtoint ptr_ty vpe val_ty), [])
                :: (IId naen, INSTR_Op (gep_at a0e nwords), [])
                :: (IVoid 7%Z, INSTR_Store (ptr_ty, EXP_Ident (ID_Local naen)) (ptr_ty, allocp) [], [])
                :: [] )%list in
            ( prepend_code alloc_code blks, f' )
          else
          (* HEAD: check + register roots + [garbage_collect] for the whole chunk. *)
          let cw        := (nwords + chunk_words e')%N in
          let cwn       := N.to_nat cw in
          let fv        := PS.elements (exp_fv e') in
          let roots     := List.filter (fun v => negb (is_fun fs v))
                             (nodup Pos.eq_dec (List.remove Pos.eq_dec x fv ++ ys)) in
          let nr        := List.length roots in
          let arr_ty    := TYPE_Array (N.of_nat nr) val_ty in
          let env''     := safepoint_env env fresh roots in
          let '(blks, f0) := translate_cfg get_ord get_arity prim_of fs env'' (cw - nwords)%N e' (Pos.succ fresh) in
          let klbl      := match blks with b :: _ => blk_id b | [] => Anon (Zpos f0) end in
          let check_lbl := Anon (Zpos f0) in
          let gc_lbl    := Anon (Zpos (Pos.succ f0)) in
          let alloc_lbl := Anon (Zpos (Pos.succ (Pos.succ f0))) in
          let f'        := Pos.succ (Pos.succ (Pos.succ f0)) in
          let nwn       := N.to_nat nwords in
          let limitp    := gep_tinfo 1 in
          let fpp       := gep_tinfo 4 in
          let nallocp   := gep_tinfo 5 in
          let rootsp    := ssname fresh 1 in  let rootse := EXP_Ident (ID_Local rootsp) in
          let framep    := ssname fresh 2 in  let framee := EXP_Ident (ID_Local framep) in
          let allocRn   := ssname fresh 3 in  let allocR := EXP_Ident (ID_Local allocRn) in
          let limitRn   := ssname fresh 4 in  let limitR := EXP_Ident (ID_Local limitRn) in
          let availRn   := ssname fresh 5 in  let availR := EXP_Ident (ID_Local availRn) in
          let cmpRn     := ssname fresh 6 in
          let a0n       := ssname fresh 7 in  let a0e    := EXP_Ident (ID_Local a0n) in
          let vpn       := ssname fresh 8 in  let vpe    := EXP_Ident (ID_Local vpn) in
          let naen      := ssname fresh 9 in
          let prevRn    := ssname fresh 10 in let prevR  := EXP_Ident (ID_Local prevRn) in
          let check_blk :=
            mk_block check_lbl []
              [ (IId rootsp, INSTR_Alloca arr_ty [], []);
                (IId framep, INSTR_Alloca frame_ty [], []);
                (IId allocRn, INSTR_Load ptr_ty (ptr_ty, allocp) [], []);
                (IId limitRn, INSTR_Load ptr_ty (ptr_ty, limitp) [], []);
                (IId availRn,
                 INSTR_Op (OP_IBinop (Sub false false) val_ty
                            (OP_Conversion Ptrtoint ptr_ty limitR val_ty)
                            (OP_Conversion Ptrtoint ptr_ty allocR val_ty)), []);
                (IId cmpRn,
                 INSTR_Op (OP_ICmp false Uge val_ty availR (lit (8 * cwn))), []) ]
              (IVoid 2%Z,
               TERM_Br (TYPE_I 1%positive, EXP_Ident (ID_Local cmpRn)) alloc_lbl gc_lbl, [])
              None in
          let gc_blk :=
            mk_block gc_lbl []
              (( spill_code env rootse arr_ty 0 roots
                ++ [ (IVoid 0%Z, INSTR_Store (tinfo_ty, gep_arr arr_ty rootse nr)
                        (tinfo_ty, gep_struct frame_ty framee 0) [], []);
                     (IVoid 0%Z, INSTR_Store (tinfo_ty, gep_arr arr_ty rootse 0)
                        (tinfo_ty, gep_struct frame_ty framee 1) [], []);
                     (IId prevRn, INSTR_Load tinfo_ty (tinfo_ty, fpp) [], []);
                     (IVoid 0%Z, INSTR_Store (tinfo_ty, prevR)
                        (tinfo_ty, gep_struct frame_ty framee 2) [], []);
                     (IVoid 0%Z, INSTR_Store (tinfo_ty, framee) (tinfo_ty, fpp) [], []);
                     (IVoid 0%Z, INSTR_Store (val_ty, lit cwn) (ptr_ty, nallocp) [], []);
                     (IVoid 0%Z,
                      INSTR_Call (TYPE_Void, EXP_Ident (ID_Global (Name "garbage_collect")))
                        [ ((tinfo_ty, etinfo), @nil param_attr) ] [] [], []) ]
                ++ reload_code fresh rootse arr_ty 0 roots
                ++ [ (IVoid 0%Z, INSTR_Store (tinfo_ty, prevR) (tinfo_ty, fpp) [], []) ] )%list)
              (IVoid 5%Z, TERM_Br_1 alloc_lbl, [])
              None in
          let alloc_blk :=
            mk_block alloc_lbl
              (phi_list env fresh check_lbl gc_lbl 0 roots)
              (( (IId a0n, INSTR_Load ptr_ty (ptr_ty, allocp) [], [])
                :: (IVoid 6%Z,
                    INSTR_Store (val_ty, header_word get_ord get_arity t)
                      (ptr_ty, gep_at a0e 0) [], [])
                :: (IId vpn, INSTR_Op (gep_at a0e 1), [])
                :: store_fields fs env'' vpe 0 ys
                ++ (IId (Raw (Zpos x)),
                    INSTR_Op (OP_Conversion Ptrtoint ptr_ty vpe val_ty), [])
                :: (IId naen, INSTR_Op (gep_at a0e nwords), [])
                :: (IVoid 7%Z, INSTR_Store (ptr_ty, EXP_Ident (ID_Local naen)) (ptr_ty, allocp) [], [])
                :: [] )%list)
              (IVoid 8%Z, TERM_Br_1 klbl, [])
              None in
          ( (check_blk :: gc_blk :: alloc_blk :: blks)%list, f' )
      end
  | Eprim x p ys e' =>
      (* Primitive operator [p] resolves through [prim_of] to its runtime target
         name and whether it allocates.  A non-allocating int63 op (add, sub, mul,
         div, comparisons, bitwise, shifts) is a direct call to the [prim_int63_*]
         C runtime on the tagged words — the ABI is byte-identical.  Allocating
         prims (carry/pair results) additionally take [tinfo]. *)
      let '(blks, f') := translate_cfg get_ord get_arity prim_of fs env 0%N e' fresh in
      let args := map (fun y => ((val_ty, gvar fs env y), @nil param_attr)) ys in
      let call :=
        match prim_of p with
        | Some (name, false) =>
            INSTR_Call (val_ty, EXP_Ident (ID_Global (Name name))) args [] []
        | Some (name, true) =>
            (* NOTE: allocating prims (addc/mulc/diveucl, …) also need a GC
               safepoint (as for [Eletapp]); they are rare and unused by the
               current benchmarks, so only the [tinfo] argument is threaded here. *)
            INSTR_Call (val_ty, EXP_Ident (ID_Global (Name name)))
              (((tinfo_ty, etinfo), @nil param_attr) :: args) [] []
        | None =>
            INSTR_Call (val_ty, EXP_Ident (ID_Global (Name "certirocq_prim"))) args [] []
        end in
      ( prepend_code [ (IId (Raw (Zpos x)), call, []) ] blks, f' )
  | Eprim_val x pv e' =>
      let '(blks, f') := translate_cfg get_ord get_arity prim_of fs env chunk e' fresh in
      (* Materialise the primitive literal.  A primitive int [n] becomes the
         unboxed word [Val_long n = (n<<1)|1]; non-int primitives (float/string)
         are not represented at this ABI layer and fall back to unboxed 0. *)
      let vexp := match prim_val_Z pv with
                  | Some z => val_long (litZ z)
                  | None   => val_long (lit 0)
                  end in
      ( prepend_code
          [ (IId (Raw (Zpos x)), INSTR_Op vexp, []) ] blks, f' )
  | Eletapp x f _ ys e' =>
      (* Non-tail call — a GC SAFEPOINT: the callee may collect, so the caller's
         values live across the call ([FV(e') \ {x}], functions excluded) are
         registered on the shadow stack around it.  No limit-check/phi is needed
         (the call always runs; we always reload afterward, which is a no-op if no
         collection moved anything).  [f]/[ys] use the pre-call [env]; the
         continuation is compiled under [env''] mapping each root to its reloaded
         name.  [fresh] is reserved as the [ssname] seed (continuation from
         [fresh+1]). *)
      let fv     := PS.elements (exp_fv e') in
      let roots  := List.filter (fun v => negb (is_fun fs v))
                      (nodup Pos.eq_dec (List.remove Pos.eq_dec x fv)) in
      let nr     := List.length roots in
      let arr_ty := TYPE_Array (N.of_nat nr) val_ty in
      let env''  := env_set_list env roots
                      (map (fun i => ssname fresh (1000 + i)) (seq 0 nr)) in
      let '(blks, f') := translate_cfg get_ord get_arity prim_of fs env'' 0%N e' (Pos.succ fresh) in
      let fpp    := gep_tinfo 4 in
      let rootsp := ssname fresh 1 in let rootse := EXP_Ident (ID_Local rootsp) in
      let framep := ssname fresh 2 in let framee := EXP_Ident (ID_Local framep) in
      let prevRn := ssname fresh 3 in let prevR  := EXP_Ident (ID_Local prevRn) in
      let setup :=
        ( (IId rootsp, INSTR_Alloca arr_ty [], [])
          :: (IId framep, INSTR_Alloca frame_ty [], [])
          :: spill_code env rootse arr_ty 0 roots
          ++ [ (IVoid 0%Z, INSTR_Store (tinfo_ty, gep_arr arr_ty rootse nr)
                  (tinfo_ty, gep_struct frame_ty framee 0) [], []);
               (IVoid 0%Z, INSTR_Store (tinfo_ty, gep_arr arr_ty rootse 0)
                  (tinfo_ty, gep_struct frame_ty framee 1) [], []);
               (IId prevRn, INSTR_Load tinfo_ty (tinfo_ty, fpp) [], []);
               (IVoid 0%Z, INSTR_Store (tinfo_ty, prevR)
                  (tinfo_ty, gep_struct frame_ty framee 2) [], []);
               (IVoid 0%Z, INSTR_Store (tinfo_ty, framee) (tinfo_ty, fpp) [], []);
               (IId (Raw (Zpos x)),
                INSTR_Call (val_ty, gcallee fs env f) (call_args fs env ys) [] [], []) ]
          ++ reload_code fresh rootse arr_ty 0 roots
          ++ [ (IVoid 0%Z, INSTR_Store (tinfo_ty, prevR) (tinfo_ty, fpp) [], []) ] )%list in
      ( prepend_code setup blks, f' )
  | Efun _ e' =>
      (* Post-pipeline the fundefs are flat top-level closed functions, lifted
         to their own [define]s by [compile_prog]; a function *body* just
         translates its continuation. *)
      translate_cfg get_ord get_arity prim_of fs env 0%N e' fresh
  | Eapp f _ ys =>
      (* Tail call.  [f] is a top-level function (global) or a local code
         pointer; [gcallee] resolves which.  Return its result (tail position). *)
      let r := ntmp fresh 1 in
      ( [ mk_block (Anon (Zpos fresh)) []
            [ (IId r, INSTR_Call (val_ty, gcallee fs env f) (call_args fs env ys) [] [], []) ]
            (IVoid 1%Z, TERM_Ret (val_ty, EXP_Ident (ID_Local r)), []) None ],
        Pos.succ fresh )
  | Ecase y arms =>
      (* Real multi-block dispatch (folds in v1's [translate_case_cfg]):
           - [test]   : [Is_block y] ? [boxed] : [unboxed];
           - [unboxed]: [switch (Long_val y)] over the nullary (arity-0) arms;
           - [boxed]  : load header, mask 10-bit tag, [switch] over the boxed arms;
           - one block(-chain) per arm, keyed by [get_ord t], partitioned by
             [get_arity t] into the unboxed vs boxed switch. *)
      let fix arm_loop (arms : list (ctor_tag * cps.exp)) (fr : positive)
            {struct arms}
            : list (block typ) * list (N * (tint_literal * block_id)) * positive :=
        match arms with
        | [] => ([], [], fr)
        | (t, ae) :: rest =>
            let '(ablks, fr1) := translate_cfg get_ord get_arity prim_of fs env 0%N ae fr in
            let lbl := match ablks with b :: _ => blk_id b | [] => Anon (Zpos fr) end in
            let '(rblks, redges, fr2) := arm_loop rest fr1 in
            ( (ablks ++ rblks)%list,
              (get_arity t,
               (TInt_Literal 64 (Nat.to_num_int (N.to_nat (get_ord t))), lbl)) :: redges,
              fr2 )
        end in
      let '(arm_blks, aedges, f1) := arm_loop arms fresh in
      let unboxed_edges := map snd (filter (fun ae => N.eqb (fst ae) 0) aedges) in
      let boxed_edges   := map snd (filter (fun ae => negb (N.eqb (fst ae) 0)) aedges) in
      let boxed_lbl   := Anon (Zpos f1) in
      let unboxed_lbl := Anon (Zpos (Pos.succ f1)) in
      let test_lbl    := Anon (Zpos (Pos.succ (Pos.succ f1))) in
      let default_lbl :=
        match arm_blks with b :: _ => blk_id b | [] => test_lbl end in
      let test_blk :=
        mk_block test_lbl [] []
          (IVoid 3%Z, TERM_Br (TYPE_I 1%positive, is_block (nvar env y)) boxed_lbl unboxed_lbl, [])
          None in
      let unboxed_blk :=
        mk_block unboxed_lbl [] []
          (IVoid 4%Z, TERM_Switch (val_ty, long_val (nvar env y)) default_lbl unboxed_edges, [])
          None in
      let boxed_blk :=
        mk_block boxed_lbl []
          [ (IId (ntmp f1 1), load_header env y, []) ]
          (IVoid 5%Z,
           TERM_Switch
             (val_ty, OP_IBinop And val_ty (EXP_Ident (ID_Local (ntmp f1 1))) (lit 1023))
             default_lbl boxed_edges, [])
          None in
      ( (test_blk :: unboxed_blk :: boxed_blk :: arm_blks)%list,
        Pos.succ (Pos.succ (Pos.succ f1)) )
  end.

(** ** A whole [define] for one function

    [define i64 @name(ptr %tinfo, i64 %a0, ...) { entry: ... ; rest... }].
    The CFG body form [block typ * list (block typ)] (entry block + the rest) is
    exactly what [ShowAST] renders; [translate_cfg] returns the full block list,
    of which the head is the entry. *)

Definition mk_fun (get_ord get_arity : ctor_tag -> N)
                  (prim_of : positive -> option (string * bool)) (fs : list positive)
                  (name : function_id) (params : list var) (body : cps.exp)
  : definition typ (block typ * list (block typ)) :=
  let '(blks, _) := translate_cfg get_ord get_arity prim_of fs base_env 0%N body 1%positive in
  let entry :=
    match blks with
    | b :: _ => b
    | [] => mk_block (Name "entry") [] [] (IVoid 0%Z, TERM_Unreachable, []) None
    end in
  let rest := match blks with _ :: r => r | [] => [] end in
  let nargs := S (List.length params) in
  let decl :=
    @mk_declaration typ
      name
      (TYPE_Function val_ty (tinfo_ty :: map (fun _ => val_ty) params) false)
      ([], List.repeat (@nil param_attr) nargs)
      []
      [] in
  @mk_definition typ (block typ * list (block typ))
    decl
    (Name "tinfo" :: map (fun v => Raw (Zpos v)) params)
    (entry, rest).

(** ** Whole-program compilation ([Efun] lifting)

    After the pipeline the program is [Efun <flat top-level fundefs> <main>]; each
    [Fcons] becomes its own top-level [define], and [main] a nullary entry. *)

(** The positives naming the top-level functions of a [fundefs] block — the set
    [gvar] treats as global code pointers. *)
Fixpoint fun_ids (fds : fundefs) : list positive :=
  match fds with
  | Fnil => []
  | Fcons f _ _ _ rest => f :: fun_ids rest
  end.

Fixpoint funs_to_defs (get_ord get_arity : ctor_tag -> N)
                      (prim_of : positive -> option (string * bool)) (fs : list positive)
                      (fds : fundefs)
  : list (definition typ (block typ * list (block typ))) :=
  match fds with
  | Fnil => []
  | Fcons f _ ys body rest =>
      mk_fun get_ord get_arity prim_of fs (Anon (Zpos f)) ys body
        :: funs_to_defs get_ord get_arity prim_of fs rest
  end.

Definition compile_prog (get_ord get_arity : ctor_tag -> N)
                        (prim_of : positive -> option (string * bool)) (e : cps.exp)
  : list (toplevel_entity typ (block typ * list (block typ))) :=
  match e with
  | Efun fds main =>
      let fs := fun_ids fds in
      (map (fun d => TLE_Definition d) (funs_to_defs get_ord get_arity prim_of fs fds)
      ++ [ TLE_Definition (mk_fun get_ord get_arity prim_of fs (Name "certirocq_main") [] main) ])%list
  | _ =>
      [ TLE_Definition (mk_fun get_ord get_arity prim_of [] (Name "certirocq_main") [] e) ]
  end.

(** ** Smoke tests *)

(** A concrete demo ctor-env: ordinal and arity both [tag - 1] (so tag 1 is a
    nullary/unboxed constructor with ordinal 0, tag 2 a unary boxed one, ...). *)
Definition demo_ord   (t : ctor_tag) : N := Pos.pred_N t.
Definition demo_arity (t : ctor_tag) : N := Pos.pred_N t.

(** Identity-in-the-answer function [fun x => halt x]. *)
Definition sample_id : definition typ (block typ * list (block typ)) :=
  mk_fun demo_ord demo_arity (fun _ => None) [] (Name "certirocq_id") [1%positive] (Ehalt 1%positive).

(** Allocate [Econstr x c [a;b]] (boxed, with the GC safepoint) then tail-call
    it — exercises the boxed-alloc CFG and the direct indirect tail call. *)
Definition sample_constr_app : definition typ (block typ * list (block typ)) :=
  mk_fun demo_ord demo_arity (fun _ => None) [] (Name "certirocq_pair_apply")
    [1%positive; 2%positive; 3%positive]
    (Econstr 4%positive 2%positive [1%positive; 2%positive]
       (Eapp 3%positive 1%positive [4%positive])).

(** The [Ecase] dispatch CFG on scrutinee [%1] with a nullary (tag 1) and a
    boxed (tag 2) arm — exercises the arity partition. *)
Definition sample_case_blocks : list (block typ) * positive :=
  translate_cfg demo_ord demo_arity (fun _ => None) [] base_env 0%N
    (Ecase 1%positive
       [(1%positive, Ehalt 2%positive); (2%positive, Ehalt 3%positive)])
    10%positive.

(** Whole-program smoke test: one lifted function plus [main]. *)
Definition sample_prog : list (toplevel_entity typ (block typ * list (block typ))) :=
  compile_prog demo_ord demo_arity (fun _ => None)
    (Efun (Fcons 10%positive 1%positive [1%positive] (Ehalt 1%positive) Fnil)
       (Econstr 4%positive 1%positive [] (Ehalt 4%positive))).
