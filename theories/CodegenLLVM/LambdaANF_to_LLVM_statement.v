(** * Correctness statement for the LambdaANF -> LLVM (Vellvm VIR) backend

    End-to-end correctness of the code the pipeline emits,
    [flatten_prog (compile_prog ...)], against Vellvm's executable semantics
    [interp_mcfg] with the concrete memory model and 64-bit pointers.

    There are two hypotheses besides the source evaluation [bstep_e]: the
    runtime contract [runtime_correct] (the garbage collector and the
    [thread_info] set-up, linked as Vellvm library functions acting on
    Vellvm's memory), and the source-side restrictions [llvm_restricted]
    (closed program with unique bindings, no [Eprim], no nested [Efun],
    bounds on constructor ordinals, arities, projection indices and
    allocation chunks).  The theorem is about terminating source runs;
    divergence is not covered.

    The statement is [LambdaANF_to_LLVM_correct_statement] at the end of this
    file.  It is proved as [LambdaANF_to_LLVM_correct] in [LLVM_sim_exp.v]. *)

From Stdlib Require Import ZArith NArith List Lia String.
From ITree Require Import ITree Eq.Eqit.
From ExtLib Require Import Structures.Monads.

From CertiRocq.LambdaANF Require Import term term_util eval identifiers.
From CertiRocq.Common Require Import AstCommon.
From CertiRocq.CodegenLLVM Require Import LambdaANF_to_LLVM Flatten.

From Vellvm Require Import
  Utils Syntax Params
  Interfaces.Memory Implementations.Memory
  Implementations.ParamsV Implementations.IPtrFinite
  Semantics.DynamicValues Semantics.LLVMEvents Semantics.Denotation
  Semantics.Libraries Semantics.InterpretationStack Semantics.TopLevel
  Handlers.

Import ListNotations.
Import MonadNotation.
Open Scope monad_scope.
Open Scope Z_scope.

Notation LLprog := (list (toplevel_entity typ (LLVMAst.block typ * list (LLVMAst.block typ)))) (only parsing).

(** Vellvm's concrete memory model with 64-bit pointers. *)
#[global] Instance Pa64 : Params := @ParamsV IP64Bit IP64BitTheory.
#[global] Existing Instance MemoryModelPrimitivesV.

(* ------------------------------------------------------------------ *)
(** ** What the pipeline emits *)

Definition ord_of (cenv : ctor_env) (t : ctor_tag) : N :=
  match M.get t cenv with Some info => ctor_ordinal info | None => 0%N end.
Definition arity_of (cenv : ctor_env) (t : ctor_tag) : N :=
  match M.get t cenv with Some info => ctor_arity info | None => 0%N end.

(** Same as [LambdaANF_to_LLVM_Wrapper] in [CodegenLLVM/toplevel.v]. *)
Definition emitted (cenv : ctor_env) (prim_of : positive -> option (string * bool))
           (e : term.exp) : LLprog :=
  flatten_prog (compile_prog (ord_of cenv) (arity_of cenv) prim_of e).

(* ------------------------------------------------------------------ *)
(** ** Reading Vellvm memory *)

(** [m] runs from memory state [st] to [st'] returning [x], without choices
    or errors (what Vellvm's [memM_interp] does on such [m]). *)
Inductive memS_runs {X} : state -> memM X -> state -> X -> Prop :=
| MR_ret st x : memS_runs st (Mret x) st x
| MR_get st k st' x : memS_runs st (k st) st' x -> memS_runs st (Mget k) st' x
| MR_put st st0 k st' x : memS_runs st0 (k tt) st' x -> memS_runs st (Mput st0 k) st' x.

Definition memS_returns {X} (st : state) (m : memM X) (x : X) : Prop :=
  exists st', memS_runs st m st' x.

Definition I64 (z : Z) : dvalue := DVALUE_Base (DVALUE_I 64 (@Integers.repr 64 z)).

Definition reads_word (st : state) (p : ptr) (z : Z) : Prop :=
  memS_returns st (read_dvalue (DTYPE_I 64) p) (I64 z).

(** Pointers read from memory carry wildcard provenance: only the address
    is meaningful. *)
Definition reads_ptr (st : state) (p q : ptr) : Prop :=
  memS_returns st (read_dvalue DTYPE_Pointer p) (DVALUE_Base (DVALUE_Pointer q)).

Definition writable_word (st : state) (p : ptr) : Prop :=
  forall z, exists st', memS_runs st (write_dvalue (DTYPE_I 64) p (I64 z)) st' tt
                   /\ reads_word st' p z.

(** [p + off] bytes, keeping [p]'s provenance. *)
Definition ptr_off (p : ptr) (off : Z) (q : ptr) : Prop :=
  int_to_ptr (ptr_to_int p + off) (ptr_provenance p) = EOU.raise_ret q.

Definition mem_of (st : state) : memory := Memory_stack_memory (state_memory_stack st).
Definition heap_of (st : state) : Heap := Memory_stack_heap (state_memory_stack st).
Definition frames_of (st : state) : Framestack := Memory_stack_frame_stack (state_memory_stack st).

(** [a] is an address inside a malloc'd (heap, not stack) block. *)
Definition in_heap (st : state) (a : Z) : Prop :=
  exists root blk, IntMaps.lookup root (heap_of st) = Some blk /\ In a (map ptr_to_int blk).

(** [st2] has the same bytes as [st] at the heap addresses of [st], except
    possibly at the addresses in [S].  Stack memory is unconstrained. *)
Definition heap_bytes_agree_except (st st2 : state) (S : Z -> Prop) : Prop :=
  forall a, in_heap st a -> ~ S a -> IntMaps.lookup a (mem_of st2) = IntMaps.lookup a (mem_of st).

(** In addition, the set of heap blocks is the same. *)
Definition heap_agree_except (st st2 : state) (S : Z -> Prop) : Prop :=
  heap_of st2 = heap_of st /\ heap_bytes_agree_except st st2 S.

(* ------------------------------------------------------------------ *)
(** ** Value representation (the C runtime's ABI, [values.h])

    - nullary constructor: unboxed word [ord * 2 + 1];
    - n-ary constructor: a word-aligned pointer [p] to the first field,
      header [arity << 10 | ord] at [p - 8], field [i] at [p + 8 i]
      (the emitted code tells boxed from unboxed by the low bit, so a boxed
      object must not live at an odd address);
    - primitive integer [n]: unboxed word [n * 2 + 1];
    - function [f] of the top-level block [fds]: the address of [@f]. *)

Section Repr.
  Variable cenv : ctor_env.
  Variable fds : fundefs.            (* the program's top-level functions *)
  Variable genv : global_env.        (* Vellvm's global environment *)
  Variable st : state.               (* Vellvm's memory *)

  Inductive repr_val : term.val -> Z -> Prop :=
  | Repr_unboxed t :
      arity_of cenv t = 0%N ->
      repr_val (Vconstr t []) (Z.of_N (ord_of cenv t) * 2 + 1)
  | Repr_boxed t vs p ph :
      arity_of cenv t = N.of_nat (length vs) ->
      vs <> [] ->
      ptr_off p (-8) ph ->
      reads_word st ph (Z.of_N (arity_of cenv t) * 1024 + Z.of_N (ord_of cenv t)) ->
      repr_fields vs p 0 ->
      ptr_to_int p mod 8 = 0 ->
      repr_val (Vconstr t vs) (ptr_to_int p)
  | Repr_int n :
      repr_val (Vprim (existT _ primInt n)) (Uint63.to_Z n * 2 + 1)
  | Repr_fun rho f fp :
      RawIdMaps.rid_lookup (Anon (Zpos f)) genv
        = Some (DVALUE_Base (DVALUE_Pointer fp)) ->
      repr_val (Vfun rho fds f) (ptr_to_int fp)
  with repr_fields : list term.val -> ptr -> Z -> Prop :=
  | Repr_nil p off : repr_fields [] p off
  | Repr_cons v vs p off q z :
      ptr_off p off q ->
      reads_word st q z ->
      repr_val v z ->
      repr_fields vs p (off + 8) ->
      repr_fields (v :: vs) p off.
End Repr.

(* ------------------------------------------------------------------ *)
(** ** The runtime's state: [thread_info] and the shadow stack

    [thread_info] (gc_stack.h): alloc @0, limit @8, heap @16,
    args[1024] @24, fp @8216, nalloc @8224; 8232 bytes in all.
    A shadow-stack frame: { roots_end @0; roots_start @8; prev @16 }.
    A null pointer is any pointer whose address is 0. *)

Definition off_alloc  := 0%Z.
Definition off_limit  := 8%Z.
Definition off_fp     := 8216%Z.
Definition off_nalloc := 8224%Z.

(** The pointer stored in the field of [tinfo] at offset [off]. *)
Definition field (st : state) (tinfo : ptr) (off : Z) (q : ptr) : Prop :=
  exists a, ptr_off tinfo off a /\ reads_ptr st a q.

Definition field_addr (tinfo : ptr) (off : Z) (a : Z) : Prop :=
  ptr_to_int tinfo + off <= a < ptr_to_int tinfo + off + 8.

(** The root slots of one frame, from [s] up to [e]. *)
Inductive slots_from (st : state) (s e : ptr) : list ptr -> Prop :=
| Slots_done : ptr_to_int s = ptr_to_int e -> slots_from st s e []
| Slots_more s' rs :
    (ptr_to_int s < ptr_to_int e)%Z ->
    ptr_off s 8 s' -> slots_from st s' e rs -> slots_from st s e (s :: rs).

(** The root slots [rs] of the shadow stack starting at frame [fp]. *)
Inductive shadow_stack (st : state) : ptr -> list ptr -> Prop :=
| SS_nil f : ptr_to_int f = 0 -> shadow_stack st f []
| SS_frame f e s prev rs rs' :
    ptr_to_int f <> 0 ->
    reads_ptr st f e ->
    (exists a, ptr_off f 8 a /\ reads_ptr st a s) ->
    (exists a, ptr_off f 16 a /\ reads_ptr st a prev) ->
    slots_from st s e rs ->
    shadow_stack st prev rs' ->
    shadow_stack st f (rs ++ rs').

(** The nursery [alloc, limit) of [st]. *)
Definition nursery (st : state) (tinfo : ptr) (a : Z) : Prop :=
  exists alloc limit,
    field st tinfo off_alloc alloc /\ field st tinfo off_limit limit /\
    ptr_to_int alloc <= a < ptr_to_int limit.

(** The heap addresses the generated code writes: the nursery and the
    [alloc], [fp] and [nalloc] fields of [thread_info]. *)
Definition mutator_writes (st : state) (tinfo : ptr) (a : Z) : Prop :=
  nursery st tinfo a \/ field_addr tinfo off_alloc a \/
  field_addr tinfo off_fp a \/ field_addr tinfo off_nalloc a.

(** Heap objects live outside the nursery and outside [thread_info]. *)
Definition not_object (st : state) (tinfo : ptr) (a : Z) : Prop :=
  nursery st tinfo a \/ (ptr_to_int tinfo <= a < ptr_to_int tinfo + 8232).

(** A well-formed [thread_info]: its fields are writable heap words, [fp]
    heads a shadow stack, and the nursery is a writable heap region whose
    two ends are word-aligned. *)
Definition tinfo_ok (st : state) (tinfo : ptr) : Prop :=
  (forall off a, In off [off_alloc; off_limit; off_fp; off_nalloc] ->
     ptr_off tinfo off a -> writable_word st a /\
       forall b, field_addr tinfo off b -> in_heap st b) /\
  (exists fp rs, field st tinfo off_fp fp /\ shadow_stack st fp rs) /\
  exists alloc limit,
    field st tinfo off_alloc alloc /\ field st tinfo off_limit limit /\
    (ptr_to_int alloc mod 8 = 0)%Z /\
    ptr_to_int alloc <= ptr_to_int limit /\
    (forall a, ptr_to_int alloc <= a < ptr_to_int limit -> in_heap st a) /\
    (forall i q, 0 <= 8 * i < ptr_to_int limit - ptr_to_int alloc ->
       ptr_off alloc (8 * i) q -> writable_word st q) /\
    (ptr_to_int limit mod 8 = 0)%Z.

(** At least [n] free words in the nursery. *)
Definition room (st : state) (tinfo : ptr) (n : Z) : Prop :=
  exists alloc limit,
    field st tinfo off_alloc alloc /\ field st tinfo off_limit limit /\
    (ptr_to_int limit - ptr_to_int alloc >= 8 * n)%Z.

(** The roots [rs] hold words representing [vs], and these representations
    depend only on heap bytes outside the nursery and [thread_info]: they
    survive everything the generated code writes and the collector's run. *)
Definition roots_ok cenv fds genv (st : state) tinfo (rs : list ptr) (vs : list term.val) : Prop :=
  exists zs,
    Forall2 (reads_word st) rs zs /\
    forall st2, heap_bytes_agree_except st st2 (not_object st tinfo) ->
      Forall2 (repr_val cenv fds genv st2) vs zs.

(** Vellvm's memory has malloc'd heap blocks and [alloca]'d stack frames.
    [mem_ok_stmt]: every heap address is allocated and no stack-frame address
    is a heap address.  Vellvm's own memory operations preserve this; the
    runtime is asked to. *)
Fixpoint frames_ptrs_stmt (fs : Framestack) : list ptr :=
  match fs with
  | Singleton f => f
  | Snoc s f => (f ++ frames_ptrs_stmt s)%list
  end.

Definition in_frames_stmt (st : state) (a : Z) : Prop :=
  In a (map ptr_to_int (frames_ptrs_stmt (frames_of st))).

Definition mem_ok_stmt (st : state) : Prop :=
  (forall a, in_heap st a -> IntMaps.lookup a (mem_of st) <> None) /\
  (forall a, in_frames_stmt st a -> ~ in_heap st a).

(** The nursery and [thread_info] are distinct malloc'd objects. *)
Definition nursery_tinfo_disjoint_stmt (st : state) (tinfo : ptr) : Prop :=
  forall a, nursery st tinfo a -> ~ (ptr_to_int tinfo <= a < ptr_to_int tinfo + 8232).

(** The bytes of the root slots [rs] (8 bytes each). *)
Definition slot_bytes_stmt (rs : list ptr) (a : Z) : Prop :=
  exists r, In r rs /\ ptr_to_int r <= a < ptr_to_int r + 8.

(* ------------------------------------------------------------------ *)
(** ** Running Vellvm code *)

Definition lift_top {R} (t : MCFGtop R) : CFGtop R :=
  translate (fun _ e => inr1 e) t.

Definition returns {R} (t : MCFGbot R) (r : R) : Prop := t ≈ Ret r.

Definition ends_in_oom {R} (t : MCFGbot R) : Prop :=
  exists (k : void -> MCFGbot R), t ≈ Vis (subevent _ (ThrowOOM tt)) k.

(** [denote_vellvm] from [Semantics/TopLevel.v], with the runtime's
    library functions [rt] added to Vellvm's built-in [_LIBRARIES]. *)
Definition denote_with_runtime
           (rt : list (function_id * function_denotation))
           (ret_typ : dtyp) (entry : function_id) (args : list dvalue)
           (mcfg : CFG.mcfg dtyp) : MCFGtop dvalue :=
  build_global_environment mcfg ;;
  'defns <- map_monad address_one_function (m_definitions mcfg) ;;
  'libraries <- map_monad address_one_library_function
                 (rt ++ library_functions (m_declarations mcfg)) ;;
  'addr <- gread entry ;;
  'rv <- denote_mcfg (IP.of_list (defns ++ libraries)) ret_typ addr args ;;
  match rv with
  | inl e => raiseLLVM e
  | inr rv => ret rv
  end.

Definition initial_fused : FusedS :=
  (initial_state, ((Build_stack_frame Maps.empty None None, []), Maps.empty)).

(** The runtime prelude: [declare void @garbage_collect(ptr)]. *)
Definition gc_decl : declaration typ :=
  mk_declaration (Name "garbage_collect")
    (TYPE_Function TYPE_Void [TYPE_Pointer None] false)
    ([], [[]]) [] [].

Definition runtime_prelude : LLprog := [TLE_Declaration gc_decl].

(** Set up [tinfo], then run [@certirocq_main(tinfo)]. *)
Definition run_program (gc : list dvalue -> MCFGtop (exc + dvalue))
           (make_tinfo : MCFGtop dvalue) (prog : LLprog)
  : MCFGbot (Res dvalue) :=
  interp_mcfg
    (tinfo <- make_tinfo ;;
     denote_with_runtime [(Name "garbage_collect", fun args => lift_top (gc args))]
       (DTYPE_I 64) (Name "certirocq_main") [tinfo]
       (convert_types (CFG.mcfg_of_tle (link runtime_prelude prog))))
    initial_fused.

(* ------------------------------------------------------------------ *)
(** ** The runtime contract *)

Section Runtime.
  Variable cenv : ctor_env.
  Variable fds : fundefs.
  (** The heap invariant is the runtime's choice. *)
  Variable heap_inv : state -> ptr -> Prop.

  (** The runtime's state is well-formed, with shadow stack [fp] holding the
      root slots [rs]. *)
  Definition rt_ok (st : state) (tinfo fp : ptr) (rs : list ptr) : Prop :=
    heap_inv st tinfo /\ tinfo_ok st tinfo /\
    mem_ok_stmt st /\ nursery_tinfo_disjoint_stmt st tinfo /\
    field st tinfo off_fp fp /\ shadow_stack st fp rs.

  (** 1. [make_tinfo] runs out of memory or returns a [thread_info] in a
         well-formed state with an empty shadow stack, that fits in the
         address space.
      2. The generated code preserves [heap_inv]: it only writes the
         nursery and the [alloc]/[fp]/[nalloc] fields, and moves [alloc]
         forward within the nursery, word-aligned.
      3. The collector, called in a well-formed state whose roots represent
         [vs], with a request for [nalloc] words, runs out of memory or
         returns with the state well-formed again, the same roots
         representing the same [vs], [nalloc] words of room, and the memory
         frames unchanged.  Outside the heap it writes only the root slots;
         every new heap address was unallocated (fresh [malloc]s); and the
         root slots keep their Vellvm allocation ids (the generated code
         reloads them through its own [alloca]).  Nothing is said about the
         ids of heap bytes: a copying collector frees its from-space.
         [nalloc] is bounded because the stored word only determines it
         modulo 2^64; the generated code requests small constants. *)
  Definition runtime_correct (gc : list dvalue -> MCFGtop (exc + dvalue))
             (make_tinfo : MCFGtop dvalue) : Prop :=
    (ends_in_oom (interp_mcfg make_tinfo initial_fused)
     \/ exists st tinfo fp,
         returns (interp_mcfg make_tinfo initial_fused)
                 ((st, snd initial_fused), DVALUE_Base (DVALUE_Pointer tinfo)) /\
         rt_ok st tinfo fp [] /\ ptr_to_int fp = 0 /\
         ptr_to_int tinfo + 8232 < 2 ^ 64) /\
    (forall st st2 tinfo alloc alloc2 limit,
       heap_inv st tinfo -> tinfo_ok st tinfo ->
       heap_agree_except st st2 (mutator_writes st tinfo) ->
       field st tinfo off_alloc alloc -> field st tinfo off_limit limit ->
       field st2 tinfo off_alloc alloc2 ->
       (ptr_to_int alloc <= ptr_to_int alloc2 <= ptr_to_int limit)%Z ->
       (ptr_to_int alloc2 mod 8 = 0)%Z ->
       heap_inv st2 tinfo) /\
    (forall (genv : global_env) (tinfo : ptr) (st : state) ls fp rs vs nalloc,
       rt_ok st tinfo fp rs ->
       roots_ok cenv fds genv st tinfo rs vs ->
       0 <= nalloc < 2 ^ 61 ->
       (exists a, ptr_off tinfo off_nalloc a /\ reads_word st a nalloc) ->
       ends_in_oom (interp_mcfg (gc [DVALUE_Base (DVALUE_Pointer tinfo)]) (st, (ls, genv)))
       \/ exists st',
           returns (interp_mcfg (gc [DVALUE_Base (DVALUE_Pointer tinfo)]) (st, (ls, genv)))
                   ((st', (ls, genv)), inr (DVALUE_Base DVALUE_None)) /\
           rt_ok st' tinfo fp rs /\
           roots_ok cenv fds genv st' tinfo rs vs /\
           room st' tinfo nalloc /\
           frames_of st' = frames_of st /\
           (forall a, ~ in_heap st a -> ~ slot_bytes_stmt rs a ->
                      IntMaps.lookup a (mem_of st') = IntMaps.lookup a (mem_of st)) /\
           (forall a, in_heap st' a -> in_heap st a \/ IntMaps.lookup a (mem_of st) = None) /\
           (forall a, slot_bytes_stmt rs a ->
              option_map snd (IntMaps.lookup a (mem_of st')) =
              option_map snd (IntMaps.lookup a (mem_of st)))).
End Runtime.

(* ------------------------------------------------------------------ *)
(** ** Source-side restrictions *)

(** Constructor tags are in [cenv], with an ordinal below 251 and an arity
    below 2^54.  The header stores the ordinal in its low 10 bits, but
    [gc_stack.c] does not scan objects whose tag byte is at least
    [No_scan_tag = 251]. *)
Definition tag_ok (cenv : ctor_env) (t : ctor_tag) : Prop :=
  (exists info, M.get t cenv = Some info) /\
  (ord_of cenv t < 251)%N /\ (arity_of cenv t < 2 ^ 54)%N.

(** No [Eprim], only integer primitive values, no nested [Efun]; constructor
    arities match, projections are in range, and every allocation chunk
    (the words the limit check at the head of a run of constructors asks
    for) is below 2^64 bytes, as the check compares in 64-bit arithmetic. *)
Inductive body_ok (cenv : ctor_env) : term.exp -> Prop :=
| BO_constr x t ys e :
    tag_ok cenv t -> arity_of cenv t = N.of_nat (length ys) ->
    8 * Z.of_N (chunk_words (Econstr x t ys e)) < 2 ^ 64 ->
    body_ok cenv e -> body_ok cenv (Econstr x t ys e)
| BO_proj x t n y e :
    (n < arity_of cenv t)%N -> body_ok cenv e -> body_ok cenv (Eproj x t n y e)
| BO_case x bs :
    Forall (fun b => tag_ok cenv (fst b) /\ body_ok cenv (snd b)) bs -> body_ok cenv (Ecase x bs)
| BO_letapp x f ft ys e : body_ok cenv e -> body_ok cenv (Eletapp x f ft ys e)
| BO_app f ft ys : body_ok cenv (Eapp f ft ys)
| BO_prim_val x n e : body_ok cenv e -> body_ok cenv (Eprim_val x (existT _ primInt n) e)
| BO_halt x : body_ok cenv (Ehalt x).

Inductive fundefs_ok (cenv : ctor_env) : fundefs -> Prop :=
| FO_nil : fundefs_ok cenv Fnil
| FO_cons f ft xs e fds :
    body_ok cenv e -> fundefs_ok cenv fds -> fundefs_ok cenv (Fcons f ft xs e fds).

(** Two distinct constructors of one inductive with the same ordinal are one
    nullary and one not: the pipeline numbers the two classes separately
    ([LambdaBox_to_LambdaANF.common.convert_cnstrs]), and the emitted [case]
    tests the low bit before switching on the ordinal.  (The Wasm backend's
    [cenv_restricted] also forbids a boxed constructor from sharing its
    ordinal with a nullary one, which the pipeline's numbering violates for
    every inductive with both kinds, e.g. [nat]; see [LLVM_nonvacuity.nat_cenv_ok].) *)
Definition cenv_ok (cenv : ctor_env) : Prop :=
  forall t t' i i', t <> t' ->
    M.get t cenv = Some i -> M.get t' cenv = Some i' ->
    ctor_ind_tag i = ctor_ind_tag i' -> ctor_ordinal i = ctor_ordinal i' ->
    (ctor_arity i = 0%N <-> ctor_arity i' <> 0%N).

(** The program [Efun fds main] is closed with unique bindings (what the
    LambdaANF pipeline guarantees before code generation), and satisfies the
    restrictions above. *)
Definition llvm_restricted (cenv : ctor_env) (fds : fundefs) (main : term.exp) : Prop :=
  fundefs_ok cenv fds /\ body_ok cenv main /\
  (~ exists x, occurs_free (Efun fds main) x) /\
  unique_bindings (Efun fds main) /\
  cenv_ok cenv.

(* ------------------------------------------------------------------ *)
(** ** The theorem

    Proved as [Theorem LambdaANF_to_LLVM_correct : LambdaANF_to_LLVM_correct_statement]
    in [LLVM_sim_exp.v]. *)

Definition LambdaANF_to_LLVM_correct_statement : Prop :=
  forall (cenv : ctor_env) (pfs : prims) prim_of
         (heap_inv : state -> ptr -> Prop)
         (gc : list dvalue -> MCFGtop (exc + dvalue)) (make_tinfo : MCFGtop dvalue)
         (fds : fundefs) (main : term.exp) (v : term.val) (n : nat),
    runtime_correct cenv fds heap_inv gc make_tinfo ->
    llvm_restricted cenv fds main ->
    bstep_e pfs cenv (M.empty _) (Efun fds main) v n ->
    ends_in_oom (run_program gc make_tinfo (emitted cenv prim_of (Efun fds main)))
    \/ exists st ls genv z,
        returns (run_program gc make_tinfo (emitted cenv prim_of (Efun fds main)))
                ((st, (ls, genv)), I64 z) /\
        repr_val cenv fds genv st v z.
