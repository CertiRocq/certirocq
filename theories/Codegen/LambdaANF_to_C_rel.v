(* What it means for a C state to represent a LambdaANF state: values, the thread info
   with its roots, and calls. *)

From Stdlib Require Import ZArith.ZArith Lists.List.
From compcert Require Import lib.Coqlib lib.Maps lib.Integers common.AST common.Values
     common.Memory common.Events common.Globalenvs common.Smallstep
     cfrontend.Ctypes cfrontend.Clight Clightdefs.
From MetaRocq.Utils Require Import bytestring.
From CertiRocq.Common Require Import compM.
From CertiRocq.LambdaANF Require Import term algebra eval.
From CertiRocq.Codegen Require Import LambdaANF_to_C.

Import ListNotations.
Local Open Scope Z_scope.
Local Open Scope bs_scope.

(** * Layout *)

(* The offsets of the fields of [struct thread_info] and [struct stack_frame], in bytes *)
Definition alloc_ofs : Z := 0.
Definition limit_ofs : Z := 8.
Definition heap_ofs : Z := 16.
Definition args_ofs : Z := 24.
Definition fp_ofs : Z := args_ofs + 8 * max_args.
Definition tinfo_size : Z := fp_ofs + 24.
Definition next_ofs : Z := 0.
Definition root_ofs : Z := 8.
Definition prev_ofs : Z := 16.

(* The number of words of the nursery, [NURSERY_SIZE] in [gc_stack.h] *)
Definition nursery_size : Z := 2 ^ 16.

(** * The heap *)

(* What the proof sees of the collector's heap: its blocks, the addresses of its objects,
   and the free space, which is the bytes from [free_start] to [free_end] of the block
   [free_block]. [tinfo->alloc] and [tinfo->limit] point to them. *)
Record heap : Type := mkHeap
  { heap_blocks : block -> Prop;
    heap_objects : block -> Z -> Prop;
    free_block : block;
    free_start : Z;
    free_end : Z }.

(* The bytes of the heap that hold data *)
Definition allocated (h : heap) (b : block) (o : Z) : Prop :=
  heap_blocks h b /\ (b = free_block h -> o < free_start h).

(* The heap after a block of [n] words is allocated at the start of the free space *)
Definition alloc_block (h : heap) (n : Z) : heap :=
  mkHeap (heap_blocks h)
         (fun b o => heap_objects h b o \/ (b = free_block h /\ o = free_start h + 8))
         (free_block h) (free_start h + 8 * (n + 1)) (free_end h).

(* Stores the words [ws] in block [b] from offset [o] *)
Fixpoint store_words (m : mem) (b : block) (o : Z) (ws : list Values.val) : option mem :=
  match ws with
  | [] => Some m
  | w :: ws' =>
    match Mem.store Mptr m b o w with
    | Some m' => store_words m' b (o + 8) ws'
    | None => None
    end
  end.

(* A frame of the shadow stack: the address of the [struct stack_frame], the address of
   its roots and their number *)
Record frame : Type := mkFrame
  { frame_block : block;
    frame_ofs : Z;
    roots_block : block;
    roots_ofs : Z;
    roots_num : Z }.

(* The bytes of the thread info at [tb, tofs] *)
Definition in_tinfo (tb : block) (tofs : Z) (b : block) (o : Z) : Prop :=
  b = tb /\ tofs <= o < tofs + tinfo_size.

(* The bytes of the roots of the frames [fs] *)
Definition in_roots (fs : list frame) (b : block) (o : Z) : Prop :=
  exists fr, In fr fs /\ b = roots_block fr /\
             roots_ofs fr <= o < roots_ofs fr + 8 * roots_num fr.

(* The addresses of the roots: the first [n] words of [tinfo->args] and the roots of [fs] *)
Definition root_at (tb : block) (tofs : Z) (n : Z) (fs : list frame) (b : block) (o : Z) : Prop :=
  (b = tb /\ exists i, 0 <= i < n /\ o = tofs + args_ofs + 8 * i) \/
  (exists fr i, In fr fs /\ 0 <= i < roots_num fr /\ b = roots_block fr /\ o = roots_ofs fr + 8 * i).

(* The frames from the pointer [fp] *)
Inductive frames (m : mem) : Values.val -> list frame -> Prop :=
| Frames_nil : frames m Vnullptr []
| Frames_cons : forall fr prev fs,
    Mem.load Mptr m (frame_block fr) (frame_ofs fr + next_ofs)
    = Some (Vptr (roots_block fr) (Ptrofs.repr (roots_ofs fr + 8 * roots_num fr))) ->
    Mem.load Mptr m (frame_block fr) (frame_ofs fr + root_ofs)
    = Some (Vptr (roots_block fr) (Ptrofs.repr (roots_ofs fr))) ->
    Mem.load Mptr m (frame_block fr) (frame_ofs fr + prev_ofs) = Some prev ->
    frames m prev fs ->
    frames m (Vptr (frame_block fr) (Ptrofs.repr (frame_ofs fr))) (fr :: fs).

Section Relation.

  Context (cenv : ctor_env)   (* the constructors of the source program *)
          (ge : genv)         (* the global environment of the C program *)
          (nparam : nat).     (* the number of arguments passed as C arguments *)

  (* The invariant of the collector on its own data, for a heap, a memory and the address
     of the thread info. The proof never looks inside it. *)
  Context (gc_inv : heap -> mem -> block -> Z -> Prop).

  Context {fuel : Type} {Hf : @fuel_resource fuel} {trace : Type} {Ht : @trace_resource trace}.

  (** * Values *)

  (* [v] is laid out at [w] in [m]. A block is an object of the heap [h]. A function is a
     pointer to a C function that [F] accepts. *)
  Inductive repr_val (F : val -> fundef -> Prop) (h : heap) (m : mem)
    : val -> Values.val -> Prop :=
  | Repr_constant : forall t ord,
      ctor_rep_of cenv t = Ret (Constant ord) ->
      repr_val F h m (Vconstr t []) (Vlong (Int64.repr (constant_value ord)))
  | Repr_block : forall t vs ord b ofs,
      ctor_rep_of cenv t = Ret (Block ord (length vs)) ->
      heap_objects h b (Ptrofs.unsigned ofs) ->
      8 <= Ptrofs.unsigned ofs ->
      Ptrofs.unsigned ofs + 8 * Z.of_nat (length vs) <= Ptrofs.max_unsigned ->
      (forall o, Ptrofs.unsigned ofs - 8 <= o < Ptrofs.unsigned ofs + 8 * Z.of_nat (length vs) ->
                 allocated h b o) ->
      Mem.load Mptr m b (Ptrofs.unsigned ofs - 8)
      = Some (Vlong (Int64.repr (block_header ord (Z.of_nat (length vs))))) ->
      repr_fields F h m vs b (Ptrofs.unsigned ofs) ->
      repr_val F h m (Vconstr t vs) (Vptr b ofs)
  | Repr_fun : forall rho fds f b fd,
      Genv.find_funct_ptr ge b = Some fd ->
      F (Vfun rho fds f) fd ->
      repr_val F h m (Vfun rho fds f) (Vptr b Ptrofs.zero)

  (* [vs] are laid out at the words of block [b] from offset [o] *)
  with repr_fields (F : val -> fundef -> Prop) (h : heap) (m : mem)
    : list val -> block -> Z -> Prop :=
  | Repr_nil : forall b o, repr_fields F h m [] b o
  | Repr_cons : forall v vs b o w,
      Mem.load Mptr m b o = Some w ->
      repr_val F h m v w ->
      repr_fields F h m vs b (o + 8) ->
      repr_fields F h m (v :: vs) b o.

  (* [w] is the layout of some value *)
  Definition is_value (h : heap) (m : mem) (w : Values.val) : Prop :=
    exists v, repr_val (fun _ _ => True) h m v w.

  (** * The thread info *)

  (* The free space of [h] can be written *)
  Record free_ok (h : heap) (m : mem) : Prop :=
    { free_heap : heap_blocks h (free_block h);
      free_range : 0 <= free_start h <= free_end h /\ free_end h <= Ptrofs.max_unsigned;
      free_size : free_end h - free_start h <= Ptrofs.max_signed;
      free_align : (8 | free_start h);
      free_perm : Mem.range_perm m (free_block h) (free_start h) (free_end h) Cur Writable }.

  (* The frame [fr] is outside the heap and the thread info. Its struct and its roots can
     be written and each root holds a value. Its blocks are allocated. *)
  Record frame_ok (h : heap) (m : mem) (tb : block) (fr : frame) : Prop :=
    { frame_heap : ~ heap_blocks h (frame_block fr) /\ ~ heap_blocks h (roots_block fr);
      frame_tinfo : frame_block fr <> tb /\ roots_block fr <> tb;
      frame_range : 0 <= roots_ofs fr /\ 0 <= roots_num fr /\
                    roots_ofs fr + 8 * roots_num fr <= Ptrofs.max_unsigned;
      frame_perm : Mem.range_perm m (roots_block fr) (roots_ofs fr)
                                  (roots_ofs fr + 8 * roots_num fr) Cur Writable;
      frame_values : forall i, 0 <= i < roots_num fr ->
                               exists w, Mem.load Mptr m (roots_block fr) (roots_ofs fr + 8 * i)
                                         = Some w /\ is_value h m w;
      frame_valid : Mem.valid_block m (frame_block fr) /\ Mem.valid_block m (roots_block fr);
      frame_signed : 8 * roots_num fr <= Ptrofs.max_signed;
      frame_struct : 0 <= frame_ofs fr /\ frame_ofs fr + 24 <= Ptrofs.max_unsigned /\
                     Mem.range_perm m (frame_block fr) (frame_ofs fr) (frame_ofs fr + 24)
                                    Cur Writable }.

  (* The thread info at [tb, tofs] has the limit of the free space of [h] and the frames
     [fs]. The blocks of the heap are allocated, and the collector's own data are in
     order. *)
  Record tinfo_wf (h : heap) (fs : list frame) (m : mem) (tb : block) (tofs : Z) : Prop :=
    { wf_range : 0 <= tofs /\ tofs + tinfo_size <= Ptrofs.max_unsigned /\ (8 | tofs);
      wf_perm : Mem.range_perm m tb tofs (tofs + tinfo_size) Cur Writable;
      wf_block : ~ heap_blocks h tb;
      wf_limit : Mem.load Mptr m tb (tofs + limit_ofs)
                    = Some (Vptr (free_block h) (Ptrofs.repr (free_end h)));
      wf_free : free_ok h m;
      wf_fp : exists fp, Mem.load Mptr m tb (tofs + fp_ofs) = Some fp /\ frames m fp fs;
      wf_frames : Forall (frame_ok h m tb) fs;
      wf_heap : forall b, heap_blocks h b -> Mem.valid_block m b;
      wf_gc : gc_inv h m tb tofs }.

  (* [tinfo->alloc] is the start of the free space. The code lets it fall behind between
     two calls. *)
  Definition tinfo_ok (h : heap) (fs : list frame) (m : mem) (tb : block) (tofs : Z) : Prop :=
    tinfo_wf h fs m tb tofs /\
    Mem.load Mptr m tb (tofs + alloc_ofs) = Some (Vptr (free_block h) (Ptrofs.repr (free_start h))).

  (** * Calls *)

  (* The word at [b, o] in [m'] is the layout of every value that the word at [b, o]
     in [m] is the layout of *)
  Definition still_represented (h : heap) (m : mem) (h' : heap) (m' : mem)
             (b : block) (o : Z) : Prop :=
    forall w, Mem.load Mptr m b o = Some w ->
    exists w', Mem.load Mptr m' b o = Some w' /\
               forall F v, repr_val F h m v w -> repr_val F h' m' v w'.

  (* From [m] to [m'] the contents change only in the heap, the thread info, the roots
     and [X]. Memory outside the heap and [X] stays accessible. The heap grows only by
     new blocks. *)
  Definition changes (X : block -> Z -> Prop) (tb : block) (tofs : Z) (fs : list frame)
             (h : heap) (m : mem) (h' : heap) (m' : mem) : Prop :=
    Mem.unchanged_on (fun b o => ~ heap_blocks h b /\ ~ in_tinfo tb tofs b o /\
                                 ~ in_roots fs b o /\ ~ X b o) m m' /\
    (forall b o k p, ~ heap_blocks h b -> ~ X b o -> Mem.perm m b o k p -> Mem.perm m' b o k p) /\
    (forall b, heap_blocks h' b -> heap_blocks h b \/ ~ Mem.valid_block m b).

  (* The statement about a call that returns [w] and takes the heap [h] and the memory
     [m] to [h'] and [m']: the result satisfies [R], the thread info is as before, every
     root is still represented, and the memory changes as [changes] says. The roots are
     the first [n] words of [tinfo->args] and the roots of [fs]. [X] is the memory of
     foreign code. *)
  Definition call_post (X : block -> Z -> Prop) (R : heap -> mem -> Values.val -> Prop)
             (n : Z) (tb : block) (tofs : Z) (fs : list frame)
             (h : heap) (m : mem) (w : Values.val) (h' : heap) (m' : mem) : Prop :=
    R h' m' w /\
    tinfo_ok h' fs m' tb tofs /\
    (forall b o, root_at tb tofs n fs b o -> still_represented h m h' m' b o) /\
    changes X tb tofs fs h m h' m'.

  (* The C function [fd] called with [args] returns, whatever the caller does next, and
     [call_post] holds *)
  Definition call_returns (X : block -> Z -> Prop) (R : heap -> mem -> Values.val -> Prop)
             (n : Z) (tb : block) (tofs : Z) (fs : list frame) (h : heap) (m : mem)
             (fd : fundef) (args : list Values.val) : Prop :=
    exists w h' m',
      (forall k, is_call_cont k ->
                 star step2 ge (Callstate fd args k m) E0 (Returnstate w k m')) /\
      call_post X R n tb tofs fs h m w h' m'.

  (** * Functions *)

  (* The arguments [ws] that are not C arguments are in [tinfo->args] *)
  Definition args_in_tinfo (m : mem) (tb : block) (tofs : Z) (ws : list Values.val) : Prop :=
    forall i w, (nparam <= i)%nat -> nth_error ws i = Some w ->
                Mem.load Mptr m tb (tofs + args_ofs + 8 * Z.of_nat i) = Some w.

  (* For [k] steps of the source program, the C function [fd] behaves as the function [v]:
     if the body of [v] evaluates to a value, the call of [fd] with related arguments
     returns a related result *)
  Fixpoint fun_rel (k : nat) (v : val) (fd : fundef) {struct k} : Prop :=
    match v with
    | Vfun rho fds f =>
      exists t xs e,
        find_def f fds = Some (t, xs, e) /\
        type_of_fundef fd = fun_ty nparam (length xs) /\
        match k with
        | O => True
        | S k =>
          forall (j : nat) vs rho' (c : fuel) v' (tr : trace) ws tb tofs h fs m,
            (j <= k)%nat ->
            set_lists xs vs (def_funs fds fds rho rho) = Some rho' ->
            bstep_fuel cenv rho' e c (Res v') tr ->
            (to_nat c <= j)%nat ->
            tinfo_ok h fs m tb tofs ->
            (* [k - (k - j)] is [j], written so that the recursion is accepted *)
            Forall2 (repr_val (fun_rel (k - (k - j))) h m) vs ws ->
            args_in_tinfo m tb tofs ws ->
            call_returns (fun _ _ => False)
                         (fun h' m' w' => repr_val (fun_rel (k - (k - j) - to_nat c))
                                                   h' m' v' w')
                         0 tb tofs fs h m
                         fd (Vptr tb (Ptrofs.repr tofs) :: firstn nparam ws)
        end
    | _ => False
    end.

  (* [v] is laid out at [w], and its functions are related for [k] steps *)
  Definition val_rel (k : nat) (h : heap) (m : mem) (v : val) (w : Values.val) : Prop :=
    repr_val (fun_rel k) h m v w.

  (** * The functions of the runtime *)

  (* The external function that [external] of [LambdaANF_to_C] declares *)
  Definition extern (name : string) (params : list type) (res : type) : external_function :=
    EF_external (String.to_string name) (signature_of_type params res cc_default).

  (* The bytes that the collector's invariant may depend on: the blocks of the heap outside
     the free space, and the fields [heap], [nalloc] and [odata] of the thread info *)
  Definition gc_owned (h : heap) (tb : block) (tofs : Z) (b : block) (o : Z) : Prop :=
    (heap_blocks h b /\ ~ (b = free_block h /\ free_start h <= o < free_end h)) \/
    (b = tb /\ (tofs + heap_ofs <= o < tofs + args_ofs \/
                tofs + fp_ofs + 8 <= o < tofs + tinfo_size)).

  (* What the proof assumes of the collector *)
  Record collector_ok : Prop :=
    { (* Its invariant depends only on the bytes of [gc_owned] *)
      gc_stable : forall h m m' tb tofs,
          gc_inv h m tb tofs ->
          Mem.unchanged_on (gc_owned h tb tofs) m m' ->
          gc_inv h m' tb tofs;
      (* A header and values written at the start of the free space are a new object *)
      gc_alloc : forall h m m0 m' tb tofs ord ws,
          gc_inv h m tb tofs ->
          0 <= ord <= max_block_ordinal ->
          ws <> [] ->
          Forall (is_value h m) ws ->
          free_start h + 8 * (Z.of_nat (length ws) + 1) <= free_end h ->
          Mem.store Mptr m (free_block h) (free_start h)
                    (Vlong (Int64.repr (block_header ord (Z.of_nat (length ws))))) = Some m0 ->
          store_words m0 (free_block h) (free_start h + 8) ws = Some m' ->
          gc_inv (alloc_block h (Z.of_nat (length ws))) m' tb tofs;
      (* [garbage_collect_args(tinfo, n, nalloc)] returns with room for [nalloc] words.
         The first [n] words of [tinfo->args] are roots. The function may be external or
         defined in the program. *)
      gc_collect : forall b fd tb tofs h fs m n nalloc,
          Genv.find_symbol ge gcArgsId = Some b ->
          Genv.find_funct_ptr ge b = Some fd ->
          tinfo_ok h fs m tb tofs ->
          0 <= n <= max_args ->
          0 <= nalloc <= nursery_size ->
          (forall i, 0 <= i < n ->
                     exists w, Mem.load Mptr m tb (tofs + args_ofs + 8 * i) = Some w /\
                               is_value h m w) ->
          call_returns (fun _ _ => False)
                       (fun h' _ _ => 8 * nalloc <= free_end h' - free_start h')
                       n tb tofs fs h m fd
                       [Vptr tb (Ptrofs.repr tofs); Vlong (Int64.repr n);
                        Vlong (Int64.repr nalloc)] }.

  (* [certirocq_is_ptr(w)] is true for a pointer with an even offset and false for an odd
     integer *)
  Definition is_ptr_spec : Prop :=
    (forall m b ofs,
        (2 | Ptrofs.unsigned ofs) ->
        external_call (extern "certirocq_is_ptr" is_ptr_params tbool) ge
                      [Vptr b ofs] m E0 Vtrue m) /\
    (forall m i,
        Z.odd (Int64.unsigned i) = true ->
        external_call (extern "certirocq_is_ptr" is_ptr_params tbool) ge
                      [Vlong i] m E0 Vfalse m).

End Relation.
