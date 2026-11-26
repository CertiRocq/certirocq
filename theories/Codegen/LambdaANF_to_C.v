(* Translation of LambdaANF to Clight. The input is closure converted and hoisted.
   Values have the OCaml representation and the collector is [runtime/gc_stack.c]. *)

From Stdlib Require Import ZArith.ZArith Lists.List Bool.Bool.
From Stdlib Require PrimInt63 PrimString Uint63.
From ExtLib Require Import Structures.Monads.
From MetaRocq.Common Require Import BasicAst.
From MetaRocq.Utils Require Import bytestring.
From compcert Require Import common.AST lib.Integers lib.Floats
     cfrontend.Ctypes cfrontend.Cop cfrontend.Clight Clightdefs.
From CertiRocq.Common Require Import AstCommon compM Pipeline_utils.
From CertiRocq.LambdaANF Require Import set_util term identifiers cps_show.

Import MonadNotation ListNotations.
Open Scope monad_scope.
Local Open Scope bs_scope.

(* The identifiers of Clight *)
Local Notation ident := AST.ident.

(** * Names *)

(* The pipeline uses identifiers starting from 100 *)

(* The types [struct thread_info] and [struct stack_frame] of [gc_stack.h], and their fields *)
Definition threadInfoId : ident := 1%positive.
Definition allocId      : ident := 2%positive.
Definition limitId      : ident := 3%positive.
Definition heapId       : ident := 4%positive.
Definition argsId       : ident := 5%positive.
Definition fpId         : ident := 6%positive.
Definition nallocId     : ident := 7%positive.
Definition odataId      : ident := 8%positive.
Definition stackFrameId : ident := 9%positive.
Definition nextId       : ident := 10%positive.
Definition rootId       : ident := 11%positive.
Definition prevId       : ident := 12%positive.
(* The functions of [gc_stack.h] that the code calls *)
Definition gcArgsId     : ident := 13%positive.
Definition isPtrId      : ident := 14%positive.
(* The variables of a C function. [allocId] is also the variable for [tinfo->alloc]. *)
Definition tinfoId      : ident := 15%positive.
Definition frameId      : ident := 16%positive.
Definition rootsId      : ident := 17%positive.
Definition resultId     : ident := 18%positive.
Definition boxedId      : ident := 19%positive.
(* The function for the main expression, and the entry point of the Clight program *)
Definition bodyId       : ident := 20%positive.
Definition mainId       : ident := 21%positive.

Definition reserved_names (body_name : string) : list (ident * string) :=
  [ (threadInfoId, "thread_info"); (allocId, "alloc"); (limitId, "limit"); (heapId, "heap");
    (argsId, "args"); (fpId, "fp"); (nallocId, "nalloc"); (odataId, "odata");
    (stackFrameId, "stack_frame"); (nextId, "next"); (rootId, "root"); (prevId, "prev");
    (gcArgsId, "garbage_collect_args"); (isPtrId, "certirocq_is_ptr");
    (tinfoId, "tinfo"); (frameId, "frame"); (rootsId, "roots"); (resultId, "result");
    (boxedId, "boxed"); (bodyId, body_name); (mainId, "main") ].

(** * C types *)

(* The type of values. It is printed as [value]. *)
Definition tvalue : type := talignas (if Archi.ptr64 then 3%N else 2%N) (tptr tvoid).
(* The integer types with the size of a value *)
Definition tuintnat : type := if Archi.ptr64 then tulong else tuint.
Definition tintnat : type := if Archi.ptr64 then tlong else tint.

Definition tinfoT : type := Tstruct threadInfoId noattr.
Definition frameT : type := Tstruct stackFrameId noattr.

(* The size of [tinfo->args] *)
Definition max_args : Z := 1024.

(* The number of words of the nursery, [NURSERY_SIZE] in [gc_stack.h] *)
Definition nursery_size : Z := 2 ^ 16.

(* The definitions of [struct stack_frame] and [struct thread_info] in [gc_stack.h] *)
Definition composites : list composite_definition :=
  [ Composite stackFrameId Struct
      [ Member_plain nextId (tptr tvalue);
        Member_plain rootId (tptr tvalue);
        Member_plain prevId (tptr frameT) ] noattr;
    Composite threadInfoId Struct
      [ Member_plain allocId (tptr tvalue);
        Member_plain limitId (tptr tvalue);
        Member_plain heapId (tptr (Tstruct heapId noattr));
        Member_plain argsId (tarray tvalue max_args);
        Member_plain fpId (tptr frameT);
        Member_plain nallocId tuintnat;
        Member_plain odataId (tptr tvoid) ] noattr ].

(* [void garbage_collect_args(struct thread_info *, value n, value nalloc)] *)
Definition gc_args_params : list type := [tptr tinfoT; tvalue; tvalue].
Definition gc_args_ty : type := Tfunction gc_args_params tvoid cc_default.
(* [_Bool certirocq_is_ptr(value)] *)
Definition is_ptr_params : list type := [tvalue].
Definition is_ptr_ty : type := Tfunction is_ptr_params tbool cc_default.

(** * Statements and expressions *)

(* Sequence that drops [Sskip] *)
Definition seq (s1 s2 : statement) : statement :=
  match s1, s2 with
  | Sskip, _ => s2
  | _, Sskip => s1
  | _, _ => Ssequence s1 s2
  end.

Local Notation "s1 ;;; s2" := (seq s1 s2) (at level 61, right associativity).

(* An integer constant of the size of a value *)
Definition const (z : Z) (t : type) : expr :=
  if Archi.ptr64 then Econst_long (Int64.repr z) t else Econst_int (Int.repr z) t.

(* [a[i]], where [a] is an array or a pointer to elements of type [t] *)
Definition index (a : expr) (i : Z) (t : type) : expr :=
  Ederef (Ebinop Oadd a (const i tintnat) (tptr t)) t.

(* The word number [i] of the block [x] *)
Definition field (x : expr) (i : Z) : expr := index (Ecast x (tptr tvalue)) i tvalue.

(* The header of the block [x] *)
Definition header (x : expr) : expr := index (Ecast x (tptr tuintnat)) (-1) tuintnat.

(* The low 8 bits of the header of the block [x] *)
Definition tag (x : expr) : expr := Ebinop Oand (header x) (const 255 tuintnat) tuintnat.

Definition tinfo : expr := Etempvar tinfoId (tptr tinfoT).
Definition tinfo_field (f : ident) (t : type) : expr := Efield (Ederef tinfo tinfoT) f t.
Definition tinfo_alloc : expr := tinfo_field allocId (tptr tvalue).
Definition tinfo_limit : expr := tinfo_field limitId (tptr tvalue).
Definition tinfo_fp : expr := tinfo_field fpId (tptr frameT).

(* [tinfo->args[i]] *)
Definition arg (i : nat) : expr :=
  index (tinfo_field argsId (tarray tvalue max_args)) (Z.of_nat i) tvalue.

(* The C variable that holds [tinfo->alloc] *)
Definition alloc : expr := Etempvar allocId (tptr tvalue).

Definition frame : expr := Evar frameId frameT.
Definition frame_field (f : ident) (t : type) : expr := Efield frame f t.

(** * Representation of values *)

Inductive ctor_rep : Type :=
| Constant (ordinal : Z)                (* no arguments: the integer [2 * ordinal + 1] *)
| Block (ordinal : Z) (arity : nat).    (* a block with [arity] words *)

(* The collector does not look inside blocks whose header has a larger ordinal *)
Definition max_block_ordinal : Z := 250.

(* The integer of a constant with a larger ordinal does not fit in a word *)
Definition max_constant_ordinal : Z := 2 ^ 63 - 1.

Definition constant_value (ordinal : Z) : Z := 2 * ordinal + 1.
Definition block_header (ordinal : Z) (words : Z) : Z := Z.shiftl words 10 + ordinal.

(* The headers of floats and strings are those of OCaml *)
Definition float_header : Z := block_header 253 1.
Definition string_header (words : Z) : Z := block_header 252 words.

(* A primitive integer [i] is the integer [2 * i + 1] *)
Definition int_value (i : PrimInt63.int) : int64 := Int64.repr (2 * Uint63.to_Z i + 1).

Definition float64_to_model (f : PrimFloat.float) : float64_model :=
  exist (FloatOps.Prim2SF f) (FloatAxioms.Prim2SF_valid f).

Definition model_to_binary (f : float64_model) : Floats.float :=
  match proj1_sig f as x
        return is_true (SpecFloat.valid_binary FloatOps.prec FloatOps.emax x) -> Floats.float with
  | SpecFloat.S754_zero s => fun _ => Binary.B754_zero _ _ s
  | SpecFloat.S754_infinity s => fun _ => Binary.B754_infinity _ _ s
  | SpecFloat.S754_nan => fun _ => Binary.B754_nan FloatOps.prec FloatOps.emax false xH eq_refl
  | SpecFloat.S754_finite s m e => fun h => Binary.B754_finite _ _ s m e h
  end (proj2_sig f).

Definition float_value (f : PrimFloat.float) : Floats.float :=
  model_to_binary (float64_to_model f).

(* The words of an OCaml string. [w] is the word being filled, with [i] characters.
   The highest byte of the last word is [7 - i]. *)
Fixpoint string_words_aux (cs : list Z) (i : nat) (w : Z) : list Z :=
  match cs with
  | [] => [w + (7 - Z.of_nat i) * 2 ^ 56]
  | c :: cs' =>
    let w' := w + c * 2 ^ (8 * Z.of_nat i) in
    if Nat.eqb i 7 then w' :: string_words_aux cs' 0%nat 0 else string_words_aux cs' (S i) w'
  end%Z.

Definition string_words (s : PrimString.string) : list Z :=
  string_words_aux (map Uint63.to_Z (PrimStringAxioms.to_list s)) 0 0.

(* The number of words allocated for a primitive value *)
Definition prim_val_words (p : primitive_value) : nat :=
  match projT1 p as t return prim_value t -> nat with
  | primInt => fun _ => 0%nat
  | primFloat => fun _ => 2%nat
  | primString => fun s => S (length (string_words s))
  end (projT2 p).

(** * Variables defined by an expression *)

Fixpoint bound_vars (e : exp) : list var :=
  match e with
  | Econstr x _ _ e' | Eproj x _ _ _ e' | Eprim_val x _ e' | Eprim x _ _ e'
  | Eletapp x _ _ _ e' => x :: bound_vars e'
  | Ecase _ cs =>
    (fix go (cs : list (ctor_tag * exp)) : list var :=
       match cs with
       | [] => []
       | (_, e') :: cs' => (bound_vars e' ++ go cs')%list
       end) cs
  | Eapp _ _ _ | Ehalt _ | Efun _ _ => []
  end.

(* [Eletapp x f t ys (Ehalt x)] returns the result of the call *)
Definition returns (x : var) (e : exp) : bool :=
  match e with
  | Ehalt y => Pos.eqb x y
  | _ => false
  end.

(** * Variables assigned by a statement *)

Fixpoint assigns (i : ident) (s : statement) : bool :=
  match s with
  | Sset j _ | Scall (Some j) _ _ | Sbuiltin (Some j) _ _ _ => Pos.eqb i j
  | Ssequence s1 s2 | Sifthenelse _ s1 s2 | Sloop s1 s2 => assigns i s1 || assigns i s2
  | Sswitch _ ls => assigns_ls i ls
  | Slabel _ s' => assigns i s'
  | _ => false
  end
with assigns_ls (i : ident) (ls : labeled_statements) : bool :=
  match ls with
  | LSnil => false
  | LScons _ s ls' => assigns i s || assigns_ls i ls'
  end.

(** * Case analysis *)

(* A switch with a case for each element of the list. The last one is the default case. *)
Fixpoint labeled (cases : list (Z * statement)) : labeled_statements :=
  match cases with
  | [] => LSnil
  | (z, s) :: cases' =>
    match cases' with
    | [] => LScons None s LSnil
    | _ => LScons (Some z) s (labeled cases')
    end
  end.

Definition switch (a : expr) (cases : list (Z * statement)) : statement :=
  match cases with
  | [(_, s)] => s
  | _ => Sswitch a (labeled cases)
  end.

(* [blocks]: the cases of constructors with arguments, by ordinal.
   [constants]: the other cases, by value. *)
Definition case_stmt (y : expr) (blocks constants : list (Z * statement)) : statement :=
  match blocks, constants with
  | [], [] =>
    (* The source program cannot continue here *)
    Sreturn (Some (const 1 tvalue))
  | _, [] => switch (tag y) blocks
  | [], _ => switch (Ecast y tuintnat) constants
  | _, _ =>
    Scall (Some boxedId) (Evar isPtrId is_ptr_ty) [y] ;;;
    Sifthenelse (Etempvar boxedId tbool)
                (switch (tag y) blocks)
                (switch (Ecast y tuintnat) constants)
  end.

(** * Lists of variables *)

Definition in_list (x : var) (l : list var) : bool := existsb (Pos.eqb x) l.

Fixpoint index_of (x : var) (l : list var) : option nat :=
  match l with
  | [] => None
  | y :: l' => if Pos.eqb x y then Some 0%nat else option_map S (index_of x l')
  end.

(* The first [k] positions of [roots]: a variable of [old] that is [live] keeps its
   position, the other positions take the variables of [new]. *)
Fixpoint place (k : nat) (old new : list var) (live : var -> bool) : list var :=
  match k with
  | O => []
  | S k' =>
    match old with
    | x :: old' =>
      if live x then x :: place k' old' new live
      else match new with
           | y :: new' => y :: place k' old' new' live
           | [] => []
           end
    | [] =>
      match new with
      | y :: new' => y :: place k' [] new' live
      | [] => []
      end
    end
  end.

Section Translation.

  Context (nparam : nat)            (* the number of arguments passed as C arguments *)
          (prims : M.t primitive)   (* the C functions that implement the primitives *)
          (cenv : ctor_env)
          (fenv : M.t nat).         (* the number of parameters of each function *)

  (** ** Constructors *)

  Definition ctor_rep_of (t : ctor_tag) : error ctor_rep :=
    match M.get t cenv with
    | None => Err ("Codegen: unknown constructor " ++ show_pos t)
    | Some info =>
      let ordinal := Z.of_N (ctor_ordinal info) in
      if (ctor_arity info =? 0)%N then
        if (ordinal <=? max_constant_ordinal)%Z then Ret (Constant ordinal)
        else Err ("Codegen: constructor " ++ show_pos t ++ " has ordinal " ++
                  show_binnat (ctor_ordinal info) ++ ", more than fits in a word")
      else if (ordinal <=? max_block_ordinal)%Z then
             Ret (Block ordinal (N.to_nat (ctor_arity info)))
      else Err ("Codegen: constructor " ++ show_pos t ++ " has ordinal " ++
                show_binnat (ctor_ordinal info) ++ ", more than the collector supports")
    end.

  (* A constructor of [cs] other than [t] has the kind and the ordinal of [r] *)
  Definition clashes (t : ctor_tag) (r : ctor_rep) (cs : list (ctor_tag * exp)) : bool :=
    existsb (fun c =>
               negb (Pos.eqb (fst c) t) &&
               match ctor_rep_of (fst c), r with
               | Ret (Constant o), Constant o' | Ret (Block o _), Block o' _ => (o =? o')%Z
               | _, _ => false
               end) cs.

  (** ** Analyses *)

  (* The C function of the primitive takes [tinfo]. It can allocate and call the collector. *)
  Definition allocates (p : prim) : bool :=
    match M.get p prims with
    | Some info => prim_alloc info
    | None => false
    end.

  (* The number of words allocated by [e] before its next call *)
  Fixpoint alloc_need (e : exp) : nat :=
    match e with
    | Econstr _ _ ys e' =>
      match ys with
      | [] => alloc_need e'
      | _ => (S (length ys) + alloc_need e')%nat
      end
    | Eproj _ _ _ _ e' => alloc_need e'
    | Eprim_val _ p e' => (prim_val_words p + alloc_need e')%nat
    | Eprim _ p _ e' => if allocates p then 0%nat else alloc_need e'
    | Ecase _ cs =>
      (fix go (cs : list (ctor_tag * exp)) : nat :=
         match cs with
         | [] => 0%nat
         | (_, e') :: cs' => Nat.max (alloc_need e') (go cs')
         end) cs
    | Eletapp _ _ _ _ _ | Eapp _ _ _ | Ehalt _ | Efun _ _ => 0%nat
    end.

  (* The check for heap room goes before [e] if [e] allocates before it branches or if
     two branches allocate. Otherwise it goes in the branch that allocates. *)
  Fixpoint check_here (e : exp) : bool :=
    match e with
    | Econstr _ _ ys e' =>
      match ys with
      | [] => check_here e'
      | _ => true
      end
    | Eproj _ _ _ _ e' => check_here e'
    | Eprim_val _ p e' => (0 <? prim_val_words p)%nat || check_here e'
    | Eprim _ p _ e' => if allocates p then false else check_here e'
    | Ecase _ cs => (2 <=? length (List.filter (fun c => 0 <? alloc_need (snd c)) cs))%nat
    | Eletapp _ _ _ _ _ | Eapp _ _ _ | Ehalt _ | Efun _ _ => false
    end.

  (* The variables that [e] uses before its next call returns *)
  Fixpoint uses_now (e : exp) : FVSet :=
    match e with
    | Econstr _ _ ys e' => union_list (uses_now e') ys
    | Eproj _ _ _ y e' => PS.add y (uses_now e')
    | Eprim_val _ _ e' => uses_now e'
    | Eprim _ p ys e' =>
      if allocates p then union_list PS.empty ys else union_list (uses_now e') ys
    | Ecase y cs =>
      PS.add y ((fix go (cs : list (ctor_tag * exp)) : FVSet :=
                   match cs with
                   | [] => PS.empty
                   | (_, e') :: cs' => PS.union (uses_now e') (go cs')
                   end) cs)
    | Eletapp _ f _ ys _ | Eapp f _ ys => PS.add f (union_list PS.empty ys)
    | Ehalt x => PS.singleton x
    | Efun _ _ => PS.empty
    end.

  Definition is_fun (x : var) : bool :=
    match M.get x fenv with
    | Some _ => true
    | None => false
    end.

  (* The variables that [e] uses, without the names of functions *)
  Definition live_vars (e : exp) : list var :=
    List.filter (fun x => negb (is_fun x)) (PS.elements (exp_fv e)).

  (* The variables needed after a call with result [x], followed by [e] *)
  Definition live_after (x : var) (e : exp) : list var :=
    List.filter (fun y => negb (Pos.eqb y x)) (live_vars e).

  (* The size of the array [roots]: the largest number of variables needed after a call *)
  Fixpoint max_roots (e : exp) : nat :=
    match e with
    | Econstr _ _ _ e' | Eproj _ _ _ _ e' | Eprim_val _ _ e' => max_roots e'
    | Eprim x p _ e' =>
      if allocates p then Nat.max (length (live_after x e')) (max_roots e') else max_roots e'
    | Ecase _ cs =>
      (fix go (cs : list (ctor_tag * exp)) : nat :=
         match cs with
         | [] => 0%nat
         | (_, e') :: cs' => Nat.max (max_roots e') (go cs')
         end) cs
    | Eletapp x _ _ _ e' =>
      if returns x e' then 0%nat else Nat.max (length (live_after x e')) (max_roots e')
    | Eapp _ _ _ | Ehalt _ | Efun _ _ => 0%nat
    end.

  (* Whether [e] ends with a call to [f] with [n] arguments *)
  Fixpoint calls_itself (f : var) (n : nat) (e : exp) : bool :=
    match e with
    | Econstr _ _ _ e' | Eproj _ _ _ _ e' | Eprim_val _ _ e' | Eprim _ _ _ e' =>
      calls_itself f n e'
    | Ecase _ cs =>
      (fix go (cs : list (ctor_tag * exp)) : bool :=
         match cs with
         | [] => false
         | (_, e') :: cs' => calls_itself f n e' || go cs'
         end) cs
    | Eletapp x g _ ys e' =>
      if returns x e' then Pos.eqb g f && Nat.eqb (length ys) n else calls_itself f n e'
    | Eapp g _ ys => Pos.eqb g f && Nat.eqb (length ys) n
    | Ehalt _ | Efun _ _ => false
    end.

  (** ** Variables and calls *)

  (* The type of a function with [n] parameters *)
  Definition fun_ty (n : nat) : type :=
    Tfunction (tptr tinfoT :: repeat tvalue (Nat.min n nparam)) tvalue cc_default.

  (* The value of [x]. A function name is a global; any other variable is a C variable. *)
  Definition var_expr (x : var) : expr :=
    match M.get x fenv with
    | Some n => Ecast (Evar x (fun_ty n)) tvalue
    | None => Etempvar x tvalue
    end.

  (* [tinfo->args[i] = y] for the arguments [ys], the first of which has number [i] *)
  Fixpoint store_args (i : nat) (ys : list var) : statement :=
    match ys with
    | [] => Sskip
    | y :: ys' => Sassign (arg i) (var_expr y) ;;; store_args (S i) ys'
    end.

  (* [x = tinfo->args[i]] for the parameters [xs], the first of which has number [i] *)
  Fixpoint load_args (i : nat) (xs : list var) : statement :=
    match xs with
    | [] => Sskip
    | x :: xs' => Sset x (arg i) ;;; load_args (S i) xs'
    end.

  (* [r = f(tinfo, ys)] *)
  Definition call (r : ident) (f : var) (ys : list var) : error statement :=
    let n := length ys in
    if (max_args <? Z.of_nat n)%Z then
      Err ("Codegen: call of " ++ show_pos f ++ " with more arguments than tinfo->args holds")
    else
      callee <- match M.get f fenv with
                | Some m =>
                  if Nat.eqb m n then Ret (Evar f (fun_ty n))
                  else Err ("Codegen: call of " ++ show_pos f ++
                            " with the wrong number of arguments")
                | None => Ret (Ecast (Etempvar f tvalue) (tptr (fun_ty n)))
                end ;;
      ret (store_args nparam (skipn nparam ys) ;;;
           Scall (Some r) callee (tinfo :: map var_expr (firstn nparam ys))).

  (* [x = p(ys)], or [x = p(tinfo, ys)] if the C function of [p] takes [tinfo] *)
  Definition prim_call (x : var) (p : prim) (with_tinfo : bool) (ys : list var) : statement :=
    let ty := Tfunction ((if with_tinfo then [tptr tinfoT] else []) ++ repeat tvalue (length ys))%list
                        tvalue cc_default in
    Scall (Some x) (Ecast (Evar p ty) (tptr ty))
          ((if with_tinfo then [tinfo] else []) ++ map var_expr ys)%list.

  (** ** Allocation *)

  (* [x] is a new block with header [hdr] and [words] words *)
  Definition new_block (x : var) (hdr : Z) (words : Z) : statement :=
    Sset x (Ecast (Ebinop Oadd alloc (const 1 tintnat) (tptr tvalue)) tvalue) ;;;
    Sset allocId (Ebinop Oadd alloc (const (words + 1) tintnat) (tptr tvalue)) ;;;
    Sassign (header (Etempvar x tvalue)) (const hdr tuintnat).

  (* Stores [vs] in the words of [x], from word number [i] *)
  Fixpoint store_fields (x : var) (i : nat) (vs : list expr) : statement :=
    match vs with
    | [] => Sskip
    | v :: vs' =>
      Sassign (field (Etempvar x tvalue) (Z.of_nat i)) v ;;; store_fields x (S i) vs'
    end.

  Fixpoint store_words (x : var) (i : nat) (ws : list Z) : statement :=
    match ws with
    | [] => Sskip
    | w :: ws' =>
      Sassign (index (Ecast (Etempvar x tvalue) (tptr tuintnat)) (Z.of_nat i) tuintnat)
              (const w tuintnat) ;;;
      store_words x (S i) ws'
    end.

  (* [x] is the primitive value [p] *)
  Definition prim_val (x : var) (p : primitive_value) : statement :=
    match projT1 p as t return prim_value t -> statement with
    | primInt => fun i => Sset x (Econst_long (int_value i) tulong)
    | primFloat => fun f =>
      new_block x float_header 1 ;;;
      Sassign (Ederef (Ecast (Etempvar x tvalue) (tptr tdouble)) tdouble)
              (Econst_float (float_value f) tdouble)
    | primString => fun s =>
      let ws := string_words s in
      new_block x (string_header (Z.of_nat (length ws))) (Z.of_nat (length ws)) ;;;
      store_words x 0 ws
    end (projT2 p).

  (** ** What is known at a point of the C function *)

  Record state : Type := mkState
    { st_linked : bool;      (* [tinfo->fp] is [&frame] *)
      st_slots : list var;   (* the variables in [roots], in order *)
      st_stale : list var;   (* those whose C variable was not read back after the last call *)
      st_room : bool;        (* [alloc] is read and there is room up to the next call *)
      st_dirty : bool }.     (* the code has allocated since [alloc] was read *)

  Definition init_state : state := mkState false [] [] false false.

  Definition with_room (st : state) : state :=
    mkState (st_linked st) (st_slots st) (st_stale st) true false.

  Definition allocated (st : state) : state :=
    mkState (st_linked st) (st_slots st) (st_stale st) (st_room st) true.

  (* [tinfo->alloc = alloc], if the code has allocated *)
  Definition sync (st : state) : statement :=
    if st_dirty st then Sassign tinfo_alloc alloc else Sskip.

  (* [tinfo->fp = frame.prev], if [tinfo->fp] is [&frame] *)
  Definition unlink (st : state) : statement :=
    if st_linked st then Sassign tinfo_fp (frame_field prevId (tptr frameT)) else Sskip.

  (* What the function does before it returns or jumps to its start *)
  Definition leave (st : state) : statement := sync st ;;; unlink st.

  Section Body.

    Context (self : option (var * list var))  (* the name and the parameters of the function *)
            (nroots : Z)                      (* the size of [roots] *)
            (tmps : list ident).              (* a spare variable for each parameter *)

    Definition roots : expr := Evar rootsId (tarray tvalue nroots).
    Definition root (i : nat) : expr := index roots (Z.of_nat i) tvalue.

    (* [x = roots[i]] for the variables of [slots] selected by [keep], from position [i] *)
    Fixpoint read_roots (keep : var -> bool) (i : nat) (slots : list var) : statement :=
      match slots with
      | [] => Sskip
      | x :: slots' =>
        (if keep x then Sset x (root i) else Sskip) ;;; read_roots keep (S i) slots'
      end.

    (** *** The check for heap room *)

    Fixpoint save_args (i : nat) (xs : list var) : statement :=
      match xs with
      | [] => Sskip
      | x :: xs' => Sassign (arg i) (Etempvar x tvalue) ;;; save_args (S i) xs'
      end.

    (* Reads [alloc] and calls the collector if there is no room for [n] words. The
       variables of [live] that are not in [roots] are saved in [tinfo->args]. *)
    Definition check_room (st : state) (live : list var) (n : nat) : error statement :=
      let saved := List.filter (fun x => negb (in_list x (st_slots st))) live in
      let reread := fun x => in_list x live && negb (in_list x (st_stale st)) in
      if (max_args <? Z.of_nat (length saved))%Z then
        Err "Codegen: more variables to save than tinfo->args holds"
      else if (nursery_size <? Z.of_nat n)%Z then
        Err "Codegen: allocation of more words than the nursery holds"
      else
        Ret (Sset allocId tinfo_alloc ;;;
             Sifthenelse
               (Ebinop Olt (Ebinop Osub tinfo_limit alloc tintnat)
                       (const (Z.of_nat n) tintnat) tint)
               (save_args 0 saved ;;;
                Scall None (Evar gcArgsId gc_args_ty)
                      [tinfo; const (Z.of_nat (length saved)) tvalue;
                       const (Z.of_nat n) tvalue] ;;;
                load_args 0 saved ;;;
                read_roots reread 0 (st_slots st) ;;;
                Sset allocId tinfo_alloc)
               Sskip).

    (* Places the check before [e] if it belongs there *)
    Definition enter (st : state) (e : exp) : error (statement * state) :=
      if st_room st then Ret (Sskip, st)
      else if check_here e then
        s <- check_room st (live_vars e) (alloc_need e) ;;
        ret (s, with_room st)
      else Ret (Sskip, st).

    (** *** Variables that are needed after a call *)

    (* The variables in [roots] during a call after which [live] are needed *)
    Definition root_layout (st : state) (live : list var) : list var :=
      let k := length live in
      let stay := List.filter (fun x => in_list x live) (firstn k (st_slots st)) in
      let new := List.filter (fun x => negb (in_list x stay)) live in
      place k (st_slots st) new (fun x => in_list x live).

    (* [x], read from [roots] if its C variable was not read back *)
    Definition root_source (st : state) (x : var) : expr :=
      if in_list x (st_stale st) then
        match index_of x (st_slots st) with
        | Some j => root j
        | None => Etempvar x tvalue
        end
      else Etempvar x tvalue.

    (* Writes [new] to [roots] from position [i], except the variables already in place *)
    Fixpoint write_roots (st : state) (i : nat) (old new : list var) : statement :=
      match new with
      | [] => Sskip
      | x :: new' =>
        let same := match old with
                    | y :: _ => Pos.eqb x y
                    | [] => false
                    end in
        (if same then Sskip else Sassign (root i) (root_source st x)) ;;;
        write_roots st (S i) (tl old) new'
      end.

    (* [frame.root = roots; frame.prev = tinfo->fp; tinfo->fp = &frame] *)
    Definition link : statement :=
      Sassign (frame_field rootId (tptr tvalue)) roots ;;;
      Sassign (frame_field prevId (tptr frameT)) tinfo_fp ;;;
      Sassign tinfo_fp (Eaddrof frame (tptr frameT)).

    (* [frame.next = roots + k] *)
    Definition set_next (k : nat) : statement :=
      Sassign (frame_field nextId (tptr tvalue))
              (Ebinop Oadd roots (const (Z.of_nat k) tintnat) (tptr tvalue)).

    (* The statements before a call after which [live] are needed, and the state after it *)
    Definition push_roots (st : state) (live : list var) : statement * state :=
      let slots := root_layout st live in
      let k := length slots in
      let linked := st_linked st || (0 <? k)%nat in
      (write_roots st 0 (st_slots st) slots ;;;
       (if linked && negb (Nat.eqb k (length (st_slots st))) then set_next k else Sskip) ;;;
       (if linked && negb (st_linked st) then link else Sskip),
       mkState linked slots slots false false).

    (* After a call: reads back the variables that are in [used] *)
    Definition reload (st : state) (used : FVSet) : statement * state :=
      (read_roots (fun x => in_list x (st_stale st) && PS.mem x used) 0 (st_slots st),
       mkState (st_linked st) (st_slots st)
               (List.filter (fun x => negb (PS.mem x used)) (st_stale st))
               (st_room st) (st_dirty st)).

    (* The call [c] with result [x], followed by [e]. [k] translates [e]. *)
    Definition call_then (st : state) (c : statement) (x : var) (e : exp)
               (k : state -> error statement) : error statement :=
      let '(s_roots, st1) := push_roots st (live_after x e) in
      '(s_check, st2) <- enter st1 e ;;
      let '(s_reload, st3) := reload st2 (uses_now e) in
      s <- k st3 ;;
      ret (s_roots ;;; sync st ;;; c ;;; s_check ;;; s_reload ;;; s).

    (** *** Calls whose result is returned *)

    (* [ps] take the values of [ys], through [tmps] if a value is a parameter that changes *)
    Definition assign_params (ps ys : list var) : statement :=
      let moves := List.filter (fun m => negb (Pos.eqb (fst m) (snd m))) (combine ps ys) in
      let changed := map fst moves in
      if existsb (fun m => in_list (snd m) changed) moves then
        let moves := combine tmps moves in
        fold_right (fun m s => Sset (fst m) (var_expr (snd (snd m))) ;;; s) Sskip moves ;;;
        fold_right (fun m s => Sset (fst (snd m)) (Etempvar (fst m) tvalue) ;;; s) Sskip moves
      else
        fold_right (fun m s => Sset (fst m) (var_expr (snd m)) ;;; s) Sskip moves.

    (* Returns the result of the call of [f] with [ys]. [r] is a variable for the result. *)
    Definition tail_call (st : state) (r : ident) (f : var) (ys : list var) : error statement :=
      let other :=
          c <- call r f ys ;;
          ret (leave st ;;; c ;;; Sreturn (Some (Etempvar r tvalue))) in
      match self with
      | Some (g, ps) =>
        if Pos.eqb f g && Nat.eqb (length ys) (length ps) then
          Ret (leave st ;;; assign_params ps ys ;;; Scontinue)
        else other
      | None => other
      end.

    (** *** Expressions *)

    Fixpoint trans (st : state) (e : exp) {struct e} : error statement :=
      match e with
      | Econstr x t ys e' =>
        r <- ctor_rep_of t ;;
        match r with
        | Constant ordinal =>
          match ys with
          | [] =>
            s <- trans st e' ;;
            ret (Sset x (const (constant_value ordinal) tvalue) ;;; s)
          | _ => Err ("Codegen: constructor " ++ show_pos t ++ " takes no arguments")
          end
        | Block ordinal n =>
          if negb (Nat.eqb (length ys) n) then
            Err ("Codegen: wrong number of arguments for constructor " ++ show_pos t)
          else if st_room st then
            s <- trans (allocated st) e' ;;
            ret (new_block x (block_header ordinal (Z.of_nat n)) (Z.of_nat n) ;;;
                 store_fields x 0 (map var_expr ys) ;;; s)
          else Err "Codegen: allocation without a check for heap room"
        end
      | Eproj x _ n y e' =>
        s <- trans st e' ;;
        ret (Sset x (field (var_expr y) (Z.of_N n)) ;;; s)
      | Eprim_val x p e' =>
        if Nat.eqb (prim_val_words p) 0 then
          s <- trans st e' ;;
          ret (prim_val x p ;;; s)
        else if st_room st then
          s <- trans (allocated st) e' ;;
          ret (prim_val x p ;;; s)
        else Err "Codegen: allocation without a check for heap room"
      | Eprim x p ys e' =>
        match M.get p prims with
        | None => Err ("Codegen: unknown primitive " ++ show_pos p)
        | Some info =>
          if prim_alloc info then
            call_then st (prim_call x p true ys) x e' (fun st' => trans st' e')
          else
            s <- trans st e' ;;
            ret (prim_call x p false ys ;;; s)
        end
      | Ecase y cs =>
        cases <-
          (fix go (cs : list (ctor_tag * exp))
             : error (list (Z * statement) * list (Z * statement)) :=
             match cs with
             | [] => Ret ([], [])
             | (t, e') :: cs' =>
               r <- ctor_rep_of t ;;
               if clashes t r cs' then
                 Err "Codegen: two constructors of a case have the same ordinal"
               else
                 '(s_check, st') <- enter st e' ;;
                 s <- trans st' e' ;;
                 '(blocks, constants) <- go cs' ;;
                 match r with
                 | Block ordinal _ => ret ((ordinal, s_check ;;; s) :: blocks, constants)
                 | Constant ordinal =>
                   ret (blocks, (constant_value ordinal, s_check ;;; s) :: constants)
                 end
             end) cs ;;
        ret (case_stmt (var_expr y) (fst cases) (snd cases))
      | Eletapp x f _ ys e' =>
        if returns x e' then tail_call st x f ys
        else
          c <- call x f ys ;;
          call_then st c x e' (fun st' => trans st' e')
      | Eapp f _ ys => tail_call st resultId f ys
      | Ehalt x => Ret (leave st ;;; Sreturn (Some (var_expr x)))
      | Efun _ _ => Err "Codegen: function definition inside a function"
      end.

  End Body.

  (** ** Functions *)

  (* [n] identifiers from [p] *)
  Fixpoint idents_from (p : positive) (n : nat) : list ident :=
    match n with
    | O => []
    | S n' => p :: idents_from (Pos.succ p) n'
    end.

  (* [f] is [None] for the main expression. [tmp] is the first identifier for [tmps]. *)
  Definition translate_function (tmp : positive) (f : option var) (ps : list var) (e : exp)
    : error function :=
    if (max_args <? Z.of_nat (length ps))%Z then
      Err "Codegen: function with more parameters than tinfo->args holds"
    else
      let nroots := max_roots e in
      if (Ptrofs.max_signed <? 8 * Z.of_nat nroots)%Z then
        Err "Codegen: function with more roots than fit in memory"
      else
        let self := option_map (fun f => (f, ps)) f in
        let loops := match f with
                     | Some f => calls_itself f (length ps) e
                     | None => false
                     end in
        let tmps := idents_from tmp (length ps) in
        '(s_check, st) <- enter (Z.of_nat nroots) init_state e ;;
        s <- trans self (Z.of_nat nroots) tmps st e ;;
        let code := s_check ;;; s in
        let body := load_args nparam (skipn nparam ps) ;;;
                    (if loops then Sloop code Sskip else code) in
        let added := (allocId, tptr tvalue) :: (resultId, tvalue) :: (boxedId, tbool) ::
                     map (fun x => (x, tvalue)) tmps in
        ret (mkfunction
               tvalue cc_default
               ((tinfoId, tptr tinfoT) :: map (fun x => (x, tvalue)) (firstn nparam ps))
               (if Nat.eqb nroots 0 then []
                else [(frameId, frameT); (rootsId, tarray tvalue (Z.of_nat nroots))])
               (map (fun x => (x, tvalue)) (skipn nparam ps ++ bound_vars e) ++
                List.filter (fun d => assigns (fst d) body) added)%list
               body).

  Fixpoint translate_fundefs (tmp : positive) (fds : fundefs)
    : error (list (ident * globdef fundef type)) :=
    match fds with
    | Fnil => Ret []
    | Fcons f _ ps e fds' =>
      fn <- translate_function tmp (Some f) ps e ;;
      rest <- translate_fundefs tmp fds' ;;
      ret ((f, Gfun (Internal fn)) :: rest)
    end.

End Translation.

(** * Programs *)

Fixpoint fun_arities (fds : fundefs) : M.t nat :=
  match fds with
  | Fnil => M.empty nat
  | Fcons f _ ps _ fds' => M.set f (length ps) (fun_arities fds')
  end.

Fixpoint max_arity (fds : fundefs) : nat :=
  match fds with
  | Fnil => 0%nat
  | Fcons _ _ ps _ fds' => Nat.max (length ps) (max_arity fds')
  end.

(* The declaration of a function that is defined in another file *)
Definition external (name : string) (params : list type) (res : type) : globdef fundef type :=
  Gfun (External (EF_external (String.to_string name) (signature_of_type params res cc_default))
                 params res cc_default).

(* The functions of [gc_stack.h] that the code calls *)
Definition runtime_defs : list (ident * globdef fundef type) :=
  [ (gcArgsId, external "garbage_collect_args" gc_args_params tvoid);
    (isPtrId, external "certirocq_is_ptr" is_ptr_params tbool) ].

(* The printed programs have no [types]: the printed file includes [gc_stack.h] *)
Definition make_program (types : list composite_definition)
           (defs : list (ident * globdef fundef type)) : error Clight.program :=
  match Ctypes.make_program types defs [bodyId] mainId with
  | Errors.OK p => Ret p
  | Errors.Error _ => Err "Codegen: could not build the Clight program"
  end.

(* The names for printing. Pipeline names get their identifier as a suffix. *)
Definition make_names (body_name : string) (tmps : list ident) (nenv : name_env) : name_env :=
  let nenv := fold_left (fun m x => M.set x (nNamed "tmp") m) tmps nenv in
  let nenv := M.map (fun x n => match n with
                                | nAnon => nAnon
                                | nNamed s => nNamed (s ++ "_" ++ show_pos x)
                                end) nenv in
  fold_left (fun m d => M.set (fst d) (nNamed (snd d)) m) (reserved_names body_name) nenv.

(* The functions of the runtime, the functions of [e] and the function for its main
   expression *)
Definition translate_program (nparam : nat) (prims : M.t primitive) (cenv : ctor_env)
           (tmp : positive) (e : exp) : error (list (ident * globdef fundef type)) :=
  let '(fds, main) := match e with
                      | Efun fds main => (fds, main)
                      | _ => (Fnil, e)
                      end in
  let fenv := fun_arities fds in
  funs <- translate_fundefs nparam prims cenv fenv tmp fds ;;
  body <- translate_function nparam prims cenv fenv tmp None [] main ;;
  ret (runtime_defs ++ funs ++ [(bodyId, Gfun (Internal body))])%list.

(* Returns the names for printing, the header program and the program *)
Definition compile (body_name : string) (nparam : nat) (prims : M.t primitive) (e : exp)
           (cenv : ctor_env) (nenv : name_env)
  : error (name_env * Clight.program * Clight.program) :=
  if Archi.ptr64 then
    (* An identifier above those of the program, the primitives and the names *)
    let top := M.fold (fun m x _ => Pos.max m x) nenv
                      (M.fold (fun m x _ => Pos.max m x) prims (max_var e 100%positive)) in
    let tmp := Pos.succ top in
    let ntmps := match e with
                 | Efun fds _ => max_arity fds
                 | _ => 0%nat
                 end in
    defs <- translate_program nparam prims cenv tmp e ;;
    prog <- make_program [] defs ;;
    header <- make_program [] [(bodyId, external body_name [tptr tinfoT] tvalue)] ;;
    ret (make_names body_name (idents_from tmp ntmps) nenv, header, prog)
  else Err "Codegen: only 64-bit targets are supported".
