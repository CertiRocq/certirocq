(** * Syntactic properties of the LambdaANF -> LLVM (VIR) emitter

    Purely syntactic facts about [translate_cfg] / [mk_fun] / [compile_prog]
    ([LambdaANF_to_LLVM.v]) needed by the semantic correctness proof:

    - shape (unfolding) equations for every constructor (Sect. 1);
    - the label supply is monotone and every emitted CFG is non-empty, with
      labels [Anon (Zpos p)] in [fresh, fresh'), pairwise distinct, an entry
      block without phis, closed successor sets, and phis only at blocks whose
      CFG predecessors are exactly the two incoming labels of every phi
      (the [Econstr]-head alloc blocks) (Sect. 3, [translate_cfg_ok]);
    - every SSA name written is an ANF binder [Raw (Zpos x)] or an
      [ntmp]/[ssname] temporary seeded in [fresh, fresh'); [ssname] is
      injective and disjoint from [ntmp] and ANF names (Sect. 2/3);
    - the same structure for [mk_fun] / [compile_prog] (Sect. 4).

    None of the results needs [body_ok]: they hold for every [term.exp]. *)

From Stdlib Require Import ZArith NArith List Lia Bool.
From Stdlib Require String.
Import String.
From CertiRocq.LambdaANF Require Import term identifiers set_util.
From CertiRocq.Common Require Import AstCommon.
From CertiRocq.CodegenLLVM Require Import LambdaANF_to_LLVM.
From Vellvm Require Import Syntax.LLVMAst.
Import ListNotations.
Local Notation exp := term.exp.

(* ------------------------------------------------------------------ *)
(** ** 0. Auxiliary syntactic notions *)

(** Successor labels of a terminator / block. *)
Definition term_succs (t : terminator typ) : list block_id :=
  match t with
  | TERM_Br _ l1 l2 => [l1; l2]
  | TERM_Br_1 l => [l]
  | TERM_Switch _ d brs => d :: map snd brs
  | TERM_IndirectBr _ ls => ls
  | TERM_Invoke _ _ l1 l2 _ _ => [l1; l2]
  | _ => []
  end.

Definition bsuccs (b : block typ) : list block_id := term_succs (snd (fst (blk_term b))).

(** SSA names written by a code sequence / phi list / block. *)
Fixpoint code_defs (c : code typ) : list raw_id :=
  match c with
  | [] => []
  | i :: c' => match fst (fst i) with IId r => r :: code_defs c' | IVoid _ => code_defs c' end
  end.

Definition phi_defs (ps : list (local_id * phi typ * list (metadata typ))) : list raw_id :=
  map (fun p => fst (fst p)) ps.

Definition def_ids (b : block typ) : list raw_id := phi_defs (blk_phis b) ++ code_defs (blk_code b).

Definition lbl_in (lo hi : positive) (l : block_id) : Prop :=
  exists p, l = Anon (Zpos p) /\ (lo <= p)%positive /\ (p < hi)%positive.

(** An SSA name legitimately written by the translation of [e] with label/seed
    supply [lo, hi). *)
Definition local_ok (e : exp) (lo hi : positive) (r : raw_id) : Prop :=
  (exists x, r = Raw (Zpos x) /\ bound_var e x) \/
  (exists s, (lo <= s)%positive /\ (s < hi)%positive /\
             (r = ntmp s 1 \/ exists k, r = ssname s k)).

Definition phi_args_ok (lc lg : block_id) (p : local_id * phi typ * list (metadata typ)) : Prop :=
  match snd (fst p) with Phi _ args => map fst args = [lc; lg] end.

(** A block with phis: every phi has exactly the incoming labels [lc; lg], and
    the blocks of [blks] branching to it are exactly the blocks labelled [lc]
    and [lg]. *)
Definition phi_ok (blks : list (block typ)) (b : block typ) : Prop :=
  exists lc lg, In lc (map blk_id blks) /\ In lg (map blk_id blks) /\ lc <> lg /\
    Forall (phi_args_ok lc lg) (blk_phis b) /\
    forall b', In b' blks -> (In (blk_id b) (bsuccs b') <-> blk_id b' = lc \/ blk_id b' = lg).

Definition closed (blks : list (block typ)) : Prop :=
  forall b, In b blks -> forall l, In l (bsuccs b) -> In l (map blk_id blks).

Definition phis_ok (blks : list (block typ)) : Prop :=
  forall b, In b blks -> blk_phis b <> [] -> phi_ok blks b.

Record cfg_ok (e : exp) (lo hi : positive) (blks : list (block typ)) : Prop := {
  co_lt    : (lo < hi)%positive;
  co_ne    : blks <> [];
  co_lbl   : Forall (fun b => lbl_in lo hi (blk_id b)) blks;
  co_nodup : NoDup (map blk_id blks);
  co_entry : forall b rest, blks = b :: rest -> blk_phis b = [];
  co_closed : closed blks;
  co_phis  : phis_ok blks;
  co_defs  : forall b, In b blks -> forall r, In r (def_ids b) -> local_ok e lo hi r }.

(* ------------------------------------------------------------------ *)
(** ** 1. Shape equations *)

(** The nested [arm_loop] of the [Ecase] case, as a standalone function of the
    recursive translation [tr]. *)
Definition arm_loop_d (tr : exp -> positive -> list (block typ) * positive)
         (get_ord get_arity : ctor_tag -> N) :=
  fix arm_loop (arms : list (ctor_tag * exp)) (fr : positive) {struct arms}
    : list (block typ) * list (N * (tint_literal * block_id)) * positive :=
  match arms with
  | [] => ([], [], fr)
  | (t, ae) :: rest =>
      let '(ablks, fr1) := tr ae fr in
      let lbl := match ablks with b :: _ => blk_id b | [] => Anon (Zpos fr) end in
      let '(rblks, redges, fr2) := arm_loop rest fr1 in
      ((ablks ++ rblks)%list,
       (get_arity t, (TInt_Literal 64 (Nat.to_num_int (N.to_nat (get_ord t))), lbl)) :: redges,
       fr2)
  end.

Definition entry_id (blks : list (block typ)) (dflt : positive) : block_id :=
  match blks with b :: _ => blk_id b | [] => Anon (Zpos dflt) end.

Definition case_test_blk (env : nenv) (y : var) (f1 : positive) : block typ :=
  mk_block (Anon (Zpos (Pos.succ (Pos.succ f1)))) [] []
    (IVoid 3%Z, TERM_Br (TYPE_I 1%positive, is_block (nvar env y))
                  (Anon (Zpos f1)) (Anon (Zpos (Pos.succ f1))), [])
    None.

Definition case_unboxed_blk (env : nenv) (y : var) (f1 : positive) (dflt : block_id)
           (aedges : list (N * (tint_literal * block_id))) : block typ :=
  mk_block (Anon (Zpos (Pos.succ f1))) [] []
    (IVoid 4%Z, TERM_Switch (val_ty, long_val (nvar env y)) dflt
                  (map snd (List.filter (fun ae => N.eqb (fst ae) 0) aedges)), [])
    None.

Definition case_boxed_blk (env : nenv) (y : var) (f1 : positive) (dflt : block_id)
           (aedges : list (N * (tint_literal * block_id))) : block typ :=
  mk_block (Anon (Zpos f1)) []
    [ (IId (ntmp f1 1), load_header env y, []) ]
    (IVoid 5%Z,
     TERM_Switch
       (val_ty, OP_IBinop And val_ty (EXP_Ident (ID_Local (ntmp f1 1))) (lit 1023))
       dflt (map snd (List.filter (fun ae => negb (N.eqb (fst ae) 0)) aedges)), [])
    None.

Definition case_result (env : nenv) (y : var)
           (r : list (block typ) * list (N * (tint_literal * block_id)) * positive)
  : list (block typ) * positive :=
  let '(arm_blks, aedges, f1) := r in
  let dflt := entry_id arm_blks (Pos.succ (Pos.succ f1)) in
  ( case_test_blk env y f1 :: case_unboxed_blk env y f1 dflt aedges
      :: case_boxed_blk env y f1 dflt aedges :: arm_blks,
    Pos.succ (Pos.succ (Pos.succ f1)) ).

(** Boxed [Econstr] chunk head. *)
Definition hd_nwords (ys : list var) : N := (1 + N.of_nat (List.length ys))%N.

Definition hd_roots (fs : list positive) (x : var) (ys : list var) (e' : exp) : list var :=
  List.filter (fun v => negb (is_fun fs v))
    (nodup Pos.eq_dec (List.remove Pos.eq_dec x (PS.elements (exp_fv e')) ++ ys)%list).

Definition hd_env (fs : list positive) (env : nenv) (fresh : positive) (x : var)
           (ys : list var) (e' : exp) : nenv :=
  safepoint_env env fresh (hd_roots fs x ys e').

Definition hd_check_blk (fs : list positive) (x : var) (ys : list var) (e' : exp)
           (fresh f0 : positive) : block typ :=
  let roots := hd_roots fs x ys e' in
  let arr_ty := TYPE_Array (N.of_nat (List.length roots)) val_ty in
  let cwn := N.to_nat (hd_nwords ys + chunk_words e')%N in
  mk_block (Anon (Zpos f0)) []
    [ (IId (ssname fresh 1), INSTR_Alloca arr_ty [], []);
      (IId (ssname fresh 2), INSTR_Alloca frame_ty [], []);
      (IId (ssname fresh 3), INSTR_Load ptr_ty (ptr_ty, gep_tinfo 0) [], []);
      (IId (ssname fresh 4), INSTR_Load ptr_ty (ptr_ty, gep_tinfo 1) [], []);
      (IId (ssname fresh 5),
       INSTR_Op (OP_IBinop (Sub false false) val_ty
                  (OP_Conversion (CONV_Impure Ptrtoint) ptr_ty (EXP_Ident (ID_Local (ssname fresh 4))) val_ty)
                  (OP_Conversion (CONV_Impure Ptrtoint) ptr_ty (EXP_Ident (ID_Local (ssname fresh 3))) val_ty)), []);
      (IId (ssname fresh 6),
       INSTR_Op (OP_ICmp false Uge val_ty (EXP_Ident (ID_Local (ssname fresh 5))) (lit (8 * cwn))), []) ]
    (IVoid 2%Z,
     TERM_Br (TYPE_I 1%positive, EXP_Ident (ID_Local (ssname fresh 6)))
       (Anon (Zpos (Pos.succ (Pos.succ f0)))) (Anon (Zpos (Pos.succ f0))), [])
    None.

Definition hd_gc_blk (fs : list positive) (env : nenv) (x : var) (ys : list var) (e' : exp)
           (fresh f0 : positive) : block typ :=
  let roots := hd_roots fs x ys e' in
  let nr := List.length roots in
  let arr_ty := TYPE_Array (N.of_nat nr) val_ty in
  let cwn := N.to_nat (hd_nwords ys + chunk_words e')%N in
  let rootse := EXP_Ident (ID_Local (ssname fresh 1)) in
  let framee := EXP_Ident (ID_Local (ssname fresh 2)) in
  let prevR := EXP_Ident (ID_Local (ssname fresh 10)) in
  mk_block (Anon (Zpos (Pos.succ f0))) []
    (( spill_code env rootse arr_ty 0 roots
      ++ [ (IVoid 0%Z, INSTR_Store (tinfo_ty, gep_arr arr_ty rootse nr)
              (tinfo_ty, gep_struct frame_ty framee 0) [], []);
           (IVoid 0%Z, INSTR_Store (tinfo_ty, gep_arr arr_ty rootse 0)
              (tinfo_ty, gep_struct frame_ty framee 1) [], []);
           (IId (ssname fresh 10), INSTR_Load tinfo_ty (tinfo_ty, gep_tinfo 4) [], []);
           (IVoid 0%Z, INSTR_Store (tinfo_ty, prevR)
              (tinfo_ty, gep_struct frame_ty framee 2) [], []);
           (IVoid 0%Z, INSTR_Store (tinfo_ty, framee) (tinfo_ty, gep_tinfo 4) [], []);
           (IVoid 0%Z, INSTR_Store (val_ty, lit cwn) (ptr_ty, gep_tinfo 5) [], []);
           (IVoid 0%Z,
            INSTR_Call (TYPE_Void, EXP_Ident (ID_Global (Name "garbage_collect"%string)))
              [ ((tinfo_ty, etinfo), @nil param_attr) ] [] [], []) ]
      ++ reload_code fresh rootse arr_ty 0 roots
      ++ [ (IVoid 0%Z, INSTR_Store (tinfo_ty, prevR) (tinfo_ty, gep_tinfo 4) [], []) ] )%list)
    (IVoid 5%Z, TERM_Br_1 (Anon (Zpos (Pos.succ (Pos.succ f0)))), [])
    None.

(** The allocation sequence shared by chunk heads (under [hd_env]) and chunk
    members (under [env]). *)
Definition alloc_code (go ga : ctor_tag -> N) (fs : list positive) (env : nenv)
           (fresh : positive) (x : var) (t : ctor_tag) (ys : list var) : code typ :=
  let a0e := EXP_Ident (ID_Local (ssname fresh 7)) in
  let vpe := EXP_Ident (ID_Local (ssname fresh 8)) in
  ( (IId (ssname fresh 7), INSTR_Load ptr_ty (ptr_ty, gep_tinfo 0) [], [])
    :: (IVoid 6%Z, INSTR_Store (val_ty, header_word go ga t) (ptr_ty, gep_at a0e 0) [], [])
    :: (IId (ssname fresh 8), INSTR_Op (gep_at a0e 1), [])
    :: store_fields fs env vpe 0 ys
    ++ (IId (Raw (Zpos x)), INSTR_Op (OP_Conversion (CONV_Impure Ptrtoint) ptr_ty vpe val_ty), [])
    :: (IId (ssname fresh 9), INSTR_Op (gep_at a0e (hd_nwords ys)), [])
    :: (IVoid 7%Z, INSTR_Store (ptr_ty, EXP_Ident (ID_Local (ssname fresh 9))) (ptr_ty, gep_tinfo 0) [], [])
    :: [] )%list.

Definition hd_alloc_blk (go ga : ctor_tag -> N) (fs : list positive) (env : nenv)
           (x : var) (t : ctor_tag) (ys : list var) (e' : exp)
           (fresh f0 : positive) (klbl : block_id) : block typ :=
  mk_block (Anon (Zpos (Pos.succ (Pos.succ f0))))
    (phi_list env fresh (Anon (Zpos f0)) (Anon (Zpos (Pos.succ f0))) 0 (hd_roots fs x ys e'))
    (alloc_code go ga fs (hd_env fs env fresh x ys e') fresh x t ys)
    (IVoid 8%Z, TERM_Br_1 klbl, [])
    None.

(** [Eletapp] safepoint. *)
Definition la_roots (fs : list positive) (x : var) (e' : exp) : list var :=
  List.filter (fun v => negb (is_fun fs v))
    (nodup Pos.eq_dec (List.remove Pos.eq_dec x (PS.elements (exp_fv e')))).

Definition la_env (fs : list positive) (env : nenv) (fresh : positive) (x : var) (e' : exp) : nenv :=
  let roots := la_roots fs x e' in
  env_set_list env roots (map (fun i => ssname fresh (1000 + i)) (seq 0 (List.length roots))).

Definition la_code (fs : list positive) (env : nenv) (fresh : positive) (x f : var)
           (ys : list var) (e' : exp) : code typ :=
  let roots := la_roots fs x e' in
  let nr := List.length roots in
  let arr_ty := TYPE_Array (N.of_nat nr) val_ty in
  let rootse := EXP_Ident (ID_Local (ssname fresh 1)) in
  let framee := EXP_Ident (ID_Local (ssname fresh 2)) in
  let prevR := EXP_Ident (ID_Local (ssname fresh 3)) in
  ( (IId (ssname fresh 1), INSTR_Alloca arr_ty [], [])
    :: (IId (ssname fresh 2), INSTR_Alloca frame_ty [], [])
    :: spill_code env rootse arr_ty 0 roots
    ++ [ (IVoid 0%Z, INSTR_Store (tinfo_ty, gep_arr arr_ty rootse nr)
            (tinfo_ty, gep_struct frame_ty framee 0) [], []);
         (IVoid 0%Z, INSTR_Store (tinfo_ty, gep_arr arr_ty rootse 0)
            (tinfo_ty, gep_struct frame_ty framee 1) [], []);
         (IId (ssname fresh 3), INSTR_Load tinfo_ty (tinfo_ty, gep_tinfo 4) [], []);
         (IVoid 0%Z, INSTR_Store (tinfo_ty, prevR)
            (tinfo_ty, gep_struct frame_ty framee 2) [], []);
         (IVoid 0%Z, INSTR_Store (tinfo_ty, framee) (tinfo_ty, gep_tinfo 4) [], []);
         (IId (Raw (Zpos x)),
          INSTR_Call (val_ty, gcallee fs env f) (call_args fs env ys) [] [], []) ]
    ++ reload_code fresh rootse arr_ty 0 roots
    ++ [ (IVoid 0%Z, INSTR_Store (tinfo_ty, prevR) (tinfo_ty, gep_tinfo 4) [], []) ] )%list.

Definition prim_call (po : positive -> option (String.string * bool)) (fs : list positive)
           (env : nenv) (p : prim) (ys : list var) : instr typ :=
  let args := map (fun y => ((val_ty, gvar fs env y), @nil param_attr)) ys in
  match po p with
  | Some (name, false) => INSTR_Call (val_ty, EXP_Ident (ID_Global (Name name))) args [] []
  | Some (name, true) =>
      INSTR_Call (val_ty, EXP_Ident (ID_Global (Name name)))
        (((tinfo_ty, etinfo), @nil param_attr) :: args) [] []
  | None => INSTR_Call (val_ty, EXP_Ident (ID_Global (Name "certirocq_prim"%string))) args [] []
  end.

Definition prim_val_exp (pv : primitive_value) : LLVMAst.exp typ :=
  match prim_val_Z pv with
  | Some z => val_long (litZ z)
  | None => val_long (lit 0)
  end.

Section Shape.
Variables (go ga : ctor_tag -> N) (po : positive -> option (String.string * bool))
          (fs : list positive).
Notation tr := (translate_cfg go ga po fs).

Lemma tr_halt env chunk x fresh :
  tr env chunk (Ehalt x) fresh =
  ([ mk_block (Anon (Zpos fresh)) [] [] (IVoid 1%Z, TERM_Ret (val_ty, gvar fs env x), []) None ],
   Pos.succ fresh).
Proof. reflexivity. Qed.

Lemma tr_app env chunk f ft ys fresh :
  tr env chunk (Eapp f ft ys) fresh =
  ([ mk_block (Anon (Zpos fresh)) []
       [ (IId (ntmp fresh 1), INSTR_Call (val_ty, gcallee fs env f) (call_args fs env ys) [] [], []) ]
       (IVoid 1%Z, TERM_Ret (val_ty, EXP_Ident (ID_Local (ntmp fresh 1))), []) None ],
   Pos.succ fresh).
Proof. reflexivity. Qed.

Lemma tr_proj env chunk x t n y e' fresh blks f' :
  tr env chunk e' fresh = (blks, f') ->
  tr env chunk (Eproj x t n y e') fresh =
  (prepend_code [ (IId (Raw (Zpos x)), load_field env y n, []) ] blks, f').
Proof. intros H. cbn [translate_cfg]. rewrite H. reflexivity. Qed.

Lemma tr_constr_nil env chunk x t e' fresh blks f' :
  tr env chunk e' fresh = (blks, f') ->
  tr env chunk (Econstr x t [] e') fresh =
  (prepend_code [ (IId (Raw (Zpos x)), INSTR_Op (val_long (lit (N.to_nat (go t)))), []) ] blks, f').
Proof. intros H. cbn [translate_cfg]. rewrite H. reflexivity. Qed.

Lemma tr_constr_member env chunk x t ys e' fresh blks f' :
  ys <> [] -> N.leb (hd_nwords ys) chunk = true ->
  tr env (chunk - hd_nwords ys)%N e' (Pos.succ fresh) = (blks, f') ->
  tr env chunk (Econstr x t ys e') fresh =
  (prepend_code (alloc_code go ga fs env fresh x t ys) blks, f').
Proof.
  intros Hys Hl H. destruct ys as [|y ys]; [congruence|].
  cbn [translate_cfg]. unfold hd_nwords in *. rewrite Hl, H. reflexivity.
Qed.

Lemma tr_constr_head env chunk x t ys e' fresh blks f0 :
  ys <> [] -> N.leb (hd_nwords ys) chunk = false ->
  tr (hd_env fs env fresh x ys e') (chunk_words e') e' (Pos.succ fresh) = (blks, f0) ->
  tr env chunk (Econstr x t ys e') fresh =
  (hd_check_blk fs x ys e' fresh f0 :: hd_gc_blk fs env x ys e' fresh f0
     :: hd_alloc_blk go ga fs env x t ys e' fresh f0 (entry_id blks f0) :: blks,
   Pos.succ (Pos.succ (Pos.succ f0))).
Proof.
  intros Hys Hl H. destruct ys as [|y ys]; [congruence|].
  cbn [translate_cfg]. unfold hd_nwords in *. rewrite Hl.
  replace ((1 + N.of_nat (List.length (y :: ys)) + chunk_words e') - (1 + N.of_nat (List.length (y :: ys))))%N
    with (chunk_words e') by lia.
  unfold hd_env, hd_roots in H. rewrite H. reflexivity.
Qed.

Lemma tr_prim env chunk x p ys e' fresh blks f' :
  tr env 0%N e' fresh = (blks, f') ->
  tr env chunk (Eprim x p ys e') fresh =
  (prepend_code [ (IId (Raw (Zpos x)), prim_call po fs env p ys, []) ] blks, f').
Proof. intros H. cbn [translate_cfg]. rewrite H. reflexivity. Qed.

Lemma tr_prim_val env chunk x pv e' fresh blks f' :
  tr env chunk e' fresh = (blks, f') ->
  tr env chunk (Eprim_val x pv e') fresh =
  (prepend_code [ (IId (Raw (Zpos x)), INSTR_Op (prim_val_exp pv), []) ] blks, f').
Proof. intros H. cbn [translate_cfg]. rewrite H. reflexivity. Qed.

Lemma tr_letapp env chunk x f ft ys e' fresh blks f' :
  tr (la_env fs env fresh x e') 0%N e' (Pos.succ fresh) = (blks, f') ->
  tr env chunk (Eletapp x f ft ys e') fresh =
  (prepend_code (la_code fs env fresh x f ys e') blks, f').
Proof. intros H. cbn [translate_cfg]. unfold la_env, la_roots in H. rewrite H. reflexivity. Qed.

Lemma tr_fun env chunk fds e' fresh :
  tr env chunk (Efun fds e') fresh = tr env 0%N e' fresh.
Proof. reflexivity. Qed.

Lemma tr_case_unfold env chunk y arms fresh :
  tr env chunk (Ecase y arms) fresh =
  case_result env y (arm_loop_d (fun ae fr => tr env 0%N ae fr) go ga arms fresh).
Proof. reflexivity. Qed.

Lemma tr_case env chunk y arms fresh arm_blks aedges f1 :
  arm_loop_d (fun ae fr => tr env 0%N ae fr) go ga arms fresh = (arm_blks, aedges, f1) ->
  tr env chunk (Ecase y arms) fresh =
  (case_test_blk env y f1
     :: case_unboxed_blk env y f1 (entry_id arm_blks (Pos.succ (Pos.succ f1))) aedges
     :: case_boxed_blk env y f1 (entry_id arm_blks (Pos.succ (Pos.succ f1))) aedges
     :: arm_blks,
   Pos.succ (Pos.succ (Pos.succ f1))).
Proof. intros H. rewrite tr_case_unfold, H. reflexivity. Qed.

Lemma arm_loop_nil tr' fr : arm_loop_d tr' go ga [] fr = ([], [], fr).
Proof. reflexivity. Qed.

Lemma arm_loop_cons tr' t ae rest fr ablks fr1 :
  tr' ae fr = (ablks, fr1) ->
  arm_loop_d tr' go ga ((t, ae) :: rest) fr =
  (let '(rblks, redges, fr2) := arm_loop_d tr' go ga rest fr1 in
   ((ablks ++ rblks)%list,
    (ga t, (TInt_Literal 64 (Nat.to_num_int (N.to_nat (go t))), entry_id ablks fr)) :: redges,
    fr2)).
Proof. intros H. simpl. rewrite H. reflexivity. Qed.

End Shape.

(* ------------------------------------------------------------------ *)
(** ** 2. SSA name generators: injectivity and disjointness *)

Definition tri (n : N) : N := (n * (n + 1) / 2)%N.

Lemma tri_succ n : tri (n + 1) = (tri n + (n + 1))%N.
Proof.
  unfold tri.
  replace ((n + 1) * (n + 1 + 1))%N with (n * (n + 1) + (n + 1) * 2)%N by ring.
  rewrite N.div_add by lia. reflexivity.
Qed.

Lemma tri_mono n m : (n <= m)%N -> (tri n <= tri m)%N.
Proof. intros H. unfold tri. apply N.Div0.div_le_mono. nia. Qed.

Lemma cantor_tri a b : cantor a b = (tri (a + b) + b)%N.
Proof. reflexivity. Qed.

Lemma cantor_inj a b a' b' : cantor a b = cantor a' b' -> a = a' /\ b = b'.
Proof.
  rewrite !cantor_tri. intros H.
  assert (Hs : (a + b = a' + b')%N).
  { destruct (N.lt_trichotomy (a + b) (a' + b')) as [Hlt|[Heq|Hlt]]; [exfalso| exact Heq | exfalso].
    - pose proof (tri_mono (a + b + 1) (a' + b') ltac:(lia)). rewrite tri_succ in H0. lia.
    - pose proof (tri_mono (a' + b' + 1) (a + b) ltac:(lia)). rewrite tri_succ in H0. lia. }
  rewrite Hs in H. lia.
Qed.

Lemma ssname_inj s k s' k' : ssname s k = ssname s' k' -> s = s' /\ k = k'.
Proof.
  unfold ssname. intros H. injection H as H.
  apply (f_equal Npos) in H. rewrite !N.succ_pos_spec in H.
  apply N.succ_inj in H. apply cantor_inj in H as [H1 H2].
  split; [congruence | lia].
Qed.

Lemma ntmp_inj s k s' k' :
  (k < 16)%positive -> (k' < 16)%positive -> ntmp s k = ntmp s' k' -> s = s' /\ k = k'.
Proof. unfold ntmp. intros H1 H2 H. injection H as H. lia. Qed.

Lemma ssname_not_ntmp s k s' k' : ssname s k <> ntmp s' k'.
Proof. unfold ssname, ntmp. discriminate. Qed.

Lemma ssname_not_pos s k x : ssname s k <> Raw (Zpos x).
Proof. unfold ssname. discriminate. Qed.

Lemma ntmp_not_pos s k x : ntmp s k <> Raw (Zpos x).
Proof. unfold ntmp. discriminate. Qed.

Lemma local_ok_raw e lo hi r : local_ok e lo hi r -> exists z, r = Raw z.
Proof.
  intros [(x & -> & _) | (s & _ & _ & [-> | (k & ->)])]; eexists; reflexivity.
Qed.

Lemma local_ok_not_tinfo e lo hi : ~ local_ok e lo hi (Name "tinfo").
Proof. intros H. apply local_ok_raw in H as [z H]. discriminate. Qed.

Lemma local_ok_mono e e' lo hi lo' hi' r :
  local_ok e lo hi r -> (lo' <= lo)%positive -> (hi <= hi')%positive ->
  (forall x, bound_var e x -> bound_var e' x) -> local_ok e' lo' hi' r.
Proof.
  intros [(x & -> & Hx) | (s & H1 & H2 & H3)] Hl Hh Hb.
  - left. eauto.
  - right. exists s. repeat split; auto; lia.
Qed.

(* ------------------------------------------------------------------ *)
(** ** Generic list / CFG lemmas *)

Lemma NoDup_app_intro {A} (l1 l2 : list A) :
  NoDup l1 -> NoDup l2 -> (forall a, In a l1 -> In a l2 -> False) -> NoDup (l1 ++ l2).
Proof.
  induction l1 as [|a l1 IH]; intros H1 H2 Hd; simpl; auto.
  inversion H1; subst. constructor.
  - rewrite in_app_iff. intros [H|H]; [contradiction|]. eapply Hd; [left|]; eauto.
  - apply IH; auto. intros b Hb1 Hb2. eapply Hd; [right|]; eauto.
Qed.

Lemma NoDup_app_disj {A} (l1 l2 : list A) a :
  NoDup (l1 ++ l2) -> In a l1 -> In a l2 -> False.
Proof.
  induction l1 as [|b l1 IH]; intros Hn H1 H2; [destruct H1|].
  inversion Hn; subst. destruct H1 as [->|H1].
  - apply H3. apply in_app_iff. auto.
  - eauto.
Qed.

Lemma NoDup_app_l {A} (l1 l2 : list A) : NoDup (l1 ++ l2) -> NoDup l1.
Proof.
  induction l1 as [|a l1 IH]; intros H; [constructor|].
  inversion H; subst. constructor; auto. intros Ha. apply H2, in_app_iff; auto.
Qed.

Lemma NoDup_app_r {A} (l1 l2 : list A) : NoDup (l1 ++ l2) -> NoDup l2.
Proof. induction l1 as [|a l1 IH]; intros H; auto. inversion H; subst; auto. Qed.

Lemma NoDup_map_inj {A B} (f : A -> B) l a b :
  NoDup (map f l) -> In a l -> In b l -> f a = f b -> a = b.
Proof.
  induction l as [|c l IH]; intros Hn Ha Hb Hf; [destruct Ha|].
  simpl in Hn. inversion Hn; subst.
  destruct Ha as [->|Ha], Hb as [->|Hb]; auto.
  - exfalso. apply H1. rewrite Hf. apply in_map; auto.
  - exfalso. apply H1. rewrite <- Hf. apply in_map; auto.
Qed.

Lemma lbl_in_map lo hi (blks : list (block typ)) l :
  Forall (fun b => lbl_in lo hi (blk_id b)) blks -> In l (map blk_id blks) -> lbl_in lo hi l.
Proof.
  intros HF Hl. apply in_map_iff in Hl as (b & <- & Hb).
  rewrite Forall_forall in HF. auto.
Qed.

Lemma lbl_in_weaken lo hi lo' hi' l :
  lbl_in lo hi l -> (lo' <= lo)%positive -> (hi <= hi')%positive -> lbl_in lo' hi' l.
Proof. intros (p & -> & H1 & H2) H3 H4. exists p. repeat split; lia. Qed.

Lemma lbl_in_neq lo hi l q :
  lbl_in lo hi l -> ((q < lo)%positive \/ (hi <= q)%positive) -> l <> Anon (Zpos q).
Proof. intros (p & -> & H1 & H2) Hq H. injection H as H. lia. Qed.

Lemma lbl_in_disj lo hi lo' hi' l :
  lbl_in lo hi l -> lbl_in lo' hi' l -> (hi <= lo')%positive -> False.
Proof. intros (p & -> & H1 & H2) (p' & H & H3 & H4) H5. injection H as ->. lia. Qed.

(** Joining an outer block list [O] in front of a closed inner list [B]: the
    outer blocks may branch into [B] only to phi-free blocks. *)
Lemma join_ok (O B : list (block typ)) :
  NoDup (map blk_id (O ++ B)) ->
  (forall b, In b O -> forall l, In l (bsuccs b) ->
     In l (map blk_id O) \/ exists bb, In bb B /\ blk_id bb = l /\ blk_phis bb = []) ->
  closed B -> phis_ok O -> phis_ok B ->
  closed (O ++ B) /\ phis_ok (O ++ B).
Proof.
  intros Hnd HO HB PO PB.
  rewrite map_app in Hnd.
  pose proof (NoDup_app_r _ _ Hnd) as HndB.
  split.
  - intros b Hb l Hl. rewrite map_app, in_app_iff.
    apply in_app_iff in Hb as [Hb|Hb].
    + destruct (HO b Hb l Hl) as [H|(bb & Hbb & <- & _)]; auto.
      right. apply in_map; auto.
    + right. eapply HB; eauto.
  - intros b Hb Hph. apply in_app_iff in Hb as [Hb|Hb].
    + destruct (PO b Hb Hph) as (lc & lg & Hlc & Hlg & Hne & Hargs & Hiff).
      exists lc, lg. rewrite !map_app, !in_app_iff.
      repeat split; auto.
      * intros Hin. apply in_app_iff in H as [Hb'|Hb'].
        -- apply Hiff; auto.
        -- exfalso. eapply NoDup_app_disj; [exact Hnd| apply in_map; exact Hb|].
           eapply HB; eauto.
      * intros Hin. apply in_app_iff in H as [Hb'|Hb'].
        -- apply Hiff; auto.
        -- exfalso. destruct Hin as [Hin|Hin];
           (eapply NoDup_app_disj; [exact Hnd| |apply in_map; exact Hb']);
           rewrite Hin; auto.
    + destruct (PB b Hb Hph) as (lc & lg & Hlc & Hlg & Hne & Hargs & Hiff).
      exists lc, lg. rewrite !map_app, !in_app_iff.
      repeat split; auto.
      * intros Hin. apply in_app_iff in H as [Hb'|Hb'].
        -- exfalso. destruct (HO _ Hb' _ Hin) as [Hi|(bb & Hbb & Hid & Hp)].
           ++ eapply NoDup_app_disj; [exact Hnd|exact Hi|apply in_map; exact Hb].
           ++ assert (bb = b) by (eapply NoDup_map_inj; eauto). subst. congruence.
        -- apply Hiff; auto.
      * intros Hin. apply in_app_iff in H as [Hb'|Hb'].
        -- exfalso. destruct Hin as [Hin|Hin];
           (eapply NoDup_app_disj; [exact Hnd|apply in_map; exact Hb'|]);
           rewrite Hin; auto.
        -- apply Hiff; auto.
Qed.

(** Transport of CFG properties along blocks with the same label, phis and
    terminator (e.g. through [prepend_code]). *)
Definition same_shape (b' b : block typ) : Prop :=
  blk_id b' = blk_id b /\ blk_phis b' = blk_phis b /\ blk_term b' = blk_term b.

Lemma shape_ids B' B : Forall2 same_shape B' B -> map blk_id B' = map blk_id B.
Proof. induction 1 as [|b' b B' B (H1 & _) _ IH]; simpl; congruence. Qed.

Lemma shape_in_l B' B b' : Forall2 same_shape B' B -> In b' B' -> exists b, In b B /\ same_shape b' b.
Proof.
  induction 1 as [|c' c B' B Hs _ IH]; intros Hin; [destruct Hin|].
  destruct Hin as [->|Hin]; [exists c; split; [left; reflexivity|exact Hs]|].
  destruct (IH Hin) as (b & ? & ?). simpl; eauto.
Qed.

Lemma shape_in_r B' B b : Forall2 same_shape B' B -> In b B -> exists b', In b' B' /\ same_shape b' b.
Proof.
  induction 1 as [|c' c B' B Hs _ IH]; intros Hin; [destruct Hin|].
  destruct Hin as [<-|Hin]; [exists c'; split; [left; reflexivity|exact Hs]|].
  destruct (IH Hin) as (b' & ? & ?). simpl; eauto.
Qed.

Lemma shape_bsuccs b' b : same_shape b' b -> bsuccs b' = bsuccs b.
Proof. intros (_ & _ & H). unfold bsuccs. rewrite H. reflexivity. Qed.

Lemma shape_closed B' B : Forall2 same_shape B' B -> closed B -> closed B'.
Proof.
  intros HF HB b' Hb' l Hl. rewrite (shape_ids _ _ HF).
  destruct (shape_in_l _ _ _ HF Hb') as (b & Hb & Hs).
  rewrite (shape_bsuccs _ _ Hs) in Hl. eauto.
Qed.

Lemma shape_phis B' B : Forall2 same_shape B' B -> phis_ok B -> phis_ok B'.
Proof.
  intros HF HB b' Hb' Hph.
  destruct (shape_in_l _ _ _ HF Hb') as (b & Hb & Hs).
  destruct Hs as (Hid & Hp & Ht).
  rewrite Hp in Hph.
  destruct (HB b Hb Hph) as (lc & lg & Hlc & Hlg & Hne & Hargs & Hiff).
  exists lc, lg. rewrite (shape_ids _ _ HF). rewrite Hp, Hid.
  repeat split; auto.
  - intros Hin. destruct (shape_in_l _ _ _ HF H) as (b0 & Hb0 & Hs0).
    rewrite (shape_bsuccs _ _ Hs0) in Hin. destruct Hs0 as (-> & _).
    apply Hiff; auto.
  - intros Hin. destruct (shape_in_l _ _ _ HF H) as (b0 & Hb0 & Hs0).
    rewrite (shape_bsuccs _ _ Hs0). destruct Hs0 as (Hi0 & _). rewrite Hi0 in Hin.
    apply Hiff; auto.
Qed.

Lemma Forall2_same_shape_refl B : Forall2 same_shape B B.
Proof. induction B; constructor; auto. repeat split. Qed.

Lemma prepend_shape x blks : Forall2 same_shape (prepend_code x blks) blks.
Proof.
  destruct blks as [|b rest]; simpl; constructor.
  - repeat split.
  - apply Forall2_same_shape_refl.
Qed.

Lemma code_defs_app c1 c2 : code_defs (c1 ++ c2) = code_defs c1 ++ code_defs c2.
Proof.
  induction c1 as [|[[[r|n] i] m] c1 IH]; simpl; auto. rewrite IH. reflexivity.
Qed.

Lemma prepend_defs x blks b :
  In b (prepend_code x blks) -> forall r, In r (def_ids b) ->
  In r (code_defs x) \/ exists b0, In b0 blks /\ In r (def_ids b0).
Proof.
  destruct blks as [|b0 rest]; simpl; [contradiction|].
  intros [<-|Hb] r Hr.
  - unfold def_ids in Hr. simpl in Hr. rewrite code_defs_app in Hr.
    rewrite !in_app_iff in Hr. destruct Hr as [H|[H|H]].
    + right. exists b0. split; auto. unfold def_ids. apply in_app_iff; auto.
    + left; auto.
    + right. exists b0. split; auto. unfold def_ids. apply in_app_iff; auto.
  - right. eauto.
Qed.

Lemma cfg_ok_prepend e e' lo hi x blks :
  cfg_ok e' lo hi blks ->
  (forall r, In r (code_defs x) -> local_ok e lo hi r) ->
  (forall y, bound_var e' y -> bound_var e y) ->
  cfg_ok e lo hi (prepend_code x blks).
Proof.
  intros [Hlt Hne Hlbl Hnd Hent Hcl Hph Hdef] Hx Hb.
  pose proof (prepend_shape x blks) as HF.
  constructor; auto.
  - destruct blks; simpl; congruence.
  - rewrite Forall_forall in *. intros b' Hb'.
    destruct (shape_in_l _ _ _ HF Hb') as (b & Hbin & (-> & _)). auto.
  - rewrite (shape_ids _ _ HF). auto.
  - destruct blks as [|b0 rest]; simpl; [discriminate|].
    intros b r' Heq. injection Heq as <- _. simpl. eapply Hent; eauto.
  - eapply shape_closed; eauto.
  - eapply shape_phis; eauto.
  - intros b Hbin r Hr. destruct (prepend_defs _ _ _ Hbin r Hr) as [H|(b0 & Hb0 & H)]; auto.
    eapply local_ok_mono; [eapply Hdef; eauto | lia | lia | auto].
Qed.

Lemma cfg_ok_weaken e e' lo hi lo' hi' blks :
  cfg_ok e lo hi blks -> (lo' <= lo)%positive -> (hi <= hi')%positive ->
  (forall y, bound_var e y -> bound_var e' y) -> cfg_ok e' lo' hi' blks.
Proof.
  intros [Hlt Hne Hlbl Hnd Hent Hcl Hph Hdef] H1 H2 Hb.
  constructor; auto.
  - lia.
  - rewrite Forall_forall in *. intros b Hbin. eapply lbl_in_weaken; eauto.
  - intros b Hbin r Hr. eapply local_ok_mono; eauto.
Qed.

(** Names written by the code fragments. *)
Lemma code_defs_store_fields fs env vp i ys : code_defs (store_fields fs env vp i ys) = [].
Proof. revert i; induction ys; simpl; auto. Qed.

Lemma code_defs_spill env rp aty i rs : code_defs (spill_code env rp aty i rs) = [].
Proof. revert i; induction rs; simpl; auto. Qed.

Lemma code_defs_reload s rp aty i rs r :
  In r (code_defs (reload_code s rp aty i rs)) -> exists k, r = ssname s k.
Proof.
  revert i; induction rs; simpl; [contradiction|]. intros i [<-|H]; eauto.
Qed.

Lemma phi_defs_phi_list env s c g i rs r :
  In r (phi_defs (phi_list env s c g i rs)) -> exists k, r = ssname s k.
Proof.
  revert i; induction rs; simpl; [contradiction|]. intros i [<-|H]; eauto.
Qed.

Lemma phi_list_args env s c g i rs : Forall (phi_args_ok c g) (phi_list env s c g i rs).
Proof. revert i; induction rs; simpl; constructor; auto. reflexivity. Qed.

Lemma alloc_code_defs go ga fs env fresh x t ys r :
  In r (code_defs (alloc_code go ga fs env fresh x t ys)) ->
  r = Raw (Zpos x) \/ exists k, r = ssname fresh k.
Proof.
  unfold alloc_code. simpl. rewrite code_defs_app, code_defs_store_fields. simpl.
  intros [<-|[<-|[<-|[<-|[]]]]]; eauto.
Qed.

Lemma la_code_defs fs env fresh x f ys e' r :
  In r (code_defs (la_code fs env fresh x f ys e')) ->
  r = Raw (Zpos x) \/ exists k, r = ssname fresh k.
Proof.
  unfold la_code. simpl. rewrite !code_defs_app, code_defs_spill. simpl.
  intros [<-|[<-|[<-|[<-|H]]]]; eauto.
  rewrite code_defs_app, in_app_iff in H. destruct H as [H|[]].
  apply code_defs_reload in H. auto.
Qed.

(* ------------------------------------------------------------------ *)
(** ** 3. The main structural invariant of [translate_cfg] *)

Lemma exp_ind_nested (P : exp -> Prop) :
  (forall x t ys e, P e -> P (Econstr x t ys e)) ->
  (forall y arms, Forall (fun a => P (snd a)) arms -> P (Ecase y arms)) ->
  (forall x t n y e, P e -> P (Eproj x t n y e)) ->
  (forall x f ft ys e, P e -> P (Eletapp x f ft ys e)) ->
  (forall fds e, P e -> P (Efun fds e)) ->
  (forall f ft ys, P (Eapp f ft ys)) ->
  (forall x pv e, P e -> P (Eprim_val x pv e)) ->
  (forall x p ys e, P e -> P (Eprim x p ys e)) ->
  (forall x, P (Ehalt x)) ->
  forall e, P e.
Proof.
  intros H1 H2 H3 H4 H5 H6 H7 H8 H9. fix IH 1. destruct e.
  - apply H1, IH.
  - apply H2. induction l as [|[c e] l IHl]; constructor; [apply IH | exact IHl].
  - apply H3, IH.
  - apply H4, IH.
  - apply H5, IH.
  - apply H6.
  - apply H7, IH.
  - apply H8, IH.
  - apply H9.
Qed.

Ltac ss_ok := right; eexists; split; [|split; [|right; eexists; reflexivity]]; lia.

Lemma lbl_neq_succ p q : (p < q)%positive -> Anon (Zpos q) <> Anon (Zpos p).
Proof. intros H Heq. injection Heq as Heq. lia. Qed.

Section Main.
Variables (go ga : ctor_tag -> N) (po : positive -> option (String.string * bool))
          (fs : list positive).
Notation tr := (translate_cfg go ga po fs).

Definition tr_ok (e : exp) : Prop :=
  forall env chunk fresh blks fresh',
    tr env chunk e fresh = (blks, fresh') -> cfg_ok e fresh fresh' blks.

Lemma arm_loop_ok env E arms :
  Forall (fun a => tr_ok (snd a)) arms ->
  (forall c e x, In (c, e) arms -> bound_var e x -> bound_var E x) ->
  forall fr ablks edges fr2,
    arm_loop_d (fun ae fr => tr env 0%N ae fr) go ga arms fr = (ablks, edges, fr2) ->
    (fr <= fr2)%positive /\
    Forall (fun b => lbl_in fr fr2 (blk_id b)) ablks /\
    NoDup (map blk_id ablks) /\
    (forall b rest, ablks = b :: rest -> blk_phis b = []) /\
    closed ablks /\ phis_ok ablks /\
    (forall b, In b ablks -> forall r, In r (def_ids b) -> local_ok E fr fr2 r) /\
    (forall ed, In ed edges -> exists bb, In bb ablks /\ blk_id bb = snd (snd ed) /\ blk_phis bb = []).
Proof.
  induction arms as [|[t ae] rest IH]; intros HF HE fr ablks edges fr2 H.
  - rewrite arm_loop_nil in H. injection H as <- <- <-.
    repeat split; try constructor; try lia; unfold closed, phis_ok; intros; simpl in *; try discriminate; try contradiction.
  - inversion HF as [|a l Ha HFr]; subst. simpl in Ha.
    destruct (tr env 0%N ae fr) as [a1 fr1] eqn:Ha1.
    rewrite (arm_loop_cons _ _ _ t ae rest fr a1 fr1 Ha1) in H.
    destruct (arm_loop_d (fun ae fr => tr env 0%N ae fr) go ga rest fr1) as [[r1 re] fr2'] eqn:Hrst.
    injection H as <- <- <-.
    pose proof (Ha _ _ _ _ _ Ha1) as [Hlt Hne Hlbl Hnd Hent Hcl Hph Hdef].
    assert (HE' : forall c e x, In (c, e) rest -> bound_var e x -> bound_var E x)
      by (intros; eapply HE; [right|]; eauto).
    destruct (IH HFr HE' _ _ _ _ Hrst) as (Hle & Hlbl' & Hnd' & Hent' & Hcl' & Hph' & Hdef' & Hed').
    assert (Hdisj : forall l, In l (map blk_id a1) -> In l (map blk_id r1) -> False).
    { intros l H1 H2. eapply lbl_in_disj; [eapply lbl_in_map; [exact Hlbl|exact H1]
                                            |eapply lbl_in_map; [exact Hlbl'|exact H2]|]. lia. }
    assert (Hnd2 : NoDup (map blk_id (a1 ++ r1)))
      by (rewrite map_app; apply NoDup_app_intro; auto).
    destruct (join_ok a1 r1 Hnd2) as [Hcl2 Hph2]; auto.
    { intros b Hb l Hl. left. eapply Hcl; eauto. }
    destruct a1 as [|h t1]; [congruence|].
    repeat split.
    + lia.
    + apply Forall_app. split.
      * eapply Forall_impl; [|exact Hlbl]. intros b Hb. eapply (lbl_in_weaken fr fr1); [exact Hb|lia|lia].
      * eapply Forall_impl; [|exact Hlbl']. intros b Hb. eapply (lbl_in_weaken fr1 fr2'); [exact Hb|lia|lia].
    + exact Hnd2.
    + intros b rest' Heq. simpl in Heq. injection Heq as <- _. eapply Hent; eauto.
    + exact Hcl2.
    + exact Hph2.
    + intros b Hb r Hr. apply in_app_iff in Hb as [Hb|Hb].
      * eapply local_ok_mono; [eapply Hdef; eauto| lia | lia |].
        intros x Hx. eapply HE; [left; reflexivity| exact Hx].
      * eapply local_ok_mono; [eapply Hdef'; eauto| lia | lia | auto].
    + intros ed [<-|Hin].
      * exists h. split; [left; reflexivity|]. split; [reflexivity|]. eapply Hent; eauto.
      * destruct (Hed' ed Hin) as (bb & Hbb & Hid & Hp). exists bb.
        split; auto. apply in_app_iff. right; auto.
Qed.

Theorem translate_cfg_ok : forall e, tr_ok e.
Proof.
  apply exp_ind_nested; unfold tr_ok.
  - (* Econstr *)
    intros x t ys e' IH env chunk fresh blks fresh' H.
    destruct ys as [|y ys0] eqn:Hys.
    + destruct (tr env chunk e' fresh) as [b0 f0] eqn:Ht.
      rewrite (tr_constr_nil _ _ _ _ _ _ _ _ _ _ _ _ Ht) in H. injection H as <- <-.
      eapply cfg_ok_prepend; [eapply IH; eauto| |].
      * simpl. intros r [<-|[]]. left. eexists; split; [reflexivity|constructor].
      * intros; constructor; auto.
    + rewrite <- Hys in *.
      assert (Hne : ys <> []) by (subst; discriminate).
      destruct (N.leb (hd_nwords ys) chunk) eqn:Hl.
      * destruct (tr env (chunk - hd_nwords ys)%N e' (Pos.succ fresh)) as [b0 f0] eqn:Ht.
        rewrite (tr_constr_member _ _ _ _ _ _ _ _ _ _ _ _ _ Hne Hl Ht) in H. injection H as <- <-.
        pose proof (IH _ _ _ _ _ Ht) as Hok. pose proof (co_lt _ _ _ _ Hok).
        assert (Hok' : cfg_ok (Econstr x t ys e') fresh f0 b0)
          by (eapply cfg_ok_weaken; [exact Hok| lia | lia | intros; constructor; auto]).
        eapply cfg_ok_prepend; [exact Hok' | |].
        --
           intros r Hr. apply alloc_code_defs in Hr as [->|(k & ->)].
           ++ left. eexists; split; [reflexivity|constructor].
           ++ ss_ok.
        -- auto.
      * destruct (tr (hd_env fs env fresh x ys e') (chunk_words e') e' (Pos.succ fresh)) as [B f0] eqn:Ht.
        rewrite (tr_constr_head _ _ _ _ _ _ _ _ _ _ _ _ _ Hne Hl Ht) in H. injection H as <- <-.
        pose proof (IH _ _ _ _ _ Ht) as [Hlt Hne' Hlbl Hnd Hent Hcl Hph Hdef].
        set (C := hd_check_blk fs x ys e' fresh f0).
        set (G := hd_gc_blk fs env x ys e' fresh f0).
        set (A := hd_alloc_blk go ga fs env x t ys e' fresh f0 (entry_id B f0)).
        assert (HO : map blk_id [C; G; A] =
                     [Anon (Zpos f0); Anon (Zpos (Pos.succ f0)); Anon (Zpos (Pos.succ (Pos.succ f0)))])
          by reflexivity.
        assert (HBl : forall l, In l (map blk_id B) -> lbl_in (Pos.succ fresh) f0 l)
          by (intros; eapply lbl_in_map; eauto).
        assert (Hnd2 : NoDup (map blk_id ([C; G; A] ++ B))).
        { rewrite map_app. apply NoDup_app_intro; auto.
          - rewrite HO. repeat constructor; simpl; intros Hc;
              repeat (destruct Hc as [Hc|Hc]); try contradiction;
              injection Hc; lia.
          - intros l Hl1 Hl2. rewrite HO in Hl1. apply HBl in Hl2.
            simpl in Hl1. repeat (destruct Hl1 as [Hl1|Hl1]); try contradiction;
            subst; eapply lbl_in_neq; eauto; lia. }
        destruct B as [|h B']; [congruence|].
        assert (Hh : blk_phis h = []) by (eapply Hent; eauto).
        assert (Hk : lbl_in (Pos.succ fresh) f0 (blk_id h)) by (apply HBl; left; reflexivity).
        destruct (join_ok [C; G; A] (h :: B') Hnd2) as [Hcl2 Hph2]; auto.
        { intros b Hb l Hsl. simpl in Hb.
          repeat (destruct Hb as [Hb|Hb]); try contradiction; subst b.
          - left. rewrite HO. simpl in Hsl |- *. tauto.
          - left. rewrite HO. simpl in Hsl |- *. tauto.
          - right. simpl in Hsl. destruct Hsl as [<-|[]]. exists h. simpl. auto. }
        { intros b Hb Hph'. simpl in Hb.
          repeat (destruct Hb as [Hb|Hb]); try contradiction; subst b;
            try (exfalso; apply Hph'; reflexivity).
          exists (Anon (Zpos f0)), (Anon (Zpos (Pos.succ f0))).
          rewrite HO. split; [simpl; auto|]. split; [simpl; auto|].
          split; [intros Hc; injection Hc; lia|].
          split; [apply phi_list_args|].
          intros b' Hb'. simpl in Hb'.
          repeat (destruct Hb' as [Hb'|Hb']); try contradiction; subst b'; simpl.
          - tauto.
          - tauto.
          - split.
            + intros [Hc|[]]. exfalso. eapply lbl_in_neq; [exact Hk| |exact Hc]. lia.
            + intros [Hc|Hc]; injection Hc; lia. }
        change (C :: G :: A :: h :: B') with ([C; G; A] ++ h :: B').
        constructor; auto.
        -- lia.
        -- simpl; discriminate.
        -- apply Forall_app. split.
           ++ repeat constructor; eexists; (split; [reflexivity|]); lia.
           ++ eapply Forall_impl; [|exact Hlbl]. intros b Hb. eapply (lbl_in_weaken (Pos.succ fresh) f0); [exact Hb|lia|lia].
        -- intros b rest Heq. simpl in Heq. injection Heq as <- _. reflexivity.
        -- intros b Hb r Hr. apply in_app_iff in Hb as [Hb|Hb].
           ++ simpl in Hb. repeat (destruct Hb as [Hb|Hb]); try contradiction; subst b.
              ** simpl in Hr. repeat (destruct Hr as [Hr|Hr]); try contradiction; subst r; ss_ok.
              ** unfold def_ids in Hr. simpl in Hr.
                 rewrite !code_defs_app, code_defs_spill in Hr. simpl in Hr.
                 destruct Hr as [<-|Hr]; [ss_ok|].
                 rewrite code_defs_app, in_app_iff in Hr. destruct Hr as [Hr|[]].
                 apply code_defs_reload in Hr as (k & ->). ss_ok.
              ** unfold A, hd_alloc_blk, def_ids in Hr. cbn [blk_phis blk_code] in Hr. apply in_app_iff in Hr as [Hr|Hr].
                 --- apply phi_defs_phi_list in Hr as (k & ->). ss_ok.
                 --- apply alloc_code_defs in Hr as [->|(k & ->)]; [|ss_ok].
                     left. eexists; split; [reflexivity|constructor].
           ++ eapply local_ok_mono; [eapply Hdef; eauto| lia | lia |].
              intros; constructor; auto.
  - (* Ecase *)
    intros y arms HF env chunk fresh blks fresh' H.
    destruct (arm_loop_d (fun ae fr => tr env 0%N ae fr) go ga arms fresh) as [[AB ED] f1] eqn:Harm.
    rewrite (tr_case _ _ _ _ _ _ _ _ _ _ _ _ Harm) in H. injection H as <- <-.
    assert (HE : forall c e x, In (c, e) arms -> bound_var e x -> bound_var (Ecase y arms) x)
      by (intros; econstructor; eauto).
    destruct (arm_loop_ok env _ arms HF HE _ _ _ _ Harm)
      as (Hle & Hlbl & Hnd & Hent & Hcl & Hph & Hdef & Hed).
    set (dflt := entry_id AB (Pos.succ (Pos.succ f1))).
    set (T := case_test_blk env y f1).
    set (U := case_unboxed_blk env y f1 dflt ED).
    set (X := case_boxed_blk env y f1 dflt ED).
    assert (HO : map blk_id [T; U; X] =
                 [Anon (Zpos (Pos.succ (Pos.succ f1))); Anon (Zpos (Pos.succ f1)); Anon (Zpos f1)])
      by reflexivity.
    assert (HBl : forall l, In l (map blk_id AB) -> lbl_in fresh f1 l)
      by (intros; eapply lbl_in_map; eauto).
    assert (Hnd2 : NoDup (map blk_id ([T; U; X] ++ AB))).
    { rewrite map_app. apply NoDup_app_intro; auto.
      - rewrite HO. repeat constructor; simpl; intros Hc;
          repeat (destruct Hc as [Hc|Hc]); try contradiction;
          injection Hc; lia.
      - intros l Hl1 Hl2. rewrite HO in Hl1. apply HBl in Hl2.
        simpl in Hl1. repeat (destruct Hl1 as [Hl1|Hl1]); try contradiction;
        subst; eapply lbl_in_neq; eauto; lia. }
    assert (Hdflt : In dflt (map blk_id [T; U; X]) \/
                    exists bb, In bb AB /\ blk_id bb = dflt /\ blk_phis bb = []).
    { subst dflt. destruct AB as [|h AB'].
      - left. rewrite HO. left. reflexivity.
      - right. exists h. split; [left; reflexivity|]. split; [reflexivity|]. eapply Hent; eauto. }
    assert (Hedges : forall p l, In l (map snd (map snd (List.filter p ED))) ->
                       exists bb, In bb AB /\ blk_id bb = l /\ blk_phis bb = []).
    { intros p l Hl. rewrite map_map in Hl. apply in_map_iff in Hl as (ed & <- & Hin).
      apply filter_In in Hin as [Hin _]. auto. }
    destruct (join_ok [T; U; X] AB Hnd2) as [Hcl2 Hph2]; auto.
    { intros b Hb l Hl. simpl in Hb.
      repeat (destruct Hb as [Hb|Hb]); try contradiction; subst b.
      - left. rewrite HO. simpl in Hl |- *. tauto.
      - simpl in Hl. destruct Hl as [<-|Hl]; [exact Hdflt|]. right. eapply Hedges; eauto.
      - simpl in Hl. destruct Hl as [<-|Hl]; [exact Hdflt|]. right. eapply Hedges; eauto. }
    { intros b Hb Hph'. simpl in Hb.
      repeat (destruct Hb as [Hb|Hb]); try contradiction; subst b;
        exfalso; apply Hph'; reflexivity. }
    change (T :: U :: X :: AB) with ([T; U; X] ++ AB).
    constructor; auto.
    + lia.
    + simpl; congruence.
    + apply Forall_app. split.
      * repeat constructor; eexists; (split; [reflexivity|]); lia.
      * eapply Forall_impl; [|exact Hlbl]. intros b Hb. eapply (lbl_in_weaken fresh f1); [exact Hb|lia|lia].
    + intros b rest Heq. simpl in Heq. injection Heq as <- _. reflexivity.
    + intros b Hb r Hr. apply in_app_iff in Hb as [Hb|Hb].
      * simpl in Hb. repeat (destruct Hb as [Hb|Hb]); try contradiction; subst b;
          simpl in Hr; try contradiction.
        destruct Hr as [<-|[]]. right. exists f1. repeat split; [lia|lia|left; reflexivity].
      * eapply local_ok_mono; [eapply Hdef; eauto| lia | lia | auto].
  - (* Eproj *)
    intros x t n y e' IH env chunk fresh blks fresh' H.
    destruct (tr env chunk e' fresh) as [b0 f0] eqn:Ht.
    erewrite tr_proj in H by exact Ht. injection H as <- <-.
    eapply cfg_ok_prepend; [eapply IH; eauto| |].
    + simpl. intros r [<-|[]]. left. eexists; split; [reflexivity|constructor].
    + intros; constructor; auto.
  - (* Eletapp *)
    intros x f ft ys e' IH env chunk fresh blks fresh' H.
    destruct (tr (la_env fs env fresh x e') 0%N e' (Pos.succ fresh)) as [b0 f0] eqn:Ht.
    erewrite tr_letapp in H by exact Ht. injection H as <- <-.
    pose proof (IH _ _ _ _ _ Ht) as Hok. pose proof (co_lt _ _ _ _ Hok).
    assert (Hok' : cfg_ok (Eletapp x f ft ys e') fresh f0 b0)
      by (eapply cfg_ok_weaken; [exact Hok| lia | lia | intros; constructor; auto]).
    eapply cfg_ok_prepend; [exact Hok' | |].
    + intros r Hr. apply la_code_defs in Hr as [->|(k & ->)].
      * left. eexists; split; [reflexivity|constructor].
      * ss_ok.
    + auto.
  - (* Efun *)
    intros fds e' IH env chunk fresh blks fresh' H.
    rewrite tr_fun in H. eapply cfg_ok_weaken; [eapply IH; eauto| lia | lia |].
    intros; apply Bound_Efun2; auto.
  - (* Eapp *)
    intros f ft ys env chunk fresh blks fresh' H.
    rewrite tr_app in H. injection H as <- <-.
    constructor.
    + lia.
    + congruence.
    + repeat constructor. eexists; split; [reflexivity|]; lia.
    + repeat constructor. simpl; tauto.
    + intros b rest Heq. simpl in Heq. injection Heq as <- _. reflexivity.
    + intros b Hb l Hl. destruct Hb as [<-|[]]. destruct Hl.
    + intros b Hb Hph. destruct Hb as [<-|[]]. exfalso; apply Hph; reflexivity.
    + intros b Hb r Hr. destruct Hb as [<-|[]]. simpl in Hr. destruct Hr as [<-|[]].
      right. exists fresh. repeat split; [lia|lia|left; reflexivity].
  - (* Eprim_val *)
    intros x pv e' IH env chunk fresh blks fresh' H.
    destruct (tr env chunk e' fresh) as [b0 f0] eqn:Ht.
    erewrite tr_prim_val in H by exact Ht. injection H as <- <-.
    eapply cfg_ok_prepend; [eapply IH; eauto| |].
    + simpl. intros r [<-|[]]. left. eexists; split; [reflexivity|constructor].
    + intros; constructor; auto.
  - (* Eprim *)
    intros x p ys e' IH env chunk fresh blks fresh' H.
    destruct (tr env 0%N e' fresh) as [b0 f0] eqn:Ht.
    erewrite tr_prim in H by exact Ht. injection H as <- <-.
    eapply cfg_ok_prepend; [eapply IH; eauto| |].
    + simpl. intros r [<-|[]]. left. eexists; split; [reflexivity|constructor].
    + intros; constructor; auto.
  - (* Ehalt *)
    intros x env chunk fresh blks fresh' H.
    rewrite tr_halt in H. injection H as <- <-.
    constructor.
    + lia.
    + congruence.
    + repeat constructor. eexists; split; [reflexivity|]; lia.
    + repeat constructor. simpl; tauto.
    + intros b rest Heq. simpl in Heq. injection Heq as <- _. reflexivity.
    + intros b Hb l Hl. destruct Hb as [<-|[]]. destruct Hl.
    + intros b Hb Hph. destruct Hb as [<-|[]]. exfalso; apply Hph; reflexivity.
    + intros b Hb r Hr. destruct Hb as [<-|[]]. destruct Hr.
Qed.

End Main.

(** *** Corollaries, in the form used downstream. *)
Section Corollaries.
Variables (go ga : ctor_tag -> N) (po : positive -> option (String.string * bool))
          (fs : list positive) (env : nenv) (chunk : N).
Notation tr := (translate_cfg go ga po fs env chunk).

(** 1. Monotonicity / non-emptiness. *)
Corollary translate_cfg_mono e fresh blks fresh' :
  tr e fresh = (blks, fresh') -> (fresh < fresh')%positive /\ blks <> [].
Proof. intros H. destruct (translate_cfg_ok go ga po fs e _ _ _ _ _ H). auto. Qed.

(** 2. Labels: [Anon (Zpos p)] with [fresh <= p < fresh'], pairwise distinct. *)
Corollary translate_cfg_labels e fresh blks fresh' :
  tr e fresh = (blks, fresh') ->
  (forall b, In b blks -> exists p, blk_id b = Anon (Zpos p) /\
                                    (fresh <= p)%positive /\ (p < fresh')%positive) /\
  NoDup (map blk_id blks).
Proof.
  intros H. destruct (translate_cfg_ok go ga po fs e _ _ _ _ _ H) as [_ _ Hl Hn _ _ _ _].
  rewrite Forall_forall in Hl. auto.
Qed.

(** 3. Entry: the first block has no phis and an in-range label. *)
Corollary translate_cfg_entry e fresh blks fresh' :
  tr e fresh = (blks, fresh') ->
  exists b rest q, blks = b :: rest /\ blk_phis b = [] /\ blk_id b = Anon (Zpos q) /\
                   (fresh <= q)%positive /\ (q < fresh')%positive.
Proof.
  intros H. destruct (translate_cfg_ok go ga po fs e _ _ _ _ _ H) as [_ Hne Hl _ He _ _ _].
  destruct blks as [|b rest]; [congruence|]. inversion Hl as [|? ? (q & Hq & H1 & H2) _]; subst.
  exists b, rest, q. repeat split; auto. eapply He; eauto.
Qed.

(** 5. Phis: successors stay inside the CFG, and a block with phis has
    exactly two predecessors, which are the two incoming labels of each of its
    phis. *)
Corollary translate_cfg_phis e fresh blks fresh' :
  tr e fresh = (blks, fresh') -> closed blks /\ phis_ok blks.
Proof. intros H. destruct (translate_cfg_ok go ga po fs e _ _ _ _ _ H). auto. Qed.

(** 6. Locals written. *)
Corollary translate_cfg_defs e fresh blks fresh' :
  tr e fresh = (blks, fresh') ->
  forall b, In b blks -> forall r, In r (def_ids b) -> local_ok e fresh fresh' r.
Proof. intros H. destruct (translate_cfg_ok go ga po fs e _ _ _ _ _ H). auto. Qed.

Corollary translate_cfg_no_tinfo e fresh blks fresh' :
  tr e fresh = (blks, fresh') ->
  forall b, In b blks -> ~ In (Name "tinfo") (def_ids b).
Proof.
  intros H b Hb Hin. eapply local_ok_not_tinfo. eapply translate_cfg_defs; eauto.
Qed.

End Corollaries.

(* ------------------------------------------------------------------ *)
(** ** 4. [mk_fun] and [compile_prog] *)

Lemma mk_fun_spec go ga po fs name params body blks f' :
  translate_cfg go ga po fs base_env 0%N body 1%positive = (blks, f') ->
  exists b rest, blks = b :: rest /\
    df_instrs (mk_fun go ga po fs name params body) = (b, rest) /\
    dc_name (df_prototype (mk_fun go ga po fs name params body)) = name /\
    df_args (mk_fun go ga po fs name params body) = Name "tinfo" :: map (fun v => Raw (Zpos v)) params.
Proof.
  intros H. destruct (translate_cfg_mono go ga po fs _ _ _ _ _ _ H) as [_ Hne].
  destruct blks as [|b rest]; [congruence|].
  exists b, rest. unfold mk_fun. rewrite H. auto.
Qed.

Lemma mk_fun_name go ga po fs name params body :
  dc_name (df_prototype (mk_fun go ga po fs name params body)) = name.
Proof.
  unfold mk_fun. destruct (translate_cfg go ga po fs base_env 0%N body 1%positive). reflexivity.
Qed.

(** The block list of an emitted definition (entry first) is a well-formed CFG:
    distinct labels, phi-free entry, closed successors, phis well placed. *)
Lemma mk_fun_ok go ga po fs name params body :
  exists f',
    cfg_ok body 1 f' (fst (df_instrs (mk_fun go ga po fs name params body))
                       :: snd (df_instrs (mk_fun go ga po fs name params body))).
Proof.
  destruct (translate_cfg go ga po fs base_env 0%N body 1%positive) as [blks f'] eqn:H.
  destruct (mk_fun_spec go ga po fs name params body _ _ H) as (b & rest & -> & Hd & _).
  exists f'. rewrite Hd. simpl. eapply translate_cfg_ok; eauto.
Qed.

Corollary mk_fun_labels_nodup go ga po fs name params body :
  NoDup (map blk_id (fst (df_instrs (mk_fun go ga po fs name params body))
                     :: snd (df_instrs (mk_fun go ga po fs name params body)))) /\
  blk_phis (fst (df_instrs (mk_fun go ga po fs name params body))) = [].
Proof.
  destruct (mk_fun_ok go ga po fs name params body) as [f' [_ _ _ Hn He _ _ _]].
  split; auto. eapply He; reflexivity.
Qed.

Definition tle_name (t : toplevel_entity typ (block typ * list (block typ))) : option function_id :=
  match t with TLE_Definition d => Some (dc_name (df_prototype d)) | _ => None end.

Lemma funs_to_defs_names go ga po fs fds :
  map (fun d => tle_name (TLE_Definition d)) (funs_to_defs go ga po fs fds) =
  map (fun f => Some (Anon (Zpos f))) (fun_ids fds).
Proof.
  induction fds as [f ft xs e rest IH|]; [|reflexivity].
  cbn [funs_to_defs fun_ids map]. rewrite IH. unfold tle_name at 1. rewrite mk_fun_name. reflexivity.
Qed.

Lemma compile_prog_names go ga po e :
  map tle_name (compile_prog go ga po e) =
  match e with
  | Efun fds _ => (map (fun f => Some (Anon (Zpos f))) (fun_ids fds) ++ [Some (Name "certirocq_main")])%list
  | _ => [Some (Name "certirocq_main")]
  end.
Proof.
  destruct e; unfold compile_prog; try (cbn [map tle_name]; rewrite mk_fun_name; reflexivity).
  rewrite map_app, map_map, funs_to_defs_names. cbn [map tle_name]. rewrite mk_fun_name. reflexivity.
Qed.

Lemma compile_prog_names_nodup go ga po fds main :
  NoDup (fun_ids fds) -> NoDup (map tle_name (compile_prog go ga po (Efun fds main))).
Proof.
  intros Hn. rewrite compile_prog_names. apply NoDup_app_intro.
  - induction Hn as [|f l Hf Hl IH]; simpl; constructor; auto.
    intros Hin. apply in_map_iff in Hin as (g & Heq & Hg). injection Heq as ->. auto.
  - repeat constructor; auto.
  - intros a H1 [<-|[]]. apply in_map_iff in H1 as (g & Heq & _). discriminate.
Qed.

Lemma funs_to_defs_in go ga po fs fds d :
  In d (funs_to_defs go ga po fs fds) ->
  exists f ft params body, In f (fun_ids fds) /\ d = mk_fun go ga po fs (Anon (Zpos f)) params body /\
    fun_in_fundefs fds (f, ft, params, body).
Proof.
  induction fds as [f ft params body rest IH|]; simpl; [|contradiction].
  intros [<-|Hd].
  - exists f, ft, params, body. repeat split; auto. left. reflexivity.
  - destruct (IH Hd) as (g & gt & ps & bd & Hg & -> & Hf). exists g, gt, ps, bd.
    repeat split; auto. right. auto.
Qed.

(** Every top-level entity emitted is a [define] produced by [mk_fun], whose
    block list is a well-formed CFG in the sense of [cfg_ok]. *)
Lemma compile_prog_defs go ga po e tle :
  In tle (compile_prog go ga po e) ->
  exists fs name params body,
    tle = TLE_Definition (mk_fun go ga po fs name params body) /\
    exists f', cfg_ok body 1 f' (fst (df_instrs (mk_fun go ga po fs name params body))
                               :: snd (df_instrs (mk_fun go ga po fs name params body))).
Proof.
  intros Hin.
  assert (exists fs name params body, tle = TLE_Definition (mk_fun go ga po fs name params body))
    as (fs & name & params & body & ->).
  { destruct e; simpl in Hin;
      try (destruct Hin as [<-|[]]; do 4 eexists; reflexivity).
    apply in_app_iff in Hin as [Hin|[<-|[]]]; [|do 4 eexists; reflexivity].
    apply in_map_iff in Hin as (d & <- & Hd).
    destruct (funs_to_defs_in _ _ _ _ _ _ Hd) as (g & gt & ps & bd & _ & -> & _).
    do 4 eexists; reflexivity. }
  do 4 eexists. split; [reflexivity|]. apply mk_fun_ok.
Qed.
