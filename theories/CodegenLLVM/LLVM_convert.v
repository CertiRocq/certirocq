(** * Type conversion ([convert_types]) of the emitted program.

    [convert_types] uses the program's [m_type_defs] as environment; the
    emitted program has none, so everything is [typ_to_dtyp []] ([cty]).
    [link runtime_prelude P = TLE_Declaration gc_decl :: P] (nothing dropped
    or reordered), and the resulting [mcfg] has one declaration and one
    definition per emitted function, each converted pointwise ([conv_def]). *)
From Stdlib Require Import ZArith NArith List String.
From CertiRocq.LambdaANF Require Import term.
From CertiRocq.CodegenLLVM Require Import LambdaANF_to_LLVM Flatten LambdaANF_to_LLVM_statement.
From Vellvm Require Import Syntax Semantics.TopLevel.
Import ListNotations.

Notation cty := (typ_to_dtyp []).

Lemma cty_I : forall n, cty (TYPE_I n) = DTYPE_I n.
Proof. intros; rewrite typ_to_dtyp_equation; reflexivity. Qed.
Lemma cty_val : cty val_ty = DTYPE_I 64.
Proof. apply cty_I. Qed.
Lemma cty_Pointer : forall t, cty (TYPE_Pointer t) = DTYPE_Pointer.
Proof. intros; rewrite typ_to_dtyp_equation; reflexivity. Qed.
Lemma cty_Void : cty TYPE_Void = DTYPE_Void.
Proof. intros; rewrite typ_to_dtyp_equation; reflexivity. Qed.
Lemma cty_Function : forall r a v, cty (TYPE_Function r a v) = DTYPE_Pointer.
Proof. intros; rewrite typ_to_dtyp_equation; reflexivity. Qed.
Lemma cty_Array : forall n t, cty (TYPE_Array n t) = DTYPE_Array false n (cty t).
Proof. intros; rewrite typ_to_dtyp_equation; reflexivity. Qed.
Lemma map_In_const {A B : Type} : forall (l : list A) (f : forall x, In x l -> B) (g : A -> B),
    (forall x H, f x H = g x) -> ListUtil.map_In l f = map g l.
Proof.
  induction l as [|a l IH]; intros f g Hf; cbn; [reflexivity|].
  f_equal; [apply Hf|]. apply IH. intros; apply Hf.
Qed.
Lemma cty_Struct : forall l, cty (TYPE_Struct l) = DTYPE_Struct false (map cty l).
Proof. intros; rewrite typ_to_dtyp_equation. cbn. f_equal. apply map_In_const; reflexivity. Qed.
Lemma cty_ptr : cty ptr_ty = DTYPE_Pointer.
Proof. apply cty_Pointer. Qed.
Lemma cty_tinfo : cty tinfo_ty = DTYPE_Pointer.
Proof. apply cty_Pointer. Qed.
Lemma cty_tinfo_struct : cty tinfo_struct_ty =
  DTYPE_Struct false [(DTYPE_Pointer : dtyp); (DTYPE_Pointer : dtyp); (DTYPE_Pointer : dtyp);
                      DTYPE_Array false 1024 (DTYPE_I 64); (DTYPE_Pointer : dtyp); (DTYPE_I 64 : dtyp)].
Proof. unfold tinfo_struct_ty. rewrite cty_Struct. cbn [map]. rewrite cty_Array, !cty_ptr, cty_val. reflexivity. Qed.


Lemma cty_frame : cty frame_ty =
  DTYPE_Struct false [(DTYPE_Pointer : dtyp); (DTYPE_Pointer : dtyp); (DTYPE_Pointer : dtyp)].
Proof. unfold frame_ty. rewrite cty_Struct. cbn [map]. rewrite !cty_tinfo. reflexivity. Qed.
Lemma cty_val_array : forall n, cty (TYPE_Array n val_ty) = DTYPE_Array false n (DTYPE_I 64).
Proof. intros; rewrite cty_Array, cty_val; reflexivity. Qed.
Lemma cty_i1 : cty (TYPE_I 1) = DTYPE_I 1.
Proof. apply cty_I. Qed.
Lemma cty_i32 : cty (TYPE_I 32) = DTYPE_I 32.
Proof. apply cty_I. Qed.
(** Function types (of [mk_fun] and [gc_decl]) collapse to [DTYPE_Pointer]. *)
Lemma cty_mk_fun_type : forall (params : list var),
  cty (TYPE_Function val_ty (tinfo_ty :: map (fun _ => val_ty) params) false) = DTYPE_Pointer.
Proof. intros; apply cty_Function. Qed.
Lemma cty_gc_type : cty (TYPE_Function TYPE_Void [TYPE_Pointer None] false) = DTYPE_Pointer.
Proof. apply cty_Function. Qed.

Definition cexp : exp typ -> exp dtyp := convert_typ [].
Definition cinstr : instr typ -> instr dtyp := convert_typ [].
Definition cterm : terminator typ -> terminator dtyp := convert_typ [].
Definition ccode : code typ -> code dtyp := convert_typ [].
Definition cblock : block typ -> block dtyp := convert_typ [].
Definition cdecl : declaration typ -> declaration dtyp := convert_typ [].
Definition ctexp (te : texp typ) : texp dtyp := (cty (fst te), cexp (snd te)).

Lemma cexp_Ident : forall i, cexp (EXP_Ident i) = EXP_Ident i.
Proof. intros []; reflexivity. Qed.
Lemma cexp_Integer : forall n, cexp (EXP_Integer n) = EXP_Integer n.
Proof. reflexivity. Qed.
Lemma cexp_IBinop : forall op t e1 e2,
  cexp (OP_IBinop op t e1 e2) = OP_IBinop op (cty t) (cexp e1) (cexp e2).
Proof. reflexivity. Qed.
Lemma cexp_ICmp : forall s op t e1 e2,
  cexp (OP_ICmp s op t e1 e2) = OP_ICmp s op (cty t) (cexp e1) (cexp e2).
Proof. reflexivity. Qed.
Lemma cexp_Conversion : forall cv t1 e t2,
  cexp (OP_Conversion cv t1 e t2) = OP_Conversion cv (cty t1) (cexp e) (cty t2).
Proof. reflexivity. Qed.
Lemma cexp_GEP : forall t p idxs,
  cexp (OP_GetElementPtr t p idxs) = OP_GetElementPtr (cty t) (ctexp p) (map ctexp idxs).
Proof. reflexivity. Qed.

Lemma cinstr_Op : forall e, cinstr (INSTR_Op e) = INSTR_Op (cexp e).
Proof. reflexivity. Qed.
Lemma cinstr_Load : forall t p, cinstr (INSTR_Load t p []) = INSTR_Load (cty t) (ctexp p) [].
Proof. intros t []; reflexivity. Qed.
Lemma cinstr_Store : forall v p, cinstr (INSTR_Store v p []) = INSTR_Store (ctexp v) (ctexp p) [].
Proof. intros [] []; reflexivity. Qed.
Lemma cinstr_Alloca : forall t, cinstr (INSTR_Alloca t []) = INSTR_Alloca (cty t) [].
Proof. reflexivity. Qed.
Lemma cinstr_Call : forall f args,
  cinstr (INSTR_Call f args [] []) = INSTR_Call (ctexp f) (map (fun '(te, a) => (ctexp te, a)) args) [] [].
Proof. intros [] args; cbn. f_equal. apply map_ext. intros [[] ?]; reflexivity. Qed.

Lemma cterm_Ret : forall v, cterm (TERM_Ret v) = TERM_Ret (ctexp v).
Proof. intros []; reflexivity. Qed.
Lemma cterm_Br : forall v l1 l2, cterm (TERM_Br v l1 l2) = TERM_Br (ctexp v) l1 l2.
Proof. intros [] [] []; reflexivity. Qed.
Lemma cterm_Br_1 : forall l, cterm (TERM_Br_1 l) = TERM_Br_1 l.
Proof. intros []; reflexivity. Qed.
Lemma cterm_Switch : forall v d brs,
  cterm (TERM_Switch v d brs) = TERM_Switch (ctexp v) d brs.
Proof.
  intros [] d brs; cbn. f_equal.
  induction brs as [|[[] b] brs IH]; cbn; [reflexivity|]. rewrite IH. destruct b; reflexivity.
Qed.

Lemma ccode_eq : forall c : code typ,
  ccode c = map (fun '(id, i, md) => (id, cinstr i, tfmap cty md)) c.
Proof.
  intros c. unfold ccode, convert_typ, ConvertTyp_code, tfmap at 1, TFunctor_code, tfmap at 1, TFunctor_list.
  apply map_ext. intros [[[[]|] i] md]; reflexivity.
Qed.



Lemma cterm_Unreachable : cterm TERM_Unreachable = TERM_Unreachable.
Proof. reflexivity. Qed.

Lemma ccode_nil : ccode [] = [].
Proof. reflexivity. Qed.
Lemma ccode_cons : forall id i c, ccode ((id, i, []) :: c) = (id, cinstr i, []) :: ccode c.
Proof. intros. rewrite !ccode_eq. reflexivity. Qed.
Lemma ccode_app : forall c1 c2, ccode (c1 ++ c2) = (ccode c1 ++ ccode c2)%list.
Proof. intros. apply convert_typ_code_app. Qed.

Lemma cphi_eq : forall t args,
  tfmap cty (Phi t args) = Phi (cty t) (map (fun '(id, e) => (id, cexp e)) args).
Proof. intros t args. cbn. f_equal. Qed.

Lemma cblock_eq : forall b : block typ,
  cblock b =
  mk_block (blk_id b)
           (map (fun '(id, ph, md) => (id, tfmap cty ph, tfmap cty md)) (blk_phis b))
           (ccode (blk_code b))
           (let '(id, t, md) := blk_term b in (id, cterm t, tfmap cty md))
           (blk_comments b).
Proof.
  intros [id phis c [[tid t] md] cm].
  unfold cblock, convert_typ, ConvertTyp_block, tfmap at 1, TFunctor_block. cbn [blk_id blk_phis blk_code blk_term blk_comments].
  destruct id, tid as [[]|]; f_equal;
    unfold tfmap at 1, TFunctor_list; apply map_ext; intros [[[] ph] m]; reflexivity.
Qed.

(** ** Whole-program characterization *)

Notation Ldef := (definition typ (block typ * list (block typ))).

Definition prog_defs (get_ord get_arity : ctor_tag -> N)
           (prim_of : positive -> option (string * bool)) (e : term.exp) : list Ldef :=
  match e with
  | Efun fds main =>
      (funs_to_defs get_ord get_arity prim_of (fun_ids fds) fds
       ++ [mk_fun get_ord get_arity prim_of (fun_ids fds) (Name "certirocq_main") [] main])%list
  | _ => [mk_fun get_ord get_arity prim_of [] (Name "certirocq_main") [] e]
  end.

Lemma compile_prog_defs : forall get_ord get_arity prim_of e,
  compile_prog get_ord get_arity prim_of e
  = map (@TLE_Definition _ _) (prog_defs get_ord get_arity prim_of e).
Proof. intros. destruct e; try reflexivity. cbn. rewrite map_app. reflexivity. Qed.

Lemma flatten_prog_defs : forall ds : list Ldef,
  flatten_prog (map (@TLE_Definition _ _) ds) = map (@TLE_Definition _ _) (map flat_def ds).
Proof. intros. unfold flatten_prog. rewrite !map_map. reflexivity. Qed.

Lemma link_prelude : forall P : LLprog, link runtime_prelude P = (TLE_Declaration gc_decl :: P)%list.
Proof.
  intros P. unfold link. cbn. f_equal.
  induction P as [|t P IH]; cbn; [reflexivity|].
  rewrite IH. destruct t; try reflexivity.
  destruct decl as [[] ? ? ? ?]; reflexivity.
Qed.

(** The conversion of one definition: prototype converted, arguments kept,
    blocks converted pointwise, [init] the id of the entry block. *)
Definition conv_def (d : Ldef) : definition dtyp (cfg dtyp) :=
  mk_definition (cdecl (df_prototype d)) (df_args d)
    {| init := blk_id (fst (df_instrs d));
       blks := map cblock (fst (df_instrs d) :: snd (df_instrs d));
       args := df_args d |}.


Theorem convert_link_defs : forall ds : list Ldef,
  convert_types (CFG.mcfg_of_tle (link runtime_prelude (map (@TLE_Definition _ _) ds)))
  = {| m_name := None; m_target := None; m_datalayout := None;
       m_type_defs := []; m_globals := [];
       m_declarations := [cdecl gc_decl];
       m_definitions := map conv_def ds |}.
Proof.
  intros ds. rewrite link_prelude.
  unfold CFG.mcfg_of_tle, modul_of_toplevel_entities, mcfg_of_modul. cbn.
  assert (H1 : forall {A} (f : toplevel_entity typ (block typ * list (block typ)) -> option A),
             (forall d, f (TLE_Definition d) = None) ->
             ListUtil.find_option f (map (@TLE_Definition _ _) ds) = None).
  { intros A f Hf. induction ds as [|d ds' IH]; cbn; [reflexivity|]. rewrite Hf. exact IH. }
  assert (H2 : forall {A} (f : toplevel_entity typ (block typ * list (block typ)) -> list A),
             (forall d, f (TLE_Definition d) = []) ->
             flat_map f (map (@TLE_Definition _ _) ds) = []).
  { clear H1. intros A f Hf. induction ds as [|d ds' IH]; cbn; [reflexivity|]. rewrite Hf. exact IH. }
  assert (H3 : flat_map (definitions_of (T:=typ)) (map (@TLE_Definition _ _) ds) = ds).
  { clear H1 H2. induction ds as [|d ds' IH]; cbn; [reflexivity|]. f_equal. exact IH. }
  rewrite !H1, !H2, H3 by reflexivity.
  unfold convert_types, convert_typ, ConvertTyp_mcfg, tfmap at 1, TFunctor_mcfg. cbn.
  f_equal. unfold tfmap at 1, TFunctor_list'. rewrite map_map. apply map_ext.
  intros [proto dargs [entry rest]].
  unfold tfmap at 1, TFunctor_definition, conv_def, cfg_of_definition, init_of_definition. cbn.
  assert (E : forall l : list raw_id, endo l = l).
  { induction l as [|a l IH]; cbn; [reflexivity|]. rewrite IH. destruct a; reflexivity. }
  rewrite E. f_equal.
  unfold tfmap at 1, TFunctor_cfg. cbn. rewrite E. f_equal; try (destruct (blk_id entry); reflexivity).
Qed.

(** The program actually run by [run_program]: one declaration (the GC), no
    globals/type definitions, and one converted definition per emitted
    function, in emission order (lifted fundefs, then [certirocq_main]). *)
Theorem convert_emitted_prog : forall get_ord get_arity prim_of e,
  convert_types (CFG.mcfg_of_tle (link runtime_prelude
                   (flatten_prog (compile_prog get_ord get_arity prim_of e))))
  = {| m_name := None; m_target := None; m_datalayout := None;
       m_type_defs := []; m_globals := [];
       m_declarations := [cdecl gc_decl];
       m_definitions := map (fun d => conv_def (flat_def d)) (prog_defs get_ord get_arity prim_of e) |}.
Proof.
  intros. rewrite compile_prog_defs, flatten_prog_defs, convert_link_defs, map_map. reflexivity.
Qed.

Corollary convert_emitted : forall cenv prim_of e,
  convert_types (CFG.mcfg_of_tle (link runtime_prelude (emitted cenv prim_of e)))
  = {| m_name := None; m_target := None; m_datalayout := None;
       m_type_defs := []; m_globals := [];
       m_declarations := [cdecl gc_decl];
       m_definitions := map (fun d => conv_def (flat_def d))
                            (prog_defs (ord_of cenv) (arity_of cenv) prim_of e) |}.
Proof. intros. apply convert_emitted_prog. Qed.

Lemma cdecl_gc_decl :
  cdecl gc_decl = mk_declaration (Name "garbage_collect") (DTYPE_Pointer : dtyp) ([], [[]]) [] [].
Proof.
  unfold cdecl, convert_typ, ConvertTyp_declaration, tfmap, TFunctor_declaration, gc_decl.
  cbn [dc_name dc_type dc_param_attrs dc_attrs dc_annotations].
  rewrite cty_Function. reflexivity.
Qed.

Lemma cdecl_mk_fun : forall get_ord get_arity prim_of fs name params body,
  cdecl (df_prototype (mk_fun get_ord get_arity prim_of fs name params body))
  = mk_declaration name (DTYPE_Pointer : dtyp) ([], List.repeat [] (S (List.length params))) [] [].
Proof.
  intros. unfold mk_fun. destruct (translate_cfg _ _ _ _ _ _ _ _) as [blks f].
  unfold cdecl, convert_typ, ConvertTyp_declaration, tfmap, TFunctor_declaration.
  cbn [df_prototype dc_name dc_type dc_param_attrs dc_attrs dc_annotations].
  rewrite cty_Function. destruct name; f_equal; cbn; f_equal.
  all: induction (List.length params) as [|k IH]; cbn; congruence.
Qed.

Lemma mk_fun_args : forall get_ord get_arity prim_of fs name params body,
  df_args (mk_fun get_ord get_arity prim_of fs name params body)
  = Name "tinfo" :: map (fun v => Raw (Zpos v)) params.
Proof. intros. unfold mk_fun. destruct (translate_cfg _ _ _ _ _ _ _ _); reflexivity. Qed.

Lemma mk_fun_proto_name : forall get_ord get_arity prim_of fs name params body,
  dc_name (df_prototype (mk_fun get_ord get_arity prim_of fs name params body)) = name.
Proof. intros. unfold mk_fun. destruct (translate_cfg _ _ _ _ _ _ _ _); reflexivity. Qed.

(** The block list of [mk_fun] is the one [translate_cfg] produced (when non-empty). *)
Lemma mk_fun_blocks : forall get_ord get_arity prim_of fs name params body blks n,
  translate_cfg get_ord get_arity prim_of fs base_env 0%N body 1%positive = (blks, n) ->
  blks <> [] ->
  let d := mk_fun get_ord get_arity prim_of fs name params body in
  fst (df_instrs d) :: snd (df_instrs d) = blks.
Proof.
  intros * H Hne d. subst d. unfold mk_fun. rewrite H. destruct blks; [congruence|reflexivity].
Qed.

(** [flat_def] keeps prototype, arguments and the entry block's id. *)
Lemma flat_def_eq : forall d : Ldef,
  flat_def d =
  mk_definition (df_prototype d) (df_args d)
    (fst (flat_block (fst (df_instrs d)) 1%positive),
     fst (flat_blocks (snd (df_instrs d)) (snd (flat_block (fst (df_instrs d)) 1%positive)))).
Proof.
  intros [p a [entry rest]]. unfold flat_def. cbn.
  destruct (flat_block entry 1) as [e' n1]. cbn. destruct (flat_blocks rest n1) as [r' n2]. reflexivity.
Qed.

Lemma flat_block_id : forall b c, blk_id (fst (flat_block b c)) = blk_id b.
Proof.
  intros b c. unfold flat_block.
  destruct (flat_code (blk_code b) c) as [cc n1]. destruct (blk_term b) as [[tid tm] tmd].
  destruct (flat_term tm n1) as [[tc tm'] n2]. reflexivity.
Qed.

Lemma flat_blocks_ids : forall bs c, map blk_id (fst (flat_blocks bs c)) = map blk_id bs.
Proof.
  induction bs as [|b bs IH]; intros c; cbn; [reflexivity|].
  pose proof (flat_block_id b c) as Hb.
  destruct (flat_block b c) as [b' n1]. specialize (IH n1).
  destruct (flat_blocks bs n1) as [rs n2]. cbn in *. f_equal; assumption.
Qed.

Lemma flat_def_proto : forall d, df_prototype (flat_def d) = df_prototype d.
Proof. intros; rewrite flat_def_eq; reflexivity. Qed.
Lemma flat_def_args : forall d, df_args (flat_def d) = df_args d.
Proof. intros; rewrite flat_def_eq; reflexivity. Qed.
Lemma flat_def_init : forall d, blk_id (fst (df_instrs (flat_def d))) = blk_id (fst (df_instrs d)).
Proof. intros; rewrite flat_def_eq; cbn; apply flat_block_id. Qed.

(** Unfolded form of a converted definition, as seen by the semantics. *)
Lemma conv_def_fields : forall d : Ldef,
  df_prototype (conv_def d) = cdecl (df_prototype d) /\
  df_args (conv_def d) = df_args d /\
  CFG.init (df_instrs (conv_def d)) = blk_id (fst (df_instrs d)) /\
  CFG.blks (df_instrs (conv_def d)) = map cblock (fst (df_instrs d) :: snd (df_instrs d)) /\
  CFG.args (df_instrs (conv_def d)) = df_args d.
Proof. intros; repeat split. Qed.
