(* ANF conversion from MetaRocq Erasure (EAst.term) to LambdaANF.cps *)

(** Stdlib *)
From Stdlib Require Import ZArith.ZArith Lists.List Arith.Arith Sets.Ensembles.

(** MetaRocq *)
From MetaRocq.Erasure Require Import EAst EGlobalEnv.
From MetaRocq.Utils Require Import bytestring.

(** ExtLib *)
From ExtLib Require Import Data.String Data.Monads.OptionMonad Structures.Monads.

(** CompCert *)
From compcert Require Import lib.Coqlib lib.Maps.

(** CertiRocq *)
From CertiRocq.Common Require Import AstCommon compM.
From CertiRocq Require Import Pipeline_utils.
From CertiRocq.LambdaANF Require Import
  cps cps_show eval ctx List_util Ensembles_util state
  LambdaBox_to_LambdaANF_common.

Import ListNotations.
Import Monad.MonadNotation.
Open Scope monad_scope.
Open Scope bs_scope.

(** This file defines ANF conversion from MetaRocq's erased terms
    (EAst.term) to LambdaANF (cps.exp).

    Global constants (tConst) are translated to variable references via a
    [kername -> var] map. The global environment bodies are converted separately
    into the initial LambdaANF environment. *)


(** Outer section: parameters shared by both conversion and spec *)
Section ANF.

  Context (func_tag default_tag : positive).


  (** * Monadic ANF conversion *)

  Section Conversion.

    Context (prim_map : M.t primitive).
    Context (kon_tag default_itag : positive)
            (next_id : positive).
    Context (tgm : conId_map).
    Context (prims : list (primitive * positive)).
    Context (cmap : const_map).

    Definition anfM := @compM' unit.

    Definition var_map := (M.t var * N)%type.

    Definition get_var_name (vmp : var_map) (x : N) :=
      let (vm, p) := vmp in
      match (p - x)%N with
      | N0 => None
      | Npos pos => M.get pos vm
      end.

    Definition add_var_name (vmp : var_map) (x' : var) :=
      let (vm, p) := vmp in
      let p' := N.succ_pos p in
      (M.set p' x' vm, Npos p').

    Definition new_var_map := (M.empty var, 0%N).

    Definition def_name := nNamed "y"%bs.

    (** Bind projections for a match branch *)
    Definition proj_ctx (names : list name) (n : nat)
               (scrut : var) (vm : var_map) ct : anfM (exp_ctx * var_map) :=
      vars <- get_named_lst (names_lst_len names n) ;;
      let ctx_p := ctx_bind_proj ct scrut vars (List.length vars) in
      let vm' := List.fold_right (fun v vm' => add_var_name vm' v) vm vars in
      ret (ctx_p, vm').

    (** Add names for mutually recursive functions *)
    Fixpoint add_fix_names (mfix : list (EAst.def EAst.term)) (vm : var_map)
      : anfM (list var * var_map) :=
      match mfix with
      | [] => ret ([], vm)
      | d :: mfix' =>
        f_name <- get_named d.(EAst.dname) ;;
        lvm <- add_fix_names mfix' (add_var_name vm f_name) ;;
        let '(fs, vm') := lvm in
        ret (f_name :: fs, vm')
      end.

    (** ANF conversion for primitive operations *)
    Fixpoint convert_prim_anf (n : nat) (prim : positive) (args : list var)
      : anfM (var * exp_ctx) :=
      match n with
      | 0%nat =>
        x <- get_named_str "prim"%bs ;;
        ret (x, Eprim_c x prim (List.rev args) Hole_c)
      | S n =>
        arg <- get_named_str "p_arg"%bs ;;
        f <- get_named_str "prim_wrapper"%bs ;;
        '(x, C) <- convert_prim_anf n prim (arg :: args) ;;
        ret (f, Efun1_c (Fcons f func_tag [arg] (C |[ Ehalt x ]|) Fnil) Hole_c)
      end.

    (** Helper: convert a list of terms *)
    Definition convert_anf_args
               (convert : EAst.term -> var_map -> anfM (var * exp_ctx))
               (args : list EAst.term) (vm : var_map) : anfM (list var * exp_ctx) :=
      (fix go args :=
         match args with
         | [] => ret ([], Hole_c)
         | t :: args' =>
           '(y, C1) <- convert t vm ;;
           '(ys, C2) <- go args' ;;
           ret (y :: ys, comp_ctx_f C1 C2)
         end) args.

    (** Helper: convert mutually recursive fixpoint bodies *)
    Definition convert_anf_mfix
               (convert : EAst.term -> var_map -> anfM (var * exp_ctx))
               (mfix : list (EAst.def EAst.term))
               (names : list var) (idx : nat) (vm : var_map) : anfM (var * fundefs) :=
      (fix go mfix names idx :=
         match mfix, names with
         | [], [] => ret (1%positive (* dummy *), Fnil)
         | d :: mfix', f_name :: names' =>
           match d.(EAst.dbody) with
           | EAst.tLambda na e1 =>
             x <- get_named na ;;
             '(r, C) <- convert e1 (add_var_name vm x) ;;
             ds <- go mfix' names' (Nat.pred idx) ;;
             let (fi, defs') := ds in
             let fi' := match idx with
                        | 0%nat => f_name
                        | Datatypes.S _ => fi
                        end in
             ret (fi', Fcons f_name func_tag [x] (C |[ Ehalt r ]|) defs')
           | _ => failwith "body of fix must be a lambda"
           end
         | _, _ => failwith "Wrong number of names for mut. rec. functions"
         end) mfix names idx.

    (** Helper: convert case branches *)
    Definition convert_anf_branches
               (convert : EAst.term -> var_map -> anfM (var * exp_ctx))
               (ind : inductive) (brs : list (list name * EAst.term))
               (n : N) (scrut : var) (vm : var_map)
      : anfM (list (ctor_tag * exp)) :=
      (fix go brs n :=
         match brs with
         | [] => ret []
         | (lnames, e) :: brs' =>
           let dc := dcon_of_con ind (N.to_nat n) in
           let ctag := dcon_to_tag default_tag dc tgm in
           pats' <- go brs' (n + 1)%N ;;
           cm <- proj_ctx (List.rev lnames) (List.length lnames) scrut vm ctag ;;
           let (Cproj, vm') := cm in
           '(r, C) <- convert e vm' ;;
           ret ((ctag, app_ctx_f Cproj (C |[ Ehalt r ]|)) :: pats')
         end) brs n.

    (** Main ANF conversion *)
    Fixpoint convert_anf (t : EAst.term) (vm : var_map)
      {struct t} : anfM (var * exp_ctx) :=
      match t with
      | EAst.tRel n =>
        match get_var_name vm (N.of_nat n) with
        | Some v => ret (v, Hole_c)
        | None => failwith "Unknown de Bruijn index"
        end

      | EAst.tBox =>
        x <- get_named_str "y"%bs ;;
        ret (x, Econstr_c x default_tag [] Hole_c)

      | EAst.tLambda na body =>
        x <- get_named na ;;
        f <- get_named def_name ;;
        '(r, C) <- convert_anf body (add_var_name vm x) ;;
        ret (f, Efun1_c (Fcons f func_tag [x] (C |[ Ehalt r ]|) Fnil) Hole_c)

      | EAst.tLetIn na b t =>
        '(x, C1) <- convert_anf b vm ;;
        '(r, C2) <- convert_anf t (add_var_name vm x) ;;
        ret (r, comp_ctx_f C1 C2)

      | EAst.tApp u v =>
        '(x1, C1) <- convert_anf u vm ;;
        '(x2, C2) <- convert_anf v vm ;;
        r <- get_named def_name ;;
        ret (r, comp_ctx_f C1 (comp_ctx_f C2 (Eletapp_c r x1 func_tag [x2] Hole_c)))

      | EAst.tConst s =>
        match find_prim prims s with
        | Some p =>
          match M.get p prim_map with
          | Some pr => convert_prim_anf pr.(prim_arity) p []
          | None => failwith "Internal error: identifier for primitive not found"
          end
        | None =>
          match lookup_const cmap s with
          | Some v => ret (v, Hole_c)
          | None => failwith "Unknown constant"
          end
        end

      | EAst.tConstruct ind c args =>
        let c_tag := dcon_to_tag default_tag (dcon_of_con ind c) tgm in
        x <- get_named def_name ;;
        '(ys, C) <- convert_anf_args convert_anf args vm ;;
        ret (x, comp_ctx_f C (Econstr_c x c_tag ys Hole_c))

      | EAst.tCase (ind, npars) mch brs =>
        f <- get_named_str "f_case"%bs ;;
        y <- get_named_str "s"%bs ;;
        '(x1, C1) <- convert_anf mch vm ;;
        pats <- convert_anf_branches convert_anf ind brs 0%N y vm ;;
        r <- get_named def_name ;;
        ret (r, Efun1_c (Fcons f func_tag [y] (Ecase y pats) Fnil)
                        (comp_ctx_f C1 (Eletapp_c r f func_tag [x1] Hole_c)))

      | EAst.tFix mfix idx =>
        lvm <- add_fix_names mfix vm ;;
        let (names, vm') := lvm in
        '(x, defs) <- convert_anf_mfix convert_anf mfix names idx vm' ;;
        ret (x, Efun1_c defs Hole_c)

      | EAst.tProj p c =>
        let c_tag := dcon_to_tag default_tag (dcon_of_con p.(proj_ind) 0) tgm in
        '(x, C) <- convert_anf c vm ;;
        y <- get_named def_name ;;
        ret (y, comp_ctx_f C (Eproj_c y c_tag (N.of_nat p.(proj_arg)) x Hole_c))

      | EAst.tPrim p =>
        match trans_prim_val p with
        | Some pv =>
          x <- get_named_str "y"%bs ;;
          ret (x, Eprim_val_c x pv Hole_c)
        | None => failwith "Unsupported primitive type (arrays)"
        end

      (* These should not occur *)
      | EAst.tVar _ => failwith "Var"
      | EAst.tEvar _ _ => failwith "Evar"
      | EAst.tCoFix _ _ => failwith "CoFix"
      | EAst.tLazy _ => failwith "Lazy"
      | EAst.tForce _ => failwith "Force"
      end.

    (** ** Top-level conversion of a single expression *)

    Definition convert_anf_exp (e : EAst.term) : anfM cps.exp :=
      '(x, C) <- convert_anf e new_var_map ;;
      ret (C |[ Ehalt x ]|).

  End Conversion.


  (** * Environment conversion and top-level *)

  Section TopLevel.

    Context (prim_map : M.t primitive).
    Context (kon_tag default_itag : positive)
            (next_id : positive).
    Context (tgm : conId_map).
    Context (prims : list (primitive * positive)).

    (** Convert the global environment.
        Walks declarations in order. Each constant body (assumed to be a value)
        is converted to ANF, producing a binding context that directly places
        the value in rho. The [const_map] is built incrementally so each
        constant can reference previously defined ones.
        Returns the final [const_map] and a composed binding context. *)
    Fixpoint convert_global_decls (gd : EAst.global_declarations)
             (cm_acc : const_map) : (@compM' unit) (const_map * exp_ctx) :=
      match gd with
      | [] => ret (cm_acc, Hole_c)
      | (k, EAst.ConstantDecl {| EAst.cst_body := Some body |}) :: gd' =>
        '(v, C) <- convert_anf prim_map tgm prims cm_acc body (M.empty var, 0%N) ;;
        '(cm', C_rest) <- convert_global_decls gd' ((k, v) :: cm_acc) ;;
        ret (cm', comp_ctx_f C C_rest)
      | (_, EAst.ConstantDecl {| EAst.cst_body := None |}) :: gd' =>
        convert_global_decls gd' cm_acc
      | (_, EAst.InductiveDecl _) :: gd' =>
        convert_global_decls gd' cm_acc
      end.

    (** Convert a full program: global environment + main expression.
        Global constant bindings are composed around the main expression,
        producing a single [cps.exp] where all globals are in rho. *)
    Definition convert_top_anf (ie : ienv) (gd : EAst.global_declarations) (e : EAst.term)
      : error cps.exp * comp_data :=
      let '(_, cenv, ctag, itag, _dcm) := convert_env default_tag default_itag ie in
      let ftag := (func_tag + 1)%positive in
      let fenv : fun_env := M.set func_tag (1%N, (0%N::nil)) (M.empty _) in
      let comp_d := pack_data next_id ctag itag ftag cenv fenv (M.empty _) (M.empty nat) [] in
      let prog :=
        '(cm, C_env) <- convert_global_decls gd [] ;;
        '(x, C_main) <- convert_anf prim_map tgm prims cm e (M.empty var, 0%N) ;;
        ret (C_env |[ C_main |[ Ehalt x ]| ]|)
      in
      let '(res_err, (comp_d', _)) := run_compM prog comp_d tt in
      (res_err, comp_d').

  End TopLevel.


  (** * Declarative relational specification *)

  Section Spec.

    Context (tgm : conId_map).
    Context (cmap : const_map).

    Inductive anf_cvt_rel : Ensemble var ->
                            EAst.term ->
                            list var ->
                            Ensemble var ->
                            exp_ctx ->
                            var ->
                            Prop :=
    | anf_Rel :
        forall S v vn n,
          nth_error vn n = Some v ->
          anf_cvt_rel S (EAst.tRel n) vn S Hole_c v
    | anf_Lam :
        forall S S' na e1 C1 r1 x1 f vn,
          x1 \in S ->
          f \in (S \\ [set x1]) ->
          anf_cvt_rel (S \\ [set x1] \\ [set f]) e1 (x1::vn) S' C1 r1 ->
          anf_cvt_rel S
                      (EAst.tLambda na e1)
                      vn S'
                      (Efun1_c (Fcons f func_tag [x1] (C1 |[ Ehalt r1 ]|) Fnil) Hole_c)
                      f
    | anf_App :
        forall S1 S2 S3 u C1 x1 v C2 x2 r vn,
          anf_cvt_rel S1 u vn S2 C1 x1 ->
          anf_cvt_rel S2 v vn S3 C2 x2 ->
          r \in S3 ->
          anf_cvt_rel S1
                      (EAst.tApp u v)
                      vn
                      (S3 \\ [set r])
                      (comp_ctx_f C1 (comp_ctx_f C2 (Eletapp_c r x1 func_tag [x2] Hole_c)))
                      r
    | anf_Construct :
        forall S1 S2 c_tag ind c args C xs x vn,
          c_tag = dcon_to_tag default_tag (dcon_of_con ind c) tgm ->
          x \in S1 ->
          anf_cvt_rel_args (S1 \\ [set x]) args vn S2 C xs ->
          anf_cvt_rel S1
                      (EAst.tConstruct ind c args)
                      vn S2
                      (comp_ctx_f C (Econstr_c x c_tag xs Hole_c))
                      x
    | anf_LetIn :
        forall S1 S2 S3 na b t C1 x1 C2 x2 vn,
          anf_cvt_rel S1 b vn S2 C1 x1 ->
          anf_cvt_rel S2 t (x1::vn) S3 C2 x2 ->
          anf_cvt_rel S1
                      (EAst.tLetIn na b t)
                      vn S3
                      (comp_ctx_f C1 C2)
                      x2
    | anf_Case :
        forall S1 S2 S3 ind npars mch C1 x1 brs pats f y r vn,
          f \in S1 ->
          y \in (S1 \\ [set f]) ->
          anf_cvt_rel (S1 \\ [set f] \\ [set y]) mch vn S2 C1 x1 ->
          anf_cvt_rel_branches S2 ind brs 0%N vn y S3 pats ->
          r \in S3 ->
          anf_cvt_rel S1
                      (EAst.tCase (ind, npars) mch brs)
                      vn
                      (S3 \\ [set r])
                      (Efun1_c (Fcons f func_tag [y] (Ecase y pats) Fnil)
                               (comp_ctx_f C1 (Eletapp_c r f func_tag [x1] Hole_c)))
                      r
    | anf_Fix :
        forall S1 S2 mfix idx f fnames vn fdefs,
          FromList fnames \subset S1 ->
          NoDup fnames ->
          List.length fnames = List.length mfix ->
          anf_cvt_rel_mfix (S1 \\ (FromList fnames)) mfix (List.rev fnames ++ vn) fnames S2 fdefs ->
          nth_error fnames idx = Some f ->
          anf_cvt_rel S1
                      (EAst.tFix mfix idx)
                      vn S2
                      (Efun1_c fdefs Hole_c)
                      f
    | anf_Box :
        forall S vn x,
          x \in S ->
          anf_cvt_rel S EAst.tBox vn (S \\ [set x]) (Econstr_c x default_tag nil Hole_c) x
    | anf_Const :
        forall S vn s v,
          lookup_const cmap s = Some v ->
          anf_cvt_rel S (EAst.tConst s) vn S Hole_c v
    | anf_Proj :
        forall S1 S2 p c C x y vn c_tag,
          c_tag = dcon_to_tag default_tag (dcon_of_con p.(proj_ind) 0) tgm ->
          anf_cvt_rel S1 c vn S2 C x ->
          y \in S2 ->
          anf_cvt_rel S1
                      (EAst.tProj p c)
                      vn
                      (S2 \\ [set y])
                      (comp_ctx_f C (Eproj_c y c_tag (N.of_nat p.(proj_arg)) x Hole_c))
                      y
    | anf_Prim :
        forall S vn p pv x,
          trans_prim_val p = Some pv ->
          x \in S ->
          anf_cvt_rel S (EAst.tPrim p) vn (S \\ [set x]) (Eprim_val_c x pv Hole_c) x

    with anf_cvt_rel_args :
           Ensemble var -> list EAst.term -> list var ->
           Ensemble var -> exp_ctx -> list var -> Prop :=
    | anf_Args_nil :
        forall S vn,
          anf_cvt_rel_args S [] vn S Hole_c []
    | anf_Args_cons :
        forall S1 S2 S3 vn t ts C1 x1 C2 xs,
          anf_cvt_rel S1 t vn S2 C1 x1 ->
          anf_cvt_rel_args S2 ts vn S3 C2 xs ->
          anf_cvt_rel_args S1 (t :: ts) vn S3 (comp_ctx_f C1 C2) (x1 :: xs)

    with anf_cvt_rel_mfix :
           Ensemble var ->
           list (EAst.def EAst.term) ->
           list var -> list var ->
           Ensemble var -> fundefs -> Prop :=
    | anf_Mfix_nil :
        forall S vn,
          anf_cvt_rel_mfix S [] vn [] S Fnil
    | anf_Mfix_cons :
        forall S1 S2 S3 vn fnames d mfix' C1 r1 fdefs na e1 x1 f_name,
          d.(EAst.dbody) = EAst.tLambda na e1 ->
          x1 \in S1 ->
          anf_cvt_rel (S1 \\ [set x1]) e1 (x1::vn) S2 C1 r1 ->
          anf_cvt_rel_mfix S2 mfix' vn fnames S3 fdefs ->
          anf_cvt_rel_mfix
            S1 (d :: mfix') vn (f_name :: fnames) S3
            (Fcons f_name func_tag [x1] (C1 |[ Ehalt r1 ]|) fdefs)

    with anf_cvt_rel_branches :
           Ensemble var -> inductive ->
           list (list name * EAst.term) ->
           N -> list var -> var ->
           Ensemble var -> list (ctor_tag * exp) -> Prop :=
    | anf_Branches_nil :
        forall S ind vn r,
          anf_cvt_rel_branches S ind [] 0%N vn r S []
    | anf_Branches_cons :
        forall S1 S2 S3 ind vn r lnames e brs' pats' C1 r1 vars ctx_p tg n,
          tg = dcon_to_tag default_tag (dcon_of_con ind (N.to_nat n)) tgm ->
          anf_cvt_rel_branches S1 ind brs' (n + 1)%N vn r S2 pats' ->
          FromList vars \subset S2 ->
          NoDup vars ->
          Datatypes.length vars = List.length lnames ->
          ctx_bind_proj tg r vars (Datatypes.length vars) = ctx_p ->
          anf_cvt_rel (S2 \\ (FromList vars)) e (vars ++ vn) S3 C1 r1 ->
          anf_cvt_rel_branches
            S1 ind ((lnames, e) :: brs') n vn r S3
            ((tg, app_ctx_f ctx_p (C1 |[ Ehalt r1 ]|)) :: pats').

  End Spec.

End ANF.
