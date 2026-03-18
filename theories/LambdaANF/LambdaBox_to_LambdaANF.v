(* Direct ANF conversion from MetaRocq Erasure (EAst.term) to LambdaANF.cps *)

From Stdlib Require Import ZArith.ZArith Lists.List
        Sorting.Sorted Arith.Arith Sets.Ensembles.
Require Import ExtLib.Data.String.
From CertiRocq Require Import Common.AstCommon Common.compM Pipeline_utils.

From MetaRocq.Erasure Require Import EAst EGlobalEnv.
From MetaRocq.Utils Require Import bytestring.

Require Import LambdaANF.cps LambdaANF.cps_show LambdaANF.eval LambdaANF.ctx
        LambdaANF.List_util LambdaANF.Ensembles_util LambdaANF.state.
Require Import compcert.lib.Coqlib compcert.lib.Maps.

Require Import ExtLib.Data.Monads.OptionMonad ExtLib.Structures.Monads.

Import ListNotations.
Import Monad.MonadNotation.
Open Scope monad_scope.
Open Scope bs_scope.

Local Notation string := bytestring.string.

(** This file defines ANF conversion from MetaRocq's erased terms
    (EAst.term) to LambdaANF (cps.exp).

    Global constants (tConst) are translated to variable references via a
    [kername -> var] map. The global environment bodies are converted separately
    into the initial LambdaANF environment. *)

Section Translate.

  Context (prim_map : M.t primitive).
  Context (func_tag kon_tag default_tag default_itag : positive)
          (next_id : positive).


  (** * Common definitions (shared with CPS) *)

  (** Constructor discriminant: inductive type paired with constructor index *)
  Definition dcon : Set := inductive * N.

  Definition conId_map := list (dcon * ctor_tag).

  Theorem conId_dec: forall x y:dcon, {x = y} + {x <> y}.
  Proof.
    intros. destruct x,y.
    assert (H:= AstCommon.inductive_dec i i0).
    destruct H.
    - destruct (classes.eq_dec n n0).
      + subst. left. auto.
      + right. intro. apply n1. inversion H. auto.
    - right; intro; apply n1. inversion H; auto.
  Defined.

  Fixpoint dcon_to_info (a:dcon) (sig:conId_map) :=
    match sig with
    | nil => default_tag
    | ((cId, inf)::sig') => match conId_dec a cId with
                            | left _ => inf
                            | right _ => dcon_to_info a sig'
                            end
    end.

  Definition constr_env : Type := conId_map.

  Definition dcon_to_tag (a:dcon) (sig:conId_map) :=
    dcon_to_info a sig.

  Definition dcon_of_con (i : inductive) (n : nat) : dcon := (i, N.of_nat n).


  (** * Global constant environment *)

  (** Map from global constant names to LambdaANF variables.
      Built when processing the global environment; used to translate [tConst]. *)
  Definition const_map := list (kername * var).

  Fixpoint lookup_const (cm : const_map) (k : kername) : option var :=
    match cm with
    | [] => None
    | (k', v) :: cm' =>
      if eq_kername k k' then Some v else lookup_const cm' k
    end.

  (** Primitive lookup *)
  Fixpoint find_prim (prims : list (primitive * positive)) (n : kername) : option positive :=
    match prims with
    | [] => None
    | (prim, pos) :: prims =>
      if eq_kername n prim.(prim_name) then Some pos else find_prim prims n
    end.


  (** * Inductive environment processing *)

  Definition ienv := list (Kernames.kername * AstCommon.itypPack).

  Fixpoint fromN (n:positive) (m:nat) : list positive * positive :=
    match m with
    | O => (nil, n)
    | S m' =>
      let (l, nm) := (fromN (n+1) (m')) in
      (n::l, nm)
    end.

  Fixpoint ctx_bind_proj (tg:ctor_tag) (r:positive) (vars : list var) (args:nat)
    : exp_ctx :=
    match vars with
    | [] => Hole_c
    | v :: vars =>
      let ctx_p' := ctx_bind_proj tg r vars (args - 1) in
      (Eproj_c v tg (N.of_nat (args - 1)) r ctx_p')
    end.

  Fixpoint convert_cnstrs (tyname:string) (cct:list ctor_tag) (itC:list AstCommon.Cnstr)
           (ind:Kernames.inductive) (nCon:N) (unboxed : N) (boxed : N)
           (niT:ind_tag) (ce:ctor_env) (dcm:conId_map) :=
    match (cct, itC) with
    | (cn::cct', cst::icT') =>
      let (cname, ccn) := cst in
      let is_unboxed := Nat.eqb ccn 0 in
      let info := {| ctor_name := BasicAst.nNamed cname
                     ; ctor_ind_name := BasicAst.nNamed tyname
                     ; ctor_ind_tag := niT
                     ; ctor_arity := N.of_nat ccn
                     ; ctor_ordinal := if is_unboxed then unboxed else boxed
                  |} in
      convert_cnstrs tyname cct' icT' ind (nCon+1)%N
                     (if is_unboxed then unboxed + 1 else unboxed)
                     (if is_unboxed then boxed else boxed + 1)
                     niT
                     (M.set cn info ce)
                     (((ind,nCon), cn)::dcm)
    | (_, _) => (ce, dcm)
    end.

  Fixpoint convert_typack typ (idBundle:Kernames.kername) (n:nat)
           (ice : (ind_env * ctor_env * ctor_tag * ind_tag * conId_map))
    : (ind_env * ctor_env * ctor_tag * ind_tag * conId_map) :=
    let '(ie, ce, ncT, niT, dcm) := ice in
    match typ with
    | nil => ice
    | (AstCommon.mkItyp itN itC) :: typ' =>
      let (cct, ncT') := fromN ncT (List.length itC) in
      let (ce', dcm') :=
          convert_cnstrs itN cct itC (Kernames.mkInd idBundle n) 0 0 0 niT ce dcm
      in
      let ityi :=
          combine cct (map (fun (c:AstCommon.Cnstr) =>
                              let (_, n) := c in N.of_nat n) itC)
      in
      convert_typack typ' idBundle (n+1)
                     (M.set niT ityi ie, ce', ncT', (Pos.succ niT), dcm')
    end.

  Fixpoint convert_env' (g:ienv) (ice:ind_env * ctor_env * ctor_tag * ind_tag * conId_map)
    : (ind_env * ctor_env * ctor_tag * ind_tag * conId_map) :=
    let '(ie, ce, ncT, niT, dcm) := ice in
    match g with
    | nil => ice
    | (id, ty)::g' =>
      convert_env' g' (convert_typack ty id 0 (ie, ce, ncT, niT, dcm))
    end.

  Definition convert_env (g:ienv): (ind_env * ctor_env * ctor_tag * ind_tag * conId_map) :=
    let default_ind_env := M.set default_itag (cons (default_tag, 0%N) nil) (M.empty ind_ty_info) in
    let info := {| ctor_name := BasicAst.nAnon
                   ; ctor_ind_name := BasicAst.nAnon
                   ; ctor_ind_tag := default_itag
                   ; ctor_arity := 0%N
                   ; ctor_ordinal := 0%N
                |} in
    let default_ctor_env := M.set default_tag info (M.empty ctor_ty_info) in
    convert_env' g (default_ind_env, default_ctor_env, (Pos.succ default_tag:ctor_tag), (Pos.succ default_itag:ind_tag), nil).


  (** * ANF conversion *)

  Section ANF.

    Definition anfM := @compM' unit.

    (** Variable map: maps de Bruijn indices to named variables.
        The map grows from 1 onward. To lookup de Bruijn index i,
        we lookup (p - i) in the map. *)
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

    Inductive anf_value :=
    | Anf_Var (x : var)
    | Anf_App (f x : var)
    | Constr (c : ctor_tag) (xs : list var)
    | Proj (c : ctor_tag) (n : N) (y : var)
    | Fun (ft : cps.fun_tag) (x : var) (e : cps.exp)
    | Anf_Prim_val (p : AstCommon.primitive_value)
    | Anf_Prim (pr : positive) (xs : list var).

    Definition anf_term : Type := anf_value * exp_ctx.

    Definition def_name := nNamed "y"%bs.


    Section Convert.

      Context (tgm : conId_map).
      Context (prims : list (primitive * positive)).
      Context (cmap : const_map).

      (** Helper: compute names from branch argument name list, padding with nAnon *)
      Fixpoint names_lst_len (ns : list name) (m : nat) : list name :=
        match ns, m with
        | _, 0%nat => []
        | [], S _ => repeat nAnon m
        | n :: ns, S m => n :: names_lst_len ns m
        end.

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


      (** ** Main ANF conversion from EAst.term *)

      (** Helper: convert a list of terms (e.g., constructor args) *)
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
             let ctag := dcon_to_tag dc tgm in
             pats' <- go brs' (n + 1)%N ;;
             cm <- proj_ctx (List.rev lnames) (List.length lnames) scrut vm ctag ;;
             let (Cproj, vm') := cm in
             '(r, C) <- convert e vm' ;;
             ret ((ctag, app_ctx_f Cproj (C |[ Ehalt r ]|)) :: pats')
           end) brs n.


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
          let c_tag := dcon_to_tag (dcon_of_con ind c) tgm in
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

        | EAst.tPrim p =>
          failwith "Primitive values not yet supported in direct ANF"

        (* These should not occur *)
        | EAst.tVar _ => failwith "Var"
        | EAst.tEvar _ _ => failwith "Evar"
        | EAst.tProj p c =>
          let c_tag := dcon_to_tag (dcon_of_con p.(proj_ind) 0) tgm in
          '(x, C) <- convert_anf c vm ;;
          y <- get_named def_name ;;
          ret (y, comp_ctx_f C (Eproj_c y c_tag (N.of_nat p.(proj_arg)) x Hole_c))
        | EAst.tCoFix _ _ => failwith "CoFix"
        | EAst.tLazy _ => failwith "Lazy"
        | EAst.tForce _ => failwith "Force"
        end.

    End Convert.


    (** * Top-level ANF conversion *)

    Definition convert_anf_exp (dcm : conId_map) (prims : list (primitive * positive))
               (cmap : const_map) (e : EAst.term) : anfM cps.exp :=
      '(x, C) <- convert_anf dcm prims cmap e new_var_map ;;
      ret (C |[ Ehalt x ]|).

    Definition convert_top_anf (ienv : ienv) (prims : list (primitive * positive))
               (cmap : const_map) (e : EAst.term) : error cps.exp * comp_data :=
      let '(_, cenv, ctag, itag, dcm) := convert_env ienv in
      let ftag := (func_tag + 1)%positive in
      let fenv : fun_env := M.set func_tag (1%N, (0%N::nil)) (M.empty _) in
      let comp_d := pack_data next_id ctag itag ftag cenv fenv (M.empty _) (M.empty nat) [] in
      let '(res_err, (comp_d', _)) := run_compM (convert_anf_exp dcm prims cmap e) comp_d tt in
      (res_err, comp_d').

  End ANF.

End Translate.
