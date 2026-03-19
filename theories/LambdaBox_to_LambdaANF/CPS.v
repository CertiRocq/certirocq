(* CPS conversion from MetaRocq Erasure (EAst.term) to LambdaANF.cps *)

(** Stdlib *)
From Stdlib Require Import ZArith.ZArith Lists.List Arith.Arith Sets.Ensembles.

(** MetaRocq *)
From MetaRocq.Erasure Require Import EAst.
From MetaRocq.Utils Require Import bytestring.

(** ExtLib *)
From ExtLib Require Import Data.Monads.OptionMonad Structures.Monads.

(** CompCert *)
From compcert Require Import lib.Maps.

(** CertiRocq *)
From CertiRocq.Common Require Import AstCommon compM.
From CertiRocq Require Import Pipeline_utils.
From CertiRocq.LambdaANF Require Import cps ctx state.
From CertiRocq.LambdaBox_to_LambdaANF Require Import common.

Import ListNotations.
Import Monad.MonadNotation.
Open Scope monad_scope.
Open Scope bs_scope.

(** This file defines CPS conversion from MetaRocq's erased terms
    (EAst.term) to LambdaANF (cps.exp).

    Global constants (tConst) are translated to variable references via a
    [kername -> var] map. The global environment bodies are converted separately
    into the initial LambdaANF environment. *)

Section Translate.

  Context (prim_map : M.t primitive).
  Context (func_tag kon_tag default_tag default_itag : positive)
          (next_id : positive).


  (** * CPS conversion *)

  Section CPS.

    Definition cpsM := @compM' unit.

    Definition get_named_str_lst (s : list bytestring.string) : cpsM (list var) :=
      mapM get_named_str s.

    (** CPS conversion for primitive operations *)
    Fixpoint convert_prim (n : nat) (prim : positive) (args : list var) (kont : var)
      : cpsM cps.exp :=
      match n with
      | 0%nat =>
        pr <- get_named_str "prim" ;;
        ret (Eprim pr prim (List.rev args) (Eapp kont kon_tag [pr]))
      | S n =>
        arg <- get_named_str "p_arg" ;;
        kont1 <- get_named_str "p_k" ;;
        f <- get_named_str "prim_wrapper" ;;
        trm <- convert_prim n prim (arg :: args) kont1 ;;
        ret (Efun (Fcons f func_tag [kont1; arg] trm Fnil) (Eapp kont kon_tag [f]))
      end.


    Section Convert.

      Context (tgm : conId_map).
      Context (prims : list (primitive * positive)).
      Context (cmap : const_map).

      (** ** Helper: CPS convert constructor arguments *)
      Definition cps_cvt_args
                 (cvt : EAst.term -> list var -> var -> cpsM cps.exp)
                 (args : list EAst.term) (vn : list var) (e_app : exp)
                 (xs ks : list var) : cpsM cps.exp :=
        (fix go args xs ks :=
           match args with
           | [] => ret e_app
           | t :: args' =>
             match xs, ks with
             | [], _ | _, [] =>
               failwith "Internal error: wrong number of arguments in constructor continuation"
             | x1 :: xs', k1 :: ks' =>
               t' <- cvt t vn k1 ;;
               e_exp <- go args' xs' ks' ;;
               ret (Efun (Fcons k1 kon_tag (x1::nil) e_exp Fnil) t')
             end
           end) args xs ks.

      (** Helper: CPS convert mutually recursive fixpoint bodies *)
      Definition cps_cvt_mfix
                 (cvt : EAst.term -> list var -> var -> cpsM cps.exp)
                 (mfix : list (EAst.def EAst.term)) (vn : list var)
                 (nlst : list var) : cpsM fundefs :=
        (fix go mfix nlst :=
           match mfix with
           | [] => ret Fnil
           | d :: mfix' =>
             x <- get_named_str "x" ;;
             k' <- get_named_str "k" ;;
             let curr_var := List.hd 1%positive nlst in
             match d.(EAst.dbody) with
             | EAst.tLambda na e2 =>
               ce <- cvt e2 (x::vn) k' ;;
               cfdefs <- go mfix' (List.tl nlst) ;;
               ret (Fcons curr_var func_tag (k'::x::nil) ce cfdefs)
             | _ => failwith "body of fix must be a lambda expr"
             end
           end) mfix nlst.

      (** Helper: CPS convert case branches *)
      Definition cps_cvt_branches
                 (cvt : EAst.term -> list var -> var -> cpsM cps.exp)
                 (ind : inductive) (brs : list (list name * EAst.term))
                 (n : N) (vn : list var) (k : var) (r : var)
        : cpsM (list (ctor_tag * exp)) :=
        (fix go (brs : list (list name * EAst.term)) (n : N)
             : cpsM (list (ctor_tag * exp)) :=
           match brs with
           | [] => ret nil
           | (lnames, e) :: brs' =>
             let dc := dcon_of_con ind (N.to_nat n) in
             let tg := dcon_to_tag default_tag dc tgm in
             cbl <- go brs' (n + 1)%N ;;
             vars <- get_named_lst (names_lst_len (List.rev lnames) (List.length lnames)) ;;
             let ctx_p := ctx_bind_proj tg r vars (List.length vars) in
             ce <- cvt e (List.app vars vn) k ;;
             ret ((tg, app_ctx_f ctx_p ce)::cbl)
           end) brs n.


      (** ** Main CPS conversion from EAst.term *)

      Fixpoint cps_cvt (t : EAst.term) (vn : list var) (k : var)
        {struct t} : cpsM cps.exp :=
        match t with
        | EAst.tRel n =>
          match nth_error vn n with
          | Some v => ret (cps.Eapp k kon_tag (v::nil))
          | None => failwith "Unknown de Bruijn index"
          end

        | EAst.tBox =>
          x <- get_named_str "x" ;;
          ret (Econstr x default_tag nil (Eapp k kon_tag (x::nil)))

        | EAst.tLambda na e1 =>
          x1 <- get_named_str "x1" ;;
          f <- get_named na ;;
          k1 <- get_named_str "k1" ;;
          e1' <- cps_cvt e1 (x1::vn) k1 ;;
          ret (Efun
                 (Fcons f func_tag (k1::x1::nil) e1' Fnil)
                 (cps.Eapp k kon_tag (f::nil)))

        | EAst.tLetIn na b t =>
          x <- get_named_str (string_of_name na) ;;
          k1 <- get_named_str "k" ;;
          t' <- cps_cvt t (x::vn) k ;;
          b' <- cps_cvt b vn k1 ;;
          ret (Efun
                 (Fcons k1 kon_tag (x::nil) t' Fnil)
                 b')

        | EAst.tApp u v =>
          x1 <- get_named_str "x1" ;;
          k1 <- get_named_str "k1" ;;
          x2 <- get_named_str "x2" ;;
          k2 <- get_named_str "k2" ;;
          u' <- cps_cvt u vn k1 ;;
          v' <- cps_cvt v vn k2 ;;
          ret (Efun
                 (Fcons k1 kon_tag (x1::nil)
                        (cps.Efun
                           (Fcons k2 kon_tag (x2::nil)
                                  (cps.Eapp x1 func_tag (k::x2::nil)) Fnil)
                           v') Fnil)
                 u')

        | EAst.tConst s =>
          match find_prim prims s with
          | Some p =>
            match M.get p prim_map with
            | Some pr => convert_prim pr.(prim_arity) p [] k
            | None => failwith "Internal error: identifier for primitive not found"
            end
          | None =>
            match lookup_const cmap s with
            | Some v => ret (cps.Eapp k kon_tag (v::nil))
            | None => failwith "Unknown constant"
            end
          end

        | EAst.tConstruct ind c args =>
          let c_tag := dcon_to_tag default_tag (dcon_of_con ind c) tgm in
          x' <- get_named_str "x'" ;;
          xs <- get_named_str_lst (map (fun _ => "x") args) ;;
          ks <- get_named_str_lst (map (fun _ => "k") args) ;;
          cps_cvt_args cps_cvt args vn (Econstr x' c_tag xs (Eapp k kon_tag (x'::nil))) xs ks

        | EAst.tCase (ind, npars) mch brs =>
          x1 <- get_named_str "x1" ;;
          k1 <- get_named_str "k1" ;;
          mch' <- cps_cvt mch vn k1 ;;
          cbl <- cps_cvt_branches cps_cvt ind brs 0%N vn k x1 ;;
          ret (Efun (Fcons k1 kon_tag (x1::nil) (Ecase x1 cbl) Fnil) mch')

        | EAst.tFix mfix idx =>
          let names_lst := map (fun d => d.(EAst.dname)) mfix in
          nlst <- get_named_lst names_lst ;;
          fdefs <- cps_cvt_mfix cps_cvt mfix (List.rev nlst ++ vn) nlst ;;
          match nth_error nlst idx with
          | Some i' =>
            ret (Efun fdefs (Eapp k kon_tag (i'::nil)))
          | None => failwith "Unknown function index"
          end

        | EAst.tProj p c =>
          let c_tag := dcon_to_tag default_tag (dcon_of_con p.(proj_ind) 0) tgm in
          x1 <- get_named_str "x1" ;;
          k1 <- get_named_str "k1" ;;
          y <- get_named_str "y" ;;
          c' <- cps_cvt c vn k1 ;;
          ret (Efun
                 (Fcons k1 kon_tag (x1::nil)
                        (Eproj y c_tag (N.of_nat p.(proj_arg)) x1
                               (Eapp k kon_tag (y::nil))) Fnil)
                 c')

        | EAst.tPrim p =>
          match trans_prim_val p with
          | Some pv =>
            x <- get_named_str "prim" ;;
            ret (Eprim_val x pv (Eapp k kon_tag (x :: nil)))
          | None => failwith "Unsupported primitive type (arrays)"
          end

        (* These should not occur *)
        | EAst.tVar _ => failwith "Var"
        | EAst.tEvar _ _ => failwith "Evar"
        | EAst.tCoFix _ _ => failwith "CoFix"
        | EAst.tLazy _ => failwith "Lazy"
        | EAst.tForce _ => failwith "Force"
        end.

    End Convert.


    (** * Top-level CPS conversion *)

    Definition convert_cps_exp (dcm : conId_map) (prims : list (primitive * positive))
               (cmap : const_map) (e : EAst.term) : cpsM exp :=
      k <- get_named_str "k" ;;
      f <- get_named_str "f" ;;
      x <- get_named_str "x" ;;
      e' <- cps_cvt dcm prims cmap e nil k ;;
      ret (Efun
             (Fcons f kon_tag (k::nil) e'
                    (Fcons k kon_tag (x::nil) (Ehalt x) Fnil))
             (cps.Eapp f kon_tag (k::nil))).

    Definition convert_top_cps (ie : ienv) (prims : list (primitive * positive))
               (cmap : const_map) (e : EAst.term) : error cps.exp * comp_data :=
      let '(_, cenv, ctag, itag, dcm) := convert_env default_tag default_itag ie in
      let ftag := (func_tag + 1)%positive in
      let fenv : fun_env := M.set func_tag (2%N, (0%N::1%N::nil))
                                  (M.set kon_tag (1%N, (0%N::nil)) (M.empty _)) in
      let comp_d := pack_data next_id ctag itag ftag cenv fenv (M.empty _) (M.empty nat) [] in
      let '(res_err, (comp_d', _)) := run_compM (convert_cps_exp dcm prims cmap e) comp_d tt in
      (res_err, comp_d').

  End CPS.

End Translate.
