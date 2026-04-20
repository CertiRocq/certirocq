(* Conversion from LambdaBoxLocal.expression to LambdaANF.term using ANF or CPS tranformation *)

From Stdlib Require Import ZArith.ZArith Lists.List
        Sorting.Sorted Arith.Arith Sets.Ensembles.
Require Import ExtLib.Data.String.
From CertiRocq Require Import Common.AstCommon Common.compM Pipeline_utils.

Require Import LambdaBoxLocal.expression.
Require Import LambdaANF.term LambdaANF.cps_show LambdaANF.eval LambdaANF.ctx LambdaANF.List_util LambdaANF.Ensembles_util LambdaANF.state.
Require Import compcert.lib.Coqlib compcert.lib.Maps.

Require Import ExtLib.Data.Monads.OptionMonad ExtLib.Structures.Monads.
Require Import MetaRocq.Utils.bytestring.

Import ListNotations.
Import Monad.MonadNotation.
Open Scope monad_scope.

Section Translate.

  Context (prim_map : M.t primitive).
  Context (func_tag kon_tag default_tag default_itag : positive)
          (next_id : positive).


  Section COMMON.

    Definition conId_map:= list (dcon * ctor_tag).

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


    Definition t_info:Type := fun_tag.
    Definition t_map := M.t t_info.
    Definition t_empty:t_map := M.empty _.

    (* get the fun_tag of a variable, func_tag if not found *)
    Definition get_f (n:var) (sig:t_map): fun_tag :=
      match M.get n sig with
      | None => func_tag
      | Some v => v
      end.


    Definition s_map := M.t var.
    Definition s_empty := M.empty var.


    Definition constr_env:Type := conId_map.

    Definition dcon_to_tag (a:dcon) (sig:conId_map) :=
      dcon_to_info a sig.

    Definition name_env := M.t BasicAst.name.
    Definition n_empty : name_env := M.empty _.


    Definition ienv := list (Kernames.kername * AstCommon.itypPack).


    (* returns list of numbers [n, n+m[  and the positive n+m (next available pos) *)
    Fixpoint fromN (n:positive) (m:nat) : list positive * positive :=
      match m with
      | O => (nil, n)
      | S m' =>
        let (l, nm ) := (fromN (n+1) (m')) in
        (n::l, nm)
      end.

    (* Bind m projections. The first variable in the list binds the last constructor argument. *)
    Fixpoint ctx_bind_proj (tg:ctor_tag) (r:positive) (vars : list var) (args:nat) (* initially the length of args list *)
      : exp_ctx :=
      match vars with
      | [] => Hole_c
      | v :: vars =>
        let ctx_p':= ctx_bind_proj tg r vars (args - 1) in
        (Eproj_c v tg (N.of_nat (args - 1)) r ctx_p')
      end.


    (** process a list of constructors from inductive type ind with ind_tag niT.
    - update the ctor_env with a mapping from the current ctor_tag to the cTypInfo
    - update the conId_map with a pair relating the nCon'th constructor of
      ind to the ctor_tag of the current constructor *)
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
                       (((ind,nCon), cn)::dcm (** Remove this now that params are always 0? *))
      | (_, _) => (ce, dcm)
      end.


    (** For each inductive type defined in the mutually recursive bundle,
    - use tag niT for this inductive datatype
    - reserve constructor tags for each constructors of the type
    - process each of the constructor, indicating they are the ith constructor
      of the nth type of idBundle
    np: number of type parameters for this bundle
     *)
    Fixpoint convert_typack typ (idBundle:Kernames.kername) (n:nat)
             (ice : (ind_env * ctor_env*  ctor_tag * ind_tag * conId_map))
      : (ind_env * ctor_env * ctor_tag * ind_tag * conId_map) :=
      let '(ie, ce, ncT, niT, dcm) := ice in
      match typ with
      | nil => ice
      (* let cct := (ncT::nil) in
      let ncT' := Pos.succ ncT in
      let itN := "Unit"%bs in
      let itC := ((mkCnstr "prf"%bs 0%nat) :: nil) in
      let (ce', dcm') :=
          convert_cnstrs itN cct itC (BasicAst.mkInd idBundle n) 0 niT ce dcm
      in
      let ityi := ((ncT, N.of_nat 0%nat)::nil) in
      (M.set niT ityi ie, ce', ncT', (Pos.succ niT), dcm') *)
      | (AstCommon.mkItyp itN itC ) ::typ' =>
        let (cct, ncT') := fromN ncT (List.length itC) in
        let (ce', dcm') :=
            convert_cnstrs itN cct itC (Kernames.mkInd idBundle n) 0 0 0 niT ce dcm
        in
        let ityi :=
            combine cct (map (fun (c:AstCommon.Cnstr) =>
                                let (_, n) := c in N.of_nat n) itC)
        in
        convert_typack typ' idBundle (n+1)
                       (M.set niT ityi ie, ce', ncT', (Pos.succ niT) , dcm')
      end.


    Fixpoint convert_env' (g:ienv) (ice:ind_env * ctor_env * ctor_tag * ind_tag * conId_map)
      : (ind_env * ctor_env * ctor_tag * ind_tag * conId_map) :=
      let '(ie, ce, ncT, niT, dcm) := ice in
      match g with
      | nil => ice
      | (id, ty)::g' =>
        (* id is name of mutual pack ty is mutual pack *)
        (* constructors are indexed with : name (string) of the mutual pack
       with which projection of the ty, and indice of the constructor *)
        convert_env' g' (convert_typack ty id 0 (ie, ce, ncT, niT, dcm))
      end.

    (** As we process the LambdaBoxLocal inductive environment (ienv), we build:
    - an L6 inductive environment (ind_env) mapping tags (ind_tag) to constructors

      and their arities
      - an L6 constructor environment (ctor_env) mapping tags (ctor_tag) to
      information about the constructors
      - a map (conId_map) from LambdaBoxLocal tags (conId) to L6 constructor tags (ctor_tag)
      convert_env' is called with the next available constructor tag and the
      next available inductive datatype tag, and inductive and constructor
      environment containing only the default "box" constructor/type
     *)
    Definition convert_env (g:ienv): (ind_env * ctor_env*  ctor_tag * ind_tag * conId_map) :=
      let default_ind_env := M.set default_itag (cons (default_tag, 0%N) nil) (M.empty ind_ty_info) in
      let info := {| ctor_name := BasicAst.nAnon
                     ; ctor_ind_name := BasicAst.nAnon
                     ; ctor_ind_tag := default_itag
                     ; ctor_arity := 0%N
                     ; ctor_ordinal := 0%N
                  |} in
      let default_ctor_env := M.set default_tag info (M.empty ctor_ty_info) in
      convert_env' g (default_ind_env, default_ctor_env, (Pos.succ default_tag:ctor_tag), (Pos.succ default_itag:ind_tag), nil).

  End COMMON.


  (* Zoe: For erasing boxes translating proof. TODO *)
  Definition consume_fun (f x : var) : exp_ctx :=
    Efun1_c (Fcons f func_tag [x] (Ehalt f) Fnil) Hole_c.



  Section CPS.

    Definition cpsM := @compM' unit.

    (* TODO move *)
    Definition get_named_str_lst (s : list string) : cpsM (list var) :=
      mapM get_named_str s.

    Fixpoint convert_prim (n : nat) (* arity *)
             (prim : positive) (args : list var) (kont : var) : cpsM term.exp :=
      match n with
      | 0%nat =>
        pr <- get_named_str "prim"%bs ;;
        ret (Eprim pr prim (List.rev args) (Eapp kont kon_tag [pr]))
      | S n =>
        arg <- get_named_str "p_arg"%bs ;;
        kont1 <- get_named_str "p_k"%bs ;;
        f <- get_named_str "prim_wrapper"%bs ;;
        trm <- convert_prim n prim (arg :: args) kont1 ;;
        ret (Efun (Fcons f func_tag [kont1; arg] trm Fnil) (Eapp kont kon_tag [f]))
      end.



    Fixpoint names_lst_len (ns : list name) (m : nat) : list name :=
      match ns, m with
      | _, 0%nat => []
      | [], S _ => repeat nAnon m
      | n :: ns, S m => n :: names_lst_len ns m
      end.

    Lemma names_lst_length ns m :
      List.length (names_lst_len ns m) = m.
    Proof.
      revert m; induction ns; intros m; destruct m; simpl; try reflexivity.
      - rewrite repeat_length. reflexivity.
      - rewrite IHns. reflexivity.
    Qed.


    (** ** Main CPS conversion program *)

    Fixpoint cps_cvt (e : expression.exp) (vn : list var) (k : var) (tgm : constr_env) : cpsM term.exp :=
      match e with
      | Var_e x =>
        match nth_error vn (N.to_nat x) with
        | Some v => ret (term.Eapp k kon_tag (v::nil))
        | None => failwith  "Unknown DeBruijn index"
        end
      | App_e e1 e2 =>
        x1 <- get_named_str "x1"%bs ;;
        k1 <- get_named_str "k1"%bs ;;
        x2 <- get_named_str "x2"%bs ;;
        k2 <- get_named_str "k2"%bs ;;
        e1' <- cps_cvt e1 vn k1 tgm;;
        e2' <- cps_cvt e2 vn k2 tgm;;
        ret (Efun
               (Fcons k1 kon_tag (x1::nil)
                      (term.Efun
                         (Fcons k2 kon_tag (x2::nil)
                                (term.Eapp x1 func_tag (k::x2::nil)) Fnil)
                         e2') Fnil)
               e1')
      | Lam_e n e1 =>
        x1 <- get_named_str "x1"%bs ;;
        f <- get_named n ;;
        k1 <- get_named_str "k1"%bs ;;
        e1' <- cps_cvt e1 (x1::vn) k1 tgm ;;
        ret (Efun
               (Fcons f func_tag (k1::x1::nil) e1' Fnil)
               (term.Eapp k kon_tag (f::nil)))

      | Let_e n e1 e2 =>
        x <- get_named_str (string_of_name n);;
        k1 <- get_named_str "k"%bs ;;
        e2' <- cps_cvt e2 (x::vn) k tgm ;;
        e1' <- cps_cvt e1 vn k1 tgm ;;
        ret (Efun
               (Fcons k1 kon_tag (x::nil) e2' Fnil)
               e1')

      | Con_e dci es =>
        let c_tag := dcon_to_tag dci tgm in
        x' <- get_named_str "x'"%bs ;;
        xs <- get_named_str_lst (map (fun _ => "x") (exps_as_list es)) ;;
        ks <- get_named_str_lst (map (fun _ => "k") (exps_as_list es)) ;;
        cps_cvt_exps es vn (Econstr x' c_tag xs (Eapp k kon_tag (x'::nil))) xs ks tgm

      | Fix_e fnlst i =>
        let names_lst :=  fnames fnlst in
        nlst <- get_named_lst names_lst ;;
        fdefs <- cps_cvt_efnlst fnlst (List.rev nlst ++ vn) nlst tgm;;
        match nth_error nlst (N.to_nat i) with
        | Some i' =>
          ret (Efun fdefs (Eapp k kon_tag (i'::nil)))
        | None => failwith "Unknown function index"
        end

      | Match_e e1 n bl =>
        x1 <- get_named_str "x1"%bs ;;
        k1 <- get_named_str "k1"%bs ;;
        e1' <- cps_cvt e1 vn k1 tgm;;
        cbl <- cps_cvt_branches bl vn k x1 tgm;;
        ret (Efun (Fcons k1 kon_tag (x1::nil) (Ecase x1 cbl) Fnil) e1')

      | Prf_e =>
        x <- get_named_str "x"%bs ;;
        ret (Econstr x default_tag nil (Eapp k kon_tag (x::nil)))

      (* f <- get_named_str "f"%bs ;; *)
      (* x <- get_named_str "x"%bs ;; *)
      (* let c := consume_fun f x in *)
      (* ret (c |[ term.Eapp k kon_tag (f::nil) ]|) *)

      | Prim_val_e p =>
        x <- get_named_str "prim"%bs ;;
        ret (Eprim_val x p (Eapp k kon_tag (x :: nil)))

      | Prim_e p =>
        match M.get p prim_map with
        | Some prim => convert_prim prim.(prim_arity) p [] k
        | None => failwith "Internal error: identifier for primitive not found"
        end
      end

    with cps_cvt_exps (es : expression.exps) (vn : list var) (e_app : exp) (xs ks : list var) (tgm : constr_env)
         : cpsM term.exp :=
           match es with
           | enil => ret e_app
           | econs e es' =>
             match xs, ks with
             | [], _ | _, [] => failwith "Internal error: wrong number of arguments in constructor continuation"
             | x1 :: xs, k1 :: ks =>
               e' <- cps_cvt e vn k1 tgm;;
               e_exp <- cps_cvt_exps es' vn e_app xs ks tgm;;
               ret (Efun (Fcons k1 kon_tag (x1::nil) e_exp Fnil) e')
             end
           end
    (* nlst must be of the same length as fdefs *)
    with cps_cvt_efnlst (fdefs : expression.efnlst) (vn : list var)
                        (nlst : list var) (tgm : constr_env)
         : cpsM fundefs :=
           match fdefs with
           | eflnil => ret Fnil
           | eflcons n1 e1 fdefs' =>
             x <- get_named_str "x"%bs ;;
             k' <- get_named_str "k"%bs ;;
             let curr_var := List.hd 1%positive nlst in
             match e1 with
             | Lam_e n2 e2 =>
               ce <- cps_cvt e2 (x::vn) k' tgm;;
               cfdefs <- cps_cvt_efnlst fdefs' vn (List.tl nlst) tgm;;
               ret (Fcons curr_var func_tag (k'::x::nil) ce cfdefs)
             | _ => failwith "body of fix must be a lambda expr"
             end
           end

    with cps_cvt_branches (bl : expression.branches_e) (vn : list var) (k : var)
                          (r : var) (tgm : constr_env)
         : cpsM (list (ctor_tag * exp)) :=
           match bl with
           | brnil_e => ret nil
           | brcons_e dc (i, lnames) e bl' =>
             (* Zoe: Did some refactoring to remove list rev and make the proof easier. Double check it's still OK.
              Now the first variable in vars binds the last constructor argument.
              *)
             let tg := dcon_to_tag dc tgm in
             cbl <- cps_cvt_branches bl' vn k r tgm;;
             vars <- get_named_lst (names_lst_len lnames (N.to_nat i)) ;;
             let ctx_p := ctx_bind_proj tg r vars (List.length vars) in
             ce <- cps_cvt e (vars ++ vn) k tgm ;;
             ret ((tg, app_ctx_f ctx_p ce)::cbl)
           end.


    Definition convert_whole_exp (e : expression.exp ) (dcm : conId_map) : cpsM exp :=
      k <- get_named_str "k"%bs ;;
      f <- get_named_str "f"%bs ;;
      x <- get_named_str "x"%bs ;;
      e' <- cps_cvt e nil k dcm ;;
      ret (Efun
             (Fcons f kon_tag (k::nil) e'
                    (Fcons k kon_tag (x::nil) (Ehalt x) Fnil))
             (term.Eapp f kon_tag (k::nil))).


    Definition convert_top (ee:ienv * expression.exp) : error term.exp * comp_data :=
      let '(_, cenv, ctag, itag, dcm) := convert_env (fst ee) in

      let ftag := (func_tag + 1)%positive in
      let fenv : fun_env := M.set func_tag (2%N, (0%N::1%N::nil))
                                  (M.set kon_tag (1%N, (0%N::nil)) (M.empty _) ) in

      let comp_d := pack_data next_id ctag itag ftag cenv fenv (M.empty _) (M.empty nat) [] in
      let '(res_err, (comp_d', _)) := run_compM (convert_whole_exp (snd ee) dcm) comp_d tt in
      (res_err, comp_d').



    (** ** Declarative definition of CPS conversion used in proofs **)


  Inductive cps_cvt_rel : Ensemble var -> (* Input fresh identifiers *)
                          expression.exp -> (* Input LambdaBoxLocal exp *)
                          list var -> (* deBruijn index map *)
                          var -> (* Continuation variable *)
                          constr_env ->
                          Ensemble var -> (* Output fresh identifiers *)
                          term.exp -> (* CPS converted exp *)
                          Prop :=
  | e_Var :
      forall S v vn x k tgm,
        nth_error vn (N.to_nat x) = Some v ->
        cps_cvt_rel S (Var_e x) vn k tgm S (term.Eapp k kon_tag (v::nil))
  | e_Lam :
      forall S S' na e1 e1' x1 vn k k1 f tgm,
        x1 \in S ->
        f \in (S \\ [set x1]) ->
        k1 \in (S \\ (f |: [set x1])) ->
        cps_cvt_rel (S \\ [set x1] \\ [set f] \\ [set k1]) e1 (x1::vn) k1 tgm S' e1' ->
        cps_cvt_rel S
                    (Lam_e na e1)
                    vn
                    k
                    tgm
                    S'
                    (term.Efun (Fcons f func_tag (k1::x1::nil) e1' Fnil)
                              (term.Eapp k kon_tag (f::nil)))
  | e_App :
      forall S1 S2 S3 e1 e1' e2 e2' k k1 k2 x1 x2 vn tgm,
        x1 \in S1 ->
        k1 \in (S1 \\ [set x1]) ->
        x2 \in (S1 \\ [set x1] \\ [set k1]) ->
        k2 \in (S1 \\ [set x1] \\ [set k1] \\ [set x2]) ->
        cps_cvt_rel (S1 \\ [set x1] \\ [set k1] \\ [set x2] \\ [set k2]) e1 vn k1 tgm S2 e1' ->
        cps_cvt_rel S2 e2 vn k2 tgm S3 e2' ->
        cps_cvt_rel S1
                    (App_e e1 e2)
                    vn
                    k
                    tgm
                    S3
                    (term.Efun (Fcons k1 kon_tag (x1::nil)
                                     (term.Efun (Fcons k2 kon_tag (x2::nil)
                                                      (term.Eapp x1 func_tag
                                                                (k::x2::nil))
                                                      Fnil)
                                               e2') Fnil)
                              e1')
  | e_Con :
      forall S1 S2 c_tag dci tgm es e' k x1 vn xs ks,
        c_tag = dcon_to_tag dci tgm ->

        x1 \in S1 ->
        FromList xs \subset (S1 \\ [set x1]) ->
        FromList ks \subset (S1 \\ [set x1] \\ FromList xs) ->

        NoDup xs ->
        NoDup ks ->
        cps_cvt_rel_exps (S1 \\ [set x1] \\ FromList xs \\ FromList ks)
                         es vn (Econstr x1 c_tag xs (Eapp k kon_tag [x1])) xs ks tgm S2 e' ->
        cps_cvt_rel S1
                    (Con_e dci es)
                    vn
                    k
                    tgm
                    S2
                    e'
  | e_Let :
      forall S1 S2 S3 na e1 e1' e2 e2' x1 vn k k1 tgm,
        x1 \in S1 ->
        k1 \in (S1 \\ [set x1]) ->
        cps_cvt_rel (S1 \\ [set x1] \\ [set k1]) e2 (x1::vn) k tgm S2 e2' ->
        cps_cvt_rel S2 e1 vn k1 tgm S3 e1' ->
        cps_cvt_rel S1
                    (Let_e na e1 e2)
                    vn
                    k
                    tgm
                    S3
                    (term.Efun (Fcons k1 kon_tag (x1::nil) e2' Fnil) e1')
  | e_Match :
      forall S1 S2 S3 e1 e1' bs bs' vn k x1 k1 n tgm,
        x1 \in S1 ->
        k1 \in (S1 \\ [set x1]) ->
        cps_cvt_rel (S1 \\ [set x1] \\ [set k1]) e1 vn k1 tgm S2 e1' ->
        cps_cvt_rel_branches S2 bs vn k x1 tgm S3 bs' ->
        cps_cvt_rel S1
                    (Match_e e1 n bs)
                    vn
                    k
                    tgm
                    S3
                    (Efun (Fcons k1 kon_tag [x1] (Ecase x1 bs') Fnil) e1')
  | e_Fix :
      forall S1 S2 i f fnlst fnames vn k fdefs tgm,
        FromList fnames \subset S1 ->
        NoDup fnames ->
        List.length fnames = efnlength fnlst ->
        cps_cvt_rel_efnlst (S1 \\ (FromList fnames)) fnlst (List.rev fnames ++ vn) fnames tgm S2 fdefs ->
        nth_error fnames (N.to_nat i) = Some f ->
        cps_cvt_rel S1
                    (Fix_e fnlst i)
                    vn
                    k
                    tgm
                    S2
                    (term.Efun fdefs (term.Eapp k kon_tag (f::nil)))
  | e_Prf :
      forall S vn k tgm x,
        x \in S ->
        cps_cvt_rel S Prf_e vn k tgm (S \\ [set x]) (Econstr x default_tag nil (Eapp k kon_tag (x::nil)))

  | e_Prim_val :
    forall S vn k p tgm x,
          x \in S ->
          cps_cvt_rel S (Prim_val_e p) vn k tgm (S \\ [set x]) (Eprim_val x p (Eapp k kon_tag (x::nil)))

  with cps_cvt_rel_exps :
         Ensemble var -> expression.exps -> list var -> exp -> list var -> list var ->
         constr_env -> Ensemble var -> exp -> Prop :=
  | e_Enil :
      forall S vn e_app  tgm,
        cps_cvt_rel_exps S enil vn e_app [] [] tgm S e_app
  | e_Econs :
      forall S1 S2 S3 vn e_app x1 xs k1 ks e es e' es' tgm,
        cps_cvt_rel S1 e vn k1 tgm S2 e' ->
        cps_cvt_rel_exps S2 es vn e_app xs ks tgm S3 es' ->
        cps_cvt_rel_exps S1
                         (econs e es)
                         vn
                         e_app
                         (x1 :: xs)
                         (k1 :: ks)
                         tgm
                         S3
                         (Efun (Fcons k1 kon_tag [x1] es' Fnil) e')

  with cps_cvt_rel_efnlst :
         Ensemble var ->
         expression.efnlst ->
         list var ->
         list var ->
         constr_env ->
         Ensemble var ->
         fundefs ->
         Prop :=
  | e_Eflnil :
      forall S vn tgm,
        cps_cvt_rel_efnlst S eflnil vn [] tgm S Fnil
  | e_Eflcons :
      forall S1 S2 S3 vn fnames e1 e1' fnlst fdefs n n1 na x1 k1 tgm,
        x1 \in S1 ->
        k1 \in (S1 \\ [set x1]) ->
        cps_cvt_rel (S1 \\ [set x1] \\ [set k1]) e1 (x1::vn) k1 tgm S2 e1' ->
        cps_cvt_rel_efnlst S2 fnlst vn fnames tgm S3 fdefs ->
        cps_cvt_rel_efnlst
          S1 (eflcons n1 (Lam_e na e1) fnlst)
          vn (n :: fnames) tgm S3
          (Fcons n func_tag (k1::x1::nil) e1' fdefs)
  with cps_cvt_rel_branches :
         Ensemble var ->
         expression.branches_e ->
         list var ->
         var (* continuation variable *) ->
         var (* binding for scrutinee *) ->
         constr_env ->
         Ensemble var ->
         list (ctor_tag * exp) ->
         Prop :=
  | e_Brnil :
      forall S vn k r tgm,
        cps_cvt_rel_branches S brnil_e vn k r tgm S []
  | e_Brcons:
      forall S1 S2 S3 vn k r e ce bs' cbs' vars lnames n ctx_p tg dc tgm,
        tg = dcon_to_tag dc tgm ->
        FromList vars \subset S2 ->

        NoDup vars ->
        Datatypes.length vars = N.to_nat n ->


        ctx_bind_proj tg r vars (N.to_nat n) = ctx_p ->

        cps_cvt_rel_branches S1 bs' vn k r tgm S2 cbs' ->

        cps_cvt_rel (S2 \\ (FromList vars)) e (vars ++ vn) k tgm S3 ce ->

        cps_cvt_rel_branches
          S1 (brcons_e dc (n, lnames) e bs') vn k r tgm S3 ((tg, app_ctx_f ctx_p ce)::cbs').


  End CPS.


  Section ANF.

    Definition anfM := @compM' unit.


  (* Converting a DeBruijn index to named variable *)
  (** The actual map grows from 1 onward. We keep the pointer p to the last entry of the map.
      When we have to lookup DeBruijn index i in the map, we lookup (p - i). *)

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
    | Fun (ft : term.fun_tag) (x : var) (e : term.exp)
    | Prim_val (p : primitive)
    | Prim (pr : positive) (xs : list var).

    Definition anf_term : Type := anf_value * exp_ctx.

    Definition def_name := nNamed "y".


    Section Convert.

      Context (tgm : conId_map).

      (* Bind projections for a match branch.
         Follows the CPS pattern: allocate vars, build ctx_bind_proj, update var_map.
         The first variable in vars binds the last constructor argument. *)
      Definition proj_ctx (names : list name) (n : nat)
               (scrut : var) (vm : var_map) ct : anfM (exp_ctx * var_map) :=
        vars <- get_named_lst (names_lst_len names n) ;;
        let ctx_p := ctx_bind_proj ct scrut vars (List.length vars) in
        let vm' := List.fold_right (fun v vm' => add_var_name vm' v) vm vars in
        ret (ctx_p, vm').

      Fixpoint add_fix_names (B : efnlst) (vm : var_map) : anfM (list var * var_map):=
        match B with
        | eflnil => ret ([], vm)
        | eflcons n _ B' =>
          f_name <- get_named n ;;
          lvm <- add_fix_names B' (add_var_name vm f_name) ;;
          let '(fs, vm') := lvm in
          ret (f_name :: fs, vm')
        end.

      Fixpoint convert_prim_anf (n : nat) (* arity *)
               (prim : positive) (args : list var) : anfM (var * exp_ctx) :=
        match n with
        | 0%nat =>
          x <- get_named_str "prim" ;;
          ret (x, Eprim_c x prim (List.rev args) Hole_c)
        | S n =>
          arg <- get_named_str "p_arg" ;;
          f <- get_named_str "prim_wrapper" ;;
          '(x, C) <- convert_prim_anf n prim (arg :: args) ;;
          ret (f, Efun1_c (Fcons f func_tag [arg] (C |[ Ehalt x ]|) Fnil) Hole_c)
        end.


      Fixpoint convert_anf (e : expression.exp) (vm : var_map) : anfM (var * exp_ctx) :=
        match e with
        | Var_e x =>
          match get_var_name vm x with
          | Some v => ret (v, Hole_c)
          | None => failwith "Unknown DeBruijn index"
          end
        | App_e e1 e2 =>
          '(x1, C1) <- convert_anf e1 vm ;;
          '(x2, C2) <- convert_anf e2 vm ;;
          r <- get_named def_name ;;
          ret (r, comp_ctx_f C1 (comp_ctx_f C2 (Eletapp_c r x1 func_tag [x2] Hole_c)))
        | Lam_e n e1 =>
          x <- get_named n ;; (* get the name of the argument *)
          f <- get_named def_name ;;
          '(r, C) <- convert_anf e1 (add_var_name vm x) ;;
          ret (f, Efun1_c (Fcons f func_tag [x] (C |[ Ehalt r ]|) Fnil) Hole_c)
        | Let_e n e1 e2 =>
          '(x, C1) <- convert_anf e1 vm ;;
          '(r, C2) <- convert_anf e2 (add_var_name vm x) ;;
          ret (r, comp_ctx_f C1 C2)
        | Con_e dci es =>
          let c_tag := dcon_to_tag dci tgm in
          x <- get_named def_name ;;
          '(ys, C) <- convert_anf_exps es vm ;;
          ret (x, comp_ctx_f C (Econstr_c x c_tag ys Hole_c))
        | Fix_e fnlst i =>
          lvm <- add_fix_names fnlst vm ;;
          let (names, vm') := lvm in
          '(x, defs) <- convert_anf_efnlst fnlst names i vm' ;;
          ret (x, Efun1_c defs Hole_c)
        | Match_e e1 n bl =>
          f <- get_named_str "f_case" ;; (* Case-analysis function *)
          y <- get_named_str "s" ;; (* Scrutinee argument *)
          '(x1, C1) <- convert_anf e1 vm ;;
          pats <- convert_anf_branches bl y vm ;;
          r <- get_named def_name ;;
          ret (r, Efun1_c (Fcons f func_tag [y] (Ecase y pats) Fnil)
                          (comp_ctx_f C1 (Eletapp_c r f func_tag [x1] Hole_c)))
        | Prf_e =>
          x <- get_named_str "y" ;;
          ret (x, Econstr_c x default_tag [] Hole_c)
        | Prim_val_e p =>
          x <- get_named_str "y" ;;
          ret (x, Eprim_val_c x p Hole_c)
        | Prim_e p =>
          match M.get p prim_map with
          | Some prim => convert_prim_anf prim.(prim_arity) p []
          | None => failwith "Internal error: identifier for primitive not found"
          end
        end
      with convert_anf_exps (es : expression.exps) (vm : var_map) : anfM (list var * exp_ctx) :=
             match es with
             | enil => ret ((@nil var), Hole_c)
             | econs e es' =>
               '(y, C1) <- convert_anf e vm ;;
               '(ys, C2) <- convert_anf_exps es' vm ;;
               ret (y :: ys, comp_ctx_f C1 C2)
             end
      with convert_anf_efnlst (fdefs : expression.efnlst) (names : list var) (i : N) (vm : var_map) : anfM (var * fundefs) :=
             match fdefs, names with
             | eflnil, nil => ret (1%positive (* dummy var *), Fnil)
             | eflcons n e fdefs', f_name :: names =>
               match e with
               | Lam_e na e1 =>
                 x <- get_named na ;;
                 '(r, C) <- convert_anf e1 (add_var_name vm x) ;;
                 ds <- convert_anf_efnlst fdefs' names (i - 1)%N vm ;;
                 let (fi, defs') := ds in
                 let fi' := match i with
                            | 0%N => f_name
                            | Npos _ => fi
                            end in
                 ret (fi', Fcons f_name func_tag [x] (C |[ Ehalt r ]|) defs')
               | _ => failwith ("Unexpected body of fix in function " ++ print_name n)%bs
               end
             | _, _ => failwith "Wrong number of names for mut. rec. functions"
             end
      with convert_anf_branches (bl : expression.branches_e) (scrut : var) (vm : var_map) : anfM (list (ctor_tag * exp)) :=
             match bl with
             | brnil_e => ret nil
             | brcons_e dc (i, lnames) e bl' =>
               let ctag := dcon_to_tag dc tgm in
               pats' <- convert_anf_branches bl' scrut vm ;;
               cm <- proj_ctx lnames (N.to_nat i) scrut vm ctag ;;
               let (Cproj, vm') := cm in
               '(r, C) <- convert_anf e vm' ;;
               ret ((ctag, app_ctx_f Cproj (C |[ Ehalt r ]|)) :: pats')
             end.

    End Convert.


    Definition convert_anf_exp dcm e : anfM term.exp :=
      '(x, C) <- convert_anf dcm e new_var_map ;;
      ret (C |[ Ehalt x ]|).

    (** * Top-level convert function *)

    Definition convert_top_anf (ee: ienv * expression.exp) : error term.exp * comp_data :=
      let '(_, cenv, ctag, itag, dcm) := convert_env (fst ee) in
      let ftag := (func_tag + 1)%positive in
      let fenv : fun_env := M.set func_tag (1%N, (0%N::nil)) (M.empty _) in
      let comp_d := pack_data next_id ctag itag ftag cenv fenv (M.empty _) (M.empty nat) [] in
      let '(res_err, (comp_d', _)) := run_compM (convert_anf_exp dcm (snd ee)) comp_d tt in
      (res_err, comp_d').


    (** ** Declarative definition of ANF conversion used in proofs **)

    Inductive anf_cvt_rel : Ensemble var -> (* Input fresh identifiers *)
                            expression.exp -> (* Input LambdaBoxLocal exp *)
                            list var -> (* deBruijn index map *)
                            constr_env ->
                            Ensemble var -> (* Output fresh identifiers *)
                            exp_ctx -> (* ANF binding context *)
                            var -> (* Result variable *)
                            Prop :=
    | anf_Var :
        forall S v vn x tgm,
          nth_error vn (N.to_nat x) = Some v ->
          anf_cvt_rel S (Var_e x) vn tgm S Hole_c v
    | anf_Lam :
        forall S S' na e1 C1 r1 x1 f vn tgm,
          x1 \in S ->
          f \in (S \\ [set x1]) ->
          anf_cvt_rel (S \\ [set x1] \\ [set f]) e1 (x1::vn) tgm S' C1 r1 ->
          anf_cvt_rel S
                      (Lam_e na e1)
                      vn
                      tgm
                      S'
                      (Efun1_c (Fcons f func_tag [x1] (C1 |[ Ehalt r1 ]|) Fnil) Hole_c)
                      f
    | anf_App :
        forall S1 S2 S3 e1 C1 x1 e2 C2 x2 r vn tgm,
          anf_cvt_rel S1 e1 vn tgm S2 C1 x1 ->
          anf_cvt_rel S2 e2 vn tgm S3 C2 x2 ->
          r \in S3 ->
          anf_cvt_rel S1
                      (App_e e1 e2)
                      vn
                      tgm
                      (S3 \\ [set r])
                      (comp_ctx_f C1 (comp_ctx_f C2 (Eletapp_c r x1 func_tag [x2] Hole_c)))
                      r
    | anf_Con :
        forall S1 S2 c_tag dci tgm es C xs x vn,
          c_tag = dcon_to_tag dci tgm ->
          x \in S1 ->
          anf_cvt_rel_exps (S1 \\ [set x]) es vn tgm S2 C xs ->
          anf_cvt_rel S1
                      (Con_e dci es)
                      vn
                      tgm
                      S2
                      (comp_ctx_f C (Econstr_c x c_tag xs Hole_c))
                      x
    | anf_Let :
        forall S1 S2 S3 na e1 C1 x1 e2 C2 x2 vn tgm,
          anf_cvt_rel S1 e1 vn tgm S2 C1 x1 ->
          anf_cvt_rel S2 e2 (x1::vn) tgm S3 C2 x2 ->
          anf_cvt_rel S1
                      (Let_e na e1 e2)
                      vn
                      tgm
                      S3
                      (comp_ctx_f C1 C2)
                      x2
    | anf_Match :
        forall S1 S2 S3 e1 C1 x1 bs pats f y r vn n tgm,
          f \in S1 ->
          y \in (S1 \\ [set f]) ->
          anf_cvt_rel (S1 \\ [set f] \\ [set y]) e1 vn tgm S2 C1 x1 ->
          anf_cvt_rel_branches S2 bs vn y tgm S3 pats ->
          r \in S3 ->
          anf_cvt_rel S1
                      (Match_e e1 n bs)
                      vn
                      tgm
                      (S3 \\ [set r])
                      (Efun1_c (Fcons f func_tag [y] (Ecase y pats) Fnil)
                               (comp_ctx_f C1 (Eletapp_c r f func_tag [x1] Hole_c)))
                      r
    | anf_Fix :
        forall S1 S2 i f fnlst fnames vn fdefs tgm,
          FromList fnames \subset S1 ->
          NoDup fnames ->
          List.length fnames = efnlength fnlst ->
          anf_cvt_rel_efnlst (S1 \\ (FromList fnames)) fnlst (List.rev fnames ++ vn) fnames tgm S2 fdefs ->
          nth_error fnames (N.to_nat i) = Some f ->
          anf_cvt_rel S1
                      (Fix_e fnlst i)
                      vn
                      tgm
                      S2
                      (Efun1_c fdefs Hole_c)
                      f
    | anf_Prf :
        forall S vn tgm x,
          x \in S ->
          anf_cvt_rel S Prf_e vn tgm (S \\ [set x]) (Econstr_c x default_tag nil Hole_c) x
    | anf_Prim_val :
        forall S vn tgm p x,
          x \in S ->
          anf_cvt_rel S (Prim_val_e p) vn tgm (S \\ [set x]) (Eprim_val_c x p Hole_c) x

    with anf_cvt_rel_exps :
           Ensemble var -> expression.exps -> list var ->
           constr_env -> Ensemble var -> exp_ctx -> list var -> Prop :=
    | anf_Enil :
        forall S vn tgm,
          anf_cvt_rel_exps S enil vn tgm S Hole_c []
    | anf_Econs :
        forall S1 S2 S3 vn e es C1 x1 C2 xs tgm,
          anf_cvt_rel S1 e vn tgm S2 C1 x1 ->
          anf_cvt_rel_exps S2 es vn tgm S3 C2 xs ->
          anf_cvt_rel_exps S1
                           (econs e es)
                           vn
                           tgm
                           S3
                           (comp_ctx_f C1 C2)
                           (x1 :: xs)

    with anf_cvt_rel_efnlst :
           Ensemble var ->
           expression.efnlst ->
           list var ->
           list var ->
           constr_env ->
           Ensemble var ->
           fundefs ->
           Prop :=
    | anf_Eflnil :
        forall S vn tgm,
          anf_cvt_rel_efnlst S eflnil vn [] tgm S Fnil
    | anf_Eflcons :
        forall S1 S2 S3 vn fnames e1 C1 r1 fnlst fdefs n na x1 f_name tgm,
          x1 \in S1 ->
          anf_cvt_rel (S1 \\ [set x1]) e1 (x1::vn) tgm S2 C1 r1 ->
          anf_cvt_rel_efnlst S2 fnlst vn fnames tgm S3 fdefs ->
          anf_cvt_rel_efnlst
            S1 (eflcons n (Lam_e na e1) fnlst)
            vn (f_name :: fnames) tgm S3
            (Fcons f_name func_tag [x1] (C1 |[ Ehalt r1 ]|) fdefs)

    with anf_cvt_rel_branches :
           Ensemble var ->
           expression.branches_e ->
           list var ->
           var (* scrutinee variable *) ->
           constr_env ->
           Ensemble var ->
           list (ctor_tag * exp) ->
           Prop :=
    | anf_Brnil :
        forall S vn r tgm,
          anf_cvt_rel_branches S brnil_e vn r tgm S []
    | anf_Brcons :
        forall S1 S2 S3 vn r e C1 r1 bs' cbs' vars lnames n ctx_p tg dc tgm,
          tg = dcon_to_tag dc tgm ->

          anf_cvt_rel_branches S1 bs' vn r tgm S2 cbs' ->

          FromList vars \subset S2 ->
          NoDup vars ->
          Datatypes.length vars = N.to_nat n ->
          ctx_bind_proj tg r vars (N.to_nat n) = ctx_p ->

          anf_cvt_rel (S2 \\ (FromList vars)) e (vars ++ vn) tgm S3 C1 r1 ->

          anf_cvt_rel_branches
            S1 (brcons_e dc (n, lnames) e bs')
            vn r tgm S3
            ((tg, app_ctx_f ctx_p (C1 |[ Ehalt r1 ]|))::cbs').

  End ANF.


End Translate.
