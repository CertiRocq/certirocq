(* Computational definition and declarative spec for closure conversion. Part of the CertiRocq project.
 * Author: Anonymized, 2016
 *)
Require Import Common.AstCommon Common.compM.

Require Import LambdaANF.term LambdaANF.term_util LambdaANF.set_util LambdaANF.identifiers LambdaANF.ctx
        LambdaANF.Ensembles_util LambdaANF.List_util LambdaANF.functions LambdaANF.cps_show LambdaANF.state.
From Stdlib Require Import ZArith.Znumtheory.
Require Import compcert.lib.Maps.
From Stdlib Require Import Lists.List MSets.MSets MSets.MSetRBT Numbers.BinNums
        NArith.BinNat PArith.BinPos Sets.Ensembles.
Require Import Common.AstCommon.
Require Import ExtLib.Structures.Monads ExtLib.Data.Monads.StateMonad.
From Stdlib Require Import Ensembles.
Require Import MetaRocq.Utils.bytestring.
Import ListNotations Nnat MonadNotation.


Open Scope ctx_scope.
Open Scope monad_scope.
Open Scope fun_scope.
Open Scope bs_scope.

(** * Closure conversion as a relation  *)

Section CC.
  Variable (clo_tag : ctor_tag). (* Tag for closure records *)

  Variable (clo_itag : ind_tag). (* Inductive tag for closure records *)

  Inductive project_var :
    Ensemble var -> (* Variables in the current scope *)
    Ensemble var -> (* Names of the functions in the current function block *)
    Ensemble var -> (* Names of global (i.e. already closed) functions *)
    ctor_tag -> (* tag of the current environment constructor *)
    (var -> var) -> (* The environment map *)
    var -> (* The current environment *)
    list var -> (* The environment *)
    Ensemble var -> (* The free set *)
    var -> (* Before projection *)
    var -> (* After projection *)
    exp_ctx -> (* Context that will perform the projection *)
    Ensemble var -> (* The new free set *)
    Prop :=
  | Var_in_Scope :
      forall Scope Funs GFuns c gmap Γ FVs S x,
        In _ Scope x ->
        project_var Scope Funs GFuns c gmap Γ FVs S x x Hole_c S
  | Var_in_Funs :
      forall Scope Funs GFuns c gmap Γ FVs S x y,
        ~ In _ Scope x ->
        In _ Funs x ->
        In _ S y ->
        project_var Scope Funs GFuns c gmap Γ FVs S x y
                    (Econstr_c y clo_tag [x; gmap x] Hole_c) (Setminus _ S (Singleton _ y))
  | Var_in_GFuns :
      forall Scope Funs GFuns c c' gmap Γ FVs S x y g_env,
        ~ In _ Scope x ->
        ~ In _ Funs x ->
        In _ GFuns x ->
        In _ S y ->
        In _ (S \\ [set y]) g_env ->
        project_var Scope Funs GFuns c gmap Γ FVs S x y
                    (Econstr_c g_env c' [] (Econstr_c y clo_tag [x; g_env] Hole_c)) (S \\ [set y] \\ [set g_env])
  | Var_in_FVs :
      forall Scope Funs GFuns c gmap Γ FVs S x y N,
        ~ In _ Scope x ->
        ~ In _ Funs x ->
        ~ In _ GFuns x ->
        nthN FVs N = Some x ->
        In _ S y ->
        project_var Scope Funs GFuns c gmap Γ FVs S x y
                    (Eproj_c y c N Γ Hole_c) (S \\ [set y]).

  Inductive project_vars :
    Ensemble var -> (* Variables in the current scope *)
    Ensemble var -> (* Names of the functions in the current function block *)
    Ensemble var -> (* Names of global functions *)
    ctor_tag -> (* tag of the current environment constructor *)
    (var -> var) -> (* The environment map *)
    var -> (* The environment argument *)
    list var -> (* The free variables *)
    Ensemble var -> (* The free set *)
    list var -> (* Before projection *)
    list var -> (* After projection *)
    exp_ctx -> (* Context that will perform the projection *)
    Ensemble var -> (* The new free set *)
    Prop :=
  | VarsNil :
      forall Scope Funs GFuns c gmap Γ FVs S,
        project_vars Scope Funs GFuns c gmap Γ FVs S [] [] Hole_c S
  | VarsCons :
      forall Scope Funs GFuns c gmap Γ FVs y y' ys ys' C1 C2 S1 S2 S3,
        project_var Scope Funs GFuns c gmap Γ FVs S1 y y' C1 S2 ->
        project_vars Scope Funs GFuns c gmap Γ FVs S2 ys ys' C2 S3 ->
        project_vars Scope Funs GFuns c gmap Γ FVs S1 (y :: ys) (y' :: ys') (comp_ctx_f C1 C2) S3.

  Definition extend_fundefs' (f : var -> var) (B : fundefs) (x : var) : var -> var :=
    fun y => if (@Dec _ (name_in_fundefs B) _) y then x else f y.


  Inductive add_global_funs : Ensemble var -> (* Previous GFuns *)
                              Ensemble var -> (* New Funs *)
                              Ensemble var -> (* FVs of Funs *)
                              Ensemble var -> (* New GFuns *)
                              Type :=
  | Closed :
      forall GFuns Funs FVs,
        FVs <--> Empty_set _ ->
        add_global_funs GFuns Funs FVs (Funs :|: GFuns)
  | Open :
      forall GFuns Funs FVs,
        ~ FVs <--> Empty_set _ -> (* maybe not needed, but it shouldn't hurt *)
        add_global_funs GFuns Funs FVs (GFuns \\ Funs).


  Inductive Closure_conversion :
    Ensemble var -> (* Variables in the current scope *)
    Ensemble var -> (* Names of the functions in the current function block *)
    Ensemble var -> (* Names of global functions *)
    ctor_tag -> (* tag of the current environment constructor *)
    (var -> var) -> (* environment map from function name to env name *)
    var -> (* The environment argument -- needed to project the FVs *)
    list var -> (* The free variables - need to be ordered *)
    exp -> (* Before cc *)
    exp -> (* After cc *)
    exp_ctx -> (* The context that the output expression should be put in *)
    Prop :=
  | CC_Econstr :
      forall Scope Funs GFuns c genv Γ FVs S' S x ys ys' C C' t e e',
        (* Variables for projected vars should not shadow the variables in
         scope, i.e. Scope U FV U { Γ } *)
        Disjoint _ S (Scope :|: (Funs \\ Scope) :|: GFuns :|: image genv (Funs \\ Scope) :|: (FromList FVs :|: [set Γ])) ->
        project_vars Scope Funs GFuns c genv Γ FVs S ys ys' C S' ->
        (* We do not care about ys'. Should never be accessed again so do not
         add them aτ the current scope *)
        Closure_conversion (x |: Scope) Funs GFuns c genv Γ FVs e e' C' ->
        Closure_conversion Scope Funs GFuns c genv Γ FVs (Econstr x t ys e)
                           (Econstr x t ys' (C' |[ e' ]|)) C
  | CC_Ecase :
      forall Scope Funs GFuns c genv Γ FVs x x' C S S' pats pats',
        Disjoint _ S (Scope :|: (Funs \\ Scope) :|: GFuns :|: image genv (Funs \\ Scope)  :|: (FromList FVs :|: [set Γ])) ->
        project_var Scope Funs GFuns c genv Γ FVs S x x' C S' ->
        Forall2 (fun (pat pat' : ctor_tag * exp) =>
                   (fst pat) = (fst pat') /\
                   exists C' e',
                     snd pat' = C' |[ e' ]| /\
                     Closure_conversion Scope Funs GFuns c genv Γ FVs (snd pat) e' C')
                pats pats' ->
        Closure_conversion Scope Funs GFuns c genv Γ FVs (Ecase x pats) (Ecase x' pats') C
  | CC_Eproj :
      forall Scope Funs GFuns c genv Γ FVs S S' x y y' C C' t N e e',
        Disjoint _ S (Scope :|: (Funs \\ Scope) :|: GFuns :|: image genv (Funs \\ Scope) :|: (FromList FVs :|: [set Γ])) ->
        project_var Scope Funs GFuns c genv Γ FVs S y y' C S' ->
        Closure_conversion (x |: Scope) Funs GFuns c genv Γ FVs e e' C' ->
        Closure_conversion Scope Funs GFuns c genv Γ FVs (Eproj x t N y e)
                           (Eproj x t N y' (C' |[ e' ]|)) C
  | CC_Efun :
      forall Scope Funs GFuns GFuns' c genv Γ c' Γ' FVs FVs' FVs'' B B' e e' C' Ce S1 S1' S2 S3,
        (* The environment contains all the variables that are free in B *)
        (occurs_free_fundefs B) \\ GFuns <--> (FromList FVs') ->
        (* needed for cost preservation *)
        NoDup FVs' ->
        (* Project the FVs to construct the environment *)
        Disjoint _ S1 (Scope :|: (Funs \\ Scope) :|: GFuns :|: image genv (Funs \\ Scope) :|: (FromList FVs :|: [set Γ]))  ->
        project_vars Scope Funs GFuns c genv Γ FVs S1 FVs' FVs'' C' S1' ->
        (* Γ' is the variable that will hold the record of the environment *)
        Disjoint _ S3 (bound_var (Efun B e) :|: (Scope :|: (Funs \\ Scope) :|: GFuns :|: image genv (Funs \\ Scope) :|: (FromList FVs :|: [set Γ]))) ->
        In _ S3 Γ' ->
        Disjoint _ S2 (bound_var (Efun B e) :|: (Γ' |: (Scope :|: (Funs \\ Scope) :|: GFuns :|: image genv (Funs \\ Scope)) :|: (FromList FVs :|: [set Γ]))) ->
        add_global_funs GFuns (name_in_fundefs B) (FromList FVs') GFuns' ->
        Closure_conversion_fundefs B GFuns' c' FVs' B B' ->
        (* Add B in Funs if its only fvs are names are in GFuns *)
        Closure_conversion (Scope \\ name_in_fundefs B) (name_in_fundefs B :|: Funs) GFuns' c (extend_fundefs' genv B Γ') Γ FVs e e' Ce  ->
        Closure_conversion Scope Funs GFuns c genv Γ FVs (Efun B e) (Efun B' (Ce |[ e' ]|)) (comp_ctx_f C' (Econstr_c Γ' c' FVs'' Hole_c))
  | CC_Eletapp :
      forall Scope Funs GFuns c genv Γ FVs x f f' f'' ft e env' ys ys' C C' e' S S',
        Disjoint _ S (Scope :|: (Funs \\ Scope) :|: GFuns :|: image genv (Funs \\ Scope) :|: (FromList FVs :|: [set Γ])) ->
        (* Project the function name and the actual parameter *)
        project_vars Scope Funs GFuns c genv Γ FVs S (f :: ys) (f' :: ys') C S' ->
        (* The name of the function pointer and the name of the environment
         should not shadow the variables in the current scope and the
         variables that where used in the projections *)
        In _ S' f'' -> In _ S' env' -> f'' <> env' ->
        Closure_conversion (x |: Scope) Funs GFuns c genv Γ FVs e e' C' ->
        Closure_conversion Scope Funs GFuns c genv Γ FVs (Eletapp x f ft ys e)
                           (Eproj f'' clo_tag 0%N f'
                                  (Eproj env' clo_tag 1%N f'
                                         (Eletapp x f'' ft (env' :: ys') (C' |[ e' ]|)))) C
  | CC_Eapp :
      forall Scope Funs GFuns c genv Γ FVs f f' f'' ft env' ys ys' C S S',
        Disjoint _ S (Scope :|: (Funs \\ Scope) :|: GFuns :|: image genv (Funs \\ Scope) :|: (FromList FVs :|: [set Γ])) ->
        (* Project the function name and the actual parameter *)
        project_vars Scope Funs GFuns c genv Γ FVs S (f :: ys) (f' :: ys') C S' ->
        (* The name of the function pointer and the name of the environment
         should not shadow the variables in the current scope and the
         variables that where used in the projections *)
        In _ S' f'' -> In _ S' env' -> f'' <> env' ->
        Closure_conversion Scope Funs GFuns c genv Γ FVs (Eapp f ft ys)
                           (Eproj f'' clo_tag 0%N f'
                                  (Eproj env' clo_tag 1%N f'
                                         (Eapp f'' ft (env' :: ys')))) C
  | CC_Eprim_val :
      forall Scope Funs GFuns c genv Γ FVs S x C p e e',
        Disjoint _ S (Scope :|: (Funs \\ Scope) :|: GFuns :|: image genv (Funs \\ Scope)  :|: (FromList FVs :|: [set Γ])) ->
        Closure_conversion (x |: Scope) Funs GFuns c genv Γ FVs e e' C ->
        Closure_conversion Scope Funs GFuns c genv Γ FVs (Eprim_val x p e) (Eprim_val x p (C |[ e' ]|)) Hole_c
  | CC_Eprim :
      forall Scope Funs GFuns c genv Γ FVs S S' x ys ys' C C' f e e',
        Disjoint _ S (Scope :|: (Funs \\ Scope) :|: GFuns :|: image genv (Funs \\ Scope)  :|: (FromList FVs :|: [set Γ])) ->
        project_vars Scope Funs GFuns c genv Γ FVs S ys ys' C S' ->
        Closure_conversion (x |: Scope) Funs GFuns c genv Γ FVs e e' C' ->
        Closure_conversion Scope Funs GFuns c genv Γ FVs (Eprim x f ys e) (Eprim x f ys' (C' |[ e' ]|)) C
  | CC_Ehalt :
      forall Scope Funs GFuns c genv Γ FVs x x' C S S',
        Disjoint _ S (Scope :|: (Funs \\ Scope) :|: GFuns :|: image genv (Funs \\ Scope) :|: (FromList FVs :|: [set Γ])) ->
        (* Project the function name and the actual parameter *)
        project_var Scope Funs GFuns c genv Γ FVs S x x' C S' ->
        Closure_conversion Scope Funs GFuns c genv Γ FVs (Ehalt x) (Ehalt x') C
  with Closure_conversion_fundefs :
         fundefs -> (* The function names in the current block *)
         Ensemble var -> (* The global function names *)
         ctor_tag -> (* tag of the current environment constructor *)
         list var -> (* The environment *)
         fundefs -> (* Before cc *)
         fundefs -> (* After cc *)
         Prop :=
       | CC_Fcons :
           forall Bg GFuns c Γ' FVs S f t ys e e' C defs defs',
             (* The environment binding should not shadow the current scope
         (i.e. the names of the mut. rec. functions and the other arguments) *)
             Disjoint _ S (name_in_fundefs Bg :|: GFuns :|: (FromList ys :|: bound_var e)) ->
             In _ S  Γ' ->
             Closure_conversion_fundefs Bg GFuns c FVs defs defs' ->
             Closure_conversion (FromList ys) (name_in_fundefs Bg) GFuns c (extend_fundefs' id Bg Γ') Γ' FVs e e' C ->
             Closure_conversion_fundefs Bg GFuns c FVs (Fcons f t ys e defs )
                                        (Fcons f t (Γ' :: ys) (C |[ e' ]|) defs')
       | CC_Fnil :
           forall Funs GFuns c FVs,
             Closure_conversion_fundefs Funs GFuns c FVs Fnil Fnil.



  (** * Computational defintion of closure conversion *)


  Inductive VarInfo : Type :=
  (* A free variable, i.e. a variable outside the scope of the current function.
   The argument is position of a free variable in the env record *)
  | FVar : N -> VarInfo
  (* A function defined in the current block of function definitions. The argument is the name of the environment variable *)
  | MRFun : var -> VarInfo
  (* A variable declared in the scope of the current function *)
  | BoundVar : VarInfo.


  (* Maps variables to [VarInfo] *)
  Definition VarInfoMap := M.t VarInfo.

  (* A global function name *)
  Inductive GFunInfo : Type := GFun : GFunInfo.

  Definition GFunMap := M.t GFunInfo.

  Definition ccstate := @compM' unit.

  Import MonadNotation.


  (** Commonly used suffixes *)
  Definition clo_env_suffix := "_env".
  Definition clo_suffix := "_clo".
  Definition code_suffix := "_code".
  Definition proj_suffix := "_proj".



  (** Looks up a variable in the map and handles it appropriately *)
  Definition get_var (x : var) (map : VarInfoMap) (gfuns : GFunMap) (c : ctor_tag) (Γ : var)
  : ccstate (var * (exp -> exp)) :=
    match Maps.PTree.get x map with
      | Some entry =>
        match entry with
          | FVar pos =>
            (* pick a fresh name, register its pretty name *)
            y <- get_name x proj_suffix ;;
            ret (y, fun e => Eproj y c pos Γ e)
          | MRFun env =>
              (* get the new name of the function and pack it together with its *)
              (* environment argument to construct the closure *)
              y <- get_name x clo_suffix ;;
              ret (y, fun e => Econstr y clo_tag [x; env] e)
      | BoundVar => ret (x, id)
        end
      | None =>
        (* check if its a "global" function (i.e. one with no fvs) *)
        match M.get x gfuns with
        | Some GFun =>
          (* if so, construct an empty env *)
          c_env <- make_record_ctor_tag 0 ;;
          y <- get_name x clo_suffix ;;
          g_env <- get_name x "bogus_env" ;;
          ret (y, fun e => Econstr g_env c_env [] (Econstr y clo_tag [x; g_env] e))
        | None => ret (x, id) (* should never reach here *)
        end
    end.

  Fixpoint get_vars (xs : list var) (map : VarInfoMap) (gfuns : GFunMap)
           (c : ctor_tag) (Γ : var) : ccstate (list var * (exp -> exp)) :=
    match xs with
      | [] => ret ([], id)
      | x :: xs =>
        t1 <- get_var x map gfuns c Γ ;;
        let '(y, f) := t1 in
        t2 <- get_vars xs map gfuns c Γ ;;
        let '(ys, f') := t2 in
        ret (y :: ys, fun e => f (f' e))
    end.

  (** Add some bound variables in the map *)
  Fixpoint add_params args  (mapfv : VarInfoMap) : VarInfoMap :=
    match args with
      | [] => mapfv
      | x :: xs =>
        M.set x BoundVar (add_params xs mapfv)
    end.

  (** Construct the closure environment and the new variable map *)
  Definition make_env (fvs : list var) (mapfv_new : VarInfoMap)
             (mapfv_old : VarInfoMap) (c_old : ctor_tag) (Γ_new Γ_old : var) (gfuns : GFunMap)
  : ccstate (ctor_tag * VarInfoMap * (exp -> exp)) :=
    (* put the free variables in a new map *)
    let '(map_new', n) :=
        (fix add_fvs (l:list M.elt) n map :=
           match l with
             | [] => (map, n)
             | x :: xs =>
               add_fvs xs (n + 1)%N (Maps.PTree.set x (FVar n) map)
           end) fvs 0%N (Maps.PTree.empty VarInfo)
    in
    t1 <- get_vars fvs mapfv_old gfuns c_old Γ_old ;;
    let '(fv', g') :=  t1 in
    c_new <- make_record_ctor_tag n ;;
    ret (c_new, map_new', fun e => g' (Econstr Γ_new c_new fv' e)).

  (** Add closures to VarInfoMap *)
  Fixpoint add_closures (defs : fundefs) (mapfv : VarInfoMap)
           (env : var) (* the enviroment of defs *) : VarInfoMap :=
    match defs with
    | Fcons f typ xs e defs' =>
      let mapfv' := add_closures defs' mapfv env in
      let mapfv'' := Maps.PTree.set f (MRFun env) mapfv' in
      mapfv''
    | Fnil => mapfv
    end.

  (** Add closures to GFunMap *)
  Fixpoint add_closures_gfuns (defs : fundefs) (gfuns : GFunMap) (is_closed : bool) : GFunMap :=
    match defs with
    | Fcons f typ xs e defs' =>
      let gfuns' := add_closures_gfuns defs' gfuns is_closed in
      if is_closed then
        (* f_str <- get_pp_name f ;; *)
        (* log_msg ("Adding " ++ f_str) ;; *)
        M.set f GFun gfuns'
      else gfuns
    | Fnil => gfuns
    end.


  Definition bool_to_string (b : bool) : string :=
    if b then "true" else "false".

  (** Closure conversion *)
  Fixpoint exp_closure_conv (e : exp) (mapfv : VarInfoMap) (gfuns : GFunMap)
           (c : ctor_tag) (Γ : var) : ccstate (exp * (exp -> exp)) :=
    match e with
      | Econstr x tag ys e' =>
        t1 <- get_vars ys mapfv gfuns c Γ ;;
        let '(ys', f) := t1 in
        ef <- exp_closure_conv e' (Maps.PTree.set x BoundVar mapfv) gfuns c Γ ;;
        ret (Econstr x tag ys' ((snd ef) (fst ef)), f)
      | Ecase x pats =>
        pats' <-
        (fix mapM_cc l :=
         match l with
           | [] => ret []
           | (y, e) :: xs =>
             ef <- exp_closure_conv e mapfv gfuns c Γ ;;
             xs' <- mapM_cc xs ;;
             ret ((y, ((snd ef) (fst ef))) :: xs')
         end) pats;;
        t1 <- get_var x mapfv gfuns c Γ ;;
        let '(x', f1) := t1 in
        ret (Ecase x' pats', f1)
      | Eproj x tag n y e' =>
        t1 <- get_var y mapfv gfuns c Γ ;;
        let '(y', f) := t1 in
        ef <- exp_closure_conv e' (Maps.PTree.set x BoundVar mapfv) gfuns c Γ ;;
        ret (Eproj x tag n y' ((snd ef) (fst ef)), f)
      | Eletapp x f ft xs e' =>
        t1 <- get_var f mapfv gfuns c Γ ;;
        let '(f', g1) := t1 in
        t2 <- get_vars xs mapfv gfuns c Γ ;;
        let '(xs', g2) := t2 in
        ptr <- get_name f code_suffix ;;
        Γ' <- get_name f clo_env_suffix ;;
        ef <- exp_closure_conv e' (Maps.PTree.set x BoundVar mapfv) gfuns c Γ ;;
        ret (Eproj ptr clo_tag 0 f'
                   (Eproj Γ' clo_tag 1 f'
                          (Eletapp x ptr ft (Γ' :: xs')
                                   ((snd ef) (fst ef)))),
             fun e => g1 (g2 e))
      | Efun defs e =>
        let fv := fundefs_fv defs in
        let fvs :=  List.filter (fun x => match M.get x gfuns with Some _ => false | None => true end) (PS.elements fv) in
        (* let fvs := PS.elements fv in *)
         Γ' <- get_named_str "env";;
        (* register its pretty name *)
        t1 <- make_env fvs (Maps.PTree.empty VarInfo) mapfv c Γ' Γ gfuns ;;
        let '(c', mapfv_new, g1) := t1 in
        let is_closed := match fvs with [] => true | _ => false end in
        (* debug *)
        (* fv_names <- get_pp_names_list fvs ;; *)
        (* log_msg (concat " " ("Closed" :: bool_to_string is_closed :: "Block has fvs :" :: fv_names)) ;; *)

        let mapfv' := add_closures defs mapfv Γ' in
        let gfuns' := add_closures_gfuns defs gfuns is_closed in

        defs' <- fundefs_closure_conv defs defs mapfv_new gfuns' c' ;;
        ef <- exp_closure_conv e mapfv' gfuns' c Γ ;;
        ret (Efun defs' ((snd ef) (fst ef)), g1)
      | Eapp f ft xs =>
        t1 <- get_var f mapfv gfuns c Γ ;;
        let '(f', g1) := t1 in
        t2 <- get_vars xs mapfv gfuns c Γ ;;
        let '(xs', g2) := t2 in
        ptr <- get_name f code_suffix ;;
        Γ <- get_name f clo_env_suffix ;;
        ret (Eproj ptr clo_tag 0 f'
                   (Eproj Γ clo_tag 1 f'
                          (Eapp ptr ft (Γ :: xs'))), fun e => g1 (g2 e))
    | Eprim_val x prim e' =>
      ef <- exp_closure_conv e' (Maps.PTree.set x BoundVar mapfv) gfuns c Γ ;;
      ret (Eprim_val x prim ((snd ef) (fst ef)), id)
    | Eprim x prim ys e' =>
      t1 <- get_vars ys mapfv gfuns c Γ ;;
      let '(ys', f) := t1 in
      ef <- exp_closure_conv e' (Maps.PTree.set x BoundVar mapfv) gfuns c Γ ;;
      ret (Eprim x prim ys' ((snd ef) (fst ef)), f)
    | Ehalt x =>
      t1 <- get_var x mapfv gfuns c Γ ;;
      let '(x', f) := t1 in
      ret (Ehalt x', f)
    end
  with fundefs_closure_conv (all_defs defs : fundefs) (mapfv : VarInfoMap) (gfuns : GFunMap) (c : ctor_tag)
       : ccstate fundefs  :=
         match defs with
         | Fcons f tag ys e defs' =>
           (* formal parameter for the environment pointer *)
             Γ <- get_named_str "env" ;;
             (* Add mut rec functions to map *)
             let mapfv' := add_closures all_defs mapfv Γ in
             (* Add arguments to the map *)
             let mapfv' := add_params ys mapfv' in
             ef <- exp_closure_conv e mapfv' gfuns c Γ ;;
             defs'' <- fundefs_closure_conv all_defs defs' mapfv gfuns c ;;
             ret (Fcons f tag (Γ :: ys) ((snd ef) (fst ef)) defs'')
           | Fnil => ret Fnil
         end.

  Definition populate_map (s : FVSet) (map : VarInfoMap) : VarInfoMap :=
    PS.fold (fun x map => M.set x BoundVar map) s map.


  (* TODO move *)
  Definition get_name (c : comp_data) : (var * comp_data) :=
    let 'mkCompData n c i f e fenv names imap log := c in
    let c' := mkCompData (n + 1)%positive c i f e fenv names imap log in
    (n, c').

  Definition closure_conversion_top (e : exp) (c: comp_data) :=
    let '(Γ, c) := get_name c in
    let map := populate_map (exp_fv e) (Maps.PTree.empty VarInfo) in
    let '(ef'_err, (c', _)) :=
        run_compM (exp_closure_conv e map (Maps.PTree.empty GFunInfo) 1%positive Γ)
                  c tt in
    match ef'_err with
    | Ret (e', f') =>
      let cenv' := add_closure_tag clo_tag clo_itag (cenv c')  in
      let c'' := put_ctor_env cenv' c' in
      (Ret (f' e'), c'')
    | Err str =>
      (Err str, c')
    end.

End CC.
