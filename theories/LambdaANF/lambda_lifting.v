(* Computational definition and declarative spec for lambda lifting. Part of the CertiRocq project.
 * Author: Anonymized, 2016
 *)

Require Import Common.compM.
Require Import LambdaANF.alpha_conv LambdaANF.term LambdaANF.term_util LambdaANF.ctx LambdaANF.state LambdaANF.set_util LambdaANF.identifiers LambdaANF.List_util
        LambdaANF.functions LambdaANF.Ensembles_util LambdaANF.uncurry LambdaANF.tactics.
From Stdlib Require Import ZArith.Znumtheory.
From Stdlib Require Import Lists.List MSets.MSets MSets.MSetRBT Numbers.BinNums
        NArith.BinNat PArith.BinPos Sets.Ensembles.
Require Import ExtLib.Structures.Monads ExtLib.Data.Monads.StateMonad ExtLib.Data.Monads.OptionMonad.
Require Import compcert.lib.Coqlib.
Require Import MetaRocq.Utils.bytestring.
Import ListNotations Nnat MonadNotation PS.
Require Import compcert.lib.Maps.

Close Scope Z_scope.
Open Scope monad_scope.


(** * Lambda lifting *)

(** This transformation assumes that all bindings are unique and disjoint from
    the free variables of an expression.

    Given an expression of the form

    let f_1 x_1 = e_1
        ....
    and f_n x_n = e_n
    in e

    it will turn into the expression (up to α-renaming)

    let f_1' x_1 fvs = C [e_1]
        ....
    and f_n' x_n fvs = C [e_n]
    in C [e]

    where fvs are the free variables of the mutually recursive function
    definition and f_i's are now closed functions (modulo references to
    other closed functions)

    and C is a function bundle consisting of wrapper functions:

    let f_1 x_1 = f_1' x_1 fvs
        ...
    and f_n x_n = f_n' x_1 fvs
    in [·]


    f_i's that are used in known applied positions can be replaced
    with the closed functions f_i' and have their environment stored in
    registers.

    Escaping f_i's will enter the function through the wrapper which
    will be closure converted in the subsequent closure conversion pass.

**)

(** * Optimizations of the above transformation *)

(*
     Design choices for the above tranformation:

     1) What known uses of f_i will be inlined?
        This choice might incue extra closure allocation in the calling
        function. Currently we inplement two approaches:

        - Inline all (default)
        - Inline only if fvs are already in scope (local variables or fvs)

     2) fvs will be pushed into the stack and pop if their live across a
        non-tail call, incuring extra overhead.
        We calculate the number of pushes and pops from the stack a fv
        requires and we don't lambda lift the function if a fv requires
        more pushes and pops than our threshold (parameter max_push)

     3) Indirect calls go through the wrapper. We might wish to inline the known
     call inside the wrapper in subsequent passes to avoud the overhead (Flambda does something similar).
     We currently don't since experiments do not suggest performance improvement.
*)

(** * Computational Defintion *)


Section LambdaLifting.

  Context (max_args : nat). (* Maximum number of arguments that a function can have *)
  Context (max_push : nat). (* Maximum amount of times that a lifted var is allows to be stored in the stack. *)
                            (* To calculate the tradeoff between projecting from environment/stack push *)

  (* The lifting decision. Used to decide whether a particular call should use the
     lifted function or the closure (i.e. the wrapper) *)
  Context (lift_dec : list var (* the free vars of the callee *) -> FVSet (* the vars is scope in the call site *) -> bool).

  Inductive VarInfo : Type :=
  (* A variable that is free in the current function definition.
   The first argument is the name of the parameter of the lambda
   lifted function that corresponds to this free variable *)
  | FreeVar : var -> VarInfo
  | WrapperFun : var -> VarInfo.

  (* Maps variables to [VarInfo] *)
  Definition VarInfoMap := Maps.PTree.t VarInfo.

  Inductive FunInfo : Type :=
  (* A known function that is lifted *)
  | Fun :
      var ->        (* New name for the lambda lifted version *)
      fun_tag ->    (* New fun_tag *)
      list var ->   (* Free variables as list *)
      PS.t ->       (* Free variables as sets *)
      list var ->   (* Lifted variables. Invariant: either the same as the list of fvs or empty. (Use a flag?) *)
      FunInfo
  (* A known function that is not lifted *)
  | NoLiftFun :
      list var ->   (* Free variables as list *)
      PS.t ->       (* Free variables as sets *)
      FunInfo.

  (* Maps known functions to [FunInfo] *)
  Definition FunInfoMap := Maps.PTree.t FunInfo.

  (* A global function name *)
  Inductive GFunInfo : Type :=
    GFun : (* var -> *) GFunInfo (* Original global function *)
  | LGFun : GFunInfo.

  Definition GFunMap := M.t GFunInfo.

  Definition lambdaM := @compM' unit.

  Fixpoint add_functions (B : fundefs) (fvs : list var) (sfvs : PS.t) (args : list var)
           (m : FunInfoMap) (gfuns : GFunMap)
    : lambdaM (FunInfoMap * GFunMap):=
    match B with
    | Fcons f ft xs _ B =>
      '(m', gfuns') <- add_functions B fvs sfvs args m gfuns ;;
      (* is the original function closed? *)
      let is_closed := match fvs with [] => true | _ => false end in
      (* is the lifted function closed? *)
      let is_closed_lifted := (length fvs =? length args)%nat in
      (* if the function block is closed add it to the global function map *)
      let gfuns'' := if is_closed then M.set f GFun gfuns' else gfuns' in
      if is_closed_lifted then
        (* Lift only if closed *)
        (* new name for lambda lifted definition - this function will always be known *)
        f' <- get_name f "_known";;
        (* new fun_tag for lambda lifted definition *)
        ft' <- get_ftag (N.of_nat (length xs)) ;;
        let gfuns''' := M.set f' LGFun gfuns'' in
        ret (M.set f (Fun f' ft' fvs sfvs args) m', gfuns''')
      else
        ret (M.set f (NoLiftFun fvs sfvs) m', gfuns'')
    | Fnil => ret (m, gfuns)
    end.

  Definition rename (map : VarInfoMap) (x : var) : var :=
    match M.get x map with
    | Some inf =>
      match inf with
      | FreeVar y => y
      | WrapperFun y => y
      end
    | None => x
    end.

  Definition rename_lst (map : VarInfoMap) (xs : list var) : list var :=
    (* all list of variables in the AST are in an escaping positions *)
    List.map (rename map) xs.

  Fixpoint add_free_vars (fvs : list var) (m : VarInfoMap)
    : lambdaM (list var * VarInfoMap) :=
    match fvs with
    | [] => ret ([], m)
    | y :: ys =>
      p <- add_free_vars ys m ;;
      y' <- get_name y "";;
      let (ys', m') := p in
      ret (y' :: ys', M.set y (FreeVar y') m')
    end.

  Definition FVMap := Maps.PTree.t PS.t.

  (* Used when wrappers are defined separately from the mut. def. function bundle *)
  Fixpoint make_wrappers (B: fundefs) (fvm : VarInfoMap) (fm: FunInfoMap) : lambdaM (option fundefs * VarInfoMap):=
    match B with
    | Fcons f ft xs e B =>
      match M.get f fm with
      | Some inf =>
        match inf with
        | Fun f' ft' fvs sfvs args =>
          g <- get_name f "_wrapper" ;;
          xs' <- get_names_lst xs "" ;;
          cm <- make_wrappers B fvm fm ;;
          let (mb, fvm') := cm in
          let fvm'' := M.set f (WrapperFun g) fvm' in
          match mb with
          | Some Bw => ret (Some (Fcons g ft xs' (Eapp f' ft' (xs' ++ (rename_lst fvm args))) Bw), fvm'')
          | None => ret (Some (Fcons g ft xs' (Eapp f' ft' (xs' ++ (rename_lst fvm args))) Fnil), fvm'')
          end
        | NoLiftFun _ _ => ret (None, fvm) (* That's OK because the hole bundle is either all Fun or all NoLiftFun *)
        end
      | None =>
        f_str <- get_pp_name f ;;
        failwith ("Internal error in make_wrappers: All known functions should be in map. Could not find " ++ f_str)%bs
      end
    | Fnil => ret (Some Fnil, fvm)
    end.

  Definition fundefs_max_params (B: fundefs) : nat :=
    (fix aux B p : nat :=
       match B with
       | Fcons f ft xs e B =>
         aux B (max (length xs) p)
       | Fnil => 0
       end) B 0.

  Definition name_block B :=
    match B with
    | Fcons f _ _ _ _ => f
    | Fnil => 1%positive
    end.

  Section TrueFV.

    (* Returns the FVs of a term. It takes into account calls that can be modified
       to call lambda-lifted functions *)

    Variable (funmap : FunInfoMap).
    Variable (active_fun : FVSet). (* Functions whose scope is currently active *)


    Fixpoint exp_true_fv_aux (e : exp)
             (scope  : FVSet) (* the current variables in scope. *)
             (fvset : PS.t) : PS.t :=
      match e with
      | Econstr x c ys e =>
        let fvset' := add_list scope fvset ys in
        exp_true_fv_aux e (add x scope) fvset'
      | Ecase x pats =>
        let fvset' := fold_left (fun fvs p => exp_true_fv_aux (snd p) scope fvs) pats fvset in
        if mem x scope then fvset' else PS.add x fvset'
      | Eproj x tau n y e =>
        let fvset' := if mem y scope then fvset else PS.add y fvset in
        exp_true_fv_aux e (add x scope) fvset'
      | Eletapp x f ft ys e =>
        let fvset' := match funmap ! f with
                      | Some (Fun f' ft' fvs sfvs lfvs) => (* A known function call that can be lifted *)
                        if lift_dec lfvs fvset then union_list fvset (f' :: lfvs)
                        else if mem f scope then fvset else PS.add f fvset
                      | Some (NoLiftFun _ _) | None => if mem f scope then fvset else PS.add f fvset
                      end
        in
        let fvset'' := add_list scope fvset' ys in
        exp_true_fv_aux e (add x scope) fvset''
      | Efun defs e =>
        let fvs':= fundefs_fv defs in
        let '(scope', fvset') := fundefs_true_fv_aux defs scope fvset in
        exp_true_fv_aux e scope' fvset'
      | Eapp f ft xs =>
        let fvset' := match funmap ! f with
                      | Some (Fun f' ft' fvs sfvs lfvs) => (* A known function call that can be lifted *)
                        if lift_dec lfvs fvset then union_list fvset (f' :: lfvs)
                        else if mem f scope then fvset else PS.add f fvset
                      | Some (NoLiftFun _ _) | None => if mem f scope then fvset else PS.add f fvset
                      end
        in
        add_list scope fvset' xs
      | Eprim_val x p e =>
        exp_true_fv_aux e (add x scope) fvset
      | Eprim x prim ys e =>
        let fvset' := add_list scope fvset ys in
        exp_true_fv_aux e (add x scope) fvset'
      | Ehalt x => if mem x scope then fvset else PS.add x fvset
    end
    with fundefs_true_fv_aux (defs : fundefs) (scope : FVSet) (fvset : PS.t) : FVSet * PS.t :=
           match defs with
           | Fcons f t ys e defs' =>
             let (scope', fvset') := fundefs_true_fv_aux defs' (add f scope) fvset in
             (scope', exp_true_fv_aux e (union_list scope' ys) fvset')
           | Fnil => (scope, fvset)
           end.

    Definition exp_true_fv e := exp_true_fv_aux e PS.empty PS.empty.

    Definition fundefs_true_fv B := snd (fundefs_true_fv_aux B PS.empty PS.empty).

  End TrueFV.


  (* TODO move *)
  Definition subset_list (l : list var) (s : PS.t) :=
    fold_left (fun b e => PS.mem e s && b) l true.

  Fixpoint take {A} (n: nat) (l : list A) :=
    match n with
    | 0 => []
    | S n =>
      match l with
      | [] => []
      | x :: xs => x :: take n xs
      end
    end.

  Fixpoint occurs_in_exp (k:var) (curr_f: PS.t) (e:exp) : bool :=
    match e with
    | Econstr z _ xs e1 =>
      eq_var z k || occurs_in_vars k xs || occurs_in_exp k curr_f e1
    | Ecase x arms =>
      eq_var k x ||
              (fix occurs_in_arms (arms: list (ctor_tag * exp)) : bool :=
                 match arms with
                 | nil => false
                 | p::arms1 => match p with
                               | (_,e) => occurs_in_exp k curr_f e || occurs_in_arms arms1
                               end
                 end) arms
    | Eproj z _ _ x e1 =>
      eq_var z k || eq_var k x || occurs_in_exp k curr_f e1
    | Eletapp z f _ xs e1 =>
      (* If the call is recursive, then after lambda lifting k will appear free in the subexpression *)
      eq_var z k || eq_var f k || PS.mem f curr_f || occurs_in_vars k xs || occurs_in_exp k curr_f e1
    | Efun fds e =>
      occurs_in_fundefs k curr_f fds || occurs_in_exp k curr_f e
    | Eapp x _ xs => eq_var k x || PS.mem x curr_f || occurs_in_vars k xs
    | Eprim_val z p e1 =>
      eq_var z k || occurs_in_exp k curr_f e1
    | Eprim z _ xs e1 =>
      eq_var z k || occurs_in_vars k xs || occurs_in_exp k curr_f e1
    | Ehalt x => eq_var x k
    end
  (* Returns true iff [k] occurs within the function definitions [fds] *)
  with occurs_in_fundefs (k:var) (curr_f: PS.t) (fds:fundefs) : bool :=
         match fds with
         | Fnil => false
         | Fcons z _ zs e fds1 =>
           eq_var z k || occurs_in_vars k zs || occurs_in_exp k curr_f e ||
           occurs_in_fundefs k curr_f fds1
         end.



  (* Calculate how many times an argument has to be pushed into the (shadow) stack because
   * of intermediate calls. Assumes unique binders *)
  Fixpoint stack_push (x : var) (curr_f : PS.t) (e : exp) : nat :=
    match e with
    | Econstr _ _ _ e
    | Eproj _ _ _ _ e
    | Eprim_val _ _ e
    | Eprim _ _ _ e
    | Efun _ e =>
      stack_push x curr_f e
    | Eapp _ _ _
    | Ehalt _ => 0
    | Ecase _ P =>
      fold_left (fun n br => max n (stack_push x curr_f (snd br))) P 0
    | Eletapp _ f ft ys e =>
      let n := stack_push x curr_f e in
      (* Before the call, if x is used in e, then it has to be stored *)
      if occurs_in_exp x curr_f e then n + 1 else n
    end.

  Fixpoint stack_push_fundefs_aux (x : var) (curr_f : PS.t)  (B : fundefs) : nat :=
    match B with
    | Fcons f ft xs e B' =>
      max (stack_push x curr_f e) (stack_push_fundefs_aux x curr_f B')
    | Fnil => 0
    end.

  Definition stack_push_fundefs (x : var) (B : fundefs) : nat :=
    stack_push_fundefs_aux x (fundefs_names B) B.

  Fixpoint exp_lambda_lift (e : exp) (scope: PS.t) (active_funs : PS.t)
           (fvm : VarInfoMap) (fm : FunInfoMap) (gfuns : GFunMap) : lambdaM exp :=
    match e with
    | Econstr x t ys e =>
      e' <- exp_lambda_lift e (PS.add x scope) active_funs fvm fm gfuns ;;
      ret (Econstr x t (rename_lst fvm ys) e')
    | Ecase x P =>
      P' <-
      (fix mapM_ll l :=
         match l with
         | [] => ret []
         | (c, e) :: P =>
           e' <- exp_lambda_lift e scope active_funs fvm fm gfuns ;;
              P' <- mapM_ll P ;;
              ret ((c, e') :: P')
         end) P ;;
      ret (Ecase (rename fvm x) P')
    | Eproj x t N y e =>
      e' <- exp_lambda_lift e (PS.add x scope) active_funs fvm fm gfuns ;;
      ret (Eproj x t N (rename fvm y) e')
    | Eletapp x f ft ys e =>
      e' <- exp_lambda_lift e (PS.add x scope) active_funs fvm fm gfuns ;;
      match fm ! f with
      | Some (Fun f' ft' fvs sfvs args) =>
          if lift_dec args scope then
            ret (Eletapp x (rename fvm f') ft' (rename_lst fvm (ys ++ args)) e')
          else ret (Eletapp x (rename fvm f) ft (rename_lst fvm ys) e')
      | Some (NoLiftFun _ _) | None =>
        ret (Eletapp x (rename fvm f) ft (rename_lst fvm ys) e')
      end
    | Efun B e =>
      (* Find the free variables of the fundefs *)
      let sfvsi := fundefs_true_fv fm B in
      (* Remove global functions *)
      let sfvs := PS.filter (fun x => match M.get x gfuns with Some _ => false | None => true end) sfvsi in
      (* Turn to list *)
      let fvs := PS.elements sfvs in
      (* Can all arguments be lifted? *)
      let lfvs := if List.existsb (fun x => let n := stack_push_fundefs x B in (max_push <? n)) fvs then [] else fvs in
      (* DEBUG *)
      (* b_name <- get_pp_name (name_block B) ;; *)
      (* fv_names <- get_pp_names_list (PS.elements sfvsi) ;; *)
      (* log_msg (String.concat " " ("Block" :: b_name :: "has fvs :" :: fv_names)) ;; *)
      (* END DEBUG *)
      (* Number of argument slots available. *)
      let lifted_args := max_args - (fundefs_max_params B) in
      (* Don't lift if args > slots *)
      let lfvs := if (lifted_args <? List.length lfvs) then [] else lfvs in
      '(fm', gfuns') <- add_functions B fvs sfvs lfvs fm gfuns ;;
      let names := fundefs_names B in
      let scope' := PS.union names scope in
      let max_params := fundefs_max_params B in
      B' <- fundefs_lambda_lift B B names (PS.union names active_funs) fvm fm' gfuns' lifted_args ;;
      '(ob, fvm') <- make_wrappers B fvm fm' ;;
      e' <- exp_lambda_lift e (PS.union names scope) active_funs fvm' fm' gfuns' ;;
      match ob with
      | Some Bw => ret (Efun B' (Efun Bw e'))
      | None => ret (Efun B' e')
      end
    | Eapp f ft xs =>
      match fm ! f with
      | Some (Fun f' ft' fvs sfvs args) =>
        if lift_dec args scope then
          ret (Eapp (rename fvm f') ft' (rename_lst fvm (xs ++ args)))
        else
          (* f_str_r <- get_pp_name (rename fvm f) ;; *)
          (* log_msg ("Lifted is not called. Calling " ++ f_str_r) ;; *)
          ret (Eapp (rename fvm f) ft (rename_lst fvm xs))
      | Some (NoLiftFun _ _) | None =>
        ret (Eapp (rename fvm f) ft (rename_lst fvm xs))
      end
    | Eprim_val x p e =>
      e' <- exp_lambda_lift e (PS.add x scope) active_funs fvm fm gfuns ;;
      ret (Eprim_val x p e')
    | Eprim x f ys e =>
      e' <- exp_lambda_lift e (PS.add x scope) active_funs fvm fm gfuns ;;
      ret (Eprim x f (rename_lst fvm ys) e')
    | Ehalt x => ret (Ehalt (rename fvm x))
    end
  with fundefs_lambda_lift B Bfull (fnames : FVSet) active_funs fvm (fm : FunInfoMap) (gfuns : GFunMap) (fv_no : nat) :=
         match B with
         | Fcons f ft xs e B =>
           match M.get f fm with
           | Some (Fun f' ft' fvs sfvs args) =>
             (* DEBUG *)
             (* f_str <- get_pp_name f ;; *)
             (* fv_names <- get_pp_names_list fvs ;; *)
             (* log_msg (String.concat " " (f_str :: "has fvs :" :: fv_names)) ;; *)
             (* END DEBUG *)
             '(ys, fvm') <- add_free_vars args fvm ;;
             '(ob, fvm'') <- make_wrappers Bfull fvm' fm ;;
             (* Variables in scope are :
                1. Whatever variables are locally bound (current functions, arguments, local defs), and
                2. The FVs of the current function *)
             e' <- exp_lambda_lift e (PS.union fnames (union_list sfvs xs)) active_funs fvm'' fm gfuns ;;
             B' <- fundefs_lambda_lift B Bfull fnames active_funs fvm fm gfuns fv_no ;;
             match ob with
             | Some Bw => ret (Fcons f' ft' (xs ++ ys) (Efun Bw e')  B')
             | None =>
               f_str <- get_pp_name f ;;
               failwith ("Internal error in fundefs_lambda_lift: Wrappers cannot be empty in lambda lifted function " ++ f_str)%bs
             end
           | Some (NoLiftFun fvs sfvs) =>
             e' <- exp_lambda_lift e (PS.union fnames (union_list sfvs xs)) active_funs fvm fm gfuns ;;
             B' <- fundefs_lambda_lift B Bfull fnames active_funs fvm fm gfuns fv_no ;;
             ret (Fcons f ft xs e'  B')
           | None =>
             f_str <- get_pp_name f ;;
             failwith ("Internal error in fundefs_lambda_lift: All known functions should be in map. Could not find " ++ f_str)%bs
           end

         | Fnil => ret Fnil
         end.

  (* Example :

   let f x =
     let g y = x + y + z in
       g 3 + x

   ==>

   let f' x z' =
       let g' y x' z'' = y + x' + z'' in
       let g y = g' y x z'
       in g' 3 x z' + 3 in
   let f x = f' x z
   *)

End LambdaLifting.

Definition lift_all (fvs : list var) (scope : FVSet) := true.

(* Never increase fvs *)
Definition lift_conservative (fvs : list var) (scope : FVSet) := PS.subset (union_list PS.empty fvs) scope.

Definition lambda_lift (args : nat) (no_push : nat) (inl : bool) (e : exp) (c : comp_data) : error exp * comp_data :=
  let '(e', (c', _)) := run_compM (exp_lambda_lift args no_push (if inl then lift_all else lift_conservative)
                                                   e PS.empty PS.empty (Maps.PTree.empty VarInfo)
                                                   (Maps.PTree.empty FunInfo) (M.empty GFunInfo))
                                  c tt in
  (e', c').


(** * Relational Defintion *)

Inductive Add_functions :
  fundefs ->
  list var ->
  (var -> var) ->
  (var -> option (var * fun_tag * list var)) ->
  Ensemble var ->
  (var -> var) ->
  (var -> option (var * fun_tag * list var)) ->
  Ensemble var ->
  Prop :=
| Add_Fcons :
    forall f ft xs e B fvs σ σ' ζ ζ' S S' f' ft',
      Add_functions B fvs σ ζ S σ' ζ' S' ->
      Ensembles.In _ S' f' ->
      Add_functions (Fcons f ft xs e B) fvs σ ζ S
                    (σ' {f ~> f} {f' ~> f'}) (ζ' {f ~> Some (f', ft', fvs)})
                    (Setminus _ S' (Singleton _ f'))
| Add_Fnil :
    forall fvs σ ζ S,
      Add_functions Fnil fvs σ ζ S σ ζ S.

(* Map from the original name to the name of the lifted function *)
Definition lifted_name (ζ : var -> option (var * fun_tag * list var)) : var -> option var :=
  fun f => (liftM (fun x => (fst (fst x)))) (ζ f).

(* Map from the original name to the list of free vars *)
Definition free_vars (ζ : var -> option (var * fun_tag * list var)) : var -> option (list var) :=
  fun f => (liftM (fun x => snd x)) (ζ f).

(** The domain of ζ *)
Definition Funs (ζ : var -> option (var * fun_tag * list var)) : Ensemble var :=
  domain (lifted_name ζ).

(** The image of ζ on its domain - i.e. the names of the lifted functions *)
Definition LiftedFuns (ζ : var -> option (var * fun_tag * list var)) : Ensemble var :=
  image' (lifted_name ζ) (Funs ζ).

(**  The free variables of functions in ζ, alternative definition *)
Definition FunsFVsLst (ζ : var -> option (var * fun_tag * list var)) : Ensemble (list var) :=
  fun fvs => exists f f' ft', ζ f = Some (f', ft', fvs).

(**  The free variables of functions in ζ *)
Definition FunsFVs (ζ : var -> option (var * fun_tag * list var)) : Ensemble var :=
  fun v => exists f f' ft' fvs, ζ f = Some (f', ft', fvs) /\
                        Ensembles.In _ (FromList fvs) v.

Inductive Make_wrappers :
  (var -> option (var * fun_tag * list var)) ->
  (var -> var) ->
  fundefs ->
  Ensemble var ->
  fundefs ->
  Ensemble var ->
  (var -> var) ->
  Prop :=
| MW_Fnil :
    forall ζ σ S, Make_wrappers ζ σ Fnil S Fnil S σ
| MW_Fcons :
    forall  (ζ : var -> option (var * fun_tag * list var)) σ σ' f ft xs xs' e B fds S S' f' ft' fvs g,
      ζ f = Some (f', ft', fvs) ->
      (FromList xs') \subset S ->
      NoDup xs' -> length xs = length xs' ->
      g \in (S \\ FromList xs') ->
      Make_wrappers ζ σ B (S \\ FromList xs' \\ [set g]) fds S' σ' ->
      Make_wrappers ζ σ (Fcons f ft xs e B) S (Fcons g ft xs' (Eapp f' ft' (xs' ++ (map σ fvs))) fds) S' (σ' {f ~> g}).


Inductive Exp_lambda_lift :
  (var -> option (var * fun_tag * list var)) ->
  (var -> var) ->
  exp ->
  Ensemble var ->
  exp ->
  Ensemble var ->
  Prop :=
| LL_Econstr :
    forall ζ σ x t ys e e' S S',
      Exp_lambda_lift ζ (σ {x ~> x}) e S e' S' ->
      Exp_lambda_lift ζ σ (Econstr x t ys e) S (Econstr x t (map σ ys) e') S'
| LL_Ecase_nil :
    forall ζ σ x S,
      Exp_lambda_lift ζ σ (Ecase x []) S (Ecase (σ x) []) S
| LL_Ecase_cons :
    forall ζ σ x y c e e' P P' S S' S'',
      Exp_lambda_lift ζ σ e S e' S' ->
      Exp_lambda_lift ζ σ (Ecase x P) S' (Ecase y P') S'' ->
      Exp_lambda_lift ζ σ (Ecase x ((c, e) :: P)) S (Ecase (σ x) ((c, e') :: P')) S''
| LL_Eproj :
    forall ζ σ x t N y e e' S S',
      Exp_lambda_lift ζ (σ {x ~> x}) e S e' S' ->
      Exp_lambda_lift ζ σ (Eproj x t N y e) S (Eproj x t N (σ y) e') S'
(* Note: That was the old approach to lambda lifting: wrapper
         functions were mutually defined with the original function
         bundle.  The problem with this approach is that the whole
         bundle after lambda lifting has the original free variables
         (because of the wrappers), meaning lambda-lifted functions
         cannot be considered closed top-level functions by closure
         conversion and they will end up in closure environments of
         the callers. Until recently, the inductive spec of lambda
         lifting supported both approaches. I'm commenting out the
         original rules to declutter the proofs.
         Old proofs can be retrieved from commit 3e9040fcff9434f9274091e9bac79b935ddbb32d  *)
(* | LL_Efun1 : (* wrappers are mutually defined *) *)
(*     forall B B' e e' σ σ' ζ ζ' fvs S S' S'' S''', *)
(*       FromList fvs \subset occurs_free_fundefs B :|: (FunsFVs ζ :|: LiftedFuns ζ) -> *)
(*       NoDup fvs -> *)
(*       Add_functions B fvs σ ζ S σ' ζ' S' -> *)
(*       Fundefs_lambda_lift1 ζ' σ' B S' B' S'' -> *)
(*       Exp_lambda_lift ζ' σ' e S'' e' S''' -> *)
(*       Exp_lambda_lift ζ σ (Efun B e) S (Efun B' e') S''' *)
| LL_Efun2 : (* wrappers are defined afterwards *)
    forall B B' e e' fds σ σ' σ'' ζ ζ' fvs S S' S'' S''' S'''',
      FromList fvs \subset occurs_free_fundefs B :|: (FunsFVs ζ :|: LiftedFuns ζ) ->
      NoDup fvs ->
      Add_functions B fvs σ ζ S σ' ζ' S' ->
      Fundefs_lambda_lift2 ζ' σ' B B S' B' S'' ->
      Make_wrappers ζ' σ' B S'' fds S''' σ'' ->
      Exp_lambda_lift ζ' σ'' e S''' e' S'''' ->
      Exp_lambda_lift ζ σ (Efun B e) S (Efun B' (Efun fds e')) S''''
| LL_Efun3 : (* No Lambda Lifting *)
    forall B B' e e' σ ζ S S' S'',
      Fundefs_lambda_lift3 ζ (extend_fundefs σ B B) B B S B' S' ->
      Exp_lambda_lift ζ (extend_fundefs σ B B) e S' e' S'' ->
      Exp_lambda_lift ζ σ (Efun B e) S (Efun B' e') S''
| LL_Eletapp_known :
    forall ζ σ x f ft xs e e' f' ft' fvs S S',
      ζ f = Some (f', ft', fvs) ->
      Exp_lambda_lift ζ (σ {x ~> x}) e S e' S' ->
      Exp_lambda_lift ζ σ (Eletapp x f ft xs e) S (Eletapp x (σ f') ft' (map σ (xs ++ fvs)) e') S'
| LL_Eletapp_unknown :
    forall ζ σ x f ft xs e e' S S',
      Exp_lambda_lift ζ  (σ {x ~> x}) e S e' S' ->
      Exp_lambda_lift ζ σ (Eletapp x f ft xs e) S (Eletapp x (σ f) ft (map σ xs) e') S'
| LL_Eapp_known :
    forall ζ σ f ft xs f' ft' fvs S,
      ζ f = Some (f', ft', fvs) ->
      Exp_lambda_lift ζ σ (Eapp f ft xs) S (Eapp (σ f') ft' (map σ (xs ++ fvs))) S
| LL_Eapp_unknown :
    forall ζ σ f ft xs S,
      Exp_lambda_lift ζ σ (Eapp f ft xs) S (Eapp (σ f) ft (map σ xs)) S
| LL_Eprim_val :
    forall ζ σ x p e e' S S',
      Exp_lambda_lift ζ (σ {x ~> x}) e S e' S' ->
      Exp_lambda_lift ζ σ (Eprim_val x p e) S (Eprim_val x p e') S'
| LL_Eprim :
    forall ζ σ x f ys e e' S S',
      Exp_lambda_lift ζ (σ {x ~> x}) e S e' S' ->
      Exp_lambda_lift ζ σ (Eprim x f ys e) S (Eprim x f (map σ ys) e') S'
| LL_Ehalt :
    forall ζ σ x S,
      Exp_lambda_lift ζ σ (Ehalt x) S (Ehalt (σ x)) S
(* with Fundefs_lambda_lift1 : *)
(*   (var -> option (var * fun_tag * list var)) -> *)
(*   (var -> var) -> *)
(*   fundefs -> *)
(*   Ensemble var -> *)
(*   fundefs -> *)
(*   Ensemble var -> *)
(*   Prop := *)
(*      | LL_Fcons1 : *)
(*          forall ζ σ f ft xs xs' e e' B B' S S' S'' f' ft' fvs ys, *)
(*            ζ f = Some (f', ft', fvs) -> *)
(*            FromList ys \subset S -> *)
(*            FromList xs' \subset (S \\ (FromList ys)) -> *)
(*            NoDup ys -> NoDup xs' -> *)
(*            length ys = length fvs -> *)
(*            length xs' = length xs ->  *)
(*            Exp_lambda_lift ζ (σ <{ (xs ++ fvs) ~> (xs ++ ys) }>) *)
(*                            e ((S \\ (FromList ys)) \\ (FromList xs')) e' S' -> *)
(*            Fundefs_lambda_lift1 ζ σ B S' B' S'' -> *)
(*            Fundefs_lambda_lift1 ζ σ (Fcons f ft xs e B) S *)
(*                                 (Fcons f' ft' (xs ++ ys) e' *)
(*                                        (Fcons f ft xs' *)
(*                                               (Eapp f' ft' (xs' ++ (map σ fvs))) B')) S'' *)
(*      | LL_Fnil1 : *)
(*          forall ζ σ S, *)
(*            Fundefs_lambda_lift1 ζ σ Fnil S Fnil S *)
with Fundefs_lambda_lift2 :
  (var -> option (var * fun_tag * list var)) ->
  (var -> var) ->
  fundefs -> (* original fundefs *)
  fundefs ->
  Ensemble var ->
  fundefs ->
  Ensemble var ->
  Prop :=
     | LL_Fcons2 :
         forall ζ σ σ' f ft xs e e' B0 B B' S S' S'' S''' f' ft' fvs ys fds,
           ζ f = Some (f', ft', fvs) ->
           Included _ (FromList ys) S ->
           NoDup ys ->
           length ys = length fvs ->
           Make_wrappers ζ (σ <{ (xs ++ fvs) ~> (xs ++ ys) }>) B0 (S \\ FromList ys) fds S' σ' ->
           Exp_lambda_lift ζ σ' e S' e' S'' ->
           Fundefs_lambda_lift2 ζ σ B0 B S'' B' S''' ->
           Fundefs_lambda_lift2 ζ σ B0 (Fcons f ft xs e B) S
                                (Fcons f' ft' (xs ++ ys) (Efun fds e') B') S'''
     | LL_Fnil2 :
         forall ζ σ S B0,
           Fundefs_lambda_lift2 ζ σ B0 Fnil S Fnil S
with Fundefs_lambda_lift3 :
  (var -> option (var * fun_tag * list var)) ->
  (var -> var) ->
  fundefs ->
  fundefs ->
  Ensemble var ->
  fundefs ->
  Ensemble var ->
  Prop :=
     | LL_Fcons3 :
         forall ζ σ  f ft xs e e' B0 B B' S S' S'',
           (* extending σ with B0 ~> B0 is not technically needed but it helps some proofs *)
           Exp_lambda_lift ζ ((extend_fundefs σ B0 B0) <{ xs ~> xs }>) e S e' S' ->
           Fundefs_lambda_lift3 ζ σ B0 B S' B' S'' ->
           Fundefs_lambda_lift3 ζ σ B0 (Fcons f ft xs e B) S (Fcons f ft xs e' B') S''
     | LL_Fnil3 :
         forall ζ σ B0 S,
           Fundefs_lambda_lift3 ζ σ B0 Fnil S Fnil S.
