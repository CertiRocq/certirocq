(* Correctness proof for lambda lifting. Part of the CertiRocq project.
 * Author: Katja Vassilev, 2018
 *)

Require Import LambdaANF.term LambdaANF.identifiers LambdaANF.ctx LambdaANF.set_util LambdaANF.state.
Require Import compcert.lib.Coqlib Common.compM Common.Pipeline_utils.
From Stdlib Require Import Lists.List MSets.MSets MSets.MSetRBT Numbers.BinNums
        NArith.BinNat PArith.BinPos Sets.Ensembles micromega.Lia.
Require Import ExtLib.Structures.Monads ExtLib.Data.Monads.StateMonad.
Import ListNotations Nnat.

Import MonadNotation.
Open Scope monad_scope.

Open Scope ctx_scope.
Open Scope fun_scope.
Close Scope Z_scope.

(* Map from function identifier to its live parameter list *)
Definition live_fun : Type :=  M.t (list bool).

Definition get_fun_vars (m : live_fun) (f : var) := M.get f m.

Definition set_fun_vars (m : live_fun) (f : var) (b : list bool) :=
  M.set f b m.

(* Apply bit mask to argument list*)
Fixpoint live_args {A} (ys : list A) (bs : list bool) : list A :=
  match bs, ys with
  | [], [] => ys
  |  b :: bs', y :: ys' =>
    if b then y :: (live_args ys' bs')
    else live_args ys' bs'
  | _, _ => ys
  end.

(* Get list of list of bools corresponding to fundefs *)
Fixpoint get_bool_false {A} (ys : list A) : list bool :=
match ys with
| y :: ys' => false :: get_bool_false ys'
| [] => []
end.

Fixpoint get_bool_true {A} (ys : list A) : list bool :=
match ys with
| [] => []
| y :: ys' => true :: get_bool_true ys'
end.

(* Make initial live function *)
Fixpoint init_live_fun_aux (m : live_fun) (B : fundefs) : live_fun :=
  match B with
  | Fcons f ft xs e B' => init_live_fun_aux (set_fun_vars m f (get_bool_false xs)) B'
  | Fnil => m
end.


Definition init_live_fun (B : fundefs) : live_fun := init_live_fun_aux (M.empty _) B.

(* Identity escaping functions *)

Definition remove_escaping (L : live_fun) (f : var) : live_fun :=
  match get_fun_vars L f with
  | Some bs => M.remove f L
  | None => L
  end.

Definition remove_escapings (L : live_fun) (fs : list var) : live_fun :=
  fold_left remove_escaping fs L.

Fixpoint escaping_fun_exp (e : exp) (L : live_fun) :=
match e with
| Eapp f t ys => remove_escapings L ys
| Econstr x t ys e' => escaping_fun_exp e' (remove_escapings L ys)
| Eproj x t n y e' => escaping_fun_exp e' (remove_escaping L y)
| Eletapp x f ft ys e' => escaping_fun_exp e' (remove_escapings L ys)
| Ecase x P =>
  fold_left (fun L '(c', e') => escaping_fun_exp e' L) P L
| Ehalt x => remove_escaping L x
| Efun fl e' => escaping_fun_exp e' (escaping_fun_fundefs fl L)
| Eprim_val x p e' => escaping_fun_exp e' L
| Eprim x fs ys e' => escaping_fun_exp e' (remove_escapings L ys)
end
with escaping_fun_fundefs (B : fundefs) (L : live_fun) :=
       match B with
       | Fcons f ft xs e B' =>
         let L' := escaping_fun_exp e L in
         escaping_fun_fundefs B' L'
       | Fnil => L
       end.

(* LIve parameter analysis *)

Definition add_fun_vars (L : live_fun) (f : var) (xs : list var) (S : PS.t) : PS.t :=
  match get_fun_vars L f with
  | Some bs =>
    let xs' := live_args xs bs in
    union_list S xs'
  | None => union_list S xs
  end.

(* Returns a set that's an underapproximation of the live vars in e *)
Fixpoint live_expr (L : live_fun) (e : exp) (S : PS.t) : PS.t :=
match e with
| Econstr x t ys e' =>
  live_expr L e' (union_list S ys)
| Eproj x t m y e' =>
  live_expr L e' (PS.add y S)
| Eletapp x f ft ys e' =>
  let S' := PS.add f S in
  let S'' := add_fun_vars L f ys S' in
  live_expr L e' S''
| Ecase x P =>
  PS.add x (fold_left (fun S '(c', e') => live_expr L e' S) P S)
| Ehalt x => PS.add x S
| Eapp f t ys =>
  let S' := PS.add f S in
  add_fun_vars L f ys S'
| Efun fl e' => S (* Should not happen, assuming hoisted program *)
| Eprim_val x p e' => live_expr L e' S
| Eprim x f ys e' => live_expr L e' (union_list S ys)
end.

Fixpoint update_bs (S : PS.t) xs (bs : list bool) : (list bool * bool) :=
  match xs, bs with
  | [], _ | _, [] => (bs, false)
  | x :: xs, b :: bs =>
    let (bs', d) := update_bs S xs bs in
    if b then (b :: bs', d) (* if the bit is on don't change it *)
    else
      let b' := PS.mem x S in
      (b' :: bs', (negb (eqb b b') || d))
  end.

Definition update_live_fun (L : live_fun) (f : var) (xs : list var) (S : PS.t) : live_fun * bool :=
  match get_fun_vars L f with
  | Some bs =>
    let (bs, diff) := update_bs S xs bs in
    if diff then (set_fun_vars L f bs, diff)
    else  (L, diff)
  | None => (L, false)
  end.


(* One pass through fundefs to L variables and keep track of live variables *)
Fixpoint live (B : fundefs) (L : live_fun) (diff : bool) : live_fun * bool :=
match B with
| Fcons f ft xs e B' =>
  let S := live_expr L e PS.empty in
  let (L', d) := update_live_fun L f xs S in
  live B' L' (d || diff)
| Fnil => (L, diff)
end.

(* Iteratively create live functions for B, when they are equal, stop *)
(* Note that a naive upper bound for the number of passes is the number of total variables
   as at each step, if the process doesn't terminate at least one variable must be eliminated *)
Fixpoint find_live_helper (B : fundefs) (prev_L : live_fun) (n : nat) : error live_fun :=
match n with
| 0 => Ret prev_L
| S n' =>
  let (curr_L, diff) := live B prev_L false in
  if diff then find_live_helper B curr_L n' else Ret curr_L (* should be equal to prevL *)
end.

Fixpoint num_vars (B : fundefs) (n : nat) : nat :=
match B with
| Fcons f ft xs e B' => num_vars B' (n + length(xs))
| Fnil => n
end.


Definition find_live (e : exp) : error live_fun :=
  match e with
  | Efun B e' =>
    let initial_L := init_live_fun B in
    (* Mark all variables of escaping function as live *)
    let L' := escaping_fun_exp e' (escaping_fun_fundefs B initial_L) in
    let n := num_vars B 0 + 1 in
    find_live_helper B L' n
  | _ => Ret (M.empty _)
  end.

(* ELIMINATING VARIABLES *)

Definition is_nil {A} (l : list A) : bool :=
  match l with
  | [] => true
  | _ :: _ => false
  end.


Definition arityMap : Type := M.t fun_tag.
Definition ftagMap : Type := M.t fun_tag.

Definition elimM := @compM' unit.


(** * fun_tag bookeeping *)

(* Single pass to create arity map. Assumes that initial fun_tags are consistent with arities *)

Fixpoint make_arityMap (e : exp) (m : arityMap) : arityMap :=
  match e with
  | Econstr _ _ _ e => make_arityMap e m
  | Ecase x bs =>
    fold_left (fun m p => make_arityMap (snd p) m) bs m
  | Eproj _ _ _ _ e => make_arityMap e m
  | Eletapp x f ft xs e =>
    make_arityMap e (M.set (Positive_as_DT.of_succ_nat (length xs)) ft m)
  | Efun B e =>
    make_arityMap e (make_arityMap_fundefs B m)
  | Eapp f ft xs => M.set (Positive_as_DT.of_succ_nat (length xs)) ft m
  | Eprim_val _ _ e => make_arityMap e m
  | Eprim _ _ _ e => make_arityMap e m
  | Ehalt x => m
  end
with make_arityMap_fundefs (B : fundefs) (m : arityMap) : arityMap :=
       match B with
       | Fcons f ft xs e B =>
         let m := M.set (Positive_as_DT.of_succ_nat (length xs)) ft m in
         make_arityMap_fundefs B (make_arityMap e m)
       | Fnil => m
       end.


(* TODO move *)

Definition make_ftag (arity : nat) (c : comp_data) : fun_tag * comp_data:=
  let 'mkCompData x c i f e fenv names imap log := c in
  (f, mkCompData x c i (f + 1)%positive e (M.set f (N.of_nat arity, (List_util.fromN (0%N) arity)) fenv) names imap log).



Fixpoint create_fun_tag (L : live_fun) (m : arityMap) (B : fundefs) (c : comp_data) (fmap : ftagMap) : ftagMap * comp_data :=
  match B with
  | Fcons f ft ys e B =>
    match get_fun_vars L f with
    | Some bs =>
      let n := length (live_args ys bs) in
      let p := Positive_as_DT.of_succ_nat n in
      match M.get p m with
      | Some t => create_fun_tag L m B c (M.set f t fmap)
      | None =>
        let '(ft, c') := make_ftag n c in
        create_fun_tag L m B c' (M.set f ft fmap)
      end
    | None => create_fun_tag L m B c fmap
    end
  | Fnil => (fmap, c)
  end.




(* For debugging *)

Definition show_bool (b : bool) : string :=
  if b then "true" else "false".


Fixpoint show_bool_list (bs : list bool) : string :=
  match bs with
  | [] => ""
  | b :: bs =>
    String.concat " " [show_bool b ; show_bool_list bs]
  end.



Fixpoint is_hoisted_exp (e : exp) : bool :=
  match e with
  | Econstr _ _ _ e
  | Eproj _ _ _ _ e
  | Eletapp _ _ _ _ e
  | Eprim_val _ _ e
  | Eprim _ _ _ e => is_hoisted_exp e
  | Ecase x bs =>
    forallb (fun p => is_hoisted_exp (snd p)) bs
  | Efun B e => false
  | Eapp _ _ _ => true
  | Ehalt _ => true
  end.

Fixpoint is_hoisted_fundefs (B : fundefs) : bool :=
  match B with
  | Fcons _ _ _ e B =>
    is_hoisted_exp e && is_hoisted_fundefs B
  | Fnil => true
  end.

Definition is_hoisted (e : exp) :=
  match e with
  | Efun B e => is_hoisted_fundefs B && is_hoisted_exp e
  | _ => is_hoisted_exp e
  end.

(** Do dead paremeter elimination *)

Section Elim.

  Context (fmap : ftagMap).

  Definition get_fun_tag (f : var) : fun_tag :=
    match M.get f fmap with
  | Some t => t
  | None => 1%positive (* dummy *)
  end.



  Fixpoint eliminate_expr (L : live_fun) (e : exp) : elimM exp :=
    match e with
    | Econstr x t ys e' =>
      e'' <- eliminate_expr L e' ;;
      ret (Econstr x t ys e'')
    | Eproj x t m y e' =>
      e'' <- eliminate_expr L e' ;;
      ret (Eproj x t m y e'')
    | Eletapp x f ft ys e' =>
      (* f_str <- get_pp_name f ;; *)
      (* state.log_msg (String.concat " " ["Letapp" ; f_str ]) ;; *)
      match get_fun_vars L f with
      | Some bs =>
        (* ys_or <- get_pp_names_list ys ;;     *)
        (* state.log_msg (String.concat " " ("bs" ::  show_bool_list bs :: "Original Params" :: ys_or )) ;;  *)
        let ys' := live_args ys bs in
        e'' <- eliminate_expr L e';;
        let ft' := get_fun_tag f in
        (* ys_names <- get_pp_names_list ys' ;; *)
        (* state.log_msg (String.concat " " ["Function entry" ; f_str ; "found"; "id"; cps_show.show_pos f]) ;; *)
        (* state.log_msg (String.concat " " ("New params" :: ys_names)) ;;    *)
        ret (Eletapp x f ft' ys' e'')
      | None =>
        e'' <- eliminate_expr L e' ;;
        ret (Eletapp x f ft ys e'')
      end
    | Ecase x P =>
      P' <- (fix mapM_LD (l : list (ctor_tag * exp)) : elimM (list (ctor_tag * exp)) :=
               match l with
               | [] => ret []
               | (c', e') :: l' =>
                 e' <- eliminate_expr L e';;
                 l' <- mapM_LD l' ;;
                 ret ((c', e') :: l')
               end) P ;;
      ret (Ecase x P')
    | Ehalt x => ret (Ehalt x)
    | Efun fl e' => ret e
    | Eprim_val x p e' =>
      e'' <- eliminate_expr L e' ;;
      ret (Eprim_val x p e'')
    | Eprim x f ys e' =>
      e'' <- eliminate_expr L e' ;;
      ret (Eprim x f ys e'')
    | Eapp f ft ys =>
      match get_fun_vars L f with
      | Some bs =>
        let ys' := live_args ys bs in
        let ft' := get_fun_tag f in
        ret (Eapp f ft' ys')
      | None => ret (Eapp f ft ys)
      end
    end.

  Fixpoint eliminate_fundefs (L : live_fun) (B : fundefs) : elimM fundefs :=
    match B with
    | Fcons f ft ys e B' =>
      match get_fun_vars L f with
      | Some bs =>
        let ys' := live_args ys bs in
        (* f_str <- get_pp_name f ;; *)
        (* ys_names <- get_pp_names_list ys' ;; *)
        (* ys_or <- get_pp_names_list ys ;; *)
        (* state.log_msg (String.concat " " ["Def Function entry" ; f_str ; "found" ; "id"; cps_show.show_pos f]) ;; *)
        (* state.log_msg (String.concat " " ("Def New params" :: ys_names)) ;; *)
        (* state.log_msg (String.concat " " ("bs" ::  show_bool_list bs :: "Original Params" :: ys_or )) ;; *)
        e' <- eliminate_expr L e ;;
        B'' <- eliminate_fundefs L B' ;;
        let ft' := get_fun_tag f in
        ret (Fcons f ft' ys' e' B'')
      | None =>
        e' <- eliminate_expr L e ;;
        B'' <- eliminate_fundefs L B' ;;
        ret (Fcons f ft ys e' B'')
      end
    | Fnil => ret Fnil
    end.

End Elim.

Require Import MetaRocq.Utils.bytestring.

Definition DPE (e : exp) (c_data : comp_data) : error exp * comp_data :=
  if is_hoisted e then
    match e with
    | Efun B e' =>
      match find_live e with
      | Ret L =>
        let m := make_arityMap e (M.empty _) in
        let '(ftagMap, c_data) := create_fun_tag L m B c_data (M.empty _) in

        match run_compM (eliminate_fundefs ftagMap L B) c_data tt with
        | (Ret B', (c_data, m)) =>
          match run_compM (eliminate_expr ftagMap L e') c_data tt with
          | (Ret e'', (c_data, m)) =>
            (Ret (Efun B' e''), c_data)
          | (Err s, (c_data, m)) => (Err s, c_data)
          end
        | (Err s, (c_data, m)) => (Err s, c_data)
        end
      | Err s => (Ret e, add_log s c_data)
      end
    | e => (Ret e, c_data)
    end
  else (Ret e, add_log "Internal error: program is not hoisted"%bs c_data).
