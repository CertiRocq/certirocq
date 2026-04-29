(* Freshen the names in a term by renaming its bound variables to be unique positives starting from a given positive, except for a finite number of positives *)

Require Import Common.compM LambdaANF.term.
From Stdlib Require Import ZArith.ZArith Lists.List.
Import ListNotations.
Require Import ExtLib.Structures.Monad.
Require Import ExtLib.Structures.MonadState.
Require Import ExtLib.Data.Monads.StateMonad.
Require Import LambdaANF.term_util LambdaANF.term_util LambdaANF.cps_show LambdaANF.state.
Require Import MetaRocq.Utils.bytestring.
Open Scope monad_scope.
Import MonadNotation.

Definition freshM : Type -> Type := @compM' unit.

(* TODO: move apply_r and apply_r_list to term_util, and all_fun_name (and proofs) to identifiers *)
(* after freshen_term e sigma curr l = e', curr', l', BV(e') are in interval [curr, curr'[ and disjoint from l *)

(* XXX Copied temporarily from shrink_cps. Probably move to common file *)
Definition apply_r sigma y :=
  match (@M.get M.elt y sigma) with
    | Some v => v
    | None => y
  end.

Definition apply_r_list sigma ys :=
  map (apply_r sigma) ys.

Fixpoint all_fun_name (fds:fundefs) : list var :=
  match fds with
    | Fcons f t ys e fds' => f::(all_fun_name fds')
    | Fnil => []
  end.


Fixpoint freshen_term (e:exp) (sigma:M.t positive) : freshM exp :=
  match e with
  | Econstr x t ys e =>
    x' <- get_name x "";;
    let ys' := apply_r_list sigma ys in
    e' <- freshen_term e (M.set x x' sigma) ;;
    ret (Econstr x' t ys' e')
  | Ecase v cl =>
    cl' <- (fix alpha_list (pats: list (ctor_tag*exp)) : freshM (list (ctor_tag*exp)) :=
             match pats with
             | nil => ret nil
             | pat::pats =>
               let '(t, e) := pat in
               e' <- freshen_term e sigma ;;
               pats' <- alpha_list pats ;;
               ret ((t, e')::pats')
             end) cl ;;
     ret (Ecase (apply_r sigma v) cl')
  | Eproj x t n y e =>
    x' <- get_name x "" ;;
    let y' := apply_r sigma y in
    e' <- freshen_term e (M.set x x' sigma) ;;
    ret (Eproj x' t n y' e')
  | Eletapp x f ft ys e =>
    x' <- get_name x "" ;;
    let f' := apply_r sigma f in
    let ys' := apply_r_list sigma ys in
    e' <- freshen_term e (M.set x x' sigma) ;;
    ret (Eletapp x' f' ft ys' e')
  | Efun fds e =>
    let f_names := all_fun_name fds in
    f_names' <- get_names_lst f_names "" ;;
    (match @set_lists var f_names f_names' sigma with
     | Some sigma' =>
       fds' <- freshen_fun fds sigma' ;;
       e' <- freshen_term e sigma' ;;
       ret (Efun fds' e')
     | None => (* unreachable *)
       ret (Efun Fnil e)
     end)
  | Eapp f t ys =>
    let f' := apply_r sigma f  in
    let ys' := apply_r_list sigma ys in
    ret (Eapp f' t ys')
  | Eprim_val x p e =>
    x' <- get_name x "" ;;
    e' <- freshen_term e (M.set x x' sigma) ;;
    ret (Eprim_val x' p e')
  | Eprim x t ys e =>
    x' <- get_name x "" ;;
    let ys' := apply_r_list sigma ys in
    e' <- freshen_term e (M.set x x' sigma) ;;
    ret (Eprim x' t ys' e')
  | Ehalt x =>
    let x' := apply_r sigma x in
    ret (Ehalt x')
  end
with freshen_fun (fds:fundefs) (sigma:M.t positive) : freshM fundefs :=
       match fds with
       | Fcons f t xs e fds =>
         let f' := apply_r sigma f in
         xs' <- get_names_lst xs "" ;;
         (match @set_lists var xs xs' sigma with
          | Some sigma' =>
            e' <- freshen_term e sigma' ;;
            fds' <- freshen_fun fds sigma ;;
            ret (Fcons f' t xs' e' fds')
          | None => (* unreachable *)
            ret Fnil
          end)
       | Fnil => ret Fnil
       end.


Definition freshen_top (e: exp) (c: comp_data) : error exp * comp_data :=
  let '(e', (st', _)) := run_compM (freshen_term e (M.empty _)) c tt in
  (e', st').


(* Some unit tests *)
Definition test :=
  (Efun (Fcons 1 2 [3] (Ehalt 3) Fnil)
  (Efun (Fcons 1 2 [3] (Ehalt 3) Fnil) (Ehalt 1)))%positive.

Definition dummy_tag := 1%positive.
Definition c := pack_data 10%positive dummy_tag dummy_tag dummy_tag  (M.empty _) (M.empty _) (M.empty _) (M.empty _) [].

(* Definition testf := Eval native_compute in (freshen_top test c). *)

(* Definition test2 := *)
(*   (Econstr 1 2 [3; 4] (Econstr 1 2 [3; 4] (Ehalt 1)))%positive. *)

(* Definition testf2 := Eval native_compute in (freshen_top test2 c). *)
