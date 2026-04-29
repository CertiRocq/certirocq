Require Import Common.compM Common.Pipeline_utils.
From Stdlib Require Import ZArith.ZArith Lists.List micromega.Lia.
Import ListNotations.
Require Import identifiers.
Require Import LambdaANF.state LambdaANF.term_util LambdaANF.cps_show LambdaANF.ctx LambdaANF.uncurry LambdaANF.shrink_cps LambdaANF.rename LambdaANF.inline_letapp LambdaANF.term.
Require Import ExtLib.Structures.Monad.
Require Import ExtLib.Structures.MonadState.
Require Import ExtLib.Data.Monads.StateMonad.
From Stdlib Require Program.Wf.
From Stdlib Require Import Program.
From Stdlib Require Import Structures.OrdersEx.
Require Import MetaRocq.Utils.bytestring.
Import MonadNotation.
Open Scope monad_scope.

Definition r_map := M.t var.

(* St is the type of the state used by the heuristic *)
Record InlineHeuristic (St:Type) :=
  { update_funDef:(fundefs -> r_map -> St -> (St * St)); (* update inlining decision at functions declaraction. First state is used for the body of the program, second for the function definitions *)
    update_inFun:(var -> fun_tag -> list var -> exp -> r_map -> St -> St); (* update inlining decisions when converting a function within a bundle *)
    update_App:(var -> fun_tag -> list var -> St -> (St * bool)); (* update and return inlining decision for f on function application *)
    update_letApp:(var -> fun_tag -> list var -> St -> (St * St * bool)) (* update and return inlining decision for f on let bound function application *)
  }.

Definition fun_map := M.t (fun_tag * list var * exp).

Definition inline_state := (bool * name_env)%type.
(* We keep a state consisting of the old name map and a boolean state to "click"
   when a function is inlined (so that we stop iterating) *)

Definition inlineM : Type -> Type := @compM' inline_state.

Section Inline.

  Variable St:Type.
  (* Pretty print the state for debugging purposes *)
  Variable (pp_St : St -> name_env -> string).
  Variable IH : InlineHeuristic St.

  Variable (max_var : var). (* The maximum reserved variable *)

  Definition click : inlineM unit :=
    '(b, s) <- get_state () ;;
    put_state (true, s).

  Definition get_fresh_name (x : var) :inlineM var :=
    '(_, nenv_old) <- get_state () ;;
    get_name' x "" nenv_old.

  Definition get_fresh_names (xs : list var) :inlineM (list var) :=
    '(_, nenv_old) <- get_state () ;;
    get_names_lst' xs "" nenv_old.


  (* Construct known-functions map *)
  Fixpoint add_fundefs (fds:fundefs) (fm: fun_map) : fun_map :=
    match fds with
    | Fnil => fm
    | Fcons f t xs e fds => M.set f (t, xs, e) (add_fundefs fds fm)
    end.

  Instance OptMonad : Monad option.
  Proof.
    constructor.
    - intros X x. exact (Some x).
    - intros A B [ a | ] f.
      now eauto.
      exact None.
  Defined.

  Definition debug_st (s : St) : inlineM unit :=
    nenv <- get_name_env () ;;
    log_msg (pp_St s nenv);;
    log_msg Pipeline_utils.newline.

  Definition split_fuel d : nat * nat :=
    let d2 := Nat.div2 d in
    (d2, d2 + Nat.b2n (Nat.odd d)).

  Lemma split_fuel_add d :
    d = fst (split_fuel d) + snd (split_fuel d).
  Proof.
    unfold split_fuel. simpl. rewrite (Nat.div2_odd d) at 1. simpl.
    lia.
  Qed.

  Fixpoint inline_exp (d : nat) (j : nat) {struct d} :=
    let fix inline_exp_aux (e : exp) (sig : r_map) (fm:fun_map) (s:St) {struct e} : inlineM exp :=
        match e with
        | Econstr x t ys e =>
          let ys' := apply_r_list sig ys in
          x' <- get_fresh_name x ;;
          e' <- inline_exp_aux e (M.set x x' sig) fm s ;;
          ret (Econstr x' t ys' e')
        | Ecase v cl =>
          let v' := apply_r sig v in
          cl' <- (fix beta_list (br: list (ctor_tag*exp)) : inlineM (list (ctor_tag*exp)) :=
                   match br with
                   | nil => ret ( nil)
                   | (t, e)::br' =>
                     e' <- inline_exp_aux e sig fm s ;;
                     br'' <- beta_list br';;
                     ret ((t, e')::br'')
                   end) cl;;
          ret (Ecase v' cl')
       | Eproj x t n y e =>
         let y' := apply_r sig y in
         x' <- get_fresh_name x ;;
         e' <- inline_exp_aux e (M.set x x' sig) fm s ;;
         ret (Eproj x' t n y' e')
       | Eletapp x f t ys ec =>
         let f' := apply_r sig f in
         let ys' := apply_r_list sig ys in
         let '(s', s'' , inl_dec) := update_letApp _ IH f t ys' s in
         (* fstr <- get_pp_name f' ;; *)
         (* log_msg ("Application of " ++ fstr ++ " is " ++ (if inl_dec then else "not ") ++ "inlined") ;; *)
         (match (inl_dec, M.get f fm, d, j) with
          | (true, Some  (ft, xs, e), S d', S j') =>
            if (Nat.eqb (List.length xs) (List.length ys)) then
              let sig' := set_list (combine xs ys') sig  in
              x' <- get_fresh_name x ;;
              let '(j1, j2) := split_fuel j' in
              e' <- inline_exp d' j1 e sig' (M.remove f fm) s' ;;
              match inline_letapp e' x' with
              | Some (C, x') =>
                click ;;
                ec' <- inline_exp d' j2 ec (M.set x x' sig) fm s'' ;;
                ret (C |[ ec' ]|)
              | _ =>
                x' <- get_fresh_name x ;;
                ec' <- inline_exp_aux ec (M.set x x' sig) fm s' ;;
                ret (Eletapp x' f' t ys' ec')
              end
            else
              x' <- get_fresh_name x ;;
              ec' <- inline_exp_aux ec (M.set x x' sig) fm s' ;;
              ret (Eletapp x' f' t ys' ec')
          | _ =>
            x' <- get_fresh_name x ;;
            ec' <- inline_exp_aux ec (M.set x x' sig) fm s' ;;
            ret (Eletapp x' f' t ys' ec')
          end)
       | Efun fds e =>
         let fm' := add_fundefs fds fm in
         let (s1, s2) := update_funDef _ IH fds sig s in
         let names := all_fun_name fds in
         names' <- get_fresh_names names ;;
         let sig' := set_list (combine names names') sig in
         fds' <- (fix inline_exp_fds (fds:fundefs) (s:St) : inlineM fundefs :=
                   match fds with
                   | Fcons f t xs e fds' =>
                     let s' := update_inFun _ IH f t xs e sig s in
                     let f' := apply_r sig' f in
                     xs' <- get_fresh_names xs ;;
                     e' <- inline_exp_aux e (set_list (combine xs xs') sig') (M.remove f fm') s' ;;
                     fds'' <- inline_exp_fds fds' s ;;
                     ret (Fcons f' t xs' e' fds'')
                   | Fnil => ret Fnil
                   end) fds s1 ;;
         e' <- inline_exp_aux e sig' fm' s2 ;;
         ret (Efun fds' e')
       | Eapp f t ys =>
         let f' := apply_r sig f in
         let ys' := apply_r_list sig ys in
         let (s', inl) := update_App _ IH f t ys' s in
         (* fstr <- get_pp_name f' ;; *)
         (* log_msg ("Application of " ++ fstr ++ " is " ++ (if inl then "" else "not ") ++ "inlined") ;; *)
         (match (inl, M.get f fm, d, j) with
          | (true, Some (ft, xs, e), S d', S j') =>
            if (Nat.eqb (List.length xs) (List.length ys))%bool then
              let sig' := set_list (combine xs ys') sig  in
              click ;;
              inline_exp d' j' e sig' (M.remove f fm) s'
            else
              ret (Eapp f' t ys')
          | _ =>
            ret (Eapp f' t ys')
          end)
       | Eprim_val x p e =>
         x' <- get_fresh_name x ;;
         e' <- inline_exp_aux e (M.set x x' sig) fm s ;;
         ret (Eprim_val x' p e')
       | Eprim x t ys e =>
         let ys' := apply_r_list sig ys in
         x' <- get_fresh_name x ;;
         e' <- inline_exp_aux e (M.set x x' sig) fm s ;;
         ret (Eprim x' t ys' e')
       | Ehalt x =>
         let x' := apply_r sig x in
         ret (Ehalt x')
        end
    in inline_exp_aux.

  (* Since inlining will rename *all* bound variables, we can restart
     the name count, so we dont generate large positive numbers
     resulting in performance bugs *)

  (* We will also create a new name environment, (tha maps vars to
     their string names in the source program) and we will discard the
     old one. But we should keep it around to copy the names to the
     new name map *)

  (* To restart the pool counter, take the max of the max free var and
     the max reserved var *)

  Definition restart_names (e : exp) (c : comp_data) : comp_data * name_env :=
    let fvs := exp_fv e in
    let new_var :=
        match set_util.PS.max_elt fvs with
        | Some v => (Pos.max v max_var + 1)%positive
        | None => (max_var + 1)%positive
        end
    in
    let (_, ct, it, ft, c, f, names, imap,  l) := c in

    (mkCompData new_var ct it ft c f (M.empty _) imap l, names).



  Definition inline_top' (d:nat) (s:St) (e:exp) (c:comp_data) : error exp * comp_data * bool :=
    let (c, nenv) := restart_names e c in
    let '(e', (st', (click, _old_map))) := run_compM (inline_exp d d e (M.empty var) (M.empty _) s) c (false, nenv) in
    (e', st', click).

  Definition inline_top (d:nat) (s:St) (e:exp) (c:comp_data)  : error exp * comp_data :=
    let '(e', st', _click) := inline_top' d s e c in
    (e', st').


  (* Run until nothing changes and call shrink reducer after each pass *)
  Fixpoint inline_loop_aux (fuel : nat) (d:nat) (s:St) (e:exp) (c:comp_data)  : error exp * comp_data :=
    match fuel with
    | 0 => (Ret e, c)
    | S fuel =>
      let '(e', c', click) := inline_top' d s e c in
      match e' with
      | Ret e' =>
        if click then
          inline_loop_aux fuel d s (fst (shrink_cps.shrink_top e')) c'
        else (Ret (fst (shrink_cps.shrink_top e')) , c')
      | Err s => (Err s, c')
      end
    end.

  Definition inline_loop d s e c := inline_loop_aux 1000 d s e c.

End Inline.

(** * Encoding of inline heuristics *)
(* Currently supported heuristics:
   1. Inline uncurry shells
      - By inlinning marked functions from uncurry, OR
      - By looking for the pattern of uncurry shell
   2. Inline small functions
 *)


Definition CombineInlineHeuristic {St1 St2:Type} (deci:bool -> bool -> bool)
           (IH1:InlineHeuristic St1) (IH2:InlineHeuristic St2) : InlineHeuristic (prod St1 St2) :=
  {| update_funDef :=
       fun fds sigma (s:(prod St1 St2)) =>
         let (s1, s2) := s in
         let (s11, s12) := update_funDef _ IH1 fds sigma s1 in
         let (s21, s22) := update_funDef _ IH2 fds sigma s2 in
         ((s11, s21) , (s12, s22));
     update_inFun  :=
       fun (f:var) (t:fun_tag) (xs:list var) (e:exp) (sigma:r_map) (s:_) =>
         let (s1, s2) := s in
         let s1' := update_inFun _ IH1 f t xs e sigma s1 in
         let s2' := update_inFun _ IH2 f t xs e sigma s2 in
         (s1', s2');
     update_App  :=
       fun (f:var) (t:fun_tag) (ys:list var) (s:_) =>
         let (s1, s2) := s in
         let (s1', b1) := update_App _ IH1 f t ys s1 in
         let (s2', b2) := update_App _ IH2 f t ys s2 in
         ((s1', s2'), deci b1 b2 );
     update_letApp  :=
       fun (f:var) (t:fun_tag) (ys:list var) (s:_) =>
         let (s1, s2) := s in
         let '(s1', s1'', b1) := update_letApp _ IH1 f t ys s1 in
         let '(s2', s2'', b2) := update_letApp _ IH2 f t ys s2 in
         ((s1', s2'), (s1'', s2''), deci b1 b2 )|}.

Definition forall_fundefs (f : exp -> bool) : fundefs -> bool :=
  fun fns =>
  let fix aux fns :=
    match fns with
    | Fnil => true
    | Fcons x t xs e tl => (f e && aux tl)%bool
    end
  in aux fns.

(* Don't inline functions with nested function definitions (code duplication)
   and functions with case analysis (to avoid inlining uncurried functions)
   and recursive functions *)

Fixpoint do_inline (f : var) (e : exp) :=
  match e with
  | Econstr _ _ _  e
  | Eproj _ _ _ _ e
  | Eprim_val _ _ e
  | Eprim _ _ _ e => do_inline f e
  | Ecase _ _ => false
  | Efun fns e => (forall_fundefs (do_inline f) fns && do_inline f e)%bool
  | Eletapp _ f' _ _ e => (negb (BinPosDef.Pos.eqb f f') && do_inline f e)%bool
  | Eapp f' _ _ => negb (BinPosDef.Pos.eqb f f')
  | Ehalt _ => true
  end.


Definition InlineSmall (bound:nat): InlineHeuristic (M.t bool) :=
  {| (* Inline small functions, but not inside their body (alternatively, check if they are recursive) *)
    update_funDef  := (fun (fds:fundefs) (sigma:r_map) (s:_) =>
                         let s' :=
                             (fix upd (fds:fundefs) (sigma:r_map) (s:_) :=
                                match fds with
                                | Fcons f t xs e fdc' => if ((term_size e <? bound) && do_inline f e)%bool then
                                                          upd fdc' sigma (M.set f true s)
                                                        else  upd fdc' sigma s
                                | Fnil => s
                                end) fds sigma s in (s', s'));
    update_inFun := fun (f:var) (t:fun_tag) (xs:list var) (e:exp) (sigma:r_map) (s:_) => (M.remove f s);
    update_App := fun (f:var) (t:fun_tag) (ys:list var) (s:_) =>
                    match M.get f s with
                    | Some true => (M.remove f s, true)
                    | _ => (s, false)
                    end;
    update_letApp := fun (f:var) (t:fun_tag) (ys:list var) (s:_) =>
                       match M.get f s with
                       | Some true => (M.remove f s, s, true)
                       | _ => (s, s, false)
                       end;
  |}.

Open Scope positive.

Definition InlinedUncurriedMarked : InlineHeuristic (M.t nat) :=
  {| update_funDef := fun (fds:fundefs) (sigma:r_map) (s:_) => (s, s);
     update_inFun := fun (f:var) (t:fun_tag) (xs:list var) (e:exp) (sigma:r_map) (s:_) => s;
     update_App := fun (f:var) (t:fun_tag) (ys:list var) (s:_) =>
                    match M.get f s with
                    | Some 1%nat => (s, true)
                    | Some 2%nat => (s, true)
                    | _ => (s, false)
                    end;
     update_letApp :=
       fun (f:var) (t:fun_tag) (ys:list var) (s:_) =>
         match M.get f s with
         | Some 1%nat => (s, s, true)
         | Some 2%nat => (s, s, true)
         | _ => (s, s, false)
         end;
  |}.


Fixpoint find_uncurried (fds : fundefs) (s:M.t bool) : M.t bool :=
  match fds with
  | Fcons f t (k::xs) (Efun (Fcons h _ _ _ Fnil) (Eapp k' _ [h'])) fds' =>
    let s' := M.set f true s in
        (* if andb (h =? h') (k =? k') then M.set f true s else s in *)
    find_uncurried fds' s'
  | _ => s
  end.

Definition InineUncurriedPats: InlineHeuristic (M.t bool) :=
  {| update_funDef  := (fun (fds:fundefs) (sigma:r_map) (s:_) =>
                          let s' := find_uncurried fds s in
                          (s', s'));
     update_inFun := fun (f:var) (t:fun_tag) (xs:list var) (e:exp) (sigma:r_map) (s:_) => (M.remove f s);
     update_App := fun (f:var) (t:fun_tag) (ys:list var) (s:_) =>
                     match M.get f s with
                     | Some true => (s, true)
                     | _ => (s, false)
                     end;
     update_letApp := fun (f:var) (t:fun_tag) (ys:list var) (s:_) => (s, s, false)
  |}.


Definition find_uncurried_pats_anf (fds : fundefs) (s:M.t bool) : M.t bool :=
  match fds with
  | Fcons f t xs (Efun (Fcons h ht ys e Fnil) (Ehalt h')) fds' =>
    let s' := if ((h =? h') && negb (occurs_in_exp f (Efun (Fcons h ht ys e Fnil) (Ehalt h'))))%bool then M.set f true s else s in
    find_uncurried fds' s'
  | Fcons f t xs (Eapp f' t' xs') fds' =>
    let s' := if (occurs_in_exp f (Eapp f' t' xs')) then s else M.set f true s in
    find_uncurried fds' s'
  | _ => s
  end.


(* Inlines functions based on patterns found in the code *)
Definition InineUncurriedPatsAnf : InlineHeuristic (M.t bool) :=
  {| update_funDef  := (fun (fds:fundefs) (sigma:r_map) (s:_) =>
                          let s' := find_uncurried_pats_anf fds s in
                          (s', s'));
     update_inFun := fun (f:var) (t:fun_tag) (xs:list var) (e:exp) (sigma:r_map) (s:_) => (M.remove f s);
     update_App := fun (f:var) (t:fun_tag) (ys:list var) (s:_) =>
                     match M.get f s with
                     | Some true => (s, true)
                     | _ => (s, false)
                     end;
     update_letApp := fun (f:var) (t:fun_tag) (ys:list var) (s:_) =>
                        match M.get f s with
                        | Some true => (s, s, true)
                        | _ => (s, s, false)
                        end;
  |}.


(* DEBUGGING *)
Definition show_map {A} (m : M.t A) (nenv : name_env) (str : A -> string) :=
  (let fix show_lst (lst : list (var * A)) :=
      match lst with
      | (x, a) :: lst =>
        (show_tree (show_var nenv x)) ++ " -> " ++ str a ++ "; " ++ show_lst lst
      | [] => ""
      end
   in
   "S{" ++ show_lst (M.elements m) ++ "}")%bs.

Definition show_map_bool m nenv := show_map m nenv (fun (b : bool) => if b then "true" else "false")%bs.
Definition show_map_nat m nenv := show_map m nenv show_nat.


Definition InlineSmallOrUncurried (bound:nat): InlineHeuristic (prod (M.t bool) (M.t nat)) :=
  CombineInlineHeuristic orb (InlineSmall bound) InlinedUncurriedMarked.

Definition inline_uncurry (max_var : var) (bound:nat) (d:nat) (e:exp) (c : comp_data) :=
  let inline_map := inline_map c in
  inline_top _ (InlineSmallOrUncurried bound) max_var d (M.empty _, inline_map) e c.

(* Run after hoisting to eliminate outermost lambdas (e.g, repeat) *)
Definition inline_shrink_loop (max_var : var) (bound:nat) (d:nat) (e:exp) (c : comp_data) :=
  inline_loop _ (InlineSmall bound) max_var d (M.empty _) e c.


(* Inline the calls to known functions from the escaping  wrappers *)
Definition find_indirect_call (f : var) (e : exp) (s:M.t bool) : M.t bool :=
  let b := (fix is_wrapper e :=
              match e with
              | Econstr _ _ _  e
              | Eproj _ _ _ _ e
              | Eprim_val _ _ e
              | Eprim _ _ _ e => is_wrapper e
              | Eletapp _ _ _ _ e => None
              | Ecase _ _
              | Ehalt _
              | Efun _ _ => None
              | Eapp g _ _ => Some g
              (* | _ => None *)
                end) e in
  match b with
  | None => s
  | Some g => M.set g true s
  end.


Definition InineLifted: InlineHeuristic (M.t bool) :=
  {| update_funDef  := (fun (fds:fundefs) (sigma:r_map) (s:_) => (s, s));
     update_inFun := fun (f:var) (t:tag) (xs:list var) (e:exp) (sigma:r_map) (s:_) => (M.remove f (find_indirect_call f e s));
     update_App := fun (f:var) (t:tag) (ys:list var) (s:_) =>
                     match M.get f s with
                     | Some true => (s, true)
                     | _ => (s, false)
                     end;
     update_letApp := fun (f:var) (t:tag) (ys:list var) (s:_) =>
                        match M.get f s with
                        | Some true => (s, s, true)
                        | _ => (s, s, false)
                        end;
  |}.

Definition inline_lifted (max_var : var) (bound:nat) (d:nat) (e:exp) (c : comp_data) :=
  inline_top _ InineLifted max_var d (M.empty bool) e c.

(* "Bogus" inlining. Renames all variables with fresh names but does not inline any function. *)

(* Inlines functions based on patterns found in the code *)
Definition InlineNone: InlineHeuristic unit :=
  {| update_funDef  := fun (fds:fundefs) (sigma:r_map) (s:_) => (tt, tt);
     update_inFun := fun (f:var) (t:fun_tag) (xs:list var) (e:exp) (sigma:r_map) (s:_) => tt;
     update_App := fun (f:var) (t:fun_tag) (ys:list var) (s:_) => (tt, false);
     update_letApp := fun (f:var) (t:fun_tag) (ys:list var) (s:_) => (tt, tt, false);
  |}.

Definition inline_none (max_var : var) (e:exp) (bound:nat) (d:nat) (c : comp_data) :=
  inline_top _ InlineNone max_var d tt e c.

(*
(* Inline the calls to known functions from the escaping  wrappers *)
Fixpoint find_wrappers (fds : fundefs) (s:M.t bool) : M.t bool :=
  match fds with
  | Fcons f _ _ (Eapp g _ _) fds' =>
    (* f immediately calls g -- inline f *)
    let s' := if (f =? g) then s else  M.set f true s in
    find_wrappers fds' s'
  | _ => s
  end.


Definition InineLambdaLifted: InlineHeuristic (M.t bool) :=
  {| update_funDef  := (fun (fds:fundefs) (sigma:r_map) (s:_) =>
                          let s' := find_wrappers fds s in
                          (s', s'));
     update_inFun := fun (f:var) (t:tag) (xs:list var) (e:exp) (sigma:r_map) (s:_) => (M.remove f s);
     update_App := fun (f:var) (t:tag) (ys:list var) (s:_) =>
                     match M.get f s with
                     | Some true => (s, true)
                     | _ => (s, false)
                     end;
     update_letApp := fun (f:var) (t:tag) (ys:list var) (s:_) =>
                        match M.get f s with
                        | Some true => (s, s, true)
                        | _ => (s, s, false)
                        end;
  |}.

Definition inline_lambda_lifted (max_var : var) (e:exp) (s:M.t nat) (bound:nat) (d:nat) (c : comp_data) :=
  inline_top _ InineLambdaLifted max_var e d (M.empty bool) c false.
*)
