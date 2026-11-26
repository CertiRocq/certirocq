(* For functions defined with an induction principle, such as [Pos.eq_dec]: moves the
   recursive call next to its use and gives the function the parameter of its result. *)

From Stdlib Require Import Lists.List PArith.BinPos Arith.PeanoNat Bool.Bool.
Require Import LambdaANF.term LambdaANF.term_util LambdaANF.state LambdaANF.case_inline.
Require Import MetaRocq.Utils.bytestring.

Import ListNotations.

Section Sink.

  (* The uses of [y] in [e] that are not inside a function defined in [e] *)
  Fixpoint top_occ (y : var) (e : exp) {struct e} : nat :=
    match e with
    | Econstr _ _ ys k => occ_list y ys + top_occ y k
    | Ecase x bs =>
      occ_list y [x] +
      (fix go (bs : list (ctor_tag * exp)) : nat :=
         match bs with
         | [] => 0
         | (_, e') :: bs' => top_occ y e' + go bs'
         end) bs
    | Eproj _ _ _ z k => occ_list y [z] + top_occ y k
    | Eletapp _ f _ ys k => occ_list y (f :: ys) + top_occ y k
    | Efun _ k => top_occ y k
    | Eapp f _ ys => occ_list y (f :: ys)
    | Eprim_val _ _ k => top_occ y k
    | Eprim _ _ ys k => occ_list y ys + top_occ y k
    | Ehalt x => occ_list y [x]
    end.

  (* [y] is only used as the function of a call *)
  Fixpoint only_called (y : var) (e : exp) {struct e} : bool :=
    match e with
    | Econstr _ _ ys k => Nat.eqb (occ_list y ys) 0 && only_called y k
    | Ecase x bs =>
      negb (Pos.eqb x y) &&
      (fix go (bs : list (ctor_tag * exp)) : bool :=
         match bs with
         | [] => true
         | (_, e') :: bs' => only_called y e' && go bs'
         end) bs
    | Eproj _ _ _ z k => negb (Pos.eqb z y) && only_called y k
    | Eletapp _ _ _ ys k => Nat.eqb (occ_list y ys) 0 && only_called y k
    | Efun fds k => only_called_fds y fds && only_called y k
    | Eapp _ _ ys => Nat.eqb (occ_list y ys) 0
    | Eprim_val _ _ k => only_called y k
    | Eprim _ _ ys k => Nat.eqb (occ_list y ys) 0 && only_called y k
    | Ehalt x => negb (Pos.eqb x y)
    end
  with only_called_fds (y : var) (fds : fundefs) {struct fds} : bool :=
    match fds with
    | Fcons _ _ _ e fds' => only_called y e && only_called_fds y fds'
    | Fnil => true
    end.

  (* Puts the binding [b] of [y] right before the expression that uses [y] *)
  Fixpoint place (y : var) (b : exp -> exp) (e : exp) {struct e} : exp :=
    match e with
    | Econstr x c ys k =>
      if Nat.eqb (occ_list y ys) 0 then Econstr x c ys (place y b k) else b e
    | Ecase x bs =>
      if Pos.eqb x y then b e
      else Ecase x ((fix go (bs : list (ctor_tag * exp)) : list (ctor_tag * exp) :=
                       match bs with
                       | [] => []
                       | (c, e') :: bs' => (c, place y b e') :: go bs'
                       end) bs)
    | Eproj x c n z k => if Pos.eqb z y then b e else Eproj x c n z (place y b k)
    | Eletapp x f ft ys k =>
      if Nat.eqb (occ_list y (f :: ys)) 0 then Eletapp x f ft ys (place y b k) else b e
    | Efun fds k => Efun (place_fds y b fds) (place y b k)
    | Eapp f _ ys => if Nat.eqb (occ_list y (f :: ys)) 0 then e else b e
    | Eprim_val x p k => Eprim_val x p (place y b k)
    | Eprim x p ys k =>
      if Nat.eqb (occ_list y ys) 0 then Eprim x p ys (place y b k) else b e
    | Ehalt x => if Pos.eqb x y then b e else e
    end
  with place_fds (y : var) (b : exp -> exp) (fds : fundefs) {struct fds} : fundefs :=
    match fds with
    | Fcons f t xs e fds' => Fcons f t xs (place y b e) (place_fds y b fds')
    | Fnil => Fnil
    end.

  Definition mem (x : var) (l : list var) : bool := existsb (Pos.eqb x) l.

  Fixpoint names (fds : fundefs) : list var :=
    match fds with
    | Fcons f _ _ _ fds' => f :: names fds'
    | Fnil => []
    end.

  (* [anc]: the functions whose body contains the expression *)
  Fixpoint sink (anc : list var) (e : exp) {struct e} : exp :=
    match e with
    | Econstr x c ys k => Econstr x c ys (sink anc k)
    | Ecase x bs =>
      Ecase x ((fix go (bs : list (ctor_tag * exp)) : list (ctor_tag * exp) :=
                  match bs with
                  | [] => []
                  | (c, e') :: bs' => (c, sink anc e') :: go bs'
                  end) bs)
    | Eproj x c n y k => Eproj x c n y (sink anc k)
    | Eletapp y f ft ys k =>
      let k' := sink anc k in
      if mem f anc && Nat.eqb (occ y k') 1 && Nat.eqb (top_occ y k') 0 && only_called y k'
      then place y (Eletapp y f ft ys) k'
      else Eletapp y f ft ys k'
    | Efun fds k => Efun (sink_fds (names fds ++ anc) fds) (sink anc k)
    | Eapp f ft ys => Eapp f ft ys
    | Eprim_val x p k => Eprim_val x p (sink anc k)
    | Eprim x p ys k => Eprim x p ys (sink anc k)
    | Ehalt x => Ehalt x
    end
  with sink_fds (anc : list var) (fds : fundefs) {struct fds} : fundefs :=
    match fds with
    | Fcons f t xs e fds' => Fcons f t xs (sink anc e) (sink_fds anc fds')
    | Fnil => Fnil
    end.

End Sink.

Section Eta.

  Local Notation "x <- m ;; k" := (bind m (fun x => k))
                                    (at level 100, m at next level, right associativity).

  (* The functions in scope, with their tag and number of parameters *)
  Definition fun_map := M.t (fun_tag * nat).

  Fixpoint add_funs (fds : fundefs) (m : fun_map) : fun_map :=
    match fds with
    | Fcons f t xs _ fds' => add_funs fds' (M.set f (t, length xs) m)
    | Fnil => m
    end.

  (* The tag of the one-parameter functions that [e] returns in every branch, if [e]
     only projects, branches and defines functions. The boolean tells if it branches. *)
  Fixpoint returned_tag (m : fun_map) (e : exp) {struct e} : option (fun_tag * bool) :=
    match e with
    | Eproj _ _ _ _ k => returned_tag m k
    | Econstr _ _ [] k => returned_tag m k
    | Efun fds k => returned_tag (add_funs fds m) k
    | Ecase _ bs =>
      (fix go (bs : list (ctor_tag * exp)) (acc : option fun_tag) : option (fun_tag * bool) :=
         match bs with
         | [] => match acc with
                 | Some t => Some (t, true)
                 | None => None
                 end
         | (_, e') :: bs' =>
           match returned_tag m e' with
           | Some (t, _) =>
             match acc with
             | Some t' => if Pos.eqb t t' then go bs' acc else None
             | None => go bs' (Some t)
             end
           | None => None
           end
         end) bs None
    | Ehalt h =>
      match M.get h m with
      | Some (t, 1) => Some (t, false)
      | _ => None
      end
    | _ => None
    end.

  (* Every returned function is called with [x] *)
  Fixpoint apply_result (t : fun_tag) (x : var) (e : exp) {struct e} : exp :=
    match e with
    | Eproj y c n z k => Eproj y c n z (apply_result t x k)
    | Econstr y c ys k => Econstr y c ys (apply_result t x k)
    | Efun fds k => Efun fds (apply_result t x k)
    | Ecase y bs => Ecase y (List.map (fun b => (fst b, apply_result t x (snd b))) bs)
    | Ehalt h => Eapp h t [x]
    | _ => e
    end.

  Fixpoint eta (m : fun_map) (e : exp) {struct e} : St exp :=
    match e with
    | Econstr x c ys k => k' <- eta m k ;; ret (Econstr x c ys k')
    | Ecase x bs =>
      bs' <- (fix go (bs : list (ctor_tag * exp)) : St (list (ctor_tag * exp)) :=
                match bs with
                | [] => ret []
                | (c, e') :: bs' =>
                  e'' <- eta m e' ;;
                  bs'' <- go bs' ;;
                  ret ((c, e'') :: bs'')
                end) bs ;;
      ret (Ecase x bs')
    | Eproj x c n y k => k' <- eta m k ;; ret (Eproj x c n y k')
    | Eletapp x f ft ys k => k' <- eta m k ;; ret (Eletapp x f ft ys k')
    | Efun fds k =>
      let m' := add_funs fds m in
      fds' <- eta_fds m' fds ;;
      k' <- eta m' k ;;
      ret (Efun fds' k')
    | Eapp f ft ys => ret (Eapp f ft ys)
    | Eprim_val x p k => k' <- eta m k ;; ret (Eprim_val x p k')
    | Eprim x p ys k => k' <- eta m k ;; ret (Eprim x p ys k')
    | Ehalt x => ret (Ehalt x)
    end
  with eta_fds (m : fun_map) (fds : fundefs) {struct fds} : St fundefs :=
    match fds with
    | Fcons f t xs e fds' =>
      e' <- eta m e ;;
      fds'' <- eta_fds m fds' ;;
      match returned_tag m e' with
      | Some (t', true) =>
        g <- fresh "eta" ;;
        x <- fresh "x" ;;
        ret (Fcons f t xs (Efun (Fcons g t' [x] (apply_result t' x e') Fnil) (Ehalt g)) fds'')
      | _ => ret (Fcons f t xs e' fds'')
      end
    | Fnil => ret Fnil
    end.

End Eta.
