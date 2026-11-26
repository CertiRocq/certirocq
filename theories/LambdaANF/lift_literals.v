(* Data built inside a function from constructors only, with no variable of the
   function, is built once at the start of the program instead. *)

From Stdlib Require Import Lists.List PArith.BinPos Bool.Bool.
Require Import LambdaANF.term LambdaANF.state.

Import ListNotations.

Section LiftLiterals.

  Record lifted : Type :=
    { bindings : list (var * ctor_tag * list var);  (* the lifted data, last one first *)
      lits : M.t unit;                              (* the variables bound to lifted data *)
      consts : M.t ctor_tag;                        (* the variables bound to a constant *)
      next : var }.                                 (* the next unused variable *)

  Definition L (A : Type) : Type := lifted -> A * lifted.
  Definition ret {A} (a : A) : L A := fun s => (a, s).
  Definition bind {A B} (m : L A) (f : A -> L B) : L B :=
    fun s => let (a, s') := m s in f a s'.

  Local Notation "x <- m ;; k" := (bind m (fun x => k))
                                    (at level 100, m at next level, right associativity).

  Definition closed (s : lifted) (x : var) : bool :=
    match M.get x (lits s), M.get x (consts s) with
    | None, None => false
    | _, _ => true
    end.

  (* The arguments of lifted data: a constant gets a copy at the start of the program *)
  Fixpoint lift_args (ys : list var) (s : lifted) : list var * lifted :=
    match ys with
    | [] => ([], s)
    | y :: ys' =>
      match M.get y (lits s), M.get y (consts s) with
      | None, Some c =>
        let y' := next s in
        let s' := {| bindings := (y', c, []) :: bindings s; lits := lits s;
                     consts := consts s; next := Pos.succ y' |} in
        let (zs, s'') := lift_args ys' s' in
        (y' :: zs, s'')
      | _, _ =>
        let (zs, s') := lift_args ys' s in
        (y :: zs, s')
      end
    end.

  (* [inside]: in the body of a function *)
  Fixpoint lift (inside : bool) (e : exp) {struct e} : L exp :=
    match e with
    | Econstr x c ys k =>
      fun s =>
        match ys with
        | [] =>
          let s' := {| bindings := bindings s; lits := lits s;
                       consts := M.set x c (consts s); next := next s |} in
          let (k', s'') := lift inside k s' in
          (Econstr x c ys k', s'')
        | _ =>
          if inside && forallb (closed s) ys then
            let (ys', s') := lift_args ys s in
            lift inside k {| bindings := (x, c, ys') :: bindings s'; lits := M.set x tt (lits s');
                             consts := consts s'; next := next s' |}
          else let (k', s') := lift inside k s in (Econstr x c ys k', s')
        end
    | Ecase x bs =>
      bs' <- (fix go (bs : list (ctor_tag * exp)) : L (list (ctor_tag * exp)) :=
                match bs with
                | [] => ret []
                | (c, e') :: bs' =>
                  e'' <- lift inside e' ;;
                  bs'' <- go bs' ;;
                  ret ((c, e'') :: bs'')
                end) bs ;;
      ret (Ecase x bs')
    | Eproj x c n y k => k' <- lift inside k ;; ret (Eproj x c n y k')
    | Eletapp x f t ys k => k' <- lift inside k ;; ret (Eletapp x f t ys k')
    | Efun fds k =>
      fds' <- lift_fds fds ;;
      k' <- lift inside k ;;
      ret (Efun fds' k')
    | Eapp f t ys => ret e
    | Eprim_val x p k => k' <- lift inside k ;; ret (Eprim_val x p k')
    | Eprim x p ys k => k' <- lift inside k ;; ret (Eprim x p ys k')
    | Ehalt x => ret e
    end
  with lift_fds (fds : fundefs) {struct fds} : L fundefs :=
    match fds with
    | Fcons f t xs e fds' =>
      e' <- lift true e ;;
      fds'' <- lift_fds fds' ;;
      ret (Fcons f t xs e' fds'')
    | Fnil => ret Fnil
    end.

  Definition lift_literals (e : exp) (c : comp_data) : exp * comp_data :=
    match c with
    | mkCompData n ct it ft cenv fenv names imap log =>
      let (e', s) := lift false e {| bindings := []; lits := M.empty unit;
                                     consts := M.empty ctor_tag; next := n |} in
      (fold_left (fun k b => let '(x, c, ys) := b in Econstr x c ys k) (bindings s) e',
       mkCompData (next s) ct it ft cenv fenv names imap log)
    end.

End LiftLiterals.
