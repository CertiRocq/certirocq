(* Copies a recursive function for a known function argument that it passes unchanged. *)

From Stdlib Require Import Lists.List PArith.BinPos NArith.BinNat Arith.PeanoNat Bool.Bool.
Require Import LambdaANF.term LambdaANF.term_util LambdaANF.state LambdaANF.case_inline
        LambdaANF.apply_n.
Require Import MetaRocq.Utils.bytestring.

Import ListNotations.

Section Specialize.

  (* The largest body that is copied *)
  Context (bound : nat).

  Local Notation "x <- m ;; k" := (bind m (fun x => k))
                                    (at level 100, m at next level, right associativity).

  Definition mem (x : var) (l : list var) : bool := existsb (Pos.eqb x) l.

  (* Every use of [g] is a call with [n] arguments, the one number [i] being [xi] *)
  Definition good_call (g : var) (n i : nat) (xi : var) (f : var) (ys : list var) : bool :=
    negb (mem g ys) &&
    (if Pos.eqb f g then
       Nat.eqb (length ys) n &&
       match nth_error ys i with
       | Some y => Pos.eqb y xi
       | None => false
       end
     else true).

  Fixpoint invariant (g : var) (n i : nat) (xi : var) (e : exp) {struct e} : bool :=
    match e with
    | Econstr _ _ ys k => negb (mem g ys) && invariant g n i xi k
    | Ecase x bs =>
      negb (Pos.eqb x g) &&
      (fix go (bs : list (ctor_tag * exp)) : bool :=
         match bs with
         | [] => true
         | (_, e') :: bs' => invariant g n i xi e' && go bs'
         end) bs
    | Eproj _ _ _ y k => negb (Pos.eqb y g) && invariant g n i xi k
    | Eletapp _ f _ ys k => good_call g n i xi f ys && invariant g n i xi k
    | Efun fds k => invariant_fds g n i xi fds && invariant g n i xi k
    | Eapp f _ ys => good_call g n i xi f ys
    | Eprim_val _ _ k => invariant g n i xi k
    | Eprim _ _ ys k => negb (mem g ys) && invariant g n i xi k
    | Ehalt x => negb (Pos.eqb x g)
    end
  with invariant_fds (g : var) (n i : nat) (xi : var) (fds : fundefs) {struct fds} : bool :=
    match fds with
    | Fcons _ _ _ e fds' => invariant g n i xi e && invariant_fds g n i xi fds'
    | Fnil => true
    end.

  Fixpoint remove_nth {A} (i : nat) (l : list A) : list A :=
    match l, i with
    | [], _ => []
    | _ :: l', O => l'
    | x :: l', S i' => x :: remove_nth i' l'
    end.

  (* The calls of [g'] lose their argument number [i] *)
  Fixpoint drop_arg (g' : var) (t' : fun_tag) (i : nat) (e : exp) {struct e} : exp :=
    match e with
    | Econstr x c ys k => Econstr x c ys (drop_arg g' t' i k)
    | Ecase x bs => Ecase x (List.map (fun b => (fst b, drop_arg g' t' i (snd b))) bs)
    | Eproj x c n y k => Eproj x c n y (drop_arg g' t' i k)
    | Eletapp x f ft ys k =>
      if Pos.eqb f g' then Eletapp x f t' (remove_nth i ys) (drop_arg g' t' i k)
      else Eletapp x f ft ys (drop_arg g' t' i k)
    | Efun fds k => Efun (drop_arg_fds g' t' i fds) (drop_arg g' t' i k)
    | Eapp f ft ys => if Pos.eqb f g' then Eapp f t' (remove_nth i ys) else e
    | Eprim_val x p k => Eprim_val x p (drop_arg g' t' i k)
    | Eprim x p ys k => Eprim x p ys (drop_arg g' t' i k)
    | Ehalt x => e
    end
  with drop_arg_fds (g' : var) (t' : fun_tag) (i : nat) (fds : fundefs) {struct fds} : fundefs :=
    match fds with
    | Fcons f ft xs e fds' => Fcons f ft xs (drop_arg g' t' i e) (drop_arg_fds g' t' i fds')
    | Fnil => Fnil
    end.

  (* The single functions in scope, and all the function names in scope *)
  Definition defs := M.t (fun_tag * list var * exp).
  Definition known := M.t unit.

  (* The first parameter that gets a known function and is passed unchanged *)
  Fixpoint pick (kn : known) (g : var) (n : nat) (body : exp) (i : nat) (xs ys : list var)
    : option (nat * var * var) :=
    match xs, ys with
    | x :: xs', y :: ys' =>
      match M.get y kn with
      | Some _ =>
        if negb (Pos.eqb y g) && invariant g n i x body then Some (i, x, y)
        else pick kn g n body (S i) xs' ys'
      | None => pick kn g n body (S i) xs' ys'
      end
    | _, _ => None
    end.

  Fixpoint set_list (xs ys : list var) (s : M.t var) : M.t var :=
    match xs, ys with
    | x :: xs', y :: ys' => set_list xs' ys' (M.set x y s)
    | _, _ => s
    end.

  (* The copy, its name, its tag and the remaining arguments *)
  Definition spec_call (dm : defs) (kn : known) (g : var) (ys : list var)
    : St (option (fundefs * var * fun_tag * list var)) :=
    match M.get g dm with
    | Some (_, xs, body) =>
      if Nat.eqb (length xs) (length ys) && Nat.leb (size body) bound then
        match pick kn g (length xs) body 0 xs ys with
        | Some (i, xi, h) =>
          g' <- fresh "spec" ;;
          t' <- fresh_ftag (N.of_nat (length xs - 1)) ;;
          xs' <- fresh_list (length xs - 1) ;;
          let s := M.set g g' (M.set xi h (set_list (remove_nth i xs) xs' (M.empty var))) in
          body' <- freshen body s ;;
          ret (Some (Fcons g' t' xs' (drop_arg g' t' i body') Fnil, g', t', remove_nth i ys))
        | None => ret None
        end
      else ret None
    | None => ret None
    end.

  Fixpoint add_names (fds : fundefs) (kn : known) : known :=
    match fds with
    | Fcons f _ _ _ fds' => add_names fds' (M.set f tt kn)
    | Fnil => kn
    end.

  Fixpoint spec (dm : defs) (kn : known) (e : exp) {struct e} : St exp :=
    match e with
    | Econstr x c ys k => k' <- spec dm kn k ;; ret (Econstr x c ys k')
    | Ecase x bs =>
      bs' <- (fix go (bs : list (ctor_tag * exp)) : St (list (ctor_tag * exp)) :=
                match bs with
                | [] => ret []
                | (c, e') :: bs' =>
                  e'' <- spec dm kn e' ;;
                  bs'' <- go bs' ;;
                  ret ((c, e'') :: bs'')
                end) bs ;;
      ret (Ecase x bs')
    | Eproj x c n y k => k' <- spec dm kn k ;; ret (Eproj x c n y k')
    | Eletapp x g t ys k =>
      k' <- spec dm kn k ;;
      r <- spec_call dm kn g ys ;;
      match r with
      | Some (d, g', t', ys') => ret (Efun d (Eletapp x g' t' ys' k'))
      | None => ret (Eletapp x g t ys k')
      end
    | Efun fds k =>
      let kn' := add_names fds kn in
      let dm' := match fds with
                 | Fcons g t xs b Fnil => M.set g (t, xs, b) dm
                 | _ => dm
                 end in
      fds' <- spec_fds dm' kn' fds ;;
      k' <- spec dm' kn' k ;;
      ret (Efun fds' k')
    | Eapp g t ys =>
      r <- spec_call dm kn g ys ;;
      match r with
      | Some (d, g', t', ys') => ret (Efun d (Eapp g' t' ys'))
      | None => ret e
      end
    | Eprim_val x p k => k' <- spec dm kn k ;; ret (Eprim_val x p k')
    | Eprim x p ys k => k' <- spec dm kn k ;; ret (Eprim x p ys k')
    | Ehalt x => ret e
    end
  with spec_fds (dm : defs) (kn : known) (fds : fundefs) {struct fds} : St fundefs :=
    match fds with
    | Fcons f t xs e fds' =>
      e' <- spec dm kn e ;;
      fds'' <- spec_fds dm kn fds' ;;
      ret (Fcons f t xs e' fds'')
    | Fnil => ret Fnil
    end.

  Definition specialize (e : exp) : St exp := spec (M.empty _) (M.empty _) e.

End Specialize.
