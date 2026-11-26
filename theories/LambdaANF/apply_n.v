(* Unknown calls with two arguments in direct style, without the closure in between.
   A function that only builds a closure gets a second entry, kept in its closures. *)

From Stdlib Require Import Lists.List PArith.BinPos NArith.BinNat Arith.PeanoNat Bool.Bool.
Require Import LambdaANF.term LambdaANF.term_util LambdaANF.List_util LambdaANF.state LambdaANF.merge_dup_funs
        LambdaANF.case_inline LambdaANF.freshen.
Require Import Common.compM.
Require Import MetaRocq.Utils.bytestring.

Import ListNotations.

Section ApplyN.

  Context (clo_tag : ctor_tag).

  Local Notation "x <- m ;; k" := (bind m (fun x => k))
                                    (at level 100, m at next level, right associativity).

  Definition fresh_ftag (arity : N) : St fun_tag :=
    fun c =>
      match c with
      | mkCompData x ct it f e fenv names imap log =>
        (f, mkCompData x ct it (Pos.succ f) e
                       (M.set f (arity, fromN 0%N (N.to_nat arity)) fenv) names imap log)
      end.

  (* A second constructor for closures, with three fields *)
  Definition fresh_clo_tag : St ctor_tag :=
    fun c =>
      match c with
      | mkCompData x ct it f e fenv names imap log =>
        let ind := match M.get clo_tag e with
                   | Some info => ctor_ind_tag info
                   | None => it
                   end in
        let info := {| ctor_name := BasicAst.nNamed "clo2"%bs
                     ; ctor_ind_name := BasicAst.nAnon
                     ; ctor_ind_tag := ind
                     ; ctor_arity := 3%N
                     ; ctor_ordinal := 1%N |} in
        (ct, mkCompData x (Pos.succ ct) it f (M.set ct info e) fenv names imap log)
      end.

  Definition mem (x : var) (l : list var) : bool := existsb (Pos.eqb x) l.

  (* [e] with new binders, and its free variables renamed by [s] *)
  Definition freshen (e : exp) (s : M.t var) : St exp :=
    fun c =>
      match run_compM (freshen_term e s) c tt with
      | (Ret e', (c', _)) => (e', c')
      | (Err _, (c', _)) => (e, c')
      end.

  Fixpoint size (e : exp) {struct e} : nat :=
    match e with
    | Econstr _ _ _ k | Eproj _ _ _ _ k | Eletapp _ _ _ _ k | Eprim_val _ _ k
    | Eprim _ _ _ k => S (size k)
    | Ecase _ bs =>
      S ((fix go (bs : list (ctor_tag * exp)) : nat :=
            match bs with
            | [] => 0
            | (_, e') :: bs' => size e' + go bs'
            end) bs)
    | Efun fds k => size_fds fds + size k
    | Eapp _ _ _ | Ehalt _ => 1
    end
  with size_fds (fds : fundefs) {struct fds} : nat :=
    match fds with
    | Fcons _ _ _ e fds' => S (size e + size_fds fds')
    | Fnil => 0
    end.

  (* The largest body that is copied into a second entry *)
  Definition copy_bound : nat := 30.

  (** Functions that only build a closure *)

  (* [h] if the expression projects, builds records and returns the closure of [h] *)
  Fixpoint curry_target (b : exp) {struct b} : option var :=
    match b with
    | Eproj _ _ _ _ k => curry_target k
    | Econstr x c ys k =>
      match k with
      | Ehalt x' =>
        if Pos.eqb c clo_tag && Pos.eqb x x' then
          match ys with
          | [h; _] => Some h
          | _ => None
          end
        else None
      | _ => curry_target k
      end
    | _ => None
    end.

  (* The same expression with new binders, ending with the body of [h] applied
     to the record and to [b2], or with a call of [h] if its body is large *)
  Fixpoint copy (s : M.t var) (b2 : var) (h : var) (ht : fun_tag) (henv hb : var) (hbody : exp)
           (b : exp) {struct b}
    : St exp :=
    match b with
    | Eproj x c n y k =>
      x' <- fresh "p" ;;
      k' <- copy (M.set x x' s) b2 h ht henv hb hbody k ;;
      ret (Eproj x' c n (rn s y) k')
    | Econstr x c ys k =>
      match k with
      | Ehalt _ =>
        match ys with
        | [_; e] =>
          if Nat.leb (size hbody) copy_bound
          then freshen hbody (M.set henv (rn s e) (M.set hb b2 (M.empty var)))
          else ret (Eapp h ht [rn s e; b2])
        | _ => ret b
        end
      | _ =>
        x' <- fresh "env" ;;
        k' <- copy (M.set x x' s) b2 h ht henv hb hbody k ;;
        ret (Econstr x' c (List.map (rn s) ys) k')
      end
    | _ => ret b
    end.

  (* The second entries: a map from [g] to [g2], and the definitions of the [g2] *)
  Fixpoint second_entries (all : fundefs) (t3 : fun_tag) (fds : fundefs) {struct fds}
    : St (M.t var * fundefs) :=
    match fds with
    | Fnil => ret (M.empty var, Fnil)
    | Fcons g t xs body fds' =>
      r <- second_entries all t3 fds' ;;
      let '(w, new) := r in
      match xs, curry_target body with
      | [env; a], Some h =>
        match find_def h all with
        | Some (ht, [henv; hb], hbody) =>
          g2 <- fresh "second" ;;
          env2 <- fresh "env" ;;
          a2 <- fresh "a" ;;
          b2 <- fresh "b" ;;
          body2 <- copy (M.set env env2 (M.set a a2 (M.empty var))) b2 h ht henv hb hbody body ;;
          ret (M.set g g2 w, Fcons g2 t3 [env2; a2; b2] body2 new)
        | _ => ret (w, new)
        end
      | _, _ => ret (w, new)
      end
    end.

  (** Call sites *)

  Definition eq_tag2 (p q : fun_tag * fun_tag) : bool :=
    Pos.eqb (fst p) (fst q) && Pos.eqb (snd p) (snd q).

  Fixpoint assoc {A B} (eq : A -> A -> bool) (x : A) (l : list (A * B)) : option B :=
    match l with
    | [] => None
    | (y, b) :: l' => if eq x y then Some b else assoc eq x l'
    end.

  (* The helpers for unknown calls: for each tag, the number of arguments and the name *)
  Definition helpers := list (fun_tag * (nat * var)).

  (* The tag and the number of arguments for which [g] is the helper *)
  Fixpoint tag_of (g : var) (l : helpers) : option (fun_tag * nat) :=
    match l with
    | [] => None
    | (t, (n, h)) :: l' => if Pos.eqb g h then Some (t, n) else tag_of g l'
    end.

  (* [cd = f.0; en = f.1; g(e1, args)] is a call of the closure [f] *)
  Definition is_call (cd : var) (c : ctor_tag) (n : N) (f : var)
             (en : var) (c' : ctor_tag) (n' : N) (f' : var)
             (g : var) (e1 : var) (args : list var) : bool :=
    Pos.eqb c clo_tag && Pos.eqb c' clo_tag && N.eqb n 0 && N.eqb n' 1 &&
    Pos.eqb f f' && Pos.eqb g cd && Pos.eqb e1 en &&
    negb (mem cd args) && negb (mem en args) && negb (Nat.eqb (length args) 0).

  Section Rewrite.

    Context (w : M.t var)                           (* the functions with a second entry *)
            (c2 : ctor_tag)
            (t3 : fun_tag)
            (ap1 : helpers)
            (ap2 : list (fun_tag * fun_tag * var)).  (* [apply2] for each pair of tags *)

    (* [k] with its call [apply1(y, b)] replaced by [apply2(f, a, b)], if the code
       before it only projects and builds records, and [y] has no other use *)
    Fixpoint merge (ta : fun_tag) (y f a : var) (k : exp) {struct k} : option exp :=
      match k with
      | Eproj x c n z k' =>
        if Pos.eqb z y then None else option_map (Eproj x c n z) (merge ta y f a k')
      | Econstr x c ys k' =>
        if mem y ys then None else option_map (Econstr x c ys) (merge ta y f a k')
      | Eletapp z g t' ys k' =>
        match ys, tag_of g ap1 with
        | [y'; b], Some (tb, _) =>
          if Pos.eqb y' y && negb (Pos.eqb b y) && Nat.eqb (occ y k') 0 then
            match assoc eq_tag2 (ta, tb) ap2 with
            | Some h => Some (Eletapp z h t3 [f; a; b] k')
            | None => None
            end
          else None
        | _, _ => None
        end
      | Eapp g t' ys =>
        match ys, tag_of g ap1 with
        | [y'; b], Some (tb, _) =>
          if Pos.eqb y' y && negb (Pos.eqb b y) then
            match assoc eq_tag2 (ta, tb) ap2 with
            | Some h => Some (Eapp h t3 [f; a; b])
            | None => None
            end
          else None
        | _, _ => None
        end
      | _ => None
      end.

    Fixpoint rw (e : exp) {struct e} : exp :=
      match e with
      | Econstr x c ys k =>
        let k' := rw k in
        if Pos.eqb c clo_tag then
          match ys with
          | [g; en] =>
            match M.get g w with
            | Some g2 => Econstr x c2 [g; en; g2] k'
            | None => Econstr x c ys k'
            end
          | _ => Econstr x c ys k'
          end
        else Econstr x c ys k'
      | Ecase x bs => Ecase x (List.map (fun b => (fst b, rw (snd b))) bs)
      | Eproj cd c n f k1 =>
        match k1 with
        | Eproj en c' n' f' (Eletapp y g t' (e1 :: args) k) =>
          match assoc Pos.eqb t' ap1 with
          | Some (m, h) =>
            if is_call cd c n f en c' n' f' g e1 args && Nat.eqb (length args) m &&
               Nat.eqb (occ cd k) 0 && Nat.eqb (occ en k) 0 then
              let k' := rw k in
              match args with
              | [a] =>
                match merge t' y f a k' with
                | Some e' => e'
                | None => Eletapp y h t' [f; a] k'
                end
              | _ => Eletapp y h t' (f :: args) k'
              end
            else Eproj cd c n f (rw k1)
          | None => Eproj cd c n f (rw k1)
          end
        | Eproj en c' n' f' (Eapp g t' (e1 :: args)) =>
          match assoc Pos.eqb t' ap1 with
          | Some (m, h) =>
            if is_call cd c n f en c' n' f' g e1 args && Nat.eqb (length args) m
            then Eapp h t' (f :: args)
            else Eproj cd c n f (rw k1)
          | None => Eproj cd c n f (rw k1)
          end
        | _ => Eproj cd c n f (rw k1)
        end
      | Eletapp x f ft ys k => Eletapp x f ft ys (rw k)
      | Efun fds k => Efun (rw_fds fds) (rw k)
      | Eapp f ft ys => Eapp f ft ys
      | Eprim_val x p k => Eprim_val x p (rw k)
      | Eprim x p ys k => Eprim x p ys (rw k)
      | Ehalt x => Ehalt x
      end
    with rw_fds (fds : fundefs) {struct fds} : fundefs :=
      match fds with
      | Fcons f ft xs e fds' => Fcons f ft xs (rw e) (rw_fds fds')
      | Fnil => Fnil
      end.

  End Rewrite.

  (* No projection from a closure is left *)
  Fixpoint clean (e : exp) {struct e} : bool :=
    match e with
    | Econstr _ _ _ k => clean k
    | Ecase _ bs => forallb (fun b => clean (snd b)) bs
    | Eproj _ c _ _ k => negb (Pos.eqb c clo_tag) && clean k
    | Eletapp _ _ _ _ k => clean k
    | Efun fds k => clean_fds fds && clean k
    | Eapp _ _ _ => true
    | Eprim_val _ _ k => clean k
    | Eprim _ _ _ k => clean k
    | Ehalt _ => true
    end
  with clean_fds (fds : fundefs) {struct fds} : bool :=
    match fds with
    | Fcons _ _ _ e fds' => clean e && clean_fds fds'
    | Fnil => true
    end.

  Definition add_tag (t : fun_tag) (n : nat) (l : list (fun_tag * nat)) : list (fun_tag * nat) :=
    if existsb (fun p => Pos.eqb t (fst p)) l then l else (t, n) :: l.

  (* The tags of the unknown calls, with their number of arguments *)
  Fixpoint site_tags (e : exp) (acc : list (fun_tag * nat)) {struct e} : list (fun_tag * nat) :=
    match e with
    | Econstr _ _ _ k => site_tags k acc
    | Ecase _ bs =>
      (fix go (bs : list (ctor_tag * exp)) (acc : list (fun_tag * nat)) : list (fun_tag * nat) :=
         match bs with
         | [] => acc
         | (_, e') :: bs' => go bs' (site_tags e' acc)
         end) bs acc
    | Eproj cd c n f k1 =>
      match k1 with
      | Eproj en c' n' f' (Eletapp _ g t' (e1 :: args) k) =>
        if is_call cd c n f en c' n' f' g e1 args then site_tags k (add_tag t' (length args) acc)
        else site_tags k1 acc
      | Eproj en c' n' f' (Eapp g t' (e1 :: args)) =>
        if is_call cd c n f en c' n' f' g e1 args then add_tag t' (length args) acc else acc
      | _ => site_tags k1 acc
      end
    | Eletapp _ _ _ _ k => site_tags k acc
    | Efun fds k => site_tags k (site_tags_fds fds acc)
    | Eapp _ _ _ => acc
    | Eprim_val _ _ k => site_tags k acc
    | Eprim _ _ _ k => site_tags k acc
    | Ehalt _ => acc
    end
  with site_tags_fds (fds : fundefs) (acc : list (fun_tag * nat)) {struct fds}
       : list (fun_tag * nat) :=
    match fds with
    | Fcons _ _ _ e fds' => site_tags_fds fds' (site_tags e acc)
    | Fnil => acc
    end.

  (** The helper functions *)

  (* [code = f.0; env = f.1; code(env, args)] for a closure with tag [c] *)
  Definition callk (c : ctor_tag) (t : fun_tag) (f : var) (args : list var) : St exp :=
    cd <- fresh "code" ;;
    en <- fresh "env" ;;
    ret (Eproj cd c 0%N f (Eproj en c 1%N f (Eapp cd t (en :: args)))).

  Definition both (c2 : ctor_tag) (t : fun_tag) (f : var) (args : list var) : St exp :=
    e1 <- callk clo_tag t f args ;;
    e2 <- callk c2 t f args ;;
    ret (Ecase f [(clo_tag, e1); (c2, e2)]).

  (* A call of a helper whose result is returned is replaced by its body *)
  Fixpoint expand_tail (c2 : ctor_tag) (ap1 : helpers) (e : exp) {struct e} : St exp :=
    match e with
    | Econstr x c ys k => k' <- expand_tail c2 ap1 k ;; ret (Econstr x c ys k')
    | Ecase x bs =>
      bs' <- (fix go (bs : list (ctor_tag * exp)) : St (list (ctor_tag * exp)) :=
                match bs with
                | [] => ret []
                | (c, e') :: bs' =>
                  e'' <- expand_tail c2 ap1 e' ;;
                  bs'' <- go bs' ;;
                  ret ((c, e'') :: bs'')
                end) bs ;;
      ret (Ecase x bs')
    | Eproj x c n y k => k' <- expand_tail c2 ap1 k ;; ret (Eproj x c n y k')
    | Eletapp x f ft ys k => k' <- expand_tail c2 ap1 k ;; ret (Eletapp x f ft ys k')
    | Efun fds k =>
      fds' <- expand_tail_fds c2 ap1 fds ;;
      k' <- expand_tail c2 ap1 k ;;
      ret (Efun fds' k')
    | Eapp g ft ys =>
      match ys, tag_of g ap1 with
      | f :: args, Some (t, _) => both c2 t f args
      | _, _ => ret e
      end
    | Eprim_val x p k => k' <- expand_tail c2 ap1 k ;; ret (Eprim_val x p k')
    | Eprim x p ys k => k' <- expand_tail c2 ap1 k ;; ret (Eprim x p ys k')
    | Ehalt x => ret e
    end
  with expand_tail_fds (c2 : ctor_tag) (ap1 : helpers) (fds : fundefs) {struct fds}
       : St fundefs :=
    match fds with
    | Fcons f ft xs e fds' =>
      e' <- expand_tail c2 ap1 e ;;
      fds'' <- expand_tail_fds c2 ap1 fds' ;;
      ret (Fcons f ft xs e' fds'')
    | Fnil => ret Fnil
    end.

  Fixpoint fresh_list (n : nat) : St (list var) :=
    match n with
    | O => ret []
    | S n' => x <- fresh "a" ;; xs <- fresh_list n' ;; ret (x :: xs)
    end.

  Definition apply1_def (c2 : ctor_tag) (t : fun_tag) (n : nat) (h : var) : St fundefs :=
    f <- fresh "f" ;;
    args <- fresh_list n ;;
    body <- both c2 t f args ;;
    ret (Fcons h t (f :: args) body Fnil).

  (* [h1] is the helper for the tag [tb] *)
  Definition apply2_def (c2 : ctor_tag) (ta tb t3 : fun_tag) (h1 h : var) : St fundefs :=
    f <- fresh "f" ;;
    a <- fresh "a" ;;
    b <- fresh "b" ;;
    cd <- fresh "code" ;;
    en <- fresh "env" ;;
    y <- fresh "y" ;;
    cd2 <- fresh "code" ;;
    en2 <- fresh "env" ;;
    let slow := Eproj cd clo_tag 0%N f
                      (Eproj en clo_tag 1%N f
                             (Eletapp y cd ta [en; a] (Eapp h1 tb [y; b]))) in
    let fast := Eproj cd2 c2 2%N f (Eproj en2 c2 1%N f (Eapp cd2 t3 [en2; a; b])) in
    ret (Fcons h t3 [f; a; b] (Ecase f [(clo_tag, slow); (c2, fast)]) Fnil).

  Fixpoint make_apply1 (c2 : ctor_tag) (ts : list (fun_tag * nat)) : St (helpers * fundefs) :=
    match ts with
    | [] => ret ([], Fnil)
    | (t, n) :: ts' =>
      r <- make_apply1 c2 ts' ;;
      h <- fresh "apply" ;;
      d <- apply1_def c2 t n h ;;
      ret ((t, (n, h)) :: fst r, fundefs_append d (snd r))
    end.

  Fixpoint make_apply2 (c2 : ctor_tag) (t3 : fun_tag)
           (pairs : list ((fun_tag * (nat * var)) * (fun_tag * (nat * var))))
    : St (list (fun_tag * fun_tag * var) * fundefs) :=
    match pairs with
    | [] => ret ([], Fnil)
    | ((ta, _), (tb, (_, h1))) :: pairs' =>
      r <- make_apply2 c2 t3 pairs' ;;
      h <- fresh "apply2" ;;
      d <- apply2_def c2 ta tb t3 h1 h ;;
      ret ((ta, tb, h) :: fst r, fundefs_append d (snd r))
    end.

  Fixpoint all_pairs {A B} (l : list A) (l' : list B) : list (A * B) :=
    match l with
    | [] => []
    | x :: l0 => (List.map (fun y => (x, y)) l' ++ all_pairs l0 l')%list
    end.

  Definition apply_n (e : exp) : St exp :=
    match e with
    | Efun fds main =>
      match site_tags e [] with
      | [] => ret e
      | ts =>
        c2 <- fresh_clo_tag ;;
        t3 <- fresh_ftag 3%N ;;
        r1 <- make_apply1 c2 ts ;;
        let '(ap1, d1) := r1 in
        let one := List.filter (fun p => Nat.eqb (fst (snd p)) 1) ap1 in
        r2 <- make_apply2 c2 t3 (all_pairs one one) ;;
        let '(ap2, d2) := r2 in
        r <- second_entries fds t3 fds ;;
        let '(w, new) := r in
        let fds' := rw_fds w c2 t3 ap1 ap2 fds in
        let main' := rw w c2 t3 ap1 ap2 main in
        if clean_fds fds' && clean main' then
          fds'' <- expand_tail_fds c2 ap1 fds' ;;
          main'' <- expand_tail c2 ap1 main' ;;
          ret (Efun (fundefs_append d1 (fundefs_append d2 (fundefs_append new fds''))) main'')
        else ret e
      end
    | _ => ret e
    end.

End ApplyN.
