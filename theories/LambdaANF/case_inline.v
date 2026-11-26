(* Replaces the function that the ANF conversion makes for a [match] in tail position
   by the case. *)

From Stdlib Require Import Lists.List PArith.BinPos Arith.PeanoNat Bool.Bool.
Require Import LambdaANF.term LambdaANF.term_util LambdaANF.state LambdaANF.merge_dup_funs.
Require Import MetaRocq.Utils.bytestring.

Import ListNotations.

Section Occurrences.

  Definition occ_list (y : var) (xs : list var) : nat :=
    length (List.filter (Pos.eqb y) xs).

  (* The number of uses of [y] in [e] *)
  Fixpoint occ (y : var) (e : exp) {struct e} : nat :=
    match e with
    | Econstr _ _ ys k => occ_list y ys + occ y k
    | Ecase x bs =>
      occ_list y [x] +
      (fix go (bs : list (ctor_tag * exp)) : nat :=
         match bs with
         | [] => 0
         | (_, e') :: bs' => occ y e' + go bs'
         end) bs
    | Eproj _ _ _ z k => occ_list y [z] + occ y k
    | Eletapp _ f _ ys k => occ_list y (f :: ys) + occ y k
    | Efun fds k => occ_fds y fds + occ y k
    | Eapp f _ ys => occ_list y (f :: ys)
    | Eprim_val _ _ k => occ y k
    | Eprim _ _ ys k => occ_list y ys + occ y k
    | Ehalt x => occ_list y [x]
    end
  with occ_fds (y : var) (fds : fundefs) {struct fds} : nat :=
    match fds with
    | Fcons _ _ _ e fds' => occ y e + occ_fds y fds'
    | Fnil => 0
    end.

End Occurrences.

Section CaseInline.

  Definition St (A : Type) : Type := comp_data -> A * comp_data.
  Definition ret {A} (a : A) : St A := fun c => (a, c).
  Definition bind {A B} (m : St A) (f : A -> St B) : St B :=
    fun c => let (a, c') := m c in f a c'.

  Local Notation "x <- m ;; k" := (bind m (fun x => k))
                                    (at level 100, m at next level, right associativity).

  Definition fresh (name : string) : St var :=
    fun c =>
      match c with
      | mkCompData n ct it ft cenv fenv names imap log =>
        (n, mkCompData (Pos.succ n) ct it ft cenv fenv (add_entry_str names n name) imap log)
      end.

  (* Finds [Eletapp r f [x] (Ehalt r)] on the spine of [e] and replaces it by the case.
     [None] if it is not there. *)
  Fixpoint replace_call (f : var) (s : var) (t : fun_tag) (brs : list (ctor_tag * exp))
           (e : exp) {struct e} : St (option exp) :=
    let under (mk : exp -> exp) (k : exp) : St (option exp) :=
        r <- replace_call f s t brs k ;;
        ret (option_map mk r) in
    match e with
    | Econstr x c ys k => under (Econstr x c ys) k
    | Eproj x c n y k => under (Eproj x c n y) k
    | Eprim_val x p k => under (Eprim_val x p) k
    | Eprim x p ys k => under (Eprim x p ys) k
    | Efun fds k => under (Efun fds) k
    | Eletapp r g gt ys k =>
      if Pos.eqb g f then
        match ys with
        | [x] =>
          let case := Ecase x (List.map (fun b => (fst b, rename_exp (M.set s x (M.empty var)) (snd b))) brs) in
          match k with
          | Ehalt r' => if Pos.eqb r r' then ret (Some case) else ret None
          | _ => ret None
          end
        | _ => ret None
        end
      else under (Eletapp r g gt ys) k
    | Ecase _ _ | Eapp _ _ _ | Ehalt _ => ret None
    end.

  Fixpoint inline_case (e : exp) {struct e} : St exp :=
    match e with
    | Econstr x c ys k => k' <- inline_case k ;; ret (Econstr x c ys k')
    | Ecase x bs =>
      bs' <- (fix go (bs : list (ctor_tag * exp)) : St (list (ctor_tag * exp)) :=
                match bs with
                | [] => ret []
                | (c, e') :: bs' =>
                  e'' <- inline_case e' ;;
                  bs'' <- go bs' ;;
                  ret ((c, e'') :: bs'')
                end) bs ;;
      ret (Ecase x bs')
    | Eproj x c n y k => k' <- inline_case k ;; ret (Eproj x c n y k')
    | Eletapp x f ft ys k => k' <- inline_case k ;; ret (Eletapp x f ft ys k')
    | Efun fds k =>
      fds' <- inline_case_fds fds ;;
      k' <- inline_case k ;;
      match fds' with
      | Fcons f t [s] (Ecase s' brs) Fnil =>
        if Pos.eqb s s' && Nat.eqb (occ f (Ecase s' brs)) 0 && Nat.eqb (occ f k') 1 then
          r <- replace_call f s t brs k' ;;
          match r with
          | Some e' => ret e'
          | None => ret (Efun fds' k')
          end
        else ret (Efun fds' k')
      | _ => ret (Efun fds' k')
      end
    | Eapp f ft ys => ret (Eapp f ft ys)
    | Eprim_val x p k => k' <- inline_case k ;; ret (Eprim_val x p k')
    | Eprim x p ys k => k' <- inline_case k ;; ret (Eprim x p ys k')
    | Ehalt x => ret (Ehalt x)
    end
  with inline_case_fds (fds : fundefs) {struct fds} : St fundefs :=
    match fds with
    | Fcons f t xs e fds' =>
      e' <- inline_case e ;;
      fds'' <- inline_case_fds fds' ;;
      ret (Fcons f t xs e' fds'')
    | Fnil => ret Fnil
    end.

End CaseInline.

(* [Eletapp y f ys (Ehalt y)] becomes [Eapp f ys], which the inliner can replace by
   any function body *)
Fixpoint tail_calls (e : exp) {struct e} : exp :=
  match e with
  | Econstr x c ys k => Econstr x c ys (tail_calls k)
  | Ecase x bs => Ecase x (List.map (fun b => (fst b, tail_calls (snd b))) bs)
  | Eproj x c n y k => Eproj x c n y (tail_calls k)
  | Eletapp y f t ys k =>
    match k with
    | Ehalt y' => if Pos.eqb y y' then Eapp f t ys else Eletapp y f t ys k
    | _ => Eletapp y f t ys (tail_calls k)
    end
  | Efun fds k => Efun (tail_calls_fds fds) (tail_calls k)
  | Eapp f t ys => Eapp f t ys
  | Eprim_val x p k => Eprim_val x p (tail_calls k)
  | Eprim x p ys k => Eprim x p ys (tail_calls k)
  | Ehalt x => Ehalt x
  end
with tail_calls_fds (fds : fundefs) {struct fds} : fundefs :=
  match fds with
  | Fcons f t xs e fds' => Fcons f t xs (tail_calls e) (tail_calls_fds fds')
  | Fnil => Fnil
  end.
