(* A constant [c(x) = b], where [b] ignores [x] and only builds data and functions, is
   evaluated once where it is defined. Inside a function, only if [b] builds no data. *)

From Stdlib Require Import Lists.List PArith.BinPos Arith.PeanoNat Bool.Bool.
Require Import LambdaANF.term LambdaANF.merge_dup_funs LambdaANF.case_inline.

Import ListNotations.

Section Unthunk.

  (* [e] only builds data and functions, and returns a variable. With [data = false]
     it builds no data. *)
  Fixpoint cheap (data : bool) (e : exp) {struct e} : bool :=
    match e with
    | Econstr _ _ ys k =>
      match ys with
      | [] => cheap data k
      | _ => data && cheap data k
      end
    | Eprim_val _ _ k => data && cheap data k
    | Eproj _ _ _ _ k | Efun _ k => cheap data k
    | Ehalt _ => true
    | _ => false
    end.

  (* [e] with [k v] in place of its final [Ehalt v] *)
  Fixpoint splice (e : exp) (k : var -> exp) {struct e} : exp :=
    match e with
    | Econstr x c ys e' => Econstr x c ys (splice e' k)
    | Eproj x c n y e' => Eproj x c n y (splice e' k)
    | Eprim_val x p e' => Eprim_val x p (splice e' k)
    | Efun fds e' => Efun fds (splice e' k)
    | Ehalt v => k v
    | _ => e
    end.

  Fixpoint result (e : exp) {struct e} : option var :=
    match e with
    | Econstr _ _ _ k | Eproj _ _ _ _ k | Eprim_val _ _ k | Efun _ k => result k
    | Ehalt v => Some v
    | _ => None
    end.

  (* [top]: not inside a function.  [vals]: the value of each constant.
     [s]: the results of removed calls. *)
  Fixpoint unthunk (top : bool) (vals s : M.t var) (e : exp) {struct e} : exp :=
    match e with
    | Econstr x c ys k => Econstr x c (List.map (rn s) ys) (unthunk top vals s k)
    | Ecase x bs => Ecase (rn s x) (List.map (fun b => (fst b, unthunk top vals s (snd b))) bs)
    | Eproj x c n y k => Eproj x c n (rn s y) (unthunk top vals s k)
    | Eletapp y g t ys k =>
      match M.get (rn s g) vals with
      | Some v => unthunk top vals (M.set y v s) k
      | None => Eletapp y (rn s g) t (List.map (rn s) ys) (unthunk top vals s k)
      end
    | Efun fds k =>
      match fds with
      | Fcons c t [x] body Fnil =>
        let body' := unthunk false vals s body in
        match result body' with
        | Some v =>
          if cheap top body' && Nat.eqb (occ x body') 0 && Nat.eqb (occ c body') 0 then
            splice body' (fun v => Efun (Fcons c t [x] (Ehalt v) Fnil)
                                        (unthunk top (M.set c v vals) s k))
          else Efun (Fcons c t [x] body' Fnil) (unthunk top vals s k)
        | None => Efun (Fcons c t [x] body' Fnil) (unthunk top vals s k)
        end
      | _ => Efun (unthunk_fds top vals s fds) (unthunk top vals s k)
      end
    | Eapp g t ys =>
      match M.get (rn s g) vals with
      | Some v => Ehalt v
      | None => Eapp (rn s g) t (List.map (rn s) ys)
      end
    | Eprim_val x p k => Eprim_val x p (unthunk top vals s k)
    | Eprim x p ys k => Eprim x p (List.map (rn s) ys) (unthunk top vals s k)
    | Ehalt x => Ehalt (rn s x)
    end
  with unthunk_fds (top : bool) (vals s : M.t var) (fds : fundefs) {struct fds} : fundefs :=
    match fds with
    | Fcons f t xs e fds' => Fcons f t xs (unthunk false vals s e) (unthunk_fds top vals s fds')
    | Fnil => Fnil
    end.

End Unthunk.
