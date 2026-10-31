From Stdlib Require Import Lists.List NArith.BinNat PArith.BinPos.
Require Import LambdaANF.term.

(** Merge alpha-equivalent closed top-level functions, after hoisting. Erasure implements
    every [□] as its own copy of [fix reccall _ := reccall]; this keeps a single copy.
    TODO: prove [merge_dup_funs] correct. *)
Section MergeDupFuns.

  Local Open Scope bool_scope.

  Definition rn (σ : M.t var) (x : var) : var :=
    match M.get x σ with Some y => y | None => x end.

  Fixpoint rename_exp (σ : M.t var) (e : exp) {struct e} : exp :=
    match e with
    | Econstr x c ys k => Econstr x c (List.map (rn σ) ys) (rename_exp σ k)
    | Ecase x bs => Ecase (rn σ x) (List.map (fun b => (fst b, rename_exp σ (snd b))) bs)
    | Eproj x c n y k => Eproj x c n (rn σ y) (rename_exp σ k)
    | Eletapp x f t ys k => Eletapp x (rn σ f) t (List.map (rn σ) ys) (rename_exp σ k)
    | Efun fds k => Efun (rename_fds σ fds) (rename_exp σ k)
    | Eapp f t ys => Eapp (rn σ f) t (List.map (rn σ) ys)
    | Eprim_val x p k => Eprim_val x p (rename_exp σ k)
    | Eprim x p ys k => Eprim x p (List.map (rn σ) ys) (rename_exp σ k)
    | Ehalt x => Ehalt (rn σ x)
    end
  with rename_fds (σ : M.t var) (fds : fundefs) {struct fds} : fundefs :=
    match fds with
    | Fcons f t xs e fds' => Fcons f t xs (rename_exp σ e) (rename_fds σ fds')
    | Fnil => Fnil
    end.

  (* Lazy conjunction: [b] is evaluated only when [a] is true. Unlike [&&], this also holds
     in code compiled by CertiRocq itself, where both arguments of [andb] are evaluated. *)
  Local Notation "a &&& b" := (if a then b else false) (at level 40, left associativity).

  Section AlphaEq.

    (* Compares the body of [f1] with the body of [f2], with [f1] renamed to [f2]. *)
    Context (f1 f2 : var).

    (* Bound variables are compared up to a bijection: [σ] maps left binders to right
       ones, [ρ] back. Free variables must be equal, after renaming [f1] to [f2]. *)
    Definition var_eqb (σ ρ : M.t var) (x y : var) : bool :=
      match M.get x σ, M.get y ρ with
      | Some y', Some x' => Pos.eqb y' y &&& Pos.eqb x' x
      | None, None => Pos.eqb (if Pos.eqb x f1 then f2 else x) y
      | _, _ => false
      end.

    Fixpoint vars_eqb (σ ρ : M.t var) (xs ys : list var) : bool :=
      match xs, ys with
      | nil, nil => true
      | x :: xs, y :: ys => var_eqb σ ρ x y &&& vars_eqb σ ρ xs ys
      | _, _ => false
      end.

    Fixpoint exp_alpha_eqb (σ ρ : M.t var) (e1 e2 : exp) {struct e1} : bool :=
      match e1, e2 with
      | Econstr x1 c1 ys1 k1, Econstr x2 c2 ys2 k2 =>
        Pos.eqb c1 c2 &&& vars_eqb σ ρ ys1 ys2 &&&
        exp_alpha_eqb (M.set x1 x2 σ) (M.set x2 x1 ρ) k1 k2
      | Ecase x1 bs1, Ecase x2 bs2 =>
        var_eqb σ ρ x1 x2 &&&
        (fix go (bs1 bs2 : list (ctor_tag * exp)) : bool :=
           match bs1, bs2 with
           | nil, nil => true
           | (c1, b1) :: bs1, (c2, b2) :: bs2 =>
             Pos.eqb c1 c2 &&& exp_alpha_eqb σ ρ b1 b2 &&& go bs1 bs2
           | _, _ => false
           end) bs1 bs2
      | Eproj x1 c1 n1 y1 k1, Eproj x2 c2 n2 y2 k2 =>
        Pos.eqb c1 c2 &&& N.eqb n1 n2 &&& var_eqb σ ρ y1 y2 &&&
        exp_alpha_eqb (M.set x1 x2 σ) (M.set x2 x1 ρ) k1 k2
      | Eletapp x1 g1 t1 ys1 k1, Eletapp x2 g2 t2 ys2 k2 =>
        var_eqb σ ρ g1 g2 &&& Pos.eqb t1 t2 &&& vars_eqb σ ρ ys1 ys2 &&&
        exp_alpha_eqb (M.set x1 x2 σ) (M.set x2 x1 ρ) k1 k2
      | Eapp g1 t1 ys1, Eapp g2 t2 ys2 =>
        var_eqb σ ρ g1 g2 &&& Pos.eqb t1 t2 &&& vars_eqb σ ρ ys1 ys2
      | Eprim x1 p1 ys1 k1, Eprim x2 p2 ys2 k2 =>
        Pos.eqb p1 p2 &&& vars_eqb σ ρ ys1 ys2 &&&
        exp_alpha_eqb (M.set x1 x2 σ) (M.set x2 x1 ρ) k1 k2
      | Ehalt x1, Ehalt x2 => var_eqb σ ρ x1 x2
      | _, _ => false (* [Efun] and [Eprim_val] are conservatively treated as distinct *)
      end.

  End AlphaEq.

  (* Size of a function body, used to group candidates for merging. *)
  Fixpoint exp_size (e : exp) : positive :=
    match e with
    | Econstr _ _ _ k | Eproj _ _ _ _ k | Eletapp _ _ _ _ k
    | Eprim_val _ _ k | Eprim _ _ _ k | Efun _ k => Pos.succ (exp_size k)
    | Ecase _ bs =>
      (fix go (bs : list (ctor_tag * exp)) : positive :=
         match bs with
         | nil => 1%positive
         | (_, b) :: bs => Pos.add (exp_size b) (go bs)
         end) bs
    | Eapp _ _ _ | Ehalt _ => 1%positive
    end.

  (* The functions a body references. Bodies that are equal up to renaming reference the
     same functions, except that references of [f] to itself may correspond to references
     to the other function. [funs] are the top-level function names. *)
  Section Refs.

    Context (funs : M.t unit) (f : var).

    Definition is_fun (x : var) : bool :=
      match M.get x funs with Some _ => true | None => false end.

    (* Local variables and [f] itself weigh 1; other functions are told apart by name. *)
    Definition ref_weight (x : var) : positive :=
      if is_fun x then (if Pos.eqb x f then 1%positive else Pos.succ x) else 1%positive.

    Definition vars_weight (xs : list var) : positive :=
      fold_left (fun w x => Pos.add w (ref_weight x)) xs 1%positive.

    Fixpoint exp_refs (e : exp) : positive :=
      match e with
      | Econstr _ _ ys k | Eprim _ _ ys k => Pos.add (vars_weight ys) (exp_refs k)
      | Eproj _ _ _ y k => Pos.add (ref_weight y) (exp_refs k)
      | Eletapp _ g _ ys k => Pos.add (Pos.add (ref_weight g) (vars_weight ys)) (exp_refs k)
      | Eprim_val _ _ k | Efun _ k => exp_refs k
      | Ecase x bs =>
        (fix go (bs : list (ctor_tag * exp)) : positive :=
           match bs with
           | nil => ref_weight x
           | (_, b) :: bs => Pos.add (exp_refs b) (go bs)
           end) bs
      | Eapp g _ ys => Pos.add (ref_weight g) (vars_weight ys)
      | Ehalt x => ref_weight x
      end.

    (* The other top-level functions that a body references. *)
    Definition add_callees (xs : list var) (acc : list var) : list var :=
      fold_left (fun acc x => if is_fun x then (if Pos.eqb x f then acc else x :: acc) else acc)
                xs acc.

    Fixpoint exp_callees (e : exp) (acc : list var) : list var :=
      match e with
      | Econstr _ _ ys k | Eprim _ _ ys k => exp_callees k (add_callees ys acc)
      | Eproj _ _ _ y k => exp_callees k (add_callees (y :: nil) acc)
      | Eletapp _ g _ ys k => exp_callees k (add_callees (g :: ys) acc)
      | Eprim_val _ _ k | Efun _ k => exp_callees k acc
      | Ecase x bs =>
        (fix go (bs : list (ctor_tag * exp)) (acc : list var) : list var :=
           match bs with
           | nil => add_callees (x :: nil) acc
           | (_, b) :: bs => go bs (exp_callees b acc)
           end) bs acc
      | Eapp g _ ys => add_callees (g :: ys) acc
      | Ehalt x => add_callees (x :: nil) acc
      end.

  End Refs.

  Definition fundef : Type := var * fun_tag * list var * exp.

  Fixpoint fds_to_list (fds : fundefs) : list fundef :=
    match fds with
    | Fcons f t xs e fds' => (f, t, xs, e) :: fds_to_list fds'
    | Fnil => nil
    end.

  Fixpoint list_to_fds (l : list fundef) : fundefs :=
    match l with
    | (f, t, xs, e) :: l' => Fcons f t xs e (list_to_fds l')
    | nil => Fnil
    end.

  Fixpoint bind_vars (σ : M.t var) (xs ys : list var) : M.t var :=
    match xs, ys with
    | x :: xs, y :: ys => bind_vars (M.set x y σ) xs ys
    | _, _ => σ
    end.

  (* [f1] can be replaced by [f2] if they have the same tag and arity, and the body of
     [f1], with [f1] renamed to [f2], is alpha-equivalent to the body of [f2]. *)
  Definition fundef_eqb (d1 d2 : fundef) : bool :=
    let '(f1, t1, xs1, e1) := d1 in
    let '(f2, t2, xs2, e2) := d2 in
    Pos.eqb t1 t2 &&& Nat.eqb (length xs1) (length xs2) &&&
    exp_alpha_eqb f1 f2 (bind_vars (M.empty _) xs1 xs2) (bind_vars (M.empty _) xs2 xs1) e1 e2.

  Definition fundef_name (d : fundef) : var := let '(f, _, _, _) := d in f.

  Fixpoint find_dup (d : fundef) (reps : list fundef) : option var :=
    match reps with
    | nil => None
    | r :: reps => if fundef_eqb d r then Some (fundef_name r) else find_dup d reps
    end.

  (* Candidates are grouped by function tag and a fingerprint of the body: its size and the
     functions it references, so that each function is only compared with its group. *)
  Definition buckets : Type := M.t (M.t (list fundef)).

  Definition fingerprint (funs : M.t unit) (d : fundef) : positive :=
    let '(f, _, _, e) := d in
    Pos.add (Pos.mul (exp_refs funs f e) 65536%positive) (exp_size e).

  Definition get_bucket (t : fun_tag) (n : positive) (bs : buckets) : list fundef :=
    match M.get t bs with
    | Some m => match M.get n m with Some l => l | None => nil end
    | None => nil
    end.

  Definition add_to_bucket (t : fun_tag) (n : positive) (d : fundef) (bs : buckets) : buckets :=
    let m := match M.get t bs with Some m => m | None => M.empty _ end in
    M.set t (M.set n (d :: get_bucket t n bs) m) bs.

  (* Compare [d] with the kept functions it references. This finds the matches whose
     fingerprint differs: [d]'s body references [g] where [g]'s body references itself. *)
  Fixpoint find_callee (d : fundef) (gs : list var) (keptm : M.t fundef) : option var :=
    match gs with
    | nil => None
    | g :: gs =>
      match M.get g keptm with
      | Some r => if fundef_eqb d r then Some g else find_callee d gs keptm
      | None => find_callee d gs keptm
      end
    end.

  (* Keep the first function of each equivalence class and map the others to it. *)
  Fixpoint merge_list (funs : M.t unit) (l kept : list fundef) (bs : buckets)
           (keptm : M.t fundef) (σ : M.t var) : list fundef * M.t var :=
    match l with
    | nil => (List.rev kept, σ)
    | d :: l =>
      let '(f, t, _, e) := d in
      let n := fingerprint funs d in
      match find_callee d (exp_callees funs f e nil) keptm with
      | Some g => merge_list funs l kept bs keptm (M.set f g σ)
      | None =>
        match find_dup d (get_bucket t n bs) with
        | Some g => merge_list funs l kept bs keptm (M.set f g σ)
        | None => merge_list funs l (d :: kept) (add_to_bucket t n d bs) (M.set f d keptm) σ
        end
      end
    end.

  (* Iterate, since merging functions can make the functions that use them identical. *)
  Fixpoint merge_dup_funs (fuel : nat) (e : exp) : exp :=
    match fuel, e with
    | S fuel, Efun fds k =>
      let l := fds_to_list fds in
      let funs := fold_left (fun m d => M.set (fundef_name d) tt m) l (M.empty _) in
      let '(kept, σ) := merge_list funs l nil (M.empty _) (M.empty _) (M.empty _) in
      if Nat.eqb (length kept) (length l) then e
      else merge_dup_funs fuel (Efun (rename_fds σ (list_to_fds kept)) (rename_exp σ k))
    | _, _ => e
    end.

End MergeDupFuns.
