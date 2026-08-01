Require Import MetaRocq.Utils.bytestring.
Open Scope bs_scope.
Import String.

Infix "+++" := append (at level 60, right associativity).

From Stdlib Require Import Lists.List.
Import ListNotations.

From MetaRocq Require Import Template.All.
Import MonadNotation.
Module TM := MetaRocq.Utils.monad_utils.

From ExtLib.Core Require Import RelDec.
From ExtLib.Data Require Import Nat List Option Pair String.
From ExtLib.Structures Require Import Monoid Functor Applicative Monads Traversable.
From ExtLib.Data.Monads Require Import IdentityMonad EitherMonad StateMonad.

From Stdlib Require Import NArith.BinNat.
Local Open Scope N_scope.

From Stdlib Require Import Relations.Relations.

Require Import Ltac2.Ltac2.
Import Ltac2.Notations.
Set Default Proof Mode "Ltac2".

(* Set Universe Polymorphism. *)

Require Export CertiRocq.LambdaANF.Frame.

Notation "'let!' x ':=' c1 'in' c2" := (@bind _ _ _ _ c1 (fun x => c2))
  (at level 61, c1 at next level, right associativity).
Notation "'let!' ' p ':=' c1 'in' c2" :=
  (@bind _ _ _ _ c1 (fun x => match x with p => c2 end))
  (at level 61, p pattern, c1 at next level, right associativity).
Infix "<$>" := fmap (at level 52, left associativity).
Infix "<*>" := ap (at level 52, left associativity).

Section Helpers.

Context {M : Type -> Type} {A B : Type} `{Monad M}.

Definition mapM (f : A -> M B) : list A -> M (list B) :=
  fix go xs :=
    match xs with
    | [] => pure []
    | x :: xs => pure cons <*> f x <*> go xs
    end.

Definition mapi' (f : nat -> A -> B) : list A -> list B :=
  (fix go n xs :=
    match xs with
    | [] => []
    | x :: xs => f n x :: go (S n) xs
    end) O.

Definition mapiM (f : N -> A -> M B) : list A -> M (list B) :=
  (fix go n xs :=
    match xs with
    | [] => pure []
    | x :: xs => pure cons <*> f n x <*> go (1 + n) xs
    end) 0.

Definition mapiM_nat (f : nat -> A -> M B) : list A -> M (list B) :=
  (fix go n xs :=
    match xs with
    | [] => pure []
    | x :: xs => pure cons <*> f n x <*> go (S n) xs
    end) O.

Definition foldrM (f : A -> B -> M B) (e : B) (xs : list A) : M B :=
  fold_right (fun x m => let! y := m in f x y) (ret e) xs.

Definition foldlM (f : B -> A -> M B) (x : B) : list A -> M B :=
  let fix go acc xs :=
    match xs with
    | [] => ret acc
    | x :: xs =>
      let! acc := f acc x in
      go acc xs
    end
  in go x.

Definition foldri {A B} (f : N -> A -> B -> B) (g : N -> B) : list A -> B :=
  let fix go n xs :=
    match xs with
    | [] => g n
    | x :: xs => f n x (go (1 + n) xs)
    end
  in go 0.

Definition foldri_nat {A B} (f : nat -> A -> B -> B) (g : nat -> B) : list A -> B :=
  let fix go n xs :=
    match xs with
    | [] => g n
    | x :: xs => f n x (go (S n) xs)
    end
  in go O.

Definition foldli (f : N -> B -> A -> B) (x : B) : list A -> B :=
  let fix go n acc xs :=
    match xs with
    | [] => acc
    | x :: xs =>
      let acc := f n acc x in
      go (1 + n) acc xs
    end
  in go 0 x.

Definition foldriM (f : N -> A -> B -> M B) (x : B) : list A -> M B :=
  let fix go n xs :=
    match xs with
    | [] => ret x
    | x :: xs => let! y := go (1 + n) xs in f n x y
    end
  in go 0.

Definition foldriM_nat (f : nat -> A -> B -> M B) (x : B) : list A -> M B :=
  let fix go n xs :=
    match xs with
    | [] => ret x
    | x :: xs => let! y := go (S n) xs in f n x y
    end
  in go O.

Definition foldliM (f : N -> B -> A -> M B) (x : B) : list A -> M B :=
  let fix go n acc xs :=
    match xs with
    | [] => ret acc
    | x :: xs =>
      let! acc := f n acc x in
      go (1 + n) acc xs
    end
  in go 0 x.

End Helpers.

(* -------------------- Finite maps -------------------- *)

Notation "'Eq' A" := (RelDec (@eq A)) (at level 1, no associativity).
Infix "==?" := eq_dec (at level 40, no associativity).

#[export] Instance Eq_N : Eq N := {rel_dec := N.eqb}.
#[export] Instance Eq_kername : Eq kername := {rel_dec := eq_kername}.

Definition Map A B := list (A * B).
Definition Set' A := Map A unit.

Definition empty {A B} : Map A B := [].

Definition sing {A B} k v : Map A B := [(k, v)].

Definition size {A B} (m : Map A B) : nat := #|m|.

Definition insert {A B} k v m : Map A B := (k, v) :: m.

Definition delete {A B} `{Eq A} k : Map A B -> Map A B :=
 filter (fun '(k', _) => negb (k ==? k')).

Fixpoint find {A B} `{Eq A} k m : option B :=
  match m with
  | [] => None
  | (k', v) :: m => if k ==? k' then Some v else find k m
  end.

Fixpoint find_d {A B} `{Eq A} k d m : B :=
  match m with
  | [] => d
  | (k', v) :: m => if k ==? k' then v else find_d k d m
  end.

Definition find_exc {M E A B} `{Eq A} `{Monad M} `{MonadExc E M} k m e : M B :=
  match find k m with
  | Some v => ret v
  | None => raise e
  end.

Definition update {A B} `{Eq A} k (f : B -> B) d m : Map A B :=
  insert k (f (find_d k d m)) m.

Definition list_of_map {A B} : Map A B -> list (A * B) := id.

Definition map_of_list {A B} : list (A * B) -> Map A B := id.
Definition set_of_list {A} (xs : list A) : Set' A := map_of_list (map (fun x => (x, tt)) xs).
Definition list_of_set {A} : Set' A -> list A := map fst.
Definition set_of_option {A} (x : option A) : Set' A :=
  match x with
  | Some x => sing x tt
  | None => empty
  end.

Definition map_of_ilist {A} : list A -> Map N A :=
  let fix go n xs :=
    match xs with
    | [] => []
    | x :: xs => (n, x) :: go (1 + n) xs
    end
  in go 0.

Definition subset {A B} `{Eq A} `{Eq B} (m1 m2 : Map A B) : bool :=
  forallb
    (fun '(k1, v1) =>
       existsb
         (fun '(k2, v2) =>
            if k1 ==? k2
            then v1 ==? v2
            else false)
         m2)
    m1.

Definition mmap {A B C} (f : B -> C) : Map A B -> Map A C :=
  fix go m :=
    match m with
    | [] => []
    | (k, x) :: m => (k, f x) :: go m
    end.

Definition mkmap {A B C} (f : A -> B -> C) : Map A B -> Map A C :=
  fix go m :=
    match m with
    | [] => []
    | (k, x) :: m => (k, f k x) :: go m
    end.

Definition mfold {A B C} (f : A -> B -> C -> C) (e : C) : Map A B -> C :=
  fix go m :=
    match m with
    | [] => e
    | (k, x) :: m => f k x (go m)
    end.

Definition mfoldM {M A B C} `{Monad M} (f : A -> B -> C -> M C) (e : C) : Map A B -> M C :=
  fix go m :=
    match m with
    | [] => ret e
    | (k, x) :: m => let! r := go m in f k x r
    end.

Definition mmapM {M A B C} `{Monad M} (f : B -> M C) : Map A B -> M (Map A C) :=
  fix go m :=
    match m with
    | [] => ret []
    | (k, x) :: m => cons <$> (pair k <$> f x) <*> go m
    end.

Definition mchoose {A B} (m : Map A B) : option (A * B) :=
  match m with
  | [] => None
  | kv :: _ => Some kv
  end.

Definition member {A B} `{Eq A} k (m : Map A B) : bool := if find k m then true else false.

Definition intersect {A B C} `{Eq A} (m1 : Map A B) (m2 : Map A C) : Map A B :=
  filter (fun '(x, _) => if find x m2 then true else false) m1.
(* Definition union {A B} (m1 m2 : Map A B) := m1 ++ m2. *)
Definition union {A B} `{Eq A} (m1 m2 : Map A B) := m1 ++ filter (fun '(x, _) => if find x m1 then false else true) m2.
Infix "∪" := union (at level 50, left associativity).
Infix "∩" := intersect (at level 50, left associativity).

Definition minus {A B C} `{Eq A} (m1 : Map A B) (m2 : Map A C) : Map A B :=
  filter (fun '(x, _) => if find x m2 then false else true) m1.
Infix "\" := minus (at level 50, left associativity).

Definition union_all {A B} `{Eq A} : list (Map A B) -> Map A B := fold_right union empty.

Definition intersect_by {A B C} `{Eq A} (f : A -> B -> B -> option C) (m1 m2 : Map A B) : Map A C :=
  fold_right
   (fun '(k, v1) acc =>
      match find k m2 with
      | Some v2 => match f k v1 v2 with Some c => (k, c) :: acc | None => acc end
      | None => acc
      end)
   [] m1.

(* -------------------- Context generation -------------------- *)

(* Reverse hex *)
Fixpoint string_of_positive n :=
  match n with
  | xH => "1"
  | xO xH => "2"
  | xI xH => "3"
  | xO (xO xH) => "4"
  | xI (xO xH) => "5"
  | xO (xI xH) => "6"
  | xI (xI xH) => "7"
  | xO (xO (xO xH)) => "8"
  | xI (xO (xO xH)) => "9"
  | xO (xI (xO xH)) => "A"
  | xI (xI (xO xH)) => "B"
  | xO (xO (xI xH)) => "C"
  | xI (xO (xI xH)) => "D"
  | xO (xI (xI xH)) => "E"
  | xI (xI (xI xH)) => "F"
  | xO (xO (xO (xO n))) => String "0" (string_of_positive n)
  | xI (xO (xO (xO n))) => String "1" (string_of_positive n)
  | xO (xI (xO (xO n))) => String "2" (string_of_positive n)
  | xI (xI (xO (xO n))) => String "3" (string_of_positive n)
  | xO (xO (xI (xO n))) => String "4" (string_of_positive n)
  | xI (xO (xI (xO n))) => String "5" (string_of_positive n)
  | xO (xI (xI (xO n))) => String "6" (string_of_positive n)
  | xI (xI (xI (xO n))) => String "7" (string_of_positive n)
  | xO (xO (xO (xI n))) => String "8" (string_of_positive n)
  | xI (xO (xO (xI n))) => String "9" (string_of_positive n)
  | xO (xI (xO (xI n))) => String "A" (string_of_positive n)
  | xI (xI (xO (xI n))) => String "B" (string_of_positive n)
  | xO (xO (xI (xI n))) => String "C" (string_of_positive n)
  | xI (xO (xI (xI n))) => String "D" (string_of_positive n)
  | xO (xI (xI (xI n))) => String "E" (string_of_positive n)
  | xI (xI (xI (xI n))) => String "F" (string_of_positive n)
  end.
Definition string_of_N n :=
  match n with
  | N0 => "0"
  | Npos n => string_of_positive n
  end.
(* Compute (string_of_N 100). *)
(* Compute (string_of_N 200). *)
(* Compute (string_of_N 350). *)

Notation "'GM'" := (stateT N (sum string)).

#[global] Existing Instance Monad_either.
#[global] Existing Instance Monad_stateT.

Definition fresh (prefix : string) : GM string :=
  let! n := get in
  let! _ := modify (fun x => 1 + x) in
  ret (prefix +++ string_of_N n).

Definition runGM {A} (m : GM A) : TemplateMonad A :=
  m <- tmEval cbv m ;; (* Necessary: if removed, evaluation takes forever *)
  match runStateT m 0 with
  | inl e => tmFail ("runGM: " +++ e)
  | inr (x, _) => ret x
  end.

Definition runGM' {A} (n : N) (m : GM A) : string + (A × N) :=
  runStateT m n.

Class Show A := show : A -> string.
#[global] Instance Show_string : Show string := fun x => x.
#[global] Instance Show_kername : Show kername := string_of_kername.

(* TODO: impl Show typeclass *)
Definition findM {K A} `{Eq K} `{Show K} (k : K) (m : Map K A) : GM A :=
  match find k m with
  | Some v => ret v
  | None => raise ("findM: " +++ show k)
  end.

Definition findM' {K A} `{Eq K} `{Show K} (k : K) (m : Map K A) (s : string) : GM A :=
  match find k m with
  | Some v => ret v
  | None => raise ("findM': " +++ s +++ ": " +++ show k)
  end.

Definition findM'' {A B} `{Eq A} (k : A) (m : Map A B) (s : string) : GM B :=
  match find k m with
  | Some v => ret v
  | None => raise ("findM'': " +++ s)
  end.

Definition nth_errorN {A} (xs : list A) (n : N) : option A :=
  let fix go n xs :=
    match n, xs with
    | _, [] => None
    | N0, x :: _ => Some x
    | n, _ :: xs => go (n - 1) xs
    end
  in go 0 xs.

Definition nthM {A} (n : N) (xs : list A) : GM A :=
  match nth_errorN xs n with
  | Some v => ret v
  | None => raise ("nthM: " +++ string_of_N n)
  end.

Definition nthM_nat {A} (n : nat) (xs : list A) : GM A :=
  match nth_error xs n with
  | Some v => ret v
  | None => raise ("nthM: " +++ of_string (nat2string10 n))
  end.

(* Parse a mutual inductive definition into constructor names + argument types *)

Definition ind_info := Map kername ((mutual_inductive_body × list inductive) × nat).

Record mind_graph_t := mk_mg {
  mgAtoms : Map string term; (* name -> AST e.g. "list_nat" -> tApp {| .. |} {| .. |} *)
  mgTypes : Map string term; (* name -> AST *)
  mgConstrs : Map string (list string); (* e.g. "nat" -> ["S"; "O"] *)
  mgChildren : Map string ((N × list string) × string) }. (* e.g. "cons_nat" -> (1, ["nat"; "list_nat"], "list_nat") *)

Definition is_sep (c : Byte.byte) : bool :=
  match c with
  | "." | "#" => true
  | _ => false
  end%byte.

Definition qualifier (s : string) : string :=
  let fix go s :=
    match s with
    | "" => ("", false)
    | String c s =>
      let '(s, qualified) := go s in
      let qualified := (qualified || is_sep c)%bool in
      (if qualified then String c s else s, qualified)
    end
  in fst (go s).

Definition unqualified (s : string) : string :=
  let fix go s :=
    match s with
    | "" => ("", false)
    | String c s =>
      let '(s, qualified) := go s in
      let qualified := (qualified || is_sep c)%bool in
      (if qualified then s else String c s, qualified)
    end
  in fst (go s).

Definition inductives_of_env (decls : global_env) : ind_info :=
  fold_right
    (fun '(kername, decl) m =>
      match decl with
      | ConstantDecl _ => m
      | InductiveDecl mbody =>
        (* let '(qual, _) := kername in *)
        (* let kernames := mapi (fun i body => (i, (qual, body.(ind_name)))) mbody.(ind_bodies) in *)
        let kernames := mapi (fun i body => (i, kername)) mbody.(ind_bodies) in
        let inds := map (fun '(i, kername) => mkInd kername i) kernames in
        fold_right
          (fun '(i, kername) m =>
            insert kername (mbody, inds, i) m)
          m kernames
      end)
    empty
    decls.(declarations).

Fixpoint mangle (inds : ind_info) (e : term) : GM string :=
  match e with
  | tRel n => raise "mangle: relative binders not allowed"
  | tApp tycon tys =>
    let! tycon := mangle inds tycon in
    foldlM
      (fun tys ty =>
        let! ty := mangle inds ty in
        ret (tys +++ "_" +++ ty))
      tycon tys
  | tInd ind n =>
    let! '(mbody, _, _) := findM ind.(inductive_mind) inds in
    let! body := nthM_nat ind.(inductive_ind) mbody.(ind_bodies) in
    ret body.(ind_name)
  | tConstruct ind n _ =>
    let! '(mbody, _, _) := findM ind.(inductive_mind) inds in
    let! body := nthM_nat ind.(inductive_ind) mbody.(ind_bodies) in
    let! 'c := nthM_nat n body.(ind_ctors) in
    ret c.(cstr_name)
  | tConst (_, name) _ => ret name
  | e => raise ("mangle: Unrecognized type: " +++ string_of_term e)
  end.

Fixpoint decompose_sorts (ty : term) : list aname × term :=
  match ty with
  | tProd n (tSort _) ty =>
    let '(ns, ty) := decompose_sorts ty in
    (n :: ns, ty)
  | ty => ([], ty)
  end.

Definition tm_type_of (inds : ind_info) (ind : inductive) (n : nat) (pars : list term) : GM term :=
  let! '(mbody, inductives, _) := findM ind.(inductive_mind) inds in
  let! body := nthM_nat ind.(inductive_ind) mbody.(ind_bodies) in
  let! c := nthM_nat n body.(ind_ctors) in
  let '(_, cty) := decompose_sorts c.(cstr_type) in
  let ind_env := (rev pars ++ rev_map (fun ind => tInd ind []) inductives)%list in
  ret (subst0 ind_env cty).

(* Types of constructors for ind specialized to pars *)
Definition constr_types (inds : ind_info) (ind : inductive) (pars : list term)
  : GM (list (string × (list term × term))) :=
  let! '(mbody, _, _) := findM ind.(inductive_mind) inds in
  let! body := nthM_nat ind.(inductive_ind) mbody.(ind_bodies) in
  foldriM_nat
    (fun n _ cs =>
      let ctr := mkApps (tConstruct ind n []) pars in
      let! ctr_ty := tm_type_of inds ind n pars in
      let '(_, tys, rty) := decompose_prod ctr_ty in
      let! c := mangle inds ctr in
      ret ((c, (tys, rty)) :: cs))
    [] body.(ind_ctors).

Definition decompose_ind (decls : global_env) (ty : term) : GM (inductive × list term) :=
  let fix go n ty {struct n} :=
    let find_const n c :=
      let! decl := findM' c decls.(declarations) "decompose_ind tConst" in
      match decl with
      | ConstantDecl {| cst_body := Some body |} => go n body
      | ConstantDecl {| cst_body := None |} =>
        raise ("decompose_ind: empty ConstantDecl body: " +++ string_of_kername c)
      | InductiveDecl _ => raise ("decompose_ind: got InductiveDecl: " +++ string_of_kername c)
      end
    in
    match n with O => raise "decompose_ind: OOF" | S n =>
      match ty with
      | tInd ind _ => ret (ind, [])
      | tApp (tInd ind _) ts => ret (ind, ts)
      | tConst kername _ => find_const n kername
      (* TODO: support "higher kinded type aliases"
         At present, writing recursive functions in TemplateMonad is prohibitively slow,
         but eventually this whole function should be replaced by a call to tmEval. *)
      | ty => raise ("decompose_ind: Unrecognized type: " +++ string_of_term ty)
      end
    end
  in go 100%nat ty.

Global Instance string_Eq : Eq string := { rel_dec := eqb }.

Definition build_graph (atoms : list term) (p : program) : GM (ind_info × mind_graph_t) :=
  let '(decls, ty) := p in
  let inds := inductives_of_env decls in
  let! atoms :=
    fold_right
      (fun '(k, v) m => insert k v m)
      empty
      <$> (let! ids := mapM (mangle inds) atoms in ret (combine ids atoms))
  in
  let fix go n ty g : GM mind_graph_t :=
    let! '(ind, pars) := decompose_ind decls ty in
    match n with O => ret g | S n =>
      let! s := mangle inds ty in
      if member s g.(mgTypes) then ret g else
      let mgTypes := insert s ty g.(mgTypes) in
      let! ctys := constr_types inds ind pars in
      let mgConstrs := insert s (map fst ctys) g.(mgConstrs) in
      let! mgChildren :=
        foldriM
          (fun n '(c, (tys, _)) m =>
            let! tys := mapM (mangle inds) tys in
            ret (insert c (n, tys, s) m))
          g.(mgChildren) ctys
      in
      let g := mk_mg g.(mgAtoms) mgTypes mgConstrs mgChildren in
      let! g :=
        foldrM
          (fun '(c, (tys, _)) g =>
            foldrM (fun ty g => go n ty g) g tys)
          g ctys
      in
      ret g
    end
  in
  let! g := go 100%nat ty (mk_mg atoms atoms empty empty) in
  ret (inds, g).

(* Generate a type of depth-1 frames + associated operations *)

Record frame := mk_frame {
  hIndex : nat;
  hName : string;
  hConstr : term;
  hLefts : list term;
  hFrame : term;
  hRights : list term;
  hRoot : term }.

Definition nAnon := {| binder_name := nAnon; binder_relevance := Relevant |}.
Definition nNamed n := {| binder_name := nNamed n; binder_relevance := Relevant |}.

Definition fn : term -> term -> term := tProd nAnon.
Definition type0 := tSort Sort.type0.
Definition func x t e := tLambda (nNamed x) t e.
Definition lam t e := tLambda nAnon t e.

Definition gen_univ_univD (qual : modpath) (typename : kername) (g : mind_graph_t)
  : ((mutual_inductive_entry × Map string N) × kername) × term :=
  let ty_u := snd typename +++ "_univ" in
  let mgTypes := list_of_map g.(mgTypes) in
  let tys := map (fun '(ty, _) => (ty, ty_u +++ "_" +++ ty)) mgTypes in
  let ty_ns := foldri (fun n '(ty, _) m => insert ty n m) (fun _ => empty) tys in
  let tys := map snd tys in
  let ind_entry : one_inductive_entry := {|
    mind_entry_typename := ty_u;
    mind_entry_arity := type0;
    mind_entry_consnames := tys;
    mind_entry_lc := repeat (tRel 0) #|tys| |}
  in
  let univ_ind := mkInd (qual, snd typename +++ "_univ") 0 in
  let univ := tInd univ_ind [] in
  let ci := {| ci_ind := univ_ind; ci_npar := 0; ci_relevance := Relevant |} in
  let p := {|
    pparams := [];
    puinst := [];
    pcontext := [nAnon];
    preturn := type0
    |}
  in
  let body :=
    func "u" univ
      (tCase ci p (tRel 0)
        (map (fun '(_, ty) => {| bcontext := []; bbody := ty |}) mgTypes))
  in ({|
    mind_entry_record := None;
    mind_entry_finite := Finite;
    mind_entry_params := [];
    mind_entry_inds := [ind_entry];
    mind_entry_universes := Monomorphic_entry;
    mind_entry_template := false;
    mind_entry_variance := None;
    mind_entry_private := None |}, ty_ns, (qual, snd typename +++ "_univD"), body).

Definition holes_of {A} (xs : list A) : list ((list A × A) × list A) :=
  let fix go l xs :=
    match xs with
    | [] => []
    | x :: xs => (rev l, x, xs) :: go (x :: l) xs
    end
  in go [] xs.

Definition gen_frames (decls : global_env) (g : mind_graph_t)
  : GM (list frame × Map string (list frame)) :=
  let! cfs :=
    foldrM
      (fun '(c, (n_constr, tys, rty)) hs =>
        let! tys := mapM (fun ty => findM ty g.(mgTypes)) tys in
        let! rty := findM rty g.(mgTypes) in
        let! '(ind, pars) := decompose_ind decls rty in
        foldriM
          (fun n_arg '(l, x, r) hs =>
            ret ((c, {|
              hIndex := 0; (* bogus! filled in below *)
              hName := c +++ string_of_N n_arg;
              hConstr := mkApps (tConstruct ind (N.to_nat n_constr) []) pars;
              hLefts := l;
              hFrame := x;
              hRights := r;
              hRoot := rty |}) :: hs))
          hs (holes_of tys))
      [] (list_of_map g.(mgChildren))
  in
  ret (foldri_nat
    (fun i '(c, f) '(fs, m) =>
      let f := mk_frame i f.(hName) f.(hConstr) f.(hLefts) f.(hFrame) f.(hRights) f.(hRoot) in
      (f :: fs, update c (cons f) [] m))
    (fun _ => ([], empty))
    cfs).

Definition index_of {A} (f : A -> bool) (xs : list A) : GM nat :=
  let fix go n xs :=
    match xs with
    | [] => raise "index_of: not found"
    | x :: xs => if f x then ret n else go (S n) xs
    end
  in go O xs.

Definition gen_frame_t (qual : modpath) (typename : kername) (inds : ind_info) (g : mind_graph_t) (fs : list frame)
  : GM mutual_inductive_entry :=
  let univ := tInd (mkInd (qual, snd typename +++ "_univ") 0) [] in
  let to_univ ty :=
    let! mangled := mangle inds ty in
    let! n := index_of (fun '(s, _) => rel_dec s mangled) (list_of_map g.(mgTypes)) in
    ret (tConstruct (mkInd (qual, snd typename +++ "_univ") 0) n [])
  in
  let! ctr_types :=
    mapM
      (fun '(mk_frame _ _ _ ls t rs root) =>
        let! args := mapM to_univ [t; root] in
        let rty := mkApps (tRel #|ls ++ rs|) args in
        ret (fold_right fn (fold_right fn rty rs) ls))
      fs
  in
  let ind_entry : one_inductive_entry := {|
    mind_entry_typename := snd typename +++ "_frame_t";
    mind_entry_arity := fn univ (fn univ type0);
    mind_entry_consnames := map (fun h => h.(hName)) fs;
    mind_entry_lc := ctr_types |}
  in
  ret {|
    mind_entry_record := None;
    mind_entry_finite := Finite;
    mind_entry_params := [];
    mind_entry_inds := [ind_entry];
    mind_entry_universes := Monomorphic_entry;
    mind_entry_template := false;
    mind_entry_variance := None;
    mind_entry_private := None |}.

Definition gen_frameD (qual : modpath) (typename : kername) (univD_kername : kername) (fs : list frame)
  : kername × term :=
  let univ_ty := tInd (mkInd (qual, snd typename +++ "_univ") O) [] in
  let univD ty := mkApps (tConst univD_kername []) [ty] in
  let frame_ind := mkInd (qual, snd typename +++ "_frame_t") O in
  let frame_ty := mkApps (tInd frame_ind []) [tRel 1; tRel O] in
  let mk_arm h :=
    let 'mk_frame _ name constr lefts frame rights root := h in
    let ctr_arity := lefts ++ rights in
    let indices := rev (seq (1 + #|rights|) #|lefts|) ++ [O] ++ rev (seq 1 #|rights|) in
    let add_arg arg_ty body := lam arg_ty body in
    {| bcontext := map (fun _ => nAnon) ctr_arity;
       bbody := lam frame (mkApps constr (map tRel indices)) |}
  in
  let p :=
    {| pparams := [];
       puinst := [];
       pcontext := [nNamed "h"; nNamed "B"; nNamed "A"];
       preturn := (fn (univD (tRel 2)) (univD (tRel 2))) |}
  in
  let body :=
    func "A" univ_ty (func "B" univ_ty (func "h" frame_ty
      (tCase {| ci_ind := frame_ind ; ci_npar := O ; ci_relevance := Relevant |}
        p
        (tRel O) (map mk_arm fs))))
  in
  ((qual, snd typename +++ "_frameD"), body).

Definition kername_of_const (s : string) : TemplateMonad kername :=
  refs <- tmLocate s ;;
  match refs with
  | ConstRef kername :: _ => ret kername
  | _ :: _ => tmFail ("kername_of_const: Not a constant: " +++ s)
  | [] => tmFail ("kername_of_const: Not in scope: " +++ s)
  end.

Definition gen_Frame_ops (qual : modpath) (typename : kername) (T : program) (atoms : list term) : GM _ :=
  let! '(inds, g) := build_graph atoms T in
  let! '(fs, cfs) := gen_frames (fst T) g in
  let '(univ, univ_of_tyname, univD, univD_body) := gen_univ_univD qual typename g in
  let! frame_t := gen_frame_t qual typename inds g fs in
  ret (inds, g, fs, cfs, univ, univ_of_tyname, univD, univD_body, frame_t).

Record aux_data_t := mk_aux_data {
  aQual : modpath;
  aEnv : global_env;
  aIndInfo : ind_info;
  aTypename : kername;
  aGraph : mind_graph_t;
  aUnivOfTyname : Map string N;
  aFramesOfConstr : Map string (list frame) }.

Class AuxData (U : Set) := aux_data : aux_data_t.

Definition mk_Frame_ops (qual : modpath) (typename : kername) (T : Type) (atoms : list Set) : TemplateMonad unit :=
  p <- tmQuoteRec T ;;
  atoms <- monad_map tmQuote atoms ;;
  let! '(inds, g, fs, cfs, univ, univ_of_tyname, univD, univD_body, frame_t) :=
    runGM (gen_Frame_ops qual typename p atoms) in
  tmMkInductive false univ ;;
  (* tmPrint univD ;; *)
  (* tmPrint univD_body ;; *)
  (* tmPrint =<< tmUnquote univD_body ;; *)
  tmMkDefinition (snd univD) univD_body ;;
  tmMkInductive false frame_t ;;
  let univD_kername := univD in
  let '(frameD, frameD_body) := gen_frameD qual typename univD_kername fs in
  tmMkDefinition (snd frameD) frameD_body ;;
  match <%@Frame%> with
  | tInd Frame_ind [] =>
    tmMkDefinition (snd typename +++ "_Frame_ops") (
      mkApps (tConstruct Frame_ind 0 []) [
        tInd (mkInd (qual, snd typename +++ "_univ") 0) [];
        tConst (qual, snd typename +++ "_univD") [];
        tInd (mkInd (qual, snd typename +++ "_frame_t") 0) [];
           tConst (qual, snd typename +++ "_frameD") []]) ;;
    tmDefinition (snd typename +++ "_aux_data")
                 (mk_aux_data qual (fst p) inds typename g univ_of_tyname cfs) ;;
    ret tt
  | _ => tmPrint "Error: Frame was not as expected"
  end.
