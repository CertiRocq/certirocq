
type __ = Obj.t
let __ = let rec f _ = Obj.repr f in Obj.repr f

type unit0 =
| Tt

type bool =
| True
| False

(** val negb : bool -> bool **)

let negb = function
| True -> False
| False -> True

type nat =
| O
| S of nat

type 'a option =
| Some of 'a
| None

type ('a, 'b) sum =
| Inl of 'a
| Inr of 'b

type ('a, 'b) prod =
| Pair of 'a * 'b

(** val fst : ('a1, 'a2) prod -> 'a1 **)

let fst = function
| Pair (x0, _) -> x0

(** val snd : ('a1, 'a2) prod -> 'a2 **)

let snd = function
| Pair (_, y) -> y

type 'a list =
| Nil
| Cons of 'a * 'a list

(** val app : 'a1 list -> 'a1 list -> 'a1 list **)

let rec app l m =
  match l with
  | Nil -> m
  | Cons (a, l1) -> Cons (a, (app l1 m))

type comparison =
| Eq
| Lt
| Gt

type compareSpecT =
| CompEqT
| CompLtT
| CompGtT

(** val compareSpec2Type : comparison -> compareSpecT **)

let compareSpec2Type = function
| Eq -> CompEqT
| Lt -> CompLtT
| Gt -> CompGtT

type 'a compSpecT = compareSpecT

(** val compSpec2Type : 'a1 -> 'a1 -> comparison -> 'a1 compSpecT **)

let compSpec2Type _ _ =
  compareSpec2Type

(** val id : 'a1 -> 'a1 **)

let id x0 =
  x0

type 'a sig0 = 'a
  (* singleton inductive, whose constructor was exist *)

type sumbool =
| Left
| Right

type uint =
| Nil0
| D0 of uint
| D1 of uint
| D2 of uint
| D3 of uint
| D4 of uint
| D5 of uint
| D6 of uint
| D7 of uint
| D8 of uint
| D9 of uint

type int =
| Pos of uint
| Neg of uint

(** val revapp : uint -> uint -> uint **)

let rec revapp d d' =
  match d with
  | Nil0 -> d'
  | D0 d0 -> revapp d0 (D0 d')
  | D1 d0 -> revapp d0 (D1 d')
  | D2 d0 -> revapp d0 (D2 d')
  | D3 d0 -> revapp d0 (D3 d')
  | D4 d0 -> revapp d0 (D4 d')
  | D5 d0 -> revapp d0 (D5 d')
  | D6 d0 -> revapp d0 (D6 d')
  | D7 d0 -> revapp d0 (D7 d')
  | D8 d0 -> revapp d0 (D8 d')
  | D9 d0 -> revapp d0 (D9 d')

(** val rev : uint -> uint **)

let rev d =
  revapp d Nil0

module Little =
 struct
  (** val double : uint -> uint **)

  let rec double = function
  | Nil0 -> Nil0
  | D0 d0 -> D0 (double d0)
  | D1 d0 -> D2 (double d0)
  | D2 d0 -> D4 (double d0)
  | D3 d0 -> D6 (double d0)
  | D4 d0 -> D8 (double d0)
  | D5 d0 -> D0 (succ_double d0)
  | D6 d0 -> D2 (succ_double d0)
  | D7 d0 -> D4 (succ_double d0)
  | D8 d0 -> D6 (succ_double d0)
  | D9 d0 -> D8 (succ_double d0)

  (** val succ_double : uint -> uint **)

  and succ_double = function
  | Nil0 -> D1 Nil0
  | D0 d0 -> D1 (double d0)
  | D1 d0 -> D3 (double d0)
  | D2 d0 -> D5 (double d0)
  | D3 d0 -> D7 (double d0)
  | D4 d0 -> D9 (double d0)
  | D5 d0 -> D1 (succ_double d0)
  | D6 d0 -> D3 (succ_double d0)
  | D7 d0 -> D5 (succ_double d0)
  | D8 d0 -> D7 (succ_double d0)
  | D9 d0 -> D9 (succ_double d0)
 end

type uint0 =
| Nil1
| D10 of uint0
| D11 of uint0
| D12 of uint0
| D13 of uint0
| D14 of uint0
| D15 of uint0
| D16 of uint0
| D17 of uint0
| D18 of uint0
| D19 of uint0
| Da of uint0
| Db of uint0
| Dc of uint0
| Dd of uint0
| De of uint0
| Df of uint0

type int0 =
| Pos0 of uint0
| Neg0 of uint0

(** val revapp0 : uint0 -> uint0 -> uint0 **)

let rec revapp0 d d' =
  match d with
  | Nil1 -> d'
  | D10 d0 -> revapp0 d0 (D10 d')
  | D11 d0 -> revapp0 d0 (D11 d')
  | D12 d0 -> revapp0 d0 (D12 d')
  | D13 d0 -> revapp0 d0 (D13 d')
  | D14 d0 -> revapp0 d0 (D14 d')
  | D15 d0 -> revapp0 d0 (D15 d')
  | D16 d0 -> revapp0 d0 (D16 d')
  | D17 d0 -> revapp0 d0 (D17 d')
  | D18 d0 -> revapp0 d0 (D18 d')
  | D19 d0 -> revapp0 d0 (D19 d')
  | Da d0 -> revapp0 d0 (Da d')
  | Db d0 -> revapp0 d0 (Db d')
  | Dc d0 -> revapp0 d0 (Dc d')
  | Dd d0 -> revapp0 d0 (Dd d')
  | De d0 -> revapp0 d0 (De d')
  | Df d0 -> revapp0 d0 (Df d')

(** val rev0 : uint0 -> uint0 **)

let rev0 d =
  revapp0 d Nil1

module Coq_Little =
 struct
  (** val double : uint0 -> uint0 **)

  let rec double = function
  | Nil1 -> Nil1
  | D10 d0 -> D10 (double d0)
  | D11 d0 -> D12 (double d0)
  | D12 d0 -> D14 (double d0)
  | D13 d0 -> D16 (double d0)
  | D14 d0 -> D18 (double d0)
  | D15 d0 -> Da (double d0)
  | D16 d0 -> Dc (double d0)
  | D17 d0 -> De (double d0)
  | D18 d0 -> D10 (succ_double d0)
  | D19 d0 -> D12 (succ_double d0)
  | Da d0 -> D14 (succ_double d0)
  | Db d0 -> D16 (succ_double d0)
  | Dc d0 -> D18 (succ_double d0)
  | Dd d0 -> Da (succ_double d0)
  | De d0 -> Dc (succ_double d0)
  | Df d0 -> De (succ_double d0)

  (** val succ_double : uint0 -> uint0 **)

  and succ_double = function
  | Nil1 -> D11 Nil1
  | D10 d0 -> D11 (double d0)
  | D11 d0 -> D13 (double d0)
  | D12 d0 -> D15 (double d0)
  | D13 d0 -> D17 (double d0)
  | D14 d0 -> D19 (double d0)
  | D15 d0 -> Db (double d0)
  | D16 d0 -> Dd (double d0)
  | D17 d0 -> Df (double d0)
  | D18 d0 -> D11 (succ_double d0)
  | D19 d0 -> D13 (succ_double d0)
  | Da d0 -> D15 (succ_double d0)
  | Db d0 -> D17 (succ_double d0)
  | Dc d0 -> D19 (succ_double d0)
  | Dd d0 -> Db (succ_double d0)
  | De d0 -> Dd (succ_double d0)
  | Df d0 -> Df (succ_double d0)
 end

type uint1 =
| UIntDec of uint
| UIntHex of uint0

type int1 =
| IntDec of int
| IntHex of int0

module Coq__1 = struct
 (** val add : nat -> nat -> nat **)let rec add n0 m =
   match n0 with
   | O -> m
   | S p -> S (add p m)
end
include Coq__1

(** val max : nat -> nat -> nat **)

let rec max n0 m =
  match n0 with
  | O -> m
  | S n' -> (match m with
             | O -> n0
             | S m' -> S (max n' m'))

(** val min : nat -> nat -> nat **)

let rec min n0 m =
  match n0 with
  | O -> O
  | S n' -> (match m with
             | O -> O
             | S m' -> S (min n' m'))

type reflect =
| ReflectT
| ReflectF

(** val iff_reflect : bool -> reflect **)

let iff_reflect = function
| True -> ReflectT
| False -> ReflectF

(** val flip : ('a1 -> 'a2 -> 'a3) -> 'a2 -> 'a1 -> 'a3 **)

let flip f x0 y =
  f y x0

module type OrderedType =
 sig
  type t

  val compare : t -> t -> comparison

  val eq_dec : t -> t -> sumbool
 end

module type OrderedType' =
 sig
  type t

  val compare : t -> t -> comparison

  val eq_dec : t -> t -> sumbool
 end

module OT_to_Full =
 functor (O:OrderedType') ->
 struct
  type t = O.t

  (** val compare : t -> t -> comparison **)

  let compare =
    O.compare

  (** val eq_dec : t -> t -> sumbool **)

  let eq_dec =
    O.eq_dec
 end

module OT_to_OrderTac =
 functor (OT:OrderedType) ->
 struct
  module OTF = OT_to_Full(OT)

  module TO =
   struct
    type t = OTF.t

    (** val compare : t -> t -> comparison **)

    let compare =
      OTF.compare

    (** val eq_dec : t -> t -> sumbool **)

    let eq_dec =
      OTF.eq_dec
   end
 end

module OrderedTypeFacts =
 functor (O:OrderedType') ->
 struct
  module OrderTac = OT_to_OrderTac(O)

  (** val eq_dec : O.t -> O.t -> sumbool **)

  let eq_dec =
    O.eq_dec

  (** val lt_dec : O.t -> O.t -> sumbool **)

  let lt_dec x0 y =
    let c = compSpec2Type x0 y (O.compare x0 y) in (match c with
                                                    | CompLtT -> Left
                                                    | _ -> Right)

  (** val eqb : O.t -> O.t -> bool **)

  let eqb x0 y =
    match eq_dec x0 y with
    | Left -> True
    | Right -> False
 end

type positive =
| XI of positive
| XO of positive
| XH

type n =
| N0
| Npos of positive

type z =
| Z0
| Zpos of positive
| Zneg of positive

module Pos =
 struct
  type mask =
  | IsNul
  | IsPos of positive
  | IsNeg
 end

module Coq_Pos =
 struct
  type t = positive

  (** val succ : positive -> positive **)

  let rec succ = function
  | XI p -> XO (succ p)
  | XO p -> XI p
  | XH -> XO XH

  (** val add : positive -> positive -> positive **)

  let rec add x0 y =
    match x0 with
    | XI p -> (match y with
               | XI q -> XO (add_carry p q)
               | XO q -> XI (add p q)
               | XH -> XO (succ p))
    | XO p -> (match y with
               | XI q -> XI (add p q)
               | XO q -> XO (add p q)
               | XH -> XI p)
    | XH -> (match y with
             | XI q -> XO (succ q)
             | XO q -> XI q
             | XH -> XO XH)

  (** val add_carry : positive -> positive -> positive **)

  and add_carry x0 y =
    match x0 with
    | XI p -> (match y with
               | XI q -> XI (add_carry p q)
               | XO q -> XO (add_carry p q)
               | XH -> XI (succ p))
    | XO p -> (match y with
               | XI q -> XO (add_carry p q)
               | XO q -> XI (add p q)
               | XH -> XO (succ p))
    | XH -> (match y with
             | XI q -> XI (succ q)
             | XO q -> XO (succ q)
             | XH -> XI XH)

  (** val pred_double : positive -> positive **)

  let rec pred_double = function
  | XI p -> XI (XO p)
  | XO p -> XI (pred_double p)
  | XH -> XH

  (** val pred : positive -> positive **)

  let pred = function
  | XI p -> XO p
  | XO p -> pred_double p
  | XH -> XH

  (** val pred_N : positive -> n **)

  let pred_N = function
  | XI p -> Npos (XO p)
  | XO p -> Npos (pred_double p)
  | XH -> N0

  type mask = Pos.mask =
  | IsNul
  | IsPos of positive
  | IsNeg

  (** val mask_rect : 'a1 -> (positive -> 'a1) -> 'a1 -> mask -> 'a1 **)

  let mask_rect f f0 f1 = function
  | IsNul -> f
  | IsPos x0 -> f0 x0
  | IsNeg -> f1

  (** val mask_rec : 'a1 -> (positive -> 'a1) -> 'a1 -> mask -> 'a1 **)

  let mask_rec f f0 f1 = function
  | IsNul -> f
  | IsPos x0 -> f0 x0
  | IsNeg -> f1

  (** val succ_double_mask : mask -> mask **)

  let succ_double_mask = function
  | IsNul -> IsPos XH
  | IsPos p -> IsPos (XI p)
  | IsNeg -> IsNeg

  (** val double_mask : mask -> mask **)

  let double_mask = function
  | IsPos p -> IsPos (XO p)
  | x1 -> x1

  (** val double_pred_mask : positive -> mask **)

  let double_pred_mask = function
  | XI p -> IsPos (XO (XO p))
  | XO p -> IsPos (XO (pred_double p))
  | XH -> IsNul

  (** val pred_mask : mask -> mask **)

  let pred_mask = function
  | IsPos q -> (match q with
                | XH -> IsNul
                | _ -> IsPos (pred q))
  | _ -> IsNeg

  (** val sub_mask : positive -> positive -> mask **)

  let rec sub_mask x0 y =
    match x0 with
    | XI p ->
      (match y with
       | XI q -> double_mask (sub_mask p q)
       | XO q -> succ_double_mask (sub_mask p q)
       | XH -> IsPos (XO p))
    | XO p ->
      (match y with
       | XI q -> succ_double_mask (sub_mask_carry p q)
       | XO q -> double_mask (sub_mask p q)
       | XH -> IsPos (pred_double p))
    | XH -> (match y with
             | XH -> IsNul
             | _ -> IsNeg)

  (** val sub_mask_carry : positive -> positive -> mask **)

  and sub_mask_carry x0 y =
    match x0 with
    | XI p ->
      (match y with
       | XI q -> succ_double_mask (sub_mask_carry p q)
       | XO q -> double_mask (sub_mask p q)
       | XH -> IsPos (pred_double p))
    | XO p ->
      (match y with
       | XI q -> double_mask (sub_mask_carry p q)
       | XO q -> succ_double_mask (sub_mask_carry p q)
       | XH -> double_pred_mask p)
    | XH -> IsNeg

  (** val sub : positive -> positive -> positive **)

  let sub x0 y =
    match sub_mask x0 y with
    | IsPos z0 -> z0
    | _ -> XH

  (** val mul : positive -> positive -> positive **)

  let rec mul x0 y =
    match x0 with
    | XI p -> add y (XO (mul p y))
    | XO p -> XO (mul p y)
    | XH -> y

  (** val iter : ('a1 -> 'a1) -> 'a1 -> positive -> 'a1 **)

  let rec iter f x0 = function
  | XI n' -> f (iter f (iter f x0 n') n')
  | XO n' -> iter f (iter f x0 n') n'
  | XH -> f x0

  (** val pow : positive -> positive -> positive **)

  let pow x0 =
    iter (mul x0) XH

  (** val square : positive -> positive **)

  let rec square = function
  | XI p0 -> XI (XO (add (square p0) p0))
  | XO p0 -> XO (XO (square p0))
  | XH -> XH

  (** val div2 : positive -> positive **)

  let div2 = function
  | XI p0 -> p0
  | XO p0 -> p0
  | XH -> XH

  (** val div2_up : positive -> positive **)

  let div2_up = function
  | XI p0 -> succ p0
  | XO p0 -> p0
  | XH -> XH

  (** val size_nat : positive -> nat **)

  let rec size_nat = function
  | XI p0 -> S (size_nat p0)
  | XO p0 -> S (size_nat p0)
  | XH -> S O

  (** val size : positive -> positive **)

  let rec size = function
  | XI p0 -> succ (size p0)
  | XO p0 -> succ (size p0)
  | XH -> XH

  (** val compare_cont : comparison -> positive -> positive -> comparison **)

  let rec compare_cont r x0 y =
    match x0 with
    | XI p -> (match y with
               | XI q -> compare_cont r p q
               | XO q -> compare_cont Gt p q
               | XH -> Gt)
    | XO p -> (match y with
               | XI q -> compare_cont Lt p q
               | XO q -> compare_cont r p q
               | XH -> Gt)
    | XH -> (match y with
             | XH -> r
             | _ -> Lt)

  (** val compare : positive -> positive -> comparison **)

  let compare =
    compare_cont Eq

  (** val min : positive -> positive -> positive **)

  let min p p' =
    match compare p p' with
    | Gt -> p'
    | _ -> p

  (** val max : positive -> positive -> positive **)

  let max p p' =
    match compare p p' with
    | Gt -> p
    | _ -> p'

  (** val eqb : positive -> positive -> bool **)

  let rec eqb p q =
    match p with
    | XI p0 -> (match q with
                | XI q0 -> eqb p0 q0
                | _ -> False)
    | XO p0 -> (match q with
                | XO q0 -> eqb p0 q0
                | _ -> False)
    | XH -> (match q with
             | XH -> True
             | _ -> False)

  (** val leb : positive -> positive -> bool **)

  let leb x0 y =
    match compare x0 y with
    | Gt -> False
    | _ -> True

  (** val ltb : positive -> positive -> bool **)

  let ltb x0 y =
    match compare x0 y with
    | Lt -> True
    | _ -> False

  (** val sqrtrem_step :
      (positive -> positive) -> (positive -> positive) -> (positive, mask) prod -> (positive, mask) prod **)

  let sqrtrem_step f g = function
  | Pair (s, y) ->
    (match y with
     | IsPos r ->
       let s' = XI (XO s) in
       let r' = g (f r) in
       (match leb s' r' with
        | True -> Pair ((XI s), (sub_mask r' s'))
        | False -> Pair ((XO s), (IsPos r')))
     | _ -> Pair ((XO s), (sub_mask (g (f XH)) (XO (XO XH)))))

  (** val sqrtrem : positive -> (positive, mask) prod **)

  let rec sqrtrem = function
  | XI p0 ->
    (match p0 with
     | XI p1 -> sqrtrem_step (fun x0 -> XI x0) (fun x0 -> XI x0) (sqrtrem p1)
     | XO p1 -> sqrtrem_step (fun x0 -> XO x0) (fun x0 -> XI x0) (sqrtrem p1)
     | XH -> Pair (XH, (IsPos (XO XH))))
  | XO p0 ->
    (match p0 with
     | XI p1 -> sqrtrem_step (fun x0 -> XI x0) (fun x0 -> XO x0) (sqrtrem p1)
     | XO p1 -> sqrtrem_step (fun x0 -> XO x0) (fun x0 -> XO x0) (sqrtrem p1)
     | XH -> Pair (XH, (IsPos XH)))
  | XH -> Pair (XH, IsNul)

  (** val sqrt : positive -> positive **)

  let sqrt p =
    fst (sqrtrem p)

  (** val gcdn : nat -> positive -> positive -> positive **)

  let rec gcdn n0 a b =
    match n0 with
    | O -> XH
    | S n1 ->
      (match a with
       | XI a' ->
         (match b with
          | XI b' -> (match compare a' b' with
                      | Eq -> a
                      | Lt -> gcdn n1 (sub b' a') a
                      | Gt -> gcdn n1 (sub a' b') b)
          | XO b0 -> gcdn n1 a b0
          | XH -> XH)
       | XO a0 -> (match b with
                   | XI _ -> gcdn n1 a0 b
                   | XO b0 -> XO (gcdn n1 a0 b0)
                   | XH -> XH)
       | XH -> XH)

  (** val gcd : positive -> positive -> positive **)

  let gcd a b =
    gcdn (Coq__1.add (size_nat a) (size_nat b)) a b

  (** val ggcdn : nat -> positive -> positive -> (positive, (positive, positive) prod) prod **)

  let rec ggcdn n0 a b =
    match n0 with
    | O -> Pair (XH, (Pair (a, b)))
    | S n1 ->
      (match a with
       | XI a' ->
         (match b with
          | XI b' ->
            (match compare a' b' with
             | Eq -> Pair (a, (Pair (XH, XH)))
             | Lt ->
               let Pair (g, p) = ggcdn n1 (sub b' a') a in
               let Pair (ba, aa) = p in Pair (g, (Pair (aa, (add aa (XO ba)))))
             | Gt ->
               let Pair (g, p) = ggcdn n1 (sub a' b') b in
               let Pair (ab, bb) = p in Pair (g, (Pair ((add bb (XO ab)), bb))))
          | XO b0 -> let Pair (g, p) = ggcdn n1 a b0 in let Pair (aa, bb) = p in Pair (g, (Pair (aa, (XO bb))))
          | XH -> Pair (XH, (Pair (a, XH))))
       | XO a0 ->
         (match b with
          | XI _ -> let Pair (g, p) = ggcdn n1 a0 b in let Pair (aa, bb) = p in Pair (g, (Pair ((XO aa), bb)))
          | XO b0 -> let Pair (g, p) = ggcdn n1 a0 b0 in Pair ((XO g), p)
          | XH -> Pair (XH, (Pair (a, XH))))
       | XH -> Pair (XH, (Pair (XH, b))))

  (** val ggcd : positive -> positive -> (positive, (positive, positive) prod) prod **)

  let ggcd a b =
    ggcdn (Coq__1.add (size_nat a) (size_nat b)) a b

  (** val coq_Nsucc_double : n -> n **)

  let coq_Nsucc_double = function
  | N0 -> Npos XH
  | Npos p -> Npos (XI p)

  (** val coq_Ndouble : n -> n **)

  let coq_Ndouble = function
  | N0 -> N0
  | Npos p -> Npos (XO p)

  (** val coq_lor : positive -> positive -> positive **)

  let rec coq_lor p q =
    match p with
    | XI p0 -> (match q with
                | XI q0 -> XI (coq_lor p0 q0)
                | XO q0 -> XI (coq_lor p0 q0)
                | XH -> p)
    | XO p0 -> (match q with
                | XI q0 -> XI (coq_lor p0 q0)
                | XO q0 -> XO (coq_lor p0 q0)
                | XH -> XI p0)
    | XH -> (match q with
             | XO q0 -> XI q0
             | _ -> q)

  (** val coq_land : positive -> positive -> n **)

  let rec coq_land p q =
    match p with
    | XI p0 ->
      (match q with
       | XI q0 -> coq_Nsucc_double (coq_land p0 q0)
       | XO q0 -> coq_Ndouble (coq_land p0 q0)
       | XH -> Npos XH)
    | XO p0 ->
      (match q with
       | XI q0 -> coq_Ndouble (coq_land p0 q0)
       | XO q0 -> coq_Ndouble (coq_land p0 q0)
       | XH -> N0)
    | XH -> (match q with
             | XO _ -> N0
             | _ -> Npos XH)

  (** val ldiff : positive -> positive -> n **)

  let rec ldiff p q =
    match p with
    | XI p0 ->
      (match q with
       | XI q0 -> coq_Ndouble (ldiff p0 q0)
       | XO q0 -> coq_Nsucc_double (ldiff p0 q0)
       | XH -> Npos (XO p0))
    | XO p0 ->
      (match q with
       | XI q0 -> coq_Ndouble (ldiff p0 q0)
       | XO q0 -> coq_Ndouble (ldiff p0 q0)
       | XH -> Npos p)
    | XH -> (match q with
             | XO _ -> Npos XH
             | _ -> N0)

  (** val coq_lxor : positive -> positive -> n **)

  let rec coq_lxor p q =
    match p with
    | XI p0 ->
      (match q with
       | XI q0 -> coq_Ndouble (coq_lxor p0 q0)
       | XO q0 -> coq_Nsucc_double (coq_lxor p0 q0)
       | XH -> Npos (XO p0))
    | XO p0 ->
      (match q with
       | XI q0 -> coq_Nsucc_double (coq_lxor p0 q0)
       | XO q0 -> coq_Ndouble (coq_lxor p0 q0)
       | XH -> Npos (XI p0))
    | XH -> (match q with
             | XI q0 -> Npos (XO q0)
             | XO q0 -> Npos (XI q0)
             | XH -> N0)

  (** val shiftl_nat : positive -> nat -> positive **)

  let rec shiftl_nat p = function
  | O -> p
  | S n1 -> XO (shiftl_nat p n1)

  (** val shiftr_nat : positive -> nat -> positive **)

  let rec shiftr_nat p = function
  | O -> p
  | S n1 -> div2 (shiftr_nat p n1)

  (** val shiftl : positive -> n -> positive **)

  let shiftl p = function
  | N0 -> p
  | Npos n1 -> iter (fun x0 -> XO x0) p n1

  (** val shiftr : positive -> n -> positive **)

  let shiftr p = function
  | N0 -> p
  | Npos n1 -> iter div2 p n1

  (** val testbit_nat : positive -> nat -> bool **)

  let rec testbit_nat p n0 =
    match p with
    | XI p0 -> (match n0 with
                | O -> True
                | S n' -> testbit_nat p0 n')
    | XO p0 -> (match n0 with
                | O -> False
                | S n' -> testbit_nat p0 n')
    | XH -> (match n0 with
             | O -> True
             | S _ -> False)

  (** val testbit : positive -> n -> bool **)

  let rec testbit p n0 =
    match p with
    | XI p0 -> (match n0 with
                | N0 -> True
                | Npos n1 -> testbit p0 (pred_N n1))
    | XO p0 -> (match n0 with
                | N0 -> False
                | Npos n1 -> testbit p0 (pred_N n1))
    | XH -> (match n0 with
             | N0 -> True
             | Npos _ -> False)

  (** val iter_op : ('a1 -> 'a1 -> 'a1) -> positive -> 'a1 -> 'a1 **)

  let rec iter_op op p a =
    match p with
    | XI p0 -> op a (iter_op op p0 (op a a))
    | XO p0 -> iter_op op p0 (op a a)
    | XH -> a

  (** val to_nat : positive -> nat **)

  let to_nat x0 =
    iter_op Coq__1.add x0 (S O)

  (** val of_nat : nat -> positive **)

  let rec of_nat = function
  | O -> XH
  | S x0 -> (match x0 with
             | O -> XH
             | S _ -> succ (of_nat x0))

  (** val of_succ_nat : nat -> positive **)

  let rec of_succ_nat = function
  | O -> XH
  | S x0 -> succ (of_succ_nat x0)

  (** val of_uint_acc : uint -> positive -> positive **)

  let rec of_uint_acc d acc =
    match d with
    | Nil0 -> acc
    | D0 l -> of_uint_acc l (mul (XO (XI (XO XH))) acc)
    | D1 l -> of_uint_acc l (add XH (mul (XO (XI (XO XH))) acc))
    | D2 l -> of_uint_acc l (add (XO XH) (mul (XO (XI (XO XH))) acc))
    | D3 l -> of_uint_acc l (add (XI XH) (mul (XO (XI (XO XH))) acc))
    | D4 l -> of_uint_acc l (add (XO (XO XH)) (mul (XO (XI (XO XH))) acc))
    | D5 l -> of_uint_acc l (add (XI (XO XH)) (mul (XO (XI (XO XH))) acc))
    | D6 l -> of_uint_acc l (add (XO (XI XH)) (mul (XO (XI (XO XH))) acc))
    | D7 l -> of_uint_acc l (add (XI (XI XH)) (mul (XO (XI (XO XH))) acc))
    | D8 l -> of_uint_acc l (add (XO (XO (XO XH))) (mul (XO (XI (XO XH))) acc))
    | D9 l -> of_uint_acc l (add (XI (XO (XO XH))) (mul (XO (XI (XO XH))) acc))

  (** val of_uint : uint -> n **)

  let rec of_uint = function
  | Nil0 -> N0
  | D0 l -> of_uint l
  | D1 l -> Npos (of_uint_acc l XH)
  | D2 l -> Npos (of_uint_acc l (XO XH))
  | D3 l -> Npos (of_uint_acc l (XI XH))
  | D4 l -> Npos (of_uint_acc l (XO (XO XH)))
  | D5 l -> Npos (of_uint_acc l (XI (XO XH)))
  | D6 l -> Npos (of_uint_acc l (XO (XI XH)))
  | D7 l -> Npos (of_uint_acc l (XI (XI XH)))
  | D8 l -> Npos (of_uint_acc l (XO (XO (XO XH))))
  | D9 l -> Npos (of_uint_acc l (XI (XO (XO XH))))

  (** val of_hex_uint_acc : uint0 -> positive -> positive **)

  let rec of_hex_uint_acc d acc =
    match d with
    | Nil1 -> acc
    | D10 l -> of_hex_uint_acc l (mul (XO (XO (XO (XO XH)))) acc)
    | D11 l -> of_hex_uint_acc l (add XH (mul (XO (XO (XO (XO XH)))) acc))
    | D12 l -> of_hex_uint_acc l (add (XO XH) (mul (XO (XO (XO (XO XH)))) acc))
    | D13 l -> of_hex_uint_acc l (add (XI XH) (mul (XO (XO (XO (XO XH)))) acc))
    | D14 l -> of_hex_uint_acc l (add (XO (XO XH)) (mul (XO (XO (XO (XO XH)))) acc))
    | D15 l -> of_hex_uint_acc l (add (XI (XO XH)) (mul (XO (XO (XO (XO XH)))) acc))
    | D16 l -> of_hex_uint_acc l (add (XO (XI XH)) (mul (XO (XO (XO (XO XH)))) acc))
    | D17 l -> of_hex_uint_acc l (add (XI (XI XH)) (mul (XO (XO (XO (XO XH)))) acc))
    | D18 l -> of_hex_uint_acc l (add (XO (XO (XO XH))) (mul (XO (XO (XO (XO XH)))) acc))
    | D19 l -> of_hex_uint_acc l (add (XI (XO (XO XH))) (mul (XO (XO (XO (XO XH)))) acc))
    | Da l -> of_hex_uint_acc l (add (XO (XI (XO XH))) (mul (XO (XO (XO (XO XH)))) acc))
    | Db l -> of_hex_uint_acc l (add (XI (XI (XO XH))) (mul (XO (XO (XO (XO XH)))) acc))
    | Dc l -> of_hex_uint_acc l (add (XO (XO (XI XH))) (mul (XO (XO (XO (XO XH)))) acc))
    | Dd l -> of_hex_uint_acc l (add (XI (XO (XI XH))) (mul (XO (XO (XO (XO XH)))) acc))
    | De l -> of_hex_uint_acc l (add (XO (XI (XI XH))) (mul (XO (XO (XO (XO XH)))) acc))
    | Df l -> of_hex_uint_acc l (add (XI (XI (XI XH))) (mul (XO (XO (XO (XO XH)))) acc))

  (** val of_hex_uint : uint0 -> n **)

  let rec of_hex_uint = function
  | Nil1 -> N0
  | D10 l -> of_hex_uint l
  | D11 l -> Npos (of_hex_uint_acc l XH)
  | D12 l -> Npos (of_hex_uint_acc l (XO XH))
  | D13 l -> Npos (of_hex_uint_acc l (XI XH))
  | D14 l -> Npos (of_hex_uint_acc l (XO (XO XH)))
  | D15 l -> Npos (of_hex_uint_acc l (XI (XO XH)))
  | D16 l -> Npos (of_hex_uint_acc l (XO (XI XH)))
  | D17 l -> Npos (of_hex_uint_acc l (XI (XI XH)))
  | D18 l -> Npos (of_hex_uint_acc l (XO (XO (XO XH))))
  | D19 l -> Npos (of_hex_uint_acc l (XI (XO (XO XH))))
  | Da l -> Npos (of_hex_uint_acc l (XO (XI (XO XH))))
  | Db l -> Npos (of_hex_uint_acc l (XI (XI (XO XH))))
  | Dc l -> Npos (of_hex_uint_acc l (XO (XO (XI XH))))
  | Dd l -> Npos (of_hex_uint_acc l (XI (XO (XI XH))))
  | De l -> Npos (of_hex_uint_acc l (XO (XI (XI XH))))
  | Df l -> Npos (of_hex_uint_acc l (XI (XI (XI XH))))

  (** val of_num_uint : uint1 -> n **)

  let of_num_uint = function
  | UIntDec d0 -> of_uint d0
  | UIntHex d0 -> of_hex_uint d0

  (** val of_int : int -> positive option **)

  let of_int = function
  | Pos d0 -> (match of_uint d0 with
               | N0 -> None
               | Npos p -> Some p)
  | Neg _ -> None

  (** val of_hex_int : int0 -> positive option **)

  let of_hex_int = function
  | Pos0 d0 -> (match of_hex_uint d0 with
                | N0 -> None
                | Npos p -> Some p)
  | Neg0 _ -> None

  (** val of_num_int : int1 -> positive option **)

  let of_num_int = function
  | IntDec d0 -> of_int d0
  | IntHex d0 -> of_hex_int d0

  (** val to_little_uint : positive -> uint **)

  let rec to_little_uint = function
  | XI p0 -> Little.succ_double (to_little_uint p0)
  | XO p0 -> Little.double (to_little_uint p0)
  | XH -> D1 Nil0

  (** val to_uint : positive -> uint **)

  let to_uint p =
    rev (to_little_uint p)

  (** val to_little_hex_uint : positive -> uint0 **)

  let rec to_little_hex_uint = function
  | XI p0 -> Coq_Little.succ_double (to_little_hex_uint p0)
  | XO p0 -> Coq_Little.double (to_little_hex_uint p0)
  | XH -> D11 Nil1

  (** val to_hex_uint : positive -> uint0 **)

  let to_hex_uint p =
    rev0 (to_little_hex_uint p)

  (** val to_num_uint : positive -> uint1 **)

  let to_num_uint p =
    UIntDec (to_uint p)

  (** val to_int : positive -> int **)

  let to_int n0 =
    Pos (to_uint n0)

  (** val to_hex_int : positive -> int0 **)

  let to_hex_int p =
    Pos0 (to_hex_uint p)

  (** val to_num_int : positive -> int1 **)

  let to_num_int n0 =
    IntDec (to_int n0)

  (** val eq_dec : positive -> positive -> sumbool **)

  let rec eq_dec p x0 =
    match p with
    | XI p0 -> (match x0 with
                | XI p1 -> eq_dec p0 p1
                | _ -> Right)
    | XO p0 -> (match x0 with
                | XO p1 -> eq_dec p0 p1
                | _ -> Right)
    | XH -> (match x0 with
             | XH -> Left
             | _ -> Right)

  (** val peano_rect : 'a1 -> (positive -> 'a1 -> 'a1) -> positive -> 'a1 **)

  let rec peano_rect a f p =
    let f2 = peano_rect (f XH a) (fun p0 x0 -> f (succ (XO p0)) (f (XO p0) x0)) in
    (match p with
     | XI q -> f (XO q) (f2 q)
     | XO q -> f2 q
     | XH -> a)

  (** val peano_rec : 'a1 -> (positive -> 'a1 -> 'a1) -> positive -> 'a1 **)

  let peano_rec =
    peano_rect

  type coq_PeanoView =
  | PeanoOne
  | PeanoSucc of positive * coq_PeanoView

  (** val coq_PeanoView_rect :
      'a1 -> (positive -> coq_PeanoView -> 'a1 -> 'a1) -> positive -> coq_PeanoView -> 'a1 **)

  let rec coq_PeanoView_rect f f0 _ = function
  | PeanoOne -> f
  | PeanoSucc (p0, p1) -> f0 p0 p1 (coq_PeanoView_rect f f0 p0 p1)

  (** val coq_PeanoView_rec :
      'a1 -> (positive -> coq_PeanoView -> 'a1 -> 'a1) -> positive -> coq_PeanoView -> 'a1 **)

  let rec coq_PeanoView_rec f f0 _ = function
  | PeanoOne -> f
  | PeanoSucc (p0, p1) -> f0 p0 p1 (coq_PeanoView_rec f f0 p0 p1)

  (** val peanoView_xO : positive -> coq_PeanoView -> coq_PeanoView **)

  let rec peanoView_xO _ = function
  | PeanoOne -> PeanoSucc (XH, PeanoOne)
  | PeanoSucc (p0, q0) -> PeanoSucc ((succ (XO p0)), (PeanoSucc ((XO p0), (peanoView_xO p0 q0))))

  (** val peanoView_xI : positive -> coq_PeanoView -> coq_PeanoView **)

  let rec peanoView_xI _ = function
  | PeanoOne -> PeanoSucc ((succ XH), (PeanoSucc (XH, PeanoOne)))
  | PeanoSucc (p0, q0) -> PeanoSucc ((succ (XI p0)), (PeanoSucc ((XI p0), (peanoView_xI p0 q0))))

  (** val peanoView : positive -> coq_PeanoView **)

  let rec peanoView = function
  | XI p0 -> peanoView_xI p0 (peanoView p0)
  | XO p0 -> peanoView_xO p0 (peanoView p0)
  | XH -> PeanoOne

  (** val coq_PeanoView_iter : 'a1 -> (positive -> 'a1 -> 'a1) -> positive -> coq_PeanoView -> 'a1 **)

  let rec coq_PeanoView_iter a f _ = function
  | PeanoOne -> a
  | PeanoSucc (p0, q0) -> f p0 (coq_PeanoView_iter a f p0 q0)

  (** val eqb_spec : positive -> positive -> reflect **)

  let eqb_spec x0 y =
    iff_reflect (eqb x0 y)

  (** val switch_Eq : comparison -> comparison -> comparison **)

  let switch_Eq c = function
  | Eq -> c
  | x0 -> x0

  (** val mask2cmp : mask -> comparison **)

  let mask2cmp = function
  | IsNul -> Eq
  | IsPos _ -> Gt
  | IsNeg -> Lt

  (** val leb_spec0 : positive -> positive -> reflect **)

  let leb_spec0 x0 y =
    iff_reflect (leb x0 y)

  (** val ltb_spec0 : positive -> positive -> reflect **)

  let ltb_spec0 x0 y =
    iff_reflect (ltb x0 y)

  module Private_Tac =
   struct
   end

  module Private_Dec =
   struct
    (** val max_case_strong :
        positive -> positive -> (positive -> positive -> __ -> 'a1 -> 'a1) -> (__ -> 'a1) -> (__ -> 'a1) -> 'a1 **)

    let max_case_strong n0 m compat hl hr =
      let c = compSpec2Type n0 m (compare n0 m) in
      (match c with
       | CompGtT -> compat n0 (max n0 m) __ (hl __)
       | _ -> compat m (max n0 m) __ (hr __))

    (** val max_case : positive -> positive -> (positive -> positive -> __ -> 'a1 -> 'a1) -> 'a1 -> 'a1 -> 'a1 **)

    let max_case n0 m x0 x1 x2 =
      max_case_strong n0 m x0 (fun _ -> x1) (fun _ -> x2)

    (** val max_dec : positive -> positive -> sumbool **)

    let max_dec n0 m =
      max_case n0 m (fun _ _ _ h0 -> h0) Left Right

    (** val min_case_strong :
        positive -> positive -> (positive -> positive -> __ -> 'a1 -> 'a1) -> (__ -> 'a1) -> (__ -> 'a1) -> 'a1 **)

    let min_case_strong n0 m compat hl hr =
      let c = compSpec2Type n0 m (compare n0 m) in
      (match c with
       | CompGtT -> compat m (min n0 m) __ (hr __)
       | _ -> compat n0 (min n0 m) __ (hl __))

    (** val min_case : positive -> positive -> (positive -> positive -> __ -> 'a1 -> 'a1) -> 'a1 -> 'a1 -> 'a1 **)

    let min_case n0 m x0 x1 x2 =
      min_case_strong n0 m x0 (fun _ -> x1) (fun _ -> x2)

    (** val min_dec : positive -> positive -> sumbool **)

    let min_dec n0 m =
      min_case n0 m (fun _ _ _ h0 -> h0) Left Right
   end

  (** val max_case_strong : positive -> positive -> (__ -> 'a1) -> (__ -> 'a1) -> 'a1 **)

  let max_case_strong n0 m x0 x1 =
    Private_Dec.max_case_strong n0 m (fun _ _ _ x2 -> x2) x0 x1

  (** val max_case : positive -> positive -> 'a1 -> 'a1 -> 'a1 **)

  let max_case n0 m x0 x1 =
    max_case_strong n0 m (fun _ -> x0) (fun _ -> x1)

  (** val max_dec : positive -> positive -> sumbool **)

  let max_dec =
    Private_Dec.max_dec

  (** val min_case_strong : positive -> positive -> (__ -> 'a1) -> (__ -> 'a1) -> 'a1 **)

  let min_case_strong n0 m x0 x1 =
    Private_Dec.min_case_strong n0 m (fun _ _ _ x2 -> x2) x0 x1

  (** val min_case : positive -> positive -> 'a1 -> 'a1 -> 'a1 **)

  let min_case n0 m x0 x1 =
    min_case_strong n0 m (fun _ -> x0) (fun _ -> x1)

  (** val min_dec : positive -> positive -> sumbool **)

  let min_dec =
    Private_Dec.min_dec
 end

(** val rev1 : 'a1 list -> 'a1 list **)

let rec rev1 = function
| Nil -> Nil
| Cons (x0, l') -> app (rev1 l') (Cons (x0, Nil))

(** val rev_append : 'a1 list -> 'a1 list -> 'a1 list **)

let rec rev_append l l' =
  match l with
  | Nil -> l'
  | Cons (a, l0) -> rev_append l0 (Cons (a, l'))

(** val map : ('a1 -> 'a2) -> 'a1 list -> 'a2 list **)

let rec map f = function
| Nil -> Nil
| Cons (a, t0) -> Cons ((f a), (map f t0))

(** val fold_left : ('a1 -> 'a2 -> 'a1) -> 'a2 list -> 'a1 -> 'a1 **)

let rec fold_left f l a0 =
  match l with
  | Nil -> a0
  | Cons (b, t0) -> fold_left f t0 (f a0 b)

(** val fold_right : ('a2 -> 'a1 -> 'a1) -> 'a1 -> 'a2 list -> 'a1 **)

let rec fold_right f a0 = function
| Nil -> a0
| Cons (b, t0) -> f b (fold_right f a0 t0)

(** val existsb : ('a1 -> bool) -> 'a1 list -> bool **)

let rec existsb f = function
| Nil -> False
| Cons (a, l0) -> (match f a with
                   | True -> True
                   | False -> existsb f l0)

(** val forallb : ('a1 -> bool) -> 'a1 list -> bool **)

let rec forallb f = function
| Nil -> True
| Cons (a, l0) -> (match f a with
                   | True -> forallb f l0
                   | False -> False)

(** val filter : ('a1 -> bool) -> 'a1 list -> 'a1 list **)

let rec filter f = function
| Nil -> Nil
| Cons (x0, l0) -> (match f x0 with
                    | True -> Cons (x0, (filter f l0))
                    | False -> filter f l0)

(** val partition : ('a1 -> bool) -> 'a1 list -> ('a1 list, 'a1 list) prod **)

let rec partition f = function
| Nil -> Pair (Nil, Nil)
| Cons (x0, tl) ->
  let Pair (g, d) = partition f tl in
  (match f x0 with
   | True -> Pair ((Cons (x0, g)), d)
   | False -> Pair (g, (Cons (x0, d))))

module Positive_as_OT = Coq_Pos

module MakeListOrdering =
 functor (O:OrderedType) ->
 struct
  module MO = OrderedTypeFacts(O)
 end

type color =
| Red
| Black

module Color =
 struct
  type t = color
 end

module Make =
 functor (X:OrderedType) ->
 struct
  module Raw =
   struct
    type elt = X.t

    type tree =
    | Leaf
    | Node of Color.t * tree * X.t * tree

    (** val empty : tree **)

    let empty =
      Leaf

    (** val is_empty : tree -> bool **)

    let is_empty = function
    | Leaf -> True
    | Node (_, _, _, _) -> False

    (** val mem : X.t -> tree -> bool **)

    let rec mem x0 = function
    | Leaf -> False
    | Node (_, l, k, r) -> (match X.compare x0 k with
                            | Eq -> True
                            | Lt -> mem x0 l
                            | Gt -> mem x0 r)

    (** val min_elt : tree -> elt option **)

    let rec min_elt = function
    | Leaf -> None
    | Node (_, l, x0, _) -> (match l with
                             | Leaf -> Some x0
                             | Node (_, _, _, _) -> min_elt l)

    (** val max_elt : tree -> elt option **)

    let rec max_elt = function
    | Leaf -> None
    | Node (_, _, x0, r) -> (match r with
                             | Leaf -> Some x0
                             | Node (_, _, _, _) -> max_elt r)

    (** val choose : tree -> elt option **)

    let choose =
      min_elt

    (** val fold : (elt -> 'a1 -> 'a1) -> tree -> 'a1 -> 'a1 **)

    let rec fold f t0 base =
      match t0 with
      | Leaf -> base
      | Node (_, l, x0, r) -> fold f r (f x0 (fold f l base))

    (** val elements_aux : X.t list -> tree -> X.t list **)

    let rec elements_aux acc = function
    | Leaf -> acc
    | Node (_, l, x0, r) -> elements_aux (Cons (x0, (elements_aux acc r))) l

    (** val elements : tree -> X.t list **)

    let elements =
      elements_aux Nil

    (** val rev_elements_aux : X.t list -> tree -> X.t list **)

    let rec rev_elements_aux acc = function
    | Leaf -> acc
    | Node (_, l, x0, r) -> rev_elements_aux (Cons (x0, (rev_elements_aux acc l))) r

    (** val rev_elements : tree -> X.t list **)

    let rev_elements =
      rev_elements_aux Nil

    (** val cardinal : tree -> nat **)

    let rec cardinal = function
    | Leaf -> O
    | Node (_, l, _, r) -> S (add (cardinal l) (cardinal r))

    (** val maxdepth : tree -> nat **)

    let rec maxdepth = function
    | Leaf -> O
    | Node (_, l, _, r) -> S (max (maxdepth l) (maxdepth r))

    (** val mindepth : tree -> nat **)

    let rec mindepth = function
    | Leaf -> O
    | Node (_, l, _, r) -> S (min (mindepth l) (mindepth r))

    (** val for_all : (elt -> bool) -> tree -> bool **)

    let rec for_all f = function
    | Leaf -> True
    | Node (_, l, x0, r) ->
      (match match f x0 with
             | True -> for_all f l
             | False -> False with
       | True -> for_all f r
       | False -> False)

    (** val exists_ : (elt -> bool) -> tree -> bool **)

    let rec exists_ f = function
    | Leaf -> False
    | Node (_, l, x0, r) ->
      (match match f x0 with
             | True -> True
             | False -> exists_ f l with
       | True -> True
       | False -> exists_ f r)

    type enumeration =
    | End
    | More of elt * tree * enumeration

    (** val cons : tree -> enumeration -> enumeration **)

    let rec cons s e =
      match s with
      | Leaf -> e
      | Node (_, l, x0, r) -> cons l (More (x0, r, e))

    (** val compare_more : X.t -> (enumeration -> comparison) -> enumeration -> comparison **)

    let compare_more x1 cont = function
    | End -> Gt
    | More (x2, r2, e3) -> (match X.compare x1 x2 with
                            | Eq -> cont (cons r2 e3)
                            | x0 -> x0)

    (** val compare_cont : tree -> (enumeration -> comparison) -> enumeration -> comparison **)

    let rec compare_cont s1 cont e2 =
      match s1 with
      | Leaf -> cont e2
      | Node (_, l1, x1, r1) -> compare_cont l1 (compare_more x1 (compare_cont r1 cont)) e2

    (** val compare_end : enumeration -> comparison **)

    let compare_end = function
    | End -> Eq
    | More (_, _, _) -> Lt

    (** val compare : tree -> tree -> comparison **)

    let compare s1 s2 =
      compare_cont s1 compare_end (cons s2 End)

    (** val equal : tree -> tree -> bool **)

    let equal s1 s2 =
      match compare s1 s2 with
      | Eq -> True
      | _ -> False

    (** val subsetl : (tree -> bool) -> X.t -> tree -> bool **)

    let rec subsetl subset_l1 x1 s2 = match s2 with
    | Leaf -> False
    | Node (_, l2, x2, r2) ->
      (match X.compare x1 x2 with
       | Eq -> subset_l1 l2
       | Lt -> subsetl subset_l1 x1 l2
       | Gt -> (match mem x1 r2 with
                | True -> subset_l1 s2
                | False -> False))

    (** val subsetr : (tree -> bool) -> X.t -> tree -> bool **)

    let rec subsetr subset_r1 x1 s2 = match s2 with
    | Leaf -> False
    | Node (_, l2, x2, r2) ->
      (match X.compare x1 x2 with
       | Eq -> subset_r1 r2
       | Lt -> (match mem x1 l2 with
                | True -> subset_r1 s2
                | False -> False)
       | Gt -> subsetr subset_r1 x1 r2)

    (** val subset : tree -> tree -> bool **)

    let rec subset s1 s2 =
      match s1 with
      | Leaf -> True
      | Node (_, l1, x1, r1) ->
        (match s2 with
         | Leaf -> False
         | Node (_, l2, x2, r2) ->
           (match X.compare x1 x2 with
            | Eq -> (match subset l1 l2 with
                     | True -> subset r1 r2
                     | False -> False)
            | Lt -> (match subsetl (subset l1) x1 l2 with
                     | True -> subset r1 s2
                     | False -> False)
            | Gt -> (match subsetr (subset r1) x1 r2 with
                     | True -> subset l1 s2
                     | False -> False)))

    type t = tree

    (** val singleton : elt -> tree **)

    let singleton k =
      Node (Black, Leaf, k, Leaf)

    (** val makeBlack : tree -> tree **)

    let makeBlack = function
    | Leaf -> Leaf
    | Node (_, a, x0, b) -> Node (Black, a, x0, b)

    (** val makeRed : tree -> tree **)

    let makeRed = function
    | Leaf -> Leaf
    | Node (_, a, x0, b) -> Node (Red, a, x0, b)

    (** val lbal : tree -> X.t -> tree -> tree **)

    let lbal l k r =
      match l with
      | Leaf -> Node (Black, l, k, r)
      | Node (t0, a, x0, c) ->
        (match t0 with
         | Red ->
           (match a with
            | Leaf ->
              (match c with
               | Leaf -> Node (Black, l, k, r)
               | Node (t1, b, y, c0) ->
                 (match t1 with
                  | Red -> Node (Red, (Node (Black, a, x0, b)), y, (Node (Black, c0, k, r)))
                  | Black -> Node (Black, l, k, r)))
            | Node (t1, a0, x1, b) ->
              (match t1 with
               | Red -> Node (Red, (Node (Black, a0, x1, b)), x0, (Node (Black, c, k, r)))
               | Black ->
                 (match c with
                  | Leaf -> Node (Black, l, k, r)
                  | Node (t2, b0, y, c0) ->
                    (match t2 with
                     | Red -> Node (Red, (Node (Black, a, x0, b0)), y, (Node (Black, c0, k, r)))
                     | Black -> Node (Black, l, k, r)))))
         | Black -> Node (Black, l, k, r))

    (** val rbal : tree -> X.t -> tree -> tree **)

    let rbal l k r = match r with
    | Leaf -> Node (Black, l, k, r)
    | Node (t0, b, y, d) ->
      (match t0 with
       | Red ->
         (match b with
          | Leaf ->
            (match d with
             | Leaf -> Node (Black, l, k, r)
             | Node (t1, c, z0, d0) ->
               (match t1 with
                | Red -> Node (Red, (Node (Black, l, k, b)), y, (Node (Black, c, z0, d0)))
                | Black -> Node (Black, l, k, r)))
          | Node (t1, b0, y0, c) ->
            (match t1 with
             | Red -> Node (Red, (Node (Black, l, k, b0)), y0, (Node (Black, c, y, d)))
             | Black ->
               (match d with
                | Leaf -> Node (Black, l, k, r)
                | Node (t2, c0, z0, d0) ->
                  (match t2 with
                   | Red -> Node (Red, (Node (Black, l, k, b)), y, (Node (Black, c0, z0, d0)))
                   | Black -> Node (Black, l, k, r)))))
       | Black -> Node (Black, l, k, r))

    (** val rbal' : tree -> X.t -> tree -> tree **)

    let rbal' l k r = match r with
    | Leaf -> Node (Black, l, k, r)
    | Node (t0, b, z0, d) ->
      (match t0 with
       | Red ->
         (match b with
          | Leaf ->
            (match d with
             | Leaf -> Node (Black, l, k, r)
             | Node (t1, c, z1, d0) ->
               (match t1 with
                | Red -> Node (Red, (Node (Black, l, k, b)), z0, (Node (Black, c, z1, d0)))
                | Black -> Node (Black, l, k, r)))
          | Node (t1, b0, y, c) ->
            (match t1 with
             | Red ->
               (match d with
                | Leaf -> Node (Red, (Node (Black, l, k, b0)), y, (Node (Black, c, z0, d)))
                | Node (t2, c0, z1, d0) ->
                  (match t2 with
                   | Red -> Node (Red, (Node (Black, l, k, b)), z0, (Node (Black, c0, z1, d0)))
                   | Black -> Node (Red, (Node (Black, l, k, b0)), y, (Node (Black, c, z0, d)))))
             | Black ->
               (match d with
                | Leaf -> Node (Black, l, k, r)
                | Node (t2, c0, z1, d0) ->
                  (match t2 with
                   | Red -> Node (Red, (Node (Black, l, k, b)), z0, (Node (Black, c0, z1, d0)))
                   | Black -> Node (Black, l, k, r)))))
       | Black -> Node (Black, l, k, r))

    (** val lbalS : tree -> X.t -> tree -> tree **)

    let lbalS l k r =
      match l with
      | Leaf ->
        (match r with
         | Leaf -> Node (Red, l, k, r)
         | Node (t0, a, z0, c) ->
           (match t0 with
            | Red ->
              (match a with
               | Leaf -> Node (Red, l, k, r)
               | Node (t1, a0, y, b) ->
                 (match t1 with
                  | Red -> Node (Red, l, k, r)
                  | Black -> Node (Red, (Node (Black, l, k, a0)), y, (rbal' b z0 (makeRed c)))))
            | Black -> rbal' l k (Node (Red, a, z0, c))))
      | Node (t0, a, x0, b) ->
        (match t0 with
         | Red -> Node (Red, (Node (Black, a, x0, b)), k, r)
         | Black ->
           (match r with
            | Leaf -> Node (Red, l, k, r)
            | Node (t1, a0, z0, c) ->
              (match t1 with
               | Red ->
                 (match a0 with
                  | Leaf -> Node (Red, l, k, r)
                  | Node (t2, a1, y, b0) ->
                    (match t2 with
                     | Red -> Node (Red, l, k, r)
                     | Black -> Node (Red, (Node (Black, l, k, a1)), y, (rbal' b0 z0 (makeRed c)))))
               | Black -> rbal' l k (Node (Red, a0, z0, c)))))

    (** val rbalS : tree -> X.t -> tree -> tree **)

    let rbalS l k r = match r with
    | Leaf ->
      (match l with
       | Leaf -> Node (Red, l, k, r)
       | Node (t0, a, x0, b) ->
         (match t0 with
          | Red ->
            (match b with
             | Leaf -> Node (Red, l, k, r)
             | Node (t1, b0, y, c) ->
               (match t1 with
                | Red -> Node (Red, l, k, r)
                | Black -> Node (Red, (lbal (makeRed a) x0 b0), y, (Node (Black, c, k, r)))))
          | Black -> lbal (Node (Red, a, x0, b)) k r))
    | Node (t0, b, y, c) ->
      (match t0 with
       | Red -> Node (Red, l, k, (Node (Black, b, y, c)))
       | Black ->
         (match l with
          | Leaf -> Node (Red, l, k, r)
          | Node (t1, a, x0, b0) ->
            (match t1 with
             | Red ->
               (match b0 with
                | Leaf -> Node (Red, l, k, r)
                | Node (t2, b1, y0, c0) ->
                  (match t2 with
                   | Red -> Node (Red, l, k, r)
                   | Black -> Node (Red, (lbal (makeRed a) x0 b1), y0, (Node (Black, c0, k, r)))))
             | Black -> lbal (Node (Red, a, x0, b0)) k r)))

    (** val ins : X.t -> tree -> tree **)

    let rec ins x0 s = match s with
    | Leaf -> Node (Red, Leaf, x0, Leaf)
    | Node (c, l, y, r) ->
      (match X.compare x0 y with
       | Eq -> s
       | Lt -> (match c with
                | Red -> Node (Red, (ins x0 l), y, r)
                | Black -> lbal (ins x0 l) y r)
       | Gt -> (match c with
                | Red -> Node (Red, l, y, (ins x0 r))
                | Black -> rbal l y (ins x0 r)))

    (** val add : X.t -> tree -> tree **)

    let add x0 s =
      makeBlack (ins x0 s)

    (** val append : tree -> tree -> tree **)

    let rec append l = match l with
    | Leaf -> (fun r -> r)
    | Node (lc, ll, lx, lr) ->
      let rec append_l r = match r with
      | Leaf -> l
      | Node (rc, rl, rx, rr) ->
        (match lc with
         | Red ->
           (match rc with
            | Red ->
              let lrl = append lr rl in
              (match lrl with
               | Leaf -> Node (Red, ll, lx, (Node (Red, lrl, rx, rr)))
               | Node (t0, lr', x0, rl') ->
                 (match t0 with
                  | Red -> Node (Red, (Node (Red, ll, lx, lr')), x0, (Node (Red, rl', rx, rr)))
                  | Black -> Node (Red, ll, lx, (Node (Red, lrl, rx, rr)))))
            | Black -> Node (Red, ll, lx, (append lr r)))
         | Black ->
           (match rc with
            | Red -> Node (Red, (append_l rl), rx, rr)
            | Black ->
              let lrl = append lr rl in
              (match lrl with
               | Leaf -> lbalS ll lx (Node (Black, lrl, rx, rr))
               | Node (t0, lr', x0, rl') ->
                 (match t0 with
                  | Red -> Node (Red, (Node (Black, ll, lx, lr')), x0, (Node (Black, rl', rx, rr)))
                  | Black -> lbalS ll lx (Node (Black, lrl, rx, rr))))))
      in append_l

    (** val del : X.t -> tree -> tree **)

    let rec del x0 = function
    | Leaf -> Leaf
    | Node (_, a, y, b) ->
      (match X.compare x0 y with
       | Eq -> append a b
       | Lt ->
         (match a with
          | Leaf -> Node (Red, (del x0 a), y, b)
          | Node (t1, _, _, _) ->
            (match t1 with
             | Red -> Node (Red, (del x0 a), y, b)
             | Black -> lbalS (del x0 a) y b))
       | Gt ->
         (match b with
          | Leaf -> Node (Red, a, y, (del x0 b))
          | Node (t1, _, _, _) ->
            (match t1 with
             | Red -> Node (Red, a, y, (del x0 b))
             | Black -> rbalS a y (del x0 b))))

    (** val remove : X.t -> tree -> tree **)

    let remove x0 t0 =
      makeBlack (del x0 t0)

    (** val delmin : tree -> elt -> tree -> (elt, tree) prod **)

    let rec delmin l x0 r =
      match l with
      | Leaf -> Pair (x0, r)
      | Node (lc, ll, lx, lr) ->
        let Pair (k, l') = delmin ll lx lr in
        (match lc with
         | Red -> Pair (k, (Node (Red, l', x0, r)))
         | Black -> Pair (k, (lbalS l' x0 r)))

    (** val remove_min : tree -> (elt, tree) prod option **)

    let remove_min = function
    | Leaf -> None
    | Node (_, l, x0, r) -> let Pair (k, t1) = delmin l x0 r in Some (Pair (k, (makeBlack t1)))

    (** val bogus : (tree, elt list) prod **)

    let bogus =
      Pair (Leaf, Nil)

    (** val treeify_zero : elt list -> (tree, elt list) prod **)

    let treeify_zero acc =
      Pair (Leaf, acc)

    (** val treeify_one : elt list -> (tree, elt list) prod **)

    let treeify_one = function
    | Nil -> bogus
    | Cons (x0, acc0) -> Pair ((Node (Red, Leaf, x0, Leaf)), acc0)

    (** val treeify_cont :
        (elt list -> (tree, elt list) prod) -> (elt list -> (tree, elt list) prod) -> elt list -> (tree, elt
        list) prod **)

    let treeify_cont f g acc =
      let Pair (l, l0) = f acc in
      (match l0 with
       | Nil -> bogus
       | Cons (x0, acc0) -> let Pair (r, acc1) = g acc0 in Pair ((Node (Black, l, x0, r)), acc1))

    (** val treeify_aux : bool -> positive -> elt list -> (tree, elt list) prod **)

    let rec treeify_aux pred0 = function
    | XI n1 -> treeify_cont (treeify_aux False n1) (treeify_aux pred0 n1)
    | XO n1 -> treeify_cont (treeify_aux pred0 n1) (treeify_aux True n1)
    | XH -> (match pred0 with
             | True -> treeify_zero
             | False -> treeify_one)

    (** val plength_aux : elt list -> positive -> positive **)

    let rec plength_aux l p =
      match l with
      | Nil -> p
      | Cons (_, l0) -> plength_aux l0 (Coq_Pos.succ p)

    (** val plength : elt list -> positive **)

    let plength l =
      plength_aux l XH

    (** val treeify : elt list -> tree **)

    let treeify l =
      fst (treeify_aux True (plength l) l)

    (** val filter_aux : (elt -> bool) -> tree -> X.t list -> X.t list **)

    let rec filter_aux f s acc =
      match s with
      | Leaf -> acc
      | Node (_, l, k, r) ->
        let acc0 = filter_aux f r acc in
        (match f k with
         | True -> filter_aux f l (Cons (k, acc0))
         | False -> filter_aux f l acc0)

    (** val filter : (elt -> bool) -> t -> t **)

    let filter f s =
      treeify (filter_aux f s Nil)

    (** val partition_aux : (elt -> bool) -> tree -> X.t list -> X.t list -> (X.t list, X.t list) prod **)

    let rec partition_aux f s acc1 acc2 =
      match s with
      | Leaf -> Pair (acc1, acc2)
      | Node (_, sl, k, sr) ->
        let Pair (acc3, acc4) = partition_aux f sr acc1 acc2 in
        (match f k with
         | True -> partition_aux f sl (Cons (k, acc3)) acc4
         | False -> partition_aux f sl acc3 (Cons (k, acc4)))

    (** val partition : (elt -> bool) -> t -> (t, t) prod **)

    let partition f s =
      let Pair (ok, ko) = partition_aux f s Nil Nil in Pair ((treeify ok), (treeify ko))

    (** val union_list : elt list -> elt list -> elt list -> elt list **)

    let rec union_list l1 = match l1 with
    | Nil -> rev_append
    | Cons (x0, l1') ->
      let rec union_l1 l2 acc =
        match l2 with
        | Nil -> rev_append l1 acc
        | Cons (y, l2') ->
          (match X.compare x0 y with
           | Eq -> union_list l1' l2' (Cons (x0, acc))
           | Lt -> union_l1 l2' (Cons (y, acc))
           | Gt -> union_list l1' l2 (Cons (x0, acc)))
      in union_l1

    (** val linear_union : tree -> tree -> tree **)

    let linear_union s1 s2 =
      treeify (union_list (rev_elements s1) (rev_elements s2) Nil)

    (** val inter_list : X.t list -> elt list -> elt list -> elt list **)

    let rec inter_list = function
    | Nil -> (fun _ acc -> acc)
    | Cons (x0, l1') ->
      let rec inter_l1 l2 acc =
        match l2 with
        | Nil -> acc
        | Cons (y, l2') ->
          (match X.compare x0 y with
           | Eq -> inter_list l1' l2' (Cons (x0, acc))
           | Lt -> inter_l1 l2' acc
           | Gt -> inter_list l1' l2 acc)
      in inter_l1

    (** val linear_inter : tree -> tree -> tree **)

    let linear_inter s1 s2 =
      treeify (inter_list (rev_elements s1) (rev_elements s2) Nil)

    (** val diff_list : elt list -> elt list -> elt list -> elt list **)

    let rec diff_list l1 = match l1 with
    | Nil -> (fun _ acc -> acc)
    | Cons (x0, l1') ->
      let rec diff_l1 l2 acc =
        match l2 with
        | Nil -> rev_append l1 acc
        | Cons (y, l2') ->
          (match X.compare x0 y with
           | Eq -> diff_list l1' l2' acc
           | Lt -> diff_l1 l2' acc
           | Gt -> diff_list l1' l2 (Cons (x0, acc)))
      in diff_l1

    (** val linear_diff : tree -> tree -> tree **)

    let linear_diff s1 s2 =
      treeify (diff_list (rev_elements s1) (rev_elements s2) Nil)

    (** val skip_red : tree -> tree **)

    let skip_red t0 = match t0 with
    | Leaf -> t0
    | Node (t1, t', _, _) -> (match t1 with
                              | Red -> t'
                              | Black -> t0)

    (** val skip_black : tree -> tree **)

    let skip_black t0 =
      match skip_red t0 with
      | Leaf -> Leaf
      | Node (t1, t', t2, t3) -> (match t1 with
                                  | Red -> Node (Red, t', t2, t3)
                                  | Black -> t')

    (** val compare_height : tree -> tree -> tree -> tree -> comparison **)

    let rec compare_height s1x s1 s2 s2x =
      match skip_red s1x with
      | Leaf ->
        (match skip_red s1 with
         | Leaf -> (match skip_red s2x with
                    | Leaf -> Eq
                    | Node (_, _, _, _) -> Lt)
         | Node (_, s1', _, _) ->
           (match skip_red s2 with
            | Leaf -> Eq
            | Node (_, s2', _, _) ->
              (match skip_red s2x with
               | Leaf -> Eq
               | Node (_, s2x', _, _) -> compare_height Leaf s1' s2' (skip_black s2x'))))
      | Node (_, s1x', _, _) ->
        (match skip_red s1 with
         | Leaf ->
           (match skip_red s2 with
            | Leaf -> (match skip_red s2x with
                       | Leaf -> Gt
                       | Node (_, _, _, _) -> Lt)
            | Node (_, _, _, _) -> (match skip_red s2x with
                                    | Leaf -> Eq
                                    | Node (_, _, _, _) -> Lt))
         | Node (_, s1', _, _) ->
           (match skip_red s2 with
            | Leaf -> Gt
            | Node (_, s2', _, _) ->
              (match skip_red s2x with
               | Leaf -> compare_height (skip_black s1x') s1' s2' Leaf
               | Node (_, s2x', _, _) -> compare_height (skip_black s1x') s1' s2' (skip_black s2x'))))

    (** val union : t -> t -> t **)

    let union t1 t2 =
      match compare_height t1 t1 t2 t2 with
      | Eq -> linear_union t1 t2
      | Lt -> fold add t1 t2
      | Gt -> fold add t2 t1

    (** val diff : t -> t -> t **)

    let diff t1 t2 =
      match compare_height t1 t1 t2 t2 with
      | Eq -> linear_diff t1 t2
      | Lt -> filter (fun k -> negb (mem k t2)) t1
      | Gt -> fold remove t2 t1

    (** val inter : t -> t -> t **)

    let inter t1 t2 =
      match compare_height t1 t1 t2 t2 with
      | Eq -> linear_inter t1 t2
      | Lt -> filter (fun k -> mem k t2) t1
      | Gt -> filter (fun k -> mem k t1) t2

    (** val ltb_tree : X.t -> tree -> bool **)

    let rec ltb_tree x0 = function
    | Leaf -> True
    | Node (_, l, y, r) ->
      (match X.compare x0 y with
       | Gt -> (match ltb_tree x0 l with
                | True -> ltb_tree x0 r
                | False -> False)
       | _ -> False)

    (** val gtb_tree : X.t -> tree -> bool **)

    let rec gtb_tree x0 = function
    | Leaf -> True
    | Node (_, l, y, r) ->
      (match X.compare x0 y with
       | Lt -> (match gtb_tree x0 l with
                | True -> gtb_tree x0 r
                | False -> False)
       | _ -> False)

    (** val isok : tree -> bool **)

    let rec isok = function
    | Leaf -> True
    | Node (_, l, x0, r) ->
      (match match match isok l with
                   | True -> isok r
                   | False -> False with
             | True -> ltb_tree x0 l
             | False -> False with
       | True -> gtb_tree x0 r
       | False -> False)

    module MX = OrderedTypeFacts(X)

    type coq_R_min_elt =
    | R_min_elt_0 of tree
    | R_min_elt_1 of tree * Color.t * tree * X.t * tree
    | R_min_elt_2 of tree * Color.t * tree * X.t * tree * Color.t * tree * X.t * tree * elt option * coq_R_min_elt

    type coq_R_max_elt =
    | R_max_elt_0 of tree
    | R_max_elt_1 of tree * Color.t * tree * X.t * tree
    | R_max_elt_2 of tree * Color.t * tree * X.t * tree * Color.t * tree * X.t * tree * elt option * coq_R_max_elt

    module L = MakeListOrdering(X)

    (** val flatten_e : enumeration -> elt list **)

    let rec flatten_e = function
    | End -> Nil
    | More (x0, t0, r) -> Cons (x0, (app (elements t0) (flatten_e r)))

    (** val rcase : (tree -> X.t -> tree -> 'a1) -> (tree -> 'a1) -> tree -> 'a1 **)

    let rcase f g t0 = match t0 with
    | Leaf -> g t0
    | Node (t1, a, x0, b) -> (match t1 with
                              | Red -> f a x0 b
                              | Black -> g t0)

    (** val rrcase : (tree -> X.t -> tree -> X.t -> tree -> 'a1) -> (tree -> 'a1) -> tree -> 'a1 **)

    let rrcase f g t0 = match t0 with
    | Leaf -> g t0
    | Node (t1, a, x0, c) ->
      (match t1 with
       | Red ->
         (match a with
          | Leaf ->
            (match c with
             | Leaf -> g t0
             | Node (t2, b, y, c0) -> (match t2 with
                                       | Red -> f a x0 b y c0
                                       | Black -> g t0))
          | Node (t2, a0, x1, b) ->
            (match t2 with
             | Red -> f a0 x1 b x0 c
             | Black ->
               (match c with
                | Leaf -> g t0
                | Node (t3, b0, y, c0) -> (match t3 with
                                           | Red -> f a x0 b0 y c0
                                           | Black -> g t0))))
       | Black -> g t0)

    (** val rrcase' : (tree -> X.t -> tree -> X.t -> tree -> 'a1) -> (tree -> 'a1) -> tree -> 'a1 **)

    let rrcase' f g t0 = match t0 with
    | Leaf -> g t0
    | Node (t1, a, y, c) ->
      (match t1 with
       | Red ->
         (match a with
          | Leaf ->
            (match c with
             | Leaf -> g t0
             | Node (t2, b, y0, c0) -> (match t2 with
                                        | Red -> f a y b y0 c0
                                        | Black -> g t0))
          | Node (t2, a0, x0, b) ->
            (match t2 with
             | Red ->
               (match c with
                | Leaf -> f a0 x0 b y c
                | Node (t3, b0, y0, c0) -> (match t3 with
                                            | Red -> f a y b0 y0 c0
                                            | Black -> f a0 x0 b y c))
             | Black ->
               (match c with
                | Leaf -> g t0
                | Node (t3, b0, y0, c0) -> (match t3 with
                                            | Red -> f a y b0 y0 c0
                                            | Black -> g t0))))
       | Black -> g t0)
   end

  module E =
   struct
    type t = X.t

    (** val compare : t -> t -> comparison **)

    let compare =
      X.compare

    (** val eq_dec : t -> t -> sumbool **)

    let eq_dec =
      X.eq_dec
   end

  type elt = X.t

  type t_ = Raw.t
    (* singleton inductive, whose constructor was Mkt *)

  (** val this : t_ -> Raw.t **)

  let this t0 =
    t0

  type t = t_

  (** val mem : elt -> t -> bool **)

  let mem x0 s =
    Raw.mem x0 (this s)

  (** val add : elt -> t -> t **)

  let add x0 s =
    Raw.add x0 (this s)

  (** val remove : elt -> t -> t **)

  let remove x0 s =
    Raw.remove x0 (this s)

  (** val singleton : elt -> t **)

  let singleton =
    Raw.singleton

  (** val union : t -> t -> t **)

  let union s s' =
    Raw.union (this s) (this s')

  (** val inter : t -> t -> t **)

  let inter s s' =
    Raw.inter (this s) (this s')

  (** val diff : t -> t -> t **)

  let diff s s' =
    Raw.diff (this s) (this s')

  (** val equal : t -> t -> bool **)

  let equal s s' =
    Raw.equal (this s) (this s')

  (** val subset : t -> t -> bool **)

  let subset s s' =
    Raw.subset (this s) (this s')

  (** val empty : t **)

  let empty =
    Raw.empty

  (** val is_empty : t -> bool **)

  let is_empty s =
    Raw.is_empty (this s)

  (** val elements : t -> elt list **)

  let elements s =
    Raw.elements (this s)

  (** val choose : t -> elt option **)

  let choose s =
    Raw.choose (this s)

  (** val fold : (elt -> 'a1 -> 'a1) -> t -> 'a1 -> 'a1 **)

  let fold f s =
    Raw.fold f (this s)

  (** val cardinal : t -> nat **)

  let cardinal s =
    Raw.cardinal (this s)

  (** val filter : (elt -> bool) -> t -> t **)

  let filter f s =
    Raw.filter f (this s)

  (** val for_all : (elt -> bool) -> t -> bool **)

  let for_all f s =
    Raw.for_all f (this s)

  (** val exists_ : (elt -> bool) -> t -> bool **)

  let exists_ f s =
    Raw.exists_ f (this s)

  (** val partition : (elt -> bool) -> t -> (t, t) prod **)

  let partition f s =
    let p = Raw.partition f (this s) in Pair ((fst p), (snd p))

  (** val eq_dec : t -> t -> sumbool **)

  let eq_dec s0 s'0 =
    let b = Raw.equal s0 s'0 in (match b with
                                 | True -> Left
                                 | False -> Right)

  (** val compare : t -> t -> comparison **)

  let compare s s' =
    Raw.compare (this s) (this s')

  (** val min_elt : t -> elt option **)

  let min_elt s =
    Raw.min_elt (this s)

  (** val max_elt : t -> elt option **)

  let max_elt s =
    Raw.max_elt (this s)

  (** val mk_opt_t : (elt, Raw.t) prod option -> (elt, t) prod option **)

  let mk_opt_t = function
  | Some p -> let Pair (k, s') = p in Some (Pair (k, s'))
  | None -> None

  (** val remove_min : t_ -> (elt, t) prod option **)

  let remove_min s =
    mk_opt_t (Raw.remove_min (this s))
 end

(** val compose : ('a2 -> 'a3) -> ('a1 -> 'a2) -> 'a1 -> 'a3 **)

let compose g f a =
  g (f a)

module Ident = Positive_as_OT

(** val z2id : z -> Ident.t **)

let z2id = function
| Zpos p -> Coq_Pos.add p XH
| _ -> XH

(** val add_id : positive -> positive -> positive **)

let add_id =
  Coq_Pos.add

type var = Ident.t

type expr =
| Nil2
| Var of var

type pn_atom =
| Equ of expr * expr
| Nequ of expr * expr

type space_atom =
| Next of expr * expr
| Lseg of expr * expr

type assertion =
| Assertion of pn_atom list * space_atom list

type entailment =
| Entailment of assertion * assertion

(** val subst_expr : var -> expr -> expr -> expr **)

let subst_expr i t0 t' = match t' with
| Nil2 -> Nil2
| Var j -> (match Ident.eq_dec i j with
            | Left -> t0
            | Right -> t')

(** val subst_space : var -> expr -> space_atom -> space_atom **)

let subst_space i t0 = function
| Next (t1, t2) -> Next ((subst_expr i t0 t1), (subst_expr i t0 t2))
| Lseg (t1, t2) -> Lseg ((subst_expr i t0 t1), (subst_expr i t0 t2))

(** val subst_spaces : var -> expr -> space_atom list -> space_atom list **)

let subst_spaces i t0 =
  map (subst_space i t0)

(** val isGeq : comparison -> bool **)

let isGeq = function
| Lt -> False
| _ -> True

(** val insert : ('a1 -> 'a1 -> comparison) -> 'a1 -> 'a1 list -> 'a1 list **)

let rec insert cmp a l = match l with
| Nil -> Cons (a, Nil)
| Cons (h, t0) -> (match isGeq (cmp a h) with
                   | True -> Cons (a, l)
                   | False -> Cons (h, (insert cmp a t0)))

(** val rsort : ('a1 -> 'a1 -> comparison) -> 'a1 list -> 'a1 list **)

let rec rsort cmp = function
| Nil -> Nil
| Cons (h, t0) -> insert cmp h (rsort cmp t0)

(** val insert_uniq : ('a1 -> 'a1 -> comparison) -> 'a1 -> 'a1 list -> 'a1 list **)

let rec insert_uniq cmp a l = match l with
| Nil -> Cons (a, Nil)
| Cons (h, t0) -> (match cmp a h with
                   | Eq -> l
                   | Lt -> Cons (h, (insert_uniq cmp a t0))
                   | Gt -> Cons (a, l))

(** val rsort_uniq : ('a1 -> 'a1 -> comparison) -> 'a1 list -> 'a1 list **)

let rec rsort_uniq cmp = function
| Nil -> Nil
| Cons (h, t0) -> insert_uniq cmp h (rsort_uniq cmp t0)

(** val compare_list : ('a1 -> 'a1 -> comparison) -> 'a1 list -> 'a1 list -> comparison **)

let rec compare_list f xl yl =
  match xl with
  | Nil -> (match yl with
            | Nil -> Eq
            | Cons (_, _) -> Lt)
  | Cons (x0, xl') ->
    (match yl with
     | Nil -> Gt
     | Cons (y, yl') -> (match f x0 y with
                         | Eq -> compare_list f xl' yl'
                         | x1 -> x1))

type pure_atom =
| Eqv of expr * expr

(** val var1 : var **)

let var1 =
  z2id (Zpos XH)

(** val var0 : var **)

let var0 =
  z2id Z0

(** val var2 : var **)

let var2 =
  z2id (Zpos (XO XH))

(** val list_prio : var -> 'a1 list -> var -> var **)

let rec list_prio weight l p =
  match l with
  | Nil -> p
  | Cons (_, l') -> list_prio weight l' (add_id weight p)

(** val prio : pure_atom list -> pure_atom list -> var **)

let prio gamma delta =
  list_prio var2 gamma (list_prio var1 delta var0)

type clause =
| PureClause of pure_atom list * pure_atom list * var
| PosSpaceClause of pure_atom list * pure_atom list * space_atom list
| NegSpaceClause of pure_atom list * space_atom list * pure_atom list

(** val expr_cmp : expr -> expr -> comparison **)

let expr_cmp e e' =
  match e with
  | Nil2 -> (match e' with
             | Nil2 -> Eq
             | Var _ -> Lt)
  | Var v -> (match e' with
              | Nil2 -> Gt
              | Var v' -> Ident.compare v v')

(** val pure_atom_cmp : pure_atom -> pure_atom -> comparison **)

let pure_atom_cmp a a' =
  let Eqv (e1, e2) = a in let Eqv (e1', e2') = a' in (match expr_cmp e1 e1' with
                                                      | Eq -> expr_cmp e2 e2'
                                                      | x0 -> x0)

(** val order_eqv_pure_atom : pure_atom -> pure_atom **)

let order_eqv_pure_atom = function
| Eqv (i, j) -> (match expr_cmp i j with
                 | Lt -> Eqv (j, i)
                 | _ -> Eqv (i, j))

(** val nonreflex_atom : pure_atom -> bool **)

let nonreflex_atom = function
| Eqv (i, j) -> (match expr_cmp i j with
                 | Eq -> False
                 | _ -> True)

(** val normalize_atoms : pure_atom list -> pure_atom list **)

let normalize_atoms pa =
  rsort_uniq pure_atom_cmp (map order_eqv_pure_atom pa)

(** val mkPureClause : pure_atom list -> pure_atom list -> clause **)

let mkPureClause gamma delta =
  PureClause (gamma, delta, (prio gamma delta))

(** val order_eqv_clause : clause -> clause **)

let order_eqv_clause = function
| PureClause (pa, pa', _) -> mkPureClause (normalize_atoms (filter nonreflex_atom pa)) (normalize_atoms pa')
| PosSpaceClause (pa, pa', sa') ->
  PosSpaceClause ((normalize_atoms (filter nonreflex_atom pa)), (normalize_atoms pa'), sa')
| NegSpaceClause (pa, sa, pa') ->
  NegSpaceClause ((normalize_atoms (filter nonreflex_atom pa)), sa, (normalize_atoms pa'))

(** val mk_pureL : pn_atom -> clause **)

let mk_pureL = function
| Equ (x0, y) -> mkPureClause Nil (Cons ((order_eqv_pure_atom (Eqv (x0, y))), Nil))
| Nequ (x0, y) -> mkPureClause (Cons ((order_eqv_pure_atom (Eqv (x0, y))), Nil)) Nil

(** val mk_pureR : pn_atom list -> (pure_atom list, pure_atom list) prod **)

let rec mk_pureR = function
| Nil -> Pair (Nil, Nil)
| Cons (p, l') ->
  (match p with
   | Equ (x0, y) -> let Pair (p0, n0) = mk_pureR l' in Pair ((Cons ((order_eqv_pure_atom (Eqv (x0, y))), p0)), n0)
   | Nequ (x0, y) ->
     let Pair (p0, n0) = mk_pureR l' in Pair (p0, (Cons ((order_eqv_pure_atom (Eqv (x0, y))), n0))))

(** val cnf : entailment -> clause list **)

let cnf = function
| Entailment (a, a0) ->
  let Assertion (pureL, spaceL) = a in
  let Assertion (pureR, spaceR) = a0 in
  let Pair (p, n0) = mk_pureR pureR in
  app (map mk_pureL pureL)
    (app (Cons ((PosSpaceClause (Nil, Nil, spaceL)), Nil))
      (match spaceL with
       | Nil ->
         (match spaceR with
          | Nil -> Cons ((mkPureClause p n0), Nil)
          | Cons (_, _) -> Cons ((NegSpaceClause (p, spaceR, n0)), Nil))
       | Cons (_, _) -> Cons ((NegSpaceClause (p, spaceR, n0)), Nil)))

(** val pure_atom_gt : pure_atom -> pure_atom -> bool **)

let pure_atom_gt a b =
  match pure_atom_cmp a b with
  | Gt -> True
  | _ -> False

(** val pure_atom_eq : pure_atom -> pure_atom -> bool **)

let pure_atom_eq a b =
  match pure_atom_cmp a b with
  | Eq -> True
  | _ -> False

(** val expr_lt : expr -> expr -> bool **)

let expr_lt a b =
  match expr_cmp a b with
  | Lt -> True
  | _ -> False

(** val expr_eq : expr -> expr -> bool **)

let expr_eq a b =
  match expr_cmp a b with
  | Eq -> True
  | _ -> False

(** val expr_geq : expr -> expr -> bool **)

let expr_geq a b =
  match expr_cmp a b with
  | Lt -> False
  | _ -> True

(** val norm_pure_atom : pure_atom -> pure_atom **)

let norm_pure_atom = function
| Eqv (i, j) -> (match expr_lt i j with
                 | True -> Eqv (j, i)
                 | False -> Eqv (i, j))

(** val subst_pure : var -> expr -> pure_atom -> pure_atom **)

let subst_pure i t0 = function
| Eqv (t1, t2) -> Eqv ((subst_expr i t0 t1), (subst_expr i t0 t2))

(** val subst_pures : var -> expr -> pure_atom list -> pure_atom list **)

let subst_pures i t0 pa =
  map (subst_pure i t0) pa

(** val compare_space_atom : space_atom -> space_atom -> comparison **)

let compare_space_atom a b =
  match a with
  | Next (i, j) ->
    (match b with
     | Next (i', j') -> (match expr_cmp i i' with
                         | Eq -> expr_cmp j j'
                         | x0 -> x0)
     | Lseg (i', _) -> (match expr_cmp i i' with
                        | Eq -> Lt
                        | x0 -> x0))
  | Lseg (i, j) ->
    (match b with
     | Next (i', _) -> (match expr_cmp i i' with
                        | Eq -> Gt
                        | x0 -> x0)
     | Lseg (i', j') -> (match expr_cmp i i' with
                         | Eq -> expr_cmp j j'
                         | x0 -> x0))

(** val compare_clause : clause -> clause -> comparison **)

let compare_clause cl1 cl2 =
  match cl1 with
  | PureClause (neg, pos, _) ->
    (match cl2 with
     | PureClause (neg', pos', _) ->
       (match compare_list pure_atom_cmp neg neg' with
        | Eq -> compare_list pure_atom_cmp pos pos'
        | x0 -> x0)
     | _ -> Lt)
  | PosSpaceClause (gamma, delta, sigma) ->
    (match cl2 with
     | PureClause (_, _, _) -> Gt
     | PosSpaceClause (gamma', delta', sigma') ->
       (match compare_list pure_atom_cmp gamma gamma' with
        | Eq ->
          (match compare_list pure_atom_cmp delta delta' with
           | Eq -> compare_list compare_space_atom sigma sigma'
           | x0 -> x0)
        | x0 -> x0)
     | NegSpaceClause (_, _, _) -> Lt)
  | NegSpaceClause (gamma, sigma, delta) ->
    (match cl2 with
     | NegSpaceClause (gamma', sigma', delta') ->
       (match compare_list pure_atom_cmp gamma gamma' with
        | Eq ->
          (match compare_list pure_atom_cmp delta delta' with
           | Eq -> compare_list compare_space_atom sigma sigma'
           | x0 -> x0)
        | x0 -> x0)
     | _ -> Gt)

(** val rev_cmp : ('a1 -> 'a1 -> comparison) -> 'a1 -> 'a1 -> comparison **)

let rev_cmp cmp a b =
  match cmp a b with
  | Eq -> Eq
  | Lt -> Gt
  | Gt -> Lt

(** val prio1000 : Ident.t **)

let prio1000 =
  z2id (Zpos (XO (XO (XO (XI (XO (XI (XI (XI (XI XH))))))))))

(** val prio1001 : Ident.t **)

let prio1001 =
  z2id (Zpos (XI (XO (XO (XI (XO (XI (XI (XI (XI XH))))))))))

(** val clause_prio : clause -> var **)

let clause_prio = function
| PureClause (_, _, prio0) -> prio0
| PosSpaceClause (_, _, _) -> prio1000
| NegSpaceClause (_, _, _) -> prio1001

(** val compare_clause' : clause -> clause -> comparison **)

let compare_clause' cl1 cl2 =
  match Ident.compare (clause_prio cl1) (clause_prio cl2) with
  | Eq -> compare_clause cl1 cl2
  | x0 -> x0

module OrderedClause =
 struct
  type t = clause

  (** val compare : clause -> clause -> comparison **)

  let compare =
    compare_clause'

  (** val eq_dec : clause -> clause -> sumbool **)

  let eq_dec x0 y =
    let j = compare x0 y in
    (match j with
     | Eq ->
       let c = compSpec2Type x0 y (compare x0 y) in
       (match c with
        | CompEqT -> Left
        | _ -> assert false (* absurd case *))
     | Lt -> Right
     | Gt -> let c = compSpec2Type x0 y (compare_clause' x0 y) in (match c with
                                                                   | CompEqT -> Left
                                                                   | _ -> Right))
 end

module M = Make(OrderedClause)

(** val clause_list2set : clause list -> M.t **)

let clause_list2set l =
  fold_left (fun s0 c -> M.add c s0) l M.empty

(** val empty_clause : clause **)

let empty_clause =
  mkPureClause Nil Nil

(** val remove_trivial_atoms : pure_atom list -> pure_atom list **)

let remove_trivial_atoms =
  filter (fun a -> let Eqv (e1, e2) = a in (match expr_cmp e1 e2 with
                                            | Eq -> False
                                            | _ -> True))

(** val subst_pures_delete : var -> expr -> pure_atom list -> pure_atom list **)

let subst_pures_delete i e =
  compose remove_trivial_atoms (subst_pures i e)

(** val isEq : comparison -> bool **)

let isEq = function
| Eq -> True
| _ -> False

(** val eq_space_atomlist : space_atom list -> space_atom list -> bool **)

let eq_space_atomlist a b =
  isEq (compare_list compare_space_atom a b)

(** val eq_var : positive -> positive -> bool **)

let eq_var i j =
  isEq (Ident.compare i j)

(** val drop_reflex_lseg : space_atom list -> space_atom list **)

let drop_reflex_lseg =
  filter (fun sa ->
    match sa with
    | Next (_, _) -> True
    | Lseg (e, e0) ->
      (match e with
       | Nil2 -> (match e0 with
                  | Nil2 -> False
                  | Var _ -> True)
       | Var x0 -> (match e0 with
                    | Nil2 -> True
                    | Var y -> negb (eq_var x0 y))))

(** val greater_than_expr : var -> expr -> bool **)

let greater_than_expr i = function
| Nil2 -> True
| Var j -> (match Ident.compare i j with
            | Gt -> True
            | _ -> False)

(** val greater_than_atom : pure_atom -> pure_atom -> bool **)

let greater_than_atom s u =
  let Eqv (s0, t0) = s in
  let Eqv (u0, v) = u in
  (match match match expr_lt u0 s0 with
               | True -> (match expr_geq s0 v with
                          | True -> True
                          | False -> expr_geq t0 v)
               | False -> False with
         | True -> True
         | False ->
           (match expr_lt v s0 with
            | True -> (match expr_geq s0 u0 with
                       | True -> True
                       | False -> expr_geq t0 u0)
            | False -> False) with
   | True -> True
   | False ->
     (match match expr_lt u0 t0 with
            | True -> (match expr_geq s0 v with
                       | True -> True
                       | False -> expr_geq t0 v)
            | False -> False with
      | True -> True
      | False ->
        (match expr_lt v t0 with
         | True -> (match expr_geq s0 u0 with
                    | True -> True
                    | False -> expr_geq t0 u0)
         | False -> False)))

(** val greater_than_atoms : pure_atom -> pure_atom list -> bool **)

let greater_than_atoms s delta =
  forallb (fun u -> greater_than_atom s u) delta

(** val greater_than_all : var -> pure_atom list -> bool **)

let greater_than_all i =
  forallb (fun a ->
    let Eqv (x0, y) = a in (match greater_than_expr i x0 with
                            | True -> greater_than_expr i y
                            | False -> False))

(** val merge : ('a1 -> 'a1 -> comparison) -> 'a1 list -> 'a1 list -> 'a1 list **)

let rec merge cmp l1 l2 =
  let rec merge_aux l3 =
    match l1 with
    | Nil -> l3
    | Cons (a1, l1') ->
      (match l3 with
       | Nil -> l1
       | Cons (a2, l2') ->
         (match cmp a1 a2 with
          | Eq -> Cons (a1, (merge cmp l1' l2'))
          | Lt -> Cons (a2, (merge_aux l2'))
          | Gt -> Cons (a1, (merge cmp l1' l3))))
  in merge_aux l2

(** val pure_atom2pn_atom : bool -> pure_atom -> pn_atom **)

let pure_atom2pn_atom b = function
| Eqv (e1, e2) -> (match b with
                   | True -> Equ (e1, e2)
                   | False -> Nequ (e1, e2))

(** val pn_atom_cmp : pn_atom -> pn_atom -> comparison **)

let pn_atom_cmp a1 a2 =
  match a1 with
  | Equ (e1, e2) ->
    (match a2 with
     | Equ (e1', e2') -> pure_atom_cmp (Eqv (e1, e2)) (Eqv (e1', e2'))
     | Nequ (e1', e2') ->
       (match expr_eq e1 e1' with
        | True -> Lt
        | False -> pure_atom_cmp (Eqv (e1, e2)) (Eqv (e1', e2'))))
  | Nequ (e1, e2) ->
    (match a2 with
     | Equ (e1', e2') ->
       (match expr_eq e1 e1' with
        | True -> Gt
        | False -> pure_atom_cmp (Eqv (e1, e2)) (Eqv (e1', e2')))
     | Nequ (e1', e2') -> pure_atom_cmp (Eqv (e1, e2)) (Eqv (e1', e2')))

(** val pure_clause2pn_list : clause -> pn_atom list **)

let pure_clause2pn_list = function
| PureClause (gamma, delta, _) ->
  rsort pn_atom_cmp (app (map (pure_atom2pn_atom False) gamma) (map (pure_atom2pn_atom True) delta))
| _ -> Nil

(** val compare_clause2 : clause -> clause -> comparison **)

let compare_clause2 cl1 cl2 =
  match cl1 with
  | PureClause (_, _, _) ->
    (match cl2 with
     | PureClause (_, _, _) -> compare_list pn_atom_cmp (pure_clause2pn_list cl1) (pure_clause2pn_list cl2)
     | _ -> compare_clause cl1 cl2)
  | _ -> compare_clause cl1 cl2

type ce_type =
| CexpL
| CexpR
| CexpEf

module DebuggingHooks =
 struct
  (** val print_new_pures_set : M.t -> M.t **)

  let print_new_pures_set s =
    s

  (** val print_wf_set : M.t -> M.t **)

  let print_wf_set s =
    s

  (** val print_unfold_set : M.t -> M.t **)

  let print_unfold_set s =
    s

  (** val print_inferred_list : clause list -> clause list **)

  let print_inferred_list l =
    l

  (** val print_pures_list : clause list -> clause list **)

  let print_pures_list l =
    l

  (** val print_eqs_list : clause list -> clause list **)

  let print_eqs_list l =
    l

  (** val print_spatial_model : clause -> (var, expr) prod list -> clause **)

  let print_spatial_model c _ =
    c

  (** val print_spatial_model2 : clause -> clause -> (var, expr) prod list -> clause **)

  let print_spatial_model2 _ c' _ =
    c'

  (** val print_ce_clause :
      (var, expr) prod list -> clause -> ce_type -> (((var, expr) prod list, clause) prod, ce_type) prod **)

  let print_ce_clause r cl ct =
    Pair ((Pair (r, cl)), ct)
 end

(** val lookC : ('a1 -> 'a1 -> comparison) -> ('a1 -> 'a2) -> 'a1 -> ('a1, 'a2) prod list -> 'a2 **)

let rec lookC a_cmp fAB a = function
| Nil -> fAB a
| Cons (p, cs') ->
  let Pair (a1, b1) = p in (match isEq (a_cmp a a1) with
                            | True -> b1
                            | False -> lookC a_cmp fAB a cs')

(** val rewriteC : ('a2 -> 'a2 -> comparison) -> 'a2 -> 'a2 -> ('a1, 'a2) prod list -> ('a1, 'a2) prod list **)

let rec rewriteC b_cmp b1 b2 = function
| Nil -> Nil
| Cons (p, cs') ->
  let Pair (a1, b1') = p in
  let new_cs = rewriteC b_cmp b1 b2 cs' in
  (match isEq (b_cmp b1 b1') with
   | True -> Cons ((Pair (a1, b2)), new_cs)
   | False -> Cons ((Pair (a1, b1')), new_cs))

(** val mergeC :
    ('a1 -> 'a1 -> comparison) -> ('a2 -> 'a2 -> comparison) -> ('a1 -> 'a2) -> 'a1 -> 'a1 -> ('a1, 'a2) prod
    list -> ('a1, 'a2) prod list **)

let mergeC a_cmp b_cmp fAB a1 a2 cs =
  match isEq (b_cmp (lookC a_cmp fAB a1 cs) (lookC a_cmp fAB a2 cs)) with
  | True -> cs
  | False ->
    Cons ((Pair (a1, (lookC a_cmp fAB a2 cs))), (Cons ((Pair (a2, (lookC a_cmp fAB a2 cs))),
      (rewriteC b_cmp (lookC a_cmp fAB a1 cs) (lookC a_cmp fAB a2 cs) cs))))

(** val cclose_aux : clause list -> (expr, expr) prod list **)

let rec cclose_aux = function
| Nil -> Nil
| Cons (c, l') ->
  (match c with
   | PureClause (gamma, delta, _) ->
     (match gamma with
      | Nil ->
        (match delta with
         | Nil -> Nil
         | Cons (p, l0) ->
           let Eqv (s, t0) = p in
           (match l0 with
            | Nil -> mergeC expr_cmp expr_cmp id s t0 (cclose_aux l')
            | Cons (_, _) -> Nil))
      | Cons (_, _) -> Nil)
   | _ -> Nil)

(** val cclose : clause list -> clause list **)

let cclose l =
  map (fun p -> let Pair (e1, e2) = p in mkPureClause Nil (Cons ((Eqv (e1, e2)), Nil))) (cclose_aux l)

module Superposition =
 struct
  type model = (var, expr) prod list

  type superposition_result =
  | Valid
  | C_example of model * M.t
  | Aborted of clause list

  (** val pure_atom_gt1 : pure_atom -> pure_atom list -> bool **)

  let pure_atom_gt1 a = function
  | Nil -> True
  | Cons (b, _) -> pure_atom_gt a b

  (** val ef_aux :
      pure_atom list -> var -> expr -> expr -> pure_atom list -> pure_atom list -> clause list -> clause list **)

  let rec ef_aux neg u0 u v pos0 pos l0 =
    match pos with
    | Nil -> l0
    | Cons (a2, pos') ->
      let Eqv (s, t0) = a2 in
      (match match expr_eq s u with
             | True -> greater_than_all u0 neg
             | False -> False with
       | True ->
         Cons
           ((mkPureClause (insert_uniq pure_atom_cmp (norm_pure_atom (Eqv (v, t0))) neg)
              (insert_uniq pure_atom_cmp (norm_pure_atom (Eqv (u, t0))) (merge pure_atom_cmp (rev1 pos0) pos))),
           (ef_aux neg u0 u v (insert_uniq pure_atom_cmp a2 pos0) pos' l0))
       | False -> l0)

  (** val ef : ce_type -> clause -> clause list -> clause list **)

  let ef cty c l0 =
    match cty with
    | CexpEf ->
      (match c with
       | PureClause (neg, delta, _) ->
         (match delta with
          | Nil -> l0
          | Cons (p, pos) ->
            let Eqv (u, v) = p in
            (match u with
             | Nil2 -> l0
             | Var u0 -> (match greater_than_all u0 neg with
                          | True -> ef_aux neg u0 u v Nil pos l0
                          | False -> l0)))
       | _ -> l0)
    | _ -> l0

  (** val sp : ce_type -> clause -> clause -> clause list -> clause list **)

  let sp cty c d l0 =
    match cty with
    | CexpL ->
      (match c with
       | PureClause (gamma, pos', _) ->
         (match gamma with
          | Nil -> l0
          | Cons (p, neg') ->
            let Eqv (s', v) = p in
            (match d with
             | PureClause (neg, delta, _) ->
               (match delta with
                | Nil -> l0
                | Cons (p0, pos) ->
                  let Eqv (s, t0) = p0 in
                  (match s with
                   | Nil2 -> l0
                   | Var s0 ->
                     (match match match match match expr_eq s s' with
                                              | True -> expr_lt t0 s
                                              | False -> False with
                                        | True -> expr_lt v s'
                                        | False -> False with
                                  | True -> pure_atom_gt1 (Eqv (s, t0)) pos
                                  | False -> False with
                            | True -> greater_than_all s0 neg
                            | False -> False with
                      | True ->
                        Cons
                          ((mkPureClause
                             (insert_uniq pure_atom_cmp (norm_pure_atom (Eqv (t0, v)))
                               (merge pure_atom_cmp neg neg')) (merge pure_atom_cmp pos pos')), l0)
                      | False -> l0)))
             | _ -> l0))
       | _ -> l0)
    | CexpR ->
      (match c with
       | PureClause (neg, delta, _) ->
         (match delta with
          | Nil -> l0
          | Cons (p, pos) ->
            let Eqv (s, t0) = p in
            (match s with
             | Nil2 -> l0
             | Var s0 ->
               (match d with
                | PureClause (neg', delta0, _) ->
                  (match delta0 with
                   | Nil -> l0
                   | Cons (p0, pos') ->
                     let Eqv (s', v) = p0 in
                     (match s' with
                      | Nil2 -> l0
                      | Var s'0 ->
                        (match match match match match match match match expr_eq s s' with
                                                                   | True -> expr_lt t0 s
                                                                   | False -> False with
                                                             | True -> expr_lt v s'
                                                             | False -> False with
                                                       | True -> pure_atom_gt1 (Eqv (s, t0)) pos
                                                       | False -> False with
                                                 | True -> pure_atom_gt1 (Eqv (s', v)) pos'
                                                 | False -> False with
                                           | True -> pure_atom_gt (Eqv (s, t0)) (Eqv (s', v))
                                           | False -> False with
                                     | True -> greater_than_all s0 neg
                                     | False -> False with
                               | True -> greater_than_all s'0 neg'
                               | False -> False with
                         | True ->
                           Cons
                             ((mkPureClause (merge pure_atom_cmp neg neg')
                                (insert_uniq pure_atom_cmp (norm_pure_atom (Eqv (t0, v)))
                                  (merge pure_atom_cmp pos pos'))), l0)
                         | False -> l0)))
                | _ -> l0)))
       | _ -> l0)
    | CexpEf -> l0

  (** val rewrite_expr : expr -> expr -> expr -> expr **)

  let rewrite_expr s t0 u =
    match expr_eq s u with
    | True -> t0
    | False -> u

  (** val rewrite_by : expr -> expr -> pure_atom -> pure_atom **)

  let rewrite_by s t0 atm = match atm with
  | Eqv (u, v) ->
    (match expr_eq s u with
     | True ->
       (match expr_eq s v with
        | True -> norm_pure_atom (Eqv (t0, t0))
        | False -> norm_pure_atom (Eqv (t0, v)))
     | False -> (match expr_eq s v with
                 | True -> norm_pure_atom (Eqv (u, t0))
                 | False -> atm))

  (** val rewrite_in_space : expr -> expr -> space_atom -> space_atom **)

  let rewrite_in_space s t0 = function
  | Next (u, v) -> Next ((rewrite_expr s t0 u), (rewrite_expr s t0 v))
  | Lseg (u, v) -> Lseg ((rewrite_expr s t0 u), (rewrite_expr s t0 v))

  (** val rewrite_clause_in_space : clause -> space_atom -> space_atom **)

  let rewrite_clause_in_space c atm =
    match c with
    | PureClause (gamma, delta, _) ->
      (match gamma with
       | Nil ->
         (match delta with
          | Nil -> atm
          | Cons (p, l) ->
            let Eqv (s, t0) = p in (match l with
                                    | Nil -> rewrite_in_space s t0 atm
                                    | Cons (_, _) -> atm))
       | Cons (_, _) -> atm)
    | _ -> atm

  (** val demodulate : clause -> clause -> clause **)

  let demodulate c d =
    match c with
    | PureClause (gamma, delta, _) ->
      (match gamma with
       | Nil ->
         (match delta with
          | Nil -> d
          | Cons (p, l) ->
            let Eqv (s, t0) = p in
            (match l with
             | Nil ->
               (match d with
                | PureClause (neg, pos, _) -> mkPureClause (map (rewrite_by s t0) neg) (map (rewrite_by s t0) pos)
                | PosSpaceClause (neg, pos, space) ->
                  PosSpaceClause ((map (rewrite_by s t0) neg), (map (rewrite_by s t0) pos),
                    (map (rewrite_in_space s t0) space))
                | NegSpaceClause (neg, space, pos) ->
                  NegSpaceClause ((map (rewrite_by s t0) neg), (map (rewrite_in_space s t0) space),
                    (map (rewrite_by s t0) pos)))
             | Cons (_, _) -> d))
       | Cons (_, _) -> d)
    | _ -> d

  (** val delete_resolved : clause -> clause **)

  let delete_resolved c = match c with
  | PureClause (neg, pos, _) ->
    mkPureClause (rsort_uniq pure_atom_cmp (remove_trivial_atoms neg)) (rsort_uniq pure_atom_cmp pos)
  | _ -> c

  (** val not_taut : clause -> bool **)

  let not_taut c =
    negb
      (match c with
       | PureClause (neg, pos, _) ->
         (match existsb (fun a -> existsb (fun b -> pure_atom_eq a b) pos) neg with
          | True -> True
          | False -> existsb (fun a -> let Eqv (e1, e2) = a in expr_eq e1 e2) pos)
       | _ -> False)

  (** val simplify : clause list -> clause -> clause **)

  let simplify l c =
    delete_resolved (fold_left (fun d c0 -> demodulate c0 d) l c)

  (** val simplify_atoms : clause list -> space_atom list -> space_atom list **)

  let simplify_atoms l atms =
    fold_left (fun atms0 d -> map (rewrite_clause_in_space d) atms0) l atms

  (** val infer : ce_type -> clause -> clause list -> clause list **)

  let infer cty c l =
    DebuggingHooks.print_inferred_list
      (rsort_uniq compare_clause
        (filter not_taut (map (simplify Nil) (ef cty c (fold_left (fun l0 d -> sp cty c d l0) l Nil)))))

  (** val is_model_of : model -> pure_atom list -> pure_atom list -> bool **)

  let is_model_of r gamma delta =
    match fold_right (fun ve -> subst_pures_delete (fst ve) (snd ve)) (remove_trivial_atoms gamma) r with
    | Nil -> negb (forallb nonreflex_atom (fold_right (fun ve -> subst_pures (fst ve) (snd ve)) delta r))
    | Cons (_, _) -> True

  (** val is_model_of_PI : model -> clause -> bool **)

  let is_model_of_PI r = function
  | NegSpaceClause (pi_plus, _, pi_minus) ->
    (match fold_right (fun ve -> subst_pures_delete (fst ve) (snd ve)) (remove_trivial_atoms pi_plus) r with
     | Nil -> forallb nonreflex_atom (fold_right (fun ve -> subst_pures (fst ve) (snd ve)) pi_minus r)
     | Cons (_, _) -> False)
  | _ -> False

  (** val reduces : model -> var -> bool **)

  let reduces r v =
    existsb (fun ve' -> match Ident.eq_dec v (fst ve') with
                        | Left -> True
                        | Right -> False) r

  (** val clause_generate : model -> clause -> (((var, expr) prod, clause) prod, ce_type) sum **)

  let clause_generate r cl = match cl with
  | PureClause (gamma, delta0, _) ->
    (match delta0 with
     | Nil -> Inr CexpL
     | Cons (p, delta) ->
       let Eqv (l, r0) = p in
       (match l with
        | Nil2 -> Inr CexpL
        | Var l' ->
          (match match match greater_than_expr l' r0 with
                       | True -> greater_than_all l' gamma
                       | False -> False with
                 | True -> greater_than_atoms (Eqv (l, r0)) delta
                 | False -> False with
           | True ->
             (match reduces r l' with
              | True -> Inr CexpR
              | False ->
                (match is_model_of (rev1 r) Nil (map (rewrite_by l r0) delta) with
                 | True -> Inr CexpEf
                 | False -> Inl (Pair ((Pair (l', r0)), cl))))
           | False -> Inr CexpL)))
  | _ -> Inr CexpL

  (** val partial_mod :
      model -> clause list -> clause list -> ((model, clause list) prod, ((model, clause) prod, ce_type) prod) sum **)

  let rec partial_mod r acc = function
  | Nil -> Inl (Pair (r, acc))
  | Cons (cl, l') ->
    (match cl with
     | PureClause (gamma, delta, _) ->
       (match is_model_of (rev1 r) gamma delta with
        | True -> partial_mod r acc l'
        | False ->
          (match clause_generate r cl with
           | Inl p -> let Pair (p0, cl') = p in partial_mod (Cons (p0, r)) (Cons (cl', acc)) l'
           | Inr cty -> Inr (DebuggingHooks.print_ce_clause r cl cty)))
     | _ -> Inl (Pair (r, acc)))

  (** val is_empty_clause : clause -> bool **)

  let is_empty_clause = function
  | PureClause (gamma, delta, _) ->
    (match gamma with
     | Nil -> (match delta with
               | Nil -> True
               | Cons (_, _) -> False)
     | Cons (_, _) -> False)
  | _ -> False

  (** val is_unit_clause : clause -> bool **)

  let is_unit_clause = function
  | PureClause (gamma, delta, _) ->
    (match gamma with
     | Nil -> (match delta with
               | Nil -> False
               | Cons (_, l) -> (match l with
                                 | Nil -> True
                                 | Cons (_, _) -> False))
     | Cons (_, _) -> False)
  | _ -> False

  (** val main_terminate :
      positive -> clause list -> clause list -> (((superposition_result, clause list) prod, M.t) prod, M.t) prod **)

  let rec main_terminate n0 units l =
    match Coq_Pos.eqb n0 XH with
    | True -> Pair ((Pair ((Pair ((Aborted l), units)), M.empty)), M.empty)
    | False ->
      (match existsb is_empty_clause (map delete_resolved l) with
       | True -> Pair ((Pair ((Pair (Valid, units)), M.empty)), M.empty)
       | False ->
         let Pair (us, rs) = partition is_unit_clause l in
         (match partial_mod Nil Nil
                  (filter not_taut (map (simplify (DebuggingHooks.print_eqs_list (cclose us))) rs)) with
          | Inl p ->
            let Pair (r, selected) = p in
            Pair ((Pair ((Pair ((C_example (r, (clause_list2set selected))), (cclose (app (cclose us) units)))),
            (clause_list2set (filter not_taut (map (simplify (DebuggingHooks.print_eqs_list (cclose us))) rs))))),
            M.empty)
          | Inr p ->
            let Pair (p0, cty) = p in
            let Pair (_, cl) = p0 in
            main_terminate (Coq_Pos.pred n0) (cclose (app (cclose us) units))
              (DebuggingHooks.print_pures_list
                (rsort (rev_cmp compare_clause2)
                  (app
                    (infer cty cl
                      (filter not_taut (map (simplify (DebuggingHooks.print_eqs_list (cclose us))) rs)))
                    (filter not_taut (map (simplify (DebuggingHooks.print_eqs_list (cclose us))) rs)))))))

  (** val main :
      positive -> clause list -> clause list -> (((superposition_result, clause list) prod, M.t) prod, M.t) prod **)

  let rec main n0 units l =
    match Coq_Pos.eqb n0 XH with
    | True -> Pair ((Pair ((Pair ((Aborted l), units)), M.empty)), M.empty)
    | False ->
      (match existsb is_empty_clause (map delete_resolved l) with
       | True -> Pair ((Pair ((Pair (Valid, units)), M.empty)), M.empty)
       | False ->
         let Pair (us, rs) = partition is_unit_clause l in
         (match partial_mod Nil Nil
                  (filter not_taut (map (simplify (DebuggingHooks.print_eqs_list (cclose us))) rs)) with
          | Inl p ->
            let Pair (r, selected) = p in
            Pair ((Pair ((Pair ((C_example (r, (clause_list2set selected))), (cclose (app (cclose us) units)))),
            (clause_list2set (filter not_taut (map (simplify (DebuggingHooks.print_eqs_list (cclose us))) rs))))),
            M.empty)
          | Inr p ->
            let Pair (p0, cty) = p in
            let Pair (_, cl) = p0 in
            main (Coq_Pos.pred n0) (cclose (app (cclose us) units))
              (DebuggingHooks.print_pures_list
                (rsort (rev_cmp compare_clause2)
                  (app
                    (infer cty cl
                      (filter not_taut (map (simplify (DebuggingHooks.print_eqs_list (cclose us))) rs)))
                    (filter not_taut (map (simplify (DebuggingHooks.print_eqs_list (cclose us))) rs)))))))

  (** val check_clauseset : M.t -> (((superposition_result, clause list) prod, M.t) prod, M.t) prod **)

  let check_clauseset s =
    main (XO (XO (XO (XO (XO (XO (XO (XO (XO (XI (XO (XI (XO (XO (XI (XI (XO (XI (XO (XI (XI (XO (XO (XI (XI (XI
      (XO (XI (XI XH))))))))))))))))))))))))))))) Nil
      (DebuggingHooks.print_pures_list (rsort (rev_cmp compare_clause2) (M.elements (M.filter not_taut s))))
 end

module HeapResolve =
 struct
  (** val normalize1_3 : clause -> clause -> clause **)

  let normalize1_3 pc sc =
    match pc with
    | PureClause (gamma, delta0, _) ->
      (match delta0 with
       | Nil -> sc
       | Cons (p, delta) ->
         let Eqv (e, y) = p in
         (match e with
          | Nil2 -> sc
          | Var x0 ->
            (match sc with
             | PureClause (_, _, _) -> sc
             | PosSpaceClause (gamma', delta', sigma) ->
               PosSpaceClause ((rsort_uniq pure_atom_cmp (app gamma gamma')),
                 (rsort_uniq pure_atom_cmp (app delta delta')), (subst_spaces x0 y sigma))
             | NegSpaceClause (gamma', sigma, delta') ->
               NegSpaceClause ((rsort_uniq pure_atom_cmp (app gamma gamma')), (subst_spaces x0 y sigma),
                 (rsort_uniq pure_atom_cmp (app delta delta'))))))
    | _ -> sc

  (** val normalize2_4 : clause -> clause **)

  let normalize2_4 sc = match sc with
  | PureClause (_, _, _) -> sc
  | PosSpaceClause (gamma, delta, sigma) -> PosSpaceClause (gamma, delta, (drop_reflex_lseg sigma))
  | NegSpaceClause (gamma, sigma, delta) -> NegSpaceClause (gamma, (drop_reflex_lseg sigma), delta)

  (** val norm : M.t -> clause -> clause **)

  let norm s sc =
    normalize2_4 (fold_right normalize1_3 sc (rsort (rev_cmp compare_clause2) (M.elements s)))

  (** val do_well1_2 : space_atom list -> pure_atom list list **)

  let rec do_well1_2 = function
  | Nil -> Nil
  | Cons (s, sc') ->
    (match s with
     | Next (e, _) -> (match e with
                       | Nil2 -> Cons (Nil, (do_well1_2 sc'))
                       | Var _ -> do_well1_2 sc')
     | Lseg (e, y) ->
       (match e with
        | Nil2 -> Cons ((Cons ((Eqv (y, Nil2)), Nil)), (do_well1_2 sc'))
        | Var _ -> do_well1_2 sc'))

  (** val next_in_dom : Ident.t -> space_atom list -> bool **)

  let rec next_in_dom x0 = function
  | Nil -> False
  | Cons (s, sc') ->
    (match s with
     | Next (e, _) ->
       (match e with
        | Nil2 -> next_in_dom x0 sc'
        | Var x' -> (match Ident.eq_dec x0 x' with
                     | Left -> True
                     | Right -> next_in_dom x0 sc'))
     | Lseg (_, _) -> next_in_dom x0 sc')

  (** val next_in_dom1 : Ident.t -> expr -> space_atom list -> bool **)

  let rec next_in_dom1 x0 y = function
  | Nil -> False
  | Cons (s, sc') ->
    (match s with
     | Next (e, y') ->
       (match e with
        | Nil2 -> next_in_dom1 x0 y sc'
        | Var x' ->
          (match Ident.eq_dec x0 x' with
           | Left -> (match expr_eq y y' with
                      | True -> True
                      | False -> next_in_dom1 x0 y sc')
           | Right -> next_in_dom1 x0 y sc'))
     | Lseg (_, _) -> next_in_dom1 x0 y sc')

  (** val next_in_dom2 : Ident.t -> expr -> space_atom list -> expr option **)

  let rec next_in_dom2 x0 y = function
  | Nil -> None
  | Cons (s, sc') ->
    (match s with
     | Next (e, y') ->
       (match e with
        | Nil2 -> next_in_dom2 x0 y sc'
        | Var x' ->
          (match Ident.eq_dec x0 x' with
           | Left -> (match expr_eq y y' with
                      | True -> next_in_dom2 x0 y sc'
                      | False -> Some y')
           | Right -> next_in_dom2 x0 y sc'))
     | Lseg (_, _) -> next_in_dom2 x0 y sc')

  (** val do_well3 : space_atom list -> pure_atom list list **)

  let rec do_well3 = function
  | Nil -> Nil
  | Cons (s, sc') ->
    (match s with
     | Next (e, _) ->
       (match e with
        | Nil2 -> do_well3 sc'
        | Var x0 -> (match next_in_dom x0 sc' with
                     | True -> Cons (Nil, (do_well3 sc'))
                     | False -> do_well3 sc'))
     | Lseg (_, _) -> do_well3 sc')

  (** val lseg_in_dom2 : Ident.t -> expr -> space_atom list -> expr option **)

  let rec lseg_in_dom2 x0 y = function
  | Nil -> None
  | Cons (s, sc') ->
    (match s with
     | Next (_, _) -> lseg_in_dom2 x0 y sc'
     | Lseg (x1, y0) ->
       (match x1 with
        | Nil2 -> lseg_in_dom2 x0 y sc'
        | Var x' ->
          (match Ident.eq_dec x0 x' with
           | Left -> (match negb (expr_eq y0 y) with
                      | True -> Some y0
                      | False -> lseg_in_dom2 x0 y sc')
           | Right -> lseg_in_dom2 x0 y sc')))

  (** val lseg_in_dom_atoms : Ident.t -> space_atom list -> pure_atom list **)

  let rec lseg_in_dom_atoms x0 = function
  | Nil -> Nil
  | Cons (s, sc') ->
    (match s with
     | Next (_, _) -> lseg_in_dom_atoms x0 sc'
     | Lseg (x1, y0) ->
       (match x1 with
        | Nil2 -> lseg_in_dom_atoms x0 sc'
        | Var x' ->
          (match Ident.eq_dec x0 x' with
           | Left -> Cons ((order_eqv_pure_atom (Eqv (x1, y0))), (lseg_in_dom_atoms x0 sc'))
           | Right -> lseg_in_dom_atoms x0 sc')))

  (** val do_well4_5 : space_atom list -> pure_atom list list **)

  let rec do_well4_5 = function
  | Nil -> Nil
  | Cons (a, sc') ->
    (match a with
     | Next (e, _) ->
       (match e with
        | Nil2 -> do_well4_5 sc'
        | Var x' ->
          let atms = map (fun a0 -> Cons (a0, Nil)) (lseg_in_dom_atoms x' sc') in app atms (do_well4_5 sc'))
     | Lseg (x0, y) ->
       (match x0 with
        | Nil2 -> do_well4_5 sc'
        | Var x' ->
          let l0 = lseg_in_dom_atoms x' sc' in
          (match l0 with
           | Nil -> do_well4_5 sc'
           | Cons (_, _) ->
             let atms = map (fun a0 -> normalize_atoms (Cons ((Eqv (x0, y)), (Cons (a0, Nil))))) l0 in
             app atms (do_well4_5 sc'))))

  (** val do_well : space_atom list -> pure_atom list list **)

  let do_well sc =
    app (do_well1_2 sc) (app (do_well3 sc) (do_well4_5 sc))

  (** val do_wellformed : clause -> M.t **)

  let do_wellformed = function
  | PosSpaceClause (gamma, delta, sigma) ->
    let sigma' = rsort (rev_cmp compare_space_atom) sigma in
    clause_list2set (map (fun ats -> mkPureClause gamma (normalize_atoms (app ats delta))) (do_well sigma'))
  | _ -> M.empty

  (** val spatial_resolution : clause -> clause -> M.t **)

  let spatial_resolution pc nc =
    match pc with
    | PosSpaceClause (gamma', delta', sigma') ->
      (match nc with
       | NegSpaceClause (gamma, sigma, delta) ->
         (match eq_space_atomlist (rsort compare_space_atom sigma) (rsort compare_space_atom sigma') with
          | True -> M.singleton (order_eqv_clause (mkPureClause (app gamma gamma') (app delta delta')))
          | False -> M.empty)
       | _ -> M.empty)
    | _ -> M.empty

  (** val unfolding1' :
      space_atom list -> space_atom list -> space_atom list -> (pure_atom, space_atom list) prod list **)

  let rec unfolding1' sigma0 sigma1 = function
  | Nil -> Nil
  | Cons (a, sigma2') ->
    (match a with
     | Next (_, _) -> unfolding1' (Cons (a, sigma0)) sigma1 sigma2'
     | Lseg (x0, z0) ->
       (match x0 with
        | Nil2 -> unfolding1' (Cons (a, sigma0)) sigma1 sigma2'
        | Var x' ->
          (match next_in_dom1 x' z0 sigma1 with
           | True ->
             Cons ((Pair ((Eqv (x0, z0)),
               (insert (rev_cmp compare_space_atom) (Next (x0, z0)) (app (rev1 sigma0) sigma2')))),
               (unfolding1' (Cons ((Lseg (x0, z0)), sigma0)) sigma1 sigma2'))
           | False -> unfolding1' (Cons ((Lseg (x0, z0)), sigma0)) sigma1 sigma2')))

  (** val unfolding1 : clause -> clause -> clause list **)

  let unfolding1 sc1 sc2 =
    match sc1 with
    | PosSpaceClause (_, _, sigma1) ->
      (match sc2 with
       | NegSpaceClause (gamma', sigma2, delta') ->
         let l0 = unfolding1' Nil sigma1 sigma2 in
         let build_clause = fun p ->
           let Pair (atm, sigma2') = p in
           NegSpaceClause (gamma', sigma2', (insert_uniq pure_atom_cmp (order_eqv_pure_atom atm) delta'))
         in
         map build_clause l0
       | _ -> Nil)
    | _ -> Nil

  (** val unfolding2' :
      space_atom list -> space_atom list -> space_atom list -> (pure_atom, space_atom list) prod list **)

  let rec unfolding2' sigma0 sigma1 = function
  | Nil -> Nil
  | Cons (a, sigma2') ->
    (match a with
     | Next (_, _) -> unfolding2' (Cons (a, sigma0)) sigma1 sigma2'
     | Lseg (x0, z0) ->
       (match x0 with
        | Nil2 -> unfolding2' (Cons (a, sigma0)) sigma1 sigma2'
        | Var x' ->
          (match next_in_dom2 x' z0 sigma1 with
           | Some y ->
             Cons ((Pair ((Eqv (x0, z0)),
               (insert (rev_cmp compare_space_atom) (Next (x0, y))
                 (insert (rev_cmp compare_space_atom) (Lseg (y, z0)) (app (rev1 sigma0) sigma2'))))),
               (unfolding2' (Cons ((Lseg (x0, z0)), sigma0)) sigma1 sigma2'))
           | None -> unfolding2' (Cons ((Lseg (x0, z0)), sigma0)) sigma1 sigma2')))

  (** val unfolding2 : clause -> clause -> clause list **)

  let unfolding2 sc1 sc2 =
    match sc1 with
    | PosSpaceClause (_, _, sigma1) ->
      (match sc2 with
       | NegSpaceClause (gamma', sigma2, delta') ->
         let l0 = unfolding2' Nil sigma1 sigma2 in
         let build_clause = fun p ->
           let Pair (atm, sigma2') = p in
           NegSpaceClause (gamma', sigma2', (insert_uniq pure_atom_cmp (order_eqv_pure_atom atm) delta'))
         in
         map build_clause l0
       | _ -> Nil)
    | _ -> Nil

  (** val unfolding3' : space_atom list -> space_atom list -> space_atom list -> space_atom list list **)

  let rec unfolding3' sigma0 sigma1 = function
  | Nil -> Nil
  | Cons (a, sigma2') ->
    (match a with
     | Next (_, _) -> unfolding3' (Cons (a, sigma0)) sigma1 sigma2'
     | Lseg (x0, e) ->
       (match x0 with
        | Nil2 -> unfolding3' (Cons (a, sigma0)) sigma1 sigma2'
        | Var x' ->
          (match e with
           | Nil2 ->
             (match lseg_in_dom2 x' Nil2 sigma1 with
              | Some y ->
                Cons
                  ((insert (rev_cmp compare_space_atom) (Lseg (x0, y))
                     (insert (rev_cmp compare_space_atom) (Lseg (y, Nil2)) (app (rev1 sigma0) sigma2'))),
                  (unfolding3' (Cons ((Lseg (x0, Nil2)), sigma0)) sigma1 sigma2'))
              | None -> unfolding3' (Cons ((Lseg (x0, Nil2)), sigma0)) sigma1 sigma2')
           | Var _ -> unfolding3' (Cons (a, sigma0)) sigma1 sigma2')))

  (** val unfolding3 : clause -> clause -> clause list **)

  let unfolding3 sc1 sc2 =
    match sc1 with
    | PosSpaceClause (_, _, sigma1) ->
      (match sc2 with
       | NegSpaceClause (gamma', sigma2, delta') ->
         let l0 = unfolding3' Nil sigma1 sigma2 in
         let build_clause = fun sigma2' -> NegSpaceClause (gamma', sigma2', delta') in map build_clause l0
       | _ -> Nil)
    | _ -> Nil

  (** val unfolding4NPR' : space_atom list -> space_atom list -> space_atom list -> space_atom list list **)

  let rec unfolding4NPR' sigma0 sigma1 = function
  | Nil -> Nil
  | Cons (a, sigma2') ->
    (match a with
     | Next (_, _) -> unfolding4NPR' (Cons (a, sigma0)) sigma1 sigma2'
     | Lseg (x0, z0) ->
       (match x0 with
        | Nil2 -> unfolding4NPR' (Cons (a, sigma0)) sigma1 sigma2'
        | Var x' ->
          (match z0 with
           | Nil2 -> unfolding4NPR' (Cons (a, sigma0)) sigma1 sigma2'
           | Var z' ->
             (match lseg_in_dom2 x' z0 sigma1 with
              | Some y ->
                (match next_in_dom z' sigma1 with
                 | True ->
                   Cons
                     ((insert (rev_cmp compare_space_atom) (Lseg (x0, y))
                        (insert (rev_cmp compare_space_atom) (Lseg (y, z0)) (app (rev1 sigma0) sigma2'))),
                     (unfolding4NPR' (Cons ((Lseg (x0, z0)), sigma0)) sigma1 sigma2'))
                 | False -> unfolding4NPR' (Cons ((Lseg (x0, z0)), sigma0)) sigma1 sigma2')
              | None -> unfolding4NPR' (Cons ((Lseg (x0, z0)), sigma0)) sigma1 sigma2'))))

  (** val unfolding4 : clause -> clause -> clause list **)

  let unfolding4 sc1 sc2 =
    match sc1 with
    | PosSpaceClause (gamma, delta, sigma1) ->
      (match sc2 with
       | NegSpaceClause (gamma', sigma2, delta') ->
         let l0 = unfolding4NPR' Nil sigma1 sigma2 in
         let gG' = rsort_uniq pure_atom_cmp (app gamma gamma') in
         let dD' = rsort_uniq pure_atom_cmp (app delta delta') in
         let build_clause = fun sigma2' -> NegSpaceClause (gG', sigma2', dD') in map build_clause l0
       | _ -> Nil)
    | _ -> Nil

  (** val unfolding6NPR' :
      space_atom list -> space_atom list -> space_atom list -> (pure_atom, space_atom list) prod list **)

  let rec unfolding6NPR' sigma0 sigma1 = function
  | Nil -> Nil
  | Cons (a, sigma2') ->
    (match a with
     | Next (_, _) -> unfolding6NPR' (Cons (a, sigma0)) sigma1 sigma2'
     | Lseg (x0, z0) ->
       (match x0 with
        | Nil2 -> unfolding6NPR' (Cons (a, sigma0)) sigma1 sigma2'
        | Var x' ->
          (match z0 with
           | Nil2 -> unfolding6NPR' (Cons (a, sigma0)) sigma1 sigma2'
           | Var z' ->
             (match Ident.eq_dec x' z' with
              | Left -> unfolding6NPR' sigma0 sigma1 sigma2'
              | Right ->
                (match lseg_in_dom2 x' z0 sigma1 with
                 | Some y ->
                   let atms = lseg_in_dom_atoms z' sigma1 in
                   let build_res = fun atm -> Pair (atm,
                     (insert (rev_cmp compare_space_atom) (Lseg (x0, y))
                       (insert (rev_cmp compare_space_atom) (Lseg (y, z0)) (app (rev1 sigma0) sigma2'))))
                   in
                   app (map build_res atms) (unfolding6NPR' (Cons ((Lseg (x0, z0)), sigma0)) sigma1 sigma2')
                 | None -> unfolding6NPR' (Cons ((Lseg (x0, z0)), sigma0)) sigma1 sigma2')))))

  (** val unfolding6 : clause -> clause -> clause list **)

  let unfolding6 sc1 sc2 =
    match sc1 with
    | PosSpaceClause (gamma, delta, sigma1) ->
      (match sc2 with
       | NegSpaceClause (gamma', sigma2, delta') ->
         let l0 = unfolding6NPR' Nil sigma1 sigma2 in
         let gG' = rsort_uniq pure_atom_cmp (app gamma gamma') in
         let dD' = rsort_uniq pure_atom_cmp (app delta delta') in
         let build_clause = fun p ->
           let Pair (atm, sigma2') = p in
           NegSpaceClause (gG', sigma2', (insert_uniq pure_atom_cmp (order_eqv_pure_atom atm) dD'))
         in
         map build_clause l0
       | _ -> Nil)
    | _ -> Nil

  (** val mem_add : M.elt -> M.t -> M.t option **)

  let mem_add x0 s =
    match M.mem x0 s with
    | True -> None
    | False -> Some (M.add x0 s)

  (** val add_list_to_set_simple : M.elt list -> M.t -> M.t **)

  let add_list_to_set_simple l s =
    fold_left (flip M.add) l s

  (** val add_list_to_set : M.elt list -> M.t -> M.t option **)

  let rec add_list_to_set l s =
    match l with
    | Nil -> None
    | Cons (x0, xs) ->
      (match mem_add x0 s with
       | Some s' -> Some (add_list_to_set_simple xs s')
       | None -> add_list_to_set xs s)

  (** val do_unfold' : clause -> clause -> clause list -> clause list **)

  let do_unfold' pc nc l =
    app (unfolding1 pc nc)
      (app (unfolding2 pc nc) (app (unfolding3 pc nc) (app (unfolding4 pc nc) (app (unfolding6 pc nc) l))))

  (** val do_unfold : nat -> clause -> M.t -> M.t **)

  let rec do_unfold n0 pc s =
    match n0 with
    | O -> s
    | S n' ->
      (match add_list_to_set (M.fold (do_unfold' pc) s Nil) s with
       | Some s'' -> do_unfold n' pc s''
       | None -> s)

  (** val unfolding : clause -> clause -> M.t **)

  let unfolding pc nc =
    M.fold (fun c -> M.union (spatial_resolution pc c))
      (do_unfold (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
        (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
        (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
        (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
        (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
        (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
        (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
        (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
        (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
        (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
        (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
        (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
        (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
        (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
        (S (S (S (S (S (S (S (S (S (S (S (S (S
        O))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
        pc (M.add nc M.empty)) M.empty
 end

module VeriStar =
 struct
  type veristar_result =
  | Valid
  | C_example of Superposition.model
  | Aborted of clause list * clause

  (** val pureb : clause -> bool **)

  let pureb = function
  | PureClause (_, _, _) -> True
  | _ -> False

  (** val pure_clauses : clause list -> clause list **)

  let pure_clauses =
    filter pureb

  (** val pures : M.t -> M.t **)

  let pures =
    M.filter pureb

  (** val sublistg : ('a1 -> 'a1 -> comparison) -> 'a1 list -> 'a1 list -> bool **)

  let rec sublistg cmp l1 l2 =
    match l1 with
    | Nil -> True
    | Cons (a, l1') ->
      (match l2 with
       | Nil -> False
       | Cons (b, l2') -> (match isEq (cmp a b) with
                           | True -> sublistg cmp l1' l2'
                           | False -> False))

  (** val sublist : ('a1 -> 'a1 -> comparison) -> 'a1 list -> 'a1 list -> bool **)

  let rec sublist cmp l1 l2 =
    match l1 with
    | Nil -> True
    | Cons (a, l1') ->
      (match l2 with
       | Nil -> False
       | Cons (b, l2') -> (match isEq (cmp a b) with
                           | True -> sublistg cmp l1' l2'
                           | False -> sublist cmp l1 l2'))

  (** val impl_pure_clause : clause -> clause -> bool **)

  let impl_pure_clause c d =
    match c with
    | PureClause (gamma, delta, _) ->
      (match d with
       | PureClause (gamma', delta', _) ->
         (match sublist pure_atom_cmp gamma gamma' with
          | True -> sublist pure_atom_cmp delta delta'
          | False -> False)
       | _ -> False)
    | _ -> False

  (** val relim1 : clause -> M.t -> M.t **)

  let relim1 c s =
    M.filter (fun d -> negb (impl_pure_clause c d)) s

  (** val incorp : M.t -> M.t -> M.t **)

  let incorp s t0 =
    M.union s (M.fold relim1 s t0)

  (** val the_loop_terminate : positive -> space_atom list -> clause -> M.t -> clause -> veristar_result **)

  let rec the_loop_terminate n0 sigma nc s cl =
    match Coq_Pos.eqb n0 XH with
    | True -> Aborted ((M.elements s), cl)
    | False ->
      let Pair (p, _) = Superposition.check_clauseset s in
      let Pair (p0, s_star) = p in
      let Pair (s0, units) = p0 in
      (match s0 with
       | Superposition.Valid -> Valid
       | Superposition.C_example (r, selected) ->
         (match isEq
                  (M.compare
                    (incorp
                      (DebuggingHooks.print_wf_set
                        (HeapResolve.do_wellformed
                          (DebuggingHooks.print_spatial_model
                            (HeapResolve.norm (DebuggingHooks.print_wf_set selected) (PosSpaceClause (Nil, Nil,
                              (Superposition.simplify_atoms units sigma)))) r))) s_star) s_star) with
          | True ->
            (match Superposition.is_model_of_PI (rev1 r)
                     (DebuggingHooks.print_spatial_model (Superposition.simplify units nc) r) with
             | True ->
               (match isEq
                        (M.compare
                          (incorp
                            (DebuggingHooks.print_wf_set
                              (HeapResolve.do_wellformed
                                (DebuggingHooks.print_spatial_model
                                  (HeapResolve.norm (DebuggingHooks.print_wf_set selected) (PosSpaceClause (Nil,
                                    Nil, (Superposition.simplify_atoms units sigma)))) r))) s_star)
                          (incorp
                            (DebuggingHooks.print_unfold_set
                              (pures
                                (HeapResolve.unfolding
                                  (DebuggingHooks.print_spatial_model
                                    (HeapResolve.norm (DebuggingHooks.print_wf_set selected) (PosSpaceClause
                                      (Nil, Nil, (Superposition.simplify_atoms units sigma)))) r)
                                  (DebuggingHooks.print_spatial_model2
                                    (DebuggingHooks.print_spatial_model
                                      (HeapResolve.norm (DebuggingHooks.print_wf_set selected) (PosSpaceClause
                                        (Nil, Nil, (Superposition.simplify_atoms units sigma)))) r)
                                    (HeapResolve.norm selected (Superposition.simplify units nc)) r))))
                            (incorp
                              (DebuggingHooks.print_wf_set
                                (HeapResolve.do_wellformed
                                  (DebuggingHooks.print_spatial_model
                                    (HeapResolve.norm (DebuggingHooks.print_wf_set selected) (PosSpaceClause
                                      (Nil, Nil, (Superposition.simplify_atoms units sigma)))) r))) s_star))) with
                | True -> C_example r
                | False ->
                  the_loop_terminate (Coq_Pos.pred n0) (Superposition.simplify_atoms units sigma)
                    (Superposition.simplify units nc)
                    (incorp
                      (DebuggingHooks.print_unfold_set
                        (pures
                          (HeapResolve.unfolding
                            (DebuggingHooks.print_spatial_model
                              (HeapResolve.norm (DebuggingHooks.print_wf_set selected) (PosSpaceClause (Nil, Nil,
                                (Superposition.simplify_atoms units sigma)))) r)
                            (DebuggingHooks.print_spatial_model2
                              (DebuggingHooks.print_spatial_model
                                (HeapResolve.norm (DebuggingHooks.print_wf_set selected) (PosSpaceClause (Nil,
                                  Nil, (Superposition.simplify_atoms units sigma)))) r)
                              (HeapResolve.norm selected (Superposition.simplify units nc)) r))))
                      (incorp
                        (DebuggingHooks.print_wf_set
                          (HeapResolve.do_wellformed
                            (DebuggingHooks.print_spatial_model
                              (HeapResolve.norm (DebuggingHooks.print_wf_set selected) (PosSpaceClause (Nil, Nil,
                                (Superposition.simplify_atoms units sigma)))) r))) s_star))
                    (DebuggingHooks.print_spatial_model
                      (HeapResolve.norm (DebuggingHooks.print_wf_set selected) (PosSpaceClause (Nil, Nil,
                        (Superposition.simplify_atoms units sigma)))) r))
             | False -> C_example r)
          | False ->
            the_loop_terminate (Coq_Pos.pred n0) (Superposition.simplify_atoms units sigma)
              (Superposition.simplify units nc)
              (incorp
                (DebuggingHooks.print_wf_set
                  (HeapResolve.do_wellformed
                    (DebuggingHooks.print_spatial_model
                      (HeapResolve.norm (DebuggingHooks.print_wf_set selected) (PosSpaceClause (Nil, Nil,
                        (Superposition.simplify_atoms units sigma)))) r))) s_star)
              (DebuggingHooks.print_spatial_model
                (HeapResolve.norm (DebuggingHooks.print_wf_set selected) (PosSpaceClause (Nil, Nil,
                  (Superposition.simplify_atoms units sigma)))) r))
       | Superposition.Aborted l -> Aborted (l, cl))

  (** val the_loop : positive -> space_atom list -> clause -> M.t -> clause -> veristar_result **)

  let rec the_loop n0 sigma nc s cl =
    match Coq_Pos.eqb n0 XH with
    | True -> Aborted ((M.elements s), cl)
    | False ->
      let Pair (p, _) = Superposition.check_clauseset s in
      let Pair (p0, s_star) = p in
      let Pair (s0, units) = p0 in
      (match s0 with
       | Superposition.Valid -> Valid
       | Superposition.C_example (r, selected) ->
         (match isEq
                  (M.compare
                    (incorp
                      (DebuggingHooks.print_wf_set
                        (HeapResolve.do_wellformed
                          (DebuggingHooks.print_spatial_model
                            (HeapResolve.norm (DebuggingHooks.print_wf_set selected) (PosSpaceClause (Nil, Nil,
                              (Superposition.simplify_atoms units sigma)))) r))) s_star) s_star) with
          | True ->
            (match Superposition.is_model_of_PI (rev1 r)
                     (DebuggingHooks.print_spatial_model (Superposition.simplify units nc) r) with
             | True ->
               (match isEq
                        (M.compare
                          (incorp
                            (DebuggingHooks.print_wf_set
                              (HeapResolve.do_wellformed
                                (DebuggingHooks.print_spatial_model
                                  (HeapResolve.norm (DebuggingHooks.print_wf_set selected) (PosSpaceClause (Nil,
                                    Nil, (Superposition.simplify_atoms units sigma)))) r))) s_star)
                          (incorp
                            (DebuggingHooks.print_unfold_set
                              (pures
                                (HeapResolve.unfolding
                                  (DebuggingHooks.print_spatial_model
                                    (HeapResolve.norm (DebuggingHooks.print_wf_set selected) (PosSpaceClause
                                      (Nil, Nil, (Superposition.simplify_atoms units sigma)))) r)
                                  (DebuggingHooks.print_spatial_model2
                                    (DebuggingHooks.print_spatial_model
                                      (HeapResolve.norm (DebuggingHooks.print_wf_set selected) (PosSpaceClause
                                        (Nil, Nil, (Superposition.simplify_atoms units sigma)))) r)
                                    (HeapResolve.norm selected (Superposition.simplify units nc)) r))))
                            (incorp
                              (DebuggingHooks.print_wf_set
                                (HeapResolve.do_wellformed
                                  (DebuggingHooks.print_spatial_model
                                    (HeapResolve.norm (DebuggingHooks.print_wf_set selected) (PosSpaceClause
                                      (Nil, Nil, (Superposition.simplify_atoms units sigma)))) r))) s_star))) with
                | True -> C_example r
                | False ->
                  the_loop (Coq_Pos.pred n0) (Superposition.simplify_atoms units sigma)
                    (Superposition.simplify units nc)
                    (incorp
                      (DebuggingHooks.print_unfold_set
                        (pures
                          (HeapResolve.unfolding
                            (DebuggingHooks.print_spatial_model
                              (HeapResolve.norm (DebuggingHooks.print_wf_set selected) (PosSpaceClause (Nil, Nil,
                                (Superposition.simplify_atoms units sigma)))) r)
                            (DebuggingHooks.print_spatial_model2
                              (DebuggingHooks.print_spatial_model
                                (HeapResolve.norm (DebuggingHooks.print_wf_set selected) (PosSpaceClause (Nil,
                                  Nil, (Superposition.simplify_atoms units sigma)))) r)
                              (HeapResolve.norm selected (Superposition.simplify units nc)) r))))
                      (incorp
                        (DebuggingHooks.print_wf_set
                          (HeapResolve.do_wellformed
                            (DebuggingHooks.print_spatial_model
                              (HeapResolve.norm (DebuggingHooks.print_wf_set selected) (PosSpaceClause (Nil, Nil,
                                (Superposition.simplify_atoms units sigma)))) r))) s_star))
                    (DebuggingHooks.print_spatial_model
                      (HeapResolve.norm (DebuggingHooks.print_wf_set selected) (PosSpaceClause (Nil, Nil,
                        (Superposition.simplify_atoms units sigma)))) r))
             | False -> C_example r)
          | False ->
            the_loop (Coq_Pos.pred n0) (Superposition.simplify_atoms units sigma)
              (Superposition.simplify units nc)
              (incorp
                (DebuggingHooks.print_wf_set
                  (HeapResolve.do_wellformed
                    (DebuggingHooks.print_spatial_model
                      (HeapResolve.norm (DebuggingHooks.print_wf_set selected) (PosSpaceClause (Nil, Nil,
                        (Superposition.simplify_atoms units sigma)))) r))) s_star)
              (DebuggingHooks.print_spatial_model
                (HeapResolve.norm (DebuggingHooks.print_wf_set selected) (PosSpaceClause (Nil, Nil,
                  (Superposition.simplify_atoms units sigma)))) r))
       | Superposition.Aborted l -> Aborted (l, cl))

  (** val check_entailment : entailment -> veristar_result **)

  let check_entailment ent =
    let s = clause_list2set (pure_clauses (map order_eqv_clause (cnf ent))) in
    let Entailment (a, a0) = ent in
    let Assertion (_, sigma) = a in
    let Assertion (pi', sigma') = a0 in
    let Pair (pi'plus, pi'minus) = mk_pureR pi' in
    the_loop (XO (XO (XO (XO (XO (XO (XO (XO (XO (XI (XO (XI (XO (XO (XI (XI (XO (XI (XO (XI (XI (XO (XO (XI (XI
      (XI (XO (XI (XI XH))))))))))))))))))))))))))))) sigma (NegSpaceClause (pi'plus, sigma', pi'minus))
      (DebuggingHooks.print_new_pures_set s) empty_clause
 end

(** val x : positive -> expr **)

let x p =
  Var p

(** val harder_ent : entailment **)

let harder_ent () =
  Entailment ((Assertion (Nil, (Cons ((Next ((x (XI (XO (XO XH)))), (x (XI XH)))), (Cons ((Lseg
    ((x (XI (XI XH))), (x (XO (XO (XO XH)))))), (Cons ((Lseg ((x XH), (x (XO (XI XH))))), (Cons ((Next
    ((x (XO (XI (XO XH)))), (x (XO XH)))), (Cons ((Next ((x (XI XH)), (x (XI (XI XH))))), (Cons ((Lseg
    ((x (XI (XO XH))), (x (XO (XI (XO XH)))))), (Cons ((Next ((x (XO (XO XH))), (x (XI (XO (XO XH)))))), (Cons
    ((Next ((x (XI (XO (XI XH)))), (x (XI (XO XH))))), (Cons ((Lseg ((x (XO (XO (XO XH)))), (x (XI (XO XH))))),
    (Cons ((Next ((x (XI (XI (XO XH)))), (x (XO (XO (XI XH)))))), (Cons ((Next ((x (XO (XO (XI XH)))),
    (x (XI (XI (XO XH)))))), (Cons ((Next ((x (XO XH)), (x (XO (XO XH))))), (Cons ((Lseg ((x (XO (XI XH))),
    (x (XI XH)))), Nil)))))))))))))))))))))))))))), (Assertion (Nil, (Cons ((Lseg ((x (XO XH)),
    (x (XO (XI (XO XH)))))), (Cons ((Lseg ((x (XO (XO (XI XH)))), (x (XI (XI (XO XH)))))), (Cons ((Lseg
    ((x (XI (XI (XO XH)))), (x (XO (XO (XI XH)))))), (Cons ((Lseg ((x (XO (XI XH))), (x (XI XH)))), (Cons ((Lseg
    ((x XH), (x (XO (XI XH))))), (Cons ((Lseg ((x (XI (XO (XI XH)))), (x (XI (XO XH))))), (Cons ((Lseg
    ((x (XO (XI (XO XH)))), (x (XO XH)))), Nil)))))))))))))))))

(** val main_h : VeriStar.veristar_result **)

let main_h () =
  VeriStar.check_entailment (harder_ent ())

(** val vs_hard : unit0 -> bool **)

let vs_hard _ =
  match main_h () with
  | VeriStar.Valid -> True
  | _ -> False
