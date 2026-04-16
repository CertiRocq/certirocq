
type __ = Obj.t
let __ = let rec f _ = Obj.repr f in Obj.repr f

type unit0 =
| Tt

type bool =
| True
| False

(** val xorb : bool -> bool -> bool **)

let xorb b1 b2 =
  match b1 with
  | True -> (match b2 with
             | True -> False
             | False -> True)
  | False -> b2

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

type ('a, 'b) prod =
| Pair of 'a * 'b

(** val fst : ('a1, 'a2) prod -> 'a1 **)

let fst = function
| Pair (x, _) -> x

(** val snd : ('a1, 'a2) prod -> 'a2 **)

let snd = function
| Pair (_, y) -> y

type 'a list =
| Nil
| Cons of 'a * 'a list

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

(** val nzhead : uint -> uint **)

let rec nzhead d = match d with
| D0 d0 -> nzhead d0
| _ -> d

(** val unorm : uint -> uint **)

let unorm d =
  match nzhead d with
  | Nil0 -> D0 Nil0
  | x -> x

(** val norm : int -> int **)

let norm = function
| Pos d0 -> Pos (unorm d0)
| Neg d0 -> (match nzhead d0 with
             | Nil0 -> Pos (D0 Nil0)
             | x -> Neg x)

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
  (** val succ : uint -> uint **)

  let rec succ = function
  | Nil0 -> D1 Nil0
  | D0 d0 -> D1 d0
  | D1 d0 -> D2 d0
  | D2 d0 -> D3 d0
  | D3 d0 -> D4 d0
  | D4 d0 -> D5 d0
  | D5 d0 -> D6 d0
  | D6 d0 -> D7 d0
  | D7 d0 -> D8 d0
  | D8 d0 -> D9 d0
  | D9 d0 -> D0 (succ d0)
 end

type reflect =
| ReflectT
| ReflectF

(** val iff_reflect : bool -> reflect **)

let iff_reflect = function
| True -> ReflectT
| False -> ReflectF

module Nat =
 struct
  type t = nat

  (** val zero : nat **)

  let zero =
    O

  (** val one : nat **)

  let one =
    S O

  (** val two : nat **)

  let two =
    S (S O)

  (** val succ : nat -> nat **)

  let succ x =
    S x

  (** val pred : nat -> nat **)

  let pred n = match n with
  | O -> n
  | S u -> u

  (** val add : nat -> nat -> nat **)

  let rec add n m =
    match n with
    | O -> m
    | S p -> S (add p m)

  (** val double : nat -> nat **)

  let double n =
    add n n

  (** val mul : nat -> nat -> nat **)

  let rec mul n m =
    match n with
    | O -> O
    | S p -> add m (mul p m)

  (** val sub : nat -> nat -> nat **)

  let rec sub n m =
    match n with
    | O -> n
    | S k -> (match m with
              | O -> n
              | S l -> sub k l)

  (** val eqb : nat -> nat -> bool **)

  let rec eqb n m =
    match n with
    | O -> (match m with
            | O -> True
            | S _ -> False)
    | S n' -> (match m with
               | O -> False
               | S m' -> eqb n' m')

  (** val leb : nat -> nat -> bool **)

  let rec leb n m =
    match n with
    | O -> True
    | S n' -> (match m with
               | O -> False
               | S m' -> leb n' m')

  (** val ltb : nat -> nat -> bool **)

  let ltb n m =
    leb (S n) m

  (** val compare : nat -> nat -> comparison **)

  let rec compare n m =
    match n with
    | O -> (match m with
            | O -> Eq
            | S _ -> Lt)
    | S n' -> (match m with
               | O -> Gt
               | S m' -> compare n' m')

  (** val max : nat -> nat -> nat **)

  let rec max n m =
    match n with
    | O -> m
    | S n' -> (match m with
               | O -> n
               | S m' -> S (max n' m'))

  (** val min : nat -> nat -> nat **)

  let rec min n m =
    match n with
    | O -> O
    | S n' -> (match m with
               | O -> O
               | S m' -> S (min n' m'))

  (** val even : nat -> bool **)

  let rec even = function
  | O -> True
  | S n0 -> (match n0 with
             | O -> False
             | S n' -> even n')

  (** val odd : nat -> bool **)

  let odd n =
    negb (even n)

  (** val pow : nat -> nat -> nat **)

  let rec pow n = function
  | O -> S O
  | S m0 -> mul n (pow n m0)

  (** val tail_add : nat -> nat -> nat **)

  let rec tail_add n m =
    match n with
    | O -> m
    | S n0 -> tail_add n0 (S m)

  (** val tail_addmul : nat -> nat -> nat -> nat **)

  let rec tail_addmul r n m =
    match n with
    | O -> r
    | S n0 -> tail_addmul (tail_add m r) n0 m

  (** val tail_mul : nat -> nat -> nat **)

  let tail_mul n m =
    tail_addmul O n m

  (** val of_uint_acc : uint -> nat -> nat **)

  let rec of_uint_acc d acc =
    match d with
    | Nil0 -> acc
    | D0 d0 ->
      of_uint_acc d0 (tail_mul (S (S (S (S (S (S (S (S (S (S O)))))))))) acc)
    | D1 d0 ->
      of_uint_acc d0 (S
        (tail_mul (S (S (S (S (S (S (S (S (S (S O)))))))))) acc))
    | D2 d0 ->
      of_uint_acc d0 (S (S
        (tail_mul (S (S (S (S (S (S (S (S (S (S O)))))))))) acc)))
    | D3 d0 ->
      of_uint_acc d0 (S (S (S
        (tail_mul (S (S (S (S (S (S (S (S (S (S O)))))))))) acc))))
    | D4 d0 ->
      of_uint_acc d0 (S (S (S (S
        (tail_mul (S (S (S (S (S (S (S (S (S (S O)))))))))) acc)))))
    | D5 d0 ->
      of_uint_acc d0 (S (S (S (S (S
        (tail_mul (S (S (S (S (S (S (S (S (S (S O)))))))))) acc))))))
    | D6 d0 ->
      of_uint_acc d0 (S (S (S (S (S (S
        (tail_mul (S (S (S (S (S (S (S (S (S (S O)))))))))) acc)))))))
    | D7 d0 ->
      of_uint_acc d0 (S (S (S (S (S (S (S
        (tail_mul (S (S (S (S (S (S (S (S (S (S O)))))))))) acc))))))))
    | D8 d0 ->
      of_uint_acc d0 (S (S (S (S (S (S (S (S
        (tail_mul (S (S (S (S (S (S (S (S (S (S O)))))))))) acc)))))))))
    | D9 d0 ->
      of_uint_acc d0 (S (S (S (S (S (S (S (S (S
        (tail_mul (S (S (S (S (S (S (S (S (S (S O)))))))))) acc))))))))))

  (** val of_uint : uint -> nat **)

  let of_uint d =
    of_uint_acc d O

  (** val to_little_uint : nat -> uint -> uint **)

  let rec to_little_uint n acc =
    match n with
    | O -> acc
    | S n0 -> to_little_uint n0 (Little.succ acc)

  (** val to_uint : nat -> uint **)

  let to_uint n =
    rev (to_little_uint n (D0 Nil0))

  (** val of_int : int -> nat option **)

  let of_int d =
    match norm d with
    | Pos u -> Some (of_uint u)
    | Neg _ -> None

  (** val to_int : nat -> int **)

  let to_int n =
    Pos (to_uint n)

  (** val divmod : nat -> nat -> nat -> nat -> (nat, nat) prod **)

  let rec divmod x y q u =
    match x with
    | O -> Pair (q, u)
    | S x' ->
      (match u with
       | O -> divmod x' y (S q) y
       | S u' -> divmod x' y q u')

  (** val div : nat -> nat -> nat **)

  let div x y = match y with
  | O -> y
  | S y' -> fst (divmod x y' O y')

  (** val modulo : nat -> nat -> nat **)

  let modulo x y = match y with
  | O -> y
  | S y' -> sub y' (snd (divmod x y' O y'))

  (** val gcd : nat -> nat -> nat **)

  let rec gcd a b =
    match a with
    | O -> b
    | S a' -> gcd (modulo b (S a')) (S a')

  (** val square : nat -> nat **)

  let square n =
    mul n n

  (** val sqrt_iter : nat -> nat -> nat -> nat -> nat **)

  let rec sqrt_iter k p q r =
    match k with
    | O -> p
    | S k' ->
      (match r with
       | O -> sqrt_iter k' (S p) (S (S q)) (S (S q))
       | S r' -> sqrt_iter k' p q r')

  (** val sqrt : nat -> nat **)

  let sqrt n =
    sqrt_iter n O O O

  (** val log2_iter : nat -> nat -> nat -> nat -> nat **)

  let rec log2_iter k p q r =
    match k with
    | O -> p
    | S k' ->
      (match r with
       | O -> log2_iter k' (S p) (S q) q
       | S r' -> log2_iter k' p (S q) r')

  (** val log2 : nat -> nat **)

  let log2 n =
    log2_iter (pred n) O (S O) O

  (** val iter : nat -> ('a1 -> 'a1) -> 'a1 -> 'a1 **)

  let rec iter n f x =
    match n with
    | O -> x
    | S n0 -> f (iter n0 f x)

  (** val div2 : nat -> nat **)

  let rec div2 = function
  | O -> O
  | S n0 -> (match n0 with
             | O -> O
             | S n' -> S (div2 n'))

  (** val testbit : nat -> nat -> bool **)

  let rec testbit a = function
  | O -> odd a
  | S n0 -> testbit (div2 a) n0

  (** val shiftl : nat -> nat -> nat **)

  let rec shiftl a = function
  | O -> a
  | S n0 -> double (shiftl a n0)

  (** val shiftr : nat -> nat -> nat **)

  let rec shiftr a = function
  | O -> a
  | S n0 -> div2 (shiftr a n0)

  (** val bitwise : (bool -> bool -> bool) -> nat -> nat -> nat -> nat **)

  let rec bitwise op n a b =
    match n with
    | O -> O
    | S n' ->
      add (match op (odd a) (odd b) with
           | True -> S O
           | False -> O) (mul (S (S O)) (bitwise op n' (div2 a) (div2 b)))

  (** val coq_land : nat -> nat -> nat **)

  let coq_land a b =
    bitwise (fun b1 b2 -> match b1 with
                          | True -> b2
                          | False -> False) a a b

  (** val coq_lor : nat -> nat -> nat **)

  let coq_lor a b =
    bitwise (fun b1 b2 -> match b1 with
                          | True -> True
                          | False -> b2) (max a b) a b

  (** val ldiff : nat -> nat -> nat **)

  let ldiff a b =
    bitwise (fun b0 b' -> match b0 with
                          | True -> negb b'
                          | False -> False) a a b

  (** val coq_lxor : nat -> nat -> nat **)

  let coq_lxor a b =
    bitwise xorb (max a b) a b

  (** val recursion : 'a1 -> (nat -> 'a1 -> 'a1) -> nat -> 'a1 **)

  let rec recursion x f = function
  | O -> x
  | S n0 -> f n0 (recursion x f n0)

  (** val eq_dec : nat -> nat -> sumbool **)

  let rec eq_dec n m =
    match n with
    | O -> (match m with
            | O -> Left
            | S _ -> Right)
    | S n0 -> (match m with
               | O -> Right
               | S m0 -> eq_dec n0 m0)

  (** val leb_spec0 : nat -> nat -> reflect **)

  let leb_spec0 x y =
    iff_reflect (leb x y)

  (** val ltb_spec0 : nat -> nat -> reflect **)

  let ltb_spec0 x y =
    iff_reflect (ltb x y)

  module Private_OrderTac =
   struct
    module IsTotal =
     struct
     end

    module Tac =
     struct
     end
   end

  module Private_Tac =
   struct
   end

  module Private_Dec =
   struct
    (** val max_case_strong :
        nat -> nat -> (nat -> nat -> __ -> 'a1 -> 'a1) -> (__ -> 'a1) -> (__
        -> 'a1) -> 'a1 **)

    let max_case_strong n m compat hl hr =
      let c = compSpec2Type n m (compare n m) in
      (match c with
       | CompGtT -> compat n (max n m) __ (hl __)
       | _ -> compat m (max n m) __ (hr __))

    (** val max_case :
        nat -> nat -> (nat -> nat -> __ -> 'a1 -> 'a1) -> 'a1 -> 'a1 -> 'a1 **)

    let max_case n m x x0 x1 =
      max_case_strong n m x (fun _ -> x0) (fun _ -> x1)

    (** val max_dec : nat -> nat -> sumbool **)

    let max_dec n m =
      max_case n m (fun _ _ _ h0 -> h0) Left Right

    (** val min_case_strong :
        nat -> nat -> (nat -> nat -> __ -> 'a1 -> 'a1) -> (__ -> 'a1) -> (__
        -> 'a1) -> 'a1 **)

    let min_case_strong n m compat hl hr =
      let c = compSpec2Type n m (compare n m) in
      (match c with
       | CompGtT -> compat m (min n m) __ (hr __)
       | _ -> compat n (min n m) __ (hl __))

    (** val min_case :
        nat -> nat -> (nat -> nat -> __ -> 'a1 -> 'a1) -> 'a1 -> 'a1 -> 'a1 **)

    let min_case n m x x0 x1 =
      min_case_strong n m x (fun _ -> x0) (fun _ -> x1)

    (** val min_dec : nat -> nat -> sumbool **)

    let min_dec n m =
      min_case n m (fun _ _ _ h0 -> h0) Left Right
   end

  (** val max_case_strong :
      nat -> nat -> (__ -> 'a1) -> (__ -> 'a1) -> 'a1 **)

  let max_case_strong n m x x0 =
    Private_Dec.max_case_strong n m (fun _ _ _ x1 -> x1) x x0

  (** val max_case : nat -> nat -> 'a1 -> 'a1 -> 'a1 **)

  let max_case n m x x0 =
    max_case_strong n m (fun _ -> x) (fun _ -> x0)

  (** val max_dec : nat -> nat -> sumbool **)

  let max_dec =
    Private_Dec.max_dec

  (** val min_case_strong :
      nat -> nat -> (__ -> 'a1) -> (__ -> 'a1) -> 'a1 **)

  let min_case_strong n m x x0 =
    Private_Dec.min_case_strong n m (fun _ _ _ x1 -> x1) x x0

  (** val min_case : nat -> nat -> 'a1 -> 'a1 -> 'a1 **)

  let min_case n m x x0 =
    min_case_strong n m (fun _ -> x) (fun _ -> x0)

  (** val min_dec : nat -> nat -> sumbool **)

  let min_dec =
    Private_Dec.min_dec

  module Private_Parity =
   struct
   end

  module Private_NZPow =
   struct
   end

  module Private_NZSqrt =
   struct
   end

  (** val sqrt_up : nat -> nat **)

  let sqrt_up a =
    match compare O a with
    | Lt -> S (sqrt (pred a))
    | _ -> O

  (** val log2_up : nat -> nat **)

  let log2_up a =
    match compare (S O) a with
    | Lt -> S (log2 (pred a))
    | _ -> O

  module Private_NZDiv =
   struct
   end

  (** val lcm : nat -> nat -> nat **)

  let lcm a b =
    mul a (div b (gcd a b))

  (** val eqb_spec : nat -> nat -> reflect **)

  let eqb_spec x y =
    iff_reflect (eqb x y)

  (** val b2n : bool -> nat **)

  let b2n = function
  | True -> S O
  | False -> O

  (** val setbit : nat -> nat -> nat **)

  let setbit a n =
    coq_lor a (shiftl (S O) n)

  (** val clearbit : nat -> nat -> nat **)

  let clearbit a n =
    ldiff a (shiftl (S O) n)

  (** val ones : nat -> nat **)

  let ones n =
    pred (shiftl (S O) n)

  (** val lnot : nat -> nat -> nat **)

  let lnot a n =
    coq_lxor a (ones n)
 end

module Coq_Nat = Nat

type key = nat

type tree =
| Node of key * tree * tree
| Leaf

type priqueue = tree list

(** val empty : priqueue **)

let empty =
  Nil

(** val smash : tree -> tree -> tree **)

let smash t0 u =
  match t0 with
  | Node (x, t1, t2) ->
    (match t2 with
     | Node (_, _, _) -> Leaf
     | Leaf ->
       (match u with
        | Node (y, u1, t3) ->
          (match t3 with
           | Node (_, _, _) -> Leaf
           | Leaf ->
             (match Coq_Nat.ltb y x with
              | True -> Node (x, (Node (y, u1, t1)), Leaf)
              | False -> Node (y, (Node (x, t1, u1)), Leaf)))
        | Leaf -> Leaf))
  | Leaf -> Leaf

(** val carry : tree list -> tree -> tree list **)

let rec carry q t0 =
  match q with
  | Nil -> (match t0 with
            | Node (_, _, _) -> Cons (t0, Nil)
            | Leaf -> Nil)
  | Cons (u, q') ->
    (match u with
     | Node (_, _, _) ->
       (match t0 with
        | Node (_, _, _) -> Cons (Leaf, (carry q' (smash t0 u)))
        | Leaf -> Cons (u, q'))
     | Leaf -> Cons (t0, q'))

(** val insert : key -> priqueue -> priqueue **)

let insert x q =
  carry q (Node (x, Leaf, Leaf))

(** val join : priqueue -> priqueue -> tree -> priqueue **)

let rec join p q c =
  match p with
  | Nil -> carry q c
  | Cons (p1, p') ->
    (match p1 with
     | Node (_, _, _) ->
       (match q with
        | Nil -> carry p c
        | Cons (q1, q') ->
          (match q1 with
           | Node (_, _, _) -> Cons (c, (join p' q' (smash p1 q1)))
           | Leaf ->
             (match c with
              | Node (_, _, _) -> Cons (Leaf, (join p' q' (smash c p1)))
              | Leaf -> Cons (p1, (join p' q' Leaf)))))
     | Leaf ->
       (match q with
        | Nil -> carry p c
        | Cons (q1, q') ->
          (match q1 with
           | Node (_, _, _) ->
             (match c with
              | Node (_, _, _) -> Cons (Leaf, (join p' q' (smash c q1)))
              | Leaf -> Cons (q1, (join p' q' Leaf)))
           | Leaf -> Cons (c, (join p' q' Leaf)))))

(** val unzip : tree -> (priqueue -> priqueue) -> priqueue **)

let rec unzip t0 cont =
  match t0 with
  | Node (x, t1, t2) ->
    unzip t2 (fun q -> Cons ((Node (x, t1, Leaf)), (cont q)))
  | Leaf -> cont Nil

(** val heap_delete_max : tree -> priqueue **)

let heap_delete_max = function
| Node (_, t1, t2) ->
  (match t2 with
   | Node (_, _, _) -> Nil
   | Leaf -> unzip t1 (fun u -> u))
| Leaf -> Nil

(** val find_max' : key -> priqueue -> key **)

let rec find_max' current = function
| Nil -> current
| Cons (t0, q') ->
  (match t0 with
   | Node (x, _, _) ->
     find_max'
       (match Coq_Nat.ltb current x with
        | True -> x
        | False -> current) q'
   | Leaf -> find_max' current q')

(** val find_max : priqueue -> key option **)

let rec find_max = function
| Nil -> None
| Cons (t0, q') ->
  (match t0 with
   | Node (x, _, _) -> Some (find_max' x q')
   | Leaf -> find_max q')

(** val delete_max_aux : key -> priqueue -> (priqueue, priqueue) prod **)

let rec delete_max_aux m = function
| Nil -> Pair (Nil, Nil)
| Cons (t0, p') ->
  (match t0 with
   | Node (x, t1, t2) ->
     (match t2 with
      | Node (_, _, _) -> Pair (Nil, Nil)
      | Leaf ->
        (match Coq_Nat.ltb x m with
         | True ->
           let Pair (j, k) = delete_max_aux m p' in
           Pair ((Cons ((Node (x, t1, Leaf)), j)), k)
         | False ->
           Pair ((Cons (Leaf, p')), (heap_delete_max (Node (x, t1, Leaf))))))
   | Leaf ->
     let Pair (j, k) = delete_max_aux m p' in Pair ((Cons (Leaf, j)), k))

(** val delete_max : priqueue -> (key, priqueue) prod option **)

let delete_max q =
  match find_max q with
  | Some m ->
    let Pair (p', q') = delete_max_aux m q in
    Some (Pair (m, (join p' q' Leaf)))
  | None -> None

(** val merge : priqueue -> priqueue -> priqueue **)

let merge p q =
  join p q Leaf

(** val insert_list : nat list -> priqueue -> priqueue **)

let rec insert_list l q =
  match l with
  | Nil -> q
  | Cons (x, l0) -> insert_list l0 (insert x q)

(** val make_list : nat -> nat list -> nat list **)

let rec make_list n l =
  match n with
  | O -> Cons (O, l)
  | S n0 ->
    (match n0 with
     | O -> Cons ((S O), l)
     | S n1 -> make_list n1 (Cons ((S (S n1)), l)))

(** val main : key **)

let main (_ : unit0) =
  let a =
    insert_list
      (make_list (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
        (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
        (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
        (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
        (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
        (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
        (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
        (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
        (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
        (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
        (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
        (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
        (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
        (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
        (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
        (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
        (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
        (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
        (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
        (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
        (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
        (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
        (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
        (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
        (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
        (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
        (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
        (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
        (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
        (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
        (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
        (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
        (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
        (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
        (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
        (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
        (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
        (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
        (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
        (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
        (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
        (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
        (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
        (S (S (S (S (S (S (S (S (S (S (S (S (S (S
        O))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
        Nil) empty
  in
  let b =
    insert_list
      (make_list (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
        (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
        (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
        (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
        (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
        (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
        (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
        (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
        (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
        (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
        (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
        (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
        (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
        (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
        (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
        (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
        (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
        (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
        (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
        (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
        (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
        (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
        (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
        (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
        (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
        (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
        (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
        (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
        (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
        (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
        (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
        (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
        (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
        (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
        (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
        (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
        (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
        (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
        (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
        (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
        (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
        (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
        (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
        (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
        O)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
        Nil) empty
  in
  let c = merge a b in
  (match delete_max c with
   | Some p -> let Pair (k, _) = p in k
   | None -> O)

(** val binom : unit0 -> key **)

let binom _ =
  main Tt
