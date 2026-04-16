
type __ = Obj.t

type unit0 =
| Tt

type bool =
| True
| False

val xorb : bool -> bool -> bool

val negb : bool -> bool

type nat =
| O
| S of nat

type 'a option =
| Some of 'a
| None

type ('a, 'b) prod =
| Pair of 'a * 'b

val fst : ('a1, 'a2) prod -> 'a1

val snd : ('a1, 'a2) prod -> 'a2

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

val compareSpec2Type : comparison -> compareSpecT

type 'a compSpecT = compareSpecT

val compSpec2Type : 'a1 -> 'a1 -> comparison -> 'a1 compSpecT

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

val nzhead : uint -> uint

val unorm : uint -> uint

val norm : int -> int

val revapp : uint -> uint -> uint

val rev : uint -> uint

module Little :
 sig
  val succ : uint -> uint
 end

type reflect =
| ReflectT
| ReflectF

val iff_reflect : bool -> reflect

module Nat :
 sig
  type t = nat

  val zero : nat

  val one : nat

  val two : nat

  val succ : nat -> nat

  val pred : nat -> nat

  val add : nat -> nat -> nat

  val double : nat -> nat

  val mul : nat -> nat -> nat

  val sub : nat -> nat -> nat

  val eqb : nat -> nat -> bool

  val leb : nat -> nat -> bool

  val ltb : nat -> nat -> bool

  val compare : nat -> nat -> comparison

  val max : nat -> nat -> nat

  val min : nat -> nat -> nat

  val even : nat -> bool

  val odd : nat -> bool

  val pow : nat -> nat -> nat

  val tail_add : nat -> nat -> nat

  val tail_addmul : nat -> nat -> nat -> nat

  val tail_mul : nat -> nat -> nat

  val of_uint_acc : uint -> nat -> nat

  val of_uint : uint -> nat

  val to_little_uint : nat -> uint -> uint

  val to_uint : nat -> uint

  val of_int : int -> nat option

  val to_int : nat -> int

  val divmod : nat -> nat -> nat -> nat -> (nat, nat) prod

  val div : nat -> nat -> nat

  val modulo : nat -> nat -> nat

  val gcd : nat -> nat -> nat

  val square : nat -> nat

  val sqrt_iter : nat -> nat -> nat -> nat -> nat

  val sqrt : nat -> nat

  val log2_iter : nat -> nat -> nat -> nat -> nat

  val log2 : nat -> nat

  val iter : nat -> ('a1 -> 'a1) -> 'a1 -> 'a1

  val div2 : nat -> nat

  val testbit : nat -> nat -> bool

  val shiftl : nat -> nat -> nat

  val shiftr : nat -> nat -> nat

  val bitwise : (bool -> bool -> bool) -> nat -> nat -> nat -> nat

  val coq_land : nat -> nat -> nat

  val coq_lor : nat -> nat -> nat

  val ldiff : nat -> nat -> nat

  val coq_lxor : nat -> nat -> nat

  val recursion : 'a1 -> (nat -> 'a1 -> 'a1) -> nat -> 'a1

  val eq_dec : nat -> nat -> sumbool

  val leb_spec0 : nat -> nat -> reflect

  val ltb_spec0 : nat -> nat -> reflect

  module Private_OrderTac :
   sig
    module IsTotal :
     sig
     end

    module Tac :
     sig
     end
   end

  module Private_Tac :
   sig
   end

  module Private_Dec :
   sig
    val max_case_strong :
      nat -> nat -> (nat -> nat -> __ -> 'a1 -> 'a1) -> (__ -> 'a1) -> (__ ->
      'a1) -> 'a1

    val max_case :
      nat -> nat -> (nat -> nat -> __ -> 'a1 -> 'a1) -> 'a1 -> 'a1 -> 'a1

    val max_dec : nat -> nat -> sumbool

    val min_case_strong :
      nat -> nat -> (nat -> nat -> __ -> 'a1 -> 'a1) -> (__ -> 'a1) -> (__ ->
      'a1) -> 'a1

    val min_case :
      nat -> nat -> (nat -> nat -> __ -> 'a1 -> 'a1) -> 'a1 -> 'a1 -> 'a1

    val min_dec : nat -> nat -> sumbool
   end

  val max_case_strong : nat -> nat -> (__ -> 'a1) -> (__ -> 'a1) -> 'a1

  val max_case : nat -> nat -> 'a1 -> 'a1 -> 'a1

  val max_dec : nat -> nat -> sumbool

  val min_case_strong : nat -> nat -> (__ -> 'a1) -> (__ -> 'a1) -> 'a1

  val min_case : nat -> nat -> 'a1 -> 'a1 -> 'a1

  val min_dec : nat -> nat -> sumbool

  module Private_Parity :
   sig
   end

  module Private_NZPow :
   sig
   end

  module Private_NZSqrt :
   sig
   end

  val sqrt_up : nat -> nat

  val log2_up : nat -> nat

  module Private_NZDiv :
   sig
   end

  val lcm : nat -> nat -> nat

  val eqb_spec : nat -> nat -> reflect

  val b2n : bool -> nat

  val setbit : nat -> nat -> nat

  val clearbit : nat -> nat -> nat

  val ones : nat -> nat

  val lnot : nat -> nat -> nat
 end

module Coq_Nat :
 sig
  type t = nat

  val zero : nat

  val one : nat

  val two : nat

  val succ : nat -> nat

  val pred : nat -> nat

  val add : nat -> nat -> nat

  val double : nat -> nat

  val mul : nat -> nat -> nat

  val sub : nat -> nat -> nat

  val eqb : nat -> nat -> bool

  val leb : nat -> nat -> bool

  val ltb : nat -> nat -> bool

  val compare : nat -> nat -> comparison

  val max : nat -> nat -> nat

  val min : nat -> nat -> nat

  val even : nat -> bool

  val odd : nat -> bool

  val pow : nat -> nat -> nat

  val tail_add : nat -> nat -> nat

  val tail_addmul : nat -> nat -> nat -> nat

  val tail_mul : nat -> nat -> nat

  val of_uint_acc : uint -> nat -> nat

  val of_uint : uint -> nat

  val to_little_uint : nat -> uint -> uint

  val to_uint : nat -> uint

  val of_int : int -> nat option

  val to_int : nat -> int

  val divmod : nat -> nat -> nat -> nat -> (nat, nat) prod

  val div : nat -> nat -> nat

  val modulo : nat -> nat -> nat

  val gcd : nat -> nat -> nat

  val square : nat -> nat

  val sqrt_iter : nat -> nat -> nat -> nat -> nat

  val sqrt : nat -> nat

  val log2_iter : nat -> nat -> nat -> nat -> nat

  val log2 : nat -> nat

  val iter : nat -> ('a1 -> 'a1) -> 'a1 -> 'a1

  val div2 : nat -> nat

  val testbit : nat -> nat -> bool

  val shiftl : nat -> nat -> nat

  val shiftr : nat -> nat -> nat

  val bitwise : (bool -> bool -> bool) -> nat -> nat -> nat -> nat

  val coq_land : nat -> nat -> nat

  val coq_lor : nat -> nat -> nat

  val ldiff : nat -> nat -> nat

  val coq_lxor : nat -> nat -> nat

  val recursion : 'a1 -> (nat -> 'a1 -> 'a1) -> nat -> 'a1

  val eq_dec : nat -> nat -> sumbool

  val leb_spec0 : nat -> nat -> reflect

  val ltb_spec0 : nat -> nat -> reflect

  module Private_OrderTac :
   sig
    module IsTotal :
     sig
     end

    module Tac :
     sig
     end
   end

  module Private_Tac :
   sig
   end

  module Private_Dec :
   sig
    val max_case_strong :
      nat -> nat -> (nat -> nat -> __ -> 'a1 -> 'a1) -> (__ -> 'a1) -> (__ ->
      'a1) -> 'a1

    val max_case :
      nat -> nat -> (nat -> nat -> __ -> 'a1 -> 'a1) -> 'a1 -> 'a1 -> 'a1

    val max_dec : nat -> nat -> sumbool

    val min_case_strong :
      nat -> nat -> (nat -> nat -> __ -> 'a1 -> 'a1) -> (__ -> 'a1) -> (__ ->
      'a1) -> 'a1

    val min_case :
      nat -> nat -> (nat -> nat -> __ -> 'a1 -> 'a1) -> 'a1 -> 'a1 -> 'a1

    val min_dec : nat -> nat -> sumbool
   end

  val max_case_strong : nat -> nat -> (__ -> 'a1) -> (__ -> 'a1) -> 'a1

  val max_case : nat -> nat -> 'a1 -> 'a1 -> 'a1

  val max_dec : nat -> nat -> sumbool

  val min_case_strong : nat -> nat -> (__ -> 'a1) -> (__ -> 'a1) -> 'a1

  val min_case : nat -> nat -> 'a1 -> 'a1 -> 'a1

  val min_dec : nat -> nat -> sumbool

  module Private_Parity :
   sig
   end

  module Private_NZPow :
   sig
   end

  module Private_NZSqrt :
   sig
   end

  val sqrt_up : nat -> nat

  val log2_up : nat -> nat

  module Private_NZDiv :
   sig
   end

  val lcm : nat -> nat -> nat

  val eqb_spec : nat -> nat -> reflect

  val b2n : bool -> nat

  val setbit : nat -> nat -> nat

  val clearbit : nat -> nat -> nat

  val ones : nat -> nat

  val lnot : nat -> nat -> nat
 end

type key = nat

type tree =
| Node of key * tree * tree
| Leaf

type priqueue = tree list

val empty : priqueue

val smash : tree -> tree -> tree

val carry : tree list -> tree -> tree list

val insert : key -> priqueue -> priqueue

val join : priqueue -> priqueue -> tree -> priqueue

val unzip : tree -> (priqueue -> priqueue) -> priqueue

val heap_delete_max : tree -> priqueue

val find_max' : key -> priqueue -> key

val find_max : priqueue -> key option

val delete_max_aux : key -> priqueue -> (priqueue, priqueue) prod

val delete_max : priqueue -> (key, priqueue) prod option

val merge : priqueue -> priqueue -> priqueue

val insert_list : nat list -> priqueue -> priqueue

val make_list : nat -> nat list -> nat list

val main : unit0 -> key

val binom : unit0 -> key
