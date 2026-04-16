
type __ = Obj.t

type unit0 =
| Tt

type bool =
| True
| False

val negb : bool -> bool

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

val fst : ('a1, 'a2) prod -> 'a1

val snd : ('a1, 'a2) prod -> 'a2

type 'a list =
| Nil
| Cons of 'a * 'a list

val app : 'a1 list -> 'a1 list -> 'a1 list

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

val id : 'a1 -> 'a1

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

val revapp : uint -> uint -> uint

val rev : uint -> uint

module Little :
 sig
  val double : uint -> uint

  val succ_double : uint -> uint
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

val revapp0 : uint0 -> uint0 -> uint0

val rev0 : uint0 -> uint0

module Coq_Little :
 sig
  val double : uint0 -> uint0

  val succ_double : uint0 -> uint0
 end

type uint1 =
| UIntDec of uint
| UIntHex of uint0

type int1 =
| IntDec of int
| IntHex of int0

val add : nat -> nat -> nat

val max : nat -> nat -> nat

val min : nat -> nat -> nat

type reflect =
| ReflectT
| ReflectF

val iff_reflect : bool -> reflect

val flip : ('a1 -> 'a2 -> 'a3) -> 'a2 -> 'a1 -> 'a3

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

module OT_to_Full :
 functor (O:OrderedType') ->
 sig
  type t = O.t

  val compare : t -> t -> comparison

  val eq_dec : t -> t -> sumbool
 end

module OT_to_OrderTac :
 functor (OT:OrderedType) ->
 sig
  module OTF :
   sig
    type t = OT.t

    val compare : t -> t -> comparison

    val eq_dec : t -> t -> sumbool
   end

  module TO :
   sig
    type t = OTF.t

    val compare : t -> t -> comparison

    val eq_dec : t -> t -> sumbool
   end
 end

module OrderedTypeFacts :
 functor (O:OrderedType') ->
 sig
  module OrderTac :
   sig
    module OTF :
     sig
      type t = O.t

      val compare : t -> t -> comparison

      val eq_dec : t -> t -> sumbool
     end

    module TO :
     sig
      type t = OTF.t

      val compare : t -> t -> comparison

      val eq_dec : t -> t -> sumbool
     end
   end

  val eq_dec : O.t -> O.t -> sumbool

  val lt_dec : O.t -> O.t -> sumbool

  val eqb : O.t -> O.t -> bool
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

module Pos :
 sig
  type mask =
  | IsNul
  | IsPos of positive
  | IsNeg
 end

module Coq_Pos :
 sig
  type t = positive

  val succ : positive -> positive

  val add : positive -> positive -> positive

  val add_carry : positive -> positive -> positive

  val pred_double : positive -> positive

  val pred : positive -> positive

  val pred_N : positive -> n

  type mask = Pos.mask =
  | IsNul
  | IsPos of positive
  | IsNeg

  val mask_rect : 'a1 -> (positive -> 'a1) -> 'a1 -> mask -> 'a1

  val mask_rec : 'a1 -> (positive -> 'a1) -> 'a1 -> mask -> 'a1

  val succ_double_mask : mask -> mask

  val double_mask : mask -> mask

  val double_pred_mask : positive -> mask

  val pred_mask : mask -> mask

  val sub_mask : positive -> positive -> mask

  val sub_mask_carry : positive -> positive -> mask

  val sub : positive -> positive -> positive

  val mul : positive -> positive -> positive

  val iter : ('a1 -> 'a1) -> 'a1 -> positive -> 'a1

  val pow : positive -> positive -> positive

  val square : positive -> positive

  val div2 : positive -> positive

  val div2_up : positive -> positive

  val size_nat : positive -> nat

  val size : positive -> positive

  val compare_cont : comparison -> positive -> positive -> comparison

  val compare : positive -> positive -> comparison

  val min : positive -> positive -> positive

  val max : positive -> positive -> positive

  val eqb : positive -> positive -> bool

  val leb : positive -> positive -> bool

  val ltb : positive -> positive -> bool

  val sqrtrem_step :
    (positive -> positive) -> (positive -> positive) -> (positive, mask) prod -> (positive, mask) prod

  val sqrtrem : positive -> (positive, mask) prod

  val sqrt : positive -> positive

  val gcdn : nat -> positive -> positive -> positive

  val gcd : positive -> positive -> positive

  val ggcdn : nat -> positive -> positive -> (positive, (positive, positive) prod) prod

  val ggcd : positive -> positive -> (positive, (positive, positive) prod) prod

  val coq_Nsucc_double : n -> n

  val coq_Ndouble : n -> n

  val coq_lor : positive -> positive -> positive

  val coq_land : positive -> positive -> n

  val ldiff : positive -> positive -> n

  val coq_lxor : positive -> positive -> n

  val shiftl_nat : positive -> nat -> positive

  val shiftr_nat : positive -> nat -> positive

  val shiftl : positive -> n -> positive

  val shiftr : positive -> n -> positive

  val testbit_nat : positive -> nat -> bool

  val testbit : positive -> n -> bool

  val iter_op : ('a1 -> 'a1 -> 'a1) -> positive -> 'a1 -> 'a1

  val to_nat : positive -> nat

  val of_nat : nat -> positive

  val of_succ_nat : nat -> positive

  val of_uint_acc : uint -> positive -> positive

  val of_uint : uint -> n

  val of_hex_uint_acc : uint0 -> positive -> positive

  val of_hex_uint : uint0 -> n

  val of_num_uint : uint1 -> n

  val of_int : int -> positive option

  val of_hex_int : int0 -> positive option

  val of_num_int : int1 -> positive option

  val to_little_uint : positive -> uint

  val to_uint : positive -> uint

  val to_little_hex_uint : positive -> uint0

  val to_hex_uint : positive -> uint0

  val to_num_uint : positive -> uint1

  val to_int : positive -> int

  val to_hex_int : positive -> int0

  val to_num_int : positive -> int1

  val eq_dec : positive -> positive -> sumbool

  val peano_rect : 'a1 -> (positive -> 'a1 -> 'a1) -> positive -> 'a1

  val peano_rec : 'a1 -> (positive -> 'a1 -> 'a1) -> positive -> 'a1

  type coq_PeanoView =
  | PeanoOne
  | PeanoSucc of positive * coq_PeanoView

  val coq_PeanoView_rect : 'a1 -> (positive -> coq_PeanoView -> 'a1 -> 'a1) -> positive -> coq_PeanoView -> 'a1

  val coq_PeanoView_rec : 'a1 -> (positive -> coq_PeanoView -> 'a1 -> 'a1) -> positive -> coq_PeanoView -> 'a1

  val peanoView_xO : positive -> coq_PeanoView -> coq_PeanoView

  val peanoView_xI : positive -> coq_PeanoView -> coq_PeanoView

  val peanoView : positive -> coq_PeanoView

  val coq_PeanoView_iter : 'a1 -> (positive -> 'a1 -> 'a1) -> positive -> coq_PeanoView -> 'a1

  val eqb_spec : positive -> positive -> reflect

  val switch_Eq : comparison -> comparison -> comparison

  val mask2cmp : mask -> comparison

  val leb_spec0 : positive -> positive -> reflect

  val ltb_spec0 : positive -> positive -> reflect

  module Private_Tac :
   sig
   end

  module Private_Dec :
   sig
    val max_case_strong :
      positive -> positive -> (positive -> positive -> __ -> 'a1 -> 'a1) -> (__ -> 'a1) -> (__ -> 'a1) -> 'a1

    val max_case : positive -> positive -> (positive -> positive -> __ -> 'a1 -> 'a1) -> 'a1 -> 'a1 -> 'a1

    val max_dec : positive -> positive -> sumbool

    val min_case_strong :
      positive -> positive -> (positive -> positive -> __ -> 'a1 -> 'a1) -> (__ -> 'a1) -> (__ -> 'a1) -> 'a1

    val min_case : positive -> positive -> (positive -> positive -> __ -> 'a1 -> 'a1) -> 'a1 -> 'a1 -> 'a1

    val min_dec : positive -> positive -> sumbool
   end

  val max_case_strong : positive -> positive -> (__ -> 'a1) -> (__ -> 'a1) -> 'a1

  val max_case : positive -> positive -> 'a1 -> 'a1 -> 'a1

  val max_dec : positive -> positive -> sumbool

  val min_case_strong : positive -> positive -> (__ -> 'a1) -> (__ -> 'a1) -> 'a1

  val min_case : positive -> positive -> 'a1 -> 'a1 -> 'a1

  val min_dec : positive -> positive -> sumbool
 end

val rev1 : 'a1 list -> 'a1 list

val rev_append : 'a1 list -> 'a1 list -> 'a1 list

val map : ('a1 -> 'a2) -> 'a1 list -> 'a2 list

val fold_left : ('a1 -> 'a2 -> 'a1) -> 'a2 list -> 'a1 -> 'a1

val fold_right : ('a2 -> 'a1 -> 'a1) -> 'a1 -> 'a2 list -> 'a1

val existsb : ('a1 -> bool) -> 'a1 list -> bool

val forallb : ('a1 -> bool) -> 'a1 list -> bool

val filter : ('a1 -> bool) -> 'a1 list -> 'a1 list

val partition : ('a1 -> bool) -> 'a1 list -> ('a1 list, 'a1 list) prod

module Positive_as_OT :
 sig
  type t = positive

  val succ : positive -> positive

  val add : positive -> positive -> positive

  val add_carry : positive -> positive -> positive

  val pred_double : positive -> positive

  val pred : positive -> positive

  val pred_N : positive -> n

  type mask = Pos.mask =
  | IsNul
  | IsPos of positive
  | IsNeg

  val mask_rect : 'a1 -> (positive -> 'a1) -> 'a1 -> mask -> 'a1

  val mask_rec : 'a1 -> (positive -> 'a1) -> 'a1 -> mask -> 'a1

  val succ_double_mask : mask -> mask

  val double_mask : mask -> mask

  val double_pred_mask : positive -> mask

  val pred_mask : mask -> mask

  val sub_mask : positive -> positive -> mask

  val sub_mask_carry : positive -> positive -> mask

  val sub : positive -> positive -> positive

  val mul : positive -> positive -> positive

  val iter : ('a1 -> 'a1) -> 'a1 -> positive -> 'a1

  val pow : positive -> positive -> positive

  val square : positive -> positive

  val div2 : positive -> positive

  val div2_up : positive -> positive

  val size_nat : positive -> nat

  val size : positive -> positive

  val compare_cont : comparison -> positive -> positive -> comparison

  val compare : positive -> positive -> comparison

  val min : positive -> positive -> positive

  val max : positive -> positive -> positive

  val eqb : positive -> positive -> bool

  val leb : positive -> positive -> bool

  val ltb : positive -> positive -> bool

  val sqrtrem_step :
    (positive -> positive) -> (positive -> positive) -> (positive, mask) prod -> (positive, mask) prod

  val sqrtrem : positive -> (positive, mask) prod

  val sqrt : positive -> positive

  val gcdn : nat -> positive -> positive -> positive

  val gcd : positive -> positive -> positive

  val ggcdn : nat -> positive -> positive -> (positive, (positive, positive) prod) prod

  val ggcd : positive -> positive -> (positive, (positive, positive) prod) prod

  val coq_Nsucc_double : n -> n

  val coq_Ndouble : n -> n

  val coq_lor : positive -> positive -> positive

  val coq_land : positive -> positive -> n

  val ldiff : positive -> positive -> n

  val coq_lxor : positive -> positive -> n

  val shiftl_nat : positive -> nat -> positive

  val shiftr_nat : positive -> nat -> positive

  val shiftl : positive -> n -> positive

  val shiftr : positive -> n -> positive

  val testbit_nat : positive -> nat -> bool

  val testbit : positive -> n -> bool

  val iter_op : ('a1 -> 'a1 -> 'a1) -> positive -> 'a1 -> 'a1

  val to_nat : positive -> nat

  val of_nat : nat -> positive

  val of_succ_nat : nat -> positive

  val of_uint_acc : uint -> positive -> positive

  val of_uint : uint -> n

  val of_hex_uint_acc : uint0 -> positive -> positive

  val of_hex_uint : uint0 -> n

  val of_num_uint : uint1 -> n

  val of_int : int -> positive option

  val of_hex_int : int0 -> positive option

  val of_num_int : int1 -> positive option

  val to_little_uint : positive -> uint

  val to_uint : positive -> uint

  val to_little_hex_uint : positive -> uint0

  val to_hex_uint : positive -> uint0

  val to_num_uint : positive -> uint1

  val to_int : positive -> int

  val to_hex_int : positive -> int0

  val to_num_int : positive -> int1

  val eq_dec : positive -> positive -> sumbool

  val peano_rect : 'a1 -> (positive -> 'a1 -> 'a1) -> positive -> 'a1

  val peano_rec : 'a1 -> (positive -> 'a1 -> 'a1) -> positive -> 'a1

  type coq_PeanoView = Coq_Pos.coq_PeanoView =
  | PeanoOne
  | PeanoSucc of positive * coq_PeanoView

  val coq_PeanoView_rect : 'a1 -> (positive -> coq_PeanoView -> 'a1 -> 'a1) -> positive -> coq_PeanoView -> 'a1

  val coq_PeanoView_rec : 'a1 -> (positive -> coq_PeanoView -> 'a1 -> 'a1) -> positive -> coq_PeanoView -> 'a1

  val peanoView_xO : positive -> coq_PeanoView -> coq_PeanoView

  val peanoView_xI : positive -> coq_PeanoView -> coq_PeanoView

  val peanoView : positive -> coq_PeanoView

  val coq_PeanoView_iter : 'a1 -> (positive -> 'a1 -> 'a1) -> positive -> coq_PeanoView -> 'a1

  val eqb_spec : positive -> positive -> reflect

  val switch_Eq : comparison -> comparison -> comparison

  val mask2cmp : mask -> comparison

  val leb_spec0 : positive -> positive -> reflect

  val ltb_spec0 : positive -> positive -> reflect

  module Private_Tac :
   sig
   end

  module Private_Dec :
   sig
    val max_case_strong :
      positive -> positive -> (positive -> positive -> __ -> 'a1 -> 'a1) -> (__ -> 'a1) -> (__ -> 'a1) -> 'a1

    val max_case : positive -> positive -> (positive -> positive -> __ -> 'a1 -> 'a1) -> 'a1 -> 'a1 -> 'a1

    val max_dec : positive -> positive -> sumbool

    val min_case_strong :
      positive -> positive -> (positive -> positive -> __ -> 'a1 -> 'a1) -> (__ -> 'a1) -> (__ -> 'a1) -> 'a1

    val min_case : positive -> positive -> (positive -> positive -> __ -> 'a1 -> 'a1) -> 'a1 -> 'a1 -> 'a1

    val min_dec : positive -> positive -> sumbool
   end

  val max_case_strong : positive -> positive -> (__ -> 'a1) -> (__ -> 'a1) -> 'a1

  val max_case : positive -> positive -> 'a1 -> 'a1 -> 'a1

  val max_dec : positive -> positive -> sumbool

  val min_case_strong : positive -> positive -> (__ -> 'a1) -> (__ -> 'a1) -> 'a1

  val min_case : positive -> positive -> 'a1 -> 'a1 -> 'a1

  val min_dec : positive -> positive -> sumbool
 end

module MakeListOrdering :
 functor (O:OrderedType) ->
 sig
  module MO :
   sig
    module OrderTac :
     sig
      module OTF :
       sig
        type t = O.t

        val compare : t -> t -> comparison

        val eq_dec : t -> t -> sumbool
       end

      module TO :
       sig
        type t = OTF.t

        val compare : t -> t -> comparison

        val eq_dec : t -> t -> sumbool
       end
     end

    val eq_dec : O.t -> O.t -> sumbool

    val lt_dec : O.t -> O.t -> sumbool

    val eqb : O.t -> O.t -> bool
   end
 end

type color =
| Red
| Black

module Color :
 sig
  type t = color
 end

module Make :
 functor (X:OrderedType) ->
 sig
  module Raw :
   sig
    type elt = X.t

    type tree =
    | Leaf
    | Node of Color.t * tree * X.t * tree

    val empty : tree

    val is_empty : tree -> bool

    val mem : X.t -> tree -> bool

    val min_elt : tree -> elt option

    val max_elt : tree -> elt option

    val choose : tree -> elt option

    val fold : (elt -> 'a1 -> 'a1) -> tree -> 'a1 -> 'a1

    val elements_aux : X.t list -> tree -> X.t list

    val elements : tree -> X.t list

    val rev_elements_aux : X.t list -> tree -> X.t list

    val rev_elements : tree -> X.t list

    val cardinal : tree -> nat

    val maxdepth : tree -> nat

    val mindepth : tree -> nat

    val for_all : (elt -> bool) -> tree -> bool

    val exists_ : (elt -> bool) -> tree -> bool

    type enumeration =
    | End
    | More of elt * tree * enumeration

    val cons : tree -> enumeration -> enumeration

    val compare_more : X.t -> (enumeration -> comparison) -> enumeration -> comparison

    val compare_cont : tree -> (enumeration -> comparison) -> enumeration -> comparison

    val compare_end : enumeration -> comparison

    val compare : tree -> tree -> comparison

    val equal : tree -> tree -> bool

    val subsetl : (tree -> bool) -> X.t -> tree -> bool

    val subsetr : (tree -> bool) -> X.t -> tree -> bool

    val subset : tree -> tree -> bool

    type t = tree

    val singleton : elt -> tree

    val makeBlack : tree -> tree

    val makeRed : tree -> tree

    val lbal : tree -> X.t -> tree -> tree

    val rbal : tree -> X.t -> tree -> tree

    val rbal' : tree -> X.t -> tree -> tree

    val lbalS : tree -> X.t -> tree -> tree

    val rbalS : tree -> X.t -> tree -> tree

    val ins : X.t -> tree -> tree

    val add : X.t -> tree -> tree

    val append : tree -> tree -> tree

    val del : X.t -> tree -> tree

    val remove : X.t -> tree -> tree

    val delmin : tree -> elt -> tree -> (elt, tree) prod

    val remove_min : tree -> (elt, tree) prod option

    val bogus : (tree, elt list) prod

    val treeify_zero : elt list -> (tree, elt list) prod

    val treeify_one : elt list -> (tree, elt list) prod

    val treeify_cont :
      (elt list -> (tree, elt list) prod) -> (elt list -> (tree, elt list) prod) -> elt list -> (tree, elt list)
      prod

    val treeify_aux : bool -> positive -> elt list -> (tree, elt list) prod

    val plength_aux : elt list -> positive -> positive

    val plength : elt list -> positive

    val treeify : elt list -> tree

    val filter_aux : (elt -> bool) -> tree -> X.t list -> X.t list

    val filter : (elt -> bool) -> t -> t

    val partition_aux : (elt -> bool) -> tree -> X.t list -> X.t list -> (X.t list, X.t list) prod

    val partition : (elt -> bool) -> t -> (t, t) prod

    val union_list : elt list -> elt list -> elt list -> elt list

    val linear_union : tree -> tree -> tree

    val inter_list : X.t list -> elt list -> elt list -> elt list

    val linear_inter : tree -> tree -> tree

    val diff_list : elt list -> elt list -> elt list -> elt list

    val linear_diff : tree -> tree -> tree

    val skip_red : tree -> tree

    val skip_black : tree -> tree

    val compare_height : tree -> tree -> tree -> tree -> comparison

    val union : t -> t -> t

    val diff : t -> t -> t

    val inter : t -> t -> t

    val ltb_tree : X.t -> tree -> bool

    val gtb_tree : X.t -> tree -> bool

    val isok : tree -> bool

    module MX :
     sig
      module OrderTac :
       sig
        module OTF :
         sig
          type t = X.t

          val compare : t -> t -> comparison

          val eq_dec : t -> t -> sumbool
         end

        module TO :
         sig
          type t = OTF.t

          val compare : t -> t -> comparison

          val eq_dec : t -> t -> sumbool
         end
       end

      val eq_dec : X.t -> X.t -> sumbool

      val lt_dec : X.t -> X.t -> sumbool

      val eqb : X.t -> X.t -> bool
     end

    type coq_R_min_elt =
    | R_min_elt_0 of tree
    | R_min_elt_1 of tree * Color.t * tree * X.t * tree
    | R_min_elt_2 of tree * Color.t * tree * X.t * tree * Color.t * tree * X.t * tree * elt option * coq_R_min_elt

    type coq_R_max_elt =
    | R_max_elt_0 of tree
    | R_max_elt_1 of tree * Color.t * tree * X.t * tree
    | R_max_elt_2 of tree * Color.t * tree * X.t * tree * Color.t * tree * X.t * tree * elt option * coq_R_max_elt

    module L :
     sig
      module MO :
       sig
        module OrderTac :
         sig
          module OTF :
           sig
            type t = X.t

            val compare : t -> t -> comparison

            val eq_dec : t -> t -> sumbool
           end

          module TO :
           sig
            type t = OTF.t

            val compare : t -> t -> comparison

            val eq_dec : t -> t -> sumbool
           end
         end

        val eq_dec : X.t -> X.t -> sumbool

        val lt_dec : X.t -> X.t -> sumbool

        val eqb : X.t -> X.t -> bool
       end
     end

    val flatten_e : enumeration -> elt list

    val rcase : (tree -> X.t -> tree -> 'a1) -> (tree -> 'a1) -> tree -> 'a1

    val rrcase : (tree -> X.t -> tree -> X.t -> tree -> 'a1) -> (tree -> 'a1) -> tree -> 'a1

    val rrcase' : (tree -> X.t -> tree -> X.t -> tree -> 'a1) -> (tree -> 'a1) -> tree -> 'a1
   end

  module E :
   sig
    type t = X.t

    val compare : t -> t -> comparison

    val eq_dec : t -> t -> sumbool
   end

  type elt = X.t

  type t_ = Raw.t
    (* singleton inductive, whose constructor was Mkt *)

  val this : t_ -> Raw.t

  type t = t_

  val mem : elt -> t -> bool

  val add : elt -> t -> t

  val remove : elt -> t -> t

  val singleton : elt -> t

  val union : t -> t -> t

  val inter : t -> t -> t

  val diff : t -> t -> t

  val equal : t -> t -> bool

  val subset : t -> t -> bool

  val empty : t

  val is_empty : t -> bool

  val elements : t -> elt list

  val choose : t -> elt option

  val fold : (elt -> 'a1 -> 'a1) -> t -> 'a1 -> 'a1

  val cardinal : t -> nat

  val filter : (elt -> bool) -> t -> t

  val for_all : (elt -> bool) -> t -> bool

  val exists_ : (elt -> bool) -> t -> bool

  val partition : (elt -> bool) -> t -> (t, t) prod

  val eq_dec : t -> t -> sumbool

  val compare : t -> t -> comparison

  val min_elt : t -> elt option

  val max_elt : t -> elt option

  val mk_opt_t : (elt, Raw.t) prod option -> (elt, t) prod option

  val remove_min : t_ -> (elt, t) prod option
 end

val compose : ('a2 -> 'a3) -> ('a1 -> 'a2) -> 'a1 -> 'a3

module Ident :
 sig
  type t = positive

  val succ : positive -> positive

  val add : positive -> positive -> positive

  val add_carry : positive -> positive -> positive

  val pred_double : positive -> positive

  val pred : positive -> positive

  val pred_N : positive -> n

  type mask = Pos.mask =
  | IsNul
  | IsPos of positive
  | IsNeg

  val mask_rect : 'a1 -> (positive -> 'a1) -> 'a1 -> mask -> 'a1

  val mask_rec : 'a1 -> (positive -> 'a1) -> 'a1 -> mask -> 'a1

  val succ_double_mask : mask -> mask

  val double_mask : mask -> mask

  val double_pred_mask : positive -> mask

  val pred_mask : mask -> mask

  val sub_mask : positive -> positive -> mask

  val sub_mask_carry : positive -> positive -> mask

  val sub : positive -> positive -> positive

  val mul : positive -> positive -> positive

  val iter : ('a1 -> 'a1) -> 'a1 -> positive -> 'a1

  val pow : positive -> positive -> positive

  val square : positive -> positive

  val div2 : positive -> positive

  val div2_up : positive -> positive

  val size_nat : positive -> nat

  val size : positive -> positive

  val compare_cont : comparison -> positive -> positive -> comparison

  val compare : positive -> positive -> comparison

  val min : positive -> positive -> positive

  val max : positive -> positive -> positive

  val eqb : positive -> positive -> bool

  val leb : positive -> positive -> bool

  val ltb : positive -> positive -> bool

  val sqrtrem_step :
    (positive -> positive) -> (positive -> positive) -> (positive, mask) prod -> (positive, mask) prod

  val sqrtrem : positive -> (positive, mask) prod

  val sqrt : positive -> positive

  val gcdn : nat -> positive -> positive -> positive

  val gcd : positive -> positive -> positive

  val ggcdn : nat -> positive -> positive -> (positive, (positive, positive) prod) prod

  val ggcd : positive -> positive -> (positive, (positive, positive) prod) prod

  val coq_Nsucc_double : n -> n

  val coq_Ndouble : n -> n

  val coq_lor : positive -> positive -> positive

  val coq_land : positive -> positive -> n

  val ldiff : positive -> positive -> n

  val coq_lxor : positive -> positive -> n

  val shiftl_nat : positive -> nat -> positive

  val shiftr_nat : positive -> nat -> positive

  val shiftl : positive -> n -> positive

  val shiftr : positive -> n -> positive

  val testbit_nat : positive -> nat -> bool

  val testbit : positive -> n -> bool

  val iter_op : ('a1 -> 'a1 -> 'a1) -> positive -> 'a1 -> 'a1

  val to_nat : positive -> nat

  val of_nat : nat -> positive

  val of_succ_nat : nat -> positive

  val of_uint_acc : uint -> positive -> positive

  val of_uint : uint -> n

  val of_hex_uint_acc : uint0 -> positive -> positive

  val of_hex_uint : uint0 -> n

  val of_num_uint : uint1 -> n

  val of_int : int -> positive option

  val of_hex_int : int0 -> positive option

  val of_num_int : int1 -> positive option

  val to_little_uint : positive -> uint

  val to_uint : positive -> uint

  val to_little_hex_uint : positive -> uint0

  val to_hex_uint : positive -> uint0

  val to_num_uint : positive -> uint1

  val to_int : positive -> int

  val to_hex_int : positive -> int0

  val to_num_int : positive -> int1

  val eq_dec : positive -> positive -> sumbool

  val peano_rect : 'a1 -> (positive -> 'a1 -> 'a1) -> positive -> 'a1

  val peano_rec : 'a1 -> (positive -> 'a1 -> 'a1) -> positive -> 'a1

  type coq_PeanoView = Coq_Pos.coq_PeanoView =
  | PeanoOne
  | PeanoSucc of positive * coq_PeanoView

  val coq_PeanoView_rect : 'a1 -> (positive -> coq_PeanoView -> 'a1 -> 'a1) -> positive -> coq_PeanoView -> 'a1

  val coq_PeanoView_rec : 'a1 -> (positive -> coq_PeanoView -> 'a1 -> 'a1) -> positive -> coq_PeanoView -> 'a1

  val peanoView_xO : positive -> coq_PeanoView -> coq_PeanoView

  val peanoView_xI : positive -> coq_PeanoView -> coq_PeanoView

  val peanoView : positive -> coq_PeanoView

  val coq_PeanoView_iter : 'a1 -> (positive -> 'a1 -> 'a1) -> positive -> coq_PeanoView -> 'a1

  val eqb_spec : positive -> positive -> reflect

  val switch_Eq : comparison -> comparison -> comparison

  val mask2cmp : mask -> comparison

  val leb_spec0 : positive -> positive -> reflect

  val ltb_spec0 : positive -> positive -> reflect

  module Private_Tac :
   sig
   end

  module Private_Dec :
   sig
    val max_case_strong :
      positive -> positive -> (positive -> positive -> __ -> 'a1 -> 'a1) -> (__ -> 'a1) -> (__ -> 'a1) -> 'a1

    val max_case : positive -> positive -> (positive -> positive -> __ -> 'a1 -> 'a1) -> 'a1 -> 'a1 -> 'a1

    val max_dec : positive -> positive -> sumbool

    val min_case_strong :
      positive -> positive -> (positive -> positive -> __ -> 'a1 -> 'a1) -> (__ -> 'a1) -> (__ -> 'a1) -> 'a1

    val min_case : positive -> positive -> (positive -> positive -> __ -> 'a1 -> 'a1) -> 'a1 -> 'a1 -> 'a1

    val min_dec : positive -> positive -> sumbool
   end

  val max_case_strong : positive -> positive -> (__ -> 'a1) -> (__ -> 'a1) -> 'a1

  val max_case : positive -> positive -> 'a1 -> 'a1 -> 'a1

  val max_dec : positive -> positive -> sumbool

  val min_case_strong : positive -> positive -> (__ -> 'a1) -> (__ -> 'a1) -> 'a1

  val min_case : positive -> positive -> 'a1 -> 'a1 -> 'a1

  val min_dec : positive -> positive -> sumbool
 end

val z2id : z -> Ident.t

val add_id : positive -> positive -> positive

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

val subst_expr : var -> expr -> expr -> expr

val subst_space : var -> expr -> space_atom -> space_atom

val subst_spaces : var -> expr -> space_atom list -> space_atom list

val isGeq : comparison -> bool

val insert : ('a1 -> 'a1 -> comparison) -> 'a1 -> 'a1 list -> 'a1 list

val rsort : ('a1 -> 'a1 -> comparison) -> 'a1 list -> 'a1 list

val insert_uniq : ('a1 -> 'a1 -> comparison) -> 'a1 -> 'a1 list -> 'a1 list

val rsort_uniq : ('a1 -> 'a1 -> comparison) -> 'a1 list -> 'a1 list

val compare_list : ('a1 -> 'a1 -> comparison) -> 'a1 list -> 'a1 list -> comparison

type pure_atom =
| Eqv of expr * expr

val var1 : var

val var0 : var

val var2 : var

val list_prio : var -> 'a1 list -> var -> var

val prio : pure_atom list -> pure_atom list -> var

type clause =
| PureClause of pure_atom list * pure_atom list * var
| PosSpaceClause of pure_atom list * pure_atom list * space_atom list
| NegSpaceClause of pure_atom list * space_atom list * pure_atom list

val expr_cmp : expr -> expr -> comparison

val pure_atom_cmp : pure_atom -> pure_atom -> comparison

val order_eqv_pure_atom : pure_atom -> pure_atom

val nonreflex_atom : pure_atom -> bool

val normalize_atoms : pure_atom list -> pure_atom list

val mkPureClause : pure_atom list -> pure_atom list -> clause

val order_eqv_clause : clause -> clause

val mk_pureL : pn_atom -> clause

val mk_pureR : pn_atom list -> (pure_atom list, pure_atom list) prod

val cnf : entailment -> clause list

val pure_atom_gt : pure_atom -> pure_atom -> bool

val pure_atom_eq : pure_atom -> pure_atom -> bool

val expr_lt : expr -> expr -> bool

val expr_eq : expr -> expr -> bool

val expr_geq : expr -> expr -> bool

val norm_pure_atom : pure_atom -> pure_atom

val subst_pure : var -> expr -> pure_atom -> pure_atom

val subst_pures : var -> expr -> pure_atom list -> pure_atom list

val compare_space_atom : space_atom -> space_atom -> comparison

val compare_clause : clause -> clause -> comparison

val rev_cmp : ('a1 -> 'a1 -> comparison) -> 'a1 -> 'a1 -> comparison

val prio1000 : Ident.t

val prio1001 : Ident.t

val clause_prio : clause -> var

val compare_clause' : clause -> clause -> comparison

module OrderedClause :
 sig
  type t = clause

  val compare : clause -> clause -> comparison

  val eq_dec : clause -> clause -> sumbool
 end

module M :
 sig
  module Raw :
   sig
    type elt = clause

    type tree =
    | Leaf
    | Node of Color.t * tree * clause * tree

    val empty : tree

    val is_empty : tree -> bool

    val mem : clause -> tree -> bool

    val min_elt : tree -> elt option

    val max_elt : tree -> elt option

    val choose : tree -> elt option

    val fold : (elt -> 'a1 -> 'a1) -> tree -> 'a1 -> 'a1

    val elements_aux : clause list -> tree -> clause list

    val elements : tree -> clause list

    val rev_elements_aux : clause list -> tree -> clause list

    val rev_elements : tree -> clause list

    val cardinal : tree -> nat

    val maxdepth : tree -> nat

    val mindepth : tree -> nat

    val for_all : (elt -> bool) -> tree -> bool

    val exists_ : (elt -> bool) -> tree -> bool

    type enumeration =
    | End
    | More of elt * tree * enumeration

    val cons : tree -> enumeration -> enumeration

    val compare_more : clause -> (enumeration -> comparison) -> enumeration -> comparison

    val compare_cont : tree -> (enumeration -> comparison) -> enumeration -> comparison

    val compare_end : enumeration -> comparison

    val compare : tree -> tree -> comparison

    val equal : tree -> tree -> bool

    val subsetl : (tree -> bool) -> clause -> tree -> bool

    val subsetr : (tree -> bool) -> clause -> tree -> bool

    val subset : tree -> tree -> bool

    type t = tree

    val singleton : elt -> tree

    val makeBlack : tree -> tree

    val makeRed : tree -> tree

    val lbal : tree -> clause -> tree -> tree

    val rbal : tree -> clause -> tree -> tree

    val rbal' : tree -> clause -> tree -> tree

    val lbalS : tree -> clause -> tree -> tree

    val rbalS : tree -> clause -> tree -> tree

    val ins : clause -> tree -> tree

    val add : clause -> tree -> tree

    val append : tree -> tree -> tree

    val del : clause -> tree -> tree

    val remove : clause -> tree -> tree

    val delmin : tree -> elt -> tree -> (elt, tree) prod

    val remove_min : tree -> (elt, tree) prod option

    val bogus : (tree, elt list) prod

    val treeify_zero : elt list -> (tree, elt list) prod

    val treeify_one : elt list -> (tree, elt list) prod

    val treeify_cont :
      (elt list -> (tree, elt list) prod) -> (elt list -> (tree, elt list) prod) -> elt list -> (tree, elt list)
      prod

    val treeify_aux : bool -> positive -> elt list -> (tree, elt list) prod

    val plength_aux : elt list -> positive -> positive

    val plength : elt list -> positive

    val treeify : elt list -> tree

    val filter_aux : (elt -> bool) -> tree -> clause list -> clause list

    val filter : (elt -> bool) -> t -> t

    val partition_aux : (elt -> bool) -> tree -> clause list -> clause list -> (clause list, clause list) prod

    val partition : (elt -> bool) -> t -> (t, t) prod

    val union_list : elt list -> elt list -> elt list -> elt list

    val linear_union : tree -> tree -> tree

    val inter_list : clause list -> elt list -> elt list -> elt list

    val linear_inter : tree -> tree -> tree

    val diff_list : elt list -> elt list -> elt list -> elt list

    val linear_diff : tree -> tree -> tree

    val skip_red : tree -> tree

    val skip_black : tree -> tree

    val compare_height : tree -> tree -> tree -> tree -> comparison

    val union : t -> t -> t

    val diff : t -> t -> t

    val inter : t -> t -> t

    val ltb_tree : clause -> tree -> bool

    val gtb_tree : clause -> tree -> bool

    val isok : tree -> bool

    module MX :
     sig
      module OrderTac :
       sig
        module OTF :
         sig
          type t = clause

          val compare : clause -> clause -> comparison

          val eq_dec : clause -> clause -> sumbool
         end

        module TO :
         sig
          type t = clause

          val compare : clause -> clause -> comparison

          val eq_dec : clause -> clause -> sumbool
         end
       end

      val eq_dec : clause -> clause -> sumbool

      val lt_dec : clause -> clause -> sumbool

      val eqb : clause -> clause -> bool
     end

    type coq_R_min_elt =
    | R_min_elt_0 of tree
    | R_min_elt_1 of tree * Color.t * tree * clause * tree
    | R_min_elt_2 of tree * Color.t * tree * clause * tree * Color.t * tree * clause * tree * elt option
       * coq_R_min_elt

    type coq_R_max_elt =
    | R_max_elt_0 of tree
    | R_max_elt_1 of tree * Color.t * tree * clause * tree
    | R_max_elt_2 of tree * Color.t * tree * clause * tree * Color.t * tree * clause * tree * elt option
       * coq_R_max_elt

    module L :
     sig
      module MO :
       sig
        module OrderTac :
         sig
          module OTF :
           sig
            type t = clause

            val compare : clause -> clause -> comparison

            val eq_dec : clause -> clause -> sumbool
           end

          module TO :
           sig
            type t = clause

            val compare : clause -> clause -> comparison

            val eq_dec : clause -> clause -> sumbool
           end
         end

        val eq_dec : clause -> clause -> sumbool

        val lt_dec : clause -> clause -> sumbool

        val eqb : clause -> clause -> bool
       end
     end

    val flatten_e : enumeration -> elt list

    val rcase : (tree -> clause -> tree -> 'a1) -> (tree -> 'a1) -> tree -> 'a1

    val rrcase : (tree -> clause -> tree -> clause -> tree -> 'a1) -> (tree -> 'a1) -> tree -> 'a1

    val rrcase' : (tree -> clause -> tree -> clause -> tree -> 'a1) -> (tree -> 'a1) -> tree -> 'a1
   end

  module E :
   sig
    type t = clause

    val compare : clause -> clause -> comparison

    val eq_dec : clause -> clause -> sumbool
   end

  type elt = clause

  type t_ = Raw.t
    (* singleton inductive, whose constructor was Mkt *)

  val this : t_ -> Raw.t

  type t = t_

  val mem : elt -> t -> bool

  val add : elt -> t -> t

  val remove : elt -> t -> t

  val singleton : elt -> t

  val union : t -> t -> t

  val inter : t -> t -> t

  val diff : t -> t -> t

  val equal : t -> t -> bool

  val subset : t -> t -> bool

  val empty : t

  val is_empty : t -> bool

  val elements : t -> elt list

  val choose : t -> elt option

  val fold : (elt -> 'a1 -> 'a1) -> t -> 'a1 -> 'a1

  val cardinal : t -> nat

  val filter : (elt -> bool) -> t -> t

  val for_all : (elt -> bool) -> t -> bool

  val exists_ : (elt -> bool) -> t -> bool

  val partition : (elt -> bool) -> t -> (t, t) prod

  val eq_dec : t -> t -> sumbool

  val compare : t -> t -> comparison

  val min_elt : t -> elt option

  val max_elt : t -> elt option

  val mk_opt_t : (elt, Raw.t) prod option -> (elt, t) prod option

  val remove_min : t_ -> (elt, t) prod option
 end

val clause_list2set : clause list -> M.t

val empty_clause : clause

val remove_trivial_atoms : pure_atom list -> pure_atom list

val subst_pures_delete : var -> expr -> pure_atom list -> pure_atom list

val isEq : comparison -> bool

val eq_space_atomlist : space_atom list -> space_atom list -> bool

val eq_var : positive -> positive -> bool

val drop_reflex_lseg : space_atom list -> space_atom list

val greater_than_expr : var -> expr -> bool

val greater_than_atom : pure_atom -> pure_atom -> bool

val greater_than_atoms : pure_atom -> pure_atom list -> bool

val greater_than_all : var -> pure_atom list -> bool

val merge : ('a1 -> 'a1 -> comparison) -> 'a1 list -> 'a1 list -> 'a1 list

val pure_atom2pn_atom : bool -> pure_atom -> pn_atom

val pn_atom_cmp : pn_atom -> pn_atom -> comparison

val pure_clause2pn_list : clause -> pn_atom list

val compare_clause2 : clause -> clause -> comparison

type ce_type =
| CexpL
| CexpR
| CexpEf

module DebuggingHooks :
 sig
  val print_new_pures_set : M.t -> M.t

  val print_wf_set : M.t -> M.t

  val print_unfold_set : M.t -> M.t

  val print_inferred_list : clause list -> clause list

  val print_pures_list : clause list -> clause list

  val print_eqs_list : clause list -> clause list

  val print_spatial_model : clause -> (var, expr) prod list -> clause

  val print_spatial_model2 : clause -> clause -> (var, expr) prod list -> clause

  val print_ce_clause :
    (var, expr) prod list -> clause -> ce_type -> (((var, expr) prod list, clause) prod, ce_type) prod
 end

val lookC : ('a1 -> 'a1 -> comparison) -> ('a1 -> 'a2) -> 'a1 -> ('a1, 'a2) prod list -> 'a2

val rewriteC : ('a2 -> 'a2 -> comparison) -> 'a2 -> 'a2 -> ('a1, 'a2) prod list -> ('a1, 'a2) prod list

val mergeC :
  ('a1 -> 'a1 -> comparison) -> ('a2 -> 'a2 -> comparison) -> ('a1 -> 'a2) -> 'a1 -> 'a1 -> ('a1, 'a2) prod list
  -> ('a1, 'a2) prod list

val cclose_aux : clause list -> (expr, expr) prod list

val cclose : clause list -> clause list

module Superposition :
 sig
  type model = (var, expr) prod list

  type superposition_result =
  | Valid
  | C_example of model * M.t
  | Aborted of clause list

  val pure_atom_gt1 : pure_atom -> pure_atom list -> bool

  val ef_aux :
    pure_atom list -> var -> expr -> expr -> pure_atom list -> pure_atom list -> clause list -> clause list

  val ef : ce_type -> clause -> clause list -> clause list

  val sp : ce_type -> clause -> clause -> clause list -> clause list

  val rewrite_expr : expr -> expr -> expr -> expr

  val rewrite_by : expr -> expr -> pure_atom -> pure_atom

  val rewrite_in_space : expr -> expr -> space_atom -> space_atom

  val rewrite_clause_in_space : clause -> space_atom -> space_atom

  val demodulate : clause -> clause -> clause

  val delete_resolved : clause -> clause

  val not_taut : clause -> bool

  val simplify : clause list -> clause -> clause

  val simplify_atoms : clause list -> space_atom list -> space_atom list

  val infer : ce_type -> clause -> clause list -> clause list

  val is_model_of : model -> pure_atom list -> pure_atom list -> bool

  val is_model_of_PI : model -> clause -> bool

  val reduces : model -> var -> bool

  val clause_generate : model -> clause -> (((var, expr) prod, clause) prod, ce_type) sum

  val partial_mod :
    model -> clause list -> clause list -> ((model, clause list) prod, ((model, clause) prod, ce_type) prod) sum

  val is_empty_clause : clause -> bool

  val is_unit_clause : clause -> bool

  val main_terminate :
    positive -> clause list -> clause list -> (((superposition_result, clause list) prod, M.t) prod, M.t) prod

  val main :
    positive -> clause list -> clause list -> (((superposition_result, clause list) prod, M.t) prod, M.t) prod

  val check_clauseset : M.t -> (((superposition_result, clause list) prod, M.t) prod, M.t) prod
 end

module HeapResolve :
 sig
  val normalize1_3 : clause -> clause -> clause

  val normalize2_4 : clause -> clause

  val norm : M.t -> clause -> clause

  val do_well1_2 : space_atom list -> pure_atom list list

  val next_in_dom : Ident.t -> space_atom list -> bool

  val next_in_dom1 : Ident.t -> expr -> space_atom list -> bool

  val next_in_dom2 : Ident.t -> expr -> space_atom list -> expr option

  val do_well3 : space_atom list -> pure_atom list list

  val lseg_in_dom2 : Ident.t -> expr -> space_atom list -> expr option

  val lseg_in_dom_atoms : Ident.t -> space_atom list -> pure_atom list

  val do_well4_5 : space_atom list -> pure_atom list list

  val do_well : space_atom list -> pure_atom list list

  val do_wellformed : clause -> M.t

  val spatial_resolution : clause -> clause -> M.t

  val unfolding1' :
    space_atom list -> space_atom list -> space_atom list -> (pure_atom, space_atom list) prod list

  val unfolding1 : clause -> clause -> clause list

  val unfolding2' :
    space_atom list -> space_atom list -> space_atom list -> (pure_atom, space_atom list) prod list

  val unfolding2 : clause -> clause -> clause list

  val unfolding3' : space_atom list -> space_atom list -> space_atom list -> space_atom list list

  val unfolding3 : clause -> clause -> clause list

  val unfolding4NPR' : space_atom list -> space_atom list -> space_atom list -> space_atom list list

  val unfolding4 : clause -> clause -> clause list

  val unfolding6NPR' :
    space_atom list -> space_atom list -> space_atom list -> (pure_atom, space_atom list) prod list

  val unfolding6 : clause -> clause -> clause list

  val mem_add : M.elt -> M.t -> M.t option

  val add_list_to_set_simple : M.elt list -> M.t -> M.t

  val add_list_to_set : M.elt list -> M.t -> M.t option

  val do_unfold' : clause -> clause -> clause list -> clause list

  val do_unfold : nat -> clause -> M.t -> M.t

  val unfolding : clause -> clause -> M.t
 end

module VeriStar :
 sig
  type veristar_result =
  | Valid
  | C_example of Superposition.model
  | Aborted of clause list * clause

  val pureb : clause -> bool

  val pure_clauses : clause list -> clause list

  val pures : M.t -> M.t

  val sublistg : ('a1 -> 'a1 -> comparison) -> 'a1 list -> 'a1 list -> bool

  val sublist : ('a1 -> 'a1 -> comparison) -> 'a1 list -> 'a1 list -> bool

  val impl_pure_clause : clause -> clause -> bool

  val relim1 : clause -> M.t -> M.t

  val incorp : M.t -> M.t -> M.t

  val the_loop_terminate : positive -> space_atom list -> clause -> M.t -> clause -> veristar_result

  val the_loop : positive -> space_atom list -> clause -> M.t -> clause -> veristar_result

  val check_entailment : entailment -> veristar_result
 end

val x : positive -> expr

val harder_ent : unit -> entailment

val main_h : unit -> VeriStar.veristar_result

val vs_hard : unit0 -> bool
