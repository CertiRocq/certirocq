(* Implementation of the Kempe/Chaitin algorithm for graph coloring,
   by Andrew W. Appel, 2011.

  Required reading:
  Formal Verification of Coalescing Graph-Coloring Register Allocation,
  by Sandrine Blazy, Benoit Robillard, and Andrew W. Appel.
  ESOP 2010: 19th European Symposium on Programming, pp. 145-164, March 2010.
  http://www.cs.princeton.edu/~appel/papers/regalloc.pdf

  We implement a program to K-color an undirected graph, perhaps leaving
  some nodes uncolored.  In a register-allocation problem, the graph nodes
  correspond to variables in a program, the colors correspond to registers,
  and the graph edges are interference constraints:  two nodes connected
  by an edge cannot be assigned the same color.  Nodes left uncolored are
  "spilled," that is, a register allocator would implement such nodes in
  memory locations instead of in registers.  We desire to have as few
  uncolored nodes as possible, but this desire is not formally specified.

  In this exercise we show a simple and unsophisticated algorithm; the program
  described by Blazy et al. (cited above) is more sophisticated in several ways,
  such as the use of "register coalescing" to get better results and the use of
  worklists to make it run faster.

  Our algorithm does, at least, make use of efficient data structures for
  representing undirected graphs, adjacency sets, and so on.

*)

(*  PRELIMINARIES:  EFFICIENT DATA STRUCTURES FOR REPRESENTING
    SETS OF NODES, and FUNCTIONS THAT MAP NODES TO WHATEVER *)

Require Import List ZArith Coq.micromega.Lia.
Require Import FSets.    (* Efficient functional sets *)
Require Import FMaps.  (* Efficient functional maps *)
Require Import Compare_dec.  (* to get lt_dec on natural numbers *)

(* The nodes in our graph will be taken from some ordered type, so that
  we can use efficient data structures for sets and maps.  FSets are a purely
  functional representation of sets over some element type,
  with logarithmic-time membership test and add-one-element,
  and linear-time or NlogN set union.  The type of keys (members of sets, indexes
  of maps) will be E.t;  and type type of sets will be S.t, and maps from E.t to A
  will be M.t(A) for any type A.

   We choose the "positive" type, because the Coq library has particularly efficient
   implementations of sets and maps on positives.  But our proofs will
  be easier if we hide the particular representation type.  We would like to say,
   Module E <: OrderedType := PositiveOrderedTypeBits.
   Module S <: (FSetInterface.S with Module E := E) := PositiveSet.
   Module M <: (FMapInterface.S with Module E := E) := PositiveMap.
  but for a stupid Coq technical reason (transparency of definitions interfering
  with rewrite tactics) we use the following clumsy definition instead:
*)
Module E : OrderedType with Definition t := BinPos.positive
                                      with Definition eq := (@eq BinPos.positive)
                                      with Definition lt := PositiveOrderedTypeBits.bits_lt
                                      with Definition eq_dec := PositiveOrderedTypeBits.eq_dec
                                      with Definition eq_refl := PositiveOrderedTypeBits.eq_refl
                                      with Definition eq_sym := PositiveOrderedTypeBits.eq_sym
                                      with Definition eq_trans := PositiveOrderedTypeBits.eq_trans
                                      with Definition lt_trans := PositiveOrderedTypeBits.lt_trans
                                      with Definition lt_not_eq := PositiveOrderedTypeBits.lt_not_eq
                                      with Definition compare := PositiveOrderedTypeBits.compare
     := PositiveOrderedTypeBits.
Module S : FSetInterface.S with Module E := E
                                         with Definition elt := PositiveSet.elt
                                         with Definition t := PositiveSet.t
                                         with Definition empty := PositiveSet.empty
                                     with Definition is_empty :=  PositiveSet.is_empty
                                     with Definition mem :=  PositiveSet.mem
                                     with Definition add := PositiveSet.add
                                     with Definition singleton :=  PositiveSet.singleton
                                     with Definition remove :=  PositiveSet.remove
                                     with Definition union :=  PositiveSet.union
                                     with Definition inter :=  PositiveSet.inter
                                     with Definition diff :=  PositiveSet.diff
                                     with Definition equal :=  PositiveSet.equal
                                     with Definition subset :=  PositiveSet.subset
                                     with Definition fold :=  PositiveSet.fold
                                     with Definition for_all :=  PositiveSet.for_all
                                     with Definition exists_ :=  PositiveSet.exists_
                                     with Definition filter :=  PositiveSet.filter
                                     with Definition partition :=  PositiveSet.partition
                                     with Definition cardinal :=  PositiveSet.cardinal
                                     with Definition elements :=  PositiveSet.elements
                                     with Definition choose :=  PositiveSet.choose
     := PositiveSet.

Module M : FMapInterface.S with Module E := E
                       with Definition t := PositiveMap.t
                       with Definition empty := PositiveMap.empty
                       with Definition is_empty := PositiveMap.is_empty
                       with Definition add := PositiveMap.add
                       with Definition find := PositiveMap.find
                       with Definition remove := PositiveMap.remove
                       with Definition mem := PositiveMap.mem
                       with Definition map := PositiveMap.map
                       with Definition mapi := PositiveMap.mapi
                       with Definition map2 := PositiveMap.map2
                       with Definition elements := PositiveMap.elements
                       with Definition cardinal := PositiveMap.cardinal
                       with Definition fold := PositiveMap.fold
                       with Definition equal := PositiveMap.equal
                       with Definition MapsTo := PositiveMap.MapsTo

 := PositiveMap.
Module Import WF := WFacts_fun E M.  (* Library of useful lemmas about maps *)
Module Import WP := WProperties_fun E M.  (* More useful stuff about maps *)

(* USEFUL LEMMAS ABOUT SETS AND MAPS *)

(* The domain of a map is the set of elements that map to Some(_) *)
Definition Mdomain {A} (m: M.t A) : S.t :=
   M.fold (fun n _ s => S.add n s) m S.empty.

Hint Resolve E.eq_refl E.eq_sym E.eq_trans.

Lemma StrictOrder_lt: StrictOrder E.lt.
(* This lemma useful when using the lemma SortA_equivlistA_eqlistA *)
Proof.
constructor.
unfold Irreflexive, Reflexive, complement.
intros; eapply E.lt_not_eq; eauto.
unfold Transitive.
intros; eapply M.E.lt_trans; eauto.
Qed.

Lemma lt_eq_trans: forall {x y z}, E.lt x y -> E.eq y z -> E.lt x z.
Proof.
intros. destruct (E.compare x z); auto.
apply E.lt_not_eq in H. contradiction H. transitivity z; auto.
contradiction (E.lt_not_eq (E.lt_trans l H)); auto.
Qed.

Lemma eq_lt_trans: forall {x y z}, E.eq x y -> E.lt y z -> E.lt x z.
Proof.
intros. destruct (E.compare x z); auto.
apply E.lt_not_eq in H0. contradiction H0. transitivity x; auto.
contradiction (E.lt_not_eq (E.lt_trans H0 l)); auto.
Qed.

Lemma Proper_lt: Proper (E.eq ==> E.eq ==> iff) E.lt.
Proof.
constructor; intros.
destruct (E.compare y y0); auto.
apply E.lt_not_eq in H1.  contradiction H1; congruence.
generalize (E.lt_trans (lt_eq_trans l (E.eq_sym H)) H1); intro.
apply E.lt_not_eq in H2. contradiction H2; auto.
generalize (lt_eq_trans H1 (E.eq_sym H0)); intro.
apply @eq_lt_trans with y; auto.
Qed.

(* Pay attention here to the use of SortA_equivlistA_eqlistA.
  Here we specialize it to the case there the comparison operator is E.lt,
  but in the proof of Mremove_elements we will use it specialized to a
  different (though related) total ordering on a different type of list elements. *)
Lemma SortE_equivlistE_eqlistE:
 forall l l', Sorted E.lt l -> Sorted E.lt l' -> equivlistA E.eq l l' -> eqlistA E.eq l l'.
Proof.
  apply SortA_equivlistA_eqlistA; auto.
  apply StrictOrder_lt.
  apply Proper_lt.
Qed.

Lemma filter_sortE: forall f l, Sorted E.lt l -> Sorted E.lt (List.filter f l).
(* This lemma is useful in the proof of Sremove_elements *)
Proof.
apply filter_sort with E.eq; auto.
apply StrictOrder_lt.
apply Proper_lt.
Qed.

(* EX3 (Sremove_elements) *)
Lemma Sremove_elements:  forall (i: E.t) (s: S.t),
  S.In i s ->
     eqlistA E.eq (S.elements (S.remove i s))
              (List.filter (fun x => if E.eq_dec x i then false else true) (S.elements s)).
Proof.
intros.
assert (PROPER: Proper (E.eq ==> eq)
  (fun x : E.t => if F.eq_dec x i then false else true)).
(* ADMIT *)
intro; intros; destruct (F.eq_dec x i); destruct (F.eq_dec y i); auto;
       contradiction n; congruence.
(* /ADMIT *)
apply SortE_equivlistE_eqlistE; auto.
(* ADMITTED *)
apply S.elements_3.
apply filter_sortE; auto. apply S.elements_3.
intro j; intuition.
rewrite filter_InA; auto.
destruct (E.eq_dec j i).
symmetry in e; apply (@S.remove_1 s i j) in e.
contradiction e. apply S.elements_2. auto.
apply S.elements_2 in H0.
apply S.remove_3 in H0;
split; auto.
apply S.elements_1; auto.
apply S.elements_1.
rewrite filter_InA in H0; auto.
destruct H0.
destruct (F.eq_dec j i); try discriminate.
apply S.remove_2; auto.
apply S.elements_2; auto.
Qed.
(* /ADMITTED *)
(** [] *)

(* EX2 (InA_map_fst_key) *)
Lemma InA_map_fst_key:
 forall A j l, InA E.eq j (map (@fst _ A) l) <-> exists e, InA (@M.eq_key_elt _) (j,e) l.
(* ADMITTED *)
Proof.
induction l; simpl; intuition. apply InA_nil in H; intuition.
destruct H. apply InA_nil in H; intuition.
inversion H1; clear H1; subst.
exists b. constructor; auto. unfold M.eq_key_elt.  split; auto; apply H3.
destruct (H H3). exists x; constructor 2; auto.
destruct H1. inversion H1; clear H1; subst.
constructor 1; auto. destruct H3; auto. constructor 2.
apply H0. exists x.  auto.
Qed.
(* /ADMITTED *)
(** [] *)

(* EX3 (cardinal_map) *)
Lemma cardinal_map:  forall A B (f: A -> B) g, M.cardinal (M.map f g) = M.cardinal g.
(* ADMITTED *)
Proof.
intros.
do 2 rewrite M.cardinal_1.
transitivity (length (map (@fst _ _) (M.elements (M.map f g)))).
rewrite length_map; auto.
transitivity (length (map (@fst _ _) (M.elements g))).
2: rewrite length_map; auto.
apply eqlistA_length with E.eq.
apply SortE_equivlistE_eqlistE; auto.
generalize (M.elements_3 (M.map f g)).
remember (M.elements (M.map f g)) as l; clear; induction 1.
constructor.
constructor; auto.
clear - H0; induction H0. constructor.
constructor; auto.
generalize (M.elements_3 g).
remember (M.elements g) as l; clear; induction 1.
constructor.
constructor; auto.
clear - H0; induction H0. constructor.
constructor; auto.
intro j.
do 2 rewrite InA_map_fst_key.
intuition. destruct H as [e ?]. apply M.elements_2 in H.
rewrite map_mapsto_iff in H.
destruct H as [a [? ?]]. subst e. exists a.
apply M.elements_1. auto.
destruct H as [e ?].
apply M.elements_2 in H. exists (f e).
apply M.elements_1. rewrite map_mapsto_iff. exists e; split; auto.
Qed.
(* /ADMITTED *)
(** [] *)

(* EX3 (Sremove_cardinal_less) *)
Lemma Sremove_cardinal_less: forall i s, S.In i s ->
        S.cardinal (S.remove i s) < S.cardinal s.
(* ADMITTED *)
Proof.
intros.
repeat rewrite S.cardinal_1.
generalize (Sremove_elements _ _ H); intro.
change S.elt with E.t.
rewrite (eqlistA_length H0).
clear H0.
apply S.elements_1 in H.
remember (S.elements s) as al.
clear s Heqal.
remember (fun x : E.t => if F.eq_dec x i then false else true) as f.
assert (forall x, E.eq x i <-> f x = false).
 subst. intros. destruct (F.eq_dec x i); intuition.  inversion H0.
clear Heqf.
induction H; simpl.
destruct (H0 y).
symmetry in H. rewrite (H1 H).
clear. induction l; simpl; intros. auto. destruct (f a). simpl; auto. lia.
lia.
destruct (f y). simpl; lia. lia.
Qed.
(* /ADMITTED *)
(** [] *)

(* EX2 (eqv_eq_key_elt) *)
Lemma eqv_eq_key_elt: forall elt, Equivalence (@M.eq_key_elt elt).
(* This lemma is useful in the proof of Mremove_elements *)
(* ADMITTED *)
Proof.
 intros. unfold M.eq_key_elt; split; repeat intro; intuition.
   eapply M.E.eq_trans; eauto. rewrite H2; auto.
Qed.
(* /ADMITTED *)
(** [] *)

(* EX3 (Mremove_elements) *)
Lemma Mremove_elements:  forall A i s,
  M.In i s ->
     eqlistA (@M.eq_key_elt A) (M.elements (M.remove i s))
              (List.filter (fun x => if E.eq_dec (fst x) i then false else true) (M.elements s)).
(* ADMITTED *)
Proof.
intros.
assert (SO: StrictOrder (fun x y : E.t * A => E.lt (fst x) (fst y))).
constructor. repeat intro. apply StrictOrder_lt in H0; auto.
repeat intro. eapply StrictOrder_lt; eauto.
assert (PR: Proper (@M.eq_key_elt A ==> @M.eq_key_elt A ==> iff)
                (fun x y : E.t * A => E.lt (fst x) (fst y))).
repeat intro. destruct H0; destruct H1.
intuition. apply @eq_lt_trans with (fst x); auto. apply @lt_eq_trans with (fst x0); auto.
apply @eq_lt_trans with (fst y); auto. apply @lt_eq_trans with (fst y0); auto.
assert (PR': Proper (@M.eq_key_elt A ==> eq)
  (fun x : E.t * A => if F.eq_dec (fst x) i then false else true)).
clear. repeat intro.
destruct H. change M.key with E.t in *.
  destruct (F.eq_dec (fst x) i); destruct (F.eq_dec (fst y) i); auto; contradiction n; eauto.

apply SortA_equivlistA_eqlistA with (fun x y => E.lt (fst x) (fst y)); auto.
apply eqv_eq_key_elt.
apply M.elements_3.
apply filter_sort with (@M.eq_key_elt A); auto.
apply eqv_eq_key_elt.
apply M.elements_3.
intro j; intuition.
rewrite filter_InA; auto.
simpl.
destruct (F.eq_dec a i).
symmetry in e; apply (@M.remove_1 _ s i a) in e.
contradiction e. apply M.elements_2 in H0. exists b. auto.
apply M.elements_2 in H0.
apply M.remove_3 in H0;
split; auto.
apply M.elements_1; auto.
apply M.elements_1.
rewrite filter_InA in H0; auto.
destruct H0. simpl in H1.
destruct (F.eq_dec a i); try discriminate.
apply M.remove_2; auto.
apply M.elements_2; auto.
Qed.
(* /ADMITTED *)
(** [] *)

(* EX3 (Mremove_cardinal_less) *)
Lemma Mremove_cardinal_less: forall A i (s: M.t A), M.In i s ->
        M.cardinal (M.remove i s) < M.cardinal s.
(* ADMITTED *)
Proof.
intros.
repeat rewrite M.cardinal_1.
generalize (Mremove_elements _ _ _ H); intro.
change M.key with E.t in *.
rewrite (eqlistA_length H0).
clear H0.
destruct H. apply M.elements_1 in H.
remember (M.elements s) as al.
clear s Heqal.
remember (fun x : E.t * A => if F.eq_dec (fst x) i then false else true) as f.
assert (forall x, E.eq (fst x) i <-> f x = false).
 subst. intros. destruct (F.eq_dec (fst x0) i); intuition.  inversion H0.
clear Heqf.
induction H; simpl.
destruct H as [H H'].
destruct (H0 y).
symmetry in H. rewrite (H1 H).
clear. induction l; simpl; intros. auto. destruct (f a). simpl; auto. lia.
lia.
destruct (f y). simpl; lia. lia.
Qed.
(* /ADMITTED *)
(** [] *)

(* EX2 (two_little_lemmas) *)

Lemma fold_right_rev_left:
  forall (A B: Type) (f: A -> B -> A) (l: list B) (i: A),
  fold_left f l i = fold_right (fun x y => f y x) i (rev l).
(* ADMITTED *)
Proof.
intros. rewrite fold_left_rev_right.
induction l; simpl; auto.
Qed.
(* /ADMITTED *)

Lemma Snot_in_empty: forall n, ~ S.In n S.empty.
(* ADMITTED *)
Proof.
intros. intro.
apply S.empty_1 in H.
auto.
Qed.
(* /ADMITTED *)
(** [] *)

(* EX3 (Sin_domain) *)
Lemma Sin_domain: forall A n (g: M.t A), S.In n (Mdomain g) <-> M.In n g.
(* ADMITTED *)
Proof.
unfold Mdomain.
intros.
rewrite M.fold_1.
rewrite elements_in_iff.
remember (M.elements g) as al. clear g Heqal.
assert ((exists e : A, InA (@M.eq_key_elt _) (n, e) al) <->
            (exists e : A, InA (@M.eq_key_elt _) (n, e) (rev al))).
split; intros [e ?]; exists e; rewrite (InA_rev) in *; auto; apply eqv_eq_key_elt.
rewrite H; clear H.
rewrite fold_right_rev_left.
remember (rev al) as bl; clear al Heqbl.
induction bl; simpl; auto.
intuition.
contradiction (Snot_in_empty n); auto.
destruct H. inversion H.
intuition.
destruct (E.eq_dec n a0).
exists b; constructor; auto.  split; auto.
apply (@S.add_3 _ a0 n) in H1.
apply H in H1. destruct H1 as [e ?].
exists e. constructor 2. auto.
contradict n0. apply E.eq_sym; auto.
destruct H1 as [e ?].
inversion H1; clear H1; subst.
destruct H3. simpl in *. subst e.
apply S.add_1. apply E.eq_sym; apply H1.
apply S.add_2. apply H0.
clear - H3.
exists e.
auto.
Qed.
(* /ADMITTED *)
(** [] *)

(* Now begins the graph coloring program *)

Definition node := E.t.
Definition nodeset := S.t.
Definition nodemap: Type -> Type := M.t.
Definition graph := nodemap nodeset.

Definition adj (g: graph) (i: node) : nodeset :=
  match M.find i g with Some a => a | None => S.empty end.

Definition undirected (g: graph) :=
   forall i j, S.In j (adj g i) -> S.In i (adj g j).

Definition no_selfloop (g: graph) := forall i, ~ S.In i (adj g i).

Definition nodes (g: graph) := Mdomain g.

Definition subset_nodes
                    {P: node -> nodeset -> Prop}
                    (P_dec: forall n adj, {P n adj}+{~P n adj})
                    (g: graph) :=
   M.fold (fun n adj s => if P_dec n adj then S.add n s else s) g S.empty.

(* We need to prove some lemmas related to the termination of the algorithm
  before we can actually define the Function *)

(* EX3 (subset_notes_sub) *)
Lemma subset_nodes_sub:  forall P f g, S.Subset (@subset_nodes P f g) (nodes g).
(* ADMITTED *)
Proof.
intros.
intro i.
set (R x y := S.In i x -> S.In i y).
assert (R (subset_nodes f g) (nodes g)); [ | auto].
unfold subset_nodes, nodes.
apply WP.fold_rel.
unfold R; auto.
unfold R; clear R; intros.
destruct (f k e).
destruct (S.E.eq_dec i k).
apply S.add_1; auto.
apply S.add_2.
apply H0.
eapply S.add_3; eauto.
apply S.add_2. auto.
Qed.
(* /ADMITTED *)
(** [] *)

Definition low_deg (K: nat) (n: node) (adj: nodeset) := S.cardinal adj < K.

Lemma low_deg_dec: forall K n adj, {low_deg K n adj}+{~low_deg K n adj}.
Proof.
intros. unfold low_deg. destruct (lt_dec (S.cardinal adj0) K); auto.
Defined.  (* Must use Defined here instead of Qed so it Computes *)

Definition remove_node (n: node) (g: graph) : graph :=
  M.map (S.remove n) (M.remove n g).

(* EX3 (select_terminates) *)
Lemma select_terminates:
  forall (K: nat) (g : graph) (n : S.elt),
   S.choose (subset_nodes (low_deg_dec K) g) = Some n ->
   M.cardinal (remove_node n g) < M.cardinal g.
(* ADMITTED *)
Proof.
intros.
unfold remove_node.
rewrite cardinal_map.
apply Mremove_cardinal_less.
apply S.choose_1 in H.
apply subset_nodes_sub in H.
rewrite <- Sin_domain. auto.
Qed.
(* /ADMITTED *)
(** [] *)

Require Recdef.

Function select (K: nat) (g: graph) {measure M.cardinal g}: list node :=
  match S.choose (subset_nodes (low_deg_dec K) g) with
  | Some n => n :: select K (remove_node n g)
  | None => nil
  end.
Proof. apply select_terminates.
Defined.  (* Do not use Qed on a Function, otherwise it won't Compute! *)

Definition coloring := M.t node.

Definition colors_of (f: coloring) (s: S.t) : S.t :=
   S.fold (fun n s => match M.find n f with Some c => S.add c s | None => s end) s S.empty.

Definition color1 (palette: S.t) (g: graph) (n: node) (f: coloring) : coloring :=
   match S.choose (S.diff palette (colors_of f (adj g n))) with
   | Some c => M.add n c f
   | None => f
   end.

Definition color (palette: S.t) (g: graph) : coloring :=
  fold_right (color1 palette g)  (M.empty _) (select (S.cardinal palette) g).

(* Now, the proof of correctness of the algorithm.
  We want to show that any coloring produced by the [color] function
  actually respects the interference constraints.  This property is
  called [coloring_ok].
*)

Definition coloring_ok (palette: S.t) (g: graph) (f: coloring) :=
 forall i j, S.In j (adj g i) ->
     (forall ci, M.find i f = Some ci -> S.In ci palette) /\
     (forall ci cj, M.find i f = Some ci -> M.find j f = Some cj -> ci<>cj).

(* EX2 (adj_ext) *)
Lemma adj_ext: forall g i j, E.eq i j -> S.eq (adj g i) (adj g j).
(* ADMITTED *)
Proof.
unfold adj; intros.
rewrite (F.find_o _ H). apply S.eq_refl.
Qed.
(* /ADMITTED *)
(** [] *)

(* EX3 (in_colors_of_1) *)
Lemma in_colors_of_1:
  forall i s f c, S.In i s -> M.find i f = Some c -> S.In c (colors_of f s).
(* ADMITTED *)
Proof.
intros.
unfold colors_of.
rewrite S.fold_1.
rewrite fold_right_rev_left.
apply S.elements_1 in H.
apply InA_rev in H; auto.
change E.t with S.elt in H.
remember (rev (S.elements s)) as al; clear s Heqal.
revert H; induction al; simpl; intros; auto.
inversion H.
inversion H; clear H; subst.
rewrite (F.find_o _ H2) in H0.
change node with S.elt; rewrite H0.
apply S.add_1; auto.
specialize (IHal H2).
change node with S.elt.
case_eq (M.find a f); intros.
apply S.add_2. auto.
auto.
Qed.
(* /ADMITTED *)
(** [] *)

(* EX3 (color_correct) *)
Theorem color_correct:
  forall palette g,
       no_selfloop g ->
       undirected g ->
       coloring_ok palette g (color palette g).
(* ADMITTED *)
Proof.
unfold color.
intros palette g NS UD.
remember (select (S.cardinal palette) g) as nl; clear Heqnl.
rename nl into al.
split.
clear j H.
revert i; induction al; simpl; intros.
rewrite F.empty_o in H. inversion H.
remember (fold_right (color1 palette g) (M.empty node) al) as f.
clear Heqf.
unfold color1 in *.
revert H; case_eq (S.choose (S.diff palette (colors_of f (adj g a)))); intros.
apply S.choose_1 in H.
destruct (E.eq_dec i a).
rewrite F.add_eq_o in H0; auto. inversion H0; clear H0; subst.
apply S.diff_1 in H; auto.
rewrite F.add_neq_o in H0; auto.
apply (IHal _ _ H0).
apply (IHal _ _ H0).

revert i j H; induction al; simpl; intros.
rewrite F.empty_o in H0. inversion H0.
remember (fold_right (color1 palette g) (M.empty node) al) as f.
clear Heqf.
intro. subst cj; rename ci into c.
destruct (E.eq_dec i a).
unfold color1 at 1 in H0.
revert H0; case_eq (S.choose (S.diff palette (colors_of f (adj g a)))); intros.
apply S.choose_1 in H0.
rewrite F.add_eq_o in H2; auto.
inversion H2; clear H2; subst e0.
destruct (E.eq_dec j a).
apply (@S.In_1 _ j i) in H; eauto.
apply NS in H. auto.
unfold color1  in H1.
revert H1; case_eq (S.choose (S.diff palette (colors_of f (adj g a)))); intros.
apply S.choose_1 in H1.
rewrite F.add_neq_o in H2; auto.
apply S.diff_2 in H0.
clear e0 H1.
apply (adj_ext g i a e j) in H.
remember (adj g a) as s.
clear - H H0 H2.
contradiction H0; clear H0.
eapply in_colors_of_1; eauto.
apply S.choose_2 in H1.
clear - H0 H1.
apply H1 in H0. auto.
unfold color1 in H1.
rewrite H0 in H1.
unfold coloring_ok in IHal.
specialize (IHal _ _ H).
specialize (IHal _ _ H2 H1).
contradiction IHal; auto.
unfold color1 in *.
revert H0 H1; case_eq (S.choose (S.diff palette (colors_of f (adj g a)))); intros.
apply S.choose_1 in H0.
rewrite F.add_neq_o in H1; auto.
apply S.diff_2 in H0.
destruct (E.eq_dec j a).
rewrite F.add_eq_o in H2; auto.
inversion H2; clear H2; subst e.
apply (@S.In_1 _ j a) in H; eauto.
clear j e0.
unfold undirected in UD.
apply UD in H; auto.
remember (adj g a) as s.
contradiction H0; clear H0.
eapply in_colors_of_1; eauto.
rewrite F.add_neq_o in H2; auto.
eapply IHal; eauto.
eapply IHal; eauto.
Qed.
(* /ADMITTED *)
(** [] *)

(* GRAPH PARSIING *)

Definition graph_description : Type := Z * list (Z * list Z).

Lemma Z_pred_less_nat:
  forall i : Z, (i >? 0)%Z = true -> Z.to_nat (Z.pred i) < Z.to_nat i.
Proof.
 intros.  rewrite Z2Nat.inj_pred. apply Z.gtb_lt in H.
 apply Nat.lt_pred_l. intro.
 pose proof (Z2Nat.id i). rewrite H0 in H1. simpl in H1.
 absurd (0%Z=i). lia. apply H1; lia.
Defined.

Function iota' (i: Z) (al: list Z) {measure Z.to_nat i} : list Z :=
 if Z.gtb i 0
 then  iota' (Z.pred i) (Z.pred i :: al)
 else rev_append nil al.
Proof. intros; apply Z_pred_less_nat; auto. Defined.

Definition iota (i: Z) : list Z := iota' i nil.

Function clique (k: Z) {measure Z.to_nat k} : list (Z * Z) :=
 if Z.gtb k 0 then
  clique (k-1) ++ map (fun i => ((k-1)%Z, i)) (iota (k-1))
 else nil.
Proof. intros; apply Z_pred_less_nat; auto. Defined.

Definition zzlist_to_poslist : list (Z*Z) -> list (positive*positive) :=
  map (fun ij => (Z.to_pos (Z.succ (fst ij)), Z.to_pos (Z.succ (snd ij)))).

Definition translate_adj_list (a: (Z * list Z)) : list (Z * Z) :=
 let (i, al) := a in
 map (fun j => (i,j)) al.

Definition parse_graph (G: graph_description) : list (positive * positive) :=
  let (k,L) := G in
   zzlist_to_poslist (concat (clique k :: map translate_adj_list L)).

Definition make_palette (G: graph_description) : S.t :=
  fold_right S.add S.empty (map (Basics.compose Z.to_pos Z.succ) (iota (fst G))).

Definition add_edge (e: (E.t*E.t)) (g: graph) : graph :=
 M.add (fst e) (S.add (snd e) (adj g (fst e)))
  (M.add (snd e) (S.add (fst e) (adj g (snd e))) g).

Definition mk_graph (el: list (E.t*E.t)) :=
  fold_right add_edge (M.empty _) el.




Definition run (G: graph_description) :=
  let result := M.elements (color (make_palette G) (mk_graph (parse_graph G)))
  in (fst G + Z.of_nat (length (snd G)), Z.of_nat (length result))%Z.

(* TEST CASE *)

Delimit Scope positive_scope with positive.

(* Let's use only three colors *)
Definition palette: S.t := fold_right S.add S.empty (1::2::3::nil)%positive.


Definition mygraph := mk_graph ( (5,6)::(6,2)::(5,2)::(1,5)::(1,2)::(2,4)::(1,4)::nil)%positive.

Definition ex_1 := (S.elements (Mdomain mygraph)).
(*   = 4%positive
       :: 2%positive :: 6%positive :: 1%positive :: 5%positive :: nil
     : list S.elt
*)

Definition ex_2 := (M.elements (color palette mygraph)).
(*   = (4%positive, 1%positive)
       :: (2%positive, 3%positive)
          :: (6%positive, 2%positive)
             :: (1%positive, 2%positive) :: (5%positive, 1%positive) :: nil
     : list (M.key * node)
*)

Import ListNotations.
Definition G16 : graph_description :=
(16, [
(32,[8;0;6;7;1;2]);
(33,[8;0;6;7;1]);
(34,[8;0;7;6;35;36;37;38;40;39;41;42;43;44;45;46;47;48;49;50;51;52;53;54;55;56;57;58;59;60;61;62;63;64;65;66;67;68;69;70;71;72;73;74;75;76;77;78;79;80;81;82;83;84;85;86;87;88;89;90;91;92;93;94;95;96;97;98;99;100;101;102;103;104;105;106;107;108;109;110;111;112;113;114;115;116;117;118;119;120;121;122;123;124;125;126;127;128;129;130;131;132;133;134;135;136;137;138;139;140;141;142;143;144;145;146;147;148;149;150;151;152;153;154]);
(35,[8;0;34;7;36;37;38;40;39;41;42;43;44;45;46;47;48;49;50;51;52;53;54;55;56;57;58;59;60;61;62;63;64;65;66;67;68;69;70;71;72;73;74;75;76;77;78;79;80;81;82;83;84;85;86;87;88;89;90;91;92;93;94;95;96;97;98;99;100;101;102;103;104;105;106;107;108;109;110;111;112;113;114;115;116;117;118;119;120;121;122;123;124;125;126;127;128;129;130;131;132;133;134;135;136;137;138;139;140;141;142;143;144;145;146;147;148;149;150;151;152;153;154]);
(36,[0;34;35;8;37;38;40;39;41;42;43;44;45;46;47;48;49;50;51;52;53;54;55;56;57;58;59;60;61;62;63;64;65;66;67;68;69;70;71;72;73;74;75;76;77;78;79;80;81;82;83;84;85;86;87;88;89;90;91;92;93;94;95;96;97;98;99;100;101;102;103;104;105;106;107;108;109;110;111;112;113;114;115;116;117;118;119;120;121;122;123;124;125;126;127;128;129;130;131;132;133;134;135;136;137;138;139;140;141;142;143;144;145;146;147;148;149;150;151;152;153;154;155;156;3;2;6]);
(37,[36;34;35;0;38;40;39;41;42;43;44;45;46;47;48;49;50;51;52;53;54;55;56;57;58;59;60;61;62;63;64;65;66;67;68;69;70;71;72;73;74;75;76;77;78;79;80;81;82;83;84;85;86;87;88;89;90;91;92;93;94;95;96;97;98;99;100;101;102;103;104;105;106;107;108;109;110;111;112;113;114;115;116;117;118;119;120;121;122;123;124;125;126;127;128;129;130;131;132;133;134;135;136;137;138;139;140;141;142;143;144;145;146;147;148;149;150;151;152;153;154;155;156;3;2;6;7]);
(38,[36;37;34;35]);
(39,[36;37;34;35;41;42;43;44;45;46;47;48;49;50;51;52;53;54;55;56;57;58;59;60;61;62;63;64;65;66;67;68;69;70;71;72;73;74;75;76;77;78;79;80;81;82;83;84;85;86;87;88;89;90;91]);
(40,[36;37;34;35]);
(41,[36;37;39;35;34;42;43;44;45;46;47;48;49;50;51;52;53;54;55;56;57;58;59;60;61;62;63;64;65;66;67;68;69;70;71;72;73;74]);
(42,[36;37;41;39;35;34]);
(43,[36;37;41;39;35;34]);
(44,[36;37;41;39;35;34]);
(45,[36;37;39;35;34;41;46;47;48;49;50;51;52;53;54;55;56;57;58;59;60;61;62;63;64;65;66;67;68;69;70;71]);
(46,[36;37;45;39;35;34;41]);
(47,[36;37;45;39;35;34;41]);
(48,[36;37;45;39;35;34;41]);
(49,[36;37;39;35;34;41;45;50;51;52;53;54;55;56;57;58;59;60;61;62;63;64;65;66;67;68;69;70;71]);
(50,[36;37;49;39;35;34;41;45]);
(51,[36;37;49;39;35;34;41;45]);
(52,[36;37;49;39;35;34;41;45]);
(53,[36;37;39;35;34;41;45;49;54;55;56;57;58;59;60;61;62;63;64;65;66;67;68;69;70;71]);
(54,[36;37;39;35;34;41;45;49;53;55;56;57;58;59;60;61;62;63;64;65;66;67;68;69;70;71;72;73;74;75;76;77;78;79;80;81;82;83;84;85;86;87;88;89;90;91;92;93;94;95;96;97;98;99;100;101;102;103;104;105;106;107;108;109;110;111;112;113;114;115;116;117;118;119;120;121;122;123;124;125;126;127;128;129;130;131;132;133;134;135;136;137;138;139;140;141;142;143;144;145;146;147;148;149;150;151;152;153;154;155;156;3]);
(55,[36;37;54;39;35;34;41;45;49;53]);
(56,[36;37;54;39;35;34;41;45;49;53]);
(57,[36;37;54;39;35;34;41;45;49;53]);
(58,[36;37;54;39;35;34;41;45;49;53;59;60;61;62;63;64;65;66;67;68;69;70;71;72;73]);
(59,[36;37;54;39;35;34;41;45;49;53;58]);
(60,[36;37;54;39;35;34;41;45;49;53;58]);
(61,[36;37;54;39;35;34;41;45;49;53;58]);
(62,[36;37;54;39;35;34;41;45;49;58;53;63;64;65;66;67;68;69;70;71;72;73]);
(63,[36;37;54;39;35;34;41;45;49;62;58;53]);
(64,[36;37;54;39;35;34;41;45;49;62;58;53]);
(65,[36;37;54;39;35;34;41;45;49;62;58;53]);
(66,[36;37;54;39;35;34;41;45;62;58;53;49;67;68;69;70;71;72;73]);
(67,[36;37;54;39;35;34;41;45;66;62;58;53;49]);
(68,[36;37;54;39;35;34;41;45;66;62;58;53;49]);
(69,[36;37;54;39;35;34;41;45;66;62;58;53;49]);
(70,[36;37;54;39;35;34;41;66;62;58;53;49;45;71;72;73]);
(71,[36;37;54;39;35;34;41;70;66;62;58;53;49;45]);
(72,[36;37;54;39;35;34;41;70;66;62;58]);
(73,[36;37;54;39;35;34;41;70;66;62;58]);
(74,[36;37;54;39;35;34;41]);
(75,[36;37;54;39;35;34]);
(76,[36;37;54;35;34;39;77;78]);
(77,[36;37;54;35;34;39;76;78;79;80;81;82;83;84;85;86;87;88;89;90;91;92;93;94;95;96;97;98;99;100;101;102;103;104;105;106;107;108;109;110;111;112;113;114;115;116;117;118;119;120;121;122;123;124;125;126;127;128;129;130;131;132;133;134;135;136;137;138;139;140;141;142;143;144;145;146;147;148;149;150;151;152;153;154]);
(78,[36;37;54;77;35;34;39;76]);
(79,[36;37;54;77;35;34;39]);
(80,[36;37;54;77;35;34;39]);
(81,[36;37;54;77;35;34;39]);
(82,[36;37;54;77;35;34;39]);
(83,[36;37;54;77;35;34;39]);
(84,[36;37;54;77;35;34;39]);
(85,[36;37;54;77;35;34;39]);
(86,[36;37;54;77;35;34;39]);
(87,[36;37;54;77;35;34;39]);
(88,[36;37;54;77;35;34;39]);
(89,[36;37;54;77;35;34;39]);
(90,[36;37;54;77;35;34;39]);
(91,[36;37;54;77;35;34;39]);
(92,[36;37;54;77;35;34]);
(93,[36;37;54;77;35;34;94;95;96;97;98;99;100;101;102;103;104;105;106;107;108;109;110;111;112;113;114;115;116;117;118;119;120;121;122;123;124;125;126;127;128;129;130;131;132;133;134;135;136;137;138;139;140;141;142;143;144;145;146;147;148;149;150;151;152;153;154]);
(94,[36;37;54;77;35;34;93]);
(95,[36;37;54;77;35;34;93]);
(96,[36;37;54;77;35;34;93;97]);
(97,[36;37;54;77;35;34;93;96]);
(98,[36;37;54;77;35;34;93]);
(99,[36;37;54;77;35;34;93]);
(100,[36;37;54;77;35;34;93;101;102;103;104;105;106;107;108;109;110;111;112;113;114;115;116;117;118;119;120;121;122;123;124;125;126;127;128;129;130;131;132;133;134;135;136;137;138;139;140;141;142;143;144;145;146;147;148;149;150;151;152;153;154]);
(101,[36;37;54;77;35;34;93;100]);
(102,[36;37;54;77;35;34;93;100]);
(103,[36;37;54;77;35;34;93;100;104]);
(104,[36;37;54;77;35;34;93;100;103]);
(105,[36;37;54;77;35;34;93;100]);
(106,[36;37;54;77;35;34;93;100]);
(107,[36;37;54;77;35;34;93;100;108;109;110;111;112;113;114;115;116;117;118;119;120;121;122;123;124;125;126;127;128;129;130;131;132;133;134;135;136;137;138;139;140;141;142;143;144;145;146;147;148;149;150;151;152;153;154]);
(108,[36;37;54;77;35;34;93;100;107]);
(109,[36;37;54;77;35;34;93;100;107]);
(110,[36;37;54;77;35;34;93;100;107;111]);
(111,[36;37;54;77;35;34;93;100;107;110]);
(112,[36;37;54;77;35;34;93;100;107]);
(113,[36;37;54;77;35;34;93;100;107]);
(114,[36;37;54;77;35;34;93;100;107;115;116;117;118;119;120;121;122;123;124;125;126;127;128;129;130;131;132;133;134;135;136;137;138;139;140;141;142;143;144;145;146;147;148;149;150;151;152;153;154]);
(115,[36;37;54;77;35;34;93;100;107;114]);
(116,[36;37;54;77;35;34;93;100;107;114]);
(117,[36;37;54;77;35;34;93;100;107;114;118]);
(118,[36;37;54;77;35;34;93;100;107;114;117]);
(119,[36;37;54;77;35;34;93;100;107;114]);
(120,[36;37;54;77;35;34;93;100;107;114]);
(121,[36;37;54;77;35;34;93;100;107;114;122;123;124;125;126;127;128;129;130;131;132;133;134;135;136;137;138;139;140;141;142;143;144;145;146;147;148;149;150;151;152;153;154]);
(122,[36;37;54;77;35;34;93;100;107;114;121]);
(123,[36;37;54;77;35;34;93;100;107;114;121]);
(124,[36;37;54;77;35;34;93;100;107;114;121;125]);
(125,[36;37;54;77;35;34;93;100;107;114;121;124]);
(126,[36;37;54;77;35;34;93;100;107;114;121]);
(127,[36;37;54;77;35;34;93;100;107;114;121]);
(128,[36;37;54;77;35;34;93;100;107;121;114;129;130;131;132;133;134;135;136;137;138;139;140;141;142;143;144;145;146;147;148;149;150;151;152;153;154]);
(129,[36;37;54;77;35;34;93;100;107;128;121;114]);
(130,[36;37;54;77;35;34;93;100;107;128;121;114]);
(131,[36;37;54;77;35;34;93;100;107;128;121;114;132]);
(132,[36;37;54;77;35;34;93;100;107;128;121;114;131]);
(133,[36;37;54;77;35;34;93;100;107;128;121;114]);
(134,[36;37;54;77;35;34;93;100;107;128;121;114]);
(135,[36;37;54;77;35;34;93;100;128;121;114;107;136;137;138;139;140;141;142;143;144;145;146;147;148;149;150;151;152;153;154]);
(136,[36;37;54;77;35;34;93;100;135;128;121;114;107]);
(137,[36;37;54;77;35;34;93;100;135;128;121;114;107]);
(138,[36;37;54;77;35;34;93;100;135;128;121;114;107;139]);
(139,[36;37;54;77;35;34;93;100;135;128;121;114;107;138]);
(140,[36;37;54;77;35;34;93;100;135;128;121;114;107]);
(141,[36;37;54;77;35;34;93;100;135;128;121;114;107]);
(142,[36;37;54;77;35;34;93;135;128;121;114;107;100;143;144;145;146;147;148;149;150;151;152;153;154]);
(143,[36;37;54;77;35;34;93;142;135;128;121;114;107;100]);
(144,[36;37;54;77;35;34;93;142;135;128;121;114;107;100]);
(145,[36;37;54;77;35;34;93;142;135;128;121;114;107;100;146;147]);
(146,[36;37;54;77;35;34;93;142;135;128;121;114;107;100;145]);
(147,[36;37;54;77;35;34;93;142;135;128;121;114;107;100;145]);
(148,[36;37;54;77;35;34;93;142;135;128;121;114;107;100;149]);
(149,[36;37;54;77;35;34;93;142;135;128;121;114;107;100;148]);
(150,[36;37;54;77;35;34;142;135;128;121;114;107;100;93;151;152;153;154]);
(151,[36;37;54;77;35;34;150;142;135;128;121;114;107;100;93]);
(152,[36;37;54;77;35;34;150;142;135;128;121;114;107;100;93]);
(153,[36;37;54;35;34;150;142;135;128;121;114;107;100;93;77;154]);
(154,[36;37;54;153;35;34;150;142;135;128;121;114;107;100;93;77]);
(155,[36;37;54;156;3;2]);
(156,[36;37;155;54])
])%Z.


Time Compute (run G16).

Definition graph40 :=
(21,[
(32,[6;7;8;0;1;2]);
(33,[6;7;8;0;1]);
(34,[7;8;0;6;35;36;37;38;39;41;40;42;43;44;45;46;47;48;49;50;51;52;53;54;55;56;57;58;59;60;61;62;63;64;65;66;67;68;69;70;71;72;73;74;75;76;77;78;79;80;81;82;83;84;85;86;87;88;89;90;91;92;93;94;95;96;97;98;99;100;101;102;103;104;105;106;107;108;109;110;111;112;113;114;115;116;117;118;119;120;121;122;123;124;125;126;127;128;129;130;131;132;133;134;135;136;137;138;139;140;141;142;143;144;145;146;147;148;149;150;151;152;153;154;155;156;157;158;159;160;161;162;163;164;165;166;167;168;169;170;171;172;173;174;175;176;177;178;179;180;181;182;183;184;185;186;187;188;189;190;191;192;193;194;195;196;197;198;199;200;201;202;203;204;205;206;207;208;209;210;211;212;213;214;215;216;217;218;219;220;221;222;223;224;225;226;227;228;229;230;231;232;233;234;235;236;237;238;239;240;241;242;243;244;245;246;247;248;249;250;251;252;253;254;255;256;257;258;259;260;261;262;263;264;265;266;267;268;269;270;271;272;273;274;275;276;277;278;279;280;281;282;283;284;285;286;287;288;289;290;291;292;293;294;295;296;297;298;299;300;301;302;303;304;305;306;307;308;309;310;311;312;313;314;315;316;317;318;319;320;321;322;323;324;325;326;327;328;329;330;331;332;333;334;335;336;337;338;339;340;341;342;343;344;345;346;347;348;349;350;351;352;353;354;355;356;357;358;359;360;361;362;363;364;365;366;367;368;369;370;371;372;373;374;375;376;377;378;379;380;381;382;383;384;385;386;387;388;389;390;391;392;393;394;395;396;397;398;399;400;401;402;403;404;405;406;407;408;409;410;411;412;413;414;415;416;417;418;419;420;421;422;423;424;425;426;427;428;429;430;431;432;433;434;435;436;437;438;439;440;441;442;443;444;445;446;447;448;449;450;451;452;453;454;455;456;457;458;459;460;461;462;463;464;465;466;467;468;469;470;471;472;473;474;475;476;477;478;479;480;481;482;483;484;485;486;487;488;489;490;491;492;493;494;495;496;497;498;499;500;501;502;503;504;505;506;507;508;509;510;511;512;513;514;515;516;517;518;519;520;521;522;523;524;525;526;527;528;529;530;531;532;533;534;535;536;537;538;539;540;541;542;543;544;545;546;547;548;549;550;551;552;553;554;555;556;557;558;559;560;561;562;563;564;565;566;567;568;569;570;571;573;572;574;575;577;576;578;579]);
(35,[34;8;0;7;36;37;38;39;41;40;42;43;44;45;46;47;48;49;50;51;52;53;54;55;56;57;58;59;60;61;62;63;64;65;66;67;68;69;70;71;72;73;74;75;76;77;78;79;80;81;82;83;84;85;86;87;88;89;90;91;92;93;94;95;96;97;98;99;100;101;102;103;104;105;106;107;108;109;110;111;112;113;114;115;116;117;118;119;120;121;122;123;124;125;126;127;128;129;130;131;132;133;134;135;136;137;138;139;140;141;142;143;144;145;146;147;148;149;150;151;152;153;154;155;156;157;158;159;160;161;162;163;164;165;166;167;168;169;170;171;172;173;174;175;176;177;178;179;180;181;182;183;184;185;186;187;188;189;190;191;192;193;194;195;196;197;198;199;200;201;202;203;204;205;206;207;208;209;210;211;212;213;214;215;216;217;218;219;220;221;222;223;224;225;226;227;228;229;230;231;232;233;234;235;236;237;238;239;240;241;242;243;244;245;246;247;248;249;250;251;252;253;254;255;256;257;258;259;260;261;262;263;264;265;266;267;268;269;270;271;272;273;274;275;276;277;278;279;280;281;282;283;284;285;286;287;288;289;290;291;292;293;294;295;296;297;298;299;300;301;302;303;304;305;306;307;308;309;310;311;312;313;314;315;316;317;318;319;320;321;322;323;324;325;326;327;328;329;330;331;332;333;334;335;336;337;338;339;340;341;342;343;344;345;346;347;348;349;350;351;352;353;354;355;356;357;358;359;360;361;362;363;364;365;366;367;368;369;370;371;372;373;374;375;376;377;378;379;380;381;382;383;384;385;386;387;388;389;390;391;392;393;394;395;396;397;398;399;400;401;402;403;404;405;406;407;408;409;410;411;412;413;414;415;416;417;418;419;420;421;422;423;424;425;426;427;428;429;430;431;432;433;434;435;436;437;438;439;440;441;442;443;444;445;446;447;448;449;450;451;452;453;454;455;456;457;458;459;460;461;462;463;464;465;466;467;468;469;470;471;472;473;474;475;476;477;478;479;480;481;482;483;484;485;486;487;488;489;490;491;492;493;494;495;496;497;498;499;500;501;502;503;504;505;506;507;508;509;510;511;512;513;514;515;516;517;518;519;520;521;522;523;524;525;526;527;528;529;530;531;532;533;534;535;536;537;538;539;540;541;542;543;544;545;546;547;548;549;550;551;552;553;554;555;556;557;558;559;560;561;562;563;564;565;566;567;568;569;570;571;573;572;574;575;577;576;578;579;1]);
(36,[34;35;0;8;37;38;39;41;40;42;43;44;45;46;47;48;49;50;51;52;53;54;55;56;57;58;59;60;61;62;63;64;65;66;67;68;69;70;71;72;73;74;75;76;77;78;79;80;81;82;83;84;85;86;87;88;89;90;91;92;93;94;95;96;97;98;99;100;101;102;103;104;105;106;107;108;109;110;111;112;113;114;115;116;117;118;119;120;121;122;123;124;125;126;127;128;129;130;131;132;133;134;135;136;137;138;139;140;141;142;143;144;145;146;147;148;149;150;151;152;153;154;155;156;157;158;159;160;161;162;163;164;165;166;167;168;169;170;171;172;173;174;175;176;177;178;179;180;181;182;183;184;185;186;187;188;189;190;191;192;193;194;195;196;197;198;199;200;201;202;203;204;205;206;207;208;209;210;211;212;213;214;215;216;217;218;219;220;221;222;223;224;225;226;227;228;229;230;231;232;233;234;235;236;237;238;239;240;241;242;243;244;245;246;247;248;249;250;251;252;253;254;255;256;257;258;259;260;261;262;263;264;265;266;267;268;269;270;271;272;273;274;275;276;277;278;279;280;281;282;283;284;285;286;287;288;289;290;291;292;293;294;295;296;297;298;299;300;301;302;303;304;305;306;307;308;309;310;311;312;313;314;315;316;317;318;319;320;321;322;323;324;325;326;327;328;329;330;331;332;333;334;335;336;337;338;339;340;341;342;343;344;345;346;347;348;349;350;351;352;353;354;355;356;357;358;359;360;361;362;363;364;365;366;367;368;369;370;371;372;373;374;375;376;377;378;379;380;381;382;383;384;385;386;387;388;389;390;391;392;393;394;395;396;397;398;399;400;401;402;403;404;405;406;407;408;409;410;411;412;413;414;415;416;417;418;419;420;421;422;423;424;425;426;427;428;429;430;431;432;433;434;435;436;437;438;439;440;441;442;443;444;445;446;447;448;449;450;451;452;453;454;455;456;457;458;459;460;461;462;463;464;465;466;467;468;469;470;471;472;473;474;475;476;477;478;479;480;481;482;483;484;485;486;487;488;489;490;491;492;493;494;495;496;497;498;499;500;501;502;503;504;505;506;507;508;509;510;511;512;513;514;515;516;517;518;519;520;521;522;523;524;525;526;527;528;529;530;531;532;533;534;535;536;537;538;539;540;541;542;543;544;545;546;547;548;549;550;551;552;553;554;555;556;557;558;559;560;561;562;563;564;565;566;567;568;569;570;571;573;572;574;575;577;576;578;579;1;6]);
(37,[34;35;36;0;38;39;41;40;42;43;44;45;46;47;48;49;50;51;52;53;54;55;56;57;58;59;60;61;62;63;64;65;66;67;68;69;70;71;72;73;74;75;76;77;78;79;80;81;82;83;84;85;86;87;88;89;90;91;92;93;94;95;96;97;98;99;100;101;102;103;104;105;106;107;108;109;110;111;112;113;114;115;116;117;118;119;120;121;122;123;124;125;126;127;128;129;130;131;132;133;134;135;136;137;138;139;140;141;142;143;144;145;146;147;148;149;150;151;152;153;154;155;156;157;158;159;160;161;162;163;164;165;166;167;168;169;170;171;172;173;174;175;176;177;178;179;180;181;182;183;184;185;186;187;188;189;190;191;192;193;194;195;196;197;198;199;200;201;202;203;204;205;206;207;208;209;210;211;212;213;214;215;216;217;218;219;220;221;222;223;224;225;226;227;228;229;230;231;232;233;234;235;236;237;238;239;240;241;242;243;244;245;246;247;248;249;250;251;252;253;254;255;256;257;258;259;260;261;262;263;264;265;266;267;268;269;270;271;272;273;274;275;276;277;278;279;280;281;282;283;284;285;286;287;288;289;290;291;292;293;294;295;296;297;298;299;300;301;302;303;304;305;306;307;308;309;310;311;312;313;314;315;316;317;318;319;320;321;322;323;324;325;326;327;328;329;330;331;332;333;334;335;336;337;338;339;340;341;342;343;344;345;346;347;348;349;350;351;352;353;354;355;356;357;358;359;360;361;362;363;364;365;366;367;368;369;370;371;372;373;374;375;376;377;378;379;380;381;382;383;384;385;386;387;388;389;390;391;392;393;394;395;396;397;398;399;400;401;402;403;404;405;406;407;408;409;410;411;412;413;414;415;416;417;418;419;420;421;422;423;424;425;426;427;428;429;430;431;432;433;434;435;436;437;438;439;440;441;442;443;444;445;446;447;448;449;450;451;452;453;454;455;456;457;458;459;460;461;462;463;464;465;466;467;468;469;470;471;472;473;474;475;476;477;478;479;480;481;482;483;484;485;486;487;488;489;490;491;492;493;494;495;496;497;498;499;500;501;502;503;504;505;506;507;508;509;510;511;512;513;514;515;516;517;518;519;520;521;522;523;524;525;526;527;528;529;530;531;532;533;534;535;536;537;538;539;540;541;542;543;544;545;546;547;548;549;550;551;552;553;554;555;556;557;558;559;560;561;562;563;564;565;566;567;568;569;570;571;573;572;574;575;577;576;578;579;1;6;7]);
(38,[34;35;36;37]);
(39,[34;35;36;37;41;40;42;43;44;45;46;47;48;49;50;51;52;53;54;55;56;57;58;59;60;61;62;63;64;65;66;67;68;69;70;71;72;73;74;75;76;77;78;79;80;81;82;83;84;85;86;87;88;89;90;91;92;93;94;95;96;97;98;99;100;101;102;103;104;105;106;107;108;109;110;111;112;113;114;115;116;117;118;119;120;121;122;123;124;125;126;127;128;129;130;131;132;133;134;135;136;137;138;139;140;141;142;143;144;145;146;147;148;149;150;151;152;153;154;155;156;157;158;159;160;161;162;163;164;165;166;167;168;169;170;171;172;173;174;175;176;177;178;179;180;181;182;183;184;185;186;187;188;189;190;191;192;193;194;195;196;197;198;199;200;201;202;203;204;205;206;207;208;209;210;211;212;213;214;215;216;217;218;219;220;221;222;223;224;225;226;227;228;229;230;231;232;233;234;235;236;237;238;239;240;241;242;243;244;245;246;247;248;249;250;251;252;253;254;255;256;257;258;259;260;261;262;263;264;265;266;267;268;269;270;271;272;273;274;275;276;277;278;279;280;281;282;283;284;285;286;287;288;289;290;291;292;293;294;295;296;297;298;299;300;301;302;303;304;305;306;307;308;309;310;311;312;313;314;315;316;317;318;319;320;321;322;323;324;325;326;327;328;329;330;331;332;333;334;335;336;337;338;339;340;341;342;343;344;345;346;347;348;349;350;351;352;353;354;355;356;357;358;359;360;361;362;363;364;365;366;367;368;369;370;371;372;373;374;375;376;377;378;379;380;381;382;383;384;385;386;387;388;389;390;391;392;393;394;395;396;397;398;399;400;401;402;403;404;405;406;407;408;409;410;411;412;413;414;415;416;417;418;419;420;421;422;423;424;425;426;427;428;429;430;431;432;433;434;435;436;437;438;439;440;441;442;443;444;445;446;447;448;449;450;451;452;453;454;455;456;457;458;459;460;461;462;463;464;465;466;467;468;469;470;471;472;473;474;475;476;477;478;479;480;481;482;483;484;485;486;487;488;489;490;491;492;493;494;495;496;497;498;499;500;501;502;503;504;505;506;507;508;509;510;511;512;513;514;515;516;517;518;519;520;521;522;523;524;525;526;527;528;529;530;531;532;533;534;535;536;537;538;539;540;541;542;543;544;545;546;547;548;549;550;551;552;553;554;555;556;557;558;559;560;561;562;563;564;565;566;567;568;569;570;571;573;572;574;575]);
(40,[34;35;36;37;39;42;43;44;45;46;47;48;49;50;51;52;53;54;55;56;57;58;59;60;61;62;63;64;65;66;67;68;69;70;71;72;73;74;75;76;77;78;79;80;81;82;83;84;85;86;87;88;89;90;91;92;93;94;95;96;97;98;99;100;101;102;103;104;105;106;107;108;109;110;111;112;113;114;115;116;117;118;119;120;121;122;123;124;125;126;127;128;129;130;131;132;133;134;135;136;137;138;139;140;141;142;143;144;145;146;147;148;149;150;151;152;153;154;155;156;157;158;159;160;161;162;163;164;165;166;167;168;169;170;171;172;173;174;175;176;177;178;179;180;181;182;183;184;185;186;187;188;189;190;191;192;193;194;195;196;197;198;199;200;201;202;203;204;205;206;207;208;209;210;211;212;213;214;215;216;217;218;219;220;221;222;223;224;225;226;227;228;229;230;231;232;233;234;235;236;237;238;239;240;241;242;243;244;245;246;247;248;249;250;251;252;253;254;255;256;257;258;259;260;261;262;263;264;265;266;267;268;269;270;271;272;273;274;275;276;277;278;279;280;281;282;283;284;285;286;287;288;289;290;291;292;293;294;295;296;297;298;299;300;301;302;303;304;305;306;307;308;309;310;311;312;313;314;315;316;317;318;319;320;321;322;323;324;325;326;327;328;329;330;331;332;333;334;335;336;337;338;339;340;341;342;343;344;345;346;347;348;349;350;351;352;353;354;355;356;357;358;359;360;361;362;363;364;365;366;367;368;369;370;371;372;373;374;375;376;377;378;379;380;381;382;383;384;385;386;387;388;389;390;391;392;393;394;395;396;397;398;399;400;401;402;403;404;405;406;407;408;409;410;411;412;413;414;415;416;417;418;419;420;421;422;423;424;425;426;427;428;429;430;431;432;433;434;435;436;437;438;439;440;441;442;443;444;445;446;447;448;449;450;451;452;453;454;455;456;457;458;459;460;461;462;463;464;465;466;467;468;469;470;471;472;473;474;475;476]);
(41,[34;35;36;37;39]);
(42,[34;35;36;37;39;40]);
(43,[34;35;36;37;39;40]);
(44,[34;35;36;37;39;40;45;46;47;48;49;50;51;52;53;54;55;56;57;58;59;60;61;62;63;64;65;66;67;68;69;70;71;72;73;74;75;76;77;78;79;80;81;82;83;84;85;86;87;88;89;90;91;92;93;94;95;96;97;98;99;100;101;102;103;104;105;106;107;108;109;110;111;112;113;114;115;116;117]);
(45,[34;35;36;37;39;40;44]);
(46,[34;35;36;37;39;40;44]);
(47,[34;35;36;37;39;40;44;48;49;50;51;52;53;54;55;56;57;58;59;60;61;62;63;64;65;66;67;68;69;70;71;72;73;74;75;76;77;78;79;80;81;82;83;84;85;86;87;88;89;90;91;92;93;94;95;96;97;98;99;100;101;102;103;104;105;106;107;108;109;110;111;112;113;114;115;116;117]);
(48,[34;35;36;37;39;40;47;44]);
(49,[34;35;36;37;39;40;47;44]);
(50,[34;35;36;37;39;40;47;44;51;52;53;54;55;56;57;58;59;60;61;62;63;64;65;66;67;68;69;70;71;72;73;74;75;76;77;78;79;80;81;82;83;84;85;86;87;88;89;90;91;92;93;94;95;96;97;98;99;100;101;102;103;104;105;106;107;108;109;110;111;112;113;114;115;116;117]);
(51,[34;35;36;37;39;40;47;50;44]);
(52,[34;35;36;37;39;40;47;50;44]);
(53,[34;35;36;37;39;40;47;50;44;54;55;56;57;58;59;60;61;62;63;64;65;66;67;68;69;70;71;72;73;74;75;76;77;78;79;80;81;82;83;84;85;86;87;88;89;90;91;92;93;94;95;96;97;98;99;100;101;102;103;104;105;106;107;108;109;110;111;112;113;114;115;116;117]);
(54,[34;35;36;37;39;40;47;50;53;44]);
(55,[34;35;36;37;39;40;47;50;53;44]);
(56,[34;35;36;37;39;40;47;53;44;50;57;58;59;60;61;62;63;64;65;66;67;68;69;70;71;72;73;74;75;76;77;78;79;80;81;82;83;84;85;86;87;88;89;90;91;92;93;94;95;96;97;98;99;100;101;102;103;104;105;106;107;108;109;110;111;112;113;114;115;116;117]);
(57,[34;35;36;37;39;40;47;56;53;44;50]);
(58,[34;35;36;37;39;40;47;56;53;44;50]);
(59,[34;35;36;37;39;40;47;56;53;50;44;60;61;62;63;64;65;66;67;68;69;70;71;72;73;74;75;76;77;78;79;80;81;82;83;84;85;86;87;88;89;90;91;92;93;94;95;96;97;98;99;100;101;102;103;104;105;106;107;108;109;110;111;112;113;114;115;116;117]);
(60,[34;35;36;37;39;40;47;56;53;59;50;44]);
(61,[34;35;36;37;39;40;47;56;53;59;50;44]);
(62,[34;35;36;37;39;40;56;53;59;50;44;47;63;64;65;66;67;68;69;70;71;72;73;74;75;76;77;78;79;80;81;82;83;84;85;86;87;88;89;90;91;92;93;94;95;96;97;98;99;100;101;102;103;104;105;106;107;108;109;110;111;112;113;114;115;116;117]);
(63,[34;35;36;37;39;40;62;56;53;59;50;44;47]);
(64,[34;35;36;37;39;40;62;56;53;59;50;44;47]);
(65,[34;35;36;37;39;40;62;53;59;50;44;47;56;66;67;68;69;70;71;72;73;74;75;76;77;78;79;80;81;82;83;84;85;86;87;88;89;90;91;92;93;94;95;96;97;98;99;100;101;102;103;104;105;106;107;108;109;110;111;112;113;114;115;116;117]);
(66,[34;35;36;37;39;40;62;65;53;59;50;44;47;56]);
(67,[34;35;36;37;39;40;62;65;53;59;50;44;47;56]);
(68,[34;35;36;37;39;40;62;65;59;50;44;47;56;53;69;70;71;72;73;74;75;76;77;78;79;80;81;82;83;84;85;86;87;88;89;90;91;92;93;94;95;96;97;98;99;100;101;102;103;104;105;106;107;108;109;110;111;112;113;114;115;116;117]);
(69,[34;35;36;37;39;40;62;65;68;59;50;44;47;56;53]);
(70,[34;35;36;37;39;40;62;65;68;59;50;44;47;56;53]);
(71,[34;35;36;37;39;40;62;65;68;59;44;47;56;53;50;72;73;74;75;76;77;78;79;80;81;82;83;84;85;86;87;88;89;90;91;92;93;94;95;96;97;98;99;100;101;102;103;104;105;106;107;108;109;110;111;112;113;114;115;116;117]);
(72,[34;35;36;37;39;40;62;65;68;59;71;44;47;56;53;50]);
(73,[34;35;36;37;39;40;62;65;68;59;71;44;47;56;53;50]);
(74,[34;35;36;37;39;40;62;65;68;59;71;47;56;53;50;44;75;76;77;78;79;80;81;82;83;84;85;86;87;88;89;90;91;92;93;94;95;96;97;98;99;100;101;102;103;104;105;106;107;108;109;110;111;112;113;114;115;116;117]);
(75,[34;35;36;37;39;40;62;65;68;59;71;74;47;56;53;50;44]);
(76,[34;35;36;37;39;40;62;65;68;59;71;74;47;56;53;50;44]);
(77,[34;35;36;37;39;40;62;65;68;59;71;74;56;53;50;44;47;78;79;80;81;82;83;84;85;86;87;88;89;90;91;92;93;94;95;96;97;98;99;100;101;102;103;104;105;106;107;108;109;110;111;112;113;114;115;116;117]);
(78,[34;35;36;37;39;40;62;65;68;59;71;74;77;56;53;50;44;47]);
(79,[34;35;36;37;39;40;62;65;68;59;71;74;77;56;53;50;44;47]);
(80,[34;35;36;37;39;40;62;65;68;59;71;74;77;56;53;50;47;44;81;82;83;84;85;86;87;88;89;90;91;92;93;94;95;96;97;98;99;100;101;102;103;104;105;106;107;108;109;110;111;112;113;114;115;116;117]);
(81,[34;35;36;37;39;40;62;65;68;59;71;74;77;56;53;50;80;47;44]);
(82,[34;35;36;37;39;40;62;65;68;59;71;74;77;56;53;50;80;47;44]);
(83,[34;35;36;37;39;40;62;65;68;59;71;74;77;56;53;50;80;44;47;84;85;86;87;88;89;90;91;92;93;94;95;96;97;98;99;100;101;102;103;104;105;106;107;108;109;110;111;112;113;114;115;116;117]);
(84,[34;35;36;37;39;40;62;65;68;59;71;74;77;56;53;50;80;83;44;47]);
(85,[34;35;36;37;39;40;62;65;68;59;71;74;77;56;53;50;80;83;44;47]);
(86,[34;35;36;37;39;40;62;65;68;59;71;74;77;56;53;50;80;83;47;44;87;88;89;90;91;92;93;94;95;96;97;98;99;100;101;102;103;104;105;106;107;108;109;110;111;112;113;114;115;116;117]);
(87,[34;35;36;37;39;40;62;65;68;59;71;74;77;56;53;50;80;83;86;47;44]);
(88,[34;35;36;37;39;40;62;65;68;59;71;74;77;56;53;50;80;83;86;47;44]);
(89,[34;35;36;37;39;40;62;65;68;59;71;74;77;56;53;50;80;83;86;47;44;90;91;92;93;94;95;96;97;98;99;100;101;102;103;104;105;106;107;108;109;110;111;112;113;114;115;116;117]);
(90,[34;35;36;37;39;40;62;65;68;59;71;74;77;56;53;50;80;83;86;47;89;44]);
(91,[34;35;36;37;39;40;62;65;68;59;71;74;77;56;53;50;80;83;86;47;89;44]);
(92,[34;35;36;37;39;40;62;65;68;59;71;74;77;56;53;50;80;83;47;89;44;86;93;94;95;96;97;98;99;100;101;102;103;104;105;106;107;108;109;110;111;112;113;114;115;116;117]);
(93,[34;35;36;37;39;40;62;65;68;59;71;74;77;56;53;50;80;83;92;47;89;44;86]);
(94,[34;35;36;37;39;40;62;65;68;59;71;74;77;56;53;50;80;83;92;47;89;44;86]);
(95,[34;35;36;37;39;40;62;65;68;59;71;74;77;56;53;50;80;92;47;89;44;86;83;96;97;98;99;100;101;102;103;104;105;106;107;108;109;110;111;112;113;114;115;116;117]);
(96,[34;35;36;37;39;40;62;65;68;59;71;74;77;56;53;50;80;95;92;47;89;44;86;83]);
(97,[34;35;36;37;39;40;62;65;68;59;71;74;77;56;53;50;80;95;92;47;89;44;86;83]);
(98,[34;35;36;37;39;40;62;65;68;59;71;74;77;56;53;50;95;92;47;89;44;86;83;80;99;100;101;102;103;104;105;106;107;108;109;110;111;112;113;114;115;116;117]);
(99,[34;35;36;37;39;40;62;65;68;59;71;74;77;56;53;50;98;95;92;47;89;44;86;83;80]);
(100,[34;35;36;37;39;40;62;65;68;59;71;74;77;56;53;50;98;95;92;47;89;44;86;83;80]);
(101,[34;35;36;37;39;40;62;65;68;59;71;74;56;53;50;98;95;92;47;89;44;86;83;80;77;102;103;104;105;106;107;108;109;110;111;112;113;114;115;116;117]);
(102,[34;35;36;37;39;40;62;65;68;59;71;74;101;56;53;50;98;95;92;47;89;44;86;83;80;77]);
(103,[34;35;36;37;39;40;62;65;68;59;71;74;101;56;53;50;98;95;92;47;89;44;86;83;80;77]);
(104,[34;35;36;37;39;40;62;65;68;59;71;101;56;53;50;98;95;92;47;89;44;86;83;80;77;74;105;106;107;108;109;110;111;112;113;114;115;116;117]);
(105,[34;35;36;37;39;40;62;65;68;59;71;104;101;56;53;50;98;95;92;47;89;44;86;83;80;77;74]);
(106,[34;35;36;37;39;40;62;65;68;59;71;104;101;56;53;50;98;95;92;47;89;44;86;83;80;77;74]);
(107,[34;35;36;37;39;40;62;65;68;59;104;101;56;53;50;98;95;92;47;89;44;86;83;80;77;74;71;108;109;110;111;112;113;114;115;116;117]);
(108,[34;35;36;37;39;40;62;65;68;59;107;104;101;56;53;50;98;95;92;47;89;44;86;83;80;77;74;71]);
(109,[34;35;36;37;39;40;62;65;68;59;107;104;101;56;53;50;98;95;92;47;89;44;86;83;80;77;74;71]);
(110,[34;35;36;37;39;40;62;65;59;107;104;101;56;53;50;98;95;92;47;89;44;86;83;80;77;74;71;68;111;112;113;114;115;116;117]);
(111,[34;35;36;37;39;40;62;65;110;59;107;104;101;56;53;50;98;95;92;47;89;44;86;83;80;77;74;71;68]);
(112,[34;35;36;37;39;40;62;65;110;59;107;104;101;56;53;50;98;95;92;47;89;44;86;83;80;77;74;71;68]);
(113,[34;35;36;37;39;40;62;110;59;107;104;101;56;53;50;98;95;92;47;89;44;86;83;80;77;74;71;68;65;114;115;116;117]);
(114,[34;35;36;37;39;40;62;113;110;59;107;104;101;56;53;50;98;95;92;47;89;44;86;83;80;77;74;71;68;65]);
(115,[34;35;36;37;39;40;62;113;110;59;107;104;101;56;53;50;98;95;92;47;89;44;86;83;80;77;74;71;68;65]);
(116,[34;35;36;37;39;40;113;110;59;107;104;101;56;53;50;98;95;92;47;89;44;86;83;80;77;74;71;68;65;62;117]);
(117,[34;35;36;37;39;40;116;113;110;59;107;104;101;56;53;50;98;95;92;47;89;44;86;83;80;77;74;71;68;65;62]);
(118,[34;35;36;37;39;40;119;120;121;122;123;124;125;126;127;128;129;130;131;132;133;134;135;136;137;138;139;140;141;142;143;144;145;146;147;148;149;150;151;152;153;154;155;156;157;158;159;160;161;162;163;164;165;166;167;168;169;170;171;172;173;174;175;176;177;178;179;180;181;182;183;184;185;186;187;188;189;190;191;192;193;194;195;196;197;198;199;200;201;202;203;204;205;206;207;208;209;210;211;212;213;214;215;216;217;218;219;220;221;222;223;224;225;226;227;228;229;230;231;232;233;234;235;236;237;238;239;240;241;242;243;244;245;246;247;248;249;250;251;252;253;254;255;256;257;258;259;260;261;262;263;264;265;266;267;268;269;270;271;272;273;274;275;276;277;278;279;280;281;282;283;284;285;286;287;288;289;290;291;292;293;294;295;296;297;298;299;300;301;302;303;304;305;306;307;308;309;310;311;312;313;314;315;316;317;318;319;320;321;322;323;324;325;326;327;328;329;330;331;332;333;334;335;336;337;338;339;340;341;342;343;344;345;346;347;348;349;350;351;352;353;354;355;356;357;358;359;360;361;362;363;364;365;366;367;368;369;370;371;372;373;374;375;376;377;378;379;380;381;382;383;384;385;386;387;388;389;390;391;392;393;394;395;396;397;398;399;400;401;402;403;404;405;406;407;408;409;410;411;412;413;414;415;416;417;418;419;420;421;422;423;424;425;426;427;428;429;430;431;432;433;434;435;436;437;438;439;440;441;442;443;444;445;446;447;448;449;450;451;452;453;454;455;456;457;458;459;460;461;462;463;464;465;466;467;468;469;470;471;472;473;474;475;476;477;478;479;480;481;482;483;484;485;486;487;488;489;490;491;492;493;494;495;496;497;498;499;500;501;502;503;504;505;506;507;508;509;510;511;512;513;514;515;516;517;518;519;520;521;522;523;524;525;526;527;528;529;530;531;532;533;534;535;536;537;538;539;540;541;542;543;544;545;546;547;548;549;550;551;552;553;554;555;556;557;558;559;560;561;562;563;564;565;566;567;568;569;570;571]);
(119,[34;35;36;37;39;40;118]);
(120,[34;35;36;37;39;40;118]);
(121,[34;35;36;37;39;40;118;122;123;124;125;126;127;128;129;130;131;132;133;134;135;136;137;138;139;140;141;142;143;144;145;146;147;148;149;150;151;152;153;154;155]);
(122,[34;35;36;37;39;40;118;121]);
(123,[34;35;36;37;39;40;118;121]);
(124,[34;35;36;37;39;40;118;121;125;126;127;128;129;130;131;132;133;134;135;136;137;138;139;140;141;142;143;144;145;146;147;148;149;150;151;152;153;154;155]);
(125,[34;35;36;37;39;40;118;121;124]);
(126,[34;35;36;37;39;40;118;121;124]);
(127,[34;35;36;37;39;40;118;121;124;128;129;130;131;132;133;134;135;136;137;138;139;140;141;142;143;144;145;146;147;148;149;150;151;152;153;154;155]);
(128,[34;35;36;37;39;40;118;121;124;127]);
(129,[34;35;36;37;39;40;118;121;124;127]);
(130,[34;35;36;37;39;40;118;121;124;127;131;132;133;134;135;136;137;138;139;140;141;142;143;144;145;146;147;148;149;150;151;152;153;154;155]);
(131,[34;35;36;37;39;40;118;121;124;127;130]);
(132,[34;35;36;37;39;40;118;121;124;127;130]);
(133,[34;35;36;37;39;40;118;121;124;127;130;134;135;136;137;138;139;140;141;142;143;144;145;146;147;148;149;150;151;152;153;154;155]);
(134,[34;35;36;37;39;40;118;121;124;127;130;133]);
(135,[34;35;36;37;39;40;118;121;124;127;130;133]);
(136,[34;35;36;37;39;40;118;121;124;127;130;133;137;138;139;140;141;142;143;144;145;146;147;148;149;150;151;152;153;154;155]);
(137,[34;35;36;37;39;40;118;121;124;127;130;133;136]);
(138,[34;35;36;37;39;40;118;121;124;127;130;133;136]);
(139,[34;35;36;37;39;40;118;121;124;127;130;133;136;140;141;142;143;144;145;146;147;148;149;150;151;152;153;154;155]);
(140,[34;35;36;37;39;40;118;121;124;127;130;133;139;136]);
(141,[34;35;36;37;39;40;118;121;124;127;130;133;139;136]);
(142,[34;35;36;37;39;40;118;121;124;127;130;139;136;133;143;144;145;146;147;148;149;150;151;152;153;154;155]);
(143,[34;35;36;37;39;40;118;121;124;127;130;142;139;136;133]);
(144,[34;35;36;37;39;40;118;121;124;127;130;142;139;136;133]);
(145,[34;35;36;37;39;40;118;121;124;127;142;139;136;133;130;146;147;148;149;150;151;152;153;154;155]);
(146,[34;35;36;37;39;40;118;121;124;127;145;142;139;136;133;130]);
(147,[34;35;36;37;39;40;118;121;124;127;145;142;139;136;133;130]);
(148,[34;35;36;37;39;40;118;121;124;145;142;139;136;133;130;127;149;150;151;152;153;154;155]);
(149,[34;35;36;37;39;40;118;121;124;148;145;142;139;136;133;130;127]);
(150,[34;35;36;37;39;40;118;121;124;148;145;142;139;136;133;130;127]);
(151,[34;35;36;37;39;40;118;121;148;145;142;139;136;133;130;127;124;152;153;154;155]);
(152,[34;35;36;37;39;40;118;121;151;148;145;142;139;136;133;130;127;124]);
(153,[34;35;36;37;39;40;118;121;151;148;145;142;139;136;133;130;127;124]);
(154,[34;35;36;37;39;40;118;151;148;145;142;139;136;133;130;127;124;121;155]);
(155,[34;35;36;37;39;40;118;154;151;148;145;142;139;136;133;130;127;124;121]);
(156,[34;35;36;37;39;118;40;157;158;159;160;161;162;163;164;165;166;167;168;169;170;171;172;173;174;175;176;177;178;179;180;181;182;183;184;185;186;187;188;189;190;191;192;193;194;195;196;197;198;199;200;201;202;203;204;205;206;207;208;209;210;211;212;213;214;215;216;217;218;219;220;221;222;223;224;225;226;227;228;229;230;231;232;233;234;235;236;237;238;239;240;241;242;243;244;245;246;247;248;249;250;251;252;253;254;255;256;257;258;259;260;261;262;263;264;265;266;267;268;269;270;271;272;273;274;275;276;277;278;279;280;281;282;283;284;285;286;287;288;289;290;291;292;293;294;295;296;297;298;299;300;301;302;303;304;305;306;307;308;309;310;311;312;313;314;315;316;317;318;319;320;321;322;323;324;325;326;327;328;329;330;331;332;333;334;335;336;337;338;339;340;341;342;343;344;345;346;347;348;349;350;351;352;353;354;355;356;357;358;359;360;361;362;363;364;365;366;367;368;369;370;371;372;373;374;375;376;377;378;379;380;381;382;383;384;385;386;387;388;389;390;391;392;393;394;395;396;397;398;399;400;401;402;403;404;405;406;407;408;409;410;411;412;413;414;415;416;417;418;419;420;421;422;423;424;425;426;427;428;429;430;431;432;433;434;435;436;437;438;439;440;441;442;443;444;445;446;447;448;449;450;451;452;453;454;455;456;457;458;459;460;461;462;463;464;465;466;467;468;469;470;471;472;473;474;475;476;477;478;479;480;481;482;483;484;485;486;487;488;489;490;491;492;493;494;495;496;497;498;499;500;501;502;503;504;505;506;507;508;509;510;511;512;513;514;515;516;517;518;519;520;521;522;523;524;525;526;527;528;529;530;531;532;533;534;535;536;537;538;539;540;541;542;543;544;545;546;547;548;549;550;551;552;553;554;555;556;557;558;559;560;561;562;563;564;565;566;567;568;569;570;571]);
(157,[34;35;36;37;39;156;118;40]);
(158,[34;35;36;37;39;156;118;40]);
(159,[34;35;36;37;39;156;118;40;160;161;162;163;164;165;166;167;168;169;170;171;172;173;174;175;176;177;178;179;180;181;182;183;184;185;186;187;188;189;190;191;192;193;194;195;196;197;198;199;200;201;202;203;204;205;206;207;208]);
(160,[34;35;36;37;39;156;118;40;159]);
(161,[34;35;36;37;39;156;118;40;159]);
(162,[34;35;36;37;39;156;118;40;159;163;164;165;166;167;168;169;170;171;172;173;174;175;176;177;178;179;180;181;182;183;184;185;186;187;188;189;190;191;192;193;194;195;196;197;198;199;200;201;202;203;204;205;206;207;208]);
(163,[34;35;36;37;39;156;118;40;159;162]);
(164,[34;35;36;37;39;156;118;40;159;162]);
(165,[34;35;36;37;39;156;118;40;159;162;166;167;168;169;170;171;172;173;174;175;176;177;178;179;180;181;182;183;184;185;186;187;188;189;190;191;192;193;194;195;196;197;198;199;200;201;202;203;204;205;206;207;208]);
(166,[34;35;36;37;39;156;118;40;159;162;165]);
(167,[34;35;36;37;39;156;118;40;159;162;165]);
(168,[34;35;36;37;39;156;118;40;159;162;165;169;170;171;172;173;174;175;176;177;178;179;180;181;182;183;184;185;186;187;188;189;190;191;192;193;194;195;196;197;198;199;200;201;202;203;204;205;206;207;208]);
(169,[34;35;36;37;39;156;118;40;159;162;165;168]);
(170,[34;35;36;37;39;156;118;40;159;162;165;168]);
(171,[34;35;36;37;39;156;118;40;159;162;165;168;172;173;174;175;176;177;178;179;180;181;182;183;184;185;186;187;188;189;190;191;192;193;194;195;196;197;198;199;200;201;202;203;204;205;206;207;208]);
(172,[34;35;36;37;39;156;118;40;159;162;165;168;171]);
(173,[34;35;36;37;39;156;118;40;159;162;165;168;171]);
(174,[34;35;36;37;39;156;118;40;159;162;165;168;171;175;176;177;178;179;180;181;182;183;184;185;186;187;188;189;190;191;192;193;194;195;196;197;198;199;200;201;202;203;204;205;206;207;208]);
(175,[34;35;36;37;39;156;118;40;159;162;165;168;171;174]);
(176,[34;35;36;37;39;156;118;40;159;162;165;168;171;174]);
(177,[34;35;36;37;39;156;118;40;159;162;165;168;171;174;178;179;180;181;182;183;184;185;186;187;188;189;190;191;192;193;194;195;196;197;198;199;200;201;202;203;204;205;206;207;208]);
(178,[34;35;36;37;39;156;118;40;159;162;165;168;171;174;177]);
(179,[34;35;36;37;39;156;118;40;159;162;165;168;171;174;177]);
(180,[34;35;36;37;39;156;118;40;159;162;165;168;171;174;177;181;182;183;184;185;186;187;188;189;190;191;192;193;194;195;196;197;198;199;200;201;202;203;204;205;206;207;208]);
(181,[34;35;36;37;39;156;118;40;159;162;165;168;171;174;177;180]);
(182,[34;35;36;37;39;156;118;40;159;162;165;168;171;174;177;180]);
(183,[34;35;36;37;39;156;118;40;159;162;165;168;171;174;177;180;184;185;186;187;188;189;190;191;192;193;194;195;196;197;198;199;200;201;202;203;204;205;206;207;208]);
(184,[34;35;36;37;39;156;118;40;159;162;165;168;171;174;177;180;183]);
(185,[34;35;36;37;39;156;118;40;159;162;165;168;171;174;177;180;183]);
(186,[34;35;36;37;39;156;118;40;159;162;165;168;171;174;177;183;180;187;188;189;190;191;192;193;194;195;196;197;198;199;200;201;202;203;204;205;206;207;208]);
(187,[34;35;36;37;39;156;118;40;159;162;165;168;171;174;177;186;183;180]);
(188,[34;35;36;37;39;156;118;40;159;162;165;168;171;174;177;186;183;180]);
(189,[34;35;36;37;39;156;118;40;159;162;165;168;171;174;186;183;180;177;190;191;192;193;194;195;196;197;198;199;200;201;202;203;204;205;206;207;208]);
(190,[34;35;36;37;39;156;118;40;159;162;165;168;171;174;189;186;183;180;177]);
(191,[34;35;36;37;39;156;118;40;159;162;165;168;171;174;189;186;183;180;177]);
(192,[34;35;36;37;39;156;118;40;159;162;165;168;171;189;186;183;180;177;174;193;194;195;196;197;198;199;200;201;202;203;204;205;206;207;208]);
(193,[34;35;36;37;39;156;118;40;159;162;165;168;171;192;189;186;183;180;177;174]);
(194,[34;35;36;37;39;156;118;40;159;162;165;168;171;192;189;186;183;180;177;174]);
(195,[34;35;36;37;39;156;118;40;159;162;165;168;192;189;186;183;180;177;174;171;196;197;198;199;200;201;202;203;204;205;206;207;208]);
(196,[34;35;36;37;39;156;118;40;159;162;165;168;195;192;189;186;183;180;177;174;171]);
(197,[34;35;36;37;39;156;118;40;159;162;165;168;195;192;189;186;183;180;177;174;171]);
(198,[34;35;36;37;39;156;118;40;159;162;165;195;192;189;186;183;180;177;174;171;168;199;200;201;202;203;204;205;206;207;208]);
(199,[34;35;36;37;39;156;118;40;159;162;165;198;195;192;189;186;183;180;177;174;171;168]);
(200,[34;35;36;37;39;156;118;40;159;162;165;198;195;192;189;186;183;180;177;174;171;168]);
(201,[34;35;36;37;39;156;118;40;159;162;198;195;192;189;186;183;180;177;174;171;168;165;202;203;204;205;206;207;208]);
(202,[34;35;36;37;39;156;118;40;159;162;201;198;195;192;189;186;183;180;177;174;171;168;165]);
(203,[34;35;36;37;39;156;118;40;159;162;201;198;195;192;189;186;183;180;177;174;171;168;165]);
(204,[34;35;36;37;39;156;118;40;159;201;198;195;192;189;186;183;180;177;174;171;168;165;162;205;206;207;208]);
(205,[34;35;36;37;39;156;118;40;159;204;201;198;195;192;189;186;183;180;177;174;171;168;165;162]);
(206,[34;35;36;37;39;156;118;40;159;204;201;198;195;192;189;186;183;180;177;174;171;168;165;162]);
(207,[34;35;36;37;39;156;118;40;204;201;198;195;192;189;186;183;180;177;174;171;168;165;162;159;208]);
(208,[34;35;36;37;39;156;118;40;207;204;201;198;195;192;189;186;183;180;177;174;171;168;165;162;159]);
(209,[34;35;36;37;39;118;40;156;210;211;212;213;214;215;216;217;218;219;220;221;222;223;224;225;226;227;228;229;230;231;232;233;234;235;236;237;238;239;240;241;242;243;244;245;246;247;248;249;250;251;252;253;254;255;256;257;258;259;260;261;262;263;264;265;266;267;268;269;270;271;272;273;274;275;276;277;278;279;280;281;282;283;284;285;286;287;288;289;290;291;292;293;294;295;296;297;298;299;300;301;302;303;304;305;306;307;308;309;310;311;312;313;314;315;316;317;318;319;320;321;322;323;324;325;326;327;328;329;330;331;332;333;334;335;336;337;338;339;340;341;342;343;344;345;346;347;348;349;350;351;352;353;354;355;356;357;358;359;360;361;362;363;364;365;366;367;368;369;370;371;372;373;374;375;376;377;378;379;380;381;382;383;384;385;386;387;388;389;390;391;392;393;394;395;396;397;398;399;400;401;402;403;404;405;406;407;408;409;410;411;412;413;414;415;416;417;418;419;420;421;422;423;424;425;426;427;428;429;430;431;432;433;434;435;436;437;438;439;440;441;442;443;444;445;446;447;448;449;450;451;452;453;454;455;456;457;458;459;460;461;462;463;464;465;466;467;468;469;470;471;472;473;474;475;476;477;478;479;480;481;482;483;484;485;486;487;488;489;490;491;492;493;494;495;496;497;498;499;500;501;502;503;504;505;506;507;508;509;510;511;512;513;514;515;516;517;518;519;520;521;522;523;524;525;526;527;528;529;530;531;532;533;534;535;536;537;538;539;540;541;542;543;544;545;546;547;548;549;550;551;552;553;554;555;556;557;558;559;560;561;562;563;564;565;566;567;568;569;570;571]);
(210,[34;35;36;37;39;209;118;40;156]);
(211,[34;35;36;37;39;209;118;40;156]);
(212,[34;35;36;37;39;209;118;40;156;213;214;215;216;217;218;219;220;221;222;223;224;225;226;227;228;229;230;231;232;233;234;235;236;237;238;239;240;241;242;243;244;245;246;247;248;249;250;251;252;253;254;255;256;257;258;259;260;261;262;263;264;265;266;267]);
(213,[34;35;36;37;39;209;118;40;156;212]);
(214,[34;35;36;37;39;209;118;40;156;212]);
(215,[34;35;36;37;39;209;118;40;156;212;216;217;218;219;220;221;222;223;224;225;226;227;228;229;230;231;232;233;234;235;236;237;238;239;240;241;242;243;244;245;246;247;248;249;250;251;252;253;254;255;256;257;258;259;260;261;262;263;264;265;266;267]);
(216,[34;35;36;37;39;209;118;40;156;212;215]);
(217,[34;35;36;37;39;209;118;40;156;212;215]);
(218,[34;35;36;37;39;209;118;40;156;212;215;219;220;221;222;223;224;225;226;227;228;229;230;231;232;233;234;235;236;237;238;239;240;241;242;243;244;245;246;247;248;249;250;251;252;253;254;255;256;257;258;259;260;261;262;263;264;265;266;267]);
(219,[34;35;36;37;39;209;118;40;156;212;215;218]);
(220,[34;35;36;37;39;209;118;40;156;212;215;218]);
(221,[34;35;36;37;39;209;118;40;156;212;215;218;222;223;224;225;226;227;228;229;230;231;232;233;234;235;236;237;238;239;240;241;242;243;244;245;246;247;248;249;250;251;252;253;254;255;256;257;258;259;260;261;262;263;264;265;266;267]);
(222,[34;35;36;37;39;209;118;40;156;212;215;218;221]);
(223,[34;35;36;37;39;209;118;40;156;212;215;218;221]);
(224,[34;35;36;37;39;209;118;40;156;212;215;218;221;225;226;227;228;229;230;231;232;233;234;235;236;237;238;239;240;241;242;243;244;245;246;247;248;249;250;251;252;253;254;255;256;257;258;259;260;261;262;263;264;265;266;267]);
(225,[34;35;36;37;39;209;118;40;156;212;215;218;221;224]);
(226,[34;35;36;37;39;209;118;40;156;212;215;218;221;224]);
(227,[34;35;36;37;39;209;118;40;156;212;215;218;221;224;228;229;230;231;232;233;234;235;236;237;238;239;240;241;242;243;244;245;246;247;248;249;250;251;252;253;254;255;256;257;258;259;260;261;262;263;264;265;266;267]);
(228,[34;35;36;37;39;209;118;40;156;212;215;218;221;224;227]);
(229,[34;35;36;37;39;209;118;40;156;212;215;218;221;224;227]);
(230,[34;35;36;37;39;209;118;40;156;212;215;218;221;224;227;231;232;233;234;235;236;237;238;239;240;241;242;243;244;245;246;247;248;249;250;251;252;253;254;255;256;257;258;259;260;261;262;263;264;265;266;267]);
(231,[34;35;36;37;39;209;118;40;156;212;215;218;221;224;227;230]);
(232,[34;35;36;37;39;209;118;40;156;212;215;218;221;224;227;230]);
(233,[34;35;36;37;39;209;118;40;156;212;215;218;221;224;227;230;234;235;236;237;238;239;240;241;242;243;244;245;246;247;248;249;250;251;252;253;254;255;256;257;258;259;260;261;262;263;264;265;266;267]);
(234,[34;35;36;37;39;209;118;40;156;212;215;218;221;224;227;230;233]);
(235,[34;35;36;37;39;209;118;40;156;212;215;218;221;224;227;230;233]);
(236,[34;35;36;37;39;209;118;40;156;212;215;218;221;224;227;230;233;237;238;239;240;241;242;243;244;245;246;247;248;249;250;251;252;253;254;255;256;257;258;259;260;261;262;263;264;265;266;267]);
(237,[34;35;36;37;39;209;118;40;156;212;215;218;221;224;227;230;233;236]);
(238,[34;35;36;37;39;209;118;40;156;212;215;218;221;224;227;230;233;236]);
(239,[34;35;36;37;39;209;118;40;156;212;215;218;221;224;227;230;233;236;240;241;242;243;244;245;246;247;248;249;250;251;252;253;254;255;256;257;258;259;260;261;262;263;264;265;266;267]);
(240,[34;35;36;37;39;209;118;40;156;212;215;218;221;224;227;230;233;236;239]);
(241,[34;35;36;37;39;209;118;40;156;212;215;218;221;224;227;230;233;236;239]);
(242,[34;35;36;37;39;209;118;40;156;212;215;218;221;224;227;230;233;239;236;243;244;245;246;247;248;249;250;251;252;253;254;255;256;257;258;259;260;261;262;263;264;265;266;267]);
(243,[34;35;36;37;39;209;118;40;156;212;215;218;221;224;227;230;233;242;239;236]);
(244,[34;35;36;37;39;209;118;40;156;212;215;218;221;224;227;230;233;242;239;236]);
(245,[34;35;36;37;39;209;118;40;156;212;215;218;221;224;227;230;242;239;236;233;246;247;248;249;250;251;252;253;254;255;256;257;258;259;260;261;262;263;264;265;266;267]);
(246,[34;35;36;37;39;209;118;40;156;212;215;218;221;224;227;230;245;242;239;236;233]);
(247,[34;35;36;37;39;209;118;40;156;212;215;218;221;224;227;230;245;242;239;236;233]);
(248,[34;35;36;37;39;209;118;40;156;212;215;218;221;224;227;245;242;239;236;233;230;249;250;251;252;253;254;255;256;257;258;259;260;261;262;263;264;265;266;267]);
(249,[34;35;36;37;39;209;118;40;156;212;215;218;221;224;227;248;245;242;239;236;233;230]);
(250,[34;35;36;37;39;209;118;40;156;212;215;218;221;224;227;248;245;242;239;236;233;230]);
(251,[34;35;36;37;39;209;118;40;156;212;215;218;221;224;248;245;242;239;236;233;230;227;252;253;254;255;256;257;258;259;260;261;262;263;264;265;266;267]);
(252,[34;35;36;37;39;209;118;40;156;212;215;218;221;224;251;248;245;242;239;236;233;230;227]);
(253,[34;35;36;37;39;209;118;40;156;212;215;218;221;224;251;248;245;242;239;236;233;230;227]);
(254,[34;35;36;37;39;209;118;40;156;212;215;218;221;251;248;245;242;239;236;233;230;227;224;255;256;257;258;259;260;261;262;263;264;265;266;267]);
(255,[34;35;36;37;39;209;118;40;156;212;215;218;221;254;251;248;245;242;239;236;233;230;227;224]);
(256,[34;35;36;37;39;209;118;40;156;212;215;218;221;254;251;248;245;242;239;236;233;230;227;224]);
(257,[34;35;36;37;39;209;118;40;156;212;215;218;254;251;248;245;242;239;236;233;230;227;224;221;258;259;260;261;262;263;264;265;266;267]);
(258,[34;35;36;37;39;209;118;40;156;212;215;218;257;254;251;248;245;242;239;236;233;230;227;224;221]);
(259,[34;35;36;37;39;209;118;40;156;212;215;218;257;254;251;248;245;242;239;236;233;230;227;224;221]);
(260,[34;35;36;37;39;209;118;40;156;212;215;257;254;251;248;245;242;239;236;233;230;227;224;221;218;261;262;263;264;265;266;267]);
(261,[34;35;36;37;39;209;118;40;156;212;215;260;257;254;251;248;245;242;239;236;233;230;227;224;221;218]);
(262,[34;35;36;37;39;209;118;40;156;212;215;260;257;254;251;248;245;242;239;236;233;230;227;224;221;218]);
(263,[34;35;36;37;39;209;118;40;156;212;260;257;254;251;248;245;242;239;236;233;230;227;224;221;218;215;264;265;266;267]);
(264,[34;35;36;37;39;209;118;40;156;212;263;260;257;254;251;248;245;242;239;236;233;230;227;224;221;218;215]);
(265,[34;35;36;37;39;209;118;40;156;212;263;260;257;254;251;248;245;242;239;236;233;230;227;224;221;218;215]);
(266,[34;35;36;37;39;209;118;40;156;263;260;257;254;251;248;245;242;239;236;233;230;227;224;221;218;215;212;267]);
(267,[34;35;36;37;39;209;118;40;156;266;263;260;257;254;251;248;245;242;239;236;233;230;227;224;221;218;215;212]);
(268,[34;35;36;37;39;118;40;156;209;269;270;271;272;273;274;275;276;277;278;279;280;281;282;283;284;285;286;287;288;289;290;291;292;293;294;295;296;297;298;299;300;301;302;303;304;305;306;307;308;309;310;311;312;313;314;315;316;317;318;319;320;321;322;323;324;325;326;327;328;329;330;331;332;333;334;335;336;337;338;339;340;341;342;343;344;345;346;347;348;349;350;351;352;353;354;355;356;357;358;359;360;361;362;363;364;365;366;367;368;369;370;371;372;373;374;375;376;377;378;379;380;381;382;383;384;385;386;387;388;389;390;391;392;393;394;395;396;397;398;399;400;401;402;403;404;405;406;407;408;409;410;411;412;413;414;415;416;417;418;419;420;421;422;423;424;425;426;427;428;429;430;431;432;433;434;435;436;437;438;439;440;441;442;443;444;445;446;447;448;449;450;451;452;453;454;455;456;457;458;459;460;461;462;463;464;465;466;467;468;469;470;471;472;473;474;475;476;477;478;479;480;481;482;483;484;485;486;487;488;489;490;491;492;493;494;495;496;497;498;499;500;501;502;503;504;505;506;507;508;509;510;511;512;513;514;515;516;517;518;519;520;521;522;523;524;525;526;527;528;529;530;531;532;533;534;535;536;537;538;539;540;541;542;543;544;545;546;547;548;549;550;551;552;553;554;555;556;557;558;559;560;561;562;563;564;565;566;567;568;569;570;571]);
(269,[34;35;36;37;39;268;118;40;156;209]);
(270,[34;35;36;37;39;268;118;40;156;209]);
(271,[34;35;36;37;39;268;118;40;156;209;272;273;274;275;276;277;278;279;280;281;282;283;284;285;286;287;288;289;290;291;292;293;294;295;296;297;298;299;300;301;302;303;304;305;306;307;308;309;310;311;312;313;314;315;316;317;318;319;320;321;322;323;324;325;326]);
(272,[34;35;36;37;39;268;118;40;156;209;271]);
(273,[34;35;36;37;39;268;118;40;156;209;271]);
(274,[34;35;36;37;39;268;118;40;156;209;271;275;276;277;278;279;280;281;282;283;284;285;286;287;288;289;290;291;292;293;294;295;296;297;298;299;300;301;302;303;304;305;306;307;308;309;310;311;312;313;314;315;316;317;318;319;320;321;322;323;324;325;326]);
(275,[34;35;36;37;39;268;118;40;156;209;274;271]);
(276,[34;35;36;37;39;268;118;40;156;209;274;271]);
(277,[34;35;36;37;39;268;118;40;156;209;274;271;278;279;280;281;282;283;284;285;286;287;288;289;290;291;292;293;294;295;296;297;298;299;300;301;302;303;304;305;306;307;308;309;310;311;312;313;314;315;316;317;318;319;320;321;322;323;324;325;326]);
(278,[34;35;36;37;39;268;118;40;156;209;274;277;271]);
(279,[34;35;36;37;39;268;118;40;156;209;274;277;271]);
(280,[34;35;36;37;39;268;118;40;156;209;274;277;271;281;282;283;284;285;286;287;288;289;290;291;292;293;294;295;296;297;298;299;300;301;302;303;304;305;306;307;308;309;310;311;312;313;314;315;316;317;318;319;320;321;322;323;324;325;326]);
(281,[34;35;36;37;39;268;118;40;156;209;274;277;280;271]);
(282,[34;35;36;37;39;268;118;40;156;209;274;277;280;271]);
(283,[34;35;36;37;39;268;118;40;156;209;274;277;280;271;284;285;286;287;288;289;290;291;292;293;294;295;296;297;298;299;300;301;302;303;304;305;306;307;308;309;310;311;312;313;314;315;316;317;318;319;320;321;322;323;324;325;326]);
(284,[34;35;36;37;39;268;118;40;156;209;274;277;280;283;271]);
(285,[34;35;36;37;39;268;118;40;156;209;274;277;280;283;271]);
(286,[34;35;36;37;39;268;118;40;156;209;274;277;280;283;271;287;288;289;290;291;292;293;294;295;296;297;298;299;300;301;302;303;304;305;306;307;308;309;310;311;312;313;314;315;316;317;318;319;320;321;322;323;324;325;326]);
(287,[34;35;36;37;39;268;118;40;156;209;274;277;280;283;286;271]);
(288,[34;35;36;37;39;268;118;40;156;209;274;277;280;283;286;271]);
(289,[34;35;36;37;39;268;118;40;156;209;274;277;280;283;286;271;290;291;292;293;294;295;296;297;298;299;300;301;302;303;304;305;306;307;308;309;310;311;312;313;314;315;316;317;318;319;320;321;322;323;324;325;326]);
(290,[34;35;36;37;39;268;118;40;156;209;274;277;280;283;286;289;271]);
(291,[34;35;36;37;39;268;118;40;156;209;274;277;280;283;286;289;271]);
(292,[34;35;36;37;39;268;118;40;156;209;274;277;280;283;286;289;271;293;294;295;296;297;298;299;300;301;302;303;304;305;306;307;308;309;310;311;312;313;314;315;316;317;318;319;320;321;322;323;324;325;326]);
(293,[34;35;36;37;39;268;118;40;156;209;274;277;280;283;286;289;292;271]);
(294,[34;35;36;37;39;268;118;40;156;209;274;277;280;283;286;289;292;271]);
(295,[34;35;36;37;39;268;118;40;156;209;274;277;280;283;286;289;292;271;296;297;298;299;300;301;302;303;304;305;306;307;308;309;310;311;312;313;314;315;316;317;318;319;320;321;322;323;324;325;326]);
(296,[34;35;36;37;39;268;118;40;156;209;274;277;280;283;286;289;292;295;271]);
(297,[34;35;36;37;39;268;118;40;156;209;274;277;280;283;286;289;292;295;271]);
(298,[34;35;36;37;39;268;118;40;156;209;274;277;280;283;286;289;292;295;271;299;300;301;302;303;304;305;306;307;308;309;310;311;312;313;314;315;316;317;318;319;320;321;322;323;324;325;326]);
(299,[34;35;36;37;39;268;118;40;156;209;274;277;280;283;286;289;292;295;271;298]);
(300,[34;35;36;37;39;268;118;40;156;209;274;277;280;283;286;289;292;295;271;298]);
(301,[34;35;36;37;39;268;118;40;156;209;274;277;280;283;286;289;292;295;298;271;302;303;304;305;306;307;308;309;310;311;312;313;314;315;316;317;318;319;320;321;322;323;324;325;326]);
(302,[34;35;36;37;39;268;118;40;156;209;274;277;280;283;286;289;292;295;301;298;271]);
(303,[34;35;36;37;39;268;118;40;156;209;274;277;280;283;286;289;292;295;301;298;271]);
(304,[34;35;36;37;39;268;118;40;156;209;274;277;280;283;286;289;292;301;298;271;295;305;306;307;308;309;310;311;312;313;314;315;316;317;318;319;320;321;322;323;324;325;326]);
(305,[34;35;36;37;39;268;118;40;156;209;274;277;280;283;286;289;292;304;301;298;271;295]);
(306,[34;35;36;37;39;268;118;40;156;209;274;277;280;283;286;289;292;304;301;298;271;295]);
(307,[34;35;36;37;39;268;118;40;156;209;274;277;280;283;286;289;304;301;298;271;295;292;308;309;310;311;312;313;314;315;316;317;318;319;320;321;322;323;324;325;326]);
(308,[34;35;36;37;39;268;118;40;156;209;274;277;280;283;286;289;307;304;301;298;271;295;292]);
(309,[34;35;36;37;39;268;118;40;156;209;274;277;280;283;286;289;307;304;301;298;271;295;292]);
(310,[34;35;36;37;39;268;118;40;156;209;274;277;280;283;286;307;304;301;298;271;295;292;289;311;312;313;314;315;316;317;318;319;320;321;322;323;324;325;326]);
(311,[34;35;36;37;39;268;118;40;156;209;274;277;280;283;286;310;307;304;301;298;271;295;292;289]);
(312,[34;35;36;37;39;268;118;40;156;209;274;277;280;283;286;310;307;304;301;298;271;295;292;289]);
(313,[34;35;36;37;39;268;118;40;156;209;274;277;280;283;310;307;304;301;298;271;295;292;289;286;314;315;316;317;318;319;320;321;322;323;324;325;326]);
(314,[34;35;36;37;39;268;118;40;156;209;274;277;280;283;313;310;307;304;301;298;271;295;292;289;286]);
(315,[34;35;36;37;39;268;118;40;156;209;274;277;280;283;313;310;307;304;301;298;271;295;292;289;286]);
(316,[34;35;36;37;39;268;118;40;156;209;274;277;280;313;310;307;304;301;298;271;295;292;289;286;283;317;318;319;320;321;322;323;324;325;326]);
(317,[34;35;36;37;39;268;118;40;156;209;274;277;280;316;313;310;307;304;301;298;271;295;292;289;286;283]);
(318,[34;35;36;37;39;268;118;40;156;209;274;277;280;316;313;310;307;304;301;298;271;295;292;289;286;283]);
(319,[34;35;36;37;39;268;118;40;156;209;274;277;316;313;310;307;304;301;298;271;295;292;289;286;283;280;320;321;322;323;324;325;326]);
(320,[34;35;36;37;39;268;118;40;156;209;274;277;319;316;313;310;307;304;301;298;271;295;292;289;286;283;280]);
(321,[34;35;36;37;39;268;118;40;156;209;274;277;319;316;313;310;307;304;301;298;271;295;292;289;286;283;280]);
(322,[34;35;36;37;39;268;118;40;156;209;274;319;316;313;310;307;304;301;298;271;295;292;289;286;283;280;277;323;324;325;326]);
(323,[34;35;36;37;39;268;118;40;156;209;274;322;319;316;313;310;307;304;301;298;271;295;292;289;286;283;280;277]);
(324,[34;35;36;37;39;268;118;40;156;209;274;322;319;316;313;310;307;304;301;298;271;295;292;289;286;283;280;277]);
(325,[34;35;36;37;39;268;118;40;156;209;322;319;316;313;310;307;304;301;298;271;295;292;289;286;283;280;277;274;326]);
(326,[34;35;36;37;39;268;118;40;156;209;325;322;319;316;313;310;307;304;301;298;271;295;292;289;286;283;280;277;274]);
(327,[34;35;36;37;39;268;40;156;209;118;328;329;330;331;332;333;334;335;336;337;338;339;340;341;342;343;344;345;346;347;348;349;350;351;352;353;354;355;356;357;358;359;360;361;362;363;364;365;366;367;368;369;370;371;372;373;374;375;376;377;378;379;380;381;382;383;384;385;386;387;388;389;390;391;392;393;394;395;396;397;398;399;400;401;402;403;404;405;406;407;408;409;410;411;412;413;414;415;416;417;418;419;420;421;422;423;424;425;426;427;428;429;430;431;432;433;434;435;436;437;438;439;440;441;442;443;444;445;446;447;448;449;450;451;452;453;454;455;456;457;458;459;460;461;462;463;464;465;466;467;468;469;470;471;472;473;474;475;476;477;478;479;480;481;482;483;484;485;486;487;488;489;490;491;492;493;494;495;496;497;498;499;500;501;502;503;504;505;506;507;508;509;510;511;512;513;514;515;516;517;518;519;520;521;522;523;524;525;526;527;528;529;530;531;532;533;534;535;536;537;538;539;540;541;542;543;544;545;546;547;548;549;550;551;552;553;554;555;556;557;558;559;560;561;562;563;564;565;566;567;568;569;570;571]);
(328,[34;35;36;37;39;268;327;40;156;209;118]);
(329,[34;35;36;37;39;268;327;40;156;209;118]);
(330,[34;35;36;37;39;268;327;40;156;209;118;331;332;333;334;335;336]);
(331,[34;35;36;37;39;268;327;40;156;209;118;330]);
(332,[34;35;36;37;39;268;327;40;156;209;118;330]);
(333,[34;35;36;37;39;268;327;40;156;209;118;330]);
(334,[34;35;36;37;39;268;327;40;156;209;118;330;335;336;337;338;339;340;341;342;343;344;345;346;347;348;349;350;351;352;353]);
(335,[34;35;36;37;39;268;327;40;156;209;118;334;330]);
(336,[34;35;36;37;39;268;327;40;156;209;118;334;330]);
(337,[34;35;36;37;39;268;327;40;156;209;118;334;338;339;340;341;342;343;344;345;346;347;348;349;350;351;352;353]);
(338,[34;35;36;37;39;268;327;40;156;209;118;334;337]);
(339,[34;35;36;37;39;268;327;40;156;209;118;334;337]);
(340,[34;35;36;37;39;268;327;40;156;209;118;334;337;341;342;343;344;345;346;347;348;349;350;351;352;353]);
(341,[34;35;36;37;39;268;327;40;156;209;118;334;337;340]);
(342,[34;35;36;37;39;268;327;40;156;209;118;334;337;340]);
(343,[34;35;36;37;39;268;327;40;156;209;118;334;337;340;344;345;346;347;348;349;350;351;352;353]);
(344,[34;35;36;37;39;268;327;40;156;209;118;334;337;340;343]);
(345,[34;35;36;37;39;268;327;40;156;209;118;334;337;340;343]);
(346,[34;35;36;37;39;268;327;40;156;209;118;334;337;340;343;347;348;349;350;351;352;353]);
(347,[34;35;36;37;39;268;327;40;156;209;118;334;337;340;346;343]);
(348,[34;35;36;37;39;268;327;40;156;209;118;334;337;340;346;343]);
(349,[34;35;36;37;39;268;327;40;156;209;118;334;337;346;343;340;350;351;352;353]);
(350,[34;35;36;37;39;268;327;40;156;209;118;334;337;349;346;343;340]);
(351,[34;35;36;37;39;268;327;40;156;209;118;334;337;349;346;343;340]);
(352,[34;35;36;37;39;268;327;40;156;209;118;337;349;346;343;340;334;353;354]);
(353,[34;35;36;37;39;268;327;40;156;209;118;352;337;349;346;343;340;334]);
(354,[34;35;36;37;39;268;327;40;156;209;118;352]);
(355,[34;35;36;37;39;327;40;156;209;118;268;356;357;358;359;360;361;362;363;364;365;366;367;368;369;370;371;372;373;374;375;376;377;378;379;380;381;382;383;384;385;386;387;388;389;390;391;392;393;394;395;396;397;398;399;400;401;402;403;404;405;406;407;408;409;410;411;412;413;414;415;416;417;418;419;420;421;422;423;424;425;426;427;428;429;430;431;432;433;434;435;436;437;438;439;440;441;442;443;444;445;446;447;448;449;450;451;452;453;454;455;456;457;458;459;460;461;462;463;464;465;466;467;468;469;470;471;472;473;474;475;476;477;478;479;480;481;482;483;484;485;486;487;488;489;490;491;492;493;494;495;496;497;498;499;500;501;502;503;504;505;506;507;508;509;510;511;512;513;514;515;516;517;518;519;520;521;522;523;524;525;526;527;528;529;530;531;532;533;534;535;536;537;538;539;540;541;542;543;544;545;546;547;548;549;550;551;552;553;554;555;556;557;558;559;560;561;562;563;564;565;566;567;568;569;570;571]);
(356,[34;35;36;37;39;355;327;40;156;209;118;268]);
(357,[34;35;36;37;39;355;327;40;156;209;118;268]);
(358,[34;35;36;37;39;355;327;40;156;209;118;268;359;360;361;362;363;364;365;366;367;368;369;370;371]);
(359,[34;35;36;37;39;355;327;40;156;209;118;268;358]);
(360,[34;35;36;37;39;355;327;40;156;209;118;268;358]);
(361,[34;35;36;37;39;355;327;40;156;209;118;268;358;362;363;364;365;366;367;368;369;370;371]);
(362,[34;35;36;37;39;355;327;40;156;209;118;268;361;358]);
(363,[34;35;36;37;39;355;327;40;156;209;118;268;361;358]);
(364,[34;35;36;37;39;355;327;40;156;209;118;268;358;361;365;366;367;368;369;370;371]);
(365,[34;35;36;37;39;355;327;40;156;209;118;268;364;358;361]);
(366,[34;35;36;37;39;355;327;40;156;209;118;268;364;358;361]);
(367,[34;35;36;37;39;355;327;40;156;209;118;268;364;358;361;368;369;370;371]);
(368,[34;35;36;37;39;355;327;40;156;209;118;268;364;358;367;361]);
(369,[34;35;36;37;39;355;327;40;156;209;118;268;364;358;367;361]);
(370,[34;35;36;37;39;355;327;40;156;209;118;268;364;367;361;358;371]);
(371,[34;35;36;37;39;355;327;40;156;209;118;268;364;370;367;361;358]);
(372,[34;35;36;37;39;355;327;40;156;209;118;268;373;374;375;376;377;378;379;380;381;382;383;384;385;386;387;388;389;390;391;392;393;394;395;396;397;398;399;400;401;402;403;404;405;406;407;408;409;410;411;412;413;414;415;416;417;418;419;420;421;422;423;424;425;426;427;428;429;430;431;432;433;434;435;436;437;438;439;440;441;442;443;444;445;446;447;448;449;450;451;452;453;454;455;456;457;458;459;460;461;462;463;464;465;466;467;468;469;470;471;472;473;474;475;476;477;478;479;480;481;482;483;484;485;486;487;488;489;490;491;492;493;494;495;496;497;498;499;500;501;502;503;504;505;506;507;508;509;510;511;512;513;514;515;516;517;518;519;520;521;522;523;524;525;526;527;528;529;530;531;532;533;534;535;536;537;538;539;540;541;542;543;544;545;546;547;548;549;550;551;552;553;554;555;556;557;558;559;560;561;562;563;564;565;566;567;568;569;570;571]);
(373,[34;35;36;37;39;355;327;40;156;209;118;372;268]);
(374,[34;35;36;37;39;355;327;40;156;209;118;372;268]);
(375,[34;35;36;37;39;355;327;40;156;209;118;372;268;376;377;378;379;380;381;382]);
(376,[34;35;36;37;39;355;327;40;156;209;118;372;268;375]);
(377,[34;35;36;37;39;355;327;40;156;209;118;372;268;375]);
(378,[34;35;36;37;39;355;327;40;156;209;118;372;268;375;379;380;381;382]);
(379,[34;35;36;37;39;355;327;40;156;209;118;372;268;375;378]);
(380,[34;35;36;37;39;355;327;40;156;209;118;372;268;375;378]);
(381,[34;35;36;37;39;355;327;40;156;209;118;372;268;378;375;382]);
(382,[34;35;36;37;39;355;327;40;156;209;118;372;268;381;378;375]);
(383,[34;35;36;37;39;355;327;40;156;209;118;372;268;384;385;386;387;388;389;390;391;392;393;394;395;396;397;398;399;400;401;402;403;404;405;406;407;408;409;410;411;412;413;414;415;416;417;418;419;420;421;422;423;424;425;426;427;428;429;430;431;432;433;434;435;436;437;438;439;440;441;442;443;444;445;446;447;448;449;450;451;452;453;454;455;456;457;458;459;460;461;462;463;464;465;466;467;468;469;470;471;472;473;474;475;476;477;478;479;480;481;482;483;484;485;486;487;488;489;490;491;492;493;494;495;496;497;498;499;500;501;502;503;504;505;506;507;508;509;510;511;512;513;514;515;516;517;518;519;520;521;522;523;524;525;526;527;528;529;530;531;532;533;534;535;536;537;538;539;540;541;542;543;544;545;546;547;548;549;550;551;552;553;554;555;556;557;558;559;560;561;562;563;564;565;566;567;568;569;570;571]);
(384,[34;35;36;37;39;355;327;40;156;209;118;372;383;268]);
(385,[34;35;36;37;39;355;327;40;156;209;118;372;383;268]);
(386,[34;35;36;37;39;355;327;40;156;209;118;372;383;268;387;388;389;390;391;392;393;394;395;396;397;398;399]);
(387,[34;35;36;37;39;355;327;40;156;209;118;372;383;268;386]);
(388,[34;35;36;37;39;355;327;40;156;209;118;372;383;268;386]);
(389,[34;35;36;37;39;355;327;40;156;209;118;372;383;268;386;390;391;392;393;394;395;396;397;398;399]);
(390,[34;35;36;37;39;355;327;40;156;209;118;372;383;268;386;389]);
(391,[34;35;36;37;39;355;327;40;156;209;118;372;383;268;386;389]);
(392,[34;35;36;37;39;355;327;40;156;209;118;372;383;268;386;389;393;394;395;396;397;398;399]);
(393,[34;35;36;37;39;355;327;40;156;209;118;372;383;268;386;389;392]);
(394,[34;35;36;37;39;355;327;40;156;209;118;372;383;268;386;389;392]);
(395,[34;35;36;37;39;355;327;40;156;209;118;372;383;268;386;392;389;396;397;398;399]);
(396,[34;35;36;37;39;355;327;40;156;209;118;372;383;268;386;395;392;389]);
(397,[34;35;36;37;39;355;327;40;156;209;118;372;383;268;386;395;392;389]);
(398,[34;35;36;37;39;355;327;40;156;209;118;372;383;268;395;392;389;386;399]);
(399,[34;35;36;37;39;355;327;40;156;209;118;372;383;268;398;395;392;389;386]);
(400,[34;35;36;37;39;355;327;40;156;118;372;383;268;209;401;402;403;404;405;406;407;408;409;410;411;412;413;414;415;416;417;418;419;420;421;422;423;424;425;426;427;428;429;430;431;432;433;434;435;436;437;438;439;440;441;442;443;444;445;446;447;448;449;450;451;452;453;454;455;456;457;458;459;460;461;462;463;464;465;466;467;468;469;470;471;472;473;474;475;476;477;478;479;480;481;482;483;484;485;486;487;488;489;490;491;492;493;494;495;496;497;498;499;500;501;502;503;504;505;506;507;508;509;510;511;512;513;514;515;516;517;518;519;520;521;522;523;524;525;526;527;528;529;530;531;532;533;534;535;536;537;538;539;540;541;542;543;544;545;546;547;548;549;550;551;552;553;554;555;556;557;558;559;560;561;562;563;564;565;566;567;568;569;570;571]);
(401,[34;35;36;37;39;355;327;40;156;400;118;372;383;268;209]);
(402,[34;35;36;37;39;355;327;40;156;400;118;372;383;268;209]);
(403,[34;35;36;37;39;355;327;40;156;400;118;372;383;268;209;404;405;406;407;408;409;410;411;412;413;414;415;416]);
(404,[34;35;36;37;39;355;327;40;156;400;118;372;383;268;209;403]);
(405,[34;35;36;37;39;355;327;40;156;400;118;372;383;268;209;403]);
(406,[34;35;36;37;39;355;327;40;156;400;118;372;383;268;209;403;407;408;409;410;411;412;413;414;415;416]);
(407,[34;35;36;37;39;355;327;40;156;400;118;372;383;268;209;403;406]);
(408,[34;35;36;37;39;355;327;40;156;400;118;372;383;268;209;403;406]);
(409,[34;35;36;37;39;355;327;40;156;400;118;372;383;268;209;403;406;410;411;412;413;414;415;416]);
(410,[34;35;36;37;39;355;327;40;156;400;118;372;383;268;209;403;406;409]);
(411,[34;35;36;37;39;355;327;40;156;400;118;372;383;268;209;403;406;409]);
(412,[34;35;36;37;39;355;327;40;156;400;118;372;383;268;209;403;409;406;413;414;415;416]);
(413,[34;35;36;37;39;355;327;40;156;400;118;372;383;268;209;403;412;409;406]);
(414,[34;35;36;37;39;355;327;40;156;400;118;372;383;268;209;403;412;409;406]);
(415,[34;35;36;37;39;355;327;40;156;400;118;372;383;268;209;412;409;406;403;416]);
(416,[34;35;36;37;39;355;327;40;156;400;118;372;383;268;209;415;412;409;406;403]);
(417,[34;35;36;37;39;355;40;156;400;118;372;383;268;209;327;418;419;420;421;422;423;424;425;426;427;428;429;430;431;432;433;434;435;436;437;438;439;440;441;442;443;444;445;446;447;448;449;450;451;452;453;454;455;456;457;458;459;460;461;462;463;464;465;466;467;468;469;470;471;472;473;474;475;476;477;478;479;480;481;482;483;484;485;486;487;488;489;490;491;492;493;494;495;496;497;498;499;500;501;502;503;504;505;506;507;508;509;510;511;512;513;514;515;516;517;518;519;520;521;522;523;524;525;526;527;528;529;530;531;532;533;534;535;536;537;538;539;540;541;542;543;544;545;546;547;548;549;550;551;552;553;554;555;556;557;558;559;560;561;562;563;564;565;566;567;568;569;570;571]);
(418,[34;35;36;37;39;355;417;40;156;400;118;372;383;268;209;327]);
(419,[34;35;36;37;39;355;417;40;156;400;118;372;383;268;209;327]);
(420,[34;35;36;37;39;355;417;40;156;400;118;372;383;268;209;327;421;422;423;424;425;426;427;428;429;430]);
(421,[34;35;36;37;39;355;417;40;156;400;118;372;383;268;209;327;420]);
(422,[34;35;36;37;39;355;417;40;156;400;118;372;383;268;209;327;420]);
(423,[34;35;36;37;39;355;417;40;156;400;118;372;383;268;209;327;420;424;425;426;427;428;429;430]);
(424,[34;35;36;37;39;355;417;40;156;400;118;372;383;268;209;327;420;423]);
(425,[34;35;36;37;39;355;417;40;156;400;118;372;383;268;209;327;420;423]);
(426,[34;35;36;37;39;355;417;40;156;400;118;372;383;268;209;327;420;423;427;428;429;430]);
(427,[34;35;36;37;39;355;417;40;156;400;118;372;383;268;209;327;420;426;423]);
(428,[34;35;36;37;39;355;417;40;156;400;118;372;383;268;209;327;420;426;423]);
(429,[34;35;36;37;39;355;417;40;156;400;118;372;383;268;209;327;426;423;420;430]);
(430,[34;35;36;37;39;355;417;40;156;400;118;372;383;268;209;327;429;426;423;420]);
(431,[34;35;36;37;39;355;40;156;400;118;372;383;268;209;327;417;432;433;434;435;436;437;438;439;440;441;442;443;444;445;446;447;448;449;450;451;452;453;454;455;456;457;458;459;460;461;462;463;464;465;466;467;468;469;470;471;472;473;474;475;476;477;478;479;480;481;482;483;484;485;486;487;488;489;490;491;492;493;494;495;496;497;498;499;500;501;502;503;504;505;506;507;508;509;510;511;512;513;514;515;516;517;518;519;520;521;522;523;524;525;526;527;528;529;530;531;532;533;534;535;536;537;538;539;540;541;542;543;544;545;546;547;548;549;550;551;552;553;554;555;556;557;558;559;560;561;562;563;564;565;566;567;568;569;570;571]);
(432,[34;35;36;37;39;355;431;40;156;400;118;372;383;268;209;327;417]);
(433,[34;35;36;37;39;355;431;40;156;400;118;372;383;268;209;327;417]);
(434,[34;35;36;37;39;355;431;40;156;400;118;372;383;268;209;327;417;435;436;437;438;439;440;441;442;443;444;445;446;447]);
(435,[34;35;36;37;39;355;431;40;156;400;118;372;383;268;209;327;417;434]);
(436,[34;35;36;37;39;355;431;40;156;400;118;372;383;268;209;327;417;434]);
(437,[34;35;36;37;39;355;431;40;156;400;118;372;383;268;209;327;417;434;438;439;440;441;442;443;444;445;446;447]);
(438,[34;35;36;37;39;355;431;40;156;400;118;372;383;268;209;327;417;434;437]);
(439,[34;35;36;37;39;355;431;40;156;400;118;372;383;268;209;327;417;434;437]);
(440,[34;35;36;37;39;355;431;40;156;400;118;372;383;268;209;327;417;434;437;441;442;443;444;445;446;447]);
(441,[34;35;36;37;39;355;431;40;156;400;118;372;383;268;209;327;417;434;437;440]);
(442,[34;35;36;37;39;355;431;40;156;400;118;372;383;268;209;327;417;434;437;440]);
(443,[34;35;36;37;39;355;431;40;156;400;118;372;383;268;209;327;417;434;440;437;444;445;446;447]);
(444,[34;35;36;37;39;355;431;40;156;400;118;372;383;268;209;327;417;434;443;440;437]);
(445,[34;35;36;37;39;355;431;40;156;400;118;372;383;268;209;327;417;434;443;440;437]);
(446,[34;35;36;37;39;355;431;40;156;400;118;372;383;268;209;327;417;443;440;437;434;447]);
(447,[34;35;36;37;39;355;431;40;156;400;118;372;383;268;209;327;417;446;443;440;437;434]);
(448,[34;35;36;37;39;355;40;156;400;118;372;383;268;209;327;417;431;449;450;451;452;453;454;455;456;457;458;459;460;461;462;463;464;465;466;467;468;469;470;471;472;473;474;475;476;477;478;479;480;481;482;483;484;485;486;487;488;489;490;491;492;493;494;495;496;497;498;499;500;501;502;503;504;505;506;507;508;509;510;511;512;513;514;515;516;517;518;519;520;521;522;523;524;525;526;527;528;529;530;531;532;533;534;535;536;537;538;539;540;541;542;543;544;545;546;547;548;549;550;551;552;553;554;555;556;557;558;559;560;561;562;563;564;565;566;567;568;569;570;571]);
(449,[34;35;36;37;39;355;448;40;156;400;118;372;383;268;209;327;417;431]);
(450,[34;35;36;37;39;355;448;40;156;400;118;372;383;268;209;327;417;431]);
(451,[34;35;36;37;39;355;448;40;156;400;118;372;383;268;209;327;417;431;452;453;454;455;456;457;458;459;460;461]);
(452,[34;35;36;37;39;355;448;40;156;400;118;372;383;268;209;327;417;431;451]);
(453,[34;35;36;37;39;355;448;40;156;400;118;372;383;268;209;327;417;431;451]);
(454,[34;35;36;37;39;355;448;40;156;400;118;372;383;268;209;327;417;431;451;455;456;457;458;459;460;461]);
(455,[34;35;36;37;39;355;448;40;156;400;118;372;383;268;209;327;417;431;451;454]);
(456,[34;35;36;37;39;355;448;40;156;400;118;372;383;268;209;327;417;431;451;454]);
(457,[34;35;36;37;39;355;448;40;156;400;118;372;383;268;209;327;417;431;451;454;458;459;460;461]);
(458,[34;35;36;37;39;355;448;40;156;400;118;372;383;268;209;327;417;431;451;457;454]);
(459,[34;35;36;37;39;355;448;40;156;400;118;372;383;268;209;327;417;431;451;457;454]);
(460,[34;35;36;37;39;355;448;40;156;400;118;372;383;268;209;327;417;431;457;454;451;461]);
(461,[34;35;36;37;39;355;448;40;156;400;118;372;383;268;209;327;417;431;460;457;454;451]);
(462,[34;35;36;37;39;355;448;156;400;118;372;383;268;209;327;417;431;40;463;464;465;466;467;468;469;470;471;472;473;474;475;476;477;478;479;480;481;482;483;484;485;486;487;488;489;490;491;492;493;494;495;496;497;498;499;500;501;502;503;504;505;506;507;508;509;510;511;512;513;514;515;516;517;518;519;520;521;522;523;524;525;526;527;528;529;530;531;532;533;534;535;536;537;538;539;540;541;542;543;544;545;546;547;548;549;550;551;552;553;554;555;556;557;558;559;560;561;562;563;564;565;566;567;568;569;570;571]);
(463,[34;35;36;37;39;355;448;462;156;400;118;372;383;268;209;327;417;431;40]);
(464,[34;35;36;37;39;355;448;462;156;400;118;372;383;268;209;327;417;431;40]);
(465,[34;35;36;37;39;355;448;462;156;400;118;372;383;268;209;327;417;431;40;466;467;468;469;470;471;472;473;474;475;476;477;478;479;480;481;482;483;484;485;486;487;488;489;490;491;492;493;494;495;496;497;498;499;500;501;502;503;504;505;506;507;508;509;510;511;512;513;514;515;516;517;518;519;520;521;522;523;524;525;526;527;528;529;530;531;532;533;534;535;536;537;538;539;540;541;542;543;544;545;546;547;548;549;550;551;552;553;554;555;556;557;558;559;560;561;562;563;564;565;566;567;568;569;570;571]);
(466,[34;35;36;37;39;355;448;462;156;400;118;372;383;268;209;327;417;431;40;465]);
(467,[34;35;36;37;39;355;448;462;156;400;118;372;383;268;209;327;417;431;40;465]);
(468,[34;35;36;37;39;355;448;462;156;400;118;372;383;268;209;327;417;431;40;465;469;470;471;472;473;474;475;476;477;478;479;480;481;482;483;484;485;486;487;488;489;490;491;492;493;494;495;496;497;498;499;500;501;502;503;504;505;506;507;508;509;510;511;512;513;514;515;516;517;518;519;520;521;522;523;524;525;526;527;528;529;530;531;532;533;534;535;536;537;538;539;540;541;542;543;544;545;546;547;548;549;550;551;552;553;554;555;556;557;558;559;560;561;562;563;564;565;566;567;568;569;570;571]);
(469,[34;35;36;37;39;355;448;462;156;400;118;372;383;268;209;327;417;431;40;465;468]);
(470,[34;35;36;37;39;355;448;462;156;400;118;372;383;268;209;327;417;431;40;465;468]);
(471,[34;35;36;37;39;355;448;462;156;400;118;372;383;268;209;327;417;431;40;468;465;472;473;474;475;476;477;478;479;480;481;482;483;484;485;486;487;488;489;490;491;492;493;494;495;496;497;498;499;500;501;502;503;504;505;506;507;508;509;510;511;512;513;514;515;516;517;518;519;520;521;522;523;524;525;526;527;528;529;530;531;532;533;534;535;536;537;538;539;540;541;542;543;544;545;546;547;548;549;550;551;552;553;554;555;556;557;558;559;560;561;562;563;564;565;566;567;568;569;570;571;573;572]);
(472,[34;35;36;37;39;355;448;462;156;400;118;372;383;268;209;327;417;431;40;471;468;465]);
(473,[34;35;36;37;39;355;448;462;156;400;118;372;383;268;209;327;417;431;40;471;468;465]);
(474,[34;35;36;37;39;355;448;462;156;400;118;372;383;268;209;327;417;431;471;468;465;40;475;476;477;478;479;480;481;482;483;484;485;486;487;488;489;490;491;492;493;494;495;496;497;498;499;500;501;502;503;504;505;506;507;508;509;510;511;512;513;514;515;516;517;518;519;520;521;522;523;524;525;526;527;528;529;530;531;532;533;534;535;536;537;538;539;540;541;542;543;544;545;546;547;548;549;550;551;552;553;554;555;556;557;558;559;560;561;562;563;564;565;566;567;568;569;570;571;573;572]);
(475,[34;35;36;37;39;355;448;462;156;400;118;372;383;268;209;327;417;431;474;471;468;465;40]);
(476,[34;35;36;37;39;355;448;462;156;400;118;372;383;268;209;327;417;431;474;471;468;465;40]);
(477,[34;35;36;37;39;355;448;462;156;400;118;372;383;268;209;327;417;431;474;471;465;468;478;479;480;481;482;483;484;485;486;487;488;489;490;491;492;493;494;495;496;497;498;499;500;501;502;503;504;505;506;507;508;509;510;511;512;513;514;515;516;517;518;519;520;521;522;523;524;525;526;527;528;529;530;531;532;533;534;535;536;537;538;539;540;541;542;543;544;545;546;547;548;549;550;551;552;553;554;555;556;557;558;559;560;561;562;563;564;565;566;567;568;569;570;571;573;572]);
(478,[34;35;36;37;39;355;448;462;156;400;118;372;383;268;209;327;417;431;474;471;477;465;468]);
(479,[34;35;36;37;39;355;448;462;156;400;118;372;383;268;209;327;417;431;474;471;477;465;468]);
(480,[34;35;36;37;39;355;448;462;156;400;118;372;383;268;209;327;417;431;474;477;465;468;471;481;482;483;484;485;486;487;488;489;490;491;492;493;494;495;496;497;498;499;500;501;502;503;504;505;506;507;508;509;510;511;512;513;514;515;516;517;518;519;520;521;522;523;524;525;526;527;528;529;530;531;532;533;534;535;536;537;538;539;540;541;542;543;544;545;546;547;548;549;550;551;552;553;554;555;556;557;558;559;560;561;562;563;564;565;566;567;568;569;570;571;573;572]);
(481,[34;35;36;37;39;355;448;462;156;400;118;372;383;268;209;327;417;431;474;480;477;465;468;471]);
(482,[34;35;36;37;39;355;448;462;156;400;118;372;383;268;209;327;417;431;474;480;477;465;468;471]);
(483,[34;35;36;37;39;355;448;462;156;400;118;372;383;268;209;327;417;431;480;477;465;468;471;474;484;485;486;487;488;489;490;491;492;493;494;495;496;497;498;499;500;501;502;503;504;505;506;507;508;509;510;511;512;513;514;515;516;517;518;519;520;521;522;523;524;525;526;527;528;529;530;531;532;533;534;535;536;537;538;539;540;541;542;543;544;545;546;547;548;549;550;551;552;553;554;555;556;557;558;559;560;561;562;563;564;565;566;567;568;569;570;571]);
(484,[34;35;36;37;39;355;448;462;156;400;118;372;383;268;209;327;417;431;483;480;477;465;468;471;474]);
(485,[34;35;36;37;39;355;448;462;156;400;118;372;383;268;209;327;417;431;483;480;477;465;468;471;474]);
(486,[34;35;36;37;39;355;448;462;156;400;118;372;383;268;209;327;417;431;483;480;477;465;468;471;474;487;488;489;490;491;492;493;494;495;496;497;498;499;500;501;502;503;504;505;506;507;508;509;510;511;512;513;514;515;516;517;518;519;520;521;522;523;524;525;526;527;528;529;530;531;532;533;534;535;536;537;538;539;540;541;542;543;544;545;546;547;548;549;550;551;552;553;554;555;556;557;558;559;560;561;562;563;564;565;566;567;568;569;570;571;573;572]);
(487,[34;35;36;37;39;355;448;462;156;400;118;372;383;268;209;327;417;431;483;480;477;465;468;471;486;474]);
(488,[34;35;36;37;39;355;448;462;156;400;118;372;383;268;209;327;417;431;483;480;477;465;468;471;486;474]);
(489,[34;35;36;37;39;355;448;462;156;400;118;372;383;268;209;327;417;431;483;480;477;465;468;471;486;474;490;491;492;493;494;495;496;497;498;499;500;501;502;503;504;505;506;507;508;509;510;511;512;513;514;515;516;517;518;519;520;521;522;523;524;525;526;527;528;529;530;531;532;533;534;535;536;537;538;539;540;541;542;543;544;545;546;547;548;549;550;551;552;553;554;555;556;557;558;559;560;561;562;563;564;565;566;567;568;569;570;571;573;572]);
(490,[34;35;36;37;39;355;448;462;156;400;118;372;383;268;209;327;417;431;483;480;477;465;468;471;486;489;474]);
(491,[34;35;36;37;39;355;448;462;156;400;118;372;383;268;209;327;417;431;483;480;477;465;468;471;486;489;474]);
(492,[34;35;36;37;39;355;448;462;156;400;118;372;383;268;209;327;417;431;483;480;477;465;468;471;486;489;474;493;494;495;496;497;498;499;500;501;502;503;504;505;506;507;508;509;510;511;512;513;514;515;516;517;518;519;520;521;522;523;524;525;526;527;528;529;530;531;532;533;534;535;536;537;538;539;540;541;542;543;544;545;546;547;548;549;550;551;552;553;554;555;556;557;558;559;560;561;562;563;564;565;566;567;568;569;570;571;573;572]);
(493,[34;35;36;37;39;355;448;462;156;400;118;372;383;268;209;327;417;431;483;480;477;465;468;471;486;489;492;474]);
(494,[34;35;36;37;39;355;448;462;156;400;118;372;383;268;209;327;417;431;483;480;477;465;468;471;486;489;492;474]);
(495,[34;35;36;37;39;355;448;462;156;400;118;372;383;268;209;327;417;431;483;480;477;465;468;471;486;489;492;474;496;497;498;499;500;501;502;503;504;505;506;507;508;509;510;511;512;513;514;515;516;517;518;519;520;521;522;523;524;525;526;527;528;529;530;531;532;533;534;535;536;537;538;539;540;541;542;543;544;545;546;547;548;549;550;551;552;553;554;555;556;557;558;559;560;561;562;563;564;565;566;567;568;569;570;571;573;572]);
(496,[34;35;36;37;39;355;448;462;156;400;118;372;383;268;209;327;417;431;483;480;477;465;468;471;486;489;492;495;474]);
(497,[34;35;36;37;39;355;448;462;156;400;118;372;383;268;209;327;417;431;483;480;477;465;468;471;486;489;492;495;474]);
(498,[34;35;36;37;39;355;448;462;156;400;118;372;383;268;209;327;417;431;483;480;477;465;468;471;486;489;492;495;474;499;500;501;502;503;504;505;506;507;508;509;510;511;512;513;514;515;516;517;518;519;520;521;522;523;524;525;526;527;528;529;530;531;532;533;534;535;536;537;538;539;540;541;542;543;544;545;546;547;548;549;550;551;552;553;554;555;556;557;558;559;560;561;562;563;564;565;566;567;568;569;570;571;573;572]);
(499,[34;35;36;37;39;355;448;462;156;400;118;372;383;268;209;327;417;431;483;480;477;465;468;471;486;489;492;495;498;474]);
(500,[34;35;36;37;39;355;448;462;156;400;118;372;383;268;209;327;417;431;483;480;477;465;468;471;486;489;492;495;498;474]);
(501,[34;35;36;37;39;355;448;462;156;400;118;372;383;268;209;327;417;431;483;480;477;465;468;471;486;489;492;495;498;474;502;503;504;505;506;507;508;509;510;511;512;513;514;515;516;517;518;519;520;521;522;523;524;525;526;527;528;529;530;531;532;533;534;535;536;537;538;539;540;541;542;543;544;545;546;547;548;549;550;551;552;553;554;555;556;557;558;559;560;561;562;563;564;565;566;567;568;569;570;571;573;572]);
(502,[34;35;36;37;39;355;448;462;156;400;118;372;383;268;209;327;417;431;483;480;477;465;468;471;486;489;492;495;498;474;501]);
(503,[34;35;36;37;39;355;448;462;156;400;118;372;383;268;209;327;417;431;483;480;477;465;468;471;486;489;492;495;498;474;501]);
(504,[34;35;36;37;39;355;448;462;156;400;118;372;383;268;209;327;417;431;483;480;477;465;468;471;486;489;492;495;498;474;501;505;506;507;508;509;510;511;512;513;514;515;516;517;518;519;520;521;522;523;524;525;526;527;528;529;530;531;532;533;534;535;536;537;538;539;540;541;542;543;544;545;546;547;548;549;550;551;552;553;554;555;556;557;558;559;560;561;562;563;564;565;566;567;568;569;570;571;573;572]);
(505,[34;35;36;37;39;355;448;462;156;400;118;372;383;268;209;327;417;431;483;480;477;465;468;471;486;489;492;495;498;474;504;501]);
(506,[34;35;36;37;39;355;448;462;156;400;118;372;383;268;209;327;417;431;483;480;477;465;468;471;486;489;492;495;498;474;504;501]);
(507,[34;35;36;37;39;355;448;462;156;400;118;372;383;268;209;327;417;431;483;480;477;465;468;471;486;489;492;495;474;504;501;498;508;509;510;511;512;513;514;515;516;517;518;519;520;521;522;523;524;525;526;527;528;529;530;531;532;533;534;535;536;537;538;539;540;541;542;543;544;545;546;547;548;549;550;551;552;553;554;555;556;557;558;559;560;561;562;563;564;565;566;567;568;569;570;571;573;572]);
(508,[34;35;36;37;39;355;448;462;156;400;118;372;383;268;209;327;417;431;483;480;477;465;468;471;486;489;492;495;507;474;504;501;498]);
(509,[34;35;36;37;39;355;448;462;156;400;118;372;383;268;209;327;417;431;483;480;477;465;468;471;486;489;492;495;507;474;504;501;498]);
(510,[34;35;36;37;39;355;448;462;156;400;118;372;383;268;209;327;417;431;483;480;477;465;468;471;486;489;492;507;474;504;501;498;495;511;512;513;514;515;516;517;518;519;520;521;522;523;524;525;526;527;528;529;530;531;532;533;534;535;536;537;538;539;540;541;542;543;544;545;546;547;548;549;550;551;552;553;554;555;556;557;558;559;560;561;562;563;564;565;566;567;568;569;570;571;573;572]);
(511,[34;35;36;37;39;355;448;462;156;400;118;372;383;268;209;327;417;431;483;480;477;465;468;471;486;489;492;510;507;474;504;501;498;495]);
(512,[34;35;36;37;39;355;448;462;156;400;118;372;383;268;209;327;417;431;483;480;477;465;468;471;486;489;492;510;507;474;504;501;498;495]);
(513,[34;35;36;37;39;355;448;462;156;400;118;372;383;268;209;327;417;431;483;480;477;465;468;471;486;489;510;507;474;504;501;498;495;492;514;515;516;517;518;519;520;521;522;523;524;525;526;527;528;529;530;531;532;533;534;535;536;537;538;539;540;541;542;543;544;545;546;547;548;549;550;551;552;553;554;555;556;557;558;559;560;561;562;563;564;565;566;567;568;569;570;571;573;572]);
(514,[34;35;36;37;39;355;448;462;156;400;118;372;383;268;209;327;417;431;483;480;477;465;468;471;486;489;513;510;507;474;504;501;498;495;492]);
(515,[34;35;36;37;39;355;448;462;156;400;118;372;383;268;209;327;417;431;483;480;477;465;468;471;486;489;513;510;507;474;504;501;498;495;492]);
(516,[34;35;36;37;39;355;448;462;156;400;118;372;383;268;209;327;417;431;483;480;477;465;468;471;486;513;510;507;474;504;501;498;495;492;489;517;518;519;520;521;522;523;524;525;526;527;528;529;530;531;532;533;534;535;536;537;538;539;540;541;542;543;544;545;546;547;548;549;550;551;552;553;554;555;556;557;558;559;560;561;562;563;564;565;566;567;568;569;570;571;573;572]);
(517,[34;35;36;37;39;355;448;462;156;400;118;372;383;268;209;327;417;431;483;480;477;465;468;471;486;516;513;510;507;474;504;501;498;495;492;489]);
(518,[34;35;36;37;39;355;448;462;156;400;118;372;383;268;209;327;417;431;483;480;477;465;468;471;486;516;513;510;507;474;504;501;498;495;492;489]);
(519,[34;35;36;37;39;355;448;462;156;400;118;372;383;268;209;327;417;431;483;480;477;465;468;471;516;513;510;507;474;504;501;498;495;492;489;486;520;521;522;523;524;525;526;527;528;529;530;531;532;533;534;535;536;537;538;539;540;541;542;543;544;545;546;547;548;549;550;551;552;553;554;555;556;557;558;559;560;561;562;563;564;565;566;567;568;569;570;571;573;572]);
(520,[34;35;36;37;39;355;448;462;156;400;118;372;383;268;209;327;417;431;483;480;477;465;468;471;519;516;513;510;507;474;504;501;498;495;492;489;486]);
(521,[34;35;36;37;39;355;448;462;156;400;118;372;383;268;209;327;417;431;483;480;477;465;468;471;519;516;513;510;507;474;504;501;498;495;492;489;486]);
(522,[34;35;36;37;39;355;448;462;156;400;118;372;383;268;209;327;417;431;483;480;477;465;468;519;516;513;510;507;474;504;501;498;495;492;489;486;471;523;524;525;526;527;528;529;530;531;532;533;534;535;536;537;538;539;540;541;542;543;544;545;546;547;548;549;550;551;552;553;554;555;556;557;558;559;560;561;562;563;564;565;566;567;568;569;570;571;573;572]);
(523,[34;35;36;37;39;355;448;462;156;400;118;372;383;268;209;327;417;431;483;480;477;465;468;522;519;516;513;510;507;474;504;501;498;495;492;489;486;471]);
(524,[34;35;36;37;39;355;448;462;156;400;118;372;383;268;209;327;417;431;483;480;477;465;468;522;519;516;513;510;507;474;504;501;498;495;492;489;486;471]);
(525,[34;35;36;37;39;355;448;462;156;400;118;372;383;268;209;327;417;431;483;480;477;465;522;519;516;513;510;507;474;504;501;498;495;492;489;486;471;468;526;527;528;529;530;531;532;533;534;535;536;537;538;539;540;541;542;543;544;545;546;547;548;549;550;551;552;553;554;555;556;557;558;559;560;561;562;563;564;565;566;567;568;569;570;571;573;572]);
(526,[34;35;36;37;39;355;448;462;156;400;118;372;383;268;209;327;417;431;483;480;477;465;525;522;519;516;513;510;507;474;504;501;498;495;492;489;486;471;468]);
(527,[34;35;36;37;39;355;448;462;156;400;118;372;383;268;209;327;417;431;483;480;477;465;525;522;519;516;513;510;507;474;504;501;498;495;492;489;486;471;468]);
(528,[34;35;36;37;39;355;448;462;156;400;118;372;383;268;209;327;417;431;483;480;477;525;522;519;516;513;510;507;474;504;501;498;495;492;489;486;471;468;465;529;530;531;532;533;534;535;536;537;538;539;540;541;542;543;544;545;546;547;548;549;550;551;552;553;554;555;556;557;558;559;560;561;562;563;564;565;566;567;568;569;570;571;573;572]);
(529,[34;35;36;37;39;355;448;462;156;400;118;372;383;268;209;327;417;431;483;480;477;528;525;522;519;516;513;510;507;474;504;501;498;495;492;489;486;471;468;465]);
(530,[34;35;36;37;39;355;448;462;156;400;118;372;383;268;209;327;417;431;483;480;477;528;525;522;519;516;513;510;507;474;504;501;498;495;492;489;486;471;468;465]);
(531,[34;35;36;37;39;355;448;462;156;400;118;372;383;268;209;327;417;431;480;477;528;525;522;519;516;513;510;507;474;504;501;498;495;492;489;486;471;468;465;483;532;533;534;535;536;537;538;539;540;541;542;543;544;545;546;547;548;549;550;551;552;553;554;555;556;557;558;559;560;561;562;563;564;565;566;567;568;569;570;571;573;572]);
(532,[34;35;36;37;39;355;448;462;156;400;118;372;383;268;209;327;417;431;531;480;477;528;525;522;519;516;513;510;507;474;504;501;498;495;492;489;486;471;468;465;483]);
(533,[34;35;36;37;39;355;448;462;156;400;118;372;383;268;209;327;417;431;531;480;477;528;525;522;519;516;513;510;507;474;504;501;498;495;492;489;486;471;468;465;483]);
(534,[34;35;36;37;39;355;448;462;156;400;118;372;383;268;209;327;417;531;480;477;528;525;522;519;516;513;510;507;474;504;501;498;495;492;489;486;471;468;465;483;431;535;536;537;538;539;540;541;542;543;544;545;546;547;548;549;550;551;552;553;554;555;556;557;558;559;560;561;562;563;564;565;566;567;568;569;570;571;573;572]);
(535,[34;35;36;37;39;355;448;462;156;400;118;372;383;268;209;327;417;534;531;480;477;528;525;522;519;516;513;510;507;474;504;501;498;495;492;489;486;471;468;465;483;431]);
(536,[34;35;36;37;39;355;448;462;156;400;118;372;383;268;209;327;417;534;531;480;477;528;525;522;519;516;513;510;507;474;504;501;498;495;492;489;486;471;468;465;483;431]);
(537,[34;35;36;37;39;355;448;462;156;400;118;372;383;268;209;327;534;531;480;477;528;525;522;519;516;513;510;507;474;504;501;498;495;492;489;486;471;468;465;483;431;417;538;539;540;541;542;543;544;545;546;547;548;549;550;551;552;553;554;555;556;557;558;559;560;561;562;563;564;565;566;567;568;569;570;571;573;572]);
(538,[34;35;36;37;39;355;448;462;156;400;118;372;383;268;209;327;537;534;531;480;477;528;525;522;519;516;513;510;507;474;504;501;498;495;492;489;486;471;468;465;483;431;417]);
(539,[34;35;36;37;39;355;448;462;156;400;118;372;383;268;209;327;537;534;531;480;477;528;525;522;519;516;513;510;507;474;504;501;498;495;492;489;486;471;468;465;483;431;417]);
(540,[34;35;36;37;39;355;448;462;156;400;118;372;383;268;209;537;534;531;480;477;528;525;522;519;516;513;510;507;474;504;501;498;495;492;489;486;471;468;465;483;431;417;327;541;542;543;544;545;546;547;548;549;550;551;552;553;554;555;556;557;558;559;560;561;562;563;564;565;566;567;568;569;570;571;573;572]);
(541,[34;35;36;37;39;355;448;462;156;400;118;372;383;268;209;540;537;534;531;480;477;528;525;522;519;516;513;510;507;474;504;501;498;495;492;489;486;471;468;465;483;431;417;327]);
(542,[34;35;36;37;39;355;448;462;156;400;118;372;383;268;209;540;537;534;531;480;477;528;525;522;519;516;513;510;507;474;504;501;498;495;492;489;486;471;468;465;483;431;417;327]);
(543,[34;35;36;37;39;355;448;462;156;400;118;372;383;268;540;537;534;531;480;477;528;525;522;519;516;513;510;507;474;504;501;498;495;492;489;486;471;468;465;483;431;417;327;209;544;545;546;547;548;549;550;551;552;553;554;555;556;557;558;559;560;561;562;563;564;565;566;567;568;569;570;571;573;572]);
(544,[34;35;36;37;39;355;448;462;156;400;118;372;383;268;543;540;537;534;531;480;477;528;525;522;519;516;513;510;507;474;504;501;498;495;492;489;486;471;468;465;483;431;417;327;209]);
(545,[34;35;36;37;39;355;448;462;156;400;118;372;383;268;543;540;537;534;531;480;477;528;525;522;519;516;513;510;507;474;504;501;498;495;492;489;486;471;468;465;483;431;417;327;209]);
(546,[34;35;36;37;39;355;448;462;156;400;118;372;383;543;540;537;534;531;480;477;528;525;522;519;516;513;510;507;474;504;501;498;495;492;489;486;471;468;465;483;431;417;327;209;268;547;548;549;550;551;552;553;554;555;556;557;558;559;560;561;562;563;564;565;566;567;568;569;570;571;573;572]);
(547,[34;35;36;37;39;355;448;462;156;400;118;372;383;546;543;540;537;534;531;480;477;528;525;522;519;516;513;510;507;474;504;501;498;495;492;489;486;471;468;465;483;431;417;327;209;268]);
(548,[34;35;36;37;39;355;448;462;156;400;118;372;383;546;543;540;537;534;531;480;477;528;525;522;519;516;513;510;507;474;504;501;498;495;492;489;486;471;468;465;483;431;417;327;209;268]);
(549,[34;35;36;37;39;355;448;462;156;400;118;372;546;543;540;537;534;531;480;477;528;525;522;519;516;513;510;507;474;504;501;498;495;492;489;486;471;468;465;483;431;417;327;209;268;383;550;551;552;553;554;555;556;557;558;559;560;561;562;563;564;565;566;567;568;569;570;571;573;572]);
(550,[34;35;36;37;39;355;448;462;156;400;118;372;549;546;543;540;537;534;531;480;477;528;525;522;519;516;513;510;507;474;504;501;498;495;492;489;486;471;468;465;483;431;417;327;209;268;383]);
(551,[34;35;36;37;39;355;448;462;156;400;118;372;549;546;543;540;537;534;531;480;477;528;525;522;519;516;513;510;507;474;504;501;498;495;492;489;486;471;468;465;483;431;417;327;209;268;383]);
(552,[34;35;36;37;39;355;448;462;156;400;118;549;546;543;540;537;534;531;480;477;528;525;522;519;516;513;510;507;474;504;501;498;495;492;489;486;471;468;465;483;431;417;327;209;268;383;372;553;554;555;556;557;558;559;560;561;562;563;564;565;566;567;568;569;570;571;573;572]);
(553,[34;35;36;37;39;355;448;462;156;400;118;552;549;546;543;540;537;534;531;480;477;528;525;522;519;516;513;510;507;474;504;501;498;495;492;489;486;471;468;465;483;431;417;327;209;268;383;372]);
(554,[34;35;36;37;39;355;448;462;156;400;118;552;549;546;543;540;537;534;531;480;477;528;525;522;519;516;513;510;507;474;504;501;498;495;492;489;486;471;468;465;483;431;417;327;209;268;383;372]);
(555,[34;35;36;37;39;355;448;462;156;400;552;549;546;543;540;537;534;531;480;477;528;525;522;519;516;513;510;507;474;504;501;498;495;492;489;486;471;468;465;483;431;417;327;209;268;383;372;118;556;557;558;559;560;561;562;563;564;565;566;567;568;569;570;571;573;572]);
(556,[34;35;36;37;39;355;448;462;156;400;555;552;549;546;543;540;537;534;531;480;477;528;525;522;519;516;513;510;507;474;504;501;498;495;492;489;486;471;468;465;483;431;417;327;209;268;383;372;118]);
(557,[34;35;36;37;39;355;448;462;156;400;555;552;549;546;543;540;537;534;531;480;477;528;525;522;519;516;513;510;507;474;504;501;498;495;492;489;486;471;468;465;483;431;417;327;209;268;383;372;118]);
(558,[34;35;36;37;39;355;448;462;156;555;552;549;546;543;540;537;534;531;480;477;528;525;522;519;516;513;510;507;474;504;501;498;495;492;489;486;471;468;465;483;431;417;327;209;268;383;372;118;400;559;560;561;562;563;564;565;566;567;568;569;570;571;573;572]);
(559,[34;35;36;37;39;355;448;462;156;558;555;552;549;546;543;540;537;534;531;480;477;528;525;522;519;516;513;510;507;474;504;501;498;495;492;489;486;471;468;465;483;431;417;327;209;268;383;372;118;400]);
(560,[34;35;36;37;39;355;448;462;156;558;555;552;549;546;543;540;537;534;531;480;477;528;525;522;519;516;513;510;507;474;504;501;498;495;492;489;486;471;468;465;483;431;417;327;209;268;383;372;118;400]);
(561,[34;35;36;37;39;355;448;462;558;555;552;549;546;543;540;537;534;531;480;477;528;525;522;519;516;513;510;507;474;504;501;498;495;492;489;486;471;468;465;483;431;417;327;209;268;383;372;118;400;156;562;563;564;565;566;567;568;569;570;571;573;572]);
(562,[34;35;36;37;39;355;448;462;561;558;555;552;549;546;543;540;537;534;531;480;477;528;525;522;519;516;513;510;507;474;504;501;498;495;492;489;486;471;468;465;483;431;417;327;209;268;383;372;118;400;156]);
(563,[34;35;36;37;39;355;448;462;561;558;555;552;549;546;543;540;537;534;531;480;477;528;525;522;519;516;513;510;507;474;504;501;498;495;492;489;486;471;468;465;483;431;417;327;209;268;383;372;118;400;156]);
(564,[34;35;36;37;39;355;448;561;558;555;552;549;546;543;540;537;534;531;480;477;528;525;522;519;516;513;510;507;474;504;501;498;495;492;489;486;471;468;465;483;431;417;327;209;268;383;372;118;400;156;462;565;566;567;568;569;570;571;573;572]);
(565,[34;35;36;37;39;355;448;564;561;558;555;552;549;546;543;540;537;534;531;480;477;528;525;522;519;516;513;510;507;474;504;501;498;495;492;489;486;471;468;465;483;431;417;327;209;268;383;372;118;400;156;462]);
(566,[34;35;36;37;39;355;448;564;561;558;555;552;549;546;543;540;537;534;531;480;477;528;525;522;519;516;513;510;507;474;504;501;498;495;492;489;486;471;468;465;483;431;417;327;209;268;383;372;118;400;156;462]);
(567,[34;35;36;37;39;355;564;561;558;555;552;549;546;543;540;537;534;531;480;477;528;525;522;519;516;513;510;507;474;504;501;498;495;492;489;486;471;468;465;483;431;417;327;209;268;383;372;118;400;156;462;448;568;569;570;571;573;572]);
(568,[34;35;36;37;39;355;567;564;561;558;555;552;549;546;543;540;537;534;531;480;477;528;525;522;519;516;513;510;507;474;504;501;498;495;492;489;486;471;468;465;483;431;417;327;209;268;383;372;118;400;156;462;448]);
(569,[34;35;36;37;39;355;567;564;561;558;555;552;549;546;543;540;537;534;531;480;477;528;525;522;519;516;513;510;507;474;504;501;498;495;492;489;486;471;468;465;483;431;417;327;209;268;383;372;118;400;156;462;448]);
(570,[34;35;36;37;39;567;564;561;558;555;552;549;546;543;540;537;534;531;480;477;528;525;522;519;516;513;510;507;474;504;501;498;495;492;489;486;471;468;465;483;431;417;327;209;268;383;372;118;400;156;462;448;355;571;573;572]);
(571,[34;35;36;37;39;570;567;564;561;558;555;552;549;546;543;540;537;534;531;480;477;528;525;522;519;516;513;510;507;474;504;501;498;495;492;489;486;471;468;465;483;431;417;327;209;268;383;372;118;400;156;462;448;355]);
(572,[34;35;36;37;39;570;567;564;561;558;555;552;549;546;543;540;537;534;531;480;477;528;525;522;519;516;513;510;507;474;504;501;498;495;492;489;486;471]);
(573,[34;35;36;37;39;570;567;564;561;558;555;552;549;546;543;540;537;534;531;480;477;528;525;522;519;516;513;510;507;474;504;501;498;495;492;489;486;471]);
(574,[34;35;36;37;39;575;577;576]);
(575,[34;35;36;37;574;39]);
(576,[34;35;36;37;574]);
(577,[34;35;36;37;574]);
(578,[34;35;36;37]);
(579,[35;36;37;34;1;6;7;8])
])%Z.

(* Time Compute (run graph40). *)
Definition main := run G16.


(* Extraction "color.ml" main. *)
(* Some code in ocaml to time this test case:
  let timeit() = let t = Sys.time() in let r = run graph40 in (Sys.time()-.t, r);;
 On my machine, vm_compute takes 2.171 seconds, ocaml takes 1.453 seconds.
  -- Andrew Appel, September 16, 2016.
*)
