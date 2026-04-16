(* NOTE: This program is NOT open-source, and is NOT licensed for
 * redistribution.  It is copyright by the authors.  Permission is
 * granted only to the CertiCoq project for the use of this program
 * as a benchmark in measuring CertiCoq performance. *)

(************************************************************************************)
(**                                                                                  *)
(**                              The DataCert Library                                *)
(**                                                                                  *)
(**                           LRI, CNRS & Université Paris-Sud                       *)
(**                                                                                  *)
(**                 Copyright 2016 : Véronique Benzaken & Évelyne Contejean          *)
(**                                                                                  *)
(************************************************************************************)

Set Implicit Arguments.

(** printing inS? $\in_?$ #∈<SUB>?</SUB># *)
(** printing inS $\in$ #∈# *)
(** printing subS? $\subseteq_?$ #⊆<SUB>?</SUB># *)
(** printing subS $\subseteq$ #⊆# *)
(** printing unionS $\cup$ #⋃# *)
(** printing interS $\cap$ #⋂# *)
(** printing inI $\in_I$ #∈<SUB><I>I</I></SUB># *)
(** printing theta $\theta$ #θ# *)
(** printing nu1 $\nu_1$ #ν<SUB><I>1</I></SUB># *)
(** printing nu $\nu$ #ν# *)
(** printing mu $\mu$ #μ# *)
(** printing sigma $\sigma$ #σ# *)
(** printing -> #⟶# *)
(** printing <-> #⟷# *)
(** printing => #⟹# *)
(** printing (emptysetS) $\emptyset$ #Ø# *)
(** printing emptysetS $\emptyset$ #Ø# *)
(** printing {{ $\{$ #{# *)
(** printing }} $\}$ #}# *)

Require Import Relations SetoidList List String Ascii Bool ZArith NArith.

Require Import FlatData ListFacts OrderedSet FiniteSet Tree Formula Sql.


Section Try.
Import Tuple Expression.
Require Import Values Relnames SortedAttributes SortedTuples.

(** Defining functions and aggregates, and giving their interpretation *)

Inductive symbol : Type :=
  | Symbol : string -> symbol
  | CstVal : value -> symbol.

Inductive predicate : Type := Predicate : string -> predicate.

Definition OP : Oset.Rcd predicate.
split with (fun x y => match x, y with Predicate s1, Predicate s2 => string_compare s1 s2 end).
- intros [s1] [s2]; generalize (Oset.eq_bool_ok Ostring s1 s2); simpl.
  case (string_compare s1 s2).
  + apply f_equal.
  + intros H1 H2; apply H1; injection H2; exact (fun h => h).
  + intros H1 H2; apply H1; injection H2; exact (fun h => h).
- intros [s1] [s2] [s3]; apply (Oset.compare_lt_trans Ostring s1 s2 s3).
- intros [s1] [s2]; apply (Oset.compare_lt_gt Ostring s1 s2).
Defined.

Definition symbol_compare (s1 s2 : symbol) :=
  match s1, s2 with
    | Symbol s1, Symbol s2 => string_compare s1 s2
    | Symbol _, CstVal _ => Lt
    | CstVal _, Symbol _ => Gt
    | CstVal v1, CstVal v2 => value_compare v1 v2
  end.

Definition OSymbol : Oset.Rcd symbol.
split with symbol_compare.
- intros [s1 | s1] [s2 | s2]; simpl; try discriminate.
  + generalize (Oset.eq_bool_ok Ostring s1 s2); simpl.
    case (string_compare s1 s2).
    * apply f_equal.
    * intros H1 H2; apply H1; injection H2; exact (fun h => h).
    * intros H1 H2; apply H1; injection H2; exact (fun h => h).
  + generalize (Oset.eq_bool_ok OVal s1 s2); simpl.
    case (value_compare s1 s2).
    * apply f_equal.
    * intros H1 H2; apply H1; injection H2; exact (fun h => h).
    * intros H1 H2; apply H1; injection H2; exact (fun h => h).
- intros [s1 | s1] [s2 | s2] [s3 | s3]; simpl;
  try (apply (Oset.compare_lt_trans Ostring) ||
             apply (Oset.compare_lt_trans OVal) ||
             trivial || discriminate).
- intros [s1 | s1] [s2 | s2]; simpl;
  try (apply (Oset.compare_lt_gt Ostring) ||
             apply (Oset.compare_lt_gt OVal) ||
             trivial || discriminate).
Defined.

Definition interp_symbol f :=
  match f with
    | Symbol "plus" =>
      fun l =>
        match l with
          | Value_N a1 :: Value_N a2 :: nil => Value_N (Nplus a1 a2)
          | _ => Value_N 0 end
    | Symbol "mult" =>
      fun l =>
        match l with
          | Value_N a1 :: Value_N a2 :: nil => Value_N (Nmult a1 a2)
          | _ => Value_N 0 end
    | Symbol "minus" =>
      fun l =>
        match l with
          | Value_N a1 :: Value_N a2 :: nil => Value_N (Nminus a1 a2)
          | _ => Value_N 0 end
    | Symbol "opp" =>
      fun l =>
        match l with
          | Value_N a1 :: nil => Value_N (Nopp a1)
          | _ => Value_N 0 end
    | CstVal v =>
      fun l =>
        match l with
          | nil => v
          | _ => default_value (type_of_value v)
        end
    | _ => fun _ => Value_N 0
  end.

Definition interp_predicate p :=
  match p with
    | Predicate "<" =>
      fun l =>
        match l with
          | Value_N a1 :: Value_N a2 :: nil =>
            match Ncompare a1 a2 with Lt => true | _ => false end
          | _ => false
        end
    | Predicate "<=" =>
      fun l =>
        match l with
          | Value_N a1 :: Value_N a2 :: nil =>
            match Ncompare a1 a2 with Gt => false | _ => true end
          | _ => false
        end
    | Predicate ">" =>
      fun l =>
        match l with
          | Value_N a1 :: Value_N a2 :: nil =>
            match Ncompare a1 a2 with Gt => true | _ => false end
          | _ => false
        end
    | Predicate ">=" =>
      fun l =>
        match l with
          | Value_N a1 :: Value_N a2 :: nil =>
            match Ncompare a1 a2 with Lt => false | _ => true end
          | _ => false
        end
    | Predicate "=" =>
      fun l =>
        match l with
          | Value_N a1 :: Value_N a2 :: nil =>
            match Ncompare a1 a2 with Eq => true | _ => false end
          | Value_string s1 :: Value_string s2 :: nil =>
            match string_compare s1 s2 with Eq => true | _ => false end
          | _ => false
        end
   | _ => fun _ => false
  end.

Inductive aggregate : Type :=
  | Aggregate : string -> aggregate.

Definition OAgg : Oset.Rcd aggregate.
split with (fun x y => match x, y with Aggregate s1, Aggregate s2 => string_compare s1 s2 end).
- intros [s1] [s2]; generalize (Oset.eq_bool_ok Ostring s1 s2); simpl.
  case (string_compare s1 s2).
  + apply f_equal.
  + intros H1 H2; apply H1; injection H2; exact (fun h => h).
  + intros H1 H2; apply H1; injection H2; exact (fun h => h).
- intros [s1] [s2] [s3]; apply (Oset.compare_lt_trans Ostring s1 s2 s3).
- intros [s1] [s2]; apply (Oset.compare_lt_gt Ostring s1 s2).
Defined.

Definition interp_aggregate a :=
  match a with
    | Aggregate "count" =>
      fun (l : list (Tuple.value T)) => Value_N (N_of_nat (List.length l))
    | Aggregate "sum" =>
      fun (l : list (Tuple.value T)) =>
           Value_N (fold_left (fun acc x => match x with Value_N x => (acc + x)%N | _ => acc end) l 0%N)
    | Aggregate "avg" =>
      fun (l : list (Tuple.value T)) =>
           Value_N (let sum := fold_left (fun acc x => match x with Value_N x => (acc + x)%N | _ => acc end) l 0%N in Ndiv sum (N_of_nat (List.length l)))
    | Aggregate _ => fun _ => Value_N 0
  end.

(** Building a database instance, and updating it  *)
Definition mk_tuple la f := mk_tuple T (mk_set FAN la) f.

Definition show_tuple t :=
  List.map
    (fun a => (a, dot T t a))
    (Fset.elements _ (support _ t)).

Definition show_tuples x :=
  List.map show_tuple (Feset.elements (FTuple T) x).

Record db_state : Type :=
  mk_state
    {
      _relnames : list relname;
      _basesort : relname -> Fset.set FAN;
      _instance : relname -> Feset.set (FTuple T)
    }.

Definition show_state (db : db_state) :=
  (_relnames db,
   List.map (fun r => (r, Fset.elements _ (_basesort db r))) (_relnames db),
   List.map (fun r => (r, show_tuples (_instance db r))) (_relnames db)).

Definition init_db :=
  mk_state
    nil
    (fun _ => Fset.empty FAN)
    (fun _ => Feset.empty (FTuple T)).

Definition create_table
           (* old state *) db
           (* new table name *) t
           (* new table sort *) st
            :=
  mk_state
    (t :: _relnames db)
    (fun x =>
       match Oset.compare ORN x t with
         | Eq => mk_set FAN st
         |_ => _basesort db x
       end)
    (_instance db).

Definition insert_tuple_into
           (* old state *) db
           (* new tuple *) tpl
           (* table *) tbl
            :=
  if Fset.equal FAN (support T tpl) (_basesort db tbl)
  then
    mk_state
      (_relnames db)
      (_basesort db)
      (fun x =>
         match Oset.compare ORN x tbl with
           | Eq => Feset.add (FTuple T) tpl (_instance db tbl)
           |_ => _instance db x
         end)
   else (* no NULL values by default *) db.

Fixpoint insert_tuples_into
           (* old state *) db
           (* new tuple list *) ltpl
           (* table *) tbl :=
  match ltpl with
    | nil => db
    | t :: l => insert_tuple_into (insert_tuples_into db l tbl) t tbl
  end.

Definition MyDBS db := DatabaseSchema.mk_R (Tuple.A T) ORN (_basesort db).

(** Evaluation of SQL-COQ queries *)

Definition eval_sql_query_in_state (db : db_state) q :=
  eval_sql_query
    (DBS := MyDBS db) interp_predicate interp_symbol interp_aggregate (_instance db) q.

(** Some notations, to ease the readability *)
Notation aa := (Attr_N 0 "a").
Notation bb := (Attr_N 0 "b").
Notation cc := (Attr_N 0 "c").
Notation ac := (Attr_N 0 "ac").
Notation cb := (Attr_N 0 "cb").
Notation b_plus_c := (Attr_N 0 "b_plus_c").
Notation a := (Attr_N 0 "a").
Notation b := (Attr_N 0 "b").
Notation c := (Attr_N 0 "c").
Notation a1 := (Attr_N 0 "a1").
Notation b1 := (Attr_N 0 "b1").
Notation c1 := (Attr_N 0 "c1").
Notation a0 := (Attr_N 0 "a0").
Notation b0 := (Attr_N 0 "b0").
Notation c0 := (Attr_N 0 "c0").
Notation a2 := (Attr_N 0 "a2").
Notation b2 := (Attr_N 0 "b2").
Notation c2 := (Attr_N 0 "c2").
Notation a3 := (Attr_N 0 "a3").
Notation b3 := (Attr_N 0 "b3").
Notation c3 := (Attr_N 0 "c3").
Notation a4 := (Attr_N 0 "a4").
Notation b4 := (Attr_N 0 "b4").
Notation c4 := (Attr_N 0 "c4").

Notation table0 :=  (Rel "table0").
Notation t0 :=  (Rel "t0").
Notation table1 :=  (Rel "table1").
Notation t1 :=  (Rel "t1").
Notation table2 :=  (Rel "table2").
Notation t2 :=  (Rel "t2").
Notation table3 :=  (Rel "table3").
Notation t3 :=  (Rel "t3").

(** Again, for the constructs of the SQL framework *)
Definition _Select_Star := (@Select_Star symbol aggregate T).

Definition _Select_List := (@Select_List symbol aggregate T).

Definition _Select_As := (@Select_As symbol aggregate T).

Definition _Att_Ren_Star := (@Att_Ren_Star T).

Definition _Att_Ren_List := (@Att_Ren_List T).

Definition _Att_As := (@Att_As T).

Definition _Sql_Table db := (@Sql_Table predicate symbol aggregate T (MyDBS db)).

Definition _Sql_Select db := @Sql_Select predicate symbol aggregate T (MyDBS db).

Definition _From_Item db := (@From_Item predicate symbol aggregate T (MyDBS db)).

Definition _Sql_Atom db := (@Sql_Atom predicate symbol aggregate T (MyDBS db)).

Definition _Sql_True db := (@Sql_True predicate symbol aggregate T (MyDBS db)).

Definition _Sql_Not db := (@Sql_Not predicate symbol aggregate T (MyDBS db)).

Definition _Sql_Conj db := (@Sql_Conj predicate symbol aggregate T (MyDBS db)).

Definition _Group_Fine := (@Group_Fine symbol T).

Definition __Sql_Dot a := (@F_Dot T symbol a).

Definition _Sql_Dot a := (@A_Expr T _ aggregate (@F_Dot T symbol a)).

Definition _Sql_Pred db := (@Sql_Pred predicate symbol aggregate T (MyDBS db)).

Definition _Sql_In db := (@Sql_In predicate symbol aggregate T (MyDBS db)).

Definition _Sql_Quant db := (@Sql_Quant predicate symbol aggregate T (MyDBS db)).

Definition _A_Expr := (@A_Expr T symbol aggregate).

Definition _F_Expr := (@F_Expr T symbol).

Definition _CstN n := (F_Constant T symbol (Value_N n)).

Definition CstN n := (_A_Expr (F_Constant T symbol (Value_N n))).

Definition t123 :=
  mk_tuple
    (aa :: bb :: cc :: nil)
    (fun x => match x with
                | aa => Value_N 1
                | bb => Value_N 2
                | cc => Value_N 3
                | _ => Value_N 0 end).

Definition t456 := mk_tuple
        (aa :: bb :: cc :: nil)
        (fun x => match x with
                    | aa => Value_N 4
                    | bb => Value_N 5
                    | cc => Value_N 6
                    | _ => Value_N 0 end).

Definition t778 := mk_tuple
        (aa :: bb :: cc :: nil)
        (fun x => match x with
                    | aa => Value_N 7
                    | bb => Value_N 7
                    | cc => Value_N 8
                    | _ => Value_N 0 end).

Definition t779 := mk_tuple
        (aa :: bb :: cc :: nil)
        (fun x => match x with
                    | aa => Value_N 7
                    | bb => Value_N 7
                    | cc => Value_N 9
                    | _ => Value_N 0 end).

Definition db0 := init_db.

(**
create table table1(a integer, b integer, c integer);
*)

Definition db1 :=
  create_table
    (create_table db0 table0 (aa :: bb :: cc :: nil))
    table1 (aa :: bb :: cc :: nil).

(**
insert into table1 values (1,2,3);
insert into table1 values (4,5,6);
*)
Definition db2 := insert_tuples_into db1 (t123 :: t456 :: nil) table1.

Definition db3 := insert_tuples_into db2 (t778 :: t779 :: nil) table1.

(**
insert into table1 values (4,5);
*)

Definition db4 :=
  insert_tuple_into
    db3
    (mk_tuple
        (aa :: bb :: nil)
        (fun x => match x with
                    | aa => Value_N 4
                    | bb => Value_N 5
                    | _ => Value_N 0 end))
    table1.

(** select t5.a2 as a3 from table5 as t5(a2) *)

Definition eval_sql0 :=
  let a1 := Attr_N 0 "a1" in
  let a2 := Attr_N 0 "a2" in
  let a3 := Attr_N 0 "a3" in
  let table5 := Rel "table5" in
  let tpl n :=
      mk_tuple
        (a1 :: nil)
        (fun x => match x with a1 => Value_N n | _ => Value_N 0 end) in
  let db1 :=
      insert_tuples_into
        (create_table db0 table5 (a1 :: nil))
        (tpl 1 :: tpl 2 :: tpl 3 :: nil)
        table5 in
  let sql0 db :=
  _Sql_Select
        (* select *) (_Select_List ((_Select_As (_Sql_Dot a2) a3) :: nil))
        (* from *) ((_From_Item
                       (_Sql_Table table5)
                       (Att_Ren_List ((Att_As T a1 a2) :: nil))) :: nil)
        (* where *) (_Sql_Atom (_Sql_True db))
        (* groupby *) (_Group_Fine)
        (* having *) (_Sql_Atom (_Sql_True db)) in

  eval_sql_query_in_state (sql0 db1).

Eval compute in (show_tuples eval_sql0).

(** select * from table1; *)

Definition sql1 db :=
  _Sql_Select
    (* select *) _Select_Star
    (* from *) ((_From_Item (_Sql_Table table1) _Att_Ren_Star) :: nil)
    (* where *) (_Sql_Atom (_Sql_True db))
    (* groupby *) _Group_Fine
    (* having *) (_Sql_Atom (_Sql_True db)).

Definition eval_sql1 := eval_sql_query_in_state (sql1 db2).

Eval compute in (show_tuples eval_sql1).

(** select * from table1 where aa = bb *)
Definition sql2 db :=
  _Sql_Select
    (* select *) _Select_Star
    (* from *) ((_From_Item (_Sql_Table table1) _Att_Ren_Star) :: nil)
    (* where *) (_Sql_Atom (_Sql_Pred db (Predicate "=") (_Sql_Dot aa :: _Sql_Dot bb :: nil)))
    (* groupby *) _Group_Fine
    (* having *) (_Sql_Atom (_Sql_True db)).

Definition eval_sql2 := eval_sql_query_in_state (sql2 db2).
Eval compute in (show_tuples eval_sql2).

(** Evalution of the same query in different states (that is instances) of the database *)
Definition eval_sql2' := eval_sql_query_in_state (sql2 db3).
Eval compute in (show_tuples eval_sql2').

Definition eval_sql1' := eval_sql_query_in_state (sql1 db3).
Eval compute in (show_tuples eval_sql1').

Definition eval_sql1'' := eval_sql_query_in_state (sql1 db4).
Eval compute in (show_tuples eval_sql1'').

(** (4,5) has not been inserted in db4, as specified by insert_tuple.
 We COULD have made another choice, and null values in that case would correspond
 to an attribute which occurs in the sort of the query, but not in the support
 of the tuple.*)

(** SELECT a, b FROM table1; *)

Definition sql5 db :=
  _Sql_Select
    (* select *) (_Select_List
                    ((_Select_As (_Sql_Dot aa) aa) ::
                     (_Select_As (_Sql_Dot bb) bb ) :: nil))
    (* from *) ((_From_Item (_Sql_Table table1) _Att_Ren_Star) :: nil)
    (* where *) (_Sql_Atom (_Sql_True db))
    (* groupby *) _Group_Fine
    (* having *) (_Sql_Atom (_Sql_True db)).

Definition eval_sql5 := eval_sql_query_in_state (sql5 db4).
Eval vm_compute in (show_tuples eval_sql5).

(** SELECT a, b + c FROM table1; actully, we use
   SELECT a, b + c AS bplusc FROM table1; *)
Definition sql6 db :=
  _Sql_Select
    (* select *) (_Select_List
                    ((_Select_As (_Sql_Dot aa) aa) ::
                     (_Select_As
                        (_A_Expr ((_F_Expr (Symbol "plus")) ((__Sql_Dot bb) :: (__Sql_Dot cc) :: nil)))
                          b_plus_c ) :: nil))
    (* from *) ((_From_Item (_Sql_Table table1) _Att_Ren_Star) :: nil)
    (* where *) (_Sql_Atom (_Sql_True db))
    (* groupby *) _Group_Fine
    (* having *) (_Sql_Atom (_Sql_True db)).

Definition eval_sql6 := eval_sql_query_in_state (sql6 db4).
Eval compute in (show_tuples eval_sql6).

(** explicit renaming of attributes
      select * from table1 as t1(a1 , b1 , c1 ); *)

Definition sql7 db :=
  _Sql_Select
    (* select *) _Select_Star
    (* from *) ((_From_Item
                   (_Sql_Table table1)
                   (_Att_Ren_List
                      (_Att_As aa a1 ::
                       _Att_As bb b1 ::
                       _Att_As cc c1 :: nil))) :: nil)
    (* where *) (_Sql_Atom (_Sql_True db))
    (* groupby *) _Group_Fine
    (* having *) (_Sql_Atom (_Sql_True db)).

Definition eval_sql7 := eval_sql_query_in_state (sql7 db4).
Eval vm_compute in (show_tuples eval_sql7).

(** select * from table1 as t1 where t1.a < 4*)
Definition sql8 db :=
  _Sql_Select
    (* select *) _Select_Star
    (* from *) ((_From_Item (_Sql_Table table1) _Att_Ren_Star) :: nil)
    (* where *) (_Sql_Atom
                   (_Sql_Pred db (Predicate "<")
                              (_Sql_Dot aa :: CstN 4 :: nil)))
    (* groupby *) _Group_Fine
    (* having *) (_Sql_Atom (_Sql_True db)).

Definition eval_sql8 := eval_sql_query_in_state (sql8 db4).
Eval vm_compute in (show_tuples eval_sql8).

(** select * from table1 as t1 where t1.a > 4*)

Definition sql9 db :=
  _Sql_Select
    (* select *) _Select_Star
    (* from *) ((_From_Item (_Sql_Table table1) _Att_Ren_Star) :: nil)
    (* where *) (_Sql_Atom
                   (_Sql_Pred db (Predicate ">")
                              (_Sql_Dot aa :: CstN 4 :: nil)))
    (* groupby *) _Group_Fine
    (* having *) (_Sql_Atom (_Sql_True db)).

Definition eval_sql9 := eval_sql_query_in_state (sql9 db4).
Eval vm_compute in (show_tuples eval_sql9).

(** select * from table1 as t1 where t1.a = 4*)
Definition sql10 db :=
  _Sql_Select
    (* select *) _Select_Star
    (* from *) ((_From_Item (_Sql_Table table1) _Att_Ren_Star) :: nil)
    (* where *) (_Sql_Atom
                   (_Sql_Pred db (Predicate "=")
                              (_Sql_Dot aa :: CstN 4 :: nil)))
    (* groupby *) _Group_Fine
    (* having *) (_Sql_Atom (_Sql_True db)).

Definition eval_sql10 := eval_sql_query_in_state (sql10 db4).
Eval vm_compute in (show_tuples eval_sql10).

(** select * from table1 as t1 where t1.a <> 4*)

Definition sql11 db :=
  _Sql_Select
    (* select *) _Select_Star
    (* from *) ((_From_Item (_Sql_Table table1) _Att_Ren_Star) :: nil)
    (* where *) (_Sql_Not
                   (_Sql_Atom
                   (_Sql_Pred db (Predicate "=")
                              (_Sql_Dot aa :: CstN 4 :: nil))))
    (* groupby *) _Group_Fine
    (* having *) (_Sql_Atom (_Sql_True db)).

Definition eval_sql11 := eval_sql_query_in_state (sql11 db4).
Eval vm_compute in (show_tuples eval_sql11).


(** select * from table1 as t1 where t1.a < 4 or t1.a >= 7*)
Definition sql12 db :=
  _Sql_Select
    (* select *) _Select_Star
    (* from *) ((_From_Item (_Sql_Table table1) _Att_Ren_Star) :: nil)
    (* where *) (_Sql_Conj Or_F
                   (_Sql_Atom
                   (_Sql_Pred db (Predicate "<")
                              (_Sql_Dot aa :: CstN 4 :: nil)))
                   (_Sql_Atom
                   (_Sql_Pred db (Predicate ">=")
                              (_Sql_Dot aa :: CstN 7 :: nil))))
    (* groupby *) _Group_Fine
    (* having *) (_Sql_Atom (_Sql_True db)).

Definition eval_sql12 := eval_sql_query_in_state (sql12 db4).
Eval vm_compute in (show_tuples eval_sql12).

(** select * from table1 where 2 * a < 12 *)
Definition sql13 db :=
  _Sql_Select
    (* select *) _Select_Star
    (* from *) ((_From_Item (_Sql_Table table1) _Att_Ren_Star) :: nil)
    (* where *) (_Sql_Atom
                   (_Sql_Pred db (Predicate "<")
                              (_A_Expr (((_F_Expr (Symbol "mult"))
                                     (_CstN 2 :: __Sql_Dot aa :: nil))) ::
                              (CstN 12) :: nil)))
    (* groupby *) _Group_Fine
    (* having *) (_Sql_Atom (_Sql_True db)).

Definition eval_sql13 := eval_sql_query_in_state (sql13 db4).

Eval vm_compute in (show_tuples eval_sql13).

Notation a_plus_b :=
  (_A_Expr ((_F_Expr (Symbol "plus")) ((__Sql_Dot a) :: (__Sql_Dot b) :: nil))).

Notation a0_plus_c1 :=
  (_A_Expr ((_F_Expr (Symbol "plus")) ((__Sql_Dot a0) :: (__Sql_Dot c1) :: nil))).

Notation rho0 := (Att_Ren_List ((Att_As T a a0) :: (Att_As T b b0) ::  (Att_As T c c0) ::  nil)).
Notation rho1 := (Att_Ren_List ((Att_As T a a1) :: (Att_As T b b1) ::  (Att_As T c c1) ::  nil)).

(** select * from from tbl1[[*]] where (a+b) >= all (select (a0 + c1) as a0_plus_c1 from tbl0[[rho0]], tbl1[[rho1]]) *)
Definition sql17 db :=
  _Sql_Select
    (* select *) _Select_Star
    (* from *) ((_From_Item (_Sql_Table table1) _Att_Ren_Star) :: nil)
    (* where *) (_Sql_Atom
                   (_Sql_Quant
                      Forall_F (db := db)
                      (Predicate ">=") (a_plus_b :: nil)
                      (_Sql_Select
                         (_Select_List (_Select_As a0_plus_c1 (Attr_N 0 "a0_plus_c1") :: nil))
                         (_From_Item (_Sql_Table table0) rho0 ::
                                     _From_Item  (_Sql_Table table1) rho1 :: nil)
                         (_Sql_Atom (_Sql_True db))
                         _Group_Fine
                         (_Sql_Atom (_Sql_True db)))))
    (* groupby *) _Group_Fine
    (* having *) (_Sql_Atom (_Sql_True db)).


End Try.
