(*
  Proof of correctness of the Clight code generation phase of CertiRocq

  > Relates values to location in memory (syntactic)
  > Relates expression to statements (syntactic)
  > Relates Codegen values (header, payload) to Codegen values after GC (syntactic, up to non-function pointer location)
  > Relates LambdaANF states to Codegen states according to execution semantics



TODO: bundle the notation in LambdaANF_to_Clight and import it instead of redefining it

Done: change LambdaANF_to_Clight's fn_vars into fn_temps
Done: change LambdaANF_to_Clight's reserve into reserve', todo update proof with new order
Done: update proof to 64 bits (parametric over Archi.ptr64)
 *)

Require Import LambdaANF.term LambdaANF.eval LambdaANF.term_util LambdaANF.List_util LambdaANF.Ensembles_util LambdaANF.identifiers LambdaANF.tactics LambdaANF.shrink_cps_corresp.



(* Require Import RamifyCoq.CertiGC.GCGraph. *)



From Stdlib Require Import Arith.Arith NArith.BinNat
Require Import ExtLib.Data.String ExtLib.Data.List
From Stdlib Require Import micromega.Lia Program.Program micromega.Psatz Sets.Ensembles Logic.Decidable Lists.ListDec Relations.Relations.

Require Import compcert.common.AST
        compcert.common.Errors
        compcert.lib.Integers
        compcert.cfrontend.Cop
        compcert.cfrontend.Ctypes
        compcert.cfrontend.Clight
        compcert.common.Values
        compcert.common.Globalenvs
        compcert.common.Memory.

Require Import Codegen.tactics
               Codegen.LambdaANF_to_Clight.

Require Import Libraries.maps_util.


(* Space guarantied by the GC on return *)
Definition gc_size:Z := Z.shiftl 1%Z 16%Z.

Definition loc:Type := block * ptrofs.


Notation intTy := (Tint I32 Signed
                        {| attr_volatile := false; attr_alignas := None |}).

Notation uintTy := (Tint I32 Unsigned
                         {| attr_volatile := false; attr_alignas := None |}).

Notation longTy := (Tlong Signed
                        {| attr_volatile := false; attr_alignas := None |}).

Notation ulongTy := (Tlong Unsigned
                           {| attr_volatile := false; attr_alignas := None |}).
Notation boolTy := (Tint IBool Unsigned noattr).


 (* 64-bit

Definition int_chunk := if Archi.ptr64 then Mint64 else Mint32.
Definition val := if Archi.ptr64 then ulongTy else uintTy. (* NOTE: in Clight, SIZEOF_PTR == SIZEOF_INT *)
Definition uval := if Archi.ptr64 then ulongTy else uintTy.
Definition sval := if Archi.ptr64 then longTy else intTy.
Definition val_typ := if Archi.ptr64 then  (AST.Tlong:typ) else (Tany32:typ).
Definition Init_int x := if Archi.ptr64 then (Init_int64 (Int64.repr x)) else (Init_int32 (Int.repr x)).
Definition make_vint z := if Archi.ptr64 then Vlong (Int64.repr z) else Vint (Int.repr z).
Definition make_cint z t := if Archi.ptr64 then Econst_long (Int64.repr z) t else (Econst_int (Int.repr z) t).
Transparent val.
Transparent uval.
Transparent val_typ.
Transparent Init_int.
Transparent make_vint.
Transparent make_cint.
  *)







Definition int_size := (size_chunk int_chunk).
Definition max_args :=   1024%Z. (* limited by space in boxed header *)

Theorem int_size_pos:
  (0 <= size_chunk int_chunk)%Z.
Proof.
  apply Z.lt_le_incl. apply Z.gt_lt.   apply size_chunk_pos.
Qed.


Definition uint_range : Z -> Prop :=
  fun i => (0 <= i <=   Ptrofs.max_unsigned)%Z.
Transparent uint_range.

Theorem uint_range_unsigned:
  forall i,
    uint_range (Ptrofs.unsigned i).
Proof.
  apply Ptrofs.unsigned_range_2.
Qed.

Ltac int_red := unfold int_size in *; simpl size_chunk in *.

Ltac chunk_red := unfold int_size in *; unfold int_chunk in *; destruct Archi.ptr64 eqn:Harchi; simpl size_chunk in *.

Ltac uomega := (unfold int_size; simpl size_chunk; omega).

Definition uint_range_l: list Z -> Prop :=
  fun l => Forall uint_range l.


Theorem ptrofs_mu_weak:
  (Int.max_unsigned <= Ptrofs.max_unsigned)%Z.
Proof.
  unfold Int.max_unsigned.
  unfold Ptrofs.max_unsigned.

  destruct (Archi.ptr64) eqn:Harchi.

  rewrite Ptrofs.modulus_eq64 by auto. unfold Int.modulus. unfold Int64.modulus. simpl. omega.
  rewrite Ptrofs.modulus_eq32 by auto. reflexivity.
Qed.

Theorem ptrofs_ms:
(Ptrofs.max_signed = if Archi.ptr64 then Int64.max_signed else Int.max_signed )%Z.
Proof.
  unfold Int.max_signed.
  unfold Ptrofs.max_signed.
  unfold Ptrofs.half_modulus.
  destruct (Archi.ptr64) eqn:Harchi.
  rewrite Ptrofs.modulus_eq64 by auto; reflexivity.
  rewrite Ptrofs.modulus_eq32 by auto; reflexivity.
Qed.


Theorem ptrofs_mu:
  (Ptrofs.max_unsigned = if Archi.ptr64 then Int64.max_unsigned else Int.max_unsigned )%Z.
Proof.
  unfold Int.max_unsigned.
  unfold Ptrofs.max_unsigned.

  destruct (Archi.ptr64) eqn:Harchi.
  rewrite Ptrofs.modulus_eq64 by auto; reflexivity.
  rewrite Ptrofs.modulus_eq32 by auto; reflexivity.
Qed.

Ltac uint_range_ptrofs :=
  unfold uint_range_l; unfold uint_range; rewrite ptrofs_mu.

Ltac solve_uint_range:=
  unfold Int64.max_unsigned in *; unfold Int64.modulus in *; unfold Int.max_unsigned in *; unfold Int.modulus in *;  simpl in *; (match goal with
          | [H:uint_range _ |- _] => unfold uint_range in H; rewrite ptrofs_mu in H; solve_uint_range
          | [H:uint_range_l _ |- _] => unfold uint_range_l in H;  solve_uint_range
          | [H: Forall uint_range _ |- _] => inv H; solve_uint_range
          | [|- uint_range _] => unfold uint_range; unfold Int.max_unsigned; unfold Int.modulus; simpl; try omega
          | [|- uint_range (Ptrofs.unsigned _)] => apply uint_range_unsigned
          | [|- uint_range (Int.unsigned _)] => apply uint_range_unsigned
          | [|- uint_range_l _] => unfold uint_range_l; solve_uint_range
          | [ |- Forall uint_range _] => constructor; solve_uint_range
          | _ => auto
          end).



Theorem int_z_mul :
  forall i y,
    uint_range_l [i; y] ->
  Ptrofs.mul (Ptrofs.repr i) (Ptrofs.repr y) = Ptrofs.repr (i * y)%Z.
Proof.
  intros.
  unfold Ptrofs.mul.
  rewrite Ptrofs.unsigned_repr.
  rewrite Ptrofs.unsigned_repr. reflexivity.
  inv H. inv H3; auto.
  inv H; auto.
Qed.


Theorem int_z_add:
  forall i y,
    uint_range_l [i; y] ->
    Ptrofs.add (Ptrofs.repr i) (Ptrofs.repr y) = Ptrofs.repr (i + y)%Z.
Proof.
  intros.
  unfold Ptrofs.add.
  rewrite Ptrofs.unsigned_repr.
  rewrite Ptrofs.unsigned_repr.
  reflexivity.
  inv H. inv H3; auto.
  inv H; auto.
Qed.


Theorem pointer_ofs_no_overflow:
forall ofs z,
  (0 <= z)%Z ->
  (Ptrofs.unsigned ofs + int_size * z <= Ptrofs.max_unsigned )%Z ->

                        Ptrofs.unsigned (Ptrofs.add ofs (Ptrofs.repr (int_size * z))) =
        (Ptrofs.unsigned ofs + int_size * z)%Z.
Proof.
  intros.
  unfold int_size in *; simpl size_chunk in *.
  assert (0 <=  Ptrofs.unsigned ofs)%Z by apply Ptrofs.unsigned_range_2.
  unfold Ptrofs.add.
  assert (0 <= size_chunk int_chunk)%Z by apply int_size_pos.
  rewrite Ptrofs.unsigned_repr with (z := (_ * z)%Z).
  rewrite Ptrofs.unsigned_repr. reflexivity.

  split; auto. apply Z.add_nonneg_nonneg; auto. apply Z.mul_nonneg_nonneg; auto.
  split; auto. apply Z.mul_nonneg_nonneg; auto.
  omega.
Qed.


 (* TODO: move to identifiers *)
Inductive bound_var_val: LambdaANF.term.val -> Ensemble var :=
| Bound_Vconstr :
    forall c vs v x,
    bound_var_val v x ->
    List.In v vs ->
    bound_var_val (Vconstr c vs) x
| Bound_Vfun:
    forall fds rho x f,
    bound_var_fundefs fds x ->
    bound_var_val (Vfun rho fds f) x.


Inductive occurs_free_val: LambdaANF.term.val -> Ensemble var :=
| OF_Vconstr :
    forall c vs v x,
    occurs_free_val v x ->
    List.In v vs ->
    occurs_free_val (Vconstr c vs) x
| OF_Vfun:
    forall fds rho x f,
      occurs_free_fundefs fds x ->
      M.get x rho = None ->
      occurs_free_val (Vfun rho fds f) x.


Definition closed_val (v : LambdaANF.term.val) : Prop :=
  Same_set var (occurs_free_val v) (Empty_set var).


Theorem closed_val_fun:
  forall fl f t vs e,
    closed_val (Vfun (M.empty term.val) fl f) ->
    find_def f fl = Some (t, vs, e) ->
    (Included _ (occurs_free e) (Ensembles.Union _  (FromList vs) (name_in_fundefs fl)) ).
Proof.
  intros. inv H. intro. intros.
  assert (~  occurs_free_val (Vfun (M.empty term.val) fl f) x). intro. apply H1 in H3. inv H3.
  clear H1. clear H2.
  assert (decidable (List.In x vs)). apply In_decidable. apply shrink_cps_correct.var_dec_eq.
  assert (decidable (name_in_fundefs fl x)). unfold decidable. assert (Hd := Decidable_name_in_fundefs fl). inv Hd. specialize (Dec x). inv Dec; auto.
  inv H1; inv H2; auto. exfalso.
  apply H3. constructor. SearchAbout occurs_free_fundefs find_def.
  eapply shrink_cps_correct.find_def_free_included. eauto. constructor. constructor. auto. auto. auto.
  apply M.gempty.
Qed.



Inductive dsubval_v: LambdaANF.term.val -> LambdaANF.term.val -> Prop :=
| dsubval_constr: forall v vs c,
  List.In v vs ->
  dsubval_v v (Vconstr c vs)
| dsubval_fun : forall x fds rho f,
  name_in_fundefs fds x ->
    dsubval_v (Vfun rho fds x) (Vfun rho fds f)
.

Definition subval_v := clos_trans _ dsubval_v.
Definition subval_or_eq := clos_refl_trans _ dsubval_v.



Theorem t_then_rt:
  forall A R (v v':A),
  clos_trans _ R v v'  ->
  clos_refl_trans _ R v v'.
Proof.
  intros. induction H.
  apply rt_step. auto.
  eapply rt_trans; eauto.
Qed.


Theorem rt_then_t_or_eq:
  forall A R (v v':A),
    clos_refl_trans _ R v v' ->
    v = v' \/ clos_trans _ R v v'.
Proof.
  intros. induction H.
  right. apply t_step; auto.
  left; auto.
  inv IHclos_refl_trans1; inv IHclos_refl_trans2.
  left; auto.
  right; auto.
  right; auto. right.
  eapply t_trans; eauto.
Qed.

Theorem dsubterm_case_cons:
  forall v l e',
    dsubterm_e e' (Ecase v l) ->
  forall a, dsubterm_e e' (Ecase v (a:: l)).
Proof.
  intros. inv H. econstructor.
  right; eauto.
Qed.



Theorem subterm_case:
forall v l e',
  subterm_e e' (Ecase v l) ->
  forall a, subterm_e e' (Ecase v (a:: l)).
Proof.
  intros. remember (Ecase v l) as y. revert dependent v. revert l. induction H.
  - intros. subst. constructor.
    eapply dsubterm_case_cons; eauto.
  - intros. apply IHclos_trans2 in Heqy.
    eapply t_trans. apply H. eauto.
Qed.


Theorem subval_fun: forall v rho fl x,
    name_in_fundefs fl x ->
        subval_or_eq v (Vfun rho fl x) ->
        exists l, v = Vfun rho fl l /\ name_in_fundefs fl l.
Proof.
  intros. apply rt_then_t_or_eq in H0.
  inv H0.
  exists x; auto.
  remember (Vfun rho fl x) as y.
  assert (exists x, y = Vfun rho fl x /\ name_in_fundefs fl x ) by eauto.
  clear H. clear Heqy. clear x.
  induction H1.  destructAll. subst. inv H. eauto.
  destructAll.
  assert ( (exists x : var, Vfun rho fl x0 = Vfun rho fl x /\ name_in_fundefs fl x)) by eauto.
  apply IHclos_trans2 in H. apply IHclos_trans1 in H. auto.
Qed.

Theorem subval_or_eq_constr:
forall v v' vs c,
  subval_or_eq v v' ->
  List.In v' vs ->
  subval_or_eq v (Vconstr c vs).
Proof.
  intros.
  eapply rt_trans; eauto.
  apply rt_step. constructor; auto.
Qed.



Theorem subval_v_constr:
  forall v vs t,
  subval_v v (Vconstr t vs) ->
  exists v',
    subval_or_eq v v' /\ List.In v' vs.
Proof.
  intros.
  remember (Vconstr t vs) as v'. revert t vs Heqv'.
  induction H; intros; subst.
  - inv H. exists x. split.
    apply rt_refl. apply H2.
  -  specialize (IHclos_trans2 t vs eq_refl).
     destruct IHclos_trans2.
     exists x0. destruct H1. split.
     apply t_then_rt in H.
     eapply rt_trans; eauto.
     auto.
Qed.

Theorem subval_or_eq_fun:
  forall rho' fds f vs t,
  subval_or_eq (Vfun rho' fds f) (Vconstr t vs) ->
  exists v',
    subval_or_eq (Vfun rho' fds f) v' /\ List.In v' vs.
Proof.
  intros.
  apply rt_then_t_or_eq in H. destruct H.
  inv H.
  eapply subval_v_constr; eauto.
Qed.


Theorem bound_var_subval:
  forall x v v',
  bound_var_val v x ->
  subval_or_eq v v' ->
  bound_var_val v' x.
Proof.
  intros. induction H0.
  - inv H0. econstructor; eauto.
    inv H. constructor. auto.
  - auto.
  - apply   IHclos_refl_trans2.
    apply   IHclos_refl_trans1.
    auto.
Qed.


(* bound_var_val - name_in_fds *)
Inductive bound_subvar_val : term.val -> Ensemble var :=
    Bound_SVconstr : forall (c : ctor_tag) (vs : list term.val) (v : term.val) (x : var),
                    bound_var_val (Vconstr c vs) x -> bound_subvar_val (Vconstr c vs) x
  | Bound_SVfun : forall (fds : fundefs) (rho : term.M.t term.val) (x f : var),
      bound_var_val (Vfun rho fds f) x -> ~name_in_fundefs fds x -> bound_subvar_val (Vfun rho fds f) x.



(* deep version of bound_subvar_val, likely what is needed for functions_not_bound inv *)
Inductive bound_notfun_val: term.val -> Ensemble var :=
  Bound_FVconstr : forall (c : ctor_tag) (vs : list term.val)
                         (v : term.val) (x : var),
                    bound_notfun_val v x ->
                    List.In v vs -> bound_notfun_val (Vconstr c vs) x
| Bound_FVfun : forall (e:exp) (fds : fundefs) (rho : term.M.t term.val) ys (x f f' : var) t,
    In _ (Ensembles.Union _ (FromList ys) (bound_var e)) x ->  find_def f' fds = Some (t, ys, e) ->  bound_notfun_val (Vfun rho fds f) x.


Theorem find_dsubterm:
  forall x t ys e fl,
find_def x fl = Some (t, ys, e) -> dsubterm_fds_e e fl.
Proof.
  induction fl; intros.
  - simpl in H. destruct (term.M.elt_eq x v) eqn:Heq_xv. inv H. constructor.
    constructor 2. eapply IHfl; eauto.
  - inv H.
Qed.

Theorem bound_subvar_var: forall v x,
  bound_subvar_val v x -> bound_var_val v x.
Proof.
  intros. inv H; auto.
Qed.

Theorem bound_notfun_var: forall v x,
  bound_notfun_val v x -> bound_var_val v x.
Proof.
  intros. induction H.
  - econstructor; eauto.
  -  constructor. induction fds. simpl in H0.
     destruct  (term.M.elt_eq f' v). inv H0. inv H. constructor; auto.
     constructor 3; auto.
     constructor 2. auto.
     inv H0.
Qed.


Theorem set_lists_In:
  forall {A} x xs (v:A) vs rho rho' ,
    List.In x xs ->
    M.get x rho' = Some v ->
    set_lists xs vs rho = Some rho' ->
    List.In  v vs.
Proof.
  induction xs; intros.
  -   inv H.
  - destruct vs. simpl in H1; inv H1. simpl in H1.
    destruct (set_lists xs vs rho) eqn:Hsl; inv H1.
    destruct (var_dec x a).
    + subst.
      rewrite M.gss in H0. inv H0. constructor; reflexivity.
    + rewrite M.gso in H0 by auto.
      constructor 2.
      inv H. exfalso; apply n; reflexivity.
      eapply IHxs; eauto.
Qed.

Ltac inList := repeat (try (left; reflexivity); right).


Ltac solve_nodup :=
  let hxy := fresh "Hxy" in
  intro hxy; subst; try (clear hxy);
repeat (match goal with
        | [H: NoDup _ |- _] => let h2 := fresh "Hnd" in
                               let h1 := fresh "HinList" in
                               let x := fresh "x" in
                               let l := fresh "l" in
                               inversion H as [h1 | x l h1 h2];
                               subst; clear H;
                               try (solve [apply h1; inList])
        end).

(**** Representation relation for LambdaANF values, expressions and functions ****)
Section RELATION.

  (* same as LambdaANF_to_Clight *)
  Variable (argsIdent : ident).
  Variable (allocIdent : ident).
  Variable (limitIdent : ident).
  Variable (gcIdent : ident).
  Variable (mainIdent : ident).
  Variable (bodyIdent : ident).
  Variable (threadInfIdent : ident).
  Variable (tinfIdent : ident).
  Variable (heapInfIdent : ident).
  Variable (numArgsIdent : ident).
  Variable (isptrIdent: ident). (* ident for the isPtr external function *)
  Variable (caseIdent:ident).
  Variable (nParam:nat).

  Definition protectedIdent: list ident := (argsIdent::allocIdent::limitIdent::gcIdent::mainIdent::bodyIdent::threadInfIdent::tinfIdent::heapInfIdent::numArgsIdent::numArgsIdent::isptrIdent::caseIdent::[]).



  Variable cenv:LambdaANF.term.ctor_env.
  Variable fenv:LambdaANF.term.fun_env.
  Variable finfo_env: LambdaANF_to_Clight.fun_info_env. (* map from a function name to its type info *)
  Variable p:program.

  (* This should be a definition rather than a parameter, computed once and for all from cenv *)
  Variable rep_env: M.t ctor_rep.


  Notation threadStructInf := (Tstruct threadInfIdent noattr).
  Notation threadInf := (Tpointer threadStructInf noattr).

  Notation funTy := (Tfunction (Tcons threadInf Tnil) Tvoid
                            {|
                              cc_vararg := false;
                              cc_unproto := false;
                              cc_structret := false |}).

Notation pfunTy := (Tpointer funTy noattr).

Notation gcTy := (Tfunction (Tcons (Tpointer (Tint I32 Unsigned noattr) noattr) (Tcons threadInf Tnil)) Tvoid
                            {|
                              cc_vararg := false;
                              cc_unproto := false;
                              cc_structret := false |}).

Notation isptrTy := (Tfunction (Tcons (Tint I32 Unsigned noattr) Tnil) (Tint IBool Unsigned noattr)
                               {|
                                 cc_vararg := false;
                                 cc_unproto := false;
                                 cc_structret := false |}).







Notation valPtr := (Tpointer val
                            {| attr_volatile := false; attr_alignas := None |}).

Notation boolTy := (Tint IBool Unsigned noattr).

Notation "'var' x" := (Etempvar x val) (at level 20).
Notation "'ptrVar' x" := (Etempvar x valPtr) (at level 20).

Notation "'bvar' x" := (Etempvar x boolTy) (at level 20).
Notation "'funVar' x" := (Evar x funTy) (at level 20).


Notation allocPtr := (Etempvar allocIdent valPtr).
Notation limitPtr := (Etempvar limitIdent valPtr).
Notation args := (Etempvar argsIdent valPtr).
Notation gc := (Evar gcIdent gcTy).
Notation ptr := (Evar isptrIdent isptrTy).



(* changed tinf to be tempvar and have type Tstruct rather than Tptr Tstruct *)
Notation tinf := (Etempvar tinfIdent threadInf).
Notation tinfd := (Ederef tinf threadStructInf).

Notation heapInf := (Tstruct heapInfIdent noattr).


Notation " a '+'' b " := (add a b) (at level 30).


Notation " a '-'' b " := (sub a b) (at level 30).


Notation " a '='' b " := (int_eq a b) (at level 35).


Notation "'!' a " := (not a) (at level 40).

Notation seq := Ssequence.

Notation " p ';' q " := (seq p q)
                         (at level 100, format " p ';' '//' q ").

Notation " a '::=' b " := (Sset a b) (at level 50).
Notation " a ':::=' b " := (Sassign a b) (at level 50).

Notation "'*' p " := (Ederef p val) (at level 40).

Notation "'&' p " := (Eaddrof p valPtr) (at level 40).



Notation c_int := c_int'.

Notation "'while(' a ')' '{' b '}'" :=
  (Swhile a b) (at level 60).

Notation "'call' f " := (Scall None f (tinf :: nil)) (at level 35).

Notation "'[' t ']' e " := (Ecast e t) (at level 34).

Notation "'Field(' t ',' n ')'" :=
  ( *(add ([valPtr] t) (c_int n%Z val))) (at level 36). (* what is the type of int being added? *)

Notation "'args[' n ']'" :=
  ( *(add args (c_int n%Z val))) (at level 36).

Definition int_shru z1 z2 := if Archi.ptr64 then (Vlong (Int64.shru (Int64.repr z1) (Int64.repr z2)))
                                                  else (Vint (Int.shru (Int.repr z1) (Int.repr z2))).

Definition int_and z1 z2 := if Archi.ptr64 then
                              (Vlong (Int64.and (Int64.repr z1) (Int64.repr z2))) else
                              (Vint (Int.and (Int.repr z1) (Int.repr z2))).

Ltac archi_red :=
  int_red;
  unfold sizeof in *;
  unfold int_chunk in *;
  unfold val in *;
  unfold uval in *;
  unfold val_typ in *;
  unfold Init_int in *;
  unfold make_vint in *;
  unfold make_cint in *;
  unfold int_shru in *;
  unfold int_and in *;
  unfold c_int in *;
  unfold uint_range in *;
  try (rewrite ptrofs_mu in *);
  (match goal with
   | [ H : Archi.ptr64 = _ |- _] => try (rewrite H in *)
   end).

(* these ltac are agnostic on archi, useful for automation *)
   Ltac ptrofs_of_int :=
     unfold Ptrofs.of_int64 in *;
     unfold ptrofs_of_int in *;
     unfold Ptrofs.of_intu in *;
     unfold Ptrofs.of_int in *.

   Ltac int_unsigned_repr :=
     try (rewrite Int64.unsigned_repr in *);
     try (rewrite Int.unsigned_repr in *).

   Ltac int_max_unsigned:=
     unfold Int64.max_unsigned in *;
     unfold Int.max_unsigned in *.



 Inductive header_of_rep: ctor_rep -> Z -> Prop :=
 | header_enum: forall t, header_of_rep (enum t) (Z.of_N ((N.shiftl t 1) + 1))
 | header_boxed: forall t a, header_of_rep (boxed t a) (Z.of_N ((N.shiftl a 10) + t)).

 Function var_or_funvar_f' (n : nat) (x:positive):expr :=
   match Genv.find_symbol (Genv.globalenv p) x with
   | Some _ =>  makeVar threadInfIdent n x fenv finfo_env
   | None => var x
   end.

 Function var_or_funvar_f (x:positive):expr :=
   match Genv.find_symbol (Genv.globalenv p) x with
   | Some _ =>  makeVar threadInfIdent nParam x fenv finfo_env
   | None => var x
   end.

 (* The full the domain of map is exactly the symbols of globalenv *)
  Definition find_symbol_domain {A} (map:M.t A):=
   forall (x:positive), (exists V1, M.get x map = Some V1) <-> (exists b, Genv.find_symbol (Genv.globalenv p) x = Some b).

 Definition finfo_env_correct :=
   forall (x:positive) i t, M.get x finfo_env = Some (i , t) -> (exists finfo, M.get t fenv = Some finfo).

(* CHANGE THIS *)
Inductive repr_asgn_fun': list positive -> list N -> statement -> Prop :=
| repr_asgn_nil: repr_asgn_fun' [] [] Sskip
| repr_asgn_cons: forall y ys i inf s, repr_asgn_fun' ys inf s ->
                 repr_asgn_fun' (y::ys) (i::inf) (s; args[ Z.of_N i ] :::= (var_or_funvar_f y)).

Inductive repr_asgn_fun: list positive -> list N -> statement -> Prop :=
  |repr_asgn_wrap: forall ys inf s, repr_asgn_fun' ys inf s ->
                   repr_asgn_fun ys inf (argsIdent ::= Efield tinfd argsIdent (Tarray val maxArgs noattr);s).

Inductive repr_call_vars' (par : nat) : nat -> list positive -> list expr -> Prop :=
| repr_call_nil : repr_call_vars' par 0 [] []
| repr_call_cons : forall n y ys es, repr_call_vars' par n ys es ->
                                     repr_call_vars' par (S n) (y :: ys) (var_or_funvar_f' par y :: es).


Definition repr_call_vars : nat -> list positive -> list expr -> Prop := repr_call_vars' nParam.

(* like fromN but for Z, should move to list_util and make a generic one *)
Fixpoint fromZ (z:Z) (m:nat): list Z :=
  match m with
  | 0 => nil
  | S m' => z :: (fromZ (Z.succ z) m')
  end.

Fixpoint fromInt (i:int) (m:nat): list int :=
  match m with
  | 0 => nil
  | S m' => i :: (fromInt (Int.add i Int.one) m')
  end.


Theorem fromN_Some: forall x n z l ,
 nthN (fromN l z) n = Some x ->
 x = N.add l n.
Proof.
  induction n using N.peano_rect; intros; simpl in H.
  - destruct z. simpl in H. inv H.
    simpl in H. inv H.
    rewrite N.add_0_r. reflexivity.
  - destruct z. simpl in H. inv H.
    simpl in H. (destruct (N.succ n) eqn:Sn). apply N.neq_succ_0 in Sn.  inv Sn.
    assert (n = (N.sub (N.pos p0)  1)).
    rewrite <- Sn. rewrite <- N.pred_sub.
    symmetry. apply N.pred_succ.
    rewrite <- H0 in H.
    apply IHn in H. rewrite <- Sn.
    rewrite N.add_succ_l in H.
    rewrite N.add_succ_r. auto.
Qed.



Definition Forall_in_mem_block {A} : (A -> (block *  int) -> Prop) -> list A -> (block * int) -> int -> Prop :=
  fun P ls loc z =>
    let (b, z0) := loc in
    let ids := fromN 0%N  (length ls) in
    Forall2 (fun a i => P a (b, Int.add z0 (Int.mul (Int.repr (Z.of_N i)) z))) ls ids.


Theorem Forall_in_mem_block_nthN :
  forall {A P vs b i z v n},
     Forall_in_mem_block P vs  (b, i) z ->
     @nthN A vs n = Some v ->
     P v (b, Int.add i (Int.mul (Int.repr (Z.of_N n)) z)).
Proof.
  intros. unfold Forall_in_mem_block in H.
  assert (Hf2 := Forall2_nthN _ _ _ _ _ H H0).
  destruct Hf2. destruct H1.
  apply fromN_Some in H1. simpl in H1. subst; assumption.
Qed.

Inductive Forall_statements_in_seq' {A}: (BinNums.Z  -> A -> statement -> Prop) ->  list A -> statement -> BinNums.Z -> Prop :=
| Fsis_last: forall (R: (BinNums.Z  -> A -> statement -> Prop)) n v s, R n v s -> Forall_statements_in_seq' R [v] s n
| Fsis_cons: forall R v vs s s' n, Forall_statements_in_seq' R vs s' (Z.succ n) ->
                                   R n v s ->  Forall_statements_in_seq' R (v::vs) (s; s') n.



Inductive Forall_statements_in_seq_rev {A}: (BinNums.Z  -> A -> statement -> Prop) ->  list A -> statement -> nat -> Prop :=
| Fsir_last: forall (R: (BinNums.Z  -> A -> statement -> Prop)) v s, R 0%Z v s -> Forall_statements_in_seq_rev R [v] s 0
| Fsir_cons: forall R v vs s s' n, Forall_statements_in_seq_rev R vs s' n ->
                                   R (Z.of_nat (S n)) v s ->  Forall_statements_in_seq_rev R (v::vs) (s; s') (S n).




(* This is true for R, vs and S iff forall i, R i (nth vs) (nth s)
   > list cannot be empty (o.w. no statement)
   > nth on statement is taken as nth on a list of sequenced statement (;) *)
Definition Forall_statements_in_seq {A}: (BinNums.Z  -> A -> statement -> Prop) ->  list A -> statement -> Prop :=
  fun P vs s =>  Forall_statements_in_seq' P vs s (0%Z).

(* This should sync with makeVar *)
Inductive var_or_funvar : positive -> expr -> Prop :=
| F_VoF : forall x b,
    Genv.find_symbol (Genv.globalenv p) x = Some b ->
                var_or_funvar x (makeVar threadInfIdent nParam x fenv finfo_env)
| V_VoF : forall x,
    Genv.find_symbol (Genv.globalenv p) x = None ->
       var_or_funvar x (var x).

Theorem var_or_funvar_of_f:
  forall x e,
  var_or_funvar x e <-> var_or_funvar_f x = e.
Proof.
  unfold var_or_funvar_f; split; intro.
  inv H;  rewrite H0; auto.
  destruct ( Genv.find_symbol (Genv.globalenv p) x) eqn:Hx; subst; econstructor; eauto.
Qed.

Fixpoint Vint_or_Vptr (v:Values.val): bool :=
  match v with
  | Vint _ => negb Archi.ptr64
  | Vlong _ => Archi.ptr64
  | Vptr _ _ => true
  | _ => false
  end.

Inductive get_var_or_funvar (lenv: temp_env): positive -> Values.val -> Prop :=
|F_gVoF:
   forall b x,
     Genv.find_symbol (Genv.globalenv p) x = Some b ->
   get_var_or_funvar lenv x (Vptr b (Ptrofs.repr 0%Z))
| V_gVoF:
    forall x v,
      Genv.find_symbol (Genv.globalenv p) x = None ->
      M.get x lenv = Some v ->
      Vint_or_Vptr v = true ->
      get_var_or_funvar lenv x v.

(* goes through a lists of positive l and returns a lists of Values vs for which
 Forall2 (get_var_or_fun lenv) l vs *)
Fixpoint get_var_or_funvar_list (lenv:temp_env) (l:list positive): option (list (Values.val)) :=
  match l with
  | nil => Some nil
  | x::ls =>
    (match get_var_or_funvar_list lenv ls with
     | Some vs =>
       (match Genv.find_symbol (Genv.globalenv p) x with
        | Some b => Some ((Vptr b Ptrofs.zero)::vs)
        | None =>
          (match (M.get x lenv) with
           | Some v =>
             (match v with
              | Vint _ => if Archi.ptr64 then None else Some (v::vs)
              | Vlong _ => if Archi.ptr64 then Some (v::vs) else None
              | Vptr _ _ => Some (v::vs)
              | _ => None
              end)
           | None => None
           end)
        end)
     | None => None
     end)
  end.


Lemma get_var_or_funvar_list_correct1:
  forall lenv l vs,
  get_var_or_funvar_list lenv l = Some vs ->
  Forall2 (get_var_or_funvar lenv) l vs.
Proof.
  induction l; intros.
  simpl in H. inv H. constructor.
  simpl in H.
  destruct (get_var_or_funvar_list lenv l)  eqn:gvl.
  specialize (IHl l0 (eq_refl _)).
  destruct (Genv.find_symbol (Genv.globalenv p) a) eqn:gfpa.
  - inv H.
    constructor; auto.
    left; auto.
  - destruct  (M.get a lenv) eqn:gal.
    destruct v; inv H.
    destruct (Archi.ptr64) eqn:Harch; constructor. right; auto. auto.
    constructor; auto. auto.
    constructor; auto. right;  auto.  inv H.
  - inv H.
Qed.

Theorem get_var_or_funvar_list_correct2:
  forall lenv l vs,
    Forall2 (get_var_or_funvar lenv) l vs    ->
    get_var_or_funvar_list lenv l = Some vs.
Proof.
  induction l; intros.
  - inv H. reflexivity.
  - inv H. apply IHl in H4. simpl. rewrite H4.
    inv H2.
    rewrite H.
    reflexivity.
    rewrite H. rewrite H0. destruct y; inv H1; auto.
Qed.

Theorem get_var_or_funvar_list_correct:
  forall lenv l vs,
  Forall2 (get_var_or_funvar lenv) l vs    <->
    get_var_or_funvar_list lenv l = Some vs.
Proof.
  split. apply get_var_or_funvar_list_correct2.
  apply get_var_or_funvar_list_correct1.
Qed.

(* can be strenghten to lenv maps that are equal over l *)
Theorem get_var_or_funvar_list_set:
  forall lenv x v l,
    ~ List.In x l ->
              get_var_or_funvar_list lenv l = get_var_or_funvar_list (M.set x v lenv) l.
Proof.
  induction l; intros.
  - reflexivity.
  - simpl. rewrite M.gso. rewrite IHl. reflexivity.
    intro. apply H. constructor 2. auto. intro; apply H.
    constructor; auto.
Qed.


Theorem Forall2_length':
  forall A B (R:A -> B -> Prop) l l',
  Forall2 R l l' ->
  length l = length l'.
Proof.
  induction l; intros. inv H. auto.
  inv H. apply IHl in H4. simpl; auto.
Qed.

Theorem get_var_or_funvar_list_same_length:
  forall lenv l vs,
  get_var_or_funvar_list lenv l = Some vs ->
  length l = length vs.
Proof.
  intros.
  apply get_var_or_funvar_list_correct in H.
  apply Forall2_length' in H.
  auto.
Qed.


Definition map_get_r_l: forall t l, relation (M.t t) :=
  fun t l => fun sub sub' => forall v,
               List.In v l ->
               M.get v sub = M.get v sub'.

Theorem get_var_or_funvar_proper:
  forall lenv lenv' l x v,
  get_var_or_funvar lenv x v ->
  map_get_r_l _ l lenv lenv' ->
  List.In x l ->
  get_var_or_funvar lenv' x v.
Proof.
  intros.
  inv H. constructor; auto.
  constructor 2; auto. erewrite <- H0; auto.
Qed.

Theorem get_var_or_funvar_int_or_ptr:
  forall lenv y v7,
    get_var_or_funvar lenv y v7 ->
    Vint_or_Vptr v7 = true.
Proof.
  intros. inv H. auto.
  auto.
Qed.


Theorem get_var_or_funvar_list_proper:
  forall lenv lenv' l vs,
  get_var_or_funvar_list lenv l = Some vs ->
  map_get_r_l _ l lenv lenv' ->
  get_var_or_funvar_list lenv' l = Some vs.
Proof.
  induction l; intros.
  simpl. simpl in H. auto.
  simpl in H.
  destruct (get_var_or_funvar_list lenv l) eqn:Hgll.
  assert ( Some l0 = Some l0) by reflexivity.
  assert (map_get_r_l Values.val l lenv lenv'). intro; intros.
  apply H0. constructor 2; auto.
  specialize (IHl _ H1 H2).
  simpl. rewrite IHl.
  destruct  (Genv.find_symbol (Genv.globalenv p) a).
  auto.
  rewrite <- H0. auto.
  constructor. auto.
  inv H.
Qed.

Inductive is_nth_projection_of_x : positive -> Z -> positive -> statement -> Prop :=
  Make_nth_proj: forall x  n v e,
                         var_or_funvar v  e ->
                          is_nth_projection_of_x x n v (Field(var x, n) :::=  e).


(* this version of mem_after_n_proj casts to match is_nth_projection *)
Inductive mem_after_n_proj_store_cast : block -> Z -> (list Values.val) -> Z -> mem -> mem ->  Prop :=
| Mem_last_c:
    forall m b ofs i v m',
    Mem.store int_chunk m b  (Ptrofs.unsigned (Ptrofs.add (Ptrofs.repr ofs) (Ptrofs.repr (int_size*i)))) v = Some m' ->
    mem_after_n_proj_store_cast b ofs [v] i m m'
| Mem_next_c:
    forall m b ofs i v m' m'' vs,
      Mem.store int_chunk m b (Ptrofs.unsigned (Ptrofs.add (Ptrofs.repr ofs) (Ptrofs.repr (int_size*i)))) v = Some m' ->
      mem_after_n_proj_store_cast b ofs vs (Z.succ i) m' m'' ->
      mem_after_n_proj_store_cast b ofs (v::vs) i m m''.


Inductive mem_after_n_proj_store : block -> Z -> (list Values.val) -> Z -> mem -> mem ->  Prop :=
| Mem_last:
    forall m b ofs i v m',
    Mem.store int_chunk m b  (ofs + (int_size*i)) v = Some m' ->
    mem_after_n_proj_store b ofs [v] i m m'
| Mem_next:
    forall m b ofs i v m' m'' vs,
      Mem.store int_chunk m b (ofs + (int_size*i)) v = Some m' ->
      mem_after_n_proj_store b ofs vs (Z.succ i) m' m'' ->
      mem_after_n_proj_store b ofs (v::vs) i m m''.

(* represent work "already done" while consuming mem_after_n_proj *)
Inductive mem_after_n_proj_snoc :  block -> Z -> (list Values.val)  -> mem -> mem ->  Prop :=
| Mem_nil_snoc: forall m b ofs,
    mem_after_n_proj_snoc b ofs [] m m
| Mem_cons_snoc: forall m b ofs m' m'' v vs,
    mem_after_n_proj_snoc b ofs vs m m' ->
    Mem.store int_chunk m' b (ofs + (int_size*(Z.of_nat (length vs)))) v = Some m'' ->
    mem_after_n_proj_snoc b ofs (v::vs) m m''.




Theorem  mem_after_n_proj_store_snoc:
  forall b ofs vs1 m m1,
  mem_after_n_proj_snoc b ofs vs1 m m1 ->
forall vs2 m',
  mem_after_n_proj_store b ofs vs2 (Z.of_nat (length vs1)) m1 m' ->
  forall vs,
    List.app (rev vs1) vs2 = vs ->
    mem_after_n_proj_store b ofs vs 0 m m'.
Proof.
  induction vs1; intros.
  - simpl in H1; subst. simpl in H0. inv H. auto.
  -   simpl in H1. inv H.
      rewrite <- app_assoc. eapply IHvs1. apply H6. 2: reflexivity.
      simpl.
      simpl length in H0. rewrite Nat2Z.inj_succ in H0.
      econstructor; eauto.
Qed.

Theorem  mem_after_n_proj_store_snoc':
  forall b ofs vs m m',
    mem_after_n_proj_store b ofs vs 0 m m' ->
    forall vs1 vs2,
      vs2 <> nil ->
      List.app (rev vs1) vs2 = vs ->
      exists m1,
  mem_after_n_proj_snoc b ofs vs1 m m1 /\
  mem_after_n_proj_store b ofs vs2 (Z.of_nat (length vs1)) m1 m'.
Proof.
  intros b ofs vs m m' Hmm'.
  induction vs1; intros.
  -  simpl in H0; subst. exists m. simpl. split.
     constructor. auto.
  - simpl in H0. rewrite <- app_assoc in H0. apply IHvs1 in H0. destruct H0. destruct H0.
    simpl in H1.
    inv H1. (* impossible, vs2 is not empty *)  exfalso; auto.
    exists m'0. split. econstructor; eauto. simpl length. rewrite Nat2Z.inj_succ. auto. intro. inv H1.
Qed.




  (*
todo:
Theorem mem_after_n_proj_store_snoc:
  forall b ofs,
  forall vs1 vs2,
    List.app (rev vs1) vs2 = vs ->
    forall vs m m' i,
      mem_after_n_proj_store b ofs vs i m m' ->
      exists m1,
        mem_after_n_proj_snoc b ofs vs1 m m1  /\
        mem_after_n_proj_store b ofs vs2 (Z.of_nat (length (rev vs1))) m1 m'.
*)


Theorem mem_after_n_proj_wo_cast:
  forall vs b ofs i m m',

  (0 <= ofs)%Z -> (0 <= i)%Z ->
   (uint_range (ofs+int_size*(i+(Z.of_nat (length vs)))))%Z ->
      mem_after_n_proj_store_cast b ofs vs i m m' <-> mem_after_n_proj_store b ofs vs i m m'.
Proof.
  induction vs; intros.
  { (* impossible *) split; intro; inv H2. }
  assert (ofs + int_size * i  = Ptrofs.unsigned (Ptrofs.add (Ptrofs.repr ofs) (Ptrofs.repr (int_size * i))))%Z.
  assert (0 <=  int_size * (i + Z.of_nat (length (a::vs)))<= Ptrofs.max_unsigned)%Z.
  unfold int_size in *. simpl size_chunk in *.
  inv H1. assert (Hisp := int_size_pos).
  split. apply Z.mul_nonneg_nonneg; auto.  omega. omega.
  rewrite Ptrofs.add_unsigned.
  unfold int_size in *.
  simpl size_chunk in *.
  inv H1.
  rewrite Ptrofs.unsigned_repr with (z := ofs).
  rewrite Ptrofs.unsigned_repr with (z := (_ * i)%Z).
  rewrite Ptrofs.unsigned_repr.
  reflexivity. split.
  assert (Hisp := int_size_pos).
  apply Z.add_nonneg_nonneg; auto.
  apply Z.mul_nonneg_nonneg; auto.
  chunk_red; omega.
  chunk_red; omega.
  omega.
  simpl length in H1.
  rewrite Nat2Z.inj_succ in H1.
  rewrite Z.add_succ_r in H1.
  split; intro; inv H3.
  - constructor. rewrite H2. auto.
  - econstructor. rewrite H2. apply H8.
    rewrite <- IHvs; auto. omega.
    rewrite Z.add_succ_l.
    apply H1.
  - constructor. rewrite <- H2. auto.
  - econstructor. rewrite <- H2. apply H8.
    rewrite IHvs; auto. omega.
    rewrite Z.add_succ_l.
    apply H1.
Qed.


(* mem_after_n_proj_store_load *)

Theorem mem_after_n_proj_store_load:
  forall b ofs vs i m m',
    mem_after_n_proj_store b ofs vs i m m' ->
    forall ofs' b',
      ( b' <> b \/
        (ofs' + int_size <= ofs + int_size * i)%Z \/
        (ofs + int_size * (1+(i+(Z.of_nat (length vs)))) <= ofs')%Z) ->
      Mem.load int_chunk m' b' ofs' = Mem.load int_chunk m b' ofs'.
Proof.
  induction vs; intros; inv H.
  - eapply Mem.load_store_other.
    apply H8.
    unfold int_size in *.
    rewrite <- Zred_factor3 in H0.
    rewrite Z.add_assoc in H0.
    simpl length in H0. simpl Z.of_nat in H0.
    inv H0; auto.
    inv H; auto.
    right; right.
    rewrite Z.add_comm with (n := i) in H0.
    rewrite  <- Zred_factor3 in H0.
    rewrite Z.add_assoc in H0.  simpl size_chunk in H0. assert (Hisp := int_size_pos). omega.
  - eapply IHvs in H9.
     symmetry.
     erewrite <- Mem.load_store_other.
     symmetry. apply H9. apply H5.
     { destruct H0; auto.
       unfold int_size in *.
       destruct H; auto.
       right. right.
       simpl length in H.
       rewrite Nat2Z.inj_succ in H.
       chunk_red ; omega.
     }
     {
       assert (Hisp := int_size_pos).
       unfold int_size in *.
       simpl size_chunk in *.
       simpl length in H0.
       rewrite Nat2Z.inj_succ in H0.
       destruct H0; auto.
       destruct H. right. left. chunk_red; omega.
       right. right. chunk_red; omega.
     }
Qed.


(* mem_after_n_proj_store on area in comp(L) leaves m unchanged on L (or any area unaffected by the proj stored *)
Theorem mem_after_n_proj_store_unchanged:
  forall L b ofs vs i m m',
    mem_after_n_proj_store b ofs vs i m m' ->
  (forall j, (ofs+int_size*i) <= j < ofs+int_size*(i + Z.of_nat (length vs)) ->  ~ L b j)%Z ->
  Mem.unchanged_on L m m'.
Proof.
  induction vs; intros; inv H.
  - eapply Mem.store_unchanged_on; eauto.
    intros.
    apply H0.
    unfold int_size in *.
    simpl length. simpl Z.of_nat.
    chunk_red; omega.
  - apply Mem.unchanged_on_trans with (m2 := m'0).
    + eapply Mem.store_unchanged_on; eauto.
      intros. apply H0.
      simpl length.
      rewrite Nat2Z.inj_succ.
      chunk_red;
      omega.
    + eapply IHvs; eauto.
      intros. apply H0.
      simpl length.
      rewrite Nat2Z.inj_succ.
      chunk_red;
      omega.
Qed.

Theorem mem_after_n_proj_snoc_unchanged:
  forall L b ofs vs  m m',
    mem_after_n_proj_snoc b ofs vs m m' ->
  (forall j, ofs <= j < ofs+int_size*(Z.of_nat (length vs)) ->  ~ L b j)%Z ->
  Mem.unchanged_on L m m'.
Proof.
  induction vs.
  - intros. inv H. apply Mem.unchanged_on_refl.
  - intros. inv H.
    apply Mem.unchanged_on_trans with (m2 := m'0).
    + apply IHvs in H5; auto.
      simpl length in H0.
      rewrite Nat2Z.inj_succ in H0.        intros. apply H0. chunk_red; omega.
    + eapply Mem.store_unchanged_on; eauto.
      intros.
      simpl length in H0.
      rewrite Nat2Z.inj_succ in H0. intros. apply H0. chunk_red;
      omega.
Qed.


Definition prefix_ctx {A:Type} rho' rho :=
  forall x v, M.get x rho' = Some v -> @M.get A x rho = Some v.



(* keep around the fact that t is no bigger than 2^(int_size-1) [which we know by correct_crep] *)
 Definition repr_unboxed_Codegen: N -> Z -> Prop :=
   fun t => fun h =>
              (h = (Z.shiftl (Z.of_N t) 1) + 1)%Z /\
              (0 <= (Z.of_N t)  <  Ptrofs.half_modulus )%Z.

 Theorem repr_unboxed_eqm: forall h t,
     repr_unboxed_Codegen t h ->
   Ptrofs.eqm h (Z.of_N ((N.shiftl t 1) + 1)).
 Proof.
   intros. inv H.
   rewrite OrdersEx.Z_as_DT.shiftl_mul_pow2; try omega.
   simpl.
   rewrite N.shiftl_mul_pow2.
   rewrite N2Z.inj_add.
   rewrite N2Z.inj_mul.
   simpl.
   rewrite Z.pow_pos_fold.
   rewrite Pos2Z.inj_pow.  apply Ptrofs.eqm_refl.
 Qed.
 SearchAbout Int.max_signed.

 Theorem nat_shiftl_p1:
   forall n z,
     1 < z ->
 n  < (z / 2) ->
 n * 2 + 1 < z.
 Proof.
   induction n; intros.
   simpl. auto.
   simpl.
   destruct z. inv H0. destruct z.
   - inv H0.
   - rewrite <- Nat.div2_div in H0. simpl in H0. rewrite Nat.div2_div in H0.
     apply Nat.succ_lt_mono in H0.
     assert (Hz := NPeano.Nat.lt_decidable 1 z). inv Hz.
     specialize (IHn _ H1 H0). omega.
     destruct z.
       (* case 0 *) inv H0. inv H.
     destruct z.
     (* case 1 *) inv H0.
     exfalso. apply H1. omega.
 Qed.

 Theorem pos_nat_div2 : forall p,
    p <> xH ->
  Pos.to_nat (Pos.div2 p) = Nat.div2 (Pos.to_nat p).
 Proof.
   intros. destruct p0.
   - simpl Pos.div2.
     rewrite Pos2Nat.inj_xI.
     rewrite Nat.div2_succ_double. reflexivity.
   - simpl Pos.div2.
     rewrite Pos2Nat.inj_xO.
     rewrite Div2.div2_double. reflexivity.
   - exfalso. apply H; auto.
 Qed.

 Theorem Div2_Z_to_nat: forall n,
     (0 <= n)%Z ->
    Z.to_nat (Z.div2 n) = Nat.div2 (Z.to_nat n).
 Proof.
   induction n; intros.
   - reflexivity.
   -  simpl. destruct p0.
      rewrite Z2Nat.inj_pos.
      rewrite pos_nat_div2. reflexivity.
      intro. inv H0.
      rewrite Z2Nat.inj_pos.
      rewrite pos_nat_div2. reflexivity.
      intro. inv H0.
      reflexivity.
   - assert (Hp0 := Zlt_neg_0 p0). exfalso. omega.
 Qed.



 Theorem repr_unboxed_header_range:
   forall t h,
     repr_unboxed_Codegen t h ->
     (0 <= h <= Ptrofs.max_unsigned)%Z.
 Proof.
   intros. inv H.
   unfold Ptrofs.max_unsigned.
   unfold Ptrofs.half_modulus in *.

   unfold Ptrofs.modulus in *.
   rewrite OrdersEx.Z_as_DT.shiftl_mul_pow2; try omega.
   rewrite Z.pow_1_r.
   split; try omega.

   rewrite Z.sub_1_r.
   rewrite <- ReflOmegaCore.Z_as_Int.le_lt_int.
   destruct H1.
   unfold Ptrofs.wordsize in *. unfold Wordsize_Ptrofs.wordsize in *.
   assert (Hws:(0 <= Zpower.two_power_nat (if Archi.ptr64 then 64%nat else 32%nat))%Z).
   {
     assert (Hws' := Coqlib.two_power_nat_pos (if Archi.ptr64 then 64%nat else 32%nat)). omega.
   }
   rewrite Z2Nat.inj_lt; try omega. rewrite Z2Nat.inj_lt in H0; try omega.
   rewrite Z2Nat.inj_add in * by omega.
   rewrite Z2Nat.inj_mul in * by omega.
   rewrite <- Z.div2_div in H0.
   rewrite Div2_Z_to_nat in H0.
   rewrite Nat.div2_div in H0.
   eapply nat_shiftl_p1.
   chunk_red; simpl; rewrite <- Pos2Nat.inj_1;
     apply nat_of_P_lt_Lt_compare_morphism; auto.
   auto. auto.
 Qed.



 Theorem repr_unboxed_shiftr:
   forall t h,
   repr_unboxed_Codegen t h ->
   Z.shiftr h 1 =  Z.of_N t.
 Proof.
   intros.
   inv H.
   rewrite Ptrofs.Zshiftl_mul_two_p by omega.
   unfold Z.shiftr.
   simpl Z.shiftl.
   unfold Zpower.two_power_pos. simpl.
   rewrite Zdiv.Zdiv2_div.
   replace (Z.of_N t * 2 + 1)%Z with (OrdersEx.Z_as_OT.b2z true + 2 * (Z.of_N t))%Z by (simpl OrdersEx.Z_as_OT.b2z; omega).
   apply OrdersEx.Z_as_OT.add_b2z_double_div2.
Qed.


Definition boxed_header: N -> N -> Z -> Prop :=
  fun t => fun a =>  fun h =>
                       (h =  (Z.shiftl (Z.of_N a) 10) + (Z.of_N t))%Z /\
                       (0 <= Z.of_N t <  Zpower.two_power_pos 8)%Z /\
                       (0 <= Z.of_N a <  Zpower.two_power_nat (Ptrofs.wordsize - 10))%Z.

Theorem repr_boxed_header_range:
   forall t a h,
     boxed_header t a h ->
     (0 <= h <= Ptrofs.max_unsigned)%Z.
 Proof.
   intros. inv H.
   rewrite  OrdersEx.Z_as_DT.shiftl_mul_pow2.
   destruct H1.
   rewrite Zpower.two_power_pos_correct in *.
   rewrite Zpower.two_power_nat_correct in *.
   simpl in *.
   unfold Z.pow_pos in *.
   2: omega.
   split.
   - apply Z.add_nonneg_nonneg.
     apply Z.mul_nonneg_nonneg. omega. simpl; omega.
     omega.
   - (* moving to pos then computing by archi *)
     unfold Ptrofs.max_unsigned. unfold Ptrofs.modulus.
     unfold Ptrofs.wordsize in *.
     unfold Wordsize_Ptrofs.wordsize in *.
     chunk_red; simpl in *. omega. omega.
Qed.

Theorem div2_iter_pos:
  forall p0 a,
    (0 <= a -> 0 <= Pos.iter Z.div2 a p0)%Z.
Proof.
  induction p0; intros.
  - simpl.
    rewrite OrdersEx.Z_as_OT.div2_nonneg.
    apply IHp0. apply IHp0. auto.
  - simpl. apply IHp0. apply IHp0.
    auto.
  - simpl; rewrite OrdersEx.Z_as_OT.div2_nonneg; auto.
Qed.


Theorem mul2_iter_pos:
  forall p0 a,
    (0 <= a -> 0 <= Pos.iter (Z.mul 2) a p0)%Z.
Proof.
  induction p0; intros.
  - simpl. destruct (Pos.iter (Z.mul 2) (Pos.iter (Z.mul 2) a p0) p0) eqn:Hp.
    * reflexivity.
    * apply Pos2Z.is_nonneg.
    * exfalso.
      assert (0 <=  Pos.iter (Z.mul 2) (Pos.iter (Z.mul 2) a p0) p0)%Z.
      apply IHp0. apply IHp0. auto.
      rewrite Hp in H0.
      assert (Hneg := Pos2Z.neg_is_neg p1).
      omega.
  - simpl. apply IHp0. apply IHp0. auto.
  - simpl. destruct a; try omega.
    apply Pos2Z.is_nonneg.
    exfalso.
    assert (Hneg := Pos2Z.neg_is_neg p0).
    omega.
Qed.


Theorem pos_iter_xI: forall A f (a:A) p,
  Pos.iter f (a)%Z p~1 = f (Pos.iter f (Pos.iter f a p)%Z p).
Proof.
  intros. simpl. reflexivity.
Qed.

Theorem pos_iter_xH: forall A f (a:A),
  Pos.iter f (a)%Z 1 = f a.
Proof.
  intros. simpl. reflexivity.
Qed.

Theorem pos_iter_xO: forall A f (a:A) p,
  Pos.iter f (a)%Z p~0 = (Pos.iter f (Pos.iter f a p)%Z p).
Proof.
  intros. simpl. reflexivity.
Qed.

SearchAbout Z.div2 Z.add.


Theorem div2_even_add:
  forall a b,
    (Z.odd a = false ->
   Z.div2 (a + b) = Z.div2 a + Z.div2 b)%Z.
Proof.
  intros.
  repeat (rewrite Z.div2_div).
  rewrite Z.div2_odd with (a := b).
  rewrite Z.add_assoc.
  rewrite Z.add_carry_div2.
  rewrite <- Z.div2_odd with (a := b).
  repeat (rewrite Z.bit0_odd).
  rewrite H.
  rewrite <- Z.bit0_odd.
  rewrite Z.testbit_even_0.
  replace  (Z.b2z (false && false || Z.odd b && (false || false))) with 0%Z.
  rewrite Z.mul_comm.
  rewrite Zdiv.Z_div_mult.
  rewrite Z.add_0_r.
  rewrite Z.div2_div. reflexivity.
  omega.
  destruct (Z.odd b); simpl; reflexivity.
Qed.



Theorem shiftl_add_nonneg:
  forall c a b,
   ( 0 <= a ->
    0 <= b ->
     0 <= c ->
    Z.shiftl (a + b) c = Z.shiftl a c + Z.shiftl b c)%Z.
Proof.
  destruct c; intros.
  reflexivity.
  - simpl.
    revert dependent a. revert dependent b.
    clear H1. revert p0.
    induction p0; intros.
    + do 3 (rewrite pos_iter_xI).
      rewrite <- Z.mul_add_distr_l.
      rewrite <- IHp0.
      rewrite <- IHp0.
      reflexivity.
      auto. auto.
      apply mul2_iter_pos; auto.
      apply mul2_iter_pos; auto.
    + simpl. rewrite IHp0.
      rewrite IHp0.
      reflexivity.
      apply mul2_iter_pos; auto.
      apply mul2_iter_pos; auto.
      auto. auto.
    + do 3 (rewrite pos_iter_xH).
      apply Z.mul_add_distr_l.
  - simpl.
    exfalso.
    assert (Hneg := Pos2Z.neg_is_neg p0). omega.
Qed.



Theorem iter_div_testbit_decompose:
  (forall c a b,
      (forall d, (0 <= d < (Z.pos c))%Z ->
                 Z.testbit a d = false) ->
      Pos.iter Z.div2 (a + b) c =
      Pos.iter Z.div2 a c + Pos.iter Z.div2 b c)%Z.
Proof.
  induction c; intros.
  - do 3 (rewrite pos_iter_xI).
    assert (Hrw := Z.shiftr_spec).
    rewrite IHc.
    rewrite IHc.
    rewrite div2_even_add. reflexivity.
    rewrite <- Z.bit0_odd.
    assert (Hrw' := Hrw).
    specialize (Hrw (Pos.iter Z.div2 a c) (Z.pos c)).
    unfold Z.shiftr in Hrw. simpl in Hrw.
    rewrite Hrw by omega.
    specialize (Hrw' a (Z.pos c)). rewrite Hrw'.
    simpl Z.add.
    apply H. split.
    apply Pos2Z.pos_is_nonneg.
    rewrite Pos.add_diag.
    rewrite Pos2Z.inj_xI.
    rewrite Pos2Z.inj_xO. omega.
    simpl.
    apply Pos2Z.pos_is_nonneg.
    specialize (Hrw a (Z.pos c)).
    unfold Z.shiftr in Hrw. simpl in Hrw.
    intros.
    rewrite Hrw. apply H.
    rewrite Pos2Z.inj_xI.
    omega. omega.
    intros. apply H.
    rewrite Pos2Z.inj_xI. omega.
  - rewrite pos_iter_xO.
    rewrite IHc.
    rewrite pos_iter_xO.
    rewrite pos_iter_xO.
    2:{ intros. apply H.
    rewrite Pos2Z.inj_xO.
    assert (0 < Z.pos c)%Z by apply Pos2Z.is_pos.
    omega. }
    rewrite IHc. reflexivity.
    intros.
    assert (Hrw := Z.shiftr_spec).
    specialize (Hrw a (Z.pos c)). unfold Z.shiftr in Hrw.
    simpl in Hrw.  rewrite Hrw.
    2:{ destruct H0. auto. }
    apply H.
    rewrite Pos2Z.inj_xO. omega.
  - repeat (rewrite pos_iter_xH).
    rewrite div2_even_add. reflexivity.
    rewrite <- Z.bit0_odd.
    apply H. omega.
Qed.

Corollary shiftr_testbit_decompose:
  (forall c a b,
      (forall d, (0 <= d < (Z.pos c))%Z ->
                 Z.testbit a d = false) ->
      Z.shiftr (a + b) (Z.pos c) =
      Z.shiftr a (Z.pos c) + Z.shiftr b (Z.pos c))%Z.
Proof.
  intros. unfold Z.shiftr. simpl.
  apply iter_div_testbit_decompose; auto.
Qed.


Theorem shiftr_bounded_decompose:
  forall a b c,
  (0 <= a ->
  0 < c ->
  (0 <= b < Zpower.two_p c) ->
  Z.shiftr ((Z.shiftl a c) + b) c = a)%Z.
Proof.
  intros.
  destruct c.
  (* impossible cases *)
  inv H0.
  2:{ exfalso.
  assert (Hneg:= Pos2Z.neg_is_neg p0). omega. }
  rewrite shiftr_testbit_decompose.
  rewrite Z.shiftr_shiftl_l.
  rewrite Z.sub_diag. simpl.

  rewrite Int.Zshiftr_div_two_p.
  rewrite Zdiv.Zdiv_small. omega.
  auto.
  omega.
  omega.
  intros.
  apply Z.shiftl_spec_low. destruct H2. auto.
Qed.

Theorem repr_boxed_a:
   forall a t h,
     boxed_header t a h ->
   Z.shiftr h 10 =  Z.of_N a.
Proof.
  intros.
  inv H.
  destructAll.
  rewrite shiftr_bounded_decompose; auto.
  omega. simpl.
  split; auto.
  rewrite Zpower.two_power_pos_equiv in *.
  simpl in *. unfold Z.pow_pos in *. simpl in *.
  omega.
Qed.

Theorem pos_testbit_impossible:
  forall b,
  ~ (forall d : N, (0 <= d)%N -> Pos.testbit b d = false).
Proof.
  induction b; intro.
  - apply IHb; intros.
    assert ( 0 <= 0)%N by reflexivity.
    apply H in H1. inv H1.
  - apply IHb.
    intros.
    simpl in H.
    assert (0 <= (N.pos (N.succ_pos d)))%N.
    apply N.lt_le_incl.
    unfold N.lt. reflexivity.
    apply H in H1.
    rewrite N.pos_pred_succ in H1.
    auto.
  - assert (0 <= 0)%N.
    reflexivity.
    apply H in H0. inv H0.
Qed.

Theorem pos_testbit_nat_impossible:
  forall b,
  ~(forall d : nat, 0 <= d -> Pos.testbit_nat b d = false).
Proof.
  induction b; intro.
  - apply IHb; intros.
    assert ( 0 <= 0) by reflexivity.
    apply H in H1. inv H1.
  - apply IHb.
    intros.
    simpl in H.
    assert (0 <= S d) by omega.
    apply H in H1.
    auto.
  - assert (0 <= 0).
    reflexivity.
    apply H in H0. inv H0.
Qed.

Theorem N_lt_pos:
  forall p, (0 < N.pos p)%N.
Proof.
  intro.
  apply N2Z.inj_lt.
  simpl.
  apply Pos2Z.is_pos.
Qed.

Theorem pos_testbit_false_xI:
  forall b,
  (forall d : N, (1 <= d)%N -> Pos.testbit b~1 d = false) ->
  (forall d : N, (0 <= d)%N -> Pos.testbit b d = false).
Proof.
  intros.
  assert (1 <= (N.pos (N.succ_pos d)))%N.
  apply N2Z.inj_le.
  apply Z.lt_pred_le.
  simpl.
  apply Pos2Z.is_pos.
  apply H in H1.
  simpl in H1.
  rewrite N.pos_pred_succ in H1.
  auto.
Qed.

Theorem pos_testbit_false_xO:
  forall b,
  (forall d : N, (1 <= d)%N -> Pos.testbit b~0 d = false) ->
  (forall d : N, (0 <= d)%N -> Pos.testbit b d = false).
Proof.
  intros.
  assert (1 <= (N.pos (N.succ_pos d)))%N.
  apply N2Z.inj_le.
  apply Z.lt_pred_le.
  simpl.
  apply Pos2Z.is_pos.
  apply H in H1.
  simpl in H1.
  rewrite N.pos_pred_succ in H1.
  auto.
Qed.



Theorem pland_split_nat:
  forall c a b,
  (forall d, d < c -> Pos.testbit_nat a d = false) ->
  (forall d, c <= d -> Pos.testbit_nat b d = false) ->
                Pos.land a b = 0%N.
Proof.
  induction c; intros.
  - apply pos_testbit_nat_impossible in H0.
    inv H0.
  - destruct a.
    + (* impossible: a needs to be 0 on lower bits *)
      assert (0 < S c) by omega.
      apply H in H1.
      inv H1.
    + destruct b.
      * simpl.
        rewrite IHc; intros.
        reflexivity.
        simpl in H.
        assert (S d < S c) by omega.
        apply H in H2. auto.
        assert (S c <= S d) by omega.
        apply H0 in H2.
        simpl in H2. auto.
      * simpl.
        rewrite IHc; intros.
        reflexivity.
        simpl in H.
        assert (S d < S c) by omega.
        apply H in H2. auto.
        assert (S c <= S d) by omega.
        apply H0 in H2.
        simpl in H2. auto.
      * reflexivity.
    + (* impossible: a needs to be 0 on lower bits *)
      assert (0 < S c) by omega.
      apply H in H1.
      inv H1.
Qed.




Theorem repr_boxed_t:
   forall a t h,
     boxed_header t a h ->
   Z.land h 255 =  Z.of_N t.
Proof.
  intros. inv H.
  apply Z.bits_inj.
  unfold Z.eqf.
  intro.
  destruct H1.
  rewrite Z.land_spec.
  assert (Hcase_z:= Z.lt_ge_cases n 0%Z).
  destruct Hcase_z as [Hnz | Hnz].
  { (* testbit = false *)
    destruct n. exfalso; omega.
    exfalso. assert (0 < Z.pos p0)%Z by apply Pos2Z.pos_is_pos. omega.
    reflexivity.
  }

  assert (Hcase := Z.lt_ge_cases n 8%Z).

  destruct Hcase.
  - replace 255%Z with (Z.pred (2^8))%Z.
    rewrite <- Z.ones_equiv.
    rewrite Z.ones_spec_low.
    rewrite Bool.andb_true_r.
    rewrite Z.add_nocarry_lxor.
    rewrite Z.lxor_spec.
    rewrite OrdersEx.Z_as_OT.shiftl_spec_low.
    rewrite Bool.xorb_false_l.
    reflexivity. omega.
    (* multiple cases depending of if one is 0 or not *)
    {
      destruct (Z.shiftl (Z.of_N a) 10) eqn:Ha.
      - reflexivity.
      - destruct (Z.of_N t) eqn:Hb.
        + reflexivity.
        + simpl.
          rewrite pland_split_nat with (c := 8). reflexivity.
          * intros.
            rewrite <- Ndigits.Ptestbit_Pbit.
            destruct d. simpl.
            destruct (Z.of_N a). simpl in Ha.
            assert (0 < Z.pos p0)%Z by apply Pos2Z.pos_is_pos. omega.
            simpl in Ha. inv Ha. reflexivity.
            inv Ha.
            replace false with
                (Z.testbit (Z.pos p0)  (Z.of_nat (S d))).
            reflexivity.
            rewrite <- Ha.
            apply Z.shiftl_spec_low.
            apply Nat2Z.inj_lt in H2.
            simpl Z.of_nat in *. omega.
          * intros.
            rewrite Zpower.two_power_pos_nat in H.
            rewrite <- Ndigits.Ptestbit_Pbit.
            destruct d. exfalso; omega.
            replace false with
                (Z.testbit (Z.pos p1)  (Z.of_nat (S d))). reflexivity.
            eapply Int.Ztestbit_above.
            apply H.
            apply Nat2Z.inj_le in H2.
            replace (Pos.to_nat 8) with 8.
            omega. reflexivity.
        + destruct t; inv Hb.
      - exfalso.
        destruct H0.
        rewrite <- Z.shiftl_nonneg with (n := 10%Z) in H0.
        rewrite Ha in H0.
        assert (Hnn := Zlt_neg_0 p0). omega.
    }


    omega.
    simpl. reflexivity.
  - (* always false *)
    rewrite Bool.andb_false_intro2.
    symmetry.
    eapply Byte.Ztestbit_above with (n := 8).
    rewrite Zpower.two_power_nat_correct.
    rewrite Zpower.two_power_pos_correct in *.
    unfold Z.pow_pos in H. simpl in *.
    omega.
    simpl. omega.
    eapply Byte.Ztestbit_above with (n := 8).
    rewrite Zpower.two_power_nat_correct. simpl. omega.
    simpl. omega.
Qed.





Definition arity_of_header (h:Z): N :=
  Z.to_N (Z.shiftr h 10).

Definition tag_of_header (h:Z): N :=
    Z.to_N (Z.land h 255).



Inductive repr_asgn_constr: positive -> ctor_tag -> list positive -> statement -> Prop :=
| Rconstr_ass_boxed: forall x (t:ctor_tag) vs s a n h,
    (* boxed x *)
    M.get t rep_env = Some (boxed n a) ->
    boxed_header n a h ->
    Forall_statements_in_seq (is_nth_projection_of_x x) vs s ->
    repr_asgn_constr x t vs (x ::= [val] (allocPtr +' (c_int Z.one val));
                                     allocIdent ::= allocPtr +'
                                           (c_int (Z.of_N (a + 1)) val); Field(var x, -1) :::= c_int h val;  s)
| Rconstr_ass_enum: forall x t n h,
    (* unboxed x *)
    M.get t rep_env  = Some (enum n) ->
    repr_unboxed_Codegen n h  ->
    repr_asgn_constr x t nil (x ::= c_int h val).


Inductive repr_switch_LambdaANF_Codegen: positive -> labeled_statements -> labeled_statements -> statement -> Prop :=
| Mk_switch: forall x ls ls',
    repr_switch_LambdaANF_Codegen x ls ls'
                      (isPtr isptrIdent caseIdent x;
                         Sifthenelse
                           (bvar caseIdent)
                           (Sswitch (Ebinop Oand (Field(var x, -1)) (make_cint 255 val) val) ls)
                           (
                             Sswitch (Ebinop Oshr (var x) (make_cint 1 val) val)
                                     ls')).

(* relate a LambdaANF.exp -| ctor_env, fun_env to a series of statements in a clight program (passed as parameter) -- syntactic relation that shows the right instructions have been generated for functions body. There should not be function definitions (Efun), or primitive operations (they are not supported by our backend) in this
TODO: maybe this should be related to a state instead?
 *)

(* CHANGE THIS (relational version from translate body) *)
Inductive repr_expr_LambdaANF_Codegen: LambdaANF.term.exp -> statement -> Prop :=
| Rconstr_e:
    forall x t vs  s s' e,
    repr_asgn_constr x t vs s ->
    repr_expr_LambdaANF_Codegen e  s' ->
    repr_expr_LambdaANF_Codegen (Econstr x t vs e)  (s; s')
| Rproj_e: forall x t n v e  s,
    repr_expr_LambdaANF_Codegen e  s ->
    repr_expr_LambdaANF_Codegen (Eproj x t n v e)  (x ::= Field(var v, Z.of_N n) ; s)
| R_app_e: forall f inf ainf ys ays bys pnum (t : fun_tag) s1 s2,
    (* 1 - assign vs to the right args acording to fenv(f)*)
    M.get t fenv = Some inf ->
    ays = skipn nParam ys ->
    bys = firstn nParam ys ->
    ainf = skipn nParam (snd inf) ->
    repr_asgn_fun ays ainf s1 ->
    pnum = min (N.to_nat (fst inf)) nParam ->
    repr_call_vars pnum bys s2 ->
    (* 2 - call f *)
    (* NOTE: added redundant limitIdent |-> limitPtr to avoid having to carry this info around, but could optimize it away *)
    repr_expr_LambdaANF_Codegen (Eapp f t ys) (s1; Efield tinfd allocIdent valPtr :::= allocPtr ; Efield tinfd limitIdent valPtr  :::= limitPtr ;
                                      (Scall None ([Tpointer (mkFunTy threadInfIdent pnum) noattr] (var_or_funvar_f f)) ((Etempvar tinfIdent threadInf) :: s2)))
| R_halt_e: forall v e,
    (* halt v <-> end with v in args[1] *)
    var_or_funvar v e ->
    repr_expr_LambdaANF_Codegen (Ehalt v)  (args[Z.of_nat 1 ] :::= e)
| Rcase_e: forall v cl ls ls' s ,
    (* 1 - branches matches the lists of two lists of labeled statements *)
    repr_branches_LambdaANF_Codegen cl ls ls' ->
    (* 2 - switch-header matches  *)
    repr_switch_LambdaANF_Codegen v ls ls' s ->
    repr_expr_LambdaANF_Codegen  (Ecase v cl)  s
                     (* default case for last boxed and unboxed constructor
                        OS: perhaps want to include a *)
with repr_branches_LambdaANF_Codegen: list (ctor_tag * exp) -> labeled_statements -> labeled_statements -> Prop :=
     | Rempty_br : repr_branches_LambdaANF_Codegen nil LSnil LSnil
     | Runboxed_default_br: forall t e cl ls n s,
         repr_expr_LambdaANF_Codegen e s ->
         M.get t rep_env  = Some (enum n) ->
         repr_branches_LambdaANF_Codegen cl ls LSnil ->
         repr_branches_LambdaANF_Codegen ((t, e) ::cl) ls (LScons None  (Ssequence s Sbreak)
                                                      LSnil)
     | Runboxed_br: forall cl ls lsa' lsb' lsc' t n tag e s, repr_branches_LambdaANF_Codegen cl ls (LScons lsa' lsb' lsc') ->
                                                repr_expr_LambdaANF_Codegen e s ->
                                                M.get t rep_env  = Some (enum n) ->
                                                repr_unboxed_Codegen n tag ->
                                                repr_branches_LambdaANF_Codegen ((t, e) ::cl) ls (LScons (Some (Z.shiftr tag 1)) (Ssequence s Sbreak) (LScons lsa' lsb' lsc'))
     | Rboxed_default_br : forall cl  ls' t a n e s, repr_branches_LambdaANF_Codegen cl LSnil ls' ->
                                           repr_expr_LambdaANF_Codegen e s ->
                                           M.get t rep_env = Some (boxed n a) ->
                                           repr_branches_LambdaANF_Codegen ((t, e)::cl) (LScons None  (Ssequence s Sbreak) LSnil) ls'
     | Rboxed_br : forall cl lsa lsb lsc ls' t a n tag e s, repr_branches_LambdaANF_Codegen cl (LScons lsa lsb lsc) ls' ->
                                           repr_expr_LambdaANF_Codegen e s ->
                                           M.get t rep_env = Some (boxed n a) ->
                                           boxed_header n a tag ->
                                           repr_branches_LambdaANF_Codegen ((t, e)::cl) (LScons (Some (Z.land tag 255)) (Ssequence s Sbreak)  (LScons lsa lsb lsc)) ls'.


Theorem repr_branches_LSnil_no_unboxed:
  forall t e cl  ls,
    findtag cl t = Some e ->
    repr_branches_LambdaANF_Codegen cl ls LSnil  ->
    ~ (exists arr, M.get t rep_env = Some (enum arr)).
Proof.
  induction cl; intros.
  - inv H.
  - simpl in H. destruct a.
    destruct (M.elt_eq c t).
    + subst. inv H0; intro; destruct H0; rewrite H0 in H8; inv H8.
    + inv H0. inv H4. inv H.
      eapply IHcl; eauto.
Qed.

Theorem repr_branches_LSnil_no_boxed:
  forall t e cl  ls,
    findtag cl t = Some e ->
    repr_branches_LambdaANF_Codegen cl LSnil ls  ->
    ~ (exists arr s, M.get t rep_env = Some (boxed arr s)).
Proof.
  induction cl; intros.
  - inv H.
  - simpl in H. destruct a.
    destruct (M.elt_eq c t).
    + subst. inv H0; intro; destruct H0; destruct H0. rewrite H0 in H7; inv H7. rewrite H0 in H8; inv H8.
    + inv H0. inv H8. inv H.
      eapply IHcl; eauto.
Qed.



Definition gc_vars := ((allocIdent, valPtr)::(limitIdent, valPtr)::(argsIdent, valPtr)::(caseIdent, boolTy) ::nil).

Definition gc_set := (allocIdent ::= Efield tinfd allocIdent valPtr ;
                                                    limitIdent ::= Efield tinfd limitIdent valPtr ;
                                                    argsIdent ::= Efield tinfd argsIdent (Tarray val maxArgs noattr)).

Definition gc_test (gcArrIdent:positive) (l:N) (vs : list positive) (ind : list N) (fenv : fun_env) (finfo_env : fun_info_env) := (reserve argsIdent allocIdent limitIdent gcIdent threadInfIdent tinfIdent nParam gcArrIdent
                                                           (Z.of_N (l + 2)) vs ind fenv finfo_env).

Definition gc_test' (gcArrIdent:positive) (l:N) (vs : list positive) (ind : list N) (fenv : fun_env) (finfo_env : fun_info_env) := (reserve' argsIdent allocIdent limitIdent gcIdent threadInfIdent tinfIdent nParam gcArrIdent
                                                           (Z.of_N (l + 2)) vs ind fenv finfo_env).

Inductive right_param_asgn: list positive -> list N -> statement -> Prop :=
| asgn_nil: right_param_asgn nil nil Sskip
| asgn_cons: forall x xs n ns s,  right_param_asgn xs ns s -> right_param_asgn (x::xs) (n::ns) ((x ::= args[Z.of_N n]);s).


(* lenv' is lenv after binding xs->vs with NoDup xs *)
Definition lenv_param_asgn (lenv lenv':temp_env) (xs:list positive) (vs:list Values.val): Prop :=
  forall i, (forall z, nthN xs z  = Some i ->  M.get i lenv' = nthN vs z)
            /\
            (~ List.In i xs -> M.get i lenv' = M.get i lenv).

Inductive lenv_param_asgn_i: temp_env -> temp_env -> list positive -> list Values.val -> Prop :=
| LPA_nil: forall lenv, lenv_param_asgn_i lenv lenv [] []
| LPA_cons: forall lenv lenv' ys vs y v,
    lenv_param_asgn_i (M.set y v lenv) lenv' ys vs ->
    lenv_param_asgn_i lenv lenv' (y::ys) (v::vs).


Theorem lenv_param_asgn_i_length:
  forall ys vs lenv lenv',
    lenv_param_asgn_i lenv lenv' ys vs ->
    length ys = length vs.
Proof.
  induction ys; intros. inv H; reflexivity.
  inv H. simpl. eapply IHys in H5. auto.
Qed.


Theorem lenv_param_asgn_rel:
  forall ys vs lenv lenv',
    lenv_param_asgn_i lenv lenv' ys vs ->
    NoDup ys ->
    lenv_param_asgn lenv lenv' ys vs.
Proof.
  induction ys; intros.
  - inv H. constructor; intros. inv H. reflexivity.
  - inv H. eapply IHys in H6. split; intros; specialize (H6 i); destruct H6.
    + rewrite nthN_equation in *. destruct (var_dec a i).
      * destruct z. subst.
        rewrite H2. rewrite M.gss. reflexivity. inv H0; auto.
        apply H1 in H. auto.
      * destruct z. exfalso. inv H. apply n; auto.
        apply H1 in H. auto.
    + rewrite M.gso in H2. apply H2.
      intro. apply H. constructor 2. auto.
      intro. apply H. constructor; auto.
    + inv H0; auto.
Qed.

Theorem e_lenv_param_asgn_i:
  forall ys lenv vs,
    length ys = length vs ->
    NoDup ys ->
    exists lenv',
      lenv_param_asgn_i lenv lenv' ys vs.
Proof.
  induction ys; intros.
  - destruct vs; inv H. exists lenv. constructor.
  - destruct vs; inv H. inv H0.
    specialize (IHys  (M.set a v lenv)).
    specialize (IHys _ H2 H4).
    destruct IHys as [lenv' Hlenv'].
    eexists; constructor; eauto.
Qed.



Theorem e_lenv_param_asgn:
  forall lenv ys vs,
    length ys = length vs ->
    NoDup ys ->
    exists lenv',
      lenv_param_asgn lenv lenv' ys vs.
Proof.
  intros.
  assert (Hi := e_lenv_param_asgn_i ys lenv vs H H0).
  destruct Hi.
  apply lenv_param_asgn_rel in H1; eauto.
Qed.


Theorem get_list_nth_get' (B:Type):
  forall  (vs : list B) rho v xs  N,
  get_list xs rho = Some vs ->
  nthN vs N = Some v ->
  exists x, nthN xs N = Some x /\ M.get x rho = Some v.
Proof.
  induction vs; intros; destruct xs.
  inv H0. inv H0.
  simpl in H. inv H.
  rewrite nthN_equation in H0.
  destruct N.
  - inv H0. simpl in H.
    exists e. split. reflexivity.
    destruct (M.get e rho).
    destruct (get_list xs rho). inv H; auto.
    inv H. inv H.
  - simpl in H. destruct (M.get e rho).
    destruct (get_list xs rho) eqn:Hxs. inv H.
    specialize (IHvs _ _ _ _ Hxs H0).
    rewrite nthN_equation. auto. inv H.
    inv H.
Qed.


Theorem in_rho_entry:
  forall xs vs fl rho x v,
  set_lists xs vs (def_funs fl fl (M.empty term.val) (M.empty term.val)) = Some rho ->
  NoDup xs ->
  M.get x rho = Some v ->
  (exists n, nthN xs n = Some x /\ nthN vs n = Some v) \/
  (exists t ys b, ~List.In x xs /\  find_def x fl = Some (t, ys, b) /\ v = Vfun (M.empty term.val) fl x).
Proof.
  intros.
  assert (decidable (List.In x xs)). apply In_decidable. apply shrink_cps_correct.var_dec_eq.
  inv H2.
  - left.
    assert (Hgl := get_list_set_lists _ _ _ _  H0 H ).
    apply In_nthN in H3. destruct H3.
    assert (Hgl' := get_list_nth_get _ _ _ _ _ Hgl H2).
    destruct Hgl'.
    destruct H3.
    exists x0.
    rewrite H4 in H1; inv H1.
    split; auto.
  - right.
    erewrite <- set_lists_not_In in H1; eauto.
    assert (decidable (name_in_fundefs fl x)). unfold decidable. assert (Hd := Decidable_name_in_fundefs fl). inv Hd. specialize (Dec x). inv Dec; auto.
    inv H2.
    + assert (H4' := H4).
      eapply def_funs_eq in H4.
      rewrite H1 in H4.
      inv H4.
      apply name_in_fundefs_find_def_is_Some in H4'.
      destruct H4' as [ft [ys [e Hfd]]].
      exists ft, ys, e; eauto.
    +  erewrite def_funs_neq in H1; eauto.
       rewrite M.gempty in H1; inv H1.
Qed.




Inductive repr_val_LambdaANF_Codegen:  LambdaANF.term.val -> mem -> Values.val -> Prop :=
| Rint_v: forall  z r m,
    repr_unboxed_Codegen (Z.to_N z) r ->
    repr_val_LambdaANF_Codegen (LambdaANF.term.Vint z) m (make_vint r)
| Rconstr_unboxed_v:
    forall t arr n m,
      M.get t rep_env = Some (enum arr) ->
      repr_unboxed_Codegen arr n ->
      repr_val_LambdaANF_Codegen (LambdaANF.term.Vconstr t nil) m  (make_vint n)
| Rconstr_boxed_v: forall  t vs n a b i m h,
    (* t is a boxed constructor, n ends with 0 and represents
      a pointer to repr_val_ptr of (t, vs)  *)
    M.get t rep_env = Some (boxed n a) ->
    (* 1) well-formedness of the header block *)

    Mem.load int_chunk m b (Ptrofs.unsigned (Ptrofs.sub i (Ptrofs.repr int_size))) = Some (make_vint h) ->
    boxed_header n a h ->
    (* 2) all the fields are also well-represented *)
    repr_val_ptr_list_LambdaANF_Codegen vs m b i ->
    repr_val_LambdaANF_Codegen (LambdaANF.term.Vconstr t vs) m  (Vptr b i)
| Rfunction_v:
    forall vars avars fds f m b t t' vs pvs avs alocs e asgn body l locs finfo gccall,
      let F := mkfunction (Tvoid)
                          ((mkcallconv false false false)) (*({| cc_vararg := false; cc_unproto := false; cc_structret := false |})*)
             ((tinfIdent, threadInf)::(map (fun x => (x , val)) pvs))
             (nil)
             (List.app avars gc_vars)
             (Ssequence gccall (Ssequence (Ssequence gc_set asgn)
                                          body)) in
      find_def f fds = Some (t, vs, e) ->
      M.get t fenv = Some (l, locs) ->
      M.get f finfo_env = Some (finfo , t') -> (* TODO: check this *)
      t = t' ->
      Genv.find_symbol (Genv.globalenv p) f = Some b -> (* symbol f points to b in the globalenv *)
      (* b points to an internal function in the heap [and i is 0] *)
      gc_test' finfo l vs locs fenv finfo_env = Some gccall ->
      Genv.find_funct (globalenv p) (Vptr b  Ptrofs.zero) = Some (Internal F) ->
      (* F should have the shape that we expect for functions generated by our compiler,
       > see translate_fundefs i.e.
        - returns a Tvoid *)
      (*
       - calling convention?
        - only param is the threadinfo (tinfIdent of type threadInf) *)
       (*
        - all the vars match + the 3 gc vars *)

       (* - no temps *)
       (*
        - function header: threadInfo, gc check, load parameters,  then body equivalent to e (related according to repr_exp_LambdaANF_Codegen)
        *)
      Forall2 (fun x xt =>  xt = (x, val))  vs vars  ->
      pvs = firstn nParam vs ->
      avs = skipn nParam vs ->
      alocs = skipn nParam locs ->
      avars = skipn nParam vars ->
      right_param_asgn avs alocs asgn ->
      repr_expr_LambdaANF_Codegen e body ->
      repr_val_LambdaANF_Codegen (term.Vfun (M.empty term.val) fds f) m (Vptr b Ptrofs.zero)
with repr_val_ptr_list_LambdaANF_Codegen: (list LambdaANF.term.val) -> mem -> block -> ptrofs -> Prop :=
     | Rnil_l:
         forall m b i,
           repr_val_ptr_list_LambdaANF_Codegen nil m b i
     | Rcons_l:
         forall v vs m b i v7,
           Mem.load int_chunk m b (Ptrofs.unsigned  i) = Some v7 ->
           repr_val_LambdaANF_Codegen v m v7 ->
           repr_val_ptr_list_LambdaANF_Codegen vs m b (Ptrofs.add i (Ptrofs.repr int_size)) ->
           repr_val_ptr_list_LambdaANF_Codegen (v::vs) m b i.



Definition locProp := block -> Z -> Prop.


(* m and m' are the _same_ over subheap L *)

Definition sub_locProp: locProp -> locProp -> Prop :=
  fun L L' => forall b ofs, L b ofs -> L' b ofs.



(* CHANGE THIS *)
Inductive repr_val_L_LambdaANF_Codegen:  LambdaANF.term.val -> mem -> locProp -> Values.val -> Prop :=
| RSint_v: forall L z r m,
    repr_unboxed_Codegen (Z.to_N z) r ->
    repr_val_L_LambdaANF_Codegen (LambdaANF.term.Vint z) m L (make_vint r)
| RSconstr_unboxed_v:
    forall t arr n m L,
      M.get t rep_env = Some (enum arr) ->
      repr_unboxed_Codegen arr n ->
      repr_val_L_LambdaANF_Codegen (LambdaANF.term.Vconstr t nil) m L (make_vint n)
| RSconstr_boxed_v: forall (L:block -> Z -> Prop) t vs n a b i m h,
    (* t is a boxed constructor, n ends with 0 and represents
      a pointer to repr_val_ptr of (t, vs)  *)
    M.get t rep_env = Some (boxed n a) ->
    (forall j : Z, (Ptrofs.unsigned (Ptrofs.sub i (Ptrofs.repr int_size)) <= j <
   Ptrofs.unsigned (Ptrofs.sub i (Ptrofs.repr int_size)) + size_chunk int_chunk)%Z  -> L b j%Z) ->
    (* 1) well-formedness of the header block *)

    Mem.load int_chunk m b (Ptrofs.unsigned (Ptrofs.sub i (Ptrofs.repr int_size))) = Some (make_vint h) ->
    boxed_header n a h ->
    (* 2) all the fields are also well-represented *)
    repr_val_ptr_list_L_LambdaANF_Codegen vs m L b i ->
    repr_val_L_LambdaANF_Codegen (LambdaANF.term.Vconstr t vs) m L (Vptr b i)
| RSfunction_v:
    forall (L:block -> Z -> Prop)  vars avars fds f m b t t' vs pvs avs e asgn body l locs alocs finfo gccall,
      let F := mkfunction (Tvoid)
                          ((mkcallconv false false false)) (*({| cc_vararg := false; cc_unproto := false; cc_structret := false |})*)
             ((tinfIdent, threadInf)::(map (fun x => (x , val)) pvs))
             (nil)
             (List.app avars gc_vars)
             (Ssequence gccall (Ssequence (Ssequence gc_set asgn)
                                          body)) in
      find_def f fds = Some (t, vs, e) ->
      M.get t fenv = Some (l, locs) ->
      M.get f finfo_env = Some (finfo , t') -> (* TODO: check this *)
      t = t' ->
      Genv.find_symbol (Genv.globalenv p) f = Some b -> (* symbol f points to b in the globalenv *)
      (* b points to an internal function in the heap [and i is 0] *)
      gc_test' finfo l vs locs fenv finfo_env = Some gccall ->
      Genv.find_funct (globalenv p) (Vptr b  Ptrofs.zero) = Some (Internal F) ->
      (* F should have the shape that we expect for functions generated by our compiler,
       > see translate_fundefs i.e.
        - returns a Tvoid *)
      (*
       - calling convention?
        - only param is the threadinfo (tinfIdent of type threadInf) *)
       (*
        - all the vars match + the 3 gc vars *)

       (* - no temps *)
       (*
        - function header: threadInfo, gc check, load parameters,  then body equivalent to e (related according to repr_exp_LambdaANF_Codegen)
        *)
      Forall2 (fun x xt =>  xt = (x, val))  vs vars  ->
      pvs = firstn nParam vs ->
      avs = skipn nParam vs ->
      alocs = skipn nParam locs ->
      avars = skipn nParam vars ->
      right_param_asgn avs alocs asgn ->
      repr_expr_LambdaANF_Codegen e body ->
      repr_val_L_LambdaANF_Codegen (term.Vfun (M.empty term.val) fds f) m L (Vptr b Ptrofs.zero)
with repr_val_ptr_list_L_LambdaANF_Codegen: (list LambdaANF.term.val) -> mem -> locProp -> block -> ptrofs -> Prop :=
     | RSnil_l:
         forall m L b i,
           repr_val_ptr_list_L_LambdaANF_Codegen nil m L b i
     | RScons_l:
         forall v vs m (L:block -> Z -> Prop) b i v7,
           (forall j : Z, ((Ptrofs.unsigned i) <= j < (Ptrofs.unsigned i) + int_size)%Z -> L b j) ->
           Mem.load int_chunk m b (Ptrofs.unsigned i) = Some v7 ->
           repr_val_L_LambdaANF_Codegen v m L v7 ->
           repr_val_ptr_list_L_LambdaANF_Codegen vs m L b (Ptrofs.add i (Ptrofs.repr int_size)) ->
           repr_val_ptr_list_L_LambdaANF_Codegen (v::vs) m L b i.

Scheme repr_val_L_LambdaANF_Codegen_rec := Induction for repr_val_L_LambdaANF_Codegen Sort Prop
  with repr_val_ptr_list_L_LambdaANF_Codegen_rec := Induction for repr_val_ptr_list_L_LambdaANF_Codegen Sort Prop.



Inductive  repr_val_ptr_list_L_LambdaANF_Codegen_Z: (list LambdaANF.term.val) -> mem -> locProp -> block -> Z -> Prop :=
     | RSnil_l_Z:
         forall m L b i,
           repr_val_ptr_list_L_LambdaANF_Codegen_Z nil m L b i
     | RScons_l_Z:
         forall v vs m (L:block -> Z -> Prop) b i v7,
           (forall j : Z, (i <= j < i + int_size)%Z -> L b j) ->
           Mem.load int_chunk m b i = Some v7 ->
           repr_val_L_LambdaANF_Codegen v m L v7 ->
           repr_val_ptr_list_L_LambdaANF_Codegen_Z vs m L b (i+ int_size)%Z ->
           repr_val_ptr_list_L_LambdaANF_Codegen_Z (v::vs) m L b i.






(*
Theorem repr_val_forall_L_fun:
  forall L fds f m b,
  repr_val_ptr_LambdaANF_Codegen (term.Vfun (M.empty term.val) fds f) m (b,Int.zero) <-> repr_val_L_LambdaANF_Codegen (term.Vfun (M.empty term.val) fds f) m L (Vptr b Int.zero).
Proof.
  intros. split; intro H; inv H; econstructor; eauto.
Qed.   *)

Theorem repr_val_ptr_list_Z:
  forall m L b vs i,
    uint_range ((Ptrofs.unsigned i) + (Z.of_nat (length vs)* int_size))%Z ->
  repr_val_ptr_list_L_LambdaANF_Codegen vs m L b i <-> repr_val_ptr_list_L_LambdaANF_Codegen_Z vs m L b (Ptrofs.unsigned i).
Proof.
  induction vs; intros.
  - split; intro; constructor.
  - assert  (Hi4 : (Ptrofs.unsigned i + int_size)%Z = (Ptrofs.unsigned (Ptrofs.add i (Ptrofs.repr int_size)))).
    {
      unfold int_size in *; simpl size_chunk in *.
      rewrite Ptrofs.add_unsigned.
      rewrite Ptrofs.unsigned_repr.
      rewrite Ptrofs.unsigned_repr. reflexivity.
      compute; destruct Archi.ptr64; split; intros Hlt; inv Hlt.


      rewrite Ptrofs.unsigned_repr.
      simpl length in H.
      rewrite Nat2Z.inj_succ in H.
      rewrite Z.mul_succ_l in H.
      assert (0 <= Z.of_nat (length vs))%Z.
      apply Zle_0_nat.
      rewrite Z.add_assoc in H.
      assert (0 <= Ptrofs.unsigned i)%Z by apply Ptrofs.unsigned_range.
      inv H. split. apply OrdersEx.Z_as_OT.add_nonneg_nonneg. auto.
      chunk_red; omega. chunk_red; omega. compute; destruct Archi.ptr64; split; intros Hlt; inv Hlt.
      }
    split; intro; inv H0.
    + econstructor; eauto; unfold int_size in *; simpl size_chunk in *.
      apply IHvs in H10.
      rewrite Hi4.
      auto.
      rewrite <- Hi4.

      simpl length in H.
      rewrite Nat2Z.inj_succ in H.

      assert (0 <= Ptrofs.unsigned i)%Z by apply Ptrofs.unsigned_range.
      assert (0 <= Z.of_nat (length vs))%Z by       apply Zle_0_nat.
      inv H.
      rewrite Z.mul_succ_l in H7.
      rewrite Z.add_assoc in H7.
      split; chunk_red; omega.
    + econstructor; eauto.
      unfold int_size in *; simpl size_chunk in *.
      apply IHvs.
      rewrite <- Hi4.
      simpl length in H.
      rewrite Nat2Z.inj_succ in H.
      assert (0 <= Ptrofs.unsigned i)%Z by apply Ptrofs.unsigned_range.
      assert (0 <= Z.of_nat (length vs))%Z by       apply Zle_0_nat.
      inv H.
      rewrite Z.mul_succ_l in H6.
      rewrite Z.add_assoc in H6.
      split; chunk_red; omega.
      rewrite <- Hi4. auto.
Qed.




(* this is the sum of get_var_or_funvar and repr_val_L_LambdaANF_Codegen (-> and <-\-) *)
Inductive repr_val_id_L_LambdaANF_Codegen: LambdaANF.term.val -> mem -> locProp -> temp_env -> positive -> Prop :=
| RVid_F:
   forall b f lenv fds L m,
     Genv.find_symbol (Genv.globalenv p) f = Some b ->
     repr_val_L_LambdaANF_Codegen (term.Vfun (M.empty term.val) fds f) m L (Vptr b (Ptrofs.zero)) ->
     repr_val_id_L_LambdaANF_Codegen (term.Vfun (M.empty term.val) fds f) m L lenv f
| RVid_V:
    forall x m lenv L v6 v7,
      Genv.find_symbol (Genv.globalenv p) x = None ->
      M.get x lenv = Some v7 ->
      repr_val_L_LambdaANF_Codegen v6 m L v7 ->
      repr_val_id_L_LambdaANF_Codegen v6 m L lenv x.


Theorem repr_val_id_L_LambdaANF_Codegen_vint_or_vptr:
  forall v6 m L v7,
  repr_val_L_LambdaANF_Codegen v6 m L v7 ->
  Vint_or_Vptr v7 = true.
Proof.
  intros; inv H; auto.
Qed.


(* If v is needed *)
Theorem repr_val_id_L_LambdaANF_Codegen_ptr:
  forall v6 m L lenv x,
  repr_val_id_L_LambdaANF_Codegen v6 m L lenv x ->
  exists v7, repr_val_L_LambdaANF_Codegen v6 m L v7 /\
            ((M.get x lenv = Some v7 /\
             Genv.find_symbol (Genv.globalenv p) x = None)
             \/
             (exists b, v7 = Vptr b Ptrofs.zero /\
                        Genv.find_symbol (Genv.globalenv p) x = Some b)).
Proof.
  intros. inv H.
  - exists (Vptr b (Ptrofs.zero)). split; auto.
    right. exists b; auto.
  - exists v7. split; auto.
Qed.


Theorem get_var_or_funvar_eval:
  forall lenv a v m,
    find_symbol_domain finfo_env ->
    finfo_env_correct ->
    get_var_or_funvar lenv a v ->
    eval_expr (globalenv p) empty_env lenv m (var_or_funvar_f   a) v.
Proof.
  intros. specialize (H a). inv H. unfold var_or_funvar_f. inv H1.
  - rewrite H. destruct (H3 (ex_intro _ b H)).
    unfold makeVar. rewrite H1.
    destruct x.
    specialize (H0 _ _ f H1).
    destruct H0. destruct x.
    rewrite H0.
    econstructor. constructor 2.
    apply M.gempty. eauto.
    constructor. auto.
  - rewrite H. constructor. auto.
Qed.

Theorem get_var_or_funvar_semcast:
  forall v a m lenv,
    find_symbol_domain finfo_env ->
    finfo_env_correct ->
    get_var_or_funvar lenv a v ->
    sem_cast v (typeof (var_or_funvar_f a)) uval m = Some v.
Proof.
  intros. unfold var_or_funvar_f. specialize (H a). inv H. inv H1.
  - rewrite H. destruct (H3 (ex_intro _ b H)).
    unfold makeVar. rewrite H1.
    destruct x.
    specialize (H0 _ _ f H1).
    destruct H0. destruct x.
    rewrite H0.
    constructor.
  - rewrite H. destruct v; inv H5; auto.
Qed.

Theorem repr_val_id_implies_var_or_funvar:
  forall v6 m L lenv x,
  repr_val_id_L_LambdaANF_Codegen v6 m L lenv x ->
  exists v7, get_var_or_funvar lenv x v7 /\
             repr_val_L_LambdaANF_Codegen v6 m L v7.
Proof.
  intros. inv H.
  - exists (Vptr b Ptrofs.zero).
    split. constructor; auto.
    auto.
  - exists v7.
    split. constructor 2; auto. inv H2; auto.
    auto.
Qed.

Theorem repr_val_id_set:
  forall v6 m L lenv x,
    repr_val_id_L_LambdaANF_Codegen v6 m L lenv x ->
    forall x0 v,
    x <> x0 ->
    repr_val_id_L_LambdaANF_Codegen v6 m L (M.set x0 v lenv) x.
Proof.
  intros. inv H.
  - econstructor; eauto.
  - econstructor 2; eauto.
    rewrite M.gso; auto.
Qed.

Scheme repr_val_ind' := Minimality for repr_val_L_LambdaANF_Codegen Sort Prop
  with repr_val_list_ind' := Minimality for repr_val_ptr_list_L_LambdaANF_Codegen Sort Prop.
 (* Combined Scheme repr_val_L_LambdaANF_Codegen_mutind from repr_val_L_LambdaANF_Codegen_ind, repr_val_ptr_list_L_LambdaANF_Codegen_ind. *)

Theorem nthN_pos_pred:
  forall {A} (a:A) vs v6 p0,
  nthN (a :: vs) (N.pos p0) = Some v6 ->
  nthN vs (N.pred (N.pos p0)) = Some v6.
Proof.
  intros. destruct p0; auto.
Qed.

Theorem Z_mul_4:
  forall p,
   Z.pos p~0~0 = (4 * Z.pos p)%Z.
Proof.
  intro.
  replace ((xO (xO p0))) with (Zpower.shift 2%Z p0) by reflexivity.
  rewrite Zpower.shift_equiv; auto. omega.
Qed.


Theorem repr_val_ptr_list_L_Z_nth:
  forall {m L  v6 vs n b i},
 repr_val_ptr_list_L_LambdaANF_Codegen_Z vs m L b i ->
 nthN vs n = Some v6 ->
 exists v7, Mem.load int_chunk m b (i + (Z.of_N n * int_size))  = Some v7 /\
 repr_val_L_LambdaANF_Codegen v6 m L v7.
Proof.
  induction vs; intros. inv H0.
  inv H.
  destruct n. simpl in H0. inv H0.
  exists v7.
  simpl. rewrite Z.add_0_r. auto.
  apply nthN_pos_pred in H0.
  eapply IHvs in H0; eauto. destruct H0. exists x. inv H.
  split; auto.
  rewrite N2Z.inj_pred in H0. 2: apply N_lt_pos. rewrite Z.mul_pred_l in H0.
  replace (i +  int_size + (Z.of_N (N.pos p0) *  int_size -  int_size))%Z with (i + Z.of_N (N.pos p0) *  int_size)%Z in H0 by (chunk_red; omega).
  auto.
Qed.


Theorem repr_val_ptr_list_L_nth:
  forall {m L  v6 vs n b i},
 repr_val_ptr_list_L_LambdaANF_Codegen vs m L b i ->
 nthN vs n = Some v6 ->
 exists v7, Mem.load int_chunk m b (Ptrofs.unsigned (Ptrofs.add i (Ptrofs.mul (Ptrofs.repr (Z.of_N n)) (Ptrofs.repr int_size))))  = Some v7 /\
 repr_val_L_LambdaANF_Codegen v6 m L v7.
Proof.
  induction vs; intros. inversion H0.
  destruct n.
  - simpl. inv H0.
    inv H.
    rewrite Ptrofs.add_zero.
    exists v7; auto.
  - simpl.
    inv H.
    apply nthN_pos_pred in H0.
    specialize (IHvs _ _ _ H10 H0).
    destruct IHvs. destruct H.
    exists x; split; auto.
    replace (Ptrofs.unsigned
           (Ptrofs.add (Ptrofs.add i (Ptrofs.repr int_size))
              (Ptrofs.mul (Ptrofs.repr (Z.of_N (N.pred (N.pos p0))))
                       (Ptrofs.repr int_size)))) with
        (Ptrofs.unsigned
           (Ptrofs.add i (Ptrofs.mul (Ptrofs.repr (Z.pos p0)) (Ptrofs.repr int_size)))) in H.
    auto.
    rewrite Ptrofs.add_assoc.
    unfold Ptrofs.mul.
    unfold Ptrofs.add.
    erewrite  Ptrofs.eqm_samerepr.
    reflexivity.
    apply Ptrofs.eqm_add.
    apply Ptrofs.eqm_refl.
    eapply Ptrofs.eqm_trans.
    apply Ptrofs.eqm_unsigned_repr_l.
    2:{
    apply Ptrofs.eqm_unsigned_repr_r.
    apply Ptrofs.eqm_refl. }
    rewrite Z.add_comm.
    rewrite N2Z.inj_pred by (unfold N.lt; auto).
    int_red.
    rewrite N2Z.inj_pos.
    eapply Ptrofs.eqm_trans.
    apply Ptrofs.eqm_mult.
    apply Ptrofs.eqm_unsigned_repr_l.
    apply Ptrofs.eqm_refl.
    apply Ptrofs.eqm_unsigned_repr_l.
    apply Ptrofs.eqm_refl.
    eapply Ptrofs.eqm_trans.
    2:{
    apply Ptrofs.eqm_add.
    apply Ptrofs.eqm_unsigned_repr_r.
    apply Ptrofs.eqm_mult.
    apply Ptrofs.eqm_unsigned_repr_r.
    apply Ptrofs.eqm_refl.
    apply Ptrofs.eqm_unsigned_repr_r.
    apply Ptrofs.eqm_refl.
    apply Ptrofs.eqm_unsigned_repr_r.
    apply Ptrofs.eqm_refl. }
    rewrite Z.mul_pred_l.
    apply Ptrofs.eqm_refl2. omega.
Qed.



Theorem repr_val_L_unchanged:
  forall v6 m L v7,
  repr_val_L_LambdaANF_Codegen v6 m L v7 ->
  forall m', Mem.unchanged_on L m m' ->
  repr_val_L_LambdaANF_Codegen v6 m' L v7.
Proof.
  apply (repr_val_ind' (fun v m L v7 => forall m', Mem.unchanged_on L m m' -> repr_val_L_LambdaANF_Codegen v m' L v7)
                       (fun vs m L b i => forall m', Mem.unchanged_on L m m' -> repr_val_ptr_list_L_LambdaANF_Codegen vs m' L b i)); intros; try (now econstructor; eauto).
  - specialize (H4 _ H5).
    econstructor; eauto.
    eapply Mem.load_unchanged_on; eauto.
  - econstructor; eauto.
    eapply Mem.load_unchanged_on; eauto.
Qed.

Theorem repr_val_id_L_unchanged:
  forall v6 m lenv L x,
  repr_val_id_L_LambdaANF_Codegen v6 m L lenv x ->
  forall m', Mem.unchanged_on L m m' ->
  repr_val_id_L_LambdaANF_Codegen v6 m' L lenv x.
Proof.
    intros. inv H.
  - econstructor; eauto. eapply repr_val_L_unchanged; eauto.
  - econstructor 2; eauto.
    eapply repr_val_L_unchanged; eauto.
Qed.

Theorem repr_val_ptr_list_L_unchanged:
  forall vs m L b i,
    repr_val_ptr_list_L_LambdaANF_Codegen vs m L b i ->
forall m', Mem.unchanged_on L m m' -> repr_val_ptr_list_L_LambdaANF_Codegen vs m' L b i.
Proof.
  apply (repr_val_list_ind' (fun v m L v7 => forall m', Mem.unchanged_on L m m' -> repr_val_L_LambdaANF_Codegen v m' L v7)
                       (fun vs m L b i => forall m', Mem.unchanged_on L m m' -> repr_val_ptr_list_L_LambdaANF_Codegen vs m' L b i)); intros; try (now econstructor; eauto).
  - specialize (H4 _ H5).
    econstructor; eauto.
    eapply Mem.load_unchanged_on; eauto.
  - econstructor; eauto.
    eapply Mem.load_unchanged_on; eauto.
Qed.

Corollary repr_val_ptr_list_L_Z_unchanged:
  forall vs m L b i,
    repr_val_ptr_list_L_LambdaANF_Codegen_Z vs m L b i ->
forall m', Mem.unchanged_on L m m' -> repr_val_ptr_list_L_LambdaANF_Codegen_Z vs m' L b i.
Proof.
  induction vs; intros.
  constructor.
  inv H. econstructor; eauto.
  eapply Mem.load_unchanged_on; eauto.
  eapply repr_val_L_unchanged; eauto.
Qed.

Theorem repr_val_L_sub_locProp:
    forall v6 m L v7,
  repr_val_L_LambdaANF_Codegen v6 m L v7 ->
  forall L', sub_locProp L L' ->
  repr_val_L_LambdaANF_Codegen v6 m L' v7.
Proof.
  apply (repr_val_ind' (fun v6 m L v7 => forall L', sub_locProp L L' ->
                                                   repr_val_L_LambdaANF_Codegen v6 m L' v7)
                       (fun vs m L b i => forall L', sub_locProp L L' ->  repr_val_ptr_list_L_LambdaANF_Codegen vs m L' b i)); intros; try (now econstructor; eauto).
Qed.

Theorem repr_val_id_L_sub_locProp:
  forall v6 m L x lenv,
    repr_val_id_L_LambdaANF_Codegen v6 m L lenv x ->
    forall L', sub_locProp L L' ->
               repr_val_id_L_LambdaANF_Codegen v6 m L' lenv x.
Proof.
  intros. inv H.
  - econstructor; eauto. eapply repr_val_L_sub_locProp; eauto.
  - econstructor 2; eauto.
    eapply repr_val_L_sub_locProp; eauto.
Qed.


Theorem repr_val_ptr_list_L_sub_locProp:
    forall vs m L b i,
      repr_val_ptr_list_L_LambdaANF_Codegen vs m L b i ->
      forall L', sub_locProp L L' ->
                 repr_val_ptr_list_L_LambdaANF_Codegen vs m L' b i.
Proof.
  apply (repr_val_list_ind' (fun v6 m L v7 => forall L', sub_locProp L L' ->
                                                   repr_val_L_LambdaANF_Codegen v6 m L' v7)
                       (fun vs m L b i => forall L', sub_locProp L L' ->  repr_val_ptr_list_L_LambdaANF_Codegen vs m L' b i)); intros; try (now econstructor; eauto).
Qed.

Corollary repr_val_ptr_list_L_Z_sub_locProp:
    forall vs m L b i,
      repr_val_ptr_list_L_LambdaANF_Codegen_Z vs m L b i ->
      forall L', sub_locProp L L' ->
                 repr_val_ptr_list_L_LambdaANF_Codegen_Z vs m L' b i.
Proof.
  induction vs; intros.
  -  constructor.
  - inv H. econstructor; eauto.
    eapply repr_val_L_sub_locProp; eauto.
Qed.




(*
Returns True if the pointer Vptr q_b q_ofs is reachable by crawling v7
Assumes correct memory layout (i.e. repr_val_LambdaANF_Codegen v6 m v7)
 *)
Fixpoint reachable_val_Codegen (v6:LambdaANF.term.val) (m:mem) (v7:Values.val) (q_b:block) (q_ofs:ptrofs): Prop :=
  match v6, v7 with
  | LambdaANF.term.Vint z, Vint r => False
  | LambdaANF.term.Vconstr t vs, Vptr b i =>
    (fst (List.fold_left (fun curr v =>
                            let '(p, (p_b, p_ofs)) := curr in
                            (match Val.cmpu_bool (Mem.valid_pointer m) Ceq (Vptr p_b p_ofs) (Vptr q_b q_ofs) with
                             | Some true => (True, (p_b, (Ptrofs.add p_ofs (Ptrofs.repr (sizeof (M.empty composite) val)))))
                             | _ =>
                               (match Mem.load int_chunk m p_b (Ptrofs.unsigned p_ofs) with
                                | Some v7 =>
                                  (reachable_val_Codegen v m v7 q_b q_ofs, (p_b, (Ptrofs.add p_ofs (Ptrofs.repr (sizeof (M.empty composite) val)))))
                                | _ => curr
                                end)
                             end))
                        vs (False, (b,i))))
  | (LambdaANF.term.Vfun rho fds f), Vptr b i => False
  | _, _ => False
  end.



(*
Theorem repr_val_load_result: forall v6 m v7,
    repr_val_LambdaANF_Codegen v6 m (Val.load_result int_chunk v7)
                   <->
  repr_val_LambdaANF_Codegen v6 m v7.
Proof.
  intros.
  destruct v7; split; intro H; inv H; simpl in *; econstructor; eauto.
Qed.   *)

Theorem repr_val_L_load_result: forall v6 m v7 L,
    repr_val_L_LambdaANF_Codegen v6 m L (Val.load_result int_chunk v7)
                   <->
  repr_val_L_LambdaANF_Codegen v6 m L v7.
Proof.
  intros.
  unfold Val.load_result in *. unfold int_chunk in *.
  destruct Archi.ptr64 eqn:Harch;
  destruct v7; split; intro H; try (inv H; simpl in *; unfold make_vint; try (rewrite Harch); econstructor; eauto).
  apply repr_val_id_L_LambdaANF_Codegen_vint_or_vptr in H. simpl in H. rewrite Harch in H. inv H.
Qed.





(* the memory blocks in the sequence (b, i), (b, i+off) ... (b, i+((n-1)*off)) are pairwise related with the sequence (b', i'), (b', i'+off) ... (b', i'+(n-1*off))  *)
Inductive For_N_blocks (P:(block * ptrofs) -> (block * ptrofs) -> Prop) (loc:block * ptrofs) (loc':block * ptrofs) (off: ptrofs) :  nat -> Prop :=
| FNb_O: For_N_blocks P loc loc' off 0
| FNb_S: forall n,
    P (fst loc, Ptrofs.add (snd loc) (Ptrofs.mul off (Ptrofs.repr (Z.of_nat n)))) (fst loc', Ptrofs.add (snd loc') (Ptrofs.mul off (Ptrofs.repr (Z.of_nat n)))) ->
    For_N_blocks P  loc loc' off n ->
    For_N_blocks P loc  loc' off (S n).


(* Related (deep copy) vals that may have been moved by the GC, in such way that they can be used in place of the other in repr_val_ptr_LambdaANF_Codegen
 *)
Inductive related_boxed_Codegen: mem -> (block *  ptrofs) -> mem -> (block *  ptrofs) -> Prop :=
| SV_constr_boxed :
    forall m m' b i b' i' h h' n a,
    (* same tag *)
      Mem.load int_chunk m b (Ptrofs.unsigned (Ptrofs.sub i Ptrofs.one)) = Some (make_vint h) ->
      boxed_header n a  h ->
      Mem.load int_chunk m' b' (Ptrofs.unsigned (Ptrofs.sub i' Ptrofs.one)) = Some (make_vint h') ->
      boxed_header n a  h' ->
      (* each of the a (arrity) fields are either same int shifted+1, same function or pointers (0-ended) related according to same_boxed *)
      For_N_blocks (fun loc loc' => related_boxed_or_same_val_Codegen m loc m' loc') (b,i) (b', i') (Ptrofs.repr (sizeof (M.empty composite) val)) (N.to_nat a) ->
      related_boxed_Codegen m (b,i) m' (b', i')
with related_boxed_or_same_val_Codegen: mem -> (block *  ptrofs) -> mem -> (block * ptrofs) -> Prop :=
     | RBSI_fun :
         (* same fun *)
         forall m m' b i b' i' F,
           b = b' /\ i = i' ->
           Genv.find_funct (globalenv p) (Vptr b i) = Some (Internal F) ->
           related_boxed_or_same_val_Codegen m (b,i) m' (b', i')
     | RBSI_int :
         (* same int/unboxed constructor *)
         forall m b i n m' b' i' h,
           Mem.load int_chunk m b (Ptrofs.unsigned i) = Some (make_vint h) ->
           Mem.load int_chunk m' b' (Ptrofs.unsigned i') = Some (make_vint h) ->
           repr_unboxed_Codegen n h ->
           related_boxed_or_same_val_Codegen m (b,i) m' (b', i')
     | RBSI_pointer:
         forall m b i  m' b' i' b1 i1 b2 i2,
         Mem.load int_chunk m b (Ptrofs.unsigned i) = Some (Vptr b1 i1) ->
         Mem.load int_chunk m' b' (Ptrofs.unsigned i') = Some (Vptr b2 i2) ->
         (* TODO: may be Vint h and h' that needs to be interpreted as pointers inside m *)
         (* TODO: make sure that *)
         related_boxed_Codegen m (b1, i1) m' (b2,i2) ->
         related_boxed_or_same_val_Codegen m (b,i) m' (b', i').

(* TODO: related or boxed which also checks that what is reachable is in L *)
(*
Inductive val_tree: Type :=
| u_c_leaf :  int -> val_tree
| f_leaf : block -> int -> val_tree
| b_c_node :
    (* header *) int ->
                 list val_tree -> val_tree.

Fixpoint eq_val_trees (v1:val_tree) (v2:val_tree): bool :=
  match v1, v2 with
  | u_c_leaf i1, u_c_leaf i2 => Int.eq i1 i2
  | f_leaf b1 ofs1, f_leaf b2 ofs2 =>
    andb (Pos.eqb b1 b2) (Int.eq ofs1 ofs2)
  | b_c_node h1 l1, b_c_node h2 l2 =>
    andb (Int.eq h1 h2) (utils.forallb2 eq_val_trees l1 l2)
  | _ , _ => false
  end.



(* need either fuel or assumption that blocks are increasing when allocated [thus decreasing while traversing]
   fuel bounds the depth of the tree
*)
Fixpoint load_val_tree (m:mem) (v:Values.val) (fuel:nat) : option val_tree :=
  match fuel with
  | S fuel' =>
    (match v with
     | (Vptr b' i') =>
       if (Mem.valid_pointer m b' (Int.unsigned i')) then
         (* this is a b_c, load the header and then the rest of the tree *)
         (match Mem.load int_chunk m b' ((Int.unsigned i') - int_size) with
          | Some (Vint h) =>
            (* get arity from header *)
            let n := arity_of_header (Int.unsigned h) in
            (*
            let fix load_val_tree_ptr (m:mem) (b:block) (ofs:Z) (i:nat): option (list val_tree) :=
                (match i with
                | 0 =>  Some nil
                | S i' =>
                  (match Mem.load int_chunk m b ofs with
                   | Some v =>
                     (match load_val_tree m v fuel, load_val_tree_ptr m b (ofs + int_size)%Z i' with
                      | Some vt, Some lv => Some (vt::lv)
                      | _, _ => None
                      end)
                   | None => None
                   end)
                 end) in

            (match load_val_tree_ptr m b' (Int.unsigned i') (N.to_nat n) with
             | Some vl => Some (b_c_node h vl)
             | None => None
             end) *)
            None
          | _ => None
          end)
       else
         (* this is a function [ outside of m ]*)
         Some (f_leaf b' i')
     | (Vint h) => Some (u_c_leaf h)
     | _ => None
     end)
  | 0 => None
  end
.



  *)




(* this is false, missing the boxed case which is off-shifted
Theorem repr_val_ptr_load :
  forall v6 m b i,
    repr_val_ptr_LambdaANF_Codegen v6 m (b, i) ->
    (exists v7, Mem.load int_chunk m b (Int.unsigned i)  = Some v7 /\ repr_val_LambdaANF_Codegen v6 m v7)
             \/ exists F, Genv.find_funct (globalenv p) (Vptr b i) = Some (Internal F). *)

(* relational version of get_allocs *)
Inductive get_allocs_ind: exp -> list positive -> Prop :=
| GEI_constr: forall x t vs e l, get_allocs_ind e l -> get_allocs_ind (Econstr x t vs e) (x::l)
| GEI_case: forall x cs l, get_allocs_case_ind cs l -> get_allocs_ind (Ecase x cs) l
| GEI_proj: forall x t n v e l, get_allocs_ind e l -> get_allocs_ind (Eproj x t n v e) (x::l)
| GEI_app: forall x t vs, get_allocs_ind (Eapp x t vs) []
| GEI_prim: forall x p vs e l, get_allocs_ind e l -> get_allocs_ind (Eprim x p vs e) (x::l)
| GEI_halt: forall x, get_allocs_ind (Ehalt x) []
| GEI_fun: forall fnd e l l', get_allocs_fundefs_ind fnd l ->
                              get_allocs_ind e l' ->
                              get_allocs_ind (Efun fnd e) (l ++ l')
with get_allocs_case_ind: list (ctor_tag * exp) -> list positive -> Prop :=
   | GEI_nil: get_allocs_case_ind nil nil
   | GEI_cons: forall z e cs l l',
       get_allocs_ind e l ->
       get_allocs_case_ind cs l' ->
       get_allocs_case_ind (cons (z, e) cs) (l++l')
with get_allocs_fundefs_ind: fundefs -> list positive -> Prop :=
   | GEI_Fnil: get_allocs_fundefs_ind Fnil nil
   | GEI_Fcons:
       forall f t vs e fnd l l',
         get_allocs_ind e l ->
         get_allocs_fundefs_ind fnd l' ->
       get_allocs_fundefs_ind (Fcons f t vs e fnd)  (vs++l++l').



Theorem get_allocs_correct:
  (forall e,
      get_allocs_ind e (get_allocs e))
  /\
  (forall fds,
      get_allocs_fundefs_ind fds (get_allocs_fundefs fds)).
Proof.
  eapply exp_def_mutual_ind; intros; simpl; try  (constructor; auto; fail).
  - constructor. constructor.
  - constructor. constructor. auto.
    clear H.  inv H0. simpl in H3. induction l.
    + constructor.
    + inv H3. constructor. auto. auto.
Qed.



(* TODO: write this to ensure that the GC nevers runs out of space in the middle of a function*)
Definition correct_alloc: exp -> Z -> Prop := fun e i => i =  Z.of_nat (max_allocs e ).

Theorem e_correct_alloc:
  forall e, exists i, correct_alloc e i.
Proof.
  intros.
  eexists. unfold correct_alloc. reflexivity.
Qed.



Theorem max_allocs_boxed: forall v c e l,
    l <> nil ->
(max_allocs (Econstr v c l e) = 1 + (length l) + max_allocs e).
Proof.
  intros; simpl. induction l.
  exfalso; auto.
  destruct l. omega.
  simpl.
  simpl in IHl.
  rewrite <- IHl. omega.
  intro. inv H0.
Qed.


(* see make_fundef_info, this is w.r.t. some fenv, another prop should assert the fenv is correct w.r.t. all functions *)

Definition correct_fundef_info (m:mem) (f:positive) (t:fun_tag) (vs:list positive) e finfo :=
  exists n l b fi_0,
   (* the tag for f points to a record r *)
    M.get t fenv =  Some (n, l) /\
    n = N.of_nat (length l) /\
    length l = length vs /\
    (* no duplicate could be weaken if shared *)
    NoDup l /\
    Forall (fun i => 0 <= (Z.of_N i) < max_args)%Z l /\
    (* id points to an array in global memory *)
    Genv.find_symbol (globalenv p) finfo = Some b /\

    (*
 12/17 -- now looking this up in mem directly
Genv.find_var_info (globalenv p) b = Some finfo_init /\
*)

    (* the record has the right information w.r.t. vs and r
       fi[0] = alloc(e)
       fi[1] = number of roots
       |fi| = 2+fi[1] *)
    Mem.loadv int_chunk m (Vptr b Ptrofs.zero) = Some (make_vint fi_0) /\

             Mem.loadv int_chunk m (Vptr b (Ptrofs.repr int_size)) = Some (make_vint (Z.of_N n)) /\

    (* gvar_init finfo_init = ((Init_int32 fi_0)::(Init_int32 fi_1)::fi_rest) /\ *)
             correct_alloc e fi_0 /\
             (int_size * fi_0 <= gc_size)%Z /\

    (forall (i:N), (i < n)%N ->
                   exists li, Mem.loadv int_chunk m (Vptr b (Ptrofs.repr (int_size*(Z.of_N (2+i)%N)))) = Some (make_vint (Z.of_N li)) /\
                                (nthN l i) = Some li).
(*
 12/17: probably need something w.r.t permissions
/\

    (forall (j:N), (j < n + 2)%N ->
        Mem.perm int_chunk m (Vptr b (Int.repr (int_size * (Z.of_N j)))) Readable) *)



(*     Forall2 (fun a i => exists i', i = Init_int32 i' /\ (Z.of_N a) = Int.unsigned i')  l fi_rest. *)

(* P is true of every fundefs in a bundle *)
(* TODO: move this to term_util *)
Inductive Forall_fundefs: (LambdaANF.term.var -> fun_tag -> list LambdaANF.term.var -> exp -> Prop) -> fundefs -> Prop :=
| Ff_cons : forall (P:(LambdaANF.term.var -> fun_tag -> list LambdaANF.term.var -> exp -> Prop)) f t vs e fds,
         P f t vs e ->
         Forall_fundefs P fds ->
         Forall_fundefs P (Fcons f t vs e fds)
| Ff_nil: forall P, Forall_fundefs P Fnil.


Theorem Forall_fundefs_In:
  forall P f t vs e fds,
  Forall_fundefs P fds ->
  fun_in_fundefs fds (f,t,vs,e) ->
  P f t vs e.
Proof.
  induction fds; intros.
  - inv H; inv H0; subst.
    + inv H; auto.
    +  apply IHfds; auto.
  - inv H0.
Qed.
(* END TODO move *)


(* 1) finfo_env has the correct finfo
   2) fenv is consistent with the info
   3) global env holds a correct Codegen representation of the function *)
Definition correct_environments_for_function:
  genv -> fun_env -> M.t positive -> mem -> fundefs ->  LambdaANF.term.var ->
  fun_tag -> list LambdaANF.term.var -> exp ->  Prop
  := fun ge fenv finfo_env m fds f t vs e =>
       exists l locs finfo b,
         (*1*)
         M.get f finfo_env = Some finfo /\
         correct_fundef_info m f t vs e finfo  /\
         (*2*)
         M.get t fenv = Some (l, locs) /\
         l = N.of_nat (length vs) /\
         (* may want to check that locs are distinct and same as in finfo? *)
         (*3*)
         Genv.find_symbol (globalenv p) f = Some b /\
         (* TODO: change this to repr_val_LambdaANF_Codegen *)
         repr_val_LambdaANF_Codegen (term.Vfun (M.empty term.val) fds f) m (Vptr b Ptrofs.zero).


Definition correct_environments_for_functions: fundefs -> genv -> fun_env -> M.t positive -> mem ->  Prop := fun fds ge fenv finfo_env m =>
                                                                                                            Forall_fundefs (correct_environments_for_function ge fenv finfo_env m fds) fds.


Definition is_protected_id  (id:positive)  : Prop :=
  List.In id protectedIdent.

Definition is_protected_tinfo_id (id:positive) : Prop :=
    id = allocIdent \/ id = limitIdent \/ id = argsIdent.

Theorem is_protected_tinfo_weak:
  forall x, is_protected_tinfo_id x ->
            is_protected_id x.
Proof.
  intros. repeat destruct H; subst; inList.
Qed.


(* Domain of find_symbol (globalenv p) is disjoint from bound_var e /\ \sum_rho (bound_var_val x \setminus names_in_fundef x) *)
(*  *)
Definition functions_not_bound (rho:LambdaANF.eval.env) (e:exp): Prop :=
  (forall x,
    bound_var e x ->
    Genv.find_symbol (Genv.globalenv p) x = None)/\
  (forall x y v,
      M.get y rho = Some v ->
      bound_notfun_val v x ->
      Genv.find_symbol (Genv.globalenv p) x = None).



Inductive unique_bindings_val: LambdaANF.term.val -> Prop :=
| UB_Vfun: forall rho fds f,
    unique_bindings_fundefs fds ->
    unique_bindings_val (Vfun rho fds f)
| UB_Vconstr: forall c vs,
    Forall unique_bindings_val vs ->
    unique_bindings_val (Vconstr c vs)
|UB_VInt: forall z,
    unique_bindings_val (term.Vint z)
.


(* UB + disjoint bound and in env *)
Definition unique_bindings_env (rho:LambdaANF.eval.env) (e:exp) : Prop :=
      unique_bindings e  /\
      (forall x v,
        M.get x rho = Some v ->
    ~ bound_var e x /\ unique_bindings_val v).

Theorem unique_bindings_env_prefix:
  forall e rho,
    unique_bindings_env rho e ->
    forall rho',
  prefix_ctx rho' rho ->
  unique_bindings_env rho' e.
Proof.
  intros.
  inv H.
  split; auto.
Qed.


(* TODO: also need UB for the functions in rho
Theorem unique_bindings_env_weaken :
  unique_bindings_env rho e ->
  rho' subseteq rho
unique_bindings_env rho e *)


Theorem functions_not_bound_subterm:
  forall rho e,
    functions_not_bound rho e ->
    forall e',
    subterm_e e' e ->
    functions_not_bound rho e'.
Proof.
  intros. split. intro; intros.
  apply H.
  eapply bound_var_subterm_e; eauto.
  apply H.
Qed.

Theorem functions_not_bound_set:
    forall rho e y v,
      functions_not_bound rho e ->
      (forall x, bound_notfun_val v x -> Genv.find_symbol (globalenv p) x = None) ->
      functions_not_bound (M.set y v rho) e.
Proof.
  intros. split. apply H.
  intros. destruct (var_dec y0 y).
  - subst. rewrite M.gss in H1. inv H1. destruct H. apply H0. auto.
  - rewrite M.gso in H1 by auto. inv H. eapply H4; eauto.
Qed.

Definition protected_id_not_bound  (rho:LambdaANF.eval.env) (e:exp) : Prop :=
  (forall x y v, M.get x rho = Some v ->
                 is_protected_id  y ->
                 ~ (x = y \/ bound_var_val v y) )/\
  (forall y, is_protected_id  y ->
             ~ bound_var e y).


Theorem protected_id_not_bound_prefix:
  forall rho rho' e,
    protected_id_not_bound rho e ->
    prefix_ctx rho' rho ->
    protected_id_not_bound rho' e.
Proof.
  intros. inv H. split; intros.
  - apply H0 in H.
    apply H1; eauto.
  - eapply H2; eauto.
Qed.



Theorem find_def_bound_in_bundle:
  forall e y t xs f fds,
  bound_var e y ->
  find_def f fds = Some (t, xs, e) ->
  bound_var_fundefs fds y.
Proof.
  induction fds; intros.
  simpl in H0. destruct (term.M.elt_eq f v). inv H0. constructor 3; auto.
  constructor 2. apply IHfds; auto.
  inv H0.
Qed.

Theorem protected_id_not_bound_closure:
  forall rho e e' f' f fds rho' t xs,
    protected_id_not_bound rho e ->
    M.get f rho = Some (Vfun rho' fds f') ->
    find_def f' fds = Some (t, xs, e') ->
   protected_id_not_bound rho e'.
Proof.
  intros.
  inv H.
  split. auto.
  intros.
  intro.
  specialize (H2 _ _ _ H0 H).
  apply H2. right.
  constructor.
  eapply find_def_bound_in_bundle; eauto.
Qed.

Theorem protected_id_closure:
  forall rho rho' f t0 ys fl f' t xs e' vs,
    protected_id_not_bound rho (Eapp f t0 ys) ->
    term.M.get f rho = Some (Vfun (M.empty _) fl f') ->
    get_list ys rho = Some vs ->
    find_def f' fl = Some (t, xs, e') ->
    set_lists xs vs (def_funs fl fl (M.empty _) (M.empty _)) = Some rho' ->
    protected_id_not_bound rho' e'.
Proof.
  intros.
  assert (protected_id_not_bound rho e') by (eapply protected_id_not_bound_closure; eauto).
  split. intros.
  assert (decidable (List.In x xs)). apply In_decidable. apply shrink_cps_correct.var_dec_eq.
  inv H7.
  (* in vs *)
  { inv H.
    intro. inv H.
    - specialize (H7 _ _ _ H0 H6). apply H7. right.
      constructor. eapply shrink_cps_correct.name_boundvar_arg; eauto.
    - assert (List.In v vs) by (eapply set_lists_In; eauto).
      assert (Hgl := get_list_In_val _ _ _ _  H1 H). destruct Hgl.
      destruct H11. specialize (H7 _ _ _ H12 H6). apply H7. auto.
  }
  erewrite <- set_lists_not_In in H5.
  2: eauto.
  2: eauto.
  assert (decidable (name_in_fundefs fl x)). unfold decidable. assert (Hd := Decidable_name_in_fundefs fl). inv Hd. specialize (Dec x). inv Dec; auto.
      inv H7.
        (*
          2) in fl *)
      rewrite def_funs_eq in H5. 2: eauto. inv H5.
      inv H.
      specialize (H5 _ _ _ H0 H6).
      intro. inv H.

      apply H5. right. constructor.
      apply name_in_fundefs_bound_var_fundefs. auto.

      apply H5. right. constructor. inv H10. auto.

      rewrite def_funs_neq in H5. 2: eauto.
      rewrite M.gempty in H5. inv H5.

        apply H4.
Qed.

Inductive empty_cont: cont -> Prop :=
| Kempty_stop: empty_cont Kstop
| Kempty_switch: forall k, empty_cont k ->
                           empty_cont (Kswitch k)
| Kempty_sbreak: forall k, empty_cont k ->
                           empty_cont (Kseq Sbreak k)
| Kempty_sskip: forall k, empty_cont k ->
                           empty_cont (Kseq Sskip k)
.
About int_size.

Definition protected_non_reachable_val_Codegen v6 m v7 (lenv:temp_env) : Prop :=
      exists alloc_b alloc_ofs limit_b limit_ofs args_b args_ofs,
        M.get allocIdent lenv = Some (Vptr alloc_b alloc_ofs) /\
        ~reachable_val_Codegen v6 m v7 alloc_b alloc_ofs /\
        M.get limitIdent lenv = Some (Vptr limit_b limit_ofs) /\
        ~reachable_val_Codegen v6 m v7 limit_b limit_ofs /\
        M.get argsIdent lenv = Some (Vptr args_b args_ofs) /\
        (forall i,
            Ptrofs.ltu i (Ptrofs.repr max_args) = true ->
            ~reachable_val_Codegen v6 m v7 args_b (Ptrofs.add args_ofs (Ptrofs.mul (Ptrofs.repr int_size) i))).

(* true if alloc, limit or args *)
Definition is_protected_loc lenv b ofs : Prop  :=
  M.get allocIdent lenv = Some (Vptr b ofs)
  \/
  M.get limitIdent lenv = Some (Vptr b ofs)
  \/
  (exists args_ofs i, M.get argsIdent lenv = Some (Vptr b (Ptrofs.add args_ofs (Ptrofs.repr (int_size * i))))%Z /\
                      (0 <= i < max_args)%Z).


(* L is the current allocated memory for user's datastructure
   space between alloc_ofs and limit_ofs is not in L
   anything in the args array is not in L
   tinfo is not in L
   anything pointed to by global env is not in L
*)

Definition protected_not_in_L (lenv:temp_env)  (L:block -> Z -> Prop): Prop :=
  exists alloc_b alloc_ofs limit_ofs args_b args_ofs tinf_b tinf_ofs,
    M.get allocIdent lenv = Some (Vptr alloc_b alloc_ofs) /\
    (forall j : Z, ((Ptrofs.unsigned alloc_ofs) <= j <
                    Ptrofs.unsigned limit_ofs)%Z  ->
                   ~ L alloc_b j) /\
    M.get limitIdent lenv = Some (Vptr alloc_b limit_ofs) /\
(*         (forall j : Z, ((Int.unsigned limit_ofs) <= j <
                    Int.unsigned limit_ofs + size_chunk int_chunk)%Z  ->
                   ~ L alloc_b_b j) *)
    M.get argsIdent lenv = Some (Vptr args_b args_ofs) /\
          (forall z j: Z,
              (0 <= z < max_args)%Z ->
              ((Ptrofs.unsigned  (Ptrofs.add args_ofs (Ptrofs.repr (int_size * z))))
               <= j <
               (Ptrofs.unsigned (Ptrofs.add args_ofs (Ptrofs.repr (int_size * z)))) +  int_size)%Z ->

              ~ L args_b j) /\
          (* tinfo_b is disjoint from L *)
          M.get tinfIdent lenv = Some (Vptr tinf_b tinf_ofs) /\
          (forall i, ~ L tinf_b i) /\
          (* anything pointed out by the global env is disjoint from l *)
          (forall x b,
              Genv.find_symbol (globalenv p) x = Some b ->
              b <> args_b /\ b <> alloc_b   (* these are also covered by correct_tinfo, but convenient here *)
            /\
              forall i, ~ L b i)
.

Theorem protected_not_in_L_proper:
  forall lenv lenv' L,
    protected_not_in_L lenv L ->
      map_get_r_l _ (cons argsIdent (cons limitIdent (cons allocIdent (cons tinfIdent nil)))) lenv lenv' ->
      protected_not_in_L lenv' L.
Proof.
  intros.
  inv H. destructAll. rewrite H0 in *; inList.
  do 7 eexists. repeat split; eauto.
  eapply H7; eauto.
  eapply H7; eauto.
  eapply H7; eauto.
Qed.

Theorem protected_not_in_L_proper_weak:
  forall lenv lenv' L ,
  map_get_r _ lenv lenv' ->
  protected_not_in_L lenv  L ->
  protected_not_in_L lenv'  L.
Proof.
  intros.
  eapply protected_not_in_L_proper. eauto.
  intro. intro. apply H.
Qed.

Theorem protected_not_in_L_set:
  forall lenv  L x v ,
  protected_not_in_L lenv  L ->
  ~ is_protected_tinfo_id x ->
  x <> tinfIdent ->
  protected_not_in_L (M.set x v lenv)  L.
Proof.
  intros.
  destruct H.
  destructAll.
  exists x0, x1, x2, x3, x4, x5, x6.
  repeat split;auto.
  - destruct (var_dec allocIdent x).
    + exfalso; apply H0.
      rewrite <- e.
      unfold is_protected_id.
      left; auto.
    +  rewrite M.gso by auto. auto.
  - destruct (var_dec limitIdent x).
    + exfalso; apply H0.
      rewrite <- e.
      unfold is_protected_id.
      right; auto.
    +  rewrite M.gso by auto. auto.
  - destruct (var_dec argsIdent x).
    + exfalso; apply H0.
      rewrite <- e.
      unfold is_protected_id.
      right; auto.
    +  rewrite M.gso by auto. auto.
  - rewrite M.gso; auto.
  - eapply H8; eauto.
  - eapply H8; eauto.
  - eapply H8; eauto.
Qed.

Theorem lenv_param_refl :
  forall lenv lenv' vs,
  lenv_param_asgn lenv lenv' [] vs
  -> map_get_r _ lenv lenv'.
Proof.
  intros.
  intro.
  specialize (H v).
  destruct H.
  symmetry.
  apply H0.
  intro.
  inv H1.
Qed.

Theorem lenv_param_asgn_not_in:
  forall lenv lenv' b ofs x (L:positive -> Prop) xs vs7,
M.get x lenv = Some (Vptr b ofs) ->
  L x ->
  (forall x6 : positive, List.In x6 xs -> ~ L x6) ->
  lenv_param_asgn lenv lenv' xs vs7 ->
  M.get x lenv' = Some (Vptr b ofs).
Proof.
  intros.
  specialize (H2 x).
  destruct H2.
  rewrite H3.
  auto.
  intro.
  eapply H1; eauto.
Qed.


Theorem lenv_param_asgn_map:
  forall lenv lenv' xs vs7 l,
  lenv_param_asgn lenv lenv' xs vs7 ->
  Disjoint _ (FromList xs) (FromList l) ->
  map_get_r_l _ l lenv lenv'.
Proof.
  intros.
  intro.
  intro.
  specialize (H v); destruct H.
  rewrite H2.
  auto.
  inv H0. specialize (H3 v).
  intro.
  apply H3.
  auto.
Qed.


  Theorem protected_not_in_L_asgn:
  forall L xs vs7 lenv lenv',
protected_not_in_L lenv  L ->
lenv_param_asgn lenv lenv' xs vs7 ->
(forall x, List.In x xs -> ~ (is_protected_tinfo_id x \/ x = tinfIdent)) ->
protected_not_in_L lenv'  L.
  Proof.
    intros.
    inv H; destructAll.
    exists x, x0, x1, x2, x3, x4, x5.

    repeat split; auto; try (eapply lenv_param_asgn_not_in with (L :=  fun x => (is_protected_tinfo_id x \/ x = tinfIdent)); eauto).
    left; inList. left; inList.
    left; inList. reflexivity.
    eapply H8; eauto.
    eapply H8; eauto.
    eapply H8; eauto.
  Qed.

  (* no longer needed without max_alloc *)
      (* Mono + extra assumptions to avoid overflow
Theorem protected_not_in_L_mono:
  forall lenv alloc_b alloc_ofs z limit_ofs,
    M.get allocIdent lenv = Some (Vptr alloc_b alloc_ofs) ->
    M.get limitIdent lenv = Some (Vptr alloc_b limit_ofs) ->
    ((Int.unsigned alloc_ofs) + int_size * z <=  Int.unsigned limit_ofs)%Z ->
    forall L z',
   protected_not_in_L lenv z L ->
  (0 <= z' <= z)%Z ->
  protected_not_in_L lenv z' L.
Proof.
  intros.
  inv H2. destructAll.
  rewrite H4 in H. inv H.
  rewrite H6 in H0. inv H0.
  exists alloc_b, alloc_ofs, limit_ofs.
  do 4 (eexists).
  repeat split; eauto.
  intros. apply H5.
  unfold int_size in *; simpl size_chunk in *.
  assert (Int.unsigned limit_ofs <= Int.max_unsigned)%Z by apply Int.unsigned_range_2 .
  assert (0 <= Int.unsigned alloc_ofs)%Z by apply Int.unsigned_range_2 .
  unfold Int.add in *.
  rewrite Int.unsigned_repr with (z := (4 * z)%Z) by omega.
  rewrite Int.unsigned_repr with (z := (4 * z')%Z) in H by omega.
  rewrite Int.unsigned_repr by omega.
  rewrite Int.unsigned_repr in H by omega. omega.
  apply H11 in H; destructAll; auto.
  apply H11 in H; destructAll; auto.
  apply H11 in H; destructAll; auto.
Qed. *)


Definition Vint_or_Vconstr (v:term.val): Prop :=
  (exists i, v = term.Vint i) \/ (exists c vs, v = term.Vconstr c vs).

Definition correct_fundef_id_info (m:mem) (fds:fundefs) (f:positive) :=
            exists finfo t t' vs e, (find_def f fds = Some (t, vs, e) /\
                                     M.get f finfo_env = Some (finfo , t') /\
                                     t = t' /\
                                     correct_fundef_info  m f t vs e finfo).

(* relates a LambdaANF evaluation environment to a Clight memory up to the free variables in e *)
(* If x is a free variable of e, then it might be in the generated code:
   1) a function (may want to handle this separately as they won't get moved by the GC) in the global environment, evaluates to a location related to f by repr_val_ptr_LambdaANF_Codegen
   2) a local variable in le related to (rho x) according to repr_val_LambdaANF_Codegen -- this happens when e.g. x := proj m, or after function initialization

All the values are in a space L which is disjoint form protected space

Note that parameters are heap allocated, and at function entry "free variables" are held in args and related according to repr_val_ptr_LambdaANF_Codegen

Now also makes sure none of the protected portion are reachable by the v7

TODO: second section needs that for any such f s.t. find_def f fl = Some (t, vs4, e),  e is closed by  var (FromList vsm4 :|: name_in_fundefs fl)
 may want something about functions in rho, i.e. that they don't need to be free to be repr_val_id, since they are the only thing that may appear free in other functions body (and not bound in the opening
may need rho' also has the Vfun
 *)

    Definition rel_mem_LambdaANF_Codegen: exp -> LambdaANF.eval.env -> mem -> temp_env -> Prop :=
      fun e rho m le =>
        exists L, protected_not_in_L le L /\
        (forall x,
        (occurs_free e x ->
                  exists v6, M.get x rho = Some v6 /\
                             repr_val_id_L_LambdaANF_Codegen v6 m L le x)
        /\
        (forall rho' fds f v,
            M.get x rho = Some v ->
            subval_or_eq (Vfun rho' fds f) v ->
            repr_val_id_L_LambdaANF_Codegen (Vfun rho' fds f) m L le f /\
            closed_val (Vfun rho' fds f) /\
            correct_fundef_id_info m fds f)).
(*
    Theorem rel_mem_LambdaANF_Codegen_set_vconstr:
      rel_mem_LambdaANF_Codegen e rho m lenv ->
      rel_mem_LambdaANF_Codegen e rho m (M.set x (Vconstr c vs)) *)

    (* this is wrong, the block after limit may be in L
    Theorem protected_not_L:
      forall e le b ofs L,
      protected_not_in_L le (Z.of_nat (max_allocs e)) L ->
      is_protected_loc le b (Int.repr ofs) -> forall i : Z, (ofs <= i < ofs + size_chunk int_chunk)%Z -> ~ L b i. *)

Definition unchanged_globals: mem -> mem -> Prop :=
  fun m m' =>
    forall x b,
      Genv.find_symbol (globalenv p) x = Some b ->
      forall i chunk, Mem.loadv chunk m (Vptr b i) =  Mem.loadv chunk m' (Vptr b i).

Theorem unchanged_globals_trans:
  forall m1 m2 m3,
    unchanged_globals m1 m2 ->
    unchanged_globals m2 m3 ->
    unchanged_globals m1 m3.
Proof.
  intros.
  intro; intros.
  specialize (H _ _ H1 i chunk).
  specialize (H0 _ _ H1 i chunk).
  rewrite H; rewrite H0.
  reflexivity.
Qed.

Theorem correct_fundefs_unchanged_global:
  forall m m' fds f,
    correct_fundef_id_info m fds f ->
    unchanged_globals m m' ->
    correct_fundef_id_info m' fds f.
Proof.
  intros.
  destruct H as [finfo [t [t' [vs [e H]]]]].
  exists finfo, t, t', vs, e.
  destruct H. destruct H1. destruct H2.
  split; auto.
  split; auto.
  split; auto.
  destruct H3 as [n [l [b [fi_0 [fi_1 H3]]]]].
  exists n, l, b, fi_0.
  destructAll.
  repeat split; auto.
  specialize (H0 finfo b); rewrite <- H0; auto.
  specialize (H0 finfo b); rewrite <- H0; auto.
  intros.
  apply H12 in H2.
  destruct H2 as [li H2].
  exists li.
  destructAll.
  split; auto.
  specialize (H0 finfo b); rewrite <- H0; auto.
Qed.


Theorem store_globals_unchanged:
  forall b' i m m' a,
     Mem.store int_chunk m b' i a = Some m' ->
 (forall (x : ident) (b : block),
          Genv.find_symbol (globalenv p) x = Some b -> b <> b') ->
  unchanged_globals m m'.
Proof.
  intros.
  intro; intros. apply H0 in H1.
  symmetry.
  eapply Mem.load_store_other. apply H.
  auto.
Qed.

Theorem mem_after_n_proj_store_globals_unchanged:
  forall b' i vs z  m m',
  mem_after_n_proj_store b' i vs z m m' ->
 (forall (x : ident) (b : block),
          Genv.find_symbol (globalenv p) x = Some b -> b <> b') ->
  unchanged_globals m m'.
Proof.
  induction vs; intros. inv H.
  inv H.
  - eapply store_globals_unchanged; eauto.
  - specialize (IHvs _ _ _ H9 H0).
    eapply unchanged_globals_trans; eauto.
    eapply store_globals_unchanged; eauto.
Qed.


Theorem rel_mem_update_protected:
  forall e rho m le args_b args_ofs i v m',
    rel_mem_LambdaANF_Codegen e rho m le ->
    M.get argsIdent le = Some (Vptr args_b args_ofs) ->
    (0 <= Z.of_N i < max_args)%Z ->
    Mem.store int_chunk m args_b (Ptrofs.unsigned (Ptrofs.add args_ofs  (Ptrofs.repr (int_size * Z.of_N i)))) v = Some m' ->
    rel_mem_LambdaANF_Codegen e rho m' le.
Proof.
  intros. destruct H as [L Hrel_mem].
  destruct Hrel_mem as [Hprotect Hof_v].
  exists L.
  split; auto.
  intro.
  specialize (Hof_v x).
  destruct Hof_v as [Hof_v1 Hof_v2].
  split.
  * intros. apply Hof_v1 in H.
    destructAll. exists x0. split; auto.
    eapply repr_val_id_L_unchanged.
    eauto.
    eapply Mem.store_unchanged_on. eauto.
    intros.
    inv Hprotect. destructAll. rewrite H10 in H0. inv H0.
    eapply H11. eauto. unfold int_size in *.
    split; auto.

  * intros.
    specialize (Hof_v2 _ _ _ _ H H3).
    destruct Hof_v2 as [Hof_v2 [Hv2_closed Hv2_f]]. split.
    eapply repr_val_id_L_unchanged.
    eauto.
    eapply Mem.store_unchanged_on. eauto.
    intros.     inv Hprotect. destructAll. rewrite H10 in H0. inv H0.
    eapply H11. eauto. unfold int_size in *.
    split; auto.
    auto.
    split. auto.
    eapply correct_fundefs_unchanged_global.
    eauto.
    intro finfo; intros.
    inv Hprotect. destructAll.
    symmetry. eapply Mem.load_store_other.
    eauto. left.
    rewrite H9 in H0; inv H0. eapply H13. eauto.
Qed.

 Fixpoint mem_of_state (s:state) : mem :=
  match s with
  | State f s k e le m => m
  | Callstate f vs k m => m
  | Returnstate x k m =>  m
  end.



(* [pure] step with no built-in, i.e. trace is always E0 *)
Definition traceless_step2:  genv -> state -> state -> Prop := fun ge s s' => step2 ge s nil s'.

Definition m_tstep2 (ge:genv):=  clos_trans state (traceless_step2 ge).

#[global] Hint Unfold Ptrofs.modulus Ptrofs.max_unsigned uint_range : core.
#[global] Hint Transparent Ptrofs.max_unsigned Ptrofs.modulus uint_range : core.

Inductive mem_after_n_proj_store_rev: block -> Z -> (list Values.val) -> mem -> mem -> Prop :=
| Mem_last_ind: forall m b ofs v m',
    Mem.store int_chunk m b ofs v = Some m' ->
    mem_after_n_proj_store_rev b ofs [v] m m'
| Mem_next_ind:
    forall b ofs vs v m m' m'',
    mem_after_n_proj_store_rev b (ofs + int_size) vs m m' ->
    Mem.store int_chunk m' b ofs v = Some m'' ->
    mem_after_n_proj_store_rev b ofs (v::vs) m m''.

Theorem set_commute:
  forall A (vx vy:A) (x y:positive) rho,
    x <> y ->
    M.set x vx (M.set y vy rho) = M.set y vy  (M.set x vx rho).
Proof.
  induction x; intros; simpl; destruct y; try solve [simpl; destruct rho; reflexivity].
  - simpl.  destruct rho. rewrite IHx. reflexivity. intro. apply H. subst. auto.
      rewrite IHx. reflexivity. intro; apply H; subst; auto.
  - simpl. destruct rho. rewrite IHx. reflexivity. intro. apply H. subst; auto.
    rewrite IHx. reflexivity. intro; apply H; subst; auto.
  - exfalso. auto.
Qed.






Theorem mem_of_Forall_nth_projection_cast:
  forall x lenv b ofs f,
    find_symbol_domain finfo_env ->
    finfo_env_correct ->
    M.get x lenv = Some (Vptr b ofs) ->
    forall l s i m k,
      (0 <= i /\ i + (Z.of_nat (List.length l)) <= Ptrofs.max_unsigned )%Z ->
      (forall j, 0 <= j < i + Z.of_nat (List.length l) -> Mem.valid_access m int_chunk b (Ptrofs.unsigned (Ptrofs.add ofs (Ptrofs.repr  (int_size * j)))) Writable)%Z ->
      Forall_statements_in_seq'
        (is_nth_projection_of_x x) l s i ->
      forall vs,
      Forall2 (get_var_or_funvar lenv) l vs ->
      exists m', m_tstep2 (globalenv p) (State f s k empty_env lenv m)
               (State f Sskip k empty_env lenv m') /\
      mem_after_n_proj_store_cast b (Ptrofs.unsigned ofs) vs i m m'.
Proof with archi_red.
  intros x lenv b ofs f Hsym HfinfoCorrect Hxlenv.
  induction l; intros s i m k Hil_max; intros.
  - (* empty -- impossible *)
    inv H1. inv H0.
  -   assert (length (a :: l) = length vs) by (eapply Forall2_length'; eauto). rewrite H2 in *. clear H2.
      assert (Hi_range : uint_range i) by solve_uint_range.
     inv H1.
     assert (Hvas :  Mem.valid_access m int_chunk b
                                      (Ptrofs.unsigned (Ptrofs.add ofs (Ptrofs.repr (int_size * i))))
                                      Writable).
     apply H. simpl. split.
     omega.
     rewrite Zplus_0_r_reverse with (n := i) at 1.
     apply Zplus_lt_compat_l.
     apply Pos2Z.is_pos.
     assert (Hvra := Mem.valid_access_store m int_chunk b  (Ptrofs.unsigned (Ptrofs.add ofs (Ptrofs.repr (int_size* i)))) y Hvas).
     destruct Hvra as [m2 Hsm2].
     inv H0.
     + (* last statement *)
       inv H6.
       inv H8.
       exists m2.
       split.
       2:{
       constructor. rewrite Ptrofs.repr_unsigned. auto. }
       inv H0.
       * inv H4.
         2:{ exfalso. rewrite H1 in H0. inv H0. }

         rewrite H1 in H0; inv H0.
         constructor.

         destruct (Archi.ptr64) eqn:Harchi.
         {
           econstructor.
         constructor. econstructor. econstructor.
         econstructor. apply Hxlenv. constructor.
         archi_red. constructor.
         archi_red. constructor.
         specialize (Hsym a). inv Hsym.
         destruct (H2 (ex_intro _ b1 H1)). destruct x0.
         unfold makeVar. rewrite H3.
         specialize (HfinfoCorrect _ _ _ H3). inv HfinfoCorrect.
         destruct x0. rewrite H4.
         econstructor.  apply eval_Evar_global.  apply M.gempty.

         apply H1. constructor. constructor.
         specialize (Hsym a). inv Hsym.
         destruct (H2 (ex_intro _ b1 H1)). destruct x0.
         unfold makeVar. rewrite H3.
         specialize (HfinfoCorrect _ _ _ H3). inv HfinfoCorrect.
         destruct x0. rewrite H4.
         constructor.
         eapply assign_loc_value.

         2:{ unfold Ptrofs.of_int64.
         rewrite Int64.unsigned_repr in *.
         rewrite int_z_mul. archi_red. apply Hsm2.
         solve_uint_range. archi_red. unfold Int64.max_unsigned. simpl; omega.
         archi_red. auto. }
         archi_red.
         constructor. }
         {
           econstructor.
         constructor. econstructor. econstructor.
         econstructor. apply Hxlenv. constructor.
         archi_red. constructor.
         archi_red. constructor.

         specialize (Hsym a). inv Hsym.
         destruct (H2 (ex_intro _ b1 H1)). destruct x0.
         unfold makeVar. rewrite H3.
         specialize (HfinfoCorrect _ _ _ H3). inv HfinfoCorrect.
         destruct x0. rewrite H4.
         econstructor. apply eval_Evar_global.  apply M.gempty.
         apply H1. constructor. constructor.
         specialize (Hsym a). inv Hsym.
         destruct (H2 (ex_intro _ b1 H1)). destruct x0.
         unfold makeVar. rewrite H3.
         specialize (HfinfoCorrect _ _ _ H3). inv HfinfoCorrect.
         destruct x0. rewrite H4.
         constructor.
         eapply assign_loc_value.


         2:{ unfold ptrofs_of_int.  unfold Ptrofs.of_intu.
         unfold Ptrofs.of_int.
         rewrite Int.unsigned_repr in *.
         rewrite int_z_mul. archi_red. apply Hsm2.
         solve_uint_range. archi_red. solve_uint_range. omega.
         archi_red. auto. }
         archi_red.
         constructor.
         }
       * inv H4. exfalso; rewrite H1 in H0; inv H0.
         constructor.
         destruct (Archi.ptr64) eqn:Harchi...

         {
           eapply step_assign with (v2 := y) (v := y).
           constructor. econstructor. econstructor.
           econstructor. apply Hxlenv. constructor.
           constructor. constructor. constructor. apply H2.
           simpl. destruct y; inv H3; auto.
           eapply assign_loc_value. 2:{  unfold Ptrofs.of_int64.
           rewrite Int64.unsigned_repr in *.
           rewrite int_z_mul. archi_red. eauto. solve_uint_range.
           archi_red. unfold Int64.max_unsigned. simpl; omega.
           archi_red. auto. auto. }
           constructor. }
         {
           eapply step_assign with (v2 := y) (v := y).
           constructor. econstructor. econstructor.
           econstructor. apply Hxlenv. simpl. unfold sem_cast. simpl. rewrite Harchi. constructor.
           constructor. constructor. constructor. apply H2.
           simpl.  destruct y; inversion H3; auto. simpl in H3. rewrite H3 in Harchi; inv Harchi.
           unfold sem_cast. simpl. rewrite Harchi. constructor.
           eapply assign_loc_value.
           2:{ unfold ptrofs_of_int. unfold Ptrofs.of_intu. unfold Ptrofs.of_int.
           rewrite Int.unsigned_repr.
           rewrite int_z_mul. eauto. solve_uint_range.
           archi_red. solve_uint_range. omega.
           archi_red. auto.
           solve_uint_range. }
           constructor. }

     +  (* IH *)
       inv H9.
       eapply IHl with (m := m2) in H5; eauto. destruct H5 as [m3 [H5a H5b]]. exists m3.
       split.
       2:{ econstructor. rewrite Ptrofs.repr_unsigned. apply Hsm2. apply H5b. }

       inv H0.
       * inv H4.
         2:{ exfalso; rewrite H1 in H0; inv H0. }
         rewrite H1 in H0; inv H0.
         eapply t_trans.
         econstructor.  constructor.
         (* branch here *)
         destruct (Archi.ptr64) eqn:Harchi...
         {
         eapply t_trans. constructor. econstructor.
         constructor. econstructor. econstructor. constructor. eauto. constructor.
         constructor. constructor.
         specialize (Hsym a). inv Hsym.
         destruct (H2 (ex_intro _ b1 H1)). destruct x0.
         unfold makeVar. rewrite H3. econstructor.
         specialize (HfinfoCorrect _ _ _ H3). inv HfinfoCorrect.
         destruct x0. rewrite H4.
         apply eval_Evar_global. apply M.gempty. eauto.
         specialize (HfinfoCorrect _ _ _ H3). inv HfinfoCorrect.
         destruct x0. rewrite H4.
         constructor. constructor.
         specialize (Hsym a). inv Hsym.
         destruct (H2 (ex_intro _ b1 H1)). destruct x0.
         unfold makeVar. rewrite H3.
         specialize (HfinfoCorrect _ _ _ H3). inv HfinfoCorrect.
         destruct x0. rewrite H4.
         constructor. eapply assign_loc_value. constructor.
          unfold Ptrofs.of_int64.
           rewrite Int64.unsigned_repr in *.
           rewrite int_z_mul. eauto. solve_uint_range.
           archi_red. unfold Int64.max_unsigned. simpl; omega.
           archi_red. auto. auto.
         eapply t_trans. constructor. constructor.
         apply H5a. }
         {
         eapply t_trans. constructor. econstructor.
         constructor. econstructor. econstructor. constructor. eauto. unfold sem_cast. simpl. archi_red. constructor.
         constructor. constructor.
         specialize (Hsym a). inv Hsym.
         destruct (H2 (ex_intro _ b1 H1)). destruct x0.
         unfold makeVar. rewrite H3.
         specialize (HfinfoCorrect _ _ _ H3). inv HfinfoCorrect.
         destruct x0. rewrite H4.
         econstructor.
         apply eval_Evar_global.  apply M.gempty. eauto. constructor. constructor.
         unfold sem_cast. simpl. archi_red.
         specialize (Hsym a). inv Hsym.
         destruct (H2 (ex_intro _ b1 H1)). destruct x0.
         unfold makeVar. rewrite H3. specialize (HfinfoCorrect _ _ _ H3). inv HfinfoCorrect.
         destruct x0. rewrite H4. constructor.  eapply assign_loc_value. constructor.
         unfold ptrofs_of_int. unfold Ptrofs.of_intu. unfold Ptrofs.of_int.
           rewrite Int.unsigned_repr in *.
         rewrite int_z_mul. eauto. solve_uint_range.
         archi_red. solve_uint_range. omega.
         archi_red. solve_uint_range. omega.
         eapply t_trans. constructor. constructor.
         apply H5a. }

       * inv H4. exfalso; rewrite H1 in H0; inv H0.
         (* branch here *)
         destruct (Archi.ptr64) eqn:Harchi...
{         eapply t_trans.
         econstructor.  constructor.
         eapply t_trans. constructor. eapply step_assign with (v2 := y) (v := y).
         constructor. econstructor. econstructor. constructor. eauto. constructor.
         constructor. constructor. econstructor. auto. simpl.
         destruct y; inv H3; auto.
         eapply assign_loc_value.
         2:{ unfold Ptrofs.of_int64.
           rewrite Int64.unsigned_repr in *.

           rewrite int_z_mul. apply Hsm2. solve_uint_range.  archi_red; eauto.
           unfold Int64.max_unsigned; simpl; omega. archi_red; auto. auto. }
           constructor.
         eapply t_trans. constructor. constructor.
         apply H5a. }

{         eapply t_trans.
         econstructor.  constructor.
         eapply t_trans. constructor. eapply step_assign with (v2 := y) (v := y).
         constructor. econstructor. econstructor. constructor. eauto. unfold sem_cast.
         simpl. archi_red. constructor.
         constructor.
         constructor. constructor.  auto. simpl.
         destruct y; inversion H3; auto. simpl in H3. rewrite H3 in Harchi; inv Harchi.
         unfold sem_cast. simpl. archi_red. constructor.
         eapply assign_loc_value.
         2:{ unfold ptrofs_of_int. unfold Ptrofs.of_intu. unfold Ptrofs.of_int.
         rewrite Int.unsigned_repr.
         rewrite int_z_mul. apply Hsm2. solve_uint_range.  archi_red. solve_uint_range.
         omega. archi_red. auto. auto. }
         constructor.
         eapply t_trans. constructor. constructor.
         apply H5a. }


       * destruct Hil_max.
         split. apply Z.lt_le_incl.  apply Zle_lt_succ. auto.
         simpl in H2. rewrite Zpos_P_of_succ_nat in H2. rewrite Z.add_succ_comm.
         assert (Hll' : length l = length l') by (eapply Forall2_length'; eauto).
         rewrite Hll' in *. auto.
       * intros.
         eapply Mem.store_valid_access_1. apply Hsm2.
         apply H. simpl.
         rewrite Zpos_P_of_succ_nat.
         assert (Hll' : length l = length l') by (eapply Forall2_length'; eauto).
         rewrite Hll' in *.
         omega.
Qed.







End RELATION.




Section THEOREM.


Ltac archi_red :=
  int_red;
  unfold int_chunk in *;
  unfold val in *;
  unfold uval in *;
  unfold val_typ in *;
  unfold Init_int in *;
  unfold make_vint in *;
  unfold c_int' in *;
  unfold uint_range in *;
  try (rewrite ptrofs_mu in *);
  (match goal with
   | [ H : Archi.ptr64 = _ |- _] => try (rewrite H in *)
   end).

(* these ltac are agnostic on archi, useful for automation *)
   Ltac ptrofs_of_int :=
     unfold Ptrofs.of_int64 in *;
     unfold ptrofs_of_int in *;
     unfold Ptrofs.of_intu in *;
     unfold Ptrofs.of_int in *.

   Ltac int_unsigned_repr :=
     try (rewrite Int64.unsigned_repr in *);
     try (rewrite Int.unsigned_repr in *).

   Ltac int_max_unsigned:=
     try (rewrite Int64.max_unsigned in *);
     try (rewrite Int.max_unsigned in *).




Notation vval := val. (* NOTE: in Clight, SIZEOF_PTR == SIZEOF_INT *)
Notation uval := val.

Notation valPtr := (Tpointer vval
                            {| attr_volatile := false; attr_alignas := None |}).


  (* same as LambdaANF_to_Clight *)
  Variable (argsIdent : ident).
  Variable (allocIdent : ident).
  Variable (limitIdent : ident).
  Variable (gcIdent : ident).
  Variable (mainIdent : ident).
  Variable (bodyIdent : ident).
  Variable (threadInfIdent : ident).
  Variable (tinfIdent : ident).
  Variable (heapInfIdent : ident).
  Variable (numArgsIdent : ident).
  Variable (isptrIdent: ident). (* ident for the isPtr external function *)
  Variable (caseIdent:ident).
  Variable (nParam:nat).

  Definition protectedIdent_thm := protectedIdent argsIdent allocIdent limitIdent gcIdent mainIdent bodyIdent threadInfIdent tinfIdent heapInfIdent numArgsIdent isptrIdent caseIdent.
  Variable (disjointIdent: NoDup protectedIdent_thm).

  Definition protectedNotTinfoIdent_thm: list ident := (gcIdent::mainIdent::bodyIdent::threadInfIdent::tinfIdent::heapInfIdent::numArgsIdent::numArgsIdent::isptrIdent::caseIdent::[]).


  Definition is_protected_id_thm := is_protected_id argsIdent allocIdent limitIdent gcIdent mainIdent bodyIdent threadInfIdent tinfIdent heapInfIdent numArgsIdent isptrIdent caseIdent.

  Definition is_protected_tinfo_id_thm := is_protected_tinfo_id argsIdent allocIdent limitIdent.

  Definition repr_val_id_L_LambdaANF_Codegen_thm := repr_val_id_L_LambdaANF_Codegen argsIdent allocIdent limitIdent gcIdent threadInfIdent tinfIdent isptrIdent caseIdent nParam.

  Definition repr_val_LambdaANF_Codegen_thm := repr_val_LambdaANF_Codegen argsIdent allocIdent limitIdent gcIdent threadInfIdent tinfIdent isptrIdent caseIdent nParam.



Theorem is_protected_not_tinfo:
  forall x, List.In x protectedNotTinfoIdent_thm ->
            ~ is_protected_tinfo_id_thm x.
Proof.
 intros.
 intro.
 assert (H_dj := disjointIdent).
 inv H_dj. inv H4. inv H6.
 inv H0.
 apply H5. right; auto.
 inv H1.
 apply H4; auto.
 apply H3. right; right; auto.
Qed.

(*
    Variable cenv:LambdaANF.term.ctor_env.
  Variable fenv:LambdaANF.term.fun_env.
  Variable finfo_env: M.t positive. (* map from a function name to its type info *)
  Variable p:program.


  (* This should be a definition rather than a parameter, computed once and for all from cenv *)
  Variable rep_env: M.t ctor_rep.
*)


  (* TODO: move this to term_util *)
  Definition Forall_constructors_in_e (P: var -> ctor_tag -> list var -> Prop) (e:exp) :=
    forall x t  ys e',
      subterm_or_eq (Econstr x t ys e') e -> P x t ys.


  Definition Forall_projections_in_e (P: var -> ctor_tag -> N -> var -> Prop) (e:exp) :=
    forall x t n v e',
      subterm_or_eq (Eproj x t n v e') e -> P x t n v.

  (* Note: the fundefs in P is the whole bundle, not the rest of the list *)
  Definition Forall_functions_in_e (P: var -> fun_tag -> list var -> exp ->  fundefs -> Prop) (e:exp) :=
    forall fds e' f t xs e'',  subterm_or_eq (Efun fds e') e ->
                               fun_in_fundefs fds (f, t, xs, e'') ->
                               P f t xs e'' fds.


  Definition Forall_exp_in_caselist (P: exp -> Prop) (cl:list (ctor_tag * exp)) :=
    forall g e, List.In (g, e) cl -> P e.




  Theorem crt_incl_ct:
          forall T P e e',
          clos_trans T P e e' ->
          clos_refl_trans T P e e'.
  Proof.
    intros. induction H. constructor; auto.
    eapply rt_trans; eauto.
  Qed.

  Theorem Forall_constructors_subterm:
    forall P e e' ,
    Forall_constructors_in_e P e ->
    subterm_e e' e ->
    Forall_constructors_in_e P e'.
  Proof.
    intros. intro; intros.
    eapply H.
    assert (subterm_or_eq e' e).
    apply crt_incl_ct.
    apply H0.
    eapply rt_trans; eauto.
  Qed.


  (* END TODO move *)

  (* all constructors in the exp exists in cenv and are applied to the right number of arguments
    May want to have "exists in cenv" also true for constructors in rho *)
  Definition correct_cenv_of_exp: LambdaANF.term.ctor_env -> exp -> Prop :=
    fun cenv e =>
      Forall_constructors_in_e (fun x t ys =>
                                  match (M.get t cenv) with
                                  | Some (Build_ctor_ty_info _ _ _ a _) =>
                                    N.of_nat (length ys) = a
                                  | None => False
                                  end) e.

  Definition correct_cenv_of_caselist: LambdaANF.term.ctor_env -> list (ctor_tag * exp) -> Prop :=
    fun cenv cl =>
      Forall_exp_in_caselist (correct_cenv_of_exp cenv) cl.



  Theorem correct_cenv_of_case:
    forall cenv v l,
      correct_cenv_of_exp cenv (Ecase v l) ->
      correct_cenv_of_caselist cenv l.
  Proof.
    intros; intro; intros.
    eapply Forall_constructors_subterm. apply H.
    constructor. econstructor. eauto.
  Qed.

  Theorem Forall_constructors_in_constr:
  forall P x t ys e,
  Forall_constructors_in_e P (Econstr x t ys e) ->
  P x t ys.
  Proof.
    intros.
    unfold Forall_constructors_in_e in *.
    eapply H.
    apply rt_refl.
  Qed.



  Theorem nodup_test:
    forall (x1 x2 x3 x4 x5: positive),
  NoDup [x1; x2; x3; x4; x5] ->
   x4 <> x2.
  Proof.
    intros.
    intro; subst.
    inversion H as [H1 | x l H1 H2]; subst.
    try (solve [apply H1; inList]).
    inversion H2 as [H3 | x l H3 H4]; subst.
    try (solve [apply H3; inList]).
  Qed.



Inductive correct_cenv_of_val: LambdaANF.term.ctor_env -> (LambdaANF.term.val) -> Prop :=
| CCV_constr:forall cenv c vs inf,
    Forall (correct_cenv_of_val cenv) vs ->
    M.get c cenv = Some inf ->
    N.of_nat (length vs) = ctor_arity inf ->
    correct_cenv_of_val cenv (Vconstr c vs)
| CCV_fun: forall cenv rho fds f,
    Forall_fundefs (fun v t xs e => correct_cenv_of_exp cenv e) fds ->
    correct_cenv_of_val cenv (Vfun rho fds f)
| CCV_int: forall cenv z,
    correct_cenv_of_val cenv (term.Vint z).



(* everything in cenv is in ienv, AND there is a unique entry for it, AND its ord is not reused
    Doesn't check that name of the i will be consistent (namei could be different from name') *)
  Definition correct_ienv_of_cenv: LambdaANF.term.ctor_env -> n_ind_env -> Prop :=
    fun cenv ienv =>
      forall x, forall i a ord name name', M.get x cenv = Some (Build_ctor_ty_info name name' i a ord) ->
                                   exists  namei cl, M.get i ienv = Some (namei, cl) /\ List.In (name, x, a, ord) cl /\ ~ (exists ord' name' a', (name', a', ord') <> (name, a, ord) /\ List.In (name', x, a', ord') cl) /\ ~ (exists name' x' a', (name', x', a') <> (name, x, a) /\ List.In (name', x', a', ord) cl).

  (* all constructors found in ienv are in cenv *)
  Definition domain_ienv_cenv:  LambdaANF.term.ctor_env -> n_ind_env -> Prop :=
    fun cenv ienv =>
      forall i namei cl, M.get i ienv = Some (namei, cl)  ->
                         forall name x a ord, List.In (name, x, a, ord) cl ->
                                              exists namei', M.get x cenv = Some (Build_ctor_ty_info name namei' i a ord).



(* stronger version of ienv_of_cenv that enforces uniqueness of name' for i and that nothing is in ienv and not in cenv *)
    Definition correct_ienv_of_cenv_strong: LambdaANF.term.ctor_env -> n_ind_env -> Prop :=
    fun cenv ienv =>
      forall x, forall i a ord name namei, M.get x cenv = Some (Build_ctor_ty_info name namei i a ord) ->
                                   exists   cl, M.get i ienv = Some (namei, cl) /\ List.In (name, x, a, ord) cl /\ ~ (exists ord' name' a', (name', a', ord') <> (name, a, ord) /\ List.In (name', x, a', ord') cl) /\ ~ (exists name' x' a', (name', x', a') <> (name, x, a) /\ List.In (name', x', a', ord) cl).




  (* OS 04/24: added in bound on n includes in this *)
  Inductive correct_crep (cenv:ctor_env): ctor_tag -> ctor_rep -> Prop :=
  | rep_enum :
      forall c name namei it  n,
        M.get c cenv = Some (Build_ctor_ty_info name namei it 0%N n) ->
        (* there should not be more than 2^(intsize - 1) unboxed constructors *)
        (0 <= (Z.of_N n) <   Ptrofs.half_modulus)%Z ->
      correct_crep cenv c (enum n)
  | rep_boxed:
      forall c name namei it a n,
        M.get c cenv = Some (Build_ctor_ty_info name namei it (Npos a%N) n) ->
        (* there should not be more than 2^8 - 1 boxed constructors *)
        (0 <= (Z.of_N n) <  Zpower.two_p 8)%Z ->
        (* arity shouldn't be higher than 2^54 - 1  *)
        (0 <= Z.of_N (Npos a) <  Zpower.two_power_nat (Ptrofs.wordsize - 10))%Z ->
      correct_crep cenv c (boxed n (Npos a)).

  (* crep <-> make_ctor_rep cenv *)
  Definition correct_crep_of_env: LambdaANF.term.ctor_env -> M.t ctor_rep -> Prop :=
    fun cenv crep_env =>
      (forall c name namei it a n,
        M.get c cenv = Some (Build_ctor_ty_info name namei it a n) ->
        exists crep, M.get c crep_env = Some crep /\
                     correct_crep cenv c crep) /\
      (forall c crep, M.get c crep_env = Some crep ->
                     correct_crep cenv c crep).


  Definition correct_cenv_of_env: ctor_env -> term.M.t term.val -> Prop :=
    fun cenv rho =>
      forall x v,
        M.get x rho = Some v ->
        correct_cenv_of_val cenv v.

  Definition correct_envs: ctor_env -> n_ind_env -> M.t ctor_rep ->  term.M.t term.val ->  exp -> Prop :=
    fun cenv ienv crep_env rho e =>
      correct_ienv_of_cenv cenv ienv /\
      correct_cenv_of_env cenv rho /\
      correct_cenv_of_exp cenv e /\
      correct_crep_of_env cenv crep_env.

  Theorem correct_envs_subterm:
    forall cenv ienv crep rho e,
           correct_envs cenv ienv crep rho e ->
    forall e', subterm_e e' e ->
               correct_envs cenv ienv crep rho e'.
  Proof.
    intros.
    inv H. inv H2. inv H3. split; auto.
    split; auto. split; auto.
    eapply Forall_constructors_subterm; eauto.
  Qed.


  Theorem correct_envs_set:
    forall cenv ienv crep rho x v e,
    correct_envs cenv ienv crep rho e ->
    correct_cenv_of_val cenv v ->
    correct_envs cenv ienv crep (M.set x v rho) e.
  Proof.
    intros.
    inv H. inv H2. inv H3.
    split; auto. split; auto.
    intro; intros. destruct (var_dec x0 x).
    - subst.  rewrite M.gss in H3.
      inv H3. auto.
    - rewrite M.gso in H3 by auto.
      eapply H; eauto.
  Qed.


  (*
   correct_tinfo alloc_id limit_id args_id alloc_max le m
  > alloc and limit are respectively valid and weak-valid pointers in memory, alloc is at least max before limit_id
  > args points to an array of size max_args in memory before alloc

limit might be on the edge of current memory so weak_valid, alloc and args are pointing in mem. the int is the max number of blocks allocated by the function

   *)

Definition correct_tinfo: program ->  Z -> temp_env ->  mem  -> Prop :=
  fun p max_alloc lenv m  =>
    exists alloc_b alloc_ofs limit_ofs args_b args_ofs tinf_b tinf_ofs,
      M.get allocIdent lenv = Some (Vptr alloc_b alloc_ofs) /\
      (align_chunk int_chunk | Ptrofs.unsigned alloc_ofs)%Z /\
      (* everything between alloc_ofs and limit_fs is writable *)
      Mem.range_perm m alloc_b (Ptrofs.unsigned alloc_ofs) (Ptrofs.unsigned limit_ofs) Cur Writable /\
      M.get limitIdent lenv = Some (Vptr alloc_b limit_ofs) /\
      (* alloc is at least max blocks from limit *)
      (int_size*max_alloc <= (Ptrofs.unsigned limit_ofs -  Ptrofs.unsigned alloc_ofs) <= gc_size)%Z /\
      M.get argsIdent lenv = Some (Vptr args_b args_ofs) /\
      (* args is in a different block from alloc *)
      args_b <> alloc_b /\
      (* the max_args int blocks after args are Writable *)
      ((Ptrofs.unsigned args_ofs)+ int_size * max_args <= Ptrofs.max_unsigned)%Z  /\
      (forall i, 0 <= i < max_args ->  Mem.valid_access m int_chunk args_b (Ptrofs.unsigned (Ptrofs.add args_ofs (Ptrofs.mul (Ptrofs.repr int_size) (Ptrofs.repr i))))  Writable)%Z /\
      M.get tinfIdent lenv = Some (Vptr tinf_b tinf_ofs) /\
      tinf_b <> args_b /\
      tinf_b <> alloc_b /\
      (* valid access on four pointers in tinfo *)
      (forall i, 0 <= i < 4 -> Mem.valid_access m int_chunk tinf_b (Ptrofs.unsigned (Ptrofs.add tinf_ofs (Ptrofs.repr (int_size*i)))) Writable)%Z
      /\  deref_loc (Tarray uval maxArgs noattr) m tinf_b (Ptrofs.add tinf_ofs (Ptrofs.repr (int_size*3))) (Vptr args_b args_ofs) /\
(* everything pointed to by globals is valid, and not alloc, tinf or args*)
      (forall x b,
          Genv.find_symbol (globalenv p) x = Some b ->
          b <> args_b /\ b <> alloc_b /\ b <> tinf_b /\ (exists chunk, Mem.valid_access m chunk b 0%Z Nonempty)).


Theorem range_perm_to_valid_access:
  forall alloc_b alloc_ofs limit_ofs size m,
    Mem.range_perm m alloc_b alloc_ofs limit_ofs Cur Writable ->
    forall ofs,
      (align_chunk size | ofs)%Z ->
      (alloc_ofs <= ofs)%Z ->
      (ofs + size_chunk size <= limit_ofs)%Z ->
      Mem.valid_access m size alloc_b ofs Writable.
  Proof.
    intros.
    constructor; auto.
    intro. intro.
    eapply H.
    omega.
  Qed.


Theorem correct_tinfo_mono:
  forall p z lenv m,
    correct_tinfo p z lenv m ->
    forall z',
      (0 <= z' <= z)%Z ->
    correct_tinfo p z' lenv m.
Proof.
  intros.
  inv H; destructAll.
  do 7 eexists.
  repeat (split; eauto).
  unfold int_size in *. chunk_red; omega.
Qed.


Theorem correct_tinfo_proper:
  forall p z lenv m lenv',
  correct_tinfo p z lenv m ->
  map_get_r_l _ [argsIdent; limitIdent; allocIdent;  tinfIdent] lenv lenv' ->
  correct_tinfo p z lenv' m.
Proof.
  intros.
  inv H; destructAll.
  exists x, x0, x1, x2, x3, x4, x5.
  repeat (split; auto; try (rewrite <- H0; auto; inList)).
Qed.

Theorem correct_tinfo_not_protected:
  forall p z lenv m,
  correct_tinfo p z lenv m ->
  forall x v,
    ~ is_protected_tinfo_id_thm x ->
    x <> tinfIdent ->
  correct_tinfo p z (M.set x v lenv) m.
Proof.
  intros.
  destruct H as [alloc_b [alloc_ofs [limit_ofs [args_b [args_ofs [tinf_b [tinf_ofs H]]]]]]].
  exists alloc_b, alloc_ofs, limit_ofs, args_b, args_ofs, tinf_b, tinf_ofs.
  destructAll.
  repeat (split; auto).
  rewrite M.gso; auto. intro. apply H0. left; auto.
  rewrite M.gso; auto. intro. apply H0. right; auto.
  rewrite M.gso; auto. intro. apply H0. right; auto.
  rewrite M.gso; auto.
Qed.


Theorem correct_tinfo_param_asgn:
  forall p lenv m xs z vs7 lenv',
  correct_tinfo p z lenv m ->
  lenv_param_asgn lenv lenv' xs vs7 ->
  (forall x, List.In x xs -> ~ (is_protected_tinfo_id_thm x \/ x = tinfIdent)) ->
  correct_tinfo p z lenv' m.
Proof.
  intros.
  destruct H.
  destructAll.
  exists x, x0, x1, x2, x3, x4, x5.
  repeat (split; auto; try (eapply lenv_param_asgn_not_in with (L :=  fun x => (is_protected_tinfo_id_thm x \/ x = tinfIdent)); eauto; try (left; inList); try (right; reflexivity))).
Qed.





Theorem mem_range_valid: forall m m',
    (forall b ofs ofs'  p, Mem.range_perm m b ofs ofs' Cur p -> Mem.range_perm m' b ofs ofs' Cur p) <->
    (forall b ofs chunk  p, Mem.valid_access m chunk b ofs p -> Mem.valid_access m' chunk b ofs p).
Proof.
  split.
  - intros.
    inv H0.
    apply H in H1.
    constructor;  auto.
  - intros.
    intro.
    intros.
    specialize (H b ofs0  Mint8unsigned p).
    apply H0 in H1.
    assert ( Mem.valid_access m Mint8unsigned b ofs0 p).
    constructor. simpl. intro. intro. assert (ofs0 = ofs1)%Z by omega. subst; auto.
    simpl. apply Z.divide_1_l. apply H in H2. inv H2. simpl in H3.
    eapply H3. omega.
Qed.


Theorem correct_tinfo_valid_access:
  forall  p z lenv m,
    correct_tinfo p z lenv m ->
    forall m',
    (forall b ofs ofs'  p, Mem.range_perm m b ofs ofs' Cur p -> Mem.range_perm m' b ofs ofs' Cur p) ->
    correct_tinfo p z lenv m'.
Proof.
  intros.
  unfold correct_tinfo in H.
  destruct H as [alloc_b [alloc_ofs [limit_ofs [args_b [args_ofs [tinf_b [tinf_ofs [Hget_alloc [Hdiv_alloc [Hrange_alloc [Hget_limit [Hbound_limit [Hget_args [Hdj_args [Hbound_args [Hrange_args [Hget_tinf [Htinfne1 [Htinfne2 [Hinf_limit [Hloc_args  Hglobal ]]]]]]]]]]]]]]]]]]]]].
  do 7 eexists.

  repeat (split; eauto).
  eapply H0.
  eapply Hrange_args.
  auto.

  apply Hrange_args in H.
  inv H. auto.
  eapply H0.
  apply Hinf_limit. auto.
  apply Hinf_limit. auto.

  inv Hloc_args. inv H. constructor; auto. inv H1.



  apply Hglobal in H. destructAll; auto.
  apply Hglobal in H; destructAll; auto.
  apply Hglobal in H; destructAll; auto.
  erewrite mem_range_valid in H0.
  apply Hglobal in H. destructAll.
  exists x0. apply H0. auto.
Qed.

Corollary correct_tinfo_after_store:
  forall p z lenv m,
    correct_tinfo p z lenv m ->
    forall m' chunk b ofs v,
      Mem.store chunk m b ofs v = Some m' ->
    correct_tinfo p z lenv m'.
Proof.
  intros.
  eapply correct_tinfo_valid_access.
  apply H.
  eapply mem_range_valid. intros.
  eapply Mem.store_valid_access_1 in H0; eauto.
Qed.

Corollary valid_access_after_nstore:
  forall  vs m m' i b' ofs',
    forall chunk b ofs p, Mem.valid_access m chunk b ofs p ->
                          mem_after_n_proj_store b' ofs' vs i m m' ->
                         Mem.valid_access m' chunk b ofs p.
Proof.
  induction vs; intros.
  - inv H0.
  - inv H0.
    + eapply Mem.store_valid_access_1; eauto.
    + eapply IHvs.
      2: apply H9.
      eapply Mem.store_valid_access_1; eauto.
Qed.


Corollary correct_tinfo_after_nstore:
  forall p vs  z lenv m m' b ofs i,
    correct_tinfo p z lenv m ->
      mem_after_n_proj_store b ofs vs i m m' ->
      correct_tinfo p z lenv m'.
Proof.
  induction vs; intros.
  - inv H0.
  -   inv H0.
      + eapply correct_tinfo_after_store; eauto.
      + eapply IHvs. 2:{ apply H9. }
        eapply correct_tinfo_after_store; eauto.
Qed.




Theorem var_names_app:
  forall l1 l2,
    (var_names (l1 ++ l2)) = (var_names l1 ++ var_names l2).
Proof.
  induction l1. reflexivity.
  intros.
  destruct a; simpl. rewrite IHl1. reflexivity.
Qed.






Definition repr_expr_LambdaANF_Codegen_id := repr_expr_LambdaANF_Codegen argsIdent allocIdent limitIdent threadInfIdent tinfIdent
     isptrIdent caseIdent nParam.


Definition rel_mem_LambdaANF_Codegen_id := rel_mem_LambdaANF_Codegen argsIdent allocIdent limitIdent gcIdent threadInfIdent tinfIdent
   isptrIdent caseIdent nParam.


Definition repr_val_L_LambdaANF_Codegen_id := repr_val_L_LambdaANF_Codegen argsIdent allocIdent limitIdent gcIdent threadInfIdent tinfIdent isptrIdent caseIdent nParam.

Definition repr_val_id_L_LambdaANF_Codegen_id := repr_val_id_L_LambdaANF_Codegen
    argsIdent allocIdent limitIdent gcIdent threadInfIdent tinfIdent isptrIdent
     caseIdent nParam.

Definition protected_id_not_bound_id := protected_id_not_bound argsIdent allocIdent limitIdent gcIdent mainIdent bodyIdent threadInfIdent tinfIdent heapInfIdent numArgsIdent isptrIdent
   caseIdent.

Definition protected_not_in_L_id := protected_not_in_L argsIdent allocIdent limitIdent tinfIdent.

Theorem Z_non_neg_add:
        forall n m p,
        (n <= m -> 0 <= p -> n <= p + m)%Z.
Proof.
  intros.
  etransitivity. eauto. omega.
Qed.

(* ident[n] contains either a Vint representing an enum or an integer OR a pointer to a function or the boxed representation of v *)
Inductive nth_arg_rel_LambdaANF_Codegen (fenv:fun_env) (finfo_env:fun_info_env) (p:program) (rep_env: M.t ctor_rep) : LambdaANF.eval.env -> positive -> temp_env -> mem -> Z -> Prop :=
| is_in_and_rel:
    forall lenv args_b args_ofs rho m n x LambdaANFv Codegenv L,
       protected_not_in_L argsIdent allocIdent limitIdent tinfIdent p lenv  L ->
      (* get the value rho(x)*)
      M.get x rho = Some LambdaANFv ->
      (* get Vargs pointer and load the value from it *)
      M.get argsIdent lenv = Some (Vptr args_b args_ofs) ->
      Mem.load int_chunk m args_b (Ptrofs.unsigned (Ptrofs.add args_ofs  (Ptrofs.mul
                   (Ptrofs.repr (sizeof (M.empty composite) val))
                   (Ptrofs.repr n)))) = Some Codegenv ->
      (* relate both val *)
      repr_val_L_LambdaANF_Codegen_id fenv finfo_env p rep_env LambdaANFv m L Codegenv ->
          nth_arg_rel_LambdaANF_Codegen fenv finfo_env p rep_env rho x lenv m n.


Theorem caseConsistent_findtag_In_cenv:
  forall cenv t e l,
    caseConsistent cenv l t ->
    findtag l t = Some e ->
    exists (a aty:BasicAst.name) (ty:ind_tag) (n:N) (i:N), M.get t cenv = Some (Build_ctor_ty_info a aty ty n i).
Proof.
  destruct l; intros.
  - inv H0.
  - inv H. destruct info.
    exists ctor_name, ctor_ind_name, ctor_ind_tag,ctor_arity,ctor_ordinal; auto.
Qed.


Inductive isPtr_sem: Events.extcall_sem :=
| isPtr_true : forall genv m b ofs,
    isPtr_sem genv ((Vptr b ofs)::nil) m nil (Vtrue) m
| isPtr_false : forall genv m i,
    isPtr_sem genv ((Vint i)::nil) m nil (Vfalse) m.


Definition bind_n_after_ptr (n:Z) (x:block) (x0:Z) (L: block -> Z -> Prop): block -> Z -> Prop :=
  fun b ofs =>
                   match Pos.eqb b x with
                   | true => (match Z.leb x0 ofs with
                              | true =>
                                (match Z.ltb ofs (x0 + n)%Z with
                                 | true => True
                                 | false => L b ofs
                                 end)
                              | false => L b ofs
                              end
                             )
                   | false => L b ofs
                   end.

Theorem bind_n_after_ptr_def:
  forall n x x0 L b ofs,
  bind_n_after_ptr n x x0 L b ofs
  <->
  (L b ofs \/ (b = x /\ x0 <= ofs < x0 + n))%Z.
Proof.
  intros. unfold bind_n_after_ptr.
  destruct (b =? x)%positive eqn:bxeq.
  apply Peqb_true_eq in bxeq; subst.
  destruct (x0 <=? ofs)%Z eqn:x0ofsle.
  destruct (ofs <? x0 + n)%Z eqn:ofsx0lt.
  split; auto.
  intro. right; auto. split; auto.
  split.
  apply Zle_bool_imp_le in x0ofsle. auto.
  apply Z.ltb_lt in ofsx0lt. auto.
  split; auto.
  intro. inv H; auto. destruct H0.
  apply OrdersEx.Z_as_DT.ltb_nlt in ofsx0lt.
  exfalso; omega.
  split; auto. intros.
  inv H; auto.
  destruct H0.
  apply Z.leb_nle in x0ofsle. exfalso; omega.
  split; auto. intro.
  inv H; auto.
  destruct H0.
  apply Pos.eqb_neq in bxeq. exfalso; auto.
Qed.



Inductive bind_n_after_ptr_rev: nat -> block -> Z ->  (block -> Z -> Prop) -> (block -> Z -> Prop) -> Prop :=
| Bind_0_ind: forall b ofs L,  bind_n_after_ptr_rev 0 b ofs L L

| Bind_S_ind : forall n b ofs L L',
    bind_n_after_ptr_rev n b (ofs + int_size) L L' ->
    bind_n_after_ptr_rev (S n) b ofs L (fun b' z => L' b' z \/ (b = b' /\ ofs <= z < ofs + int_size)%Z).






Theorem bind_n_after_ptr_exists':
forall n b ofs L,
exists L',
  bind_n_after_ptr_rev n b ofs L L'.
Proof.
  induction n; intros.
  eexists. constructor.
  specialize (IHn b (ofs+int_size)%Z L). inv IHn.
  eexists.  constructor. eauto.
Qed.


Theorem bind_n_after_ptr_from_rev:
forall n b ofs L L',
  bind_n_after_ptr_rev n b ofs L L' -> (forall b' z', (bind_n_after_ptr ((Z.of_nat n) * int_size) b ofs L) b' z' <-> L' b' z').
Proof.
  induction n; intros.
  -  inv H. split.  intro. rewrite bind_n_after_ptr_def in H. inv H; auto. destruct H0.  simpl in H0.
    exfalso.  omega.
    rewrite bind_n_after_ptr_def. auto.
  - inv H.
    specialize (IHn _ _ _ _ H1).
    split; intro.
    + rewrite bind_n_after_ptr_def in H.
      inv H.
      * left.
        rewrite <- IHn.
        rewrite bind_n_after_ptr_def. auto.
      * (* either z is in the first portion OR it is in the rest of the binds *)
        rewrite <- IHn.
        rewrite bind_n_after_ptr_def.
        destruct H0.
        unfold int_size in *; simpl size_chunk in *.
        rewrite Nat2Z.inj_succ in H0.
        assert (0 <= Z.of_nat n)%Z by apply Zle_0_nat.
        assert (Hcase := Z.lt_ge_cases z' (ofs+int_size)%Z).
        destruct Hcase.
        right.  split; auto.  chunk_red; omega.
        left. right. split; auto. chunk_red; omega.
    + inv H.
      rewrite <- IHn in H0.
      rewrite bind_n_after_ptr_def.
      rewrite bind_n_after_ptr_def in H0.
      rewrite Nat2Z.inj_succ.
      rewrite Z.mul_succ_l. destruct H0. auto. right.
      destruct H. split; auto. chunk_red; omega.
      rewrite bind_n_after_ptr_def.
      right.       unfold int_size in *; simpl size_chunk in *.
      destruct H0. split. auto.
      rewrite Nat2Z.inj_succ.
      rewrite Z.mul_succ_l. chunk_red; omega.
Qed.


Theorem bind_n_after_ptr_exists:
forall n b ofs L,
exists L',
  bind_n_after_ptr_rev n b ofs L L' /\ (forall b' z', (bind_n_after_ptr ((Z.of_nat n) * int_size) b ofs L) b' z' <-> L' b' z').
Proof.
  intros.
  assert (H_L := bind_n_after_ptr_exists' n b ofs L).
  destruct H_L.
  exists x. split. auto.
  eapply bind_n_after_ptr_from_rev. auto.
Qed.


Theorem load_ptr_or_int:
  forall y,
    Vint_or_Vptr y = true ->
    Val.load_result int_chunk y = y.
Proof.
  intros. simpl. destruct y; inv H; auto.
Qed.




Theorem mem_after_n_proj_rev_unchanged:
  forall b  vs ofs m m',
    mem_after_n_proj_store_rev b ofs vs m m' ->
    forall L,
  (forall j, ofs <= j < ofs+int_size*(Z.of_nat (length vs)) ->  ~ L b j)%Z ->
  Mem.unchanged_on L m m'.
Proof.
  induction vs; intros; inv H.
  -  eapply Mem.store_unchanged_on. eauto.
     simpl in H0.
     simpl size_chunk. auto.
  - eapply IHvs with (L := L) in H5.
    + apply Mem.unchanged_on_trans with (m2 := m'0).
      auto.
      eapply Mem.store_unchanged_on; eauto.
      intros. apply H0.
      simpl length.
      rewrite Nat2Z.inj_succ.
      chunk_red;
      omega.
    + intros. apply H0.
      simpl length.
      rewrite Nat2Z.inj_succ.
      chunk_red;
      omega.
Qed.

(* not true as state, m' are equivalent w.r.t. load, may not be equal. also
need a lemma that says you can commute store which don't affect each other
Theorem mem_after_n_proj_eq_rev:
  forall b vs ofs i m m',
  mem_after_n_proj_store_rev b (ofs + (int_size * i)) vs m m' <->
  mem_after_n_proj_store b ofs vs i m m'.
Proof.
  induction vs.
  - intros.
    split; intro; inv H.
  - intros.
    split; intro; inv H.
    + constructor. auto.
    + rewrite <- Z.add_assoc in H4. rewrite <- Z.mul_succ_r in H4.
      econstructor.
      SearchAbout Mem.store.
    + constructor. auto.
    +
*)
Definition arg_val_LambdaANF_Codegen (fenv:fun_env) (finfo_env:fun_info_env) (p:program) (rep_env: M.t ctor_rep): LambdaANF.term.val -> mem -> temp_env -> Prop :=
  fun v m lenv =>
    exists args_b args_ofs Codegenv L,
(*       M.get tinfIdent lenv = Some (Vptr tinf_b tinf_ofs) /\
      deref_loc (Tarray uval maxArgs noattr) m tinf_b (Ptrofs.add tinf_ofs (Ptrofs.repr 12)) (Vptr args_b args_ofs) /\ *)
      M.get argsIdent lenv = Some (Vptr args_b args_ofs) /\
                                  Mem.load int_chunk m args_b (Ptrofs.unsigned (Ptrofs.add args_ofs (Ptrofs.repr int_size))) = Some Codegenv /\
                                  repr_val_L_LambdaANF_Codegen_id fenv finfo_env p rep_env v m L Codegenv.


Definition same_args_ptr lenv lenv' :=
  @M.get  Values.val argsIdent lenv = M.get argsIdent lenv'.

Definition same_tinf_ptr lenv lenv' :=
  @M.get Values.val tinfIdent lenv =  M.get tinfIdent lenv'.

Definition mem_same_block (b:block) (m m':mem) : Prop :=
  forall chunk ofs,
    Mem.load chunk m b ofs = Mem.load chunk m' b ofs.


Theorem max_allocs_case:
  forall c e y cl,
  List.In (c, e) cl ->
  max_allocs e <= max_allocs (Ecase y cl).
Proof.
  induction cl; intros.
  inv H.
  simpl. destruct a. inv H.
  - inv H0.
    apply Nat.le_max_l.
  - apply IHcl in H0. simpl in H0.
    etransitivity. apply H0.
    apply Nat.le_max_r.
Qed.


Theorem get_list_cons :
  forall A rho v ys vs,
    @get_list A ys rho = Some (v :: vs) ->
  exists y ys', ys = y::ys' /\
                term.M.get y rho = Some v /\
                get_list ys' rho = Some vs.
Proof.
  intros. destruct ys as [ | y ys'].
  inv H. exists y, ys'.
  split; auto.  simpl in H.
  destruct  (term.M.get y rho).
  destruct (get_list ys' rho). inv H. auto.
  inv H. inv H.
Qed.


Theorem exists_getvar_or_funvar_list:
  forall lenv p rho L rep_env finfo_env argsIdent allocIdent limitIdent gcIdent threadInfIdent tinfIdent isptrIdent caseIdent nParam fenv
         m xs vs,
            ( forall x, List.In x xs ->
                        exists v6 : term.val,
         M.get x rho = Some v6 /\
         repr_val_id_L_LambdaANF_Codegen argsIdent allocIdent limitIdent gcIdent threadInfIdent tinfIdent isptrIdent caseIdent nParam fenv finfo_env
                             p rep_env v6 m L lenv x)
            ->
            get_list xs rho = Some vs  ->
            exists vs7 : list Values.val, get_var_or_funvar_list p lenv xs = Some vs7.
Proof.
  induction xs; intros.
  - exists nil. auto.
  - simpl in H0.
    destruct (term.M.get a rho) eqn:Hgar.
    destruct (get_list xs rho) eqn:Hgxsr.
    inv H0.
    specialize (IHxs l).
    assert ((forall x : positive,
          List.In x xs ->
          exists v6 : term.val,
            M.get x rho = Some v6 /\
            repr_val_id_L_LambdaANF_Codegen argsIdent0 allocIdent0 limitIdent0 gcIdent0 threadInfIdent0 tinfIdent0 isptrIdent0 caseIdent0 nParam0
                                fenv finfo_env p rep_env v6 m L lenv x)).
    {
      intros. apply H. constructor 2; auto.
    }
    apply IHxs in H0. destruct H0.
    assert
      (exists v6 : term.val,
        M.get a rho = Some v6 /\
        repr_val_id_L_LambdaANF_Codegen argsIdent0 allocIdent0 limitIdent0 gcIdent0 threadInfIdent0 tinfIdent0 isptrIdent0 caseIdent0 nParam0 fenv
                            finfo_env p rep_env v6 m L lenv a).
    apply H. constructor. reflexivity.
    destruct H1. destruct H1.
    rewrite H1 in Hgar. inv Hgar.
    inv H2. eexists. simpl. rewrite H0. rewrite H3. reflexivity.
    destruct Archi.ptr64 eqn:Harchi; eexists; simpl; rewrite H0; rewrite H3; rewrite H4; inv H5; archi_red; reflexivity.
    reflexivity.
    inv H0.
    inv H0.
Qed.



Theorem store_unchanged_on' :
        forall m m'' m' L v b chunk ofs,
          Mem.unchanged_on L m m'' ->
          (forall i, ofs <= i < ofs + size_chunk chunk -> ~ L b i)%Z ->
          Mem.store chunk m' b ofs v = Some m'' ->
          Mem.unchanged_on L m m'.
Proof.
  intros. inv H. constructor.
  - apply Mem.nextblock_store in H1.
    rewrite <- H1. auto.
  - split; intros.
    eapply Mem.perm_store_2.
    apply H1. apply unchanged_on_perm; auto.
    apply unchanged_on_perm; auto.
    eapply Mem.perm_store_1; eauto.
  - intros.
    rewrite <- unchanged_on_contents; auto.
    symmetry.
    erewrite Mem.store_mem_contents; eauto.
    rewrite Maps.PMap.gsspec.
    destruct (Coqlib.peq b0 b); auto. subst b0. apply Mem.setN_outside.
  rewrite encode_val_length. rewrite <- size_chunk_conv.
  destruct (Coqlib.zlt ofs0 ofs); auto.
  destruct (Coqlib.zlt ofs0 (ofs + size_chunk chunk)); auto.
  elim (H0 ofs0). chunk_red; omega. auto.
Qed.








Theorem sem_shr_unboxed:
  forall n,
(*     sem_shr (Vint n) val (Vint (Int.repr 1)) val = Some (Vint (Int.repr (Z.shiftr (Int.unsigned n) 1))).*)

    sem_shr (make_vint (Ptrofs.unsigned n)) val (make_vint 1) val = Some (make_vint (Z.shiftr (Ptrofs.unsigned n) 1)).
Proof.
  intros.
  unfold sem_shr. unfold sem_shift. simpl.
  assert (Hrange:= uint_range_unsigned n).
  destruct Archi.ptr64 eqn:Harchi;
    archi_red; unfold classify_shift; simpl.
  {   (* unfold Int64.ltu. rewrite Coqlib.zlt_true. *)
      rewrite Int64.shru_div_two_p.
      rewrite Int64.Zshiftr_div_two_p by omega.
      rewrite Int64.unsigned_repr by (archi_red; solve_uint_range; omega).
      unfold Int64.iwordsize. unfold Int64.zwordsize. simpl.
      unfold Int64.ltu.
      rewrite Int64.unsigned_repr by (unfold Int64.max_unsigned; solve_uint_range; omega).
      rewrite Int64.unsigned_repr by (unfold Int64.max_unsigned; solve_uint_range; omega).
  unfold classify_shift. simpl. reflexivity.
}
{
  rewrite Int.shru_div_two_p.
  rewrite Int.Zshiftr_div_two_p by omega.
  rewrite Int.unsigned_repr by (archi_red; solve_uint_range; omega).
  unfold Int.iwordsize. unfold Int.zwordsize. simpl.
  unfold Int.ltu.
  rewrite Int.unsigned_repr by (solve_uint_range; omega).
  rewrite Int.unsigned_repr by (solve_uint_range; omega).
  unfold classify_shift. simpl. reflexivity.
}
Qed.


Theorem sem_switch_and_255: forall h,
     (0 <= h <= Ptrofs.max_unsigned)%Z ->
  sem_switch_arg (int_and h 255) uval = Some (Z.land h 255).
Proof.
  intros.
  rewrite ptrofs_mu in H.
  unfold sem_switch_arg. unfold int_and.
  destruct Archi.ptr64 eqn:Harchi;
    archi_red; unfold classify_shift; simpl.
  { unfold Int64.and.
    rewrite Int64.unsigned_repr with (z := h) by (archi_red; solve_uint_range; omega).
    rewrite Int64.unsigned_repr with (z := 255%Z) by (archi_red; solve_uint_range; omega).
    rewrite Int64.unsigned_repr. reflexivity.
    replace 255%Z with (Z.ones 8) by reflexivity.
    rewrite Z.land_ones. unfold Int64.max_unsigned in *; simpl in *.
    assert ( (0 <= h mod Z.pow_pos 2 8 < Z.pow_pos 2 8)%Z).
    apply Z.mod_bound_pos.  omega. compute. reflexivity.
    destruct H0. split; auto.
    eapply OrdersEx.Z_as_OT.lt_le_incl.
    eapply OrdersEx.Z_as_DT.lt_le_trans.
    eauto. compute. intro. inv H2.
    omega.
  }
  { unfold Int.and.
    rewrite Int.unsigned_repr with (z := h) by (archi_red; solve_uint_range; omega).
    rewrite Int.unsigned_repr with (z := 255%Z) by (archi_red; solve_uint_range; omega).
    rewrite Int.unsigned_repr. reflexivity.
    replace 255%Z with (Z.ones 8) by reflexivity.
    rewrite Z.land_ones. unfold Int.max_unsigned in *; simpl in *.
    assert ( (0 <= h mod Z.pow_pos 2 8 < Z.pow_pos 2 8)%Z).
    apply Z.mod_bound_pos.  omega. compute. reflexivity.
    destruct H0. split; auto.
    eapply OrdersEx.Z_as_OT.lt_le_incl.
    eapply OrdersEx.Z_as_DT.lt_le_trans.
    eauto. compute. intro. inv H2.
    omega.
  }
Qed.

Theorem sem_switch_arg_1: forall n,
     (0 <= n <= Ptrofs.max_unsigned)%Z ->
        sem_switch_arg (int_shru n 1) uval = Some (Z.shiftr n 1).
Proof.
  intros. rewrite ptrofs_mu in H.
  unfold sem_switch_arg. unfold int_shru.

  destruct Archi.ptr64 eqn:Harchi;
    archi_red; unfold classify_shift; simpl.
  {   (* unfold Int64.ltu. rewrite Coqlib.zlt_true. *)
    rewrite Int64.shru_div_two_p.
    rewrite Int64.Zshiftr_div_two_p by omega.
      rewrite Int64.unsigned_repr with (z := n) by (archi_red; solve_uint_range; omega).
      rewrite Int64.unsigned_repr with (z := 1%Z) by (archi_red; solve_uint_range; omega).
      rewrite Int64.unsigned_repr. reflexivity.
      unfold Int64.max_unsigned; solve_uint_range.
    unfold  Zpower.two_power_pos.  simpl.
    inv H. split.
    apply Z.div_pos; omega.
    apply OrdersEx.Z_as_OT.div_le_upper_bound. omega. omega.
}
  {
        rewrite Int.shru_div_two_p.
    rewrite Int.Zshiftr_div_two_p by omega.
      rewrite Int.unsigned_repr with (z := n) by (archi_red; solve_uint_range; omega).
      rewrite Int.unsigned_repr with (z := 1%Z) by (archi_red; solve_uint_range; omega).
      rewrite Int.unsigned_repr. reflexivity.
      unfold Int.max_unsigned; solve_uint_range.
    unfold  Zpower.two_power_pos.  simpl.
    inv H. split.
    apply Z.div_pos; omega.
    apply OrdersEx.Z_as_OT.div_le_upper_bound. omega. omega.
  }
Qed.


(* Two constructors of the same inductive cannot have the same ordinal *)
Theorem disjoint_ord:
  forall {cenv ienv c c' namec namec' namei namei' i a a' ord ord'},
    correct_ienv_of_cenv cenv ienv ->
    M.get c cenv = Some (Build_ctor_ty_info namec namei i a ord) ->
    M.get c' cenv = Some (Build_ctor_ty_info namec' namei' i a' ord') ->
    (c <> c' <-> ord <> ord').
Proof.
  intros.
  apply H in H0. apply H in H1. destructAll.
  rewrite H1 in H0. inv H0.
  split; intro; intro; subst.
  - (* c -> ord *)
    apply H7. exists namec', c', a'.  split. intro. inv H8. apply H0; auto. auto.
  - (* ord -> c *)
    apply H6. exists ord', namec', a'. split. intro. inv H8. apply H0; auto. auto.
Qed.



Theorem pos_iter_injective:
  forall A f,
         (forall a b, f a = f b -> a = b) ->
         forall p (a b:A),
  Pos.iter f a p = Pos.iter f b p ->
  a = b.
Proof.
  induction p; intros.
  simpl in H0.
  apply H in H0.
  apply IHp in H0. apply IHp in H0. auto.
  simpl in H0. apply IHp in H0. apply IHp; auto.
  simpl in H0. apply H; auto.
Qed.


Theorem shiftl_injective:
  forall c a b,
    (0 <= c)%Z ->
  Z.shiftl a c = Z.shiftl b c ->
  a = b.
Proof.
  induction c; intros.
  simpl in *. auto.
  simpl in H0.
  apply pos_iter_injective in H0. auto.
  intros. omega.
  simpl in H0. exfalso.
  assert (Z.neg p < 0)%Z by apply Pos2Z.neg_is_neg.
  omega.
Qed.

Theorem unzip_vars:
  forall vs0 vars x,
    Forall2 (fun (x0 : var) (xt : var * type) => xt = (x0, uval)) vs0 vars ->
    List.In x (var_names vars) <->
    List.In x vs0.
Proof.
  induction vs0; intros.
  inv H. split; intro H; inv H.
  inv H. simpl.
  apply IHvs0 with (x := x) in H4.
  rewrite <- H4. reflexivity.
Qed.



Theorem case_of_labeled_stm_unboxed:
  forall rep_env arr t  n0 e p fenv finfo_env ienv cenv ,
    correct_ienv_of_cenv cenv ienv ->
    M.get t rep_env = Some (enum arr) ->
    correct_crep_of_env cenv  rep_env ->
    repr_unboxed_Codegen arr n0 ->
    forall cl ls ls',
      caseConsistent cenv cl t ->
  findtag cl t = Some e ->
  repr_branches_LambdaANF_Codegen argsIdent allocIdent limitIdent threadInfIdent tinfIdent isptrIdent caseIdent nParam fenv finfo_env p rep_env cl ls ls' ->
  exists s s',
    seq_of_labeled_statement (select_switch (Z.shiftr n0 1) ls') = (Ssequence (Ssequence s Sbreak) s') /\  repr_expr_LambdaANF_Codegen_id fenv finfo_env p rep_env e s.
Proof.
  intros rep_env arr t  n0 e p fenv finfo_env ienv cenv Hienv H H0 H1.
  induction cl;
  intros ls ls' Hcc; intros.
  (* impossible empty cl *)  inv H2.
  simpl in H2. destruct a. destruct (M.elt_eq c t).
  - (* is-case *)
    inv H2. inv H3.
    (* remove impossible boxed cases *)
    3:{   rewrite H10 in H. inv H. }
    3:{  rewrite H10 in H. inv H. }
    + (* default *)
      simpl. exists s, Sskip.
      split. reflexivity.
      auto.
    + rewrite H10 in H. inv H.
      exists s, (seq_of_labeled_statement ( (LScons lsa' lsb' lsc'))). split; auto.
      simpl. unfold select_switch. simpl.

      assert (tag = n0).
      inv H11; inv H1. auto.
      subst.
      rewrite Coqlib.zeq_true.
      simpl. reflexivity.
  - (*is not case -- IH *)
    inv H3.
    + (* impossible because rep_env is correct, t is in cl but cl -unboxed-> LSnil *)
      exfalso.
      assert (Hn_repr := repr_branches_LSnil_no_unboxed _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ H2 H11). apply Hn_repr.
      eauto.
     + simpl. (* c <> t so arr <> n1 and the headers are different *)
       unfold select_switch.
       simpl select_switch_case.
       rewrite Coqlib.zeq_false.
       inv Hcc.
       specialize (IHcl _ _ H14 H2 H7). apply IHcl.
       inv H0. apply H4 in H11.
       apply H4 in H. inv H. inv H11.
       assert (it = it0). {
         inv Hcc.  rewrite H5 in H13; rewrite H0 in H14; inv H13; inv H14. auto.
       }
       subst.
       assert (n1 <> arr). {
         assert (Hdj := disjoint_ord Hienv H0 H5).
         apply Hdj. auto.
       }
       inv Hcc. rewrite H5 in H14; inv H14. rewrite H0 in H15; inv H15.
       intro. do 2 (erewrite repr_unboxed_shiftr in H6 by eauto).
       apply H. apply N2Z.inj. apply H6.
     + inv Hcc; eapply IHcl; eauto.
     + inv Hcc; eapply IHcl; eauto.
Qed.

(*
Definition z_and z1 z2 :=
  if Archi.ptr64 then (Int64.unsigned (Int64.and (Int.repr z1) (Int64.repr z2))) else
    (Int.unsigned (Int.and (Int.repr z1) (Int.repr z2))). *)

Theorem case_of_labeled_stm_boxed:
  forall rep_env n arr t  h e p fenv finfo_env ienv cenv ,
    correct_ienv_of_cenv cenv ienv ->
     M.get t rep_env = Some (boxed n arr)  ->
    correct_crep_of_env cenv rep_env ->
    boxed_header n arr  h ->
    forall cl ls ls',
      caseConsistent cenv cl t ->
  findtag cl t = Some e ->
  repr_branches_LambdaANF_Codegen argsIdent allocIdent limitIdent threadInfIdent tinfIdent isptrIdent caseIdent nParam fenv finfo_env p rep_env cl ls ls' ->
  exists s s',
                       (seq_of_labeled_statement (select_switch (Z.land  h 255) ls)) = (Ssequence (Ssequence s Sbreak) s') /\  repr_expr_LambdaANF_Codegen_id fenv finfo_env p rep_env e s.
Proof.
  intros rep_env n arr t  h e p fenv finfo_env ienv cenv  Hienv H H0 H1.
  induction cl; intros ls ls' Hcc; intros.
  (* impossible empty cl *) inv H2.
  simpl in H2. destruct a. destruct (M.elt_eq c t).
  - (* is case *)
    inv H2. inv H3. rewrite H9 in H; inv H.
    rewrite H10 in H; inv H.
    + (* default *)
      simpl. exists s, Sskip.
      split; auto.
    + rewrite H10 in H. inv H.
      assert (tag = h). {
        inv H1; inv H11. auto.
      }
      rewrite <- H in *. clear H. clear H11.
      unfold select_switch. simpl.
      rewrite Coqlib.zeq_true. simpl.
      do 2 eexists.
      split. reflexivity. auto.
  - (* is-not-case -- IH *)
    inv H3.
    + (* enum default *)
      inv Hcc; eapply IHcl; eauto.
    + inv Hcc; eapply IHcl; eauto.
    + exfalso.
      eapply repr_branches_LSnil_no_boxed; eauto.
    + (* c <> t so arr <> n1 and the header are different *)
      unfold select_switch.
      simpl select_switch_case.
      rewrite Coqlib.zeq_false.
      inv Hcc.
      specialize (IHcl _ _ H14 H2 H7). apply IHcl.
      do 2 (erewrite  repr_boxed_t; eauto).


      inv H0. apply H4 in H11.
      apply H4 in H. inv H. inv H11.
      inv Hcc.

      rewrite H6 in H11. inv H11. rewrite H5 in H16. inv H16.
      simpl in H18. inv H18.

      assert (Hdj := disjoint_ord Hienv H5 H6).
      apply Hdj in n0. intro. apply n0.
      apply N2Z.inj. auto.
Qed.

(* CHANGE HERE *)

Lemma skipn_suc1  {A} n (x : A) (l1 l2 : list A) : skipn n l1 = x :: l2 -> skipn (S n) l1 = l2.
Proof.
  generalize n l2. induction l1; destruct n0; intros.
  - simpl in H. rewrite H; reflexivity.
  - inv H.
  - inv H. reflexivity.
  - apply (IHl1 n0 l0 H).
Qed.

Lemma skipn_suc2 {A} n (x y : A) (l1 l2 : list A) : skipn n (x :: l1) = y :: l2 -> skipn n l1 = l2.
Proof.
  generalize x y n l2. induction l1; destruct n0; intros; inv H; try reflexivity.
  - destruct n0; inv H1.
  - apply (IHl1 _ _ _ _ H1).
Qed.

Lemma skipn_cons {A} n (x y : A) (l1 l2 : list A) : skipn n (x :: l1) = (y :: l2) -> skipn n l1 = l2.
Proof.
  induction l2 , l1; intros.
  - destruct n; reflexivity.
  - destruct n; inv H.
    destruct n; intros.
    + inv H1. reflexivity.
    + inv H1. apply (skipn_suc1 n y l1 []). assumption.
  - apply (skipn_suc1 n y [x] (a :: l2)). assumption.
  - apply (skipn_suc2 _ x y). assumption.
Qed.

Lemma skipn_cons_nil {A} n (x : A) (l : list A) : skipn n (x :: l) = [] -> skipn n l = [].
Proof.
  generalize n x. induction l; intros.
  - destruct n0; reflexivity.
  - destruct n0.
    + inv H.
    + simpl in H. simpl.  apply (IHl n0 a). assumption.
Qed.

(* place values lenv(ys) into the inf slots of the args array
   something about allocPtr *)
Definition mem_of_asgn argsIdent p lenv (ys:list positive) (inf:list N) m :=
  exists args_b args_ofs, M.get argsIdent lenv = Some (Vptr args_b args_ofs)  /\ Forall2 (fun y i => exists v, Mem.loadv int_chunk m (Vptr args_b (Ptrofs.add args_ofs (Ptrofs.repr (int_size * (Z.of_N i))))) = Some v /\ get_var_or_funvar p lenv y v) ys inf.

(* same as above but with val list explicit *)
Inductive mem_of_asgn_v args_b args_ofs p lenv m: list positive -> list N -> list Values.val -> Prop :=
| moa_cons: forall y i v ys inf vs,
    mem_of_asgn_v args_b args_ofs p lenv m ys inf vs ->
    Mem.loadv int_chunk m (Vptr args_b (Ptrofs.add args_ofs (Ptrofs.repr (int_size * (Z.of_N i))))) = Some v ->
    get_var_or_funvar p lenv y v ->
     mem_of_asgn_v args_b args_ofs p lenv m (y::ys) (i::inf) (v::vs)
| moa_nil:
    mem_of_asgn_v args_b args_ofs p lenv m [] [] [].

(* same as above, but without lenv and ys
   i.e. disregarding provenance *)
Inductive mem_after_asgn args_b args_ofs  m: list N -> list Values.val -> Prop :=
  | maa_cons: forall  i v  inf vs,
    mem_after_asgn args_b args_ofs  m inf vs ->
    Mem.loadv int_chunk m (Vptr args_b (Ptrofs.add args_ofs (Ptrofs.repr (int_size * (Z.of_N i))))) = Some v ->
     mem_after_asgn args_b args_ofs  m (i::inf) (v::vs)
| maa_nil:
    mem_after_asgn args_b args_ofs  m [] [].



Theorem mem_of_asgn_nthN:
  forall {args_b args_ofs p lenv m ys inf vs y v n},
  mem_of_asgn_v args_b args_ofs p lenv m ys inf vs  ->
  nthN ys n = Some y ->
  nthN vs n = Some v ->
  get_var_or_funvar p lenv y v.
Proof.
  induction ys; intros.
  inv H0.
  destruct vs. inv H1.
  inv H.
  destruct n. inv H0; inv H1; auto.
  apply nthN_pos_pred in H0.
  apply nthN_pos_pred in H1.
  eapply IHys; eauto.
Qed.

Theorem mem_of_asgn_after:
  forall args_b args_ofs p m lenv inf ys vs,
  mem_of_asgn_v args_b args_ofs p lenv m ys inf vs ->
  mem_after_asgn args_b args_ofs m inf vs.
Proof.
  induction inf; intros.
  - inv H; constructor.
  - inv H; constructor; eauto.
Qed.

Theorem mem_after_asgn_length:
  forall args_b args_ofs m  inf vs,
  mem_after_asgn args_b args_ofs m inf vs ->
  length inf = length vs.
Proof.
  induction inf; intros.
  inv H; auto.
  inv H. simpl. erewrite IHinf; eauto.
Qed.

Theorem mem_of_asgn_exists_v:
  forall {argsIdent p lenv m args_b args_ofs ys inf},
  mem_of_asgn argsIdent p lenv ys inf m ->
  M.get argsIdent lenv = Some (Vptr args_b args_ofs) ->
  exists vs,
    mem_of_asgn_v args_b args_ofs p lenv m ys inf vs.
Proof.
  intros. inv H. destruct H1. destruct H.
  rewrite H in H0. inv H0.
  clear H. revert dependent inf. induction ys; intros.
  -  inv H1.
     exists []. constructor.
  - inv H1. specialize (IHys _ H4).
    inv IHys. inv H2.
    exists (x0::x). destruct H0. constructor; eauto.
Qed.


Theorem mem_of_asgn_forall_v:
  forall {argsIdent p lenv m args_b args_ofs ys inf vs},
  mem_of_asgn_v args_b args_ofs p lenv m ys inf vs ->
  M.get argsIdent lenv = Some (Vptr args_b args_ofs) ->
  mem_of_asgn argsIdent p lenv ys inf m.
Proof.
  induction ys; intros.
  - inv H. eexists. eexists. split; eauto.
  - inv H. specialize (IHys _ _ H3 H0).
    exists args_b, args_ofs. split; auto. constructor.
    exists v; eauto.
    inv IHys. destructAll. rewrite H in H0. inv H0.
    auto.
Qed.


Theorem mem_of_asgn_v_length:
  forall {p lenv m args_b args_ofs ys inf vs},
    mem_of_asgn_v args_b args_ofs p lenv m ys inf vs ->
    length inf = length vs.
Proof.
  induction ys; intros; inv H.
  reflexivity.
  simpl. erewrite IHys. reflexivity.
  eauto.
Qed.

Theorem mem_of_asgn_v_length13:
  forall {p lenv m args_b args_ofs ys inf vs},
    mem_of_asgn_v args_b args_ofs p lenv m ys inf vs ->
    length ys = length vs.
Proof.
  induction ys; intros; inv H.
  reflexivity.
  simpl. erewrite IHys. reflexivity.
  eauto.
Qed.




Theorem mem_of_asgn_v_disjoint:
  forall a v lenv args_b args_ofs p ys vs inf m,
    ~ List.In a ys ->
    mem_of_asgn_v args_b args_ofs p lenv m ys inf vs ->
    mem_of_asgn_v args_b args_ofs p (Maps.PTree.set a v lenv) m ys inf vs.
Proof.
  induction ys; intros.
  - inv H0. constructor.
  - inv H0. constructor. apply IHys. intro; apply H. constructor 2; auto.
    auto. auto. inv H7.
    + constructor. auto.
    + constructor 2; auto.
      rewrite M.gso. auto. intro; apply H. subst.
      constructor. auto.
Qed.

Theorem mem_of_asgn_v_store:
  forall args_b args_ofs p v chunk b ofs lenv m m' ys inf vs,
  mem_of_asgn_v args_b args_ofs p lenv m ys inf vs ->
  Mem.store chunk m b ofs v  = Some m' ->
  b <> args_b ->
  mem_of_asgn_v args_b args_ofs p lenv m' ys inf vs.
Proof.
  induction ys; intros.
  - inv H.
    constructor.
  - inv H.
    constructor; auto.
    unfold Mem.loadv in *.
    erewrite Mem.load_store_other; eauto.
Qed.

Ltac solve_ptrofs_range:=
  solve_uint_range; uint_range_ptrofs; chunk_red; archi_red; unfold Int64.max_unsigned; unfold Int.max_unsigned; simpl; try omega.

(* w/o destructing ptr64 *)
Ltac solve_ptrofs_range':=
  solve_uint_range; uint_range_ptrofs; archi_red; unfold Int64.max_unsigned; unfold Int.max_unsigned; simpl; try omega.


Definition mem_of_asgn_cons:
  forall p y lenv ys inf m i max_alloc m' v args_ofs args_b,
  mem_of_asgn argsIdent p lenv ys inf m ->
  NoDup (i::inf) ->
  Forall (fun i => 0 <= (Z.of_N i) < max_args)%Z (i::inf) ->
  (0 <= Ptrofs.unsigned args_ofs + int_size * max_args  <= Ptrofs.max_unsigned )%Z ->
  correct_tinfo p max_alloc lenv m ->
  M.get argsIdent lenv = Some (Vptr args_b args_ofs) ->

  get_var_or_funvar p lenv y v ->


  Mem.storev int_chunk m (Vptr args_b (Ptrofs.add args_ofs (Ptrofs.repr (int_size * (Z.of_N i))))) v = Some m' ->
  mem_of_asgn argsIdent p lenv (y::ys) (i::inf) m'.
Proof.
   intros.
  destruct H3 as [alloc_b [alloc_ofs [limit_ofs [args_b' [args_ofs' [tinf_b [tinf_ofs [Hget_alloc [Halign_alloc [Hrange_alloc [Hget_limit [Hbound_limit [Hget_args [Hdj_args [Hbound_args [Hrange_args [Htinf1 Htinf2]]]]]]]]]]]]]]]]].
  rewrite Hget_args in H4. inv H4.
  destruct H as [args_b' [args_ofs' [H3]]]. rewrite H3 in Hget_args.  inv Hget_args.
  exists args_b, args_ofs.
  split; auto.
  constructor.
  - exists v. split; auto.
    simpl in *. erewrite Mem.load_store_same; eauto.
    simpl.  destruct v; inv H5; inv H8; auto.
  - eapply Forall2_monotonic_strong; eauto.
    intros. cbv beta in *.
    destruct H8. exists x.
    destruct H8. split; auto.
    unfold Mem.loadv in *.
    erewrite Mem.load_store_other; eauto.
    right.  inv H0.
    assert (i <> x2).
    intro. apply H12. subst; auto.
    inv H1.
    eapply Forall_forall in H15; eauto.
    assert ( uint_range_l [int_size; Z.of_N i] ) by  (unfold max_args in *; solve_ptrofs_range).
    assert ( uint_range_l [int_size; Z.of_N x2] ) by (unfold int_size in *; unfold max_args in *; solve_ptrofs_range).
    assert (Hix2 := N.le_gt_cases x2 i).
    inv Hix2.
    + left.
      assert (x2 < i)%N.
      apply N.le_neq. split; auto.
      clear H11.
      rewrite Ptrofs.add_unsigned.
      rewrite Ptrofs.add_unsigned.
      repeat (rewrite Ptrofs.unsigned_repr_eq).
      rewrite Zdiv.Zplus_mod_idemp_r.
      rewrite Zdiv.Zplus_mod_idemp_r.

      destruct H2.  apply Z.lt_le_pred in H11.
      rewrite Z.mod_small.
      rewrite Z.mod_small.
      assert (Z.of_N x2 + 1 <=  Z.of_N i)%Z.
      apply Zlt_le_succ.        apply N2Z.inj_lt. auto.
      rewrite <- Z.add_assoc.
      replace (Z.add (Z.mul int_size (Z.of_N x2)) (size_chunk int_chunk)) with (int_size * (Z.of_N x2 + 1))%Z by (chunk_red; omega).


      chunk_red; uomega.
      split. apply OrdersEx.Z_as_OT.add_nonneg_nonneg. apply Ptrofs.unsigned_range. chunk_red; uomega.
      eapply OrdersEx.Z_as_OT.le_lt_trans; eauto. chunk_red; uomega.
      split. apply OrdersEx.Z_as_OT.add_nonneg_nonneg. apply Ptrofs.unsigned_range. chunk_red; uomega.
      eapply OrdersEx.Z_as_OT.le_lt_trans; eauto. chunk_red; uomega.
    + right.
      rewrite Ptrofs.add_unsigned.
       rewrite Ptrofs.add_unsigned.
       repeat (rewrite Ptrofs.unsigned_repr_eq).
       rewrite Zdiv.Zplus_mod_idemp_r.
       rewrite Zdiv.Zplus_mod_idemp_r.

       destruct H2.
       unfold Ptrofs.max_unsigned in *. apply Z.lt_le_pred in H16.
       rewrite Z.mod_small.
       rewrite Z.mod_small.
       assert (Z.of_N i + 1 <=  Z.of_N x2)%Z.
       apply Zlt_le_succ.        apply N2Z.inj_lt. auto.
       replace (int_size*Z.of_N i + int_size)%Z with (int_size * (Z.of_N i + 1))%Z  by (chunk_red; uomega).
       chunk_red; uomega.
       split. apply OrdersEx.Z_as_OT.add_nonneg_nonneg. apply Ptrofs.unsigned_range. chunk_red; uomega.
       eapply OrdersEx.Z_as_OT.le_lt_trans; eauto. chunk_red; uomega.
       split. apply OrdersEx.Z_as_OT.add_nonneg_nonneg. apply Ptrofs.unsigned_range. chunk_red; uomega.
       eapply OrdersEx.Z_as_OT.le_lt_trans; eauto. chunk_red; uomega.
Qed.

(* What is needed at function entry to unmarshal the parameters *)
Theorem repr_asgn_fun_entry:
  forall args_b args_ofs argsIdent F p m k xs locs vs7 asgn lenv lenv',
    M.get argsIdent lenv = Some (Vptr args_b args_ofs) ->
    mem_after_asgn args_b args_ofs m (skipn nParam locs) (skipn nParam vs7) ->
    right_param_asgn argsIdent (skipn nParam xs) (skipn nParam locs) asgn ->
    lenv_param_asgn_i lenv lenv' (skipn nParam xs) (skipn nParam vs7) ->
    NoDup xs ->
    ~ List.In argsIdent xs ->
    Forall (fun i : N => (0 <= Z.of_N i < max_args)%Z) locs ->
    clos_refl_trans state (traceless_step2 (globalenv p))
               (State F asgn k empty_env lenv m)
               (State F Sskip k empty_env lenv' m).
Proof. Admitted. (*
  induction xs; intros.
  - (* base case *)
    inv H1; inv H2; inv H0.
    apply rt_refl.
  - (* Inductive case *)
    inv H1; inv H2; inv H3; inv H0.
    inv H5.

    eapply rt_trans. constructor. constructor.
    (* BRANCH ptr64*)
    chunk_red;  archi_red.
    {
    eapply rt_trans. constructor. constructor. econstructor. constructor. econstructor. constructor. eauto.
    constructor. constructor.
    ptrofs_of_int. int_unsigned_repr.
    rewrite int_z_mul. econstructor. reflexivity. eauto.
    unfold max_args in *.  solve_ptrofs_range'. unfold max_args in *.  solve_uint_range. omega.
    eapply rt_trans. constructor. constructor.
    eapply IHxs; eauto.  rewrite M.gso. auto. intro; apply H4; constructor; auto.
    intro. apply H4. constructor 2; auto.    }
    {
    eapply rt_trans. constructor. constructor. econstructor. constructor. econstructor. constructor. eauto.
    constructor. constructor.
    ptrofs_of_int. rewrite Int.unsigned_repr.
    rewrite int_z_mul. econstructor. reflexivity. eauto.
    unfold max_args in *.  solve_ptrofs_range'. unfold max_args in *.  solve_uint_range. omega.
    eapply rt_trans. constructor. constructor.

    eapply IHxs; eauto.  rewrite M.gso. auto. intro; apply H4; constructor; auto.
    intro. apply H4. constructor 2; auto. }
Qed. *)

(* CHANGE THIS *)
(* after stepping through a repr_asgn_fun', argsIdent[i] contain valuees y_i *)
(* rest of m is the same *)
(* maybe also have that L stays the same between the two *)
(* also wants NoDup on i *)
Theorem repr_asgn_fun_mem:
  forall fu lenv p rho e fenv max_alloc rep_env finfo_env,
  forall ys inf s m,
    find_symbol_domain p finfo_env ->
    finfo_env_correct fenv finfo_env ->
 rel_mem_LambdaANF_Codegen_id fenv finfo_env p rep_env e rho m lenv ->
 correct_tinfo p max_alloc lenv m ->
 Forall (fun x => exists v, get_var_or_funvar p lenv x v) ys ->
 Forall (fun i => 0 <= (Z.of_N i) < max_args)%Z inf ->
 NoDup inf ->
 repr_asgn_fun' argsIdent threadInfIdent nParam fenv finfo_env p ys inf s ->
 exists m',
  (forall k, clos_refl_trans state (traceless_step2 (globalenv p))
    (State fu s k empty_env lenv m)
    (State fu Sskip k empty_env lenv m')) /\ mem_of_asgn argsIdent p lenv ys inf m' /\rel_mem_LambdaANF_Codegen_id fenv finfo_env p rep_env e  rho m' lenv /\ correct_tinfo p max_alloc lenv m'.
Proof.
  intros fu lenv p rho e fenv max_alloc rep_env finfo_env.
  induction ys; intros inf s m Hsym HfinfoCorrect Hrel_mem Htinfo Hfys Hfinf Hnodub Hasgn; inv Hasgn.
  - (* ys = [] inf = [] *)
    assert (Htinfo' := Htinfo).
    destruct Htinfo as [alloc_b [alloc_ofs [limit_ofs [args_b [args_ofs [tinf_b [tinf_ofs [Hget_alloc [Halign_alloc [Hrange_alloc [Hget_limit [Hbound_limit [Hget_args [Hdj_args [Hbound_args [Hrange_args [Htinf1 Htinf2]]]]]]]]]]]]]]]]].
    (* cam have empty asgn now *)
    exists m.
    repeat split; try assumption.
    + intros. constructor 2.
    + econstructor. eauto.

  -  (* ys = a::ys0 inf = i::inf0 *)
    (* repeat of the init case *)
    assert (Hfinf' := Hfinf).
    inv Hfys; inv Hfinf. destruct H1.
    assert (Hnodub' := Hnodub). inv Hnodub.
    specialize (IHys inf0 s0 m Hsym HfinfoCorrect Hrel_mem Htinfo H2 H5 H7 H3).
    destruct IHys as [m' [Hclo_m' [Hmem_m' [Hrel_m' Htinfo_m']]]].
    assert (Htinfo_m'c := Htinfo_m').
    destruct Htinfo_m' as [alloc_b [alloc_ofs [limit_ofs [args_b [args_ofs [tinf_b [tinf_ofs [Hget_alloc [Halign_alloc [Hrange_alloc [Hget_limit [Hbound_limit [Hget_args [Hdj_args [Hbound_args [Hrange_args [Htinf1 Htinf2]]]]]]]]]]]]]]]]].
    assert (Hm'_valid : Mem.valid_access m' int_chunk args_b (Ptrofs.unsigned
                                                               (Ptrofs.add args_ofs
                                                                        (Ptrofs.mul (Ptrofs.repr int_size) (Ptrofs.repr (Z.of_N i))))) Writable).
    apply Hrange_args. auto.
    assert (Hm' := Mem.valid_access_store _ _ _ _ x Hm'_valid).
    destruct Hm' as [m2 Hm2].
    exists m2.

    (* apply mem_of_asgn_cons *)
    assert (Hm2' := Hm2).
    rewrite int_z_mul in Hm2'.

    assert (Hargs_bound :   (0 <= Ptrofs.unsigned args_ofs + int_size * max_args <= Ptrofs.max_unsigned)%Z). split.
    apply OrdersEx.Z_as_OT.add_nonneg_nonneg. apply Ptrofs.unsigned_range. chunk_red; uomega.
    auto.
    assert (Hmem_of_asgn := mem_of_asgn_cons _ _ _ _ _ _ _ _ _ _ _ _ Hmem_m' Hnodub' Hfinf' Hargs_bound Htinfo_m'c Hget_args H Hm2').

    split.

    (* step though cons and then asgn *)
      intro.
      eapply rt_trans.
      constructor. constructor.
      eapply rt_trans.
      apply Hclo_m'.
      (* branch ptr64 *)
      chunk_red; archi_red.
      {
        eapply rt_trans. constructor. constructor.
        constructor. econstructor. constructor. econstructor. constructor. eauto.
        constructor. simpl. constructor.
        eapply get_var_or_funvar_eval; eauto.
        eapply get_var_or_funvar_semcast; eauto.
        simpl. eapply assign_loc_value. constructor. auto.
        ptrofs_of_int. int_unsigned_repr. auto.
        unfold max_args in *.  solve_uint_range. omega.
      }
      {
        eapply rt_trans. constructor. constructor.
        constructor. econstructor. constructor. econstructor. constructor. eauto.
        constructor. simpl. constructor.
        eapply get_var_or_funvar_eval; eauto.

        eapply get_var_or_funvar_semcast in H; archi_red; eauto.
        simpl. eapply assign_loc_value. constructor.
        ptrofs_of_int. int_unsigned_repr. auto.
        unfold max_args in *.  solve_uint_range. omega.
      }

    split; auto.
    split.
    eapply rel_mem_update_protected with (m := m'); eauto.


    eapply correct_tinfo_valid_access; eauto.
    eapply mem_range_valid. intros.
    eapply Mem.store_valid_access_1; eauto.
    unfold max_args in *; solve_ptrofs_range.
Qed.




Definition program_isPtr_inv (p:program) :=
  exists b_isPtr name sg, Genv.find_symbol (globalenv p) isptrIdent = Some b_isPtr /\
                          Genv.find_funct (globalenv p) (Vptr  b_isPtr Ptrofs.zero) = Some (External (EF_external name sg) (Tcons val Tnil)  (Tint IBool Unsigned noattr)   {| cc_vararg := false; cc_unproto := false; cc_structret := false |}) /\
                                  (forall m n, Events.external_functions_sem name sg (Genv.globalenv p) [make_vint n] m [] Vfalse m) /\
                                  (forall m b i, Events.external_functions_sem name sg (Genv.globalenv p) [Vptr b i] m [] Vtrue m).


 (*  deprecated version
the lenv should actually be post asgn

 e_lenv_param_asgn_i  vsm4 lenv_new' vs7 Hl_temp Hnd_vs0
where lenv_new' = (M.set limitIdent (Vptr alloc_b limit_ofs) (M.set allocIdent (Vptr alloc_b alloc_ofs) lenv_new))
Definition program_gc_inv (p:program) :=
  exists b_gcPtr name sg, Genv.find_symbol (globalenv p) gcIdent = Some b_gcPtr /\
                          Genv.find_funct (globalenv p) (Vptr  b_gcPtr Int.zero) = Some (External (EF_external name sg) (Tcons (Tpointer (Tint I32 Unsigned noattr) noattr) (Tcons (Tpointer (Tstruct threadInfIdent noattr) noattr) Tnil)) Tvoid
                            {|
                              cc_vararg := false;
                              cc_unproto := false;
                              cc_structret := false |}) /\
                          forall lenv m rho rep_env finfo_env finfo_b finfo_maxalloc fenv e tinf_b tinf_ofs args_b args_ofs,
                            rel_mem_LambdaANF_Codegen_id fenv finfo_env p rep_env e rho m lenv ->
                            M.get tinfIdent lenv = Some (Vptr tinf_b tinf_ofs) ->
                            Mem.loadv int_chunk m (Vptr finfo_b Int.zero) = Some (Vint finfo_maxalloc) ->
                            deref_loc valPtr m tinf_b (Int.add tinf_ofs (Int.repr (3*int_size))) (Vptr args_b args_ofs) ->
                          exists v m' alloc_b alloc_ofs limit_ofs,
                            (Events.external_functions_sem name sg (Genv.globalenv p) [Vptr finfo_b Int.zero; Vptr tinf_b tinf_ofs] m [] v m') /\
                            (* get new alloc *)
                            deref_loc valPtr m' tinf_b tinf_ofs (Vptr alloc_b alloc_ofs) /\
                             (* get new limit *)
                            deref_loc valPtr m' tinf_b (Int.add tinf_ofs (Int.repr int_size)) (Vptr alloc_b limit_ofs)  /\
                            (* same args block and offset *)
                            deref_loc valPtr m' tinf_b (Int.add tinf_ofs (Int.repr (3*int_size))) (Vptr args_b args_ofs)  /\
                            (* same thing in the args block *)
                             mem_same_block args_b m m' /\
                             (forall lenv' : temp_env,
                                 forall vsm4 vs7 vars,
   lenv_param_asgn
     (M.set argsIdent (Vptr args_b args_ofs)
        (M.set limitIdent (Vptr alloc_b limit_ofs)
           (M.set allocIdent (Vptr alloc_b alloc_ofs)
                 (Maps.PTree.set tinfIdent (Vptr tinf_b tinf_ofs)
                    (create_undef_temps
                       vars)))))
     lenv' vsm4 vs7 ->
   rel_mem_LambdaANF_Codegen_id fenv finfo_env p rep_env e rho m' lenv' /\
   correct_tinfo p (Int.unsigned finfo_maxalloc) lenv' m'). *)

(* deep version of mem_after_asgn  *)
 Inductive rel_mem_asgn {fenv finfo_env p rep_env} args_b args_ofs m L: list LambdaANF.term.val -> list N -> list Values.val -> Prop :=
  | rma_cons: forall  i v6 v7  vs6 inf vs7,
    rel_mem_asgn args_b args_ofs  m L vs6 inf vs7 ->
    Mem.loadv int_chunk m (Vptr args_b (Ptrofs.add args_ofs (Ptrofs.repr (int_size * (Z.of_N i))))) = Some v7 ->
    repr_val_L_LambdaANF_Codegen_id fenv finfo_env p rep_env v6 m L v7 ->
     rel_mem_asgn args_b args_ofs  m L (v6::vs6) (i::inf) (v7::vs7)
| rma_nil:
    rel_mem_asgn args_b args_ofs  m L [] [] [].

 Theorem rel_mem_asgn_length:
   forall {fenv finfo_env p rep_env m L args_b args_ofs ys inf vs},
     @rel_mem_asgn fenv finfo_env p rep_env args_b args_ofs m L ys inf vs ->
    length ys = length vs.
 Proof.
   induction ys; intros.
   inv H; auto.
   inv H. simpl. erewrite IHys. reflexivity.
   eauto.
 Qed.


 Theorem rel_mem_asgn_nthN:
  forall {L rep_env finfo_env fenv args_b args_ofs p  m vs6 inf vs7 v6 v7 n},
  @rel_mem_asgn fenv finfo_env p rep_env args_b args_ofs  m L vs6 inf vs7 ->
  nthN vs6 n = Some v6 ->
  nthN vs7 n = Some v7 ->
  repr_val_L_LambdaANF_Codegen_id fenv finfo_env p rep_env v6 m L v7.
Proof.
  induction vs6; intros.
  inv H0.
  destruct vs7. inv H1.
  inv H.
  destruct n. inv H0; inv H1; auto.
  apply nthN_pos_pred in H0.
  apply nthN_pos_pred in H1.
  eapply IHvs6; eauto.
Qed.


 Theorem cons_get_list: forall {A y ys rho vs},
   @get_list A (y::ys) rho = Some vs ->
   exists v vs',
     v::vs' = vs /\ M.get y rho = Some v /\ @get_list A ys rho = Some vs'.
 Proof.
   intros. simpl in H. destruct (M.get y rho) eqn:Hgy; destruct (get_list ys rho) eqn:Hgys.
   exists a, l. split. inv H; auto. split; reflexivity.
   inv H. inv H. inv H.
 Qed.


 Theorem rel_mem_after_asgn:
   forall fenv finfo_env p rep_env args_b args_ofs m L vs6 locs vs7,
   @rel_mem_asgn fenv finfo_env p rep_env args_b args_ofs  m L vs6 locs vs7 ->
     mem_after_asgn args_b args_ofs m locs vs7.
 Proof.
   induction vs6; intros.
   - inv H.
     constructor.
   - inv H.
     constructor; eauto.
 Qed.

Theorem rel_mem_of_asgn: forall fenv finfo_env  rep_env args_b args_ofs p lenv m rho L ys inf vs7 vs6,
 mem_of_asgn_v args_b args_ofs p lenv m ys inf vs7 ->
 get_list ys rho = Some vs6 ->
 (forall x, List.In x ys ->
            exists v6, M.get x rho = Some v6 /\
                       repr_val_id_L_LambdaANF_Codegen_id fenv finfo_env p rep_env v6 m L lenv x) ->
 @rel_mem_asgn fenv finfo_env p rep_env args_b args_ofs m L vs6 inf vs7.
Proof.
  induction ys; intros.
  -   inv H0; inv H. constructor.
  - apply cons_get_list in H0. destruct H0 as [v [vs' [Heqvs [Hgar Hgysr]]]]. subst.
    inv H. constructor.
    eapply IHys; eauto. intros. eapply H1. constructor 2; auto.
    eauto.
    assert (Hli: List.In a (a :: ys)) by (constructor; reflexivity).
    apply H1 in Hli. destruct Hli. destruct H. inv H7; inv H0.
    rewrite H2 in H5. inv H5. rewrite H in Hgar. inv Hgar. auto.
    rewrite H2 in H5; inv H5. rewrite H2 in H7; inv H7.
    rewrite H5 in H8; inv H8. rewrite H in Hgar. inv Hgar. auto.
Qed.

(* invariant for GC, needs to be shown to be provable from GC proof *)
(* OS: Changed returned vs7 into vs7' s.t. the pointers can have changed (but represent the same values in LambdaANF) *)
 Definition program_gc_inv (p:program) :=
  exists b_gcPtr name sg, Genv.find_symbol (globalenv p) gcIdent = Some b_gcPtr /\
                          Genv.find_funct (globalenv p) (Vptr  b_gcPtr Ptrofs.zero) = Some (External (EF_external name sg) (Tcons (Tpointer val noattr) (Tcons (Tpointer (Tstruct threadInfIdent noattr) noattr) Tnil)) Tvoid
                            {|
                              cc_vararg := false;
                              cc_unproto := false;
                              cc_structret := false |}) /\
                          forall lenv m finfo_b finfo_env (p:program) rep_env finfo_maxalloc fenv tinf_b tinf_ofs args_b args_ofs L vs6 vs7 inf,
                            @rel_mem_asgn fenv finfo_env p rep_env args_b args_ofs m L vs6 inf vs7 ->
                            M.get tinfIdent lenv = Some (Vptr tinf_b tinf_ofs) ->
                            Mem.loadv int_chunk m (Vptr finfo_b Ptrofs.zero) = Some (make_vint finfo_maxalloc) ->
                            (int_size * finfo_maxalloc <= gc_size)%Z ->
                            deref_loc (Tarray uval maxArgs noattr) m tinf_b (Ptrofs.add tinf_ofs (Ptrofs.repr (3*int_size))) (Vptr args_b args_ofs) ->
                          exists v m' alloc_b alloc_ofs limit_ofs L' vs7',
                            (Events.external_functions_sem name sg (Genv.globalenv p) [Vptr finfo_b Ptrofs.zero; Vptr tinf_b tinf_ofs] m [] v m') /\
                            (* get new alloc *)
                            deref_loc valPtr m' tinf_b tinf_ofs (Vptr alloc_b alloc_ofs) /\
                             (* get new limit *)
                            deref_loc valPtr m' tinf_b (Ptrofs.add tinf_ofs (Ptrofs.repr int_size)) (Vptr alloc_b limit_ofs)  /\
                            (* same args block and offset *)
                            deref_loc (Tarray uval maxArgs noattr) m' tinf_b (Ptrofs.add tinf_ofs (Ptrofs.repr (3*int_size))) (Vptr args_b args_ofs)  /\
                            (* deep copied arguments *)
                            @rel_mem_asgn fenv finfo_env p rep_env args_b args_ofs m' L' vs6 inf vs7' /\
                            Mem.unchanged_on (fun b z => and (~(L b z)) (and (~ (L' b z)) (b <> tinf_b))) m m' /\
                            (* SEP :- this is just L' disjoint from m \ L + tinfo AND tinfo [args, alloc_b] is disjoint from global *)
                            protected_not_in_L_id p  (M.set argsIdent (Vptr args_b args_ofs) (M.set limitIdent (Vptr alloc_b limit_ofs)
               (M.set allocIdent (Vptr alloc_b alloc_ofs)
                      (Maps.PTree.set tinfIdent (Vptr tinf_b tinf_ofs) (M.empty _))))) L' /\
                            (* Some SEP, some GC :- enough space in nursey, aligned pointers, enough space in args *)
                            correct_tinfo p finfo_maxalloc (M.set argsIdent (Vptr args_b args_ofs)
            (M.set limitIdent (Vptr alloc_b limit_ofs)
               (M.set allocIdent (Vptr alloc_b alloc_ofs)
                     (Maps.PTree.set tinfIdent (Vptr tinf_b tinf_ofs) (M.empty _)))))  m'.




 (* Working towards a clearer interface with the gc


About meminj.
About Mem.mem_inj.
   sep1) inject f m m'
       if not L or tinfo, then f = x -> Some (x, 0)

   gc1) deep roots are copied to L' (in m')
   sep2)
       If y in L', then either in L or did not exists in m, i.e. there doesn't exists an x, f x = y

   gc2) limit - alloc > tinfo.max_alloc

as injection, this looks like:




  *)




(* find the right co for threadInf *)


Definition program_threadinfo_inv (p:program) :=
  exists co,
    Maps.PTree.get threadInfIdent (genv_cenv (globalenv p))= Some co /\
    co_members co =  ((allocIdent, valPtr) ::
                         (limitIdent, valPtr) :: (heapInfIdent, (Clightdefs.tptr (Tstruct heapInfIdent noattr))) ::
                         (argsIdent, (Tarray val maxArgs noattr))::nil).

Theorem allocIdent_delta:
  forall p,
      field_offset p allocIdent
    [(allocIdent, valPtr); (limitIdent, valPtr); (heapInfIdent, Clightdefs.tptr (Tstruct heapInfIdent noattr));
       (argsIdent, Tarray uval maxArgs noattr)] = OK (0)%Z.
Proof.
   intro. chunk_red; archi_red; simpl; unfold field_offset; simpl;
  assert (Hnd := disjointIdent);
  inv Hnd; rewrite Coqlib.peq_true;
  reflexivity.
Qed.


Theorem limitIdent_delta:
  forall p,
      field_offset p limitIdent
    [(allocIdent, valPtr); (limitIdent, valPtr); (heapInfIdent, Clightdefs.tptr (Tstruct heapInfIdent noattr));
       (argsIdent, Tarray uval maxArgs noattr)] = OK (1*int_size)%Z.
Proof.
   intro. chunk_red; archi_red; simpl; unfold field_offset; simpl;
  assert (Hnd := disjointIdent);
  inv Hnd.

  rewrite Coqlib.peq_false.
  rewrite Coqlib.peq_true.
  reflexivity.
  inv H2.
  intro; subst; apply H3; inList.

  rewrite Coqlib.peq_false.
  rewrite Coqlib.peq_true.
  archi_red. simpl. reflexivity.
  inv H2.
  intro; subst; apply H3; inList.
Qed.

Theorem argsIdent_delta:
  forall p,
  field_offset p argsIdent
    [(allocIdent, valPtr); (limitIdent, valPtr);
    (heapInfIdent, Clightdefs.tptr (Tstruct heapInfIdent noattr));
    (argsIdent, Tarray uval maxArgs noattr)] = OK (3*int_size)%Z.
Proof.
  intro. chunk_red; archi_red; simpl; unfold field_offset; simpl;
  assert (Hnd := disjointIdent);
  inv Hnd.

  rewrite Coqlib.peq_false.
  rewrite Coqlib.peq_false.
  rewrite Coqlib.peq_false.
  rewrite Coqlib.peq_true.
  reflexivity.
  intro; subst; apply H1; inList.
  intro; subst; apply H1; inList.
  intro; subst; apply H1; inList.

  rewrite Coqlib.peq_false.
  rewrite Coqlib.peq_false.
  rewrite Coqlib.peq_false.
  rewrite Coqlib.peq_true.
  archi_red. simpl. reflexivity.
  intro; subst; apply H1; inList.
  intro; subst; apply H1; inList.
  intro; subst; apply H1; inList.
Qed.

(*
Theorem direct_assignConstructor:
  forall cenv ienv map v c l,
    assignConstructor allocIdent threadInfIdent cenv ienv map v c l =
    assignConstructorS allocIdent threadInfIdent cenv ienv map v c l.
Proof.
  intros. unfold assignConstructor.
  unfold assignConstructorS.
  destruct (makeTag cenv c) eqn:H_makeTag.
  destruct (make_ctor_rep cenv c) eqn:H_make_ctor_rep.
  simpl. destruct c0.
  - (* true because enum n means l is empty, but need some assumptions on the size of l w.r.t. arity of the constructor *)

    admit.
  - (* by construction*)
    admit.


  - simpl. induction (rev l). simpl. rewrite H_makeTag. rewrite H_make_ctor_rep. auto.
  simpl. rewrite IHl0. auto.
  -  simpl. induction (rev l). simpl. rewrite H_makeTag. auto.
  simpl. rewrite IHl0. auto.
Admitted.
*)



Theorem find_symbol_map:
  forall p fenv m finfo_env id v,
    find_symbol_domain p finfo_env ->
    var_or_funvar id m fenv finfo_env p v (makeVar id m v fenv finfo_env).
Proof.
  intros. specialize (H v). inv H.
  destruct (term.M.get v finfo_env) eqn:Hgvm.
  - destruct (H0 (ex_intro _ p0 (eq_refl _))). econstructor. apply H.
  - unfold makeVar. rewrite Hgvm. econstructor.
    destruct (Genv.find_symbol (Genv.globalenv p) v) eqn:Hgpv; auto.
    exfalso.
    destruct (H1 (ex_intro _ b (eq_refl _))).
    inv H.
Qed.

Theorem find_symbol_map_f:
    forall p fenv m finfo_env id v,
    find_symbol_domain p finfo_env ->
    var_or_funvar_f id m fenv finfo_env p v = makeVar id m v fenv finfo_env.
Proof.
  intros. apply var_or_funvar_of_f.
  apply find_symbol_map; auto.
Qed.

Theorem asgnAppVars_correct:
  forall p fenv finfo_env,
    forall vs avs ind aind s,
    find_symbol_domain p finfo_env ->
      avs = skipn nParam vs ->
      aind = skipn nParam ind ->
      asgnAppVars' argsIdent threadInfIdent nParam vs ind fenv finfo_env = Some s ->
      repr_asgn_fun' argsIdent threadInfIdent nParam fenv finfo_env p avs aind s.
Proof.
  intros p fenv finfo_env vs avs. generalize vs. clear vs.
  induction avs; intros vs ind aind s Hfinfo_env Hvs Hind Hasgn; unfold asgnAppVars' in Hasgn.
  - destruct aind; rewrite <- Hvs in Hasgn; rewrite <- Hind in Hasgn;
      destruct nParam; inv Hasgn; constructor.
  - destruct aind; rewrite <- Hvs in Hasgn; rewrite <- Hind in Hasgn; [ destruct nParam; inv Hasgn | ].
    destruct vs; [destruct nParam; inv Hvs | ].
    destruct ind; [destruct nParam; inv Hind | ].
    symmetry in Hvs.
    set (Hvs' := skipn_cons nParam p0 a vs avs Hvs).
    symmetry in Hvs'.
    symmetry in Hind.
    set (Hind' := skipn_cons nParam n0 n ind aind Hind).
    symmetry in Hind'.
    simpl in Hasgn.
    destruct (asgnAppVars'' argsIdent threadInfIdent nParam avs aind fenv) eqn:Happ.
    2: inv Hasgn.
    specialize (IHavs _ _ _ s0 Hfinfo_env Hvs' Hind').
    unfold asgnAppVars' in IHavs.
    rewrite <- Hvs' in IHavs.
    rewrite <- Hind' in IHavs.
    apply IHavs in Happ.
    inv Hasgn.
    erewrite <- find_symbol_map_f; eauto.
    exact (repr_asgn_cons _ _ _ _ _ _ _ _ _ _ s0 Happ).
Qed.

Theorem repr_call_vars_length1 : forall p fenv map n l1 l2, repr_call_vars threadInfIdent nParam fenv map p  n l1 l2 -> length l1 = n.
Proof.
      induction n; intros l1 l2 Hr; destruct l1; inv Hr.
      + reflexivity.
      + simpl. apply f_equal.
        eapply IHn. eauto.
Qed.


Theorem  mkCallVars_correct:
  forall p fenv map n vs bvs es,
    find_symbol_domain p map ->
    bvs = firstn nParam vs ->
    mkCallVars threadInfIdent nParam fenv map n bvs = Some es ->
    repr_call_vars threadInfIdent nParam fenv map p n bvs es.
Proof.
  Admitted. (*
  intros p fenv map n. unfold repr_call_vars.
  generalize nParam as m.
  induction n; intros m vs bvs es Hsym bvsEq Hcall;
    destruct bvs; try solve [unfold mkCallVars in Hcall; inv Hcall; try constructor; try inv bvsEq].
  + simpl in Hcall.
    match_case_hyp Hcall.
    inv Hcall.
    erewrite <- (find_symbol_map_f _ _ _ _ _ _ Hsym).
    constructor.
    eapply IHn; eauto.
    constructor. destruct m; inv bvsEq.
    destruct m. inv bvsEq.
    rewrite (firstn_cons m p1 vs) in bvsEq.
    eapply IHn; auto.
    inbvsEq. destruct m; inv bvsEq.
    destruct m. inv bvsEq.
    rewrite (firstn_cons m p1 vs) in bvsEq.
    inversion bvsEq. Print repr_call_vars.
    admit.

  Set Printing All. simpl.
  generalize nParam as m.
  induction m; induction n; intros vs bvs es Hsym bvsEq Hcall;
    destruct bvs; try solve [unfold mkCallVars in Hcall; inv Hcall; try constructor].
  - inv bvsEq.
  - simpl in Hcall.
    destruct (mkCallVars threadInfIdent (S m) fenv map n bvs) eqn:HcallEq; inv Hcall.
    erewrite <- (find_symbol_map_f _ _ _ _ _ _ Hsym).
    constructor.
    Print repr_call_vars.
  intro n.


    admit.
(*
    eapply IHn.
    reflexivity.
    assumption.
Qed. *)
Admitted. *)


Theorem repr_make_case_switch:
  forall x ls ls',
  repr_switch_LambdaANF_Codegen isptrIdent caseIdent x ls ls' (make_case_switch isptrIdent caseIdent x ls ls').
Proof.
  intros. unfold make_case_switch. constructor.
Qed.


Definition makeCases argsIdent allocIdent limitIdent threadInfIdent tinfIdent isptrIdent caseIdent (p:program) fenv cenv ienv map :=
 (fix makeCases (l : list (ctor_tag * exp)) :
            option (labeled_statements * labeled_statements) :=
            match l with
            | [] => Monad.ret (LSnil, LSnil)
            | p :: l' =>
                Monad.pbind
                  (translate_body argsIdent allocIdent limitIdent threadInfIdent tinfIdent isptrIdent caseIdent nParam (snd p) fenv cenv ienv map)
                  (fun prog : statement =>
                   Monad.pbind (makeCases l')
                     (fun '(ls, ls') =>
                      match make_ctor_rep cenv (fst p) with
                      | Some (enum t) =>
                        let tag := ((Z.shiftl (Z.of_N t) 1) + 1)%Z in
                          match ls' with
                          | LSnil =>
                              Monad.ret (ls, LScons None  (Ssequence prog Sbreak) ls')
                          | LScons _ _ _ =>
                              Monad.ret
                                (ls,
                                LScons (Some (Z.shiftr tag 1))
                                  (Ssequence prog Sbreak) ls')
                          end
                      | Some (boxed t a) =>
                        let tag := ((Z.shiftl (Z.of_N a) 10) + (Z.of_N t))%Z in
                          match ls with
                          | LSnil =>
                              Monad.ret (LScons None (Ssequence prog Sbreak) ls, ls')
                          | LScons _ _ _ =>
                              Monad.ret
                                (LScons (Some (Z.land tag 255))
                                   (Ssequence prog Sbreak) ls,
                                ls')
                          end
                      | None => None
                      end))
            end).

Definition fmake_ctor_rep (p:positive) (c:ctor_ty_info) : ctor_rep :=
  let '(Build_ctor_ty_info name _ it  a  n) := c in
      match (a =? 0)%N with
      | true =>
        (enum n)
      | false =>
        (boxed n a)
      end.


Definition compute_rep_env (cenv:ctor_env): M.t ctor_rep :=
  M.map fmake_ctor_rep cenv.



Theorem crep_cenv_correct:
forall cenv rep_env,
  correct_crep_of_env cenv rep_env ->
  forall c,
    make_ctor_rep cenv c =  M.get c rep_env.
Proof.
  intros. unfold make_ctor_rep.
  destruct (term.M.get c cenv) eqn:Hgc.
  - destruct c0.
    simpl.
    destruct (ctor_arity =? 0)%N eqn:Hn0.
    + rewrite N.eqb_eq in Hn0. subst.
      inv H. specialize (H0 _ _ _ _ _ _ Hgc). destruct H0. destruct H. inv H0; rewrite H2 in Hgc; inv Hgc. auto.
    + rewrite N.eqb_neq in Hn0.
      inv H. specialize (H0 _ _ _ _ _ _ Hgc). destruct H0. destruct H. inv H0; rewrite H2 in Hgc; inv Hgc.  exfalso; apply Hn0; auto.
      auto.
  -  simpl. symmetry.
     inv H. destruct (M.get c rep_env) eqn:Hcr.
     exfalso. apply H1 in Hcr. inv Hcr; rewrite H in Hgc; inv Hgc. auto.
Qed.

Theorem nth_proj_assign':
      forall p fenv finfo_env,
        find_symbol_domain p finfo_env ->
        forall v l a n,
        Forall_statements_in_seq' (is_nth_projection_of_x threadInfIdent nParam fenv finfo_env p v)
                                  (a :: l) (assignConstructorS' threadInfIdent nParam fenv finfo_env v n (a :: l)) (Z.of_nat n).
Proof.
  induction l; intros.
  - (* last *)
    simpl. constructor.
    constructor.
    apply find_symbol_map; eauto.
  - (* IH *)
    specialize (IHl a (S n)).
    remember (a::l) as l'. simpl.
    rewrite Heql'.  constructor.
    rewrite Nat2Z.inj_succ in IHl.
    rewrite <- Heql'. rewrite Nat.add_1_r. auto.
    constructor.
    apply find_symbol_map; eauto.
Qed.


Theorem nth_proj_assign:
      forall p fenv finfo_env ,
        find_symbol_domain p finfo_env ->
        forall v l,
          length l > 0 ->
      Forall_statements_in_seq (is_nth_projection_of_x threadInfIdent nParam fenv finfo_env p v) l (assignConstructorS' threadInfIdent nParam fenv finfo_env v 0 l).
Proof.
  induction l.
  intros Hl. inv Hl.
  intros. unfold Forall_statements_in_seq.
  apply nth_proj_assign'. auto.
Qed.

Theorem repr_asgn_constructorS:
  forall p cenv ienv  rep_env fenv finfo_env v c l s name iname it n,
      find_symbol_domain p finfo_env ->
  correct_crep_of_env cenv  rep_env ->
  M.get c cenv = Some  (Build_ctor_ty_info name iname it (N.of_nat (length l)) n) ->
        assignConstructorS allocIdent threadInfIdent nParam cenv ienv fenv finfo_env v c l = Some s ->
repr_asgn_constr allocIdent threadInfIdent nParam fenv finfo_env p rep_env v c l s.
Proof.
  intros p cenv ienv rep_env fenv map v c l s name iname it n Hsymbol; intros.
  unfold assignConstructorS in *.
    destruct (makeTag cenv c) eqn:H_makeTag.
    destruct (make_ctor_rep cenv c) eqn:H_make_ctor_rep.
    simpl in H1. destruct c0; inv H1.
  - unfold make_ctor_rep in H_make_ctor_rep. rewrite H0 in H_make_ctor_rep. simpl in *.
    destruct ((N.of_nat (length l) =? 0)%N ) eqn:Hll; inv H_make_ctor_rep.
    rewrite OrdersEx.N_as_OT.eqb_eq in Hll.
    destruct l; inv Hll.
    unfold makeTag in *.
    destruct (makeTagZ cenv c) eqn:H_makeTagZ; inv H_makeTag.
    inv H. specialize (H1 _ _ _ _ _ _ H0). inv H1. inv H. inv H3; rewrite H0 in H; inv H.
    econstructor. apply H1.
    {split.  unfold makeTagZ in *.  unfold make_ctor_rep in *. rewrite H0 in H_makeTagZ. simpl in H_makeTagZ. inv H_makeTagZ.
     reflexivity.
     auto. }
  - unfold make_ctor_rep in H_make_ctor_rep. rewrite H0 in H_make_ctor_rep. simpl in *.
    destruct ((N.of_nat (length l) =? 0)%N ) eqn:Hll; inv H_make_ctor_rep.
    unfold makeTag in H_makeTag.
    destruct (makeTagZ cenv c) eqn:H_makeTagZ; inv H_makeTag.
    inv H. specialize (H1 _ _ _ _ _ _ H0). destruct H1. destruct H.
    rewrite OrdersEx.N_as_OT.eqb_neq in Hll.
    inv H1; rewrite H3 in H0; inv H0. exfalso; auto.
    econstructor. eauto.
    { split. unfold makeTagZ in *. unfold make_ctor_rep in *.
      rewrite H3 in H_makeTagZ. simpl Monad.pbind in H_makeTagZ.
      inv H_makeTagZ; auto.
      split; auto.  }
    apply nth_proj_assign. auto.
    destruct l. exfalso; auto. apply gt_Sn_O.
  - simpl in H1; inv H1.
  - simpl in H1. inv H1.
Qed.






Theorem make_crep_none:
  forall c cenv,
  make_ctor_rep cenv c = None ->
  M.get c cenv = None.
Proof.
  intros.
  unfold make_ctor_rep in *.
  destruct (term.M.get c cenv); auto.
  exfalso. destruct c0. inv H.
  destruct (ctor_arity =? 0)%N; inv H1.
Qed.

Theorem make_tagZ_none:
  forall c cenv,
  makeTagZ cenv c = None ->
  M.get c cenv = None.
Proof.
  intros.
  unfold makeTagZ in *.
  unfold make_ctor_rep in *.
  destruct (term.M.get c cenv). destruct c0. simpl in H.
  destruct  (ctor_arity =? 0)%N; inv H. auto.
Qed.

(* Main Theorem *)
Theorem translate_body_correct:
  forall fenv cenv ienv  p rep_env map,
    find_symbol_domain p map ->
    finfo_env_correct fenv map ->
    correct_crep_of_env cenv rep_env ->
    forall  e stm,
      correct_cenv_of_exp cenv e ->
    translate_body argsIdent allocIdent limitIdent threadInfIdent tinfIdent isptrIdent caseIdent nParam e fenv cenv ienv map = Some stm ->
    repr_expr_LambdaANF_Codegen_id fenv map p rep_env e stm.
Proof.
  intros fenv cenv ienv  p rep_env map Hmap Hmapcorrect Hcrep.
  induction e using exp_ind'; intros stm Hcenv; intros.
  - (* Econstr *)
    simpl in H.
    destruct (assignConstructorS allocIdent threadInfIdent nParam cenv ienv fenv map v t l) eqn:H_eqAssign.
    destruct (translate_body argsIdent allocIdent limitIdent threadInfIdent tinfIdent isptrIdent caseIdent nParam e fenv cenv ienv map) eqn:H_eqTranslate; inv H.
    2: inv H.
    constructor.
    2: eapply IHe; eauto.
    clear IHe H_eqTranslate.
    apply Forall_constructors_in_constr in Hcenv.
    destruct (M.get t cenv) eqn:Hccenv. destruct c.
    subst.
    eapply repr_asgn_constructorS; eauto.
    inv Hcenv.
    eapply Forall_constructors_subterm. apply Hcenv. constructor. constructor.
  -  (* Ecase nil *) simpl in H. inv H.
                     econstructor. constructor. apply repr_make_case_switch.
  - (* Ecase *)
    simpl in H.
    destruct (translate_body argsIdent allocIdent limitIdent threadInfIdent tinfIdent isptrIdent caseIdent nParam e fenv cenv ienv map) eqn:He.
    destruct (translate_body argsIdent allocIdent limitIdent threadInfIdent tinfIdent isptrIdent caseIdent nParam (Ecase v l) fenv cenv ienv map) eqn:Hl.
    assert (correct_cenv_of_exp cenv (Ecase v l)).
    { intro; intros. eapply Hcenv. apply rt_then_t_or_eq in H0. inv H0. inv H1. apply t_then_rt. apply subterm_case. eauto. }
    specialize (IHe0 s0 H0). clear H0.  assert (Some s0 = Some s0) by reflexivity. specialize (IHe0 H0). clear H0.
    simpl in Hl.
    destruct (makeCases argsIdent allocIdent limitIdent threadInfIdent tinfIdent isptrIdent caseIdent p fenv cenv ienv map l) eqn:Hmc.
    assert (Hmc' := Hmc); unfold makeCases in Hmc; simpl in Hmc; rewrite Hmc in H; rewrite Hmc in Hl; clear Hmc.
    destruct p0. inv Hl.
    + (* step case *)
      {
        assert ( correct_cenv_of_exp cenv e).
        { intro; intros. eapply Hcenv.  eapply rt_trans. eauto. constructor. econstructor. constructor. reflexivity. }
        specialize (IHe s H0 eq_refl). clear H0.
        inv IHe0. (* l0 = ls, ls' = l1 *) unfold make_case_switch in H4. inv H4.
        destruct ( make_ctor_rep cenv c ) eqn:Hctor_rep. 2: inv H.
        destruct c0.
        - (* case-enum *)
          destruct l1.
          + (* case-enum-last *)
            inv H. econstructor.
            eapply Runboxed_default_br; eauto. erewrite <- crep_cenv_correct; eauto.
            apply repr_make_case_switch.
          + (* case-enum-step *)
            inv H. econstructor.
            eapply Runboxed_br; eauto. erewrite <- crep_cenv_correct; eauto.
            2: apply repr_make_case_switch.
            erewrite crep_cenv_correct in Hctor_rep; eauto.
            inv Hcrep. apply H0 in Hctor_rep.  inv Hctor_rep. constructor; auto.
        - (* case-boxed *)
          destruct l0.
          + (* case-boxed-last *)
            inv H. econstructor.
            eapply Rboxed_default_br; eauto. erewrite <- crep_cenv_correct; eauto.
            apply repr_make_case_switch.
          + (* case-boxed-step *)
            inv H. econstructor.
            eapply Rboxed_br; eauto. erewrite <- crep_cenv_correct; eauto.
            2: apply repr_make_case_switch.
            erewrite crep_cenv_correct in Hctor_rep; eauto.
            inv Hcrep. apply H0 in Hctor_rep.  inv Hctor_rep. constructor; auto.

      }
    +   assert (Hmc' := Hmc); unfold makeCases in Hmc; simpl in Hmc; rewrite Hmc in H; rewrite Hmc in Hl; clear Hmc.  inv H.
    +  (* should probably invvert destruction of makeCases and Hl to avoid this redundant case *) simpl in Hl.
      destruct (makeCases argsIdent allocIdent limitIdent threadInfIdent tinfIdent isptrIdent caseIdent p fenv cenv ienv map l) eqn:Hmc.
      assert (Hmc' := Hmc); unfold makeCases in Hmc; simpl in Hmc; rewrite Hmc in H; rewrite Hmc in Hl; clear Hmc.  destruct p0; inv Hl.
      assert (Hmc' := Hmc); unfold makeCases in Hmc; simpl in Hmc; rewrite Hmc in H; rewrite Hmc in Hl; clear Hmc.  inv H.
    +  inv H.
  - (* Eproj *)
      simpl in H.
      destruct (translate_body argsIdent allocIdent limitIdent threadInfIdent tinfIdent isptrIdent caseIdent nParam e fenv cenv ienv map) eqn:He.
      2: inv H.
      inv H. constructor.
      eapply IHe.
      eapply Forall_constructors_subterm. apply Hcenv. constructor. constructor.
      reflexivity.
  - (* Efun *)
    inv H.
  - (* Eapp *)
    unfold translate_body in H.
    destruct (term.M.get t fenv) eqn:Hffenv. 2:inv H.
    destruct f as [n locs].
    unfold var , term.M.elt in l.
    set (avs := skipn nParam l).
    set (aind := skipn nParam locs).
    set (bvs := firstn nParam l).
    assert (vsEq : avs = skipn nParam l). reflexivity.
    assert (indEq : aind = skipn nParam locs). reflexivity.
    assert (bvsEq : bvs = firstn nParam l). reflexivity.
    unfold asgnAppVars in H. unfold asgnAppVars' in H.
    unfold mkCall in H.
    simpl in H.
    rewrite <- vsEq in H. rewrite <- indEq in H. rewrite <- bvsEq in H.
    destruct (asgnAppVars'' argsIdent threadInfIdent nParam avs aind fenv map) eqn:Happvar; inv H.
    destruct (mkCallVars threadInfIdent nParam fenv map (Init.Nat.min (N.to_nat n) nParam) bvs) eqn:Hcallvar; inv H1.
    erewrite <- find_symbol_map_f. 2: eauto.
    econstructor; eauto.
    constructor.
    eapply asgnAppVars_correct; eauto.
    eapply mkCallVars_correct; eauto.
  - (* Eprim *)
    inv H.
  - (* Ehalt *)
    simpl in H. inv H.

    eapply R_halt_e.
    apply find_symbol_map. auto.
Qed.



(* PROOFs on correct environments *)

(* ctor_ty_info is proper if a and ord are small enough to be represented *)
Inductive proper_ctor_ty_info: ctor_ty_info -> Prop :=
| PC_enum: forall name iname it ord,
    (0 <= (Z.of_N ord) <   Ptrofs.half_modulus)%Z ->
    proper_ctor_ty_info (Build_ctor_ty_info name iname it 0%N ord)
| PC_boxed: forall name iname it a ord,
    (* there should not be more than 2^8 - 1 boxed constructors *)
    (0 <= (Z.of_N ord) <  Zpower.two_p 8)%Z ->
    (* arity shouldn't be higher than 2^54 - 1  *)
    (0 <= Z.of_N (Npos a) <  Zpower.two_power_nat (Ptrofs.wordsize - 10))%Z ->
    proper_ctor_ty_info (Build_ctor_ty_info name iname it (Npos a)%N ord).



(* cenv is proper if ctor_ty_info is proper, and that there is a unique (ty, ord) pair for each constructors  *)
Definition proper_cenv (cenv:ctor_env):=
  forall c name iname it a ord,
    M.get c cenv = Some (Build_ctor_ty_info name iname it a ord) ->
    proper_ctor_ty_info (Build_ctor_ty_info name iname it a ord) /\
      ~ (exists c' name' iname' a', c <> c' /\
                    M.get c' cenv = Some (Build_ctor_ty_info name' iname' it a' ord)).

(* Definition proper_nenv ? *)



Theorem proper_cenv_set_none:
  forall k v m,
  proper_cenv (Maps.PTree.set k v m) ->
  M.get k m = None ->
  proper_cenv m.
Proof.
  intros; intro; intros.
  assert (c <> k). intro; subst. rewrite H1 in H0; inv H0.
  split.
  erewrite <- M.gso in H1. 2: eauto. apply H in H1. destruct H1; auto.
  intro; destructAll.
  assert (x <> k). intro; subst. rewrite H4 in H0; inv H0.
  erewrite <- M.gso in H1.
  apply H in H1. destruct H1.
  apply H6.
  exists x, x0, x1, x2.
  split; auto.
  rewrite M.gso; auto.
  auto.
Qed.





Theorem compute_proper_rep_env: forall cenv,
proper_cenv cenv ->
  correct_crep_of_env cenv (compute_rep_env cenv).
Proof.
  intros. split; intros.
  - unfold compute_rep_env. rewrite M.gmap.
    unfold fmake_ctor_rep. rewrite H0.
    simpl.
    specialize (H _ _ _ _ _ _ H0). destructAll.
    destruct a.
    + eexists; split; auto. rewrite N.eqb_refl.  inv H. econstructor; eauto.
    + eexists; split; auto. assert (N.pos p <> 0%N). intro Hp; inv Hp. rewrite <- N.eqb_neq in H2.  rewrite H2. inv H. econstructor; eauto.
  - unfold compute_rep_env in H0.
    rewrite M.gmap in H0.
    unfold fmake_ctor_rep in H0.
    destruct (M.get c cenv) eqn:Hccenv. 2: inv H0.
    destruct c0. simpl in H0.
    specialize (H _ _ _ _ _ _ Hccenv). destruct H.
    destruct ctor_arity.
    + rewrite N.eqb_refl in H0.  inv H0. inv H. econstructor; eauto.
    + assert (N.pos p <> 0%N). intro Hp; inv Hp. rewrite <- N.eqb_neq in H2.  rewrite H2 in H0. inv H0. inv H. econstructor; eauto.
Qed.


  Theorem compute_dc_ienv:
  forall cenv,
    (fun cenv ienv => proper_cenv cenv ->
                      domain_ienv_cenv cenv ienv /\
                    correct_ienv_of_cenv cenv ienv) cenv (compute_ind_env cenv).
Proof.
  intro cenv.
  eapply Maps.PTree_Properties.fold_rec; intros.
  - assert (proper_cenv m).
    { intro; intros. rewrite H in H2. apply H1 in H2. destruct H2.
      split; auto. intro; apply H3.  destructAll. rewrite H in H5.
      exists x , x0 , x1 , x2. auto.
    }
    specialize (H0 H2). destruct H0. split.
    intro; intros. eapply H0 in H5; eauto. rewrite H in H5. auto.
    intro; intros. rewrite <- H in H4. apply H3 in H4. auto.
  - split; intro; intros; rewrite M.gempty in *; exfalso; inv H0.
  - assert (proper_cenv  m) by (eapply proper_cenv_set_none; eauto).
    specialize (H1 H3). destruct H1.
    assert ( domain_ienv_cenv (Maps.PTree.set k v m) (update_ind_env a k v)).
    {
      intro; intros. destruct v. simpl in H5.
      destruct ( term.M.get ctor_ind_tag a) eqn:Hgi0a.
      + destruct n.
        destruct (var_dec i ctor_ind_tag).
        * subst. rewrite M.gss in H5. inv H5. inv H6.
          (* k = x *)
          inv H5. eexists. apply M.gss.
          (* k <> x *)
          eapply H1 in H5; eauto. destruct H5. eexists.
          rewrite M.gso. eauto. intro; subst. rewrite H5 in H. inv H.
        * rewrite M.gso in H5 by auto.
          eapply H1 in H6; eauto. destruct H6. eexists.
          rewrite M.gso. eauto. intro; subst. rewrite H6 in H; inv H.
      + destruct (var_dec i ctor_ind_tag).
        * subst. rewrite M.gss in H5. inv H5. inv H6. inv H5. exists namei. apply M.gss. inv H5.
        * rewrite M.gso in H5 by auto. apply H1 in H5. apply H5 in H6. destruct H6.
          exists x0. rewrite M.gso. auto.  intro; subst. rewrite H in H6. inv H6.
    } split; auto.



    intro. intros.
    assert (H6' := H6).
    apply H2 in H6'. destruct H6' as [H6b H6'].
    destruct (term_util.var_dec x k).
    + (* x = k  -> can update i and it still be proper *)
      subst. rewrite M.gss in H6. inv H6.
      simpl.  destruct (M.get i a) eqn:Hgia.
      * (* i was already in a *)
        destruct n. eexists. eexists. split.  apply M.gss.
        split. constructor. reflexivity.
        split; intro; intros; destructAll.
        inv H7. inv H8. apply H6; auto.
        eapply H1 in H8; eauto. inv H8. rewrite H7 in H; inv H.
        inv H7. inv H8. apply H6; auto.
        (* constructor shares the same ord, cannot be proper *)
        eapply H1 in H8; eauto. inv H8.
        destruct (var_dec x0 k); subst. rewrite H7 in H; inv H.
        apply H6'. exists x0. eexists. eexists. eexists.
        split; auto. rewrite M.gso by auto. eauto.
      * (* k is the first cons of i *)
        eexists. eexists. split. apply M.gss.
        split. constructor. reflexivity.
        split; intro; intros; destructAll.
        inv H7; inv H8. apply H6; auto.
        inv H7; inv H8. apply H6; auto.
    + (* x <> k *)

      assert (H6'' := H6).
      rewrite M.gso in H6 by auto.
      apply H4 in H6. destructAll.
      {
        unfold update_ind_env. destruct v.
        destruct  (term.M.get ctor_ind_tag a) eqn:Hi0a.
        - destruct n0.
          destruct (var_dec i ctor_ind_tag).
          + subst.
            rewrite Hi0a in H6. inv H6.
            eexists. exists  ((ctor_name, k, ctor_arity, ctor_ordinal) :: x1).
            split. rewrite M.gss; auto.
            split. constructor 2. auto.
            split.
            * intro; intros.
              destructAll.
              inv H10.
              inv H11. apply n; auto.
              apply H8. eexists; eexists; eexists. split; eauto.
            * intro; intros.
              destructAll.
              inv H10.
              inv H11. apply H6'. eexists. eexists. eexists. eexists. split.
              apply n. rewrite M.gss. reflexivity.
              eapply H9.
              eexists. eexists. eexists. split; eauto.
          + exists x0, x1. rewrite M.gso; auto.
        - exists x0, x1. rewrite M.gso. auto. intro; subst. rewrite H6 in Hi0a. inv Hi0a.
      }
Qed.



(* Note: can be proven directly *)
Corollary compute_domain_ienv:
  forall cenv,
                    (fun cenv ienv => proper_cenv cenv ->
                    domain_ienv_cenv cenv ienv) cenv (compute_ind_env cenv).
Proof.
    assert ( forall cenv,
           (fun cenv ienv => proper_cenv cenv ->
                              domain_ienv_cenv cenv ienv /\
                    correct_ienv_of_cenv cenv ienv) cenv (compute_ind_env cenv)) by apply compute_dc_ienv. simpl; intros. simpl in H.  apply H in H0. destruct H0.
  auto.
Qed.


Corollary compute_correct_ienv:
  forall cenv,
                    (fun cenv ienv => proper_cenv cenv ->
                    correct_ienv_of_cenv cenv ienv) cenv (compute_ind_env cenv).
Proof.
  assert ( forall cenv,
           (fun cenv ienv => proper_cenv cenv ->
                              domain_ienv_cenv cenv ienv /\
                    correct_ienv_of_cenv cenv ienv) cenv (compute_ind_env cenv)) by apply compute_dc_ienv. simpl; intros. simpl in H.  apply H in H0. destruct H0.
  auto.
Qed.


Definition correct_fenv_for_function (fenv:fun_env):=
  fun f (t:fun_tag) (ys:list LambdaANF.term.var) (e:exp) =>
    exists n l, M.get f fenv = Some (n, l) /\
                n = N.of_nat (length l) /\
                length l = length ys /\
                    NoDup l /\
                    Forall (fun i => 0 <= (Z.of_N i) < max_args)%Z l.

SearchAbout fun_tag.
(* fun_tag are associated with an arity and a calling convention.
   all functions and applications with this fun_tag have the right number of arguments *)

Definition correct_fenv (fenv:fun_env) (fds:fundefs):= Forall_fundefs (correct_fenv_for_function fenv) fds.

(*
(* unique tags of arity *)
Theorem compute_correct_fenv:
  forall fds  fenv,

    forall fenv',
  compute_fun_env_fds fds fenv' = fenv ->
  Forall_fundefs (correct_fenv_for_function fenv) fds.
Proof.
  induction fds; intros.
  -  simpl in H0.
     inv H.
     constructor.
     +   admit.
     + eapply IHfds. auto. reflexivity.
  - constructor.
Qed.  *)




(* TODO: something that implies correct_fundef_info when ldefs are put in memory
Theorem make_fundef_info_correct:
  correct_fenv fenv fds ->
  make_fundef_info fds fenv nenv = Some (ldefs * finfo_env * nenv') ->


*)






Definition program_inv (p:program) := program_isPtr_inv p /\ program_threadinfo_inv p /\ program_gc_inv p.

(* At the top level:
  correct_envs >
    > correct_ienv_of_cenv -> link ienv and crep
    > correct_cenv_of_env -> this is just correct_cenv_of_exp for all functions, which is to say correct_cenv_of_exp on the full initial term
    > correct_cenv_of_exp -> see above, correct_cenv_of_exp (fds e) so correct_cenv_of_exp e
    > correct_crep_of_env -> correctness of crep
  protected_id_not_bound -> disjoint bound_var and protected_id
  unique_bindings_envs -> by unique_bindings on e
  functions_not_bound -> by unique_bindings, all bound vars in e are disjoint from functions which were added to globalenv
  rel_mem -> L can be empty since rho only has fun,
             repr_val_id for all funs
             closed_val for all funs
             correct_fundefs_info for all funs
  correct_alloc -> just computed
  correct_tinfo ->  tinfo is initialized properly
 *)

Theorem sizeof_uval:
  forall p,
  (sizeof p uval) = int_size.
Proof.
  intro. unfold sizeof.
  chunk_red; archi_red; auto.
Qed.

Theorem sizeof_val:
  forall p,
  (sizeof p val) = int_size.
Proof.
  intro. unfold sizeof.
  chunk_red; archi_red; auto.
Qed.


Theorem ptrofs_of_int64:
  forall x,
  Ptrofs.repr (Int64.unsigned (Int64.repr x)) = Ptrofs.repr x.
Proof.
  intro.
  symmetry.
  eapply Ptrofs.eqm_samerepr. apply Int64.eqm_unsigned_repr.
Qed.

Theorem ptrofs_of_int:
  forall x,
    Archi.ptr64 = false ->
  Ptrofs.repr (Int.unsigned (Int.repr x)) = Ptrofs.repr x.
Proof.
  intros.
  symmetry.
  eapply Ptrofs.eqm_samerepr.
  apply Ptrofs.eqm32; auto.
  apply Int.eqm_unsigned_repr.
Qed.

Theorem sem_cast_vint:
  forall n m,
 sem_cast (make_vint n) uval uval m = Some (make_vint n).
Proof.
  intros. unfold sem_cast; chunk_red; simpl; archi_red; simpl; archi_red; auto.
Qed.


Theorem sem_notbool_val:
  forall n m,
    sem_notbool
          (Val.of_bool n) type_bool  m = Some (Val.of_bool (negb n)).
Proof.
  intros; destruct n; simpl; reflexivity.
Qed.

Theorem eval_cint :
  forall p env lenv m z,
 eval_expr (globalenv p) env lenv m
    (make_cint z val) (make_vint z).
Proof.
  intros.
  chunk_red; archi_red.
  constructor.
  unfold make_cint. archi_red. constructor.
Qed.

Definition mk_gc_call_env' p (ys vs : list positive) (lenv_old lenv : temp_env) :
  (Forall (fun x : positive => exists v : Values.val, get_var_or_funvar p lenv_old x v) ys) -> length ys = length vs -> temp_env.
Proof.
  generalize vs. clear vs.
  induction ys; intros vs Hval Hlen; destruct vs; [ | inv Hlen | inv Hlen | ].
  - exact lenv.
  - refine (M.set p0 _ (IHys vs _ _)).
    destruct (Genv.find_symbol (Genv.globalenv p) a) eqn:geta1.
    + exact (Vptr b (Ptrofs.repr 0)).
    + destruct (M.get a lenv_old) eqn:geta2.
      * exact v.
      * abstract (
            set (t := proj1 (Forall_forall _ _) Hval a (or_introl eq_refl));
            simpl in t;
            exfalso; inv t; inv H; [ rewrite geta1 in H0; inv H0
                                   | rewrite geta2 in H1; inv H1]
            ).
    + abstract(apply Forall_forall; intros x Hin;
               exact (proj1 (Forall_forall _ _) Hval x (or_intror Hin))).
    + abstract (inv Hlen; auto).
Defined.


Definition mk_gc_call_env p (ys vs : list positive) (lenv_old lenv : temp_env) :
  (Forall (fun x : positive => exists v : Values.val, get_var_or_funvar p lenv_old x v) ys) -> length ys = length vs -> temp_env.
Proof.
  generalize vs. clear vs.
  induction ys; intros vs Hval Hlen; destruct vs; [ | inv Hlen | inv Hlen | ].
  - exact lenv.
  - refine (M.set p0 _ (IHys vs _ _)).
    destruct (Genv.find_symbol (Genv.globalenv p) a).
    + exact (Vptr b (Ptrofs.repr 0)).
    + destruct (M.get a lenv_old).
      * exact v.
      * exact Vundef.
    + abstract(apply Forall_forall; intros x Hin;
               exact (proj1 (Forall_forall _ _) Hval x (or_intror Hin))).
    + abstract (inv Hlen; auto).
Defined.

Theorem mk_gc_call_env_correct : forall p (ys vs : list positive) (lenv_old lenv : temp_env) Hys Hlen, NoDup vs ->
    (Forall (fun x : positive => exists v : Values.val, get_var_or_funvar p (mk_gc_call_env p ys vs lenv_old lenv Hys Hlen) x v) vs).
Proof.
  intros p ys. induction ys; intros vs lenv_old lenv Hys Hlen noDupvs; destruct vs; [ | inv Hlen | inv Hlen | ]; constructor.
  - destruct Hys. inv Hlen. clear a.
    destruct e as [v Hv]. exists v.
    destruct Hv; simpl.
    + constructor 2.
      * admit.
      * rewrite Maps.PTree.gss. rewrite e.
        reflexivity.
      * auto.
    + constructor 2.
      * admit.
      * rewrite Maps.PTree.gss. rewrite e.
        rewrite e0.
        reflexivity.
      * auto.
  - admit.
    Admitted.
   (* apply IHys.

    destruct (Genv.find_symbol (Genv.globalenv p) x) eqn:geta1.
    + exists (Vptr b (Ptrofs.repr 0)).
      simpl. constructor 2.
      * admit.
      * rewrite Maps.PTree.gss.
        rewrite geta1. reflexivity.
      *

    + destruct (M.get a lenv_old) eqn:geta2.
      *
      *
        rewrite geta1.
        rewrite geta1.
    unfold mk_gc_call_env. simpl.

    eexists.
    simpl.
    rewrite geta1. *)

Ltac unsigned_ptrofs_range :=
  split; [apply Ptrofs.unsigned_range |  etransitivity;  [apply Ptrofs.unsigned_range_2 | rewrite ptrofs_mu; archi_red; reflexivity] ].


Theorem type_of_mkFunTyList:
  forall nParam vsm4,
  (mkFunTyList
     (Init.Nat.min (length vsm4)
             nParam)) = (type_of_params (map (fun x : ident => (x, uval))
                                              (firstn nParam vsm4))).
Proof.
  induction nParam0; intros; simpl.
  -  rewrite Nat.min_0_r.
     reflexivity.
  - destruct vsm4.
    + (* empty list *)
      reflexivity.
    + simpl. erewrite IHnParam0. reflexivity.
Qed.

(* Main Theorem *)
Theorem repr_bs_LambdaANF_Codegen_related:
  forall (p : program) (rep_env : M.t ctor_rep) (cenv : ctor_env)
         (fenv : fun_env) (finfo_env : M.t (positive * fun_tag)) (ienv : n_ind_env),
    program_inv p -> (* isPtr function is defined/correct /\ thread info is correct /\ gc invariant *)
    find_symbol_domain p finfo_env -> (* finfo_env [LambdaANF] contains precisely the same things as global env [Clight] *)
    finfo_env_correct fenv finfo_env -> (* everything in finfo_env is in the function environment *)
    forall (rho : eval.env) (v : term.val) (e : exp) (n : nat), (* rho is environment containing outer fundefs. e is body of LambdaANF program *)
      bstep_e (M.empty _) cenv rho e v n ->  (* e n-steps to v *) (* for linking: environment won't be empty *)
      correct_envs cenv ienv rep_env rho e -> (* inductive type/constructor environments are correct/pertain to e*)
      protected_id_not_bound_id rho e ->
      unique_bindings_env rho e ->
      functions_not_bound p rho e -> (* function names in p/rho not bound in e *)
      forall (stm : statement) (lenv : temp_env) (m : mem) (k : cont) (max_alloc : Z) (fu : function),
        repr_expr_LambdaANF_Codegen_id fenv finfo_env p rep_env e stm -> (* translate_body e returns stm *)
        rel_mem_LambdaANF_Codegen_id fenv finfo_env p rep_env e rho m lenv ->
        (* " relates a LambdaANF evaluation environment [rho] to a Clight memory [m/lenv] up to the free variables in e " *)
        (* also says fundefs in e are correct in m *)
        (* NOTE: this is only place pertaining to outside of the body, and can likely incorporate free variables here *)
        correct_alloc e max_alloc ->  (* max_alloc correct *)
        correct_tinfo p max_alloc lenv m -> (* thread_info correct *)
        exists (m' : mem) (lenv' : temp_env),
          m_tstep2 (globalenv p) (State fu stm k empty_env lenv m) (State fu Sskip k empty_env lenv' m') /\
          (* memory m/lenv becomes m'/lenv' after executing stm *)
          same_args_ptr lenv lenv' /\
          arg_val_LambdaANF_Codegen fenv finfo_env p rep_env v m' lenv'. (* value v is related to memory m'/lenv' *)
Proof.
  intros p rep_env cenv fenv finfo_env ienv Hpinv Hsym HfinfoCorrect rho v e n Hev.
  induction Hev; intros Hc_env Hp_id Hrho_id Hf_id stm lenv m k max_alloc fu Hrepr_e Hrel_m Hc_alloc Hc_tinfo; inv Hrepr_e.
  - (* Econstr *)

    assert (Hx_not:  ~ is_protected_id_thm  x). {
          intro. inv Hp_id. eapply H2; eauto.
    }


    (* get the tempenv and mem after assigning the constructor *)
    assert (exists lenv' m',
               ( clos_trans state (traceless_step2 (globalenv p))
                                     (State fu s (Kseq s' k) empty_env lenv m)
                                     (State fu Sskip (Kseq s' k) empty_env lenv' m') )
               /\  rel_mem_LambdaANF_Codegen_id fenv finfo_env p rep_env e (M.set x (Vconstr t vs) rho) m' lenv'
               /\ correct_tinfo p (Z.of_nat (max_allocs e)) lenv' m' /\
                   same_args_ptr lenv lenv').
    {
      inv H6.
      - (* boxed *)

        assert (Ha_l : a = N.of_nat (length ys) /\ ys <> []). {
          assert (subterm_or_eq (Econstr x t ys e) (Econstr x t ys e)) by constructor 2.
          inv Hc_env. destruct H5 as [H5' H5]. destruct H5 as [H5 H6].
          apply H5 in H3.   destruct (M.get t cenv) eqn:Hmc. destruct c0. inv H6.
          apply H9 in H0. inv H0. rewrite H10 in Hmc. inv Hmc.
          split; auto. destruct ys. inv H2. intro. inv H0. inv H3.
        }


        (* 1 -> get the alloc info, steps through the assignment of the header *)
        assert (Hc_tinfo' := Hc_tinfo).
        unfold correct_tinfo in Hc_tinfo.
        destruct Hc_tinfo as [alloc_b [alloc_ofs [limit_ofs [args_b [args_ofs [tinf_b [tinf_ofs [Hget_alloc [Halign_alloc [Hrange_alloc [Hget_limit [Hbound_limit [Hget_args [Hdj_args [Hbound_args [Hrange_args [Htinf1 [Htinf2 [Htinf3 [Hinf_limit [Htinf_deref Hglobals]]]]]]]]]]]]]]]]]]]]].

        assert (~ is_protected_id_thm x).
        { intro. inv Hp_id. eapply H5; eauto. }

        assert (Hx_loc_eq : (Ptrofs.add (Ptrofs.add alloc_ofs (Ptrofs.mul (Ptrofs.repr int_size) (Ptrofs.repr Z.one))) (Ptrofs.mul (Ptrofs.repr int_size) (Ptrofs.repr (-1)))) = alloc_ofs). {
          rewrite Ptrofs.add_assoc.
          rewrite Ptrofs.mul_mone.
          rewrite Ptrofs.mul_one.
          rewrite Ptrofs.add_neg_zero.
          apply Ptrofs.add_zero.
        }


        assert ( {m2 : mem |  Mem.store int_chunk m alloc_b
                                      (Ptrofs.unsigned alloc_ofs) (make_vint h) = Some m2}). {
          apply Mem.valid_access_store.
          split.
          intro.
          intro. apply Hrange_alloc.
          unfold int_size in *.
          simpl size_chunk in *.
          inv H4.
          split; auto.
          eapply OrdersEx.Z_as_OT.lt_le_trans. eauto.
          inv Hbound_limit.
          inv Hc_alloc. simpl max_allocs. destruct ys. exfalso; inv Ha_l; auto. simpl max_allocs in H4.
          rewrite Nat2Z.inj_succ in H4. chunk_red; omega.
          auto.
        }
        destruct X as [m2 Hm2].

        assert (Hstep_m2 : clos_trans state (traceless_step2 (globalenv p))
                            (State fu
         (Ssequence
            (Ssequence
               (Ssequence
                  (Sset x
                     (Ecast
                        (add (Etempvar allocIdent (Tpointer val {| attr_volatile := false; attr_alignas := None |}))
                           (c_int' Z.one val)) val))
                  (Sset allocIdent
                     (add (Etempvar allocIdent (Tpointer val {| attr_volatile := false; attr_alignas := None |}))
                        (c_int' (Z.of_N (a + 1)) val))))
               (Sassign
                  (Ederef
                     (add (Ecast (Etempvar x val) (Tpointer val {| attr_volatile := false; attr_alignas := None |}))
                          (c_int' (-1)%Z val)) val) (c_int' h val))) s0) (Kseq s' k) empty_env lenv m)
                           (State fu s0 (Kseq s' k) empty_env
       (Maps.PTree.set allocIdent
          (Vptr alloc_b (Ptrofs.add alloc_ofs (Ptrofs.mul (Ptrofs.repr (sizeof (globalenv p) val)) (Ptrofs.repr (Z.of_N (a + 1))))))
          (Maps.PTree.set x
             (Vptr alloc_b (Ptrofs.add alloc_ofs (Ptrofs.mul (Ptrofs.repr (sizeof (globalenv p) val)) (Ptrofs.repr Z.one)))) lenv)) m2)).
        {
          eapply t_trans. constructor. constructor.
          eapply t_trans. constructor. constructor.
          eapply t_trans. constructor. constructor.
          chunk_red; archi_red.
          (* branch ptr64 *)

          {
            eapply t_trans. constructor. constructor. econstructor.
            econstructor. constructor. eauto. constructor. constructor.
            constructor.
            eapply t_trans. constructor. constructor.

            eapply t_trans. constructor. constructor.
            econstructor. constructor. rewrite M.gso.
            eauto. intro. apply H3. rewrite <- H4. inList.
            constructor. constructor.
            eapply t_trans. constructor. constructor.
            eapply t_trans. constructor. econstructor. constructor. simpl. econstructor.
            econstructor. constructor. rewrite M.gso. rewrite M.gss. reflexivity.
            intro. apply H3. rewrite  H4. inList.
            constructor. econstructor. constructor. constructor. constructor. simpl.
            econstructor. econstructor.  simpl.  unfold Ptrofs.of_int64. rewrite ptrofs_of_int64. rewrite ptrofs_of_int64.
            rewrite Hx_loc_eq. eauto.
            constructor. unfold Ptrofs.of_int64. do 2 (rewrite ptrofs_of_int64).
            constructor.
          }
          {
            archi_red.
            eapply t_trans. constructor. constructor. econstructor.
            econstructor. constructor. eauto. constructor. constructor.
            unfold sem_cast. simpl; archi_red.  constructor.

            eapply t_trans. constructor. constructor.

            eapply t_trans. constructor. constructor.
            econstructor. constructor. rewrite M.gso.
            eauto. intro. apply H3. rewrite <- H4. inList.
            constructor. constructor.
            eapply t_trans. constructor. constructor.
            archi_red.
            eapply t_trans. constructor. econstructor. constructor. simpl. econstructor.
            econstructor. constructor. rewrite M.gso. rewrite M.gss. reflexivity.
            intro. apply H3. rewrite  H4. inList.
            unfold sem_cast; simpl; archi_red. constructor.
            constructor. simpl.  unfold Ptrofs.of_intu. unfold Ptrofs.of_int. rewrite ptrofs_of_int.
            unfold sval; archi_red. constructor. auto.
            econstructor. constructor. simpl. econstructor. constructor.
            unfold Ptrofs.of_intu. unfold Ptrofs.of_int. rewrite ptrofs_of_int.
            rewrite Hx_loc_eq. eauto. auto.
            constructor.
            unfold Ptrofs.of_intu. unfold Ptrofs.of_int. rewrite ptrofs_of_int.
            unfold Cop.ptrofs_of_int.             unfold Ptrofs.of_intu. unfold Ptrofs.of_int. rewrite ptrofs_of_int.
            constructor.
            auto. auto.
          } }


        (* 2 -> use mem_of_Forall_nth_projection to step through the assignment of vs *)
        assert (Hstep_m3 := mem_of_Forall_nth_projection_cast).
        specialize (Hstep_m3 threadInfIdent nParam fenv finfo_env p x
                             (Maps.PTree.set allocIdent
                                             (Vptr alloc_b
                                                   (Ptrofs.add alloc_ofs (Ptrofs.mul (Ptrofs.repr (sizeof (globalenv p) val)) (Ptrofs.repr (Z.of_N (a + 1))))))
                                             (Maps.PTree.set x
                                                             (Vptr alloc_b (Ptrofs.add alloc_ofs (Ptrofs.mul (Ptrofs.repr (sizeof (globalenv p) val)) (Ptrofs.repr Z.one))))
                                                             lenv))
                             alloc_b
                             (Ptrofs.add alloc_ofs (Ptrofs.mul (Ptrofs.repr (sizeof (globalenv p) val)) (Ptrofs.repr Z.one)))
                             fu
                   ).
        assert (Htemp :  M.get x
               (Maps.PTree.set allocIdent
                  (Vptr alloc_b
                     (Ptrofs.add alloc_ofs (Ptrofs.mul (Ptrofs.repr (sizeof (globalenv p) val)) (Ptrofs.repr (Z.of_N (a + 1))))))
                  (Maps.PTree.set x
                     (Vptr alloc_b (Ptrofs.add alloc_ofs (Ptrofs.mul (Ptrofs.repr (sizeof (globalenv p) val)) (Ptrofs.repr Z.one)))) lenv)) =
             Some (Vptr alloc_b (Ptrofs.add alloc_ofs (Ptrofs.mul (Ptrofs.repr (sizeof (globalenv p) val)) (Ptrofs.repr Z.one))))).
        rewrite M.gso. rewrite M.gss. reflexivity. intro; apply Hx_not. rewrite H4. inList.
        specialize (Hstep_m3 Hsym HfinfoCorrect Htemp ys s0 0%Z m2 (Kseq s' k)). clear Htemp.
        assert (Htemp : (0 <= 0)%Z /\ (0 + Z.of_nat (length ys) <= Ptrofs.max_unsigned)%Z ).
        {
          split. omega.
          assert (Ptrofs.unsigned limit_ofs <= Ptrofs.max_unsigned)%Z.
          assert (Htemp := Ptrofs.unsigned_range_2 limit_ofs). omega.
          assert (int_size * max_alloc <= gc_size)%Z by omega.
          chunk_red; archi_red.

          inv Hc_alloc; destruct ys; inv H2.
          simpl. unfold Int64.max_unsigned. simpl. omega.
          simpl max_allocs in H5.
          rewrite Nat2Z.inj_succ in H5.
          rewrite Nat2Z.inj_add in H5.
          simpl length.
          etransitivity. etransitivity.
          2:apply H5. omega.
          unfold gc_size. simpl. unfold Int64.max_unsigned. simpl. omega.


          inv Hc_alloc; destruct ys; inv H2.
          simpl. unfold Int.max_unsigned. simpl. omega.
          simpl max_allocs in H5.
          rewrite Nat2Z.inj_succ in H5.
          rewrite Nat2Z.inj_add in H5.
          simpl length.
          etransitivity. etransitivity.
          2:apply H5. omega.
          unfold gc_size. simpl. unfold Int.max_unsigned. simpl. omega.

        }

        specialize (Hstep_m3 Htemp). clear Htemp.
        assert (Htemp : (forall j : Z,
              (0 <= j < 0 + Z.of_nat (length ys))%Z ->
              Mem.valid_access m2 int_chunk alloc_b
                (Ptrofs.unsigned
                   (Ptrofs.add (Ptrofs.add alloc_ofs (Ptrofs.mul (Ptrofs.repr (sizeof (globalenv p) val)) (Ptrofs.repr Z.one)))
                            (Ptrofs.repr (int_size * j)))) Writable)). {


          intros.

          (* BACK specialize (Hrange_alloc (j+1)%Z). *)

          inv Hc_alloc.  destruct ys. inv H2.
          assert ((0 <= j + 1 <  Z.of_nat (max_allocs (Econstr x t (v0 :: ys) e)))%Z).
          simpl. simpl in H4.
          rewrite Zpos_P_of_succ_nat.
          rewrite Nat2Z.inj_add.
          rewrite Zpos_P_of_succ_nat in H4.
          rewrite Nat2Z.inj_succ. omega.
          replace ((Ptrofs.add (Ptrofs.add alloc_ofs (Ptrofs.mul (Ptrofs.repr (sizeof (globalenv p) val)) (Ptrofs.repr Z.one))) (Ptrofs.repr (int_size * j)))) with (Ptrofs.add alloc_ofs (Ptrofs.repr (int_size * (j + 1)))).

          eapply Mem.store_valid_access_1; eauto.
          replace (Ptrofs.unsigned (Ptrofs.add alloc_ofs (Ptrofs.repr (int_size * (j + 1))))) with
                   (Ptrofs.unsigned alloc_ofs + int_size * (j+1))%Z.
          eapply range_perm_to_valid_access.
          eapply Hrange_alloc.
          eapply OrdersEx.Z_as_DT.divide_add_r.
          auto.
          unfold int_size.
          eapply OrdersEx.Z_as_DT.divide_factor_l.
          unfold int_size. chunk_red; omega.
          inv Hbound_limit.
          unfold int_size in *. chunk_red; omega.

          symmetry.
          apply  pointer_ofs_no_overflow.
          omega.
          destruct Hbound_limit.
          unfold int_size in *.
          assert (Ptrofs.unsigned limit_ofs <= Ptrofs.max_unsigned)%Z by apply Ptrofs.unsigned_range_2.

          chunk_red; omega.

          rewrite Ptrofs.add_assoc.
          replace (Ptrofs.add (Ptrofs.mul (Ptrofs.repr (sizeof (globalenv p) val)) (Ptrofs.repr Z.one))
                           (Ptrofs.repr (int_size * j))) with (Ptrofs.repr (int_size * (j + 1))). reflexivity.
          rewrite int_z_mul.
          rewrite int_z_add.
          rewrite Zred_factor4.
          rewrite Z.add_comm. reflexivity.
          constructor. solve_uint_range.
          constructor. unfold uval. chunk_red; archi_red; simpl; omega.
          rewrite ptrofs_mu. chunk_red; archi_red; simpl; solve_uint_range. omega. omega.
          solve_uint_range.

          destruct Hbound_limit.


          assert (gc_size <= Int.max_unsigned)%Z. unfold gc_size; unfold Int.max_unsigned; simpl; omega.
          split. chunk_red; omega.
          etransitivity. 2: apply ptrofs_mu_weak.
          assert ((int_size * j <= int_size * Z.pos (Pos.of_succ_nat (length ys))))%Z.
          apply OrdersEx.Z_as_OT.mul_le_mono_pos_l. chunk_red; omega. omega.
          etransitivity.
          eauto.
          etransitivity. 2: eauto. etransitivity. 2:eauto.
          etransitivity. 2: eauto.
          do 2 (rewrite Zpos_P_of_succ_nat).
          rewrite Nat2Z.inj_add.
          rewrite Nat2Z.inj_succ.
          rewrite <- Z.add_succ_l.
          assert (0 <= (Z.succ (Z.of_nat (max_allocs e))))%Z.
          assert (0 <= (Z.of_nat (max_allocs e)))%Z.  omega. omega.
          rewrite Z.mul_add_distr_l.
          chunk_red; archi_red; omega.

          chunk_red; archi_red; solve_uint_range; rewrite ptrofs_mu; archi_red; solve_uint_range; unfold Z.one; omega.
        }
        specialize (Hstep_m3 Htemp H2). clear Htemp.

        (* first prove that allocIdent \/ x is disjoint from ys s.t. can be ignore. then show that get_list works and that vs7 is the right thing  *)
        assert (Htemp : exists vs : list Values.val,
             Forall2
               (get_var_or_funvar p
                  (Maps.PTree.set allocIdent
                     (Vptr alloc_b
                        (Ptrofs.add alloc_ofs (Ptrofs.mul (Ptrofs.repr (sizeof (globalenv p) val)) (Ptrofs.repr (Z.of_N (a + 1))))))
                     (Maps.PTree.set x
                        (Vptr alloc_b (Ptrofs.add alloc_ofs (Ptrofs.mul (Ptrofs.repr (sizeof (globalenv p) val)) (Ptrofs.repr Z.one))))
                        lenv))) ys vs).
        {
          assert (exists vs, get_var_or_funvar_list p lenv ys = Some vs).
          {

            inv Hrel_m.  destruct H4.
            eapply exists_getvar_or_funvar_list.
            2:{  eauto. }
            intros.
            apply H5. constructor. auto.
          }
          destruct H4 as [x0 Hgv_x0].
          exists x0.
          rewrite get_var_or_funvar_list_correct.
          rewrite <- get_var_or_funvar_list_set.
          rewrite <- get_var_or_funvar_list_set.
          auto.

          intro.
          eassert (Hxrho := get_list_In _ _ _ _ H H4).
          destruct Hxrho as [vv Hxrho].
          eapply Hrho_id; eauto.


          intro.
          inv Hp_id.

          assert (Hgl := get_list_In _ _ _ _ H H4). destruct Hgl.
          specialize (H5 _ allocIdent _ H8). apply H5.
          right.
          left. auto. left; auto.
        }
        destruct Htemp as [vs7 Hvs7].
        specialize (Hstep_m3 vs7 Hvs7).
        destruct Hstep_m3 as [m3 Hstep_m3].
        assert (H_m2_m3 :  mem_after_n_proj_store alloc_b
                                                       (Ptrofs.unsigned (Ptrofs.add alloc_ofs (Ptrofs.mul (Ptrofs.repr (sizeof (globalenv p) val)) (Ptrofs.repr Z.one)))) vs7 0 m2 m3). {
          apply mem_after_n_proj_wo_cast.
          destruct Hstep_m3; auto.
          apply Ptrofs.unsigned_range. reflexivity.
          inv Hc_alloc.
          int_red. simpl max_allocs in Hbound_limit. destruct ys. destruct Ha_l. exfalso. auto.
          rewrite Nat2Z.inj_succ in Hbound_limit.
          rewrite Nat2Z.inj_add in Hbound_limit.

          split.
          apply Z.add_nonneg_nonneg.
          apply Ptrofs.unsigned_range.
          assert (0 <= Z.of_nat (length vs7))%Z by apply Zle_0_nat. chunk_red; omega.
          apply Forall2_length' in Hvs7.
          rewrite <- Hvs7 in *.
          inv Hbound_limit.
          rewrite int_z_mul.
          unfold Ptrofs.add.
          rewrite Ptrofs.unsigned_repr with (z := (sizeof (globalenv p) uval * Z.one)%Z).
          rewrite Ptrofs.unsigned_repr.

          unfold Z.one.
          rewrite Z.mul_succ_r in H4.



          assert (Ptrofs.unsigned alloc_ofs + sizeof (globalenv p) uval * 1 +  size_chunk int_chunk * (0 + Z.of_nat (length (v0 :: ys))) <= Ptrofs.unsigned alloc_ofs + (Ptrofs.unsigned limit_ofs - Ptrofs.unsigned alloc_ofs))%Z. chunk_red; unfold sizeof; archi_red; omega. etransitivity. eauto.
          rewrite Zplus_minus. apply Ptrofs.unsigned_range_2.
          unfold Z.one.
          rewrite Z.mul_succ_r in H4.
          assert (0 <= Ptrofs.unsigned alloc_ofs)%Z by apply Ptrofs.unsigned_range_2. split. chunk_red; unfold sizeof; archi_red; omega.
          assert (Ptrofs.unsigned alloc_ofs +  sizeof (globalenv p) uval * 1 <= Ptrofs.unsigned alloc_ofs + ( Ptrofs.unsigned limit_ofs - Ptrofs.unsigned alloc_ofs))%Z by (chunk_red; unfold sizeof; archi_red; omega).
          etransitivity. eauto.
          rewrite Zplus_minus. apply Ptrofs.unsigned_range_2.

          unfold Z.one; rewrite ptrofs_mu.  chunk_red; unfold sizeof; archi_red; solve_uint_range; omega.
          simpl sizeof. unfold Z.one. chunk_red; unfold sizeof; solve_uint_range; rewrite ptrofs_mu; archi_red; solve_uint_range; omega.
          destruct Hstep_m3.
          auto.
        }
        assert (H_ug1 :unchanged_globals p m m2). {
          intro.
          intros. symmetry.
          eapply Mem.load_store_other.
          eauto.
          left.
          inv Hrel_m. destructAll. inv H5. destructAll.
          apply H19 in H4. destructAll. rewrite H5 in Hget_alloc; inv Hget_alloc. auto.
        }
        assert (H_ug2 : unchanged_globals p m2 m3). {
          inv Hrel_m. destructAll. inv H4.
          destructAll.
          eapply mem_after_n_proj_store_globals_unchanged. eauto.
          intros.
          apply H18 in H19. rewrite H4 in Hget_alloc; inv Hget_alloc. destructAll; auto.
        }



        do 2 eexists.
        split.
        eapply t_trans.

        apply Hstep_m2.
        apply Hstep_m3.
        split.
        { (* rel_mem after adding the new constructor *)
          inversion Hrel_m as [L [Hrel_pL Hrel_mL]].
          assert (Hbound_max:
                    (Ptrofs.unsigned alloc_ofs + int_size * (Z.succ (Z.of_nat (max_allocs e)) + Z.of_N a) <= Ptrofs.unsigned limit_ofs)%Z). {
            inv Hc_alloc.
            simpl max_allocs in Hbound_limit.
            destruct ys. exfalso.
            destruct Ha_l. auto.

            rewrite Nat2Z.inj_succ in Hbound_limit.
            rewrite Nat2Z.inj_add in Hbound_limit.
            destruct Ha_l.

            replace (Z.of_N a) with (Z.of_nat (length (v0 :: ys))).
            rewrite  Z.add_succ_l.
            destruct Hbound_limit.
            omega.
            rewrite H4. rewrite nat_N_Z. reflexivity.
          }
          assert (H_unchanged_m2_m3: Mem.unchanged_on L m2 m3). {
            inv Hrel_pL.
            destructAll.
            rewrite H4 in Hget_alloc. inv Hget_alloc.

            eapply mem_after_n_proj_store_unchanged.
            eauto.
            intros.
            apply H12.
            simpl max_allocs in *.
            apply Forall2_length' in Hvs7.
            rewrite <- Hvs7 in *.
            clear Hvs7.

            destruct ys.
            exfalso; auto.
            rewrite Hget_limit in H13; inv H13.


            simpl length in H8. unfold int_size in *; simpl size_chunk in *.
            simpl sizeof in *.
            simpl length in Hbound_max.
            rewrite int_z_mul in H8.
            rewrite pointer_ofs_no_overflow in H8.
            inv Hc_alloc. simpl max_allocs in H10.
            rewrite Nat2Z.inj_succ in *.
            unfold int_size in *;  simpl size_chunk in *.
            unfold Z.one in *. split. chunk_red; omega.
            inv H8.
            eapply OrdersEx.Z_as_OT.lt_le_trans; eauto.
            rewrite Nat2Z.inj_add in H10.
            rewrite Z.mul_succ_r in H10.
            assert (0 <= Z.of_nat (max_allocs e))%Z by apply Zle_0_nat.
            rewrite <- OrdersEx.Z_as_DT.le_add_le_sub_l in H10.
            etransitivity. 2: apply H10.
            rewrite Nat2Z.inj_succ.

            rewrite Z.add_0_l.
            rewrite Z.mul_add_distr_l.
            repeat (rewrite Z.mul_succ_r).
            repeat rewrite Z.add_assoc.
            rewrite Z.add_comm with (m := (size_chunk int_chunk * Z.of_nat (max_allocs e))%Z).
            repeat rewrite <- Z.add_assoc.
            apply Z_non_neg_add.
            assert (Ptrofs.unsigned alloc_ofs + (size_chunk int_chunk * 1 + ((size_chunk int_chunk) * Z.of_nat (length ys) + (size_chunk int_chunk))) <= (Ptrofs.unsigned alloc_ofs + ((size_chunk int_chunk) * Z.of_nat (length ys) + ((size_chunk int_chunk) + (size_chunk int_chunk)))))%Z. chunk_red; omega. etransitivity. eauto. reflexivity. chunk_red; omega.
            unfold Z.one; omega.
            inv Hc_alloc. simpl max_allocs in H10.
            rewrite Nat2Z.inj_succ in H10.
            rewrite <- Z.le_add_le_sub_l in H10.
            etransitivity.
            etransitivity.
            2: apply H10.
            unfold Z.one. rewrite Nat2Z.inj_add.
            rewrite Nat2Z.inj_succ. chunk_red; omega.
            apply Ptrofs.unsigned_range_2.

            unfold Z.one.
            solve_uint_range; rewrite ptrofs_mu; chunk_red; archi_red; solve_uint_range; omega.

          }
          assert (H_unchanged_m_m3:   Mem.unchanged_on L m m3). {

            inv Hrel_pL.
            destructAll.
            rewrite H4 in Hget_alloc. inv Hget_alloc.

            eapply Mem.unchanged_on_trans.
            eapply Mem.store_unchanged_on.

            eauto.
            intros.
            apply H12.
            inv H8.
            split; auto.
            rewrite H13 in Hget_limit; inv Hget_limit.
            eapply OrdersEx.Z_as_OT.lt_le_trans. eauto.
            rewrite <- Z.le_add_le_sub_l in H10.
            etransitivity; eauto.
            apply Zplus_le_compat_l.
            rewrite Z.mul_add_distr_l.
            rewrite Z.mul_succ_r. repeat rewrite  Z.add_assoc.
            rewrite OrdersEx.Z_as_OT.add_shuffle0.
            apply Z_non_neg_add.
            reflexivity.
            rewrite nat_N_Z.
            chunk_red; omega.
            auto.
              }

          exists (bind_n_after_ptr (Z.of_N (a+1) * int_size) alloc_b (Ptrofs.unsigned alloc_ofs)  L).
          split.
          - (* protected okay since only took the space from Econstr to e *)
            exists alloc_b, (Ptrofs.add alloc_ofs (Ptrofs.mul (Ptrofs.repr (sizeof (globalenv p) val)) (Ptrofs.repr (Z.of_N (a + 1))))),
            limit_ofs, args_b, args_ofs, tinf_b, tinf_ofs.
            assert (H_dj := disjointIdent).
            repeat split.
            + rewrite M.gss. reflexivity.
            + intros.
              inv Hrel_pL.
              destructAll.
              inv Hc_alloc.
              destruct ys. exfalso; auto.
              simpl max_allocs in *.
              int_red.
              rewrite Nat2Z.inj_succ in H12.
              rewrite Nat2Z.inj_add in H12.
              rewrite H5 in Hget_alloc. inv Hget_alloc.
              rewrite H15 in Hget_limit. inv Hget_limit.
              intro.
              apply bind_n_after_ptr_def in H10.
              rewrite Ptrofs.add_unsigned with (x := alloc_ofs) in * .
              replace (Ptrofs.unsigned
                         (Ptrofs.mul (Ptrofs.repr (sizeof (globalenv p) val)) (Ptrofs.repr (Z.of_N (N.of_nat (@length var (v0 :: ys)) + 1))))) with
                  ((size_chunk int_chunk) * Z.of_nat (length (v0 :: ys)) + (size_chunk int_chunk))%Z in *.
              unfold Ptrofs.add in H6.
              replace  (Ptrofs.unsigned (Ptrofs.repr ((size_chunk int_chunk) * Z.of_nat (max_allocs e)))) with
                  ((size_chunk int_chunk) * Z.of_nat (max_allocs e))%Z in *.
              replace (Ptrofs.unsigned (Ptrofs.repr (Ptrofs.unsigned alloc_ofs + ((size_chunk int_chunk) * Z.of_nat (length (v0 :: ys)) + (size_chunk int_chunk))))) with
                  (Ptrofs.unsigned alloc_ofs + ((size_chunk int_chunk) * Z.of_nat (length (v0 :: ys)) + (size_chunk int_chunk)))%Z in *.
              inv H10.
              * revert H21.
                eapply H14.
                split; auto.
                etransitivity; eauto; chunk_red; omega.
              * inv H21.

                rewrite N2Z.inj_add in H22.
                rewrite nat_N_Z in H22.
                simpl Z.of_N in *.
                chunk_red; omega.

              * assert (0 <= Ptrofs.unsigned alloc_ofs)%Z by apply Ptrofs.unsigned_range.
                rewrite Ptrofs.unsigned_repr. reflexivity.
                split. chunk_red; omega.
                rewrite <- Z.le_add_le_sub_l in H12.
                etransitivity. etransitivity.
                2: apply H12.
                rewrite Z.mul_succ_r.
                simpl length.
                chunk_red; omega.
                apply Ptrofs.unsigned_range_2.
              * rewrite Ptrofs.unsigned_repr. reflexivity.
                split. chunk_red; omega.
                rewrite <- Z.le_add_le_sub_l in H12.
                etransitivity. etransitivity.
                2: apply H12.
                rewrite Nat2Z.inj_succ.
                rewrite Z.mul_succ_r.
                assert (0 <= Ptrofs.unsigned alloc_ofs)%Z by apply Ptrofs.unsigned_range.
                chunk_red; omega.
                apply Ptrofs.unsigned_range_2.
              * simpl sizeof.
                unfold Ptrofs.mul.
                rewrite Ptrofs.unsigned_repr with (z :=  (Z.of_N (N.of_nat (length (v0 :: ys)) + 1))).
                rewrite Ptrofs.unsigned_repr with (z := (sizeof (prog_comp_env p) uval)).
                rewrite Ptrofs.unsigned_repr. reflexivity.
                split. apply Z.mul_nonneg_nonneg. unfold sizeof. chunk_red; archi_red; omega.
                apply N2Z.is_nonneg.
                rewrite <- Z.le_add_le_sub_l in H12.
                etransitivity. etransitivity. 2: apply H12.  simpl length.
                assert (0 <= Ptrofs.unsigned alloc_ofs)%Z by apply Ptrofs.unsigned_range.
                rewrite Z.mul_succ_r.
                rewrite N2Z.inj_add.
                rewrite nat_N_Z.
                simpl Z.of_N.
                rewrite Z.mul_add_distr_l.
                rewrite Z.mul_add_distr_l. unfold sizeof. chunk_red; archi_red; omega.
                apply Ptrofs.unsigned_range_2.
                rewrite ptrofs_mu.
                unfold sizeof; chunk_red; archi_red; solve_uint_range; omega.
                rewrite N2Z.inj_add.
                rewrite nat_N_Z.
                simpl Z.of_N.
                split.
                apply Z_non_neg_add. omega. omega.
                rewrite <- Z.le_add_le_sub_l in H12.
                etransitivity. etransitivity. 2: apply H12.
                simpl length.
                rewrite Z.mul_succ_r.
                assert (0 <= Ptrofs.unsigned alloc_ofs)%Z by apply Ptrofs.unsigned_range.
                chunk_red; omega.
                apply Ptrofs.unsigned_range_2.
            + rewrite M.gso. rewrite M.gso.
              auto.
              intro.
              apply H3.
              subst. rewrite <- H4. inList.
              intro. inv H_dj. rewrite <- H4 in *.
              inv H9.
              apply H10. constructor; auto.
            + rewrite M.gso. rewrite M.gso.
              auto. intro.
              apply H3. rewrite <- H4.  inList.
              intro; inv H_dj. apply H8. left. auto.
            + intros.
              inv Hrel_pL.
              destructAll.
              rewrite H18 in Hget_args; inv Hget_args.
              intro.
              apply bind_n_after_ptr_def in H12. inv H12.
              revert H23. apply H19 with (z := z); auto.
              destruct H23.
              apply Hdj_args.
              auto.
            + rewrite M.gso. rewrite M.gso.
              eauto. intro. apply H3.  unfold is_protected_id_thm; subst; inList.
              intro. inv H_dj. inversion H9. apply H10. inList.
            + intros; inv Hrel_pL; destructAll.
              rewrite H16 in Htinf1; inv Htinf1.
(*              apply H15 in H4. destructAll.  *)
              specialize (H17 i). intro.
              (* either b i is in L OR b = alloc_b  -> FALSE *)
              apply bind_n_after_ptr_def in H8.               inv H8.
              apply H17; auto.
              destruct H19. subst. rewrite H4 in Hget_alloc; inv Hget_alloc. apply Htinf3; reflexivity.
            + intros; inv Hrel_pL; destructAll.
              apply H19 in H4. rewrite H15 in Hget_args; inv Hget_args.
              destructAll; auto.
            + intros; inv Hrel_pL; destructAll.
              apply H19 in H4. rewrite H5 in Hget_alloc; inv Hget_alloc.
              destructAll; auto.
            + intros; inv Hrel_pL; destructAll.
              apply H19 in H4. destructAll.
              intro. apply bind_n_after_ptr_def in H21.
              inv H21.
              eapply H20; eauto.
              rewrite H5 in Hget_alloc; inv Hget_alloc.
              inv H22. apply H9; auto.
          - intros. destruct (var_dec x0 x).
                 + (* x0 = x *)
                   subst. split.
                   2:{
                     intros. rewrite M.gss in H4. inv H4.
                     apply subval_or_eq_fun in H5. destruct H5. destruct H4.
                     assert (Hy0x0 := get_list_In_val _ _ _ _ H H5).
                     destruct Hy0x0 as [y0 [Hy0In Hy0x0]].
                     specialize (Hrel_mL y0).
                     destruct Hrel_mL as [Hrem_mL Hrel_mL'].
                     specialize (Hrel_mL' _ _ _ _ Hy0x0 H4).
                     destruct Hrel_mL' as [Hrel_mL' [Hrel_closed Hrel_f]]. split.
                     eapply repr_val_id_L_sub_locProp.
                     eapply repr_val_id_L_unchanged.
                     2: eauto.
                     2:{ intro. intro. intro. apply bind_n_after_ptr_def. left; auto. }
                     apply repr_val_id_set. apply repr_val_id_set.
                     auto.
                     (* unique binding env should take care of this one? ...also since function not bound, but Hrel_mL'...*)
                     intro; subst. inv Hrho_id.
                     inv Hf_id.
                     assert (bound_var (Econstr x t ys e) x) by constructor.
                     apply H9 in H11.
                     inv Hrel_mL'. rewrite H19 in H11. inv H11.
                     inv H14. rewrite H22 in H11. inv H11.

                     (* since fds includes f *)
                     intro. inv Hp_id. eapply H8.
                     apply Hy0x0.
                     right. left. reflexivity.
                     right.
                     eapply bound_var_subval; eauto.
                     inv Hrel_mL'.
                     inv H17.
                     constructor.
                     apply name_in_fundefs_bound_var_fundefs.
                     eapply find_def_name_in_fundefs. eauto.
                     inv H11. rewrite H19 in H6. inv H6. split. auto.

                     eapply correct_fundefs_unchanged_global with (m := m2).
                     eapply correct_fundefs_unchanged_global with (m := m).
                     apply Hrel_f.
                     auto.
                     auto. }

                   intros. eexists. split.
                   rewrite M.gss. reflexivity.
                   eapply RVid_V.
                   apply Hf_id. constructor. (* x is not global *)
                   rewrite M.gso. rewrite M.gss. reflexivity.
                   intro. apply H3. subst. inList.
                   eapply RSconstr_boxed_v.
                   *  eauto.
                   *  rewrite Ptrofs.sub_add_opp.
                      rewrite Ptrofs.mul_one.
                      rewrite Ptrofs.add_assoc.
                      rewrite Ptrofs.add_neg_zero.
                      rewrite Ptrofs.add_zero. intros.
                      rewrite bind_n_after_ptr_def. right. split; auto.
                      simpl size_chunk in *.
                      rewrite N2Z.inj_add.
                      simpl Z.of_N.
                      rewrite Z.mul_add_distr_r.
                      rewrite Z.add_assoc.
                      simpl Z.mul.
                      assert (0 <=  Z.of_N a)%Z by apply N2Z.is_nonneg.
                      chunk_red; omega.
                   * (* skip m3, (repr H) is what is stored for m2 *)
                     rewrite Ptrofs.sub_add_opp.
                     rewrite Ptrofs.mul_one.
                     rewrite Ptrofs.add_assoc.
                     rewrite Ptrofs.add_neg_zero.
                     rewrite Ptrofs.add_zero.
                     destruct Hstep_m3 as [Hstep_m3_s Hstep_m3_mem].
                     apply Mem.load_store_same in Hm2. simpl in Hm2.
                     erewrite mem_after_n_proj_store_load.
                     apply Hm2.
                     apply H_m2_m3.
                     right. left.
                     simpl.
                     rewrite Ptrofs.mul_one.
                     unfold Ptrofs.add.
                     rewrite Ptrofs.unsigned_repr with (z := (sizeof (prog_comp_env p) uval)).
                     rewrite Ptrofs.unsigned_repr.
                     unfold sizeof; unfold int_size; chunk_red; archi_red; omega.
                     split.
                     apply Z_non_neg_add.
                     unfold sizeof; chunk_red; archi_red; omega. apply Ptrofs.unsigned_range.
                     destruct Hbound_limit.
                     rewrite <- Z.le_add_le_sub_l in H5.
                     etransitivity. etransitivity.
                     2: apply H5.
                     inv Hc_alloc. simpl max_allocs.
                     destruct ys.  inv Ha_l. exfalso; auto.
                     rewrite Nat2Z.inj_succ.
                     rewrite Z.mul_succ_r.
                     int_red.
                     assert (0 <=  Z.of_nat (max_allocs e + length (v0 :: ys))%nat)%Z by       apply Zle_0_nat.
                     unfold sizeof; chunk_red; archi_red; omega.
                     apply Ptrofs.unsigned_range_2.
                     rewrite ptrofs_mu.
                     unfold sizeof; chunk_red; archi_red; solve_uint_range; omega.
                   *
                     auto.

                   * (* todo: theorem linking repr_val_ptr_list and mem_after_n_proj_store *)
                     (* need to clear a few things here before inducting on vs *)
                     { clear IHHev.
                       assert (H_alloc4 :(Ptrofs.unsigned (Ptrofs.add alloc_ofs (Ptrofs.mul (Ptrofs.repr (sizeof (globalenv p) val)) (Ptrofs.repr Z.one)))
                                          = (Ptrofs.unsigned alloc_ofs) + int_size)%Z).
                       {

                         rewrite Ptrofs.mul_one.
                         rewrite Ptrofs.add_unsigned.
                         rewrite Ptrofs.unsigned_repr with (z := (sizeof (globalenv p) uval)).
                         rewrite Ptrofs.unsigned_repr. auto.
                         inv Hc_alloc.
                         split. apply OrdersEx.Z_as_OT.add_nonneg_nonneg. apply Ptrofs.unsigned_range.  unfold sizeof; chunk_red; archi_red; omega.
                    inv Hbound_limit.
                    rewrite <- Z.le_add_le_sub_l in H5.
                    etransitivity. etransitivity. 2: apply H5. unfold int_size in *. 2: eapply Ptrofs.unsigned_range_2.
                    simpl max_allocs. destruct ys. exfalso. apply Ha_l. auto.
                    rewrite Nat2Z.inj_succ.
                    rewrite Z.mul_succ_r.
                    rewrite Z.add_assoc. unfold int_size; simpl size_chunk.
                    assert (0 <=  Ptrofs.unsigned alloc_ofs)%Z.
                    apply Ptrofs.unsigned_range.
                    assert (0 <= Z.of_nat (max_allocs e + length (v0 :: ys)))%Z by
                    apply Zle_0_nat.
                    unfold sizeof; chunk_red; archi_red; omega.
                    rewrite ptrofs_mu.
                    unfold sizeof; chunk_red; archi_red; solve_uint_range; omega.
                  }




                  rewrite repr_val_ptr_list_Z.
                  2:{
                  rewrite H_alloc4.
                    unfold int_size in *; simpl size_chunk in *.
                    inv Hc_alloc.
                    split. apply OrdersEx.Z_as_OT.add_nonneg_nonneg. apply OrdersEx.Z_as_OT.add_nonneg_nonneg.
                    apply Ptrofs.unsigned_range. chunk_red; omega.  chunk_red; omega.
                    inv Hbound_limit.
                    rewrite <- Z.le_add_le_sub_l in H5.
                    etransitivity. etransitivity. 2: apply H5. 2: apply Ptrofs.unsigned_range_2.
                    simpl max_allocs.
                    apply get_list_length_eq in H.
                    destruct ys. exfalso. apply Ha_l. auto.
                    rewrite Nat2Z.inj_succ.
                    rewrite Nat2Z.inj_add.
                    simpl length.
                    simpl in H. rewrite <- H.
                    rewrite Nat2Z.inj_succ.
                    rewrite Nat2Z.inj_succ.
                    assert (0 <=  Ptrofs.unsigned alloc_ofs)%Z by apply Ptrofs.unsigned_range.
                    rewrite Z.mul_succ_r.
                    rewrite Z.mul_add_distr_l.
                    rewrite Z.mul_succ_r.
                    rewrite Z.add_assoc.
                    assert (0 <= (Z.of_nat (length ys)))%Z by                     apply Zle_0_nat.
                    assert (0 <= (Z.of_nat (max_allocs e)))%Z by                     apply Zle_0_nat.
                    rewrite Z.mul_succ_l.
                    rewrite <- Z.add_assoc.
                    rewrite <- Z.add_assoc.
                    apply Zplus_le_compat_l.
                    rewrite Z.add_comm.
                    rewrite Z.add_assoc.
                    rewrite Z.mul_comm.
                    rewrite <- Z.add_0_l at 1.
                    replace  (int_size * Z.of_nat (max_allocs e) + int_size * Z.of_nat (length ys) + int_size + int_size)%Z with  (int_size * Z.of_nat (max_allocs e) + ( int_size * Z.of_nat (length ys) + int_size + int_size))%Z by omega.

                    rewrite Z.add_0_l;
                    apply Z.add_le_mono; [ | omega];
                    apply Z.add_le_mono; [ | omega];
                    rewrite <- Z.add_0_l at 1;
                    apply Z.add_le_mono_r; chunk_red; omega. }

                    (* done *)


                    rewrite H_alloc4.
                    rewrite H_alloc4 in H_m2_m3.
                  clear H_alloc4.








                  (* creating an intermediate memory representing the work done so far, with equality that will be cleared before induction *)
                  assert (H_mmid: exists m_mid vs1 vs2, mem_after_n_proj_snoc alloc_b (Ptrofs.unsigned alloc_ofs + int_size) vs1 m2 m_mid /\
                                                        (rev (vs1) ++ vs2 = vs7) /\ vs7 = vs2 /\ vs1 = [] /\  m2 = m_mid). {

                    exists m2, [], vs7. split. constructor.
                    auto.
                  }
                  destruct H_mmid as [m_mid [vs1 [vs2 [H_m2_mmid [H_rev_vs7 [H_eq_vs7 [H_eq_vs1 H_eq_m2]]]]]]].
                  rewrite H_eq_vs7 in H_m2_m3.
                  rewrite H_eq_m2 in H_m2_m3.
                  rewrite H_eq_vs7 in Hvs7.
                  replace 0%Z with (Z.of_nat (length vs1)) in H_m2_m3 by (rewrite H_eq_vs1; auto).








                  (* IH needs to walk on the total (a) size of ys *)
                  assert (Hays: (Z.of_N a - Z.of_nat (length ys) = 0)%Z).
                  destruct Ha_l; subst. rewrite nat_N_Z.
                  omega.


                  replace (Ptrofs.unsigned alloc_ofs + int_size)%Z with  (Ptrofs.unsigned alloc_ofs + int_size + int_size * Z.of_nat (length vs1))%Z by (rewrite H_eq_vs1; simpl; omega).

                  assert (Hrel_pL' := Hrel_pL).
(*   Not needed w/o maxalloc in pniL
               assert (Hrel_pL' :  protected_not_in_L argsIdent allocIdent limitIdent tinfIdent p lenv (Z.succ (Z.of_nat (max_allocs e)) + Z.of_nat (length vs7) )%Z L). {
                    simpl in Hrel_pL. destruct ys. exfalso; destruct Ha_l. apply H6; auto.
                    rewrite Nat2Z.inj_succ in Hrel_pL.
                    rewrite Nat2Z.inj_add in Hrel_pL.
                    replace (Z.of_nat (length vs7)) with (Z.of_nat (length (v0 :: ys))).
                    rewrite  Z.add_succ_l. auto.
                    rewrite H_eq_vs7.
                    apply Forall2_length' in Hvs7. rewrite <- Hvs7; auto.

                  } *)
                  assert (forall y, List.In y ys ->
                                    exists v6 : term.val,
              M.get y rho = Some v6 /\
              repr_val_id_L_LambdaANF_Codegen argsIdent allocIdent limitIdent gcIdent threadInfIdent tinfIdent isptrIdent caseIdent nParam fenv
                                  finfo_env p rep_env v6 m L lenv y).
                  intros. apply Hrel_mL. constructor. auto.

                  (* replacing bind_n_after_ptr to something easier to induct on *)
                  assert (Hll' := bind_n_after_ptr_exists  (length vs2) alloc_b (Ptrofs.unsigned alloc_ofs + int_size + int_size * Z.of_nat (length vs1)) L).
                  destruct Hll' as [L' [H_ll' H_eql']].
                  eapply  repr_val_ptr_list_L_Z_sub_locProp with (L := L'); auto.
                  2:{
                  intro. intro. intro. apply bind_n_after_ptr_def.
                  rewrite <- H_eql' in H6.
                  apply bind_n_after_ptr_def in H6.
                  inv H6. auto.
                  destruct H8. right. split. auto.
                  split. chunk_red; omega.
                  rewrite N2Z.inj_add.
                  replace (Z.of_N a) with (Z.of_nat (length ys)) by omega.
                  replace (length ys) with (length vs2). int_red. simpl in H8. simpl Z.of_N. chunk_red; omega.
                  apply Forall2_length' in Hvs7. auto. }

                  (* current locprop, from L + 1 to L + 1 + length vs *)
                  assert (H_ll'':= bind_n_after_ptr_exists' (length vs1) alloc_b  (Ptrofs.unsigned alloc_ofs + int_size) L).
                  destruct H_ll'' as [L'' H_ll''].

                  assert (H_not_in_L:
                            (forall j:Z,
                                (Ptrofs.unsigned alloc_ofs  <= j <
                                 Ptrofs.unsigned alloc_ofs + int_size + int_size  * (Z.of_nat (length vs7)))%Z -> ~ L alloc_b j)).
                  {
                    inv Hrel_pL. destructAll. rewrite H6 in Hget_alloc. inv Hget_alloc.
                    intros.
                    apply H14.

                    simpl max_allocs. destruct ys. exfalso; auto. rewrite H15 in Hget_limit. inv Hget_limit.
                    destruct H10. split; auto.
                    eapply OrdersEx.Z_as_OT.lt_le_trans.
                    eauto.

                    etransitivity.
                    2: apply Hbound_max. rewrite H_eq_vs7.
                    int_red.
                    apply Forall2_length' in Hvs7. replace (@length var (@cons var v0 ys)) with (@length Values.val vs2).
                    rewrite Z.mul_add_distr_l.
                    rewrite Z.mul_succ_r.
                    rewrite nat_N_Z.
                    chunk_red; omega.
                  }
                  assert (H_u_mmid_m3: Mem.unchanged_on L'' m_mid m3). {
                    eapply mem_after_n_proj_store_unchanged. eauto.
                    intros; intro.
                    eapply bind_n_after_ptr_from_rev in H_ll''. rewrite <- H_ll'' in H8.
                    rewrite bind_n_after_ptr_def in H8.
                    destruct H8.
                    - (* L alloc_b j is protected *)
                      revert H8. apply H_not_in_L. subst. simpl length in *. int_red. simpl Z.of_nat in *.  chunk_red; omega.

                    - (* j is both in and after vs1 so impossible *)
                      int_red. chunk_red; omega.
                    }

                  clear H_eql'.

                  rewrite get_var_or_funvar_list_correct in Hvs7. rewrite <- get_var_or_funvar_list_set in Hvs7.
                  rewrite <- get_var_or_funvar_list_set in Hvs7.
                  2:{  intro.
                  assert (Hxrho := get_list_In _ _ _ _ H H6).
                  destruct Hxrho as [vv Hxrho].
                  eapply Hrho_id; eauto. }
                  2:{  intro.
                  inv Hp_id.

                  eapply get_list_In in H; eauto.
                  destruct H.
                  eapply H8. apply H.
                  right.
                  left. reflexivity.
                  left. reflexivity. }
                  rewrite <- get_var_or_funvar_list_correct in Hvs7.

                  clear Hrel_mL.
                  clear Hev.  clear Hc_env. revert H. clear Hp_id. clear Hf_id. revert H5.  clear Hrel_m. clear Hc_alloc.
                  clear H2.
                  clear H1.  clear H0.   clear Hstep_m2.  destruct Hstep_m3 as [Htemp Hm3]. clear Htemp.




                  clear Hm3.
                  revert H_m2_m3.
                  revert H_m2_mmid.
                  revert H_rev_vs7.


                  revert H_ll'. revert L'.
                  revert H_ll''. revert H_u_mmid_m3. revert L''.
                  revert Hvs7.
                  clear Hrel_pL.
                  clear Hays.

                  clear Hrho_id.
                  clear Ha_l.
                  revert ys.


                  clear H_eq_vs7. clear H_eq_vs1. clear H_eq_m2.
                  revert m_mid.
                  revert vs1. revert vs2.

                  induction vs. constructor.
                   intros.
                  apply get_list_cons in H. destruct H as [y [ys' [H_ys [Hyrho Hget_ys']]]].
                  subst.
                  inv Hvs7.

                  assert (H_repr_a0: repr_val_L_LambdaANF_Codegen_id fenv finfo_env p rep_env a0 m3 L'  (Val.load_result int_chunk y0)). {
                    assert (List.In y (y::ys')) by (constructor; auto). apply H5 in H. destructAll.
                    rewrite H in Hyrho. inv Hyrho.  inv H1.
                    inv H8. rewrite H9 in H1; inv H1.
                    - (* fun *)
                      eapply repr_val_L_sub_locProp.
                      2:{  intro.  intros. eapply bind_n_after_ptr_from_rev in H_ll'. rewrite <- H_ll'.
                      apply bind_n_after_ptr_def. left. apply H1. }
                      eapply repr_val_L_unchanged; eauto.
                    - (* constr *)
                      rewrite load_ptr_or_int.
                      rewrite H9 in H1.  inv H1.
                      rewrite H9 in H1; inv H1.
                    -
                      eapply repr_val_L_sub_locProp.
                      2:{ intro.  intros. eapply bind_n_after_ptr_from_rev in H_ll'. rewrite <- H_ll'.
                      apply bind_n_after_ptr_def. left. apply H1. }
                      eapply repr_val_L_unchanged; eauto.
                      rewrite load_ptr_or_int by auto.
                      inv H8. rewrite H1 in H9. inv H9.
                      rewrite H10 in H12. inv H12. auto.

                  }


                   simpl length in H_ll'.
                   inv H_ll'.



                   inv H_m2_m3.
                  - (* vs2 = [a] last case *)
                    inv H6. inv Hget_ys'. econstructor.
                    + intros.
                      right. split; auto.
                    + int_red.
                      eapply Mem.load_store_same. auto. apply H13.
                    + auto.
                    + constructor.
                   - (* vs2 = a::vs2' IH *)

                     assert (H_m2_m': mem_after_n_proj_snoc alloc_b (Ptrofs.unsigned alloc_ofs + int_size) (y0::vs1) m2 m') by (econstructor; eauto).
                     assert (H_ll''_new:= bind_n_after_ptr_exists (length (y0::vs1)) alloc_b  (Ptrofs.unsigned alloc_ofs + int_size) L).
                     destruct H_ll''_new as [L3 [H_ll3 H_ll3_def]].
                     assert (H_unchanged_L3: Mem.unchanged_on L3 m' m3).
                     {  eapply mem_after_n_proj_store_unchanged. apply H14.
                       intros. intro. rewrite <- H_ll3_def in H2.
                       rewrite bind_n_after_ptr_def in H2.
                       destruct H2.
                       * revert H2. apply H_not_in_L.
                         int_red.
                         rewrite length_app.
                         rewrite length_rev.
                         simpl length.
                         rewrite Nat2Z.inj_add.
                         rewrite Nat2Z.inj_succ. chunk_red; omega.
                       * destruct H2. simpl length in H8.
                         rewrite Nat2Z.inj_succ in H8. int_red. chunk_red; omega.
                     }
                     eapply IHvs in H_m2_m'; eauto.
                     + econstructor.
                       * intros. right. auto.
                       * int_red.
                         eapply Mem.load_unchanged_on.
                         eauto.
                         intros. rewrite <- H_ll3_def.
                         rewrite bind_n_after_ptr_def. right. split; auto. simpl length.
                         rewrite Nat2Z.inj_succ. int_red. chunk_red; omega.
                         eapply Mem.load_store_same. apply H10.
                       * (* this is from m3 unchanged m over L *)
                         auto.

                       *  eapply repr_val_ptr_list_L_Z_sub_locProp; auto.
                          replace (Ptrofs.unsigned alloc_ofs + int_size + int_size * Z.of_nat (length vs1) + int_size)%Z
                           with
                             (Ptrofs.unsigned alloc_ofs + int_size + int_size * Z.of_nat (length (y0 :: vs1)))%Z.
                         apply H_m2_m'. simpl length. rewrite Nat2Z.inj_succ.
                         rewrite Z.mul_succ_r. int_red. omega.
                         intro. intros. left. eauto.
                     + simpl length. rewrite Nat2Z.inj_succ. rewrite Z.mul_succ_r. int_red. rewrite Z.add_assoc. eauto.
                     + simpl. rewrite <- app_assoc. simpl. auto.
                     + simpl length. rewrite Nat2Z.inj_succ. auto.
                     + intros. apply H5. constructor 2. auto.
                     }
        (*

 get_list ys rho = Some vs ->
Forall2
           (get_var_or_funvar p
              (Maps.PTree.set allocIdent
                 (Vptr alloc_b (Int.add alloc_ofs (Int.mul (Int.repr (sizeof (globalenv p) val)) (Int.repr (Z.of_N (a + 1))))))
                 (Maps.PTree.set x
                    (Vptr alloc_b (Int.add alloc_ofs (Int.mul (Int.repr (sizeof (globalenv p) val)) (Int.repr Z.one)))) lenv)))
           ys vs7
 rel_mem_LambdaANF_Codegen_id fenv finfo_env p rep_env (Econstr x t ys e) rho m lenv
 ->
 mem_after_n_proj_store_cast alloc_b
               (Int.unsigned (Int.add alloc_ofs (Int.mul (Int.repr (sizeof (globalenv p) val)) (Int.repr Z.one)))) vs7 0 m2 m3
 ->
  repr_val_ptr_list_L_LambdaANF_Codegen argsIdent allocIdent limitIdent gcIdent threadInfIdent tinfIdent isptrIdent caseIdent fenv finfo_env
    p rep_env vs m3 (bind_n_after_ptr (Z.of_N (a + 1)) alloc_b (Int.unsigned alloc_ofs) L) alloc_b
    (Int.add alloc_ofs (Int.mul (Int.repr (sizeof (globalenv p) val)) (Int.repr Z.one)))

*)
                 + (* x0 <> x*)
                   {
                     specialize (Hrel_mL x0).
                     destruct Hrel_mL as [Hrel_mL Hrel_ml'].

                     split.
                     - intro.
                       assert (occurs_free (Econstr x t ys e) x0).
                       constructor 2; auto.
                       specialize (Hrel_mL  H5).
                       destruct Hrel_mL as [v6 [Hx0_v6 Hrepr_v6]].
                       exists v6. split.
                       rewrite M.gso; auto.
                       apply repr_val_id_set.
                       apply repr_val_id_set.
                       eapply repr_val_id_L_sub_locProp with (L := L).
                       eapply repr_val_id_L_unchanged. apply Hrepr_v6. auto.
                       intro. intros.
                       rewrite bind_n_after_ptr_def. auto.
                       auto.
                       inv Hp_id.
                       intro.
                       eapply H6. apply Hx0_v6.
                       right. left. reflexivity. auto.
                     -  intros.
                        rewrite M.gso in H4 by auto. assert (H4' := H4).
                        specialize (Hrel_ml' _ _ _ _ H4 H5).
                        destruct Hrel_ml' as [Hrel_ml' [Hrel_closed Hrel_f]]. split.
                        2: auto.
                        apply repr_val_id_set.
                        apply repr_val_id_set.
                        eapply repr_val_id_L_sub_locProp with (L := L).
                        eapply repr_val_id_L_unchanged. eauto.  auto.
                        intro. intros.                        rewrite bind_n_after_ptr_def. auto.
                        subst; auto.
                        inv Hf_id.
                        assert ( bound_var (Econstr x t ys e) x) by constructor. intro; subst.
                        apply H6 in H9. inv Hrel_ml'.
                        rewrite H17 in H9; inv H9.
                        inv H12. rewrite H20 in H9. inv H9.
                        intro. subst.

                        inv Hp_id. eapply H6.  apply H4. right; left. reflexivity. right.
                        eapply bound_var_subval; eauto.
                        inv Hrel_ml'. inv H17. constructor.
                        apply name_in_fundefs_bound_var_fundefs.
                        eapply find_def_name_in_fundefs. eauto.
                        inv H11. rewrite H19 in H9. inv H9. split. auto.
                        eapply correct_fundefs_unchanged_global with (m := m2).
                        eapply correct_fundefs_unchanged_global with (m := m).
                        apply Hrel_f.
                        auto.
                        auto.
                   }      }
        { (* correct_tinfo after adding the constructor *)


          assert (correct_tinfo p (Z.of_nat (max_allocs e))
                                (Maps.PTree.set x (Vptr alloc_b (Ptrofs.add alloc_ofs (Ptrofs.mul (Ptrofs.repr (sizeof (globalenv p) val)) (Ptrofs.repr Z.one))))
                                                lenv) m3).

          eapply correct_tinfo_not_protected.
          eapply correct_tinfo_mono.
          destruct Hstep_m3.
          eapply correct_tinfo_after_nstore.

          2: eauto.

          eapply correct_tinfo_after_store; eauto.
          inv Hc_alloc.
          simpl max_allocs. destruct ys. omega.
          rewrite Nat2Z.inj_succ.
          rewrite Nat2Z.inj_add.
          omega.
          intro; apply H3.
          apply is_protected_tinfo_weak. auto.
          {
            inv Hp_id.
            intro; subst; eapply H5.
            2: constructor.
            inList.
          }
          (* alloc is moved to an OK location *)
          {



            destruct H4 as [alloc_b' [alloc_ofs' [limit_ofs' [args_b' [args_ofs' [tinf_b' [tinf_ofs' [Hget_alloc' [Hdiv_alloc [Hrange_alloc' [Hget_limit' [Hbound_limit' [Hget_args' [Hdj_args' [Hbound_args' [Hrange_args' [Htinf1' [Htinf2' [Htinf3' [Hinf_limit' Htinf_deref']]]]]]]]]]]]]]]]]]]].
            assert (alloc_b' = alloc_b /\ alloc_ofs' = alloc_ofs).  rewrite M.gso in Hget_alloc'. rewrite Hget_alloc' in Hget_alloc. inv Hget_alloc. auto.
            intro.  apply H3. subst. rewrite <- H4. inList.
            destruct H4; subst.
            assert (args_b' = args_b /\ args_ofs' = args_ofs).  rewrite M.gso in Hget_args'. rewrite Hget_args' in Hget_args. inv Hget_args. auto.
            intro.  apply H3. subst. rewrite <- H4; inList.
            destruct H4; subst.
            assert (limit_ofs = limit_ofs'). rewrite M.gso in Hget_limit'. rewrite Hget_limit' in Hget_limit. inv Hget_limit. auto.
            intro.  apply H3. rewrite <- H4; inList.
            subst.
            assert (tinf_b' = tinf_b /\ tinf_ofs' = tinf_ofs). rewrite M.gso in Htinf1'. rewrite Htinf1' in Htinf1; inv Htinf1; auto. intro. apply H3. subst. rewrite <- H4. inList. destruct H4; subst. split.
            do 7 eexists. split.
            rewrite M.gss. reflexivity.
            split.
            (* align *)
            rewrite int_z_mul.
            rewrite pointer_ofs_no_overflow.
            apply Z.divide_add_r. auto.
            apply OrdersEx.Z_as_DT.divide_factor_l. apply N2Z.is_nonneg.
            inv Hbound_limit.
            rewrite <- Z.le_add_le_sub_l in H4.
            etransitivity. etransitivity. 2: apply H4.
            inv Hc_alloc. simpl max_allocs. destruct ys. inv Ha_l; exfalso; auto.
            destruct Ha_l. rewrite H6. rewrite N2Z.inj_add. rewrite nat_N_Z.
            rewrite Nat2Z.inj_succ.
            rewrite Nat2Z.inj_add.
            unfold int_size. simpl size_chunk.  simpl Z.of_N. chunk_red; omega.
            apply Ptrofs.unsigned_range_2. constructor.
            constructor. unfold sizeof. chunk_red; archi_red; omega. rewrite ptrofs_mu. chunk_red; archi_red; solve_uint_range; omega.
            constructor.
            split.
            apply N2Z.is_nonneg.
            inv Hbound_limit.
            rewrite <- Z.le_add_le_sub_l in H4.
            etransitivity. etransitivity. 2: apply H4.
            inv Hc_alloc. simpl max_allocs.
             destruct ys. inv Ha_l; exfalso; auto.
            destruct Ha_l. rewrite H6. rewrite N2Z.inj_add. rewrite nat_N_Z.
            rewrite Nat2Z.inj_succ.
            rewrite Nat2Z.inj_add.
            unfold int_size. simpl size_chunk. simpl Z.of_N.
            rewrite <- Z.add_succ_l.
            assert (0 <=   Ptrofs.unsigned alloc_ofs)%Z by apply Ptrofs.unsigned_range_2.
            chunk_red; omega.
            apply Ptrofs.unsigned_range_2. constructor.



            split.
            intro. intro. apply Hrange_alloc'. destruct H4. split; eauto.
            etransitivity. 2: apply H4. rewrite int_z_mul. rewrite pointer_ofs_no_overflow.
            int_red. rewrite Z.add_comm. apply Z_non_neg_add. reflexivity. apply Z.mul_nonneg_nonneg.
            chunk_red; omega. apply N2Z.is_nonneg. apply N2Z.is_nonneg.
            inv Hbound_limit.
            rewrite <- Z.le_add_le_sub_l in H6.
            etransitivity. etransitivity. 2: apply H6.
            inv Hc_alloc. simpl max_allocs. destruct ys. inv Ha_l; exfalso; auto.
            destruct Ha_l. rewrite H9. rewrite N2Z.inj_add. rewrite nat_N_Z.
            rewrite Nat2Z.inj_succ.
            rewrite Nat2Z.inj_add.
            unfold int_size. simpl size_chunk. simpl Z.of_N. chunk_red; omega.
            apply Ptrofs.unsigned_range_2. constructor.
            unfold uint_range. unfold sizeof. rewrite ptrofs_mu. chunk_red; archi_red; solve_uint_range; omega.
            constructor.
            split.
            apply N2Z.is_nonneg.
            destruct Hbound_limit.
            rewrite <- Z.le_add_le_sub_l in H6.
            etransitivity. etransitivity. 2: apply H6.
            inv Hc_alloc. simpl max_allocs.
             destruct ys. inv Ha_l; exfalso; auto.
            destruct Ha_l. rewrite H9. rewrite N2Z.inj_add. rewrite nat_N_Z.
            rewrite Nat2Z.inj_succ.
            rewrite Nat2Z.inj_add.
            unfold int_size. simpl size_chunk. simpl Z.of_N.
            rewrite <- Z.add_succ_l.
            assert (0 <=   Ptrofs.unsigned alloc_ofs)%Z by apply Ptrofs.unsigned_range_2.
            chunk_red; omega.
            apply Ptrofs.unsigned_range_2. constructor.
(*

            intros. inv Hc_alloc.
            assert ( (0 <= i + (Z.of_N (a + 1)) < Z.of_nat (max_allocs (Econstr x t ys e))))%Z.
            simpl max_allocs.   destruct ys. inv H2.
            rewrite Nat2Z.inj_succ.
            rewrite Nat2Z.inj_add.
            destruct Ha_l. rewrite H5. simpl.  rewrite Pos2Z.inj_add.
            rewrite Z.add_1_r.
            rewrite Z.add_succ_r.
            split.
            apply Z.le_le_succ_r.
            apply Z_non_neg_add.
            apply Pos2Z.is_nonneg.
            apply H4.
            omega.
            apply Hrange_alloc in H5.
            rewrite Z.mul_add_distr_l in H5.
            rewrite Z.add_comm in H5.
            rewrite Int.add_assoc.
            replace (Int.add (Int.mul (Int.repr (sizeof (globalenv p) val)) (Int.repr (Z.of_N (a + 1)))) (Int.repr (int_size * i)))  with (Int.repr (int_size * Z.of_N (a + 1) + int_size * i)).
            eapply valid_access_after_nstore.
            eapply Mem.store_valid_access_1.
            eauto. apply H5.
            destruct Hstep_m3; eauto.


            assert (Halloc_ofs := Int.unsigned_range_2 alloc_ofs).
            assert (Hlimit_ofs' := Int.unsigned_range_2 limit_ofs').
            simpl max_allocs in Hbound_limit.
            destruct ys. inv Ha_l. exfalso. apply H8; auto.
            destruct Ha_l.
            rewrite Nat2Z.inj_succ in Hbound_limit.
            rewrite Nat2Z.inj_add in Hbound_limit.
            rewrite <- nat_N_Z with (n := (length (v0 :: ys))) in Hbound_limit.
            rewrite <- H6 in Hbound_limit.
            rewrite N.add_1_r.
            rewrite N2Z.inj_succ.
            rewrite Zplus_succ_r_reverse in Hbound_limit.
            rewrite Z.mul_add_distr_l in Hbound_limit.

            rewrite int_z_mul.

            rewrite int_z_add. reflexivity.
            simpl sizeof. int_red.
            constructor.
            split.
            assert (0 <= Z.of_N a)%Z by apply N2Z.is_nonneg. omega.
            etransitivity. etransitivity. Focus 2. apply Hbound_limit.
            assert (0 <= Int.unsigned alloc_ofs)%Z by apply Int.unsigned_range. omega.
            apply Int.unsigned_range_2.
            constructor. split. omega.
            etransitivity. etransitivity. Focus 2. apply Hbound_limit.
            assert (0 <= Int.unsigned alloc_ofs)%Z by apply Int.unsigned_range.
            assert (0 <= Z.of_N a)%Z by apply N2Z.is_nonneg. omega.
            apply Int.unsigned_range_2.
            constructor.
            simpl sizeof. constructor. solve_uint_range. constructor.

            assert (0 <= Z.of_N a)%Z by apply N2Z.is_nonneg.
            split. omega.
            etransitivity. etransitivity. Focus 2. apply Hbound_limit.
            assert (0 <= Int.unsigned alloc_ofs)%Z by apply Int.unsigned_range.
            int_red.
            omega.
            apply Int.unsigned_range_2.
            constructor.
*)
            split. rewrite M.gso.
            subst.
            eauto. intro.
            assert (H_nodup := disjointIdent).
            inv H_nodup. inversion H9.
            apply H10. constructor. constructor.
            split.
            rewrite int_z_mul.
            unfold Ptrofs.add.
            destruct Ha_l. rewrite H4.
            destruct ys. exfalso; apply H5; auto.
            rewrite N2Z.inj_add.
            rewrite nat_N_Z.
            simpl Z.of_N.
            simpl sizeof. rewrite Ptrofs.unsigned_repr with (z := (sizeof (prog_comp_env p) uval * (Z.of_nat (length (v0 :: ys)) + 1))%Z).
            rewrite Ptrofs.unsigned_repr.
            inv Hbound_limit.
            inv Hc_alloc. simpl max_allocs in H6.
            repeat (rewrite Nat2Z.inj_succ in H6).
            rewrite Nat2Z.inj_add in H6. unfold int_size in *.
            simpl size_chunk in *.
            rewrite Nat2Z.inj_succ in H6.
            split.
            rewrite Z.sub_add_distr.
            rewrite <- Z.le_add_le_sub_l.
            etransitivity. 2: apply H6.
            simpl length. rewrite Nat2Z.inj_succ.
            chunk_red; unfold sizeof; archi_red; omega.
            chunk_red; unfold sizeof; archi_red; omega.


            split. apply Z_non_neg_add.
            chunk_red; unfold sizeof; archi_red; omega.
            apply Ptrofs.unsigned_range.
            inv Hbound_limit. inv Hc_alloc.
            rewrite <- Z.le_add_le_sub_l in H6.
            etransitivity. etransitivity. 2: apply H6.
            simpl max_allocs. simpl length.
            rewrite Nat2Z.inj_succ.
            rewrite Nat2Z.inj_succ.
            rewrite Nat2Z.inj_add.
            rewrite Nat2Z.inj_succ. unfold int_size in *.
            chunk_red; unfold sizeof; archi_red; omega.

            apply Ptrofs.unsigned_range_2.
            split.             chunk_red; unfold sizeof; archi_red; omega.
            inv Hbound_limit. inv Hc_alloc. etransitivity.
            etransitivity. 2: apply H8.
            etransitivity. 2: apply H6.
            unfold int_size.
            simpl max_allocs. simpl length.
            rewrite Nat2Z.inj_succ.
            rewrite Nat2Z.inj_succ.
            rewrite Nat2Z.inj_add.
            rewrite Nat2Z.inj_succ.
            assert (0 <=  Ptrofs.unsigned alloc_ofs)%Z by apply Ptrofs.unsigned_range.
            chunk_red; unfold sizeof; archi_red; omega.

            unfold gc_size. rewrite ptrofs_mu. chunk_red; archi_red;  solve_uint_range; omega.
            constructor.             chunk_red; unfold sizeof; archi_red; solve_uint_range; omega.
            constructor.
            split. apply N2Z.is_nonneg.
            destruct Ha_l. rewrite H4.
            destruct ys. exfalso; auto.
            inv Hbound_limit.
            rewrite <- Z.le_add_le_sub_l in H6. etransitivity.
            etransitivity. 2: apply H6. 2: apply Ptrofs.unsigned_range_2.
            inv Hc_alloc.  simpl max_allocs. simpl length.
            rewrite Nat2Z.inj_succ.
            rewrite Nat2Z.inj_add.
            rewrite N2Z.inj_add.
            rewrite nat_N_Z.
            unfold int_size. simpl size_chunk. simpl Z.of_N.
            assert (0 <=  Ptrofs.unsigned alloc_ofs)%Z by apply Ptrofs.unsigned_range.
            simpl in H6. chunk_red; omega.

            constructor.


            split. rewrite M.gso. eauto.
            intro.
            assert (H_nodup := disjointIdent). subst.
            inversion H_nodup. subst. apply H8; inList.
            split. auto. split. auto. split. auto.
            split. rewrite M.gso. rewrite M.gso. eauto.
            { inv Hp_id.
              intro; subst.
              eapply H5.
              2: constructor.
              inList.
            }
            intro.
            assert (H_dj := disjointIdent); inv H_dj.
            clear H4. inv H9. apply H6.
            inList.
            split. eauto. eauto.

            (* same args_ptr *)
            unfold same_args_ptr.
            rewrite M.gso. rewrite M.gso. reflexivity.
            intro. apply H3. unfold is_protected_id_thm. subst. inList.
            assert (Hnd := disjointIdent).
            inv Hnd. intro; apply H6; subst; inList.

        }}

      - (* unboxed *)
        eexists. eexists. split.
        constructor. constructor. constructor.
        split.
        + (* mem *)
          destruct Hrel_m as [L  [Hnot_in_L Hrepr_m]].
          exists L. split.
          eapply protected_not_in_L_set; eauto.
          intro; apply Hx_not; apply is_protected_tinfo_weak; eauto.
          intro. apply Hx_not. unfold is_protected_id_thm. subst; inList.
          intros.  specialize (Hrepr_m x0).
          destruct Hrepr_m as [Hrepr_m Hrepr_m'].
          destruct (var_dec x0 x).
          * subst.
            split.
              2:{ intros. rewrite M.gss in H2. inv H2.
              apply subval_or_eq_fun in H3. destruct H3. destruct H2.
              assert (Hy0x0 := get_list_In_val _ _ _ _ H H3).
              destruct Hy0x0 as [y0 [Hy0 Hy0']].
              inv Hy0. }


            intro.
            exists (Vconstr t vs). split.
            rewrite M.gss. reflexivity.
            econstructor 2.
            apply Hf_id. constructor.
            rewrite M.gss. reflexivity.
            simpl in H. inv H.
            econstructor; eauto.

          *
            split. intro.
            assert (occurs_free (Econstr x t [] e) x0).
            constructor 2; auto.
            specialize (Hrepr_m  H3).
            destruct Hrepr_m as [v6 [Hx0v6 Hrepr_v6]].
            exists v6.
            split.
            rewrite M.gso; auto.
            apply repr_val_id_set; auto.

            intros. rewrite M.gso in H2 by auto.
            eapply Hrepr_m' in H2; eauto.
            destruct H2 as [H2 Hrepr_f].
            split. 2: auto.
            apply repr_val_id_set; auto.
            intro; subst.
            inv Hf_id.
            assert ( bound_var (Econstr x t [] e) x) by constructor.

            apply H4 in H6.
            inv H2.
            rewrite H15 in H6; inv H6.
            inv H10.
            rewrite H17 in H6.
            inv H6.
        + split.
          (* tinfo *)
          apply correct_tinfo_not_protected.
          eapply correct_tinfo_mono; eauto.
          inv Hc_alloc. simpl. omega.
          intro.
          inv Hp_id.
          eapply H4. apply is_protected_tinfo_weak. eauto. eauto.
          { inv Hp_id.
            intro; subst.
            eapply H3.
            2: constructor.
            inList.
          }

          (* same args *)
          unfold same_args_ptr. rewrite M.gso. reflexivity.
          inv Hp_id. intro. apply Hx_not.
          unfold is_protected_id_thm. subst; inList.

    }  destruct H0 as [lenv' [m' [Hstep [Hrel_m' [Htinfo_e Hsame_args]]]]].

    (* set up the with the recursive call *)
    assert (Hc_env_e: correct_envs cenv ienv rep_env (term.M.set x (Vconstr t vs) rho) e). {
      eapply correct_envs_subterm.
      eapply correct_envs_set.
      eauto.
      - inv Hc_env.
        destructAll.
        apply Forall_constructors_in_constr in H2. destruct (M.get t cenv) eqn:Mtcenv. 2: inv H2. destruct c0.
        econstructor; eauto.
        2:{ simpl. simpl. subst. symmetry. exact (f_equal N.of_nat (get_list_length_eq _ _ _ H)). }
        apply Forall_forall. intros.
        assert (Hgiv := get_list_In_val _ _ _ _ H H4).
        destruct Hgiv. destruct H5.
        eapply H1. eauto.
      -  constructor. constructor.
    }
    assert (Hp_id_e: protected_id_not_bound_id (term.M.set x (Vconstr t vs) rho) e).
    { split; intros.
      - inv Hp_id.
        destruct (var_dec x0 x).
        + subst. intro. inv H4; subst.
          eapply H3; eauto.
          rewrite M.gss in H0. inv H0.
          inv H5.
          assert (Hgi_v := get_list_In_val _ _ _ _ H H10).
          destructAll.
          eapply H2; eauto.
        + rewrite M.gso in H0 by auto. eapply H2; auto.
      - inv Hp_id.
        intro. eapply H2; eauto.
    }
    assert (Hf_id_e:  functions_not_bound p (term.M.set x (Vconstr t vs) rho) e). {
      eapply functions_not_bound_subterm.
      eapply functions_not_bound_set;
        eauto.
      - intros.

        inv H0.
        inv Hf_id.
        assert (Hx0rho := get_list_In_val _ _ _ _ H H5).
        destruct Hx0rho. destruct H2.
        eapply H1; eauto.
      - constructor. constructor.
    }
    assert (H_rho_e:  unique_bindings_env (term.M.set x (Vconstr t vs) rho) e ).
    {  destruct Hrho_id as [Hub Hrho_id].
      split.
      inv Hub; auto.
      intro. intros.
      destruct (var_dec x0 x).
      - subst. (* need unique binding *)
        inv Hub. auto.
        rewrite M.gss in H0. inv H0.
        split; auto. constructor.
        apply Forall_forall. intros.
        assert (Hx0rho := get_list_In_val _ _ _ _ H H0). destruct Hx0rho as [xx0 [Hinys Hxx0rho]].
        apply Hrho_id in Hxx0rho. destruct Hxx0rho. auto.
      -  rewrite M.gso in H0 by auto.
         apply Hrho_id in H0.
         destruct H0. split; auto.
    }
    specialize (IHHev Hc_env_e Hp_id_e H_rho_e Hf_id_e).
    assert (Hca_e : correct_alloc e (Z.of_nat (max_allocs e))).
    unfold correct_alloc. reflexivity.
    specialize (IHHev _ _ _ k _ fu H7 Hrel_m' Hca_e Htinfo_e).
    destruct IHHev as [m'' [lenv'' [Hstep' [Hargs1 Hargs2]]]].
    exists m'', lenv''.
    split; auto.
    eapply t_trans. eapply t_trans.
    constructor. constructor. apply Hstep.
    eapply t_trans. constructor. constructor.
    auto.
    split; auto.
    unfold same_args_ptr in *. etransitivity; eauto.


  - (* Eproj *)

    (* > representation in memory of the Vconstr *)
    assert (Hy : occurs_free (Eproj x t n y e) y) by constructor.
    destruct (Hrel_m) as [L [HL_pro Hmem]].
    apply Hmem in Hy. destruct Hy as [v6 [Hyv6 Hrepr_v6]].
    rewrite Hyv6 in H. inv H.
    inversion Hrepr_v6; subst.

    rename H1 into Hyv7.
    inv H2.
    (* impossible that v7 is an enum, if taking proj, then vs is not empty so c is boxed *)
    { exfalso.
      inv H0.
    }
    (* get the value on the nth of vs in memory *)

    assert (Hvn := repr_val_ptr_list_L_nth argsIdent allocIdent limitIdent gcIdent threadInfIdent tinfIdent isptrIdent caseIdent nParam _ _ _ _ H12  H0).

    (* done setting up, taking the proj step *)
    destruct Hvn as [v7' [Hv7'_l Hv7'_rep]].
    assert (m_tstep2 (globalenv p)
      (State fu
         (Ssequence
            (Sset x
               (Ederef
                  (add
                     (Ecast (Etempvar y val)
                        (Tpointer val
                           {|
                           attr_volatile := false;
                           attr_alignas := None |}))
                     (c_int' (Z.of_N n) val)) val)) s) k empty_env
         lenv m)
      (State fu s k empty_env (Maps.PTree.set x v7' lenv) m)).
    {
      eapply t_trans.
      constructor. constructor.
      eapply t_trans.
      constructor. constructor. eapply eval_Elvalue. apply eval_Ederef.
      econstructor. econstructor. constructor.
      eauto. reflexivity. constructor.
      simpl. unfold sem_add. simpl. reflexivity.
      eapply deref_loc_value. constructor. simpl.
      rewrite Ptrofs.mul_commut. unfold Ptrofs.of_int64.
      rewrite ptrofs_of_int64.
      rewrite sizeof_uval.
      apply Hv7'_l.
      constructor. constructor.
    }

    simpl in Hc_alloc.
    assert (Hc_env_e: correct_envs cenv ienv rep_env (term.M.set x v rho) e). {
      eapply correct_envs_subterm.
      eapply correct_envs_set.
      eauto.
      - inv Hc_env. destructAll.
        apply nthN_In in H0.
        apply H3 in Hyv6. inv Hyv6.
        rewrite Forall_forall in H14.
        apply H14; auto.
      - constructor. constructor.
    }
    specialize (IHHev Hc_env_e).
    assert (Hp_id_e: protected_id_not_bound_id (term.M.set x v rho) e).
    { split; intros.
      - inv Hp_id.
        destruct (var_dec x0 x).
        + subst. intro. inv H11; subst.
          eapply H10. apply H3. constructor.
          rewrite M.gss in H2. inv H2.
          eapply H9. apply Hyv6. apply H3.
          right. econstructor.
          apply H13. eapply nthN_In; eauto.
        + rewrite M.gso in H2 by auto. eapply H9. apply H2. auto.
      - inv Hp_id.
        intro. eapply H9. apply H2.
        constructor; auto.
    }
    specialize (IHHev Hp_id_e).
    assert (Hf_id_e: functions_not_bound p (term.M.set x v rho) e). {
      eapply functions_not_bound_subterm.
      eapply functions_not_bound_set; eauto.
      - intros.
        inv Hf_id. eapply H9. apply Hyv6.
        econstructor. apply H2.
        eapply nthN_In; eauto.
      - constructor. constructor.
    }

    assert (Hrho_id_e: unique_bindings_env (term.M.set x v rho) e). {
      destruct Hrho_id as [Hub Hrho_id].
      split.
      inv Hub; auto.
      intros. destruct (var_dec x0 x).
      - subst. rewrite M.gss in H2. inv H2. inv Hub; auto.
        split; auto.
        apply Hrho_id in Hyv6.
        destruct Hyv6. inv H3. rewrite Forall_forall in H11.
        apply H11; auto. eapply nthN_In. eauto.
      - rewrite M.gso in H2 by auto. apply Hrho_id in H2.
        destruct H2. split; auto.
    }
    specialize (IHHev Hrho_id_e Hf_id_e _ (Maps.PTree.set x v7' lenv) m k max_alloc fu H7).
    assert (Hx_not:  ~ is_protected_id_thm x). {
      intro. inv Hp_id. eapply H9; eauto.
    }
    assert (rel_mem_LambdaANF_Codegen_id fenv finfo_env p rep_env e (term.M.set x v rho) m (Maps.PTree.set x v7' lenv)).
    { exists L.

      split.
      -  eapply protected_not_in_L_set; eauto.
         intro; apply Hx_not; apply is_protected_tinfo_weak; auto.
         intro; apply Hx_not. subst. unfold is_protected_id_thm; inList.
      - intros.
        destruct (var_dec x0 x).
        + subst.
          split; intros.
          * exists v. split.
            rewrite M.gss; auto.
            specialize (Hmem x). destruct Hmem as [Hmem Hmem'].
            econstructor 2.
            (* x is bound in Eproj x t n y e so cannot be a function name  *)
            apply Hf_id. constructor.
            rewrite M.gss. reflexivity.
            apply Hv7'_rep.
          * rewrite M.gss in H2. inv H2.
            apply nthN_In in H0.
            specialize (Hmem y). destruct Hmem as [Hmem Hmem'].
            specialize (Hmem' _ _ _ _ Hyv6 (subval_or_eq_constr _ _ _ _ H3 H0)).
            destruct Hmem' as [Hmem' Hmem_f]. split. 2: auto.
            apply repr_val_id_set. auto.
            intro. subst.
            inv Hf_id.
            assert ( bound_var (Eproj x t n y e) x) by constructor.
            apply H2 in H10.
            inv Hmem'.
            rewrite H10 in H19. inv H19.
            inv H14. rewrite H10 in H22. inv H22.
        + rewrite M.gso by auto.
          specialize (Hmem x0). destruct Hmem as [Hmem Hmem'].
          split. intros.
          assert ( occurs_free (Eproj x t n y e) x0). constructor; auto.

          specialize (Hmem  H3). destructAll.
          exists x1; split; auto.
          inv H10.
          * econstructor; eauto.
          * econstructor 2; eauto.
            rewrite M.gso; auto.
          * intros. specialize (Hmem' _ _ _ _ H2 H3).
            destruct Hmem' as [Hmem' Hmem_f].
            split. 2: auto.
            apply repr_val_id_set. auto.
            inv Hmem'. intro.  inv Hf_id. specialize (H10 x).
            assert ( bound_var (Eproj x t n y e) x) by constructor. apply H10 in H9.
            rewrite H9 in H17. inv H17.
            inv H11.
            rewrite H20 in H9. inv H9.
    }
    assert ( correct_alloc e max_alloc). inv Hc_alloc.
    simpl. constructor.
    assert ( correct_tinfo p max_alloc
            (Maps.PTree.set x v7' lenv) m ).
    apply correct_tinfo_not_protected; auto.
    intro; apply Hx_not; apply is_protected_tinfo_weak; auto.
    {
      inv Hp_id.
      intro. eapply H10.
      2:{ subst. constructor. }
      inList.
    }
    specialize (IHHev H2 H3 H9).
    destruct IHHev as [m' [lenv' [Hstep [Hargs1 Hargs2]]]].
    exists m', lenv'.
    split; auto.
    eapply t_trans; eauto.
    split; auto.
    unfold same_args_ptr in *.
    rewrite <- Hargs1.
    rewrite M.gso. auto.
    inv Hp_id. intro. apply Hx_not. unfold is_protected_id_thm. subst; inList.
  - (* Ecase *)

    (* get the representation of y *)
    assert (Hrel_m' := Hrel_m).
    destruct Hrel_m' as [L [Hmem_p Hmem_rel]].
    assert (occurs_free (Ecase y cl) y) by constructor.
    apply Hmem_rel in H2. destruct H2 as [y6 [Hy6 Hrepr_id_y6]].
    rewrite Hy6 in H. inv H.

    assert (Htcenv := caseConsistent_findtag_In_cenv _ _ _ _ H0 H1).
    destruct Htcenv as [a [ty [n [i Htcenv]]]].
    (** Hrepr_id_y6 must be RVid_V *)
    inv Hrepr_id_y6.
    rename H into Hglob_y. rename H2 into Hlenv_y. rename H3 into Hrepr_y.


    (* step through the assignment and the isptr check *)
    inv H6.
    destruct Hpinv as [Hptr_inv Htinf_inv].
    clear Htinf_inv.
    destruct Hptr_inv as [b_isPtr [isPtr_name [isPtr_sg [H_isPtr [H_isPtr_ff [H_isPtr_int H_isPtr_ptr]]]]]].

    assert (Hstep_case:
        exists vbool s s',
          m_tstep2 (globalenv p)
         (State fu
         (Ssequence (isPtr isptrIdent caseIdent y)
            (Sifthenelse (Etempvar caseIdent boolTy)
               (Sswitch
                  (Ebinop Oand
                     (Ederef
                        (add
                           (Ecast (Etempvar y val)
                              (Tpointer val
                                 {| attr_volatile := false; attr_alignas := None |}))
                           (c_int' (-1) val)) val) (make_cint 255 val)
                     val) ls)
               (Sswitch
                  (Ebinop Oshr (Etempvar y val) (make_cint 1 val) val) ls')))
         k empty_env lenv m)
         (State fu s (Kseq Sbreak (Kseq s' (Kswitch k))) empty_env
                (Maps.PTree.set caseIdent vbool lenv) m) /\
         repr_expr_LambdaANF_Codegen_id fenv finfo_env p rep_env e s).
    {
      inv Hrepr_y.
      - (* unboxed *)
        exists (Vfalse).
        assert (exists s s', seq_of_labeled_statement (select_switch (Z.shiftr n0 1) ls') = (Ssequence (Ssequence s Sbreak) s') /\  repr_expr_LambdaANF_Codegen_id fenv finfo_env p rep_env e s).
        eapply case_of_labeled_stm_unboxed; eauto; inv Hc_env; destruct H2; destruct H5; eauto.
        destruct H as [s [s' [Hseq Hrepr_es]]].
        exists s, s'.
        split; auto.


        eapply t_trans. constructor.
        constructor. eapply t_trans.
        constructor. unfold isPtr.


        econstructor.
        simpl. constructor.
        econstructor.  apply eval_Evar_global. apply Maps.PTree.gempty. (* assumption 1 *) eauto.
        constructor. constructor. econstructor. econstructor. constructor. apply Hlenv_y. apply sem_cast_vint. apply sem_cast_vint.         constructor. eauto.
        reflexivity.
        eapply t_trans. constructor.

        eapply step_external_function. apply H_isPtr_int.

        (* return *)
        eapply t_trans. constructor. constructor. eapply t_trans. constructor. constructor.
        eapply t_trans. constructor. econstructor. constructor. unfold set_opttemp. rewrite M.gss. reflexivity. simpl.  constructor.
        rewrite Int.eq_true. simpl.

         (* switch to the right case *)
        eapply t_trans. constructor. econstructor. simpl. econstructor. constructor.
        rewrite M.gso. apply Hlenv_y. (* caseIdent is protected *)
        {
          destruct Hp_id as [Hp_1 Hp_2].
          intro; eapply Hp_1; eauto.
          inList.
        }
        apply eval_cint.
        simpl.
        assert (  sem_binary_operation (globalenv p) Oshr (make_vint n0) (typeof (Etempvar y uval))
                                       (make_vint 1) (typeof (make_cint 1 uval)) m = (Some (int_shru n0 1))).  unfold int_shru. unfold make_cint. chunk_red; archi_red. constructor. constructor. apply H.
        apply sem_switch_arg_1.
        eapply repr_unboxed_header_range; eauto.

         rewrite Hseq. eapply t_trans.
        constructor. constructor.
        constructor. constructor.
      - exists Vtrue.

        assert ( exists s s',
                   (seq_of_labeled_statement (select_switch (Z.land h 255) ls)) = (Ssequence (Ssequence s Sbreak) s') /\  repr_expr_LambdaANF_Codegen_id fenv finfo_env p rep_env e s).
        inv Hc_env. inv H2. destruct H9.
         eapply case_of_labeled_stm_boxed; eauto.
        destruct H as [s [s' [H_seq H_repr_es]]].
        exists s, s'.
        split; auto.
        eapply t_trans. constructor.
        constructor. eapply t_trans.
        constructor. unfold isPtr.
        econstructor.
        simpl. constructor.
        econstructor.  apply eval_Evar_global. apply Maps.PTree.gempty. (* assumption 1 *) eauto.
        constructor. constructor. econstructor. econstructor. constructor. apply Hlenv_y. simpl. constructor. simpl. constructor.
        constructor. (* assumption 2 *) eauto. reflexivity.
        eapply t_trans. constructor.

        eapply step_external_function.
        apply H_isPtr_ptr.

        (* return *)
        eapply t_trans. constructor. constructor. eapply t_trans. constructor. constructor.

        (* if-then-else *)
        eapply t_trans. constructor. econstructor. constructor. unfold set_opttemp. rewrite M.gss. reflexivity. simpl. constructor.
        simpl. rewrite Int.eq_false. simpl.

      (* switch to the right case *)
      eapply t_trans. constructor. econstructor. simpl. econstructor. econstructor. constructor.
      econstructor. econstructor. constructor.
      rewrite M.gso. apply Hlenv_y.
      (* caseIdent is protected *)
      {
        destruct Hp_id as [Hp_id1 Hp_id2].
        intro; eapply Hp_id1; eauto.
        inList.
      }
      constructor. constructor.  constructor. eapply  deref_loc_value. simpl. reflexivity.
      simpl. rewrite Ptrofs.sub_add_opp in H6.
      unfold Ptrofs.of_int64. rewrite ptrofs_of_int64.
      rewrite Ptrofs.mul_mone. rewrite sizeof_val. eauto.
      apply eval_cint.
      simpl.
      assert (  sem_and (make_vint h) uval (make_vint 255) (typeof (make_cint 255 uval)) m = Some (int_and h 255)). {
        unfold sem_and. unfold int_and. chunk_red; archi_red; auto.
      }
      apply H. simpl.
      apply sem_switch_and_255.
      eapply repr_boxed_header_range; eauto.
      rewrite H_seq.
      eapply t_trans.
      constructor.  constructor.
      constructor. constructor.
      intro. inv H.
    }
    destruct Hstep_case as [vbool [s [s' [Hstep_case H_repr_es]]]].

    (* building up the IHHev to use after Hstep_case *)
    assert (H_cenv_e: correct_envs cenv ienv rep_env rho e).
    {
      eapply correct_envs_subterm; eauto.
      constructor. eapply dsubterm_case.
      apply findtag_In. eauto.
    }
    assert (Hp_id_e: protected_id_not_bound_id rho e).
    {
      inv Hp_id.
      split; intros.
      apply H; eauto.
      intro.
      eapply H2. apply H3.
      econstructor. apply H5.
      apply findtag_In. eauto.
    }
    assert (H_rho_id_e:  unique_bindings_env rho e).
    { inv Hrho_id.
      split.
      - assert (Hcase := shrink_cps_correct.ub_case_inl).
        specialize (Hcase ctx.Hole_c). simpl in Hcase.
        eapply Hcase; eauto.
      - intros. apply H2 in H3.
        destruct H3; split; auto.
        intro.
        apply H3.
        eapply Bound_Ecase; eauto.
        eapply findtag_In; eauto.
    }
    assert (Hf_id_e: functions_not_bound p rho e).
    {
      eapply functions_not_bound_subterm.
      eauto.
      econstructor.
      econstructor. apply findtag_In; eauto.
    }
    assert (Hca_e : correct_alloc e (Z.of_nat (max_allocs e))).
    unfold correct_alloc. reflexivity.
    assert (Hmem_e : rel_mem_LambdaANF_Codegen_id fenv finfo_env p rep_env e rho m  (Maps.PTree.set caseIdent vbool lenv)).
    {
      inv Hc_tinfo; destructAll.
      exists L.
      split.
      -  eapply protected_not_in_L_set.
         auto.
        apply is_protected_not_tinfo. inList.
        intro.   assert (Hnd := disjointIdent). inv Hnd.
        replace [allocIdent; limitIdent; gcIdent; mainIdent; bodyIdent;
          threadInfIdent; tinfIdent; heapInfIdent; numArgsIdent;
          numArgsIdent; isptrIdent; tinfIdent] with ([allocIdent; limitIdent; gcIdent; mainIdent; bodyIdent;
          threadInfIdent]++[tinfIdent; heapInfIdent; numArgsIdent;
          numArgsIdent; isptrIdent; tinfIdent]) in * by reflexivity. apply NoDup_cons_r in H23. inversion H23. apply H24; inList.
      - intros.
        specialize (Hmem_rel x7). destruct Hmem_rel as [Hmem_rel Hmem_rel'].
        split; intros.

        assert (occurs_free (Ecase y cl) x7).
        eapply occurs_free_Ecase_Included.
        apply findtag_In. eauto. auto.

        apply Hmem_rel in H20.
        destruct H20 as [v6 [Hx4v6 Hrepr_v6]].
        exists v6. split; auto.
        apply repr_val_id_set. auto.
        inv Hp_id_e.
        eapply H20 in Hx4v6.
        intro. apply Hx4v6. left. apply H22.
        inList.

        specialize (Hmem_rel' _ _ _ _ H19 H20).
        destruct Hmem_rel' as [Hmem_rel' Hmem_f].
        split. 2: auto.
        apply repr_val_id_set. auto.
        intro. inv Hp_id. eapply H22. apply H19. 2:{ right.
        eapply bound_var_subval; eauto.
        inv Hmem_rel'.
        inv H31.
        constructor.
        apply name_in_fundefs_bound_var_fundefs.
        eapply find_def_name_in_fundefs. eauto.
        inv H25. rewrite H33 in H21. inv H21. }
        inList.

    }
    assert (H_tinfo_e: correct_tinfo p  (Z.of_nat (max_allocs e))
                           (Maps.PTree.set caseIdent vbool lenv) m ).
    {
      apply correct_tinfo_not_protected.
      eapply correct_tinfo_mono; eauto.
      split. omega.
      inv Hc_alloc.
      apply inj_le.
      eapply max_allocs_case.
      apply findtag_In. eauto.
      intro.
      assert (Hdj:=disjointIdent).
      inv Hdj.
      inv H. clear H2.
      inv H6. apply H3; inList.
      destruct H2; subst.
      clear H. inv H6. inv H7. apply H6; inList.
      clear H.
      apply H5; inList.
      assert (Hdj:=disjointIdent).
      inv Hdj.
      intro. inv H5. clear H.  inv H8.
      inv H6. inv H9. inv H10. inv H11. inv H12. apply H11.
      inList.
    }

    specialize (IHHev H_cenv_e Hp_id_e H_rho_id_e Hf_id_e _ _ _ (Kseq Sbreak (Kseq s' (Kswitch k))) _ fu H_repr_es Hmem_e Hca_e H_tinfo_e).

    destruct IHHev as [m' [lenv' [Hstep_end [Hargs1 Hargs2]]]].
    exists m', lenv'.
    split; auto.

    (* step to e, then IH *)
    eapply t_trans.
    apply Hstep_case.
    eapply t_trans.
    apply Hstep_end.

    (* break back to k *)
    eapply t_trans.
    constructor. constructor.
    eapply t_trans.
    constructor. constructor.
    constructor.
    constructor. auto.
    split; auto.
    unfold same_args_ptr in *. rewrite <- Hargs1.
    rewrite M.gso; auto.
    assert (H_dj := disjointIdent). inv H_dj.
    intro; apply H3; subst; inList.
  - (* Eapp  *)  (* CHANGE THIS *)

    (* need assumption that unique_binding_env -> done! and functions_not_bound is preserved by all closures (rho', e) in rho - DONE *)
    (* Show protected_id_not_bound_id is preserved by prefixes - done *)
    (* also need to should that correct_cenv_of_exp is respected for all constructors found DONE! *)
    (* > new max_alloc is correct_alloc for e *)
    (* > tinfo is updated to reflect the max_alloc of e *)
    (* IH will be on Hev with rho'' |- e -> v. Need to show that rho' is a sufficient prefix of rho, and create a related mem *)


    (* show that tinfo -> argsIdent is some pointer to the right thing, and then that
  rel_mem_LambdaANF_Codegen_id fenv finfo_env p rep_env e  rho (M.set argsIdent ( m) lenv *)
    destruct inf as [n ind].
    unfold ctor_tag in t.
    set (bys := firstn nParam ys).
    set (ays := skipn nParam ys).
    set (aind := skipn nParam ind).
    set (bind := firstn nParam ind).
    assert (bysEq : bys = firstn nParam ys) by reflexivity.
    assert (aysEq : ays = skipn nParam ys) by reflexivity.
    assert (aindEq : aind = skipn nParam ind) by reflexivity.
    assert (bindEq : bind = firstn nParam ind) by reflexivity.

    inv H10.

    assert (Hrepr : repr_asgn_fun' argsIdent threadInfIdent nParam fenv finfo_env p ays aind s) by apply H3.
    clear H3.

    assert (Hcall : repr_call_vars threadInfIdent nParam fenv finfo_env p (Init.Nat.min (N.to_nat n) nParam) bys s2) by apply H13.
    clear H13.

    destruct Hpinv as [Hpinv_ptr [Hpinv_tinfo Hpinv_gc]].
    destruct Hpinv_tinfo as [co [Hget_tinfident Htinfident_members]].

    (* get more info about the function *)
    assert (Hrel' := Hrel_m).
    destruct Hrel' as [L [Hrel_p Hrel_m']].
    specialize (Hrel_m' f).
    destruct Hrel_m' as [Hrel_of Hrel_fun].

    assert (Hsubval : subval_or_eq (Vfun rho' fl f') (Vfun rho' fl f')) by apply rt_refl.

    specialize (Hrel_fun rho' fl f' _ H Hsubval).
    destruct Hrel_fun as [Hrepr_f [Hclosed_f Hfundef_f]].
    destruct Hfundef_f as [finfo [t' [t'' [vs' [e' [Hfind_def_f' [Hfinfo_env_f' [Hfundef_tag' Hfundef_f']]]]]]]].
    rewrite Hfind_def_f' in H1. inversion H1. subst. clear H1. clear Hsubval.

    destruct Hfundef_f' as [n' [l' [b' [fi_0 [Hf_fenv [Hnl [Hlvs [Hl_nodub [Hinf1 [Hfind_symbol [Hload_fi0 [Hload_fi1 [Hcorrect_alloc [Hgc_size_fi0 Hforall_l_fi]]]]]]]]]]]]]].
    rewrite Hf_fenv in H6. inv H6.
    rewrite Nnat.Nat2N.id in Hcall.

    (* break apart the tinfo *)
    assert (Hc_tinfo' := Hc_tinfo).
    destruct Hc_tinfo as [alloc_b [alloc_ofs [limit_ofs [args_b [args_ofs [tinf_b [tinf_ofs [Hget_alloc [Hdiv_alloc [Hrange_alloc [Hget_limit [Hbound_limit [Hget_args [Hdj_args [Hbound_args [Hrange_args [Hget_tinf [Htinfne1 [Htinfne2 [Hinfo_limit [Hloc_args Hglobals]]]]]]]]]]]]]]]]]]]]].
    destruct Hbound_limit as [Hbound_limit Hbound_gc_size].
    rewrite <- Z.le_add_le_sub_l in Hbound_limit.

    remember (Kseq
                (Sassign
                   (Efield
                      (Ederef (Etempvar tinfIdent (Tpointer (Tstruct threadInfIdent noattr) noattr)) (Tstruct threadInfIdent noattr))
                      allocIdent valPtr) (Etempvar allocIdent valPtr))
                (Kseq
                   (Sassign
                      (Efield
                         (Ederef (Etempvar tinfIdent (Tpointer (Tstruct threadInfIdent noattr) noattr)) (Tstruct threadInfIdent noattr))
                         limitIdent valPtr) (Etempvar limitIdent valPtr))
                   (Kseq
                      (Scall None (Ecast (var_or_funvar_f threadInfIdent nParam fenv finfo_env p f)
                                         (Tpointer (mkFunTy threadInfIdent (Init.Nat.min (N.to_nat (fst (N.of_nat (length ind), ind))) nParam)) noattr))
                             (Etempvar tinfIdent (Tpointer (Tstruct threadInfIdent noattr) noattr) :: s2)) k))) as k'.

    remember (Maps.PTree.set argsIdent (Vptr args_b args_ofs) lenv) as  lenv'.
    assert (Hlenv' : (Maps.PTree.set argsIdent (Vptr args_b args_ofs) lenv) = lenv) by (apply  Maps.PTree.gsident; auto).
    assert (Hrel_m' : rel_mem_LambdaANF_Codegen_id fenv finfo_env p rep_env  (Eapp f t ys) rho m lenv'). {
      rewrite Heqlenv'. rewrite Hlenv'. auto.
    }

    assert (Hys: Forall (fun x => exists v, get_var_or_funvar p lenv x v) ys). {
      apply Forall_forall. intros.
      assert (Hgl := get_list_In _ _ _ _ H0 H1).
      destruct Hgl. destruct Hrel_m. destructAll. specialize (H5 x). destruct H5.
      assert ( occurs_free (Eapp f t ys) x). constructor. auto.
      specialize (H5 H7). inv H5. destruct H8. rewrite H5 in H3. inv H3.
      inv H8. eexists. constructor. eauto.
      eexists. constructor 2. eauto. eauto. inv H10; auto.
    }
    assert (HInFirstn : forall {A} n x (l : list A) , List.In x (firstn n l) -> List.In x l). (* TODO : move out *)
    {
      intros A n x l Hl.
      erewrite <- firstn_skipn.
      eapply in_or_app. eauto.
    }
    assert (HInSkipn : forall {A} n x (l : list A) , List.In x (skipn n l) -> List.In x l). (* TODO : move out *)
    {
      induction n; intros. assumption.
      induction l. inv H1.
      simpl in H1.
      specialize (IHn x l H1).
      right. assumption.
    }
    assert (HFirstnLength : forall {A B} n (l1 : list A) (l2 : list B), length l1 = length l2 -> length (firstn n l1) = length (firstn n l2)). (* TODO : move out *)
    {
      intros A B n l1. generalize n. clear n. induction l1; intros n l2 Hlen; destruct l2; [ | inv Hlen | inv Hlen | ].
      + destruct n; reflexivity.
      + inv Hlen. destruct n. reflexivity.
        simpl. apply f_equal.
        auto.
    }
    assert (HSkipnLength : forall {A B} n (l1 : list A) (l2 : list B), length l1 = length l2 -> length (skipn n l1) = length (skipn n l2)). (* TODO : move out *)
    {
      intros A B n l1. generalize n. clear n. induction l1; intros n l2 Hlen; destruct l2; [ | inv Hlen | inv Hlen | ].
      + destruct n; reflexivity.
      + inv Hlen. destruct n.
        * simpl. apply f_equal. auto.
        * simpl. apply IHl1; auto.
    }
    assert (Hbys : Forall (fun x : positive => exists v : Values.val, get_var_or_funvar p lenv x v) bys).
    {
      apply Forall_forall. intros.
      apply (proj1 (Forall_forall _ ys) Hys x).
      rewrite bysEq in H1. eapply HInFirstn. eauto.
    }
    assert (Hays : Forall (fun x : positive => exists v : Values.val, get_var_or_funvar p lenv x v) ays).
    {
      apply Forall_forall. intros.
      apply (proj1 (Forall_forall _ ys) Hys x).
      rewrite aysEq in H1. eapply HInSkipn. eauto.
    }
    assert (Haind :  Forall (fun i : N => (0 <= Z.of_N i < max_args)%Z) aind).
    {
      apply Forall_forall. intros.
      apply (proj1 (Forall_forall _ ind) Hinf1 x).
      rewrite aindEq in H1. eapply HInSkipn. eauto.
    }
    assert (Hbind :  Forall (fun i : N => (0 <= Z.of_N i < max_args)%Z) bind).
    {
      apply Forall_forall. intros.
      apply (proj1 (Forall_forall _ ind) Hinf1 x).
      rewrite bindEq in H1. eapply HInFirstn. eauto.
    }
    assert (Haind_nodup : NoDup aind).
    {
      rewrite aindEq.
      eapply NoDup_cons_r.
      rewrite (firstn_skipn nParam ind).
      assumption.
    }
    assert (Hbind_nodup : NoDup bind).
    {
      rewrite bindEq.
      eapply NoDup_cons_l.
      rewrite (firstn_skipn nParam ind).
      assumption.
    }

    assert (Hasgn_fun_mem :=  repr_asgn_fun_mem fu lenv p rho (Eapp f t ys) fenv max_alloc rep_env finfo_env ays aind s m Hsym HfinfoCorrect Hrel_m Hc_tinfo' Hays Haind Haind_nodup Hrepr).
    destruct Hasgn_fun_mem as [m2 [Hasgn_fun_mem [Hmem_of_asgn Hrel_mem]]].
    specialize (Hasgn_fun_mem k').
    (* lenv' := (Maps.PTree.set argsIdent (Vptr args_b args_ofs) lenv) *)
    (* k := (Kseq
          (Sassign
             (Efield
                (Ederef (Etempvar tinfIdent (Tpointer (Tstruct threadInfIdent noattr) noattr)) (Tstruct threadInfIdent noattr))
                allocIdent valPtr) (Etempvar allocIdent valPtr))
          (Kseq
             (Scall None
                (Ecast
                   (Evar f
                      (Tfunction (Tcons (Tpointer (Tstruct threadInfIdent noattr) noattr) Tnil) Tvoid
                         {| cc_vararg := false; cc_unproto := false; cc_structret := false |}))
                   (Tpointer
                      (Tfunction (Tcons (Tpointer (Tstruct threadInfIdent noattr) noattr) Tnil) Tvoid
                         {| cc_vararg := false; cc_unproto := false; cc_structret := false |}) noattr))
                [Etempvar tinfIdent (Tpointer (Tstruct threadInfIdent noattr) noattr)]) k)) *)


    (* m3 saves the value of alloc_ofs into the tinfo *)

    assert (Hm3 : Mem.valid_access m2 int_chunk tinf_b (Ptrofs.unsigned tinf_ofs) Writable). {
      destruct Hrel_mem. inv H3. destructAll. rewrite H12 in Hget_tinf; inv Hget_tinf. specialize (H15 0%Z). rewrite Ptrofs.add_zero in H15. eapply H15. omega.
    }
    eapply Mem.valid_access_store with (v := (Vptr alloc_b alloc_ofs)) in Hm3.
    destruct Hm3 as [m3 Hm3].

    (* m4 saves the value of limit_ofs into tinfo *)
    assert (Hm4 : Mem.valid_access m3 int_chunk tinf_b (Ptrofs.unsigned (Ptrofs.add tinf_ofs (Ptrofs.repr int_size))) Writable). {
      eapply Mem.store_valid_access_1.
      eauto.
      destruct Hrel_mem. inv H3. destructAll.
      rewrite H12 in Hget_tinf; inv Hget_tinf.
      specialize (H15 1%Z). simpl in H15. eapply H15. omega.
    }
    eapply Mem.valid_access_store with (v := (Vptr alloc_b limit_ofs)) in Hm4.
    destruct Hm4 as [m4 Hm4].
    destruct Hrel_mem as [Hrel_mem2 Hc_tinfo_m2].

    assert (Hrel_mem3 :  rel_mem_LambdaANF_Codegen_id fenv finfo_env p rep_env (Eapp f t ys) rho m3 lenv). {
      inv Hrel_mem2.
      exists x.
      assert (Mem.unchanged_on x m2 m3). {
        (* protected not in x *)
        destruct H1. eapply Mem.store_unchanged_on; eauto.
        intros.
        inv H1. destructAll. rewrite H10 in Hget_tinf; inv Hget_tinf. apply H11.
      }
      destructAll.
      split; auto. intro. specialize (H4 x0).
      destruct H4.
      split. intro. apply H4 in H6.
      destructAll.
      exists x1. split; auto.
      apply repr_val_id_L_unchanged with (m := m2); eauto.
      intros. specialize (H5 _ _ _ _ H6 H7).
      destruct H5. destruct H8 as [Hclosed H8].
      split; auto.
      apply repr_val_id_L_unchanged with (m := m2); eauto.
      (* tinf_b disjoint from global *)  split; auto.
      eapply correct_fundefs_unchanged_global.
      eauto.
      eapply store_globals_unchanged.
      eauto.
      intros.
      specialize (Hglobals _ _ H9). destructAll; auto.
    }

    assert (Hrel_mem4 :  rel_mem_LambdaANF_Codegen_id fenv finfo_env p rep_env (Eapp f t ys) rho m4 lenv). {
      inv Hrel_mem3.
      exists x.
      assert (Mem.unchanged_on x m3 m4). {
        destruct H1. eapply Mem.store_unchanged_on; eauto.
        intros.
        inv H1. destructAll. rewrite H10 in Hget_tinf; inv Hget_tinf. apply H11.
      }
      destructAll.
      split; auto. intro. specialize (H4 x0).
      destruct H4.
      split. intro. apply H4 in H6.
      destructAll.
      exists x1. split; auto.
      apply repr_val_id_L_unchanged with (m := m3); eauto.
      intros. specialize (H5 _ _ _ _ H6 H7).
      destruct H5. destruct H8 as [Hclosed H8].
      split; auto.
      apply repr_val_id_L_unchanged with (m := m3); eauto.
      (* tinf_b disjoint from global *) split; auto.
      eapply correct_fundefs_unchanged_global.
      eauto.
      eapply store_globals_unchanged.
      eauto.
      intros.
      specialize (Hglobals _ _ H9). destructAll; auto.
    }

    assert (Hc_tinfo_m4 :  correct_tinfo p max_alloc lenv m4). {
      eapply correct_tinfo_after_store.
      eapply correct_tinfo_after_store.
      apply Hc_tinfo_m2.
      eauto.
      eauto.
    }

    assert (exists b,
               (repr_val_LambdaANF_Codegen_thm fenv finfo_env p rep_env (term.Vfun (M.empty term.val) fl f') m4 (Vptr b Ptrofs.zero)) /\
(*               Genv.find_symbol (globalenv p) f' = Some b /\ *)
               eval_expr (globalenv p) empty_env lenv m4
                         (Ecast (var_or_funvar_f threadInfIdent nParam fenv finfo_env p f)
                                (Tpointer
                                   (mkFunTy threadInfIdent (Init.Nat.min (length ind) nParam)) noattr)) (Vptr b Ptrofs.zero)). {
      inv Hrel_mem4. destruct H1. specialize (H3 f). destruct H3.
      assert ( occurs_free (Eapp f t ys) f) by constructor.
      specialize (H3 H5).
      destruct H3. destruct H3. rewrite H3 in H. inv H.
      inv H6.
      - exists b. split; auto.
        inv H14; econstructor; eauto.
        unfold var_or_funvar_f. rewrite H13.
        specialize (Hsym f). inv Hsym.
        destruct (H6 (ex_intro _ b H13)). destruct x0.
        unfold makeVar. rewrite H7.
        specialize (HfinfoCorrect _ _ _ H7). inv HfinfoCorrect.
        destruct x0. rewrite H8.
        econstructor. econstructor.
        constructor 2. apply M.gempty. eauto. constructor. constructor.
        auto.
      - admit. (* inv H8. exists b. split. auto.
        econstructor; eauto.
        unfold var_or_funvar_f. rewrite H. econstructor. econstructor.
        eauto. constructor.*)
    }
    destruct H1 as [bf' [Hfind_f' Heval_f']].
    inv Hfind_f'.


    rewrite  Hfind_def_f' in H5; inv H5.
    rewrite Hf_fenv in H6; inv H6.

    (* clear old assumptions about m and get them about m4 instead *)
    clear Hload_fi0 Hload_fi1.
    assert (Hrel_mem4' := Hrel_mem4).
    destruct Hrel_mem4' as [Lm4 [Hrel_pm4 Hrel_rho_m4]].
    assert (Hrel_rho_m4f := Hrel_rho_m4 f).
    destruct Hrel_rho_m4f as [_  Hrel_fun_m4].
    assert (Hsubval : subval_or_eq (Vfun rho' fl f') (Vfun rho' fl f')) by apply rt_refl.

    specialize (Hrel_fun_m4 rho' fl f' _ H Hsubval).
    destruct Hrel_fun_m4 as [Hrepr_f_m4 [Hclosed_f_m4 Hfundef_f_m4]].
    clear Hsubval.
    destruct Hfundef_f_m4 as [finfom4 [tm4 [tm4' [vsm4 [e4 [Hbd_f' [Hget_finfo [hfundef_tag' Hfundef_f']]]]]]]].
    rewrite Hfind_def_f' in Hbd_f'; inv Hbd_f'.

    destruct Hfundef_f' as [nm4 [lm4 [bm4 [fi_0_m4  [_ [_ [_ [_ [_ [Hfind_symbol_m4 [Hload_fi0 [Hload_fi1 [Hcorrect_alloc_m4 [Hgc_size_fi0m4 _]]]]]]]]]]]]]].
    rewrite  Hfinfo_env_f' in Hget_finfo. inv Hget_finfo.

    rewrite Hfind_symbol in Hfind_symbol_m4. inv Hfind_symbol_m4.

    assert (repr_asgn_fun_length : forall ys ind s,
               repr_asgn_fun' argsIdent threadInfIdent nParam fenv finfo_env p ys ind s -> length ys = length ind). (* TODO : Move out *)
    {
      intro ys0. induction ys0; intros ind s' Hr; destruct ind; [ | inv Hr | inv Hr | ].
      - reflexivity.
      - simpl. apply f_equal. inv Hr. apply (IHys0 _ _ H8).
    }
    assert (ays_aind_length : length ays = length aind).
    { eapply repr_asgn_fun_length. apply Hrepr. }
    assert (bys_bind_length : length bys = length bind).
    { eapply repr_call_vars_length1. rewrite bindEq.
      rewrite firstn_length. rewrite Nat.min_comm. apply Hcall. }

    set (bvsm4 := firstn nParam vsm4).
    set (avsm4 := skipn nParam vsm4).
    assert (bvsm4Eq : bvsm4 = firstn nParam vsm4) by reflexivity.
    assert (avsm4Eq : avsm4 = skipn nParam vsm4) by reflexivity.

    assert (bys_bvsm4_length : length bys = length bvsm4).
    {
      rewrite bvsm4Eq. Set Printing All.
      simpl. unfold var , term.M.elt.
      rewrite <- (HFirstnLength _ _ nParam _ _ Hlvs).
      rewrite <- bindEq.
      Unset Printing All. simpl.
      apply bys_bind_length.
    }

    (* lenv_new is just lenv from fentry *)

    remember (create_undef_temps (skipn nParam vars ++ gc_vars argsIdent allocIdent limitIdent caseIdent)) as lenv_new''.

    set (lenv_new' := mk_gc_call_env p bys bvsm4 lenv lenv_new'' Hbys bys_bvsm4_length).
    assert (lenv_newEq' : lenv_new' = mk_gc_call_env p bys bvsm4 lenv lenv_new'' Hbys bys_bvsm4_length) by reflexivity.

    set (lenv_new := Maps.PTree.set tinfIdent (Vptr tinf_b tinf_ofs) lenv_new').
    assert (lenv_newEq : lenv_new = Maps.PTree.set tinfIdent (Vptr tinf_b tinf_ofs) lenv_new') by reflexivity.
    (* show that after the branch, some memory m5 will be correct and contain enough space to execute the body *)
    (* need to construct the memory and environment that exists after the (potential) gc call
    > every function has a code_info which points to the total number of alloc

     *)
    assert (Hc_alloc' : exists max_alloc',  correct_alloc e4 max_alloc') by apply e_correct_alloc.
    destruct Hc_alloc' as [max_alloc' Hc_alloc'].

    assert (rho' = M.empty _). { inv Hrepr_f_m4. reflexivity. inv H4. reflexivity. } rewrite H1 in *. clear H1.



    assert (Hvs := mem_of_asgn_exists_v Hmem_of_asgn Hget_args).
    destruct Hvs as [avs7 Hvs7].


    assert (Hnd_vs0: NoDup vsm4). {
      destruct Hrho_id as [Hrho_id1 Hrho_id2].
      apply Hrho_id2 in H.
      destruct H as [_ Hub].
      inv Hub.
      eapply shrink_cps_correct.ub_find_def_nodup; eauto.
    }
    assert (Hnoprot_vs0:  (forall x : positive, List.In x vsm4 -> ~ (is_protected_tinfo_id argsIdent allocIdent limitIdent x \/ x = tinfIdent))). {
                intros.
                inv Hp_id.
                intro.
                eapply H3 with (y := x) in H.
                apply H.
                right. constructor.
                eapply shrink_cps_correct.name_boundvar_arg; eauto.
                inv H5.
                apply is_protected_tinfo_weak; auto.
                inList. }

    assert (Hnoargs_vs0: ~ List.In argsIdent vsm4).
    {
      intro.
      eapply Hnoprot_vs0.
      eauto.
      left; inList.
      reflexivity.
    }

    assert (Hnotinf_vs0: ~ List.In tinfIdent vsm4).
    {
      intro.
      eapply Hnoprot_vs0.
      eauto.
      right.
      reflexivity.
    }

(* TODO: do something with bvs7, lenv, lenv_new, bys, and bvsm4 *)

(*
    assert (Hl_temp: length vsm4 = length vs7). {

      eapply mem_of_asgn_v_length in Hvs7.
      rewrite <- Hvs7.
      auto.
    }
    assert (Hvs7_m4 : mem_after_asgn args_b args_ofs m4 aind avs7). {
      assert (Hdj := disjointIdent).
      eapply mem_of_asgn_after. Print mem_of_asgn_after.
      apply aindEq. apply aysEq. apply avs7eq.
      eapply mem_of_asgn_v_store.
      eapply mem_of_asgn_v_store.
      eauto. eauto.
      solve_nodup.
      eauto.
      solve_nodup.
    } *)
    (* MAIN CHANGE: This is stepping through the function call, stitch together function arguments.
               Need to update memory state proof to account for the reading/writing with args around gc call *)

    (*
    set (bind := firstn nParam locs).
    assert (bindEq : bind = firstn nParam locs) by reflexivity.
    assert (Hgc : exists s ,
               match asgnAppVars'' argsIdent threadInfIdent ays aind fenv with
               | Some bef =>
                 match asgnFunVars' argsIdent bys bind with
                 | Some aft =>
                   Some
                     (Sifthenelse
                        (not
                           (Ebinop Ole
                                   (Ederef
                                      (Evar finfo0 (Tarray LambdaANF_to_Clight.uval (Z.of_N (N.of_nat (length locs) + 2)) noattr))
                                      LambdaANF_to_Clight.uval)
                                   (sub
                                      (Efield
                                         (Ederef (Etempvar tinfIdent (Tpointer (Tstruct threadInfIdent noattr) noattr))
                                                 (Tstruct threadInfIdent noattr)) limitIdent valPtr)
                                      (Efield
                                         (Ederef (Etempvar tinfIdent (Tpointer (Tstruct threadInfIdent noattr) noattr))
                                                 (Tstruct threadInfIdent noattr)) allocIdent valPtr)) type_bool))
                        (Ssequence
                           (Ssequence bef
                                      (Scall None
                                             (Evar gcIdent
                                                   (Tfunction
                                                      (Tcons (Tpointer uval noattr)
                                                             (Tcons (Tpointer (Tstruct threadInfIdent noattr) noattr) Tnil)) Tvoid
                                                      {| cc_vararg := false; cc_unproto := false; cc_structret := false |}))
                                             [Evar finfo0 (Tarray LambdaANF_to_Clight.uval (Z.of_N (N.of_nat (length locs) + 2)) noattr);
                                              Etempvar tinfIdent (Tpointer (Tstruct threadInfIdent noattr) noattr)])) aft) Sskip)
                 | None => None
                 end
               | None => None
               end = Some s). {
     *)

(*
    set (bvsm4 := firstn nParam vsm4).
    assert (bvsm4Eq : bvsm4 = firstn nParam vsm4) by reflexivity.
    assert(firstnLengthEq : forall {A B} n (l1 : list A) (l2 : list B), length l1 = length l2 -> length (firstn n l1) = length (firstn n l2)).
    {
      intros A B n l1. generalize n. clear n. induction l1; destruct l2; intros Heq; inv Heq.
      + destruct n; reflexivity.
      + destruct n. auto.
        simpl.
        apply f_equal. apply IHl1. auto.
    }
    assert (bindLengthEq : length bind = length bvsm4).
    {
      rewrite bindEq. rewrite bvsm4Eq.
      apply firstnLengthEq. assumption.
    }
    assert(lengthAsgnFun : forall l1 l2, length l1 = length l2 -> exists s, asgnFunVars' argsIdent l1 l2 = Some s).
    {
      induction l1; intros l2 lEq; destruct l2; inv lEq.
      - eexists. reflexivity.
      - apply IHl1 in H3. inv H3.
        eexists. simpl.
        rewrite H1. reflexivity.
    }
    assert (HgcAsgn : exists gcAsgn, asgnFunVars' argsIdent bvsm4 bind = Some gcAsgn).
    {
      apply lengthAsgnFun. auto.
    }
    destruct HgcAsgn as [gcAsgn gcAsgnEq].

    Forall (fun x : positive => exists v : Values.val, get_var_or_funvar p lenv x v) bvsm4
    assert (Hasgn_gc_fun_mem :=  repr_asgn_fun_mem fu lenv p rho (Eapp f t ys) fenv max_alloc rep_env finfo_env ays aind s0 m Hsym Hrel_m Hc_tinfo' Hays Haind Haind_nodup Hrepr). *)
    assert (Hgcbef : exists bef, asgnAppVars'' argsIdent threadInfIdent nParam (firstn nParam vsm4) (firstn nParam locs) fenv finfo_env = Some bef).
    {
      unfold gc_test' in H9. unfold reserve' in H9.
      remember (asgnAppVars'' argsIdent threadInfIdent nParam (firstn nParam vsm4) (firstn nParam locs) fenv finfo_env) as bef.
      assert (match bef with
              | Some bef =>
                match asgnFunVars' argsIdent (firstn nParam vsm4) (firstn nParam locs) with
                | Some aft =>
                  Some
                    (Sifthenelse
                       (not
                          (Ebinop Ole (Ederef (Evar finfo0 (Tarray LambdaANF_to_Clight.uval (Z.of_N (N.of_nat (length locs) + 2)) noattr)) LambdaANF_to_Clight.uval)
                                  (sub (Efield (Ederef (Etempvar tinfIdent (Tpointer (Tstruct threadInfIdent noattr) noattr)) (Tstruct threadInfIdent noattr)) limitIdent valPtr)
                                       (Efield (Ederef (Etempvar tinfIdent (Tpointer (Tstruct threadInfIdent noattr) noattr)) (Tstruct threadInfIdent noattr)) allocIdent valPtr))
                                  type_bool))
                       (Ssequence
                          (Ssequence bef
                                     (Scall None
                                            (Evar gcIdent
                                                  (Tfunction (Tcons (Tpointer uval noattr) (Tcons (Tpointer (Tstruct threadInfIdent noattr) noattr) Tnil)) Tvoid
                                                             {| cc_vararg := false; cc_unproto := false; cc_structret := false |}))
                                            [Evar finfo0 (Tarray LambdaANF_to_Clight.uval (Z.of_N (N.of_nat (length locs) + 2)) noattr);
                                             Etempvar tinfIdent (Tpointer (Tstruct threadInfIdent noattr) noattr)])) aft) Sskip)
                | None => None
                end
              | None => None
              end = Some gccall).
      { rewrite Heqbef. assumption. }
      destruct bef.
      + exists s0. auto.
      + inv H1.
    }
    assert (Hgcaft : exists aft, asgnFunVars' argsIdent (firstn nParam vsm4) (firstn nParam locs) = Some aft).
    {
      unfold gc_test' in H9. unfold reserve' in H9.
      remember (asgnFunVars' argsIdent (firstn nParam vsm4) (firstn nParam locs)) as aft.
      assert (match asgnAppVars'' argsIdent threadInfIdent nParam (firstn nParam vsm4) (firstn nParam locs) fenv finfo_env with
              | Some bef =>
                match aft with
                | Some aft =>
                  Some
                    (Sifthenelse
                       (not
                          (Ebinop Ole (Ederef (Evar finfo0 (Tarray LambdaANF_to_Clight.uval (Z.of_N (N.of_nat (length locs) + 2)) noattr)) LambdaANF_to_Clight.uval)
                                  (sub (Efield (Ederef (Etempvar tinfIdent (Tpointer (Tstruct threadInfIdent noattr) noattr)) (Tstruct threadInfIdent noattr)) limitIdent valPtr)
                                       (Efield (Ederef (Etempvar tinfIdent (Tpointer (Tstruct threadInfIdent noattr) noattr)) (Tstruct threadInfIdent noattr)) allocIdent valPtr))
                                  type_bool))
                       (Ssequence
                          (Ssequence bef
                                     (Scall None
                                            (Evar gcIdent
                                                  (Tfunction (Tcons (Tpointer uval noattr) (Tcons (Tpointer (Tstruct threadInfIdent noattr) noattr) Tnil)) Tvoid
                                                             {| cc_vararg := false; cc_unproto := false; cc_structret := false |}))
                                            [Evar finfo0 (Tarray LambdaANF_to_Clight.uval (Z.of_N (N.of_nat (length locs) + 2)) noattr);
                                             Etempvar tinfIdent (Tpointer (Tstruct threadInfIdent noattr) noattr)])) aft) Sskip)
                | None => None
                end
              | None => None
              end = Some gccall).
      { rewrite Heqaft. assumption. }
      destruct aft.
      + exists s0. auto.
      + destruct (asgnAppVars'' argsIdent threadInfIdent nParam (firstn nParam vsm4) (firstn nParam locs) fenv); inv H1.
    }
    destruct Hgcbef as [bef Heqbef].
    destruct Hgcaft as [aft Heqaft].

    assert (Hgc : gc_test' argsIdent allocIdent limitIdent gcIdent threadInfIdent tinfIdent nParam finfo0 (N.of_nat (length locs)) vsm4 locs fenv finfo_env =
            Some
              (Sifthenelse
                 (not
                    (Ebinop Ole (Ederef (Evar finfo0 (Tarray LambdaANF_to_Clight.uval (Z.of_N (N.of_nat (length locs) + 2)) noattr)) LambdaANF_to_Clight.uval)
                            (sub (Efield (Ederef (Etempvar tinfIdent (Tpointer (Tstruct threadInfIdent noattr) noattr)) (Tstruct threadInfIdent noattr)) limitIdent valPtr)
                                 (Efield (Ederef (Etempvar tinfIdent (Tpointer (Tstruct threadInfIdent noattr) noattr)) (Tstruct threadInfIdent noattr)) allocIdent valPtr)) type_bool))
                 (Ssequence
                    (Ssequence bef
                               (Scall None
                                      (Evar gcIdent
                                            (Tfunction (Tcons (Tpointer uval noattr) (Tcons (Tpointer (Tstruct threadInfIdent noattr) noattr) Tnil)) Tvoid
                                                       {| cc_vararg := false; cc_unproto := false; cc_structret := false |}))
                                      [Evar finfo0 (Tarray LambdaANF_to_Clight.uval (Z.of_N (N.of_nat (length locs) + 2)) noattr); Etempvar tinfIdent (Tpointer (Tstruct threadInfIdent noattr) noattr)])) aft)
                 Sskip)).
    { unfold gc_test'. unfold reserve'. Set Printing All. simpl.
      unfold var , term.M.elt in Heqbef.
      unfold var , term.M.elt in Heqaft.
      rewrite Heqbef. rewrite Heqaft.
      Unset Printing All. simpl.
      reflexivity.
    }
    assert (Hgccalleq : gccall = (Sifthenelse
                 (not
                    (Ebinop Ole (Ederef (Evar finfo0 (Tarray LambdaANF_to_Clight.uval (Z.of_N (N.of_nat (length locs) + 2)) noattr)) LambdaANF_to_Clight.uval)
                            (sub (Efield (Ederef (Etempvar tinfIdent (Tpointer (Tstruct threadInfIdent noattr) noattr)) (Tstruct threadInfIdent noattr)) limitIdent valPtr)
                                 (Efield (Ederef (Etempvar tinfIdent (Tpointer (Tstruct threadInfIdent noattr) noattr)) (Tstruct threadInfIdent noattr)) allocIdent valPtr)) type_bool))
                 (Ssequence
                    (Ssequence bef
                               (Scall None
                                      (Evar gcIdent
                                            (Tfunction (Tcons (Tpointer uval noattr) (Tcons (Tpointer (Tstruct threadInfIdent noattr) noattr) Tnil)) Tvoid
                                                       {| cc_vararg := false; cc_unproto := false; cc_structret := false |}))
                                      [Evar finfo0 (Tarray LambdaANF_to_Clight.uval (Z.of_N (N.of_nat (length locs) + 2)) noattr); Etempvar tinfIdent (Tpointer (Tstruct threadInfIdent noattr) noattr)])) aft)
                 Sskip)).
    {
      rewrite Hgc in H10. inv H10. reflexivity.
    }

    assert (rel_mem_gc : rel_mem_LambdaANF_Codegen_id fenv finfo_env p rep_env (Ehalt 1%positive) rho m4 lenv_new).
    {
      admit.
    }

    assert (Hbvsm4_nodup : NoDup bvsm4).
    {
      rewrite bvsm4Eq.
      eapply NoDup_cons_l.
      rewrite (firstn_skipn nParam vsm4).
      assumption.
    }

    assert (Havsm4_nodup : NoDup avsm4).
    {
      rewrite avsm4Eq.
      eapply NoDup_cons_r.
      rewrite (firstn_skipn nParam vsm4).
      assumption.
    }

    assert (Hvsm4 : Forall (fun x : positive => exists v : Values.val, get_var_or_funvar p lenv_new x v) bvsm4).
    {
      rewrite lenv_newEq.
      apply Forall_forall. intros.
      assert (Hcorrect := proj1 (Forall_forall _ _) (mk_gc_call_env_correct p bys bvsm4 lenv lenv_new'' Hbys bys_bvsm4_length Hbvsm4_nodup) x H1).
      rewrite <- lenv_newEq' in Hcorrect.
      destruct Hcorrect as [z Hz].
      exists z.
      eapply get_var_or_funvar_proper; eauto.
      unfold map_get_r_l. intros.
      symmetry. apply M.gso. intros veq. inv veq.
      rewrite bvsm4Eq in H3. apply HInFirstn in H3.
      apply Hnotinf_vs0. assumption.
    }

    assert (Hc_tinfo_m4_new : correct_tinfo p max_alloc lenv_new m4).
    {
      admit.
    }

    assert (Hrepr_gc : repr_asgn_fun' argsIdent threadInfIdent nParam fenv finfo_env p bvsm4 bind bef).
    {
      admit.
    }

    (*
    NEED:
      rel_mem_LambdaANF_Codegen_id fenv finfo_env p rep_env (Ehalt 1%positive) rho m4 lenv
      correct_tinfo p max_alloc lenv_new m4
      Forall (fun x : positive => exists v : Values.val, get_var_or_funvar p lenv x v) bvsm4
      repr_asgn_fun' argsIdent threadInfIdent nParam fenv p bvsm4 bind bef
     *)

    assert (Hasgn_fun_mem_bgc := repr_asgn_fun_mem fu lenv_new p rho (Ehalt 1%positive) fenv max_alloc rep_env finfo_env bvsm4 bind bef m4 Hsym HfinfoCorrect rel_mem_gc Hc_tinfo_m4_new Hvsm4 Hbind Hbind_nodup Hrepr_gc).
    destruct Hasgn_fun_mem_bgc as [mgc [Hasgn_fun_mem_bgc [Hmem_of_asgn_bgc Hrel_mem_bgc]]].

    assert (Hm_agc : exists magc lenv_new_agc,
               clos_trans state (traceless_step2 (globalenv p))
                          (State F
                                 (Ssequence bef
                                            (Scall None
                                                   (Evar gcIdent
                                                         (Tfunction (Tcons (Tpointer uval noattr) (Tcons (Tpointer (Tstruct threadInfIdent noattr) noattr) Tnil)) Tvoid
                                                                    {| cc_vararg := false; cc_unproto := false; cc_structret := false |}))
                                                   [Evar finfo0 (Tarray LambdaANF_to_Clight.uval (Z.of_N (N.of_nat (length locs) + 2)) noattr);
                                                    Etempvar tinfIdent (Tpointer (Tstruct threadInfIdent noattr) noattr)]))
                                 (Kseq (Ssequence aft Sskip) (Kseq  (Ssequence (Ssequence (gc_set argsIdent allocIdent limitIdent threadInfIdent tinfIdent) asgn) body)
                                                                    (Kcall None fu empty_env lenv k)))
                                       empty_env lenv_new m4)
                                 (State F
                                        Sskip
                                        (Kseq (Ssequence aft Sskip) (Kseq  (Ssequence (Ssequence (gc_set argsIdent allocIdent limitIdent threadInfIdent tinfIdent) asgn) body)
                                                                           (Kcall None fu empty_env lenv k)))
                                              empty_env lenv_new_agc magc) /\
                           same_tinf_ptr lenv_new lenv_new_agc /\
                           exists alloc_b alloc_ofs limit_ofs,
                             deref_loc (Tarray uval maxArgs noattr) magc tinf_b
                                       (Ptrofs.add tinf_ofs (Ptrofs.repr (int_size * 3)))
                                       (Vptr args_b args_ofs) /\
                             Mem.load int_chunk magc tinf_b
                                      (Ptrofs.unsigned tinf_ofs) = Some (Val.load_result int_chunk (Vptr alloc_b alloc_ofs)) /\
                             Mem.load int_chunk magc tinf_b
                                      (Ptrofs.unsigned (Ptrofs.add tinf_ofs (Ptrofs.repr int_size))) = Some (Val.load_result int_chunk (Vptr alloc_b limit_ofs))).
    {
      admit.
    }

    destruct Hm_agc as [macg [lenv_new_agc [Hmem_agc [Hptr_agc [alloc_b_agc [alloc_ofs_agc [limit_ofs_agc [Hderef_agc [Htinf_ofs_agc H_tinf_ofs_size_agc]]]]]]]]].

    assert (Hm5 : exists m5 lenv_new',
               clos_trans state (traceless_step2 (globalenv p))
                          (State F
                                 gccall
                                 (Kseq  (Ssequence (Ssequence (gc_set argsIdent allocIdent limitIdent threadInfIdent tinfIdent) asgn) body)
                                        (Kcall None fu empty_env lenv k))
                                 empty_env lenv_new m4)
                          (State F
                                 Sskip
                                 (Kseq (Ssequence (Ssequence (gc_set argsIdent allocIdent limitIdent threadInfIdent tinfIdent) asgn) body)
                                       (Kcall None fu empty_env lenv k))
                                 empty_env lenv_new' m5) /\
               same_tinf_ptr lenv_new lenv_new' /\
               exists alloc_b alloc_ofs limit_ofs vs7',

                 deref_loc (Tarray uval maxArgs noattr) m5 tinf_b
                           (Ptrofs.add tinf_ofs (Ptrofs.repr (int_size * 3)))
                           (Vptr args_b args_ofs) /\
                 Mem.load int_chunk m5 tinf_b
                              (Ptrofs.unsigned tinf_ofs) = Some (Val.load_result int_chunk (Vptr alloc_b alloc_ofs)) /\
                   Mem.load int_chunk m5 tinf_b
                            (Ptrofs.unsigned (Ptrofs.add tinf_ofs (Ptrofs.repr int_size))) = Some (Val.load_result int_chunk (Vptr alloc_b limit_ofs)) /\
                   mem_after_asgn args_b args_ofs m5 (skipn nParam locs) (skipn nParam vs7') /\
                (* lenv_new' then gets the tinf ptr, and then the param_asgn *) (* TODO: say something about lenv_new' and firstn nParam *)
                   (forall lenv_new'', lenv_param_asgn (M.set argsIdent (Vptr args_b args_ofs) (M.set limitIdent (Vptr alloc_b limit_ofs) (M.set allocIdent (Vptr alloc_b alloc_ofs) lenv_new'))) lenv_new'' (skipn nParam vsm4) (skipn nParam vs7') ->
                rel_mem_LambdaANF_Codegen_id fenv finfo_env p rep_env e4 rho'' m5 lenv_new'' /\
                correct_tinfo p max_alloc' lenv_new'' m5)).
    { (*
      unfold gc_test' in H9. unfold reserve' in H9. simpl in H9.
      unfold gc_test'.
      unfold reserve'.
      remember  (LambdaANF_to_Clight.not
               (Ebinop Ole
                  (Ederef
                     (Evar finfo0
                        (Tarray uval (Z.of_N (N.of_nat (length locs) + 2)) noattr)) uval)
                  (LambdaANF_to_Clight.sub
                     (Efield
                        (Ederef
                           (Etempvar tinfIdent
                              (Tpointer (Tstruct threadInfIdent noattr) noattr))
                           (Tstruct threadInfIdent noattr)) limitIdent valPtr)
                     (Efield
                        (Ederef
                           (Etempvar tinfIdent
                              (Tpointer (Tstruct threadInfIdent noattr) noattr))
                           (Tstruct threadInfIdent noattr)) allocIdent valPtr)) type_bool)) as gc_test.

      unfold LambdaANF_to_Clight.not in *.
       *)
      rewrite Hgccalleq.
      eexists. eexists.
      repeat weak_split.
      - remember  (not (Ebinop Ole (Ederef (Evar finfo0 (Tarray LambdaANF_to_Clight.uval (Z.of_N (N.of_nat (length locs) + 2)) noattr)) LambdaANF_to_Clight.uval)
                               (sub (Efield (Ederef (Etempvar tinfIdent (Tpointer (Tstruct threadInfIdent noattr) noattr)) (Tstruct threadInfIdent noattr)) limitIdent valPtr)
                                    (Efield (Ederef (Etempvar tinfIdent (Tpointer (Tstruct threadInfIdent noattr) noattr)) (Tstruct threadInfIdent noattr)) allocIdent valPtr)) type_bool)) as gc_test.
        unfold LambdaANF_to_Clight.not in *.

        assert (Hgc_test : exists v,  eval_expr (globalenv p) empty_env lenv_new m4 gc_test v /\ exists b, bool_val v (typeof gc_test) m4 = Some b).
        {
          rewrite Heqgc_test.
          assert (exists v, match
                       Val.of_bool (negb (Ptrofs.ltu (Ptrofs.divs (Ptrofs.sub limit_ofs alloc_ofs) (Ptrofs.repr int_size)) (Ptrofs.repr fi_0_m4)))
                     with
                     | Vint n => Some (Val.of_bool (Int.eq n Int.zero))
                     | _ => None
                     end = Some v).  {
            destruct (negb (Ptrofs.ltu (Ptrofs.divs (Ptrofs.sub limit_ofs alloc_ofs) (Ptrofs.repr int_size)) (Ptrofs.repr fi_0_m4))); eexists; reflexivity.
          }
          destruct H1 as [vb Hvb].
          rewrite Hfinfo_env_f' in H7. inv H7.
          assert (Hnd := disjointIdent).
          eexists. split.
          - econstructor. econstructor. econstructor. constructor. econstructor. constructor 2. apply M.gempty. eauto.
            constructor. reflexivity. econstructor 1. constructor. eauto.

            econstructor. econstructor. econstructor. econstructor. constructor. constructor. apply M.gss. constructor 3. reflexivity.
            reflexivity. eauto. rewrite  Htinfident_members. apply limitIdent_delta.
            econstructor 1. reflexivity.
            eapply Mem.load_store_same. eauto.

            econstructor. econstructor. econstructor. econstructor. constructor. apply M.gss. constructor 3. reflexivity. reflexivity. eauto.
            rewrite Htinfident_members. apply allocIdent_delta. econstructor 1. reflexivity.
            simpl. rewrite Ptrofs.add_zero. erewrite Mem.load_store_other.
            eapply Mem.load_store_same. eauto. eauto.
            right.
            assert (Het := Ptrofs.unsigned_add_either tinf_ofs (Ptrofs.repr int_size)). destruct Het. rewrite H1. left. simpl. rewrite Ptrofs.unsigned_repr. reflexivity.
            rewrite ptrofs_mu. chunk_red; archi_red; solve_uint_range; omega.

            right. rewrite H1.  rewrite Ptrofs.unsigned_repr. fold int_size.
            assert (int_size - Ptrofs.modulus + int_size < 0)%Z. 2: omega.
            unfold Ptrofs.modulus; unfold Ptrofs.wordsize;  unfold Wordsize_Ptrofs.wordsize;
              chunk_red; archi_red; simpl; omega.
            rewrite ptrofs_mu; chunk_red; archi_red; solve_uint_range; omega.


            simpl. unfold sem_sub. simpl. rewrite load_ptr_or_int. rewrite load_ptr_or_int. rewrite Coqlib.peq_true. reflexivity. reflexivity. reflexivity.
            simpl.
            assert (
                sem_cmp Cle (make_vint fi_0_m4) uval
                        (Vptrofs (Ptrofs.divs (Ptrofs.sub limit_ofs alloc_ofs) (Ptrofs.repr (sizeof (prog_comp_env p) uval))))
                        (Tpointer LambdaANF_to_Clight.val {| attr_volatile := false; attr_alignas := None |}) m4 =
                Some (Val.of_bool (negb (Ptrofs.ltu (Ptrofs.divs (Ptrofs.sub limit_ofs alloc_ofs) (Ptrofs.repr int_size)) (Ptrofs.repr fi_0_m4))))).
            {
              unfold sem_cmp. simpl. chunk_red; archi_red; simpl; unfold cmp_ptr; archi_red; unfold Val.cmplu_bool; unfold Vptrofs; archi_red; simpl. unfold Int64.ltu. unfold Ptrofs.to_int64. rewrite Int64.unsigned_repr.  rewrite Int64.unsigned_repr.
              unfold Ptrofs.ltu. unfold Ptrofs.of_int64.  rewrite ptrofs_of_int64. reflexivity. unsigned_ptrofs_range.
              unsigned_ptrofs_range.

              unfold Int.ltu. unfold Ptrofs.to_int. rewrite Int.unsigned_repr. rewrite Int.unsigned_repr.
              unfold Ptrofs.ltu. unfold Ptrofs.of_intu. unfold Ptrofs.of_int. rewrite ptrofs_of_int. reflexivity. auto.
              unsigned_ptrofs_range.
              unsigned_ptrofs_range.
            } apply H1.

            simpl. unfold sem_notbool. unfold bool_val. simpl.
            destruct (Val.of_bool (negb (Ptrofs.ltu (Ptrofs.divs (Ptrofs.sub limit_ofs alloc_ofs) (Ptrofs.repr int_size)) (Ptrofs.repr fi_0_m4))));
              try (solve [inv Hvb]). simpl. rewrite Bool.negb_involutive. apply Hvb.

          - destruct (negb (Ptrofs.ltu (Ptrofs.divs (Ptrofs.sub limit_ofs alloc_ofs) (Ptrofs.repr int_size)) (Ptrofs.repr fi_0_m4))); eexists; inv Hvb; reflexivity.
        }

        destruct Hgc_test as [gc_test_v [Hgc_test_v [gc_test_b Hgc_test_b]]].
        (* give the gc_test inequality with Z ops *)
        (* Ederef evaluated to the old limit_ofs and alloc_ofs *)
        assert (Hgc_case : (((Ptrofs.unsigned limit_ofs - Ptrofs.unsigned alloc_ofs) / int_size) <?  max_alloc' = gc_test_b)%Z).
        {

          subst.
          simpl in Hgc_test_b.
          unfold bool_val in Hgc_test_b. simpl in Hgc_test_b.

          (* * get the value of gc_test_v *)
          destruct gc_test_v; inv Hgc_test_b.

          inv Hgc_test_v.  2: inv H1.
          inv H6. 2: inv H1.
          inv H14.
          inv H1. inv H14. inv H1. rewrite M.gempty in H17; inv H17.
          inv H15. 2: inv H1.

          inv H22.  inv H21.


          assert (H_dj := disjointIdent).
          inv H1. 2: inv H26.
          inv H24. rewrite <- H15 in *. clear H15.

          inv H6. 2: inv H26. inv H24.
          rewrite <- H6 in *; clear H6.
          rewrite Hget_tinfident in H29; inv H29.
          rewrite Hget_tinfident in H27; inv H27.
          rewrite Htinfident_members in *. simpl in H28.
          rewrite allocIdent_delta in H28. inv H28.
          rewrite limitIdent_delta in H30; inv H30.

          inv H21. inv H1. inv H6. inv H1. inv H15. clear H15.
          inv H22. inv H1. inv H6. inv H1. inv H15. clear H15.
          inv H25. 2: inv H1. rewrite lenv_newEq in *.
          rewrite M.gss in H17; inv H17.

          inv H24. 2: inv H1. rewrite M.gss in H17; inv H17.
          inv H5; inv H1.
          inv H14; inv H1.


          unfold Mem.loadv in H5.
          erewrite Mem.load_store_same in H5; eauto.
          simpl in H5. inv H5.

          unfold Mem.loadv in H6.
          erewrite Mem.load_store_other in H6; eauto.
          rewrite Ptrofs.add_zero in H6.
          erewrite Mem.load_store_same in H6; eauto. inv H6.
          2: { right. rewrite Ptrofs.add_zero. simpl.
               assert (Het := Ptrofs.unsigned_add_either ofs2 (Ptrofs.repr int_size)). destruct Het.
               rewrite H1. left. rewrite Ptrofs.unsigned_repr. unfold Mptr; chunk_red; archi_red; omega. rewrite ptrofs_mu; chunk_red; archi_red; solve_uint_range; omega.
               right. rewrite H1. rewrite Ptrofs.unsigned_repr.
               fold int_size.
               assert (int_size - Ptrofs.modulus + int_size < 0)%Z. 2: omega.
               unfold Ptrofs.modulus; unfold Ptrofs.wordsize;  unfold Wordsize_Ptrofs.wordsize;
                 chunk_red; archi_red; simpl; omega.
               rewrite ptrofs_mu; chunk_red; archi_red; solve_uint_range; omega.
               }


             (* get the value of max_alloc in tinfo *)
             rewrite Hfinfo_env_f' in H7; inv H7.
               rewrite Hfind_symbol in H20 ; inv H20.

               inv H4. inv H1. 2: inv H5.
               inv H3; inv H1.
               unfold int_chunk in *.
               assert
                 (Some v0 =  Some (make_vint fi_0_m4) ).
               chunk_red; archi_red; simpl in *; rewrite Hload_fi0 in H4; auto.
               clear H4. inv H1.

               clear H5.


               assert (max_alloc' = fi_0_m4).
               unfold correct_alloc in *; subst; auto. subst.

               simpl in H16.
               simpl in H23.  unfold sem_sub in H23; simpl in H23.
               rewrite load_ptr_or_int in H23; [ | auto].
               rewrite load_ptr_or_int in H23; [ | auto].
               rewrite Coqlib.peq_true in H23.
               assert ((Coqlib.proj_sumbool (Coqlib.zlt 0 (sizeof (prog_comp_env p) uval)) &&
                                            Coqlib.proj_sumbool (Coqlib.zle (sizeof (prog_comp_env p) uval) Ptrofs.max_signed))%bool = true). { rewrite ptrofs_ms. unfold sizeof in *; chunk_red; archi_red; reflexivity. }
                                                                                                                                              rewrite H1 in H23. inv H23. clear H1.
               assert (
                   sem_cmp Cle (make_vint fi_0_m4) LambdaANF_to_Clight.uval (Vptrofs (Ptrofs.divs (Ptrofs.sub limit_ofs alloc_ofs) (Ptrofs.repr (sizeof (prog_comp_env p) uval)))) valPtr m4 =
                   Some (Val.of_bool (negb (Ptrofs.ltu (Ptrofs.divs (Ptrofs.sub limit_ofs alloc_ofs) (Ptrofs.repr int_size)) (Ptrofs.repr fi_0_m4))))).
               {
                 unfold sem_cmp. simpl. chunk_red; archi_red; simpl; unfold cmp_ptr; archi_red; unfold Val.cmplu_bool; unfold Vptrofs; archi_red; simpl. unfold Int64.ltu. unfold Ptrofs.to_int64. rewrite Int64.unsigned_repr.  rewrite Int64.unsigned_repr.
                 unfold Ptrofs.ltu. unfold Ptrofs.of_int64.  rewrite ptrofs_of_int64. reflexivity. unsigned_ptrofs_range.
                 unsigned_ptrofs_range.

                 unfold Int.ltu. unfold Ptrofs.to_int. rewrite Int.unsigned_repr. rewrite Int.unsigned_repr.
                 unfold Ptrofs.ltu. unfold Ptrofs.of_intu. unfold Ptrofs.of_int. rewrite ptrofs_of_int. reflexivity. auto.
                 unsigned_ptrofs_range.
                 unsigned_ptrofs_range.
               }
               Set Printing All. simpl. rewrite H16 in H1.
               Unset Printing All. simpl. inv H1.

               simpl in H8. rewrite sem_notbool_val in H8.
               rewrite Bool.negb_involutive in H8. simpl in H8.
               clear H16.
               unfold Ptrofs.ltu in *. unfold Ptrofs.sub in *.
               unfold Ptrofs.divs in *.

               rewrite Ptrofs.signed_repr with (z := int_size%Z) in H8.
               rewrite Ptrofs.signed_repr in H8.
               2:{ split.
                   rewrite <- Z.le_add_le_sub_l. etransitivity. 2: eauto.
                   unfold Ptrofs.min_signed.
                   inv Hc_alloc.    unfold Ptrofs.half_modulus. unfold Ptrofs.modulus. simpl. unfold Ptrofs.wordsize. unfold Wordsize_Ptrofs.wordsize. chunk_red; archi_red; simpl; omega.
                   etransitivity; eauto. unfold gc_size; unfold Ptrofs.max_signed. unfold Ptrofs.half_modulus. unfold Ptrofs.modulus.  unfold Ptrofs.wordsize. unfold Wordsize_Ptrofs.wordsize. chunk_red; archi_red; simpl; omega. }
                 2:unfold Ptrofs.min_signed; unfold Ptrofs.max_signed; unfold Ptrofs.half_modulus;  unfold Ptrofs.modulus;  unfold Ptrofs.wordsize; unfold Wordsize_Ptrofs.wordsize; chunk_red; archi_red; simpl; omega.
                   rewrite Ptrofs.unsigned_repr in H8.
                   rewrite Ptrofs.unsigned_repr in H8.
                   rewrite  Zquot.Zquot_Zdiv_pos in H8.
                   destruct  ((Ptrofs.unsigned limit_ofs - Ptrofs.unsigned alloc_ofs) / int_size <?  fi_0_m4)%Z eqn: Hcase.
                   (* true *)
                   apply Z.ltb_lt in Hcase.
                   rewrite Coqlib.zlt_true in H8 by auto. simpl in H8. inv H8.
                   reflexivity.
                   (* false *)
                   apply Z.ltb_ge in Hcase.
                   apply Z.le_ge in Hcase.
                   rewrite Coqlib.zlt_false in H8 by auto.
                   inv H8. reflexivity.
                   (* bounds *)
                   apply Zle_minus_le_0. unfold int_size in *. etransitivity; eauto.
                   inv Hc_alloc.
                   simpl. chunk_red; omega. chunk_red; omega.
                   (* Assumption that max_allocs is smaller than gc_size -- add this to correct_fundef_info *)
                   assert (  (0 <= fi_0_m4)%Z) by (inv Hcorrect_alloc_m4; apply Zle_0_nat).
                   split. auto.
                   unfold gc_size in *. rewrite ptrofs_mu. simpl in Hgc_size_fi0m4. etransitivity. etransitivity. 2: apply Hgc_size_fi0m4. chunk_red; omega. chunk_red; archi_red; solve_uint_range; simpl; omega.

                   split. apply Zquot.Z_quot_pos.
                   apply Zle_minus_le_0. unfold int_size in *. etransitivity; eauto.
                   inv Hc_alloc.
                   simpl. chunk_red; omega. chunk_red; omega.
                   apply Z.quot_le_upper_bound. chunk_red; omega.
                   assert  (Ptrofs.max_unsigned <= int_size * Ptrofs.max_unsigned)%Z. assert (0 <= Ptrofs.max_unsigned)%Z. etransitivity. 2: apply ptrofs_mu_weak. unfold Int.max_unsigned; simpl; omega. chunk_red; omega.
                   etransitivity; eauto.

                   }

        destruct gc_test_b.
      (* two cases *)
      (** 1) not enough space in the nursery for body, GC call *)

      *   (* done - modify gc_inv to account for new lenv and additional restriction on args*)
        rewrite Hfinfo_env_f' in H7. inv H7.
        destruct Hpinv_gc as [b_gcPtr [name_gc [sg_gc [Hfind_gc_ptr [Hfind_gc_funct Hinv_gc]]]]].

        assert (@rel_mem_asgn fenv finfo_env p rep_env args_b args_ofs m4 Lm4 (skipn nParam vs) aind avs7). {
          assert (Hdj := disjointIdent).
          assert (Hmem_of_asgn_m4: mem_of_asgn_v args_b args_ofs p lenv m4 ays aind avs7).
          eapply mem_of_asgn_v_store.
          eapply mem_of_asgn_v_store.
          eauto. eauto. solve_nodup.
          eauto. solve_nodup.
          eapply rel_mem_of_asgn; eauto.
          intros.
          assert (Hskipn_get_list : forall {A} n l1 (l2 : list A) rho,
                                        get_list l1 rho = Some l2 -> get_list (skipn n l1) rho = Some (skipn n l2)). (* TODO : Move out *)
          {
            intros A. induction n; intros. auto.
            destruct l1 , l2.
            - reflexivity.
            - inv H1.
            - simpl in H1.
              repeat match_case in H1.
            - simpl in H1.
              repeat match_case in H1.
              simpl. apply IHn; auto.
              inv H1. assumption.
          }
          rewrite aysEq.
          apply Hskipn_get_list. eauto. intros.
          assert (occurs_free (Eapp f tm4' ys) x). constructor. eauto.
          specialize (Hrel_rho_m4 x). destruct Hrel_rho_m4 as [Hrel_mg1 Hrel_mg2].
          specialize (Hrel_mg1 H3).
          destruct Hrel_mg1 as [v6 [Hgv6 Hv6_repr]].
          exists v6. split; auto.
        }

        assert ( deref_loc (Tarray uval maxArgs noattr) m4 tinf_b (Ptrofs.add tinf_ofs (Ptrofs.repr (3 * int_size)))
                           (Vptr args_b args_ofs)). {
          destruct Hc_tinfo_m4.
          destructAll.
          rewrite H14 in  Hget_args; inv Hget_args.
          rewrite H20 in  Hget_tinf; inv Hget_tinf.
          eauto.
        }

        specialize (Hinv_gc _ _ _ _ _ _ _  _ _   _ _ _ _ _ _ _ H1 Hget_tinf  Hload_fi0  Hgc_size_fi0m4 H3).

        destruct Hinv_gc as [gc_vret [m5 [alloc_b' [alloc_ofs' [limit_ofs' [L' [vs7' [Hinv_gc [Hderef_alloc' [Hderef_limit' [Hderef_args' [Hrel_mem_asgn' [Hrel_mem_unchanged' [Hprotected_L' Hcorrect_tinfo']]]]]]]]]]]]]]. (* I'M HERE *)
        eexists. eexists. split.
        eapply t_trans.
        constructor. econstructor. eauto. eauto.
        simpl.



        (* true branch -> call to gc *)
        eapply t_trans.
        constructor. econstructor. reflexivity. eauto.
        econstructor.
        apply eval_Evar_global. apply M.gempty. eauto.
        simpl. constructor. simpl. constructor.
        econstructor. econstructor. constructor 2.
        apply M.gempty.  eauto.
        constructor. reflexivity. simpl. reflexivity.
        econstructor. constructor.
        assert (Hdj:=disjointIdent).
        rewrite M.gss. reflexivity.
        reflexivity. constructor.
        eauto. simpl. reflexivity.

        eapply t_trans.
        constructor.
        eapply step_external_function.
        eauto.

        constructor. constructor.

        split. simpl. reflexivity.
        exists alloc_b', alloc_ofs', limit_ofs', vs7'.
        split. auto. split.
        inv Hderef_alloc' ; try (inv H6). inv H5. auto.
        split. inv Hderef_limit'; try (inv H6). inv H5; auto.

        split.
        eapply rel_mem_after_asgn; eauto.
        intros.
        assert (map_get_r_l Values.val [argsIdent; limitIdent; allocIdent; tinfIdent]
                            (M.set argsIdent (Vptr args_b args_ofs)
                                   (M.set limitIdent (Vptr alloc_b' limit_ofs')
                                          (M.set allocIdent (Vptr alloc_b' alloc_ofs')
                                                 (Maps.PTree.set tinfIdent (Vptr tinf_b tinf_ofs) (M.empty Values.val))))) lenv_new''). {
          assert (H_nodup := disjointIdent).
          eapply lenv_param_asgn_map with (l := [argsIdent; limitIdent; allocIdent; tinfIdent]) in H5.

          intro. intro. rewrite <- H5.
          2: auto.
          inv H6. rewrite M.gss. rewrite M.gss. reflexivity.
          inv H7. clear H6. rewrite M.gso. rewrite M.gss. rewrite M.gso. rewrite M.gss.
          reflexivity.
          solve_nodup. solve_nodup.
          inv H6. clear H7. rewrite M.gso by solve_nodup. rewrite M.gso by solve_nodup. rewrite M.gss.
          rewrite M.gso by solve_nodup. rewrite M.gso by solve_nodup. rewrite M.gss. reflexivity.
          inv H7. clear H6.
          rewrite M.gso by solve_nodup. rewrite M.gso by solve_nodup. rewrite M.gso by solve_nodup. rewrite M.gss.
          rewrite M.gso by solve_nodup. rewrite M.gso by solve_nodup. rewrite M.gso by solve_nodup. simpl. rewrite M.gss. reflexivity.
          inv H6.
          split. intro. intro. destruct H6. apply Hnoprot_vs0 in H6. apply H6. inv H7. left. constructor 2. auto.
          inv H8. left. constructor 2. auto. inv H7. left. constructor. auto. inv H8. auto. inv H7.
        }
        split.
      * (* rel_mem m5 *)
        exists L'.

        assert (Hug_m45: unchanged_globals p m4 m5). {
          intro.
          intros. symmetry.
          eapply Mem.load_unchanged_on_1.
          eauto. destruct Hc_tinfo_m4. destructAll. apply H27 in H7. destructAll.
          eapply Mem.valid_access_valid_block. eauto. (* any block in globalenv is valid, and that GC preserve those blocks *)
          intros. simpl. split.
          inv Hrel_pm4. destructAll.
          rewrite  Hget_args in H18; inv H18.
          rewrite Hget_alloc in H12; inv H12. eapply H22.
          apply H7.
          inv  Hprotected_L'. destructAll.
          rewrite M.gss in H18. inv H18.
          assert (Hnd := disjointIdent).
          rewrite M.gso in H20 by solve_nodup.
          rewrite M.gso in H20 by solve_nodup.
          rewrite M.gso in H20 by solve_nodup.
          rewrite M.gss in H20. inv H20.
          split.
          eapply H22. eauto.
          inv Hc_tinfo'. destructAll.
          apply H35 in H7. destructAll. rewrite H30 in Hget_tinf. inv Hget_tinf. eauto.
        }


        split.
        eapply protected_not_in_L_proper; eauto. split.
        { (* rel_mem of *)
          intros.
          (* e4 is closed under  (name_in_fundefs fl + vsm4) so x is in rho'' *)
          assert (Hx_in: (In _ (Ensembles.Union _  (FromList vsm4) (name_in_fundefs fl)) x)). {
            eapply closed_val_fun; eauto.
          }
          assert (Hx_vsm4: decidable (List.In x vsm4)). apply In_decidable. apply shrink_cps_correct.var_dec_eq.
          inv Hx_vsm4.
          + (* x in vsm4 *)
            assert (Hx_rho'' := get_set_lists_In_xs _ _ _ _ _ H8 H2). destruct Hx_rho''. exists x0. split; auto.
            assert (Hx_in_rho := in_rho_entry _ _ _ _ _ _ H2  Hnd_vs0  H12). destruct Hx_in_rho.
            2: exfalso; destructAll; auto.
            destruct H15. destruct H15.
            assert (H_x0_vs := nthN_In _ _ _ H16).
            specialize ( H5 x). destruct H5. specialize (H5 _ H15).

            assert (Hx_rho_x_val := get_list_nth_get' _ _ _ _ _ _ H0 H16). destruct Hx_rho_x_val as [y4 [Hy4_ys Hy4_rho]].

            specialize (Hrel_rho_m4 y4). destruct (Hrel_rho_m4).
            assert (occurs_free (Eapp f tm4 ys) y4). constructor. apply nthN_In in Hy4_ys; auto. apply H18 in H20.
            destruct H20. destruct H20. rewrite Hy4_rho in H20. inv H20.
            assert (Genv.find_symbol (Genv.globalenv p) x = None). {
              inv Hf_id. eapply H22. apply H.
              eapply  Bound_FVfun. left. eauto. eauto.
            }
            assert (exists v7, nthN vs7' x1 = Some v7).
            eapply nthN_length. eapply OrdersEx.Nat_as_OT.eq_le_incl. eapply rel_mem_asgn_length; eauto.
            eauto. destruct H22 as [v7 Hv7_vs7].
            econstructor. eauto. erewrite Hv7_vs7 in H5. apply H5.
            assert (Hx2v7 := rel_mem_asgn_nthN   Hrel_mem_asgn' H16 Hv7_vs7). auto.
          + (* x in fl *)
            inv Hx_in. exfalso; auto.
            eapply set_lists_not_In in H2. 2: eauto.
            rewrite def_funs_eq in H2; auto. eexists. split; eauto.
            assert (subval_or_eq  (Vfun (M.empty term.val) fl x) (Vfun (M.empty term.val) fl f')). constructor. eapply dsubval_fun.  auto. destruct (Hrel_rho_m4 f). specialize (H17 _ _ _ _  H H15). destruct H17. inv H17.

            econstructor. apply H21. inv H26.
            econstructor; eauto.
            (* impossible, functions not bound *)
            inv H21. rewrite H26 in H19. inv H19.
        }
        { (* rel_mem fun *)
          intros.



          assert (Hin := in_rho_entry _ _ _ _ _ _ H2 Hnd_vs0 H7).

          destruct Hin.
          + (* x is from vs0 *)
            destruct H12.
            destruct H12.
            apply nthN_In in H15.
            apply (get_list_In_val _ _ _  _ H0) in H15.
            destruct H15. destruct H15.


            specialize (Hrel_rho_m4 x1).
            destruct Hrel_rho_m4.
            specialize (H18 _ _ _ _ H16 H8).
            destruct H18 as [Hrel_m421 Hrel_m422].
            split.
          - inv Hrel_m421.
            inv H26. econstructor; eauto.
            econstructor; eauto.
            (* imposible since function not bound *)
            inv H20. rewrite H27 in H18. inv H18.
          - destruct  Hrel_m422.  split. auto. eapply correct_fundefs_unchanged_global; eauto.

            + (* x is from fl *)
              destructAll.
              specialize (Hrel_rho_m4 f). destruct Hrel_rho_m4 as [Hrel_m41 Hrel_m42].
              assert (    exists l,  (Vfun rho'0 fds f0) = Vfun  (M.empty term.val) fl l /\ name_in_fundefs fl l).
              eapply subval_fun.                     eapply find_def_name_in_fundefs; eauto. auto. destruct H16. destruct H16. inv H16.
              assert (subval_or_eq (Vfun (M.empty term.val) fl x3) (Vfun (M.empty term.val) fl f')).
              constructor. constructor. auto.
              specialize (Hrel_m42 _ _ _ _ H H16). destruct Hrel_m42 as [Hrel_m421 [Hrel_closed_m42 Hrel_m422]].

              split.
          - inv Hrel_m421.
            inv H25. econstructor; eauto.
            econstructor; eauto.
            (* imposible since function not bound *)
            inv H20. rewrite H26 in H18. inv H18.
          - split; auto. eapply correct_fundefs_unchanged_global; eauto.
        }

      *             (* correct_tinfo m5 *)
        assert ( max_alloc' = fi_0_m4).
        inv Hc_alloc'; inv Hcorrect_alloc_m4.
        reflexivity.
        eapply correct_tinfo_proper. rewrite H7. eauto.
        eauto.





      (** 2) enough space in the nursery, so m5 = bindings + m4 *)
      -
        assert (Hlenv_asgn := e_lenv_param_asgn_i  vsm4 lenv_new vs7 Hl_temp Hnd_vs0).
        clear Hl_temp.
        destruct Hlenv_asgn as [lenv_new' Hlenv_new'].
        exists m4, lenv_new.
        split.
        evar (e:statement). replace Sskip with e at 2.
        eapply t_step.  eapply step_ifthenelse. unfold  LambdaANF_to_Clight.uval in *; unfold  LambdaANF_to_Clight.val in *; unfold val in *; unfold uval in *. rewrite <-   Heqgc_test.
        eauto.
        unfold  LambdaANF_to_Clight.uval in *; unfold  LambdaANF_to_Clight.val in *; unfold val in *; unfold uval in *. rewrite <-   Heqgc_test.
        eauto. reflexivity.
        split.
        reflexivity. exists alloc_b, alloc_ofs, limit_ofs, vs7.
        split. inv Hc_tinfo_m4. destructAll. rewrite H12 in Hget_args; inv Hget_args. rewrite H18 in Hget_tinf; inv Hget_tinf. unfold int_chunk. simpl.  auto.
        split.
        erewrite Mem.load_store_other.
        eapply Mem.load_store_same. eauto.  eauto.
        right.
        assert (Het := Ptrofs.unsigned_add_either tinf_ofs (Ptrofs.repr int_size)). destruct Het.
        rewrite H1. left.  rewrite Ptrofs.unsigned_repr. unfold Mptr; chunk_red; archi_red; omega. rewrite ptrofs_mu; chunk_red; archi_red; solve_uint_range; omega.
        right. rewrite H1. rewrite Ptrofs.unsigned_repr.
            fold int_size.
            assert (int_size - Ptrofs.modulus + int_size < 0)%Z. 2: omega.
            unfold Ptrofs.modulus; unfold Ptrofs.wordsize;  unfold Wordsize_Ptrofs.wordsize;
        chunk_red; archi_red; simpl; omega.
            rewrite ptrofs_mu; chunk_red; archi_red; solve_uint_range; omega.
        split.
        eapply Mem.load_store_same. eauto. split; auto.
        intros.
        split.
        + (* destruct Hrel_mem4 as [Lm4' [Hp_Lm4' Hrel_mem4]]. *)
           exists Lm4.
            split.
            * apply lenv_param_asgn_rel in Hlenv_new'; auto.
              eapply protected_not_in_L_asgn. 2: eauto.
              inv Hrel_pm4.
              destructAll.
              rewrite H4 in Hget_alloc; inv Hget_alloc.
              rewrite H6 in Hget_limit; inv Hget_limit.
              rewrite H15 in Hget_tinf; inv Hget_tinf.
              rewrite H7 in Hget_args; inv Hget_args.
              assert (Hdj := disjointIdent).
              do 7 eexists. repeat (split; eauto).
              rewrite M.gso. rewrite M.gso. rewrite M.gss. reflexivity.
              solve_nodup.  solve_nodup.
              rewrite M.gso. rewrite M.gss. reflexivity.
              solve_nodup.
              rewrite M.gss. reflexivity.
              rewrite M.gso. rewrite M.gso. rewrite M.gso. rewrite M.gss.
              reflexivity. solve_nodup. solve_nodup. solve_nodup.
              auto.
            * intro.

              {
                split.
                - (* need closed term at top level, s.t. x has to come from fl or xs *)
                  intro.
                  assert (Hx_in: (In _ (Ensembles.Union _  (FromList vsm4) (name_in_fundefs fl)) x)). {
                    eapply closed_val_fun; eauto.
                  }
                  assert (Hx_vsm4: decidable (List.In x vsm4)). apply In_decidable. apply shrink_cps_correct.var_dec_eq.
                  inv Hx_vsm4.
                  + (* x in vsm4 *)
                    assert (Hx_rho'' := get_set_lists_In_xs _ _ _ _ _ H5 H2). destruct Hx_rho''. exists x0. split; auto.
                    assert (Hx_in_rho := in_rho_entry _ _ _ _ _ _ H2  Hnd_vs0  H6). destruct Hx_in_rho.
                    2: exfalso; destructAll; auto.
                    destruct H7. destruct H7.
                    assert (H_x0_vs := nthN_In _ _ _ H12).
                    specialize (H1 x). destruct H1. specialize (H1 _ H7).
                    assert (Hx_rho_x_val := get_list_nth_get' _ _ _ _ _ _ H0 H12). destruct Hx_rho_x_val as [y4 [Hy4_ys Hy4_rho]].

                    specialize (Hrel_rho_m4 y4). destruct (Hrel_rho_m4).
                    assert (occurs_free (Eapp f tm4 ys) y4). constructor. apply nthN_In in Hy4_ys; auto. apply H16 in H18.
                    destruct H18. destruct H18. rewrite Hy4_rho in H18. inv H18.
                    assert (Genv.find_symbol (Genv.globalenv p) x = None). {
                      inv Hf_id. eapply H20. apply H.
                      eapply  Bound_FVfun. left. apply H5. eauto.
                    }
                    assert (exists v7, nthN vs7 x1 = Some v7).
                    eapply nthN_length. eapply OrdersEx.Nat_as_OT.eq_le_incl. eapply lenv_param_asgn_i_length. eauto.
                    eauto. destruct H20 as [v7 Hv7_vs7].
                    econstructor. eauto. erewrite Hv7_vs7 in H1. apply H1.
                    assert (Hy4v7 := mem_of_asgn_nthN  Hvs7 Hy4_ys Hv7_vs7).
                    inv Hy4v7.
                    * inv H19. rewrite H20 in H21. inv H21. eauto. rewrite H20 in H21. inv H21.
                    * inv H19. rewrite H23 in H20. inv H20. rewrite H21 in H24. inv H24. auto.
                  + (* x in fl *)
                    inv Hx_in. exfalso; auto.
                    eapply set_lists_not_In in H2. 2: eauto.
                    rewrite def_funs_eq in H2; auto. eexists. split; eauto.
                    assert (subval_or_eq  (Vfun (M.empty term.val) fl x) (Vfun (M.empty term.val) fl f')). constructor. eapply dsubval_fun.  auto. destruct (Hrel_rho_m4 f). specialize (H15 _ _ _ _  H H7). destruct H15. inv H15. econstructor; eauto.
                    (* impossible, functions not bound *)
                    inv H19. rewrite H24 in H17. inv H17.
                -  intros.
                  assert (Hin := in_rho_entry _ _ _ _ _ _ H2 Hnd_vs0 H4).
                  destruct Hin.
                  + (* x is from vs0 *)
                    destruct H6.
                    destruct H6.
                    apply nthN_In in H7.
                    apply (get_list_In_val _ _ _  _ H0) in H7.
                    destruct H7. destruct H7.
                    specialize (Hrel_rho_m4 x1).
                    destruct Hrel_rho_m4.
                    specialize (H16 _ _ _ _ H12 H5).
                    destruct H16.
                    split; auto.
                    inv H16. econstructor; eauto.

                    (* impossible *)
                    inv H20. destructAll. rewrite H26 in H18; inv H18.
                  + (* x is from fl *)
                    destructAll.
                    specialize (Hrel_rho_m4 f). destruct Hrel_rho_m4 as [Hrel_m41 Hrel_m42].
                    assert (    exists l,  (Vfun rho'0 fds f0) = Vfun  (M.empty term.val) fl l /\ name_in_fundefs fl l).
                    eapply subval_fun.                     eapply find_def_name_in_fundefs; eauto. auto. destruct H12. destruct H12. inv H12.
                    assert (subval_or_eq (Vfun (M.empty term.val) fl x3) (Vfun (M.empty term.val) fl f')).
                    constructor. constructor. auto.
                    specialize (Hrel_m42 _ _ _ _ H H12). destruct Hrel_m42 as [Hrel_m421 Hrel_m422]. split; auto.
                    inv Hrel_m421; subst. econstructor; eauto.
                    (* imposible since function not bound *)
                    inv H18. rewrite H24 in H16. inv H16.
              }
        + eapply correct_tinfo_param_asgn; eauto.
(*          2: eapply lenv_param_asgn_rel in Hlenv_new'; eauto. *)
          eapply correct_tinfo_proper with (lenv := lenv).
          2 : {
            intro; intros.
            destruct (var_dec v0 argsIdent).
            subst. rewrite M.gss; auto.
            inv H4. exfalso; auto.
            rewrite M.gso by auto.
            destruct (var_dec v0 limitIdent).
            subst. rewrite M.gss; auto.
            rewrite M.gso by auto.
            inv H5. exfalso; auto.
            destruct (var_dec v0 allocIdent).
            subst; rewrite M.gss; auto.
            inv H4. exfalso; auto.
            rewrite M.gso by auto.
            inv H5. rewrite M.gss; auto.
            inv H4. }
            destruct Hc_tinfo_m4; destructAll.
            rewrite H4 in Hget_alloc; inv Hget_alloc.
            rewrite H15 in Hget_args; inv Hget_args.
            rewrite H7 in Hget_limit; inv Hget_limit.
            rewrite H19 in Hget_tinf; inv Hget_tinf.
            exists alloc_b, alloc_ofs, limit_ofs, args_b, args_ofs, tinf_b, tinf_ofs.
            repeat (split; auto).
            apply Z.ltb_ge in Hgc_case.
            eapply OrdersEx.Z_as_OT.mul_le_mono_nonneg_l with (p := int_size%Z) in Hgc_case.

            assert ( int_size * ((Ptrofs.unsigned limit_ofs - Ptrofs.unsigned alloc_ofs) / int_size)<= ((Ptrofs.unsigned limit_ofs - Ptrofs.unsigned alloc_ofs)))%Z by (apply Z.mul_div_le; chunk_red; archi_red; omega).
            omega.
            chunk_red; archi_red; omega.
                       *)
            } (*END OF Hm5*)

              destruct Hm5 as [m5 [lenv_new'' [Hm5 [Hm5_lenv [alloc_b_m5 [alloc_ofs_m5 [limit_ofs_m5 [vs7_m5 [deref_args_m5 [load_alloc_m5 [load_limit_m5 [Hvs7_m5 Hm5_all_rel]]]]]]]]]]]].

    assert (Hl_temp': length avsm4 = length (skipn nParam vs7_m5)). {
      SearchAbout mem_after_asgn length.
      apply mem_after_asgn_length in Hvs7_m5.
      eapply HSkipnLength in Hlvs.
      rewrite avsm4Eq.
      rewrite <- Hlvs. auto.
    }

    assert (Help := e_lenv_param_asgn_i _ (M.set argsIdent (Vptr args_b args_ofs)
                                                 (M.set limitIdent (Vptr alloc_b_m5 limit_ofs_m5)
                                                        (M.set allocIdent (Vptr alloc_b_m5 alloc_ofs_m5) lenv_new'')))  _ Hl_temp' Havsm4_nodup).
    destruct Help as [lenv_new''' Hlenv_new'''_asgn_i].
    assert (Hlenv_new'''_asgn := lenv_param_asgn_rel _ _ _ _ Hlenv_new'''_asgn_i Havsm4_nodup).
    specialize (Hm5_all_rel lenv_new''' Hlenv_new'''_asgn).
    destruct Hm5_all_rel as [Hm5_relmem Hm5_tinfo].


    assert (Hc_env' : correct_envs cenv ienv rep_env rho'' e4). {
      inv Hc_env. destructAll.
      split.
      (* ienv_of_cenv *)
      auto. split.
      (* cenv of env  ccenv rho'' *)
      { intro; intros.
        assert (decidable (List.In x vsm4)). apply In_decidable. apply shrink_cps_correct.var_dec_eq.
        inv H14.
        (* 1) in vs  *)
        assert (List.In v0 vs) by (eapply set_lists_In; eauto).

        assert (Hgl := get_list_In_val _ _ _ _  H0 H14).
        destruct Hgl. destruct H16.
        apply H3 in H17. auto.

        erewrite <- set_lists_not_In in H13.
        2: eauto.
        2: eauto.

        assert (decidable (name_in_fundefs fl x)).
        {
          unfold decidable. assert (Hd := Decidable_name_in_fundefs fl). inv Hd. specialize (Dec x). inv Dec; auto.
        }
        inv H14.
        (*
          2) in fl *)
        rewrite def_funs_eq in H13. 2: eauto.
        inv H13.
        apply H3 in H. inv H.
        constructor. auto.

        (*
          3* ) in rho' (EMPTY!!!)
         *)
        rewrite def_funs_neq in H13. 2: eauto.
        rewrite M.gempty in H13. inv H13.
      }

      split.
      (* cenv_of_exp cenv e0 -- can get this from correct_cenv_of_val (CCV_fun) *)
      apply H3 in H. inv H.
      eapply Forall_fundefs_In in H15. apply H15.
      eapply find_def_correct. eauto.

      (* crep_of_env *)
      auto.

    }
    assert (Hrel_p'': protected_id_not_bound_id rho'' e4 ) by (eapply protected_id_closure; eauto).

    assert (Hrho''_id : unique_bindings_env rho'' e4). {
      destruct Hrho_id.
      split.
      apply H3 in H.

      destruct H as [Hbv Hubv].
      inv Hubv.
      eapply shrink_cps_correct.ub_in_fundefs; eauto.


      intros.   assert (decidable (List.In x vsm4)). apply In_decidable. apply shrink_cps_correct.var_dec_eq.
      destruct H5.
      (* in vs0 *)
      apply H3 in H.
      destruct H as [Hbv Hubv].
      inv Hubv.
      assert (List.In v0 vs) by (eapply set_lists_In; eauto).
      assert (Hgl := get_list_In_val _ _ _ _  H0 H). destruct Hgl. destruct H8.

      split. intro.

      assert (Hdj:=shrink_cps_correct.Disjoint_bindings_find_def _ _ _ _ _ H6 Hfind_def_f').
      inv Hdj. specialize (H15 x). apply H15. split; auto.

      apply H3 in H13. destruct H13; auto.


      (* in fl *)
      erewrite <- set_lists_not_In in H4. 2: eauto. 2:eauto.

      assert (decidable (name_in_fundefs fl x)). unfold decidable. assert (Hd := Decidable_name_in_fundefs fl). inv Hd. specialize (Dec x). inv Dec; auto.
      inv H6.
      apply H3 in H.
      destruct H as [Hbv Hubv].
      inv Hubv.
      erewrite def_funs_eq in H4. 2: eauto.
      inv H4.
      split.
      assert  (Hdj := shrink_cps_correct.Disjoint_bindings_fundefs _ _ _ _ _ H6 Hfind_def_f').
      inv Hdj. intro. specialize (H x). apply H. split; auto.

      constructor; auto.

      rewrite def_funs_neq in H4; eauto.
      rewrite M.gempty in H4. inv H4.
    }
        assert (Hf_id': functions_not_bound p rho'' e4 ). {
      destruct Hf_id as [Hf_id1 Hf_id2].
      split.

      -  intros. eapply Hf_id2 in H. eauto.
        econstructor. right. apply H1. eauto.
      - intros.
        assert (decidable (List.In y vsm4)). apply In_decidable. apply shrink_cps_correct.var_dec_eq.
        inv H4.
        (* in vsm4 *)
        assert (List.In v0 vs) by (eapply set_lists_In; eauto).
        assert (Hgl := get_list_In_val _ _ _ _  H0 H4). destruct Hgl. destruct H6.
        eapply Hf_id2 in H8; eauto.


        (* in fl *)
        erewrite <- set_lists_not_In in H1. 2: eauto. 2: eauto.
        assert (decidable (name_in_fundefs fl y)). unfold decidable. assert (Hd := Decidable_name_in_fundefs fl). inv Hd. specialize (Dec y). inv Dec; auto.
        inv H4.

        erewrite def_funs_eq in H1. 2: eauto. inv H1.
        eapply Hf_id2 in H; eauto. inv H3. econstructor; eauto.

        rewrite def_funs_neq in H1; eauto.
        rewrite M.gempty in H1. inv H1.

    }
    specialize (IHHev Hc_env' Hrel_p'' Hrho''_id Hf_id' _ _ _ (Kcall None fu empty_env lenv k) _ F H19 Hm5_relmem Hc_alloc' Hm5_tinfo).
    destruct IHHev as [m6 [lenv6 [Hstep_m6 Hargs_m6]]].


    exists m6, lenv.

    split.

    (* step through s*)
    eapply t_trans.
    constructor. constructor.

    eapply t_trans.
    constructor. constructor.

    eapply t_trans.
    constructor. constructor.

    eapply t_trans.
    econstructor. constructor.

    eapply t_trans.
    econstructor. constructor.

    econstructor. econstructor. econstructor.  constructor.
    constructor.
    (* tinfIdent is in lenv *) eauto.
    constructor 3. simpl. reflexivity. simpl. reflexivity.
    eauto.
    rewrite Htinfident_members. apply argsIdent_delta.
    simpl. eauto.

    eapply t_trans.
    constructor.
    constructor.

    eapply clos_rt_t.
    Set Printing All. simpl.
    rewrite Hlenv'.
    Unset Printing All. simpl.
    eauto.

    (* done marshalling elements *)
    eapply t_trans.
    constructor.
    constructor.

    eapply t_trans.
    constructor. econstructor. econstructor. econstructor.
    constructor. constructor. eauto.
    constructor 3. reflexivity. reflexivity. eauto.
    rewrite Htinfident_members. apply allocIdent_delta. constructor. eauto. simpl. reflexivity.
    econstructor. reflexivity.
    unfold Mem.storev. rewrite Ptrofs.add_zero. apply Hm3.


    eapply t_trans.
    constructor. constructor.



    (* step to m4 now *)
    eapply t_trans.
    constructor. econstructor. econstructor. econstructor.
    constructor. constructor. eauto.
    constructor 3. reflexivity. reflexivity. eauto.
    rewrite Htinfident_members. apply limitIdent_delta.

    constructor. eauto. reflexivity. econstructor. reflexivity.
    unfold Mem.storev. apply Hm4.


    eapply t_trans.
    constructor. econstructor.


    (* CALL TIME! *)

    eapply t_trans.
    constructor. econstructor.
    reflexivity.
    simpl. rewrite Nnat.Nat2N.id.
    eapply Heval_f'.
    econstructor. econstructor.
    eauto. constructor.
    (* OSTODO: need a hyp:
   eval_exprlist (globalenv p) empty_env lenv m4 s2
    (mkFunTyList
       (Init.Nat.min
          (N.to_nat (fst (N.of_nat (length locs), locs))) nParam))
    ?Goal12 for some ?Goal12 equivalent to values in bys *)
    simpl. rewrite Nnat.Nat2N.id.
    admit.
    (* -- find_funct f'*)
    eauto.
    (* -- type_of_fundef F*)
    simpl. unfold type_of_function. rewrite Nnat.Nat2N.id.
    rewrite Hlvs. unfold fn_params. simpl.
    rewrite type_of_mkFunTyList. reflexivity.



    (* - step through the Callstate *)
    (* OSTODO: HOSTEMP1 shows that you can skip the mk_gv_call when looking up a protected ident [whenever used to rewrite Heqlenv_new *)
    assert (HOSTEMP1: M.get tinfIdent lenv_new = Some (Vptr tinf_b tinf_ofs)) by admit.
    eapply t_trans.
    constructor.
    (* I'M HERE : TODO: update the le in step_internal_function to include the argument vector computed earlier [in the eval_exprlist] *)

    eapply  step_internal_function with (le := lenv_new).
(*    (Maps.PTree.set tinfIdent (Vptr tinf_b tinf_ofs)
       (create_undef_temps ((skipn nParam vars) ++ gc_vars argsIdent allocIdent limitIdent caseIdent)))). *)
    constructor.
    simpl. constructor.
    (* OSTODO: need to show that tinfo and all params are disjoint (from unique_bindigns and protected_not_bound) *)
    (*    simpl. constructor. intro Hfalse; inv Hfalse. constructor. *)
    admit.
    (* OSTODO: need to show that first n param are disjoint from last arity-n *)
    (*simpl. intro; intros. inv H1. rewrite <- H5 in *. clear H5. *)
    admit.


    (* --  alloc_variables (globalenv p) empty_env m4
    (fn_vars F) ?Goal12 ?Goal13 *)
    admit.

    (* -- bind_parameter_temps*)
    unfold lenv_new; rewrite Heqlenv_new'.
    admit.
    (*
    rewrite var_names_app in H4.
    rewrite Coqlib.in_app in H4. destruct H4.
    intro. rewrite <- H4 in *; clear H4.
    assert (List.In tinfIdent vsm4).
    eapply unzip_vars; eauto.
    inv Hp_id.
    assert ( is_protected_id argsIdent allocIdent limitIdent gcIdent mainIdent bodyIdent threadInfIdent
         tinfIdent heapInfIdent numArgsIdent isptrIdent caseIdent tinfIdent) by inList.
    specialize (H5 _ _ _ H H7).
    apply H5. right.
    constructor.
    eapply shrink_cps_correct.name_boundvar_arg.
    apply H4. eauto.
    simpl in H1. intro. rewrite <- H4 in *. clear H4.
    assert (H_dj := disjointIdent). inv H_dj. inv H7. inv H15.
    inv H16. inv H17. inv H18. inv H19. inv H20. inv H1. apply H12; inList. inv H4. apply H7; inList. inv H1. apply H6; inList.
    inv H4. apply H19; inList. auto.
    inv H5.
    constructor. reflexivity.
     *)


    eapply t_trans.
    constructor. constructor.

    (* go through gc_test' to m5 *)
    eapply t_trans.
    apply Hm5.


    eapply t_trans.
    constructor. constructor.
    eapply t_trans.
    constructor. constructor.
    eapply t_trans.
    constructor. constructor.

    (* step through gc_set *)
    unfold gc_set.


    (* step through reestablishing locals for tinfo's field *)
    eapply t_trans.
    constructor. constructor.

    eapply t_trans.
    constructor. constructor.
    (* * allocs *)
    eapply t_trans.
    constructor. constructor.

    econstructor. econstructor. econstructor.
    constructor. constructor. rewrite <- Hm5_lenv.
    eauto.
(*    unfold lenv_new; rewrite Heqlenv_new'. rewrite M.gss. reflexivity.     *)
    constructor 3. reflexivity.
    reflexivity.
    eauto. rewrite Htinfident_members.  apply allocIdent_delta.  eapply deref_loc_value. constructor.
    unfold Mem.loadv.   rewrite Ptrofs.add_zero. eauto.


    eapply t_trans.
    constructor. constructor.

    (* * limit *)
    eapply t_trans.
    constructor. constructor.
    econstructor. econstructor. econstructor.
    constructor. constructor.
    rewrite M.gso. rewrite <- Hm5_lenv. eauto.  (* rewrite Heqlenv_new. rewrite M.gss. reflexivity. *)

    assert (H_dj := disjointIdent).
    solve_nodup.
    constructor 3. reflexivity.
    reflexivity.
    eauto. rewrite Htinfident_members. apply limitIdent_delta.
    eapply deref_loc_value. constructor.
    eauto.



    eapply t_trans.
    constructor. constructor.

    (* * args *)

    eapply t_trans.
    constructor. constructor.
    econstructor. econstructor. econstructor.
    constructor. constructor. rewrite M.gso. rewrite M.gso. rewrite <- Hm5_lenv.
    eauto.  (* rewrite Heqlenv_new. rewrite M.gss. reflexivity. *)
    assert (H_dj := disjointIdent).  solve_nodup.
    assert (H_dj := disjointIdent).  solve_nodup.
    constructor 3. reflexivity. reflexivity.
    eauto. rewrite Htinfident_members. apply argsIdent_delta.
    simpl. eauto.



    eapply t_trans.
    constructor. constructor.

    (* asgn! *)

    eapply clos_rt_t.

    eapply repr_asgn_fun_entry; eauto.
    rewrite M.gss. reflexivity. eauto.



    eapply t_trans. constructor. constructor.

    eapply t_trans.
    apply Hstep_m6.


    eapply t_trans.
    constructor.
    constructor. constructor. compute. reflexivity.
    constructor. constructor.


    (* lenv6 and lenv are equivalent here since argsIdent stays the same *)
    split.
    reflexivity.
    destruct Hargs_m6 as [Hargs_m61 Hargs_m62].
    inv Hargs_m62. destructAll.
    inv Hc_tinfo'.
    exists x, x0, x1, x2. split; auto. rewrite <- Hargs_m61 in H1.

    assert (M.get argsIdent (M.set argsIdent (Vptr args_b args_ofs)
                          (M.set limitIdent (Vptr alloc_b_m5 limit_ofs_m5)
                                 (M.set allocIdent (Vptr alloc_b_m5 alloc_ofs_m5) lenv_new'')))= M.get argsIdent lenv_new''').
    eapply lenv_param_asgn_map with (l := [argsIdent]). eauto.
    split. intro; intro.
    inv H13. inv H15. eapply Hnoprot_vs0. eauto.

    left. right. auto. inv H13. constructor; auto. rewrite <- H13 in H1.
    rewrite M.gss in H1. inv H1. auto.
  - (* Ehalt *)

    (* find out what v looks like in memory *)
    assert (Hof: occurs_free (Ehalt x) x) by constructor.
    destruct (Hrel_m) as [L [HL_pro Hmem]].
    apply Hmem in Hof. destruct Hof as [v6 [Hxrho Hrel_v6]].
    clear Hmem.

    (* show that we have write access to args[1] *)
    unfold correct_tinfo in Hc_tinfo.
    destruct Hc_tinfo as [alloc_b [alloc_ofs [limit_ofs [args_b [args_ofs [tinf_b [tinf_ofs [Hget_alloc [Hdiv_alloc [Hrange_alloc [Hget_limit [Hbound_limit [Hget_args [Hdj_args [Hbound_args [Hrange_args [Htinf1 [Htinf2 [Htinf3 [Htinf4 Hglobals]]]]]]]]]]]]]]]]]]]].
    assert (Htemp : (0 <= 1 < max_args)%Z) by (unfold max_args; omega).

    assert (Hvalid_args1:= Hrange_args _ Htemp).
    clear Htemp.

    inv Hrel_v6.

    + (* halt on a function *)
      inv H1. rewrite H0 in H3. inv H3.

      assert (Hvv  :=  Mem.valid_access_store _ _ _ _ (Vptr b0 Ptrofs.zero) Hvalid_args1).
      destruct Hvv as [m2 Hm2].

      assert (Hm2_u : Mem.unchanged_on L m m2). {
        inv HL_pro.
        destructAll.
        eapply Mem.store_unchanged_on; eauto; intros.
        rewrite Hget_args in H9; inv H9.
        apply H10 with (z := 1%Z).
        unfold max_args; omega.
        rewrite Ptrofs.mul_one in *.
        simpl. unfold int_size in *; eauto.
      }
      exists m2, lenv.

      split.

      *
        apply t_step.
        eapply step_assign with (v := (Vptr b0 Ptrofs.zero)) (m' := m2).
        {
          constructor.
          econstructor. constructor; eauto.
          constructor. simpl. unfold sem_add. simpl. reflexivity.
        }
        assert (Hvorfv : get_var_or_funvar p lenv x (Vptr b0 (Ptrofs.repr 0))).
        {
          constructor. auto.
        }
        assert (HvorfvEval := get_var_or_funvar_eval threadInfIdent nParam fenv finfo_env p lenv x (Vptr b0 (Ptrofs.repr 0)) m Hsym HfinfoCorrect Hvorfv).
        assert (HvorfvEq : var_or_funvar_f threadInfIdent nParam fenv finfo_env p x = makeVar threadInfIdent nParam x fenv finfo_env).
        {
          unfold var_or_funvar_f. rewrite H0. reflexivity.
        }
        rewrite <- HvorfvEq.
        eassumption.
        assert (Hvorfv : get_var_or_funvar p lenv x (Vptr b0 (Ptrofs.repr 0))).
        {
          constructor. auto.
        }
        assert (HvorfvEq : var_or_funvar_f threadInfIdent nParam fenv finfo_env p x = makeVar threadInfIdent nParam x fenv finfo_env).
        {
          unfold var_or_funvar_f. rewrite H0. reflexivity.
        }
        rewrite <- HvorfvEq.
        eapply get_var_or_funvar_semcast; eauto.
        econstructor. simpl. reflexivity. apply Hm2.
      * unfold arg_val_LambdaANF_Codegen. split. reflexivity.
        exists args_b, args_ofs, (Vptr b0 Ptrofs.zero), L.
        split; auto. rewrite Ptrofs.mul_one in Hm2. split.
        eapply Mem.load_store_same in Hm2.
        simpl in Hm2. auto.
        rewrite Hxrho in H; inv H.
        eapply repr_val_L_unchanged; eauto.
      * rewrite H0 in H3; inv H3.
    + (* halt on constr or vint *)
      inv H1. rewrite H4 in H0; inv H0.
      clear H4.
      assert (Hvv  :=  Mem.valid_access_store _ _ _ _ v7 Hvalid_args1).
      destruct Hvv as [m2 Hm2].
      assert (Hm2_u : Mem.unchanged_on L m m2). {
        inv HL_pro.
        destructAll.
        eapply Mem.store_unchanged_on; eauto; intros.
        rewrite Hget_args in H10; inv H10.
        apply H11 with (z := 1%Z).
        unfold max_args; omega.
        rewrite Ptrofs.mul_one in *.
        simpl. unfold int_size in *; eauto.
      }
      exists m2, lenv.
      split.
      * apply t_step. eapply step_assign with (v := v7) (m' := m2).
        {
          constructor.
          econstructor. constructor; eauto.
          constructor. simpl. unfold sem_add. simpl. reflexivity.
        }
        econstructor. eauto.  simpl.
        unfold sem_cast. simpl. inv H3; reflexivity.
        econstructor. constructor.
        simpl. apply Hm2.
      * unfold arg_val_LambdaANF_Codegen. split. reflexivity.
        exists args_b, args_ofs, v7, L.
        split; auto. split.
        rewrite Ptrofs.mul_one in Hm2.
        eapply Mem.load_store_same in Hm2. simpl in Hm2. destruct v7; inv H3; auto.
        rewrite H in Hxrho. inv Hxrho.
        eapply repr_val_L_unchanged; eauto.
Admitted.



(* Top level theorem on the LambdaANF_to_Clight translation
Theorem top_repr_LambdaANF_Codegen_are_related:
   forall fds e,
well_formed (Efun fds e) ->
proper_cenv cenv ->
proper_cenv_of_exp cenv e ->
compile e cenv nenv = ...

 *)
