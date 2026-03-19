(* Common definitions for converting MetaRocq Erasure (EAst.term) to LambdaANF *)

(** Stdlib *)
From Stdlib Require Import ZArith.ZArith Lists.List Arith.Arith.

(** MetaRocq *)
From MetaRocq.Erasure Require Import EAst EPrimitive.
From MetaRocq.Common Require Import Primitive Kernames.
From MetaRocq.Utils Require Import bytestring.

(** CompCert *)
From compcert Require Import lib.Maps.

(** CertiRocq *)
From CertiRocq.Common Require Import AstCommon.
From CertiRocq Require Import Pipeline_utils.
From CertiRocq.LambdaANF Require Import cps ctx.

Import ListNotations.
Open Scope bs_scope.

Local Notation string := bytestring.string.

(** * Constructor discriminant *)

Definition dcon : Set := inductive * N.

Definition dcon_of_con (i : inductive) (n : nat) : dcon := (i, N.of_nat n).

(** * Constructor tag mapping *)

Definition conId_map := list (dcon * ctor_tag).

Theorem conId_dec: forall x y:dcon, {x = y} + {x <> y}.
Proof.
  intros. destruct x,y.
  assert (H:= AstCommon.inductive_dec i i0).
  destruct H.
  - destruct (classes.eq_dec n n0).
    + subst. left. auto.
    + right. intro. apply n1. inversion H. auto.
  - right; intro; apply n1. inversion H; auto.
Defined.

Section TagLookup.

  Context (default_tag : positive).

  Fixpoint dcon_to_info (a:dcon) (sig:conId_map) :=
    match sig with
    | nil => default_tag
    | ((cId, inf)::sig') => match conId_dec a cId with
                            | left _ => inf
                            | right _ => dcon_to_info a sig'
                            end
    end.

  Definition dcon_to_tag (a:dcon) (sig:conId_map) :=
    dcon_to_info a sig.

End TagLookup.

Definition constr_env : Type := conId_map.

(** * Global constant environment *)

(** Map from global constant names to LambdaANF variables.
    Built when processing the global environment; used to translate [tConst]. *)
Definition const_map := list (kername * var).

Fixpoint lookup_const (cm : const_map) (k : kername) : option var :=
  match cm with
  | [] => None
  | (k', v) :: cm' =>
    if eq_kername k k' then Some v else lookup_const cm' k
  end.

(** Primitive lookup *)
Fixpoint find_prim (prims : list (primitive * positive)) (n : kername) : option positive :=
  match prims with
  | [] => None
  | (prim, pos) :: prims =>
    if eq_kername n prim.(prim_name) then Some pos else find_prim prims n
  end.


(** * Inductive environment processing *)

Definition ienv := list (Kernames.kername * AstCommon.itypPack).

Fixpoint fromN (n:positive) (m:nat) : list positive * positive :=
  match m with
  | O => (nil, n)
  | S m' =>
    let (l, nm) := (fromN (n+1) (m')) in
    (n::l, nm)
  end.

(** Bind m projections. The first variable in the list binds the last constructor argument. *)
Fixpoint ctx_bind_proj (tg:ctor_tag) (r:positive) (vars : list var) (args:nat)
  : exp_ctx :=
  match vars with
  | [] => Hole_c
  | v :: vars =>
    let ctx_p' := ctx_bind_proj tg r vars (args - 1) in
    (Eproj_c v tg (N.of_nat (args - 1)) r ctx_p')
  end.

Section InductiveEnv.

  Context (default_tag default_itag : positive).

  Fixpoint convert_cnstrs (tyname:string) (cct:list ctor_tag) (itC:list AstCommon.Cnstr)
           (ind:Kernames.inductive) (nCon:N) (unboxed : N) (boxed : N)
           (niT:ind_tag) (ce:ctor_env) (dcm:conId_map) :=
    match (cct, itC) with
    | (cn::cct', cst::icT') =>
      let (cname, ccn) := cst in
      let is_unboxed := Nat.eqb ccn 0 in
      let info := {| ctor_name := BasicAst.nNamed cname
                     ; ctor_ind_name := BasicAst.nNamed tyname
                     ; ctor_ind_tag := niT
                     ; ctor_arity := N.of_nat ccn
                     ; ctor_ordinal := if is_unboxed then unboxed else boxed
                  |} in
      convert_cnstrs tyname cct' icT' ind (nCon+1)%N
                     (if is_unboxed then unboxed + 1 else unboxed)
                     (if is_unboxed then boxed else boxed + 1)
                     niT
                     (M.set cn info ce)
                     (((ind,nCon), cn)::dcm)
    | (_, _) => (ce, dcm)
    end.

  Fixpoint convert_typack typ (idBundle:Kernames.kername) (n:nat)
           (ice : (ind_env * ctor_env * ctor_tag * ind_tag * conId_map))
    : (ind_env * ctor_env * ctor_tag * ind_tag * conId_map) :=
    let '(ie, ce, ncT, niT, dcm) := ice in
    match typ with
    | nil => ice
    | (AstCommon.mkItyp itN itC) :: typ' =>
      let (cct, ncT') := fromN ncT (List.length itC) in
      let (ce', dcm') :=
          convert_cnstrs itN cct itC (Kernames.mkInd idBundle n) 0 0 0 niT ce dcm
      in
      let ityi :=
          combine cct (map (fun (c:AstCommon.Cnstr) =>
                              let (_, n) := c in N.of_nat n) itC)
      in
      convert_typack typ' idBundle (n+1)
                     (M.set niT ityi ie, ce', ncT', (Pos.succ niT), dcm')
    end.

  Fixpoint convert_env' (g:ienv) (ice:ind_env * ctor_env * ctor_tag * ind_tag * conId_map)
    : (ind_env * ctor_env * ctor_tag * ind_tag * conId_map) :=
    let '(ie, ce, ncT, niT, dcm) := ice in
    match g with
    | nil => ice
    | (id, ty)::g' =>
      convert_env' g' (convert_typack ty id 0 (ie, ce, ncT, niT, dcm))
    end.

  Definition convert_env (g:ienv): (ind_env * ctor_env * ctor_tag * ind_tag * conId_map) :=
    let default_ind_env := M.set default_itag (cons (default_tag, 0%N) nil) (M.empty ind_ty_info) in
    let info := {| ctor_name := BasicAst.nAnon
                   ; ctor_ind_name := BasicAst.nAnon
                   ; ctor_ind_tag := default_itag
                   ; ctor_arity := 0%N
                   ; ctor_ordinal := 0%N
                |} in
    let default_ctor_env := M.set default_tag info (M.empty ctor_ty_info) in
    convert_env' g (default_ind_env, default_ctor_env, (Pos.succ default_tag:ctor_tag), (Pos.succ default_itag:ind_tag), nil).

End InductiveEnv.


(** * Primitive value translation *)

(** Translate MetaRocq's [prim_val] to CertiRocq's [primitive_value].
    Arrays are not supported and return [None]. *)
Definition trans_prim_val {T} (p : EPrimitive.prim_val T) : option primitive_value :=
  match prim_val_model p in prim_model t return option primitive_value with
  | primIntModel i => Some (existT _ AstCommon.primInt i)
  | primFloatModel f => Some (existT _ AstCommon.primFloat f)
  | primStringModel s => Some (existT _ AstCommon.primString s)
  | primArrayModel _ => None
  end.


(** * Helper: pad name list to given length *)

Fixpoint names_lst_len (ns : list name) (m : nat) : list name :=
  match ns, m with
  | _, 0%nat => []
  | [], S _ => repeat nAnon m
  | n :: ns, S m => n :: names_lst_len ns m
  end.
