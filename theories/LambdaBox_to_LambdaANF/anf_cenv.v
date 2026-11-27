(** * Constructor environments along ANF conversion and the LambdaANF pipeline

    ANF conversion does not modify the constructor environment computed from the inductive
    declarations ([convert_top_anf_cenv]), and the LambdaANF pipeline only extends it with fresh
    tags ([anf_pipeline_cenv_extends]): closure conversion registers the constructors of
    closure environments, and the closure constructor. *)

From Stdlib Require Import ssreflect ssrbool.
From Stdlib Require Import ZArith List RelationClasses Lia.
Require Import Common.Common Common.compM Common.Pipeline_utils.
Require Import ExtLib.Structures.Monad.
From MetaRocq.Utils Require Import All_Forall.
From CertiRocq.LambdaANF Require Import term state toplevel.
From CertiRocq.LambdaBox_to_LambdaANF Require Import common anf.

Import Monads.
Import MonadNotation.
Import ListNotations.

(** ** Constructor environments *)

(** [cenv'] extends [cenv] *)
Definition cenv_extends (cenv cenv' : ctor_env) : Prop :=
  forall t info, M.get t cenv = Some info -> M.get t cenv' = Some info.

(** All the tags of [cenv] are smaller than [t] *)
Definition fresh_ctor_tags (cenv : ctor_env) (t : ctor_tag) : Prop :=
  forall t' info, M.get t' cenv = Some info -> (t' < t)%positive.

Lemma cenv_extends_trans c1 c2 c3 :
  cenv_extends c1 c2 -> cenv_extends c2 c3 -> cenv_extends c1 c3.
Proof. intros h1 h2 t i h. now apply h2, h1. Qed.

(** ** Computations preserving a relation on the compilation state *)

Section Preserves.

  Context (Rel : comp_data -> comp_data -> Prop) {HRel : PreOrder Rel}.

  (** The relation contains the identity on the constructor environment and tag *)
  Context (Hstable : forall c c',
    state.cenv c' = state.cenv c -> nect_ctor_tag c' = nect_ctor_tag c -> Rel c c').

  (** [m] relates its initial and final compilation states, whether it fails or not *)
  Definition pres {S A} (m : @compM' S A) : Prop :=
    forall c s, Rel c (fst (snd (compM.runState m tt (c, s)))).

  Lemma pres_ret {S A} (x : A) : pres (S := S) (ret x).
  Proof. intros c s. cbn. reflexivity. Qed.

  Lemma pres_failwith {S A} msg : pres (S := S) (A := A) (failwith msg).
  Proof. intros c s. cbn. reflexivity. Qed.

  Lemma pres_bind {S A B} (m : @compM' S A) (f : A -> @compM' S B) :
    pres m -> (forall x, pres (f x)) -> pres (x <- m ;; f x).
  Proof.
    intros hm hf c s. specialize (hm c s). destruct m as [fm]. cbn in *.
    destruct (fm tt (c, s)) as [[|a] [c' s']]; cbn in * => //.
    etransitivity; [exact hm|]. apply hf.
  Qed.

  Ltac pres_prim := intros [] ?; cbn; apply Hstable; reflexivity.

  Lemma pres_get_named {S} na : pres (S := S) (get_named na).
  Proof. pres_prim. Qed.

  Lemma pres_get_named_str {S} na : pres (S := S) (get_named_str na).
  Proof. pres_prim. Qed.

  Lemma pres_reserve_named_var {S} x na : pres (S := S) (reserve_named_var x na).
  Proof. pres_prim. Qed.

  Lemma pres_set_var_name {S} x na : pres (S := S) (set_var_name x na).
  Proof. pres_prim. Qed.

  Lemma pres_mapM {S A B} (f : A -> @compM' S B) l :
    (forall x, pres (f x)) -> pres (mapM f l).
  Proof.
    intros hf. induction l as [|x l IH]; cbn [mapM]; [apply pres_ret|].
    apply pres_bind => // y. apply pres_bind => // ys. apply pres_ret.
  Qed.

  Lemma pres_get_named_lst {S} l : pres (S := S) (get_named_lst l).
  Proof. apply pres_mapM, pres_get_named. Qed.

  Lemma pres_get_name {S} x suff : pres (S := S) (get_name x suff).
  Proof. pres_prim. Qed.

  Lemma pres_get_name' {S} x suff nenv : pres (S := S) (get_name' x suff nenv).
  Proof. pres_prim. Qed.

  Lemma pres_get_names_lst {S} xs suff : pres (S := S) (get_names_lst xs suff).
  Proof. apply pres_mapM => x. apply pres_get_name. Qed.

  Lemma pres_get_names_lst' {S} xs suff nenv : pres (S := S) (get_names_lst' xs suff nenv).
  Proof. apply pres_mapM => x. apply pres_get_name'. Qed.

  Lemma pres_get_ftag {S} n : pres (S := S) (get_ftag n).
  Proof. pres_prim. Qed.

  Lemma pres_get_state {S} u : pres (S := S) (get_state u).
  Proof. pres_prim. Qed.

  Lemma pres_put_state {S} st : pres (S := S) (put_state st).
  Proof. pres_prim. Qed.

  Lemma pres_log_msg {S} msg : pres (S := S) (log_msg msg).
  Proof. pres_prim. Qed.

  Lemma pres_get_name_env {S} u : pres (S := S) (get_name_env u).
  Proof. pres_prim. Qed.

  Lemma pres_get_pp_name {S} x : pres (S := S) (get_pp_name x).
  Proof. pres_prim. Qed.

  Lemma pres_get_pp_names_list {S} xs : pres (S := S) (get_pp_names_list xs).
  Proof. apply pres_mapM => x. apply pres_get_pp_name. Qed.

End Preserves.

(** One step of a proof of [pres], for a relation with preorder proof [hpre] and stability
    proof [hst] *)
Ltac pres_gen hpre hst :=
  lazymatch goal with
  | |- PreOrder _ => exact hpre
  | |- pres _ (Monad.ret _) => apply pres_ret; exact hpre
  | |- pres _ (failwith _) => apply pres_failwith; exact hpre
  | |- pres _ (get_named _) => refine (pres_get_named _ hst _)
  | |- pres _ (get_named_str _) => refine (pres_get_named_str _ hst _)
  | |- pres _ (reserve_named_var _ _) => refine (pres_reserve_named_var _ hst _ _)
  | |- pres _ (set_var_name _ _) => refine (pres_set_var_name _ hst _ _)
  | |- pres _ (get_named_lst _) => refine (pres_get_named_lst _ hst _)
  | |- pres _ (get_name _ _) => refine (pres_get_name _ hst _ _)
  | |- pres _ (get_name' _ _ _) => refine (pres_get_name' _ hst _ _ _)
  | |- pres _ (get_names_lst _ _) => refine (pres_get_names_lst _ hst _ _)
  | |- pres _ (get_names_lst' _ _ _) => refine (pres_get_names_lst' _ hst _ _ _)
  | |- pres _ (get_ftag _) => refine (pres_get_ftag _ hst _)
  | |- pres _ (get_state _) => refine (pres_get_state _ hst tt)
  | |- pres _ (put_state _) => refine (pres_put_state _ hst _)
  | |- pres _ (log_msg _) => refine (pres_log_msg _ hst _)
  | |- pres _ (get_name_env _) => refine (pres_get_name_env _ hst tt)
  | |- pres _ (get_pp_name _) => refine (pres_get_pp_name _ hst _)
  | |- pres _ (get_pp_names_list _) => refine (pres_get_pp_names_list _ hst _)
  | |- pres _ (Monad.bind _ _) => apply pres_bind; [exact hpre| |intros ?]
  | |- pres _ (match ?x with _ => _ end) => destruct x
  end.

(** ** ANF conversion *)

(** ANF conversion leaves the constructor environment and the next constructor tag unchanged *)
Definition same_cenv (c c' : comp_data) : Prop :=
  state.cenv c' = state.cenv c /\ nect_ctor_tag c' = nect_ctor_tag c.

#[local] Instance same_cenv_preorder : PreOrder same_cenv.
Proof.
  split.
  - now intros c.
  - intros c1 c2 c3 [h1 h1'] [h2 h2']. split; congruence.
Qed.

Lemma same_cenv_stable c c' :
  state.cenv c' = state.cenv c -> nect_ctor_tag c' = nect_ctor_tag c -> same_cenv c c'.
Proof. now split. Qed.

Ltac pres_step := pres_gen same_cenv_preorder same_cenv_stable.

Section ANF.
  Context (func_tag default_tag : positive) (prim_map : M.t primitive) (tgm : conId_map)
    (prims : list (primitive * positive)).

  Lemma pres_get_named_or_reserve rname na : pres same_cenv (get_named_or_reserve rname na).
  Proof. destruct rname; cbn [get_named_or_reserve]; repeat pres_step. Qed.

  Lemma pres_proj_ctx names n scrut vm ct : pres same_cenv (proj_ctx names n scrut vm ct).
  Proof. unfold proj_ctx. repeat pres_step. Qed.

  Lemma pres_add_fix_names mfix vm idx rname : pres same_cenv (add_fix_names mfix vm idx rname).
  Proof.
    induction mfix in vm, idx |- *; cbn [add_fix_names]; repeat pres_step.
    all: try apply pres_get_named_or_reserve; auto.
  Qed.

  Lemma pres_convert_prim_anf n prim args rname :
    pres same_cenv (convert_prim_anf func_tag n prim args rname).
  Proof.
    induction n in args, rname |- *; cbn [convert_prim_anf]; repeat pres_step.
    all: try apply pres_get_named_or_reserve; auto.
  Qed.

  Lemma pres_convert_anf_args conv args vm :
    All (fun t => forall vm, pres same_cenv (conv t vm)) args ->
    pres same_cenv (convert_anf_args conv args vm).
  Proof.
    unfold convert_anf_args. induction 1; cbv beta iota fix; repeat pres_step; auto.
  Qed.

  Lemma pres_convert_anf_mfix conv mfix names idx vm :
    All (fun d => match EAst.dbody d with
                  | EAst.tLambda _ e1 => forall vm, pres same_cenv (conv e1 vm)
                  | _ => True end) mfix ->
    pres same_cenv (convert_anf_mfix func_tag conv mfix names idx vm).
  Proof.
    unfold convert_anf_mfix. intros hall.
    induction hall as [|d mfix hd hall IH] in names, idx |- *; destruct names;
      cbv beta iota fix; repeat pres_step; auto.
  Qed.

  Lemma pres_convert_anf_branches conv ind brs n scrut vm :
    All (fun br => forall vm, pres same_cenv (conv (snd br) vm)) brs ->
    pres same_cenv (convert_anf_branches tgm conv ind brs n scrut vm).
  Proof.
    unfold convert_anf_branches. intros hall.
    induction hall as [|[lnames e] brs hd hall IH] in n |- *; cbv beta iota fix;
      repeat pres_step; auto; try apply pres_proj_ctx.
  Qed.

  Lemma pres_convert_anf cmap t vm rname :
    pres same_cenv (convert_anf func_tag default_tag prim_map tgm prims cmap t vm rname).
  Proof.
    induction t using term_ind_fix_body in vm, rname |- *; cbn [convert_anf];
      repeat (pres_step || apply pres_get_named_or_reserve || apply pres_convert_prim_anf
        || apply pres_proj_ctx || apply pres_add_fix_names || auto).
    - apply pres_convert_anf_args. eapply All_impl; [exact X|]. cbn. auto.
    - apply pres_convert_anf_branches. eapply All_impl; [exact X|]. cbn. auto.
    - apply pres_convert_anf_mfix. eapply All_impl; [exact X|]. cbn. intros d.
      destruct EAst.dbody => //.
  Qed.

  Lemma pres_convert_global_decls preferred gd cm :
    pres same_cenv (convert_global_decls func_tag default_tag prim_map tgm prims preferred gd cm).
  Proof.
    induction gd as [|[k [[[body|]]|]] gd IH] in cm |- *; cbn [convert_global_decls];
      repeat (pres_step || apply pres_convert_anf || auto).
  Qed.

End ANF.

(** ** The constructor environment computed from the inductive declarations *)

(** All the tags of [cenv] are in [[lo, hi)] *)
Definition tags_between (cenv : ctor_env) (lo hi : ctor_tag) : Prop :=
  forall t info, M.get t cenv = Some info -> (lo <= t < hi)%positive.

Lemma fromN_spec n m :
  let '(l, n') := fromN n m in (n <= n')%positive /\ forall t, In t l -> (n <= t < n')%positive.
Proof.
  induction m as [|m IH] in n |- *; cbn; [split; [lia|easy]|].
  specialize (IH (n + 1)%positive). destruct fromN as [l nm]. destruct IH as [hle hin].
  split; [lia|]. intros t [<-|ht]; [lia|]. specialize (hin t ht). lia.
Qed.

Lemma convert_cnstrs_tags tyname cct itC ind nCon unb box niT ce dcm lo hi :
  tags_between ce lo hi -> (forall t, In t cct -> (lo <= t < hi)%positive) ->
  tags_between (fst (convert_cnstrs tyname cct itC ind nCon unb box niT ce dcm)) lo hi.
Proof.
  induction cct as [|cn cct IH] in itC, nCon, unb, box, ce, dcm |- *; intros hce hcct;
    destruct itC as [|[cname ccn] itC]; cbn => //.
  apply IH; [|intros t ht; apply hcct; now right].
  intros t i. rewrite M.gsspec. destruct Coqlib.peq; [subst|now apply hce].
  intros _. apply hcct. now left.
Qed.

Lemma convert_typack_tags typ id n ie ce ct it dcm lo :
  tags_between ce lo ct -> (lo < ct)%positive ->
  let '(_, ce', ct', _, _) := convert_typack typ id n (ie, ce, ct, it, dcm) in
  tags_between ce' lo ct' /\ (lo < ct')%positive.
Proof.
  induction typ as [|[itN itC] typ IH] in n, ie, ce, ct, it, dcm |- *; intros hce hlo; cbn => //.
  have := fromN_spec ct (List.length itC). destruct fromN as [cct ct'] => -[hle hin].
  destruct convert_cnstrs as [ce' dcm'] eqn:hcv.
  apply IH; [|lia].
  have := convert_cnstrs_tags itN cct itC (Kernames.mkInd id n) 0 0 0 it ce dcm lo ct'.
  rewrite hcv. apply.
  - intros t i hi. specialize (hce t i hi). lia.
  - intros t ht. specialize (hin t ht). lia.
Qed.

Lemma convert_env'_tags g ie ce ct it dcm lo :
  tags_between ce lo ct -> (lo < ct)%positive ->
  let '(_, ce', ct', _, _) := convert_env' g (ie, ce, ct, it, dcm) in
  tags_between ce' lo ct' /\ (lo < ct')%positive.
Proof.
  induction g as [|[id ty] g IH] in ie, ce, ct, it, dcm |- *; intros hce hlo; cbn => //.
  have := convert_typack_tags ty id 0 ie ce ct it dcm lo hce hlo.
  destruct convert_typack as [[[[ie' ce'] ct'] it'] dcm'] => -[hce' hlo'].
  now apply IH.
Qed.

Lemma convert_env_tags default_tag default_itag ie :
  let '(_, ce, ct, _, _) := convert_env default_tag default_itag ie in
  tags_between ce default_tag ct /\ (default_tag < ct)%positive.
Proof.
  unfold convert_env.
  have := convert_env'_tags ie
    (M.set default_itag [(default_tag, 0%N)] (M.empty ind_ty_info))
    (M.set default_tag {| ctor_name := BasicAst.nAnon; ctor_ind_name := BasicAst.nAnon;
      ctor_ind_tag := default_itag; ctor_arity := 0%N; ctor_ordinal := 0%N |}
      (M.empty ctor_ty_info))
    (Pos.succ default_tag) (Pos.succ default_itag) [] default_tag.
  destruct convert_env' as [[[[ie' ce'] ct'] it'] dcm'].
  intros h. apply h; [|lia].
  intros t i. rewrite M.gsspec. destruct Coqlib.peq; [subst; lia|].
  now rewrite M.gempty.
Qed.

(** ANF conversion does not modify the constructor environment computed from the inductive
    declarations, whose tags are all between [default_tag] and the next free tag *)
Lemma convert_top_anf_cenv func_tag default_tag prim_map default_itag next_id prims
  preferred ie gd e res comp_d :
  convert_top_anf func_tag default_tag prim_map default_itag next_id prims preferred ie gd e =
    (res, comp_d) ->
  state.cenv comp_d = top_cenv default_tag default_itag ie /\
  tags_between (state.cenv comp_d) default_tag (nect_ctor_tag comp_d) /\
  (default_tag < nect_ctor_tag comp_d)%positive.
Proof.
  unfold convert_top_anf, top_cenv.
  have := convert_env_tags default_tag default_itag ie.
  destruct convert_env as [[[[ie' ce] ct] it] dcm] => htags.
  set (prog := Monad.bind _ _).
  set (c0 := pack_data _ _ _ _ _ _ _ _ _).
  have hpres : pres same_cenv prog.
  { subst prog. repeat (pres_step || apply pres_convert_global_decls || apply pres_convert_anf). }
  unfold run_compM. specialize (hpres c0 tt).
  destruct (compM.runState prog tt (c0, tt)) as [r [c' []]]. intros [= <- <-].
  cbn in hpres. destruct hpres as [hc ht]. rewrite hc ht. cbn. now split.
Qed.

(** ** The LambdaANF pipeline *)

Definition clo_info : ctor_ty_info :=
  {| ctor_name := BasicAst.nAnon; ctor_ind_name := BasicAst.nAnon; ctor_ind_tag := clo_ind_tag;
     ctor_arity := 2%N; ctor_ordinal := 0%N |}.

(** The invariant on the constructor environment maintained by the LambdaANF pipeline: the
    next constructor tag is fresh, and the closure constructor is either not registered yet or
    registered with its expected information *)
Definition cenv_ok (c : comp_data) : Prop :=
  fresh_ctor_tags (state.cenv c) (nect_ctor_tag c) /\ (clo_tag < nect_ctor_tag c)%positive /\
  (M.get clo_tag (state.cenv c) = None \/ M.get clo_tag (state.cenv c) = Some clo_info).

(** The passes preserve the invariant and only extend the constructor environment *)
Definition cenv_R (c c' : comp_data) : Prop :=
  cenv_ok c -> cenv_ok c' /\ cenv_extends (state.cenv c) (state.cenv c').

#[local] Instance cenv_R_preorder : PreOrder cenv_R.
Proof.
  split.
  - intros c h. split => //.
  - intros c1 c2 c3 h12 h23 h1. destruct (h12 h1) as [h2 e12]. destruct (h23 h2) as [h3 e23].
    split => //. eapply cenv_extends_trans; eauto.
Qed.

Lemma cenv_R_stable c c' :
  state.cenv c' = state.cenv c -> nect_ctor_tag c' = nect_ctor_tag c -> cenv_R c c'.
Proof.
  intros hc ht h. rewrite /cenv_ok hc ht. split => //.
Qed.

Ltac pres_R := pres_gen cenv_R_preorder cenv_R_stable.

Lemma pres_make_record_ctor_tag {S} n : pres (S := S) cenv_R (make_record_ctor_tag n).
Proof.
  intros [] s [hfresh [hclo hget]]; cbn in *. rewrite /cenv_ok /=. split; [split; [|split]|].
  - intros t i. rewrite M.gsspec. destruct Coqlib.peq; [subst; lia|].
    intros h. specialize (hfresh _ _ h). lia.
  - lia.
  - rewrite M.gso //. intros heq. rewrite heq in hclo. lia.
  - intros t i h. rewrite M.gso //. intros ->. specialize (hfresh _ _ h). lia.
Qed.

Lemma add_closure_tag_R c :
  cenv_R c (put_ctor_env (add_closure_tag clo_tag clo_ind_tag (state.cenv c)) c).
Proof.
  destruct c as [? ? ? ? cenv ? ? ? ?]. rewrite /cenv_R /cenv_ok /=. intros [hfresh [hclo hget]].
  split; [split; [|split]|].
  - intros t i. rewrite M.gsspec. destruct Coqlib.peq; [subst; lia|]. apply hfresh.
  - lia.
  - right. now rewrite M.gss.
  - intros t i h. rewrite M.gsspec. destruct Coqlib.peq => //. subst.
    destruct hget as [hget|hget]; rewrite h in hget; [discriminate|].
    injection hget as ->. reflexivity.
Qed.

(** Computations in the [anf_state] monad of the LambdaANF pipeline *)
Definition apres {A} (m : anf_state A) : Prop := forall c, cenv_R c (snd (m c)).

(** The invariant holds for the compilation state built from ANF conversion, whose constructor
    tags are all above [default_ctor_tag] *)
Lemma cenv_ok_init c :
  tags_between (state.cenv c) default_ctor_tag (nect_ctor_tag c) ->
  (default_ctor_tag < nect_ctor_tag c)%positive -> cenv_ok c.
Proof.
  intros htags hlt. split; [|split].
  - intros t i h. now apply (htags t i h).
  - rewrite /clo_tag. rewrite /default_ctor_tag in hlt. lia.
  - left. destruct (M.get clo_tag (state.cenv c)) eqn:h => //.
    apply htags in h. rewrite /clo_tag /default_ctor_tag in h. lia.
Qed.

Lemma apres_ret {A} (x : A) : apres (ret x).
Proof. intros c. cbn. reflexivity. Qed.

Lemma apres_bind {A B} (m : anf_state A) (f : A -> anf_state B) :
  apres m -> (forall x, apres (f x)) -> apres (x <- m ;; f x).
Proof.
  intros hm hf c. specialize (hm c). cbv [Monad.bind toplevel.MonadState].
  destruct (m c) as [[|a] c']; cbn in hm |- * => //.
  etransitivity; [exact hm|]. apply hf.
Qed.

Lemma apres_time_anf {A B} opts name (f : A -> anf_state B) x :
  apres (f x) -> apres (time_anf opts name f x).
Proof. intros h c. unfold time_anf. now destruct time. Qed.

(** From [pres] in [compM'] to [apres], for a pass run with [run_compM] *)
Lemma apres_run_compM {S A} (m : @compM' S A) s :
  pres cenv_R m -> apres (fun c => let '(r, (c', _)) := run_compM m c s in (r, c')).
Proof.
  intros h c. specialize (h c s). unfold run_compM. cbn in h.
  destruct compM.runState as [r [c' s']]. exact h.
Qed.

(** *** Uncurrying *)

Lemma pres_uncurry cps :
  (forall e, pres cenv_R (uncurry.uncurry_exp cps e)) /\
  (forall fds, pres cenv_R (uncurry.uncurry_fundefs cps fds)).
Proof.
  apply exp_def_mutual_ind'; intros; cbn [uncurry.uncurry_exp uncurry.uncurry_fundefs];
    rewrite /uncurry.already_uncurried /uncurry.mark_as_uncurried /uncurry.click
      /uncurry.markToInline /uncurry.get_fun_tag;
    repeat (assumption || pres_R).
  induction H as [|[c e] arms he hl IH]; cbv beta iota fix; repeat (assumption || pres_R).
Qed.

Lemma apres_uncurry_top cps e : apres (uncurry.uncurry_top cps e).
Proof.
  intros c. unfold uncurry.uncurry_top, uncurry.uncurry_fuel, uncurry.uncurry_fuel''.
  set (n := uncurry.uncurry_passes_exp e).
  have h : pres cenv_R (uncurry.uncurry_fuel' uncurry.uncurry_exp cps n e).
  { clearbody n. induction n as [|n IH] in e |- *; cbn [uncurry.uncurry_fuel'];
      rewrite /uncurry.uncurry /uncurry.has_clicked /uncurry.unclick;
      repeat (assumption || apply pres_uncurry || apply IH || pres_R). }
  specialize (h c (false, M.empty _, M.empty _, (0%nat, M.empty _))).
  unfold run_compM. destruct compM.runState as [r [c' [[[? ?] ?] [? ?]]]].
  cbn in h |- *. etransitivity; [exact h|]. apply cenv_R_stable; now destruct c'.
Qed.

(** *** Inlining *)

(** All the function bodies of a block of function definitions satisfy [P] *)
Fixpoint fundefs_all (P : exp -> Prop) (fds : fundefs) : Prop :=
  match fds with
  | Fnil => True
  | Fcons _ _ _ e fds' => P e /\ fundefs_all P fds'
  end.

(** Calls to the local recursive function: the induction hypotheses are stated on its
    unfolded [fix], captured from the goal *)
Ltac pres_inline_step :=
  repeat (assumption || pres_R ||
    match goal with H : forall sig fm s, pres _ _ |- _ => apply H end ||
    match goal with H : forall j e sig fm s, pres _ _ |- _ => apply H end).

Lemma pres_inline_exp St IH d :
  forall j e sig fm s, pres cenv_R (inline.inline_exp St IH d j e sig fm s).
Proof.
  induction d as [|d IHd]; intros j e sig fm s; cbn [inline.inline_exp];
    rewrite /inline.click /inline.get_fresh_name /inline.get_fresh_names;
    match goal with |- pres _ (?F e sig fm s) => revert e sig fm s;
      apply (exp_mut_alt (fun e => forall sig fm s, pres cenv_R (F e sig fm s))
        (fundefs_all (fun e => forall sig fm s, pres cenv_R (F e sig fm s)))) end;
    intros; try exact I; try (now split); cbv beta iota fix; pres_inline_step.
  (* Case analyses and blocks of functions: inner fixpoints *)
  all: first [
    match goal with H : Forall _ _ |- _ =>
      induction H as [|[c e] l he hl IH']; cbv beta iota fix; pres_inline_step end
  | match goal with H : fundefs_all ?P ?fds |- pres _ (?G ?fds ?s0) =>
      assert (Hg : forall fds0, fundefs_all P fds0 -> forall s, pres cenv_R (G fds0 s));
      [ clear H; intros fds0; induction fds0 as [f t xs e1 fds0 IHf|]; intros Hall s';
        cbv beta iota fix; [destruct Hall as [He Hf]|];
        repeat (pres_inline_step || apply IHf)
      | exact (Hg fds H s0) ] end ].
Qed.

Lemma inline_top'_R St IH max_var d s e c :
  cenv_R c (snd (fst (inline.inline_top' St IH max_var d s e c))).
Proof.
  unfold inline.inline_top'.
  destruct (inline.restart_names max_var e c) as [c1 nenv] eqn:hr.
  have h1 : cenv_R c c1.
  { revert hr. unfold inline.restart_names. destruct c. intros [= <- _].
    now apply cenv_R_stable. }
  have h := pres_inline_exp St IH d d e (M.empty _) (M.empty _) s c1 (false, nenv).
  unfold run_compM. destruct compM.runState as [r [c2 [? ?]]].
  cbn in h |- *. etransitivity; eassumption.
Qed.

Lemma apres_inline_top St IH max_var d s e : apres (inline.inline_top St IH max_var d s e).
Proof.
  intros c. have := inline_top'_R St IH max_var d s e c.
  unfold inline.inline_top. now destruct inline.inline_top' as [[? ?] ?].
Qed.

Lemma apres_inline_loop_aux St IH max_var fuel d s e :
  apres (inline.inline_loop_aux St IH max_var fuel d s e).
Proof.
  induction fuel as [|fuel IHf] in e |- *; intros c; cbn [inline.inline_loop_aux]; [reflexivity|].
  have h := inline_top'_R St IH max_var d s e c.
  destruct inline.inline_top' as [[[|e'] c'] []]; cbn in h |- * => //.
  etransitivity; [exact h|]. apply IHf.
Qed.

Lemma apres_inline_uncurry max_var bound d e : apres (inline.inline_uncurry max_var bound d e).
Proof. intros c. apply apres_inline_top. Qed.

Lemma apres_inline_shrink_loop max_var bound d e :
  apres (inline.inline_shrink_loop max_var bound d e).
Proof. apply apres_inline_loop_aux. Qed.

Lemma apres_inline_lifted max_var bound d e : apres (inline.inline_lifted max_var bound d e).
Proof. apply apres_inline_top. Qed.

(** *** Lambda lifting *)

(** [pres_R] steps, closing recursive calls with the (possibly generalized) induction hypotheses *)
Ltac pres_auto :=
  repeat (assumption || pres_R || match goal with H : forall (_ : _), _ |- _ => apply H end).

Lemma pres_add_functions B fvs sfvs args m gfuns :
  pres cenv_R (lambda_lifting.add_functions B fvs sfvs args m gfuns).
Proof.
  induction B in m, gfuns |- *; cbn [lambda_lifting.add_functions]; pres_auto.
Qed.

Lemma pres_add_free_vars fvs m : pres cenv_R (lambda_lifting.add_free_vars fvs m).
Proof.
  induction fvs in m |- *; cbn [lambda_lifting.add_free_vars]; pres_auto.
Qed.

Lemma pres_make_wrappers B fvm fm : pres cenv_R (lambda_lifting.make_wrappers B fvm fm).
Proof.
  induction B in fvm |- *; cbn [lambda_lifting.make_wrappers]; pres_auto.
Qed.

Lemma pres_lambda_lift ma mp ld :
  (forall e scope af fvm fm gfuns,
    pres cenv_R (lambda_lifting.exp_lambda_lift ma mp ld e scope af fvm fm gfuns)) /\
  (forall B Bfull fnames af fvm fm gfuns fv_no,
    pres cenv_R (lambda_lifting.fundefs_lambda_lift ma mp ld B Bfull fnames af fvm fm gfuns fv_no)).
Proof.
  apply exp_def_mutual_ind'; intros;
    cbn [lambda_lifting.exp_lambda_lift lambda_lifting.fundefs_lambda_lift];
    repeat (assumption || pres_R || apply pres_add_functions || apply pres_add_free_vars ||
      apply pres_make_wrappers || match goal with H : forall (_ : _), _ |- _ => apply H end).
  induction H as [|[c e] l he hl IH']; cbv beta iota fix;
    repeat (assumption || pres_R || apply he).
Qed.

Lemma apres_lambda_lift args no_push inl e : apres (lambda_lifting.lambda_lift args no_push inl e).
Proof. apply apres_run_compM, pres_lambda_lift. Qed.

(** *** Closure conversion: the only pass registering new constructors *)

Lemma pres_get_var ct e0 x map gfuns c Γ :
  pres cenv_R (closure_conversion.get_var ct e0 x map gfuns c Γ).
Proof. unfold closure_conversion.get_var. pres_auto. Qed.

Lemma pres_get_vars ct e0 xs map gfuns c Γ :
  pres cenv_R (closure_conversion.get_vars ct e0 xs map gfuns c Γ).
Proof.
  induction xs; cbn [closure_conversion.get_vars]; repeat (pres_auto || apply pres_get_var).
Qed.

Lemma pres_make_env_tag e0 n : pres cenv_R (closure_conversion.make_env_tag e0 n).
Proof.
  destruct n; cbn [closure_conversion.make_env_tag]; [pres_R|apply pres_make_record_ctor_tag].
Qed.

Lemma pres_make_env ct e0 fvs mnew mold c Γn Γo gfuns :
  pres cenv_R (closure_conversion.make_env ct e0 fvs mnew mold c Γn Γo gfuns).
Proof.
  unfold closure_conversion.make_env.
  repeat (pres_auto || apply pres_get_vars || apply pres_make_env_tag).
Qed.

Lemma pres_closure_conv ct e0 :
  (forall e mapfv gfuns c Γ,
    pres cenv_R (closure_conversion.exp_closure_conv ct e0 e mapfv gfuns c Γ)) /\
  (forall defs all_defs mapfv gfuns c,
    pres cenv_R (closure_conversion.fundefs_closure_conv ct e0 all_defs defs mapfv gfuns c)).
Proof.
  apply exp_def_mutual_ind'; intros;
    cbn [closure_conversion.exp_closure_conv closure_conversion.fundefs_closure_conv];
    repeat (pres_auto || apply pres_get_var || apply pres_get_vars || apply pres_make_env).
  induction H as [|[c' e] l he hl IH']; cbv beta iota fix;
    repeat (pres_auto || apply pres_get_var || apply he).
Qed.

Lemma closure_conversion_top_R e c :
  cenv_R c (snd (closure_conversion.closure_conversion_top clo_tag clo_ind_tag e c)).
Proof.
  unfold closure_conversion.closure_conversion_top.
  destruct (closure_conversion.get_name c) as [Γ c1] eqn:hg.
  have h1 : cenv_R c c1.
  { revert hg. destruct c. intros [= _ <-]. now apply cenv_R_stable. }
  set (m := Monad.bind _ _).
  have h2 : pres cenv_R m.
  { subst m. apply pres_bind; [exact cenv_R_preorder|apply pres_make_record_ctor_tag|].
    intros. apply pres_closure_conv. }
  specialize (h2 c1 tt). unfold run_compM.
  destruct compM.runState as [[|[e' f']] [c2 []]]; cbn in h2 |- *.
  - etransitivity; eassumption.
  - etransitivity; [exact h1|]. etransitivity; [exact h2|]. apply add_closure_tag_R.
Qed.

Lemma apres_closure_conversion_hoist e :
  apres (hoisting.closure_conversion_hoist clo_tag clo_ind_tag e).
Proof.
  intros c. have := closure_conversion_top_R e c. unfold hoisting.closure_conversion_hoist.
  now destruct closure_conversion.closure_conversion_top as [[|] ?].
Qed.

(** *** Dead parameter elimination *)

Lemma pres_eliminate_expr fmap L e : pres cenv_R (dead_param_elim.eliminate_expr fmap L e).
Proof.
  revert e. match goal with |- forall e, @?P e => apply (exp_mut_alt P (fun _ => True)) end;
    intros; try exact I; cbn [dead_param_elim.eliminate_expr]; pres_auto.
  induction H as [|[c e] l he hl IH']; cbv beta iota fix; pres_auto.
Qed.

Lemma pres_eliminate_fundefs fmap L B : pres cenv_R (dead_param_elim.eliminate_fundefs fmap L B).
Proof.
  induction B; cbn [dead_param_elim.eliminate_fundefs];
    repeat (pres_auto || apply pres_eliminate_expr).
Qed.

Lemma create_fun_tag_R L m B c fmap :
  cenv_R c (snd (dead_param_elim.create_fun_tag L m B c fmap)).
Proof.
  induction B as [f ft ys e B IH|] in c, fmap |- *; cbn [dead_param_elim.create_fun_tag];
    [|reflexivity].
  destruct dead_param_elim.get_fun_vars; [destruct M.get|]; try apply IH.
  destruct c. cbn. etransitivity; [|apply IH]. now apply cenv_R_stable.
Qed.

Lemma apres_DPE e : apres (dead_param_elim.DPE e).
Proof.
  intros c. unfold dead_param_elim.DPE.
  destruct dead_param_elim.is_hoisted; [|destruct c; now apply cenv_R_stable].
  destruct e as [| | | |B e'| | | |]; try reflexivity.
  destruct dead_param_elim.find_live as [s|L]; [destruct c; now apply cenv_R_stable|].
  have h1 := create_fun_tag_R L (dead_param_elim.make_arityMap (Efun B e') (M.empty _)) B c
    (M.empty _).
  destruct dead_param_elim.create_fun_tag as [ftm c1]. cbn in h1.
  have h2 := pres_eliminate_fundefs ftm L B c1 tt. unfold run_compM.
  destruct compM.runState as [[|B'] [c2 []]]; cbn in h2 |- *.
  - etransitivity; eassumption.
  - have h3 := pres_eliminate_expr ftm L e' c2 tt.
    destruct compM.runState as [[|e''] [c3 []]]; cbn in h3 |- *;
      (etransitivity; [exact h1|]; etransitivity; [exact h2|exact h3]).
Qed.

(** *** The pipeline *)

Lemma apres_shrink_err e : apres (shrink_cps.shrink_err e).
Proof. intros c. reflexivity. Qed.

Lemma apres_merge_dup_funs_trans e : apres (merge_dup_funs_trans e).
Proof. intros c. reflexivity. Qed.

Lemma apres_id_trans e : apres (id_trans e).
Proof. intros c. reflexivity. Qed.

Lemma apres_anf_pipeline next_var opts e : apres (anf_pipeline next_var opts e).
Proof.
  unfold anf_pipeline.
  repeat (apply apres_bind; [|intros ?] || apply apres_ret || apply apres_time_anf ||
    match goal with |- apres (if ?b then _ else _) => destruct b end).
  all: first [ apply apres_shrink_err | apply apres_uncurry_top | apply apres_inline_uncurry
             | apply apres_inline_shrink_loop | apply apres_lambda_lift
             | apply apres_closure_conversion_hoist | intros ?; apply closure_conversion_top_R
             | apply apres_DPE | apply apres_inline_lifted
             | apply apres_merge_dup_funs_trans | apply apres_id_trans ].
Qed.

(** The LambdaANF pipeline only extends the constructor environment *)
Theorem anf_pipeline_cenv_extends next_var opts e c e' c' :
  cenv_ok c ->
  anf_pipeline next_var opts e c = (compM.Ret e', c') ->
  cenv_extends (state.cenv c) (state.cenv c').
Proof.
  intros hok hrun. have h := apres_anf_pipeline next_var opts e c.
  rewrite hrun in h. exact (proj2 (h hok)).
Qed.
