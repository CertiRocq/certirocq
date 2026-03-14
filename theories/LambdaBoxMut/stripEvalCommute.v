From Stdlib Require Import FunInd.
From Stdlib Require Import Lists.List.
From Stdlib Require Import Strings.String.
From Stdlib Require Import Strings.Ascii.
From Stdlib Require Import Arith.Compare_dec.
From Stdlib Require Import Arith.Peano_dec.
From Stdlib Require Import Setoids.Setoid.
From Stdlib Require Import micromega.Lia.

Require Import Common.Common.

From Stdlib Require Import ssreflect ssrbool.
From Equations Require Import Equations.

From MetaRocq.Utils Require Import utils.
From MetaRocq.Common Require Import BasicAst.
From MetaRocq.Template Require Import Ast.
From MetaRocq.Erasure Require Import EAst EAstUtils EGlobalEnv EExtends.
From MetaRocq.Erasure Require Import ESpineView EWcbvEvalEtaInd EWellformed EEtaExpanded.
Import utils.


Require Import LambdaBoxMut.compile.
Require Import LambdaBoxMut.term.
Require Import LambdaBoxMut.program.
Require Import LambdaBoxMut.wcbvEval.

Local Open Scope bool.
Local Open Scope list.
Set Implicit Arguments.

(** We do not support arrays (yet) *)
Definition prim_flags :=
  {| has_primint := true;
     has_primfloat := true;
     has_primstring := true ;
     has_primarray := false |}.

(** Cofixpoints are not supported, Var and Evar don't actually appear
    in terms to compile, and projections are inlined to cases earlier
    in the pipeline. We compile down lazy/force to thunks, for a purely
    functional implementation of cofixpoints. *)
Definition term_flags :=
  {|
    has_tBox := true;
    has_tRel := true;
    has_tVar := false;
    has_tEvar := false;
    has_tLambda := true;
    has_tLetIn := true;
    has_tApp := true;
    has_tConst := true;
    has_tConstruct := true;
    has_tCase := true;
    has_tProj := false;
    has_tFix := true;
    has_tCoFix := false;
    has_tPrim := prim_flags;
    has_tLazy_Force := true;
  |}.

Definition env_flags :=
  {| has_axioms := false;
    has_cstr_params := false;
    term_switches := term_flags;
    cstr_as_blocks := true |}.

Local Existing Instance env_flags.

Section OnGlobalEnv.
  Context (Σ : global_context).

  Definition compile_terms ts := list_terms (map compile ts).

  Definition compile_br (br : list name * EAst.term) :=
    (List.rev (fst br), compile (snd br)).

  Definition compile_brs ts := list_Brs (map compile_br ts).

  Definition compile_def d :=
    {| dname := dname d; dbody := compile d.(dbody); rarg := d.(rarg) |}.

  Definition compile_defs ts := list_Defs (map compile_def ts).

  Lemma tlength_hom:
    forall ts, tlength (compile_terms ts) = List.length ts.
  Proof.
    induction ts; intros; try reflexivity.
    - cbn. apply f_equal. assumption.
  Qed.

Lemma Lookup_hom :
  wf_glob Σ ->
  forall s ec, lookup_env Σ s = Some ec ->
    ∑ Σ', [× extends Σ' Σ, wf_global_decl Σ' ec & lookup s (compile_ctx Σ) = Some (compile_global_decl ec)].
Proof.
  induction Σ; cbn => //.
  intros s ec.
  case: eqb_specT.
  - intros -> ? [= <-].
    exists g. split. red. intros kn d hl. cbn. depelim s. cbn.
    case: eqb_specT. intros ->. now eapply lookup_env_Some_fresh in hl. auto. now depelim s.
    destruct a as [kn d]; cbn.
    now rewrite eqb_refl.
  - intros neq d hl.
    forward IHg. now depelim s.
    destruct (IHg _ _ hl) as [Σ' [ext hl']].
    exists Σ'. split => //.
    + intros kn d' hl''; cbn.
      case: eqb_specT.
      * intros ->. destruct a as [kn' ?]; cbn in *. eapply ext in hl''.  depelim s. now eapply lookup_env_Some_fresh in hl''.
      * intros hkn. now eapply ext in hl''.
    + destruct a as [kn d']; cbn.
      cbn in neq; case: eqb_specT => //.
Qed.

Lemma lookup_hom_None:
  forall nm,
    lookup_env Σ nm = None -> lookup nm (compile_ctx Σ) = None.
Proof.
  induction Σ; intros.
  - cbn. reflexivity.
  - destruct a. cbn in *.
    destruct (eqb_spec nm k) => //.
    now apply IHg.
Qed.

Lemma dlength_hom:
  forall ds, List.length ds = dlength (compile_defs ds).
induction ds. intuition. simpl. rewrite IHds. reflexivity.
Qed.

Lemma tcons_hom:
  forall t ts, compile_terms (cons t ts) = tcons (compile t) (compile_terms ts).
reflexivity.
Qed.

Lemma tnil_hom: compile_terms nil = tnil.
reflexivity.
Qed.


Lemma tappend_hom:
  forall ts us : list EAst.term,
    compile_terms (List.app ts us) = tappend (compile_terms ts) (compile_terms us).
Proof.
  induction ts; intros us; simpl. reflexivity.
  cbn. f_equal. apply IHts.
Qed.


End OnGlobalEnv.

Lemma compile_mkApps_nApp fn args :
  negb (EAst.isApp fn) ->
  compile (mkApps fn args) = TmkApps (compile fn) (compile_terms args).
Proof.
  intros napp; simp compile.
  destruct args eqn:hargs => //.
  simp compile.
  set (v := TermSpineView.view _).
  destruct (TermSpineView.view_mkApps v) as [hf [vn eq]] => //.
  rewrite eq /=. now simp_compile.
Qed.

From Stdlib Require Import ssrbool.

Lemma wellformed_lookup_inductive_pars Σ kn mdecl :
  wf_glob Σ ->
  lookup_minductive Σ kn = Some mdecl -> mdecl.(ind_npars) = 0.
Proof.
  induction 1; cbn => //.
  case: eqb_spec => [|].
  - intros ->. destruct d => //. intros [= <-].
    cbn in H0. move/andP: H0 => [] H0 _. cbn in H0. now eapply eqb_eq in H0.
  - intros _. eapply IHwf_glob.
Qed.

Lemma wellformed_lookup_constructor_pars {Σ kn c mdecl idecl cdecl} :
  wf_glob Σ ->
  lookup_constructor Σ kn c = Some (mdecl, idecl, cdecl) -> mdecl.(ind_npars) = 0.
Proof.
  intros wf. unfold lookup_constructor, lookup_inductive.
  destruct lookup_minductive eqn:hl => //=.
  do 2 destruct nth_error => //=.
  eapply wellformed_lookup_inductive_pars in hl => //. congruence.
Qed.

Lemma lookup_constructor_pars_args_spec {Σ ind n mdecl idecl cdecl} :
  wf_glob Σ ->
  lookup_constructor Σ ind n = Some (mdecl, idecl, cdecl) ->
  lookup_constructor_pars_args Σ ind n = Some (mdecl.(ind_npars), cdecl.(cstr_nargs)).
Proof.
  cbn -[lookup_constructor] => wfΣ. unfold lookup_constructor_pars_args.
  destruct lookup_constructor as [[[mdecl' idecl'] [pars args]]|] eqn:hl => //.
  intros [= -> -> <-]. cbn. f_equal.
Qed.

Lemma wellformed_lookup_constructor_pars_args {Σ ind n k args} :
  wf_glob Σ ->
  wellformed Σ k (EAst.tConstruct ind n args) ->
  ∑ nargs, lookup_constructor_pars_args Σ ind n = Some (0, nargs).
Proof.
  intros wfΣ wf. cbn -[lookup_constructor] in wf.
  destruct lookup_constructor as [[[mdecl idecl] cdecl]|] eqn:hl => //.
  exists cdecl.(cstr_nargs).
  pose proof (wellformed_lookup_constructor_pars wfΣ hl).
  eapply lookup_constructor_pars_args_spec in hl => //. congruence.
Qed.

Lemma constructor_isprop_pars_decl_params {Σ ind c b pars cdecl} :
  wf_glob Σ ->
  constructor_isprop_pars_decl Σ ind c = Some (b, pars, cdecl) -> pars = 0.
Proof.
  intros hwf.
  rewrite /constructor_isprop_pars_decl /lookup_constructor /lookup_inductive.
  destruct lookup_minductive as [mdecl|] eqn:hl => /= //.
  do 2 destruct nth_error => //=.
  eapply wellformed_lookup_inductive_pars in hl => //. congruence.
Qed.

Lemma compile_mkApps_wf (P : Term -> Prop) Σ k fn args :
  wf_glob Σ ->
  ~~ EAst.isApp fn ->
  wellformed Σ k (mkApps fn args) ->
  P (TmkApps (compile fn) (list_terms (map (compile ) args))) ->
  P (compile (mkApps fn args)).
Proof.
  intros wfΣ napp.
  rewrite wellformed_mkApps // => /andP[] wffn wfargs.
  rewrite compile_mkApps_nApp //.
Qed.

Lemma compile_decompose f :
  compile f =
  let (fn, args) := decompose_app f in
  TmkApps (compile fn) (compile_terms args).
Proof.
  destruct (decompose_app f) eqn:da.
  rewrite (decompose_app_inv da). apply compile_mkApps_nApp.
  now eapply decompose_app_notApp.
Qed.

(* Lemma compile_mkApps_eta (P : Term -> Prop) Σ fn args :
  wf_glob Σ ->
  ~~ EAst.isApp fn ->
  isEtaExp Σ (mkApps fn args) ->
  (P (TmkApps (compile fn) (list_terms (map compile args)))) ->
  P (compile (mkApps fn args)).
Proof.
  intros wfΣ napp.
  move/isEtaExp_mkApps.
  rewrite decompose_app_mkApps //.
  destruct construct_viewc eqn:vc.
  + rewrite /isEtaExp_app.
    destruct lookup_constructor_pars_args as [[]|] eqn:hl.
    rewrite compile_decompose decompose_app_mkApps // /= hl.
    move=> /andP[] /Nat.leb_le hargs etaargs.
    move/(_ _ _ eq_refl).
    destruct chop eqn:eqch => //.
    move => /andP[] => //.
  + intros ht. rewrite compile_mkApps // vc //.
Qed. *)

Inductive Forall2_terms (P : Term -> Term -> Prop) : Terms -> Terms -> Prop :=
  | Forall2_nil_terms : Forall2_terms P tnil tnil
  | Forall2_cons_terms t t' l l' : P t t' -> Forall2_terms P l l' -> Forall2_terms P (tcons t l) (tcons t' l').

Section Reverse_Induction.
  Lemma trev_list_ind :
    forall P:Terms -> Type,
      P tnil ->
        (forall (a:Term) (l:Terms), P (treverse l) -> P (treverse (tcons a l))) ->
        forall l, P (treverse l).
  Proof.
    induction l; auto.
  Qed.

  Theorem trev_ind :
    forall P:Terms -> Type,
      P tnil ->
      (forall x l, P l -> P (tappend l (tcons x tnil))) -> forall l, P l.
  Proof.
    intros.
    generalize (treverse_involutive l).
    intros E; rewrite <- E.
    apply (trev_list_ind P).
    auto.

    simpl.
    intros.
    apply (X0 a (treverse l0)).
    auto.
  Qed.

End Reverse_Induction.

Derive Signature for WcbvEval.
Derive NoConfusion for Term Terms.

Lemma TmkApps_tappend f args args' : TmkApps f (tappend args args') = TmkApps (TmkApps f args) args'.
Proof.
  induction args in args' |- * using trev_ind.
  - cbn => //.
  - cbn.
    rewrite IHargs /=.
    rewrite -tappend_assoc. rewrite IHargs //=.
Qed.

Lemma eval_mkAppsConstruct_inv' :
  forall p t x, WcbvEval p t x ->
  forall f args, t = TmkApps f args ->
  forall i r args', f = TConstruct i r args' ->
  args = tnil /\ exists argsv, WcbvEvals p args' argsv /\ x = TConstruct i r argsv.
Proof.
  intros p t x ev f args.
  induction args in f, t, x, ev |- *using trev_ind. cbn.
  - intros -> i r args' ->.
    split => //.
    depind ev; try discriminate. exists args'. split => //.
  - cbn.
    intros ht i r args' ->.
    rewrite ht in ev. rewrite !TmkApps_tappend /= in ev.
    cbn in ev. depelim ev.
    specialize (IHargs _ _ ev1 _ eq_refl _ _ _ eq_refl) as [? [? []]]. discriminate.
    specialize (IHargs _ _ ev1 _ eq_refl _ _ _ eq_refl) as [? [? []]]. discriminate.
    specialize (IHargs _ _ ev1 _ eq_refl _ _ _ eq_refl) as [? [? []]]. discriminate.
    specialize (IHargs _ _ ev1 _ eq_refl _ _ _ eq_refl) as [? [? []]]. subst fn'.
    destruct H as [? [? []]]. elim H3. now eauto.
Qed.

Lemma eval_TmkApps_Construct_inv :
  forall p i r args' args x, WcbvEval p (TmkApps (TConstruct i r args') args) x ->
  args = tnil /\ exists argsv, WcbvEvals p args' argsv /\ x = TConstruct i r argsv.
Proof.
  intros. eapply eval_mkAppsConstruct_inv'; trea.
Qed.

Lemma TApp_TmkApps f l t : TApp (TmkApps f l) t = TmkApps f (tappend l (tunit t)).
Proof.
  rewrite TmkApps_tappend //.
Qed.

Lemma eval_to_mkApps_Construct_inv_gen :
  forall p t x, WcbvEval p t x ->
  forall f args, x = TmkApps f args ->
  args <> tnil -> ~ isConstruct f.
Proof.
  intros p t x ev f args -> hargs.
  destruct args using trev_ind. congruence. cbn in ev.
  rewrite -TApp_TmkApps in ev. clear IHargs. clear hargs.
  depind ev; auto.
  destruct H as [? [? []]].
  destruct args using trev_ind. cbn in *. apply H1.
  clear IHargs.
  intros [ind [n [args' eq]]].
  subst f. eapply IHev1. rewrite TApp_TmkApps. reflexivity.
  now do 3 eexists.
Qed.

Definition eq_nil_dec l : l = tnil \/ l <> tnil.
Proof.
  destruct l; auto. right; congruence.
Qed.

Lemma eval_to_mkApps_Construct_inv p t ind c args args' :
  WcbvEval p t (TmkApps (TConstruct ind c args) args') -> args' = tnil.
Proof.
  move/eval_to_mkApps_Construct_inv_gen.
  intros Hf.
  specialize (Hf (TConstruct ind c args) _ eq_refl).
  destruct (eq_nil_dec args') => //.
  specialize (Hf H). elim Hf. now do 3 eexists.
Qed.


(* Lemma tappend_compile_terms : tappend (compile_terms Σ l) (compile_terms Σ l') = compile_terms (l ++ l'). *)

Lemma compile_tApp Σ t a (P : Term -> Prop) k :
  wf_glob Σ ->
  wellformed Σ k (tApp t a) ->
  (let (fn, args) := decompose_app (tApp t a) in

      P (TApp (compile t) (compile a))
  ) ->
  P (compile (tApp t a)).
Proof.
  intros wfΣ wf.
  rewrite (compile_decompose (tApp t a)).
  destruct decompose_app eqn:da.
  pose proof (decompose_app_notApp _ _ _ da).
  pose proof (EInduction.decompose_app_app _ _ _ _ da).
  + pose proof (decompose_app_notApp _ _ _ da).
    pose proof (EInduction.decompose_app_app _ _ _ _ da).
    eapply EEtaExpandedFix.decompose_app_tApp_split in da as [Ha Ht].
    rewrite Ha Ht.
    rewrite compile_mkApps_nApp //.
    rewrite TApp_TmkApps.
    cbn. rewrite -(tappend_hom (remove_last l) [last l a]).
    rewrite -remove_last_last //.
Qed.

Derive Signature for crctTerms.

Lemma crctTerm_tmkApps Σ n f args :
  crctTerm Σ n f ->
  crctTerms Σ n args ->
  crctTerm Σ n (TmkApps f args).
Proof.
  induction args in f |- *. cbn; auto.
  intros hf hargs. depelim hargs.
  cbn. eapply IHargs => //. constructor => //.
Qed.

From MetaRocq.SafeChecker Require PCUICTypeChecker.

Ltac simp_eta_in := match goal with [ H : is_true (isEtaExp _ _) |- _ ] => simp_eta in H end.

Lemma compile_isLambda t : EAst.isLambda t -> isLambda (compile t).
Proof. destruct t => //. now simp_compile. Qed.

Definition preserves_some_gen {A B} (t : option A) (f : A -> B) (t' : option B) := forall b, t = Some b -> t' = Some (f b).

Definition preserves_some {A} (t t' : option A) : Prop := preserves_some_gen t id t'.

Lemma preserves_some_refl {A} (t : option A) : preserves_some t t.
Proof.
  now intros b.
Qed.

Lemma lookup_constructor_pars_args_extends {Σ Σ' ind c} :
  wf_glob Σ' ->
  extends Σ Σ' ->
  EWellformed.isSome (lookup_constructor Σ ind c) ->
  lookup_constructor_pars_args Σ' ind c = lookup_constructor_pars_args Σ ind c.
Proof.
  intros wfΣ ext.
  rewrite /lookup_constructor_pars_args.
  destruct lookup_constructor eqn:hl => /= //.
  now rewrite (extends_lookup_constructor wfΣ ext _ _ _ hl).
Qed.

Lemma decompose_app_napp {t} : ~~ EAst.isApp t -> decompose_app t = (t, []).
Proof.
  intros napp. destruct t => //.
Qed.

Import ELiftSubst.

Lemma wf_mkApps Σ k f args : reflect (wellformed Σ k f /\ forallb (wellformed Σ k) args) (wellformed Σ k (mkApps f args)).
Proof.
  rewrite wellformed_mkApps //. eapply andP.
Qed.

Lemma lookup_env_lookup {Σ c decl} :
  wf_glob Σ ->
  lookup_env Σ c = Some decl ->
  lookup c (compile_ctx Σ) = Some (compile_global_decl decl).
Proof.
  move=> wfΣ /(Lookup_hom wfΣ) [Σ' [ext wf ->]]. f_equal.
Qed.

Lemma exnNth_nth_error {A} (l : list A) n t :
  nth_error l n = Some t ->
  exnNth l n = Ret t.
Proof.
  induction l in n |- *; destruct n; cbn => //; auto.
  intros [= <-]. reflexivity.
Qed.

Lemma compile_crctInd {Σ ind mdecl idecl} :
  wf_glob Σ ->
  lookup_inductive Σ ind = Some (mdecl, idecl) ->
  crctInd (compile_ctx Σ) ind (ibody_ityp idecl).
Proof.
  move=> wfΣ.
  unfold lookup_inductive, lookup_minductive.
  destruct lookup_env eqn:hl => /= //=.
  eapply lookup_env_lookup in hl => //.
  destruct g => //=.
  destruct nth_error eqn:hnth => //.
  intros [= <- <-]. econstructor. red.
  split. eapply lookup_Lookup. cbn. rewrite hl //.
  { eapply nth_error_Some_length in hnth.
    unfold ibodies_itypPack. destruct (ind_bodies m) => //. cbn in hnth; lia. }
  cbn. unfold ibodies_itypPack, getInd.
  eapply exnNth_nth_error. rewrite nth_error_map hnth //.
Qed.

Lemma compile_crctCnstr Σ ind n args mdecl idecl cdecl :
  wf_glob Σ ->
  lookup_constructor Σ ind n = Some (mdecl, idecl, cdecl) ->
  tlength args = cstr_arity mdecl cdecl ->
  crctCnstr (compile_ctx Σ) ind n args.
Proof.
  intros wfΣ.
  rewrite /lookup_constructor.
  destruct lookup_inductive as [[mdecl' idecl']|] eqn:hl => /= //.
  destruct nth_error eqn:hnth => //. intros [= <- <- <-].
  intros hlen.
  econstructor. eapply compile_crctInd; tea.
  rewrite /getCnstr. cbn.
  eapply exnNth_nth_error. rewrite nth_error_map hnth //.
  cbn. rewrite hlen. destruct c as [cname arity]; cbn.
  rewrite /cstr_arity. cbn.
  move: hl. rewrite /lookup_inductive. destruct lookup_minductive eqn:hl' => /= //.
  destruct (nth_error (ind_bodies m) _) => //. intros [= <- <-].
  now rewrite (wellformed_lookup_inductive_pars _ wfΣ hl').
Qed.


Lemma compile_lift n t : compile.lift n (compile t) = compile (lift 1 n t).
Proof.
  funelim (compile t); cbn [lift compile.lift]; simp compile => //.
  - destruct (Nat.compare_spec n n0);
    destruct (Nat.leb_spec n0 n); subst; try lia; simp compile; auto.
  -
  Admitted.


Lemma wellformed_crct {Σ} t :
  wf_glob Σ ->
  crctEnv (compile_ctx Σ) ->
  forall k, wellformed Σ k t ->
  crctTerm (compile_ctx Σ) k (compile t).
Proof.
  intros wfΣ crctΣ.
  revert t. apply: EInduction.MkAppsInd.rec; cbn [wellformed]; intros; try simp_compile.
  all:intros; simp_compile; intuition auto; try cbn -[lookup_env lookup_constant lookup_constructor lookup_constructor_pars_args lookup_inductive] in *; rtoProp; try constructor; eauto.
  - now eapply Nat.ltb_lt.
  - simp_compile.
    move: H2; rewrite wellformed_mkApps // => /andP[] wfc wfu.
    eapply compile_mkApps_wf => //; tea. rewrite wellformed_mkApps //. now erewrite wfc, wfu.
    eapply crctTerm_tmkApps; eauto.
    solve_all. clear -wfu crctΣ. induction wfu; constructor; intuition eauto.
  - destruct lookup_constant as [[]|] eqn:hl => //.
    destruct cst_body => //.
    econstructor; eauto. unfold LookupDfn. eapply lookup_Lookup.
    eapply (lookup_env_lookup (decl := ConstantDecl {| Extract.E.cst_body := Some t |})) => //.
    move: hl; rewrite /lookup_constant. destruct lookup_env => //=.
    destruct g => //. congruence.
  - move: H0. rewrite /isEtaExp_app.
    destruct lookup_constructor as [[[mdecl idecl] cdecl]|] eqn:hl => //.
    move: H1.
    rewrite (lookup_constructor_pars_args_spec wfΣ hl).
    have hpars := wellformed_lookup_constructor_pars wfΣ hl => /= hargs lenargs.
    eapply compile_crctCnstr; eauto. cbn. rewrite /cstr_arity.
    rewrite tlength_hom. apply eqb_eq in lenargs. lia.
  - destruct args => //. now constructor.
    solve_all. clear -crctΣ H1; induction H1; cbn; constructor; auto. repeat apply p.
  - rewrite /wf_brs in H0. destruct lookup_inductive as [[mdecl idecl]|] eqn:hl => //.
    econstructor.
    eapply compile_crctInd; tea. eauto.
    repeat toAll. clear -wfΣ crctΣ H1.
    induction H1; cbn; constructor; auto.
    rewrite List.length_rev. now apply p.
  - cbn. rewrite -dlength_hom.
    move/andP: H0 => [] hn H1. clear hn.
    rewrite Nat.add_comm. eapply forallb_All in H1. eapply forallb_All in H.
    eapply All_mix in X; [|exact H]. clear H; eapply All_mix in X; [|exact H1]. clear H1.
    move: X. generalize (#|m| + k).
    induction 1; try solve [constructor; cbn; auto].
    intuition auto.
    constructor; eauto.
    now eapply compile_isLambda.
  - cbn. rewrite -dlength_hom. move/andP: H0 => [] /Nat.ltb_lt //.
  - destruct p as [? []]; try constructor; eauto.
    + simp trans_prim_val. cbn. now cbn in H.
  - specialize (H k H0). now eapply Crct_lift in H.
Qed.

Lemma compile_fresh kn Σ : fresh_global kn Σ -> fresh kn (compile_ctx Σ).
Proof.
  induction 1; cbn. constructor.
  destruct x as [kn' d]. constructor => //. cbn in H. congruence.
Qed.

Lemma wellformed_env_crctEnv {Σ} :
  wf_glob Σ ->
  crctEnv (compile_ctx Σ).
Proof.
  induction Σ; cbn.
  - constructor.
  - intros wf. depelim wf.
    destruct d.
    * cbn. destruct c as [[b|]]; econstructor; eauto.
      now apply compile_fresh.
      eapply wellformed_crct => //. eauto.
      now apply compile_fresh.
    * constructor; eauto.
      now apply compile_fresh.
Qed.

Lemma isLambda_substl s t : EAst.isLambda t -> EAst.isLambda (ECSubst.substl s t).
Proof. induction s in t |- * => //.
  intros isl. cbn.
  eapply IHs. destruct t => //.
Qed.

Local Lemma decompose_app_app t u f l : decompose_app (tApp t u) = (f, l) -> l <> [].
Proof.
  intros da.
  pose proof (decompose_app_inv da).
  intros ->. cbn in H. subst f.
  now move: (decompose_app_notApp _ _ _ da).
Defined.

Lemma list_terms_app l l' : list_terms (l ++ l') = tappend (list_terms l) (list_terms l').
Proof.
  induction l in l' |- *.
  - cbn; auto.
  - cbn. now f_equal.
Qed.

Lemma compile_terms_tappend l l' :
  compile_terms (l ++ l') = tappend (compile_terms l) (compile_terms l').
Proof.
  rewrite /compile_terms map_app list_terms_app //.
Qed.

Lemma isLambda_compile f :
  ~~ EAst.isLambda f -> ~~ isLazy f -> ~ isLambda (compile f).
Proof.
  intros nf nl. move=> [] na [] bod.
  destruct f; simp_compile => /= //.
  rewrite compile_decompose.
  destruct decompose_app eqn:da.
  cbn.
  eapply decompose_app_app in da. destruct l using rev_ind => //.
  rewrite compile_terms_tappend // -TApp_TmkApps //.
  destruct prim as [? []]; simp trans_prim_val; cbn => //.
Qed.

Lemma isBox_compile f :
  ~~ EAstUtils.isBox f -> compile f <> TProof.
Proof.
  intros nf.
  destruct f; simp_compile => /= //.
  rewrite compile_decompose.
  destruct decompose_app eqn:da.
  eapply decompose_app_app in da. destruct l using rev_ind => //.
  rewrite compile_terms_tappend // -TApp_TmkApps //.
  destruct prim as [? []]; simp trans_prim_val; cbn => //.
Qed.

Lemma isFix_compile f :
  ~~ EAstUtils.isFix f -> ~ isFix (compile f).
Proof.
  move=> nf [] defs [n].
  destruct f; simp_compile => /= //.
  rewrite compile_decompose.
  destruct decompose_app eqn:da.
  eapply decompose_app_app in da. destruct l using rev_ind => //.
  rewrite compile_terms_tappend // -TApp_TmkApps //.
  destruct prim as [? []]; simp trans_prim_val; cbn => //.
Qed.

Lemma isConstructApp_compile f :
  ~~ isConstructApp f -> ~ isConstruct (compile f).
Proof.
  move=> nf [] i [] n [] args.
  destruct f; simp_compile => /= //.
  rewrite compile_decompose.
  destruct decompose_app eqn:da.
  eapply decompose_app_app in da. destruct l using rev_ind => //.
  rewrite compile_terms_tappend // -TApp_TmkApps //.
  destruct prim as [? []]; simp trans_prim_val; cbn => //.
Qed.


Lemma isPrimApp_compile f :
  ~~ isPrimApp f -> ~ isPrim (compile f).
Proof.
  move=> nf [] p.
  destruct f; simp_compile => /= //.
  rewrite compile_decompose.
  destruct decompose_app eqn:da.
  eapply decompose_app_app in da. destruct l using rev_ind => //.
  rewrite compile_terms_tappend // -TApp_TmkApps //.
Qed.

Import EWcbvEval.

Lemma isEtaExp_tApp_nConstruct {Σ f a} :
  isEtaExp Σ (tApp f a) -> ~~ isConstructApp (tApp f a) -> isEtaExp Σ f && isEtaExp Σ a.
Proof.
  intros eta nc.
  move/isEtaExp_tApp: eta.
  destruct decompose_app eqn:da.
  destruct construct_viewc.
  rewrite (decompose_app_inv da) in nc.
  case/negP: nc. rewrite /isConstructApp head_mkApps //.
  now move/and4P => [] _ _ -> ->.
Qed.

Lemma isConstructApp_tApp {f a} : isConstructApp (tApp f a) = isConstructApp f.
Proof.
  rewrite /isConstructApp. cbn.
  now rewrite head_tApp.
Qed.

Lemma instantiate_TmkApps a k f l :
  instantiate a k (TmkApps f l) =
  TmkApps (instantiate a k f) (instantiates a k l).
Proof.
  induction l using trev_ind; auto.
  rewrite TmkApps_tappend.
  cbn -[instantiate instantiates].
  rewrite instantiate_TApp_commute IHl //.
  cbn -[instantiate].
  rewrite instantiates_tappend /= TmkApps_tappend //.
Qed.

From MetaRocq.Erasure Require Import EInduction ECSubst.

Lemma compile_mkApps f args :
  compile (mkApps f args) = TmkApps (compile f) (list_terms (map compile args)).
Proof.
  destruct (decompose_app f) eqn:df.
  rewrite (decompose_app_inv df) in |- *.
  rewrite -mkApps_app.
  pose proof (decompose_app_notApp _ _ _ df).
  rewrite compile_decompose.
  rewrite decompose_app_mkApps /= //.
  rewrite (compile_decompose (mkApps t l)).
  rewrite decompose_app_mkApps //.
  rewrite -TmkApps_tappend. f_equal.
  now rewrite tappend_hom.
Qed.

Lemma negbF b : ~~ b -> b -> False.
Proof. destruct b => //. Qed.

Lemma compile_mkApps_nConstructApp_nApp f args :
  ~~ EAst.isApp f ->
  ~~ isConstructApp (mkApps f args) ->
  compile (mkApps f args) = TmkApps (compile f) (list_terms (map compile args)).
Proof.
  intros napp nc.
  rewrite compile_decompose decompose_app_mkApps //.
Qed.

Lemma compile_mkApps_nConstructApp f args :
  ~~ isConstructApp (mkApps f args) ->
  compile (mkApps f args) = TmkApps (compile f) (list_terms (map compile args)).
Proof.
  intros nc.
  destruct (decompose_app f) eqn:da.
  rewrite (decompose_app_inv da) -mkApps_app in nc *.
  pose proof (decompose_app_notApp _ _ _ da).
  rewrite compile_mkApps_nConstructApp_nApp //.
  rewrite (compile_mkApps_nConstructApp_nApp t) //.
  move: nc; rewrite !isConstructApp_mkApps //.
  rewrite -TmkApps_tappend. f_equal. now rewrite -tappend_hom.
Qed.

Lemma isConstruct_csubst a k t :
  ~~ EAst.isApp t ->
  ~~ EAstUtils.isConstruct t ->
  EAstUtils.isConstruct (EAstUtils.head (csubst a k t)) ->
  t = tRel k.
Proof.
  induction t => /= //.
  destruct (Nat.compare_spec k n) => //.
  intros; f_equal; auto.
Qed.

Arguments instantiate _ _ !tbod.

Lemma compile_csubst Σ a n k b :
  wf_glob Σ ->
  wellformed Σ 0 a ->
  wellformed Σ (n + k) b ->
  compile (ECSubst.csubst a k b) = instantiate (compile a) k (compile b).
Proof.
  intros wfΣ wfa.
  revert b n k.
  apply: MkAppsInd.rec. all:intros *.
  all:cbn -[instantiateBrs instantiateDefs lookup_inductive lookup_constructor]; try intros until k; simp_eta;
     intros; simp_compile; try solve [cbn -[instantiateBrs instantiateDefs lookup_inductive lookup_constructor];
     try f_equal; rtoProp;
     intuition eauto; eauto].

  - cbn. destruct Nat.compare => //; reflexivity.
  - cbn. f_equal; eauto. eapply H => //. rewrite -Nat.add_succ_r in H0; tea.
  - cbn. f_equal; eauto. eapply H => //. rtoProp; intuition eauto. move/andP: H1 => [] wf wf'.
    eapply H0 => //; rtoProp; intuition eauto. rewrite -Nat.add_succ_r in wf'; tea.
  - move/wf_mkApps: H2 => [] wft wfu. rewrite csubst_mkApps.
    rewrite !compile_mkApps.
    rewrite instantiate_TmkApps.
    rewrite (H1 _ _ wft). f_equal.
    { clear -X wfu. repeat toAll. induction wfu.
        - constructor.
        - cbn -[instantiates]. rewrite instantiates_tcons.
          f_equal; eauto. now eapply p. }
  - rewrite instantiate_TConstruct. f_equal.
    move/and3P: H => [] _ _ wfa'. solve_all.
    induction wfa'; auto.
    cbn -[instantiates].
    rewrite instantiates_tcons. f_equal. repeat eapply p.
    eapply IHwfa'.
  - rewrite map_map_compose.
    move/andP: H0 => [] /andP[] wfi wft wfl.
    set (brs' := map _ l). cbn in brs'.
    set (brs'0 := map _ l). simpl.
(*    rewrite instantiate_TCase. *) rtoProp; intuition auto. f_equal; eauto.
    clear -X wfl.
    { subst brs' brs'0. repeat toAll. induction wfl.
    - constructor.
    - cbn -[instantiateBrs]. rewrite instantiateBrs_equation.
      f_equal; eauto. destruct p. rewrite List.length_rev. repeat eapply (e n).
      eapply wellformed_up; tea. lia. }
  - rewrite map_map_compose. set (mfix' := map _ m).
    simpl. (*rewrite instantiate_TFix. *) f_equal.
    clear -X H.
    move/andP: H => [] _ /andP[] _ H1. repeat toAll.
    rewrite -dlength_hom.
    subst mfix'. rewrite Nat.add_comm.
    revert H1. generalize #|m|.
    induction 1.
    * constructor.
    * cbn -[instantiateDefs]. rewrite instantiateDefs_equation.
      destruct p; len.
      f_equal; eauto. apply (e n0) => //. eapply wellformed_up; tea. lia.
  - destruct p as [? []]; simp trans_prim_val; cbn => //.
  - cbn. f_equal. rewrite (H n); auto.
    pose proof (instantiate_lift (compile a)) as [il _].
    specialize (il (compile t) k 0).
    apply il. lia. eapply Crct_WFTrm.
    eapply wellformed_crct; tea. now eapply wellformed_env_crctEnv.
Qed.

Fixpoint substl_rev terms k body :=
  match terms with
  | [] => body
  | term :: terms => substl_rev terms k (csubst term (#|terms| + k) body)
  end.

From MetaRocq.Erasure Require Import ELiftSubst.

Lemma csubst_substl_comm a n terms k body :
  closed a ->
  forallb (closedn 0) terms ->
  csubst a (n + k) (substl_rev terms k body) =
  substl_rev terms k (csubst a (n + #|terms| + k) body).
Proof.
  induction terms in k, body |- *.
  - cbn. intros. now rewrite Nat.add_0_r.
  - cbn. move=> cla /andP[] cla0 clts.
    rewrite IHterms //. f_equal.
    rewrite !closed_subst //.
    rewrite -Nat.add_assoc (Nat.add_comm n).
    rewrite distr_subst_rec. cbn. lia_f_equal.
    rewrite subst_closed //. eapply closed_upwards; tea. lia.
Qed.

Lemma substl_rev_app {terms terms' k body} :
  forallb (closedn 0) terms ->
  forallb (closedn 0) terms' ->
  substl_rev (terms ++ terms') k body =
  substl_rev terms k (substl_rev terms' k body).
Proof.
  induction terms in body |- *; cbn => //.
  move=> /andP[] cla clt clt'.
  rewrite IHterms //. f_equal.
  rewrite csubst_substl_comm //. f_equal. now len.
Qed.

Lemma substl_substl_rev terms k body :
  forallb (closedn 0) terms ->
  fold_left (fun bod term : term => csubst term k bod) (List.rev terms) body = substl_rev terms k body.
Proof.
  revert k body.
  induction terms using rev_ind; intros k body.
  - cbn. reflexivity.
  - rewrite forallb_app => /andP[] clterms /=; rewrite andb_true_r => clx.
    cbn. rewrite List.rev_app_distr /=. rewrite IHterms //.
    rewrite substl_rev_app //. now rewrite /= clx.
Qed.

Definition t_fix_subst (ds : Defs) :=
  let fix aux (n : nat) : Terms :=
	  match n with
    | 0 => tnil
    | S n0 => tcons (TFix ds n0) (aux n0)
    end in
  aux (dlength ds).

Lemma compile_fix_subst mfix :
  compile_terms (fix_subst mfix) = t_fix_subst (list_Defs (map (compile_def) mfix)).
Proof.
  unfold fix_subst, t_fix_subst.
  rewrite -dlength_hom.
  induction #|mfix|; cbn; auto.
  f_equal. simp_compile. cbn. reflexivity.
  now rewrite -IHn.
Qed.

Fixpoint tfold_left {A} (f : A -> Term -> A) l acc :=
  match l with
  | tnil => acc
  | tcons b t => tfold_left f t (f acc b)
  end.

Lemma instantiate_fold mfix bod :
  fold_left
    (fun (bod : Term) (ndx : nat) =>
      instantiate (TFix mfix ndx) 0 bod)
    (list_to_zero (dlength mfix)) bod =
  tfold_left (fun bod term => instantiate term 0 bod) (t_fix_subst mfix) bod.
Proof.
  unfold t_fix_subst.
  induction (dlength mfix) in bod |- *; cbn; auto.
Qed.

Lemma wellformed_csubst Σ t n k u :
  wellformed Σ 0 t ->
  wellformed Σ (S (n + k)) u ->
  wellformed Σ (n + k) (ECSubst.csubst t k u).
Proof.
  intros.
  rewrite ECSubst.closed_subst //.
  now eapply wellformed_closed.
  rewrite -{1}(Nat.add_0_l k). cbn. eapply wellformed_subst_eq => /= //.
  rewrite andb_true_r //. eapply wellformed_up; tea. lia. now rewrite Nat.add_comm.
Qed.

Lemma substl_fold_left Σ terms k body :
  wf_glob Σ ->
  wellformed Σ (#|terms| + k) body ->
  forallb (wellformed Σ 0) terms ->
  compile (fold_left (fun bod term : term => csubst term k bod) terms body) =
  tfold_left (fun bod term => instantiate term k bod) (list_terms (map compile terms)) (compile body).
Proof.
  intros wfΣ.
  revert k body.
  induction terms; intros k body.
  - cbn. reflexivity.
  - rewrite /= => wfb /andP[] clx clterms.
    cbn. rewrite IHterms //.
    eapply wellformed_csubst => //.
    rewrite (compile_csubst (Σ := Σ) _ (S #|terms|)) //.
Qed.

Lemma compile_substl Σ a b :
  wf_glob Σ ->
  forallb (wellformed Σ 0) a ->
  wellformed Σ #|a| b ->
  compile (substl (List.rev a) b) = instantiatel (list_terms (map compile a)) 0 (compile b).
Proof.
  intros wf cla.
  repeat toAll.
  unfold substl. rewrite substl_substl_rev. solve_all.
  now eapply wellformed_closed.
  induction cla in b |- *; cbn => //.
  rewrite !Nat.add_0_r. cbn. intros wfb. rewrite IHcla.
  eapply (wellformed_csubst _ _ 0) => //.
  f_equal.
  rewrite tlength_hom. eapply (compile_csubst _ 1); tea.
Qed.

Lemma compile_substl_nrev Σ a b :
  wf_glob Σ ->
  forallb (wellformed Σ 0) a ->
  wellformed Σ #|a| b ->
  compile (substl a b) = instantiatel (list_terms (map compile (List.rev a))) 0 (compile b).
Proof.
  intros wf wfa wfb.
  rewrite -(List.rev_involutive a) (compile_substl _ _ wf) // ?forallb_rev //. now len.
  f_equal. now rewrite List.rev_involutive.
Qed.

Lemma nth_error_bnth {brs : list (list name × term)} {n br f} :
  nth_error brs n = Some br ->
  bnth n (list_Brs (map f brs)) = Some (f br).
Proof.
  induction brs in n, br |- *; destruct n; cbn; auto => //.
  intros [= <-]. destruct (f a). now cbn.
  intros h. specialize (IHbrs _ _ h).
  now destruct (f a); cbn.
Qed.

Lemma nth_error_dnth {mfix : list (def term)} {n fn f} :
  nth_error mfix n = Some fn ->
  dnth n (list_Defs (map f mfix)) = Some (f fn).
Proof.
  induction mfix in n |- *; destruct n; cbn; auto => //.
  intros [= <-]. now destruct (f a).
Qed.

Lemma compile_whFixStep Σ mfix idx rarg fn :
  wf_glob Σ ->
  wellformed Σ 0 (tFix mfix idx) ->
  cunfold_fix mfix idx = Some (rarg, fn) ->
  whFixStep (list_Defs (map compile_def mfix)) idx = Some (compile fn).
Proof.
  unfold cunfold_fix, whFixStep. simp_eta.
  intros wfΣ cla.
  destruct nth_error eqn:hnth => //.
  intros [= <- <-].
  rewrite (nth_error_dnth hnth).
  destruct d as [dbody] => /=. f_equal.
  rewrite instantiate_fold.
  cbn in cla. move/andP: cla => [isl /andP[hn cla]].
  rewrite (substl_fold_left _ _ _ wfΣ) //.
  { eapply nth_error_forallb in cla => //; tea. cbn in cla. len. rewrite fix_subst_length.
    now rewrite Nat.add_0_r in cla. }
  { eapply wellformed_fix_subst => //. }
  f_equal. now rewrite -compile_fix_subst.
Qed.

Lemma nisLazyApp_isLazy t : ~~ isLazyApp t -> ~~ isLazy t.
Proof.
  unfold isLazyApp.
  have da := decompose_app_head_spine t.
  rewrite -{2}(mkApps_head_spine t).
  destruct (spine t) using rev_case => //.
  rewrite mkApps_app //=.
Qed.

From MetaRocq.Erasure Require Import EConstructorsAsBlocks EWcbvEvalCstrsAsBlocksInd.

Lemma WcbvEval_hom (fl := block_wcbv_flags) :
  forall Σ, wf_glob Σ ->
  forall t t',
    wellformed Σ 0 t ->
    EWcbvEval.eval Σ t t' ->
    WcbvEval (compile_ctx Σ) (compile t) (compile t').
Proof.
  intros Σ wfΣ.
  eapply (eval_preserve_mkApps_ind fl eq_refl Σ (fun t t' : term =>
    WcbvEval (compile_ctx Σ) (compile t) (compile t'))
    (wellformed Σ) (Qpres := Qpreserves_wellformed _ _ wfΣ)) => //; eauto.
  all:intros *.
  - intros; eapply eval_wellformed; tea => //.
  - intros ev [IHev wfa wfb] ev' [ih' wft wft'].
    eapply compile_tApp with (k := 0) => //; eauto.
    cbn. now rewrite wfa wft.
    destruct decompose_app eqn:da.
    simp_compile in IHev.
    eapply wAppProof; eauto.
  - intros ev [IHev wff wflam] ev' [IHev' wfa wfa'] ev'' [IHev'' wfsubs wfres].
    simp_compile in IHev.
    eapply compile_tApp with (k := 0) => //; tea.
    cbn. now rewrite wff wfa.
    destruct decompose_app eqn:da.
    econstructor; eauto.
    unfold whBetaStep.
    rewrite -(compile_csubst (Σ := Σ) _ 1) //.
  - intros ev [IHev wfa wfb] wfb1.
    intros ev' [IHev' wft wft'].
    simp_compile. econstructor; tea.
    rewrite -(compile_csubst (Σ := Σ) _ 1) //.
  - intros ev [IHev wfa wfb].
    intros isp hnth hskip hbr wfbr.
    intros ev' [IHev' wft wft'].
    simp_compile. simp_compile in IHev.
    destruct (wellformed_lookup_constructor_pars_args wfΣ eq_refl wfb) as [nargs eq].
    move: wfb => /= /andP[] wfc wfargs.
    rewrite eq in wfargs.
    move/andP: wfargs => [] eqb hargs. apply ReflectEq.eqb_eq in eqb. cbn in eqb; subst nargs.
    set (brs' := map _ brs). cbn.
    assert (pars = 0).
    { now eapply constructor_isprop_pars_decl_params in isp. }
    subst pars. rewrite skipn_0 in hbr.
    econstructor; tea.
    unfold whCaseStep.
    rewrite (nth_error_bnth hnth) List.length_rev tlength_hom.
    case: Nat.eqb_spec => //; try congruence.
    intros _. rewrite /iota_red skipn_0.
    f_equal. rewrite (compile_substl (Σ := Σ)) //. solve_all.
    rewrite hbr //.
  - (* Fix case *) intros _.
    rename f5 into f.
    intros ev [IHev wff wffix].
    intros unffix eva [IHeva wfa wfav].
    move=> evapp [IHevapp wftapp wfres].
    eapply compile_tApp with (k := 0) => //. tea.
    { cbn; now rewrite wff wfa. }
    destruct decompose_app eqn:da.
    simp_compile in IHev.
    set (mfix' := map _ mfix) in *.
    eapply (wAppFix (x := compile fn)); tea.
    { rewrite /mfix'. eapply compile_whFixStep; tea => //. }
    move: IHevapp.
    change (tApp fn av) with (mkApps fn [av]).
    assert (isl : EAst.isLambda fn).
    { move: wffix => /= /andP[] hfix _.
      unfold cunfold_fix in unffix. destruct nth_error eqn:hnth => //.
      noconf unffix. eapply nth_error_forallb in hfix; tea. cbn in hfix.
      eapply (isLambda_substl (fix_subst mfix)) in hfix.
      destruct ECSubst.substl => //. }
    destruct fn => //.
    eapply compile_mkApps_wf; tea.
    cbn. auto.
  - (* No cofixpoints allowed *)
    intros cunfcof.
    move=> ev [IHev wfd wfcof].
    move: wfcof. rewrite wellformed_mkApps //.
  - (* Declarations *)
    intros hdecl res hbod hev.
    move => [] IHev wfbo wfr.
    simp_compile. econstructor; tea.
    eapply lookup_env_lookup in hdecl; tea.
    rewrite /lookupDfn hdecl /compile_global_decl.
    destruct decl as [[body'|]] => //. unfold exceptionMonad.ret. f_equal.
    now noconf hbod.
  - (* Congruence *)
    intros [hif' wff wff'].
    intros IHapp. intros nlam.
    intros eva [iheva wfa wfa'].
    eapply compile_tApp; tea. cbn. now erewrite wff, wfa.
    destruct decompose_app eqn:da.
    apply (compile_tApp (Σ := Σ) _ _ _ 0) => //. cbn. now rewrite wff' wfa'.
    destruct (decompose_app (tApp f' a')) eqn:da'.
    constructor; eauto.
    rewrite !negb_or in nlam. rtoProp; intuition auto.
    eapply (isLambda_compile) in H. contradiction. now eapply nisLazyApp_isLazy in H0.
    eapply (isFix_compile) in H4; auto.
    eapply (isConstructApp_compile) in H5; auto.
    eapply (isBox_compile) in H3. contradiction.
    now eapply isPrimApp_compile in H5.
  - intros hl hargs evargs IHargs.
    simp_compile. econstructor. clear hargs.
    move: IHargs. cbn. induction 1; cbn; constructor; intuition auto.
    apply r. apply IHIHargs. now depelim evargs.
  - cbn. move/andP=> [hasp testp] ih. depelim ih; simp_compile; simp trans_prim_val; cbn => //; try constructor.
  - intros evt evt' [IHt wft wfl] [IHt' wft' wfv].
    simp_compile. simp_compile in IHt. cbn.
    eapply wAppLam; tea. eapply wProof.
    unfold whBetaStep.
    rewrite (proj1 (instantiate_noLift TProof) (compile t') 0). exact IHt'.
  - intros isat wf.
    destruct t => //; simp_compile; econstructor.
    cbn in isat. destruct args => //.
Qed.

Lemma compile_sound (wfl := block_wcbv_flags) {Σ t t'} :
  wf_glob Σ ->
  wellformed Σ 0 t ->
  EWcbvEval.eval Σ t t' ->
  forall v, WcbvEval (compile_ctx Σ) (compile t) v -> v = compile t'.
Proof.
  intros wfΣ wft ev v ev'.
  apply (WcbvEval_single_valued ev').
  eapply WcbvEval_hom; eauto.
Qed.
(* Print Assumptions compile_sound. *)

Definition program := environ Term * Term.

From MetaRocq.Erasure Require Import EProgram.

Definition compile_program (e : eprogram) : program :=
  (compile_ctx e.1, compile e.2).

Definition wf_program (p : program) :=
  crctEnv p.1 /\ crctTerm p.1 0 p.2.

Lemma wf_compile (p : eprogram) :
  wf_eprogram env_flags p ->
  wf_program (compile_program p).
Proof.
  destruct p as [env main].
  move=> [wfe wfmain]. cbn in *.
  split; cbn.
  - eapply wellformed_env_crctEnv, wfe.
  - eapply wellformed_crct => //.
    eapply wellformed_env_crctEnv, wfe.
Qed.
