(** Properties of the constructor tag map and constructor env provided by convert_env *)

From Stdlib Require Import ssreflect ssrbool.
From Equations Require Import Equations.

Require Import LambdaBox_to_LambdaANF.fuel_sem.
Require Import LambdaBox_to_LambdaANF.common.
Require Import LambdaANF.term.
Require Import compcert.lib.Maps.
From Stdlib Require Import ZArith.
From CertiRocq Require Import Common.Common Common.compM Common.Pipeline_utils.
From Stdlib Require Import List.
Require Import maps_util.

Require Import ExtLib.Structures.Monad.
Require Import MetaRocq.Common.BasicAst.
From MetaRocq.Erasure Require Import EAst Erasure EWellformed EGlobalEnv.
From MetaRocq.Utils Require Import utils.

Import ListNotations.
Import EEnvMap.

Definition inductive_entry_aux_east (x : kername * EAst.global_decl) acc : common.ienv :=
  match x with
  | (s, EAst.ConstantDecl _) => acc
  | (s, EAst.InductiveDecl m) =>
    (s, ibodies_itypPack m.(ind_bodies)) :: acc
  end.

Definition inductive_env_east (e : EAst.global_declarations) : common.ienv :=
  fold_right inductive_entry_aux_east [] e.

Definition inj_conIdMap tgm :=
  (forall dc dc' tg, dcon_to_tag dc tgm = Some tg ->
     dcon_to_tag dc' tgm = Some tg -> dc = dc').

Definition registered_constructors tgm Σ :=
 (forall ind c d, lookup_constructor Σ ind c = Some d -> 
  dcon_to_tag (dcon_of_con ind c) tgm <> None).

Definition cenv_tgm_coherence cenv tgm :=
  forall ind n n' c_tag c_tag', 
    dcon_to_tag (ind, n) tgm = Some c_tag ->
    dcon_to_tag (ind, n') tgm = Some c_tag' ->
    exists info info', 
      cenv ! c_tag = Some info /\
      cenv ! c_tag' = Some info' /\
      ctor_ind_tag info = ctor_ind_tag info'.

Definition bounded_conIdMap (tgm : conId_map) p :=
  Forall (fun '(ind', nCon', tg) => tg < p)%positive tgm.

Inductive fromNP p : nat -> list positive -> positive -> Prop :=
| fromN0 : fromNP p 0 [] p
| fromNS n l p' : fromNP (p + 1)%positive n l p' -> fromNP p (S n) (cons p l) p'.

Lemma fromN_spec p n : fromNP p n (fromN p n).1 (fromN p n).2.
Proof.
  induction n in p |- *; cbn.
  - constructor.
  - destruct fromN eqn:hf.
    constructor. specialize (IHn (p + 1)%positive).
    rewrite hf in IHn. apply IHn.
Qed.

Lemma dcon_to_info_all_lt {dc tgm tg P} : dcon_to_info dc tgm = Some tg -> Forall (fun '(_, _, tg) => P tg) tgm -> P tg.
Proof.
  induction tgm; cbn; auto.
  - intros [=].
  - destruct a as [[] ?]. destruct conId_dec.
    + intros [= <-].
      intros hf; depelim hf. now destruct d as [].
    + move/IHtgm.
      intros ih hf; depelim hf. apply ih, hf.
Qed.

Definition declared_constructor_ityp ityp ind cstr := 
  match nth_error ityp ind with
  | Some {| itypCnstrs := cstrs |} => cstr <? #|cstrs|
  | None => false
  end.

Fixpoint lookup_env_east (ie : ienv) id := 
  match ie with
  | [] => None
  | hd :: tl => if id == hd.1 then Some hd.2 else lookup_env_east tl id
  end.

Definition declared_constructor_ienv (ie : ienv) (mind : kername) (ind : nat) (cstr : nat) :=
  match lookup_env_east ie mind with
  | Some ityp => declared_constructor_ityp ityp ind cstr
  | None => false
  end.

Definition registered_constructors_ienv (ie : ienv) tgm :=
  forall mind ind cstr, declared_constructor_ienv ie mind ind cstr -> dcon_to_tag (dcon_of_con (mkInd mind ind) cstr) tgm <> None.

Lemma inductive_env_east_eq_ind s m Σ : inductive_env_east (cons (s, InductiveDecl m) Σ) = (s, ibodies_itypPack (ind_bodies m)) :: inductive_env_east Σ.
Proof.
  cbn. reflexivity.
Qed.

Lemma inductive_env_east_eq_const s b Σ : inductive_env_east (cons (s, ConstantDecl b) Σ) = inductive_env_east Σ.
Proof.
  cbn. reflexivity.
Qed.

Lemma declared_minductive_ienv Σ mind mdecl : declared_minductive Σ mind mdecl -> lookup_env_east (inductive_env_east Σ) mind = Some (ibodies_itypPack (ind_bodies mdecl)).
Proof.
  induction Σ.
  - unfold declared_minductive; cbn => //.
  - unfold declared_minductive; destruct a as [kn []].
    rewrite inductive_env_east_eq_const.
    intros hl; apply IHΣ. cbn in hl. destruct (eqb_spec mind kn). congruence. exact hl.
    rewrite inductive_env_east_eq_ind. cbn.
    destruct (eqb_spec mind kn).
    + now intros [= <-].
    + apply IHΣ.
Qed.

Lemma registered_constructors_inductive_env Σ tgm : 
  registered_constructors_ienv (inductive_env_east Σ) tgm -> registered_constructors tgm Σ.
Proof.
  intros hr [mind ind] c d hl.
  eapply hr. clear -hl.
  destruct d as [[mdecl idecl] cdecl].
  eapply (EReorderCstrs.lookup_declared_constructor (id := (mkInd mind ind, c))) in hl.
  destruct hl as [[declm decli] declc].
  cbn in *.
  eapply declared_minductive_ienv in declm.
  unfold declared_constructor_ienv. rewrite declm.
  unfold declared_constructor_ityp, ibodies_itypPack.
  rewrite nth_error_map decli /= length_map. eapply nth_error_Some_length in declc.
  now eapply Nat.ltb_lt.
Qed.

Definition cenv_tgm_cnstrs_coh c (tgm : conId_map) :=
  (forall ind n itag ctag, In (ind, n, itag, ctag) tgm ->
   exists info, c ! ctag = Some info /\ ctor_ind_tag info = itag) /\
  (forall ind n n' itag itag' ctag ctag', 
    In (ind, n, itag, ctag) tgm ->
    In (ind, n', itag', ctag') tgm -> itag = itag').
    
Lemma convert_cnstrs_tgm_l itypNm l cstrs ncstrs ind nCon unboxed boxed i0 c tgm cenv' tgm' p p' : 
  fromNP p ncstrs l p' ->
  ncstrs = #|cstrs| ->
  convert_cnstrs itypNm l cstrs ind nCon unboxed boxed i0 c tgm = (cenv', tgm') ->
  tgm' = (List.rev (mapi (fun i tag => (ind, (nCon + N.of_nat i)%N, i0, tag)) l) ++ tgm)%list.
Proof.
  induction 1 in cstrs, nCon, unboxed, boxed, i0, c, tgm |- *.
   (* in cstrs, ind, nCon, unboxed, boxed, i0, c, tgm |- *. *)
  - cbn. intros ? [= <- <-]; auto.
  - rewrite rev_mapi. cbn -[mapi]. destruct cstrs => //.
    cbn -[mapi]. intros [= ->]. 
    destruct c0 as [cname ccn].
    move/IHfromNP => IH. specialize (IH eq_refl).
    subst tgm'.
    rewrite rev_mapi mapi_app //=. cbn.
    rewrite List.length_rev Nat.add_0_r Nat.sub_diag.
    rewrite -app_assoc. cbn. rewrite N.add_0_r. f_equal.
    destruct l; cbn -[mapi] => //.
    apply mapi_ext_size. len. intros n x hlt. f_equal. f_equal. cbn. f_equal. lia.
Qed.

Lemma convert_cnstrs_tgm itypNm l cstrs ncstrs ind nCon unboxed boxed i0 c tgm cenv' tgm' p p' : 
  fromNP p ncstrs l p' ->
  ncstrs = #|cstrs| ->
  convert_cnstrs itypNm l cstrs ind nCon unboxed boxed i0 c tgm = (cenv', tgm') ->
  inj_conIdMap tgm ->
  bounded_conIdMap tgm p ->
  cenv_tgm_cnstrs_coh c tgm ->
  (forall n itag ctag, In (ind, n, itag, ctag) tgm -> itag = i0) ->
  inj_conIdMap tgm' /\ bounded_conIdMap tgm' p' /\ 
  cenv_tgm_cnstrs_coh cenv' tgm' /\ 
  (forall n itag ctag, In (ind, n, itag, ctag) tgm' -> itag = i0).
Proof.
  induction 1 in cstrs, nCon, unboxed, boxed, i0, c, tgm |- *.
   (* in cstrs, ind, nCon, unboxed, boxed, i0, c, tgm |- *. *)
  - cbn. now intros ? [= <- <-].
  - cbn. destruct cstrs => //.
    cbn. intros [= ->]. 
    destruct c0 as [cname ccn].
    move/IHfromNP => IH. specialize (IH eq_refl).
    intros injm hlt coh hi0.
    apply IH.
    { clear -injm hlt.
      intros dc dc' tg; cbn.
      destruct conId_dec; subst.
      intros [=]. subst p.
      destruct conId_dec; subst.
      intros [=]. reflexivity.
      have h := (dcon_to_info_all_lt _ hlt).
      move/h. lia.
      destruct conId_dec. subst.
      intros hd [= <-].
      have h := (dcon_to_info_all_lt hd hlt). lia.
      apply injm. }
    { constructor. lia.
      eapply Forall_impl; tea. intros [[] ?]. lia. }
    { split. intros ind' n i_tag c_tag [hin'|hin'].
      * noconf hin'. eexists. split. rewrite PTree.gss; reflexivity. reflexivity.
      * rewrite M.gso.
        red in hlt. eapply Forall_forall in hlt; tea. cbn in hlt. lia.
        red in coh. eapply coh; tea.
      * intros ind' n n' itag itag' ctag ctag' H0 H1.
        destruct H0, H1. 
        + noconf H0; noconf H1. auto.
        + noconf H0. red in coh. destruct coh as [? coh].
          now apply hi0 in H1.
        + noconf H1. now apply hi0 in H0.
        + eapply coh; tea.      
      }
    { intros. destruct H0; subst. now noconf H0. now eapply hi0. } 
Qed.

Definition fresh_ind_tgm id n (tgm : conId_map) := 
  ~ (exists j k itag ctag, 
    In ({| inductive_mind := id; inductive_ind := j + n |}, k, itag, ctag) tgm ).

Lemma In_mapi_rec {A B} (x : B) f (l : list A) n : In x (mapi_rec f l n) -> 
  exists i v, nth_error l i = Some v /\ f (n + i) v = x.
Proof.
  induction l in n |- *; cbn => //.
  intros [<-|hin].
  exists 0. exists a; cbn. now rewrite Nat.add_0_r.
  eapply IHl in hin as [i [v [hnth heq]]].
  exists (S i), v. cbn. split => //. rewrite -heq; lia_f_equal.
Qed.

Lemma In_mapi {A B} (x : B) f (l : list A) : In x (mapi f l) -> exists i v, nth_error l i = Some v /\ f i v = x.
Proof. apply In_mapi_rec. Qed.

Lemma In_convert_typack ty id n acc acc' : 
  convert_typack ty id n acc = acc' -> 
  forall ind n' itag ctag, 
    In (ind, n', itag, ctag) acc'.2 ->
    inductive_mind ind = id \/ In (ind, n', itag, ctag) acc.2.
Proof.
  induction ty in n, acc, acc' |- *.
  - destruct acc as ((((? & ?) & ?) & ?) & tgm); cbn.
    intros <-. now cbn.
  - destruct acc as ((((? & ?) & cn) & ?) & tgm); cbn.
    destruct acc' as ((((? & ?) & cn') & ?) & tgm'); cbn.
    destruct a as [itypNm cstrs].
    destruct fromN eqn:hfr.
    destruct convert_cnstrs eqn:eqcs.
    move/IHty. cbn.
    intros h2 ind n' itag ctag.
    move/h2.
    have he := fromN_spec cn #|cstrs|. rewrite hfr //= in he.
    eapply convert_cnstrs_tgm_l in eqcs; tea. 2:reflexivity.
    rewrite eqcs Coqlib.in_app.
    firstorder. eapply In_rev in H.
    eapply In_mapi in H as [i' [v [hnth heq]]].
    noconf heq. cbn. now left. 
Qed.

Lemma convert_typack_tgm ty id n acc acc' : 
  convert_typack ty id n acc = acc' -> 
  inj_conIdMap acc.2 -> bounded_conIdMap acc.2 acc.1.1.2 ->
  fresh_ind_tgm id n acc.2 -> 
  cenv_tgm_cnstrs_coh acc.1.1.1.2 acc.2 ->
  inj_conIdMap acc'.2 /\ bounded_conIdMap acc'.2 acc'.1.1.2 /\
  cenv_tgm_cnstrs_coh acc'.1.1.1.2 acc'.2.
Proof.
  induction ty in n, acc, acc' |- *.
  - destruct acc as ((((? & ?) & ?) & ?) & tgm); cbn.
    intros <-. now cbn.
  - destruct acc as ((((? & ?) & cn) & ?) & tgm); cbn.
    destruct acc' as ((((? & ?) & cn') & ?) & tgm'); cbn.
    destruct a as [itypNm cstrs].
    destruct fromN eqn:hfr.
    destruct convert_cnstrs eqn:eqcs.
    move/IHty. cbn.
    intros h2 inj0 hb fr coh.
    have eqcs' := eqcs.
    have he := fromN_spec cn #|cstrs|. rewrite hfr //= in he.
    eapply convert_cnstrs_tgm_l in eqcs'; tea. 2:reflexivity.
    eapply convert_cnstrs_tgm in eqcs.
    apply h2. apply eqcs. apply eqcs.
    clear -fr eqcs'.
    { intros [j [k [itag [ctag hin]]]].
      apply fr. exists (j + 1), k, itag, ctag.
      rewrite -Nat.add_assoc (Nat.add_comm 1).
      rewrite eqcs' Coqlib.in_app in hin.
      destruct hin.
      { eapply In_rev in H. apply In_mapi in H as [i [v [hnth heq]]].
        noconf heq. lia. } 
        exact H. }
    apply eqcs.
    exact he. 
    reflexivity. exact inj0. exact hb. assumption.
    intros. destruct fr. exists 0; do 3 eexists. exact H.
Qed.

Inductive wf_env_east : list (kername * itypPack) -> Prop :=
| wf_env_east_nil : wf_env_east []
| wf_env_east_cons Σ kn p : 
  wf_env_east Σ ->
  Forall (fun d => d.1 <> kn) Σ ->
  wf_env_east ((kn, p) :: Σ).
Derive Signature for wf_env_east.

Lemma wf_env_inductive {efl : EEnvFlags} Σ :
  wf_glob Σ ->
  wf_env_east (inductive_env_east Σ).
Proof.
  induction 1.
  - econstructor; tea.
  - destruct d; cbn; tea.
    constructor; tea.
    clear -H1 IHwf_glob.
    induction H1.
    * constructor.
    * destruct x as [kn' []]; tea. 
      + cbn in *. now apply IHForall.
      + cbn in *. constructor; tea.
        apply IHForall.
        now depelim IHwf_glob.
Qed.

Lemma convert_env'_tgm ie acc acc' : convert_env' ie acc = acc' -> 
  wf_env_east ie ->
  (forall ind n itag ctag, In (ind, n, itag, ctag) acc.2 -> 
    Forall (fun d => d.1 <> inductive_mind ind) ie) ->
  inj_conIdMap acc.2 -> bounded_conIdMap acc.2 acc.1.1.2 -> 
  cenv_tgm_cnstrs_coh acc.1.1.1.2 acc.2 ->
  inj_conIdMap acc'.2 /\ bounded_conIdMap acc'.2 acc'.1.1.2 /\
  cenv_tgm_cnstrs_coh acc'.1.1.1.2 acc'.2.
Proof.
  induction ie in acc, acc' |- *.
  - destruct acc as ((((? & ?) & ?) & ?) & tgm); cbn.
    intros <-. now cbn.
  - destruct acc as ((((? & ?) & ?) & ?) & tgm); cbn.
    destruct acc' as ((((? & ?) & ?) & ?) & tgm'); cbn.
    destruct a as [id ty].
    intros ce' wf fr injtgm btgm coh.
    depelim wf.
    have hc := convert_typack_tgm ty id 0 (i, c, c0, i0, tgm) _ eq_refl injtgm btgm.
    forward hc.
    { intros [j [k [itag [ctag hin]]]]. eapply fr in hin. cbn in hin.
      depelim hin. cbn in H0; congruence. }
    eapply IHie in ce'; auto.
    { intros ind n itag ctag hin. cbn in fr. cbn in hin.
      eapply In_convert_typack in hin; trea. cbn in hin.
      destruct hin. rewrite H0. apply H.
      apply fr in H0. now depelim H0. }
    apply hc. 
    apply coh. apply hc. cbn. apply coh. apply hc. apply coh.
Qed.

Lemma convert_env_inj default_tag default_itag ie : 
  wf_env_east ie ->
  let tgm := (convert_env default_tag default_itag ie).2 in
  inj_conIdMap tgm.
Proof.
  unfold convert_env. cbn.
  intros wf.
  have he := convert_env'_tgm ie _ _ eq_refl.
  apply he; cbn; auto. red. cbn => //.
  cbn. red. constructor. cbn.
  red. now cbn.
Qed.

Lemma convert_env_coh default_tag default_itag ie :
  wf_env_east ie ->
  let acc := convert_env default_tag default_itag ie in
  cenv_tgm_cnstrs_coh acc.1.1.1.2 acc.2.
Proof.
  unfold convert_env. cbn.
  intros wf.
  have he := convert_env'_tgm ie _ _ eq_refl.
  apply he; cbn; auto. red. cbn => //.
  cbn. red. constructor. cbn.
  red. now cbn.
Qed.

Lemma convert_cnstrs_tgm_In itypNm l cstrs ncstrs ind nCon unboxed boxed i0 c tgm cenv' tgm' p p' : 
  fromNP p ncstrs l p' ->
  ncstrs = #|cstrs| ->
  convert_cnstrs itypNm l cstrs ind nCon unboxed boxed i0 c tgm = (cenv', tgm') ->
  forall dcon, (exists itag ctag, In (dcon, itag, ctag) tgm') <-> 
    (exists itag ctag, In (dcon, itag, ctag) tgm) \/ (exists i, dcon = (ind, i) /\ N.to_nat nCon <= N.to_nat i < N.to_nat nCon + #|cstrs|).
Proof.
  induction 1 in cstrs, nCon, unboxed, boxed, i0, c, tgm |- *.
   (* in cstrs, ind, nCon, unboxed, boxed, i0, c, tgm |- *. *)
  - cbn. intros ? [= <- <-]. intros []. firstorder. noconf H0. lia.
  - cbn. destruct cstrs => //.
    cbn. intros [= ->]. 
    destruct c0 as [cname ccn].
    move/IHfromNP => IH. specialize (IH eq_refl).
    intros dcon.
    specialize (IH dcon). rewrite IH.
    destruct IH as [IH IH']. split.
    intros [[itag [ctag [hin|hin]]]|].
    + noconf hin. right. exists nCon. split => //. split; try lia.
    + now left.
    + destruct H0 as [n' [eq hlt]]. subst dcon. right. exists n'. split => //. lia.
    + intros [[itag [ctag hin]]|].
      * left. do 2 eexists. now right.
      * destruct H0 as [n' [eq hlt]]. subst dcon.
        cbn in *.
        destruct (eq_dec n' nCon). subst.
        left. do 2 eexists. now left. firstorder eauto.
        cbn in *.
        specialize (H3 n'). forward H3. split => //. lia.
        firstorder.
Qed.

Definition declared_cstrs ty id n dcon :=
 exists i cstrs c, 
  dcon = ({| inductive_mind := id; inductive_ind := i |}, c) /\ 
  n <= i <= i + (n + #|ty|) /\
  nth_error ty (i - n) = Some cstrs /\ N.to_nat c < #|itypCnstrs cstrs|.

Lemma convert_typack_tgm_In ty id n acc acc' : convert_typack ty id n acc = acc' -> 
  forall dcon, (exists itag ctag, In (dcon, itag, ctag) acc'.2) <-> 
    (exists itac ctag, In (dcon, itac, ctag) acc.2) \/ declared_cstrs ty id n dcon.
Proof.
  unfold declared_cstrs.
  induction ty in n, acc, acc' |- *.
  - destruct acc as ((((? & ?) & ?) & ?) & tgm); cbn.
    intros <-. cbn. firstorder auto. now rewrite nth_error_nil in H1.
  - destruct acc as ((((? & ?) & cn) & ?) & tgm); cbn.
    destruct acc' as ((((? & ?) & cn') & ?) & tgm'); cbn.
    destruct a as [itypNm cstrs].
    destruct fromN eqn:hfr.
    destruct convert_cnstrs eqn:eqcs.
    move/IHty. cbn.
    intros ih dcon.
    eapply convert_cnstrs_tgm_In in eqcs; trea. 2:{
    have he := fromN_spec cn #|cstrs|. rewrite hfr //= in he. exact he. }
    Unshelve. 2:{ exact dcon. }
    specialize (ih dcon). rewrite eqcs in ih.
    rewrite ih.
    split.
    move=> -[].
    move=> -[] [tag hin].
    { now left. }
    { move: hin => -[-> hlt].
      right. exists n, {|itypNm := itypNm; itypCnstrs := cstrs |}, tag.
      split => //. split => //. lia. rewrite Nat.sub_diag //=. split => //. lia. }
    { move=> -[] x [cstrs' [c3 []]] -> -[] hlt [] hnth hlt'.
      right. exists x, cstrs', c3.
      split => //. split => //. lia. cbn.
      have->: x - n = S (x - (n + 1)) by lia. cbn. split => //. }
    move=> -[]. firstorder.
    { move=> -[] x [cstrs' [c3 []]] -> -[] hlt [] hnth hlt'.
      destruct (le_dec (n + 1) x).
      right. exists x, cstrs', c3.
      split => //. split => //. lia.
      move: hnth. have->: x - n = S (x - (n + 1)) by lia. cbn. split => //.
      assert (x = n) by lia. rewrite H Nat.sub_diag in hnth. cbn in hnth. noconf hnth.
      subst x.
      left; right. exists c3. split => //. now cbn in hlt'. }
Qed.

Lemma in_convert_env' ie acc :
  forall dcon, 
    (exists itag ctag, In (dcon, itag, ctag) (convert_env' ie acc).2) <-> 
    (exists itag ctag, In (dcon, itag, ctag) acc.2) \/ 
      (exists i id ty, nth_error ie i = Some (id, ty) /\ declared_cstrs ty id 0 dcon).
Proof.
  intros dcon.
  induction ie in acc |- *.
  - destruct acc as ((((? & ?) & ?) & ?) & tgm); cbn.
    firstorder. now rewrite nth_error_nil in H.
  - destruct acc as ((((? & ?) & ?) & ?) & tgm); cbn.
    destruct a. rewrite IHie.
    split.
    intros [].
    have := convert_typack_tgm_In i1 k 0 (i, c, c0, i0, tgm) _ eq_refl dcon.
    intros []. forward H0. exact H.
    destruct H0. now left. right. exists 0, k, i1. split => //.
    right.
    destruct H as [i' [id [ty []]]].
    exists (S i'), id, ty. cbn. split => //.
    intros []. left. 
    rewrite (convert_typack_tgm_In i1 k 0 (i, c, c0, i0, tgm) _ eq_refl dcon).
    now left.
    destruct H as [i' [id [ty []]]].
    destruct i'.
    cbn in H. noconf H. left.
    rewrite (convert_typack_tgm_In i1 k 0 (i, c, c0, i0, tgm) _ eq_refl dcon). now right.
    cbn in H.
    right. exists i', id, ty. split => //.
Qed.

Lemma in_convert_env default_tag default_itag ie :
  forall kn pack,
  In (kn, pack) ie -> 
  forall i ityp, nth_error pack i = Some ityp ->
  forall c, c < #|itypCnstrs ityp| ->  
  exists it ct, In (dcon_of_con {| inductive_mind := kn; inductive_ind := i |} c, it, ct) 
    (convert_env default_tag default_itag ie).2.
Proof.
  intros kn pack e i ityp hnth c hl.
  unfold convert_env.
  apply in_convert_env'. cbn. right.
  eapply In_nth_error in e as [n hnth'].
  exists n, kn, pack; split => //.
  red. exists i, ityp, (N.of_nat c). cbn. split => //.
  split => //. lia. rewrite Nat.sub_0_r. split => //. lia.
Qed.

Lemma dcon_to_tag_ok tag tgm : (exists it ct, In (tag, it, ct) tgm) -> dcon_to_tag tag tgm <> None.
Proof.
  induction tgm.
  cbn. firstorder.
  intros [it [ct hin]]. cbn in hin. destruct hin; subst. cbn.
  destruct conId_dec; try congruence. destruct a as [[a it'] ct']; cbn.
  destruct conId_dec; try congruence. apply IHtgm. now exists it, ct.
Qed.

Lemma convert_env_reg default_tag default_itag Σ : 
  let ie := inductive_env_east Σ in
  let tgm := (convert_env default_tag default_itag ie).2 in
  registered_constructors tgm Σ.
Proof.
  intros ie ice.
  eapply registered_constructors_inductive_env. subst ie.
  subst ice. generalize (inductive_env_east Σ).
  clear.
  intros i mind ind cstrs hl. apply dcon_to_tag_ok.
  unfold declared_constructor_ienv in hl.
  destruct lookup_env_east eqn:hl' => //.
  unfold declared_constructor_ityp in hl.
  destruct nth_error eqn:hn => //.
  destruct i1 as [na cnstrs]. apply Nat.ltb_lt in hl.
  eapply (in_convert_env _ _ _ mind i0); tea.
  clear -hl'; move: hl'.
  induction i in mind, i0 |- * => //.
  cbn. case: eqb_spec.
  + intros -> [= <-]. now left.
  + now move=> diff /IHi.
Qed.

Lemma dcon_to_info_spec ind n c_tag tgm : dcon_to_info (ind, n) tgm = Some c_tag ->
  exists ind_tag, In (ind, n, ind_tag, c_tag) tgm.
Proof.
  induction tgm.
  - cbn => //.
  - destruct a as [[[ind' n'] itag] ctag]. cbn -[conId_dec].
    destruct conId_dec.
    + intros [= <-].
      noconf e. exists itag. now left.
    + move/IHtgm.
      intros [itag' hin].
      exists itag'. now right.
Qed.

Lemma cenv_tgm_coh default_tag default_itag ie : 
  wf_env_east ie ->
  let tgm := convert_env default_tag default_itag ie in
  cenv_tgm_coherence tgm.1.1.1.2 tgm.2.
Proof.
  intros wf.
  have h := convert_env_coh default_tag default_itag ie wf.
  cbn. set (ce := convert_env _ _ _) in *.
  cbn in *.
  destruct ce as ((((? & ?) & ?) & ?) & tgm); cbn in *.
  destruct h as [hin htwo].
  intros ind n n' c_tag c_tag' ha hb.
  unfold dcon_to_tag in *.
  apply dcon_to_info_spec in ha, hb.
  destruct ha as [itag hin'].
  destruct hb as [itag' hin''].
  specialize (htwo _ _ _ _ _ _ _ hin' hin''). subst itag'.
  apply hin in hin' as [cinfo []].
  apply hin in hin'' as [cinfo' []].
  exists cinfo, cinfo'; split => //; split => //.
  congruence.
Qed.
