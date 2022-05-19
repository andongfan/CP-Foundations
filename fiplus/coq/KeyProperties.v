(**  Lemmas about pType & Typing
*)
Require Import LibTactics.
Require Import Coq.Program.Equality.
Require Export TermLemmas
               IsomorphicSubtyping.

(************************* ptype *************************************)

Create HintDb common.
#[export] Hint Extern 1 (exists _, _) => exists : common.
#[export] Hint Extern 1 => match goal with
                   [ h : exists _ , _ |- _ ] => destruct h
                 end : common.

Ltac ptype_unify :=
  repeat match goal with
  | H: pType (e_anno _ _) _ |- _ => inverts H
         end; subst.

Lemma principal_type_checks: forall e A B D,
    pType e A -> Typing D nil e Inf B -> A = B.
Proof.
  intros e A B D H H0. gen B D.
  induction H; intros; try solve [ inverts* H0 | inverts* H1 | inverts* H2 ].
  - inverts H1;
    forwards*: IHpType1;
    forwards*: IHpType2;
    subst*.
Qed.


Lemma prevalue_exists_ptype : forall u,
    prevalue u -> exists A, pType u A.
Proof with eauto with common.
  intros u H.
  induction H...
Qed.


Lemma typ_value_ptype: forall v A D,
    Typing D nil v Inf A -> value v -> pType v A.
Proof.
  introv Ht Hv. gen D A.
  induction Hv; intros; inverts~ Ht.
  - (* disjoint *)
    forwards: IHHv1 H1.
    forwards: IHHv2 H4. auto.
  - (* consistent *)
    forwards: IHHv1 H4.
    forwards: IHHv2 H7. auto.
Qed.

#[export] Hint Immediate typ_value_ptype : core.


Lemma typ_prevalue_ptype: forall u A D,
    Typing D nil u Inf A -> prevalue u -> pType u A.
Proof.
  introv Ht Hp. gen D A.
  induction Hp; intros; inverts~ Ht; try inverts~ H; try constructor*.
Qed.

#[export] Hint Immediate typ_prevalue_ptype : core.

Ltac unify_pType e :=
  match goal with
  | [ H1: pType e _, H2: Typing _ e Inf _ |- _] =>
    (forwards: principal_type_checks H1 H2; subst)
  | [ H1: prevalue e, H2: Typing _ e Inf _ |- _] =>
    (forwards: typ_prevalue_ptype H2 H1)
  | [ H1: value e, H2: Typing _ e Inf _ |- _] =>
    (forwards: typ_value_ptype H2 H1)
  | [ H1: prevalue e |- _] =>
    (forwards (?&?): prevalue_exists_ptype H1)
  end.

(************************** some substitution lemmas **************************)


Lemma disjoint_subst: forall E F S U Z B A,
  disjoint (E ++ [(Z,S)] ++ F) B A->
  disjoint F U S ->
  disjoint (map (typsubst_typ U Z) E ++ F) [Z ~~> U] (B) [Z ~~> U] (A).
Proof.
  intros.
  assert(close_typ_wrt_typ_rec 0 Z A -^ Z = A). apply open_typ_wrt_typ_close_typ_wrt_typ.
  assert(close_typ_wrt_typ_rec 0 Z B -^ Z = B). apply open_typ_wrt_typ_close_typ_wrt_typ.
    rewrite <- H1 in H.
    rewrite <- H2 in H.
  apply disjoint_symm in H0.
  forwards: disjoint_disjoint_weakening H H0. auto.
  assert(typsubst_typ U Z B = open_typ_wrt_typ (close_typ_wrt_typ Z B) U).
    apply typsubst_typ_spec.
  assert(typsubst_typ U Z A = open_typ_wrt_typ (close_typ_wrt_typ Z A) U).
    apply typsubst_typ_spec.
  rewrite H4. rewrite H5. auto.
Qed.


Lemma algo_sub_subst: forall E F S U Z B A,
  algo_sub (E ++ [(Z,S)] ++ F) B A->
  disjoint F U S ->
  algo_sub (map (typsubst_typ U Z) E ++ F) [Z ~~> U] (B) [Z ~~> U] (A).
Proof.
  intros.
  assert(close_typ_wrt_typ_rec 0 Z A -^ Z = A). apply open_typ_wrt_typ_close_typ_wrt_typ.
  assert(close_typ_wrt_typ_rec 0 Z B -^ Z = B). apply open_typ_wrt_typ_close_typ_wrt_typ.
    rewrite <- H1 in H.
    rewrite <- H2 in H.
  apply disjoint_symm in H0.
  forwards: algo_sub_disjoint_weakening H H0. auto.
  assert(typsubst_typ U Z B = open_typ_wrt_typ (close_typ_wrt_typ Z B) U).
    apply typsubst_typ_spec.
  assert(typsubst_typ U Z A = open_typ_wrt_typ (close_typ_wrt_typ Z A) U).
    apply typsubst_typ_spec.
  rewrite H4. rewrite H5. auto.
Qed.

(********************************** Typing ************************************)


#[export] Hint Extern 1 => match goal with
                   | [ H: Typing _ _ _ _ _ |- _ ] => inverts H; fail
                           end : FalseHd.

#[export] Hint Extern 3 => match goal with
                   | [ H: notTopLike _ t_top |- _ ] => inverts H; solve_false
                           end : FalseHd.

(* Weakening *)
Lemma Typing_weakening_1: forall E D y X G e dir A,
    Typing (E ++ D) G e dir A ->
    TWell D X ->
    y # (E ++ D) ->
    Typing (E ++ [(y, X)] ++ D) G e dir A.
Proof with try eassumption; auto using algo_sub_weakening, CWell_weakening, TCWell_weakening, TWell_weakening.
  intros. remember (E ++ D). gen E.
  induction H; intros; subst; try solve [
                                    constructor*;
                                    apply~ CWell_weakening;
                                    solve_uniq ].
  - pick fresh x and apply Typ_abs...
  - forwards* : Typ_app...
  - pick fresh x and apply Typ_tabs...
    forwards*: H3 x ((x, A) :: E). solve_notin.
  - forwards*: Typ_tapp.
  - forwards*: Typ_proj.
  - forwards*: Typ_fix.
  - forwards*: IHTyping.
Qed.

Lemma Typing_weakening_2 : forall D G E F e dir T,
    Typing D (E ++ G) e dir T ->
    uniq (E ++ F ++ G) ->
    CWell D F ->
    Typing D (E ++ F ++ G) e dir T.
Proof.
  introv Typ; gen F;
    inductions Typ;
    introv Ok Well; try solve [
      constructor*;
      forwards* HCWell: CWell_app_1 H0 Well;
      forwards*: CWell_reorder HCWell
    ].
    + (* abs *)
      pick fresh x and apply Typ_abs; try assumption.
      rewrite_env (([(x, A)] ++ E) ++ F ++ G).
      applys~ H1.
      solve_uniq.
    + (* app *)
      forwards*: IHTyp1 G E.
    + (* tabs *)
      pick fresh x and apply Typ_tabs.
      forwards* HCWell: CWell_app_1 H Well.
      forwards*: CWell_reorder HCWell.
      forwards*: H1 x.
      applys* (CWell_weakening D [(x, A)] nil F).
    + (* tapp *)
      forwards*: IHTyp.
    + (* proj *)
      forwards*: IHTyp.
    + (* fix *)
      pick fresh x and apply Typ_fix.
      rewrite_env (([(x, A)] ++ E) ++ F ++ G).
      apply~ H0.
      solve_uniq.
    + (* sub *)
      forwards*: IHTyp.
Qed.

Lemma Typing_weakening_3 : forall D (E F : ctx) e dir T,
    Typing D E e dir T ->
    CWell D F ->
    uniq (F ++ E) ->
    Typing D (F ++ E) e dir T.
Proof.
  intros.
  rewrite_env (nil ++ F ++ E).
  apply~ Typing_weakening_2.
Qed.

Lemma Typing_weakening_4: forall F E D G e dir A,
    Typing (F ++ D) G e dir A ->
    TCWell (F ++ E ++ D) ->
    Typing (F ++ E ++ D) G e dir A.
Proof with eauto using CWell_weakening, TWell_weakening, algo_sub_weakening, disjoint_weakening.
  introv Typ TCW. remember (F ++ D). gen F.
  induction Typ; intros; substs...
  - pick fresh X and apply Typ_tabs...
    instantiate_cofinites.
    forwards*: H1 ((X, A) :: F).
    simpl_env. constructor...
Qed.


Lemma Typing_narrowing: forall D E F X A B T e dir,
    Typing (D ++ X ~ A ++ E) F e dir T ->
    algo_sub E B A ->
    Typing (D ++ X ~ B ++ E) F e dir T.
Proof with eauto 4 using algo_sub_regular, TCWell_bind_weakening, TWell_bind_weakening_2, CWell_narrowing; try solve_uniq.
  introv Typ Sub. remember (D ++ X ~ A ++ E). gen D.
  induction Typ; intros; substs...
  - applys Typ_abs... forwards*:algo_sub_bind_weakening H Sub.
  - pick fresh Y and apply Typ_tabs.
    forwards(?&?):algo_sub_regular Sub...
    forwards~: H1 Y ((Y, A0) :: D0).
  - applys Typ_tapp...
    forwards*: disjoint_narrowing H0 Sub.
  - applys Typ_merge...
    forwards*: disjoint_narrowing H Sub.
  - applys Typ_sub...
    forwards*:algo_sub_bind_weakening H Sub.
Qed.

Lemma Typing_narrowing_simpl : forall D A B X G e dir C,
    Typing ((X,B) :: D) G e dir C ->
    D ||- A <: B ->
    Typing ((X,A) :: D) G e dir C.
Proof.
  intros.
  rewrite_env (nil ++ X ~ B ++ D) in H.
  rewrite_env (nil ++ X ~ A ++ D).
  applys* Typing_narrowing.
Qed.

(******************************************************************************)
(* the inferred type is unique *)
Lemma Typing_strenthening_3 : forall D G e A1 A2,
    ( Typing D nil e Inf A1 -> Typing D G e Inf A2 -> A1 = A2 )
    /\
    ( Typing nil G e Inf A1 -> Typing D G e Inf A2 -> A1 = A2 ).
Proof.
  introv. gen_eq Dir : Inf. gen A2 D G.
  inductions e; substs; split; substs; introv Ty1 Ty2; substs; inverts Ty2;
    inverts Ty1; auto; solve_false.
  - eauto using binds_unique.
  - forwards* (?&?): IHe1 A0 A D G.
    forwards*: H; substs.
    forwards*: appDist_arrow_unique H4 H7.
  - forwards* (?&?): IHe1 A0 A D G.
    forwards*: H0; substs.
    forwards*: appDist_arrow_unique H4 H7.
  - forwards* (?&?): IHe1 A0 A D G.
    forwards*: H.
    forwards* (?&?): IHe2 B0 B D G.
    forwards*: H6.
    congruence.
  - forwards* (?&?): IHe1 A0 A D G.
    forwards* (?&?): IHe2 B0 B D G.
    assert (HH7: Typing (nil ++ nil) nil e1 Inf A0) by auto.
    forwards*: Typing_weakening_4 D HH7. simpl_env; auto.
    assert (HH10: Typing (nil ++ nil) nil e2 Inf B0) by auto.
    forwards*: Typing_weakening_4 D HH10. simpl_env; auto.
    simpl_env in *.
    forwards*: H.
    forwards*: H8.
    congruence.
  - forwards* (?&?): IHe1 A A0 D.
    forwards*: H0 H4 H5.
    forwards* (?&?): IHe2 B B0 D.
    forwards*: H12 H7 H10.
    congruence.
  - forwards* (?&?): IHe1 A A0.
    rewrites H.
    forwards* (?&?): IHe2 B B0.
    rewrites~ H11.
    all: eassumption.
  - forwards* (?&?): IHe1 A0 A D G.
    forwards* (?&?): IHe2 B0 B D G.
    forwards~: H0.
    forwards~: H6.
    congruence.
  - forwards* (?&?): IHe1 A0 A D G.
    forwards* (?&?): IHe2 B0 B D G.
    assert (HH7: Typing (nil ++ nil) nil e1 Inf A0) by auto.
    forwards*: Typing_weakening_4 D HH7. simpl_env; auto.
    assert (HH10: Typing (nil ++ nil) nil e2 Inf B0) by auto.
    forwards*: Typing_weakening_4 D HH10. simpl_env; auto.
    simpl_env in *.
    forwards*: H.
    forwards*: H8.
    congruence.
  - forwards* (?&?): IHe1 A A0.
    forwards* (?&?): IHe2 B B0.
    rewrites H.
    rewrites~ H6.
    all: eassumption.
  - forwards* (?&?): IHe1 A A0.
    rewrites H.
    forwards* (?&?): IHe2 B B0.
    rewrites~ H11.
    all: eassumption.
  - forwards* (?&?): IHe A0 A D G.
    forwards*: H; substs.
    forwards*: appDist_rcd_unique H4 H6.
  - forwards* (?&?): IHe A0 A D G.
    forwards*: H0; substs.
    forwards*: appDist_rcd_unique H4 H6.
  - forwards* (?&?): IHe B0 B D G.
    forwards*: H; substs.
    forwards* (_&?): appDist_forall_unique H4 H7.
    congruence.
  - forwards* (?&?): IHe B0 B D G.
    forwards*: H0; substs.
    forwards* (_&?): appDist_forall_unique H4 H7.
    congruence.
Qed.


Lemma inference_unique : forall D G e A1 A2,
    Typing D G e Inf A1 ->
    Typing D G e Inf A2 ->
    A1 = A2.
Proof.
  introv Ty1.
  gen A2.
  dependent induction Ty1; introv Ty2; try (inverts* Ty2).
  - (* t_var *)
    forwards * : binds_unique H1 H6.
  - (* t_app *)
    forwards * : IHTy1_1 H2. subst*.
    forwards * : appDist_arrow_unique H H5.
  - (* t_tabs *)
    forwards * : IHTy1 H3. subst*.
    forwards*(?&?): appDist_forall_unique H H6. subst. auto.
  - (* t_proj *)
    forwards * : IHTy1 H4. subst*.
    forwards * : appDist_rcd_unique H H5.
  - (* t_rcd *)
    forwards * : IHTy1_1.
    forwards * : IHTy1_2.
    subst*.
  - (* t_and *)
    assert(H5': Typing (nil ++ nil) nil e1 Inf A0) by auto.
    forwards * HT1: Typing_weakening_4 D H5'. simpl_env. auto.
    forwards * HT1': Typing_weakening_3 G HT1. simpl_env. auto.
    assert(H8': Typing (nil ++ nil) nil e2 Inf B0) by auto.
    forwards * HT3: Typing_weakening_4 D H8'. simpl_env. auto.
    forwards * HT3': Typing_weakening_3 G HT3. simpl_env. auto.
    simpl_env in *.
    forwards * : IHTy1_1 HT1'.
    forwards * : IHTy1_2 HT3'.
    congruence.
  - (* t_and *)
    assert(M1: Typing (nil ++ nil) nil u1 Inf A) by auto.
    forwards*: Typing_weakening_4 D M1. simpl_env. auto.
    assert(M2: Typing (nil ++ nil) nil u2 Inf B) by auto.
    forwards*: Typing_weakening_4 D M2. simpl_env. auto.
    simpl_env in *.
    forwards (N1&_): Typing_strenthening_3.
    forwards: N1 H3 H5.
    forwards (N2&_): Typing_strenthening_3.
    forwards: N2 H4 H8.
    congruence.
  - (* t_and *)
    forwards *: IHTy1_1 H8.
    forwards *: IHTy1_2 H11.
    substs*.
Qed.


(****************************** Inversion Lemmas ******************************)

(* The relationship of the inferred type and the checked type *)
Lemma Typing_inf_chk_sub: forall D G e B A,
   Typing D G e Inf B -> Typing D G e Chk A -> algo_sub D B A.
Proof.
  introv TypI TypC. gen B.
  inductions TypC; intros; solve_false.
  - (* inter *) intuition eauto.
  - forwards: inference_unique TypC TypI. subst~.
Qed.

Lemma Typing_chk_inter_inv: forall D G e A B,
    Typing D G e Chk (A&B) -> Typing D G e Chk A /\ Typing D G e Chk B.
Proof.
  introv Typ. inverts~ Typ.
  - (* subumption *)
    split; applys* Typ_sub; applys* sub_transtivity.
Qed.


(* This is trivial here but does not hold in v18 which has complete check subsumption *)
(* papp_consistent in TypeSafety.v relies on it implicitly *)
Lemma Typing_abs_chk_arrow_inv : forall D G A e B1 B2,
    Typing D G (e_abs A e) Chk (t_arrow B1 B2) ->
    ( ( D ||- B1 <: A ) /\
    exists L, forall x , x \notin L -> Typing D ((x, A)::G) (e ^ x) Chk B2 ).
Proof with eauto.
  introv Typ; inverts* Typ; solve_false.
Qed.

(* This is trivial here but does not hold in v18 which has complete check subsumption *)
Lemma Typing_chk_arrow_inv : forall D G e B1 B2,
    Typing D G e Chk (t_arrow B1 B2) ->
    ( exists A e', e = e_abs A e' ) \/
    ( exists A, Typing D G e Inf A ).
Proof with eauto.
  introv Typ. inverts* Typ.
Qed.

(****************************** Typing Properties *****************************)

Ltac typing_unify :=
  repeat match goal with
  | H: Typing _ _ e_top Inf _ |- _ => inverts H
  | H: Typing _ _ (e_lit _) Inf _ |- _ => inverts H
  | H: Typing _ _ (e_anno _ _) Inf _ |- _ => inverts H
  | H1: Typing ?D ?G ?e Inf _, H2: Typing ?D ?G ?e Inf _ |- _ => forwards: inference_unique H1 H2; clear H1; subst
(*  | H1: Typing ?D ?G ?e Inf _, H2: Typing ?D ?G ?e Chk _ |- _ => forwards: Typing_inf_chk_sub H1 H2; clear H2 *)
         end.

(* for pre-values only *)
Lemma Typing_chk2inf: forall D G u A,
    Typing D G u Chk A -> prevalue u -> exists B, Typing D G u Inf B /\ algo_sub D B A.
Proof with eauto.
  introv Typ Pre.
  inductions Typ.
  1-3: inverts Pre; solve_false.
  - (* inter *) forwards (?&?&?): IHTyp1... forwards (?&?&?): IHTyp2...
    typing_unify. exists*.
  - exists*.
Qed.

(* for pre-values only *)
Lemma Typing_chk_sub: forall D G u A B,
    Typing D G u Chk A -> prevalue u -> algo_sub D A B -> Typing D G u Chk B.
Proof with eauto.
  introv Typ Pre HS.
  inductions Typ...
  1-3: inverts Pre; solve_false.
  - (* inter *)
    forwards~ (?&?&?): Typing_chk2inf Typ1... forwards~ (?&?&?): Typing_chk2inf Typ2...
    typing_unify. applys* Typ_sub.
    applys* sub_transtivity HS.
Qed.

(* key lemma *)

Lemma Typing_chk_sub_2: forall D G e A B,
  Typing D G e Chk A -> algo_sub D A B -> notTopLike D B -> ord B -> Typing D G e Chk B.
Proof with solve_false.
  introv Typ HS Hnt Ord. gen D G e. indTypSize (size_typ A + size_typ B).
  inverts Typ; inverts keep Hnt.
  - (* abs *) forwards [?| [?|?] ]: sub_arrow_l_inv HS; destruct_conj; subst...
    + applys* Typ_abs. intros. instantiate_cofinites.
      applys* IH. elia.
  - (* tabs *) forwards [?| [?|?] ]: sub_forall_l_inv HS; destruct_conj; subst...
    + inverts Ord.
      forwards (?&?): notTopLike_forall_inv Hnt.
      pick fresh X and apply Typ_tabs.
      now eauto. instantiate_cofinites.
      applys* IH. elia.
      applys Typing_narrowing_simpl; eassumption.
  - (* rcd *) forwards [?| [?|?] ]: sub_rcd_l_inv HS; destruct_conj; subst...
    + applys* Typ_rcd.
      applys* IH. elia.
  - (* inter *)
    inverts HS...
    + applys* IH. elia.
    + applys* IH. elia.
  - applys* Typ_sub.
Qed.

(****************************** Typing Equivalence ***************************)

(* the conventional application typing rule is admissible *)
Lemma Typing_app_subsume : forall D G e1 e2 A B,
    Typing D G e1 Inf (t_arrow A B) -> Typing D G e2 Chk A -> Typing D G (e_app e1 e2) Inf B.
Proof.
  intros D G e1 e2 A B t1 t2.
  applys* Typ_app.
Qed.

#[export] Hint Immediate Typing_app_subsume : core.

(* alternative design of Typ-inter *)
Lemma Typing_chk_spl_merge : forall D G e A B1 B2,
    spl A B1 B2 ->
    Typing D G e Chk B1 ->
    Typing D G e Chk B2 ->
    Typing D G e Chk A.
Proof with destruct_conj; subst; typing_unify; solve_false.
  introv Spl Typ1 Typ2.
  gen D G e. induction Spl; intros.
  - forwards [?|?]: Typing_chk_arrow_inv Typ1; forwards [?|?]: Typing_chk_arrow_inv Typ2...
    + (* e is a lambda *) inverts H1.
      forwards : Typing_abs_chk_arrow_inv Typ1;
        forwards : Typing_abs_chk_arrow_inv Typ2...
      * (* no toplike *) pick fresh X and apply Typ_abs. now auto.
        instantiate_cofinites_with X.
        applys~ IHSpl.
    + (* inferrable term *) applys Typ_sub; eauto using Typing_inf_chk_sub.
  - inverts Typ1; inverts Typ2...
    + (* e is a big lambda *) pick fresh X and apply Typ_tabs. now auto.
      instantiate_cofinites_with X. repeat tassumption.
    + (* inferrable term *) applys* Typ_sub.
  - inverts Typ1; inverts Typ2...
    + (* e is rcd *) constructor*.
    + (* inferrable term *) applys* Typ_sub.
  - applys* Typ_inter.
Qed.

(* check subsumption holds in some special cases *)
Lemma Typing_chk_dup: forall D G e B A,
   Typing D G e Chk A -> DuplicatedType B A -> Typing D G e Chk B.
Proof.
  introv HT HD. induction~ HD.
  - forwards* (?&?): Typing_chk_inter_inv HT.
Qed.


Lemma Typing_chk_subsub : forall G D e A B,
    TWell D B -> Typing D G e Chk A -> subsub A B -> Typing D G e Chk B.
Proof.
  intros. induction~ H1.
  forwards* (?&?): Typing_chk_inter_inv H0.
  applys* Typing_chk_spl_merge.
Qed.

Lemma BCD_arrow : forall B1 C1 B2 C2 D,
    TCWell D ->
    TWell D (t_arrow B1 C1) ->
    TWell D (t_arrow B2 C2) ->
    D ||- (t_arrow B1 C1) & (t_arrow B2 C2) <: (t_arrow (B1 & B2) (C1 & C2)).
Proof.
  intros.
  assert (D ||- (t_arrow B1 C1) & (t_arrow B2 C2) <: (t_arrow (B1 & B2) C1)).
  assert (D ||- (t_arrow B1 C1) <: (t_arrow (B1 & B2) C1)); auto_sub; auto.
  assert (D ||- (t_arrow B1 C1) & (t_arrow B2 C2) <: (t_arrow (B1 & B2) C2)).
  assert (D ||- (t_arrow B2 C2) <: (t_arrow (B1 & B2) C2)); auto_sub; auto.
  assert (spl (t_arrow (B1 & C1) (B2 & C2)) (t_arrow (B1 & C1) B2) (t_arrow (B1 & C1) C2))
    by auto.
  applys~ S_and.
Qed.

Lemma BCD_forall : forall B1 C1 B2 C2 D,
    TCWell D ->
    TWell D (t_forall B1 C1) ->
    TWell D (t_forall B2 C2) ->
    D ||- (t_forall B1 C1) & (t_forall B2 C2) <: (t_forall (B1 & B2) (C1 & C2)).
Proof.
  intros.
  assert (D ||- (t_forall B1 C1) & (t_forall B2 C2) <: (t_forall (B1 & B2) C1)).
  assert (D ||- (t_forall B1 C1) <: (t_forall (B1 & B2) C1)); auto_sub; auto.
  inverts H0.
  pick fresh X.
    applys* algosub_forall_exists_2 X.
    solve_notin.
    auto_sub.
    constructor*.
    instantiate_cofinites.
    rewrite_env (nil ++ X ~ B1 ++ D) in H6.
    forwards~: TWell_bind_weakening_2 (B1 & B2) H6.

  assert (D ||- (t_forall B1 C1) & (t_forall B2 C2) <: (t_forall (B1 & B2) C2)).
  assert (D ||- (t_forall B2 C2) <: (t_forall (B1 & B2) C2)); auto_sub; auto.
  inverts H1.
  pick fresh X.
    applys* algosub_forall_exists_2 X.
    solve_notin.
    auto_sub.
    constructor*.
    instantiate_cofinites.
    rewrite_env (nil ++ X ~ B2 ++ D) in H7.
    forwards~: TWell_bind_weakening_2 (B1 & B2) H7.
  
  applys* S_and (t_forall (B1 & B2) C1) (t_forall (B1 & B2) C2).
  Unshelve. applys empty.
Qed.

Lemma Typing_chk_appDist : forall e A B D G,
    Typing D G e Chk A ->
    appDist A B ->
    Typing D G e Chk B.
Proof with eauto.
  intros. induction* H0;
  forwards (?&?): Typing_chk_inter_inv H.
  forwards~: IHappDist1;
  forwards~: IHappDist2.
  - inverts H2.
    inverts H3; solve_false.
    pick fresh x and apply Typ_abs...
    forwards: Typing_inf_chk_sub H4 H3.
    assert (D ||- A <: (t_arrow B1 C1) & (t_arrow B2 C2)) by eauto.
    forwards: Typing_TCWell H.
    forwards~: BCD_arrow B1 C1 B2 C2.
    forwards: sub_transtivity H6 H8.
    applys~ Typ_sub H9.
  - forwards~: IHappDist1.
    forwards~: IHappDist2.
    inverts H2.
    inverts H3; solve_false.

    applys Typ_rcd...
    forwards: Typing_inf_chk_sub H4 H3.
    assert (D ||- A <: (t_rcd l (B1 & B2))) by eauto.
    applys Typ_sub...
  - forwards~: IHappDist1.
    forwards~: IHappDist2.
    inverts H3.

    inverts H2; solve_false.
    pick fresh X and apply Typ_tabs...
    instantiate_cofinites.
    unfold open_typ_wrt_typ. simpls.
    applys~ Typ_inter.
    rewrite_env (nil ++ X ~ B1 ++ D) in H11.
    forwards~: Typing_narrowing (B1 & B2) H11.
    rewrite_env (nil ++ X ~ B2 ++ D) in H10.
    forwards~: Typing_narrowing (B1 & B2) H10.

    forwards: Typing_inf_chk_sub H4 H2.
    assert (D ||- A <: (t_forall B1 C1) & (t_forall B2 C2)) by eauto.
    forwards~: Typing_TCWell H4.
    forwards~: BCD_forall B1 C1 B2 C2.
    forwards: sub_transtivity H6 H8.
    applys~ Typ_sub H9.
Qed.

Lemma value_inf_prevalue: forall v A,
    value v ->
    Typing nil nil v Inf A ->
    prevalue v.
Proof.
  intros. gen A. inductions H; intros; eauto; solve_false.
  inverts* H1.
Qed.
