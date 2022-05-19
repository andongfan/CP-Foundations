Require Import LibTactics.
Require Import Lia.
Require Import Coq.Program.Equality.
Require Export TypeLemmas.


(*********************************** ord & split *******************************)
#[export] Hint Extern 1 (ord _) =>
progress match goal with
         | H: forall X : atom, X `notin` _ -> ord (?B -^ X) |- ord (t_forall _ ?B) => applys O_all H
         | |- ord (t_forall _ _) => detect_fresh_var_and_apply ord_forall_exists
         | _ => applys O_var + applys O_top + applys O_int + applys O_bot + applys O_arrow + applys O_rcd
         end : core.

(*
#[export] Hint Extern 1 (spl _ _ _) => applys Sp_arrow + applys Sp_rcd + applys Sp_and : core.

#[export] Hint Extern 1 (spl (t_forall _ _)  _ _) => applys Sp_forall : core.
*)

Lemma ord_or_split: forall A,
    lc_typ A -> ord A \/ exists B C, spl A B C.
Proof with (subst~; simpl in *; eauto).
  introv Lc. induction Lc...
  - (* forall *)
    pick fresh x.
    forwards* [?|(?&?&?)]: H0 x.
  - (* arrow *)
    forwards* [?|(?&?&?)]: IHLc2.
  - (* arrow *)
    forwards* [?|(?&?&?)]: IHLc.
Qed.


(********************************************)
(*                                          *)
(*            Ltac solve_false              *)
(*  try solve the goal by contradiction     *)
(*                                          *)
(********************************************)
Lemma split_ord_false : forall T T1 T2,
    lc_typ T -> spl T T1 T2 -> ord T -> False.
Proof with eauto.
  introv Lc Spl Ord. gen T1 T2.
  induction Ord; intros; inverts Spl...
  pick fresh X...
Qed.

#[export]
 Hint Extern 0 =>
match goal with
| [ H1: spl ?T _ _ , H2: ord ?T |- _ ] => applys~ split_ord_false H1 H2
| [ H1: ord _ |- _ ] => inverts H1; fail
| [ H1: spl _ _ _ |- _ ] => inverts H1; fail
| [ H1: topLike _ _ |- _ ] => inverts H1; fail
| [ H1: botLike _ |- _ ] => inverts H1; fail
end : FalseHd.

#[export]
 Hint Extern 1 => match goal with
                               | [ H1: ord (t_arrow _ ?A), H2: spl ?A _ _ |- _ ] =>
                                 inverts H1; applys split_ord_false H2; easy
                               | [ H1: ord ?A, H2: spl (t_arrow _ ?A) _ _ |- _ ] =>
                                 inverts H2; applys split_ord_false H1; easy
                               end : FalseHd.

#[export]
 Hint Extern 3 (False) =>
match goal with
| [ H1: forall _, _ `notin` _ -> spl _ _ _ , H2: forall _ , _ `notin` _ -> ord _ |- _ ]
  => let Xf := fresh in
     let H1f := fresh in
     let H2f := fresh in
     (pick fresh Xf; forwards~ H1f: H1 Xf; forwards~ H2f: H2 Xf; applys~ split_ord_false H1f H2f); fail
end : FalseHd.

Lemma split_unique : forall T A1 A2 B1 B2,
    spl T A1 B1 -> spl T A2 B2 -> A1 = A2 /\ B1 = B2.
Proof with eauto.
  introv s1 s2. gen A2 B2.
  induction s1; intros;
    inverts* s2;
    try solve [forwards* (eq1&eq2): IHs1; subst*].
  pick fresh X.
  forwards* HS: H7 X.
  forwards* (eq1&eq2): H1 HS.
  assert (HR0: C0 = close_typ_wrt_typ X (C0 -^X)). rewrite close_typ_wrt_typ_open_typ_wrt_typ...
  assert (HR1: C1 = close_typ_wrt_typ X (C1 -^X)). rewrite close_typ_wrt_typ_open_typ_wrt_typ...
  assert (HR2: C2 = close_typ_wrt_typ X (C2 -^X)). rewrite close_typ_wrt_typ_open_typ_wrt_typ...
  assert (HR3: C3 = close_typ_wrt_typ X (C3 -^X)). rewrite close_typ_wrt_typ_open_typ_wrt_typ...
  rewrite HR0. rewrite HR1. rewrite HR2. rewrite HR3.
  rewrite eq1. rewrite eq2. split*.
Qed.

Ltac split_unify :=
  repeat match goal with
         | [ H1: spl ?A _ _ , H2: spl ?A _ _ |- _ ] =>
           (progress forwards (?&?): split_unique H1 H2;
            subst; clear H2)
         | [ H: spl (t_and _ _) _ _ |- _ ] => inverts H
         | [ H: spl (t_arrow _ _) _ _ |- _ ] => inverts H
         | [ H: spl (t_rcd _ _) _ _ |- _ ] => inverts H
         | [ H: spl (t_forall _ _) _ _ |- _ ] => inverts H
         end;
  auto.

#[export]
 Hint Extern 1 (spl _ _ _) =>
match goal with
| H: spl ?A _ _ |- spl (t_arrow _ ?A) _ _ => applys Sp_arrow H
| |- spl (t_and _ _) _ _ => applys Sp_and
| H: spl ?A _ _ |- spl (t_rcd _ ?A) _ _ => applys Sp_rcd H
end : core.

(********************************* botlike ************************************)
Lemma top_bot_false: forall D A,
    topLike D A -> botLike A -> False.
Proof.
  intros. induction H0. inversion H. inversion H;subst. auto.
    inversion H;subst. auto.
Qed.

#[export]
 Hint Extern 1 =>
match goal with
| [ H1: topLike _ ?A , H2: botLike ?A |- _ ] => applys top_bot_false H1 H2
end : FalseHd.


Lemma botlike_sub : forall D A B,
    botLike A -> algo_sub D B A -> botLike B.
Proof with eauto.
  intros. induction H0; solve_false...
  inverts H0; solve_false... inverts~ H.
Qed.


Lemma botlike_complete : forall D A,
    algo_sub D A t_bot -> botLike A.
Proof.
  introv H. applys~ botlike_sub H.
Qed.

#[export] Hint Immediate botlike_sub botlike_complete : core.



Lemma botLike_tapp: forall A x J, lc_typ J -> botLike A ->  botLike ([x ~~> J]A).
Proof.
  intros. dependent induction H0;simpl;auto.
  - assert(lc_typ ([x~~>J] B)).
    apply degree_typ_wrt_typ_of_lc_typ in H.
    apply degree_typ_wrt_typ_of_lc_typ in H0.
    apply lc_typ_of_degree.
    apply typsubst_typ_degree_typ_wrt_typ. auto. auto. auto.
  - assert(lc_typ ([x~~>J] A)).
    apply degree_typ_wrt_typ_of_lc_typ in H.
    apply degree_typ_wrt_typ_of_lc_typ in H0.
    apply lc_typ_of_degree.
    apply typsubst_typ_degree_typ_wrt_typ. auto. auto. auto.
Qed.

(********************************* toplike ************************************)

Ltac inverts_for_toplike u :=
  repeat match goal with
         | H: topLike ?A |- _ => match A with
                                 | u => exact H
                                 | context [ u ] => inverts H
                                 end
         end.

#[export] Hint Extern 1 (topLike _ ?A) => progress inverts_for_toplike A : core.

#[export] Hint Extern 1 (topLike _ (?A -^ _) ) =>
destruct_conj;
  progress match A with
           | t_and ?A1 ?A2 => inverts_for_toplike A1; inverts_for_toplike A2
           | _ => inverts_for_toplike A
           end : core.

#[export]
 Hint Extern 1 (topLike ?A) =>
match goal with
| H: forall X : atom, X `notin` _ -> topLike _ |- (topLike _ -^ ?Y) =>
  instantiate_cofinite_with H Y
end : core.

#[export] Hint Extern 2 (topLike (t_forall _ _)) => pick_fresh_applys_and_instantiate_cofinites TL_all : ForallHd2.

Lemma topLike_notTopLike_False: forall D A, topLike D A -> notTopLike D A -> False.
Proof. intros. inverts~ H0. Qed.

#[export] Hint Extern 1 =>
match goal with | H: topLike _ ?A |- _ => applys topLike_notTopLike_False H; applys notTopLike_weakening; [ eassumption | ] end : FalseHd.


Lemma notTopLike_arrow_inv : forall D A B,
    notTopLike D (t_arrow A B) -> notTopLike D B.
Proof.
  introv H. econstructor; inverts~ H.
Qed.

Lemma notTopLike_forall_inv : forall D A B,
    notTopLike D (t_forall A B) ->
    exists L, forall X , X \notin  L  ->
    notTopLike  (cons ( X , A )  D )   (B -^ X).
Proof.
  introv H. inverts H. inverts H1.
  exists (L \u (dom D) \u [[B]]). intros. instantiate_cofinites.
  constructor; auto. intros HF.
  applys H2. econstructor. intros.
  applys* topLike_simpl_subst HF.
Qed.

Lemma notTopLike_rcd_inv : forall D l B,
    notTopLike D (t_rcd l B) -> notTopLike D B.
Proof.
  introv H. econstructor; inverts~ H.
Qed.

#[export] Hint Immediate notTopLike_arrow_inv notTopLike_rcd_inv : core.

#[export] Hint Immediate topLike_notTopLike_False : FalseHd.

Lemma topLike_spl_combine: forall D A B C,
    spl C A B -> topLike D A -> topLike D B -> topLike D C.
Proof.
  introv s. gen D. induction s;intros; eauto.
  - inversion H0;subst. inversion H1;subst. eauto.
  - (* forall *) inverts H2. inverts H3.
    applys~ TL_all (L \u L0 \u L1).
  - inversion H;subst. inversion H0;subst. eauto.
Qed.

Lemma topLike_split_inv: forall D A B C,
    topLike D C -> spl C A B -> topLike D A /\ topLike D B.
Proof.
  introv tl s. gen D.
  induction s; intros; eauto.
  - inversion tl;subst. assert(topLike D C1 /\ topLike D C2). auto.
    destruct H0. auto.
  - (* forall *)  inverts tl. split.
    applys~ TL_all (L \u L0).
    intros. assert (topLike ((X, A) :: D) (C1 -^ X)/\ topLike ((X, A) :: D) (C2 -^ X)). auto.
    destruct H3. auto.
    applys~ TL_all (L \u L0).
    intros. assert (topLike ((X, A) :: D) (C1 -^ X)/\ topLike ((X, A) :: D) (C2 -^ X)). auto.
    destruct H3. auto.
  - inversion tl;subst. assert(topLike D C1 /\ topLike D C2). auto.
    destruct H. auto.
  - (* forall *)  inverts tl. auto.
Qed.

(* this hint make use of the above lemmas, but do not guess the split part *)
#[export]
 Hint Extern 1 (topLike _ ?A) =>
match goal with
| H1: spl A _ _  |- _ => apply (topLike_spl_combine _ _ _ H1)
end : core.

#[export]
 Hint Extern 1 (topLike _ ?A) =>
match goal with
| H1: spl ?C A  _, H2: topLike _ ?C |- _ => lets (?&?): topLike_split_inv H2 H1; easy
| H1: spl ?C _  A, H2: topLike _ ?C |- _ => lets (?&?): topLike_split_inv H2 H1; easy
end : core.


Lemma topLike_weakening : forall T D E F,
    topLike (F ++ D) T ->
    TCWell (F ++ E ++ D) ->
    topLike (F ++ E ++ D) T.
Proof.
  introv H. remember (F ++ D). gen F.
  induction* H; introv Heq; subst*.
  - intros.
    apply TL_all with (union L (dom (F ++ E ++ D))). intros.
    rewrite_env(((X, A) :: F) ++ E ++ D). apply H0. auto. auto.
    rewrite_env((X, A) :: F ++ E ++ D). apply TCW_cons. auto.
    assert(topLike ((X, A) :: F ++ D) (B -^ X)). auto.
    apply topLike_well_tctx in H3. inversion H3;subst.
    apply TWell_weakening. auto.
    apply uniq_push. apply TCWell_uniq. auto. auto.
Qed.
(*
Lemma topLike_weakening : forall T D E F,
    topLike (F ++ D) T ->
    TCWell(F ++ E ++ D) ->
    topLike (F ++ E ++ D) T.
Proof.
  intros. dependent induction H;auto.
  - apply TL_all with (union L (union (dom F) (union (dom E) (dom D)))). intros. rewrite_env(((X, A) :: F) ++ E ++ D).  apply H0. auto. auto.
    simpl. apply TCW_cons. auto. assert(topLike ((X, A) :: F ++ D) (B -^ X)). auto. apply topLike_well_tctx in H3. inversion H3;subst.
    apply TWell_weakening. auto. apply uniq_push. apply TCWell_uniq. auto. auto.
  - assert(binds X A (F ++ E ++ D)). auto. eauto.
Qed. *)
(******************************************************************************)
(******************************* subtyping ************************************)

Ltac try_algo_sub_constructors :=
  applys S_var +
  applys S_int +
  match goal with
  | H: spl ?B _ _ |- algo_sub _ ?B => applys S_and H
  | H: spl ?B _ _ |- algo_sub _ (t_arrow _ ?B) => applys S_and
  | H: spl ?B _ _ |- algo_sub _ (t_rcd _ ?B) => applys S_and
  | |- algo_sub _ (t_and _ _) => applys S_and
  | |- algo_sub _ (t_arrow _ (t_and _ _)) => applys S_and
  | |- algo_sub _ (t_rcd _ (t_and _ _)) => applys S_and
  | |- algo_sub _ (t_forall _ (t_and _ _)) => applys S_and
  | H: topLike ?B |- algo_sub _ ?B => applys S_top H
  | H: topLike _ |- _ => applys S_top
  | H: algo_sub ?A ?B |- algo_sub (t_and ?A _) ?B => applys S_andl
  | H: algo_sub ?A ?B |- algo_sub (t_and  _ ?A) ?B => applys S_andr
  | |- _ =>  applys S_bot +
             applys S_arrow +
             applys S_rcd +
             applys S_all
  end.

#[local] Hint Extern 2 (algo_sub _ _) => progress try_algo_sub_constructors : core.

#[local] Hint Constructors sub : core.

(* topLike specification eqv *)
Lemma topLike_super_top: forall D A,
    topLike D A <-> algo_sub D t_top A.
Proof with eauto.
  split; intros H.
  - proper_ind A...
  - inductions H...
    assert(topLike D B1). auto.
    assert(topLike D B2). auto.
    forwards*: topLike_spl_combine H H2 H3.
Qed.

Lemma topLike_bind_weakening : forall x I J D C F,
    topLike (F ++ (x ~ I) ++ D) C->
    algo_sub D J I ->
    topLike (F ++ (x ~ J) ++ D) C.
Proof.
    intros. remember (F ++ (x ~ I) ++ D) as G. gen F. induction* H; intros; subst.
  - apply algo_sub_regular in H0. destruct H0.
    forwards: TCWell_bind_weakening H H0. auto.
  - assert(TWell (F ++ x ~ J ++ D) A). apply TWell_bind_weakening_2 with I. auto. auto.
  - apply TL_all with L. intros. rewrite_env(((X, A) :: F) ++ x ~ J ++ D). apply H1. auto. auto.
  - assert(exists B, binds X B (F ++ x ~ J ++ D)/\botLike B). clear H. induction F.
    simpl in H1. inversion H1;subst. inversion H;subst.
    forwards: botlike_sub H2 H0. exists J. auto. exists A. auto.
      destruct a. inversion H1;subst. inversion H;subst. exists A. auto.
      apply IHF in H. destruct H. destruct H. exists x0. simpl. auto.
      destruct H3. destruct H3.
      apply TL_var with x0. apply TCWell_bind_weakening with I. auto.
      apply algo_sub_regular in H0. destruct H0. auto. auto. auto.
Qed.

Lemma toplike_sub : forall D A B,
    topLike D A -> algo_sub D A B -> topLike D B.
Proof with eauto.
  introv TL S.
  induction S; inverts~ TL;try solve[apply topLike_spl_combine with B1 B2; auto; eauto; eauto];eauto.
  - apply TL_all with (union L L0). intros. apply H1. auto.
    rewrite_env(nil ++ [(X,B1)] ++ D). apply topLike_bind_weakening with A1. apply H4. auto. auto.
Qed.

#[export] Hint Immediate topLike_spl_combine toplike_sub : core.

#[export] Hint Extern 0 (algo_sub _ ?A ?B) =>
match goal with
| H1: topLike _ ?C, H2: algo_sub _ ?C B |- _ => applys S_top; [ | | applys toplike_sub H1 H2]
end : core.


Lemma algo_sub_bind_weakening : forall x I J D A B F,
    algo_sub (F ++ (x ~ I) ++ D) A B->
    algo_sub D J I ->
    algo_sub (F ++ (x ~ J) ++ D) A B.
Proof.
    intros. remember (F ++ (x ~ I) ++ D) as G. gen D F. induction H; intros; subst;auto.
  - apply algo_sub_regular in H1. destruct H1.
    forwards: TCWell_bind_weakening H H1.
    inversion H0;subst. simpl in H6. apply binds_app_1 in H6. destruct H6. eauto.
      apply binds_cons_iff in H4. destruct H4. destruct H4;subst. assert(TWell (F ++ x ~ J ++ D0) (t_tvar_f x)). eauto. auto.
      eauto.
  - apply algo_sub_regular in H0. destruct H0.
    forwards: TCWell_bind_weakening H H0. auto.
  - forwards: topLike_bind_weakening H1 H2.
    apply algo_sub_regular in H2. destruct H2.
    assert(TWell (F ++ x ~ J ++ D0) A). apply TWell_bind_weakening_2 with I. auto. auto.
  - assert(TWell (F ++ x ~ J ++ D0) A). apply TWell_bind_weakening_2 with I. auto.
    apply algo_sub_regular in H2. destruct H2.
    forwards: TCWell_bind_weakening H H2. auto.
  - assert(TWell (F ++ x ~ J ++ D0) B). apply TWell_bind_weakening_2 with I. auto.
    auto.
  - assert(TWell (F ++ x ~ J ++ D0) A). apply TWell_bind_weakening_2 with I. auto.
    auto.
  - apply S_all with L. auto. auto. intros. rewrite_env(((X, B1) :: F) ++ x ~ J ++ D0).
    apply H2. auto. auto. auto.
  - assert(algo_sub (F ++ x ~ J ++ D0) A B2). auto.
    assert(algo_sub (F ++ x ~ J ++ D0) A B1). auto.
    eauto.
Qed.

Lemma algo_sub_weakening :forall A B D E F,
    algo_sub (F ++ D) A B ->
    TCWell(F ++ E ++ D) ->
    algo_sub (F ++ E ++ D) A B.
Proof with repeat (try applys TWell_weakening; try applys topLike_weakening; try eassumption; auto).
  intros. dependent induction H; auto.
  - applys~ S_top...
  - apply S_all with (union L (union (dom F) (union (dom E) (dom D))))...
    intros. rewrite_env(((X, B1) :: F) ++ E ++ D). applys~ H2... simpl. apply TCW_cons.
    auto. apply algo_sub_regular in H0. destruct H0. apply TWell_weakening. auto. apply uniq_push. apply TCWell_uniq. auto. auto.
  - eauto.
Qed.
(*
Lemma algo_sub_weakening : forall A B D E F,
    algo_sub (F ++ D) A B ->
    TCWell (F ++ E ++ D) ->
    algo_sub (F ++ E ++ D) A B.
Proof.
  intros. dependent induction H;auto.
  - inversion H0;subst. eauto.
  - forwards: topLike_weakening H1 H2.
    forwards*: TWell_weakening H.
  - forwards*: TWell_weakening H0.
  - forwards*: TWell_weakening H.
  - forwards*: TWell_weakening H.
  - forwards: IHalgo_sub... reflexivity. auto.
    apply sub_all with (union L (dom (F ++ E ++ D))) . intros.
      rewrite_env(((X, B1) :: F) ++ E ++ D).
    apply H2. auto. auto. simpl. apply TCW_cons. auto.
      apply algo_sub_regular in H4. auto. apply uniq_push.
      apply TCWell_uniq. auto. auto. auto.
  - eauto.
Qed.
*)

(****************************** splitting *************************************)
#[export] Hint Extern 3 (algo_sub _ t_top _) => applys topLike_super_top : core.
#[export] Hint Immediate topLike_super_top toplike_sub : core.
#[export] Hint Extern 2 (topLike _ ?C) =>
match goal with
| H: algo_sub _ t_top C |- _ => applys topLike_super_top; exact H
| H: topLike _ (t_arrow _ ?A), HS: algo_sub _ ?A ?B |- topLike _ (t_arrow _ ?B) =>
  inverts H; applys TL_arrow; try applys toplike_sub HS
end : core.

(************************ msub <-> algo_sub ***********************************)
(* generalize S_top *)
Lemma sub_top : forall D A B,
    TWell D B -> topLike D A -> algo_sub D B A.
Proof with eauto.
  introv LC TL.
  proper_ind A; try solve [inverts TL; applys* S_top]...
Qed.

(* generalize S_bot *)
Lemma sub_bot : forall D A,
    TCWell D -> TWell D A -> algo_sub D t_bot A.
Proof with eauto.
  introv CTX LC.
  proper_ind A; try solve [applys S_bot; eauto]...
Qed.

(* generalize S_andl *)
Lemma sub_l_andl : forall D A B C,
    TWell D B -> algo_sub D A C -> algo_sub D (t_and A B) C.
Proof with eauto.
  introv lc s. induction s; try solve [applys S_andl; eauto]...
Qed.

(* generalize S_andr *)
Lemma sub_l_andr : forall D A B C,
    TWell D A ->  algo_sub D B C -> algo_sub D (t_and A B) C.
Proof with eauto.
  introv lc s. induction s; try solve [applys S_andr; eauto]...
Qed.

(* generalize S_arr *)
Lemma sub_fun : forall E A B C D,
    algo_sub E B D -> algo_sub E C A -> algo_sub E (t_arrow A B) (t_arrow C D).
Proof with eauto.
  introv s. induction s; intros; try solve [applys S_arrow; eauto]...
Qed.

(* generalize S_rcd *)
Lemma sub_rcd : forall D A B l,
    algo_sub D A B -> algo_sub D (t_rcd l A) (t_rcd l B).
Proof with eauto.
  introv H. induction H. all: try solve [applys S_rcd; eauto]...
Qed.

#[export] Hint Resolve sub_rcd : core.

Lemma algo_sub_rename_alternative:forall n X Y (A B C:typ) (D E:tctx),
    size_typ A + size_typ B <= n
    -> X `notin`  (Metatheory.union [[A]] [[B]])
    -> Y `notin` (Metatheory.union (dom D) (dom E))
    -> algo_sub (E ++ [(X , C)] ++ D) (A -^ X) (B -^ X)
    -> algo_sub ((map (typsubst_typ (t_tvar_f Y) X) E) ++ [(Y ,C)] ++ D) (A -^ Y) (B -^ Y).
Proof.
  intros n. induction n. intros. destruct A;inversion H.
  intros. dependent induction H2.
  - (* var_f *)
    destruct B;inversion x. unfold open_typ_wrt_typ in x. simpl in x.
    destruct(lt_eq_lt_dec n0 0). destruct s. inversion x. inversion x;subst.
    destruct A;inversion x0. unfold open_typ_wrt_typ in x0. simpl in x0.
    destruct(lt_eq_lt_dec n0 0). destruct s. inversion x0. inversion x0;subst.
    unfold open_typ_wrt_typ. simpl.
    assert(TCWell (map (typsubst_typ (t_tvar_f Y) X) E ++ [(Y, C)] ++ D)). apply TCW_subst. auto. auto.
    auto. eauto. inversion x0. subst. assert(X0<>X0). simpl in H0. auto. contradiction.
    inversion x. subst. simpl in H0. assert(X<>X1). auto.
    destruct A;inversion x0. unfold open_typ_wrt_typ in x0. simpl in x0.
    destruct(lt_eq_lt_dec n0 0). destruct s. inversion x0. inversion x0;subst. contradiction.
    inversion x0. subst.
    assert(TCWell (map (typsubst_typ (t_tvar_f Y) X) E ++ [(Y, C)] ++ D)). apply TCW_subst. auto. auto.
    unfold open_typ_wrt_typ. simpl. inversion H3;subst.
    assert(binds X0 (typsubst_typ (t_tvar_f Y) X A) (map (typsubst_typ (t_tvar_f Y) X) E ++ [(Y, C)] ++ D)).
    apply TCW_binds_2. auto. auto. auto. eauto.
  - (* t_int *)
    destruct B;inversion x. unfold open_typ_wrt_typ in x. simpl in x.
    destruct(lt_eq_lt_dec n0 0). destruct s. inversion x. inversion x. inversion x.
    destruct A;inversion x0. unfold open_typ_wrt_typ in x0. simpl in x0.
    destruct(lt_eq_lt_dec n0 0). destruct s. inversion x0. inversion x0. inversion x0.
    assert(TCWell (map (typsubst_typ (t_tvar_f Y) X) E ++ [(Y, C)] ++ D)). apply TCW_subst. auto. auto.
    unfold open_typ_wrt_typ. simpl. auto.
  - (* topLike *)
    assert(ord (B -^ Y)). apply ord_rename with X. auto. auto.
    forwards: topLike_well_tctx H2.
    assert(TWell (map (typsubst_typ (t_tvar_f Y) X) E ++ [(Y, C)] ++ D) (A -^ Y)). apply TW_subst. auto. auto. auto. auto.
    assert(topLike (map (typsubst_typ (t_tvar_f Y) X) E ++ Y ~ C ++ D) (B -^ Y)). apply topLike_subst. auto. auto. auto. auto.
  - (* bot *)
    destruct A;inversion x. unfold open_typ_wrt_typ in x. simpl in x.
    destruct(lt_eq_lt_dec n0 0). destruct s. inversion x. inversion x. inversion x.
    unfold open_typ_wrt_typ. simpl.
    assert(TCWell (map (typsubst_typ (t_tvar_f Y) X) E ++ [(Y, C)] ++ D)). apply TCW_subst. auto. auto.
    assert(ord (B -^ Y)). apply ord_rename with X. auto. auto.
    assert(TWell (map (typsubst_typ (t_tvar_f Y) X) E ++ [(Y, C)] ++ D) (B -^ Y)). apply TW_subst. auto. auto. auto. auto.
    auto.
  - (* andL *)
    destruct A;inversion x. unfold open_typ_wrt_typ in x. simpl in x.
    destruct(lt_eq_lt_dec n0 0). destruct s. inversion x. inversion x. inversion x. subst. simpl in H0.
    forwards:algo_sub_well_tctx H2.
    assert(TWell (map (typsubst_typ (t_tvar_f Y) X) E ++ [(Y, C)] ++ D) (A2 -^ Y)). apply TW_subst. auto. auto. auto. auto.
    simpl in H.
    assert(algo_sub (map (typsubst_typ (t_tvar_f Y) X) E ++ [(Y, C)] ++ D) (A1 -^ Y) (B -^ Y)). apply IHn. lia. auto. auto. auto.
    unfold open_typ_wrt_typ. simpl.
    assert(ord (B -^ Y)). apply ord_rename with X. auto. auto. auto.
  - (* andR *)
    destruct A;inversion x. unfold open_typ_wrt_typ in x. simpl in x.
    destruct(lt_eq_lt_dec n0 0). destruct s. inversion x. inversion x. inversion x. subst. simpl in H0.
    forwards:algo_sub_well_tctx H2.
    assert(TWell (map (typsubst_typ (t_tvar_f Y) X) E ++ [(Y, C)] ++ D) (A1 -^ Y)). apply TW_subst. auto. auto. auto. auto.
    simpl in H.
    assert(algo_sub (map (typsubst_typ (t_tvar_f Y) X) E ++ [(Y, C)] ++ D) (A2 -^ Y) (B -^ Y)). apply IHn. lia. auto. auto. auto.
    unfold open_typ_wrt_typ. simpl.
    assert(ord (B -^ Y)). apply ord_rename with X. auto. auto. auto.
  - (* arrow *)
    destruct B;inversion x. unfold open_typ_wrt_typ in x. simpl in x.
    destruct(lt_eq_lt_dec n0 0). destruct s. inversion x. inversion x. inversion x.
    destruct A;inversion x0. unfold open_typ_wrt_typ in x0. simpl in x0.
    destruct(lt_eq_lt_dec n0 0). destruct s. inversion x0. inversion x0. inversion x0.
    subst. simpl in H. simpl in H0.
    assert(ord (open_typ_wrt_typ_rec 0 (t_tvar_f Y) B4)). apply ord_rename with X. auto. auto.
    assert(algo_sub (map (typsubst_typ (t_tvar_f Y) X) E ++ Y ~ C ++ D)  (open_typ_wrt_typ_rec 0 (t_tvar_f Y) B3)
                    (open_typ_wrt_typ_rec 0 (t_tvar_f Y) A3)). apply IHn. lia. auto. auto. auto.
    assert(algo_sub (map (typsubst_typ (t_tvar_f Y) X) E ++ Y ~ C ++ D)  (open_typ_wrt_typ_rec 0 (t_tvar_f Y) A4)
                    (open_typ_wrt_typ_rec 0 (t_tvar_f Y) B4)). apply IHn. lia. auto. auto. auto.
    unfold open_typ_wrt_typ. simpl. auto.
  - (* forall *)
    destruct B;inversion x. unfold open_typ_wrt_typ in x. simpl in x.
    destruct(lt_eq_lt_dec n0 0). destruct s. inversion x. inversion x. inversion x.
    destruct A;inversion x0. unfold open_typ_wrt_typ in x0. simpl in x0.
    destruct(lt_eq_lt_dec n0 0). destruct s. inversion x0. inversion x0. inversion x0.
    subst. unfold open_typ_wrt_typ. simpl. clear IHalgo_sub H3 x x0. simpl in H. simpl in H0.
    apply S_all with (union L (union (singleton X) (singleton Y))).
    intros. assert(ord (open_typ_wrt_typ_rec 1 (t_tvar_f X) B4 -^ X0)). auto.
    assert(open_typ_wrt_typ_rec 1 (t_tvar_f Y) B4 -^ X0 = (B4 -^ X0) -^ Y). apply open_comm. auto.
    rewrite H7. assert(open_typ_wrt_typ_rec 1 (t_tvar_f X) B4 -^ X0 = (B4 -^ X0) -^ X). apply open_comm. auto.
    rewrite H8 in H6. apply ord_rename with X.
    assert(AtomSetImpl.Subset (typefv_typ (B4 -^ X0)) (typefv_typ (t_tvar_f X0) `union` typefv_typ B4)).
    apply typefv_typ_open_typ_wrt_typ_rec_upper_mutual.
    assert(X `notin` (union [[t_tvar_f X0]] [[B4]])). auto. auto. auto.
    apply IHn. lia. auto. auto. auto. intros.
    assert(algo_sub (map (typsubst_typ (t_tvar_f Y) X) ((X0, open_typ_wrt_typ_rec 0 (t_tvar_f X) B3) :: E) ++ [(Y, C)] ++ D)
                    ((A4 -^ X0) -^ Y) ((B4 -^ X0) -^ Y)).
    apply IHn. rewrite size_typ_open_typ_wrt_typ_var. rewrite size_typ_open_typ_wrt_typ_var. lia.
    assert(AtomSetImpl.Subset (typefv_typ (B4 -^ X0)) (typefv_typ (t_tvar_f X0) `union` typefv_typ B4)).
    apply typefv_typ_open_typ_wrt_typ_rec_upper_mutual.
    assert(AtomSetImpl.Subset (typefv_typ (A4 -^ X0)) (typefv_typ (t_tvar_f X0) `union` typefv_typ A4)).
    apply typefv_typ_open_typ_wrt_typ_rec_upper_mutual.
    assert(X `notin` (union [[t_tvar_f X0]] [[B4]])). auto.
    assert(X `notin` (union [[t_tvar_f X0]] [[A4]])). auto. auto.
    simpl. auto.
    assert(open_typ_wrt_typ_rec 1 (t_tvar_f X) B4 -^ X0 = (B4 -^ X0) -^ X). apply open_comm. auto. rewrite <- H6.
    assert(open_typ_wrt_typ_rec 1 (t_tvar_f X) A4 -^ X0 = (A4 -^ X0) -^ X). apply open_comm. auto. rewrite <- H7.
    apply H5. auto.
    assert((X0, (B3 -^ Y)) :: map (typsubst_typ (t_tvar_f Y) X) E
           = map (typsubst_typ (t_tvar_f Y) X) ((X0, (B3 -^ X)):: E)).
    simpl.
    assert([X ~~> t_tvar_f Y] (B3 -^ X)  = [X ~~> t_tvar_f Y] (B3) ^-^  [X ~~> t_tvar_f Y] (t_tvar_f X)).
    apply typsubst_typ_open_typ_wrt_typ_rec. auto.
    rewrite H7.
    assert([X ~~> t_tvar_f Y] B3 = B3).
    apply typsubst_typ_fresh_eq. simpl in H0. auto.
    rewrite H8.
    assert([X ~~> t_tvar_f Y] (t_tvar_f X) = t_tvar_f Y ).
    simpl. unfold "==". destruct(EqDec_eq_of_X X X);subst;auto.
    contradiction.
    rewrite H9. auto.
    unfold open_typ_wrt_typ in H7.
    rewrite <- H7 in H6.
    assert(open_typ_wrt_typ_rec 1 (t_tvar_f Y) B4 -^ X0 = (B4 -^ X0) -^ Y). apply open_comm. auto. rewrite H8.
    assert(open_typ_wrt_typ_rec 1 (t_tvar_f Y) A4 -^ X0 = (A4 -^ X0) -^ Y). apply open_comm. auto. rewrite H9.
    auto.
  - (* rcd *)
    destruct B;inversion x. unfold open_typ_wrt_typ in x. simpl in x.
    destruct(lt_eq_lt_dec n0 0). destruct s. inversion x. inversion x. inversion x.
    destruct A;inversion x0. unfold open_typ_wrt_typ in x0. simpl in x0.
    destruct(lt_eq_lt_dec n0 0). destruct s. inversion x0. inversion x0. inversion x0.
    subst. simpl in H. simpl in H0.
    assert(ord (open_typ_wrt_typ_rec 0 (t_tvar_f Y) B)). apply ord_rename with X. auto. auto.
    assert(algo_sub (map (typsubst_typ (t_tvar_f Y) X) E ++ Y ~ C ++ D)  (open_typ_wrt_typ_rec 0 (t_tvar_f Y) A)
                    (open_typ_wrt_typ_rec 0 (t_tvar_f Y) B)). apply IHn. lia. auto. auto. auto.
    unfold open_typ_wrt_typ. simpl. auto.
  - (* spl *)
    clear IHalgo_sub1 IHalgo_sub2.
    forwards: open_spl H2. destruct H3. destruct H3.
    assert(spl (B -^ X) (x -^ X) (x0 -^ X)). auto. forwards:split_unique H2 H4. destruct H5;subst.
    clear H4. assert(spl (B -^ Y) (x -^ Y) (x0 -^ Y)). auto.
    forwards:split_decrease_size H2.
    rewrite size_typ_open_typ_wrt_typ_var in H5.
    rewrite size_typ_open_typ_wrt_typ_var in H5.
    rewrite size_typ_open_typ_wrt_typ_var in H5.
    destruct H5.
    pick fresh Z. assert(spl (B -^ Z) (x -^ Z) (x0 -^ Z)). auto.
    assert(X `notin` [[(B -^ Z)]]). assert(X<>Z). auto.
    assert(AtomSetImpl.Subset (typefv_typ (B -^ Z)) (typefv_typ (t_tvar_f Z) `union` typefv_typ B)).
    apply typefv_typ_open_typ_wrt_typ_rec_upper_mutual.
    assert(X `notin` (Metatheory.union [[t_tvar_f Z]] [[B]])). auto. auto.
    forwards: split_fv H8 H7. destruct H9.
    assert(algo_sub (map (typsubst_typ (t_tvar_f Y) X) E ++ Y ~ C ++ D) (A -^ Y) (x -^ Y)).
    apply IHn. lia.
    assert(AtomSetImpl.Subset (typefv_typ x) (typefv_typ (x -^ Z))).
    apply typefv_typ_open_typ_wrt_typ_rec_lower_mutual. auto. auto. auto.
    assert(algo_sub (map (typsubst_typ (t_tvar_f Y) X) E ++ Y ~ C ++ D) (A -^ Y) (x0 -^ Y)).
    apply IHn. lia.
    assert(AtomSetImpl.Subset (typefv_typ x0) (typefv_typ (x0 -^ Z))).
    apply typefv_typ_open_typ_wrt_typ_rec_lower_mutual. auto. auto. auto.
    eauto.
Qed.

Lemma algo_sub_rename:forall X Y (A B C:typ) (D E:tctx),
    X `notin`  (Metatheory.union [[A]] [[B]])
    -> Y `notin` (Metatheory.union (dom D) (dom E))
    -> algo_sub (E ++ [(X , C)] ++ D) (A -^ X) (B -^ X)
    -> algo_sub ((map (typsubst_typ (t_tvar_f Y) X) E) ++ [(Y ,C)] ++ D) (A -^ Y) (B -^ Y).
Proof.
  intros. forwards: algo_sub_rename_alternative H H0 H1. eauto. auto.
Qed.

Lemma algo_sub_simpl_rename:forall X Y (A B C:typ) (D E:tctx),
    X `notin`  (Metatheory.union [[A]] [[B]])
    -> Y `notin`  (dom D)
    -> algo_sub ([(X , C)] ++ D) (A -^ X) (B -^ X)
    -> algo_sub ([(Y ,C)] ++ D) (A -^ Y) (B -^ Y).
Proof.
  intros.
  assert(nil ++ [(X ,C)] ++ D = [(X ,C)] ++ D ). auto.
  rewrite <- H2 in H1.
  apply algo_sub_rename with X Y A B C D nil in H1. auto. auto. auto.
Qed.

(* generalize S_arr *)
Lemma algosub_forall_exists_1 : forall D X A1 A2 B1 B2,
    algo_sub (cons (X,B1) D)A2 B2
    -> algo_sub D B1 A1
    -> algo_sub D (t_forall A1 (close_typ_wrt_typ X A2)) (t_forall B1 (close_typ_wrt_typ X B2)).
Proof with auto.
  introv s. lets s': s.
  dependent induction s; intros;
    try solve [
          applys~ S_all; intros Y FrY;
          repeat rewrite <- typsubst_typ_spec;
          try applys~ ord_rename_aux;
          try applys~ split_rename_aux;
          eauto].
  - apply S_all with (dom D). intros. unfold close_typ_wrt_typ. simpl.
    unfold "==". destruct(EqDec_eq_of_X X X0). subst. auto. auto. auto.
    intros. unfold close_typ_wrt_typ. simpl.
    unfold "==". destruct(EqDec_eq_of_X X X0). subst.
    unfold open_typ_wrt_typ. simpl. inversion H;subst. inversion H8;subst.
    apply S_var. auto. eauto. unfold open_typ_wrt_typ. simpl. inversion H;subst. inversion H8;subst.
    apply S_var. auto. assert(TWell D (t_tvar_f X0)). inversion H0;subst. apply binds_cons_iff in H9.
    destruct H9. destruct H3;subst. contradiction. eauto. rewrite_env(nil++[(X1,B1)]++D). apply TWell_weakening. auto.
  - unfold close_typ_wrt_typ. apply S_all with (dom D). intros. rewrite <- typsubst_typ_spec.
    applys ord_rename_aux. auto. auto. intros.
    assert(close_typ_wrt_typ_rec 0 X A -^ X = A). apply open_typ_wrt_typ_close_typ_wrt_typ.
    rewrite <- H4 in s'.
    assert(close_typ_wrt_typ_rec 0 X B -^ X = B). apply open_typ_wrt_typ_close_typ_wrt_typ.
    rewrite <- H5 in s'.
    apply algo_sub_simpl_rename with X. auto. auto. auto. auto.
  - unfold close_typ_wrt_typ. simpl. apply S_all with (dom D). intros.
    assert(close_typ_wrt_typ_rec 0 X A -^ X = A). apply open_typ_wrt_typ_close_typ_wrt_typ.
    rewrite <- H4 in H1. apply ord_rename with X. auto. auto. auto.
    intros. assert(close_typ_wrt_typ_rec 0 X A -^ X = A). apply open_typ_wrt_typ_close_typ_wrt_typ.
      rewrite <- H4 in s'.
    apply algo_sub_simpl_rename with X. auto. auto. auto. auto.
  - unfold close_typ_wrt_typ. simpl. apply S_all with (dom D). intros.
    assert(close_typ_wrt_typ_rec 0 X C -^ X = C). apply open_typ_wrt_typ_close_typ_wrt_typ.
      rewrite <- H3 in H0. apply ord_rename with X. auto. auto. auto.
    intros. assert(close_typ_wrt_typ_rec 0 X C -^ X = C). apply open_typ_wrt_typ_close_typ_wrt_typ.
      rewrite <- H3 in s'.
    apply algo_sub_simpl_rename with X. auto. auto. auto.
      unfold open_typ_wrt_typ. simpl.
      rewrite open_typ_wrt_typ_rec_close_typ_wrt_typ_rec. rewrite open_typ_wrt_typ_rec_close_typ_wrt_typ_rec. auto.
  - unfold close_typ_wrt_typ. simpl. apply S_all with (dom D). intros.
    assert(close_typ_wrt_typ_rec 0 X C -^ X = C). apply open_typ_wrt_typ_close_typ_wrt_typ.
      rewrite <- H3 in H0. apply ord_rename with X. auto. auto. auto.
    intros. assert(close_typ_wrt_typ_rec 0 X C -^ X = C). apply open_typ_wrt_typ_close_typ_wrt_typ.
      rewrite <- H3 in s'.
    apply algo_sub_simpl_rename with X. auto. auto. auto.
      unfold open_typ_wrt_typ. simpl.
      rewrite open_typ_wrt_typ_rec_close_typ_wrt_typ_rec. rewrite open_typ_wrt_typ_rec_close_typ_wrt_typ_rec. auto.
  - unfold close_typ_wrt_typ. simpl. apply S_all with (dom D). intros.
    assert(close_typ_wrt_typ_rec 0 X B2 -^ X = B2). apply open_typ_wrt_typ_close_typ_wrt_typ.
      rewrite <- H2 in H. apply ord_rename with X. auto. unfold open_typ_wrt_typ. simpl.
        rewrite open_typ_wrt_typ_rec_close_typ_wrt_typ_rec. forwards: algo_sub_lc s1. destruct H3. auto. auto.
    intros. apply algo_sub_simpl_rename with X. auto. auto. auto.
      unfold open_typ_wrt_typ. simpl. rewrite open_typ_wrt_typ_rec_close_typ_wrt_typ_rec.
      rewrite open_typ_wrt_typ_rec_close_typ_wrt_typ_rec. rewrite open_typ_wrt_typ_rec_close_typ_wrt_typ_rec.
      rewrite open_typ_wrt_typ_rec_close_typ_wrt_typ_rec.
      auto.
  - apply S_all with (dom D). intros.
    apply ord_rename with X. auto. rewrite open_typ_wrt_typ_close_typ_wrt_typ. auto. auto.
    intros. apply algo_sub_simpl_rename with X. auto. auto. auto. rewrite open_typ_wrt_typ_close_typ_wrt_typ.
    rewrite open_typ_wrt_typ_close_typ_wrt_typ. auto.
  - apply S_all with (dom D). intros.
    apply ord_rename with X. auto. rewrite open_typ_wrt_typ_close_typ_wrt_typ. auto. auto.
    intros. apply algo_sub_simpl_rename with X. auto. auto. auto. rewrite open_typ_wrt_typ_close_typ_wrt_typ.
    rewrite open_typ_wrt_typ_close_typ_wrt_typ. auto.
  - assert(algo_sub D (t_forall A1 (close_typ_wrt_typ X A))
  (t_forall B1 (close_typ_wrt_typ X B0))). auto.
    assert(algo_sub D (t_forall A1 (close_typ_wrt_typ X A))
  (t_forall B1 (close_typ_wrt_typ X B2))). auto.
    assert(spl (t_forall B1 (close_typ_wrt_typ X B)) (t_forall B1 (close_typ_wrt_typ X B0)) (t_forall B1 (close_typ_wrt_typ X B2))).
    apply Sp_all with {}. forwards:algo_sub_lc H0. destruct H3. auto. intros.
    assert(close_typ_wrt_typ_rec 0 X B -^ X = B). apply open_typ_wrt_typ_close_typ_wrt_typ.
      rewrite <- H4 in H.
    assert(close_typ_wrt_typ_rec 0 X B0 -^ X = B0). apply open_typ_wrt_typ_close_typ_wrt_typ.
      rewrite <- H5 in H.
    assert(close_typ_wrt_typ_rec 0 X B2 -^ X = B2). apply open_typ_wrt_typ_close_typ_wrt_typ.
      rewrite <- H6 in H.
    apply split_rename with X. auto. auto. eauto.
Qed.


(* alternative formulation of algosub_forall_exists_1 *)
Lemma algosub_forall_exists_2 : forall D X A1 A2 B1 B2,
    X \notin ([[A2]] \u [[B2]]) ->
    algo_sub (cons (X,B1) D) (A2-^X) (B2-^X) ->
    algo_sub D B1 A1 ->
    algo_sub D (t_forall A1 A2) (t_forall B1 B2).
Proof with eauto.
  introv Fr s2 s1.
  forwards*: algosub_forall_exists_1 X s2 s1.
  rewrite 2 close_typ_wrt_typ_open_typ_wrt_typ in H...
Qed.


(* generalize S_arr *)
Lemma sub_forall : forall D L A1 A2 B1 B2,
    ( forall X , X \notin  L  -> algo_sub (cons (X,B1) D) ( open_typ_wrt_typ A2 (t_tvar_f X) )
                                           ( open_typ_wrt_typ B2 (t_tvar_f X) ))
    -> algo_sub D B1 A1
    -> algo_sub D (t_forall A1 A2) (t_forall B1 B2).
Proof with eauto.
  introv s2 s1.
  pick fresh X.
  forwards* Hs2: s2 X.
  pick_fresh_applys_and_instantiate_cofinites algosub_forall_exists_2.
Qed.

#[export]
 Hint Immediate sub_top algosub_forall_exists_2 : core.
#[export]
 Hint Resolve sub_bot sub_fun sub_rcd sub_forall algosub_forall_exists_1 : core.

(* this hint has higher priority than try_algo_sub_constructors *)
#[export] Hint Extern 1 (algo_sub _ _ _) =>
match goal with
  | H: algo_sub _ ?A ?B |- algo_sub _ (t_and ?A _) ?B => applys sub_l_andl
  | H: algo_sub _ ?A ?B |- algo_sub _ (t_and  _ ?A) ?B => applys sub_l_andr
  | |- algo_sub _ (t_and ?B _) ?B => applys sub_l_andl
  | |- algo_sub _ (t_and _ ?B) ?B => applys sub_l_andr
end : core.


(*********************** algorithmic subtyping relexivity *********************)
Lemma sub_reflexivity : forall D A,
    TCWell D -> TWell D A -> algo_sub D A A.
Proof.
  introv CTX Lc. induction Lc;auto. eauto.
    apply S_and with A B. eauto. auto. auto.
  apply sub_forall with (union (dom D) L). intros. apply H0. auto.
    apply TCW_cons. auto. auto. apply TCWell_uniq in CTX. auto. auto.
Qed.

#[export] Hint Extern 1 (algo_sub _ _ _) =>
match goal with
  | |- algo_sub _ ?A ?A => applys sub_reflexivity
end : core.

(************************ around split and subtyping **************************)
Lemma spl_sub_l : forall D A B C,
    spl A B C -> TCWell D-> TWell D A -> algo_sub D A B.
Proof.
  introv H. gen D. induction H;intros;auto.
    intros. apply sub_forall with (union L (dom D)). intros. apply H1. auto.
      apply TCW_cons. auto. auto. apply TCWell_uniq in H2. auto.
      apply TWell_all_open with A. rewrite_env(nil++[(X,A)]++D). apply TWell_weakening. auto.
      eauto. auto.
Qed.

Lemma spl_sub_r : forall D A B C,
    spl A B C -> TCWell D-> TWell D A -> algo_sub D A C.
Proof.
  introv H. gen D. induction H;intros;auto.
    intros. apply sub_forall with (union L (dom D)). intros. apply H1. auto.
      apply TCW_cons. auto. auto. apply TCWell_uniq in H2. auto.
      apply TWell_all_open with A. rewrite_env(nil++[(X,A)]++D). apply TWell_weakening. auto.
      eauto. auto.
Qed.

#[export] Hint Immediate spl_sub_l spl_sub_r : core.

(* splitting does not lose or add information to a type *)

Lemma split_sub: forall D A B C,
    spl A B C -> TCWell D-> TWell D A -> algo_sub D A (t_and B C) /\ algo_sub D (t_and B C) A.
Proof.
  intros D A B C H CTX TW.
  split.
  - lets~: spl_sub_l H CTX TW. lets~: spl_sub_r H CTX TW. eauto.
  - gen D. induction H;intros.
      assert(spl (t_arrow A B) (t_arrow A C1) (t_arrow A C2)). auto.
      forwards: TWell_spl TW H1. destruct H2.
      apply S_and with (t_arrow A C1) (t_arrow A C2). auto. auto. auto.
      assert(spl (t_forall A B) (t_forall A C1) (t_forall A C2)). eauto.
      forwards: TWell_spl TW H2. destruct H3.
      apply S_and with (t_forall A C1) (t_forall A C2). auto. auto. auto.
      assert(spl (t_rcd l B) (t_rcd l C1) (t_rcd l C2)). auto.
      forwards: TWell_spl TW H0. destruct H1.
      apply S_and with (t_rcd l C1) (t_rcd l C2). auto. auto. auto.
      auto.
Qed.

(********************** around bottom type ************************************)
Lemma bot_sub : forall D A B,
    algo_sub D A t_bot -> TWell D B -> algo_sub D A B.
Proof.
  introv S LC.
  inductions S; solve_false; try forwards~: IHS; eauto.
Qed.

#[local] Hint Immediate bot_sub : core.

(********************** some subtyping inversion lemmas ***********************)
(* inversion on left split *)
Lemma sub_inversion_split_l : forall D A B A1 A2,
    algo_sub D A B -> spl A A1 A2 -> ord B -> algo_sub D A1 B \/ algo_sub D A2 B.
Proof with auto.
  introv H. gen A1 A2.
  induction H; intros; solve_false; split_unify...
  - (* arrow *)
    forwards*: IHalgo_sub2. intuition eauto.
  - (* forall *)
    pick fresh X. forwards: H10 X. solve_notin.
    forwards [?|?]: H2 X H3. solve_notin. inverts H4...
    + left. applys* algosub_forall_exists_2. solve_notin.
    + right. applys* algosub_forall_exists_2. solve_notin.
  - (* record *)
    forwards*: IHalgo_sub. intuition eauto.
Qed.

(* inversion on right split *)
Lemma sub_r_spl_l : forall D A B B1 B2,
    spl B B1 B2 -> algo_sub D A B -> algo_sub D A B1.
Proof.
  introv Hspl Hsub.
  inverts Hsub; split_unify; solve_false.
Qed.

Lemma sub_r_spl_r : forall D A B B1 B2,
    spl B B1 B2 -> algo_sub D A B -> algo_sub D A B2.
Proof.
  introv Hspl Hsub.
  inverts Hsub; split_unify; solve_false.
Qed.

Lemma sub_inversion_split_r : forall D A B B1 B2,
    algo_sub D A B -> spl B B1 B2 -> algo_sub D A B1 /\ algo_sub D A B2.
Proof.
  introv Hsub Hspl. gen B1 B2.
  inductions Hsub; intros; split_unify; solve_false.
Qed.


Lemma sub_inversion_split_r_equiv : forall D A B B1 B2,
    spl B B1 B2 ->
    algo_sub D A B <-> (algo_sub D A B1 /\ algo_sub D A B2).
Proof.
  introv Hspl. split.
  intros. applys~ sub_inversion_split_r H Hspl.
  intros. destruct H. applys* S_and.
Qed.

#[export] Hint Immediate sub_r_spl_l sub_r_spl_r : core.

(* prove trans via proper type *)
Lemma sub_transtivity : forall D A B C,
    algo_sub D A B -> algo_sub D B C -> algo_sub D A C.
Proof with ( split_unify; solve_false; eauto 4).
  introv S1 S2.
  assert (Lc: lc_typ B) by eauto.
  assert (r: R B) by applys* (lc_types_are_proper B).
  clear Lc. gen D A C.
  induction r; (* <- proper_ind B *)
    intros; try solve [inductions S2; auto].
  - inductions S2...
  - inductions S2...
  - inductions S2...
  - (* bot *)
    applys bot_sub...
  - (* arrow *)
    inductions S2... clear IHS2_1 IHS2_2.
    (* S_arr *)
    inductions S1...
  - (* forall *)
    inductions S2... forwards~ (?&?):algo_sub_regular S1. clear H4 IHS2.
    inductions S1...
    + inverts H6.
      assert(topLike D (t_forall B1 B2)). apply TL_all with (union L0 L1).
      intros. assert(algo_sub ((X, B1) :: D) (B -^ X) (B2 -^ X)). auto.
      assert(topLike ((X, A) :: D) (B -^ X)). auto.
      assert(topLike ((X, B1) :: D) (B -^ X)). rewrite_env(nil ++ [(X,B1)] ++ D).
      apply topLike_bind_weakening with A. auto. auto.
      applys* toplike_sub. auto.
    + pick_fresh_applys_and_instantiate_cofinites algosub_forall_exists_2.
      apply H1. rewrite_env(nil ++ [(H9, B1)] ++ D). applys~ algo_sub_bind_weakening A. auto.
  - (* rcd *)
    inductions S2... forwards~ (?&?):algo_sub_regular S1. clear IHS2.
    (* S_rcd *)
    inductions S1...
    applys* S_top.
    applys* toplike_sub H1.
  - (* split A B C *)
    assert (r: R C0) by applys* (lc_types_are_proper C0). gen A B.
    induction r; (* <- proper_ind C0, the type at the end *)
      introv S1 S2 Hspl HRb IH;
      try solve [ (* if C0 is an ordinary type *)
            forwards (?&?): sub_inversion_split_r S1 Hspl;
            forwards [?|?]: sub_inversion_split_l S2 Hspl;
            [eauto | applys~ IH | applys~ IHr2 ] ].
    + (* splittable type *)
      forwards (?&?): sub_inversion_split_r S2 H.
      applys S_and H. applys~ IHr1 S1 Hspl. applys~ IHr3 S1 Hspl.
Qed.

#[export] Hint Immediate sub_transtivity : core.


#[export]
Hint Extern 1 (algo_sub _ ?A ?B) =>
match goal with
| |- algo_sub _ (t_and B _) B => applys sub_l_andl
| |- algo_sub _ (t_and _ B) B => applys sub_l_andr
| |- algo_sub _ A A  => applys sub_reflexivity
| H: algo_sub _ A ?C |- _  => applys sub_transtivity H
end : SubHd.

Ltac auto_sub :=
  try (trivial ;
       match goal with
       | [ |- algo_sub _ ?A ?A ] => (applys sub_reflexivity)
       | [ |- algo_sub _ (t_and ?A1 _) ?A1 ] => (applys sub_l_andl; eauto with LcHd)
       | [ |- algo_sub _ (t_and _ ?A2) ?A2 ] => (applys sub_l_andr; eauto with LcHd)
       | [ H : algo_sub _ ?A (t_and ?A1 _) |- algo_sub _ ?A ?A1 ] => (applys sub_transtivity H; auto_sub)
       | [ H : algo_sub _?A (t_and _ ?A2) |- algo_sub _ ?A ?A2 ] => (applys sub_transtivity H; auto_sub)
       | [ |- algo_sub _ (t_and ?C ?D) (t_and ?A ?B) ] => (eapply S_and; try apply Sp_and)
       | [ |- algo_sub _ (t_and (t_arrow ?A ?B) (t_arrow ?A ?C)) (t_arrow ?A (t_and ?B ?C)) ] => (eapply S_and)
       | [ H1: algo_sub _ ?A ?B, H2: algo_sub _ ?B ?C |- algo_sub _ ?A ?C ] =>
         (forwards: sub_transtivity H1 H2; auto)
       | [ H: topLike ?A |- algo_sub _ _ ?A ] =>
         (applys sub_top H; auto)
       | [ H: algo_sub _ t_top ?A |- algo_sub _ _ ?A ] =>
         (apply topLike_super_top in H; apply sub_top; auto)
       | [ H: topLike _ ?A |- algo_sub _ _ (t_arrow _ ?A) ] =>
         (apply TL_arrow in H; apply S_top; auto)

       | [ H: spl ?A _ _ |- algo_sub _ _ ?A ] => (applys S_and H)

       | [ H1: spl ?A ?B ?C, H2: ord ?D, H3: algo_sub _ ?A ?D |- _ ] => (
           forwards [?|?]: sub_inversion_split_l H1 H2 H3;
           clear H3)
       | [ H1: spl ?A ?B ?C |- _ ] => (
           forwards : split_sub H1;
           forwards : spl_sub_l H1;
           forwards : spl_sub_r H1;
           clear H1)
       | [ |- algo_sub _ (t_arrow ?A ?B) (t_arrow ?C ?D) ] => apply sub_fun
       | [ H1: algo_sub _ ?A ?B |- algo_sub _ ?A ?C ] =>
         assert ( algo_sub _ B C ) by auto
       end).


Notation "D ||- A <: B"         := (algo_sub D A B) (at level 70, A at level 69, B at level 69).

Lemma topLike_super_any: forall D A B,
    topLike D A -> TWell D B -> algo_sub D B A.
Proof with eauto.
  introv tl tw.
  applys* sub_transtivity t_top.
Qed.

#[export] Hint Extern 1 (algo_sub ?D ?B ?A) =>
match goal with
| H: topLike D A |- _ => applys topLike_super_any
end : core.

Lemma sub_arrow_rcd_inv : forall D A1 A2 l B,
    D ||- t_arrow A1 A2 <: t_rcd l B -> topLike D (t_rcd l B).
Proof.
  introv H. inductions H; eauto.
  - inverts~ H.
    forwards~ : IHalgo_sub1.
    forwards~ : IHalgo_sub2.
    inverts H. inverts* H2.
Qed.

Lemma sub_arrow_forall_inv : forall D A1 A2 B1 B2,
    D ||- t_arrow A1 A2 <: t_forall B1 B2 -> topLike D (t_forall B1 B2).
Proof.
  introv H. inductions H; eauto.
  - inverts~ H.
    forwards~ : IHalgo_sub1.
    forwards~ : IHalgo_sub2.
    assert (spl (t_forall B1 B2) (t_forall B1 C1) (t_forall B1 C2)) by eauto.
    eauto.
Qed.

Lemma sub_forall_arrow_inv : forall D A1 A2 B1 B2,
    D ||- t_forall A1 A2 <: t_arrow B1 B2 -> topLike D (t_arrow B1 B2).
Proof.
  introv H. inductions H; eauto.
  - inverts~ H.
    forwards~ : IHalgo_sub1.
    forwards~ : IHalgo_sub2.
    assert (spl (t_arrow B1 B2) (t_arrow B1 C1) (t_arrow B1 C2)) by eauto.
    eauto.
Qed.

Lemma sub_forall_rcd_inv : forall D A1 A2 l B,
    D ||- t_forall A1 A2 <: t_rcd l B -> topLike D (t_rcd l B).
Proof.
  introv H. inductions H; eauto.
  - inverts~ H.
    forwards~ : IHalgo_sub1.
    forwards~ : IHalgo_sub2.
    inverts H. inverts* H2.
Qed.

Lemma sub_rcd_arrow_inv : forall D l A B1 B2,
    D ||-  t_rcd l A <: t_arrow B1 B2 -> topLike D (t_arrow B1 B2).
Proof.
  introv H. inductions H; eauto.
  - inverts~ H.
    forwards~ : IHalgo_sub1.
    forwards~ : IHalgo_sub2.
    assert (spl (t_arrow B1 B2) (t_arrow B1 C1) (t_arrow B1 C2)) by eauto.
    eauto.
Qed.

Lemma sub_rcd_forall_inv : forall D l A B1 B2,
    D ||- t_rcd l A <: t_forall B1 B2 -> topLike D (t_forall B1 B2).
Proof.
  introv H. inductions H; eauto.
  - inverts~ H.
    forwards~ : IHalgo_sub1.
    forwards~ : IHalgo_sub2.
    assert (spl (t_forall B1 B2) (t_forall B1 C1) (t_forall B1 C2)) by eauto.
    eauto.
Qed.

Lemma sub_arrow_l_inv : forall D A1 A2 B,
    D ||- (t_arrow A1 A2) <: B ->
    topLike D B \/
    (exists B1 B2, B = t_arrow B1 B2 /\ D ||- B1 <: A1 /\ D ||- A2 <: B2) \/
    (exists B1 B2, B = B1&B2 /\ D ||- (t_arrow A1 A2) <: B1 /\ D ||- (t_arrow A1 A2) <: B2).
Proof with try eassumption.
  introv sub. indTypSize (size_typ A1 + size_typ A2 + size_typ B).
  inverts sub.
  - left~.
  - right. left. exists*.
  - (* splittable *) inverts H.
    + (* arrow *)
      repeat match goal with
             | H: algo_sub D (t_arrow _ _) (t_arrow _ _) |- _ =>
               forwards [?| [?|?] ]: IH H; elia; clear H
             end; destruct_conj;
        repeat match goal with
               | H: topLike _ (t_arrow _ _) |- _ => inverts H
               | H: _ = _ |- _ => inverts H
               end; solve_false.
      1: (* both toplike *) left*.
      1-3: (* one toplike *) right; left; exists; splits~; applys* S_and.
    + (* forall *) left.
      forwards : sub_arrow_forall_inv H0.
      forwards : sub_arrow_forall_inv H1.
      assert (spl (t_forall A B0) (t_forall A C1) (t_forall A C2)) by eauto.
      now eauto.
    + (* rcd *) left.
      forwards : sub_arrow_rcd_inv H0.
      forwards : sub_arrow_rcd_inv H1.
      assert (spl (t_rcd l0 B0) (t_rcd l0 C1) (t_rcd l0 C2)) by eauto.
      now eauto.
    + (* and *) right. right*.
Qed.

Lemma sub_forall_l_inv : forall D A1 A2 B,
    D ||- (t_forall A1 A2) <: B ->
    topLike D B \/
    (exists B1 B2 L, B = t_forall B1 B2 /\ D ||- B1 <: A1 /\
    ( forall X , X \notin  L  -> algo_sub  (cons ( X , B1 )  D )   ( open_typ_wrt_typ A2 (t_tvar_f X) )   ( open_typ_wrt_typ B2 (t_tvar_f X) )  ) ) \/
    (exists B1 B2, B = B1&B2 /\ D ||- (t_forall A1 A2) <: B1 /\ D ||- (t_forall A1 A2) <: B2).
Proof with try eassumption.
  introv sub. indTypSize (size_typ A1 + size_typ A2 + size_typ B).
  inverts sub.
  - left~.
  - right. left. exists*.
  - (* splittable *) inverts H.
    + (* arrow *) left.
      forwards : sub_forall_arrow_inv H0.
      forwards : sub_forall_arrow_inv H1.
      assert (spl (t_arrow A B0) (t_arrow A C1) (t_arrow A C2)) by eauto.
      now eauto.
    + (* forall *)
      assert (spl (t_forall A B0) (t_forall A C1) (t_forall A C2)) by eauto.
      repeat match goal with
             | H: algo_sub D (t_forall _ _) (t_forall _ _) |- _ =>
               forwards [?| [?|?] ]: IH H; elia; clear H
             end; destruct_conj;
        repeat match goal with
               | H: topLike _ (t_forall _ _) |- _ => inverts H
               | H: _ = _ |- _ => inverts H
               end; solve_false;
          try assert (topLike D (t_forall A C1)) by eauto;
          try assert (topLike D (t_forall A C2)) by eauto.
      1: (* both toplike *) left*.
      1-3: (* one toplike *) right; left.
      1-2: exists x B0 (L \u x1 \u L0); splits~;
           intros X Fry; instantiate_cofinites_with X; applys* S_and.
      1: exists x2 B0 (L \u x1 \u x4); splits~;
           intros X Fry; instantiate_cofinites_with X; applys* S_and.
    + (* rcd *) left.
      forwards : sub_forall_rcd_inv H0.
      forwards : sub_forall_rcd_inv H1.
      assert (spl (t_rcd l0 B0) (t_rcd l0 C1) (t_rcd l0 C2)) by eauto.
      now eauto.
    + (* and *) right. right*.
Qed.

Lemma sub_rcd_l_inv : forall D l A B,
    D ||- (t_rcd l A) <: B ->
    topLike D B \/
    (exists B2, B = t_rcd l B2 /\ D ||- A <: B2) \/
    (exists B1 B2, B = B1&B2 /\ D ||- (t_rcd l A) <: B1 /\ D ||- (t_rcd l A) <: B2).
Proof with try eassumption.
  introv sub. indTypSize (size_typ A + size_typ B).
  inverts sub.
  - left~.
  - right. left. exists*.
  - (* splittable *) inverts H.
    + (* arrow *) left.
      forwards : sub_rcd_arrow_inv H0.
      forwards : sub_rcd_arrow_inv H1.
      assert (spl (t_arrow A0 B0) (t_arrow A0 C1) (t_arrow A0 C2)) by eauto.
      now eauto.
    + (* forall *) left.
      forwards : sub_rcd_forall_inv H0.
      forwards : sub_rcd_forall_inv H1.
      assert (spl (t_forall A0 B0) (t_forall A0 C1) (t_forall A0 C2)) by eauto.
      now eauto.
    + (* rcd *)
      repeat match goal with
             | H: algo_sub D (t_rcd _ _) (t_rcd _ _) |- _ =>
               forwards [?| [?|?] ]: IH H; elia; clear H
             end; destruct_conj;
        repeat match goal with
               | H: topLike _ (t_rcd _ _) |- _ => inverts H
               | H: _ = _ |- _ => inverts H
               end; solve_false.
      1: (* both toplike *) left*.
      1-3: (* one toplike *) right; left; exists; splits~; applys* S_and.
    + (* and *) right. right*.
Qed.


(**************************** declarative subtyping ***************************)
#[local] Remove Hints DS_trans : core.

Lemma sub_decidable_alternative: forall n, forall D A B,
      size_typ A + size_typ B <= n -> (algo_sub D A B)\/~(algo_sub D A B).
Proof.
  intros n. induction n.
    intros. destruct A;inversion H.
    intros.
    assert(TCWell D\/~TCWell D). apply TCWell_decidable.
    assert(TWell D A\/~TWell D A). apply TWell_decidable.
    assert(TWell D B\/~TWell D B). apply TWell_decidable.
    destruct H0. destruct H1. destruct H2.
    assert(topLike D B\/~topLike D B).
    apply toplike_decidable.
    destruct H3. auto.
    forwards: TWell_lc_typ H2.
    forwards: TWell_lc_typ H1.
    assert(ord B\/exists E F,spl B E F). apply ord_or_split. auto.
    assert(ord A\/exists E F,spl A E F). apply ord_or_split. auto.
    destruct H6. destruct H7.
    destruct A;auto;destruct B; try solve[ auto; right; unfold not; intros; inversion H8;subst; auto; forwards: split_ord_false H4 H9 H6; auto].
      -(* var_f var_f *)
      unfold typevar in X. unfold typevar in X0.
        assert( {X = X0} + {~X = X0}). eauto.
        destruct H8;subst;auto. right. unfold not. intros. inversion H8;subst. auto. auto.
        forwards: split_ord_false H4 H9 H6. auto.
      -(* forall forall *)
        assert(algo_sub D B1 A1\/~algo_sub D B1 A1). apply IHn. simpl in H. lia.
        destruct H8.
        pick fresh X.
        assert( algo_sub (cons (X,B1) D) (A2-^X) (B2-^X)\/~algo_sub (cons (X,B1) D) (A2-^X) (B2-^X)). apply IHn.
        rewrite size_typ_open_typ_wrt_typ_var. rewrite size_typ_open_typ_wrt_typ_var. simpl in H. lia.
        destruct H9. left. apply algosub_forall_exists_2 with X. eauto. auto. auto.
        right. unfold not. intros. inversion H10;subst. auto. pick fresh Y.
        assert(algo_sub ((Y, B1) :: D) (A2 -^ Y) (B2 -^ Y)). apply H18. eauto.
        assert(algo_sub ((X, B1) :: D) (A2 -^ X) (B2 -^ X)). apply algo_sub_simpl_rename with Y. auto. auto. auto. auto. auto.
        forwards: split_ord_false H4 H11 H6; auto.
        right. unfold not. intros. inversion H9;subst. auto. auto.
        forwards: split_ord_false H4 H10 H6; auto.
      -(* arrow arrow *)
      simpl in H. assert(algo_sub D B1 A1\/~algo_sub D B1 A1). apply IHn. lia.
        assert(algo_sub D A2 B2\/~algo_sub D A2 B2). apply IHn. lia.
        destruct H8. destruct H9. auto. right. unfold not. intros.
        inversion H10;subst. auto. auto.
        forwards: split_ord_false H4 H11 H6; auto.
        right. unfold not. intros.
        inversion H10;subst. auto. auto.
        forwards: split_ord_false H4 H11 H6; auto.
      - (* andL *)
        inversion H7.
      - (* andL *)
        inversion H7.
      - (* andL *)
        inversion H7.
      - (* andL *)
        inversion H7.
      - (* andL *)
        inversion H7.
      - (* andL *)
        inversion H7.
      - (* andL *)
        inversion H7.
      - (* andL *)
        inversion H7.
      - (* rcd *)
      assert({l=l0}+{~l=l0}). apply Nat_decidable.
        assert(algo_sub D A B\/~algo_sub D A B). apply IHn. simpl in H. lia.
        destruct H8;subst. destruct H9. auto.
        right. unfold not. intros.
        inversion H9;subst. auto. auto.
        forwards: split_ord_false H4 H10 H6; auto.
        right. unfold not. intros.
        inversion H8;subst. auto. auto.
        forwards: split_ord_false H4 H10 H6; auto.
    - (* spl ord *)
    destruct H7. destruct H7.
      forwards: split_decrease_size H7. destruct H8.
      assert(algo_sub D x B\/~algo_sub D x B). apply IHn. lia.
      assert(algo_sub D x0 B\/~algo_sub D x0 B). apply IHn. lia.
      forwards: split_sub H7. apply H0. auto. destruct H12.
      assert(algo_sub D A x /\ algo_sub D A x0).
      apply sub_inversion_split_r with (t_and x x0). auto. auto.
      destruct H14.
      destruct H10. left. apply sub_transtivity with x. auto. auto.
      destruct H11. left. apply sub_transtivity with x0. auto. auto.
      right. unfold not. intros.
      forwards: sub_inversion_split_l H16 H7 H6. destruct H17;auto.
    - (* __ spl *)
    destruct H6. destruct H6.
      forwards: split_decrease_size H6. destruct H8.
      assert(algo_sub D A x\/~algo_sub D A x). apply IHn. lia.
      assert(algo_sub D A x0\/~algo_sub D A x0). apply IHn. lia.
      destruct H10. destruct H11. eauto.
      right. unfold not. intros.
      forwards: sub_inversion_split_r H12 H6. destruct H13. auto.
      right. unfold not. intros.
      forwards: sub_inversion_split_r H12 H6. destruct H13. auto.
    - (*~TWell *)
    right. unfold not. intros. forwards: algo_sub_regular H3. destruct H4. auto.
    - (*~TWell *)
    right. unfold not. intros. forwards: algo_sub_regular H3. destruct H4. auto.
    - (*~TCWell *)
    right. unfold not. intros. forwards: algo_sub_well_tctx H3. auto.
Qed.


Lemma sub_decidable:forall D A B ,
    (algo_sub D A B)\/~(algo_sub D A B).
Proof.
  intros. eapply sub_decidable_alternative. eauto.
Qed.

Lemma declarative_sub_botlike : forall D A B,
    botLike B -> TWell D A -> TWell D B -> TCWell D -> sub D B A.
Proof.
  introv Hbl. gen A.
  inductions Hbl; introv TW1 TW2 TCW; eauto.
  all: eauto using DS_trans.
Qed.

Lemma sub_toparr : forall D,
    TCWell D -> sub D t_top (t_forall t_top t_top).
Proof. intros. eauto. Qed.

#[local] Hint Resolve sub_toparr : core.

Lemma declarative_sub_toplike : forall D A B,
    topLike D B -> TWell D A -> sub D A B.
Proof with eauto using DS_trans.
  introv Htl. gen A.
  induction Htl; eauto 4; introv Lc.
  - (* arrow *)
    applys* DS_trans (t_arrow t_top t_top)...
  - (* rcd *)
    applys* DS_trans (t_rcd l t_top)...
  - (* forall *)
    pick_fresh X.
    forwards~ Htc: topLike_well_tctx (H X).
    apply DS_trans with (t_forall t_top t_top).
    apply DS_trans with t_top.
    now eauto. now eauto.
    applys DS_all. eauto. eauto.
  - applys~ DS_trans t_top.
    applys~ DS_topVar A.
    applys* declarative_sub_botlike.
    applys* TCWell_TWell H H0.
Qed.

Lemma declarative_sub_split : forall D A B B1 B2,
    spl B B1 B2 -> sub D A B1 -> sub D A B2 -> sub D A B.
Proof.
  introv Hspl Hsub1 Hsub2. gen D A.
  induction Hspl; intros; try forwards (?&?&?): split_lc Hspl.
  - (* arrow *)
    forwards: sub_well_tctx Hsub1.
    forwards(?&?): sub_regular Hsub1.
    forwards(?&?): sub_regular Hsub2.
    apply DS_trans with (t_and (t_arrow A C1) (t_arrow A C2)). auto.
    applys~ DS_trans DS_distArrow.
  - (* forall *)
    forwards: sub_well_tctx Hsub1.
    forwards(?&?): sub_regular Hsub1.
    forwards(?&?): sub_regular Hsub2.
    apply DS_trans with (t_and (t_forall A C1) (t_forall A C2)). auto.
    applys~ DS_trans DS_distAll.
    inversion H4;subst. inversion H6;subst.
    apply DS_all with (union L (union L0 (union L1 (dom D)))). auto. intros.
    assert(TCWell ((X,A)::D)). apply TCW_cons. auto. auto.
    apply uniq_push. apply TCWell_uniq. auto. auto.
    unfold open_typ_wrt_typ. simpl.
    apply H1. auto. eauto. eauto.
  - (* rcd *)
    forwards: sub_well_tctx Hsub1.
    forwards(?&?): sub_regular Hsub1.
    forwards(?&?): sub_regular Hsub2.
    apply DS_trans with (t_and (t_rcd l C1) (t_rcd l C2)). auto.
    applys~ DS_trans DS_distRcd.
  - (* split *)
    applys~ DS_and.
Qed.


(* original declarative bcd subtyping <=> algorithmic subtyping *)
Theorem declarative_sub_eqv: forall D A B,
    sub D A B <-> algo_sub D A B.
Proof.
  split; introv H.
  + induction H; eauto.
    - applys~ S_and (t_arrow A B) (t_arrow A C).
    - applys~ S_and (t_rcd l A) (t_rcd l B).
    - assert(spl (t_forall A (t_and B1 B2)) (t_forall A B1) (t_forall A B2)).
      apply TWell_lc_typ in H0.
      inversion H0;subst. unfold open_typ_wrt_typ in H4. simpl in H4.
      apply Sp_all with {}. auto. intros. eauto.
      applys~ S_and (t_forall A B1) (t_forall A B2).
    - assert (topLike D (t_forall t_top t_top)); eauto.
  + induction H; auto.
    - applys~ declarative_sub_toplike.
    - forwards(?&?): algo_sub_regular H1. eauto using DS_trans.
    - forwards(?&?): algo_sub_regular H1. eauto using DS_trans.
    - eauto.
    - applys~ declarative_sub_split H.
Qed.


Lemma botLike_equiv : forall A D,
    TCWell D -> TWell D A ->
    botLike A <-> sub D A t_bot.
Proof.
  intros. split; intros.
  applys* declarative_sub_botlike.
  inductions H1; eauto.
  forwards*: IHsub2.
  apply (declarative_sub_eqv D A B) in H1_.
  forwards*: botlike_sub.
Qed.


Lemma topLike_equiv : forall A D,
    TCWell D -> TWell D A ->
    topLike D A <-> sub D t_top A.
Proof.
  intros. splits; intros.
  applys* declarative_sub_toplike.
  apply (declarative_sub_eqv D t_top A) in H1.
  forwards*: toplike_sub.
  Unshelve. all: apply 1.
Qed.


Lemma dsub_decidable : forall D A B ,
  (sub D A B)\/~(sub D A B).
Proof.
  intros. rewrite declarative_sub_eqv.
  applys sub_decidable.
Qed.