(**
   lemmas that are about ordinary types, splittable types, proper types
*)
Require Import LibTactics.
Require Import Coq.micromega.Lia.
Require Export Infrastructure.


(******************************* proper types *********************************)
(** an alternative way to do induction on types.
It separates ordinary types and splittable types *)

Inductive R : typ -> Prop :=
| R_var : forall (X:typevar), R (t_tvar_f X)
| R_int : R t_int
| R_top : R t_top
| R_bot : R t_bot
| R_ordFun : forall A B, ord B -> R A -> R B -> R (t_arrow A B)
| R_ordAll : forall L A B,
    ( forall X , X \notin L -> ord  ( open_typ_wrt_typ B (t_tvar_f X) )  )
    -> R A ->
    ( forall X , X \notin L -> R  ( open_typ_wrt_typ B (t_tvar_f X) )  )  -> R (t_forall A B)
| R_ordRcd : forall l A, ord A -> R A -> R (t_rcd l A)
| R_spl : forall B C A, spl A B C -> R B -> R C -> R A.



(****************************** type sizes ***********************************)
(** defines size on types and proves some related
lemmas. It aims to make later proofs easier if they do
induction on the size of types *)

Lemma split_decrease_size: forall A B C,
    spl A B C -> size_typ B < size_typ A /\ size_typ C < size_typ A.
Proof with (pose proof (size_typ_min); simpl in *; try lia).
  introv H.
  induction H; simpl in *; eauto...
  pick fresh X. forwards* (?&?): H1.
  rewrite 2 size_typ_open_typ_wrt_typ_var in H3.
  rewrite 2 size_typ_open_typ_wrt_typ_var in H4.
  eauto...
Qed.

Ltac spl_size :=
  try repeat match goal with
         | [ H: spl _ _ _ |- _ ] =>
           ( lets (?&?): split_decrease_size H; clear H)
             end.

(********************************************)
(*                                          *)
(*               Ltac elia                  *)
(*  enhanced lia with split_decrease_size   *)
(*                                          *)
(********************************************)
Ltac elia :=
  try solve [pose proof (size_typ_min);
             spl_size; simpl in *;
             try repeat rewrite size_typ_open_typ_wrt_typ_var;
             try repeat rewrite size_exp_open_exp_wrt_typ_var;
             try repeat rewrite size_exp_open_exp_wrt_exp_var;
             try lia].
(* eauto with typSize lngen ? *)

Ltac indTypSize s :=
  assert (SizeInd: exists i, s < i) by eauto;
  destruct SizeInd as [i SizeInd];
  repeat match goal with | [ h : typ |- _ ] => (gen h) end;
  induction i as [|i IH]; [
    intros; match goal with | [ H : _ < 0 |- _ ] => inverts H end
  | intros ].


(* ********************************************************************** *)
(** ** Regularity of relations: type related *)

(* TODO:
I think We dont need lc_typ A since it can be implied by TWell D A
maybe we can get one regularity lemma for some relations *)

Lemma ord_lc : forall A, ord A -> lc_typ A.
Proof. introv H. induction~ H. Qed.

Lemma split_lc : forall A B C, spl A B C-> lc_typ A /\ lc_typ B /\ lc_typ C.
Proof.
  introv H.
  induction H; destruct_conj; repeat split; eauto.
Qed.

Lemma topLike_well_tctx : forall D A, topLike D A -> TCWell D.
Proof.
  introv H. induction~ H.
  pick fresh X. specialize_all X.
  forwards*: H0.
Qed.

Lemma notTopLike_well_tctx : forall D A, notTopLike D A -> TCWell D.
Proof.
  introv H. inverts~ H.
Qed.


Lemma topLike_regular : forall D A, topLike D A -> TWell D A.
Proof.
  introv H.
  induction~ H.
  pick fresh X. assert(topLike ((X, A) :: D) (B -^ X)). auto.
  apply topLike_well_tctx in H1. inversion H1;subst. eauto.
  eauto.
Qed.

Lemma notTopLike_regular : forall D A, notTopLike D A -> TWell D A.
Proof.
  introv H. inverts~ H.
Qed.

#[local] Hint Immediate topLike_well_tctx topLike_regular TWell_lc_typ notTopLike_well_tctx notTopLike_regular : core.


Lemma topLike_lc : forall D A, topLike D A -> lc_typ A.
Proof.
  intros. forwards: topLike_regular H. apply TWell_lc_typ in H0. auto.
Qed.

Lemma notTopLike_lc : forall D A, notTopLike D A -> lc_typ A.
Proof.
  intros. inverts H. eauto using TWell_lc_typ.
Qed.

Lemma botLike_lc : forall A, botLike A -> lc_typ A.
Proof.
  intros. induction* H.
Qed.

#[local] Hint Resolve topLike_lc : core.
(* get lc_typ information from existing hypotheses *)
Ltac solve_lc_1 A :=
  repeat match goal with
  | H: TWell _ ?B |- _ => match B with context[ A ] => forwards: TWell_lc_typ H; clear H end
  | H: ord _ |- _ => match type of H with context[ A ] => lets: ord_lc H; clear H end
  | H: spl _ _ _ |- _ => match type of H with context[ A ] => lets (?&?&?): split_lc H; clear H end
  | H: botLike _ |- _ => match type of H with context[ A ] => lets: botLike_lc H; clear H end
  end.

#[export] Hint Extern 1 (lc_typ ?A ) => solve_lc_1 A ; easy + (repeat solve_lc_0 A; easy): core.
#[export] Hint Extern 1 (lc_typ (?A ^-^ _) ) => solve_lc_1 A; tassumption + (repeat solve_lc_0 A; tassumption)  : core.

#[local] Hint Immediate topLike_well_tctx : core.

(* R: proper types *)
Lemma r_lc : forall A, R A -> lc_typ A.
Proof with firstorder.
  introv H. induction H; lets: split_lc...
Qed.


Lemma appDist_lc: forall A B,
    appDist A B -> lc_typ A /\ lc_typ B.
Proof with (jauto_set; eauto using notTopLike_lc).
  introv H. induction H...
Qed.

Lemma disjoint_axiom_lc: forall A B,
    disjoint_axiom A B -> lc_typ A /\ lc_typ B.
Proof. introv H. inverts~ H. Qed.

Ltac solve_lc_2 A :=
  match goal with
  | H: R _ |- _ => match type of H with context[ A ] => lets: r_lc H end
  | H: appDist _ _ |- _ => match type of H with context[ A ] => lets (?&?): appDist_lc H end
  | H: disjoint_axiom _ _ |- _ => match type of H with context[ A ] =>  lets (?&?): disjoint_axiom_lc H end
  end.

#[export] Hint Extern 1 (lc_typ ?A ) => solve_lc_2 A ; easy + (repeat solve_lc_0 A; easy): core.
#[export] Hint Extern 1 (lc_typ (?A ^-^ _) ) => solve_lc_2 A; tassumption + (repeat solve_lc_0 A; tassumption)  : core.


(******************** rename / typsubst in ord & split *************************)
#[local] Hint Resolve typsubst_typ_lc_typ : core.

(*********************************)
(* some useful lemmas            *)
(* for proving typsubst lemmas:  *)
(* lc_t_forall_exists            *)
(* typsubst_typ_spec             *)
(* typsubst_typ_open_typ_wrt_typ *)
(*********************************)

(* mimic the form of typsubst_typ_lc_typ *)
Lemma ord_rename_aux : forall A X Y,
  ord A ->
  ord ( [X ~~> (t_tvar_f Y)] A ).
Proof with (simpl in *; eauto).
  introv Ord. gen X Y. induction Ord; intros...
  - destruct (X==X0)...
  - applys~ (O_all (L \u {{X}})).
    introv Fr. forwards* Ord: H1 X0 X Y.
    rewrite typsubst_typ_open_typ_wrt_typ in Ord...
    case_eq (@eq_dec typevar EqDec_eq_of_X X0 X); intuition...
    rewrite H2 in Ord...
Qed.

Lemma split_rename_aux : forall A B C X Y,
  spl A B C->
  spl ([X ~~> (t_tvar_f Y)] A) ([X ~~> (t_tvar_f Y)] B) ([X ~~> (t_tvar_f Y)] C).
Proof with (simpl in *; eauto).
  introv Spl. gen X Y.
  induction Spl; intros...
  - applys~ (Sp_all (L \u {{X}})).
    introv Fr. forwards* Spl: H1 X0 X Y.
    rewrite 3 typsubst_typ_open_typ_wrt_typ in Spl...
    case_eq (@eq_dec typevar EqDec_eq_of_X X0 X); intuition...
    rewrite H2 in Spl...
Qed.

#[export] Hint Resolve ord_rename_aux split_rename_aux : core.

Lemma ord_rename : forall A X Y,
    X \notin (typefv_typ A) -> ord ( A -^ X ) -> ord ( A -^ Y ).
Proof with (simpl in *; eauto).
  introv Fr Lc.
  assert (H: ord [X ~~> (t_tvar_f Y)] (A -^ X) ).
  applys~ ord_rename_aux.
  simpl in H. rewrite typsubst_typ_spec in H.
  rewrite close_typ_wrt_typ_open_typ_wrt_typ in H...
Qed.

Lemma split_rename : forall A B C X Y,
    X \notin (typefv_typ A) \u (typefv_typ B) \u (typefv_typ C)->
    spl ( A -^ X ) ( B -^ X ) ( C -^ X ) ->
    spl ( A -^ Y ) ( B -^ Y ) ( C -^ Y ).
Proof with (simpl in *; eauto).
  introv Fr Lc.
  assert (H: spl [X ~~> (t_tvar_f Y)] (A -^ X) [X ~~> (t_tvar_f Y)] (B -^ X) [X ~~> (t_tvar_f Y)] (C -^ X)).
  applys~ split_rename_aux.
  simpl in H. rewrite 3 typsubst_typ_spec in H.
  rewrite 3 close_typ_wrt_typ_open_typ_wrt_typ in H...
Qed.

#[export]
Hint Extern 1 (ord ( ?A -^ ?Y )) =>
  match goal with
  | H: ord ( A -^ ?X ) |- _ => let Fr := fresh in
                               assert (Fr: X \notin (typefv_typ A)) by solve_notin;
                                 applys ord_rename Fr H
  end : core.


#[export]
Hint Extern 1 (spl ( ?A -^ ?Y ) _ _) =>
  match goal with
| H: spl ( A -^ ?X ) ( ?B -^ ?X ) ( ?C -^ ?X ) |- _ => applys split_rename H; solve_notin
end : core.

#[local] Hint Resolve ord_rename split_rename : core.

Lemma ord_forall_exists : forall X A B,
  X `notin` typefv_typ B ->
  lc_typ A ->
  ord (open_typ_wrt_typ B (t_tvar_f X)) ->
  ord (t_forall A B).
Proof with (simpl in *; eauto).
  introv Fr Lc Ord.
  applys~ O_all (typefv_typ B).
Qed.

#[export]
Hint Extern 1 =>
match goal with
| H: ord (open_typ_wrt_typ ?B (t_tvar_f ?X)) |- ord (t_forall _ ?B) =>
  applys~ ord_forall_exists H; solve_notin
end : core.

Lemma split_fv_1 : forall A B C,
    spl A B C -> (typefv_typ B) [<=] (typefv_typ A).
Proof with (subst; simpl in *).
  introv Hspl.
  induction Hspl; simpl in *; try fsetdec.
  remember ((typefv_typ A) \u (typefv_typ B) \u (typefv_typ C1)).
  pick fresh X.
  forwards~ Aux1: H1 X.
  lets* Aux2: typefv_typ_open_typ_wrt_typ_upper B (t_tvar_f X).
  lets* Aux3: typefv_typ_open_typ_wrt_typ_lower C1 (t_tvar_f X).
  assert (HS: typefv_typ C1 [<=] union (typefv_typ (t_tvar_f X)) (typefv_typ B)) by fsetdec.
  clear Aux1 Aux2 Aux3...
  fsetdec.
Qed.

Lemma split_fv_2 : forall A B C,
    spl A B C -> (typefv_typ C) [<=] (typefv_typ A).
Proof with (subst; simpl in *).
  introv Hspl.
  induction Hspl; simpl in *; try fsetdec.
  remember ((typefv_typ A) \u (typefv_typ B) \u (typefv_typ C2)).
  pick fresh X.
  forwards~ Aux1: H1 X.
  lets* Aux2: typefv_typ_open_typ_wrt_typ_upper B (t_tvar_f X).
  lets* Aux3: typefv_typ_open_typ_wrt_typ_lower C2 (t_tvar_f X).
  assert (HS: typefv_typ C2 [<=] union (typefv_typ (t_tvar_f X)) (typefv_typ B)) by fsetdec.
  clear Aux1 Aux2 Aux3...
  fsetdec.
Qed.

Lemma split_fv: forall X A B C, X `notin` [[A]]-> spl A B C -> X `notin` [[B]] /\X `notin` [[C]].
Proof.
  intros. induction H0;simpl in H;simpl;auto.
  - (* forall *)
    pick fresh X0.
    assert( X `notin` [[C1 -^ X0]] /\ X `notin` [[C2 -^ X0]]). apply H2.
    auto. assert(AtomSetImpl.Subset (typefv_typ (B -^ X0)) (typefv_typ (t_tvar_f X0)`union`  typefv_typ B)).
      apply typefv_typ_open_typ_wrt_typ_upper.
      assert(X `notin` (Metatheory.union [[t_tvar_f X0]] [[B]])). simpl in H. auto.
    eauto. destruct H3.
      assert(AtomSetImpl.Subset (typefv_typ (C1)) (typefv_typ (C1 -^ X0))).
    apply typefv_typ_open_typ_wrt_typ_lower.
      assert( X `notin` [[C1]]). eauto.
      assert(AtomSetImpl.Subset (typefv_typ (C2)) (typefv_typ (C2 -^ X0))).
    apply typefv_typ_open_typ_wrt_typ_lower.
      assert( X `notin` [[C2]]). eauto.
    simpl in H. simpl. auto.
Qed.

Lemma split_forall_exists : forall X A B B1 B2,
  X `notin` typefv_typ B ->
  lc_typ A ->
  spl (B -^ X) B1 B2->
  spl (t_forall A B) (t_forall A (close_typ_wrt_typ X B1)) (t_forall A (close_typ_wrt_typ X B2)).
Proof with (simpl in *; eauto).
  introv Fr Lc Ord.
  rewrite <- (open_typ_wrt_typ_close_typ_wrt_typ B1 X) in Ord.
  rewrite <- (open_typ_wrt_typ_close_typ_wrt_typ B2 X) in Ord.
  applys~ Sp_all.
  Unshelve. applys empty.
Qed.

Lemma subst_spl: forall A B C X Y, spl A B C -> spl (typsubst_typ (t_tvar_f X) Y A) (typsubst_typ (t_tvar_f X) Y B) (typsubst_typ (t_tvar_f X) Y C).
Proof.
  intros. induction H.
    -(* arrow *)
    simpl. assert(lc_typ(typsubst_typ (t_tvar_f X) Y A)). apply lc_subst_2. auto. auto.
    -(* forall *)
    simpl. apply Sp_all with (Metatheory.union L (Metatheory.singleton Y)). apply lc_subst_2. auto. intros.
      assert(X0 <> Y). auto.
    assert(spl [Y ~~> t_tvar_f X] (B -^ X0) [Y ~~> t_tvar_f X] (C1 -^ X0)
       [Y ~~> t_tvar_f X] (C2 -^ X0)). apply H1. auto.
    assert([Y ~~> t_tvar_f X] (B -^ X0)  = [Y ~~> t_tvar_f X] (B) ^-^  [Y ~~> t_tvar_f X] (t_tvar_f X0)).
    apply typsubst_typ_open_typ_wrt_typ_rec. auto.
    assert([Y ~~> t_tvar_f X] (C1 -^ X0)  = [Y ~~> t_tvar_f X] (C1) ^-^  [Y ~~> t_tvar_f X] (t_tvar_f X0)).
    apply typsubst_typ_open_typ_wrt_typ_rec. auto.
    assert([Y ~~> t_tvar_f X] (C2 -^ X0)  = [Y ~~> t_tvar_f X] (C2) ^-^  [Y ~~> t_tvar_f X] (t_tvar_f X0)).
    apply typsubst_typ_open_typ_wrt_typ_rec. auto.
    rewrite H5 in H4. rewrite H6 in H4. rewrite H7 in H4.
    assert([Y ~~> t_tvar_f X] (t_tvar_f X0) = (t_tvar_f X0)).
    apply typsubst_typ_fresh_eq. auto. rewrite H8 in H4. auto.
    - (* rcd *)
    simpl. auto.
    - (* and *)
    simpl. assert(lc_typ(typsubst_typ (t_tvar_f X) Y A)). apply lc_subst_2. auto.
    assert(lc_typ(typsubst_typ (t_tvar_f X) Y B)). apply lc_subst_2. auto.
    auto.
Qed.

Lemma open_spl: forall A B C X,
    spl (A -^ X) B C -> exists D1 D2, forall Y, spl (A -^ Y) (D1 -^ Y) (D2 -^ Y).
Proof.
  intros. inductions H.
    - (* arrow *)
    destruct A; inversion x. unfold open_typ_wrt_typ in x. simpl in x.
      destruct(lt_eq_lt_dec n 0). destruct s. inversion x. inversion x. inversion x.
    forwards: IHspl H3. destruct H1. destruct H1. exists (t_arrow A1 x0) (t_arrow A1 x1). subst.
    unfold open_typ_wrt_typ. simpl. intros. apply Sp_arrow.
    apply degree_typ_wrt_typ_of_lc_typ in H. apply degree_typ_wrt_typ_open_typ_wrt_typ_inv in H.
    assert(degree_typ_wrt_typ 0 (A1 -^ Y)). apply degree_typ_wrt_typ_open_typ_wrt_typ. auto. auto.
    apply lc_typ_of_degree in H2. auto. eauto.
    - (* forall *)
    destruct A;inversion x. unfold open_typ_wrt_typ in x. simpl in x.
      destruct(lt_eq_lt_dec n 0). destruct s. inversion x. inversion x. inversion x.
    subst. pick fresh X0.
    assert(open_typ_wrt_typ_rec 1 (t_tvar_f X) A2 -^ X0 = A2 -^ X0 -^ X).
    apply open_comm. auto.
    assert(exists D1 D2 : typ, forall Y : typevar, spl ((A2 -^ X0) -^ Y) (D1 -^ Y) (D2 -^ Y)).
    apply H1 with X0 X. auto. auto. destruct H3. destruct H3.
    exists (t_forall A1 (close_typ_wrt_typ X0 x0)) (t_forall A1 (close_typ_wrt_typ X0 x1)). intros.
    unfold open_typ_wrt_typ. simpl. apply Sp_all with L.
      apply degree_typ_wrt_typ_of_lc_typ in H. apply degree_typ_wrt_typ_open_typ_wrt_typ_inv in H.
    assert(degree_typ_wrt_typ 0 (A1 -^ Y)). apply degree_typ_wrt_typ_open_typ_wrt_typ. auto. auto.
    apply lc_typ_of_degree in H4. auto. intros.
    assert(open_typ_wrt_typ_rec 1 (t_tvar_f Y) A2 -^ X1 = A2 -^ X1 -^ Y).
    apply open_comm. auto. rewrite H5.
    assert(open_typ_wrt_typ_rec 1 (t_tvar_f Y) (close_typ_wrt_typ X0 x0) -^ X1 = (close_typ_wrt_typ X0 x0) -^ X1 -^ Y).
    apply open_comm. auto. rewrite H6.
    assert(open_typ_wrt_typ_rec 1 (t_tvar_f Y) (close_typ_wrt_typ X0 x1) -^ X1 = (close_typ_wrt_typ X0 x1) -^ X1 -^ Y).
    apply open_comm. auto. rewrite H7.
    assert(typsubst_typ (t_tvar_f X1) X0 x0 = (close_typ_wrt_typ X0 x0 -^ X1)).
     apply typsubst_typ_spec_rec. rewrite <- H8.
    assert(typsubst_typ (t_tvar_f X1) X0 x1 = (close_typ_wrt_typ X0 x1 -^ X1)).
     apply typsubst_typ_spec_rec. rewrite <- H9.
    assert([X0 ~~> t_tvar_f X1] (A2 -^ X0)  = [X0 ~~> t_tvar_f X1] (A2) ^-^  [X0 ~~> t_tvar_f X1] (t_tvar_f X0)).
    apply typsubst_typ_open_typ_wrt_typ_rec. auto.
    assert([X0 ~~> t_tvar_f X1] (t_tvar_f X0) = (t_tvar_f X1)). simpl. unfold " x == y ".
      destruct(EqDec_eq_of_X X0 X0). auto. contradiction.
    rewrite H11 in H10. pick fresh Z.
      assert(spl ((A2 -^ X0) -^ Z) (x0 -^ Z) (x1 -^ Z)). auto.
    assert(spl ([X0 ~~> t_tvar_f X1]((A2 -^ X0) -^ Z)) ([X0 ~~> t_tvar_f X1](x0 -^ Z)) ([X0 ~~> t_tvar_f X1](x1 -^ Z))).
      apply subst_spl. auto.
    clear H H1 H0 H2 H3 H4 H5 H6 H7 H8 H9 H11 x.
      assert([X0 ~~> t_tvar_f X1] (A2) = A2). apply typsubst_typ_fresh_eq. auto. rewrite H in H10. clear H Fr H12.
    assert([X0 ~~> t_tvar_f X1] ((A2 -^ X0) -^ Z) = [X0 ~~> t_tvar_f X1](A2 -^ X0) ^-^[X0 ~~> t_tvar_f X1] (t_tvar_f Z)).
      apply typsubst_typ_open_typ_wrt_typ_rec. auto.
    rewrite H in H13. rewrite H10 in H13. clear H H10.
    assert([X0 ~~> t_tvar_f X1] (x0 -^ Z) = [X0 ~~> t_tvar_f X1]x0 ^-^[X0 ~~> t_tvar_f X1] (t_tvar_f Z)).
      apply typsubst_typ_open_typ_wrt_typ_rec. auto.
    assert([X0 ~~> t_tvar_f X1] (x1 -^ Z) = [X0 ~~> t_tvar_f X1]x1 ^-^[X0 ~~> t_tvar_f X1] (t_tvar_f Z)).
      apply typsubst_typ_open_typ_wrt_typ_rec. auto.
    rewrite H in H13. rewrite H0 in H13. clear H H0.
    assert([X0 ~~> t_tvar_f X1] (t_tvar_f Z) = t_tvar_f Z).
      apply typsubst_typ_fresh_eq. auto. rewrite H in H13. clear H.
    assert(spl ([Z ~~> t_tvar_f Y]((A2 -^ X1) -^ Z)) ([Z ~~> t_tvar_f Y]([X0 ~~> t_tvar_f X1] (x0) -^ Z))
        ([Z ~~> t_tvar_f Y]([X0 ~~> t_tvar_f X1] (x1) -^ Z))).
    apply subst_spl. auto.
    assert([Z ~~> t_tvar_f Y] ((A2 -^ X1) -^ Z) = ([Z ~~> t_tvar_f Y] (A2 -^ X1)) ^-^ ([Z ~~> t_tvar_f Y](t_tvar_f Z))).
      apply typsubst_typ_open_typ_wrt_typ_rec. auto.
    assert([Z ~~> t_tvar_f Y] ([X0 ~~> t_tvar_f X1] (x0) -^ Z) = ([Z ~~> t_tvar_f Y] [X0 ~~> t_tvar_f X1] (x0)) ^-^ ([Z ~~> t_tvar_f Y](t_tvar_f Z))).
      apply typsubst_typ_open_typ_wrt_typ_rec. auto.
    assert([Z ~~> t_tvar_f Y] ([X0 ~~> t_tvar_f X1] (x1) -^ Z) = ([Z ~~> t_tvar_f Y] [X0 ~~> t_tvar_f X1] (x1)) ^-^ ([Z ~~> t_tvar_f Y](t_tvar_f Z))).
      apply typsubst_typ_open_typ_wrt_typ_rec. auto.
    rewrite H0 in H. rewrite H1 in H. rewrite H2 in H. clear H0 H1 H2.
      assert([Z ~~> t_tvar_f Y] (A2 -^ X1) = (A2 -^ X1)).
      apply typsubst_typ_fresh_eq.
      assert(AtomSetImpl.Subset (typefv_typ (A2 -^ X1)) (typefv_typ (t_tvar_f X1)`union`  typefv_typ A2)).
      apply typefv_typ_open_typ_wrt_typ_upper.
      assert(Z `notin` (Metatheory.union [[t_tvar_f X1]] [[A2]])). auto. eauto.
      assert([Z ~~> t_tvar_f Y] ([X0 ~~> t_tvar_f X1] (x0)) = ([X0 ~~> t_tvar_f X1] (x0))).
      apply typsubst_typ_fresh_eq. apply typsubst_typ_fresh_mutual. auto. auto.
      assert([Z ~~> t_tvar_f Y] ([X0 ~~> t_tvar_f X1] (x1)) = ([X0 ~~> t_tvar_f X1] (x1))).
      apply typsubst_typ_fresh_eq. apply typsubst_typ_fresh_mutual. auto. auto.
    rewrite H0 in H. rewrite H1 in H. rewrite H2 in H. clear H0 H1 H2.
    assert([Z ~~> t_tvar_f Y] (t_tvar_f Z) = (t_tvar_f Y)). simpl. unfold "==".
    destruct EqDec_eq_of_X. auto. contradiction. rewrite H0 in H. auto.
  - (* rcd *)
    destruct A;inversion x. unfold open_typ_wrt_typ in x. simpl in x.
      destruct(lt_eq_lt_dec n 0). destruct s. inversion x. inversion x. inversion x.
    forwards: IHspl H2. destruct H0. destruct H0. subst. exists (t_rcd l0 x0) (t_rcd l0 x1). subst.
    unfold open_typ_wrt_typ. simpl. intros. apply Sp_rcd. eauto.
  - (* and *)
    destruct A;inversion x. unfold open_typ_wrt_typ in x. simpl in x.
    destruct(lt_eq_lt_dec n 0). destruct s. inversion x. inversion x. inversion x.
    exists A1 A2. intros.
    unfold open_typ_wrt_typ. simpl. subst. apply Sp_and. apply lc_subst with X. auto.
    apply lc_subst with X. auto.
Qed.


Lemma open_spl_2: forall A B C L,
    (forall X, X `notin` L -> spl (A -^ X) (B -^ X) (C -^ X)) -> forall Y, lc_typ Y -> spl (A ^-^ Y) (B ^-^ Y) (C ^-^ Y).
Proof.
  intros. pick fresh X.
    assert(spl (A -^ X) (B -^ X) (C -^ X)). auto. clear H.
      inductions H1;auto.
  -    destruct C;inversion x. unfold open_typ_wrt_typ in x. simpl in x.
      destruct(lt_eq_lt_dec n 0). destruct s. inversion x. inversion x. inversion x.
    destruct A;inversion x0. unfold open_typ_wrt_typ in x0. simpl in x0.
      destruct(lt_eq_lt_dec n 0). destruct s. inversion x0. inversion x0. inversion x0.
    destruct B;inversion x1. unfold open_typ_wrt_typ in x1. simpl in x1.
      destruct(lt_eq_lt_dec n 0). destruct s. inversion x1. inversion x1. inversion x1.
    subst. unfold open_typ_wrt_typ. simpl.
      simpl in Fr.
      forwards*:open_typ_wrt_typ_rec_inj H5; try solve_notin.
      forwards*:open_typ_wrt_typ_rec_inj H7; try solve_notin.
      subst.
    apply Sp_arrow.
    apply degree_typ_wrt_typ_of_lc_typ in H. apply degree_typ_wrt_typ_open_typ_wrt_typ_inv in H.
    assert(degree_typ_wrt_typ 0 (B1 ^-^ Y)). apply degree_typ_wrt_typ_open_typ_wrt_typ. auto.
    apply degree_typ_wrt_typ_of_lc_typ in H0. auto.
    apply lc_typ_of_degree. auto. eauto.
  -    destruct C;inversion x. unfold open_typ_wrt_typ in x. simpl in x.
      destruct(lt_eq_lt_dec n 0). destruct s. inversion x. inversion x. inversion x.
    destruct A;inversion x0. unfold open_typ_wrt_typ in x0. simpl in x0.
      destruct(lt_eq_lt_dec n 0). destruct s. inversion x0. inversion x0. inversion x0.
    destruct B;inversion x1. unfold open_typ_wrt_typ in x1. simpl in x1.
      destruct(lt_eq_lt_dec n 0). destruct s. inversion x1. inversion x1. inversion x1.
    subst. unfold open_typ_wrt_typ. simpl.
      simpl in Fr.
      forwards*:open_typ_wrt_typ_rec_inj H6; try solve_notin.
      forwards*:open_typ_wrt_typ_rec_inj H8; try solve_notin.
      subst.
    apply Sp_all with (union L0 (union L (singleton X))).
    apply degree_typ_wrt_typ_of_lc_typ in H. apply degree_typ_wrt_typ_open_typ_wrt_typ_inv in H.
    assert(degree_typ_wrt_typ 0 (B1 ^-^ Y)). apply degree_typ_wrt_typ_open_typ_wrt_typ. auto.
    apply degree_typ_wrt_typ_of_lc_typ in H0. auto.
    apply lc_typ_of_degree. auto. intros.
    assert(open_typ_wrt_typ_rec 1 Y A2 -^ X0 = A2 -^ X0 ^-^ Y).
    apply open_comm_2. auto. auto. rewrite H4.
    assert(open_typ_wrt_typ_rec 1 Y B2 -^ X0 = B2 -^ X0 ^-^ Y).
    apply open_comm_2. auto. auto. rewrite H5.
    assert(open_typ_wrt_typ_rec 1 Y C4 -^ X0 = C4 -^ X0 ^-^ Y).
    apply open_comm_2. auto. auto. rewrite H7.
    apply H1 with X0 X. auto. auto.
    assert(X<>X0). auto.
    assert(AtomSetImpl.Subset (typefv_typ (A2 -^ X0)) (typefv_typ (t_tvar_f X0)`union`  typefv_typ A2)).
    apply typefv_typ_open_typ_wrt_typ_upper.
    assert(X `notin` (Metatheory.union [[t_tvar_f X0]] [[A2]])). auto.
    assert(AtomSetImpl.Subset (typefv_typ (B2 -^ X0)) (typefv_typ (t_tvar_f X0)`union`  typefv_typ B2)).
    apply typefv_typ_open_typ_wrt_typ_upper.
    assert(X `notin` (Metatheory.union [[t_tvar_f X0]] [[B2]])). auto.
    assert(AtomSetImpl.Subset (typefv_typ (C4 -^ X0)) (typefv_typ (t_tvar_f X0)`union`  typefv_typ C4)).
    apply typefv_typ_open_typ_wrt_typ_upper.
    assert(X `notin` (Metatheory.union [[t_tvar_f X0]] [[C4]])). auto.
    assert(X `notin` [[A2 -^ X0]]). auto.
    assert(X `notin` [[B2 -^ X0]]). auto.
    assert(X `notin` [[C4 -^ X0]]). auto. auto.
    apply open_comm. auto.
    apply open_comm. auto.
    apply open_comm. auto.
  -  destruct C;inversion x. unfold open_typ_wrt_typ in x. simpl in x.
      destruct(lt_eq_lt_dec n 0). destruct s. inversion x. inversion x. inversion x.
    destruct A;inversion x0. unfold open_typ_wrt_typ in x0. simpl in x0.
      destruct(lt_eq_lt_dec n 0). destruct s. inversion x0. inversion x0. inversion x0.
    destruct B;inversion x1. unfold open_typ_wrt_typ in x1. simpl in x1.
      destruct(lt_eq_lt_dec n 0). destruct s. inversion x1. inversion x1. inversion x1.
    subst. unfold open_typ_wrt_typ. simpl.
      simpl in Fr. eauto.
  -  destruct A;inversion x. unfold open_typ_wrt_typ in x. simpl in x.
      destruct(lt_eq_lt_dec n 0). destruct s. inversion x. inversion x. inversion x.
      simpl in Fr.
      forwards*:open_typ_wrt_typ_rec_inj H3; try solve_notin.
      forwards*:open_typ_wrt_typ_rec_inj H4; try solve_notin. subst.
    apply Sp_and.
    apply degree_typ_wrt_typ_of_lc_typ in H. apply degree_typ_wrt_typ_open_typ_wrt_typ_inv in H.
    assert(degree_typ_wrt_typ 0 (A1 ^-^ Y)). apply degree_typ_wrt_typ_open_typ_wrt_typ. auto.
    apply degree_typ_wrt_typ_of_lc_typ in H0. auto.
    apply lc_typ_of_degree. auto.
    apply degree_typ_wrt_typ_of_lc_typ in H1. apply degree_typ_wrt_typ_open_typ_wrt_typ_inv in H1.
    assert(degree_typ_wrt_typ 0 (A2 ^-^ Y)). apply degree_typ_wrt_typ_open_typ_wrt_typ. auto.
    apply degree_typ_wrt_typ_of_lc_typ in H0. auto.
    apply lc_typ_of_degree. auto.
Qed.

Lemma open_spl_all: forall A B C X, spl (A -^ X) B C -> exists D1 D2, forall Y, lc_typ Y -> spl (A ^-^ Y) (D1 ^-^ Y) (D2 ^-^ Y).
Proof.
  intros. apply open_spl in H. destruct H. destruct H.
    exists x x0. apply open_spl_2 with {}. auto.
Qed.

#[export]
Hint Extern 2 =>
match goal with
| H: spl (?B -^ ?X) ?B1 ?B2 |-
  spl (t_forall ?A ?B) (t_forall ?A (close_typ_wrt_typ ?X ?B1)) (t_forall ?A (close_typ_wrt_typ ?X ?B2)) =>
  applys split_forall_exists H; solve_notin
| H: spl (?B -^ ?X) _ _ |-
  spl (t_forall ?A ?B) _ _ =>
  applys split_forall_exists H; solve_notin
end : core.

#[export] Hint Constructors R : core.

Lemma proper_rename_aux : forall A X Y,
  R A ->
  R [X~~> (t_tvar_f Y)] A.
Proof with (simpl in *; eauto).
  introv Hr. gen X Y.
  induction Hr; intros...
  - destruct (X==X0)...
  - applys~ (R_ordAll (L \u {{X}}) ).
    + (* goal1: ord *)
      intros X0 Fr0. forwards* Ord0: H.
      eapply (ord_rename_aux _ X Y) in Ord0.
      rewrite typsubst_typ_open_typ_wrt_typ in Ord0...
      case_eq (@eq_dec typevar EqDec_eq_of_X X0 X); intuition...
      rewrite H2 in Ord0...
    + (* goal2: r *)
      intros X0 Fr0. forwards* R0: H1 X0 X Y.
      rewrite typsubst_typ_open_typ_wrt_typ in R0...
      case_eq (@eq_dec typevar EqDec_eq_of_X X0 X); intuition...
      rewrite H2 in R0...
Qed.

Lemma proper_rename : forall A X Y,
    X \notin (typefv_typ A) -> R ( A -^ X ) -> R ( A -^ Y ).
Proof with (simpl in *; eauto).
  introv Fr Lc.
  assert (H: R [X ~~> (t_tvar_f Y)] (A -^ X) ).
  applys~ proper_rename_aux.
  simpl in H. rewrite typsubst_typ_spec in H.
  rewrite close_typ_wrt_typ_open_typ_wrt_typ in H...
Qed.

(*********************** botlike toplike subst ********************************)

Lemma botLike_subst_2: forall X Y A, botLike A -> botLike (typsubst_typ (t_tvar_f Y) X A).
Proof. intros. induction H; simpl; auto. Qed.

Lemma TCW_binds_botLike_2: forall A0 C D E X Y X1, TCWell (E ++ [(X,C)] ++ D) -> binds X1 A0 (E ++ [(X,C)] ++ D) -> botLike A0
-> X <> X1-> botLike (typsubst_typ (t_tvar_f Y) X A0) /\binds X1 (typsubst_typ (t_tvar_f Y) X A0) ((map (typsubst_typ (t_tvar_f Y) X) E) ++ [(Y,C)] ++ D).
Proof.
  intros. split.
    apply botLike_subst_2. auto.
    clear H1.
    apply binds_app_1 in H0. destruct H0. auto.
    apply binds_app_1 in H0. destruct H0. unfold binds in H0. simpl in H0. destruct H0;subst.
    inversion H0;subst. contradiction. contradiction.
    assert(TCWell ([(X,C)]++ D)) by eauto. clear H.
    assert(X `notin` (typefv_typ_range D)).
    inversion H1; subst. inversion H7;subst. clear H0 H1 H2 H4 H6 H7.
    induction D. simpl. auto. destruct a. simpl.
    inversion H5; subst.
    assert(X `notin` [[t]]). apply TW_not_in with D. auto. auto. auto.
    assert(binds X1 ([X ~~> t_tvar_f Y] (A0)) (map (typsubst_typ (t_tvar_f Y) X) D)).
    clear H H1 H2. induction D;simpl. auto.
    destruct a. apply binds_cons_iff in H0. destruct H0. destruct H;subst.
    auto. auto.
    assert(map (typsubst_typ (t_tvar_f Y) X) D = D). apply no_effect_subst. auto.
    rewrite H4 in H3. auto.
Qed.


Lemma topLike_subst_alternative:forall n X Y (A C:typ) (D E:tctx),
size_typ A  <= n
-> X `notin`  [[A]]
-> Y `notin` (Metatheory.union (dom D) (dom E))
-> topLike (E ++ [(X , C)] ++ D) (A -^ X)
-> topLike ((map (typsubst_typ (t_tvar_f Y) X) E) ++ [(Y ,C)] ++ D) (A -^ Y).
Proof.
  intros n. induction n. intros. destruct A;inversion H.
  intros. inductions H2.
   - (* top *)
    destruct A;inversion x. unfold open_typ_wrt_typ in x. simpl in x.
      destruct(lt_eq_lt_dec n0 0). destruct s. inversion x. inversion x. inversion x.
    unfold open_typ_wrt_typ. simpl.
      assert(TCWell ((map (typsubst_typ (t_tvar_f Y) X)E) ++ [(Y , C)] ++ D)). apply TCW_subst. auto. auto. auto.
   - (* and *)
    destruct A;inversion x. unfold open_typ_wrt_typ in x. simpl in x.
      destruct(lt_eq_lt_dec n0 0). destruct s. inversion x. inversion x. inversion x.
    unfold open_typ_wrt_typ. simpl. subst. simpl in H0. simpl in H.
    assert(topLike (map (typsubst_typ (t_tvar_f Y) X) E ++ (Y, C) :: D) (open_typ_wrt_typ_rec 0 (t_tvar_f Y) A1)).
    apply IHn. lia. auto. auto. auto.
    assert(topLike (map (typsubst_typ (t_tvar_f Y) X) E ++ (Y, C) :: D) (open_typ_wrt_typ_rec 0 (t_tvar_f Y) A2)).
    apply IHn. lia. auto. auto. auto. auto.
   - (* arrow *)
    destruct A;inversion x. unfold open_typ_wrt_typ in x. simpl in x.
      destruct(lt_eq_lt_dec n0 0). destruct s. inversion x. inversion x. inversion x.
    unfold open_typ_wrt_typ. simpl. subst. simpl in H0. simpl in H.
    assert(topLike (map (typsubst_typ (t_tvar_f Y) X) E ++ (Y, C) :: D) (open_typ_wrt_typ_rec 0 (t_tvar_f Y) A2)).
    apply IHn. lia. auto. auto. auto.
    assert(TWell (map (typsubst_typ (t_tvar_f Y) X) E ++ (Y, C) :: D) (open_typ_wrt_typ_rec 0 (t_tvar_f Y) A1)).
    apply TW_subst. auto. auto. apply topLike_well_tctx in H2. auto. auto. auto.
   - (* rcd *)
    destruct A;inversion x. unfold open_typ_wrt_typ in x. simpl in x.
      destruct(lt_eq_lt_dec n0 0). destruct s. inversion x. inversion x. inversion x.
    unfold open_typ_wrt_typ. simpl. subst. simpl in H0. simpl in H.
    assert(topLike (map (typsubst_typ (t_tvar_f Y) X) E ++ (Y, C) :: D) (open_typ_wrt_typ_rec 0 (t_tvar_f Y) A)).
    apply IHn. lia. auto. auto. auto. auto.
   - (* forall *)
    destruct A;inversion x. unfold open_typ_wrt_typ in x. simpl in x.
      destruct(lt_eq_lt_dec n0 0). destruct s. inversion x. inversion x. inversion x.
    unfold open_typ_wrt_typ. simpl. subst. simpl in H0. simpl in H.
      apply TL_all with (union L (union (singleton X) (singleton Y))). intros.
    assert((open_typ_wrt_typ_rec 1 (t_tvar_f Y) A2 -^ X0) = (A2 -^ X0) -^ Y).
      apply open_comm. auto. rewrite H5.
    assert((X0, (A1 -^ Y)) :: map (typsubst_typ (t_tvar_f Y) X) E
      = map (typsubst_typ (t_tvar_f Y) X) ((X0, (A1 -^ X)):: E) ).
    simpl.
    assert([X ~~> t_tvar_f Y] (A1 -^ X)  = [X ~~> t_tvar_f Y] (A1) ^-^  [X ~~> t_tvar_f Y] (t_tvar_f X)).
    apply typsubst_typ_open_typ_wrt_typ_rec. auto.
    rewrite H6.
    assert([X ~~> t_tvar_f Y] A1 = A1).
    apply typsubst_typ_fresh_eq. simpl in H0. auto.
    assert([X ~~> t_tvar_f Y] (t_tvar_f X) = t_tvar_f Y ).
    simpl. unfold "==". destruct(EqDec_eq_of_X X X);subst;auto.
    contradiction.
    rewrite H7. rewrite H8. auto.
    assert(topLike  (map (typsubst_typ (t_tvar_f Y) X) ((X0, A1 -^ X) :: E) ++ [(Y, C)] ++ D)
  ((A2 -^ X0) -^ Y)).
    apply IHn. rewrite size_typ_open_typ_wrt_typ_var. lia.
    assert(AtomSetImpl.Subset (typefv_typ (A2 -^ X0)) (typefv_typ (t_tvar_f X0) `union` typefv_typ A2)).
      apply typefv_typ_open_typ_wrt_typ_rec_upper_mutual.
    assert(X `notin` (Metatheory.union [[t_tvar_f X0]] [[A2]])). auto.
    auto. simpl. auto.
    assert((open_typ_wrt_typ_rec 1 (t_tvar_f X) A2 -^ X0) = (A2 -^ X0) -^ X).
      apply open_comm. auto. rewrite <- H7. apply H2. auto.
    rewrite <- H6 in H7. auto.
   - (* var_f *)
    destruct A;inversion x. unfold open_typ_wrt_typ in x. simpl in x.
      destruct(lt_eq_lt_dec n0 0). destruct s. inversion x. inversion x;subst.
    unfold open_typ_wrt_typ. simpl.
      assert(A0 = C). eapply binds_unique. apply H4. eauto. apply TCWell_uniq. auto. subst.
      assert(TCWell ((map (typsubst_typ (t_tvar_f Y) X)E) ++ [(Y , C)] ++ D)). apply TCW_subst. auto. auto.
    apply TL_var with C. auto. auto. auto.
      inversion x. subst. simpl in H0.
    unfold open_typ_wrt_typ. simpl.
    assert(botLike (typsubst_typ (t_tvar_f Y) X A0) /\binds X1 (typsubst_typ (t_tvar_f Y) X A0) ((map (typsubst_typ (t_tvar_f Y) X) E) ++ [(Y,C)] ++ D)).
    apply TCW_binds_botLike_2. auto. auto. auto. auto.
    destruct H5.
    apply TL_var with (typsubst_typ (t_tvar_f Y) X A0).
    assert(TCWell ((map (typsubst_typ (t_tvar_f Y) X)E) ++ [(Y , C)] ++ D)).
    apply TCW_subst. auto. auto. auto. auto. auto.
Qed.

Lemma topLike_subst:forall X Y (A C:typ) (D E:tctx),
    X `notin`  [[A]]
    -> Y `notin` (Metatheory.union (dom D) (dom E))
    -> topLike (E ++ [(X , C)] ++ D) (A -^ X)
    -> topLike ((map (typsubst_typ (t_tvar_f Y) X) E) ++ [(Y ,C)] ++ D) (A -^ Y).
Proof.
  intros. forwards: topLike_subst_alternative H H0 H1. eauto. auto.
Qed.

Lemma topLike_simpl_subst:forall X Y (A C:typ) (D:tctx),
    X `notin`  [[A]]
    -> Y `notin` (dom D)
    -> topLike ([(X ,C)] ++ D) (A -^ X)
    -> topLike ([(Y ,C)] ++ D) (A -^ Y).
Proof.
  intros.
    assert(nil ++ [(X ,C)] ++ D = [(X ,C)] ++ D ). auto.
    rewrite <- H2 in H1.
  apply topLike_subst with X Y A C D nil in H1. auto. auto. auto.
Qed.

Lemma botLike_decidable_alternative: forall n A,
    size_typ A <= n -> botLike A\/~botLike A.
Proof.
  intros n. induction n;intros. destruct A;inversion H.
    destruct A; try solve [right;unfold not;intros;inversion H0].
  -(* bot *)
    auto.
  -(* and *)
  simpl in H.
  assert(lc_typ A1\/~lc_typ A1). apply lc_decidable.
  assert(lc_typ A2\/~lc_typ A2). apply lc_decidable.
  destruct H0. destruct H1.
  assert(botLike A1\/~botLike A1). apply IHn. lia.
  assert(botLike A2\/~botLike A2). apply IHn. lia. destruct H2. jauto. destruct H3. auto.
    right. unfold not. intros. inversion H4;subst;auto.
    right. unfold not. intros. inversion H2;subst;auto.
    right. unfold not. intros. inversion H2;subst;auto.
Qed.

Lemma botLike_decidable: forall A,
  botLike A\/~botLike A.
Proof.
  intros. eapply botLike_decidable_alternative. eauto.
Qed.

Lemma toplike_decidable_alternative : forall n D A,
    size_typ A<= n -> topLike D A \/ ~topLike D A.
Proof with jauto.
  intros n. induction n. intros. destruct A;inversion H.
    intros. assert(TCWell D\/~TCWell D). apply TCWell_decidable. destruct H0.
      assert(TWell D A\/~TWell D A). apply TWell_decidable. destruct H1.
      destruct A;auto.
      -(* var_b *)
       inversion H1.
      -(* var_f *)
      inversion H1;subst. assert(botLike A\/~botLike A). apply botLike_decidable. destruct H2. eauto.
      right. unfold not. intros. inversion H3;subst. apply TCWell_uniq in H6. forwards: binds_unique H4 H7 H6 . subst. auto.
      -(* int *)
      right. unfold not. intros. inversion H2.
      -(* bot *)
      right. unfold not. intros. inversion H2.
      -(* forall *)
      pick fresh X. assert(topLike ((X, A1) :: D) (A2 -^ X)\/~topLike ((X, A1) :: D) (A2 -^ X)).
      apply IHn. rewrite size_typ_open_typ_wrt_typ_var. simpl in H. lia.
      destruct H2. left. apply TL_all with (dom D). intros.
        apply topLike_simpl_subst with X. auto. auto. auto.
      right. unfold not. intros. inversion H3;subst. pick fresh Y.
        assert(topLike ((Y, A1) :: D) (A2 -^ Y)). auto.
      assert(topLike ((X, A1) :: D) (A2 -^ X)). apply topLike_simpl_subst with Y. auto. auto. auto. auto.
      -(* arrow *)
      assert(topLike D A2\/~topLike D A2). apply IHn. simpl in H. lia. destruct H2. auto. right. unfold not.
        intros. inversion H3;subst. auto.
      -(* and *)
      assert(topLike D A1\/~topLike D A1). apply IHn. simpl in H. lia. destruct H2.
      assert(topLike D A2\/~topLike D A2). apply IHn. simpl in H. lia. destruct H3.
        auto.
      right. unfold not. intros. inversion H4;subst. auto.
      right. unfold not. intros. inversion H3;subst. auto.
      -(* rcd *)
      assert(topLike D A\/~topLike D A). apply IHn. simpl in H. lia. destruct H2. auto. right. unfold not.
        intros. inversion H3;subst. auto.
      -(* ~TWell *)
      right. unfold not. intros. apply topLike_regular in H2. auto.
      -(* ~TCWell *)
      right. unfold not. intros. apply topLike_well_tctx in H1. auto.
Qed.

Lemma toplike_decidable : forall D A,
    topLike D A \/ ~topLike D A.
Proof with jauto.
  intros. eapply toplike_decidable_alternative. eauto.
Qed.


(************************** weakening ********************************)

Lemma topLike_weakening: forall y X D E A,
    TWell D X ->
    y # (E ++ D) ->
    topLike (E ++ D) A->
    topLike (E ++ [(y, X)] ++ D) A.
Proof.
  intros. remember (E ++ D). gen E.
  induction H1; eauto; intros; subst;
    try solve [eauto using TWell_weakening].
  apply TL_all with (union (singleton y) L). intros. rewrite_env(((X0, A) :: E) ++ y ~ X ++ D). apply H2. auto.
  assert(y<>X0). auto. simpl. auto. auto.
Qed.

Lemma notTopLike_weakening_full : forall D E F A,
    notTopLike (D ++ F) A ->
    TCWell (D ++ E ++ F) ->
    notTopLike (D ++ E ++ F) A.
Proof.
  intros. inverts H. 
  constructor~.
  remember (D ++ F). gen D.
  inductions H2; intros; substs; eauto; solve_false.
  - inverts H.
  - inverts H.
  - inverts H2.
    forwards: binds_weaken E H.
    forwards~: binds_unique H6 H2.
    substs.
    solve_false.
  - assert ( ~ topLike (D0 ++ F) A) by eauto.
    forwards~: IHTWell; simpl_env in *. inverts H; solve_false.
  - inverts H.
    assert (~ topLike (D0 ++ F) B) by eauto.
    forwards~: IHTWell2.
  - assert (topLike (D0 ++ F) A \/ ~ topLike (D0 ++ F) A) by applys toplike_decidable.
    destruct H2.
    + assert (topLike (D0 ++ F) B \/ ~ topLike (D0 ++ F) B) by applys toplike_decidable.
      destruct H4.
      * solve_false.
      * forwards~: IHTWell2.
        inverts H. solve_false.
    + forwards~: IHTWell1.
      inverts H.
      solve_false.
  - inverts H5.
    instantiate_cofinites.
    assert (~ topLike ((x, A) :: D0 ++ F) (B -^ x)).
    { 
      intros contra.
      assert (topLike (D0 ++ F) (t_forall A B)).
      pick fresh y and apply TL_all.
      rewrite_env (nil ++ x ~ A ++ (D0 ++ F)) in contra.
      forwards~: topLike_subst y contra.
      solve_false.
    }
    forwards*: H0 ((x, A) :: D0).
Qed.


Lemma notTopLike_weakening: forall D A,
    notTopLike nil A -> TCWell D ->
    notTopLike D A.
Proof.
  introv TL TC.
  rewrite_env (nil++D++nil).
  applys~ notTopLike_weakening_full.
  simpl_env. auto.
Qed.


#[local] Hint Immediate topLike_weakening notTopLike_weakening : core.

#[export] Hint Extern 1 (notTopLike ?D ?A) =>
match goal with | H: notTopLike nil A |- _ => applys notTopLike_weakening H end : core.


Lemma algo_sub_weakening: forall y X D E A B,
    TWell D X ->
    y # (E ++ D) ->
    algo_sub (E ++ D) A B->
    algo_sub (E ++ [(y, X)] ++ D) A B.
Proof.
  intros. remember (E ++ D). gen E.
  induction H1; eauto; intros; subst;
    try solve [eauto using TWell_weakening].
  apply S_all with (union (singleton y) L). auto. auto.
  intros.
  rewrite_env(((X0, B1) :: E) ++ y ~ X ++ D). apply H4. auto.
  assert(y<>X0). auto. simpl. auto. auto.
Qed.

#[export] Hint Immediate algo_sub_weakening : core.


(* disjoint *)

Lemma disjoint_weakening: forall y X D E A B,
    TWell D X ->
    y # (E ++ D) ->
    disjoint (E ++ D) A B ->
    disjoint (E ++ [(y, X)] ++ D) A B.
Proof.
  intros. remember (E ++ D). gen E.
  induction H1; intros; subst.
  6: { pick fresh x and apply D_all. eauto. eauto.
       forwards*: H4 x ((x, t_and A1 A2) :: E). solve_notin. }
  all: eauto.
Qed.


#[export] Hint Immediate disjoint_weakening : core.


(************************* TWell **********************************************)

Lemma TWell_appDist: forall D A B, TWell D A -> appDist A B -> TWell D B.
Proof.
  intros. induction~ H0;
  inverts H;
  forwards~: IHappDist1;
  forwards*: IHappDist2.

  inverts H.
  inverts H0.
  pick fresh X and apply TW_all.
  eauto.
  forwards~: H7 X.
  forwards~: H8 X.

  unfold open_typ_wrt_typ. simpls. constructor;
  rewrite_env (nil ++ (X ~ (B1 & B2)) ++ D);
  applys* TWell_bind_weakening.
Qed.

Lemma TWell_appDist_2: forall D A B, TWell D B -> appDist A B -> TWell D A.
Proof.
  intros. induction H0; eauto.
  inverts H.
  forwards*: IHappDist1.

  inverts H.
  forwards*: IHappDist1.

  inverts H.
  forwards*: IHappDist1.
  pick fresh X and apply TW_all; auto.
  instantiate_cofinites_with X.
  unfold open_typ_wrt_typ in H4. simpls.
  inverts H4.
  rewrite_env (nil ++ (X ~ B1) ++ D);
  applys* TWell_bind_weakening.

  forwards*: IHappDist2.
  pick fresh X and apply TW_all; auto.
  instantiate_cofinites_with X.
  unfold open_typ_wrt_typ in H4. simpls.
  inverts H4.
  rewrite_env (nil ++ (X ~ B2) ++ D);
  applys* TWell_bind_weakening.
Qed.

Lemma TWell_spl : forall A B C D,
    TWell D A -> spl A B C -> (TWell D B) /\ (TWell D C).
Proof with eauto.
  intros. gen D. induction H0; intros; eauto.
  - inverts H1.
    forwards*: IHspl.
  - inverts H2.
    splits.
    pick fresh x and apply TW_all...
    forwards*: H7 x.
    forwards*: H1 H2.
    pick fresh x and apply TW_all...
    forwards*: H7 x.
    forwards*: H1 H2.
  - inverts H.
    forwards*: IHspl.
Qed.


Lemma TWell_spl_2 : forall A B C D,
    spl A B C -> TWell D B -> TWell D C -> TWell D A.
Proof with eauto.
  introv Hs Hw1 Hw2. gen D.
  induction Hs; intros...
Qed.

#[export] Hint Immediate TWell_spl_2 : core.

#[export] Hint Extern 1 (TWell ?D ?A) =>
match goal with
| H: spl A _ _ |- _ => applys TWell_spl_2 H; eassumption
| H: spl _ A _ |- _ => lets (?&?): TWell_spl H; eassumption
| H: spl _ _ A |- _ => lets (?&?): TWell_spl H; eassumption
| H: appDist _ A |- _ => applys TWell_appDist H
| H: appDist A _ |- _ => applys TWell_appDist_2 H
end : core.

(******************************************************************************)
Lemma algo_sub_regular : forall D A B, algo_sub D A B -> TWell D A/\TWell D B.
Proof.
  introv H.
  induction~ H;split*.
  destruct IHalgo_sub. apply TW_all with L. auto. intros. apply H2 in H5.
  destruct H5. rewrite_env(nil ++ [(X,A1)] ++ D). apply TWell_bind_weakening with B1. auto.
  destruct IHalgo_sub. apply TW_all with L. auto. intros. apply H2 in H5.
  destruct H5. auto.
Qed.

Lemma algo_sub_lc : forall D A B, algo_sub D A B -> lc_typ A /\ lc_typ B.
Proof.
  introv H.
  apply algo_sub_regular in H. destruct H. apply TWell_lc_typ in H.
  apply TWell_lc_typ in H0. auto.
Qed.

Lemma sub_regular : forall D A B, sub D A B -> TWell D A /\ TWell D B.
Proof.
  introv H.
  induction~ H;split*.
  destruct IHsub. apply TW_all with L. auto. intros. apply H1 in H4.
  destruct H4. rewrite_env(nil ++ [(X,A1)] ++ D). apply TWell_bind_weakening with A2. auto.
  destruct IHsub. apply TW_all with L. auto. intros. apply H1 in H4.
  destruct H4. auto.
Qed.


Lemma sub_lc : forall D A B, sub D A B -> lc_typ A /\ lc_typ B.
Proof.
  introv H.
  forwards*(?&?): sub_regular H.
Qed.


Lemma subsub_lc : forall A B, subsub A B -> lc_typ A /\ lc_typ B.
Proof.
  introv H.
  induction H; split*.
Qed.


(* disjointness regularity lemmas depend on TWell_spl_2 *)

Lemma disjoint_regular: forall D A B,
    disjoint D A B -> TWell D A /\ TWell D B.
Proof.
  intros. induction* H.
  - (* forall *)
    split. apply TW_all with L. auto. intros. apply H2 in H3.
    destruct H3. rewrite_env(nil ++ [(X,A1)] ++ D). apply TWell_bind_weakening with (t_and A1 A2). auto.
    apply TW_all with L. auto. intros. apply H2 in H3.
    destruct H3. rewrite_env(nil ++ [(X,A2)] ++ D). apply TWell_bind_weakening with (t_and A1 A2). auto.
  - (* var L *)
    split. eauto. apply algo_sub_regular in H0. auto.
  - (* var R *)
    split. apply algo_sub_regular in H0. auto. eauto.
Qed.

Lemma disjoint_lc: forall D A B,
    disjoint D A B -> lc_typ A /\ lc_typ B.
Proof. intros. forwards*: disjoint_regular H. Qed.

Lemma algo_sub_well_tctx : forall D A B, algo_sub D A B -> TCWell D.
Proof. introv H. induction* H. Qed.

Lemma sub_well_tctx : forall D A B, sub D A B -> TCWell D.
Proof. introv H. induction~ H. Qed.

#[export] Hint Immediate algo_sub_well_tctx sub_well_tctx : core.


Lemma disjoint_well_tctx: forall D A B,
    disjoint D A B -> TCWell D.
Proof.
  introv H. induction* H.
  - (* forall *)
    instantiate_cofinites. eauto.
Qed.


#[export] Hint Immediate disjoint_well_tctx : core.



(* get twell information from existing hypotheses *)

Ltac solve_twell_1 A :=
  repeat match goal with
  | H: topLike _ _ |- _ => match type of H with context[ A ] => lets: topLike_well_tctx H; lets: topLike_regular H end; clear H
  | H: notTopLike _ _ |- _ => match type of H with context[ A ] => lets: notTopLike_well_tctx H; lets: notTopLike_regular H end; clear H
  | H: algo_sub _ _ _ |- _ => match type of H with context[ A ] => lets (?&?): algo_sub_regular H; lets : algo_sub_well_tctx H end; clear H
  | H: sub _ _ _ |- _ => match type of H with context[ A ] => lets (?&?): sub_regular H; lets : sub_well_tctx H end; clear H
  | H: disjoint _ _ _ |- _ => match type of H with context[ A ] => lets (?&?): disjoint_regular H; lets : disjoint_well_tctx H end; clear H
  (* | H: subsub _ _ _ |- _ => match type of H with context[ A ] => lets (?&?): subsub_regular H; lets : subsub_well_tctx H end; clear H *)
  end.

#[export] Hint Extern 1 (TCWell ?D ) => progress solve_twell_1 D; easy + (repeat solve_tcwell_0 D; easy) : core.
#[export] Hint Extern 1 (TWell ?D ?A ) => progress (solve_twell_1 A; repeat solve_twell_0 A); easy : core.
#[export] Hint Extern 1 (TWell ?D ?A -^ _ ) => progress (solve_twell_1 A; solve_twell_0 A) : core.

#[export] Hint Extern 1 (lc_typ ?A ) => solve_twell_1 A ; solve_lc_1 A; repeat solve_lc_0 A; easy : core.
#[export] Hint Extern 1 (lc_typ (?A ^-^ _) ) =>  solve_twell_1 A ; solve_lc_1 A; solve_lc_0 A; tassumption : core.


(* get all lc_typ information from existing hypotheses *)
Ltac get_all_lc :=
  repeat match goal with
         | H: ord _ |- _ => lets: ord_lc H; clear H
         | H: topLike _ _ |- _ => lets: topLike_lc H; clear H
         | H: notTopLike _ _ |- _ => lets: notTopLike_lc H; clear H
         | H: algo_sub _ _ _ |- _ => lets (?&?): algo_sub_lc H; clear H
         | H: sub _ _ _ |- _ => lets (?&?): sub_lc H; clear H
         | H: appDist _ _ |- _ => lets (?&?): appDist_lc H; clear H
         | H: disjoint_axiom _ _ |- _ => lets (?&?): disjoint_axiom_lc H; clear H
         | H: disjoint _ _ _ |- _ => lets (?&?): disjoint_lc H; clear H
         | H: R _ |- _ => lets: r_lc H; clear H
         | H: TWell _ _ |- _ => lets: TWell_lc_typ H; clear H
         end.


(*
Lemma TWell_appDist_arr : forall D A B1 B2,
    TWell D A ->
    appDist A (t_arrow B1 B2) ->
    TWell D B2.
Proof.
  intros. gen B1 B2. inductions H; intros; try solve [inverts* H0].
  - inverts~ H1.
  - inverts H1.
    forwards*: IHTWell1 H5.
  - inverts H2.
Qed.

Lemma TWell_appDist_rcd : forall D A l B,
    TWell D A ->
    appDist A (t_rcd l B) ->
    TWell D B.
Proof.
  intros. gen l B. inductions H; intros; try solve [inverts* H0].
  - inverts~ H1.
  - inverts H1.
    forwards*: IHTWell1 H5.
  - inverts H2.
Qed.


Lemma TWell_appDist_forall : forall D A B1 B2,
    TWell D A ->
    appDist A (t_forall B1 B2) ->
    (exists L, forall X : atom, X `notin` L -> TWell ((X, B1) :: D) (B2 -^ X)).
Proof.
  intros. gen B1 B2. inductions H; intros; try solve [inverts* H0].
  - inverts~ H1.
  - inverts H1.
    forwards*: IHTWell1 H5.
    forwards*: IHTWell2 H7.
    forwards (D1&?): H1.
    forwards (D2&?): H2.
    exists (D1 `union` D2). intros X HF. specialize_all X.
    rewrite_env (nil ++ X ~ B0 ++ D) in H3.
    forwards*: TWell_bind_weakening H3.
    rewrite_env (nil ++ X ~ B3 ++ D) in H4.
    forwards*: TWell_bind_weakening H4.
    assert (t_and C1 C2 -^ X = t_and (C1 -^ X) (C2 -^ X)) by eauto.
    rewrite_env (nil ++ X ~ (t_and B0 B3) ++ D).
    applys TW_and H6 H8.
  - inverts H2. exists. applys H0.
    Unshelve. applys [[B1]].
Qed.

Lemma TWell_appDist_and : forall D A B1 B2,
    TWell D A ->
    appDist A (t_and B1 B2) ->
    TWell D B1 /\ TWell D B2.
Proof.
  intros. gen B1 B2. inductions H; intros; try solve [inverts* H0].
  - inverts~ H1.
  - inverts H1.
  - inverts H2.
Qed.
 *)
(*
Lemma TWell_arr : forall D A B,
    TWell D A ->
    appDist A B ->
    TWell D B.
Proof.
  intros. gen B. inductions H; intros; try solve [inverts* H0].
  - inverts H1. constructor*.
  - inverts H1.
    + forwards*: IHTWell1 H4.
      forwards*: IHTWell2 H6.
    + forwards*: IHTWell1 H4.
      forwards*: IHTWell2 H6.
    + forwards*: IHTWell1 H4.
      forwards*: IHTWell2 H6.
      inverts H1. inverts H2.
      pick fresh x and apply TW_all.
      constructor*.
      forwards*: H9 x.
      forwards*: H10 x.
      forwards*: TW_and ((x, B1) :: (x, B2) :: D) (C1 -^ x) (C2 -^ x).
      simpl_env.
      applys* TWell_weakening.
      applys (TWell_weakening (C2 -^ x) ((x, B2) :: D) [(x, B1)] nil).
      simpl_env. auto.
      assert (RH: t_and (C1 -^ x) (C2 -^ x) = (t_and C1 C2) -^ x).
      { unfolds. simpl. reflexivity. }
      rewrites <- RH; clear RH. constructor.
      rewrite_env (nil ++ x ~ B1 ++ D) in H1.
      forwards*: TWell_bind_weakening H1.
      rewrite_env (nil ++ x ~ B2 ++ D) in H2.
      forwards*: TWell_bind_weakening H2.
  - inverts H2.
    pick fresh x and apply TW_all. auto.
    forwards*: H0 x.
  Unshelve. apply empty.
Qed.
 *)
(******************************************************************************)

Lemma appDist_subst : forall A B Z U,
    appDist A B ->
    lc_typ U ->
    appDist [Z ~~> U] (A) [Z ~~> U] (B).
Proof with eauto 3 using typsubst_typ_lc_typ.
  intros. induction* H; simpl; eauto with lngen.
Qed.

(******************************* proper types *********************************)
Lemma rfun : forall B, R B -> forall A, R A -> R (t_arrow A B).
Proof with eauto.
  intros B RB.
  induction RB; intros...
Qed.

Lemma rrcd : forall A, R A-> forall l, R (t_rcd l A).
Proof with eauto.
  intros A RA.
  induction RA; intros...
Qed.

#[local] Hint Resolve rfun rrcd : core.

(* depends on ord_or_split *)
Lemma rforall : forall A B X,
    R A -> R B
    -> R (t_forall A (close_typ_wrt_typ X B)).
Proof with eauto.
  introv RA RB. gen A.
  lets RB': RB.
  inductions RB; intros;
    try solve [
          applys~ R_ordAll; introv Fr1; clear Fr1];
    try solve [
          applys~ R_ordAll; introv Fr1; clear Fr1;
          [applys ord_rename X | applys~ proper_rename X]; try applys notin_close;
          try rewrite open_typ_wrt_typ_close_typ_wrt_typ;
          eauto].
  - (* spl *)
    rewrite <- (open_typ_wrt_typ_close_typ_wrt_typ _ X)in H.
    applys R_spl...

    Unshelve. all: applys empty.
Qed.

#[local] Hint Resolve rforall : core.

Lemma lc_types_are_proper : forall A, lc_typ A -> R A.
Proof with auto.
  introv H. induction* H.
  - remember (typefv_typ B). pick fresh X. subst.
    forwards* RB: H1 X.
    forwards* RF: rforall A X RB.
    rewrite (close_typ_wrt_typ_open_typ_wrt_typ _ X) in RF...
Qed.

Ltac proper_ind A := assert (Hlc: lc_typ A) by eauto; assert (r: R A) by applys lc_types_are_proper A Hlc; clear Hlc; induction r.
