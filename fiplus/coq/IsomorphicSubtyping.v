(**  Lemmas about Isomorphic Subtyping and Applicative Distributivity
     including binding related ones
*)
Require Import LibTactics.
Require Import Metalib.Metatheory.
Require Import Coq.Program.Equality.
Require Import Lia.
Require Export Disjointness.


(***************************** Isomorphic Subtyping ***************************)
(******************************************************************************)


Lemma subsub2sub: forall D A B,
  TCWell D ->
  TWell D A ->
  TWell D B ->
  subsub A B ->
  algo_sub D A B /\ algo_sub D B A.
Proof with eauto.
  intros. induction H2; auto.
  - (* and and *)
    destruct~ IHsubsub1. destruct~ IHsubsub2.
    (* destruct H6. destruct H7. *)
    (* forwards: TWell_lc_typ H6. *)
    (* forwards: TWell_lc_typ H7. *)
    assert(spl (t_and A1 A2) A1 A2) by auto.
    split.
    + apply S_and with B1 B2...
    + apply S_and with A1 A2. now auto.
      apply sub_transtivity with B1.
      apply spl_sub_l with B2... now auto.
      apply sub_transtivity with B2.
      apply spl_sub_r with B1... now auto.
Qed.

Lemma TWell_subsub_1: forall D A B,
    TWell D A -> subsub A B -> TWell D B.
Proof.
  intros. inductions H0; eauto.
    inverts H.
    forwards~: IHsubsub1.
    forwards~: IHsubsub2.
Qed.

Lemma TWell_subsub_2: forall D A B,
    TWell D B -> subsub A B -> TWell D A.
Proof.
  intros. inductions H0; eauto.
Qed.

#[export] Hint Immediate TWell_subsub_1 TWell_subsub_2 : core.

(*********************** Applicative Distributivity ***************************)
(******************************************************************************)

(***************** Applicative Distributivity determinism *********************)


Lemma appDist_arrow_unique: forall A B1 B2 C1 C2,
    appDist A (t_arrow B1 B2) -> appDist A (t_arrow C1 C2) -> B1 = C1 /\ B2 = C2.
Proof.
  intros. gen C1 C2.
  inductions H; intros.
  - (* merge *) 
    inverts H1.
    forwards*: IHappDist1.
    forwards*: IHappDist2.
    destruct_conj.
    split; congruence.
  - (* refl *)
    inverts~ H0.
Qed.


Lemma appDist_forall_unique: forall A B1 B2 C1 C2,
    appDist A (t_forall B1 B2) ->
    appDist A (t_forall C1 C2) ->
    B1 = C1 /\ B2 = C2.
Proof.
  intros. gen C1 C2.
  inductions H; intros.
  - (* merge *) 
    inverts H1.
    forwards*: IHappDist1.
    forwards*: IHappDist2.
    destruct_conj.
    split; congruence.
  - (* refl *)
    inverts~ H0.
Qed.


Lemma appDist_rcd_unique: forall A l B2 C2,
    appDist A (t_rcd l B2) -> appDist A (t_rcd l C2) -> B2 = C2.
Proof.
  intros. gen C2.
  inductions H; intros.
  - (* merge *) 
    inverts H1.
    forwards*: IHappDist1.
    forwards*: IHappDist2.
    congruence.
  - (* refl *)
    inverts~ H0.
Qed.

Ltac appdist_unify :=
  repeat match goal with
  | H1: appDist ?A (t_forall _ _), H2: appDist ?A (t_forall _ _) |- _ => forwards (?&?): appDist_forall_unique H1 H2; clear H2
  | H1: appDist ?A (t_arrow _ _), H2: appDist ?A (t_arrow _ _) |- _ => forwards (?&?): appDist_arrow_unique H1 H2; clear H2
  | H1: appDist ?A (t_rcd ?l _), H2: appDist ?A (t_rcd ?l  _) |- _ => forwards : appDist_rcd_unique H1 H2; clear H2
  | H: appDist (t_forall _ _) _ |- _ => inverts H
  | H: appDist (t_arrow _ _) _ |- _ => inverts H
  | H: appDist (t_rcd _ _) _ |- _ => inverts H
  | H: appDist (t_and _ _) _ |- _ => inverts H
         end; subst.

(*********************** Applicative Distributivity disjoint ***************************)

Lemma appDist_arr_disjoint: forall A B D A1 A2 B1 B2,
    appDist A (t_arrow A1 A2) -> appDist B (t_arrow B1 B2) -> disjoint D A B -> disjoint D A2 B2.
Proof.
  intros. gen D B B1 B2.
  inductions H; intros.
  - (* Merge *)
    assert(spl (t_and A0 A3) A0 A3). eauto.
    forwards: disjoint_andl_inv H3 H1. destruct H4.
    forwards*: IHappDist1.
  - (* refl *)
    inductions H0; auto.
    + (* Merge *)
    assert(spl (t_and A0 A3) A0 A3). eauto.
    forwards: disjoint_andr_inv H0 H1. destruct H2.
    forwards*: IHappDist1.
Qed.


Lemma appDist_rcd_disjoint: forall D A B l A' B',
    appDist A (t_rcd l A') -> appDist B (t_rcd l B') ->  disjoint D A B -> disjoint D A' B'.
Proof.
  intros. gen D B B'.
  inductions H; intros.
  - (* Merge *)
    forwards*: disjoint_andl_inv H1.
  - (* refl *)
    inductions H0; auto.
    + (* Merge *)
    forwards*: disjoint_andr_inv H1.
    + forwards~ [|]: disjoint_rcd_inv H1; contradiction.
Qed.

Lemma subsub_spl:forall A B C D,
    subsub A B -> 
    spl A C D ->
    exists G H, spl B G H/\ subsub C G /\subsub D H.
Proof.
  intros. gen C D.
  induction H; intros; split_unify; exists*.
 Qed.

Lemma subsub_trans : forall A B C,
    subsub A B -> subsub B C -> subsub A C.
Proof with (auto; solve_false).
  introv s1 s2.
  indTypSize (size_typ B).
  inverts keep s2...
  + (* spl *)
    inverts keep s1;auto.
    * (* spl *)
      forwards(?&?&?&?&?): subsub_spl s2 H2.
      forwards(?&?): split_decrease_size H5.
      assert(subsub A0 x). applys IH. apply H3. elia. auto.
      assert(subsub A3 x0). applys IH. apply H4. elia. auto.
      apply IS_and with x x0...
Qed.

Lemma subsub_rename : forall A B X Y,
    X \notin ( union [[A]] [[B]] ) ->
    subsub (A -^ X) (B -^ X) ->
    subsub (A -^ Y) (B -^ Y).
Proof.
  intros. dependent induction H0.
  - forwards~: open_typ_wrt_typ_inj A B X.
    substs. applys IS_refl.
    forwards~: lc_typ_rename_2 Y H0.
  - (* spl *)
    destruct A;inversion x. unfold open_typ_wrt_typ in x. simpl in x.
      destruct(lt_eq_lt_dec n 0). destruct s. inversion x. inversion x. inversion x.
    simpl in H. unfold open_typ_wrt_typ. simpl.
      forwards: open_spl H0. destruct H1. destruct H1.
    assert(spl (B -^ X) (x0 -^ X) (x1 -^ X)).
    auto. forwards*(?&?): split_unique H0 H4. subst.
    pick fresh Z. assert(spl (B -^ Z) (x0 -^ Z) (x1 -^ Z)). auto.
      assert(X `notin` [[(B -^ Z)]]). assert(X<>Z). auto.
    assert(AtomSetImpl.Subset (typefv_typ (B -^ Z)) (typefv_typ (t_tvar_f Z) `union` typefv_typ B)).
      apply typefv_typ_open_typ_wrt_typ_rec_upper_mutual.
    assert(X `notin` (Metatheory.union [[t_tvar_f Z]] [[B]])). auto. auto.
    forwards: split_fv H3 H2. destruct H5.
    assert(subsub(A3 -^ Y) (x0 -^ Y)). applys* IHsubsub1.
    assert(AtomSetImpl.Subset (typefv_typ x0) (typefv_typ (x0 -^ Z))).
      apply typefv_typ_open_typ_wrt_typ_rec_lower_mutual. auto. auto. auto. auto.
    assert(subsub (A4 -^ Y) (x1 -^ Y)). applys* IHsubsub2. auto.
    assert(AtomSetImpl.Subset (typefv_typ x1) (typefv_typ (x1 -^ Z))).
      apply typefv_typ_open_typ_wrt_typ_rec_lower_mutual. auto. auto. auto. auto.
    eauto.
Qed.

Lemma subsub_subst : forall A B C X,
    lc_typ C ->
    X `notin` (union [[A]] [[B]]) ->
    subsub (A -^ X) (B -^ X) ->
    subsub (A ^-^ C) (B ^-^ C).
Proof.
  intros. inductions H1; simpls.
  - forwards~: open_typ_wrt_typ_inj A B X.
    substs. applys IS_refl.
    eauto with lngen.
  - forwards (D1&D2&?): open_spl H1.
    forwards: H2 X.
    forwards (?&?): split_unique H1 H3; substs.
    destruct* A; solve_false.
    destruct n; solve_false.
    unfold open_typ_wrt_typ in x. simpls.
    inverts x.
    pick fresh Z.
    forwards: H2 Z.
    forwards: split_fv X H4.
    assert(X<>Z); auto.
    assert(AtomSetImpl.Subset (typefv_typ (B -^ Z)) (typefv_typ (t_tvar_f Z) `union` typefv_typ B)).
      apply typefv_typ_open_typ_wrt_typ_rec_upper_mutual.
    assert(X `notin` (Metatheory.union [[t_tvar_f Z]] [[B]])). auto. auto.
    destruct H5.
    unfold open_typ_wrt_typ in H5.
    lets: (typefv_typ_open_typ_wrt_typ_rec_lower_mutual D1 (t_tvar_f Z) 0).
    lets: (typefv_typ_open_typ_wrt_typ_rec_lower_mutual D2 (t_tvar_f Z) 0).
    forwards*: IHsubsub1 X D1 A3; auto.
    forwards*: IHsubsub2 X D2 A4; auto.
    unfold open_typ_wrt_typ.
    applys* IS_and.
    forwards: open_spl_2.
    intros. forwards: H2 X0.
    apply H12.
    eassumption.
    auto.
  Unshelve. apply empty.
Qed.


(*********************** Applicative Distributivity subsub ***************************)

Lemma appDist_forall_subsub: forall L D A1 A2 C C',
    TCWell D ->
    TWell D C ->
    TWell D C' ->
    appDist C (t_forall A1 A2) ->
    subsub C' C ->
    exists A1' A2', appDist C' (t_forall A1' A2')
      /\ (forall Y, Y `notin` L -> subsub (A2' -^ Y) (A2 -^ Y))
      /\ algo_sub D A1 A1'.
Proof.
  intros. gen A1 A2. inductions H3; intros.
  - (* refl *)
    exists A1 A2.
    forwards: TWell_appDist H0 H3. eauto.
  - (* and forall *)
    inverts H3.
    + inverts H2. 
      forwards (?&?&?&?&?): IHsubsub1; eauto.
      forwards (?&?&?&?&?): IHsubsub2; eauto.
      exists (t_and x x1) (t_and x0 x2). split. eauto. split.
      pick fresh X.
      assert(subsub (x0 -^ X) (C1 -^ X)). auto.
      assert(subsub (x2 -^ X) (C2 -^ X)). auto.
      unfold open_typ_wrt_typ. simpl. eauto.
      intros.
      applys IS_and. constructor.
      forwards (_&?): subsub_lc H12.
      eauto using lc_typ_rename_2.
      forwards (_&?): subsub_lc H13.
      eauto using lc_typ_rename_2.
      apply subsub_rename with X. auto. auto. 
      apply subsub_rename with X. auto. auto. eauto.
    + inversion H1;subst.
      inversion H2;subst.
      inverts H4.
      forwards (?&?&?&?&?): IHsubsub1; eauto.
      forwards (?&?&?&?&?): IHsubsub2; eauto.
      exists (t_and x x1) (t_and x0 x2). split. eauto. split.
      pick fresh X.
      intros. unfold open_typ_wrt_typ. simpls.
      applys IS_and.
      forwards~: H11 X.
      forwards~: split_rename Y H16.
      eauto.
      instantiate_cofinites; auto.
      instantiate_cofinites; auto.
      eauto.
Qed.

Lemma appDist_rcd_subsub: forall D l A C C',
    TCWell D ->
    TWell D C ->
    TWell D C' ->
    appDist C (t_rcd l A) ->
    subsub C' C ->
    exists A', appDist C' (t_rcd l A') /\ subsub A' A.
Proof.
  intros. gen A. induction H3;intros.
  - (* refl *)
    exists A0.
    forwards: TWell_appDist H0 H3. 
    splits*.
  - (* and arrow *)
    inversion H1;subst.
    inversion H2;subst; solve_false.

    inverts H3.
    forwards (?&?&?): IHsubsub1; eauto.
    forwards (?&?&?): IHsubsub2; eauto.

    inversion H1;subst.
    inversion H3;subst.

    forwards (?&?&?): IHsubsub1; eauto.
    forwards (?&?&?): IHsubsub2; eauto.
    exists (t_and x x0). split. eauto. eauto.
  Unshelve. 1,3: apply nil. all: pick fresh x; apply x.
Qed.


Lemma appDist_forall_subsub_disjoint: forall D A1 A2 C C',
    TCWell D ->
    TWell D C ->
    TWell D C' ->
    appDist C (t_forall A1 A2) ->
    subsub C' C ->
    exists A1' A2', appDist C' (t_forall A1' A2')
      /\ (forall T, disjoint D T A1 -> subsub (A2' ^-^ T) (A2 ^-^ T))
      /\ algo_sub D A1 A1'.
Proof with intuition eauto.
  intros.
  forwards* (A1'&A2'&AD&SS&Sub): appDist_forall_subsub H2.
  exists; splits*.
  intros.
  pick fresh Y.
  forwards~: SS Y.
  applys* subsub_subst.
  solve_notin.
Qed.

Lemma disjoint_appDist_forall : forall D A1 A2 B1 C1 B2 C2,
    disjoint D A1 A2 ->
    appDist A1 (t_forall B1 C1) ->
    appDist A2 (t_forall B2 C2) ->
    disjoint D (t_forall B1 C1) (t_forall B2 C2).
Proof.
  intros. gen D B2 C2. inductions H0; intros.
  - inductions H1.
    + clear IHappDist0 IHappDist3.
      assert(spl (A1 & A0) A1 A0) by auto.
      forwards~ (?&?): disjoint_andl_inv H.
      forwards*: IHappDist1.
      forwards*: IHappDist2.
      pick fresh X and apply D_all; auto.
      unfold open_typ_wrt_typ. simpls.
      assert (spl ((C0 -^ X) & (C2 -^ X)) (C0 -^ X) (C2 -^ X)) by auto.
      applys D_andl. eassumption.
      * forwards~: disjoint_forall_inv H3 X.
        rewrite_env (nil ++ X ~ ((B0 & B2) & (B4 & B3)) ++ D).
        applys disjoint_narrowing.
        unfold open_typ_wrt_typ in H6. simpls.
        eassumption. auto_sub; auto.
        assert(D ||- (B0 & B2) & (B4 & B3) <: (B0 & B2)) by auto.
        assert(D ||- B0 & B2 <: B0) by auto; auto.
      * forwards~: disjoint_forall_inv H4 X.
        rewrite_env (nil ++ X ~ ((B0 & B2) & (B4 & B3)) ++ D).
        applys disjoint_narrowing.
        unfold open_typ_wrt_typ in H6. simpls.
        eassumption. auto_sub; auto.
        assert(D ||- (B0 & B2) & (B4 & B3) <: (B0 & B2)) by auto.
        assert(D ||- B0 & B2 <: B2) by auto; auto.
    + forwards~ (?&?): disjoint_andl_inv H.
      forwards*: IHappDist1.
      forwards*: IHappDist2.
      pick fresh X and apply D_all; eauto.
      forwards~: disjoint_forall_inv H3 X.
      forwards~: disjoint_forall_inv H4 X.
      unfold open_typ_wrt_typ. simpls.
      assert (spl ((C0 -^ X) & (C2 -^ X)) (C0 -^ X) (C2 -^ X)) by auto.
      applys D_andl. eassumption.
      * rewrite_env (nil ++ X ~ ((B0 & B2) & B1) ++ D).
        applys disjoint_narrowing.
        unfold open_typ_wrt_typ in H6. simpls.
        eassumption. auto_sub; auto.
        assert(D ||- (B0 & B2) & B1 <: (B0 & B2)) by auto.
        assert(D ||- B0 & B2 <: B0) by auto; auto.
      * rewrite_env (nil ++ X ~ ((B0 & B2) & B1) ++ D).
        applys disjoint_narrowing.
        unfold open_typ_wrt_typ in H6. simpls.
        eassumption. auto_sub; auto.
        assert(D ||- (B0 & B2) & B1 <: (B0 & B2)) by auto.
        assert(D ||- B0 & B2 <: B2) by auto; auto.
  - inductions H1; auto.
    assert(spl (A1 & A2) A1 A2) by auto.
    forwards(?&?): disjoint_andr_inv H0. eassumption.
    forwards~: IHappDist1. 
    forwards~: IHappDist2.
    pick fresh X and apply D_all; auto.
    unfold open_typ_wrt_typ. simpls.
    assert (spl ((C0 -^ X) & (C3 -^ X)) (C0 -^ X) (C3 -^ X)) by auto.
    forwards~: disjoint_forall_inv H4 X.
    forwards~: disjoint_forall_inv H5 X.
    applys D_andr. eassumption.
    + rewrite_env (nil ++ X ~ ( B1 & (B0 & B3)) ++ D).
      applys disjoint_narrowing. simpls.
      eassumption. auto_sub; auto.
      assert(D ||- B1 & (B0 & B3) <: (B0 & B3)) by auto.
      assert(D ||- B0 & B3 <: B0) by auto; auto.
    + rewrite_env (nil ++ X ~ ( B1 & (B0 & B3)) ++ D).
      applys disjoint_narrowing. simpls.
      eassumption. auto_sub; auto.
      assert(D ||- B1 & (B0 & B3) <: (B0 & B3)) by auto.
      assert(D ||- B0 & B3 <: B3) by auto; auto.
Qed.

Lemma disjoint_appDist_forall_inv : forall D T A1 A2 B1 C1 B2 C2,
    disjoint D A1 A2 ->
    appDist A1 (t_forall B1 C1) ->
    appDist A2 (t_forall B2 C2) ->
    disjoint D T (t_and B1 B2) ->
    disjoint D (C1 ^-^ T) (C2 ^-^ T).
Proof.
  intros.
  forwards*: disjoint_appDist_forall H.
  pick fresh X.
  forwards~: disjoint_forall_inv H3 X.
  rewrite_env (nil ++ (X ~ (B1 & B2)) ++ D) in H4.
  forwards*: disjoint_disjoint_weakening X H4.
  auto.
Qed.

Lemma appDist_arr_subsub: forall D A1 A2 C C',
    TCWell D ->
    TWell D C ->
    TWell D C' ->
    appDist C (t_arrow A1 A2) -> subsub C' C
    -> exists A1' A2', appDist C' (t_arrow A1' A2') /\ subsub A2' A2 /\ DuplicatedType A1' A1.
Proof.
  intros. gen A1 A2. induction H3; intros.
  - (* refl *)
    exists A1 A2.
    forwards~: TWell_appDist H1 H3.
  - (* and arrow *)
    inversion H1;subst.
    inversion H3;subst.
    inverts H2.
    forwards (?&?&?&?&?): IHsubsub1; eauto.
    inverts H0.
    forwards (?&?&?&?&?): IHsubsub2; eauto.
    exists (t_and x x1) (t_and x0 x2). split. eauto. split. eauto. eauto.
    inversion H2;subst.
    inverts H4.
    forwards (?&?&?&?&?): IHsubsub1; intuition eauto.
    forwards (?&?&?&?&?): IHsubsub2; intuition eauto.
    exists (t_and x x1) (t_and x0 x2). split. eauto. split.
    eauto. eauto.
Qed.
