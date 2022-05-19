Require Import LibTactics.
Require Import Lia.
Require Import Coq.Program.Equality.
Require Export Subtyping.


(***************************** disjointness axiom ***********************************)

Ltac try_disjoint_axiom_constructors :=
  match goal with
  | |- disjoint_axiom t_int (t_rcd _ _) => applys Dax_intRcd
  | |- disjoint_axiom t_int (t_arrow _ _) => applys Dax_intArrow
  | |- disjoint_axiom t_int (t_forall _ _) => applys Dax_intAll
  | |- disjoint_axiom (t_arrow _ _) (t_rcd _ _) => applys Dax_arrowRcd
  | |- disjoint_axiom (t_arrow _ _) (t_forall _ _) => applys Dax_arrowAll
  | |- disjoint_axiom (t_rcd _ _) (t_rcd _ _) => applys Dax_rcdNeq
  end.

#[export] Hint Extern 1 (disjoint_axiom _ _) => try_disjoint_axiom_constructors : core.

#[export] Hint Extern 1 => match goal with
                           | [ H: topLike _ _ |- _ ] =>
                             inverts H; fail
                           | [ H: disjoint_axiom _ _ |- _ ] =>
                             inverts H; fail
                           end : FalseHd.

Lemma disjoint_axiom_symm: forall A B,
    disjoint_axiom A B -> disjoint_axiom B A.
Proof.
  introv H.
  induction* H.
Qed.

#[export] Hint Immediate disjoint_axiom_symm : core.


Ltac try_disjoint_constructors :=
  match goal with
  |  H: topLike _ ?A |- disjoint _ ?A ?B => applys D_topl H
  |  H: topLike _ ?B |- disjoint _ ?A ?B => applys D_topr H
  |  H: disjoint_axiom ?A ?B |- disjoint _ ?A ?B => applys D_ax H
  |  |- disjoint _ t_int (t_arrow _ _) => applys D_ax; try applys Dax_intArrow
  |  |- disjoint _ (t_arrow _ _) t_int => applys D_ax; try applys Dax_arrowInt
  |  |- disjoint _ t_int (t_rcd _ _) => applys D_ax; try applys Dax_intRcd
  |  |- disjoint _ (t_rcd _ _) t_int => applys D_ax; try applys Dax_rcdInt
  (* too many cases for disjoint axioms... *)
  (* the following two lines try to cover all disjoint axioms cases *)
  |  |- _ => applys D_ax; [ | | try_disjoint_axiom_constructors]
  |  |- disjoint _ (t_and _ _) _ => applys D_andl
  |  |- disjoint _ _ (t_and _ _) => applys D_andr
  |  H: spl ?A ?A1 ?A2 |- disjoint _ ?A _ => applys D_andl H
  |  H: spl ?A ?A1 ?A2 |- disjoint _ _ ?A => applys D_andr H
  |  |- disjoint _ (t_forall _ _) _ => applys D_all; try eassumption
  |  |- disjoint _ _ (t_forall _ _) => applys D_all; try eassumption
  |  |- disjoint _ (t_arrow _ _) _ => applys D_arrow
  |  |- disjoint _ _ (t_arrow _ _) => applys D_arrow
  |  H: ?l1 <> ?l2 |- disjoint _ (t_rcd ?l1 _) (t_rcd ?l2 _) => applys D_ax; try applys Dax_rcdNeq H
  |  |- disjoint _ (t_rcd _ _) (t_rcd _ _) => applys D_rcdEq
  |  |- disjoint _ (t_tvar_f _) _ => applys D_varl
  |  |- disjoint _ _ (t_tvar_f _) => applys D_varr
  end.

#[export] Hint Extern 0 (disjoint _ _ _) => try_disjoint_constructors : core.


Ltac split_toplike :=
  match goal with
  | H1: spl ?A _ _, H2: topLike ?A |- _ => forwards (?&?): topLike_split_inv H2 H1
  end
.

Ltac solve_TWell_by_split :=
  match goal with
  | H1 : TWell ?D ?B, H2 : spl ?B ?A _ |- _ => forwards(?&?): TWell_spl H1 H2; easy
  | H1 : TWell ?D ?B, H2 : spl ?B _ ?A |- _ => forwards(?&?): TWell_spl H1 H2; easy
  | H1 : TWell ?D (t_arrow ?A _) |- TWell ?D (t_arrow ?A _) => forwards(?&?): TWell_spl H1; easy
  | H1 : TWell ?D (t_rcd ?l _) |- TWell ?D (t_rcd ?l _) => forwards(?&?): TWell_spl H1; easy
  | H1 : TWell ?D (t_forall ?A _) |- TWell ?D (t_forall ?A _) => forwards(?&?): TWell_spl H1; easy
  | H1 : TWell ?D _ |- TWell ?D _ => forwards(?&?): TWell_spl H1; easy
  end.

#[export] Hint Extern 1 (TWell _ _) => solve_TWell_by_split : core.

Lemma disjoint_andl_inv: forall D A A1 A2 B,
    spl A A1 A2 -> disjoint D A B -> disjoint D A1 B /\ disjoint D A2 B.
Proof with (split_unify; solve_false).
  introv Hspl Hdis. gen A1 A2.
  induction Hdis; intros...
  - forwards: TWell_spl H0 Hspl.  destruct H3. inversion Hspl;subst;inversion H2;subst;auto.
  - apply IHHdis in H6. destruct H6. auto.
  - apply IHHdis in H3. destruct H3. auto.
  - split; try_disjoint_constructors; auto; intros X HN;
      instantiate ( 1 := (L `union` L0) ) in HN;
      instantiate_cofinites_with X;
      forwards* (?&?): H2 H8.
  - assert (algo_sub D A A1) by eauto.
    assert (algo_sub D A A2) by eauto.
    split*.
  - forwards: IHHdis1; try eassumption.
    forwards: IHHdis2; try eassumption; jauto.
Qed.


Lemma disjoint_andr_inv: forall D A A1 A2 B,
    spl A A1 A2 -> disjoint D B A -> disjoint D B A1 /\ disjoint D B A2.
Proof with (split_unify; solve_false).
  introv Hspl Hdis. gen A1 A2.
  induction Hdis; intros...
  - forwards: TWell_spl H1 Hspl.  destruct H3. inversion Hspl;subst;inversion H2;subst;auto.
  - apply IHHdis in H6. destruct H6. auto.
  - apply IHHdis in H3. destruct H3. auto.
  - split; try_disjoint_constructors; auto; intros X HN;
      instantiate ( 1 := (L `union` L0) ) in HN;
      instantiate_cofinites_with X;
      forwards* (?&?): H2 H8.
  - assert (algo_sub D A A1) by eauto.
    assert (algo_sub D A A2) by eauto.
    split*.
  - forwards: IHHdis1; try eassumption.
    forwards: IHHdis2; try eassumption; jauto.
Qed.



#[export] Hint Extern 0 (ord _) =>
match goal with
| H: ord (t_rcd _ ?A) |- ord ?A => inverts H
| H: ord (t_arrow _ ?A) |- ord ?A => inverts H
end : core.


Lemma disjoint_rcd_inv: forall D A B l1 l2,
    disjoint D (t_rcd l1 A) (t_rcd l2 B) -> l1 <> l2 \/ disjoint D A B.
Proof with (split_unify; solve_false; auto with  SubHd).
  introv H.
  inductions H...
  - inverts H2...
  - inversion H;subst. inversion H0;subst. auto.
  - inversion H;subst. inversion H0;subst. auto.
  - forwards [?|?]: IHdisjoint1; try reflexivity; auto.
    forwards [?|?]: IHdisjoint2; try reflexivity; auto.
  - forwards [?|?]: IHdisjoint1; try reflexivity; auto.
    forwards [?|?]: IHdisjoint2; try reflexivity; auto.
Qed.

Lemma disjoint_arr_inv: forall D A1 A2 B1 B2,
    disjoint D (t_arrow A1 A2) (t_arrow B1 B2) -> disjoint D A2 B2.
Proof with (split_unify; solve_false; auto with  SubHd).
  introv H.
  inductions H...
  - inversion H;subst. inversion H0;subst. auto.
  - inversion H;subst. inversion H0;subst. auto.
  - applys* D_andl.
  - applys* D_andr.
Qed.

Ltac disjoint_solve_by_inv :=
  match goal with
  | H: disjoint ?D (t_rcd ?l ?A) (t_rcd ?l ?B) |- disjoint ?D ?A ?B => applys~ disjoint_rcd_inv H
  | H: disjoint ?D (t_arrow _ ?A) (t_arrow _ ?B) |- disjoint ?D ?A ?B => applys~ disjoint_arr_inv H
  |  H: disjoint ?D (t_forall ?A _) ?B |- disjoint ?D (t_forall ?A _) ?B => forwards (?&?): disjoint_andl_inv H
  |  H: disjoint ?D (t_arrow ?A _) ?B |- disjoint ?D (t_arrow ?A _) ?B => forwards (?&?): disjoint_andl_inv H
  |  H: disjoint ?D (t_rcd ?l _) ?B |- disjoint ?D (t_rcd ?l _) ?B => forwards (?&?): disjoint_andl_inv H
  |  H: disjoint ?D ?B (t_and ?A _) |- disjoint ?D ?A ?B => forwards (?&?): disjoint_andl_inv H
  |  H: disjoint ?D ?B (t_and _ ?A) ?B |- disjoint ?D ?A _ => forwards (?&?): disjoint_andl_inv H
  |  H: disjoint ?D ?B (t_and _ _) ?B |- disjoint ?D ?A _ => forwards (?&?): disjoint_andl_inv H
  |  Hspl: spl ?A ?A1 _, H: disjoint ?D ?B ?A ?B |- disjoint ?D ?A1 ?B => forwards (?&?): disjoint_andl_inv Hspl H
  |  Hspl: spl ?A _ ?A1, H: disjoint ?D ?B ?A ?B |- disjoint ?D ?A1 ?B => forwards (?&?): disjoint_andl_inv Hspl H
  |  H: disjoint ?D ?B (t_forall ?A _) |- disjoint ?D ?B (t_forall ?A _) => forwards (?&?): disjoint_andr_inv H
  |  H: disjoint ?D ?B (t_arrow ?A _) |- disjoint ?D ?B (t_arrow ?A _) => forwards (?&?): disjoint_andr_inv H
  |  H: disjoint ?D ?B (t_rcd ?l _) |- disjoint ?D ?B (t_rcd ?l _) => forwards (?&?): disjoint_andr_inv H
  |  H: disjoint ?D ?B (t_and ?A _) |- disjoint ?D _ ?A => forwards (?&?): disjoint_andr_inv H
  |  H: disjoint ?D ?B (t_and _ ?A) |- disjoint ?D _ ?A => forwards (?&?): disjoint_andr_inv H
  |  Hspl: spl ?A ?A1 _, H: disjoint ?D ?B ?A |- disjoint ?D ?B ?A1 => forwards (?&?): disjoint_andr_inv Hspl H
  |  Hspl: spl ?A _ ?A1, H: disjoint ?D ?B ?A |- disjoint ?D ?B ?A1 => forwards (?&?): disjoint_andr_inv Hspl H
  end.

#[export] Hint Extern 1 (disjoint _ _ _) => disjoint_solve_by_inv : core.


Ltac inverts_for_disjointness :=
  match goal with
  | H: disjoint_axiom _ _ |- _ => inverts H
  | H: disjoint _ (t_and _ _) _ |- _ => forwards(?&?): disjoint_andl_inv H; clear H
  | H: disjoint _ _ (t_and _ _) |- _ => forwards(?&?): disjoint_andr_inv H; clear H
  | H: disjoint _ ?A _ , Hspl: spl ?A _ _ |- _ => forwards(?&?): disjoint_andl_inv Hspl H
  | H: disjoint _ _ ?A , Hspl: spl ?A _ _ |- _ => forwards(?&?): disjoint_andl_inv Hspl H
  | H: disjoint _ (t_arrow _ _) (t_arrow _ _) |- _ => forwards: disjoint_arr_inv H
  | H: disjoint _ (t_rcd _ _) (t_rcd _ _) |- _ => forwards: disjoint_rcd_inv H
  end.

(************************************************************************)
Lemma disjoint_narrowing : forall X Q F E P S T,
    disjoint (F ++ [(X, Q)] ++ E) S T ->
    algo_sub E P Q ->
    disjoint (F ++ [(X, P)] ++ E) S T.
Proof with repeat (try applys TCWell_bind_weakening; try applys TWell_bind_weakening_2; try applys topLike_bind_weakening; try eassumption; auto).
  introv Hdis Hsub.
  inductions Hdis.
  - (* axiom *) applys~ D_ax...
  - applys~ D_topl...
  - applys~ D_topr...
  - (* arrow *)
    try_disjoint_constructors...
    applys* IHHdis.
  - (* rcd *)
    try_disjoint_constructors...
    applys* IHHdis.
  - (* forall *)
    try_disjoint_constructors...
    intros Y HN.
    instantiate_cofinites_with Y.
    rewrite_env (((Y, t_and A1 A2) :: F) ++ X ~ P ++ E).
    applys* H2. intuition eauto.
  - (* fvar L *)
    forwards: algo_sub_well_tctx H0.
    forwards: algo_sub_regular Hsub. destruct H2.
    forwards [?|(?&?&?)]: binds_replace H H1 H2.
    forwards: algo_sub_bind_weakening H0 Hsub. eauto.
    subst.
    assert (algo_sub (F ++ X ~ P ++ E) P B).
    apply sub_transtivity with Q. rewrite_env(nil ++ (F ++ X ~ P) ++ E).
    apply algo_sub_weakening. auto. rewrite_env(F ++ X ~ P ++ E).
    apply TCWell_bind_weakening with Q. auto. auto.
    apply algo_sub_bind_weakening with Q. auto. auto. auto.
  - (* fvar L *)
    forwards: algo_sub_well_tctx H0.
    forwards: algo_sub_regular Hsub. destruct H2.
    forwards [?|(?&?&?)]: binds_replace H H1 H2.
    forwards: algo_sub_bind_weakening H0 Hsub. eauto.
    subst.
    assert (algo_sub (F ++ X ~ P ++ E) P B).
    apply sub_transtivity with Q. rewrite_env(nil ++ (F ++ X ~ P) ++ E).
    apply algo_sub_weakening. auto. rewrite_env(F ++ X ~ P ++ E).
    apply TCWell_bind_weakening with Q. auto. auto.
    apply algo_sub_bind_weakening with Q. auto. auto. auto.
  - (* spl L *)
    try_disjoint_constructors...
    applys* IHHdis1.
    applys* IHHdis2.
  - (* spl R *)
    try_disjoint_constructors...
    applys* IHHdis1.
    applys* IHHdis2.
Qed.


Ltac narrow :=
  match goal with
  | H: disjoint ((?X,?A) :: ?D) ?B ?C |- disjoint ((?X,?A') :: ?D) ?B ?C => (
      rewrite_env ( nil ++ [(X, A')] ++ D );
      rewrite_env ( nil ++ [(X, A)] ++ D ) in H;
      applys~ disjoint_narrowing H;
      auto with SubHd
    )
  | H: TWell ((?X,?A) :: ?D) ?B |- TWell ((?X,?A') :: ?D) ?B => (
      rewrite_env ( nil ++ [(X, A')] ++ D );
      rewrite_env ( nil ++ [(X, A)] ++ D ) in H;
      applys~ TWell_bind_weakening_2 H;
      auto with SubHd
    )
  end.

Lemma disjoint_eqv_context : forall X D A1 A2 B1 B2,
    disjoint ((X, A1) :: D) B1 B2 -> algo_sub D A2 A1 ->
    disjoint ((X, A2) :: D) B1 B2.
Proof.
  introv Hdis Hsub.
  narrow.
Qed.

Lemma disjoint_well_tctx: forall D A B,
    disjoint D A B -> TCWell D.
Proof.
  introv H. induction* H.
  pick fresh X. assert(TCWell ((X, t_and A1 A2) :: D)). auto. inversion H3;subst. auto.
Qed.


Lemma disjoint_symm: forall D A B,
    disjoint D A B -> disjoint D B A.
Proof with auto with SubHd .
  introv H.
  induction H...
  - try_disjoint_constructors.
    introv HN. forwards: H2 HN.
    applys~ disjoint_eqv_context H3...
    apply disjoint_well_tctx in H3.
    inversion H3;subst.
    apply S_and with A1 A2...
  - try_disjoint_constructors; eauto.
  - try_disjoint_constructors; eauto.
Qed.

#[export] Hint Immediate disjoint_symm : core.


Lemma disjoint_covariance : forall D A B C,
    disjoint D A B -> algo_sub D B C -> disjoint D A C.
Proof with (split_unify; solve_false; auto 3 with SubHd).
  introv HD HS. gen D.
  indTypSize (size_typ A + size_typ B + size_typ C).
  inverts HS; intros.
  1-3: try solve [split_unify; solve_false; auto 3 with SubHd].
  - (* bot *)
    inverts HD.
    1-3,6: try solve [split_unify; solve_false; auto 3 with SubHd].
    + applys* D_varl...
    + forwards: split_decrease_size H2. destruct H5.
      applys~ D_andl H2. apply IH with t_bot. lia...
      auto. auto. apply IH with t_bot. lia... auto. auto.
  - (* andl *)
    assert(spl (t_and A0 B0) A0 B0). eauto.
    forwards: disjoint_andr_inv H2 HD. destruct H3. simpl in SizeInd.
    forwards: IH H3 H1. lia. auto.
  - (* andr *)
    assert(spl (t_and A0 B0) A0 B0). eauto.
    forwards: disjoint_andr_inv H2 HD. destruct H3. simpl in SizeInd.
    forwards: IH H4 H1. lia. auto.
  - (* arrow *)
    inverts HD.
    + inverts H5; forwards: algo_sub_regular H0; destruct H5;
        forwards: algo_sub_regular H1; destruct H7; auto.
    + forwards: algo_sub_regular H0; destruct H4;
        forwards: algo_sub_regular H1; destruct H6; auto.
    + forwards: algo_sub_regular H0; destruct H4;
        forwards: algo_sub_regular H1; destruct H6; auto.
    + try_disjoint_constructors; auto.
      applys IH H8; try eassumption; elia; eauto.
    + applys* D_varl. auto with SubHd.
    + applys~ D_andl H2; applys IH; try eassumption; elia; eauto.
    + inverts H2. forwards~ [?|?]: sub_inversion_split_l H1 H10.
      * applys IH H3; try eassumption; elia. eauto.
      * applys IH H4; try eassumption; elia. eauto.
  - (* forall *)
    inverts HD.
    + inverts H5; assert(algo_sub D (t_forall A1 A2) (t_forall B1 B2)); eauto; apply algo_sub_regular in H5; auto.
    + assert(algo_sub D (t_forall A1 A2) (t_forall B1 B2)); eauto.
    + assert(algo_sub D (t_forall A1 A2) (t_forall B1 B2)); eauto.
    + apply D_all with (union L L0). auto. apply algo_sub_regular in H0. auto.
      intros. assert(disjoint ((X, t_and A0 B1) :: D) (B0 -^ X) (A2 -^ X)).
      rewrite_env(disjoint (nil++[(X, t_and A0 B1)]++D) (B0 -^ X) (A2 -^ X)).
      apply disjoint_narrowing with (t_and A0 A1). simpl. auto. apply S_and with A0 A1.
      eauto. apply sub_l_andl. apply algo_sub_regular in H0. auto. apply sub_reflexivity. apply algo_sub_well_tctx in H0. auto. auto.
      apply sub_l_andr. apply algo_sub_regular in H0. auto. auto.
      assert(algo_sub ((X, t_and A0 B1) :: D) (A2 -^ X) (B2 -^ X)).
      rewrite_env((nil++[(X, t_and A0 B1)]++D)). apply algo_sub_bind_weakening with B1. apply H1. auto.
      apply sub_l_andr. apply algo_sub_regular in H0. auto. apply sub_reflexivity. apply algo_sub_well_tctx in H0. auto. auto.
      apply algo_sub_regular in H0. auto.
      forwards*: IH H3 H5. rewrite size_typ_open_typ_wrt_typ_var.
      rewrite size_typ_open_typ_wrt_typ_var.
      rewrite size_typ_open_typ_wrt_typ_var. simpl in SizeInd. lia.
    + applys* D_varl. eauto with SubHd.
    + applys~ D_andl H2; applys IH; try eassumption; elia; eauto.
    + assert (Hord: ord (t_forall B1 B2)) by eauto.
      assert (HS: algo_sub D (t_forall A1 A2) (t_forall B1 B2)) by eauto.
      forwards~ [Hi|Hi]: sub_inversion_split_l HS H2 Hord.
      * applys IH Hi; try eassumption; elia.
      * applys IH Hi; try eassumption; elia.
  - (* rcd *)
    inverts HD.
    + inverts H4; forwards: algo_sub_regular H0; destruct H4;auto.
    + forwards: algo_sub_regular H0; destruct H3; auto.
    + forwards: algo_sub_regular H0; destruct H3; auto.
      inversion H2;subst. eauto.
    + try_disjoint_constructors; auto.
      applys IH H4; try eassumption; elia; eauto.
    + applys* D_varl. auto with SubHd.
    + applys~ D_andl H1; applys IH; try eassumption; elia; eauto.
    + inverts H1. forwards~ [?|?]: sub_inversion_split_l H0 H8.
      * applys IH H2; try eassumption; elia. eauto.
      * applys IH H3; try eassumption; elia. eauto.
  - (* spl C *)
    applys~ D_andr H. forwards: disjoint_well_tctx HD. all: applys IH; try eassumption; elia; eauto.
Qed.

Definition disjointSpec D A B :=
  forall C, algo_sub D A C -> algo_sub D B C -> topLike D C.


Lemma disjointSpec_complete_to_disjoint_axiom : forall D A B,
    TCWell D -> TWell D A -> TWell D B -> disjoint_axiom A B -> disjointSpec D A B.
Proof with solve_false.
  intros D A B CTX TW1 TW2 Dis C S1 S2.
  indTypSize (size_typ A + size_typ B + size_typ C).
  forwards [?|(?&?&?)]: ord_or_split C. eauto.
  - inverts~ Dis; inverts S1; inverts S2; trivial; solve_false.
  - (* splittable C *)
    applys topLike_spl_combine H; applys* IH Dis; elia.
Qed.

Inductive varLike : atom -> typ -> Prop :=
| VA_self :
    forall X,
      varLike X (t_tvar_f X)
| VA_andl : forall X (A B:typ),
    varLike X  A ->
    varLike X (t_and A B)
| VA_andr : forall X (A B:typ),
    varLike X  B ->
    varLike X  (t_and A B).

#[export] Hint Constructors varLike : core.

Lemma bot_or_var: forall D X A, algo_sub D A (t_tvar_f X) -> (botLike A\/varLike X A\/topLike D (t_tvar_f X)).
Proof.
  intros. induction A;try solve[inversion H;subst;auto;inversion H2;inversion H0].
  inversion H;subst. auto. apply IHA1 in H6. destruct H6;auto. apply TWell_lc_typ in H2. auto. destruct H0;auto.
  apply IHA2 in H6. destruct H6;auto. apply TWell_lc_typ in H2. auto. destruct H0;auto. inversion H0.
Qed.

Lemma bot_or_var_2: forall D X A B, varLike X B -> algo_sub D A B -> (botLike A\/varLike X A\/topLike D (t_tvar_f X)).
Proof.
  intros. induction H. apply bot_or_var. auto.
  assert(spl (t_and A0 B) A0 B). apply algo_sub_regular in H0. destruct H0. inversion H1;subst.
  apply TWell_lc_typ in H5. apply TWell_lc_typ in H6. auto.
  forwards: sub_inversion_split_r H0 H1. destruct H2. auto.
  assert(spl (t_and A0 B) A0 B). apply algo_sub_regular in H0. destruct H0. inversion H1;subst.
  apply TWell_lc_typ in H5. apply TWell_lc_typ in H6. auto.
  forwards: sub_inversion_split_r H0 H1. destruct H2. auto.
Qed.

Lemma TW_in: forall D X A, TWell D A-> varLike X A-> exists B, binds X B D.
Proof.
  intros. induction H0. inversion H;subst. eauto.
  inversion H;subst. auto.
  inversion H;subst. auto.
Qed.

Lemma TCW_no_rec: forall D X A, TCWell D -> varLike X A -> binds X A D -> False.
Proof.
  intros.
  induction H.
  inversion H1.
  apply binds_cons_iff in H1. destruct H1. destruct H1. subst.
  inversion H3;subst.
  forwards: TW_in H2 H0. destruct H1.
  eapply binds_dom_contradiction. apply H1. auto.
  auto.
Qed.


#[export]
 Hint Extern 1 => applys TCW_no_rec; easy : FalseHd.


Lemma disjoint_soundness: forall D A B,
    disjoint D A B -> disjointSpec D A B.
Proof with intuition eauto.
  intros D A B Dis C S1 S2. gen D.
  indTypSize (size_typ A + size_typ B + size_typ C).
  forwards [?|(?&?&?)]: ord_or_split C. eauto.
  - inverts Dis.
    + forwards: disjointSpec_complete_to_disjoint_axiom H0 H1 H2 H3. apply H4. auto. auto.
    + forwards*: toplike_sub H1 S1.
    + forwards*: toplike_sub H1 S2.
    + inversion S1;subst;auto. inversion S2;subst;auto.
      simpl in SizeInd. inversion H;subst. forwards: IH H2 H9 H13. lia. apply algo_sub_regular in H12. destruct H12. auto.
      forwards: ord_lc H. forwards:split_ord_false H8 H3 H. contradiction.
      forwards: ord_lc H. forwards:split_ord_false H6 H3 H. contradiction.
    + inversion S1;subst;auto. inversion S2;subst;auto.
      simpl in SizeInd. inversion H;subst. forwards: IH H0 H6 H8. lia. auto.
      forwards: ord_lc H. forwards:split_ord_false H5 H1 H. contradiction.
      forwards: ord_lc H. forwards:split_ord_false H4 H1 H. contradiction.
    + inversion S1;subst;auto. inversion S2;subst;auto.
      simpl in SizeInd. inversion H;subst. apply TL_all with (union L (union L0 (union L1 L2))).
      intros. assert(disjoint ((X, B0) :: D) (B1 -^ X) (B2 -^ X)). rewrite_env(nil++[(X,B0)]++D).
      apply disjoint_narrowing with (t_and A1 A2). simpl. auto. apply S_and with A1 A2. eauto.
      auto. auto. assert(algo_sub ((X, B0) :: D) (B1 -^ X) (B3 -^ X)). auto.
      assert(algo_sub ((X, B0) :: D) (B2 -^ X) (B3 -^ X)). auto. forwards*: IH H4 H10 H14.
      rewrite size_typ_open_typ_wrt_typ_var.
      rewrite size_typ_open_typ_wrt_typ_var.
      rewrite size_typ_open_typ_wrt_typ_var. lia.
      forwards: ord_lc H. forwards:split_ord_false H8 H3 H. contradiction.
      forwards: ord_lc H. forwards:split_ord_false H6 H3 H. contradiction.
    + inversion S1;subst;auto. forwards: bot_or_var S2. destruct H2.
      forwards: botlike_sub H2 H1. eauto. destruct H2.
      forwards: bot_or_var_2 H2 H1. destruct H4. eauto.
      destruct H4. forwards*: TCW_no_rec H3 H4 H0; intuition eauto. auto.
      auto. forwards: ord_lc H. forwards*: split_ord_false H5 H2 H. intuition eauto.
    + inversion S2;subst;auto. forwards: bot_or_var S1. destruct H2.
      forwards: botlike_sub H2 H1. eauto. destruct H2.
      forwards: bot_or_var_2 H2 H1. destruct H4. eauto.
      destruct H4. forwards*: TCW_no_rec H3 H4 H0... auto.
      auto. forwards: ord_lc H. forwards*: split_ord_false H5 H2 H...
    + forwards: sub_inversion_split_l S1 H0 H.
      forwards: split_decrease_size H0. destruct H4. destruct H3.
      forwards*: IH H1 H3 S2... lia.
      forwards*: IH H2 H3 S2... lia.
    + forwards: sub_inversion_split_l S2 H0 H.
      forwards: split_decrease_size H0. destruct H4. destruct H3.
      forwards*: IH H1 S1 H3. lia.
      forwards*: IH H2 S1 H3. lia.
  - forwards: sub_inversion_split_r S1 H. destruct H0.
    forwards: sub_inversion_split_r S2 H. destruct H2.
    forwards: split_decrease_size H. destruct H4.
    forwards: IH Dis H0 H2. lia.
    forwards: IH Dis H1 H3. lia. eauto.
Qed.


Lemma disjoint_axiom_decidable:
  forall A B, disjoint_axiom A B \/ ~disjoint_axiom A B.
Proof.
  intros.
  assert(lc_typ A\/~lc_typ A). apply lc_decidable.
  assert(lc_typ B\/~lc_typ B). apply lc_decidable.
  destruct H. destruct H0.
  destruct A;try solve [right;unfold not;intros;inversion H1;subst;auto].
  destruct B;try solve[auto;right; unfold not; intros; inversion H1;subst;auto].
  destruct B;try solve[auto;right; unfold not; intros; inversion H1;subst;auto].
  destruct B;try solve[auto;right; unfold not; intros; inversion H1;subst;auto].
  destruct B;try solve[auto;right; unfold not; intros; inversion H1;subst;auto].
  assert({l=l0}+{~l=l0}). auto. destruct H1;subst;auto. right. unfold not. intros.
  inversion H1;subst;auto.
  right. unfold not. intros. apply disjoint_axiom_lc in H1. tauto.
  right. unfold not. intros. apply disjoint_axiom_lc in H1. tauto.
Qed.

Lemma TCW_no_contains: forall B C D E X Y, X `notin` [[B]] -> Y `notin` (union (dom D) (dom E)) -> TCWell (E ++ [(X,C)] ++ D) -> algo_sub (E ++ [(X,C)] ++ D) C (B -^ X) -> algo_sub ((map (typsubst_typ (t_tvar_f Y) X) E) ++ [(Y ,C)] ++ D) C (B -^ Y).
Proof.
  intros. assert(X `notin` [[C]]). clear H2. induction E. simpl in H1. inversion H1;subst. inversion H7;subst.
  clear H1 H5 H4 H7 H0 H. induction H6;auto.
  assert({X = X0}+{~X=X0}). auto. destruct H0;subst;auto.
  forwards: binds_dom_contradiction H H9. contradiction. simpl.
  pick fresh X0. assert(X `notin` [[B0 -^ X0]]). apply H0. auto. auto.
  assert(AtomSetImpl.Subset (typefv_typ B0) (typefv_typ (B0 -^ X0)) ).
  apply typefv_typ_open_typ_wrt_typ_rec_lower_mutual.
  assert(X `notin` [[B0]]). auto. auto.
  inversion H1;subst. auto.
  assert(open_typ_wrt_typ (close_typ_wrt_typ X C) (t_tvar_f X) = C).
  apply open_typ_wrt_typ_close_typ_wrt_typ.
  assert(algo_sub (E ++ X ~ C ++ D) (close_typ_wrt_typ X C -^ X) (B -^ X)).
  rewrite H4. auto.
  assert(algo_sub (map (typsubst_typ (t_tvar_f Y) X) E ++ Y ~ C ++ D) (close_typ_wrt_typ X C -^ Y) (B -^ Y)).
  apply algo_sub_rename. auto. auto. auto.
  assert ((close_typ_wrt_typ X C -^ Y) = C).
  apply Degree_subst. auto. apply degree_typ_wrt_typ_of_lc_typ. auto.
  rewrite H7 in H6. auto.
Qed.

Lemma TCW_no_contains_2: forall A0 B C D E X Y X1,
    X `notin` [[B]] -> Y `notin` (union (dom D) (dom E)) ->
    TCWell (E ++ [(X,C)] ++ D) -> binds X1 A0 (E ++ [(X,C)] ++ D) ->
    algo_sub (E ++ [(X,C)] ++ D) A0 (B -^ X) -> X <> X1 ->
    algo_sub ((map (typsubst_typ (t_tvar_f Y) X) E) ++ [(Y ,C)] ++ D) (typsubst_typ (t_tvar_f Y) X A0) (B -^ Y)/\binds X1 (typsubst_typ (t_tvar_f Y) X A0) ((map (typsubst_typ (t_tvar_f Y) X) E) ++ [(Y,C)] ++ D).
Proof.
  intros. split.
  assert(open_typ_wrt_typ (close_typ_wrt_typ X A0) (t_tvar_f X) = A0).
  apply open_typ_wrt_typ_close_typ_wrt_typ.
  assert(typsubst_typ (t_tvar_f Y) X A0 = open_typ_wrt_typ_rec 0 (t_tvar_f Y) (close_typ_wrt_typ_rec 0 X A0)).
  apply typsubst_typ_spec_rec. rewrite H6.
  apply algo_sub_rename. auto. auto. rewrite open_typ_wrt_typ_close_typ_wrt_typ. auto.
  apply TCW_binds_2. auto. auto. auto.
Qed.


Lemma disjoint_rename_alternative:forall n X Y (A B C:typ) (D E:tctx),
    size_typ A + size_typ B <= n
    -> X `notin`  (Metatheory.union [[A]] [[B]])
    -> Y `notin` (Metatheory.union (dom D) (dom E))
    -> disjoint (E ++ [(X , C)] ++ D) (A -^ X) (B -^ X)
    -> disjoint ((map (typsubst_typ (t_tvar_f Y) X) E) ++ [(Y ,C)] ++ D) (A -^ Y) (B -^ Y).
Proof.
  intros n. induction n. intros. destruct A;inversion H.
  intros. dependent induction H2.
  - (* axiom *)
    assert(disjoint_axiom (A -^ Y) (B -^ Y)).
    forwards: disjoint_axiom_lc H2. destruct H6.
    assert(lc_typ (A -^ Y)). apply lc_typ_rename_2 with X. auto.
    assert(lc_typ (B -^ Y)). apply lc_typ_rename_2 with X. auto.
    dependent induction H2;auto.
    destruct B;inversion x. unfold open_typ_wrt_typ in x. simpl in x.
    destruct(lt_eq_lt_dec n0 0). destruct s. inversion x. inversion x. inversion x.
    destruct A;inversion x0. unfold open_typ_wrt_typ in x0. simpl in x0.
    destruct(lt_eq_lt_dec n0 0). destruct s. inversion x0. inversion x0. inversion x0.
    unfold open_typ_wrt_typ. simpl. subst. auto. unfold open_typ_wrt_typ in H9. unfold open_typ_wrt_typ in H10. simpl in H9. simpl in H10. auto.
    destruct B;inversion x. unfold open_typ_wrt_typ in x. simpl in x.
    destruct(lt_eq_lt_dec n0 0). destruct s. inversion x. inversion x. inversion x.
    destruct A;inversion x0. unfold open_typ_wrt_typ in x0. simpl in x0.
    destruct(lt_eq_lt_dec n0 0). destruct s. inversion x0. inversion x0. inversion x0.
    unfold open_typ_wrt_typ. simpl. subst. auto. unfold open_typ_wrt_typ in H8. unfold open_typ_wrt_typ in H9. simpl in H8. simpl in H9. auto.
    destruct B;inversion x. unfold open_typ_wrt_typ in x. simpl in x.
    destruct(lt_eq_lt_dec n0 0). destruct s. inversion x. inversion x. inversion x.
    destruct A;inversion x0. unfold open_typ_wrt_typ in x0. simpl in x0.
    destruct(lt_eq_lt_dec n0 0). destruct s. inversion x0. inversion x0. inversion x0.
    unfold open_typ_wrt_typ. simpl. subst. auto. unfold open_typ_wrt_typ in H9. unfold open_typ_wrt_typ in H10. simpl in H9. simpl in H10. auto.
    destruct B;inversion x. unfold open_typ_wrt_typ in x. simpl in x.
    destruct(lt_eq_lt_dec n0 0). destruct s. inversion x. inversion x. inversion x.
    destruct A;inversion x0. unfold open_typ_wrt_typ in x0. simpl in x0.
    destruct(lt_eq_lt_dec n0 0). destruct s. inversion x0. inversion x0. inversion x0.
    unfold open_typ_wrt_typ. simpl. subst. auto. unfold open_typ_wrt_typ in H10. unfold open_typ_wrt_typ in H11. simpl in H10. simpl in H11. auto.
    destruct B;inversion x. unfold open_typ_wrt_typ in x. simpl in x.
    destruct(lt_eq_lt_dec n0 0). destruct s. inversion x. inversion x. inversion x.
    destruct A;inversion x0. unfold open_typ_wrt_typ in x0. simpl in x0.
    destruct(lt_eq_lt_dec n0 0). destruct s. inversion x0. inversion x0. inversion x0.
    unfold open_typ_wrt_typ. simpl. subst. auto. unfold open_typ_wrt_typ in H11. unfold open_typ_wrt_typ in H12. simpl in H11. simpl in H12. auto.
    destruct B;inversion x. unfold open_typ_wrt_typ in x. simpl in x.
    destruct(lt_eq_lt_dec n0 0). destruct s. inversion x. inversion x. inversion x.
    destruct A;inversion x0. unfold open_typ_wrt_typ in x0. simpl in x0.
    destruct(lt_eq_lt_dec n0 0). destruct s. inversion x0. inversion x0. inversion x0.
    unfold open_typ_wrt_typ. simpl. subst. auto. unfold open_typ_wrt_typ in H10. unfold open_typ_wrt_typ in H11. simpl in H10. simpl in H11. auto.
    destruct B;inversion x. unfold open_typ_wrt_typ in x. simpl in x.
    destruct(lt_eq_lt_dec n0 0). destruct s. inversion x. inversion x. inversion x.
    destruct A;inversion x0. unfold open_typ_wrt_typ in x0. simpl in x0.
    destruct(lt_eq_lt_dec n0 0). destruct s. inversion x0. inversion x0. inversion x0.
    unfold open_typ_wrt_typ. simpl. subst. auto. unfold open_typ_wrt_typ in H9. unfold open_typ_wrt_typ in H10. simpl in H9. simpl in H10. auto.
    destruct B;inversion x. unfold open_typ_wrt_typ in x. simpl in x.
    destruct(lt_eq_lt_dec n0 0). destruct s. inversion x. inversion x. inversion x.
    destruct A;inversion x0. unfold open_typ_wrt_typ in x0. simpl in x0.
    destruct(lt_eq_lt_dec n0 0). destruct s. inversion x0. inversion x0. inversion x0.
    unfold open_typ_wrt_typ. simpl. subst. auto. unfold open_typ_wrt_typ in H8. unfold open_typ_wrt_typ in H9. simpl in H8. simpl in H9. auto.
    destruct B;inversion x. unfold open_typ_wrt_typ in x. simpl in x.
    destruct(lt_eq_lt_dec n0 0). destruct s. inversion x. inversion x. inversion x.
    destruct A;inversion x0. unfold open_typ_wrt_typ in x0. simpl in x0.
    destruct(lt_eq_lt_dec n0 0). destruct s. inversion x0. inversion x0. inversion x0.
    unfold open_typ_wrt_typ. simpl. subst. auto. unfold open_typ_wrt_typ in H9. unfold open_typ_wrt_typ in H10. simpl in H9. simpl in H10. auto.
    destruct B;inversion x. unfold open_typ_wrt_typ in x. simpl in x.
    destruct(lt_eq_lt_dec n0 0). destruct s. inversion x. inversion x. inversion x.
    destruct A;inversion x0. unfold open_typ_wrt_typ in x0. simpl in x0.
    destruct(lt_eq_lt_dec n0 0). destruct s. inversion x0. inversion x0. inversion x0.
    unfold open_typ_wrt_typ. simpl. subst. auto. unfold open_typ_wrt_typ in H10. unfold open_typ_wrt_typ in H11. simpl in H10. simpl in H11. auto.
    destruct B;inversion x. unfold open_typ_wrt_typ in x. simpl in x.
    destruct(lt_eq_lt_dec n0 0). destruct s. inversion x. inversion x. inversion x.
    destruct A;inversion x0. unfold open_typ_wrt_typ in x0. simpl in x0.
    destruct(lt_eq_lt_dec n0 0). destruct s. inversion x0. inversion x0. inversion x0.
    unfold open_typ_wrt_typ. simpl. subst. auto. unfold open_typ_wrt_typ in H11. unfold open_typ_wrt_typ in H12. simpl in H11. simpl in H12. auto.
    destruct B;inversion x. unfold open_typ_wrt_typ in x. simpl in x.
    destruct(lt_eq_lt_dec n0 0). destruct s. inversion x. inversion x. inversion x.
    destruct A;inversion x0. unfold open_typ_wrt_typ in x0. simpl in x0.
    destruct(lt_eq_lt_dec n0 0). destruct s. inversion x0. inversion x0. inversion x0.
    unfold open_typ_wrt_typ. simpl. subst. auto. unfold open_typ_wrt_typ in H10. unfold open_typ_wrt_typ in H11. simpl in H10. simpl in H11. auto.
    destruct B;inversion x. unfold open_typ_wrt_typ in x. simpl in x.
    destruct(lt_eq_lt_dec n0 0). destruct s. inversion x. inversion x. inversion x.
    destruct A;inversion x0. unfold open_typ_wrt_typ in x0. simpl in x0.
    destruct(lt_eq_lt_dec n0 0). destruct s. inversion x0. inversion x0. inversion x0.
    unfold open_typ_wrt_typ. simpl. subst. auto. unfold open_typ_wrt_typ in H10. unfold open_typ_wrt_typ in H11. simpl in H10. simpl in H11. auto.
    assert(TWell (map (typsubst_typ (t_tvar_f Y) X) E ++ [(Y,C)] ++ D) (A -^ Y)). apply TW_subst. auto. auto. auto. auto.
    assert(TWell (map (typsubst_typ (t_tvar_f Y) X) E ++ [(Y,C)] ++ D) (B -^ Y)). apply TW_subst. auto. auto. auto. auto.
    assert(TCWell (map (typsubst_typ (t_tvar_f Y) X) E ++ [(Y,C)] ++ D)). apply TCW_subst. auto. auto. auto.
  - (* topl *)
    assert(topLike (map (typsubst_typ (t_tvar_f Y) X) E ++ Y ~ C ++ D) (A -^ Y)). apply topLike_subst. auto. auto. auto.
    assert(TWell (map (typsubst_typ (t_tvar_f Y) X) E ++ [(Y,C)] ++ D) (B -^ Y)). apply TW_subst. auto. auto. apply topLike_well_tctx in H3. auto. auto.
    auto.
  - (* topr *)
    assert(topLike (map (typsubst_typ (t_tvar_f Y) X) E ++ Y ~ C ++ D) (B -^ Y)). apply topLike_subst. auto. auto. auto.
    assert(TWell (map (typsubst_typ (t_tvar_f Y) X) E ++ [(Y,C)] ++ D) (A -^ Y)). apply TW_subst. auto. auto. apply topLike_well_tctx in H3. auto. auto.
    auto.
  - (* arrow arrow *)
    destruct B;inversion x. unfold open_typ_wrt_typ in x. simpl in x.
    destruct(lt_eq_lt_dec n0 0). destruct s. inversion x. inversion x. inversion x.
    destruct A;inversion x0. unfold open_typ_wrt_typ in x0. simpl in x0.
    destruct(lt_eq_lt_dec n0 0). destruct s. inversion x0. inversion x0. inversion x0.
    assert(disjoint (map (typsubst_typ (t_tvar_f Y) X) E ++ [(Y,C)] ++ D) (A4 -^ Y) (B4 -^ Y)). apply IHdisjoint. auto.
    simpl in H. simpl. lia. simpl in H0. auto. auto. auto. auto. unfold open_typ_wrt_typ. simpl. subst. auto.
    assert(TWell (map (typsubst_typ (t_tvar_f Y) X) E ++ [(Y,C)] ++ D) (t_arrow A3 A4  -^ Y)). apply TW_subst. auto. auto. apply disjoint_well_tctx in H2. auto. rewrite <- x0. auto.
    assert(TWell (map (typsubst_typ (t_tvar_f Y) X) E ++ [(Y,C)] ++ D) (t_arrow B3 B4  -^ Y)). apply TW_subst. auto. auto. apply disjoint_well_tctx in H2. auto. rewrite <- x. auto.
    assert(TCWell (map (typsubst_typ (t_tvar_f Y) X) E ++ [(Y,C)] ++ D)). apply TCW_subst. auto. apply disjoint_well_tctx in H2. auto.
    unfold open_typ_wrt_typ. simpl.
    unfold open_typ_wrt_typ in H10. simpl in H10.
    unfold open_typ_wrt_typ in H11. simpl in H11. auto.
  - (* rcd rcd *)
    destruct B;inversion x. unfold open_typ_wrt_typ in x. simpl in x.
    destruct(lt_eq_lt_dec n0 0). destruct s. inversion x. inversion x. inversion x.
    destruct A;inversion x0. unfold open_typ_wrt_typ in x0. simpl in x0.
    destruct(lt_eq_lt_dec n0 0). destruct s. inversion x0. inversion x0. inversion x0.
    assert(disjoint (map (typsubst_typ (t_tvar_f Y) X) E ++ [(Y,C)] ++ D) (A -^ Y) (B -^ Y)). apply IHdisjoint. auto.
    simpl in H. lia. simpl in H. auto. auto. auto. auto. unfold open_typ_wrt_typ. simpl. subst. auto. subst.
    assert(TCWell (map (typsubst_typ (t_tvar_f Y) X) E ++ [(Y,C)] ++ D)). apply TCW_subst. auto. apply disjoint_well_tctx in H2. auto.
    unfold open_typ_wrt_typ. simpl. subst. auto.
  - (* forall forall *)
    destruct B;inversion x. unfold open_typ_wrt_typ in x. simpl in x.
    destruct(lt_eq_lt_dec n0 0). destruct s. inversion x. inversion x. inversion x.
    destruct A;inversion x0. unfold open_typ_wrt_typ in x0. simpl in x0.
    destruct(lt_eq_lt_dec n0 0). destruct s. inversion x0. inversion x0. inversion x0.
    subst.
    assert(disjoint (E ++ X ~ C ++ D) (t_forall A3 A4 -^ X) (t_forall B3 B4 -^ X)).
    unfold open_typ_wrt_typ. simpl. subst. eauto.
    forwards: disjoint_well_tctx H6.
    forwards: disjoint_regular H6.
    assert(TWell (map (typsubst_typ (t_tvar_f Y) X) E ++ [(Y,C)] ++ D) (t_forall A3 A4  -^ Y)). apply TW_subst. auto. auto. auto. auto.
    assert(TWell (map (typsubst_typ (t_tvar_f Y) X) E ++ [(Y,C)] ++ D) (t_forall B3 B4  -^ Y)). apply TW_subst. auto. auto. auto. auto.
    assert(TCWell (map (typsubst_typ (t_tvar_f Y) X) E ++ [(Y,C)] ++ D)). apply TCW_subst. auto. auto. auto.
    unfold open_typ_wrt_typ. simpl.
    apply D_all with (Metatheory.union (Metatheory.union L (Metatheory.singleton Y)) (Metatheory.singleton X)).
    inversion H9;subst;auto. inversion H10;subst;auto.
    intros.
    assert((open_typ_wrt_typ_rec 1 (t_tvar_f Y) A4 -^ X0) = (A4 -^ X0) -^ Y).
    apply open_comm. auto.
    assert((open_typ_wrt_typ_rec 1 (t_tvar_f Y) B4 -^ X0) = (B4 -^ X0) -^ Y).
    apply open_comm. auto.
    rewrite H13. rewrite H14.
    assert((X0, t_and (A3 -^ Y) (B3 -^ Y)) :: map (typsubst_typ (t_tvar_f Y) X) E
           = map (typsubst_typ (t_tvar_f Y) X) ((X0, t_and (A3 -^ X) (B3 -^ X)):: E) ).
    simpl.
    assert([X ~~> t_tvar_f Y] (A3 -^ X)  = [X ~~> t_tvar_f Y] (A3) ^-^  [X ~~> t_tvar_f Y] (t_tvar_f X)).
    apply typsubst_typ_open_typ_wrt_typ_rec. auto.
    rewrite H15.
    assert([X ~~> t_tvar_f Y] (B3 -^ X)  = [X ~~> t_tvar_f Y] (B3) ^-^  [X ~~> t_tvar_f Y] (t_tvar_f X)).
    apply typsubst_typ_open_typ_wrt_typ_rec. auto.
    rewrite H16.
    assert([X ~~> t_tvar_f Y] A3 = A3).
    apply typsubst_typ_fresh_eq. simpl in H0. auto.
    assert([X ~~> t_tvar_f Y] B3 = B3).
    apply typsubst_typ_fresh_eq. simpl in H0. auto.
    rewrite H17. rewrite H18.
    assert([X ~~> t_tvar_f Y] (t_tvar_f X) = t_tvar_f Y ).
    simpl. unfold "==". destruct(EqDec_eq_of_X X X);subst;auto.
    contradiction.
    rewrite H19. auto.
    assert(disjoint
             (map (typsubst_typ (t_tvar_f Y) X) ((X0, t_and (A3 -^ X) (B3 -^ X)) :: E) ++
                  [(Y, C)] ++ D) ((A4 -^ X0) -^ Y) ((B4 -^ X0) -^ Y)).
    apply IHn. rewrite size_typ_open_typ_wrt_typ_var. rewrite size_typ_open_typ_wrt_typ_var. simpl in H. lia.
    assert(X <> X0). auto. assert(X `notin` [[(t_tvar_f X0)]]). auto.
    assert(AtomSetImpl.Subset (typefv_typ (A4 -^ X0)) (typefv_typ (t_tvar_f X0) `union` typefv_typ A4)).
    apply typefv_typ_open_typ_wrt_typ_rec_upper_mutual.
    assert(AtomSetImpl.Subset (typefv_typ (B4 -^ X0)) (typefv_typ (t_tvar_f X0) `union` typefv_typ B4)).
    apply typefv_typ_open_typ_wrt_typ_rec_upper_mutual.
    simpl in H0.
    assert(X `notin` (Metatheory.union [[t_tvar_f X0]] [[A4]])). auto.
    assert(X `notin` [[A4 -^ X0]]). auto.
    assert(X `notin` (Metatheory.union [[t_tvar_f X0]] [[B4]])). auto.
    assert(X `notin` [[B4 -^ X0]]). auto.
    auto. simpl.
    assert(X0 <> Y). auto. auto.
    assert(disjoint
             ((X0,
               t_and (open_typ_wrt_typ_rec 0 (t_tvar_f X) A3)
                     (open_typ_wrt_typ_rec 0 (t_tvar_f X) B3)) :: E ++ [(X ,C)] ++ D)
             (open_typ_wrt_typ_rec 1 (t_tvar_f X) A4 -^ X0)
             (open_typ_wrt_typ_rec 1 (t_tvar_f X) B4 -^ X0)).
    auto.
    assert((open_typ_wrt_typ_rec 1 (t_tvar_f X) A4 -^ X0) = (A4 -^ X0) -^ X).
    apply open_comm. auto.
    assert((open_typ_wrt_typ_rec 1 (t_tvar_f X) B4 -^ X0) = (B4 -^ X0) -^ X).
    apply open_comm. auto.
    rewrite H17 in H16. rewrite H18 in H16. auto.
    rewrite <- H15 in H16. auto.
  - (* varl *)
    assert(TWell (map (typsubst_typ (t_tvar_f Y) X) E ++ [(Y,C)] ++ D) (A -^ Y)). apply TW_subst. auto. auto. apply algo_sub_well_tctx in H3. auto. rewrite <- x. eauto.
    assert(TWell (map (typsubst_typ (t_tvar_f Y) X) E ++ [(Y,C)] ++ D) (B -^ Y)). apply TW_subst. auto. auto. apply algo_sub_well_tctx in H3. auto. apply algo_sub_regular in H3. auto.
    assert(TCWell (map (typsubst_typ (t_tvar_f Y) X) E ++ [(Y,C)] ++ D)). apply TCW_subst. auto. apply algo_sub_well_tctx in H3. auto.
    destruct A;inversion x. unfold open_typ_wrt_typ in x. simpl in x.
    destruct(lt_eq_lt_dec n0 0). destruct s. inversion x. inversion x;subst.
    assert(A0 = C). eapply binds_unique. apply H2. eauto. apply TCWell_uniq. apply algo_sub_well_tctx in H3. auto.
    subst. apply D_varl with C. auto. apply TCW_no_contains. auto. auto. apply algo_sub_well_tctx in H3. auto. auto.
    inversion x. subst.
    assert(X<>X1). simpl in H0. auto.
    assert(algo_sub ((map (typsubst_typ (t_tvar_f Y) X) E) ++ [(Y ,C)] ++ D) (typsubst_typ (t_tvar_f Y) X A0) (B -^ Y)/\binds X1 (typsubst_typ (t_tvar_f Y) X A0) ((map (typsubst_typ (t_tvar_f Y) X) E) ++ [(Y,C)] ++ D)).
    apply TCW_no_contains_2. auto. auto. apply algo_sub_well_tctx in H3. auto. auto. auto. auto. destruct H8.
    apply D_varl with ([X ~~> t_tvar_f Y] (A0)). auto. auto.
  - (* varr *)
    assert(TWell (map (typsubst_typ (t_tvar_f Y) X) E ++ [(Y,C)] ++ D) (A -^ Y)). apply TW_subst. auto. auto. apply algo_sub_well_tctx in H3. auto. apply algo_sub_regular in H3. auto.
    assert(TWell (map (typsubst_typ (t_tvar_f Y) X) E ++ [(Y,C)] ++ D) (B -^ Y)). apply TW_subst. auto. auto. apply algo_sub_well_tctx in H3. auto. rewrite <- x. eauto.
    assert(TCWell (map (typsubst_typ (t_tvar_f Y) X) E ++ [(Y,C)] ++ D)). apply TCW_subst. auto. apply algo_sub_well_tctx in H3. auto.
    destruct B;inversion x. unfold open_typ_wrt_typ in x. simpl in x.
    destruct(lt_eq_lt_dec n0 0). destruct s. inversion x. inversion x;subst.
    assert(A0 = C). eapply binds_unique. apply H2. eauto. apply TCWell_uniq. apply algo_sub_well_tctx in H3. auto.
    subst. apply D_varr with C. auto. apply TCW_no_contains. auto. auto. apply algo_sub_well_tctx in H3. auto. auto.
    inversion x. subst.
    assert(X<>X1). simpl in H0. auto.
    assert(algo_sub ((map (typsubst_typ (t_tvar_f Y) X) E) ++ [(Y ,C)] ++ D) (typsubst_typ (t_tvar_f Y) X A0) (A -^ Y)/\binds X1 (typsubst_typ (t_tvar_f Y) X A0) ((map (typsubst_typ (t_tvar_f Y) X) E) ++ [(Y,C)] ++ D)).
    apply TCW_no_contains_2. auto. auto. apply algo_sub_well_tctx in H3. auto. auto. auto. auto. destruct H8.
    apply D_varr with ([X ~~> t_tvar_f Y] (A0)). auto. auto.
  - (* andl *)
    clear IHdisjoint1 IHdisjoint2.
    forwards: open_spl H2. destruct H3. destruct H3.
    assert(spl (A -^ X) (x -^ X) (x0 -^ X)). auto.
    assert(spl (A -^ Y) (x -^ Y) (x0 -^ Y)). auto.
    pick fresh Z.
    assert(spl (A -^ Z) (x -^ Z) (x0 -^ Z)). auto.
    forwards: split_unique H2 H4. destruct H7;subst.
    assert(disjoint (map (typsubst_typ (t_tvar_f Y) X) E ++ [(Y, C)] ++ D) (x -^ Y) (B -^ Y)).
    apply IHn. apply split_decrease_size in H2. destruct H2.
    rewrite size_typ_open_typ_wrt_typ_var in H2. rewrite size_typ_open_typ_wrt_typ_var in H2. lia.
    assert(X `notin` [[(A -^ Z)]]). assert(X<>Z). auto.
    assert(AtomSetImpl.Subset (typefv_typ (A -^ Z)) (typefv_typ (t_tvar_f Z) `union` typefv_typ A)).
    apply typefv_typ_open_typ_wrt_typ_rec_upper_mutual.
    assert(X `notin` (Metatheory.union [[t_tvar_f Z]] [[A]])). auto. auto.
    forwards: split_fv H7 H6. destruct H8.
    assert(AtomSetImpl.Subset (typefv_typ x) (typefv_typ (x -^ Z))).
    apply typefv_typ_open_typ_wrt_typ_rec_lower_mutual.
    auto. auto. auto.
    assert(disjoint (map (typsubst_typ (t_tvar_f Y) X) E ++ [(Y, C)] ++ D) (x0 -^ Y) (B -^ Y)).
    apply IHn. apply split_decrease_size in H2. destruct H2.
    rewrite size_typ_open_typ_wrt_typ_var in H8. rewrite size_typ_open_typ_wrt_typ_var in H8. lia.
    assert(X `notin` [[(A -^ Z)]]). assert(X<>Z). auto.
    assert(AtomSetImpl.Subset (typefv_typ (A -^ Z)) (typefv_typ (t_tvar_f Z) `union` typefv_typ A)).
    apply typefv_typ_open_typ_wrt_typ_rec_upper_mutual.
    assert(X `notin` (Metatheory.union [[t_tvar_f Z]] [[A]])). auto. auto.
    forwards: split_fv H8 H6. destruct H9.
    assert(AtomSetImpl.Subset (typefv_typ x0) (typefv_typ (x0 -^ Z))).
    apply typefv_typ_open_typ_wrt_typ_rec_lower_mutual.
    auto. auto. auto. auto.
  - (* andr *)
    clear IHdisjoint1 IHdisjoint2.
    forwards: open_spl H2. destruct H3. destruct H3.
    assert(spl (B -^ X) (x -^ X) (x0 -^ X)). auto.
    assert(spl (B -^ Y) (x -^ Y) (x0 -^ Y)). auto.
    pick fresh Z.
    assert(spl (B -^ Z) (x -^ Z) (x0 -^ Z)). auto.
    forwards: split_unique H2 H4. destruct H7;subst.
    assert(disjoint (map (typsubst_typ (t_tvar_f Y) X) E ++ [(Y, C)] ++ D) (A -^ Y) (x -^ Y)).
    apply IHn. apply split_decrease_size in H2. destruct H2.
    rewrite size_typ_open_typ_wrt_typ_var in H2. rewrite size_typ_open_typ_wrt_typ_var in H2. lia.
    assert(X `notin` [[(B -^ Z)]]). assert(X<>Z). auto.
    assert(AtomSetImpl.Subset (typefv_typ (B -^ Z)) (typefv_typ (t_tvar_f Z) `union` typefv_typ B)).
    apply typefv_typ_open_typ_wrt_typ_rec_upper_mutual.
    assert(X `notin` (Metatheory.union [[t_tvar_f Z]] [[B]])). auto. auto.
    forwards: split_fv H7 H6. destruct H8.
    assert(AtomSetImpl.Subset (typefv_typ x) (typefv_typ (x -^ Z))).
    apply typefv_typ_open_typ_wrt_typ_rec_lower_mutual.
    auto. auto. auto.
    assert(disjoint (map (typsubst_typ (t_tvar_f Y) X) E ++ [(Y, C)] ++ D) (A -^ Y) (x0 -^ Y)).
    apply IHn. apply split_decrease_size in H2. destruct H2.
    rewrite size_typ_open_typ_wrt_typ_var in H8. rewrite size_typ_open_typ_wrt_typ_var in H8. lia.
    assert(X `notin` [[(B -^ Z)]]). assert(X<>Z). auto.
    assert(AtomSetImpl.Subset (typefv_typ (B -^ Z)) (typefv_typ (t_tvar_f Z) `union` typefv_typ B)).
    apply typefv_typ_open_typ_wrt_typ_rec_upper_mutual.
    assert(X `notin` (Metatheory.union [[t_tvar_f Z]] [[B]])). auto. auto.
    forwards: split_fv H8 H6. destruct H9.
    assert(AtomSetImpl.Subset (typefv_typ x0) (typefv_typ (x0 -^ Z))).
    apply typefv_typ_open_typ_wrt_typ_rec_lower_mutual.
    auto. auto. auto. auto.
Qed.

Lemma disjoint_rename:forall X Y (A B C:typ) (D E:tctx),
    X `notin`  (Metatheory.union [[A]] [[B]])
    -> Y `notin` (Metatheory.union (dom D) (dom E))
    -> disjoint (E ++ [(X , C)] ++ D) (A -^ X) (B -^ X)
    -> disjoint ((map (typsubst_typ (t_tvar_f Y) X) E) ++ [(Y ,C)] ++ D) (A -^ Y) (B -^ Y).
Proof.
  intros. forwards: disjoint_rename_alternative H H0 H1. eauto. auto.
Qed.

Lemma disjoint_simpl_rename:forall X Y (A B C:typ) (D E:tctx),
    X `notin`  (Metatheory.union [[A]] [[B]])
    -> Y `notin`  (dom D)
    -> disjoint ([(X , C)] ++ D) (A -^ X) (B -^ X)
    -> disjoint ([(Y ,C)] ++ D) (A -^ Y) (B -^ Y).
Proof.
  intros.
  assert(nil ++ [(X ,C)] ++ D = [(X ,C)] ++ D ). auto.
  rewrite <- H2 in H1.
  apply disjoint_rename with X Y A B C D nil in H1. auto. auto. auto.
Qed.

Lemma disjoint_forall_inv: forall D B1 C1 B2 C2,
  disjoint D (t_forall B1 C1) (t_forall B2 C2) ->
  (forall X, X#D -> disjoint (cons (X, t_and B1 B2) D) (C1 -^ X) (C2 -^ X)).
Proof.
  intros. dependent induction H;subst.
    -
    inversion H2.
    -
    inversion H0;subst. inversion H;subst.
    pick fresh Y.
    assert(topLike ((Y, B1) :: D) (C1 -^ Y)). auto.
    assert(topLike ((Y, t_and B1 B2) :: D) (C1 -^ Y)). rewrite_env(nil ++ [(Y, t_and B1 B2)] ++ D).
    apply topLike_bind_weakening with B1. auto.
    forwards: topLike_well_tctx H0.
    forwards: topLike_regular H0. auto.
    assert(topLike ((X, t_and B1 B2) :: D) (C1 -^ X)).
    apply topLike_simpl_subst with Y. auto. auto. auto.
    assert(TWell ((X,  B2) :: D) (C2 -^ X)).
    apply TWell_all_open with B2.
    rewrite_env(nil ++ [(X,B2)] ++ D). apply TWell_weakening.
    auto. eauto.
    assert(TWell ((X, t_and B1 B2) :: D) (C2 -^ X)).
    rewrite_env(nil ++ [(X, t_and B1 B2)] ++ D).
    apply TWell_bind_weakening with B2. auto. auto.
    -
    inversion H0;subst. inversion H;subst.
    pick fresh Y.
    assert(topLike ((Y, B2) :: D) (C2 -^ Y)). auto.
    assert(topLike ((Y, t_and B1 B2) :: D) (C2 -^ Y)). rewrite_env(nil ++ [(Y, t_and B1 B2)] ++ D).
    apply topLike_bind_weakening with B2. auto.
    forwards: topLike_well_tctx H0.
    forwards: topLike_regular H0. auto.
    assert(topLike ((X, t_and B1 B2) :: D) (C2 -^ X)).
    apply topLike_simpl_subst with Y. auto. auto. auto.
    assert(TWell ((X,  B1) :: D) (C1 -^ X)).
    apply TWell_all_open with B1.
    rewrite_env(nil ++ [(X,B1)] ++ D). apply TWell_weakening.
    auto. eauto.
    assert(TWell ((X, t_and B1 B2) :: D) (C1 -^ X)).
    rewrite_env(nil ++ [(X, t_and B1 B2)] ++ D).
    apply TWell_bind_weakening with B1. auto. auto.
  - pick fresh Y. assert(disjoint ((Y, t_and B1 B2) :: D) (C1 -^ Y) (C2 -^ Y)). auto.
    apply disjoint_simpl_rename with Y. auto. auto. auto. auto.
  -
    inversion H;subst.
    assert(disjoint ((X, t_and B1 B2) :: D) (C0 -^ X) (C2 -^ X)). auto.
    assert(disjoint ((X, t_and B1 B2) :: D) (C3 -^ X) (C2 -^ X)). auto.
    assert(spl (C1 -^ X) (C0 -^ X) (C3 -^ X)). apply open_spl_2 with L. auto. auto. auto.
  -
    inversion H;subst.
    assert(disjoint ((X, t_and B1 B2) :: D) (C1 -^ X) (C0 -^ X)). auto.
    assert(disjoint ((X, t_and B1 B2) :: D) (C1 -^ X) (C3 -^ X)). auto.
    assert(spl (C2 -^ X) (C0 -^ X) (C3 -^ X)). apply open_spl_2 with L. auto. auto. auto.
Qed.


Lemma TWell_disjoint_weakening: forall X J A1 A2 D E, X `notin` [[A2]] -> TWell (E ++ [(X, A1)] ++ D) (A2 -^ X)
-> TWell D J -> TWell (map (typsubst_typ J X)E  ++ D) (A2 ^-^ J).
Proof.
  intros.
    forwards: TWell_subst H1 H0.
    assert([X ~~> J] (A2 -^ X)  = [X ~~> J] (A2) ^-^  [X ~~> J] (t_tvar_f X)).
    apply typsubst_typ_open_typ_wrt_typ_rec. eauto.
    rewrite H3 in H2.
    assert([X ~~> J] A2 = A2).
    apply typsubst_typ_fresh_eq. auto.
    rewrite H4 in H2.
    assert([X ~~> J] (t_tvar_f X) = J).
    simpl. unfold "==". destruct (EqDec_eq_of_X X X). auto. contradiction. rewrite H5 in H2. auto.
Qed.

Lemma TCWell_strengening : forall x A D F J,
    TCWell (F ++ x ~ A ++ D) ->
    TWell D J ->
    TCWell (map (typsubst_typ J x) F ++ D).
Proof with simpl_env; eauto.
  intros. induction F. inversion H;subst;auto.
    destruct a. inversion H;subst.
    simpl.
    apply TCW_cons. apply IHF. auto.
     assert(close_typ_wrt_typ_rec 0 x t -^ x = t). apply open_typ_wrt_typ_close_typ_wrt_typ.
    rewrite <- H1.
    apply TWell_subst with A. auto.
    rewrite H1. auto.
    assert(TCWell (map (typsubst_typ J x) F ++ D)). auto. apply TCWell_uniq in H1.
    apply uniq_push. auto. inversion H6;subst. auto.
Qed.

Lemma botLike_disjointness: forall D A B, botLike A -> disjoint D A B -> topLike D B.
Proof.
  intros.
    dependent induction H0;auto;try solve [inversion H].
  - (* axiom *)
    inversion H;subst;inversion H3.
  - (* topLike *)
    forwards*: top_bot_false H1 H; intuition eauto.
  - (* var *)
    forwards*: botlike_sub H H1; intuition eauto.
  - (* spl l *)
    inversion H0;subst;inversion H;auto.
  - (* spl r *)
    forwards*: IHdisjoint1; intuition eauto.
Qed.

Lemma botLike_subst_1 : forall A B X,
    lc_typ B ->
    botLike A ->
    botLike [X ~~> B] A.
Proof.
  intros. inductions H0; simpls; eauto.
  applys* BL_andl. eauto with lngen.
  applys* BL_andr. eauto with lngen.
Qed.


Lemma topLike_subst_1 : forall X I J D A F,
    topLike (F ++ (X ~ I) ++ D) A ->
    disjoint D I J ->
    topLike (map (typsubst_typ J X) F ++ D) ((typsubst_typ J X) A).
Proof with eauto using TCWell_strengening, TWell_subst_1, botLike_subst_2.
  introv TL Dis. remember (F ++ (X ~ I) ++ D) as G. gen F.
  inductions TL; intros; simpls; substs...
  - pick fresh Y and apply TL_all...
    instantiate_cofinites.
    forwards*: H0 ((Y, A) :: F).
    simpls. rewrites typsubst_typ_open_typ_wrt_typ_var...
  - case_if; substs.
    + forwards*: binds_mid_eq H0; substs.
      forwards*: botLike_disjointness.
      rewrite_env (nil ++ map (typsubst_typ J X) F ++ D).
      applys topLike_weakening...
    + analyze_binds H0...
      applys TL_var...
      forwards*: botLike_subst_1 J X H1.
Qed.


Lemma algo_sub_disjoint_weakening : forall x I J D A B F,
    x `notin` (union [[A]] [[B]]) ->
    algo_sub (F ++ (x ~ I) ++ D) (A -^ x) (B -^ x)->
    disjoint D I J ->
    algo_sub (map (typsubst_typ J x) F ++ D) (A ^-^ J) (B ^-^ J).
Proof.
    intros. remember (F ++ (x ~ I) ++ D) as G. gen F. dependent induction H0; intros; subst.
    -  destruct B;inversion x. unfold open_typ_wrt_typ in x. simpl in x.
        destruct(lt_eq_lt_dec n 0). destruct s. inversion x. inversion x;subst.
       destruct A;inversion x1. unfold open_typ_wrt_typ in x1. simpl in x1.
        destruct(lt_eq_lt_dec n 0). destruct s. inversion x1. inversion x1;subst.
       unfold open_typ_wrt_typ. simpl.
        assert(TWell (map (typsubst_typ J x0) F ++ D) J).
        rewrite_env(nil ++ (map (typsubst_typ J x0) F) ++ D).
        apply TWell_weakening. apply disjoint_regular in H2. auto.
       apply disjoint_regular in H2. destruct H2.
       forwards: TCWell_strengening H1 H6. auto.
       inversion x1. subst. simpl in H.
       assert(X<>X). auto. contradiction.
       inversion x. subst.
       destruct A;inversion x1. unfold open_typ_wrt_typ in x1. simpl in x1.
        destruct(lt_eq_lt_dec n 0). destruct s. inversion x1. inversion x1;subst.
       simpl in H.
       assert(x0<>x0). auto. contradiction. inversion x1. subst.
       apply disjoint_regular in H2. destruct H2.
       forwards: TCWell_strengening H1 H3. eauto.
       assert(x0<>X). simpl in H. auto. inversion H0;subst.
       
       forwards: TCW_binds_3 H1 H3 H8 H5.
       unfold open_typ_wrt_typ. simpl. eauto.
    -  destruct B;inversion x. unfold open_typ_wrt_typ in x. simpl in x.
        destruct(lt_eq_lt_dec n 0). destruct s. inversion x. inversion x. inversion x.
       destruct A;inversion x1. unfold open_typ_wrt_typ in x1. simpl in x1.
        destruct(lt_eq_lt_dec n 0). destruct s. inversion x1. inversion x1. inversion x1.
       apply disjoint_regular in H1. destruct H1.
       forwards: TCWell_strengening H0 H2. eauto.
    -  forwards: topLike_subst_1 H1 H3. auto.
       rewrite <- (@typsubst_typ_intro x) in H4; auto.
       apply disjoint_regular in H3. destruct H3.
       forwards: TWell_disjoint_weakening H2 H5. auto. auto.
    -  destruct A;inversion x. unfold open_typ_wrt_typ in x. simpl in x.
        destruct(lt_eq_lt_dec n 0). destruct s. inversion x. inversion x. inversion x.
       apply disjoint_regular in H3. destruct H3.
       forwards: TCWell_strengening H2 H4.
       forwards: TWell_disjoint_weakening H0 H4. auto. auto.
    -  destruct A;inversion x. unfold open_typ_wrt_typ in x. simpl in x.
        destruct(lt_eq_lt_dec n 0). destruct s. inversion x. inversion x. inversion x.
       subst. unfold open_typ_wrt_typ. simpl.
        assert(algo_sub (map (typsubst_typ J x0) F ++ D) (A1 ^-^ J) (B ^-^ J)). simpl in H.
       apply IHalgo_sub with(F ++ [(x0,I)] ++ D). auto. auto. auto. auto. auto. auto.
        apply disjoint_regular in H3. destruct H3.
       forwards: TWell_disjoint_weakening H2 H5. simpl in H. auto. auto.
    -  destruct A;inversion x. unfold open_typ_wrt_typ in x. simpl in x.
        destruct(lt_eq_lt_dec n 0). destruct s. inversion x. inversion x. inversion x.
       subst. unfold open_typ_wrt_typ. simpl.
        assert(algo_sub (map (typsubst_typ J x0) F ++ D) (A2 ^-^ J) (B ^-^ J)). simpl in H.
       apply IHalgo_sub with(F ++ [(x0,I)] ++ D). auto. auto. auto. auto. auto. auto.
        apply disjoint_regular in H3. destruct H3.
       forwards: TWell_disjoint_weakening H2 H5. simpl in H. auto. auto.
    -  destruct B;inversion x. unfold open_typ_wrt_typ in x. simpl in x.
        destruct(lt_eq_lt_dec n 0). destruct s. inversion x. inversion x. inversion x.
       destruct A;inversion x1. unfold open_typ_wrt_typ in x1. simpl in x1.
        destruct(lt_eq_lt_dec n 0). destruct s. inversion x1. inversion x1. inversion x1.
       subst. unfold open_typ_wrt_typ. simpl. simpl in H.
        assert(algo_sub (map (typsubst_typ J x0) F ++ D) (A4 ^-^ J) (B4 ^-^ J)).
       apply IHalgo_sub2 with (F ++ [(x0,I)] ++ D). auto. auto. auto. auto. auto. auto.
        assert(algo_sub (map (typsubst_typ J x0) F ++ D) (B3 ^-^ J) (A3 ^-^ J)).
       apply IHalgo_sub1 with (F ++ [(x0,I)] ++ D). auto. auto. auto. auto. auto. auto. auto.
    -  destruct B;inversion x. unfold open_typ_wrt_typ in x. simpl in x.
        destruct(lt_eq_lt_dec n 0). destruct s. inversion x. inversion x. inversion x.
       destruct A;inversion x1. unfold open_typ_wrt_typ in x1. simpl in x1.
        destruct(lt_eq_lt_dec n 0). destruct s. inversion x1. inversion x1. inversion x1.
       simpl in H. subst. unfold open_typ_wrt_typ. simpl.
       apply sub_forall with (union L (singleton x0)).
       intros.
       assert(open_typ_wrt_typ_rec 1 J A4 -^ X = (A4 -^ X) ^-^ J). apply open_comm_2. auto. apply disjoint_lc in H4. auto.
       assert(open_typ_wrt_typ_rec 1 J B4 -^ X = (B4 -^ X) ^-^ J). apply open_comm_2. auto. apply disjoint_lc in H4. auto.
       rewrite H6. rewrite H7.
       assert((X, open_typ_wrt_typ_rec 0 J B3) :: map (typsubst_typ J x0) F =
             map (typsubst_typ J x0) ((X, open_typ_wrt_typ_rec 0 (t_tvar_f x0) B3) ::F)).
      simpl. assert( open_typ_wrt_typ_rec 0 J B3 = [x0 ~~> J] (open_typ_wrt_typ_rec 0 (t_tvar_f x0) B3)).
      assert([x0 ~~> J] (B3 -^ x0)  = [x0 ~~> J] (B3) ^-^  [x0 ~~> J] (t_tvar_f x0)).
      apply typsubst_typ_open_typ_wrt_typ_rec. apply disjoint_lc in H4. auto.
      unfold open_typ_wrt_typ in H8.
      rewrite H8.
      assert([x0 ~~> J] B3 = B3).
      apply typsubst_typ_fresh_eq. auto.
      rewrite H9.
      assert([x0 ~~> J] (t_tvar_f x0) = J).
      simpl. unfold "==". destruct (EqDec_eq_of_X x0 x0). auto. contradiction. rewrite H10. auto.
      rewrite H8. auto. rewrite_env(((X, open_typ_wrt_typ_rec 0 J B3) :: map (typsubst_typ J x0) F) ++ D).
      rewrite H8.
      apply H2 with X ((X, open_typ_wrt_typ_rec 0 (t_tvar_f x0) B3) :: F ++ x0 ~ I ++ D).
      auto.
      assert(AtomSetImpl.Subset (typefv_typ (A4 -^ X)) (typefv_typ (t_tvar_f X)`union`  typefv_typ A4)).
      apply typefv_typ_open_typ_wrt_typ_upper.
      assert(x0 `notin` (Metatheory.union [[t_tvar_f X]] [[A4]])). auto.
      assert(AtomSetImpl.Subset (typefv_typ (B4 -^ X)) (typefv_typ (t_tvar_f X)`union`  typefv_typ B4)).
      apply typefv_typ_open_typ_wrt_typ_upper.
      assert(x0 `notin` (Metatheory.union [[t_tvar_f X]] [[B4]])). auto. auto. auto.
      apply open_comm. auto. apply open_comm. auto. auto. auto. eauto.
    -  destruct B;inversion x. unfold open_typ_wrt_typ in x. simpl in x.
        destruct(lt_eq_lt_dec n 0). destruct s. inversion x. inversion x. inversion x.
       destruct A;inversion x1. unfold open_typ_wrt_typ in x1. simpl in x1.
        destruct(lt_eq_lt_dec n 0). destruct s. inversion x1. inversion x1. inversion x1.
       subst. unfold open_typ_wrt_typ. simpl. simpl in H.
        assert(algo_sub (map (typsubst_typ J x0) F ++ D) (A ^-^ J) (B ^-^ J)).
       apply IHalgo_sub with (F ++ [(x0,I)] ++ D). auto. auto. auto. auto. auto. auto. auto.
    - forwards: open_spl_all H0. destruct H2. destruct H2.
      assert(spl (B -^ x) (x0 -^ x) (x1 -^ x)). auto.
      forwards:split_unique H0 H3. destruct H4;subst.
      pick fresh Z. assert(spl (B -^ Z) (x0 -^ Z) (x1 -^ Z)). auto.
      assert(x `notin` [[(B -^ Z)]]). assert(x<>Z). auto.
      assert(AtomSetImpl.Subset (typefv_typ (B -^ Z)) (typefv_typ (t_tvar_f Z) `union` typefv_typ B)).
      apply typefv_typ_open_typ_wrt_typ_rec_upper_mutual.
      assert(x `notin` (Metatheory.union [[t_tvar_f Z]] [[B]])). auto. auto.
      forwards: split_fv H5 H4. destruct H6.
      assert(algo_sub (map (typsubst_typ J x) F  ++ D) (A ^-^ J) (x0 ^-^ J)).
      apply IHalgo_sub1 with (F ++ x ~ I ++ D).
      assert(AtomSetImpl.Subset (typefv_typ x0) (typefv_typ (x0 -^ Z))).
      apply typefv_typ_open_typ_wrt_typ_rec_lower_mutual. auto. auto. auto. auto. auto. auto.
      assert(algo_sub (map (typsubst_typ J x) F ++ D) (A ^-^ J) (x1 ^-^ J)).
      apply IHalgo_sub2 with(F ++ x ~ I ++ D).
      assert(AtomSetImpl.Subset (typefv_typ x1) (typefv_typ (x1 -^ Z))).
      apply typefv_typ_open_typ_wrt_typ_rec_lower_mutual. auto. auto. auto. auto. auto. auto.
      assert(spl (B ^-^ J) (x0 ^-^ J) (x1 ^-^ J)). apply H2. eauto.
      eauto.
Qed.


Lemma disjoint_weakening : forall A B D E F,
    disjoint (F ++ D) A B ->
    TCWell (F ++ E ++ D) ->
    disjoint (F ++ E ++ D) A B.
Proof.
  intros. inductions H; auto.
  - forwards~: topLike_weakening E H0.
  - forwards~: topLike_weakening E H0.
  - apply syntax_ott.D_all with (union L (dom (F ++ E ++ D))) .
    forwards*: TWell_weakening H.
    forwards*: TWell_weakening H0.
    intros.
      rewrite_env(((X, t_and A1 A2) :: F) ++ E ++ D).
    apply H2. auto. auto.
      assert(disjoint ((X, t_and A1 A2) :: F ++ D) (B1 -^ X) (B2 -^ X)). auto.
      simpl. apply TCW_cons. auto. apply disjoint_well_tctx in H5.
      inversion H5;subst.
      forwards*: TWell_weakening H10.
      apply uniq_push. apply TCWell_uniq in H3. auto. auto.
  - assert(binds X A (F ++ E ++ D)). auto.
      forwards*: algo_sub_weakening H0 H1.
  - assert(binds X A (F ++ E ++ D)). auto.
      forwards*: algo_sub_weakening H0 H1.
Qed.


Lemma disjoint_disjoint_weakening : forall x I J D A B F,
    x `notin` (union [[A]] [[B]]) ->
    disjoint (F ++ (x ~ I) ++ D) (A -^ x) (B -^ x)->
    disjoint D I J ->
    disjoint (map (typsubst_typ J x) F ++ D) (A ^-^ J) (B ^-^ J).
Proof.
  intros. dependent induction H0.
  - forwards: disjoint_regular H4. destruct H5.
    forwards: TWell_disjoint_weakening H0 H6. auto.
    forwards: TWell_disjoint_weakening H1 H6. auto.
    assert(disjoint_axiom (A ^-^ J) (B ^-^ J)).
    forwards: TWell_lc_typ H7.
    forwards: TWell_lc_typ H8.
    clear H H0 H1 H3 H4 H5 H6 H7 H8.
    dependent induction H2.
    destruct B;inversion x. unfold open_typ_wrt_typ in x. simpl in x.
      destruct(lt_eq_lt_dec n 0). destruct s. inversion x. inversion x. inversion x.
    destruct A;inversion x1. unfold open_typ_wrt_typ in x1. simpl in x1.
      destruct(lt_eq_lt_dec n 0). destruct s. inversion x1. inversion x1. inversion x1.
    unfold open_typ_wrt_typ. simpl. subst. unfold open_typ_wrt_typ in H9. unfold open_typ_wrt_typ in H10. simpl in H9. simpl in H10. auto.
    destruct B;inversion x. unfold open_typ_wrt_typ in x. simpl in x.
      destruct(lt_eq_lt_dec n 0). destruct s. inversion x. inversion x. inversion x.
    destruct A;inversion x1. unfold open_typ_wrt_typ in x1. simpl in x1.
      destruct(lt_eq_lt_dec n 0). destruct s. inversion x1. inversion x1. inversion x1.
    unfold open_typ_wrt_typ. simpl. subst. unfold open_typ_wrt_typ in H9. unfold open_typ_wrt_typ in H10. simpl in H9. simpl in H10. auto.
    destruct B;inversion x. unfold open_typ_wrt_typ in x. simpl in x.
      destruct(lt_eq_lt_dec n 0). destruct s. inversion x. inversion x. inversion x.
    destruct A;inversion x1. unfold open_typ_wrt_typ in x1. simpl in x1.
      destruct(lt_eq_lt_dec n 0). destruct s. inversion x1. inversion x1. inversion x1.
    unfold open_typ_wrt_typ. simpl. subst. unfold open_typ_wrt_typ in H9. unfold open_typ_wrt_typ in H10. simpl in H9. simpl in H10. auto.    destruct B;inversion x. unfold open_typ_wrt_typ in x. simpl in x.
      destruct(lt_eq_lt_dec n 0). destruct s. inversion x. inversion x. inversion x.
    destruct A;inversion x1. unfold open_typ_wrt_typ in x1. simpl in x1.
      destruct(lt_eq_lt_dec n 0). destruct s. inversion x1. inversion x1. inversion x1.
    unfold open_typ_wrt_typ. simpl. subst. unfold open_typ_wrt_typ in H9. unfold open_typ_wrt_typ in H10. simpl in H9. simpl in H10. auto.
    destruct B;inversion x. unfold open_typ_wrt_typ in x. simpl in x.
      destruct(lt_eq_lt_dec n 0). destruct s. inversion x. inversion x. inversion x.
    destruct A;inversion x1. unfold open_typ_wrt_typ in x1. simpl in x1.
      destruct(lt_eq_lt_dec n 0). destruct s. inversion x1. inversion x1. inversion x1.
    unfold open_typ_wrt_typ. simpl. subst. unfold open_typ_wrt_typ in H9. unfold open_typ_wrt_typ in H10. simpl in H9. simpl in H10. auto.
    destruct B;inversion x. unfold open_typ_wrt_typ in x. simpl in x.
      destruct(lt_eq_lt_dec n 0). destruct s. inversion x. inversion x. inversion x.
    destruct A;inversion x1. unfold open_typ_wrt_typ in x1. simpl in x1.
      destruct(lt_eq_lt_dec n 0). destruct s. inversion x1. inversion x1. inversion x1.
    unfold open_typ_wrt_typ. simpl. subst. unfold open_typ_wrt_typ in H9. unfold open_typ_wrt_typ in H10. simpl in H9. simpl in H10. auto.
    destruct B;inversion x. unfold open_typ_wrt_typ in x. simpl in x.
      destruct(lt_eq_lt_dec n 0). destruct s. inversion x. inversion x. inversion x.
    destruct A;inversion x1. unfold open_typ_wrt_typ in x1. simpl in x1.
      destruct(lt_eq_lt_dec n 0). destruct s. inversion x1. inversion x1. inversion x1.
    unfold open_typ_wrt_typ. simpl. subst. unfold open_typ_wrt_typ in H9. unfold open_typ_wrt_typ in H10. simpl in H9. simpl in H10. auto.
    destruct B;inversion x. unfold open_typ_wrt_typ in x. simpl in x.
      destruct(lt_eq_lt_dec n 0). destruct s. inversion x. inversion x. inversion x.
    destruct A;inversion x1. unfold open_typ_wrt_typ in x1. simpl in x1.
      destruct(lt_eq_lt_dec n 0). destruct s. inversion x1. inversion x1. inversion x1.
    unfold open_typ_wrt_typ. simpl. subst. unfold open_typ_wrt_typ in H9. unfold open_typ_wrt_typ in H10. simpl in H9. simpl in H10. auto.
    destruct B;inversion x. unfold open_typ_wrt_typ in x. simpl in x.
      destruct(lt_eq_lt_dec n 0). destruct s. inversion x. inversion x. inversion x.
    destruct A;inversion x1. unfold open_typ_wrt_typ in x1. simpl in x1.
      destruct(lt_eq_lt_dec n 0). destruct s. inversion x1. inversion x1. inversion x1.
    unfold open_typ_wrt_typ. simpl. subst. unfold open_typ_wrt_typ in H9. unfold open_typ_wrt_typ in H10. simpl in H9. simpl in H10. auto.
    destruct B;inversion x. unfold open_typ_wrt_typ in x. simpl in x.
      destruct(lt_eq_lt_dec n 0). destruct s. inversion x. inversion x. inversion x.
    destruct A;inversion x1. unfold open_typ_wrt_typ in x1. simpl in x1.
      destruct(lt_eq_lt_dec n 0). destruct s. inversion x1. inversion x1. inversion x1.
    unfold open_typ_wrt_typ. simpl. subst. unfold open_typ_wrt_typ in H9. unfold open_typ_wrt_typ in H10. simpl in H9. simpl in H10. auto.
    destruct B;inversion x. unfold open_typ_wrt_typ in x. simpl in x.
      destruct(lt_eq_lt_dec n 0). destruct s. inversion x. inversion x. inversion x.
    destruct A;inversion x1. unfold open_typ_wrt_typ in x1. simpl in x1.
      destruct(lt_eq_lt_dec n 0). destruct s. inversion x1. inversion x1. inversion x1.
    unfold open_typ_wrt_typ. simpl. subst. unfold open_typ_wrt_typ in H9. unfold open_typ_wrt_typ in H10. simpl in H9. simpl in H10. auto.
    destruct B;inversion x. unfold open_typ_wrt_typ in x. simpl in x.
      destruct(lt_eq_lt_dec n 0). destruct s. inversion x. inversion x. inversion x.
    destruct A;inversion x1. unfold open_typ_wrt_typ in x1. simpl in x1.
      destruct(lt_eq_lt_dec n 0). destruct s. inversion x1. inversion x1. inversion x1.
    unfold open_typ_wrt_typ. simpl. subst. unfold open_typ_wrt_typ in H9. unfold open_typ_wrt_typ in H10. simpl in H9. simpl in H10. auto.
    destruct B;inversion x. unfold open_typ_wrt_typ in x. simpl in x.
      destruct(lt_eq_lt_dec n 0). destruct s. inversion x. inversion x. inversion x.
    destruct A;inversion x1. unfold open_typ_wrt_typ in x1. simpl in x1.
      destruct(lt_eq_lt_dec n 0). destruct s. inversion x1. inversion x1. inversion x1.
    unfold open_typ_wrt_typ. simpl. subst. unfold open_typ_wrt_typ in H9. unfold open_typ_wrt_typ in H10. simpl in H9. simpl in H10. auto.
    forwards: TCWell_strengening H3 H6. auto.
  - forwards: topLike_subst_1 H0 H2.
    rewrite <- (@typsubst_typ_intro x) in H3; auto.
    forwards(?&?): disjoint_regular H2.
    forwards:TWell_disjoint_weakening H1 H5. auto. auto.
  - forwards: topLike_subst_1 H0 H2.
    rewrite <- (@typsubst_typ_intro x) in H3; auto.
    forwards:TWell_disjoint_weakening J H1; auto.
  - destruct B;inversion x. unfold open_typ_wrt_typ in x. simpl in x.
      destruct(lt_eq_lt_dec n 0). destruct s. inversion x. inversion x. inversion x.
    destruct A;inversion x1. unfold open_typ_wrt_typ in x1. simpl in x1.
      destruct(lt_eq_lt_dec n 0). destruct s. inversion x1. inversion x1. inversion x1.
    unfold open_typ_wrt_typ. simpl.
    forwards(?&?): disjoint_regular H3.
    rewrite x1 in H2.
    rewrite x in H0.
    forwards: TWell_disjoint_weakening H2 H9. auto.
    forwards: TWell_disjoint_weakening H0 H9. auto.
    subst.
    simpl in H.
    assert(disjoint (map (typsubst_typ J x0) F ++ D) (open_typ_wrt_typ_rec 0 J A4) (open_typ_wrt_typ_rec 0 J B4)).
    eauto. auto.
  - destruct B;inversion x. unfold open_typ_wrt_typ in x. simpl in x.
      destruct(lt_eq_lt_dec n 0). destruct s. inversion x. inversion x. inversion x.
    destruct A;inversion x1. unfold open_typ_wrt_typ in x1. simpl in x1.
      destruct(lt_eq_lt_dec n 0). destruct s. inversion x1. inversion x1. inversion x1.
    subst. simpl in H.
    assert(disjoint (map (typsubst_typ J x0) F ++ D) (open_typ_wrt_typ_rec 0 J A) (open_typ_wrt_typ_rec 0 J B)).
    eauto. unfold open_typ_wrt_typ. simpl. auto.
  - destruct B;inversion x. unfold open_typ_wrt_typ in x. simpl in x.
      destruct(lt_eq_lt_dec n 0). destruct s. inversion x. inversion x. inversion x.
    destruct A;inversion x1. unfold open_typ_wrt_typ in x1. simpl in x1.
      destruct(lt_eq_lt_dec n 0). destruct s. inversion x1. inversion x1. inversion x1.
    simpl in H. subst.
    unfold open_typ_wrt_typ. simpl.
    apply syntax_ott.D_all with (union L (singleton x0)).
    apply TWell_disjoint_weakening with I. auto. auto. apply disjoint_regular in H4. auto.
    apply TWell_disjoint_weakening with I. auto. auto. apply disjoint_regular in H4. auto.
    intros.
    assert(open_typ_wrt_typ_rec 1 J A4 -^ X = (A4 -^ X) ^-^ J). apply open_comm_2. auto. apply disjoint_lc in H4. auto.
    assert(open_typ_wrt_typ_rec 1 J B4 -^ X = (B4 -^ X) ^-^ J). apply open_comm_2. auto. apply disjoint_lc in H4. auto.
    rewrite H6. rewrite H7.
    assert((X, t_and (open_typ_wrt_typ_rec 0 J A3) (open_typ_wrt_typ_rec 0 J B3)) :: map (typsubst_typ J x0) F =
             map (typsubst_typ J x0) ((X, t_and (open_typ_wrt_typ_rec 0 (t_tvar_f x0) A3)
       (open_typ_wrt_typ_rec 0 (t_tvar_f x0) B3)) ::F)).
      simpl. assert( open_typ_wrt_typ_rec 0 J B3 = [x0 ~~> J] (open_typ_wrt_typ_rec 0 (t_tvar_f x0) B3)).
      assert([x0 ~~> J] (B3 -^ x0)  = [x0 ~~> J] (B3) ^-^  [x0 ~~> J] (t_tvar_f x0)).
      apply typsubst_typ_open_typ_wrt_typ_rec. apply disjoint_lc in H4. auto.
      unfold open_typ_wrt_typ in H8.
      rewrite H8.
                                                                                                         assert([x0 ~~> J] B3 = B3).
      apply typsubst_typ_fresh_eq. auto.
      rewrite H9.
      assert([x0 ~~> J] (t_tvar_f x0) = J).
      simpl. unfold "==". destruct (EqDec_eq_of_X x0 x0). auto. contradiction. rewrite H10. auto.
      assert( open_typ_wrt_typ_rec 0 J A3 = [x0 ~~> J] (open_typ_wrt_typ_rec 0 (t_tvar_f x0) A3)).
      assert([x0 ~~> J] (A3 -^ x0)  = [x0 ~~> J] (A3) ^-^  [x0 ~~> J] (t_tvar_f x0)).
      apply typsubst_typ_open_typ_wrt_typ_rec. apply disjoint_lc in H4. auto.
      unfold open_typ_wrt_typ in H9.
      rewrite H9.
      assert([x0 ~~> J] A3 = A3).
      apply typsubst_typ_fresh_eq. auto.
      rewrite H10.
      assert([x0 ~~> J] (t_tvar_f x0) = J).
      simpl. unfold "==". destruct (EqDec_eq_of_X x0 x0). auto. contradiction. rewrite H11. auto.
      rewrite H8. rewrite H9. auto.
      rewrite_env(((X, t_and (open_typ_wrt_typ_rec 0 J A3) (open_typ_wrt_typ_rec 0 J B3)) :: map (typsubst_typ J x0) F) ++ D).
      rewrite H8. apply H2 with X I. auto.
      assert(AtomSetImpl.Subset (typefv_typ (A4 -^ X)) (typefv_typ (t_tvar_f X)`union`  typefv_typ A4)).
      apply typefv_typ_open_typ_wrt_typ_upper.
      assert(x0 `notin` (Metatheory.union [[t_tvar_f X]] [[A4]])). auto.
      assert(AtomSetImpl.Subset (typefv_typ (B4 -^ X)) (typefv_typ (t_tvar_f X)`union`  typefv_typ B4)).
      apply typefv_typ_open_typ_wrt_typ_upper.
      assert(x0 `notin` (Metatheory.union [[t_tvar_f X]] [[B4]])). auto. auto. auto.
      apply open_comm. auto. apply open_comm. auto. auto.
   - destruct A;inversion x. unfold open_typ_wrt_typ in x. simpl in x.
      destruct(lt_eq_lt_dec n 0). destruct s. inversion x. inversion x. subst.
     unfold open_typ_wrt_typ. simpl.
      assert(A0 = I). eapply binds_unique. apply H1. eauto. apply TCWell_uniq.
      apply algo_sub_well_tctx in H0. auto. subst.
     assert(close_typ_wrt_typ_rec 0 x0 I -^ x0 = I). apply open_typ_wrt_typ_close_typ_wrt_typ.
     assert(algo_sub (F ++ x0 ~ I ++ D) (close_typ_wrt_typ_rec 0 x0 I -^ x0) (B -^ x0)). rewrite H3. auto.
     forwards: algo_sub_disjoint_weakening H5 H2. auto.
     forwards: disjoint_regular H2. destruct H7.
     assert(x0#D). apply algo_sub_well_tctx in H0. apply TCWell_uniq in H0.
     clear H1 H x H2 H3 H4 H5 H6 H7 H8. induction F.
      inversion H0;subst;auto.
      destruct a. inversion H0;subst. auto.
     forwards: TW_not_in H7 H9.
      assert(close_typ_wrt_typ_rec 0 x0 I = I).
     apply close_typ_wrt_typ_lc_typ. auto. auto.
      rewrite H11 in H6.
     assert(open_typ_wrt_typ I J = I). apply open_typ_wrt_typ_lc_typ. auto.
      rewrite H12 in H6.
     apply disjoint_covariance with I.
     rewrite_env(nil ++ map (typsubst_typ J x0) F ++ D). apply disjoint_weakening.
       auto. apply algo_sub_well_tctx in H6. auto. auto.
     inversion x. subst.
       unfold open_typ_wrt_typ. simpl.
     simpl in H. assert(x0<>X0). auto.
     forwards: algo_sub_well_tctx H0.
     forwards(?&?): disjoint_regular H2.
     forwards: TCW_binds_3 H4 H6 H1 H3.
     assert(close_typ_wrt_typ_rec 0 x0 A0 -^ x0 = A0). apply open_typ_wrt_typ_close_typ_wrt_typ.
     rewrite <- H8 in H0.
     forwards: algo_sub_disjoint_weakening H0 H2. auto.
     assert([x0 ~~> J] (A0) = (close_typ_wrt_typ_rec 0 x0 A0 ^-^ J)).
     apply typsubst_typ_spec. rewrite <- H10 in H9.
     forwards: TCWell_strengening H4 H6. eauto.
   - destruct B;inversion x. unfold open_typ_wrt_typ in x. simpl in x.
      destruct(lt_eq_lt_dec n 0). destruct s. inversion x. inversion x. subst.
     unfold open_typ_wrt_typ. simpl.
      assert(A0 = I). eapply binds_unique. apply H1. eauto. apply TCWell_uniq.
      apply algo_sub_well_tctx in H0. auto. subst.
     assert(close_typ_wrt_typ_rec 0 x0 I -^ x0 = I). apply open_typ_wrt_typ_close_typ_wrt_typ.
     assert(algo_sub (F ++ x0 ~ I ++ D) (close_typ_wrt_typ_rec 0 x0 I -^ x0) (A -^ x0)). rewrite H3. auto.
     forwards: algo_sub_disjoint_weakening H5 H2. auto.
     forwards: disjoint_regular H2. destruct H7.
     assert(x0#D). apply algo_sub_well_tctx in H0. apply TCWell_uniq in H0.
     clear H1 H x H2 H3 H4 H5 H6 H7 H8. induction F.
      inversion H0;subst;auto.
      destruct a. inversion H0;subst. auto.
     forwards: TW_not_in H7 H9.
      assert(close_typ_wrt_typ_rec 0 x0 I = I).
     apply close_typ_wrt_typ_lc_typ. auto. auto.
      rewrite H11 in H6.
     assert(open_typ_wrt_typ I J = I). apply open_typ_wrt_typ_lc_typ. auto.
      rewrite H12 in H6.
     apply disjoint_symm.
     apply disjoint_covariance with I.
     rewrite_env(nil ++ map (typsubst_typ J x0) F ++ D). apply disjoint_weakening.
       apply disjoint_symm. auto. apply algo_sub_well_tctx in H6. auto. auto.
     inversion x. subst.
       unfold open_typ_wrt_typ. simpl.
     simpl in H. assert(x0<>X0). auto.
     forwards: algo_sub_well_tctx H0.
     forwards(?&?): disjoint_regular H2.
     forwards: TCW_binds_3 H4 H6 H1 H3.
     assert(close_typ_wrt_typ_rec 0 x0 A0 -^ x0 = A0). apply open_typ_wrt_typ_close_typ_wrt_typ.
     rewrite <- H8 in H0.
     forwards: algo_sub_disjoint_weakening H0 H2. auto.
     assert([x0 ~~> J] (A0) = (close_typ_wrt_typ_rec 0 x0 A0 ^-^ J)).
     apply typsubst_typ_spec. rewrite <- H10 in H9.
     forwards: TCWell_strengening H4 H6. eauto.
  - forwards(?&?&?):open_spl_all H0.
    assert(spl (A -^ x) (x0 -^ x) (x1 -^ x)). auto.
    forwards:split_unique H0 H3. destruct H4;subst.
    pick fresh Z. assert(spl (A -^ Z) (x0 -^ Z) (x1 -^ Z)). auto.
      assert(x `notin` [[(A -^ Z)]]). assert(x<>Z). auto.
    assert(AtomSetImpl.Subset (typefv_typ (A -^ Z)) (typefv_typ (t_tvar_f Z) `union` typefv_typ A)).
      apply typefv_typ_open_typ_wrt_typ_rec_upper_mutual.
    assert(x `notin` (Metatheory.union [[t_tvar_f Z]] [[A]])). auto. auto.
    forwards(?&?): split_fv H5 H4.
    assert(disjoint (map (typsubst_typ J x) F ++ D) (x0 ^-^ J) (B ^-^ J)).
    apply IHdisjoint1 with I.
    assert(AtomSetImpl.Subset (typefv_typ x0) (typefv_typ (x0 -^ Z))).
      apply typefv_typ_open_typ_wrt_typ_rec_lower_mutual. auto. auto. auto. auto. auto.
    assert(disjoint (map (typsubst_typ J x) F ++ D) (x1 ^-^ J) (B ^-^ J)).
    apply IHdisjoint2 with I.
    assert(AtomSetImpl.Subset (typefv_typ x1) (typefv_typ (x1 -^ Z))).
      apply typefv_typ_open_typ_wrt_typ_rec_lower_mutual. auto. auto. auto. auto. auto.
      assert(spl (A ^-^ J) (x0 ^-^ J) (x1 ^-^ J)). apply H2. eauto.
      eauto.
  - forwards(?&?&?):open_spl_all H0.
    assert(spl (B -^ x) (x0 -^ x) (x1 -^ x)). auto.
    forwards:split_unique H0 H3. destruct H4;subst.
    pick fresh Z. assert(spl (B -^ Z) (x0 -^ Z) (x1 -^ Z)). auto.
      assert(x `notin` [[(B -^ Z)]]). assert(x<>Z). auto.
    assert(AtomSetImpl.Subset (typefv_typ (B -^ Z)) (typefv_typ (t_tvar_f Z) `union` typefv_typ B)).
      apply typefv_typ_open_typ_wrt_typ_rec_upper_mutual.
    assert(x `notin` (Metatheory.union [[t_tvar_f Z]] [[B]])). auto. auto.
    forwards(?&?): split_fv H5 H4.
    assert(disjoint (map (typsubst_typ J x) F ++ D) (A ^-^ J) (x0 ^-^ J)).
    apply IHdisjoint1 with I.
    assert(AtomSetImpl.Subset (typefv_typ x0) (typefv_typ (x0 -^ Z))).
      apply typefv_typ_open_typ_wrt_typ_rec_lower_mutual. auto. auto. auto. auto. auto.
    assert(disjoint (map (typsubst_typ J x) F ++ D) (A ^-^ J) (x1 ^-^ J)).
    apply IHdisjoint2 with I.
    assert(AtomSetImpl.Subset (typefv_typ x1) (typefv_typ (x1 -^ Z))).
      apply typefv_typ_open_typ_wrt_typ_rec_lower_mutual. auto. auto. auto. auto. auto.
    assert(spl (B ^-^ J) (x0 ^-^ J) (x1 ^-^ J)). apply H2. auto.
    eauto.
Qed.


Ltac binds_unify :=
  repeat match goal with
  | H: uniq ?D, H1: binds ?X _ ?D , H2: binds ?X _ ?D |- _ =>
    forwards : binds_unique H1 H2 H; clear H2
  | H: TCWell ?D, H1: binds ?X _ ?D , H2: binds ?X _ ?D |- _ =>
    apply TCWell_uniq in H; forwards : binds_unique H1 H2 H; clear H2
  end; subst.

Ltac impossible_right := right; unfold not; intros HF; inverts~ HF; try binds_unify;
                         try split_unify; solve_false.

Lemma disjoint_dec_alternative: forall n D A B,
    size_typ A + size_typ B <= n -> disjoint D A B \/ ~disjoint D A B.
Proof with try binds_unify; try split_unify; solve_false.
  intros n. induction n. intros.
  - destruct A; inversion H.
  - intros.
    forwards [?|?]: TCWell_decidable D.
    forwards [?|?]: TWell_decidable D A.
    forwards [?|?]: TWell_decidable D B.
    forwards~ [?|?]: disjoint_axiom_decidable A B.
    forwards~ [?|?]: toplike_decidable D A.
    forwards~ [?|?]: toplike_decidable D B.
    forwards: TWell_lc_typ H1. forwards: TWell_lc_typ H2.
    forwards~ [HA|(?&?&?)]: ord_or_split A...
    forwards~ [HB|(?&?&?)]: ord_or_split B...
    destruct HA; destruct HB...
    1: { (* var_f var_f *)
      lets [(?&?)|?]: binds_lookup_dec X D...
      * lets [?|?]: sub_decidable D x (t_tvar_f X0). now eauto.
        lets [(?&?)|?]: binds_lookup_dec X0 D...
        ** lets [?|?]: sub_decidable D x0 (t_tvar_f X)... now eauto.
           impossible_right.
        ** impossible_right.
      * lets [(?&?)|?]: binds_lookup_dec X0 D...
        ** lets [?|?]: sub_decidable D x (t_tvar_f X)... now eauto.
           impossible_right.
        ** impossible_right. }
    1: { (* var_f bot *)
      lets [(?&?)|?]: binds_lookup_dec X D...
      lets [?|?]: sub_decidable D x t_bot.
      * eauto.
      * impossible_right.
      * impossible_right. }

    1-4: lets [(?&?)|?]: binds_lookup_dec X D; try binds_unify; solve_false;
      [ | impossible_right ];
      match goal with
      | H: binds ?X ?A ?D |- disjoint ?D (t_tvar_f ?X) ?B \/ ~ _ =>
        lets [?|?]: sub_decidable D A B
      end;
      [ now eauto | impossible_right ].

    1-6,8-9,11,14,17:
      impossible_right.

    1-2,4,6: lets [(?&?)|?]: binds_lookup_dec X D; try binds_unify; solve_false;
      [ | impossible_right ];
      match goal with
      | H: binds ?X ?A ?D |- disjoint ?D ?B (t_tvar_f ?X) \/ ~ _ =>
        lets [?|?]: sub_decidable D A B
      end;
      [ now eauto | impossible_right ].

    1:  { forwards* [?|?]: IHn D B0 B. simpl in H. lia. }

    1:  { pick fresh X. forwards [?|?]: IHn (cons (X, A & A0) D) (B0 -^ X) (B -^ X). simpl in H. repeat rewrite size_typ_open_typ_wrt_typ_var. lia.
           -
             left. apply D_all with (dom D)... intros. applys~ disjoint_simpl_rename.
           -
             right. unfold not. intros Ds. inverts Ds.
               1-3: auto.
               * pick fresh Y. forwards : H20 Y. auto.
                   forwards~: disjoint_simpl_rename Y X H13.
               * assert(ord (t_forall A B0)). { eauto. } solve_false.
               * assert(ord (t_forall A0 B)). { eauto. } solve_false. }

    1:  { forwards[?|?]: Nat_decidable l l0.
          - subst.
            forwards [?|?]: IHn D B0 B. simpl in H. lia.
            * eauto.
            * right. unfold not. intros Ds. inverts Ds;try auto.
              ** assert(ord (t_rcd l0 B0)). { eauto. } solve_false.
              ** assert(ord (t_rcd l0 B)). { eauto. } solve_false.
          - auto. }
    1: {  forwards(Sx&Sx0): split_decrease_size H8.
          forwards[Dx|Dx]: IHn D A x. lia.
            forwards[Dx0|Dx0]: IHn D A x0. lia.
          auto.
          1-2: right; unfold not; intros Ds; auto. }
    1: {  forwards(Sx&Sx0): split_decrease_size H8.
          forwards[Dx|Dx]: IHn D x B. lia.
            forwards[Dx0|Dx0]: IHn D x0 B. lia.
          auto.
          1-2: right; unfold not; intros Ds; forwards*(?&?): disjoint_andl_inv H8 Ds. }
    1-3: auto.
Qed.


Lemma disjoint_dec: forall D A B,disjoint D A B\/~disjoint D A B.
Proof.
  intros. eapply disjoint_dec_alternative. eauto.
Qed.

(* Inductive disjoint_original : tctx -> typ -> typ -> Prop :=    (* defn disjoint *)
| D_ax : forall (D:tctx) (A B:typ),
    TCWell D ->
    TWell D A ->
    TWell D B ->
    disjoint_axiom A B ->
    disjoint_original D A B
| D_topl : forall (D:tctx) (A B:typ),
    TWell D B ->
    topLike D A ->
    disjoint_original D A B
| D_topr : forall (D:tctx) (A B:typ),
    TWell D A ->
    topLike D B ->
    disjoint_original D A B
| D_arrArr : forall (D:tctx) (A1 A2 B1 B2:typ),
    TWell D (t_arrow A1 A2) ->
    TWell D (t_arrow B1 B2) ->
    disjoint_original D A2 B2 ->
    disjoint_original D (t_arrow A1 A2) (t_arrow B1 B2)
| D_rcdEq : forall (D:tctx) (l:label) (A B:typ),
    disjoint_original D A B ->
    disjoint_original D (t_rcd l A) (t_rcd l B)
| D_forall : forall (L:vars) (D:tctx) (A1 B1 A2 B2:typ),
    TWell D A1 ->
    TWell D A2 ->
    ( forall X , X \notin  L  -> disjoint_original  (cons ( X , (t_and A1 A2) )  D )   ( open_typ_wrt_typ B1 (t_tvar_f X) )   ( open_typ_wrt_typ B2 (t_tvar_f X) )  )  ->
    disjoint_original D (t_forall A1 B1) (t_forall A2 B2)
| D_varl : forall (D:tctx) (X:typevar) (B A:typ),
    binds  X A D  ->
    algo_sub D A B ->
    disjoint_original D (t_tvar_f X) B
| D_varr : forall (D:tctx) (B:typ) (X:typevar) (A:typ),
    binds  X A D  ->
    algo_sub D A B ->
    disjoint_original D B (t_tvar_f X)
| D_andl : forall (D:tctx) (A B A1 A2:typ),
    disjoint_original D A1 B ->
    disjoint_original D A2 B ->
    disjoint_original D (t_and A1 A2) B
| D_andr : forall (D:tctx) (A B B1 B2:typ),
    disjoint_original D A B1 ->
    disjoint_original D A B2 ->
    disjoint_original D A (t_and B1 B2).

#[local] Hint Constructors disjoint_original : core.

Lemma disjoint_original_regular: forall D A B,
    disjoint_original D A B -> TWell D A /\ TWell D B.
Proof.
  intros. induction* H.
  split. apply TW_all with L. auto. intros. forwards*(?&?): H2 X.
  rewrite_env(nil ++[(X,A1)] ++D). apply TWell_bind_weakening_2 with (t_and A1 A2). auto.
  apply TW_all with L. auto. intros. forwards*(?&?): H2 X.
  rewrite_env(nil ++[(X,A2)] ++D). apply TWell_bind_weakening_2 with (t_and A1 A2). auto.
Qed.

Lemma disjoint_original_well_tctx: forall D A B,
    disjoint_original D A B -> TCWell D.
Proof.
  introv H. induction* H.
  pick fresh X. forwards*: H2 X.
Qed. *)

(*
Lemma disjoint_spl_alternative: forall n D A B C E, size_typ A + size_typ E <= n -> spl A B C -> disjoint_original D B E -> disjoint_original D C E -> disjoint_original D A E.
Proof.
  intros n. induction n. intros. destruct A;inversion H.
  intros. inversion H0;subst.
  inversion H1;subst;auto.
  inversion H2;subst;auto;inversion H8;subst;auto.
  inversion H2;subst;auto. inversion H10;subst;auto.
  assert(topLike D (t_arrow A0 B0)). eauto. auto.
  inversion H6;subst. assert(disjoint_original D C1 B2). auto.
  forwards:IHn H4 H7 H13. simpl in H. lia. auto.
  assert(algo_sub D A (t_arrow A0 B0)).
  apply sub_transtivity with (t_arrow A0 C2). auto.
  forwards*(?&?):algo_sub_regular H8.
  apply D_varr with A. auto. auto.
  assert(disjoint_original D (t_arrow A0 C1) B1). auto.
  assert(disjoint_original D (t_arrow A0 C1) B2). auto.
  assert(spl (t_arrow A0 B0) (t_arrow A0 C1) (t_arrow A0 C2)). auto.
  forwards:IHn H11 H9 H7. simpl. simpl in H. lia.
  forwards:IHn H11 H10 H8. simpl. simpl in H. lia. auto.
  assert(TWell D (t_arrow A0 B0)).
  forwards(?&?):disjoint_original_regular H1.
  forwards(?&?):disjoint_original_regular H2. auto. auto.
  inversion H2;subst;auto. inversion H10;subst;auto.
  inversion H6;subst.
  assert(disjoint_original D C2 B2). auto.
  forwards:IHn H4 H11 H8. simpl in H. lia. auto.
  forwards:IHn H4 H11 H15. simpl in H. lia. auto.
  inversion H2;subst;auto. inversion H10;subst;auto.
  assert(algo_sub D A (t_arrow A0 B0)).
  apply sub_transtivity with (t_arrow A0 C1). auto.
  forwards*(?&?):algo_sub_regular H6.
  apply D_varr with A. auto. auto.
  assert(TWell D (t_arrow A0 B0)).
  forwards(?&?):disjoint_original_regular H1.
  forwards(?&?):disjoint_original_regular H2. auto. auto.
  forwards:binds_unique H5 H8. apply TCWell_uniq.
  forwards*:algo_sub_well_tctx H11.
  subst.
  assert(algo_sub D A1 (t_arrow A0 B0)). eauto.
  apply D_varr with A1. auto. auto.
  inversion H2;subst;auto. inversion H10;subst;auto.
  assert(disjoint_original D (t_arrow A0 C2) B1). auto.
  assert(disjoint_original D (t_arrow A0 C2) B2). auto.
  assert(spl (t_arrow A0 B0) (t_arrow A0 C1) (t_arrow A0 C2)). auto.
  forwards:IHn H11 H5 H9. simpl. simpl in H. lia.
  forwards:IHn H11 H6 H10. simpl. simpl in H. lia. auto.
  assert(TWell D (t_arrow A0 B0)).
  forwards(?&?):disjoint_original_regular H1.
  forwards(?&?):disjoint_original_regular H2. auto. auto.
  assert(spl (t_arrow A0 B0) (t_arrow A0 C1) (t_arrow A0 C2)). auto.
  forwards:IHn H7 H5 H11. simpl. simpl in H. lia.
  forwards:IHn H7 H6 H12. simpl. simpl in H. lia. auto.
  inversion H1;subst;auto.
  inversion H2;subst;auto;inversion H8;subst;auto.
  inversion H2;subst;auto. inversion H10;subst;auto.
  assert(topLike D (t_forall A0 B0)). eauto. auto.
  inversion H6;subst.
  apply D_forall with (union L
                             (union L0
                                    (union L1
                                           (dom D)))). auto. auto. auto. intros.
  assert(disjoint_original ((X, t_and A0 A2) :: D) (C2 -^ X) (B2 -^ X)). auto.
  assert(disjoint_original ((X, t_and A0 A2) :: D) (C1 -^ X) (B2 -^ X)).
  assert(topLike ((X, A0) :: D) (C1 -^ X)). auto.
  assert(topLike ((X, (t_and A0 A2)) :: D) (C1 -^ X)).
  rewrite_env(nil++[(X, t_and A0 A2)] ++ D).
  apply topLike_bind_weakening with A0. auto. eauto.
  forwards(?&?): disjoint_original_regular H8. auto.
  assert(spl (B0 -^ X) (C1 -^ X) (C2 -^ X)). auto.
  forwards:IHn H14 H12 H8.
  unfold open_typ_wrt_typ.
  rewrite size_typ_open_typ_wrt_typ_rec_var_mutual.
  rewrite size_typ_open_typ_wrt_typ_rec_var_mutual.
  simpl in H. lia. auto.
  assert(algo_sub D A (t_forall A0 B0)).
  apply sub_transtivity with (t_forall A0 C2). auto.
  forwards*(?&?):algo_sub_regular H8.
  apply D_varr with A. auto. auto.
  assert(disjoint_original D (t_forall A0 C1) B1). auto.
  assert(disjoint_original D (t_forall A0 C1) B2). auto.
  assert(spl (t_forall A0 B0) (t_forall A0 C1) (t_forall A0 C2)). auto.
  forwards:IHn H11 H9 H7. simpl. simpl in H. lia.
  forwards:IHn H11 H10 H8. simpl. simpl in H. lia. auto.
  assert(TWell D (t_forall A0 B0)).
  forwards(?&?):disjoint_original_regular H1.
  forwards(?&?):disjoint_original_regular H2. auto. auto.
  inversion H2;subst;auto. inversion H10;subst;auto.
  inversion H6;subst.
  apply D_forall with (union L
                             (union L0
                                    (union L1
                                           (dom D)))). auto. auto. auto. intros.
  assert(disjoint_original ((X, t_and A0 A2) :: D) (C1 -^ X) (B2 -^ X)). auto.
  assert(disjoint_original ((X, t_and A0 A2) :: D) (C2 -^ X) (B2 -^ X)).
  assert(topLike ((X, A0) :: D) (C2 -^ X)). auto.
  assert(topLike ((X, (t_and A0 A2)) :: D) (C2 -^ X)).
  rewrite_env(nil++[(X, t_and A0 A2)] ++ D).
  apply topLike_bind_weakening with A0. auto. eauto.
  forwards(?&?): disjoint_original_regular H10. auto.
  assert(spl (B0 -^ X) (C1 -^ X) (C2 -^ X)). auto.
  forwards:IHn H14 H10 H13.
  unfold open_typ_wrt_typ.
  rewrite size_typ_open_typ_wrt_typ_rec_var_mutual.
  rewrite size_typ_open_typ_wrt_typ_rec_var_mutual.
  simpl in H. lia. auto.
  assert(TWell D (t_forall A0 B0)).
  forwards(?&?):disjoint_original_regular H1.
  forwards(?&?):disjoint_original_regular H2. auto. auto.
  apply D_forall with (union L
                             (union L0
                                    (union L1
                                           (dom D)))). auto. auto. auto. intros.
  assert(disjoint_original ((X, t_and A0 A2) :: D) (C1 -^ X) (B2 -^ X)). auto.
  assert(disjoint_original ((X, t_and A0 A2) :: D) (C2 -^ X) (B2 -^ X)). auto.
  assert(spl (B0 -^ X) (C1 -^ X) (C2 -^ X)). auto.
  forwards:IHn H10 H6 H8.
  unfold open_typ_wrt_typ.
  rewrite size_typ_open_typ_wrt_typ_rec_var_mutual.
  rewrite size_typ_open_typ_wrt_typ_rec_var_mutual.
  simpl in H. lia. auto.
  inversion H2;subst;auto. inversion H10;subst;auto.
  assert(algo_sub D A (t_forall A0 B0)).
  apply sub_transtivity with (t_forall A0 C1). auto.
  forwards*(?&?):algo_sub_regular H6.
  apply D_varr with A. auto. auto. auto. auto.
  assert(TWell D (t_forall A0 B0)).
  forwards(?&?):disjoint_original_regular H1.
  forwards(?&?):disjoint_original_regular H2. auto. auto.
  forwards:binds_unique H5 H8. apply TCWell_uniq.
  forwards*: algo_sub_well_tctx H6.
  subst.
  assert(algo_sub D A1 (t_forall A0 B0)). eauto.
  apply D_varr with A1. auto. auto. auto. auto.
  inversion H2;subst;auto. inversion H10;subst;auto.
  assert(disjoint_original D (t_forall A0 C2) B1). auto.
  assert(disjoint_original D (t_forall A0 C2) B2). auto.
  assert(spl (t_forall A0 B0) (t_forall A0 C1) (t_forall A0 C2)). auto.
  forwards:IHn H11 H5 H9. simpl. simpl in H. lia.
  forwards:IHn H11 H6 H10. simpl. simpl in H. lia. auto.
  assert(TWell D (t_forall A0 B0)).
  forwards(?&?):disjoint_original_regular H1.
  forwards(?&?):disjoint_original_regular H2. auto. auto.
  assert(spl (t_forall A0 B0) (t_forall A0 C1) (t_forall A0 C2)). auto.
  forwards:IHn H7 H5 H11. simpl. simpl in H. lia.
  forwards:IHn H7 H6 H12. simpl. simpl in H. lia. auto.
  inversion H1;subst;auto.
  inversion H2;subst;auto;inversion H7;subst;auto. contradiction.
  inversion H2;subst;auto. inversion H9;subst;auto.
  assert(topLike D (t_rcd l B0)). eauto. auto.
  inversion H5;subst. assert(disjoint_original D C1 B). auto.
  forwards:IHn H3 H6 H10. simpl in H. lia. auto.
  assert(algo_sub D A (t_rcd l B0)).
  apply sub_transtivity with (t_rcd l C2). auto.
  forwards*(?&?): algo_sub_regular H7.
  apply D_varr with A. auto. auto.
  assert(disjoint_original D (t_rcd l C1) B1). auto.
  assert(disjoint_original D (t_rcd l C1) B2). auto.
  assert(spl (t_rcd l B0) (t_rcd l C1) (t_rcd l C2)). auto.
  forwards:IHn H10 H8 H6. simpl. simpl in H. lia.
  forwards:IHn H10 H9 H7. simpl. simpl in H. lia. auto.
  assert(TWell D (t_rcd l B0)).
  forwards(?&?):disjoint_original_regular H1.
  forwards(?&?):disjoint_original_regular H2. auto. auto.
  inversion H2;subst;auto. inversion H7;subst;auto. contradiction.
  inversion H5;subst. assert(disjoint_original D C2 B). auto.
  forwards:IHn H3 H8 H6. simpl in H. lia. auto.
  assert(TWell D (t_rcd l B0)).
  forwards(?&?):disjoint_original_regular H1.
  forwards(?&?):disjoint_original_regular H2. auto. auto.
  forwards:IHn H3 H8 H6. simpl in H. lia. auto.
  inversion H2;subst;auto. inversion H9;subst;auto.
  assert(algo_sub D A (t_rcd l B0)).
  apply sub_transtivity with (t_rcd l C1). auto.
  forwards*(?&?): algo_sub_regular H5.
  apply D_varr with A. auto. auto. auto. auto.
  assert(TWell D (t_rcd l B0)).
  forwards(?&?):disjoint_original_regular H1.
  forwards(?&?):disjoint_original_regular H2. auto. auto.
  forwards:binds_unique H4 H7. apply TCWell_uniq.
  forwards*:algo_sub_well_tctx H5. subst.
  assert(algo_sub D A0 (t_rcd l B0)). eauto.
  apply D_varr with A0. auto. auto. auto. auto.
  inversion H2;subst;auto. inversion H9;subst;auto.
  assert(disjoint_original D (t_rcd l C2) B1). auto.
  assert(disjoint_original D (t_rcd l C2) B2). auto.
  assert(spl (t_rcd l B0) (t_rcd l C1) (t_rcd l C2)). auto.
  forwards:IHn H10 H4 H8. simpl. simpl in H. lia.
  forwards:IHn H10 H5 H9. simpl. simpl in H. lia. auto.
  assert(TWell D (t_rcd l B0)).
  forwards(?&?):disjoint_original_regular H1.
  forwards(?&?):disjoint_original_regular H2. auto. auto.
  assert(spl (t_rcd l B0) (t_rcd l C1) (t_rcd l C2)). auto.
  forwards:IHn H6 H4 H10. simpl. simpl in H. lia.
  forwards:IHn H6 H5 H11. simpl. simpl in H. lia. auto.
  forwards:disjoint_original_well_tctx H1. auto.
Qed.

Lemma disjoint_spl: forall D A B C E, spl A B C -> disjoint_original D B E -> disjoint_original D C E -> disjoint_original D A E.
Proof.
  intros. forwards:disjoint_spl_alternative H H0 H1. eauto. auto.
Qed.

Lemma disjoint_spl_symm_alternative: forall n D A B C E, size_typ A + size_typ E <= n -> spl A B C -> disjoint_original D E B -> disjoint_original D E C -> disjoint_original D E A.
Proof.
  intros n. induction n. intros. destruct A;inversion H.
  intros. inversion H0;subst.
  inversion H1;subst;auto.
  inversion H2;subst;auto;inversion H8;subst;auto.
  assert(TWell D (t_arrow A0 B0)).
  forwards(?&?):disjoint_original_regular H1.
  forwards(?&?):disjoint_original_regular H2. auto. auto.
  inversion H2;subst;auto. inversion H10;subst;auto.
  assert(topLike D (t_arrow A0 B0)). eauto. auto.
  inversion H6;subst. assert(disjoint_original D A2 C1). auto.
  forwards:IHn H4 H7 H13. simpl in H. lia. auto.
  assert(algo_sub D A (t_arrow A0 B0)).
  apply sub_transtivity with (t_arrow A0 C2). auto.
  forwards*(?&?):algo_sub_regular H8.
  apply D_varl with A. auto. auto.
  assert(disjoint_original D A1 (t_arrow A0 C1)). auto.
  assert(disjoint_original D A2 (t_arrow A0 C1)). auto.
  assert(spl (t_arrow A0 B0) (t_arrow A0 C1) (t_arrow A0 C2)). auto.
  forwards:IHn H11 H9 H7. simpl. simpl in H. lia.
  forwards:IHn H11 H10 H8. simpl. simpl in H. lia. auto.
  inversion H2;subst;auto. inversion H9;subst;auto.
  inversion H6;subst.
  assert(disjoint_original D A2 C2). auto.
  forwards:IHn H4 H11 H8. simpl in H. lia. auto.
  forwards:IHn H4 H11 H15. simpl in H. lia. auto.
  inversion H2;subst;auto. inversion H10;subst;auto.
  assert(TWell D (t_arrow A0 B0)).
  forwards(?&?):disjoint_original_regular H1.
  forwards(?&?):disjoint_original_regular H2. auto. auto.
  assert(algo_sub D A (t_arrow A0 B0)).
  apply sub_transtivity with (t_arrow A0 C1). auto.
  forwards*(?&?):algo_sub_regular H6.
  apply D_varl with A. auto. auto.
  forwards:binds_unique H5 H8. apply TCWell_uniq.
  forwards*: algo_sub_well_tctx H6. subst.
  assert(algo_sub D A1 (t_arrow A0 B0)). eauto.
  apply D_varl with A1. auto. auto. auto. auto.
  inversion H2;subst;auto. inversion H10;subst;auto.
  assert(TWell D (t_arrow A0 B0)).
  forwards(?&?):disjoint_original_regular H1.
  forwards(?&?):disjoint_original_regular H2. auto. auto.
  assert(disjoint_original D A1 (t_arrow A0 C2)). auto.
  assert(disjoint_original D A2 (t_arrow A0 C2)). auto.
  assert(spl (t_arrow A0 B0) (t_arrow A0 C1) (t_arrow A0 C2)). auto.
  forwards:IHn H11 H5 H9. simpl. simpl in H. lia.
  forwards:IHn H11 H6 H10. simpl. simpl in H. lia. auto.
  assert(TWell D (t_arrow A0 B0)).
  forwards(?&?):disjoint_original_regular H1.
  forwards(?&?):disjoint_original_regular H2. auto. auto.
  assert(spl (t_arrow A0 B0) (t_arrow A0 C1) (t_arrow A0 C2)). auto.
  forwards:IHn H8 H5 H10. simpl. simpl in H. lia.
  forwards:IHn H8 H6 H12. simpl. simpl in H. lia. auto.
  inversion H1;subst;auto.
  inversion H2;subst;auto;inversion H8;subst;auto.
  assert(TWell D (t_forall A0 B0)).
  forwards(?&?):disjoint_original_regular H1.
  forwards(?&?):disjoint_original_regular H2. auto. auto.
  inversion H2;subst;auto. inversion H10;subst;auto.
  assert(topLike D (t_forall A0 B0)). eauto. auto.
  inversion H6;subst.
  apply D_forall with (union L
                             (union L0
                                    (union L1
                                           (dom D)))). auto. auto. auto. intros.
  assert(disjoint_original ((X, t_and A1 A0) :: D) (B1 -^ X) (C2 -^ X)). auto.
  assert(disjoint_original ((X, t_and A1 A0) :: D) (B1 -^ X) (C1 -^ X)).
  assert(topLike ((X, A0) :: D) (C1 -^ X)). auto.
  assert(topLike ((X, (t_and A1 A0)) :: D) (C1 -^ X)).
  rewrite_env(nil++[(X, t_and A1 A0)] ++ D).
  apply topLike_bind_weakening with A0. auto. eauto.
  forwards(?&?): disjoint_original_regular H8. auto.
  assert(spl (B0 -^ X) (C1 -^ X) (C2 -^ X)). auto.
  forwards:IHn H14 H11 H8.
  unfold open_typ_wrt_typ.
  rewrite size_typ_open_typ_wrt_typ_rec_var_mutual.
  rewrite size_typ_open_typ_wrt_typ_rec_var_mutual.
  simpl in H. lia. auto.
  assert(algo_sub D A (t_forall A0 B0)).
  apply sub_transtivity with (t_forall A0 C2). auto.
  forwards*(?&?): algo_sub_regular H8.
  apply D_varl with A. auto. auto.
  assert(disjoint_original D A1 (t_forall A0 C1)). auto.
  assert(disjoint_original D A2 (t_forall A0 C1)). auto.
  assert(spl (t_forall A0 B0) (t_forall A0 C1) (t_forall A0 C2)). auto.
  forwards:IHn H11 H9 H7. simpl. simpl in H. lia.
  forwards:IHn H11 H10 H8. simpl. simpl in H. lia. auto.
  assert(TWell D (t_forall A0 B0)).
  forwards(?&?):disjoint_original_regular H1.
  forwards(?&?):disjoint_original_regular H2. auto. auto.
  inversion H2;subst;auto. inversion H12;subst;auto.
  inversion H8;subst.
  apply D_forall with (union L
                             (union L0
                                    (union L1
                                           (dom D)))). auto. auto. auto. intros.
  assert(disjoint_original ((X, t_and A1 A0) :: D) (B1 -^ X) (C1 -^ X)). auto.
  assert(disjoint_original ((X, t_and A1 A0) :: D) (B1 -^ X) (C2 -^ X)).
  assert(topLike ((X, A0) :: D) (C2 -^ X)). auto.
  assert(topLike ((X, (t_and A1 A0)) :: D) (C2 -^ X)).
  rewrite_env(nil++[(X, t_and A1 A0)] ++ D).
  apply topLike_bind_weakening with A0. auto. eauto.
  forwards(?&?): disjoint_original_regular H12. auto.
  assert(spl (B0 -^ X) (C1 -^ X) (C2 -^ X)). auto.
  forwards:IHn H15 H12 H14.
  unfold open_typ_wrt_typ.
  rewrite size_typ_open_typ_wrt_typ_rec_var_mutual.
  rewrite size_typ_open_typ_wrt_typ_rec_var_mutual.
  simpl in H. lia. auto.
  apply D_forall with (union L
                             (union L0
                                    (union L1
                                           (dom D)))). auto. auto. auto. intros.
  assert(disjoint_original ((X, t_and A1 A0) :: D) (B1 -^ X) (C1 -^ X)). auto.
  assert(disjoint_original ((X, t_and A1 A0) :: D) (B1 -^ X) (C2 -^ X)). auto.
  assert(spl (B0 -^ X) (C1 -^ X) (C2 -^ X)). auto.
  forwards:IHn H12 H8 H9.
  unfold open_typ_wrt_typ.
  rewrite size_typ_open_typ_wrt_typ_rec_var_mutual.
  rewrite size_typ_open_typ_wrt_typ_rec_var_mutual.
  simpl in H. lia. auto.
  inversion H2;subst;auto. inversion H10;subst;auto.
  assert(TWell D (t_forall A0 B0)).
  forwards(?&?):disjoint_original_regular H1.
  forwards(?&?):disjoint_original_regular H2. auto. auto.
  assert(algo_sub D A (t_forall A0 B0)).
  apply sub_transtivity with (t_forall A0 C1). auto.
  forwards*(?&?):algo_sub_regular H6.
  apply D_varl with A. auto. auto.
  forwards:binds_unique H5 H8. apply TCWell_uniq.
  forwards*:algo_sub_well_tctx H6.
  subst.
  assert(algo_sub D A1 (t_forall A0 B0)). eauto.
  apply D_varl with A1. auto. auto.
  inversion H2;subst;auto. inversion H10;subst;auto.
  assert(TWell D (t_forall A0 B0)).
  forwards(?&?):disjoint_original_regular H1.
  forwards(?&?):disjoint_original_regular H2. auto. auto.
  assert(disjoint_original D A1 (t_forall A0 C2)). auto.
  assert(disjoint_original D A2 (t_forall A0 C2)). auto.
  assert(spl (t_forall A0 B0) (t_forall A0 C1) (t_forall A0 C2)). auto.
  forwards:IHn H11 H5 H9. simpl. simpl in H. lia.
  forwards:IHn H11 H6 H10. simpl. simpl in H. lia. auto.
  assert(spl (t_forall A0 B0) (t_forall A0 C1) (t_forall A0 C2)). auto.
  forwards:IHn H7 H5 H10. simpl. simpl in H. lia.
  forwards:IHn H7 H6 H12. simpl. simpl in H. lia. auto.
  inversion H1;subst;auto.
  inversion H2;subst;auto;inversion H7;subst;auto. contradiction.
  assert(TWell D (t_rcd l B0)).
  forwards(?&?):disjoint_original_regular H1.
  forwards(?&?):disjoint_original_regular H2. auto. auto.
  inversion H2;subst;auto. inversion H9;subst;auto.
  assert(topLike D (t_rcd l B0)). eauto. auto.
  inversion H5;subst. assert(disjoint_original D A C1). auto.
  forwards:IHn H3 H6 H9. simpl in H. lia. auto.
  assert(algo_sub D A (t_rcd l B0)).
  apply sub_transtivity with (t_rcd l C2). auto.
  forwards*(?&?): algo_sub_regular H7.
  apply D_varl with A. auto. auto.
  assert(disjoint_original D A1 (t_rcd l C1)). auto.
  assert(disjoint_original D A2 (t_rcd l C1)). auto.
  assert(spl (t_rcd l B0) (t_rcd l C1) (t_rcd l C2)). auto.
  forwards:IHn H10 H8 H6. simpl. simpl in H. lia.
  forwards:IHn H10 H9 H7. simpl. simpl in H. lia. auto.
  inversion H2;subst;auto. inversion H8;subst;auto. contradiction.
  assert(TWell D (t_rcd l B0)).
  forwards(?&?):disjoint_original_regular H1.
  forwards(?&?):disjoint_original_regular H2. auto. auto.
  inversion H5;subst. assert(disjoint_original D A C2). auto.
  forwards:IHn H3 H7 H6. simpl in H. lia. auto.
  forwards:IHn H3 H7 H6. simpl in H. lia. auto.
  inversion H2;subst;auto. inversion H9;subst;auto.
  assert(TWell D (t_rcd l B0)).
  forwards(?&?):disjoint_original_regular H1.
  forwards(?&?):disjoint_original_regular H2. auto. auto.
  assert(algo_sub D A (t_rcd l B0)).
  apply sub_transtivity with (t_rcd l C1). auto.
  forwards*(?&?):algo_sub_regular H5.
  apply D_varl with A. auto. auto.
  forwards:binds_unique H4 H7. apply TCWell_uniq.
  forwards*:algo_sub_well_tctx H5. subst.
  assert(algo_sub D A0 (t_rcd l B0)). eauto.
  apply D_varl with A0. auto. auto.
  inversion H2;subst;auto. inversion H9;subst;auto.
  assert(TWell D (t_rcd l B0)).
  forwards(?&?):disjoint_original_regular H1.
  forwards(?&?):disjoint_original_regular H2. auto. auto.
  assert(TWell D (t_rcd l B0)).
  forwards(?&?):disjoint_original_regular H1.
  forwards(?&?):disjoint_original_regular H2. auto. auto.
  assert(disjoint_original D A1 (t_rcd l C2)). auto.
  assert(disjoint_original D A2 (t_rcd l C2)). auto.
  assert(spl (t_rcd l B0) (t_rcd l C1) (t_rcd l C2)). auto.
  forwards:IHn H11 H4 H9. simpl. simpl in H. lia.
  forwards:IHn H11 H5 H10. simpl. simpl in H. lia. auto.
  assert(spl (t_rcd l B0) (t_rcd l C1) (t_rcd l C2)). auto.
  forwards:IHn H6 H4 H9. simpl. simpl in H. lia.
  forwards:IHn H6 H5 H11. simpl. simpl in H. lia. auto.
  forwards:disjoint_original_well_tctx H1. auto.
Qed.

Lemma disjoint_spl_symm: forall D A B C E, spl A B C -> disjoint_original D E B -> disjoint_original D E C -> disjoint_original D E A.
Proof.
  intros. forwards:disjoint_spl_symm_alternative H H0 H1. eauto. auto.
Qed.


Lemma disjoint_original_eqv: forall D A B, disjoint D A B <-> disjoint_original D A B.
Proof.
  intros. split;intros.
  dependent induction H;eauto.
  forwards:disjoint_spl H IHdisjoint1 IHdisjoint2. auto.
  forwards:disjoint_spl_symm H IHdisjoint1 IHdisjoint2. auto.
  dependent induction H;eauto. forwards:disjoint_regular IHdisjoint_original1. destruct H1.
  forwards:disjoint_regular IHdisjoint_original2. destruct H3. eauto.
  forwards:disjoint_regular IHdisjoint_original1. destruct H1.
  forwards:disjoint_regular IHdisjoint_original2. destruct H3. eauto.
Qed.
*)
