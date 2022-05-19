(**
       preservation
       also includes lemmas about Typing
*)
Require Import LibTactics.
Require Import Coq.Program.Equality.
Require Import List. Import ListNotations.
Require Import Arith Lia.
Require Export Progress.

(**************************** Typing ******************************************)

Lemma prevalue_subst : forall P Z u A,
    prevalue u ->
    pType u A ->
    lc_typ P ->
    prevalue (typsubst_exp P Z u) /\ pType (typsubst_exp P Z u) [Z ~~> P] A.
Proof with simpls; eauto using typsubst_exp_lc_exp, typsubst_typ_lc_typ.
  intros. gen A. inductions H; intros.
  - inverts H0...
  - inverts H0...  
  - inverts H2. splits...
  - inverts H2. splits; forwards~ (?&?): IHprevalue1; forwards~ (?&?): IHprevalue2...
Qed.

Lemma consistent_subst : forall U Z u1 u2,
    consistent u1 u2 ->
    TWell nil U ->
    consistent (typsubst_exp U Z u1) (typsubst_exp U Z u2).
Proof.
  intros. inductions H; simpls; eauto.
  - applys C_anno; eauto 4 with lngen.
  - forwards: TWell_lc_typ H4.
    applys C_disjoint.
    forwards*: prevalue_subst H2 H.
    forwards*: prevalue_subst H3 H0.
    forwards(?&?): disjoint_regular H1.
    forwards~: TW_not_in Z H6.
    forwards~: TW_not_in Z H7.
    rewrites~ typsubst_typ_fresh_eq.
    rewrites~ typsubst_typ_fresh_eq.
    applys* prevalue_subst.
    applys* prevalue_subst.
Qed.


Lemma Typing_subst_1 : forall E F D e dir T S U Z,
    Typing (E ++ Z ~ S ++ F) D e dir T ->
    TWell [] U ->
    disjoint F U S ->
    TCWell (map (typsubst_typ U Z) E ++ F) ->
    Typing (map (typsubst_typ U Z) E ++ F) (map (typsubst_typ U Z) D) (typsubst_exp U Z e) dir (typsubst_typ U Z T).
Proof with eauto 3 using Typing_regular_3, TWell_lc_typ, Typing_TCWell, TWell_weakening.
  introv Typ.
  remember (E ++ Z ~ S ++ F) as E'. gen E.
  inductions Typ; intros E Eq TW TD TCW; subst; simpl;
  try solve [ constructor; eauto;
              applys CWell_subst; eauto;
              rewrite_env ([] ++ F ++ []);
              applys TWell_weakening; eauto ].
  - pick fresh x and apply Typ_abs.
    (* forwards: appDist_subst Z U H. *)
    (* eauto. simpl in H3. apply H3. *)
    applys algo_sub_subst...
    forwards~: H1 x.
    (* forwards~: H2 x. *)
    rewrites typsubst_exp_open_exp_wrt_exp in H2...
  - forwards: IHTyp2...
    applys Typ_app...
    forwards: appDist_subst Z U.
    applys H.
    forwards~: TWell_lc_typ TW.
    simpls...
  - pick fresh X and apply Typ_tabs.
    applys CWell_subst...
    instantiate_cofinites.
    forwards~: H1 ((X, A) :: E).
    simpl_env.
    constructor~.
    applys TWell_subst_1...
    rewrites typsubst_typ_open_typ_wrt_typ_var...
    rewrites typsubst_exp_open_exp_wrt_typ_var...
  - rewrites typsubst_typ_open_typ_wrt_typ...
    forwards~: IHTyp.
    applys Typ_tapp...
    forwards~: appDist_subst Z U H.
    forwards~: TWell_lc_typ TW.
    simpl in H2. applys H2.
    applys disjoint_subst...
  - applys Typ_proj...
    forwards~: appDist_subst Z U H...
  - applys Typ_merge...
    forwards: disjoint_subst H...
  - pick fresh x and apply Typ_fix.
    forwards*: H0 x.
    simpls.
    rewrites typsubst_exp_open_exp_wrt_exp_var...
  - applys Typ_mergev...
    applys CWell_subst...
    forwards: Typing_regular_0 Typ1.
    assert(Z `notin` {}). auto.
    forwards: TW_not_in H3 H4.
    forwards: TY_not_in Typ1. apply H4.
    assert([Z ~~> U] (A) = A).
    apply typsubst_typ_fresh_eq. auto.
    assert((typsubst_exp U Z u1) = u1).
    apply typsubst_exp_fresh_eq. auto.
    rewrite H7. rewrite H8. auto.
    forwards: Typing_regular_0 Typ2.
    assert(Z `notin` {}). auto.
    forwards: TW_not_in H3 H4.
    forwards: TY_not_in Typ2. apply H4.
    assert([Z ~~> U] (B) = B).
    apply typsubst_typ_fresh_eq. auto.
    assert((typsubst_exp U Z u2) = u2).
    apply typsubst_exp_fresh_eq. auto.
    rewrite H7. rewrite H8. auto.
    applys consistent_subst...
  - applys Typ_sub...
    forwards~: Typing_regular_3 Typ.
    applys algo_sub_subst...
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

(* its form can be simplified, like preservation *)

Lemma Typing_subst_2_inf_subsub : forall D (E F : ctx) e u S S' dir T (z : atom),
    Typing D (F ++ [(z,S)] ++ E) e dir T ->
    Typing D E u Inf S' -> subsub S' S ->
    ( dir = Inf ->
      exists T', Typing D (F ++ E) ([z ~> u] e) Inf T' /\ subsub T' T )
    /\
    ( dir = Chk -> Typing D (F ++ E) ([z ~> u] e) Chk T ).
Proof.
  introv Typ Typv Subsub.
  remember (F ++ [(z,S)] ++ E) as E'.
  generalize dependent F.
  inductions Typ;
    intros F Eq; subst; simpl;
      lets Lc  : Typing_regular_1 Typv;
      lets Uni : Typing_regular_2 Typv.
  all: split; intro Heq; try solve [inverts Heq].
  - (* top *)
    exists; split*; constructor*.
    forwards* HH: CWell_app_2 H0.
    destruct* HH as [HH1 HH2].
    forwards*: CWell_app_2 HH1.
    destruct* H2 as [HH3 _].
    forwards*: CWell_app_1 HH3 HH2.
  - (* lit *)
    exists; split*; constructor*.
    forwards* HH: CWell_app_2 H0.
    destruct* HH as [HH1 HH2].
    forwards*: CWell_app_2 HH1.
    destruct* H2 as [HH3 _].
    forwards*: CWell_app_1 HH3 HH2.
  - (* var *)
    case_if. substs. assert (A = S).
    eapply binds_mid_eq; eauto.
    + substs.
      exists. split.
      apply~ Typing_weakening_3. eauto.
      forwards*: CWell_app_2 H0.
      solve_uniq.
      auto.
    + exists A.
      split.
      constructor*.
      forwards* HH: CWell_app_2 H0.
      destruct* HH as [HH1 HH2].
      forwards*: CWell_app_2 HH1.
      destruct* H3 as [HH3 _].
      forwards*: CWell_app_1 HH3 HH2.
      constructor*.
  - (* abs *)
    pick fresh x and apply Typ_abs. now auto.
    forwards~ (HF&HT1): H1 x.
    rewrite_env (([(x, A)] ++ F) ++ [(z, S)] ++ E). now reflexivity.
    forwards~ HT1': HT1. clear HT1 HF.
    rewrites subst_exp_open_exp_wrt_exp_var. eassumption.
    eauto. eauto.
  - (* app *)
    forwards* (HT1&HF): IHTyp1. forwards~ (?&HT1'&HS): HT1. clear HF.
    forwards* (HF&HT2): IHTyp2. forwards~ HT2': HT2. clear HF.
    forwards* (B'&T'&?&?&?): appDist_arr_subsub D HS.
    exists T'. split*. econstructor; try eassumption.
    (* duplicated Type *)
    forwards: Typing_chk_dup; try eassumption.
  - (* tabs *)
    pick fresh x and apply Typ_tabs.
    forwards* HH: CWell_app_2 H. destruct* HH as [HH1 HH2].
    forwards* HHH: CWell_app_2 HH1. destruct* HHH as [HH3 _].
    forwards*: CWell_app_1 HH3 HH2.
    forwards*: H0 x.
    forwards~ (HF&HT1): H1 x.
    { applys* (Typing_weakening_1 [] D x A E u Inf S'). solve_notin. }
    forwards~ HT1': HT1. clear HT1 HF.
    rewrite subst_exp_open_exp_wrt_typ in HT1'.
    applys HT1'. eauto.
  - (* tapp *)
    forwards* (HT1&HF): IHTyp. forwards~ (?&HT1'&HS): HT1. clear HT1 HF.
    forwards~ (?&?&?&?&?): appDist_forall_subsub_disjoint D H HS.
    exists (x1 ^-^ A). split.
    applys* Typ_tapp HT1'.
    apply disjoint_covariance with C1. auto. auto. auto.
  - (* proj *)
    forwards* (HT1&HF): IHTyp. forwards~ (?&HT1'&HS): HT1. clear HT1 HF.
    forwards* (?&?&?): appDist_rcd_subsub D HS.
  - (* rcd *)
    forwards* (HT1&HF): IHTyp.
  - (* merge *)
    forwards* (HT1&HF): IHTyp1. forwards~ (?&HT1'&HS): HT1. clear HT1 HF.
    forwards* (HT2&HF): IHTyp2. forwards~ (?&HT2'&HS'): HT2. clear HT2 HF.
    exists (t_and x x0). split. constructor~.
    apply subsub2sub with D x A in HS; auto. destruct HS.
    apply subsub2sub with D x0 B in HS'; auto. destruct HS'.
    apply disjoint_covariance with B.
    apply disjoint_symm.
    apply disjoint_covariance with A.
    auto. auto. auto. econstructor; eauto.
  - (* inter *)
    forwards* (HF&HT1): IHTyp1. forwards~ HT1': HT1. clear HT1 HF.
    forwards* (HF&HT2): IHTyp2.
  - (* anno *)
    forwards* (HT1&HF): IHTyp.
  - (* fix *)
    exists A. split*.
    pick fresh x and apply Typ_fix.
    forwards* (HF&HT): H0 x.
    rewrite_env (((x, A) :: F) ++ [(z, S)] ++ E). reflexivity.
    forwards~ HT': HT. clear HT HF.
    rewrites subst_exp_open_exp_wrt_exp_var; eauto.
    econstructor; eauto.
    instantiate_cofinites. now eauto.
  - (* mergev *)
    lets Eq1: ((subst_value _ _ _ _ z u) Typ1).
    lets Eq2: ((subst_value _ _ _ _ z u) Typ2).
    rewrite Eq1.
    rewrite Eq2.
    exists (t_and A B).
    split~.
    applys* (Typ_mergev D (F ++ E) u1 u2 A B).
    forwards* HH: CWell_app_2 H0.
    destruct* HH as [HH1 HH2].
    forwards*: CWell_app_2 HH1.
    destruct* H3.
    forwards*: CWell_app_1 H3 HH2.
    (* assert(subsub (t_and A B) (t_and A B)).
    eauto.
    rewrite_env(nil ++ D ++ nil).
    apply subsub_weakening. auto.
    apply subsub_well_tctx in Subsub.
    assert(nil ++ D ++ nil = D). simpl. eauto.
    rewrite H4. auto. *)
  - (* subsumption *)
    forwards* (HT1&HF): IHTyp. forwards~ (?&HT1'&HS): HT1. clear HT1 HF.
    apply subsub2sub with D x A in HS; auto. destruct HS.
    assert (algo_sub D x B) by auto_sub.
    applys* Typ_sub.
Qed.

(****************************** reduction-related *****************************)

(****************************** casting *****************************)

Lemma casting_value_2: forall v A v',
    value v ->
    casting v A v' ->
    value v' /\ exists A', pType v' A' /\ subsub A' A.
Proof with eauto 3 with lngen.
  intros v A v' Val Red.
  induction Red...
  all: splits...
  all: try solve [exists; split*].
  1: now inverts~ Val.
  1,2: forwards~: IHRed1; forwards~: IHRed2; destruct_conj; eauto.
Qed.

Lemma consistent_keep: forall v v1 v2 A C,
    value v -> pType v1 C -> TWell nil C -> consistent v v1 ->
    casting v A v2 -> consistent v2 v1.
Proof with eauto.
  introv Val PT TW Con TR. gen v2 A C.
  inductions Con; intros v2 A' TR C PT TW.
  - inductions TR.
    2-5: try solve [applys* C_disjoint].
    all: eauto.
  - inductions TR.
    1-4: try solve [applys* C_disjoint].
    all: eauto.
  - forwards: casting_sub TR...
    forwards~ (?&?&?&?): casting_value_2 TR.
    forwards (_&?): algo_sub_regular H4.
    forwards: TWell_subsub_2 H8 H7.
    applys C_disjoint H0...
    forwards~ (?&?): subsub2sub H7; auto.
    applys disjoint_symm.
    apply disjoint_symm in H1.
    applys* disjoint_covariance H1.
  - inductions TR.
    1-4: try solve [applys* C_disjoint].
    all: eauto.
  - inverts PT. forwards: IHCon1...
Qed.


Lemma casting_consistent : forall v A B C v1 v2,
    value v -> 
    Typing nil nil v Inf C -> 
    casting v A v1 -> 
    casting v B v2 ->
    consistent v1 v2.
Proof with try eassumption.
  intros. gen B C v2.
  dependent induction H1;intros.
  - (* lit *)
    dependent induction H2; intros; eauto.
  - (* top *)
    forwards* (?&?&?&SS): casting_value_2 H2.
    forwards~: typ_value_ptype H1.
    forwards~: casting_sub H2 H5.
    forwards (_&?): algo_sub_regular H6.
    forwards*: TWell_subsub_1.
  - (* topabs *)
    forwards~ (?&?&?&SS): casting_value_2 H4.
    forwards~: typ_value_ptype H3.
    forwards~: casting_sub H4 H7.
    forwards (_&?): algo_sub_regular H8.
    forwards*: TWell_subsub_1.
  - (* toptabs *)
    forwards~ (?&?&?&?): casting_value_2 H4.
    forwards~: typ_value_ptype H3.
    forwards~: casting_sub H4 H8.
    forwards (_&?): algo_sub_regular H9.
    forwards*: TWell_subsub_1.
  - (* toprcd *)
    forwards~ (?&?&?&?): casting_value_2 H4.
    forwards~: typ_value_ptype H3.
    forwards~: casting_sub H4 H8.
    forwards (_&?): algo_sub_regular H9.
    forwards*: TWell_subsub_1.
  - (* anno *)
    dependent induction H5; intros.
    1-4: applys* C_disjoint.
    + (* C-anno *) eauto.
    + (* merge *) eauto.
  - (* mergel *)
    inverts H.
    inverts H3.
    {
      inductions H4.
      1-4: forwards~ (?&?&?&?): casting_value_2 H2; applys* C_disjoint;
            forwards~ PT: typ_value_ptype H6;
            forwards~ Sub: casting_sub H2 PT;
            forwards (_&?): algo_sub_regular Sub;
            forwards*: TWell_subsub_1.
      all: forwards~ (?&?&?&SS): casting_value_2 H2;
            forwards~ PT: typ_value_ptype H6;
            forwards~ Sub: casting_sub H2 PT;
            forwards (_&TW): algo_sub_regular Sub;
            try forwards~: TWell_subsub_1 TW SS;
            try forwards~: TWell_subsub_2 TW SS.
      + (* same branch *)
        inverts~ H3; applys* IHcasting.
      + (* diff branch *)
        forwards~(?&?): subsub2sub SS; auto.
        forwards~ (?&?&?&SS'): casting_value_2 H4;
          forwards~ PT': typ_value_ptype H11;
          forwards~ Sub': casting_sub H4 PT';
          forwards (_&TW'): algo_sub_regular Sub';
          try forwards~: TWell_subsub_1 TW' SS';
          try forwards~: TWell_subsub_2 TW' SS'.
        forwards(?&?): subsub2sub SS'; auto; auto.
        forwards PV1': cast_prevalue H2.
        forwards PV2': cast_prevalue H4.
        forwards~ PV1: value_inf_prevalue H6.
        forwards~ PV2: value_inf_prevalue H11.
        applys~ C_disjoint x x0.
        apply disjoint_covariance with B0.
        apply disjoint_symm.
        apply disjoint_covariance with A0.
        apply disjoint_symm. auto.
        eauto. eauto.
        + (* spl *)
          assert (consistent v1' v3). eauto.
          assert (consistent v1' v0). eauto. auto.
    }
    {
      inductions H4.
      1-4: forwards~ (?&?&?&?): casting_value_2 H2; applys* C_disjoint;
            forwards~ PT: typ_value_ptype H11;
            forwards~ Sub: casting_sub H2 PT;
            forwards (_&?): algo_sub_regular Sub;
            forwards*: TWell_subsub_1.
      all: forwards~ (?&?&?&SS): casting_value_2 H2;
            forwards~ PT: typ_value_ptype H11;
            forwards~ Sub: casting_sub H2 PT;
            forwards (_&TW): algo_sub_regular Sub;
            try forwards~: TWell_subsub_1 TW SS;
            try forwards~: TWell_subsub_2 TW SS.
      + (* same branch *)
        inverts~ H3; applys* IHcasting.
      + (* diff branch *)
        forwards~(?&?): subsub2sub SS; auto.
        forwards~ (?&?&?&SS'): casting_value_2 H4;
          forwards~ PT': typ_value_ptype H14;
          forwards~ Sub': casting_sub H4 PT';
          forwards (_&TW'): algo_sub_regular Sub';
          try forwards~: TWell_subsub_1 TW' SS';
          try forwards~: TWell_subsub_2 TW' SS'.
        forwards(?&?): subsub2sub SS'; auto; auto.
        forwards~ PV1: value_inf_prevalue v1. eassumption.
        forwards~ PV2: value_inf_prevalue v2. eassumption.
        applys consistent_keep H2...
        applys consistent_symm.
        apply consistent_symm in H15.
        applys* consistent_keep H15.
      + (* spl *)
        assert (consistent v1' v3). eauto.
        assert (consistent v1' v0). eauto. auto.
    }
  - (* merger *)
  inverts H.
  inverts H3.
  {
    inductions H4.
    1-4: forwards~ (?&?&?&?): casting_value_2 H2; applys* C_disjoint;
          forwards~ PT: typ_value_ptype H11;
          forwards~ Sub: casting_sub H2 PT;
          forwards (_&?): algo_sub_regular Sub;
          forwards*: TWell_subsub_1.
    all: forwards~ (?&?&?&SS): casting_value_2 H2;
          forwards~ PT: typ_value_ptype H11;
          forwards~ Sub: casting_sub H2 PT;
          forwards (_&TW): algo_sub_regular Sub;
          try forwards~: TWell_subsub_1 TW SS;
          try forwards~: TWell_subsub_2 TW SS.
    + (* diff branch *)
      forwards~(?&?): subsub2sub SS; auto.
      forwards~ (?&?&?&SS'): casting_value_2 H4;
        forwards~ PT': typ_value_ptype H6;
        forwards~ Sub': casting_sub H4 PT';
        forwards (_&TW'): algo_sub_regular Sub';
        try forwards~: TWell_subsub_1 TW' SS';
        try forwards~: TWell_subsub_2 TW' SS'.
      forwards(?&?): subsub2sub SS'; auto; auto.
      forwards PV1': cast_prevalue H2.
      forwards PV2': cast_prevalue H4.
      forwards~ PV1: value_inf_prevalue H6.
      forwards~ PV2: value_inf_prevalue H11.
      applys~ C_disjoint x x0.
      apply disjoint_covariance with A0.
      apply disjoint_symm.
      apply disjoint_covariance with B0.
      apply disjoint_symm. auto.
      eauto. eauto.
    + (* same branch *)
      inverts~ H3; applys* IHcasting.
    + (* spl *)
      assert (consistent v2' v3). eauto.
      assert (consistent v2' v0). eauto. auto.
  }
  {
    inductions H4.
    1-4: forwards~ (?&?&?&?): casting_value_2 H2; applys* C_disjoint;
          forwards~ PT: typ_value_ptype H14;
          forwards~ Sub: casting_sub H2 PT;
          forwards (_&?): algo_sub_regular Sub;
          forwards*: TWell_subsub_1.
    all: forwards~ (?&?&?&SS): casting_value_2 H2;
          forwards~ PT: typ_value_ptype H14;
          forwards~ Sub: casting_sub H2 PT;
          forwards (_&TW): algo_sub_regular Sub;
          try forwards~: TWell_subsub_1 TW SS;
          try forwards~: TWell_subsub_2 TW SS.
    + (* diff branch *)
      forwards~(?&?): subsub2sub SS; auto.
      forwards~ (?&?&?&SS'): casting_value_2 H4;
        forwards~ PT': typ_value_ptype H11;
        forwards~ Sub': casting_sub H4 PT';
        forwards (_&TW'): algo_sub_regular Sub';
        try forwards~: TWell_subsub_1 TW' SS';
        try forwards~: TWell_subsub_2 TW' SS'.
      forwards(?&?): subsub2sub SS'; auto; auto.
      forwards~ PV1: value_inf_prevalue v1. eassumption.
      forwards~ PV2: value_inf_prevalue v2. eassumption.
      applys consistent_keep H2...
      applys consistent_symm.
      applys* consistent_keep H15.
    + (* same branch *)
      inverts~ H3; applys* IHcasting.
    + (* spl *)
      assert (consistent v2' v3). eauto.
      assert (consistent v2' v0). eauto. auto.
  }
   - (* spl *)
     assert(consistent v1 v0). eauto.
     assert(consistent v2 v0). eauto. auto.
Qed.


Lemma casting_preservation: forall v v' A B,
    value v ->
    casting v A v'->
    Typing nil nil v Inf B ->
    exists C, pType v' C /\ Typing nil nil v' Inf C /\ subsub C A.
Proof with eauto.
  introv Val Red Typ. (* '. forwards* (B&Typ&Sub): Typing_chk2inf Typ'. *)
  gen B. lets Red': Red.
  induction Red; intros.
  - (* lit *)
    exists. splits*.
  - (* top *)
    exists. splits*.
  - (* topAbs *)
    inverts H1. exists. splits*. repeat econstructor; eauto.
  - (* topTabs *)
    inverts H0. inverts H1. exists. splits*.
    econstructor. pick fresh x and apply Typ_tabs. now eauto.
    instantiate_cofinites_with x. eauto.
  - (* topRcd *)
    inverts H0. inverts H1. exists. splits*.
  - (* anno *)
    inverts Typ. forwards: Typing_chk_sub_2; try eassumption.
    exists*.
  - (* mergel *)
    inverts Val. inverts Typ; forwards*: IHRed.
  - (* merger *)
    inverts Val. inverts Typ; forwards*: IHRed.
  - (* merge_and *)
    forwards* (?&?): TWell_spl H.
    forwards (?&?&?&?): IHRed1 Val Red1 Typ...
    forwards (?&?&?&?): IHRed2 Val Red2 Typ...
    exists (t_and x x0). split. auto.
    forwards: casting_consistent Val Typ Red1 Red2.
    split. applys~ Typ_mergev. eauto.
Qed.

(*************************** wrapping *****************************)

Lemma wrapping_consistent : forall e A B C u1 u2,
    Typing nil nil e Chk C ->
    TWell nil A ->
    TWell nil B ->
    wrapping e A u1 ->
    wrapping e B u2 ->
    consistent u1 u2.
Proof with eauto 4.
  introv Typ TW1 TW2 cast1 cast2.
  forwards~ (PV1&B1&PT1&?): wrapping_prevalue cast1.
  forwards~ (PV2&B2&PT2&?): wrapping_prevalue cast2.
  inductions cast1.
  - applys C_disjoint t_top...
  - inverts PT1. inductions cast2; applys* C_disjoint.
  - inverts PT1. inductions cast2; applys* C_disjoint.
  - inverts PT1. inductions cast2; applys* C_disjoint.
  - inductions cast2.
    + applys C_disjoint B1 t_top...
    + applys C_disjoint B1 (t_arrow A1 A2)...
    + applys C_disjoint B1 (t_forall A1 A2)...
    + applys C_disjoint B1 (t_rcd l A0)...
    + applys C_anno...
    + forwards: prevalue_merge_l_inv PV2.
      forwards: prevalue_merge_r_inv PV2.
      inverts PT2.
      forwards~: IHcast2_1 H9.
      forwards~: IHcast2_2 H11.
  - forwards: prevalue_merge_l_inv PV1.
    forwards: prevalue_merge_r_inv PV1.
    inverts PT1.
    forwards*: IHcast1_1.
Qed.


Lemma wrapping_preservation: forall e u A B,
    wrapping e A u ->
    Typing nil nil e Chk B -> nil ||- B <: A ->
    prevalue u /\ exists C, pType u C /\ Typing nil nil u Inf C /\ subsub C A.
Proof.
  intros. gen e u. indTypSize (size_typ A).
  inverts* H. all: try (split; [now eauto | ]).
  - exists. splits*.
    applys Typ_anno.
    pick fresh x and apply Typ_abs; eauto.
    inverts H4.
    unfolds open_exp_wrt_exp; simpls*.
  - exists. splits*.
    applys Typ_anno.
    inverts H4.
    pick fresh X and apply Typ_tabs; eauto.
    instantiate_cofinites.
    unfolds open_exp_wrt_typ; simpls*.
  - exists. splits*.
    applys Typ_anno.
    applys Typ_rcd.
    inverts H4.
    unfolds open_exp_wrt_exp; simpls*.
  - forwards*: Typing_chk_sub_2 H0 H1.
  - forwards*: IH H3. elia.
    forwards~: IH C B H4. elia.
    forwards*: split_sub H2.
    destruct H as (C'&?).
    destruct H5 as (C''&?).
    destruct_conj.
    split. { applys* PV_merge. }
    exists; splits; eauto 3.
    forwards: Typing_regular_0 H6.
    forwards: Typing_regular_0 H8.
    forwards*: wrapping_consistent H0 H3 H4.
    forwards~: TWell_subsub_1 H10 H7.
Qed.

(******************************** papp ********************************)


Lemma papp_consistent : forall v1 v2 e e1 e2 A B C,
    value v1 -> value v2 ->
    Typing nil nil v1 Inf A -> Typing nil nil v2 Inf B -> Typing nil nil e Chk C ->
    papp v1 (arg_exp e) e1 -> papp v2 (arg_exp e) e2 -> consistent v1 v2 -> consistent e1 e2.
Proof with (eauto using lc_body_exp_wrt_exp; solve_false).
  introv Val1 Val2 Typ1 Typ2 Typ3 P1 P2 Cons.
  gen A B C. lets P1': P1. lets P2': P2.
  inductions P1; inductions P2; intros.
  - inverts* Cons.
    + forwards*: wrapping_unique H1 H4; substs.
      applys C_anno...
    + inverts H5. inverts H6.
      forwards*: appDist_arr_disjoint H7.
      applys C_disjoint...
  - lets (?&?): consistent_merger Cons. eauto. eauto.
    inverts Typ2; eauto 4.
  - lets (?&?): consistent_mergel Cons. eauto. eauto. inverts* Typ1.
  - (* merge ~ merge *)
    inverts Val1. lets~ (?&?): consistent_mergel Cons. inverts* Typ1.
Qed.


Lemma papp_consistent2 : forall v1 v2 l e1 e2 A B,
    value v1 -> value v2 ->
    Typing nil nil v1 Inf A -> Typing nil nil v2 Inf B ->
    papp v1 (arg_la l) e1 -> papp v2 (arg_la l) e2 -> consistent v1 v2 -> consistent e1 e2.
Proof with (try eassumption; eauto 2).
  introv Val1 Val2 Typ1 Typ2 P1 P2 Cons.
  gen A B. lets P1': P1. lets P2': P2.
  inductions P1; inductions P2; intros.
  - inverts~ Cons.
    inverts H3. inverts H4. typing_unify.
    forwards: appDist_rcd_disjoint H5...
    applys C_disjoint...
  - lets (?&?): consistent_merger Cons. now eauto. now eauto.
    inverts Typ2; applys C_merger.
    all: try applys IHP2_1... all: try applys IHP2_2...
  - lets (?&?): consistent_mergel Cons. now eauto. now eauto.
    inverts Typ1; applys C_mergel.
    all: try applys IHP2_1... all: try applys IHP2_2...
  - (* merge ~ merge *)
    inverts Val1. lets~ (?&?): consistent_mergel Cons. inverts* Typ1.
Qed.


Lemma papp_consistent3 : forall v1 v2 T e1 e2 A B A1 A2 B1 B2,
    value v1 -> value v2 ->
    Typing nil nil v1 Inf A -> Typing nil nil v2 Inf B ->
    appDist A (t_forall A1 A2) -> appDist B (t_forall B1 B2) ->
    disjoint [] T (t_and A1 B1) ->
    papp v1 (arg_typ T) e1 -> papp v2 (arg_typ T) e2 ->
    consistent v1 v2 ->
    consistent e1 e2.
Proof with (try eassumption; eauto 2 with lngen).
  introv Val1 Val2 Typ1 Typ2 AD1 AD2 HD P1 P2.
  introv Cons.
  gen A B A1 A2 B1 B2. lets P1': P1. lets P2': P2.
  inductions P1; inductions P2; intros.
  - inverts~ Cons; auto_unify.
    + constructor; eauto 3 with lngen.
    + (* disjoint case *)
      applys C_disjoint.
      1-2: econstructor; eauto with lngen.
      applys disjoint_appDist_forall_inv H1 H2...
      all: applys PV_anno; eauto with lngen.
  - lets (?&?): consistent_merger Cons; auto_unify.
    forwards (?&HD2): disjoint_andr_inv HD...
    applys C_merger; inverts Typ2; appdist_unify;
      forwards (?&?): disjoint_andr_inv HD2...
    all: try applys IHP2_1 T; try applys IHP2_2 T; try assumption.
    all: match goal with
         | |- disjoint _ _ _ => idtac
         | _ => try eassumption; eauto
         end.
    all: eauto.
  - lets (?&?): consistent_mergel Cons; auto_unify.
    forwards (HD2&?): disjoint_andr_inv HD...
    applys C_mergel; inverts Typ1; appdist_unify;
      forwards (?&?): disjoint_andr_inv HD2...
    all: try applys IHP1_1; try applys IHP1_2; try assumption.
    all: match goal with
         | |- disjoint _ _ _ => idtac
         | _ => try eassumption; eauto
         end.
    all: applys* D_andr.
  - (* merge ~ merge *)
    inverts Val1. lets~ (?&?): consistent_mergel Cons.
    applys C_mergel; inverts Typ1; appdist_unify.
    all: try applys IHP1_1; try applys IHP1_2; try reflexivity; try eassumption.
    all: forwards (HD2&?): disjoint_andr_inv HD; now eauto.
Qed.


Lemma papp_preservation : forall v e e' A,
    value v ->
    Typing nil nil (e_app v e) Inf A ->
    papp v (arg_exp e) e' ->
    exists A', Typing nil nil e' Inf A' /\ subsub A' A.
Proof with try eassumption.
  intros v e e' A Val Typ P. gen A.
  inductions P; intros; inverts Typ as Typ1 Typ2 Typ3; auto_unify.
  - (* abs *)
    exists A0. split.
    2: { econstructor; eauto. }
         (* eapply TWell_appDist in H0. inverts H0. eassumption. eauto. } *)
    forwards* Typ': Typing_chk_appDist H5.
    inverts Typ' as ? HT; solve_false.
    econstructor.

    forwards: wrapping_preservation H1... destruct_conj.

    pick fresh y. forwards~ HT': HT y.
    rewrite_env ([]++[(y,A)]++[]) in HT'.
    forwards (HL&HR): Typing_subst_2_inf_subsub HT'...
    clear HL. forwards~ HR': HR.
    rewrite (@subst_exp_intro y). all: eauto.
  - (* merge *)
    inverts Val as Val1 Val2.
    inverts Typ1; appdist_unify;
      forwards (?&?): Typing_chk_inter_inv Typ3.
    + forwards~: IHP1 e. applys Typ_app...
      forwards~: IHP2 e. applys Typ_app... destruct_conj.
      exists. split.
      { applys Typ_merge...
        forwards: appDist_arr_disjoint H3 H7...
        forwards (_&?): disjoint_regular H10.
        forwards~ (?&?): subsub2sub H8; auto.
        forwards~ (?&?): subsub2sub H9; auto.
        applys disjoint_covariance...
        applys disjoint_symm.
        apply disjoint_symm in H10.
        applys disjoint_covariance... }
      { applys IS_and... eauto. }
    + forwards~: IHP1 e. applys Typ_app...
      forwards~: IHP2 e. applys Typ_app... destruct_conj.
      exists. split.
      { applys Typ_mergev...
        applys papp_consistent P1 P2... }
      econstructor; eauto.
Qed.


Lemma papp_preservation2 : forall v l e A,
    value v ->
    Typing nil nil (e_proj v l) Inf A ->
    papp v (arg_la l) e ->
    exists A', Typing nil nil e Inf A' /\ subsub A' A.
Proof with try eassumption.
  introv Val Typ P. gen A.
  inductions P; intros; inverts Typ as Typ1 Typ2 Typ3; auto_unify.
  - (* rcd *)
    exists A0. split.
    2: { econstructor; eauto. }
         (* eapply TWell_appDist in H0. inverts H0. eassumption. eauto. } *)
    forwards* Typ': Typing_chk_appDist H0.
    inverts Typ'; solve_false.
    econstructor...
  - (* merge *)
    inverts Val as Val1 Val2.
    inverts Typ1; appdist_unify.
    + forwards~: IHP1 l. applys Typ_proj...
      forwards~: IHP2 l. applys Typ_proj... destruct_conj.
      exists. split.
      { applys Typ_merge...
        forwards: appDist_rcd_disjoint H3 H7...
        forwards (_&?): disjoint_regular H8.
        forwards~ (?&?): subsub2sub H2; auto.
        forwards~ (?&?): subsub2sub H6; auto.
        applys disjoint_covariance...
        applys disjoint_symm.
        apply disjoint_symm in H8.
        applys disjoint_covariance... }
      { applys IS_and... eauto. }
    + forwards~: IHP1 l. applys Typ_proj...
      forwards~: IHP2 l. applys Typ_proj... destruct_conj.
      exists. split.
      { applys Typ_mergev...
        applys papp_consistent2 P1 P2... }
      econstructor; eauto.
Qed.


Lemma papp_preservation3 : forall v T e A,
    value v ->
    Typing nil nil (e_tapp v T) Inf A ->
    papp v (arg_typ T) e ->
    TWell [] T ->
    exists A', Typing nil nil e Inf A' /\ subsub A' A.
Proof with try eassumption.
  introv Val Typ P TW. gen A.
  inductions P; intros; inverts Typ as Typ1 Typ2 Typ3; auto_unify.
  - (* tabs *)
    exists (C2 ^-^ T). split.
    2: { econstructor; eauto.
         eapply TWell_appDist in H1. 2: now eauto. inverts H1.
         instantiate_cofinites.
         rewrite_env (nil ++ x ~ C1 ++ nil) in H7.
         forwards: TWell_subst TW H7.
         simpls.
         rewrites~ (@typsubst_typ_intro x). }
    forwards* Typ': Typing_chk_appDist H5.
    inverts Typ' as ? HT; solve_false.
    econstructor.
    instantiate_cofinites.
    rewrite_env ([]++[(x,C1)]++[]) in HT.
    forwards*: Typing_subst_1 HT.
    simpls.
    rewrites~ (@typsubst_typ_intro x).
    rewrites* (@typsubst_exp_intro x).
  - (* merge *)
    inverts Val as Val1 Val2.
    inverts Typ1. appdist_unify.
      (* forwards (?&?): Typing_chk_inter_inv Typ3. *)
    + forwards~: IHP1. applys Typ_tapp...
      applys~ disjoint_covariance Typ3.
      forwards~: IHP2. applys Typ_tapp...
      applys~ disjoint_covariance Typ3.
      destruct_conj.
      exists. split.
      { applys Typ_merge...
        forwards: disjoint_appDist_forall_inv H3 H7...
        forwards (_&?): disjoint_regular H8.
        forwards (_&?): subsub2sub H6; auto; auto 1.
        forwards (_&?): subsub2sub H2; auto; auto 1.
        applys disjoint_covariance...
        applys disjoint_symm.
        apply disjoint_symm in H8.
        applys disjoint_covariance... }
      { applys IS_and... eauto. }
    + appdist_unify.
      forwards~: IHP1. applys Typ_tapp...
      applys disjoint_covariance...
      auto_sub.
      forwards~: IHP2. applys Typ_tapp...
      applys disjoint_covariance...
      auto_sub.
      destruct_conj.
      exists. split.
      { applys Typ_mergev...
        applys~ (papp_consistent3 v1 v2 T e1 e2 A B0 B1 C0 B2 C3). }
      econstructor; eauto.
Qed.


Inductive step_or_v : exp -> exp -> Prop :=
| ST_v : forall v, value v -> step_or_v v v
| ST_s : forall e1 e2, step e1 e2 -> step_or_v e1 e2.

#[export]
Hint Constructors step_or_v : core.

(* to prove the consistent merge case in preservation_subsub *)

Lemma consistent_steps: forall e1 e2 e1' e2' A B,
    Typing [] [] e1 Inf A -> Typing [] [] e2 Inf B ->
    step_or_v e1 e1' -> step_or_v e2 e2' -> consistent e1 e2 ->
    ( forall (e e' : exp) (A : typ),
        size_exp e < (size_exp e1 + size_exp e2) -> 
        Typing [] [] e Inf A -> step e e' -> 
        exists C, Typing [] [] e' Inf C /\ subsub C A ) ->
    consistent e1' e2'.
Proof with (simpl; elia).
  introv Typ1 Typ2 ST1 ST2 Cons IH. gen e1' e2' A B.
  induction Cons; intros; try solve [inverts ST1; inverts ST2; solve_false; eauto].
  + inverts ST1 as ST1'; inverts ST2 as ST2'.
    * constructor*.
    * inverts ST1'; inverts ST2'; solve_false.
    * inverts ST1'; inverts ST2'; solve_false.
    * inverts ST1'; inverts ST2'; solve_false.
      - inverts Typ1.
        forwards~ (?&?&_): Typing_chk2inf H11.
        applys* casting_consistent H6 H2.
      - inverts Typ1. clear IH.
        inductions H9; solve_false.
          forwards~: IHTyping1.
          forwards~: IHTyping2.
          inverts~ H2; inverts~ H3.
          ptype_unify.
          applys* C_disjoint.
        forwards: step_unique H6 H8. applys~ H9.
        substs~.
  + (* disjoint *)
    inverts ST1 as ST1'; [unify_pType e1' | unify_pType u1];
    inverts ST2 as ST2'.
    - forwards: principal_type_checks H Typ1.
      forwards: principal_type_checks H0 Typ2.
      substs. applys* C_disjoint H H0.
    - forwards* (C&?&?): IH u2.
      forwards: size_exp_min e1'...
      forwards: principal_type_checks H0 Typ2; substs.
      forwards: Typing_regular_0 Typ2.
      forwards~ (_&?): subsub2sub H6; auto.
      forwards~: step_prv_prevalue ST2'.
      applys* C_disjoint.
      forwards: principal_type_checks H4 Typ1; substs.
      forwards: principal_type_checks H Typ1; substs.
      applys* disjoint_covariance.
    - forwards* (C&?&?): IH u1.
      forwards: size_exp_min e2'...
      forwards: principal_type_checks H Typ1; substs.
      forwards: Typing_regular_0 Typ1.
      forwards~ (_&?): subsub2sub H6; auto.
      forwards~: step_prv_prevalue ST1'.
      applys* C_disjoint.
      apply disjoint_symm in H1.
      applys disjoint_symm.
      applys* disjoint_covariance.
    - forwards* (C&?&?): IH u2.
      forwards: size_exp_min u1...
      forwards: principal_type_checks H0 Typ2; substs.
      forwards: Typing_regular_0 Typ2.
      forwards~ (_&?): subsub2sub H6; auto.
      forwards~: step_prv_prevalue ST2'.

      forwards* (C'&?&?): IH u1.
      forwards: size_exp_min u2...
      forwards: principal_type_checks H Typ1; substs.
      forwards: Typing_regular_0 Typ1.
      forwards~ (_&?): subsub2sub H11; auto.
      forwards~: step_prv_prevalue ST1'.
      applys* C_disjoint.

      assert (disjoint nil A0 C) by applys* disjoint_covariance.
      apply disjoint_symm in H15.
      applys disjoint_symm.
      applys* disjoint_covariance.
  + inverts ST1 as ST1'; [ | inverts ST1' as ST1_1 ST1_2 ]; inverts Typ1;
    try solve [
      forwards*: IHCons1; try introv p1 p2 p3; try applys~ IH p2 p3; try (simpl; lia);
      forwards*: IHCons2; try introv p1 p2 p3; try applys~ IH p2 p3; try (simpl; lia)].
  + inverts ST2 as ST2'; [ | inverts ST2' as ST2_1 ST2_2 ]; inverts Typ2;
    try solve [
      forwards*: IHCons1; try introv p1 p2 p3; try applys~ IH p2 p3; try (simpl; lia);
      forwards*: IHCons2; try introv p1 p2 p3; try applys~ IH p2 p3; try (simpl; lia)]. 
  Unshelve. all: try apply nil; pick fresh x; apply x.
Qed.

Ltac indExpDirSize s :=
  assert (SizeInd: exists i, s < i) by eauto;
  destruct SizeInd as [i SizeInd];
  repeat match goal with | [ h : dirflag |- _ ] => (gen h) end;
  repeat match goal with | [ h : exp |- _ ] => (gen h) end;
  induction i as [|i IH]; [
      intros; match goal with | [ H : _ < 0 |- _ ] => inverts H end
    | intros ].

Definition size_dir dir :=
  match dir with
  | Inf => 0
  | Chk => 1
  end.

Theorem preservation_subsub : forall e e' dir A,
    Typing nil nil e dir A ->
    step e e' ->
    exists C, Typing nil nil e' dir C /\ subsub C A.
Proof with simpl; elia; eauto.
  introv.
  assert (Siz: exists n1 n2 n3, size_exp e < n1 /\ size_dir dir < n2 /\ size_typ A < n3).
  { exists. splits*. }
  destruct Siz as (n1 & n2 & n3 & Siz1 & Siz2 & Siz3).
  gen n2 n3 e' e dir A.
  induction n1; induction n2; induction n3; introv Siz1 Siz2 Siz3 Typ J; destruct_conj.
  all: try match goal with
           | H : _ < 0 |- _ => exfalso; inverts H
           end.

  inverts keep Typ as Ht1 Ht2 Ht3 Ht4 Ht5 Ht6;
    try solve [inverts J]; repeat simpl in SizeInd.
  - (* typing_app *)
    inverts J as J1 J2 J3.
    + forwards*: papp_preservation J2.
    + forwards (?&?&S2): IHn1 Ht1 J2...
      forwards: Typing_regular_0 H.
      lets* ( ?&? & Harr & Hsubsub & Hsub ): appDist_arr_subsub Ht2.
      exists x1. split~.
      forwards*: Typing_chk_dup Ht3 Hsub.
  - (* typing_tapp *)
    inverts J as J1 J2 J3.
    + forwards*: papp_preservation3 J2.
    + forwards* (B' & HT & HS) : IHn1 Ht1 J2...
      forwards: Typing_regular_0 HT.
      forwards* (C1' & C2' & HAD & HSS  & HAS): appDist_forall_subsub_disjoint Ht2 HS.
      exists (C2' ^-^ A0). splits~.
      applys Typ_tapp. apply HT. apply HAD.
      apply disjoint_covariance with C1. auto. auto.
  - (* typing_proj *)
    inverts J as J1 J2 J3.
    + forwards*: papp_preservation2 J2.
    + forwards* (?&?&S2): IHn1 Ht1 J1...
      forwards: Typing_regular_0 H.
      lets* ( ? & Harr & Hsub ): appDist_rcd_subsub Ht2 S2.
  - (* typing_merge *)
    (* disjoint *)
    inverts J as J1 J2 J3.
    + forwards (?&?&?): IHn1 Ht1 J1...
      forwards (?&?&?): IHn1 Ht2 J2...
      exists. splits. applys Typ_merge H H1.
      forwards: Typing_regular_0 H.
      forwards: Typing_regular_0 H1.
      forwards~ (?&?): subsub2sub H0; auto.
      forwards~ (?&?): subsub2sub H2; auto.
      apply disjoint_covariance with B.
      apply disjoint_symm.
      apply disjoint_covariance with A0.
      apply disjoint_symm. auto. auto. auto.
      eauto.
    + forwards (?&?&?): IHn1 Ht1 J2...
      exists. splits. applys Typ_merge H Ht2.
      forwards: Typing_regular_0 Ht1.
      apply disjoint_symm.
      apply disjoint_covariance with A0.
      apply disjoint_symm. auto.
      forwards~(?&?): subsub2sub H0. auto. eauto.
    + forwards (?&?&?): IHn1 Ht2 J2...
      exists. splits. applys Typ_merge Ht1 H.
      forwards: Typing_regular_0 H.
      apply disjoint_covariance with B.
      auto.
      forwards~(?&?): subsub2sub H0. auto. eauto.
  - (* typing_inter *)
    forwards (T1 &?&?): IHn3 Ht1...
    forwards (T2 &?&?): IHn3 Ht2...
    exists (T1&T2). split*.
     - (* typing_anno *)
    inverts J.
    + forwards~ (?&?&?): Typing_chk2inf Ht1.
      lets* (?&?): casting_preservation H.
    + forwards* (?&?&?): IHn1 Ht1 H3...
      exists A. split*.
      forwards: Typing_regular_0 H.
      forwards*: Typing_chk_subsub H H0.
      (* check subsub or refine the lemma *)
  - (* typing_fix *)
    inverts J as Lc. pick_fresh x.
    rewrite* (@subst_exp_intro x).
    forwards~ Typ_chk: Ht1.
    rewrite_env(nil++[(x,A)]++nil) in Typ_chk.
    lets~ (HF&HT): Typing_subst_2_inf_subsub Typ_chk Typ.
    clear HF. forwards~ : HT.
    exists A. split*.
  - (* typing_mergev *) (* consistent merge *)
    inverts J as J1 J2 J3;
    forwards: consistent_steps Ht4 Ht5; eauto;
      try introv p1 p2 p3; try forwards~: IHn1 p2 p3...
    1: forwards (?&?&?): IHn1 Ht4 J1...
    1: forwards (?&?&?): IHn1 Ht5 J2; elia; auto.
    2: forwards (?&?&?): IHn1 Ht4 J2; elia; auto.
    3: forwards (?&?&?): IHn1 Ht5 J2; elia; auto.
    all: exists; splits; [applys* Typ_mergev H | ]; eauto.
  - (* subsumption *)
    forwards* (?&?& HS): IHn2 Ht1...
    forwards: Typing_regular_0 H.
    forwards~ (?&?): subsub2sub HS; auto.
    assert (algo_sub nil x A) by auto_sub.
    exists* A.
Qed.


Theorem preservation : forall e e' dir A,
    Typing nil nil e dir A ->
    step e e' ->
    Typing nil nil e' Chk A.
Proof.
  intros e e' dir A H H0.
  lets* (?&?&?): preservation_subsub H H0.
  destruct dir.
  forwards: Typing_regular_0 H1.
  - forwards~: subsub2sub H2; auto.
    sapply* Typ_sub.
  - sapply* Typing_chk_subsub.
Qed.

(* Type Safety *)

Theorem preservation_multi_step : forall e e' dir A,
    Typing nil nil e dir A ->
    e ->* e' ->
    exists C, Typing nil nil e' dir C /\ subsub C A.
Proof.
  introv Typ Red.
  gen A. inductions Red; intros.
  - exists. splits; eauto using Typing_lc_typ.
  - lets* (?&?&?): preservation_subsub Typ H.
    forwards* (?&?&?): IHRed H0.
    exists x0. split*.
    forwards*: subsub_trans H3 H1.
Qed.


Theorem type_safety : forall e e' A,
    Typing nil nil e Inf A ->
    e ->* e' ->
    value e' \/ exists e'', step e' e''.
Proof.
  introv Typ Red. gen A.
  induction Red; intros.
  lets*: progress Typ.
  lets* (?&?&?): preservation_subsub Typ H.
Qed.
