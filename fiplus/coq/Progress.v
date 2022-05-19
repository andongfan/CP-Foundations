(**
       determinism & progress
       also includes lemmas about Casting & Consistency
*)
Require Import LibTactics.
Require Import Arith Lia.
Require Export KeyProperties.

(***************************** casting ************************************)

#[export] Hint Immediate casting_prv_value : core.

Lemma casting_top_normal : forall (v v': exp),
    casting v t_top v' -> v' = e_top.
Proof.
  intros v v' H.
  inductions H; solve_false; auto.
Qed.


Lemma casting_toplike : forall A v1 v2 v1' v2',
    topLike nil A -> value v1 -> value v2 -> casting v1 A v1' -> casting v2 A v2' -> v1' = v2'.
Proof with (split_unify; solve_false; auto).
  assert (HH: forall v v', value v -> casting v t_top v' -> v' = e_top). {
    intros.
    inductions H0; solve_false; eauto;
    inverts H; forwards*: IHcasting.
  }
  assert (HHarrow: forall v v' A1 A2, value v -> ord (t_arrow A1 A2) ->
                   topLike nil (t_arrow A1 A2) ->
                   casting v (t_arrow A1 A2) v' ->
          v' = (e_anno (e_abs t_top e_top) (t_arrow A1 A2))). {
    intros.
    inductions H2; solve_false; eauto.
  }
  assert (HHforall: forall v v' A1 A2, value v -> ord (t_forall A1 A2) ->
                   topLike nil (t_forall A1 A2) ->
                   casting v (t_forall A1 A2) v' ->
          v' = (e_anno (e_tabs e_top) (t_forall A1 A2))). {
    intros.
    inductions H2; solve_false; eauto.
  }
  assert (HHrcd: forall v v' l A, value v -> ord (t_rcd l A) ->
                   topLike nil (t_rcd l A) ->
                   casting v (t_rcd l A) v' ->
          v' = (e_anno (e_rcd l e_top) (t_rcd l A))). {
    intros.
    inductions H2; solve_false; eauto.
  }
  intros A v1 v2 v1' v2' TL Val1 Val2 Red1 Red2.
  gen v1' v2'.
  proper_ind A; intros;
  try solve [ inverts TL ].
  - inverts TL. inverts H1.
  - forwards*: HH Red1; forwards*: HH Val2 Red2; subst*.
  - forwards*: HHarrow TL Red1.
    forwards*: HHarrow TL Red2.
    congruence.
  - forwards*: HHforall TL Red1.
    forwards*: HHforall TL Red2.
    congruence.
  - forwards*: HHrcd TL Red1.
    forwards*: HHrcd TL Red2.
    congruence.
  - inverts Red1; solve_false; try solve [inverts H1; solve_false].
    inverts Red2; solve_false; try solve [inverts H1; solve_false].
    split_unify.
    forwards*: IHr1 H1 H4.
    forwards*: IHr2 H2 H5.
    congruence.
Qed.

Lemma casting_sub: forall v v' A B,
    value v -> casting v A v' -> pType v B -> TWell nil B -> algo_sub nil B A.
Proof with eauto with common.
  introv Val Red Typ Wf. gen B.
  induction Red; intros; try solve [ inverts Val; inverts Typ; auto_sub; eauto].
Qed.


(**************************** consistency ************************************)

Lemma consistent_symm: forall v1 v2,
    consistent v1 v2 -> consistent v2 v1.
Proof.
  intros. induction H; auto.
  applys* C_disjoint.
Qed.

Lemma consistent_refl: forall v A,
    value v -> Typing nil nil v Inf A -> consistent v v.
Proof with auto.
  intros v A Val Typ. gen A. induction Val;intros;auto.
  -(* top top *)
    apply C_disjoint with t_top t_top...
  - inverts~ Typ.
  - inverts~ Typ.
  - inverts~ Typ.
  - (*merge merge*)
    inverts~ Typ.
    + assert(consistent v1 v1). eauto.
      assert(consistent v2 v2). eauto.
      forwards:typ_value_ptype H1 Val1.
      forwards:typ_value_ptype H4 Val2.
      assert(consistent v1 v2). eauto.
      assert(consistent v2 v1). eauto. auto.
    + assert(consistent v1 v1). eauto.
      assert(consistent v2 v2). eauto.
      forwards: consistent_symm H8. auto.
Qed.

Lemma consistent_mergel: forall v1 v2 v,
    lc_exp v1 -> lc_exp v2 -> consistent (e_merge v1 v2) v -> consistent v1 v /\ consistent v2 v.
Proof.
  intros v1 v2 v Lc1 Lc2 H.
  inductions H.
  -
    inverts H.
    lets* (?&?): disjoint_andl_inv H1.
  - split; eauto.
  - forwards (?&?): IHconsistent1; try reflexivity; auto.
    forwards (?&?): IHconsistent2; try reflexivity; auto.
Qed.

Lemma consistent_merger: forall v1 v2 v,
    lc_exp v1 -> lc_exp v2 -> consistent v (e_merge v1 v2) -> consistent v v1 /\ consistent v v2.
Proof.
  intros v1 v2 v Lc1 Lc2 H.
  inductions H.
  -
    inverts H0.
    lets* (?&?): disjoint_andr_inv H1.
  - forwards (?&?): IHconsistent1; try reflexivity; auto.
    forwards (?&?): IHconsistent2; try reflexivity; auto.
  - split; eauto.
Qed.

(***************************** determinism ************************************)


Lemma consistent_casting_no_ambiguity: forall (v1 v2 v1' v2': exp) (C: typ),
    value v1 -> value v2 ->
    casting v1 C v1' -> casting v2 C v2' ->
    consistent v1 v2 -> v1' = v2'.
Proof with (solve_false; auto).
  introv Val1 Val2 R1 R2 Cons.
  gen v1 v2 v1' v2'. indTypSize (size_typ C).
  lets~ [?|(?&?&?)]: ord_or_split C.
  - inductions Cons.
    + inverts R1; inverts R2...
    + inverts R1; inverts R2...
    + forwards~ S1: casting_sub R1 H.
      forwards~ S2: casting_sub R2 H0.
      apply disjoint_soundness in H1.
      forwards~: H1 S1 S2.
      forwards*: casting_toplike R1 R2.
    + inverts Val1.
      inverts keep R1; try solve [forwards~: casting_toplike R1 R2]; solve_false; auto.
    + inverts Val2.
      inverts keep R2; try solve [forwards~: casting_toplike R1 R2]; solve_false; auto.
  - intros.
  inverts keep R1; try solve [forwards~: casting_toplike R1 R2]; solve_false; auto.
      inverts keep R2; try solve [forwards*: casting_toplike R1 R2]; solve_false; auto.
        split_unify.
        assert (HS: forall A B C, spl A B C -> size_typ B < size_typ A /\ size_typ C < size_typ A). {
          intros. induction H0; simpl; try lia.
          pick fresh x. forwards~: H6 x.
          forwards: size_typ_open_typ_wrt_typ_var C0 x.
          forwards: size_typ_open_typ_wrt_typ_var C2 x.
          forwards: size_typ_open_typ_wrt_typ_var B x.
          elia.
        }
        lets~ (?&?): HS H.
        forwards~: IH H1 H4. lia.
        forwards~: IH H2 H5. lia.
        congruence.
Qed.

Lemma casting_unique: forall v A B v1' v2',
    Typing nil nil v Inf B ->
    value v -> prevalue v -> casting v A v1' -> casting v A v2' -> v1' = v2'.
Proof with (solve_false; auto).
  intros.
  applys* consistent_casting_no_ambiguity.
  applys* consistent_refl.
Qed.

Lemma wrapping_prevalue : forall e A u,
    TWell nil A ->
    wrapping e A u ->
    prevalue u /\
    exists B, pType u B /\
    TWell nil B.
Proof.
  intros. induction* H0.
  forwards*: TWell_spl H0.
  forwards*: IHwrapping1.
  forwards*: IHwrapping2.
Qed.

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


Lemma wrapping_unique : forall e A C u1 u2,
    Typing nil nil e Chk C ->
    wrapping e A u1 ->
    wrapping e A u2 ->
    u1 = u2.
Proof with eauto; solve_false.
  introv Typ cast1 cast2. gen e u1 u2.
  indTypSize (size_typ A).
  inverts cast1; inverts cast2...
  - split_unify.
    forwards*: IH H0 H3; elia.
    forwards*: IH H1 H4; elia.
    congruence.
Qed.


Ltac papp_unify :=
  repeat match goal with
  | H: papp (e_anno (e_rcd _ _) _) (arg_la _) _ |- _ => inverts H
  | H: papp (e_anno (e_abs _ _) _) (arg_exp _) _ |- _ => inverts H
  | H: papp (e_anno (e_tabs _ _) _) (arg_typ _) _ |- _ => inverts H
         end; subst.


Ltac auto_unify := try binds_unify; typing_unify; split_unify; appdist_unify; papp_unify; ptype_unify.

Lemma papp_unique: forall v e e1 e2 A,
    value v -> Typing nil nil (e_app v e) Inf A ->
    papp v (arg_exp e) e1 ->
    papp v (arg_exp e) e2 ->
    e1 = e2.
Proof with eauto.
  intros v e e1 e2 A Val Typ P1 P2.
  gen e2 A.
  inductions P1; intros; inverts* P2.
  - inverts Val.
    inverts Typ.
    forwards*: wrapping_unique H1 H9.
    forwards* (_&?): appDist_arrow_unique H0 H8.
    substs~.
  - inverts Typ.
    inverts H2.
    + inverts H6.
      forwards*: Typing_chk_inter_inv H7.
      forwards*: IHP1_1.
      forwards*: IHP1_2.
      congruence.
    + inverts H6.
      forwards*: Typing_chk_inter_inv H7.
      forwards*: IHP1_1.
      forwards*: IHP1_2.
      congruence.
Qed.

Lemma papp_unique2: forall v1 la e1 e2 A,
    value v1 -> Typing nil nil (e_proj v1 la) Inf A -> papp v1 (arg_la la) e1 -> papp v1 (arg_la la) e2 -> e1 = e2.
Proof with eauto.
  intros v1 la e1 e2 A Val1 Typ P1 P2. gen e2 A.
  inductions P1; intros; inverts* P2.
  - inverts Val1.
    inverts Typ.
    inverts H10.
      inverts H9.
      forwards*: appDist_rcd_unique H0 H6.
      congruence.
      forwards*: appDist_rcd_unique H0 H6.
      congruence.
  - inverts Typ.
    inverts H5.
      inversion H6;subst.
      inverts H6.
      forwards*: Typ_proj H5.
      forwards*: IHP1_1 H1.
      forwards*: Typ_proj H10.
      forwards*: IHP1_2 H4.
      subst*.

      inversion H6;subst.
      inverts H6.
      forwards*: Typ_proj H9.
      forwards*: IHP1_1 H1.
      forwards*: Typ_proj H13.
      forwards*: IHP1_2 H4.
      subst*.
Qed.

Lemma papp_unique3: forall v1 e1 e2 A T,
    value v1 -> Typing nil nil (e_tapp v1 T) Inf A -> papp v1 (arg_typ T) e1 -> papp v1 (arg_typ T) e2 -> e1 = e2.
Proof with eauto.
  introv Val1 Typ P1 P2. gen e2 A.
  inductions P1; intros; inverts* P2.
  inverts Val1.
  inverts Typ.
  inverts H9.
    forwards* (_&?): appDist_forall_unique H1 H8.
    congruence.

  inverts Typ.
  inverts H6.

    inverts H2.
    forwards*: IHP1_1.
    forwards*: IHP1_2.
    congruence.
    forwards*: IHP1_1.
    forwards*: IHP1_2.
    congruence.

  inverts H2.
Qed.


Theorem step_unique: forall A (e e1 e2 : exp),
    Typing nil nil e Inf A -> step e e1 -> step e e2 -> e1 = e2.
Proof with intuition eauto.
  introv Typ Red1.
  gen A e2.
  lets Red1' : Red1.
  induction Red1;
    introv Typ Red2.
  - (* papp*)
    inverts* Red2.
    + forwards*: papp_unique H0 H5.
    + forwards*: step_not_value H5...
  - (* proj*)
    inverts* Red2.
    + forwards*: papp_unique2 H0 H5.
    + forwards*: step_not_value H4...
  - (* tapp*)
    inverts* Red2.
    + forwards*: papp_unique3 H0 H5.
    + forwards*: step_not_value H5...
  - (* annov*)
    inverts* Red2.
    + (* annov*)
      inverts* Typ.
      forwards* (N&Ty&S): Typing_chk2inf H8.
      forwards*: casting_unique H1 H7.
    + (* anno*)
      forwards*: step_not_value H6...
  - (* appl*)
    inverts Red2;
      try solve [forwards*: step_not_value Red1; intuition eauto].
    + (* appl*)
      inverts Typ.
      forwards: IHRed1...
      congruence.
  - (* merge*)
    inverts Typ;
      inverts* Red2;
      try solve [forwards*: step_not_value Red1_2; intuition eauto];
      try solve [forwards*: step_not_value Red1_1; intuition eauto];
      forwards*: IHRed1_1;
      forwards*: IHRed1_2;
      subst*...
  - (* mergel*)
    inverts* Red2;
      try solve [forwards*: step_not_value H4; intuition eauto].
    + (* mergel*)
      inverts* Typ;
        forwards*: IHRed1; intuition eauto;
        congruence.
  - (* merger*)
    inverts* Red2;
      try solve [forwards*: step_not_value H2; intuition eauto].
    + (* mergel*)
      forwards*: step_not_value H4...
    + (* merger*)
      inverts* Typ;
        forwards*: IHRed1; intuition eauto;
        congruence.
  - (* anno*)
    inverts* Red2;
      inverts* Typ;
      try solve [inverts* Red1; intuition eauto];
      try solve [lets*: step_not_value Red1; intuition eauto].

      inductions H5; solve_false.
      forwards*: IHTyping1. congruence.
    forwards*: IHRed1.
    congruence.
  - (* fix*)
    inverts* Red2.
  - (* rcd*)
    inverts* Typ. inverts* Red2.
    forwards*: step_not_value H1 Red1...
    forwards*: IHRed1... congruence.
  - (* proj*)
    inverts* Typ. inverts* Red2; try solve [forwards*: step_not_value Red1; intuition eauto]. forwards*: IHRed1. congruence.
  Unshelve.
  1,3,5: apply nil. 1,2,3: pick_fresh x; apply x.
Qed.

(***************************** progress ***************************************)

Lemma casting_progress: forall v A,
    value v -> prevalue v -> Typing nil nil v Chk A -> exists v', casting v A v'.
Proof with eauto 4.
  intros v A Val PV TypC.
  lets* (B&Typ&Sub): Typing_chk2inf TypC. clear TypC. gen v.
  inductions Sub; intros;
    try solve [inverts Typ; inverts Val; exists~].
  - inverts H0. inverts H3.
  - inverts Typ; solve_false...
    inverts Val; inverts H0; inverts H1.
  - inductions Typ; inverts Val...
    + inverts* H1; solve_false.
    + inverts* H1; solve_false.
    + inverts* H1; solve_false.
    + inverts H1; eauto 4; solve_false; exists*.
    + inverts H1; eauto 4; solve_false; exists*.
    + inverts H1; eauto 4; solve_false; exists*.
    + forwards* (?&?): IHTyp1.
  - inverts Typ; inverts~ Val; inverts H2; inverts H3.
  - inverts Typ; inverts Val...
    + forwards* (?&?): IHSub H3.
    + assert (topLike nil C \/ ~topLike nil C).
      applys toplike_decidable.
      destruct H2.
      inverts H2; try solve [ solve_false | exists* ].
      exists*.
    + assert (topLike nil C \/ ~topLike nil C).
      applys toplike_decidable.
      destruct H2.
      inverts H2; try solve [ solve_false | exists* ].
      exists*.
    + assert (topLike nil C \/ ~topLike nil C).
      applys toplike_decidable.
      destruct H2.
      inverts H2; try solve [ solve_false | exists* ].
      exists*.
    + forwards*: IHSub H6.
  - inverts Typ; inverts Val...
    + forwards* (?&?): IHSub H7.
    + assert (topLike nil C \/ ~topLike nil C).
      applys toplike_decidable.
      destruct H2.
      inverts H2; try solve [ solve_false | exists* ].
      exists*.
    + assert (topLike nil C \/ ~topLike nil C).
      applys toplike_decidable.
      destruct H2.
      inverts H2; try solve [ solve_false | exists* ].
      exists*.
    + assert (topLike nil C \/ ~topLike nil C).
      applys toplike_decidable.
      destruct H2.
      inverts H2; try solve [ solve_false | exists* ].
      exists*.
    + forwards*: IHSub H10.
  - assert(topLike nil (t_arrow A2 B2)\/~topLike nil (t_arrow A2 B2)).
    apply toplike_decidable. destruct H0.
    exists*. inverts Typ; solve_false.
    exists (e_anno e (t_arrow A2 B2)).
    assert (nil ||- (t_arrow A1 B1) <: (t_arrow A2 B2)) by eauto.
    applys Cast_anno...
    forwards~: Typing_regular_1 H1.
  - assert(topLike nil (t_forall B1 B2)\/~topLike nil (t_forall B1 B2)).
    apply toplike_decidable. destruct H2.
    exists*. inverts Typ; solve_false.
    exists (e_anno e (t_forall B1 B2)).
    assert (nil ||- (t_forall A1 A2) <: (t_forall B1 B2)) by eauto.
    applys Cast_anno...
    forwards~: Typing_regular_1 H3.
  - assert(topLike nil (t_rcd l B)\/~topLike nil (t_rcd l B)).
    apply toplike_decidable. destruct H0.
    exists*. inverts Typ; solve_false.
    exists (e_anno e (t_rcd l B)).
    assert (nil ||- (t_rcd l A) <: (t_rcd l B)) by eauto.
    applys Cast_anno...
    forwards~: Typing_regular_1 H1.
  - forwards* (?&?): IHSub1 Typ.
    forwards* (?&?): IHSub2 Typ.
Qed.


Lemma casting_progress_1: forall v A' A,
    value v ->
    Typing nil nil v Inf A' ->
    Typing nil nil v Chk A ->
    exists v', casting v A v'.
Proof.
  intros. forwards*: value_inf_prevalue.
  applys~ casting_progress.
Qed.


Lemma wrapping_progress: forall e A B,
    Typing nil nil e Chk A ->
    TWell nil B ->
    exists e', wrapping e B e'.
Proof with eauto 4 using Typing_regular_1, TWell_lc_typ.
  intros.
  forwards: Typing_regular_1 H.
  forwards: TWell_lc_typ H0.
  proper_ind B;
  eauto 4 using Typing_regular_1;
                try solve [ exists;
                            constructor*;
                            constructor*;
                            intros contra; solve_false].
  + inverts H0. inverts H5.
  + assert (TL: topLike nil (t_arrow A0 B) \/ ~topLike nil (t_arrow A0 B))
        by applys toplike_decidable.
      destruct TL.
      * exists. applys EW_topArrow...
      * exists. applys EW_anno...
  + assert (TL: topLike nil (t_forall A0 B) \/ ~topLike nil (t_forall A0 B))
      by applys toplike_decidable.
    destruct TL.
    * exists. applys EW_topAll...
    * exists. applys EW_anno...
  + assert (TL: topLike nil (t_rcd l A0) \/ ~topLike nil (t_rcd l A0))
      by applys toplike_decidable.
    destruct TL.
    * exists. applys EW_topRcd...
    * exists. applys EW_anno...
  + forwards~ (?&?): IHr1.
    forwards~ (?&?): IHr2.
    exists. applys EW_and...
Qed.

Lemma TWell_checked_abs : forall D G A e T,
    Typing D G (e_abs A e) Chk T ->
    TWell D A.
Proof.
  intros. inductions H; eauto.
Qed.


Lemma papp_progress: forall v e A,
    value v -> Typing nil nil (e_app v e) Inf A -> exists e', papp v (arg_exp e) e'.
Proof with eauto using Typing_regular_1.
  intros v e A Val Typ. gen A.
  induction Val; intros.
  - inverts Typ. inverts H1. inverts H4.
  - inverts Typ. inverts H1. inverts H4.
  - inverts Typ. inverts H4.
    inverts H7.
    inverts H6.
    forwards: TWell_checked_abs H11.
    forwards (e'&CE): wrapping_progress A H8...
    forwards (e'&CE): wrapping_progress A H8...
    forwards (e'&CE): wrapping_progress A H8...
    forwards~: TWell_checked_abs H6.
  - inverts Typ. inverts H3.
  - inverts Typ. inverts H3.
    forwards: Typing_chk_appDist H5 H6.
    inverts H1; solve_false.
  - inverts Typ. inverts H2.
  - inverts Typ. inverts H3.
    forwards: Typing_chk_appDist H5 H6.
    inverts H1; solve_false.
  - inverts Typ. inverts H2.
  - inverts Typ.
    inverts H1.
    + inverts H4.
      forwards: Typing_chk_inter_inv H5.
      forwards*: IHVal1.
      forwards*: IHVal2.
    + inverts H4.
      forwards: Typing_chk_inter_inv H5.
      forwards*: IHVal1.
      forwards*: IHVal2.
Qed.


Lemma papp_progress2: forall v1 la A,
    value v1 -> Typing nil nil (e_proj v1 la) Inf A -> exists e, papp v1 (arg_la la) e.
Proof with eauto.
  intros v1 la A Val1 Typ. gen A.
  induction Val1; intros;
    try solve [exists*].
  - inverts Typ. inverts H3. inverts H4.
  - inverts Typ. inverts H3. inverts H4.
  - inverts Typ.
    inverts H6.
    forwards: Typing_chk_appDist H5 H7.
    inverts H2; solve_false.
  - inverts Typ.
    inverts H5.
  - inverts Typ. inverts H5.
    forwards: Typing_chk_appDist H4 H6.
    inverts H1; solve_false.
  - inverts Typ. inverts H4.
  - inverts Typ. inverts H5.
    forwards: Typing_chk_appDist H4 H6.
    inverts H1; solve_false.
    exists*.
  - inverts Typ. inverts H4.
  - inverts Typ.
    inverts H3; inverts H4...
    + lets*: Typ_proj v1 la H3.
      lets*: Typ_proj v2 la H8.
      forwards* (?&?): IHVal1_1.
      forwards* (?&?): IHVal1_2.
    + lets*: Typ_proj v1 la H7.
      lets*: Typ_proj v2 la H11.
      forwards* (?&?): IHVal1_1.
      forwards* (?&?): IHVal1_2.
Qed.


Lemma papp_progress3: forall v1 A B,
    value v1 -> Typing nil nil (e_tapp v1 A) Inf B -> exists e, papp v1 (arg_typ A) e.
Proof with eauto.
  introv Val1 Typ. gen B.
  induction Val1; intros;
  forwards Lc : Typing_regular_1 Typ;
  inverts Lc.
  - inverts Typ. inverts H3. inverts H6.
  - inverts Typ. inverts H3. inverts H6.
  - inverts Typ. inverts H6.
    forwards: Typing_chk_appDist H8 H9.
    inverts H2; solve_false.
  - inverts Typ. inverts H5.
  - inverts Typ. inverts H5.
    exists*.
  - inverts Typ. inverts H4.
  - inverts Typ. inverts H5.
    forwards: Typing_chk_appDist H7 H8.
    inverts H1; solve_false.
  - inverts Typ. inverts H4.
  - inverts Typ.
    forwards (_&?): disjoint_regular H7.
    inverts H3; inverts H6...
    + inversion H;subst.
      forwards (?&?): disjoint_andr_inv B1 B2 H7.
      constructor; inverts H...
      forwards: Typ_tapp v1 A...
      forwards: Typ_tapp v2 A...
      forwards (?&?): IHVal1_1...
      forwards (?&?): IHVal1_2...
    + inversion H;subst.
      forwards (?&?): disjoint_andr_inv B1 B2 H7.
      constructor; inverts H...
      forwards: Typ_tapp v1 A...
      forwards: Typ_tapp v2 A...
      forwards (?&?): IHVal1_1...
      forwards (?&?): IHVal1_2...
Qed.


Theorem progress : forall dir e A,
    Typing nil nil e dir A ->
    value e \/ exists e', step e e'.
Proof with auto.
  introv Typ. lets Typ': Typ.
  inductions Typ; eauto;
    lets Lc: Typing_regular_1 Typ'.
  - (* var *)
    invert H1.
  - left...  
  - (* app *)
    inverts Lc.
    right.
    destruct~ IHTyp1 as [Val1 | [e1' Red1] ]...
    elia.
    + (* v1 v2 *)
      forwards (?&?): papp_progress Val1 Typ'.
      exists. applys Step_papp H0...
    + exists*.
  - left...  
  - (* tabs *)
    inverts Lc.
    right.
    destruct~ IHTyp as [Val1 | [e1' Red1] ].
    elia.
    + forwards* (?&?): papp_progress3 Val1 Typ'.
    + exists*.
  - (* proj *)
    inverts Lc.
    right.
    destruct~ IHTyp as [ Val1 | [t1' Red1] ].
    elia.
    + forwards* (?&?): papp_progress2 Val1 Typ'.
    + exists*.
  - left... 
  - (* merge *)
    inverts Lc.
    destruct~ IHTyp1 as [ Val1 | [t1' Red1] ];
      destruct~ IHTyp2 as [ Val2 | [t2' Red2] ];
      subst; elia.
    + (* e_merge v1 e2 *)
      inverts* Typ1.
    + (* e_merge e1 v2 *)
      inverts* Typ2.
    + (* e_merge e1 e2 *)
      inverts* Typ2.
  - (* anno *)
    inductions Typ.
    + left...
    + left...
    + left...
    + forwards~: IHTyp1.
      forwards~: IHTyp2.
      destruct H. inverts H; left...
      destruct H0. inverts H0; left...
      destruct_conj.
      right...
      inverts keep H; inverts keep H0; exists*.
    + inverts Typ'.
      forwards*: IHTyp0.
      destruct H0.
      forwards*: value_inf_prevalue.
        forwards*: casting_progress H3.
        right. destruct H0. exists (e_anno x B)...
  - (* fixpoint *)
    right. eauto.
  - (* mergev *)
    destruct~ IHTyp1 as [ Val1 | [t1' Red1] ];
      destruct~ IHTyp2 as [ Val2 | [t2' Red2] ];
      subst; elia.
    + (* e_merge v1 e2 *)
      inverts* Typ1.
    + (* e_merge e1 v2 *)
      inverts* Typ2.
    + (* e_merge e1 e2 *)
      inverts* Typ2.
Qed.
