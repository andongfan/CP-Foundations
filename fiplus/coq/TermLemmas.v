(**
   Lemmas about regularity and subst on typing &
   Lemmas about values and prevalues
 *)
Require Import LibTactics.
Require Export TypeLemmas.


#[export] Hint Extern 0 => match goal with
                   | [ H: value _ |- _ ] => inverts H; fail
                   | [ H: prevalue _ |- _ ] => inverts H; fail
                           end : FalseHd.


Ltac indExpSize s :=
  assert (SizeInd: exists i, s < i) by eauto;
  destruct SizeInd as [i SizeInd];
  repeat match goal with | [ h : exp |- _ ] => (gen h) end;
  induction i as [|i IH]; [
      intros; match goal with | [ H : _ < 0 |- _ ] => inverts H end
    | intros ].


(******************************************************************************)
(* inversion lemmas for lc *)

Ltac try_lc_exp_constructors :=
  match goal with
  | x : atom |- _ =>
    (* instead of constructors that contain forall *)
    applys lc_e_abs_exists +
    applys lc_e_fixpoint_exists +
    applys lc_e_tabs_exists;
    instantiate_cofinites_with x
  | |- _ =>
    let x := fresh in pick fresh x;
                      applys lc_e_abs_exists x +
                      applys lc_e_fixpoint_exists x +
                      applys lc_e_tabs_exists x;
                      instantiate_cofinites_with x
  end.


#[export] Hint Extern 1 (lc_exp _ ) => try_lc_exp_constructors : core.

(* destruct hypotheses *)

Ltac inverts_for_lc u :=
  repeat match goal with
         | H: lc_exp ?e |- _ => match e with
                                  context [ u ] => inverts H
                                end
         end.

#[export] Hint Extern 1 (lc_exp ?e ) =>
destruct_conj; progress inverts_for_lc e : core.


(* ********************************************************************** *)
(** ** Regularity of relations: typing *)

Lemma Typing_TCWell: forall D G e dir A,
    Typing D G e dir A -> TCWell D.
Proof.
  introv H. induction* H; instantiate_cofinites; auto.
Qed.


Lemma Typing_regular_0 : forall e D G dir A,
    Typing D G e dir A -> TWell D A.
Proof.
  intros. remember H as Typ. clear HeqTyp. inductions H; eauto.
  - clear Typ.
    inductions H0; auto.
    analyze_binds H2.
    forwards~: IHCWell.
    solve_uniq.
  - inverts* Typ.
    instantiate_cofinites.
    applys* TW_arrow.
  - forwards*: IHTyping1.
    forwards*: TWell_appDist H2 H0.
  - pick fresh x and apply TW_all.
    pick fresh y.
    forwards*: H0 y.
    forwards*: Typing_TCWell H2.
    forwards~: H1 x.
  - forwards*: IHTyping.
    forwards*: TWell_appDist H2 H0.
    forwards*: disjoint_regular H1.
    destruct H4 as [H4 _].
    forwards*: TWell_all_open H3 H4.
  - forwards*: IHTyping.
    forwards*: TWell_appDist H1 H0.
  - pick fresh x. forwards*: H0 x.
  - assert(TWell D A).
    rewrite_env(nil ++ D ++ nil).
    apply TWell_weakening. auto.
    assert(TWell D B).
    rewrite_env(nil ++ D ++ nil).
    apply TWell_weakening. auto.
    auto.
Qed.

Lemma Typing_lc_typ : forall e D G dir A,
    Typing D G e dir A -> lc_typ A.
Proof.
  intros. forwards*: Typing_regular_0 H.
Qed.

#[export] Hint Immediate Typing_lc_typ Typing_regular_0 : core.


Lemma Typing_regular_1 : forall e D G dir A,
    Typing D G e dir A -> lc_exp e.
Proof with (eauto 3).
  introv H.
  induction H...
Qed.
  (* instantiate_cofinites. applys* lc_e_abs_exists. *)


Lemma Typing_regular_2 : forall D G e dir T,
    Typing D G e dir T -> uniq G.
Proof.
  intros. induction* H; instantiate_cofinites; solve_uniq.
Qed.


Lemma Typing_regular_3 : forall D G e dir T,
    Typing D G e dir T -> uniq D.
Proof.
  intros. induction* H; instantiate_cofinites; solve_uniq.
Qed.

Lemma Typing_CWell: forall D G e dir A,
    Typing D G e dir A -> CWell D G.
Proof.
  introv H.
  induction* H; instantiate_cofinites.
    try forwards*: H0 x;
    try forwards*: H1 x;
    try forwards*: H2 x;
    try inverts* H1;
    try inverts* H3.
  inverts~ H0.
Qed.

(* get lc_typ A from typing related hypotheses *)
#[export] Hint Extern 1 (lc_typ ?A) =>
match goal with
| H: binds _ A _ |- _ => applys TWell_lc_typ; applys CWell_TWell H
| H: CWell _ ((_, A) :: _) |- _ => applys TWell_lc_typ; applys CWell_TWell H; try applys binds_trivial
| H: Typing _ ((_, A) :: _) _ _ _ |- _ => apply Typing_CWell in H; applys TWell_lc_typ; applys CWell_TWell H; try applys binds_trivial
| H: Typing ((_, A) :: _) _ _ _ _ |- _ => apply Typing_TCWell in H; apply TCWell_cons_TWell in H; applys TWell_lc_typ H
end : core.

(* ********************************************************************** *)
(** ** Regularity of relations: term related *)

#[export] Hint Extern 1 (lc_exp ?e ^ _) =>
match goal with
| H: lc_exp (e_abs _ e _) |- _ => inverts H
| H: lc_exp (e_fixpoint e _) |- _ => inverts H
end : core.

#[export] Hint Extern 1 (lc_exp (open_exp_wrt_typ ?e _)) =>
match goal with
| H: lc_exp (e_tabs _ e _) |- _ => inverts H
end : core.

#[export] Hint Extern 3 (lc_exp _) =>
match goal with
| H: forall x : atom, x `notin` _ -> _ |- _ =>
  progress instantiate_cofinites
end : LcHd.

Lemma ptype_lc : forall u A,
    pType u A -> lc_typ A.
Proof.
  intros. induction* H.
Qed.

Lemma value_lc : forall v,
    value v -> lc_exp v.
Proof.
  introv H. induction* H.
Qed.

Lemma casting_regular : forall v1 A v2,
    casting v1 A v2 -> TWell nil A /\ lc_typ A /\ lc_exp v1 /\ lc_exp v2.
Proof.
  introv H.
  induction H; destruct_conj; repeat split~.
Qed.

Lemma wrapping_lc : forall e1 A e2,
    wrapping e1 A e2 -> lc_typ A /\ lc_exp e1 /\ lc_exp e2.
Proof with eauto.
  introv H.
  induction H; destruct_conj; repeat split...
Qed.

Ltac solve_lc_3 u :=
  match goal with
  | H: algo_sub _ u _ |- _ => lets (?&?): algo_sub_lc H; assumption
  | H: algo_sub _ _ u |- _ => lets (?&?): algo_sub_lc H; assumption
  | H: sub _ u _ |- _ => lets (?&?): sub_lc H; assumption
  | H: sub _ _ u |- _ => lets (?&?): sub_lc H; assumption
  | H: subsub u _ |- _ => lets (?&?): subsub_lc H; assumption
  | H: subsub _ u |- _ => lets (?&?): subsub_lc H; assumption
  | H: Typing _ _ _ _ u |- _ => lets : Typing_lc_typ H; assumption
  | H: Typing _ _ u _ _|- _ => lets : Typing_regular_0 H; assumption
  | H: disjoint _ u _ |- _ => lets (?&?&?): disjoint_lc H; assumption
  | H: disjoint _ _ u |- _ => lets (?&?&?): disjoint_lc H; assumption
  | H: pType _ u |- _ => lets: ptype_lc H; assumption
  | H: value u |- _ => lets: value_lc H; assumption
  | H: casting u _ _ |- _ => lets (?&?&?&?): casting_regular H; assumption
  | H: casting _ u _ |- _ => lets (?&?&?&?): casting_regular H; assumption
  | H: casting _ _ u |- _ => lets (?&?&?&?): casting_regular H; assumption
  | H: wrapping u _ _ |- _ => lets (?&?&?): wrapping_lc H; assumption
  | H: wrapping _ u _ |- _ => lets (?&?&?): wrapping_lc H; assumption
  | H: wrapping _ _ u |- _ => lets (?&?&?): wrapping_lc H; assumption
  end.

#[export] Hint Extern 1 (lc_typ ?A ) => progress solve_lc_3 A : core.
#[export] Hint Extern 1 (lc_exp ?e ) => progress solve_lc_3 e : core.

#[local] Hint Resolve lc_body_exp_wrt_typ : core.
#[local] Hint Extern 1 => match goal with H: lc_arg _ |- _ => inverts H end : core.

Lemma papp_lc: forall v1 arg e,
    papp v1 arg e -> lc_exp v1 /\ lc_arg arg /\ lc_exp e.
Proof with eauto.
  introv H. induction H; destruct_conj; splits; try assumption; try constructor...
  - apply~ lc_body_exp_wrt_exp...
  - apply lc_body_exp_wrt_typ...
    inverts* H.
  - apply lc_body_typ_wrt_typ...
Qed.

Lemma step_lc: forall e1 e2,
    step e1 e2 -> lc_exp e1 /\ lc_exp e2.
Proof.
  introv H.
  induction H; lets: papp_lc; firstorder; eauto with lngen.
Qed.


Ltac solve_lc_4 u :=
  match goal with
  | H: papp u _ _ |- _ => lets (?&?&?): papp_lc H; assumption
  | H: papp _ (arg_exp u) _ |- _ =>
    let H:= fresh in lets (?&H&?): papp_lc H; inverts H; assumption
  | H: papp _ _ u |- _ => lets (?&?&?): papp_lc H; assumption
  | H: step u _ |- _ => lets (?&?): step_lc H; assumption
  | H: step _ u |- _ => lets (?&?): step_lc H; assumption
  end.

#[export] Hint Extern 2 (lc_exp ?e ) => progress solve_lc_4 e : core.

#[export] Hint Extern 1 =>
match goal with
| H: papp _ ?u _ |- lc_arg ?u => lets (?&?&?): papp_lc H; assumption
| H: papp _ (arg_typ ?u) _ |- lc_typ ?u =>
  let H:= fresh in lets (?&H&?): papp_lc H; inverts H; assumption
end : core.


Ltac solve_lc :=
  repeat match goal with
         | H: ord _ |- _ => lets: ord_lc H; clear H
         | H: spl _ _ _ |- _ => lets (?&?&?): split_lc H; clear H
         | H: topLike _ _ |- _ => lets: topLike_lc H; clear H
         | H: algo_sub _ _ _ |- _ => lets (?&?): algo_sub_lc H; clear H
         | H: sub _ _ _ |- _ => (lets (?&?): sub_lc H; clear H)
         | H: R _ |- _ => lets: r_lc H; clear H
         | H: appDist _ _ |- _ => (lets (?&?): appDist_lc H; clear H)
         | H: disjoint_axiom _ _ |- _ => (lets (?&?): disjoint_axiom_lc H; clear H)
         | H: disjoint _ _ _ |- _ => ( lets (?&?&?): disjoint_lc H; clear H )
         | H: Typing _ _ _ _ _|- _ => lets : Typing_lc_typ H; lets : Typing_regular_1 H; lets : Typing_regular_0 H; clear H
         | H: pType _ _ |- _ => lets : ptype_lc H; clear H
         | H: value _ |- _ => lets: value_lc H; clear H
         | H: casting _ _ _ |- _ => lets (?&?&?&?): casting_regular H; clear H
         | H: papp _ _ _ |- _ => lets (?&?&?): papp_lc H; clear H
         | H: step _ _ |- _ => lets (?&?): step_lc H; clear H
         end;
  repeat match goal with
         | H: lc_arg _ |- _ => inverts H
         | H: lc_exp (e_abs _ _ _) |- _ => inverts H
         | H: lc_exp (e_abs _ _ _) |- _ => inverts H
         | H: lc_exp (e_tabs _ _ _) |- _ => inverts H
         | H: lc_exp (e_tabs _ _ _) |- _ => inverts H
         | H: lc_exp (e_fixpoint _ _) |- _ => inverts H
         | H: lc_typ (t_and _ _) |- _ => inverts H
         | H: lc_typ (t_rcd _ _) |- _ => inverts H
         | H: lc_typ (t_arrow _ _) |- _ => inverts H
         | H: lc_typ (t_forall _ _) |- _ => inverts H
         end;
  match goal with
    |- lc_arg _ => applys lc_arg_exp + applys lc_arg_la + applys lc_arg_typ
  end;
  progress repeat
           (trivial; try_lc_typ_constructors + try_lc_exp_constructors).


#[export] Hint Extern 3 (lc_typ ?A) =>
match goal with
| H: forall x : atom, x `notin` _ -> _ |- _ =>
  progress instantiate_cofinites
end : LcHd.

#[local] Hint Immediate Typing_CWell CWell_TWell : core.


Ltac solve_twell_2 A :=
  match goal with
         | H: Typing _ _ _ _ _ |- _ => match type of H with context[ A ] =>
                                                            lets: Typing_CWell H;
                                                            lets: Typing_TCWell H;
                                                            lets: Typing_regular_0 H;
                                                            lets: Typing_regular_1 H;
                                                            lets: Typing_regular_2 H;
                                                            lets: Typing_regular_3 H
                                       end; clear H
         | H: casting _ _ _ |- _ => match type of H with context[ A ] =>
                                         lets (?&?&?&?): casting_regular H; clear H
                                       end; clear H
  end.

#[export] Hint Extern 1 (TCWell ?D ) => progress solve_twell_2 D; easy + (repeat solve_tcwell_0 D; easy) : core.
#[export] Hint Extern 1 (TWell ?D ?A ) => progress (solve_twell_2 A; repeat solve_twell_0 A); easy : core.
#[export] Hint Extern 1 (TWell ?D ?A -^ _ ) => progress (solve_twell_2 A; solve_twell_0 A) : core.


(******************************** value ***************************************)

Lemma fv_in_dom: forall D G e dir T,
    Typing D G e dir T -> termfv_exp e [<=] dom G.
Proof.
  intros D G e dir T H.
  induction H; simpl; try fsetdec.
  - (* typing_var*)
    apply binds_In in H1.
    fsetdec.
  - (* typing_abs*)
    pick fresh x for (L \u dom (G) \u termfv_exp e).
    assert (Fx : termfv_exp (e ^ x) [<=] dom ([(x,A)] ++ G)).
    { tassumption. auto. }
    simpl in Fx.
    assert (Fy : termfv_exp e [<=] termfv_exp (e ^ x)) by
        eapply termfv_exp_open_exp_wrt_exp_lower.
    fsetdec.
  - (* typing_tabs*)
    pick fresh x for (L \u dom (G) \u termfv_exp e).
    assert (Fx : termfv_exp (open_exp_wrt_typ e (t_tvar_f x)) [<=] dom G).
    { forwards*: H1 x. }
    assert (Fy : termfv_exp e [<=] termfv_exp (open_exp_wrt_typ e (t_tvar_f x))).
    eapply termfv_exp_open_exp_wrt_typ_lower.
    fsetdec.
  - (* typing_fix*)
    pick fresh x for (L \u dom (G) \u termfv_exp e).
    assert (Fx : termfv_exp (e ^ x) [<=] dom ([(x,A)] ++ G)).
    { forwards*: H0 x. }
    simpl in Fx.
    assert (Fy : termfv_exp e [<=] termfv_exp (e ^ x)) by
        eapply termfv_exp_open_exp_wrt_exp_lower.
    fsetdec.
Qed.

Lemma TY_not_in: forall X D G e dir A,
    X `notin` (dom D) -> Typing D G e dir A -> X `notin` (typefv_exp e).
Proof.
  intros. induction H0; auto.
    - simpl. forwards(?&?): algo_sub_regular H0.
      forwards: TW_not_in H3 H.
      forwards: TW_not_in H4 H.
      pick fresh Y.
      assert(X `notin` typefv_exp (e ^ Y)). auto.
      assert(AtomSetImpl.Subset (typefv_exp e) (typefv_exp (e ^ Y))).
      apply typefv_exp_open_exp_wrt_exp_rec_lower.
      assert(X `notin` typefv_exp e). auto.
      assert(Typing D ((Y, A) :: G) (e ^ Y) Chk B2). auto.
      apply Typing_regular_0 in H10.
      forwards: TW_not_in H10 H. auto.
    - simpl. pick fresh Y. instantiate_cofinites_with Y.
      assert(Typing ((Y, A) :: D) G (open_exp_wrt_typ e (t_tvar_f Y)) Chk (B -^ Y)).
      auto.
      assert(X `notin` typefv_exp (open_exp_wrt_typ e (t_tvar_f Y))). auto.
      assert(AtomSetImpl.Subset (typefv_exp e) (typefv_exp (open_exp_wrt_typ e (t_tvar_f Y)))).
      apply typefv_exp_open_exp_wrt_typ_rec_lower.
      assert(X `notin` typefv_exp e). auto.
      forwards: Typing_TCWell H3. inversion H7;subst.
      inversion H13;subst.
      forwards: TW_not_in H12 H.
      forwards: Typing_regular_0 H3.
      assert( X # ((Y, A) :: D)). auto.
      forwards: TW_not_in H9 H14.
      assert(AtomSetImpl.Subset [[B]] [[B -^ Y]]).
      apply typefv_typ_open_typ_wrt_typ_rec_lower. auto.
    - simpl. forwards(?&?): disjoint_regular H2.
      forwards: TW_not_in H3 H. auto.
    - simpl. forwards: Typing_regular_0 H0.
      forwards: TW_not_in H1 H. auto.
    - simpl. pick fresh Y.
      assert (Typing D ((Y, A) :: G) (e ^ Y) Chk A) by auto.
      apply Typing_regular_0 in H2.
      forwards: TW_not_in H2 H.
      assert(X `notin` typefv_exp (e ^ Y)). auto.
      assert(AtomSetImpl.Subset (typefv_exp e) (typefv_exp (e ^ Y))).
      apply typefv_exp_open_exp_wrt_exp_rec_lower.
      assert(X `notin` typefv_exp e). auto. auto.
Qed.


Lemma value_no_fv : forall D v dir T,
    Typing D nil v dir T -> termfv_exp v [<=] empty.
Proof.
  intros D v.
  pose proof (fv_in_dom D nil v).
  intuition eauto.
Qed.

Lemma subst_value : forall D v T dir z u,
    Typing D nil v dir T -> subst_exp u z v = v.
Proof.
  introv Typ.
  lets* Fv: value_no_fv Typ.
  forwards*: subst_exp_fresh_eq.
  rewrite Fv.
  fsetdec.
Qed.

Lemma value_merge_l_inv : forall v1 v2,
    value (e_merge v1 v2) -> value v1.
Proof.
  introv H.
  inverts~ H.
Qed.

Lemma value_merge_r_inv : forall v1 v2,
    value (e_merge v1 v2) -> value v2.
Proof.
  introv H.
  inverts~ H.
Qed.

(* relys on lemmas about lc in wellformedness *)
#[local]
 Hint Extern 3 (lc_typ _) =>
progress (solve_lc; trivial) : LcHd.

Lemma casting_prv_value: forall v A v',
    lc_typ A -> value v -> casting v A v' -> value v'.
Proof with eauto with lngen.
  intros v A v' Lc Val Red.
  induction Red; auto; inverts Val...
Qed.

#[export] Hint Immediate value_merge_l_inv value_merge_r_inv value_lc casting_prv_value : core.

#[export] Hint Extern 1 => match goal with
                   | [ H: step _ _ |- _ ] => inverts H; fail
                   | [ H: casting _ _ |- _ ] => inverts H; fail
                 end : FalseHd.


Lemma step_not_value: forall (v:exp),
    value v -> irred exp step v.
Proof with solve_false.
  introv.
  unfold irred.
  induction v; introv H; inverts H...
  all: try solve [unfold not; intros HF; solve_false].
  1: (* merge *) unfold not; intros HF; inverts* HF.
  all: (* anno *) unfold not; intros HF; inverts* HF...
Qed.


Lemma value_no_step : forall (v t: exp),
    value v -> v ->* t -> v = t.
Proof.
  introv Val Red.
  induction* Red.
  lets : step_not_value Val H.
  tryfalse.
Qed.


#[export] Hint Extern 1 => match goal with
                           | [ H1: step ?e _, H2: value ?e |- _ ] =>
                             forwards: step_not_value H2 H1
                           | [ H1: step (e_lit _) _ |- _ ] =>
                             forwards: step_not_value H1
                           | [ H1: step e_top _ |- _ ] =>
                             forwards: step_not_value H1
                           end : FalseHd.

Lemma cast_prevalue : forall e A e',
    casting e A e' ->
    prevalue e'.
Proof.
  intros. inductions H; eauto.
Qed.

#[export] Hint Immediate cast_prevalue : core.

Lemma step_prv_prevalue : forall u1 u2,
    step u1 u2 -> prevalue u1 -> prevalue u2.
Proof.
  intros. gen u2. inductions H0; intros.
  - inverts H; solve_false;
    inverts H0; solve_false.
  - inverts H.
  - inverts* H1.
  - inverts* H.
Qed.

Lemma consistent_prevalue1 : forall u1 u2,
    consistent u1 u2 -> lc_exp u1 -> prevalue u1.
Proof.
  intros u1 u2 H. induction~ H.
Qed.

Lemma consistent_prevalue2 : forall u1 u2,
    consistent u1 u2 -> prevalue u2.
Proof.
  intros u1 u2 H. induction~ H.
Qed.

#[export] Hint Immediate step_prv_prevalue consistent_prevalue1 consistent_prevalue2: core.


Lemma prevalue_merge_l_inv : forall u1 u2,
    prevalue (e_merge u1 u2) -> prevalue u1.
Proof.
  intros u1 u2 H.
  inductions H; auto.
Qed.

Lemma prevalue_merge_r_inv : forall u1 u2,
    prevalue (e_merge u1 u2) -> prevalue u2.
Proof.
  intros u1 u2 H.
  inductions H; auto.
Qed.


#[export] Hint Immediate prevalue_merge_l_inv prevalue_merge_r_inv: core.

Lemma value_subst : forall v A P Z,
    value v ->
    pType v A ->
    lc_typ P ->
    prevalue (typsubst_exp P Z v) /\ pType (typsubst_exp P Z v) [Z ~~> P] A.
Proof with eauto 3 using typsubst_typ_lc_typ, typsubst_exp_lc_exp.
  introv Value PT Lc. gen A. inductions Value; intros; inverts PT; simpls; eauto.
  - forwards~: typsubst_exp_lc_exp P Z H0.
    splits. constructor... constructor...
  - forwards~: typsubst_exp_lc_exp P Z H.
    splits. constructor... constructor...
  - forwards~: typsubst_exp_lc_exp P Z H.
    splits. constructor... constructor...
  - forwards~: IHValue1 H1.
    forwards~: IHValue2 H3.
    splits.
    apply PV_merge; firstorder.
    apply PT_merge; firstorder.
Qed.
