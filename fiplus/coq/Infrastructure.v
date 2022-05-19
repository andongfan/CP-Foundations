(**
   lemmas that are based only on the syntax and well-formedness
*)
Require Import LibTactics.
Require Import Coq.micromega.Lia.
Require Export rules_inf.

(************************************ Ltac ************************************)

(* try any assumption *)
Ltac tassumption := match goal with | H : _ |-_=> apply H end.

(* try solve the goal by contradiction *)
Create HintDb FalseHd.
Ltac solve_false := try intro; try solve [false; eauto 3 with FalseHd].

(* destrcut conjunctions *)
Ltac destruct_conj :=
  repeat match goal with H: ?T |- _ =>
    match T with
    | _ /\ _ => destruct H
    | exists _, _ => destruct H
    end
         end.

(* Ltac from Alvin *)
Ltac detect_fresh_var_and_do t :=
  match goal with
  | Fr : ?x `notin` ?L1 |- _ => t x
  | _ =>
    let x := fresh "x" in
    pick fresh x; t x
  end.

Ltac instantiate_cofinite_with H X :=
  match type of H with
  | forall x, x `notin` ?L -> _ =>
    let H1 := fresh "H" in
    assert (H1 : X `notin` L) by solve_notin;
    specialize (H X H1); clear H1
  end.

Ltac instantiate_cofinites_with x :=
  repeat match goal with
  | H : forall x, x `notin` ?L -> _ |- _ =>
    instantiate_cofinite_with H x
  | H : forall X : typevar , _ |- _ =>
    specialize (H X)
  | H : forall X : termvar , _ |- _ =>
    specialize (H X)
         end;
  destruct_conj.

Ltac instantiate_cofinites :=
  detect_fresh_var_and_do instantiate_cofinites_with.

Ltac applys_and_instantiate_cofinites_with H x :=
  applys H x; try solve_notin; instantiate_cofinites_with x.

Ltac pick_fresh_applys_and_instantiate_cofinites H :=
  let X:= fresh in
  pick fresh X; applys_and_instantiate_cofinites_with H X.

Ltac detect_fresh_var_and_apply H :=
  let f x := applys_and_instantiate_cofinites_with H x in
  detect_fresh_var_and_do f.


(************************ Notations related to types **************************)
Notation "A & B"         := (t_and A B) (at level 66).
Notation "[ z ~~> u ] t" := (typsubst_typ u z t) (at level 0).
Notation "t ^-^ u"       := (open_typ_wrt_typ t u) (at level 67).
Notation "t -^ x"        := (open_typ_wrt_typ t (t_tvar_f x))(at level 67).
Notation "[[ A ]]"       := (typefv_typ A) (A at level 99).


(*********************** Locally nameless related defns ***********************)
Fixpoint typefv_typ_range (E : list (atom*typ))
  : atoms :=
  match E with
    | nil => empty
    | (_, A) :: E' => [[A]] \u (typefv_typ_range E')
  end.

(* redefine gather_atoms for pick fresh *)
Ltac gather_atoms ::= (* for type var *)
  let A := gather_atoms_with (fun x : atoms => x) in
  let B := gather_atoms_with (fun x : atom => singleton x) in
  let C := gather_atoms_with (fun x : list (var * typ) => dom x) in
  let C':= gather_atoms_with (fun x : exp => termfv_exp x) in
  let D := gather_atoms_with (fun x : exp => typefv_exp x) in
  let E := gather_atoms_with (fun x : typ => typefv_typ x) in
  let F := gather_atoms_with (fun x : tctx => dom x) in
  let G := gather_atoms_with (fun x : ctx => dom x) in
  let G' := gather_atoms_with (fun x : ctx => typefv_typ_range x) in
  constr:(A `union` B `union` C `union` C' `union` D `union` E `union` F `union` G  `union` G').


(******************************************************************************)
Definition relation (X:Type) := X -> X -> Prop.

Section Star.

  Variable A : Type.
  Variable R : relation A.

  Inductive star: relation A:=
  | star_refl: forall a,
      star a a
  | star_step: forall a b c,
      R a b -> star b c -> star a c.

  Lemma star_one:
    forall a b, R a b -> star a b.
  Proof.
    eauto using star.
  Qed.

  Lemma star_trans:
    forall a b, star a b -> forall c, star b c -> star a c.
  Proof.
    induction 1; eauto using star.
  Qed.


  Hypothesis R_functional:
    forall a b c, R a b -> R a c -> b = c.

  Lemma star_star_inv:
    forall a b, star a b -> forall c, star a c -> star b c \/ star c b.
  Proof.
    induction 1; intros.
    - auto.
    - inversion H1; subst.
      + right. eauto using star.
      + assert (b = b0) by (eapply R_functional; eauto). subst b0.
        apply IHstar; auto.
  Qed.

  Definition irred a : Prop := forall b, ~(R a b).

  Lemma finseq_unique:
    forall a b b',
      star a b -> irred b ->
      star a b' -> irred b' ->
      b = b'.
  Proof.
    intros. destruct (star_star_inv _ _ H _ H1).
    - inversion H3; subst. auto. elim (H0 _ H4).
    - inversion H3; subst. auto. elim (H2 _ H4).
  Qed.


End Star.

#[export] Hint Constructors star : core.

#[export] Hint Resolve star_trans star_one : core.


(***************************** Other notations ********************************)
Notation "Γ ⊢ E ⇒ A" := (Typing Γ E Inf A) (at level 45).
Notation "Γ ⊢ E ⇐ A" := (Typing Γ E Chk A) (at level 45).


Notation "[ z ~> u ] e" := (subst_exp u z e) (at level 0).
Notation "t ^^ u"       := (open_exp_wrt_exp t u) (at level 67).
Notation "e ^ x"        := (open_exp_wrt_exp e (e_var_f x)).

Notation "v ~-> A v'" := (casting v A v') (at level 68).

Notation "R 'star'" := (star exp R) (at level 69).

Notation "t ->* t'" := (step star t t') (at level 68).

(** [x # E] to be read x fresh from E captures the fact that
    x is unbound in E . *)

Notation "x '#' E" := (x \notin (dom E)) (at level 67) : env_scope.

Definition env := list (atom * exp).


(******************************* vars *********************************)

Lemma notin_close : forall X A,
    X `notin` typefv_typ (close_typ_wrt_typ X A).
Proof.
  introv HF.
  apply typefv_typ_close_typ_wrt_typ in HF.
  applys* remove_iff X.
Qed.

#[export] Hint Resolve notin_close : core.


Lemma binds_trivial : forall x (A: typ) G,
    binds x A ((x, A) :: G).
Proof.  eauto. Qed.

#[export] Hint Resolve binds_trivial : core.

Lemma no_effect_subst: forall X E T,
    X `notin` (typefv_typ_range E) -> (map (typsubst_typ T X) E) = E.
Proof.
  intros.
  induction E. auto.
    simpl. destruct a.
  forwards: IHE. simpl in H. auto. rewrite H0.
  simpl in H.
  assert([X ~~> T] t = t).
    apply typsubst_typ_fresh_eq. auto. rewrite H1.
  auto.
Qed.

Lemma Degree_subst_alternative: forall n1 n C X Y,  size_typ C <= n1 -> X `notin` [[C]] -> degree_typ_wrt_typ n C ->
(open_typ_wrt_typ_rec n (t_tvar_f Y) (close_typ_wrt_typ_rec n X C) = C).
Proof.
  intros n1. induction n1. intros. destruct C;inversion H.
  apply_mutual_ind typ_mutind;default_simp.
  apply IHtyp1. lia. auto. auto.
  apply IHn1. lia. auto. auto.
  apply IHtyp1. lia. auto. auto.
  apply IHtyp2. lia. auto. auto.
  apply IHtyp1. lia. auto. auto.
  apply IHtyp2. lia. auto. auto.
  apply IHtyp. lia. auto. auto.
Qed.

Lemma Degree_subst: forall n C X Y, X `notin` [[C]] -> degree_typ_wrt_typ n C ->
(open_typ_wrt_typ_rec n (t_tvar_f Y) (close_typ_wrt_typ_rec n X C) = C).
Proof.
  intros. eapply Degree_subst_alternative. eauto. auto. auto.
Qed.

(*************************** open *********************************************)

Lemma open_into_and : forall B C X, (B&C) ^-^ X = (B ^-^ X) & (C ^-^ X).
Proof. eauto. Qed.

Lemma open_into_top : forall X, t_top -^ X = t_top.
Proof. eauto. Qed.

Lemma open_into_int : forall X, t_int -^ X = t_int.
Proof. eauto. Qed.

Ltac let_open_in := rewrite open_into_and + rewrite open_into_top + rewrite open_into_int.

#[export] Hint Extern 1 (lc_typ (_ ^-^ _)) => let_open_in; econstructor : core.
#[export] Hint Extern 1 (TWell _ (_ ^-^ _)) => let_open_in; econstructor : core.
#[export] Hint Extern 1 (spl (_ ^-^ _) _ _) => let_open_in; econstructor : core.
#[export] Hint Extern 1 (sub _ (_ ^-^ _) _) => let_open_in; econstructor : core.
#[export] Hint Extern 1 (sub _ _ (_ ^-^ _)) => let_open_in; econstructor : core.
#[export] Hint Extern 1 (algo_sub _ (_ ^-^ _) _) => let_open_in; econstructor : core.
#[export] Hint Extern 1 (algo_sub _ _ (_ ^-^ _)) => let_open_in; econstructor : core.

Lemma open_wrt_A: forall A X Y, t_tvar_f X = A -^ Y -> ((A = t_tvar_b 0 /\ X = Y) \/ A = t_tvar_f X).
Proof.
  intros. destruct A;inversion H.
    unfold open_typ_wrt_typ in H. simpl in H.
    destruct(lt_eq_lt_dec n 0). destruct s. inversion H. inversion H;subst. auto.
    inversion H. subst.
    auto.
Qed.

Lemma open_comm: forall A n n0 X Y,
    n0 <= n ->
    open_typ_wrt_typ_rec n0 (t_tvar_f Y) (open_typ_wrt_typ_rec (S n) (t_tvar_f X) A) =
    open_typ_wrt_typ_rec n (t_tvar_f X) (open_typ_wrt_typ_rec n0 (t_tvar_f Y) A).
Proof.
  intros A. induction A;intros;simpl;auto.
    - (* var_b *)
    simpl. destruct(lt_eq_lt_dec n (S n0)). destruct s. simpl.
      destruct(lt_eq_lt_dec n n1). destruct s.
      simpl. destruct(lt_eq_lt_dec n n0). destruct s. auto. subst.
      assert(~n1 <= n0). lia. contradiction.
      assert(~n1 <= n0). lia. contradiction. simpl. auto.
      simpl. destruct(lt_eq_lt_dec (n-1) n0). destruct s. auto.
      assert(~n < (S n0)). lia. contradiction. assert(~n < (S n0)). lia. contradiction.
      subst. destruct(lt_eq_lt_dec (S n0) n1). destruct s.
      assert(~n1<=n0). lia. contradiction. assert(~n1<=n0). lia. contradiction.
      simpl. destruct (lt_eq_lt_dec (n0 - 0) n0). destruct s.
      assert(~n0 - 0 < n0). lia. contradiction. auto.
      assert(~n0 < n0 - 0). lia. contradiction.
      simpl. destruct(lt_eq_lt_dec n n1). destruct s.
      assert(~n1 <= n0). lia. contradiction.
      assert(~n1 <= n0). lia. contradiction.
      destruct(lt_eq_lt_dec (n - 1) n1). destruct s.
      assert(~n1 <= n0). lia. contradiction.
      assert(~n1 <= n0). lia. contradiction.
      simpl. destruct(lt_eq_lt_dec (n - 1) n0). destruct s.
      assert(~(S n0) < n). lia. contradiction. assert(~(S n0) < n). lia. contradiction. auto.
   -  (* forall *)
      assert((open_typ_wrt_typ_rec n0 (t_tvar_f Y) (open_typ_wrt_typ_rec (S n) (t_tvar_f X) A1)) =
        (open_typ_wrt_typ_rec n (t_tvar_f X) (open_typ_wrt_typ_rec n0 (t_tvar_f Y) A1))). eauto.
      assert((open_typ_wrt_typ_rec (S n0) (t_tvar_f Y) (open_typ_wrt_typ_rec (S (S n)) (t_tvar_f X) A2)) =
        (open_typ_wrt_typ_rec (S n) (t_tvar_f X) (open_typ_wrt_typ_rec (S n0) (t_tvar_f Y) A2))).
      apply IHA2. lia. rewrite H0. rewrite H1. auto.
   -  (* arrow *)
      assert((open_typ_wrt_typ_rec n0 (t_tvar_f Y) (open_typ_wrt_typ_rec (S n) (t_tvar_f X) A1)) =
        (open_typ_wrt_typ_rec n (t_tvar_f X) (open_typ_wrt_typ_rec n0 (t_tvar_f Y) A1))). eauto.
      assert((open_typ_wrt_typ_rec n0 (t_tvar_f Y) (open_typ_wrt_typ_rec (S n) (t_tvar_f X) A2)) =
        (open_typ_wrt_typ_rec n (t_tvar_f X) (open_typ_wrt_typ_rec n0 (t_tvar_f Y) A2))). eauto.
      rewrite H0. rewrite H1. auto.
   -  (* and *)
      assert((open_typ_wrt_typ_rec n0 (t_tvar_f Y) (open_typ_wrt_typ_rec (S n) (t_tvar_f X) A1)) =
        (open_typ_wrt_typ_rec n (t_tvar_f X) (open_typ_wrt_typ_rec n0 (t_tvar_f Y) A1))). eauto.
      assert((open_typ_wrt_typ_rec n0 (t_tvar_f Y) (open_typ_wrt_typ_rec (S n) (t_tvar_f X) A2)) =
        (open_typ_wrt_typ_rec n (t_tvar_f X) (open_typ_wrt_typ_rec n0 (t_tvar_f Y) A2))). eauto.
      rewrite H0. rewrite H1. auto.
   -  (* rcd *)
      assert((open_typ_wrt_typ_rec n0 (t_tvar_f Y) (open_typ_wrt_typ_rec (S n) (t_tvar_f X) A)) =
        (open_typ_wrt_typ_rec n (t_tvar_f X) (open_typ_wrt_typ_rec n0 (t_tvar_f Y) A))). eauto.
      rewrite H0. auto.
Qed.

Lemma open_comm_2: forall A n n0 X Y,
    n0 <= n ->
    lc_typ X ->
    open_typ_wrt_typ_rec n0 (t_tvar_f Y) (open_typ_wrt_typ_rec (S n) X A) =
    open_typ_wrt_typ_rec n X (open_typ_wrt_typ_rec n0 (t_tvar_f Y) A).
Proof.
  intros A. induction A;intros;simpl;auto.
  - (* var_b *)
    simpl. destruct(lt_eq_lt_dec n (S n0)). destruct s. simpl.
    destruct(lt_eq_lt_dec n n1). destruct s.
      simpl. destruct(lt_eq_lt_dec n n0). destruct s. auto. subst.
      assert(~n1 <= n0). lia. contradiction.
      assert(~n1 <= n0). lia. contradiction. simpl. auto.
      simpl. destruct(lt_eq_lt_dec (n-1) n0). destruct s. auto.
      assert(~n < (S n0)). lia. contradiction. assert(~n < (S n0)). lia. contradiction.
      subst. destruct(lt_eq_lt_dec (S n0) n1). destruct s.
      assert(~n1<=n0). lia. contradiction. assert(~n1<=n0). lia. contradiction.
      simpl. destruct (lt_eq_lt_dec (n0 - 0) n0). destruct s.
      assert(~n0 - 0 < n0). lia. contradiction.
      apply open_typ_wrt_typ_rec_degree_typ_wrt_typ.
        apply degree_typ_wrt_typ_of_lc_typ in H0.
        apply degree_typ_wrt_typ_O. auto.
      assert(~n0 < n0 - 0). lia. contradiction.
      simpl. destruct(lt_eq_lt_dec n n1). destruct s.
      assert(~n1 <= n0). lia. contradiction.
      assert(~n1 <= n0). lia. contradiction.
      destruct(lt_eq_lt_dec (n - 1) n1). destruct s.
      assert(~n1 <= n0). lia. contradiction.
      assert(~n1 <= n0). lia. contradiction.
      simpl. destruct(lt_eq_lt_dec (n - 1) n0). destruct s.
      assert(~(S n0) < n). lia. contradiction. assert(~(S n0) < n). lia. contradiction. auto.
   -  (* forall *)
      assert((open_typ_wrt_typ_rec n0 (t_tvar_f Y) (open_typ_wrt_typ_rec (S n) X A1)) =
        (open_typ_wrt_typ_rec n X (open_typ_wrt_typ_rec n0 (t_tvar_f Y) A1))). eauto.
      assert((open_typ_wrt_typ_rec (S n0) (t_tvar_f Y) (open_typ_wrt_typ_rec (S (S n)) X A2)) =
        (open_typ_wrt_typ_rec (S n) X (open_typ_wrt_typ_rec (S n0) (t_tvar_f Y) A2))).
      apply IHA2. lia. auto. rewrite H1. rewrite H2. auto.
   -  (* arrow *)
      assert((open_typ_wrt_typ_rec n0 (t_tvar_f Y) (open_typ_wrt_typ_rec (S n) X A1)) =
        (open_typ_wrt_typ_rec n X (open_typ_wrt_typ_rec n0 (t_tvar_f Y) A1))). eauto.
      assert((open_typ_wrt_typ_rec n0 (t_tvar_f Y) (open_typ_wrt_typ_rec (S n) X A2)) =
        (open_typ_wrt_typ_rec n X (open_typ_wrt_typ_rec n0 (t_tvar_f Y) A2))). eauto.
      rewrite H1. rewrite H2. auto.
   -  (* and *)
      assert((open_typ_wrt_typ_rec n0 (t_tvar_f Y) (open_typ_wrt_typ_rec (S n) X A1)) =
        (open_typ_wrt_typ_rec n X (open_typ_wrt_typ_rec n0 (t_tvar_f Y) A1))). eauto.
      assert((open_typ_wrt_typ_rec n0 (t_tvar_f Y) (open_typ_wrt_typ_rec (S n) X A2)) =
        (open_typ_wrt_typ_rec n X (open_typ_wrt_typ_rec n0 (t_tvar_f Y) A2))). eauto.
      rewrite H1. rewrite H2. auto.
   -  (* rcd *)
      assert((open_typ_wrt_typ_rec n0 (t_tvar_f Y) (open_typ_wrt_typ_rec (S n) X A)) =
        (open_typ_wrt_typ_rec n X (open_typ_wrt_typ_rec n0 (t_tvar_f Y) A))). eauto.
      rewrite H1. auto.
Qed.


(*************************** uniq *********************************************)
Lemma uniq_dom_binds:forall (A:typ) D F x, uniq(F ++ [(x,A)]++ D) -> x # (F ++ D).
Proof.
  intros. induction F. simpl in H. simpl. inversion H;subst. auto.
    destruct a. simpl in H. inversion H;subst. apply IHF in H2.
      assert(a<>x). eauto. auto.
Qed.

Lemma uniq_bind_weakening : forall x (I J:typ) D F,
    uniq (F ++ (x ~ I) ++ D) ->
    uniq (F ++ (x ~ J) ++ D) .
Proof with eauto.
  intros. induction F. simpl. simpl in H. inversion H;subst. auto.
    destruct a. inversion H;subst. apply IHF in H2. simpl. apply uniq_push. auto. auto.
Qed.

#[export] Hint Immediate uniq_bind_weakening : core.


Lemma uniq_decidable:
  forall (G:tctx), uniq G\/~uniq G.
Proof.
  intros. induction G. auto.
    destruct a.
    assert((exists x, binds a x G)\/~(exists x, binds a x G)).
    apply binds_lookup_dec.
    destruct IHG. destruct H. destruct H. apply binds_In in H.
    right. unfold not. intros. inversion H1;subst. auto.
    assert(~a `in` dom G). unfold not. intros.
    apply binds_In_inv in H1. auto. auto.
    right. unfold not. intros. inversion H1;subst. auto.
Qed.


Lemma uniq_subst: forall X Y C D E,
    Y `notin` (Metatheory.union (dom D) (dom E))->
    uniq (E ++ [(X, C)] ++ D) -> uniq ((map (typsubst_typ (t_tvar_f Y) X)E)++ [(Y, C)]++ D).
Proof.
  intros. induction E. simpl. simpl in H0. inversion H0;subst. apply uniq_push. auto. auto.
  destruct a. simpl. simpl in H0. inversion H0;subst.
  apply IHE in H3. apply uniq_push. auto. auto. auto.
Qed.


Lemma Nat_decidable: forall l1 l2:nat,{l1=l2}+{~l1=l2}.
Proof.
    intros l1. induction l1. intros. induction l2.
    auto. right. unfold not. intros. inversion H.
    intros. destruct l2. right. unfold not. intros. inversion H.
    specialize IHl1 with l2. destruct IHl1. left. subst. auto.
    right. unfold not. intros. inversion H;subst. auto.
Qed.

#[export] Hint Immediate Nat_decidable : core.

Lemma Typ_decidable: forall A B:typ, {A = B}+{~A = B}.
Proof.
  repeat decide equality.
Qed.

Lemma binds_typ_dec: forall x E (A:typ), {binds x A E} + {~ binds x A E}.
Proof.
  intros. apply binds_dec. apply Typ_decidable.
Qed.


(********************* rename & subst for lc **********************************)
#[export] Remove Hints lc_t_forall : core.
Ltac try_lc_typ_constructors :=
  match goal with (* pick fresh first if no atom exists *)
  | x : atom |- _ =>
    (* use the lemma from rule_inf.v instead of lc_t_forall *)
    applys lc_t_forall_exists x;
    instantiate_cofinites_with x
  | |- _ =>
    let x := fresh in pick fresh x;
                      applys lc_t_forall_exists x;
                      instantiate_cofinites_with x
  end.

#[export] Hint Extern 1 (lc_typ _ ) => try_lc_typ_constructors : core.

(* lc_exp *)
Lemma lc_exp_rename : forall e x y,
    x \notin (termfv_exp e) -> lc_exp (e ^ x) -> lc_exp (e ^ y).
Proof with (simpl in *; eauto).
  introv Fr Lc.
  assert (H: lc_exp ( [x ~> (e_var_f y)] (e ^ x) )).
  applys~ subst_exp_lc_exp.
  simpl in H. rewrite subst_exp_spec in H.
  rewrite close_exp_wrt_exp_open_exp_wrt_exp in H...
Qed.

Lemma abs_lc_open : forall e A v,
    lc_exp (e_abs A e) -> lc_exp v -> lc_exp (e ^^ v).
Proof.
  introv H H0.
  inverts H.
  apply~ lc_body_exp_wrt_exp.
Qed.

(* lc_typ *)
Lemma lc_typ_rename : forall A X Y,
    X \notin (typefv_typ A) -> lc_typ (A -^ X) -> lc_typ (A -^ Y).
Proof with (simpl in *; eauto).
  introv Fr Lc.
  assert (H: lc_typ [X ~~> (t_tvar_f Y)] (A -^ X)).
  applys~ typsubst_typ_lc_typ.
  simpl in H. rewrite typsubst_typ_spec in H.
  rewrite close_typ_wrt_typ_open_typ_wrt_typ in H...
Qed.

Lemma lc_subst: forall A X Y, lc_typ(A -^ X) -> lc_typ(A -^ Y).
Proof.
  intros. apply degree_typ_wrt_typ_of_lc_typ in H. apply degree_typ_wrt_typ_open_typ_wrt_typ_inv in H.
    assert(degree_typ_wrt_typ 0 (A -^ Y)). apply degree_typ_wrt_typ_open_typ_wrt_typ. auto. auto.
    apply lc_typ_of_degree in H0. auto.
Qed.

Lemma lc_subst_2: forall A X Y, lc_typ(A) -> lc_typ(typsubst_typ (t_tvar_f X) Y A).
Proof.
  intros. apply degree_typ_wrt_typ_of_lc_typ in H.
    assert(degree_typ_wrt_typ 0 (typsubst_typ (t_tvar_f X) Y A)).
  apply typsubst_typ_degree_typ_wrt_typ. auto. auto.
    apply lc_typ_of_degree in H0. auto.
Qed.

Lemma lc_typ_rename_2 : forall A X Y,
    lc_typ (A -^ X) -> lc_typ (A -^ Y).
Proof with (simpl in *; eauto).
  introv Lc.
  apply degree_typ_wrt_typ_of_lc_typ_mutual in Lc.
  apply degree_typ_wrt_typ_open_typ_wrt_typ_rec_inv_mutual in Lc.
  apply lc_typ_of_degree.
  apply degree_typ_wrt_typ_open_typ_wrt_typ. auto. auto.
Qed.


Lemma typsubst_typ_lc_typ : forall A X Y,
  lc_typ A ->
  lc_typ Y ->
  lc_typ ( [X ~~> Y] A ).
Proof with (simpl in *; eauto).
  introv Lc. gen X Y. induction Lc; intros...
  - destruct (X==X0)...
  - applys~ lc_t_forall.
    intros.
      apply lc_typ_of_degree.
      apply degree_typ_wrt_typ_open_typ_wrt_typ.
    assert(lc_typ [X ~~> Y] (B -^ X)). auto.
    assert([X ~~> Y] (B -^ X)  = [X ~~> Y] (B) ^-^  [X ~~> Y] (t_tvar_f X)).
    apply typsubst_typ_open_typ_wrt_typ_rec. auto.
    rewrite H3 in H2.
     apply degree_typ_wrt_typ_of_lc_typ in H2.
    apply degree_typ_wrt_typ_open_typ_wrt_typ_inv in H2. auto. auto.
Qed.

Lemma TWell_lc_typ: forall D A,
    TWell D A -> lc_typ A.
Proof.
  introv H. induction H; eauto with lngen.
Qed.

#[local] Hint Resolve TWell_lc_typ : core.

Ltac solve_lc_0 A :=
  match goal with
  | H: lc_typ _ |- _ => exact H
  | H: lc_typ (t_and _ _) |- _ => match type of H with context[ A ] => inverts H end
  | H: lc_typ (t_rcd _ _) |- _ => match type of H with context[ A ] => inverts H end
  | H: lc_typ (t_arrow _ _) |- _ => match type of H with context[ A ] => inverts H end
  | H: lc_typ (t_forall _ _) |- _ => match type of H with context[ A ] => inverts H end
  end.


#[export] Hint Extern 1 (lc_typ ?A ) => progress solve_lc_0 A : core.
#[export] Hint Extern 1 (lc_typ (?A -^ _) ) => progress instantiate_cofinites : core.
#[export] Hint Extern 1 (lc_typ (?A -^ _) ) => progress solve_lc_0 A; tassumption : core.


Ltac solve_twell_0 A :=
  match goal with
  | H: TWell _ _ |- _ => exact H
  | H: TWell _ (_ _ _) |- _ => match type of H with context[ A ] => inverts H end
  | H: TCWell ?D |-_ => match D with context[ A ] => inverts H end
  end.

#[export] Hint Extern 2 (TWell _ ?A ) => repeat solve_twell_0 A; easy : core.
#[export] Hint Extern 2 (TWell _ (?A -^ _) ) => progress instantiate_cofinites : core.
#[export] Hint Extern 1 (TWell _ (?A -^ _) ) => progress solve_twell_0 A : core.

#[export] Hint Extern 1 (lc_exp ?e ^ _) =>
match goal with
  H: lc_exp e ^ ?x |- _ => let Fr := fresh in
                           assert (Fr: x \notin (termfv_exp e)) by solve_notin;
                             applys lc_exp_rename Fr H
end : core.

#[export] Hint Extern 1 (lc_typ ?A ^ _) =>
match goal with
  H: lc_typ A ^ ?x |- _ => let Fr := fresh in
                           assert (Fr: x \notin (typefv_typ A)) by solve_notin;
                             applys lc_typ_rename Fr H
end : core.

#[export] Hint Immediate abs_lc_open : core.


Lemma lc_decidable_alternative: forall n A, size_typ A <= n ->lc_typ A\/~lc_typ A.
Proof.
  intros n. induction n. intros. destruct A;inversion H.
    intros. induction A;auto. right. unfold not. intros. inversion H0.
    - (* forall *)
      pick fresh X. simpl in H. assert(lc_typ  ( open_typ_wrt_typ A2 (t_tvar_f X))\/~lc_typ  ( open_typ_wrt_typ A2 (t_tvar_f X))).
      apply IHn. rewrite size_typ_open_typ_wrt_typ_var. lia.
      forwards: IHA1. lia. destruct H0. destruct H1. left. apply lc_t_forall.
      auto. intros. forwards: lc_t_forall_exists H1 H0.
      apply lc_body_t_forall_2 in H2. apply H2.
      right. unfold not. intros. inversion H2;subst. auto.
      right. unfold not. intros. apply lc_body_t_forall_2 in H2.
      unfold body_typ_wrt_typ in H2. specialize H2 with X. auto.
    - (* arrow *)
    simpl in H. forwards: IHA1. lia. forwards: IHA2. lia.
      destruct H0. destruct H1. auto. right. unfold not. intros.
      inversion H2;subst. auto. right. unfold not. intros.
      inversion H2;subst. auto.
    - (* and *)
    simpl in H. forwards: IHA1. lia. forwards: IHA2. lia.
      destruct H0. destruct H1. auto. right. unfold not. intros.
      inversion H2;subst. auto. right. unfold not. intros.
      inversion H2;subst. auto.
    - (* rcd *)
    simpl in H. forwards: IHA. lia.
      destruct H0. auto. right. unfold not. intros.
      inversion H1;subst. auto.
Qed.

Lemma lc_decidable: forall A, lc_typ A\/~lc_typ A.
Proof.
  intros. eapply lc_decidable_alternative. eauto.
Qed.

Lemma lc_topabs : lc_exp (e_abs t_top e_top).
Proof. eauto. Qed.

Lemma lc_toptabs : lc_exp (e_tabs e_top).
Proof. eauto. Qed.

Lemma lc_toprcd : forall l, lc_exp (e_rcd l e_top).
Proof. eauto. Qed.

#[export] Hint Resolve lc_topabs lc_toptabs lc_toprcd : core.
(******************************************************************************)
(* wellformedness *)

(* some hypothesis that cannot be true *)
#[export]
 Hint Extern 1 =>
match goal with
| H: TWell _ _ |- _ => solve [inverts H]
| H: _ = _ |- _ => solve [inverts H]
| H: nil = _ ++ _ |- _ => forwards (?&?): nil_eq_app H
end : FalseHd.

Ltac auto_twell_forall :=
  repeat match goal with
         | H: TWell _ (_ _ _) |- _ => inverts H
         end;
  let X := fresh "X" in
  pick fresh X and apply TW_all; instantiate_cofinites.

#[export] Hint Extern 1 (TWell ?D (t_forall _ _) ) => auto_twell_forall : core.

#[export] Hint Extern 1 (topLike ?D (t_forall _ _) ) => let X := fresh "X" in
  pick fresh X and apply TL_all; instantiate_cofinites: core.
(* TWell: type *)

Lemma TWell_weakening : forall T D E F,
    TWell (F ++ D) T ->
    TWell (F ++ E ++ D) T.
Proof.
  introv H. remember (F ++ D). gen F.
  induction* H; introv Heq; subst*.
  pick fresh y and apply TW_all. auto.
  rewrite* app_comm_cons.
Qed.

#[export] Hint Resolve TWell_weakening : core.

Lemma TWell_bind_weakening : forall x I J D C F,
    TWell (F ++ (x ~ I) ++ D) (C -^ x) ->
    TWell (F ++ (x ~ J) ++ D) (C -^ x).
Proof with eauto.
  intros. remember (F ++ (x ~ I) ++ D) as G. gen F. induction* H; intros; subst.
  - analyze_binds H.
    applys TW_var A...
    applys TW_var J...
    applys TW_var A.
    simpl_env.
    rewrite_env (nil ++ x ~ J ++ D).
    applys binds_weaken...
  - pick fresh y and apply TW_all...
    forwards*: H1 y ((y, A) :: F).
Qed.

Lemma TWell_bind_weakening_2 : forall x I J D C F,
    TWell (F ++ (x ~ I) ++ D) C ->
    TWell (F ++ (x ~ J) ++ D) C.
Proof with eauto.
  intros. remember (F ++ (x ~ I) ++ D) as G. gen F. induction* H; intros; subst.
  - analyze_binds H.
    applys TW_var A...
    applys TW_var J...
    applys TW_var A.
    simpl_env.
    rewrite_env (nil ++ x ~ J ++ D).
    applys binds_weaken...
  - pick fresh y and apply TW_all...
    forwards*: H1 y ((y, A) :: F).
Qed.

#[export] Hint Immediate TWell_bind_weakening TWell_bind_weakening_2 : core.

Lemma TWell_in : forall X A D,
    In (X, A) D -> TWell D (t_tvar_f X).
Proof.
  introv H.
  induction D; inverts* H.
  intuition eauto.
Qed.

#[export] Hint Immediate TWell_in : core.

Lemma TWell_subst : forall x A D F B T,
    TWell D T ->
    TWell (F ++ x ~ A ++ D) (B -^ x) ->
    TWell (map (typsubst_typ T x) F ++ D) [x ~~> T] (B -^ x).
Proof with simpl_env; eauto.
  intros. remember (F ++ x ~ A ++ D) as G. gen F. induction* H0; intros; subst; simpl.
  - case_if.
    applys (TWell_weakening T D (map (typsubst_typ T x) F) nil)...
    analyze_binds H0...
  - forwards: IHTWell...
  - forwards: IHTWell1...
  - forwards: IHTWell1...
  - pick fresh y and apply TW_all.
    forwards*: IHTWell.
    forwards*: H2 y ((y, A0) :: F).
    rewrites typsubst_typ_open_typ_wrt_typ_var...
Qed.

Lemma TWell_subst_2: forall X X0 A1 A2 D E,
    X \notin [[A2]] -> TWell (E ++ [(X, A1)] ++ D) (A2 -^ X)
    -> TWell (map (typsubst_typ (t_tvar_f X0) X)E ++ [(X0, A1)] ++ D) (A2 -^ X0).
Proof.
  intros.
    assert(TWell (E ++ [(X, A1)]++ [(X0, A1)]++ D) (A2 -^ X)).
      rewrite_env((E ++[(X, A1)])++ [(X0,A1)] ++ D).
    apply TWell_weakening.
      rewrite_env(E ++[(X, A1)] ++ D). auto.
    assert(TWell (map (typsubst_typ (t_tvar_f X0) X) E ++ (X0, A1) ::D) [X ~~> (t_tvar_f X0)] (A2 -^ X)).
  apply TWell_subst with A1.
    apply TW_var with A1. auto. auto.
    assert([X ~~> t_tvar_f X0] (A2 -^ X)  = [X ~~> t_tvar_f X0] (A2) ^-^  [X ~~> t_tvar_f X0] (t_tvar_f X)).
    apply typsubst_typ_open_typ_wrt_typ_rec. auto.
    rewrite H3 in H2.
    assert([X ~~> t_tvar_f X0] A2 = A2).
    apply typsubst_typ_fresh_eq. auto.
    rewrite H4 in H2.
    assert([X ~~> t_tvar_f X0] (t_tvar_f X) = (t_tvar_f X0)).
    simpl. unfold "==". destruct (EqDec_eq_of_X X X). auto. contradiction. rewrite H5 in H2. auto.
Qed.

Lemma TW_strengthen: forall A C D E X,
    X \notin [[A]] -> TWell (E ++ [(X , C)] ++ D) A -> TWell (E ++ D) A.
Proof with auto.
  intros. inductions H0...
    -(* var_f *)
    simpl in H. assert(X0 <> X)...
    assert(binds X0 A (E ++ D)). eauto.
    eauto.
  - (* rcd *)
    assert(TWell (E++D) A). apply IHTWell with C X. auto. auto. auto.
  - (* arrow *)
    simpl in H.
    assert(TWell (E++D) A). apply IHTWell1 with C X. auto. auto.
    assert(TWell (E++D) B). apply IHTWell2 with C X. auto. auto. auto.
  - (* and *)
    simpl in H.
    assert(TWell (E++D) A). apply IHTWell1 with C X. auto. auto.
    assert(TWell (E++D) B). apply IHTWell2 with C X. auto. auto. auto.
  - (* forall *)
    simpl in H.
    assert(TWell (E++D) A). apply IHTWell with C X. auto. auto.
    apply TW_all with (Metatheory.union L (Metatheory.singleton X)). auto.
    intros. rewrite_env (((X0, A) :: E) ++ D).
    apply H1 with C X. auto. assert(X <> X0). auto.
    assert(AtomSetImpl.Subset (typefv_typ (B -^ X0)) (typefv_typ (t_tvar_f X0) `union` typefv_typ B)).
      apply typefv_typ_open_typ_wrt_typ_rec_upper_mutual.
    assert(X `notin` (Metatheory.union [[t_tvar_f X0]] [[B]])). auto. auto.
    auto.
Qed.


Lemma TW_not_in: forall D A X, TWell D A -> X `notin` (dom D) -> X `notin` [[A]].
Proof.
  intros. induction H;auto.
    assert({X=X0}+{~X=X0}). auto.
    destruct H1. subst.
    forwards: binds_dom_contradiction H H0. contradiction.
    auto.
    simpl. pick fresh Y.
    assert(X `notin` [[B -^ Y]]). auto.
    assert(AtomSetImpl.Subset (typefv_typ B) (typefv_typ (B -^ Y))).
      apply typefv_typ_open_typ_wrt_typ_rec_lower_mutual.
    auto.
Qed.

Lemma TWell_all_open : forall D A B T,
    TWell D (t_forall A B) ->
    TWell D T ->
    TWell D (B ^-^ T).
Proof.
  intros. inverts H.
  pick fresh x.
  rewrite* (typsubst_typ_intro x).
  forwards*: H5 x.
  forwards*: TWell_subst H0.
  rewrite_env (nil ++ x ~ A ++ D) in H. applys H.
  forwards*: TWell_weakening. solve_notin.
  Unshelve. apply nil.
Qed.

(* it helps when the type in the goal is a subterm of the type in the hypothesis *)
(*
Ltac inverts_all_TWell :=
  repeat match goal with
         | H: TWell _ (t_rcd _ _) |- _ => inverts H
         | H: TWell _ (t_and _ _) |- _ => inverts H
         | H: TWell _ (t_arrow _ _) |- _ => inverts H
         | H: TWell _ (t_forall _ _) |- _ => inverts H
         end.

(* it is possible for the context in H and goal to mismatch *)
Ltac inverts_for_TWell A :=
  repeat match goal with
         | H: TWell _ ?B |- _ => match B with
                                 | A => exact H
                                 | context [ A ] => inverts H
                                 end
         end.
*)


Lemma TWell_decidable_alternative:
  forall n D A, size_typ A <= n ->  TWell D A\/~TWell D A.
Proof.
  intros n. induction n. intros. destruct A;inversion H.
    intros. destruct A;auto.
  - (* var_b *)
  right. unfold not. intros. inversion H0.
  - (* var_f *)
  assert((exists a, binds X a D)\/~(exists a, binds X a D)).
  apply binds_lookup_dec. destruct H0. destruct H0. left.
    eauto. right. unfold not. intros. inversion H1;subst. assert(exists a : typ, binds X a D).
    exists*. auto.
  - (* forall *)
  pick fresh X.
  assert(TWell D A1\/~TWell D A1). apply IHn. simpl in H. lia.
  assert(TWell  (cons ( X , A1 )  D )   ( open_typ_wrt_typ A2 (t_tvar_f X))\/~TWell  (cons ( X , A1 )  D )   ( open_typ_wrt_typ A2 (t_tvar_f X))).
    apply IHn. rewrite size_typ_open_typ_wrt_typ_var. simpl in H. lia.
  destruct H0. destruct H1. left. apply TW_all with {}. auto. intros.
    assert(TWell ((X, A1):: (X0, A1) :: D) (A2 -^ X)).
      rewrite_env([(X, A1)]++ [(X0,A1)] ++ D).
    apply TWell_weakening. auto.
    assert(TWell (map (typsubst_typ (t_tvar_f X0) X) nil ++ (X0, A1) ::D) [X ~~> (t_tvar_f X0)] (A2 -^ X)).
  apply TWell_subst with A1.
    apply TW_var with A1. auto. auto. simpl in H4.
    assert([X ~~> t_tvar_f X0] (A2 -^ X)  = [X ~~> t_tvar_f X0] (A2) ^-^  [X ~~> t_tvar_f X0] (t_tvar_f X)).
    apply typsubst_typ_open_typ_wrt_typ_rec. auto.
    rewrite H5 in H4.
    assert([X ~~> t_tvar_f X0] A2 = A2).
    apply typsubst_typ_fresh_eq. auto.
    rewrite H6 in H4.
    assert([X ~~> t_tvar_f X0] (t_tvar_f X) = (t_tvar_f X0)).
    simpl. unfold "==". destruct (EqDec_eq_of_X X X). auto. contradiction. rewrite H7 in H4. auto.
    right. unfold not. intros.
    assert(TWell ((X, A1) :: D) (t_forall A1 A2)).
    rewrite_env (nil++[(X, A1)] ++D). apply TWell_weakening. auto.
    assert(TWell ((X, A1) :: D) (A2 -^ X)). apply TWell_all_open with A1. auto. eauto.
    auto.
    right. unfold not. intros.
    inversion H2;subst. auto.
  - (* arrow *)
    simpl in H.
    assert(TWell D A1\/~TWell D A1). apply IHn. lia.
    assert(TWell D A2\/~TWell D A2). apply IHn. lia.
    destruct H0. destruct H1. auto.
    right. unfold not. intros. inversion H2;subst. auto.
    right. unfold not. intros. inversion H2;subst. auto.
  - (* and *)
    simpl in H.
    assert(TWell D A1\/~TWell D A1). apply IHn. lia.
    assert(TWell D A2\/~TWell D A2). apply IHn. lia.
    destruct H0. destruct H1. auto.
    right. unfold not. intros. inversion H2;subst. auto.
    right. unfold not. intros. inversion H2;subst. auto.
  - (* rcd *)
    simpl in H.
    assert(TWell D A\/~TWell D A). apply IHn. lia.
    destruct H0. auto.
    right. unfold not. intros. inversion H1;subst. auto.
Qed.


Lemma TWell_decidable:
  forall D A,  TWell D A\/~TWell D A.
Proof.
  intros. eapply TWell_decidable_alternative. eauto.
Qed.

(* CWell: term context *)

Lemma CWell_weakening: forall D E F G,
    CWell (F ++ D) G ->
    CWell (F ++ E ++ D) G.
Proof.
  introv H. remember (F ++ D). gen F.
  induction* H. constructor*. subst.
  apply~ TWell_weakening.
Qed.

Lemma CWell_app_1 : forall D G F,
    CWell D G -> CWell D F -> CWell D (F ++ G).
Proof.
  introv H1 H2.
  induction* H2.
  constructor*.
Qed.

Lemma CWell_app_2 : forall D G F,
    CWell D (F ++ G) -> (CWell D G /\ CWell D F).
Proof.
  introv H1.
  induction* F.
  inverts* H1. intuition eauto.
Qed.

Lemma CWell_reorder : forall D E F G,
    CWell D (E ++ F ++ G) -> CWell D (F ++ E ++ G).
Proof.
  introv. induction* E. introv H.
  inverts H. forwards: IHE H3.
  apply CWell_app_2 in H.
  destruct H.
  apply CWell_app_1.
  constructor*.
  auto.
Qed.

Lemma CWell_narrowing : forall V E F U X G,
    CWell (F ++ [(X, V)] ++ E) G ->
    TWell E U ->
    CWell (F ++ [(X, U)] ++ E) G.
Proof.
  intros. inductions H. auto.
  apply CW_cons. eauto.
  apply TWell_bind_weakening_2 with V. auto.
Qed.

Lemma CWell_TWell: forall D G x A,
    CWell D G -> binds x A G -> TWell D A.
Proof.
  introv HG H.
  induction HG.
  inverts H.
  destruct H.
  injection H.
  intros eq1 eq2; subst*.
  auto.
Qed.

(* TCWell: type context *)
Lemma TCWell_uniq: forall D,
    TCWell D -> uniq D.
Proof. intros. induction H. auto. auto. Qed.

#[export] Hint Immediate TCWell_uniq : core.

Lemma binds_replace : forall X1 A F X2 Q (P:typ) E,
    binds X1 A (F ++ X2 ~ Q ++ E) ->
    TCWell (F ++ X2 ~ Q ++ E) -> TWell E P ->
    binds X1 A (F ++ X2 ~ P ++ E) \/ binds X1 P (F ++ X2 ~ P ++ E) /\ A=Q /\ X1=X2.
Proof.
  intros.
  forwards:TCWell_uniq H0.
  assert({X1=X2}+{~X1=X2}). auto.
  destruct H3;subst.
  forwards: binds_mid_eq H H2. subst. right. auto.
  forwards: binds_remove_mid H n. eauto.
Qed.

Lemma TCWell_weakening: forall E D x T,
    x # (E ++ D) ->
    TWell D T ->
    TCWell (E ++ D) ->
    TCWell (E ++ [(x, T)] ++ D).
Proof.
  intros. induction* E; intros; simpl_env.
  - constructor*.
  - destruct a. constructor*.
    + inverts* H1. forwards ~: IHE.
    + inverts* H1. solve_uniq.
(*
      apply uniq_push.
      apply uniq_insert_mid. inversion H7;subst. auto.
      unfold "#" in H. simpl in H. rewrite dom_app in H.
      unfold not. intros. assert(x `in` add a (union (dom E) (dom D))). auto.
      auto.
      unfold "#" in H. simpl in H. rewrite dom_app in H.
      unfold not. intros. assert(x `in` add a (union (dom E) (dom D))). auto.
      auto.
      unfold "#". inversion H7;subst. rewrite dom_app. rewrite dom_app. simpl.
      unfold "#" in H8. rewrite dom_app in H8.
      unfold "#" in H. rewrite dom_app in H. simpl in H.
      assert(x = a\/~x = a). eauto. destruct H1;subst.
      assert(a `in` union (add a (dom E)) (dom D)). auto. contradiction.
      assert(a `notin` (add x empty)). eauto.
      assert(a `notin` union (dom E) (dom D)). auto.
      assert(a `notin` union (dom E) (union (add x empty) (dom D))). auto. auto. *)
Qed.

#[export] Hint Immediate TCWell_weakening : core.

Lemma TCWell_bind_weakening : forall x (I J:typ) D F,
    TCWell (F ++ (x ~ I) ++ D) ->
    TWell D J ->
    TCWell (F ++ (x ~ J) ++ D) .
Proof with eauto.
  intros. induction F. simpl. simpl in H. inversion H;subst.
      inversion H6;subst. auto.
      destruct a. inversion H;subst. simpl. apply TCW_cons. auto. rewrite_env(F++[(x,J)]++D). apply TWell_bind_weakening_2 with I. auto.
      rewrite_env(((a,t)::F)++[(x,J)]++D). apply uniq_bind_weakening with I. auto.
Qed.

Lemma TCWell_TWell: forall D x A,
    TCWell D -> binds x A D -> TWell D A.
Proof.
  introv Hw Hb. induction Hw; induction Hb. injects H1.
  - rewrite_env (nil ++ [(x, A)] ++ D).
    apply TWell_weakening. apply H.
  - apply IHHw in H1.
    rewrite_env (nil ++ [(X, A0)] ++ D).
    apply TWell_weakening. apply H1.
Qed.

(* it helps when A is bound in D *)
Ltac solve_TWell_by_TCWell :=
  match goal with
  | H: TCWell ?D |- TWell ?D ?A => applys TCWell_TWell H
  end.

#[export]
 Hint Extern 1 (TWell _) => solve_TWell_by_TCWell : core.

Lemma TCWell_cons_TWell: forall D x A,
    TCWell ((x, A) :: D) -> TWell D A.
Proof.
  introv H. inverts* H.
Qed.

Lemma TCWell_inv: forall D x A,
    TCWell ((x, A) :: D) -> TCWell D.
Proof.
  introv H. inverts* H.
Qed.

Lemma TCWell_inv_2: forall E D, TCWell (E ++ D) -> TCWell D.
Proof.
  introv H. induction E; auto. inversion H; subst. auto.
Qed.

#[local] Hint Immediate TCWell_inv TCWell_inv_2 : core.

Lemma TCW_well:forall C D E X, TCWell (E ++ [(X , C)] ++ D) -> TWell D C.
Proof.
  intros C D E. generalize dependent D. generalize dependent C. induction E;intros.
    simpl in H. apply TCWell_cons_TWell in H. auto.
  inversion H;subst. apply IHE in H2. auto.
Qed.

Ltac solve_tcwell_0 D :=
  match goal with
  | H: TCWell _ |- _ => exact H
  | H: TCWell _ |- _ => apply TCWell_inv in H
  | H: TCWell _ |- _ => apply TCWell_inv_2 in H
  end.

#[export] Hint Extern 1 (TCWell ?D) => progress solve_tcwell_0 D : core.

Lemma TCWell_decidable: forall D, TCWell D \/ ~TCWell D.
Proof.
  intros. induction D. auto.
    destruct a. destruct IHD.
    assert(TWell D t\/~TWell D t). apply TWell_decidable.
    destruct H0.
    assert(uniq  (cons ( a , t )  D )\/~uniq (cons ( a , t)  D )).
    apply uniq_decidable. destruct H1. auto.
    right. unfold not. intros. inversion H2;subst. auto.
    right. unfold not. intros. inversion H1;subst. auto.
    right. unfold not. intros. inversion H0;subst. auto.
Qed.


Lemma TCW_subst:forall C D E X Y,
    Y `notin` ((dom D) `union` (dom E)) ->
    TCWell (E ++ [(X , C)] ++ D) ->
    TCWell ((map (typsubst_typ (t_tvar_f Y) X)E) ++ [(Y , C)] ++ D).
Proof.
  intros. induction E. simpl. simpl in H0. inversion H0;subst. apply TCW_cons.
    auto. auto. apply uniq_push. inversion H6;subst. auto. auto.
    destruct a. simpl. apply TCW_cons. apply IHE. auto. simpl in H0. inversion H0;subst. auto.
    rewrite_env((map (typsubst_typ (t_tvar_f Y) X) E ++ ((Y, C) :: D))).
    assert(open_typ_wrt_typ (close_typ_wrt_typ X t) (t_tvar_f X) = t).
    apply open_typ_wrt_typ_close_typ_wrt_typ. rewrite <- H1.
    apply TWell_subst with C. eauto. inversion H0;subst.
    rewrite H1. rewrite_env((E ++ [(X, C)]) ++ [(Y, C)] ++ D).
    apply TWell_weakening.
    rewrite_env(E ++ [(X, C)] ++ D). auto.
   inversion H0;subst. clear H0 H4 H5.
   clear IHE.
    assert(uniq ((map (typsubst_typ (t_tvar_f Y) X) ((a,t)::E)) ++ (Y, C) :: D)).
    apply uniq_subst. auto. auto. auto.
Qed.

Lemma TCW_binds_2: forall A0 C D E X Y X1,
    TCWell (E ++ [(X,C)] ++ D) -> binds X1 A0 (E ++ [(X,C)] ++ D)
    -> X <> X1 -> binds X1 (typsubst_typ (t_tvar_f Y) X A0) ((map (typsubst_typ (t_tvar_f Y) X) E) ++ [(Y,C)] ++ D).
Proof with solve_false.
  intros.
  apply binds_app_1 in H0. destruct~ H0.
  apply binds_app_1 in H0. destruct~ H0.
  - unfold binds in H0. simpl in H0. destruct H0; subst~...
  - assert(TCWell ([(X,C)]++ D)). {
      induction~ E.
    }
    clear H. assert(X `notin` (typefv_typ_range D)). {
      inversion H2;subst. inversion H7;subst. clear H0 H1 H2 H4 H6 H7.
      induction D. simpl. auto. destruct a. simpl.
      inversion H5;subst.
      assert(X `notin` [[t]]). apply TW_not_in with D. auto. auto. auto.
    }
    assert(binds X1 ([X ~~> t_tvar_f Y] (A0)) (map (typsubst_typ (t_tvar_f Y) X) D)). {
      clear H H1 H2. induction D;simpl. auto.
      destruct a. apply binds_cons_iff in H0. destruct H0. destruct H;subst.
      auto. auto.
    }
    assert(map (typsubst_typ (t_tvar_f Y) X) D = D). apply no_effect_subst. auto.
    rewrite H4 in H3. auto.
Qed.

Lemma TCW_binds_TWell : forall D X A,
    TCWell D ->
    binds X A D ->
    TWell D A.
Proof.
  intros. inductions H; eauto.
  analyze_binds H2.
  rewrite_env (nil ++ X0 ~ A0 ++ D).
  applys~ TWell_weakening.
  forwards~: IHTCWell.
  rewrite_env (nil ++ X0 ~ A0 ++ D).
  applys~ TWell_weakening.
Qed.


Lemma TCW_binds_3: forall A0 C D E X J X1,
    TCWell (E ++ [(X,C)] ++ D) ->
    TWell D J ->
    binds X1 A0 (E ++ [(X,C)] ++ D) ->
    X <> X1 ->
    binds X1 (typsubst_typ J X A0) ((map (typsubst_typ J X) E)  ++ D).
Proof.
  intros.
  analyze_binds H1.
  assert (TCWell D) by eauto.
  forwards: TCW_binds_TWell H1 BindsTac0.
  forwards: TW_not_in X H3.
  assert (TCWell (X ~ C ++ D)) by eauto.
  forwards: TCWell_uniq H4.
  inverts~ H5.
  rewrites~ (@typsubst_typ_fresh_eq_mutual A0 J X).
Qed.


Lemma TW_subst:forall  C D E X Y A,
    X `notin`  [[A]] -> Y `notin` (Metatheory.union (dom D) (dom E))
    -> TCWell (E ++ [(X, C)] ++ D)
    -> TWell (E ++ [(X, C)] ++ D) (A -^ X)->TWell ((map (typsubst_typ (t_tvar_f Y) X) E)  ++ [(Y, C)] ++ D) (A -^ Y).
Proof.
  intros.
    pick fresh Z.
    assert(TCWell ([(Z,A -^X)]++ (E ++ [(X, C)] ++ D))).
    apply TCW_cons. auto. auto. apply uniq_push. apply TCWell_uniq in H1. auto.
    auto. assert(TCWell (map (typsubst_typ (t_tvar_f Y) X) ([(Z,(A -^X))]++E) ++ [(Y, C)] ++ D)).
    apply TCW_subst. simpl. assert(Y<>Z). auto. auto. auto.
    simpl in H4. inversion H4;subst.
    assert([X ~~> t_tvar_f Y] (A -^ X) = [X ~~> t_tvar_f Y] (A) ^-^  [X ~~> t_tvar_f Y] (t_tvar_f X)).
    apply typsubst_typ_open_typ_wrt_typ_rec. auto.
    rewrite H5 in H9.
    assert([X ~~> t_tvar_f Y] A = A).
    apply typsubst_typ_fresh_eq. auto.
    assert([X ~~> t_tvar_f Y] (t_tvar_f X) = t_tvar_f Y).
    simpl. unfold "==". destruct (EqDec_eq_of_X X X). auto. contradiction.
    rewrite H6 in H9. rewrite H7 in H9. auto.
Qed.


Lemma TWell_subst_1 : forall x A D F B T,
    TWell D T ->
    TWell (F ++ x ~ A ++ D) B ->
    TWell (map (typsubst_typ T x) F ++ D) [x ~~> T] B.
Proof with simpl_env; eauto.
  intros. remember (F ++ x ~ A ++ D) as G. gen F. induction* H0; intros; subst; simpl.
  - case_if.
    applys (TWell_weakening T D (map (typsubst_typ T x) F) nil)...
    analyze_binds H0...
  - forwards: IHTWell...
  - forwards: IHTWell1...
  - forwards: IHTWell1...
  - pick fresh y and apply TW_all.
    forwards*: IHTWell.
    forwards*: H2 y ((y, A0) :: F).
    rewrites typsubst_typ_open_typ_wrt_typ_var...
Qed.


Lemma CWell_subst : forall E Z S F G U,
    CWell (E ++ Z ~ S ++ F) G ->
    TWell F U ->
    CWell (map (typsubst_typ U Z) E ++ F) (map (typsubst_typ U Z) G).
Proof.
  intros. remember (E ++ Z ~ S ++ F) as E'. gen F.
  inductions H; intros; substs; eauto; simpl.
  forwards*: IHCWell.
  constructor*.
  applys* TWell_subst_1.
Qed.
