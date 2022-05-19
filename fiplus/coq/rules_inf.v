Require Import Coq.Arith.Wf_nat.
Require Import Coq.Logic.FunctionalExtensionality.
Require Import Coq.Program.Equality.

Require Export Metalib.Metatheory.
Require Export Metalib.LibLNgen.

Require Export syntax_ott.

(** NOTE: Auxiliary theorems are hidden in generated documentation.
    In general, there is a [_rec] version of every lemma involving
    [open] and [close]. *)


(* *********************************************************************** *)
(** * Induction principles for nonterminals *)

Scheme typ_ind' := Induction for typ Sort Prop.

Definition typ_mutind :=
  fun H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 =>
  typ_ind' H1 H2 H3 H4 H5 H6 H7 H8 H9 H10.

Scheme typ_rec' := Induction for typ Sort Set.

Definition typ_mutrec :=
  fun H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 =>
  typ_rec' H1 H2 H3 H4 H5 H6 H7 H8 H9 H10.

Scheme exp_ind' := Induction for exp Sort Prop.

Definition exp_mutind :=
  fun H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13 H14 =>
  exp_ind' H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13 H14.

Scheme exp_rec' := Induction for exp Sort Set.

Definition exp_mutrec :=
  fun H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13 H14 =>
  exp_rec' H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13 H14.


(* *********************************************************************** *)
(** * Close *)

Fixpoint close_typ_wrt_typ_rec (n1 : nat) (X1 : typevar) (A1 : typ) {struct A1} : typ :=
  match A1 with
    | t_tvar_f X2 => if (X1 == X2) then (t_tvar_b n1) else (t_tvar_f X2)
    | t_tvar_b n2 => if (lt_ge_dec n2 n1) then (t_tvar_b n2) else (t_tvar_b (S n2))
    | t_int => t_int
    | t_top => t_top
    | t_bot => t_bot
    | t_forall A2 B1 => t_forall (close_typ_wrt_typ_rec n1 X1 A2) (close_typ_wrt_typ_rec (S n1) X1 B1)
    | t_arrow A2 B1 => t_arrow (close_typ_wrt_typ_rec n1 X1 A2) (close_typ_wrt_typ_rec n1 X1 B1)
    | t_and A2 B1 => t_and (close_typ_wrt_typ_rec n1 X1 A2) (close_typ_wrt_typ_rec n1 X1 B1)
    | t_rcd l1 A2 => t_rcd l1 (close_typ_wrt_typ_rec n1 X1 A2)
  end.

Definition close_typ_wrt_typ X1 A1 := close_typ_wrt_typ_rec 0 X1 A1.

Fixpoint close_exp_wrt_typ_rec (n1 : nat) (X1 : typevar) (e1 : exp) {struct e1} : exp :=
  match e1 with
    | e_var_f x1 => e_var_f x1
    | e_var_b n2 => e_var_b n2
    | e_top => e_top
    | e_lit i1 => e_lit i1
    | e_abs A1 e2 => e_abs (close_typ_wrt_typ_rec n1 X1 A1) (close_exp_wrt_typ_rec n1 X1 e2)
    | e_fixpoint A1 e2 => e_fixpoint (close_typ_wrt_typ_rec n1 X1 A1) (close_exp_wrt_typ_rec n1 X1 e2)
    | e_app e2 e3 => e_app (close_exp_wrt_typ_rec n1 X1 e2) (close_exp_wrt_typ_rec n1 X1 e3)
    | e_merge e2 e3 => e_merge (close_exp_wrt_typ_rec n1 X1 e2) (close_exp_wrt_typ_rec n1 X1 e3)
    | e_anno e2 A1 => e_anno (close_exp_wrt_typ_rec n1 X1 e2) (close_typ_wrt_typ_rec n1 X1 A1)
    | e_rcd l1 e2 => e_rcd l1 (close_exp_wrt_typ_rec n1 X1 e2)
    | e_proj e2 l1 => e_proj (close_exp_wrt_typ_rec n1 X1 e2) l1
    | e_tabs e2 => e_tabs (close_exp_wrt_typ_rec (S n1) X1 e2)
    | e_tapp e2 A1 => e_tapp (close_exp_wrt_typ_rec n1 X1 e2) (close_typ_wrt_typ_rec n1 X1 A1)
  end.

Fixpoint close_exp_wrt_exp_rec (n1 : nat) (x1 : termvar) (e1 : exp) {struct e1} : exp :=
  match e1 with
    | e_var_f x2 => if (x1 == x2) then (e_var_b n1) else (e_var_f x2)
    | e_var_b n2 => if (lt_ge_dec n2 n1) then (e_var_b n2) else (e_var_b (S n2))
    | e_top => e_top
    | e_lit i1 => e_lit i1
    | e_abs A1 e2 => e_abs A1 (close_exp_wrt_exp_rec (S n1) x1 e2)
    | e_fixpoint A1 e2 => e_fixpoint A1 (close_exp_wrt_exp_rec (S n1) x1 e2)
    | e_app e2 e3 => e_app (close_exp_wrt_exp_rec n1 x1 e2) (close_exp_wrt_exp_rec n1 x1 e3)
    | e_merge e2 e3 => e_merge (close_exp_wrt_exp_rec n1 x1 e2) (close_exp_wrt_exp_rec n1 x1 e3)
    | e_anno e2 A1 => e_anno (close_exp_wrt_exp_rec n1 x1 e2) A1
    | e_rcd l1 e2 => e_rcd l1 (close_exp_wrt_exp_rec n1 x1 e2)
    | e_proj e2 l1 => e_proj (close_exp_wrt_exp_rec n1 x1 e2) l1
    | e_tabs e2 => e_tabs (close_exp_wrt_exp_rec n1 x1 e2)
    | e_tapp e2 A1 => e_tapp (close_exp_wrt_exp_rec n1 x1 e2) A1
  end.

Definition close_exp_wrt_typ X1 e1 := close_exp_wrt_typ_rec 0 X1 e1.

Definition close_exp_wrt_exp x1 e1 := close_exp_wrt_exp_rec 0 x1 e1.


(* *********************************************************************** *)
(** * Size *)

Fixpoint size_typ (A1 : typ) {struct A1} : nat :=
  match A1 with
    | t_tvar_f X1 => 1
    | t_tvar_b n1 => 1
    | t_int => 1
    | t_top => 1
    | t_bot => 1
    | t_forall A2 B1 => 1 + (size_typ A2) + (size_typ B1)
    | t_arrow A2 B1 => 1 + (size_typ A2) + (size_typ B1)
    | t_and A2 B1 => 1 + (size_typ A2) + (size_typ B1)
    | t_rcd l1 A2 => 1 + (size_typ A2)
  end.

Fixpoint size_exp (e1 : exp) {struct e1} : nat :=
  match e1 with
    | e_var_f x1 => 1
    | e_var_b n1 => 1
    | e_top => 1
    | e_lit i1 => 1
    | e_abs A1 e2 => 1 + (size_typ A1) + (size_exp e2)
    | e_fixpoint A1 e2 => 1 + (size_typ A1) + (size_exp e2)
    | e_app e2 e3 => 1 + (size_exp e2) + (size_exp e3)
    | e_merge e2 e3 => 1 + (size_exp e2) + (size_exp e3)
    | e_anno e2 A1 => 1 + (size_exp e2) + (size_typ A1)
    | e_rcd l1 e2 => 1 + (size_exp e2)
    | e_proj e2 l1 => 1 + (size_exp e2)
    | e_tabs e2 => 1 + (size_exp e2)
    | e_tapp e2 A1 => 1 + (size_exp e2) + (size_typ A1)
  end.


(* *********************************************************************** *)
(** * Degree *)

(** These define only an upper bound, not a strict upper bound. *)

Inductive degree_typ_wrt_typ : nat -> typ -> Prop :=
  | degree_wrt_typ_t_tvar_f : forall n1 X1,
    degree_typ_wrt_typ n1 (t_tvar_f X1)
  | degree_wrt_typ_t_tvar_b : forall n1 n2,
    lt n2 n1 ->
    degree_typ_wrt_typ n1 (t_tvar_b n2)
  | degree_wrt_typ_t_int : forall n1,
    degree_typ_wrt_typ n1 (t_int)
  | degree_wrt_typ_t_top : forall n1,
    degree_typ_wrt_typ n1 (t_top)
  | degree_wrt_typ_t_bot : forall n1,
    degree_typ_wrt_typ n1 (t_bot)
  | degree_wrt_typ_t_forall : forall n1 A1 B1,
    degree_typ_wrt_typ n1 A1 ->
    degree_typ_wrt_typ (S n1) B1 ->
    degree_typ_wrt_typ n1 (t_forall A1 B1)
  | degree_wrt_typ_t_arrow : forall n1 A1 B1,
    degree_typ_wrt_typ n1 A1 ->
    degree_typ_wrt_typ n1 B1 ->
    degree_typ_wrt_typ n1 (t_arrow A1 B1)
  | degree_wrt_typ_t_and : forall n1 A1 B1,
    degree_typ_wrt_typ n1 A1 ->
    degree_typ_wrt_typ n1 B1 ->
    degree_typ_wrt_typ n1 (t_and A1 B1)
  | degree_wrt_typ_t_rcd : forall n1 l1 A1,
    degree_typ_wrt_typ n1 A1 ->
    degree_typ_wrt_typ n1 (t_rcd l1 A1).

Scheme degree_typ_wrt_typ_ind' := Induction for degree_typ_wrt_typ Sort Prop.

Definition degree_typ_wrt_typ_mutind :=
  fun H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 =>
  degree_typ_wrt_typ_ind' H1 H2 H3 H4 H5 H6 H7 H8 H9 H10.

Hint Constructors degree_typ_wrt_typ : core lngen.

Inductive degree_exp_wrt_typ : nat -> exp -> Prop :=
  | degree_wrt_typ_e_var_f : forall n1 x1,
    degree_exp_wrt_typ n1 (e_var_f x1)
  | degree_wrt_typ_e_var_b : forall n1 n2,
    degree_exp_wrt_typ n1 (e_var_b n2)
  | degree_wrt_typ_e_top : forall n1,
    degree_exp_wrt_typ n1 (e_top)
  | degree_wrt_typ_e_lit : forall n1 i1,
    degree_exp_wrt_typ n1 (e_lit i1)
  | degree_wrt_typ_e_abs : forall n1 A1 e1,
    degree_typ_wrt_typ n1 A1 ->
    degree_exp_wrt_typ n1 e1 ->
    degree_exp_wrt_typ n1 (e_abs A1 e1)
  | degree_wrt_typ_e_fixpoint : forall n1 A1 e1,
    degree_typ_wrt_typ n1 A1 ->
    degree_exp_wrt_typ n1 e1 ->
    degree_exp_wrt_typ n1 (e_fixpoint A1 e1)
  | degree_wrt_typ_e_app : forall n1 e1 e2,
    degree_exp_wrt_typ n1 e1 ->
    degree_exp_wrt_typ n1 e2 ->
    degree_exp_wrt_typ n1 (e_app e1 e2)
  | degree_wrt_typ_e_merge : forall n1 e1 e2,
    degree_exp_wrt_typ n1 e1 ->
    degree_exp_wrt_typ n1 e2 ->
    degree_exp_wrt_typ n1 (e_merge e1 e2)
  | degree_wrt_typ_e_anno : forall n1 e1 A1,
    degree_exp_wrt_typ n1 e1 ->
    degree_typ_wrt_typ n1 A1 ->
    degree_exp_wrt_typ n1 (e_anno e1 A1)
  | degree_wrt_typ_e_rcd : forall n1 l1 e1,
    degree_exp_wrt_typ n1 e1 ->
    degree_exp_wrt_typ n1 (e_rcd l1 e1)
  | degree_wrt_typ_e_proj : forall n1 e1 l1,
    degree_exp_wrt_typ n1 e1 ->
    degree_exp_wrt_typ n1 (e_proj e1 l1)
  | degree_wrt_typ_e_tabs : forall n1 e1,
    degree_exp_wrt_typ (S n1) e1 ->
    degree_exp_wrt_typ n1 (e_tabs e1)
  | degree_wrt_typ_e_tapp : forall n1 e1 A1,
    degree_exp_wrt_typ n1 e1 ->
    degree_typ_wrt_typ n1 A1 ->
    degree_exp_wrt_typ n1 (e_tapp e1 A1).

Inductive degree_exp_wrt_exp : nat -> exp -> Prop :=
  | degree_wrt_exp_e_var_f : forall n1 x1,
    degree_exp_wrt_exp n1 (e_var_f x1)
  | degree_wrt_exp_e_var_b : forall n1 n2,
    lt n2 n1 ->
    degree_exp_wrt_exp n1 (e_var_b n2)
  | degree_wrt_exp_e_top : forall n1,
    degree_exp_wrt_exp n1 (e_top)
  | degree_wrt_exp_e_lit : forall n1 i1,
    degree_exp_wrt_exp n1 (e_lit i1)
  | degree_wrt_exp_e_abs : forall n1 A1 e1,
    degree_exp_wrt_exp (S n1) e1 ->
    degree_exp_wrt_exp n1 (e_abs A1 e1)
  | degree_wrt_exp_e_fixpoint : forall n1 A1 e1,
    degree_exp_wrt_exp (S n1) e1 ->
    degree_exp_wrt_exp n1 (e_fixpoint A1 e1)
  | degree_wrt_exp_e_app : forall n1 e1 e2,
    degree_exp_wrt_exp n1 e1 ->
    degree_exp_wrt_exp n1 e2 ->
    degree_exp_wrt_exp n1 (e_app e1 e2)
  | degree_wrt_exp_e_merge : forall n1 e1 e2,
    degree_exp_wrt_exp n1 e1 ->
    degree_exp_wrt_exp n1 e2 ->
    degree_exp_wrt_exp n1 (e_merge e1 e2)
  | degree_wrt_exp_e_anno : forall n1 e1 A1,
    degree_exp_wrt_exp n1 e1 ->
    degree_exp_wrt_exp n1 (e_anno e1 A1)
  | degree_wrt_exp_e_rcd : forall n1 l1 e1,
    degree_exp_wrt_exp n1 e1 ->
    degree_exp_wrt_exp n1 (e_rcd l1 e1)
  | degree_wrt_exp_e_proj : forall n1 e1 l1,
    degree_exp_wrt_exp n1 e1 ->
    degree_exp_wrt_exp n1 (e_proj e1 l1)
  | degree_wrt_exp_e_tabs : forall n1 e1,
    degree_exp_wrt_exp n1 e1 ->
    degree_exp_wrt_exp n1 (e_tabs e1)
  | degree_wrt_exp_e_tapp : forall n1 e1 A1,
    degree_exp_wrt_exp n1 e1 ->
    degree_exp_wrt_exp n1 (e_tapp e1 A1).

Scheme degree_exp_wrt_typ_ind' := Induction for degree_exp_wrt_typ Sort Prop.

Definition degree_exp_wrt_typ_mutind :=
  fun H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13 H14 =>
  degree_exp_wrt_typ_ind' H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13 H14.

Scheme degree_exp_wrt_exp_ind' := Induction for degree_exp_wrt_exp Sort Prop.

Definition degree_exp_wrt_exp_mutind :=
  fun H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13 H14 =>
  degree_exp_wrt_exp_ind' H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13 H14.

Hint Constructors degree_exp_wrt_typ : core lngen.

Hint Constructors degree_exp_wrt_exp : core lngen.


(* *********************************************************************** *)
(** * Local closure (version in [Set], induction principles) *)

Inductive lc_set_typ : typ -> Set :=
  | lc_set_t_tvar_f : forall X1,
    lc_set_typ (t_tvar_f X1)
  | lc_set_t_int :
    lc_set_typ (t_int)
  | lc_set_t_top :
    lc_set_typ (t_top)
  | lc_set_t_bot :
    lc_set_typ (t_bot)
  | lc_set_t_forall : forall A1 B1,
    lc_set_typ A1 ->
    (forall X1 : typevar, lc_set_typ (open_typ_wrt_typ B1 (t_tvar_f X1))) ->
    lc_set_typ (t_forall A1 B1)
  | lc_set_t_arrow : forall A1 B1,
    lc_set_typ A1 ->
    lc_set_typ B1 ->
    lc_set_typ (t_arrow A1 B1)
  | lc_set_t_and : forall A1 B1,
    lc_set_typ A1 ->
    lc_set_typ B1 ->
    lc_set_typ (t_and A1 B1)
  | lc_set_t_rcd : forall l1 A1,
    lc_set_typ A1 ->
    lc_set_typ (t_rcd l1 A1).

Scheme lc_typ_ind' := Induction for lc_typ Sort Prop.

Definition lc_typ_mutind :=
  fun H1 H2 H3 H4 H5 H6 H7 H8 H9 =>
  lc_typ_ind' H1 H2 H3 H4 H5 H6 H7 H8 H9.

Scheme lc_set_typ_ind' := Induction for lc_set_typ Sort Prop.

Definition lc_set_typ_mutind :=
  fun H1 H2 H3 H4 H5 H6 H7 H8 H9 =>
  lc_set_typ_ind' H1 H2 H3 H4 H5 H6 H7 H8 H9.

Scheme lc_set_typ_rec' := Induction for lc_set_typ Sort Set.

Definition lc_set_typ_mutrec :=
  fun H1 H2 H3 H4 H5 H6 H7 H8 H9 =>
  lc_set_typ_rec' H1 H2 H3 H4 H5 H6 H7 H8 H9.

Hint Constructors lc_typ : core lngen.

Hint Constructors lc_set_typ : core lngen.

Inductive lc_set_exp : exp -> Set :=
  | lc_set_e_var_f : forall x1,
    lc_set_exp (e_var_f x1)
  | lc_set_e_top :
    lc_set_exp (e_top)
  | lc_set_e_lit : forall i1,
    lc_set_exp (e_lit i1)
  | lc_set_e_abs : forall A1 e1,
    lc_set_typ A1 ->
    (forall x1 : termvar, lc_set_exp (open_exp_wrt_exp e1 (e_var_f x1))) ->
    lc_set_exp (e_abs A1 e1)
  | lc_set_e_fixpoint : forall A1 e1,
    lc_set_typ A1 ->
    (forall x1 : termvar, lc_set_exp (open_exp_wrt_exp e1 (e_var_f x1))) ->
    lc_set_exp (e_fixpoint A1 e1)
  | lc_set_e_app : forall e1 e2,
    lc_set_exp e1 ->
    lc_set_exp e2 ->
    lc_set_exp (e_app e1 e2)
  | lc_set_e_merge : forall e1 e2,
    lc_set_exp e1 ->
    lc_set_exp e2 ->
    lc_set_exp (e_merge e1 e2)
  | lc_set_e_anno : forall e1 A1,
    lc_set_exp e1 ->
    lc_set_typ A1 ->
    lc_set_exp (e_anno e1 A1)
  | lc_set_e_rcd : forall l1 e1,
    lc_set_exp e1 ->
    lc_set_exp (e_rcd l1 e1)
  | lc_set_e_proj : forall e1 l1,
    lc_set_exp e1 ->
    lc_set_exp (e_proj e1 l1)
  | lc_set_e_tabs : forall e1,
    (forall X1 : typevar, lc_set_exp (open_exp_wrt_typ e1 (t_tvar_f X1))) ->
    lc_set_exp (e_tabs e1)
  | lc_set_e_tapp : forall e1 A1,
    lc_set_exp e1 ->
    lc_set_typ A1 ->
    lc_set_exp (e_tapp e1 A1).

Scheme lc_exp_ind' := Induction for lc_exp Sort Prop.

Definition lc_exp_mutind :=
  fun H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13 =>
  lc_exp_ind' H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13.

Scheme lc_set_exp_ind' := Induction for lc_set_exp Sort Prop.

Definition lc_set_exp_mutind :=
  fun H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13 =>
  lc_set_exp_ind' H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13.

Scheme lc_set_exp_rec' := Induction for lc_set_exp Sort Set.

Definition lc_set_exp_mutrec :=
  fun H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13 =>
  lc_set_exp_rec' H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13.

Hint Constructors lc_exp : core lngen.

Hint Constructors lc_set_exp : core lngen.


(* *********************************************************************** *)
(** * Body *)

Definition body_typ_wrt_typ A1 := forall X1, lc_typ (open_typ_wrt_typ A1 (t_tvar_f X1)).

Hint Unfold body_typ_wrt_typ : core.

Definition body_exp_wrt_typ e1 := forall X1, lc_exp (open_exp_wrt_typ e1 (t_tvar_f X1)).

Definition body_exp_wrt_exp e1 := forall x1, lc_exp (open_exp_wrt_exp e1 (e_var_f x1)).

Hint Unfold body_exp_wrt_typ : core.

Hint Unfold body_exp_wrt_exp : core.


(* *********************************************************************** *)
(** * Tactic support *)

(** Additional hint declarations. *)

Hint Resolve @plus_le_compat : lngen.

(** Redefine some tactics. *)

Ltac default_case_split ::=
  first
    [ progress destruct_notin
    | progress destruct_sum
    | progress safe_f_equal
    ].


(* *********************************************************************** *)
(** * Theorems about [size] *)

Ltac default_auto ::= auto with arith lngen; tauto.
Ltac default_autorewrite ::= fail.

(* begin hide *)

Lemma size_typ_min_mutual :
(forall A1, 1 <= size_typ A1).
Proof.
apply_mutual_ind typ_mutind;
default_simp.
Qed.

(* end hide *)

Lemma size_typ_min :
forall A1, 1 <= size_typ A1.
Proof.
pose proof size_typ_min_mutual as H; intuition eauto.
Qed.

Hint Resolve size_typ_min : lngen.

(* begin hide *)

Lemma size_exp_min_mutual :
(forall e1, 1 <= size_exp e1).
Proof.
apply_mutual_ind exp_mutind;
default_simp.
Qed.

(* end hide *)

Lemma size_exp_min :
forall e1, 1 <= size_exp e1.
Proof.
pose proof size_exp_min_mutual as H; intuition eauto.
Qed.

Hint Resolve size_exp_min : lngen.

(* begin hide *)

Lemma size_typ_close_typ_wrt_typ_rec_mutual :
(forall A1 X1 n1,
  size_typ (close_typ_wrt_typ_rec n1 X1 A1) = size_typ A1).
Proof.
apply_mutual_ind typ_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma size_typ_close_typ_wrt_typ_rec :
forall A1 X1 n1,
  size_typ (close_typ_wrt_typ_rec n1 X1 A1) = size_typ A1.
Proof.
pose proof size_typ_close_typ_wrt_typ_rec_mutual as H; intuition eauto.
Qed.

Hint Resolve size_typ_close_typ_wrt_typ_rec : lngen.
Hint Rewrite size_typ_close_typ_wrt_typ_rec using solve [auto] : lngen.

(* end hide *)

(* begin hide *)

Lemma size_exp_close_exp_wrt_typ_rec_mutual :
(forall e1 X1 n1,
  size_exp (close_exp_wrt_typ_rec n1 X1 e1) = size_exp e1).
Proof.
apply_mutual_ind exp_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma size_exp_close_exp_wrt_typ_rec :
forall e1 X1 n1,
  size_exp (close_exp_wrt_typ_rec n1 X1 e1) = size_exp e1.
Proof.
pose proof size_exp_close_exp_wrt_typ_rec_mutual as H; intuition eauto.
Qed.

Hint Resolve size_exp_close_exp_wrt_typ_rec : lngen.
Hint Rewrite size_exp_close_exp_wrt_typ_rec using solve [auto] : lngen.

(* end hide *)

(* begin hide *)

Lemma size_exp_close_exp_wrt_exp_rec_mutual :
(forall e1 x1 n1,
  size_exp (close_exp_wrt_exp_rec n1 x1 e1) = size_exp e1).
Proof.
apply_mutual_ind exp_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma size_exp_close_exp_wrt_exp_rec :
forall e1 x1 n1,
  size_exp (close_exp_wrt_exp_rec n1 x1 e1) = size_exp e1.
Proof.
pose proof size_exp_close_exp_wrt_exp_rec_mutual as H; intuition eauto.
Qed.

Hint Resolve size_exp_close_exp_wrt_exp_rec : lngen.
Hint Rewrite size_exp_close_exp_wrt_exp_rec using solve [auto] : lngen.

(* end hide *)

Lemma size_typ_close_typ_wrt_typ :
forall A1 X1,
  size_typ (close_typ_wrt_typ X1 A1) = size_typ A1.
Proof.
unfold close_typ_wrt_typ; default_simp.
Qed.

Hint Resolve size_typ_close_typ_wrt_typ : lngen.
Hint Rewrite size_typ_close_typ_wrt_typ using solve [auto] : lngen.

Lemma size_exp_close_exp_wrt_typ :
forall e1 X1,
  size_exp (close_exp_wrt_typ X1 e1) = size_exp e1.
Proof.
unfold close_exp_wrt_typ; default_simp.
Qed.

Hint Resolve size_exp_close_exp_wrt_typ : lngen.
Hint Rewrite size_exp_close_exp_wrt_typ using solve [auto] : lngen.

Lemma size_exp_close_exp_wrt_exp :
forall e1 x1,
  size_exp (close_exp_wrt_exp x1 e1) = size_exp e1.
Proof.
unfold close_exp_wrt_exp; default_simp.
Qed.

Hint Resolve size_exp_close_exp_wrt_exp : lngen.
Hint Rewrite size_exp_close_exp_wrt_exp using solve [auto] : lngen.

(* begin hide *)

Lemma size_typ_open_typ_wrt_typ_rec_mutual :
(forall A1 A2 n1,
  size_typ A1 <= size_typ (open_typ_wrt_typ_rec n1 A2 A1)).
Proof.
apply_mutual_ind typ_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma size_typ_open_typ_wrt_typ_rec :
forall A1 A2 n1,
  size_typ A1 <= size_typ (open_typ_wrt_typ_rec n1 A2 A1).
Proof.
pose proof size_typ_open_typ_wrt_typ_rec_mutual as H; intuition eauto.
Qed.

Hint Resolve size_typ_open_typ_wrt_typ_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma size_exp_open_exp_wrt_typ_rec_mutual :
(forall e1 A1 n1,
  size_exp e1 <= size_exp (open_exp_wrt_typ_rec n1 A1 e1)).
Proof.
apply_mutual_ind exp_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma size_exp_open_exp_wrt_typ_rec :
forall e1 A1 n1,
  size_exp e1 <= size_exp (open_exp_wrt_typ_rec n1 A1 e1).
Proof.
pose proof size_exp_open_exp_wrt_typ_rec_mutual as H; intuition eauto.
Qed.

Hint Resolve size_exp_open_exp_wrt_typ_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma size_exp_open_exp_wrt_exp_rec_mutual :
(forall e1 e2 n1,
  size_exp e1 <= size_exp (open_exp_wrt_exp_rec n1 e2 e1)).
Proof.
apply_mutual_ind exp_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma size_exp_open_exp_wrt_exp_rec :
forall e1 e2 n1,
  size_exp e1 <= size_exp (open_exp_wrt_exp_rec n1 e2 e1).
Proof.
pose proof size_exp_open_exp_wrt_exp_rec_mutual as H; intuition eauto.
Qed.

Hint Resolve size_exp_open_exp_wrt_exp_rec : lngen.

(* end hide *)

Lemma size_typ_open_typ_wrt_typ :
forall A1 A2,
  size_typ A1 <= size_typ (open_typ_wrt_typ A1 A2).
Proof.
unfold open_typ_wrt_typ; default_simp.
Qed.

Hint Resolve size_typ_open_typ_wrt_typ : lngen.

Lemma size_exp_open_exp_wrt_typ :
forall e1 A1,
  size_exp e1 <= size_exp (open_exp_wrt_typ e1 A1).
Proof.
unfold open_exp_wrt_typ; default_simp.
Qed.

Hint Resolve size_exp_open_exp_wrt_typ : lngen.

Lemma size_exp_open_exp_wrt_exp :
forall e1 e2,
  size_exp e1 <= size_exp (open_exp_wrt_exp e1 e2).
Proof.
unfold open_exp_wrt_exp; default_simp.
Qed.

Hint Resolve size_exp_open_exp_wrt_exp : lngen.

(* begin hide *)

Lemma size_typ_open_typ_wrt_typ_rec_var_mutual :
(forall A1 X1 n1,
  size_typ (open_typ_wrt_typ_rec n1 (t_tvar_f X1) A1) = size_typ A1).
Proof.
apply_mutual_ind typ_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma size_typ_open_typ_wrt_typ_rec_var :
forall A1 X1 n1,
  size_typ (open_typ_wrt_typ_rec n1 (t_tvar_f X1) A1) = size_typ A1.
Proof.
pose proof size_typ_open_typ_wrt_typ_rec_var_mutual as H; intuition eauto.
Qed.

Hint Resolve size_typ_open_typ_wrt_typ_rec_var : lngen.
Hint Rewrite size_typ_open_typ_wrt_typ_rec_var using solve [auto] : lngen.

(* end hide *)

(* begin hide *)

Lemma size_exp_open_exp_wrt_typ_rec_var_mutual :
(forall e1 X1 n1,
  size_exp (open_exp_wrt_typ_rec n1 (t_tvar_f X1) e1) = size_exp e1).
Proof.
apply_mutual_ind exp_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma size_exp_open_exp_wrt_typ_rec_var :
forall e1 X1 n1,
  size_exp (open_exp_wrt_typ_rec n1 (t_tvar_f X1) e1) = size_exp e1.
Proof.
pose proof size_exp_open_exp_wrt_typ_rec_var_mutual as H; intuition eauto.
Qed.

Hint Resolve size_exp_open_exp_wrt_typ_rec_var : lngen.
Hint Rewrite size_exp_open_exp_wrt_typ_rec_var using solve [auto] : lngen.

(* end hide *)

(* begin hide *)

Lemma size_exp_open_exp_wrt_exp_rec_var_mutual :
(forall e1 x1 n1,
  size_exp (open_exp_wrt_exp_rec n1 (e_var_f x1) e1) = size_exp e1).
Proof.
apply_mutual_ind exp_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma size_exp_open_exp_wrt_exp_rec_var :
forall e1 x1 n1,
  size_exp (open_exp_wrt_exp_rec n1 (e_var_f x1) e1) = size_exp e1.
Proof.
pose proof size_exp_open_exp_wrt_exp_rec_var_mutual as H; intuition eauto.
Qed.

Hint Resolve size_exp_open_exp_wrt_exp_rec_var : lngen.
Hint Rewrite size_exp_open_exp_wrt_exp_rec_var using solve [auto] : lngen.

(* end hide *)

Lemma size_typ_open_typ_wrt_typ_var :
forall A1 X1,
  size_typ (open_typ_wrt_typ A1 (t_tvar_f X1)) = size_typ A1.
Proof.
unfold open_typ_wrt_typ; default_simp.
Qed.

Hint Resolve size_typ_open_typ_wrt_typ_var : lngen.
Hint Rewrite size_typ_open_typ_wrt_typ_var using solve [auto] : lngen.

Lemma size_exp_open_exp_wrt_typ_var :
forall e1 X1,
  size_exp (open_exp_wrt_typ e1 (t_tvar_f X1)) = size_exp e1.
Proof.
unfold open_exp_wrt_typ; default_simp.
Qed.

Hint Resolve size_exp_open_exp_wrt_typ_var : lngen.
Hint Rewrite size_exp_open_exp_wrt_typ_var using solve [auto] : lngen.

Lemma size_exp_open_exp_wrt_exp_var :
forall e1 x1,
  size_exp (open_exp_wrt_exp e1 (e_var_f x1)) = size_exp e1.
Proof.
unfold open_exp_wrt_exp; default_simp.
Qed.

Hint Resolve size_exp_open_exp_wrt_exp_var : lngen.
Hint Rewrite size_exp_open_exp_wrt_exp_var using solve [auto] : lngen.


(* *********************************************************************** *)
(** * Theorems about [degree] *)

Ltac default_auto ::= auto with lngen; tauto.
Ltac default_autorewrite ::= fail.

(* begin hide *)

Lemma degree_typ_wrt_typ_S_mutual :
(forall n1 A1,
  degree_typ_wrt_typ n1 A1 ->
  degree_typ_wrt_typ (S n1) A1).
Proof.
apply_mutual_ind degree_typ_wrt_typ_mutind;
default_simp.
Qed.

(* end hide *)

Lemma degree_typ_wrt_typ_S :
forall n1 A1,
  degree_typ_wrt_typ n1 A1 ->
  degree_typ_wrt_typ (S n1) A1.
Proof.
pose proof degree_typ_wrt_typ_S_mutual as H; intuition eauto.
Qed.

Hint Resolve degree_typ_wrt_typ_S : lngen.

(* begin hide *)

Lemma degree_exp_wrt_typ_S_mutual :
(forall n1 e1,
  degree_exp_wrt_typ n1 e1 ->
  degree_exp_wrt_typ (S n1) e1).
Proof.
apply_mutual_ind degree_exp_wrt_typ_mutind;
default_simp.
Qed.

(* end hide *)

Lemma degree_exp_wrt_typ_S :
forall n1 e1,
  degree_exp_wrt_typ n1 e1 ->
  degree_exp_wrt_typ (S n1) e1.
Proof.
pose proof degree_exp_wrt_typ_S_mutual as H; intuition eauto.
Qed.

Hint Resolve degree_exp_wrt_typ_S : lngen.

(* begin hide *)

Lemma degree_exp_wrt_exp_S_mutual :
(forall n1 e1,
  degree_exp_wrt_exp n1 e1 ->
  degree_exp_wrt_exp (S n1) e1).
Proof.
apply_mutual_ind degree_exp_wrt_exp_mutind;
default_simp.
Qed.

(* end hide *)

Lemma degree_exp_wrt_exp_S :
forall n1 e1,
  degree_exp_wrt_exp n1 e1 ->
  degree_exp_wrt_exp (S n1) e1.
Proof.
pose proof degree_exp_wrt_exp_S_mutual as H; intuition eauto.
Qed.

Hint Resolve degree_exp_wrt_exp_S : lngen.

Lemma degree_typ_wrt_typ_O :
forall n1 A1,
  degree_typ_wrt_typ O A1 ->
  degree_typ_wrt_typ n1 A1.
Proof.
induction n1; default_simp.
Qed.

Hint Resolve degree_typ_wrt_typ_O : lngen.

Lemma degree_exp_wrt_typ_O :
forall n1 e1,
  degree_exp_wrt_typ O e1 ->
  degree_exp_wrt_typ n1 e1.
Proof.
induction n1; default_simp.
Qed.

Hint Resolve degree_exp_wrt_typ_O : lngen.

Lemma degree_exp_wrt_exp_O :
forall n1 e1,
  degree_exp_wrt_exp O e1 ->
  degree_exp_wrt_exp n1 e1.
Proof.
induction n1; default_simp.
Qed.

Hint Resolve degree_exp_wrt_exp_O : lngen.

(* begin hide *)

Lemma degree_typ_wrt_typ_close_typ_wrt_typ_rec_mutual :
(forall A1 X1 n1,
  degree_typ_wrt_typ n1 A1 ->
  degree_typ_wrt_typ (S n1) (close_typ_wrt_typ_rec n1 X1 A1)).
Proof.
apply_mutual_ind typ_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma degree_typ_wrt_typ_close_typ_wrt_typ_rec :
forall A1 X1 n1,
  degree_typ_wrt_typ n1 A1 ->
  degree_typ_wrt_typ (S n1) (close_typ_wrt_typ_rec n1 X1 A1).
Proof.
pose proof degree_typ_wrt_typ_close_typ_wrt_typ_rec_mutual as H; intuition eauto.
Qed.

Hint Resolve degree_typ_wrt_typ_close_typ_wrt_typ_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma degree_exp_wrt_typ_close_exp_wrt_typ_rec_mutual :
(forall e1 X1 n1,
  degree_exp_wrt_typ n1 e1 ->
  degree_exp_wrt_typ (S n1) (close_exp_wrt_typ_rec n1 X1 e1)).
Proof.
apply_mutual_ind exp_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma degree_exp_wrt_typ_close_exp_wrt_typ_rec :
forall e1 X1 n1,
  degree_exp_wrt_typ n1 e1 ->
  degree_exp_wrt_typ (S n1) (close_exp_wrt_typ_rec n1 X1 e1).
Proof.
pose proof degree_exp_wrt_typ_close_exp_wrt_typ_rec_mutual as H; intuition eauto.
Qed.

Hint Resolve degree_exp_wrt_typ_close_exp_wrt_typ_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma degree_exp_wrt_typ_close_exp_wrt_exp_rec_mutual :
(forall e1 x1 n1 n2,
  degree_exp_wrt_typ n2 e1 ->
  degree_exp_wrt_typ n2 (close_exp_wrt_exp_rec n1 x1 e1)).
Proof.
apply_mutual_ind exp_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma degree_exp_wrt_typ_close_exp_wrt_exp_rec :
forall e1 x1 n1 n2,
  degree_exp_wrt_typ n2 e1 ->
  degree_exp_wrt_typ n2 (close_exp_wrt_exp_rec n1 x1 e1).
Proof.
pose proof degree_exp_wrt_typ_close_exp_wrt_exp_rec_mutual as H; intuition eauto.
Qed.

Hint Resolve degree_exp_wrt_typ_close_exp_wrt_exp_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma degree_exp_wrt_exp_close_exp_wrt_typ_rec_mutual :
(forall e1 X1 n1 n2,
  degree_exp_wrt_exp n2 e1 ->
  degree_exp_wrt_exp n2 (close_exp_wrt_typ_rec n1 X1 e1)).
Proof.
apply_mutual_ind exp_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma degree_exp_wrt_exp_close_exp_wrt_typ_rec :
forall e1 X1 n1 n2,
  degree_exp_wrt_exp n2 e1 ->
  degree_exp_wrt_exp n2 (close_exp_wrt_typ_rec n1 X1 e1).
Proof.
pose proof degree_exp_wrt_exp_close_exp_wrt_typ_rec_mutual as H; intuition eauto.
Qed.

Hint Resolve degree_exp_wrt_exp_close_exp_wrt_typ_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma degree_exp_wrt_exp_close_exp_wrt_exp_rec_mutual :
(forall e1 x1 n1,
  degree_exp_wrt_exp n1 e1 ->
  degree_exp_wrt_exp (S n1) (close_exp_wrt_exp_rec n1 x1 e1)).
Proof.
apply_mutual_ind exp_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma degree_exp_wrt_exp_close_exp_wrt_exp_rec :
forall e1 x1 n1,
  degree_exp_wrt_exp n1 e1 ->
  degree_exp_wrt_exp (S n1) (close_exp_wrt_exp_rec n1 x1 e1).
Proof.
pose proof degree_exp_wrt_exp_close_exp_wrt_exp_rec_mutual as H; intuition eauto.
Qed.

Hint Resolve degree_exp_wrt_exp_close_exp_wrt_exp_rec : lngen.

(* end hide *)

Lemma degree_typ_wrt_typ_close_typ_wrt_typ :
forall A1 X1,
  degree_typ_wrt_typ 0 A1 ->
  degree_typ_wrt_typ 1 (close_typ_wrt_typ X1 A1).
Proof.
unfold close_typ_wrt_typ; default_simp.
Qed.

Hint Resolve degree_typ_wrt_typ_close_typ_wrt_typ : lngen.

Lemma degree_exp_wrt_typ_close_exp_wrt_typ :
forall e1 X1,
  degree_exp_wrt_typ 0 e1 ->
  degree_exp_wrt_typ 1 (close_exp_wrt_typ X1 e1).
Proof.
unfold close_exp_wrt_typ; default_simp.
Qed.

Hint Resolve degree_exp_wrt_typ_close_exp_wrt_typ : lngen.

Lemma degree_exp_wrt_typ_close_exp_wrt_exp :
forall e1 x1 n1,
  degree_exp_wrt_typ n1 e1 ->
  degree_exp_wrt_typ n1 (close_exp_wrt_exp x1 e1).
Proof.
unfold close_exp_wrt_exp; default_simp.
Qed.

Hint Resolve degree_exp_wrt_typ_close_exp_wrt_exp : lngen.

Lemma degree_exp_wrt_exp_close_exp_wrt_typ :
forall e1 X1 n1,
  degree_exp_wrt_exp n1 e1 ->
  degree_exp_wrt_exp n1 (close_exp_wrt_typ X1 e1).
Proof.
unfold close_exp_wrt_typ; default_simp.
Qed.

Hint Resolve degree_exp_wrt_exp_close_exp_wrt_typ : lngen.

Lemma degree_exp_wrt_exp_close_exp_wrt_exp :
forall e1 x1,
  degree_exp_wrt_exp 0 e1 ->
  degree_exp_wrt_exp 1 (close_exp_wrt_exp x1 e1).
Proof.
unfold close_exp_wrt_exp; default_simp.
Qed.

Hint Resolve degree_exp_wrt_exp_close_exp_wrt_exp : lngen.

(* begin hide *)

Lemma degree_typ_wrt_typ_close_typ_wrt_typ_rec_inv_mutual :
(forall A1 X1 n1,
  degree_typ_wrt_typ (S n1) (close_typ_wrt_typ_rec n1 X1 A1) ->
  degree_typ_wrt_typ n1 A1).
Proof.
apply_mutual_ind typ_mutind;
default_simp; eauto with lngen.
Qed.

(* end hide *)

(* begin hide *)

Lemma degree_typ_wrt_typ_close_typ_wrt_typ_rec_inv :
forall A1 X1 n1,
  degree_typ_wrt_typ (S n1) (close_typ_wrt_typ_rec n1 X1 A1) ->
  degree_typ_wrt_typ n1 A1.
Proof.
pose proof degree_typ_wrt_typ_close_typ_wrt_typ_rec_inv_mutual as H; intuition eauto.
Qed.

Hint Immediate degree_typ_wrt_typ_close_typ_wrt_typ_rec_inv : lngen.

(* end hide *)

(* begin hide *)

Lemma degree_exp_wrt_typ_close_exp_wrt_typ_rec_inv_mutual :
(forall e1 X1 n1,
  degree_exp_wrt_typ (S n1) (close_exp_wrt_typ_rec n1 X1 e1) ->
  degree_exp_wrt_typ n1 e1).
Proof.
apply_mutual_ind exp_mutind;
default_simp; eauto with lngen.
Qed.

(* end hide *)

(* begin hide *)

Lemma degree_exp_wrt_typ_close_exp_wrt_typ_rec_inv :
forall e1 X1 n1,
  degree_exp_wrt_typ (S n1) (close_exp_wrt_typ_rec n1 X1 e1) ->
  degree_exp_wrt_typ n1 e1.
Proof.
pose proof degree_exp_wrt_typ_close_exp_wrt_typ_rec_inv_mutual as H; intuition eauto.
Qed.

Hint Immediate degree_exp_wrt_typ_close_exp_wrt_typ_rec_inv : lngen.

(* end hide *)

(* begin hide *)

Lemma degree_exp_wrt_typ_close_exp_wrt_exp_rec_inv_mutual :
(forall e1 x1 n1 n2,
  degree_exp_wrt_typ n2 (close_exp_wrt_exp_rec n1 x1 e1) ->
  degree_exp_wrt_typ n2 e1).
Proof.
apply_mutual_ind exp_mutind;
default_simp; eauto with lngen.
Qed.

(* end hide *)

(* begin hide *)

Lemma degree_exp_wrt_typ_close_exp_wrt_exp_rec_inv :
forall e1 x1 n1 n2,
  degree_exp_wrt_typ n2 (close_exp_wrt_exp_rec n1 x1 e1) ->
  degree_exp_wrt_typ n2 e1.
Proof.
pose proof degree_exp_wrt_typ_close_exp_wrt_exp_rec_inv_mutual as H; intuition eauto.
Qed.

Hint Immediate degree_exp_wrt_typ_close_exp_wrt_exp_rec_inv : lngen.

(* end hide *)

(* begin hide *)

Lemma degree_exp_wrt_exp_close_exp_wrt_typ_rec_inv_mutual :
(forall e1 X1 n1 n2,
  degree_exp_wrt_exp n2 (close_exp_wrt_typ_rec n1 X1 e1) ->
  degree_exp_wrt_exp n2 e1).
Proof.
apply_mutual_ind exp_mutind;
default_simp; eauto with lngen.
Qed.

(* end hide *)

(* begin hide *)

Lemma degree_exp_wrt_exp_close_exp_wrt_typ_rec_inv :
forall e1 X1 n1 n2,
  degree_exp_wrt_exp n2 (close_exp_wrt_typ_rec n1 X1 e1) ->
  degree_exp_wrt_exp n2 e1.
Proof.
pose proof degree_exp_wrt_exp_close_exp_wrt_typ_rec_inv_mutual as H; intuition eauto.
Qed.

Hint Immediate degree_exp_wrt_exp_close_exp_wrt_typ_rec_inv : lngen.

(* end hide *)

(* begin hide *)

Lemma degree_exp_wrt_exp_close_exp_wrt_exp_rec_inv_mutual :
(forall e1 x1 n1,
  degree_exp_wrt_exp (S n1) (close_exp_wrt_exp_rec n1 x1 e1) ->
  degree_exp_wrt_exp n1 e1).
Proof.
apply_mutual_ind exp_mutind;
default_simp; eauto with lngen.
Qed.

(* end hide *)

(* begin hide *)

Lemma degree_exp_wrt_exp_close_exp_wrt_exp_rec_inv :
forall e1 x1 n1,
  degree_exp_wrt_exp (S n1) (close_exp_wrt_exp_rec n1 x1 e1) ->
  degree_exp_wrt_exp n1 e1.
Proof.
pose proof degree_exp_wrt_exp_close_exp_wrt_exp_rec_inv_mutual as H; intuition eauto.
Qed.

Hint Immediate degree_exp_wrt_exp_close_exp_wrt_exp_rec_inv : lngen.

(* end hide *)

Lemma degree_typ_wrt_typ_close_typ_wrt_typ_inv :
forall A1 X1,
  degree_typ_wrt_typ 1 (close_typ_wrt_typ X1 A1) ->
  degree_typ_wrt_typ 0 A1.
Proof.
unfold close_typ_wrt_typ; eauto with lngen.
Qed.

Hint Immediate degree_typ_wrt_typ_close_typ_wrt_typ_inv : lngen.

Lemma degree_exp_wrt_typ_close_exp_wrt_typ_inv :
forall e1 X1,
  degree_exp_wrt_typ 1 (close_exp_wrt_typ X1 e1) ->
  degree_exp_wrt_typ 0 e1.
Proof.
unfold close_exp_wrt_typ; eauto with lngen.
Qed.

Hint Immediate degree_exp_wrt_typ_close_exp_wrt_typ_inv : lngen.

Lemma degree_exp_wrt_typ_close_exp_wrt_exp_inv :
forall e1 x1 n1,
  degree_exp_wrt_typ n1 (close_exp_wrt_exp x1 e1) ->
  degree_exp_wrt_typ n1 e1.
Proof.
unfold close_exp_wrt_exp; eauto with lngen.
Qed.

Hint Immediate degree_exp_wrt_typ_close_exp_wrt_exp_inv : lngen.

Lemma degree_exp_wrt_exp_close_exp_wrt_typ_inv :
forall e1 X1 n1,
  degree_exp_wrt_exp n1 (close_exp_wrt_typ X1 e1) ->
  degree_exp_wrt_exp n1 e1.
Proof.
unfold close_exp_wrt_typ; eauto with lngen.
Qed.

Hint Immediate degree_exp_wrt_exp_close_exp_wrt_typ_inv : lngen.

Lemma degree_exp_wrt_exp_close_exp_wrt_exp_inv :
forall e1 x1,
  degree_exp_wrt_exp 1 (close_exp_wrt_exp x1 e1) ->
  degree_exp_wrt_exp 0 e1.
Proof.
unfold close_exp_wrt_exp; eauto with lngen.
Qed.

Hint Immediate degree_exp_wrt_exp_close_exp_wrt_exp_inv : lngen.

(* begin hide *)

Lemma degree_typ_wrt_typ_open_typ_wrt_typ_rec_mutual :
(forall A1 A2 n1,
  degree_typ_wrt_typ (S n1) A1 ->
  degree_typ_wrt_typ n1 A2 ->
  degree_typ_wrt_typ n1 (open_typ_wrt_typ_rec n1 A2 A1)).
Proof.
apply_mutual_ind typ_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma degree_typ_wrt_typ_open_typ_wrt_typ_rec :
forall A1 A2 n1,
  degree_typ_wrt_typ (S n1) A1 ->
  degree_typ_wrt_typ n1 A2 ->
  degree_typ_wrt_typ n1 (open_typ_wrt_typ_rec n1 A2 A1).
Proof.
pose proof degree_typ_wrt_typ_open_typ_wrt_typ_rec_mutual as H; intuition eauto.
Qed.

Hint Resolve degree_typ_wrt_typ_open_typ_wrt_typ_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma degree_exp_wrt_typ_open_exp_wrt_typ_rec_mutual :
(forall e1 A1 n1,
  degree_exp_wrt_typ (S n1) e1 ->
  degree_typ_wrt_typ n1 A1 ->
  degree_exp_wrt_typ n1 (open_exp_wrt_typ_rec n1 A1 e1)).
Proof.
apply_mutual_ind exp_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma degree_exp_wrt_typ_open_exp_wrt_typ_rec :
forall e1 A1 n1,
  degree_exp_wrt_typ (S n1) e1 ->
  degree_typ_wrt_typ n1 A1 ->
  degree_exp_wrt_typ n1 (open_exp_wrt_typ_rec n1 A1 e1).
Proof.
pose proof degree_exp_wrt_typ_open_exp_wrt_typ_rec_mutual as H; intuition eauto.
Qed.

Hint Resolve degree_exp_wrt_typ_open_exp_wrt_typ_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma degree_exp_wrt_typ_open_exp_wrt_exp_rec_mutual :
(forall e1 e2 n1 n2,
  degree_exp_wrt_typ n1 e1 ->
  degree_exp_wrt_typ n1 e2 ->
  degree_exp_wrt_typ n1 (open_exp_wrt_exp_rec n2 e2 e1)).
Proof.
apply_mutual_ind exp_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma degree_exp_wrt_typ_open_exp_wrt_exp_rec :
forall e1 e2 n1 n2,
  degree_exp_wrt_typ n1 e1 ->
  degree_exp_wrt_typ n1 e2 ->
  degree_exp_wrt_typ n1 (open_exp_wrt_exp_rec n2 e2 e1).
Proof.
pose proof degree_exp_wrt_typ_open_exp_wrt_exp_rec_mutual as H; intuition eauto.
Qed.

Hint Resolve degree_exp_wrt_typ_open_exp_wrt_exp_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma degree_exp_wrt_exp_open_exp_wrt_typ_rec_mutual :
(forall e1 A1 n1 n2,
  degree_exp_wrt_exp n1 e1 ->
  degree_exp_wrt_exp n1 (open_exp_wrt_typ_rec n2 A1 e1)).
Proof.
apply_mutual_ind exp_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma degree_exp_wrt_exp_open_exp_wrt_typ_rec :
forall e1 A1 n1 n2,
  degree_exp_wrt_exp n1 e1 ->
  degree_exp_wrt_exp n1 (open_exp_wrt_typ_rec n2 A1 e1).
Proof.
pose proof degree_exp_wrt_exp_open_exp_wrt_typ_rec_mutual as H; intuition eauto.
Qed.

Hint Resolve degree_exp_wrt_exp_open_exp_wrt_typ_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma degree_exp_wrt_exp_open_exp_wrt_exp_rec_mutual :
(forall e1 e2 n1,
  degree_exp_wrt_exp (S n1) e1 ->
  degree_exp_wrt_exp n1 e2 ->
  degree_exp_wrt_exp n1 (open_exp_wrt_exp_rec n1 e2 e1)).
Proof.
apply_mutual_ind exp_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma degree_exp_wrt_exp_open_exp_wrt_exp_rec :
forall e1 e2 n1,
  degree_exp_wrt_exp (S n1) e1 ->
  degree_exp_wrt_exp n1 e2 ->
  degree_exp_wrt_exp n1 (open_exp_wrt_exp_rec n1 e2 e1).
Proof.
pose proof degree_exp_wrt_exp_open_exp_wrt_exp_rec_mutual as H; intuition eauto.
Qed.

Hint Resolve degree_exp_wrt_exp_open_exp_wrt_exp_rec : lngen.

(* end hide *)

Lemma degree_typ_wrt_typ_open_typ_wrt_typ :
forall A1 A2,
  degree_typ_wrt_typ 1 A1 ->
  degree_typ_wrt_typ 0 A2 ->
  degree_typ_wrt_typ 0 (open_typ_wrt_typ A1 A2).
Proof.
unfold open_typ_wrt_typ; default_simp.
Qed.

Hint Resolve degree_typ_wrt_typ_open_typ_wrt_typ : lngen.

Lemma degree_exp_wrt_typ_open_exp_wrt_typ :
forall e1 A1,
  degree_exp_wrt_typ 1 e1 ->
  degree_typ_wrt_typ 0 A1 ->
  degree_exp_wrt_typ 0 (open_exp_wrt_typ e1 A1).
Proof.
unfold open_exp_wrt_typ; default_simp.
Qed.

Hint Resolve degree_exp_wrt_typ_open_exp_wrt_typ : lngen.

Lemma degree_exp_wrt_typ_open_exp_wrt_exp :
forall e1 e2 n1,
  degree_exp_wrt_typ n1 e1 ->
  degree_exp_wrt_typ n1 e2 ->
  degree_exp_wrt_typ n1 (open_exp_wrt_exp e1 e2).
Proof.
unfold open_exp_wrt_exp; default_simp.
Qed.

Hint Resolve degree_exp_wrt_typ_open_exp_wrt_exp : lngen.

Lemma degree_exp_wrt_exp_open_exp_wrt_typ :
forall e1 A1 n1,
  degree_exp_wrt_exp n1 e1 ->
  degree_exp_wrt_exp n1 (open_exp_wrt_typ e1 A1).
Proof.
unfold open_exp_wrt_typ; default_simp.
Qed.

Hint Resolve degree_exp_wrt_exp_open_exp_wrt_typ : lngen.

Lemma degree_exp_wrt_exp_open_exp_wrt_exp :
forall e1 e2,
  degree_exp_wrt_exp 1 e1 ->
  degree_exp_wrt_exp 0 e2 ->
  degree_exp_wrt_exp 0 (open_exp_wrt_exp e1 e2).
Proof.
unfold open_exp_wrt_exp; default_simp.
Qed.

Hint Resolve degree_exp_wrt_exp_open_exp_wrt_exp : lngen.

(* begin hide *)

Lemma degree_typ_wrt_typ_open_typ_wrt_typ_rec_inv_mutual :
(forall A1 A2 n1,
  degree_typ_wrt_typ n1 (open_typ_wrt_typ_rec n1 A2 A1) ->
  degree_typ_wrt_typ (S n1) A1).
Proof.
apply_mutual_ind typ_mutind;
default_simp; eauto with lngen.
Qed.

(* end hide *)

(* begin hide *)

Lemma degree_typ_wrt_typ_open_typ_wrt_typ_rec_inv :
forall A1 A2 n1,
  degree_typ_wrt_typ n1 (open_typ_wrt_typ_rec n1 A2 A1) ->
  degree_typ_wrt_typ (S n1) A1.
Proof.
pose proof degree_typ_wrt_typ_open_typ_wrt_typ_rec_inv_mutual as H; intuition eauto.
Qed.

Hint Immediate degree_typ_wrt_typ_open_typ_wrt_typ_rec_inv : lngen.

(* end hide *)

(* begin hide *)

Lemma degree_exp_wrt_typ_open_exp_wrt_typ_rec_inv_mutual :
(forall e1 A1 n1,
  degree_exp_wrt_typ n1 (open_exp_wrt_typ_rec n1 A1 e1) ->
  degree_exp_wrt_typ (S n1) e1).
Proof.
apply_mutual_ind exp_mutind;
default_simp; eauto with lngen.
Qed.

(* end hide *)

(* begin hide *)

Lemma degree_exp_wrt_typ_open_exp_wrt_typ_rec_inv :
forall e1 A1 n1,
  degree_exp_wrt_typ n1 (open_exp_wrt_typ_rec n1 A1 e1) ->
  degree_exp_wrt_typ (S n1) e1.
Proof.
pose proof degree_exp_wrt_typ_open_exp_wrt_typ_rec_inv_mutual as H; intuition eauto.
Qed.

Hint Immediate degree_exp_wrt_typ_open_exp_wrt_typ_rec_inv : lngen.

(* end hide *)

(* begin hide *)

Lemma degree_exp_wrt_typ_open_exp_wrt_exp_rec_inv_mutual :
(forall e1 e2 n1 n2,
  degree_exp_wrt_typ n1 (open_exp_wrt_exp_rec n2 e2 e1) ->
  degree_exp_wrt_typ n1 e1).
Proof.
apply_mutual_ind exp_mutind;
default_simp; eauto with lngen.
Qed.

(* end hide *)

(* begin hide *)

Lemma degree_exp_wrt_typ_open_exp_wrt_exp_rec_inv :
forall e1 e2 n1 n2,
  degree_exp_wrt_typ n1 (open_exp_wrt_exp_rec n2 e2 e1) ->
  degree_exp_wrt_typ n1 e1.
Proof.
pose proof degree_exp_wrt_typ_open_exp_wrt_exp_rec_inv_mutual as H; intuition eauto.
Qed.

Hint Immediate degree_exp_wrt_typ_open_exp_wrt_exp_rec_inv : lngen.

(* end hide *)

(* begin hide *)

Lemma degree_exp_wrt_exp_open_exp_wrt_typ_rec_inv_mutual :
(forall e1 A1 n1 n2,
  degree_exp_wrt_exp n1 (open_exp_wrt_typ_rec n2 A1 e1) ->
  degree_exp_wrt_exp n1 e1).
Proof.
apply_mutual_ind exp_mutind;
default_simp; eauto with lngen.
Qed.

(* end hide *)

(* begin hide *)

Lemma degree_exp_wrt_exp_open_exp_wrt_typ_rec_inv :
forall e1 A1 n1 n2,
  degree_exp_wrt_exp n1 (open_exp_wrt_typ_rec n2 A1 e1) ->
  degree_exp_wrt_exp n1 e1.
Proof.
pose proof degree_exp_wrt_exp_open_exp_wrt_typ_rec_inv_mutual as H; intuition eauto.
Qed.

Hint Immediate degree_exp_wrt_exp_open_exp_wrt_typ_rec_inv : lngen.

(* end hide *)

(* begin hide *)

Lemma degree_exp_wrt_exp_open_exp_wrt_exp_rec_inv_mutual :
(forall e1 e2 n1,
  degree_exp_wrt_exp n1 (open_exp_wrt_exp_rec n1 e2 e1) ->
  degree_exp_wrt_exp (S n1) e1).
Proof.
apply_mutual_ind exp_mutind;
default_simp; eauto with lngen.
Qed.

(* end hide *)

(* begin hide *)

Lemma degree_exp_wrt_exp_open_exp_wrt_exp_rec_inv :
forall e1 e2 n1,
  degree_exp_wrt_exp n1 (open_exp_wrt_exp_rec n1 e2 e1) ->
  degree_exp_wrt_exp (S n1) e1.
Proof.
pose proof degree_exp_wrt_exp_open_exp_wrt_exp_rec_inv_mutual as H; intuition eauto.
Qed.

Hint Immediate degree_exp_wrt_exp_open_exp_wrt_exp_rec_inv : lngen.

(* end hide *)

Lemma degree_typ_wrt_typ_open_typ_wrt_typ_inv :
forall A1 A2,
  degree_typ_wrt_typ 0 (open_typ_wrt_typ A1 A2) ->
  degree_typ_wrt_typ 1 A1.
Proof.
unfold open_typ_wrt_typ; eauto with lngen.
Qed.

Hint Immediate degree_typ_wrt_typ_open_typ_wrt_typ_inv : lngen.

Lemma degree_exp_wrt_typ_open_exp_wrt_typ_inv :
forall e1 A1,
  degree_exp_wrt_typ 0 (open_exp_wrt_typ e1 A1) ->
  degree_exp_wrt_typ 1 e1.
Proof.
unfold open_exp_wrt_typ; eauto with lngen.
Qed.

Hint Immediate degree_exp_wrt_typ_open_exp_wrt_typ_inv : lngen.

Lemma degree_exp_wrt_typ_open_exp_wrt_exp_inv :
forall e1 e2 n1,
  degree_exp_wrt_typ n1 (open_exp_wrt_exp e1 e2) ->
  degree_exp_wrt_typ n1 e1.
Proof.
unfold open_exp_wrt_exp; eauto with lngen.
Qed.

Hint Immediate degree_exp_wrt_typ_open_exp_wrt_exp_inv : lngen.

Lemma degree_exp_wrt_exp_open_exp_wrt_typ_inv :
forall e1 A1 n1,
  degree_exp_wrt_exp n1 (open_exp_wrt_typ e1 A1) ->
  degree_exp_wrt_exp n1 e1.
Proof.
unfold open_exp_wrt_typ; eauto with lngen.
Qed.

Hint Immediate degree_exp_wrt_exp_open_exp_wrt_typ_inv : lngen.

Lemma degree_exp_wrt_exp_open_exp_wrt_exp_inv :
forall e1 e2,
  degree_exp_wrt_exp 0 (open_exp_wrt_exp e1 e2) ->
  degree_exp_wrt_exp 1 e1.
Proof.
unfold open_exp_wrt_exp; eauto with lngen.
Qed.

Hint Immediate degree_exp_wrt_exp_open_exp_wrt_exp_inv : lngen.


(* *********************************************************************** *)
(** * Theorems about [open] and [close] *)

Ltac default_auto ::= auto with lngen brute_force; tauto.
Ltac default_autorewrite ::= fail.

(* begin hide *)

Lemma close_typ_wrt_typ_rec_inj_mutual :
(forall A1 A2 X1 n1,
  close_typ_wrt_typ_rec n1 X1 A1 = close_typ_wrt_typ_rec n1 X1 A2 ->
  A1 = A2).
Proof.
apply_mutual_ind typ_mutind;
intros; match goal with
          | |- _ = ?term => destruct term
        end;
default_simp; eauto with lngen.
Qed.

(* end hide *)

(* begin hide *)

Lemma close_typ_wrt_typ_rec_inj :
forall A1 A2 X1 n1,
  close_typ_wrt_typ_rec n1 X1 A1 = close_typ_wrt_typ_rec n1 X1 A2 ->
  A1 = A2.
Proof.
pose proof close_typ_wrt_typ_rec_inj_mutual as H; intuition eauto.
Qed.

Hint Immediate close_typ_wrt_typ_rec_inj : lngen.

(* end hide *)

(* begin hide *)

Lemma close_exp_wrt_typ_rec_inj_mutual :
(forall e1 e2 X1 n1,
  close_exp_wrt_typ_rec n1 X1 e1 = close_exp_wrt_typ_rec n1 X1 e2 ->
  e1 = e2).
Proof.
apply_mutual_ind exp_mutind;
intros; match goal with
          | |- _ = ?term => destruct term
        end;
default_simp; eauto with lngen.
Qed.

(* end hide *)

(* begin hide *)

Lemma close_exp_wrt_typ_rec_inj :
forall e1 e2 X1 n1,
  close_exp_wrt_typ_rec n1 X1 e1 = close_exp_wrt_typ_rec n1 X1 e2 ->
  e1 = e2.
Proof.
pose proof close_exp_wrt_typ_rec_inj_mutual as H; intuition eauto.
Qed.

Hint Immediate close_exp_wrt_typ_rec_inj : lngen.

(* end hide *)

(* begin hide *)

Lemma close_exp_wrt_exp_rec_inj_mutual :
(forall e1 e2 x1 n1,
  close_exp_wrt_exp_rec n1 x1 e1 = close_exp_wrt_exp_rec n1 x1 e2 ->
  e1 = e2).
Proof.
apply_mutual_ind exp_mutind;
intros; match goal with
          | |- _ = ?term => destruct term
        end;
default_simp; eauto with lngen.
Qed.

(* end hide *)

(* begin hide *)

Lemma close_exp_wrt_exp_rec_inj :
forall e1 e2 x1 n1,
  close_exp_wrt_exp_rec n1 x1 e1 = close_exp_wrt_exp_rec n1 x1 e2 ->
  e1 = e2.
Proof.
pose proof close_exp_wrt_exp_rec_inj_mutual as H; intuition eauto.
Qed.

Hint Immediate close_exp_wrt_exp_rec_inj : lngen.

(* end hide *)

Lemma close_typ_wrt_typ_inj :
forall A1 A2 X1,
  close_typ_wrt_typ X1 A1 = close_typ_wrt_typ X1 A2 ->
  A1 = A2.
Proof.
unfold close_typ_wrt_typ; eauto with lngen.
Qed.

Hint Immediate close_typ_wrt_typ_inj : lngen.

Lemma close_exp_wrt_typ_inj :
forall e1 e2 X1,
  close_exp_wrt_typ X1 e1 = close_exp_wrt_typ X1 e2 ->
  e1 = e2.
Proof.
unfold close_exp_wrt_typ; eauto with lngen.
Qed.

Hint Immediate close_exp_wrt_typ_inj : lngen.

Lemma close_exp_wrt_exp_inj :
forall e1 e2 x1,
  close_exp_wrt_exp x1 e1 = close_exp_wrt_exp x1 e2 ->
  e1 = e2.
Proof.
unfold close_exp_wrt_exp; eauto with lngen.
Qed.

Hint Immediate close_exp_wrt_exp_inj : lngen.

(* begin hide *)

Lemma close_typ_wrt_typ_rec_open_typ_wrt_typ_rec_mutual :
(forall A1 X1 n1,
  X1 `notin` typefv_typ A1 ->
  close_typ_wrt_typ_rec n1 X1 (open_typ_wrt_typ_rec n1 (t_tvar_f X1) A1) = A1).
Proof.
apply_mutual_ind typ_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma close_typ_wrt_typ_rec_open_typ_wrt_typ_rec :
forall A1 X1 n1,
  X1 `notin` typefv_typ A1 ->
  close_typ_wrt_typ_rec n1 X1 (open_typ_wrt_typ_rec n1 (t_tvar_f X1) A1) = A1.
Proof.
pose proof close_typ_wrt_typ_rec_open_typ_wrt_typ_rec_mutual as H; intuition eauto.
Qed.

Hint Resolve close_typ_wrt_typ_rec_open_typ_wrt_typ_rec : lngen.
Hint Rewrite close_typ_wrt_typ_rec_open_typ_wrt_typ_rec using solve [auto] : lngen.

(* end hide *)

(* begin hide *)

Lemma close_exp_wrt_typ_rec_open_exp_wrt_typ_rec_mutual :
(forall e1 X1 n1,
  X1 `notin` typefv_exp e1 ->
  close_exp_wrt_typ_rec n1 X1 (open_exp_wrt_typ_rec n1 (t_tvar_f X1) e1) = e1).
Proof.
apply_mutual_ind exp_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma close_exp_wrt_typ_rec_open_exp_wrt_typ_rec :
forall e1 X1 n1,
  X1 `notin` typefv_exp e1 ->
  close_exp_wrt_typ_rec n1 X1 (open_exp_wrt_typ_rec n1 (t_tvar_f X1) e1) = e1.
Proof.
pose proof close_exp_wrt_typ_rec_open_exp_wrt_typ_rec_mutual as H; intuition eauto.
Qed.

Hint Resolve close_exp_wrt_typ_rec_open_exp_wrt_typ_rec : lngen.
Hint Rewrite close_exp_wrt_typ_rec_open_exp_wrt_typ_rec using solve [auto] : lngen.

(* end hide *)

(* begin hide *)

Lemma close_exp_wrt_exp_rec_open_exp_wrt_exp_rec_mutual :
(forall e1 x1 n1,
  x1 `notin` termfv_exp e1 ->
  close_exp_wrt_exp_rec n1 x1 (open_exp_wrt_exp_rec n1 (e_var_f x1) e1) = e1).
Proof.
apply_mutual_ind exp_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma close_exp_wrt_exp_rec_open_exp_wrt_exp_rec :
forall e1 x1 n1,
  x1 `notin` termfv_exp e1 ->
  close_exp_wrt_exp_rec n1 x1 (open_exp_wrt_exp_rec n1 (e_var_f x1) e1) = e1.
Proof.
pose proof close_exp_wrt_exp_rec_open_exp_wrt_exp_rec_mutual as H; intuition eauto.
Qed.

Hint Resolve close_exp_wrt_exp_rec_open_exp_wrt_exp_rec : lngen.
Hint Rewrite close_exp_wrt_exp_rec_open_exp_wrt_exp_rec using solve [auto] : lngen.

(* end hide *)

Lemma close_typ_wrt_typ_open_typ_wrt_typ :
forall A1 X1,
  X1 `notin` typefv_typ A1 ->
  close_typ_wrt_typ X1 (open_typ_wrt_typ A1 (t_tvar_f X1)) = A1.
Proof.
unfold close_typ_wrt_typ; unfold open_typ_wrt_typ; default_simp.
Qed.

Hint Resolve close_typ_wrt_typ_open_typ_wrt_typ : lngen.
Hint Rewrite close_typ_wrt_typ_open_typ_wrt_typ using solve [auto] : lngen.

Lemma close_exp_wrt_typ_open_exp_wrt_typ :
forall e1 X1,
  X1 `notin` typefv_exp e1 ->
  close_exp_wrt_typ X1 (open_exp_wrt_typ e1 (t_tvar_f X1)) = e1.
Proof.
unfold close_exp_wrt_typ; unfold open_exp_wrt_typ; default_simp.
Qed.

Hint Resolve close_exp_wrt_typ_open_exp_wrt_typ : lngen.
Hint Rewrite close_exp_wrt_typ_open_exp_wrt_typ using solve [auto] : lngen.

Lemma close_exp_wrt_exp_open_exp_wrt_exp :
forall e1 x1,
  x1 `notin` termfv_exp e1 ->
  close_exp_wrt_exp x1 (open_exp_wrt_exp e1 (e_var_f x1)) = e1.
Proof.
unfold close_exp_wrt_exp; unfold open_exp_wrt_exp; default_simp.
Qed.

Hint Resolve close_exp_wrt_exp_open_exp_wrt_exp : lngen.
Hint Rewrite close_exp_wrt_exp_open_exp_wrt_exp using solve [auto] : lngen.

(* begin hide *)

Lemma open_typ_wrt_typ_rec_close_typ_wrt_typ_rec_mutual :
(forall A1 X1 n1,
  open_typ_wrt_typ_rec n1 (t_tvar_f X1) (close_typ_wrt_typ_rec n1 X1 A1) = A1).
Proof.
apply_mutual_ind typ_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma open_typ_wrt_typ_rec_close_typ_wrt_typ_rec :
forall A1 X1 n1,
  open_typ_wrt_typ_rec n1 (t_tvar_f X1) (close_typ_wrt_typ_rec n1 X1 A1) = A1.
Proof.
pose proof open_typ_wrt_typ_rec_close_typ_wrt_typ_rec_mutual as H; intuition eauto.
Qed.

Hint Resolve open_typ_wrt_typ_rec_close_typ_wrt_typ_rec : lngen.
Hint Rewrite open_typ_wrt_typ_rec_close_typ_wrt_typ_rec using solve [auto] : lngen.

(* end hide *)

(* begin hide *)

Lemma open_exp_wrt_typ_rec_close_exp_wrt_typ_rec_mutual :
(forall e1 X1 n1,
  open_exp_wrt_typ_rec n1 (t_tvar_f X1) (close_exp_wrt_typ_rec n1 X1 e1) = e1).
Proof.
apply_mutual_ind exp_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma open_exp_wrt_typ_rec_close_exp_wrt_typ_rec :
forall e1 X1 n1,
  open_exp_wrt_typ_rec n1 (t_tvar_f X1) (close_exp_wrt_typ_rec n1 X1 e1) = e1.
Proof.
pose proof open_exp_wrt_typ_rec_close_exp_wrt_typ_rec_mutual as H; intuition eauto.
Qed.

Hint Resolve open_exp_wrt_typ_rec_close_exp_wrt_typ_rec : lngen.
Hint Rewrite open_exp_wrt_typ_rec_close_exp_wrt_typ_rec using solve [auto] : lngen.

(* end hide *)

(* begin hide *)

Lemma open_exp_wrt_exp_rec_close_exp_wrt_exp_rec_mutual :
(forall e1 x1 n1,
  open_exp_wrt_exp_rec n1 (e_var_f x1) (close_exp_wrt_exp_rec n1 x1 e1) = e1).
Proof.
apply_mutual_ind exp_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma open_exp_wrt_exp_rec_close_exp_wrt_exp_rec :
forall e1 x1 n1,
  open_exp_wrt_exp_rec n1 (e_var_f x1) (close_exp_wrt_exp_rec n1 x1 e1) = e1.
Proof.
pose proof open_exp_wrt_exp_rec_close_exp_wrt_exp_rec_mutual as H; intuition eauto.
Qed.

Hint Resolve open_exp_wrt_exp_rec_close_exp_wrt_exp_rec : lngen.
Hint Rewrite open_exp_wrt_exp_rec_close_exp_wrt_exp_rec using solve [auto] : lngen.

(* end hide *)

Lemma open_typ_wrt_typ_close_typ_wrt_typ :
forall A1 X1,
  open_typ_wrt_typ (close_typ_wrt_typ X1 A1) (t_tvar_f X1) = A1.
Proof.
unfold close_typ_wrt_typ; unfold open_typ_wrt_typ; default_simp.
Qed.

Hint Resolve open_typ_wrt_typ_close_typ_wrt_typ : lngen.
Hint Rewrite open_typ_wrt_typ_close_typ_wrt_typ using solve [auto] : lngen.

Lemma open_exp_wrt_typ_close_exp_wrt_typ :
forall e1 X1,
  open_exp_wrt_typ (close_exp_wrt_typ X1 e1) (t_tvar_f X1) = e1.
Proof.
unfold close_exp_wrt_typ; unfold open_exp_wrt_typ; default_simp.
Qed.

Hint Resolve open_exp_wrt_typ_close_exp_wrt_typ : lngen.
Hint Rewrite open_exp_wrt_typ_close_exp_wrt_typ using solve [auto] : lngen.

Lemma open_exp_wrt_exp_close_exp_wrt_exp :
forall e1 x1,
  open_exp_wrt_exp (close_exp_wrt_exp x1 e1) (e_var_f x1) = e1.
Proof.
unfold close_exp_wrt_exp; unfold open_exp_wrt_exp; default_simp.
Qed.

Hint Resolve open_exp_wrt_exp_close_exp_wrt_exp : lngen.
Hint Rewrite open_exp_wrt_exp_close_exp_wrt_exp using solve [auto] : lngen.

(* begin hide *)

Lemma open_typ_wrt_typ_rec_inj_mutual :
(forall A2 A1 X1 n1,
  X1 `notin` typefv_typ A2 ->
  X1 `notin` typefv_typ A1 ->
  open_typ_wrt_typ_rec n1 (t_tvar_f X1) A2 = open_typ_wrt_typ_rec n1 (t_tvar_f X1) A1 ->
  A2 = A1).
Proof.
apply_mutual_ind typ_mutind;
intros; match goal with
          | |- _ = ?term => destruct term
        end;
default_simp; eauto with lngen.
Qed.

(* end hide *)

(* begin hide *)

Lemma open_typ_wrt_typ_rec_inj :
forall A2 A1 X1 n1,
  X1 `notin` typefv_typ A2 ->
  X1 `notin` typefv_typ A1 ->
  open_typ_wrt_typ_rec n1 (t_tvar_f X1) A2 = open_typ_wrt_typ_rec n1 (t_tvar_f X1) A1 ->
  A2 = A1.
Proof.
pose proof open_typ_wrt_typ_rec_inj_mutual as H; intuition eauto.
Qed.

Hint Immediate open_typ_wrt_typ_rec_inj : lngen.

(* end hide *)

(* begin hide *)

Lemma open_exp_wrt_typ_rec_inj_mutual :
(forall e2 e1 X1 n1,
  X1 `notin` typefv_exp e2 ->
  X1 `notin` typefv_exp e1 ->
  open_exp_wrt_typ_rec n1 (t_tvar_f X1) e2 = open_exp_wrt_typ_rec n1 (t_tvar_f X1) e1 ->
  e2 = e1).
Proof.
apply_mutual_ind exp_mutind;
intros; match goal with
          | |- _ = ?term => destruct term
        end;
default_simp; eauto with lngen.
Qed.

(* end hide *)

(* begin hide *)

Lemma open_exp_wrt_typ_rec_inj :
forall e2 e1 X1 n1,
  X1 `notin` typefv_exp e2 ->
  X1 `notin` typefv_exp e1 ->
  open_exp_wrt_typ_rec n1 (t_tvar_f X1) e2 = open_exp_wrt_typ_rec n1 (t_tvar_f X1) e1 ->
  e2 = e1.
Proof.
pose proof open_exp_wrt_typ_rec_inj_mutual as H; intuition eauto.
Qed.

Hint Immediate open_exp_wrt_typ_rec_inj : lngen.

(* end hide *)

(* begin hide *)

Lemma open_exp_wrt_exp_rec_inj_mutual :
(forall e2 e1 x1 n1,
  x1 `notin` termfv_exp e2 ->
  x1 `notin` termfv_exp e1 ->
  open_exp_wrt_exp_rec n1 (e_var_f x1) e2 = open_exp_wrt_exp_rec n1 (e_var_f x1) e1 ->
  e2 = e1).
Proof.
apply_mutual_ind exp_mutind;
intros; match goal with
          | |- _ = ?term => destruct term
        end;
default_simp; eauto with lngen.
Qed.

(* end hide *)

(* begin hide *)

Lemma open_exp_wrt_exp_rec_inj :
forall e2 e1 x1 n1,
  x1 `notin` termfv_exp e2 ->
  x1 `notin` termfv_exp e1 ->
  open_exp_wrt_exp_rec n1 (e_var_f x1) e2 = open_exp_wrt_exp_rec n1 (e_var_f x1) e1 ->
  e2 = e1.
Proof.
pose proof open_exp_wrt_exp_rec_inj_mutual as H; intuition eauto.
Qed.

Hint Immediate open_exp_wrt_exp_rec_inj : lngen.

(* end hide *)

Lemma open_typ_wrt_typ_inj :
forall A2 A1 X1,
  X1 `notin` typefv_typ A2 ->
  X1 `notin` typefv_typ A1 ->
  open_typ_wrt_typ A2 (t_tvar_f X1) = open_typ_wrt_typ A1 (t_tvar_f X1) ->
  A2 = A1.
Proof.
unfold open_typ_wrt_typ; eauto with lngen.
Qed.

Hint Immediate open_typ_wrt_typ_inj : lngen.

Lemma open_exp_wrt_typ_inj :
forall e2 e1 X1,
  X1 `notin` typefv_exp e2 ->
  X1 `notin` typefv_exp e1 ->
  open_exp_wrt_typ e2 (t_tvar_f X1) = open_exp_wrt_typ e1 (t_tvar_f X1) ->
  e2 = e1.
Proof.
unfold open_exp_wrt_typ; eauto with lngen.
Qed.

Hint Immediate open_exp_wrt_typ_inj : lngen.

Lemma open_exp_wrt_exp_inj :
forall e2 e1 x1,
  x1 `notin` termfv_exp e2 ->
  x1 `notin` termfv_exp e1 ->
  open_exp_wrt_exp e2 (e_var_f x1) = open_exp_wrt_exp e1 (e_var_f x1) ->
  e2 = e1.
Proof.
unfold open_exp_wrt_exp; eauto with lngen.
Qed.

Hint Immediate open_exp_wrt_exp_inj : lngen.


(* *********************************************************************** *)
(** * Theorems about [lc] *)

Ltac default_auto ::= auto with lngen brute_force; tauto.
Ltac default_autorewrite ::= autorewrite with lngen.

(* begin hide *)

Lemma degree_typ_wrt_typ_of_lc_typ_mutual :
(forall A1,
  lc_typ A1 ->
  degree_typ_wrt_typ 0 A1).
Proof.
apply_mutual_ind lc_typ_mutind;
intros;
let X1 := fresh "X1" in pick_fresh X1;
repeat (match goal with
          | H1 : _, H2 : _ |- _ => specialize H1 with H2
        end);
default_simp; eauto with lngen.
Qed.

(* end hide *)

Lemma degree_typ_wrt_typ_of_lc_typ :
forall A1,
  lc_typ A1 ->
  degree_typ_wrt_typ 0 A1.
Proof.
pose proof degree_typ_wrt_typ_of_lc_typ_mutual as H; intuition eauto.
Qed.

Hint Resolve degree_typ_wrt_typ_of_lc_typ : lngen.

(* begin hide *)

Lemma degree_exp_wrt_typ_of_lc_exp_mutual :
(forall e1,
  lc_exp e1 ->
  degree_exp_wrt_typ 0 e1).
Proof.
apply_mutual_ind lc_exp_mutind;
intros;
let X1 := fresh "X1" in pick_fresh X1;
let x1 := fresh "x1" in pick_fresh x1;
repeat (match goal with
          | H1 : _, H2 : _ |- _ => specialize H1 with H2
        end);
default_simp; eauto with lngen.
Qed.

(* end hide *)

Lemma degree_exp_wrt_typ_of_lc_exp :
forall e1,
  lc_exp e1 ->
  degree_exp_wrt_typ 0 e1.
Proof.
pose proof degree_exp_wrt_typ_of_lc_exp_mutual as H; intuition eauto.
Qed.

Hint Resolve degree_exp_wrt_typ_of_lc_exp : lngen.

(* begin hide *)

Lemma degree_exp_wrt_exp_of_lc_exp_mutual :
(forall e1,
  lc_exp e1 ->
  degree_exp_wrt_exp 0 e1).
Proof.
apply_mutual_ind lc_exp_mutind;
intros;
let X1 := fresh "X1" in pick_fresh X1;
let x1 := fresh "x1" in pick_fresh x1;
repeat (match goal with
          | H1 : _, H2 : _ |- _ => specialize H1 with H2
        end);
default_simp; eauto with lngen.
Qed.

(* end hide *)

Lemma degree_exp_wrt_exp_of_lc_exp :
forall e1,
  lc_exp e1 ->
  degree_exp_wrt_exp 0 e1.
Proof.
pose proof degree_exp_wrt_exp_of_lc_exp_mutual as H; intuition eauto.
Qed.

Hint Resolve degree_exp_wrt_exp_of_lc_exp : lngen.

(* begin hide *)

Lemma lc_typ_of_degree_size_mutual :
forall i1,
(forall A1,
  size_typ A1 = i1 ->
  degree_typ_wrt_typ 0 A1 ->
  lc_typ A1).
Proof.
intros i1; pattern i1; apply lt_wf_rec;
clear i1; intros i1 H1;
apply_mutual_ind typ_mutind;
default_simp;
(* non-trivial cases *)
constructor; default_simp; eapply_first_lt_hyp;
(* instantiate the size *)
match goal with
  | |- _ = _ => reflexivity
  | _ => idtac
end;
instantiate;
(* everything should be easy now *)
default_simp.
Qed.

(* end hide *)

Lemma lc_typ_of_degree :
forall A1,
  degree_typ_wrt_typ 0 A1 ->
  lc_typ A1.
Proof.
intros A1; intros;
pose proof (lc_typ_of_degree_size_mutual (size_typ A1));
intuition eauto.
Qed.

Hint Resolve lc_typ_of_degree : lngen.

(* begin hide *)

Lemma lc_exp_of_degree_size_mutual :
forall i1,
(forall e1,
  size_exp e1 = i1 ->
  degree_exp_wrt_typ 0 e1 ->
  degree_exp_wrt_exp 0 e1 ->
  lc_exp e1).
Proof.
intros i1; pattern i1; apply lt_wf_rec;
clear i1; intros i1 H1;
apply_mutual_ind exp_mutind;
default_simp;
(* non-trivial cases *)
constructor; default_simp; eapply_first_lt_hyp;
(* instantiate the size *)
match goal with
  | |- _ = _ => reflexivity
  | _ => idtac
end;
instantiate;
(* everything should be easy now *)
default_simp.
Qed.

(* end hide *)

Lemma lc_exp_of_degree :
forall e1,
  degree_exp_wrt_typ 0 e1 ->
  degree_exp_wrt_exp 0 e1 ->
  lc_exp e1.
Proof.
intros e1; intros;
pose proof (lc_exp_of_degree_size_mutual (size_exp e1));
intuition eauto.
Qed.

Hint Resolve lc_exp_of_degree : lngen.

Ltac typ_lc_exists_tac :=
  repeat (match goal with
            | H : _ |- _ =>
              let J1 := fresh in pose proof H as J1; apply degree_typ_wrt_typ_of_lc_typ in J1; clear H
          end).

Ltac exp_lc_exists_tac :=
  repeat (match goal with
            | H : _ |- _ =>
              let J1 := fresh in pose proof H as J1; apply degree_exp_wrt_typ_of_lc_exp in J1;
              let J2 := fresh in pose proof H as J2; apply degree_exp_wrt_exp_of_lc_exp in J2; clear H
          end).

Lemma lc_t_forall_exists :
forall X1 A1 B1,
  lc_typ A1 ->
  lc_typ (open_typ_wrt_typ B1 (t_tvar_f X1)) ->
  lc_typ (t_forall A1 B1).
Proof.
intros; typ_lc_exists_tac; eauto with lngen.
Qed.

Lemma lc_e_abs_exists :
forall x1 A1 e1,
  lc_typ A1 ->
  lc_exp (open_exp_wrt_exp e1 (e_var_f x1)) ->
  lc_exp (e_abs A1 e1).
Proof.
intros; exp_lc_exists_tac; eauto with lngen.
Qed.

Lemma lc_e_fixpoint_exists :
forall x1 A1 e1,
  lc_typ A1 ->
  lc_exp (open_exp_wrt_exp e1 (e_var_f x1)) ->
  lc_exp (e_fixpoint A1 e1).
Proof.
intros; exp_lc_exists_tac; eauto with lngen.
Qed.

Lemma lc_e_tabs_exists :
forall X1 e1,
  lc_exp (open_exp_wrt_typ e1 (t_tvar_f X1)) ->
  lc_exp (e_tabs e1).
Proof.
intros; exp_lc_exists_tac; eauto with lngen.
Qed.

Hint Extern 1 (lc_typ (t_forall _ _)) =>
  let X1 := fresh in
  pick_fresh X1;
  apply (lc_t_forall_exists X1) : core.

Hint Extern 1 (lc_exp (e_abs _ _)) =>
  let x1 := fresh in
  pick_fresh x1;
  apply (lc_e_abs_exists x1) : core.

Hint Extern 1 (lc_exp (e_fixpoint _ _)) =>
  let x1 := fresh in
  pick_fresh x1;
  apply (lc_e_fixpoint_exists x1) : core.

Hint Extern 1 (lc_exp (e_tabs _)) =>
  let X1 := fresh in
  pick_fresh X1;
  apply (lc_e_tabs_exists X1) : core.

Lemma lc_body_typ_wrt_typ :
forall A1 A2,
  body_typ_wrt_typ A1 ->
  lc_typ A2 ->
  lc_typ (open_typ_wrt_typ A1 A2).
Proof.
unfold body_typ_wrt_typ;
default_simp;
let X1 := fresh "x" in
pick_fresh X1;
specialize_all X1;
typ_lc_exists_tac;
eauto with lngen.
Qed.

Hint Resolve lc_body_typ_wrt_typ : lngen.

Lemma lc_body_exp_wrt_typ :
forall e1 A1,
  body_exp_wrt_typ e1 ->
  lc_typ A1 ->
  lc_exp (open_exp_wrt_typ e1 A1).
Proof.
unfold body_exp_wrt_typ;
default_simp;
let X1 := fresh "x" in
pick_fresh X1;
specialize_all X1;
exp_lc_exists_tac;
eauto with lngen.
Qed.

Hint Resolve lc_body_exp_wrt_typ : lngen.

Lemma lc_body_exp_wrt_exp :
forall e1 e2,
  body_exp_wrt_exp e1 ->
  lc_exp e2 ->
  lc_exp (open_exp_wrt_exp e1 e2).
Proof.
unfold body_exp_wrt_exp;
default_simp;
let x1 := fresh "x" in
pick_fresh x1;
specialize_all x1;
exp_lc_exists_tac;
eauto with lngen.
Qed.

Hint Resolve lc_body_exp_wrt_exp : lngen.

Lemma lc_body_t_forall_2 :
forall A1 B1,
  lc_typ (t_forall A1 B1) ->
  body_typ_wrt_typ B1.
Proof.
default_simp.
Qed.

Hint Resolve lc_body_t_forall_2 : lngen.

Lemma lc_body_e_abs_2 :
forall A1 e1,
  lc_exp (e_abs A1 e1) ->
  body_exp_wrt_exp e1.
Proof.
default_simp.
Qed.

Hint Resolve lc_body_e_abs_2 : lngen.

Lemma lc_body_e_fixpoint_2 :
forall A1 e1,
  lc_exp (e_fixpoint A1 e1) ->
  body_exp_wrt_exp e1.
Proof.
default_simp.
Qed.

Hint Resolve lc_body_e_fixpoint_2 : lngen.

Lemma lc_body_e_tabs_1 :
forall e1,
  lc_exp (e_tabs e1) ->
  body_exp_wrt_typ e1.
Proof.
default_simp.
Qed.

Hint Resolve lc_body_e_tabs_1 : lngen.

(* begin hide *)

Lemma lc_typ_unique_mutual :
(forall A1 (proof2 proof3 : lc_typ A1), proof2 = proof3).
Proof.
apply_mutual_ind lc_typ_mutind;
intros;
let proof1 := fresh "proof1" in
rename_last_into proof1; dependent destruction proof1;
f_equal; default_simp; auto using @functional_extensionality_dep with lngen.
Qed.

(* end hide *)

Lemma lc_typ_unique :
forall A1 (proof2 proof3 : lc_typ A1), proof2 = proof3.
Proof.
pose proof lc_typ_unique_mutual as H; intuition eauto.
Qed.

Hint Resolve lc_typ_unique : lngen.

(* begin hide *)

Lemma lc_exp_unique_mutual :
(forall e1 (proof2 proof3 : lc_exp e1), proof2 = proof3).
Proof.
apply_mutual_ind lc_exp_mutind;
intros;
let proof1 := fresh "proof1" in
rename_last_into proof1; dependent destruction proof1;
f_equal; default_simp; auto using @functional_extensionality_dep with lngen.
Qed.

(* end hide *)

Lemma lc_exp_unique :
forall e1 (proof2 proof3 : lc_exp e1), proof2 = proof3.
Proof.
pose proof lc_exp_unique_mutual as H; intuition eauto.
Qed.

Hint Resolve lc_exp_unique : lngen.

(* begin hide *)

Lemma lc_typ_of_lc_set_typ_mutual :
(forall A1, lc_set_typ A1 -> lc_typ A1).
Proof.
apply_mutual_ind lc_set_typ_mutind;
default_simp.
Qed.

(* end hide *)

Lemma lc_typ_of_lc_set_typ :
forall A1, lc_set_typ A1 -> lc_typ A1.
Proof.
pose proof lc_typ_of_lc_set_typ_mutual as H; intuition eauto.
Qed.

Hint Resolve lc_typ_of_lc_set_typ : lngen.

(* begin hide *)

Lemma lc_exp_of_lc_set_exp_mutual :
(forall e1, lc_set_exp e1 -> lc_exp e1).
Proof.
apply_mutual_ind lc_set_exp_mutind;
default_simp.
Qed.

(* end hide *)

Lemma lc_exp_of_lc_set_exp :
forall e1, lc_set_exp e1 -> lc_exp e1.
Proof.
pose proof lc_exp_of_lc_set_exp_mutual as H; intuition eauto.
Qed.

Hint Resolve lc_exp_of_lc_set_exp : lngen.

(* begin hide *)

Lemma lc_set_typ_of_lc_typ_size_mutual :
forall i1,
(forall A1,
  size_typ A1 = i1 ->
  lc_typ A1 ->
  lc_set_typ A1).
Proof.
intros i1; pattern i1; apply lt_wf_rec;
clear i1; intros i1 H1;
apply_mutual_ind typ_mutrec;
default_simp;
try solve [assert False by default_simp; tauto];
(* non-trivial cases *)
constructor; default_simp;
try first [apply lc_set_typ_of_lc_typ];
default_simp; eapply_first_lt_hyp;
(* instantiate the size *)
match goal with
  | |- _ = _ => reflexivity
  | _ => idtac
end;
instantiate;
(* everything should be easy now *)
default_simp.
Qed.

(* end hide *)

Lemma lc_set_typ_of_lc_typ :
forall A1,
  lc_typ A1 ->
  lc_set_typ A1.
Proof.
intros A1; intros;
pose proof (lc_set_typ_of_lc_typ_size_mutual (size_typ A1));
intuition eauto.
Qed.

Hint Resolve lc_set_typ_of_lc_typ : lngen.

(* begin hide *)

Lemma lc_set_exp_of_lc_exp_size_mutual :
forall i1,
(forall e1,
  size_exp e1 = i1 ->
  lc_exp e1 ->
  lc_set_exp e1).
Proof.
intros i1; pattern i1; apply lt_wf_rec;
clear i1; intros i1 H1;
apply_mutual_ind exp_mutrec;
default_simp;
try solve [assert False by default_simp; tauto];
(* non-trivial cases *)
constructor; default_simp;
try first [apply lc_set_typ_of_lc_typ
 | apply lc_set_exp_of_lc_exp];
default_simp; eapply_first_lt_hyp;
(* instantiate the size *)
match goal with
  | |- _ = _ => reflexivity
  | _ => idtac
end;
instantiate;
(* everything should be easy now *)
default_simp.
Qed.

(* end hide *)

Lemma lc_set_exp_of_lc_exp :
forall e1,
  lc_exp e1 ->
  lc_set_exp e1.
Proof.
intros e1; intros;
pose proof (lc_set_exp_of_lc_exp_size_mutual (size_exp e1));
intuition eauto.
Qed.

Hint Resolve lc_set_exp_of_lc_exp : lngen.


(* *********************************************************************** *)
(** * More theorems about [open] and [close] *)

Ltac default_auto ::= auto with lngen; tauto.
Ltac default_autorewrite ::= fail.

(* begin hide *)

Lemma close_typ_wrt_typ_rec_degree_typ_wrt_typ_mutual :
(forall A1 X1 n1,
  degree_typ_wrt_typ n1 A1 ->
  X1 `notin` typefv_typ A1 ->
  close_typ_wrt_typ_rec n1 X1 A1 = A1).
Proof.
apply_mutual_ind typ_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma close_typ_wrt_typ_rec_degree_typ_wrt_typ :
forall A1 X1 n1,
  degree_typ_wrt_typ n1 A1 ->
  X1 `notin` typefv_typ A1 ->
  close_typ_wrt_typ_rec n1 X1 A1 = A1.
Proof.
pose proof close_typ_wrt_typ_rec_degree_typ_wrt_typ_mutual as H; intuition eauto.
Qed.

Hint Resolve close_typ_wrt_typ_rec_degree_typ_wrt_typ : lngen.
Hint Rewrite close_typ_wrt_typ_rec_degree_typ_wrt_typ using solve [auto] : lngen.

(* end hide *)

(* begin hide *)

Lemma close_exp_wrt_typ_rec_degree_exp_wrt_typ_mutual :
(forall e1 X1 n1,
  degree_exp_wrt_typ n1 e1 ->
  X1 `notin` typefv_exp e1 ->
  close_exp_wrt_typ_rec n1 X1 e1 = e1).
Proof.
apply_mutual_ind exp_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma close_exp_wrt_typ_rec_degree_exp_wrt_typ :
forall e1 X1 n1,
  degree_exp_wrt_typ n1 e1 ->
  X1 `notin` typefv_exp e1 ->
  close_exp_wrt_typ_rec n1 X1 e1 = e1.
Proof.
pose proof close_exp_wrt_typ_rec_degree_exp_wrt_typ_mutual as H; intuition eauto.
Qed.

Hint Resolve close_exp_wrt_typ_rec_degree_exp_wrt_typ : lngen.
Hint Rewrite close_exp_wrt_typ_rec_degree_exp_wrt_typ using solve [auto] : lngen.

(* end hide *)

(* begin hide *)

Lemma close_exp_wrt_exp_rec_degree_exp_wrt_exp_mutual :
(forall e1 x1 n1,
  degree_exp_wrt_exp n1 e1 ->
  x1 `notin` termfv_exp e1 ->
  close_exp_wrt_exp_rec n1 x1 e1 = e1).
Proof.
apply_mutual_ind exp_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma close_exp_wrt_exp_rec_degree_exp_wrt_exp :
forall e1 x1 n1,
  degree_exp_wrt_exp n1 e1 ->
  x1 `notin` termfv_exp e1 ->
  close_exp_wrt_exp_rec n1 x1 e1 = e1.
Proof.
pose proof close_exp_wrt_exp_rec_degree_exp_wrt_exp_mutual as H; intuition eauto.
Qed.

Hint Resolve close_exp_wrt_exp_rec_degree_exp_wrt_exp : lngen.
Hint Rewrite close_exp_wrt_exp_rec_degree_exp_wrt_exp using solve [auto] : lngen.

(* end hide *)

Lemma close_typ_wrt_typ_lc_typ :
forall A1 X1,
  lc_typ A1 ->
  X1 `notin` typefv_typ A1 ->
  close_typ_wrt_typ X1 A1 = A1.
Proof.
unfold close_typ_wrt_typ; default_simp.
Qed.

Hint Resolve close_typ_wrt_typ_lc_typ : lngen.
Hint Rewrite close_typ_wrt_typ_lc_typ using solve [auto] : lngen.

Lemma close_exp_wrt_typ_lc_exp :
forall e1 X1,
  lc_exp e1 ->
  X1 `notin` typefv_exp e1 ->
  close_exp_wrt_typ X1 e1 = e1.
Proof.
unfold close_exp_wrt_typ; default_simp.
Qed.

Hint Resolve close_exp_wrt_typ_lc_exp : lngen.
Hint Rewrite close_exp_wrt_typ_lc_exp using solve [auto] : lngen.

Lemma close_exp_wrt_exp_lc_exp :
forall e1 x1,
  lc_exp e1 ->
  x1 `notin` termfv_exp e1 ->
  close_exp_wrt_exp x1 e1 = e1.
Proof.
unfold close_exp_wrt_exp; default_simp.
Qed.

Hint Resolve close_exp_wrt_exp_lc_exp : lngen.
Hint Rewrite close_exp_wrt_exp_lc_exp using solve [auto] : lngen.

(* begin hide *)

Lemma open_typ_wrt_typ_rec_degree_typ_wrt_typ_mutual :
(forall A2 A1 n1,
  degree_typ_wrt_typ n1 A2 ->
  open_typ_wrt_typ_rec n1 A1 A2 = A2).
Proof.
apply_mutual_ind typ_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma open_typ_wrt_typ_rec_degree_typ_wrt_typ :
forall A2 A1 n1,
  degree_typ_wrt_typ n1 A2 ->
  open_typ_wrt_typ_rec n1 A1 A2 = A2.
Proof.
pose proof open_typ_wrt_typ_rec_degree_typ_wrt_typ_mutual as H; intuition eauto.
Qed.

Hint Resolve open_typ_wrt_typ_rec_degree_typ_wrt_typ : lngen.
Hint Rewrite open_typ_wrt_typ_rec_degree_typ_wrt_typ using solve [auto] : lngen.

(* end hide *)

(* begin hide *)

Lemma open_exp_wrt_typ_rec_degree_exp_wrt_typ_mutual :
(forall e1 A1 n1,
  degree_exp_wrt_typ n1 e1 ->
  open_exp_wrt_typ_rec n1 A1 e1 = e1).
Proof.
apply_mutual_ind exp_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma open_exp_wrt_typ_rec_degree_exp_wrt_typ :
forall e1 A1 n1,
  degree_exp_wrt_typ n1 e1 ->
  open_exp_wrt_typ_rec n1 A1 e1 = e1.
Proof.
pose proof open_exp_wrt_typ_rec_degree_exp_wrt_typ_mutual as H; intuition eauto.
Qed.

Hint Resolve open_exp_wrt_typ_rec_degree_exp_wrt_typ : lngen.
Hint Rewrite open_exp_wrt_typ_rec_degree_exp_wrt_typ using solve [auto] : lngen.

(* end hide *)

(* begin hide *)

Lemma open_exp_wrt_exp_rec_degree_exp_wrt_exp_mutual :
(forall e2 e1 n1,
  degree_exp_wrt_exp n1 e2 ->
  open_exp_wrt_exp_rec n1 e1 e2 = e2).
Proof.
apply_mutual_ind exp_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma open_exp_wrt_exp_rec_degree_exp_wrt_exp :
forall e2 e1 n1,
  degree_exp_wrt_exp n1 e2 ->
  open_exp_wrt_exp_rec n1 e1 e2 = e2.
Proof.
pose proof open_exp_wrt_exp_rec_degree_exp_wrt_exp_mutual as H; intuition eauto.
Qed.

Hint Resolve open_exp_wrt_exp_rec_degree_exp_wrt_exp : lngen.
Hint Rewrite open_exp_wrt_exp_rec_degree_exp_wrt_exp using solve [auto] : lngen.

(* end hide *)

Lemma open_typ_wrt_typ_lc_typ :
forall A2 A1,
  lc_typ A2 ->
  open_typ_wrt_typ A2 A1 = A2.
Proof.
unfold open_typ_wrt_typ; default_simp.
Qed.

Hint Resolve open_typ_wrt_typ_lc_typ : lngen.
Hint Rewrite open_typ_wrt_typ_lc_typ using solve [auto] : lngen.

Lemma open_exp_wrt_typ_lc_exp :
forall e1 A1,
  lc_exp e1 ->
  open_exp_wrt_typ e1 A1 = e1.
Proof.
unfold open_exp_wrt_typ; default_simp.
Qed.

Hint Resolve open_exp_wrt_typ_lc_exp : lngen.
Hint Rewrite open_exp_wrt_typ_lc_exp using solve [auto] : lngen.

Lemma open_exp_wrt_exp_lc_exp :
forall e2 e1,
  lc_exp e2 ->
  open_exp_wrt_exp e2 e1 = e2.
Proof.
unfold open_exp_wrt_exp; default_simp.
Qed.

Hint Resolve open_exp_wrt_exp_lc_exp : lngen.
Hint Rewrite open_exp_wrt_exp_lc_exp using solve [auto] : lngen.


(* *********************************************************************** *)
(** * Theorems about [fv] *)

Ltac default_auto ::= auto with set lngen; tauto.
Ltac default_autorewrite ::= autorewrite with lngen.

(* begin hide *)

Lemma typefv_typ_close_typ_wrt_typ_rec_mutual :
(forall A1 X1 n1,
  typefv_typ (close_typ_wrt_typ_rec n1 X1 A1) [=] remove X1 (typefv_typ A1)).
Proof.
apply_mutual_ind typ_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

(* begin hide *)

Lemma typefv_typ_close_typ_wrt_typ_rec :
forall A1 X1 n1,
  typefv_typ (close_typ_wrt_typ_rec n1 X1 A1) [=] remove X1 (typefv_typ A1).
Proof.
pose proof typefv_typ_close_typ_wrt_typ_rec_mutual as H; intuition eauto.
Qed.

Hint Resolve typefv_typ_close_typ_wrt_typ_rec : lngen.
Hint Rewrite typefv_typ_close_typ_wrt_typ_rec using solve [auto] : lngen.

(* end hide *)

(* begin hide *)

Lemma typefv_exp_close_exp_wrt_typ_rec_mutual :
(forall e1 X1 n1,
  typefv_exp (close_exp_wrt_typ_rec n1 X1 e1) [=] remove X1 (typefv_exp e1)).
Proof.
apply_mutual_ind exp_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

(* begin hide *)

Lemma typefv_exp_close_exp_wrt_typ_rec :
forall e1 X1 n1,
  typefv_exp (close_exp_wrt_typ_rec n1 X1 e1) [=] remove X1 (typefv_exp e1).
Proof.
pose proof typefv_exp_close_exp_wrt_typ_rec_mutual as H; intuition eauto.
Qed.

Hint Resolve typefv_exp_close_exp_wrt_typ_rec : lngen.
Hint Rewrite typefv_exp_close_exp_wrt_typ_rec using solve [auto] : lngen.

(* end hide *)

(* begin hide *)

Lemma typefv_exp_close_exp_wrt_exp_rec_mutual :
(forall e1 x1 n1,
  typefv_exp (close_exp_wrt_exp_rec n1 x1 e1) [=] typefv_exp e1).
Proof.
apply_mutual_ind exp_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

(* begin hide *)

Lemma typefv_exp_close_exp_wrt_exp_rec :
forall e1 x1 n1,
  typefv_exp (close_exp_wrt_exp_rec n1 x1 e1) [=] typefv_exp e1.
Proof.
pose proof typefv_exp_close_exp_wrt_exp_rec_mutual as H; intuition eauto.
Qed.

Hint Resolve typefv_exp_close_exp_wrt_exp_rec : lngen.
Hint Rewrite typefv_exp_close_exp_wrt_exp_rec using solve [auto] : lngen.

(* end hide *)

(* begin hide *)

Lemma termfv_exp_close_exp_wrt_typ_rec_mutual :
(forall e1 X1 n1,
  termfv_exp (close_exp_wrt_typ_rec n1 X1 e1) [=] termfv_exp e1).
Proof.
apply_mutual_ind exp_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

(* begin hide *)

Lemma termfv_exp_close_exp_wrt_typ_rec :
forall e1 X1 n1,
  termfv_exp (close_exp_wrt_typ_rec n1 X1 e1) [=] termfv_exp e1.
Proof.
pose proof termfv_exp_close_exp_wrt_typ_rec_mutual as H; intuition eauto.
Qed.

Hint Resolve termfv_exp_close_exp_wrt_typ_rec : lngen.
Hint Rewrite termfv_exp_close_exp_wrt_typ_rec using solve [auto] : lngen.

(* end hide *)

(* begin hide *)

Lemma termfv_exp_close_exp_wrt_exp_rec_mutual :
(forall e1 x1 n1,
  termfv_exp (close_exp_wrt_exp_rec n1 x1 e1) [=] remove x1 (termfv_exp e1)).
Proof.
apply_mutual_ind exp_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

(* begin hide *)

Lemma termfv_exp_close_exp_wrt_exp_rec :
forall e1 x1 n1,
  termfv_exp (close_exp_wrt_exp_rec n1 x1 e1) [=] remove x1 (termfv_exp e1).
Proof.
pose proof termfv_exp_close_exp_wrt_exp_rec_mutual as H; intuition eauto.
Qed.

Hint Resolve termfv_exp_close_exp_wrt_exp_rec : lngen.
Hint Rewrite termfv_exp_close_exp_wrt_exp_rec using solve [auto] : lngen.

(* end hide *)

Lemma typefv_typ_close_typ_wrt_typ :
forall A1 X1,
  typefv_typ (close_typ_wrt_typ X1 A1) [=] remove X1 (typefv_typ A1).
Proof.
unfold close_typ_wrt_typ; default_simp.
Qed.

Hint Resolve typefv_typ_close_typ_wrt_typ : lngen.
Hint Rewrite typefv_typ_close_typ_wrt_typ using solve [auto] : lngen.

Lemma typefv_exp_close_exp_wrt_typ :
forall e1 X1,
  typefv_exp (close_exp_wrt_typ X1 e1) [=] remove X1 (typefv_exp e1).
Proof.
unfold close_exp_wrt_typ; default_simp.
Qed.

Hint Resolve typefv_exp_close_exp_wrt_typ : lngen.
Hint Rewrite typefv_exp_close_exp_wrt_typ using solve [auto] : lngen.

Lemma typefv_exp_close_exp_wrt_exp :
forall e1 x1,
  typefv_exp (close_exp_wrt_exp x1 e1) [=] typefv_exp e1.
Proof.
unfold close_exp_wrt_exp; default_simp.
Qed.

Hint Resolve typefv_exp_close_exp_wrt_exp : lngen.
Hint Rewrite typefv_exp_close_exp_wrt_exp using solve [auto] : lngen.

Lemma termfv_exp_close_exp_wrt_typ :
forall e1 X1,
  termfv_exp (close_exp_wrt_typ X1 e1) [=] termfv_exp e1.
Proof.
unfold close_exp_wrt_typ; default_simp.
Qed.

Hint Resolve termfv_exp_close_exp_wrt_typ : lngen.
Hint Rewrite termfv_exp_close_exp_wrt_typ using solve [auto] : lngen.

Lemma termfv_exp_close_exp_wrt_exp :
forall e1 x1,
  termfv_exp (close_exp_wrt_exp x1 e1) [=] remove x1 (termfv_exp e1).
Proof.
unfold close_exp_wrt_exp; default_simp.
Qed.

Hint Resolve termfv_exp_close_exp_wrt_exp : lngen.
Hint Rewrite termfv_exp_close_exp_wrt_exp using solve [auto] : lngen.

(* begin hide *)

Lemma typefv_typ_open_typ_wrt_typ_rec_lower_mutual :
(forall A1 A2 n1,
  typefv_typ A1 [<=] typefv_typ (open_typ_wrt_typ_rec n1 A2 A1)).
Proof.
apply_mutual_ind typ_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

(* begin hide *)

Lemma typefv_typ_open_typ_wrt_typ_rec_lower :
forall A1 A2 n1,
  typefv_typ A1 [<=] typefv_typ (open_typ_wrt_typ_rec n1 A2 A1).
Proof.
pose proof typefv_typ_open_typ_wrt_typ_rec_lower_mutual as H; intuition eauto.
Qed.

Hint Resolve typefv_typ_open_typ_wrt_typ_rec_lower : lngen.

(* end hide *)

(* begin hide *)

Lemma typefv_exp_open_exp_wrt_typ_rec_lower_mutual :
(forall e1 A1 n1,
  typefv_exp e1 [<=] typefv_exp (open_exp_wrt_typ_rec n1 A1 e1)).
Proof.
apply_mutual_ind exp_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

(* begin hide *)

Lemma typefv_exp_open_exp_wrt_typ_rec_lower :
forall e1 A1 n1,
  typefv_exp e1 [<=] typefv_exp (open_exp_wrt_typ_rec n1 A1 e1).
Proof.
pose proof typefv_exp_open_exp_wrt_typ_rec_lower_mutual as H; intuition eauto.
Qed.

Hint Resolve typefv_exp_open_exp_wrt_typ_rec_lower : lngen.

(* end hide *)

(* begin hide *)

Lemma typefv_exp_open_exp_wrt_exp_rec_lower_mutual :
(forall e1 e2 n1,
  typefv_exp e1 [<=] typefv_exp (open_exp_wrt_exp_rec n1 e2 e1)).
Proof.
apply_mutual_ind exp_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

(* begin hide *)

Lemma typefv_exp_open_exp_wrt_exp_rec_lower :
forall e1 e2 n1,
  typefv_exp e1 [<=] typefv_exp (open_exp_wrt_exp_rec n1 e2 e1).
Proof.
pose proof typefv_exp_open_exp_wrt_exp_rec_lower_mutual as H; intuition eauto.
Qed.

Hint Resolve typefv_exp_open_exp_wrt_exp_rec_lower : lngen.

(* end hide *)

(* begin hide *)

Lemma termfv_exp_open_exp_wrt_typ_rec_lower_mutual :
(forall e1 A1 n1,
  termfv_exp e1 [<=] termfv_exp (open_exp_wrt_typ_rec n1 A1 e1)).
Proof.
apply_mutual_ind exp_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

(* begin hide *)

Lemma termfv_exp_open_exp_wrt_typ_rec_lower :
forall e1 A1 n1,
  termfv_exp e1 [<=] termfv_exp (open_exp_wrt_typ_rec n1 A1 e1).
Proof.
pose proof termfv_exp_open_exp_wrt_typ_rec_lower_mutual as H; intuition eauto.
Qed.

Hint Resolve termfv_exp_open_exp_wrt_typ_rec_lower : lngen.

(* end hide *)

(* begin hide *)

Lemma termfv_exp_open_exp_wrt_exp_rec_lower_mutual :
(forall e1 e2 n1,
  termfv_exp e1 [<=] termfv_exp (open_exp_wrt_exp_rec n1 e2 e1)).
Proof.
apply_mutual_ind exp_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

(* begin hide *)

Lemma termfv_exp_open_exp_wrt_exp_rec_lower :
forall e1 e2 n1,
  termfv_exp e1 [<=] termfv_exp (open_exp_wrt_exp_rec n1 e2 e1).
Proof.
pose proof termfv_exp_open_exp_wrt_exp_rec_lower_mutual as H; intuition eauto.
Qed.

Hint Resolve termfv_exp_open_exp_wrt_exp_rec_lower : lngen.

(* end hide *)

Lemma typefv_typ_open_typ_wrt_typ_lower :
forall A1 A2,
  typefv_typ A1 [<=] typefv_typ (open_typ_wrt_typ A1 A2).
Proof.
unfold open_typ_wrt_typ; default_simp.
Qed.

Hint Resolve typefv_typ_open_typ_wrt_typ_lower : lngen.

Lemma typefv_exp_open_exp_wrt_typ_lower :
forall e1 A1,
  typefv_exp e1 [<=] typefv_exp (open_exp_wrt_typ e1 A1).
Proof.
unfold open_exp_wrt_typ; default_simp.
Qed.

Hint Resolve typefv_exp_open_exp_wrt_typ_lower : lngen.

Lemma typefv_exp_open_exp_wrt_exp_lower :
forall e1 e2,
  typefv_exp e1 [<=] typefv_exp (open_exp_wrt_exp e1 e2).
Proof.
unfold open_exp_wrt_exp; default_simp.
Qed.

Hint Resolve typefv_exp_open_exp_wrt_exp_lower : lngen.

Lemma termfv_exp_open_exp_wrt_typ_lower :
forall e1 A1,
  termfv_exp e1 [<=] termfv_exp (open_exp_wrt_typ e1 A1).
Proof.
unfold open_exp_wrt_typ; default_simp.
Qed.

Hint Resolve termfv_exp_open_exp_wrt_typ_lower : lngen.

Lemma termfv_exp_open_exp_wrt_exp_lower :
forall e1 e2,
  termfv_exp e1 [<=] termfv_exp (open_exp_wrt_exp e1 e2).
Proof.
unfold open_exp_wrt_exp; default_simp.
Qed.

Hint Resolve termfv_exp_open_exp_wrt_exp_lower : lngen.

(* begin hide *)

Lemma typefv_typ_open_typ_wrt_typ_rec_upper_mutual :
(forall A1 A2 n1,
  typefv_typ (open_typ_wrt_typ_rec n1 A2 A1) [<=] typefv_typ A2 `union` typefv_typ A1).
Proof.
apply_mutual_ind typ_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

(* begin hide *)

Lemma typefv_typ_open_typ_wrt_typ_rec_upper :
forall A1 A2 n1,
  typefv_typ (open_typ_wrt_typ_rec n1 A2 A1) [<=] typefv_typ A2 `union` typefv_typ A1.
Proof.
pose proof typefv_typ_open_typ_wrt_typ_rec_upper_mutual as H; intuition eauto.
Qed.

Hint Resolve typefv_typ_open_typ_wrt_typ_rec_upper : lngen.

(* end hide *)

(* begin hide *)

Lemma typefv_exp_open_exp_wrt_typ_rec_upper_mutual :
(forall e1 A1 n1,
  typefv_exp (open_exp_wrt_typ_rec n1 A1 e1) [<=] typefv_typ A1 `union` typefv_exp e1).
Proof.
apply_mutual_ind exp_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

(* begin hide *)

Lemma typefv_exp_open_exp_wrt_typ_rec_upper :
forall e1 A1 n1,
  typefv_exp (open_exp_wrt_typ_rec n1 A1 e1) [<=] typefv_typ A1 `union` typefv_exp e1.
Proof.
pose proof typefv_exp_open_exp_wrt_typ_rec_upper_mutual as H; intuition eauto.
Qed.

Hint Resolve typefv_exp_open_exp_wrt_typ_rec_upper : lngen.

(* end hide *)

(* begin hide *)

Lemma typefv_exp_open_exp_wrt_exp_rec_upper_mutual :
(forall e1 e2 n1,
  typefv_exp (open_exp_wrt_exp_rec n1 e2 e1) [<=] typefv_exp e2 `union` typefv_exp e1).
Proof.
apply_mutual_ind exp_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

(* begin hide *)

Lemma typefv_exp_open_exp_wrt_exp_rec_upper :
forall e1 e2 n1,
  typefv_exp (open_exp_wrt_exp_rec n1 e2 e1) [<=] typefv_exp e2 `union` typefv_exp e1.
Proof.
pose proof typefv_exp_open_exp_wrt_exp_rec_upper_mutual as H; intuition eauto.
Qed.

Hint Resolve typefv_exp_open_exp_wrt_exp_rec_upper : lngen.

(* end hide *)

(* begin hide *)

Lemma termfv_exp_open_exp_wrt_typ_rec_upper_mutual :
(forall e1 A1 n1,
  termfv_exp (open_exp_wrt_typ_rec n1 A1 e1) [<=] termfv_exp e1).
Proof.
apply_mutual_ind exp_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

(* begin hide *)

Lemma termfv_exp_open_exp_wrt_typ_rec_upper :
forall e1 A1 n1,
  termfv_exp (open_exp_wrt_typ_rec n1 A1 e1) [<=] termfv_exp e1.
Proof.
pose proof termfv_exp_open_exp_wrt_typ_rec_upper_mutual as H; intuition eauto.
Qed.

Hint Resolve termfv_exp_open_exp_wrt_typ_rec_upper : lngen.

(* end hide *)

(* begin hide *)

Lemma termfv_exp_open_exp_wrt_exp_rec_upper_mutual :
(forall e1 e2 n1,
  termfv_exp (open_exp_wrt_exp_rec n1 e2 e1) [<=] termfv_exp e2 `union` termfv_exp e1).
Proof.
apply_mutual_ind exp_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

(* begin hide *)

Lemma termfv_exp_open_exp_wrt_exp_rec_upper :
forall e1 e2 n1,
  termfv_exp (open_exp_wrt_exp_rec n1 e2 e1) [<=] termfv_exp e2 `union` termfv_exp e1.
Proof.
pose proof termfv_exp_open_exp_wrt_exp_rec_upper_mutual as H; intuition eauto.
Qed.

Hint Resolve termfv_exp_open_exp_wrt_exp_rec_upper : lngen.

(* end hide *)

Lemma typefv_typ_open_typ_wrt_typ_upper :
forall A1 A2,
  typefv_typ (open_typ_wrt_typ A1 A2) [<=] typefv_typ A2 `union` typefv_typ A1.
Proof.
unfold open_typ_wrt_typ; default_simp.
Qed.

Hint Resolve typefv_typ_open_typ_wrt_typ_upper : lngen.

Lemma typefv_exp_open_exp_wrt_typ_upper :
forall e1 A1,
  typefv_exp (open_exp_wrt_typ e1 A1) [<=] typefv_typ A1 `union` typefv_exp e1.
Proof.
unfold open_exp_wrt_typ; default_simp.
Qed.

Hint Resolve typefv_exp_open_exp_wrt_typ_upper : lngen.

Lemma typefv_exp_open_exp_wrt_exp_upper :
forall e1 e2,
  typefv_exp (open_exp_wrt_exp e1 e2) [<=] typefv_exp e2 `union` typefv_exp e1.
Proof.
unfold open_exp_wrt_exp; default_simp.
Qed.

Hint Resolve typefv_exp_open_exp_wrt_exp_upper : lngen.

Lemma termfv_exp_open_exp_wrt_typ_upper :
forall e1 A1,
  termfv_exp (open_exp_wrt_typ e1 A1) [<=] termfv_exp e1.
Proof.
unfold open_exp_wrt_typ; default_simp.
Qed.

Hint Resolve termfv_exp_open_exp_wrt_typ_upper : lngen.

Lemma termfv_exp_open_exp_wrt_exp_upper :
forall e1 e2,
  termfv_exp (open_exp_wrt_exp e1 e2) [<=] termfv_exp e2 `union` termfv_exp e1.
Proof.
unfold open_exp_wrt_exp; default_simp.
Qed.

Hint Resolve termfv_exp_open_exp_wrt_exp_upper : lngen.

(* begin hide *)

Lemma typefv_typ_typsubst_typ_fresh_mutual :
(forall A1 A2 X1,
  X1 `notin` typefv_typ A1 ->
  typefv_typ (typsubst_typ A2 X1 A1) [=] typefv_typ A1).
Proof.
apply_mutual_ind typ_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

Lemma typefv_typ_typsubst_typ_fresh :
forall A1 A2 X1,
  X1 `notin` typefv_typ A1 ->
  typefv_typ (typsubst_typ A2 X1 A1) [=] typefv_typ A1.
Proof.
pose proof typefv_typ_typsubst_typ_fresh_mutual as H; intuition eauto.
Qed.

Hint Resolve typefv_typ_typsubst_typ_fresh : lngen.
Hint Rewrite typefv_typ_typsubst_typ_fresh using solve [auto] : lngen.

(* begin hide *)

Lemma typefv_exp_typsubst_exp_fresh_mutual :
(forall e1 A1 X1,
  X1 `notin` typefv_exp e1 ->
  typefv_exp (typsubst_exp A1 X1 e1) [=] typefv_exp e1).
Proof.
apply_mutual_ind exp_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

Lemma typefv_exp_typsubst_exp_fresh :
forall e1 A1 X1,
  X1 `notin` typefv_exp e1 ->
  typefv_exp (typsubst_exp A1 X1 e1) [=] typefv_exp e1.
Proof.
pose proof typefv_exp_typsubst_exp_fresh_mutual as H; intuition eauto.
Qed.

Hint Resolve typefv_exp_typsubst_exp_fresh : lngen.
Hint Rewrite typefv_exp_typsubst_exp_fresh using solve [auto] : lngen.

(* begin hide *)

Lemma typefv_exp_subst_exp_fresh_mutual :
(forall e1 A1 X1,
  termfv_exp (typsubst_exp A1 X1 e1) [=] termfv_exp e1).
Proof.
apply_mutual_ind exp_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

Lemma typefv_exp_subst_exp_fresh :
forall e1 A1 X1,
  termfv_exp (typsubst_exp A1 X1 e1) [=] termfv_exp e1.
Proof.
pose proof typefv_exp_subst_exp_fresh_mutual as H; intuition eauto.
Qed.

Hint Resolve typefv_exp_subst_exp_fresh : lngen.
Hint Rewrite typefv_exp_subst_exp_fresh using solve [auto] : lngen.

(* begin hide *)

Lemma termfv_exp_subst_exp_fresh_mutual :
(forall e1 e2 x1,
  x1 `notin` termfv_exp e1 ->
  termfv_exp (subst_exp e2 x1 e1) [=] termfv_exp e1).
Proof.
apply_mutual_ind exp_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

Lemma termfv_exp_subst_exp_fresh :
forall e1 e2 x1,
  x1 `notin` termfv_exp e1 ->
  termfv_exp (subst_exp e2 x1 e1) [=] termfv_exp e1.
Proof.
pose proof termfv_exp_subst_exp_fresh_mutual as H; intuition eauto.
Qed.

Hint Resolve termfv_exp_subst_exp_fresh : lngen.
Hint Rewrite termfv_exp_subst_exp_fresh using solve [auto] : lngen.

(* begin hide *)

Lemma typefv_typ_typsubst_typ_lower_mutual :
(forall A1 A2 X1,
  remove X1 (typefv_typ A1) [<=] typefv_typ (typsubst_typ A2 X1 A1)).
Proof.
apply_mutual_ind typ_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

Lemma typefv_typ_typsubst_typ_lower :
forall A1 A2 X1,
  remove X1 (typefv_typ A1) [<=] typefv_typ (typsubst_typ A2 X1 A1).
Proof.
pose proof typefv_typ_typsubst_typ_lower_mutual as H; intuition eauto.
Qed.

Hint Resolve typefv_typ_typsubst_typ_lower : lngen.

(* begin hide *)

Lemma typefv_exp_typsubst_exp_lower_mutual :
(forall e1 A1 X1,
  remove X1 (typefv_exp e1) [<=] typefv_exp (typsubst_exp A1 X1 e1)).
Proof.
apply_mutual_ind exp_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

Lemma typefv_exp_typsubst_exp_lower :
forall e1 A1 X1,
  remove X1 (typefv_exp e1) [<=] typefv_exp (typsubst_exp A1 X1 e1).
Proof.
pose proof typefv_exp_typsubst_exp_lower_mutual as H; intuition eauto.
Qed.

Hint Resolve typefv_exp_typsubst_exp_lower : lngen.

(* begin hide *)

Lemma typefv_exp_subst_exp_lower_mutual :
(forall e1 e2 x1,
  typefv_exp e1 [<=] typefv_exp (subst_exp e2 x1 e1)).
Proof.
apply_mutual_ind exp_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

Lemma typefv_exp_subst_exp_lower :
forall e1 e2 x1,
  typefv_exp e1 [<=] typefv_exp (subst_exp e2 x1 e1).
Proof.
pose proof typefv_exp_subst_exp_lower_mutual as H; intuition eauto.
Qed.

Hint Resolve typefv_exp_subst_exp_lower : lngen.

(* begin hide *)

Lemma termfv_exp_typsubst_exp_lower_mutual :
(forall e1 A1 X1,
  termfv_exp e1 [<=] termfv_exp (typsubst_exp A1 X1 e1)).
Proof.
apply_mutual_ind exp_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

Lemma termfv_exp_typsubst_exp_lower :
forall e1 A1 X1,
  termfv_exp e1 [<=] termfv_exp (typsubst_exp A1 X1 e1).
Proof.
pose proof termfv_exp_typsubst_exp_lower_mutual as H; intuition eauto.
Qed.

Hint Resolve termfv_exp_typsubst_exp_lower : lngen.

(* begin hide *)

Lemma termfv_exp_subst_exp_lower_mutual :
(forall e1 e2 x1,
  remove x1 (termfv_exp e1) [<=] termfv_exp (subst_exp e2 x1 e1)).
Proof.
apply_mutual_ind exp_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

Lemma termfv_exp_subst_exp_lower :
forall e1 e2 x1,
  remove x1 (termfv_exp e1) [<=] termfv_exp (subst_exp e2 x1 e1).
Proof.
pose proof termfv_exp_subst_exp_lower_mutual as H; intuition eauto.
Qed.

Hint Resolve termfv_exp_subst_exp_lower : lngen.

(* begin hide *)

Lemma typefv_typ_typsubst_typ_notin_mutual :
(forall A1 A2 X1 X2,
  X2 `notin` typefv_typ A1 ->
  X2 `notin` typefv_typ A2 ->
  X2 `notin` typefv_typ (typsubst_typ A2 X1 A1)).
Proof.
apply_mutual_ind typ_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

Lemma typefv_typ_typsubst_typ_notin :
forall A1 A2 X1 X2,
  X2 `notin` typefv_typ A1 ->
  X2 `notin` typefv_typ A2 ->
  X2 `notin` typefv_typ (typsubst_typ A2 X1 A1).
Proof.
pose proof typefv_typ_typsubst_typ_notin_mutual as H; intuition eauto.
Qed.

Hint Resolve typefv_typ_typsubst_typ_notin : lngen.

(* begin hide *)

Lemma typefv_exp_typsubst_exp_notin_mutual :
(forall e1 A1 X1 X2,
  X2 `notin` typefv_exp e1 ->
  X2 `notin` typefv_typ A1 ->
  X2 `notin` typefv_exp (typsubst_exp A1 X1 e1)).
Proof.
apply_mutual_ind exp_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

Lemma typefv_exp_typsubst_exp_notin :
forall e1 A1 X1 X2,
  X2 `notin` typefv_exp e1 ->
  X2 `notin` typefv_typ A1 ->
  X2 `notin` typefv_exp (typsubst_exp A1 X1 e1).
Proof.
pose proof typefv_exp_typsubst_exp_notin_mutual as H; intuition eauto.
Qed.

Hint Resolve typefv_exp_typsubst_exp_notin : lngen.

(* begin hide *)

Lemma typefv_exp_subst_exp_notin_mutual :
(forall e1 e2 x1 X1,
  X1 `notin` typefv_exp e1 ->
  X1 `notin` typefv_exp e2 ->
  X1 `notin` typefv_exp (subst_exp e2 x1 e1)).
Proof.
apply_mutual_ind exp_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

Lemma typefv_exp_subst_exp_notin :
forall e1 e2 x1 X1,
  X1 `notin` typefv_exp e1 ->
  X1 `notin` typefv_exp e2 ->
  X1 `notin` typefv_exp (subst_exp e2 x1 e1).
Proof.
pose proof typefv_exp_subst_exp_notin_mutual as H; intuition eauto.
Qed.

Hint Resolve typefv_exp_subst_exp_notin : lngen.

(* begin hide *)

Lemma termfv_exp_typsubst_exp_notin_mutual :
(forall e1 A1 X1 x1,
  x1 `notin` termfv_exp e1 ->
  x1 `notin` termfv_exp (typsubst_exp A1 X1 e1)).
Proof.
apply_mutual_ind exp_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

Lemma termfv_exp_typsubst_exp_notin :
forall e1 A1 X1 x1,
  x1 `notin` termfv_exp e1 ->
  x1 `notin` termfv_exp (typsubst_exp A1 X1 e1).
Proof.
pose proof termfv_exp_typsubst_exp_notin_mutual as H; intuition eauto.
Qed.

Hint Resolve termfv_exp_typsubst_exp_notin : lngen.

(* begin hide *)

Lemma termfv_exp_subst_exp_notin_mutual :
(forall e1 e2 x1 x2,
  x2 `notin` termfv_exp e1 ->
  x2 `notin` termfv_exp e2 ->
  x2 `notin` termfv_exp (subst_exp e2 x1 e1)).
Proof.
apply_mutual_ind exp_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

Lemma termfv_exp_subst_exp_notin :
forall e1 e2 x1 x2,
  x2 `notin` termfv_exp e1 ->
  x2 `notin` termfv_exp e2 ->
  x2 `notin` termfv_exp (subst_exp e2 x1 e1).
Proof.
pose proof termfv_exp_subst_exp_notin_mutual as H; intuition eauto.
Qed.

Hint Resolve termfv_exp_subst_exp_notin : lngen.

(* begin hide *)

Lemma typefv_typ_typsubst_typ_upper_mutual :
(forall A1 A2 X1,
  typefv_typ (typsubst_typ A2 X1 A1) [<=] typefv_typ A2 `union` remove X1 (typefv_typ A1)).
Proof.
apply_mutual_ind typ_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

Lemma typefv_typ_typsubst_typ_upper :
forall A1 A2 X1,
  typefv_typ (typsubst_typ A2 X1 A1) [<=] typefv_typ A2 `union` remove X1 (typefv_typ A1).
Proof.
pose proof typefv_typ_typsubst_typ_upper_mutual as H; intuition eauto.
Qed.

Hint Resolve typefv_typ_typsubst_typ_upper : lngen.

(* begin hide *)

Lemma typefv_exp_typsubst_exp_upper_mutual :
(forall e1 A1 X1,
  typefv_exp (typsubst_exp A1 X1 e1) [<=] typefv_typ A1 `union` remove X1 (typefv_exp e1)).
Proof.
apply_mutual_ind exp_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

Lemma typefv_exp_typsubst_exp_upper :
forall e1 A1 X1,
  typefv_exp (typsubst_exp A1 X1 e1) [<=] typefv_typ A1 `union` remove X1 (typefv_exp e1).
Proof.
pose proof typefv_exp_typsubst_exp_upper_mutual as H; intuition eauto.
Qed.

Hint Resolve typefv_exp_typsubst_exp_upper : lngen.

(* begin hide *)

Lemma typefv_exp_subst_exp_upper_mutual :
(forall e1 e2 x1,
  typefv_exp (subst_exp e2 x1 e1) [<=] typefv_exp e2 `union` typefv_exp e1).
Proof.
apply_mutual_ind exp_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

Lemma typefv_exp_subst_exp_upper :
forall e1 e2 x1,
  typefv_exp (subst_exp e2 x1 e1) [<=] typefv_exp e2 `union` typefv_exp e1.
Proof.
pose proof typefv_exp_subst_exp_upper_mutual as H; intuition eauto.
Qed.

Hint Resolve typefv_exp_subst_exp_upper : lngen.

(* begin hide *)

Lemma termfv_exp_typsubst_exp_upper_mutual :
(forall e1 A1 X1,
  termfv_exp (typsubst_exp A1 X1 e1) [<=] termfv_exp e1).
Proof.
apply_mutual_ind exp_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

Lemma termfv_exp_typsubst_exp_upper :
forall e1 A1 X1,
  termfv_exp (typsubst_exp A1 X1 e1) [<=] termfv_exp e1.
Proof.
pose proof termfv_exp_typsubst_exp_upper_mutual as H; intuition eauto.
Qed.

Hint Resolve termfv_exp_typsubst_exp_upper : lngen.

(* begin hide *)

Lemma termfv_exp_subst_exp_upper_mutual :
(forall e1 e2 x1,
  termfv_exp (subst_exp e2 x1 e1) [<=] termfv_exp e2 `union` remove x1 (termfv_exp e1)).
Proof.
apply_mutual_ind exp_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

Lemma termfv_exp_subst_exp_upper :
forall e1 e2 x1,
  termfv_exp (subst_exp e2 x1 e1) [<=] termfv_exp e2 `union` remove x1 (termfv_exp e1).
Proof.
pose proof termfv_exp_subst_exp_upper_mutual as H; intuition eauto.
Qed.

Hint Resolve termfv_exp_subst_exp_upper : lngen.


(* *********************************************************************** *)
(** * Theorems about [subst] *)

Ltac default_auto ::= auto with lngen brute_force; tauto.
Ltac default_autorewrite ::= autorewrite with lngen.

(* begin hide *)

Lemma typsubst_typ_close_typ_wrt_typ_rec_mutual :
(forall A2 A1 X1 X2 n1,
  degree_typ_wrt_typ n1 A1 ->
  X1 <> X2 ->
  X2 `notin` typefv_typ A1 ->
  typsubst_typ A1 X1 (close_typ_wrt_typ_rec n1 X2 A2) = close_typ_wrt_typ_rec n1 X2 (typsubst_typ A1 X1 A2)).
Proof.
apply_mutual_ind typ_mutind;
default_simp.
Qed.

(* end hide *)

Lemma typsubst_typ_close_typ_wrt_typ_rec :
forall A2 A1 X1 X2 n1,
  degree_typ_wrt_typ n1 A1 ->
  X1 <> X2 ->
  X2 `notin` typefv_typ A1 ->
  typsubst_typ A1 X1 (close_typ_wrt_typ_rec n1 X2 A2) = close_typ_wrt_typ_rec n1 X2 (typsubst_typ A1 X1 A2).
Proof.
pose proof typsubst_typ_close_typ_wrt_typ_rec_mutual as H; intuition eauto.
Qed.

Hint Resolve typsubst_typ_close_typ_wrt_typ_rec : lngen.

(* begin hide *)

Lemma typsubst_exp_close_exp_wrt_typ_rec_mutual :
(forall e1 A1 X1 X2 n1,
  degree_typ_wrt_typ n1 A1 ->
  X1 <> X2 ->
  X2 `notin` typefv_typ A1 ->
  typsubst_exp A1 X1 (close_exp_wrt_typ_rec n1 X2 e1) = close_exp_wrt_typ_rec n1 X2 (typsubst_exp A1 X1 e1)).
Proof.
apply_mutual_ind exp_mutind;
default_simp.
Qed.

(* end hide *)

Lemma typsubst_exp_close_exp_wrt_typ_rec :
forall e1 A1 X1 X2 n1,
  degree_typ_wrt_typ n1 A1 ->
  X1 <> X2 ->
  X2 `notin` typefv_typ A1 ->
  typsubst_exp A1 X1 (close_exp_wrt_typ_rec n1 X2 e1) = close_exp_wrt_typ_rec n1 X2 (typsubst_exp A1 X1 e1).
Proof.
pose proof typsubst_exp_close_exp_wrt_typ_rec_mutual as H; intuition eauto.
Qed.

Hint Resolve typsubst_exp_close_exp_wrt_typ_rec : lngen.

(* begin hide *)

Lemma typsubst_exp_close_exp_wrt_exp_rec_mutual :
(forall e1 A1 x1 X1 n1,
  typsubst_exp A1 x1 (close_exp_wrt_exp_rec n1 X1 e1) = close_exp_wrt_exp_rec n1 X1 (typsubst_exp A1 x1 e1)).
Proof.
apply_mutual_ind exp_mutind;
default_simp.
Qed.

(* end hide *)

Lemma typsubst_exp_close_exp_wrt_exp_rec :
forall e1 A1 x1 X1 n1,
  typsubst_exp A1 x1 (close_exp_wrt_exp_rec n1 X1 e1) = close_exp_wrt_exp_rec n1 X1 (typsubst_exp A1 x1 e1).
Proof.
pose proof typsubst_exp_close_exp_wrt_exp_rec_mutual as H; intuition eauto.
Qed.

Hint Resolve typsubst_exp_close_exp_wrt_exp_rec : lngen.

(* begin hide *)

Lemma subst_exp_close_exp_wrt_typ_rec_mutual :
(forall e2 e1 X1 x1 n1,
  degree_exp_wrt_typ n1 e1 ->
  x1 `notin` typefv_exp e1 ->
  subst_exp e1 X1 (close_exp_wrt_typ_rec n1 x1 e2) = close_exp_wrt_typ_rec n1 x1 (subst_exp e1 X1 e2)).
Proof.
apply_mutual_ind exp_mutind;
default_simp.
Qed.

(* end hide *)

Lemma subst_exp_close_exp_wrt_typ_rec :
forall e2 e1 X1 x1 n1,
  degree_exp_wrt_typ n1 e1 ->
  x1 `notin` typefv_exp e1 ->
  subst_exp e1 X1 (close_exp_wrt_typ_rec n1 x1 e2) = close_exp_wrt_typ_rec n1 x1 (subst_exp e1 X1 e2).
Proof.
pose proof subst_exp_close_exp_wrt_typ_rec_mutual as H; intuition eauto.
Qed.

Hint Resolve subst_exp_close_exp_wrt_typ_rec : lngen.

(* begin hide *)

Lemma subst_exp_close_exp_wrt_exp_rec_mutual :
(forall e2 e1 x1 x2 n1,
  degree_exp_wrt_exp n1 e1 ->
  x1 <> x2 ->
  x2 `notin` termfv_exp e1 ->
  subst_exp e1 x1 (close_exp_wrt_exp_rec n1 x2 e2) = close_exp_wrt_exp_rec n1 x2 (subst_exp e1 x1 e2)).
Proof.
apply_mutual_ind exp_mutind;
default_simp.
Qed.

(* end hide *)

Lemma subst_exp_close_exp_wrt_exp_rec :
forall e2 e1 x1 x2 n1,
  degree_exp_wrt_exp n1 e1 ->
  x1 <> x2 ->
  x2 `notin` termfv_exp e1 ->
  subst_exp e1 x1 (close_exp_wrt_exp_rec n1 x2 e2) = close_exp_wrt_exp_rec n1 x2 (subst_exp e1 x1 e2).
Proof.
pose proof subst_exp_close_exp_wrt_exp_rec_mutual as H; intuition eauto.
Qed.

Hint Resolve subst_exp_close_exp_wrt_exp_rec : lngen.

Lemma typsubst_typ_close_typ_wrt_typ :
forall A2 A1 X1 X2,
  lc_typ A1 ->  X1 <> X2 ->
  X2 `notin` typefv_typ A1 ->
  typsubst_typ A1 X1 (close_typ_wrt_typ X2 A2) = close_typ_wrt_typ X2 (typsubst_typ A1 X1 A2).
Proof.
unfold close_typ_wrt_typ; default_simp.
Qed.

Hint Resolve typsubst_typ_close_typ_wrt_typ : lngen.

Lemma typsubst_exp_close_exp_wrt_typ :
forall e1 A1 X1 X2,
  lc_typ A1 ->  X1 <> X2 ->
  X2 `notin` typefv_typ A1 ->
  typsubst_exp A1 X1 (close_exp_wrt_typ X2 e1) = close_exp_wrt_typ X2 (typsubst_exp A1 X1 e1).
Proof.
unfold close_exp_wrt_typ; default_simp.
Qed.

Hint Resolve typsubst_exp_close_exp_wrt_typ : lngen.

Lemma typsubst_exp_close_exp_wrt_exp :
forall e1 A1 x1 X1,
  lc_typ A1 ->  typsubst_exp A1 x1 (close_exp_wrt_exp X1 e1) = close_exp_wrt_exp X1 (typsubst_exp A1 x1 e1).
Proof.
unfold close_exp_wrt_exp; default_simp.
Qed.

Hint Resolve typsubst_exp_close_exp_wrt_exp : lngen.

Lemma subst_exp_close_exp_wrt_typ :
forall e2 e1 X1 x1,
  lc_exp e1 ->  x1 `notin` typefv_exp e1 ->
  subst_exp e1 X1 (close_exp_wrt_typ x1 e2) = close_exp_wrt_typ x1 (subst_exp e1 X1 e2).
Proof.
unfold close_exp_wrt_typ; default_simp.
Qed.

Hint Resolve subst_exp_close_exp_wrt_typ : lngen.

Lemma subst_exp_close_exp_wrt_exp :
forall e2 e1 x1 x2,
  lc_exp e1 ->  x1 <> x2 ->
  x2 `notin` termfv_exp e1 ->
  subst_exp e1 x1 (close_exp_wrt_exp x2 e2) = close_exp_wrt_exp x2 (subst_exp e1 x1 e2).
Proof.
unfold close_exp_wrt_exp; default_simp.
Qed.

Hint Resolve subst_exp_close_exp_wrt_exp : lngen.

(* begin hide *)

Lemma typsubst_typ_degree_typ_wrt_typ_mutual :
(forall A1 A2 X1 n1,
  degree_typ_wrt_typ n1 A1 ->
  degree_typ_wrt_typ n1 A2 ->
  degree_typ_wrt_typ n1 (typsubst_typ A2 X1 A1)).
Proof.
apply_mutual_ind typ_mutind;
default_simp.
Qed.

(* end hide *)

Lemma typsubst_typ_degree_typ_wrt_typ :
forall A1 A2 X1 n1,
  degree_typ_wrt_typ n1 A1 ->
  degree_typ_wrt_typ n1 A2 ->
  degree_typ_wrt_typ n1 (typsubst_typ A2 X1 A1).
Proof.
pose proof typsubst_typ_degree_typ_wrt_typ_mutual as H; intuition eauto.
Qed.

Hint Resolve typsubst_typ_degree_typ_wrt_typ : lngen.

(* begin hide *)

Lemma typsubst_exp_degree_exp_wrt_typ_mutual :
(forall e1 A1 X1 n1,
  degree_exp_wrt_typ n1 e1 ->
  degree_typ_wrt_typ n1 A1 ->
  degree_exp_wrt_typ n1 (typsubst_exp A1 X1 e1)).
Proof.
apply_mutual_ind exp_mutind;
default_simp.
Qed.

(* end hide *)

Lemma typsubst_exp_degree_exp_wrt_typ :
forall e1 A1 X1 n1,
  degree_exp_wrt_typ n1 e1 ->
  degree_typ_wrt_typ n1 A1 ->
  degree_exp_wrt_typ n1 (typsubst_exp A1 X1 e1).
Proof.
pose proof typsubst_exp_degree_exp_wrt_typ_mutual as H; intuition eauto.
Qed.

Hint Resolve typsubst_exp_degree_exp_wrt_typ : lngen.

(* begin hide *)

Lemma typsubst_exp_degree_exp_wrt_exp_mutual :
(forall e1 A1 X1 n1,
  degree_exp_wrt_exp n1 e1 ->
  degree_exp_wrt_exp n1 (typsubst_exp A1 X1 e1)).
Proof.
apply_mutual_ind exp_mutind;
default_simp.
Qed.

(* end hide *)

Lemma typsubst_exp_degree_exp_wrt_exp :
forall e1 A1 X1 n1,
  degree_exp_wrt_exp n1 e1 ->
  degree_exp_wrt_exp n1 (typsubst_exp A1 X1 e1).
Proof.
pose proof typsubst_exp_degree_exp_wrt_exp_mutual as H; intuition eauto.
Qed.

Hint Resolve typsubst_exp_degree_exp_wrt_exp : lngen.

(* begin hide *)

Lemma subst_exp_degree_exp_wrt_typ_mutual :
(forall e1 e2 x1 n1,
  degree_exp_wrt_typ n1 e1 ->
  degree_exp_wrt_typ n1 e2 ->
  degree_exp_wrt_typ n1 (subst_exp e2 x1 e1)).
Proof.
apply_mutual_ind exp_mutind;
default_simp.
Qed.

(* end hide *)

Lemma subst_exp_degree_exp_wrt_typ :
forall e1 e2 x1 n1,
  degree_exp_wrt_typ n1 e1 ->
  degree_exp_wrt_typ n1 e2 ->
  degree_exp_wrt_typ n1 (subst_exp e2 x1 e1).
Proof.
pose proof subst_exp_degree_exp_wrt_typ_mutual as H; intuition eauto.
Qed.

Hint Resolve subst_exp_degree_exp_wrt_typ : lngen.

(* begin hide *)

Lemma subst_exp_degree_exp_wrt_exp_mutual :
(forall e1 e2 x1 n1,
  degree_exp_wrt_exp n1 e1 ->
  degree_exp_wrt_exp n1 e2 ->
  degree_exp_wrt_exp n1 (subst_exp e2 x1 e1)).
Proof.
apply_mutual_ind exp_mutind;
default_simp.
Qed.

(* end hide *)

Lemma subst_exp_degree_exp_wrt_exp :
forall e1 e2 x1 n1,
  degree_exp_wrt_exp n1 e1 ->
  degree_exp_wrt_exp n1 e2 ->
  degree_exp_wrt_exp n1 (subst_exp e2 x1 e1).
Proof.
pose proof subst_exp_degree_exp_wrt_exp_mutual as H; intuition eauto.
Qed.

Hint Resolve subst_exp_degree_exp_wrt_exp : lngen.

(* begin hide *)

Lemma typsubst_typ_fresh_eq_mutual :
(forall A2 A1 X1,
  X1 `notin` typefv_typ A2 ->
  typsubst_typ A1 X1 A2 = A2).
Proof.
apply_mutual_ind typ_mutind;
default_simp.
Qed.

(* end hide *)

Lemma typsubst_typ_fresh_eq :
forall A2 A1 X1,
  X1 `notin` typefv_typ A2 ->
  typsubst_typ A1 X1 A2 = A2.
Proof.
pose proof typsubst_typ_fresh_eq_mutual as H; intuition eauto.
Qed.

Hint Resolve typsubst_typ_fresh_eq : lngen.
Hint Rewrite typsubst_typ_fresh_eq using solve [auto] : lngen.

(* begin hide *)

Lemma typsubst_exp_fresh_eq_mutual :
(forall e1 A1 X1,
  X1 `notin` typefv_exp e1 ->
  typsubst_exp A1 X1 e1 = e1).
Proof.
apply_mutual_ind exp_mutind;
default_simp.
Qed.

(* end hide *)

Lemma typsubst_exp_fresh_eq :
forall e1 A1 X1,
  X1 `notin` typefv_exp e1 ->
  typsubst_exp A1 X1 e1 = e1.
Proof.
pose proof typsubst_exp_fresh_eq_mutual as H; intuition eauto.
Qed.

Hint Resolve typsubst_exp_fresh_eq : lngen.
Hint Rewrite typsubst_exp_fresh_eq using solve [auto] : lngen.

(* begin hide *)

Lemma subst_exp_fresh_eq_mutual :
(forall e2 e1 x1,
  x1 `notin` termfv_exp e2 ->
  subst_exp e1 x1 e2 = e2).
Proof.
apply_mutual_ind exp_mutind;
default_simp.
Qed.

(* end hide *)

Lemma subst_exp_fresh_eq :
forall e2 e1 x1,
  x1 `notin` termfv_exp e2 ->
  subst_exp e1 x1 e2 = e2.
Proof.
pose proof subst_exp_fresh_eq_mutual as H; intuition eauto.
Qed.

Hint Resolve subst_exp_fresh_eq : lngen.
Hint Rewrite subst_exp_fresh_eq using solve [auto] : lngen.

(* begin hide *)

Lemma typsubst_typ_fresh_same_mutual :
(forall A2 A1 X1,
  X1 `notin` typefv_typ A1 ->
  X1 `notin` typefv_typ (typsubst_typ A1 X1 A2)).
Proof.
apply_mutual_ind typ_mutind;
default_simp.
Qed.

(* end hide *)

Lemma typsubst_typ_fresh_same :
forall A2 A1 X1,
  X1 `notin` typefv_typ A1 ->
  X1 `notin` typefv_typ (typsubst_typ A1 X1 A2).
Proof.
pose proof typsubst_typ_fresh_same_mutual as H; intuition eauto.
Qed.

Hint Resolve typsubst_typ_fresh_same : lngen.

(* begin hide *)

Lemma typsubst_exp_fresh_same_mutual :
(forall e1 A1 X1,
  X1 `notin` typefv_typ A1 ->
  X1 `notin` typefv_exp (typsubst_exp A1 X1 e1)).
Proof.
apply_mutual_ind exp_mutind;
default_simp.
Qed.

(* end hide *)

Lemma typsubst_exp_fresh_same :
forall e1 A1 X1,
  X1 `notin` typefv_typ A1 ->
  X1 `notin` typefv_exp (typsubst_exp A1 X1 e1).
Proof.
pose proof typsubst_exp_fresh_same_mutual as H; intuition eauto.
Qed.

Hint Resolve typsubst_exp_fresh_same : lngen.

(* begin hide *)

Lemma subst_exp_fresh_same_mutual :
(forall e2 e1 x1,
  x1 `notin` termfv_exp e1 ->
  x1 `notin` termfv_exp (subst_exp e1 x1 e2)).
Proof.
apply_mutual_ind exp_mutind;
default_simp.
Qed.

(* end hide *)

Lemma subst_exp_fresh_same :
forall e2 e1 x1,
  x1 `notin` termfv_exp e1 ->
  x1 `notin` termfv_exp (subst_exp e1 x1 e2).
Proof.
pose proof subst_exp_fresh_same_mutual as H; intuition eauto.
Qed.

Hint Resolve subst_exp_fresh_same : lngen.

(* begin hide *)

Lemma typsubst_typ_fresh_mutual :
(forall A2 A1 X1 X2,
  X1 `notin` typefv_typ A2 ->
  X1 `notin` typefv_typ A1 ->
  X1 `notin` typefv_typ (typsubst_typ A1 X2 A2)).
Proof.
apply_mutual_ind typ_mutind;
default_simp.
Qed.

(* end hide *)

Lemma typsubst_typ_fresh :
forall A2 A1 X1 X2,
  X1 `notin` typefv_typ A2 ->
  X1 `notin` typefv_typ A1 ->
  X1 `notin` typefv_typ (typsubst_typ A1 X2 A2).
Proof.
pose proof typsubst_typ_fresh_mutual as H; intuition eauto.
Qed.

Hint Resolve typsubst_typ_fresh : lngen.

(* begin hide *)

Lemma typsubst_exp_fresh_mutual :
(forall e1 A1 X1 X2,
  X1 `notin` typefv_exp e1 ->
  X1 `notin` typefv_typ A1 ->
  X1 `notin` typefv_exp (typsubst_exp A1 X2 e1)).
Proof.
apply_mutual_ind exp_mutind;
default_simp.
Qed.

(* end hide *)

Lemma typsubst_exp_fresh :
forall e1 A1 X1 X2,
  X1 `notin` typefv_exp e1 ->
  X1 `notin` typefv_typ A1 ->
  X1 `notin` typefv_exp (typsubst_exp A1 X2 e1).
Proof.
pose proof typsubst_exp_fresh_mutual as H; intuition eauto.
Qed.

Hint Resolve typsubst_exp_fresh : lngen.

(* begin hide *)

Lemma subst_exp_fresh_mutual :
(forall e2 e1 x1 x2,
  x1 `notin` termfv_exp e2 ->
  x1 `notin` termfv_exp e1 ->
  x1 `notin` termfv_exp (subst_exp e1 x2 e2)).
Proof.
apply_mutual_ind exp_mutind;
default_simp.
Qed.

(* end hide *)

Lemma subst_exp_fresh :
forall e2 e1 x1 x2,
  x1 `notin` termfv_exp e2 ->
  x1 `notin` termfv_exp e1 ->
  x1 `notin` termfv_exp (subst_exp e1 x2 e2).
Proof.
pose proof subst_exp_fresh_mutual as H; intuition eauto.
Qed.

Hint Resolve subst_exp_fresh : lngen.

Lemma typsubst_typ_lc_typ :
forall A1 A2 X1,
  lc_typ A1 ->
  lc_typ A2 ->
  lc_typ (typsubst_typ A2 X1 A1).
Proof.
default_simp.
Qed.

Hint Resolve typsubst_typ_lc_typ : lngen.

Lemma typsubst_exp_lc_exp :
forall e1 A1 X1,
  lc_exp e1 ->
  lc_typ A1 ->
  lc_exp (typsubst_exp A1 X1 e1).
Proof.
default_simp.
Qed.

Hint Resolve typsubst_exp_lc_exp : lngen.

Lemma subst_exp_lc_exp :
forall e1 e2 x1,
  lc_exp e1 ->
  lc_exp e2 ->
  lc_exp (subst_exp e2 x1 e1).
Proof.
default_simp.
Qed.

Hint Resolve subst_exp_lc_exp : lngen.

(* begin hide *)

Lemma typsubst_typ_open_typ_wrt_typ_rec_mutual :
(forall A3 A1 A2 X1 n1,
  lc_typ A1 ->
  typsubst_typ A1 X1 (open_typ_wrt_typ_rec n1 A2 A3) = open_typ_wrt_typ_rec n1 (typsubst_typ A1 X1 A2) (typsubst_typ A1 X1 A3)).
Proof.
apply_mutual_ind typ_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma typsubst_typ_open_typ_wrt_typ_rec :
forall A3 A1 A2 X1 n1,
  lc_typ A1 ->
  typsubst_typ A1 X1 (open_typ_wrt_typ_rec n1 A2 A3) = open_typ_wrt_typ_rec n1 (typsubst_typ A1 X1 A2) (typsubst_typ A1 X1 A3).
Proof.
pose proof typsubst_typ_open_typ_wrt_typ_rec_mutual as H; intuition eauto.
Qed.

Hint Resolve typsubst_typ_open_typ_wrt_typ_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma typsubst_exp_open_exp_wrt_typ_rec_mutual :
(forall e1 A1 A2 X1 n1,
  lc_typ A1 ->
  typsubst_exp A1 X1 (open_exp_wrt_typ_rec n1 A2 e1) = open_exp_wrt_typ_rec n1 (typsubst_typ A1 X1 A2) (typsubst_exp A1 X1 e1)).
Proof.
apply_mutual_ind exp_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma typsubst_exp_open_exp_wrt_typ_rec :
forall e1 A1 A2 X1 n1,
  lc_typ A1 ->
  typsubst_exp A1 X1 (open_exp_wrt_typ_rec n1 A2 e1) = open_exp_wrt_typ_rec n1 (typsubst_typ A1 X1 A2) (typsubst_exp A1 X1 e1).
Proof.
pose proof typsubst_exp_open_exp_wrt_typ_rec_mutual as H; intuition eauto.
Qed.

Hint Resolve typsubst_exp_open_exp_wrt_typ_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma typsubst_exp_open_exp_wrt_exp_rec_mutual :
(forall e2 A1 e1 X1 n1,
  typsubst_exp A1 X1 (open_exp_wrt_exp_rec n1 e1 e2) = open_exp_wrt_exp_rec n1 (typsubst_exp A1 X1 e1) (typsubst_exp A1 X1 e2)).
Proof.
apply_mutual_ind exp_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma typsubst_exp_open_exp_wrt_exp_rec :
forall e2 A1 e1 X1 n1,
  typsubst_exp A1 X1 (open_exp_wrt_exp_rec n1 e1 e2) = open_exp_wrt_exp_rec n1 (typsubst_exp A1 X1 e1) (typsubst_exp A1 X1 e2).
Proof.
pose proof typsubst_exp_open_exp_wrt_exp_rec_mutual as H; intuition eauto.
Qed.

Hint Resolve typsubst_exp_open_exp_wrt_exp_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma subst_exp_open_exp_wrt_typ_rec_mutual :
(forall e2 e1 A1 x1 n1,
  lc_exp e1 ->
  subst_exp e1 x1 (open_exp_wrt_typ_rec n1 A1 e2) = open_exp_wrt_typ_rec n1 A1 (subst_exp e1 x1 e2)).
Proof.
apply_mutual_ind exp_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma subst_exp_open_exp_wrt_typ_rec :
forall e2 e1 A1 x1 n1,
  lc_exp e1 ->
  subst_exp e1 x1 (open_exp_wrt_typ_rec n1 A1 e2) = open_exp_wrt_typ_rec n1 A1 (subst_exp e1 x1 e2).
Proof.
pose proof subst_exp_open_exp_wrt_typ_rec_mutual as H; intuition eauto.
Qed.

Hint Resolve subst_exp_open_exp_wrt_typ_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma subst_exp_open_exp_wrt_exp_rec_mutual :
(forall e3 e1 e2 x1 n1,
  lc_exp e1 ->
  subst_exp e1 x1 (open_exp_wrt_exp_rec n1 e2 e3) = open_exp_wrt_exp_rec n1 (subst_exp e1 x1 e2) (subst_exp e1 x1 e3)).
Proof.
apply_mutual_ind exp_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma subst_exp_open_exp_wrt_exp_rec :
forall e3 e1 e2 x1 n1,
  lc_exp e1 ->
  subst_exp e1 x1 (open_exp_wrt_exp_rec n1 e2 e3) = open_exp_wrt_exp_rec n1 (subst_exp e1 x1 e2) (subst_exp e1 x1 e3).
Proof.
pose proof subst_exp_open_exp_wrt_exp_rec_mutual as H; intuition eauto.
Qed.

Hint Resolve subst_exp_open_exp_wrt_exp_rec : lngen.

(* end hide *)

Lemma typsubst_typ_open_typ_wrt_typ :
forall A3 A1 A2 X1,
  lc_typ A1 ->
  typsubst_typ A1 X1 (open_typ_wrt_typ A3 A2) = open_typ_wrt_typ (typsubst_typ A1 X1 A3) (typsubst_typ A1 X1 A2).
Proof.
unfold open_typ_wrt_typ; default_simp.
Qed.

Hint Resolve typsubst_typ_open_typ_wrt_typ : lngen.

Lemma typsubst_exp_open_exp_wrt_typ :
forall e1 A1 A2 X1,
  lc_typ A1 ->
  typsubst_exp A1 X1 (open_exp_wrt_typ e1 A2) = open_exp_wrt_typ (typsubst_exp A1 X1 e1) (typsubst_typ A1 X1 A2).
Proof.
unfold open_exp_wrt_typ; default_simp.
Qed.

Hint Resolve typsubst_exp_open_exp_wrt_typ : lngen.

Lemma typsubst_exp_open_exp_wrt_exp :
forall e2 A1 e1 X1,
  typsubst_exp A1 X1 (open_exp_wrt_exp e2 e1) = open_exp_wrt_exp (typsubst_exp A1 X1 e2) (typsubst_exp A1 X1 e1).
Proof.
unfold open_exp_wrt_exp; default_simp.
Qed.

Hint Resolve typsubst_exp_open_exp_wrt_exp : lngen.

Lemma subst_exp_open_exp_wrt_typ :
forall e2 e1 A1 x1,
  lc_exp e1 ->
  subst_exp e1 x1 (open_exp_wrt_typ e2 A1) = open_exp_wrt_typ (subst_exp e1 x1 e2) A1.
Proof.
unfold open_exp_wrt_typ; default_simp.
Qed.

Hint Resolve subst_exp_open_exp_wrt_typ : lngen.

Lemma subst_exp_open_exp_wrt_exp :
forall e3 e1 e2 x1,
  lc_exp e1 ->
  subst_exp e1 x1 (open_exp_wrt_exp e3 e2) = open_exp_wrt_exp (subst_exp e1 x1 e3) (subst_exp e1 x1 e2).
Proof.
unfold open_exp_wrt_exp; default_simp.
Qed.

Hint Resolve subst_exp_open_exp_wrt_exp : lngen.

Lemma typsubst_typ_open_typ_wrt_typ_var :
forall A2 A1 X1 X2,
  X1 <> X2 ->
  lc_typ A1 ->
  open_typ_wrt_typ (typsubst_typ A1 X1 A2) (t_tvar_f X2) = typsubst_typ A1 X1 (open_typ_wrt_typ A2 (t_tvar_f X2)).
Proof.
intros; rewrite typsubst_typ_open_typ_wrt_typ; default_simp.
Qed.

Hint Resolve typsubst_typ_open_typ_wrt_typ_var : lngen.

Lemma typsubst_exp_open_exp_wrt_typ_var :
forall e1 A1 X1 X2,
  X1 <> X2 ->
  lc_typ A1 ->
  open_exp_wrt_typ (typsubst_exp A1 X1 e1) (t_tvar_f X2) = typsubst_exp A1 X1 (open_exp_wrt_typ e1 (t_tvar_f X2)).
Proof.
intros; rewrite typsubst_exp_open_exp_wrt_typ; default_simp.
Qed.

Hint Resolve typsubst_exp_open_exp_wrt_typ_var : lngen.

Lemma typsubst_exp_open_exp_wrt_exp_var :
forall e1 A1 X1 x1,
  open_exp_wrt_exp (typsubst_exp A1 X1 e1) (e_var_f x1) = typsubst_exp A1 X1 (open_exp_wrt_exp e1 (e_var_f x1)).
Proof.
intros; rewrite typsubst_exp_open_exp_wrt_exp; default_simp.
Qed.

Hint Resolve typsubst_exp_open_exp_wrt_exp_var : lngen.

Lemma subst_exp_open_exp_wrt_typ_var :
forall e2 e1 x1 X1,
  lc_exp e1 ->
  open_exp_wrt_typ (subst_exp e1 x1 e2) (t_tvar_f X1) = subst_exp e1 x1 (open_exp_wrt_typ e2 (t_tvar_f X1)).
Proof.
intros; rewrite subst_exp_open_exp_wrt_typ; default_simp.
Qed.

Hint Resolve subst_exp_open_exp_wrt_typ_var : lngen.

Lemma subst_exp_open_exp_wrt_exp_var :
forall e2 e1 x1 x2,
  x1 <> x2 ->
  lc_exp e1 ->
  open_exp_wrt_exp (subst_exp e1 x1 e2) (e_var_f x2) = subst_exp e1 x1 (open_exp_wrt_exp e2 (e_var_f x2)).
Proof.
intros; rewrite subst_exp_open_exp_wrt_exp; default_simp.
Qed.

Hint Resolve subst_exp_open_exp_wrt_exp_var : lngen.

(* begin hide *)

Lemma typsubst_typ_spec_rec_mutual :
(forall A1 A2 X1 n1,
  typsubst_typ A2 X1 A1 = open_typ_wrt_typ_rec n1 A2 (close_typ_wrt_typ_rec n1 X1 A1)).
Proof.
apply_mutual_ind typ_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma typsubst_typ_spec_rec :
forall A1 A2 X1 n1,
  typsubst_typ A2 X1 A1 = open_typ_wrt_typ_rec n1 A2 (close_typ_wrt_typ_rec n1 X1 A1).
Proof.
pose proof typsubst_typ_spec_rec_mutual as H; intuition eauto.
Qed.

Hint Resolve typsubst_typ_spec_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma typsubst_exp_spec_rec_mutual :
(forall e1 A1 X1 n1,
  typsubst_exp A1 X1 e1 = open_exp_wrt_typ_rec n1 A1 (close_exp_wrt_typ_rec n1 X1 e1)).
Proof.
apply_mutual_ind exp_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma typsubst_exp_spec_rec :
forall e1 A1 X1 n1,
  typsubst_exp A1 X1 e1 = open_exp_wrt_typ_rec n1 A1 (close_exp_wrt_typ_rec n1 X1 e1).
Proof.
pose proof typsubst_exp_spec_rec_mutual as H; intuition eauto.
Qed.

Hint Resolve typsubst_exp_spec_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma subst_exp_spec_rec_mutual :
(forall e1 e2 x1 n1,
  subst_exp e2 x1 e1 = open_exp_wrt_exp_rec n1 e2 (close_exp_wrt_exp_rec n1 x1 e1)).
Proof.
apply_mutual_ind exp_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma subst_exp_spec_rec :
forall e1 e2 x1 n1,
  subst_exp e2 x1 e1 = open_exp_wrt_exp_rec n1 e2 (close_exp_wrt_exp_rec n1 x1 e1).
Proof.
pose proof subst_exp_spec_rec_mutual as H; intuition eauto.
Qed.

Hint Resolve subst_exp_spec_rec : lngen.

(* end hide *)

Lemma typsubst_typ_spec :
forall A1 A2 X1,
  typsubst_typ A2 X1 A1 = open_typ_wrt_typ (close_typ_wrt_typ X1 A1) A2.
Proof.
unfold close_typ_wrt_typ; unfold open_typ_wrt_typ; default_simp.
Qed.

Hint Resolve typsubst_typ_spec : lngen.

Lemma typsubst_exp_spec :
forall e1 A1 X1,
  typsubst_exp A1 X1 e1 = open_exp_wrt_typ (close_exp_wrt_typ X1 e1) A1.
Proof.
unfold close_exp_wrt_typ; unfold open_exp_wrt_typ; default_simp.
Qed.

Hint Resolve typsubst_exp_spec : lngen.

Lemma subst_exp_spec :
forall e1 e2 x1,
  subst_exp e2 x1 e1 = open_exp_wrt_exp (close_exp_wrt_exp x1 e1) e2.
Proof.
unfold close_exp_wrt_exp; unfold open_exp_wrt_exp; default_simp.
Qed.

Hint Resolve subst_exp_spec : lngen.

(* begin hide *)

Lemma typsubst_typ_typsubst_typ_mutual :
(forall A1 A2 A3 X2 X1,
  X2 `notin` typefv_typ A2 ->
  X2 <> X1 ->
  typsubst_typ A2 X1 (typsubst_typ A3 X2 A1) = typsubst_typ (typsubst_typ A2 X1 A3) X2 (typsubst_typ A2 X1 A1)).
Proof.
apply_mutual_ind typ_mutind;
default_simp.
Qed.

(* end hide *)

Lemma typsubst_typ_typsubst_typ :
forall A1 A2 A3 X2 X1,
  X2 `notin` typefv_typ A2 ->
  X2 <> X1 ->
  typsubst_typ A2 X1 (typsubst_typ A3 X2 A1) = typsubst_typ (typsubst_typ A2 X1 A3) X2 (typsubst_typ A2 X1 A1).
Proof.
pose proof typsubst_typ_typsubst_typ_mutual as H; intuition eauto.
Qed.

Hint Resolve typsubst_typ_typsubst_typ : lngen.

(* begin hide *)

Lemma typsubst_exp_typsubst_exp_mutual :
(forall e1 A1 A2 X2 X1,
  X2 `notin` typefv_typ A1 ->
  X2 <> X1 ->
  typsubst_exp A1 X1 (typsubst_exp A2 X2 e1) = typsubst_exp (typsubst_typ A1 X1 A2) X2 (typsubst_exp A1 X1 e1)).
Proof.
apply_mutual_ind exp_mutind;
default_simp.
Qed.

(* end hide *)

Lemma typsubst_exp_typsubst_exp :
forall e1 A1 A2 X2 X1,
  X2 `notin` typefv_typ A1 ->
  X2 <> X1 ->
  typsubst_exp A1 X1 (typsubst_exp A2 X2 e1) = typsubst_exp (typsubst_typ A1 X1 A2) X2 (typsubst_exp A1 X1 e1).
Proof.
pose proof typsubst_exp_typsubst_exp_mutual as H; intuition eauto.
Qed.

Hint Resolve typsubst_exp_typsubst_exp : lngen.

(* begin hide *)

Lemma typsubst_exp_subst_exp_mutual :
(forall e1 A1 e2 x1 X1,
  typsubst_exp A1 X1 (subst_exp e2 x1 e1) = subst_exp (typsubst_exp A1 X1 e2) x1 (typsubst_exp A1 X1 e1)).
Proof.
apply_mutual_ind exp_mutind;
default_simp.
Qed.

(* end hide *)

Lemma typsubst_exp_subst_exp :
forall e1 A1 e2 x1 X1,
  typsubst_exp A1 X1 (subst_exp e2 x1 e1) = subst_exp (typsubst_exp A1 X1 e2) x1 (typsubst_exp A1 X1 e1).
Proof.
pose proof typsubst_exp_subst_exp_mutual as H; intuition eauto.
Qed.

Hint Resolve typsubst_exp_subst_exp : lngen.

(* begin hide *)

Lemma subst_exp_typsubst_exp_mutual :
(forall e1 e2 A1 X1 x1,
  X1 `notin` typefv_exp e2 ->
  subst_exp e2 x1 (typsubst_exp A1 X1 e1) = typsubst_exp A1 X1 (subst_exp e2 x1 e1)).
Proof.
apply_mutual_ind exp_mutind;
default_simp.
Qed.

(* end hide *)

Lemma subst_exp_typsubst_exp :
forall e1 e2 A1 X1 x1,
  X1 `notin` typefv_exp e2 ->
  subst_exp e2 x1 (typsubst_exp A1 X1 e1) = typsubst_exp A1 X1 (subst_exp e2 x1 e1).
Proof.
pose proof subst_exp_typsubst_exp_mutual as H; intuition eauto.
Qed.

Hint Resolve subst_exp_typsubst_exp : lngen.

(* begin hide *)

Lemma subst_exp_subst_exp_mutual :
(forall e1 e2 e3 x2 x1,
  x2 `notin` termfv_exp e2 ->
  x2 <> x1 ->
  subst_exp e2 x1 (subst_exp e3 x2 e1) = subst_exp (subst_exp e2 x1 e3) x2 (subst_exp e2 x1 e1)).
Proof.
apply_mutual_ind exp_mutind;
default_simp.
Qed.

(* end hide *)

Lemma subst_exp_subst_exp :
forall e1 e2 e3 x2 x1,
  x2 `notin` termfv_exp e2 ->
  x2 <> x1 ->
  subst_exp e2 x1 (subst_exp e3 x2 e1) = subst_exp (subst_exp e2 x1 e3) x2 (subst_exp e2 x1 e1).
Proof.
pose proof subst_exp_subst_exp_mutual as H; intuition eauto.
Qed.

Hint Resolve subst_exp_subst_exp : lngen.

(* begin hide *)

Lemma typsubst_typ_close_typ_wrt_typ_rec_open_typ_wrt_typ_rec_mutual :
(forall A2 A1 X1 X2 n1,
  X2 `notin` typefv_typ A2 ->
  X2 `notin` typefv_typ A1 ->
  X2 <> X1 ->
  degree_typ_wrt_typ n1 A1 ->
  typsubst_typ A1 X1 A2 = close_typ_wrt_typ_rec n1 X2 (typsubst_typ A1 X1 (open_typ_wrt_typ_rec n1 (t_tvar_f X2) A2))).
Proof.
apply_mutual_ind typ_mutrec;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma typsubst_typ_close_typ_wrt_typ_rec_open_typ_wrt_typ_rec :
forall A2 A1 X1 X2 n1,
  X2 `notin` typefv_typ A2 ->
  X2 `notin` typefv_typ A1 ->
  X2 <> X1 ->
  degree_typ_wrt_typ n1 A1 ->
  typsubst_typ A1 X1 A2 = close_typ_wrt_typ_rec n1 X2 (typsubst_typ A1 X1 (open_typ_wrt_typ_rec n1 (t_tvar_f X2) A2)).
Proof.
pose proof typsubst_typ_close_typ_wrt_typ_rec_open_typ_wrt_typ_rec_mutual as H; intuition eauto.
Qed.

Hint Resolve typsubst_typ_close_typ_wrt_typ_rec_open_typ_wrt_typ_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma typsubst_exp_close_exp_wrt_typ_rec_open_exp_wrt_typ_rec_mutual :
(forall e1 A1 X1 X2 n1,
  X2 `notin` typefv_exp e1 ->
  X2 `notin` typefv_typ A1 ->
  X2 <> X1 ->
  degree_typ_wrt_typ n1 A1 ->
  typsubst_exp A1 X1 e1 = close_exp_wrt_typ_rec n1 X2 (typsubst_exp A1 X1 (open_exp_wrt_typ_rec n1 (t_tvar_f X2) e1))).
Proof.
apply_mutual_ind exp_mutrec;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma typsubst_exp_close_exp_wrt_typ_rec_open_exp_wrt_typ_rec :
forall e1 A1 X1 X2 n1,
  X2 `notin` typefv_exp e1 ->
  X2 `notin` typefv_typ A1 ->
  X2 <> X1 ->
  degree_typ_wrt_typ n1 A1 ->
  typsubst_exp A1 X1 e1 = close_exp_wrt_typ_rec n1 X2 (typsubst_exp A1 X1 (open_exp_wrt_typ_rec n1 (t_tvar_f X2) e1)).
Proof.
pose proof typsubst_exp_close_exp_wrt_typ_rec_open_exp_wrt_typ_rec_mutual as H; intuition eauto.
Qed.

Hint Resolve typsubst_exp_close_exp_wrt_typ_rec_open_exp_wrt_typ_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma typsubst_exp_close_exp_wrt_exp_rec_open_exp_wrt_exp_rec_mutual :
(forall e1 A1 X1 x1 n1,
  x1 `notin` termfv_exp e1 ->
  typsubst_exp A1 X1 e1 = close_exp_wrt_exp_rec n1 x1 (typsubst_exp A1 X1 (open_exp_wrt_exp_rec n1 (e_var_f x1) e1))).
Proof.
apply_mutual_ind exp_mutrec;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma typsubst_exp_close_exp_wrt_exp_rec_open_exp_wrt_exp_rec :
forall e1 A1 X1 x1 n1,
  x1 `notin` termfv_exp e1 ->
  typsubst_exp A1 X1 e1 = close_exp_wrt_exp_rec n1 x1 (typsubst_exp A1 X1 (open_exp_wrt_exp_rec n1 (e_var_f x1) e1)).
Proof.
pose proof typsubst_exp_close_exp_wrt_exp_rec_open_exp_wrt_exp_rec_mutual as H; intuition eauto.
Qed.

Hint Resolve typsubst_exp_close_exp_wrt_exp_rec_open_exp_wrt_exp_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma subst_exp_close_exp_wrt_typ_rec_open_exp_wrt_typ_rec_mutual :
(forall e2 e1 x1 X1 n1,
  X1 `notin` typefv_exp e2 ->
  X1 `notin` typefv_exp e1 ->
  degree_exp_wrt_typ n1 e1 ->
  subst_exp e1 x1 e2 = close_exp_wrt_typ_rec n1 X1 (subst_exp e1 x1 (open_exp_wrt_typ_rec n1 (t_tvar_f X1) e2))).
Proof.
apply_mutual_ind exp_mutrec;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma subst_exp_close_exp_wrt_typ_rec_open_exp_wrt_typ_rec :
forall e2 e1 x1 X1 n1,
  X1 `notin` typefv_exp e2 ->
  X1 `notin` typefv_exp e1 ->
  degree_exp_wrt_typ n1 e1 ->
  subst_exp e1 x1 e2 = close_exp_wrt_typ_rec n1 X1 (subst_exp e1 x1 (open_exp_wrt_typ_rec n1 (t_tvar_f X1) e2)).
Proof.
pose proof subst_exp_close_exp_wrt_typ_rec_open_exp_wrt_typ_rec_mutual as H; intuition eauto.
Qed.

Hint Resolve subst_exp_close_exp_wrt_typ_rec_open_exp_wrt_typ_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma subst_exp_close_exp_wrt_exp_rec_open_exp_wrt_exp_rec_mutual :
(forall e2 e1 x1 x2 n1,
  x2 `notin` termfv_exp e2 ->
  x2 `notin` termfv_exp e1 ->
  x2 <> x1 ->
  degree_exp_wrt_exp n1 e1 ->
  subst_exp e1 x1 e2 = close_exp_wrt_exp_rec n1 x2 (subst_exp e1 x1 (open_exp_wrt_exp_rec n1 (e_var_f x2) e2))).
Proof.
apply_mutual_ind exp_mutrec;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma subst_exp_close_exp_wrt_exp_rec_open_exp_wrt_exp_rec :
forall e2 e1 x1 x2 n1,
  x2 `notin` termfv_exp e2 ->
  x2 `notin` termfv_exp e1 ->
  x2 <> x1 ->
  degree_exp_wrt_exp n1 e1 ->
  subst_exp e1 x1 e2 = close_exp_wrt_exp_rec n1 x2 (subst_exp e1 x1 (open_exp_wrt_exp_rec n1 (e_var_f x2) e2)).
Proof.
pose proof subst_exp_close_exp_wrt_exp_rec_open_exp_wrt_exp_rec_mutual as H; intuition eauto.
Qed.

Hint Resolve subst_exp_close_exp_wrt_exp_rec_open_exp_wrt_exp_rec : lngen.

(* end hide *)

Lemma typsubst_typ_close_typ_wrt_typ_open_typ_wrt_typ :
forall A2 A1 X1 X2,
  X2 `notin` typefv_typ A2 ->
  X2 `notin` typefv_typ A1 ->
  X2 <> X1 ->
  lc_typ A1 ->
  typsubst_typ A1 X1 A2 = close_typ_wrt_typ X2 (typsubst_typ A1 X1 (open_typ_wrt_typ A2 (t_tvar_f X2))).
Proof.
unfold close_typ_wrt_typ; unfold open_typ_wrt_typ; default_simp.
Qed.

Hint Resolve typsubst_typ_close_typ_wrt_typ_open_typ_wrt_typ : lngen.

Lemma typsubst_exp_close_exp_wrt_typ_open_exp_wrt_typ :
forall e1 A1 X1 X2,
  X2 `notin` typefv_exp e1 ->
  X2 `notin` typefv_typ A1 ->
  X2 <> X1 ->
  lc_typ A1 ->
  typsubst_exp A1 X1 e1 = close_exp_wrt_typ X2 (typsubst_exp A1 X1 (open_exp_wrt_typ e1 (t_tvar_f X2))).
Proof.
unfold close_exp_wrt_typ; unfold open_exp_wrt_typ; default_simp.
Qed.

Hint Resolve typsubst_exp_close_exp_wrt_typ_open_exp_wrt_typ : lngen.

Lemma typsubst_exp_close_exp_wrt_exp_open_exp_wrt_exp :
forall e1 A1 X1 x1,
  x1 `notin` termfv_exp e1 ->
  lc_typ A1 ->
  typsubst_exp A1 X1 e1 = close_exp_wrt_exp x1 (typsubst_exp A1 X1 (open_exp_wrt_exp e1 (e_var_f x1))).
Proof.
unfold close_exp_wrt_exp; unfold open_exp_wrt_exp; default_simp.
Qed.

Hint Resolve typsubst_exp_close_exp_wrt_exp_open_exp_wrt_exp : lngen.

Lemma subst_exp_close_exp_wrt_typ_open_exp_wrt_typ :
forall e2 e1 x1 X1,
  X1 `notin` typefv_exp e2 ->
  X1 `notin` typefv_exp e1 ->
  lc_exp e1 ->
  subst_exp e1 x1 e2 = close_exp_wrt_typ X1 (subst_exp e1 x1 (open_exp_wrt_typ e2 (t_tvar_f X1))).
Proof.
unfold close_exp_wrt_typ; unfold open_exp_wrt_typ; default_simp.
Qed.

Hint Resolve subst_exp_close_exp_wrt_typ_open_exp_wrt_typ : lngen.

Lemma subst_exp_close_exp_wrt_exp_open_exp_wrt_exp :
forall e2 e1 x1 x2,
  x2 `notin` termfv_exp e2 ->
  x2 `notin` termfv_exp e1 ->
  x2 <> x1 ->
  lc_exp e1 ->
  subst_exp e1 x1 e2 = close_exp_wrt_exp x2 (subst_exp e1 x1 (open_exp_wrt_exp e2 (e_var_f x2))).
Proof.
unfold close_exp_wrt_exp; unfold open_exp_wrt_exp; default_simp.
Qed.

Hint Resolve subst_exp_close_exp_wrt_exp_open_exp_wrt_exp : lngen.

Lemma typsubst_typ_t_forall :
forall X2 A2 B1 A1 X1,
  lc_typ A1 ->
  X2 `notin` typefv_typ A1 `union` typefv_typ B1 `union` singleton X1 ->
  typsubst_typ A1 X1 (t_forall A2 B1) = t_forall (typsubst_typ A1 X1 A2) (close_typ_wrt_typ X2 (typsubst_typ A1 X1 (open_typ_wrt_typ B1 (t_tvar_f X2)))).
Proof.
default_simp.
Qed.

Hint Resolve typsubst_typ_t_forall : lngen.

Lemma typsubst_exp_e_abs :
forall x1 A2 e1 A1 X1,
  lc_typ A1 ->
  x1 `notin` termfv_exp e1 ->
  typsubst_exp A1 X1 (e_abs A2 e1) = e_abs (typsubst_typ A1 X1 A2) (close_exp_wrt_exp x1 (typsubst_exp A1 X1 (open_exp_wrt_exp e1 (e_var_f x1)))).
Proof.
default_simp.
Qed.

Hint Resolve typsubst_exp_e_abs : lngen.

Lemma typsubst_exp_e_fixpoint :
forall x1 A2 e1 A1 X1,
  lc_typ A1 ->
  x1 `notin` termfv_exp e1 ->
  typsubst_exp A1 X1 (e_fixpoint A2 e1) = e_fixpoint (typsubst_typ A1 X1 A2) (close_exp_wrt_exp x1 (typsubst_exp A1 X1 (open_exp_wrt_exp e1 (e_var_f x1)))).
Proof.
default_simp.
Qed.

Hint Resolve typsubst_exp_e_fixpoint : lngen.

Lemma typsubst_exp_e_tabs :
forall X2 e1 A1 X1,
  lc_typ A1 ->
  X2 `notin` typefv_typ A1 `union` typefv_exp e1 `union` singleton X1 ->
  typsubst_exp A1 X1 (e_tabs e1) = e_tabs (close_exp_wrt_typ X2 (typsubst_exp A1 X1 (open_exp_wrt_typ e1 (t_tvar_f X2)))).
Proof.
default_simp.
Qed.

Hint Resolve typsubst_exp_e_tabs : lngen.

Lemma subst_exp_e_abs :
forall x2 A1 e2 e1 x1,
  lc_exp e1 ->
  x2 `notin` termfv_exp e1 `union` termfv_exp e2 `union` singleton x1 ->
  subst_exp e1 x1 (e_abs A1 e2) = e_abs (A1) (close_exp_wrt_exp x2 (subst_exp e1 x1 (open_exp_wrt_exp e2 (e_var_f x2)))).
Proof.
default_simp.
Qed.

Hint Resolve subst_exp_e_abs : lngen.

Lemma subst_exp_e_fixpoint :
forall x2 A1 e2 e1 x1,
  lc_exp e1 ->
  x2 `notin` termfv_exp e1 `union` termfv_exp e2 `union` singleton x1 ->
  subst_exp e1 x1 (e_fixpoint A1 e2) = e_fixpoint (A1) (close_exp_wrt_exp x2 (subst_exp e1 x1 (open_exp_wrt_exp e2 (e_var_f x2)))).
Proof.
default_simp.
Qed.

Hint Resolve subst_exp_e_fixpoint : lngen.

Lemma subst_exp_e_tabs :
forall X1 e2 e1 x1,
  lc_exp e1 ->
  X1 `notin` typefv_exp e1 `union` typefv_exp e2 ->
  subst_exp e1 x1 (e_tabs e2) = e_tabs (close_exp_wrt_typ X1 (subst_exp e1 x1 (open_exp_wrt_typ e2 (t_tvar_f X1)))).
Proof.
default_simp.
Qed.

Hint Resolve subst_exp_e_tabs : lngen.

(* begin hide *)

Lemma typsubst_typ_intro_rec_mutual :
(forall A1 X1 A2 n1,
  X1 `notin` typefv_typ A1 ->
  open_typ_wrt_typ_rec n1 A2 A1 = typsubst_typ A2 X1 (open_typ_wrt_typ_rec n1 (t_tvar_f X1) A1)).
Proof.
apply_mutual_ind typ_mutind;
default_simp.
Qed.

(* end hide *)

Lemma typsubst_typ_intro_rec :
forall A1 X1 A2 n1,
  X1 `notin` typefv_typ A1 ->
  open_typ_wrt_typ_rec n1 A2 A1 = typsubst_typ A2 X1 (open_typ_wrt_typ_rec n1 (t_tvar_f X1) A1).
Proof.
pose proof typsubst_typ_intro_rec_mutual as H; intuition eauto.
Qed.

Hint Resolve typsubst_typ_intro_rec : lngen.
Hint Rewrite typsubst_typ_intro_rec using solve [auto] : lngen.

(* begin hide *)

Lemma typsubst_exp_intro_rec_mutual :
(forall e1 X1 A1 n1,
  X1 `notin` typefv_exp e1 ->
  open_exp_wrt_typ_rec n1 A1 e1 = typsubst_exp A1 X1 (open_exp_wrt_typ_rec n1 (t_tvar_f X1) e1)).
Proof.
apply_mutual_ind exp_mutind;
default_simp.
Qed.

(* end hide *)

Lemma typsubst_exp_intro_rec :
forall e1 X1 A1 n1,
  X1 `notin` typefv_exp e1 ->
  open_exp_wrt_typ_rec n1 A1 e1 = typsubst_exp A1 X1 (open_exp_wrt_typ_rec n1 (t_tvar_f X1) e1).
Proof.
pose proof typsubst_exp_intro_rec_mutual as H; intuition eauto.
Qed.

Hint Resolve typsubst_exp_intro_rec : lngen.
Hint Rewrite typsubst_exp_intro_rec using solve [auto] : lngen.

(* begin hide *)

Lemma subst_exp_intro_rec_mutual :
(forall e1 x1 e2 n1,
  x1 `notin` termfv_exp e1 ->
  open_exp_wrt_exp_rec n1 e2 e1 = subst_exp e2 x1 (open_exp_wrt_exp_rec n1 (e_var_f x1) e1)).
Proof.
apply_mutual_ind exp_mutind;
default_simp.
Qed.

(* end hide *)

Lemma subst_exp_intro_rec :
forall e1 x1 e2 n1,
  x1 `notin` termfv_exp e1 ->
  open_exp_wrt_exp_rec n1 e2 e1 = subst_exp e2 x1 (open_exp_wrt_exp_rec n1 (e_var_f x1) e1).
Proof.
pose proof subst_exp_intro_rec_mutual as H; intuition eauto.
Qed.

Hint Resolve subst_exp_intro_rec : lngen.
Hint Rewrite subst_exp_intro_rec using solve [auto] : lngen.

Lemma typsubst_typ_intro :
forall X1 A1 A2,
  X1 `notin` typefv_typ A1 ->
  open_typ_wrt_typ A1 A2 = typsubst_typ A2 X1 (open_typ_wrt_typ A1 (t_tvar_f X1)).
Proof.
unfold open_typ_wrt_typ; default_simp.
Qed.

Hint Resolve typsubst_typ_intro : lngen.

Lemma typsubst_exp_intro :
forall X1 e1 A1,
  X1 `notin` typefv_exp e1 ->
  open_exp_wrt_typ e1 A1 = typsubst_exp A1 X1 (open_exp_wrt_typ e1 (t_tvar_f X1)).
Proof.
unfold open_exp_wrt_typ; default_simp.
Qed.

Hint Resolve typsubst_exp_intro : lngen.

Lemma subst_exp_intro :
forall x1 e1 e2,
  x1 `notin` termfv_exp e1 ->
  open_exp_wrt_exp e1 e2 = subst_exp e2 x1 (open_exp_wrt_exp e1 (e_var_f x1)).
Proof.
unfold open_exp_wrt_exp; default_simp.
Qed.

Hint Resolve subst_exp_intro : lngen.


(* *********************************************************************** *)
(** * "Restore" tactics *)

Ltac default_auto ::= auto; tauto.
Ltac default_autorewrite ::= fail.
