(* Completeness of algorithm W, stage 7.8b: canonical representatives of a
   conversion class (docs/design/phase7-proof-plan.md).

   The field of an absent entry is free: [req_absf] makes [l ^ Bool : T ; R]
   and [l ^ Bool : T' ; R] equal for every [T] and [T'].  A type [teq] to a type
   [T] can therefore mention atoms [T] does not, all of them inside absent
   fields, and a bound on the atoms of [T] bounds only the atoms of the
   canonical representative [erT T], which replaces the field of each absent
   entry by [Unit].  The atoms of [erT T] are a conversion invariant
   ([er_inv]), which is what lets the extension a step invents be bounded by
   the atoms of the substitution it extends.

   Axiom- and admit-free. *)

Require Import Metalib.Metatheory.
Require Import Goat.Goat_ott.
Require Import Goat.GoatRows.
Require Import Goat.GoatDefs.

Fixpoint erT (T : typ) {struct T} : typ :=
  match T with
  | typ_Arrow A B => typ_Arrow (erT A) (erT B)
  | typ_Record R => typ_Record (erR R)
  | typ_Mu B => typ_Mu (erT B)
  | typ_Grp w A => typ_Grp w (erT A)
  | _ => T
  end
with erR (R : row) {struct R} : row :=
  match R with
  | row_Ext l T R' => row_Ext l (erT T) (erR R')
  | row_Maybe l P T R' =>
      if is_abs P then row_Maybe l P typ_Unit (erR R') else row_Maybe l (erT P) (erT T) (erR R')
  | _ => R
  end.

Lemma abs_is_bool : forall P, is_abs P = true -> P = typ_Bool.
Proof. intros P H. destruct P; cbn in H; try discriminate. reflexivity. Qed.

(* The canonical representative is in the class. *)
Lemma er_teq : (forall T, teq (erT T) T) /\ (forall R, req (erR R) R).
Proof.
  apply typ_row_mutind; cbn [erT erR].
  - apply teq_refl.
  - apply teq_refl.
  - apply teq_refl.
  - apply teq_refl.
  - apply teq_refl.
  - intros A IHA B IHB. apply teq_arrow; assumption.
  - intros R IH. apply teq_rec; assumption.
  - intros a. apply teq_refl.
  - intros i. apply teq_refl.
  - intros B IH. apply teq_mu; assumption.
  - intros w A IH. apply teq_grp; assumption.
  - apply req_refl.
  - intros r. apply req_refl.
  - intros l T IHT R IHR. apply req_head; assumption.
  - intros l P IHP T IHT R IHR. destruct (is_abs P) eqn:E.
    + apply abs_is_bool in E. subst P.
      eapply req_trans; [ apply req_absf with (T' := T) | ].
      apply req_maybe; [ apply teq_refl | apply teq_refl | assumption ].
    + apply req_maybe; assumption.
Qed.

(* It mentions no atom the type does not. *)
Lemma er_sub : (forall T, ftv_typ (erT T) [<=] ftv_typ T /\ frv_typ (erT T) [<=] frv_typ T) /\
               (forall R, ftv_row (erR R) [<=] ftv_row R /\ frv_row (erR R) [<=] frv_row R).
Proof.
  apply typ_row_mutind; cbn [erT erR ftv_typ frv_typ ftv_row frv_row];
    try (intros; repeat match goal with H : _ /\ _ |- _ => destruct H end; split; fsetdec; fail).
  intros l P IHP T IHT R IHR. destruct (is_abs P) eqn:E; cbn [ftv_typ frv_typ ftv_row frv_row];
    repeat match goal with H : _ /\ _ |- _ => destruct H end; split; fsetdec.
Qed.

Lemma er_not_abs : forall P, is_abs P = false -> is_abs (erT P) = false.
Proof. intros P H. destruct P; cbn in *; try reflexivity; discriminate. Qed.

Definition ErEq (A B : typ) : Prop :=
  ftv_typ (erT A) [=] ftv_typ (erT B) /\ frv_typ (erT A) [=] frv_typ (erT B).

Definition ErEqR (A B : row) : Prop :=
  ftv_row (erR A) [=] ftv_row (erR B) /\ frv_row (erR A) [=] frv_row (erR B).

(* Conversion preserves the atoms of the canonical representative. *)
Lemma er_inv : (forall A B, teq A B -> ErEq A B) /\ (forall A B, req A B -> ErEqR A B).
Proof.
  apply teq_req_mutind; unfold ErEq, ErEqR; cbn [erT erR ftv_typ frv_typ ftv_row frv_row is_abs];
    try (intros; repeat match goal with H : _ /\ _ |- _ => destruct H end; split; fsetdec; fail).
  - (* req_maybe *)
    intros l T1 T2 R T1' T2' R' H1 IH1 H2 IH2 H3 IH3.
    repeat match goal with H : _ /\ _ |- _ => destruct H end.
    pose proof (teq_is_abs _ _ H1) as Ha. rewrite <- Ha.
    destruct (is_abs T1) eqn:E.
    + apply abs_is_bool in E. subst T1. assert (E' : is_abs T1' = true) by (rewrite <- Ha; reflexivity).
      apply abs_is_bool in E'. subst T1'. cbn [ftv_typ frv_typ ftv_row frv_row]. split; fsetdec.
    + cbn [ftv_typ frv_typ ftv_row frv_row]. split; fsetdec.
  - (* req_swap_em *)
    intros l T1 T l' T' R Hne.
    destruct (is_abs T1) eqn:E.
    + apply abs_is_bool in E. subst T1. cbn [ftv_typ frv_typ ftv_row frv_row]. split; fsetdec.
    + cbn [ftv_typ frv_typ ftv_row frv_row]. split; fsetdec.
  - (* req_swap_mm *)
    intros l T1 T l' T1' T' R Hne.
    destruct (is_abs T1) eqn:E; destruct (is_abs T1') eqn:E'; cbn [ftv_typ frv_typ ftv_row frv_row].
    + apply abs_is_bool in E. apply abs_is_bool in E'. subst T1 T1'. cbn [ftv_typ frv_typ]. split; fsetdec.
    + apply abs_is_bool in E. subst T1. cbn [ftv_typ frv_typ]. split; fsetdec.
    + apply abs_is_bool in E'. subst T1'. cbn [ftv_typ frv_typ]. split; fsetdec.
    + split; fsetdec.
Qed.
