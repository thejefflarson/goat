(* Tying a knot (phase 5, stage 4, part 3; docs/design/w-recursive-types-plan.md).
   When the unifier meets a variable [x] and a type [T] that mentions [x], the
   checker solves [x := mu v. T[x := v]].  In the calculus that is
   [x := knot x T], and [abs_typ x 0 T] is the body: [x] replaced by the index
   of the new binder.

   The solution makes [x] and [T] differ by one unrolling ([knot_unrolls]),
   so the unifier's equation [x = T] holds up to [unroll_eq] with a budget of
   one ([knot_unroll_eq]), and a single [fold] or [unfold] in the elaborated
   term repairs it ([knot_chain_fold], [knot_chain_unfold]).  [gdb] decides
   the guard the checker requires of a knot, and [gdb_abs_guarded] says the
   body it builds is [guarded], which [T_Fold] and [T_Unfold] ask. *)

Require Import Metalib.Metatheory.
Require Import Goat.Goat_ott.
Require Import Goat.GoatRows.
Require Import Goat.GoatDefs.
Require Import Goat.GoatMu.
Require Import Goat.GoatElab.
Require Import Stdlib.Arith.Compare_dec.
Require Import Stdlib.Lists.List.
Import ListNotations.
From Stdlib Require Import Lia.

(* ---- abstracting an atom ---- *)

(* Replace the free atom [x] by the index [k], one binder deeper under each
   mu. *)
Fixpoint abs_typ (x : typvar) (k : nat) (T : typ) {struct T} : typ :=
  match T with
  | typ_Int => typ_Int
  | typ_Float => typ_Float
  | typ_Bool => typ_Bool
  | typ_Unit => typ_Unit
  | typ_String => typ_String
  | typ_Arrow A B => typ_Arrow (abs_typ x k A) (abs_typ x k B)
  | typ_Record R => typ_Record (abs_row x k R)
  | typ_Var a => if Atom.eq_dec a x then typ_Bvar k else typ_Var a
  | typ_Bvar n => typ_Bvar n
  | typ_Mu B => typ_Mu (abs_typ x (S k) B)
  | typ_Grp w A => typ_Grp w (abs_typ x k A)
  end
with abs_row (x : typvar) (k : nat) (R : row) {struct R} : row :=
  match R with
  | row_Empty => row_Empty
  | row_Var r => row_Var r
  | row_Ext l T R' => row_Ext l (abs_typ x k T) (abs_row x k R')
  | row_Maybe l P T R' => row_Maybe l (abs_typ x k P) (abs_typ x k T) (abs_row x k R')
  end.

(* The substitution that replaces [x] by [U] and leaves every other type
   variable. *)
Definition sub1 (x : typvar) (U : typ) : tsub :=
  fun a => if Atom.eq_dec a x then U else typ_Var a.

Lemma sub1_x : forall x U, sub1 x U x = U.
Proof. intros. unfold sub1. destruct (Atom.eq_dec x x); [ reflexivity | congruence ]. Qed.

Lemma abs_lc_mut : forall x,
  (forall T k, lct k T -> lct (S k) (abs_typ x k T)) /\
  (forall R k, lcr k R -> lcr (S k) (abs_row x k R)).
Proof.
  intros x. apply typ_row_mutind; simpl; intros;
    repeat match goal with H : _ /\ _ |- _ => destruct H end;
    try split; auto;
    try match goal with |- context [Atom.eq_dec ?a ?b] => destruct (Atom.eq_dec a b) end;
    simpl; auto; try lia.
Qed.

Lemma abs_lc : forall x T k, lct k T -> lct (S k) (abs_typ x k T).
Proof. intros. apply (proj1 (abs_lc_mut x)); auto. Qed.

(* [U] is closed, so it needs no shifting under a binder, and [T] has no index
   at or above [k], so the only index the opening finds is the one [abs_typ]
   put there. *)
Lemma open_abs_mut : forall x U, lct 0 U ->
  (forall T k, lct k T ->
     open_typ k U (abs_typ x k T) = ap_typ (sub1 x U) idr T) /\
  (forall R k, lcr k R ->
     open_row k U (abs_row x k R) = ap_row (sub1 x U) idr R).
Proof.
  intros x U HU. apply typ_row_mutind; simpl; intros;
    repeat match goal with H : _ /\ _ |- _ => destruct H end;
    try reflexivity.
  - rewrite H, H0; auto.
  - rewrite H; auto.
  - unfold sub1. destruct (Atom.eq_dec a x); simpl.
    + destruct (lt_eq_lt_dec k k) as [[?|?]|?]; [ lia | reflexivity | lia ].
    + reflexivity.
  - destruct (lt_eq_lt_dec i k) as [[?|?]|?]; [ reflexivity | lia | lia ].
  - rewrite H; auto.
  - rewrite H; auto.
  - rewrite H, H0; auto.
  - rewrite H, H0, H1; auto.
Qed.

Lemma open_abs : forall x U T k, lct 0 U -> lct k T ->
  open_typ k U (abs_typ x k T) = ap_typ (sub1 x U) idr T.
Proof. intros. apply (proj1 (open_abs_mut x U H)); auto. Qed.

Definition knot (x : typvar) (T : typ) : typ := typ_Mu (abs_typ x 0 T).

Lemma knot_lc : forall x T, lct 0 T -> lct 0 (knot x T).
Proof. intros. unfold knot. simpl. apply abs_lc. auto. Qed.

(* The unrolling of what the knot gives [x] is what it gives [T]. *)
Theorem knot_unrolls : forall x T, lct 0 T ->
  open_typ 0 (knot x T) (abs_typ x 0 T) = ap_typ (sub1 x (knot x T)) idr T.
Proof. intros. apply open_abs; [ apply knot_lc | ]; auto. Qed.

(* The abstracted body no longer mentions [x], and mentions no other atom
   that [T] did not. *)
Lemma abs_ftv_mut : forall x,
  (forall T k, ftv_typ (abs_typ x k T) [<=] AtomSetImpl.remove x (ftv_typ T)) /\
  (forall R k, ftv_row (abs_row x k R) [<=] AtomSetImpl.remove x (ftv_row R)).
Proof.
  intros x. apply typ_row_mutind; simpl; intros;
    try match goal with |- context [Atom.eq_dec ?a ?b] => destruct (Atom.eq_dec a b) end;
    simpl; try fsetdec;
    try (pose proof (H k); pose proof (H0 k); try pose proof (H1 k); fsetdec);
    try (pose proof (H (S k)); fsetdec);
    try (apply H; fail); try (apply (H (S k)); fail).
Qed.

Lemma abs_no_x : forall x T k, ~ x `in` ftv_typ (abs_typ x k T).
Proof.
  intros x T k Hin. apply (proj1 (abs_ftv_mut x) T k) in Hin. fsetdec.
Qed.

Lemma abs_ftv : forall x T k, ftv_typ (abs_typ x k T) [<=] ftv_typ T.
Proof.
  intros x T k a Ha. apply (proj1 (abs_ftv_mut x) T k) in Ha. fsetdec.
Qed.

Lemma abs_frv_mut : forall x,
  (forall T k, frv_typ (abs_typ x k T) = frv_typ T) /\
  (forall R k, frv_row (abs_row x k R) = frv_row R).
Proof.
  intros x. apply typ_row_mutind; simpl; intros;
    try match goal with |- context [Atom.eq_dec ?a ?b] => destruct (Atom.eq_dec a b) end;
    simpl; try reflexivity;
    try (rewrite H, ?H0, ?H1; reflexivity);
    try (rewrite H; reflexivity).
Qed.

Lemma abs_frv : forall x T k, frv_typ (abs_typ x k T) = frv_typ T.
Proof. intros. apply (proj1 (abs_frv_mut x)). Qed.

Lemma knot_ftv : forall x T, ftv_typ (knot x T) [<=] ftv_typ T.
Proof. intros. unfold knot. simpl. apply abs_ftv. Qed.

Lemma knot_frv : forall x T, frv_typ (knot x T) = frv_typ T.
Proof. intros. unfold knot. simpl. apply abs_frv. Qed.

(* ---- the guard ---- *)

(* [gdb r f x T] decides that every mention of [x] sits under a record field
   and a function type, mirroring [gd]. *)
Fixpoint gdb (r f : bool) (x : typvar) (T : typ) {struct T} : bool :=
  match T with
  | typ_Int | typ_Float | typ_Bool | typ_Unit | typ_String | typ_Bvar _ => true
  | typ_Arrow A B => gdb r true x A && gdb r true x B
  | typ_Record R => gdbr true f x R
  | typ_Var a => if Atom.eq_dec a x then r && f else true
  | typ_Mu B => gdb r f x B
  | typ_Grp _ A => gdb true true x A
  end
with gdbr (r f : bool) (x : typvar) (R : row) {struct R} : bool :=
  match R with
  | row_Empty | row_Var _ => true
  | row_Ext _ T R' => gdb r f x T && gdbr r f x R'
  | row_Maybe _ P T R' => gdb r f x P && (is_abs P || gdb r f x T) && gdbr r f x R'
  end.

Lemma abs_is_abs : forall x k P, is_abs (abs_typ x k P) = is_abs P.
Proof. intros x k P. destruct P; simpl; try reflexivity. destruct (Atom.eq_dec a x); reflexivity. Qed.

Lemma gdb_abs_mut : forall x,
  (forall T r f k, lct k T -> gdb r f x T = true -> gd r f k (abs_typ x k T)) /\
  (forall R r f k, lcr k R -> gdbr r f x R = true -> gdr r f k (abs_row x k R)).
Proof.
  intros x. apply typ_row_mutind; simpl; intros;
    repeat match goal with
           | H : _ /\ _ |- _ => destruct H
           | H : (_ && _) = true |- _ => apply Bool.andb_true_iff in H as [? ?]
           end;
    try exact I; try (split; eauto; fail); eauto.
  - destruct (Atom.eq_dec a x); simpl; [ | exact I ].
    intros _. apply Bool.andb_true_iff in H0 as [-> ->]. split; reflexivity.
  - exfalso. lia.
  - repeat split; eauto. rewrite abs_is_abs.
    match goal with H : (_ || _) = true |- _ => apply Bool.orb_true_iff in H as [?|?] end;
      [ left; assumption | right; eauto ].
Qed.

Theorem gdb_abs_guarded : forall x T, lct 0 T -> gdb false false x T = true ->
  guarded (abs_typ x 0 T).
Proof. intros. apply (proj1 (gdb_abs_mut x)); auto. Qed.

(* ---- the coercion a knot calls for ---- *)

Theorem knot_chain_fold : forall x T, lct 0 T -> gdb false false x T = true ->
  chain [d_fold] (ap_typ (sub1 x (knot x T)) idr T) (knot x T).
Proof.
  intros x T Hlc Hg. rewrite <- knot_unrolls by exact Hlc.
  unfold knot. apply ch_fold; [ apply knot_lc; exact Hlc | apply gdb_abs_guarded; assumption | constructor ].
Qed.

Theorem knot_chain_unfold : forall x T, lct 0 T -> gdb false false x T = true ->
  chain [d_unfold] (knot x T) (ap_typ (sub1 x (knot x T)) idr T).
Proof.
  intros x T Hlc Hg. rewrite <- knot_unrolls by exact Hlc.
  unfold knot. apply ch_unfold; [ apply knot_lc; exact Hlc | apply gdb_abs_guarded; assumption | constructor ].
Qed.

Theorem knot_unroll_eq : forall x T, lct 0 T ->
  unroll_eq 1 (knot x T) (ap_typ (sub1 x (knot x T)) idr T).
Proof.
  intros x T Hlc. rewrite <- knot_unrolls by exact Hlc.
  unfold knot. apply (UE_unfold 0).
Qed.
