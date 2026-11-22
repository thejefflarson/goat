(* Spike for docs/design/w-recursive-types-plan.md, option B.  Not part of proofs/.

   The hardest lemma of making Algorithm W infer a mu by tying a knot.  When
   W unifies a variable [x] with a type [T] that mentions [x], the checker's
   [tie_ty_knot] solves [x := mu v. T[x := v]].  In the calculus that is
   [x := typ_Mu (abs_typ x 0 T)].  The lemmas below say the solution is right
   in the iso-recursive sense: the two sides of the equation [x = T] differ by
   exactly one unrolling, so one [fold] (or [unfold]) in the elaborated term
   makes the derivation go through.

     abs_lc            abstracting an atom keeps a type locally closed (one
                       binder deeper)
     open_abs          unrolling the abstracted body at the knot is the
                       substitution [x := knot] (the hardest lemma)
     knot_unrolls      the corollary at the top: open 0 knot B = s T
     abs_gd            a guarded mention of [x] becomes a guarded index, so
                       [guarded B] holds when every mention of [x] is guarded
     knot_fold_types / knot_unfold_types
                       the instances of T_Fold and T_Unfold the elaboration
                       inserts, against master's real typing rules
     abs_no_x          the abstracted body no longer mentions [x] (the
                       checker's [!occurs(x, &body)])

   0 admits.  Only the type-variable knot is covered.  The row knot
   ([tie_row_knot]) abstracts a *mention* of a row variable (a record or
   variant type with a given prefix), not an atom; its lemma is the same shape
   with [abs_mention] in place of [abs_typ] and is not written here. *)

Require Import Metalib.Metatheory.
Require Import Goat.Goat_ott.
Require Import Goat.GoatRows.
Require Import Goat.GoatDefs.
Require Import Goat.GoatMu.
Require Import Stdlib.Arith.Compare_dec.
From Stdlib Require Import Lia.

(* Replace the free atom [x] by the index [k], going one binder deeper under
   each mu, as [plug] does in checker/src/infer.rs. *)
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
  end
with abs_row (x : typvar) (k : nat) (R : row) {struct R} : row :=
  match R with
  | row_Empty => row_Empty
  | row_Var r => row_Var r
  | row_Ext l T R' => row_Ext l (abs_typ x k T) (abs_row x k R')
  end.

(* The substitution that replaces [x] by [U] and leaves everything else. *)
Definition sub1 (x : typvar) (U : typ) : tsub :=
  fun a => if Atom.eq_dec a x then U else typ_Var a.

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

(* The hardest lemma.  [U] is closed, so it needs no shifting when it lands
   under a binder; [T] has no index at or above [k], so the only index the
   opening finds is the one [abs_typ] put there. *)
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
  - rewrite H, H0; auto.
Qed.

Lemma open_abs : forall x U T k, lct 0 U -> lct k T ->
  open_typ k U (abs_typ x k T) = ap_typ (sub1 x U) idr T.
Proof. intros. apply (proj1 (open_abs_mut x U H)); auto. Qed.

Definition knot (x : typvar) (T : typ) : typ := typ_Mu (abs_typ x 0 T).

Lemma knot_lc : forall x T, lct 0 T -> lct 0 (knot x T).
Proof. intros. unfold knot. simpl. apply abs_lc. auto. Qed.

(* The solution [x := knot x T] makes [x] and [T] differ by one unrolling:
   the unrolling of what it gives [x] is what it gives [T]. *)
Theorem knot_unrolls : forall x T, lct 0 T ->
  open_typ 0 (knot x T) (abs_typ x 0 T) = ap_typ (sub1 x (knot x T)) idr T.
Proof. intros. apply open_abs; [ apply knot_lc | ]; auto. Qed.

Lemma sub1_x : forall x U, sub1 x U x = U.
Proof. intros. unfold sub1. destruct (Atom.eq_dec x x); [ reflexivity | congruence ]. Qed.

(* A mention of [x] is guarded when it sits under a record field and a
   function type, the same two flags as [gd]. *)
Fixpoint gdv (r f : bool) (x : typvar) (T : typ) {struct T} : Prop :=
  match T with
  | typ_Int | typ_Float | typ_Bool | typ_Unit | typ_String | typ_Bvar _ => True
  | typ_Arrow A B => gdv r true x A /\ gdv r true x B
  | typ_Record R => gdvr true f x R
  | typ_Var a => a = x -> r = true /\ f = true
  | typ_Mu B => gdv r f x B
  end
with gdvr (r f : bool) (x : typvar) (R : row) {struct R} : Prop :=
  match R with
  | row_Empty | row_Var _ => True
  | row_Ext _ T R' => gdv r f x T /\ gdvr r f x R'
  end.

Lemma abs_gd_mut : forall x,
  (forall T r f k, lct k T -> gdv r f x T -> gd r f k (abs_typ x k T)) /\
  (forall R r f k, lcr k R -> gdvr r f x R -> gdr r f k (abs_row x k R)).
Proof.
  intros x. apply typ_row_mutind; simpl; intros;
    repeat match goal with H : _ /\ _ |- _ => destruct H end;
    try split; eauto;
    try match goal with |- context [Atom.eq_dec ?a ?b] => destruct (Atom.eq_dec a b) end;
    simpl; eauto; try (exfalso; lia).
Qed.

Theorem abs_guarded : forall x T, lct 0 T -> gdv false false x T ->
  guarded (abs_typ x 0 T).
Proof. intros. apply (proj1 (abs_gd_mut x)); auto. Qed.

(* The abstracted body no longer mentions [x]. *)
Lemma abs_no_x_mut : forall x,
  (forall T k, ~ x `in` ftv_typ (abs_typ x k T)) /\
  (forall R k, ~ x `in` ftv_row (abs_row x k R)).
Proof.
  intros x. apply typ_row_mutind; simpl; intros;
    try match goal with |- context [Atom.eq_dec ?a ?b] => destruct (Atom.eq_dec a b) end;
    simpl;
    try (intros Hin; apply AtomSetImpl.singleton_1 in Hin; congruence);
    try (try pose proof (H k); try pose proof (H0 k); fsetdec);
    try (pose proof (H (S k)); fsetdec);
    try fsetdec.
Qed.

Theorem abs_no_x : forall x T, ~ x `in` ftv_typ (abs_typ x 0 T).
Proof. intros. apply (proj1 (abs_no_x_mut x)). Qed.

(* The coercions the elaboration inserts, against the real rules.  If the
   knot's body is guarded, a term of [T[x := knot]] folds to the knot, and a
   term of the knot unfolds to [T[x := knot]]. *)
Theorem knot_fold_types : forall D G e x T,
  lct 0 T -> gdv false false x T ->
  typing D G e (ap_typ (sub1 x (knot x T)) idr T) ->
  typing D G (e_fold e) (sub1 x (knot x T) x).
Proof.
  intros D G e x T Hlc Hg Hty. rewrite sub1_x.
  pose proof (knot_unrolls x T Hlc) as E. pose proof (knot_lc x T Hlc) as Hk.
  unfold knot in *.
  apply T_Fold; [ exact Hk | apply abs_guarded; auto | ].
  rewrite E. exact Hty.
Qed.

Theorem knot_unfold_types : forall D G e x T,
  lct 0 T -> gdv false false x T ->
  typing D G e (sub1 x (knot x T) x) ->
  typing D G (e_unfold e) (ap_typ (sub1 x (knot x T)) idr T).
Proof.
  intros D G e x T Hlc Hg Hty. rewrite sub1_x in Hty.
  pose proof (knot_unrolls x T Hlc) as E. pose proof (knot_lc x T Hlc) as Hk.
  unfold knot in *.
  rewrite <- E.
  apply T_Unfold; [ exact Hk | apply abs_guarded; auto | exact Hty ].
Qed.

Print Assumptions knot_fold_types.
Print Assumptions knot_unfold_types.
Print Assumptions abs_no_x.
