(* The primary expressions and postfixes the printer writes, each parsed by the
   rule that should take it and by no earlier alternative of the ordered choice
   in [_primary] (a binding, a destructuring, a function, a record, a name). *)

From Stdlib Require Import String List.
Import ListNotations.
Require Import Goat.GoatGrammar.
Require Import Goat.GoatPeg.
Require Import Goat.GoatPegTac.
Require Import Goat.GoatDen.
Require Import Goat.GoatPrint.
Require Import Goat.GoatPrintChain.
Open Scope string_scope.
Open Scope list_scope.

(* What an expression's parse needs: it stops before anything that can follow. *)
Definition ExprParses (b : list tree) : Prop :=
  forall r, StopE r ->
    peg (E_rule R_expr) (flats b ++ r) (Ok [Node R_expr b] r).

Ltac plain_head :=
  simpl; repeat split; intro; match goal with H : _ = _ |- _ => discriminate H end.

Lemma prim_name : forall x, PrimOK [ident x].
Proof.
  intros x r Hne.
  assert (Hnd : NotDecl (TName x :: r))
    by (destruct r as [| [? | ? | | ?] ?]; simpl in *; exact I || exact Hne).
  flat_simp. refine (conj _ (conj _ _)).
  - exact I.
  - exact Hnd.
  - pok ltac:(eapply notdecl_fail; exact Hnd).
Qed.

Lemma prim_number : forall n, PrimOK [Node R_number [Leaf (TNum n)]].
Proof.
  intros n r Hne. flat_simp. refine (conj _ (conj _ _)).
  - exact I.
  - exact I.
  - pok nope.
Qed.

Lemma prim_true : PrimOK [Node R_boolean [Node R_true_lit [sym "true"]]].
Proof.
  intros r Hne. flat_simp. refine (conj _ (conj _ _)).
  - plain_head.
  - exact I.
  - pok nope.
Qed.

Lemma prim_false : PrimOK [Node R_boolean [Node R_false_lit [sym "false"]]].
Proof.
  intros r Hne. flat_simp. refine (conj _ (conj _ _)).
  - plain_head.
  - exact I.
  - pok nope.
Qed.

Lemma prim_function : forall P b,
  ExprParses b -> PrimOK [function_tree P b].
Proof.
  intros P b Hb r Hne. unfold function_tree. flat_simp. rewrite <- ?app_assoc. refine (conj _ (conj _ _)).
  - plain_head.
  - exact I.
  - pok ltac:(eapply Hb; constructor).
Qed.

Lemma prim_paren : forall b, ExprParses b -> PrimOK (paren_kids b).
Proof.
  intros b Hb r Hne. unfold paren_kids. flat_simp. rewrite <- ?app_assoc. refine (conj _ (conj _ _)).
  - plain_head.
  - exact I.
  - pok ltac:(eapply Hb; constructor).
Qed.

Lemma post_access : forall l, PostOK (access_tree l).
Proof.
  intros l. split.
  - intros r. unfold access_tree. flat_simp. simpl. discriminate.
  - intros r. unfold access_tree. flat_simp. pok nope.
Qed.

Lemma post_call : forall b, ExprParses b -> PostOK (call_tree b).
Proof.
  intros b Hb. split.
  - intros r. unfold call_tree. flat_simp. simpl. discriminate.
  - intros r. unfold call_tree. flat_simp. rewrite <- ?app_assoc. pok ltac:(eapply Hb; constructor).
Qed.
