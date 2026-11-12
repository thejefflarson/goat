(* The labels the printed tree mentions, in order, are the labels of the term:
   the label table that T1 builds from the parse tree is the first-occurrence
   table of the term's labels. *)

From Coq Require Import String List.
Import ListNotations.
Require Import Goat.Goat_ott.
Require Import Goat.GoatProofs.
Require Import Goat.GoatGrammar.
Require Import Goat.GoatPeg.
Require Import Goat.GoatDen.
Require Import Goat.GoatParse.
Require Import Goat.GoatPrint.
Open Scope string_scope.
Open Scope list_scope.

Definition occs (ts : list tree) : list string := flat_map label_occurrences ts.

Definition lo_head (r : rule) (cs : list tree) : list string :=
  match r, cs with
  | R_access, [_; Node _ [Leaf (TName l)]] => [l]
  | R_take, [_; Node _ [Leaf (TName l)]] => [l]
  | R_field, Node _ [Leaf (TName l)] :: _ => [l]
  | _, _ => []
  end.

Lemma lo_node : forall r cs, label_occurrences (Node r cs) = lo_head r cs ++ occs cs.
Proof.
  intros r cs. reflexivity.
Qed.

Lemma lo_leaf : forall k, label_occurrences (Leaf k) = [].
Proof. reflexivity. Qed.

Lemma occs_nil : occs [] = [].
Proof. reflexivity. Qed.

Lemma occs_cons : forall t ts, occs (t :: ts) = label_occurrences t ++ occs ts.
Proof. reflexivity. Qed.

Lemma occs_app : forall a b, occs (a ++ b) = occs a ++ occs b.
Proof. intros a b. unfold occs. apply flat_map_app. Qed.

Arguments occs : simpl never.
Arguments label_occurrences : simpl never.

Ltac occ_simp :=
  (try unfold ident, sym);
  repeat (progress rewrite ?lo_node, ?lo_leaf, ?occs_nil, ?occs_cons, ?occs_app);
  cbn [lo_head app]; rewrite ?List.app_nil_l, ?List.app_nil_r.

Lemma occs_block :
  (forall e P, occs (block P e) = List.map lname (lbls e)) /\
  (forall fs P, occs (field_trees P fs) = List.map lname (lbls_fields fs)
                /\ occs (more_field_trees P fs) = List.map lname (lbls_fields fs)).
Proof.
  apply exp_fields_mutind.
  - intros i P. cbn [block]. occ_simp. reflexivity.
  - intros y P. reflexivity.
  - intros n P. cbn [block]. occ_simp. reflexivity.
  - intros P. cbn [block]. occ_simp. reflexivity.
  - intros P. cbn [block]. occ_simp. reflexivity.
  - intros b IH P. cbn [block lbls]. unfold function_tree. occ_simp. exact (IH (S P)).
  - intros f IHf a IHa P. cbn [block lbls]. rewrite occs_app, List.map_app.
    unfold call_tree. occ_simp. rewrite IHa.
    destruct f; cbn [as_callee as_operand]; first
      [ unfold paren_kids; occ_simp; try rewrite IHf; reflexivity
      | rewrite IHf; reflexivity ].
  - intros v IHv b IHb P. cbn [block lbls]. unfold decl_tree.
    rewrite List.map_app. occ_simp.
    rewrite IHb.
    destruct v; cbn [as_value]; first
      [ unfold paren_kids; occ_simp; try rewrite IHv; reflexivity | rewrite IHv; reflexivity ].
  - intros fs IH P. cbn [block lbls]. occ_simp.
    exact (proj1 (IH P)).
  - intros f IH l P. cbn [block lbls]. rewrite occs_app, List.map_app.
    unfold access_tree. occ_simp.
    destruct f; cbn [as_operand]; first
      [ unfold paren_kids; occ_simp; try rewrite IH; reflexivity | rewrite IH; reflexivity ].
  - intros P. split; reflexivity.
  - intros l e IHe rest IHrest P. destruct (IHrest P) as [IHf IHm].
    cbn [field_trees more_field_trees lbls_fields]. unfold field_tree.
    split.
    + rewrite occs_cons. occ_simp. rewrite IHe, IHm. cbn [List.map]. rewrite List.map_app. reflexivity.
    + rewrite occs_cons. occ_simp. rewrite IHe, IHm. cbn [List.map]. rewrite List.map_app. reflexivity.
Qed.

Lemma labels_print : forall e,
  labels (print_tree e) = nub_from [] (List.map lname (lbls e)).
Proof.
  intros e. unfold labels, print_tree. f_equal.
  occ_simp. exact (proj1 occs_block e 0).
Qed.
