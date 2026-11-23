(* The labels the printed tree mentions, in order, are the labels of the term:
   the label table that T1 builds from the parse tree is the first-occurrence
   table of the term's labels. *)

From Stdlib Require Import String List.
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

Lemma occs_as_binop : forall e b, occs (as_binop e b) = occs b.
Proof.
  intros e b. destruct e; cbn [as_binop]; try reflexivity;
    unfold paren_kids; occ_simp; reflexivity.
Qed.

Lemma occs_op : forall o, label_occurrences (op_tree o) = [].
Proof. intros o. destruct o; reflexivity. Qed.

Lemma occs_block :
  (forall e G P, occs (block G P e) = List.map lname (lbls G P e)) /\
  (forall fs, (forall G P, occs (field_trees G P fs) = List.map lname (lbls_fields G P fs)
                /\ occs (more_field_trees G P fs) = List.map lname (lbls_fields G P fs))
              /\ (forall G P i, occs (member_trees G P i fs)
                                = List.map lname (lbls_members G P fs))) /\
  (forall ars : arms, True).
Proof.
  apply exp_fields_mutind.
  - intros i G P. cbn [block]. occ_simp. reflexivity.
  - intros y G P. reflexivity.
  - intros n G P. cbn [block]. occ_simp. reflexivity.
  - intros d G P. cbn [block lbls]. occ_simp. reflexivity.
  - intros G P. cbn [block]. occ_simp. reflexivity.
  - intros G P. cbn [block]. occ_simp. reflexivity.
  - intros b IH G P. cbn [lbls].
    destruct (block_abs_cases G P b) as [(-> & E) | (_ & E)]; rewrite E.
    + unfold function_empty_tree. occ_simp. reflexivity.
    + unfold function_tree. occ_simp. exact (IH G (S P)).
  - intros f IHf a IHa G P. cbn [lbls]. rewrite List.map_app.
    assert (Hc : occs (callee_of G P f (block G P f)) = List.map lname (lbls G P f)).
    { unfold callee_of. destruct (is_group_proj G P f); [ exact (IHf G P) | ].
      destruct f; cbn [as_callee as_operand]; first
        [ unfold paren_kids; occ_simp; try rewrite IHf; reflexivity
        | rewrite IHf; reflexivity ]. }
    destruct (block_app_cases G P f a) as [(-> & E) | (_ & E)]; rewrite E; rewrite occs_app, Hc.
    + unfold call_unit_tree. occ_simp. cbn [lbls List.map]. rewrite ?List.app_nil_r. reflexivity.
    + unfold call_tree. occ_simp. rewrite IHa. reflexivity.
  - intros v IHv b IHb G P. cbn [block lbls]. unfold decl_tree, decl_named.
    rewrite List.map_app. occ_simp.
    rewrite IHb.
    destruct v; cbn [as_value]; first
      [ unfold paren_kids; occ_simp; try rewrite IHv; reflexivity | rewrite IHv; reflexivity ].
  - intros fs [IHfs IHmem] b IHb G P. cbn [block lbls].
    rewrite occs_app, List.map_app, (IHmem _ _ 0), IHb. reflexivity.
  - intros fs [IH _] G P. cbn [block lbls]. occ_simp.
    exact (proj1 (IH G P)).
  - intros f IH l G P. cbn [lbls].
    destruct (proj_level G P f) eqn:EL.
    + rewrite (block_proj_group G P f l n EL). occ_simp. reflexivity.
    + rewrite (block_proj_plain G P f l EL), occs_app, List.map_app.
      unfold access_tree. occ_simp.
      destruct f; cbn [as_operand]; first
        [ unfold paren_kids; occ_simp; try rewrite IH; reflexivity | rewrite IH; reflexivity ].
  - intros G P. cbn [block lbls]. occ_simp. reflexivity.
  - intros q G P. cbn [block lbls]. occ_simp. reflexivity.
  - intros c IHc a IHa b IHb G P.
    cbn [lbls]. rewrite !List.map_app.
    destruct (block_ite_cases G P c a b) as [(-> & E) | (_ & E)]; rewrite E.
    + unfold cond_tree_noelse. occ_simp. rewrite IHc, IHa. cbn [lbls List.map].
      rewrite ?List.app_nil_r. reflexivity.
    + unfold cond_tree. occ_simp. rewrite IHc, IHa, IHb.
      repeat rewrite <- List.app_assoc. reflexivity.
  - intros a IHa o b IHb G P. cbn [block lbls].
    rewrite occs_app, occs_cons, occs_op, !occs_as_binop, IHa, IHb, List.map_app.
    reflexivity.
  - intros a IH G P. cbn [block lbls]. occ_simp. reflexivity.
  - intros w tg a IH G P. cbn [block lbls]. occ_simp. reflexivity.
  - intros w a IHa ars IHars G P. cbn [block lbls]. occ_simp. reflexivity.
  - intros a IHa l b IHb G P. cbn [block lbls].
    unfold spread_tree, field_tree, paren_kids. occ_simp.
    rewrite IHa, IHb, List.map_app. cbn [List.map]. reflexivity.
  - intros a IH l G P. cbn [block lbls]. occ_simp. reflexivity.
  - intros a IH G P. cbn [block lbls]. occ_simp. reflexivity.
  - intros a IH G P. cbn [block lbls]. occ_simp. reflexivity.
  - split.
    + intros G P. split; reflexivity.
    + intros G P i. reflexivity.
  - intros l e IHe rest [IHrest IHmem]. split.
    + intros G P. destruct (IHrest G P) as [IHf IHm].
      cbn [field_trees more_field_trees lbls_fields]. unfold field_tree.
      split.
      * rewrite occs_cons. occ_simp. rewrite IHe, IHm. cbn [List.map]. rewrite List.map_app. reflexivity.
      * rewrite occs_cons. occ_simp. rewrite IHe, IHm. cbn [List.map]. rewrite List.map_app. reflexivity.
    + intros G P i. cbn [member_trees lbls_members]. unfold decl_named.
      rewrite occs_cons. occ_simp. rewrite IHe, (IHmem G P (S i)), List.map_app. reflexivity.
  - intros l e IHe rest [IHrest IHmem]. split.
    + intros G P. destruct (IHrest G P) as [IHf IHm].
      cbn [field_trees more_field_trees lbls_fields]. unfold field_tree.
      split.
      * rewrite occs_cons. occ_simp. rewrite IHe, IHm. cbn [List.map]. rewrite List.map_app. reflexivity.
      * rewrite occs_cons. occ_simp. rewrite IHe, IHm. cbn [List.map]. rewrite List.map_app. reflexivity.
    + intros G P i. cbn [member_trees lbls_members]. unfold decl_named.
      rewrite occs_cons. occ_simp. rewrite IHe, (IHmem G P (S i)), List.map_app. reflexivity.
  - intros; exact I.
  - intros; exact I.
  - intros; exact I.
Qed.

Lemma labels_print : forall e,
  labels (print_tree e) = nub_from [] (List.map lname (lbls [] 0 e)).
Proof.
  intros e. unfold labels, print_tree. f_equal.
  occ_simp. exact (proj1 occs_block e [] 0).
Qed.
