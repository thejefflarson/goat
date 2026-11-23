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
Require Import Goat.GoatPrintArm.
Require Import Goat.GoatPrintInd.
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

Definition OccP (e : exp) : Prop :=
  forall G P, occs (block G P e) = List.map lname (lbls G P e).

Lemma occs_arm_names : forall m q, occs (arm_names q m) = [].
Proof.
  induction m as [| m IH]; intros q; [ reflexivity | ].
  cbn [arm_names]. destruct m as [| m]; [ occ_simp; reflexivity | ].
  occ_simp. rewrite IH. reflexivity.
Qed.

Lemma occs_pattern : forall w tg P, occs (arm_pattern w tg P) = [].
Proof.
  intros w tg P. unfold arm_pattern. destruct (arm_arity w tg) as [| m]; [ occ_simp; reflexivity | ].
  occ_simp. rewrite occs_arm_names. reflexivity.
Qed.

(* The body of an arm is the term left after its slots are bound. *)
Lemma occs_arm_body : forall m b G Q,
  (forall k, OccP (arm_inner k b)) ->
  occs (arm_body G Q (S m) b) = List.map lname (lbls_body G Q (S m) b).
Proof.
  induction m as [| m IH]; intros b G Q HP; destruct b; try reflexivity.
  - cbn [arm_body lbls_body]. exact (HP 1 G (S Q)).
  - cbn [arm_body lbls_body]. exact (IH b2 G (S Q) (fun k => HP (S k))).
Qed.

Lemma occs_slot_args : forall fs G P,
  fields_all OccP fs -> occs (slot_args G P fs) = List.map lname (lbls_slots G P fs).
Proof.
  induction fs as [| l e rest IH | l e rest IH]; intros G P Hall; [ reflexivity | | ];
    destruct Hall as [He Hall]; cbn [slot_args lbls_slots]; rewrite occs_cons;
    occ_simp; rewrite (He G P), (IH G P Hall), List.map_app; reflexivity.
Qed.

Lemma occs_block :
  (forall e G P, occs (block G P e) = List.map lname (lbls G P e)) /\
  (forall fs, (forall G P, occs (field_trees G P fs) = List.map lname (lbls_fields G P fs)
                /\ occs (more_field_trees G P fs) = List.map lname (lbls_fields G P fs))
              /\ (forall G P i, occs (member_trees G P i fs)
                                = List.map lname (lbls_members G P fs))) /\
  (forall ars, forall w G P, occs (arm_trees G P w ars) = List.map lname (lbls_arms G P w ars)).
Proof.
  apply exp_fields_mutind_chain.
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
  - intros w tg a IHa Hall G P. cbn [lbls].
    destruct a; try (destruct fs as [| l x rest | l x rest]); cbn [block lbls]; occ_simp;
      try reflexivity.
    destruct (Hall _ eq_refl) as [Hx Hrall].
    rewrite (Hx G P), (occs_slot_args _ G P Hrall), List.map_app. reflexivity.
  - intros w a IHa ars IHars G P. cbn [block lbls]. occ_simp.
    rewrite (IHa G P), (IHars w G P), List.map_app. reflexivity.
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
  - intros w G P. reflexivity.
  - intros e IHe w G P. cbn [arm_trees lbls_arms]. occ_simp. rewrite (IHe G P). reflexivity.
  - intros tg b IHb IHc rest IHrest w G P. cbn [arm_trees lbls_arms].
    rewrite occs_cons, List.map_app, <- (IHrest w G P). f_equal.
    occ_simp. rewrite occs_pattern. cbn [app].
    destruct (arm_arity w tg) as [| m]; cbn [app].
    + rewrite (IHb G (S P)). reflexivity.
    + rewrite (occs_arm_body m b G (S P) IHc). reflexivity.
Qed.

(* A declaration mentions no label. *)
Lemma occs_slot_trees : forall w cs, occs (slot_trees w cs) = [].
Proof.
  intros w. induction cs as [| c cs IH]; [ reflexivity | ].
  destruct cs as [| c2 cs].
  - cbn [slot_trees]. unfold slot_tree. destruct (slot_name w c); reflexivity.
  - rewrite slot_trees_cons2, !occs_cons, IH. unfold slot_tree.
    destruct (slot_name w c); reflexivity.
Qed.

Lemma occs_case_tree : forall w tg cs, label_occurrences (case_tree w tg cs) = [].
Proof.
  intros w tg cs. unfold case_tree, case_kids. rewrite lo_node. cbn [lo_head].
  destruct cs as [| c cs]; [ reflexivity | ].
  repeat (first [ rewrite occs_cons | rewrite occs_app | rewrite occs_slot_trees ]). reflexivity.
Qed.

Lemma occs_more_case_trees : forall w css tg, occs (more_case_trees w tg css) = [].
Proof.
  intros w. induction css as [| cs css IH]; intros tg; [ reflexivity | ].
  cbn [more_case_trees]. rewrite occs_cons. cbn [label_occurrences]. rewrite occs_cons.
  rewrite occs_case_tree, (IH (S tg)). reflexivity.
Qed.

Lemma occs_print_decls : forall D, occs (print_decls D) = [].
Proof.
  induction D as [| w D IH]; [ reflexivity | ].
  unfold print_decls in *. cbn [List.map]. rewrite occs_cons, IH.
  unfold tag_decl_tree. rewrite lo_node. cbn [lo_head]. rewrite occs_app.
  destruct (snd w) as [| cs rest].
  - reflexivity.
  - repeat (first [ rewrite occs_cons | rewrite occs_case_tree | rewrite occs_more_case_trees ]).
    reflexivity.
Qed.

Lemma labels_print : forall D e,
  labels (print_tree D e) = nub_from [] (List.map lname (lbls [] 0 e)).
Proof.
  intros D e. unfold labels, print_tree. f_equal.
  occ_simp. rewrite occs_print_decls, (proj1 occs_block e [] 0). reflexivity.
Qed.
