(* Completeness of algorithm W, stage 7.6, part L2: the row combinatorics the
   unifier's completeness stands on (docs/design/phase7-proof-plan.md).

   [req] is an equivalence closed under swaps, so a hypothesis [req R1 R2]
   says little until it is inverted.  [GoatRows.v] proves the soundness half of
   the characterization ([req_pres]: equal tails and, per label, [teq] field
   lists).  What a completeness proof needs is the other half, and for a closed
   row of plain fields it is a constructive swap argument: the first entry of a
   label can be surfaced ([surface_req]), and two rows with the same field list
   at every label are [req] ([req_of_pi]).  [rewrite_row] on such a row is the
   same surfacing ([rewrite_row_found]).

   The sizes [tsz] and [rsz] are invariant under [teq] and [req] (an absent
   presence counts for nothing, as [req_abs] drops it), so a measure computed on
   the image of a type stays put as the substitution is rearranged. *)

Require Import Metalib.Metatheory.
Require Import Goat.Goat_ott.
Require Import Goat.GoatRows.
Require Import Goat.GoatDefs.
Require Import Goat.GoatInfer.
Require Import Goat.GoatInferSub.
Require Import Goat.GoatInferUnify.
Require Import Stdlib.Arith.Arith.
Require Import Stdlib.micromega.Lia.
Require Import Stdlib.Lists.List.
Import ListNotations.

(* ---- sizes ---- *)

Fixpoint tsz (T : typ) : nat :=
  match T with
  | typ_Arrow A B => S (tsz A + tsz B)
  | typ_Record R => S (rsz R)
  | _ => 1
  end
with rsz (R : row) : nat :=
  match R with
  | row_Empty | row_Var _ => 0
  | row_Ext _ T R' => S (tsz T + rsz R')
  | row_Maybe _ P T R' => if is_abs P then rsz R' else S (tsz T + rsz R')
  end.

Lemma teq_req_size :
  (forall T T', teq T T' -> tsz T = tsz T') /\ (forall R R', req R R' -> rsz R = rsz R').
Proof.
  apply teq_req_mutind; intros; simpl in *; try reflexivity; try lia.
  - (* maybe *) rewrite <- (teq_is_abs _ _ t). destruct (is_abs T1); lia.
  - (* swap_em *) destruct (is_abs T1); lia.
  - (* swap_mm *) destruct (is_abs T1), (is_abs T1'); lia.
Qed.

Lemma teq_tsz : forall T T', teq T T' -> tsz T = tsz T'.
Proof. exact (proj1 teq_req_size). Qed.

Lemma req_rsz : forall R R', req R R' -> rsz R = rsz R'.
Proof. exact (proj2 teq_req_size). Qed.

(* ---- closed rows of fields ---- *)

(* A spine of plain fields with no tail variable and no presence entry. *)
Fixpoint cext (R : row) : Prop :=
  match R with
  | row_Empty => True
  | row_Ext _ _ R' => cext R'
  | _ => False
  end.

Fixpoint get_l (l : label) (R : row) : option typ :=
  match R with
  | row_Ext l' T R' => if Nat.eqb l l' then Some T else get_l l R'
  | _ => None
  end.

Fixpoint rm_l (l : label) (R : row) : row :=
  match R with
  | row_Ext l' T R' => if Nat.eqb l l' then R' else row_Ext l' T (rm_l l R')
  | _ => R
  end.

Lemma cext_rm : forall l R, cext R -> cext (rm_l l R).
Proof.
  intros l R. induction R; simpl; try tauto.
  intros H. destruct (Nat.eqb l l0); simpl; auto.
Qed.

Lemma cext_ap : forall s R, cext R -> cext (apR s R).
Proof. intros s R. induction R; simpl; try tauto. Qed.

Lemma get_l_ap : forall s l R, cext R ->
  get_l l (apR s R) = option_map (apT s) (get_l l R).
Proof.
  intros s l R. induction R; try (simpl; tauto); try reflexivity.
  intros H. rewrite apR_Ext. cbn [get_l]. destruct (Nat.eqb l l0); simpl; auto.
Qed.

Lemma rm_l_ap : forall s l R, cext R -> rm_l l (apR s R) = apR s (rm_l l R).
Proof.
  intros s l R. induction R; try (simpl; tauto); try reflexivity.
  intros H. rewrite apR_Ext. cbn [rm_l]. destruct (Nat.eqb l l0); [ reflexivity | ].
  rewrite apR_Ext. f_equal. auto.
Qed.

Lemma pi_get_none : forall l R, cext R -> get_l l R = None -> pi l R = nil.
Proof.
  intros l R. induction R; simpl; try tauto; try reflexivity.
  intros H E. destruct (Nat.eqb l l0); [ discriminate | auto ].
Qed.

Lemma pi_get_some : forall l R B, cext R -> get_l l R = Some B ->
  pi l R = B :: pi l (rm_l l R) /\ (forall m, m <> l -> pi m (rm_l l R) = pi m R).
Proof.
  intros l R B. induction R; simpl; try tauto; try (intros _ E; discriminate E).
  intros H E. destruct (Nat.eqb l l0) eqn:El.
  - inversion E; subst. apply Nat.eqb_eq in El. subst.
    split; [ reflexivity | ]. intros m Hm. destruct (Nat.eqb m l0) eqn:Em;
      [ apply Nat.eqb_eq in Em; congruence | reflexivity ].
  - destruct (IHR H E) as [Hp Hm]. split.
    + rewrite Hp. simpl. rewrite El. reflexivity.
    + intros m Hm'. simpl. destruct (Nat.eqb m l0); [ f_equal | ]; apply Hm; exact Hm'.
Qed.

Lemma surface_req : forall l R B, cext R -> get_l l R = Some B ->
  req R (row_Ext l B (rm_l l R)).
Proof.
  intros l R B. induction R; simpl; try tauto; try (intros _ E; discriminate E).
  intros H E. destruct (Nat.eqb l l0) eqn:El.
  - inversion E; subst. apply Nat.eqb_eq in El. subst. apply req_refl.
  - apply Nat.eqb_neq in El.
    eapply req_trans; [ apply req_head; [ apply teq_refl | exact (IHR H E) ] | ].
    apply req_swap. congruence.
Qed.

Lemma req_of_pi : forall X Y, cext X -> cext Y ->
  (forall m, Forall2 teq (pi m X) (pi m Y)) -> req X Y.
Proof.
  induction X; intros Y HX HY Hpi; simpl in HX; try tauto.
  - destruct Y; simpl in HY; try tauto; [ apply req_empty | ].
    specialize (Hpi l). simpl in Hpi. rewrite Nat.eqb_refl in Hpi. inversion Hpi.
  - destruct (get_l l Y) as [B|] eqn:Eg.
    + destruct (pi_get_some l Y B HY Eg) as [Hp Hm].
      assert (Hl := Hpi l). rewrite pi_head, Hp in Hl. inversion Hl; subst.
      eapply req_trans; [ | apply req_sym; exact (surface_req l Y B HY Eg) ].
      apply req_head; [ assumption | ].
      apply IHX; [ exact HX | apply cext_rm; exact HY | ].
      intros m. destruct (Nat.eq_dec m l) as [->|Hne]; [ assumption | ].
      rewrite (Hm m Hne). specialize (Hpi m). simpl in Hpi.
      destruct (Nat.eqb m l) eqn:E; [ apply Nat.eqb_eq in E; congruence | exact Hpi ].
    + specialize (Hpi l). rewrite (pi_get_none l Y HY Eg) in Hpi. simpl in Hpi.
      rewrite Nat.eqb_refl in Hpi. inversion Hpi.
Qed.

Lemma req_cancel : forall l A B X Y, cext X -> cext Y ->
  req (row_Ext l A X) (row_Ext l B Y) -> teq A B /\ req X Y.
Proof.
  intros l A B X Y HX HY H. pose proof (req_pi _ _ H) as Hpi.
  assert (Hl := Hpi l). rewrite !pi_head in Hl. inversion Hl; subst. split; [ assumption | ].
  apply req_of_pi; [ exact HX | exact HY | ].
  intros m. destruct (Nat.eq_dec m l) as [->|Hne]; [ assumption | ].
  specialize (Hpi m). simpl in Hpi.
  destruct (Nat.eqb m l) eqn:E; [ apply Nat.eqb_eq in E; congruence | exact Hpi ].
Qed.

(* [rewrite_row] on a closed row that has the label surfaces its first field. *)
Lemma rewrite_row_found : forall l av D R n T', cext R -> get_l l R = Some T' ->
  rewrite_row l av D R n = Some (typ_Unit, T', rm_l l R, sid, D, n).
Proof.
  intros l av D R n T'. induction R; simpl; try tauto; try (intros _ E; discriminate E).
  intros H E. destruct (Nat.eqb l l0) eqn:El.
  - inversion E; subst. reflexivity.
  - rewrite (IHR H E). rewrite apT_id. reflexivity.
Qed.

(* ---- the field list of an image ---- *)

Lemma pi_apR_ext : forall S l T R, pi l (apR S (row_Ext l T R)) = apT S T :: pi l (apR S R).
Proof. intros. rewrite apR_Ext. apply pi_head. Qed.
