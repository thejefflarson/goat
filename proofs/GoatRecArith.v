(* Record arithmetic (ADR 0012): [+ - * // %] and [/] on records of numbers act
   field by field.

   Two records of one numeric type may list their fields in different orders
   and may repeat a label, so [rec_zip] (GoatDefs.v) pairs each field of the
   first with the first field of the second under its label.  Given two field
   lists typed by rows equivalent to one numeric row [R], this file shows that
   the pairing exists and that the record of operator applications it builds
   has a row equivalent to [R] again.  [row_sig] says every field of the row
   takes the operator ([bin_sig]).

   Axiom- and admit-free. *)

Require Import Metalib.Metatheory.
Require Import Goat.Goat_ott.
Require Import Goat.GoatRows.
Require Import Goat.GoatDefs.
Require Import Goat.GoatPresence.

Fixpoint row_sig (D : denv) (o : bop) (R : row) {struct R} : Prop :=
  match R with
  | row_Empty => True
  | row_Ext _ T R' => bin_sig D o T T T /\ row_sig D o R'
  | _ => False
  end.

Lemma rsat_row_sig : forall D o R,
  (kind o = k_ring \/ kind o = k_whole) -> rsat D R -> row_sig D o R.
Proof.
  intros D o R Hk. induction R using row_ind4; simpl; intros H; try contradiction; auto.
  destruct H as [H1 H2]. split; [ | auto ].
  destruct Hk as [Hk | Hk]; [ apply sig_ring | apply sig_whole ]; assumption.
Qed.

Lemma rfsat_row_sig : forall D R, rfsat R -> row_sig D bop_div R.
Proof.
  intros D R. induction R using row_ind4; simpl; intros H; try contradiction; auto.
  destruct H as [H1 H2]. split; [ | auto ].
  destruct T; simpl in H1; try contradiction.
  - apply sig_quot.
  - apply sig_quot_rec; exact H1.
Qed.

(* An operator on records takes records of one row, and every field of the row
   takes the operator. *)
Lemma bin_sig_record : forall D o R B X,
  bin_sig D o (typ_Record R) B X ->
  B = typ_Record R /\ X = typ_Record R /\ row_sig D o R.
Proof.
  intros D o R B X H. inversion H; subst.
  - repeat split. apply rsat_row_sig; [ left; assumption | assumption ].
  - repeat split. apply rsat_row_sig; [ right; assumption | assumption ].
  - repeat split. apply rfsat_row_sig; assumption.
  - match goal with Hc : cmp_typ _ |- _ => inversion Hc end.
Qed.

Lemma rm_row_sig : forall D o l R T R',
  row_sig D o R -> rm l R T R' -> bin_sig D o T T T /\ row_sig D o R'.
Proof.
  intros D o l R. induction R using row_ind4; intros T0 R0 Hs Hrm.
  - unfold rm in Hrm. simpl in Hrm. discriminate.
  - simpl in Hs. contradiction.
  - simpl in Hs. destruct Hs as [Hb Hs].
    destruct (rm_ext_inv _ _ _ _ _ _ Hrm) as [[E1 [E2 E3]] | [Hne [R1 [E ->]]]].
    + subst. split; assumption.
    + destruct (IHR _ _ Hs E) as [Hb1 Hs1]. split; [ exact Hb1 | simpl; split; assumption ].
  - simpl in Hs. contradiction.
Qed.

(* A row is its first [l] field in front of what is left. *)
Lemma rm_ext_req : forall D o l R T R',
  row_sig D o R -> rm l R T R' -> req R (row_Ext l T R').
Proof.
  intros D o l R. induction R using row_ind4; intros T0 R0 Hs Hrm.
  - unfold rm in Hrm. simpl in Hrm. discriminate.
  - simpl in Hs. contradiction.
  - simpl in Hs. destruct Hs as [Hb Hs].
    destruct (rm_ext_inv _ _ _ _ _ _ Hrm) as [[E1 [E2 E3]] | [Hne [R1 [E ->]]]].
    + subst. apply req_refl.
    + pose proof (IHR _ _ Hs E) as Hq.
      eapply req_trans; [ apply req_head; [ apply teq_refl | exact Hq ] | ].
      apply req_swap. auto.
  - simpl in Hs. contradiction.
Qed.

Lemma field_typing_lookup_rm : forall D G fs R l T R',
  field_typing D G fs R -> rm l R T R' ->
  exists v, lookup_first l fs = Some v /\ typing D G v T.
Proof.
  intros D G fs R l T R' H. revert T R'.
  induction H as [D0 G0 Hu | D0 G0 l1 e1 T1 fs1 R1 Hty Hft IH]; intros T0 R0 Hrm.
  - exfalso. eapply rm_empty_inv; eassumption.
  - destruct (rm_ext_inv _ _ _ _ _ _ Hrm) as [[E1 [E2 E3]] | [Hne [R2 [E ->]]]].
    + subst. exists e1. simpl. rewrite Nat.eqb_refl. split; [ reflexivity | exact Hty ].
    + destruct (IH _ _ E) as [v [Hl Hv]]. exists v. simpl.
      rewrite (proj2 (Nat.eqb_neq _ _) Hne). split; assumption.
Qed.

Lemma field_typing_drop : forall D G fs R l T R',
  field_typing D G fs R -> rm l R T R' -> field_typing D G (fs_drop l fs) R'.
Proof.
  intros D G fs R l T R' H. revert T R'.
  induction H as [D0 G0 Hu | D0 G0 l1 e1 T1 fs1 R1 Hty Hft IH];
    intros T0 R0 Hrm.
  - exfalso. eapply rm_empty_inv; eassumption.
  - destruct (rm_ext_inv _ _ _ _ _ _ Hrm) as [[E1 [E2 E3]] | [Hne [R2 [E ->]]]].
    + subst. simpl. rewrite Nat.eqb_refl. exact Hft.
    + simpl. rewrite (proj2 (Nat.eqb_neq _ _) Hne).
      apply FT_cons; [ exact Hty | eapply IH; exact E ].
Qed.

(* Two records typed by rows equivalent to a numeric row [R] pair up field by
   field, and the pairing is a record of the same type. *)
Lemma zip_typing : forall D G o fs1 Rf1,
  field_typing D G fs1 Rf1 ->
  forall fs2 Rf2 R,
    field_typing D G fs2 Rf2 -> req Rf1 R -> req Rf2 R -> row_sig D o R ->
    exists fs Rout, rec_zip o fs1 fs2 fs /\ field_typing D G fs Rout /\ req Rout R.
Proof.
  intros D G o fs1 Rf1 H.
  induction H as [D0 G0 Hu | D0 G0 l e T fs1' R1 Hty Hft IH];
    intros fs2 Rf2 R H2 Hq1 Hq2 Hs.
  - exists fs_nil, row_Empty.
    split; [ apply rz_nil | split; [ apply FT_nil; exact Hu | exact Hq1 ] ].
  - destruct (rm_req _ _ Hq1 l T R1 (rm_ext_here l T R1)) as [T' [R'' [Hrm [HT Hq1']]]].
    destruct (rm_row_sig _ _ _ _ _ _ Hs Hrm) as [Hb Hs'].
    destruct (rm_req _ _ (req_sym _ _ Hq2) l T' R'' Hrm) as [T2 [R2 [Hrm2 [HT2 Hq2']]]].
    destruct (field_typing_lookup_rm _ _ _ _ _ _ _ H2 Hrm2) as [v2 [Hl Hv2]].
    pose proof (field_typing_drop _ _ _ _ _ _ _ H2 Hrm2) as Hd.
    destruct (IH _ _ _ Hd Hq1' (req_sym _ _ Hq2') Hs') as [fs [Ro [Hz [Hf Hq]]]].
    exists (fs_cons l (e_bin e o v2) fs), (row_Ext l T' Ro).
    split; [ eapply rz_cons; eassumption | split ].
    + apply FT_cons; [ | exact Hf ].
      eapply T_Bin with (A := T') (B := T').
      * eapply T_Conv; [ exact Hty | exact HT ].
      * eapply T_Conv; [ exact Hv2 | apply teq_sym; exact HT2 ].
      * exact Hb.
    + eapply req_trans; [ apply req_head; [ apply teq_refl | exact Hq ] | ].
      apply req_sym. eapply rm_ext_req; eassumption.
Qed.

Lemma rec_zip_det : forall o fs1 fs2 fs,
  rec_zip o fs1 fs2 fs -> forall fs', rec_zip o fs1 fs2 fs' -> fs = fs'.
Proof.
  intros o fs1 fs2 fs H. induction H as [fs2 | l v1 r1 fs2 v2 rs Hl Hz IH];
    intros fs' H'; inversion H'; subst; try reflexivity.
  match goal with
  | Hl' : lookup_first l fs2 = Some ?v |- _ => rewrite Hl in Hl'; inversion Hl'; subst
  end.
  f_equal. apply IH. assumption.
Qed.
