(* Spread and restrict (ADR 0033, docs/design/phase4-proof-plan.md): the
   inversions and the two typing facts preservation needs.

   A spread of a record literal sets the first field labeled [l], or adds one
   in front, by looking at the record alone ([fs_set]).  The type of the base,
   [l ^ P : T ; R], says which: [presence_inv] (GoatPresence.v) shows a
   literal's row is equivalent to such a row only when [P] is [Unit] (the
   record has an [l], and the update keeps its type up to equality) or [P] is
   [Bool] (no [l], and the row is equivalent to [R]).  A restrict takes out the
   first [l]; [rm] respects [req] (GoatPresence.v), so the row of the literal
   has the same first [l] as the row the rule saw.

   Axiom- and admit-free. *)

Require Import Metalib.Metatheory.
Require Import Goat.Goat_ott.
Require Import Goat.GoatRows.
Require Import Goat.GoatDefs.
Require Import Goat.GoatPresence.
Require Import Goat.GoatRecArith.
Require Import Goat.GoatMeta.
Require Import Goat.GoatConv.
Require Import Stdlib.Lists.List.

Lemma spread_inv : forall D G e1 l e2 T,
  typing D G (e_spread e1 l e2) T ->
  exists T0 R, typing D G e2 T0 /\ teqD D (typ_Record (row_Ext l T0 R)) T /\
    ((exists P, typing D G e1 (typ_Record (row_Maybe l P T0 R))) \/
     (typing D G e1 (typ_Record R) /\ rlacksD D l R = true)).
Proof.
  intros D G e1 l e2 T H. remember (e_spread e1 l e2) as e0 eqn:He.
  induction H; try discriminate He.
  - (* T_Conv *) destruct (IHtyping He) as [T0 [R [H1 [H2 H3]]]].
    exists T0, R. repeat split; try assumption. eauto using teqD_trans.
  - (* T_Spread *) inversion He; subst. exists T, R.
    repeat split; [ eassumption | apply teqD_refl | left; eexists; eassumption ].
  - (* T_SpreadL *) inversion He; subst. exists T, R.
    repeat split; [ eassumption | apply teqD_refl | right; split; eassumption ].
Qed.

Lemma restrict_inv : forall D G e l T,
  typing D G (e_restrict e l) T ->
  exists R0 T0 R, typing D G e (typ_Record R0) /\ rm l R0 T0 R /\
    teqD D (typ_Record R) T.
Proof.
  intros D G e l T H. remember (e_restrict e l) as e0 eqn:He.
  induction H; try discriminate He.
  - (* T_Conv *) destruct (IHtyping He) as [R0 [T0 [R [H1 [H2 H3]]]]].
    exists R0, T0, R. repeat split; try assumption. eauto using teqD_trans.
  - (* T_Restrict *) inversion He; subst. do 3 eexists.
    repeat split; try eassumption; apply teqD_refl.
Qed.

(* The row of a record literal is a plain spine. *)
Lemma field_typing_plain : forall D G fs R,
  field_typing D G fs R -> nmaybe R = 0.
Proof. intros D G fs R H. induction H; simpl; auto. Qed.

(* A field that is there is in the row. *)
Lemma lookup_pi : forall D G fs R l e,
  field_typing D G fs R -> lookup_first l fs = Some e ->
  exists T rest, pi l R = T :: rest.
Proof.
  intros D G fs R l e H. induction H as [D0 G0 Hu | D0 G0 l1 e1 T1 fs1 R1 Hty Hft IH | D0 G0 l1 e1 T1 fs1 R1 Hty Hft IH];
    intros Hl; simpl in *.
  - discriminate.
  - destruct (Nat.eqb l l1) eqn:E.
    + exists T1, (pi l R1). reflexivity.
    + exact (IH Hl).
  - destruct (Nat.eqb l l1) eqn:E.
    + exists T1, (pi l R1). reflexivity.
    + exact (IH Hl).
Qed.

(* The row with the type of its first [l] field replaced. *)
Fixpoint row_replace (l : label) (T : typ) (R : row) {struct R} : row :=
  match R with
  | row_Ext l' T' R' =>
      if Nat.eqb l l' then row_Ext l' T R' else row_Ext l' T' (row_replace l T R')
  | _ => R
  end.

Lemma field_typing_replace : forall D G fs R l v T,
  field_typing D G fs R -> (exists e, lookup_first l fs = Some e) ->
  typing D G v T -> field_typing D G (fs_replace l v fs) (row_replace l T R).
Proof.
  intros D G fs R l v T H. induction H as [D0 G0 Hu | D0 G0 l1 e1 T1 fs1 R1 Hty Hft IH | D0 G0 l1 e1 T1 fs1 R1 Hty Hft IH];
    intros [e Hl] Hv; simpl in *.
  - discriminate.
  - destruct (Nat.eqb l l1) eqn:E; simpl.
    + apply FT_cons; assumption.
    + apply FT_cons; [ assumption | apply IH; [ exists e; exact Hl | exact Hv ] ].
  - destruct (Nat.eqb l l1) eqn:E; simpl.
    + apply FT_cons; assumption.
    + apply FT_meth; [ assumption | apply IH; [ exists e; exact Hl | exact Hv ] ].
Qed.

Lemma row_replace_req : forall D G fs R l T T0 rest,
  field_typing D G fs R -> pi l R = T0 :: rest -> teq T0 T ->
  req (row_replace l T R) R.
Proof.
  intros D G fs R l T T0 rest H. revert T0 rest.
  induction H as [D0 G0 Hu | D0 G0 l1 e1 T1 fs1 R1 Hty Hft IH | D0 G0 l1 e1 T1 fs1 R1 Hty Hft IH];
    intros T0' rest' Hpi Hq; simpl in *.
  - discriminate.
  - destruct (Nat.eqb l l1) eqn:E; simpl.
    + inversion Hpi; subst. apply req_head; [ apply teq_sym; assumption | apply req_refl ].
    + apply req_head; [ apply teq_refl | eapply IH; eassumption ].
  - destruct (Nat.eqb l l1) eqn:E; simpl.
    + inversion Hpi; subst. apply req_head; [ apply teq_sym; assumption | apply req_refl ].
    + apply req_head; [ apply teq_refl | eapply IH; eassumption ].
Qed.

(* A row that lacks a label has no field-carrying entry for it. *)
Lemma rlacksD_pi : forall D l R, rlacksD D l R = true -> pi l R = nil.
Proof.
  intros D l R. induction R as [|r|l' T R IH|l' P T R IH]; simpl; intros H; try reflexivity.
  - apply Bool.andb_true_iff in H as [H1 H2].
    destruct (Nat.eqb l l'); [ discriminate H1 | apply IH; exact H2 ].
  - destruct (Nat.eqb l l') eqn:E; simpl.
    + apply Bool.andb_true_iff in H as [H1 H2].
      destruct P; try discriminate H1. simpl. apply IH. exact H2.
    + apply IH. exact H.
Qed.


Lemma Forall2_nil_r : forall (A B : Type) (R : A -> B -> Prop) (l : list A),
  Forall2 R l nil -> l = nil.
Proof. intros A B R l H. inversion H. reflexivity. Qed.


(* ------------------------------------------------------------------ *)
(* Normal forms of rows and the first-field operations.                *)
(* ------------------------------------------------------------------ *)

Lemma nmaybe_nf : forall D R, nmaybe R = 0 -> nmaybe (nfR D R) = 0.
Proof.
  intros D R. induction R as [ | | l T R IH | l P T R IH]; simpl; intros H; try reflexivity.
  - auto.
  - discriminate H.
Qed.


Lemma nfR_row_replace : forall D G fs R l T,
  field_typing D G fs R ->
  nfR D (row_replace l T R) = row_replace l (nfT D T) (nfR D R).
Proof.
  intros D G fs R l T H.
  induction H as [D0 G0 Hu | D0 G0 l1 e1 T1 fs1 R1 Hty Hft IH | D0 G0 l1 e1 T1 fs1 R1 Hty Hft IH].
  - reflexivity.
  - cbn [row_replace nfR]. destruct (Nat.eqb l l1) eqn:E; cbn [nfR];
      [ reflexivity | rewrite IH; reflexivity ].
  - cbn [row_replace nfR]. destruct (Nat.eqb l l1) eqn:E; cbn [nfR];
      [ reflexivity | rewrite IH; reflexivity ].
Qed.

Lemma rlacksD_rmf : forall l R T R0, rmf l R = Some (T, R0) ->
  forall D l', l <> l' -> rlacksD D l' R0 = rlacksD D l' R.
Proof.
  intros l R. induction R as [ | | l1 T1 R1 IH | l1 P T1 R1 IH]; intros T R0 H D l' Hne; simpl in H.
  - discriminate H.
  - discriminate H.
  - destruct (Nat.eqb l l1) eqn:E.
    + injection H as <- <-. apply Nat.eqb_eq in E. subst l1. cbn [rlacksD].
      apply Nat.eqb_neq in Hne. rewrite (Nat.eqb_sym l' l), Hne. reflexivity.
    + destruct (rmf l R1) as [[T0 R00] | ] eqn:E2; [ | discriminate H ].
      injection H as <- <-. cbn [rlacksD]. rewrite (IH _ _ eq_refl D l' Hne). reflexivity.
  - destruct (Nat.eqb l l1) eqn:E.
    + destruct (is_unit P); [ | discriminate H ]. injection H as <- <-.
      apply Nat.eqb_eq in E. subst l1. cbn [rlacksD]. apply Nat.eqb_neq in Hne.
      rewrite (Nat.eqb_sym l' l), Hne. reflexivity.
    + destruct (rmf l R1) as [[T0 R00] | ] eqn:E2; [ | discriminate H ].
      injection H as <- <-. cbn [rlacksD]. rewrite (IH _ _ eq_refl D l' Hne). reflexivity.
Qed.

Lemma rmf_nf : forall D l R T R', rmf l R = Some (T, R') ->
  rmf l (nfR D R) = Some (nfT D T, nfR D R').
Proof.
  intros D l R. induction R as [ | | l1 T1 R1 IH | l1 P T1 R1 IH]; intros T R' H; simpl in H.
  - discriminate H.
  - discriminate H.
  - destruct (Nat.eqb l l1) eqn:E.
    + injection H as <- <-. rewrite nfR_ext. simpl. rewrite E. reflexivity.
    + destruct (rmf l R1) as [[T0 R0] | ] eqn:E2; [ | discriminate H ].
      injection H as <- <-. rewrite nfR_ext, nfR_ext. simpl. rewrite E.
      rewrite (IH _ _ eq_refl). reflexivity.
  - destruct (Nat.eqb l l1) eqn:E.
    + destruct (is_unit P) eqn:EU; [ | discriminate H ]. injection H as <- <-.
      destruct P; try discriminate EU. rewrite nfR_maybe. cbn [is_abs andb]. cbv iota.
      simpl. rewrite E. reflexivity.
    + destruct (rmf l R1) as [[T0 R0] | ] eqn:E2; [ | discriminate H ].
      injection H as <- <-.
      assert (Ene : l <> l1) by (apply Nat.eqb_neq; exact E).
      pose proof (rlacksD_rmf _ _ _ _ E2 D l1 Ene) as Hl.
      pose proof (IH _ _ eq_refl) as IH2.
      rewrite !nfR_maybe. rewrite !nf_rlacksD, Hl.
      destruct (is_abs P && rlacksD D l1 R1); cbv iota.
      * exact IH2.
      * simpl. rewrite E, IH2. reflexivity.
Qed.

Lemma rm_nf : forall D l R T R', rm l R T R' -> rm l (nfR D R) (nfT D T) (nfR D R').
Proof. intros. unfold rm in *. apply rmf_nf. assumption. Qed.


(* A literal's row is equivalent to [l ^ P : T ; R], up to the dropping of
   absent entries: [P] is [Unit], or [P] is [Bool], the literal's row is
   equivalent to [R] and it has no field [l]. *)
Lemma presence_invD : forall D Rf l P T R,
  nmaybe Rf = 0 -> reqD D Rf (row_Maybe l P T R) ->
  P = typ_Unit \/
  (P = typ_Bool /\ reqD D Rf R /\ pi l Rf = nil).
Proof.
  intros D Rf l P T R Hn H. unfold reqD in H. rewrite nfR_maybe in H.
  destruct (is_abs P && rlacksD D l (nfR D R)) eqn:E.
  - cbv iota in H. right. apply andb_prop in E as [Ea Eb].
    destruct P; cbn in Ea; try discriminate. split; [ reflexivity | ].
    split; [ exact H | ].
    pose proof (req_pi _ _ H l) as Hp.
    rewrite (rlacksD_pi _ _ _ Eb) in Hp. pose proof (Forall2_nil_r _ _ _ _ Hp) as H0.
    rewrite pi_nf in H0. exact (map_nil_inv _ _ _ _ H0).
  - cbv iota in H.
    destruct (presence_inv (nfR D Rf) l (nfT D P) (nfT D T) (nfR D R) (nmaybe_nf D Rf Hn) H)
      as [HP | [HP [Hr Hpi]]].
    + left. destruct P; cbn in HP; congruence.
    + right. destruct P; cbn in HP; try discriminate. split; [ reflexivity | ].
      split; [ exact Hr | ].
      rewrite pi_nf in Hpi. exact (map_nil_inv _ _ _ _ Hpi).
Qed.

(* Preservation of a spread of a record literal. *)
Lemma spread_step_typing : forall D G fs l v P T R,
  typing D G (e_rec fs) (typ_Record (row_Maybe l P T R)) -> typing D G v T ->
  typing D G (e_rec (fs_plain (fs_set l v fs))) (typ_Record (row_Ext l T R)).
Proof.
  intros D G fs l v P T R Hty Hv.
  destruct (rec_inv _ _ _ _ Hty) as [Rf [Hft Hteq]].
  apply teqD_sym in Hteq. destruct (teqD_Record_inv _ _ _ Hteq) as [R2 [Heq Hreq]].
  inversion Heq; subst R2. apply req_sym in Hreq.
  destruct (presence_invD D Rf l P T R (field_typing_plain _ _ _ _ Hft) Hreq)
    as [-> | [-> [Hr Hpi]]].
  - (* an update *)
    assert (Hex : req (nfR D Rf) (row_Ext l (nfT D T) (nfR D R))).
    { eapply req_trans; [ exact Hreq | ]. rewrite nfR_maybe. cbn [is_abs andb nfT]. cbv iota.
      apply req_pre. }
    destruct (req_surface _ _ _ _ Hex) as [T0 [rest [Hpin Hq]]].
    pose proof Hpin as Hpi. rewrite pi_nf in Hpi.
    destruct (map_cons_inv _ _ _ _ _ _ Hpi) as [T1 [rest1 [Hpi1 [E1 _]]]].
    destruct (field_lookup_some _ _ _ _ _ _ _ Hft Hpi1) as [e0 [Hl _]].
    unfold fs_set. rewrite Hl.
    eapply T_ConvD.
    + apply T_Record; [ | apply no_meth_plain ].
      apply field_typing_fs_plain. apply field_typing_replace; [ exact Hft | exists e0; exact Hl | exact Hv ].
    + apply teqD_Record. rewrite (nfR_row_replace _ _ _ _ _ _ Hft), nfR_ext.
      eapply req_trans; [ | exact Hex ].
      eapply row_replace_req; [ apply field_typing_nf; exact Hft | exact Hpin | exact Hq ].
  - (* an extension *)
    assert (Hl : lookup_first l fs = None).
    { destruct (lookup_first l fs) as [e|] eqn:E; [ | reflexivity ].
      destruct (lookup_pi _ _ _ _ _ _ Hft E) as [T0 [rest Hp]].
      rewrite Hpi in Hp. discriminate. }
    unfold fs_set. rewrite Hl.
    eapply T_ConvD.
    + apply T_Record; [ | apply no_meth_plain ].
      apply field_typing_fs_plain. apply FT_cons; eassumption.
    + apply teqD_Record. rewrite !nfR_ext. apply req_head; [ apply teq_refl | exact Hr ].
Qed.

(* Preservation of a restrict of a record literal. *)
Lemma restrict_step_typing : forall D G fs l R0 T R,
  typing D G (e_rec fs) (typ_Record R0) -> rm l R0 T R ->
  typing D G (e_rec (fs_plain (fs_drop l fs))) (typ_Record R).
Proof.
  intros D G fs l R0 T R Hty Hrm.
  destruct (rec_inv _ _ _ _ Hty) as [Rf [Hft Hteq]].
  destruct (teqD_Record_inv _ _ _ Hteq) as [R2 [Heq Hreq]].
  inversion Heq; subst R2.
  destruct (rm_req _ _ (req_sym _ _ Hreq) _ _ _ (rm_nf D _ _ _ _ Hrm)) as [T' [R' [Hrm' [_ Hq]]]].
  eapply T_ConvD.
  - apply T_Record; [ | apply no_meth_plain ].
    apply field_typing_fs_plain. eapply field_typing_drop; [ apply field_typing_nf; exact Hft | exact Hrm' ].
  - apply teqD_Record. pose proof (req_reqD D _ _ (req_sym _ _ Hq)) as H2.
    unfold reqD in H2. rewrite nfR_idem in H2. exact H2.
Qed.

(* Preservation of a spread whose base row lacks the label by its kind: the
   base is a record literal, so it carries no field for the label either. *)
Lemma spread_step_typing_L : forall D G fs l v T R,
  typing D G (e_rec fs) (typ_Record R) -> rlacksD D l R = true -> typing D G v T ->
  typing D G (e_rec (fs_plain (fs_set l v fs))) (typ_Record (row_Ext l T R)).
Proof.
  intros D G fs l v T R Hty Hl Hv.
  destruct (rec_inv _ _ _ _ Hty) as [Rf [Hft Hteq]].
  destruct (teqD_Record_inv _ _ _ Hteq) as [R2 [Heq Hreq]].
  inversion Heq; subst R2.
  assert (Hpi : pi l Rf = nil).
  { pose proof (req_pi _ _ Hreq l) as Hp.
    rewrite (rlacksD_pi D l (nfR D R)) in Hp by (rewrite nf_rlacksD; exact Hl).
    pose proof (Forall2_nil_r _ _ _ _ Hp) as H0. rewrite pi_nf in H0. exact (map_nil_inv _ _ _ _ H0). }
  assert (Hlk : lookup_first l fs = None).
  { destruct (lookup_first l fs) as [e|] eqn:E; [ | reflexivity ].
    destruct (lookup_pi _ _ _ _ _ _ Hft E) as [T0 [rest Hp]].
    rewrite Hpi in Hp. discriminate. }
  unfold fs_set. rewrite Hlk.
  eapply T_ConvD.
  - apply T_Record; [ | apply no_meth_plain ].
    apply field_typing_fs_plain. apply FT_cons; eassumption.
  - apply teqD_Record. rewrite !nfR_ext. apply req_head; [ apply teq_refl | exact Hreq ].
Qed.

