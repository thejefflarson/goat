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
Require Import Goat.GoatMeta.
Require Import Stdlib.Lists.List.

Lemma spread_inv : forall D G e1 l e2 T,
  typing D G (e_spread e1 l e2) T ->
  exists P T0 R, typing D G e1 (typ_Record (row_Maybe l P T0 R)) /\
    typing D G e2 T0 /\ teq (typ_Record (row_Ext l T0 R)) T.
Proof.
  intros D G e1 l e2 T H. remember (e_spread e1 l e2) as e0 eqn:He.
  induction H; try discriminate He.
  - (* T_Conv *) destruct (IHtyping He) as [P [T0 [R [H1 [H2 H3]]]]].
    exists P, T0, R. repeat split; try assumption. eauto using teq_trans.
  - (* T_Spread *) inversion He; subst. do 3 eexists.
    repeat split; try eassumption; apply teq_refl.
Qed.

Lemma restrict_inv : forall D G e l T,
  typing D G (e_restrict e l) T ->
  exists R0 T0 R, typing D G e (typ_Record R0) /\ rm l R0 T0 R /\
    teq (typ_Record R) T.
Proof.
  intros D G e l T H. remember (e_restrict e l) as e0 eqn:He.
  induction H; try discriminate He.
  - (* T_Conv *) destruct (IHtyping He) as [R0 [T0 [R [H1 [H2 H3]]]]].
    exists R0, T0, R. repeat split; try assumption. eauto using teq_trans.
  - (* T_Restrict *) inversion He; subst. do 3 eexists.
    repeat split; try eassumption; apply teq_refl.
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
  intros D G fs R l e H. induction H as [D0 G0 Hu | D0 G0 l1 e1 T1 fs1 R1 Hty Hft IH];
    intros Hl; simpl in *.
  - discriminate.
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
  intros D G fs R l v T H. induction H as [D0 G0 Hu | D0 G0 l1 e1 T1 fs1 R1 Hty Hft IH];
    intros [e Hl] Hv; simpl in *.
  - discriminate.
  - destruct (Nat.eqb l l1) eqn:E; simpl.
    + apply FT_cons; assumption.
    + apply FT_cons; [ assumption | apply IH; [ exists e; exact Hl | exact Hv ] ].
Qed.

Lemma row_replace_req : forall D G fs R l T T0 rest,
  field_typing D G fs R -> pi l R = T0 :: rest -> teq T0 T ->
  req (row_replace l T R) R.
Proof.
  intros D G fs R l T T0 rest H. revert T0 rest.
  induction H as [D0 G0 Hu | D0 G0 l1 e1 T1 fs1 R1 Hty Hft IH];
    intros T0' rest' Hpi Hq; simpl in *.
  - discriminate.
  - destruct (Nat.eqb l l1) eqn:E; simpl.
    + inversion Hpi; subst. apply req_head; [ apply teq_sym; assumption | apply req_refl ].
    + apply req_head; [ apply teq_refl | eapply IH; eassumption ].
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

(* Preservation of a spread of a record literal. *)
Lemma spread_step_typing : forall D G fs l v P T R,
  typing D G (e_rec fs) (typ_Record (row_Maybe l P T R)) -> typing D G v T ->
  typing D G (e_rec (fs_set l v fs)) (typ_Record (row_Ext l T R)).
Proof.
  intros D G fs l v P T R Hty Hv.
  destruct (rec_inv _ _ _ _ Hty) as [Rf [Hft Hteq]].
  apply teq_sym in Hteq. destruct (teq_Record_inv _ _ Hteq) as [R2 [Heq Hreq]].
  inversion Heq; subst R2. apply req_sym in Hreq.
  destruct (presence_inv Rf l P T R (field_typing_plain _ _ _ _ Hft) Hreq)
    as [-> | [-> [Hr Hpi]]].
  - (* an update *)
    assert (Hex : req Rf (row_Ext l T R))
      by (eapply req_trans; [ exact Hreq | apply req_pre ]).
    destruct (req_surface _ _ _ _ Hex) as [T0 [rest [Hpi Hq]]].
    destruct (field_lookup_some _ _ _ _ _ _ _ Hft Hpi) as [e0 [Hl _]].
    unfold fs_set. rewrite Hl.
    eapply T_Conv.
    + apply T_Record. apply field_typing_replace; [ exact Hft | exists e0; exact Hl | exact Hv ].
    + apply teq_rec. eapply req_trans; [ eapply row_replace_req; eassumption | exact Hex ].
  - (* an extension *)
    assert (Hl : lookup_first l fs = None).
    { destruct (lookup_first l fs) as [e|] eqn:E; [ | reflexivity ].
      destruct (lookup_pi _ _ _ _ _ _ Hft E) as [T0 [rest Hp]].
      rewrite Hpi in Hp. discriminate. }
    unfold fs_set. rewrite Hl.
    eapply T_Conv.
    + apply T_Record. apply FT_cons; eassumption.
    + apply teq_rec. apply req_head; [ apply teq_refl | exact Hr ].
Qed.

(* Preservation of a restrict of a record literal. *)
Lemma restrict_step_typing : forall D G fs l R0 T R,
  typing D G (e_rec fs) (typ_Record R0) -> rm l R0 T R ->
  typing D G (e_rec (fs_drop l fs)) (typ_Record R).
Proof.
  intros D G fs l R0 T R Hty Hrm.
  destruct (rec_inv _ _ _ _ Hty) as [Rf [Hft Hteq]].
  destruct (teq_Record_inv _ _ Hteq) as [R2 [Heq Hreq]].
  inversion Heq; subst R2.
  destruct (rm_req _ _ (req_sym _ _ Hreq) _ _ _ Hrm) as [T' [R' [Hrm' [_ Hq]]]].
  eapply T_Conv.
  - apply T_Record. eapply field_typing_drop; eassumption.
  - apply teq_rec. apply req_sym. exact Hq.
Qed.
