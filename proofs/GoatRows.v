(* Row-equivalence theory for core goat (docs/semantics.md sections 3 and 7,
   lemmas L1-L3). Everything here is over the Ott-generated [teq]/[req]
   relations and the [typ]/[row] grammar; it does not mention terms, so it is
   the reusable "row machinery" the record cases of canonical forms and
   preservation stand on.

   The pivotal design point (docs/semantics.md section 10, ADR 0008's named
   schedule risk): the SEMANTIC characterization of section 3 -- a row is, up to
   [req], its tail together with the per-label list of field types -- is proved
   here only in the SOUNDNESS direction ([req] respects the characterization,
   [req_pres]). That direction is exactly L2' as stated, and it is what the
   soundness theorems need: it discharges "no confusion" for rows, label
   surfacing (L3), and the record case of canonical forms. The COMPLETENESS
   direction (the characterization implies [req]) is the genuinely hard swap
   -congruence obligation; it is not needed for progress/preservation and is not
   proved here. *)

Require Import Metalib.Metatheory.
Require Import Goat.Goat_ott.
Require Import Coq.Lists.List.

(* ------------------------------------------------------------------ *)
(* L1: equivalence + congruence.                                       *)
(* reflexivity is [GoatProofs.teq_refl]/[req_refl] (derived by mutual   *)
(* induction, since the relation states no reflexivity rule); symmetry, *)
(* transitivity and the per-constructor congruences are the generated   *)
(* constructors [teq_sym]/[teq_trans]/[teq_arrow]/[teq_rec]/[req_head]   *)
(* etc.  We re-derive reflexivity here to keep the file self-contained.  *)
(* ------------------------------------------------------------------ *)

Scheme typ_mutind := Induction for typ Sort Prop
with   row_mutind := Induction for row Sort Prop.
Combined Scheme typ_row_mutind from typ_mutind, row_mutind.

Lemma teq_req_refl :
  (forall T : typ, teq T T) /\ (forall R : row, req R R).
Proof. apply typ_row_mutind; intros; eauto. Qed.

Lemma teq_refl : forall T, teq T T. Proof. apply teq_req_refl. Qed.
Lemma req_refl : forall R, req R R. Proof. apply teq_req_refl. Qed.

#[local] Hint Resolve teq_refl req_refl : core.

(* ------------------------------------------------------------------ *)
(* L2: head shape is preserved ("no confusion").                       *)
(* ------------------------------------------------------------------ *)

Definition thead_tag (T : typ) : nat :=
  match T with
  | typ_Number => 0
  | typ_Bool => 1
  | typ_Arrow _ _ => 2
  | typ_Record _ => 3
  | typ_Var _ => 4
  | typ_Unit => 5
  | typ_String => 6
  end.

Lemma teq_thead : forall T1 T2, teq T1 T2 -> thead_tag T1 = thead_tag T2.
Proof. induction 1; simpl in *; congruence. Qed.

Lemma teq_Number_inv : forall T, teq typ_Number T -> T = typ_Number.
Proof.
  intros T H. apply teq_thead in H; simpl in H.
  destruct T; simpl in H; try discriminate; reflexivity.
Qed.

Lemma teq_Bool_inv : forall T, teq typ_Bool T -> T = typ_Bool.
Proof.
  intros T H. apply teq_thead in H; simpl in H.
  destruct T; simpl in H; try discriminate; reflexivity.
Qed.

Lemma teq_Unit_inv : forall T, teq typ_Unit T -> T = typ_Unit.
Proof.
  intros T H. apply teq_thead in H; simpl in H.
  destruct T; simpl in H; try discriminate; reflexivity.
Qed.

Lemma teq_String_inv : forall T, teq typ_String T -> T = typ_String.
Proof.
  intros T H. apply teq_thead in H; simpl in H.
  destruct T; simpl in H; try discriminate; reflexivity.
Qed.

(* Arrow / record inversion up to [teq].  The statement is bidirectional
   (every clause both ways) precisely so the induction is closed under the
   [teq_sym] and [teq_trans] constructors; the one-directional corollaries
   follow. *)
Lemma teq_shape : forall T1 T2, teq T1 T2 ->
  (forall A B, T1 = typ_Arrow A B ->
     exists A' B', T2 = typ_Arrow A' B' /\ teq A A' /\ teq B B') /\
  (forall A B, T2 = typ_Arrow A B ->
     exists A' B', T1 = typ_Arrow A' B' /\ teq A A' /\ teq B B') /\
  (forall R, T1 = typ_Record R -> exists R', T2 = typ_Record R' /\ req R R') /\
  (forall R, T2 = typ_Record R -> exists R', T1 = typ_Record R' /\ req R R').
Proof.
  induction 1.
  - (* num *) repeat split; intros; discriminate.
  - (* bool *) repeat split; intros; discriminate.
  - (* unit *) repeat split; intros; discriminate.
  - (* string *) repeat split; intros; discriminate.
  - (* var *) repeat split; intros; discriminate.
  - (* arrow *) repeat split; intros; try discriminate;
      match goal with H : typ_Arrow _ _ = typ_Arrow _ _ |- _ => inversion H; subst end.
    + exists T1', T2'; auto.
    + exists T1, T2; auto using teq_sym.
  - (* rec *) repeat split; intros; try discriminate;
      match goal with H : typ_Record _ = typ_Record _ |- _ => inversion H; subst end.
    + exists R'; auto.
    + exists R; auto using req_sym.
  - (* trans *)
    destruct IHteq1 as [A1 [A2 [A3 A4]]].
    destruct IHteq2 as [B1 [B2 [B3 B4]]].
    repeat split; intros.
    + destruct (A1 _ _ H1) as [A' [B' [HeqT2 [? ?]]]].
      destruct (B1 _ _ HeqT2) as [A'' [B'' [HeqT3 [? ?]]]].
      exists A'', B''; eauto using teq_trans.
    + destruct (B2 _ _ H1) as [A' [B' [HeqT2 [? ?]]]].
      destruct (A2 _ _ HeqT2) as [A'' [B'' [HeqT1 [? ?]]]].
      exists A'', B''; eauto using teq_trans.
    + destruct (A3 _ H1) as [R' [HeqT2 ?]].
      destruct (B3 _ HeqT2) as [R'' [HeqT3 ?]].
      exists R''; eauto using req_trans.
    + destruct (B4 _ H1) as [R' [HeqT2 ?]].
      destruct (A4 _ HeqT2) as [R'' [HeqT1 ?]].
      exists R''; eauto using req_trans.
  - (* sym *)
    destruct IHteq as [A1 [A2 [A3 A4]]].
    repeat split; intros; eauto.
Qed.

Lemma teq_Arrow_inv : forall A B T, teq (typ_Arrow A B) T ->
  exists A' B', T = typ_Arrow A' B' /\ teq A A' /\ teq B B'.
Proof. intros A B T H. apply (proj1 (teq_shape _ _ H)); reflexivity. Qed.

Lemma teq_Record_inv : forall R T, teq (typ_Record R) T ->
  exists R', T = typ_Record R' /\ req R R'.
Proof.
  intros R T H.
  apply (proj1 (proj2 (proj2 (teq_shape _ _ H)))); reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(* L2': labels are preserved -- the section-3 characterization, proved  *)
(* in the soundness direction (by induction on the [req] derivation).   *)
(* [pi l R] is the list of field types carried by [l], in order; [rtail] *)
(* is the row's tail (empty or a row variable).                          *)
(* ------------------------------------------------------------------ *)

Fixpoint pi (l : label) (R : row) : list typ :=
  match R with
  | row_Empty => nil
  | row_Var _ => nil
  | row_Ext l' T R' => if Nat.eqb l l' then T :: pi l R' else pi l R'
  end.

Fixpoint rtail (R : row) : row :=
  match R with
  | row_Empty => row_Empty
  | row_Var r => row_Var r
  | row_Ext _ _ R' => rtail R'
  end.

Lemma Forall2_teq_refl : forall l : list typ, Forall2 teq l l.
Proof. induction l; auto. Qed.

Lemma Forall2_teq_sym : forall l1 l2,
  Forall2 teq l1 l2 -> Forall2 teq l2 l1.
Proof. induction 1; auto using teq_sym. Qed.

Lemma Forall2_teq_trans : forall l1 l2 l3,
  Forall2 teq l1 l2 -> Forall2 teq l2 l3 -> Forall2 teq l1 l3.
Proof.
  intros l1 l2 l3 H; revert l3. induction H; intros l3 H2.
  - inversion H2; subst; auto.
  - inversion H2; subst; eauto using teq_trans.
Qed.

Lemma req_pres : forall R1 R2, req R1 R2 ->
  rtail R1 = rtail R2 /\ (forall l, Forall2 teq (pi l R1) (pi l R2)).
Proof.
  induction 1.
  - (* empty *) split; [ reflexivity | intros; apply Forall2_teq_refl ].
  - (* var *) split; [ reflexivity | intros; apply Forall2_teq_refl ].
  - (* head: l:T;R ~ l:T';R' with teq T T', req R R' *)
    destruct IHreq as [Htl Hpi]. split.
    + simpl; assumption.
    + intros l0. simpl. destruct (Nat.eqb l0 l); auto.
  - (* swap: l<>l' *)
    split.
    + reflexivity.
    + intros l0. simpl.
      destruct (Nat.eqb l0 l) eqn:El; destruct (Nat.eqb l0 l') eqn:El';
        try apply Forall2_teq_refl.
      apply Nat.eqb_eq in El; apply Nat.eqb_eq in El'; congruence.
  - (* trans *)
    destruct IHreq1 as [T1 P1]. destruct IHreq2 as [T2 P2].
    split; [ congruence | intros l0; eauto using Forall2_teq_trans ].
  - (* sym *)
    destruct IHreq as [T1 P1].
    split; [ auto | intros l0; auto using Forall2_teq_sym ].
Qed.

Corollary req_rtail : forall R1 R2, req R1 R2 -> rtail R1 = rtail R2.
Proof. intros. apply req_pres; auto. Qed.

Corollary req_pi : forall R1 R2, req R1 R2 ->
  forall l, Forall2 teq (pi l R1) (pi l R2).
Proof. intros. apply req_pres; auto. Qed.

(* ------------------------------------------------------------------ *)
(* L3: row surfacing.  If [R] is equivalent to a row presenting [l] at   *)
(* the head with field type [T], then [R] actually carries an [l]-field, *)
(* and its FIRST one has a type [teq]-equivalent to [T].  This is the     *)
(* declarative analogue of [rewrite_row] and the bridge from T-Proj to   *)
(* ST-ProjRec.                                                            *)
(* ------------------------------------------------------------------ *)

Lemma pi_head : forall l T R, pi l (row_Ext l T R) = T :: pi l R.
Proof. intros. simpl. rewrite Nat.eqb_refl. reflexivity. Qed.

Lemma req_surface : forall R l T R',
  req R (row_Ext l T R') ->
  exists T0 rest, pi l R = T0 :: rest /\ teq T0 T.
Proof.
  intros R l T R' H.
  apply req_pi with (l := l) in H.
  rewrite pi_head in H.
  inversion H; subst.
  eexists; eexists; split; [ reflexivity | assumption ].
Qed.
