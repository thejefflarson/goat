(* Tag groups: the algebra of group types and payloads (docs/design/closed-tags-plan.md;
   GoatDefs.v defines [spine], [slot_ty], [tag_payload]
   and the arms functions).  What the metatheory needs of them: the arguments
   of a group type are equal exactly when their lists are, equal arguments
   give equal payloads, and substitution acts on the arguments alone. *)

Require Import Metalib.Metatheory.
Require Import Goat.Goat_ott.
Require Import Stdlib.Lists.List.
Require Import Goat.GoatRows.
Require Import Goat.GoatDefs.
Require Import Goat.GoatMu.

(* ------------------------------------------------------------------ *)
(* The spine of the arguments                                            *)
(* ------------------------------------------------------------------ *)

Lemma spine_inj : forall Ts Ts', spine Ts = spine Ts' -> Ts = Ts'.
Proof.
  induction Ts as [|T Ts IH]; intros [|T' Ts'] H; simpl in H;
    try discriminate; try reflexivity.
  inversion H; subst. f_equal. apply IH; auto.
Qed.

Lemma teq_spine_inv : forall Ts Ts', teq (spine Ts) (spine Ts') -> Forall2 teq Ts Ts'.
Proof.
  induction Ts as [|T Ts IH]; intros Ts' H; simpl in H.
  - destruct Ts' as [|T' Ts'].
    + constructor.
    + simpl in H. apply teq_Unit_inv in H. discriminate.
  - destruct Ts' as [|T' Ts'].
    + simpl in H. apply teq_Arrow_inv in H. destruct H as [A [B [E _]]]. discriminate.
    + simpl in H. apply teq_Arrow_inv in H. destruct H as [A [B [E [H1 H2]]]].
      inversion E; subst. constructor; [ assumption | apply IH; assumption ].
Qed.

Lemma teq_spine : forall Ts Ts', Forall2 teq Ts Ts' -> teq (spine Ts) (spine Ts').
Proof.
  intros Ts Ts' H. induction H; simpl; auto using teq_refl.
Qed.

(* ------------------------------------------------------------------ *)
(* Equal arguments give equal payloads                                    *)
(* ------------------------------------------------------------------ *)

Lemma teq_nth : forall Ts Ts', Forall2 teq Ts Ts' ->
  forall j, teq (nth j Ts typ_Unit) (nth j Ts' typ_Unit).
Proof.
  intros Ts Ts' H. induction H; intros [|j]; simpl; auto using teq_refl.
Qed.

Lemma teq_slot_ty : forall w Ts Ts' c, Forall2 teq Ts Ts' ->
  teq (slot_ty w Ts c) (slot_ty w Ts' c).
Proof.
  intros w Ts Ts' c H. unfold slot_ty.
  destruct c as [|[|[|[|[|[|c]]]]]]; auto using teq_refl.
  - apply teq_grp. apply teq_spine; assumption.
  - apply teq_nth; assumption.
Qed.

Lemma teq_slots_row : forall w Ts Ts' cs i, Forall2 teq Ts Ts' ->
  req (slots_row w Ts i cs) (slots_row w Ts' i cs).
Proof.
  intros w Ts Ts' cs. induction cs as [|c cs IH]; intros i H; simpl.
  - apply req_empty.
  - apply req_head; [ apply teq_slot_ty; assumption | apply IH; assumption ].
Qed.

Lemma teq_tag_payload : forall w Ts Ts' tg, Forall2 teq Ts Ts' ->
  teq (tag_payload w Ts tg) (tag_payload w Ts' tg).
Proof.
  intros w Ts Ts' tg H. unfold tag_payload.
  destruct (nth_error w tg) as [cs|]; [ | apply teq_unit ].
  unfold payload_ty. destruct cs; [ apply teq_unit | ].
  apply teq_rec. apply teq_slots_row; assumption.
Qed.

(* ------------------------------------------------------------------ *)
(* Substitution acts on the arguments                                     *)
(* ------------------------------------------------------------------ *)

Lemma ap_spine : forall st sr Ts,
  ap_typ st sr (spine Ts) = spine (map (ap_typ st sr) Ts).
Proof.
  intros st sr. induction Ts as [|T Ts IH]; simpl; [ reflexivity | rewrite IH; reflexivity ].
Qed.

Lemma ap_nth : forall st sr Ts j,
  ap_typ st sr (nth j Ts typ_Unit) = nth j (map (ap_typ st sr) Ts) typ_Unit.
Proof.
  intros st sr. induction Ts as [|T Ts IH]; intros [|j]; simpl; auto.
Qed.

Lemma ap_slot_ty : forall st sr w Ts c,
  ap_typ st sr (slot_ty w Ts c) = slot_ty w (map (ap_typ st sr) Ts) c.
Proof.
  intros st sr w Ts c. unfold slot_ty.
  destruct c as [|[|[|[|[|[|c]]]]]]; simpl; try reflexivity.
  - rewrite ap_spine. reflexivity.
  - rewrite ?Nat.sub_0_r. apply ap_nth.
Qed.

Lemma ap_slots_row : forall st sr w Ts cs i,
  ap_row st sr (slots_row w Ts i cs) = slots_row w (map (ap_typ st sr) Ts) i cs.
Proof.
  intros st sr w Ts cs. induction cs as [|c cs IH]; intros i; simpl;
    [ reflexivity | rewrite ap_slot_ty, IH; reflexivity ].
Qed.

Lemma ap_tag_payload : forall st sr w Ts tg,
  ap_typ st sr (tag_payload w Ts tg) = tag_payload w (map (ap_typ st sr) Ts) tg.
Proof.
  intros st sr w Ts tg. unfold tag_payload.
  destruct (nth_error w tg) as [cs|]; [ | reflexivity ].
  unfold payload_ty. destruct cs; [ reflexivity | ].
  cbn [ap_typ]. f_equal. apply ap_slots_row.
Qed.

(* ------------------------------------------------------------------ *)
(* Substituting into the arms of a match                                  *)
(* ------------------------------------------------------------------ *)

Lemma arms_idx_subst : forall u x ars,
  arms_idx (subst_arms u x ars) = arms_idx ars.
Proof. induction ars; simpl; congruence. Qed.

Lemma arms_find_subst_inv : forall u x ars tg b,
  arms_find tg (subst_arms u x ars) = Some b ->
  exists b0, b = subst_exp u x b0 /\ arms_find tg ars = Some b0.
Proof.
  induction ars as [|e|tg0 e ars IH]; simpl; intros tg b H; try discriminate.
  destruct (Nat.eqb tg tg0).
  - inversion H; subst. eexists; split; reflexivity.
  - apply IH. exact H.
Qed.

Lemma arms_default_subst_inv : forall u x ars e0,
  arms_default (subst_arms u x ars) = Some e0 ->
  exists e1, e0 = subst_exp u x e1 /\ arms_default ars = Some e1.
Proof.
  induction ars as [|e|tg0 e ars IH]; simpl; intros e0 H; try discriminate.
  - inversion H; subst. eexists; split; reflexivity.
  - apply IH. exact H.
Qed.

Lemma arms_default_subst_none : forall u x ars,
  arms_default (subst_arms u x ars) = None <-> arms_default ars = None.
Proof.
  induction ars as [|e|tg0 e ars IH]; simpl.
  - split; reflexivity.
  - split; intros H; discriminate H.
  - exact IH.
Qed.

Lemma arms_wf_subst : forall u x w ars,
  arms_wf w ars -> arms_wf w (subst_arms u x ars).
Proof.
  intros u x w ars (Hnd & Hlt & Hcov). unfold arms_wf.
  rewrite arms_idx_subst. split; [ exact Hnd | split; [ exact Hlt | ] ].
  destruct Hcov as [Hd | Hall]; [ left | right; exact Hall ].
  intros Hn. apply Hd. apply (proj1 (arms_default_subst_none u x ars)). exact Hn.
Qed.
