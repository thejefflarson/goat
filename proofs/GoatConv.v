(* Conversion at a row environment ([teqD], GoatDefs.v): the equivalence
   relation, its head-shape inversions, and the characterizations of
   [Record] and tag-group types that the canonical-forms and preservation
   proofs read.  [nfT D] only rewrites inside arrows and records, so every
   inversion on a non-record, non-arrow head is [teq]'s own.

   Axiom- and admit-free. *)

Require Import Metalib.Metatheory.
Require Import Goat.Goat_ott.
Require Import Goat.GoatRows.
Require Import Goat.GoatDefs.
Require Import Goat.GoatPresence.
Require Import Goat.GoatRecArith.
Require Import Stdlib.Lists.List.

Lemma teqD_refl : forall D T, teqD D T T.
Proof. intros. apply teq_refl. Qed.

Lemma teqD_sym : forall D T T', teqD D T T' -> teqD D T' T.
Proof. intros. apply teq_sym. assumption. Qed.

Lemma teqD_trans : forall D T1 T2 T3, teqD D T1 T2 -> teqD D T2 T3 -> teqD D T1 T3.
Proof. intros. eapply teq_trans; eassumption. Qed.

#[export] Hint Resolve teqD_refl teq_teqD : core.

Lemma nfT_thead : forall D T, thead_tag (nfT D T) = thead_tag T.
Proof. intros. destruct T; reflexivity. Qed.

Lemma teqD_thead : forall D T T', teqD D T T' -> thead_tag T = thead_tag T'.
Proof.
  intros D T T' H. apply teq_thead in H. rewrite !nfT_thead in H. exact H.
Qed.

(* A type that [nfT D] sends to anything but an arrow or a record is its
   own normal form. *)
Lemma nfT_other : forall D T,
  (forall A B, T <> typ_Arrow A B) -> (forall R, T <> typ_Record R) -> nfT D T = T.
Proof.
  intros D T Ha Hr. destruct T; try reflexivity.
  - exfalso. eapply Ha; reflexivity.
  - exfalso. eapply Hr; reflexivity.
Qed.

Lemma nfT_Arrow_inv : forall D T A B, nfT D T = typ_Arrow A B ->
  exists A0 B0, T = typ_Arrow A0 B0 /\ nfT D A0 = A /\ nfT D B0 = B.
Proof.
  intros D T A B H. destruct T; simpl in H; try discriminate.
  inversion H; subst. eexists; eexists; repeat split; reflexivity.
Qed.

Lemma nfT_Record_inv : forall D T R, nfT D T = typ_Record R ->
  exists R0, T = typ_Record R0 /\ nfR D R0 = R.
Proof.
  intros D T R H. destruct T; simpl in H; try discriminate.
  inversion H; subst. eexists; split; reflexivity.
Qed.

Lemma teqD_Arrow_inv : forall D A B T, teqD D (typ_Arrow A B) T ->
  exists A' B', T = typ_Arrow A' B' /\ teqD D A A' /\ teqD D B B'.
Proof.
  intros D A B T H. unfold teqD in H. cbn [nfT] in H.
  destruct (teq_Arrow_inv _ _ _ H) as (A2 & B2 & E & H1 & H2).
  destruct (nfT_Arrow_inv _ _ _ _ E) as (A0 & B0 & -> & EA & EB).
  exists A0, B0. split; [ reflexivity | ]. split; unfold teqD; [ rewrite EA | rewrite EB ]; assumption.
Qed.

Lemma teqD_Arrow : forall D A B A' B',
  teqD D A A' -> teqD D B B' -> teqD D (typ_Arrow A B) (typ_Arrow A' B').
Proof. intros. unfold teqD in *. cbn [nfT]. apply teq_arrow; assumption. Qed.

Lemma teqD_Record_inv : forall D R T, teqD D (typ_Record R) T ->
  exists R', T = typ_Record R' /\ req (nfR D R) (nfR D R').
Proof.
  intros D R T H. unfold teqD in H. cbn [nfT] in H.
  destruct (teq_Record_inv _ _ H) as (R2 & E & Hq).
  destruct (nfT_Record_inv _ _ _ E) as (R0 & -> & ER).
  exists R0. split; [ reflexivity | rewrite ER; exact Hq ].
Qed.

Lemma teqD_Record : forall D R R', req (nfR D R) (nfR D R') ->
  teqD D (typ_Record R) (typ_Record R').
Proof. intros. unfold teqD. cbn [nfT]. apply teq_rec; assumption. Qed.

Lemma teqD_Mu_inv : forall D B T, teqD D (typ_Mu B) T ->
  exists B', T = typ_Mu B' /\ teq B B'.
Proof.
  intros D B T H. unfold teqD in H. cbn [nfT] in H.
  destruct (teq_Mu_inv _ _ H) as (B2 & E & Hq).
  destruct T; simpl in E; try discriminate. inversion E; subst. eexists; split; [ reflexivity | exact Hq ].
Qed.

Lemma teqD_Grp_inv : forall D w A T, teqD D (typ_Grp w A) T ->
  exists A', T = typ_Grp w A' /\ teq A A'.
Proof.
  intros D w A T H. unfold teqD in H. cbn [nfT] in H.
  destruct (teq_Grp_inv _ _ _ H) as (A2 & E & Hq).
  destruct T; simpl in E; try discriminate. inversion E; subst. eexists; split; [ reflexivity | exact Hq ].
Qed.

Lemma teqD_Mu : forall D B B', teq B B' -> teqD D (typ_Mu B) (typ_Mu B').
Proof. intros. apply teq_teqD. apply teq_mu. assumption. Qed.

Lemma teqD_Grp : forall D w A A', teq A A' -> teqD D (typ_Grp w A) (typ_Grp w A').
Proof. intros. apply teq_teqD. apply teq_grp. assumption. Qed.

(* A base type is equal only to itself, and a variable only to itself. *)
Lemma teqD_Int_inv : forall D T, teqD D typ_Int T -> T = typ_Int.
Proof.
  intros D T H. apply teqD_thead in H. simpl in H. destruct T; simpl in H; try discriminate; reflexivity.
Qed.

Lemma teqD_Float_inv : forall D T, teqD D typ_Float T -> T = typ_Float.
Proof.
  intros D T H. apply teqD_thead in H. simpl in H. destruct T; simpl in H; try discriminate; reflexivity.
Qed.

Lemma teqD_Bool_inv : forall D T, teqD D typ_Bool T -> T = typ_Bool.
Proof.
  intros D T H. apply teqD_thead in H. simpl in H. destruct T; simpl in H; try discriminate; reflexivity.
Qed.

Lemma teqD_Unit_inv : forall D T, teqD D typ_Unit T -> T = typ_Unit.
Proof.
  intros D T H. apply teqD_thead in H. simpl in H. destruct T; simpl in H; try discriminate; reflexivity.
Qed.

Lemma teqD_String_inv : forall D T, teqD D typ_String T -> T = typ_String.
Proof.
  intros D T H. apply teqD_thead in H. simpl in H. destruct T; simpl in H; try discriminate; reflexivity.
Qed.

(* The same for rows. *)
Definition reqD (D : denv) (R R' : row) : Prop := req (nfR D R) (nfR D R').

Lemma reqD_refl : forall D R, reqD D R R.
Proof. intros. apply req_refl. Qed.

Lemma reqD_sym : forall D R R', reqD D R R' -> reqD D R' R.
Proof. intros. apply req_sym. assumption. Qed.

Lemma reqD_trans : forall D R1 R2 R3, reqD D R1 R2 -> reqD D R2 R3 -> reqD D R1 R3.
Proof. intros. eapply req_trans; eassumption. Qed.

Lemma req_reqD : forall D R R', req R R' -> reqD D R R'.
Proof. intros. apply (proj2 teq_nf_mut). assumption. Qed.

#[export] Hint Resolve reqD_refl req_reqD : core.

Lemma teqD_Record_reqD : forall D R R', reqD D R R' -> teqD D (typ_Record R) (typ_Record R').
Proof. intros. apply teqD_Record. assumption. Qed.

Lemma nfT_is_unit : forall D T, is_unit (nfT D T) = is_unit T.
Proof. intros. destruct T; reflexivity. Qed.

(* The present fields of a row are the same before and after normalizing,
   up to the normal form of each field's type. *)
Lemma pi_nf : forall D l R, pi l (nfR D R) = map (nfT D) (pi l R).
Proof.
  intros D l. induction R as [ | | l0 t R IHR | l0 t t0 R IHR]; try reflexivity.
  - cbn [nfR pi]. destruct (Nat.eqb l l0); [ cbn [map]; rewrite IHR; reflexivity | exact IHR ].
  - rewrite nfR_maybe. destruct (is_abs t && rlacksD D l0 (nfR D R)) eqn:E.
    + apply andb_prop in E as [Ha _]. cbn [pi]. destruct t; cbn in Ha; try discriminate.
      cbn [is_unit]. rewrite Bool.andb_false_r. exact IHR.
    + cbn [pi]. rewrite nfT_is_unit. destruct (Nat.eqb l l0 && is_unit t);
        [ cbn [map]; rewrite IHR; reflexivity | exact IHR ].
Qed.

Lemma teqD_Mu_teq : forall D B B', teqD D (typ_Mu B) (typ_Mu B') -> teq (typ_Mu B) (typ_Mu B').
Proof. intros. exact H. Qed.

Lemma teqD_Grp_teq : forall D w A A', teqD D (typ_Grp w A) (typ_Grp w A') -> teq A A'.
Proof.
  intros D w A A' H. destruct (teq_Grp_inv _ _ _ H) as (A2 & E & Hq).
  inversion E; subst. exact Hq.
Qed.

(* Normalizing twice is normalizing once, so a type is converted to its own
   normal form. *)
Lemma nf_idem_mut : forall D,
  (forall T, nfT D (nfT D T) = nfT D T) /\ (forall R, nfR D (nfR D R) = nfR D R).
Proof.
  intros D. apply typ_row_mutind.
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - intros A HA B HB. cbn [nfT]. rewrite HA, HB. reflexivity.
  - intros R HR. cbn [nfT]. rewrite HR. reflexivity.
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - intros l T HT R HR. rewrite nfR_ext, nfR_ext, HT, HR. reflexivity.
  - intros l P HP T HT R HR. rewrite nfR_maybe.
    destruct (is_abs P && rlacksD D l (nfR D R)) eqn:E.
    + cbv iota. exact HR.
    + cbv iota. rewrite nfR_maybe, HR, nfT_is_abs, E.
      cbv iota. rewrite HP, HT. reflexivity.
Qed.

Lemma nfT_idem : forall D T, nfT D (nfT D T) = nfT D T.
Proof. intros. apply (proj1 (nf_idem_mut D)). Qed.

Lemma nfR_idem : forall D R, nfR D (nfR D R) = nfR D R.
Proof. intros. apply (proj2 (nf_idem_mut D)). Qed.

Lemma teqD_nf : forall D T, teqD D T (nfT D T).
Proof. intros. unfold teqD. rewrite nfT_idem. apply teq_refl. Qed.

Lemma reqD_nf : forall D R, reqD D R (nfR D R).
Proof. intros. unfold reqD. rewrite nfR_idem. apply req_refl. Qed.

(* The sorts see only the fields: an absent entry satisfies every sort. *)
Lemma sat_nf_mut : forall D k,
  (forall T, sat D k (nfT D T) <-> sat D k T) /\ (forall R, rsat D k (nfR D R) <-> rsat D k R).
Proof.
  intros D k. apply typ_row_mutind.
  - tauto.
  - tauto.
  - tauto.
  - tauto.
  - tauto.
  - intros A HA B HB. cbn [nfT sat]. tauto.
  - intros R HR. cbn [nfT sat]. destruct k; tauto.
  - tauto.
  - tauto.
  - tauto.
  - tauto.
  - tauto.
  - tauto.
  - intros l T HT R HR. rewrite nfR_ext. cbn [rsat]. rewrite HT, HR. tauto.
  - intros l P HP T HT R HR. rewrite nfR_maybe.
    destruct (is_abs P && rlacksD D l (nfR D R)) eqn:E.
    + cbv iota. apply andb_prop in E as [Ea _]. destruct P; cbn in Ea; try discriminate.
      cbn [rsat]. rewrite HR. tauto.
    + cbv iota. cbn [rsat]. rewrite HR, HT.
      assert (Hp : nfT D P = typ_Bool <-> P = typ_Bool)
        by (destruct P; cbn; split; intros; congruence).
      tauto.
Qed.

Lemma sat_nf : forall D k T, sat D k (nfT D T) <-> sat D k T.
Proof. intros. apply (proj1 (sat_nf_mut D k)). Qed.

Lemma rsat_nf : forall D k R, rsat D k (nfR D R) <-> rsat D k R.
Proof. intros. apply (proj2 (sat_nf_mut D k)). Qed.

(* A record literal's row, with each field at its normal form. *)
Lemma field_typing_nf : forall D G fs R,
  field_typing D G fs R -> field_typing D G fs (nfR D R).
Proof.
  intros D G fs R H. induction H.
  - apply FT_nil; assumption.
  - rewrite nfR_ext. apply FT_cons; [ | assumption ].
    eapply T_ConvD; [ eassumption | apply teqD_nf ].
  - rewrite nfR_ext. apply FT_meth; [ | assumption ].
    eapply T_ConvD; [ eassumption | apply teqD_nf ].
Qed.

(* The operator signatures see only the fields too. *)
Lemma fsat_nf_mut : forall D,
  (forall T, fsat T -> fsat (nfT D T)) /\ (forall R, rfsat R -> rfsat (nfR D R)).
Proof.
  intros D. apply typ_row_mutind.
  - intros H; contradiction.
  - intros _; exact I.
  - intros H; contradiction.
  - intros H; contradiction.
  - intros H; contradiction.
  - intros A HA B HB H; contradiction.
  - intros R HR H. cbn [nfT fsat] in *. apply HR. exact H.
  - intros a H; contradiction.
  - intros i H; contradiction.
  - intros B HB H; contradiction.
  - intros w B HB H; contradiction.
  - intros _; exact I.
  - intros r H; contradiction.
  - intros l T HT R HR H. cbn [rfsat] in H. destruct H as [H1 H2].
    rewrite nfR_ext. cbn [rfsat]. split; auto.
  - intros l P HP T HT R HR H; contradiction.
Qed.

Lemma bin_sig_nf : forall D o A B R,
  bin_sig D o A B R -> bin_sig D o (nfT D A) (nfT D B) (nfT D R).
Proof.
  intros D o A B R H. inversion H; subst; cbn [nfT].
  - apply sig_ring; [ assumption | apply sat_nf; assumption ].
  - apply sig_quot.
  - apply sig_whole; [ assumption | apply sat_nf; assumption ].
  - apply sig_quot_rec. apply (proj2 (fsat_nf_mut D)). assumption.
  - apply sig_cmp; [ assumption | apply sat_nf; assumption ].
Qed.

Lemma row_sig_nf : forall D o R, row_sig D o R -> row_sig D o (nfR D R).
Proof.
  intros D o R. induction R using row_ind4; intros H.
  - exact I.
  - exact H.
  - rewrite nfR_ext. cbn [row_sig] in *. destruct H as [H1 H2]. split;
      [ apply bin_sig_nf in H1; exact H1 | auto ].
  - rewrite nfR_maybe. cbn [row_sig] in H. destruct H as [H1 H2].
    destruct (is_abs p && rlacksD D l (nfR D R)).
    + cbv iota. auto.
    + cbv iota. cbn [row_sig]. split; [ | auto ].
      destruct H1 as [H1 | H1]; [ left; destruct p; cbn in *; congruence | right ].
      apply bin_sig_nf in H1. exact H1.
Qed.

Lemma map_cons_inv : forall (A B : Type) (f : A -> B) xs y ys,
  map f xs = y :: ys -> exists x xs', xs = x :: xs' /\ f x = y /\ map f xs' = ys.
Proof.
  intros A B f xs y ys H. destruct xs as [ | x xs']; simpl in H; [ discriminate | ].
  injection H as H1 H2. exists x, xs'. auto.
Qed.

Lemma map_nil_inv : forall (A B : Type) (f : A -> B) xs, map f xs = nil -> xs = nil.
Proof. intros A B f xs H. destruct xs; [ reflexivity | discriminate H ]. Qed.

(* A record whose row is equivalent to [l : T ; R'] has an [l] field, and
   its first one has the type [T] up to conversion. *)
Lemma teqD_Record_pi : forall D R l T R',
  teqD D (typ_Record R) (typ_Record (row_Ext l T R')) ->
  exists T0 rest, pi l R = T0 :: rest /\ teqD D T0 T.
Proof.
  intros D R l T R' H. apply teqD_Record_inv in H as (R2 & E & Hq). injection E as <-.
  rewrite nfR_ext in Hq. destruct (req_surface _ _ _ _ Hq) as (T1 & rest & Hpi & Ht).
  rewrite pi_nf in Hpi. destruct (map_cons_inv _ _ _ _ _ _ Hpi) as (T0 & rest0 & E0 & E1 & _).
  exists T0, rest0. split; [ exact E0 | ]. unfold teqD. rewrite E1. exact Ht.
Qed.
