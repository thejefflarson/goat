(* [sat] does not tell [teq] types apart.  A presence entry at [Unit] is a field
   ([req_pre]) and one at [Bool] is no field ([req_abs]), and [rsat] reads
   them that way, so a sort holds of a type exactly when it holds of every type
   [teq] to it.  Completeness needs this: a sorted variable may be sent to any
   representative of a type's class.  Axiom- and admit-free. *)

Require Import Metalib.Metatheory.
Require Import Goat.Goat_ott.
Require Import Goat.GoatRows.
Require Import Goat.GoatDefs.

Lemma presence_bool_teq : forall P P', teq P P' -> (P = typ_Bool <-> P' = typ_Bool).
Proof.
  intros P P' H. split; intros E; subst.
  - exact (teq_Bool_inv _ H).
  - exact (teq_Bool_inv _ (teq_sym _ _ H)).
Qed.

Lemma sat_teq_mut : forall D,
  (forall T T', teq T T' ->
     (forall k, sat D k T <-> sat D k T') /\
     (forall w j, spine_sat D w j T <-> spine_sat D w j T')) /\
  (forall R R', req R R' -> forall k, rsat D k R <-> rsat D k R').
Proof.
  intros D. apply teq_req_mutind; simpl.
  - split; intros; tauto.
  - split; intros; tauto.
  - split; intros; tauto.
  - split; intros; tauto.
  - split; intros; tauto.
  - intros a. split; intros; tauto.
  - intros T1 T2 T1' T2' _ [IH1 _] _ [_ IH2]. split; [ intros; tauto | ].
    intros w j. rewrite (IH2 w (S j)).
    split; intros [Hu Hs]; split; [ | tauto | | tauto ]; intros Hc;
      [ apply (proj1 (IH1 k_Eq)) | apply (proj2 (IH1 k_Eq)) ]; apply Hu; exact Hc.
  - intros i. split; intros; tauto.
  - intros T T' _ [IH _]. split; [ | intros; tauto ].
    intros k. destruct k; first [ exact (IH k_Eq) | tauto ].
  - intros w T T' _ [_ IH]. split; [ | intros; tauto ].
    intros k. destruct k; first [ exact (IH w 0) | tauto ].
  - intros R R' _ IH. split; [ | intros; tauto ].
    intros k. destruct k; try tauto; exact (IH _).
  - intros T1 T3 T2 _ [IH12 IH12'] _ [IH23 IH23']. split.
    + intros k. rewrite (IH12 k). apply IH23.
    + intros w j. rewrite (IH12' w j). apply IH23'.
  - intros T2 T1 _ [IH IH']. split.
    + intros k. symmetry. apply IH.
    + intros w j. symmetry. apply IH'.
  - intros k. tauto.
  - intros r k. tauto.
  - intros l T T' R R' _ [IHT _] _ IHR k. rewrite (IHT k), (IHR k). tauto.
  - intros l T l' T' R _ k. tauto.
  - intros l P T R P' T' R' HP _ _ [IHT _] _ IHR k.
    rewrite (presence_bool_teq _ _ HP), (IHT k), (IHR k). tauto.
  - intros l T R k. split.
    + intros [[H | H] H2]; [ discriminate H | split; assumption ].
    + intros [H H2]. split; [ right; exact H | exact H2 ].
  - intros l T R _ k. split.
    + intros [_ H]. exact H.
    + intros H. split; [ left; reflexivity | exact H ].
  - intros l T T' R k. split; intros [_ H]; (split; [ left; reflexivity | exact H ]).
  - intros l T1 T l' T' R _ k. tauto.
  - intros l T1 T l' T1' T' R _ k. tauto.
  - intros R1 R3 R2 _ IH12 _ IH23 k. rewrite (IH12 k). apply IH23.
  - intros R2 R1 _ IH k. symmetry. apply IH.
Qed.

Lemma sat_teq : forall D k T T', teq T T' -> sat D k T -> sat D k T'.
Proof. intros D k T T' H Hs. exact (proj1 (proj1 (proj1 (sat_teq_mut D) T T' H) k) Hs). Qed.

Lemma rsat_req : forall D k R R', req R R' -> rsat D k R -> rsat D k R'.
Proof. intros D k R R' H Hs. exact (proj1 (proj2 (sat_teq_mut D) R R' H k) Hs). Qed.
