(* Iso-recursive types in the calculus (ADR 0037, decision 3;
   docs/design/recursive-types-plan.md).  The type algebra of the one new
   binder: unrolling ([open_typ]), local closure ([lct]), the guard predicate
   ([gd]), and how each interacts with type/row substitution and type
   equality.

   Two facts carry the metatheory.  Substitution commutes with unrolling when
   the substituted types have no free index ([ap_open_mut]).  Type equality
   respects unrolling, in the body and in the argument ([teq_open]); it has no
   unrolling equation, which is what makes the recursion iso.

   Assumption-free (no axioms, no admits). *)

Require Import Metalib.Metatheory.
Require Import Goat.Goat_ott.
Require Import Goat.GoatRows.
Require Import Goat.GoatDefs.
Require Import Stdlib.Arith.Compare_dec.
From Stdlib Require Import Lia.

(* ------------------------------------------------------------------ *)
(* A row that lacks a label still lacks it after a substitution or an   *)
(* unrolling: both rewrite the types in a spine and leave its labels     *)
(* alone, and a lacking row has no row variable to replace.               *)
(* ------------------------------------------------------------------ *)

Lemma rlacks_ap_mut : forall st sr l,
  (forall T : typ, True) /\
  (forall R, rlacks l R = true -> rlacks l (ap_row st sr R) = true).
Proof.
  intros st sr l.
  apply typ_row_mutind; simpl; intros; try exact I; try discriminate; auto.
  - apply Bool.andb_true_iff in H1 as [H1 H2]. rewrite H1. auto.
  - apply Bool.andb_true_iff in H2 as [H2 H3]. rewrite H2. auto.
Qed.

Lemma rlacks_ap : forall st sr l R,
  rlacks l R = true -> rlacks l (ap_row st sr R) = true.
Proof. intros. apply (proj2 (rlacks_ap_mut st sr l)); auto. Qed.

Lemma rlacks_open_mut : forall k U l,
  (forall T : typ, True) /\
  (forall R, rlacks l R = true -> rlacks l (open_row k U R) = true).
Proof.
  intros k U l.
  apply typ_row_mutind; simpl; intros; try exact I; try discriminate; auto.
  - apply Bool.andb_true_iff in H1 as [H1 H2]. rewrite H1. auto.
  - apply Bool.andb_true_iff in H2 as [H2 H3]. rewrite H2. auto.
Qed.

Lemma rlacks_open : forall k U l R,
  rlacks l R = true -> rlacks l (open_row k U R) = true.
Proof. intros. apply (proj2 (rlacks_open_mut k U l)); auto. Qed.

Lemma rmf_ap_mut : forall st sr l,
  (forall T : typ, True) /\
  (forall R T R0, rmf l R = Some (T, R0) ->
     rmf l (ap_row st sr R) = Some (ap_typ st sr T, ap_row st sr R0)).
Proof.
  intros st sr l.
  apply typ_row_mutind; try (intros; exact I).
  - intros T0 R0 H. simpl in H. discriminate.
  - intros r T0 R0 H. simpl in H. discriminate.
  - intros l0 T1 _ R1 IH T0 R0 H. simpl in H |- *.
    destruct (Nat.eqb l l0).
    + inversion H; subst. reflexivity.
    + destruct (rmf l R1) as [[T2 R2]|] eqn:E; [ | discriminate ].
      inversion H; subst. rewrite (IH _ _ eq_refl). reflexivity.
  - intros l0 P _ T1 _ R1 IH T0 R0 H. simpl in H |- *.
    destruct (Nat.eqb l l0).
    + destruct P; simpl in H; try discriminate. inversion H; subst. reflexivity.
    + destruct (rmf l R1) as [[T2 R2]|] eqn:E; [ | discriminate ].
      inversion H; subst. rewrite (IH _ _ eq_refl). reflexivity.
Qed.

Lemma rm_ap : forall st sr l R0 T R,
  rm l R0 T R -> rm l (ap_row st sr R0) (ap_typ st sr T) (ap_row st sr R).
Proof. intros. apply (proj2 (rmf_ap_mut st sr l)); auto. Qed.

(* ------------------------------------------------------------------ *)
(* Local closure                                                         *)
(* ------------------------------------------------------------------ *)

Lemma lc_mono_mut :
  (forall T k m, lct k T -> k <= m -> lct m T) /\
  (forall R k m, lcr k R -> k <= m -> lcr m R).
Proof.
  apply typ_row_mutind; simpl; intros; try tauto.
  - destruct H1; split; eauto.
  - eauto.
  - lia.
  - eapply H; eauto. lia.
  - eapply H; eauto.
  - destruct H1; split; eauto.
  - repeat match goal with H : _ /\ _ |- _ => destruct H end;
      repeat split; eauto.
Qed.

Lemma lct_mono : forall T k m, lct k T -> k <= m -> lct m T.
Proof. apply lc_mono_mut. Qed.

Lemma lcr_mono : forall R k m, lcr k R -> k <= m -> lcr m R.
Proof. apply lc_mono_mut. Qed.

(* Unrolling a closed type changes nothing. *)
Lemma open_closed_mut :
  (forall T k U, lct k T -> open_typ k U T = T) /\
  (forall R k U, lcr k R -> open_row k U R = R).
Proof.
  apply typ_row_mutind; simpl; intros; try reflexivity.
  - destruct H1. rewrite H, H0; auto.
  - rewrite H; auto.
  - destruct (lt_eq_lt_dec i k) as [[?|?]|?]; auto; lia.
  - rewrite H; auto.
  - rewrite H; auto.
  - destruct H1. rewrite H, H0; auto.
  - repeat match goal with H : _ /\ _ |- _ => destruct H end.
    rewrite H, H0, H1; auto.
Qed.

Lemma open_typ_closed : forall T k U, lct k T -> open_typ k U T = T.
Proof. apply open_closed_mut. Qed.

Lemma open_row_closed : forall R k U, lcr k R -> open_row k U R = R.
Proof. apply open_closed_mut. Qed.

(* The hardest lemma: substitution commutes with unrolling.  It needs the
   substitution to be locally closed, so that an index never leaks into the
   binder the substituted type is placed under. *)
Lemma ap_open_mut : forall st sr, lc_sub st sr ->
  (forall T k U, ap_typ st sr (open_typ k U T) = open_typ k (ap_typ st sr U) (ap_typ st sr T)) /\
  (forall R k U, ap_row st sr (open_row k U R) = open_row k (ap_typ st sr U) (ap_row st sr R)).
Proof.
  intros st sr [Hs Hr].
  apply typ_row_mutind; simpl; intros; try reflexivity.
  - rewrite H, H0; reflexivity.
  - rewrite H; reflexivity.
  - symmetry. apply open_typ_closed. eapply lct_mono; [ apply Hs | lia ].
  - destruct (lt_eq_lt_dec i k) as [[?|?]|?]; reflexivity.
  - rewrite H; reflexivity.
  - rewrite H; reflexivity.
  - symmetry. apply open_row_closed. eapply lcr_mono; [ apply Hr | lia ].
  - rewrite H, H0; reflexivity.
  - rewrite H, H0, H1; reflexivity.
Qed.

Lemma ap_open : forall st sr T k U, lc_sub st sr ->
  ap_typ st sr (open_typ k U T) = open_typ k (ap_typ st sr U) (ap_typ st sr T).
Proof. intros. apply (proj1 (ap_open_mut st sr H)). Qed.

Lemma ap_lc_mut : forall st sr, lc_sub st sr ->
  (forall T k, lct k T -> lct k (ap_typ st sr T)) /\
  (forall R k, lcr k R -> lcr k (ap_row st sr R)).
Proof.
  intros st sr [Hs Hr].
  apply typ_row_mutind; simpl; intros;
    repeat match goal with H : _ /\ _ |- _ => destruct H end;
    try split; auto;
    first [ eapply lct_mono; [ apply Hs | lia ]
          | eapply lcr_mono; [ apply Hr | lia ] ].
Qed.

Lemma ap_lc : forall st sr T k, lc_sub st sr -> lct k T -> lct k (ap_typ st sr T).
Proof. intros. apply (proj1 (ap_lc_mut st sr H)); auto. Qed.

Lemma ap_lcr : forall st sr R k, lc_sub st sr -> lcr k R -> lcr k (ap_row st sr R).
Proof. intros. apply (proj2 (ap_lc_mut st sr H)); auto. Qed.

Lemma lc_sub_id : lc_sub idt idr.
Proof. split; intros; simpl; exact I. Qed.

Lemma lc_sub_comp : forall st sr st0 sr0,
  lc_sub st sr -> lc_sub st0 sr0 ->
  lc_sub (fun a => ap_typ st sr (st0 a)) (fun r => ap_row st sr (sr0 r)).
Proof.
  intros st sr st0 sr0 H [H1 H2]. split; intros.
  - apply ap_lc; auto.
  - apply ap_lcr; auto.
Qed.

(* ------------------------------------------------------------------ *)
(* Type equality and unrolling                                           *)
(* ------------------------------------------------------------------ *)

(* Equality respects unrolling in the body ... *)
Lemma teq_open_body_mut : forall U,
  (forall T T', teq T T' -> forall k, teq (open_typ k U T) (open_typ k U T')) /\
  (forall R R', req R R' -> forall k, req (open_row k U R) (open_row k U R')).
Proof.
  intros U.
  apply teq_req_mutind; simpl; intros; eauto using teq_refl, rlacks_open.
Qed.

(* ... and in the argument. *)
Lemma teq_open_arg_mut :
  (forall T k U U', teq U U' -> teq (open_typ k U T) (open_typ k U' T)) /\
  (forall R k U U', teq U U' -> req (open_row k U R) (open_row k U' R)).
Proof.
  apply typ_row_mutind; simpl; intros; auto using teq_refl, req_refl.
  destruct (lt_eq_lt_dec i k) as [[?|?]|?]; auto using teq_refl.
Qed.

Lemma teq_open : forall T T' U U' k,
  teq T T' -> teq U U' -> teq (open_typ k U T) (open_typ k U' T').
Proof.
  intros. eapply teq_trans.
  - apply (proj1 (teq_open_body_mut U)); eauto.
  - apply (proj1 teq_open_arg_mut); auto.
Qed.

(* The unrolling of equal recursive types is equal. *)
Lemma teq_unroll : forall B B',
  teq (typ_Mu B) (typ_Mu B') -> teq (open_typ 0 (typ_Mu B) B) (open_typ 0 (typ_Mu B') B').
Proof.
  intros B B' H. destruct (teq_Mu_inv _ _ H) as [B'' [E Hb]]. inversion E; subst.
  apply teq_open; auto.
Qed.

(* ------------------------------------------------------------------ *)
(* The guard                                                             *)
(* ------------------------------------------------------------------ *)

(* A type that never reaches the index has no mention to guard. *)
Lemma gd_closed_mut :
  (forall T k m, lct m T -> m <= k -> forall r f, gd r f k T) /\
  (forall R k m, lcr m R -> m <= k -> forall r f, gdr r f k R).
Proof.
  apply typ_row_mutind; simpl; intros; try tauto.
  - destruct H1. split; [ eapply H | eapply H0 ]; eauto.
  - eapply H; eauto.
  - exfalso. lia.
  - eapply H; [ eassumption | lia ].
  - eapply H; eauto.
  - destruct H1. split; [ eapply H | eapply H0 ]; eauto.
  - repeat match goal with H : _ /\ _ |- _ => destruct H end.
    repeat split; [ eapply H | right; eapply H0 | eapply H1 ]; eauto.
Qed.

Lemma gd_ap_mut : forall st sr, lc_sub st sr ->
  (forall T r f k, gd r f k T -> gd r f k (ap_typ st sr T)) /\
  (forall R r f k, gdr r f k R -> gdr r f k (ap_row st sr R)).
Proof.
  intros st sr [Hs Hr].
  apply typ_row_mutind; simpl; intros; try exact I.
  - destruct H1. split; eauto.
  - eauto.
  - eapply (proj1 gd_closed_mut); [ apply Hs | lia ].
  - exact (H H0).
  - eapply H; eauto.
  - eauto.
  - eapply (proj2 gd_closed_mut); [ apply Hr | lia ].
  - destruct H1. split; eauto.
  - repeat match goal with H : _ /\ _ |- _ => destruct H end.
    repeat split; [ eauto | | eauto ].
    match goal with
    | Ha : is_abs ?P = true \/ _ |- _ =>
        destruct Ha as [Ha | Hb];
        [ left; destruct P; simpl in Ha; try discriminate; reflexivity
        | right; eauto ]
    end.
Qed.

Lemma guarded_ap : forall st sr B,
  lc_sub st sr -> guarded B -> guarded (ap_typ st sr B).
Proof. intros. apply (proj1 (gd_ap_mut st sr H)); auto. Qed.

(* Equal types are guarded alike, so the guard cannot be dodged by a
   conversion.  The row rules only reorder or relate fields, and the guard
   asks the same of every field. *)
Lemma gd_teq_mut :
  (forall T T', teq T T' -> forall r f k, gd r f k T <-> gd r f k T') /\
  (forall R R', req R R' -> forall r f k, gdr r f k R <-> gdr r f k R').
Proof.
  apply teq_req_mutind; simpl; try (intros; tauto).
  - intros A B A' B' _ IH1 _ IH2 rr ff kk. rewrite (IH1 rr true kk), (IH2 rr true kk). tauto.
  - intros A A' _ IH rr ff kk. apply IH.
  - intros w A A' _ IH rr ff kk. apply IH.
  - intros R R' _ IH rr ff kk. apply IH.
  - intros A C B _ IH1 _ IH2 rr ff kk. rewrite (IH1 rr ff kk). apply IH2.
  - intros A B _ IH rr ff kk. symmetry. apply IH.
  - intros l T T' R R' _ IH1 _ IH2 rr ff kk. rewrite (IH1 rr ff kk), (IH2 rr ff kk). tauto.
  - intros l P T R P' T' R' H1 IH1 _ IH2 _ IH3 rr ff kk.
    rewrite (teq_is_abs _ _ H1), (IH1 rr ff kk), (IH2 rr ff kk), (IH3 rr ff kk). tauto.
  - intros l T R rr ff kk.
    split; [ intros [_ [[Hd | Hd] H]]; [ discriminate | split; assumption ]
           | intros [Hd H]; split; [ exact I | split; [ right; exact Hd | exact H ] ] ].
  - intros A C B _ IH1 _ IH2 rr ff kk. rewrite (IH1 rr ff kk). apply IH2.
  - intros A B _ IH rr ff kk. symmetry. apply IH.
Qed.

Lemma guarded_teq : forall B B', teq B B' -> guarded B -> guarded B'.
Proof. intros B B' H. apply (proj1 gd_teq_mut B B' H). Qed.
