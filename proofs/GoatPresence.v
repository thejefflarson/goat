(* Presence rows (ADR 0033, docs/design/phase4-proof-plan.md).  A [Maybe]
   entry [l ^ P : T ; R] holds the field [l] at [T] when its presence [P] is
   [Unit], holds none when [P] is [Bool] and [R] lacks [l], and is stuck
   otherwise (a variable, an ill-sorted type).

   Preservation of a spread asks one question of the row equivalence: when a
   record literal's row [Rf] is equivalent to [l ^ P : T ; R], which is [P]?
   [presence_inv] answers: [Unit], or [Bool] with [Rf] equivalent to [R] and
   no [l] in [Rf].  The proof normalizes both rows ([nf]: a [Unit] entry
   becomes a field, a [Bool] entry whose normalized tail lacks its label is
   dropped), shows normalizing commutes with every [req] rule up to [req0] (the
   rules that do not mention [pre] or [abs]), and counts the [Maybe] entries
   that remain, which a literal's row does not have.

   Axiom- and admit-free. *)

Require Import Metalib.Metatheory.
Require Import Goat.Goat_ott.
Require Import Goat.GoatRows.
Require Import Goat.GoatDefs.
Require Import Stdlib.Lists.List.

(* The old relation: congruence and the swaps, with no [pre] or [abs]. *)
Inductive req0 : row -> row -> Prop :=
 | r0_empty : req0 row_Empty row_Empty
 | r0_var : forall r, req0 (row_Var r) (row_Var r)
 | r0_head : forall l T R T' R',
     teq T T' -> req0 R R' -> req0 (row_Ext l T R) (row_Ext l T' R')
 | r0_swap : forall l T l' T' R,
     l <> l' ->
     req0 (row_Ext l T (row_Ext l' T' R)) (row_Ext l' T' (row_Ext l T R))
 | r0_maybe : forall l P T R P' T' R',
     teq P P' -> teq T T' -> req0 R R' ->
     req0 (row_Maybe l P T R) (row_Maybe l P' T' R')
 | r0_swap_em : forall l P T l' T' R,
     l <> l' ->
     req0 (row_Maybe l P T (row_Ext l' T' R)) (row_Ext l' T' (row_Maybe l P T R))
 | r0_swap_mm : forall l P T l' P' T' R,
     l <> l' ->
     req0 (row_Maybe l P T (row_Maybe l' P' T' R))
          (row_Maybe l' P' T' (row_Maybe l P T R))
 | r0_trans : forall R1 R2 R3, req0 R1 R2 -> req0 R2 R3 -> req0 R1 R3
 | r0_sym : forall R1 R2, req0 R1 R2 -> req0 R2 R1.

#[export] Hint Constructors req0 : core.

Lemma req0_req : forall R1 R2, req0 R1 R2 -> req R1 R2.
Proof.
  induction 1; eauto using req_empty, req_var, req_head, req_swap, req_maybe,
    req_swap_em, req_swap_mm, req_trans, req_sym.
Qed.

(* Reflexivity, as for [req]: induction on the row. *)
Lemma req0_refl_mut :
  (forall T : typ, True) /\ (forall R : row, req0 R R).
Proof.
  apply typ_row_mutind; intros; try exact I; eauto using teq_refl.
Qed.

Lemma req0_refl : forall R, req0 R R.
Proof. intros. apply (proj2 req0_refl_mut). Qed.

#[export] Hint Resolve req0_refl : core.

(* The number of [Maybe] entries is invariant under [req0]. *)
Fixpoint nmaybe (R : row) : nat :=
  match R with
  | row_Empty | row_Var _ => 0
  | row_Ext _ _ R' => nmaybe R'
  | row_Maybe _ _ _ R' => S (nmaybe R')
  end.

Lemma req0_nmaybe : forall R1 R2, req0 R1 R2 -> nmaybe R1 = nmaybe R2.
Proof. induction 1; simpl; congruence. Qed.

(* [rlacks] is invariant under [req0]. *)
Lemma req0_rlacks : forall R1 R2, req0 R1 R2 -> forall l, rlacks l R1 = rlacks l R2.
Proof.
  induction 1; intros l0; simpl.
  - reflexivity.
  - reflexivity.
  - rewrite (IHreq0 l0). reflexivity.
  - destruct (Nat.eqb l0 l) eqn:E1; destruct (Nat.eqb l0 l') eqn:E2; simpl;
      try reflexivity.
  - rewrite (IHreq0 l0). reflexivity.
  - destruct (Nat.eqb l0 l) eqn:E1; destruct (Nat.eqb l0 l') eqn:E2; simpl;
      try reflexivity.
  - destruct (Nat.eqb l0 l) eqn:E1; destruct (Nat.eqb l0 l') eqn:E2; simpl;
      try reflexivity.
  - rewrite (IHreq0_1 l0). apply IHreq0_2.
  - symmetry. apply IHreq0.
Qed.

(* PART2 *)
(* ------------------------------------------------------------------ *)
(* The normalizer.                                                       *)
(* ------------------------------------------------------------------ *)

Definition nfm (l : label) (P T : typ) (R : row) : row :=
  match P with
  | typ_Unit => row_Ext l T R
  | typ_Bool => if rlacks l R then R else row_Maybe l P T R
  | _ => row_Maybe l P T R
  end.

Fixpoint nf (R : row) : row :=
  match R with
  | row_Empty => row_Empty
  | row_Var r => row_Var r
  | row_Ext l T R' => row_Ext l T (nf R')
  | row_Maybe l P T R' => nfm l P T (nf R')
  end.

Lemma nfm_req : forall l P T R R'',
  req R R'' -> req (row_Maybe l P T R) (nfm l P T R'').
Proof.
  intros l P T R R'' H.
  assert (Hc : req (row_Maybe l P T R) (row_Maybe l P T R''))
    by (apply req_maybe; auto using teq_refl).
  destruct P; simpl; try exact Hc.
  - destruct (rlacks l R'') eqn:E.
    + eapply req_trans; [ exact Hc | apply req_abs; exact E ].
    + exact Hc.
  - eapply req_trans; [ exact Hc | apply req_pre ].
Qed.

Lemma nf_req_mut :
  (forall T : typ, True) /\ (forall R : row, req R (nf R)).
Proof.
  apply typ_row_mutind; intros; try exact I; simpl; eauto using req_refl, req_head, teq_refl.
  apply nfm_req. assumption.
Qed.

Lemma nf_req : forall R, req R (nf R).
Proof. intros. apply (proj2 nf_req_mut). Qed.

Lemma nf_nomaybe_mut :
  (forall T : typ, True) /\ (forall R : row, nmaybe R = 0 -> nf R = R).
Proof.
  apply typ_row_mutind; intros; try exact I; simpl in *; try reflexivity.
  - rewrite H0; auto.
  - discriminate.
Qed.

Lemma nf_nomaybe : forall R, nmaybe R = 0 -> nf R = R.
Proof. intros. apply (proj2 nf_nomaybe_mut); auto. Qed.

(* A lacking row stays lacking once normalized. *)
Lemma rlacks_nf_mut :
  (forall T : typ, True) /\
  (forall R : row, forall l, rlacks l R = true -> rlacks l (nf R) = true).
Proof.
  apply typ_row_mutind; intros; try exact I; simpl in *; try reflexivity.
  - discriminate.
  - apply Bool.andb_true_iff in H1 as [H1 H2]. rewrite H1. simpl. auto.
  - apply Bool.andb_true_iff in H2 as [H2 H3].
    specialize (H1 l0 H3).
    destruct T1; simpl; try (rewrite H2, H1; reflexivity).
    destruct (rlacks l (nf R)); [ exact H1 | simpl; rewrite H2, H1; reflexivity ].
Qed.

Lemma rlacks_nf : forall R l, rlacks l R = true -> rlacks l (nf R) = true.
Proof. intros. apply (proj2 rlacks_nf_mut); auto. Qed.

(* PART3 *)
Lemma nfm_cong : forall l P P' T T' R R',
  teq P P' -> teq T T' -> req0 R R' -> req0 (nfm l P T R) (nfm l P' T' R').
Proof.
  intros l P P' T T' R R' HP HT HR.
  assert (Hl := req0_rlacks _ _ HR l).
  destruct P; destruct P'; simpl;
    try (apply teq_thead in HP; simpl in HP; discriminate);
    try (apply r0_maybe; assumption).
  - rewrite <- Hl. destruct (rlacks l R); [ exact HR | apply r0_maybe; assumption ].
  - apply r0_head; assumption.
Qed.

Lemma rlacks_ext_ne : forall l l' T X,
  l <> l' -> rlacks l (row_Ext l' T X) = rlacks l X.
Proof. intros. simpl. rewrite (proj2 (Nat.eqb_neq l l') H). reflexivity. Qed.

Lemma rlacks_maybe_ne : forall l l' P T X,
  l <> l' -> rlacks l (row_Maybe l' P T X) = rlacks l X.
Proof. intros. simpl. rewrite (proj2 (Nat.eqb_neq l l') H). reflexivity. Qed.

(* A presence is [Unit], [Bool], or neither, and then [nfm] leaves the entry. *)
Lemma pcases : forall P,
  P = typ_Unit \/ P = typ_Bool \/
  (forall l T X, nfm l P T X = row_Maybe l P T X).
Proof.
  destruct P; try (right; right; reflexivity); auto.
Qed.

Lemma nfm_swap_mm : forall l P T l' P' T' X, l <> l' ->
  req0 (nfm l P T (nfm l' P' T' X)) (nfm l' P' T' (nfm l P T X)).
Proof.
  intros l P T l' P' T' X Hne.
  assert (Hne' : l' <> l) by auto.
  destruct (pcases P) as [-> | [-> | HP]]; destruct (pcases P') as [-> | [-> | HP']].
  - (* U U *) cbn [nfm]. apply r0_swap; assumption.
  - (* U B *) cbn [nfm]. destruct (rlacks l' X) eqn:Hb.
    + rewrite (rlacks_ext_ne l' l T X Hne'), Hb. apply req0_refl.
    + rewrite (rlacks_ext_ne l' l T X Hne'), Hb.
      apply r0_sym. apply r0_swap_em; assumption.
  - (* U O *) cbn [nfm]. rewrite !HP'. apply r0_sym. apply r0_swap_em; assumption.
  - (* B U *) cbn [nfm]. destruct (rlacks l X) eqn:Ha.
    + rewrite (rlacks_ext_ne l l' T' X Hne), Ha. apply req0_refl.
    + rewrite (rlacks_ext_ne l l' T' X Hne), Ha. apply r0_swap_em; assumption.
  - (* B B *) cbn [nfm].
    destruct (rlacks l X) eqn:Ha; destruct (rlacks l' X) eqn:Hb;
      rewrite ?(rlacks_maybe_ne l l' typ_Bool T' X Hne),
              ?(rlacks_maybe_ne l' l typ_Bool T X Hne'), ?Ha, ?Hb; cbn [nfm];
      rewrite ?(rlacks_maybe_ne l l' typ_Bool T' X Hne),
              ?(rlacks_maybe_ne l' l typ_Bool T X Hne'), ?Ha, ?Hb;
      try apply req0_refl.
    apply r0_swap_mm; assumption.
  - (* B O *) rewrite !HP'. cbn [nfm]. destruct (rlacks l X) eqn:Ha.
    + rewrite (rlacks_maybe_ne l l' P' T' X Hne), Ha. apply req0_refl.
    + rewrite (rlacks_maybe_ne l l' P' T' X Hne), Ha. apply r0_swap_mm; assumption.
  - (* O U *) rewrite !HP. cbn [nfm]. apply r0_swap_em; assumption.
  - (* O B *) rewrite !HP. cbn [nfm]. destruct (rlacks l' X) eqn:Hb.
    + rewrite (rlacks_maybe_ne l' l P T X Hne'), Hb. apply req0_refl.
    + rewrite (rlacks_maybe_ne l' l P T X Hne'), Hb. apply r0_swap_mm; assumption.
  - (* O O *) rewrite !HP, !HP'. apply r0_swap_mm; assumption.
Qed.

Lemma nfm_swap_em : forall l P T l' T' X, l <> l' ->
  req0 (nfm l P T (row_Ext l' T' X)) (row_Ext l' T' (nfm l P T X)).
Proof.
  intros l P T l' T' X Hne.
  destruct (pcases P) as [-> | [-> | HP]].
  - cbn [nfm]. apply r0_swap; assumption.
  - cbn [nfm]. destruct (rlacks l X) eqn:Ha.
    + rewrite (rlacks_ext_ne l l' T' X Hne), Ha. apply req0_refl.
    + rewrite (rlacks_ext_ne l l' T' X Hne), Ha. apply r0_swap_em; assumption.
  - rewrite !HP. apply r0_swap_em; assumption.
Qed.

(* Normalizing commutes with every [req] rule, up to [req0]. *)
Lemma nf_req0 : forall R1 R2, req R1 R2 -> req0 (nf R1) (nf R2).
Proof.
  intros R1 R2 H.
  assert (Hm : (forall T T', teq T T' -> True) /\
               (forall R R', req R R' -> req0 (nf R) (nf R'))).
  { apply teq_req_mutind; intros; try exact I; simpl.
    - apply r0_empty.
    - apply r0_var.
    - apply r0_head; assumption.
    - apply r0_swap; assumption.
    - apply nfm_cong; assumption.
    - apply req0_refl.
    - assert (Hl : rlacks l (nf R) = true) by (apply rlacks_nf; assumption).
      simpl. rewrite Hl. apply req0_refl.
    - apply nfm_swap_em; assumption.
    - apply nfm_swap_mm; assumption.
    - eapply r0_trans; eassumption.
    - apply r0_sym; assumption. }
  exact (proj2 Hm R1 R2 H).
Qed.

(* A lacking row has no field of that label. *)
Lemma rlacks_pi_mut :
  (forall T : typ, True) /\
  (forall R : row, forall l, rlacks l R = true -> pi l R = nil).
Proof.
  apply typ_row_mutind; intros; try exact I; simpl in *.
  - reflexivity.
  - discriminate.
  - apply Bool.andb_true_iff in H1 as [H1 H2].
    destruct (Nat.eqb l0 l) eqn:E; simpl in H1; [ discriminate | auto ].
  - apply Bool.andb_true_iff in H2 as [H2 H3].
    destruct (Nat.eqb l0 l) eqn:E; simpl in H2; [ discriminate | simpl; auto ].
Qed.

Lemma rlacks_pi : forall R l, rlacks l R = true -> pi l R = nil.
Proof. intros. apply (proj2 rlacks_pi_mut); auto. Qed.

(* The row of a record literal has no [Maybe] entry.  If it is equivalent to
   [l ^ P : T ; R], then [P] is [Unit], or [P] is [Bool], the literal's row is
   equivalent to [R], and it has no field [l]. *)
Lemma presence_inv : forall Rf l P T R,
  nmaybe Rf = 0 -> req Rf (row_Maybe l P T R) ->
  P = typ_Unit \/
  (P = typ_Bool /\ req Rf R /\ pi l Rf = nil).
Proof.
  intros Rf l P T R Hn H.
  pose proof (nf_req0 _ _ H) as H0.
  rewrite (nf_nomaybe _ Hn) in H0.
  pose proof (req0_nmaybe _ _ H0) as Hc. rewrite Hn in Hc.
  simpl in Hc.
  destruct (pcases P) as [-> | [-> | HP]].
  - left. reflexivity.
  - right. simpl in H0, Hc. cbn [nfm] in H0, Hc.
    revert H0 Hc. case_eq (rlacks l (nf R)); intros E H0 Hc.
    + split; [ reflexivity | ].
      split.
      * eapply req_trans; [ apply req0_req; exact H0 | apply req_sym; apply nf_req ].
      * pose proof (req_pres _ _ (req0_req _ _ H0)) as [_ Hpi].
        specialize (Hpi l). rewrite (rlacks_pi _ _ E) in Hpi.
        inversion Hpi; reflexivity.
    + simpl in Hc. discriminate.
  - simpl in Hc. rewrite HP in Hc. simpl in Hc. discriminate.
Qed.

(* ------------------------------------------------------------------ *)
(* Taking the first field out of a row ([rm]) respects [req].            *)
(* ------------------------------------------------------------------ *)

Fixpoint row_ind4 (P : row -> Prop) (f1 : P row_Empty)
  (f2 : forall r, P (row_Var r))
  (f3 : forall l T R, P R -> P (row_Ext l T R))
  (f4 : forall l p T R, P R -> P (row_Maybe l p T R))
  (R : row) {struct R} : P R :=
  match R with
  | row_Empty => f1
  | row_Var r => f2 r
  | row_Ext l T R' => f3 l T R' (row_ind4 P f1 f2 f3 f4 R')
  | row_Maybe l p T R' => f4 l p T R' (row_ind4 P f1 f2 f3 f4 R')
  end.

Lemma rm_ext_here : forall l T R, rm l (row_Ext l T R) T R.
Proof. intros. unfold rm. simpl. rewrite Nat.eqb_refl. reflexivity. Qed.

Lemma rm_ext_skip : forall l l' T' R T R0,
  l <> l' -> rm l R T R0 -> rm l (row_Ext l' T' R) T (row_Ext l' T' R0).
Proof.
  intros. unfold rm in *. simpl.
  rewrite (proj2 (Nat.eqb_neq l l') H), H0. reflexivity.
Qed.

Lemma rm_maybe_here : forall l T R, rm l (row_Maybe l typ_Unit T R) T R.
Proof. intros. unfold rm. simpl. rewrite Nat.eqb_refl. reflexivity. Qed.

Lemma rm_maybe_skip : forall l l' P T' R T R0,
  l <> l' -> rm l R T R0 -> rm l (row_Maybe l' P T' R) T (row_Maybe l' P T' R0).
Proof.
  intros. unfold rm in *. simpl.
  rewrite (proj2 (Nat.eqb_neq l l') H), H0. reflexivity.
Qed.

Lemma rm_ext_inv : forall l l0 T0 R0 T R,
  rm l (row_Ext l0 T0 R0) T R ->
  (l = l0 /\ T = T0 /\ R = R0) \/
  (l <> l0 /\ exists R1, rm l R0 T R1 /\ R = row_Ext l0 T0 R1).
Proof.
  intros l l0 T0 R0 T R H. unfold rm in H. simpl in H.
  destruct (Nat.eqb l l0) eqn:E.
  - apply Nat.eqb_eq in E. inversion H; subst. left. auto.
  - apply Nat.eqb_neq in E.
    destruct (rmf l R0) as [[T1 R1]|] eqn:E2; [ | discriminate ].
    inversion H; subst. right. split; [ exact E | exists R1; split; [ exact E2 | reflexivity ] ].
Qed.

Lemma rm_maybe_inv : forall l l0 P T0 R0 T R,
  rm l (row_Maybe l0 P T0 R0) T R ->
  (l = l0 /\ P = typ_Unit /\ T = T0 /\ R = R0) \/
  (l <> l0 /\ exists R1, rm l R0 T R1 /\ R = row_Maybe l0 P T0 R1).
Proof.
  intros l l0 P T0 R0 T R H. unfold rm in H. simpl in H.
  destruct (Nat.eqb l l0) eqn:E.
  - apply Nat.eqb_eq in E.
    destruct P; simpl in H; try discriminate. inversion H; subst. left. auto.
  - apply Nat.eqb_neq in E.
    destruct (rmf l R0) as [[T1 R1]|] eqn:E2; [ | discriminate ].
    inversion H; subst. right. split; [ exact E | exists R1; split; [ exact E2 | reflexivity ] ].
Qed.

Lemma rm_empty_inv : forall l T R, ~ rm l row_Empty T R.
Proof. intros l T R H. unfold rm in H. simpl in H. discriminate. Qed.

Lemma rm_var_inv : forall l r T R, ~ rm l (row_Var r) T R.
Proof. intros l r T R H. unfold rm in H. simpl in H. discriminate. Qed.

Lemma rm_not_lacks : forall l R T R', rm l R T R' -> rlacks l R = false.
Proof.
  intros l R. induction R using row_ind4; intros Tq Rq H.
  - exfalso. eapply rm_empty_inv; eassumption.
  - exfalso. eapply rm_var_inv; eassumption.
  - destruct (rm_ext_inv _ _ _ _ _ _ H) as [[-> [-> ->]] | [Hne [R1 [E ->]]]].
    + simpl. rewrite Nat.eqb_refl. reflexivity.
    + simpl. rewrite (IHR _ _ E). apply Bool.andb_false_r.
  - destruct (rm_maybe_inv _ _ _ _ _ _ _ H) as [[-> [-> [-> ->]]] | [Hne [R1 [E ->]]]].
    + simpl. rewrite Nat.eqb_refl. reflexivity.
    + simpl. rewrite (IHR _ _ E). apply Bool.andb_false_r.
Qed.

Lemma rm_rlacks : forall l R T R', rm l R T R' ->
  forall l0, rlacks l0 R = true -> rlacks l0 R' = true.
Proof.
  intros l R. induction R using row_ind4; intros Tq Rq H lq Hl.
  - exfalso. eapply rm_empty_inv; eassumption.
  - exfalso. eapply rm_var_inv; eassumption.
  - destruct (rm_ext_inv _ _ _ _ _ _ H) as [[-> [-> ->]] | [Hne [R1 [E ->]]]].
    + simpl in Hl. apply Bool.andb_true_iff in Hl as [_ Hl]. exact Hl.
    + simpl in *. apply Bool.andb_true_iff in Hl as [Hl1 Hl2].
      rewrite Hl1. simpl. eapply IHR; eassumption.
  - destruct (rm_maybe_inv _ _ _ _ _ _ _ H) as [[-> [-> [-> ->]]] | [Hne [R1 [E ->]]]].
    + simpl in Hl. apply Bool.andb_true_iff in Hl as [_ Hl]. exact Hl.
    + simpl in *. apply Bool.andb_true_iff in Hl as [Hl1 Hl2].
      rewrite Hl1. simpl. eapply IHR; eassumption.
Qed.

Ltac ext_inv H Hn Rx Hm :=
  destruct (rm_ext_inv _ _ _ _ _ _ H) as [[? [? ?]] | [Hn [Rx [Hm ?]]]]; subst.
Ltac may_inv H Hn Rx Hm :=
  destruct (rm_maybe_inv _ _ _ _ _ _ _ H) as [[? [? [? ?]]] | [Hn [Rx [Hm ?]]]]; subst.

Lemma rm_req_mut :
  (forall T T' : typ, teq T T' -> True) /\
  (forall R1 R2, req R1 R2 ->
    (forall l T R, rm l R1 T R ->
       exists T' R', rm l R2 T' R' /\ teq T T' /\ req R R') /\
    (forall l T R, rm l R2 T R ->
       exists T' R', rm l R1 T' R' /\ teq T T' /\ req R R')).
Proof.
  apply teq_req_mutind; try (intros; exact I).
  - split; intros l T R Hrm; exfalso; eapply rm_empty_inv; eassumption.
  - intros r. split; intros l T R Hrm; exfalso; eapply rm_var_inv; eassumption.
  - (* head *)
    intros l T R T' R' Ht _ Hr IH. split.
    + intros l0 T0 R0 Hrm. ext_inv Hrm Hn1 Rx1 Hm1.
      * exists T', R'. split; [ apply rm_ext_here | split; assumption ].
      * destruct ((proj1 IH) _ _ _ Hm1) as [T1 [R1 [Hr1 [Ht1 Hq1]]]].
        exists T1, (row_Ext l T' R1).
        split; [ apply rm_ext_skip; assumption | split; [ assumption | apply req_head; assumption ] ].
    + intros l0 T0 R0 Hrm. ext_inv Hrm Hn1 Rx1 Hm1.
      * exists T, R. split; [ apply rm_ext_here | split; [ apply teq_sym; assumption | apply req_sym; assumption ] ].
      * destruct ((proj2 IH) _ _ _ Hm1) as [T1 [R1 [Hr1 [Ht1 Hq1]]]].
        exists T1, (row_Ext l T R1).
        split; [ apply rm_ext_skip; assumption
               | split; [ assumption | apply req_head; [ apply teq_sym; assumption | assumption ] ] ].
  - (* swap *)
    intros l T l' T' R Hne. pose proof (not_eq_sym Hne) as Hne'. split.
    + intros l0 T0 R0 Hrm. ext_inv Hrm Hn1 Rx1 Hm1.
      * exists T. exists (row_Ext l' T' R).
        split; [ apply rm_ext_skip; [ exact Hne | apply rm_ext_here ]
               | split; [ apply teq_refl | apply req_refl ] ].
      * ext_inv Hm1 Hn2 Rx2 Hm2.
        -- exists T'. exists (row_Ext l T R).
           split; [ apply rm_ext_here | split; [ apply teq_refl | apply req_refl ] ].
        -- exists T0. exists (row_Ext l' T' (row_Ext l T Rx2)).
           split; [ apply rm_ext_skip; [ assumption | apply rm_ext_skip; assumption ]
                  | split; [ apply teq_refl | apply req_swap; assumption ] ].
    + intros l0 T0 R0 Hrm. ext_inv Hrm Hn1 Rx1 Hm1.
      * exists T'. exists (row_Ext l T R).
        split; [ apply rm_ext_skip; [ exact Hne' | apply rm_ext_here ]
               | split; [ apply teq_refl | apply req_refl ] ].
      * ext_inv Hm1 Hn2 Rx2 Hm2.
        -- exists T. exists (row_Ext l' T' R).
           split; [ apply rm_ext_here | split; [ apply teq_refl | apply req_refl ] ].
        -- exists T0. exists (row_Ext l T (row_Ext l' T' Rx2)).
           split; [ apply rm_ext_skip; [ assumption | apply rm_ext_skip; assumption ]
                  | split; [ apply teq_refl | apply req_sym, req_swap; assumption ] ].
  - (* maybe *)
    intros l P T R P' T' R' HP _ HT _ HR IH. split.
    + intros l0 T0 R0 Hrm. may_inv Hrm Hn1 Rx1 Hm1.
      * apply teq_Unit_inv in HP; subst.
        exists T', R'. split; [ apply rm_maybe_here | split; assumption ].
      * destruct ((proj1 IH) _ _ _ Hm1) as [T1 [R1 [Hr1 [Ht1 Hq1]]]].
        exists T1, (row_Maybe l P' T' R1).
        split; [ apply rm_maybe_skip; assumption
               | split; [ assumption | apply req_maybe; assumption ] ].
    + intros l0 T0 R0 Hrm. may_inv Hrm Hn1 Rx1 Hm1.
      * apply teq_sym, teq_Unit_inv in HP; subst.
        exists T, R. split; [ apply rm_maybe_here
                            | split; [ apply teq_sym; assumption | apply req_sym; assumption ] ].
      * destruct ((proj2 IH) _ _ _ Hm1) as [T1 [R1 [Hr1 [Ht1 Hq1]]]].
        exists T1, (row_Maybe l P T R1).
        split; [ apply rm_maybe_skip; assumption
               | split; [ assumption | apply req_maybe; [ apply teq_sym; assumption | apply teq_sym; assumption | assumption ] ] ].
  - (* pre *)
    intros l T R. split.
    + intros l0 T0 R0 Hrm. may_inv Hrm Hn1 Rx1 Hm1.
      * exists T, R. split; [ apply rm_ext_here | split; [ apply teq_refl | apply req_refl ] ].
      * exists T0, (row_Ext l T Rx1).
        split; [ apply rm_ext_skip; assumption | split; [ apply teq_refl | apply req_pre ] ].
    + intros l0 T0 R0 Hrm. ext_inv Hrm Hn1 Rx1 Hm1.
      * exists T, R. split; [ apply rm_maybe_here | split; [ apply teq_refl | apply req_refl ] ].
      * exists T0, (row_Maybe l typ_Unit T Rx1).
        split; [ apply rm_maybe_skip; assumption
               | split; [ apply teq_refl | apply req_sym, req_pre ] ].
  - (* abs *)
    intros l T R Hl. split.
    + intros l0 T0 R0 Hrm. may_inv Hrm Hn1 Rx1 Hm1.
      * discriminate.
      * exists T0, Rx1. split; [ assumption | split; [ apply teq_refl | ] ].
        apply req_abs. eapply rm_rlacks; eassumption.
    + intros l0 T0 R0 Hrm.
      assert (Hne : l0 <> l).
      { intros ->. pose proof (rm_not_lacks _ _ _ _ Hrm). congruence. }
      exists T0, (row_Maybe l typ_Bool T R0).
      split; [ apply rm_maybe_skip; assumption | split; [ apply teq_refl | ] ].
      apply req_sym, req_abs. eapply rm_rlacks; eassumption.
  - (* swap_em *)
    intros l P T l' T' R Hne. pose proof (not_eq_sym Hne) as Hne'. split.
    + intros l0 T0 R0 Hrm. may_inv Hrm Hn1 Rx1 Hm1.
      * exists T. exists (row_Ext l' T' R).
        split; [ apply rm_ext_skip; [ exact Hne | apply rm_maybe_here ]
               | split; [ apply teq_refl | apply req_refl ] ].
      * ext_inv Hm1 Hn2 Rx2 Hm2.
        -- exists T'. exists (row_Maybe l P T R).
           split; [ apply rm_ext_here | split; [ apply teq_refl | apply req_refl ] ].
        -- exists T0. exists (row_Ext l' T' (row_Maybe l P T Rx2)).
           split; [ apply rm_ext_skip; [ assumption | apply rm_maybe_skip; assumption ]
                  | split; [ apply teq_refl | apply req_swap_em; assumption ] ].
    + intros l0 T0 R0 Hrm. ext_inv Hrm Hn1 Rx1 Hm1.
      * exists T'. exists (row_Maybe l P T R).
        split; [ apply rm_maybe_skip; [ exact Hne' | apply rm_ext_here ]
               | split; [ apply teq_refl | apply req_refl ] ].
      * may_inv Hm1 Hn2 Rx2 Hm2.
        -- exists T. exists (row_Ext l' T' R).
           split; [ apply rm_maybe_here | split; [ apply teq_refl | apply req_refl ] ].
        -- exists T0. exists (row_Maybe l P T (row_Ext l' T' Rx2)).
           split; [ apply rm_maybe_skip; [ assumption | apply rm_ext_skip; assumption ]
                  | split; [ apply teq_refl | apply req_sym, req_swap_em; assumption ] ].
  - (* swap_mm *)
    intros l P T l' P' T' R Hne. pose proof (not_eq_sym Hne) as Hne'. split.
    + intros l0 T0 R0 Hrm. may_inv Hrm Hn1 Rx1 Hm1.
      * exists T. exists (row_Maybe l' P' T' R).
        split; [ apply rm_maybe_skip; [ exact Hne | apply rm_maybe_here ]
               | split; [ apply teq_refl | apply req_refl ] ].
      * may_inv Hm1 Hn2 Rx2 Hm2.
        -- exists T'. exists (row_Maybe l P T R).
           split; [ apply rm_maybe_here | split; [ apply teq_refl | apply req_refl ] ].
        -- exists T0. exists (row_Maybe l' P' T' (row_Maybe l P T Rx2)).
           split; [ apply rm_maybe_skip; [ assumption | apply rm_maybe_skip; assumption ]
                  | split; [ apply teq_refl | apply req_swap_mm; assumption ] ].
    + intros l0 T0 R0 Hrm. may_inv Hrm Hn1 Rx1 Hm1.
      * exists T'. exists (row_Maybe l P T R).
        split; [ apply rm_maybe_skip; [ exact Hne' | apply rm_maybe_here ]
               | split; [ apply teq_refl | apply req_refl ] ].
      * may_inv Hm1 Hn2 Rx2 Hm2.
        -- exists T. exists (row_Maybe l' P' T' R).
           split; [ apply rm_maybe_here | split; [ apply teq_refl | apply req_refl ] ].
        -- exists T0. exists (row_Maybe l P T (row_Maybe l' P' T' Rx2)).
           split; [ apply rm_maybe_skip; [ assumption | apply rm_maybe_skip; assumption ]
                  | split; [ apply teq_refl | apply req_sym, req_swap_mm; assumption ] ].
  - (* trans *)
    intros R1 R3 R2 _ IH1 _ IH2. split.
    + intros l T R Hrm.
      destruct ((proj1 IH1) _ _ _ Hrm) as [T1 [R1' [H1 [Ht1 Hq1]]]].
      destruct ((proj1 IH2) _ _ _ H1) as [T2 [R2' [H2 [Ht2 Hq2]]]].
      exists T2, R2'. split; [ exact H2 | split; [ eapply teq_trans; eassumption | eapply req_trans; eassumption ] ].
    + intros l T R Hrm.
      destruct ((proj2 IH2) _ _ _ Hrm) as [T1 [R1' [H1 [Ht1 Hq1]]]].
      destruct ((proj2 IH1) _ _ _ H1) as [T2 [R2' [H2 [Ht2 Hq2]]]].
      exists T2, R2'. split; [ exact H2 | split; [ eapply teq_trans; eassumption | eapply req_trans; eassumption ] ].
  - (* sym *)
    intros R2 R1 _ IH. split; [ exact (proj2 IH) | exact (proj1 IH) ].
Qed.

Lemma rm_req : forall R1 R2, req R1 R2 -> forall l T R, rm l R1 T R ->
  exists T' R', rm l R2 T' R' /\ teq T T' /\ req R R'.
Proof. intros R1 R2 H. exact (proj1 (proj2 rm_req_mut R1 R2 H)). Qed.
