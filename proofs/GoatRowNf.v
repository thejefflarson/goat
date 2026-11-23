(* A normal form for rows, and cancellation (stage 7.6f of
   docs/design/phase7-proof-plan.md).

   [req] is an equivalence closed under swaps of different labels, the
   rewriting of a [Unit] presence to a plain field ([req_pre]), and the
   dropping of an absent entry the rest of the row has no [l] after and a
   closed tail ([req_abs]).  Rows may carry a tail variable and presence
   variables, so [req] relates rows only through what it can see: the entries
   of one label keep their order, a presence variable is rigid, and an absent
   entry survives unless the rest lacks its label.

   The normal form is the tail together with, for each label, the list of its
   entries, each a presence and a field type ([raw]), with the absent entries
   at the end of the list dropped when the tail is closed ([ents]).  Two rows
   are [req] exactly when the tails agree and, at every label, the entry lists
   agree up to [teq] ([req_iff_nf]).  Soundness is an induction on [req];
   completeness surfaces the first entry of a label ([extract_req]), the
   constructive swap argument [GoatRows.v] leaves out.

   Cancellation ([req_cancel]) is what the unifier's completeness needs: two
   rows that begin with the same label are [req] only if their rests are, and
   then either the presences and field types agree or both entries are absent
   (an absent field's type is no information).  In goat source:

     program(p, q) do {...p, x: 1} == {...q, x: 1} done

   unifies [x ^ pa : Int ; ra] with [x ^ pb : Int ; rb]: the cancellation gives
   [pa = pb] and [ra = rb], where two absent entries would give [ra = rb]
   alone. *)

Require Import Metalib.Metatheory.
Require Import Goat.Goat_ott.
Require Import Goat.GoatRows.
Require Import Stdlib.Lists.List.
Import ListNotations.

#[local] Hint Resolve teq_refl req_refl : core.

(* ---- entries and the normal form ---- *)

Definition ent_eq (e e' : typ * typ) : Prop :=
  teq (fst e) (fst e') /\ teq (snd e) (snd e').

Lemma ent_eq_refl : forall e, ent_eq e e.
Proof. intros e. split; apply teq_refl. Qed.

Lemma ent_eq_sym : forall e e', ent_eq e e' -> ent_eq e' e.
Proof. intros e e' [H1 H2]. split; apply teq_sym; assumption. Qed.

Lemma ent_eq_trans : forall e e' e'', ent_eq e e' -> ent_eq e' e'' -> ent_eq e e''.
Proof. intros e e' e'' [H1 H2] [H3 H4]. split; eapply teq_trans; eauto. Qed.

Lemma Forall2_ent_refl : forall l, Forall2 ent_eq l l.
Proof. induction l; constructor; auto using ent_eq_refl. Qed.

Lemma Forall2_ent_sym : forall l1 l2, Forall2 ent_eq l1 l2 -> Forall2 ent_eq l2 l1.
Proof. induction 1; constructor; auto using ent_eq_sym. Qed.

Lemma Forall2_ent_trans : forall l1 l2 l3,
  Forall2 ent_eq l1 l2 -> Forall2 ent_eq l2 l3 -> Forall2 ent_eq l1 l3.
Proof.
  intros l1 l2 l3 H; revert l3. induction H; intros l3 H2.
  - inversion H2; subst; constructor.
  - inversion H2; subst; constructor; eauto using ent_eq_trans.
Qed.

(* The entries of [l] in [R], in order; a plain field has presence [Unit]. *)
Fixpoint raw (l : label) (R : row) : list (typ * typ) :=
  match R with
  | row_Empty | row_Var _ => nil
  | row_Ext l' T R' => if Nat.eqb l l' then (typ_Unit, T) :: raw l R' else raw l R'
  | row_Maybe l' P T R' => if Nat.eqb l l' then (P, T) :: raw l R' else raw l R'
  end.

(* Put an entry in front of a list whose absent entries at the end are gone. *)
Definition cons_d (e : typ * typ) (es : list (typ * typ)) : list (typ * typ) :=
  match es with
  | nil => if is_abs (fst e) then nil else [e]
  | _ => e :: es
  end.

Fixpoint dropT (es : list (typ * typ)) : list (typ * typ) :=
  match es with
  | nil => nil
  | e :: es' => cons_d e (dropT es')
  end.

(* A closed tail lets [req_abs] drop the absent entries at the end of a
   label's list; an open tail keeps them. *)
Definition cons_t (t : row) (e : typ * typ) (es : list (typ * typ)) : list (typ * typ) :=
  match t with
  | row_Empty => cons_d e es
  | _ => e :: es
  end.

Definition ents_t (t : row) (es : list (typ * typ)) : list (typ * typ) :=
  match t with
  | row_Empty => dropT es
  | _ => es
  end.

Definition ents (l : label) (R : row) : list (typ * typ) := ents_t (rtail R) (raw l R).

Lemma ents_t_cons : forall t e es, ents_t t (e :: es) = cons_t t e (ents_t t es).
Proof. intros t e es. destruct t; reflexivity. Qed.

Lemma cons_t_unit : forall t T es, cons_t t (typ_Unit, T) es = (typ_Unit, T) :: es.
Proof. intros t T es. destruct t; try reflexivity. destruct es; reflexivity. Qed.

Lemma ents_ext : forall m l T R, ents m (row_Ext l T R) =
  if Nat.eqb m l then cons_t (rtail R) (typ_Unit, T) (ents m R) else ents m R.
Proof.
  intros m l T R. unfold ents. simpl. destruct (Nat.eqb m l); [ apply ents_t_cons | reflexivity ].
Qed.

Lemma ents_maybe : forall m l P T R, ents m (row_Maybe l P T R) =
  if Nat.eqb m l then cons_t (rtail R) (P, T) (ents m R) else ents m R.
Proof.
  intros m l P T R. unfold ents. simpl. destruct (Nat.eqb m l); [ apply ents_t_cons | reflexivity ].
Qed.

Lemma cons_t_Forall2 : forall t e e' a b, ent_eq e e' -> Forall2 ent_eq a b ->
  Forall2 ent_eq (cons_t t e a) (cons_t t e' b).
Proof.
  intros t e e' a b He H. destruct t; try (constructor; assumption).
  unfold cons_t, cons_d.
  assert (Hab : is_abs (fst e) = is_abs (fst e')) by (apply teq_is_abs; apply He).
  inversion H; subst.
  - rewrite Hab. destruct (is_abs (fst e')); constructor; [ | constructor ]. exact He.
  - constructor; assumption.
Qed.

(* A closed tail and no entry of [l]: the row lacks [l]. *)
Lemma rlacks_iff : forall l R,
  rlacks l R = true <-> rtail R = row_Empty /\ raw l R = nil.
Proof.
  intros l R. induction R; simpl.
  - tauto.
  - split; [ discriminate | intros [H _]; discriminate ].
  - destruct (Nat.eqb l l0) eqn:E; simpl.
    + split; [ discriminate | intros [_ H]; discriminate ].
    + exact IHR.
  - destruct (Nat.eqb l l0) eqn:E; simpl.
    + split; [ discriminate | intros [_ H]; discriminate ].
    + exact IHR.
Qed.

(* ---- soundness: [req] respects the normal form ---- *)

Lemma req_nf : forall R1 R2, req R1 R2 ->
  rtail R1 = rtail R2 /\ forall l, Forall2 ent_eq (ents l R1) (ents l R2).
Proof.
  induction 1.
  - split; [ reflexivity | intros; constructor ].
  - split; [ reflexivity | intros; constructor ].
  - (* head *)
    destruct IHreq as [Ht Hl]. split; [ exact Ht | ]. intros l0.
    rewrite !ents_ext. rewrite <- Ht. destruct (Nat.eqb l0 l); [ | apply Hl ].
    apply cons_t_Forall2; [ split; [ apply teq_refl | assumption ] | apply Hl ].
  - (* swap *)
    split; [ reflexivity | ]. intros l0. unfold ents. simpl.
    destruct (Nat.eqb l0 l) eqn:E1; destruct (Nat.eqb l0 l') eqn:E2; try apply Forall2_ent_refl.
    apply Nat.eqb_eq in E1; apply Nat.eqb_eq in E2; congruence.
  - (* maybe *)
    destruct IHreq as [Ht Hl]. split; [ exact Ht | ]. intros l0.
    rewrite !ents_maybe. rewrite <- Ht. destruct (Nat.eqb l0 l); [ | apply Hl ].
    apply cons_t_Forall2; [ split; assumption | apply Hl ].
  - (* pre *)
    split; [ reflexivity | ]. intros l0. unfold ents. simpl. apply Forall2_ent_refl.
  - (* abs *)
    match goal with H : rlacks _ _ = true |- _ => rename H into Hl end.
    apply rlacks_iff in Hl as [Ht Hr].
    split; [ reflexivity | ]. intros l0. unfold ents. simpl. rewrite Ht.
    destruct (Nat.eqb l0 l) eqn:E; simpl.
    + apply Nat.eqb_eq in E. subst l0. rewrite Hr. simpl. constructor.
    + apply Forall2_ent_refl.
  - (* swap_em *)
    split; [ reflexivity | ]. intros l0. unfold ents. simpl.
    destruct (Nat.eqb l0 l) eqn:E1; destruct (Nat.eqb l0 l') eqn:E2; try apply Forall2_ent_refl.
    apply Nat.eqb_eq in E1; apply Nat.eqb_eq in E2; congruence.
  - (* swap_mm *)
    split; [ reflexivity | ]. intros l0. unfold ents. simpl.
    destruct (Nat.eqb l0 l) eqn:E1; destruct (Nat.eqb l0 l') eqn:E2; try apply Forall2_ent_refl.
    apply Nat.eqb_eq in E1; apply Nat.eqb_eq in E2; congruence.
  - (* trans *)
    destruct IHreq1 as [T1 P1]. destruct IHreq2 as [T2 P2].
    split; [ congruence | intros l0; eauto using Forall2_ent_trans ].
  - (* sym *)
    destruct IHreq as [T1 P1].
    split; [ auto | intros l0; auto using Forall2_ent_sym ].
Qed.

(* ---- completeness ---- *)

(* The first entry of a label can be surfaced, whatever its presence. *)
Lemma extract_req : forall l R P T es, raw l R = (P, T) :: es ->
  exists R0, req R (row_Maybe l P T R0) /\ rtail R0 = rtail R /\ raw l R0 = es /\
    forall m, m <> l -> raw m R0 = raw m R.
Proof.
  intros l R. induction R as [ | r | l0 t0 R IHR | l0 p0 t0 R IHR ]; intros P T es H; simpl in H; try discriminate.
  - destruct (Nat.eqb l l0) eqn:E.
    + apply Nat.eqb_eq in E. subst l0. inversion H; subst.
      exists R. split; [ apply req_sym; apply req_pre | ].
      split; [ reflexivity | ]. split; [ reflexivity | ].
      intros m Hm. simpl. apply Nat.eqb_neq in Hm. rewrite Hm. reflexivity.
    + pose proof (proj1 (Nat.eqb_neq _ _) E) as En.
      destruct (IHR _ _ _ H) as [R0 [Hq [Ht [Hr Hm]]]].
      exists (row_Ext l0 t0 R0). split; [ | split; [ exact Ht | split ] ].
      * eapply req_trans; [ apply req_head; [ apply teq_refl | exact Hq ] | ].
        apply req_sym. apply req_swap_em. exact En.
      * simpl. rewrite E. exact Hr.
      * intros m Hm'. simpl. destruct (Nat.eqb m l0); [ f_equal | ]; apply Hm; exact Hm'.
  - destruct (Nat.eqb l l0) eqn:E.
    + apply Nat.eqb_eq in E. subst l0. inversion H; subst.
      exists R. split; [ apply req_refl | ].
      split; [ reflexivity | ]. split; [ reflexivity | ].
      intros m Hm. simpl. apply Nat.eqb_neq in Hm. rewrite Hm. reflexivity.
    + pose proof (proj1 (Nat.eqb_neq _ _) E) as En.
      destruct (IHR _ _ _ H) as [R0 [Hq [Ht [Hr Hm]]]].
      exists (row_Maybe l0 p0 t0 R0). split; [ | split; [ exact Ht | split ] ].
      * eapply req_trans; [ apply req_maybe; [ apply teq_refl | apply teq_refl | exact Hq ] | ].
        apply req_sym. apply req_swap_mm. exact En.
      * simpl. rewrite E. exact Hr.
      * intros m Hm'. simpl. destruct (Nat.eqb m l0); [ f_equal | ]; apply Hm; exact Hm'.
Qed.

Lemma no_entries : forall R, (forall l, raw l R = nil) -> R = rtail R.
Proof.
  intros R. induction R; intros H; try reflexivity.
  - specialize (H l). simpl in H. rewrite Nat.eqb_refl in H. discriminate H.
  - specialize (H l). simpl in H. rewrite Nat.eqb_refl in H. discriminate H.
Qed.

(* Two rows with the same tail and entry lists, entry by entry, are [req]. *)
Lemma req_of_raw : forall R1 R2, rtail R1 = rtail R2 ->
  (forall l, Forall2 ent_eq (raw l R1) (raw l R2)) -> req R1 R2.
Proof.
  intros R1. induction R1 as [ | r | l T R1 IHR1 | l P T R1 IHR1 ]; intros R2 Ht H.
  - assert (HR : forall l, raw l R2 = nil).
    { intros l. specialize (H l). simpl in H. inversion H; reflexivity. }
    rewrite (no_entries R2 HR). simpl in Ht. rewrite <- Ht. apply req_refl.
  - assert (HR : forall l, raw l R2 = nil).
    { intros l. specialize (H l). simpl in H. inversion H; reflexivity. }
    rewrite (no_entries R2 HR). simpl in Ht. rewrite <- Ht. apply req_refl.
  - (* plain field *)
    pose proof (H l) as Hl. simpl in Hl. rewrite Nat.eqb_refl in Hl.
    destruct (raw l R2) as [ | [P2 T2] es2 ] eqn:E2; [ inversion Hl | ].
    inversion Hl as [ | e1 e2 es1 es2' Hhe Hrest ]; subst. destruct Hhe as [HP HT]. simpl in HP, HT.
    destruct (extract_req l R2 P2 T2 es2 E2) as [R0 [Hq [Ht0 [Hr0 Hm0]]]].
    assert (Hunit : P2 = typ_Unit)
      by (apply teq_Unit_inv in HP; exact HP). subst P2.
    assert (Hreq : req R1 R0).
    { apply IHR1; [ simpl in Ht; congruence | ]. intros m.
      destruct (Nat.eq_dec m l) as [-> | Hne].
      - rewrite Hr0. exact Hrest.
      - rewrite (Hm0 m Hne). specialize (H m). simpl in H.
        apply Nat.eqb_neq in Hne. rewrite Hne in H. exact H. }
    eapply req_trans; [ apply req_sym; apply req_pre | ].
    eapply req_trans; [ apply req_maybe; [ apply teq_refl | exact HT | exact Hreq ] | ].
    apply req_sym. exact Hq.
  - (* presence entry *)
    pose proof (H l) as Hl. simpl in Hl. rewrite Nat.eqb_refl in Hl.
    destruct (raw l R2) as [ | [P2 T2] es2 ] eqn:E2; [ inversion Hl | ].
    inversion Hl as [ | e1 e2 es1 es2' Hhe Hrest ]; subst. destruct Hhe as [HP HT]. simpl in HP, HT.
    destruct (extract_req l R2 P2 T2 es2 E2) as [R0 [Hq [Ht0 [Hr0 Hm0]]]].
    assert (Hreq : req R1 R0).
    { apply IHR1; [ simpl in Ht; congruence | ]. intros m.
      destruct (Nat.eq_dec m l) as [-> | Hne].
      - rewrite Hr0. exact Hrest.
      - rewrite (Hm0 m Hne). specialize (H m). simpl in H.
        apply Nat.eqb_neq in Hne. rewrite Hne in H. exact H. }
    eapply req_trans; [ apply req_maybe; [ exact HP | exact HT | exact Hreq ] | ].
    apply req_sym. exact Hq.
Qed.

(* Every row is [req] to one whose entry lists are its normal form. *)
Lemma nf_exists : forall R, exists R', req R R' /\ rtail R' = rtail R /\
  forall l, raw l R' = ents l R.
Proof.
  induction R as [ | r | l T R IHR | l P T R IHR ].
  - exists row_Empty. split; [ apply req_refl | split; [ reflexivity | intros l; reflexivity ] ].
  - exists (row_Var r). split; [ apply req_refl | split; [ reflexivity | intros l; reflexivity ] ].
  - destruct IHR as [R' [Hq [Ht Hr]]].
    exists (row_Ext l T R'). split; [ apply req_head; [ apply teq_refl | exact Hq ] | ].
    split; [ simpl; exact Ht | ]. intros m. rewrite ents_ext. simpl.
    destruct (Nat.eqb m l); [ | apply Hr ].
    rewrite cons_t_unit, Hr. reflexivity.
  - destruct IHR as [R' [Hq [Ht Hr]]].
    destruct (is_abs P && rlacks l R') eqn:Hdrop.
    + apply andb_true_iff in Hdrop as [Hab Hlk].
      assert (HP : P = typ_Bool) by (destruct P; simpl in Hab; try discriminate; reflexivity). subst P.
      apply rlacks_iff in Hlk as [HtE Hr0].
      exists R'. split; [ | split; [ simpl; exact Ht | ] ].
      * eapply req_trans; [ apply req_maybe; [ apply teq_refl | apply teq_refl | exact Hq ] | ].
        apply req_abs. apply rlacks_iff. split; assumption.
      * intros m. rewrite ents_maybe. destruct (Nat.eqb m l) eqn:E.
        -- apply Nat.eqb_eq in E. subst m. rewrite <- Hr, Hr0.
           simpl in Ht. rewrite <- Ht, HtE. reflexivity.
        -- apply Hr.
    + exists (row_Maybe l P T R'). split; [ apply req_maybe; [ apply teq_refl | apply teq_refl | exact Hq ] | ].
      split; [ simpl; exact Ht | ]. intros m. rewrite ents_maybe. simpl.
      destruct (Nat.eqb m l) eqn:E; [ | apply Hr ].
      apply Nat.eqb_eq in E. subst m. rewrite Hr.
      unfold cons_t. destruct (rtail R) eqn:HtR; try reflexivity. unfold cons_d.
      destruct (ents l R) eqn:Hes; [ | reflexivity ].
      assert (Hl : raw l R' = nil) by (rewrite Hr; exact Hes).
      assert (Hlk : rlacks l R' = true)
        by (apply rlacks_iff; split; [ exact Ht | exact Hl ]).
      rewrite Hlk, Bool.andb_true_r in Hdrop. simpl. rewrite Hdrop. reflexivity.
Qed.

Lemma req_iff_nf : forall R1 R2, req R1 R2 <->
  rtail R1 = rtail R2 /\ forall l, Forall2 ent_eq (ents l R1) (ents l R2).
Proof.
  intros R1 R2. split; [ apply req_nf | intros [Ht H] ].
  destruct (nf_exists R1) as [R1' [Hq1 [Ht1 Hr1]]].
  destruct (nf_exists R2) as [R2' [Hq2 [Ht2 Hr2]]].
  eapply req_trans; [ exact Hq1 | ].
  eapply req_trans; [ | apply req_sym; exact Hq2 ].
  apply req_of_raw; [ congruence | ]. intros l. rewrite Hr1, Hr2. apply H.
Qed.

(* ---- cancellation ---- *)

(* The entry lists of two rows that begin with one label, in the one case the
   unifier meets: the lists after the front entries agree, and the front
   entries agree unless both are absent and have nothing absent-free after. *)
Lemma cons_t_inv : forall t e e' a b,
  Forall2 ent_eq (cons_t t e a) (cons_t t e' b) ->
  (ent_eq e e' /\ Forall2 ent_eq a b) \/
  (is_abs (fst e) = true /\ is_abs (fst e') = true /\ a = nil /\ b = nil).
Proof.
  intros t e e' a b H. destruct t; try (inversion H; subst; left; split; assumption).
  unfold cons_t, cons_d in H.
  destruct a as [ | a1 a2 ], b as [ | b1 b2 ].
  - destruct (is_abs (fst e)) eqn:E1, (is_abs (fst e')) eqn:E2.
    + right. repeat split; reflexivity.
    + inversion H.
    + inversion H.
    + inversion H; subst. left. split; [ assumption | constructor ].
  - destruct (is_abs (fst e)) eqn:E1.
    + inversion H.
    + inversion H; subst. inversion H5.
  - destruct (is_abs (fst e')) eqn:E2.
    + inversion H.
    + inversion H; subst. inversion H5.
  - inversion H; subst. left. split; assumption.
Qed.

Theorem req_cancel : forall l P A X Q B Y,
  req (row_Maybe l P A X) (row_Maybe l Q B Y) ->
  req X Y /\ ((teq P Q /\ teq A B) \/ (is_abs P = true /\ is_abs Q = true)).
Proof.
  intros l P A X Q B Y H. apply req_nf in H as [Ht H]. simpl in Ht.
  assert (Hl : Forall2 ent_eq (cons_t (rtail X) (P, A) (ents l X))
                              (cons_t (rtail X) (Q, B) (ents l Y))).
  { specialize (H l). rewrite !ents_maybe, Nat.eqb_refl in H. rewrite <- Ht in H. exact H. }
  destruct (cons_t_inv _ _ _ _ _ Hl) as [[He Hrest] | (Ha & Hb & Hn1 & Hn2)].
  - split; [ | left; exact He ].
    apply req_iff_nf. split; [ exact Ht | ]. intros m.
    destruct (Nat.eq_dec m l) as [-> | Hne]; [ exact Hrest | ].
    specialize (H m). rewrite !ents_maybe in H.
    apply Nat.eqb_neq in Hne. rewrite Hne in H. exact H.
  - split; [ | right; split; assumption ].
    apply req_iff_nf. split; [ exact Ht | ]. intros m.
    destruct (Nat.eq_dec m l) as [-> | Hne].
    + rewrite Hn1, Hn2. constructor.
    + specialize (H m). rewrite !ents_maybe in H.
      apply Nat.eqb_neq in Hne. rewrite Hne in H. exact H.
Qed.

(* Plain fields cancel too: [req_pre] reads one as a [Unit] presence. *)
Corollary req_cancel_ext : forall l A X B Y,
  req (row_Ext l A X) (row_Ext l B Y) -> teq A B /\ req X Y.
Proof.
  intros l A X B Y H.
  assert (H' : req (row_Maybe l typ_Unit A X) (row_Maybe l typ_Unit B Y)).
  { eapply req_trans; [ apply req_pre | ].
    eapply req_trans; [ exact H | apply req_sym; apply req_pre ]. }
  apply req_cancel in H' as [Hr [[_ Ht] | [Hu _]]]; [ split; assumption | simpl in Hu; discriminate Hu ].
Qed.

(* A presence entry against a plain field: the presence is [Unit]. *)
Corollary req_cancel_mixed : forall l P A X B Y,
  req (row_Maybe l P A X) (row_Ext l B Y) -> P = typ_Unit /\ teq A B /\ req X Y.
Proof.
  intros l P A X B Y H.
  assert (H' : req (row_Maybe l P A X) (row_Maybe l typ_Unit B Y)).
  { eapply req_trans; [ exact H | apply req_sym; apply req_pre ]. }
  apply req_cancel in H' as [Hr [[HP Ht] | [_ Hu]]].
  - apply teq_sym in HP. apply teq_Unit_inv in HP.
    split; [ exact HP | split; assumption ].
  - simpl in Hu. discriminate Hu.
Qed.
