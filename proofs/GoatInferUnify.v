(* Soundness of row-aware unification: a unifier the algorithm returns makes
   the two types equivalent under [teq] (the two rows under [req]), and
   respects the sorts of the kinding environment it ran in. *)

Require Import Metalib.Metatheory.
Require Import Goat.Goat_ott.
Require Import Goat.GoatProofs.
Require Import Goat.GoatRows.
Require Import Goat.GoatDefs.
Require Import Goat.GoatSubst.
Require Import Goat.GoatHM.
Require Import Goat.GoatSound.
Require Import Goat.GoatInfer.
Require Import Goat.GoatInferSub.
Require Import Goat.GoatInferSort.
Require Import Stdlib.Lists.List.
From Stdlib Require Import Lia.
Import ListNotations.

Lemma teq_apT : forall s T T', teq T T' -> teq (apT s T) (apT s T').
Proof. intros. apply teq_ap. auto. Qed.

Lemma req_apR : forall s R R', req R R' -> req (apR s R) (apR s R').
Proof. intros s R R' H. exact (proj2 teq_ap_mut R R' H (sT s) (sR s)). Qed.

Lemma apR_Ext : forall s l T R, apR s (row_Ext l T R) = row_Ext l (apT s T) (apR s R).
Proof. reflexivity. Qed.

Lemma apR_id : forall R, apR sid R = R.
Proof. intros R. apply (proj2 ap_pointwise_id_mut); reflexivity. Qed.

Lemma ev_var_T : forall a, EvT (typ_Var a) -> ev a.
Proof. intros a [H _]. apply H. simpl. fsetdec. Qed.

Lemma ev_var_R : forall a, EvR (row_Var a) -> ev a.
Proof. intros a [_ H]. apply H. simpl. fsetdec. Qed.

Lemma EvT_var : forall a, ev a -> EvT (typ_Var a).
Proof. intros a Ha. split; intros b Hb; simpl in Hb;
  [ apply AtomSetFacts.singleton_iff in Hb; subst; exact Ha | fsetdec ]. Qed.

Lemma EvR_var : forall a, ev a -> EvR (row_Var a).
Proof. intros a Ha. split; intros b Hb; simpl in Hb;
  [ fsetdec | apply AtomSetFacts.singleton_iff in Hb; subst; exact Ha ]. Qed.

(* ------------------------------------------------------------------ *)
(* Binding a variable                                                   *)
(* ------------------------------------------------------------------ *)

Lemma sound_bindT : forall a T, ev a -> EvT T -> occT a T = false ->
  OkS (sbT a T) /\ teq (apT (sbT a T) (typ_Var a)) (apT (sbT a T) T).
Proof.
  intros a T Ha HT Hocc. destruct (occT_false _ _ Hocc) as [Hnot HL].
  split; [exact (OkS_sbT a T Ha HT HL)|].
  assert (E1 : apT (sbT a T) (typ_Var a) = T).
  { unfold apT, sbT; simpl. destruct (Atom.eq_dec a a); [reflexivity | contradiction]. }
  assert (E2 : apT (sbT a T) T = T).
  { unfold apT. apply ap_typ_fix.
    - intros b Hb. unfold sbT; simpl. destruct (Atom.eq_dec b a) as [->|]; [contradiction | reflexivity].
    - intros r Hr. reflexivity. }
  rewrite E1, E2. apply teq_refl.
Qed.

Lemma kres_sbT : forall D a T, sat D (D a) T -> kres D D (sT (sbT a T)).
Proof.
  intros D a T H b. unfold sbT. simpl.
  destruct (Atom.eq_dec b a) as [->|Hne]; [ exact H | simpl; apply finer_refl ].
Qed.

Lemma sound_bindR : forall r R, ev r -> EvR R -> occR r R = false ->
  OkS (sbR r R) /\ req (apR (sbR r R) (row_Var r)) (apR (sbR r R) R).
Proof.
  intros r R Hr HR Hocc. destruct (occR_false _ _ Hocc) as [Hnot HL].
  split; [exact (OkS_sbR r R Hr HR HL)|].
  assert (E1 : apR (sbR r R) (row_Var r) = R).
  { unfold apR, sbR; simpl. destruct (Atom.eq_dec r r); [reflexivity | contradiction]. }
  assert (E2 : apR (sbR r R) R = R).
  { unfold apR. apply ap_row_fix.
    - intros b Hb. reflexivity.
    - intros q Hq. unfold sbR; simpl. destruct (Atom.eq_dec q r) as [->|]; [contradiction | reflexivity]. }
  rewrite E1, E2. apply req_refl.
Qed.

(* ------------------------------------------------------------------ *)
(* Rewriting a row to present a label first                             *)
(* ------------------------------------------------------------------ *)

Lemma EvT_arrow_inv : forall A B, EvT (typ_Arrow A B) -> EvT A /\ EvT B.
Proof.
  intros A B [H1 H2]. simpl in H1, H2.
  split; split; intros c Hc; [apply H1 | apply H2 | apply H1 | apply H2]; fsetdec.
Qed.

Lemma EvR_ext_inv : forall l T R, EvR (row_Ext l T R) -> EvT T /\ EvR R.
Proof.
  intros l T R [H1 H2]. simpl in H1, H2.
  split; split; intros c Hc; [apply H1 | apply H2 | apply H1 | apply H2]; fsetdec.
Qed.

Lemma EvR_ext : forall l T R, EvT T -> EvR R -> EvR (row_Ext l T R).
Proof.
  intros l T R [H1 H2] [H3 H4]. split; intros b Hb; simpl in Hb;
    apply AtomSetFacts.union_iff in Hb; destruct Hb as [Hb|Hb]; auto.
Qed.

Lemma rewrite_row_sound : forall l av R n T' R' s n',
  rewrite_row l av R n = Some (T', R', s, n') -> EvR R ->
  OkS s /\ EvT T' /\ EvR R' /\ req (apR s R) (row_Ext l T' R') /\
  (forall D, kres D D (sT s)) /\ n <= n'.
Proof.
  intros l av R. induction R as [| r | l' T'' R'' IH]; intros n T' R' s n' H HR;
    cbn [rewrite_row] in H.
  - discriminate.
  - destruct (AtomSetImpl.mem r av); [discriminate|]. inversion H; subst; clear H.
    assert (Hr : ev r) by exact (ev_var_R r HR).
    assert (HEv : EvR (row_Ext l (typ_Var (ea n)) (row_Var (ea (S n))))).
    { apply EvR_ext; [ apply EvT_var, ev_ea | apply EvR_var, ev_ea ]. }
    split; [ apply OkS_sbR; [ auto | auto | exact (conj I I) ] | ].
    split; [ apply EvT_var, ev_ea | ].
    split; [ apply EvR_var, ev_ea | ].
    split.
    { unfold apR, sbR; simpl. destruct (Atom.eq_dec r r); [|contradiction].
      apply req_refl. }
    split; [ intros D; exact (kres_id D) | lia ].
  - destruct (Nat.eqb l l') eqn:El.
    + inversion H; subst; clear H. apply Nat.eqb_eq in El; subst l'.
      destruct (EvR_ext_inv _ _ _ HR) as [HT HR''].
      split; [ apply OkS_id | ].
      split; [ exact HT | ].
      split; [ exact HR'' | ].
      split.
      { rewrite apR_Ext, apR_id. unfold apT, sid; simpl.
        rewrite (ap_typ_pointwise_id _ idt idr) by reflexivity.
        apply req_refl. }
      split; [ intros D; exact (kres_id D) | lia ].
    + destruct (rewrite_row l av R'' n) as [[[[T0 R3] s0] n1]|] eqn:E; [|discriminate].
      inversion H; subst; clear H.
      destruct (EvR_ext_inv _ _ _ HR) as [HT'' HR''].
      destruct (IH _ _ _ _ _ E HR'') as (Hs0 & HT0 & HR3 & Hreq & Hk0 & Hle).
      split; [ exact Hs0 | ].
      split; [ exact HT0 | ].
      split; [ apply EvR_ext; [ apply EvT_ap; auto | exact HR3 ] | ].
      split.
      { rewrite apR_Ext.
        eapply req_trans; [ apply req_head; [ apply teq_refl | exact Hreq ] | ].
        apply req_swap. intro Heq. subst. rewrite Nat.eqb_refl in El. discriminate. }
      split; [ exact Hk0 | exact Hle ].
Qed.

(* ------------------------------------------------------------------ *)
(* Unification                                                          *)
(* ------------------------------------------------------------------ *)

Lemma var_left_T : forall D a T n s n',
  (if occT a T then (None : option (sub * nat))
   else if sat_b D (D a) T then Some (sbT a T, n) else None) = Some (s, n') ->
  EvT (typ_Var a) -> EvT T ->
  OkS s /\ teq (apT s (typ_Var a)) (apT s T) /\ kres D D (sT s) /\ n <= n'.
Proof.
  intros D a T n s n' H Ha HT.
  destruct (occT a T) eqn:Eo; [discriminate|].
  destruct (sat_b D (D a) T) eqn:Es; [|discriminate]. inversion H; subst; clear H.
  destruct (sound_bindT a T (ev_var_T a Ha) HT Eo) as [Hs Ht].
  split; [exact Hs|]. split; [exact Ht|]. split; [ apply kres_sbT; apply sat_b_sound; exact Es | lia ].
Qed.

Lemma var_right_T : forall D b T n s n',
  (if occT b T then (None : option (sub * nat))
   else if sat_b D (D b) T then Some (sbT b T, n) else None) = Some (s, n') ->
  EvT T -> EvT (typ_Var b) ->
  OkS s /\ teq (apT s T) (apT s (typ_Var b)) /\ kres D D (sT s) /\ n <= n'.
Proof.
  intros D b T n s n' H HT Hb.
  destruct (occT b T) eqn:Eo; [discriminate|].
  destruct (sat_b D (D b) T) eqn:Es; [|discriminate]. inversion H; subst; clear H.
  destruct (sound_bindT b T (ev_var_T b Hb) HT Eo) as [Hs Ht].
  split; [exact Hs|]. split; [apply teq_sym; exact Ht|].
  split; [ apply kres_sbT; apply sat_b_sound; exact Es | lia ].
Qed.

Lemma var_left_R : forall D a R n s n',
  (if occR a R then (None : option (sub * nat)) else Some (sbR a R, n)) = Some (s, n') ->
  EvR (row_Var a) -> EvR R ->
  OkS s /\ req (apR s (row_Var a)) (apR s R) /\ kres D D (sT s) /\ n <= n'.
Proof.
  intros D a R n s n' H Ha HR.
  destruct (occR a R) eqn:Eo; [discriminate|]. inversion H; subst; clear H.
  destruct (sound_bindR a R (ev_var_R a Ha) HR Eo) as [Hs Hr].
  split; [exact Hs|]. split; [exact Hr|]. split; [ exact (kres_id D) | lia ].
Qed.

Lemma var_right_R : forall D b R n s n',
  (if occR b R then (None : option (sub * nat)) else Some (sbR b R, n)) = Some (s, n') ->
  EvR R -> EvR (row_Var b) ->
  OkS s /\ req (apR s R) (apR s (row_Var b)) /\ kres D D (sT s) /\ n <= n'.
Proof.
  intros D b R n s n' H HR Hb.
  destruct (occR b R) eqn:Eo; [discriminate|]. inversion H; subst; clear H.
  destruct (sound_bindR b R (ev_var_R b Hb) HR Eo) as [Hs Hr].
  split; [exact Hs|]. split; [apply req_sym; exact Hr|].
  split; [ exact (kres_id D) | lia ].
Qed.

Lemma unify_sound : forall f,
  (forall D T1 T2 n s n', unify_t f D T1 T2 n = Some (s, n') ->
     EvT T1 -> EvT T2 ->
     OkS s /\ teq (apT s T1) (apT s T2) /\ kres D D (sT s) /\ n <= n') /\
  (forall D R1 R2 n s n', unify_r f D R1 R2 n = Some (s, n') ->
     EvR R1 -> EvR R2 ->
     OkS s /\ req (apR s R1) (apR s R2) /\ kres D D (sT s) /\ n <= n').
Proof.
  induction f as [|f IH]; [ split; intros; discriminate | ].
  destruct IH as [IHt IHr].
  split.
  - intros D T1 T2 n s n' H H1 H2. cbn [unify_t] in H.
    destruct T1 as [| | | | | A B | R | a | i | B1 | w1 A1]; destruct T2 as [| | | | | A' B' | R' | b | i' | B1' | w1' A1'];
      try discriminate H.
    all: try (exact (var_left_T _ _ _ _ _ _ H H1 H2)).
    all: try (exact (var_right_T _ _ _ _ _ _ H H1 H2)).
    1-5: inversion H; subst; split; [apply OkS_id | split; [apply teq_refl | split; [ exact (kres_id D) | lia ]]].
    + (* Arrow, Arrow *)
      destruct (unify_t f D A A' n) as [[s1 n1]|] eqn:E1; [|discriminate].
      destruct (unify_t f D (apT s1 B) (apT s1 B') n1) as [[s2 n2]|] eqn:E2; [|discriminate].
      inversion H; subst; clear H.
      destruct (EvT_arrow_inv _ _ H1) as [EA EB].
      destruct (EvT_arrow_inv _ _ H2) as [EA' EB'].
      destruct (IHt _ _ _ _ _ _ E1 EA EA') as (Hs1 & Ht1 & Hk1 & Hl1).
      destruct (IHt _ _ _ _ _ _ E2 (EvT_ap s1 B Hs1 EB) (EvT_ap s1 B' Hs1 EB')) as (Hs2 & Ht2 & Hk2 & Hl2).
      split; [ apply OkS_comp; auto | ].
      split.
      { change (apT (scomp s2 s1) (typ_Arrow A B))
          with (typ_Arrow (apT (scomp s2 s1) A) (apT (scomp s2 s1) B)).
        change (apT (scomp s2 s1) (typ_Arrow A' B'))
          with (typ_Arrow (apT (scomp s2 s1) A') (apT (scomp s2 s1) B')).
        rewrite <- !apT_comp. apply teq_arrow.
        - apply teq_apT; exact Ht1.
        - exact Ht2. }
      split; [ exact (kres_scomp D D D s1 s2 Hk1 Hk2) | lia ].
    + (* Record, Record *)
      destruct (IHr _ _ _ _ _ _ H) as (Hs & Hr & Hk & Hl); [exact H1 | exact H2 | ].
      split; [exact Hs | split; [apply teq_rec; exact Hr | split; [exact Hk | exact Hl]]].
    + (* Var, Var *)
      destruct (Atom.eq_dec a b) as [->|Hne].
      * inversion H; subst. split; [apply OkS_id | split; [apply teq_refl | split; [ exact (kres_id D) | lia ]]].
      * assert (Eoa : occT a (typ_Var b) = false).
        { unfold occT. simpl. apply Bool.orb_false_iff. split; [ | reflexivity ].
          apply AtomSetFacts.not_mem_iff. intro Hin.
          apply AtomSetFacts.singleton_iff in Hin. congruence. }
        assert (Eob : occT b (typ_Var a) = false).
        { unfold occT. simpl. apply Bool.orb_false_iff. split; [ | reflexivity ].
          apply AtomSetFacts.not_mem_iff. intro Hin.
          apply AtomSetFacts.singleton_iff in Hin. congruence. }
        destruct (finer_b (D b) (D a)) eqn:Ef.
        -- inversion H; subst; clear H.
           destruct (sound_bindT a (typ_Var b) (ev_var_T a H1) H2 Eoa) as [Hs Ht].
           split; [exact Hs|]. split; [exact Ht|].
           split; [ apply kres_sbT; simpl; apply finer_b_sound; exact Ef | lia ].
        -- inversion H; subst; clear H.
           destruct (sound_bindT b (typ_Var a) (ev_var_T b H2) H1 Eob) as [Hs Ht].
           split; [exact Hs|]. split; [apply teq_sym; exact Ht|].
           split; [ apply kres_sbT; simpl; apply finer_b_total; exact Ef | lia ].
    + (* Grp, Grp *)
      destruct (gdecl_eq_dec w1 w1') as [->|]; [|discriminate].
      destruct (IHt _ _ _ _ _ _ H H1 H2) as (Hs & Ht & Hk & Hl).
      split; [exact Hs | split; [ apply teq_grp; exact Ht | split; [exact Hk | exact Hl]]].
  - intros D R1 R2 n s n' H H1 H2. cbn [unify_r] in H.
    destruct R1 as [| r | l T R1']; destruct R2 as [| q | l2 T2 R2'];
      try discriminate H.
    all: try (exact (var_left_R _ _ _ _ _ _ H H1 H2)).
    all: try (exact (var_right_R _ _ _ _ _ _ H H1 H2)).
    + inversion H; subst. split; [apply OkS_id | split; [apply req_refl | split; [ exact (kres_id D) | lia ]]].
    + (* Var, Var *)
      destruct (Atom.eq_dec r q) as [->|Hne].
      * inversion H; subst. split; [apply OkS_id | split; [apply req_refl | split; [ exact (kres_id D) | lia ]]].
      * inversion H; subst; clear H.
        assert (Eo : occR r (row_Var q) = false).
        { unfold occR. simpl. apply Bool.orb_false_iff. split; [ | reflexivity ].
          apply AtomSetFacts.not_mem_iff. intro Hin.
          apply AtomSetFacts.singleton_iff in Hin. congruence. }
        destruct (sound_bindR r (row_Var q) (ev_var_R r H1) H2 Eo) as [Hs Hr].
        split; [exact Hs|]. split; [exact Hr|]. split; [ exact (kres_id D) | lia ].
    + (* Ext, Ext *)
      destruct (rewrite_row l (frv_row (row_Ext l T R1')) (row_Ext l2 T2 R2') n)
        as [[[[T' R2''] s0] n1]|] eqn:Erw; [|discriminate].
      destruct (unify_t f D (apT s0 T) T' n1) as [[s1 n2]|] eqn:Eu1; [|discriminate].
      destruct (unify_r f D (apR s1 (apR s0 R1')) (apR s1 R2'') n2) as [[s2 n3]|] eqn:Eu2;
        [|discriminate].
      inversion H; subst; clear H.
      destruct (rewrite_row_sound _ _ _ _ _ _ _ _ Erw H2) as (Hs0 & HT' & HR2'' & Hrw & Hk0 & Hl0).
      destruct (EvR_ext_inv _ _ _ H1) as [HT HR1'].
      destruct (IHt _ _ _ _ _ _ Eu1 (EvT_ap s0 T Hs0 HT) HT') as (Hs1 & Ht1 & Hk1 & Hl1).
      destruct (IHr _ _ _ _ _ _ Eu2
                  (EvR_ap s1 _ Hs1 (EvR_ap s0 R1' Hs0 HR1'))
                  (EvR_ap s1 _ Hs1 HR2'')) as (Hs2 & Hr2 & Hk2 & Hl2).
      split; [ apply OkS_comp; [exact Hs2 | apply OkS_comp; auto] | ].
      split.
      { rewrite <- !apR_comp.
        assert (Hmid : req (apR s2 (apR s1 (apR s0 (row_Ext l2 T2 R2'))))
                           (row_Ext l (apT s2 (apT s1 T')) (apR s2 (apR s1 R2''))))
          by exact (req_apR s2 _ _ (req_apR s1 _ _ Hrw)).
        eapply req_trans; [ | apply req_sym; exact Hmid ].
        exact (req_head l _ _ _ _ (teq_apT s2 _ _ Ht1) Hr2). }
      split; [ exact (kres_scomp D D D (scomp s1 s0) s2 (kres_scomp D D D s0 s1 (Hk0 D) Hk1) Hk2) | lia ].
Qed.
