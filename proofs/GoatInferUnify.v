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

(* ------------------------------------------------------------------ *)
(* Pushing a sort onto the variables of a type                          *)
(* ------------------------------------------------------------------ *)

Lemma Good_rename : forall D n b k, DOk D n -> ev b -> finer k (D b) ->
  Good D n (sbT b (typ_Var (ea n))) (upd D (ea n) k) (S n).
Proof.
  intros D n b k Hd Hb Hf.
  refine (conj Hd (conj _ (conj (DOk_upd D n k Hd) (conj (le_S _ _ (le_n n))
    (conj (kres_upd D n k Hd) _))))).
  - apply OkS_sbT; [ exact Hb | apply EvT_var, ev_ea | exact I ].
  - intros a. unfold sbT. simpl.
    destruct (Atom.eq_dec a b) as [->|Hne]; cbn [sat].
    + rewrite upd_same. exact Hf.
    + exact (kres_upd D n k Hd a).
Qed.

Lemma push_sort_good : forall l D k n s D' n',
  push_sort D k l n = (s, D', n') -> (forall b, In b l -> ev b) ->
  OkS s /\ GoodU D n s D' n' /\ (forall x, ~ In x l -> sT s x = typ_Var x).
Proof.
  induction l as [|b l IH]; intros D k n s D' n' H Hev; cbn [push_sort] in H.
  - inversion H; subst; clear H. refine (conj OkS_id (conj (GoodU_id _ _) _)). intros x _. reflexivity.
  - destruct (finer_b (D b) k) eqn:Ef.
    + destruct (IH D k n s D' n' H (fun c Hc => Hev c (or_intror Hc))) as (Hs & Hg & Hfx).
      refine (conj Hs (conj Hg _)). intros x Hx. apply Hfx. intros Hin. apply Hx. right. exact Hin.
    + destruct (push_sort (upd D (ea n) k) k l (S n)) as [[s1 D1] n1] eqn:E.
      inversion H; subst; clear H.
      destruct (IH _ _ _ _ _ _ E (fun c Hc => Hev c (or_intror Hc))) as (Hs1 & [Hl1 Hg1] & Hfx).
      assert (Hb : ev b) by (apply Hev; left; reflexivity).
      assert (Hs0 : OkS (sbT b (typ_Var (ea n)))) by (apply OkS_sbT; [ exact Hb | apply EvT_var, ev_ea | exact I ]).
      refine (conj (OkS_comp _ _ Hs1 Hs0) (conj _ _)).
      * split; [ lia | intros Hd ].
        pose proof (Good_rename D n b k Hd Hb (finer_b_total _ _ Ef)) as G0.
        exact (Good_comp _ _ _ _ _ _ _ _ G0 (Hg1 (proj1 (proj2 (proj2 G0))))).
      * intros x Hx. unfold scomp, tcomp. simpl. unfold sbT. simpl.
        destruct (Atom.eq_dec x b) as [->|Hne]; [ exfalso; apply Hx; left; reflexivity | ].
        apply Hfx. intros Hin. apply Hx. right. exact Hin.
Qed.

Lemma bind_prop_sound : forall D a T n s D' n',
  bind_prop D a T n = Some (s, D', n') -> EvT (typ_Var a) -> EvT T ->
  OkS s /\ teq (apT s (typ_Var a)) (apT s T) /\ GoodU D n s D' n'.
Proof.
  intros D a T n s D' n' H Ha HT. unfold bind_prop in H.
  destruct (occT a T) eqn:Eo; [ discriminate | ].
  destruct (push_sort D (D a) (AtomSetImpl.elements (ftv_typ T)) n) as [[sp D1] n1] eqn:Ep.
  cbn zeta in H. destruct (occT a (apT sp T)) eqn:Eo'; [ discriminate | ].
  destruct (sat_b D1 (D1 a) (apT sp T)) eqn:Es; [ | discriminate ].
  inversion H; subst; clear H.
  destruct (occT_false _ _ Eo) as [Hnot _].
  assert (Hev : forall b, In b (AtomSetImpl.elements (ftv_typ T)) -> ev b).
  { intros b Hb. apply (proj1 HT). apply AtomSetFacts.elements_iff. apply SetoidList.In_InA; [ exact eq_equivalence | exact Hb ]. }
  destruct (push_sort_good _ _ _ _ _ _ _ Ep Hev) as (Hsp & Hgu & Hfx).
  assert (Hna : ~ In a (AtomSetImpl.elements (ftv_typ T))).
  { intros Hin. apply Hnot. apply AtomSetFacts.elements_iff.
    apply SetoidList.In_InA; [ exact eq_equivalence | exact Hin ]. }
  assert (HT' : EvT (apT sp T)) by (apply EvT_ap; assumption).
  destruct (sound_bindT a (apT sp T) (ev_var_T a Ha) HT' Eo') as [Hs0 Ht0].
  refine (conj (OkS_comp _ _ Hs0 Hsp) (conj _ _)).
  - rewrite <- !apT_comp.
    assert (E : apT sp (typ_Var a) = typ_Var a) by (unfold apT; simpl; apply Hfx; exact Hna).
    rewrite E. exact Ht0.
  - eapply GoodU_comp; [ exact Hgu | ].
    apply GoodU_same; [ exact Hs0 | apply kres_sbT; apply sat_b_sound; exact Es | lia ].
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

Lemma EvT_Unit : EvT typ_Unit.
Proof. split; intros a Ha; simpl in Ha; fsetdec. Qed.

Lemma EvT_Bool : EvT typ_Bool.
Proof. split; intros a Ha; simpl in Ha; fsetdec. Qed.

Lemma apT_id : forall T, apT sid T = T.
Proof. intros T. unfold apT, sid; simpl. apply ap_typ_pointwise_id; reflexivity. Qed.

Lemma apR_Maybe : forall s l P T R,
  apR s (row_Maybe l P T R) = row_Maybe l (apT s P) (apT s T) (apR s R).
Proof. reflexivity. Qed.

Lemma EvR_maybe_inv : forall l P T R, EvR (row_Maybe l P T R) -> EvT P /\ EvT T /\ EvR R.
Proof.
  intros l P T R [H1 H2]. simpl in H1, H2.
  split; [|split]; split; intros c Hc; [apply H1 | apply H2 | apply H1 | apply H2 | apply H1 | apply H2];
    fsetdec.
Qed.

Lemma EvR_maybe : forall l P T R, EvT P -> EvT T -> EvR R -> EvR (row_Maybe l P T R).
Proof.
  intros l P T R [H1 H2] [H3 H4] [H5 H6]. split; intros b Hb; simpl in Hb;
    repeat (apply AtomSetFacts.union_iff in Hb; destruct Hb as [Hb|Hb]); auto.
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

Lemma rewrite_row_sound : forall l av R n P' T' R' s n',
  rewrite_row l av R n = Some (P', T', R', s, n') -> EvR R ->
  OkS s /\ EvT P' /\ EvT T' /\ EvR R' /\ req (apR s R) (row_Maybe l P' T' R') /\
  (forall D, kres D D (sT s)) /\ n <= n'.
Proof.
  intros l av R. induction R as [| r | l' T'' R'' IH | l' P'' T'' R'' IH]; intros n P' T' R' s n' H HR;
    cbn [rewrite_row] in H.
  - inversion H; subst; clear H.
    split; [ apply OkS_id | ].
    split; [ exact EvT_Bool | ].
    split; [ apply EvT_var, ev_ea | ].
    split; [ split; intros b Hb; simpl in Hb; fsetdec | ].
    split; [ rewrite apR_id; apply req_sym; apply req_abs; reflexivity | ].
    split; [ intros D; exact (kres_id _) | lia ].
  - destruct (AtomSetImpl.mem r av); [discriminate|]. inversion H; subst; clear H.
    assert (Hr : ev r) by exact (ev_var_R r HR).
    assert (HEv : EvR (row_Maybe l (typ_Var (ea n)) (typ_Var (ea (S n))) (row_Var (ea (n + 2))))).
    { apply EvR_maybe; [ apply EvT_var, ev_ea | apply EvT_var, ev_ea | apply EvR_var, ev_ea ]. }
    split; [ apply OkS_sbR; [ auto | auto | exact (conj I (conj I I)) ] | ].
    split; [ apply EvT_var, ev_ea | ].
    split; [ apply EvT_var, ev_ea | ].
    split; [ apply EvR_var, ev_ea | ].
    split.
    { unfold apR, sbR; simpl. destruct (Atom.eq_dec r r); [|contradiction].
      apply req_refl. }
    split; [ intros D; exact (kres_id _) | lia ].
  - destruct (Nat.eqb l l') eqn:El.
    + inversion H; subst; clear H. apply Nat.eqb_eq in El; subst l'.
      destruct (EvR_ext_inv _ _ _ HR) as [HT HR''].
      split; [ apply OkS_id | ].
      split; [ exact EvT_Unit | ].
      split; [ exact HT | ].
      split; [ exact HR'' | ].
      split.
      { rewrite apR_Ext, apR_id, apT_id. apply req_sym. apply req_pre. }
      split; [ intros D; exact (kres_id _) | lia ].
    + destruct (rewrite_row l av R'' n) as [[[[[P0 T0] R3] s0] n1]|] eqn:E; [|discriminate].
      inversion H; subst; clear H.
      destruct (EvR_ext_inv _ _ _ HR) as [HT'' HR''].
      destruct (IH _ _ _ _ _ _ E HR'') as (Hs0 & HP0 & HT0 & HR3 & Hreq & Hk0 & Hle).
      split; [ exact Hs0 | ].
      split; [ exact HP0 | ].
      split; [ exact HT0 | ].
      split; [ apply EvR_ext; [ apply EvT_ap; auto | exact HR3 ] | ].
      split.
      { rewrite apR_Ext.
        eapply req_trans; [ apply req_head; [ apply teq_refl | exact Hreq ] | ].
        apply req_sym. apply req_swap_em. intro Heq. subst. rewrite Nat.eqb_refl in El. discriminate. }
      split; [ exact Hk0 | exact Hle ].
  - destruct (Nat.eqb l l') eqn:El.
    + inversion H; subst; clear H. apply Nat.eqb_eq in El; subst l'.
      destruct (EvR_maybe_inv _ _ _ _ HR) as (HP & HT & HR'').
      split; [ apply OkS_id | ].
      split; [ exact HP | ].
      split; [ exact HT | ].
      split; [ exact HR'' | ].
      split.
      { rewrite apR_Maybe, apR_id, !apT_id. apply req_refl. }
      split; [ intros D; exact (kres_id _) | lia ].
    + destruct (rewrite_row l av R'' n) as [[[[[P0 T0] R3] s0] n1]|] eqn:E; [|discriminate].
      inversion H; subst; clear H.
      destruct (EvR_maybe_inv _ _ _ _ HR) as (HP'' & HT'' & HR'').
      destruct (IH _ _ _ _ _ _ E HR'') as (Hs0 & HP0 & HT0 & HR3 & Hreq & Hk0 & Hle).
      split; [ exact Hs0 | ].
      split; [ exact HP0 | ].
      split; [ exact HT0 | ].
      split; [ apply EvR_maybe; [ apply EvT_ap; auto | apply EvT_ap; auto | exact HR3 ] | ].
      split.
      { rewrite apR_Maybe.
        eapply req_trans; [ apply req_maybe; [ apply teq_refl | apply teq_refl | exact Hreq ] | ].
        apply req_sym. apply req_swap_mm. intro Heq. subst. rewrite Nat.eqb_refl in El. discriminate. }
      split; [ exact Hk0 | exact Hle ].
Qed.

Lemma row_head_sound : forall R l P T R',
  row_head R = Some (l, P, T, R') -> EvR R ->
  EvT P /\ EvT T /\ EvR R' /\ req R (row_Maybe l P T R').
Proof.
  intros R l P T R' H HR. destruct R as [| r | l0 T0 R0 | l0 P0 T0 R0]; cbn [row_head] in H;
    try discriminate; inversion H; subst; clear H.
  - destruct (EvR_ext_inv _ _ _ HR) as [HT HR0].
    refine (conj EvT_Unit (conj HT (conj HR0 _))). apply req_sym, req_pre.
  - destruct (EvR_maybe_inv _ _ _ _ HR) as (HP & HT & HR0).
    exact (conj HP (conj HT (conj HR0 (req_refl _)))).
Qed.

Lemma row_step_req : forall s0 sp s1 s2 R1 R2 l P T R1' P' T' R2',
  req R1 (row_Maybe l P T R1') ->
  req (apR s0 R2) (row_Maybe l P' T' R2') ->
  teq (apT sp (apT s0 P)) (apT sp P') ->
  teq (apT s1 (apT sp (apT s0 T))) (apT s1 (apT sp T')) ->
  req (apR s2 (apR s1 (apR sp (apR s0 R1')))) (apR s2 (apR s1 (apR sp R2'))) ->
  req (apR (scomp s2 (scomp s1 (scomp sp s0))) R1) (apR (scomp s2 (scomp s1 (scomp sp s0))) R2).
Proof.
  intros s0 sp s1 s2 R1 R2 l P T R1' P' T' R2' H1 H2 Hp Ht Hr.
  rewrite <- !apR_comp.
  eapply req_trans.
  { exact (req_apR s2 _ _ (req_apR s1 _ _ (req_apR sp _ _ (req_apR s0 _ _ H1)))). }
  eapply req_trans; [ | apply req_sym; exact (req_apR s2 _ _ (req_apR s1 _ _ (req_apR sp _ _ H2))) ].
  rewrite !apR_Maybe. apply req_maybe.
  - apply teq_apT. exact (teq_apT s1 _ _ Hp).
  - exact (teq_apT s2 _ _ Ht).
  - exact Hr.
Qed.
(* ------------------------------------------------------------------ *)
(* Unification                                                          *)
(* ------------------------------------------------------------------ *)

Lemma var_left_R : forall D a R n s D' n',
  (if occR a R then (None : option (sub * denv * nat)) else Some (sbR a R, D, n)) = Some (s, D', n') ->
  EvR (row_Var a) -> EvR R ->
  OkS s /\ req (apR s (row_Var a)) (apR s R) /\ GoodU D n s D' n'.
Proof.
  intros D a R n s D' n' H Ha HR.
  destruct (occR a R) eqn:Eo; [discriminate|]. inversion H; subst; clear H.
  destruct (sound_bindR a R (ev_var_R a Ha) HR Eo) as [Hs Hr].
  split; [exact Hs|]. split; [exact Hr|]. apply GoodU_same; [ exact Hs | exact (kres_id _) | lia ].
Qed.

Lemma var_right_R : forall D b R n s D' n',
  (if occR b R then (None : option (sub * denv * nat)) else Some (sbR b R, D, n)) = Some (s, D', n') ->
  EvR R -> EvR (row_Var b) ->
  OkS s /\ req (apR s R) (apR s (row_Var b)) /\ GoodU D n s D' n'.
Proof.
  intros D b R n s D' n' H HR Hb.
  destruct (occR b R) eqn:Eo; [discriminate|]. inversion H; subst; clear H.
  destruct (sound_bindR b R (ev_var_R b Hb) HR Eo) as [Hs Hr].
  split; [exact Hs|]. split; [apply req_sym; exact Hr|].
  apply GoodU_same; [ exact Hs | exact (kres_id _) | lia ].
Qed.

Lemma unify_sound : forall f,
  (forall D T1 T2 n s D' n', unify_t f D T1 T2 n = Some (s, D', n') ->
     EvT T1 -> EvT T2 ->
     OkS s /\ teq (apT s T1) (apT s T2) /\ GoodU D n s D' n') /\
  (forall D R1 R2 n s D' n', unify_r f D R1 R2 n = Some (s, D', n') ->
     EvR R1 -> EvR R2 ->
     OkS s /\ req (apR s R1) (apR s R2) /\ GoodU D n s D' n').
Proof.
  induction f as [|f IH]; [ split; intros; discriminate | ].
  destruct IH as [IHt IHr].
  split.
  - intros D T1 T2 n s D' n' H H1 H2. cbn [unify_t] in H.
    destruct T1 as [| | | | | A B | R | a | i | B1 | w1 A1]; destruct T2 as [| | | | | A' B' | R' | b | i' | B1' | w1' A1'];
      try discriminate H.
    all: try (exact (bind_prop_sound _ _ _ _ _ _ _ H H1 H2)).
    all: try (destruct (bind_prop_sound _ _ _ _ _ _ _ H H2 H1) as (Hs & Ht & Hg);
              exact (conj Hs (conj (teq_sym _ _ Ht) Hg))).
    1-5: inversion H; subst; split; [apply OkS_id | split; [apply teq_refl | exact (GoodU_id _ _) ]].
    + (* Arrow, Arrow *)
      destruct (unify_t f D A A' n) as [[[s1 D1] n1]|] eqn:E1; [|discriminate].
      destruct (unify_t f D1 (apT s1 B) (apT s1 B') n1) as [[[s2 D2] n2]|] eqn:E2; [|discriminate].
      inversion H; subst; clear H.
      destruct (EvT_arrow_inv _ _ H1) as [EA EB].
      destruct (EvT_arrow_inv _ _ H2) as [EA' EB'].
      destruct (IHt _ _ _ _ _ _ _ E1 EA EA') as (Hs1 & Ht1 & Hg1).
      destruct (IHt _ _ _ _ _ _ _ E2 (EvT_ap s1 B Hs1 EB) (EvT_ap s1 B' Hs1 EB')) as (Hs2 & Ht2 & Hg2).
      split; [ apply OkS_comp; auto | ].
      split.
      { change (apT (scomp s2 s1) (typ_Arrow A B))
          with (typ_Arrow (apT (scomp s2 s1) A) (apT (scomp s2 s1) B)).
        change (apT (scomp s2 s1) (typ_Arrow A' B'))
          with (typ_Arrow (apT (scomp s2 s1) A') (apT (scomp s2 s1) B')).
        rewrite <- !apT_comp. apply teq_arrow.
        - apply teq_apT; exact Ht1.
        - exact Ht2. }
      exact (GoodU_comp _ _ _ _ _ _ _ _ Hg1 Hg2).
    + (* Record, Record *)
      destruct (IHr _ _ _ _ _ _ _ H) as (Hs & Hr & Hg); [exact H1 | exact H2 | ].
      split; [exact Hs | split; [apply teq_rec; exact Hr | exact Hg]].
    + (* Var, Var *)
      destruct (Atom.eq_dec a b) as [->|Hne].
      * inversion H; subst. split; [apply OkS_id | split; [apply teq_refl | exact (GoodU_id _ _) ]].
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
           apply GoodU_same; [ exact Hs | apply kres_sbT; simpl; apply finer_b_sound; exact Ef | lia ].
        -- inversion H; subst; clear H.
           destruct (sound_bindT b (typ_Var a) (ev_var_T b H2) H1 Eob) as [Hs Ht].
           split; [exact Hs|]. split; [apply teq_sym; exact Ht|].
           apply GoodU_same; [ exact Hs | apply kres_sbT; simpl; apply finer_b_total; exact Ef | lia ].
    + (* Grp, Grp *)
      destruct (gdecl_eq_dec w1 w1') as [->|]; [|discriminate].
      destruct (IHt _ _ _ _ _ _ _ H H1 H2) as (Hs & Ht & Hg).
      split; [exact Hs | split; [ apply teq_grp; exact Ht | exact Hg ]].
  - intros D R1 R2 n s D' n' H H1 H2. cbn [unify_r] in H.
    assert (Hgen : forall R1 R2, EvR R1 -> EvR R2 -> forall s D' n',
      (match row_head R1 with
       | None => None
       | Some (l, P, T, R1') =>
           match rewrite_row l (frv_row R1) R2 n with
           | None => None
           | Some (P', T', R2', s0, n1) =>
               match unify_t f D (apT s0 P) P' n1 with
               | None => None
               | Some (sp, D1, n2) =>
                   match unify_t f D1 (apT sp (apT s0 T)) (apT sp T') n2 with
                   | None => None
                   | Some (s1, D2, n3) =>
                       match unify_r f D2 (apR s1 (apR sp (apR s0 R1'))) (apR s1 (apR sp R2')) n3 with
                       | None => None
                       | Some (s2, D3, n4) => Some (scomp s2 (scomp s1 (scomp sp s0)), D3, n4)
                       end
                   end
               end
           end
       end) = Some (s, D', n') ->
      OkS s /\ req (apR s R1) (apR s R2) /\ GoodU D n s D' n').
    { intros R1' R2' Hg1 Hg2 s' D'' n'' Hg.
      destruct (row_head R1') as [[[[l P] T] R1'']|] eqn:Eh; [|discriminate].
      destruct (rewrite_row l (frv_row R1') R2' n) as [[[[[P' T'] R2''] s0] n1]|] eqn:Erw; [|discriminate].
      destruct (unify_t f D (apT s0 P) P' n1) as [[[sp D1] n2]|] eqn:Eu0; [|discriminate].
      destruct (unify_t f D1 (apT sp (apT s0 T)) (apT sp T') n2) as [[[s1 D2] n3]|] eqn:Eu1; [|discriminate].
      destruct (unify_r f D2 (apR s1 (apR sp (apR s0 R1''))) (apR s1 (apR sp R2'')) n3)
        as [[[s2 D3] n4]|] eqn:Eu2; [|discriminate].
      inversion Hg; subst; clear Hg.
      destruct (row_head_sound _ _ _ _ _ Eh Hg1) as (HP & HT & HR1' & Hhd).
      destruct (rewrite_row_sound _ _ _ _ _ _ _ _ _ Erw Hg2) as (Hs0 & HP' & HT' & HR2' & Hrw & Hk0 & Hl0).
      destruct (IHt _ _ _ _ _ _ _ Eu0 (EvT_ap s0 P Hs0 HP) HP') as (Hsp & Htp & Hgp).
      destruct (IHt _ _ _ _ _ _ _ Eu1 (EvT_ap sp _ Hsp (EvT_ap s0 T Hs0 HT)) (EvT_ap sp T' Hsp HT'))
        as (Hs1 & Ht1 & Hg1').
      destruct (IHr _ _ _ _ _ _ _ Eu2
                  (EvR_ap s1 _ Hs1 (EvR_ap sp _ Hsp (EvR_ap s0 R1'' Hs0 HR1')))
                  (EvR_ap s1 _ Hs1 (EvR_ap sp _ Hsp HR2'))) as (Hs2 & Hr2 & Hg2').
      split; [ apply OkS_comp; [ exact Hs2 | apply OkS_comp; [ exact Hs1 | apply OkS_comp; auto ] ] | ].
      split; [ exact (row_step_req s0 sp s1 s2 R1' R2' _ _ _ _ _ _ _ Hhd Hrw Htp Ht1 Hr2) | ].
      exact (GoodU_comp _ _ _ _ _ _ _ _
               (GoodU_comp _ _ _ _ _ _ _ _
                  (GoodU_comp _ _ _ _ _ _ _ _ (GoodU_same D n s0 n1 Hs0 (Hk0 D) Hl0) Hgp) Hg1') Hg2'). }
    destruct R1 as [| r | l T R1' | lm Pm Tm Rm]; destruct R2 as [| q | l2 T2 R2' | lm2 Pm2 Tm2 Rm2];
      try (exact (var_left_R _ _ _ _ _ _ _ H H1 H2));
      try (exact (var_right_R _ _ _ _ _ _ _ H H1 H2));
      try (exact (Hgen _ _ H1 H2 _ _ _ H)).
    + inversion H; subst. split; [apply OkS_id | split; [apply req_refl | exact (GoodU_id _ _) ]].
    + (* Empty, Maybe: the same equation read the other way *)
      destruct (IHr _ _ _ _ _ _ _ H H2 H1) as (Hs & Hr & Hg).
      split; [ exact Hs | split; [ apply req_sym; exact Hr | exact Hg ]].
    + (* Var, Var *)
      destruct (Atom.eq_dec r q) as [->|Hne].
      * inversion H; subst. split; [apply OkS_id | split; [apply req_refl | exact (GoodU_id _ _) ]].
      * inversion H; subst; clear H.
        assert (Eo : occR r (row_Var q) = false).
        { unfold occR. simpl. apply Bool.orb_false_iff. split; [ | reflexivity ].
          apply AtomSetFacts.not_mem_iff. intro Hin.
          apply AtomSetFacts.singleton_iff in Hin. congruence. }
        destruct (sound_bindR r (row_Var q) (ev_var_R r H1) H2 Eo) as [Hs Hr].
        split; [exact Hs|]. split; [exact Hr|]. apply GoodU_same; [ exact Hs | exact (kres_id _) | lia ].
Qed.
