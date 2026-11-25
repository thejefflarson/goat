(* Soundness of row-aware unification: a unifier the algorithm returns makes
   the two types equivalent under [teq] (the two rows under [req]), and
   respects the sorts of the kinding environment it ran in. *)

Require Import Metalib.Metatheory.
Require Import Goat.Goat_ott.
Require Import Goat.GoatProofs.
Require Import Goat.GoatRows.
Require Import Goat.GoatDefs.
Require Import Goat.GoatSubst.
Require Import Goat.GoatConv.
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

Lemma KR_sbT : forall D a T, sat D (D a) T -> KR D D (sbT a T).
Proof.
  intros D a T H. split; [ exact (kres_sbT D a T H) | intros r; exact (rkok_self D r) ].
Qed.

Lemma sound_meet : forall D a b, EvT (typ_Var a) -> EvT (typ_Var b) -> a <> b ->
  OkS (meet_float a b) /\
  teq (apT (meet_float a b) (typ_Var a)) (apT (meet_float a b) (typ_Var b)) /\
  KR D D (meet_float a b).
Proof.
  intros D a b Ha Hb Hne. unfold meet_float.
  assert (Hsa : OkS (sbT a typ_Float)) by (apply OkS_sbT; [ exact (ev_var_T a Ha) | (split; intros x Hx; simpl in Hx; fsetdec) | exact I ]).
  assert (Hsb : OkS (sbT b typ_Float)) by (apply OkS_sbT; [ exact (ev_var_T b Hb) | (split; intros x Hx; simpl in Hx; fsetdec) | exact I ]).
  refine (conj (OkS_comp _ _ Hsb Hsa) (conj _ _)).
  - assert (E1 : apT (sbT a typ_Float) (typ_Var a) = typ_Float).
    { unfold apT, sbT; simpl. destruct (Atom.eq_dec a a); [reflexivity | contradiction]. }
    assert (E2 : apT (sbT a typ_Float) (typ_Var b) = typ_Var b).
    { unfold apT, sbT; simpl. destruct (Atom.eq_dec b a); [ congruence | reflexivity ]. }
    assert (E3 : apT (sbT b typ_Float) typ_Float = typ_Float) by (unfold apT, sbT; simpl; reflexivity).
    assert (E4 : apT (sbT b typ_Float) (typ_Var b) = typ_Float).
    { unfold apT, sbT; simpl. destruct (Atom.eq_dec b b); [reflexivity | contradiction]. }
    rewrite <- !apT_comp. rewrite E1, E2, E3, E4. apply teq_refl.
  - apply KR_comp with (D' := D); apply KR_sbT; exact I.
Qed.

(* ------------------------------------------------------------------ *)
(* Pushing a sort onto the variables of a type                          *)
(* ------------------------------------------------------------------ *)

Lemma Good_rename : forall D n b k, DOk D n -> ev b -> finer k (D b) ->
  Good D n (sbT b (typ_Var (ea n))) (upd D (ea n) k) (S n).
Proof.
  intros D n b k Hd Hb Hf.
  refine (conj Hd (conj _ (conj (DOk_upd D n k Hd) (conj (le_S _ _ (le_n n))
    (conj (KR_upd D n k Hd) _))))).
  - apply OkS_sbT; [ exact Hb | apply EvT_var, ev_ea | exact I ].
  - split.
    + intros a. unfold sbT. simpl.
      destruct (Atom.eq_dec a b) as [->|Hne]; cbn [sat].
      * rewrite upd_same. exact Hf.
      * exact (proj1 (KR_upd D n k Hd) a).
    + intros r. exact (rkok_self (upd D (ea n) k) r).
Qed.

Lemma push_sort_good : forall l D k n s D' n',
  push_sort D k l n = (s, D', n') -> (forall b, In b l -> ev b) ->
  OkS s /\ GoodU D n s D' n' /\ (forall x, ~ In x l -> sT s x = typ_Var x) /\
  (forall r, sR s r = row_Var r).
Proof.
  induction l as [|b l IH]; intros D k n s D' n' H Hev; cbn [push_sort] in H.
  - inversion H; subst; clear H. refine (conj OkS_id (conj (GoodU_id _ _) (conj _ _))).
    + intros x _. reflexivity.
    + intros r. reflexivity.
  - destruct (finer_b (D b) k) eqn:Ef.
    + destruct (IH D k n s D' n' H (fun c Hc => Hev c (or_intror Hc))) as (Hs & Hg & Hfx & Hfr).
      refine (conj Hs (conj Hg (conj _ Hfr))). intros x Hx. apply Hfx. intros Hin. apply Hx. right. exact Hin.
    + destruct (finer_b k (D b)) eqn:Ef2.
      * destruct (push_sort (upd D (ea n) k) k l (S n)) as [[s1 D1] n1] eqn:E.
        inversion H; subst; clear H.
        destruct (IH _ _ _ _ _ _ E (fun c Hc => Hev c (or_intror Hc))) as (Hs1 & [Hl1 Hg1] & Hfx & Hfr).
        assert (Hb : ev b) by (apply Hev; left; reflexivity).
        assert (Hs0 : OkS (sbT b (typ_Var (ea n)))) by (apply OkS_sbT; [ exact Hb | apply EvT_var, ev_ea | exact I ]).
        refine (conj (OkS_comp _ _ Hs1 Hs0) (conj _ (conj _ _))).
        -- split; [ lia | intros Hd ].
           pose proof (Good_rename D n b k Hd Hb (finer_b_sound _ _ Ef2)) as G0.
           exact (Good_comp _ _ _ _ _ _ _ _ G0 (Hg1 (proj1 (proj2 (proj2 G0))))).
        -- intros x Hx. unfold scomp, tcomp. simpl. unfold sbT. simpl.
           destruct (Atom.eq_dec x b) as [->|Hne]; [ exfalso; apply Hx; left; reflexivity | ].
           apply Hfx. intros Hin. apply Hx. right. exact Hin.
        -- intros r. unfold scomp, rcomp. simpl. unfold sbT. simpl. unfold idr. simpl. exact (Hfr r).
      * destruct (push_sort D k l n) as [[s1 D1] n1] eqn:E.
        inversion H; subst; clear H.
        destruct (IH _ _ _ _ _ _ E (fun c Hc => Hev c (or_intror Hc))) as (Hs1 & Hg1 & Hfx & Hfr).
        assert (Hb : ev b) by (apply Hev; left; reflexivity).
        assert (Hs0 : OkS (sbT b typ_Float))
          by (apply OkS_sbT; [ exact Hb | (split; intros x Hx; simpl in Hx; fsetdec) | exact I ]).
        refine (conj (OkS_comp _ _ Hs1 Hs0) (conj _ (conj _ _))).
        -- exact (GoodU_comp _ _ _ _ _ _ _ _ (GoodU_same D n (sbT b typ_Float) n Hs0 (KR_sbT D b typ_Float I) (le_n n)) Hg1).
        -- intros x Hx. unfold scomp, tcomp. simpl. unfold sbT. simpl.
           destruct (Atom.eq_dec x b) as [->|Hne]; [ exfalso; apply Hx; left; reflexivity | ].
           apply Hfx. intros Hin. apply Hx. right. exact Hin.
        -- intros r. unfold scomp, rcomp. simpl. unfold sbT. simpl. unfold idr. simpl. exact (Hfr r).
Qed.

Lemma Good_rename_r : forall D n q K, DOk D n -> ev q ->
  finer (rk_sort K) (rk_sort (drk D q)) ->
  (forall l, rk_lacks (drk D q) l = true -> rk_lacks K l = true) ->
  Good D n (sbR q (row_Var (ea n))) (rupd D (ea n) K) (S n).
Proof.
  intros D n q K Hd Hq Hf Hl.
  pose proof (Good_rupd D n K Hd) as (_ & _ & Hd' & Hle & Hi & _).
  assert (Hs : OkS (sbR q (row_Var (ea n)))).
  { apply OkS_sbR; [ exact Hq | apply EvR_var, ev_ea | exact I ]. }
  refine (conj Hd (conj Hs (conj Hd' (conj Hle (conj Hi (conj (proj1 Hi) _)))))).
  intros r0. unfold sbR. cbn [sR].
  destruct (Atom.eq_dec r0 q) as [->|Hne].
  - split.
    + cbn [rsat]. rewrite rupd_same. exact Hf.
    + intros l Hl'. cbn [rlacksD]. rewrite rupd_same. exact (Hl l Hl').
  - exact (proj2 Hi r0).
Qed.

Lemma push_sort_r_good : forall l D k n s D' n',
  push_sort_r D k l n = (s, D', n') -> (forall b, In b l -> ev b) ->
  OkS s /\ GoodU D n s D' n' /\ (forall x, sT s x = typ_Var x).
Proof.
  induction l as [|b l IH]; intros D k n s D' n' H Hev; cbn [push_sort_r] in H.
  - inversion H; subst; clear H. refine (conj OkS_id (conj (GoodU_id _ _) _)). intros x. reflexivity.
  - destruct (finer_b (rk_sort (drk D b)) k) eqn:Ef.
    + exact (IH D k n s D' n' H (fun c Hc => Hev c (or_intror Hc))).
    + destruct (finer_b k (rk_sort (drk D b))) eqn:Ef2.
      * destruct (push_sort_r (rupd D (ea n) (RK k (rk_lacks (drk D b)))) k l (S n)) as [[s1 D1] n1] eqn:E.
        inversion H; subst; clear H.
        destruct (IH _ _ _ _ _ _ E (fun c Hc => Hev c (or_intror Hc))) as (Hs1 & [Hl1 Hg1] & Hft).
        assert (Hb : ev b) by (apply Hev; left; reflexivity).
        assert (Hs0 : OkS (sbR b (row_Var (ea n)))) by (apply OkS_sbR; [ exact Hb | apply EvR_var, ev_ea | exact I ]).
        refine (conj (OkS_comp _ _ Hs1 Hs0) (conj _ _)).
        -- split; [ lia | intros Hd ].
           pose proof (Good_rename_r D n b (RK k (rk_lacks (drk D b))) Hd Hb
                         (finer_b_sound _ _ Ef2) (fun l Hl => Hl)) as G0.
           exact (Good_comp _ _ _ _ _ _ _ _ G0 (Hg1 (proj1 (proj2 (proj2 G0))))).
        -- intros x. unfold scomp, tcomp. simpl. unfold sbR. simpl. unfold idt. simpl. exact (Hft x).
      * exact (IH D k n s D' n' H (fun c Hc => Hev c (or_intror Hc))).
Qed.

Lemma push_sort_r_fix : forall l D k n s D' n',
  push_sort_r D k l n = (s, D', n') -> forall x, ~ In x l -> sR s x = row_Var x.
Proof.
  induction l as [|b l IH]; intros D k n s D' n' H x Hx; cbn [push_sort_r] in H.
  - inversion H; subst; clear H. reflexivity.
  - destruct (finer_b (rk_sort (drk D b)) k).
    + apply (IH _ _ _ _ _ _ H). intros Hin. apply Hx. right. exact Hin.
    + destruct (finer_b k (rk_sort (drk D b))).
      * destruct (push_sort_r (rupd D (ea n) (RK k (rk_lacks (drk D b)))) k l (S n)) as [[s1 D1] n1] eqn:E.
        inversion H; subst; clear H.
        assert (Hxb : x <> b) by (intros ->; apply Hx; left; reflexivity).
        assert (Hxl : ~ In x l) by (intros Hin; apply Hx; right; exact Hin).
        pose proof (IH _ _ _ _ _ _ E x Hxl) as Hs1.
        unfold scomp, rcomp. simpl. unfold sbR. simpl.
        destruct (Atom.eq_dec x b) as [->|_]; [ exfalso; apply Hxb; reflexivity | ].
        exact Hs1.
      * apply (IH _ _ _ _ _ _ H). intros Hin. apply Hx. right. exact Hin.
Qed.

Lemma live_sub_mut :
  (forall T, ftv_live T [<=] ftv_typ T /\ frv_live T [<=] frv_typ T) /\
  (forall R, ftv_live_row R [<=] ftv_row R /\ frv_live_row R [<=] frv_row R).
Proof.
  apply typ_row_mutind; cbn [ftv_live frv_live ftv_typ frv_typ ftv_live_row frv_live_row ftv_row frv_row];
    intros; repeat match goal with H : _ /\ _ |- _ => destruct H end;
    try (match goal with |- context [is_abs ?P] => destruct (is_abs P) end);
    split; fsetdec.
Qed.

Lemma na_live_mut :
  (forall T, na T = true -> ftv_live T = ftv_typ T /\ frv_live T = frv_typ T) /\
  (forall R, nar R = true -> ftv_live_row R = ftv_row R /\ frv_live_row R = frv_row R).
Proof.
  apply typ_row_mutind; cbn [na nar ftv_live frv_live ftv_live_row frv_live_row ftv_typ frv_typ ftv_row frv_row];
    intros; try (split; reflexivity).
  - apply Bool.andb_true_iff in H1 as [H1 H2].
    destruct (H H1) as [E1 E2]. destruct (H0 H2) as [E3 E4]. rewrite E1, E2, E3, E4. split; reflexivity.
  - destruct (H H0) as [E1 E2]. rewrite E1, E2. split; reflexivity.
  - destruct (H H0) as [E1 E2]. rewrite E1, E2. split; reflexivity.
  - destruct (H H0) as [E1 E2]. rewrite E1, E2. split; reflexivity.
  - apply Bool.andb_true_iff in H1 as [H1 H2].
    destruct (H H1) as [E1 E2]. destruct (H0 H2) as [E3 E4]. rewrite E1, E2, E3, E4. split; reflexivity.
  - apply Bool.andb_true_iff in H2 as [H2 H4]. apply Bool.andb_true_iff in H2 as [H2 H3].
    apply Bool.andb_true_iff in H2 as [H2 H5].
    apply Bool.negb_true_iff in H2. rewrite H2.
    destruct (H H5) as [E1 E2]. destruct (H0 H3) as [E3 E4]. destruct (H1 H4) as [E5 E6].
    rewrite E1, E2, E3, E4, E5, E6. split; reflexivity.
Qed.

Lemma ftv_live_sub : forall T, ftv_live T [<=] ftv_typ T.
Proof. intros T. exact (proj1 ((proj1 live_sub_mut) T)). Qed.

Lemma frv_live_sub : forall T, frv_live T [<=] frv_typ T.
Proof. intros T. exact (proj2 ((proj1 live_sub_mut) T)). Qed.

Lemma ftv_live_row_sub : forall R, ftv_live_row R [<=] ftv_row R.
Proof. intros R. exact (proj1 ((proj2 live_sub_mut) R)). Qed.

Lemma frv_live_row_sub : forall R, frv_live_row R [<=] frv_row R.
Proof. intros R. exact (proj2 ((proj2 live_sub_mut) R)). Qed.

Lemma bind_prop0_sound : forall D a T n s D' n',
  bind_prop0 D a T n = Some (s, D', n') -> EvT (typ_Var a) -> EvT T ->
  OkS s /\ teq (apT s (typ_Var a)) (apT s T) /\ GoodU D n s D' n'.
Proof.
  intros D a T n s D' n' H Ha HT. unfold bind_prop0 in H.
  destruct (occT a T) eqn:Eo; [ discriminate | ].
  destruct (push_sort D (D a) (AtomSetImpl.elements (ftv_live T)) n) as [[sp D1] n1] eqn:Ep.
  destruct (push_sort_r D1 (D1 a) (AtomSetImpl.elements (frv_live T)) n1) as [[sr D2] n2] eqn:Epr.
  cbn zeta in H. destruct (occT a (apT sr (apT sp T))) eqn:Eo'; [ discriminate | ].
  destruct (sat_b D2 (D2 a) (apT sr (apT sp T))) eqn:Es; [ | discriminate ].
  inversion H; subst; clear H.
  destruct (occT_false _ _ Eo) as [Hnot _].
  assert (Hev : forall b, In b (AtomSetImpl.elements (ftv_live T)) -> ev b).
  { intros b Hb. apply (proj1 HT). apply ftv_live_sub. apply AtomSetFacts.elements_iff. apply SetoidList.In_InA; [ exact eq_equivalence | exact Hb ]. }
  assert (Hevr : forall b, In b (AtomSetImpl.elements (frv_live T)) -> ev b).
  { intros b Hb. apply (proj2 HT). apply frv_live_sub. apply AtomSetFacts.elements_iff. apply SetoidList.In_InA; [ exact eq_equivalence | exact Hb ]. }
  destruct (push_sort_good _ _ _ _ _ _ _ Ep Hev) as (Hsp & Hgu & Hfx & _).
  destruct (push_sort_r_good _ _ _ _ _ _ _ Epr Hevr) as (Hsr & Hgr & Hft).
  assert (Hna : ~ In a (AtomSetImpl.elements (ftv_live T))).
  { intros Hin. apply Hnot. apply ftv_live_sub. apply AtomSetFacts.elements_iff.
    apply SetoidList.In_InA; [ exact eq_equivalence | exact Hin ]. }
  assert (HT' : EvT (apT sr (apT sp T))) by (apply EvT_ap; [ exact Hsr | apply EvT_ap; assumption ]).
  destruct (sound_bindT a (apT sr (apT sp T)) (ev_var_T a Ha) HT' Eo') as [Hs0 Ht0].
  refine (conj (OkS_comp _ _ Hs0 (OkS_comp _ _ Hsr Hsp)) (conj _ _)).
  - rewrite <- !apT_comp.
    assert (E : apT sr (apT sp (typ_Var a)) = typ_Var a).
    { assert (E1 : apT sp (typ_Var a) = typ_Var a) by (unfold apT; simpl; apply Hfx; exact Hna).
      rewrite E1. unfold apT. simpl. apply Hft. }
    rewrite E. exact Ht0.
  - eapply GoodU_comp; [ eapply GoodU_comp; [ exact Hgu | exact Hgr ] | ].
    apply GoodU_same; [ exact Hs0 | apply KR_sbT; apply sat_b_sound; exact Es | lia ].
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
(* Dropping absent entries                                              *)
(* ------------------------------------------------------------------ *)

Lemma req_drop_abs : forall R, req R (drop_abs R).
Proof.
  induction R as [| r | l T R IH | l P T R IH]; simpl.
  - apply req_empty.
  - apply req_var.
  - apply req_head; [ apply teq_refl | exact IH ].
  - destruct (is_abs P && rlacks l (drop_abs R)) eqn:E.
    + apply Bool.andb_true_iff in E as [Ha Hl]. destruct P; try discriminate Ha.
      eapply req_trans; [ apply req_maybe; [ apply teq_refl | apply teq_refl | exact IH ] | ].
      apply req_abs. exact Hl.
    + apply req_maybe; [ apply teq_refl | apply teq_refl | exact IH ].
Qed.

Lemma drop_abs_fv : forall R,
  ftv_row (drop_abs R) [<=] ftv_row R /\ frv_row (drop_abs R) [<=] frv_row R.
Proof.
  induction R as [| r | l T R IH | l P T R IH]; simpl.
  - split; fsetdec.
  - split; fsetdec.
  - destruct IH as [H1 H2]. split; fsetdec.
  - destruct IH as [H1 H2].
    destruct (is_abs P && rlacks l (drop_abs R)); split; simpl; fsetdec.
Qed.

Lemma EvR_drop_abs : forall R, EvR R -> EvR (drop_abs R).
Proof.
  intros R [H1 H2]. destruct (drop_abs_fv R) as [F1 F2].
  split; intros b Hb; [ apply H1 | apply H2 ]; [ apply F1 | apply F2 ]; exact Hb.
Qed.

Lemma req_via_drop : forall s R R',
  req (apR s (drop_abs R)) (apR s (drop_abs R')) -> req (apR s R) (apR s R').
Proof.
  intros s R R' H.
  eapply req_trans; [ apply req_apR; exact (req_drop_abs R) | ].
  eapply req_trans; [ exact H | ].
  apply req_sym. apply req_apR. exact (req_drop_abs R').
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

Lemma rewrite_row_sound : forall l av D R n P' T' R' s D' n',
  rewrite_row l av D R n = Some (P', T', R', s, D', n') -> EvR R ->
  OkS s /\ EvT P' /\ EvT T' /\ EvR R' /\ req (apR s R) (row_Maybe l P' T' R') /\
  GoodU D n s D' n'.
Proof.
  intros l av D R. induction R as [| r | l' T'' R'' IH | l' P'' T'' R'' IH]; intros n P' T' R' s D' n' H HR;
    cbn [rewrite_row] in H.
  - inversion H; subst; clear H.
    split; [ apply OkS_id | ].
    split; [ exact EvT_Bool | ].
    split; [ apply EvT_var, ev_ea | ].
    split; [ split; intros b Hb; simpl in Hb; fsetdec | ].
    split; [ rewrite apR_id; apply req_sym; apply req_abs; reflexivity | ].
    exact (GoodU_same _ n sid (S n) OkS_id (KR_id _) (le_S _ _ (le_n n))).
  - destruct (AtomSetImpl.mem r av); [discriminate|].
    assert (Hr : ev r) by exact (ev_var_R r HR).
    destruct (rk_lacks (drk D r) l) eqn:El.
    + (* the row variable lacks [l]: it becomes [l ^ Bool : a ; r'] *)
      inversion H; subst; clear H.
      assert (HEv : EvR (row_Maybe l typ_Bool (typ_Var (ea n)) (row_Var (ea (S n))))).
      { apply EvR_maybe; [ exact EvT_Bool | apply EvT_var, ev_ea | apply EvR_var, ev_ea ]. }
      assert (Hs : OkS (sbR r (row_Maybe l typ_Bool (typ_Var (ea n)) (row_Var (ea (S n))))))
        by (apply OkS_sbR; [ auto | auto | exact (conj I (conj I I)) ]).
      split; [ exact Hs | ].
      split; [ exact EvT_Bool | ].
      split; [ apply EvT_var, ev_ea | ].
      split; [ apply EvR_var, ev_ea | ].
      split.
      { unfold apR, sbR; simpl. destruct (Atom.eq_dec r r); [|contradiction].
        apply req_refl. }
      split; [ lia | intros Hd ].
      pose proof (Good_pre D n (S n) sid (rupd D (ea (S n)) (drk D r)) (S (S n))
                    ltac:(lia) Hd (Good_rupd D (S n) (drk D r) (DOk_mono D n (S n) Hd ltac:(lia))))
        as (_ & _ & Hd' & Hl & Hi & _).
      replace (n + 2) with (S (S n)) by lia.
      refine (conj Hd (conj Hs (conj Hd' (conj Hl (conj Hi (conj (proj1 Hi) _)))))).
      intros r0. unfold sbR. cbn [sR].
      destruct (Atom.eq_dec r0 r) as [->|Hne].
      * split.
        -- cbn [rsat]. split; [ left; reflexivity | ]. cbn [rsat]. rewrite rupd_same. apply finer_refl.
        -- intros l' Hl'. cbn [rlacksD]. destruct (Nat.eqb l' l) eqn:Ell; cbn [rlacksD].
           ++ apply Nat.eqb_eq in Ell. subst l'. cbn [is_abs]. rewrite rupd_same. exact Hl'.
           ++ rewrite rupd_same. exact Hl'.
      * exact (proj2 Hi r0).
    + (* the row variable has a kind: its sort reaches the field variable *)
      inversion H; subst; clear H.
      assert (HEv : EvR (row_Maybe l (typ_Var (ea n)) (typ_Var (ea (S n))) (row_Var (ea (n + 2))))).
      { apply EvR_maybe; [ apply EvT_var, ev_ea | apply EvT_var, ev_ea | apply EvR_var, ev_ea ]. }
      assert (Hs : OkS (sbR r (row_Maybe l (typ_Var (ea n)) (typ_Var (ea (S n))) (row_Var (ea (n + 2))))))
        by (apply OkS_sbR; [ auto | auto | exact (conj I (conj I I)) ]).
      split; [ exact Hs | ].
      split; [ apply EvT_var, ev_ea | ].
      split; [ apply EvT_var, ev_ea | ].
      split; [ apply EvR_var, ev_ea | ].
      split.
      { unfold apR, sbR; simpl. destruct (Atom.eq_dec r r); [|contradiction].
        apply req_refl. }
      split; [ lia | intros Hd ].
      replace (n + 3) with (S (n + 2)) by lia.
      pose proof (Good_pre D n (S n) sid (upd D (ea (S n)) (rk_sort (drk D r))) (S (S n))
                    ltac:(lia) Hd (Good_upd D (S n) (rk_sort (drk D r)) (DOk_mono D n (S n) Hd ltac:(lia))))
        as G1.
      pose proof (Good_rupd (upd D (ea (S n)) (rk_sort (drk D r))) (n + 2) (drk D r)
                    (DOk_mono _ (S (S n)) (n + 2) (Good_dok _ _ _ _ _ G1) ltac:(lia))) as G2.
      pose proof (Good_lift _ _ _ _ _ _ _ G1 (Good_pre _ (S (S n)) (n + 2) _ _ _ ltac:(lia)
                    (Good_dok _ _ _ _ _ G1) G2)) as G3.
      destruct G3 as (_ & _ & Hd' & Hl & Hi & _).
      refine (conj Hd (conj Hs (conj Hd' (conj Hl (conj Hi (conj (proj1 Hi) _)))))).
      intros r0. unfold sbR. cbn [sR].
      destruct (Atom.eq_dec r0 r) as [->|Hne].
      * split.
        -- cbn [rsat]. split; [ right; cbn [sat]; unfold rupd; cbn [dsort]; rewrite upd_same; apply finer_refl | ].
           cbn [rsat]. rewrite rupd_same. apply finer_refl.
        -- intros l' Hl'. cbn [rlacksD]. destruct (Nat.eqb l' l) eqn:Ell; cbn [rlacksD].
           ++ apply Nat.eqb_eq in Ell. subst l'. rewrite El in Hl'. discriminate Hl'.
           ++ rewrite rupd_same. exact Hl'.
      * exact (proj2 Hi r0).
  - destruct (Nat.eqb l l') eqn:El.
    + inversion H; subst; clear H. apply Nat.eqb_eq in El; subst l'.
      destruct (EvR_ext_inv _ _ _ HR) as [HT HR''].
      split; [ apply OkS_id | ].
      split; [ exact EvT_Unit | ].
      split; [ exact HT | ].
      split; [ exact HR'' | ].
      split.
      { rewrite apR_Ext, apR_id, apT_id. apply req_sym. apply req_pre. }
      exact (GoodU_same _ _ sid _ OkS_id (KR_id _) (le_n _)).
    + destruct (rewrite_row l av D R'' n) as [[[[[[P0 T0] R3] s0] D1] n1]|] eqn:E; [|discriminate].
      inversion H; subst; clear H.
      destruct (EvR_ext_inv _ _ _ HR) as [HT'' HR''].
      destruct (IH _ _ _ _ _ _ _ E HR'') as (Hs0 & HP0 & HT0 & HR3 & Hreq & Hg).
      split; [ exact Hs0 | ].
      split; [ exact HP0 | ].
      split; [ exact HT0 | ].
      split; [ apply EvR_ext; [ apply EvT_ap; auto | exact HR3 ] | ].
      split.
      { rewrite apR_Ext.
        eapply req_trans; [ apply req_head; [ apply teq_refl | exact Hreq ] | ].
        apply req_sym. apply req_swap_em. intro Heq. subst. rewrite Nat.eqb_refl in El. discriminate. }
      exact Hg.
  - destruct (Nat.eqb l l') eqn:El.
    + inversion H; subst; clear H. apply Nat.eqb_eq in El; subst l'.
      destruct (EvR_maybe_inv _ _ _ _ HR) as (HP & HT & HR'').
      split; [ apply OkS_id | ].
      split; [ exact HP | ].
      split; [ exact HT | ].
      split; [ exact HR'' | ].
      split.
      { rewrite apR_Maybe, apR_id, !apT_id. apply req_refl. }
      exact (GoodU_same _ _ sid _ OkS_id (KR_id _) (le_n _)).
    + destruct (rewrite_row l av D R'' n) as [[[[[[P0 T0] R3] s0] D1] n1]|] eqn:E; [|discriminate].
      inversion H; subst; clear H.
      destruct (EvR_maybe_inv _ _ _ _ HR) as (HP'' & HT'' & HR'').
      destruct (IH _ _ _ _ _ _ _ E HR'') as (Hs0 & HP0 & HT0 & HR3 & Hreq & Hg).
      split; [ exact Hs0 | ].
      split; [ exact HP0 | ].
      split; [ exact HT0 | ].
      split; [ apply EvR_maybe; [ apply EvT_ap; auto | apply EvT_ap; auto | exact HR3 ] | ].
      split.
      { rewrite apR_Maybe.
        eapply req_trans; [ apply req_maybe; [ apply teq_refl | apply teq_refl | exact Hreq ] | ].
        apply req_sym. apply req_swap_mm. intro Heq. subst. rewrite Nat.eqb_refl in El. discriminate. }
      exact Hg.
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

(* What the tail variable of a row and its labels let a kind demand of it. *)
Lemma rlacksD_spine : forall (D : denv) (K : rkind) R,
  (forall t, row_tail R = Some t -> forall l, rk_lacks K l = true -> rk_lacks (drk D t) l = true) ->
  lacks_ok K R = true ->
  forall l, rk_lacks K l = true -> rlacksD D l R = true.
Proof.
  intros D K R. induction R as [| r | l' T R IH | l' P T R IH]; intros Ht Hok l Hl; cbn [rlacksD].
  - reflexivity.
  - exact (Ht r eq_refl l Hl).
  - cbn [lacks_ok] in Hok. apply Bool.andb_true_iff in Hok as [H1 H2].
    apply Bool.andb_true_iff. split.
    + apply Bool.negb_true_iff. apply Bool.not_true_is_false. intros Heq.
      apply Nat.eqb_eq in Heq. subst l'. apply Bool.negb_true_iff in H1. rewrite Hl in H1. discriminate H1.
    + apply IH; [ exact Ht | exact H2 | exact Hl ].
  - cbn [lacks_ok] in Hok. apply Bool.andb_true_iff in Hok as [H1 H2].
    destruct (Nat.eqb l l') eqn:Heq.
    + apply Nat.eqb_eq in Heq. subst l'. rewrite Hl in H1. cbn in H1.
      apply Bool.andb_true_iff. split; [ exact H1 | apply IH; [ exact Ht | exact H2 | exact Hl ] ].
    + apply IH; [ exact Ht | exact H2 | exact Hl ].
Qed.

Lemma row_tail_ap_none : forall st sr R,
  row_tail R = None -> row_tail (ap_row st sr R) = None.
Proof.
  intros st sr R. induction R as [| r | l' T R IH | l' P T R IH]; cbn [row_tail ap_row]; intros H;
    first [ reflexivity | discriminate | apply IH; exact H ].
Qed.

Lemma row_tail_ap_var : forall st sr R q,
  row_tail R = Some q -> row_tail (ap_row st sr R) = row_tail (sr q).
Proof.
  intros st sr R q. induction R as [| r | l' T R IH | l' P T R IH]; cbn [row_tail ap_row]; intros H;
    first [ discriminate | (inversion H; subst; reflexivity) | apply IH; exact H ].
Qed.

Lemma row_tail_frv : forall R q, row_tail R = Some q -> q `in` frv_row R.
Proof.
  intros R q. induction R as [| r | l' T R IH | l' P T R IH]; cbn [row_tail frv_row]; intros H;
    first [ discriminate | (inversion H; subst; fsetdec) | (apply IH in H; fsetdec) ].
Qed.

Lemma push_sort_drk : forall l D k n s D' n',
  push_sort D k l n = (s, D', n') -> drk D' = drk D.
Proof.
  induction l as [|b l IH]; intros D k n s D' n' H; cbn [push_sort] in H.
  - inversion H; subst; reflexivity.
  - destruct (finer_b (D b) k).
    + exact (IH _ _ _ _ _ _ H).
    + destruct (finer_b k (D b));
        [ | destruct (push_sort D k l n) as [[s1 D1] n1] eqn:E1; inversion H; subst; exact (IH _ _ _ _ _ _ E1) ].
      destruct (push_sort (upd D (ea n) k) k l (S n)) as [[s1 D1] n1] eqn:E.
      inversion H; subst; clear H. exact (IH _ _ _ _ _ _ E).
Qed.

Lemma bind_row_fin_sound : forall r R sq D0 D n n0 s D' n',
  bind_row_fin r R sq D0 n0 = Some (s, D', n') ->
  EvR (row_Var r) -> EvR R -> OkS sq -> GoodU D n sq D0 n0 -> apR sq (row_Var r) = row_Var r ->
  (forall t, row_tail (apR sq R) = Some t ->
     forall l, rk_lacks (drk D0 r) l = true -> rk_lacks (drk D0 t) l = true) ->
  OkS s /\ req (apR s (row_Var r)) (apR s R) /\ GoodU D n s D' n'.
Proof.
  intros r R sq D0 D n n0 s D' n' H Hr HR Hsq Hgq Hfix Htl. unfold bind_row_fin in H.
  destruct (push_sort D0 (rk_sort (drk D0 r)) (AtomSetImpl.elements (ftv_row (apR sq R))) n0)
    as [[sp D1] n1] eqn:Ep.
  cbn zeta in H.
  destruct (occR r (apR sp (apR sq R))) eqn:Eo; [ discriminate | ].
  destruct (rsat_b D1 (rk_sort (drk D1 r)) (apR sp (apR sq R))
            && lacks_ok (drk D1 r) (apR sp (apR sq R))) eqn:Ec; [ | discriminate ].
  inversion H; subst; clear H.
  apply Bool.andb_true_iff in Ec as [Es Hl].
  assert (HR0 : EvR (apR sq R)) by (apply EvR_ap; assumption).
  assert (Hev : forall b, In b (AtomSetImpl.elements (ftv_row (apR sq R))) -> ev b).
  { intros b Hb. apply (proj1 HR0). apply AtomSetFacts.elements_iff.
    apply SetoidList.In_InA; [ exact eq_equivalence | exact Hb ]. }
  destruct (push_sort_good _ _ _ _ _ _ _ Ep Hev) as (Hsp & Hgp & Hfx & Hfr).
  pose proof (push_sort_drk _ _ _ _ _ _ _ Ep) as Hdrk.
  assert (HR1 : EvR (apR sp (apR sq R))) by (apply EvR_ap; assumption).
  assert (Hrv : ev r) by exact (ev_var_R r Hr).
  destruct (sound_bindR r _ Hrv HR1 Eo) as [Hsb Hreq].
  assert (Hspr : apR sp (row_Var r) = row_Var r) by (unfold apR; simpl; apply Hfr).
  refine (conj (OkS_comp _ _ Hsb (OkS_comp _ _ Hsp Hsq)) (conj _ _)).
  - rewrite <- !apR_comp. rewrite Hfix, Hspr. exact Hreq.
  - eapply GoodU_comp; [ eapply GoodU_comp; [ exact Hgq | exact Hgp ] | ].
    apply GoodU_same; [ exact Hsb | | exact (le_n _) ].
    split; [ exact (kres_id _) | ].
    intros r0. unfold sbR. cbn [sR].
    destruct (Atom.eq_dec r0 r) as [->|Hne].
    + split.
      * exact (proj2 (sat_b_sound_mut _) _ _ Es).
      * apply rlacksD_spine; [ | exact Hl ].
        intros t Ht l Hlk. rewrite Hdrk in Hlk |- *.
        change (apR sp (apR sq R)) with (ap_row (sT sp) (sR sp) (apR sq R)) in Ht.
        destruct (row_tail (apR sq R)) as [q0|] eqn:Et0.
        -- rewrite (row_tail_ap_var _ _ _ _ Et0) in Ht. rewrite (Hfr q0) in Ht. cbn in Ht.
           inversion Ht; subst t. exact (Htl q0 eq_refl l Hlk).
        -- rewrite (row_tail_ap_none _ _ _ Et0) in Ht. discriminate Ht.
    + exact (rkok_self _ r0).
Qed.

Lemma bind_row_core_sound : forall D r R n s D' n',
  bind_row_core D r R n = Some (s, D', n') -> EvR (row_Var r) -> EvR R ->
  OkS s /\ req (apR s (row_Var r)) (apR s R) /\ GoodU D n s D' n'.
Proof.
  intros D r R n s D' n' H Hr HR. unfold bind_row_core in H.
  destruct (occR r R) eqn:Eo; [ discriminate | ].
  destruct (row_tail R) as [q|] eqn:Et.
  - assert (Hq : q `in` frv_row R) by exact (row_tail_frv _ _ Et).
    destruct (occR_false _ _ Eo) as [Hnot _].
    assert (Hqr : q <> r) by (intros Heq; subst; contradiction).
    assert (Hqv : ev q) by exact ((proj2 HR) q Hq).
    assert (Hsq : OkS (sbR q (row_Var (ea n)))).
    { apply OkS_sbR; [ exact Hqv | apply EvR_var, ev_ea | exact I ]. }
    refine (bind_row_fin_sound _ _ _ _ D n _ _ _ _ H Hr HR Hsq _ _ _).
    + split; [ lia | intros Hd ].
      pose proof (Good_rupd D n (rk_join (drk D r) (drk D q)) Hd) as (_ & _ & Hd' & Hl & Hi & _).
      refine (conj Hd (conj Hsq (conj Hd' (conj Hl (conj Hi (conj (proj1 Hi) _)))))).
      intros r0. unfold sbR. cbn [sR]. destruct (Atom.eq_dec r0 q) as [->|Hne].
      * split.
        -- cbn [rsat]. rewrite rupd_same. cbn [rk_join rk_sort].
           destruct (finer_b (rk_sort (drk D r)) (rk_sort (drk D q))) eqn:Ef;
             [ apply finer_b_sound; exact Ef | apply finer_refl ].
        -- intros l Hl'. cbn [rlacksD]. rewrite rupd_same. cbn [rk_join rk_lacks].
           rewrite Hl'. apply Bool.orb_true_r.
      * exact (proj2 Hi r0).
    + unfold apR, sbR; simpl. destruct (Atom.eq_dec r q) as [->|]; [ contradiction | reflexivity ].
    + intros t Ht l Hl'.
      change (apR (sbR q (row_Var (ea n))) R)
        with (ap_row (sT (sbR q (row_Var (ea n)))) (sR (sbR q (row_Var (ea n)))) R) in Ht.
      rewrite (row_tail_ap_var _ _ _ _ Et) in Ht. unfold sbR in Ht. cbn [sR] in Ht.
      destruct (Atom.eq_dec q q) as [_|]; [ | contradiction ]. cbn in Ht. inversion Ht; subst t.
      destruct (Atom.eq_dec r (ea n)) as [->|Hne]; [ exact Hl' | ].
      rewrite (rupd_other D (ea n) _ r Hne) in Hl'. rewrite rupd_same. cbn [rk_join rk_lacks].
      rewrite Hl'. reflexivity.
  - refine (bind_row_fin_sound _ _ _ _ D n _ _ _ _ H Hr HR OkS_id (GoodU_id D n) eq_refl _).
    intros t Ht. exfalso. unfold apR in Ht. simpl in Ht.
    rewrite (row_tail_ap_none _ _ _ Et) in Ht. discriminate Ht.
Qed.

Lemma abs_vars_ftv : forall K R p, In p (abs_vars K R) -> p `in` ftv_row R.
Proof.
  intros K R p. induction R as [| r | l' T R IH | l' P T R IH]; intros H.
  - contradiction.
  - contradiction.
  - cbn [abs_vars] in H. apply IH in H. cbn [ftv_row]. fsetdec.
  - cbn [ftv_row]. destruct P as [| | | | | | | a | | |]; cbn [abs_vars] in H;
      try (apply IH in H; fsetdec).
    destruct (rk_lacks K l').
    + destruct H as [<-|H]; [ simpl; fsetdec | apply IH in H; simpl; fsetdec ].
    + apply IH in H. simpl. fsetdec.
Qed.

Lemma bool_sub_ok : forall D ps, (forall p, In p ps -> ev p) ->
  forallb (fun p => sat_b D (D p) typ_Bool) ps = true ->
  OkS (bool_sub ps) /\ KR D D (bool_sub ps) /\ (forall r, sR (bool_sub ps) r = row_Var r).
Proof.
  intros D ps. induction ps as [|p ps IH]; intros Hev Hf; cbn [bool_sub].
  - exact (conj OkS_id (conj (KR_id D) (fun r => eq_refl))).
  - cbn [forallb] in Hf. apply Bool.andb_true_iff in Hf as [Hp Hf].
    destruct (IH (fun q Hq => Hev q (or_intror Hq)) Hf) as (Hs & Hk & Hr).
    refine (conj (OkS_comp _ _ Hs (OkS_sbT p typ_Bool (Hev p (or_introl eq_refl)) EvT_Bool I)) (conj _ _)).
    + exact (KR_comp _ _ _ _ _ (KR_sbT D p typ_Bool (sat_b_sound _ _ _ Hp)) Hk).
    + intros r. unfold scomp, rcomp. simpl. unfold sbT, idr. simpl. exact (Hr r).
Qed.

Lemma bool_sub_in : forall ps x, In x ps -> sT (bool_sub ps) x = typ_Bool.
Proof.
  induction ps as [|p ps IH]; intros x Hx; [ destruct Hx | ].
  change (ap_typ (sT (bool_sub ps)) (sR (bool_sub ps)) (sT (sbT p typ_Bool) x) = typ_Bool).
  cbn [sT sbT]. destruct (Atom.eq_dec x p) as [->|Hne]; [ reflexivity | ].
  destruct Hx as [E|Hx]; [ exfalso; apply Hne; symmetry; exact E | exact (IH x Hx) ].
Qed.

Lemma bool_sub_out : forall ps x, ~ In x ps -> sT (bool_sub ps) x = typ_Var x.
Proof.
  induction ps as [|p ps IH]; intros x Hx; [ reflexivity | ].
  change (ap_typ (sT (bool_sub ps)) (sR (bool_sub ps)) (sT (sbT p typ_Bool) x) = typ_Var x).
  cbn [sT sbT]. destruct (Atom.eq_dec x p) as [->|Hne].
  - exfalso. apply Hx. left. reflexivity.
  - exact (IH x (fun H => Hx (or_intror H))).
Qed.

Lemma bool_sub_R : forall ps q, sR (bool_sub ps) q = row_Var q.
Proof.
  induction ps as [|p ps IH]; intros q; [ reflexivity | ].
  change (ap_row (sT (bool_sub ps)) (sR (bool_sub ps)) (sR (sbT p typ_Bool) q) = row_Var q).
  cbn [sR sbT]. exact (IH q).
Qed.

Lemma bool_sub_T_cases : forall ps x, sT (bool_sub ps) x = typ_Var x \/ sT (bool_sub ps) x = typ_Bool.
Proof.
  intros ps x. destruct (in_dec Atom.eq_dec x ps) as [H|H];
    [ right; exact (bool_sub_in ps x H) | left; exact (bool_sub_out ps x H) ].
Qed.

Lemma bool_sub_agree : forall Sg ps, (forall p, In p ps -> sT Sg p = typ_Bool) ->
  (forall x, sT Sg x = apT Sg (sT (bool_sub ps) x)) /\ (forall q, sR Sg q = apR Sg (sR (bool_sub ps) q)).
Proof.
  intros Sg ps H. split.
  - intros x. destruct (in_dec Atom.eq_dec x ps) as [Hin|Hin].
    + rewrite (bool_sub_in ps x Hin). exact (H x Hin).
    + rewrite (bool_sub_out ps x Hin). reflexivity.
  - intros q. rewrite bool_sub_R. reflexivity.
Qed.

Lemma bind_row0_sound : forall D r R n s D' n',
  bind_row0 D r R n = Some (s, D', n') -> EvR (row_Var r) -> EvR R ->
  OkS s /\ req (apR s (row_Var r)) (apR s R) /\ GoodU D n s D' n'.
Proof.
  intros D r R n s D' n' H Hr HR. unfold bind_row0 in H. cbn zeta in H.
  destruct (forallb (fun p => sat_b D (D p) typ_Bool) (abs_vars (drk D r) R)) eqn:Ef; [ | discriminate ].
  destruct (occR r (apR (bool_sub (abs_vars (drk D r) R)) R)) eqn:Eo; [ discriminate | ].
  destruct (push_sort_r D (rk_sort (drk D r))
              (AtomSetImpl.elements (frv_row (apR (bool_sub (abs_vars (drk D r) R)) R))) n)
    as [[sr D1] n1] eqn:Ep.
  destruct (bind_row_core D1 r (apR sr (apR (bool_sub (abs_vars (drk D r) R)) R)) n1)
    as [[[s1 D2] n2]|] eqn:E; [ | discriminate ].
  inversion H; subst; clear H.
  destruct (bool_sub_ok D _ (fun p Hp => (proj1 HR) p (abs_vars_ftv _ _ _ Hp)) Ef)
    as (Hs0 & Hk0 & Hr0).
  set (R0 := apR (bool_sub (abs_vars (drk D r) R)) R) in *.
  assert (HR0 : EvR R0) by (apply EvR_ap; assumption).
  assert (Hevr : forall b, In b (AtomSetImpl.elements (frv_row R0)) -> ev b).
  { intros b Hb. apply (proj2 HR0). apply AtomSetFacts.elements_iff.
    apply SetoidList.In_InA; [ exact eq_equivalence | exact Hb ]. }
  destruct (push_sort_r_good _ _ _ _ _ _ _ Ep Hevr) as (Hsr & Hgr & _).
  assert (Hnr : ~ In r (AtomSetImpl.elements (frv_row R0))).
  { intros Hin. destruct (occR_false _ _ Eo) as [Hnot _]. apply Hnot.
    apply AtomSetFacts.elements_iff. apply SetoidList.In_InA; [ exact eq_equivalence | exact Hin ]. }
  pose proof (push_sort_r_fix _ _ _ _ _ _ _ Ep r Hnr) as Hfr.
  destruct (bind_row_core_sound _ _ _ _ _ _ _ E Hr (EvR_ap _ _ Hsr HR0)) as (Hs1 & Hreq & Hg).
  refine (conj (OkS_comp _ _ Hs1 (OkS_comp _ _ Hsr Hs0)) (conj _ _)).
  - rewrite <- !apR_comp.
    assert (Ev : apR sr (apR (bool_sub (abs_vars (drk D r) R)) (row_Var r)) = row_Var r).
    { assert (E1 : apR (bool_sub (abs_vars (drk D r) R)) (row_Var r) = row_Var r)
        by (unfold apR; simpl; apply Hr0).
      rewrite E1. unfold apR. simpl. exact Hfr. }
    rewrite Ev. exact Hreq.
  - eapply GoodU_comp; [ eapply GoodU_comp; [ | exact Hgr ] | exact Hg ].
    apply GoodU_same; [ exact Hs0 | exact Hk0 | exact (le_n _) ].
Qed.

Lemma bool_sub_fix : forall ps a, ~ In a ps -> sT (bool_sub ps) a = typ_Var a.
Proof.
  induction ps as [|p ps IH]; intros a Ha; cbn [bool_sub].
  - reflexivity.
  - unfold scomp, tcomp. simpl. unfold sbT. simpl.
    destruct (Atom.eq_dec a p) as [->|Hne]; [ exfalso; apply Ha; left; reflexivity | ].
    exact (IH a (fun Hin => Ha (or_intror Hin))).
Qed.

Lemma bool_sub_rfix : forall ps r, sR (bool_sub ps) r = row_Var r.
Proof.
  induction ps as [|p ps IH]; intros r; cbn [bool_sub].
  - reflexivity.
  - unfold scomp, rcomp. simpl. unfold sbT, idr. simpl. apply IH.
Qed.

Lemma forced_ftv_mut :
  (forall T k p, In p (forced k T) -> p `in` ftv_typ T) /\
  (forall R k p, In p (forced_row k R) -> p `in` ftv_row R).
Proof.
  apply typ_row_mutind; cbn [forced forced_row ftv_typ ftv_row].
  - intros k p H. contradiction.
  - intros k p H. contradiction.
  - intros k p H. contradiction.
  - intros k p H. contradiction.
  - intros k p H. contradiction.
  - intros A _ B _ k p H. contradiction.
  - intros R IH k p H. destruct k; cbn in H; first [ contradiction | exact (IH _ _ H) ].
  - intros a k p H. contradiction.
  - intros i k p H. contradiction.
  - intros B IH k p H. destruct k; cbn in H; first [ contradiction | exact (IH _ _ H) ].
  - intros w A _ k p H. contradiction.
  - intros k p H. contradiction.
  - intros r k p H. contradiction.
  - intros l T IHT R IHR k p H. apply in_app_or in H as [H|H];
      [ apply IHT in H | apply IHR in H ]; fsetdec.
  - intros l P _ T IHT R IHR k p H.
    assert (Hrest : In p (forced_row k R) -> p `in` ftv_typ P `union` (ftv_typ T `union` ftv_row R))
      by (intros HH; apply IHR in HH; fsetdec).
    destruct P as [| | | | | | | q | | | ]; cbn [forced_row] in H; apply in_app_or in H as [H|H];
      try exact (Hrest H);
      first
        [ (destruct (perm_b k T) eqn:Eperm;
           [ apply IHT in H; fsetdec | destruct H as [H|[]]; subst; simpl; fsetdec ])
        | (cbn in H; first [ contradiction | (apply IHT in H; fsetdec) ]) ].
Qed.

Lemma forced_ftv : forall k T p, In p (forced k T) -> p `in` ftv_typ T.
Proof. intros k T p H. exact (proj1 forced_ftv_mut T k p H). Qed.

Lemma forced_row_ftv : forall k R p, In p (forced_row k R) -> p `in` ftv_row R.
Proof. intros k R p H. exact (proj2 forced_ftv_mut R k p H). Qed.

Lemma bind_prop_sound : forall D a T n s D' n',
  bind_prop D a T n = Some (s, D', n') -> EvT (typ_Var a) -> EvT T ->
  OkS s /\ teq (apT s (typ_Var a)) (apT s T) /\ GoodU D n s D' n'.
Proof.
  intros D a T n s D' n' H Ha HT. unfold bind_prop in H.
  destruct (bind_prop0 D a T n) as [r|] eqn:E0.
  - inversion H; subst; clear H. exact (bind_prop0_sound _ _ _ _ _ _ _ E0 Ha HT).
  - destruct (occT a T) eqn:Eo; [ discriminate | ].
    destruct (forced (D a) T) as [|p0 ps0] eqn:Ef; [ discriminate | ].
    remember (p0 :: ps0) as ps eqn:Eps; clear Eps.
    destruct (forallb (fun p => sat_b D (D p) typ_Bool) ps) eqn:Eb; [ | discriminate ].
    destruct (bind_prop0 D a (apT (bool_sub ps) T) n) as [[[s1 D1] n1]|] eqn:E1; [ | discriminate ].
    injection H as <- <- <-.
    assert (Hps : forall p, In p ps -> ev p).
    { intros p Hp. apply (proj1 HT). apply (forced_ftv (D a) T). rewrite Ef. exact Hp. }
    destruct (bool_sub_ok D ps Hps Eb) as (Hs0 & Hk0 & Hr0).
    assert (HT0 : EvT (apT (bool_sub ps) T)) by (apply EvT_ap; assumption).
    destruct (bind_prop0_sound _ _ _ _ _ _ _ E1 Ha HT0) as (Hs1 & Ht1 & Hg1).
    assert (Hna : apT (bool_sub ps) (typ_Var a) = typ_Var a).
    { change (apT (bool_sub ps) (typ_Var a)) with (sT (bool_sub ps) a). apply bool_sub_fix. intros Hin.
      destruct (occT_false _ _ Eo) as [Hnot _]. apply Hnot.
      apply (forced_ftv (D a) T). rewrite Ef. exact Hin. }
    refine (conj (OkS_comp _ _ Hs1 Hs0) (conj _ _)).
    + assert (Hxa : apT (scomp s1 (bool_sub ps)) (typ_Var a) = apT s1 (typ_Var a))
        by (rewrite <- apT_comp, Hna; reflexivity).
      assert (Hxb : apT (scomp s1 (bool_sub ps)) T = apT s1 (apT (bool_sub ps) T))
        by (rewrite apT_comp; reflexivity).
      rewrite Hxa, Hxb. exact Ht1.
    + eapply GoodU_comp; [ | exact Hg1 ].
      apply GoodU_same; [ exact Hs0 | exact Hk0 | exact (le_n _) ].
Qed.

Lemma bind_row_sound : forall D r R n s D' n',
  bind_row D r R n = Some (s, D', n') -> EvR (row_Var r) -> EvR R ->
  OkS s /\ req (apR s (row_Var r)) (apR s R) /\ GoodU D n s D' n'.
Proof.
  intros D r R n s D' n' H Hr HR. unfold bind_row in H.
  destruct (bind_row0 D r R n) as [x|] eqn:E0.
  - inversion H; subst; clear H. exact (bind_row0_sound _ _ _ _ _ _ _ E0 Hr HR).
  - destruct (forced_row (rk_sort (drk D r)) R) as [|p0 ps0] eqn:Ef; [ discriminate | ].
    remember (p0 :: ps0) as ps eqn:Eps; clear Eps.
    destruct (forallb (fun p => sat_b D (D p) typ_Bool) ps) eqn:Eb; [ | discriminate ].
    destruct (bind_row0 D r (apR (bool_sub ps) R) n) as [[[s1 D1] n1]|] eqn:E1; [ | discriminate ].
    injection H as <- <- <-.
    assert (Hps : forall p, In p ps -> ev p).
    { intros p Hp. apply (proj1 HR). apply (forced_row_ftv (rk_sort (drk D r)) R). rewrite Ef. exact Hp. }
    destruct (bool_sub_ok D ps Hps Eb) as (Hs0 & Hk0 & Hr0).
    assert (HR0 : EvR (apR (bool_sub ps) R)) by (apply EvR_ap; assumption).
    destruct (bind_row0_sound _ _ _ _ _ _ _ E1 Hr HR0) as (Hs1 & Hq1 & Hg1).
    assert (Hna : apR (bool_sub ps) (row_Var r) = row_Var r)
      by (change (apR (bool_sub ps) (row_Var r)) with (sR (bool_sub ps) r); apply bool_sub_rfix).
    refine (conj (OkS_comp _ _ Hs1 Hs0) (conj _ _)).
    + assert (Hxa : apR (scomp s1 (bool_sub ps)) (row_Var r) = apR s1 (row_Var r))
        by (rewrite <- apR_comp, Hna; reflexivity).
      assert (Hxb : apR (scomp s1 (bool_sub ps)) R = apR s1 (apR (bool_sub ps) R))
        by (rewrite apR_comp; reflexivity).
      rewrite Hxa, Hxb. exact Hq1.
    + eapply GoodU_comp; [ | exact Hg1 ].
      apply GoodU_same; [ exact Hs0 | exact Hk0 | exact (le_n _) ].
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
      destruct (IHr _ _ _ _ _ _ _ H) as (Hs & Hr & Hg); [exact (EvR_drop_abs _ H1) | exact (EvR_drop_abs _ H2) | ].
      split; [exact Hs | split; [apply teq_rec; exact (req_via_drop _ _ _ Hr) | exact Hg]].
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
           apply GoodU_same; [ exact Hs | apply KR_sbT; simpl; apply finer_b_sound; exact Ef | lia ].
        -- destruct (finer_b (D a) (D b)) eqn:Ef2.
           ++ inversion H; subst; clear H.
              destruct (sound_bindT b (typ_Var a) (ev_var_T b H2) H1 Eob) as [Hs Ht].
              split; [exact Hs|]. split; [apply teq_sym; exact Ht|].
              apply GoodU_same; [ exact Hs | apply KR_sbT; simpl; apply finer_b_sound; exact Ef2 | lia ].
           ++ inversion H; subst; clear H.
              destruct (sound_meet D' a b H1 H2 Hne) as [Hs [Ht Hk]].
              split; [exact Hs|]. split; [exact Ht|].
              apply GoodU_same; [ exact Hs | exact Hk | lia ].
    + (* Grp, Grp *)
      destruct (gdecl_eq_dec w1 w1') as [->|]; [|discriminate].
      destruct (IHt _ _ _ _ _ _ _ H H1 H2) as (Hs & Ht & Hg).
      split; [exact Hs | split; [ apply teq_grp; exact Ht | exact Hg ]].
  - intros D R1 R2 n s D' n' H H1 H2. cbn [unify_r] in H.
    assert (Hgen : forall R1 R2, EvR R1 -> EvR R2 -> forall s D' n',
      (match row_head R1 with
       | None => None
       | Some (l, P, T, R1') =>
           match rewrite_row l (side_av R1) D R2 n with
           | None => None
           | Some (P', T', R2', s0, D0, n1) =>
               match unify_t f D0 (apT s0 P) P' n1 with
               | None => None
               | Some (sp, D1, n2) =>
                   match unify_t f D1 (apT sp (apT s0 T)) (apT sp T') n2 with
                   | None => None
                   | Some (s1, D2, n3) =>
                       match unify_r f D2 (drop_abs (apR s1 (apR sp (apR s0 R1')))) (drop_abs (apR s1 (apR sp R2'))) n3 with
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
      destruct (rewrite_row l (side_av R1') D R2' n) as [[[[[[P' T'] R2''] s0] D0] n1]|] eqn:Erw; [|discriminate].
      destruct (unify_t f D0 (apT s0 P) P' n1) as [[[sp D1] n2]|] eqn:Eu0; [|discriminate].
      destruct (unify_t f D1 (apT sp (apT s0 T)) (apT sp T') n2) as [[[s1 D2] n3]|] eqn:Eu1; [|discriminate].
      destruct (unify_r f D2 (drop_abs (apR s1 (apR sp (apR s0 R1'')))) (drop_abs (apR s1 (apR sp R2''))) n3)
        as [[[s2 D3] n4]|] eqn:Eu2; [|discriminate].
      inversion Hg; subst; clear Hg.
      destruct (row_head_sound _ _ _ _ _ Eh Hg1) as (HP & HT & HR1' & Hhd).
      destruct (rewrite_row_sound _ _ _ _ _ _ _ _ _ _ _ Erw Hg2) as (Hs0 & HP' & HT' & HR2' & Hrw & Hg0).
      destruct (IHt _ _ _ _ _ _ _ Eu0 (EvT_ap s0 P Hs0 HP) HP') as (Hsp & Htp & Hgp).
      destruct (IHt _ _ _ _ _ _ _ Eu1 (EvT_ap sp _ Hsp (EvT_ap s0 T Hs0 HT)) (EvT_ap sp T' Hsp HT'))
        as (Hs1 & Ht1 & Hg1').
      destruct (IHr _ _ _ _ _ _ _ Eu2
                  (EvR_drop_abs _ (EvR_ap s1 _ Hs1 (EvR_ap sp _ Hsp (EvR_ap s0 R1'' Hs0 HR1'))))
                  (EvR_drop_abs _ (EvR_ap s1 _ Hs1 (EvR_ap sp _ Hsp HR2')))) as (Hs2 & Hr2' & Hg2').
      pose proof (req_via_drop _ _ _ Hr2') as Hr2.
      split; [ apply OkS_comp; [ exact Hs2 | apply OkS_comp; [ exact Hs1 | apply OkS_comp; auto ] ] | ].
      split; [ exact (row_step_req s0 sp s1 s2 R1' R2' _ _ _ _ _ _ _ Hhd Hrw Htp Ht1 Hr2) | ].
      exact (GoodU_comp _ _ _ _ _ _ _ _
               (GoodU_comp _ _ _ _ _ _ _ _
                  (GoodU_comp _ _ _ _ _ _ _ _ Hg0 Hgp) Hg1') Hg2'). }
    destruct R1 as [| r | l T R1' | lm Pm Tm Rm]; destruct R2 as [| q | l2 T2 R2' | lm2 Pm2 Tm2 Rm2];
      try (exact (bind_row_sound _ _ _ _ _ _ _ H H1 H2));
      try (destruct (bind_row_sound _ _ _ _ _ _ _ H H2 H1) as (Hs & Hr & Hg);
           exact (conj Hs (conj (req_sym _ _ Hr) Hg)));
      try (exact (Hgen _ _ H1 H2 _ _ _ H)).
    + inversion H; subst. split; [apply OkS_id | split; [apply req_refl | exact (GoodU_id _ _) ]].
    + (* Empty, Maybe: the same equation read the other way *)
      destruct (IHr _ _ _ _ _ _ _ H H2 H1) as (Hs & Hr & Hg).
      split; [ exact Hs | split; [ apply req_sym; exact Hr | exact Hg ]].
    + (* Var, Var *)
      destruct (Atom.eq_dec r q) as [->|Hne].
      * inversion H; subst. split; [apply OkS_id | split; [apply req_refl | exact (GoodU_id _ _) ]].
      * exact (bind_row_sound _ _ _ _ _ _ _ H H1 H2).
Qed.

(* ------------------------------------------------------------------ *)
(* Conversion at the environment: the unifier [unify_tD]                *)
(* ------------------------------------------------------------------ *)

Lemma nf_fv_mut : forall D,
  (forall T, ftv_typ (nfT D T) [<=] ftv_typ T /\ frv_typ (nfT D T) [<=] frv_typ T) /\
  (forall R, ftv_row (nfR D R) [<=] ftv_row R /\ frv_row (nfR D R) [<=] frv_row R).
Proof.
  intros D. apply typ_row_mutind.
  - split; fsetdec.
  - split; fsetdec.
  - split; fsetdec.
  - split; fsetdec.
  - split; fsetdec.
  - intros A HA B HB. cbn [nfT ftv_typ frv_typ]. destruct HA as [HA1 HA2], HB as [HB1 HB2]. split; fsetdec.
  - intros R HR. cbn [nfT ftv_typ frv_typ]. exact HR.
  - split; fsetdec.
  - split; fsetdec.
  - split; fsetdec.
  - split; fsetdec.
  - split; fsetdec.
  - split; fsetdec.
  - intros l T HT R HR. rewrite nfR_ext. cbn [ftv_row frv_row].
    destruct HT as [HT1 HT2], HR as [HR1 HR2]. split; fsetdec.
  - intros l P HP T HT R HR. rewrite nfR_maybe.
    destruct HP as [HP1 HP2], HT as [HT1 HT2], HR as [HR1 HR2].
    destruct (is_abs P && rlacksD D l (nfR D R)); cbv iota; cbn [ftv_row frv_row]; split; fsetdec.
Qed.

Lemma EvR_nfR : forall D R, EvR R -> EvR (nfR D R).
Proof.
  intros D R [H1 H2]. destruct (proj2 (nf_fv_mut D) R) as [F1 F2].
  split; intros b Hb; [ apply H1 | apply H2 ]; [ apply F1 | apply F2 ]; exact Hb.
Qed.

Lemma Good_rkres : forall D n s D' n', Good D n s D' n' -> rkres D D' (sR s).
Proof. intros D n s D' n' G. destruct G as (_ & _ & _ & _ & _ & [_ Hr]). exact Hr. Qed.

Lemma lift_teqD : forall D n s D' n' T T', Good D n s D' n' -> teqD D T T' ->
  teqD D' (apT s T) (apT s T').
Proof. intros D n s D' n' T T' G H. exact (teqD_ap D D' (sT s) (sR s) T T' (Good_rkres _ _ _ _ _ G) H). Qed.

Lemma reqD_ap : forall D D' st sr R R', rkres D D' sr -> reqD D R R' ->
  reqD D' (ap_row st sr R) (ap_row st sr R').
Proof.
  intros D D' st sr R R' Hk H.
  pose proof (teqD_ap D D' st sr (typ_Record R) (typ_Record R') Hk (teqD_Record _ _ _ H)) as H0.
  cbn [ap_typ] in H0. destruct (teqD_Record_inv _ _ _ H0) as (R2 & E & Hq). injection E as <-. exact Hq.
Qed.

Lemma lift_reqD : forall D n s D' n' R R', Good D n s D' n' -> reqD D R R' ->
  reqD D' (apR s R) (apR s R').
Proof. intros D n s D' n' R R' G H. exact (reqD_ap D D' (sT s) (sR s) R R' (Good_rkres _ _ _ _ _ G) H). Qed.

Lemma req_via_nfD : forall D D' s R R', rkres D D' (sR s) ->
  reqD D' (apR s (nfR D R)) (apR s (nfR D R')) -> reqD D' (apR s R) (apR s R').
Proof.
  intros D D' s R R' Hk H.
  eapply reqD_trans; [ exact (proj2 (teqD_ap_nf_mut D D' (sT s) (sR s) Hk) R) | ].
  eapply reqD_trans; [ exact H | ].
  apply reqD_sym. exact (proj2 (teqD_ap_nf_mut D D' (sT s) (sR s) Hk) R').
Qed.

Lemma Good_DOk : forall D n s D' n', Good D n s D' n' -> DOk D' n'.
Proof. intros D n s D' n' G. exact (proj1 (proj2 (proj2 G))). Qed.

Lemma GoodU_Good : forall D n s D' n', DOk D n -> GoodU D n s D' n' -> Good D n s D' n'.
Proof. intros D n s D' n' HD [_ H]. exact (H HD). Qed.

Lemma row_step_reqD : forall s0 sp s1 s2 R1 R2 l P T R1' P' T' R2' D1 n2 D2 n3 D3 n4,
  Good D1 n2 s1 D2 n3 -> Good D2 n3 s2 D3 n4 ->
  req R1 (row_Maybe l P T R1') ->
  req (apR s0 R2) (row_Maybe l P' T' R2') ->
  teqD D1 (apT sp (apT s0 P)) (apT sp P') ->
  teqD D2 (apT s1 (apT sp (apT s0 T))) (apT s1 (apT sp T')) ->
  reqD D3 (apR s2 (apR s1 (apR sp (apR s0 R1')))) (apR s2 (apR s1 (apR sp R2'))) ->
  reqD D3 (apR (scomp s2 (scomp s1 (scomp sp s0))) R1) (apR (scomp s2 (scomp s1 (scomp sp s0))) R2).
Proof.
  intros s0 sp s1 s2 R1 R2 l P T R1' P' T' R2' D1 n2 D2 n3 D3 n4 G1 G2 H1 H2 Hp Ht Hr.
  rewrite <- !apR_comp.
  eapply reqD_trans.
  { apply req_reqD. exact (req_apR s2 _ _ (req_apR s1 _ _ (req_apR sp _ _ (req_apR s0 _ _ H1)))). }
  eapply reqD_trans; [ | apply reqD_sym; apply req_reqD;
    exact (req_apR s2 _ _ (req_apR s1 _ _ (req_apR sp _ _ H2))) ].
  rewrite !apR_Maybe. apply reqD_maybe.
  - exact (lift_teqD _ _ _ _ _ _ _ G2 (lift_teqD _ _ _ _ _ _ _ G1 Hp)).
  - exact (lift_teqD _ _ _ _ _ _ _ G2 Ht).
  - exact Hr.
Qed.

Lemma bool_sub_one : forall p, sT (bool_sub (p :: nil)) p = typ_Bool.
Proof.
  intros p. cbn [bool_sub]. unfold scomp, tcomp. simpl. unfold sbT. simpl.
  destruct (Atom.eq_dec p p) as [_|N]; [ reflexivity | congruence ].
Qed.

Lemma absent_clash_inv : forall D l P T T' R1 R2 p,
  absent_clash D l P T T' R1 R2 = Some p ->
  P = typ_Var p /\ sat_b D (D p) typ_Bool = true /\
  rlacksD D l R1 = true /\ rlacksD D l R2 = true.
Proof.
  intros D l P T T' R1 R2 p H. unfold absent_clash in H.
  destruct P as [| | | | | | | q | | | ]; try discriminate H.
  destruct (clash D T T' && sat_b D (D q) typ_Bool && rlacksD D l R1 && rlacksD D l R2) eqn:E;
    [ | discriminate H ].
  injection H as <-.
  apply Bool.andb_true_iff in E as [E Hr2]. apply Bool.andb_true_iff in E as [E Hr1].
  apply Bool.andb_true_iff in E as [_ Hs].
  exact (conj eq_refl (conj Hs (conj Hr1 Hr2))).
Qed.

Lemma reqD_drop_abs : forall D l T C, rlacksD D l C = true ->
  reqD D (row_Maybe l typ_Bool T C) C.
Proof.
  intros D l T C H. unfold reqD. rewrite nfR_maybe. cbn [is_abs].
  rewrite (nf_rlacksD D l C), H. cbn iota. apply req_refl.
Qed.

Lemma row_step_reqD_abs : forall s0 sp sb s2 R1 R2 l P T R1' P' T' R2' D1 n2 D3 n4 p,
  Good D1 n2 sb D1 n2 -> Good D1 n2 s2 D3 n4 ->
  req R1 (row_Maybe l P T R1') ->
  req (apR s0 R2) (row_Maybe l P' T' R2') ->
  apT sp (apT s0 P) = typ_Var p -> sT sb p = typ_Bool ->
  teqD D1 (apT sp (apT s0 P)) (apT sp P') ->
  rlacksD D1 l (apR sp (apR s0 R1')) = true -> rlacksD D1 l (apR sp R2') = true ->
  reqD D3 (apR s2 (apR sb (apR sp (apR s0 R1')))) (apR s2 (apR sb (apR sp R2'))) ->
  reqD D3 (apR (scomp s2 (scomp sb (scomp sp s0))) R1) (apR (scomp s2 (scomp sb (scomp sp s0))) R2).
Proof.
  intros s0 sp sb s2 R1 R2 l P T R1' P' T' R2' D1 n2 D3 n4 p Gb G2 H1 H2 Hp Hb Htp Hl1 Hl2 Hr.
  rewrite <- !apR_comp.
  eapply reqD_trans.
  { apply req_reqD. exact (req_apR s2 _ _ (req_apR sb _ _ (req_apR sp _ _ (req_apR s0 _ _ H1)))). }
  eapply reqD_trans; [ | apply reqD_sym; apply req_reqD;
    exact (req_apR s2 _ _ (req_apR sb _ _ (req_apR sp _ _ H2))) ].
  rewrite !apR_Maybe.
  assert (E1 : apT s2 (apT sb (apT sp (apT s0 P))) = typ_Bool).
  { rewrite Hp. change (apT sb (typ_Var p)) with (sT sb p). rewrite Hb. reflexivity. }
  assert (E2 : apT s2 (apT sb (apT sp P')) = typ_Bool).
  { rewrite Hp in Htp.
    pose proof (lift_teqD _ _ _ _ _ _ _ G2 (lift_teqD _ _ _ _ _ _ _ Gb Htp)) as Hq.
    change (apT sb (typ_Var p)) with (sT sb p) in Hq. rewrite Hb in Hq.
    change (apT s2 typ_Bool) with typ_Bool in Hq.
    exact (teqD_Bool_inv _ _ Hq). }
  rewrite E1, E2.
  assert (Hk1 : rlacksD D3 l (apR s2 (apR sb (apR sp (apR s0 R1')))) = true).
  { exact (rlacksD_ap D1 D3 (sT s2) (sR s2) l _ (Good_rkres _ _ _ _ _ G2)
             (rlacksD_ap D1 D1 (sT sb) (sR sb) l _ (Good_rkres _ _ _ _ _ Gb) Hl1)). }
  assert (Hk2 : rlacksD D3 l (apR s2 (apR sb (apR sp R2'))) = true).
  { exact (rlacksD_ap D1 D3 (sT s2) (sR s2) l _ (Good_rkres _ _ _ _ _ G2)
             (rlacksD_ap D1 D1 (sT sb) (sR sb) l _ (Good_rkres _ _ _ _ _ Gb) Hl2)). }
  eapply reqD_trans; [ exact (reqD_drop_abs _ _ _ _ Hk1) | ].
  eapply reqD_trans; [ exact Hr | ].
  apply reqD_sym. exact (reqD_drop_abs _ _ _ _ Hk2).
Qed.

Lemma unify_tD_sound : forall f,
  (forall D T1 T2 n s D' n', unify_tD f D T1 T2 n = Some (s, D', n') -> DOk D n ->
     EvT T1 -> EvT T2 ->
     OkS s /\ teqD D' (apT s T1) (apT s T2) /\ GoodU D n s D' n') /\
  (forall D R1 R2 n s D' n', unify_rD f D R1 R2 n = Some (s, D', n') -> DOk D n ->
     EvR R1 -> EvR R2 ->
     OkS s /\ reqD D' (apR s R1) (apR s R2) /\ GoodU D n s D' n').
Proof.
  induction f as [|f IH]; [ split; intros; discriminate | ].
  destruct IH as [IHt IHr].
  split.
  - intros D T1 T2 n s D' n' H HD H1 H2. cbn [unify_tD] in H.
    destruct T1 as [| | | | | A B | R | a | i | B1 | w1 A1]; destruct T2 as [| | | | | A' B' | R' | b | i' | B1' | w1' A1'];
      try discriminate H.
    all: try (destruct (bind_prop_sound _ _ _ _ _ _ _ H H1 H2) as (Hs & Ht & Hg);
              exact (conj Hs (conj (teq_teqD _ _ _ Ht) Hg))).
    all: try (destruct (bind_prop_sound _ _ _ _ _ _ _ H H2 H1) as (Hs & Ht & Hg);
              exact (conj Hs (conj (teq_teqD _ _ _ (teq_sym _ _ Ht)) Hg))).
    1-5: inversion H; subst; split; [apply OkS_id | split; [apply teqD_refl | exact (GoodU_id _ _) ]].
    + (* Arrow, Arrow *)
      destruct (unify_tD f D A A' n) as [[[s1 D1] n1]|] eqn:E1; [|discriminate].
      destruct (unify_tD f D1 (apT s1 B) (apT s1 B') n1) as [[[s2 D2] n2]|] eqn:E2; [|discriminate].
      inversion H; subst; clear H.
      destruct (EvT_arrow_inv _ _ H1) as [EA EB].
      destruct (EvT_arrow_inv _ _ H2) as [EA' EB'].
      destruct (IHt _ _ _ _ _ _ _ E1 HD EA EA') as (Hs1 & Ht1 & Hg1).
      pose proof (GoodU_Good _ _ _ _ _ HD Hg1) as G1.
      destruct (IHt _ _ _ _ _ _ _ E2 (Good_DOk _ _ _ _ _ G1) (EvT_ap s1 B Hs1 EB) (EvT_ap s1 B' Hs1 EB'))
        as (Hs2 & Ht2 & Hg2).
      pose proof (GoodU_Good _ _ _ _ _ (Good_DOk _ _ _ _ _ G1) Hg2) as G2.
      split; [ apply OkS_comp; auto | ].
      split.
      { change (apT (scomp s2 s1) (typ_Arrow A B))
          with (typ_Arrow (apT (scomp s2 s1) A) (apT (scomp s2 s1) B)).
        change (apT (scomp s2 s1) (typ_Arrow A' B'))
          with (typ_Arrow (apT (scomp s2 s1) A') (apT (scomp s2 s1) B')).
        rewrite <- !apT_comp. apply teqD_Arrow.
        - exact (lift_teqD _ _ _ _ _ _ _ G2 Ht1).
        - exact Ht2. }
      exact (GoodU_comp _ _ _ _ _ _ _ _ Hg1 Hg2).
    + (* Record, Record *)
      destruct (IHr _ _ _ _ _ _ _ H HD (EvR_nfR _ _ H1) (EvR_nfR _ _ H2)) as (Hs & Hr & Hg).
      split; [exact Hs | split; [ | exact Hg ]].
      apply teqD_Record.
      exact (req_via_nfD _ _ _ _ _ (Good_rkres _ _ _ _ _ (GoodU_Good _ _ _ _ _ HD Hg)) Hr).
    + (* Var, Var *)
      destruct (Atom.eq_dec a b) as [->|Hne].
      * inversion H; subst. split; [apply OkS_id | split; [apply teqD_refl | exact (GoodU_id _ _) ]].
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
           split; [exact Hs|]. split; [exact (teq_teqD _ _ _ Ht)|].
           apply GoodU_same; [ exact Hs | apply KR_sbT; simpl; apply finer_b_sound; exact Ef | lia ].
        -- destruct (finer_b (D a) (D b)) eqn:Ef2.
           ++ inversion H; subst; clear H.
              destruct (sound_bindT b (typ_Var a) (ev_var_T b H2) H1 Eob) as [Hs Ht].
              split; [exact Hs|]. split; [apply teqD_sym; exact (teq_teqD _ _ _ Ht)|].
              apply GoodU_same; [ exact Hs | apply KR_sbT; simpl; apply finer_b_sound; exact Ef2 | lia ].
           ++ inversion H; subst; clear H.
              destruct (sound_meet D' a b H1 H2 Hne) as [Hs [Ht Hk]].
              split; [exact Hs|]. split; [exact (teq_teqD _ _ _ Ht)|].
              apply GoodU_same; [ exact Hs | exact Hk | lia ].
    + (* Grp, Grp *)
      destruct (gdecl_eq_dec w1 w1') as [->|]; [|discriminate].
      destruct ((proj1 (unify_sound f)) _ _ _ _ _ _ _ H H1 H2) as (Hs & Ht & Hg).
      split; [exact Hs | split; [ apply teqD_Grp; exact Ht | exact Hg ]].
  - intros D R1 R2 n s D' n' H HD H1 H2. cbn [unify_rD] in H.
    assert (Hgen : forall R1 R2, EvR R1 -> EvR R2 -> forall s D' n',
      (match row_head R1 with
       | None => None
       | Some (l, P, T, R1') =>
           match rewrite_row l (side_av R1) D R2 n with
           | None => None
           | Some (P', T', R2', s0, D0, n1) =>
               match unify_tD f D0 (apT s0 P) P' n1 with
               | None => None
               | Some (sp, D1, n2) =>
                   match unify_tD f D1 (apT sp (apT s0 T)) (apT sp T') n2 with
                   | None =>
                       match absent_clash D1 l (apT sp (apT s0 P)) (apT sp (apT s0 T)) (apT sp T')
                               (apR sp (apR s0 R1')) (apR sp R2') with
                       | None => None
                       | Some p =>
                           match unify_rD f D1 (nfR D1 (apR (bool_sub (p :: nil)) (apR sp (apR s0 R1'))))
                                   (nfR D1 (apR (bool_sub (p :: nil)) (apR sp R2'))) n2 with
                           | None => None
                           | Some (s2, D3, n4) =>
                               Some (scomp s2 (scomp (bool_sub (p :: nil)) (scomp sp s0)), D3, n4)
                           end
                       end
                   | Some (s1, D2, n3) =>
                       match unify_rD f D2 (nfR D2 (apR s1 (apR sp (apR s0 R1')))) (nfR D2 (apR s1 (apR sp R2'))) n3 with
                       | None => None
                       | Some (s2, D3, n4) => Some (scomp s2 (scomp s1 (scomp sp s0)), D3, n4)
                       end
                   end
               end
           end
       end) = Some (s, D', n') ->
      OkS s /\ reqD D' (apR s R1) (apR s R2) /\ GoodU D n s D' n').
    { intros R1' R2' Hg1 Hg2 s' D'' n'' Hg.
      destruct (row_head R1') as [[[[l P] T] R1'']|] eqn:Eh; [|discriminate].
      destruct (rewrite_row l (side_av R1') D R2' n) as [[[[[[P' T'] R2''] s0] D0] n1]|] eqn:Erw; [|discriminate].
      destruct (unify_tD f D0 (apT s0 P) P' n1) as [[[sp D1] n2]|] eqn:Eu0; [|discriminate].
      destruct (unify_tD f D1 (apT sp (apT s0 T)) (apT sp T') n2) as [[[s1 D2] n3]|] eqn:Eu1.
      2: { destruct (absent_clash D1 l (apT sp (apT s0 P)) (apT sp (apT s0 T)) (apT sp T')
                       (apR sp (apR s0 R1'')) (apR sp R2'')) as [p|] eqn:Eac; [ | discriminate Hg ].
           destruct (unify_rD f D1 (nfR D1 (apR (bool_sub (p :: nil)) (apR sp (apR s0 R1''))))
                       (nfR D1 (apR (bool_sub (p :: nil)) (apR sp R2''))) n2)
             as [[[s2 D3] n4]|] eqn:Eu2; [ | discriminate Hg ].
           inversion Hg; subst; clear Hg.
           destruct (absent_clash_inv _ _ _ _ _ _ _ _ Eac) as (EP & Hsat & Hl1 & Hl2).
           destruct (row_head_sound _ _ _ _ _ Eh Hg1) as (HP & HT & HR1' & Hhd).
           destruct (rewrite_row_sound _ _ _ _ _ _ _ _ _ _ _ Erw Hg2) as (Hs0 & HP' & HT' & HR2' & Hrw & Hg0).
           pose proof (GoodU_Good _ _ _ _ _ HD Hg0) as G0.
           destruct (IHt _ _ _ _ _ _ _ Eu0 (Good_DOk _ _ _ _ _ G0) (EvT_ap s0 P Hs0 HP) HP') as (Hsp & Htp & Hgp).
           pose proof (GoodU_Good _ _ _ _ _ (Good_DOk _ _ _ _ _ G0) Hgp) as Gp.
           assert (Hevp : ev p).
           { apply ev_var_T. rewrite <- EP. exact (EvT_ap sp _ Hsp (EvT_ap s0 P Hs0 HP)). }
           assert (Hf : forallb (fun q => sat_b D1 (D1 q) typ_Bool) (p :: nil) = true)
             by (cbn [forallb]; rewrite Hsat; reflexivity).
           destruct (bool_sub_ok D1 (p :: nil) (fun q Hq => ltac:(destruct Hq as [<-|[]]; exact Hevp)) Hf)
             as (Hsb & Hkb & Hrb).
           pose proof (Good_unify D1 n2 (bool_sub (p :: nil)) n2 Hsb Hkb (le_n n2) (Good_DOk _ _ _ _ _ Gp)) as Gb.
           assert (Hgb : GoodU D1 n2 (bool_sub (p :: nil)) D1 n2)
             by exact (GoodU_same D1 n2 _ n2 Hsb Hkb (le_n n2)).
           assert (HR1x : EvR (apR sp (apR s0 R1''))) by exact (EvR_ap sp _ Hsp (EvR_ap s0 R1'' Hs0 HR1')).
           assert (HR2x : EvR (apR sp R2'')) by exact (EvR_ap sp _ Hsp HR2').
           destruct (IHr _ _ _ _ _ _ _ Eu2 (Good_DOk _ _ _ _ _ Gp)
                       (EvR_nfR _ _ (EvR_ap _ _ Hsb HR1x)) (EvR_nfR _ _ (EvR_ap _ _ Hsb HR2x)))
             as (Hs2 & Hr2' & Hg2').
           pose proof (GoodU_Good _ _ _ _ _ (Good_DOk _ _ _ _ _ Gp) Hg2') as G2.
           pose proof (req_via_nfD _ _ _ _ _ (Good_rkres _ _ _ _ _ G2) Hr2') as Hr2.
           split; [ apply OkS_comp; [ exact Hs2 | apply OkS_comp; [ exact Hsb | apply OkS_comp; auto ] ] | ].
           split; [ | exact (GoodU_comp _ _ _ _ _ _ _ _
                       (GoodU_comp _ _ _ _ _ _ _ _ (GoodU_comp _ _ _ _ _ _ _ _ Hg0 Hgp) Hgb) Hg2') ].
           exact (row_step_reqD_abs s0 sp (bool_sub (p :: nil)) s2 R1' R2' _ _ _ _ _ _ _ _ _ _ _ _ Gb G2
                    Hhd Hrw EP (bool_sub_one p) Htp Hl1 Hl2 Hr2). }
      destruct (unify_rD f D2 (nfR D2 (apR s1 (apR sp (apR s0 R1'')))) (nfR D2 (apR s1 (apR sp R2''))) n3)
        as [[[s2 D3] n4]|] eqn:Eu2; [|discriminate].
      inversion Hg; subst; clear Hg.
      destruct (row_head_sound _ _ _ _ _ Eh Hg1) as (HP & HT & HR1' & Hhd).
      destruct (rewrite_row_sound _ _ _ _ _ _ _ _ _ _ _ Erw Hg2) as (Hs0 & HP' & HT' & HR2' & Hrw & Hg0).
      pose proof (GoodU_Good _ _ _ _ _ HD Hg0) as G0.
      destruct (IHt _ _ _ _ _ _ _ Eu0 (Good_DOk _ _ _ _ _ G0) (EvT_ap s0 P Hs0 HP) HP') as (Hsp & Htp & Hgp).
      pose proof (GoodU_Good _ _ _ _ _ (Good_DOk _ _ _ _ _ G0) Hgp) as Gp.
      destruct (IHt _ _ _ _ _ _ _ Eu1 (Good_DOk _ _ _ _ _ Gp)
                  (EvT_ap sp _ Hsp (EvT_ap s0 T Hs0 HT)) (EvT_ap sp T' Hsp HT'))
        as (Hs1 & Ht1 & Hg1').
      pose proof (GoodU_Good _ _ _ _ _ (Good_DOk _ _ _ _ _ Gp) Hg1') as G1.
      destruct (IHr _ _ _ _ _ _ _ Eu2 (Good_DOk _ _ _ _ _ G1)
                  (EvR_nfR _ _ (EvR_ap s1 _ Hs1 (EvR_ap sp _ Hsp (EvR_ap s0 R1'' Hs0 HR1'))))
                  (EvR_nfR _ _ (EvR_ap s1 _ Hs1 (EvR_ap sp _ Hsp HR2')))) as (Hs2 & Hr2' & Hg2').
      pose proof (GoodU_Good _ _ _ _ _ (Good_DOk _ _ _ _ _ G1) Hg2') as G2.
      pose proof (req_via_nfD _ _ _ _ _ (Good_rkres _ _ _ _ _ G2) Hr2') as Hr2.
      split; [ apply OkS_comp; [ exact Hs2 | apply OkS_comp; [ exact Hs1 | apply OkS_comp; auto ] ] | ].
      split; [ | exact (GoodU_comp _ _ _ _ _ _ _ _
               (GoodU_comp _ _ _ _ _ _ _ _
                  (GoodU_comp _ _ _ _ _ _ _ _ Hg0 Hgp) Hg1') Hg2') ].
      exact (row_step_reqD s0 sp s1 s2 R1' R2' _ _ _ _ _ _ _ _ _ _ _ _ _ G1 G2 Hhd Hrw Htp Ht1 Hr2). }
    destruct R1 as [| r | l T R1' | lm Pm Tm Rm]; destruct R2 as [| q | l2 T2 R2' | lm2 Pm2 Tm2 Rm2];
      try (destruct (bind_row_sound _ _ _ _ _ _ _ H H1 H2) as (Hs & Hr & Hg);
           exact (conj Hs (conj (req_reqD _ _ _ Hr) Hg)));
      try (destruct (bind_row_sound _ _ _ _ _ _ _ H H2 H1) as (Hs & Hr & Hg);
           exact (conj Hs (conj (req_reqD _ _ _ (req_sym _ _ Hr)) Hg)));
      try (exact (Hgen _ _ H1 H2 _ _ _ H)).
    + inversion H; subst. split; [apply OkS_id | split; [apply reqD_refl | exact (GoodU_id _ _) ]].
    + (* Empty, Maybe: the same equation read the other way *)
      destruct (IHr _ _ _ _ _ _ _ H HD H2 H1) as (Hs & Hr & Hg).
      split; [ exact Hs | split; [ apply reqD_sym; exact Hr | exact Hg ]].
    + (* Var, Var *)
      destruct (Atom.eq_dec r q) as [->|Hne].
      * inversion H; subst. split; [apply OkS_id | split; [apply reqD_refl | exact (GoodU_id _ _) ]].
      * destruct (bind_row_sound _ _ _ _ _ _ _ H H1 H2) as (Hs & Hr & Hg).
        exact (conj Hs (conj (req_reqD _ _ _ Hr) Hg)).
Qed.
