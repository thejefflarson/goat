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

Lemma KR_sbT : forall D a T, sat D (D a) T -> KR D D (sbT a T).
Proof.
  intros D a T H. split; [ exact (kres_sbT D a T H) | intros r; exact (rkok_self D r) ].
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
    + destruct (push_sort (upd D (ea n) k) k l (S n)) as [[s1 D1] n1] eqn:E.
      inversion H; subst; clear H.
      destruct (IH _ _ _ _ _ _ E (fun c Hc => Hev c (or_intror Hc))) as (Hs1 & [Hl1 Hg1] & Hfx & Hfr).
      assert (Hb : ev b) by (apply Hev; left; reflexivity).
      assert (Hs0 : OkS (sbT b (typ_Var (ea n)))) by (apply OkS_sbT; [ exact Hb | apply EvT_var, ev_ea | exact I ]).
      refine (conj (OkS_comp _ _ Hs1 Hs0) (conj _ (conj _ _))).
      * split; [ lia | intros Hd ].
        pose proof (Good_rename D n b k Hd Hb (finer_b_total _ _ Ef)) as G0.
        exact (Good_comp _ _ _ _ _ _ _ _ G0 (Hg1 (proj1 (proj2 (proj2 G0))))).
      * intros x Hx. unfold scomp, tcomp. simpl. unfold sbT. simpl.
        destruct (Atom.eq_dec x b) as [->|Hne]; [ exfalso; apply Hx; left; reflexivity | ].
        apply Hfx. intros Hin. apply Hx. right. exact Hin.
      * intros r. unfold scomp, rcomp. simpl. unfold sbT. simpl. unfold idr. simpl. exact (Hfr r).
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
    + destruct (push_sort_r (rupd D (ea n) (RK k (rk_lacks (drk D b)))) k l (S n)) as [[s1 D1] n1] eqn:E.
      inversion H; subst; clear H.
      destruct (IH _ _ _ _ _ _ E (fun c Hc => Hev c (or_intror Hc))) as (Hs1 & [Hl1 Hg1] & Hft).
      assert (Hb : ev b) by (apply Hev; left; reflexivity).
      assert (Hs0 : OkS (sbR b (row_Var (ea n)))) by (apply OkS_sbR; [ exact Hb | apply EvR_var, ev_ea | exact I ]).
      refine (conj (OkS_comp _ _ Hs1 Hs0) (conj _ _)).
      * split; [ lia | intros Hd ].
        pose proof (Good_rename_r D n b (RK k (rk_lacks (drk D b))) Hd Hb
                      (finer_b_total _ _ Ef) (fun l Hl => Hl)) as G0.
        exact (Good_comp _ _ _ _ _ _ _ _ G0 (Hg1 (proj1 (proj2 (proj2 G0))))).
      * intros x. unfold scomp, tcomp. simpl. unfold sbR. simpl. unfold idt. simpl. exact (Hft x).
Qed.

Lemma push_sort_r_fix : forall l D k n s D' n',
  push_sort_r D k l n = (s, D', n') -> forall x, ~ In x l -> sR s x = row_Var x.
Proof.
  induction l as [|b l IH]; intros D k n s D' n' H x Hx; cbn [push_sort_r] in H.
  - inversion H; subst; clear H. reflexivity.
  - destruct (finer_b (rk_sort (drk D b)) k).
    + apply (IH _ _ _ _ _ _ H). intros Hin. apply Hx. right. exact Hin.
    + destruct (push_sort_r (rupd D (ea n) (RK k (rk_lacks (drk D b)))) k l (S n)) as [[s1 D1] n1] eqn:E.
      inversion H; subst; clear H.
      assert (Hxb : x <> b) by (intros ->; apply Hx; left; reflexivity).
      assert (Hxl : ~ In x l) by (intros Hin; apply Hx; right; exact Hin).
      pose proof (IH _ _ _ _ _ _ E x Hxl) as Hs1.
      unfold scomp, rcomp. simpl. unfold sbR. simpl.
      destruct (Atom.eq_dec x b) as [->|_]; [ exfalso; apply Hxb; reflexivity | ].
      exact Hs1.
Qed.

Lemma bind_prop_sound : forall D a T n s D' n',
  bind_prop D a T n = Some (s, D', n') -> EvT (typ_Var a) -> EvT T ->
  OkS s /\ teq (apT s (typ_Var a)) (apT s T) /\ GoodU D n s D' n'.
Proof.
  intros D a T n s D' n' H Ha HT. unfold bind_prop in H.
  destruct (occT a T) eqn:Eo; [ discriminate | ].
  destruct (push_sort D (D a) (AtomSetImpl.elements (ftv_typ T)) n) as [[sp D1] n1] eqn:Ep.
  destruct (push_sort_r D1 (D1 a) (AtomSetImpl.elements (frv_typ T)) n1) as [[sr D2] n2] eqn:Epr.
  cbn zeta in H. destruct (occT a (apT sr (apT sp T))) eqn:Eo'; [ discriminate | ].
  destruct (sat_b D2 (D2 a) (apT sr (apT sp T))) eqn:Es; [ | discriminate ].
  inversion H; subst; clear H.
  destruct (occT_false _ _ Eo) as [Hnot _].
  assert (Hev : forall b, In b (AtomSetImpl.elements (ftv_typ T)) -> ev b).
  { intros b Hb. apply (proj1 HT). apply AtomSetFacts.elements_iff. apply SetoidList.In_InA; [ exact eq_equivalence | exact Hb ]. }
  assert (Hevr : forall b, In b (AtomSetImpl.elements (frv_typ T)) -> ev b).
  { intros b Hb. apply (proj2 HT). apply AtomSetFacts.elements_iff. apply SetoidList.In_InA; [ exact eq_equivalence | exact Hb ]. }
  destruct (push_sort_good _ _ _ _ _ _ _ Ep Hev) as (Hsp & Hgu & Hfx & _).
  destruct (push_sort_r_good _ _ _ _ _ _ _ Epr Hevr) as (Hsr & Hgr & Hft).
  assert (Hna : ~ In a (AtomSetImpl.elements (ftv_typ T))).
  { intros Hin. apply Hnot. apply AtomSetFacts.elements_iff.
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
    + destruct (push_sort (upd D (ea n) k) k l (S n)) as [[s1 D1] n1] eqn:E.
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

Lemma bind_row_sound : forall D r R n s D' n',
  bind_row D r R n = Some (s, D', n') -> EvR (row_Var r) -> EvR R ->
  OkS s /\ req (apR s (row_Var r)) (apR s R) /\ GoodU D n s D' n'.
Proof.
  intros D r R n s D' n' H Hr HR. unfold bind_row in H. cbn zeta in H.
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
        -- inversion H; subst; clear H.
           destruct (sound_bindT b (typ_Var a) (ev_var_T b H2) H1 Eob) as [Hs Ht].
           split; [exact Hs|]. split; [apply teq_sym; exact Ht|].
           apply GoodU_same; [ exact Hs | apply KR_sbT; simpl; apply finer_b_total; exact Ef | lia ].
    + (* Grp, Grp *)
      destruct (gdecl_eq_dec w1 w1') as [->|]; [|discriminate].
      destruct (IHt _ _ _ _ _ _ _ H H1 H2) as (Hs & Ht & Hg).
      split; [exact Hs | split; [ apply teq_grp; exact Ht | exact Hg ]].
  - intros D R1 R2 n s D' n' H H1 H2. cbn [unify_r] in H.
    assert (Hgen : forall R1 R2, EvR R1 -> EvR R2 -> forall s D' n',
      (match row_head R1 with
       | None => None
       | Some (l, P, T, R1') =>
           match rewrite_row l (frv_row R1) D R2 n with
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
      destruct (rewrite_row l (frv_row R1') D R2' n) as [[[[[[P' T'] R2''] s0] D0] n1]|] eqn:Erw; [|discriminate].
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
