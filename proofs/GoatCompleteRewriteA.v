(* Completeness of algorithm W, stage 7.8m (partial): [rewrite_row] when the
   front entry is absent (docs/design/phase7-proof-plan.md).

   [rewrite_row_spec] (GoatCompleteRewrite.v) walks the second row for an entry
   [Sg] presents with a presence that is no [Bool].  When the first row's front
   entry is absent under [Sg], the second row presents its label absent too, and
   the walk meets three things the present case never does:

   - the closed end: [rewrite_row] returns the entry [l ^ Bool : a ; {}] with a
     fresh field variable [a].  The row [Sg] gives the label no entry, and
     [req_abs] reads the absent entry away, so [a] may be sent to any field
     (the front's field image);
   - a row variable: the same fresh field variable stands for a field the sort of
     the variable does not constrain ([rsat] says nothing of an absent entry), so
     the sort hypothesis [HF] is a real condition: the front's field has the sort
     of every row variable that does not lack the label ([fld]'s first half);
   - an entry for another label before the front label: the walk passes it, and
     the label's presentation in the rest keeps its (absent) presence and may be
     given the same field ([req_absf]), so the walk is stated for one field [T0].

   Two presentations of one label cancel to equal rests whatever their presences
   ([row_cancel]), so [rewrite_row_frontA] reads the rewritten entry off exactly
   as the present case does: presence and field agree, or both are absent.

   Axiom- and admit-free. *)

Require Import Metalib.Metatheory.
Require Import Goat.Goat_ott.
Require Import Goat.GoatRows.
Require Import Goat.GoatRowNf.
Require Import Goat.GoatDefs.
Require Import Goat.GoatSubst.
Require Import Goat.GoatInfer.
Require Import Goat.GoatInferSub.
Require Import Goat.GoatInferSort.
Require Import Goat.GoatInferUnify.
Require Import Goat.GoatSatTeq.
Require Import Goat.GoatCompleteEr.
Require Import Goat.GoatCompleteSorts.
Require Import Goat.GoatCompleteBind.
Require Import Goat.GoatCompleteSide.
Require Import Goat.GoatCompleteRewrite.
Require Import Stdlib.Lists.List.
Import ListNotations.
From Stdlib Require Import Lia.

(* The row can present [l] absent with the field [T0]. *)
Definition SurfA (l : label) (T0 : typ) (Q : row) : Prop :=
  exists R0, req Q (row_Maybe l typ_Bool T0 R0).

(* Two presentations of one label by one row: if one is absent, the other is. *)
Lemma abs_of_cancel : forall l P2 T2 R2 T0 R0 Q,
  req Q (row_Maybe l P2 T2 R2) -> req Q (row_Maybe l typ_Bool T0 R0) -> is_abs P2 = true.
Proof.
  intros l P2 T2 R2 T0 R0 Q H2 H0.
  pose proof (row_cancel _ _ _ _ _ _ _ (req_trans _ _ _ (req_sym _ _ H2) H0)) as [_ Hc].
  destruct Hc as [[Hp _] | [Hp _]]; [ rewrite (teq_is_abs _ _ Hp); reflexivity | exact Hp ].
Qed.

Lemma SurfA_ext : forall l T0 l' X Q, l' <> l -> SurfA l T0 (row_Ext l' X Q) -> SurfA l T0 Q.
Proof.
  intros l T0 l' X Q Hne (R0 & Hq).
  assert (Hs : Surf l Q) by (eapply Surf_ext; [ exact Hne | exists typ_Bool, T0, R0; exact Hq ]).
  destruct Hs as (P2 & T2 & R2 & Hq2).
  assert (H1 : req (row_Ext l' X Q) (row_Maybe l P2 T2 (row_Ext l' X R2))).
  { eapply req_trans; [ apply req_head; [ apply teq_refl | exact Hq2 ] | ].
    apply req_sym. apply req_swap_em. congruence. }
  pose proof (abs_of_cancel _ _ _ _ _ _ _ H1 Hq) as Ha. rewrite (is_abs_Bool _ Ha) in Hq2.
  exists R2. eapply req_trans; [ exact Hq2 | apply req_absf ].
Qed.

Lemma SurfA_maybe : forall l T0 l' P' X Q, l' <> l -> SurfA l T0 (row_Maybe l' P' X Q) -> SurfA l T0 Q.
Proof.
  intros l T0 l' P' X Q Hne (R0 & Hq).
  assert (Hs : Surf l Q) by (eapply Surf_maybe; [ exact Hne | exists typ_Bool, T0, R0; exact Hq ]).
  destruct Hs as (P2 & T2 & R2 & Hq2).
  assert (H1 : req (row_Maybe l' P' X Q) (row_Maybe l P2 T2 (row_Maybe l' P' X R2))).
  { eapply req_trans; [ apply req_maybe; [ apply teq_refl | apply teq_refl | exact Hq2 ] | ].
    apply req_sym. apply req_swap_mm. congruence. }
  pose proof (abs_of_cancel _ _ _ _ _ _ _ H1 Hq) as Ha. rewrite (is_abs_Bool _ Ha) in Hq2.
  exists R2. eapply req_trans; [ exact Hq2 | apply req_absf ].
Qed.

(* A row variable with an absent presentation of the label is bound to an entry whose
   field is [T0], the front's field. *)
Lemma rewrite_row_var_absent : forall l av D n r D1 Sg T0 R0,
  DOk D n -> KR D D1 Sg -> AtomSetImpl.mem r av = false ->
  req (sR Sg r) (row_Maybe l typ_Bool T0 R0) ->
  (rk_lacks (drk D r) l = false -> sat D1 (rk_sort (drk D r)) T0) ->
  (forall E F, Bnd E F Sg -> (forall x, x `in` ftv_typ T0 -> E x) /\ (forall q, q `in` frv_typ T0 -> F q)) ->
  exists P' T' R' s0 D0 n1 S2,
    rewrite_row l av D (row_Var r) n = Some (P', T', R', s0, D0, n1) /\
    KR D0 D1 S2 /\ n <= n1 /\
    req (row_Maybe l (apT S2 P') (apT S2 T') (apR S2 R')) (row_Maybe l typ_Bool T0 R0) /\
    (forall x, (forall m, n <= m -> x <> ea m) -> sT Sg x = apT S2 (sT s0 x)) /\
    (forall q, (forall m, n <= m -> q <> ea m) -> req (sR Sg q) (apR S2 (sR s0 q))) /\
    Cov Sg S2.
Proof.
  intros l av D n r D1 Sg T0 R0 Hd HK Hav Hreq Hfield HT0.
  pose proof (proj2 er_teq R0) as HR.
  assert (Hq : req (row_Maybe l typ_Bool T0 (erR R0)) (row_Maybe l typ_Bool T0 R0))
    by (apply req_maybe; [ apply teq_refl | apply teq_refl | exact HR ]).
  destruct (rewrite_row_var_complete l av D n r D1 Sg typ_Bool T0 (erR R0) Hd HK Hav
              (req_trans _ _ _ Hreq (req_sym _ _ Hq)) (fun H _ => Hfield H))
    as (P' & T' & R' & s0 & D0 & n1 & S2 & E & K & Hn & HP' & HT' & HR' & F1 & F2 & Hb).
  exists P', T', R', s0, D0, n1, S2.
  refine (conj E (conj K (conj Hn (conj _ (conj F1 (conj F2 _)))))).
  - rewrite HP', HT', HR'. exact Hq.
  - intros E0 F0 HB. refine (Hb E0 F0 HB _). destruct HB as (B1 & B2 & B3 & B4).
    pose proof (proj2 er_inv _ _ Hreq) as [Hf Hr]. cbn [erR is_abs] in Hf, Hr.
    cbn [ftv_row frv_row ftv_typ frv_typ] in Hf, Hr.
    pose proof (proj2 er_sub (sR Sg r)) as [Hs1 Hs2].
    pose proof (HT0 E0 F0 (conj B1 (conj B2 (conj B3 B4)))) as [HE HF].
    refine (conj _ (conj _ (conj _ (conj _ (conj _ _))))).
    + intros x Hx. simpl in Hx. fsetdec.
    + exact HE.
    + intros x Hx. apply (B3 r x). apply Hs1. apply (proj2 (Hf x)). fsetdec.
    + intros x Hx. simpl in Hx. fsetdec.
    + exact HF.
    + intros x Hx. apply (B4 r x). apply Hs2. apply (proj2 (Hr x)). fsetdec.
Qed.

(* The walk for an entry of [l] when [Sg] presents the label absent with the field
   [T0]: the closed end gives the entry its field [T0]. *)
Theorem rewrite_row_specA : forall l av R D n D1 Sg T0,
  DOk D n -> KR D D1 Sg ->
  (forall x, x `in` ftv_row R -> old n x) -> (forall q, q `in` frv_row R -> old n q) ->
  SurfA l T0 (apR Sg R) ->
  (forall r, r `in` frv_row R -> rk_lacks (drk D r) l = false -> sat D1 (rk_sort (drk D r)) T0) ->
  (forall E F, Bnd E F Sg -> (forall x, x `in` ftv_typ T0 -> E x) /\ (forall q, q `in` frv_typ T0 -> F q)) ->
  forall P' T' R' s0 D0 n1, rewrite_row l av D R n = Some (P', T', R', s0, D0, n1) ->
  exists S2, KR D0 D1 S2 /\ n <= n1 /\ DOk D0 n1 /\
    (forall x, old n x -> teq (sT Sg x) (apT S2 (sT s0 x))) /\
    (forall q, old n q -> req (sR Sg q) (apR S2 (sR s0 q))) /\
    req (apR Sg R) (row_Maybe l (apT S2 P') (apT S2 T') (apR S2 R')) /\ Cov Sg S2.
Proof.
  intros l av R. induction R as [ | r | l' T' R IHR | l' P1 T' R IHR ];
    intros D n D1 Sg T0 Hd HK Hx Hq Hsurf HF HT0 P' T1 R' s0 D0 n1 E.
  - (* the closed end: the label gets an absent entry with a fresh field *)
    cbn [rewrite_row] in E. inversion E; subst P' T1 R' s0 D0 n1. clear E.
    set (S2 := supd Sg (ea n) T0).
    assert (Hea : D (ea n) = k_Any) by exact (DOk_ea D n n Hd (le_n n)).
    exists S2. fin5.
    + split.
      * intros a. cbn [sT S2 supd]. destruct (Atom.eq_dec a (ea n)) as [->|Hne].
        -- rewrite Hea. apply sat_any.
        -- exact (proj1 HK a).
      * intros q. cbn [sR S2 supd]. exact (proj2 HK q).
    + lia.
    + eapply DOk_mono; [ exact Hd | lia ].
    + intros x Hxo. cbn [sT sid idt apT ap_typ S2 supd].
      destruct (Atom.eq_dec x (ea n)) as [->|Hne]; [ exfalso; exact (Hxo n (le_n n) eq_refl) | apply teq_refl ].
    + intros q _. cbn [sR sid idr apR ap_row S2 supd]. apply req_refl.
    + cbn [apR ap_row apT ap_typ sT S2 supd]. rewrite dec_same.
      apply req_sym. apply req_abs. reflexivity.
    + intros E0 F0 HB. destruct (HT0 E0 F0 HB) as [HE HFr].
      exact (Bnd_supd E0 F0 Sg (ea n) T0 HB HE HFr).
  - (* the row variable *)
    assert (Hm : AtomSetImpl.mem r av = false).
    { cbn [rewrite_row] in E. destruct (AtomSetImpl.mem r av); [ discriminate | reflexivity ]. }
    destruct Hsurf as (R0 & Hreq). cbn [apR ap_row] in Hreq.
    destruct (rewrite_row_var_absent l av D n r D1 Sg T0 R0 Hd HK Hm Hreq
                (HF r ltac:(simpl; fsetdec)) HT0)
      as (P1 & T2 & R1 & s1 & D2 & n2 & S2 & E2 & HK2 & Hn & Hinv & Hs1 & Hs2 & Hcov).
    rewrite E2 in E. inversion E; subst P1 T2 R1 s1 D2 n2. clear E.
    exists S2. fin5.
    + exact HK2.
    + exact Hn.
    + cbn [rewrite_row] in E2. rewrite Hm in E2. cbn zeta in E2.
      destruct (rk_lacks (drk D r) l); inversion E2; subst.
      * apply DOk_two. exact Hd.
      * apply DOk_three. exact Hd.
    + intros x Hxo. rewrite (Hs1 x Hxo). apply teq_refl.
    + intros q Hqo. exact (Hs2 q Hqo).
    + cbn [apR ap_row]. exact (req_trans _ _ _ Hreq (req_sym _ _ Hinv)).
    + exact Hcov.
  - (* a plain field *)
    cbn [rewrite_row] in E. destruct (Nat.eqb l l') eqn:Ell.
    + apply Nat.eqb_eq in Ell. subst l'. inversion E; subst. clear E.
      exists Sg. fin5; try assumption; try apply le_n; try apply Cov_refl.
      * intros x _. cbn [sT sid idt apT ap_typ]. apply teq_refl.
      * intros q _. cbn [sR sid idr apR ap_row]. apply req_refl.
      * cbn [apR ap_row apT ap_typ]. apply req_sym. apply req_pre.
    + apply Nat.eqb_neq in Ell.
      destruct (rewrite_row l av D R n) as [[[[[[P0 T1'] R3] s] D2] n2] | ] eqn:E1;
        [ | discriminate ].
      inversion E; subst P' T1 R' s0 D0 n1. clear E.
      cbn [apR ap_row] in Hsurf. pose proof (SurfA_ext _ _ _ _ _ (not_eq_sym Ell) Hsurf) as Hs.
      destruct (IHR D n D1 Sg T0 Hd HK
                  (fun x Hx' => Hx x ltac:(simpl; fsetdec)) (fun q Hq' => Hq q ltac:(simpl; fsetdec))
                  Hs (fun r Hr => HF r ltac:(simpl; fsetdec)) HT0 P0 T1' R3 s D2 n2 E1)
        as (S2 & HK2 & Hn & Hd2 & Hf1 & Hf2 & Hinv & HCov).
      exists S2. fin5; try assumption.
      cbn [apR ap_row]. eapply req_trans.
      { apply req_head; [ | exact Hinv ].
        apply (ap_factor Sg S2 s T'); [ intros x Hx'; apply Hf1; apply Hx; simpl; fsetdec
                                      | intros q Hq'; apply Hf2; apply Hq; simpl; fsetdec ]. }
      apply req_sym. apply req_swap_em. exact Ell.
  - (* a presence entry *)
    cbn [rewrite_row] in E. destruct (Nat.eqb l l') eqn:Ell.
    + apply Nat.eqb_eq in Ell. subst l'. inversion E; subst. clear E.
      exists Sg. fin5; try assumption; try apply le_n; try apply Cov_refl.
      * intros x _. cbn [sT sid idt apT ap_typ]. apply teq_refl.
      * intros q _. cbn [sR sid idr apR ap_row]. apply req_refl.
      * cbn [apR ap_row]. apply req_refl.
    + apply Nat.eqb_neq in Ell.
      destruct (rewrite_row l av D R n) as [[[[[[P0 T1'] R3] s] D2] n2] | ] eqn:E1;
        [ | discriminate ].
      inversion E; subst P' T1 R' s0 D0 n1. clear E.
      cbn [apR ap_row] in Hsurf. pose proof (SurfA_maybe _ _ _ _ _ _ (not_eq_sym Ell) Hsurf) as Hs.
      destruct (IHR D n D1 Sg T0 Hd HK
                  (fun x Hx' => Hx x ltac:(simpl; fsetdec)) (fun q Hq' => Hq q ltac:(simpl; fsetdec))
                  Hs (fun r Hr => HF r ltac:(simpl; fsetdec)) HT0 P0 T1' R3 s D2 n2 E1)
        as (S2 & HK2 & Hn & Hd2 & Hf1 & Hf2 & Hinv & HCov).
      exists S2. fin5; try assumption.
      cbn [apR ap_row]. eapply req_trans.
      { apply req_maybe; [ | | exact Hinv ].
        - apply (ap_factor Sg S2 s P1); [ intros x Hx'; apply Hf1; apply Hx; simpl; fsetdec
                                        | intros q Hq'; apply Hf2; apply Hq; simpl; fsetdec ].
        - apply (ap_factor Sg S2 s T'); [ intros x Hx'; apply Hf1; apply Hx; simpl; fsetdec
                                        | intros q Hq'; apply Hf2; apply Hq; simpl; fsetdec ]. }
      apply req_sym. apply req_swap_mm. exact Ell.
Qed.

(* What the unifier reads off the walk at an absent front: the entry [Sg R] has for
   the label (presence [Bool], field [T0], rest [R0]) is the rewritten front entry
   under [S2] up to the field of an absent entry, and the rests are equal. *)
Corollary rewrite_row_frontA : forall l av R D n D1 Sg T0 R0,
  DOk D n -> KR D D1 Sg ->
  (forall x, x `in` ftv_row R -> old n x) -> (forall q, q `in` frv_row R -> old n q) ->
  req (apR Sg R) (row_Maybe l typ_Bool T0 R0) ->
  (forall r, r `in` frv_row R -> rk_lacks (drk D r) l = false -> sat D1 (rk_sort (drk D r)) T0) ->
  (forall E F, Bnd E F Sg -> (forall x, x `in` ftv_typ T0 -> E x) /\ (forall q, q `in` frv_typ T0 -> F q)) ->
  forall P' T' R' s0 D0 n1, rewrite_row l av D R n = Some (P', T', R', s0, D0, n1) ->
  exists S2, KR D0 D1 S2 /\ n <= n1 /\ DOk D0 n1 /\
    (forall x, old n x -> teq (sT Sg x) (apT S2 (sT s0 x))) /\
    (forall q, old n q -> req (sR Sg q) (apR S2 (sR s0 q))) /\
    req (apR S2 R') R0 /\
    ((teq (apT S2 P') typ_Bool /\ teq (apT S2 T') T0) \/ is_abs (apT S2 P') = true) /\ Cov Sg S2.
Proof.
  intros l av R D n D1 Sg T0 R0 Hd HK Hx Hq Hreq HF HT0 P' T' R' s0 D0 n1 E.
  destruct (rewrite_row_specA l av R D n D1 Sg T0 Hd HK Hx Hq (ex_intro _ R0 Hreq) HF HT0 P' T' R' s0 D0 n1 E)
    as (S2 & HK2 & Hn & Hd2 & Hf1 & Hf2 & Hinv & HCov).
  pose proof (row_cancel _ _ _ _ _ _ _ (req_trans _ _ _ (req_sym _ _ Hinv) Hreq)) as [Hr Hc].
  exists S2. refine (conj HK2 (conj Hn (conj Hd2 (conj Hf1 (conj Hf2 (conj Hr (conj _ HCov))))))).
  destruct Hc as [[H1 H2] | [H1 H2]]; [ left; split; assumption | right; exact H1 ].
Qed.
