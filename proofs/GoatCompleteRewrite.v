(* Completeness of algorithm W, stage 7.6i: [rewrite_row] on a whole second row
   (docs/design/phase7-proof-plan.md).

   [rewrite_row l av D R n] walks the entries of [R] that are not for [l] and
   stops at the entry for [l] (found: nothing is bound), at the closed end of
   the row (the label gets presence [Bool]) or at the row variable at its tail
   (which [rewrite_row_var_complete] binds).  The invariant of the walk is that
   the substituted row equals the rewritten one with the entry for [l] in
   front: [req (apR Sg R) (l ^ S2 P' : S2 T' ; S2 R')].  The caller reads the
   presence, the field type and the rest off it with [row_cancel].

   [Surf l Q] says a row can present [l] (some presence, field and rest).  It
   holds exactly when the row has an entry for [l] or a closed tail, so it is
   inherited by the rest of a row after an entry for another label.  It is the
   one fact about [Sg] the walk needs, at the row variable.

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
Require Import Goat.GoatCompleteSorts.
Require Import Goat.GoatCompleteBind.
Require Import Goat.GoatCompleteSide.
Require Import Stdlib.Lists.List.
Import ListNotations.
From Stdlib Require Import Lia.

(* ---- substitutions that agree up to conversion on the atoms of a type ---- *)

Lemma ap_cong_on : forall S S',
  (forall T, (forall x, x `in` ftv_typ T -> teq (sT S x) (sT S' x)) ->
     (forall q, q `in` frv_typ T -> req (sR S q) (sR S' q)) ->
     teq (apT S T) (apT S' T)) /\
  (forall R, (forall x, x `in` ftv_row R -> teq (sT S x) (sT S' x)) ->
     (forall q, q `in` frv_row R -> req (sR S q) (sR S' q)) ->
     req (apR S R) (apR S' R)).
Proof.
  intros S S'. unfold apT, apR. apply typ_row_mutind; simpl; intros.
  - constructor.
  - constructor.
  - constructor.
  - constructor.
  - constructor.
  - constructor; [ apply H | apply H0 ];
      first [ intros x Hx; apply H1; fsetdec | intros q Hq; apply H2; fsetdec ].
  - constructor. apply H; assumption.
  - apply H. fsetdec.
  - constructor.
  - constructor. apply H; assumption.
  - constructor. apply H; assumption.
  - constructor.
  - apply H0. fsetdec.
  - constructor; [ apply H | apply H0 ];
      first [ intros x Hx; apply H1; fsetdec | intros q Hq; apply H2; fsetdec ].
  - constructor; [ apply H | apply H0 | apply H1 ];
      first [ intros x Hx; apply H2; fsetdec | intros q Hq; apply H3; fsetdec ].
Qed.

(* A substitution [S2] after [s] is [Sg] up to conversion on the atoms of [T]. *)
Lemma ap_factor : forall Sg S2 s T,
  (forall x, x `in` ftv_typ T -> teq (sT Sg x) (apT S2 (sT s x))) ->
  (forall q, q `in` frv_typ T -> req (sR Sg q) (apR S2 (sR s q))) ->
  teq (apT Sg T) (apT S2 (apT s T)).
Proof.
  intros Sg S2 s T Hx Hq. rewrite apT_comp.
  exact (proj1 (ap_cong_on Sg (scomp S2 s)) T Hx Hq).
Qed.

(* ---- rows that can present a label ---- *)

Definition Surf (l : label) (Q : row) : Prop :=
  exists P T R0, req Q (row_Maybe l P T R0).

Lemma Surf_iff : forall l Q, Surf l Q <-> (raw l Q <> nil \/ rtail Q = row_Empty).
Proof.
  intros l Q. split.
  - intros (P & T & R0 & H). apply req_nf in H as [Ht Hl].
    destruct (rtail Q) eqn:Eq; try (right; reflexivity).
    all: left; intros Hn; specialize (Hl l); rewrite ents_maybe, Nat.eqb_refl in Hl;
      cbn [rtail] in Ht; rewrite <- Ht in Hl; unfold ents in Hl;
      rewrite Eq, Hn in Hl; cbn in Hl; inversion Hl.
  - intros [H | H].
    + destruct (raw l Q) as [ | [P T] es] eqn:Er; [ contradiction | ].
      destruct (extract_req l Q P T es Er) as (R0 & Hq & _). exists P, T, R0. exact Hq.
    + destruct (raw l Q) as [ | [P T] es] eqn:Er.
      * assert (Hlk : rlacks l Q = true) by (apply rlacks_iff; split; assumption).
        exists typ_Bool, typ_Bool, Q. apply req_sym. apply req_abs. exact Hlk.
      * destruct (extract_req l Q P T es Er) as (R0 & Hq & _). exists P, T, R0. exact Hq.
Qed.

Lemma Surf_ext : forall l l' X Q, l' <> l -> Surf l (row_Ext l' X Q) -> Surf l Q.
Proof.
  intros l l' X Q Hne H. apply Surf_iff in H. apply Surf_iff.
  assert (E : Nat.eqb l l' = false) by (apply Nat.eqb_neq; congruence).
  cbn in H. rewrite E in H. exact H.
Qed.

Lemma Surf_maybe : forall l l' P X Q, l' <> l -> Surf l (row_Maybe l' P X Q) -> Surf l Q.
Proof.
  intros l l' P X Q Hne H. apply Surf_iff in H. apply Surf_iff.
  assert (E : Nat.eqb l l' = false) by (apply Nat.eqb_neq; congruence).
  cbn in H. rewrite E in H. exact H.
Qed.

(* The row can present [l] with a presence that is no [Bool]: an entry [l] is
   present, which is all the unifier asks of the rewritten row when the front entry
   it unifies with is present. *)
Definition SurfP (l : label) (Q : row) : Prop :=
  exists P T R0, req Q (row_Maybe l P T R0) /\ is_abs P = false.

Lemma SurfP_empty : forall l, SurfP l row_Empty -> False.
Proof.
  intros l (P & T & R0 & Hq & Hna).
  assert (Hb : req (row_Maybe l typ_Bool typ_Bool row_Empty) row_Empty) by (apply req_abs; reflexivity).
  pose proof (row_cancel _ _ _ _ _ _ _ (req_trans _ _ _ (req_sym _ _ Hq) (req_sym _ _ Hb))) as [_ Hc].
  destruct Hc as [[Hp _]|[Hp _]].
  - rewrite (teq_is_abs _ _ Hp) in Hna. discriminate Hna.
  - rewrite Hp in Hna. discriminate Hna.
Qed.

(* Skipping an entry for another label keeps the presence, because two presentations
   of one label agree on a present one ([row_cancel]). *)
Lemma SurfP_ext : forall l l' X Q, l' <> l -> SurfP l (row_Ext l' X Q) -> SurfP l Q.
Proof.
  intros l l' X Q Hne (P & T & R0 & Hq & Hna).
  assert (Hs : Surf l Q) by (eapply Surf_ext; [ exact Hne | exists P, T, R0; exact Hq ]).
  destruct Hs as (P2 & T2 & R2 & Hq2).
  exists P2, T2, R2. split; [ exact Hq2 | ].
  assert (H1 : req (row_Ext l' X Q) (row_Maybe l P2 T2 (row_Ext l' X R2))).
  { eapply req_trans; [ apply req_head; [ apply teq_refl | exact Hq2 ] | ].
    apply req_sym. apply req_swap_em. congruence. }
  pose proof (row_cancel _ _ _ _ _ _ _ (req_trans _ _ _ (req_sym _ _ H1) Hq)) as [_ Hc].
  destruct Hc as [[Hp _]|[_ Hp]].
  - rewrite (teq_is_abs _ _ Hp). exact Hna.
  - rewrite Hp in Hna. discriminate Hna.
Qed.

Lemma SurfP_maybe : forall l l' P' X Q, l' <> l -> SurfP l (row_Maybe l' P' X Q) -> SurfP l Q.
Proof.
  intros l l' P' X Q Hne (P & T & R0 & Hq & Hna).
  assert (Hs : Surf l Q) by (eapply Surf_maybe; [ exact Hne | exists P, T, R0; exact Hq ]).
  destruct Hs as (P2 & T2 & R2 & Hq2).
  exists P2, T2, R2. split; [ exact Hq2 | ].
  assert (H1 : req (row_Maybe l' P' X Q) (row_Maybe l P2 T2 (row_Maybe l' P' X R2))).
  { eapply req_trans; [ apply req_maybe; [ apply teq_refl | apply teq_refl | exact Hq2 ] | ].
    apply req_sym. apply req_swap_mm. congruence. }
  pose proof (row_cancel _ _ _ _ _ _ _ (req_trans _ _ _ (req_sym _ _ H1) Hq)) as [_ Hc].
  destruct Hc as [[Hp _]|[_ Hp]].
  - rewrite (teq_is_abs _ _ Hp). exact Hna.
  - rewrite Hp in Hna. discriminate Hna.
Qed.

(* ---- the walk ---- *)

Lemma DOk_two : forall D n K, DOk D n -> DOk (rupd D (ea (Datatypes.S n)) K) (n + 2).
Proof.
  intros D n K H. replace (n + 2) with (Datatypes.S (Datatypes.S n)) by lia.
  apply DOk_rupd. eapply DOk_mono; [ exact H | lia ].
Qed.

Lemma DOk_three : forall D n k K,
  DOk D n -> DOk (rupd (upd D (ea (Datatypes.S n)) k) (ea (n + 2)) K) (n + 3).
Proof.
  intros D n k K H. replace (n + 3) with (Datatypes.S (n + 2)) by lia.
  replace (n + 2) with (Datatypes.S (Datatypes.S n)) by lia.
  apply DOk_rupd. apply DOk_upd. eapply DOk_mono; [ exact H | lia ].
Qed.

Ltac fin5 := refine (conj _ (conj _ (conj _ (conj _ (conj _ _))))).

Theorem rewrite_row_spec : forall l av R D n D1 Sg,
  DOk D n -> KR D D1 Sg ->
  (forall x, x `in` ftv_row R -> old n x) -> (forall q, q `in` frv_row R -> old n q) ->
  SurfP l (apR Sg R) ->
  forall P' T' R' s0 D0 n1, rewrite_row l av D R n = Some (P', T', R', s0, D0, n1) ->
  exists S2, KR D0 D1 S2 /\ n <= n1 /\ DOk D0 n1 /\
    (forall x, old n x -> teq (sT Sg x) (apT S2 (sT s0 x))) /\
    (forall q, old n q -> req (sR Sg q) (apR S2 (sR s0 q))) /\
    req (apR Sg R) (row_Maybe l (apT S2 P') (apT S2 T') (apR S2 R')).
Proof.
  intros l av R. induction R as [ | r | l' T' R IHR | l' P1 T' R IHR ];
    intros D n D1 Sg Hd HK Hx Hq Hsurf P' T0 R' s0 D0 n1 E.
  - (* the closed end: no entry presents the label *)
    exfalso. exact (SurfP_empty l Hsurf).
  - (* the row variable *)
    assert (Hm : AtomSetImpl.mem r av = false).
    { cbn [rewrite_row] in E. destruct (AtomSetImpl.mem r av); [ discriminate | reflexivity ]. }
    destruct Hsurf as (P0 & T1 & R0 & Hreq & Hna).
    assert (Hf : rk_lacks (drk D r) l = false -> P0 = typ_Bool -> sat D1 (rk_sort (drk D r)) T1)
      by (intros _ H; subst P0; discriminate Hna).
    destruct (rewrite_row_var_complete l av D n r D1 Sg P0 T1 R0 Hd HK Hm Hreq Hf)
      as (P1 & T2 & R1 & s1 & D2 & n2 & S2 & E2 & HK2 & Hn & HP & HT & HR & Hs1 & Hs2).
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
    + cbn [apR ap_row]. rewrite HP, HT, HR. exact Hreq.
  - (* a plain field *)
    cbn [rewrite_row] in E. destruct (Nat.eqb l l') eqn:Ell.
    + apply Nat.eqb_eq in Ell. subst l'. inversion E; subst. clear E.
      exists Sg. fin5; try assumption; try apply le_n.
      * intros x _. cbn [sT sid idt apT ap_typ]. apply teq_refl.
      * intros q _. cbn [sR sid idr apR ap_row]. apply req_refl.
      * cbn [apR ap_row apT ap_typ]. apply req_sym. apply req_pre.
    + apply Nat.eqb_neq in Ell.
      destruct (rewrite_row l av D R n) as [[[[[[P0 T1] R3] s] D2] n2] | ] eqn:E1;
        [ | discriminate ].
      inversion E; subst P' T0 R' s0 D0 n1. clear E.
      cbn [apR ap_row] in Hsurf. pose proof (SurfP_ext _ _ _ _ (not_eq_sym Ell) Hsurf) as Hs.
      destruct (IHR D n D1 Sg Hd HK
                  (fun x Hx' => Hx x ltac:(simpl; fsetdec)) (fun q Hq' => Hq q ltac:(simpl; fsetdec))
                  Hs P0 T1 R3 s D2 n2 E1)
        as (S2 & HK2 & Hn & Hd2 & Hf1 & Hf2 & Hinv).
      exists S2. fin5; try assumption.
      cbn [apR ap_row]. eapply req_trans.
      { apply req_head; [ | exact Hinv ].
        apply (ap_factor Sg S2 s T'); [ intros x Hx'; apply Hf1; apply Hx; simpl; fsetdec
                                      | intros q Hq'; apply Hf2; apply Hq; simpl; fsetdec ]. }
      apply req_sym. apply req_swap_em. exact Ell.
  - (* a presence entry *)
    cbn [rewrite_row] in E. destruct (Nat.eqb l l') eqn:Ell.
    + apply Nat.eqb_eq in Ell. subst l'. inversion E; subst. clear E.
      exists Sg. fin5; try assumption; try apply le_n.
      * intros x _. cbn [sT sid idt apT ap_typ]. apply teq_refl.
      * intros q _. cbn [sR sid idr apR ap_row]. apply req_refl.
      * cbn [apR ap_row]. apply req_refl.
    + apply Nat.eqb_neq in Ell.
      destruct (rewrite_row l av D R n) as [[[[[[P0 T1] R3] s] D2] n2] | ] eqn:E1;
        [ | discriminate ].
      inversion E; subst P' T0 R' s0 D0 n1. clear E.
      cbn [apR ap_row] in Hsurf. pose proof (SurfP_maybe _ _ _ _ _ (not_eq_sym Ell) Hsurf) as Hs.
      destruct (IHR D n D1 Sg Hd HK
                  (fun x Hx' => Hx x ltac:(simpl; fsetdec)) (fun q Hq' => Hq q ltac:(simpl; fsetdec))
                  Hs P0 T1 R3 s D2 n2 E1)
        as (S2 & HK2 & Hn & Hd2 & Hf1 & Hf2 & Hinv).
      exists S2. fin5; try assumption.
      cbn [apR ap_row]. eapply req_trans.
      { apply req_maybe; [ | | exact Hinv ].
        - apply (ap_factor Sg S2 s P1); [ intros x Hx'; apply Hf1; apply Hx; simpl; fsetdec
                                        | intros q Hq'; apply Hf2; apply Hq; simpl; fsetdec ].
        - apply (ap_factor Sg S2 s T'); [ intros x Hx'; apply Hf1; apply Hx; simpl; fsetdec
                                        | intros q Hq'; apply Hf2; apply Hq; simpl; fsetdec ]. }
      apply req_sym. apply req_swap_mm. exact Ell.
Qed.

(* What the unifier reads off the walk: the entry for [l] that [Sg R] has
   (presence [P0], field [T0], rest [R0]) is the rewritten front entry under
   [S2], except that two absent entries need not agree on the field. *)
Corollary rewrite_row_front : forall l av R D n D1 Sg P0 T0 R0,
  DOk D n -> KR D D1 Sg ->
  (forall x, x `in` ftv_row R -> old n x) -> (forall q, q `in` frv_row R -> old n q) ->
  req (apR Sg R) (row_Maybe l P0 T0 R0) -> is_abs P0 = false ->
  forall P' T' R' s0 D0 n1, rewrite_row l av D R n = Some (P', T', R', s0, D0, n1) ->
  exists S2, KR D0 D1 S2 /\ n <= n1 /\ DOk D0 n1 /\
    (forall x, old n x -> teq (sT Sg x) (apT S2 (sT s0 x))) /\
    (forall q, old n q -> req (sR Sg q) (apR S2 (sR s0 q))) /\
    req (apR S2 R') R0 /\
    ((teq (apT S2 P') P0 /\ teq (apT S2 T') T0) \/
     (is_abs (apT S2 P') = true /\ is_abs P0 = true)).
Proof.
  intros l av R D n D1 Sg P0 T0 R0 Hd HK Hx Hq Hreq Hna P' T' R' s0 D0 n1 E.
  destruct (rewrite_row_spec l av R D n D1 Sg Hd HK Hx Hq
              (ex_intro _ P0 (ex_intro _ T0 (ex_intro _ R0 (conj Hreq Hna)))) P' T' R' s0 D0 n1 E)
    as (S2 & HK2 & Hn & Hd2 & Hf1 & Hf2 & Hinv).
  pose proof (row_cancel _ _ _ _ _ _ _ (req_trans _ _ _ (req_sym _ _ Hinv) Hreq)) as [Hr Hc].
  exists S2. refine (conj HK2 (conj Hn (conj Hd2 (conj Hf1 (conj Hf2 (conj Hr _)))))).
  destruct Hc as [[H1 H2] | [H1 H2]]; [ left; split; assumption | right; split; assumption ].
Qed.

(* The call [unify_rD] makes: [Sg] unifies two rows, the first starts with an
   entry [Sg] makes present, and the second is rewritten to present its label.
   The rewrite succeeds (the guard [side_av] never blocks, [side_guard_passes]),
   and the extension [S2] of [Sg] to the fresh variables reads the rewritten
   front entry as [Sg]'s image of the first row's: presence and field agree (an
   absent pair, the one place they need not, cannot occur), and the rests are
   equal. *)
Theorem rewrite_row_complete : forall Sg R1 R2 l P T R1' D n D1,
  row_head R1 = Some (l, P, T, R1') -> teq (apT Sg P) typ_Unit ->
  req (apR Sg R1) (apR Sg R2) ->
  DOk D n -> KR D D1 Sg ->
  (forall x, x `in` ftv_row R2 -> old n x) -> (forall q, q `in` frv_row R2 -> old n q) ->
  exists P' T' R2' s0 D0 n1 S2,
    rewrite_row l (side_av R1) D R2 n = Some (P', T', R2', s0, D0, n1) /\
    KR D0 D1 S2 /\ n <= n1 /\ DOk D0 n1 /\
    (forall x, old n x -> teq (sT Sg x) (apT S2 (sT s0 x))) /\
    (forall q, old n q -> req (sR Sg q) (apR S2 (sR s0 q))) /\
    teq (apT S2 P') (apT Sg P) /\ teq (apT S2 T') (apT Sg T) /\ req (apR S2 R2') (apR Sg R1').
Proof.
  intros Sg R1 R2 l P T R1' D n D1 Hh HP Hreq Hd HK Hx Hq.
  pose proof (side_guard_passes Sg R1 R2 l P T R1' D n Hh HP Hreq) as Hnn.
  destruct (rewrite_row l (side_av R1) D R2 n) as [[[[[[P' T'] R2'] s0] D0] n1] | ] eqn:E;
    [ | contradiction ].
  assert (Hfront : req (apR Sg R2) (row_Maybe l (apT Sg P) (apT Sg T) (apR Sg R1'))).
  { apply req_sym in Hreq. eapply req_trans; [ exact Hreq | ].
    destruct R1 as [ | | l0 T0 R0 | l0 P0 T0 R0 ]; simpl in Hh; try discriminate;
      inversion Hh; subst; cbn [apR ap_row].
    - cbn [apT ap_typ]. apply req_sym. apply req_pre.
    - apply req_refl. }
  destruct (rewrite_row_front l (side_av R1) R2 D n D1 Sg _ _ _ Hd HK Hx Hq Hfront
              (eq_trans (teq_is_abs _ _ HP) eq_refl) P' T' R2' s0 D0 n1 E)
    as (S2 & HK2 & Hn & Hd2 & Hf1 & Hf2 & Hr & Hc).
  exists P', T', R2', s0, D0, n1, S2.
  refine (conj eq_refl (conj HK2 (conj Hn (conj Hd2 (conj Hf1 (conj Hf2 _)))))).
  destruct Hc as [[H1 H2] | [H1 H2]].
  - exact (conj H1 (conj H2 Hr)).
  - exfalso. rewrite (teq_is_abs _ _ HP) in H2. discriminate H2.
Qed.

(* The recursive calls of [unify_rD] run on [nfR D2] of the substituted rows.
   Substituting into [nfR D R] and normalizing at the finer environment gives
   the row normalizing the substituted original, up to [req]: this is the
   conversion the induction carries as its invariant ([reqD], not syntactic
   equality). *)
Corollary nfR_ap_nfR : forall D D1 Sg R, rkres D D1 (sR Sg) ->
  req (nfR D1 (apR Sg (nfR D R))) (nfR D1 (apR Sg R)).
Proof.
  intros D D1 Sg R Hk. apply req_sym.
  exact (proj2 (teqD_ap_nf_mut D D1 (sT Sg) (sR Sg) Hk) R).
Qed.
