(* Completeness of algorithm W, stage 7.8e: bounds on canonical representatives
   (docs/design/phase7-proof-plan.md).

   The record-free induction moves a bound on the atoms of a type across a
   conversion with [teqD_rf_eq], which makes two convertible record-free types
   equal.  Over the fragment, convertible types differ in the fields of absent
   entries ([req_absf]), so a bound is stated on the canonical representative
   [erT] (GoatCompleteEr.v), whose atoms are a conversion invariant ([er_inv]).

   [er_ap_sub] is the transfer: when every entry of a type is present under [S],
   the representative of the image of a type mentions every atom that the
   representatives of the images of its variables do.  [AvoidE] is [Avoid] stated
   on representatives, and [AvoidE_limg] and [AvoidE_next] are the two steps the
   induction takes with it.

   Axiom- and admit-free. *)

Require Import Metalib.Metatheory.
Require Import Goat.Goat_ott.
Require Import Goat.GoatRows.
Require Import Goat.GoatDefs.
Require Import Goat.GoatConv.
Require Import Goat.GoatSubst.
Require Import Goat.GoatInfer.
Require Import Goat.GoatConv.
Require Import Goat.GoatSound.
Require Import Goat.GoatInferSub.
Require Import Goat.GoatInferSort.
Require Import Goat.GoatCoerce.
Require Import Goat.GoatCompleteFuel.
Require Import Goat.GoatCompleteRf.
Require Import Goat.GoatCompleteSorts.
Require Import Goat.GoatCompleteRewrite.
Require Import Goat.GoatCompleteHeld.
Require Import Goat.GoatCompleteBind.
Require Import Goat.GoatCompleteRfRows.
Require Import Goat.GoatCompleteEr.
Require Import Goat.GoatCompleteCtx.
Require Import Goat.GoatCompleteLive.
Require Import Stdlib.Arith.Arith.
Require Import Stdlib.micromega.Lia.
Require Import Stdlib.Lists.List.
Import ListNotations.

(* ---- the transfer ---- *)

Lemma er_ap_sub : forall S,
  (forall T, pf T -> ps S T ->
     (forall x, x `in` ftv_typ T -> ftv_typ (erT (sT S x)) [<=] ftv_typ (erT (apT S T))) /\
     (forall r, r `in` frv_typ T -> ftv_row (erR (sR S r)) [<=] ftv_typ (erT (apT S T)))) /\
  (forall R, prf R -> psr S R ->
     (forall x, x `in` ftv_row R -> ftv_typ (erT (sT S x)) [<=] ftv_row (erR (apR S R))) /\
     (forall r, r `in` frv_row R -> ftv_row (erR (sR S r)) [<=] ftv_row (erR (apR S R)))).
Proof.
  intros S. apply typ_row_mutind; cbn [pf prf ps psr]; try (intros; contradiction);
    try (intros _ _; split; intros x Hx; simpl in Hx; fsetdec; fail).
  - (* arrow *)
    intros A IHA B IHB [PA PB] [SA SB].
    destruct (IHA PA SA) as [A1 A2]. destruct (IHB PB SB) as [B1 B2].
    rewrite apT_Arrow. cbn [erT ftv_typ]. split.
    + intros x Hx. apply AtomSetFacts.union_iff in Hx. destruct Hx as [Hx|Hx];
        [ pose proof (A1 x Hx) | pose proof (B1 x Hx) ]; fsetdec.
    + intros r Hr. apply AtomSetFacts.union_iff in Hr. destruct Hr as [Hr|Hr];
        [ pose proof (A2 r Hr) | pose proof (B2 r Hr) ]; fsetdec.
  - (* record *)
    intros R IH HR PR. destruct (IH HR PR) as [H1 H2].
    change (apT S (typ_Record R)) with (typ_Record (apR S R)). cbn [erT ftv_typ]. split; assumption.
  - (* variable *)
    intros a _ _. rewrite apT_Var. split.
    + intros x Hx. apply AtomSetFacts.singleton_iff in Hx. subst x. intros y Hy. exact Hy.
    + intros r Hr. exfalso. fsetdec.
  - (* group *)
    intros w A IH [HA _] PA. destruct (IH HA PA) as [H1 H2].
    change (apT S (typ_Grp w A)) with (typ_Grp w (apT S A)). cbn [erT ftv_typ]. split; assumption.
  - (* row variable *)
    intros r _ _. change (apR S (row_Var r)) with (sR S r). split.
    + intros x Hx. exfalso. fsetdec.
    + intros q Hq. apply AtomSetFacts.singleton_iff in Hq. subst q. intros y Hy. exact Hy.
  - (* present entry *)
    intros l T IHT R IHR [HT HR] [PT PR]. destruct (IHT HT PT) as [T1 T2]. destruct (IHR HR PR) as [R1 R2].
    change (apR S (row_Ext l T R)) with (row_Ext l (apT S T) (apR S R)). cbn [erR ftv_row]. split.
    + intros x Hx. apply AtomSetFacts.union_iff in Hx. destruct Hx as [Hx|Hx];
        [ pose proof (T1 x Hx) | pose proof (R1 x Hx) ]; fsetdec.
    + intros r Hr. apply AtomSetFacts.union_iff in Hr. destruct Hr as [Hr|Hr];
        [ pose proof (T2 r Hr) | pose proof (R2 r Hr) ]; fsetdec.
  - (* maybe entry *)
    intros l P IHP T IHT R IHR [HP [HT HR]] [PP [PT PR]]. destruct (IHT HT PT) as [T1 T2]. destruct (IHR HR PR) as [R1 R2].
    change (apR S (row_Maybe l P T R)) with (row_Maybe l (apT S P) (apT S T) (apR S R)).
    rewrite PP. cbn [erR is_abs erT ftv_row ftv_typ]. split.
    + intros x Hx. apply AtomSetFacts.union_iff in Hx. destruct Hx as [Hx|Hx].
      * destruct (pres_shape S P HP PP) as [->|[v [-> Hv]]].
        -- simpl in Hx. fsetdec.
        -- simpl in Hx. apply AtomSetFacts.singleton_iff in Hx. subst x. rewrite Hv. simpl. fsetdec.
      * apply AtomSetFacts.union_iff in Hx. destruct Hx as [Hx|Hx];
          [ pose proof (T1 x Hx) | pose proof (R1 x Hx) ]; fsetdec.
    + intros r Hr. apply AtomSetFacts.union_iff in Hr. destruct Hr as [Hr|Hr].
      * exfalso. exact (pres_frv S P r HP PP Hr).
      * apply AtomSetFacts.union_iff in Hr. destruct Hr as [Hr|Hr];
          [ pose proof (T2 r Hr) | pose proof (R2 r Hr) ]; fsetdec.
Qed.

(* ---- [Avoid] on representatives ---- *)

(* The atoms of the representatives of the images of the live atoms and live row
   variables stay inside [B]: the atoms a binder generalizes are chosen outside it. *)
Definition AvoidE (B : atoms) (L LR : atoms) (Sg : sub) : Prop :=
  (forall x, x `in` L -> ftv_typ (erT (sT Sg x)) [<=] B) /\
  (forall q, q `in` LR -> ftv_row (erR (sR Sg q)) [<=] B).

Lemma AvoidE_mono : forall B B' L LR Sg, B [<=] B' -> AvoidE B L LR Sg -> AvoidE B' L LR Sg.
Proof.
  intros B B' L LR Sg Hb (H1 & H2). split.
  - intros x Hx y Hy. apply Hb. exact (H1 x Hx y Hy).
  - intros q Hq y Hy. apply Hb. exact (H2 q Hq y Hy).
Qed.

Lemma AvoidE_sub : forall B L L' LR LR' Sg, L' [<=] L -> LR' [<=] LR -> AvoidE B L LR Sg -> AvoidE B L' LR' Sg.
Proof.
  intros B L L' LR LR' Sg Hl Hr (H1 & H2). split.
  - intros x Hx. exact (H1 x (Hl x Hx)).
  - intros q Hq. exact (H2 q (Hr q Hq)).
Qed.

Lemma AvoidE_empty : forall B Sg, AvoidE B {} {} Sg.
Proof.
  intros B Sg. split; intros x Hx; exfalso; revert Hx; fsetdec.
Qed.

Lemma AvoidE_fresh : forall B n L LR Sg U, LOld n L -> AvoidE B L LR Sg -> ftv_typ (erT U) [<=] B ->
  AvoidE B (L `union` {{ ea n }}) LR (supd Sg (ea n) U).
Proof.
  intros B n L LR Sg U Ho (H1 & H2) HU. split.
  - intros x Hx. apply AtomSetFacts.union_iff in Hx. destruct Hx as [Hx|Hx].
    + rewrite supd_other by (intro E; exact (Ho x Hx n (le_n n) E)). exact (H1 x Hx).
    + apply AtomSetFacts.singleton_iff in Hx. subst x. rewrite supd_same. exact HU.
  - intros q Hq. exact (H2 q Hq).
Qed.

Lemma AvoidE_agree : forall B L LR Sg Sg', AvoidE B L LR Sg ->
  (forall a, a `in` L -> sT Sg' a = sT Sg a) -> (forall q, q `in` LR -> sR Sg' q = sR Sg q) ->
  AvoidE B L LR Sg'.
Proof.
  intros B L LR Sg Sg' (H1 & H2) Ha Hq. split.
  - intros x Hx. rewrite (Ha x Hx). exact (H1 x Hx).
  - intros q Hq'. rewrite (Hq q Hq'). exact (H2 q Hq').
Qed.

Lemma teq_er_sub : forall A A' B, teq A A' -> ftv_typ (erT A') [<=] B -> ftv_typ (erT A) [<=] B.
Proof.
  intros A A' B Ht Hb y Hy. apply Hb. exact (proj1 (proj1 (proj1 er_inv A A' Ht) y) Hy).
Qed.

Lemma req_er_sub : forall R R' B, req R R' -> ftv_row (erR R') [<=] B -> ftv_row (erR R) [<=] B.
Proof.
  intros R R' B Ht Hb y Hy. apply Hb. exact (proj1 (proj1 (proj2 er_inv R R' Ht) y) Hy).
Qed.

(* ---- a step, without the bounds clause ---- *)

(* [SemG] (GoatCompleteLive.v) without its last bounds clause.  That clause
   asks a bound on [Sg] to reach the images of the live atoms, and two steps
   compose only when it reaches the atoms of the first step's result type as
   well; the bound a derivation's types satisfy is [AvoidE], which needs no such
   hypothesis. *)
Definition SemW (E F : atom -> Prop) (L LR : atoms) (DT : denv) (Sg : sub) (n : nat) (s : sub)
  (D' : denv) (n' : nat) (S2 : sub) : Prop :=
  DOk D' n' /\ Drow D' /\ LiveG E F (limgT s L LR) (limgR s L LR) D' DT S2 /\ SIg n n' s S2 L LR /\
  (forall x, x `in` L -> teq (sT Sg x) (apT S2 (sT s x))) /\
  (forall q, q `in` LR -> req (sR Sg q) (apR S2 (sR s q))) /\ OkS s.

Lemma SemW_of_G : forall E F L LR DT Sg n s D' n' S2,
  SemG E F L LR DT Sg n s D' n' S2 -> SemW E F L LR DT Sg n s D' n' S2.
Proof.
  intros E F L LR DT Sg n s D' n' S2 (A & B & C & D & F1 & F2 & _ & Ok).
  exact (conj A (conj B (conj C (conj D (conj F1 (conj F2 Ok)))))).
Qed.

Lemma SemW_DOk : forall E F L LR DT Sg n s D' n' S2, SemW E F L LR DT Sg n s D' n' S2 -> DOk D' n'.
Proof. intros E F L LR DT Sg n s D' n' S2 H. exact (proj1 H). Qed.

Lemma SemW_live : forall E F L LR DT Sg n s D' n' S2, SemW E F L LR DT Sg n s D' n' S2 ->
  LiveG E F (limgT s L LR) (limgR s L LR) D' DT S2.
Proof. intros E F L LR DT Sg n s D' n' S2 H. exact (proj1 (proj2 (proj2 H))). Qed.

Lemma SemW_SIg : forall E F L LR DT Sg n s D' n' S2, SemW E F L LR DT Sg n s D' n' S2 -> SIg n n' s S2 L LR.
Proof. intros E F L LR DT Sg n s D' n' S2 H. exact (proj1 (proj2 (proj2 (proj2 H)))). Qed.

Lemma SemW_OkS : forall E F L LR DT Sg n s D' n' S2, SemW E F L LR DT Sg n s D' n' S2 -> OkS s.
Proof. intros E F L LR DT Sg n s D' n' S2 H. exact (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 H)))))). Qed.

Lemma SemW_F : forall E F L LR DT Sg n s D' n' S2, SemW E F L LR DT Sg n s D' n' S2 ->
  forall x, x `in` L -> teq (sT Sg x) (apT S2 (sT s x)).
Proof. intros E F L LR DT Sg n s D' n' S2 H. exact (proj1 (proj2 (proj2 (proj2 (proj2 H))))). Qed.

Lemma SemW_FR : forall E F L LR DT Sg n s D' n' S2, SemW E F L LR DT Sg n s D' n' S2 ->
  forall q, q `in` LR -> req (sR Sg q) (apR S2 (sR s q)).
Proof. intros E F L LR DT Sg n s D' n' S2 H. exact (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 H)))))). Qed.

Lemma SemW_mono : forall E F L1 L2 LR1 LR2 DT Sg n s D' n' S2, L1 [<=] L2 -> LR1 [<=] LR2 ->
  SemW E F L2 LR2 DT Sg n s D' n' S2 -> SemW E F L1 LR1 DT Sg n s D' n' S2.
Proof.
  intros E F L1 L2 LR1 LR2 DT Sg n s D' n' S2 Hl Hr (Hd & Hw & Hv & (Hn & Hx & Hq) & F1 & F2 & Ok).
  refine (conj Hd (conj Hw (conj (LiveG_mono _ _ _ _ _ _ _ _ _ (limgT_mono s _ _ _ _ Hl Hr) (limgR_mono s _ _ _ _ Hl Hr) Hv)
    (conj (conj Hn (conj _ _)) (conj _ (conj _ Ok)))))).
  - intros x Hx'. exact (Hx x (Hl x Hx')).
  - intros q Hq'. exact (Hq q (Hr q Hq')).
  - intros x Hx'. exact (F1 x (Hl x Hx')).
  - intros q Hq'. exact (F2 q (Hr q Hq')).
Qed.

(* A step from a substitution that agrees with [Sg] on the live atoms and rows,
   below a smaller supply, is a step from [Sg]. *)
Lemma SemW_weaken : forall E F L LR DT Sg Sg' n0 n1 s D' n' S2,
  n0 <= n1 -> SemW E F L LR DT Sg' n1 s D' n' S2 ->
  (forall x, x `in` L -> sT Sg' x = sT Sg x) -> (forall q, q `in` LR -> sR Sg' q = sR Sg q) ->
  SemW E F L LR DT Sg n0 s D' n' S2.
Proof.
  intros E F L LR DT Sg Sg' n0 n1 s D' n' S2 Hl (Hd & Hw & Hv & (Hn & Hx & Hq) & F1 & F2 & Ok) Ex Er.
  refine (conj Hd (conj Hw (conj Hv (conj (conj (Nat.le_trans _ _ _ Hl Hn) (conj Hx Hq)) (conj _ (conj _ Ok)))))).
  - intros x Hx'. rewrite <- (Ex x Hx'). exact (F1 x Hx').
  - intros q Hq'. rewrite <- (Er q Hq'). exact (F2 q Hq').
Qed.

Lemma SemW_id : forall E F L LR DT Sg D n, DOk D n -> Drow D -> LOld n L -> LOld n LR ->
  LiveG E F L LR D DT Sg -> SemW E F L LR DT Sg n sid D n Sg.
Proof.
  intros. apply SemW_of_G. exact (SemG_id E F L LR DT Sg D n H H0 H1 H2 H3).
Qed.

Lemma SemW_fresh : forall E F L LR DT D Sg n k U,
  DOk D n -> Drow D -> LOld n L -> LOld n LR -> LiveG E F L LR D DT Sg ->
  SemW E F L LR DT Sg n sid (upd D (ea n) k) (S n) (supd Sg (ea n) U).
Proof.
  intros. apply SemW_of_G. exact (SemG_fresh E F L LR DT D Sg n k U H H0 H1 H2 H3).
Qed.

(* The step that ran past a fresh atom is a step from the old substitution. *)
Lemma SemW_unfresh : forall E F Ln LR DT Sg n U s D' n' S2, LOld n Ln ->
  SemW E F (Ln `union` {{ ea n }}) LR DT (supd Sg (ea n) U) (S n) s D' n' S2 ->
  SemW E F Ln LR DT Sg n s D' n' S2.
Proof.
  intros E F Ln LR DT Sg n U s D' n' S2 Ho H.
  refine (SemW_weaken E F Ln LR DT Sg (supd Sg (ea n) U) n (S n) s D' n' S2 (Nat.le_succ_diag_r n)
            (SemW_mono E F Ln _ LR LR DT _ _ s D' n' S2 _ (fun y Hy => Hy) H) _ _).
  - intros x Hx. fsetdec.
  - intros x Hx. apply supd_other. intro E0. exact (Ho x Hx n (le_n n) E0).
  - intros q _. reflexivity.
Qed.

(* Two steps compose.  The second step's live set [Lm] holds the images of the first. *)
Lemma SemW_comp : forall E F L LR Lm LRm DT Sg n s D1 n1 S1 s' D2 n2 S2,
  SemW E F L LR DT Sg n s D1 n1 S1 -> limgT s L LR [<=] Lm -> limgR s L LR [<=] LRm ->
  SemW E F Lm LRm DT S1 n1 s' D2 n2 S2 ->
  SemW E F L LR DT Sg n (scomp s' s) D2 n2 S2.
Proof.
  intros E F L LR Lm LRm DT Sg n s D1 n1 S1 s' D2 n2 S2
    (Hd1 & Hw1 & Hv1 & HI1 & Fx1 & Fr1 & Ok1) HsT HsR
    (Hd2 & Hw2 & Hv2 & HI2 & Fx2 & Fr2 & Ok2).
  destruct (limg_scompG s s' L LR) as [GT GR].
  destruct HI1 as (Hl1 & Hx1 & Hq1). pose proof HI2 as HI2'. destruct HI2 as (Hl2 & Hx2 & Hq2).
  assert (Tx : forall x, x `in` L -> ftv_typ (sT s x) [<=] Lm).
  { intros x Hx y Hy. apply HsT. apply limgT_in. left. exists x. split; assumption. }
  assert (Rx : forall x, x `in` L -> frv_typ (sT s x) [<=] LRm).
  { intros x Hx y Hy. apply HsR. apply limgR_in. left. exists x. split; assumption. }
  assert (Tq : forall q, q `in` LR -> ftv_row (sR s q) [<=] Lm).
  { intros q Hq y Hy. apply HsT. apply limgT_in. right. exists q. split; assumption. }
  assert (Rq : forall q, q `in` LR -> frv_row (sR s q) [<=] LRm).
  { intros q Hq y Hy. apply HsR. apply limgR_in. right. exists q. split; assumption. }
  refine (conj Hd2 (conj Hw2 (conj _ (conj _ (conj _ (conj _ (OkS_comp _ _ Ok2 Ok1))))))).
  - exact (LiveG_mono _ _ _ _ _ _ _ _ _
             (fun y Hy => limgT_mono s' _ _ _ _ HsT HsR y (GT y Hy))
             (fun y Hy => limgR_mono s' _ _ _ _ HsT HsR y (GR y Hy)) Hv2).
  - refine (conj (Nat.le_trans _ _ _ Hl1 Hl2) (conj _ _)).
    + intros x Hx. destruct (Hx1 x Hx) as (P & A & PS).
      exact (SemG_ap_T S1 S2 s' n1 n2 Lm LRm (sT s x) HI2' (Tx x Hx) (Rx x Hx) P PS Fx2).
    + intros q Hq. destruct (Hq1 q Hq) as (P & A & PS).
      exact (SemG_ap_R S1 S2 s' n1 n2 Lm LRm (sR s q) HI2' (Tq q Hq) (Rq q Hq) P PS Fx2).
  - intros x Hx. change (teq (sT Sg x) (apT S2 (apT s' (sT s x)))).
    eapply teq_trans; [ exact (Fx1 x Hx) | ].
    apply ap_factor; [ intros y Hy; exact (Fx2 y (Tx x Hx y Hy)) | intros q Hq; exact (Fr2 q (Rx x Hx q Hq)) ].
  - intros q Hq. change (req (sR Sg q) (apR S2 (apR s' (sR s q)))).
    eapply req_trans; [ exact (Fr1 q Hq) | ].
    apply ap_factor_row; [ intros y Hy; exact (Fx2 y (Tq q Hq y Hy)) | intros r Hr; exact (Fr2 r (Rq q Hq r Hr)) ].
Qed.

Lemma SemW_live_ap : forall E F L LR DT Sg n s D' n' S2 T,
  SemW E F L LR DT Sg n s D' n' S2 ->
  ftv_typ T [<=] L -> frv_typ T [<=] LR ->
  LiveG E F (ftv_typ (apT s T)) (frv_typ (apT s T)) D' DT S2.
Proof.
  intros E F L LR DT Sg n s D' n' S2 T H Hs Hr.
  refine (LiveG_mono _ _ _ _ _ _ _ _ _ _ _ (SemW_live _ _ _ _ _ _ _ _ _ _ _ H)).
  - intros y Hy. apply limgT_in. destruct (ftv_ap_typ _ _ _ _ Hy) as [(b & Hb & Hyb)|(p & Hp & Hyp)].
    + left. exists b. split; [ exact (Hs b Hb) | exact Hyb ].
    + right. exists p. split; [ exact (Hr p Hp) | exact Hyp ].
  - intros y Hy. apply limgR_in. destruct (frv_ap_typ _ _ _ _ Hy) as [(b & Hb & Hyb)|(p & Hp & Hyp)].
    + left. exists b. split; [ exact (Hs b Hb) | exact Hyb ].
    + right. exists p. split; [ exact (Hr p Hp) | exact Hyp ].
Qed.

(* A type over live atoms factors through the step. *)
Lemma SemW_factor : forall E F L LR DT Sg n s D' n' S2 T,
  SemW E F L LR DT Sg n s D' n' S2 -> ftv_typ T [<=] L -> frv_typ T [<=] LR ->
  teq (apT Sg T) (apT S2 (apT s T)).
Proof.
  intros E F L LR DT Sg n s D' n' S2 T H Hs Hr.
  apply ap_factor; [ intros z Hz; exact (SemW_F _ _ _ _ _ _ _ _ _ _ _ H z (Hs z Hz))
                   | intros q Hq; exact (SemW_FR _ _ _ _ _ _ _ _ _ _ _ H q (Hr q Hq)) ].
Qed.

(* ---- the bounds across a step ---- *)

(* The images of the live atoms and rows keep their bound through a step. *)
Lemma AvoidE_limg : forall B E F L LR DT Sg n s D' n' S2,
  AvoidE B L LR Sg -> SemW E F L LR DT Sg n s D' n' S2 ->
  AvoidE B (limgT s L LR) (limgR s L LR) S2.
Proof.
  intros B E F L LR DT Sg n s D' n' S2 (HA1 & HA2) Hs.
  pose proof (SemW_SIg _ _ _ _ _ _ _ _ _ _ _ Hs) as (_ & Hx & Hq).
  pose proof (SemW_F _ _ _ _ _ _ _ _ _ _ _ Hs) as Fx. pose proof (SemW_FR _ _ _ _ _ _ _ _ _ _ _ Hs) as Fr.
  assert (Ty : forall y, y `in` L -> forall z, (z `in` ftv_typ (sT s y) -> ftv_typ (erT (sT S2 z)) [<=] B) /\
                                              (z `in` frv_typ (sT s y) -> ftv_row (erR (sR S2 z)) [<=] B)).
  { intros y Hy z. destruct (Hx y Hy) as (P & _ & PS). pose proof (proj1 (er_ap_sub S2) _ P PS) as (E1 & E2).
    assert (Hb : ftv_typ (erT (apT S2 (sT s y))) [<=] B) by exact (teq_er_sub _ _ _ (teq_sym _ _ (Fx y Hy)) (HA1 y Hy)).
    split; intros Hz y' Hy'; apply Hb; [ exact (E1 z Hz y' Hy') | exact (E2 z Hz y' Hy') ]. }
  assert (Tq : forall q, q `in` LR -> forall z, (z `in` ftv_row (sR s q) -> ftv_typ (erT (sT S2 z)) [<=] B) /\
                                               (z `in` frv_row (sR s q) -> ftv_row (erR (sR S2 z)) [<=] B)).
  { intros q Hq' z. destruct (Hq q Hq') as (P & _ & PS). pose proof (proj2 (er_ap_sub S2) _ P PS) as (E1 & E2).
    assert (Hb : ftv_row (erR (apR S2 (sR s q))) [<=] B) by exact (req_er_sub _ _ _ (req_sym _ _ (Fr q Hq')) (HA2 q Hq')).
    split; intros Hz y' Hy'; apply Hb; [ exact (E1 z Hz y' Hy') | exact (E2 z Hz y' Hy') ]. }
  split.
  - intros z Hz. apply limgT_in in Hz. destruct Hz as [(y & Hy & Hz)|(q & Hq' & Hz)];
      [ exact (proj1 (Ty y Hy z) Hz) | exact (proj1 (Tq q Hq' z) Hz) ].
  - intros z Hz. apply limgR_in in Hz. destruct Hz as [(y & Hy & Hz)|(q & Hq' & Hz)];
      [ exact (proj2 (Ty y Hy z) Hz) | exact (proj2 (Tq q Hq' z) Hz) ].
Qed.

(* What a run hands on: the live atoms' images and the result type's atoms. *)
Definition lnT (s : sub) (L LR : atoms) (T : typ) : atoms := limgT s L LR `union` ftv_typ T.
Definition lnR (s : sub) (L LR : atoms) (T : typ) : atoms := limgR s L LR `union` frv_typ T.

Lemma limgT_lnT : forall s L LR T, limgT s L LR [<=] lnT s L LR T.
Proof. intros s L LR T y Hy. unfold lnT. fsetdec. Qed.
Lemma ftv_lnT : forall s L LR T, ftv_typ T [<=] lnT s L LR T.
Proof. intros s L LR T y Hy. unfold lnT. fsetdec. Qed.
Lemma limgR_lnR : forall s L LR T, limgR s L LR [<=] lnR s L LR T.
Proof. intros s L LR T y Hy. unfold lnR. fsetdec. Qed.
Lemma frv_lnR : forall s L LR T, frv_typ T [<=] lnR s L LR T.
Proof. intros s L LR T y Hy. unfold lnR. fsetdec. Qed.

(* The bound reaches the atoms the next premise reads: the old ones by the
   factoring through the step, the result type's by its conversion to the
   derivation's type. *)
Lemma AvoidE_next : forall B B' E F L LR DT Sg n s D1 n1 S1 T Tp,
  AvoidE B L LR Sg -> SemW E F L LR DT Sg n s D1 n1 S1 ->
  pf T -> ps S1 T -> teq (apT S1 T) Tp ->
  B [<=] B' -> ftv_typ (erT Tp) [<=] B' ->
  AvoidE B' (lnT s L LR T) (lnR s L LR T) S1.
Proof.
  intros B B' E F L LR DT Sg n s D1 n1 S1 T Tp HA Hs HT PT Heq Hb HTp.
  pose proof (AvoidE_limg B E F L LR DT Sg n s D1 n1 S1 HA Hs) as (H1 & H2).
  pose proof (proj1 (er_ap_sub S1) _ HT PT) as (E1 & E2).
  assert (Hbt : ftv_typ (erT (apT S1 T)) [<=] B') by exact (teq_er_sub _ _ _ Heq HTp).
  split.
  - intros z Hz. unfold lnT in Hz. apply AtomSetFacts.union_iff in Hz. destruct Hz as [Hz|Hz].
    + intros y Hy. apply Hb. exact (H1 z Hz y Hy).
    + intros y Hy. apply Hbt. exact (E1 z Hz y Hy).
  - intros z Hz. unfold lnR in Hz. apply AtomSetFacts.union_iff in Hz. destruct Hz as [Hz|Hz].
    + intros y Hy. apply Hb. exact (H2 z Hz y Hy).
    + intros y Hy. apply Hbt. exact (E2 z Hz y Hy).
Qed.
