(* Completeness of algorithm W, stage 7.8g: what the induction over the core
   carries, on [SemW] (docs/design/phase7-proof-plan.md).

   GoatCompleteCtx.v states a step of the core's run as a [SemL], which reads
   the unifier through its record-free completeness and compares types by
   [teqD].  Here the step is [SemC]: a [SemW] (GoatCompleteBound.v) on the live
   type atoms, no live row variable, with the two facts the record-free core
   adds to it, namely that the step sends each live atom to a record-free type
   and that the live clauses [Live PEv] (GoatCompleteMono.v) hold of the images
   under the extension.  The types the core compares are record-free, so a
   convertible pair is equal ([teq_rf_eq]) and these two facts are what the
   cases read off a [teq]; the stage that lets a record in drops them.

   The contexts: [CIT] (GoatCompleteCtxT.v) is the comparison the derivation's
   context is held to, and [CI_stepW] is its step, the one that
   GoatCompleteCtx.v's [CI_stepL] took with [teqD_rf_eq].  A scheme of the
   algorithm's context becomes [apS (sfix q S2) (apS s sc)] where the
   derivation's side still has [apS (sfix q Sg) sc], and the two bodies are
   convertible by [ap_factor] ([sch_leT_conv]).

   Axiom- and admit-free. *)

Require Import Metalib.Metatheory.
Require Import Goat.Goat_ott.
Require Import Goat.GoatRows.
Require Import Goat.GoatDefs.
Require Import Goat.GoatConv.
Require Import Goat.GoatSubst.
Require Import Goat.GoatSound.
Require Import Goat.GoatInfer.
Require Import Goat.GoatInferSub.
Require Import Goat.GoatInferSort.
Require Import Goat.GoatInferGen.
Require Import Goat.GoatInferUnify.
Require Import Goat.GoatCoerce.
Require Import Goat.GoatCompleteFuel.
Require Import Goat.GoatCompleteBind.
Require Import Goat.GoatCompleteRf.
Require Import Goat.GoatCompleteRfRows.
Require Import Goat.GoatCompleteSorts.
Require Import Goat.GoatCompleteRewrite.
Require Import Goat.GoatCompleteInst.
Require Import Goat.GoatCompleteGen.
Require Import Goat.GoatCompleteMono.
Require Import Goat.GoatCompleteDrk.
Require Import Goat.GoatCompleteEr.
Require Import Goat.GoatCompleteCtx.
Require Import Goat.GoatCompleteLive.
Require Import Goat.GoatCompleteLiveRf.
Require Import Goat.GoatCompleteBound.
Require Import Goat.GoatCompleteSchT.
Require Import Goat.GoatCompleteMonoT.
Require Import Goat.GoatCompleteCtxT.
Require Import Stdlib.Arith.Arith.
Require Import Stdlib.micromega.Lia.
Require Import Stdlib.Lists.List.
Import ListNotations.

(* ---- the live clauses of the record-free core ---- *)

Definition evA (a : atom) : Prop := ev a.

Notation LvE := (LiveG evA evA).

Lemma LvE_of_Live : forall L D Dd S, Live PEv L D Dd S -> LvE L {} D Dd S.
Proof.
  intros L D Dd S H. refine (conj _ (conj _ (conj (conj _ _) _))).
  - intros a Ha. exact (proj1 (H a Ha)).
  - intros q Hq. exfalso. revert Hq. fsetdec.
  - intros a Ha. destruct (proj2 (H a Ha)) as [[Hf Hq] _]. exact (conj Hf Hq).
  - intros q Hq. exfalso. revert Hq. fsetdec.
  - intros a Ha _ R E0. pose proof (proj2 (proj2 (H a Ha))) as Hr.
    rewrite E0 in Hr. simpl in Hr. exact Hr.
Qed.

Lemma Live_of_LvE : forall L D Dd S, LvE L {} D Dd S -> (forall a, a `in` L -> rf (sT S a)) ->
  Live PEv L D Dd S.
Proof.
  intros L D Dd S (Hs & _ & (Ht & _) & _) Hr a Ha.
  exact (conj (Hs a Ha) (conj (conj (proj1 (Ht a Ha)) (proj2 (Ht a Ha))) (Hr a Ha))).
Qed.

Lemma limgT_nil : forall s L, limgT s L {} [=] limg s L.
Proof.
  intros s L y. rewrite limgT_in, limg_in. split.
  - intros [H|(q & Hq & _)]; [ exact H | exfalso; revert Hq; fsetdec ].
  - intros H. left. exact H.
Qed.

Lemma limgR_rf : forall s L, (forall x, x `in` L -> rf (sT s x)) -> limgR s L {} [<=] {}.
Proof.
  intros s L H y Hy. apply limgR_in in Hy.
  destruct Hy as [(x & Hx & Hy)|(q & Hq & _)]; [ | exfalso; revert Hq; fsetdec ].
  exfalso. exact (proj1 (proj2 (proj2 (rf_facts _ (H x Hx)))) y Hy).
Qed.

Lemma Drow_of_RA : forall D, RA D -> Drow D.
Proof. intros D H r. left. rewrite (H r). reflexivity. Qed.

Lemma Drow_upd : forall D a k, Drow D -> Drow (upd D a k).
Proof. intros D a k H r. cbn [upd drk]. exact (H r). Qed.

(* ---- a step of the core's run ---- *)

(* [SemW] on the live type atoms (no live row variable), and the record-free
   facts the core reads off a conversion. *)
Definition SemC (L : atoms) (DT : denv) (Sg : sub) (n : nat) (s : sub) (D' : denv) (n' : nat) (S2 : sub) : Prop :=
  SemW evA evA L {} DT Sg n s D' n' S2 /\ (forall x, x `in` L -> rf (sT s x)) /\
  Live PEv (limg s L) D' DT S2.

Section SemCAcc.
Variables (L : atoms) (DT : denv) (Sg : sub) (n : nat) (s : sub) (D' : denv) (n' : nat) (S2 : sub).
Hypothesis H : SemC L DT Sg n s D' n' S2.

Lemma SemC_W : SemW evA evA L {} DT Sg n s D' n' S2. Proof. exact (proj1 H). Qed.
Lemma SemC_rf : forall x, x `in` L -> rf (sT s x). Proof. exact (proj1 (proj2 H)). Qed.
Lemma SemC_live : Live PEv (limg s L) D' DT S2. Proof. exact (proj2 (proj2 H)). Qed.
Lemma SemC_DOk : DOk D' n'. Proof. exact (SemW_DOk _ _ _ _ _ _ _ _ _ _ _ SemC_W). Qed.
Lemma SemC_Drow : Drow D'. Proof. exact (proj1 (proj2 (SemC_W))). Qed.
Lemma SemC_OkS : OkS s. Proof. exact (SemW_OkS _ _ _ _ _ _ _ _ _ _ _ SemC_W). Qed.
Lemma SemC_F : forall x, x `in` L -> teq (sT Sg x) (apT S2 (sT s x)).
Proof. exact (SemW_F _ _ _ _ _ _ _ _ _ _ _ SemC_W). Qed.
Lemma SemC_le : n <= n'.
Proof. exact (proj1 (SemW_SIg _ _ _ _ _ _ _ _ _ _ _ SemC_W)). Qed.
Lemma SemC_old : LOld n' (limg s L).
Proof.
  intros y Hy. apply (limgT_old n n' s S2 L {} (SemW_SIg _ _ _ _ _ _ _ _ _ _ _ SemC_W)).
  apply limgT_nil. exact Hy.
Qed.
End SemCAcc.

Arguments SemC_W {L DT Sg n s D' n' S2} H.
Arguments SemC_rf {L DT Sg n s D' n' S2} H x _.
Arguments SemC_live {L DT Sg n s D' n' S2} H.
Arguments SemC_DOk {L DT Sg n s D' n' S2} H.
Arguments SemC_Drow {L DT Sg n s D' n' S2} H.
Arguments SemC_OkS {L DT Sg n s D' n' S2} H.
Arguments SemC_F {L DT Sg n s D' n' S2} H x _.
Arguments SemC_le {L DT Sg n s D' n' S2} H.
Arguments SemC_old {L DT Sg n s D' n' S2} H.

Lemma SemC_ev : forall L DT Sg n s D' n' S2, SemC L DT Sg n s D' n' S2 -> LEv L -> LEv (limg s L).
Proof. intros L DT Sg n s D' n' S2 H HL. exact (limg_ev s L (SemC_OkS H) HL). Qed.

(* A record-free type over live atoms factors through the step. *)
Lemma SemC_factor : forall L DT Sg n s D' n' S2 T, SemC L DT Sg n s D' n' S2 ->
  rf T -> ftv_typ T [<=] L -> teq (apT Sg T) (apT S2 (apT s T)).
Proof.
  intros L DT Sg n s D' n' S2 T H Hrf Hs.
  assert (Hf : frv_typ T [<=] {}) by (intros q Hq; exfalso; exact (proj1 (proj2 (proj2 (rf_facts T Hrf))) q Hq)).
  exact (SemW_factor _ _ _ _ _ _ _ _ _ _ _ _ (SemC_W H) Hs Hf).
Qed.

Lemma SemC_live_ap : forall L DT Sg n s D' n' S2 T, SemC L DT Sg n s D' n' S2 ->
  rf T -> ftv_typ T [<=] L -> Live PEv (ftv_typ (apT s T)) D' DT S2.
Proof.
  intros L DT Sg n s D' n' S2 T H Hrf Hs. eapply Live_mono; [ | exact (SemC_live H) ].
  exact (limg_ap s T L Hrf Hs).
Qed.

Lemma SemC_rf_ap : forall L DT Sg n s D' n' S2 T, SemC L DT Sg n s D' n' S2 ->
  rf T -> ftv_typ T [<=] L -> rf (apT s T).
Proof.
  intros L DT Sg n s D' n' S2 T H Hrf Hs. apply rf_ap; [ exact Hrf | intros x Hx; exact (SemC_rf H x (Hs x Hx)) ].
Qed.

Lemma SemC_mono : forall L1 L2 DT Sg n s D' n' S2, L1 [<=] L2 ->
  SemC L2 DT Sg n s D' n' S2 -> SemC L1 DT Sg n s D' n' S2.
Proof.
  intros L1 L2 DT Sg n s D' n' S2 Hs (W & R & V).
  refine (conj (SemW_mono _ _ _ _ _ _ _ _ _ _ _ _ _ Hs (fun y Hy => Hy) W) (conj _ _)).
  - intros x Hx. exact (R x (Hs x Hx)).
  - eapply Live_mono; [ | exact V ]. intros y Hy. apply limg_in in Hy. apply limg_in.
    destruct Hy as (x & Hx & Hy). exists x. split; [ apply Hs; exact Hx | exact Hy ].
Qed.

Lemma SemC_weaken : forall L DT Sg Sg' n0 n1 s D' n' S2,
  n0 <= n1 -> SemC L DT Sg' n1 s D' n' S2 ->
  (forall x, x `in` L -> sT Sg' x = sT Sg x) ->
  SemC L DT Sg n0 s D' n' S2.
Proof.
  intros L DT Sg Sg' n0 n1 s D' n' S2 Hl (W & R & V) Ex.
  exact (conj (SemW_weaken _ _ _ _ _ _ _ _ _ _ _ _ _ Hl W Ex (fun q Hq => ltac:(exfalso; revert Hq; fsetdec))) (conj R V)).
Qed.

Lemma SemC_id : forall L DT Sg D n, Drow D -> DOk D n -> LOld n L -> Live PEv L D DT Sg ->
  SemC L DT Sg n sid D n Sg.
Proof.
  intros L DT Sg D n Hr Hd Ho HL.
  refine (conj (SemW_id _ _ _ _ _ _ _ _ Hd Hr Ho (fun a Ha => ltac:(exfalso; revert Ha; fsetdec)) (LvE_of_Live _ _ _ _ HL)) (conj _ _)).
  - intros x _. cbn [sT sid idt]. exact I.
  - eapply Live_mono; [ exact (limg_sid L) | exact HL ].
Qed.

(* A fresh atom of sort [k], sent to [U]. *)
Lemma SemC_fresh : forall L DT D Sg n k U, Drow D -> DOk D n -> LOld n L -> Live PEv L D DT Sg ->
  SemC L DT Sg n sid (upd D (ea n) k) (S n) (supd Sg (ea n) U).
Proof.
  intros L DT D Sg n k U Hr Hd Ho HL.
  refine (conj (SemW_fresh _ _ _ _ _ _ _ _ _ _ Hd Hr Ho (fun a Ha => ltac:(exfalso; revert Ha; fsetdec)) (LvE_of_Live _ _ _ _ HL)) (conj _ _)).
  - intros x _. cbn [sT sid idt]. exact I.
  - intros a Ha. pose proof (limg_sid L a Ha) as Ha'.
    assert (Hne : a <> ea n) by (intro E; exact (Ho a Ha' n (le_n n) E)).
    rewrite upd_other by exact Hne. rewrite supd_other by exact Hne. exact (HL a Ha').
Qed.

(* The step that ran past the fresh atom is a step from the old substitution. *)
Lemma SemC_unfresh : forall Ln DT Sg n U s D' n' S2, LOld n Ln ->
  SemC (Ln `union` {{ ea n }}) DT (supd Sg (ea n) U) (S n) s D' n' S2 ->
  SemC Ln DT Sg n s D' n' S2.
Proof.
  intros Ln DT Sg n U s D' n' S2 Ho H.
  refine (SemC_weaken Ln DT Sg (supd Sg (ea n) U) n (S n) s D' n' S2 (Nat.le_succ_diag_r n)
            (SemC_mono Ln _ DT _ _ s D' n' S2 _ H) _).
  - intros x Hx. fsetdec.
  - intros x Hx. apply supd_other. intro E. exact (Ho x Hx n (le_n n) E).
Qed.

Lemma limg_scompC : forall s s' L, (forall x, x `in` L -> rf (sT s x)) ->
  limg (scomp s' s) L [<=] limg s' (limg s L).
Proof.
  intros s s' L H y Hy. apply limg_in in Hy. destruct Hy as (x & Hx & Hy).
  change (y `in` ftv_typ (apT s' (sT s x))) in Hy.
  destruct (ftv_ap_rf s' _ y (H x Hx) Hy) as (z & Hz & Hyz).
  apply limg_in. exists z. split; [ apply limg_in; exists x; split; assumption | exact Hyz ].
Qed.

Lemma SemC_comp : forall L Lm DT Sg n s D1 n1 S1 s' D2 n2 S2,
  SemC L DT Sg n s D1 n1 S1 -> limg s L [<=] Lm ->
  SemC Lm DT S1 n1 s' D2 n2 S2 -> SemC L DT Sg n (scomp s' s) D2 n2 S2.
Proof.
  intros L Lm DT Sg n s D1 n1 S1 s' D2 n2 S2 H1 Hsub H2.
  pose proof (SemC_rf H1) as R1. pose proof (SemC_rf H2) as R2.
  assert (HT : limgT s L {} [<=] Lm) by (intros y Hy; apply Hsub; apply limgT_nil; exact Hy).
  assert (HR : limgR s L {} [<=] {}) by exact (limgR_rf s L R1).
  assert (Hrfc : forall x, x `in` L -> rf (sT (scomp s' s) x)).
  { intros x Hx. change (rf (apT s' (sT s x))). apply rf_ap; [ exact (R1 x Hx) | ].
    intros y Hy. apply R2. apply Hsub. apply limg_in. exists x. split; assumption. }
  refine (conj (SemW_comp _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (SemC_W H1) HT HR (SemC_W H2)) (conj Hrfc _)).
  eapply Live_mono; [ | exact (SemC_live H2) ].
  intros y Hy. apply (limg_mono s' _ _ Hsub). exact (limg_scompC s s' L R1 y Hy).
Qed.

(* The derivation's environment moved: the images of the live atoms read the same sorts. *)
Lemma SemC_env : forall L (Dg Dd : denv) Sg n s D' n' S2, SemC L Dg Sg n s D' n' S2 ->
  (forall x, x `in` limg s L -> forall c, c `in` ftv_typ (sT S2 x) -> Dd c = Dg c) ->
  (forall r, drk Dd r = drk Dg r) ->
  SemC L Dd Sg n s D' n' S2.
Proof.
  intros L Dg Dd Sg n s D' n' S2 H Hs Hr.
  pose proof (SemC_W H) as (Hd & Hw & (Sat & RL & Bnd & NN) & SI & F1 & F2 & Ok).
  pose proof (SemC_rf H) as R1. pose proof (limgR_rf s L R1) as HR.
  assert (HLG : LvE (limgT s L {}) (limgR s L {}) D' Dd S2).
  { refine (conj _ (conj _ (conj Bnd NN))).
    - intros a Ha. apply limgT_nil in Ha. eapply sat_loc; [ intros c Hc; exact (Hs a Ha c Hc) | intros r _; exact (Hr r) | exact (Sat a (proj2 (limgT_nil s L a) Ha)) ].
    - intros q Hq. exfalso. exact (proj1 (AtomSetFacts.empty_iff q) (HR q Hq)). }
  refine (conj (conj Hd (conj Hw (conj HLG (conj SI (conj F1 (conj F2 Ok)))))) (conj R1 _)).
  intros a Ha. destruct (SemC_live H a Ha) as [Hsat HP]. split; [ | exact HP ].
  eapply sat_loc; [ intros c Hc; exact (Hs a Ha c Hc) | intros r _; exact (Hr r) | exact Hsat ].
Qed.


(* The step's extension may change at atoms the step does not read. *)
Lemma SemC_agree : forall L DT Sg n s D' n' S2 S2', SemC L DT Sg n s D' n' S2 ->
  (forall y, y `in` limg s L -> sT S2' y = sT S2 y) ->
  SemC L DT Sg n s D' n' S2'.
Proof.
  intros L DT Sg n s D' n' S2 S2' H Hag.
  pose proof (SemC_W H) as (Hd & Hw & (Sat & RL & (Bt & Bq) & NN) & (Hl & Hx & Hq) & F1 & F2 & Ok).
  pose proof (SemC_rf H) as R1. pose proof (limgR_rf s L R1) as HR.
  assert (Hagt : forall y, y `in` limgT s L {} -> sT S2' y = sT S2 y)
    by (intros y Hy; apply Hag; apply limgT_nil; exact Hy).
  assert (Hfac : forall x, x `in` L -> apT S2' (sT s x) = apT S2 (sT s x)).
  { intros x Hx. apply apT_agree; [ exact (R1 x Hx) | ]. intros y Hy. apply Hag. apply limg_in. exists x. split; assumption. }
  refine (conj (conj Hd (conj Hw (conj _ (conj _ (conj _ (conj _ Ok)))))) (conj R1 _)).
  - refine (conj _ (conj _ (conj (conj _ _) _))).
    + intros a Ha. rewrite (Hagt a Ha). exact (Sat a Ha).
    + intros q Hq'. exfalso. exact (proj1 (AtomSetFacts.empty_iff q) (HR q Hq')).
    + intros a Ha. rewrite (Hagt a Ha). exact (proj1 (Bt a Ha)).
    + intros q Hq'. exfalso. exact (proj1 (AtomSetFacts.empty_iff q) (HR q Hq')).
    + intros a Ha. rewrite (Hagt a Ha). exact (NN a Ha).
  - refine (conj Hl (conj _ _)).
    + intros x Hx'. destruct (Hx x Hx') as (P & A & PS). refine (conj P (conj A _)).
      refine (proj1 (ps_agree S2 S2') _ P _ PS). intros y Hy. symmetry. apply Hag. apply limg_in. exists x. split; assumption.
    + intros q Hq'. exfalso. revert Hq'. fsetdec.
  - intros x Hx'. rewrite (Hfac x Hx'). exact (F1 x Hx').
  - intros q Hq'. exfalso. revert Hq'. fsetdec.
  - intros a Ha. destruct (SemC_live H a Ha) as [Hsat HP]. rewrite (Hag a Ha). exact (conj Hsat HP).
Qed.

(* A step followed by the identity step is the same step. *)
Lemma SemC_sid_after : forall L DT Sg n s D1 n1 S1,
  SemC L DT Sg n s D1 n1 S1 ->
  SemC L DT Sg n (scomp sid s) D1 n1 S1 /\ limg (scomp sid s) L [<=] limg s L.
Proof.
  intros L DT Sg n s D1 n1 S1 H. split.
  - exact (SemC_comp L (limg s L) DT Sg n s D1 n1 S1 sid D1 n1 S1 H (fun y Hy => Hy)
             (SemC_id (limg s L) DT S1 D1 n1 (SemC_Drow H) (SemC_DOk H) (SemC_old H) (SemC_live H))).
  - intros y Hy. apply (limg_sid (limg s L)). exact (limg_scompC s sid L (SemC_rf H) y Hy).
Qed.
