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
Require Import Goat.GoatInferW.
Require Import Goat.GoatHeld.
Require Import Goat.GoatCompleteHeld.
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

Lemma nil_in : forall q : atom, q `in` {} -> False.
Proof. intros q Hq. revert Hq. fsetdec. Qed.

Lemma LOld_nil : forall n, LOld n {}.
Proof. intros n a Ha. exfalso. exact (nil_in a Ha). Qed.

Lemma Drow_of_drk : forall D D', drk D' = drk D -> Drow D -> Drow D'.
Proof. intros D D' E H r. rewrite E. apply H. Qed.

Lemma SemC_weaken : forall L DT Sg Sg' n0 n1 s D' n' S2,
  n0 <= n1 -> SemC L DT Sg' n1 s D' n' S2 ->
  (forall x, x `in` L -> sT Sg' x = sT Sg x) ->
  SemC L DT Sg n0 s D' n' S2.
Proof.
  intros L DT Sg Sg' n0 n1 s D' n' S2 Hl (W & R & V) Ex.
  exact (conj (SemW_weaken _ _ _ _ _ _ _ _ _ _ _ _ _ Hl W Ex (fun q Hq => False_rect _ (nil_in q Hq))) (conj R V)).
Qed.

Lemma SemC_id : forall L DT Sg D n, Drow D -> DOk D n -> LOld n L -> Live PEv L D DT Sg ->
  SemC L DT Sg n sid D n Sg.
Proof.
  intros L DT Sg D n Hr Hd Ho HL.
  refine (conj (SemW_id _ _ _ _ _ _ _ _ Hd Hr Ho (LOld_nil n) (LvE_of_Live _ _ _ _ HL)) (conj _ _)).
  - intros x _. cbn [sT sid idt]. exact I.
  - eapply Live_mono; [ exact (limg_sid L) | exact HL ].
Qed.

(* A fresh atom of sort [k], sent to [U]. *)
Lemma SemC_fresh : forall L DT D Sg n k U, Drow D -> DOk D n -> LOld n L -> Live PEv L D DT Sg ->
  SemC L DT Sg n sid (upd D (ea n) k) (S n) (supd Sg (ea n) U).
Proof.
  intros L DT D Sg n k U Hr Hd Ho HL.
  refine (conj (SemW_fresh _ _ _ _ _ _ _ _ _ _ Hd Hr Ho (LOld_nil n) (LvE_of_Live _ _ _ _ HL)) (conj _ _)).
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
  refine (conj (SemW_comp evA evA L {} Lm {} DT Sg n s D1 n1 S1 s' D2 n2 S2 (SemC_W H1) HT HR (SemC_W H2)) (conj Hrfc _)).
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
  pose proof (SemC_W H) as (Hd & Hw & (Sat & RL & (Bt & Bq) & NN) & (Hl & HxS & HqS) & F1 & F2 & Ok).
  pose proof (SemC_rf H) as R1. pose proof (limgR_rf s L R1) as HR.
  assert (Hagt : forall y, y `in` limgT s L {} -> sT S2' y = sT S2 y)
    by (intros y Hy; apply Hag; apply limgT_nil; exact Hy).
  assert (Hfac : forall x, x `in` L -> apT S2' (sT s x) = apT S2 (sT s x)).
  { intros x Hx. apply apT_agree; [ exact (R1 x Hx) | ]. intros y Hy. apply Hag. apply limg_in. exists x. split; assumption. }
  refine (conj (conj Hd (conj Hw (conj _ (conj _ (conj _ (conj _ Ok)))))) (conj R1 _)).
  - refine (conj _ (conj _ (conj (conj _ _) _))).
    + intros a Ha. rewrite (Hagt a Ha). exact (Sat a Ha).
    + intros q Hq'. exfalso. exact (proj1 (AtomSetFacts.empty_iff q) (HR q Hq')).
    + intros a Ha. rewrite (Hagt a Ha). exact (Bt a Ha).
    + intros q Hq'. exfalso. exact (proj1 (AtomSetFacts.empty_iff q) (HR q Hq')).
    + intros a Ha. rewrite (Hagt a Ha). exact (NN a Ha).
  - refine (conj Hl (conj _ _)).
    + intros x Hx'. destruct (HxS x Hx') as (P & A & PS). refine (conj P (conj A _)).
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

(* ---- the unifier's step ---- *)

(* [unify_stepL_G] (GoatCompleteLiveRf.v) with the conversion plain and the
   step a [SemC]. *)
Lemma unify_stepC : forall DT D Sg L T1 T2 n,
  DOk D n -> Drow D -> LOld n L -> LEv L -> Live PEv L D DT Sg ->
  rf T1 -> rf T2 -> ftv_typ T1 [<=] L -> ftv_typ T2 [<=] L ->
  teq (apT Sg T1) (apT Sg T2) ->
  exists s D' n' S2,
    Stable (fun f => unify_coD f D T1 T2 n = Some (s, D', nil, n')) /\
    SemC L DT Sg n s D' n' S2 /\ Drow D'.
Proof.
  intros DT D Sg L T1 T2 n Hd Hrow Ho HLE HL R1 R2 S1 S2 Heq'.
  assert (HoE : LOld n {}) by (intros a Ha; exfalso; revert Ha; fsetdec).
  assert (HLG : LvE L {} D DT Sg) by exact (LvE_of_Live L D DT Sg HL).
  assert (Hfrv : forall T, rf T -> frv_typ T [<=] {}).
  { intros T H q Hq. exfalso. exact (proj1 (proj2 (proj2 (rf_facts T H))) q Hq). }
  pose proof (proj1 (rf_facts T1 R1)) as P1. pose proof (proj1 (rf_facts T2 R2)) as P2.
  destruct (unify_stepG evA evA DT D Sg L {} T1 T2 n Hd Hrow Ho HoE HLE LEv_empty HLG P1 P2
              S1 (Hfrv T1 R1) S2 (Hfrv T2 R2) (ps_rf Sg T1 R1) (ps_rf Sg T2 R2) Heq')
    as (s & D' & n' & S3 & St & Sem & [f0 Hf0] & Pk).
  destruct Pk as (Hl & Hd' & Ht' & Hk' & Fx & Fr & Cv).
  destruct (unify_tD_rf_drk f0 D T1 T2 n s D' n' (Hf0 f0 (le_n f0)) R1 R2) as [Hdrk _].
  assert (Hrfr : forall x, rf (sT (restrG L {} Sg) x)).
  { intros x. cbn [restrG sT]. destruct (AtomSetImpl.mem x L) eqn:E0;
      [ exact (proj2 (proj2 (HL x (AtomSetImpl.mem_2 E0)))) | exact I ]. }
  assert (Hfac : forall x, old n x -> apT S3 (sT s x) = sT (restrG L {} Sg) x).
  { intros x Hx. exact (teq_rf_eq _ _ (Hrfr x) (proj2 (proj2 (proj2 (Fx x Hx))))). }
  assert (Hrfs : forall x, old n x -> rf (sT s x) /\ forall y, y `in` ftv_typ (sT s x) -> rf (sT S3 y)).
  { intros x Hx. apply rf_back; [ exact (proj1 (Fx x Hx)) | rewrite (Hfac x Hx); exact (Hrfr x) ]. }
  pose proof (SemG_live _ _ _ _ _ _ _ _ _ _ _ Sem) as (Sat & _ & (Bt & _) & _).
  exists s, D', n', S3. refine (conj St (conj _ _)).
  - refine (conj (SemW_of_G _ _ _ _ _ _ _ _ _ _ _ Sem) (conj _ _)).
    + intros x Hx. exact (proj1 (Hrfs x (Ho x Hx))).
    + intros a Ha. destruct (proj1 (limg_in s L a) Ha) as (x & Hx & Hay).
      assert (Hal : a `in` limgT s L {}) by (apply limgT_in; left; exists x; split; assumption).
      refine (conj (Sat a Hal) (conj (Bt a Hal) _)).
      exact (proj2 (Hrfs x (Ho x Hx)) a Hay).
  - exact (Drow_of_drk D D' Hdrk Hrow).
Qed.

(* ---- the contexts ---- *)

Lemma GOk_GPsT : forall n Sg G, GOk n G -> GPsT Sg G.
Proof.
  intros n Sg G H. induction H as [|b G Hb _ IH]; constructor; [ | exact IH ].
  destruct Hb as (Hw & _ & Hrf & _).
  exact (conj Hw (conj (proj1 (rf_facts _ Hrf)) (ps_rf _ _ Hrf))).
Qed.

Lemma CIT_lookup : forall Pt D1 Sg G1 G x sc1,
  CIT Pt D1 Sg G1 G -> uniq G1 -> binds x sc1 G1 ->
  exists sc, lookup x G = Some sc /\
    ((exists T1 T, sc1 = sch_mono T1 /\ sc = sch_mono T /\ teq (apT Sg T) T1) \/ SchIT Pt D1 Sg sc1 sc).
Proof.
  intros Pt D1 Sg G1 G x sc1 H. induction H as [|[y s1] [z sc] G1 G [Hk Hrel] _ IH]; intros Hu Hb.
  - inversion Hb.
  - simpl in *. subst z. apply binds_cons_1 in Hb. destruct Hb as [[Hxy Hs]|Hb].
    + subst x sc1. exists sc. split.
      * cbn [lookup]. destruct (Atom.eq_dec y y); [ reflexivity | contradiction ].
      * exact Hrel.
    + inversion Hu; subst.
      destruct (IH ltac:(assumption) Hb) as (sc' & Ea & Eb). exists sc'.
      split; [ | exact Eb ].
      cbn [lookup]. destruct (Atom.eq_dec x y) as [->|_]; [ | exact Ea ].
      exfalso. apply binds_In in Hb. contradiction.
Qed.

Lemma CIT_dom_eq : forall Pt D1 Sg G1 G, CIT Pt D1 Sg G1 G -> dom G1 [=] dom G.
Proof. exact CIT_dom. Qed.

(* A scheme whose body is replaced by a convertible one, with the same
   quantifiers, is compared with the same instances. *)
Lemma sch_leT_conv : forall Pt D sa sb,
  s_tq sb = s_tq sa -> s_rq sb = s_rq sa -> s_sk sb = s_sk sa -> s_rk sb = s_rk sa ->
  teq (s_body sa) (s_body sb) -> sch_leT Pt D sa sb.
Proof.
  intros Pt D sa sb Htq Hrq Hsk Hrk Hb.
  destruct (proj1 er_inv _ _ Hb) as [E1 E2].
  assert (A : ftv_schE sb [=] ftv_schE sa) by (unfold ftv_schE; rewrite Htq, E1; reflexivity).
  assert (B : frv_schE sb [=] frv_schE sa) by (unfold frv_schE; rewrite Hrq, E2; reflexivity).
  split; [ rewrite A; reflexivity | split; [ rewrite B; reflexivity | ] ].
  intros D' _ _ T (st & sr & t1 & t2 & t3 & t4 & t5 & t6 & t7 & t8).
  exists (ap_typ st sr (s_body sb)). split.
  - exists st, sr. rewrite Htq, Hrq, Hsk, Hrk. exact (conj t1 (conj t2 (conj eq_refl (conj t4 (conj t5 (conj t6 (conj t7 t8))))))).
  - rewrite t3. exact (teq_ap _ _ st sr Hb).
Qed.

(* The atoms of the algorithm's step are not quantified: the atoms of the
   images of the live atoms are even, a quantified atom is odd. *)
Lemma sfix_img : forall L DT Sg n s D' n' S2 (q : atoms) x,
  SemC L DT Sg n s D' n' S2 -> LEv L -> (forall a, a `in` q -> od a) -> x `in` L ->
  apT (sfix q S2) (sT s x) = apT S2 (sT s x).
Proof.
  intros L DT Sg n s D' n' S2 q x H HL Hq Hx.
  apply apT_agree; [ exact (SemC_rf H x Hx) | ]. intros c Hc. apply sfix_out. intro Hcq.
  assert (Hcl : c `in` limg s L) by (apply limg_in; exists x; split; assumption).
  exact (ev_od c (SemC_ev L DT Sg n s D' n' S2 H HL c Hcl) (Hq c Hcq)).
Qed.

Lemma sfix_step_teq : forall L DT Sg n s D' n' S2 sc,
  SemC L DT Sg n s D' n' S2 -> LEv L -> SOk n sc -> ftv_sch sc [<=] L ->
  forall y, y `in` ftv_typ (s_body sc) ->
    teq (sT (sfix (s_tq sc) Sg) y) (apT (sfix (s_tq sc) S2) (sT s y)).
Proof.
  intros L DT Sg n s D' n' S2 sc H HL Hok Hl y Hy.
  pose proof Hok as (Hw & _). pose proof (proj1 Hw) as Hq.
  destruct (in_dec_set y (s_tq sc)) as [Hyq|Hyq].
  - rewrite (OkS_fix_tq s sc (SemC_OkS H) Hw y Hyq), apT_Var, !sfix_in by exact Hyq.
    apply teq_refl.
  - assert (Hf : y `in` ftv_sch sc) by (unfold ftv_sch; apply AtomSetFacts.diff_iff; split; assumption).
    rewrite sfix_out by exact Hyq. rewrite (sfix_img L DT Sg n s D' n' S2 (s_tq sc) y H HL Hq (Hl y Hf)).
    exact (SemC_F H y (Hl y Hf)).
Qed.

Lemma SOk_apSC : forall L DT Sg n s D' n' S2 sc, SemC L DT Sg n s D' n' S2 ->
  SOk n sc -> ftv_sch sc [<=] L ->
  SOk n' (apS s sc) /\ ftv_sch (apS s sc) [<=] limg s L.
Proof.
  intros L DT Sg n s D' n' S2 sc H Hok Hl.
  pose proof Hok as (Hw & Hr & Hrf & Hold).
  assert (Hftv : ftv_sch (apS s sc) [<=] limg s L).
  { intros a Ha. unfold ftv_sch in Ha. cbn [apS s_body s_tq] in Ha.
    apply AtomSetFacts.diff_iff in Ha. destruct Ha as [Ha Hn].
    destruct (ftv_ap_rf s _ a Hrf Ha) as (x & Hx & Hax).
    destruct (in_dec_set x (s_tq sc)) as [Hxq|Hxq].
    - rewrite (OkS_fix_tq s sc (SemC_OkS H) Hw x Hxq) in Hax. simpl in Hax.
      apply AtomSetFacts.singleton_iff in Hax. subst. contradiction.
    - assert (Hf : x `in` ftv_sch sc) by (unfold ftv_sch; apply AtomSetFacts.diff_iff; split; assumption).
      apply limg_in. exists x. split; [ exact (Hl x Hf) | exact Hax ]. }
  refine (conj (conj (WfSch_ap s sc (SemC_OkS H) Hw) (conj Hr (conj _ _))) Hftv).
  - cbn [apS s_body]. apply rf_ap; [ exact Hrf | ]. intros x Hx.
    destruct (in_dec_set x (s_tq sc)) as [Hxq|Hxq].
    + rewrite (OkS_fix_tq s sc (SemC_OkS H) Hw x Hxq). exact I.
    + assert (Hf : x `in` ftv_sch sc) by (unfold ftv_sch; apply AtomSetFacts.diff_iff; split; assumption).
      exact (SemC_rf H x (Hl x Hf)).
  - intros a Ha. exact (SemC_old H a (Hftv a Ha)).
Qed.

(* The run's step on the context: the derivation's bindings are still
   comparable with the algorithm's, read at the extension. *)
Lemma CI_stepW : forall L DT Sg n s D' n' S2 G1 G,
  SemC L DT Sg n s D' n' S2 -> LEv L ->
  CIT PEv DT Sg G1 G -> GOk n G -> GLive L G ->
  CIT PEv DT S2 G1 (apC s G) /\ GOk n' (apC s G) /\ GLive (limg s L) (apC s G).
Proof.
  intros L DT Sg n s D' n' S2 G1 G H HL HC HG HGL.
  rewrite apC_map.
  induction HC as [|[x s1] [y sc] G1 G [Hk Hrel] _ IH]; [ refine (conj _ (conj _ _)); constructor | ].
  inversion HG as [|b G' Hsc HG' Eb]; subst.
  inversion HGL as [|b2 G2 HL2 HL' Eb2]; subst. simpl in *. subst y.
  destruct (IH HG' HL') as (IC & IG & ILv).
  destruct (SOk_apSC L DT Sg n s D' n' S2 sc H Hsc HL2) as (Hso & Hfl).
  refine (conj _ (conj _ _)).
  - constructor; [ | exact IC ]. simpl. split; [ reflexivity | ].
    destruct Hrel as [(T1 & T & E1 & E2 & Ht)|Hsch].
    + left. rewrite E2 in Hsc. pose proof (SOk_mono_inv _ _ Hsc) as HT'.
      rewrite E2 in HL2. cbn [snd] in HL2.
      exists T1, (apT s T). split; [ exact E1 | split; [ rewrite E2; reflexivity | ] ].
      eapply teq_trans; [ | exact Ht ]. apply teq_sym.
      exact (SemC_factor L DT Sg n s D' n' S2 T H (proj1 HT')
               (fun a Ha => HL2 a (proj2 (ftv_sch_mono T a) Ha))).
    + right. unfold SchIT in *. change (s_tq (apS s sc)) with (s_tq sc).
      refine (sch_leT_trans _ _ _ _ _ Hsch _).
      apply sch_leT_conv; try reflexivity.
      cbn [apS s_body]. pose proof Hsc as (Hw & Hr & Hrf & Hold).
      apply ap_factor.
      * intros z Hz. exact (sfix_step_teq L DT Sg n s D' n' S2 sc H HL Hsc HL2 z Hz).
      * intros q Hq. exfalso. exact (proj1 (proj2 (proj2 (rf_facts _ Hrf))) q Hq).
  - constructor; [ exact Hso | exact IG ].
  - constructor; [ exact Hfl | ]. eapply GLive_mono; [ | exact ILv ]. intros z Hz. exact Hz.
Qed.

(* The substitution may change off the live atoms. *)
Lemma CIT_agree : forall Pt D1 Sg Sg' G1 G L n, CIT Pt D1 Sg G1 G -> GOk n G -> GLive L G ->
  (forall a, a `in` L -> sT Sg' a = sT Sg a) -> CIT Pt D1 Sg' G1 G.
Proof.
  intros Pt D1 Sg Sg' G1 G L n H. induction H as [|[x s1] [y s] G1 G [Hk Hrel] _ IH]; intros HO HG Hag.
  - constructor.
  - inversion HO as [|b G' Hsc HO' Eb]; subst.
    inversion HG as [|b2 G2 HL2 HG' Eb2]; subst. simpl in *. subst y.
    constructor; [ | exact (IH HO' HG' Hag) ].
    simpl. split; [ reflexivity | ]. destruct Hrel as [(T1 & T & E1 & E2 & Ht)|Hs].
    + left. exists T1, T. split; [ exact E1 | split; [ exact E2 | ] ].
      rewrite E2 in Hsc. pose proof (SOk_mono_inv _ _ Hsc) as HT.
      rewrite E2 in HL2. cbn [snd] in HL2.
      rewrite (apT_agree Sg' Sg T (proj1 HT) (fun a Ha => Hag a (HL2 a (proj2 (ftv_sch_mono T a) Ha)))). exact Ht.
    + right. unfold SchIT in *. rewrite (apS_sfix_agree n L s Sg Sg' Hsc HL2 Hag). exact Hs.
Qed.

(* ---- what a run hands the next premise ---- *)

Lemma next_factsW : forall Dd Gd Sg n L s D1 n1 S1 T G,
  LOld n L -> LEv L -> SemC L Dd Sg n s D1 n1 S1 -> TOk n1 T -> EvT T ->
  Live PEv (ftv_typ T) D1 Dd S1 ->
  GOk n G -> GLive L G -> CIT PEv Dd Sg Gd G ->
  LOld n1 (lnext s L T) /\ LEv (lnext s L T) /\ Live PEv (lnext s L T) D1 Dd S1 /\ GOk n1 (apC s G) /\
  GLive (lnext s L T) (apC s G) /\ CIT PEv Dd S1 Gd (apC s G).
Proof.
  intros Dd Gd Sg n L s D1 n1 S1 T G Ho HLE Hs HT HE Lv HG HL HC.
  destruct (CI_stepW L Dd Sg n s D1 n1 S1 Gd G Hs HLE HC HG HL) as (HC1 & HG1 & HL1).
  refine (conj (LOld_union _ _ _ (SemC_old Hs) (LOld_ftv _ _ HT))
            (conj (LEv_next s L T (SemC_OkS Hs) HLE HE) (conj _ (conj HG1 (conj _ HC1))))).
  - exact (Live_union _ _ _ _ _ _ (SemC_live Hs) Lv).
  - exact (GLive_mono _ _ _ (limg_lnext s L T) HL1).
Qed.

(* ---- the bound ---- *)

Lemma AvoidC_limg : forall B L DT Sg n s D' n' S2,
  AvoidE B L {} Sg -> SemC L DT Sg n s D' n' S2 -> AvoidE B (limg s L) {} S2.
Proof.
  intros B L DT Sg n s D' n' S2 HA Hs.
  pose proof (AvoidE_limg B evA evA L {} DT Sg n s D' n' S2 HA (SemC_W Hs)) as H.
  eapply AvoidE_sub; [ | | exact H ].
  - intros y Hy. apply limgT_nil. exact Hy.
  - intros y Hy. exfalso. revert Hy. fsetdec.
Qed.

Lemma AvoidC_next : forall B B' L DT Sg n s D1 n1 S1 T Tp,
  AvoidE B L {} Sg -> SemC L DT Sg n s D1 n1 S1 -> rf T -> teq (apT S1 T) Tp ->
  B [<=] B' -> ftv_typ Tp [<=] B' -> AvoidE B' (lnext s L T) {} S1.
Proof.
  intros B B' L DT Sg n s D1 n1 S1 T Tp HA Hs HT Heq Hb HTp.
  pose proof (AvoidE_next B B' evA evA L {} DT Sg n s D1 n1 S1 T Tp HA (SemC_W Hs)
                (proj1 (rf_facts T HT)) (ps_rf S1 T HT) Heq Hb
                (fun y Hy => HTp y (proj1 (proj1 er_sub Tp) y Hy))) as H.
  eapply AvoidE_sub; [ | | exact H ].
  - intros y Hy. unfold lnext in Hy. unfold lnT. apply AtomSetFacts.union_iff in Hy. apply AtomSetFacts.union_iff.
    destruct Hy as [Hy|Hy]; [ left; apply limgT_nil; exact Hy | right; exact Hy ].
  - intros y Hy. exfalso. revert Hy. fsetdec.
Qed.

Lemma AvoidC_fresh : forall B n L Sg U, LOld n L -> AvoidE B L {} Sg -> ftv_typ U [<=] B ->
  AvoidE B (L `union` {{ ea n }}) {} (supd Sg (ea n) U).
Proof.
  intros B n L Sg U Ho HA HU. apply AvoidE_fresh; [ exact Ho | exact HA | ].
  intros y Hy. apply HU. exact (proj1 (proj1 er_sub U) y Hy).
Qed.

(* ---- what a run ends with ---- *)

(* The induction's conclusion: the run succeeds from some fuel on holding no
   equation, its step is a [SemC], the type it returns is record-free over
   atoms below the supply, and it is convertible to the derivation's under the
   extension. *)
Definition DoneW (L : atoms) (D1 : denv) (G : ctx) (e : exp) (D : denv) (n : nat)
  (Sg : sub) (T1 : typ) : Prop :=
  exists s D' n' S2 T e',
    Stable (fun f => infer true f D G e n = Some (s, D', T, n', e', nil)) /\
    SemC L D1 Sg n s D' n' S2 /\ TOk n' T /\ EvT T /\ Live PEv (ftv_typ T) D' D1 S2 /\
    teq (apT S2 T) T1 /\ is_gen_value e' = is_gen_value e /\ let_open e' = let_open e.

(* The facts [DoneG] (GoatCompleteLive.v) states of the type. *)
Lemma DoneW_frag : forall n' S2 T, TOk n' T ->
  pf T /\ atT n' T /\ ps S2 T /\ HOkC S2 n' nil.
Proof.
  intros n' S2 T [Hrf Hold]. refine (conj (proj1 (rf_facts T Hrf)) (conj _ (conj (ps_rf S2 T Hrf) (Forall_nil _)))).
  split; [ exact Hold | intros q Hq; exfalso; exact (proj1 (proj2 (proj2 (rf_facts T Hrf))) q Hq) ].
Qed.
