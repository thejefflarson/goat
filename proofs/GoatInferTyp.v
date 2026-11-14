(* Typing is closed under the substitutions algorithm W builds, and under
   renaming the variable a binder opens with (the cofinite rules of [typing]
   quantify over every fresh name; the algorithm picks one). *)

Require Import Metalib.Metatheory.
Require Import Goat.Goat_ott.
Require Import Goat.GoatProofs.
Require Import Goat.GoatRows.
Require Import Goat.GoatDefs.
Require Import Goat.GoatMeta.
Require Import Goat.GoatSubst.
Require Import Goat.GoatHM.
Require Import Goat.GoatSound.
Require Import Goat.GoatInfer.
Require Import Goat.GoatInferSub.
Require Import Coq.Lists.List.
Import ListNotations.

Lemma ftv_ctx_has : forall a G, a `in` ftv_ctx G ->
  exists x sc, binds x sc G /\ a `in` ftv_sch sc.
Proof.
  intros a. induction G as [|[y sy] G IH]; intros H; simpl in H; [fsetdec|].
  apply AtomSetFacts.union_iff in H. destruct H as [H|H].
  - exists y, sy. split; [apply binds_cons_2; reflexivity | exact H].
  - destruct (IH H) as [x [sc [Hb Hin]]]. exists x, sc.
    split; [apply binds_cons_3; exact Hb | exact Hin].
Qed.

Lemma frv_ctx_has : forall a G, a `in` frv_ctx G ->
  exists x sc, binds x sc G /\ a `in` frv_sch sc.
Proof.
  intros a. induction G as [|[y sy] G IH]; intros H; simpl in H; [fsetdec|].
  apply AtomSetFacts.union_iff in H. destruct H as [H|H].
  - exists y, sy. split; [apply binds_cons_2; reflexivity | exact H].
  - destruct (IH H) as [x [sc [Hb Hin]]]. exists x, sc.
    split; [apply binds_cons_3; exact Hb | exact Hin].
Qed.

(* Every instance of a scheme maps to an instance of the substituted scheme. *)
Lemma sch_subst_apS : forall s sc, OkS s -> WfSch sc ->
  sch_subst (sT s) (sR s) sc (apS s sc).
Proof.
  intros s sc Hs (Hq & Hr & Hf & Hfr) W [pt [pr [Hpt [Hpr HW]]]].
  pose proof Hs as Hs0.
  destruct Hs as [_ [Ht [Hrw [Hfx Hfxr]]]].
  set (pt' := fun a => if AtomSetImpl.mem a (s_tq sc)
                       then ap_typ (sT s) (sR s) (pt a) else typ_Var a).
  set (pr' := fun r => if AtomSetImpl.mem r (s_rq sc)
                       then ap_row (sT s) (sR s) (pr r) else row_Var r).
  (* an even variable is neither quantified type variable nor row variable *)
  assert (Hpt'ev : forall c, ev c -> pt' c = typ_Var c).
  { intros c Hc. unfold pt'.
    destruct (AtomSetImpl.mem c (s_tq sc)) eqn:Em; [|reflexivity].
    apply AtomSetFacts.mem_iff in Em. exfalso. exact (not_ev_od c (Hq c Em) Hc). }
  assert (Hpr'ev : forall c, ev c -> pr' c = row_Var c).
  { intros c Hc. unfold pr'.
    destruct (AtomSetImpl.mem c (s_rq sc)) eqn:Em; [|reflexivity].
    apply AtomSetFacts.mem_iff in Em. exfalso. exact (not_ev_od c (Hr c Em) Hc). }
  exists pt', pr'. split; [|split].
  - intros a Ha. cbn [apS s_tq] in Ha. unfold pt'.
    destruct (AtomSetImpl.mem a (s_tq sc)) eqn:Em;
      [ apply AtomSetFacts.mem_iff in Em; contradiction | reflexivity ].
  - intros r Hr0. cbn [apS s_rq] in Hr0. unfold pr'.
    destruct (AtomSetImpl.mem r (s_rq sc)) eqn:Em;
      [ apply AtomSetFacts.mem_iff in Em; contradiction | reflexivity ].
  - cbn [apS s_body]. rewrite HW. unfold apT. rewrite !ap_typ_comp.
    apply ap_typ_ext.
    + intros a Ha. unfold tcomp.
      destruct (AtomSetImpl.mem a (s_tq sc)) eqn:Em.
      * pose proof Em as Em0. apply AtomSetFacts.mem_iff in Em.
        rewrite (Hfx a (not_ev_od a (Hq a Em))). cbn [ap_typ].
        unfold pt'. rewrite Em0. reflexivity.
      * apply AtomSetFacts.not_mem_iff in Em.
        assert (Hin : a `in` ftv_sch sc)
          by (unfold ftv_sch; apply AtomSetFacts.diff_iff; auto).
        rewrite (Hpt a Em). cbn [ap_typ].
        symmetry. apply ap_typ_fix.
        -- intros c Hc. apply Hpt'ev. exact (proj1 (Ht a (Hf a Hin)) c Hc).
        -- intros c Hc. apply Hpr'ev. exact (proj2 (Ht a (Hf a Hin)) c Hc).
    + intros r Hr1. unfold rcomp.
      destruct (AtomSetImpl.mem r (s_rq sc)) eqn:Em.
      * pose proof Em as Em0. apply AtomSetFacts.mem_iff in Em.
        rewrite (Hfxr r (not_ev_od r (Hr r Em))). cbn [ap_row].
        unfold pr'. rewrite Em0. reflexivity.
      * apply AtomSetFacts.not_mem_iff in Em.
        assert (Hin : r `in` frv_sch sc)
          by (unfold frv_sch; apply AtomSetFacts.diff_iff; auto).
        rewrite (Hpr r Em). cbn [ap_row].
        symmetry. apply ap_row_fix.
        -- intros c Hc. apply Hpt'ev. exact (proj1 (Hrw r (Hfr r Hin)) c Hc).
        -- intros c Hc. apply Hpr'ev. exact (proj2 (Hrw r (Hfr r Hin)) c Hc).
Qed.

Lemma tr_compat_apC : forall s G, OkS s -> WfCtx G ->
  tr_compat (sT s) (sR s) G (apC s G).
Proof.
  intros s G Hs [Hu Hw].
  destruct Hs as [[A Hsup] [Ht [Hrw [Hfx Hfxr]]]].
    assert (Hct : forall a, a `in` ftv_ctx G -> ev a ->
              ftv_typ (sT s a) [<=] ftv_ctx (apC s G) /\ frv_typ (sT s a) [<=] frv_ctx (apC s G)).
    { intros a Ha Hev. destruct (ftv_ctx_has _ _ Ha) as [x [sc [Hb Hin]]].
      pose proof (Hw _ _ Hb) as (Hq & Hr & Hf & Hfr).
      assert (Hbs := binds_apC s _ _ _ Hb).
      pose proof (binds_ftv_sch _ _ _ Hbs) as Hsub1.
      pose proof (binds_frv_sch _ _ _ Hbs) as Hsub2.
      assert (Hain : a `in` ftv_typ (s_body sc)) by (unfold ftv_sch in Hin; fsetdec).
      assert (Haq : a `notin` s_tq sc) by (unfold ftv_sch in Hin; fsetdec).
      split.
      - intros c Hc. apply Hsub1. unfold ftv_sch. apply AtomSetFacts.diff_iff. split.
        + cbn [apS s_body]. unfold apT. eapply ftv_ap_in1; eauto.
        + cbn [apS s_tq]. intro Hcq. exact (not_ev_od c (Hq c Hcq) (proj1 (Ht a Hev) c Hc)).
      - intros c Hc. apply Hsub2. unfold frv_sch. apply AtomSetFacts.diff_iff. split.
        + cbn [apS s_body]. unfold apT. eapply frv_ap_in1; eauto.
        + cbn [apS s_rq]. intro Hcq. exact (not_ev_od c (Hr c Hcq) (proj2 (Ht a Hev) c Hc)). }
    assert (Hcr : forall r, r `in` frv_ctx G -> ev r ->
              ftv_row (sR s r) [<=] ftv_ctx (apC s G) /\ frv_row (sR s r) [<=] frv_ctx (apC s G)).
    { intros r Hr0 Hev. destruct (frv_ctx_has _ _ Hr0) as [x [sc [Hb Hin]]].
      pose proof (Hw _ _ Hb) as (Hq & Hr & Hf & Hfr).
      assert (Hbs := binds_apC s _ _ _ Hb).
      pose proof (binds_ftv_sch _ _ _ Hbs) as Hsub1.
      pose proof (binds_frv_sch _ _ _ Hbs) as Hsub2.
      assert (Hrin : r `in` frv_typ (s_body sc)) by (unfold frv_sch in Hin; fsetdec).
      assert (Hrq : r `notin` s_rq sc) by (unfold frv_sch in Hin; fsetdec).
      split.
      - intros c Hc. apply Hsub1. unfold ftv_sch. apply AtomSetFacts.diff_iff. split.
        + cbn [apS s_body]. unfold apT. eapply ftv_ap_in2; eauto.
        + cbn [apS s_tq]. intro Hcq. exact (not_ev_od c (Hq c Hcq) (proj1 (Hrw r Hev) c Hc)).
      - intros c Hc. apply Hsub2. unfold frv_sch. apply AtomSetFacts.diff_iff. split.
        + cbn [apS s_body]. unfold apT. eapply frv_ap_in2; eauto.
        + cbn [apS s_rq]. intro Hcq. exact (not_ev_od c (Hr c Hcq) (proj2 (Hrw r Hev) c Hc)). }
    (* the atoms of a well-formed context's free sets are even *)
    assert (Hevc : forall a, a `in` ftv_ctx G -> ev a).
    { intros a Ha. destruct (ftv_ctx_has _ _ Ha) as [x [sc [Hb Hin]]].
      exact ((proj1 (proj2 (proj2 (Hw _ _ Hb)))) a Hin). }
    assert (Hevr : forall r, r `in` frv_ctx G -> ev r).
    { intros r Ha. destruct (frv_ctx_has _ _ Ha) as [x [sc [Hb Hin]]].
      exact ((proj2 (proj2 (proj2 (Hw _ _ Hb)))) r Hin). }
    unfold tr_compat. repeat split.
    + intros a Ha. exact (proj1 (Hct a Ha (Hevc a Ha))).
    + intros a Ha. exact (proj2 (Hct a Ha (Hevc a Ha))).
    + intros r Hr0. exact (proj1 (Hcr r Hr0 (Hevr r Hr0))).
    + intros r Hr0. exact (proj2 (Hcr r Hr0 (Hevr r Hr0))).
Qed.

Lemma typing_ap : forall s G e T,
  OkS s -> WfCtx G -> typing G e T -> typing (apC s G) e (apT s T).
Proof.
  intros s G e T Hs [Hu Hw] Hty.
  pose proof Hs as Hs0.
  destruct Hs as [[A Hsup] [Ht [Hrw [Hfx Hfxr]]]].
  apply (proj1 typing_tsubst_gen_mut G e T Hty (sT s) (sR s) (apC s G) A).
  - apply uniq_apC; exact Hu.
  - intros x sc Hb. exists (apS s sc). split.
    + apply binds_apC; exact Hb.
    + apply sch_subst_apS; [exact Hs0 | exact (Hw _ _ Hb)].
  - exact Hsup.
  - apply tr_compat_apC; [ exact Hs0 | exact (conj Hu Hw) ].
Qed.
