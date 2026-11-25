(* Completeness of algorithm W, stage 7.9: [ctyping] up to equivalent
   environments (docs/design/phase7-proof-plan.md).

   [ctyping Av D G e T] mentions its kinding environment, its context and the
   avoid set through quantities that are equal only up to a pointwise or set
   equality: [ext D V k] for [V] and [V'] with the same members, [gen] over two
   contexts whose schemes agree up to their quantifier sets ([sch_equiv]).  The
   conversion of GoatCompleteConv.v needs a [let] of a value with nothing
   generalized, whose premises hold at the environment and context the
   monomorphic derivation has; [ctyping_equiv] moves a derivation across
   [denv_eq], [ctx_equiv] and an avoid set equal as a set.

   Axiom- and admit-free. *)

Require Import Metalib.Metatheory.
Require Import Goat.Goat_ott.
Require Import Goat.GoatRows.
Require Import Goat.GoatDefs.
Require Import Goat.GoatSubst.
Require Import Goat.GoatMeta.
Require Import Goat.GoatInfer.
Require Import Goat.GoatInferSub.
Require Import Goat.GoatCompleteRf.
Require Import Goat.GoatCompleteMono.
Require Import Goat.GoatCompleteNf.
Require Import Goat.GoatCompleteCore.
Require Import Stdlib.Lists.List.
Import ListNotations.

Lemma instP_equiv : forall D D' T s s', instP D T s -> sch_equiv s s' -> denv_eq D D' -> instP D' T s'.
Proof.
  intros D D' T s s' (st & sr & H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8) (Htq & Hrq & Hbody & Hsk & Hrk) HD.
  exists st, sr.
  refine (conj _ (conj _ (conj _ (conj _ (conj _ (conj H6 (conj _ _))))))).
  - intros a Ha. apply H1. intros Hq. apply Ha. apply Htq. exact Hq.
  - intros r Hr. apply H2. intros Hq. apply Hr. apply Hrq. exact Hq.
  - rewrite <- Hbody. exact H3.
  - intros a Ha. assert (Hs : a `in` s_tq s) by (apply Htq; exact Ha).
    rewrite <- (Hsk a Hs). exact (sat_pw _ _ _ _ HD (H4 a Hs)).
  - intros r Hr. assert (Hs : r `in` s_rq s) by (apply Hrq; exact Hr).
    rewrite <- (Hrk r Hs). exact (rkok_pw _ _ _ _ HD (H5 r Hs)).
  - intros a Ha. apply H7. apply Htq. exact Ha.
  - intros r Hr. apply H8. apply Hrq. exact Hr.
Qed.

Lemma atc_equiv : forall G G', ctx_equiv G G' -> atc G [=] atc G'.
Proof.
  intros G G' H. unfold atc.
  assert (E1 : ftv_ctx G [=] ftv_ctx G') by (intro z; apply (ctx_equiv_Ftv _ _ z H)).
  assert (E2 : frv_ctx G [=] frv_ctx G') by (intro z; apply (ctx_equiv_Frv _ _ z H)).
  fsetdec.
Qed.

Lemma ctyping_equiv : forall Av D G e T, ctyping Av D G e T ->
  forall Av' D' G', Av' [=] Av -> denv_eq D D' -> ctx_equiv G G' -> ctyping Av' D' G' e T.
Proof.
  intros Av D G e T H. induction H; intros Av' D' G' HA HD HG;
    pose proof (atc_equiv _ _ HG) as Hatc; pose proof (ctx_equiv_dom _ _ HG) as Hdom;
    pose proof (ctx_equiv_uniq _ _ HG) as Hun.
  - destruct (ctx_equiv_binds _ _ _ _ HG H0) as (s' & Hb & Hse).
    pose proof Hse as (Htq & Hrq & _).
    eapply C_Var; [ exact (Hun H) | exact Hb | | exact (instP_equiv _ _ _ _ _ H2 Hse HD) ].
    rewrite <- Hrq. exact H1.
  - apply C_Num; [ exact (Hun H) | exact (sat_pw _ _ _ _ HD H0) | exact H1 ].
  - apply C_Dec. exact (Hun H).
  - apply C_True. exact (Hun H).
  - apply C_False. exact (Hun H).
  - apply C_Unit. exact (Hun H).
  - apply C_Str. exact (Hun H).
  - apply C_Abs; [ exact H | ]. intros x Hx.
    refine (H1 x _ _ _ _ _ HD (ctx_equiv_cons _ _ _ _ _ (sch_equiv_refl _) HG)); [ fsetdec | ].
    unfold bg. fsetdec.
  - apply C_App with (T1 := T1); [ exact H | | ].
    + refine (IHctyping1 _ _ _ _ HD HG). unfold bg. fsetdec.
    + refine (IHctyping2 _ _ _ _ HD HG). unfold bg. fsetdec.
  - apply C_If.
    + refine (IHctyping1 _ _ _ _ HD HG). unfold bg. fsetdec.
    + refine (IHctyping2 _ _ _ _ HD HG). unfold bg. fsetdec.
    + refine (IHctyping3 _ _ _ _ HD HG). unfold bg. fsetdec.
  - eapply C_ToFloat; [ | exact (sat_pw _ _ _ _ HD H0) | exact H1 ].
    refine (IHctyping _ _ _ _ HD HG). unfold bg. fsetdec.
  - apply C_Arith with (A := A); [ exact H | exact (sat_pw _ _ _ _ HD H0) | exact H1 | | ].
    + refine (IHctyping1 _ _ _ _ HD HG). unfold bg. fsetdec.
    + refine (IHctyping2 _ _ _ _ HD HG). unfold bg. fsetdec.
  - apply C_Cmp with (A := A); [ exact H | exact (sat_pw _ _ _ _ HD H0) | exact H1 | | ].
    + refine (IHctyping1 _ _ _ _ HD HG). unfold bg. fsetdec.
    + refine (IHctyping2 _ _ _ _ HD HG). unfold bg. fsetdec.
  - apply C_LetMono with (T1 := T1); [ exact H | | ].
    + refine (IHctyping _ _ _ _ HD HG). unfold bg. fsetdec.
    + intros x Hx.
      refine (H2 x _ _ _ _ _ HD (ctx_equiv_cons _ _ _ _ _ (sch_equiv_refl _) HG)); [ fsetdec | ].
      unfold bg. fsetdec.
  - assert (HP : ctx_equiv (pin_ctx Tm Gd) (pin_ctx Tm G')) by (apply ctx_equiv_cons; [ apply sch_equiv_refl | exact HG ]).
    assert (HV : AtomSetImpl.diff (ftv_typ T1) (ftv_ctx (pin_ctx Tm Gd))
                 [=] AtomSetImpl.diff (ftv_typ T1) (ftv_ctx (pin_ctx Tm G'))).
    { assert (E : ftv_ctx (pin_ctx Tm Gd) [=] ftv_ctx (pin_ctx Tm G')) by (intro z; apply (ctx_equiv_Ftv _ _ z HP)).
      rewrite E. reflexivity. }
    assert (HVr : AtomSetImpl.diff (frv_typ T1) (frv_ctx (pin_ctx Tm Gd))
                  [=] AtomSetImpl.diff (frv_typ T1) (frv_ctx (pin_ctx Tm G'))).
    { assert (E : frv_ctx (pin_ctx Tm Gd) [=] frv_ctx (pin_ctx Tm G')) by (intro z; apply (ctx_equiv_Frv _ _ z HP)).
      rewrite E. reflexivity. }
    assert (Hbg : bg Av' G' T2 [=] bg Av Gd T2) by (unfold bg; fsetdec).
    eapply C_Let with (k := k) (rk := rk) (Tm := Tm); [ exact H | exact H0 | | | | ].
    + intros Hl a Ha. apply H1; [ exact Hl | apply HV; exact Ha ].
    + intros a Ha. destruct (H2 a (proj2 (HV a) Ha)) as [Hev Hn]. split; [ exact Hev | ]. rewrite Hbg. exact Hn.
    + refine (IHctyping _ _ _ Hbg _ HG).
      apply denv_eq_trans with (D2 := extr (ext D' (AtomSetImpl.diff (ftv_typ T1) (ftv_ctx (pin_ctx Tm Gd))) k)
                                           (AtomSetImpl.diff (frv_typ T1) (frv_ctx (pin_ctx Tm Gd))) rk).
      * apply extr_pw. apply ext_pw. exact HD.
      * apply denv_eq_trans with (D2 := extr (ext D' (AtomSetImpl.diff (ftv_typ T1) (ftv_ctx (pin_ctx Tm G'))) k)
                                             (AtomSetImpl.diff (frv_typ T1) (frv_ctx (pin_ctx Tm Gd))) rk).
        -- apply extr_pw. apply ext_set_eq_d. exact HV.
        -- apply extr_set_eq. exact HVr.
    + intros x Hx.
      refine (H5 x _ _ _ _ _ HD _); [ fsetdec | exact Hbg | ].
      apply ctx_equiv_cons; [ exact (gen_ctx_equiv _ _ _ _ _ HP) | exact HG ].
  - eapply C_Conv; [ | eapply teqD_pw; [ exact HD | exact H0 ] ].
    refine (IHctyping _ _ _ _ HD HG). unfold bg. fsetdec.
Qed.
