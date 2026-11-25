(* Completeness of algorithm W, stage 7.8g: the core constructs on [SemC]
   (docs/design/phase7-proof-plan.md).

   L3 for the constructs whose types are base types, variables and arrows:
   variables, constants, [program], a call, [if], the operators, a comparison,
   [float(e)], and [let] (of a value, which generalizes, and of anything else,
   which does not).  A derivation [ctyping Av D1 G1 e T1] of one of them
   (GoatCompleteCore.v), a context [G] of the algorithm that [G1] is compared
   with ([CIT], GoatCompleteCtxT.v), live atoms [L] and a substitution [Sg]
   that respects the sorts on [L] ([Live PEv L D D1 Sg]) give a run of [infer]
   that succeeds from some fuel on, holding no equation, and a step [SemC]
   (GoatCompleteCtxW.v) to the derivation's side: the extension [S2] of [Sg]
   respects the sorts the run ends with on the images of the live atoms, [Sg]
   factors through the run's substitution up to conversion on [L], and the
   type the run returns is convertible to the derivation's under [S2].

   The induction reads the unifier through [unify_stepC], which comes from
   [unify_stepG] (GoatCompleteLive.v), compares schemes up to conversion
   ([sch_leT]), and bounds the atoms of the images by [AvoidE], on canonical
   representatives (GoatCompleteBound.v).  A binder generalizes atoms that are
   even and outside the bound, and the premise it reads is the one at an
   environment that re-sorts them.

   Axiom- and admit-free. *)

Require Import Metalib.Metatheory.
Require Import Goat.Goat_ott.
Require Import Goat.GoatRows.
Require Import Goat.GoatDefs.
Require Import Goat.GoatConv.
Require Import Goat.GoatSubst.
Require Import Goat.GoatMu.
Require Import Goat.GoatMeta.
Require Import Goat.GoatSound.
Require Import Goat.GoatInfer.
Require Import Goat.GoatInferSub.
Require Import Goat.GoatInferSort.
Require Import Goat.GoatInferGen.
Require Import Goat.GoatInferUnify.
Require Import Goat.GoatInferW.
Require Import Goat.GoatHeld.
Require Import Goat.GoatHeldInst.
Require Import Goat.GoatInferSound.
Require Import Goat.GoatHeldSound.
Require Import Goat.GoatInferHeld.
Require Import Goat.GoatCoerce.
Require Import Goat.GoatClose.
Require Import Goat.GoatElab.
Require Import Goat.GoatCompleteFuel.
Require Import Goat.GoatCompleteBind.
Require Import Goat.GoatCompleteRf.
Require Import Goat.GoatCompleteRfRows.
Require Import Goat.GoatCompleteSorts.
Require Import Goat.GoatCompleteInst.
Require Import Goat.GoatCompleteGen.
Require Import Goat.GoatCompleteMono.
Require Import Goat.GoatCompleteLet.
Require Import Goat.GoatCompleteNf.
Require Import Goat.GoatCompleteDrk.
Require Import Goat.GoatCompleteEr.
Require Import Goat.GoatCompleteCtx.
Require Import Goat.GoatCompleteLive.
Require Import Goat.GoatCompleteLiveRf.
Require Import Goat.GoatCompleteBound.
Require Import Goat.GoatCompleteSchT.
Require Import Goat.GoatCompleteMonoT.
Require Import Goat.GoatCompleteCtxT.
Require Import Goat.GoatCompleteCtxW.
Require Import Goat.GoatCompleteCore.
Require Import Stdlib.Arith.Arith.
Require Import Stdlib.micromega.Lia.
Require Import Stdlib.Lists.List.
Import ListNotations.

(* A step that leaves the substitution alone on the live atoms, to an
   environment that agrees with the old one there. *)
Lemma SemC_ext : forall L (DT : denv) Sg n n1 (D D1 : denv) S2, Drow D1 -> DOk D1 n1 -> n <= n1 -> LOld n L ->
  (forall a, a `in` L -> D1 a = D a) -> (forall a, a `in` L -> sT S2 a = sT Sg a) ->
  Live PEv L D DT Sg -> SemC L DT Sg n sid D1 n1 S2.
Proof.
  intros L DT Sg n n1 D D1 S2 Hr Hd Hl Ho Hag Hsg HL.
  assert (HL2 : Live PEv L D1 DT S2).
  { intros a Ha. rewrite (Hag a Ha), (Hsg a Ha). exact (HL a Ha). }
  pose proof (LvE_of_Live _ _ _ _ HL2) as HG.
  assert (HT : limgT sid L {} [<=] L) by (intros y Hy; apply (limg_sid L); apply limgT_nil; exact Hy).
  assert (HR : limgR sid L {} [<=] {}).
  { apply limgR_rf. intros x _. cbn [sT sid idt]. exact I. }
  refine (conj (conj Hd (conj Hr (conj (LiveG_mono _ _ _ _ _ _ _ _ _ HT HR HG) (conj _ (conj _ (conj _ OkS_id))))))
            (conj _ _)).
  - refine (conj Hl (conj _ _)).
    + intros x Hx. cbn [sT sid idt]. exact (conj I (conj (atT_V DT n1 x (old_le n n1 x Hl (Ho x Hx))) I)).
    + intros q Hq. exfalso. exact (nil_in q Hq).
  - intros x Hx. cbn [sid sT idt]. change (teq (sT Sg x) (sT S2 x)). rewrite (Hsg x Hx). apply teq_refl.
  - intros q Hq. exfalso. exact (nil_in q Hq).
  - intros x _. cbn [sT sid idt]. exact I.
  - eapply Live_mono; [ exact (limg_sid L) | exact HL2 ].
Qed.

(* ---- a variable bound to a scheme ---- *)

(* A variable the algorithm's context binds to a scheme, which the derivation's
   scheme is compared with: the algorithm instantiates at fresh atoms, and the
   extension sends those to the derivation's instance. *)
Lemma var_sch_doneT : forall L Dd D G n Sg x sd sc T,
  DOk D n -> Drow D -> LOld n L -> LEv L -> Live PEv L D Dd Sg -> GOk n G -> GLive L G ->
  lookup x G = Some sc -> SchIT PEv Dd Sg sd sc -> instP Dd T sd ->
  DoneW L Dd G (e_fvar_f x) D n Sg T.
Proof.
  intros L Dd D G n Sg x sd sc T Hd Hrow HLo HLE HLv HG HGL Hlk Hsch Hi.
  pose proof (GOk_lookup n G x sc HG Hlk) as Hso.
  pose proof Hso as (Hw & Hrq & Hrf & Hold).
  pose proof (GLive_lookup L G x sc HGL Hlk) as Hfl.
  destruct (SchIT_inst PEv Dd Sg sd sc T Hsch Hi) as (T' & Hi2 & HteqT).
  destruct Hi2 as (st & sr & t1 & t2 & t3 & t4 & t5 & t6 & t7 & t8).
  cbn [apS s_tq s_rq s_sk s_rk s_body] in t1, t2, t3, t4, t5, t7, t8.
  set (lq := AtomSetImpl.elements (s_tq sc)) in *.
  set (S2 := fsub Sg n lq st).
  set (T0 := apT (inst_sub sc n) (s_body sc)).
  set (D1 := inst_den D sc n).
  set (n1 := n + length lq + length (AtomSetImpl.elements (s_rq sc))).
  assert (Hinst : instantiate D sc n = (T0, D1, n1)) by reflexivity.
  destruct (instantiate_sound D sc n T0 D1 n1 Hinst Hw Hd) as (_ & HE0 & Hd1 & _).
  assert (Hlr : AtomSetImpl.elements (s_rq sc) = nil)
    by (apply elements_none; intros q Hq; apply Hrq in Hq; revert Hq; fsetdec).
  assert (Hn1 : n1 = n + length lq) by (unfold n1; rewrite Hlr; simpl; lia).
  assert (Hrow1 : Drow D1) by (intros r; unfold D1, inst_den; cbn [drk]; rewrite Hlr; simpl; exact (Hrow r)).
  assert (HoldD : forall b, old n b -> forall a, In a lq -> b <> ea (n + idx a lq)).
  { intros b Hb a Ha E. exact (Hb (n + idx a lq) (Nat.le_add_r n (idx a lq)) E). }
  assert (F2 : forall b, old n b -> sT S2 b = sT Sg b)
    by (intros b Hb; exact (fsub_out Sg n lq st b (HoldD b Hb))).
  assert (HD1o : forall b, old n b -> D1 b = D b)
    by (intros b Hb; exact (inst_den_out D sc n b (HoldD b Hb))).
  assert (Hbody : forall y, y `in` ftv_typ T0 ->
            (exists a, In a lq /\ y = ea (n + idx a lq)) \/ y `in` ftv_sch sc).
  { intros y Hy. unfold T0 in Hy. destruct (ftv_ap_rf (inst_sub sc n) _ y Hrf Hy) as (b & Hb & Hyb).
    destruct (in_dec_set b (s_tq sc)) as [Hq|Hq].
    - left. exists b. split; [ apply In_elements; exact Hq | ].
      cbn [inst_sub sT] in Hyb. destruct (in_dec Atom.eq_dec b (AtomSetImpl.elements (s_tq sc))) as [Hin|Hin].
      + simpl in Hyb. apply AtomSetFacts.singleton_iff in Hyb. exact (eq_sym Hyb).
      + exfalso. apply Hin. apply In_elements. exact Hq.
    - right. cbn [inst_sub sT] in Hyb. destruct (in_dec Atom.eq_dec b (AtomSetImpl.elements (s_tq sc))) as [Hin|Hin].
      + exfalso. apply Hq. apply In_elements. exact Hin.
      + simpl in Hyb. apply AtomSetFacts.singleton_iff in Hyb. subst y.
        unfold ftv_sch. apply AtomSetFacts.diff_iff. split; assumption. }
  assert (P4 : apT S2 T0 = T').
  { unfold T0. rewrite apT_comp. rewrite t3.
    change (ap_typ st sr (apT (sfix (s_tq sc) Sg) (s_body sc)))
      with (apT (Sub st sr) (apT (sfix (s_tq sc) Sg) (s_body sc))).
    rewrite apT_comp. apply apT_agree; [ exact Hrf | ].
    intros b Hb.
    change (sT (scomp S2 (inst_sub sc n)) b) with (apT S2 (sT (inst_sub sc n) b)).
    change (sT (scomp (Sub st sr) (sfix (s_tq sc) Sg)) b) with (apT (Sub st sr) (sT (sfix (s_tq sc) Sg) b)).
    destruct (in_dec_set b (s_tq sc)) as [Hq|Hq].
    - rewrite sfix_in by exact Hq.
      assert (Hin : In b lq) by (apply In_elements; exact Hq).
      assert (Hr : sT (inst_sub sc n) b = typ_Var (ea (n + idx b lq))).
      { cbn [inst_sub sT]. destruct (in_dec Atom.eq_dec b (AtomSetImpl.elements (s_tq sc))) as [H|H];
          [ reflexivity | contradiction ]. }
      rewrite Hr. change (sT S2 (ea (n + idx b lq)) = st b). exact (fsub_at Sg n lq st b Hin).
    - rewrite sfix_out by exact Hq.
      assert (Hbf : b `in` ftv_sch sc) by (unfold ftv_sch; apply AtomSetFacts.diff_iff; split; assumption).
      assert (Hr : sT (inst_sub sc n) b = typ_Var b).
      { cbn [inst_sub sT]. destruct (in_dec Atom.eq_dec b (AtomSetImpl.elements (s_tq sc))) as [H|H];
          [ exfalso; apply Hq; apply In_elements; exact H | reflexivity ]. }
      rewrite Hr. change (sT S2 b = apT (Sub st sr) (sT Sg b)).
      rewrite (F2 b (Hold b Hbf)).
      pose proof (HLv b (Hfl b Hbf)) as [_ [HEb HRb]].
      assert (Hag : apT (Sub st sr) (sT Sg b) = apT sid (sT Sg b)).
      { apply apT_agree; [ exact HRb | ]. intros c Hc. cbn [sT sid idt]. apply t1. intro Hcq.
        exact (ev_od c (proj1 HEb c Hc) ((proj1 Hw) c Hcq)). }
      rewrite Hag. rewrite apT_sid. reflexivity. }
  assert (HrfT0 : rf T0).
  { unfold T0. apply rf_ap; [ exact Hrf | ]. intros b _. cbn [inst_sub sT].
    destruct (in_dec Atom.eq_dec b (AtomSetImpl.elements (s_tq sc))); exact I. }
  assert (HTo : TOk n1 T0).
  { split; [ exact HrfT0 | ]. intros y Hy. destruct (Hbody y Hy) as [(a & Ha & ->)|Hf].
    - intros m Hm E. apply ea_inj in E. pose proof (idx_lt a lq Ha). lia.
    - exact (old_le n n1 y ltac:(lia) (Hold y Hf)). }
  exists sid, D1, n1, S2, T0, (e_fvar_f x).
  refine (conj _ (conj _ (conj HTo (conj HE0 (conj _ (conj _ (conj eq_refl eq_refl))))))).
  - exists 1. intros f Hf. destruct f as [|f]; [ lia | ].
    cbn [infer]. rewrite Hlk. rewrite Hinst. rewrite (rh_rf _ _ _ HrfT0). reflexivity.
  - refine (SemC_ext L Dd Sg n n1 D D1 S2 Hrow1 Hd1 ltac:(lia) HLo _ _ HLv).
    + intros a Ha. exact (HD1o a (HLo a Ha)).
    + intros a Ha. exact (F2 a (HLo a Ha)).
  - intros y Hy. destruct (Hbody y Hy) as [(a & Ha & ->)|Hf].
    + assert (Haq : a `in` s_tq sc) by (apply In_elements; exact Ha).
      change (sat Dd (D1 (ea (n + idx a lq))) (sT S2 (ea (n + idx a lq))) /\ PEv (sT S2 (ea (n + idx a lq)))).
      assert (E1 : D1 (ea (n + idx a lq)) = s_sk sc a) by exact (inst_den_at D sc n a Ha).
      assert (E2 : sT S2 (ea (n + idx a lq)) = st a) by exact (fsub_at Sg n lq st a Ha).
      rewrite E1, E2.
      exact (conj (t4 a Haq) (t7 a Haq)).
    + pose proof (Hfl y Hf) as HyL.
      change (sat Dd (D1 y) (sT S2 y) /\ PEv (sT S2 y)).
      rewrite (HD1o y (HLo y HyL)). rewrite (F2 y (HLo y HyL)). exact (HLv y HyL).
  - rewrite P4. apply teq_sym. exact HteqT.
Qed.

(* ---- facts the cases read ---- *)

Lemma PEv_er : forall X, PEv X -> PEv (erT X).
Proof. intros X [H1 H2]. split; [ exact (EvT_er _ H1) | rewrite (er_rf _ H2); exact H2 ]. Qed.

Lemma AvoidE_Avoid : forall B L Sg, (forall x, x `in` L -> rf (sT Sg x)) -> AvoidE B L {} Sg -> Avoid B L Sg.
Proof.
  intros B L Sg R H x Hx. rewrite <- (er_rf _ (R x Hx)). exact (proj1 H x Hx).
Qed.

Lemma Avoid_AvoidE : forall B L Sg, (forall x, x `in` L -> rf (sT Sg x)) -> Avoid B L Sg -> AvoidE B L {} Sg.
Proof.
  intros B L Sg R H. split.
  - intros x Hx. rewrite (er_rf _ (R x Hx)). exact (H x Hx).
  - intros q Hq. exfalso. exact (nil_in q Hq).
Qed.

Lemma Live_rf : forall L D Dd S, Live PEv L D Dd S -> forall x, x `in` L -> rf (sT S x).
Proof. intros L D Dd S H x Hx. exact (proj2 (proj2 (H x Hx))). Qed.

Lemma TOk_apC : forall L DT Sg n s D' n' S2 T, SemC L DT Sg n s D' n' S2 ->
  TOk n T -> ftv_typ T [<=] L -> TOk n' (apT s T).
Proof.
  intros L DT Sg n s D' n' S2 T H HT Hs. split.
  - exact (SemC_rf_ap L DT Sg n s D' n' S2 T H (proj1 HT) Hs).
  - intros y Hy. exact (SemC_old H y (limg_ap s T L (proj1 HT) Hs y Hy)).
Qed.

Lemma limg_chainC : forall s1 s2 L Lm Lm', (forall x, x `in` L -> rf (sT s1 x)) ->
  limg s1 L [<=] Lm -> limg s2 Lm [<=] Lm' -> limg (scomp s2 s1) L [<=] Lm'.
Proof.
  intros s1 s2 L Lm Lm' R H1 H2 y Hy. apply H2. apply (limg_mono s2 _ _ H1). exact (limg_scompC s1 s2 L R y Hy).
Qed.

(* The derivation's context holds every atom the images of the algorithm's
   context mention. *)
Lemma CIT_ftv : forall (D1 : denv) Sg G1 G n L (Dx : denv), CIT PEv D1 Sg G1 G -> GOk n G -> GLive L G ->
  Live PEv L Dx D1 Sg -> forall a, a `in` ftv_ctx G -> ftv_typ (sT Sg a) [<=] ftv_ctx G1.
Proof.
  intros D1 Sg G1 G n L Dx H. induction H as [|[x s1] [y sc] G1 G [Hk Hrel] _ IH]; intros HO HG HLv a Ha.
  - simpl in Ha. fsetdec.
  - inversion HO as [|b G' Hsc HO' Eb]; subst. inversion HG as [|b2 G2 HL2 HG' Eb2]; subst.
    simpl in *. subst y. apply AtomSetFacts.union_iff in Ha. destruct Ha as [Ha|Ha].
    + intros c Hc. apply AtomSetFacts.union_iff. left.
      destruct Hrel as [(T1 & T & E1 & E2 & Ht)|Hsch].
      * subst s1 sc. pose proof (SOk_mono_inv _ _ Hsc) as HT.
        assert (Haf : a `in` ftv_typ T) by exact (proj1 (ftv_sch_mono T a) Ha).
        assert (HrfA : rf (apT Sg T)).
        { apply rf_ap; [ exact (proj1 HT) | intros w Hw; exact (proj2 (proj2 (HLv w (HL2 w (proj2 (ftv_sch_mono T w) Hw))))) ]. }
        rewrite (teq_rf_eq _ _ HrfA Ht). apply (proj2 (ftv_sch_mono _ c)).
        exact (ftv_ap_in1 (sT Sg) (sR Sg) T c a Haf Hc).
      * pose proof Hsc as (Hw & Hr & Hrf & Hold). unfold SchIT in Hsch. destruct Hsch as (A & _ & _).
        assert (Hrfb : rf (apT (sfix (s_tq sc) Sg) (s_body sc))).
        { apply rf_ap; [ exact Hrf | ]. intros w Hw'. destruct (in_dec_set w (s_tq sc)) as [Hq|Hq].
          - rewrite sfix_in by exact Hq. exact I.
          - rewrite sfix_out by exact Hq.
            assert (Hwf : w `in` ftv_sch sc) by (unfold ftv_sch; apply AtomSetFacts.diff_iff; split; assumption).
            exact (proj2 (proj2 (HLv w (HL2 w Hwf)))). }
        apply ftv_schE_sub. apply A. unfold ftv_schE. cbn [apS s_body s_tq]. rewrite (er_rf _ Hrfb).
        apply AtomSetFacts.diff_iff. split.
        -- assert (Haf : a `in` ftv_typ (s_body sc))
             by (unfold ftv_sch in Ha; apply AtomSetFacts.diff_iff in Ha; exact (proj1 Ha)).
           assert (Haq : a `notin` s_tq sc)
             by (unfold ftv_sch in Ha; apply AtomSetFacts.diff_iff in Ha; exact (proj2 Ha)).
           assert (Hs : sT (sfix (s_tq sc) Sg) a = sT Sg a) by (apply sfix_out; exact Haq).
           assert (Hc' : c `in` ftv_typ (sT (sfix (s_tq sc) Sg) a)) by (rewrite Hs; exact Hc).
           exact (ftv_ap_in1 (sT (sfix (s_tq sc) Sg)) (sR (sfix (s_tq sc) Sg)) (s_body sc) c a Haf Hc').
        -- intro Hcq. pose proof (HLv a (HL2 a Ha)) as [_ [HEa _]].
           exact (ev_od c (proj1 HEa c Hc) ((proj1 Hw) c Hcq)).
    + intros c Hc. apply AtomSetFacts.union_iff. right. exact (IH HO' HG' HLv a Ha c Hc).
Qed.


Lemma fresh_notin_GdT : forall Pt (D1 : denv) Sg Gd G s e2, CIT Pt D1 Sg Gd G ->
  fresh_var (apC s G) e2 `notin` dom Gd `union` fv_exp e2.
Proof.
  intros Pt D1 Sg Gd G s e2 HC. rewrite (CIT_dom _ _ _ _ _ HC). pose proof (dom_apC s G).
  pose proof (fresh_var_notin_dom (apC s G) e2). pose proof (fresh_var_notin_fv (apC s G) e2). fsetdec.
Qed.

Lemma DoneW_const : forall L D1 G e D n Sg T1 c,
  (forall f, infer true (S f) D G e n = Some (sid, D, c, n, e, nil)) ->
  (c = typ_Int \/ c = typ_Float \/ c = typ_Bool \/ c = typ_Unit \/ c = typ_String) ->
  DOk D n -> Drow D -> LOld n L -> Live PEv L D D1 Sg -> teq c T1 -> DoneW L D1 G e D n Sg T1.
Proof.
  intros L D1 G e D n Sg T1 c Hi Hc Hd Hr Ho HL Hteq.
  exists sid, D, n, Sg, c, e.
  refine (conj _ (conj (SemC_id L D1 Sg D n Hr Hd Ho HL) (conj (TOk_scalar n c Hc)
    (conj (EvT_scalar c Hc) (conj (Live_scalar PEv c D D1 Sg Hc) (conj _ (conj eq_refl eq_refl))))))).
  - exists 1. intros f Hf. destruct f as [|f]; [ lia | exact (Hi f) ].
  - destruct Hc as [ -> | [ -> | [ -> | [ -> | -> ] ] ] ]; exact Hteq.
Qed.

(* ---- the induction ---- *)

Theorem infer_complete_core : forall Av D1 G1 e T1, ctyping Av D1 G1 e T1 ->
  forall D G n Sg L, DOk D n -> Drow D -> LOld n L -> LEv L -> Live PEv L D D1 Sg ->
    AvoidE (bg Av G1 T1) L {} Sg -> GOk n G -> GLive L G -> CIT PEv D1 Sg G1 G ->
    DoneW L D1 G e D n Sg T1.
Proof.
  intros Av Dd Gd e T1 H.
  induction H as
    [ Av Dd Gd x s T Hu Hb Hrq Hi
    | Av Dd Gd i T Hu Hs HPT
    | Av Dd Gd d Hu | Av Dd Gd Hu | Av Dd Gd Hu | Av Dd Gd Hu | Av Dd Gd q Hu
    | Av Dd Gd b T1 T2 HPT1 Hb IH
    | Av Dd Gd e1 e2 T1 T2 HPT2 H1 IH1 H2 IH2
    | Av Dd Gd e1 e2 e3 T H1 IH1 H2 IH2 H3 IH3
    | Av Dd Gd e A H1 IH1 Hs HPA
    | Av Dd Gd e1 o e2 A Hk1 Hs HPA H1 IH1 H2 IH2
    | Av Dd Gd e1 o e2 A Hk Hs HPA H1 IH1 H2 IH2
    | Av Dd Gd e1 e2 T1 T2 Hv H1 IH1 H2 IH2
    | Av Dd Gd e1 e2 T1 T2 k rk Tm Hgv Hrf1 Hlit HevA H1 IH1 Hb IHb
    | Av Dd Gd e T T' H1 IH1 Hteq ];
    intros D G n Sg L Hd HRw HLo HLE HLv HAv HG HGL HC.
  - (* variable *)
    destruct (CIT_lookup PEv Dd Sg Gd G x s HC Hu Hb) as (sc & Hlk & [(T1' & T' & E1 & E2 & Hc) | Hsch]).
    + subst s sc.
      pose proof (inst_mono_eq _ _ _ (instP_inst _ _ _ Hi)) as ET. subst T.
      pose proof (GOk_lookup n G x _ HG Hlk) as Hso.
      pose proof (SOk_mono_inv _ _ Hso) as HTo. pose proof (SOk_mono_ev _ _ Hso) as HTe.
      pose proof (GLive_lookup L G x _ HGL Hlk) as Hsub.
      exists sid, D, n, Sg, T', (e_fvar_f x).
      refine (conj _ (conj (SemC_id L Dd Sg D n HRw Hd HLo HLv)
                (conj HTo (conj HTe (conj _ (conj Hc (conj eq_refl eq_refl))))))).
      * exists 1. intros f Hf. destruct f as [|f]; [ lia | ].
        cbn [infer]. rewrite Hlk, instantiate_mono, inst_pres_mono, rh_t_nil. reflexivity.
      * exact (Live_mono PEv _ _ D Dd Sg (fun a Ha => Hsub a (proj2 (ftv_sch_mono T' a) Ha)) HLv).
    + exact (var_sch_doneT L Dd D G n Sg x s sc T Hd HRw HLo HLE HLv HG HGL Hlk Hsch Hi).
  - (* numeral *)
    exists sid, (upd D (ea n) k_Literal), (S n), (supd Sg (ea n) T), (typ_Var (ea n)), (e_num i).
    refine (conj _ (conj (SemC_fresh L Dd D Sg n k_Literal T HRw Hd HLo HLv)
              (conj _ (conj (EvT_var_ea n) (conj _ (conj _ (conj eq_refl eq_refl))))))).
    + exists 1. intros f Hf. destruct f as [|f]; [ lia | reflexivity ].
    + apply TOk_var. apply old_ea. lia.
    + apply Live_var; rewrite ?upd_same, ?supd_same; assumption.
    + rewrite apT_Var, supd_same. apply teq_refl.
  - (* float literal *)
    apply (DoneW_const L Dd G (e_dec d) D n Sg typ_Float typ_Float); try assumption;
      [ intros f; reflexivity | right; left; reflexivity | apply teq_refl ].
  - apply (DoneW_const L Dd G e_true D n Sg typ_Bool typ_Bool); try assumption;
      [ intros f; reflexivity | right; right; left; reflexivity | apply teq_refl ].
  - apply (DoneW_const L Dd G e_false D n Sg typ_Bool typ_Bool); try assumption;
      [ intros f; reflexivity | right; right; left; reflexivity | apply teq_refl ].
  - apply (DoneW_const L Dd G e_unit D n Sg typ_Unit typ_Unit); try assumption;
      [ intros f; reflexivity | right; right; right; left; reflexivity | apply teq_refl ].
  - apply (DoneW_const L Dd G (e_str q) D n Sg typ_String typ_String); try assumption;
      [ intros f; reflexivity | right; right; right; right; reflexivity | apply teq_refl ].
  - (* program *)
    set (x := fresh_var G b).
    assert (Hx : x `notin` dom Gd `union` fv_exp b).
    { rewrite (CIT_dom _ _ _ _ _ HC). pose proof (fresh_var_notin_dom G b). pose proof (fresh_var_notin_fv G b).
      fsetdec. }
    set (Sg' := supd Sg (ea n) T1).
    set (L' := L `union` {{ ea n }}).
    assert (Hsat : sat Dd (D (ea n)) T1) by (rewrite (DOk_ea D n n Hd (le_n n)); apply sat_any).
    assert (HTb : TOk (S n) (typ_Var (ea n))) by (apply TOk_var; apply old_ea; lia).
    assert (HsL : L [<=] L') by (intros y Hy; apply AtomSetFacts.union_iff; left; exact Hy).
    assert (HsV : ftv_typ (typ_Var (ea n)) [<=] L') by exact (ftv_var_fresh n L).
    assert (Hag : forall a, a `in` L -> sT Sg' a = sT Sg a).
    { intros a Ha. unfold Sg'. apply supd_other. intro E. exact (HLo a Ha n (le_n n) E). }
    assert (HLv' : Live PEv L' D Dd Sg').
    { exact (Live_fresh PEv L D D Dd Sg n (D (ea n)) T1 HLo HLv Hsat HPT1 eq_refl (fun _ _ => eq_refl)). }
    assert (HAv' : AvoidE (bg (bg Av Gd (typ_Arrow T1 T2)) ((x ~ sch_mono T1) ++ Gd) T2) L' {} Sg').
    { apply AvoidC_fresh; [ exact HLo | exact (AvoidE_mono _ _ _ _ _ (bg_av _ _ _) HAv) | ].
      intros y Hy. apply bg_av. apply bg_ftv. simpl. apply AtomSetFacts.union_iff. left. exact Hy. }
    destruct (IH x Hx D ((x ~ sch_mono (typ_Var (ea n))) ++ G) (S n) Sg' L'
                (DOk_mono D n (S n) Hd (Nat.le_succ_diag_r n)) HRw (LOld_fresh n L HLo) (LEv_fresh n L HLE)
                HLv' HAv'
                (GOk_cons (S n) x _ G HTb (EvT_var_ea n) (GOk_mono n (S n) G (Nat.le_succ_diag_r n) HG))
                (GLive_cons L' x _ G HsV (GLive_mono L L' G HsL HGL))
                (CIT_cons PEv Dd Sg' Gd G x T1 _ (CIT_agree PEv Dd Sg Sg' Gd G L n HC HG HGL Hag)
                   ltac:(unfold Sg'; rewrite apT_Var, supd_same; apply teq_refl)))
      as (s & D' & n' & S2 & T & e' & Hst & Hsem & HT & HE & LvT & Heq & HgHeq & HlHeq).
    exists s, D', n', S2, (typ_Arrow (apT s (typ_Var (ea n))) T), (e_abs (cl 0 x e')).
    pose proof (SemC_weaken L Dd Sg Sg' n (S n) s D' n' S2 (Nat.le_succ_diag_r n)
      (SemC_mono L L' Dd Sg' (S n) s D' n' S2 HsL Hsem) Hag) as Hsem0.
    refine (conj _ (conj Hsem0 (conj _ (conj _ (conj _ (conj _ (conj _ _))))))).
    + pose proof (Stable_below _ Hst) as HSt. stable_run HSt.
      cbn [infer]. change (fresh_var G b) with x. rewrite Hf. reflexivity.
    + apply TOk_arrow; [ exact (TOk_apC L' Dd Sg' (S n) s D' n' S2 _ Hsem HTb HsV) | exact HT ].
    + exact (EvT_arrow _ _ (EvT_ap s _ (SemC_OkS Hsem) (EvT_var_ea n)) HE).
    + cbn [ftv_typ]. apply Live_union; [ | exact LvT ].
      refine (SemC_live_ap L' Dd Sg' (S n) s D' n' S2 (typ_Var (ea n)) Hsem I _).
      exact HsV.
    + rewrite apT_Arrow. apply teq_arrow; [ | exact Heq ].
      pose proof (SemC_F Hsem (ea n) (in_fresh n L)) as F.
      unfold Sg' in F. rewrite supd_same in F. apply teq_sym. exact F.
    + reflexivity.
    + reflexivity.
  - (* call *)
    assert (HAvX : AvoidE (bg Av Gd T2 `union` ats T1) L {} Sg)
      by exact (AvoidE_mono _ _ _ _ _ (sub_ul _ _ _ (sub_id _)) HAv).
    assert (HAv1 : AvoidE (bg (bg Av Gd T2 `union` ats T1) Gd (typ_Arrow T1 T2)) L {} Sg)
      by exact (AvoidE_mono _ _ _ _ _ (bg_av _ _ _) HAvX).
    destruct (IH1 D G n Sg L Hd HRw HLo HLE HLv HAv1 HG HGL HC)
      as (s1 & D1a & n1 & Sa & Ta & e1' & St1 & Sem1 & HTa & HEa & LvTa & Heq1 & HgHeq1 & HlHeq1).
    destruct (next_factsW Dd Gd Sg n L s1 D1a n1 Sa Ta G HLo HLE Sem1 HTa HEa LvTa HG HGL HC)
      as (HLo1 & HLE1 & HLv1 & HG1 & HGL1 & HC1).
    set (L2 := lnext s1 L Ta) in *.
    assert (HAv2 : AvoidE (bg (bg Av Gd T2 `union` ats T1) Gd T1) L2 {} Sa).
    { refine (AvoidE_mono _ _ _ _ _ (bg_av _ _ _) _).
      exact (AvoidC_next _ _ L Dd Sg n s1 D1a n1 Sa Ta (typ_Arrow T1 T2) HAvX Sem1 (proj1 HTa) Heq1
                (sub_id _) (ftv_arrow_in_X Av Gd T1 T2)). }
    destruct (IH2 D1a (apC s1 G) n1 Sa L2 (SemC_DOk Sem1) (SemC_Drow Sem1) HLo1 HLE1 HLv1 HAv2 HG1 HGL1 HC1)
      as (s2 & D2 & n2 & Sb & Tb & e2' & St2 & Sem2 & HTb & HEb & LvTb & Heq2 & HgHeq2 & HlHeq2).
    destruct (next_factsW Dd Gd Sa n1 L2 s2 D2 n2 Sb Tb (apC s1 G) HLo1 HLE1 Sem2 HTb HEb LvTb HG1 HGL1 HC1)
      as (HLo2 & HLE2 & HLv2 & _ & _ & _).
    set (Ln := lnext s2 L2 Tb) in *.
    pose proof (SemC_DOk Sem2) as Hd2.
    pose proof (TOk_apC L2 Dd Sa n1 s2 D2 n2 Sb Ta Sem2 HTa (ftv_lnext s1 L Ta)) as HTa2.
    assert (Hle : n2 <= S n2) by lia.
    assert (HTv : TOk (S n2) (typ_Var (ea n2))) by (apply TOk_var; apply old_ea; lia).
    assert (HTarr : TOk (S n2) (typ_Arrow Tb (typ_Var (ea n2))))
      by (apply TOk_arrow; [ exact (TOk_mono _ _ _ Hle HTb) | exact HTv ]).
    assert (HsubTa : ftv_typ Ta [<=] L2) by exact (ftv_lnext s1 L Ta).
    assert (HsubTb : ftv_typ Tb [<=] Ln) by exact (ftv_lnext s2 L2 Tb).
    assert (HsubTa2 : ftv_typ (apT s2 Ta) [<=] Ln)
      by (intros y Hy; exact (limg_lnext s2 L2 Tb y (limg_ap s2 Ta L2 (proj1 HTa) HsubTa y Hy))).
    set (Lu := Ln `union` {{ ea n2 }}).
    assert (HLv3 : Live PEv Lu D2 Dd (supd Sb (ea n2) T2)).
    { exact (Live_fresh PEv Ln D2 D2 Dd Sb n2 k_Any T2 HLo2 HLv2 (sat_any _ _) HPT2
               (DOk_ea D2 n2 n2 Hd2 (le_n n2)) (fun _ _ => eq_refl)). }
    assert (Heq : teq (apT (supd Sb (ea n2) T2) (apT s2 Ta))
                          (apT (supd Sb (ea n2) T2) (typ_Arrow Tb (typ_Var (ea n2))))).
    { rewrite (apT_supd Sb (ea n2) T2 _ (proj1 HTa2) (fun Hin => proj2 HTa2 _ Hin n2 (le_n n2) eq_refl)).
      rewrite apT_Arrow, (apT_supd Sb (ea n2) T2 Tb (proj1 HTb) (fun Hin => proj2 HTb _ Hin n2 (le_n n2) eq_refl)),
        apT_Var, supd_same.
      eapply teq_trans; [ apply teq_sym; exact (SemC_factor L2 Dd Sa n1 s2 D2 n2 Sb Ta Sem2 (proj1 HTa) HsubTa) | ].
      eapply teq_trans; [ exact Heq1 | ]. apply teq_arrow; [ apply teq_sym; exact Heq2 | apply teq_refl ]. }
    destruct (unify_stepC Dd D2 (supd Sb (ea n2) T2) Lu (apT s2 Ta) (typ_Arrow Tb (typ_Var (ea n2))) (S n2)  (DOk_mono D2 n2 (S n2) Hd2 Hle) (SemC_Drow Sem2) (LOld_fresh n2 Ln HLo2) (LEv_fresh n2 Ln HLE2) HLv3
                (proj1 HTa2) (conj (proj1 HTb) I)
                (sub_ul _ _ _ HsubTa2)
                (ftv_arrow_sub _ _ _ (sub_ul _ _ _ HsubTb) (ftv_var_fresh n2 Ln)) Heq)
      as (s3 & D3 & n3 & S3 & St3 & Sem3 & HRA3).
    pose proof (SemC_unfresh Ln Dd Sb n2 T2 s3 D3 n3 S3 HLo2 Sem3) as Sem3'.
    pose proof (SemC_comp L L2 Dd Sg n s1 D1a n1 Sa s2 D2 n2 Sb Sem1 (limg_lnext s1 L Ta) Sem2) as Sem12.
    pose proof (limg_chainC s1 s2 L L2 Ln (SemC_rf Sem1) (limg_lnext s1 L Ta) (limg_lnext s2 L2 Tb)) as Hc2.
    exists (scomp s3 (scomp s2 s1)), D3, n3, S3, (apT s3 (typ_Var (ea n2))), (e_app e1' e2').
    refine (conj _ (conj (SemC_comp L Ln Dd Sg n (scomp s2 s1) D2 n2 Sb s3 D3 n3 S3 Sem12 Hc2 Sem3')
              (conj _ (conj _ (conj _ (conj _ (conj _ _))))))).
    + pose proof (Stable_below _ (Stable_and _ _ St1 (Stable_and _ _ St2 St3))) as HSt. stable_run HSt.
      destruct Hf as (E1 & E2 & E3). cbn [infer]. rewrite E1, E2, E3. reflexivity.
    + exact (TOk_apC Lu Dd (supd Sb (ea n2) T2) (S n2) s3 D3 n3 S3 _ Sem3 HTv (ftv_var_fresh n2 Ln)).
    + exact (EvT_ap s3 _ (SemC_OkS Sem3) (EvT_var_ea n2)).
    + refine (SemC_live_ap Lu Dd _ (S n2) s3 D3 n3 S3 (typ_Var (ea n2)) Sem3 I _).
      exact (ftv_var_fresh n2 Ln).
    + pose proof (SemC_F Sem3 (ea n2) (in_fresh n2 Ln)) as F.
      rewrite supd_same in F. apply teq_sym. exact F.
    + cbn [is_gen_value]; try reflexivity; try assumption.
    + cbn [let_open]; reflexivity.
  - (* if *)
    assert (HAv1 : AvoidE (bg (bg Av Gd T) Gd typ_Bool) L {} Sg).
    { refine (AvoidE_mono _ _ _ _ _ (bg_av _ _ _) HAv). }
    destruct (IH1 D G n Sg L Hd HRw HLo HLE HLv HAv1 HG HGL HC)
      as (s1 & D1a & n1 & Sa & Tc & c' & St1 & Sem1 & HTc & HEc & LvTc & Heq1 & HgHeq1 & HlHeq1).
    destruct (next_factsW Dd Gd Sg n L s1 D1a n1 Sa Tc G HLo HLE Sem1 HTc HEc LvTc HG HGL HC)
      as (HLo1 & HLE1 & HLv1 & HG1 & HGL1 & HC1).
    set (L1 := lnext s1 L Tc) in *.
    destruct (unify_stepC Dd D1a Sa L1 Tc typ_Bool n1  (SemC_DOk Sem1) (SemC_Drow Sem1) HLo1 HLE1 HLv1
                (proj1 HTc) I (ftv_lnext s1 L Tc) (sub_scalar typ_Bool L1 (or_intror (or_intror (or_introl eq_refl)))) Heq1)
      as (s2 & D1b & n2 & Sb & St2 & Sem2 & HRA2).
    destruct (CI_stepW L1 Dd Sa n1 s2 D1b n2 Sb Gd (apC s1 G) Sem2 HLE1 HC1 HG1 HGL1) as (HC2 & HG2 & HGL2).
    set (Lb := limg s2 L1).
    assert (HLob : LOld n2 Lb) by exact (SemC_old Sem2).
    assert (HLEb : LEv Lb) by exact (limg_ev s2 L1 (SemC_OkS Sem2) HLE1).
    assert (HAvA : AvoidE (bg Av Gd T) L1 {} Sa).
    { refine (AvoidC_next (bg Av Gd T) (bg Av Gd T) L Dd Sg n s1 D1a n1 Sa Tc typ_Bool (AvoidE_mono _ _ _ _ _ (fun y Hy => Hy) HAv) Sem1 (proj1 HTc) Heq1 (fun y Hy => Hy) _).
      intros y Hy. simpl in Hy. apply AtomSetFacts.empty_iff in Hy. contradiction. }
    assert (HAvb : AvoidE (bg Av Gd T) Lb {} Sb)
      by exact (AvoidC_limg _ L1 Dd Sa n1 s2 D1b n2 Sb HAvA Sem2).
    destruct (IH2 D1b (apC s2 (apC s1 G)) n2 Sb Lb (SemC_DOk Sem2) (SemC_Drow Sem2) HLob HLEb (SemC_live Sem2)
                (AvoidE_mono _ _ _ _ _ (bg_av _ _ _) HAvb) HG2 HGL2 HC2)
      as (s3 & D3 & n3 & Sc & Ta & a' & St3 & Sem3 & HTa & HEa & LvTa & Heq2 & HgHeq2 & HlHeq2).
    destruct (next_factsW Dd Gd Sb n2 Lb s3 D3 n3 Sc Ta (apC s2 (apC s1 G)) HLob HLEb Sem3 HTa HEa LvTa
                HG2 HGL2 HC2)
      as (HLo3 & HLE3 & HLv3 & HG3 & HGL3 & HC3).
    set (L3 := lnext s3 Lb Ta) in *.
    assert (HAv3 : AvoidE (bg Av Gd T) L3 {} Sc).
    { refine (AvoidC_next (bg Av Gd T) (bg Av Gd T) Lb Dd Sb n2 s3 D3 n3 Sc Ta T HAvb Sem3 (proj1 HTa)
                Heq2 (fun y Hy => Hy) _).
      apply bg_ftv. }
    destruct (IH3 D3 (apC s3 (apC s2 (apC s1 G))) n3 Sc L3 (SemC_DOk Sem3) (SemC_Drow Sem3) HLo3 HLE3 HLv3
                (AvoidE_mono _ _ _ _ _ (bg_av _ _ _) HAv3) HG3 HGL3 HC3)
      as (s4 & D4 & n4 & Sd & Tb & b' & St4 & Sem4 & HTb & HEb & LvTb & Heq3 & HgHeq3 & HlHeq3).
    destruct (next_factsW Dd Gd Sc n3 L3 s4 D4 n4 Sd Tb (apC s3 (apC s2 (apC s1 G))) HLo3 HLE3 Sem4 HTb HEb LvTb
                HG3 HGL3 HC3)
      as (HLo4 & HLE4 & HLv4 & _ & _ & _).
    set (L4 := lnext s4 L3 Tb) in *.
    pose proof (TOk_apC L3 Dd Sc n3 s4 D4 n4 Sd _ Sem4 HTa (ftv_lnext s3 Lb Ta)) as HTa4.
    assert (HsubTa : ftv_typ Ta [<=] L3) by exact (ftv_lnext s3 Lb Ta).
    assert (HsubTa4 : ftv_typ (apT s4 Ta) [<=] L4)
      by (intros y Hy; exact (limg_lnext s4 L3 Tb y (limg_ap s4 Ta L3 (proj1 HTa) HsubTa y Hy))).
    assert (Heq : teq (apT Sd (apT s4 Ta)) (apT Sd Tb)).
    { eapply teq_trans; [ apply teq_sym; exact (SemC_factor L3 Dd Sc n3 s4 D4 n4 Sd Ta Sem4 (proj1 HTa) HsubTa) | ].
      eapply teq_trans; [ exact Heq2 | apply teq_sym; exact Heq3 ]. }
    destruct (unify_stepC Dd D4 Sd L4 (apT s4 Ta) Tb n4  (SemC_DOk Sem4) (SemC_Drow Sem4) HLo4 HLE4 HLv4
                (proj1 HTa4) (proj1 HTb) HsubTa4 (ftv_lnext s4 L3 Tb) Heq)
      as (s5 & D5 & n5 & Se & St5 & Sem5 & HRA5).
    pose proof (SemC_comp L L1 Dd Sg n s1 D1a n1 Sa s2 D1b n2 Sb Sem1 (limg_lnext s1 L Tc)
      Sem2) as Sem12.
    pose proof (limg_chainC s1 s2 L L1 Lb (SemC_rf Sem1) (limg_lnext s1 L Tc) (fun _ H => H)) as Hc2.
    pose proof (SemC_comp L Lb Dd Sg n (scomp s2 s1) D1b n2 Sb s3 D3 n3 Sc Sem12 Hc2 Sem3) as Sem123.
    pose proof (limg_chainC (scomp s2 s1) s3 L Lb L3 (SemC_rf Sem12) Hc2 (limg_lnext s3 Lb Ta)) as Hc3.
    pose proof (SemC_comp L L3 Dd Sg n (scomp s3 (scomp s2 s1)) D3 n3 Sc s4 D4 n4 Sd Sem123 Hc3 Sem4) as Sem1234.
    pose proof (limg_chainC (scomp s3 (scomp s2 s1)) s4 L L3 L4 (SemC_rf Sem123) Hc3 (limg_lnext s4 L3 Tb)) as Hc4.
    exists (scomp s5 (scomp s4 (scomp s3 (scomp s2 s1)))), D5, n5, Se, (apT s5 Tb), (e_ite c' a' b').
    refine (conj _ (conj (SemC_comp L L4 Dd Sg n _ D4 n4 Sd s5 D5 n5 Se Sem1234 Hc4 Sem5)
              (conj _ (conj _ (conj _ (conj _ (conj _ _))))))).
    + pose proof (Stable_below _ (Stable_and _ _ St1 (Stable_and _ _ St2 (Stable_and _ _ St3
        (Stable_and _ _ St4 St5))))) as HSt. stable_run HSt.
      destruct Hf as (E1 & E2 & E3 & E4 & E5). cbn [infer]. rewrite E1, E2, E3, E4, E5. reflexivity.
    + exact (TOk_apC L4 Dd Sd n4 s5 D5 n5 Se _ Sem5 HTb (ftv_lnext s4 L3 Tb)).
    + exact (EvT_ap s5 _ (SemC_OkS Sem5) HEb).
    + exact (SemC_live_ap L4 Dd Sd n4 s5 D5 n5 Se Tb Sem5 (proj1 HTb) (ftv_lnext s4 L3 Tb)).
    + eapply teq_trans; [ apply teq_sym; exact (SemC_factor L4 Dd Sd n4 s5 D5 n5 Se Tb Sem5 (proj1 HTb) (ftv_lnext s4 L3 Tb)) | ].
      exact Heq3.
    + cbn [is_gen_value]; try reflexivity; try assumption.
    + cbn [let_open]; reflexivity.
  - (* float(e) *)
    assert (HAv1 : AvoidE (bg (bg Av Gd typ_Float `union` ats A) Gd A) L {} Sg)
      by exact (AvoidE_mono _ _ _ _ _ (bg_av _ _ _) (AvoidE_mono _ _ _ _ _ (sub_ul _ _ _ (sub_id _)) HAv)).
    destruct (IH1 D G n Sg L Hd HRw HLo HLE HLv HAv1 HG HGL HC)
      as (s1 & D1a & n1 & Sa & Ta & e' & St1 & Sem1 & HTa & HEa & LvTa & Heq1 & HgHeq1 & HlHeq1).
    destruct (next_factsW Dd Gd Sg n L s1 D1a n1 Sa Ta G HLo HLE Sem1 HTa HEa LvTa HG HGL HC)
      as (HLo1 & HLE1 & HLv1 & _ & _ & _).
    set (L1 := lnext s1 L Ta) in *.
    assert (Hle : n1 <= S n1) by lia.
    assert (HTv : TOk (S n1) (typ_Var (ea n1))) by (apply TOk_var; apply old_ea; lia).
    assert (HsubTa : ftv_typ Ta [<=] L1) by exact (ftv_lnext s1 L Ta).
    assert (HLv2 : Live PEv (L1 `union` {{ ea n1 }}) (upd D1a (ea n1) k_Literal) Dd (supd Sa (ea n1) A)).
    { refine (Live_fresh PEv L1 D1a (upd D1a (ea n1) k_Literal) Dd Sa n1 k_Literal A HLo1 HLv1 Hs HPA
                (upd_same _ _ _) (fun a Ha => upd_other D1a (ea n1) k_Literal a (fun E => HLo1 a Ha n1 (le_n n1) E))). }
    assert (Heq : teq (apT (supd Sa (ea n1) A) Ta) (apT (supd Sa (ea n1) A) (typ_Var (ea n1)))).
    { rewrite (apT_supd Sa (ea n1) A Ta (proj1 HTa) (fun Hin => proj2 HTa _ Hin n1 (le_n n1) eq_refl)),
        apT_Var, supd_same. exact Heq1. }
    destruct (unify_stepC Dd (upd D1a (ea n1) k_Literal) (supd Sa (ea n1) A) (L1 `union` {{ ea n1 }})
                Ta (typ_Var (ea n1)) (S n1)  (DOk_upd D1a n1 k_Literal (SemC_DOk Sem1)) (Drow_upd _ _ _ (SemC_Drow Sem1))
                (LOld_fresh n1 L1 HLo1) (LEv_fresh n1 L1 HLE1) HLv2 (proj1 HTa) I
                (sub_ul _ _ _ HsubTa) (ftv_var_fresh n1 L1) Heq) as (s2 & D2 & n2 & S3 & St2 & Sem2 & HRA2).
    pose proof (SemC_unfresh L1 Dd Sa n1 A s2 D2 n2 S3 HLo1 Sem2) as Sem2'.
    exists (scomp s2 s1), D2, n2, S3, typ_Float, (e_tofloat e').
    refine (conj _ (conj (SemC_comp L L1 Dd Sg n s1 D1a n1 Sa s2 D2 n2 S3 Sem1 (limg_lnext s1 L Ta) Sem2')
              (conj _ (conj _ (conj _ (conj _ (conj _ _))))))).
    + pose proof (Stable_below _ (Stable_and _ _ St1 St2)) as HSt. stable_run HSt.
      destruct Hf as (E1 & E2). cbn [infer]. rewrite E1, E2. reflexivity.
    + apply TOk_scalar. right. left. reflexivity.
    + apply EvT_scalar. right. left. reflexivity.
    + apply Live_scalar. right. left. reflexivity.
    + apply teq_refl.
    + cbn [is_gen_value]; try reflexivity; try assumption.
    + cbn [let_open]; reflexivity.
  - (* arithmetic *)
    assert (HAvX : AvoidE (bg Av Gd A `union` ats A `union` ats A) L {} Sg)
      by exact (AvoidE_mono _ _ _ _ _ (sub_ul _ _ _ (sub_id _)) HAv).
    assert (HAv1 : AvoidE (bg (bg Av Gd A `union` ats A `union` ats A) Gd A) L {} Sg)
      by exact (AvoidE_mono _ _ _ _ _ (bg_av _ _ _) HAvX).
    destruct (IH1 D G n Sg L Hd HRw HLo HLE HLv HAv1 HG HGL HC)
      as (s1 & D1a & n1 & Sa & Ta & e1' & St1 & Sem1 & HTa & HEa & LvTa & Heq1 & HgHeq1 & HlHeq1).
    destruct (next_factsW Dd Gd Sg n L s1 D1a n1 Sa Ta G HLo HLE Sem1 HTa HEa LvTa HG HGL HC)
      as (HLo1 & HLE1 & HLv1 & HG1 & HGL1 & HC1).
    set (L1 := lnext s1 L Ta) in *.
    assert (HAv2 : AvoidE (bg (bg Av Gd A `union` ats A `union` ats A) Gd A) L1 {} Sa).
    { refine (AvoidE_mono _ _ _ _ _ (bg_av _ _ _) _).
      exact (AvoidC_next _ _ L Dd Sg n s1 D1a n1 Sa Ta A HAvX Sem1 (proj1 HTa) Heq1 (sub_id _)
               (fun y Hy => sub_ur _ _ _ (sub_ul _ _ _ (sub_id _)) y (ats_ftv A y Hy))). }
    destruct (IH2 D1a (apC s1 G) n1 Sa L1 (SemC_DOk Sem1) (SemC_Drow Sem1) HLo1 HLE1 HLv1 HAv2 HG1 HGL1 HC1)
      as (s2 & D2 & n2 & Sb & Tb & e2' & St2 & Sem2 & HTb & HEb & LvTb & Heq2 & HgHeq2 & HlHeq2).
    destruct (next_factsW Dd Gd Sa n1 L1 s2 D2 n2 Sb Tb (apC s1 G) HLo1 HLE1 Sem2 HTb HEb LvTb HG1 HGL1 HC1)
      as (HLo2 & HLE2 & HLv2 & _ & _ & _).
    set (Ln := lnext s2 L1 Tb) in *.
    assert (HTv : TOk (S n2) (typ_Var (ea n2))) by (apply TOk_var; apply old_ea; lia).
    pose proof (TOk_apC L1 Dd Sa n1 s2 D2 n2 Sb Ta Sem2 HTa (ftv_lnext s1 L Ta)) as HTa2.
    assert (HsubTa : ftv_typ Ta [<=] L1) by exact (ftv_lnext s1 L Ta).
    assert (HsubTb : ftv_typ Tb [<=] Ln) by exact (ftv_lnext s2 L1 Tb).
    assert (HsubTa2 : ftv_typ (apT s2 Ta) [<=] Ln)
      by (intros y Hy; exact (limg_lnext s2 L1 Tb y (limg_ap s2 Ta L1 (proj1 HTa) HsubTa y Hy))).
    assert (Hg : sat Dd (generic_sort o) A) by exact Hs.
    assert (HLv3 : Live PEv (Ln `union` {{ ea n2 }}) (upd D2 (ea n2) (generic_sort o)) Dd (supd Sb (ea n2) A)).
    { refine (Live_fresh PEv Ln D2 (upd D2 (ea n2) (generic_sort o)) Dd Sb n2 (generic_sort o) A HLo2 HLv2 Hg HPA
                (upd_same _ _ _) (fun a Ha => upd_other D2 (ea n2) (generic_sort o) a (fun E => HLo2 a Ha n2 (le_n n2) E))). }
    assert (Heq : teq (apT (supd Sb (ea n2) A) (apT s2 Ta)) (apT (supd Sb (ea n2) A) (typ_Var (ea n2)))).
    { rewrite (apT_supd Sb (ea n2) A _ (proj1 HTa2) (fun Hin => proj2 HTa2 _ Hin n2 (le_n n2) eq_refl)),
        apT_Var, supd_same.
      eapply teq_trans; [ apply teq_sym; exact (SemC_factor L1 Dd Sa n1 s2 D2 n2 Sb Ta Sem2 (proj1 HTa) HsubTa) | ].
      exact Heq1. }
    destruct (unify_stepC Dd (upd D2 (ea n2) (generic_sort o)) (supd Sb (ea n2) A) (Ln `union` {{ ea n2 }})
                (apT s2 Ta) (typ_Var (ea n2)) (S n2)  (DOk_upd D2 n2 _ (SemC_DOk Sem2)) (Drow_upd _ _ _ (SemC_Drow Sem2))
                (LOld_fresh n2 Ln HLo2) (LEv_fresh n2 Ln HLE2) HLv3 (proj1 HTa2) I
                (sub_ul _ _ _ HsubTa2) (ftv_var_fresh n2 Ln) Heq) as (s3 & D3 & n3 & S3 & St3 & Sem3 & HRA3).
    pose proof (SemC_unfresh Ln Dd Sb n2 A s3 D3 n3 S3 HLo2 Sem3) as Sem3'.
    set (Lu := Ln `union` {{ ea n2 }}) in *.
    pose proof (TOk_apC Lu Dd (supd Sb (ea n2) A) (S n2) s3 D3 n3 S3 _ Sem3 HTv (ftv_var_fresh n2 Ln)) as HTc3.
    pose proof (TOk_apC Ln Dd Sb n2 s3 D3 n3 S3 _ Sem3' HTb HsubTb) as HTb3.
    assert (Fc : teq A (apT S3 (apT s3 (typ_Var (ea n2))))).
    { pose proof (SemC_F Sem3 (ea n2) (in_fresh n2 Ln)) as F. rewrite supd_same in F. exact F. }
    assert (Heq' : teq (apT S3 (apT s3 Tb)) (apT S3 (apT s3 (typ_Var (ea n2))))).
    { eapply teq_trans; [ apply teq_sym; exact (SemC_factor Ln Dd Sb n2 s3 D3 n3 S3 Tb Sem3' (proj1 HTb) HsubTb) | ].
      eapply teq_trans; [ exact Heq2 | exact Fc ]. }
    assert (HLo3 : LOld n3 (limg s3 Lu)) by exact (SemC_old Sem3).
    assert (HLE3 : LEv (limg s3 Lu)) by exact (limg_ev s3 Lu (SemC_OkS Sem3) (LEv_fresh n2 Ln HLE2)).
    destruct (unify_stepC Dd D3 S3 (limg s3 Lu) (apT s3 Tb) (apT s3 (typ_Var (ea n2))) n3  (SemC_DOk Sem3)
                HRA3 HLo3 HLE3 (SemC_live Sem3) (proj1 HTb3) (proj1 HTc3)
                (limg_ap s3 Tb Lu (proj1 HTb) (sub_ul _ _ _ HsubTb))
                (limg_ap s3 (typ_Var (ea n2)) Lu I (ftv_var_fresh n2 Ln)) Heq')
      as (s4 & D4 & n4 & S4 & St4 & Sem4 & HRA4).
    pose proof (SemC_comp L L1 Dd Sg n s1 D1a n1 Sa s2 D2 n2 Sb Sem1 (limg_lnext s1 L Ta) Sem2) as Sem12.
    pose proof (limg_chainC s1 s2 L L1 Ln (SemC_rf Sem1) (limg_lnext s1 L Ta) (limg_lnext s2 L1 Tb)) as Hc2.
    pose proof (SemC_comp L Ln Dd Sg n (scomp s2 s1) D2 n2 Sb s3 D3 n3 S3 Sem12 Hc2 Sem3') as Sem123.
    pose proof (limg_chainC (scomp s2 s1) s3 L Ln (limg s3 Lu) (SemC_rf Sem12) Hc2
      (limg_mono s3 _ _ (sub_ul _ _ _ (fun _ H => H)))) as Hc3.
    exists (scomp s4 (scomp s3 (scomp s2 s1))), D4, n4, S4, (apT s4 (apT s3 (typ_Var (ea n2)))), (e_bin e1' o e2').
    refine (conj _ (conj (SemC_comp L (limg s3 Lu) Dd Sg n _ D3 n3 S3 s4 D4 n4 S4 Sem123 Hc3 Sem4)
              (conj _ (conj _ (conj _ (conj _ (conj _ _))))))).
    + pose proof (Stable_below _ (Stable_and _ _ St1 (Stable_and _ _ St2 (Stable_and _ _ St3 St4)))) as HSt.
      stable_run HSt. destruct Hf as (E1 & E2 & E3 & E4). cbn [infer]. rewrite E1, E2.
      rewrite (is_cmp_op_false o Hk1). cbv beta iota zeta.
      rewrite E3, E4. rewrite (bin_res_arith o _ Hk1). reflexivity.
    + exact (TOk_apC (limg s3 Lu) Dd S3 n3 s4 D4 n4 S4 _ Sem4 HTc3 (limg_ap s3 (typ_Var (ea n2)) Lu I (ftv_var_fresh n2 Ln))).
    + exact (EvT_ap s4 _ (SemC_OkS Sem4) (EvT_ap s3 _ (SemC_OkS Sem3) (EvT_var_ea n2))).
    + exact (SemC_live_ap (limg s3 Lu) Dd S3 n3 s4 D4 n4 S4 _ Sem4 (proj1 HTc3) (limg_ap s3 (typ_Var (ea n2)) Lu I (ftv_var_fresh n2 Ln))).
    + eapply teq_trans; [ apply teq_sym; exact (SemC_factor (limg s3 Lu) Dd S3 n3 s4 D4 n4 S4 _ Sem4 (proj1 HTc3) (limg_ap s3 (typ_Var (ea n2)) Lu I (ftv_var_fresh n2 Ln))) | ].
      apply teq_sym. exact Fc.
    + cbn [is_gen_value]; try reflexivity; try assumption.
    + cbn [let_open]; reflexivity.
  - (* comparison *)
    assert (HAvX : AvoidE (bg Av Gd typ_Bool `union` ats A `union` ats A) L {} Sg)
      by exact (AvoidE_mono _ _ _ _ _ (sub_ul _ _ _ (sub_id _)) HAv).
    assert (HAv1 : AvoidE (bg (bg Av Gd typ_Bool `union` ats A `union` ats A) Gd A) L {} Sg)
      by exact (AvoidE_mono _ _ _ _ _ (bg_av _ _ _) HAvX).
    destruct (IH1 D G n Sg L Hd HRw HLo HLE HLv HAv1 HG HGL HC)
      as (s1 & D1a & n1 & Sa & Ta & e1' & St1 & Sem1 & HTa & HEa & LvTa & Heq1 & HgHeq1 & HlHeq1).
    destruct (next_factsW Dd Gd Sg n L s1 D1a n1 Sa Ta G HLo HLE Sem1 HTa HEa LvTa HG HGL HC)
      as (HLo1 & HLE1 & HLv1 & HG1 & HGL1 & HC1).
    set (L1 := lnext s1 L Ta) in *.
    assert (HAv2 : AvoidE (bg (bg Av Gd typ_Bool `union` ats A `union` ats A) Gd A) L1 {} Sa).
    { refine (AvoidE_mono _ _ _ _ _ (bg_av _ _ _) _).
      exact (AvoidC_next _ _ L Dd Sg n s1 D1a n1 Sa Ta A HAvX Sem1 (proj1 HTa) Heq1 (sub_id _)
               (fun y Hy => sub_ur _ _ _ (sub_ul _ _ _ (sub_id _)) y (ats_ftv A y Hy))). }
    destruct (IH2 D1a (apC s1 G) n1 Sa L1 (SemC_DOk Sem1) (SemC_Drow Sem1) HLo1 HLE1 HLv1 HAv2 HG1 HGL1 HC1)
      as (s2 & D2 & n2 & Sb & Tb & e2' & St2 & Sem2 & HTb & HEb & LvTb & Heq2 & HgHeq2 & HlHeq2).
    destruct (next_factsW Dd Gd Sa n1 L1 s2 D2 n2 Sb Tb (apC s1 G) HLo1 HLE1 Sem2 HTb HEb LvTb HG1 HGL1 HC1)
      as (HLo2 & HLE2 & HLv2 & _ & _ & _).
    set (Ln := lnext s2 L1 Tb) in *.
    pose proof (TOk_apC L1 Dd Sa n1 s2 D2 n2 Sb Ta Sem2 HTa (ftv_lnext s1 L Ta)) as HTa2.
    assert (HsubTa : ftv_typ Ta [<=] L1) by exact (ftv_lnext s1 L Ta).
    assert (HsubTb : ftv_typ Tb [<=] Ln) by exact (ftv_lnext s2 L1 Tb).
    assert (HsubTa2 : ftv_typ (apT s2 Ta) [<=] Ln)
      by (intros y Hy; exact (limg_lnext s2 L1 Tb y (limg_ap s2 Ta L1 (proj1 HTa) HsubTa y Hy))).
    assert (Heq : teq (apT Sb (apT s2 Ta)) (apT Sb Tb)).
    { eapply teq_trans; [ apply teq_sym; exact (SemC_factor L1 Dd Sa n1 s2 D2 n2 Sb Ta Sem2 (proj1 HTa) HsubTa) | ].
      eapply teq_trans; [ exact Heq1 | apply teq_sym; exact Heq2 ]. }
    destruct (unify_stepC Dd D2 Sb Ln (apT s2 Ta) Tb n2  (SemC_DOk Sem2) (SemC_Drow Sem2) HLo2 HLE2 HLv2
                (proj1 HTa2) (proj1 HTb) HsubTa2 HsubTb Heq) as (s3 & D3 & n3 & S3 & St3 & Sem3 & HRA3).
    pose proof (TOk_apC Ln Dd Sb n2 s3 D3 n3 S3 _ Sem3 HTb HsubTb) as HTb3.
    assert (HTv : TOk (S n3) (typ_Var (ea n3))) by (apply TOk_var; apply old_ea; lia).
    assert (HLo3 : LOld n3 (limg s3 Ln)) by exact (SemC_old Sem3).
    assert (HLE3 : LEv (limg s3 Ln)) by exact (limg_ev s3 Ln (SemC_OkS Sem3) HLE2).
    assert (HsubTb3 : ftv_typ (apT s3 Tb) [<=] limg s3 Ln) by exact (limg_ap s3 Tb Ln (proj1 HTb) HsubTb).
    assert (HLv4 : Live PEv (limg s3 Ln `union` {{ ea n3 }}) (upd D3 (ea n3) k_Eq) Dd (supd S3 (ea n3) A)).
    { refine (Live_fresh PEv (limg s3 Ln) D3 (upd D3 (ea n3) k_Eq) Dd S3 n3 k_Eq A HLo3 (SemC_live Sem3) Hs HPA
                (upd_same _ _ _) (fun a Ha => upd_other D3 (ea n3) k_Eq a (fun E => HLo3 a Ha n3 (le_n n3) E))). }
    assert (Heq' : teq (apT (supd S3 (ea n3) A) (apT s3 Tb)) (apT (supd S3 (ea n3) A) (typ_Var (ea n3)))).
    { rewrite (apT_supd S3 (ea n3) A _ (proj1 HTb3) (fun Hin => proj2 HTb3 _ Hin n3 (le_n n3) eq_refl)),
        apT_Var, supd_same.
      eapply teq_trans; [ apply teq_sym; exact (SemC_factor Ln Dd Sb n2 s3 D3 n3 S3 Tb Sem3 (proj1 HTb) HsubTb) | ].
      exact Heq2. }
    destruct (unify_stepC Dd (upd D3 (ea n3) k_Eq) (supd S3 (ea n3) A) (limg s3 Ln `union` {{ ea n3 }})
                (apT s3 Tb) (typ_Var (ea n3)) (S n3)  (DOk_upd D3 n3 k_Eq (SemC_DOk Sem3)) (Drow_upd _ _ _ (SemC_Drow Sem3))
                (LOld_fresh n3 _ HLo3) (LEv_fresh n3 _ HLE3) HLv4 (proj1 HTb3) I
                (sub_ul _ _ _ HsubTb3) (ftv_var_fresh n3 _) Heq') as (s4 & D4 & n4 & S4 & St4 & Sem4 & HRA4).
    pose proof (SemC_unfresh (limg s3 Ln) Dd S3 n3 A s4 D4 n4 S4 HLo3 Sem4) as Sem4'.
    pose proof (SemC_comp L L1 Dd Sg n s1 D1a n1 Sa s2 D2 n2 Sb Sem1 (limg_lnext s1 L Ta) Sem2) as Sem12.
    pose proof (limg_chainC s1 s2 L L1 Ln (SemC_rf Sem1) (limg_lnext s1 L Ta) (limg_lnext s2 L1 Tb)) as Hc2.
    pose proof (SemC_comp L Ln Dd Sg n (scomp s2 s1) D2 n2 Sb s3 D3 n3 S3 Sem12 Hc2 Sem3) as Sem123.
    pose proof (limg_chainC (scomp s2 s1) s3 L Ln (limg s3 Ln) (SemC_rf Sem12) Hc2 (fun _ H => H)) as Hc3.
    exists (scomp s4 (scomp s3 (scomp s2 s1))), D4, n4, S4, typ_Bool, (e_bin e1' o e2').
    refine (conj _ (conj (SemC_comp L (limg s3 Ln) Dd Sg n _ D3 n3 S3 s4 D4 n4 S4 Sem123 Hc3 Sem4')
              (conj _ (conj _ (conj _ (conj _ (conj _ _))))))).
    + pose proof (Stable_below _ (Stable_and _ _ St1 (Stable_and _ _ St2 (Stable_and _ _ St3 St4)))) as HSt.
      stable_run HSt. destruct Hf as (E1 & E2 & E3 & E4). cbn [infer]. rewrite E1, E2.
      rewrite (is_cmp_op_true o Hk). cbv beta iota zeta. rewrite E3, E4. reflexivity.
    + apply TOk_scalar. right. right. left. reflexivity.
    + apply EvT_scalar. right. right. left. reflexivity.
    + apply Live_scalar. right. right. left. reflexivity.
    + apply teq_refl.
    + cbn [is_gen_value]; try reflexivity; try assumption.
    + cbn [let_open]; reflexivity.
  - (* let of a binding that is not a value *)
    assert (HAvX : AvoidE (bg Av Gd T2 `union` ats T1) L {} Sg)
      by exact (AvoidE_mono _ _ _ _ _ (sub_ul _ _ _ (sub_id _)) HAv).
    assert (HAv1 : AvoidE (bg (bg Av Gd T2 `union` ats T1) Gd T1) L {} Sg)
      by exact (AvoidE_mono _ _ _ _ _ (bg_av _ _ _) HAvX).
    destruct (IH1 D G n Sg L Hd HRw HLo HLE HLv HAv1 HG HGL HC)
      as (s1 & D1a & n1 & Sa & Ta & e1' & St1 & Sem1 & HTa & HEa & LvTa & Heq1 & Hgv & Hlo1).
    destruct (next_factsW Dd Gd Sg n L s1 D1a n1 Sa Ta G HLo HLE Sem1 HTa HEa LvTa HG HGL HC)
      as (HLo1 & HLE1 & HLv1 & HG1 & HGL1 & HC1).
    set (L1 := lnext s1 L Ta) in *.
    rewrite Hv in Hgv.
    assert (HAvX2 : AvoidE (bg Av Gd T2 `union` ats T1) L1 {} Sa).
    { exact (AvoidC_next _ _ L Dd Sg n s1 D1a n1 Sa Ta T1 HAvX Sem1 (proj1 HTa) Heq1 (sub_id _)
               (fun y Hy => sub_ur _ _ _ (ats_ftv T1) y Hy)). }
    assert (HAv2 : AvoidE (bg (bg Av Gd T2 `union` ats T1) Gd T1) L1 {} Sa)
      by exact (AvoidE_mono _ _ _ _ _ (bg_av _ _ _) HAvX2).
    assert (Hx : fresh_var (apC s1 G) e2 `notin` dom Gd `union` fv_exp e2).
    { rewrite (CIT_dom _ _ _ _ _ HC). pose proof (dom_apC s1 G).
      pose proof (fresh_var_notin_dom (apC s1 G) e2). pose proof (fresh_var_notin_fv (apC s1 G) e2). fsetdec. }
    assert (HAv3 : AvoidE (bg (bg Av Gd T2 `union` ats T1) ((fresh_var (apC s1 G) e2 ~ sch_mono T1) ++ Gd) T2) L1 {} Sa).
    { exact (AvoidE_mono _ _ _ _ _ (bg_av _ _ _) HAvX2). }
    destruct (IH2 _ Hx D1a ((fresh_var (apC s1 G) e2 ~ sch_mono Ta) ++ apC s1 G) n1 Sa L1
                (SemC_DOk Sem1) (SemC_Drow Sem1) HLo1 HLE1 HLv1 HAv3 (GOk_cons n1 _ Ta _ HTa HEa HG1)
                (GLive_cons L1 _ Ta _ (ftv_lnext s1 L Ta) HGL1)
                (CIT_cons PEv Dd Sa Gd (apC s1 G) _ T1 Ta HC1 Heq1))
      as (s2 & D2 & n2 & Sb & T & e2' & St2 & Sem2 & HT & HE & LvT & Heq2 & Hg2 & Hl2).
    exists (scomp s2 s1), D2, n2, Sb, T, (e_let e1' (cl 0 (fresh_var (apC s1 G) e2) e2')).
    refine (conj _ (conj (SemC_comp L L1 Dd Sg n s1 D1a n1 Sa s2 D2 n2 Sb Sem1 (limg_lnext s1 L Ta) Sem2)
      (conj HT (conj HE (conj LvT (conj Heq2 (conj _ _))))))).
    + pose proof (Stable_below _ (Stable_and _ _ St1 St2)) as HSt. stable_run HSt.
      destruct Hf as (E1 & E2). cbn [infer]. rewrite E1, Hgv. cbn [andb]. cbv beta iota zeta. rewrite E2. reflexivity.
    + reflexivity.
    + reflexivity.
  - (* let of a value *)
    pose proof (proj1 (proj2 (proj2 (rf_facts T1 Hrf1)))) as Hfrv1.
    set (Vt := AtomSetImpl.diff (ftv_typ T1) (ftv_ctx (pin_ctx Tm Gd))) in *.
    set (Vr := AtomSetImpl.diff (frv_typ T1) (frv_ctx (pin_ctx Tm Gd))) in *.
    set (Dg := extr (ext Dd Vt k) Vr rk) in *.
    assert (Hdsort : forall c, c `notin` Vt -> Dg c = Dd c)
      by (intros c Hc; unfold Dg; rewrite extr_dsort; exact (ext_out _ _ _ _ Hc)).
    assert (Hdrk : forall r, drk Dg r = drk Dd r).
    { intros r. unfold Dg. rewrite extr_out; [ apply ext_drk | ].
      intro Hr. unfold Vr in Hr. apply AtomSetFacts.diff_iff in Hr. exact (Hfrv1 r (proj1 Hr)). }
    assert (HGdV : forall a, a `in` ftv_ctx Gd -> a `notin` Vt).
    { intros a Ha Hv. unfold Vt in Hv. apply AtomSetFacts.diff_iff in Hv. apply (proj2 Hv).
      apply (proj2 (ftv_pin_ctx Tm Gd a)). apply AtomSetFacts.union_iff. right. exact Ha. }
    assert (HVt : forall c, c `in` Vt -> c `notin` bg Av Gd T2) by (intros c Hc; exact (proj2 (HevA c Hc))).
    pose proof (AvoidE_Avoid _ L Sg (Live_rf L D Dd Sg HLv) HAv) as HAvO.
    assert (HAvT : forall x0, x0 `in` L -> forall c, c `in` ftv_typ (sT Sg x0) -> Dg c = Dd c).
    { intros x0 Hx0 c Hc. apply Hdsort. intro Hcv. exact (HVt c Hcv (HAvO x0 Hx0 c Hc)). }
    assert (HLvg : Live PEv L D Dg Sg) by exact (Live_env L D Dd Dg Sg HLv HAvT Hdrk).
    assert (HCg : CIT PEv Dg Sg Gd G)
      by exact (CIT_env PEv Dd Dg Sg Gd G HC (fun a Ha => Hdsort a (HGdV a Ha)) (fun r _ => Hdrk r)).
    destruct (IH1 D G n Sg L Hd HRw HLo HLE HLvg (AvoidE_mono _ _ _ _ _ (bg_av _ _ _) HAv) HG HGL HCg)
      as (s1 & D1 & n1 & Sa & Ta & e1' & St1 & Sem1 & HTa & HEa & LvTa & Heq1 & Hgv1 & Hlo1).
    destruct (next_factsW Dg Gd Sg n L s1 D1 n1 Sa Ta G HLo HLE Sem1 HTa HEa LvTa HG HGL HCg)
      as (HLo1 & HLE1 & HLv1 & HG1 & HGL1 & HC1).
    destruct (CI_stepW L Dg Sg n s1 D1 n1 Sa Gd G Sem1 HLE HCg HG HGL) as (_ & _ & HGLl).
    assert (Hgv1' : is_gen_value e1' = true) by (rewrite Hgv1; exact Hgv).
    assert (HrfA : rf (apT Sa Ta)).
    { apply rf_ap; [ exact (proj1 HTa) | intros w Hw; exact (proj2 (proj2 (LvTa w Hw))) ]. }
    pose proof (teq_rf_eq _ _ HrfA Heq1) as ET.
    pose proof (SemC_OkS Sem1) as Hok1.
    destruct (gen_ren_sc D1 (pin_ctx (let_pin D1 e1' Ta) (apC s1 G)) Ta n1 HTa HEa) as (Hsc & Hscf & Hscc).
    set (G1 := apC s1 G) in *.
    set (sc := gen_ren D1 (pin_ctx (let_pin D1 e1' Ta) G1) Ta) in *.
    set (L1 := lnext s1 L Ta) in *.
    set (Lb := limg s1 L `union` ftv_sch sc).
    assert (HlimL : limg s1 L [<=] Lb) by (intros y Hy; apply AtomSetFacts.union_iff; left; exact Hy).
    assert (HscLb : ftv_sch sc [<=] Lb) by (intros y Hy; apply AtomSetFacts.union_iff; right; exact Hy).
    assert (HLbL1 : Lb [<=] L1).
    { intros y Hy. apply AtomSetFacts.union_iff in Hy. destruct Hy as [Hy|Hy];
        [ exact (limg_lnext s1 L Ta y Hy) | exact (ftv_lnext s1 L Ta y (Hscf y Hy)) ]. }
    assert (HQ : forall b, b `in` s_tq sc -> b `notin` L1).
    { intros b Hbq HbL. exact (ev_od b (HLE1 b HbL) ((proj1 (proj1 Hsc)) b Hbq)). }
    assert (HSa'a : forall y, y `in` L1 -> sT (sfix (s_tq sc) Sa) y = sT Sa y).
    { intros y Hy. apply sfix_out. intro Hq. exact (HQ y Hq Hy). }
    assert (HG1ctx : ftv_ctx G1 [<=] limg s1 L) by exact (GLive_ftv_ctx _ _ HGLl).
    assert (HfzG1 : frozen (sfix (s_tq sc) Sa) G1 Gd).
    { split.
      - intros a Ha. assert (HaL : a `in` L1) by exact (limg_lnext s1 L Ta a (HG1ctx a Ha)).
        split.
        + rewrite (HSa'a a HaL).
          exact (CIT_ftv Dg Sa Gd G1 n1 L1 D1 HC1 HG1 HGL1 HLv1 a Ha).
        + intros c Hc. exfalso.
          rewrite (HSa'a a HaL) in Hc.
          exact (proj1 (proj2 (proj2 (rf_facts _ (proj2 (proj2 (HLv1 a HaL)))))) c Hc).
      - intros r Hr. exfalso. exact (GOk_frv n1 G1 HG1 r Hr). }
    assert (EqS : apT (sfix (s_tq sc) Sa) Ta = T1).
    { rewrite ET. apply apT_agree; [ exact (proj1 HTa) | ]. intros a Ha. apply HSa'a. exact (ftv_lnext s1 L Ta a Ha). }
    assert (Hteq : teq T1 (apT (sfix (s_tq sc) Sa) Ta)) by (rewrite EqS; apply teq_refl).
    assert (Hlit' : lit_pinned e1' (AtomSetImpl.diff (ftv_typ T1) (ftv_ctx (pin_ctx Tm Gd))) k).
    { intros Ho. apply Hlit. rewrite <- Hlo1. exact Ho. }
    assert (Hk' : forall b, b `in` ftv_typ Ta -> sat Dg (dsort D1 b) (sT (sfix (s_tq sc) Sa) b)).
    { intros b Hbq. rewrite (HSa'a b (ftv_lnext s1 L Ta b Hbq)).
      exact (proj1 (HLv1 b (ftv_lnext s1 L Ta b Hbq))). }
    pose proof (let_frozenT Dd D1 (sfix (s_tq sc) Sa) G1 Gd Tm Ta T1 e1' k rk (frozen_E _ _ _ HfzG1)
                  (proj1 (rf_facts Ta (proj1 HTa))) (ps_rf _ _ (proj1 HTa)) Hteq Hlit' Hk') as Hfzp.
    assert (HfrvTa : forall q, q `notin` frv_typ Ta) by exact (proj1 (proj2 (proj2 (rf_facts Ta (proj1 HTa))))).
    assert (Hsch : sch_leT PEv Dd (gen (pin_ctx Tm Gd) T1 k rk) (apS (sfix (s_tq sc) Sa) sc)).
    { refine (gen_mono_letT PEv PEv_lct (fun X H => proj1 H) PEv_er PEv_var
        (fun st sr X _ H1 H2 H3 => PEv_ap st sr X H1 H2 H3)
        Dd D1 (sfix (s_tq sc) Sa) G1 Gd Tm Ta T1 e1' k rk (frozen_E _ _ _ HfzG1)
        (proj1 (rf_facts Ta (proj1 HTa))) (ps_rf _ _ (proj1 HTa)) Hteq
        (fun b Hbq => sfix_in _ _ b Hbq)
        (fun r Hr => False_rect _ (proj1 (AtomSetFacts.empty_iff r) (proj1 (proj1 (proj2 Hsc) r) Hr)))
        (fun a Ha => ltac:(
           assert (HaL : a `in` L1);
           [ apply (proj1 (ftv_pin_ctx (let_pin D1 e1' Ta) G1 a)) in Ha;
             apply AtomSetFacts.union_iff in Ha; destruct Ha as [Ha|Ha];
             [ exact (ftv_lnext s1 L Ta a (let_pin_ftv D1 e1' Ta a Ha)) | exact (limg_lnext s1 L Ta a (HG1ctx a Ha)) ]
           | rewrite (HSa'a a HaL); exact (proj1 (proj2 (HLv1 a HaL))) ]))
        (fun r Hr => ltac:(
           exfalso; apply (proj1 (frv_pin_ctx (let_pin D1 e1' Ta) G1 r)) in Hr;
           apply AtomSetFacts.union_iff in Hr; destruct Hr as [Hr|Hr];
           [ exact (let_pin_frv D1 e1' Ta r Hr) | exact (GOk_frv n1 G1 HG1 r Hr) ]))
        (fun a Ha => ltac:(
           rewrite (HSa'a a (ftv_lnext s1 L Ta a Ha)); exact (proj2 (HLv1 a (ftv_lnext s1 L Ta a Ha)))))
        (fun r Hr => ltac:(exfalso; exact (HfrvTa r Hr)))
        Hlit' Hk'
        (fun r Hr => ltac:(exfalso; exact (HfrvTa r Hr)))). }
    assert (Hsch2 : SchIT PEv Dd (sfix (s_tq sc) Sa) (gen (pin_ctx Tm Gd) T1 k rk) sc).
    { unfold SchIT. rewrite apS_sfix_fixed; [ exact Hsch | exact (proj1 (proj2 (proj2 Hsc))) | ].
      intros q Hq. exact (sfix_in _ _ q Hq). }
    assert (HrfbA : rf (apT (sfix (s_tq sc) Sa) (s_body sc))).
    { apply rf_ap; [ exact (proj1 (proj2 (proj2 Hsc))) | ]. intros w Hw. destruct (in_dec_set w (s_tq sc)) as [Hq|Hq].
      - rewrite sfix_in by exact Hq. exact I.
      - assert (Hwf : w `in` ftv_sch sc) by (unfold ftv_sch; apply AtomSetFacts.diff_iff; split; assumption).
        rewrite (HSa'a w (HLbL1 w (HscLb w Hwf))). exact (proj2 (proj2 (HLv1 w (HLbL1 w (HscLb w Hwf))))). }
    assert (HschA : ftv_sch (apS (sfix (s_tq sc) Sa) sc) [<=] ftv_sch (gen (pin_ctx Tm Gd) T1 k rk)).
    { intros c Hc. apply ftv_schE_sub. apply (proj1 Hsch). unfold ftv_schE. cbn [apS s_body s_tq]. rewrite (er_rf _ HrfbA).
      unfold ftv_sch in Hc. cbn [apS s_body s_tq] in Hc. exact Hc. }
    assert (HAvl : Avoid (bg Av Gd T2) (limg s1 L) Sa)
      by exact (AvoidE_Avoid _ _ Sa (Live_rf _ _ _ _ (SemC_live Sem1)) (AvoidC_limg _ L Dg Sg n s1 D1 n1 Sa HAv Sem1)).
    assert (HnotVt : forall y, y `in` Lb -> forall c, c `in` ftv_typ (sT Sa y) -> c `notin` Vt).
    { intros y Hy c Hc Hcv. apply AtomSetFacts.union_iff in Hy. destruct Hy as [Hy|Hy].
      - exact (HVt c Hcv (HAvl y Hy c Hc)).
      - pose proof (proj1 Hfzp y (Hscc y Hy)) as [Hf _].
        assert (HyL : y `in` L1) by exact (HLbL1 y (proj2 (AtomSetFacts.union_iff _ _ _) (or_intror Hy))).
        assert (Hrfy : rf (sT (sfix (s_tq sc) Sa) y))
          by (rewrite (HSa'a y HyL); exact (proj2 (proj2 (HLv1 y HyL)))).
        rewrite (er_rf _ Hrfy) in Hf.
        assert (Hc' : c `in` ftv_typ (sT (sfix (s_tq sc) Sa) y))
          by (rewrite (HSa'a y (ftv_lnext s1 L Ta y (Hscf y Hy))); exact Hc).
        pose proof (Hf c Hc') as Hin. unfold Vt in Hcv. apply AtomSetFacts.diff_iff in Hcv.
        exact (proj2 Hcv Hin). }
    assert (HLvb : Live PEv Lb D1 Dd (sfix (s_tq sc) Sa)).
    { intros y Hy. assert (HyL : y `in` L1) by exact (HLbL1 y Hy).
      rewrite (HSa'a y HyL). destruct (HLv1 y HyL) as [Hs Hp]. split; [ | exact Hp ].
      eapply sat_loc; [ | | exact Hs ].
      - intros c Hc. exact (eq_sym (Hdsort c (HnotVt y Hy c Hc))).
      - intros r _. exact (eq_sym (Hdrk r)). }
    assert (Sem1e : SemC L Dd Sg n s1 D1 n1 Sa).
    { refine (SemC_env L Dg Dd Sg n s1 D1 n1 Sa Sem1 _ (fun r => eq_sym (Hdrk r))).
      intros x0 Hx0 c Hc. exact (eq_sym (Hdsort c (fun Hv => HVt c Hv (HAvl x0 Hx0 c Hc)))). }
    assert (Sem1' : SemC L Dd Sg n s1 D1 n1 (sfix (s_tq sc) Sa)).
    { refine (SemC_agree L Dd Sg n s1 D1 n1 Sa (sfix (s_tq sc) Sa) Sem1e _).
      intros y Hy. apply HSa'a. exact (limg_lnext s1 L Ta y Hy). }
    assert (HCd : CIT PEv Dd Sa Gd G1)
      by exact (CIT_env PEv Dg Dd Sa Gd G1 HC1 (fun a Ha => eq_sym (Hdsort a (HGdV a Ha))) (fun r _ => eq_sym (Hdrk r))).
    assert (HCd' : CIT PEv Dd (sfix (s_tq sc) Sa) Gd G1)
      by exact (CIT_agree PEv Dd Sa (sfix (s_tq sc) Sa) Gd G1 L1 n1 HCd HG1 HGL1 HSa'a).
    assert (Hx : fresh_var G1 e2 `notin` dom Gd `union` fv_exp e2) by exact (fresh_notin_GdT PEv Dd Sg Gd G s1 e2 HC).
    assert (HAvb : Avoid (bg (bg Av Gd T2) ((fresh_var G1 e2 ~ gen (pin_ctx Tm Gd) T1 k rk) ++ Gd) T2) Lb
                     (sfix (s_tq sc) Sa)).
    { intros y Hy c Hc. apply AtomSetFacts.union_iff in Hy as Hy'. destruct Hy' as [Hy'|Hy'].
      - assert (HyL : y `in` L1) by exact (HLbL1 y Hy).
        rewrite (HSa'a y HyL) in Hc. apply bg_av. exact (HAvl y Hy' c Hc).
      - assert (HyL : y `in` L1) by exact (HLbL1 y Hy).
        rewrite (HSa'a y HyL) in Hc.
        apply ftv_sch_in_bg. apply HschA. unfold ftv_sch. cbn [apS s_body s_tq].
        apply AtomSetFacts.diff_iff. split.
        + assert (Hyb : y `in` ftv_typ (s_body sc))
            by (unfold ftv_sch in Hy'; apply AtomSetFacts.diff_iff in Hy'; exact (proj1 Hy')).
          assert (Hc2 : c `in` ftv_typ (sT (sfix (s_tq sc) Sa) y)) by (rewrite (HSa'a y HyL); exact Hc).
          exact (ftv_ap_in1 (sT (sfix (s_tq sc) Sa)) (sR (sfix (s_tq sc) Sa)) (s_body sc) c y Hyb Hc2).
        + intro Hcq. exact (ev_od c (proj1 (proj1 (proj2 (HLv1 y HyL))) c Hc) ((proj1 (proj1 Hsc)) c Hcq)). }
    destruct (IHb (fresh_var G1 e2) Hx D1 ((fresh_var G1 e2 ~ sc) ++ G1) n1 (sfix (s_tq sc) Sa) Lb
                (SemC_DOk Sem1) (SemC_Drow Sem1) (LOld_sub n1 Lb L1 HLbL1 HLo1) (LEv_sub Lb L1 HLbL1 HLE1) HLvb (Avoid_AvoidE _ Lb (sfix (s_tq sc) Sa) (Live_rf _ _ _ _ HLvb) HAvb)
                (GOk_cons_sch n1 _ sc G1 Hsc HG1)
                (GLive_cons_sch Lb _ sc G1 HscLb (GLive_mono _ _ _ HlimL HGLl))
                (CIT_cons_sch PEv Dd (sfix (s_tq sc) Sa) Gd G1 _ _ sc HCd' Hsch2))
      as (s2 & D2 & n2 & Sb & T & e2' & St2 & Sem2 & HT & HE & LvT & Heq2 & Hg2 & Hl2).
    destruct (SemC_sid_after L Dd Sg n s1 D1 n1 (sfix (s_tq sc) Sa) Sem1') as (Sem1s & Hlsid).
    exists (scomp s2 (scomp sid s1)), D2, n2, Sb, T, (e_let e1' (cl 0 (fresh_var G1 e2) e2')).
    refine (conj _ (conj (SemC_comp L Lb Dd Sg n (scomp sid s1) D1 n1 (sfix (s_tq sc) Sa) s2 D2 n2 Sb Sem1s
                            (fun y Hy => HlimL y (Hlsid y Hy)) Sem2)
      (conj HT (conj HE (conj LvT (conj Heq2 (conj _ _))))))).
    + pose proof (Stable_below _ (Stable_and _ _ St1 St2)) as HSt. stable_run HSt.
      destruct Hf as (E1 & E2). cbn [infer]. rewrite E1, Hgv1'. cbn [orb andb filter length]. rewrite dis_nil.
      cbv beta iota zeta. rewrite own_sub_nil, !apT_sid, !apC_sid.
      unfold sc, G1 in E2. rewrite E2. reflexivity.
    + reflexivity.
    + reflexivity.
  - (* conversion *)
    assert (HAv1 : AvoidE (bg (bg Av Gd T' `union` ats T) Gd T) L {} Sg)
      by exact (AvoidE_mono _ _ _ _ _ (bg_av _ _ _) (AvoidE_mono _ _ _ _ _ (sub_ul _ _ _ (sub_id _)) HAv)).
    destruct (IH1 D G n Sg L Hd HRw HLo HLE HLv HAv1 HG HGL HC)
      as (s & D' & n' & S2 & T0 & e' & Hst & Hsem & HT & HE & LvT & Heq & HgHeq & HlHeq).
    exists s, D', n', S2, T0, e'.
    assert (HrfA : rf (apT S2 T0)).
    { apply rf_ap; [ exact (proj1 HT) | intros w Hw; exact (proj2 (proj2 (LvT w Hw))) ]. }
    pose proof (teq_rf_eq _ _ HrfA Heq) as ET1.
    assert (HrfT : rf T) by (rewrite ET1; exact HrfA).
    pose proof (teqD_rf_eq Dd T T' HrfT Hteq) as ET2.
    refine (conj Hst (conj Hsem (conj HT (conj HE (conj LvT (conj _ (conj HgHeq HlHeq))))))).
    rewrite ET2, ET1. apply teq_refl.
Qed.

(* The closed program: a derivation of a core program at the program judgment
   gives a run of the closed entry point from some fuel on, whose result is a
   principal type of the derivation's, and whose elaborated term erases to the
   program.  The run holds no live row variable, so the extension may send
   every row variable to the empty row, which satisfies every row kind. *)
Theorem infer_complete_core_closed : forall e T, ctyping {} d_any nil e T ->
  exists D T' e' S2,
    Stable (fun f => infer_closed_elab f e = Some (D, T', e')) /\ erase e' = e /\
    Live PEv (ftv_typ T') D d_any S2 /\ rkres D d_any (sR S2) /\
    teqD d_any (apT S2 T') T /\ rf T'.
Proof.
  intros e T H.
  destruct (infer_complete_core {} d_any nil e T H d_any nil 0 sid {}
              (d_any_DOk 0) (Drow_of_RA _ RA_d_any) (LOld_nil 0) LEv_empty
              (Live_empty _ _ _ _) (AvoidE_empty _ _) (GOk_nil 0) (GLive_nil {}) (CIT_nil PEv d_any sid))
    as (s & D' & n' & S2 & T' & e' & St & Sem & HT & HE & LvT & Heq & HgHeq & HlHeq).
  set (S2' := Sub (sT S2) (fun _ => row_Empty)).
  exists D', T', e', S2'.
  assert (St' : Stable (fun f => infer_closed_elab f e = Some (D', T', e'))).
  { eapply Stable_mono; [ | exact St ]. intros f Hf. unfold infer_closed_elab, infer_closed_elab_m. rewrite Hf.
    rewrite dis_top_nil. cbv iota. rewrite apT_sid. reflexivity. }
  refine (conj St' (conj _ (conj LvT (conj _ (conj _ (proj1 HT)))))).
  - destruct St' as [f0 Hf0]. exact (proj2 (infer_closed_sound f0 e D' T' e' (Hf0 f0 (le_n f0)))).
  - intros r. cbn [sR S2']. exact (rkok_empty d_any _).
  - apply teq_teqD. unfold S2'.
    rewrite (apT_agree (Sub (sT S2) (fun _ => row_Empty)) S2 T' (proj1 HT) (fun _ _ => eq_refl)). exact Heq.
Qed.

Lemma instP_mono : forall D T, PEv T -> instP D T (sch_mono T).
Proof.
  intros D T HP. exists idt, idr.
  refine (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ _))))))).
  - intros a _. reflexivity.
  - intros r _. reflexivity.
  - symmetry. apply ap_typ_pointwise_id; reflexivity.
  - intros a Ha. simpl in Ha. fsetdec.
  - intros r Hr. simpl in Hr. fsetdec.
  - apply lc_sub_id.
  - intros a Ha. simpl in Ha. fsetdec.
  - intros r Hr. simpl in Hr. fsetdec.
Qed.

(* The identity function has the derivation at [Int -> Int]; the algorithm
   answers with a type of which that one is an instance. *)
Example core_identity : exists D T' e' S2,
  Stable (fun f => infer_closed_elab f (e_abs (e_fvar_b 0)) = Some (D, T', e')) /\
  erase e' = e_abs (e_fvar_b 0) /\ Live PEv (ftv_typ T') D d_any S2 /\ rkres D d_any (sR S2) /\
  teqD d_any (apT S2 T') (typ_Arrow typ_Int typ_Int) /\ rf T'.
Proof.
  apply infer_complete_core_closed.
  assert (HI : PEv typ_Int) by (apply PEv_scalar; left; reflexivity).
  apply C_Abs; [ exact HI | ]. intros x Hx. simpl.
  refine (C_Var _ _ _ _ (sch_mono typ_Int) typ_Int _ _ _ (instP_mono _ _ HI)); [ solve_uniq | apply binds_one_3; reflexivity | simpl; fsetdec ].
Qed.

(* A comparison, which unifies its operands and only then requires the joined
   type to be [Eq]. *)
Example core_comparison : exists D T' e' S2,
  Stable (fun f => infer_closed_elab f (e_abs (e_bin (e_fvar_b 0) bop_eq (e_fvar_b 0))) = Some (D, T', e')) /\
  erase e' = e_abs (e_bin (e_fvar_b 0) bop_eq (e_fvar_b 0)) /\
  Live PEv (ftv_typ T') D d_any S2 /\ rkres D d_any (sR S2) /\
  teqD d_any (apT S2 T') (typ_Arrow typ_Int typ_Bool) /\ rf T'.
Proof.
  apply infer_complete_core_closed.
  assert (HI : PEv typ_Int) by (apply PEv_scalar; left; reflexivity).
  apply C_Abs; [ exact HI | ]. intros x Hx. simpl.
  apply C_Cmp with (A := typ_Int); [ reflexivity | simpl; auto | exact HI | | ];
    (refine (C_Var _ _ _ _ (sch_mono typ_Int) typ_Int _ _ _ (instP_mono _ _ HI)); [ solve_uniq | apply binds_one_3; reflexivity | simpl; fsetdec ]).
Qed.
