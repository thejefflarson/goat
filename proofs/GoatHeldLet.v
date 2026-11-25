(* [let] and [letrec] over [V] (ADR 0033 amendment, issue 667).

   The bound term of a [let] is typed once, at the state [dis] leaves; the body
   is typed after a later step, and that step is a bound variable [sg] of the
   statement.  A [V] for the body, which holds for every step [S] after the
   body's own, then gives the typing of the whole at [S o s2] ([V_let]). *)

Require Import Metalib.Metatheory.
Require Import Goat.Goat_ott.
Require Import Goat.GoatProofs.
Require Import Goat.GoatRows.
Require Import Goat.GoatDefs.
Require Import Goat.GoatTags.
Require Import Goat.GoatMeta.
Require Import Goat.GoatSubst.
Require Import Goat.GoatSound.
Require Import Goat.GoatInfer.
Require Import Goat.GoatHeld.
Require Import Goat.GoatInferSub.
Require Import Goat.GoatInferSort.
Require Import Goat.GoatInferTyp.
Require Import Goat.GoatInferRen.
Require Import Goat.GoatInferUnify.
Require Import Goat.GoatInferGen.
Require Import Goat.GoatInferRec.
Require Import Goat.GoatElab.
Require Import Goat.GoatCoerce.
Require Import Goat.GoatClose.
Require Import Goat.GoatInferW.
Require Import Goat.GoatInferSound.
Require Import Goat.GoatHeldSound.
Require Import Goat.GoatHeldV.
Require Import Stdlib.Lists.List.
Import ListNotations.

(* The typing of a generalizing [let] under an abstract step [sg] from the
   state where the bound term was typed. *)
Lemma let_typing_gen : forall D1 n1 G1 us1 T1 x e2 sg D2 n2 T2,
  WfCtx G1 -> DOk D1 n1 -> EvT T1 -> is_gen_value us1 = true -> x `notin` dom G1 ->
  typing D1 G1 us1 T1 -> lce 0 e2 -> Good D1 n1 sg D2 n2 ->
  typing D2 (apC sg ((x ~ gen_ren D1 (pin_ctx (let_pin D1 us1 T1) G1) T1) ++ G1)) e2 T2 ->
  typing D2 (apC sg G1) (e_let us1 (cl 0 x e2)) T2.
Proof.
  intros D1 n1 G1 us1 T1 x e2 sg D2 n2 T2 HG1 HD1 HT1 Hgv Hx Hty1 Hlc2 Gd2 Hty2.
  pose proof Gd2 as (_ & Hs2 & HD2 & Hl2 & Hi2 & Hk2).
  set (Tm := let_pin D1 us1 T1) in *.
  set (Pz := (x ~ sch_mono Tm) ++ G1).
  assert (HTm : EvT Tm) by (apply let_pin_EvT; exact HT1).
  assert (HPz : WfCtx Pz)
    by (apply WfCtx_cons; [ exact HG1 | exact Hx | apply WfSch_mono; exact HTm ]).
  assert (Hsc : gen_ren D1 (pin_ctx Tm G1) T1 = gen_ren D1 Pz T1) by reflexivity.
  rewrite Hsc in Hty2.
  rewrite apC_app, apC_single in Hty2.
  pose proof (gen_ren_equiv D1 Pz T1 sg Hs2 HPz HT1) as Hequiv.
  pose proof Hequiv as (Htq & Hrq & _).
  assert (Hpt : ftv_ctx (apC sg Pz) [=] ftv_ctx (pin_ctx (apT sg Tm) (apC sg G1))).
  { unfold Pz, pin_ctx. simpl. unfold ftv_sch. simpl. fsetdec. }
  assert (Hpr : frv_ctx (apC sg Pz) [=] frv_ctx (pin_ctx (apT sg Tm) (apC sg G1))).
  { unfold Pz, pin_ctx. simpl. unfold frv_sch. simpl. fsetdec. }
  apply T_Let with (L := dom G1 `union` {{x}})
                   (T1 := apT sg (s_body (gen_ren D1 Pz T1)))
                   (k := s_sk (gen_ren D1 Pz T1)) (rk := s_rk (gen_ren D1 Pz T1)) (Tm := apT sg Tm).
  - exact Hgv.
  - intros Hc a Ha.
    pose proof Htq as Htq'. cbn [apS s_tq gen s_body s_sk] in Htq'.
    assert (Hin : a `in` s_tq (gen_ren D1 Pz T1)) by (apply Htq'; fsetdec).
    refine (gen_ren_sk_not D1 Pz T1 k_Literal _ a Hin).
    intros b Hb Hlit. apply (In_la Pz T1) in Hb. destruct Hb as [Hb1 Hb2].
    assert (Hbt : b `in` ftv_typ Tm) by (apply let_pin_ftv; [ exact Hc | split; assumption ]).
    apply Hb2. unfold Pz. simpl. unfold ftv_sch. simpl. fsetdec.
  - pose proof (typing_gen_ren_on D1 Pz T1 G1 n1 us1
                  ltac:(unfold Pz; simpl; fsetdec) ltac:(unfold Pz; simpl; fsetdec)
                  HD1 Hty1) as Hg.
    destruct (DOk_supp D1 n1 HD1) as [S1 HS1].
    destruct (DOk_supp D2 n2 HD2) as [S2 HS2].
    pose proof (KR_Dsc_lift D1 D2 n1 n2 sg (gen_ren D1 Pz T1) Hs2 HD1 HD2
                  (gen_ren_od_t D1 Pz T1) (gen_ren_od_r D1 Pz T1) (Good_KR _ _ _ _ _ Gd2)) as Hkr.
    pose proof (typing_ap (Dsc D1 (gen_ren D1 Pz T1)) (Dsc D2 (gen_ren D1 Pz T1))
                  sg G1 us1 (s_body (gen_ren D1 Pz T1)) Hs2 HG1
                  (ex_intro _ _ (supp_ok_ext2 _ _ _ _ _ _ HS1))
                  (ex_intro _ _ (supp_ok_ext2 _ _ _ _ _ _ HS2))
                  (proj1 Hkr) (proj2 Hkr) Hg) as Hl.
    eapply typing_pw; [ exact Hl | ].
    unfold Dsc. apply denv_eq_sets.
    + cbn [apS s_tq gen s_body s_sk] in Htq. rewrite Htq. rewrite Hpt. reflexivity.
    + cbn [apS s_rq gen s_body s_rk] in Hrq. rewrite Hrq. rewrite Hpr. reflexivity.
  - intros y Hy.
    assert (Hdom : y `notin` dom ((x ~ apS sg (gen_ren D1 Pz T1)) ++ apC sg G1))
      by (simpl; rewrite dom_apC; fsetdec).
    pose proof (typing_open_cl D2 (apC sg G1) x y (apS sg (gen_ren D1 Pz T1)) e2 T2 Hty2 Hlc2 Hdom) as Hren.
    eapply typing_sch_equiv_ctx; [ exact Hren | ].
    apply ctx_equiv_cons; [ | apply ctx_equiv_refl ].
    eapply sch_equiv_trans; [ exact Hequiv | ].
    unfold sch_equiv, gen. cbn [s_tq s_rq s_body s_sk s_rk].
    split; [ | split; [ | split; [ reflexivity | split; [ intros a Ha; reflexivity | intros r Hr; reflexivity ] ] ] ]; fsetdec.
Qed.

(* The bound term's type is at the state [dis] left (its equations are
   solved there); the body's [V] holds for steps after [s2].  The equations
   that remain are the body's. *)
Lemma V_let : forall D1 n1 G1 us1 T1 x e2 s2 D2 n2 T2 H2,
  WfCtx G1 -> DOk D1 n1 -> EvT T1 -> is_gen_value us1 = true -> x `notin` dom G1 ->
  typing D1 G1 us1 T1 -> lce 0 e2 -> Good D1 n1 s2 D2 n2 ->
  V (apC s2 ((x ~ gen_ren D1 (pin_ctx (let_pin D1 us1 T1) G1) T1) ++ G1)) D2 n2 e2 T2 H2 ->
  V (apC s2 G1) D2 n2 (e_let us1 (cl 0 x e2)) T2 H2.
Proof.
  intros D1 n1 G1 us1 T1 x e2 s2 D2 n2 T2 H2 HG1 HD1 HT1 Hgv Hx Hty1 Hlc2 Gd2 HV S D'' n'' Hg Hs.
  pose proof (Good_comp _ _ _ _ _ _ _ _ Gd2 Hg) as Gd.
  pose proof (HV S D'' n'' Hg Hs) as Hty. rewrite apC_comp in Hty.
  rewrite apC_comp.
  exact (let_typing_gen D1 n1 G1 us1 T1 x e2 (scomp S s2) D'' n'' _ HG1 HD1 HT1 Hgv Hx Hty1 Hlc2 Gd Hty).
Qed.

(* The whole of a [let] over a bound term that still holds equations: the
   discharge, then the generalization. *)
Lemma V_let_dis : forall k f D n G us1 T1 H1 d D1 n1 x e2 s2 D2 n2 T2 H2,
  V G D n us1 T1 H1 -> dis k f D H1 n = Some (d, D1, n1) -> HOk H1 ->
  WfCtx G -> DOk D n -> EvT T1 -> is_gen_value us1 = true -> x `notin` dom G -> lce 0 e2 ->
  Good D1 n1 s2 D2 n2 ->
  V (apC s2 ((x ~ gen_ren D1 (pin_ctx (let_pin D1 us1 (apT d T1)) (apC d G)) (apT d T1)) ++ apC d G))
    D2 n2 e2 T2 H2 ->
  V (apC s2 (apC d G)) D2 n2 (e_let us1 (cl 0 x e2)) T2 H2.
Proof.
  intros k f D n G us1 T1 H1 d D1 n1 x e2 s2 D2 n2 T2 H2 HV Ed HH HG HD HT1 Hgv Hx Hlc Gd2 HV2.
  destruct (V_dis k f G D n us1 T1 H1 d D1 n1 HV Ed HD HH) as (Gd1 & Hty1).
  destruct Gd1 as (_ & Hs & HD1 & _).
  apply (V_let D1 n1 (apC d G) us1 (apT d T1) x e2 s2 D2 n2 T2 H2); try assumption.
  - apply WfCtx_ap; assumption.
  - apply EvT_ap; assumption.
  - pose proof (dom_apC d G). fsetdec.
Qed.

(* A recursive group, generalized at the state where its fields were typed. *)
Lemma letrec_typing_gen : forall D2 n2 G1 p q Rf fs el sg D3 n3 T3,
  WfCtx G1 -> DOk D2 n2 -> EvR Rf -> fn_group (clf 0 p fs) -> lcef 0 fs -> lce 0 el ->
  p `notin` dom G1 -> q `notin` dom G1 ->
  field_typing D2 ((p ~ sch_mono (typ_Record Rf)) ++ G1) fs Rf -> Good D2 n2 sg D3 n3 ->
  typing D3 (apC sg ((q ~ gen_ren D2 G1 (typ_Record Rf)) ++ G1)) el T3 ->
  typing D3 (apC sg G1) (e_letrec (clf 0 p fs) (cl 0 q el)) T3.
Proof.
  intros D2 n2 G1 p q Rf fs el sg D3 n3 T3 HG21 HD2 HRf Hfg Hlcf Hlcb Hp Hq Hty3 Gd3 Hty4.
  pose proof Gd3 as (_ & Hs3 & HD3 & Hl3 & Hi3 & Hk3).
  rewrite apC_app, apC_single in Hty4.
  pose proof (gen_ren_equiv D2 G1 (typ_Record Rf) sg Hs3 HG21 (proj2 (EvT_Record _) HRf)) as Hequiv.
  pose proof Hequiv as (Htq & Hrq & _).
  pose proof (fields_gen_ren D2 n2 G1 p Rf _ HD2 Hty3) as Hty5.
  destruct (DOk_supp D2 n2 HD2) as [S1' HS1'].
  destruct (DOk_supp D3 n3 HD3) as [S3 HS3].
  pose proof (KR_Dsc_lift D2 D3 n2 n3 sg (gen_ren D2 G1 (typ_Record Rf)) Hs3 HD2 HD3
                (gen_ren_od_t D2 G1 (typ_Record Rf)) (gen_ren_od_r D2 G1 (typ_Record Rf))
                (Good_KR _ _ _ _ _ Gd3)) as Hkr.
  pose proof (fields_ap (Dsc D2 (gen_ren D2 G1 (typ_Record Rf))) (Dsc D3 (gen_ren D2 G1 (typ_Record Rf)))
                sg G1 p _ _ _ Hs3 HG21
                (ex_intro _ _ (supp_ok_ext2 _ _ _ _ _ _ HS1'))
                (ex_intro _ _ (supp_ok_ext2 _ _ _ _ _ _ HS3))
                (proj1 Hkr) (proj2 Hkr) Hty5) as Hty6.
  apply T_Letrec with (L := dom G1 `union` {{p}} `union` {{q}})
    (R := apR sg (ap_row (rename_t (gen_vars_t G1 (typ_Record Rf)))
                         (rename_r (gen_vars_r G1 (typ_Record Rf))) Rf))
    (k := s_sk (gen_ren D2 G1 (typ_Record Rf))) (rk := s_rk (gen_ren D2 G1 (typ_Record Rf))).
  - exact Hfg.
  - intros y Hy.
    pose proof (fields_open_cl _ (apC sg G1) p y _ _ _ Hty6 Hlcf
                  ltac:(simpl; rewrite dom_apC; fsetdec)) as Hf.
    eapply field_typing_pw; [ exact Hf | ].
    unfold Dsc. apply denv_eq_sets; [ exact Htq | exact Hrq ].
  - intros y Hy.
    pose proof (typing_open_cl D3 (apC sg G1) q y
                  (apS sg (gen_ren D2 G1 (typ_Record Rf))) el T3 Hty4 Hlcb
                  ltac:(simpl; rewrite dom_apC; fsetdec)) as Hren.
    eapply typing_sch_equiv_ctx; [ exact Hren | ].
    apply ctx_equiv_cons; [ | apply ctx_equiv_refl ].
    exact Hequiv.
Qed.

Lemma V_letrec : forall D2 n2 G1 p q Rf fs el s3 D3 n3 T3 H3,
  WfCtx G1 -> DOk D2 n2 -> EvR Rf -> fn_group (clf 0 p fs) -> lcef 0 fs -> lce 0 el ->
  p `notin` dom G1 -> q `notin` dom G1 ->
  field_typing D2 ((p ~ sch_mono (typ_Record Rf)) ++ G1) fs Rf -> Good D2 n2 s3 D3 n3 ->
  V (apC s3 ((q ~ gen_ren D2 G1 (typ_Record Rf)) ++ G1)) D3 n3 el T3 H3 ->
  V (apC s3 G1) D3 n3 (e_letrec (clf 0 p fs) (cl 0 q el)) T3 H3.
Proof.
  intros D2 n2 G1 p q Rf fs el s3 D3 n3 T3 H3 HG HD HR Hfg Hlcf Hlcb Hp Hq Hty3 Gd3 HV S D'' n'' Hg Hs.
  pose proof (Good_comp _ _ _ _ _ _ _ _ Gd3 Hg) as Gd.
  pose proof (HV S D'' n'' Hg Hs) as Hty. rewrite apC_comp in Hty.
  rewrite apC_comp.
  exact (letrec_typing_gen D2 n2 G1 p q Rf fs el (scomp S s3) D'' n'' _ HG HD HR Hfg Hlcf Hlcb Hp Hq Hty3 Gd Hty).
Qed.
