(* Soundness of algorithm W with held equations (ADR 0033 amendment, issue 667).

   [infer_sound] says each type the algorithm infers is derivable once the
   equations it holds are solved: a [V] (GoatHeldV.v), not a [typing].  The
   algorithm's last substitution and the equations are those of the state it
   returns, and the proof of each construct pushes its children's [V]s to that
   state ([V_push]) and applies the typing rule over [V].  A generalizing [let]
   and a recursive group discharge the equations of their bound terms ([dis],
   GoatHeld.v) before they generalize, so what is generalized is derivable
   outright.

   This file holds the rules the construct proofs still need over [V]: the
   spread of an open entry, conversion of field types the equations equate,
   recursive literals with methods, and match arms. *)

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
Require Import Goat.GoatClose.
Require Import Goat.GoatKnot.
Require Import Goat.GoatInferKnot.
Require Import Goat.GoatCoerce.
Require Import Goat.GoatInferW.
Require Import Goat.GoatConv.
Require Import Goat.GoatInferSound.
Require Import Goat.GoatHeldSound.
Require Import Goat.GoatHeldV.
Require Import Goat.GoatHeldLet.
Require Import Stdlib.Arith.Arith.
Require Import Stdlib.micromega.Lia.
Require Import Stdlib.Lists.List.
Import ListNotations.

(* ------------------------------------------------------------------ *)
(* Moving a [V] along the algorithm's steps                              *)
(* ------------------------------------------------------------------ *)

Lemma apH_sid : forall H, apH sid H = H.
Proof.
  intros H. unfold apH. induction H as [|h H IH]; [ reflexivity | ].
  cbn [map]. rewrite IH. f_equal. destruct h as [l p y T R]. unfold apE.
  cbn [h_lbl h_pres h_fld h_val h_rest]. rewrite !apT_sid, apR_id. reflexivity.
Qed.

Lemma V_refine : forall Gs D n D' n' e T H,
  Good D n sid D' n' -> V Gs D n e T H -> V Gs D' n' e T H.
Proof.
  intros Gs D n D' n' e T H Hg HV.
  pose proof (V_push _ _ _ _ _ _ _ _ _ Hg HV) as Hp.
  rewrite apC_sid, apT_sid, apH_sid in Hp. exact Hp.
Qed.

Lemma V_pushc : forall G s D n e T H t D' n',
  Good D n t D' n' -> V (apC s G) D n e T H ->
  V (apC (scomp t s) G) D' n' e (apT t T) (apH t H).
Proof. intros. rewrite <- apC_comp. eapply V_push; eassumption. Qed.

Lemma VF_refine : forall Gs D n D' n' fs R H,
  Good D n sid D' n' -> VF Gs D n fs R H -> VF Gs D' n' fs R H.
Proof.
  intros Gs D n D' n' fs R H Hg HV.
  pose proof (VF_push _ _ _ _ _ _ _ _ _ Hg HV) as Hp.
  rewrite apC_sid, apR_id, apH_sid in Hp. exact Hp.
Qed.

(* A derivation in the state the algorithm returns, with no equation held. *)
Lemma V_leaf : forall G D n e T,
  WfCtx G -> typing D G e T -> V (apC sid G) D n e T nil.
Proof. intros. rewrite apC_sid. apply V_typing; assumption. Qed.

Lemma HOk_nil : HOk nil.
Proof. constructor. Qed.

Lemma HOk_app : forall H1 H2, HOk H1 -> HOk H2 -> HOk (H1 ++ H2).
Proof. intros H1 H2. unfold HOk. rewrite Forall_app. tauto. Qed.

(* ------------------------------------------------------------------ *)
(* A spread onto an open entry                                           *)
(* ------------------------------------------------------------------ *)

(* An entry whose presence is absent, or whose field types are equal, is the
   same entry: the conversion the held equation licenses. *)
Lemma teqD_maybe_fld : forall D l P A B R,
  (P = typ_Bool \/ teqD D A B) ->
  teqD D (typ_Record (row_Maybe l P A R)) (typ_Record (row_Maybe l P B R)).
Proof.
  intros D l P A B R Hc. unfold teqD. cbn [nfT]. apply teq_rec.
  rewrite !nfR_maybe. destruct (is_abs P && rlacksD D l (nfR D R)) eqn:Hd; [ apply req_refl | ].
  destruct Hc as [-> | Ht].
  - cbn [nfT]. apply req_absf.
  - apply req_maybe; [ apply teq_refl | exact Ht | apply req_refl ].
Qed.

Lemma V_spread_h : forall Gs D n e1 e2 l p y T2 r H1 H2,
  V Gs D n e1 (typ_Record (row_Maybe l p y r)) H1 -> V Gs D n e2 T2 H2 ->
  V Gs D n (e_spread e1 l e2) (typ_Record (row_Ext l T2 r))
    (H1 ++ H2 ++ (Heq l p y T2 r :: nil)).
Proof.
  intros Gs D n e1 e2 l p y T2 r H1 H2 V1 V2 S D'' n'' Hg Hs.
  apply Sol_app in Hs as [Hs1 Hs]. apply Sol_app in Hs as [Hs2 Hs3].
  inversion Hs3 as [|? ? Hh _]; subst.
  eapply T_Spread; [ | exact (V2 S D'' n'' Hg Hs2) ].
  eapply T_ConvD; [ exact (V1 S D'' n'' Hg Hs1) | ].
  cbn [apT ap_typ]. fold (apR S (row_Maybe l p y r)). cbn [apR ap_row].
  apply teqD_maybe_fld. exact Hh.
Qed.

Lemma V_spreadL : forall Gs D n e1 e2 l R T H1 H2,
  V Gs D n e1 (typ_Record R) H1 -> rlacksD D l R = true -> V Gs D n e2 T H2 ->
  V Gs D n (e_spread e1 l e2) (typ_Record (row_Ext l T R)) (H1 ++ H2).
Proof.
  intros Gs D n e1 e2 l R T H1 H2 V1 Hlk V2 S D'' n'' Hg Hs.
  apply Sol_app in Hs as [Hs1 Hs2].
  apply T_SpreadL with (R := apR S R).
  - exact (V1 S D'' n'' Hg Hs1).
  - exact (rlacksD_ap D D'' (sT S) (sR S) l R (Good_rkres _ _ _ _ _ Hg) Hlk).
  - exact (V2 S D'' n'' Hg Hs2).
Qed.

Lemma V_restrict : forall Gs D n e l a r H,
  V Gs D n e (typ_Record (row_Ext l a r)) H ->
  V Gs D n (e_restrict e l) (typ_Record r) H.
Proof.
  intros Gs D n e l a r H HV S D'' n'' Hg Hs.
  apply T_Restrict with (R0 := apR S (row_Ext l a r)) (T := apT S a).
  - exact (HV S D'' n'' Hg Hs).
  - unfold rm. rewrite apR_Ext. cbn [rmf]. rewrite Nat.eqb_refl. reflexivity.
Qed.

Lemma V_con : forall Gs D n w tg e Ts H,
  tg < length (gtags w) -> V Gs D n e (tag_payload w Ts tg) H ->
  V Gs D n (e_con w tg e) (typ_Grp w (spine Ts)) H.
Proof.
  intros Gs D n w tg e Ts H Hlt HV S D'' n'' Hg Hs.
  rewrite apT_grp, apT_spine. apply T_Con; [ exact Hlt | ].
  rewrite <- apT_tag_payload. exact (HV S D'' n'' Hg Hs).
Qed.

Lemma V_tofloat : forall Gs D n e A H,
  V Gs D n e A H -> sat D k_Literal A -> V Gs D n (e_tofloat e) typ_Float H.
Proof.
  intros Gs D n e A H HV Hsat S D'' n'' Hg Hs.
  apply T_ToFloat with (A := apT S A); [ exact (HV S D'' n'' Hg Hs) | ].
  exact (sat_ap D D'' k_Literal A (sT S) (sR S) (Good_kres _ _ _ _ _ Hg) (Good_rkres _ _ _ _ _ Hg) Hsat).
Qed.

Lemma V_bin : forall Gs D n e1 o e2 A B R H1 H2,
  V Gs D n e1 A H1 -> V Gs D n e2 B H2 -> bin_sig D o A B R ->
  V Gs D n (e_bin e1 o e2) R (H1 ++ H2).
Proof.
  intros Gs D n e1 o e2 A B R H1 H2 V1 V2 Hsig S D'' n'' Hg Hs.
  apply Sol_app in Hs as [Hs1 Hs2].
  eapply T_Bin; [ exact (V1 S D'' n'' Hg Hs1) | exact (V2 S D'' n'' Hg Hs2) | ].
  exact (bin_sig_ap D D'' o A B R (sT S) (sR S) (Good_kres _ _ _ _ _ Hg) (Good_rkres _ _ _ _ _ Hg) Hsig).
Qed.

(* ------------------------------------------------------------------ *)
(* Field lists                                                          *)
(* ------------------------------------------------------------------ *)

Lemma VF_nil_h : forall Gs D n H, uniq Gs -> VF Gs D n fs_nil row_Empty H.
Proof.
  intros Gs D n H Hu S D'' n'' Hg _. apply FT_nil. apply uniq_apC. exact Hu.
Qed.

Lemma VF_cons_h : forall Gs D n l e T fs R H,
  V Gs D n e T H -> VF Gs D n fs R H -> VF Gs D n (fs_cons l e fs) (row_Ext l T R) H.
Proof.
  intros Gs D n l e T fs R H V1 V2 S D'' n'' Hg Hs.
  rewrite apR_Ext. apply FT_cons; [ exact (V1 S D'' n'' Hg Hs) | exact (V2 S D'' n'' Hg Hs) ].
Qed.

Lemma VF_meth_h : forall Gs D n l e T fs R H,
  V Gs D n e T H -> VF Gs D n fs R H -> VF Gs D n (fs_meth l e fs) (row_Ext l T R) H.
Proof.
  intros Gs D n l e T fs R H V1 V2 S D'' n'' Hg Hs.
  rewrite apR_Ext. apply FT_meth; [ exact (V1 S D'' n'' Hg Hs) | exact (V2 S D'' n'' Hg Hs) ].
Qed.

Lemma VF_meth : forall Gs D n l e T fs R H1 H2,
  V Gs D n e T H1 -> VF Gs D n fs R H2 -> VF Gs D n (fs_meth l e fs) (row_Ext l T R) (H1 ++ H2).
Proof.
  intros Gs D n l e T fs R H1 H2 V1 V2 S D'' n'' Hg Hs. apply Sol_app in Hs as [Hs1 Hs2].
  rewrite apR_Ext. apply FT_meth; [ exact (V1 S D'' n'' Hg Hs1) | exact (V2 S D'' n'' Hg Hs2) ].
Qed.

Lemma VF_inv_cons : forall Gs D n l e fs T R H,
  VF Gs D n (fs_cons l e fs) (row_Ext l T R) H -> V Gs D n e T H /\ VF Gs D n fs R H.
Proof.
  intros Gs D n l e fs T R H HV. split;
  intros S D'' n'' Hg Hs; pose proof (HV S D'' n'' Hg Hs) as Hf; rewrite apR_Ext in Hf;
  inversion Hf; subst; assumption.
Qed.

Lemma VF_inv_meth : forall Gs D n l e fs T R H,
  VF Gs D n (fs_meth l e fs) (row_Ext l T R) H -> V Gs D n e T H /\ VF Gs D n fs R H.
Proof.
  intros Gs D n l e fs T R H HV. split;
  intros S D'' n'' Hg Hs; pose proof (HV S D'' n'' Hg Hs) as Hf; rewrite apR_Ext in Hf;
  inversion Hf; subst; assumption.
Qed.

(* A recursive group's members brought to the types of their slots. *)
Lemma VF_pw : forall Gs D n fs R R' fs' H,
  pw_co fs R R' fs' -> (forall S, OkS S -> pw_co fs (apR S R) (apR S R') fs') ->
  VF Gs D n fs R H -> VF Gs D n fs' R' H.
Proof.
  intros Gs D n fs R R' fs' H _ Hp HV S D'' n'' Hg Hs.
  exact (pw_co_typing _ _ _ _ _ _ (HV S D'' n'' Hg Hs) (Hp S (proj1 (proj2 Hg)))).
Qed.

(* ------------------------------------------------------------------ *)
(* Record literals with methods                                          *)
(* ------------------------------------------------------------------ *)

Fixpoint rsp (R : row) : bool :=
  match R with row_Empty => true | row_Ext _ _ R' => rsp R' | _ => false end.

Lemma rsp_apR : forall S R, rsp R = true -> rsp (apR S R) = true.
Proof.
  intros S R. induction R as [|r|l T R IH|l P T R IH]; intros H; simpl in H; try discriminate H.
  - reflexivity.
  - rewrite apR_Ext. simpl. apply IH. exact H.
Qed.

Lemma apR_tail_with : forall S R Rt, rsp R = true ->
  apR S (row_tail_with R Rt) = row_tail_with (apR S R) (apR S Rt).
Proof.
  intros S R Rt. induction R as [|r|l T R IH|l P T R IH]; intros H; simpl in H; try discriminate H.
  - reflexivity.
  - cbn [row_tail_with]. rewrite !apR_Ext. cbn [row_tail_with]. rewrite IH by exact H. reflexivity.
Qed.

Lemma rsp_group_row : forall fs n, rsp (group_row fs n) = true.
Proof.
  induction fs as [|l e rest IH|l e rest IH]; intros n; simpl; [ reflexivity | apply IH | apply IH ].
Qed.

Lemma meths_shared_ap : forall S Rs fs R, OkS S -> meths_shared Rs fs R ->
  meths_shared (apR S Rs) fs (apR S R).
Proof.
  intros S Rs fs R HS H. induction H.
  - constructor.
  - rewrite apR_Ext. constructor. exact IHmeths_shared.
  - rewrite apR_Ext. eapply MS_meth; [ | exact IHmeths_shared ].
    exact (unroll_apT S n T (typ_Arrow (typ_Record Rs) Rr) HS H).
Qed.

Lemma V_obj : forall Gs D n fs R Rt H,
  VF Gs D n fs R H -> rsp R = true -> meths_shared (row_tail_with R Rt) fs R ->
  V Gs D n (e_rec fs) (typ_Record R) H.
Proof.
  intros Gs D n fs R Rt H HV Hsp Hm S D'' n'' Hg Hs.
  assert (Hms : meths_shared (row_tail_with (apR S R) (apR S Rt)) fs (apR S R)).
  { rewrite <- (apR_tail_with S R Rt Hsp).
    exact (meths_shared_ap S _ _ _ (proj1 (proj2 Hg)) Hm). }
  exact (T_Obj D'' (apC S Gs) fs (apR S R) (apR S Rt) (HV S D'' n'' Hg Hs) Hms).
Qed.

(* [tie_obj_sound] over [V]: the slots are met with the coercions it found,
   and the fields' [V] is the one of the state it returns. *)
Lemma tie_obj_V : forall f fs D R Rsl n s D' n' fs2,
  tie_obj f D fs R Rsl n = Some (s, D', n', fs2) ->
  forall Gs H, uniq Gs -> DOk D n -> EvR R -> EvR Rsl -> VF Gs D n fs R H -> lcef 0 fs ->
  Good D n s D' n' /\ VF (apC s Gs) D' n' fs2 (apR s Rsl) (apH s H) /\
  erase_fields fs2 = erase_fields fs /\ lcef 0 fs2 /\ marks fs2 = marks fs /\
  meth_rel fs (apR s R) (apR s Rsl).
Proof.
  intros f fs. induction fs as [|l e rest IH|l e rest IH];
    intros D R Rsl n s D' n' fs2 H Gs Hh Hu HD HR HRsl Hft Hlc;
    destruct R as [|r|l1 T R'|l1 P0 T0 R'], Rsl as [|r2|l2 A Rsl'|l2 P2 T2 R2'];
    simpl in H; try discriminate H.
  - inversion H; subst; clear H.
    refine (conj (Good_id _ _ HD) _).
    rewrite apC_sid, apR_id, apH_sid.
    refine (conj _ (conj eq_refl (conj I (conj eq_refl MRl_nil)))).
    apply VF_nil_h. exact Hu.
  - destruct (Nat.eqb l l1 && Nat.eqb l l2) eqn:Hl; [ | discriminate H ].
    apply Bool.andb_true_iff in Hl. destruct Hl as [Hl1 Hl2].
    apply Nat.eqb_eq in Hl1. apply Nat.eqb_eq in Hl2. subst l1 l2.
    destruct (unify_co f D T A n) as [[[[s1 D1] cs] n1]|] eqn:E1; [ | discriminate H ].
    destruct (tie_obj f D1 rest (apR s1 R') (apR s1 Rsl') n1) as [[[[s2 D2] n2] rest']|] eqn:E2; [ | discriminate H ].
    inversion H; subst; clear H.
    destruct (VF_inv_cons _ _ _ _ _ _ _ _ _ Hft) as [Hv Hr].
    destruct (EvR_ext_inv _ _ _ HR) as [HT HR'].
    destruct (EvR_ext_inv _ _ _ HRsl) as [HA HRsl'].
    destruct (unify_co_sound _ _ _ _ _ _ _ _ _ E1 HT HA) as (Hs1 & Hch & Hgu1).
    pose proof ((proj2 Hgu1) HD) as Gd1.
    pose proof (proj1 (proj2 (proj2 Gd1))) as HD1.
    destruct (IH _ _ _ _ _ _ _ _ E2 (apC s1 Gs) (apH s1 Hh) (uniq_apC s1 _ Hu) HD1
                (EvR_ap _ _ Hs1 HR') (EvR_ap _ _ Hs1 HRsl')
                (VF_push _ _ _ _ _ _ _ _ _ Gd1 Hr) (proj2 Hlc))
      as (Gd2 & Hty2 & Her2 & Hlc2 & Hmk2 & Hmr2).
    pose proof Gd2 as (_ & Hs2 & _).
    refine (conj (Good_comp _ _ _ _ _ _ _ _ Gd1 Gd2) _).
    rewrite <- apC_comp, <- apR_comp, !apR_Ext, <- !apT_comp, <- apH_comp.
    refine (conj _ (conj _ (conj _ (conj _ _)))).
    + apply VF_cons_h; [ | exact Hty2 ].
      pose proof (V_push _ _ _ _ _ _ _ _ _ Gd1 Hv) as Hv1.
      pose proof (V_coerce _ _ _ _ _ _ _ _ (chainD_of_chain _ _ _ _ Hch) Hv1) as Hv2.
      exact (V_push _ _ _ _ _ _ _ _ _ Gd2 Hv2).
    + cbn [erase_fields]. rewrite erase_coerce, Her2. reflexivity.
    + cbn [lcef]. split; [ apply lce_coerce; exact (proj1 Hlc) | exact Hlc2 ].
    + cbn [marks]. rewrite Hmk2. reflexivity.
    + constructor. rewrite !apR_comp in Hmr2. rewrite apR_comp. exact Hmr2.
  - destruct (Nat.eqb l l1 && Nat.eqb l l2) eqn:Hl; [ | discriminate H ].
    apply Bool.andb_true_iff in Hl. destruct Hl as [Hl1 Hl2].
    apply Nat.eqb_eq in Hl1. apply Nat.eqb_eq in Hl2. subst l1 l2.
    destruct (unify_co f D T A n) as [[[[s1 D1] cs] n1]|] eqn:E1; [ | discriminate H ].
    destruct (tie_obj f D1 rest (apR s1 R') (apR s1 Rsl') n1) as [[[[s2 D2] n2] rest']|] eqn:E2; [ | discriminate H ].
    inversion H; subst; clear H.
    destruct (VF_inv_meth _ _ _ _ _ _ _ _ _ Hft) as [Hv Hr].
    destruct (EvR_ext_inv _ _ _ HR) as [HT HR'].
    destruct (EvR_ext_inv _ _ _ HRsl) as [HA HRsl'].
    destruct (unify_co_sound _ _ _ _ _ _ _ _ _ E1 HT HA) as (Hs1 & Hch & Hgu1).
    pose proof ((proj2 Hgu1) HD) as Gd1.
    pose proof (proj1 (proj2 (proj2 Gd1))) as HD1.
    destruct (IH _ _ _ _ _ _ _ _ E2 (apC s1 Gs) (apH s1 Hh) (uniq_apC s1 _ Hu) HD1
                (EvR_ap _ _ Hs1 HR') (EvR_ap _ _ Hs1 HRsl')
                (VF_push _ _ _ _ _ _ _ _ _ Gd1 Hr) (proj2 Hlc))
      as (Gd2 & Hty2 & Her2 & Hlc2 & Hmk2 & Hmr2).
    pose proof Gd2 as (_ & Hs2 & _).
    refine (conj (Good_comp _ _ _ _ _ _ _ _ Gd1 Gd2) _).
    assert (Hu' : unroll_eq (length cs) (apT s2 (apT s1 A)) (apT s2 (apT s1 T))).
    { exact (unroll_ap (sT s2) (sR s2) _ _ _ (OkS_lc s2 Hs2)
               (unroll_sym _ _ _ (chain_unroll_eq _ _ _ Hch))). }
    rewrite <- apC_comp, <- apR_comp, !apR_Ext, <- !apT_comp, <- apH_comp.
    refine (conj _ (conj _ (conj _ (conj _ _)))).
    + apply VF_meth_h; [ | exact Hty2 ].
      pose proof (V_push _ _ _ _ _ _ _ _ _ Gd1 Hv) as Hv1.
      pose proof (V_coerce _ _ _ _ _ _ _ _ (chainD_of_chain _ _ _ _ Hch) Hv1) as Hv2.
      exact (V_push _ _ _ _ _ _ _ _ _ Gd2 Hv2).
    + cbn [erase_fields]. rewrite erase_coerce, Her2. reflexivity.
    + cbn [lcef]. split; [ apply lce_coerce; exact (proj1 Hlc) | exact Hlc2 ].
    + cbn [marks]. rewrite Hmk2. reflexivity.
    + eapply MRl_meth; [ exact Hu' | ]. rewrite !apR_comp in Hmr2. rewrite apR_comp. exact Hmr2.
Qed.

(* ------------------------------------------------------------------ *)
(* Match arms                                                           *)
(* ------------------------------------------------------------------ *)

Definition VA (L : vars) (Gs : ctx) (D : denv) (n : nat) (w : gdecl) (Ts : list typ)
  (ars : arms) (T : typ) (H : list heq) : Prop :=
  forall S D'' n'', Good D n S D'' n'' -> Sol D'' S H ->
    arms_typ L D'' (apC S Gs) w (map (apT S) Ts) ars (apT S T).

Lemma VA_push : forall L Gs D n w Ts ars T H t D' n',
  Good D n t D' n' -> VA L Gs D n w Ts ars T H ->
  VA L (apC t Gs) D' n' w (map (apT t) Ts) ars (apT t T) (apH t H).
Proof.
  intros L Gs D n w Ts ars T H t D' n' Ht HV S D'' n'' Hg Hs.
  pose proof (HV (scomp S t) D'' n'' (Good_comp _ _ _ _ _ _ _ _ Ht Hg) (proj1 (Sol_apH _ _ _ _) Hs)) as Hty.
  rewrite <- apC_comp, <- apT_comp, <- map_apT_comp in Hty. exact Hty.
Qed.

Lemma VA_nil : forall L Gs D n w Ts T H, VA L Gs D n w Ts arms_nil T H.
Proof. intros. intros S D'' n'' _ _. apply arms_typ_nil. Qed.

Lemma VA_else : forall L Gs D n w Ts e T H,
  V Gs D n e T H -> VA L Gs D n w Ts (arms_else e) T H.
Proof.
  intros L Gs D n w Ts e T H HV S D'' n'' Hg Hs. apply arms_typ_else. exact (HV S D'' n'' Hg Hs).
Qed.

Lemma VA_cons : forall L Gs D n w Ts tg e rest T H1 H2,
  (forall y, y `notin` L ->
     V ((y ~ sch_mono (tag_payload w Ts tg)) ++ Gs) D n (open_exp_wrt_exp e (e_fvar_f y)) T H1) ->
  VA L Gs D n w Ts rest T H2 -> VA L Gs D n w Ts (arms_cons tg e rest) T (H1 ++ H2).
Proof.
  intros L Gs D n w Ts tg e rest T H1 H2 Hb Hr S D'' n'' Hg Hs.
  apply Sol_app in Hs as [Hs1 Hs2].
  apply arms_typ_cons; [ | exact (Hr S D'' n'' Hg Hs2) ].
  intros y Hy. pose proof (Hb y Hy S D'' n'' Hg Hs1) as Hty.
  rewrite apC_cons_mono, apT_tag_payload in Hty. exact Hty.
Qed.

Lemma VA_L : forall L1 L2 Gs D n w Ts ars T H,
  L1 [<=] L2 -> VA L1 Gs D n w Ts ars T H -> VA L2 Gs D n w Ts ars T H.
Proof.
  intros L1 L2 Gs D n w Ts ars T H Hs HV S D'' n'' Hg Hsol.
  exact (arms_typ_L _ _ _ _ _ _ _ _ Hs (HV S D'' n'' Hg Hsol)).
Qed.

Lemma V_match : forall L Gs D n w Ts e ars T H1 H2,
  V Gs D n e (typ_Grp w (spine Ts)) H1 -> arms_wf w ars -> VA L Gs D n w Ts ars T H2 ->
  V Gs D n (e_match w e ars) T (H1 ++ H2).
Proof.
  intros L Gs D n w Ts e ars T H1 H2 V1 Hwf HA S D'' n'' Hg Hs.
  apply Sol_app in Hs as [Hs1 Hs2].
  destruct (HA S D'' n'' Hg Hs2) as [Hr Hd].
  apply T_Match with (L := L) (w := w) (Ts := map (apT S) Ts).
  - pose proof (V1 S D'' n'' Hg Hs1) as Hty. rewrite apT_grp, apT_spine in Hty. exact Hty.
  - exact Hwf.
  - exact Hr.
  - exact Hd.
Qed.

(* ------------------------------------------------------------------ *)
(* The spread of an open entry                                           *)
(* ------------------------------------------------------------------ *)

Lemma HOk_cons : forall h H, (EvT (h_pres h) /\ EvT (h_fld h) /\ EvT (h_val h) /\ EvR (h_rest h)) ->
  HOk H -> HOk (h :: H).
Proof. intros h H Hh HH. unfold HOk. constructor; assumption. Qed.

Lemma HOk_ap_s : forall s H, OkS s -> HOk H -> HOk (apH s H).
Proof. exact HOk_ap. Qed.

Lemma spread_present_sound : forall f D n G l e1 e2 s1 D1 T1 n1 e1' H1 s2 D2 T2 n2 e2' H2 s D' T n' e' Hq,
  spread_present f D2 s1 s2 T1 T2 l e1' e2' n2 H1 H2 = Some (s, D', T, n', e', Hq) ->
  WfCtx G ->
  Good D n s1 D1 n1 -> EvT T1 -> HOk H1 -> V (apC s1 G) D1 n1 e1' T1 H1 -> erase e1' = e1 -> lce 0 e1' ->
  Good D1 n1 s2 D2 n2 -> EvT T2 -> HOk H2 -> V (apC s2 (apC s1 G)) D2 n2 e2' T2 H2 ->
  erase e2' = e2 -> lce 0 e2' ->
  Good D n s D' n' /\ EvT T /\ HOk Hq /\
  (V (apC s G) D' n' e' T Hq /\ erase e' = e_spread e1 l e2 /\ lce 0 e').
Proof.
  intros f D n G l e1 e2 s1 D1 T1 n1 e1' H1 s2 D2 T2 n2 e2' H2 s D' T n' e' Hq Hsp HG
    Gd1 HT1 HH1 Hv1 Her1 Hlc1 Gd2 HT2 HH2 Hv2 Her2 Hlc2.
  unfold spread_present in Hsp.
  destruct (unify_coD f (rupd D2 (ea (S n2)) (RK k_Any (Nat.eqb l))) (apT s2 T1)
              (typ_Record (row_Maybe l (typ_Var (ea n2)) (typ_Var (ea (n2 + 2))) (row_Var (ea (S n2)))))
              (n2 + 3))
    as [[[[s3 Du3] cs3] n3]|] eqn:E3; [|discriminate].
  inversion Hsp; try subst s; try subst D'; try subst T; try subst n'; try subst e'; try subst Hq; clear Hsp.
  pose proof Gd1 as (_ & Hs1 & HD1 & _).
  pose proof Gd2 as (_ & Hs2 & HD2 & _).
  assert (Hrow : EvT (typ_Record (row_Maybe l (typ_Var (ea n2)) (typ_Var (ea (n2 + 2)))
                                    (row_Var (ea (S n2)))))).
  { apply EvT_Record, EvR_maybe; [ apply EvT_var, ev_ea | apply EvT_var, ev_ea | apply EvR_var, ev_ea ]. }
  pose proof (Good_pre D2 n2 (S n2) sid (rupd D2 (ea (S n2)) (RK k_Any (Nat.eqb l))) (S (S n2))
                (le_S _ _ (le_n n2)) HD2
                (Good_rupd D2 (S n2) (RK k_Any (Nat.eqb l)) (DOk_mono D2 n2 (S n2) HD2 (le_S _ _ (le_n n2)))))
    as GdU.
  destruct (unify_coD_sound _ _ _ _ _ _ _ _ _ E3 (DOk_mono _ _ (n2 + 3) (Good_dok _ _ _ _ _ GdU) ltac:(lia))
              (EvT_ap s2 T1 Hs2 HT1) Hrow)
    as (Hs3 & Hch & Hgu3).
  pose proof (GoodU_pre _ (S (S n2)) _ s3 Du3 n3 (Good_dok _ _ _ _ _ GdU) Hgu3 ltac:(lia)) as Gd3'.
  pose proof (Good_lift _ _ _ _ _ _ _ GdU Gd3') as Gd3.
  split; [ exact (Good_comp _ _ _ _ _ _ _ _ (Good_comp _ _ _ _ _ _ _ _ Gd1 Gd2) Gd3) | ].
  split.
  { apply EvT_ap; [ exact Hs3 | ]. apply EvT_Record, EvR_ext; [ exact HT2 | apply EvR_var, ev_ea ]. }
  split.
  { apply HOk_app; [ exact (HOk_ap _ _ Hs3 (HOk_ap _ _ Hs2 HH1)) | ].
    apply HOk_app; [ exact (HOk_ap _ _ Hs3 HH2) | ].
    assert (Hnew : HOk (Heq l (typ_Var (ea n2)) (typ_Var (ea (n2 + 2))) T2 (row_Var (ea (S n2))) :: nil)).
    { apply HOk_cons; [ | apply HOk_nil ].
      cbn [h_pres h_fld h_val h_rest].
      refine (conj (EvT_var _ (ev_ea _)) (conj (EvT_var _ (ev_ea _)) (conj HT2 (EvR_var _ (ev_ea _))))). }
    exact (HOk_ap _ _ Hs3 Hnew). }
  refine (conj _ (conj _ _)).
  2: { cbn [erase]. rewrite erase_coerce, Her1, Her2. reflexivity. }
  2: { cbn [lce]. split; [ apply lce_coerce; exact Hlc1 | exact Hlc2 ]. }
  rewrite <- !apC_comp.
  pose proof (V_coerce _ _ _ _ _ _ _ _ Hch
                (V_push _ _ _ _ _ _ _ _ _ Gd3 (V_push _ _ _ _ _ _ _ _ _ Gd2 Hv1))) as V1.
  pose proof (V_push _ _ _ _ _ _ _ _ _ Gd3 Hv2) as V2.
  exact (V_spread_h _ _ _ _ _ l (apT s3 (typ_Var (ea n2))) (apT s3 (typ_Var (ea (n2 + 2))))
           (apT s3 T2) (apR s3 (row_Var (ea (S n2)))) _ _ V1 V2).
Qed.

(* ------------------------------------------------------------------ *)
(* Soundness                                                            *)
(* ------------------------------------------------------------------ *)

(* The equations a result holds are well formed, and its type is derivable
   at the state it returns once they are solved. *)
Theorem infer_sound : forall f,
  (forall D G e n s D' T n' e' Hq, infer f D G e n = Some (s, D', T, n', e', Hq) -> WfCtx G -> DOk D n ->
     Good D n s D' n' /\ EvT T /\ HOk Hq /\
     (V (apC s G) D' n' e' T Hq /\ erase e' = e /\ lce 0 e')) /\
  (forall D G fs n s D' R n' fs' Hq, infer_fields f D G fs n = Some (s, D', R, n', fs', Hq) ->
     WfCtx G -> DOk D n ->
     Good D n s D' n' /\ EvR R /\ HOk Hq /\
     (VF (apC s G) D' n' fs' R Hq /\ erase_fields fs' = fs /\ lcef 0 fs')) /\
  (forall D G w Ts x res ars n s D' T n' ars' Hq,
     infer_arms f D G w Ts x res ars n = Some (s, D', T, n', ars', Hq) ->
     WfCtx G -> DOk D n -> Forall EvT Ts -> EvT res ->
     x `notin` dom G `union` fv_arms ars ->
     Good D n s D' n' /\ EvT T /\ T = apT s res /\ HOk Hq /\
     (VA (dom G `union` {{x}}) (apC s G) D' n' w (map (apT s) Ts) ars' T Hq /\
      erase_arms ars' = ars /\ lcea 0 ars')) /\
  (forall D G p Tp fs n s D' R n' fs' Hq,
     infer_obj f D G p Tp fs n = Some (s, D', R, n', fs', Hq) ->
     WfCtx G -> DOk D n -> EvT Tp -> p `notin` dom G `union` fv_fields fs ->
     Good D n s D' n' /\ EvR R /\ HOk Hq /\
     (VF (apC s G) D' n' fs' R Hq /\ erase_fields fs' = fs /\ lcef 0 fs' /\
      marks fs' = marks fs /\ meth_ty (apT s Tp) fs' R)).
Proof.
  induction f as [|f IH]; [ refine (conj _ (conj _ (conj _ _))); intros; discriminate | ].
  destruct IH as [IHe [IHf [IHa IHo]]]. refine (conj _ (conj _ (conj _ _))).
  - intros D G e n s D' T n' e' Hq H HG HD. cbn [infer] in H.
    destruct e as [i | x | k | d | | | b | e1 e2 | e1 e2 | fl el | fs | e1 l | | q | c0 a0 b0 | a1 o a2 | a3 | w1 tg1 a6 | w2 a7 ars2 | a8 l8 a9 | a10 l10 | a4 | a5];
      try discriminate H.
    + (* variable *)
      destruct (lookup x G) as [sc|] eqn:Hl; [|discriminate].
      destruct (instantiate D sc n) as [[T0 D1] n1] eqn:Hi.
      inversion H; try subst s; try subst D'; try subst T; try subst n'; try subst e'; try subst Hq; clear H.
      pose proof (lookup_binds _ _ _ Hl) as Hb.
      destruct (instantiate_sound _ _ _ _ _ _ Hi ((proj2 HG) _ _ Hb) HD) as (Hinst & Hev & HD1 & Hk).
      assert (Hle : n <= n1) by (unfold instantiate in Hi; inversion Hi; lia).
      split; [ exact (conj HD (conj OkS_id (conj HD1 (conj Hle (conj Hk Hk))))) | ].
      split; [exact Hev|]. split; [ exact HOk_nil | ].
      refine (conj _ (conj eq_refl I)).
      apply V_leaf; [ exact HG | ].
      eapply T_Var; [ exact (proj1 HG) | exact Hb | exact Hinst ].
    + (* numeral *)
      inversion H; try subst s; try subst D'; try subst T; try subst n'; try subst e'; try subst Hq; clear H.
      split; [ apply Good_upd; exact HD | ].
      split; [apply EvT_var, ev_ea|]. split; [ exact HOk_nil | ].
      refine (conj _ (conj eq_refl I)).
      apply V_leaf; [ exact HG | ].
      apply T_Num; [ exact (proj1 HG) | ].
      cbn [sat]. rewrite upd_same. apply finer_refl.
    + inversion H; try subst s; try subst D'; try subst T; try subst n'; try subst e'; try subst Hq; clear H.
      split; [apply Good_id; exact HD|]. split; [apply EvT_Float|]. split; [ exact HOk_nil | ].
      refine (conj _ (conj eq_refl I)). apply V_leaf; [ exact HG | ]. apply T_Dec. exact (proj1 HG).
    + inversion H; try subst s; try subst D'; try subst T; try subst n'; try subst e'; try subst Hq; clear H.
      split; [apply Good_id; exact HD|]. split; [apply EvT_Bool|]. split; [ exact HOk_nil | ].
      refine (conj _ (conj eq_refl I)). apply V_leaf; [ exact HG | ]. apply T_True. exact (proj1 HG).
    + inversion H; try subst s; try subst D'; try subst T; try subst n'; try subst e'; try subst Hq; clear H.
      split; [apply Good_id; exact HD|]. split; [apply EvT_Bool|]. split; [ exact HOk_nil | ].
      refine (conj _ (conj eq_refl I)). apply V_leaf; [ exact HG | ]. apply T_False. exact (proj1 HG).
    + (* abstraction *)
      destruct (infer f D ((fresh_var G b ~ sch_mono (typ_Var (ea n))) ++ G)
                  (open_exp_wrt_exp b (e_fvar_f (fresh_var G b))) (S n))
        as [[[[[[s0 D1] T0] n0] us0] H0]|] eqn:Ei; [|discriminate].
      inversion H; try subst s; try subst D'; try subst T; try subst n'; try subst e'; try subst Hq; clear H.
      assert (Hbeta : EvT (typ_Var (ea n))) by (apply EvT_var, ev_ea).
      assert (Hwf : WfCtx ((fresh_var G b ~ sch_mono (typ_Var (ea n))) ++ G))
        by (apply WfCtx_cons; [ exact HG | apply fresh_var_notin_dom | apply WfSch_mono; exact Hbeta ]).
      destruct (IHe _ _ _ _ _ _ _ _ _ _ Ei Hwf (DOk_mono D n (S n) HD (le_S _ _ (le_n n))))
        as (Gd0 & HT0 & HH0 & Hv & Her_Hty & Hlc_Hty).
      pose proof (Good_pre D n (S n) s0 D1 n0 (le_S _ _ (le_n n)) HD Gd0) as Gd.
      destruct Gd0 as (_ & Hs0 & _).
      destruct (bind_ok _ b _ Her_Hty Hlc_Hty (fresh_var_notin_fv G b)) as [Her' Hlc'].
      split; [exact Gd|]. split.
      { apply EvT_arrow; [ apply EvT_ap; auto | exact HT0 ]. }
      split; [ exact HH0 | ].
      refine (conj _ (conj _ Hlc')).
      2: { cbn [erase]. rewrite Her'. reflexivity. }
      rewrite apC_cons_mono in Hv.
      assert (Hxd : fresh_var G b `notin` dom (apC s0 G)).
      { pose proof (dom_apC s0 G) as Hd1. pose proof (fresh_var_notin_dom G b) as Hd2. fsetdec. }
      exact (V_abs _ _ _ _ _ _ _ _ Hv Hlc_Hty Hxd).
    + (* application *)
      destruct (infer f D G e1 n) as [[[[[[s1 D1] T1] n1] us1] H1]|] eqn:E1; [|discriminate].
      destruct (infer f D1 (apC s1 G) e2 n1) as [[[[[[s2 D2] T2] n2] us2] H2]|] eqn:E2; [|discriminate].
      destruct (unify_coD f D2 (apT s2 T1) (typ_Arrow T2 (typ_Var (ea n2))) (S n2))
        as [[[[s3 Du3] cs3] n3]|] eqn:E3; [|discriminate].
      inversion H; try subst s; try subst D'; try subst T; try subst n'; try subst e'; try subst Hq; clear H.
      destruct (IHe _ _ _ _ _ _ _ _ _ _ E1 HG HD) as (Gd1 & HT1 & HH1 & Hv1 & Her_Hty1 & Hlc_Hty1).
      pose proof Gd1 as (_ & Hs1 & HD1 & _).
      pose proof (WfCtx_ap s1 G Hs1 HG) as HG1.
      destruct (IHe _ _ _ _ _ _ _ _ _ _ E2 HG1 HD1) as (Gd2 & HT2 & HH2 & Hv2 & Her_Hty2 & Hlc_Hty2).
      pose proof Gd2 as (_ & Hs2 & HD2 & _).
      assert (Hbeta : EvT (typ_Var (ea n2))) by (apply EvT_var, ev_ea).
      destruct (unify_coD_sound _ _ _ _ _ _ _ _ _ E3 ltac:(dok) (EvT_ap s2 T1 Hs2 HT1)
                  (EvT_arrow _ _ HT2 Hbeta)) as (Hs3 & Hch & Hgu3).
      pose proof (GoodU_pre D2 n2 _ s3 Du3 n3 HD2 Hgu3 ltac:(lia)) as Gd3.
      split; [ exact (Good_comp _ _ _ _ _ _ _ _ (Good_comp _ _ _ _ _ _ _ _ Gd1 Gd2) Gd3) | ].
      split; [ apply EvT_ap; auto | ].
      split; [ exact (HOk_app _ _ (HOk_ap _ _ Hs3 (HOk_ap _ _ Hs2 HH1)) (HOk_ap _ _ Hs3 HH2)) | ].
      refine (conj _ (conj _ _)).
      2: { cbn [erase]. rewrite erase_coerce, Her_Hty1, Her_Hty2. reflexivity. }
      2: { cbn [lce]. split; [ apply lce_coerce; exact Hlc_Hty1 | exact Hlc_Hty2 ]. }
      rewrite <- !apC_comp.
      pose proof (V_coerce _ _ _ _ _ _ _ _ Hch
                    (V_push _ _ _ _ _ _ _ _ _ Gd3 (V_push _ _ _ _ _ _ _ _ _ Gd2 Hv1))) as Vf.
      exact (V_app _ _ _ _ _ _ _ _ _ Vf (V_push _ _ _ _ _ _ _ _ _ Gd3 Hv2)).
    + (* let *)
      destruct (infer f D G e1 n) as [[[[[[s1 D1] T1] n1] us1] H1]|] eqn:E1; [|discriminate].
      destruct (is_gen_value us1) eqn:Hgv.
      2: { (* a computed value: monomorphic *)
      destruct (infer f D1 ((fresh_var (apC s1 G) e2 ~ sch_mono T1) ++ apC s1 G)
                  (open_exp_wrt_exp e2 (e_fvar_f (fresh_var (apC s1 G) e2))) n1)
        as [[[[[[s2 D2] T2] n2] us2] H2]|] eqn:E2; [|discriminate].
      inversion H; try subst s; try subst D'; try subst T; try subst n'; try subst e'; try subst Hq; clear H.
      destruct (IHe _ _ _ _ _ _ _ _ _ _ E1 HG HD) as (Gd1 & HT1 & HH1 & Hv1 & Her_Hty1 & Hlc_Hty1).
      pose proof Gd1 as (_ & Hs1 & HD1 & _).
      pose proof (WfCtx_ap s1 G Hs1 HG) as HG1.
      assert (Hwf : WfCtx ((fresh_var (apC s1 G) e2 ~ sch_mono T1) ++ apC s1 G))
        by (apply WfCtx_cons; [ exact HG1 | apply fresh_var_notin_dom | apply WfSch_mono; exact HT1 ]).
      destruct (IHe _ _ _ _ _ _ _ _ _ _ E2 Hwf HD1) as (Gd2 & HT2 & HH2 & Hv2 & Her_Hty2 & Hlc_Hty2).
      pose proof Gd2 as (_ & Hs2 & _).
      destruct (bind_ok _ e2 _ Her_Hty2 Hlc_Hty2 (fresh_var_notin_fv (apC s1 G) e2)) as [Her' Hlc'].
      split; [ exact (Good_comp _ _ _ _ _ _ _ _ Gd1 Gd2) | ]. split; [ exact HT2 | ].
      split; [ exact (HOk_app _ _ (HOk_ap _ _ Hs2 HH1) HH2) | ].
      refine (conj _ (conj _ (conj Hlc_Hty1 Hlc'))).
      2: { cbn [erase]. rewrite Her_Hty1, Her'. reflexivity. }
      rewrite <- apC_comp.
      rewrite apC_cons_mono in Hv2.
      exact (V_letmono_step _ _ _ _ _ _ _ _ _ _ _ _ _ Gd2 Hv1 Hv2 Hlc_Hty2 (fresh_var_notin_dom (apC s1 G) e2)). }
      destruct (dis (S (length H1)) f D1 H1 n1) as [[[d Dd] nd]|] eqn:Edis; [|discriminate].
      destruct (infer f Dd
                  ((fresh_var (apC d (apC s1 G)) e2
                      ~ gen_ren Dd (pin_ctx (let_pin Dd us1 (apT d T1)) (apC d (apC s1 G))) (apT d T1))
                     ++ apC d (apC s1 G))
                  (open_exp_wrt_exp e2 (e_fvar_f (fresh_var (apC d (apC s1 G)) e2))) nd)
        as [[[[[[s2 D2] T2] n2] us2] H2]|] eqn:E2; [|discriminate].
      inversion H; try subst s; try subst D'; try subst T; try subst n'; try subst e'; try subst Hq; clear H.
      destruct (IHe _ _ _ _ _ _ _ _ _ _ E1 HG HD) as (Gd1 & HT1 & HH1 & Hv1 & Her_Hty1 & Hlc_Hty1).
      pose proof Gd1 as (_ & Hs1 & HD1 & _).
      pose proof (WfCtx_ap s1 G Hs1 HG) as HG1.
      destruct (dis_sound _ _ _ _ _ _ _ _ Edis HD1 HH1) as (Gdd & _).
      pose proof Gdd as (_ & Hsd & HDd & _).
      pose proof (WfCtx_ap d _ Hsd HG1) as HGd.
      pose proof (EvT_ap d T1 Hsd HT1) as HT1d.
      set (Tm := let_pin Dd us1 (apT d T1)) in *.
      set (Pz := (fresh_var (apC d (apC s1 G)) e2 ~ sch_mono Tm) ++ apC d (apC s1 G)).
      assert (HTm : EvT Tm) by (apply let_pin_EvT; exact HT1d).
      assert (HPz : WfCtx Pz)
        by (apply WfCtx_cons; [ exact HGd | apply fresh_var_notin_dom | apply WfSch_mono; exact HTm ]).
      assert (Hsc : gen_ren Dd (pin_ctx Tm (apC d (apC s1 G))) (apT d T1) = gen_ren Dd Pz (apT d T1))
        by reflexivity.
      rewrite Hsc in E2.
      pose proof (gen_ren_wf Dd Pz (apT d T1) HT1d) as Hwsc.
      assert (Hwf : WfCtx ((fresh_var (apC d (apC s1 G)) e2 ~ gen_ren Dd Pz (apT d T1)) ++ apC d (apC s1 G)))
        by (apply WfCtx_cons; [ exact HGd | apply fresh_var_notin_dom | exact Hwsc ]).
      destruct (IHe _ _ _ _ _ _ _ _ _ _ E2 Hwf HDd) as (Gd2 & HT2 & HH2 & Hv2 & Her_Hty2 & Hlc_Hty2).
      destruct (bind_ok _ e2 _ Her_Hty2 Hlc_Hty2 (fresh_var_notin_fv (apC d (apC s1 G)) e2)) as [Her' Hlc'].
      split; [ exact (Good_comp _ _ _ _ _ _ _ _ (Good_comp _ _ _ _ _ _ _ _ Gd1 Gdd) Gd2) | ].
      split; [ exact HT2 | ]. split; [ exact HH2 | ].
      refine (conj _ (conj _ (conj Hlc_Hty1 Hlc'))).
      2: { cbn [erase]. rewrite Her_Hty1, Her'. reflexivity. }
      rewrite <- !apC_comp.
      assert (Hxd : fresh_var (apC d (apC s1 G)) e2 `notin` dom (apC s1 G)).
      { pose proof (dom_apC d (apC s1 G)) as Hd1.
        pose proof (fresh_var_notin_dom (apC d (apC s1 G)) e2) as Hd2. fsetdec. }
      exact (V_let_dis (S (length H1)) f D1 n1 (apC s1 G) us1 T1 H1 d Dd nd
               (fresh_var (apC d (apC s1 G)) e2) _ s2 D2 n2 T2 H2
               Hv1 Edis HH1 HG1 HD1 HT1 Hgv Hxd Hlc_Hty2 Gd2 Hv2).
    + (* recursive group *)
      destruct (is_fn_group fl) eqn:Hfg; [|discriminate].
      set (p := fresh_var G (e_rec fl)) in *.
      set (R0 := group_row fl n) in *.
      destruct (infer_fields f D ((p ~ sch_mono (typ_Record R0)) ++ G)
                  (open_fields_wrt_exp fl (e_fvar_f p)) (n + nfields fl))
        as [[[[[[s1 D1] R1] n1] us1] H1]|] eqn:E1; [|discriminate].
      destruct (unify_grp f D1 us1 R1 (apR s1 R0) n1) as [[[[s2 D2] n2] us2]|] eqn:E2; [|discriminate].
      destruct (dis (S (length (apH s2 H1))) f D2 (apH s2 H1) n2) as [[[d Dd] nd]|] eqn:Edis; [|discriminate].
      set (sg := scomp d (scomp s2 s1)) in *.
      set (G1 := apC sg G) in *.
      set (Rf := apR sg R0) in *.
      set (q := fresh_var G1 el) in *.
      destruct (infer f Dd ((q ~ gen_ren Dd G1 (typ_Record Rf)) ++ G1)
                  (open_exp_wrt_exp el (e_fvar_f q)) nd)
        as [[[[[[s3 D3] T3] n3] us3] H3]|] eqn:E3; [|discriminate].
      inversion H; try subst s; try subst D'; try subst T; try subst n'; try subst e'; try subst Hq; clear H.
      assert (HR0 : EvR R0) by apply EvR_group_row.
      assert (Hwf0 : WfCtx ((p ~ sch_mono (typ_Record R0)) ++ G))
        by (apply WfCtx_cons; [ exact HG | apply fresh_var_notin_dom | apply WfSch_mono, EvT_Record; exact HR0 ]).
      assert (Hnn : n <= n + nfields fl) by lia.
      destruct (IHf _ _ _ _ _ _ _ _ _ _ E1 Hwf0 (DOk_mono D n _ HD Hnn))
        as (Gd1' & HR1 & HH1 & Hvf1 & Her_Hty1 & Hlc_Hty1).
      pose proof (Good_pre D n _ s1 D1 n1 Hnn HD Gd1') as Gd1.
      pose proof Gd1 as (_ & Hs1 & HD1 & Hl1 & Hi1 & Hk1).
      pose proof (WfCtx_ap s1 G Hs1 HG) as HG1.
      pose proof (EvR_ap s1 _ Hs1 HR0) as HR0'.
      destruct (unify_grp_sound f D1 _ _ _ _ _ _ _ _ E2 HR1 HR0') as (Hs2 & Hpw & Hgu2 & Her_u & Hlc_u & Hfg_u).
      pose proof (GoodU_pre D1 n1 _ s2 D2 n2 HD1 Hgu2 ltac:(lia)) as Gd2.
      pose proof (Good_dok _ _ _ _ _ Gd2) as HD2.
      pose proof (VF_push _ _ _ _ _ _ _ _ _ Gd2 Hvf1) as Hvf2.
      pose proof (VF_pw _ _ _ _ _ _ _ _ Hpw (fun S HS => pw_co_ap S _ _ _ _ HS Hpw) Hvf2) as Hvf3.
      destruct (VF_dis _ f _ _ _ _ _ _ _ _ _ Hvf3 Edis HD2 (HOk_ap _ _ Hs2 HH1)) as (Gdd & Hfd).
      pose proof Gdd as (_ & Hsd & HDd & _).
      pose proof (Good_comp _ _ _ _ _ _ _ _ Gd1 Gd2) as Gd21.
      pose proof (Good_comp _ _ _ _ _ _ _ _ Gd21 Gdd) as Gdg.
      assert (Hsg : OkS sg) by (destruct Gdg as (_ & H21 & _); exact H21).
      assert (HRf : EvR Rf) by (apply EvR_ap; assumption).
      assert (HG21 : WfCtx G1) by (apply WfCtx_ap; assumption).
      assert (Hty3 : field_typing Dd ((p ~ sch_mono (typ_Record Rf)) ++ G1) us2 Rf).
      { assert (Hc : apC d (apC s2 (apC s1 ((p ~ sch_mono (typ_Record R0)) ++ G)))
                     = (p ~ sch_mono (typ_Record Rf)) ++ G1).
        { rewrite !apC_app, !apC_single, !apS_mono.
          unfold G1, Rf, sg. rewrite (apC_comp s2 s1 G), (apC_comp d (scomp s2 s1) G).
          rewrite (apT_comp s2 s1), (apT_comp d (scomp s2 s1)). reflexivity. }
        assert (Hr : apR d (apR s2 (apR s1 R0)) = Rf).
        { unfold Rf, sg. rewrite (apR_comp s2 s1), (apR_comp d (scomp s2 s1)). reflexivity. }
        rewrite Hc, Hr in Hfd. exact Hfd. }
      pose proof (gen_ren_wf Dd G1 (typ_Record Rf) (proj2 (EvT_Record _) HRf)) as Hwsc.
      assert (Hwf1 : WfCtx ((q ~ gen_ren Dd G1 (typ_Record Rf)) ++ G1))
        by (apply WfCtx_cons; [ exact HG21 | apply fresh_var_notin_dom | exact Hwsc ]).
      destruct (IHe _ _ _ _ _ _ _ _ _ _ E3 Hwf1 HDd) as (Gd3 & HT3 & HH3 & Hv3 & Her_Hty4 & Hlc_Hty4).
      pose proof (Good_comp _ _ _ _ _ _ _ _ Gdg Gd3) as Gdf.
      destruct (bind_ok_fields p fl _ (eq_trans Her_u Her_Hty1) (Hlc_u Hlc_Hty1) (fresh_var_notin_fv G (e_rec fl)))
        as [Herf Hlcf].
      destruct (bind_ok q el _ Her_Hty4 Hlc_Hty4 (fresh_var_notin_fv G1 el)) as [Herb Hlcb].
      split; [ exact Gdf | ]. split; [ exact HT3 | ]. split; [ exact HH3 | ].
      refine (conj _ (conj _ (conj Hlcf Hlcb))).
      2: { cbn [erase]. rewrite Herf, Herb. reflexivity. }
      rewrite <- apC_comp. fold G1.
      exact (V_letrec Dd nd G1 p q Rf us2 us3 s3 D3 n3 T3 H3 HG21 HDd HRf
               (fn_group_clf _ _ _ (Hfg_u (infer_fields_fn_group _ _ _ _ _ _ _ _ _ _ _
                  (is_fn_group_open_rec fl 0 (e_fvar_f p) Hfg) E1)))
               (Hlc_u Hlc_Hty1) Hlc_Hty4
               ltac:(unfold G1; rewrite dom_apC; apply fresh_var_notin_dom)
               ltac:(apply fresh_var_notin_dom) Hty3 Gd3 Hv3).
    + (* record *)
      destruct (no_meth fs) eqn:Hnm.
      all: try (rewrite Hnm in H).
      * destruct (infer_fields f D G fs n) as [[[[[[s0 D1] R0] n0] us0] H0]|] eqn:Ei; [|discriminate].
        inversion H; try subst s; try subst D'; try subst T; try subst n'; try subst e'; try subst Hq; clear H.
        destruct (IHf _ _ _ _ _ _ _ _ _ _ Ei HG HD) as (Gd0 & HR0 & HH0 & Hv & Her_Hty & Hlc_Hty).
        split; [exact Gd0|]. split; [ apply EvT_Record; exact HR0 | ]. split; [ exact HH0 | ].
        refine (conj _ (conj _ Hlc_Hty)).
        2: { cbn [erase]. rewrite Her_Hty. reflexivity. }
        apply V_record; [ exact Hv | eapply infer_fields_no_meth; exact Ei ].
      * (* methods share one receiver *)
        set (p := fresh_var G (e_rec fs)) in *.
        set (Tp := typ_Record (obj_row fs n (row_Var (ea (n + nfields fs))))) in *.
        destruct (infer_obj f D G p Tp fs (S (n + nfields fs)))
          as [[[[[[s1 D1] R1] n1] fs1] H1]|] eqn:Eo; [|discriminate].
        destruct (tie_obj f D1 fs1 R1 (apR s1 (group_row fs n)) n1) as [[[[s2 D2] n2] fs2]|] eqn:Et; [|discriminate].
        inversion H; try subst s; try subst D'; try subst T; try subst n'; try subst e'; try subst Hq; clear H.
        assert (HTp : EvT Tp) by (apply EvT_Record; apply EvR_obj_row).
        assert (Hle : n <= S (n + nfields fs)) by lia.
        assert (Hpd : p `notin` dom G) by apply fresh_var_notin_dom.
        assert (Hpf : p `notin` fv_exp (e_rec fs)) by apply fresh_var_notin_fv.
        simpl in Hpf.
        destruct (IHo _ _ _ _ _ _ _ _ _ _ _ _ Eo HG (DOk_mono D n _ HD Hle) HTp
                    ltac:(fsetdec))
          as (Gd1' & HR1 & HH1 & Hvf1 & Her1 & Hlc1 & Hmk1 & Hmt1).
        pose proof (Good_pre D n _ s1 D1 n1 Hle HD Gd1') as Gd1.
        pose proof Gd1 as (_ & Hs1 & HD1 & _).
        pose proof (WfCtx_ap s1 G Hs1 HG) as HG1.
        destruct (tie_obj_V _ _ _ _ _ _ _ _ _ _ Et (apC s1 G) H1 (proj1 HG1) HD1 HR1
                    (EvR_ap _ _ Hs1 (EvR_group_row fs n)) Hvf1 Hlc1)
          as (Gd2 & Hvf2 & Her2 & Hlc2 & Hmk2 & Hmr2).
        pose proof Gd2 as (_ & Hs2 & _).
        pose proof (OkS_comp _ _ Hs2 Hs1) as Hs21.
        split; [ exact (Good_comp _ _ _ _ _ _ _ _ Gd1 Gd2) | ].
        split; [ apply EvT_Record; apply EvR_ap; [ exact Hs21 | apply EvR_group_row ] | ].
        split; [ exact (HOk_ap _ _ Hs2 HH1) | ].
        refine (conj _ (conj _ Hlc2)).
        2: { cbn [erase]. rewrite Her2, Her1. reflexivity. }
        rewrite <- apC_comp, <- apR_comp.
        assert (Hap : apT s2 (apT s1 Tp)
                      = typ_Record (row_tail_with (apR s2 (apR s1 (group_row fs n)))
                                                  (apR s2 (apR s1 (row_Var (ea (n + nfields fs))))))).
        { subst Tp. rewrite apT_comp, apT_Record, obj_row_ap, <- !apR_comp. reflexivity. }
        refine (V_obj _ _ _ _ _ (apR s2 (apR s1 (row_Var (ea (n + nfields fs))))) _ Hvf2
                  (rsp_apR _ _ (rsp_apR _ _ (rsp_group_row fs n))) _).
        eapply meths_shared_of.
        { exact Hmr2. }
        { exact (meth_ty_ap s2 _ _ _ Hmt1). }
        { exact Hap. }
        { exact Hmk2. }
    + (* projection *)
      destruct (infer f D G e1 n) as [[[[[[s1 D1] T1] n1] us1] H1]|] eqn:E1; [|discriminate].
      destruct (unify_coD f D1 T1 (typ_Record (row_Ext l (typ_Var (ea n1)) (row_Var (ea (S n1)))))
                  (n1 + 2)) as [[[[s2 Du2] cs2] n2]|] eqn:E2; [|discriminate].
      inversion H; try subst s; try subst D'; try subst T; try subst n'; try subst e'; try subst Hq; clear H.
      destruct (IHe _ _ _ _ _ _ _ _ _ _ E1 HG HD) as (Gd1 & HT1 & HH1 & Hv1 & Her_Hty1 & Hlc_Hty1).
      pose proof Gd1 as (_ & Hs1 & HD1 & _).
      assert (Hrow : EvT (typ_Record (row_Ext l (typ_Var (ea n1)) (row_Var (ea (S n1)))))).
      { apply EvT_Record, EvR_ext; [ apply EvT_var, ev_ea | apply EvR_var, ev_ea ]. }
      destruct (unify_coD_sound _ _ _ _ _ _ _ _ _ E2 ltac:(dok) HT1 Hrow) as (Hs2 & Hch & Hgu2).
      pose proof (GoodU_pre D1 n1 _ s2 Du2 n2 HD1 Hgu2 ltac:(lia)) as Gd2.
      split; [ exact (Good_comp _ _ _ _ _ _ _ _ Gd1 Gd2) | ].
      split; [ apply EvT_ap; [exact Hs2 | apply EvT_var, ev_ea] | ].
      split; [ exact (HOk_ap _ _ Hs2 HH1) | ].
      refine (conj _ (conj _ _)).
      2: { cbn [erase]. rewrite erase_coerce, Her_Hty1. reflexivity. }
      2: { cbn [lce]. apply lce_coerce. exact Hlc_Hty1. }
      rewrite <- apC_comp.
      exact (V_proj _ _ _ _ _ _ _ _
               (V_coerce _ _ _ _ _ _ _ _ Hch (V_push _ _ _ _ _ _ _ _ _ Gd2 Hv1))).
    + inversion H; try subst s; try subst D'; try subst T; try subst n'; try subst e'; try subst Hq; clear H.
      split; [apply Good_id; exact HD|]. split; [apply EvT_Unit|]. split; [ exact HOk_nil | ].
      refine (conj _ (conj eq_refl I)). apply V_leaf; [ exact HG | ]. apply T_Unit. exact (proj1 HG).
    + inversion H; try subst s; try subst D'; try subst T; try subst n'; try subst e'; try subst Hq; clear H.
      split; [apply Good_id; exact HD|]. split; [apply EvT_String|]. split; [ exact HOk_nil | ].
      refine (conj _ (conj eq_refl I)). apply V_leaf; [ exact HG | ]. apply T_Str. exact (proj1 HG).
    + (* conditional *)
      destruct (infer f D G c0 n) as [[[[[[s1 D1] T1] n1] us1] H1]|] eqn:E1; [|discriminate].
      destruct (unify_coD f D1 T1 typ_Bool n1) as [[[[s2 Du2] cs2] n2]|] eqn:E2; [|discriminate].
      destruct (infer f Du2 (apC s2 (apC s1 G)) a0 n2) as [[[[[[s3 D3] T2] n3] us3] H2]|] eqn:E3; [|discriminate].
      destruct (infer f D3 (apC s3 (apC s2 (apC s1 G))) b0 n3) as [[[[[[s4 D4] T3] n4] us4] H3]|] eqn:E4;
        [|discriminate].
      destruct (unify_coD f D4 (apT s4 T2) T3 n4) as [[[[s5 Du5] cs5] n5]|] eqn:E5; [|discriminate].
      inversion H; try subst s; try subst D'; try subst T; try subst n'; try subst e'; try subst Hq; clear H.
      destruct (IHe _ _ _ _ _ _ _ _ _ _ E1 HG HD) as (Gd1 & HT1 & HH1 & Hv1 & Her_Hty1 & Hlc_Hty1).
      pose proof Gd1 as (_ & Hs1 & HD1 & _).
      pose proof (WfCtx_ap s1 G Hs1 HG) as HG1.
      destruct (unify_coD_sound _ _ _ _ _ _ _ _ _ E2 ltac:(dok) HT1 EvT_Bool) as (Hs2 & Hch2 & Hgu2).
      pose proof (GoodU_pre D1 n1 _ s2 Du2 n2 HD1 Hgu2 ltac:(lia)) as Gd2.
      pose proof (WfCtx_ap s2 _ Hs2 HG1) as HG2.
      assert (HD2 : DOk Du2 n2) by (destruct Gd2 as (_ & _ & H2' & _); exact H2').
      destruct (IHe _ _ _ _ _ _ _ _ _ _ E3 HG2 HD2) as (Gd3 & HT2 & HH2 & Hv2 & Her_Hty2 & Hlc_Hty2).
      pose proof Gd3 as (_ & Hs3 & HD3 & _).
      pose proof (WfCtx_ap s3 _ Hs3 HG2) as HG3.
      destruct (IHe _ _ _ _ _ _ _ _ _ _ E4 HG3 HD3) as (Gd4 & HT3 & HH3 & Hv3 & Her_Hty3 & Hlc_Hty3).
      pose proof Gd4 as (_ & Hs4 & HD4 & _).
      destruct (unify_coD_sound _ _ _ _ _ _ _ _ _ E5 ltac:(dok) (EvT_ap s4 T2 Hs4 HT2) HT3)
        as (Hs5 & Hch5 & Hgu5).
      pose proof ((proj2 Hgu5) HD4) as Gd5.
      split; [ exact (Good_comp _ _ _ _ _ _ _ _ (Good_comp _ _ _ _ _ _ _ _ (Good_comp _ _ _ _ _ _ _ _
                 (Good_comp _ _ _ _ _ _ _ _ Gd1 Gd2) Gd3) Gd4) Gd5) | ].
      split; [ apply EvT_ap; auto | ].
      split.
      { apply HOk_app; [ exact (HOk_ap _ _ Hs5 (HOk_ap _ _ Hs4 (HOk_ap _ _ Hs3 (HOk_ap _ _ Hs2 HH1)))) | ].
        apply HOk_app; [ exact (HOk_ap _ _ Hs5 (HOk_ap _ _ Hs4 HH2)) | exact (HOk_ap _ _ Hs5 HH3) ]. }
      refine (conj _ (conj _ _)).
      2: { cbn [erase]. rewrite !erase_coerce, Her_Hty1, Her_Hty2, Her_Hty3. reflexivity. }
      2: { cbn [lce]. split; [ apply lce_coerce; exact Hlc_Hty1 | split; [ apply lce_coerce; exact Hlc_Hty2 | exact Hlc_Hty3 ] ]. }
      rewrite <- !apC_comp.
      pose proof (V_coerce _ _ _ _ _ _ _ _ Hch2 (V_push _ _ _ _ _ _ _ _ _ Gd2 Hv1)) as Vc.
      refine (V_if _ _ _ _ _ _ _ _ _ _
                (V_push _ _ _ _ _ _ _ _ _ Gd5 (V_push _ _ _ _ _ _ _ _ _ Gd4 (V_push _ _ _ _ _ _ _ _ _ Gd3 Vc)))
                (V_coerce _ _ _ _ _ _ _ _ Hch5 (V_push _ _ _ _ _ _ _ _ _ Gd5 (V_push _ _ _ _ _ _ _ _ _ Gd4 Hv2)))
                (V_push _ _ _ _ _ _ _ _ _ Gd5 Hv3)).
    + (* binary operation *)
      destruct (infer f D G a1 n) as [[[[[[s1 D1] T1] n1] us1] H1]|] eqn:E1; [|discriminate].
      destruct (infer f D1 (apC s1 G) a2 n1) as [[[[[[s2 D2] T2] n2] us2] H2]|] eqn:E2; [|discriminate].
      destruct (IHe _ _ _ _ _ _ _ _ _ _ E1 HG HD) as (Gd1 & HT1 & HH1 & Hv1 & Her_Hty1 & Hlc_Hty1).
      pose proof Gd1 as (_ & Hs1 & HD1 & _).
      pose proof (WfCtx_ap s1 G Hs1 HG) as HG1.
      destruct (IHe _ _ _ _ _ _ _ _ _ _ E2 HG1 HD1) as (Gd2 & HT2 & HH2 & Hv2 & Her_Hty2 & Hlc_Hty2).
      pose proof Gd2 as (_ & Hs2 & HD2 & _).
      destruct (is_cmp_op o) eqn:Hcmp.
      { (* a comparison: the operands meet first, then the joined type must be [Eq] *)
        assert (Hk : kind o = k_cmp)
          by (unfold is_cmp_op in Hcmp; destruct (kind o); first [ reflexivity | discriminate Hcmp ]).
        destruct (unify_coD f D2 (apT s2 T1) T2 n2) as [[[[s3 Du3] cs3] n3]|] eqn:E3; [|discriminate].
        set (D3' := upd Du3 (ea n3) k_Eq) in *.
        destruct (unify_coD f D3' (apT s3 T2) (typ_Var (ea n3)) (S n3)) as [[[[s4 Du4] cs4] n4]|] eqn:E4; [|discriminate].
        inversion H; try subst s; try subst D'; try subst T; try subst n'; try subst e'; try subst Hq; clear H.
        assert (HN : D3' (ea n3) = k_Eq) by (unfold D3'; apply upd_same).
        assert (HEc : EvT (typ_Var (ea n3))) by (apply EvT_var, ev_ea).
        destruct (unify_coD_sound _ _ _ _ _ _ _ _ _ E3 ltac:(dok) (EvT_ap s2 T1 Hs2 HT1) HT2)
          as (Hs3 & Hch3 & Hgu3).
        pose proof (GoodU_pre D2 n2 _ s3 Du3 n3 HD2 Hgu3 ltac:(lia)) as Gd3.
        pose proof (Good_upd Du3 n3 k_Eq (Good_dok _ _ _ _ _ Gd3)) as GdU.
        fold D3' in GdU.
        assert (HD3' : DOk D3' (S n3)) by (destruct GdU as (_ & _ & H2' & _); exact H2').
        destruct (unify_coD_sound _ _ _ _ _ _ _ _ _ E4 ltac:(dok) (EvT_ap s3 T2 Hs3 HT2) HEc)
          as (Hs4 & Hch4 & Hgu4).
        pose proof ((proj2 Hgu4) HD3') as Gd4.
        split.
        { exact (Good_comp _ _ _ _ _ _ _ _ (Good_comp _ _ _ _ _ _ _ _ (Good_comp _ _ _ _ _ _ _ _ Gd1 Gd2) Gd3)
                   (Good_lift _ _ _ _ _ _ _ GdU Gd4)). }
        split; [ exact EvT_Bool | ].
        split; [ exact (HOk_app _ _ (HOk_ap _ _ Hs4 (HOk_ap _ _ Hs3 (HOk_ap _ _ Hs2 HH1)))
                          (HOk_ap _ _ Hs4 (HOk_ap _ _ Hs3 HH2))) | ].
        refine (conj _ (conj _ _)).
        2: { cbn [erase]. rewrite !erase_coerce, Her_Hty1, Her_Hty2. reflexivity. }
        2: { cbn [lce]. split; [ apply lce_coerce, lce_coerce; assumption | apply lce_coerce; assumption ]. }
        rewrite <- !apC_comp.
        assert (Hsat : sat Du4 k_Eq (apT s4 (typ_Var (ea n3)))).
        { pose proof (Good_kres _ _ _ _ _ Gd4 (ea n3)) as H3. rewrite HN in H3. exact H3. }
        pose proof (V_push _ _ _ _ _ _ _ _ _ Gd3 (V_push _ _ _ _ _ _ _ _ _ Gd2 Hv1)) as V13.
        pose proof (V_coerce _ _ _ _ _ _ _ _ Hch3 V13) as V13c.
        pose proof (V_coerce _ _ _ _ _ _ _ _ Hch4
                      (V_push _ _ _ _ _ _ _ _ _ Gd4 (V_refine _ _ _ _ _ _ _ _ GdU V13c))) as Vl.
        pose proof (V_coerce _ _ _ _ _ _ _ _ Hch4
                      (V_push _ _ _ _ _ _ _ _ _ Gd4
                         (V_refine _ _ _ _ _ _ _ _ GdU (V_push _ _ _ _ _ _ _ _ _ Gd3 Hv2)))) as Vr.
        exact (V_bin _ _ _ _ _ _ _ _ _ _ _ Vl Vr (sig_cmp Du4 o _ Hk Hsat)). }
      * (* [+ - * // % /]: both operands at one variable's type, of the operator's sort *)
        assert (Hko : kind o = k_ring \/ kind o = k_quot \/ kind o = k_whole \/ kind o = k_cmp)
          by (destruct (kind o); [ left; reflexivity | right; left; reflexivity | right; right; left; reflexivity | right; right; right; reflexivity ]).
        set (D2' := upd D2 (ea n2) (generic_sort o)) in *.
        destruct (unify_coD f D2' (apT s2 T1) (typ_Var (ea n2)) (S n2)) as [[[[s3 Du3] cs3] n3]|] eqn:E3; [|discriminate].
        destruct (unify_coD f Du3 (apT s3 T2) (apT s3 (typ_Var (ea n2))) n3) as [[[[s4 Du4] cs4] n4]|] eqn:E4; [|discriminate].
        inversion H; try subst s; try subst D'; try subst T; try subst n'; try subst e'; try subst Hq; clear H.
        assert (HN : D2' (ea n2) = generic_sort o) by (unfold D2'; apply upd_same).
        assert (HEc : EvT (typ_Var (ea n2))) by (apply EvT_var, ev_ea).
        pose proof (Good_upd D2 n2 (generic_sort o) HD2) as GdU.
        fold D2' in GdU.
        assert (HD2' : DOk D2' (S n2)) by (destruct GdU as (_ & _ & H2' & _); exact H2').
        destruct (unify_coD_sound _ _ _ _ _ _ _ _ _ E3 ltac:(dok) (EvT_ap s2 T1 Hs2 HT1) HEc)
          as (Hs3 & Hch3 & Hgu3).
        pose proof ((proj2 Hgu3) HD2') as Gd3.
        destruct (unify_coD_sound _ _ _ _ _ _ _ _ _ E4 ltac:(dok) (EvT_ap s3 T2 Hs3 HT2)
                    (EvT_ap s3 _ Hs3 HEc)) as (Hs4 & Hch4 & Hgu4).
        pose proof ((proj2 Hgu4) (Good_dok _ _ _ _ _ Gd3)) as Gd4.
        split.
        { exact (Good_comp _ _ _ _ _ _ _ _ (Good_comp _ _ _ _ _ _ _ _ (Good_comp _ _ _ _ _ _ _ _ Gd1 Gd2)
                   (Good_lift _ _ _ _ _ _ _ GdU Gd3)) Gd4). }
        split.
        { unfold bin_res. destruct (kind o);
            first [ apply EvT_Bool | (apply EvT_ap; [ exact Hs4 | apply EvT_ap; [ exact Hs3 | exact HEc ] ]) ]. }
        split; [ exact (HOk_app _ _ (HOk_ap _ _ Hs4 (HOk_ap _ _ Hs3 (HOk_ap _ _ Hs2 HH1)))
                          (HOk_ap _ _ Hs4 (HOk_ap _ _ Hs3 HH2))) | ].
        refine (conj _ (conj _ _)).
        2: { cbn [erase]. rewrite !erase_coerce, Her_Hty1, Her_Hty2. reflexivity. }
        2: { cbn [lce]. split; apply lce_coerce; assumption. }
        rewrite <- !apC_comp.
        assert (Hsat : sat Du4 (generic_sort o) (apT s4 (apT s3 (typ_Var (ea n2))))).
        { pose proof (Good_kres _ _ _ _ _ Gd3 (ea n2)) as H3. rewrite HN in H3.
          exact (sat_ap Du3 Du4 (generic_sort o) _ (sT s4) (sR s4) (Good_kres _ _ _ _ _ Gd4)
                   (Good_rkres _ _ _ _ _ Gd4) H3). }
        pose proof (V_coerce _ _ _ _ _ _ _ _ Hch3
                      (V_push _ _ _ _ _ _ _ _ _ Gd3 (V_refine _ _ _ _ _ _ _ _ GdU
                         (V_push _ _ _ _ _ _ _ _ _ Gd2 Hv1)))) as V13c.
        pose proof (V_coerce _ _ _ _ _ _ _ _ Hch4
                      (V_push _ _ _ _ _ _ _ _ _ Gd4 (V_push _ _ _ _ _ _ _ _ _ Gd3
                         (V_refine _ _ _ _ _ _ _ _ GdU Hv2)))) as Vr.
        pose proof (V_push _ _ _ _ _ _ _ _ _ Gd4 V13c) as Vl.
        assert (Hsig : bin_sig Du4 o (apT s4 (apT s3 (typ_Var (ea n2)))) (apT s4 (apT s3 (typ_Var (ea n2))))
                         (bin_res o (apT s4 (apT s3 (typ_Var (ea n2)))))).
        { unfold bin_res, generic_sort in *. destruct Hko as [Hko | [Hko | [Hko | Hko]]]; rewrite Hko in *;
             first [ (apply sig_ring; assumption) | (apply sig_whole; assumption) | (apply sig_cmp; assumption)
                   | (assert (Ho : o = bop_div) by (destruct o; first [ reflexivity | discriminate Hko ]);
                      rewrite Ho; apply sig_quot; assumption) ]. }
        exact (V_bin _ _ _ _ _ _ _ _ _ _ _ Vl Vr Hsig).
    + (* Int-to-Float coercion at any Numeric type *)
      destruct (infer f D G a3 n) as [[[[[[s1 D1] T1] n1] us1] H1]|] eqn:E1; [|discriminate].
      set (D1' := upd D1 (ea n1) k_Literal) in *.
      destruct (unify_coD f D1' T1 (typ_Var (ea n1)) (S n1)) as [[[[s2 Du2] cs2] n2]|] eqn:E2; [|discriminate].
      inversion H; try subst s; try subst D'; try subst T; try subst n'; try subst e'; try subst Hq; clear H.
      destruct (IHe _ _ _ _ _ _ _ _ _ _ E1 HG HD) as (Gd1 & HT1 & HH1 & Hv1 & Her_Hty1 & Hlc_Hty1).
      pose proof Gd1 as (_ & Hs1 & HD1 & _).
      assert (HN : D1' (ea n1) = k_Literal) by (unfold D1'; apply upd_same).
      assert (HEc : EvT (typ_Var (ea n1))) by (apply EvT_var, ev_ea).
      pose proof (Good_upd D1 n1 k_Literal HD1) as GdU. fold D1' in GdU.
      assert (HD1' : DOk D1' (S n1)) by (destruct GdU as (_ & _ & H2' & _); exact H2').
      destruct (unify_coD_sound _ _ _ _ _ _ _ _ _ E2 ltac:(dok) HT1 HEc) as (Hs2 & Hch & Hgu2).
      pose proof ((proj2 Hgu2) HD1') as Gd2.
      split; [ exact (Good_comp _ _ _ _ _ _ _ _ Gd1 (Good_lift _ _ _ _ _ _ _ GdU Gd2)) | ].
      split; [ apply EvT_Float | ].
      split; [ exact (HOk_ap _ _ Hs2 HH1) | ].
      refine (conj _ (conj _ _)).
      2: { cbn [erase]. rewrite erase_coerce, Her_Hty1. reflexivity. }
      2: { cbn [lce]. apply lce_coerce. exact Hlc_Hty1. }
      rewrite <- apC_comp.
      refine (V_tofloat _ _ _ _ (apT s2 (typ_Var (ea n1))) _
                (V_coerce _ _ _ _ _ _ _ _ Hch
                   (V_push _ _ _ _ _ _ _ _ _ Gd2 (V_refine _ _ _ _ _ _ _ _ GdU Hv1))) _).
      pose proof (Good_kres _ _ _ _ _ Gd2 (ea n1)) as H3. rewrite HN in H3. exact H3.
    + (* tag construction *)
      destruct (Nat.ltb tg1 (length (gtags w1))) eqn:Hlt; [|discriminate].
      destruct (infer f D G a6 n) as [[[[[[s1 D1] T1] n1] us1] H1]|] eqn:E1; [|discriminate].
      destruct (unify_coD f D1 T1 (tag_payload w1 (fresh_tys n1 (nparams w1)) tg1) (n1 + nparams w1))
        as [[[[s2 Du2] cs2] n2]|] eqn:E2; [|discriminate].
      inversion H; try subst s; try subst D'; try subst T; try subst n'; try subst e'; try subst Hq; clear H.
      destruct (IHe _ _ _ _ _ _ _ _ _ _ E1 HG HD) as (Gd1 & HT1 & HH1 & Hv1 & Her_Hty1 & Hlc_Hty1).
      pose proof Gd1 as (_ & Hs1 & HD1 & _).
      pose proof (EvT_fresh_tys (nparams w1) n1) as HTs.
      destruct (unify_coD_sound _ _ _ _ _ _ _ _ _ E2 ltac:(dok) HT1 (EvT_tag_payload _ _ _ HTs))
        as (Hs2 & Hch & Hgu2).
      pose proof ((proj2 Hgu2) (DOk_mono D1 n1 (n1 + nparams w1) HD1 ltac:(lia))) as Gd2'.
      pose proof (Good_pre D1 n1 (n1 + nparams w1) s2 Du2 n2 ltac:(lia) HD1 Gd2') as Gd2.
      split; [ exact (Good_comp _ _ _ _ _ _ _ _ Gd1 Gd2) | ].
      split; [ apply EvT_ap; [ exact Hs2 | apply EvT_grp, EvT_spine; exact HTs ] | ].
      split; [ exact (HOk_ap _ _ Hs2 HH1) | ].
      refine (conj _ (conj _ _)).
      2: { cbn [erase]. rewrite erase_coerce, Her_Hty1. reflexivity. }
      2: { cbn [lce]. apply lce_coerce. exact Hlc_Hty1. }
      rewrite <- apC_comp. rewrite apT_grp, apT_spine.
      apply V_con; [ apply Nat.ltb_lt; exact Hlt | ].
      rewrite <- apT_tag_payload.
      exact (V_coerce _ _ _ _ _ _ _ _ Hch (V_push _ _ _ _ _ _ _ _ _ Gd2 Hv1)).
    + (* match *)
      destruct (arms_wf_b w2 ars2) eqn:Hwb; [|discriminate].
      destruct (infer f D G a7 n) as [[[[[[s1 D1] T1] n1] us1] H1]|] eqn:E1; [|discriminate].
      destruct (unify_coD f D1 T1 (typ_Grp w2 (spine (fresh_tys n1 (nparams w2)))) (n1 + nparams w2))
        as [[[[s2 Du2] cs2] n2]|] eqn:E2; [|discriminate].
      destruct (infer_arms f Du2 (apC s2 (apC s1 G)) w2 (map (apT s2) (fresh_tys n1 (nparams w2)))
                  (fresh_var G (e_match w2 a7 ars2)) (typ_Var (ea n2)) ars2 (S n2))
        as [[[[[[s3 D3] T3] n3] us3] H3]|] eqn:E3; [|discriminate].
      inversion H; try subst s; try subst D'; try subst T; try subst n'; try subst e'; try subst Hq; clear H.
      destruct (IHe _ _ _ _ _ _ _ _ _ _ E1 HG HD) as (Gd1 & HT1 & HH1 & Hv1 & Her_Hty1 & Hlc_Hty1).
      pose proof Gd1 as (_ & Hs1 & HD1 & _).
      pose proof (WfCtx_ap s1 G Hs1 HG) as HG1.
      pose proof (EvT_fresh_tys (nparams w2) n1) as HTs.
      destruct (unify_coD_sound _ _ _ _ _ _ _ _ _ E2 ltac:(dok) HT1 (EvT_grp _ _ (EvT_spine _ HTs)))
        as (Hs2 & Hch & Hgu2).
      pose proof ((proj2 Hgu2) (DOk_mono D1 n1 (n1 + nparams w2) HD1 ltac:(lia))) as Gd2'.
      pose proof (Good_pre D1 n1 (n1 + nparams w2) s2 Du2 n2 ltac:(lia) HD1 Gd2') as Gd2.
      assert (HD2 : DOk Du2 n2) by (destruct Gd2 as (_ & _ & H2' & _); exact H2').
      pose proof (WfCtx_ap s2 _ Hs2 HG1) as HG2.
      assert (Hx : fresh_var G (e_match w2 a7 ars2) `notin` dom (apC s2 (apC s1 G)) `union` fv_arms ars2).
      { pose proof (fresh_var_notin_dom G (e_match w2 a7 ars2)) as H1'.
        pose proof (fresh_var_notin_fv G (e_match w2 a7 ars2)) as H2'. simpl in H2'.
        pose proof (dom_apC s1 G) as H3'. pose proof (dom_apC s2 (apC s1 G)) as H4'. fsetdec. }
      destruct (IHa _ _ _ _ _ _ _ _ _ _ _ _ _ _ E3 HG2 (DOk_mono Du2 n2 (S n2) HD2 (le_S _ _ (le_n n2)))
                  (Forall_EvT_ap s2 _ Hs2 HTs) (EvT_var _ (ev_ea n2)) Hx)
        as (Gd3' & HT3 & _ & HH3 & Harms & Herarms & Hlcarms).
      pose proof (Good_pre Du2 n2 (S n2) s3 D3 n3 (le_S _ _ (le_n n2)) HD2 Gd3') as Gd3.
      pose proof Gd3 as (_ & Hs3 & _).
      split; [ exact (Good_comp _ _ _ _ _ _ _ _ (Good_comp _ _ _ _ _ _ _ _ Gd1 Gd2) Gd3) | ].
      split; [ exact HT3 | ].
      split; [ exact (HOk_app _ _ (HOk_ap _ _ Hs3 (HOk_ap _ _ Hs2 HH1)) HH3) | ].
      refine (conj _ (conj _ (conj _ Hlcarms))).
      2: { cbn [erase]. rewrite erase_coerce, Her_Hty1, Herarms. reflexivity. }
      2: { apply lce_coerce. exact Hlc_Hty1. }
      rewrite <- !apC_comp.
      pose proof (V_coerce _ _ _ _ _ _ _ _ Hch (V_push _ _ _ _ _ _ _ _ _ Gd2 Hv1)) as Vc.
      pose proof (V_push _ _ _ _ _ _ _ _ _ Gd3 Vc) as Vs.
      rewrite !apT_grp, !apT_spine in Vs.
      refine (V_match (dom G `union` {{fresh_var G (e_match w2 a7 ars2)}}) _ _ _ _ _ _ _ _ _ _ Vs _ _).
      * apply arms_wf_b_sound. rewrite <- arms_wf_b_erase, Herarms. exact Hwb.
      * eapply VA_L; [ | exact Harms ].
        pose proof (dom_apC s1 G) as H3'. pose proof (dom_apC s2 (apC s1 G)) as H4'. fsetdec.
    + (* spread *)
      destruct (infer f D G a8 n) as [[[[[[s1 D1] T1] n1] us1] H1]|] eqn:E1; [|discriminate].
      destruct (infer f D1 (apC s1 G) a9 n1) as [[[[[[s2 D2] T2] n2] us2] H2]|] eqn:E2; [|discriminate].
      destruct (IHe _ _ _ _ _ _ _ _ _ _ E1 HG HD) as (Gd1 & HT1 & HH1 & Hv1 & Her_Hty1 & Hlc_Hty1).
      pose proof Gd1 as (_ & Hs1 & HD1 & _).
      pose proof (WfCtx_ap s1 G Hs1 HG) as HG1.
      destruct (IHe _ _ _ _ _ _ _ _ _ _ E2 HG1 HD1) as (Gd2 & HT2 & HH2 & Hv2 & Her_Hty2 & Hlc_Hty2).
      pose proof Gd2 as (_ & Hs2 & HD2 & _).
      match type of H with context [unify_coD ?f0 ?D0 ?A0 ?B0 ?n0] =>
        destruct (unify_coD f0 D0 A0 B0 n0) as [[[[s3 Du3] cs3] n3]|] eqn:E3 end.
      * match type of H with context [if rlacksD ?a0 ?b0 ?c0 then _ else _] =>
          destruct (rlacksD a0 b0 c0) eqn:Hlk end.
        -- inversion H; try subst s; try subst D'; try subst T; try subst n'; try subst e'; try subst Hq; clear H.
           assert (Hrow : EvT (typ_Record (row_Var (ea n2)))) by (apply EvT_Record, EvR_var, ev_ea).
           destruct (unify_coD_sound _ _ _ _ _ _ _ _ _ E3 ltac:(dok) (EvT_ap s2 T1 Hs2 HT1) Hrow)
             as (Hs3 & Hch & Hgu3).
           pose proof (GoodU_pre D2 n2 _ s3 Du3 n3 HD2 Hgu3 ltac:(lia)) as Gd3.
           split; [ exact (Good_comp _ _ _ _ _ _ _ _ (Good_comp _ _ _ _ _ _ _ _ Gd1 Gd2) Gd3) | ].
           split.
           { apply EvT_ap; [ exact Hs3 | ]. apply EvT_Record, EvR_ext; [ exact HT2 | apply EvR_var, ev_ea ]. }
           split; [ exact (HOk_app _ _ (HOk_ap _ _ Hs3 (HOk_ap _ _ Hs2 HH1)) (HOk_ap _ _ Hs3 HH2)) | ].
           refine (conj _ (conj _ _)).
           2: { cbn [erase]. rewrite erase_coerce, Her_Hty1, Her_Hty2. reflexivity. }
           2: { cbn [lce]. split; [ apply lce_coerce; exact Hlc_Hty1 | exact Hlc_Hty2 ]. }
           rewrite <- !apC_comp.
           exact (V_spreadL _ _ _ _ _ _ (apR s3 (row_Var (ea n2))) (apT s3 T2) _ _
                    (V_coerce _ _ _ _ _ _ _ _ Hch
                       (V_push _ _ _ _ _ _ _ _ _ Gd3 (V_push _ _ _ _ _ _ _ _ _ Gd2 Hv1)))
                    Hlk (V_push _ _ _ _ _ _ _ _ _ Gd3 Hv2)).
        -- exact (spread_present_sound f D n G l8 a8 a9 s1 D1 T1 n1 us1 H1 s2 D2 T2 n2 us2 H2 s D' T n' e' Hq
                    H HG Gd1 HT1 HH1 Hv1 Her_Hty1 Hlc_Hty1 Gd2 HT2 HH2 Hv2 Her_Hty2 Hlc_Hty2).
      * exact (spread_present_sound f D n G l8 a8 a9 s1 D1 T1 n1 us1 H1 s2 D2 T2 n2 us2 H2 s D' T n' e' Hq
                 H HG Gd1 HT1 HH1 Hv1 Her_Hty1 Hlc_Hty1 Gd2 HT2 HH2 Hv2 Her_Hty2 Hlc_Hty2).
    + (* restrict *)
      destruct (infer f D G a10 n) as [[[[[[s1 D1] T1] n1] us1] H1]|] eqn:E1; [|discriminate].
      destruct (unify_coD f (rupd D1 (ea (S n1)) (RK k_Any (Nat.eqb l10)))
                  T1 (typ_Record (row_Ext l10 (typ_Var (ea n1)) (row_Var (ea (S n1)))))
                  (n1 + 2)) as [[[[s2 Du2] cs2] n2]|] eqn:E2; [|discriminate].
      inversion H; try subst s; try subst D'; try subst T; try subst n'; try subst e'; try subst Hq; clear H.
      destruct (IHe _ _ _ _ _ _ _ _ _ _ E1 HG HD) as (Gd1 & HT1 & HH1 & Hv1 & Her_Hty1 & Hlc_Hty1).
      pose proof Gd1 as (_ & Hs1 & HD1 & _).
      assert (Hrow : EvT (typ_Record (row_Ext l10 (typ_Var (ea n1)) (row_Var (ea (S n1)))))).
      { apply EvT_Record, EvR_ext; [ apply EvT_var, ev_ea | apply EvR_var, ev_ea ]. }
      pose proof (Good_pre D1 n1 (S n1) sid (rupd D1 (ea (S n1)) (RK k_Any (Nat.eqb l10))) (S (S n1))
                    (le_S _ _ (le_n n1)) HD1
                    (Good_rupd D1 (S n1) (RK k_Any (Nat.eqb l10)) (DOk_mono D1 n1 (S n1) HD1 (le_S _ _ (le_n n1)))))
        as GdU.
      destruct (unify_coD_sound _ _ _ _ _ _ _ _ _ E2 (DOk_mono _ _ (n1 + 2) (Good_dok _ _ _ _ _ GdU) ltac:(lia)) HT1 Hrow) as (Hs2 & Hch & Hgu2).
      pose proof (GoodU_pre _ (S (S n1)) _ s2 Du2 n2 (Good_dok _ _ _ _ _ GdU) Hgu2 ltac:(lia)) as Gd2'.
      pose proof (Good_lift _ _ _ _ _ _ _ GdU Gd2') as Gd2.
      split; [ exact (Good_comp _ _ _ _ _ _ _ _ Gd1 Gd2) | ].
      split; [ apply EvT_ap; [ exact Hs2 | apply EvT_Record, EvR_var, ev_ea ] | ].
      split; [ exact (HOk_ap _ _ Hs2 HH1) | ].
      refine (conj _ (conj _ _)).
      2: { cbn [erase]. rewrite erase_coerce, Her_Hty1. reflexivity. }
      2: { cbn [lce]. apply lce_coerce. exact Hlc_Hty1. }
      rewrite <- apC_comp.
      exact (V_restrict _ _ _ _ _ (apT s2 (typ_Var (ea n1))) (apR s2 (row_Var (ea (S n1)))) _
               (V_coerce _ _ _ _ _ _ _ _ Hch (V_push _ _ _ _ _ _ _ _ _ Gd2 Hv1))).
  - intros D G fs n s D' R n' fs' Hq H HG HD. cbn [infer_fields] in H.
    destruct fs as [| l e rest | l e rest]; try discriminate H.
    + inversion H; try subst s; try subst D'; try subst R; try subst n'; try subst fs'; try subst Hq; clear H.
      split; [apply Good_id; exact HD|]. split; [apply EvR_Empty|]. split; [ exact HOk_nil | ].
      refine (conj _ (conj eq_refl I)).
      rewrite apC_sid. intros S D'' n'' Hg _. apply FT_nil. apply uniq_apC. exact (proj1 HG).
    + destruct (infer f D G e n) as [[[[[[s1 D1] T1] n1] us1] H1]|] eqn:E1; [|discriminate].
      destruct (infer_fields f D1 (apC s1 G) rest n1) as [[[[[[s2 D2] R2] n2] us2] H2]|] eqn:E2; [|discriminate].
      inversion H; try subst s; try subst D'; try subst R; try subst n'; try subst fs'; try subst Hq; clear H.
      destruct (IHe _ _ _ _ _ _ _ _ _ _ E1 HG HD) as (Gd1 & HT1 & HH1 & Hv1 & Her_Hty1 & Hlc_Hty1).
      pose proof Gd1 as (_ & Hs1 & HD1 & _).
      pose proof (WfCtx_ap s1 G Hs1 HG) as HG1.
      destruct (IHf _ _ _ _ _ _ _ _ _ _ E2 HG1 HD1) as (Gd2 & HR2 & HH2 & Hv2 & Her_Hty2 & Hlc_Hty2).
      pose proof Gd2 as (_ & Hs2 & _).
      split; [ exact (Good_comp _ _ _ _ _ _ _ _ Gd1 Gd2) | ].
      split; [ apply EvR_ext; [ apply EvT_ap; auto | exact HR2 ] | ].
      split; [ exact (HOk_app _ _ (HOk_ap _ _ Hs2 HH1) HH2) | ].
      refine (conj _ (conj _ (conj Hlc_Hty1 Hlc_Hty2))).
      2: { cbn [erase_fields]. rewrite Her_Hty1, Her_Hty2. reflexivity. }
      rewrite <- apC_comp.
      exact (VF_cons _ _ _ _ _ _ _ _ _ _ (V_push _ _ _ _ _ _ _ _ _ Gd2 Hv1) Hv2).
  - intros D G w Ts x res ars n s D' T n' ars' Hq H HG HD HTs Hres Hx. cbn [infer_arms] in H.
    destruct ars as [|e|tg e rest].
    + inversion H; try subst s; try subst D'; try subst T; try subst n'; try subst ars'; try subst Hq; clear H.
      split; [ apply Good_id; exact HD | ]. split; [ exact Hres | ].
      split; [ rewrite apT_sid; reflexivity | ]. split; [ exact HOk_nil | ].
      refine (conj _ (conj eq_refl I)). apply VA_nil.
    + destruct (infer f D G e n) as [[[[[[s1 D1] T1] n1] us1] H1]|] eqn:E1; [|discriminate].
      destruct (unify_coD f D1 T1 (apT s1 res) n1) as [[[[s2 Du2] cs2] n2]|] eqn:E2; [|discriminate].
      inversion H; try subst s; try subst D'; try subst T; try subst n'; try subst ars'; try subst Hq; clear H.
      destruct (IHe _ _ _ _ _ _ _ _ _ _ E1 HG HD) as (Gd1 & HT1 & HH1 & Hv1 & Her1 & Hlc1).
      pose proof Gd1 as (_ & Hs1 & HD1 & _).
      destruct (unify_coD_sound _ _ _ _ _ _ _ _ _ E2 ltac:(dok) HT1 (EvT_ap s1 res Hs1 Hres))
        as (Hs2 & Hch & Hgu2).
      pose proof (GoodU_pre D1 n1 _ s2 Du2 n2 HD1 Hgu2 ltac:(lia)) as Gd2.
      split; [ exact (Good_comp _ _ _ _ _ _ _ _ Gd1 Gd2) | ].
      split; [ exact (EvT_ap s2 _ Hs2 (EvT_ap s1 res Hs1 Hres)) | ].
      split; [ apply apT_comp | ].
      split; [ exact (HOk_ap _ _ Hs2 HH1) | ].
      refine (conj _ (conj _ _)).
      2: { cbn [erase_arms]. rewrite erase_coerce, Her1. reflexivity. }
      2: { cbn [lcea]. apply lce_coerce. exact Hlc1. }
      apply VA_else. rewrite <- apC_comp.
      exact (V_coerce _ _ _ _ _ _ _ _ Hch (V_push _ _ _ _ _ _ _ _ _ Gd2 Hv1)).
    + simpl in Hx.
      destruct (infer f D ((x ~ sch_mono (tag_payload w Ts tg)) ++ G)
                  (open_exp_wrt_exp e (e_fvar_f x)) n) as [[[[[[s1 D1] T1] n1] us1] H1]|] eqn:E1; [|discriminate].
      destruct (unify_coD f D1 T1 (apT s1 res) n1) as [[[[s2 Du2] cs2] n2]|] eqn:E2; [|discriminate].
      destruct (infer_arms f Du2 (apC (scomp s2 s1) G) w (map (apT (scomp s2 s1)) Ts) x
                  (apT s2 (apT s1 res)) rest n2)
        as [[[[[[s3 D3] T3] n3] us3] H3]|] eqn:E3; [|discriminate].
      inversion H; try subst s; try subst D'; try subst T; try subst n'; try subst ars'; try subst Hq; clear H.
      assert (Hwf : WfCtx ((x ~ sch_mono (tag_payload w Ts tg)) ++ G))
        by (apply WfCtx_cons; [ exact HG | fsetdec | apply WfSch_mono; apply EvT_tag_payload; exact HTs ]).
      destruct (IHe _ _ _ _ _ _ _ _ _ _ E1 Hwf HD) as (Gd1 & HT1 & HH1 & Hv1 & Her1 & Hlc1).
      pose proof Gd1 as (_ & Hs1 & HD1 & _).
      pose proof (WfCtx_ap s1 G Hs1 HG) as HG1.
      destruct (unify_coD_sound _ _ _ _ _ _ _ _ _ E2 ltac:(dok) HT1 (EvT_ap s1 res Hs1 Hres))
        as (Hs2 & Hch2 & Hgu2).
      pose proof (GoodU_pre D1 n1 _ s2 Du2 n2 HD1 Hgu2 ltac:(lia)) as Gd2.
      pose proof (Good_comp _ _ _ _ _ _ _ _ Gd1 Gd2) as Gd12.
      pose proof Gd12 as (_ & Hs12 & _).
      pose proof (WfCtx_ap _ G Hs12 HG) as HG12.
      assert (HD2 : DOk Du2 n2) by (destruct Gd2 as (_ & _ & H2' & _); exact H2').
      assert (Hx3 : x `notin` dom (apC (scomp s2 s1) G) `union` fv_arms rest)
        by (pose proof (dom_apC (scomp s2 s1) G) as H3'; fsetdec).
      destruct (IHa _ _ _ _ _ _ _ _ _ _ _ _ _ _ E3 HG12 HD2 (Forall_EvT_ap _ _ Hs12 HTs)
                  (EvT_ap s2 _ Hs2 (EvT_ap s1 res Hs1 Hres)) Hx3)
        as (Gd3 & HT3 & HT3eq & HH3 & Harms & Herrest & Hlcrest).
      pose proof Gd3 as (_ & Hs3 & _).
      destruct (bind_ok x e (coerce cs2 us1)
                  (eq_trans (erase_coerce cs2 us1) Her1)
                  (lce_coerce cs2 us1 0 Hlc1) ltac:(fsetdec)) as [Her' Hlc'].
      split; [ exact (Good_comp _ _ _ _ _ _ _ _ Gd12 Gd3) | ].
      split; [ exact HT3 | ].
      split.
      { rewrite HT3eq, (apT_comp s2 s1 res), (apT_comp s3 (scomp s2 s1) res). reflexivity. }
      split; [ exact (HOk_app _ _ (HOk_ap _ _ Hs3 (HOk_ap _ _ Hs2 HH1)) HH3) | ].
      refine (conj _ (conj _ (conj Hlc' Hlcrest))).
      2: { cbn [erase_arms]. rewrite Her', Herrest. reflexivity. }
      rewrite <- (apC_comp s3 (scomp s2 s1) G), <- (map_apT_comp s3 (scomp s2 s1) Ts).
      apply VA_cons.
      * intros y Hy.
        assert (Hyd : y `notin` dom (apC s3 (apC (scomp s2 s1) G))) by (rewrite !dom_apC; fsetdec).
        pose proof (V_push _ _ _ _ _ _ _ _ _ Gd3
                      (V_coerce _ _ _ _ _ _ _ _ Hch2 (V_push _ _ _ _ _ _ _ _ _ Gd2 Hv1))) as Hb.
        rewrite !apC_app, !apC_single, !apS_mono, !apT_tag_payload in Hb.
        rewrite (map_apT_comp s2 s1 Ts), (apC_comp s2 s1 G) in Hb.
        rewrite HT3eq.
        refine (V_open_cl _ _ _ _ _ _ _ _ _ Hb (lce_coerce cs2 us1 0 Hlc1) _).
        simpl. pose proof (dom_apC s3 (apC (scomp s2 s1) G)) as H3'.
        pose proof (dom_apC (scomp s2 s1) G) as H4'. fsetdec.
      * eapply VA_L; [ | exact Harms ].
        pose proof (dom_apC (scomp s2 s1) G) as H3'. fsetdec.
  - intros D G p Tp fs n s D' R n' fs' Hq H HG HD HTp Hp. cbn [infer_obj] in H.
    destruct fs as [| l e rest | l e rest]; try discriminate H.
    + inversion H; try subst s; try subst D'; try subst R; try subst n'; try subst fs'; try subst Hq; clear H.
      split; [apply Good_id; exact HD|]. split; [apply EvR_Empty|]. split; [ exact HOk_nil | ].
      refine (conj _ (conj eq_refl (conj I (conj eq_refl _)))).
      * rewrite apC_sid. intros S D'' n'' Hg _. apply FT_nil. apply uniq_apC. exact (proj1 HG).
      * rewrite apT_sid. constructor.
    + destruct (infer f D G e n) as [[[[[[s1 D1] T1] n1] us1] H1]|] eqn:E1; [|discriminate].
      destruct (infer_obj f D1 (apC s1 G) p (apT s1 Tp) rest n1)
        as [[[[[[s2 D2] R2] n2] us2] H2]|] eqn:E2; [|discriminate].
      inversion H; try subst s; try subst D'; try subst R; try subst n'; try subst fs'; try subst Hq; clear H.
      destruct (IHe _ _ _ _ _ _ _ _ _ _ E1 HG HD) as (Gd1 & HT1 & HH1 & Hv1 & Her_Hty1 & Hlc_Hty1).
      pose proof Gd1 as (_ & Hs1 & HD1 & _).
      pose proof (WfCtx_ap s1 G Hs1 HG) as HG1.
      simpl in Hp.
      destruct (IHo _ _ _ _ _ _ _ _ _ _ _ _ E2 HG1 HD1 (EvT_ap s1 Tp Hs1 HTp)
                  ltac:(rewrite dom_apC; fsetdec))
        as (Gd2 & HR2 & HH2 & Hv2 & Her2 & Hlc2 & Hmk2 & Hmt2).
      pose proof Gd2 as (_ & Hs2 & _).
      split; [ exact (Good_comp _ _ _ _ _ _ _ _ Gd1 Gd2) | ].
      split; [ apply EvR_ext; [ apply EvT_ap; auto | exact HR2 ] | ].
      split; [ exact (HOk_app _ _ (HOk_ap _ _ Hs2 HH1) HH2) | ].
      refine (conj _ (conj _ (conj (conj Hlc_Hty1 Hlc2) (conj _ _)))).
      4: { rewrite <- apT_comp. constructor. exact Hmt2. }
      3: { cbn [marks]. rewrite Hmk2. reflexivity. }
      2: { cbn [erase_fields]. rewrite Her_Hty1, Her2. reflexivity. }
      rewrite <- apC_comp.
      exact (VF_cons _ _ _ _ _ _ _ _ _ _ (V_push _ _ _ _ _ _ _ _ _ Gd2 Hv1) Hv2).
    + destruct e; try discriminate H.
      destruct (infer f D ((p ~ sch_mono Tp) ++ G) (open_exp_wrt_exp e (e_fvar_f p)) n)
        as [[[[[[s1 D1] T1] n1] us1] H1]|] eqn:E1; [|discriminate].
      destruct (infer_obj f D1 (apC s1 G) p (apT s1 Tp) rest n1)
        as [[[[[[s2 D2] R2] n2] us2] H2]|] eqn:E2; [|discriminate].
      inversion H; try subst s; try subst D'; try subst R; try subst n'; try subst fs'; try subst Hq; clear H.
      simpl in Hp.
      assert (Hwf : WfCtx ((p ~ sch_mono Tp) ++ G))
        by (apply WfCtx_cons; [ exact HG | fsetdec | apply WfSch_mono; exact HTp ]).
      destruct (IHe _ _ _ _ _ _ _ _ _ _ E1 Hwf HD) as (Gd1 & HT1 & HH1 & Hv1 & Her1 & Hlc1).
      pose proof Gd1 as (_ & Hs1 & HD1 & _).
      pose proof (WfCtx_ap s1 G Hs1 HG) as HG1.
      destruct (bind_ok _ e _ Her1 Hlc1 ltac:(fsetdec)) as [Her' Hlc'].
      destruct (IHo _ _ _ _ _ _ _ _ _ _ _ _ E2 HG1 HD1 (EvT_ap s1 Tp Hs1 HTp)
                  ltac:(rewrite dom_apC; fsetdec))
        as (Gd2 & HR2 & HH2 & Hv2 & Her2 & Hlc2 & Hmk2 & Hmt2).
      pose proof Gd2 as (_ & Hs2 & _).
      split; [ exact (Good_comp _ _ _ _ _ _ _ _ Gd1 Gd2) | ].
      split.
      { apply EvR_ext; [ | exact HR2 ].
        apply EvT_arrow; [ apply EvT_ap; [ exact Hs2 | apply EvT_ap; [ exact Hs1 | exact HTp ] ]
                         | apply EvT_ap; [ exact Hs2 | exact HT1 ] ]. }
      split; [ exact (HOk_app _ _ (HOk_ap _ _ Hs2 HH1) HH2) | ].
      refine (conj _ (conj _ (conj _ (conj _ _)))).
      5: { rewrite <- apT_comp. constructor. exact Hmt2. }
      4: { cbn [marks]. rewrite Hmk2. reflexivity. }
      3: { cbn [lcef]. split; [ exact Hlc' | exact Hlc2 ]. }
      2: { cbn [erase_fields erase]. rewrite Her', Her2. reflexivity. }
      rewrite <- apC_comp.
      rewrite apC_cons_mono in Hv1.
      apply VF_meth; [ | exact Hv2 ].
      pose proof (V_abs _ _ _ _ _ _ _ _ Hv1 Hlc1 ltac:(rewrite dom_apC; fsetdec)) as Hab.
      exact (V_push _ _ _ _ _ _ _ _ _ Gd2 Hab).
Qed.

(* The statement for programs: a closed term the algorithm accepts has an
   elaboration, which has the type the algorithm returns, in the kinding
   environment it returns, which records the sort of each variable the type
   leaves free, and which erases to the program. *)
Theorem infer_closed_sound : forall fuel e D T e',
  infer_closed_elab fuel e = Some (D, T, e') -> typing D nil e' T /\ erase e' = e.
Proof.
  intros fuel e D T e' H. unfold infer_closed_elab in H.
  destruct (infer fuel d_any nil e 0) as [[[[[[s D0] T0] n] us] Hq]|] eqn:Ei; [|discriminate].
  destruct (dis_top fuel D0 Hq n) as [[[d D1] n1]|] eqn:Ed; [|discriminate].
  inversion H; subst; clear H.
  assert (Hwf : WfCtx nil) by (split; [constructor | intros x sc Hb; inversion Hb]).
  destruct ((proj1 (infer_sound fuel)) _ _ _ _ _ _ _ _ _ _ Ei Hwf (d_any_DOk 0))
    as (Gd & _ & HH & Hv & Her & _).
  unfold dis_top in Ed.
  destruct (V_dis _ _ _ _ _ _ _ _ _ _ _ Hv Ed (Good_dok _ _ _ _ _ Gd) HH) as (_ & Hty).
  exact (conj Hty Her).
Qed.
