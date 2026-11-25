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
